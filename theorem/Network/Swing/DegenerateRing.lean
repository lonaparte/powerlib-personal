import theorem.Network.Swing.Degenerate
import theorem.Network.Swing.CycleMinimum

/-! # Networked swing equations: a degenerate strict minimum (five machines and more)

A five-machine ring (extended by leaves to every larger network) whose potential has a degenerate
strict minimum: locally asymptotically stable with a non-Hurwitz Jacobian, so the local
asymptotic translation of `Swing.family` is not exact from five machines on.

Model boundary.
* The model of `theorem/Network/Swing/Basic.lean`: `n + 1` machines, reduced state `(δ, ω)`, unit
  inertia and damping in the witnesses, constant power, symmetric nonnegative lossless
  couplings, constant voltages, continuous time; no governor, AVR, PLL, converter control, delay
  or PWM.
* The witness. Five machines on a ring `0 → 1 → 2 → 3 → 4 → 0` (`Ring5`): line weights
  `W = (−12, 36, 54, 54, 54)` and line flows `f = (−4, −36, −108, −108, −27)` (line `e` joins
  machines `e` and `e + 1`; `Wₑ = Bₑ cos(θₑ − θₑ₊₁)`, `fₑ = Bₑ sin(θₑ − θₑ₊₁)`,
  `Bₑ = √(Wₑ² + fₑ²)`), power `Pₖ = fₖ − fₖ₋₁`, angles `θₖ = arg wₖ` of the Gaussian-integer
  node phasors `w₀ = 1`, `wₖ₊₁ = wₖ conj(zₖ)`, `zₑ = Wₑ + i fₑ` (the product of the `zₑ` is real
  positive, so the ring closes). For more machines, unit leaves are attached to machine `0`
  (`addLeaf`, `degenerate_addLeaf`).

Source: work-sync `theory/T-synchronization-manifold.md` §1.7, §2.2 (swing network and its
energy); the characterization of local asymptotic stability is
`theorem/Network/Swing/Degenerate.lean` (`mem_den_locallyAsymptoticallyStable_iff`).

Results.
* Since `∑ 1/Wₑ = 0` the Hessian of the potential in relative angles is singular (null direction
  `(9, 6, 4, 2)`, `kernel_ring`), so the reduced Jacobian is not Hurwitz; since moreover
  `∑ fₑ/Wₑ³ = 0` the cubic term vanishes along it, and the quartic term is positive: the
  potential has a degenerate strict minimum and an isolated critical point (`ring_strictMin`,
  from `CycleMinimum.cycle_strictMin` and the flow-shift inequality `ring_gamma`).
* `ring5_mem_den_locallyAsymptoticallyStable`: the five-machine ring is locally asymptotically
  stable (connection statement), while `ring5_not_isHurwitz`: its reduced Jacobian is not
  Hurwitz.
* `not_exact_locallyAsymptoticallyStable`: for every number of machines `n + 5 ≥ 5` the local
  asymptotic translation `{powerFlow, jacobianStable}` of `Swing.family` is not exact.
* Static evidence: `norm_mul_cos_arg_sub` (line angles from node phasors), `Ring5.balance`,
  `Ring5.potential_ring`, `Ring5.crit_ring`, `Ring5.kernel_ring`, `Ring5.ring_gamma`,
  `Ring5.ring_strictMin`, `degenerate_addLeaf`, `exists_degenerate`, `not_isHurwitz_of_kernel`.

Family and connection conclusions.
* Public behavioural conclusions are `connection%` statements on `Swing.family`; everything else
  is static evidence on the models or generic foundation.
-/

noncomputable section
namespace powerlib.Network.Swing
open Matrix Finset Filter Topology Metric ComplexConjugate
open powerlib.Dynamics (State)
open powerlib.Network.Swing.CycleMinimum (edgeG edgeD edgeQ amp)

variable {n : ℕ}

/-- Line angle from node phasors: if `a · conj b = λ z` with `λ > 0`, then
`‖z‖ cos(arg a − arg b) = Re z` and `‖z‖ sin(arg a − arg b) = Im z`. -/
@[powerlib_foundation] theorem norm_mul_cos_arg_sub {a b z : ℂ} {lam : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hl : 0 < lam) (h : a * conj b = lam * z) :
    ‖z‖ * Real.cos (Complex.arg a - Complex.arg b) = z.re ∧
      ‖z‖ * Real.sin (Complex.arg a - Complex.arg b) = z.im := by
  have hz : z ≠ 0 := by
    intro hz; rw [hz, mul_zero] at h
    exact mul_ne_zero ha ((map_ne_zero _).mpr hb) h
  have hna := norm_pos_iff.mpr ha
  have hnb := norm_pos_iff.mpr hb
  have hnz := norm_pos_iff.mpr hz
  have hn : ‖a‖ * ‖b‖ = lam * ‖z‖ := by
    have := congrArg norm h
    rw [norm_mul, Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl.le]
      at this
    exact this
  have hre : a.re * b.re + a.im * b.im = lam * z.re := by
    have := congrArg Complex.re h
    simp [Complex.mul_re] at this
    linarith
  have him : a.im * b.re - a.re * b.im = lam * z.im := by
    have := congrArg Complex.im h
    simp [Complex.mul_im] at this
    linarith
  rw [Real.cos_sub, Real.sin_sub, Complex.cos_arg ha, Complex.cos_arg hb, Complex.sin_arg,
    Complex.sin_arg]
  constructor
  · have e : a.re / ‖a‖ * (b.re / ‖b‖) + a.im / ‖a‖ * (b.im / ‖b‖) =
        (a.re * b.re + a.im * b.im) / (‖a‖ * ‖b‖) := by field_simp
    rw [e, hre, hn]; field_simp
  · have e : a.im / ‖a‖ * (b.re / ‖b‖) - a.re / ‖a‖ * (b.im / ‖b‖) =
        (a.im * b.re - a.re * b.im) / (‖a‖ * ‖b‖) := by field_simp
    rw [e, him, hn]; field_simp

/-- A lossless line with weight `W = B cos φ` and flow `f = B sin φ`: its potential increment is
the cycle edge potential. -/
@[powerlib_foundation] theorem mul_edgeIncrement {B φ W f : ℝ} (hW : B * Real.cos φ = W)
    (hf : B * Real.sin φ = f) (x : ℝ) : B * edgeIncrement φ x = edgeG W f x := by
  simp only [edgeIncrement, edgeG, Real.cos_add, ← hW, ← hf]; ring

/-- … and its flow at the displaced angle is `f + G'(x)`. -/
@[powerlib_foundation] theorem mul_sin_add {B φ W f : ℝ} (hW : B * Real.cos φ = W)
    (hf : B * Real.sin φ = f) (x : ℝ) : B * Real.sin (φ + x) = f + edgeD W f x := by
  simp only [edgeD, Real.sin_add, ← hW, ← hf]; ring

/-! ## A five-machine ring -/

namespace Ring5

/-- Line weights `Wₑ = Bₑ cos(θₑ − θₑ₊₁)` of the ring `0 → 1 → 2 → 3 → 4 → 0`. -/
def Wr : Fin 5 → ℝ := ![-12, 36, 54, 54, 54]

/-- Line flows `fₑ = Bₑ sin(θₑ − θₑ₊₁)`. -/
def fr : Fin 5 → ℝ := ![-4, -36, -108, -108, -27]

/-- Line phasors `zₑ = Wₑ + i fₑ`. -/
def zr (e : Fin 5) : ℂ := ⟨Wr e, fr e⟩

/-- Node phasors: `w₀ = 1`, `wₑ₊₁ = wₑ conj(zₑ)`. -/
def wr : Fin 5 → ℂ := ![1, ⟨-12, 4⟩, ⟨-576, -288⟩, ⟨0, -77760⟩, ⟨8398080, -4199040⟩]

/-- `wₑ conj(wₑ₊₁) = λₑ zₑ`. -/
def lamr : Fin 5 → ℝ := ![1, 160, 414720, 6046617600, 155520]

/-- Selected angles `θₖ = arg wₖ`. -/
def θr (k : Fin 5) : ℝ := Complex.arg (wr k)

/-- Line amplitudes `Bₑ = √(Wₑ² + fₑ²)`. -/
def Ar (e : Fin 5) : ℝ := amp (Wr e) (fr e)

/-- Ring coupling matrix: line `e` joins machines `e` and `e + 1` (mod 5). -/
def Br (i j : Fin 5) : ℝ := if j = i + 1 then Ar i else if i = j + 1 then Ar j else 0

theorem wr_ne (k : Fin 5) : wr k ≠ 0 := by
  fin_cases k <;> simp [wr, Complex.ext_iff]

theorem lamr_pos (e : Fin 5) : 0 < lamr e := by
  fin_cases e <;> simp [lamr] <;> norm_num

theorem wr_conj (e : Fin 5) : wr e * conj (wr (e + 1)) = (lamr e : ℂ) * zr e := by
  fin_cases e <;> simp [wr, lamr, zr, Wr, fr, Complex.ext_iff] <;> norm_num

theorem norm_zr (e : Fin 5) : ‖zr e‖ = Ar e := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]; rfl

/-- `Bₑ cos(θₑ − θₑ₊₁) = Wₑ`, `Bₑ sin(θₑ − θₑ₊₁) = fₑ`. -/
theorem line_trig (e : Fin 5) :
    Ar e * Real.cos (θr e - θr (e + 1)) = Wr e ∧ Ar e * Real.sin (θr e - θr (e + 1)) = fr e := by
  have h := norm_mul_cos_arg_sub (wr_ne e) (wr_ne (e + 1)) (lamr_pos e) (wr_conj e)
  rw [norm_zr] at h
  exact h

theorem Ar_nonneg (e : Fin 5) : 0 ≤ Ar e := Real.sqrt_nonneg _

theorem Br_symm (i j : Fin 5) : Br i j = Br j i := by
  fin_cases i <;> fin_cases j <;> simp [Br] <;> decide

theorem Br_nonneg (i j : Fin 5) : 0 ≤ Br i j := by
  unfold Br; split_ifs <;> first | exact Ar_nonneg _ | exact le_rfl

/-- A sum against the ring coupling has two terms. -/
theorem sum_Br (F : Fin 5 → ℝ) (k : Fin 5) :
    ∑ j, Br k j * F j = Ar k * F (k + 1) + Ar (k - 1) * F (k - 1) := by
  have h41 : (-1 : Fin 5) = 4 := rfl
  fin_cases k <;> simp [Br, Fin.sum_univ_five, h41] <;> ring

/-! ### The flow-shift inequality of the ring -/

theorem inv_sqrt_le {q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    1 / √q ≤ (c ^ 2 * q + 1) / (2 * c * q) := by
  have hs := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  rw [div_le_div_iff₀ hs (by positivity), one_mul]
  nlinarith [sq_nonneg (c * √q - 1), mul_pos hc hs]

theorem inv_sqrt_ge {q d : ℝ} (hq : 0 < q) (hd : 0 < d) : 2 * d / (q + d ^ 2) ≤ 1 / √q := by
  have hs := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  rw [div_le_div_iff₀ (by positivity) hs, one_mul]
  nlinarith [sq_nonneg (√q - d)]

theorem term_ge (t : ℝ) {μ ρ : ℝ} (k : ℕ) (hμ : |μ| ≤ ρ) : -(|t| * ρ ^ k) ≤ t * μ ^ k := by
  have h1 : |t * μ ^ k| ≤ |t| * ρ ^ k := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg μ) hμ k) (abs_nonneg t)
  linarith [neg_abs_le (t * μ ^ k)]

theorem ring_T_pos {μ : ℝ} (hμ : |μ| ≤ 1 / 2) : 0 < (82520638541733888) * μ ^ 0 + (4006064228272128) * μ ^ 1 + (-444291750542592) * μ ^ 2 + (-7746113954880) * μ ^ 3 + (929100585600) * μ ^ 4 + (-11056492224) * μ ^ 5 + (-348275376) * μ ^ 6 + (10865016) * μ ^ 7 + (-117612) * μ ^ 8 + (567) * μ ^ 9 + (-1) * μ ^ 10 := by
  have t1 := term_ge (4006064228272128 : ℝ) 1 hμ
  norm_num at t1
  have t2 := term_ge (-444291750542592 : ℝ) 2 hμ
  norm_num at t2
  have t3 := term_ge (-7746113954880 : ℝ) 3 hμ
  norm_num at t3
  have t4 := term_ge (929100585600 : ℝ) 4 hμ
  norm_num at t4
  have t5 := term_ge (-11056492224 : ℝ) 5 hμ
  norm_num at t5
  have t6 := term_ge (-348275376 : ℝ) 6 hμ
  norm_num at t6
  have t7 := term_ge (10865016 : ℝ) 7 hμ
  norm_num at t7
  have t8 := term_ge (-117612 : ℝ) 8 hμ
  norm_num at t8
  have t9 := term_ge (567 : ℝ) 9 hμ
  norm_num at t9
  have t10 := term_ge (-1 : ℝ) 10 hμ
  norm_num at t10
  linarith

theorem five_frac {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ} (h0 : 0 < b0) (h1 : 0 < b1)
    (h2 : 0 < b2) (h3 : 0 < b3) (h4 : 0 < b4)
    (hP : 0 < a0 * b1 * b2 * b3 * b4 - a1 * b0 * b2 * b3 * b4 - a2 * b0 * b1 * b3 * b4 -
      a3 * b0 * b1 * b2 * b4 - a4 * b0 * b1 * b2 * b3) :
    a1 / b1 + a2 / b2 + a3 / b3 + a4 / b4 < a0 / b0 := by
  have hB : 0 < b0 * b1 * b2 * b3 * b4 := by positivity
  have e : (a0 / b0 - (a1 / b1 + a2 / b2 + a3 / b3 + a4 / b4)) * (b0 * b1 * b2 * b3 * b4) =
      a0 * b1 * b2 * b3 * b4 - a1 * b0 * b2 * b3 * b4 - a2 * b0 * b1 * b3 * b4 -
        a3 * b0 * b1 * b2 * b4 - a4 * b0 * b1 * b2 * b3 := by
    field_simp
    ring
  have : 0 < a0 / b0 - (a1 / b1 + a2 / b2 + a3 / b3 + a4 / b4) := by
    rw [← e] at hP
    exact pos_of_mul_pos_left hP hB.le
  linarith

theorem edgeQ_ring0 (μ : ℝ) : edgeQ (Wr 0) (fr 0) μ = 144 + 8 * μ - μ ^ 2 := by
  simp [edgeQ, Wr, fr]; ring
theorem edgeQ_ring1 (μ : ℝ) : edgeQ (Wr (Fin.succ (0 : Fin 4))) (fr (Fin.succ (0 : Fin 4))) μ =
    1296 + 72 * μ - μ ^ 2 := by
  simp [edgeQ, Wr, fr]; ring
theorem edgeQ_ring2 (μ : ℝ) : edgeQ (Wr (Fin.succ (1 : Fin 4))) (fr (Fin.succ (1 : Fin 4))) μ =
    2916 + 216 * μ - μ ^ 2 := by
  simp [edgeQ, Wr, fr]; ring
theorem edgeQ_ring3 (μ : ℝ) : edgeQ (Wr (Fin.succ (2 : Fin 4))) (fr (Fin.succ (2 : Fin 4))) μ =
    2916 + 216 * μ - μ ^ 2 := by
  simp [edgeQ, Wr, fr]
  ring
theorem edgeQ_ring4 (μ : ℝ) : edgeQ (Wr (Fin.succ (3 : Fin 4))) (fr (Fin.succ (3 : Fin 4))) μ =
    2916 + 54 * μ - μ ^ 2 := by
  simp [edgeQ, Wr, fr]
  ring

/-- **The flow-shift inequality** `∑ᵢ 1/√qᵢ(μ) < 1/√q₀(μ)` for `0 < |μ| ≤ 1/2`: AM–GM bounds of
`1/√q` by rational functions tangent at `μ = 0`, and an exact factorization of the difference. -/
theorem ring_gamma {μ : ℝ} (hμ0 : μ ≠ 0) (hμ : |μ| ≤ 1 / 2) :
    ∑ i : Fin 4, 1 / √(edgeQ (Wr i.succ) (fr i.succ) μ) < 1 / √(edgeQ (Wr 0) (fr 0) μ) := by
  have hb := abs_le.mp hμ
  rw [Fin.sum_univ_four, edgeQ_ring1, edgeQ_ring2, edgeQ_ring3, edgeQ_ring4, edgeQ_ring0]
  have q0 : 0 < 144 + 8 * μ - μ ^ 2 := by nlinarith
  have q1 : 0 < 1296 + 72 * μ - μ ^ 2 := by nlinarith
  have q2 : 0 < 2916 + 216 * μ - μ ^ 2 := by nlinarith
  have q4 : 0 < 2916 + 54 * μ - μ ^ 2 := by nlinarith
  have c1 : 0 < 1 / 36 - μ / 1296 := by linarith
  have c2 : 0 < 1 / 54 - μ / 1458 := by linarith
  have c4 : 0 < 1 / 54 - μ / 5832 := by linarith
  have d0 : 0 < 12 + μ / 3 := by linarith
  refine lt_of_le_of_lt (add_le_add (add_le_add (add_le_add (inv_sqrt_le q1 c1)
    (inv_sqrt_le q2 c2)) (inv_sqrt_le q2 c2)) (inv_sqrt_le q4 c4))
    (lt_of_lt_of_le ?_ (inv_sqrt_ge q0 d0))
  have hT := ring_T_pos hμ
  have h27 : 0 < 27 - μ := by linarith
  have hμ2 : 0 < μ ^ 2 := by positivity
  refine five_frac (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) ?_
  have e : 2 * (12 + μ / 3) * (2 * (1 / 36 - μ / 1296) * (1296 + 72 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 5832) * (2916 + 54 * μ - μ ^ 2)) -
    ((1 / 36 - μ / 1296) ^ 2 * (1296 + 72 * μ - μ ^ 2) + 1) *
      (144 + 8 * μ - μ ^ 2 + (12 + μ / 3) ^ 2) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 5832) * (2916 + 54 * μ - μ ^ 2)) -
    ((1 / 54 - μ / 1458) ^ 2 * (2916 + 216 * μ - μ ^ 2) + 1) *
      (144 + 8 * μ - μ ^ 2 + (12 + μ / 3) ^ 2) *
      (2 * (1 / 36 - μ / 1296) * (1296 + 72 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 5832) * (2916 + 54 * μ - μ ^ 2)) -
    ((1 / 54 - μ / 1458) ^ 2 * (2916 + 216 * μ - μ ^ 2) + 1) *
      (144 + 8 * μ - μ ^ 2 + (12 + μ / 3) ^ 2) *
      (2 * (1 / 36 - μ / 1296) * (1296 + 72 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 5832) * (2916 + 54 * μ - μ ^ 2)) -
    ((1 / 54 - μ / 5832) ^ 2 * (2916 + 54 * μ - μ ^ 2) + 1) *
      (144 + 8 * μ - μ ^ 2 + (12 + μ / 3) ^ 2) *
      (2 * (1 / 36 - μ / 1296) * (1296 + 72 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) *
      (2 * (1 / 54 - μ / 1458) * (2916 + 216 * μ - μ ^ 2)) =
    μ ^ 2 * (27 - μ) * (2916 + 216 * μ - μ ^ 2) * ((82520638541733888) * μ ^ 0 + (4006064228272128) * μ ^ 1 + (-444291750542592) * μ ^ 2 + (-7746113954880) * μ ^ 3 + (929100585600) * μ ^ 4 + (-11056492224) * μ ^ 5 + (-348275376) * μ ^ 6 + (10865016) * μ ^ 7 + (-117612) * μ ^ 8 + (567) * μ ^ 9 + (-1) * μ ^ 10) / 976076478078336 := by ring
  rw [e]
  positivity

/-! ### The ring as a swing network -/

/-- The five-machine ring: unit inertia and damping, power `Pₖ = fₖ − fₖ₋₁`, ring coupling. -/
def params : Params 4 where
  M := fun _ => 1
  D := fun _ => 1
  P := fun k => fr k - fr (k - 1)
  B := Br
  M_pos := fun _ => one_pos
  D_pos := fun _ => one_pos
  B_symm := Br_symm
  B_nonneg := Br_nonneg

theorem line_trig' (k : Fin 5) :
    Ar (k - 1) * Real.cos (θr k - θr (k - 1)) = Wr (k - 1) ∧
      Ar (k - 1) * Real.sin (θr k - θr (k - 1)) = -fr (k - 1) := by
  have h := line_trig (k - 1)
  rw [sub_add_cancel] at h
  rw [show θr k - θr (k - 1) = -(θr (k - 1) - θr k) by ring, Real.cos_neg, Real.sin_neg]
  exact ⟨h.1, by rw [mul_neg, h.2]⟩

theorem balance : ∀ k, params.P k = powerInjection params.B θr k := by
  intro k
  show fr k - fr (k - 1) = ∑ j, Br k j * Real.sin (θr k - θr j)
  rw [sum_Br (fun j => Real.sin (θr k - θr j)) k, (line_trig k).2, (line_trig' k).2]
  ring

theorem potential_ring (u : Fin (4 + 1) → ℝ) :
    potential params (θr + u) - potential params θr =
      ∑ e : Fin 5, edgeG (Wr e) (fr e) (u e - u (e + 1)) := by
  rw [potential_add_sub balance u]
  have hk : ∀ k : Fin 5, ∑ j, params.B k j * edgeIncrement (θr k - θr j) (u k - u j) =
      edgeG (Wr k) (fr k) (u k - u (k + 1)) + edgeG (Wr (k - 1)) (fr (k - 1)) (u (k - 1) - u k) := by
    intro k
    show ∑ j, Br k j * edgeIncrement (θr k - θr j) (u k - u j) = _
    rw [sum_Br (fun j => edgeIncrement (θr k - θr j) (u k - u j)) k,
      mul_edgeIncrement (line_trig k).1 (line_trig k).2,
      mul_edgeIncrement (line_trig' k).1 (line_trig' k).2]
    simp only [edgeG]
    rw [show u k - u (k - 1) = -(u (k - 1) - u k) by ring, Real.cos_neg, Real.sin_neg]
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib]
  have hshift : ∑ k : Fin 5, edgeG (Wr (k - 1)) (fr (k - 1)) (u (k - 1) - u k) =
      ∑ e : Fin 5, edgeG (Wr e) (fr e) (u e - u (e + 1)) :=
    Fintype.sum_equiv (Equiv.subRight (1 : Fin 5)) _ _ fun k => by
      simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [hshift]
  ring

theorem flow_ring (u : Fin (4 + 1) → ℝ) (k : Fin 5) :
    powerInjection params.B (θr + u) k =
      (fr k + edgeD (Wr k) (fr k) (u k - u (k + 1))) -
        (fr (k - 1) + edgeD (Wr (k - 1)) (fr (k - 1)) (u (k - 1) - u k)) := by
  show ∑ j, Br k j * Real.sin ((θr + u) k - (θr + u) j) = _
  rw [sum_Br (fun j => Real.sin ((θr + u) k - (θr + u) j)) k]
  simp only [Pi.add_apply]
  rw [show θr k + u k - (θr (k + 1) + u (k + 1)) = (θr k - θr (k + 1)) + (u k - u (k + 1)) by ring,
    mul_sin_add (line_trig k).1 (line_trig k).2,
    show θr k + u k - (θr (k - 1) + u (k - 1)) =
      -((θr (k - 1) - θr (k - 1 + 1)) + (u (k - 1) - u k)) by rw [sub_add_cancel]; ring,
    Real.sin_neg, mul_neg, mul_sin_add (line_trig (k - 1)).1 (line_trig (k - 1)).2]
  ring

theorem crit_ring {u : Fin (4 + 1) → ℝ} (h : ∀ k, params.P k = powerInjection params.B (θr + u) k) :
    ∀ e : Fin 5, edgeD (Wr e) (fr e) (u e - u (e + 1)) = edgeD (Wr 0) (fr 0) (u 0 - u (0 + 1)) := by
  have hk : ∀ k : Fin 5, edgeD (Wr k) (fr k) (u k - u (k + 1)) =
      edgeD (Wr (k - 1)) (fr (k - 1)) (u (k - 1) - u k) := by
    intro k
    have := h k
    rw [flow_ring] at this
    change fr k - fr (k - 1) = _ at this
    linarith
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  norm_num at h1 h2 h3 h4
  intro e
  fin_cases e <;> norm_num <;> linarith

theorem kernel_ring : ∀ k : Fin (4 + 1),
    ∑ j, flowWeights params.B θr k j * (ground ![9, 6, 4, 2] k - ground ![9, 6, 4, 2] j) = 0 := by
  intro k
  have e : ∀ j, flowWeights params.B θr k j * (ground ![9, 6, 4, 2] k - ground ![9, 6, 4, 2] j) =
      Br k j * (Real.cos (θr k - θr j) * (ground ![9, 6, 4, 2] k - ground ![9, 6, 4, 2] j)) :=
    fun j => by simp only [flowWeights, of_apply]; rw [mul_assoc]; rfl
  rw [Finset.sum_congr rfl fun j _ => e j, sum_Br, ← mul_assoc, ← mul_assoc,
    (line_trig k).1, (line_trig' k).1]
  have h41 : (-1 : Fin 5) = 4 := rfl
  fin_cases k <;> simp [ground, Wr, h41] <;> norm_num

theorem hq_ring (e : Fin (4 + 1)) (μ : ℝ) (hμ : |μ| ≤ 1 / 2) : 0 < edgeQ (Wr e) (fr e) μ := by
  have hb := abs_le.mp hμ
  fin_cases e <;> simp [edgeQ, Wr, fr] <;> nlinarith

theorem abs_ground_le (v : Fin 4 → ℝ) (k : Fin (4 + 1)) : |ground v k| ≤ ‖v‖ := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · rw [ground_succ, ← Real.norm_eq_abs]; exact norm_le_pi_norm v i

/-- **The ring potential has a strict isolated minimum at the selected angles.** -/
theorem ring_strictMin : ∃ r > 0, ∀ v : Fin 4 → ℝ, v ≠ 0 → ‖v‖ < r →
    potential params θr < potential params (θr + ground v) ∧
      ¬ ∀ k, params.P k = powerInjection params.B (θr + ground v) k := by
  obtain ⟨rc, hrc, hcyc⟩ := CycleMinimum.cycle_strictMin (m := 4) (W := Wr) (f := fr)
    (by simp [Wr]) (fun i => by fin_cases i <;> simp [Wr]) (ρ := 1 / 2) hq_ring
    (fun μ h0 h => ring_gamma h0 h) (by norm_num)
  refine ⟨rc / 2, by positivity, fun v hv0 hv => ?_⟩
  have hx : ∀ e : Fin (4 + 1), |ground v e - ground v (e + 1)| < rc := fun e => by
    have h1 := abs_ground_le v e
    have h2 := abs_ground_le v (e + 1)
    calc |ground v e - ground v (e + 1)| ≤ |ground v e| + |ground v (e + 1)| := abs_sub _ _
      _ < rc := by linarith
  have hsum : ∑ e : Fin (4 + 1), (ground v e - ground v (e + 1)) = 0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
  have hne : (fun e : Fin (4 + 1) => ground v e - ground v (e + 1)) ≠ 0 := by
    intro h
    apply hv0
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have g0 : ground v 0 = 0 := rfl
    have g1 : ground v 1 = v 0 := rfl
    have g2 : ground v 2 = v 1 := rfl
    have g3 : ground v 3 = v 2 := rfl
    have g4 : ground v 4 = v 3 := rfl
    simp only [g0, g1, g2, g3, g4, show (0 : Fin (4 + 1)) + 1 = 1 from rfl,
      show (1 : Fin (4 + 1)) + 1 = 2 from rfl, show (2 : Fin (4 + 1)) + 1 = 3 from rfl,
      show (3 : Fin (4 + 1)) + 1 = 4 from rfl, Pi.zero_apply] at h0 h1 h2 h3
    funext i
    fin_cases i <;> simp <;> linarith
  obtain ⟨hpos, hnc⟩ := hcyc _ hsum hne hx
  refine ⟨by have := potential_ring (ground v); linarith, fun hcrit => hnc ?_⟩
  exact crit_ring hcrit

end Ring5

/-! ## Adding a leaf machine -/

/-- Coupling matrix with an extra machine (the last index) attached to machine `0` by a unit
line. -/
def leafB (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  Fin.snoc (α := fun _ => Fin (n + 2) → ℝ)
    (fun i => Fin.snoc (α := fun _ => ℝ) (B i) (if i = 0 then 1 else 0))
    (Fin.snoc (α := fun _ => ℝ) (fun j => if j = 0 then 1 else 0) 0)

@[simp] theorem leafB_cc (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    leafB B i.castSucc j.castSucc = B i j := by simp [leafB]
@[simp] theorem leafB_cl (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    leafB B i.castSucc (Fin.last _) = if i = 0 then 1 else 0 := by simp [leafB]
@[simp] theorem leafB_lc (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    leafB B (Fin.last _) j.castSucc = if j = 0 then 1 else 0 := by simp [leafB]
@[simp] theorem leafB_ll (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    leafB B (Fin.last _) (Fin.last _) = 0 := by simp [leafB]

/-- The network with a leaf machine: unit inertia, damping and line, no power. -/
def addLeaf (p : Params n) : Params (n + 1) where
  M := Fin.snoc (α := fun _ => ℝ) p.M 1
  D := Fin.snoc (α := fun _ => ℝ) p.D 1
  P := Fin.snoc (α := fun _ => ℝ) p.P 0
  B := leafB p.B
  M_pos := fun k => by
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [p.M_pos]
  D_pos := fun k => by
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [p.D_pos]
  B_symm := fun i j => by
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [p.B_symm]
  B_nonneg := fun i j => by
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [p.B_nonneg] <;> split_ifs <;> norm_num

/-- The leaf machine sits at the angle of machine `0`. -/
def leafAngle (θ : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ := Fin.snoc (α := fun _ => ℝ) θ (θ 0)

theorem powerInjection_leaf_c (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (φ : Fin (n + 2) → ℝ)
    (k : Fin (n + 1)) :
    powerInjection (leafB B) φ k.castSucc = powerInjection B (fun j => φ j.castSucc) k +
      (if k = 0 then Real.sin (φ k.castSucc - φ (Fin.last _)) else 0) := by
  unfold powerInjection
  rw [Fin.sum_univ_castSucc]
  simp only [leafB_cc, leafB_cl]
  split_ifs <;> simp

theorem powerInjection_leaf_l (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (φ : Fin (n + 2) → ℝ) :
    powerInjection (leafB B) φ (Fin.last _) =
      Real.sin (φ (Fin.last _) - φ (0 : Fin (n + 1)).castSucc) := by
  unfold powerInjection
  rw [Fin.sum_univ_castSucc]
  simp only [leafB_lc, leafB_ll, zero_mul, add_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1))]
  simp

theorem potential_leaf (p : Params n) (φ : Fin (n + 2) → ℝ) :
    potential (addLeaf p) φ = potential p (fun j => φ j.castSucc) -
      Real.cos (φ (0 : Fin (n + 1)).castSucc - φ (Fin.last _)) := by
  have hP : ∑ k, (addLeaf p).P k * φ k = ∑ k : Fin (n + 1), p.P k * φ k.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp [addLeaf]
  have hrow : ∀ k : Fin (n + 1), ∑ j, (addLeaf p).B k.castSucc j * Real.cos (φ k.castSucc - φ j) =
      ∑ j : Fin (n + 1), p.B k j * Real.cos (φ k.castSucc - φ j.castSucc) +
        (if k = 0 then Real.cos (φ k.castSucc - φ (Fin.last _)) else 0) := by
    intro k
    rw [Fin.sum_univ_castSucc]
    simp only [addLeaf, leafB_cc, leafB_cl, ite_mul, one_mul, zero_mul]
  have hlast : ∑ j, (addLeaf p).B (Fin.last _) j * Real.cos (φ (Fin.last _) - φ j) =
      Real.cos (φ (Fin.last _) - φ (0 : Fin (n + 1)).castSucc) := by
    rw [Fin.sum_univ_castSucc]
    simp only [addLeaf, leafB_lc, leafB_ll, ite_mul, one_mul, zero_mul, add_zero]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1))]
    simp
  have hsplit : ∑ k : Fin (n + 2), ∑ j, (addLeaf p).B k j * Real.cos (φ k - φ j) =
      ∑ k : Fin (n + 1), ∑ j, (addLeaf p).B k.castSucc j * Real.cos (φ k.castSucc - φ j) +
        ∑ j, (addLeaf p).B (Fin.last _) j * Real.cos (φ (Fin.last _) - φ j) :=
    Fin.sum_univ_castSucc (fun k : Fin (n + 2) => ∑ j, (addLeaf p).B k j * Real.cos (φ k - φ j))
  unfold potential
  rw [hP, hsplit, Finset.sum_congr rfl fun k _ => hrow k, hlast,
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1))]
  simp only [Finset.mem_univ, if_true]
  rw [show φ (Fin.last (n + 1)) - φ (0 : Fin (n + 1)).castSucc =
    -(φ (0 : Fin (n + 1)).castSucc - φ (Fin.last (n + 1))) by ring, Real.cos_neg]
  ring

@[simp] theorem leafAngle_c (θ : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    leafAngle θ k.castSucc = θ k := by simp [leafAngle]
@[simp] theorem leafAngle_l (θ : Fin (n + 1) → ℝ) : leafAngle θ (Fin.last _) = θ 0 := by
  simp [leafAngle]

theorem ground_c (v : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    ground v k.castSucc = ground (fun i => v i.castSucc) k := by
  refine Fin.cases ?_ (fun i => ?_) k
  · rfl
  · rw [← Fin.succ_castSucc]; rfl

theorem ground_l (v : Fin (n + 1) → ℝ) : ground v (Fin.last _) = v (Fin.last n) := by
  rw [← Fin.succ_last]; rfl

theorem eq_zero_of_restrict {v : Fin (n + 1) → ℝ} (h1 : (fun i : Fin n => v i.castSucc) = 0)
    (h2 : v (Fin.last n) = 0) : v = 0 := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · exact h2
  · exact congrFun h1 i

theorem norm_restrict_le (v : Fin (n + 1) → ℝ) : ‖(fun i : Fin n => v i.castSucc)‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i => norm_le_pi_norm v i.castSucc

/-- **Adding a leaf machine preserves a degenerate strict minimum.** A unit line from machine `0`
to a new machine at the same angle, without power, keeps power balance, the strict isolated
minimum of the potential (the new relative angle adds `1 − cos y`), and a null vector of the
linearization weights (extended by `0`). -/
theorem degenerate_addLeaf {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hmin : ∃ r > 0, ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖ < r →
      potential p θ < potential p (θ + ground v) ∧
        ¬ ∀ k, p.P k = powerInjection p.B (θ + ground v) k)
    (hker : ∃ v : Fin n → ℝ, v ≠ 0 ∧
      ∀ k, ∑ j, flowWeights p.B θ k j * (ground v k - ground v j) = 0) :
    (∀ k, (addLeaf p).P k = powerInjection (addLeaf p).B (leafAngle θ) k) ∧
    (∃ r > 0, ∀ v : Fin (n + 1) → ℝ, v ≠ 0 → ‖v‖ < r →
      potential (addLeaf p) (leafAngle θ) < potential (addLeaf p) (leafAngle θ + ground v) ∧
        ¬ ∀ k, (addLeaf p).P k = powerInjection (addLeaf p).B (leafAngle θ + ground v) k) ∧
    (∃ v : Fin (n + 1) → ℝ, v ≠ 0 ∧
      ∀ k, ∑ j, flowWeights (addLeaf p).B (leafAngle θ) k j * (ground v k - ground v j) = 0) := by
  -- the shifted profile in the old coordinates
  have hφ : ∀ v : Fin (n + 1) → ℝ, (fun j => (leafAngle θ + ground v) j.castSucc) =
      θ + ground (fun i => v i.castSucc) := fun v => by
    funext j; simp only [Pi.add_apply, leafAngle_c, ground_c]
  have hφl : ∀ v : Fin (n + 1) → ℝ, (leafAngle θ + ground v) (Fin.last _) = θ 0 + v (Fin.last n) :=
    fun v => by simp only [Pi.add_apply, leafAngle_l, ground_l]
  have hφ0 : ∀ v : Fin (n + 1) → ℝ, (leafAngle θ + ground v) (0 : Fin (n + 1)).castSucc = θ 0 :=
    fun v => by simp only [Pi.add_apply, leafAngle_c, ground_c, ground_zero, add_zero]
  refine ⟨fun k => ?_, ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · change (addLeaf p).P _ = powerInjection (leafB p.B) _ _
      rw [powerInjection_leaf_l, leafAngle_l, leafAngle_c]
      simp [addLeaf]
    · change (addLeaf p).P _ = powerInjection (leafB p.B) _ _
      rw [powerInjection_leaf_c]
      have e : (fun j => leafAngle θ j.castSucc) = θ := by funext j; simp
      rw [e]
      simp only [addLeaf, Fin.snoc_castSucc, leafAngle_c, leafAngle_l]
      split_ifs with h
      · rw [h, sub_self, Real.sin_zero, add_zero]; exact hbal 0
      · rw [add_zero]; exact hbal k
  · obtain ⟨r, hr, hv⟩ := hmin
    have hpotv : ∀ v : Fin (n + 1) → ℝ, potential (addLeaf p) (leafAngle θ + ground v) =
        potential p (θ + ground (fun i => v i.castSucc)) - Real.cos (v (Fin.last n)) := by
      intro v
      rw [potential_leaf, hφ, hφ0, hφl, show θ 0 - (θ 0 + v (Fin.last n)) = -v (Fin.last n) by
        ring, Real.cos_neg]
    have hpot0 : potential (addLeaf p) (leafAngle θ) = potential p θ - 1 := by
      have := hpotv 0
      simp only [ground_zero_vec, add_zero, Pi.zero_apply, Real.cos_zero] at this
      rw [show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl, ground_zero_vec, add_zero] at this
      exact this
    refine ⟨min r 1, lt_min hr one_pos, fun v hv0 hvr => ?_⟩
    have hvr' : ‖(fun i : Fin n => v i.castSucc)‖ < r :=
      (norm_restrict_le v).trans_lt (hvr.trans_le (min_le_left _ _))
    have hy : |v (Fin.last n)| < 1 := by
      have := (norm_le_pi_norm v (Fin.last n)).trans_lt (hvr.trans_le (min_le_right _ _))
      rwa [Real.norm_eq_abs] at this
    have hy' := abs_lt.mp hy
    have hpi := Real.two_le_pi
    refine ⟨?_, fun hcrit => ?_⟩
    · rw [hpotv, hpot0]
      by_cases hR : (fun i : Fin n => v i.castSucc) = 0
      · have hyne : v (Fin.last n) ≠ 0 := fun h => hv0 (eq_zero_of_restrict hR h)
        have hcos : Real.cos (v (Fin.last n)) < 1 := by
          refine lt_of_le_of_ne (Real.cos_le_one _) fun h => hyne ?_
          exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp h
        rw [hR, ground_zero_vec, add_zero]
        linarith
      · have := (hv _ hR hvr').1
        linarith [Real.cos_le_one (v (Fin.last n))]
    · have hl := hcrit (Fin.last _)
      change (addLeaf p).P _ = powerInjection (leafB p.B) _ _ at hl
      rw [powerInjection_leaf_l, hφl, hφ0, add_sub_cancel_left] at hl
      simp only [addLeaf, Fin.snoc_last] at hl
      have hy0 : v (Fin.last n) = 0 :=
        (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).mp hl.symm
      have hR : (fun i : Fin n => v i.castSucc) = 0 := by
        by_contra hR
        refine (hv _ hR hvr').2 fun k => ?_
        have hk := hcrit k.castSucc
        change (addLeaf p).P _ = powerInjection (leafB p.B) _ _ at hk
        rw [powerInjection_leaf_c, hφ] at hk
        simp only [addLeaf, Fin.snoc_castSucc] at hk
        rw [hk]
        split_ifs with h0
        · rw [h0, hφ0, hφl, hy0, add_zero, sub_self, Real.sin_zero, add_zero]
        · rw [add_zero]
      exact hv0 (eq_zero_of_restrict hR hy0)
  · obtain ⟨v, hv0, hker⟩ := hker
    refine ⟨Fin.snoc (α := fun _ => ℝ) v 0, fun h => hv0 ?_, fun k => ?_⟩
    · funext i
      have := congrFun h i.castSucc
      simpa using this
    · have hgc : ∀ j : Fin (n + 1), ground (Fin.snoc (α := fun _ => ℝ) v 0) j.castSucc =
          ground v j := fun j => by
        rw [ground_c]; congr 1; funext i; simp
      have hgl : ground (Fin.snoc (α := fun _ => ℝ) v 0) (Fin.last _) = 0 := by
        rw [ground_l]; simp
      have hsplit : ∀ k : Fin (n + 2), ∑ j, flowWeights (addLeaf p).B (leafAngle θ) k j *
          (ground (Fin.snoc (α := fun _ => ℝ) v 0) k - ground (Fin.snoc (α := fun _ => ℝ) v 0) j) =
          ∑ j : Fin (n + 1), flowWeights (addLeaf p).B (leafAngle θ) k j.castSucc *
            (ground (Fin.snoc (α := fun _ => ℝ) v 0) k -
              ground (Fin.snoc (α := fun _ => ℝ) v 0) j.castSucc) +
          flowWeights (addLeaf p).B (leafAngle θ) k (Fin.last _) *
            (ground (Fin.snoc (α := fun _ => ℝ) v 0) k -
              ground (Fin.snoc (α := fun _ => ℝ) v 0) (Fin.last _)) := fun k =>
        Fin.sum_univ_castSucc _
      rw [hsplit]
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp only [flowWeights, of_apply, hgc, hgl]
        change ∑ j : Fin (n + 1), leafB p.B _ _ * _ * _ + leafB p.B _ _ * _ * _ = 0
        simp only [leafB_lc, leafB_ll, zero_mul, add_zero, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1))]
        simp
      · simp only [flowWeights, of_apply, hgc, hgl]
        change ∑ j : Fin (n + 1), leafB p.B _ _ * _ * _ + leafB p.B _ _ * _ * _ = 0
        simp only [leafB_cc, leafB_cl, leafAngle_c, leafAngle_l]
        rw [show ∑ j : Fin (n + 1), p.B k j * Real.cos (θ k - θ j) * (ground v k - ground v j) =
          ∑ j, flowWeights p.B θ k j * (ground v k - ground v j) from rfl, hker k]
        split_ifs with h0
        · rw [h0]; simp
        · simp


/-! ## The witness for every number of machines -/

/-- A null vector of the linearization weights (a grounded direction `v ≠ 0` with
`∑ⱼ Wₖⱼ (vₖ − vⱼ) = 0` at every machine) is a zero eigenvector of the reduced Jacobian. -/
@[powerlib_foundation] theorem not_isHurwitz_of_kernel {p : Params n} {θ : Fin (n + 1) → ℝ}
    {v : Fin n → ℝ} (hv : v ≠ 0)
    (hker : ∀ k, ∑ j, flowWeights p.B θ k j * (ground v k - ground v j) = 0) :
    ¬ LinearSystems.IsHurwitz (jacobian p θ) := by
  intro hH
  apply Dynamics.mulVec_ne_zero_of_isHurwitz hH (v := fun r => angleState v r)
  · intro h
    apply hv
    funext i
    have := congrFun h (dIdx i)
    simpa using this
  · funext r
    refine Fin.addCases (fun i => ?_) (fun k => ?_) r
    · simp only [mulVec, dotProduct, Pi.zero_apply]
      rw [sum_state]
      simp
    · simp only [mulVec, dotProduct, Pi.zero_apply]
      rw [sum_state]
      simp only [jacobian_wd, jacobian_ww, angleState_dIdx, angleState_wIdx, mul_zero,
        Finset.sum_const_zero, add_zero]
      have hL : ∑ i : Fin n, laplacian (flowWeights p.B θ) k i.succ * v i = 0 := by
        have h1 := laplacian_angleMap p θ (angleState v) k
        simp only [angleState_dIdx, angleMap_angleState, laplacian_mulVec_apply] at h1
        rw [← h1, hker k]
      have e : ∀ i : Fin n, -laplacian (flowWeights p.B θ) k i.succ / p.M k * v i =
          -(laplacian (flowWeights p.B θ) k i.succ * v i) / p.M k := fun i => by ring
      simp only [e, ← Finset.sum_div, Finset.sum_neg_distrib, hL, neg_zero, zero_div]

/-- **A degenerate witness for every number of machines `n + 5`.** Power balance, a strict isolated
minimum of the potential, and a null vector of the linearization weights. -/
@[powerlib_foundation] theorem exists_degenerate (n : ℕ) :
    ∃ p : Params (n + 4), ∃ θ : Fin (n + 4 + 1) → ℝ,
      (∀ k, p.P k = powerInjection p.B θ k) ∧
      (∃ r > 0, ∀ v : Fin (n + 4) → ℝ, v ≠ 0 → ‖v‖ < r →
        potential p θ < potential p (θ + ground v) ∧
          ¬ ∀ k, p.P k = powerInjection p.B (θ + ground v) k) ∧
      (∃ v : Fin (n + 4) → ℝ, v ≠ 0 ∧
        ∀ k, ∑ j, flowWeights p.B θ k j * (ground v k - ground v j) = 0) := by
  induction n with
  | zero =>
    refine ⟨Ring5.params, Ring5.θr, Ring5.balance, Ring5.ring_strictMin,
      ![9, 6, 4, 2], fun h => ?_, Ring5.kernel_ring⟩
    have := congrFun h 0
    norm_num at this
  | succ n ih =>
    obtain ⟨p, θ, hbal, hmin, hker⟩ := ih
    exact ⟨addLeaf p, leafAngle θ, degenerate_addLeaf hbal hmin hker⟩

/-- The five-machine ring as a model of `Swing.family`. -/
def ring5 : Model 4 := ⟨Ring5.params, Ring5.θr⟩

/-- **The five-machine ring is locally asymptotically stable** at its selected angles: a strict,
isolated minimum of the network potential (LaSalle), although the linearization is degenerate. -/
@[powerlib_domain] theorem ring5_mem_den_locallyAsymptoticallyStable :
    connection% (ring5 ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := mem_den_locallyAsymptoticallyStable_iff ring5
  unfold powerlib.TMIO.Statement at h
  exact h.mpr ⟨Ring5.balance, Ring5.ring_strictMin⟩

/-- The reduced Jacobian of the five-machine ring is not Hurwitz (zero eigenvalue along the null
direction `(9, 6, 4, 2)` of the Hessian). Static evidence on the model. -/
@[powerlib_foundation] theorem ring5_not_isHurwitz :
    ¬ LinearSystems.IsHurwitz (jacobian ring5.params ring5.θ) :=
  not_isHurwitz_of_kernel (v := ![9, 6, 4, 2]) (fun h => by
    have := congrFun h 0; norm_num at this) Ring5.kernel_ring

/-- **The local asymptotic translation is not exact for five or more machines** (`n + 5` machines,
every `n`): a ring of five machines, with unit leaves attached for more machines, is locally
asymptotically stable at a power-balance point whose reduced Jacobian has a zero eigenvalue. -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ (family (n := n + 4)).Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  obtain ⟨p, θ, hbal, hmin, v, hv, hker⟩ := exists_degenerate n
  have hmem := mem_den_locallyAsymptoticallyStable_iff (⟨p, θ⟩ : Model (n + 4))
  unfold powerlib.TMIO.Statement at hmem
  have hin := hmem.mpr ⟨hbal, hmin⟩
  rw [← h, TMIO.mem_realize] at hin
  have hj : Meets (⟨p, θ⟩ : Model (n + 4)) .jacobianStable :=
    hin .jacobianStable (by simp [family, translate])
  exact not_isHurwitz_of_kernel hv hker hj

end powerlib.Network.Swing
