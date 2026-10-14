import theorem.Numerics.LinearSchemes

/-! Stability functions of one-step methods on the Dahlquist test equation.

Model boundary: the test equation `ẋ = λ x` with complex `λ` and complex scalar state
(`testField`), fixed real step `h`.  The stability functions are *derived* by applying each
scheme predicate of `LinearSchemes` (and the classical RK4 step `rk4Step`, written for an
arbitrary vector field) to `testField` and are not postulated.  All results are general
numerical-analysis facts (foundation).

Contents.
* Derivations: forward Euler `R(z) = 1 + z`, backward Euler `R(z) = (1 - z)⁻¹`, trapezoidal
  rule `R(z) = (1 + z/2)/(1 - z/2)`, RK4 `R(z) = 1 + z + z²/2 + z³/6 + z⁴/24`.
* Trapezoidal rule: `‖R(z)‖ ≤ 1 ↔ Re z ≤ 0` (exact stability region; A-stable), `R → -1` at
  infinity (not L-stable), and the real-axis ringing statement: for `hλ < -2` every nonzero
  trajectory alternates sign, with per-step multiplier tending to `-1` as `hλ → -∞`.
* Backward Euler: A-stable and `R → 0` at infinity (L-stable); real multiplier in `(0, 1)`.
* Forward Euler: for `λ = -α + iω`, `‖1 + hλ‖ ≤ 1 ↔ h ≤ 2α/(α² + ω²)`; purely imaginary
  nonzero `λ` admits no stable step; real `λ < 0`: `|1 + hλ| < 1 ↔ h < 2/|λ|`.
  For the real recursion `e[k+1] = e[k] + T_s(−α e[k])`: `e[k] = (1 − α T_s)^k e[0]`
  (`eulerFirstOrder_closedForm`), and every trajectory tends to `0` iff `0 < α T_s < 2`
  (`eulerFirstOrder_tendsto_zero_iff`).
* RK4 on the imaginary axis: `‖R(iy)‖ ≤ 1 ↔ |y| ≤ 2√2` (exact).
* A polynomial stability function with `R'(0) = 1` is never A-stable.

Source: work-sync theory/T-numerical-integration.md §1.3, §1.7, §2.1, §2.3;
theory/T-method-of-lines.md §1.5.2–§1.5.3; theory/T-emt-simulation.md §2.3;
theory/T-sde-numerical.md §2.6.

Correction (T-method-of-lines.md §1.5.3 table): the forward-Euler stability region is
`|1 + Δtλ| ≤ 1` (disk centred at `-1`), not `|Δtλ| ≤ 1`; the two sets differ in both
directions (`forwardEuler_region_ne_unitDisk`).  The same table's RK4 value "≈ 2.83" is
`2√2` exactly.
-/

noncomputable section
namespace powerlib.Numerics
open Filter Bornology Complex
open scoped Topology

/-- The Dahlquist test field `ẋ = λ x` on the complex line. -/
def testField (lam : ℂ) (x : ℂ) : ℂ := lam * x

def stabFE (z : ℂ) : ℂ := 1 + z
def stabBE (z : ℂ) : ℂ := (1 - z)⁻¹
def stabTrap (z : ℂ) : ℂ := (1 + z / 2) / (1 - z / 2)
def stabRK4 (z : ℂ) : ℂ := 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24

/-- A-stability of a stability function: `‖R z‖ ≤ 1` on the closed left half-plane. -/
def AStable (R : ℂ → ℂ) : Prop := ∀ z : ℂ, z.re ≤ 0 → ‖R z‖ ≤ 1

/-- L-stability: A-stable and `R z → 0` as `‖z‖ → ∞`. -/
def LStable (R : ℂ → ℂ) : Prop := AStable R ∧ Tendsto R (cobounded ℂ) (𝓝 0)

/-- The classical four-stage Runge–Kutta step for an arbitrary field. -/
def rk4Step {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → E) (h : ℝ) (x : E) : E :=
  let k1 := f x
  let k2 := f (x + (h / 2) • k1)
  let k3 := f (x + (h / 2) • k2)
  let k4 := f (x + h • k3)
  x + (h / 6) • (k1 + (2 : ℝ) • k2 + (2 : ℝ) • k3 + k4)

/-! ### Derivation of the stability functions -/

section Derivation

variable (lam : ℂ) (h : ℝ) (x : ℕ → ℂ)

@[powerlib_foundation] theorem forwardEuler_testEquation :
    IsForwardEulerTrajectory (testField lam) h x ↔ ∀ k, x (k + 1) = stabFE (h * lam) * x k := by
  simp only [IsForwardEulerTrajectory, testField, stabFE, Complex.real_smul]
  refine forall_congr' fun k => ?_
  constructor <;> intro hk <;> rw [hk] <;> ring

@[powerlib_foundation] theorem backwardEuler_testEquation (hne : 1 - h * lam ≠ 0) :
    IsBackwardEulerTrajectory (testField lam) h x ↔ ∀ k, x (k + 1) = stabBE (h * lam) * x k := by
  simp only [IsBackwardEulerTrajectory, testField, stabBE, Complex.real_smul]
  refine forall_congr' fun k => ?_
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  constructor <;> intro hk
  · linear_combination hk
  · linear_combination hk

@[powerlib_foundation] theorem trapezoidal_testEquation (hne : 1 - h * lam / 2 ≠ 0) :
    IsTrapezoidalTrajectory (testField lam) h x ↔ ∀ k, x (k + 1) = stabTrap (h * lam) * x k := by
  simp only [IsTrapezoidalTrajectory, testField, stabTrap, Complex.real_smul]
  refine forall_congr' fun k => ?_
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  push_cast
  constructor <;> intro hk
  · linear_combination hk
  · linear_combination hk

@[powerlib_foundation] theorem rk4Step_testEquation (y : ℂ) :
    rk4Step (testField lam) h y = stabRK4 (h * lam) * y := by
  simp only [rk4Step, testField, stabRK4, Complex.real_smul]
  push_cast
  ring

end Derivation

/-! ### Trapezoidal rule -/

@[powerlib_foundation] theorem stabTrap_norm_le_one_iff {z : ℂ} (hz : z ≠ 2) :
    ‖stabTrap z‖ ≤ 1 ↔ z.re ≤ 0 := by
  have hd : 1 - z / 2 ≠ 0 := by
    intro h0; apply hz; linear_combination -2 * h0
  have hpos : 0 < ‖1 - z / 2‖ := norm_pos_iff.mpr hd
  have key := normSq_one_add_sub_normSq_one_sub (z / 2)
  rw [Complex.div_ofNat_re] at key
  rw [stabTrap, norm_div, div_le_one hpos, ← sq_le_sq₀ (norm_nonneg _) hpos.le,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> linarith

@[powerlib_foundation] theorem stabTrap_norm_lt_one_iff {z : ℂ} (hz : z ≠ 2) :
    ‖stabTrap z‖ < 1 ↔ z.re < 0 := by
  have hd : 1 - z / 2 ≠ 0 := by
    intro h0; apply hz; linear_combination -2 * h0
  have hpos : 0 < ‖1 - z / 2‖ := norm_pos_iff.mpr hd
  have key := normSq_one_add_sub_normSq_one_sub (z / 2)
  rw [Complex.div_ofNat_re] at key
  rw [stabTrap, norm_div, div_lt_one hpos, ← sq_lt_sq₀ (norm_nonneg _) hpos.le,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> linarith

/-- The trapezoidal rule is A-stable. -/
@[powerlib_foundation] theorem trapezoidal_aStable : AStable stabTrap := by
  intro z hz
  have h2 : z ≠ 2 := by
    rintro rfl; norm_num at hz
  exact (stabTrap_norm_le_one_iff h2).mpr hz

@[powerlib_foundation] private lemma tendsto_const_sub_cobounded (c : ℂ) :
    Tendsto (fun z : ℂ => c - z) (cobounded ℂ) (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono (fun z => ?_)
    (tendsto_atTop_add_const_right _ (-‖c‖) tendsto_norm_cobounded_atTop)
  have := norm_sub_norm_le z c
  rw [norm_sub_rev z c] at this
  linarith

/-- `R(∞) = -1` for the trapezoidal rule. -/
@[powerlib_foundation] theorem stabTrap_tendsto_neg_one :
    Tendsto stabTrap (cobounded ℂ) (𝓝 (-1)) := by
  have hlim : Tendsto (fun z : ℂ => -1 + 4 * (2 - z)⁻¹) (cobounded ℂ) (𝓝 (-1)) := by
    have h := ((tendsto_inv₀_cobounded.comp (tendsto_const_sub_cobounded 2)).const_mul
      (4 : ℂ)).const_add (-1 : ℂ)
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [eventually_cobounded_le_norm (3 : ℝ)] with z hz
  have h2 : (2 : ℂ) - z ≠ 0 := by
    intro h0
    have : z = 2 := by linear_combination -h0
    rw [this] at hz; norm_num at hz
  have h2' : 1 - z / 2 ≠ 0 := by
    intro h0; apply h2; linear_combination 2 * h0
  rw [stabTrap]
  field_simp
  ring

/-- The trapezoidal rule is not L-stable. -/
@[powerlib_foundation] theorem trapezoidal_not_lStable : ¬ LStable stabTrap := by
  rintro ⟨-, h0⟩
  have := tendsto_nhds_unique h0 stabTrap_tendsto_neg_one
  norm_num at this

/-- On the negative real axis beyond `-2` the trapezoidal multiplier lies in `(-1, 0)`. -/
@[powerlib_foundation] theorem trapezoidal_real_multiplier_mem {x : ℝ} (hx : x < -2) :
    -1 < (1 + x / 2) / (1 - x / 2) ∧ (1 + x / 2) / (1 - x / 2) < 0 := by
  have hd : 0 < 1 - x / 2 := by linarith
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · exact div_neg_of_neg_of_pos (by linarith) hd

/-- The trapezoidal multiplier tends to `-1` as `hλ → -∞`: stiff modes are not damped. -/
@[powerlib_foundation] theorem trapezoidal_real_multiplier_tendsto :
    Tendsto (fun x : ℝ => (1 + x / 2) / (1 - x / 2)) atBot (𝓝 (-1)) := by
  have hlim : Tendsto (fun x : ℝ => -1 + 4 * (2 - x)⁻¹) atBot (𝓝 (-1)) := by
    have h2 : Tendsto (fun x : ℝ => 2 - x) atBot atTop := by
      simpa [sub_eq_add_neg, add_comm] using tendsto_atTop_add_const_right _ 2 tendsto_neg_atBot_atTop
    have h := ((tendsto_inv_atTop_zero.comp h2).const_mul (4 : ℝ)).const_add (-1 : ℝ)
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  have h2 : (2 : ℝ) - x ≠ 0 := by linarith
  have h2' : 1 - x / 2 ≠ 0 := by linarith
  field_simp
  ring

/-- Trapezoidal ringing: for a real stiff mode with `hλ < -2`, every nonzero trapezoidal
trajectory changes sign at every step. -/
@[powerlib_foundation] theorem trapezoidal_ringing {lam h : ℝ} (hstiff : h * lam < -2)
    {x : ℕ → ℝ} (hx : IsTrapezoidalTrajectory (fun y : ℝ => lam * y) h x) (h0 : x 0 ≠ 0) :
    ∀ k, x (k + 1) * x k < 0 := by
  set r := (1 + h * lam / 2) / (1 - h * lam / 2) with hr
  obtain ⟨hr1, hr0⟩ := trapezoidal_real_multiplier_mem hstiff
  have hd : 1 - h * lam / 2 ≠ 0 := by
    have : 0 < 1 - h * lam / 2 := by linarith
    exact this.ne'
  have hstep : ∀ k, x (k + 1) = r * x k := by
    intro k
    have hk := hx k
    simp only [smul_eq_mul] at hk
    rw [hr, div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination hk
  have hne : ∀ k, x k ≠ 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => rw [hstep k]; exact mul_ne_zero hr0.ne ih
  intro k
  rw [hstep k, mul_assoc]
  exact mul_neg_of_neg_of_pos hr0 (mul_self_pos.mpr (hne k))

/-! ### Backward Euler -/

/-- Backward Euler is A-stable. -/
@[powerlib_foundation] theorem backwardEuler_aStable : AStable stabBE := by
  intro z hz
  have hre : 1 ≤ (1 - z).re := by simp; linarith
  have hn : 1 ≤ ‖1 - z‖ := hre.trans (Complex.re_le_norm _)
  rw [stabBE, norm_inv]
  exact inv_le_one_of_one_le₀ hn

/-- Backward Euler is L-stable: `R(∞) = 0`. -/
@[powerlib_foundation] theorem backwardEuler_lStable : LStable stabBE :=
  ⟨backwardEuler_aStable, tendsto_inv₀_cobounded.comp (tendsto_const_sub_cobounded 1)⟩

/-- On the negative real axis the backward-Euler multiplier lies in `(0, 1)`: no ringing. -/
@[powerlib_foundation] theorem backwardEuler_real_multiplier_mem {x : ℝ} (hx : x < 0) :
    0 < (1 - x)⁻¹ ∧ (1 - x)⁻¹ < 1 := by
  have hd : 1 < 1 - x := by linarith
  exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hd⟩

/-! ### Forward Euler -/

/-- Forward Euler for `λ = -α + iω`: `‖1 + hλ‖ ≤ 1 ↔ h ≤ 2α/(α² + ω²)`. -/
@[powerlib_foundation] theorem forwardEuler_stable_iff {α ω h : ℝ} (hh : 0 < h)
    (hne : α ^ 2 + ω ^ 2 ≠ 0) :
    ‖stabFE (h * (-α + ω * I))‖ ≤ 1 ↔ h ≤ 2 * α / (α ^ 2 + ω ^ 2) := by
  have hpos : 0 < α ^ 2 + ω ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
  have hns : Complex.normSq (stabFE (h * (-α + ω * I))) = (1 - h * α) ^ 2 + (h * ω) ^ 2 := by
    simp [stabFE, Complex.normSq_apply]
    ring
  rw [← sq_le_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq, hns, le_div_iff₀ hpos]
  constructor
  · intro h1; nlinarith
  · intro h1; nlinarith

/-- Forward Euler has no stable positive step for a purely imaginary nonzero eigenvalue. -/
@[powerlib_foundation] theorem forwardEuler_imaginary_unstable {ω h : ℝ} (hω : ω ≠ 0)
    (hh : 0 < h) : 1 < ‖stabFE (h * (ω * I))‖ := by
  have hns : Complex.normSq (stabFE (h * (ω * I))) = 1 + (h * ω) ^ 2 := by
    simp [stabFE, Complex.normSq_apply]
    ring
  have : 1 < Complex.normSq (stabFE (h * (ω * I))) := by
    rw [hns]
    have : 0 < (h * ω) ^ 2 := by positivity
    linarith
  rw [Complex.normSq_eq_norm_sq] at this
  exact (one_lt_sq_iff₀ (norm_nonneg _)).mp this

/-- Forward Euler (and the mean of Euler–Maruyama) for a real decaying mode `λ < 0`:
`|1 + hλ| < 1 ↔ h < 2/|λ|` for `h > 0`. -/
@[powerlib_foundation] theorem forwardEuler_real_stable_iff {lam h : ℝ} (hlam : lam < 0)
    (hh : 0 < h) : |1 + h * lam| < 1 ↔ h < 2 / |lam| := by
  rw [abs_of_neg hlam, lt_div_iff₀ (neg_pos.mpr hlam), abs_lt]
  constructor
  · rintro ⟨h1, -⟩; linarith
  · intro h1; constructor <;> nlinarith

/-- Correction to T-method-of-lines.md §1.5.3: the forward-Euler region `‖1 + z‖ ≤ 1` and the
unit disk `‖z‖ ≤ 1` differ in both directions. -/
@[powerlib_foundation] theorem forwardEuler_region_ne_unitDisk :
    (∃ z : ℂ, ‖z‖ ≤ 1 ∧ 1 < ‖stabFE z‖) ∧ (∃ z : ℂ, ‖stabFE z‖ ≤ 1 ∧ 1 < ‖z‖) := by
  refine ⟨⟨1, by simp, ?_⟩, ⟨-3 / 2, ?_, ?_⟩⟩
  · simp [stabFE]; norm_num
  · simp only [stabFE]
    have : (1 : ℂ) + -3 / 2 = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]; norm_num [abs_of_neg]
  · have : (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]; norm_num [abs_of_neg]

/-! ### Forward Euler on a real first-order loop `ė = −α e` -/

/-- Forward-Euler recursion of `ė = −α e` with period `T_s`: `e[k] = (1 − α T_s)^k e[0]`. -/
@[powerlib_foundation] theorem eulerFirstOrder_closedForm (α Ts : ℝ) (e : ℕ → ℝ)
    (he : ∀ k, e (k + 1) = e k + Ts * (-α * e k)) (k : ℕ) :
    e k = (1 - α * Ts) ^ k * e 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [he, ih, pow_succ]; ring

/-- Forward-Euler stability limit: every forward-Euler trajectory of `ė = −α e` converges to
zero iff `0 < α T_s < 2`. -/
@[powerlib_foundation] theorem eulerFirstOrder_tendsto_zero_iff (α Ts : ℝ) :
    (∀ e : ℕ → ℝ, (∀ k, e (k + 1) = e k + Ts * (-α * e k)) →
        Tendsto e atTop (𝓝 0)) ↔ 0 < α * Ts ∧ α * Ts < 2 := by
  constructor
  · intro h
    have h1 := h (fun k => (1 - α * Ts) ^ k) (fun k => by rw [pow_succ]; ring)
    have h2 := tendsto_pow_atTop_nhds_zero_iff.mp h1
    rw [abs_lt] at h2
    constructor <;> linarith [h2.1, h2.2]
  · rintro ⟨h0, h2⟩ e he
    have hr : |1 - α * Ts| < 1 := by rw [abs_lt]; constructor <;> linarith
    have hpow := (tendsto_pow_atTop_nhds_zero_iff.mpr hr).mul_const (e 0)
    rw [zero_mul] at hpow
    refine hpow.congr fun k => ?_
    rw [eulerFirstOrder_closedForm α Ts e he k]

/-! ### RK4 on the imaginary axis -/

@[powerlib_foundation] theorem stabRK4_imag_normSq (y : ℝ) :
    Complex.normSq (stabRK4 (y * I)) = 1 - y ^ 6 / 72 + y ^ 8 / 576 := by
  have hre : (stabRK4 (y * I)).re = 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
    simp [stabRK4, pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  have him : (stabRK4 (y * I)).im = y - y ^ 3 / 6 := by
    simp [stabRK4, pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  rw [Complex.normSq_apply, hre, him]
  ring

/-- RK4 is stable on the imaginary axis exactly for `|y| ≤ 2√2`. -/
@[powerlib_foundation] theorem rk4_imaginaryAxis_stable_iff (y : ℝ) :
    ‖stabRK4 (y * I)‖ ≤ 1 ↔ |y| ≤ 2 * Real.sqrt 2 := by
  have hs : (2 * Real.sqrt 2) ^ 2 = 8 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h8 : |y| ≤ 2 * Real.sqrt 2 ↔ y ^ 2 ≤ 8 := by
    rw [← hs, ← sq_abs y]
    exact (sq_le_sq₀ (abs_nonneg y) (by positivity)).symm
  rw [h8, ← sq_le_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq, stabRK4_imag_normSq]
  have hfac : 1 - y ^ 6 / 72 + y ^ 8 / 576 = 1 + y ^ 6 * (y ^ 2 - 8) / 576 := by ring
  rw [hfac]
  constructor
  · intro h1
    by_contra h2
    have hy : 0 < y ^ 6 := by
      have : y ≠ 0 := by rintro rfl; norm_num at h2
      positivity
    have : 0 < y ^ 6 * (y ^ 2 - 8) := mul_pos hy (by linarith)
    linarith
  · intro h1
    have : y ^ 6 * (y ^ 2 - 8) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith

/-! ### Polynomial stability functions are never A-stable -/

/-- A nonconstant polynomial exceeds one in modulus somewhere on the open negative real
axis. -/
@[powerlib_foundation] theorem polynomial_exists_neg_real_one_lt (p : Polynomial ℂ)
    (hdeg : 0 < p.degree) : ∃ t : ℝ, 0 < t ∧ 1 < ‖p.eval ((-t : ℝ) : ℂ)‖ := by
  have hz : Tendsto (fun t : ℝ => ‖((-t : ℝ) : ℂ)‖) atTop atTop := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact tendsto_abs_atTop_atTop
  have hlim := Polynomial.tendsto_norm_atTop p hdeg hz
  obtain ⟨t, ht, ht1⟩ :=
    ((hlim.eventually_gt_atTop 1).and (eventually_ge_atTop (1 : ℝ))).exists
  exact ⟨t, by linarith, ht⟩

/-- A polynomial stability function with `R'(0) = 1` (first-order consistency) is not
A-stable; this is the stability-function content of "no explicit Runge–Kutta method is
A-stable". -/
@[powerlib_foundation] theorem polynomial_not_aStable (p : Polynomial ℂ) (hp : p.coeff 1 = 1) :
    ¬ AStable (fun z => p.eval z) := by
  intro hA
  have hdeg : 0 < p.degree := by
    by_contra hle
    have := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hle)
    rw [this, Polynomial.coeff_C] at hp
    simp at hp
  obtain ⟨t, ht0, ht⟩ := polynomial_exists_neg_real_one_lt p hdeg
  have := hA ((-t : ℝ) : ℂ) (by simp; linarith)
  exact absurd this (not_le.mpr ht)

end powerlib.Numerics
