import theorem.Dynamics.LogisticDichotomy
import theorem.Dynamics.VariableRate
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Dispatchable virtual oscillators with set-points: the synchronous set and its attraction

Model boundary.
* `N` grid-forming inverters indexed by a finite type `ι`, each a controllable voltage source with
  the dispatchable virtual oscillator control (dVOC) of Colombino et al.; stationary `αβ` frame,
  state `v ∈ ℂ^ι` (the unit voltages `v_k = v_{α,k} + j v_{β,k}`), continuous time.
* Network: lines with a uniform ratio `ℓ/r`, in quasi-steady state (phasor approximation), line
  weights `w_{jk} = 1/|r_{jk} + jω₀ℓ_{jk}|` (`w_{jk} = w_{kj} ≥ 0` where a result needs it) and the
  common line angle `κ = arctan(ω₀ℓ/r)`: the injected currents are `i_k = e^{−jκ}(L v)_k`,
  `(L v)_k = ∑ⱼ w_{jk}(v_k − v_j)` (`lap`, `current`), so `y = R(κ) i = L v` is measured locally.
  Export-positive complex power `p_k + j q_k = v_k ī_k` (`power`).
* Control law (Colombino et al. (9), (10), (13) with Proposition 3's implementable gain):
  `v̇_k = jω₀ v_k + η (K_k v_k − (L v)_k) + α Φ_k(v_k) v_k`, `K_k = e^{jκ}(p*_k − j q*_k)/v*_k²`,
  `Φ_k(x) = (v*_k − |x|)/v*_k` (`gain`, `amp`, `field`), gains `η, α`, set-points `p*, q*` and
  `v*_k > 0`. The angle profile `θ` (`θ*_{k1}` of the paper, relative to any reference) gives the
  set-point profile `s_k = v*_k e^{jθ_k}` (`profile`) and the paper's gain
  `K^θ_k = ∑ⱼ w_{jk}(1 − (v*_j/v*_k) e^{j(θ_j − θ_k)})` (`angleGain`).
* Excluded: line dynamics, loads and synchronous machines, inner voltage/current loops, current
  limiting, PWM, delays, non-uniform `ℓ/r` ratios, time-varying set-points.

Source: M. Colombino, D. Groß, J.-S. Brouillon, F. Dörfler, "Global phase and magnitude
synchronization of coupled oscillators with application to the control of grid-forming power
inverters", *IEEE Trans. Autom. Control* 64 (2019) 4496–4511 (arXiv:1710.00694): control law (9),
closed loop (10), (13), feasible set-points Definition 2 / (24), Proposition 3 / (25), Condition 1
/ (29), Propositions 6–7, Theorems 1–4; G.-S. Seo et al., APEC 2019 (dVOC experiments); work-sync
`theory/T-voc-dvoc.md` §1.3, §1.5, `theory/papers/@seo2019dvoc.md`.

Results.
Static (the model):
* Set-point consistency (Proposition 3 and its converse): `balanced_zero_iff_powerFlow` — the
  implementable gains equal the angle gains `K^θ` exactly when the power set-points solve the power
  flow `p*_k + j q*_k = s_k ī_k(s)` at the profile. `Balanced θ ω`: the gains are `K^θ + jω`, a
  common frequency shift (consistent set-points for `ω = 0`).
* The synchronous set (`field_mul_profile`): on the profile line `S = ℂ s` of a balanced network
  `f(ζ s) = (j(ω₀ + ηω) + α(1 − |ζ|)) ζ s`; the circle `T = {ζ s : |ζ| = 1}` (every magnitude at
  its set-point, every relative angle at `θ_j − θ_k`) consists of relative equilibria rotating at
  `ω₀ + ηω`, the origin is an equilibrium.
* The decay of the phase error (Propositions 6–7): with `u = v − z(v) s`, `z(v) = ⟨s, v⟩/‖s‖²`
  (`proj`, `err`, `syncError` `V = ‖u‖²`), `sum_re_err_amp_le` (the amplitude feedback expands
  `u` at most at the rate `α`, Chebyshev's sum inequality, (33)) and `sum_re_err_field_le`
  (`∑ Re(ū_k f_k) ≤ (α − ημ) V` when the coupling is dissipative at the rate `μ` off `S`,
  `Dissipative`).
* The profile component (`proj_field`, `norm_projRem_le`): `ż = (j(ω₀ + ηω) + α(1 − |z|)) z + g`
  with `|g| ≤ (1 + |z|) h(√V)`, `h(0) = 0`.
* The stability condition: `angleGain_re`; `dissipative_of_bounds` (a sharp form of (29)): with
  symmetric weights, a connectivity bound `λ` and `Re K^θ_k ≤ ρ` the coupling is dissipative at the
  rate `λγ − ρ`, `γ = |∑ₖ s_k|²/(N‖s‖²)`; `normSq_sum_profile_ge` and `dissipative_of_condition`
  (Condition 1 — angles within `[0, π/2]`, (29) — gives a rate `μ` with `ημ > α`).
* Refuted (the remark after Condition 1, "(29) can always be satisfied by a proper choice of control
  gains and small enough angle set-points" on a connected graph): `twoUnequal_not_condition` — two
  units on one line with `v* = (1, 2)` violate (29) for every angle profile and all gains, while
  `twoUnequal_dissipative` gives the sharp condition at the in-phase profile (rate `13/10`), so the
  conclusion below holds there for `α < 13η/10`.
* Two units with equal set-points `v` on a line of weight `W`: `two_dissipative` (rate `2W`).
Trajectory level (private implementation evidence, Rules §3a; every solution on `[0, ∞)`):
* `syncError_le` (Theorem 2): `V(v(t)) ≤ V(v(0)) e^{2(α − ημ)t}`; for `ημ > α` every solution
  approaches `S` exponentially.
* `tendsto_origin_or_sync` (the attractivity half of Theorem 1, `0 < α < ημ`): every solution
  converges to the origin or to the synchronous set (`V → 0` and `|v_k| → v*_k` for every `k`),
  through the generic logistic dichotomy `Dynamics.LogisticDichotomy.tendsto_zero_or_one` applied
  to `|z|²`. The exceptional set is the basin of the origin, which meets the profile line `S` only
  at the origin (`tendsto_sync_of_profile`: a solution starting on `S \ {0}` stays on `S` and
  synchronizes); `condition_tendsto_origin_or_sync` is the statement under the paper's own
  hypotheses (consistent set-points and Condition 1).
* Two units with equal set-points (`2ηW > α > 0`): the exceptional set is exactly the anti-phase
  plane `{v₀ + v₁ = 0}` — off it every solution synchronizes (`two_tendsto_sync`), on it every
  solution converges to the origin (`two_tendsto_origin`); for `2ηW < α` the anti-phase
  oscillation `v₀ = −v₁ = v(1 − 2ηW/α) e^{j(ω₀+ηω)t}` converges to neither (`two_antiPhase`), so the
  threshold is exact up to equality. The paper's Condition 1 asks `ηW > α` here (a factor two).
* Not proved: that the basin of the origin has Lebesgue measure zero for `N ≥ 3` (Proposition 8
  through Monzón–Potrie): it needs the stable manifold theorem for the hyperbolic origin (its
  linearization `η(K^θ − L) + αI` has the unstable eigenvalue `α` on `S`), the regularity of the
  flow map and its measure-theoretic consequences, which the library does not have; and the
  stability half of Theorem 1 (Theorem 4) as a set-stability statement (no set-stability notion);
  its local, linearized form is the family of `DVOCNetworkLocal`.
-/

noncomputable section
namespace powerlib.GFM
open Complex ComplexConjugate Filter Topology

/-- Parameters of a network of dispatchable virtual oscillators. -/
structure DVOC (ι : Type*) where
  /-- Line weights `w_{jk} = 1/|r_{jk} + jω₀ℓ_{jk}|` (`w_{jk} = w_{kj} ≥ 0`). -/
  w : ι → ι → ℝ
  /-- Common line angle `κ = arctan(ω₀ ℓ/r)`. -/
  κ : ℝ
  /-- Voltage magnitude set-points `v*_k > 0`. -/
  vstar : ι → ℝ
  /-- Active power set-points. -/
  p : ι → ℝ
  /-- Reactive power set-points. -/
  q : ι → ℝ
  /-- Synchronization gain. -/
  η : ℝ
  /-- Amplitude gain. -/
  α : ℝ
  /-- Nominal frequency. -/
  ω0 : ℝ

namespace DVOC

variable {ι : Type*} [Fintype ι] (m : DVOC ι)

/-- The network output `y = R(κ) i_o = L v` (`(L v)_k = ∑ⱼ w_{jk} (v_k − v_j)`). -/
def lap (v : ι → ℂ) (k : ι) : ℂ := ∑ j, (m.w j k : ℂ) * (v k - v j)

/-- The current injected by unit `k` into lines of admittance `w_{jk} e^{−jκ}`. -/
def current (v : ι → ℂ) (k : ι) : ℂ := exp (-(m.κ * I)) * m.lap v k

/-- Complex power `p_k + j q_k = v_k ī_k` injected by unit `k`. -/
def power (v : ι → ℂ) (k : ι) : ℂ := v k * conj (m.current v k)

/-- The implementable controller gain `K_k = e^{jκ} (p*_k − j q*_k)/v*_k²`. -/
def gain (k : ι) : ℂ := exp (m.κ * I) * ((m.p k : ℂ) - m.q k * I) / ((m.vstar k : ℂ) ^ 2)

/-- Scaled magnitude error `Φ_k(x) = (v*_k − |x|)/v*_k`. -/
def amp (k : ι) (x : ℂ) : ℝ := 1 - ‖x‖ / m.vstar k

/-- The dVOC closed loop `v̇_k = jω₀ v_k + η (K_k v_k − (L v)_k) + α Φ_k(v_k) v_k`. -/
def field (v : ι → ℂ) (k : ι) : ℂ :=
  I * m.ω0 * v k + m.η * (m.gain k * v k - m.lap v k) + m.α * (m.amp k (v k) : ℂ) * v k

/-- The set-point profile `s_k = v*_k e^{jθ_k}` of an angle profile `θ`. -/
def profile (θ : ι → ℝ) (k : ι) : ℂ := m.vstar k * exp (θ k * I)

/-- The gain built from the angle set-points, `K^θ_k = ∑ⱼ w_{jk}(1 − (v*_j/v*_k) e^{j(θ_j − θ_k)})`
(Colombino et al. (7)). -/
def angleGain (θ : ι → ℝ) (k : ι) : ℂ := ∑ j, (m.w j k : ℂ) * (1 - m.profile θ j / m.profile θ k)

/-- The power set-points solve the power flow at the profile `θ`: `p*_k + j q*_k = s_k ī_k(s)`. -/
def PowerFlow (θ : ι → ℝ) : Prop := ∀ k, (m.p k : ℂ) + m.q k * I = m.power (m.profile θ) k

/-- The implementable gains are the angle gains up to a common frequency shift `ω`. -/
def Balanced (θ : ι → ℝ) (ω : ℝ) : Prop := ∀ k, m.gain k = m.angleGain θ k + ω * I

/-- `∑ₖ v*_k²`. -/
def mass : ℝ := ∑ k, m.vstar k ^ 2

/-- The common amplitude-phase `z(v) = ⟨s, v⟩ / ‖s‖²` of a state along the profile. -/
def proj (θ : ι → ℝ) (v : ι → ℂ) : ℂ := (∑ k, conj (m.profile θ k) * v k) / m.mass

/-- The phase error `u = v − z(v) s`, the component orthogonal to the profile. -/
def err (θ : ι → ℝ) (v : ι → ℂ) (k : ι) : ℂ := v k - m.proj θ v * m.profile θ k

/-- `V(v) = ‖v‖²_S = ∑ₖ |u_k|²`, the squared distance to the profile line `S = ℂ s`. -/
def syncError (θ : ι → ℝ) (v : ι → ℂ) : ℝ := ∑ k, ‖m.err θ v k‖ ^ 2

/-- The coupling is dissipative at the rate `μ` on the directions orthogonal to the profile:
`Re ⟨u, (K^θ − L) u⟩ ≤ −μ ‖u‖²` for `⟨s, u⟩ = 0`. -/
def Dissipative (θ : ι → ℝ) (μ : ℝ) : Prop :=
  ∀ u : ι → ℂ, ∑ k, conj (m.profile θ k) * u k = 0 →
    ∑ k, (conj (u k) * (m.angleGain θ k * u k - m.lap u k)).re ≤ -μ * ∑ k, ‖u k‖ ^ 2

variable {m}

omit [Fintype ι] in
@[tmio M, powerlib_domain] theorem norm_profile (hv : ∀ k, 0 < m.vstar k) (θ : ι → ℝ) (k : ι) :
    ‖m.profile θ k‖ = m.vstar k := by
  rw [profile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hv k),
    Complex.norm_exp_ofReal_mul_I, mul_one]

omit [Fintype ι] in
@[tmio M, powerlib_domain] theorem conj_profile_mul (θ : ι → ℝ) (k : ι) :
    conj (m.profile θ k) * m.profile θ k = (m.vstar k ^ 2 : ℝ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, profile, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, sq_abs]

omit [Fintype ι] in
@[tmio M, powerlib_domain] theorem profile_ne_zero (hv : ∀ k, 0 < m.vstar k) (θ : ι → ℝ)
    (k : ι) : m.profile θ k ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_profile hv]; exact (hv k).ne'

@[tmio M, powerlib_domain] theorem mass_pos [Nonempty ι] (hv : ∀ k, 0 < m.vstar k) :
    0 < m.mass := by
  obtain ⟨k⟩ := ‹Nonempty ι›
  exact lt_of_lt_of_le (pow_pos (hv k) 2)
    (Finset.single_le_sum (fun j _ => sq_nonneg (m.vstar j)) (Finset.mem_univ k))

@[tmio M, powerlib_domain] theorem sum_conj_profile_mul_profile (θ : ι → ℝ) :
    ∑ k, conj (m.profile θ k) * m.profile θ k = (m.mass : ℂ) := by
  simp only [conj_profile_mul, mass]; push_cast; rfl

/-- The phase error is orthogonal to the profile. -/
@[tmio M, powerlib_domain] theorem sum_conj_profile_err (hm : m.mass ≠ 0) (θ : ι → ℝ)
    (v : ι → ℂ) : ∑ k, conj (m.profile θ k) * m.err θ v k = 0 := by
  simp only [err, mul_sub, Finset.sum_sub_distrib]
  have h : ∑ k, conj (m.profile θ k) * (m.proj θ v * m.profile θ k) =
      m.proj θ v * m.mass := by
    rw [← sum_conj_profile_mul_profile θ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h, proj, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hm), sub_self]

/-- The angle gain annihilates the profile: `K^θ_k s_k = (L s)_k` (`(K^θ − L) s = 0`). -/
@[tmio M, powerlib_domain] theorem angleGain_mul_profile (hv : ∀ k, 0 < m.vstar k)
    (θ : ι → ℝ) (k : ι) : m.angleGain θ k * m.profile θ k = m.lap (m.profile θ) k := by
  have hs := profile_ne_zero hv θ k
  simp only [angleGain, lap, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- **Set-point consistency.** The implementable gains `K_k = e^{jκ}(p*_k − j q*_k)/v*_k²` are the
angle gains `K^θ_k` of the profile `θ` exactly when the power set-points solve the power flow at
`θ` (Colombino et al. Proposition 3, and its converse). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem balanced_zero_iff_powerFlow (hv : ∀ k, 0 < m.vstar k)
    (θ : ι → ℝ) : m.Balanced θ 0 ↔ m.PowerFlow θ := by
  refine forall_congr' fun k => ?_
  have hs := profile_ne_zero hv θ k
  have hc : conj (m.profile θ k) ≠ 0 := (map_ne_zero _).mpr hs
  have hK : m.angleGain θ k = m.lap (m.profile θ) k / m.profile θ k := by
    rw [← angleGain_mul_profile hv θ k, mul_div_cancel_right₀ _ hs]
  have hcs : (m.vstar k : ℂ) ^ 2 = conj (m.profile θ k) * m.profile θ k := by
    rw [conj_profile_mul]; push_cast; ring
  have hce : conj (exp (-(m.κ * I))) = exp (m.κ * I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have hce' : conj (exp (m.κ * I)) = exp (-(m.κ * I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have he : exp (-(m.κ * I)) * exp (m.κ * I) = 1 := by rw [← Complex.exp_add]; simp
  have hA : conj ((m.p k : ℂ) - m.q k * I) = (m.p k : ℂ) + m.q k * I := by
    simp [Complex.conj_ofReal]
  set A : ℂ := (m.p k : ℂ) - m.q k * I
  set E : ℂ := exp (m.κ * I)
  set E' : ℂ := exp (-(m.κ * I))
  set L := m.lap (m.profile θ) k
  set s := m.profile θ k
  simp only [ofReal_zero, zero_mul, add_zero, gain, power, current, hK]
  change E * A / (m.vstar k : ℂ) ^ 2 = L / s ↔ (m.p k : ℂ) + m.q k * I = s * conj (E' * L)
  rw [hcs, ← hA, map_mul, hce]
  constructor
  · intro h
    have h1 : E * A = L * conj s := by
      field_simp at h
      linear_combination h
    have h2 : A = E' * (L * conj s) := by
      rw [← h1, ← mul_assoc, he, one_mul]
    rw [h2, map_mul, map_mul, Complex.conj_conj, hce]
    ring
  · intro h
    have h2 := congrArg conj h
    rw [Complex.conj_conj, map_mul, map_mul, Complex.conj_conj, hce'] at h2
    rw [h2]
    field_simp
    linear_combination L * he

/-- The network output is linear: `L(u + c s) = L u + c L s`. -/
@[tmio M, powerlib_domain] theorem lap_add_mul (u w : ι → ℂ) (c : ℂ) (k : ι) :
    m.lap (fun j => u j + c * w j) k = m.lap u k + c * m.lap w k := by
  simp only [lap, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype ι] in
@[tmio M, powerlib_domain] theorem amp_mul_profile (hv : ∀ k, 0 < m.vstar k) (θ : ι → ℝ)
    (ζ : ℂ) (k : ι) : m.amp k (ζ * m.profile θ k) = 1 - ‖ζ‖ := by
  rw [amp, norm_mul, norm_profile hv, mul_div_assoc, div_self (hv k).ne', mul_one]

/-- **The synchronous set.** On the profile line `S = ℂ s` of a balanced network the field is
`(j(ω₀ + ηω) + α(1 − |ζ|)) ζ s`: `S` is invariant, the origin is an equilibrium and the circle
`T = {ζ s : |ζ| = 1}` (correct magnitudes `|v_k| = v*_k` and relative angles `θ_k − θ_j`) consists
of the relative equilibria rotating at `ω₀ + ηω` (for `ω = 0`, consistent set-points, at `ω₀`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem field_mul_profile (hv : ∀ k, 0 < m.vstar k) {θ : ι → ℝ}
    {ω : ℝ} (hb : m.Balanced θ ω) (ζ : ℂ) (k : ι) :
    m.field (fun j => ζ * m.profile θ j) k =
      (I * (m.ω0 + m.η * ω) + m.α * (1 - ‖ζ‖)) * (ζ * m.profile θ k) := by
  have hL : m.lap (fun j => ζ * m.profile θ j) k = ζ * (m.angleGain θ k * m.profile θ k) := by
    have := lap_add_mul (m := m) (fun _ => 0) (m.profile θ) ζ k
    simp only [zero_add] at this
    rw [this, angleGain_mul_profile hv]
    simp [lap]
  simp only [field, hL, amp_mul_profile hv, hb k]
  push_cast
  ring

/-- The state splits as `v = u + z(v) s`. -/
@[tmio M, powerlib_domain] theorem err_add_proj (θ : ι → ℝ) (v : ι → ℂ) :
    v = fun k => m.err θ v k + m.proj θ v * m.profile θ k := by
  funext k; simp [err]

@[tmio M, powerlib_domain] theorem sum_conj_err_mul_profile (hm : m.mass ≠ 0) (θ : ι → ℝ)
    (v : ι → ℂ) : ∑ k, conj (m.err θ v k) * m.profile θ k = 0 := by
  have h := congrArg conj (sum_conj_profile_err hm θ v)
  rw [map_sum, map_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, Complex.conj_conj, mul_comm]

/-- A rotation `jΩ v` does no work on the phase error: `∑ₖ Re(ū_k jΩ v_k) = 0`. -/
@[tmio M, powerlib_domain] theorem sum_re_err_rot (hm : m.mass ≠ 0) (θ : ι → ℝ) (v : ι → ℂ)
    (Ω : ℝ) : ∑ k, (conj (m.err θ v k) * (I * Ω * v k)).re = 0 := by
  have hsplit : ∀ k, conj (m.err θ v k) * (I * Ω * v k) =
      I * Ω * ((‖m.err θ v k‖ ^ 2 : ℝ) : ℂ) +
        I * Ω * m.proj θ v * (conj (m.err θ v k) * m.profile θ k) := by
    intro k
    conv_lhs => rw [show v k = m.err θ v k + m.proj θ v * m.profile θ k by simp [err]]
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    ring
  simp only [hsplit, ← Complex.re_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_conj_err_mul_profile hm, mul_zero, add_zero]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.im_sum]
  simp

/-- The Chebyshev sum inequality `(∑ a_j²)(∑ x_k³/a_k) ≥ (∑ a_j x_j)(∑ x_k²)` for `a > 0`,
`x ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem chebyshev {a x : ι → ℝ} (ha : ∀ k, 0 < a k)
    (hx : ∀ k, 0 ≤ x k) :
    (∑ j, a j * x j) * ∑ k, x k ^ 2 ≤ (∑ j, a j ^ 2) * ∑ k, x k ^ 3 / a k := by
  set T : ι → ι → ℝ := fun j k => a j ^ 2 * (x k ^ 3 / a k) - a j * x j * x k ^ 2
  have hsum : (∑ j, a j ^ 2) * (∑ k, x k ^ 3 / a k) - (∑ j, a j * x j) * ∑ k, x k ^ 2 =
      ∑ j, ∑ k, T j k := by
    simp only [T, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  have hpair : ∀ j k, 0 ≤ T j k + T k j := by
    intro j k
    have haj := ha j
    have hak := ha k
    have hid : T j k + T k j = (a j * x k + a k * x j) * (a j * x k - a k * x j) ^ 2 /
        (a j * a k) := by
      simp only [T]
      field_simp
      ring
    rw [hid]
    have := hx j; have := hx k
    positivity
  have hsym : ∑ j, ∑ k, T j k = ∑ j, ∑ k, T k j := Finset.sum_comm
  have h2 : 0 ≤ ∑ j, ∑ k, (T j k + T k j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hpair j k
  simp only [Finset.sum_add_distrib] at h2
  linarith

/-- **The amplitude feedback expands the phase error at most at the rate `α`** (Colombino et al.
(33)): `∑ₖ Re(ū_k Φ_k(v_k) v_k) ≤ ‖u‖²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sum_re_err_amp_le [Nonempty ι] (hv : ∀ k, 0 < m.vstar k)
    (θ : ι → ℝ) (v : ι → ℂ) :
    ∑ k, (conj (m.err θ v k) * ((m.amp k (v k) : ℂ) * v k)).re ≤ m.syncError θ v := by
  have hm := (mass_pos hv).ne'
  set z := m.proj θ v
  set s := m.profile θ
  set u := m.err θ v
  have hvk : ∀ k, v k = u k + z * s k := fun k => by simp [u, err, z, s]
  -- the linear part is the error itself
  have hlin : ∑ k, (conj (u k) * v k).re = m.syncError θ v := by
    have h1 : ∀ k, (conj (u k) * v k).re = ‖u k‖ ^ 2 + (z * (conj (u k) * s k)).re := by
      intro k
      rw [hvk k, mul_add, Complex.add_re, ← Complex.normSq_eq_norm_sq, mul_comm (conj (u k)),
        Complex.mul_conj, Complex.ofReal_re]
      ring_nf
    simp only [h1, Finset.sum_add_distrib, syncError]
    rw [← Complex.re_sum, ← Finset.mul_sum, sum_conj_err_mul_profile hm θ v, mul_zero,
      Complex.zero_re, add_zero]
  -- the cubic part is nonnegative
  set x : ι → ℝ := fun k => ‖v k‖
  set W : ℂ := ∑ k, ((x k / m.vstar k : ℝ) : ℂ) * (conj (s k) * v k)
  have hre : ∀ k, (conj (u k) * v k).re = x k ^ 2 - (conj z * (conj (s k) * v k)).re := by
    intro k
    rw [show u k = v k - z * s k by simp [u, err, z, s], map_sub, map_mul, sub_mul,
      Complex.sub_re, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [x, mul_assoc]
  have hcubeq : ∑ k, x k / m.vstar k * (conj (u k) * v k).re =
      ∑ k, x k ^ 3 / m.vstar k - (conj z * W).re := by
    simp only [hre, W, Finset.mul_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show conj z * (((x k / m.vstar k : ℝ) : ℂ) * (conj (s k) * v k)) =
      ((x k / m.vstar k : ℝ) : ℂ) * (conj z * (conj (s k) * v k)) by ring, Complex.re_ofReal_mul]
    ring
  have hW : ‖W‖ ≤ ∑ k, x k ^ 2 := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj,
      norm_profile hv, abs_of_nonneg (div_nonneg (norm_nonneg _) (hv k).le)]
    simp only [x]
    field_simp [(hv k).ne']
  have hz : ‖z‖ ≤ (∑ k, m.vstar k * x k) / m.mass := by
    rw [show z = (∑ k, conj (s k) * v k) / m.mass from rfl, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mass_pos hv)]
    refine div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
      (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))) (mass_pos hv).le
    rw [norm_mul, Complex.norm_conj, norm_profile hv]
  have hcheb := chebyshev (a := m.vstar) (x := x) hv (fun k => norm_nonneg _)
  have hzW : (conj z * W).re ≤ ∑ k, x k ^ 3 / m.vstar k := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    calc ‖z‖ * ‖W‖ ≤ (∑ k, m.vstar k * x k) / m.mass * ∑ k, x k ^ 2 :=
          mul_le_mul hz hW (norm_nonneg _)
            (div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hv k).le (norm_nonneg _))
              (mass_pos hv).le)
      _ ≤ ∑ k, x k ^ 3 / m.vstar k := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (mass_pos hv), mul_comm _ m.mass]
          exact hcheb
  have hcub : 0 ≤ ∑ k, x k / m.vstar k * (conj (u k) * v k).re := by
    rw [hcubeq]; linarith
  have hsplit : ∀ k, (conj (u k) * ((m.amp k (v k) : ℂ) * v k)).re =
      (conj (u k) * v k).re - x k / m.vstar k * (conj (u k) * v k).re := by
    intro k
    rw [show conj (u k) * ((m.amp k (v k) : ℂ) * v k) =
      ((m.amp k (v k) : ℝ) : ℂ) * (conj (u k) * v k) by ring, Complex.re_ofReal_mul, amp]
    ring
  simp only [hsplit, Finset.sum_sub_distrib, hlin]
  linarith

/-- The balanced field in the splitting `v = u + z s`:
`f_k(v) = j(ω₀ + ηω) v_k + η (K^θ_k u_k − (L u)_k) + α Φ_k(v_k) v_k`. -/
@[tmio M, powerlib_domain] theorem field_eq_split (hv : ∀ k, 0 < m.vstar k) {θ : ι → ℝ}
    {ω : ℝ} (hb : m.Balanced θ ω) (v : ι → ℂ) (k : ι) :
    m.field v k = I * ((m.ω0 + m.η * ω : ℝ) : ℂ) * v k +
      (m.η : ℂ) * (m.angleGain θ k * m.err θ v k - m.lap (m.err θ v) k) +
        (m.α : ℂ) * ((m.amp k (v k) : ℂ) * v k) := by
  have hlv : m.lap v k = m.lap (m.err θ v) k +
      m.proj θ v * (m.angleGain θ k * m.profile θ k) := by
    rw [angleGain_mul_profile hv, ← lap_add_mul]
    congr 1
    exact err_add_proj θ v
  have hvk : v k = m.err θ v k + m.proj θ v * m.profile θ k := by simp [err]
  rw [field, hb k, hlv]
  push_cast
  linear_combination ((m.η : ℂ) * m.angleGain θ k) * hvk

/-- **The phase error decays** (Colombino et al. Propositions 6–7, static form): for a balanced
network whose coupling is dissipative at the rate `μ` off the profile,
`∑ₖ Re(ū_k f_k(v)) ≤ (α − ημ) ‖u‖²` for every state (`η, α ≥ 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sum_re_err_field_le [Nonempty ι] (hv : ∀ k, 0 < m.vstar k)
    {θ : ι → ℝ} {ω μ : ℝ} (hb : m.Balanced θ ω) (hd : m.Dissipative θ μ) (hη : 0 ≤ m.η)
    (hα : 0 ≤ m.α) (v : ι → ℂ) :
    ∑ k, (conj (m.err θ v k) * m.field v k).re ≤ (m.α - m.η * μ) * m.syncError θ v := by
  have hm := (mass_pos hv).ne'
  have hk : ∀ k, (conj (m.err θ v k) * m.field v k).re =
      (conj (m.err θ v k) * (I * ((m.ω0 + m.η * ω : ℝ) : ℂ) * v k)).re +
        m.η * (conj (m.err θ v k) * (m.angleGain θ k * m.err θ v k - m.lap (m.err θ v) k)).re +
          m.α * (conj (m.err θ v k) * ((m.amp k (v k) : ℂ) * v k)).re := by
    intro k
    rw [field_eq_split hv hb v k, mul_add, mul_add, Complex.add_re, Complex.add_re,
      show conj (m.err θ v k) * ((m.η : ℂ) *
        (m.angleGain θ k * m.err θ v k - m.lap (m.err θ v) k)) = (m.η : ℂ) *
        (conj (m.err θ v k) * (m.angleGain θ k * m.err θ v k - m.lap (m.err θ v) k)) by ring,
      show conj (m.err θ v k) * ((m.α : ℂ) * ((m.amp k (v k) : ℂ) * v k)) = (m.α : ℂ) *
        (conj (m.err θ v k) * ((m.amp k (v k) : ℂ) * v k)) by ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp only [hk, Finset.sum_add_distrib, ← Finset.mul_sum, sum_re_err_rot hm]
  have h1 := hd (m.err θ v) (sum_conj_profile_err hm θ v)
  have h2 := sum_re_err_amp_le hv θ v
  have h1' := mul_le_mul_of_nonneg_left h1 hη
  have h2' := mul_le_mul_of_nonneg_left h2 hα
  simp only [syncError] at h1' h2' ⊢
  nlinarith

/-- `‖|x| x − |y| y‖ ≤ (|x| + |y|) ‖x − y‖`. -/
@[tmio T, powerlib_foundation] private theorem norm_norm_smul_sub_le (x y : ℂ) :
    ‖(‖x‖ : ℂ) * x - (‖y‖ : ℂ) * y‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have h : (‖x‖ : ℂ) * x - (‖y‖ : ℂ) * y = (‖x‖ : ℂ) * (x - y) + ((‖x‖ - ‖y‖ : ℝ) : ℂ) * y := by
    push_cast; ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_norm]
  have := abs_norm_sub_norm_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y),
    mul_le_mul_of_nonneg_right this (norm_nonneg y)]

/-- The remainder of the profile component: `ż = j(ω₀ + ηω) z + α(1 − |z|) z + g(v)`. -/
def projRem (θ : ι → ℝ) (v : ι → ℂ) : ℂ :=
  ((m.η : ℂ) * ∑ k, conj (m.profile θ k) * (m.angleGain θ k * m.err θ v k - m.lap (m.err θ v) k) -
    (m.α : ℂ) * ∑ k, conj (m.profile θ k) *
      (((‖v k‖ : ℂ) * v k - (‖m.proj θ v * m.profile θ k‖ : ℂ) *
        (m.proj θ v * m.profile θ k)) / (m.vstar k : ℂ))) / (m.mass : ℂ)

/-- **The profile component obeys the logistic oscillator up to the phase error**:
`⟨s, f(v)⟩/‖s‖² = (j(ω₀ + ηω) + α(1 − |z|)) z + g(v)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem proj_field [Nonempty ι] (hv : ∀ k, 0 < m.vstar k)
    {θ : ι → ℝ} {ω : ℝ} (hb : m.Balanced θ ω) (v : ι → ℂ) :
    (∑ k, conj (m.profile θ k) * m.field v k) / (m.mass : ℂ) =
      (I * ((m.ω0 + m.η * ω : ℝ) : ℂ) + (m.α : ℂ) * ((1 - ‖m.proj θ v‖ : ℝ) : ℂ)) *
        m.proj θ v + m.projRem θ v := by
  have hm : (m.mass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mass_pos hv).ne'
  set z := m.proj θ v
  set s := m.profile θ
  set Ω : ℂ := ((m.ω0 + m.η * ω : ℝ) : ℂ)
  set A := ∑ k, conj (s k) * (m.angleGain θ k * m.err θ v k - m.lap (m.err θ v) k)
  set B := ∑ k, conj (s k) * ((‖v k‖ : ℂ) * v k / (m.vstar k : ℂ))
  set C := ∑ k, conj (s k) * ((‖z * s k‖ : ℂ) * (z * s k) / (m.vstar k : ℂ))
  have hsv : ∑ k, conj (s k) * v k = z * m.mass := by
    simp only [z, proj, s]; field_simp
  have hC : C = (‖z‖ : ℂ) * z * m.mass := by
    simp only [C]
    rw [← sum_conj_profile_mul_profile θ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (m.vstar k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hv k).ne'
    rw [norm_mul, norm_profile hv]
    push_cast
    simp only [s]
    field_simp
  have hterm : ∀ k, conj (s k) * m.field v k = I * Ω * (conj (s k) * v k) +
      (m.η : ℂ) * (conj (s k) * (m.angleGain θ k * m.err θ v k - m.lap (m.err θ v) k)) +
        (m.α : ℂ) * (conj (s k) * v k - conj (s k) * ((‖v k‖ : ℂ) * v k / (m.vstar k : ℂ))) := by
    intro k
    have hk : (m.vstar k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hv k).ne'
    rw [field_eq_split hv hb v k]
    simp only [amp, Ω]
    push_cast
    field_simp
  have hsum : ∑ k, conj (s k) * m.field v k = I * Ω * (z * m.mass) + (m.η : ℂ) * A +
      (m.α : ℂ) * (z * m.mass - B) := by
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsv]
    rfl
  have hrem : m.projRem θ v * m.mass = (m.η : ℂ) * A - (m.α : ℂ) * (B - C) := by
    rw [projRem, div_mul_cancel₀ _ hm]
    congr 2
    simp only [B, C, ← Finset.sum_sub_distrib, ← mul_sub, sub_div]
    rfl
  rw [div_eq_iff hm, add_mul, hrem, hsum, hC]
  push_cast
  ring

@[tmio M, powerlib_domain] theorem norm_err_le_sqrt (θ : ι → ℝ) (v : ι → ℂ) (j : ι) :
    ‖m.err θ v j‖ ≤ Real.sqrt (m.syncError θ v) :=
  Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun k => ‖m.err θ v k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j))

/-- The constant `C₁ = ∑ₖ v*_k (|K^θ_k| + 2 ∑ⱼ |w_{jk}|)` bounding the coupling remainder. -/
def remConst (θ : ι → ℝ) : ℝ :=
  ∑ k, m.vstar k * (‖m.angleGain θ k‖ + 2 * ∑ j, |m.w j k|)

/-- The bound `h(r) = (η C₁ r + 2α (∑ v*) r + α N r²)/‖s‖²` on the remainder at `r = √V`. -/
def remBound (θ : ι → ℝ) (r : ℝ) : ℝ :=
  (m.η * m.remConst θ * r + 2 * m.α * (∑ k, m.vstar k) * r +
    m.α * Fintype.card ι * r ^ 2) / m.mass

/-- The coupling remainder is bounded by the phase error:
`|∑ₖ s̄_k (K^θ_k u_k − (L u)_k)| ≤ C₁ ‖u‖`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem norm_sum_conj_profile_coupling_le (hv : ∀ k, 0 < m.vstar k)
    (θ : ι → ℝ) (u : ι → ℂ) :
    ‖∑ k, conj (m.profile θ k) * (m.angleGain θ k * u k - m.lap u k)‖ ≤
      m.remConst θ * Real.sqrt (∑ k, ‖u k‖ ^ 2) := by
  set r := Real.sqrt (∑ k, ‖u k‖ ^ 2)
  have hu : ∀ j, ‖u j‖ ≤ r := fun j => Real.le_sqrt_of_sq_le (Finset.single_le_sum
    (f := fun k => ‖u k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
  refine (norm_sum_le _ _).trans ?_
  rw [remConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, Complex.norm_conj, norm_profile hv, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hv k).le
  have hL : ‖m.lap u k‖ ≤ (2 * ∑ j, |m.w j k|) * r := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := (norm_sub_le (u k) (u j)).trans (add_le_add (hu k) (hu j))
    nlinarith [abs_nonneg (m.w j k)]
  have h1 : ‖m.angleGain θ k * u k‖ ≤ ‖m.angleGain θ k‖ * r := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hu k) (norm_nonneg _)
  calc ‖m.angleGain θ k * u k - m.lap u k‖ ≤ ‖m.angleGain θ k‖ * r + (2 * ∑ j, |m.w j k|) * r :=
        (norm_sub_le _ _).trans (add_le_add h1 hL)
    _ = (‖m.angleGain θ k‖ + 2 * ∑ j, |m.w j k|) * r := by ring

/-- The remainder is small with the phase error: `|g(v)| ≤ (1 + |z|) h(√V)`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem norm_projRem_le [Nonempty ι] (hv : ∀ k, 0 < m.vstar k)
    (hη : 0 ≤ m.η) (hα : 0 ≤ m.α) (θ : ι → ℝ) (v : ι → ℂ) :
    ‖m.projRem θ v‖ ≤ (1 + ‖m.proj θ v‖) * m.remBound θ (Real.sqrt (m.syncError θ v)) := by
  have hmp := mass_pos hv
  set r := Real.sqrt (m.syncError θ v)
  set z := m.proj θ v
  set u := m.err θ v
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hu : ∀ j, ‖u j‖ ≤ r := norm_err_le_sqrt θ v
  -- the coupling part
  have hA : ‖∑ k, conj (m.profile θ k) * (m.angleGain θ k * u k - m.lap u k)‖ ≤
      m.remConst θ * r := norm_sum_conj_profile_coupling_le hv θ u
  -- the amplitude part
  have hB : ‖∑ k, conj (m.profile θ k) * (((‖v k‖ : ℂ) * v k -
      (‖z * m.profile θ k‖ : ℂ) * (z * m.profile θ k)) / (m.vstar k : ℂ))‖ ≤
      2 * ‖z‖ * (∑ k, m.vstar k) * r + Fintype.card ι * r ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    have hk : ∀ k, ‖conj (m.profile θ k) * (((‖v k‖ : ℂ) * v k -
        (‖z * m.profile θ k‖ : ℂ) * (z * m.profile θ k)) / (m.vstar k : ℂ))‖ ≤
        2 * ‖z‖ * m.vstar k * r + r ^ 2 := by
      intro k
      rw [norm_mul, norm_div, Complex.norm_conj, norm_profile hv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (hv k), mul_div_cancel₀ _ (hv k).ne']
      have hvz : v k - z * m.profile θ k = u k := by simp [u, err, z]
      have h1 := norm_norm_smul_sub_le (v k) (z * m.profile θ k)
      rw [hvz] at h1
      have hzs : ‖z * m.profile θ k‖ = ‖z‖ * m.vstar k := by rw [norm_mul, norm_profile hv]
      have h2 : ‖v k‖ ≤ r + ‖z‖ * m.vstar k := by
        have : v k = u k + z * m.profile θ k := by simp [u, err, z]
        rw [this]
        refine (norm_add_le _ _).trans (add_le_add (hu k) ?_)
        rw [norm_mul, norm_profile hv]
      refine h1.trans ?_
      rw [hzs]
      have := hu k
      have hzv : 0 ≤ ‖z‖ * m.vstar k := mul_nonneg (norm_nonneg _) (hv k).le
      nlinarith [norm_nonneg (u k)]
    refine (Finset.sum_le_sum fun k _ => hk k).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum,
      Finset.sum_mul]
  -- assemble
  rw [projRem, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmp, remBound,
    mul_div_assoc', div_le_div_iff_of_pos_right hmp]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hη, abs_of_nonneg hα]
  have e1 := mul_le_mul_of_nonneg_left hA hη
  have e2 := mul_le_mul_of_nonneg_left hB hα
  have hz := norm_nonneg z
  have hC1 : 0 ≤ m.remConst θ := Finset.sum_nonneg fun k _ => mul_nonneg (hv k).le
    (add_nonneg (norm_nonneg _) (mul_nonneg zero_le_two (Finset.sum_nonneg fun j _ =>
      abs_nonneg _)))
  have hS : 0 ≤ ∑ k, m.vstar k := Finset.sum_nonneg fun k _ => (hv k).le
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have f1 : 0 ≤ m.η * m.remConst θ * r := by positivity
  have f2 : 0 ≤ m.α * (∑ k, m.vstar k) * r := by positivity
  have f3 : 0 ≤ m.α * Fintype.card ι * r ^ 2 := by positivity
  nlinarith [mul_nonneg hz f1, mul_nonneg hz f2, mul_nonneg hz f3]

/-! ## The stability condition -/

/-- `Re K^θ_k = ∑ⱼ w_{jk} (1 − (v*_j/v*_k) cos(θ_j − θ_k))`. -/
@[tmio M, powerlib_domain] theorem angleGain_re (hv : ∀ k, 0 < m.vstar k) (θ : ι → ℝ) (k : ι) :
    (m.angleGain θ k).re =
      ∑ j, m.w j k * (1 - m.vstar j / m.vstar k * Real.cos (θ j - θ k)) := by
  rw [angleGain, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hk : (m.vstar k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hv k).ne'
  have hq : m.profile θ j / m.profile θ k =
      ((m.vstar j / m.vstar k : ℝ) : ℂ) * exp (((θ j - θ k : ℝ) : ℂ) * I) := by
    rw [profile, profile, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    push_cast
    field_simp
  rw [hq, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

/-- For `⟨s, u⟩ = 0`: `|∑ₖ u_k|² ≤ (N − |∑ₖ s_k|²/‖s‖²) ‖u‖²` (Cauchy–Schwarz against the
component of `𝟙` orthogonal to the profile). -/
@[tmio M, powerlib_domain] private theorem normSq_sum_le [Nonempty ι] (hv : ∀ k, 0 < m.vstar k)
    (θ : ι → ℝ) {u : ι → ℂ} (hu : ∑ k, conj (m.profile θ k) * u k = 0) :
    ‖∑ k, u k‖ ^ 2 ≤ (Fintype.card ι - ‖∑ k, m.profile θ k‖ ^ 2 / m.mass) * ∑ k, ‖u k‖ ^ 2 := by
  have hmp := mass_pos hv
  set S := ∑ k, m.profile θ k
  set β : ℂ := conj S / (m.mass : ℂ)
  have hsum : ∑ k, u k = ∑ k, conj (1 - β * m.profile θ k) * u k := by
    simp only [map_sub, map_one, map_mul, sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [show ∑ k, conj β * conj (m.profile θ k) * u k =
      conj β * ∑ k, conj (m.profile θ k) * u k by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hu, mul_zero,
      sub_zero]
  have hb : ∑ k, ‖1 - β * m.profile θ k‖ ^ 2 = Fintype.card ι - ‖S‖ ^ 2 / m.mass := by
    have hk : ∀ k, ‖1 - β * m.profile θ k‖ ^ 2 =
        1 + ‖β‖ ^ 2 * m.vstar k ^ 2 - 2 * (conj β * conj (m.profile θ k)).re := by
      intro k
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one,
        Complex.normSq_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
        norm_profile hv, one_mul, map_mul]
    simp only [hk, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum, ← Complex.re_sum]
    rw [← map_sum, show (∑ k, m.vstar k ^ 2) = m.mass from rfl]
    have hβ : ‖β‖ ^ 2 * m.mass = ‖S‖ ^ 2 / m.mass := by
      rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmp]
      field_simp
    have hβS : (conj β * conj S).re = ‖S‖ ^ 2 / m.mass := by
      rw [show conj β * conj S = ((‖S‖ ^ 2 / m.mass : ℝ) : ℂ) by
        simp only [β, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
        rw [mul_comm, mul_div_assoc', Complex.conj_mul', ← Complex.ofReal_pow]
        push_cast; ring, Complex.ofReal_re]
    rw [hβ, hβS]
    ring
  rw [hsum, ← hb]
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans
    (le_of_eq (Finset.sum_congr rfl fun k _ => by rw [norm_mul, Complex.norm_conj]))) 2) ?_
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **A sharp dissipativity bound.** With symmetric weights, a lower bound `λ ≥ 0` on the
algebraic connectivity (`λ ∑ₖ (x_k − x̄)² ≤ ½ ∑ⱼ ∑ₖ w_{jk}(x_j − x_k)²` for real `x`) and
`Re K^θ_k ≤ ρ`, the coupling is dissipative at the rate `λ γ − ρ` with
`γ = |∑ₖ s_k|² / (N ‖s‖²)`, the squared cosine of the angle between the profile and `𝟙`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dissipative_of_bounds [Nonempty ι] (hv : ∀ k, 0 < m.vstar k)
    (hw : ∀ j k, m.w j k = m.w k j) {θ : ι → ℝ} {lam ρ : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : ∀ x : ι → ℝ, lam * ∑ k, (x k - (∑ j, x j) / Fintype.card ι) ^ 2 ≤
      (∑ j, ∑ k, m.w j k * (x j - x k) ^ 2) / 2)
    (hρ : ∀ k, (m.angleGain θ k).re ≤ ρ) :
    m.Dissipative θ (lam * ‖∑ k, m.profile θ k‖ ^ 2 / (Fintype.card ι * m.mass) - ρ) := by
  intro u hu
  have hmp := mass_pos hv
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  set N : ℝ := (Fintype.card ι : ℝ)
  -- the gain part
  have hK : ∑ k, (conj (u k) * (m.angleGain θ k * u k)).re ≤ ρ * ∑ k, ‖u k‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [show conj (u k) * (m.angleGain θ k * u k) = m.angleGain θ k * (conj (u k) * u k) by ring,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_mul_ofReal]
    exact mul_le_mul_of_nonneg_right (hρ k) (sq_nonneg _)
  -- the Laplacian part
  have hL2 : 2 * ∑ k, (conj (u k) * m.lap u k).re = ∑ j, ∑ k, m.w j k * ‖u j - u k‖ ^ 2 := by
    have h1 : ∑ k, (conj (u k) * m.lap u k).re =
        ∑ k, ∑ j, m.w j k * (conj (u k) * (u k - u j)).re := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lap, Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [mul_left_comm, Complex.re_ofReal_mul]
    have hP : ∑ k, (conj (u k) * m.lap u k).re =
        ∑ j, ∑ k, m.w j k * (conj (u k) * (u k - u j)).re := by
      rw [h1, Finset.sum_comm]
    have hQ : ∑ k, (conj (u k) * m.lap u k).re =
        ∑ j, ∑ k, m.w j k * (conj (u j) * (u j - u k)).re := by
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hw]
    rw [two_mul]
    nth_rewrite 1 [hP]
    rw [hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_add, ← Complex.add_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
      Complex.sub_im]
    ring
  -- the connectivity bound on the real and imaginary parts
  have hre := hlam fun k => (u k).re
  have him := hlam fun k => (u k).im
  have hvar : ∀ x : ι → ℝ, ∑ k, (x k - (∑ j, x j) / N) ^ 2 =
      ∑ k, x k ^ 2 - (∑ j, x j) ^ 2 / N := by
    intro x
    have h1 : ∀ c : ℝ, ∑ k, (x k - c) ^ 2 = ∑ k, x k ^ 2 - 2 * c * ∑ k, x k + N * c ^ 2 := by
      intro c
      calc ∑ k, (x k - c) ^ 2 = ∑ k, (x k ^ 2 - 2 * c * x k + c ^ 2) :=
            Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1]
    field_simp
    ring
  rw [hvar] at hre him
  have hnorm : ∀ j k, ‖u j - u k‖ ^ 2 = ((u j).re - (u k).re) ^ 2 + ((u j).im - (u k).im) ^ 2 := by
    intro j k
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hsq : ∀ k, ‖u k‖ ^ 2 = (u k).re ^ 2 + (u k).im ^ 2 := by
    intro k; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hsumsq : ‖∑ k, u k‖ ^ 2 = (∑ k, (u k).re) ^ 2 + (∑ k, (u k).im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    ring
  have hlap : lam * (∑ k, ‖u k‖ ^ 2 - ‖∑ k, u k‖ ^ 2 / N) ≤
      ∑ k, (conj (u k) * m.lap u k).re := by
    have : (∑ j, ∑ k, m.w j k * ‖u j - u k‖ ^ 2) =
        (∑ j, ∑ k, m.w j k * ((u j).re - (u k).re) ^ 2) +
          ∑ j, ∑ k, m.w j k * ((u j).im - (u k).im) ^ 2 := by
      simp only [hnorm, mul_add, Finset.sum_add_distrib]
    simp only [hsq, Finset.sum_add_distrib, hsumsq]
    rw [add_div] at *
    linarith
  -- the orthogonality bound
  have hcs := normSq_sum_le hv θ hu
  set γ := ‖∑ k, m.profile θ k‖ ^ 2 / m.mass
  have hU := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖u k‖
  have hfin : lam * (γ / N) * ∑ k, ‖u k‖ ^ 2 ≤ ∑ k, (conj (u k) * m.lap u k).re := by
    refine le_trans ?_ hlap
    have : ‖∑ k, u k‖ ^ 2 / N ≤ (N - γ) * (∑ k, ‖u k‖ ^ 2) / N :=
      div_le_div_of_nonneg_right hcs hN.le
    have h2 : (N - γ) * (∑ k, ‖u k‖ ^ 2) / N = ∑ k, ‖u k‖ ^ 2 - γ / N * ∑ k, ‖u k‖ ^ 2 := by
      field_simp
    nlinarith
  have hsplit : ∑ k, (conj (u k) * (m.angleGain θ k * u k - m.lap u k)).re =
      ∑ k, (conj (u k) * (m.angleGain θ k * u k)).re - ∑ k, (conj (u k) * m.lap u k).re := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_sub, Complex.sub_re]
  rw [hsplit, show lam * ‖∑ k, m.profile θ k‖ ^ 2 / (N * m.mass) = lam * (γ / N) by
    simp only [γ]; field_simp]
  nlinarith

omit [Fintype ι] in
@[tmio T, powerlib_foundation] private theorem one_le_cos_add_sin {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ ≤ Real.pi / 2) : 1 ≤ Real.cos φ + Real.sin φ := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  nlinarith [Real.sin_sq_add_cos_sq φ, mul_nonneg hc hs]

/-- With every angle set-point within `[0, π/2]` of a reference unit,
`|∑ₖ s_k|² ≥ (N v_min)²/2` (the bound behind Colombino et al. (40)). -/
@[tmio M, powerlib_domain] theorem normSq_sum_profile_ge {θ : ι → ℝ} (r : ι)
    (hθ : ∀ k, 0 ≤ θ k - θ r ∧ θ k - θ r ≤ Real.pi / 2) {vmin : ℝ}
    (hmin : ∀ k, vmin ≤ m.vstar k) (h0 : 0 ≤ vmin) :
    (Fintype.card ι * vmin) ^ 2 / 2 ≤ ‖∑ k, m.profile θ k‖ ^ 2 := by
  have hrot : ‖∑ k, m.profile θ k‖ =
      ‖∑ k, ((m.vstar k : ℂ) * exp (((θ k - θ r : ℝ) : ℂ) * I))‖ := by
    rw [← one_mul ‖∑ k, m.profile θ k‖, ← Complex.norm_exp_ofReal_mul_I (-θ r), ← norm_mul,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [profile, mul_left_comm, ← Complex.exp_add]
    push_cast
    ring_nf
  set a := ∑ k, m.vstar k * Real.cos (θ k - θ r)
  set b := ∑ k, m.vstar k * Real.sin (θ k - θ r)
  have hab : ‖∑ k, ((m.vstar k : ℂ) * exp (((θ k - θ r : ℝ) : ℂ) * I))‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, a, b]
    ring
  have hsum : Fintype.card ι * vmin ≤ a + b := by
    rw [show a + b = ∑ k, m.vstar k * (Real.cos (θ k - θ r) + Real.sin (θ k - θ r)) by
      simp only [a, b, ← Finset.sum_add_distrib, mul_add]]
    calc (Fintype.card ι : ℝ) * vmin = ∑ _k : ι, vmin := by simp
      _ ≤ ∑ k, m.vstar k * (Real.cos (θ k - θ r) + Real.sin (θ k - θ r)) :=
          Finset.sum_le_sum fun k _ => by
            have := one_le_cos_add_sin (hθ k).1 (hθ k).2
            nlinarith [hmin k]
  rw [hrot, hab]
  have hNv : 0 ≤ (Fintype.card ι : ℝ) * vmin := mul_nonneg (Nat.cast_nonneg _) h0
  nlinarith [sq_nonneg (a - b), mul_le_mul hsum hsum hNv (hNv.trans hsum)]

/-- **Colombino et al. Condition 1 gives a dissipative coupling.** With symmetric weights,
angle set-points within `[0, π/2]` of a reference unit, magnitude bounds
`v_min ≤ v*_k ≤ v_max` (`v_min > 0`), a lower bound `λ ≥ 0` on the algebraic connectivity, `η > 0`
and the stability condition (29)
`∑ⱼ w_{jk}(1 − (v*_j/v*_k) cos(θ_j − θ_k)) + α/η < ½ (v_min²/v_max²) λ` for every `k`, the coupling
is dissipative at a rate `μ` with `ημ > α` (`dissipative_of_bounds` with
`γ ≥ v_min²/(2 v_max²)`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dissipative_of_condition [Nonempty ι]
    (hv : ∀ k, 0 < m.vstar k) (hw : ∀ j k, m.w j k = m.w k j) {θ : ι → ℝ} (r : ι)
    (hθ : ∀ k, 0 ≤ θ k - θ r ∧ θ k - θ r ≤ Real.pi / 2) {vmin vmax lam : ℝ}
    (hmin : ∀ k, vmin ≤ m.vstar k) (hmax : ∀ k, m.vstar k ≤ vmax) (h0 : 0 < vmin)
    (hlam0 : 0 ≤ lam)
    (hlam : ∀ x : ι → ℝ, lam * ∑ k, (x k - (∑ j, x j) / Fintype.card ι) ^ 2 ≤
      (∑ j, ∑ k, m.w j k * (x j - x k) ^ 2) / 2) (hη : 0 < m.η)
    (hcond : ∀ k, ∑ j, m.w j k * (1 - m.vstar j / m.vstar k * Real.cos (θ j - θ k)) +
      m.α / m.η < vmin ^ 2 / vmax ^ 2 * lam / 2) :
    ∃ μ, m.α < m.η * μ ∧ m.Dissipative θ μ := by
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ (fun k => (m.angleGain θ k).re)
    Finset.univ_nonempty
  refine ⟨_, ?_, dissipative_of_bounds hv hw hlam0 hlam (ρ := (m.angleGain θ k₀).re)
    fun k => hk₀ k (Finset.mem_univ k)⟩
  have hmp := mass_pos hv
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hvmax : 0 < vmax := h0.trans_le ((hmin k₀).trans (hmax k₀))
  have hS := normSq_sum_profile_ge r hθ hmin h0.le
  have hmass : m.mass ≤ Fintype.card ι * vmax ^ 2 := by
    calc m.mass = ∑ k, m.vstar k ^ 2 := rfl
      _ ≤ ∑ _k : ι, vmax ^ 2 := Finset.sum_le_sum fun k _ =>
          pow_le_pow_left₀ (hv k).le (hmax k) 2
      _ = Fintype.card ι * vmax ^ 2 := by simp
  have hγ : vmin ^ 2 / vmax ^ 2 / 2 ≤
      ‖∑ k, m.profile θ k‖ ^ 2 / (Fintype.card ι * m.mass) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : vmin ^ 2 / vmax ^ 2 * (Fintype.card ι * m.mass) ≤
        vmin ^ 2 / vmax ^ 2 * (Fintype.card ι * (Fintype.card ι * vmax ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass hN.le) (by positivity)
    have e2 : vmin ^ 2 / vmax ^ 2 * (Fintype.card ι * (Fintype.card ι * vmax ^ 2)) =
        (Fintype.card ι * vmin) ^ 2 := by
      field_simp
    linarith
  have hc := hcond k₀
  rw [← angleGain_re hv] at hc
  have hα : m.α / m.η < lam * ‖∑ k, m.profile θ k‖ ^ 2 / (Fintype.card ι * m.mass) -
      (m.angleGain θ k₀).re := by
    have := mul_le_mul_of_nonneg_left hγ hlam0
    rw [mul_div_assoc]
    nlinarith
  rw [div_lt_iff₀ hη] at hα
  linarith

/-! ## The stability condition cannot always be met -/

/-- Two units on one line (`w = 1`) with magnitude set-points `v* = (1, 2)`. -/
def twoUnequal (κ η α ω0 : ℝ) (p q : Fin 2 → ℝ) : DVOC (Fin 2) :=
  ⟨fun j k => if j = k then 0 else 1, κ, ![1, 2], p, q, η, α, ω0⟩

/-- **The remark after Condition 1 is false.** Colombino et al. state that on a connected graph
(29) "can always be satisfied by a proper choice of control gains and small enough angle
set-points". For two units on one line with `v* = (1, 2)` it fails for every angle profile, every
pair of gains `η > 0`, `α ≥ 0`, every admissible connectivity bound `λ` (necessarily `λ ≤ 2`) and
every magnitude bounds `v_min ≤ 1`, `v_max ≥ 2`: the unit with the larger set-point has
`Re K^θ = 1 − cos(θ₀ − θ₁)/2 ≥ ½`, while the right-hand side is at most `¼`. -/
@[tmio M, powerlib_domain] theorem twoUnequal_not_condition (κ ω0 : ℝ) (p q : Fin 2 → ℝ)
    {η α : ℝ} (hη : 0 < η) (hα : 0 ≤ α) (θ : Fin 2 → ℝ) {vmin vmax lam : ℝ}
    (hmin : ∀ k, vmin ≤ (twoUnequal κ η α ω0 p q).vstar k)
    (hmax : ∀ k, (twoUnequal κ η α ω0 p q).vstar k ≤ vmax) (h0 : 0 < vmin)
    (hlam : ∀ x : Fin 2 → ℝ, lam * ∑ k, (x k - (∑ j, x j) / Fintype.card (Fin 2)) ^ 2 ≤
      (∑ j, ∑ k, (twoUnequal κ η α ω0 p q).w j k * (x j - x k) ^ 2) / 2) :
    ¬ ∀ k, ∑ j, (twoUnequal κ η α ω0 p q).w j k *
        (1 - (twoUnequal κ η α ω0 p q).vstar j / (twoUnequal κ η α ω0 p q).vstar k *
          Real.cos (θ j - θ k)) + (twoUnequal κ η α ω0 p q).α / (twoUnequal κ η α ω0 p q).η <
      vmin ^ 2 / vmax ^ 2 * lam / 2 := by
  intro h
  have h1 := h 1
  have hm0 := hmin 0
  have hM1 := hmax 1
  have hl := hlam ![1, -1]
  simp only [twoUnequal, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fintype.card_fin, ite_true, ite_false, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, one_ne_zero] at h1 hm0 hM1 hl
  norm_num at h1 hl
  have hlam2 : lam ≤ 2 := by linarith
  have hcos := Real.cos_le_one (θ 0 - θ 1)
  have hαη : 0 ≤ α / η := div_nonneg hα hη.le
  have hc0 : 0 ≤ vmin ^ 2 / vmax ^ 2 := by positivity
  have hc : vmin ^ 2 / vmax ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have : vmin ^ 2 / vmax ^ 2 * lam ≤ vmin ^ 2 / vmax ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hlam2 hc0
  nlinarith

/-- **The conclusion survives.** For the same two units at the in-phase profile `θ = 0` the
coupling is dissipative at the rate `13/10` (`dissipative_of_bounds`: `λ = 2`, `ρ = ½`,
`γ = |1 + 2|²/(2 · 5) = 9/10`), so for `α < 13η/10` every solution of the balanced network
converges to the origin or to the synchronous set (`tendsto_origin_or_sync`), although Condition 1
fails for all gains (`twoUnequal_not_condition`). -/
@[tmio M, powerlib_domain] theorem twoUnequal_dissipative (κ η α ω0 : ℝ) (p q : Fin 2 → ℝ) :
    (twoUnequal κ η α ω0 p q).Dissipative 0 (13 / 10) := by
  set m := twoUnequal κ η α ω0 p q
  have hv : ∀ k, 0 < m.vstar k := by
    intro k; fin_cases k <;> simp [m, twoUnequal]
  have hw : ∀ j k, m.w j k = m.w k j := by
    intro j k; simp only [m, twoUnequal]; split_ifs <;> simp_all [eq_comm]
  have hlam : ∀ x : Fin 2 → ℝ, 2 * ∑ k, (x k - (∑ j, x j) / Fintype.card (Fin 2)) ^ 2 ≤
      (∑ j, ∑ k, m.w j k * (x j - x k) ^ 2) / 2 := by
    intro x
    simp only [m, twoUnequal, Fin.sum_univ_two, Fintype.card_fin, Fin.isValue, ite_true,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, one_ne_zero, ite_false]
    norm_num
    nlinarith [sq_nonneg (x 0 - x 1)]
  have hρ : ∀ k, (m.angleGain 0 k).re ≤ 1 / 2 := by
    intro k
    rw [angleGain_re hv]
    fin_cases k <;> simp [m, twoUnequal, Fin.sum_univ_two] <;> norm_num
  have h := dissipative_of_bounds hv hw (by norm_num) hlam hρ
  have hS : ‖∑ k, m.profile 0 k‖ = 3 := by
    simp [m, twoUnequal, profile, Fin.sum_univ_two]; norm_num
  have hM : m.mass = 5 := by
    simp [m, twoUnequal, mass, Fin.sum_univ_two]; norm_num
  rw [hS, hM, Fintype.card_fin] at h
  convert h using 1
  norm_num

/-! ## Trajectories (implementation evidence, Rules §3a) -/

/-- Along a solution the profile component `z(t)` has derivative `⟨s, f(v)⟩/‖s‖²`. -/
@[tmio TM, powerlib_domain] private theorem hasDerivAt_proj {θ : ι → ℝ} {X : ℝ → ι → ℂ}
    (hX : ∀ t, HasDerivAt X (m.field (X t)) t) (t : ℝ) :
    HasDerivAt (fun s => m.proj θ (X s))
      ((∑ k, conj (m.profile θ k) * m.field (X t) k) / (m.mass : ℂ)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    ((hasDerivAt_pi.mp (hX t) k).const_mul (conj (m.profile θ k)))
  exact h.div_const _

/-- Along a solution `V(t) = ‖u(t)‖²` has derivative `2 ∑ₖ Re(ū_k f_k)`. -/
@[tmio TM, powerlib_domain] private theorem hasDerivAt_syncError [Nonempty ι]
    (hv : ∀ k, 0 < m.vstar k) {θ : ι → ℝ} {X : ℝ → ι → ℂ}
    (hX : ∀ t, HasDerivAt X (m.field (X t)) t) (t : ℝ) :
    HasDerivAt (fun s => m.syncError θ (X s))
      (2 * ∑ k, (conj (m.err θ (X t) k) * m.field (X t) k).re) t := by
  have hm := (mass_pos hv).ne'
  set z' := (∑ k, conj (m.profile θ k) * m.field (X t) k) / (m.mass : ℂ)
  have he : ∀ k, HasDerivAt (fun s => m.err θ (X s) k) (m.field (X t) k - z' * m.profile θ k) t :=
    fun k => (hasDerivAt_pi.mp (hX t) k).sub ((hasDerivAt_proj hX t).mul_const _)
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (he k).norm_sq
  have hval : ∑ k, 2 * inner ℝ (m.err θ (X t) k) (m.field (X t) k - z' * m.profile θ k) =
      2 * ∑ k, (conj (m.err θ (X t) k) * m.field (X t) k).re := by
    simp only [Complex.inner, sub_mul, Complex.sub_re, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h0 : ∑ k, (z' * m.profile θ k * conj (m.err θ (X t) k)).re = 0 := by
      rw [← Complex.re_sum]
      have := sum_conj_err_mul_profile hm θ (X t)
      rw [show ∑ k, z' * m.profile θ k * conj (m.err θ (X t) k) =
        z' * ∑ k, conj (m.err θ (X t) k) * m.profile θ k by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, this]
      simp
    rw [h0, sub_zero]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  rw [← hval]
  exact h

/-- **Global exponential convergence to the profile line** (Colombino et al. Theorem 2):
`V(v(t)) ≤ V(v(0)) e^{2(α − ημ) t}` for every solution of a balanced network whose coupling is
dissipative at the rate `μ` (`η, α ≥ 0`); for `ημ > α` every solution approaches `S = ℂ s`
exponentially. Implementation evidence: trajectory level (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem syncError_le [Nonempty ι] (hv : ∀ k, 0 < m.vstar k)
    {θ : ι → ℝ} {ω μ : ℝ} (hb : m.Balanced θ ω) (hd : m.Dissipative θ μ) (hη : 0 ≤ m.η)
    (hα : 0 ≤ m.α) {X : ℝ → ι → ℂ} (hX : ∀ t, HasDerivAt X (m.field (X t)) t) {t : ℝ}
    (ht : 0 ≤ t) :
    m.syncError θ (X t) ≤ m.syncError θ (X 0) * Real.exp (2 * (m.α - m.η * μ) * t) := by
  have h := Dynamics.VariableRate.le_mul_exp_integral (g := fun s => m.syncError θ (X s))
    (lam := fun _ => 2 * (m.α - m.η * μ)) continuous_const
    (fun s _ => hasDerivAt_syncError hv hX s)
    (fun s _ => by
      have := sum_re_err_field_le hv hb hd hη hα (X s)
      linarith) ht
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  rwa [mul_comm t] at h

omit [Fintype ι] in
@[tmio M, powerlib_domain] private theorem norm_le_err_add {θ : ι → ℝ}
    (hv : ∀ k, 0 < m.vstar k) (z : ℂ) (x : ι → ℂ) (k : ι) :
    |‖x k‖ - ‖z‖ * m.vstar k| ≤ ‖x k - z * m.profile θ k‖ := by
  have h := abs_norm_sub_norm_le (x k) (z * m.profile θ k)
  rwa [norm_mul, norm_profile hv] at h

/-- **Convergence to the origin or to the synchronous set** (the attractivity half of Colombino et
al. Theorem 1): for a balanced network whose coupling is dissipative at a rate `μ` with `ημ > α`
(`α > 0`), every solution either converges to the origin or approaches the synchronous set `T`:
the phase error `V` vanishes and every magnitude tends to its set-point. The exceptional set is
the set of initial states whose solution converges to the origin (its basin). Through
`syncError_le`, `proj_field`, `norm_projRem_le` and the generic logistic dichotomy
`Dynamics.LogisticDichotomy.tendsto_zero_or_one`. Implementation evidence: trajectory level. -/
@[tmio TM, powerlib_domain] private theorem tendsto_origin_or_sync [Nonempty ι]
    (hv : ∀ k, 0 < m.vstar k) {θ : ι → ℝ} {ω μ : ℝ} (hb : m.Balanced θ ω)
    (hd : m.Dissipative θ μ) (hη : 0 ≤ m.η) (hα : 0 < m.α) (hμ : m.α < m.η * μ)
    {X : ℝ → ι → ℂ} (hX : ∀ t, HasDerivAt X (m.field (X t)) t) :
    Tendsto X atTop (𝓝 0) ∨ (Tendsto (fun t => m.syncError θ (X t)) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun t => ‖X t k‖) atTop (𝓝 (m.vstar k))) := by
  -- the phase error vanishes
  have hV : Tendsto (fun t => m.syncError θ (X t)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun t => m.syncError θ (X 0) * Real.exp (2 * (m.α - m.η * μ) * t))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => 2 * (m.η * μ - m.α) * t) atTop atTop :=
        tendsto_id.const_mul_atTop (by linarith)
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (m.syncError θ (X 0))
      simp only [mul_zero] at h2
      refine h2.congr fun t => ?_
      simp only [Function.comp_apply]
      congr 2; ring
    refine squeeze_zero' (Eventually.of_forall fun t =>
      Finset.sum_nonneg fun k _ => sq_nonneg _) ?_ hexp
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact syncError_le hv hb hd hη hα.le hX ht
  have hr : Tendsto (fun t => Real.sqrt (m.syncError θ (X t))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hV
  have hcont : Continuous (m.remBound θ) := by unfold remBound; fun_prop
  have hh : Tendsto (fun t => m.remBound θ (Real.sqrt (m.syncError θ (X t)))) atTop (𝓝 0) := by
    have := (hcont.tendsto 0).comp hr
    rw [show m.remBound θ 0 = 0 by simp [remBound]] at this
    exact this
  -- the profile component is a perturbed logistic oscillator
  set z : ℝ → ℂ := fun t => m.proj θ (X t)
  have hz : ∀ t, HasDerivAt z ((I * ((m.ω0 + m.η * ω : ℝ) : ℂ) +
      (m.α : ℂ) * ((1 - ‖z t‖ : ℝ) : ℂ)) * z t + m.projRem θ (X t)) t := fun t => by
    rw [← proj_field hv hb]; exact hasDerivAt_proj hX t
  have hdich := Dynamics.LogisticDichotomy.tendsto_zero_or_one (a := m.α) hα
    (y := fun t => ‖z t‖ ^ 2) (h := fun t => m.remBound θ (Real.sqrt (m.syncError θ (X t))))
    (fun t _ => sq_nonneg _) (fun t _ => (hz t).norm_sq) (fun t _ => by
      rw [Real.sqrt_sq (norm_nonneg _), Complex.inner]
      have hre : (((I * ((m.ω0 + m.η * ω : ℝ) : ℂ) + (m.α : ℂ) * ((1 - ‖z t‖ : ℝ) : ℂ)) *
          z t + m.projRem θ (X t)) * conj (z t)).re =
          m.α * (1 - ‖z t‖) * ‖z t‖ ^ 2 + (m.projRem θ (X t) * conj (z t)).re := by
        rw [add_mul, Complex.add_re, mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow,
          Complex.re_mul_ofReal]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      rw [hre]
      have hb' := norm_projRem_le hv hη hα.le θ (X t)
      have hle : |(m.projRem θ (X t) * conj (z t)).re| ≤
          ‖m.projRem θ (X t)‖ * ‖z t‖ := by
        refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_conj]
      have hzn := norm_nonneg (z t)
      rw [show 2 * (m.α * (1 - ‖z t‖) * ‖z t‖ ^ 2 + (m.projRem θ (X t) * conj (z t)).re) -
        2 * m.α * (1 - ‖z t‖) * ‖z t‖ ^ 2 = 2 * (m.projRem θ (X t) * conj (z t)).re by ring,
        abs_mul, abs_two]
      have := mul_le_mul_of_nonneg_right hb' hzn
      nlinarith) hh
  have hXk : ∀ t k, ‖X t k‖ ≤ Real.sqrt (m.syncError θ (X t)) + ‖z t‖ * m.vstar k := fun t k => by
    have h1 := norm_le_err_add hv (z t) (X t) k (θ := θ)
    have h2 := norm_err_le_sqrt (m := m) θ (X t) k
    simp only [err] at h2
    have := (abs_le.mp h1).2
    linarith
  rcases hdich with h0 | h1
  · left
    rw [tendsto_pi_nhds]
    intro k
    have hzk : Tendsto (fun t => ‖z t‖) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h0
      simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
    refine squeeze_zero_norm (fun t => hXk t k) ?_
    simpa using hr.add (hzk.mul_const (m.vstar k))
  · right
    refine ⟨hV, fun k => ?_⟩
    have hzk : Tendsto (fun t => ‖z t‖) atTop (𝓝 1) := by
      have := (Real.continuous_sqrt.tendsto 1).comp h1
      simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
    have hlim : Tendsto (fun t => ‖z t‖ * m.vstar k) atTop (𝓝 (m.vstar k)) := by
      simpa using hzk.mul_const (m.vstar k)
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hgap : ∀ t, ‖‖X t k‖ - m.vstar k‖ ≤
        Real.sqrt (m.syncError θ (X t)) + |‖z t‖ * m.vstar k - m.vstar k| := fun t => by
      have h1 := norm_le_err_add hv (z t) (X t) k (θ := θ)
      have h2 := norm_err_le_sqrt (m := m) θ (X t) k
      simp only [err] at h2
      rw [Real.norm_eq_abs]
      calc |‖X t k‖ - m.vstar k| ≤ |‖X t k‖ - ‖z t‖ * m.vstar k| +
            |‖z t‖ * m.vstar k - m.vstar k| := abs_sub_le _ _ _
        _ ≤ _ := by linarith
    refine squeeze_zero (fun t => norm_nonneg _) hgap ?_
    have := hr.add ((tendsto_iff_norm_sub_tendsto_zero.mp hlim))
    simpa [Real.norm_eq_abs] using this

/-- **The exceptional set meets the profile line only at the origin** (implementation evidence,
trajectory level). A solution starting on `S = ℂ s` off the origin stays on `S` (`V ≡ 0`), its
profile component obeys the exact logistic oscillator `ż = (j(ω₀ + ηω) + α(1 − |z|)) z`, and it
converges to the synchronous set. -/
@[tmio TM, powerlib_domain] private theorem tendsto_sync_of_profile [Nonempty ι]
    (hv : ∀ k, 0 < m.vstar k) {θ : ι → ℝ} {ω μ : ℝ} (hb : m.Balanced θ ω)
    (hd : m.Dissipative θ μ) (hη : 0 ≤ m.η) (hα : 0 < m.α) (hμ : m.α < m.η * μ)
    {X : ℝ → ι → ℂ} (hX : ∀ t, HasDerivAt X (m.field (X t)) t)
    (hS : m.syncError θ (X 0) = 0) (hz : m.proj θ (X 0) ≠ 0) :
    Tendsto (fun t => m.syncError θ (X t)) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun t => ‖X t k‖) atTop (𝓝 (m.vstar k)) := by
  rcases tendsto_origin_or_sync hv hb hd hη hα hμ hX with h0 | h1
  · exfalso
    -- on the profile line the remainder vanishes
    have hV0 : ∀ t, 0 ≤ t → m.syncError θ (X t) = 0 := fun t ht => by
      have h := syncError_le hv hb hd hη hα.le hX ht
      rw [hS, zero_mul] at h
      exact le_antisymm h (Finset.sum_nonneg fun k _ => sq_nonneg _)
    have hg : ∀ t, 0 ≤ t → m.projRem θ (X t) = 0 := fun t ht => by
      have h := norm_projRem_le hv hη hα.le θ (X t)
      rw [hV0 t ht, Real.sqrt_zero, show m.remBound θ 0 = 0 by simp [remBound], mul_zero] at h
      exact norm_le_zero_iff.mp h
    have hzd : ∀ t, 0 ≤ t → HasDerivAt (fun s => ‖m.proj θ (X s)‖ ^ 2)
        (2 * m.α * (1 - ‖m.proj θ (X t)‖) * ‖m.proj θ (X t)‖ ^ 2) t := fun t ht => by
      have h := (hasDerivAt_proj (θ := θ) hX t).norm_sq
      rw [proj_field hv hb, hg t ht, add_zero, Complex.inner] at h
      have key : ((I * ((m.ω0 + m.η * ω : ℝ) : ℂ) + (m.α : ℂ) *
          ((1 - ‖m.proj θ (X t)‖ : ℝ) : ℂ)) * m.proj θ (X t) * conj (m.proj θ (X t))).re =
          m.α * (1 - ‖m.proj θ (X t)‖) * ‖m.proj θ (X t)‖ ^ 2 := by
        rw [mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_mul_ofReal]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [key] at h
      convert h using 1
      ring
    have hcX : Continuous X := continuous_iff_continuousAt.mpr fun t => (hX t).continuousAt
    have hcp : Continuous fun v : ι → ℂ => ‖m.proj θ v‖ := by
      simp only [proj]; fun_prop
    set lam : ℝ → ℝ := fun t => 2 * m.α * (1 - ‖m.proj θ (X t)‖)
    have hlc : Continuous lam := by
      simp only [lam]
      exact continuous_const.mul (continuous_const.sub (hcp.comp hcX))
    -- `|z|²` stays positive
    have hpos : ∀ t, 0 ≤ t → 0 < ‖m.proj θ (X t)‖ ^ 2 := fun t ht => by
      have h := Dynamics.VariableRate.mul_exp_integral_le (g := fun s => ‖m.proj θ (X s)‖ ^ 2)
        hlc (fun s hs => hzd s hs) (fun s _ => le_of_eq (by simp only [lam])) ht
      have h0' : 0 < ‖m.proj θ (X 0)‖ ^ 2 := by positivity
      exact lt_of_lt_of_le (mul_pos h0' (Real.exp_pos _)) h
    -- the origin would make `z → 0`
    have hz0 : Tendsto (fun t => ‖m.proj θ (X t)‖) atTop (𝓝 0) := by
      have := (hcp.tendsto 0).comp h0
      simpa [proj, Function.comp_def] using this
    obtain ⟨T, hT⟩ := ((hz0.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).and
      (eventually_ge_atTop 0)).exists_forall_of_atTop
    have hgrow : ∀ s, 0 ≤ s → ‖m.proj θ (X T)‖ ^ 2 ≤ ‖m.proj θ (X (T + s))‖ ^ 2 := by
      intro s hs
      have h := Dynamics.VariableRate.mul_exp_integral_le
        (g := fun r => ‖m.proj θ (X (T + r))‖ ^ 2) (lam := fun _ => m.α) continuous_const
        (fun r hr => (hzd (T + r) (by linarith [(hT T le_rfl).2])).comp_const_add T r)
        (fun r hr => by
          have h1 := (hT (T + r) (by linarith)).1
          have h2 : m.α ≤ 2 * m.α * (1 - ‖m.proj θ (X (T + r))‖) := by nlinarith
          exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)) hs
      simp only [add_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
      refine le_trans ?_ h
      exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by positivity))
    have hzT := hpos T (hT T le_rfl).2
    have hlim : Tendsto (fun t => ‖m.proj θ (X t)‖ ^ 2) atTop (𝓝 0) := by
      simpa using hz0.pow 2
    obtain ⟨T', hT'⟩ := (hlim.eventually (gt_mem_nhds hzT)).exists_forall_of_atTop
    have := hT' (max T' T) (le_max_left _ _)
    have h2 := hgrow (max T' T - T) (by linarith [le_max_right T' T])
    rw [add_sub_cancel] at h2
    linarith
  · exact h1

/-- **Colombino et al. Theorem 1, attractivity, under the paper's hypotheses**: consistent
set-points (`PowerFlow`), symmetric weights, angles within `[0, π/2]` of a reference unit and
Condition 1 (29) with `η, α > 0`: every solution converges to the origin or to the synchronous set
(`dissipative_of_condition`, `balanced_zero_iff_powerFlow`, `tendsto_origin_or_sync`).
Implementation evidence: trajectory level. -/
@[tmio TM, powerlib_domain] private theorem condition_tendsto_origin_or_sync [Nonempty ι]
    (hv : ∀ k, 0 < m.vstar k) (hw : ∀ j k, m.w j k = m.w k j) {θ : ι → ℝ}
    (hpf : m.PowerFlow θ) (r : ι) (hθ : ∀ k, 0 ≤ θ k - θ r ∧ θ k - θ r ≤ Real.pi / 2)
    {vmin vmax lam : ℝ} (hmin : ∀ k, vmin ≤ m.vstar k) (hmax : ∀ k, m.vstar k ≤ vmax)
    (h0 : 0 < vmin) (hlam0 : 0 ≤ lam)
    (hlam : ∀ x : ι → ℝ, lam * ∑ k, (x k - (∑ j, x j) / Fintype.card ι) ^ 2 ≤
      (∑ j, ∑ k, m.w j k * (x j - x k) ^ 2) / 2) (hη : 0 < m.η) (hα : 0 < m.α)
    (hcond : ∀ k, ∑ j, m.w j k * (1 - m.vstar j / m.vstar k * Real.cos (θ j - θ k)) +
      m.α / m.η < vmin ^ 2 / vmax ^ 2 * lam / 2)
    {X : ℝ → ι → ℂ} (hX : ∀ t, HasDerivAt X (m.field (X t)) t) :
    Tendsto X atTop (𝓝 0) ∨ (Tendsto (fun t => m.syncError θ (X t)) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun t => ‖X t k‖) atTop (𝓝 (m.vstar k))) := by
  obtain ⟨μ, hμ, hd⟩ := dissipative_of_condition hv hw r hθ hmin hmax h0 hlam0 hlam hη hcond
  exact tendsto_origin_or_sync hv ((balanced_zero_iff_powerFlow hv θ).mpr hpf) hd hη.le hα hμ hX

/-! ## Two units with equal set-points: the exceptional set is the anti-phase plane -/

section Two

variable {m : DVOC (Fin 2)} {W v ω : ℝ}

omit [Fintype ι] in
/-- Two units with equal magnitude set-points `v`, one line of weight `W` and zero angle set-points:
the profile is `s = (v, v)`. -/
@[tmio M, powerlib_domain] private theorem two_profile (hv : ∀ k, m.vstar k = v) (k : Fin 2) :
    m.profile 0 k = v := by
  simp [profile, hv]

@[tmio M, powerlib_domain] private theorem two_angleGain (hv : ∀ k, m.vstar k = v) (hv0 : 0 < v)
    (k : Fin 2) : m.angleGain 0 k = 0 := by
  simp only [angleGain, two_profile hv, div_self (Complex.ofReal_ne_zero.mpr hv0.ne'), sub_self,
    mul_zero, Finset.sum_const_zero]

@[tmio M, powerlib_domain] private theorem two_lap (hW : m.w 1 0 = W) (hW' : m.w 0 1 = W)
    (X : Fin 2 → ℂ) : m.lap X 0 = W * (X 0 - X 1) ∧ m.lap X 1 = W * (X 1 - X 0) := by
  constructor <;> simp [lap, Fin.sum_univ_two, hW, hW']

/-- **Two equal units: the coupling is dissipative at the rate `2W`** off the in-phase line. -/
@[tmio M, powerlib_domain] theorem two_dissipative (hW : m.w 1 0 = W) (hW' : m.w 0 1 = W)
    (hv : ∀ k, m.vstar k = v) (hv0 : 0 < v) : m.Dissipative 0 (2 * W) := by
  intro u hu
  simp only [Fin.sum_univ_two, two_profile hv, Complex.conj_ofReal, ← mul_add,
    mul_eq_zero, Complex.ofReal_eq_zero, hv0.ne', false_or] at hu
  have h1 : u 1 = -u 0 := by linear_combination hu
  obtain ⟨hl0, hl1⟩ := two_lap hW hW' u
  simp only [Fin.sum_univ_two, two_angleGain hv hv0, zero_mul, zero_sub, hl0, hl1, h1, norm_neg]
  rw [show u 0 - -u 0 = 2 * u 0 by ring, show -u 0 - u 0 = -(2 * u 0) by ring]
  have hn : (conj (u 0) * (u 0)).re = ‖u 0‖ ^ 2 := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have e1 : (conj (u 0) * -((W : ℂ) * (2 * u 0))).re = -(2 * W) * ‖u 0‖ ^ 2 := by
    rw [show conj (u 0) * -((W : ℂ) * (2 * u 0)) = ((-(2 * W) : ℝ) : ℂ) * (conj (u 0) * u 0) by
      push_cast; ring, Complex.re_ofReal_mul, hn]
  have e2 : (conj (-u 0) * -((W : ℂ) * -(2 * u 0))).re = -(2 * W) * ‖u 0‖ ^ 2 := by
    rw [show conj (-u 0) * -((W : ℂ) * -(2 * u 0)) = ((-(2 * W) : ℝ) : ℂ) * (conj (u 0) * u 0) by
      rw [map_neg]; push_cast; ring, Complex.re_ofReal_mul, hn]
  rw [e1, e2]
  ring_nf
  exact le_refl _

/-- The in-phase component `U = v₀ + v₁` of two equal balanced units:
`|Re(U̇ Ū) − α|U|²| ≤ (α/v)(|v₀| + |v₁|)|U|²`. -/
@[tmio M, powerlib_domain] private theorem two_sum_field (hW : m.w 1 0 = W) (hW' : m.w 0 1 = W)
    (hv : ∀ k, m.vstar k = v) (hv0 : 0 < v) (hg : ∀ k, m.gain k = ω * I) (hα : 0 ≤ m.α)
    (X : Fin 2 → ℂ) :
    |((m.field X 0 + m.field X 1) * conj (X 0 + X 1)).re - m.α * ‖X 0 + X 1‖ ^ 2| ≤
      m.α / v * (‖X 0‖ + ‖X 1‖) * ‖X 0 + X 1‖ ^ 2 := by
  obtain ⟨hl0, hl1⟩ := two_lap hW hW' X
  set U := X 0 + X 1
  set Y := (‖X 0‖ : ℂ) * X 0 - (‖X 1‖ : ℂ) * (-X 1)
  have hsum : m.field X 0 + m.field X 1 =
      I * ((m.ω0 + m.η * ω : ℝ) : ℂ) * U + (m.α : ℂ) * U - ((m.α / v : ℝ) : ℂ) * Y := by
    have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv0.ne'
    simp only [field, hg, hl0, hl1, amp, hv, Y, U]
    push_cast
    field_simp
    ring
  have hre : ((m.field X 0 + m.field X 1) * conj U).re =
      m.α * ‖U‖ ^ 2 - m.α / v * (Y * conj U).re := by
    have h : (m.field X 0 + m.field X 1) * conj U = ((m.α * ‖U‖ ^ 2 : ℝ) : ℂ) +
        I * (((m.ω0 + m.η * ω) * ‖U‖ ^ 2 : ℝ) : ℂ) - ((m.α / v : ℝ) : ℂ) * (Y * conj U) := by
      rw [hsum]
      simp only [add_mul, sub_mul, mul_assoc, Complex.mul_conj']
      push_cast
      ring
    rw [h, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  have hY : ‖Y‖ ≤ (‖X 0‖ + ‖X 1‖) * ‖U‖ := by
    have := norm_norm_smul_sub_le (X 0) (-X 1)
    rw [norm_neg, sub_neg_eq_add] at this
    exact this
  have hc : |(Y * conj U).re| ≤ (‖X 0‖ + ‖X 1‖) * ‖U‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj, pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hY (norm_nonneg _)
  rw [show m.α * ‖U‖ ^ 2 - m.α / v * (Y * conj U).re - m.α * ‖U‖ ^ 2 =
    -(m.α / v * (Y * conj U).re) by ring, abs_neg, abs_mul, abs_of_nonneg (div_nonneg hα hv0.le),
    mul_assoc]
  exact mul_le_mul_of_nonneg_left hc (div_nonneg hα hv0.le)

/-- Along a solution, `|U|²` has derivative `2 Re(U̇ Ū)`. -/
@[tmio TM, powerlib_domain] private theorem two_hasDerivAt {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (m.field (X t)) t) (t : ℝ) :
    HasDerivAt (fun s => ‖X s 0 + X s 1‖ ^ 2)
      (2 * ((m.field (X t) 0 + m.field (X t) 1) * conj (X t 0 + X t 1)).re) t := by
  have h := ((hasDerivAt_pi.mp (hX t) 0).add (hasDerivAt_pi.mp (hX t) 1)).norm_sq
  rwa [Complex.inner] at h

/-- **Two equal units, off the anti-phase plane: synchronization** (implementation evidence,
trajectory level). With `0 < α < 2ηW`, every solution with `v₀(0) + v₁(0) ≠ 0` approaches the
synchronous set: the in-phase component `U` cannot vanish (`|U|²` grows wherever
`|v₀| + |v₁| < v`), so the solution does not converge to the origin, and `tendsto_origin_or_sync`
leaves the synchronous set. -/
@[tmio TM, powerlib_domain] private theorem two_tendsto_sync (hW : m.w 1 0 = W)
    (hW' : m.w 0 1 = W) (hv : ∀ k, m.vstar k = v) (hv0 : 0 < v) (hg : ∀ k, m.gain k = ω * I)
    (hη : 0 ≤ m.η) (hα : 0 < m.α) (hthr : m.α < m.η * (2 * W)) {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (m.field (X t)) t) (hU : X 0 0 + X 0 1 ≠ 0) :
    Tendsto (fun t => m.syncError 0 (X t)) atTop (𝓝 0) ∧
      ∀ k, Tendsto (fun t => ‖X t k‖) atTop (𝓝 v) := by
  have hvp : ∀ k, 0 < m.vstar k := fun k => by rw [hv]; exact hv0
  have hb : m.Balanced 0 ω := fun k => by rw [hg, two_angleGain hv hv0, zero_add]
  have hd := two_dissipative hW hW' hv hv0
  rcases tendsto_origin_or_sync hvp hb hd hη hα hthr hX with h0 | ⟨hV, hk⟩
  · exfalso
    -- the rate `λ(t) = 2α(1 − (|v₀| + |v₁|)/v)`
    set lam : ℝ → ℝ := fun t => 2 * m.α * (1 - (‖X t 0‖ + ‖X t 1‖) / v)
    have hcont : Continuous X := continuous_iff_continuousAt.mpr fun t =>
      (hX t).continuousAt
    have hlc : Continuous lam := by
      have h0c := (continuous_apply 0).comp hcont
      have h1c := (continuous_apply 1).comp hcont
      simp only [lam]
      fun_prop
    have hlow : ∀ t, lam t * ‖X t 0 + X t 1‖ ^ 2 ≤
        2 * ((m.field (X t) 0 + m.field (X t) 1) * conj (X t 0 + X t 1)).re := fun t => by
      have := two_sum_field hW hW' hv hv0 hg hα.le (X t)
      have := (abs_le.mp this).1
      simp only [lam]
      have hvv : m.α / v * (‖X t 0‖ + ‖X t 1‖) = m.α * ((‖X t 0‖ + ‖X t 1‖) / v) := by ring
      nlinarith
    -- `X → 0` makes the rate eventually at least `α`
    have h00 : Tendsto (fun t => ‖X t 0‖) atTop (𝓝 0) := by
      have := ((continuous_apply 0).tendsto (0 : Fin 2 → ℂ)).comp h0
      simpa [Function.comp_def] using this.norm
    have h11 : Tendsto (fun t => ‖X t 1‖) atTop (𝓝 0) := by
      have := ((continuous_apply 1).tendsto (0 : Fin 2 → ℂ)).comp h0
      simpa [Function.comp_def] using this.norm
    have hsmall : ∀ᶠ t in atTop, ‖X t 0‖ + ‖X t 1‖ ≤ v / 2 :=
      (h00.add h11).eventually (ge_mem_nhds (show (0 : ℝ) + 0 < v / 2 by linarith))
    obtain ⟨T, hT⟩ := (hsmall.and (eventually_ge_atTop 0)).exists_forall_of_atTop
    -- `|U(T)|² > 0`
    have hUT : 0 < ‖X T 0 + X T 1‖ ^ 2 := by
      have h := Dynamics.VariableRate.mul_exp_integral_le (g := fun s => ‖X s 0 + X s 1‖ ^ 2)
        hlc (fun s _ => two_hasDerivAt hX s) (fun s _ => hlow s) (hT T le_rfl).2
      have hpos : 0 < ‖X 0 0 + X 0 1‖ ^ 2 := by positivity
      exact lt_of_lt_of_le (mul_pos hpos (Real.exp_pos _)) h
    -- after `T`, `|U|²` does not decrease
    have hgrow : ∀ s, 0 ≤ s → ‖X T 0 + X T 1‖ ^ 2 ≤ ‖X (T + s) 0 + X (T + s) 1‖ ^ 2 := by
      intro s hs
      have h := Dynamics.VariableRate.mul_exp_integral_le
        (g := fun r => ‖X (T + r) 0 + X (T + r) 1‖ ^ 2) (lam := fun _ => m.α) continuous_const
        (fun r _ => (two_hasDerivAt hX (T + r)).comp_const_add T r)
        (fun r hr => by
          have hl := hlow (T + r)
          have hTr := (hT (T + r) (by linarith)).1
          have : m.α ≤ lam (T + r) := by
            simp only [lam]
            have : (‖X (T + r) 0‖ + ‖X (T + r) 1‖) / v ≤ 1 / 2 := by
              rw [div_le_iff₀ hv0]; linarith
            nlinarith
          nlinarith [sq_nonneg ‖X (T + r) 0 + X (T + r) 1‖]) hs
      simp only [add_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
      refine le_trans ?_ h
      exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by positivity))
    -- contradiction with `U → 0`
    have hU0 : Tendsto (fun t => ‖X t 0 + X t 1‖ ^ 2) atTop (𝓝 0) := by
      have hn : Tendsto (fun t => ‖X t 0 + X t 1‖) atTop (𝓝 0) :=
        squeeze_zero (fun _ => norm_nonneg _) (fun t => norm_add_le _ _)
          (by simpa using h00.add h11)
      simpa using hn.pow 2
    have hev := hU0.eventually (gt_mem_nhds hUT)
    obtain ⟨T', hT'⟩ := hev.exists_forall_of_atTop
    have := hT' (max T' T) (le_max_left _ _)
    have h2 := hgrow (max T' T - T) (by linarith [le_max_right T' T])
    rw [add_sub_cancel] at h2
    linarith
  · exact ⟨hV, fun k => by rw [← hv k]; exact hk k⟩

/-- **Two equal units, on the anti-phase plane: convergence to the origin** (implementation
evidence, trajectory level). With `α < 2ηW`, a solution with `v₀(0) + v₁(0) = 0` stays on the
anti-phase plane `v₁ = −v₀` (`|U|²` obeys a linear upper bound) and decays to the origin
(`|v₀|²` decays at least at the rate `2(2ηW − α)`). So the exceptional set of the two-unit
dichotomy is exactly the anti-phase plane `{v₀ + v₁ = 0}`, a real two-dimensional subspace. -/
@[tmio TM, powerlib_domain] private theorem two_tendsto_origin (hW : m.w 1 0 = W)
    (hW' : m.w 0 1 = W) (hv : ∀ k, m.vstar k = v) (hv0 : 0 < v) (hg : ∀ k, m.gain k = ω * I)
    (hα : 0 ≤ m.α) (hthr : m.α < m.η * (2 * W)) {X : ℝ → Fin 2 → ℂ}
    (hX : ∀ t, HasDerivAt X (m.field (X t)) t) (hU : X 0 0 + X 0 1 = 0) :
    Tendsto X atTop (𝓝 0) := by
  have hcont : Continuous X := continuous_iff_continuousAt.mpr fun t => (hX t).continuousAt
  -- the anti-phase plane is invariant
  have hzero : ∀ t, 0 ≤ t → X t 1 = -X t 0 := by
    intro t ht
    set lam : ℝ → ℝ := fun t => 2 * m.α * (1 + (‖X t 0‖ + ‖X t 1‖) / v)
    have hlc : Continuous lam := by
      have h0c := (continuous_apply 0).comp hcont
      have h1c := (continuous_apply 1).comp hcont
      simp only [lam]
      fun_prop
    have h := Dynamics.VariableRate.le_mul_exp_integral (g := fun s => ‖X s 0 + X s 1‖ ^ 2)
      hlc (fun s _ => two_hasDerivAt hX s) (fun s _ => by
        have := two_sum_field hW hW' hv hv0 hg hα (X s)
        have := (abs_le.mp this).2
        simp only [lam]
        have hvv : m.α / v * (‖X s 0‖ + ‖X s 1‖) = m.α * ((‖X s 0‖ + ‖X s 1‖) / v) := by ring
        nlinarith) ht
    simp only [hU, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul] at h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h (sq_nonneg _))
    rw [norm_eq_zero] at this
    linear_combination this
  -- on the plane the amplitude decays
  have hdec : ∀ t, 0 ≤ t →
      ‖X t 0‖ ^ 2 ≤ ‖X 0 0‖ ^ 2 * Real.exp (2 * (m.α - m.η * (2 * W)) * t) := by
    intro t ht
    have h := Dynamics.VariableRate.le_mul_exp_integral (g := fun s => ‖X s 0‖ ^ 2)
      (lam := fun _ => 2 * (m.α - m.η * (2 * W))) continuous_const
      (fun s _ => (hasDerivAt_pi.mp (hX s) 0).norm_sq) (fun s hs => by
        rw [Complex.inner]
        obtain ⟨hl0, -⟩ := two_lap hW hW' (X s)
        have hf : m.field (X s) 0 = (I * ((m.ω0 + m.η * ω : ℝ) : ℂ) +
            (((m.α * (1 - ‖X s 0‖ / v) - m.η * (2 * W)) : ℝ) : ℂ)) * X s 0 := by
          simp only [field, hg, hl0, hzero s hs, amp, hv]
          push_cast
          ring
        rw [hf, mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_mul_ofReal]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        have : 0 ≤ m.α * (‖X s 0‖ / v) := mul_nonneg hα (div_nonneg (norm_nonneg _) hv0.le)
        nlinarith [sq_nonneg ‖X s 0‖]) ht
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    rwa [mul_comm t] at h
  have h0 : Tendsto (fun t => ‖X t 0‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 * (m.η * (2 * W) - m.α) * t) atTop atTop :=
      tendsto_id.const_mul_atTop (by linarith)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (‖X 0 0‖ ^ 2)
    simp only [mul_zero] at h2
    refine squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) ?_ h2
    filter_upwards [eventually_ge_atTop 0] with t ht
    refine (hdec t ht).trans (le_of_eq ?_)
    simp only [Function.comp_apply]
    congr 2; ring
  have hn0 : Tendsto (fun t => X t 0) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  rw [tendsto_pi_nhds]
  intro k
  fin_cases k
  · exact hn0
  · have := hn0.neg
    simp only [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hzero t ht).symm

/-- **Two equal units below the threshold: the anti-phase oscillation** (implementation
evidence, trajectory level). With `α > 0` and `2ηW < α` the anti-phase pair
`v₀ = r e^{jΩt} = −v₁`, `r = v(1 − 2ηW/α)`, `Ω = ω₀ + ηω`, is a solution with constant amplitude
`r` and constant phase error `V = 2r² > 0`: it converges neither to the origin nor to the
synchronous set, so the threshold `2ηW > α` of `two_tendsto_sync`/`two_tendsto_origin` is exact up
to equality. -/
@[tmio TM, powerlib_domain] private theorem two_antiPhase (hW : m.w 1 0 = W) (hW' : m.w 0 1 = W)
    (hv : ∀ k, m.vstar k = v) (hv0 : 0 < v) (hg : ∀ k, m.gain k = ω * I) (hα : 0 < m.α)
    (hthr : 2 * m.η * W < m.α) :
    let r := v * (1 - 2 * m.η * W / m.α)
    let X : ℝ → Fin 2 → ℂ := fun t => ![r * exp (((m.ω0 + m.η * ω : ℝ) : ℂ) * t * I),
      -(r * exp (((m.ω0 + m.η * ω : ℝ) : ℂ) * t * I))]
    (∀ t, HasDerivAt X (m.field (X t)) t) ∧ 0 < r ∧
      ∀ t, (∀ k, ‖X t k‖ = r) ∧ m.syncError 0 (X t) = 2 * r ^ 2 := by
  intro r X
  have hr : 0 < r := mul_pos hv0 (by rw [sub_pos, div_lt_one hα]; exact hthr)
  set Ω : ℝ := m.ω0 + m.η * ω
  have hn : ∀ t : ℝ, ‖(r : ℂ) * exp (Ω * t * I)‖ = r := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      show (Ω : ℂ) * t * I = ((Ω * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hamp : m.α * (1 - r / v) = 2 * m.η * W := by
    simp only [r]; field_simp; ring
  refine ⟨fun t => ?_, hr, fun t => ⟨fun k => ?_, ?_⟩⟩
  · have hz : HasDerivAt (fun t : ℝ => (r : ℂ) * exp (Ω * t * I))
        ((r : ℂ) * exp (Ω * t * I) * (Ω * I)) t := by
      have h1 : HasDerivAt (fun t : ℝ => (Ω : ℂ) * t * I) (Ω * I) t := by
        have := ((hasDerivAt_id (t : ℝ)).ofReal_comp.const_mul (Ω : ℂ)).mul_const I
        simpa using this
      simpa [mul_assoc] using h1.cexp.const_mul (r : ℂ)
    have hf : ∀ z : ℂ, ‖z‖ = r → m.field ![z, -z] 0 = I * Ω * z ∧
        m.field ![z, -z] 1 = -(I * Ω * z) := by
      intro z hz
      obtain ⟨hl0, hl1⟩ := two_lap hW hW' ![z, -z]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hl0 hl1
      have hc := congrArg (fun x : ℝ => (x : ℂ)) hamp
      push_cast at hc
      constructor
      · rw [field, hg, hl0, amp, hv]
        simp only [Matrix.cons_val_zero]
        rw [hz]
        simp only [Ω]
        push_cast
        linear_combination z * hc
      · rw [field, hg, hl1, amp, hv]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, norm_neg]
        rw [hz]
        simp only [Ω]
        push_cast
        linear_combination -z * hc
    obtain ⟨hf0, hf1⟩ := hf _ (hn t)
    refine hasDerivAt_pi.mpr fun k => ?_
    fin_cases k
    · change HasDerivAt (fun t : ℝ => (r : ℂ) * exp (Ω * t * I))
        (m.field ![(r : ℂ) * exp (Ω * t * I), -((r : ℂ) * exp (Ω * t * I))] 0) t
      rw [hf0]
      convert hz using 1
      ring
    · change HasDerivAt (fun t : ℝ => -((r : ℂ) * exp (Ω * t * I)))
        (m.field ![(r : ℂ) * exp (Ω * t * I), -((r : ℂ) * exp (Ω * t * I))] 1) t
      rw [hf1]
      convert hz.neg using 1
      ring
  · fin_cases k
    · exact hn t
    · change ‖-((r : ℂ) * exp (Ω * t * I))‖ = r
      rw [norm_neg]; exact hn t
  · have hp : m.proj 0 (X t) = 0 := by
      simp [proj, X, Fin.sum_univ_two, two_profile hv]
    simp only [syncError, err, hp, zero_mul, sub_zero, Fin.sum_univ_two]
    change ‖(r : ℂ) * exp (Ω * t * I)‖ ^ 2 + ‖-((r : ℂ) * exp (Ω * t * I))‖ ^ 2 = 2 * r ^ 2
    rw [norm_neg, hn]
    ring

end Two

end DVOC
end powerlib.GFM
