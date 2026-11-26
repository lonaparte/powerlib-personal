import theorem.GridTiedConverter.GFM.VoltageModulationQVLink
import theorem.ParametricResonance.StableHurwitz
import theorem.Criteria.Hurwitz2

/-! # Dynamic Q–V loop at any operating point: explicit Hopf and stability conditions

`VoltageModulationQVOrbit` takes the simple root `jΩ` of the characteristic function and the
spectral radius of the stable part as hypotheses. Here both are derived from explicit real
conditions on the parameters. Every eigenvalue of `A₀` is the Q–V pole `−b/τ` or a root of the
quartic `(τs + b)(s(s + a)(s + ω_c) + d₀) − d₁`; at the Hopf point the quartic factors as
`(s² + Ω²)(τs² + ps + q)`, so the remaining modes are stable exactly when `p, q > 0` (with
`τ, b > 0`), and `stable_modal_of_hurwitz` supplies the modal coordinates. The voltage pump is
given in the compact form `g_V = −(ω₀ω_c/(2H F'(jΩ))) ρ_eff`. Instances: the lossless link and an
impedance `R + jX`, at any load angle.

Model boundary.
* `DynQV` and the field of `VoltageModulationQVOrbit`; `τ > 0`.
* Hopf conditions `pΩ² = τd₀ + b a ω_c`, `qΩ² = b d₀ − d₁` (`d₀ = ω₀ω_cP_δ/2H`,
  `d₁ = ω₀ω_c k_q P_E Q_δ/2H`, `p = τ(a + ω_c) + b`, `q = τaω_c + b(a + ω_c) − τΩ²`).
* The impedance port maps `P = (R(E² − EV cos δ) + X EV sin δ)/Z²`,
  `Q = (X(E² − EV cos δ) − R EV sin δ)/Z²` (`lossyP`, `lossyQ`), quasi-static network.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2, §3 (VSG core); the dynamic Q–V loop and the voltage excitation are new.

Results.
* `eig_cases` — every eigenpair is the Q–V pole or a root of `F` with eigenvector `∝ right λ`.
* `charP4`, `charP4d`, `p4`, `q4`, `charP4_eq`, `charP4d_eq`, `charP4_factor`, `charP4d_factor` —
  the quartic and its factorization at the Hopf point.
* `hopf_facts` (`F(jΩ) = 0`, `F'(jΩ) ≠ 0`, `F(2jΩ) ≠ 0`), `hopf_simple`, `eig_stable` (the other
  modes, through `Criteria.quadratic_roots_re_neg_iff`).
* `orbit_qv_hopf_stable`, `orbit_qv_hopf_unstable`, `orbit_qv_hopf_exp_stable` — end-to-end with
  explicit conditions.
* `rhoEff`, `gV_compact`, `gV_hopf` — `g_V = −ω₀ω_c(τjΩ + b)ρ_eff/(2H·2jΩ(q − τΩ² + jpΩ))`.
* `fderiv_comb`, `dδ_comb`, `dE_comb`, `dV_comb`, `lossyP`, `lossyQ`, `lossy_zero_R`,
  `contDiff_lossyP`, `contDiff_lossyQ`, `lossyCore`, `lossy_partials`, `lossy_second_partials` —
  the impedance instance, with all first and second partials in closed form.
* `orbit_link_hopf_stable`, `orbit_link_hopf_unstable`, `orbit_lossy_hopf_stable`,
  `orbit_lossy_hopf_unstable` — the lossless and lossy links at any operating point.

Corrections.
None: an extension (removes the spectral hypotheses of `VoltageModulationQVOrbit`).

Family and connection conclusions.
None: static evidence on the voltage-modulated dynamic Q–V core at any operating point.
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (matX)

variable (c : DynQV)

/-! ### Eigenpairs of the state matrix -/

/-- Every eigenpair of `A₀` is either the Q–V pole (`τλ + b = 0`) or a root of the characteristic
function whose eigenvector is a multiple of `right λ`. -/
@[tmio M, powerlib_domain] theorem eig_cases (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    {μ : ℂ} {v : Fin 4 → ℂ} (h : c.A0r.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    c.lag μ = 0 ∨ (v = v 0 • c.right μ ∧ (v ≠ 0 → c.charF μ = 0)) := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [A0r, mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h2 h3
  rcases eq_or_ne (c.lag μ) 0 with hl | hl
  · exact Or.inl hl
  right
  have e1 : v 1 = μ * v 0 / c.ω0 := by field_simp; linear_combination h0
  have e2 : v 2 = -(2 * c.H * μ + c.D) * μ * v 0 / c.ω0 := by
    rw [e1] at h1; field_simp at h1 ⊢; linear_combination -h1
  have e3 : v 3 = -(c.kq * c.Qδ) * v 0 / c.lag μ := by
    field_simp at h3 ⊢
    simp only [lag, b] at hl ⊢
    push_cast at hl ⊢
    field_simp
    linear_combination -h3
  have hv : v = v 0 • c.right μ := by
    funext i; fin_cases i <;> simp [right, e1, e2, e3] <;> ring
  refine ⟨hv, fun hv0 => ?_⟩
  have hv00 : v 0 ≠ 0 := by
    intro h00; apply hv0; rw [hv, h00, zero_smul]
  have key := c.charF_clear hH hl (s := μ)
  have h2' : c.ωc * c.Pδ * v 0 * c.ω0 * c.lag μ + c.ωc * (2 * c.H * μ + c.D) * μ * v 0 * c.lag μ -
      c.ωc * c.PE * c.kq * c.Qδ * v 0 * c.ω0 = -(μ * (2 * c.H * μ + c.D) * μ * v 0 * c.lag μ) := by
    rw [e2, e3] at h2
    field_simp at h2
    linear_combination (v 0) * h2
  have : 2 * c.H * c.lag μ * c.charF μ * v 0 = 0 := by
    rw [key]
    linear_combination h2'
  have := mul_eq_zero.mp this
  rcases this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exfalso; exact (mul_ne_zero (mul_ne_zero two_ne_zero hHc) hl) h
    · exact h
  · exact absurd h hv00

/-! ### The quartic and its factorization at the Hopf point -/

/-- The characteristic quartic `(τs + b)(s(s + a)(s + ω_c) + d₀) − d₁`. -/
def charP4 (s : ℂ) : ℂ :=
  c.lag s * (s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
    c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)

/-- Its derivative. -/
def charP4d (s : ℂ) : ℂ :=
  c.τ * (s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
    c.lag s * (3 * s ^ 2 + 2 * (c.a + c.ωc) * s + c.a * c.ωc)

/-- The `s³` coefficient over `τ`: `p = τ(a + ω_c) + b`. -/
def p4 : ℝ := c.τ * (c.D / (2 * c.H) + c.ωc) + c.b

/-- The remaining quadratic's constant term: `q = τ a ω_c + b(a + ω_c) − τΩ²`. -/
def q4 (Ω : ℝ) : ℝ := c.τ * (c.D / (2 * c.H)) * c.ωc + c.b * (c.D / (2 * c.H) + c.ωc) - c.τ * Ω ^ 2

@[tmio M, powerlib_domain] theorem charP4_eq {s : ℂ} (hl : c.lag s ≠ 0) :
    c.lag s * c.charF s = c.charP4 s := by
  simp only [charF, Keff, charP4]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem charP4d_eq {s : ℂ} (hl : c.lag s ≠ 0) :
    c.τ * c.charF s + c.lag s * c.charFd s = c.charP4d s := by
  simp only [charF, Keff, charFd, charP4d]
  field_simp
  simp only [lag]
  ring

/-- At the Hopf point, in the explicit real conditions
`pΩ² = τd₀ + b a ω_c` and `qΩ² = b d₀ − d₁`, the quartic factors as
`(s² + Ω²)(τs² + ps + q)`. -/
@[tmio M, powerlib_domain] theorem charP4_factor {Ω : ℝ}
    (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc)
    (hB : c.q4 Ω * Ω ^ 2 = c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)) (s : ℂ) :
    c.charP4 s = (s ^ 2 + (Ω : ℂ) ^ 2) * (c.τ * s ^ 2 + c.p4 * s + c.q4 Ω) := by
  have hA' : ((c.p4 * Ω ^ 2 : ℝ) : ℂ) = ((c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc : ℝ) : ℂ) := by rw [hA]
  have hB' : ((c.q4 Ω * Ω ^ 2 : ℝ) : ℂ) = ((c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H) : ℝ) : ℂ) := by rw [hB]
  push_cast at hA' hB'
  simp only [charP4, lag, a, p4, q4] at hA' hB' ⊢
  push_cast at hA' hB' ⊢
  linear_combination (-s) * hA' - hB'

@[tmio M, powerlib_domain] theorem charP4d_factor {Ω : ℝ}
    (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc) (s : ℂ) :
    c.charP4d s = 2 * s * (c.τ * s ^ 2 + c.p4 * s + c.q4 Ω) +
      (s ^ 2 + (Ω : ℂ) ^ 2) * (2 * c.τ * s + c.p4) := by
  have hA' : ((c.p4 * Ω ^ 2 : ℝ) : ℂ) = ((c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc : ℝ) : ℂ) := by rw [hA]
  push_cast at hA'
  simp only [charP4d, lag, a, p4, q4] at hA' ⊢
  push_cast at hA' ⊢
  linear_combination -hA'

/-- At the explicit Hopf point with `p > 0`: `F(jΩ) = 0`, `F'(jΩ) ≠ 0` (a simple pair) and
`F(2jΩ) ≠ 0` (no resonance of the forced response). -/
@[tmio M, powerlib_domain] theorem hopf_facts (hτ : c.τ ≠ 0) {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hp : c.p4 ≠ 0) (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc)
    (hB : c.q4 Ω * Ω ^ 2 = c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)) :
    c.charF (Ω * I) = 0 ∧ c.charFd (Ω * I) ≠ 0 ∧ c.charF (2 * Ω * I) ≠ 0 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hl1 := c.lag_ne hτ hΩ
  have hl2 : c.lag (2 * Ω * I) ≠ 0 := by
    have := c.lag_ne (ω := 2 * Ω) hτ (mul_ne_zero two_ne_zero hΩ); push_cast at this; exact this
  have hR : ∀ k : ℝ, k ≠ 0 → c.τ * ((k : ℂ) * I) ^ 2 + c.p4 * ((k : ℂ) * I) + c.q4 Ω ≠ 0 := by
    intro k hk h
    have him : (c.τ * ((k : ℂ) * I) ^ 2 + c.p4 * ((k : ℂ) * I) + c.q4 Ω).im = c.p4 * k := by
      simp [pow_two, Complex.mul_im, Complex.mul_re]
    rw [h, Complex.zero_im] at him
    rcases mul_eq_zero.mp him.symm with h1 | h1
    · exact hp h1
    · exact hk h1
  have hF : c.charF (Ω * I) = 0 := by
    have h := c.charP4_eq hl1
    rw [c.charP4_factor hA hB, show ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 by
      linear_combination (Ω : ℂ) ^ 2 * I_sq, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hl1
  refine ⟨hF, ?_, ?_⟩
  · intro hd
    have h := c.charP4d_eq hl1
    rw [hF, hd, mul_zero, mul_zero, add_zero, c.charP4d_factor hA,
      show ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 by linear_combination (Ω : ℂ) ^ 2 * I_sq,
      zero_mul, add_zero] at h
    have h2 : (2 * ((Ω : ℂ) * I)) * (c.τ * ((Ω : ℂ) * I) ^ 2 + c.p4 * ((Ω : ℂ) * I) + c.q4 Ω) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero)) (hR Ω hΩ)
    exact h2 h.symm
  · intro h0
    have h := c.charP4_eq hl2
    rw [h0, mul_zero, c.charP4_factor hA hB] at h
    have e : (2 * (Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
      linear_combination 4 * (Ω : ℂ) ^ 2 * I_sq
    rw [e] at h
    have h3 := hR (2 * Ω) (mul_ne_zero two_ne_zero hΩ)
    push_cast at h3
    rw [show (2 * (Ω : ℂ) * I) = (2 * (Ω : ℂ)) * I by ring] at h
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hΩc)) h3 h.symm

/-- Geometric simplicity of `jΩ`: every eigenvector is a multiple of `right(jΩ)`. -/
@[tmio M, powerlib_domain] theorem hopf_simple (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    {Ω : ℝ} (hΩ : Ω ≠ 0) (hFd : c.charFd (Ω * I) ≠ 0) (v : Fin 4 → ℂ)
    (h : c.A0r.map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v) :
    v = (c.left (Ω * I) ⬝ᵥ v) • c.right (Ω * I) := by
  have hl := c.lag_ne hτ hΩ
  rcases c.eig_cases hω0 hH hτ h with h0 | ⟨hv, -⟩
  · exact absurd h0 hl
  · conv_rhs => rw [hv]
    rw [dotProduct_smul, c.left_right hω0 hH hl hFd, smul_eq_mul, mul_one]
    exact hv

/-- Every eigenvalue other than `±jΩ` lies in the open left half plane when the Q–V pole and the
remaining quadratic `τs² + ps + q` are stable (`τ, b, p, q > 0`). -/
@[tmio M, powerlib_domain] theorem eig_stable (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ)
    (hb : 0 < c.b) {Ω : ℝ} (hp : 0 < c.p4) (hq : 0 < c.q4 Ω) (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc)
    (hB : c.q4 Ω * Ω ^ 2 = c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H))
    {μ : ℂ} {v : Fin 4 → ℂ} (hv : v ≠ 0) (h : c.A0r.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (h1 : μ ≠ (Ω : ℂ) * I) (h2 : μ ≠ -((Ω : ℂ) * I)) : μ.re < 0 := by
  rcases eq_or_ne (c.lag μ) 0 with hl | hl
  · have := congrArg Complex.re hl
    simp [lag] at this
    have : μ.re = -c.b / c.τ := by field_simp; linarith
    rw [this, neg_div]
    exact neg_neg_of_pos (div_pos hb hτ)
  rcases c.eig_cases hω0 hH hτ.ne' h with h0 | ⟨-, hF⟩
  · exact absurd h0 hl
  have hP := c.charP4_eq hl
  rw [hF hv, mul_zero, c.charP4_factor hA hB] at hP
  have hne : μ ^ 2 + (Ω : ℂ) ^ 2 ≠ 0 := by
    have : μ ^ 2 + (Ω : ℂ) ^ 2 = (μ - (Ω : ℂ) * I) * (μ + (Ω : ℂ) * I) := by
      linear_combination (Ω : ℂ) ^ 2 * I_sq
    rw [this]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))
  have hR := (mul_eq_zero.mp hP.symm).resolve_left hne
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  refine ((Criteria.quadratic_roots_re_neg_iff (c.p4 / c.τ) (c.q4 Ω / c.τ)).2
    ⟨div_pos hp hτ, div_pos hq hτ⟩) μ ?_
  push_cast
  field_simp
  linear_combination hR

/-! ### End-to-end with explicit conditions -/

/-- The synchronizing core with a dynamic Q–V loop at any operating point, grid-voltage
modulation, end-to-end, stability, with every spectral hypothesis explicit: at the Hopf point
`pΩ² = τd₀ + b a ω_c`, `qΩ² = b d₀ − d₁` with a stable Q–V pole and remaining pair
(`τ, b, p, q > 0`), `Re λ₁ < 0` and `|g_V/2| < |λ₁|` give the forced periodic orbit with all Floquet
multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_qv_hopf_stable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hb : 0 < c.b) (hp : 0 < c.p4) (hq : 0 < c.q4 Ω)
    (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc)
    (hB : c.q4 Ω * Ω ^ 2 = c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H))
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV Ω Vh / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => ParametricResonance.ForcedOrbit.smJ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
            (qxeq P δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, hF2⟩ := c.hopf_facts hτ.ne' hΩ.ne' hp.ne' hA hB
  have hl := c.lag_ne hτ.ne' hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ.ne' hl hF) (c.left_eig hω0 hH hτ.ne' hl hF)
      (c.left_right hω0 hH hl hFd) (c.hopf_simple hω0 hH hτ.ne' hΩ.ne' hFd)
      (fun μ v hv h h1 h2 => c.eig_stable hω0 hH hτ hb hp hq hA hB hv h h1 h2)
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ.ne' hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

/-- The dynamic Q–V core at any operating point with explicit conditions, parametric
instability. -/
@[tmio M, powerlib_domain] theorem orbit_qv_hopf_unstable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hb : 0 < c.b) (hp : 0 < c.p4) (hq : 0 < c.q4 Ω)
    (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc)
    (hB : c.q4 Ω * Ω ^ 2 = c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H))
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖c.gV Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => ParametricResonance.ForcedOrbit.smJ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
          (qxeq P δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, hF2⟩ := c.hopf_facts hτ.ne' hΩ.ne' hp.ne' hA hB
  have hl := c.lag_ne hτ.ne' hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ.ne' hl hF) (c.left_eig hω0 hH hτ.ne' hl hF)
      (c.left_right hω0 hH hl hFd) (c.hopf_simple hω0 hH hτ.ne' hΩ.ne' hFd)
      (fun μ v hv h h1 h2 => c.eig_stable hω0 hH hτ hb hp hq hA hB hv h h1 h2)
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ.ne' hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_
  rw [hL, hR, hA1]; exact hg

/-- The dynamic Q–V core at any operating point with explicit conditions: the forced orbit
exists and is locally exponentially stable for the nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_qv_hopf_exp_stable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hb : 0 < c.b) (hp : 0 < c.p4) (hq : 0 < c.q4 Ω)
    (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc)
    (hB : c.q4 Ω * Ω ^ 2 = c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H))
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV Ω Vh / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
        V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t v => c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + v,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, hF2⟩ := c.hopf_facts hτ.ne' hΩ.ne' hp.ne' hA hB
  have hl := c.lag_ne hτ.ne' hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ.ne' hl hF) (c.left_eig hω0 hH hτ.ne' hl hF)
      (c.left_right hω0 hH hl hFd) (c.hopf_simple hω0 hH hτ.ne' hΩ.ne' hFd)
      (fun μ v hv h h1 h2 => c.eig_stable hω0 hH hτ hb hp hq hA hB hv h h1 h2)
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ.ne' hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

/-! ### The voltage pump in compact form -/

/-- The modulation of the effective synchronizing coefficient along the first-order orbit:
`ρ_eff = A_δ + A_E r̄_E − (k_q P_E/(τjΩ + b))(B_δ + B_E r̄_E)`, with `A`, `B` the `δ` and `E`
columns of the modulated rows of `P` and `Q` and `r̄_E = conj(r_E(jΩ))`. -/
def rhoEff (Ω Vh : ℝ) : ℂ :=
  (c.Pδδ * c.forced (2 * Ω * I) Vh 0 + c.PδE * c.forced (2 * Ω * I) Vh 3 + c.PδV * Vh) +
    (c.PδE * c.forced (2 * Ω * I) Vh 0 + c.PEE * c.forced (2 * Ω * I) Vh 3 + c.PEV * Vh) *
      star (c.right (Ω * I) 3) -
    c.kq * c.PE / c.lag (Ω * I) *
      ((c.Qδδ * c.forced (2 * Ω * I) Vh 0 + c.QδE * c.forced (2 * Ω * I) Vh 3 + c.QδV * Vh) +
        (c.QδE * c.forced (2 * Ω * I) Vh 0 + c.QEE * c.forced (2 * Ω * I) Vh 3 + c.QEV * Vh) *
          star (c.right (Ω * I) 3))

/-- `g_V = −(ω₀ω_c/(2H F'(jΩ))) ρ_eff`: the three-state form `g = −(d₀/D'(λ))(ρ/P_δ)` of
`VoltageModulationQV.pump_eq`, with the modulation of the effective coefficient. -/
@[tmio M, powerlib_domain] theorem gV_compact (hτ : c.τ ≠ 0) (Ω Vh : ℝ) :
    c.gV Ω Vh = -(c.ω0 * c.ωc / (2 * c.H * c.charFd (Ω * I))) * c.rhoEff Ω Vh := by
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  rw [gV_eq]
  simp only [left, rhoEff]
  simp
  field_simp
  ring

/-- At the explicit Hopf point:
`g_V = −ω₀ω_c (τjΩ + b) ρ_eff/(2H · 2jΩ (q − τΩ² + jpΩ))`. -/
@[tmio M, powerlib_domain] theorem gV_hopf (hτ : c.τ ≠ 0) {Ω : ℝ} (hΩ : Ω ≠ 0) (hp : c.p4 ≠ 0)
    (hA : c.p4 * Ω ^ 2 = c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      c.b * (c.D / (2 * c.H)) * c.ωc)
    (hB : c.q4 Ω * Ω ^ 2 = c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)) (Vh : ℝ) :
    c.gV Ω Vh = -(c.ω0 * c.ωc * c.lag (Ω * I) /
      (2 * c.H * (2 * ((Ω : ℂ) * I) * ((c.q4 Ω - c.τ * Ω ^ 2 : ℝ) + (c.p4 * Ω : ℝ) * I)))) *
        c.rhoEff Ω Vh := by
  obtain ⟨hF, hFd, -⟩ := c.hopf_facts hτ hΩ hp hA hB
  have hl := c.lag_ne hτ hΩ
  have h := c.charP4d_eq hl
  rw [hF, mul_zero, zero_add, c.charP4d_factor hA,
    show ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 by linear_combination (Ω : ℂ) ^ 2 * I_sq,
    zero_mul, add_zero] at h
  have hR : c.τ * ((Ω : ℂ) * I) ^ 2 + c.p4 * ((Ω : ℂ) * I) + c.q4 Ω =
      ((c.q4 Ω - c.τ * Ω ^ 2 : ℝ) : ℂ) + ((c.p4 * Ω : ℝ) : ℂ) * I := by
    push_cast; linear_combination (c.τ * (Ω : ℂ) ^ 2) * I_sq
  rw [hR] at h
  have hd : c.charFd (Ω * I) = 2 * ((Ω : ℂ) * I) *
      (((c.q4 Ω - c.τ * Ω ^ 2 : ℝ) : ℂ) + ((c.p4 * Ω : ℝ) : ℂ) * I) / c.lag (Ω * I) := by
    rw [← h]; field_simp
  rw [c.gV_compact hτ, hd]
  field_simp

/-! ### Linear combinations of port maps -/

omit c in
@[tmio T, powerlib_foundation] theorem fderiv_comb {f g : (ℝ × ℝ) × ℝ → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (α β γ : ℝ) (p e : (ℝ × ℝ) × ℝ) :
    fderiv ℝ (fun q => (α * f q + β * g q) / γ) p e =
      (α * fderiv ℝ f p e + β * fderiv ℝ g p e) / γ := by
  have h : (fun q => (α * f q + β * g q) / γ) = fun q => (α / γ) * f q + (β / γ) * g q := by
    funext q; ring
  have h2 : HasFDerivAt (fun q => α / γ * f q + β / γ * g q)
      ((α / γ) • fderiv ℝ f p + (β / γ) • fderiv ℝ g p) p :=
    ((hf p).hasFDerivAt.const_mul (α / γ)).add ((hg p).hasFDerivAt.const_mul (β / γ))
  rw [h, h2.fderiv]
  simp
  ring

omit c in
@[tmio T, powerlib_foundation] theorem dδ_comb {f g : (ℝ × ℝ) × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (α β γ : ℝ) :
    dδ (fun q => (α * f q + β * g q) / γ) = fun q => (α * dδ f q + β * dδ g q) / γ :=
  funext fun q => fderiv_comb hf hg α β γ q _

omit c in
@[tmio T, powerlib_foundation] theorem dE_comb {f g : (ℝ × ℝ) × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (α β γ : ℝ) :
    dE (fun q => (α * f q + β * g q) / γ) = fun q => (α * dE f q + β * dE g q) / γ :=
  funext fun q => fderiv_comb hf hg α β γ q _

omit c in
@[tmio T, powerlib_foundation] theorem dV_comb {f g : (ℝ × ℝ) × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (α β γ : ℝ) :
    dV (fun q => (α * f q + β * g q) / γ) = fun q => (α * dV f q + β * dV g q) / γ :=
  funext fun q => fderiv_comb hf hg α β γ q _

/-! ### EMF behind an impedance `R + jX` -/

/-- Active power of `E∠δ` behind `R + jX` against `V∠0`:
`P = (R(E² − EV cos δ) + X EV sin δ)/(R² + X²)`. -/
def lossyP (R X : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ := (R * linkQ 1 q + X * linkP 1 q) / (R ^ 2 + X ^ 2)

/-- Reactive power at the EMF: `Q = (X(E² − EV cos δ) − R EV sin δ)/(R² + X²)`. -/
def lossyQ (R X : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  (X * linkQ 1 q + -R * linkP 1 q) / (R ^ 2 + X ^ 2)

omit c in
/-- Without resistance the impedance is the lossless link. -/
@[tmio M, powerlib_domain] theorem lossy_zero_R {X : ℝ} (hX : X ≠ 0) :
    lossyP 0 X = linkP X ∧ lossyQ 0 X = linkQ X := by
  constructor <;> funext q <;> simp [lossyP, lossyQ, linkP, linkQ] <;> field_simp

omit c in
@[tmio M, powerlib_domain] theorem contDiff_lossyP (R X : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (lossyP R X) := by
  unfold lossyP linkP linkQ; fun_prop

omit c in
@[tmio M, powerlib_domain] theorem contDiff_lossyQ (R X : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (lossyQ R X) := by
  unfold lossyQ linkP linkQ; fun_prop

/-- The dynamic Q–V core of the EMF behind `R + jX` at `(δ₀, E₀, V₀)`: the partial derivatives
of `lossyP`, `lossyQ` there (explicit values: `lossy_partials`). -/
def lossyCore (ω0 H D ωc τ kq R X δ0 E0 V0 : ℝ) : DynQV where
  ω0 := ω0
  H := H
  D := D
  ωc := ωc
  τ := τ
  kq := kq
  Pδ := dδ (lossyP R X) ((δ0, E0), V0)
  PE := dE (lossyP R X) ((δ0, E0), V0)
  PV := dV (lossyP R X) ((δ0, E0), V0)
  Qδ := dδ (lossyQ R X) ((δ0, E0), V0)
  QE := dE (lossyQ R X) ((δ0, E0), V0)
  QV := dV (lossyQ R X) ((δ0, E0), V0)
  Pδδ := dδ (dδ (lossyP R X)) ((δ0, E0), V0)
  PδE := dE (dδ (lossyP R X)) ((δ0, E0), V0)
  PEE := dE (dE (lossyP R X)) ((δ0, E0), V0)
  PδV := dV (dδ (lossyP R X)) ((δ0, E0), V0)
  PEV := dV (dE (lossyP R X)) ((δ0, E0), V0)
  Qδδ := dδ (dδ (lossyQ R X)) ((δ0, E0), V0)
  QδE := dE (dδ (lossyQ R X)) ((δ0, E0), V0)
  QEE := dE (dE (lossyQ R X)) ((δ0, E0), V0)
  QδV := dV (dδ (lossyQ R X)) ((δ0, E0), V0)
  QEV := dV (dE (lossyQ R X)) ((δ0, E0), V0)

omit c in
/-- The first partial derivatives of the impedance port maps, in closed form (`Z² = R² + X²`):
`P_δ = EV(R sin δ + X cos δ)/Z²`, `P_E = (2ER − VR cos δ + VX sin δ)/Z²`,
`P_V = E(X sin δ − R cos δ)/Z²`, `Q_δ = EV(X sin δ − R cos δ)/Z²`,
`Q_E = (2EX − VX cos δ − VR sin δ)/Z²`, `Q_V = −E(X cos δ + R sin δ)/Z²`. -/
@[tmio M, powerlib_domain] theorem lossy_partials (R X : ℝ) (q : (ℝ × ℝ) × ℝ) :
    dδ (lossyP R X) q = q.1.2 * q.2 * (R * Real.sin q.1.1 + X * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dE (lossyP R X) q =
      (2 * q.1.2 * R - q.2 * R * Real.cos q.1.1 + q.2 * X * Real.sin q.1.1) / (R ^ 2 + X ^ 2) ∧
    dV (lossyP R X) q = q.1.2 * (X * Real.sin q.1.1 - R * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dδ (lossyQ R X) q = q.1.2 * q.2 * (X * Real.sin q.1.1 - R * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dE (lossyQ R X) q =
      (2 * q.1.2 * X - q.2 * X * Real.cos q.1.1 - q.2 * R * Real.sin q.1.1) / (R ^ 2 + X ^ 2) ∧
    dV (lossyQ R X) q = -(q.1.2 * (X * Real.cos q.1.1 + R * Real.sin q.1.1)) / (R ^ 2 + X ^ 2) := by
  have hP := (contDiff_linkP 1 (n := 1)).differentiable (by norm_num)
  have hQ := (contDiff_linkQ 1 (n := 1)).differentiable (by norm_num)
  have eP : lossyP R X = fun q => (R * linkQ 1 q + X * linkP 1 q) / (R ^ 2 + X ^ 2) := rfl
  have eQ : lossyQ R X = fun q => (X * linkQ 1 q + -R * linkP 1 q) / (R ^ 2 + X ^ 2) := rfl
  simp only [eP, eQ, dδ_comb hQ hP, dE_comb hQ hP, dV_comb hQ hP,
    dδ_linkP, dE_linkP, dV_linkP, dδ_linkQ, dE_linkQ, dV_linkQ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

omit c in
/-- The second partial derivatives of the impedance port maps, in closed form (`Z² = R² + X²`):
`P_δδ = EV(R cos δ − X sin δ)/Z²`, `P_δE = V(R sin δ + X cos δ)/Z²`, `P_EE = 2R/Z²`,
`P_δV = E(R sin δ + X cos δ)/Z²`, `P_EV = (X sin δ − R cos δ)/Z²`,
`Q_δδ = EV(X cos δ + R sin δ)/Z²`, `Q_δE = V(X sin δ − R cos δ)/Z²`, `Q_EE = 2X/Z²`,
`Q_δV = E(X sin δ − R cos δ)/Z²`, `Q_EV = −(X cos δ + R sin δ)/Z²`. -/
@[tmio M, powerlib_domain] theorem lossy_second_partials (R X : ℝ) (q : (ℝ × ℝ) × ℝ) :
    dδ (dδ (lossyP R X)) q = q.1.2 * q.2 * (R * Real.cos q.1.1 - X * Real.sin q.1.1) / (R ^ 2 + X ^ 2) ∧
    dE (dδ (lossyP R X)) q = q.2 * (R * Real.sin q.1.1 + X * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dE (dE (lossyP R X)) q = 2 * R / (R ^ 2 + X ^ 2) ∧
    dV (dδ (lossyP R X)) q = q.1.2 * (R * Real.sin q.1.1 + X * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dV (dE (lossyP R X)) q = (X * Real.sin q.1.1 - R * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dδ (dδ (lossyQ R X)) q = q.1.2 * q.2 * (X * Real.cos q.1.1 + R * Real.sin q.1.1) / (R ^ 2 + X ^ 2) ∧
    dE (dδ (lossyQ R X)) q = q.2 * (X * Real.sin q.1.1 - R * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dE (dE (lossyQ R X)) q = 2 * X / (R ^ 2 + X ^ 2) ∧
    dV (dδ (lossyQ R X)) q = q.1.2 * (X * Real.sin q.1.1 - R * Real.cos q.1.1) / (R ^ 2 + X ^ 2) ∧
    dV (dE (lossyQ R X)) q = -(X * Real.cos q.1.1 + R * Real.sin q.1.1) / (R ^ 2 + X ^ 2) := by
  have hP := (contDiff_linkP 1 (n := 1)).differentiable (by norm_num)
  have hQ := (contDiff_linkQ 1 (n := 1)).differentiable (by norm_num)
  have hPδ : Differentiable ℝ (dδ (linkP 1)) := by rw [dδ_linkP]; fun_prop
  have hQδ : Differentiable ℝ (dδ (linkQ 1)) := by rw [dδ_linkQ]; fun_prop
  have hPE : Differentiable ℝ (dE (linkP 1)) := by rw [dE_linkP]; fun_prop
  have hQE : Differentiable ℝ (dE (linkQ 1)) := by rw [dE_linkQ]; fun_prop
  have eP : lossyP R X = fun q => (R * linkQ 1 q + X * linkP 1 q) / (R ^ 2 + X ^ 2) := rfl
  have eQ : lossyQ R X = fun q => (X * linkQ 1 q + -R * linkP 1 q) / (R ^ 2 + X ^ 2) := rfl
  simp only [eP, eQ, dδ_comb hQ hP, dE_comb hQ hP, dδ_comb hQδ hPδ, dE_comb hQδ hPδ,
    dV_comb hQδ hPδ, dE_comb hQE hPE, dV_comb hQE hPE]
  simp only [dδ_dδ_linkP, dE_dδ_linkP, dE_dE_linkP, dV_dδ_linkP, dV_dE_linkP, dδ_dδ_linkQ,
    dE_dδ_linkQ, dE_dE_linkQ, dV_dδ_linkQ, dV_dE_linkQ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- The EMF behind a reactance with a dynamic Q–V loop at any operating point, end-to-end, stability, with explicit conditions (`orbit_qv_hopf_stable` with the port maps of the link). -/
@[tmio M, powerlib_domain] theorem orbit_link_hopf_stable {ω0 H D ωc τ kq X δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : 0 < τ)
    (hb : 0 < (linkCore ω0 H D ωc τ kq X δ0 E0 V0).b) (hp : 0 < (linkCore ω0 H D ωc τ kq X δ0 E0 V0).p4) (hq : 0 < (linkCore ω0 H D ωc τ kq X δ0 E0 V0).q4 Ω)
    (hA : (linkCore ω0 H D ωc τ kq X δ0 E0 V0).p4 * Ω ^ 2 = (linkCore ω0 H D ωc τ kq X δ0 E0 V0).τ * ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).ω0 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).Pδ / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H)) +
      (linkCore ω0 H D ωc τ kq X δ0 E0 V0).b * ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).D / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H)) * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc)
    (hB : (linkCore ω0 H D ωc τ kq X δ0 E0 V0).q4 Ω * Ω ^ 2 = (linkCore ω0 H D ωc τ kq X δ0 E0 V0).b * ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).ω0 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).Pδ / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H)) -
      (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ω0 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).kq * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).PE * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).Qδ / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H))
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X δ0 E0 V0).right (Ω * I))).re < 0)
    (hg : ‖(linkCore ω0 H D ωc τ kq X δ0 E0 V0).gV Ω Vh / 2‖ ^ 2 < ‖(linkCore ω0 H D ωc τ kq X δ0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X δ0 E0 V0).right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X) ((linkP X) ((δ0, E0), V0)) E0 ((linkQ X) ((δ0, E0), V0)) (qxeq (linkP X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X) ((linkP X) ((δ0, E0), V0)) E0 ((linkQ X) ((δ0, E0), V0)) (qxeq (linkP X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => ParametricResonance.ForcedOrbit.smJ ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X) ((linkP X) ((δ0, E0), V0)) E0 ((linkQ X) ((δ0, E0), V0)))
            (qxeq (linkP X) δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 :=
  (linkCore ω0 H D ωc τ kq X δ0 E0 V0).orbit_qv_hopf_stable (contDiff_linkP X) (contDiff_linkQ X)
    hΩ hω0 hH hτ (by rw [dδ_linkP]; rfl)
    (by rw [dE_linkP]; rfl)
    (by rw [dV_linkP]; rfl)
    (by rw [dδ_linkQ]; rfl)
    (by rw [dE_linkQ]; rfl)
    (by rw [dV_linkQ]; rfl)
    (by rw [dδ_dδ_linkP]; rfl)
    (by rw [dE_dδ_linkP]; rfl)
    (by rw [dE_dE_linkP]; rfl)
    (by rw [dV_dδ_linkP]; rfl)
    (by rw [dV_dE_linkP]; rfl)
    (by rw [dδ_dδ_linkQ]; rfl)
    (by rw [dE_dδ_linkQ]; rfl)
    (by rw [dE_dE_linkQ]; rfl)
    (by rw [dV_dδ_linkQ]; rfl)
    (by rw [dV_dE_linkQ]; rfl) hb hp hq hA hB Vh A0' hs hg

/-- The EMF behind a reactance with a dynamic Q–V loop at any operating point, end-to-end, parametric instability, with explicit conditions. -/
@[tmio M, powerlib_domain] theorem orbit_link_hopf_unstable {ω0 H D ωc τ kq X δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : 0 < τ)
    (hb : 0 < (linkCore ω0 H D ωc τ kq X δ0 E0 V0).b) (hp : 0 < (linkCore ω0 H D ωc τ kq X δ0 E0 V0).p4) (hq : 0 < (linkCore ω0 H D ωc τ kq X δ0 E0 V0).q4 Ω)
    (hA : (linkCore ω0 H D ωc τ kq X δ0 E0 V0).p4 * Ω ^ 2 = (linkCore ω0 H D ωc τ kq X δ0 E0 V0).τ * ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).ω0 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).Pδ / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H)) +
      (linkCore ω0 H D ωc τ kq X δ0 E0 V0).b * ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).D / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H)) * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc)
    (hB : (linkCore ω0 H D ωc τ kq X δ0 E0 V0).q4 Ω * Ω ^ 2 = (linkCore ω0 H D ωc τ kq X δ0 E0 V0).b * ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).ω0 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).Pδ / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H)) -
      (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ω0 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).ωc * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).kq * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).PE * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).Qδ / (2 * (linkCore ω0 H D ωc τ kq X δ0 E0 V0).H))
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖(linkCore ω0 H D ωc τ kq X δ0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X δ0 E0 V0).right (Ω * I))‖ ^ 2 < ‖(linkCore ω0 H D ωc τ kq X δ0 E0 V0).gV Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X) ((linkP X) ((δ0, E0), V0)) E0 ((linkQ X) ((δ0, E0), V0)) (qxeq (linkP X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X) ((linkP X) ((δ0, E0), V0)) E0 ((linkQ X) ((δ0, E0), V0)) (qxeq (linkP X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => ParametricResonance.ForcedOrbit.smJ ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X) ((linkP X) ((δ0, E0), V0)) E0 ((linkQ X) ((δ0, E0), V0)))
          (qxeq (linkP X) δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  (linkCore ω0 H D ωc τ kq X δ0 E0 V0).orbit_qv_hopf_unstable (contDiff_linkP X) (contDiff_linkQ X)
    hΩ hω0 hH hτ (by rw [dδ_linkP]; rfl)
    (by rw [dE_linkP]; rfl)
    (by rw [dV_linkP]; rfl)
    (by rw [dδ_linkQ]; rfl)
    (by rw [dE_linkQ]; rfl)
    (by rw [dV_linkQ]; rfl)
    (by rw [dδ_dδ_linkP]; rfl)
    (by rw [dE_dδ_linkP]; rfl)
    (by rw [dE_dE_linkP]; rfl)
    (by rw [dV_dδ_linkP]; rfl)
    (by rw [dV_dE_linkP]; rfl)
    (by rw [dδ_dδ_linkQ]; rfl)
    (by rw [dE_dδ_linkQ]; rfl)
    (by rw [dE_dE_linkQ]; rfl)
    (by rw [dV_dδ_linkQ]; rfl)
    (by rw [dV_dE_linkQ]; rfl) hb hp hq hA hB Vh A0' hg

/-- The EMF behind an impedance `R + jX` with a dynamic Q–V loop at any operating point, end-to-end, stability, with explicit conditions (the partial derivatives in closed form: `lossy_partials`). -/
@[tmio M, powerlib_domain] theorem orbit_lossy_hopf_stable {ω0 H D ωc τ kq R X δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : 0 < τ)
    (hb : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b) (hp : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).p4) (hq : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).q4 Ω)
    (hA : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).p4 * Ω ^ 2 = (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).τ * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) +
      (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).D / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc)
    (hB : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).q4 Ω * Ω ^ 2 = (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) -
      (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).kq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).PE * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Qδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H))
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).right (Ω * I))).re < 0)
    (hg : ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).gV Ω Vh / 2‖ ^ 2 < ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfield (lossyP R X) (lossyQ R X) ((lossyP R X) ((δ0, E0), V0)) E0 ((lossyQ R X) ((δ0, E0), V0)) (qxeq (lossyP R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfield (lossyP R X) (lossyQ R X) ((lossyP R X) ((δ0, E0), V0)) E0 ((lossyQ R X) ((δ0, E0), V0)) (qxeq (lossyP R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => ParametricResonance.ForcedOrbit.smJ ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfield (lossyP R X) (lossyQ R X) ((lossyP R X) ((δ0, E0), V0)) E0 ((lossyQ R X) ((δ0, E0), V0)))
            (qxeq (lossyP R X) δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 :=
  (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).orbit_qv_hopf_stable (contDiff_lossyP R X) (contDiff_lossyQ R X)
    hΩ hω0 hH hτ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hb hp hq hA hB Vh A0' hs hg

/-- The EMF behind an impedance `R + jX` with a dynamic Q–V loop at any operating point, end-to-end, parametric instability, with explicit conditions. -/
@[tmio M, powerlib_domain] theorem orbit_lossy_hopf_unstable {ω0 H D ωc τ kq R X δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : 0 < τ)
    (hb : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b) (hp : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).p4) (hq : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).q4 Ω)
    (hA : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).p4 * Ω ^ 2 = (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).τ * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) +
      (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).D / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc)
    (hB : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).q4 Ω * Ω ^ 2 = (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) -
      (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).kq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).PE * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Qδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H))
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).right (Ω * I))‖ ^ 2 < ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).gV Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfield (lossyP R X) (lossyQ R X) ((lossyP R X) ((δ0, E0), V0)) E0 ((lossyQ R X) ((δ0, E0), V0)) (qxeq (lossyP R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfield (lossyP R X) (lossyQ R X) ((lossyP R X) ((δ0, E0), V0)) E0 ((lossyQ R X) ((δ0, E0), V0)) (qxeq (lossyP R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => ParametricResonance.ForcedOrbit.smJ ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfield (lossyP R X) (lossyQ R X) ((lossyP R X) ((δ0, E0), V0)) E0 ((lossyQ R X) ((δ0, E0), V0)))
          (qxeq (lossyP R X) δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) :=
  (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).orbit_qv_hopf_unstable (contDiff_lossyP R X) (contDiff_lossyQ R X)
    hΩ hω0 hH hτ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hb hp hq hA hB Vh A0' hg

end DynQV
end VoltageModulation
end powerlib.GFM
