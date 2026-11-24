import theorem.ParametricResonance.ElementDecomposition
import theorem.LTI.Sampling
import theorem.Criteria.Hurwitz2
import theorem.Periodic.Floquet

/-! # The 2:1 resonant normal form: the slow flow as an exact Floquet description

The modal projection of the forced variational equation isolates the 2:1 resonant term with the
coefficient `g/2`, and for the resonant normal form `ż = λz + c e^{jω_p t} z̄` the first-order slow
flow is not an approximation: the monodromy matrix is `−exp(T M_slow)`, so the Floquet multipliers,
the Floquet stability boundary and the threshold `ε_crit = 2√(σ² + Δ²)/|g|` are exact.

Scope.
* Modal projection: a real state matrix `A₀` (complexified), a non-real simple mode `λ` with
  right eigenvector `r`, left eigenvector `u` (row, `u ⬝ᵥ r = 1`), and a state written as
  `x = z r + z̄ r̄ + w` with `u ⬝ᵥ w = 0` (the other modes); the periodic modulation is
  `Re{A₁ e^{jω_p t}} = (e A₁ + ē Ā₁)/2`, `e = e^{jω_p t}`.
* Normal form: the scalar complex equation `ż = (−σ + jΩ) z + c e^{jω t} z̄` with real `σ, Ω`,
  pump frequency `ω > 0` and complex `c` (`c = ε g/2` in the source), written as the real
  periodic linear system `ẋ = A(t) x` on `(Re z, Im z)` (`nfMatrix`), period `T = 2π/ω`; its
  transition and monodromy matrices are those of `theorem/Periodic/Transition.lean`.
* Not formalized: the near-identity (averaging) transformation that removes the non-resonant
  terms of the modal equation (`e z`, `ē z`, `ē z̄` and the coupling to `w`); it changes the
  Floquet exponents of the full system by `O(ε²)` in the classical theory. The exact statements
  here concern the projection identity and the normal form.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}`, `g_m = l_mᴴ A₁ r_m*`,
`A_m = |g_m|/(2√(σ_m² + Δ_m²))`, `ε_crit = 2√(σ_m² + Δ_m²)/|g_m|`), §2.5 ((7)).

Results.
* `modal_projection` — `u ⬝ᵥ (A₀ x) = λ z` and
  `u ⬝ᵥ (Re{A₁ e} x) = (g/2) e z̄ + (h₁/2) e z + (h₂/2) ē z + (h₃/2) ē z̄ + (u ⬝ᵥ (e A₁ + ē Ā₁) w)/2`
  with `g = pump A₁ u r`, `h₁ = u A₁ r`, `h₂ = u Ā₁ r`, `h₃ = u Ā₁ r̄`: the only term that is
  stationary in the frame `z = e^{jω t/2} A` is `(g/2) e z̄`.
* `nfMatrix_mulVec` — `nfMatrix` is the real form of `z ↦ (−σ + jΩ) z + c e^{jωt} z̄`.
* `nfMatrix_mul_rot` — `A(t) R(ωt/2) = R(ωt/2)((ω/2)J + M)` with `M` the slow-flow matrix
  `slowFlowMatrix σ (ω/2 − Ω) c` and `R` the rotation; hence `transition_nf`:
  `Φ(t, 0) = R(ωt/2) exp(t M)`, and `monodromy_nf`: `Φ(T, 0) = −exp(T M)`.
* `schurStable_monodromy_nf_iff` — every Floquet multiplier lies strictly inside the unit circle
  iff `σ > 0` and `|c|² < σ² + (ω/2 − Ω)²` (the slow flow is Hurwitz).
* `floquetUnstable_nf_of_lt`, `floquetUnstable_nf_of_neg` — `σ² + Δ² < |c|²` (any `σ`), or
  `σ < 0`, gives a Floquet multiplier strictly outside the unit circle.
* `nf_threshold` — with `c = ε g/2`, `σ > 0`, `ε ≥ 0`: Schur stability of the monodromy iff
  `ε |g| < 2√(σ² + Δ²)`, and `ε |g| > 2√(σ² + Δ²)` gives Floquet instability: the 2:1 criterion
  of the source is exact for the normal form.
-/

noncomputable section
namespace powerlib.ParametricResonance.NormalForm

open Matrix Complex Set ComplexConjugate
open scoped Matrix.Norms.Operator

/-! ## Modal projection -/

/-- Modal projection of the forced variational field: the 2:1 resonant term has coefficient
`g/2`. -/
@[tmio T, powerlib_foundation] theorem modal_projection {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {lam : ℂ} {u r : Fin n → ℂ} (hr : Linear.complexify A *ᵥ r = lam • r)
    (hu : vecMul u (Linear.complexify A) = lam • u) (hn : u ⬝ᵥ r = 1) (hlam : lam.im ≠ 0)
    (A₁ : Matrix (Fin n) (Fin n) ℂ) (e z : ℂ) {w : Fin n → ℂ} (hw : u ⬝ᵥ w = 0) :
    u ⬝ᵥ (Linear.complexify A *ᵥ (z • r + conj z • star r + w)) = lam * z ∧
      u ⬝ᵥ (((1 / 2 : ℂ) • (e • A₁ + conj e • A₁.map conj)) *ᵥ (z • r + conj z • star r + w)) =
        Element.pump A₁ u r / 2 * e * conj z + (u ⬝ᵥ (A₁ *ᵥ r)) / 2 * e * z +
          (u ⬝ᵥ (A₁.map conj *ᵥ r)) / 2 * conj e * z +
          (u ⬝ᵥ (A₁.map conj *ᵥ star r)) / 2 * conj e * conj z +
          (u ⬝ᵥ ((e • A₁ + conj e • A₁.map conj) *ᵥ w)) / 2 := by
  have h0 := Element.dotProduct_star_eq_zero hr hu hlam
  refine ⟨?_, ?_⟩
  · rw [dotProduct_mulVec, hu, smul_dotProduct, dotProduct_add, dotProduct_add, dotProduct_smul,
      dotProduct_smul, hn, h0, hw]
    simp
  · simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      dotProduct_add, dotProduct_smul, smul_eq_mul, Element.pump]
    ring

/-! ## The normal form as a real periodic system -/

/-- Real part of the pump `c e^{jωt}`. -/
def pumpRe (c : ℂ) (ω t : ℝ) : ℝ := c.re * Real.cos (ω * t) - c.im * Real.sin (ω * t)

/-- Imaginary part of the pump `c e^{jωt}`. -/
def pumpIm (c : ℂ) (ω t : ℝ) : ℝ := c.re * Real.sin (ω * t) + c.im * Real.cos (ω * t)

/-- Real state matrix of `ż = (−σ + jΩ) z + c e^{jωt} z̄` in the state `(Re z, Im z)`. -/
def nfMatrix (σ Ω ω : ℝ) (c : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-σ + pumpRe c ω t, -Ω + pumpIm c ω t; Ω + pumpIm c ω t, -σ - pumpRe c ω t]

/-- The quarter-turn `J`. -/
def quarter : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The rotation `R(θ) = cos θ I + sin θ J`. -/
def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
  Real.sin θ • quarter

@[tmio T, powerlib_foundation] theorem nfMatrix_mulVec (σ Ω ω : ℝ) (c z : ℂ) (t : ℝ) :
    nfMatrix σ Ω ω c t *ᵥ ![z.re, z.im] =
      ![((-(σ : ℂ) + Ω * I) * z + c * exp ((ω * t : ℝ) * I) * conj z).re,
        ((-(σ : ℂ) + Ω * I) * z + c * exp ((ω * t : ℝ) * I) * conj z).im] := by
  funext i
  fin_cases i <;>
    simp [nfMatrix, pumpRe, pumpIm, mulVec, dotProduct, Fin.sum_univ_two, Complex.exp_re,
      Complex.exp_im, Complex.mul_re, Complex.mul_im] <;> ring

@[tmio T, powerlib_foundation] theorem nfMatrix_mul_rot (σ Ω ω : ℝ) (c : ℂ) (t : ℝ) :
    nfMatrix σ Ω ω c t * rot (ω * t / 2) =
      rot (ω * t / 2) * ((ω / 2) • quarter + slowFlowMatrix σ (ω / 2 - Ω) c) := by
  set θ := ω * t / 2 with hθ
  have hωt : ω * t = 2 * θ := by rw [hθ]; ring
  have hsc := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nfMatrix, pumpRe, pumpIm, rot, quarter, slowFlowMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, hωt, Real.cos_two_mul, Real.sin_two_mul]
  · linear_combination (2 * c.re * Real.cos θ) * hsc
  · linear_combination (2 * c.im * Real.cos θ) * hsc
  · linear_combination (2 * c.im * Real.cos θ) * hsc
  · linear_combination (-2 * c.re * Real.cos θ) * hsc

@[tmio T, powerlib_foundation] theorem continuous_nfMatrix (σ Ω ω : ℝ) (c : ℂ) :
    Continuous (nfMatrix σ Ω ω c) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold nfMatrix pumpRe pumpIm
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] <;> fun_prop

@[tmio T, powerlib_foundation] theorem periodic_nfMatrix (σ Ω : ℝ) {ω : ℝ} (hω : ω ≠ 0)
    (c : ℂ) : Function.Periodic (nfMatrix σ Ω ω c) (2 * Real.pi / ω) := by
  intro t
  have h : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
  simp only [nfMatrix, pumpRe, pumpIm, h, Real.cos_add_two_pi, Real.sin_add_two_pi]

@[tmio T, powerlib_foundation] theorem hasDerivAt_rot (ω t : ℝ) :
    HasDerivAt (fun t => rot (ω * t / 2)) ((ω / 2) • (rot (ω * t / 2) * quarter)) t := by
  have hθ : HasDerivAt (fun t : ℝ => ω * t / 2) (ω / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul ω).div_const 2
  have h := ((Real.hasDerivAt_cos (ω * t / 2)).comp t hθ).smul_const
    (1 : Matrix (Fin 2) (Fin 2) ℝ) |>.add
    (((Real.hasDerivAt_sin (ω * t / 2)).comp t hθ).smul_const quarter)
  have hJ : quarter * quarter = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quarter, Matrix.mul_apply, Fin.sum_univ_two]
  refine h.congr_deriv ?_
  simp only [rot, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hJ, smul_neg, smul_add,
    smul_smul, Function.comp_apply]
  module

/-- The transition matrix of the normal form: `Φ(t, 0) = R(ωt/2) exp(t M)`. -/
@[tmio T, powerlib_foundation] theorem transition_nf (σ Ω : ℝ) {ω : ℝ} (hω : 0 < ω) (c : ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    Periodic.transition (nfMatrix σ Ω ω c) t 0 =
      rot (ω * t / 2) * NormedSpace.exp (t • slowFlowMatrix σ (ω / 2 - Ω) c) := by
  set M := slowFlowMatrix σ (ω / 2 - Ω) c
  obtain ⟨B, hB⟩ := Periodic.exists_bound_of_periodic (continuous_nfMatrix σ Ω ω c)
    (periodic_nfMatrix σ Ω hω.ne' c) (by positivity)
  have hY : IsIntegralCurveOn (fun t => rot (ω * t / 2) * NormedSpace.exp (t • M))
      (Periodic.matField (nfMatrix σ Ω ω c)) (Ici 0) := by
    intro s _
    have h : HasDerivAt (fun t => rot (ω * t / 2) * NormedSpace.exp (t • M))
        ((ω / 2) • (rot (ω * s / 2) * quarter) * NormedSpace.exp (s • M) +
          rot (ω * s / 2) * (M * NormedSpace.exp (s • M))) s :=
      (hasDerivAt_rot ω s).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) M s)
    have key : (ω / 2) • (rot (ω * s / 2) * quarter) * NormedSpace.exp (s • M) +
        rot (ω * s / 2) * (M * NormedSpace.exp (s • M)) =
        nfMatrix σ Ω ω c s * (rot (ω * s / 2) * NormedSpace.exp (s • M)) := by
      calc (ω / 2) • (rot (ω * s / 2) * quarter) * NormedSpace.exp (s • M) +
            rot (ω * s / 2) * (M * NormedSpace.exp (s • M))
          = (rot (ω * s / 2) * ((ω / 2) • quarter + M)) * NormedSpace.exp (s • M) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_assoc]
        _ = (nfMatrix σ Ω ω c s * rot (ω * s / 2)) * NormedSpace.exp (s • M) := by
            rw [nfMatrix_mul_rot]
        _ = _ := Matrix.mul_assoc _ _ _
    rw [key] at h
    exact h.hasDerivWithinAt
  have h := Periodic.transition_unique (continuous_nfMatrix σ Ω ω c) hB hY t ht
  simpa [rot] using h.symm

/-- The monodromy matrix of the normal form is `−exp(T M)`, `T = 2π/ω`. -/
@[tmio T, powerlib_foundation] theorem monodromy_nf (σ Ω : ℝ) {ω : ℝ} (hω : 0 < ω) (c : ℂ) :
    Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0 =
      -NormedSpace.exp ((2 * Real.pi / ω) • slowFlowMatrix σ (ω / 2 - Ω) c) := by
  rw [Periodic.monodromy, zero_add, transition_nf σ Ω hω c (by positivity)]
  have h : ω * (2 * Real.pi / ω) / 2 = Real.pi := by field_simp
  rw [h]
  simp [rot]

/-! ## Floquet stability of the normal form -/

@[tmio T, powerlib_foundation] private theorem schurStable_neg_iff (P : Matrix (Fin 2) (Fin 2) ℝ) :
    LTI.SchurStable (-P) ↔ LTI.SchurStable P := by
  have key : ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, LTI.SchurStable Q → LTI.SchurStable (-Q) := by
    intro Q hQ μ v hv h
    have h' : Q.map (algebraMap ℝ ℂ) *ᵥ v = (-μ) • v := by
      rw [Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a), Matrix.neg_mulVec] at h
      rw [neg_smul, ← h, neg_neg]
    simpa using hQ (-μ) v hv h'
  exact ⟨fun h => by simpa using key _ h, key P⟩

/-- Every Floquet multiplier of the normal form is strictly inside the unit circle iff `σ > 0` and
`|c|² < σ² + (ω/2 − Ω)²`. -/
@[tmio T, powerlib_foundation] theorem schurStable_monodromy_nf_iff (σ Ω : ℝ) {ω : ℝ}
    (hω : 0 < ω) (c : ℂ) :
    LTI.SchurStable (Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0) ↔
      0 < σ ∧ ‖c‖ ^ 2 < σ ^ 2 + (ω / 2 - Ω) ^ 2 := by
  rw [monodromy_nf σ Ω hω c, schurStable_neg_iff,
    ← LTI.isHurwitz_iff_schurStable_exp _ (by positivity), Criteria.isHurwitz_fin_two_iff,
    trace_slowFlowMatrix, det_slowFlowMatrix]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- A slow-flow eigenvalue `μ` with `Re μ > 0` gives the Floquet multiplier `−e^{μT}` outside the
unit circle. -/
@[tmio T, powerlib_foundation] private theorem floquetUnstable_nf_of_root (σ Ω : ℝ) {ω : ℝ} (hω : 0 < ω) (c : ℂ) {μ : ℂ}
    (hμ : (Linear.characteristicMatrix (slowFlowMatrix σ (ω / 2 - Ω) c) μ).det = 0)
    (hre : 0 < μ.re) :
    Periodic.FloquetUnstable (nfMatrix σ Ω ω c) (2 * Real.pi / ω) := by
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have heig : (slowFlowMatrix σ (ω / 2 - Ω) c).map (algebraMap ℝ ℂ) *ᵥ v = μ • v := by
    simp only [Linear.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hMv
    exact hMv.symm
  have hT : (0 : ℝ) ≤ 2 * Real.pi / ω := by positivity
  have hexp := Periodic.monodromy_const_mulVec_eigen _ hT 0 heig
  rw [Periodic.monodromy_const _ hT] at hexp
  refine ⟨-Complex.exp (μ * ((2 * Real.pi / ω : ℝ) : ℂ)), ?_, ?_⟩
  · rw [LTI.mem_spectrum_iff_exists_eigvec]
    refine ⟨v, hv, ?_⟩
    rw [monodromy_nf σ Ω hω c, Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a),
      Matrix.neg_mulVec, hexp, neg_smul]
  · rw [norm_neg, Complex.norm_exp]
    apply Real.one_lt_exp_iff.mpr
    have : (μ * ((2 * Real.pi / ω : ℝ) : ℂ)).re = μ.re * (2 * Real.pi / ω) := by
      simp [Complex.mul_re]
    rw [this]
    positivity

/-- `σ² + Δ² < |c|²` gives Floquet instability of the normal form (any sign of `σ`). -/
@[tmio T, powerlib_foundation] theorem floquetUnstable_nf_of_lt (σ Ω : ℝ) {ω : ℝ} (hω : 0 < ω)
    (c : ℂ) (h : σ ^ 2 + (ω / 2 - Ω) ^ 2 < ‖c‖ ^ 2) :
    Periodic.FloquetUnstable (nfMatrix σ Ω ω c) (2 * Real.pi / ω) := by
  have hle : (ω / 2 - Ω) ^ 2 ≤ ‖c‖ ^ 2 := by nlinarith [sq_nonneg σ]
  refine floquetUnstable_nf_of_root σ Ω hω c (slowFlow_real_roots σ (ω / 2 - Ω) c hle).1 ?_
  simp only [Complex.ofReal_re]
  have hlt : σ ^ 2 < ‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2 := by linarith
  have : |σ| < √(‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
  linarith [le_abs_self σ]

/-- Negative modal damping gives Floquet instability of the normal form. -/
@[tmio T, powerlib_foundation] theorem floquetUnstable_nf_of_neg {σ : ℝ} (Ω : ℝ) {ω : ℝ}
    (hω : 0 < ω) (c : ℂ) (hσ : σ < 0) :
    Periodic.FloquetUnstable (nfMatrix σ Ω ω c) (2 * Real.pi / ω) := by
  by_cases hc : (ω / 2 - Ω) ^ 2 ≤ ‖c‖ ^ 2
  · refine floquetUnstable_nf_of_root σ Ω hω c (slowFlow_real_roots σ (ω / 2 - Ω) c hc).1 ?_
    simp only [Complex.ofReal_re]
    have := Real.sqrt_nonneg (‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2)
    linarith
  · push Not at hc
    set s := √((ω / 2 - Ω) ^ 2 - ‖c‖ ^ 2)
    have hs : s ^ 2 = (ω / 2 - Ω) ^ 2 - ‖c‖ ^ 2 := Real.sq_sqrt (by linarith)
    refine floquetUnstable_nf_of_root σ Ω hω c (μ := -(σ : ℂ) + (s : ℂ) * I) ?_ ?_
    · rw [slowFlow_root_iff]
      have hs' : (s : ℂ) ^ 2 = (((ω / 2 - Ω) ^ 2 - ‖c‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast hs
      push_cast at hs' ⊢
      linear_combination (s : ℂ) ^ 2 * I_sq - hs'
    · simp; linarith

/-- The 2:1 criterion is exact for the normal form: with `c = ε g/2`, `σ > 0`, `ε ≥ 0`, the
multipliers are inside the unit circle iff `ε|g| < 2√(σ² + Δ²)`, and `ε|g| > 2√(σ² + Δ²)`
gives a multiplier outside. -/
@[tmio T, powerlib_foundation] theorem nf_threshold {σ Ω ω ε : ℝ} (hσ : 0 < σ) (hω : 0 < ω)
    (hε : 0 ≤ ε) (g : ℂ) :
    (LTI.SchurStable (Periodic.monodromy (nfMatrix σ Ω ω ((ε : ℂ) * g / 2))
        (2 * Real.pi / ω) 0) ↔ ε * ‖g‖ < 2 * √(σ ^ 2 + (ω / 2 - Ω) ^ 2)) ∧
      (2 * √(σ ^ 2 + (ω / 2 - Ω) ^ 2) < ε * ‖g‖ →
        Periodic.FloquetUnstable (nfMatrix σ Ω ω ((ε : ℂ) * g / 2)) (2 * Real.pi / ω)) := by
  have hn : ‖(ε : ℂ) * g / 2‖ = ε * ‖g‖ / 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε]; simp
  have hpos : 0 ≤ ε * ‖g‖ / 2 := by positivity
  have hS : 0 ≤ σ ^ 2 + (ω / 2 - Ω) ^ 2 := by positivity
  have key : ‖(ε : ℂ) * g / 2‖ ^ 2 < σ ^ 2 + (ω / 2 - Ω) ^ 2 ↔
      ε * ‖g‖ < 2 * √(σ ^ 2 + (ω / 2 - Ω) ^ 2) := by
    rw [hn, ← Real.sqrt_lt_sqrt_iff (sq_nonneg _), Real.sqrt_sq hpos]
    constructor <;> intro h <;> linarith
  have key' : σ ^ 2 + (ω / 2 - Ω) ^ 2 < ‖(ε : ℂ) * g / 2‖ ^ 2 ↔
      2 * √(σ ^ 2 + (ω / 2 - Ω) ^ 2) < ε * ‖g‖ := by
    rw [hn, ← Real.sqrt_lt_sqrt_iff hS, Real.sqrt_sq hpos]
    constructor <;> intro h <;> linarith
  refine ⟨?_, fun h => floquetUnstable_nf_of_lt σ Ω hω _ (key'.mpr h)⟩
  rw [schurStable_monodromy_nf_iff σ Ω hω, key]
  exact ⟨fun h => h.2, fun h => ⟨hσ, h⟩⟩

end powerlib.ParametricResonance.NormalForm
