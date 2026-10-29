import theorem.CurrentControl.PILoop

/-! # PCC-voltage feedforward with a dedicated low-pass filter

Model boundary.
* Single-axis PI current loop as in `PILoop.lean` (series R–L branch, `L > 0`, IN-positive
  current `i`, PLL-aligned axis, ideal decoupling, no delay / PWM / limits, continuous time),
  plus the feedforward filter state.
* State order `(i, ξ, ṽ) ∈ EuclideanSpace ℝ (Fin 3)`: `ξ = ∫ (i* − i) dt`, `ṽ` the low-passed PCC
  voltage.
* Plant `L di/dt = v − v^conv − R i`; controller `v^conv = −(Kp (i* − i) + Ki ξ) + ṽ`;
  filter `τ dṽ/dt = v − ṽ` with an exact measurement `v^meas = v` (noise excluded).
* Inputs `(i*, v)`, outputs `(i, ṽ)`; held constant in the tracking statement.

Source: work-sync `theory/T-voltage-feedforward.md` §1.3, §1.4, §2.2;
`theory/T-gfl-control.md` §1.4.2, §1.4.4; `theory/T-gfl-reduced-order-dynamics.md` §1.2.7.

Results.
* `lpf_transfer`: the first-order filter `τ dṽ/dt = v − ṽ` as a linear plant has transfer
  `1/(1 + s τ)`.
* `residual_transfer`: the net uncancelled disturbance `v − ṽ` that enters the IN-positive
  closed loop has the high-pass transfer `s τ/(1 + s τ)`; the "LPF view" `ṽ − v` has
  `−s τ/(1 + s τ)` (`residualLPF_transfer`, the opposite output sign).
* `residual_norm`: on the imaginary axis the residual gain is `|ω| τ/√(1 + ω² τ²)` (`τ > 0`).
* `idealFeedforward_field`: with an unfiltered, exact measurement (`v^ff = v`) the disturbance
  cancels identically — the closed loop does not depend on `v` and equals the PI loop of
  `PILoop.lean`.
* `lpf_det_characteristicMatrix`: the closed loop is block triangular; its characteristic
  polynomial is the PI-loop polynomial times `(s + 1/τ)`, so the spectrum is the PI spectrum
  together with `−1/τ` (`characteristic_root_iff`).
* `lpf_isHurwitz_iff` (static): the state matrix is Hurwitz iff the PI loop's is and `τ > 0`.

Family and connection conclusions.
`lpfFamily : Family LPFLoop Spectral.Requirement 3 2` reads a PI loop with filter time constant
`τ` as the port system of its plant (`Family.IsLinear`, `Spectral.linearFamily`); its
requirements are the PI loop's monic coefficient conditions together with the sign of `τ`.
* `lpfChain_le_semantics`, `lpfExact`: every translation is sound; the attractive sentences and
  sampled contraction are carved out exactly.
* `lpfDen_eq`: adding the low-pass feedforward does not change the stability of the PI loop —
  the attractive denotation of the feedforward family is the pull-back of the PI family's along
  `LPFLoop.pi`, cut by `τ > 0`. Scaffold: `theorem/FeedforwardCurrentLoop.agda`.
* `lpf_mem_den_iff`: with `L > 0`, stable iff `R + Kp > 0 ∧ Ki > 0 ∧ τ > 0`.
* `lpf_tracks_reference` (`i → i*`, `ṽ → v` for constant `i*`, `v`) is a trajectory-level
  result outside the sentence language, kept as private implementation evidence.
Transfer functions, residual gains and the ideal-feedforward identity are static evidence.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter Linear LinearSystems
open scoped Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The filter and its residual -/

/-- Low-pass plant `τ dṽ/dt = v − ṽ`, output `ṽ`. -/
def lpf (τ : ℝ) : Plant 1 1 := ⟨!![-1 / τ], !![1 / τ], !![1], !![0]⟩

/-- Same filter, output the uncancelled disturbance `v − ṽ`. -/
def residual (τ : ℝ) : Plant 1 1 := ⟨!![-1 / τ], !![1 / τ], !![-1], !![1]⟩

private lemma pole_ne {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : 1 + s * τ ≠ 0) : s - ((-1 / τ : ℝ) : ℂ) ≠ 0 := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  intro h
  apply hs
  have : s = -1 / τ := by
    push_cast at h
    linear_combination h
  rw [this]
  field_simp
  ring

@[tmio M, powerlib_foundation] theorem lpf_transfer {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ} (hs : 1 + s * τ ≠ 0) :
    transfer (lpf τ) s 0 0 = 1 / (1 + s * τ) := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  rw [lpf, LTI.transfer_fin_one _ _ _ _ (pole_ne hτ hs)]
  push_cast
  field_simp
  ring

@[powerlib_foundation] theorem residual_transfer {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : 1 + s * τ ≠ 0) :
    transfer (residual τ) s 0 0 = s * τ / (1 + s * τ) := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  rw [residual, LTI.transfer_fin_one _ _ _ _ (pole_ne hτ hs)]
  have hk : s - ((-1 / τ : ℝ) : ℂ) = (1 + s * τ) / τ := by
    push_cast
    field_simp
    ring
  have e1 : ((-1 : ℝ) : ℂ) * ((1 / τ : ℝ) : ℂ) / ((1 + s * τ) / τ) = -1 / (1 + s * τ) := by
    push_cast
    rw [div_div_eq_mul_div, mul_assoc, one_div_mul_cancel hτ', mul_one]
  rw [hk, e1, Complex.ofReal_one, div_add_one hs]
  congr 1
  ring

/-- LPF view `ṽ − v`: `−s τ/(1 + s τ)`. -/
@[powerlib_foundation] theorem residualLPF_transfer {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : 1 + s * τ ≠ 0) :
    transfer (LTI.negOutput (residual τ)) s 0 0 = -(s * τ / (1 + s * τ)) := by
  rw [LTI.transfer_negOutput, Matrix.neg_apply, residual_transfer hτ hs]

/-- High-pass gain on the imaginary axis: `|jωτ/(1 + jωτ)| = |ω| τ/√(1 + ω²τ²)`. -/
@[powerlib_foundation] theorem residual_norm {τ : ℝ} (hτ : 0 < τ) (ω : ℝ) :
    ‖transfer (residual τ) ((ω : ℂ) * Complex.I) 0 0‖ =
      |ω| * τ / Real.sqrt (1 + (ω * τ) ^ 2) := by
  have hs : 1 + (ω : ℂ) * Complex.I * τ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [residual_transfer hτ.ne' hs, norm_div]
  have h1 : ‖(ω : ℂ) * Complex.I * τ‖ = |ω| * τ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hτ, mul_one]
  have h2 : ‖1 + (ω : ℂ) * Complex.I * τ‖ = Real.sqrt (1 + (ω * τ) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [h1, h2]

/-! ## Ideal feedforward cancels the disturbance exactly -/

namespace PIParams

variable (p : PIParams)

/-- IN-positive plant `L di/dt = v − v^conv − R i`, integrator `dξ/dt = i* − i`, with the
converter command `v^conv = −(Kp (i* − i) + Ki ξ) + v^ff`. -/
def ffField (vff v iref : ℝ) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![(v - (-p.control iref x + vff) - p.R * x 0) / p.L, iref - x 0]

/-- With `v^ff = v` the PCC voltage disappears from the closed loop. -/
@[powerlib_foundation] theorem idealFeedforward_field (v iref : ℝ) (x : ℝ²) :
    p.ffField v v iref x = p.field iref x := by
  ext j
  fin_cases j <;> simp [ffField, field]
  ring

/-! ## Low-pass feedforward closed loop -/

/-- Closed loop `(di/dt, dξ/dt, dṽ/dt)` with inputs `i*`, `v`. -/
def lpfField (τ iref v : ℝ) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 ![(v - (-(p.Kp * (iref - x 0) + p.Ki * x 1) + x 2) - p.R * x 0) / p.L,
    iref - x 0, (v - x 2) / τ]

/-- Plant: inputs `(i*, v)`, outputs `(i, ṽ)`. -/
def lpfModel (τ : ℝ) : Plant 3 2 :=
  ⟨!![-(p.R + p.Kp) / p.L, p.Ki / p.L, -1 / p.L; -1, 0, 0; 0, 0, -1 / τ],
    !![p.Kp / p.L, 1 / p.L; 1, 0; 0, 1 / τ], !![1, 0, 0; 0, 0, 1], 0⟩

@[powerlib_foundation] theorem lpfModel_field (τ iref v : ℝ) (x : ℝ³) :
    (p.lpfModel τ).inputField ![iref, v] x = p.lpfField τ iref v x := by
  ext j
  fin_cases j <;>
    simp [Plant.inputField, lpfModel, lpfField, op, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- Block-triangular characteristic polynomial: PI loop times `(s + 1/τ)`. -/
@[powerlib_foundation] theorem lpf_det_characteristicMatrix (τ : ℝ) (s : ℂ) :
    (characteristicMatrix (p.lpfModel τ).A s).det =
      (characteristicMatrix p.model.A s).det * (s + ((1 / τ : ℝ) : ℂ)) := by
  simp only [model, LTI.det_characteristicMatrix_of]
  simp [characteristicMatrix, lpfModel, Matrix.det_fin_three]
  ring

/-- Spectrum: the PI-loop roots together with `−1/τ`. -/
@[powerlib_foundation] theorem characteristic_root_iff (τ : ℝ) (s : ℂ) :
    (characteristicMatrix (p.lpfModel τ).A s).det = 0 ↔
      (characteristicMatrix p.model.A s).det = 0 ∨ s = ((-1 / τ : ℝ) : ℂ) := by
  rw [p.lpf_det_characteristicMatrix, mul_eq_zero]
  apply or_congr_right
  rw [add_eq_zero_iff_eq_neg]
  push_cast
  ring_nf

/-- The low-pass feedforward loop is Hurwitz iff the PI loop is and `τ > 0`. Static evidence on
the model, not a connection conclusion. -/
@[powerlib_foundation] theorem lpf_isHurwitz_iff (τ : ℝ) :
    IsHurwitz (p.lpfModel τ).A ↔ IsHurwitz p.model.A ∧ 0 < τ := by
  simp only [Criteria.isHurwitz_iff_characteristic_roots, p.characteristic_root_iff]
  constructor
  · intro h
    refine ⟨fun s hs => h s (Or.inl hs), ?_⟩
    have := h _ (Or.inr rfl)
    simp only [Complex.ofReal_re] at this
    have h1 : 0 < 1 / τ := by linarith [neg_div τ 1]
    exact one_div_pos.mp h1
  · rintro ⟨h, hτ⟩ s (hs | hs)
    · exact h s hs
    · rw [hs, Complex.ofReal_re, neg_div]
      exact neg_neg_of_pos (one_div_pos.mpr hτ)

/-- A right-half-plane root of the PI loop or a negative time constant gives a right-half-plane
root of the feedforward loop. -/
@[powerlib_foundation] theorem lpf_exists_root_of_unstable {τ : ℝ}
    (h : ((p.R + p.Kp) / p.L < 0 ∨ p.Ki / p.L < 0) ∨ τ < 0) :
    ∃ s : ℂ, (characteristicMatrix (p.lpfModel τ).A s).det = 0 ∧ 0 < s.re := by
  rcases h with h | h
  · obtain ⟨s, hs, hre⟩ := p.exists_root_of_unstable h
    exact ⟨s, (p.characteristic_root_iff τ s).mpr (Or.inl hs), hre⟩
  · refine ⟨((-1 / τ : ℝ) : ℂ), (p.characteristic_root_iff τ _).mpr (Or.inr rfl), ?_⟩
    rw [Complex.ofReal_re, neg_div, neg_pos]
    exact one_div_neg.mpr h

/-- Equilibrium for constant `i*`, `v`: `(i*, R i*/Ki, v)`. -/
def lpfEquilibrium (iref v : ℝ) : ℝ³ := WithLp.toLp 2 ![iref, p.R * iref / p.Ki, v]

@[powerlib_foundation] theorem lpf_isEquilibrium (hKi : p.Ki ≠ 0) (τ iref v : ℝ) :
    IsEquilibrium ((p.lpfModel τ).inputField ![iref, v]) (p.lpfEquilibrium iref v) := by
  rw [IsEquilibrium, lpfModel_field]
  ext j
  fin_cases j <;> simp [lpfField, lpfEquilibrium, mul_div_assoc', mul_div_cancel_left₀ _ hKi]

end PIParams

/-! ## The low-pass feedforward family -/

/-- A PI current loop with low-pass PCC-voltage feedforward of time constant `τ`. -/
@[ext] structure LPFLoop where
  /-- The PI current loop. -/
  pi : PIParams
  /-- The feedforward filter time constant. -/
  τ : ℝ

namespace LPFLoop

/-- The plant of the loop: inputs `(i*, v)`, outputs `(i, ṽ)`. -/
def plant (q : LPFLoop) : Plant 3 2 := q.pi.lpfModel q.τ

/-- Stability condition: the PI loop's positive monic coefficients and `τ > 0`. -/
def Stable (q : LPFLoop) : Prop := q.pi.Stable ∧ 0 < q.τ

/-- Instability condition: a negative PI monic coefficient or `τ < 0`. -/
def Unstable (q : LPFLoop) : Prop := q.pi.Unstable ∨ q.τ < 0

/-- The low-pass feedforward family: every loop read as the port system of its plant. -/
def lpfFamily : Family LPFLoop Spectral.Requirement 3 2 :=
  Spectral.linearFamily plant Stable Unstable

@[powerlib_foundation] theorem lpfFamily_isLinear : lpfFamily.IsLinear plant :=
  Spectral.linearFamily_isLinear _ _ _

@[powerlib_foundation] theorem isHurwitz_iff_stable (q : LPFLoop) :
    IsHurwitz q.plant.A ↔ q.Stable := by
  rw [plant, PIParams.lpf_isHurwitz_iff, PIParams.isHurwitz_iff_div]
  rfl

private theorem den_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (lpfFamily.den (.flow P) = {q | q.Stable}) := show lpfFamily.den (.flow P) = {q | q.Stable} from
  Spectral.linear_den (U := Unstable) (fun q => (isHurwitz_iff_stable q).symm) hP

/-- Every translation of the feedforward family is sound. -/
@[tmio TM, powerlib_domain] theorem lpfChain_le_semantics :
    connection% (∀ P, lpfFamily.chain P ≤ lpfFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics (fun q h => (isHurwitz_iff_stable q).mpr h)
    (fun q h => q.pi.lpf_exists_root_of_unstable h)

/-- The attractive sentences and sampled contraction of the feedforward loop are carved out
exactly by the PI loop's positive monic coefficients and `τ > 0`. -/
@[tmio TM, powerlib_domain] theorem lpfExact {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (lpfFamily.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun q => (isHurwitz_iff_stable q).symm) hP

/-- Adding the low-pass PCC-voltage feedforward preserves the stability of the PI loop exactly:
the attractive denotation of the feedforward family is the PI family's, pulled back along
`LPFLoop.pi`, cut by `τ > 0`. -/
@[tmio TM, powerlib_domain] theorem lpfDen_eq {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (lpfFamily.den (.flow P) =
      LPFLoop.pi ⁻¹' PIParams.family.den (.flow P) ∩ {q | 0 < q.τ}) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP, PIParams.family_isLinear.den_hurwitz hP]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [PIParams.isHurwitz_iff_div]
  rfl

/-- With `L > 0` the feedforward loop is stable iff `R + Kp > 0 ∧ Ki > 0 ∧ τ > 0`. -/
@[tmio TM, powerlib_domain] theorem lpf_mem_den_iff (q : LPFLoop) (hL : 0 < q.pi.L) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (q ∈ lpfFamily.den (.flow P) ↔
      q ∈ {q : LPFLoop | (0 < q.pi.R + q.pi.Kp ∧ 0 < q.pi.Ki) ∧ 0 < q.τ}) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP]
  change (q.pi.Stable ∧ 0 < q.τ) ↔ _
  rw [PIParams.Stable, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]
  rfl

/-- Tracking with low-pass feedforward: `i → i*`, `ṽ → v`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem lpf_tracks_reference (p : PIParams) (hL : 0 < p.L) (hR : 0 < p.R + p.Kp)
    (hKi : 0 < p.Ki) {τ : ℝ} (hτ : 0 < τ) {iref v : ℝ} {x : ℝ → ℝ³}
    (hx : ∀ t, HasDerivAt x (p.lpfField τ iref v (x t)) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 iref) ∧ Tendsto (fun t => x t 2) atTop (𝓝 v) := by
  have hA : IsHurwitz (p.lpfModel τ).A :=
    (p.lpf_isHurwitz_iff τ).2 ⟨(p.isHurwitz_iff hL).2 ⟨hR, hKi⟩, hτ⟩
  have he := p.lpf_isEquilibrium hKi.ne' τ iref v
  have hx' : ∀ t, HasDerivAt x ((p.lpfModel τ).inputField ![iref, v] (x t)) t := by
    intro t
    rw [PIParams.lpfModel_field]
    exact hx t
  exact ⟨by simpa [PIParams.lpfEquilibrium] using LTI.tendsto_equilibrium_apply _ hA he hx' 0,
    by simpa [PIParams.lpfEquilibrium] using LTI.tendsto_equilibrium_apply _ hA he hx' 2⟩

end LPFLoop

end powerlib.CurrentControl
