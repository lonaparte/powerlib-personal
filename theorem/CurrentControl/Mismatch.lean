import theorem.CurrentControl.PILoop
import theorem.Criteria.ComplexQuadratic
import theorem.Stack.Implementation

/-! # Decoupled dq PI current loop with inductance mismatch

Model boundary.
* System: the two-axis (dq) converter current loop through one series R–L filter, in a frame
  rotating at the constant speed `ω` (PLL locked, `ω̂ = ω`: case A of T-decoupling-control
  §1.4), closed by per-axis PI control plus ideal PCC-voltage feedforward plus cross-decoupling
  computed with the controller's inductance estimate `L̂`. Continuous time, linear.
* State order `(i_d, i_q, ξ_d, ξ_q) ∈ EuclideanSpace ℝ (Fin 4)`; currents IN-positive
  (`conventions.md` §D1); `ξ_k = ∫ (i_k* − i_k) dt`.
* Plant (T-decoupling-control §1.2, true inductance `L > 0`):
  `L di_d/dt = v_d − v^conv_d − R i_d + ω L i_q`, `L di_q/dt = v_q − v^conv_q − R i_q − ω L i_d`.
* Controller: `v^conv = v^PI + v^ff + v^dec` with `v^PI_k = −(Kp (i_k* − i_k) + Ki ξ_k)`,
  ideal feedforward `v^ff = v` (no low-pass), decoupling `v^dec_d = +ω L̂ i_q`,
  `v^dec_q = −ω L̂ i_d` (§1.3). `ΔL = L − L̂` is a constant; `ω`, `ΔL` have any sign.
* Inputs: references `(i_d*, i_q*)` and the PCC voltage `v` (which cancels exactly); the plant
  of the closed loop has the references as its two ports and the currents as outputs.
* Excluded: PLL dynamics and `ω̂ ≠ ω`, feedforward low-pass, delay, PWM, limits, DC link.

Source: work-sync `theory/T-decoupling-control.md` §1.2–§1.4, §2.2;
`theory/T-gfl-control.md` §1.4.3–§1.4.4.

Results.
* `model_field`: the closed loop is `L i' = Kp (i* − i) + Ki ξ − R i − j ω ΔL i` in complex
  notation, i.e. the residual `±ω ΔL i` of §1.4; its characteristic polynomial factors as
  `p(s) p̄(s)` with `p(s) = L s² + (R + Kp + j ω ΔL) s + Ki` (`det_characteristicMatrix`).
* `isHurwitz_iff` (static): exact Hurwitz condition `R + Kp > 0 ∧ Ki > 0`, for every `ω` and
  every mismatch `ΔL` (via `complexQuadratic_realConst_roots_re_neg_iff`: an imaginary
  perturbation of the `s` coefficient alone never moves a root across the imaginary axis).
* `equilibrium_current` (static): every equilibrium has `i = i*` (the integrators absorb the
  mismatch bias).

Family and connection conclusions.
`family : Family MismatchParams Spectral.Requirement 4 2` reads a decoupled loop as the port
system of its closed-loop plant (`Family.IsLinear`, `Spectral.linearFamily`); requirements: the
monic coefficients `(R + Kp)/L`, `Ki/L` positive (`stable`) or `(R + Kp)/L` negative
(`unstable`, a root of `s² + ((R + Kp)/L ± j ω ΔL/L) s + Ki/L` in the open right half plane).
* `chain_le_semantics`, `exact`: every translation sound, the attractive sentences and sampled
  contraction carved out exactly.
* `den_eq_base` (connection comparison): the attractive denotation of the mismatched family is
  the PI family's pulled back along `base` — the mismatch never changes the stability region.
* `mem_den_iff`: with `L > 0`, stable iff
  `R + Kp > 0 ∧ Ki > 0`.
* Implementation layer (`theorem/Stack/Implementation.lean`, `Layers.md`): the decoupling estimate
  `L̂` is a parameter tolerance of the controller, so the mismatched dq loop is an implementation
  of the single-axis PI design `PIParams.family` (perfect decoupling), realizing its base loop
  (`MismatchParams.implementation`). `realizationExactUnder`: the attractive sentences and sampled
  contraction are realized exactly, without constraints (from `den_eq_base`). Scaffold:
  `theorem/DecouplingMismatch.agda`.
* `tracks_reference` (`i → i*` for constant references) is a trajectory-level result outside the
  sentence language, kept as private implementation evidence.

Correction (T-decoupling-control §2.2 "ΔL ≠ 0 时 PI 仍能驱动稳态 i = i*"): zero steady-state
error needs closed-loop stability, which the note does not state. Here it is the exact premise
`R + Kp > 0 ∧ Ki > 0`; without it the claim fails (`PIParams.mem_den_unstable_of_Ki_neg`, the
`ΔL = 0` instance). The note's mismatch does not alter the stability region at all.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter Linear LinearSystems
open scoped Topology

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- Decoupled dq loop: PI gains and plant (`base`), frame speed `ω`, controller estimate `L̂`. -/
@[ext] structure MismatchParams where
  base : PIParams
  ω : ℝ
  Lhat : ℝ

namespace MismatchParams

variable (p : MismatchParams)

/-- Inductance mismatch `ΔL = L − L̂`. -/
def ΔL : ℝ := p.base.L - p.Lhat

/-- Converter voltage command `v^PI + v^ff + v^dec` (ideal feedforward `v^ff = v`). -/
def converterVoltage (v iref : Fin 2 → ℝ) (x : ℝ⁴) : Fin 2 → ℝ :=
  ![-(p.base.Kp * (iref 0 - x 0) + p.base.Ki * x 2) + v 0 + p.ω * p.Lhat * x 1,
    -(p.base.Kp * (iref 1 - x 1) + p.base.Ki * x 3) + v 1 - p.ω * p.Lhat * x 0]

/-- dq-frame R–L plant, IN-positive, true inductance `L`. -/
def plantDeriv (v vconv : Fin 2 → ℝ) (x : ℝ⁴) : Fin 2 → ℝ :=
  ![(v 0 - vconv 0 - p.base.R * x 0 + p.ω * p.base.L * x 1) / p.base.L,
    (v 1 - vconv 1 - p.base.R * x 1 - p.ω * p.base.L * x 0) / p.base.L]

/-- Physical closed-loop field `(di_d, di_q, dξ_d, dξ_q)/dt`. -/
def field (v iref : Fin 2 → ℝ) (x : ℝ⁴) : ℝ⁴ :=
  WithLp.toLp 2 ![p.plantDeriv v (p.converterVoltage v iref x) x 0,
    p.plantDeriv v (p.converterVoltage v iref x) x 1, iref 0 - x 0, iref 1 - x 1]

/-- State matrix, with `a = (R + Kp)/L`, `b = ω ΔL / L`, `c = Ki / L`. -/
def stateMatrix (a b c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-a, b, c, 0; -b, -a, 0, c; -1, 0, 0, 0; 0, -1, 0, 0]

/-- The closed loop as a linear plant: inputs `i*`, outputs `i`. -/
def model : Plant 4 2 :=
  ⟨stateMatrix ((p.base.R + p.base.Kp) / p.base.L) (p.ω * p.ΔL / p.base.L)
      (p.base.Ki / p.base.L),
    !![p.base.Kp / p.base.L, 0; 0, p.base.Kp / p.base.L; 1, 0; 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0], 0⟩

/-- The plant is the physical loop for every PCC voltage `v` (exact cancellation). -/
@[tmio M, powerlib_foundation] theorem model_field (hL : p.base.L ≠ 0) (v iref : Fin 2 → ℝ)
    (x : ℝ⁴) : p.model.inputField iref x = p.field v iref x := by
  ext j
  fin_cases j <;>
    simp [Plant.inputField, op, model, stateMatrix, field, plantDeriv, converterVoltage, ΔL,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Mismatch residual in the L-equation (case A): `ω L i_q − ω L̂ i_q = ω ΔL i_q`. -/
@[powerlib_foundation] theorem residual_d (iq : ℝ) :
    p.ω * p.base.L * iq - p.ω * p.Lhat * iq = p.ω * p.ΔL * iq := by
  simp only [ΔL]
  ring

private lemma eig_equations {a b c : ℝ} {μ : ℂ} {v : Fin 4 → ℂ}
    (h : (stateMatrix a b c).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    -(a : ℂ) * v 0 + b * v 1 + c * v 2 = μ * v 0 ∧
      -(b : ℂ) * v 0 - a * v 1 + c * v 3 = μ * v 1 ∧ -v 0 = μ * v 2 ∧ -v 1 = μ * v 3 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [stateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h2 h3
  exact ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2,
    by linear_combination h3⟩

/-- Every eigenvalue is a root of `s² + (a ± j b) s + c`. -/
@[powerlib_foundation] theorem eigenvalue_root {a b c : ℝ} {μ : ℂ} {v : Fin 4 → ℂ}
    (hv : v ≠ 0) (h : (stateMatrix a b c).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ ^ 2 + (⟨a, b⟩ : ℂ) * μ + (c : ℂ) = 0 ∨ μ ^ 2 + (⟨a, -b⟩ : ℂ) * μ + (c : ℂ) = 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := eig_equations h
  have hab : (⟨a, b⟩ : ℂ) = a + b * Complex.I := by apply Complex.ext <;> simp
  have hab' : (⟨a, -b⟩ : ℂ) = a - b * Complex.I := by apply Complex.ext <;> simp
  rw [hab, hab']
  set Wp := v 2 + Complex.I * v 3
  set Wm := v 2 - Complex.I * v 3
  have hp : (μ ^ 2 + (a + b * Complex.I) * μ + c) * Wp = 0 := by
    simp only [Wp]
    linear_combination e0 + Complex.I * e1 - (a + b * Complex.I + μ) * (e2 + Complex.I * e3) +
      (-b * v 1) * Complex.I_sq
  have hm : (μ ^ 2 + (a - b * Complex.I) * μ + c) * Wm = 0 := by
    simp only [Wm]
    linear_combination e0 - Complex.I * e1 - (a - b * Complex.I + μ) * (e2 - Complex.I * e3) +
      (-b * v 1) * Complex.I_sq
  by_cases hWp : Wp = 0
  · by_cases hWm : Wm = 0
    · exfalso
      apply hv
      have hv2 : v 2 = 0 := by linear_combination (hWp + hWm) / 2
      have hv3 : v 3 = 0 := by
        have : Complex.I * v 3 = 0 := by linear_combination (hWp - hWm) / 2
        simpa [Complex.I_ne_zero] using this
      have hv0 : v 0 = 0 := by linear_combination -e2 - μ * hv2
      have hv1 : v 1 = 0 := by linear_combination -e3 - μ * hv3
      ext k
      fin_cases k <;> simp [hv0, hv1, hv2, hv3]
    · exact Or.inr ((mul_eq_zero.mp hm).resolve_right hWm)
  · exact Or.inl ((mul_eq_zero.mp hp).resolve_right hWp)

/-- A root of `s² + (a + j b) s + c` is an eigenvalue, with eigenvector `(s, −j s, −1, j)`. -/
@[powerlib_foundation] theorem eigenpair_of_root {a b c : ℝ} {s : ℂ}
    (hs : s ^ 2 + (⟨a, b⟩ : ℂ) * s + (c : ℂ) = 0) :
    (stateMatrix a b c).map (algebraMap ℝ ℂ) *ᵥ ![s, -Complex.I * s, -1, Complex.I] =
      s • ![s, -Complex.I * s, -1, Complex.I] := by
  have hab : (⟨a, b⟩ : ℂ) = a + b * Complex.I := by apply Complex.ext <;> simp
  rw [hab] at hs
  ext k
  fin_cases k <;> simp [stateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · linear_combination -hs
  · linear_combination Complex.I * hs + (-b * s) * Complex.I_sq
  · ring

private lemma eigenvector_ne_zero (s : ℂ) :
    (![s, -Complex.I * s, -1, Complex.I] : Fin 4 → ℂ) ≠ 0 := by
  intro h0
  have := congrFun h0 2
  simp at this

/-- Exact Hurwitz region of the mismatched loop matrix. -/
@[powerlib_foundation] theorem stateMatrix_isHurwitz_iff (a b c : ℝ) :
    IsHurwitz (stateMatrix a b c) ↔ 0 < a ∧ 0 < c := by
  constructor
  · intro h
    rw [← Criteria.complexQuadratic_realConst_roots_re_neg_iff a b c]
    intro s hs
    simpa using h s _ (eigenvector_ne_zero s) (eigenpair_of_root hs)
  · rintro ⟨ha, hc⟩ μ v hv heig
    have hp := (Criteria.complexQuadratic_realConst_roots_re_neg_iff a b c).2 ⟨ha, hc⟩
    have hm := (Criteria.complexQuadratic_realConst_roots_re_neg_iff a (-b) c).2 ⟨ha, hc⟩
    have : μ.re < 0 := by
      rcases eigenvalue_root hv heig with h | h
      · exact hp μ h
      · exact hm μ h
    simpa using this

/-- A negative damping coefficient `a < 0` gives a characteristic root in the open right half
plane: the two roots of `s² + (a + j b) s + c` sum to `−a − j b`. -/
@[powerlib_foundation] theorem stateMatrix_exists_root_of_neg {a b c : ℝ} (ha : a < 0) :
    ∃ s : ℂ, (characteristicMatrix (stateMatrix a b c) s).det = 0 ∧ 0 < s.re := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self (discrim (1 : ℂ) (⟨a, b⟩ : ℂ) (c : ℂ))
  obtain ⟨s, hs⟩ := exists_quadratic_eq_zero (one_ne_zero) ⟨d, hd⟩
  have hs' : s ^ 2 + (⟨a, b⟩ : ℂ) * s + (c : ℂ) = 0 := by linear_combination hs
  obtain ⟨-, -, hs₂⟩ := Criteria.quadratic_partner hs'
  have hsum : s.re + (-(⟨a, b⟩ : ℂ) - s).re = -a := by simp
  by_cases hpos : 0 < s.re
  · exact ⟨s, Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _ (eigenvector_ne_zero s)
      (eigenpair_of_root hs'), hpos⟩
  · refine ⟨-(⟨a, b⟩ : ℂ) - s, Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _
      (eigenvector_ne_zero _) (eigenpair_of_root hs₂), ?_⟩
    linarith

private lemma characteristicMatrix_stateMatrix (a b c : ℝ) (s : ℂ) :
    characteristicMatrix (stateMatrix a b c) s =
      !![s + a, -b, -c, 0; b, s + a, 0, -c; 1, 0, s, 0; 0, 1, 0, s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [characteristicMatrix, stateMatrix]

private lemma det_four (a b c s : ℂ) :
    (!![s + a, -b, -c, 0; b, s + a, 0, -c; 1, 0, s, 0; 0, 1, 0, s] :
      Matrix (Fin 4) (Fin 4) ℂ).det =
      (s ^ 2 + (a + b * Complex.I) * s + c) * (s ^ 2 + (a - b * Complex.I) * s + c) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  have h1 : (Fin.succAbove (2 : Fin 4) 2) = 3 := by decide
  have h2 : (Fin.succAbove (1 : Fin 4) 2) = 3 := by decide
  simp only [h1, h2]
  simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Characteristic determinant: the product of the two complex-conjugate quadratics. -/
@[powerlib_foundation] theorem det_characteristicMatrix_stateMatrix (a b c : ℝ) (s : ℂ) :
    (characteristicMatrix (stateMatrix a b c) s).det =
      (s ^ 2 + (a + b * Complex.I) * s + c) * (s ^ 2 + (a - b * Complex.I) * s + c) := by
  rw [characteristicMatrix_stateMatrix, det_four]

/-- Characteristic polynomial: `det(sI − A) = p(s) p̄(s) / L²` with
`p(s) = L s² + (R + Kp + j ω ΔL) s + Ki`. -/
@[powerlib_foundation] theorem det_characteristicMatrix (hL : p.base.L ≠ 0) (s : ℂ) :
    (characteristicMatrix p.model.A s).det =
      ((p.base.L : ℂ) * s ^ 2 + (p.base.R + p.base.Kp + p.ω * p.ΔL * Complex.I) * s +
          p.base.Ki) *
        ((p.base.L : ℂ) * s ^ 2 + (p.base.R + p.base.Kp - p.ω * p.ΔL * Complex.I) * s +
          p.base.Ki) / (p.base.L : ℂ) ^ 2 := by
  have hL' : (p.base.L : ℂ) ≠ 0 := by exact_mod_cast hL
  change (characteristicMatrix (stateMatrix _ _ _) s).det = _
  rw [det_characteristicMatrix_stateMatrix]
  push_cast
  field_simp

/-- The equilibrium for constant references: `i = i*`, and the integrators carry the
mismatch bias: `Ki ξ_d = R i_d* − ω ΔL i_q*`, `Ki ξ_q = R i_q* + ω ΔL i_d*`. -/
def equilibrium (iref : Fin 2 → ℝ) : ℝ⁴ :=
  WithLp.toLp 2 ![iref 0, iref 1, (p.base.R * iref 0 - p.ω * p.ΔL * iref 1) / p.base.Ki,
    (p.base.R * iref 1 + p.ω * p.ΔL * iref 0) / p.base.Ki]

@[powerlib_foundation] theorem isEquilibrium (hL : p.base.L ≠ 0) (hKi : p.base.Ki ≠ 0)
    (iref : Fin 2 → ℝ) : IsEquilibrium (p.model.inputField iref) (p.equilibrium iref) := by
  ext j
  fin_cases j <;>
    simp [Plant.inputField, op, model, stateMatrix, equilibrium, dotProduct, Fin.sum_univ_two]
  · field_simp
    ring
  · field_simp
    ring

/-- Every equilibrium has zero current error `i = i*`, whatever the mismatch. Static evidence on
the model, not a connection conclusion. -/
@[powerlib_foundation] theorem equilibrium_current {iref : Fin 2 → ℝ} {e : ℝ⁴}
    (he : IsEquilibrium (p.model.inputField iref) e) : e 0 = iref 0 ∧ e 1 = iref 1 := by
  have h2 := congrArg (fun z : ℝ⁴ => z 2) he
  have h3 := congrArg (fun z : ℝ⁴ => z 3) he
  simp [Plant.inputField, op, model, stateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Fin.sum_univ_two] at h2 h3
  constructor <;> linarith

/-! ## The family -/

/-- Stability condition: positive monic coefficients `(R + Kp)/L` and `Ki/L`. -/
def Stable : Prop := 0 < (p.base.R + p.base.Kp) / p.base.L ∧ 0 < p.base.Ki / p.base.L

/-- Instability condition: negative damping coefficient `(R + Kp)/L`. -/
def Unstable : Prop := (p.base.R + p.base.Kp) / p.base.L < 0

/-- The mismatched decoupled-loop family: every loop read as the port system of its closed-loop
plant. -/
def family : Family MismatchParams Spectral.Requirement 4 2 :=
  Spectral.linearFamily model Stable Unstable

@[powerlib_foundation] theorem family_isLinear : family.IsLinear model :=
  Spectral.linearFamily_isLinear _ _ _

/-- The mismatched loop is Hurwitz iff `R + Kp > 0 ∧ Ki > 0`, for every `ω` and `ΔL`. Read through the family denotation. -/
@[tmio TM, powerlib_foundation] theorem isHurwitz_iff (hL : 0 < p.base.L) :
    connection% (p ∈ family.den (.flow .globallyExponentiallyStable) ↔ 0 < p.base.R + p.base.Kp ∧ 0 < p.base.Ki) := by
  unfold TMIO.Statement
  rw [(connection_proof% (family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)))]
  change IsHurwitz (stateMatrix _ _ _) ↔ _
  rw [stateMatrix_isHurwitz_iff, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]

@[tmio TM, powerlib_foundation] theorem isHurwitz_iff_stable :
    connection% (p ∈ family.den (.flow .globallyExponentiallyStable) ↔ p.Stable) := by
  unfold TMIO.Statement
  rw [(connection_proof% (family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)))]
  change IsHurwitz (stateMatrix _ _ _) ↔ _
  rw [stateMatrix_isHurwitz_iff]
  rfl

@[tmio TM] private theorem den_flow {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.den (.flow P) = {p | p.Stable}) := show family.den (.flow P) = {p | p.Stable} from
  Spectral.linear_den (U := Unstable) (fun p => (((family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (isHurwitz_iff_stable p))).symm) hP

/-- Every translation of the mismatched family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics (fun p h => (((family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (isHurwitz_iff_stable p))).mpr h)
    (fun _ h => stateMatrix_exists_root_of_neg h)

/-- The attractive sentences and sampled contraction of the mismatched loop are carved out
exactly by positive monic coefficients. -/
@[tmio TM, powerlib_domain] theorem exact {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun p => (((family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (isHurwitz_iff_stable p))).symm) hP

/-- The inductance mismatch never changes the stability region: the attractive denotation of the
mismatched family is the PI family's, pulled back along `base`. -/
@[tmio MI, powerlib_domain] theorem den_eq_base {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.den (.flow P) = base ⁻¹' PIParams.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP, PIParams.family_isLinear.den_hurwitz hP]
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [← (connection_proof% PIParams.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)),
    (connection_proof% PIParams.isHurwitz_iff_div)]
  rfl

/-- With `L > 0` the mismatched decoupled loop satisfies an attractive sentence iff
`R + Kp > 0 ∧ Ki > 0`, for every `ω` and every mismatch. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff (hL : 0 < p.base.L) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (p ∈ family.den (.flow P) ↔
      p ∈ {p : MismatchParams | 0 < p.base.R + p.base.Kp ∧ 0 < p.base.Ki}) := by
  unfold powerlib.TMIO.Statement
  rw [den_flow hP]
  change p.Stable ↔ _
  rw [Stable, div_pos_iff_of_pos_right hL, div_pos_iff_of_pos_right hL]
  rfl

/-- Reference tracking of the mismatched loop: both currents converge to their references.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem tracks_reference (hL : 0 < p.base.L)
    (hR : 0 < p.base.R + p.base.Kp) (hKi : 0 < p.base.Ki) (v iref : Fin 2 → ℝ)
    {x : ℝ → ℝ⁴} (hx : ∀ t, HasDerivAt x (p.field v iref (x t)) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 (iref 0)) ∧
      Tendsto (fun t => x t 1) atTop (𝓝 (iref 1)) := by
  have hA := (((family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (p.isHurwitz_iff hL))).2 ⟨hR, hKi⟩
  have he := p.isEquilibrium hL.ne' hKi.ne' iref
  have hx' : ∀ t, HasDerivAt x (p.model.inputField iref (x t)) t := by
    intro t
    rw [p.model_field hL.ne' v]
    exact hx t
  exact ⟨by simpa [equilibrium] using LTI.tendsto_equilibrium_apply p.model hA he hx' 0,
    by simpa [equilibrium] using LTI.tendsto_equilibrium_apply p.model hA he hx' 1⟩

/-! ### The mismatched loop as an implementation of the PI design -/

/-- The dq loop with decoupling computed from the estimate `L̂` as an implementation of the
single-axis PI design `PIParams.family` (perfect decoupling): the estimate is a parameter
tolerance of the controller, and each mismatched loop realizes its base PI loop. -/
def implementation :
    Implementation PIParams Spectral.Requirement MismatchParams Spectral.Requirement 2 1 4 2 :=
  { model := PIParams.family, impl := family, realizes := Implementation.ofDesign base }

/-- The attractive sentences and sampled contraction are realized exactly, without constraints:
a mismatched loop satisfies them exactly when its base PI loop does (`den_eq_base`). -/
@[tmio MI, powerlib_domain] theorem realizationExactUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (implementation.RealizationExactUnder ∅ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have h := den_eq_base hP
  unfold powerlib.TMIO.Statement at h
  exact Implementation.realizationExactUnder_of_den_eq_preimage rfl h

end MismatchParams

end powerlib.CurrentControl
