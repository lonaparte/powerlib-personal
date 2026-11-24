import theorem.GridTiedConverter.GFM.FullModel.DCSaddle
import theorem.Dynamics.Transport
import theorem.Dynamics.ConverseLinearization
import theorem.Criteria.Routh3

/-! # The full-order grid-forming converter under time-scale separation: stability transfer

Model boundary.
The 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` and its 16-state DC
variant of `theorem/GridTiedConverter/GFM/FullModel/DC.lean` (state order, frames, directions:
currents out of the converter positive, export-positive per-unit power). Continuous time,
autonomous, no input. The small parameter `ε > 0` enters in two exactly equivalent ways.
* The `ε`-system `Params.scaledField ε`: the ten fast rows (filter current, capacitor voltage,
  line current, both PI integrators) multiplied by `ε⁻¹`, the slow rows unchanged
  (`SingularPerturbation.splitScaledField`).
* The time-scaled parameter set `Params.timeScaled ε`: `ω₀ ↦ ω₀/ε`, `L_f, C_f, L_g ↦ εL_f, εC_f,
  εL_g` (so the nominal-frequency impedances `Z_f, Z_g`, the susceptance `ω₀C_f` and the reduced
  model are unchanged, while every electromagnetic time constant is multiplied by `ε`: the
  classical small parameter `1/ω₀` of the quasi-static network at fixed reactances), and the PI
  integral gains `K_ic, K_iv ↦ K_ic/ε, K_iv/ε`; all other gains, the VSM, the droop and the
  filter `ω_q` unchanged. Its field is the `ε`-system in the coordinates
  `(ξ, ζ) ↦ (εξ, εζ)` (`Params.timeScaled_field`).
The stability statements are local (equilibrium level) and hold for every `ε ∈ (0, ε*)` with an
`ε*` that is not computed; nothing is claimed about the basin, its uniformity in `ε` or
trajectory approximation. Fixed parameters (`ε = 1`) are not covered: see
`theorem/GridTiedConverter/GFM/FullModel/Counterexample.lean`.

Scaffold of the reading of the reduced Q–V droop model:
`theorem/GridTiedConverter/GFM/FullModel/FullModelTimeScale.agda`.

Source: GFM counterpart study, full-order model note (t5: "UNPROVED: stability of δ+ in full
model; Tikhonov error; DC stability") and equilibria note (t6 §c); Kokotović–Khalil–O'Reilly,
*Singular Perturbation Methods in Control* (1986), Ch. 2 (two-time-scale stability); Sauer–Pai,
*Power System Dynamics and Stability* (1998), §6 (network transients as the fast subsystem,
`ε ∝ 1/ω₀`).

Results.
* The `ε`-system (`Params.scaledField`): at a quasi-steady equilibrium whose fast block
  `Params.fastBlock δ*` is spectrally stable (the boundary layer) and whose reduced Jacobian
  `Params.reducedJacobian δ* Q*` is Hurwitz, there is `ε* > 0` such that the `ε`-system is
  locally exponentially stable at the equilibrium for every `ε ∈ (0, ε*)` (the generic law
  `SingularPerturbation.exists_epsStar_locallyExponentiallyStable_of_graph`, applied to the
  quasi-steady graph `Params.graph` with `Params.graph_slow`, `Params.fast_graph`,
  `Params.slowRows_graph`).
* `Params.timeScaled_field`, `Params.timeScaled_qssState`: the time-scaled model is the
  `ε`-system in the coordinates `(εξ, εζ)` (`Params.integratorCoord`, `Params.scaledField_apply`),
  so the same stability holds for the time-scaled parameters (`Dynamics.holds_transport_iff`).
* `Params.isHurwitz_reducedJacobian_of_swing` (`n_q = 0`, `Z_v = 0`): the reduced Jacobian is
  Hurwitz at a balanced angle with positive synchronizing coefficient of `Params.swingParams`
  and `M, D, ω_q > 0`.
* DC variant: `DCParams.scaledField`, `DCParams.timeScaled`, `DCParams.timeScaled_field`; the same
  transfer with the six-state reduced Jacobian `DCParams.reducedJacobian δ* Q* v_ref` (the field
  being `C¹` only on `v_dc ≠ 0`).
* The saddle branch needs no time-scale separation: `FullModel.mem_den_unstable` holds for every
  parameter set.

Family and connection conclusions.
* `exists_epsStar_mem_den_LES` (connection, family `FullModel.family`): at a balanced quasi-steady
  point with a spectrally stable fast block and a Hurwitz reduced Jacobian, the time-scaled full
  model is in the denotation of local exponential stability for every `ε ∈ (0, ε*)`;
  `exists_epsStar_mem_den_LES_of_qvDroop` (connection, reading `QVDroop.family`): without virtual
  impedance, a reduced Q–V droop model that is locally exponentially stable at the selected point,
  with a spectrally stable boundary layer, transfers its stability to the time-scaled full model,
  for every small `ε`; `exists_epsStar_mem_den_LES_of_swing` (no droop, no virtual impedance): the
  same from a positive synchronizing coefficient of the swing reading.
* `dcFamily_exists_epsStar_mem_den_LES` (connection, family `FullModel.dcFamily`): the DC variant.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex ComplexConjugate Matrix
open powerlib.Dynamics (State)

@[tmio M, powerlib_domain] theorem split_symm_inr (k : Fin 3) :
    split.symm (.inr k) = ⟨10 + k.val, by omega⟩ := by
  fin_cases k <;> rfl

namespace Params

variable (p : Params)

/-! ### The `ε`-system and the generic two-time-scale law -/

/-- The `ε`-system of the 13-state model: the ten fast rows multiplied by `ε⁻¹`. -/
def scaledField (ε : ℝ) : State 13 → State 13 :=
  SingularPerturbation.splitScaledField split ε p.field

@[tmio M, powerlib_domain] theorem graph_slow (s : State 3) (k : Fin 3) :
    p.graph s (split.symm (.inr k)) = s k := by
  fin_cases k <;> rfl

@[tmio M, powerlib_domain] theorem fast_graph (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0)
    (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0) (s : State 3) (i : Fin 5 × Fin 2) :
    p.field (p.graph s) (split.symm (.inl i)) = 0 := by
  have hfast := (p.fastAtRest_iff hLf hCf hLg hKic hKiv hZt (p.graph s)).mpr rfl
  obtain ⟨a, c⟩ := i
  exact hfast _ (by rw [split_symm_inl]; simp only; omega)

@[tmio M, powerlib_domain] theorem slowRows_graph :
    (fun s => (WithLp.toLp 2 fun k => p.field (p.graph s) (split.symm (.inr k)) : State 3)) =
      p.reducedField := by
  funext s
  ext k
  fin_cases k <;> rfl

@[tmio M, powerlib_domain] private theorem qssState_eq_graph (δ ω Qf : ℝ) :
    p.qssState δ ω Qf = p.graph (Dynamics.mk3 δ ω Qf) := by
  simp [graph]

/-- **Stability transfer under time-scale separation.** At a quasi-steady equilibrium
`qssState δ* 0 Q*` (`P(δ*, E*) = P_ref`, `Q(δ*, E*) = Q*`) with a spectrally stable fast block
(boundary layer) and a Hurwitz reduced Jacobian, there is `ε* > 0` such that for every
`ε ∈ (0, ε*)` the `ε`-system is locally exponentially stable at the equilibrium. -/
@[tmio TM, powerlib_domain] private theorem exists_epsStar_locallyExponentiallyStable
    (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0)
    (hZt : p.Zt ≠ 0) (hM : p.M ≠ 0) (hωq : p.ωq ≠ 0) {δ Qf : ℝ} (hP : p.Pq δ (p.emf Qf) = p.Pref)
    (hQ : p.Qq δ (p.emf Qf) = Qf) (hA : Linear.SpectrallyStable (p.fastBlock δ))
    (hR : LinearSystems.IsHurwitz (p.reducedJacobian δ Qf)) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      LocallyExponentiallyStable (p.scaledField ε) (p.qssState δ 0 Qf) := by
  have heq : p.field (p.qssState δ 0 Qf) = 0 :=
    (p.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq _).mpr ⟨δ, Qf, rfl, hP, hQ⟩
  rw [p.qssState_eq_graph] at heq ⊢
  have hRed := p.hasFDerivAt_reducedField hZt (Dynamics.mk3 δ 0 Qf)
  rw [← p.slowRows_graph] at hRed
  simp only [Dynamics.mk3_zero, Dynamics.mk3_two] at hRed
  refine SingularPerturbation.exists_epsStar_locallyExponentiallyStable_of_graph
    (A := p.fastBlock δ) split isOpen_univ (Set.mem_univ _) p.contDiff_field.contDiffOn heq
    (p.contDiff_graph.differentiable (by norm_num) _) p.graph_slow
    (p.fast_graph hLf hCf hLg hKic hKiv hZt) (fun i j => ?_) hRed hA
    ((Linear.spectrallyStable_iff_isHurwitz _).mpr hR)
  simpa [graph] using p.hasDerivAt_fast (p.graph (Dynamics.mk3 δ 0 Qf)) i j

/-! ### The time-scaled parameters -/

/-- The time-scaled parameters: `ω₀/ε`, `εL_f`, `εC_f`, `εL_g` (fixed nominal-frequency
impedances, electromagnetic time constants times `ε`) and integral gains `K_ic/ε`, `K_iv/ε`. -/
def timeScaled (ε : ℝ) : Params :=
  { p with
    ω0 := p.ω0 / ε, Lf := ε * p.Lf, Cf := ε * p.Cf, Lg := ε * p.Lg, Kic := p.Kic / ε,
    Kiv := p.Kiv / ε }

/-- The diagonal coordinate change `(ξ, ζ) ↦ (εξ, εζ)` (coordinates `6 … 9`). -/
def integratorScale (ε : ℝ) : Matrix (Fin 13) (Fin 13) ℝ :=
  Matrix.diagonal fun i => if 6 ≤ i.val ∧ i.val < 10 then ε else 1

@[tmio M, powerlib_domain] theorem integratorScale_isUnit {ε : ℝ} (hε : ε ≠ 0) :
    IsUnit (integratorScale ε) := by
  rw [Matrix.isUnit_iff_isUnit_det, integratorScale, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
  split_ifs <;> simp [hε]

/-- The integrator rescaling as a coordinate change. -/
def integratorCoord {ε : ℝ} (hε : ε ≠ 0) : State 13 ≃L[ℝ] State 13 :=
  Dynamics.matrixCoord (integratorScale ε) (integratorScale_isUnit hε)

@[tmio M, powerlib_domain] theorem integratorCoord_apply {ε : ℝ} (hε : ε ≠ 0) (x : State 13)
    (i : Fin 13) : integratorCoord hε x i = (if 6 ≤ i.val ∧ i.val < 10 then ε else 1) * x i := by
  simp [integratorCoord, integratorScale, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

@[tmio M, powerlib_domain] theorem scaledField_apply (ε : ℝ) (x : State 13) (i : Fin 13) :
    p.scaledField ε x i = (if i.val < 10 then ε⁻¹ else 1) * p.field x i := by
  simp only [scaledField, SingularPerturbation.splitScaledField,
    SingularPerturbation.splitScale, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  fin_cases i <;> rfl

@[tmio M, powerlib_domain] private theorem phasors_integratorCoord {ε : ℝ} (hε : ε ≠ 0)
    (x : State 13) :
    convCurrent (integratorCoord hε x) = convCurrent x ∧
      capVoltage (integratorCoord hε x) = capVoltage x ∧
      lineCurrent (integratorCoord hε x) = lineCurrent x ∧
      currentInt (integratorCoord hε x) = ε * currentInt x ∧
      voltageInt (integratorCoord hε x) = ε * voltageInt x ∧
      integratorCoord hε x 10 = x 10 ∧ integratorCoord hε x 11 = x 11 ∧
      integratorCoord hε x 12 = x 12 := by
  simp only [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor,
    integratorCoord_apply]
  norm_num
  refine ⟨?_, ?_⟩ <;> ring

@[tmio M, powerlib_domain] private theorem timeScaled_imp {ε : ℝ} (hε : ε ≠ 0) :
    (p.timeScaled ε).Zf = p.Zf ∧ (p.timeScaled ε).Zg = p.Zg ∧ (p.timeScaled ε).Bf = p.Bf ∧
      (p.timeScaled ε).ω0 * (p.timeScaled ε).Lf = p.ω0 * p.Lf := by
  have h1 : p.ω0 / ε * (ε * p.Lf) = p.ω0 * p.Lf := by field_simp
  have h2 : p.ω0 / ε * (ε * p.Lg) = p.ω0 * p.Lg := by field_simp
  have h3 : p.ω0 / ε * (ε * p.Cf) = p.ω0 * p.Cf := by field_simp
  refine ⟨?_, ?_, h3, h1⟩
  · rw [Zf_eq, Zf_eq]
    show (p.Rf : ℂ) + ((p.ω0 / ε : ℝ) : ℂ) * ((ε * p.Lf : ℝ) : ℂ) * I = _
    rw [← Complex.ofReal_mul, h1, Complex.ofReal_mul]
  · rw [Zg_eq, Zg_eq]
    show (p.Rg : ℂ) + ((p.ω0 / ε : ℝ) : ℂ) * ((ε * p.Lg : ℝ) : ℂ) * I = _
    rw [← Complex.ofReal_mul, h2, Complex.ofReal_mul]

@[tmio M, powerlib_domain] private theorem timeScaled_iRef {ε : ℝ} (hε : ε ≠ 0) (x : State 13) :
    (p.timeScaled ε).iRef (integratorCoord hε x) = p.iRef x := by
  obtain ⟨hi, hv, hg, hξ, hζ, h10, h11, h12⟩ := phasors_integratorCoord hε x
  obtain ⟨hZf, hZg, hBf, hωL⟩ := p.timeScaled_imp hε
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hZv : (p.timeScaled ε).Zv = p.Zv := rfl
  simp only [iRef, vRef, emf, hv, hg, hζ, h10, h12, hBf, hZv]
  simp only [timeScaled]
  push_cast
  field_simp

@[tmio M, powerlib_domain] private theorem timeScaled_uBridge {ε : ℝ} (hε : ε ≠ 0)
    (x : State 13) : (p.timeScaled ε).uBridge (integratorCoord hε x) = p.uBridge x := by
  obtain ⟨hi, hv, hg, hξ, hζ, h10, h11, h12⟩ := phasors_integratorCoord hε x
  obtain ⟨hZf, hZg, hBf, hωL⟩ := p.timeScaled_imp hε
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hω : ((p.timeScaled ε).ω0 : ℂ) * ((p.timeScaled ε).Lf : ℂ) = (p.ω0 : ℂ) * (p.Lf : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hωL]
  simp only [uBridge, uCtrl, p.timeScaled_iRef hε, hi, hv, hξ, h10]
  rw [hω]
  simp only [timeScaled]
  push_cast
  field_simp

/-- The time-scaled model is the `ε`-system in the coordinates `(εξ, εζ)`: its field at the
rescaled state is the rescaled `ε`-field. -/
@[tmio M, powerlib_domain] theorem timeScaled_field {ε : ℝ} (hε : ε ≠ 0) (x : State 13) :
    (p.timeScaled ε).field (integratorCoord hε x) = integratorCoord hε (p.scaledField ε x) := by
  obtain ⟨hi, hv, hg, hξ, hζ, h10, h11, h12⟩ := phasors_integratorCoord hε x
  obtain ⟨hZf, hZg, hBf, hωL⟩ := p.timeScaled_imp hε
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hconv : (p.timeScaled ε).convRow (integratorCoord hε x) = p.convRow x / ε := by
    simp only [convRow, p.timeScaled_uBridge hε, hi, hv, hZf]
    simp only [timeScaled]
    push_cast
    field_simp
  have hcap : (p.timeScaled ε).capRow (integratorCoord hε x) = p.capRow x / ε := by
    simp only [capRow, hi, hv, hg, hBf]
    simp only [timeScaled]
    push_cast
    field_simp
  have hline : (p.timeScaled ε).lineRow (integratorCoord hε x) = p.lineRow x / ε := by
    simp only [lineRow, hv, hg, hZg]
    simp only [timeScaled]
    push_cast
    field_simp
  have hcur : (p.timeScaled ε).currentIntRow (integratorCoord hε x) = p.currentIntRow x := by
    simp only [currentIntRow, p.timeScaled_iRef hε, hi, h10]
  have hvol : (p.timeScaled ε).voltageIntRow (integratorCoord hε x) = p.voltageIntRow x := by
    simp only [voltageIntRow, vRef, emf, hv, hg, h10, h12]
    rfl
  have hPe : Pe (integratorCoord hε x) = Pe x := by
    rw [Pe_eq, Pe_eq, hv, hg]
  have hQe : Qe (integratorCoord hε x) = Qe x := by
    rw [Qe_eq, Qe_eq, hv, hg]
  ext i
  rw [integratorCoord_apply, p.scaledField_apply]
  fin_cases i
  · simp [field, hconv]; field_simp
  · simp [field, hconv]; field_simp
  · simp [field, hcap]; field_simp
  · simp [field, hcap]; field_simp
  · simp [field, hline]; field_simp
  · simp [field, hline]; field_simp
  · simp [field, hcur, hε]
  · simp [field, hcur, hε]
  · simp [field, hvol, hε]
  · simp [field, hvol, hε]
  · simp [field, h11]
  · simp [field, h11, hPe, timeScaled]
  · simp [field, h12, hQe, timeScaled]

/-- The quasi-steady state of the time-scaled model is the rescaled quasi-steady state. -/
@[tmio M, powerlib_domain] theorem timeScaled_qssState {ε : ℝ} (hε : ε ≠ 0) (δ ω Qf : ℝ) :
    (p.timeScaled ε).qssState δ ω Qf = integratorCoord hε (p.qssState δ ω Qf) := by
  obtain ⟨hZf, hZg, hBf, hωL⟩ := p.timeScaled_imp hε
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hZt : (p.timeScaled ε).Zt = p.Zt := by rw [Zt, Zt, hZg]; rfl
  have hg : (p.timeScaled ε).igQ δ ((p.timeScaled ε).emf Qf) = p.igQ δ (p.emf Qf) := by
    rw [igQ, igQ, hZt]; rfl
  have hv : (p.timeScaled ε).vcQ δ ((p.timeScaled ε).emf Qf) = p.vcQ δ (p.emf Qf) := by
    rw [vcQ, vcQ, hg, hZg]; rfl
  have hi : (p.timeScaled ε).iQ δ ((p.timeScaled ε).emf Qf) = p.iQ δ (p.emf Qf) := by
    rw [iQ, iQ, hg, hv, hBf]
  have hξ : (p.timeScaled ε).xiQ δ ((p.timeScaled ε).emf Qf) = ε * p.xiQ δ (p.emf Qf) := by
    rw [xiQ, xiQ, hi]; simp only [timeScaled]; push_cast; field_simp
  have hζ : (p.timeScaled ε).zeQ δ ((p.timeScaled ε).emf Qf) = ε * p.zeQ δ (p.emf Qf) := by
    rw [zeQ, zeQ, hg, hv, hBf]; simp only [timeScaled]; push_cast; field_simp
  ext i
  rw [integratorCoord_apply]
  fin_cases i <;> simp [qssState, hg, hv, hi, hξ, hζ]

/-- **Stability transfer for the time-scaled parameters.** With a spectrally stable fast block and
a Hurwitz reduced Jacobian of `p` at a balanced quasi-steady point, the
quasi-steady equilibrium of the time-scaled model `timeScaled ε` is locally exponentially stable
for every `ε ∈ (0, ε*)`. -/
@[tmio TM, powerlib_domain] private theorem exists_epsStar_LES_timeScaled (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0)
    (hM : p.M ≠ 0) (hωq : p.ωq ≠ 0) {δ Qf : ℝ} (hP : p.Pq δ (p.emf Qf) = p.Pref)
    (hQ : p.Qq δ (p.emf Qf) = Qf) (hA : Linear.SpectrallyStable (p.fastBlock δ))
    (hR : LinearSystems.IsHurwitz (p.reducedJacobian δ Qf)) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      LocallyExponentiallyStable (p.timeScaled ε).field
        ((p.timeScaled ε).qssState δ 0 Qf) := by
  obtain ⟨εs, hεs, h⟩ :=
    p.exists_epsStar_locallyExponentiallyStable hLf hCf hLg hKic hKiv hZt hM hωq hP hQ hA hR
  refine ⟨εs, hεs, fun ε hε hlt => ?_⟩
  have hf : (p.timeScaled ε).field =
      Dynamics.transportField (integratorCoord hε.ne') 0 (p.scaledField ε) :=
    Dynamics.transportField_zero_eq_iff_comp.mpr (p.timeScaled_field hε.ne')
  have key := (Dynamics.holds_transport_iff (integratorCoord hε.ne') 0
    Flow.Property.locallyExponentiallyStable).mpr (h ε hε hlt)
  rw [Dynamics.affineCoord_zero_apply, ← hf, ← p.timeScaled_qssState hε.ne'] at key
  exact key

/-- Without droop and virtual impedance the reduced Jacobian is Hurwitz at an angle with
positive synchronizing coefficient of the swing reading, for `M, D, ω_q > 0`. -/
@[tmio M, powerlib_domain] theorem isHurwitz_reducedJacobian_of_swing (hZv : p.Zv = 0)
    (hZg : p.Zg ≠ 0) (hnq : p.nq = 0) (hM : 0 < p.M) (hD : 0 < p.D) (hωq : 0 < p.ωq) {δ : ℝ}
    (Qf : ℝ) (hK : 0 < p.swingParams.syncCoeff δ) :
    LinearSystems.IsHurwitz (p.reducedJacobian δ Qf) := by
  have hE : p.emf Qf = p.E0 := by simp [emf, hnq]
  have hK' : 0 < p.powerSlope δ (p.emf Qf) := by
    rw [hE, p.powerSlope_eq_syncCoeff hZv hZg]; exact hK
  set K := p.powerSlope δ (p.emf Qf)
  rw [Criteria.isHurwitz_fin_three_iff]
  simp only [reducedJacobian, hnq, zero_mul, zero_div, mul_zero, add_zero, mul_one, neg_div,
    Matrix.trace_fin_three,
    Matrix.det_fin_three, Criteria.principalMinorSum, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  have hDM : 0 < p.D / p.M := div_pos hD hM
  have hKM : 0 < K / p.M := div_pos hK' hM
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith [mul_pos hωq hKM]
  · nlinarith [mul_pos hωq hKM, mul_pos hDM hKM, mul_pos (mul_pos hDM hDM) hωq,
      mul_pos (mul_pos hωq hωq) hDM]

end Params

/-! ### The DC variant -/

namespace DCParams

variable (q : DCParams)

/-- The time-scaled DC variant: the AC parameters time-scaled, the DC side unchanged. -/
def timeScaled (ε : ℝ) : DCParams := { q with toParams := q.toParams.timeScaled ε }

/-- The `ε`-system of the DC variant: the ten fast rows multiplied by `ε⁻¹`. -/
def scaledField (ε : ℝ) : State 16 → State 16 :=
  SingularPerturbation.splitScaledField splitDC ε q.field

/-- The diagonal coordinate change `(ξ, ζ) ↦ (εξ, εζ)` of the 16-state vector. -/
def integratorScale (ε : ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.diagonal fun i => if 6 ≤ i.val ∧ i.val < 10 then ε else 1

@[tmio M, powerlib_domain] theorem integratorScale_isUnit {ε : ℝ} (hε : ε ≠ 0) :
    IsUnit (integratorScale ε) := by
  rw [Matrix.isUnit_iff_isUnit_det, integratorScale, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
  split_ifs <;> simp [hε]

/-- The integrator rescaling of the 16-state vector as a coordinate change. -/
def integratorCoord {ε : ℝ} (hε : ε ≠ 0) : State 16 ≃L[ℝ] State 16 :=
  Dynamics.matrixCoord (integratorScale ε) (integratorScale_isUnit hε)

@[tmio M, powerlib_domain] theorem integratorCoord_apply {ε : ℝ} (hε : ε ≠ 0) (x : State 16)
    (i : Fin 16) : integratorCoord hε x i = (if 6 ≤ i.val ∧ i.val < 10 then ε else 1) * x i := by
  simp [integratorCoord, integratorScale, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

@[tmio M, powerlib_domain] private theorem core_integratorCoord {ε : ℝ} (hε : ε ≠ 0)
    (x : State 16) : core (integratorCoord hε x) = Params.integratorCoord hε (core x) := by
  ext i
  rw [Params.integratorCoord_apply]
  simp only [core, PiLp.toLp_apply, integratorCoord_apply, Fin.val_castAdd]

@[tmio M, powerlib_domain] theorem scaledField_apply (ε : ℝ) (x : State 16) (i : Fin 16) :
    q.scaledField ε x i = (if i.val < 10 then ε⁻¹ else 1) * q.field x i := by
  simp only [scaledField, SingularPerturbation.splitScaledField,
    SingularPerturbation.splitScale, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  fin_cases i <;> rfl

@[tmio M, powerlib_domain] private theorem Pbr_integratorCoord {ε : ℝ} (hε : ε ≠ 0)
    (x : State 16) : (q.timeScaled ε).Pbr (integratorCoord hε x) = q.Pbr x := by
  obtain ⟨hi, -⟩ := Params.phasors_integratorCoord hε (core x)
  simp only [Pbr, core_integratorCoord]
  rw [show (q.timeScaled ε).toParams = q.toParams.timeScaled ε from rfl,
    q.toParams.timeScaled_uBridge hε, hi]

/-- The time-scaled DC variant is the `ε`-system in the coordinates `(εξ, εζ)`. -/
@[tmio M, powerlib_domain] theorem timeScaled_field {ε : ℝ} (hε : ε ≠ 0) (x : State 16) :
    (q.timeScaled ε).field (integratorCoord hε x) = integratorCoord hε (q.scaledField ε x) := by
  have hAC := q.toParams.timeScaled_field hε (core x)
  have hcore := core_integratorCoord hε x
  have hpow : (q.timeScaled ε).powerRef (integratorCoord hε x) = q.powerRef x := by
    simp only [powerRef, integratorCoord_apply]; norm_num; rfl
  ext i
  rw [integratorCoord_apply, q.scaledField_apply]
  refine Fin.addCases (m := 13) (n := 3) (fun j => ?_) (fun k => ?_) i
  · by_cases hj : j = 11
    · subst hj
      rw [show (Fin.castAdd 3 (11 : Fin 13) : Fin 16) = 11 from rfl, field_11, field_11, hpow]
      simp only [hcore]
      have hPe : Pe (Params.integratorCoord hε (core x)) = Pe (core x) := by
        rw [Pe_eq, Pe_eq]
        simp only [capVoltage, lineCurrent, phasor, Params.integratorCoord_apply]; norm_num
      rw [hPe]
      simp [integratorCoord_apply]
      rfl
    · rw [field_fast _ _ _ hj, field_fast _ _ _ hj, show (q.timeScaled ε).toParams =
        q.toParams.timeScaled ε from rfl, hcore, hAC, Params.integratorCoord_apply,
        Params.scaledField_apply]
      simp [Fin.val_castAdd]
  · obtain ⟨k, hk⟩ := k
    interval_cases k
    · change (q.timeScaled ε).field (integratorCoord hε x) 13 =
        (if 6 ≤ 13 ∧ 13 < 10 then ε else 1) * ((if 13 < 10 then ε⁻¹ else 1) * q.field x 13)
      rw [field_13, field_13, q.Pbr_integratorCoord hε, integratorCoord_apply]
      norm_num
      rfl
    · change (q.timeScaled ε).field (integratorCoord hε x) 14 =
        (if 6 ≤ 14 ∧ 14 < 10 then ε else 1) * ((if 14 < 10 then ε⁻¹ else 1) * q.field x 14)
      rw [field_14, field_14, integratorCoord_apply]
      norm_num
      rfl
    · change (q.timeScaled ε).field (integratorCoord hε x) 15 =
        (if 6 ≤ 15 ∧ 15 < 10 then ε else 1) * ((if 15 < 10 then ε⁻¹ else 1) * q.field x 15)
      rw [field_15, field_15, integratorCoord_apply, integratorCoord_apply]
      norm_num
      exact Or.inl rfl

@[tmio M, powerlib_domain] private theorem graph_integratorCoord {ε : ℝ} (hε : ε ≠ 0)
    (s : State 6) : (q.timeScaled ε).graph s = integratorCoord hε (q.graph s) := by
  ext i
  rw [integratorCoord_apply]
  refine Fin.addCases (m := 13) (n := 3) (fun j => ?_) (fun k => ?_) i
  · rw [graph_castAdd, graph_castAdd, show (q.timeScaled ε).toParams =
      q.toParams.timeScaled ε from rfl, q.toParams.timeScaled_qssState hε,
      Params.integratorCoord_apply]
    simp [Fin.val_castAdd]
  · rw [graph_natAdd, graph_natAdd]
    fin_cases k <;> simp

/-- **Stability transfer for the time-scaled DC variant.** At a quasi-steady equilibrium of the
DC variant (`P = P_ref + K_idc ξ_dc`, `Q = Q_f`, `P_br = P_dc`, `v_dc = v_f = v_ref`) with a
spectrally stable fast block and a Hurwitz six-state reduced Jacobian, there is `ε* > 0` such that
the time-scaled DC variant is locally exponentially stable at its equilibrium for every
`ε ∈ (0, ε*)`. -/
@[tmio TM, powerlib_domain] private theorem exists_epsStar_LES_timeScaled (hLf : q.Lf ≠ 0)
    (hCf : q.Cf ≠ 0) (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0)
    (hM : q.M ≠ 0) (hωq : q.ωq ≠ 0) (hCdc : q.Cdc ≠ 0) (hvref : q.vref ≠ 0) (hωf : q.ωf ≠ 0)
    {δ Qf ξ : ℝ} (hP : q.Pq δ (q.emf Qf) = q.Pref + q.Kidc * ξ) (hQ : q.Qq δ (q.emf Qf) = Qf)
    (hB : q.PbrQ δ (q.emf Qf) = q.Pdc) (hA : Linear.SpectrallyStable (q.fastBlock δ))
    (hR : LinearSystems.IsHurwitz (q.reducedJacobian δ Qf q.vref)) :
    ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      LocallyExponentiallyStable (q.timeScaled ε).field
        ((q.timeScaled ε).graph ((q.timeScaled ε).slowPoint δ Qf ξ)) := by
  set s₀ := q.slowPoint δ Qf ξ
  have hs0 : s₀ 0 = δ ∧ s₀ 1 = 0 ∧ s₀ 2 = Qf ∧ s₀ 3 = q.vref ∧ s₀ 4 = ξ ∧ s₀ 5 = q.vref := by
    simp [s₀, slowPoint]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hs0
  have hcore : core (q.graph s₀) = q.qssState δ 0 Qf := by rw [core_graph, h0, h1, h2]
  have heq : q.field (q.graph s₀) = 0 :=
    (q.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq hCdc hvref hωf _).mpr
      ⟨δ, Qf, hcore, by rw [graph_13, h3], by rw [graph_15, h5], by rw [graph_14, h4]; exact hP,
        hQ, hB⟩
  have hU : IsOpen {x : State 16 | x 13 ≠ 0} :=
    isOpen_ne_fun (Dynamics.contDiff_coord (k := 1) 13).continuous continuous_const
  have hx : q.graph s₀ ∈ {x : State 16 | x 13 ≠ 0} := by
    show q.graph s₀ 13 ≠ 0; rw [graph_13, h3]; exact hvref
  have hRed := q.hasFDerivAt_reducedField hLf hCf hLg hKic hKiv hZt hCdc s₀
    (by rw [h3]; exact hvref) (by rw [h0, h2]; exact hB)
  rw [h0, h2, h3] at hRed
  obtain ⟨εs, hεs, h⟩ :=
    SingularPerturbation.exists_epsStar_locallyExponentiallyStable_of_graph
      (A := q.fastBlock δ) splitDC hU hx (q.contDiffOn_field hCdc) heq
      ((q.contDiff_graph).differentiable (by norm_num) _) q.graph_slow
      (q.fast_graph hLf hCf hLg hKic hKiv hZt)
      (fun i j => by simpa [graph_10, h0] using q.hasDerivAt_fast (q.graph s₀) i j) hRed hA
      ((Linear.spectrallyStable_iff_isHurwitz _).mpr hR)
  refine ⟨εs, hεs, fun ε hε hlt => ?_⟩
  have hf : (q.timeScaled ε).field =
      Dynamics.transportField (integratorCoord hε.ne') 0 (q.scaledField ε) :=
    Dynamics.transportField_zero_eq_iff_comp.mpr (q.timeScaled_field hε.ne')
  have hs : (q.timeScaled ε).slowPoint δ Qf ξ = s₀ := rfl
  have key := (Dynamics.holds_transport_iff (integratorCoord hε.ne') 0
    Flow.Property.locallyExponentiallyStable).mpr (h ε hε hlt)
  rw [Dynamics.affineCoord_zero_apply, show SingularPerturbation.splitScaledField splitDC ε q.field
    = q.scaledField ε from rfl, ← hf, ← q.graph_integratorCoord hε.ne', ← hs] at key
  exact key

end DCParams

/-! ## Connection conclusions -/

/-- The time-scaled full model at the selected point of `m`. -/
def Model.timeScaled (m : Model) (ε : ℝ) : Model := ⟨m.p.timeScaled ε, m.δ, m.Qf⟩

@[tmio TM, powerlib_domain] private theorem mem_den_flow' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)

/-- **Stability transfer (connection).** At a balanced quasi-steady point with a spectrally
stable fast block and a Hurwitz reduced Jacobian, the time-scaled full model is in the
denotation of local exponential stability for every `ε ∈ (0, ε*)`. -/
@[tmio TM, powerlib_domain] theorem exists_epsStar_mem_den_LES (m : Model) (hLf : m.p.Lf ≠ 0)
    (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKic : m.p.Kic ≠ 0) (hKiv : m.p.Kiv ≠ 0)
    (hZt : m.p.Zt ≠ 0) (hM : m.p.M ≠ 0) (hωq : m.p.ωq ≠ 0)
    (hP : m.p.Pq m.δ (m.p.emf m.Qf) = m.p.Pref) (hQ : m.p.Qq m.δ (m.p.emf m.Qf) = m.Qf)
    (hA : Linear.SpectrallyStable (m.p.fastBlock m.δ))
    (hR : LinearSystems.IsHurwitz (m.p.reducedJacobian m.δ m.Qf)) :
    connection% (∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      m.timeScaled ε ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨εs, hεs, h⟩ :=
    m.p.exists_epsStar_LES_timeScaled hLf hCf hLg hKic hKiv hZt hM hωq hP hQ hA hR
  exact ⟨εs, hεs, fun ε hε hlt => mem_den_flow'.mpr (h ε hε hlt)⟩

/-- **Reading the reduced Q–V droop model (connection).** Without virtual impedance, if the
reduced Q–V droop model `Params.qvDroop` is locally exponentially stable at the selected point
`(δ*, 0, Q*)` (`QVDroop.family`) and the fast block (boundary layer) is spectrally stable, then
the time-scaled full model is locally exponentially stable for every `ε ∈ (0, ε*)` (scaffold
`theorem/GridTiedConverter/GFM/FullModel/FullModelTimeScale.agda`). -/
@[tmio TM, powerlib_domain] theorem exists_epsStar_mem_den_LES_of_qvDroop (m : Model)
    (hLf : m.p.Lf ≠ 0) (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKic : m.p.Kic ≠ 0)
    (hKiv : m.p.Kiv ≠ 0) (hZv : m.p.Zv = 0) (hZg : m.p.Zg ≠ 0) (hM : m.p.M ≠ 0)
    (hωq : m.p.ωq ≠ 0)
    (hred : (⟨m.p.qvDroop, m.δ, m.Qf⟩ : QVDroop.Model) ∈
      QVDroop.family.den (.flow .locallyExponentiallyStable))
    (hA : Linear.SpectrallyStable (m.p.fastBlock m.δ)) :
    connection% (∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      m.timeScaled ε ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  set q := m.p.qvDroop
  have hZt : m.p.Zt ≠ 0 := by rwa [Params.Zt, hZv, add_zero]
  have hLES : LocallyExponentiallyStable q.field (Dynamics.mk3 m.δ 0 m.Qf) :=
    (Spectral.mem_den_flow_iff_shift (f := fun r : QVDroop.Model => r.q.field)
      (pt := QVDroop.Model.point) QVDroop.family_isAutonomous).mp hred
  obtain ⟨heq, hH⟩ := (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _
    q.contDiff_field (q.fderiv_field _)).mp hLES
  have hJ : m.p.reducedJacobian m.δ m.Qf = q.jacobian m.δ (q.emf m.Qf) := by
    have h1 := m.p.hasFDerivAt_reducedField hZt (Dynamics.mk3 m.δ 0 m.Qf)
    rw [m.p.reducedField_eq_qvDroop hZv hZg] at h1
    have h3 := h1.unique (q.hasFDerivAt_field (Dynamics.mk3 m.δ 0 m.Qf))
    simpa using Matrix.toEuclideanCLM.injective h3
  obtain ⟨-, hP, hQ⟩ := (q.field_eq_zero_iff hM hωq _).mp heq
  have hR : LinearSystems.IsHurwitz (m.p.reducedJacobian m.δ m.Qf) := by
    rw [hJ]; simpa using hH
  exact (connection_proof% exists_epsStar_mem_den_LES) m hLf hCf hLg hKic hKiv hZt hM hωq
    (by rw [m.p.Pq_eq_qvDroop hZv hZg]; exact hP) (by rw [m.p.Qq_eq_qvDroop hZv hZg]; exact hQ)
    hA hR

/-- **Reading the swing machine (connection).** Without droop and virtual impedance, a balanced
angle of `Params.swingParams` with positive synchronizing coefficient (`M, D, ω_q > 0`) and a
spectrally stable fast block is locally exponentially stable in the time-scaled full model for
every `ε ∈ (0, ε*)`. -/
@[tmio TM, powerlib_domain] theorem exists_epsStar_mem_den_LES_of_swing (m : Model)
    (hLf : m.p.Lf ≠ 0) (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKic : m.p.Kic ≠ 0)
    (hKiv : m.p.Kiv ≠ 0) (hZg : m.p.Zg ≠ 0) (hZv : m.p.Zv = 0) (hnq : m.p.nq = 0)
    (hM : 0 < m.p.M) (hD : 0 < m.p.D) (hωq : 0 < m.p.ωq) (hb : m.p.swingParams.Pe m.δ = m.p.Pref)
    (hQ : m.p.Qq m.δ m.p.E0 = m.Qf) (hK : 0 < m.p.swingParams.syncCoeff m.δ)
    (hA : Linear.SpectrallyStable (m.p.fastBlock m.δ)) :
    connection% (∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      m.timeScaled ε ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have hE : m.p.emf m.Qf = m.p.E0 := by simp [Params.emf, hnq]
  exact exists_epsStar_mem_den_LES m hLf hCf hLg hKic hKiv (by rwa [Params.Zt, hZv, add_zero])
    hM.ne' hωq.ne' (by rw [hE, m.p.Pq_eq_swing hZv hZg]; exact hb) (by rw [hE]; exact hQ) hA
    (m.p.isHurwitz_reducedJacobian_of_swing hZv hZg hnq hM hD hωq m.Qf hK)

/-- The time-scaled DC-variant model at the selected point of `m`. -/
def DCModel.timeScaled (m : DCModel) (ε : ℝ) : DCModel := ⟨m.q.timeScaled ε, m.δ, m.Qf, m.ξ⟩

/-- **Stability transfer for the DC variant (connection).** At a balanced quasi-steady point of
the DC variant with a spectrally stable fast block and a Hurwitz six-state reduced Jacobian
`DCParams.reducedJacobian δ* Q* v_ref`, the time-scaled DC variant is in the denotation of local
exponential stability for every `ε ∈ (0, ε*)`. -/
@[tmio TM, powerlib_domain] theorem dcFamily_exists_epsStar_mem_den_LES (m : DCModel)
    (hLf : m.q.Lf ≠ 0) (hCf : m.q.Cf ≠ 0) (hLg : m.q.Lg ≠ 0) (hKic : m.q.Kic ≠ 0)
    (hKiv : m.q.Kiv ≠ 0) (hZt : m.q.Zt ≠ 0) (hM : m.q.M ≠ 0) (hωq : m.q.ωq ≠ 0)
    (hCdc : m.q.Cdc ≠ 0) (hvref : m.q.vref ≠ 0) (hωf : m.q.ωf ≠ 0)
    (hP : m.q.Pq m.δ (m.q.emf m.Qf) = m.q.Pref + m.q.Kidc * m.ξ)
    (hQ : m.q.Qq m.δ (m.q.emf m.Qf) = m.Qf) (hB : m.q.PbrQ m.δ (m.q.emf m.Qf) = m.q.Pdc)
    (hA : Linear.SpectrallyStable (m.q.fastBlock m.δ))
    (hR : LinearSystems.IsHurwitz (m.q.reducedJacobian m.δ m.Qf m.q.vref)) :
    connection% (∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      m.timeScaled ε ∈ dcFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨εs, hεs, h⟩ := m.q.exists_epsStar_LES_timeScaled hLf hCf hLg hKic hKiv hZt hM hωq
    hCdc hvref hωf hP hQ hB hA hR
  refine ⟨εs, hεs, fun ε hε hlt => ?_⟩
  exact (Spectral.mem_den_flow_iff_shift (f := fun m : DCModel => m.q.field)
    (pt := DCModel.point) (Spectral.localFamily_isAutonomous _ _ _)).mpr (h ε hε hlt)

end powerlib.GFM.FullModel
