import theorem.GridTiedConverter.GFM.DVOCNetwork
import theorem.PowerSystem.Network.Swing.Basic
import theorem.Spectral.Family
import theorem.Criteria.Lyapunov
import theorem.Dynamics.Linearization

/-! # Dispatchable virtual oscillators with set-points: local exponential stability of the
synchronous set

Model boundary.
* The dVOC network of `theorem/GridTiedConverter/GFM/DVOCNetwork.lean` (`DVOC`) on `n + 1` units
  indexed by `Fin (n + 1)`, unit `0` the angle reference, read about a selected angle profile `θ*`
  (`Model`); stationary `αβ` frame, continuous time.
* Reduced state, order `Fin (n + (n + 1))` (the ordering of `Network.Swing`): first the relative
  angles `δᵢ = (θ_{i+1} − θ₀) − (θ*_{i+1} − θ*₀)` (`dIdx i`), then the log-magnitudes
  `ρ_k = log(|v_k|/v*_k)` (`wIdx k`). The chart `v_k = s_k e^{ρ_k + jδ̃_k}` (`chart`, `δ̃₀ = 0`)
  covers the states with every `v_k ≠ 0` up to the common rotation; the origin of the reduced
  state is the selected synchronous state, whose rotation orbit is the synchronous set `T`.
* Reduced field (`polarField`): the real and imaginary parts of the logarithmic rate `v̇_k/v_k`
  (`logRate`) with the common rotation `Im(v̇₀/v₀)` removed; `field_chart` proves the reading
  identity `f_k(v) = v_k g_k` on the chart.
* Excluded: as in `DVOCNetwork`; states with a zero unit voltage (outside the chart).

Source: M. Colombino, D. Groß, J.-S. Brouillon, F. Dörfler, *IEEE Trans. Autom. Control* 64 (2019)
4496–4511 (arXiv:1710.00694), Theorem 4 (stability of the target set) in its linearized form;
the grounded relative coordinates of `theorem/PowerSystem/Network/Swing/Basic.lean` for the
rotational symmetry; work-sync `theory/T-voc-dvoc.md` §1.5.

Results.
* `field_chart` (the reading), `polarField_zero_iff` (the selected state is an equilibrium of the
  reduced field exactly when the profile is a relative equilibrium, `Synchronous`:
  `η(K_k − K^θ_k) = jω` for a common `ω`), `synchronous_of_balanced`, `polarField_contDiff`,
  `hasFDerivAt_polarField` and `fderiv_polarField` (the Jacobian `jacobian`, the matrix of
  `jacCLM`: rows `Im(dLog_{i+1} − dLog₀)` and `Re dLog_k`, `dLog_k = ηΛ_k − αρ_k`,
  `Λ_k = ∑ⱼ w_{jk}(s_j/s_k)((ρ_j − ρ_k) + j(δ̃_j − δ̃_k))`).
* `isHurwitz_jacobian_of_dissipative`: with `η, α > 0` and a coupling dissipative at any rate
  `μ > 0` off the profile (`DVOC.Dissipative`) the reduced Jacobian is Hurwitz — a strict Lyapunov
  form `(Re z)² + c‖u‖²` of the complex image (`xi_jacobian`). Locally the amplitude feedback only
  helps: the `α/η` term of (29), needed for the global result, is not needed for local stability.

Family and connection conclusions.
* `family : Family (Model n) Spectral.Requirement (n + (n + 1)) 0` (`Spectral.localFamily`) reads
  a model as its reduced field about the selected profile; stability condition `Model.Stable`
  (relative equilibrium and Hurwitz reduced Jacobian), instability condition `Model.Unstable`
  (relative equilibrium and a characteristic root in the open right half plane).
* `chain_le_semantics` (soundness: linearization and its instability form),
  `mem_den_locallyExponentiallyStable_iff` and `exact_locallyExponentiallyStable` (exact, by
  converse linearization), `mem_den_locallyExponentiallyStable_of_dissipative`,
  `mem_den_locallyExponentiallyStable_of_condition` (Colombino et al. Condition 1 with consistent
  set-points), `twoUnequal_mem_den_locallyExponentiallyStable` (two units with `v* = (1, 2)`: local
  exponential stability where Condition 1 fails for every gain).
* The local exponential stability of the reduced field is the transversal (orbital) exponential
  stability of the synchronous set: in the stationary frame the solutions on `T` are periodic
  orbits, and set stability is not a sentence of the library. The almost-global convergence
  results stay private trajectory-level evidence in `DVOCNetwork`.
-/

noncomputable section
namespace powerlib.GFM
namespace DVOC

open Complex ComplexConjugate Filter Topology
open powerlib.Dynamics (State)
open powerlib.Network.Swing (dIdx wIdx angleMap ground ground_zero ground_succ)

variable {n : ℕ}

/-- A coordinate of the reduced state. -/
abbrev coordCLM (r : Fin (n + (n + 1))) : State (n + (n + 1)) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin (n + (n + 1)) => ℝ) r

/-- The log-polar coordinate `ρ_k + j δ̃_k` of unit `k` (`δ̃₀ = 0`, `δ̃_{i+1} = δᵢ`). -/
def logCoord (k : Fin (n + 1)) : State (n + (n + 1)) →L[ℝ] ℂ :=
  ofRealCLM ∘L coordCLM (wIdx k) +
    (ContinuousLinearMap.mul ℝ ℂ I) ∘L ofRealCLM ∘L ((ContinuousLinearMap.proj k) ∘L angleMap)

@[tmio M, simp, powerlib_domain] theorem logCoord_apply (k : Fin (n + 1))
    (z : State (n + (n + 1))) :
    logCoord k z = (z (wIdx k) : ℂ) + (angleMap z k : ℂ) * I := by
  simp [logCoord, mul_comm]

variable (m : DVOC (Fin (n + 1))) (θ : Fin (n + 1) → ℝ)

/-- The log-polar chart about the profile: `v_k = s_k e^{ρ_k + j δ̃_k}`. -/
def chart (z : State (n + (n + 1))) (k : Fin (n + 1)) : ℂ :=
  m.profile θ k * exp (logCoord k z)

/-- The logarithmic rate `v̇_k / v_k` in the chart:
`jω₀ + η (K_k − ∑ⱼ w_{jk}(1 − (s_j/s_k) e^{(ρ_j − ρ_k) + j(δ̃_j − δ̃_k)})) + α (1 − e^{ρ_k})`. -/
def logRate (z : State (n + (n + 1))) (k : Fin (n + 1)) : ℂ :=
  I * m.ω0 + m.η * (m.gain k - ∑ j, (m.w j k : ℂ) *
    (1 - m.profile θ j / m.profile θ k * exp (logCoord j z - logCoord k z))) +
      m.α * (1 - exp (z (wIdx k) : ℂ))

/-- The reduced field in the log-polar coordinates `(δ, ρ)` about the profile `θ`: relative angles
`δᵢ = θ_{i+1} − θ₀ − (θ*_{i+1} − θ*₀)` and log-magnitudes `ρ_k = log(|v_k|/v*_k)`; the common
rotation is removed. -/
def polarField (z : State (n + (n + 1))) : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun i => (m.logRate θ z i.succ).im - (m.logRate θ z 0).im)
    (fun k => (m.logRate θ z k).re) r

@[tmio M, simp, powerlib_domain] theorem polarField_dIdx (z : State (n + (n + 1))) (i : Fin n) :
    m.polarField θ z (dIdx i) = (m.logRate θ z i.succ).im - (m.logRate θ z 0).im := by
  simp [polarField]

@[tmio M, simp, powerlib_domain] theorem polarField_wIdx (z : State (n + (n + 1)))
    (k : Fin (n + 1)) : m.polarField θ z (wIdx k) = (m.logRate θ z k).re := by
  simp [polarField]

variable {m}

/-- **The reading in log-polar coordinates.** At every state `v = s e^{ρ + jδ̃}` of the chart the
dVOC field is `f_k(v) = v_k (Re g_k + j Im g_k)` with the logarithmic rate `g = logRate`: the
reduced field is the dVOC field in the chart up to the common rotation `j Im g₀`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem field_chart (hv : ∀ k, 0 < m.vstar k)
    (z : State (n + (n + 1))) (k : Fin (n + 1)) :
    m.field (m.chart θ z) k = m.chart θ z k * m.logRate θ z k := by
  have hs : ∀ j, m.profile θ j ≠ 0 := profile_ne_zero hv θ
  have hlap : m.lap (m.chart θ z) k = m.chart θ z k * ∑ j, (m.w j k : ℂ) *
      (1 - m.profile θ j / m.profile θ k * exp (logCoord j z - logCoord k z)) := by
    rw [lap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hk := hs k
    have he := Complex.exp_ne_zero (logCoord k z)
    simp only [chart, Complex.exp_sub]
    field_simp
  have hnorm : ‖m.chart θ z k‖ = m.vstar k * Real.exp (z (wIdx k)) := by
    rw [chart, norm_mul, norm_profile hv, logCoord_apply, Complex.norm_exp]
    simp
  have hamp : ((m.amp k (m.chart θ z k) : ℝ) : ℂ) = 1 - exp (z (wIdx k) : ℂ) := by
    rw [amp, hnorm, mul_div_cancel_left₀ _ (hv k).ne']
    push_cast
    rw [← Complex.ofReal_exp]
  rw [field, hlap, hamp, logRate]
  ring

variable (m)

/-- The linearized coupling rate of unit `k`:
`Λ_k = ∑ⱼ w_{jk} (s_j/s_k) ((ρ_j − ρ_k) + j(δ̃_j − δ̃_k))`. -/
def rate (k : Fin (n + 1)) : State (n + (n + 1)) →L[ℝ] ℂ :=
  ∑ j, ((m.w j k : ℂ) * (m.profile θ j / m.profile θ k)) • (logCoord j - logCoord k)

/-- The derivative of the logarithmic rate at the profile: `η Λ_k − α ρ_k`. -/
def dLog (k : Fin (n + 1)) : State (n + (n + 1)) →L[ℝ] ℂ :=
  (m.η : ℂ) • m.rate θ k - (m.α : ℂ) • (ofRealCLM ∘L coordCLM (wIdx k))

/-- The reduced Jacobian as a linear map: rows `Im(dLog_{i+1} − dLog₀)` for the relative angles,
`Re dLog_k` for the log-magnitudes. -/
def jacCLM : State (n + (n + 1)) →L[ℝ] State (n + (n + 1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + (n + 1)) => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun r => Fin.addCases (motive := fun _ => State (n + (n + 1)) →L[ℝ] ℝ)
      (fun i => imCLM ∘L m.dLog θ i.succ - imCLM ∘L m.dLog θ 0) (fun k => reCLM ∘L m.dLog θ k) r

/-- The reduced Jacobian matrix of the dVOC network at the profile `θ`. -/
def jacobian : Matrix (Fin (n + (n + 1))) (Fin (n + (n + 1))) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin (n + (n + 1))) (𝕜 := ℝ)).symm (m.jacCLM θ)

/-- The profile is a relative equilibrium: the gains are the angle gains up to a common rotation,
`η (K_k − K^θ_k) = jω` for every `k`, with `ω = Im(η (K₀ − K^θ₀))`. -/
def Synchronous : Prop :=
  ∀ k, (m.η : ℂ) * (m.gain k - m.angleGain θ k) =
    (((m.η : ℂ) * (m.gain 0 - m.angleGain θ 0)).im : ℂ) * I

variable {m}

@[tmio M, simp, powerlib_domain] theorem jacCLM_dIdx (y : State (n + (n + 1))) (i : Fin n) :
    m.jacCLM θ y (dIdx i) = (m.dLog θ i.succ y).im - (m.dLog θ 0 y).im := by
  simp [jacCLM]

@[tmio M, simp, powerlib_domain] theorem jacCLM_wIdx (y : State (n + (n + 1))) (k : Fin (n + 1)) :
    m.jacCLM θ y (wIdx k) = (m.dLog θ k y).re := by
  simp [jacCLM]

@[tmio M, powerlib_domain] theorem toEuclideanCLM_jacobian :
    Matrix.toEuclideanCLM (n := Fin (n + (n + 1))) (𝕜 := ℝ) (m.jacobian θ) = m.jacCLM θ :=
  StarAlgEquiv.apply_symm_apply _ _

@[tmio M, powerlib_domain] theorem logRate_zero (k : Fin (n + 1)) :
    m.logRate θ 0 k = I * m.ω0 + m.η * (m.gain k - m.angleGain θ k) := by
  simp [logRate, angleGain]

/-- **The selected state is an equilibrium of the reduced field exactly when the profile is a
relative equilibrium** (`Synchronous`; consistent set-points, `Balanced θ ω`, give it). Static
evidence on the model. -/
@[tmio T, powerlib_foundation] private theorem sync_aux (D : Fin (n + 1) → ℂ) (ω0 : ℝ) :
    ((∀ k, (I * ω0 + D k).re = 0) ∧ ∀ i : Fin n, (I * ω0 + D i.succ).im - (I * ω0 + D 0).im = 0) ↔
      ∀ k, D k = ((D 0).im : ℂ) * I := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    zero_add]
  constructor
  · rintro ⟨hre, him⟩ k
    apply Complex.ext
    · simp [hre k]
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, add_zero]
      refine Fin.cases rfl (fun i => ?_) k
      linarith [him i]
  · intro h
    refine ⟨fun k => ?_, fun i => ?_⟩
    · rw [h k]; simp
    · rw [h i.succ]; simp

/-- **The selected state is an equilibrium of the reduced field exactly when the profile is a
relative equilibrium** (`Synchronous`; consistent set-points, `Balanced θ ω`, give it). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem polarField_zero_iff :
    m.polarField θ 0 = 0 ↔ m.Synchronous θ := by
  have hiff : m.polarField θ 0 = 0 ↔ (∀ k, (m.logRate θ 0 k).re = 0) ∧
      ∀ i : Fin n, (m.logRate θ 0 i.succ).im - (m.logRate θ 0 0).im = 0 := by
    constructor
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have := congrArg (fun z => z (wIdx k)) h; simpa using this
      · have := congrArg (fun z => z (dIdx i)) h; simpa using this
    · rintro ⟨h1, h2⟩
      apply Dynamics.state_ext_blocks
      · intro i; change m.polarField θ 0 (dIdx i) = 0; rw [polarField_dIdx]; exact h2 i
      · intro k; change m.polarField θ 0 (wIdx k) = 0; rw [polarField_wIdx]; exact h1 k
  simp only [hiff, logRate_zero]
  exact sync_aux (fun k => (m.η : ℂ) * (m.gain k - m.angleGain θ k)) m.ω0

@[tmio M, powerlib_domain] theorem synchronous_of_balanced {ω : ℝ} (hb : m.Balanced θ ω) :
    m.Synchronous θ := fun k => by
  rw [hb k, hb 0]
  simp only [add_sub_cancel_left]
  apply Complex.ext <;> simp

/-- The logarithmic rate is `C¹`. -/
@[tmio M, powerlib_domain] private theorem logRate_contDiff (k : Fin (n + 1)) :
    ContDiff ℝ 1 fun z => m.logRate θ z k := by
  unfold logRate
  have hL : ∀ j, ContDiff ℝ 1 fun z : State (n + (n + 1)) =>
      exp (logCoord j z - logCoord k z) := fun j =>
    ((logCoord j).contDiff.sub (logCoord k).contDiff).cexp
  have hR : ContDiff ℝ 1 fun z : State (n + (n + 1)) => exp (z (wIdx k) : ℂ) :=
    (ofRealCLM.contDiff.comp (coordCLM (wIdx k)).contDiff).cexp
  refine (contDiff_const.add (contDiff_const.mul (contDiff_const.sub
    (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_const.sub
      (contDiff_const.mul (hL j))))))).add (contDiff_const.mul (contDiff_const.sub hR))

/-- The reduced field is `C¹`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem polarField_contDiff : ContDiff ℝ 1 (m.polarField θ) := by
  rw [contDiff_euclidean]
  intro r
  refine Fin.addCases (fun i => ?_) (fun k => ?_) r
  · have : (fun z => m.polarField θ z (dIdx i)) =
        fun z => (m.logRate θ z i.succ).im - (m.logRate θ z 0).im := by
      funext z; exact polarField_dIdx m θ z i
    rw [this]
    exact (imCLM.contDiff.comp (logRate_contDiff (m := m) θ _)).sub
      (imCLM.contDiff.comp (logRate_contDiff (m := m) θ _))
  · have : (fun z => m.polarField θ z (wIdx k)) = fun z => (m.logRate θ z k).re := by
      funext z; exact polarField_wIdx m θ z k
    rw [this]
    exact reCLM.contDiff.comp (logRate_contDiff (m := m) θ _)

/-- The derivative of the logarithmic rate at the profile. -/
@[tmio M, powerlib_domain] private theorem hasFDerivAt_logRate (k : Fin (n + 1)) :
    HasFDerivAt (fun z => m.logRate θ z k) (m.dLog θ k) 0 := by
  have hL : ∀ j, HasFDerivAt (fun z : State (n + (n + 1)) =>
      exp ((logCoord j - logCoord k) z)) ((logCoord j - logCoord k)) 0 := fun j => by
    have := (logCoord j - logCoord k).hasFDerivAt (x := (0 : State (n + (n + 1)))).cexp
    simpa using this
  have hR : HasFDerivAt (fun z : State (n + (n + 1)) =>
      exp ((ofRealCLM ∘L coordCLM (wIdx k)) z)) (ofRealCLM ∘L coordCLM (wIdx k)) 0 := by
    have := (ofRealCLM ∘L coordCLM (wIdx k)).hasFDerivAt
      (x := (0 : State (n + (n + 1)))).cexp
    simpa using this
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((hasFDerivAt_const (1 : ℂ) (0 : State (n + (n + 1)))).sub
      ((hL j).const_mul (m.profile θ j / m.profile θ k))).const_mul (m.w j k : ℂ)
  have h := ((hasFDerivAt_const (I * m.ω0) (0 : State (n + (n + 1)))).add
    (((hasFDerivAt_const (m.gain k) (0 : State (n + (n + 1)))).sub hsum).const_mul
      (m.η : ℂ))).add (((hasFDerivAt_const (1 : ℂ) _).sub hR).const_mul (m.α : ℂ))
  have hfun : (fun z => m.logRate θ z k) = fun z => I * m.ω0 + m.η * (m.gain k - ∑ j,
      (m.w j k : ℂ) * (1 - m.profile θ j / m.profile θ k * exp ((logCoord j - logCoord k) z))) +
        m.α * (1 - exp ((ofRealCLM ∘L coordCLM (wIdx k)) z)) := by
    funext z; simp [logRate]
  rw [hfun]
  convert h using 1
  ext y
  simp only [dLog, rate, sub_apply, smul_apply, add_apply, FunLike.coe_sum, Finset.sum_apply,
    smul_eq_mul, zero_add, zero_sub, Finset.smul_sum, neg_apply, mul_neg, Finset.mul_sum]
  ring_nf
  simp only [Finset.sum_sub_distrib, mul_comm, mul_assoc, mul_left_comm]
  ring

/-- **The Jacobian of the reduced field at the profile.** Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_polarField :
    HasFDerivAt (m.polarField θ) (m.jacCLM θ) 0 := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro r
  rw [hasFDerivWithinAt_univ]
  refine Fin.addCases (fun i => ?_) (fun k => ?_) r
  · have hfun : (fun z => m.polarField θ z (dIdx i)) =
        fun z => (m.logRate θ z i.succ).im - (m.logRate θ z 0).im := by
      funext z; exact polarField_dIdx m θ z i
    rw [hfun]
    have h := (imCLM.hasFDerivAt.comp _ (hasFDerivAt_logRate (m := m) θ i.succ)).sub
      (imCLM.hasFDerivAt.comp _ (hasFDerivAt_logRate (m := m) θ 0))
    have hD : PiLp.proj 2 (fun _ : Fin (n + (n + 1)) => ℝ) (dIdx i) ∘L m.jacCLM θ =
        imCLM ∘L m.dLog θ i.succ - imCLM ∘L m.dLog θ 0 :=
      ContinuousLinearMap.ext fun y => by simp
    rw [hD]
    exact h
  · have hfun : (fun z => m.polarField θ z (wIdx k)) = fun z => (m.logRate θ z k).re := by
      funext z; exact polarField_wIdx m θ z k
    rw [hfun]
    have h := reCLM.hasFDerivAt.comp _ (hasFDerivAt_logRate (m := m) θ k)
    have hD : PiLp.proj 2 (fun _ : Fin (n + (n + 1)) => ℝ) (wIdx k) ∘L m.jacCLM θ =
        reCLM ∘L m.dLog θ k :=
      ContinuousLinearMap.ext fun y => by simp
    rw [hD]
    exact h

@[tmio M, powerlib_domain] theorem fderiv_polarField :
    fderiv ℝ (m.polarField θ) 0 =
      Matrix.toEuclideanCLM (n := Fin (n + (n + 1))) (𝕜 := ℝ) (m.jacobian θ) := by
  rw [toEuclideanCLM_jacobian, (hasFDerivAt_polarField θ).fderiv]

/-! ## The reduced Jacobian is Hurwitz under a dissipative coupling -/

open Matrix in
/-- A Lyapunov bilinear form, symmetric, positive and strictly dissipated by `A`, makes `A` Hurwitz
(`Criteria.re_neg_of_lyapunov` with the Gram matrix of the form). -/
@[tmio T, powerlib_foundation] private theorem isHurwitz_of_bilin {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (B : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] ℝ)
    (hsymm : ∀ w w', B w w' = B w' w) (hpos : ∀ w, w ≠ 0 → 0 < B w w)
    (hdiss : ∀ w, w ≠ 0 → B w (A *ᵥ w) < 0) : LinearSystems.IsHurwitz A := by
  set P := LinearMap.toMatrix₂' ℝ B
  have hPv : ∀ w w', w ⬝ᵥ (P *ᵥ w') = B w w' := fun w w' => by
    rw [← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']
  have hP : P.transpose = P := by
    ext i j
    simp only [Matrix.transpose_apply, P, LinearMap.toMatrix₂'_apply]
    exact hsymm _ _
  intro μ v hv heig
  have := Criteria.re_neg_of_lyapunov hP (fun w hw => by rw [hPv]; exact hpos w hw)
    (fun w hw => by rw [hPv]; exact hdiss w hw) hv heig
  simpa using this

variable (m) in
/-- The complex image `ξ_k = s_k (ρ_k + j δ̃_k)` of a real reduced vector. -/
def xi (w : Fin (n + (n + 1)) → ℝ) (k : Fin (n + 1)) : ℂ :=
  m.profile θ k * ((w (wIdx k) : ℂ) + (ground (fun i => w (dIdx i)) k : ℂ) * I)

@[tmio M, powerlib_domain] private theorem xi_add (w w' : Fin (n + (n + 1)) → ℝ) :
    m.xi θ (w + w') = m.xi θ w + m.xi θ w' := by
  funext k
  simp only [xi, Pi.add_apply]
  refine Fin.cases ?_ (fun i => ?_) k
  · simp only [ground_zero]; push_cast; ring
  · simp only [ground_succ]; push_cast; ring

@[tmio M, powerlib_domain] private theorem xi_smul (a : ℝ) (w : Fin (n + (n + 1)) → ℝ) :
    m.xi θ (a • w) = fun k => (a : ℂ) * m.xi θ w k := by
  funext k
  simp only [xi, Pi.smul_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun i => ?_) k
  · simp only [ground_zero]; push_cast; ring
  · simp only [ground_succ]; push_cast; ring

@[tmio M, powerlib_domain] private theorem proj_add' (v v' : Fin (n + 1) → ℂ) :
    m.proj θ (v + v') = m.proj θ v + m.proj θ v' := by
  simp only [proj, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]

@[tmio M, powerlib_domain] private theorem proj_smul' (a : ℝ) (v : Fin (n + 1) → ℂ) :
    m.proj θ (fun k => (a : ℂ) * v k) = a * m.proj θ v := by
  simp only [proj, Finset.mul_sum, mul_div_assoc']
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

@[tmio M, powerlib_domain] private theorem err_add' (v v' : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    m.err θ (v + v') k = m.err θ v k + m.err θ v' k := by
  simp only [err, proj_add', Pi.add_apply]; ring

@[tmio M, powerlib_domain] private theorem err_smul' (a : ℝ) (v : Fin (n + 1) → ℂ)
    (k : Fin (n + 1)) : m.err θ (fun k => (a : ℂ) * v k) k = a * m.err θ v k := by
  simp only [err, proj_smul']; ring

variable (m) in
/-- The Lyapunov form `B(w, w') = Re z(ξ) Re z(ξ') + c ∑ₖ Re(ū_k(ξ) u_k(ξ'))` on reduced vectors
(`ξ = xi w`, `z = proj`, `u = err`). -/
def lyapForm (c : ℝ) (w w' : Fin (n + (n + 1)) → ℝ) : ℝ :=
  (m.proj θ (m.xi θ w)).re * (m.proj θ (m.xi θ w')).re +
    c * ∑ k, (conj (m.err θ (m.xi θ w) k) * m.err θ (m.xi θ w') k).re

@[tmio M, powerlib_domain] private theorem lyapForm_symm (c : ℝ) (w w' : Fin (n + (n + 1)) → ℝ) :
    m.lyapForm θ c w w' = m.lyapForm θ c w' w := by
  simp only [lyapForm]
  congr 1
  · ring
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]

variable (m) in
/-- The Lyapunov form as a bilinear map. -/
def lyapBilin (c : ℝ) :
    (Fin (n + (n + 1)) → ℝ) →ₗ[ℝ] (Fin (n + (n + 1)) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (m.lyapForm θ c)
    (fun w₁ w₂ w' => by
      simp only [lyapForm, xi_add, proj_add', Complex.add_re, err_add', map_add, add_mul,
        Finset.sum_add_distrib]
      ring)
    (fun a w w' => by
      simp only [lyapForm, xi_smul, proj_smul', Complex.re_ofReal_mul, err_smul', map_mul,
        Complex.conj_ofReal, smul_eq_mul]
      simp only [mul_assoc, Complex.re_ofReal_mul, ← Finset.mul_sum]
      ring)
    (fun w w₁ w₂ => by
      simp only [lyapForm, xi_add, proj_add', Complex.add_re, err_add', mul_add,
        Finset.sum_add_distrib]
      ring)
    (fun a w w' => by
      simp only [lyapForm, xi_smul, proj_smul', Complex.re_ofReal_mul, err_smul', smul_eq_mul]
      simp only [mul_left_comm _ (a : ℂ), Complex.re_ofReal_mul, ← Finset.mul_sum]
      ring)

@[tmio M, powerlib_domain] private theorem logCoord_toLp (w : Fin (n + (n + 1)) → ℝ)
    (k : Fin (n + 1)) : logCoord k (WithLp.toLp 2 w) =
      (w (wIdx k) : ℂ) + (ground (fun i => w (dIdx i)) k : ℂ) * I := by
  rw [logCoord_apply, Network.Swing.angleMap_eq_ground]
  rfl

/-- The linearized rate is the coupling of the complex image: `Λ_k s_k = K^θ_k ξ_k − (L ξ)_k`. -/
@[tmio M, powerlib_domain] private theorem rate_mul_profile (hv : ∀ k, 0 < m.vstar k)
    (w : Fin (n + (n + 1)) → ℝ) (k : Fin (n + 1)) :
    m.rate θ k (WithLp.toLp 2 w) * m.profile θ k =
      m.angleGain θ k * m.xi θ w k - m.lap (m.xi θ w) k := by
  have hs := profile_ne_zero hv θ k
  simp only [rate, FunLike.coe_sum, Finset.sum_apply, smul_apply, sub_apply, logCoord_toLp,
    smul_eq_mul, Finset.sum_mul, angleGain, lap, xi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem coupling_xi (hv : ∀ k, 0 < m.vstar k)
    (w : Fin (n + (n + 1)) → ℝ) (k : Fin (n + 1)) :
    m.angleGain θ k * m.xi θ w k - m.lap (m.xi θ w) k =
      m.angleGain θ k * m.err θ (m.xi θ w) k - m.lap (m.err θ (m.xi θ w)) k := by
  have hsplit := err_add_proj (m := m) θ (m.xi θ w)
  have hl : m.lap (m.xi θ w) k = m.lap (m.err θ (m.xi θ w)) k +
      m.proj θ (m.xi θ w) * m.lap (m.profile θ) k := by
    rw [← lap_add_mul]; congr 1
  rw [hl, ← angleGain_mul_profile hv]
  conv_lhs => rw [show m.xi θ w k = m.err θ (m.xi θ w) k + m.proj θ (m.xi θ w) * m.profile θ k
    by simp [err]]
  ring

/-- **The Jacobian in the complex image**:
`ξ(J w)_k = η (K^θ_k ξ_k − (L ξ)_k) − α ρ_k s_k − j R s_k`,
`R = Im(η Λ₀)` the common rotation removed by the grounding. -/
@[tmio M, powerlib_domain] private theorem xi_jacobian (hv : ∀ k, 0 < m.vstar k)
    (w : Fin (n + (n + 1)) → ℝ) (k : Fin (n + 1)) :
    m.xi θ (Matrix.mulVec (m.jacobian θ) w) k =
      (m.η : ℂ) * (m.angleGain θ k * m.xi θ w k - m.lap (m.xi θ w) k) -
        ((m.α * w (wIdx k) : ℝ) : ℂ) * m.profile θ k -
          ((((m.η : ℂ) * m.rate θ 0 (WithLp.toLp 2 w)).im : ℝ) : ℂ) * I * m.profile θ k := by
  have hJ : Matrix.mulVec (m.jacobian θ) w = WithLp.ofLp (m.jacCLM θ (WithLp.toLp 2 w)) := by
    rw [← toEuclideanCLM_jacobian (m := m), Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_toLp]
  have hdl : ∀ j, m.dLog θ j (WithLp.toLp 2 w) =
      (m.η : ℂ) * m.rate θ j (WithLp.toLp 2 w) - ((m.α * w (wIdx j) : ℝ) : ℂ) := fun j => by
    simp [dLog]
  have hre : ∀ z : ℂ, (z.re : ℂ) = z - (z.im : ℂ) * I := fun z => by
    apply Complex.ext <;> simp
  rw [← rate_mul_profile θ hv w k]
  simp only [xi, hJ]
  refine Fin.cases ?_ (fun i => ?_) k
  · change m.profile θ 0 * (((m.jacCLM θ (WithLp.toLp 2 w)) (wIdx 0) : ℂ) + (0 : ℝ) * I) = _
    rw [jacCLM_wIdx, hdl, hre]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.ofReal_zero, zero_mul,
      add_zero]
    ring
  · change m.profile θ i.succ * (((m.jacCLM θ (WithLp.toLp 2 w)) (wIdx i.succ) : ℂ) +
      ((m.jacCLM θ (WithLp.toLp 2 w)) (dIdx i) : ℂ) * I) = _
    rw [jacCLM_wIdx, jacCLM_dIdx, hdl, hdl, hre]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    push_cast
    ring

/-- A reduced vector whose image has no profile component in the real direction and no phase
error is zero (the grounding `δ̃₀ = 0` removes the rotation). -/
@[tmio M, powerlib_domain] private theorem eq_zero_of_xi (hv : ∀ k, 0 < m.vstar k)
    {w : Fin (n + (n + 1)) → ℝ} (hX : (m.proj θ (m.xi θ w)).re = 0)
    (hE : ∀ k, m.err θ (m.xi θ w) k = 0) : w = 0 := by
  set ζ := m.proj θ (m.xi θ w)
  have hk : ∀ k, (w (wIdx k) : ℂ) + (ground (fun i => w (dIdx i)) k : ℂ) * I = ζ := by
    intro k
    have h := hE k
    simp only [err, xi, sub_eq_zero] at h
    exact mul_left_cancel₀ (profile_ne_zero hv θ k) (h.trans (mul_comm _ _))
  have h0 := hk 0
  simp only [ground_zero, Complex.ofReal_zero, zero_mul, add_zero] at h0
  have hζ : ζ = 0 := by
    apply Complex.ext
    · simpa using hX
    · rw [← h0]; simp
  funext r
  refine Fin.addCases (fun i => ?_) (fun k => ?_) r
  · have h := congrArg Complex.im (hk i.succ)
    simp [hζ] at h
    exact h
  · have h := congrArg Complex.re (hk k)
    simp [hζ] at h
    exact h

/-- **The reduced Jacobian is Hurwitz** when the coupling is dissipative at a rate `μ > 0` off the
profile and `η, α > 0` (no relation between `ημ` and `α` is needed locally): the Lyapunov form
`(Re z)² + c ‖u‖²` with `c = (η C₁/‖s‖²)²/(αημ) + 1` decreases strictly. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem isHurwitz_jacobian_of_dissipative (hv : ∀ k, 0 < m.vstar k)
    (hη : 0 < m.η) (hα : 0 < m.α) {μ : ℝ} (hμ : 0 < μ) (hd : m.Dissipative θ μ) :
    LinearSystems.IsHurwitz (m.jacobian θ) := by
  have hM := mass_pos (m := m) hv
  have hC : 0 ≤ m.remConst θ := Finset.sum_nonneg fun k _ => mul_nonneg (hv k).le
    (add_nonneg (norm_nonneg _) (mul_nonneg zero_le_two (Finset.sum_nonneg fun j _ =>
      abs_nonneg _)))
  set b := m.η * m.remConst θ / m.mass with hb
  have hb0 : 0 ≤ b := div_nonneg (mul_nonneg hη.le hC) hM.le
  set c := b ^ 2 / (m.α * (m.η * μ)) + 1 with hc
  have hημ : 0 < m.η * μ := mul_pos hη hμ
  have hc0 : 0 < c := by positivity
  have hcημ : c * (m.η * μ) = b ^ 2 / m.α + m.η * μ := by
    rw [hc]; field_simp
  refine isHurwitz_of_bilin (m.lyapBilin θ c) (lyapForm_symm θ c) (fun w hw => ?_) (fun w hw => ?_)
  · -- positivity
    change 0 < m.lyapForm θ c w w
    simp only [lyapForm]
    have hsq : ∀ k, (conj (m.err θ (m.xi θ w) k) * m.err θ (m.xi θ w) k).re =
        ‖m.err θ (m.xi θ w) k‖ ^ 2 := fun k => by
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [hsq]
    by_contra hneg
    push Not at hneg
    have hE0 : ∑ k, ‖m.err θ (m.xi θ w) k‖ ^ 2 = 0 := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖m.err θ (m.xi θ w) k‖
      nlinarith [sq_nonneg (m.proj θ (m.xi θ w)).re]
    have hX0 : (m.proj θ (m.xi θ w)).re = 0 := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖m.err θ (m.xi θ w) k‖
      nlinarith [sq_nonneg (m.proj θ (m.xi θ w)).re]
    have hEk : ∀ k, m.err θ (m.xi θ w) k = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hE0 k
        (Finset.mem_univ k)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    exact hw (eq_zero_of_xi θ hv hX0 hEk)
  · -- dissipation
    change m.lyapForm θ c w (Matrix.mulVec (m.jacobian θ) w) < 0
    set ξ := m.xi θ w
    set ζ := m.proj θ ξ
    set e := m.err θ ξ
    set ξ' := m.xi θ (Matrix.mulVec (m.jacobian θ) w)
    set R : ℝ := ((m.η : ℂ) * m.rate θ 0 (WithLp.toLp 2 w)).im
    set A := ∑ k, conj (m.profile θ k) * (m.angleGain θ k * e k - m.lap e k)
    set E := ∑ k, ‖e k‖ ^ 2
    have hξ' : ∀ k, ξ' k = (m.η : ℂ) * (m.angleGain θ k * e k - m.lap e k) -
        ((m.α * w (wIdx k) : ℝ) : ℂ) * m.profile θ k - (R : ℂ) * I * m.profile θ k := by
      intro k
      rw [show ξ' k = _ from xi_jacobian θ hv w k, coupling_xi θ hv w k]
    have hρ : ∀ k, m.vstar k ^ 2 * w (wIdx k) = (conj (m.profile θ k) * ξ k).re := by
      intro k
      simp only [ξ, xi]
      rw [← mul_assoc, conj_profile_mul, Complex.re_ofReal_mul]
      simp
    have hsumξ : ∑ k, conj (m.profile θ k) * ξ k = ζ * m.mass := by
      simp only [ζ, proj]
      exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hM.ne')).symm
    have he0 : ∑ k, conj (m.profile θ k) * e k = 0 := sum_conj_profile_err (m := m) hM.ne' θ ξ
    have hes : ∑ k, conj (e k) * m.profile θ k = 0 :=
      sum_conj_err_mul_profile (m := m) hM.ne' θ ξ
    -- the profile component of `J w`
    have hX : ∑ k, m.vstar k ^ 2 * w (wIdx k) = ζ.re * m.mass := by
      simp only [hρ, ← Complex.re_sum, hsumξ, Complex.re_mul_ofReal]
    have hζ' : (m.proj θ ξ').re = m.η * A.re / m.mass - m.α * ζ.re := by
      have hterm : ∀ k, conj (m.profile θ k) * ξ' k =
          (m.η : ℂ) * (conj (m.profile θ k) * (m.angleGain θ k * e k - m.lap e k)) -
            ((m.α * (m.vstar k ^ 2 * w (wIdx k)) : ℝ) : ℂ) -
              (R : ℂ) * I * ((m.vstar k ^ 2 : ℝ) : ℂ) := by
        intro k
        have hcs := conj_profile_mul (m := m) θ k
        rw [hξ']
        push_cast at hcs ⊢
        linear_combination (-((m.α : ℂ) * (w (wIdx k) : ℂ) + (R : ℂ) * I)) * hcs
      have hs : ∑ k, conj (m.profile θ k) * ξ' k = (m.η : ℂ) * A -
          ((m.α * (ζ.re * m.mass) : ℝ) : ℂ) - (R : ℂ) * I * (m.mass : ℂ) := by
        simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum, hX]
        rfl
      simp only [proj, hs]
      rw [Complex.div_ofReal_re]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      field_simp
    -- the phase error of `J w`
    have he' : ∑ k, (conj (e k) * m.err θ ξ' k).re ≤ -(m.η * μ) * E := by
      have hsplit : ∑ k, (conj (e k) * m.err θ ξ' k).re = ∑ k, (conj (e k) * ξ' k).re := by
        simp only [err, mul_sub, Complex.sub_re, Finset.sum_sub_distrib]
        have : ∑ k, (conj (e k) * (m.proj θ ξ' * m.profile θ k)).re = 0 := by
          rw [← Complex.re_sum]
          rw [show ∑ k, conj (e k) * (m.proj θ ξ' * m.profile θ k) =
            m.proj θ ξ' * ∑ k, conj (e k) * m.profile θ k by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hes]
          simp
        rw [this, sub_zero]
      rw [hsplit]
      have hk : ∀ k, (conj (e k) * ξ' k).re = m.η * (conj (e k) *
          (m.angleGain θ k * e k - m.lap e k)).re - m.α * (w (wIdx k) *
            (conj (e k) * m.profile θ k).re) - R * (I * (conj (e k) * m.profile θ k)).re := by
        intro k
        have h : conj (e k) * ξ' k =
            (m.η : ℂ) * (conj (e k) * (m.angleGain θ k * e k - m.lap e k)) -
              ((m.α * w (wIdx k) : ℝ) : ℂ) * (conj (e k) * m.profile θ k) -
                (R : ℂ) * (I * (conj (e k) * m.profile θ k)) := by
          rw [hξ']; ring
        rw [h, Complex.sub_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
          Complex.re_ofReal_mul]
        ring
      simp only [hk, Finset.sum_sub_distrib, ← Finset.mul_sum]
      -- the rotation does no work
      have hrot : ∑ k, (I * (conj (e k) * m.profile θ k)).re = 0 := by
        rw [← Complex.re_sum, ← Finset.mul_sum, hes, mul_zero, Complex.zero_re]
      -- the amplitude term is nonnegative
      have hamp : 0 ≤ ∑ k, w (wIdx k) * (conj (e k) * m.profile θ k).re := by
        have hk2 : ∀ k, w (wIdx k) * (conj (e k) * m.profile θ k).re =
            ((conj (e k) * m.profile θ k).re) ^ 2 / m.vstar k ^ 2 +
              ζ.re * (conj (e k) * m.profile θ k).re := by
          intro k
          have hv2 : m.vstar k ^ 2 ≠ 0 := pow_ne_zero 2 (hv k).ne'
          set B := (conj (e k) * m.profile θ k).re
          have hξk : ξ k = e k + ζ * m.profile θ k := by simp [e, err, ζ]
          have hc : (conj (m.profile θ k) * e k).re = B := by
            simp only [B]
            rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
          have h1 : m.vstar k ^ 2 * w (wIdx k) = B + ζ.re * m.vstar k ^ 2 := by
            rw [hρ k, hξk, mul_add, Complex.add_re, hc,
              show conj (m.profile θ k) * (ζ * m.profile θ k) =
                ζ * (conj (m.profile θ k) * m.profile θ k) by ring,
              conj_profile_mul, Complex.re_mul_ofReal]
          have h2 : w (wIdx k) = B / m.vstar k ^ 2 + ζ.re := by
            rw [div_add' _ _ _ hv2, eq_div_iff hv2]
            linarith
          rw [h2]
          ring
        simp only [hk2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum, hes,
          Complex.zero_re, mul_zero, add_zero]
        exact Finset.sum_nonneg fun k _ => by positivity
      have hdk := hd e he0
      have := mul_le_mul_of_nonneg_left hdk hη.le
      rw [hrot]
      nlinarith [mul_nonneg hα.le hamp]
    -- the coupling bound
    have hA : |A.re| ≤ m.remConst θ * Real.sqrt E :=
      (Complex.abs_re_le_norm _).trans (norm_sum_conj_profile_coupling_le hv θ e)
    -- assemble
    simp only [lyapForm]
    rw [hζ']
    have hE0 : 0 ≤ E := Finset.sum_nonneg fun k _ => sq_nonneg _
    set Y := Real.sqrt E
    have hY : Y ^ 2 = E := Real.sq_sqrt hE0
    have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
    set X := ζ.re
    have hXA : X * (m.η * A.re / m.mass) ≤ b * |X| * Y := by
      have h1 : X * (m.η * A.re / m.mass) ≤ |X| * (m.η * |A.re| / m.mass) := by
        rw [show X * (m.η * A.re / m.mass) = (m.η / m.mass) * (X * A.re) by ring,
          show |X| * (m.η * |A.re| / m.mass) = (m.η / m.mass) * |X * A.re| by
            rw [abs_mul]; ring]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (div_nonneg hη.le hM.le)
      have h2 : |X| * (m.η * |A.re| / m.mass) ≤ |X| * (m.η * (m.remConst θ * Y) / m.mass) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA hη.le) hM.le) (abs_nonneg _)
      have h3 : |X| * (m.η * (m.remConst θ * Y) / m.mass) = b * |X| * Y := by
        rw [hb]; ring
      linarith
    have hcE := mul_le_mul_of_nonneg_left he' hc0.le
    have hfin : X * (m.η * A.re / m.mass - m.α * X) + c * ∑ k, (conj (e k) * m.err θ ξ' k).re ≤
        -(m.α * X ^ 2) + b * |X| * Y - (b ^ 2 / m.α + m.η * μ) * Y ^ 2 := by
      rw [hY, ← hcημ]
      nlinarith
    refine lt_of_le_of_lt hfin ?_
    -- the quadratic form is negative definite
    have hsq : -(m.α * X ^ 2) + b * |X| * Y - (b ^ 2 / m.α + m.η * μ) * Y ^ 2 =
        -(m.α * (|X| - b / (2 * m.α) * Y) ^ 2) - (3 * b ^ 2 / (4 * m.α)) * Y ^ 2 -
          m.η * μ * Y ^ 2 := by
      have := hα.ne'
      rw [← sq_abs X]
      field_simp
      ring
    rw [hsq]
    by_cases hY' : Y = 0
    · have hE : E = 0 := by rw [← hY, hY']; ring
      have hX : X ≠ 0 := by
        intro hX
        have hEk : ∀ k, e k = 0 := fun k => by
          have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hE k
            (Finset.mem_univ k)
          exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
        exact hw (eq_zero_of_xi θ hv hX hEk)
      rw [hY']
      have : 0 < |X| := abs_pos.mpr hX
      have : 0 < m.α * |X| ^ 2 := by positivity
      nlinarith
    · have hYp : 0 < Y := lt_of_le_of_ne hY0 (Ne.symm hY')
      have : 0 < m.η * μ * Y ^ 2 := by positivity
      have : 0 ≤ m.α * (|X| - b / (2 * m.α) * Y) ^ 2 := by positivity
      have : 0 ≤ 3 * b ^ 2 / (4 * m.α) * Y ^ 2 := by positivity
      linarith

/-! ## The family -/

/-- A dVOC network read about a selected angle profile `θ*`. -/
structure Model (n : ℕ) where
  /-- The units, the network and the set-points. -/
  net : DVOC (Fin (n + 1))
  /-- The selected angle profile `θ*` (the synchronous set `T` it defines). -/
  θ : Fin (n + 1) → ℝ

namespace Model

variable (x : Model n)

/-- The reduced log-polar field about the selected profile; the selected synchronous state is the
origin. -/
def field (z : State (n + (n + 1))) : State (n + (n + 1)) := x.net.polarField x.θ z

/-- Stability condition: the profile is a relative equilibrium and the reduced Jacobian is
Hurwitz. -/
def Stable : Prop := x.net.Synchronous x.θ ∧ LinearSystems.IsHurwitz (x.net.jacobian x.θ)

/-- Instability condition: the profile is a relative equilibrium and the reduced Jacobian has a
characteristic root in the open right half plane. -/
def Unstable : Prop :=
  x.net.Synchronous x.θ ∧ ∃ s : ℂ,
    (Linear.characteristicMatrix (x.net.jacobian x.θ) s).det = 0 ∧ 0 < s.re

end Model

/-- The dVOC-network family: each model read as its reduced log-polar field about the selected
profile (`Spectral.localFamily`). -/
def family : Family (Model n) Spectral.Requirement (n + (n + 1)) 0 :=
  Spectral.localFamily Model.field Model.Stable Model.Unstable

@[tmio M, powerlib_domain] theorem family_isAutonomous :
    (family (n := n)).IsAutonomous Model.field :=
  Spectral.localFamily_isAutonomous _ _ _

/-- Every translation of the dVOC-network family is sound: a Hurwitz reduced Jacobian at a relative
equilibrium gives local exponential stability (linearization), a right-half-plane root
instability. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, (family (n := n)).chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun x hS => ?_) (fun x hU => ?_)
  · exact hurwitz_linearization_locally_exponentially_stable (x.net.jacobian x.θ)
      (polarField_contDiff x.θ) ((polarField_zero_iff x.θ).mpr hS.1) (fderiv_polarField x.θ) hS.2
  · obtain ⟨hsync, s, hs, hre⟩ := hU
    exact Dynamics.unstable_of_characteristic_root_re_pos (x.net.jacobian x.θ)
      (polarField_contDiff x.θ) ((polarField_zero_iff x.θ).mpr hsync) (fderiv_polarField x.θ) hs hre

/-- **Local exponential stability of the synchronous set, exact.** A dVOC network is locally
exponentially stable at its selected profile — in the reduced coordinates, i.e. transversally to
the common rotation: magnitudes at their set-points, relative angles at `θ*` — exactly when the
profile is a relative equilibrium (`Synchronous`; consistent set-points give it) and the reduced
Jacobian is Hurwitz (converse linearization). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (x : Model n) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable) ↔ x.Stable) := by
  have h := family_isAutonomous.mem_den_flow (P := .locallyExponentiallyStable) (x := x)
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  change LocallyExponentiallyStable (x.net.polarField x.θ) 0 ↔ _
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (polarField_contDiff x.θ)
    (fderiv_polarField x.θ), polarField_zero_iff]
  rfl

/-- The local exponential translation of the dVOC-network family is exact. -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% ((family (n := n)).Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_exact_locallyExponentiallyStable fun x => ?_
  have h := mem_den_locallyExponentiallyStable_iff x
  unfold powerlib.TMIO.Statement at h
  exact h.symm.trans family_isAutonomous.mem_den_flow

/-- **A dissipative coupling makes the synchronous set locally exponentially stable**: at a relative
equilibrium profile, with `η, α > 0` and a coupling dissipative at any rate `μ > 0` off the profile
(`isHurwitz_jacobian_of_dissipative`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_dissipative
    (x : Model n) (hv : ∀ k, 0 < x.net.vstar k) (hη : 0 < x.net.η) (hα : 0 < x.net.α) {μ : ℝ}
    (hμ : 0 < μ) (hd : x.net.Dissipative x.θ μ) (hsync : x.net.Synchronous x.θ) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_iff x
  unfold powerlib.TMIO.Statement at h ⊢
  exact h.mpr ⟨hsync, isHurwitz_jacobian_of_dissipative x.θ hv hη hα hμ hd⟩

/-- **Colombino et al. Condition 1 gives local exponential stability**: consistent set-points,
symmetric weights, angles within `[0, π/2]` of a reference unit and (29) with `η, α > 0`
(`dissipative_of_condition`; the rate `μ > α/η > 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_condition
    (x : Model n) (hv : ∀ k, 0 < x.net.vstar k) (hw : ∀ j k, x.net.w j k = x.net.w k j)
    (hpf : x.net.PowerFlow x.θ) (r : Fin (n + 1))
    (hθ : ∀ k, 0 ≤ x.θ k - x.θ r ∧ x.θ k - x.θ r ≤ Real.pi / 2) {vmin vmax lam : ℝ}
    (hb : (∀ k, vmin ≤ x.net.vstar k ∧ x.net.vstar k ≤ vmax) ∧ 0 < vmin ∧ 0 ≤ lam)
    (hlam : ∀ y : Fin (n + 1) → ℝ, lam * ∑ k, (y k - (∑ j, y j) / Fintype.card (Fin (n + 1))) ^ 2 ≤
      (∑ j, ∑ k, x.net.w j k * (y j - y k) ^ 2) / 2) (hη : 0 < x.net.η) (hα : 0 < x.net.α)
    (hcond : ∀ k, ∑ j, x.net.w j k * (1 - x.net.vstar j / x.net.vstar k *
      Real.cos (x.θ j - x.θ k)) + x.net.α / x.net.η < vmin ^ 2 / vmax ^ 2 * lam / 2) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨μ, hμ, hd⟩ := dissipative_of_condition hv hw r hθ (fun k => (hb.1 k).1)
    (fun k => (hb.1 k).2) hb.2.1 hb.2.2 hlam hη hcond
  have hμ0 : 0 < μ := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hη.le]
  exact mem_den_locallyExponentiallyStable_of_dissipative x hv hη hα hμ0 hd
    (synchronous_of_balanced x.θ ((balanced_zero_iff_powerFlow hv x.θ).mpr hpf))

/-- **Beyond Condition 1**: the two units on one line with `v* = (1, 2)` (`twoUnequal`), for which
(29) fails for every gain and angle profile (`twoUnequal_not_condition`), are locally exponentially
stable at the in-phase profile whenever it is a relative equilibrium and `η, α > 0` (the coupling is
dissipative at the rate `13/10`, `twoUnequal_dissipative`). -/
@[tmio TM, powerlib_domain] theorem twoUnequal_mem_den_locallyExponentiallyStable (κ η α ω0 : ℝ)
    (p q : Fin 2 → ℝ) (hη : 0 < η) (hα : 0 < α)
    (hsync : (twoUnequal κ η α ω0 p q).Synchronous 0) :
    connection% ((⟨twoUnequal κ η α ω0 p q, 0⟩ : Model 1) ∈
      family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_locallyExponentiallyStable_of_dissipative ⟨twoUnequal κ η α ω0 p q, 0⟩
    (fun k => by fin_cases k <;> simp [twoUnequal]) hη hα (by norm_num)
    (twoUnequal_dissipative κ η α ω0 p q) hsync

end DVOC
end powerlib.GFM
