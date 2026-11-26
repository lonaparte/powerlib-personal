import theorem.GridTiedConverter.GFM.DCLink.VSMDCHopf
import theorem.Dynamics.HopfCycleAmplitude

/-! # The VSM–DC model with its DC-voltage loop: Hopf cycles at the two Hopf witnesses

Domain module.

Model boundary.
* The VSM–DC family `VSMDC.family` of `theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`, on the
  slice `hopfModel M D C A I_s K_p K_i` of `theorem/GridTiedConverter/GFM/DCLink/VSMDCHopf.lean`
  (state `(δ, ω, V, ζ)` translated to the point `(0, 0, 1, 0)`; `c₀ = α = P_ff = 0`, `P_s = −I_s`,
  `V* = 1`; quasi-static line, affine DC source, DC node `C V̇ = (P_src(V) − P_e(δ))/V`, DC-voltage
  PI loop on the power reference; continuous time, autonomous; export-positive power), at the two
  Hopf witnesses `hopfSup`, `hopfSub`, unfolded in the damping: the parameter `μ` replaces `D` by
  `D + μ` (`VSMDC.hopfDampFamily`). Every model of the slice is balanced at the same point, so the
  family keeps the origin as an equilibrium.
* The field contains `1/V`: the augmented field `(z, μ) ↦ (F(z, μ), 0)` is smooth (analytic) on
  `V = 1 + z₂ > 0`, not globally; the cycles are those of the local Hopf law
  `Dynamics.HopfCycle.exists_hopfCycle_local` and stay in `V > 0`.
* Level: periodic orbits of the family. They are not sentences of `VSMDC.family`, so the
  conclusions on the model are private evidence; no new family, no connection conclusion.
  Every small cycle (`Dynamics.HopfCycle.periodic_amplitude_local`): no small cycle on the other
  side of the boundary; amplitude `(1 ± η) ν`. Uniqueness and orbital stability of the cycles are
  not proved.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3, the
transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`); the critical pairs and `ℓ₁` of
`theorem/GridTiedConverter/GFM/DCLink/VSMDCHopf.lean`. The transversality coefficients were
computed with SymPy (rational arithmetic, cross-checked by implicit differentiation of the
characteristic polynomial; untrusted) and are checked by the kernel.

Results.
* `VSMDC.hopfDampFamily`, `VSMDC.hopfDampJac` (`∂J/∂D = −(1/M) e₁e₁ᵀ`);
  `hopfDampFamily_zero_param` (at `μ = 0` the family is the slice field), `hopfDampFamily_origin`,
  `hopfJac_damp`, `fderiv_hopfDampFamily`, `hasDerivAt_fderiv_hopfDampFamily` (the Jacobian is
  affine in `μ` with slope `∂J/∂D`).
* `paramTrace_hopfSup`: the transversality coefficient along the damping at `hopfSup` is
  `τ = −1/2`; `paramTrace_hopfSub`: at `hopfSub`, `τ = −1/4` (more damping moves the critical pair
  to the left).
* Private evidence `hopfSup_periodic_amplitude` (every small cycle has `μ < 0`, amplitude
  `(1 ± η) 25|μ|/2`) and `hopfSub_periodic_amplitude` (`μ > 0`, amplitude `(1 ± η) 85μ/32`).
* Private evidence `hopfSup_exists_hopfCycle`: `ℓ₁ = −1/25`, `τ = −1/2`: for every small `μ < 0`
  (damping just below `1`, the side to which the critical pair moves into the right half-plane)
  the family has a nonconstant periodic orbit in `V > 0` with
  `25|μ|/16 ≤ ‖critπ p z(t)‖² ≤ 100|μ|` (supercritical). Private evidence
  `hopfSub_exists_hopfCycle`: `ℓ₁ = 8/85`, `τ = −1/4`: for every small `μ > 0` (damping just
  above `2`, the side to which the critical pair moves into the left half-plane) a nonconstant
  periodic orbit in `V > 0` with `85μ/256 ≤ ‖critπ p z(t)‖² ≤ 85μ/4` (subcritical). With them
  the private evidence `contDiffAt_augField_hopfDampFamily` (the augmented field is analytic on
  `V > 0`).
-/

noncomputable section
namespace powerlib.GFM.DCLink
namespace VSMDC
open Complex Polynomial Filter Matrix
open powerlib.Dynamics (State)
open powerlib.Dynamics.HopfCycle (augField xpart mpart xin emu xin_apply_castSucc
  emu_apply_castSucc)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold (critπ critι critι_apply critπ_apply0 critπ_apply1 reV_apply
  imV_apply)
open powerlib.Dynamics.Degenerate.PlanarFocus (e0 e1 e0_apply0 e0_apply1 e1_apply0 e1_apply1)

variable (M D C A Is Kp Ki : ℝ)

/-- The translated slice field with the damping `D + μ`, as a family in `μ` (the operating point
does not depend on the damping). -/
def hopfDampFamily (z : State 4) (μ : ℝ) : State 4 := (hopfModel M (D + μ) C A Is Kp Ki).field z

/-- The parameter derivative of the slice Jacobian: `∂J/∂D = −(1/M) e₁ e₁ᵀ`. -/
def hopfDampJac : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, -(1 / M), 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[tmio M, powerlib_domain] theorem hopfDampFamily_zero_param (z : State 4) :
    hopfDampFamily M D C A Is Kp Ki z 0 = (hopfModel M D C A Is Kp Ki).field z := by
  simp [hopfDampFamily]

@[tmio M, powerlib_domain] private theorem hopfDampFamily_zero_fun :
    (fun z => hopfDampFamily M D C A Is Kp Ki z 0) = (hopfModel M D C A Is Kp Ki).field :=
  funext (hopfDampFamily_zero_param M D C A Is Kp Ki)

@[tmio M, powerlib_domain] theorem hopfDampFamily_origin (μ : ℝ) :
    hopfDampFamily M D C A Is Kp Ki 0 μ = 0 :=
  Model.hopfModel_field_zero M (D + μ) C A Is Kp Ki

@[tmio M, powerlib_domain] theorem hopfJac_damp (μ : ℝ) :
    hopfJac M (D + μ) C A Is Kp Ki = hopfJac M D C A Is Kp Ki + μ • hopfDampJac M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hopfJac, hopfDampJac]
  ring

@[tmio M, powerlib_domain] theorem fderiv_hopfDampFamily (μ : ℝ) :
    fderiv ℝ (fun z => hopfDampFamily M D C A Is Kp Ki z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfJac M D C A Is Kp Ki) +
        μ • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfDampJac M) := by
  show fderiv ℝ (hopfModel M (D + μ) C A Is Kp Ki).field 0 = _
  rw [Model.hopfModel_fderiv, hopfJac_damp, map_add, map_smul]

/-- **Transversality data**: `μ ↦ D_z F(0, μ)` is affine with slope `toEuclideanCLM (∂J/∂D)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_fderiv_hopfDampFamily :
    HasDerivAt (fun μ => fderiv ℝ (fun z => hopfDampFamily M D C A Is Kp Ki z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfDampJac M)) 0 := by
  simp only [fderiv_hopfDampFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfDampJac M))).const_add
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfJac M D C A Is Kp Ki))

/-- The augmented field of the family is analytic on `V = 1 + z₂ > 0`. -/
@[tmio M, powerlib_domain] private theorem contDiffAt_augField_hopfDampFamily
    {w : State (4 + 1)} (hw : 0 < w 2 + 1) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (augField (hopfDampFamily M D C A Is Kp Ki)) w := by
  have e : augField (hopfDampFamily M D C A Is Kp Ki) = fun w : State (4 + 1) => xin
      (WithLp.toLp 2 ![w 1, (Kp * w 2 + Ki * w 3 - A * Real.sin (w 0) - (D + w 4) * w 1) / M,
        (Is + (-Is - A * Real.sin (w 0)) / (w 2 + 1)) / C, w 2] : State 4) := by
    funext w
    simp only [augField, hopfDampFamily, Model.hopfModel_field]
    rfl
  rw [e]
  refine (xin (n := 4)).contDiff.contDiffAt.comp w ?_
  rw [contDiffAt_euclidean]
  intro i
  fin_cases i
  · simp
    fun_prop
  · simp
    fun_prop
  · simp
    have h1 : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun w : State (4 + 1) => -Is - A * Real.sin (w 0)) w := by fun_prop
    have h2 : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun w : State (4 + 1) => w 2 + 1) w := by fun_prop
    exact (contDiffAt_const.add (h1.div h2 hw.ne')).div_const _
  · simp
    fun_prop

@[tmio M, powerlib_domain] private theorem isOpen_posV :
    IsOpen {w : State (4 + 1) | 0 < w 2 + 1} :=
  isOpen_lt continuous_const
    ((Dynamics.contDiff_coord (n := 5) (k := 1) 2).continuous.add continuous_const)

@[tmio M, powerlib_domain] private theorem posV_iff (x : State 4) (μ : ℝ) :
    xin x + μ • emu ∈ {w : State (4 + 1) | 0 < w 2 + 1} ↔ 0 < x 2 + 1 := by
  show 0 < (xin x + μ • emu : State (4 + 1)) (Fin.castSucc 2) + 1 ↔ _
  rw [PiLp.add_apply, PiLp.smul_apply, xin_apply_castSucc, emu_apply_castSucc, smul_zero,
    add_zero]

/-! ## The supercritical witness -/

/-- **The transversality coefficient at `hopfSup`** along the damping:
`τ = tr (critπ p ∘ ∂J/∂D ∘ critι q) = 2 Re ⟨p, (∂J/∂D) q⟩ = −1/2`. -/
@[tmio M, powerlib_domain] theorem paramTrace_hopfSup :
    Dynamics.PlanarHopf.paramTrace ((critπ hopfSupP).comp
      ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfDampJac 1)).comp (critι hopfSupQ))) =
      -1 / 2 := by
  have hB : ∀ v : State 4, Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfDampJac 1) v =
      WithLp.toLp 2 ![0, -v 1, 0, 0] := by
    intro v
    ext i
    fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four, hopfDampJac]
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp [PiLp.inner_apply, Fin.sum_univ_four, hopfSupP, hopfSupQ]
  norm_num

/-- **Hopf cycles of `hopfSup`.** `ℓ₁ = −1/25`, `τ = −1/2`: for every small `μ < 0` the slice field
with the damping `1 + μ` has a nonconstant periodic orbit in `V > 0` whose critical coordinates
satisfy `25|μ|/16 ≤ ‖critπ p z(t)‖² ≤ 100|μ|` (`HopfCycle.exists_hopfCycle_local`). Private
evidence: periodic orbits are not sentences of the family. -/
@[tmio TM, powerlib_domain] private theorem hopfSup_exists_hopfCycle :
    ∃ δ > 0, ∀ μ, -δ < μ → μ < 0 →
      ∃ z : ℝ → State 4, ∃ T, 0 < T ∧
        (∀ t, HasDerivAt z (hopfDampFamily 1 1 1 1 (-1) 1 1 (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧ (∀ t, 0 < z t 2 + 1) ∧
        ∀ t, 25 * |μ| / 16 ≤ ‖critπ hopfSupP (z t)‖ ^ 2 ∧
          ‖critπ hopfSupP (z t)‖ ^ 2 ≤ 100 * |μ| := by
  have hfun : (fun z => hopfDampFamily 1 1 1 1 (-1) 1 1 z 0) = hopfSup.field :=
    hopfDampFamily_zero_fun 1 1 1 1 (-1) 1 1
  have hl : firstLyapunov (fun z => hopfDampFamily 1 1 1 1 (-1) 1 1 z 0) 0 1 hopfSupQ hopfSupP =
      -1 / 25 := by rw [hfun]; exact hopfSup_firstLyapunov
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle_local
    (F := hopfDampFamily 1 1 1 1 (-1) 1 1) (ω := 1) (q := hopfSupQ) (p := hopfSupP) isOpen_posV
    (by simp) (fun w hw => ((contDiffAt_augField_hopfDampFamily 1 1 1 1 (-1) 1 1 hw).of_le
      le_top).contDiffWithinAt)
    (contDiffAt_augField_hopfDampFamily 1 1 1 1 (-1) 1 1 (by simp)).analyticAt
    (hopfDampFamily_origin 1 1 1 1 (-1) 1 1) (by rw [hfun]; exact hopfSup_isCriticalPair)
    (by rw [hfun]; exact hopfSup_charpoly) hopfSup_r_roots
    (hasDerivAt_fderiv_hopfDampFamily 1 1 1 1 (-1) 1 1) (by rw [paramTrace_hopfSup]; norm_num)
    (by rw [hl]; norm_num)
  refine ⟨δ, hδ, fun μ h1 h2 => ?_⟩
  have hμ : |μ| < δ := by rw [abs_of_neg h2]; linarith
  obtain ⟨z, T, hT, hz, hzT, hznc, hU, hamp⟩ := hcyc μ hμ (by
    rw [paramTrace_hopfSup, hl]; linarith)
  refine ⟨z, T, hT, hz, hzT, hznc, fun t => (posV_iff _ _).mp (hU t), fun t => ?_⟩
  have h := hamp t
  rw [paramTrace_hopfSup, hl] at h
  have e : -(μ * (-1 / 2)) / (1 * (-1 / 25)) = 25 * |μ| / 2 := by rw [abs_of_neg h2]; ring
  rw [e] at h
  constructor <;> linarith [h.1, h.2]


/-- **Every small cycle of `hopfSup`.** For every `η > 0`, every nonconstant periodic orbit of the
slice field with the damping `1 + μ`, `|μ|` small, near the operating point has `μ < 0` (none at
or above the Hopf damping) and `(1 − η) 25|μ|/2 ≤ ‖critπ p z(t)‖² ≤ (1 + η) 25|μ|/2`
(`HopfCycle.periodic_amplitude_local`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem hopfSup_periodic_amplitude {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 4) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z (hopfDampFamily 1 1 1 1 (-1) 1 1 (z t) μ) t) →
      (∀ t, z (t + T) = z t) → (∃ t, z t ≠ z 0) → (∀ t, ‖z t‖ < δ) →
      μ < 0 ∧ ∀ t, (1 - η) * (25 * |μ| / 2) ≤ ‖critπ hopfSupP (z t)‖ ^ 2 ∧
        ‖critπ hopfSupP (z t)‖ ^ 2 ≤ (1 + η) * (25 * |μ| / 2) := by
  have hfun : (fun z => hopfDampFamily 1 1 1 1 (-1) 1 1 z 0) = hopfSup.field :=
    hopfDampFamily_zero_fun 1 1 1 1 (-1) 1 1
  have hl : firstLyapunov (fun z => hopfDampFamily 1 1 1 1 (-1) 1 1 z 0) 0 1 hopfSupQ hopfSupP =
      -1 / 25 := by rw [hfun]; exact hopfSup_firstLyapunov
  obtain ⟨δ, hδ, hamp⟩ := Dynamics.HopfCycle.periodic_amplitude_local
    (F := hopfDampFamily 1 1 1 1 (-1) 1 1) (ω := 1) (q := hopfSupQ) (p := hopfSupP) isOpen_posV
    (by simp) (fun w hw => ((contDiffAt_augField_hopfDampFamily 1 1 1 1 (-1) 1 1 hw).of_le
      le_top).contDiffWithinAt)
    (contDiffAt_augField_hopfDampFamily 1 1 1 1 (-1) 1 1 (by simp)).analyticAt
    (hopfDampFamily_origin 1 1 1 1 (-1) 1 1) (by rw [hfun]; exact hopfSup_isCriticalPair)
    (by rw [hfun]; exact hopfSup_charpoly) hopfSup_r_roots
    (hasDerivAt_fderiv_hopfDampFamily 1 1 1 1 (-1) 1 1) (by rw [paramTrace_hopfSup]; norm_num)
    (by rw [hl]; norm_num) hη
  refine ⟨δ, hδ, fun μ hμ z T hT hz hzT hnc hzδ => ?_⟩
  obtain ⟨hs, hbd⟩ := hamp μ hμ z T hT hz hzT hnc hzδ
  rw [paramTrace_hopfSup, hl] at hs hbd
  have hμ0 : μ < 0 := by linarith
  have e : -(μ * (-1 / 2)) / (1 * (-1 / 25)) = 25 * |μ| / 2 := by rw [abs_of_neg hμ0]; ring
  simp only [e] at hbd
  exact ⟨hμ0, hbd⟩

/-! ## The subcritical witness -/

/-- **The transversality coefficient at `hopfSub`** along the damping: `τ = −1/4`. -/
@[tmio M, powerlib_domain] theorem paramTrace_hopfSub :
    Dynamics.PlanarHopf.paramTrace ((critπ hopfSubP).comp
      ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfDampJac 2)).comp (critι hopfSubQ))) =
      -1 / 4 := by
  have hB : ∀ v : State 4, Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfDampJac 2) v =
      WithLp.toLp 2 ![0, -(v 1 / 2), 0, 0] := by
    intro v
    ext i
    fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four, hopfDampJac]
    ring
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp [PiLp.inner_apply, Fin.sum_univ_four, hopfSubP, hopfSubQ]
  norm_num

/-- **Hopf cycles of `hopfSub`.** `ℓ₁ = 8/85`, `τ = −1/4`: for every small `μ > 0` the slice field
with the damping `2 + μ` has a nonconstant periodic orbit in `V > 0` whose critical coordinates
satisfy `85μ/256 ≤ ‖critπ p z(t)‖² ≤ 85μ/4` (`HopfCycle.exists_hopfCycle_local`). Private
evidence: periodic orbits are not sentences of the family. -/
@[tmio TM, powerlib_domain] private theorem hopfSub_exists_hopfCycle :
    ∃ δ > 0, ∀ μ, 0 < μ → μ < δ →
      ∃ z : ℝ → State 4, ∃ T, 0 < T ∧
        (∀ t, HasDerivAt z (hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧ (∀ t, 0 < z t 2 + 1) ∧
        ∀ t, 85 * μ / 256 ≤ ‖critπ hopfSubP (z t)‖ ^ 2 ∧
          ‖critπ hopfSubP (z t)‖ ^ 2 ≤ 85 * μ / 4 := by
  have hfun : (fun z => hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) z 0) = hopfSub.field :=
    hopfDampFamily_zero_fun 2 2 2 2 (-1 / 2) 2 (1 / 2)
  have hl : firstLyapunov (fun z => hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) z 0) 0 1 hopfSubQ
      hopfSubP = 8 / 85 := by rw [hfun]; exact hopfSub_firstLyapunov
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle_local
    (F := hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2)) (ω := 1) (q := hopfSubQ) (p := hopfSubP)
    isOpen_posV (by simp) (fun w hw => ((contDiffAt_augField_hopfDampFamily 2 2 2 2 (-1 / 2) 2
      (1 / 2) hw).of_le le_top).contDiffWithinAt)
    (contDiffAt_augField_hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) (by simp)).analyticAt
    (hopfDampFamily_origin 2 2 2 2 (-1 / 2) 2 (1 / 2)) (by rw [hfun]; exact hopfSub_isCriticalPair)
    (by rw [hfun]; exact hopfSub_charpoly) hopfSub_r_roots
    (hasDerivAt_fderiv_hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2))
    (by rw [paramTrace_hopfSub]; norm_num) (by rw [hl]; norm_num)
  refine ⟨δ, hδ, fun μ h1 h2 => ?_⟩
  have hμ : |μ| < δ := by rw [abs_of_pos h1]; exact h2
  obtain ⟨z, T, hT, hz, hzT, hznc, hU, hamp⟩ := hcyc μ hμ (by
    rw [paramTrace_hopfSub, hl]; linarith)
  refine ⟨z, T, hT, hz, hzT, hznc, fun t => (posV_iff _ _).mp (hU t), fun t => ?_⟩
  have h := hamp t
  rw [paramTrace_hopfSub, hl] at h
  have e : -(μ * (-1 / 4)) / (1 * (8 / 85)) = 85 * μ / 32 := by ring
  rw [e] at h
  constructor <;> linarith [h.1, h.2]


/-- **Every small cycle of `hopfSub`.** For every `η > 0`, every nonconstant periodic orbit of the
slice field with the damping `2 + μ`, `|μ|` small, near the operating point has `μ > 0` (none at
or below the Hopf damping) and `(1 − η) 85μ/32 ≤ ‖critπ p z(t)‖² ≤ (1 + η) 85μ/32`
(`HopfCycle.periodic_amplitude_local`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem hopfSub_periodic_amplitude {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 4) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z (hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) (z t) μ) t) →
      (∀ t, z (t + T) = z t) → (∃ t, z t ≠ z 0) → (∀ t, ‖z t‖ < δ) →
      0 < μ ∧ ∀ t, (1 - η) * (85 * μ / 32) ≤ ‖critπ hopfSubP (z t)‖ ^ 2 ∧
        ‖critπ hopfSubP (z t)‖ ^ 2 ≤ (1 + η) * (85 * μ / 32) := by
  have hfun : (fun z => hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) z 0) = hopfSub.field :=
    hopfDampFamily_zero_fun 2 2 2 2 (-1 / 2) 2 (1 / 2)
  have hl : firstLyapunov (fun z => hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) z 0) 0 1 hopfSubQ
      hopfSubP = 8 / 85 := by rw [hfun]; exact hopfSub_firstLyapunov
  obtain ⟨δ, hδ, hamp⟩ := Dynamics.HopfCycle.periodic_amplitude_local
    (F := hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2)) (ω := 1) (q := hopfSubQ) (p := hopfSubP)
    isOpen_posV (by simp) (fun w hw => ((contDiffAt_augField_hopfDampFamily 2 2 2 2 (-1 / 2) 2
      (1 / 2) hw).of_le le_top).contDiffWithinAt)
    (contDiffAt_augField_hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2) (by simp)).analyticAt
    (hopfDampFamily_origin 2 2 2 2 (-1 / 2) 2 (1 / 2)) (by rw [hfun]; exact hopfSub_isCriticalPair)
    (by rw [hfun]; exact hopfSub_charpoly) hopfSub_r_roots
    (hasDerivAt_fderiv_hopfDampFamily 2 2 2 2 (-1 / 2) 2 (1 / 2))
    (by rw [paramTrace_hopfSub]; norm_num) (by rw [hl]; norm_num) hη
  refine ⟨δ, hδ, fun μ hμ z T hT hz hzT hnc hzδ => ?_⟩
  obtain ⟨hs, hbd⟩ := hamp μ hμ z T hT hz hzT hnc hzδ
  rw [paramTrace_hopfSub, hl] at hs hbd
  have hμ0 : 0 < μ := by linarith
  have e : -(μ * (-1 / 4)) / (1 * (8 / 85)) = 85 * μ / 32 := by ring
  simp only [e] at hbd
  exact ⟨hμ0, hbd⟩

end VSMDC

end powerlib.GFM.DCLink
