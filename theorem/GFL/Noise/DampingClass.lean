import theorem.GFL.LCLine.Reduced2D
import theorem.Criteria.Hurwitz2

/-! # Damping-class dichotomy: constant-damping swing (class A) vs GFL type-2 PLL (class B)

Foundation module (pH structure, matrix algebra of noise ports, linearization invariants).
No stochastic statement is made: `B Bᵀ = 2 T R` is stated only as a matrix identity
(the fluctuation–dissipation *structure*), not as a theorem about stationary densities.

Model boundary.
* Class B: the reduced GFL-PLL of `theorem/GFL/LCLine/Reduced2D.lean`, state `(θ_e, η)`,
  `J = [[0, 1], [−1, 0]]`, `R = diag(K_p, 0)` (`Params.pHModel`).
* Class A: single-machine infinite-bus swing equation (or droop / VSM with first-order filter,
  which has the same synchronizing-loop form), state `x 0 = δ` (load angle), `x 1 = p`
  (momentum deviation `M (ω_r − ω_0)`), field `δ̇ = p/M`, `ṗ = P_m − P_max sin δ − D p/M`;
  `H = p²/(2M) + V(δ)`, `V(δ) = −P_m δ − P_max cos δ`; `J = [[0, 1], [−1, 0]]`, `R = diag(0, D)`,
  input port `(0, 1)ᵀ` (mechanical-power / torque perturbation). Constant damping `D`; classical
  `P_e = P_max sin δ`; continuous time; no exciter, governor, saturation or network dynamics.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md`
§1–§3; `sn-critical-scaling.md` §1.

Results.
* `swingPH` and `swingPH_zeroInputField`, `swing_energy_rate` (`Ḣ = −D (p/M)²`).
* Port inversion (`damping-class-dichotomy.md` §2): grid-frequency noise enters the class-B
  dissipation port exactly, `B Bᵀ = 2 (ε²/2K_p) R_B` (`classB_frequency_fdt`), while for class A it
  is orthogonal to `R_A` and never proportional to it (`classA_frequency_orthogonal`,
  `classA_frequency_not_fdt`); mechanical-power noise is exactly in the class-A port
  (`classA_torque_fdt`), and the class-B voltage channel is not (`classB_voltage_not_fdt`).
* Linearization (`§2b`): class-B Jacobian has `tr/det = −K_p/K_i` at every non-fold point
  (`classB_trace_div_det`) and is nonzero nilpotent at a fold (`Params.reduced_jacobian_nilpotent`,
  `theorem/GFL/LCLine/Reduced2D.lean`); the class-A Jacobian `[[0, 1/M], [−g, −D/M]]` has constant
  trace `−D/M` (`classA_trace`), so at a fold it is never nilpotent (`classA_not_nilpotent`).
* Damping ratio (`§3`): `ζ_B = (K_p/2)√(g/K_i)` (`classB_zeta_eq`), `ζ_A = D/(2√(M g))`
  (`classA_zeta_eq`); `ζ_B(λ g) = √λ ζ_B(g)`, `ζ_A(λ g) = ζ_A(g)/√λ`; `ζ_B → 0`, `ζ_A → ∞` as
  `g → 0⁺`; near the fold the class-A eigenvalues are real (`classA_eigenvalues_real_of_le`)
  and the class-B eigenvalues are non-real (`classB_eigenvalue_nonreal_of_lt`).

Family and connection conclusions.
No family and no connection conclusion: the module contains
pH constructions, energy-rate identities, matrix identities of the noise ports and linearization
invariants only (static foundation). The class-B behavioural conclusions
are made through the members `p.pllModel θ` of `PLL.PIPLL.family`
(`theorem/GFL/LCLine/Reduced2D.lean`).
-/

noncomputable section
namespace powerlib.GFL.Noise
open Real Matrix Filter Topology
open powerlib.Dynamics (State)
open powerlib.PLL
open powerlib.GFL.LCLine

/-! ### Class A: the swing equation as a pH system -/

/-- Parameters of the class-A swing model. -/
structure SwingParams where
  /-- Inertia `M`. -/
  M : ℝ
  /-- Constant damping `D`. -/
  D : ℝ
  /-- Mechanical (reference) power `P_m`. -/
  Pm : ℝ
  /-- Static transfer limit `P_max`. -/
  Pmax : ℝ

namespace SwingParams

variable (s : SwingParams)

/-- Swing field `δ̇ = p/M`, `ṗ = P_m − P_max sin δ − D p/M` (written with `M⁻¹`). -/
def field (x : State 2) : State 2 :=
  WithLp.toLp 2 ![s.M⁻¹ * x 1, s.Pm - s.Pmax * sin (x 0) - s.D * (s.M⁻¹ * x 1)]

/-- Potential `V(δ) = −P_m δ − P_max cos δ`. -/
def pot (δ : ℝ) : ℝ := -(s.Pm * δ) - s.Pmax * cos δ

/-- Hamiltonian `H = p²/(2M) + V(δ)`. -/
def hamiltonian (x : State 2) : ℝ := (2 * s.M)⁻¹ * x 1 ^ 2 + s.pot (x 0)

/-- Gradient `∇H = (P_max sin δ − P_m, p/M)`. -/
def gradH (x : State 2) : State 2 := WithLp.toLp 2 ![s.Pmax * sin (x 0) - s.Pm, s.M⁻¹ * x 1]

@[powerlib_foundation] theorem hasGradientAt_hamiltonian (x : State 2) :
    HasGradientAt s.hamiltonian (s.gradH x) x := by
  set π0 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  set π1 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 : HasFDerivAt (fun z : State 2 => z 0) π0 x := π0.hasFDerivAt
  have h1 : HasFDerivAt (fun z : State 2 => z 1) π1 x := π1.hasFDerivAt
  have hpot : HasDerivAt s.pot (s.Pmax * sin (x 0) - s.Pm) (x 0) := by
    have h := ((hasDerivAt_id (x 0)).const_mul s.Pm).neg.sub
      ((hasDerivAt_cos (x 0)).const_mul s.Pmax)
    convert h using 1
    · funext x; simp [pot]
    · simp; ring
  have hp := hpot.comp_hasFDerivAt x h0
  have hq := (h1.pow 2).const_mul (2 * s.M)⁻¹
  refine PH.hasGradientAt_of_hasFDerivAt (hq.add hp) ?_
  intro v
  simp [gradH, π0, π1, dotProduct, Fin.sum_univ_two]
  ring

@[powerlib_foundation] private lemma posSemidef_RA {D : ℝ} (hD : 0 ≤ D) :
    (!![0, 0; 0, D]).PosSemidef := by
  have : !![0, 0; 0, D] = Matrix.diagonal ![0, D] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.posSemidef_diagonal_iff]
  intro i; fin_cases i <;> simp [hD]

/-- Class A as a nonlinear pH system: `J = [[0, 1], [−1, 0]]`, `R = diag(0, D)`, port `(0, 1)ᵀ`. -/
def swingPH (hD : 0 ≤ s.D) : PH.NonlinearModel 2 1 where
  J _ := !![0, 1; -1, 0]
  R _ := !![0, 0; 0, s.D]
  g _ := !![0; 1]
  H := s.hamiltonian
  dH := s.gradH
  skew _ := PH.transpose_symplectic_two
  dissipation_posSemidef _ := posSemidef_RA hD
  hasGradient := s.hasGradientAt_hamiltonian

@[powerlib_foundation] theorem swingPH_zeroInputField (hD : 0 ≤ s.D) :
    (s.swingPH hD).zeroInputField = s.field := by
  funext x
  have hg : WithLp.ofLp (s.gradH x) = ![s.Pmax * sin (x 0) - s.Pm, s.M⁻¹ * x 1] := rfl
  simp only [PH.NonlinearModel.zeroInputField, PH.NonlinearModel.field, swingPH, hg, field]
  congr 1
  ext i; fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Class-A energy balance: `Ḣ = −D (p/M)²`. -/
@[powerlib_foundation] theorem swing_energy_rate (hD : 0 ≤ s.D) (x : State 2) :
    fderiv ℝ s.hamiltonian x (s.field x) = -(s.D * (s.M⁻¹ * x 1) ^ 2) := by
  have h := (s.swingPH hD).zeroInput_power_balance x
  have hH : (s.swingPH hD).H = s.hamiltonian := rfl
  rw [swingPH_zeroInputField, hH] at h
  rw [h]
  have hg : WithLp.ofLp (s.gradH x) = ![s.Pmax * sin (x 0) - s.Pm, s.M⁻¹ * x 1] := rfl
  simp only [PH.NonlinearModel.dampingPower, swingPH, hg]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  ring

end SwingParams

/-! ### Noise ports and the fluctuation–dissipation structure (matrix algebra) -/

/-- Class-A dissipation matrix `R_A = diag(0, D)`. -/
def RA (D : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, D]
/-- Class-B dissipation matrix `R_B = diag(K_p, 0)`. -/
def RB (Kp : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Kp, 0; 0, 0]

@[powerlib_foundation] theorem swingPH_R (s : SwingParams) (hD : 0 ≤ s.D) (x : State 2) :
    (s.swingPH hD).R x = RA s.D := rfl

@[powerlib_foundation] theorem pHModel_R (p : Params) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) (y : State 2) : (p.pHModel hwC hΔ hKp).R y = RB p.Kp := rfl

/-- Grid-frequency noise in class B, `B = (−ε, 0)ᵀ`: `B Bᵀ = 2 T R_B` with `T = ε²/(2K_p)`. -/
@[powerlib_foundation] theorem classB_frequency_fdt {Kp : ℝ} (hKp : Kp ≠ 0) (ε : ℝ) :
    !![-ε; 0] * (!![-ε; 0])ᵀ = (2 * (ε ^ 2 / (2 * Kp))) • RB Kp := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [RB, Matrix.mul_apply] <;> field_simp <;> ring

/-- Grid-frequency noise in class A, `B = (−σ, 0)ᵀ`: orthogonal to `R_A`, `tr(B Bᵀ R_A) = 0`. -/
@[powerlib_foundation] theorem classA_frequency_orthogonal (D σ : ℝ) :
    (!![-σ; 0] * (!![-σ; 0])ᵀ * RA D).trace = 0 := by
  have hB : !![-σ; 0] * (!![-σ; 0])ᵀ = !![σ ^ 2, 0; 0, (0 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, sq]
  rw [hB]
  simp [RA, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- ... and never of the form `2 T R_A` (`σ ≠ 0`). -/
@[powerlib_foundation] theorem classA_frequency_not_fdt {D σ : ℝ} (hσ : σ ≠ 0) (T : ℝ) :
    !![-σ; 0] * (!![-σ; 0])ᵀ ≠ (2 * T) • RA D := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [RA, Matrix.mul_apply] at this
  exact hσ this

/-- Mechanical-power noise in class A, `B = (0, σ)ᵀ`: `B Bᵀ = 2 T R_A` with `T = σ²/(2D)`. -/
@[powerlib_foundation] theorem classA_torque_fdt {D : ℝ} (hD : D ≠ 0) (σ : ℝ) :
    !![0; σ] * (!![0; σ])ᵀ = (2 * (σ ^ 2 / (2 * D))) • RA D := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [RA, Matrix.mul_apply] <;> field_simp <;> ring

/-- Voltage noise in class B enters both rows, `B = (K_p σ, σ)ᵀ`: never of the form `2 T R_B`. -/
@[powerlib_foundation] theorem classB_voltage_not_fdt {Kp σ : ℝ} (hσ : σ ≠ 0) (T : ℝ) :
    !![Kp * σ; σ] * (!![Kp * σ; σ])ᵀ ≠ (2 * T) • RB Kp := by
  intro h
  have := congrFun (congrFun h 1) 1
  simp [RB, Matrix.mul_apply] at this
  exact hσ this

/-! ### Linearization invariants -/

/-- Class B: `tr J / det J = −K_p/K_i` at every point with `g = h′(θ) ≠ 0` (`K_i ≠ 0`). -/
@[powerlib_foundation] theorem classB_trace_div_det {Kp Ki g : ℝ} (hKi : Ki ≠ 0) (hg : g ≠ 0) :
    (piPLLJacobian Kp Ki g).trace / (piPLLJacobian Kp Ki g).det = -Kp / Ki := by
  rw [piPLLJacobian_trace, piPLLJacobian_det]
  field_simp

/-- Class-A Jacobian at a point with restoring slope `g = P_max cos δ`:
`[[0, 1/M], [−g, −D/M]]`. -/
def classAJacobian (M D g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, M⁻¹; -g, -(D * M⁻¹)]

@[powerlib_foundation] theorem classA_trace (M D g : ℝ) :
    (classAJacobian M D g).trace = -(D * M⁻¹) := by
  simp [classAJacobian, Matrix.trace_fin_two]

@[powerlib_foundation] theorem classA_det (M D g : ℝ) :
    (classAJacobian M D g).det = g * M⁻¹ := by
  simp [classAJacobian, Matrix.det_fin_two]; ring

/-- The class-A Jacobian is the derivative of the swing field. -/
@[powerlib_foundation] theorem SwingParams.hasFDerivAt_field (s : SwingParams) (x : State 2) :
    HasFDerivAt s.field (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      (classAJacobian s.M s.D (s.Pmax * cos (x 0)))) x := by
  set π0 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  set π1 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 : HasFDerivAt (fun z : State 2 => z 0) π0 x := π0.hasFDerivAt
  have h1 : HasFDerivAt (fun z : State 2 => z 1) π1 x := π1.hasFDerivAt
  have hs := (hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  have hF0 := h1.const_mul s.M⁻¹
  have hF1 := ((hasFDerivAt_const s.Pm x).sub (hs.const_mul s.Pmax)).sub
    ((h1.const_mul s.M⁻¹).const_mul s.D)
  have hG : HasFDerivAt (fun z : State 2 => ![s.M⁻¹ * z 1,
      s.Pm - s.Pmax * sin (z 0) - s.D * (s.M⁻¹ * z 1)])
      (ContinuousLinearMap.pi ![s.M⁻¹ • π1,
        (0 - s.Pmax • (cos (x 0) • π0)) - s.D • (s.M⁻¹ • π1)]) x := by
    refine hasFDerivAt_pi.mpr ?_
    intro i; fin_cases i
    · exact hF0
    · exact hF1
  have hE := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp x hG
  have hfun : s.field = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
      (fun z : State 2 => ![s.M⁻¹ * z 1, s.Pm - s.Pmax * sin (z 0) - s.D * (s.M⁻¹ * z 1)]) := rfl
  rw [hfun]
  refine hE.congr_fderiv ?_
  ext v i
  rw [Matrix.ofLp_toEuclideanCLM]
  fin_cases i
  · simp [classAJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, π0, π1]
  · simp [classAJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, π0, π1]
    ring

/-- At a class-A fold (`g = 0`) the Jacobian is not nilpotent when `D/M ≠ 0`: one eigenvalue stays
at `−D/M` (an ordinary saddle-node), unlike the class-B fold. -/
@[powerlib_foundation] theorem classA_not_nilpotent {M D : ℝ} (h : D * M⁻¹ ≠ 0) :
    ¬ IsNilpotent (classAJacobian M D 0) := by
  rw [Criteria.isNilpotent_iff_trace_det_eq_zero_fin_two, classA_trace]
  rintro ⟨h1, -⟩
  exact h (neg_eq_zero.mp h1)

/-! ### Damping ratio laws -/

/-- `ζ = |tr|/(2√det)` of a 2×2 matrix. -/
def zeta (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := |A.trace| / (2 * √A.det)

/-- Class-B damping ratio `ζ_B = (K_p/2) √(g/K_i)`. -/
def zetaB (Kp Ki g : ℝ) : ℝ := Kp / 2 * √(g / Ki)

/-- Class-A damping ratio `ζ_A = D/(2√(M g))`. -/
def zetaA (M D g : ℝ) : ℝ := D / (2 * √(M * g))

/-- For the class-B Jacobian at a stable slope `h′ = −g`, `g > 0`: `ζ = ζ_B`. -/
@[powerlib_foundation] theorem classB_zeta_eq {Kp Ki g : ℝ} (hKp : 0 ≤ Kp) (hKi : 0 < Ki)
    (hg : 0 < g) : zeta (piPLLJacobian Kp Ki (-g)) = zetaB Kp Ki g := by
  rw [zeta, zetaB, piPLLJacobian_trace, piPLLJacobian_det,
    show -(Ki * -g) = Ki * g by ring, show Kp * -g = -(Kp * g) by ring, abs_neg,
    abs_of_nonneg (mul_nonneg hKp hg.le)]
  have h1 : √(Ki * g) = Ki * √(g / Ki) := by
    rw [show Ki * g = Ki ^ 2 * (g / Ki) by field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hKi.le]
  have h2 : 0 < √(g / Ki) := Real.sqrt_pos.mpr (div_pos hg hKi)
  rw [h1]
  have h3 : √(g / Ki) * √(g / Ki) = g / Ki := Real.mul_self_sqrt (div_pos hg hKi).le
  have h3' : √(g / Ki) * √(g / Ki) * Ki = g := by rw [h3, div_mul_cancel₀ g hKi.ne']
  rw [div_eq_iff (by positivity)]
  linear_combination (-Kp) * h3'

/-- For the class-A Jacobian with restoring slope `g > 0`: `ζ = ζ_A`. -/
@[powerlib_foundation] theorem classA_zeta_eq {M D g : ℝ} (hM : 0 < M) (hD : 0 ≤ D) (hg : 0 < g) :
    zeta (classAJacobian M D g) = zetaA M D g := by
  rw [zeta, zetaA, classA_trace, classA_det, abs_neg,
    abs_of_nonneg (mul_nonneg hD (inv_nonneg.mpr hM.le))]
  have h1 : √(M * g) = M * √(g * M⁻¹) := by
    rw [show M * g = M ^ 2 * (g * M⁻¹) by field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hM.le]
  rw [h1]
  have h2 : 0 < √(g * M⁻¹) := Real.sqrt_pos.mpr (mul_pos hg (inv_pos.mpr hM))
  field_simp

/-- Scaling law of class B: `ζ_B(λ g) = √λ ζ_B(g)`. -/
@[powerlib_foundation] theorem zetaB_scale (Kp Ki g : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    zetaB Kp Ki (l * g) = √l * zetaB Kp Ki g := by
  rw [zetaB, zetaB, mul_div_assoc, Real.sqrt_mul hl]; ring

/-- Scaling law of class A: `ζ_A(λ g) = ζ_A(g)/√λ`. -/
@[powerlib_foundation] theorem zetaA_scale (M D g : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    zetaA M D (l * g) = zetaA M D g / √l := by
  rw [zetaA, zetaA, show M * (l * g) = l * (M * g) by ring, Real.sqrt_mul hl]
  rw [div_div, mul_comm (2 * √(M * g)) (√l)]
  ring

/-- `ζ_B → 0` as `g → 0⁺`. -/
@[powerlib_foundation] theorem zetaB_tendsto_zero (Kp Ki : ℝ) :
    Tendsto (zetaB Kp Ki) (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous (zetaB Kp Ki) := by unfold zetaB; fun_prop
  have := h.tendsto 0
  simp [zetaB] at this
  exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa [zetaB] using h.tendsto 0)

/-- `ζ_A → ∞` as `g → 0⁺` (`M, D > 0`). -/
@[powerlib_foundation] theorem zetaA_tendsto_atTop {M D : ℝ} (hM : 0 < M) (hD : 0 < D) :
    Tendsto (zetaA M D) (𝓝[>] 0) atTop := by
  have hs : Tendsto (fun g : ℝ => 2 * √(M * g)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Continuous (fun g : ℝ => 2 * √(M * g)) := by fun_prop
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with g hg
      exact mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos hM hg))
  exact (tendsto_inv_nhdsGT_zero.comp hs).const_mul_atTop hD |>.congr
    (fun g => by simp [zetaA, div_eq_mul_inv])

/-- Near the fold, `0 < g ≤ D²/(4M)`, the class-A eigenvalues are real (overdamped). -/
@[powerlib_foundation] theorem classA_eigenvalues_real_of_le {M D g : ℝ} (hM : 0 < M)
    (hg : g ≤ D ^ 2 / (4 * M)) (μ : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (heig : (classAJacobian M D g).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) : μ.im = 0 := by
  refine (Criteria.eigenvalues_real_iff_discriminant_nonneg _).mpr ?_ μ v hv heig
  rw [classA_trace, classA_det]
  rw [le_div_iff₀ (by positivity)] at hg
  have : 0 ≤ D ^ 2 - 4 * M * g := by linarith
  have e : (-(D * M⁻¹)) ^ 2 - 4 * (g * M⁻¹) = (D ^ 2 - 4 * M * g) / M ^ 2 := by
    field_simp; try ring
  rw [e]; positivity

/-- Near the fold, `0 < g < 4K_i/K_p²`, the class-B linearization has a non-real eigenvalue
(underdamped). -/
@[powerlib_foundation] theorem classB_eigenvalue_nonreal_of_lt {Kp Ki g : ℝ} (hg : 0 < g)
    (hlt : Kp ^ 2 * g < 4 * Ki) :
    ∃ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧
      (piPLLJacobian Kp Ki (-g)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ μ.im ≠ 0 := by
  by_contra H
  push Not at H
  have hreal : ∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
      (piPLLJacobian Kp Ki (-g)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.im = 0 :=
    fun μ v hv he => H μ v hv he
  have := (Criteria.eigenvalues_real_iff_discriminant_nonneg _).mp hreal
  rw [piPLLJacobian_trace, piPLLJacobian_det] at this
  nlinarith

end powerlib.GFL.Noise
