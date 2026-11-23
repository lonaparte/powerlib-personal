import theorem.GridTiedConverter.GFL.LCLine.Reduced2D
import theorem.Criteria.Hurwitz2
import theorem.GridTiedConverter.PLL.Linear
import theorem.PowerSystem.Synchronous.PH

/-! # Damping-class dichotomy: constant-damping swing (class A) vs GFL type-2 PLL (class B)

Domain module (pH structure, matrix algebra of noise ports, linearization invariants).
No stochastic statement is made: `B Bᵀ = 2 T R` is stated only as a matrix identity
(the fluctuation–dissipation *structure*), not as a theorem about stationary densities.

Model boundary.
* Class B: the reduced GFL-PLL of `theorem/GridTiedConverter/GFL/LCLine/Reduced2D.lean`, state
  `(θ_e, η)`, `J = [[0, 1], [−1, 0]]`, `R_B = diag(K_p, 0)` (`Params.pHModel`; its matrices are
  the PI-PLL's `PLL.pllJ`, `PLL.pllR`).
* Class A: single-machine infinite-bus swing equation (or droop / VSM with first-order filter,
  which has the same synchronizing-loop form), state `x 0 = δ` (load angle), `x 1 = p`
  (momentum deviation `M (ω_r − ω_0)`), field `δ̇ = p/M`, `ṗ = P_m − P_max sin δ − D p/M`;
  `H = p²/(2M) + V(δ)`, `V(δ) = −P_m δ − P_max cos δ`; `J = [[0, 1], [−1, 0]]`, `R = diag(0, D)`,
  input port `(0, 1)ᵀ` (mechanical-power / torque perturbation). Constant damping `D`; classical
  `P_e = P_max sin δ`; continuous time; no exciter, governor, saturation or network dynamics.
  Class A is the classical machine `Synchronous.classicalSM` (physical range `M > 0`, `D ≥ 0`,
  `P_max = b > 0`, `Synchronous.ClassicalSMParams`): its zero-input field is the canonical swing
  field in the momentum coordinates `(δ, M ω)`
  (`Synchronous.classicalSM_zeroInputField_eq_transport`).

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md`
§1–§3; `sn-critical-scaling.md` §1.

Results.
* The class-A pH model is the classical machine `Synchronous.classicalSM`
  (`theorem/PowerSystem/Synchronous/PH.lean`, `b = P_max`): its field is the swing field
  (`Synchronous.classicalSM_field`), its energy balance `Ḣ = u ω − D ω²`
  (`PH.NonlinearModel.power_balance` with `Synchronous.classicalSM_dampingPower`, `Ḣ = −D (p/M)²`
  at `u = 0`) and its dissipation matrix
  `R_A` (`swingPH_R`).
* Port inversion (`damping-class-dichotomy.md` §2): grid-frequency noise enters the class-B
  dissipation port exactly, `B Bᵀ = 2 (ε²/2K_p) R_B` (`Embed.freqNoise_fdt`,
  `theorem/GridTiedConverter/GFL/Noise/Embedding.lean`, `R_B = PLL.pllR K_p`), while for class A it
  is orthogonal to `R_A` and never proportional to it (`classA_frequency_orthogonal`,
  `classA_frequency_not_fdt`); mechanical-power noise is exactly in the class-A port
  (`classA_torque_fdt`), and the class-B voltage channel is not (`classB_voltage_not_fdt`).
* Linearization (`§2b`): class-B Jacobian has `tr/det = −K_p/K_i` at every non-fold point
  (`PLL.piPLLJacobian_trace_det_relation`: `K_i tr + K_p det = 0`, at every slope) and is nonzero
  nilpotent at a fold (`Params.reduced_jacobian_nilpotent`,
  `theorem/GridTiedConverter/GFL/LCLine/Reduced2D.lean`); the class-A Jacobian
  `[[0, 1/M], [−g, −D/M]]` (`classAJacobian`, the mechanical Jacobian
  `PhasePlane.Conservative.jacobian M D g` (the swing Jacobian at synchronizing coefficient `g`) in
  momentum coordinates, the classical machine's `Synchronous.classicalSM_linearization`) has
  constant trace `−D/M` (`classA_trace`), so at a fold it is never nilpotent
  (`classA_not_nilpotent`).
* Damping ratio (`§3`, `Criteria.dampingRatio`): `ζ_B` is the PI-PLL damping ratio `PLL.zeta` at the
  slope `g` (`classB_zeta_eq`), `ζ_B = (K_p/2)√(g/K_i)` for `g > 0` (`zetaB_eq`),
  `ζ_A = D/(2√(M g))` (`classA_zeta_eq`: the mechanical damping ratio
  `PhasePlane.Conservative.dampingRatio_jacobian`, invariant under `Criteria.dampingRatio_conj`);
  `ζ_B(λ g) = √λ ζ_B(g)`, `ζ_A(λ g) = ζ_A(g)/√λ`; `ζ_B → 0`,
  `ζ_A → ∞` as `g → 0⁺`; near the fold the class-A eigenvalues are real
  (`classA_eigenvalues_real_of_le`) and the class-B eigenvalues are non-real
  (`classB_eigenvalue_nonreal_of_lt`).

Family and connection conclusions.
No family and no connection conclusion: the module contains
pH constructions, energy-rate identities, matrix identities of the noise ports and linearization
invariants only (static domain model identities). The class-B behavioural conclusions
are made through the members `p.pllModel θ` of `PLL.PIPLL.family`
(`theorem/GridTiedConverter/GFL/LCLine/Reduced2D.lean`).
-/

noncomputable section
namespace powerlib.GFL.Noise
open Real Matrix Filter Topology
open powerlib.Dynamics (State)
open powerlib.NormalForm.BogdanovTakens (trace_proportionalMatrix det_proportionalMatrix)
open powerlib.PLL
open powerlib.GFL.LCLine

/-! ### Noise ports and the fluctuation–dissipation structure (matrix algebra) -/

/-- Class-A dissipation matrix `R_A = diag(0, D)`. The class-B dissipation matrix
`R_B = diag(K_p, 0)` is the PI-PLL's `PLL.pllR K_p`. -/
def RA (D : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, D]

/-- The class-A pH model is the classical machine `Synchronous.classicalSM` (`b = P_max`): its
dissipation matrix is `R_A`. -/
@[tmio M, powerlib_domain] theorem swingPH_R (p : Synchronous.ClassicalSMParams) (x : State 2) :
    (Synchronous.classicalSM p).R x = RA p.D := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The class-B pH model has the dissipation matrix `R_B = PLL.pllR K_p`. Grid-frequency noise
`B = (−ε, 0)ᵀ` meets `B Bᵀ = 2 T R_B` with `T = ε²/(2K_p)` (`Embed.freqNoise_fdt`). -/
@[tmio M, powerlib_domain] theorem pHModel_R (p : Params) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0)
    (hKp : 0 ≤ p.Kp) (y : State 2) : (p.pHModel hwC hΔ hKp).R y = pllR p.Kp := rfl

/-- Grid-frequency noise in class A, `B = (−σ, 0)ᵀ`: orthogonal to `R_A`, `tr(B Bᵀ R_A) = 0`. -/
@[tmio M, powerlib_domain] theorem classA_frequency_orthogonal (D σ : ℝ) :
    (!![-σ; 0] * (!![-σ; 0])ᵀ * RA D).trace = 0 := by
  have hB : !![-σ; 0] * (!![-σ; 0])ᵀ = !![σ ^ 2, 0; 0, (0 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, sq]
  rw [hB]
  simp [RA, Matrix.trace_fin_two]

/-- ... and never of the form `2 T R_A` (`σ ≠ 0`). -/
@[tmio M, powerlib_domain] theorem classA_frequency_not_fdt {D σ : ℝ} (hσ : σ ≠ 0) (T : ℝ) :
    !![-σ; 0] * (!![-σ; 0])ᵀ ≠ (2 * T) • RA D := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [RA, Matrix.mul_apply] at this
  exact hσ this

/-- Mechanical-power noise in class A, `B = (0, σ)ᵀ`: `B Bᵀ = 2 T R_A` with `T = σ²/(2D)`. -/
@[tmio M, powerlib_domain] theorem classA_torque_fdt {D : ℝ} (hD : D ≠ 0) (σ : ℝ) :
    !![0; σ] * (!![0; σ])ᵀ = (2 * (σ ^ 2 / (2 * D))) • RA D := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [RA, Matrix.mul_apply]; field_simp

/-- Voltage noise in class B enters both rows, `B = (K_p σ, σ)ᵀ`: never of the form `2 T R_B`. -/
@[tmio M, powerlib_domain] theorem classB_voltage_not_fdt {Kp σ : ℝ} (hσ : σ ≠ 0) (T : ℝ) :
    !![Kp * σ; σ] * (!![Kp * σ; σ])ᵀ ≠ (2 * T) • pllR Kp := by
  intro h
  have := congrFun (congrFun h 1) 1
  simp [pllR, Matrix.mul_apply] at this
  exact hσ this

/-! ### Linearization invariants -/

/-- Class-A Jacobian at a point with restoring slope `g = P_max cos δ`:
`[[0, 1/M], [−g, −D/M]]`, the mechanical Jacobian `PhasePlane.Conservative.jacobian M D g` (the
swing Jacobian with synchronizing coefficient `g`) in the momentum coordinates `diag(1, M)`
(`Dynamics.scaleMatrix`); at a point `δ*` of the classical machine it is the linearization
`Synchronous.classicalSM_linearization` (`g = b cos δ*`). -/
def classAJacobian (M D g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Dynamics.scaleMatrix M * PhasePlane.Conservative.jacobian M D g * Dynamics.scaleMatrix M⁻¹

@[tmio M, powerlib_domain] theorem classA_trace {M : ℝ} (D g : ℝ) (hM : M ≠ 0) :
    (classAJacobian M D g).trace = -(D * M⁻¹) := by
  rw [classAJacobian, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    (Dynamics.scaleMatrix_mul_inv hM).2, Matrix.one_mul, PhasePlane.Conservative.trace_jacobian,
    neg_div, div_eq_mul_inv]

@[tmio M, powerlib_domain] theorem classA_det {M : ℝ} (D g : ℝ) (hM : M ≠ 0) :
    (classAJacobian M D g).det = g * M⁻¹ := by
  rw [classAJacobian, Matrix.det_conj_of_mul_eq_one (Dynamics.scaleMatrix_mul_inv hM).1
    (Dynamics.scaleMatrix_mul_inv hM).2, PhasePlane.Conservative.det_jacobian, div_eq_mul_inv]

/-- At a class-A fold (`g = 0`) the Jacobian is not nilpotent when `D/M ≠ 0`: one eigenvalue stays
at `−D/M` (an ordinary saddle-node), unlike the class-B fold. -/
@[tmio M, powerlib_domain] theorem classA_not_nilpotent {M D : ℝ} (h : D * M⁻¹ ≠ 0) :
    ¬ IsNilpotent (classAJacobian M D 0) := by
  have hM : M ≠ 0 := fun h0 => h (by simp [h0])
  rw [Criteria.isNilpotent_iff_trace_det_eq_zero_fin_two, classA_trace D 0 hM]
  rintro ⟨h1, -⟩
  exact h (neg_eq_zero.mp h1)

/-! ### Damping ratio laws -/

/-- Class-B damping ratio: the PI-PLL damping ratio `PLL.zeta` at the detector slope `g`,
`ζ_B = g K_p / (2 √(g K_i))`, which is `(K_p/2) √(g/K_i)` for `g > 0` (`zetaB_eq`). -/
def zetaB (Kp Ki g : ℝ) : ℝ := PLL.zeta g Kp Ki

/-- Class-A damping ratio `ζ_A = D/(2√(M g))`. -/
def zetaA (M D g : ℝ) : ℝ := D / (2 * √(M * g))

/-- For the class-B Jacobian at the slope `h′ = −g`: its damping ratio (`Criteria.dampingRatio`)
is `ζ_B`. -/
@[tmio M, powerlib_domain] theorem classB_zeta_eq (Kp Ki g : ℝ) :
    Criteria.dampingRatio (piPLLJacobian Kp Ki (-g)) = zetaB Kp Ki g := by
  rw [Criteria.dampingRatio, zetaB, PLL.zeta, PLL.omegaN, trace_proportionalMatrix,
    det_proportionalMatrix, show -(Ki * -g) = g * Ki by ring]
  ring

/-- The closed form `ζ_B = (K_p/2) √(g/K_i)` for a positive slope `g` (`PLL.zeta_eq`; for
`K_i ≤ 0` both sides vanish). -/
@[tmio M, powerlib_domain] theorem zetaB_eq (Kp Ki : ℝ) {g : ℝ} (hg : 0 < g) :
    zetaB Kp Ki g = Kp / 2 * √(g / Ki) := by
  rcases lt_or_ge 0 Ki with hKi | hKi
  · exact PLL.zeta_eq hg hKi
  · have h1 : √(g * Ki) = 0 := Real.sqrt_eq_zero'.mpr (mul_nonpos_of_nonneg_of_nonpos hg.le hKi)
    have h2 : √(g / Ki) = 0 := Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonneg_of_nonpos hg.le hKi)
    simp [zetaB, PLL.zeta, PLL.omegaN, h1, h2]

/-- For the class-A Jacobian with restoring slope `g > 0`: its damping ratio
(`Criteria.dampingRatio`) is `ζ_A`. -/
@[tmio M, powerlib_domain] theorem classA_zeta_eq {M D g : ℝ} (hM : 0 < M) (hg : 0 < g) :
    Criteria.dampingRatio (classAJacobian M D g) = zetaA M D g := by
  obtain ⟨h1, h2⟩ := Dynamics.scaleMatrix_mul_inv hM.ne'
  rw [classAJacobian, Criteria.dampingRatio_conj h1 h2,
    PhasePlane.Conservative.dampingRatio_jacobian hM hg, zetaA]

/-- Scaling law of class B: `ζ_B(λ g) = √λ ζ_B(g)`. -/
@[tmio M, powerlib_domain] theorem zetaB_scale (Kp Ki g : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    zetaB Kp Ki (l * g) = √l * zetaB Kp Ki g := by
  rw [zetaB, zetaB, PLL.zeta, PLL.zeta, PLL.omegaN, PLL.omegaN,
    show l * g * Ki = l * (g * Ki) by ring, Real.sqrt_mul hl]
  rcases hl.eq_or_lt with rfl | hl
  · simp
  · have hs : √l ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
    have hsl : √l * √l = l := Real.mul_self_sqrt hl.le
    have hn : l * g * Kp = √l * (√l * (g * Kp)) := by rw [← mul_assoc, hsl]; ring
    rw [hn, show 2 * (√l * √(g * Ki)) = √l * (2 * √(g * Ki)) by ring,
      mul_div_mul_left _ _ hs, mul_div_assoc]

/-- Scaling law of class A: `ζ_A(λ g) = ζ_A(g)/√λ`. -/
@[tmio M, powerlib_domain] theorem zetaA_scale (M D g : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    zetaA M D (l * g) = zetaA M D g / √l := by
  rw [zetaA, zetaA, show M * (l * g) = l * (M * g) by ring, Real.sqrt_mul hl]
  rw [div_div, mul_comm (2 * √(M * g)) (√l)]
  ring

/-- `ζ_B → 0` as `g → 0⁺`. -/
@[tmio M, powerlib_domain] theorem zetaB_tendsto_zero (Kp Ki : ℝ) :
    Tendsto (zetaB Kp Ki) (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous fun g : ℝ => Kp / 2 * √(g / Ki) := by fun_prop
  refine (tendsto_nhdsWithin_congr (fun g hg => (zetaB_eq Kp Ki hg).symm) ?_)
  exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using h.tendsto 0)

/-- `ζ_A → ∞` as `g → 0⁺` (`M, D > 0`). -/
@[tmio M, powerlib_domain] theorem zetaA_tendsto_atTop {M D : ℝ} (hM : 0 < M) (hD : 0 < D) :
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
@[tmio M, powerlib_domain] theorem classA_eigenvalues_real_of_le {M D g : ℝ} (hM : 0 < M)
    (hg : g ≤ D ^ 2 / (4 * M)) (μ : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (heig : (classAJacobian M D g).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) : μ.im = 0 := by
  refine (Criteria.eigenvalues_real_iff_discriminant_nonneg _).mpr ?_ μ v hv heig
  rw [classA_trace D g hM.ne', classA_det D g hM.ne']
  rw [le_div_iff₀ (by positivity)] at hg
  have : 0 ≤ D ^ 2 - 4 * M * g := by linarith
  have e : (-(D * M⁻¹)) ^ 2 - 4 * (g * M⁻¹) = (D ^ 2 - 4 * M * g) / M ^ 2 := by
    field_simp; try ring
  rw [e]; positivity

/-- Near the fold, `0 < g < 4K_i/K_p²`, the class-B linearization has a non-real eigenvalue
(underdamped). -/
@[tmio M, powerlib_domain] theorem classB_eigenvalue_nonreal_of_lt {Kp Ki g : ℝ} (hg : 0 < g)
    (hlt : Kp ^ 2 * g < 4 * Ki) :
    ∃ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧
      (piPLLJacobian Kp Ki (-g)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ μ.im ≠ 0 := by
  by_contra H
  push Not at H
  have hreal : ∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
      (piPLLJacobian Kp Ki (-g)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.im = 0 :=
    fun μ v hv he => H μ v hv he
  have := (Criteria.eigenvalues_real_iff_discriminant_nonneg _).mp hreal
  rw [trace_proportionalMatrix, det_proportionalMatrix] at this
  nlinarith

end powerlib.GFL.Noise
