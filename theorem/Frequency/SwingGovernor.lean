import theorem.Frequency.Basic
import theorem.Criteria.Hurwitz2
import theorem.Linear.Rate
import theorem.TMIO.ClaimElab
import theorem.SingularPerturbation.FiniteHorizon
import theorem.LTI.Decay
import theorem.Spectral.LinearNamed
import theorem.Dynamics.Coordinates

/-! # Single-area swing + first-order governor (two-state frequency model)

The two-state swing + governor frequency model as a linear family (RoCoF, quasi-steady state,
damping trend, exact Hurwitz translation), and its singular-perturbation limit `T_g → 0` to the
first-order swing with static droop.

Model boundary.
* Continuous-time, linear, small-signal model around a nominal operating point, Kundur
  per-unit form (`T-frequency-stability.md` "单位约定"): the frequency deviation `Δω` is
  dimensionless per-unit, `M = M_eff = 2 H_eff` [s], powers are system-base per-unit.
* State `x = (x 0, x 1) = (Δω, ΔP_m)` in `ℝ² = EuclideanSpace ℝ (Fin 2)`: COI frequency
  deviation and aggregated mechanical-power deviation. Input (one port, `Fin 1`): load step
  `ΔP_L` (load increase positive, i.e. the generation-side "export-positive" balance
  `M Δω̇ = ΔP_m − ΔP_L − D Δω`). Output: `Δω`.
* Swing `M Δω̇ = ΔP_m − ΔP_L − D Δω` (`D = D_eff`, damping including load damping and any
  linear virtual damping, already aggregated by `Frequency.Aggregation`), governor
  `T_g ΔṖ_m = −ΔP_m − K_R Δω` (aggregate droop gain `K_R = Σ 1/R_k`, one common `T_g`).
* Excluded: turbine/reheat dynamics (see `Frequency.SFR`), AGC, dead-bands, rate limits,
  valve saturation, converter inner loops, PLL, delays, PWM, voltage dynamics, nonlinear swing.
* Parameter ranges are stated per theorem (typically `0 < M`, `0 < T_g`, `0 ≤ D`,
  `0 < K_R + D`); the family's models carry `0 < M` and `0 < T_g`.
* Singular-perturbation limit `T_g → 0` (the governor becomes the static droop
  `ΔP_m = −K_R Δω`). Reduced model: the first-order swing `M Δω̇ = −(K_R + D) Δω − ΔP_L`
  (`reducedPlant`, state `Δω`, input `ΔP_L`, output `Δω`; it is
  `LowInertia.firstOrderModel M (K_R + D)`). Two-time-scale form `twoTimeScale`
  (`SingularPerturbation.LinearSP 1 1`): slow `Δω`, fast `ΔP_m`, `ε = T_g`.

Source: work-sync `theory/T-frequency-stability.md` §1.4–§1.8 (model §1.7/§1.8, RoCoF §1.5,
quasi-steady-state deviation §1.6, characteristic polynomial / `ω_n` / `ζ_n` §1.7, damping trend
§2.5).

Results.
Two-state model (static, foundation):
* `field_swing`, `field_governor`: the state equations are exactly the §1.7 pair.
* `transfer_apply`: `Linear.transfer` from `ΔP_L` to `Δω` is
  `−(1 + T_g s)/(M T_g s² + (M + D T_g) s + (D + K_R))` (§1.7).
* `det_characteristicMatrix_eq`: `det(sI − A) = s² + 2 ζ_n ω_n s + ω_n²` with the §1.7 boxed
  `ω_n`, `ζ_n`; `dampingRatio_strictAntiOn`: `ζ_n` strictly decreases in `K_R` (§2.5).
* `isEquilibrium_iff`: the unique equilibrium for the step `ΔP_L` is
  `(−ΔP_L/(K_R + D), K_R ΔP_L/(K_R + D))` (§1.6).
* `isHurwitz_iff`: for `0 < M`, `0 < T_g` the state matrix is Hurwitz iff `0 < M + D T_g` and
  `0 < K_R + D`; with `0 ≤ D` this is `0 < K_R + D` (`isHurwitz_iff_of_nonneg`).
Singular-perturbation limit:
* Static (foundation): `plant_A_eq_stateMatrix` (the state matrix is the generic
  two-time-scale matrix at `ε = T_g`), `twoTimeScale_gain` (quasi-steady state
  `ΔP_m = −K_R Δω`), `twoTimeScale_reducedMatrix` (the Schur complement is `−(K_R + D)/M`),
  `twoTimeScale_A22_isHurwitz`; `field_quasiSteady` (on `ΔP_m = −K_R Δω` the governor row
  vanishes and the swing row is the first-order field).
* Eigenvalues: `eigDisc`, `slowEig`, `fastEig` (the real roots of
  `M T_g s² + (M + D T_g) s + (D + K_R)`, slow root rationalized), `slowEig_root`,
  `fastEig_root`, `slowEig_eq`, Vieta (`slowEig_add_fastEig`, `slowEig_mul_fastEig`),
  `slowEig_sub_fastEig`, `det_characteristicMatrix_eq_mul` /
  `det_characteristicMatrix_eq_zero_iff` (for a nonnegative discriminant the spectrum is
  `{λ_s, λ_f}`), `plant_mulVec_slowEigvec` (slow eigenvector `(1, M λ_s + D)`). Limits:
  `eventually_eigDisc_pos` (real distinct roots for small `T_g`), `eventually_rootSum_pos`,
  `slowEig_zero`, `tendsto_slowEig` (`λ_s → −(K_R + D)/M`, continuous at `T_g = 0`),
  `tendsto_slowSlope` (the invariant slow line `ΔP_m = (M λ_s + D) Δω` tends to
  `ΔP_m = −K_R Δω`), `tendsto_mul_fastEig` (`T_g λ_f → −1`, with `mul_fastEig`),
  `tendsto_fastEig_atBot` (`λ_f → −∞` as `T_g → 0⁺`), `tendsto_dampingRatio_atTop`
  (`ζ_n → ∞`: overdamped in the limit).
* Transfer function: `reduced_field_apply`, `reduced_transfer_apply` (`−1/(M s + K_R + D)`),
  `tendsto_transfer` (pointwise convergence off the first-order pole).
* Stability (static): `reduced_isHurwitz_iff` (`0 < K_R + D`), `isHurwitz_iff_reduced`
  (Hurwitz iff the reduction is, whenever `0 < M + D T_g`), `eventually_isHurwitz_iff_reduced`;
  `rateMargin_iff`, `reduced_rateMargin_iff`, `eventually_rateMargin_iff_reduced` (off the pole
  `a M = K_R + D` the rate margins agree for small `T_g`); generic `LTI.not_decay_of_eigenvector`
  (a real eigenvalue `μ > −a` excludes decay at the rate `a`).

Family and connection conclusions.
* System map: a model (`Model`: `M, D, K_R, T_g` with `0 < M`, `0 < T_g`) is read as the port
  system of its plant (`Family.IsLinear`): port input the load deviation `ΔP_L`, port output
  `Δω`. The flow sentences therefore speak about the zero-load operating point; since the plant
  is linear, the same attractive sentences hold at the quasi-steady state of every constant load
  step (`Linear.holds_input_iff` with `steadyState_isEquilibrium`).
* Requirements (static): `stable` (`0 < M + D T_g`, `0 < K_R + D`: Jacobian trace `< 0`,
  determinant `> 0`), `unstable` (`K_R + D < 0` or `M + D T_g < 0`), `rate a`
  (`Linear.RateMargin A a`). Lyapunov stability and the attractive sentences translate into
  `stable`, instability into `unstable`, a decay rate into its margin; conservation and
  passivity have no translation (the whole, inconsistent, language).
* Connection theorems: `chain_le_semantics` (soundness of every translation), `exact_hurwitz`
  (the attractive sentences and sampled contraction are translated exactly),
  `mem_den_attractive_iff` (the member characterization), `mem_den_globallyExponentiallyStable`
  (§1.6: `0 ≤ D`, `0 < K_R + D` give global exponential stability), `mem_den_unstable`, and
  `not_mem_den_passive` (with `0 < K_R + D`, a constant load draws energy out of the
  `(ΔP_L, Δω)` port at the quasi-steady state, so the model is not passive).
* Static evidence (foundation): `isEquilibrium_iff`, `steadyState_isEquilibrium`.
  Implementation evidence (private, trajectory level, outside the sentence language): the
  initial RoCoF `Δω̇(0⁺) = −ΔP_L / M_eff` (`rocof`, `rocof_hz`, §1.5), the global exponential
  stability of the quasi-steady state of the load step (`exponentiallyConvergesTo_steadyState`)
  and the convergence `Δω(t) → −ΔP_L/(K_R + D)` of every forward solution under the load step
  (`tendsto_freq`, §1.6).
* First-order family `reducedFamily` (`ReducedModel`: `M > 0`, `D`, `K_R`; requirements
  `stable` `0 < K_R + D`, `unstable` `K_R + D < 0`, `rate a` `a M ≤ K_R + D`; `Model.reduce`
  forgets `T_g`, `reduce_plant`): `reducedFamily_isLinear`, `reduced_realize_univ`,
  `reduced_chain_le_semantics`, `reduced_exact_hurwitz`, `reduced_exact_decay` (the decay
  translation is exact at every rate: the solutions are `e^{−(K_R + D) t/M}`).
* Connection conclusions of the limit: `mem_den_iff_reduce` (for `0 < M + D T_g` a model
  satisfies an attractive sentence or sampled contraction exactly when its reduction does),
  `mem_den_iff_reduce_of_nonneg` (every `T_g` when `0 ≤ D`),
  `exists_unstable_reduce_globallyExponentiallyStable` (boundary: `M = 1`, `D = −1`,
  `K_R = 2`, `T_g = 2` is unstable while its reduction is globally exponentially stable, so with
  negative damping the transfer needs a small `T_g`), `not_mem_den_decay_of_slowEig` (the slow
  root bounds every decay rate), `exists_threshold_mem_den_decay_iff_reduce` (for a rate off the
  pole there is a threshold `τ > 0` below which the model decays at that rate exactly when its
  reduction does). Scaffold: `theorem/GovernorReduction.agda`.
* Implementation evidence of the limit (private, trajectory level): `finiteHorizon_reduce` —
  for every horizon `T` and `T_g ≤ ε₀`, `|Δω(t) − Δω̄(t)|² ≤ C T_g² |x(0) − x^∞|²` and
  `|ΔP_m(t) − (−K_R Δω̄(t) + e^{−t/T_g}(ΔP_m(0) + K_R Δω(0)))|² ≤ C T_g² |x(0) − x^∞|²` on
  `[0, T]` under any constant load (`K_R + D ≠ 0`), from the generic
  `SingularPerturbation.LinearSP.exists_finiteHorizon_error`.

Not formalized.
* The decay translation of the full model at the boundary rate `a M = K_R + D` (the slow root
  may lie on either side), uniform-in-time (infinite horizon) trajectory estimates.
-/

noncomputable section
namespace powerlib.Frequency.SwingGovernor
open Set Filter Matrix LinearSystems TMIO
open scoped Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Two-state swing + governor plant, state `(Δω, ΔP_m)`, input/output `ΔP_L` / `Δω`. -/
def plant (M D K Tg : ℝ) : Linear.Plant 2 1 where
  A := !![-D / M, 1 / M; -K / Tg, -1 / Tg]
  B := !![-1 / M; 0]
  C := !![1, 0]
  D := 0

/-- Quasi-steady state `(Δω^∞, ΔP_m^∞) = (−ΔP_L/(K_R + D), K_R ΔP_L/(K_R + D))`. -/
def steadyState (D K ΔPL : ℝ) : ℝ² := WithLp.toLp 2 ![-ΔPL / (K + D), K * ΔPL / (K + D)]

/-- Undamped natural frequency `ω_n = √((D + K_R)/(M T_g))` (§1.7). -/
def natFreq (M D K Tg : ℝ) : ℝ := Real.sqrt ((D + K) / (M * Tg))

/-- Damping ratio `ζ_n = (M + D T_g)/(2 √(M T_g (D + K_R)))` (§1.7). -/
def dampingRatio (M D K Tg : ℝ) : ℝ := (M + D * Tg) / (2 * Real.sqrt (M * Tg * (D + K)))

variable {M D K Tg ΔPL : ℝ}

@[tmio M, simp, powerlib_foundation] theorem steadyState_zero (D K ΔPL : ℝ) :
    steadyState D K ΔPL 0 = -ΔPL / (K + D) := rfl

@[simp, powerlib_foundation] theorem steadyState_one (D K ΔPL : ℝ) :
    steadyState D K ΔPL 1 = K * ΔPL / (K + D) := rfl

@[powerlib_foundation] theorem field_apply (x : ℝ²) :
    (plant M D K Tg).inputField (load ΔPL) x =
      WithLp.toLp 2 ![-D / M * x 0 + 1 / M * x 1 + -1 / M * ΔPL,
        -K / Tg * x 0 + -1 / Tg * x 1] := by
  rw [LTI.inputField_apply]
  congr 1
  ext i
  fin_cases i <;> simp [plant, load, dotProduct, Fin.sum_univ_two]

/-- Swing row of the model: `M Δω̇ = ΔP_m − ΔP_L − D Δω`. -/
@[powerlib_foundation] theorem field_swing (hM : M ≠ 0) (x : ℝ²) :
    M * (plant M D K Tg).inputField (load ΔPL) x 0 = x 1 - ΔPL - D * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  field_simp
  ring

/-- Governor row of the model: `T_g ΔṖ_m = −ΔP_m − K_R Δω`. -/
@[powerlib_foundation] theorem field_governor (hTg : Tg ≠ 0) (x : ℝ²) :
    Tg * (plant M D K Tg).inputField (load ΔPL) x 1 = -x 1 - K * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

/-! ## Transfer function, characteristic polynomial, `ω_n`, `ζ_n` -/

/-- §1.7: `Δω(s)/ΔP_L(s) = −(1 + T_g s)/(M T_g s² + (M + D T_g) s + (D + K_R))`.
At the poles both sides are `0` (Lean's `x / 0 = 0`), so the identity holds for every `s`. -/
@[powerlib_foundation] theorem transfer_apply (hM : M ≠ 0) (hTg : Tg ≠ 0) (s : ℂ) :
    Linear.transfer (plant M D K Tg) s 0 0 =
      -(1 + (Tg : ℂ) * s) / ((M : ℂ) * Tg * s ^ 2 + (M + D * Tg) * s + (D + K)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  rw [Linear.transfer_eq_adjugate]
  simp [plant, Linear.characteristicMatrix, Matrix.adjugate_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  have key : (M : ℂ) * Tg * s ^ 2 + (M + D * Tg) * s + (D + K) =
      M * Tg * ((s - -D / M) * (s - -1 / Tg) - (M : ℂ)⁻¹ * (-K / Tg)) := by
    field_simp
    ring
  rw [key]
  by_cases h : (s - -(D : ℂ) / M) * (s - -1 / Tg) - (M : ℂ)⁻¹ * (-K / Tg) = 0
  · simp [h]
  · field_simp
    ring

@[powerlib_foundation] theorem det_characteristicMatrix (s : ℂ) :
    (Linear.characteristicMatrix (plant M D K Tg).A s).det =
      s ^ 2 + ((D / M + 1 / Tg : ℝ) : ℂ) * s + (((D + K) / (M * Tg) : ℝ) : ℂ) := by
  simp [plant, Linear.characteristicMatrix, Matrix.det_fin_two]
  ring

@[powerlib_foundation] theorem natFreq_sq (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 ≤ D + K) :
    natFreq M D K Tg ^ 2 = (D + K) / (M * Tg) :=
  Real.sq_sqrt (div_nonneg hKD (mul_pos hM hTg).le)

@[powerlib_foundation] theorem natFreq_pos (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 < D + K) :
    0 < natFreq M D K Tg :=
  Real.sqrt_pos.2 (div_pos hKD (mul_pos hM hTg))

/-- `2 ζ_n ω_n = (M + D T_g)/(M T_g)` (§1.7 boxed). -/
@[powerlib_foundation] theorem two_mul_dampingRatio_mul_natFreq (hM : 0 < M) (hTg : 0 < Tg)
    (hKD : 0 < D + K) :
    2 * dampingRatio M D K Tg * natFreq M D K Tg = (M + D * Tg) / (M * Tg) := by
  have hMT : 0 < M * Tg := mul_pos hM hTg
  have hprod : 0 < M * Tg * (D + K) := mul_pos hMT hKD
  have h1 : Real.sqrt ((D + K) / (M * Tg)) * Real.sqrt (M * Tg * (D + K)) = D + K := by
    rw [← Real.sqrt_mul (div_nonneg hKD.le hMT.le)]
    rw [show (D + K) / (M * Tg) * (M * Tg * (D + K)) = (D + K) ^ 2 by field_simp]
    exact Real.sqrt_sq hKD.le
  have h2 : 0 < Real.sqrt (M * Tg * (D + K)) := Real.sqrt_pos.2 hprod
  have h3 : Real.sqrt (M * Tg * (D + K)) ^ 2 = M * Tg * (D + K) := Real.sq_sqrt hprod.le
  have hr : Real.sqrt ((D + K) / (M * Tg)) = Real.sqrt (M * Tg * (D + K)) / (M * Tg) := by
    rw [eq_div_iff hMT.ne']
    have : Real.sqrt ((D + K) / (M * Tg)) * (M * Tg) * Real.sqrt (M * Tg * (D + K)) =
        Real.sqrt (M * Tg * (D + K)) * Real.sqrt (M * Tg * (D + K)) := by
      rw [mul_right_comm, h1, ← sq, h3]; ring
    exact mul_right_cancel₀ h2.ne' this
  unfold dampingRatio natFreq
  rw [hr]
  field_simp

/-- §1.7 standard second-order form `det(sI − A) = s² + 2 ζ_n ω_n s + ω_n²`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_eq (hM : 0 < M) (hTg : 0 < Tg)
    (hKD : 0 < D + K) (s : ℂ) :
    (Linear.characteristicMatrix (plant M D K Tg).A s).det =
      s ^ 2 + ((2 * dampingRatio M D K Tg * natFreq M D K Tg : ℝ) : ℂ) * s +
        ((natFreq M D K Tg ^ 2 : ℝ) : ℂ) := by
  rw [det_characteristicMatrix, two_mul_dampingRatio_mul_natFreq hM hTg hKD,
    natFreq_sq hM hTg hKD.le]
  have : D / M + 1 / Tg = (M + D * Tg) / (M * Tg) := by
    field_simp
    ring
  rw [this]

/-- §2.5: the damping ratio strictly decreases as the droop gain `K_R` increases. -/
@[powerlib_foundation] theorem dampingRatio_strictAntiOn (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) :
    StrictAntiOn (fun K => dampingRatio M D K Tg) (Ioi (-D)) := by
  intro K₁ h₁ K₂ h₂ hlt
  simp only [mem_Ioi] at h₁ h₂
  have hMT : 0 < M * Tg := mul_pos hM hTg
  have hnum : 0 < M + D * Tg := by nlinarith
  have hs₁ : 0 < Real.sqrt (M * Tg * (D + K₁)) := Real.sqrt_pos.2 (mul_pos hMT (by linarith))
  have hlt' : Real.sqrt (M * Tg * (D + K₁)) < Real.sqrt (M * Tg * (D + K₂)) :=
    Real.sqrt_lt_sqrt (mul_pos hMT (by linarith)).le
      (mul_lt_mul_of_pos_left (by linarith) hMT)
  exact div_lt_div_of_pos_left hnum (by positivity) (by linarith)

/-! ## Quasi-steady state and the state matrix (§1.6) -/

/-- §1.6: the equilibria for the load step `ΔP_L` are exactly the quasi-steady state. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem isEquilibrium_iff (hM : M ≠ 0) (hTg : Tg ≠ 0) (hKD : K + D ≠ 0)
    (e : ℝ²) :
    IsEquilibrium ((plant M D K Tg).inputField (load ΔPL)) e ↔ e = steadyState D K ΔPL := by
  unfold IsEquilibrium
  rw [field_apply]
  constructor
  · intro h
    have h0 := congrArg (fun v : ℝ² => v 0) h
    have h1 := congrArg (fun v : ℝ² => v 1) h
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply] at h0 h1
    field_simp at h0 h1
    have he1 : e 1 = -(K * e 0) := by linarith
    have he0 : e 0 = -ΔPL / (K + D) := by
      field_simp
      nlinarith
    ext i; fin_cases i
    · simpa using he0
    · simp only [Fin.mk_one, Fin.isValue, steadyState_one]
      rw [he1, he0]
      ring
  · rintro rfl
    ext i; fin_cases i
    · simp [steadyState]
      field_simp
      ring
    · simp [steadyState]
      field_simp
      ring

/-- The quasi-steady state is an equilibrium of the load step. Static evidence on the model, not
a connection conclusion. -/
@[powerlib_foundation] theorem steadyState_isEquilibrium (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hKD : K + D ≠ 0) :
    IsEquilibrium ((plant M D K Tg).inputField (load ΔPL)) (steadyState D K ΔPL) :=
  (isEquilibrium_iff hM hTg hKD _).2 rfl

/-- For `0 < M`, `0 < T_g`: Hurwitz iff `0 < M + D T_g` (trace) and `0 < K_R + D`
(determinant). -/
@[powerlib_foundation] theorem isHurwitz_iff (hM : 0 < M) (hTg : 0 < Tg) :
    IsHurwitz (plant M D K Tg).A ↔ 0 < M + D * Tg ∧ 0 < K + D := by
  change IsHurwitz !![-D / M, 1 / M; -K / Tg, -1 / Tg] ↔ _
  rw [Criteria.isHurwitz_fin_two_of_iff]
  have htr : -D / M + -1 / Tg = -((M + D * Tg) / (M * Tg)) := by
    field_simp
    ring
  have hdet : -D / M * (-1 / Tg) - 1 / M * (-K / Tg) = (K + D) / (M * Tg) := by
    field_simp
    ring
  rw [htr, hdet, neg_lt_zero, div_pos_iff_of_pos_right (mul_pos hM hTg),
    div_pos_iff_of_pos_right (mul_pos hM hTg)]

/-- For `0 < M`, `0 < T_g`, `0 ≤ D`: Hurwitz iff `0 < K_R + D`. -/
@[powerlib_foundation] theorem isHurwitz_iff_of_nonneg (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D) :
    IsHurwitz (plant M D K Tg).A ↔ 0 < K + D := by
  rw [isHurwitz_iff hM hTg]
  exact ⟨fun h => h.2, fun h => ⟨by nlinarith, h⟩⟩

@[powerlib_foundation] theorem trace_plant :
    (plant M D K Tg).A.trace = -D / M + -1 / Tg := Matrix.trace_fin_two_of _ _ _ _

@[powerlib_foundation] theorem det_plant (hM : M ≠ 0) (hTg : Tg ≠ 0) :
    (plant M D K Tg).A.det = (K + D) / (M * Tg) := by
  change Matrix.det !![-D / M, 1 / M; -K / Tg, -1 / Tg] = _
  rw [Matrix.det_fin_two_of]
  field_simp
  ring

/-- A positive-trace or negative-determinant state matrix has a characteristic root in the open
right half plane. -/
@[powerlib_foundation] theorem exists_root_of_unstable (hM : 0 < M) (hTg : 0 < Tg)
    (h : K + D < 0 ∨ M + D * Tg < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix (plant M D K Tg).A s).det = 0 ∧ 0 < s.re := by
  rcases h with h | h
  · refine Criteria.exists_characteristic_root_re_pos_of_det_neg _ ?_
    rw [det_plant hM.ne' hTg.ne']
    exact div_neg_of_neg_of_pos h (mul_pos hM hTg)
  · refine Criteria.exists_characteristic_root_re_pos_of_trace_pos _ ?_
    rw [trace_plant]
    have : -D / M + -1 / Tg = -((M + D * Tg) / (M * Tg)) := by
      field_simp
      ring
    rw [this, neg_pos]
    exact div_neg_of_neg_of_pos h (mul_pos hM hTg)

/-! ## The family -/

/-- A swing + governor model: inertia `M > 0`, damping `D`, aggregate droop gain `K_R`, governor
time constant `T_g > 0`. -/
structure Model where
  /-- Inertia `M_eff = 2 H_eff` [s]. -/
  M : ℝ
  /-- Damping `D_eff`. -/
  D : ℝ
  /-- Aggregate droop gain `K_R`. -/
  K : ℝ
  /-- Governor time constant `T_g` [s]. -/
  Tg : ℝ
  M_pos : 0 < M
  Tg_pos : 0 < Tg

/-- The plant of a model. -/
def Model.plant (m : Model) : Linear.Plant 2 1 := SwingGovernor.plant m.M m.D m.K m.Tg

/-- Requirements on the swing + governor models, all static. -/
inductive Requirement
  /-- Trace `< 0` and determinant `> 0`: `0 < M + D T_g` and `0 < K_R + D`. -/
  | stable
  /-- Determinant `< 0` or trace `> 0`: `K_R + D < 0` or `M + D T_g < 0`. -/
  | unstable
  /-- A strict spectral margin at the rate `a`. -/
  | rate (a : ℝ)

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .stable => 0 < m.M + m.D * m.Tg ∧ 0 < m.K + m.D
  | .unstable => m.K + m.D < 0 ∨ m.M + m.D * m.Tg < 0
  | .rate a => Linear.RateMargin m.plant.A a

/-- The translation of the sentences: Lyapunov stability, the attractive sentences and sampled
contraction into `stable`, instability into `unstable`, a decay rate into its margin.
Conservation and passivity are translated into the whole language, which no model meets
(unavailable translation coverage, not a usable translation). -/
def translate : Sentence → Set Requirement
  | .flow .unstable => {.unstable}
  | .flow (.decay a) => {.rate a}
  | .flow .conservative => Set.univ
  | .flow _ => {.stable}
  | .passive => Set.univ
  | .envelope _ => ∅

/-- The swing + governor family: every model read as the port system of its plant (load
deviation in, frequency deviation out). -/
def family : Family Model Requirement 2 1 := ⟨fun m => m.plant.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear Model.plant := fun _ => rfl

/-- No model is both stable and unstable: the whole requirement language is inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  obtain ⟨h1, h2⟩ : Meets m .stable := h .stable
  rcases (h .unstable : Meets m .unstable) with h3 | h3 <;> linarith

/-- The attractive sentences and sampled contraction denote the members satisfying `stable`. -/
private theorem den_hurwitz {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.den (.flow P) = {m | Meets m .stable}) := by
  change family.den (.flow P) = {m | Meets m .stable}
  rw [family_isLinear.den_hurwitz hP]
  ext m
  exact isHurwitz_iff m.M_pos m.Tg_pos

private theorem stable_mem_den {m : Model} (h : Meets m .stable) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ family.den (.flow P)) := by
  change m ∈ family.den (.flow P)
  rw [den_hurwitz hP]
  exact h

/-- The swing + governor translation is the linear table of `theorem/Spectral/LinearNamed.lean`. -/
private theorem translate_eq_linearTable (s : Sentence) :
    translate s = Spectral.linearTable {.stable} {.unstable} univ univ (fun a => {.rate a}) s := by
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- Every translation of the swing + governor family is sound: its translation chain lies below
its semantics connection. `stable` is the Hurwitz condition of the plant, a right-half-plane root
gives instability, a spectral margin gives the decay rate (the linear table,
`Spectral.chain_le_semantics_of_linearTable_univ`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.chain_le_semantics_of_linearTable_univ (F := family) family_isLinear
    translate_eq_linearTable
    (fun m hm => (isHurwitz_iff m.M_pos m.Tg_pos).mpr ((mem_realize _ _ _).mp hm .stable rfl))
    (fun m hm => exists_root_of_unstable m.M_pos m.Tg_pos
      ((mem_realize _ _ _).mp hm .unstable rfl))
    fun a m hm => family_isLinear.mem_den_decay_of_rateMargin
      ((mem_realize _ _ _).mp hm (.rate a) rfl)

/-- On the attractive sentences and sampled contraction the chain agrees with the semantics:
`stable` (`0 < M + D T_g`, `0 < K_R + D`) is their exact translation. -/
@[tmio TM, powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.exact_of_linearTable (F := family) family_isLinear translate_eq_linearTable
    (fun m => Spectral.mem_realize_singleton.trans (isHurwitz_iff m.M_pos m.Tg_pos).symm) hP

/-- The member characterization: a model satisfies an attractive sentence exactly when
`0 < M + D T_g` and `0 < K_R + D`. -/
@[tmio TM, powerlib_domain] theorem mem_den_attractive_iff (m : Model) {P : Flow.Property}
    (hP : P.Attractive) :
    connection% (m ∈ family.den (.flow P) ↔
      m ∈ {m : Model | 0 < m.M + m.D * m.Tg ∧ 0 < m.K + m.D}) := by
  unfold powerlib.TMIO.Statement
  rw [den_hurwitz (Or.inl hP)]
  rfl

/-- §1.6: with nonnegative damping, `0 < K_R + D` makes the zero-load operating point globally
exponentially stable; by linearity so is the quasi-steady state of every constant load step. -/
@[tmio TM, powerlib_domain] theorem mem_den_globallyExponentiallyStable (m : Model) (hD : 0 ≤ m.D)
    (hKD : 0 < m.K + m.D) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine stable_mem_den ⟨?_, hKD⟩ (Or.inl (by simp))
  nlinarith [m.M_pos, m.Tg_pos]

/-- A negative determinant (`K_R + D < 0`) or a positive trace (`M + D T_g < 0`) places a model
in instability. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (h : m.K + m.D < 0 ∨ m.M + m.D * m.Tg < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨s, hs, hre⟩ := exists_root_of_unstable m.M_pos m.Tg_pos h
  exact family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 hs hre)

/-- With `0 < K_R + D` the model is not passive on its `(ΔP_L, Δω)` port: under the constant
load `ΔP_L = 1` the quasi-steady state is an equilibrium at which the port supplies
`ΔP_L Δω^∞ = −1/(K_R + D) < 0`. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_passive (m : Model) (hKD : 0 < m.K + m.D) :
    connection% (m ∉ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den), family_isLinear m, Sentence.holds_passive]
  refine Port.System.not_passive_of_equilibrium _ (x₀ := steadyState m.D m.K 1) (u₀ := load 1)
    (steadyState_isEquilibrium m.M_pos.ne' m.Tg_pos.ne' hKD.ne') ?_
  have hsupply : m.plant.system.supply (steadyState m.D m.K 1) (load 1) = -1 / (m.K + m.D) := by
    simp [Port.System.supply, Model.plant, plant, Linear.Plant.system, load, steadyState,
      dotProduct, Fin.sum_univ_two]
  rw [hsupply]
  exact div_neg_of_neg_of_pos (by norm_num) hKD

/-! ## Implementation evidence (private, trajectory level)

The initial rate of change of frequency and the convergence of the frequency deviation of a
forward solution under a load step are trajectory-level results outside the sentence language
(Rules §3a). -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.5: from rest, the right derivative of `Δω` at `0⁺` is `−ΔP_L / M_eff`. -/
private theorem rocof {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => x t 0) (-ΔPL / M) (Ici 0) 0 := by
  have h := LTI.hasDerivWithinAt_apply_zero hx 0
  rw [field_apply, h0] at h
  convert h using 1
  simp only [Fin.isValue, Matrix.cons_val_zero, PiLp.zero_apply]
  ring

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.5 in Hz/s: with `f = f₀ (1 + Δω)` and `M_eff = 2 H_eff`, `ḟ(0⁺) = −ΔP_L f₀ / (2 H_eff)`. -/
private theorem rocof_hz {H f₀ : ℝ} {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant (2 * H) D K Tg).inputField (load ΔPL) y)
      (Ici 0)) (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => f₀ * (1 + x t 0)) (-(ΔPL * f₀) / (2 * H)) (Ici 0) 0 := by
  have h := ((rocof hx h0).const_add 1).const_mul f₀
  convert h using 1
  ring

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.6 boxed: `Δω(t) → Δω^∞ = −ΔP_L/(K_R + D_eff)` along every forward solution under the load
step, read from the connection theorem `mem_den_globallyExponentiallyStable` and linearity. -/
private theorem tendsto_freq (m : Model) (hD : 0 ≤ m.D) (hKD : 0 < m.K + m.D) {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => m.plant.inputField (load ΔPL) y) (Ici 0)) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ΔPL / (m.K + m.D))) := by
  have hmem := mem_den_globallyExponentiallyStable m hD hKD
  unfold powerlib.TMIO.Statement at hmem
  have hA : IsHurwitz m.plant.A := by
    rw [family_isLinear.den_hurwitz (Or.inl (by simp))] at hmem
    exact hmem
  have h := LTI.tendsto_apply_of_isHurwitz m.plant
    (steadyState_isEquilibrium m.M_pos.ne' m.Tg_pos.ne' hKD.ne') hA hx 0
  simpa using h

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.6 at the trajectory level: every solution under the load step converges exponentially to the
quasi-steady state, read from the connection theorem `mem_den_globallyExponentiallyStable` and
linearity (`Linear.holds_input_iff`). -/
private theorem exponentiallyConvergesTo_steadyState (m : Model) (hD : 0 ≤ m.D)
    (hKD : 0 < m.K + m.D) (ΔPL : ℝ) :
    Flow.GloballyExponentiallyStable (m.plant.inputField (load ΔPL))
      (steadyState m.D m.K ΔPL) := by
  have hmem := mem_den_globallyExponentiallyStable m hD hKD
  unfold powerlib.TMIO.Statement at hmem
  rw [family_isLinear.den_hurwitz (Or.inl (by simp))] at hmem
  exact (Linear.holds_input_iff m.plant
    (steadyState_isEquilibrium m.M_pos.ne' m.Tg_pos.ne' hKD.ne')
    (P := .globallyExponentiallyStable) (by simp)).2 hmem

/-! ## Singular-perturbation limit `T_g → 0` -/

/-- The reduced first-order swing model (`T_g = 0`: instantaneous droop `ΔP_m = −K_R Δω`):
`M Δω̇ = −(K_R + D) Δω − ΔP_L`; state `Δω`, input `ΔP_L`, output `Δω`. -/
def reducedPlant (M D K : ℝ) : Linear.Plant 1 1 where
  A := !![-(K + D) / M]
  B := !![-1 / M]
  C := !![1]
  D := 0

/-- The swing + governor model as a linear two-time-scale system: slow state `Δω`, fast state
`ΔP_m`, small parameter `ε = T_g`: `Δω̇ = −(D/M) Δω + (1/M) ΔP_m`, `T_g ΔṖ_m = −K_R Δω − ΔP_m`. -/
def twoTimeScale (M D K : ℝ) : SingularPerturbation.LinearSP 1 1 where
  A11 := !![-D / M]
  A12 := !![1 / M]
  A21 := !![-K]
  A22 := !![-1]

/-- Discriminant of `M T_g s² + (M + D T_g) s + (D + K_R)`. -/
def eigDisc (M D K Tg : ℝ) : ℝ := (M + D * Tg) ^ 2 - 4 * M * Tg * (D + K)

/-- The slow characteristic root `λ_s = −2 (D + K_R)/(M + D T_g + √disc)` (rationalized form of
`(−(M + D T_g) + √disc)/(2 M T_g)`; it stays bounded as `T_g → 0`). -/
def slowEig (M D K Tg : ℝ) : ℝ := -(2 * (D + K)) / (M + D * Tg + Real.sqrt (eigDisc M D K Tg))

/-- The fast characteristic root `λ_f = −(M + D T_g + √disc)/(2 M T_g)`. -/
def fastEig (M D K Tg : ℝ) : ℝ := -(M + D * Tg + Real.sqrt (eigDisc M D K Tg)) / (2 * M * Tg)

/-- The state matrix is the two-time-scale state matrix at `ε = T_g`. -/
@[powerlib_foundation] theorem plant_A_eq_stateMatrix :
    (plant M D K Tg).A = (twoTimeScale M D K).stateMatrix Tg := by
  have h0 : (finSumFinEquiv.symm (0 : Fin (1 + 1)) : Fin 1 ⊕ Fin 1) = Sum.inl 0 := rfl
  have h1 : (finSumFinEquiv.symm (1 : Fin (1 + 1)) : Fin 1 ⊕ Fin 1) = Sum.inr 0 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plant, twoTimeScale, SingularPerturbation.LinearSP.stateMatrix,
      SingularPerturbation.LinearSP.blockMatrix, h0, h1] <;> ring

private theorem inv_neg_one_fin_one : (!![(-1 : ℝ)])⁻¹ = !![-1] :=
  Matrix.inv_eq_left_inv (by ext i j; fin_cases i; fin_cases j; simp)

/-- The quasi-steady-state gain is `K_R`: the slow manifold of the reduction is
`ΔP_m = −K_R Δω`. -/
@[powerlib_foundation] theorem twoTimeScale_gain : (twoTimeScale M D K).gain = !![K] := by
  rw [SingularPerturbation.LinearSP.gain, twoTimeScale]
  simp only
  rw [inv_neg_one_fin_one]
  ext i j; fin_cases i; fin_cases j; simp

/-- The reduced (Schur-complement) matrix is the first-order swing matrix `−(K_R + D)/M`. -/
@[powerlib_foundation] theorem twoTimeScale_reducedMatrix :
    (twoTimeScale M D K).reducedMatrix = (reducedPlant M D K).A := by
  rw [SingularPerturbation.LinearSP.reducedMatrix, twoTimeScale]
  simp only
  rw [inv_neg_one_fin_one]
  ext i j; fin_cases i; fin_cases j
  simp [reducedPlant]
  ring

/-- The boundary-layer matrix `−1` (governor time scale) is Hurwitz. -/
@[powerlib_foundation] theorem twoTimeScale_A22_isHurwitz :
    IsHurwitz (twoTimeScale M D K).A22 :=
  (Linear.isHurwitz_one_iff (-1)).2 (by norm_num)

/-! ### Characteristic roots -/

private theorem root_aux (hΔ : 0 ≤ eigDisc M D K Tg) :
    (M + D * Tg + Real.sqrt (eigDisc M D K Tg)) ^ 2
      - 2 * (M + D * Tg) * (M + D * Tg + Real.sqrt (eigDisc M D K Tg))
      + 4 * M * Tg * (D + K) = 0 := by
  have hs := Real.sq_sqrt hΔ
  unfold eigDisc at hs ⊢
  linear_combination hs

/-- The slow root solves `M T_g λ² + (M + D T_g) λ + (D + K_R) = 0`. -/
@[powerlib_foundation] theorem slowEig_root (hΔ : 0 ≤ eigDisc M D K Tg)
    (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) :
    M * Tg * slowEig M D K Tg ^ 2 + (M + D * Tg) * slowEig M D K Tg + (D + K) = 0 := by
  have h := root_aux hΔ
  set S := M + D * Tg + Real.sqrt (eigDisc M D K Tg) with hSdef
  have hl : slowEig M D K Tg * S = -(2 * (D + K)) := by
    rw [slowEig, ← hSdef]
    field_simp
  apply mul_left_cancel₀ (pow_ne_zero 2 hS)
  linear_combination (D + K) * h +
    (M * Tg * (slowEig M D K Tg * S - 2 * (D + K)) + (M + D * Tg) * S) * hl

/-- The fast root solves `M T_g λ² + (M + D T_g) λ + (D + K_R) = 0`. -/
@[powerlib_foundation] theorem fastEig_root (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hΔ : 0 ≤ eigDisc M D K Tg) :
    M * Tg * fastEig M D K Tg ^ 2 + (M + D * Tg) * fastEig M D K Tg + (D + K) = 0 := by
  have h := root_aux hΔ
  unfold fastEig
  field_simp
  linear_combination h

/-- The slow root is the textbook root `(−(M + D T_g) + √disc)/(2 M T_g)`. -/
@[powerlib_foundation] theorem slowEig_eq (hM : M ≠ 0) (hTg : Tg ≠ 0) (hΔ : 0 ≤ eigDisc M D K Tg)
    (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) :
    slowEig M D K Tg = (-(M + D * Tg) + Real.sqrt (eigDisc M D K Tg)) / (2 * M * Tg) := by
  have h := root_aux hΔ
  unfold slowEig
  rw [div_eq_div_iff hS (by simp [hM, hTg])]
  linear_combination -h

/-- `λ_s − λ_f = √disc/(M T_g)`: for positive discriminant the fast root lies strictly below the
slow root. -/
@[powerlib_foundation] theorem slowEig_sub_fastEig (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hΔ : 0 ≤ eigDisc M D K Tg) (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) :
    slowEig M D K Tg - fastEig M D K Tg = Real.sqrt (eigDisc M D K Tg) / (M * Tg) := by
  rw [slowEig_eq hM hTg hΔ hS, fastEig]
  field_simp
  ring

/-- Vieta: `λ_s + λ_f = −(D/M + 1/T_g)`, `λ_s λ_f = (D + K_R)/(M T_g)`. -/
@[powerlib_foundation] theorem slowEig_add_fastEig (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hΔ : 0 ≤ eigDisc M D K Tg) (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) :
    slowEig M D K Tg + fastEig M D K Tg = -(D / M + 1 / Tg) := by
  rw [slowEig_eq hM hTg hΔ hS, fastEig]
  field_simp
  ring

@[powerlib_foundation] theorem slowEig_mul_fastEig (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) :
    slowEig M D K Tg * fastEig M D K Tg = (D + K) / (M * Tg) := by
  unfold slowEig fastEig
  field_simp

/-- For a nonnegative discriminant the characteristic polynomial factors over the two real
roots: `det(sI − A) = (s − λ_s)(s − λ_f)`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_eq_mul (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hΔ : 0 ≤ eigDisc M D K Tg) (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) (s : ℂ) :
    (Linear.characteristicMatrix (plant M D K Tg).A s).det =
      (s - slowEig M D K Tg) * (s - fastEig M D K Tg) := by
  rw [det_characteristicMatrix]
  have e1 : ((D / M + 1 / Tg : ℝ) : ℂ) = -((slowEig M D K Tg : ℂ) + fastEig M D K Tg) := by
    rw [← Complex.ofReal_add, slowEig_add_fastEig hM hTg hΔ hS, Complex.ofReal_neg, neg_neg]
  have e2 : (((D + K) / (M * Tg) : ℝ) : ℂ) = (slowEig M D K Tg : ℂ) * fastEig M D K Tg := by
    rw [← Complex.ofReal_mul, slowEig_mul_fastEig hM hTg hS]
  rw [e1, e2]
  ring

/-- The characteristic roots are exactly `λ_s` and `λ_f` (nonnegative discriminant). -/
@[powerlib_foundation] theorem det_characteristicMatrix_eq_zero_iff (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hΔ : 0 ≤ eigDisc M D K Tg) (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) (s : ℂ) :
    (Linear.characteristicMatrix (plant M D K Tg).A s).det = 0 ↔
      s = slowEig M D K Tg ∨ s = fastEig M D K Tg := by
  rw [det_characteristicMatrix_eq_mul hM hTg hΔ hS, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The slow eigenvector `(1, M λ_s + D)`: the invariant slow line of the model is
`ΔP_m = (M λ_s + D) Δω`. -/
@[powerlib_foundation] theorem plant_mulVec_slowEigvec (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hΔ : 0 ≤ eigDisc M D K Tg) (hS : M + D * Tg + Real.sqrt (eigDisc M D K Tg) ≠ 0) :
    (plant M D K Tg).A *ᵥ ![1, M * slowEig M D K Tg + D] =
      slowEig M D K Tg • ![1, M * slowEig M D K Tg + D] := by
  have hr := slowEig_root hΔ hS
  ext i
  fin_cases i
  · simp [plant, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [plant, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination -hr

/-! ### Limits as `T_g → 0` -/

@[powerlib_foundation] theorem eigDisc_zero : eigDisc M D K 0 = M ^ 2 := by
  simp [eigDisc]

@[powerlib_foundation] theorem continuous_eigDisc : Continuous (fun Tg => eigDisc M D K Tg) := by
  unfold eigDisc
  fun_prop

private theorem continuous_rootSum :
    Continuous (fun Tg => M + D * Tg + Real.sqrt (eigDisc M D K Tg)) :=
  (continuous_const.add (continuous_const.mul continuous_id)).add
    (Real.continuous_sqrt.comp continuous_eigDisc)

private theorem rootSum_zero (hM : 0 < M) :
    M + D * 0 + Real.sqrt (eigDisc M D K 0) = 2 * M := by
  rw [eigDisc_zero, Real.sqrt_sq hM.le]
  ring

/-- For small `T_g` the discriminant is positive: both characteristic roots are real and
distinct (the oscillatory mode of §1.7 disappears in the limit). -/
@[powerlib_foundation] theorem eventually_eigDisc_pos (hM : M ≠ 0) :
    ∀ᶠ Tg in 𝓝 0, 0 < eigDisc M D K Tg := by
  have h := (continuous_eigDisc (M := M) (D := D) (K := K)).tendsto 0
  rw [eigDisc_zero] at h
  exact h.eventually_const_lt (by positivity)

@[powerlib_foundation] theorem eventually_rootSum_pos (hM : 0 < M) :
    ∀ᶠ Tg in 𝓝 0, 0 < M + D * Tg + Real.sqrt (eigDisc M D K Tg) := by
  have h := (continuous_rootSum (M := M) (D := D) (K := K)).tendsto 0
  rw [rootSum_zero hM] at h
  exact h.eventually_const_lt (by positivity)

/-- At `T_g = 0` the slow root is the pole `−(K_R + D)/M` of the first-order model. -/
@[powerlib_foundation] theorem slowEig_zero (hM : 0 < M) : slowEig M D K 0 = -(K + D) / M := by
  rw [slowEig, rootSum_zero hM]
  field_simp
  ring

/-- **Slow eigenvalue limit**: `λ_s(T_g) → −(K_R + D)/M` as `T_g → 0` (the slow root is
continuous at `T_g = 0`, where it equals the first-order pole). -/
@[powerlib_foundation] theorem tendsto_slowEig (hM : 0 < M) :
    Tendsto (fun Tg => slowEig M D K Tg) (𝓝 0) (𝓝 (-(K + D) / M)) := by
  have hc : ContinuousAt (fun Tg => slowEig M D K Tg) 0 := by
    unfold slowEig
    refine continuousAt_const.div continuous_rootSum.continuousAt ?_
    rw [rootSum_zero hM]
    positivity
  have h := hc.tendsto
  rwa [slowEig_zero hM] at h

/-- The invariant slow line `ΔP_m = (M λ_s + D) Δω` tends to the quasi-steady-state line
`ΔP_m = −K_R Δω` of the reduction. -/
@[powerlib_foundation] theorem tendsto_slowSlope (hM : 0 < M) :
    Tendsto (fun Tg => M * slowEig M D K Tg + D) (𝓝 0) (𝓝 (-K)) := by
  have h := ((tendsto_slowEig (D := D) (K := K) hM).const_mul M).add_const D
  convert h using 2
  field_simp
  ring

@[powerlib_foundation] theorem mul_fastEig (hM : M ≠ 0) (hTg : Tg ≠ 0) :
    Tg * fastEig M D K Tg = -(M + D * Tg + Real.sqrt (eigDisc M D K Tg)) / (2 * M) := by
  unfold fastEig
  field_simp

/-- **Fast eigenvalue limit**: `T_g λ_f(T_g) → −1`, i.e. `λ_f = −1/T_g + O(1)` (the governor
time scale). -/
@[powerlib_foundation] theorem tendsto_mul_fastEig (hM : 0 < M) :
    Tendsto (fun Tg => Tg * fastEig M D K Tg) (𝓝[≠] 0) (𝓝 (-1)) := by
  have hc : Tendsto (fun Tg => -(M + D * Tg + Real.sqrt (eigDisc M D K Tg)) / (2 * M)) (𝓝 0)
      (𝓝 (-1)) := by
    have h := ((continuous_rootSum (M := M) (D := D) (K := K)).tendsto 0).neg.div_const (2 * M)
    rw [rootSum_zero hM] at h
    convert h using 2
    field_simp
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Tg hTg
  exact (mul_fastEig hM.ne' hTg).symm

/-- `λ_f(T_g) → −∞` as `T_g → 0⁺`. -/
@[powerlib_foundation] theorem tendsto_fastEig_atBot (hM : 0 < M) :
    Tendsto (fun Tg => fastEig M D K Tg) (𝓝[>] 0) atBot := by
  have h := ((tendsto_mul_fastEig (D := D) (K := K) hM).mono_left
    (nhdsWithin_mono _ fun x (hx : 0 < x) => hx.ne')).neg_mul_atTop (by norm_num)
    tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Tg (hTg : 0 < Tg)
  field_simp

/-- §1.7 damping ratio in the limit: `ζ_n → ∞` as `T_g → 0⁺` (for `0 < K_R + D`): the
second-order response becomes overdamped. -/
@[powerlib_foundation] theorem tendsto_dampingRatio_atTop (hM : 0 < M) (hKD : 0 < D + K) :
    Tendsto (fun Tg => dampingRatio M D K Tg) (𝓝[>] 0) atTop := by
  have hnum : Tendsto (fun Tg => M + D * Tg) (𝓝[>] 0) (𝓝 M) := by
    have h : Continuous (fun Tg : ℝ => M + D * Tg) := by fun_prop
    exact (h.tendsto' 0 M (by simp)).mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun Tg => 2 * Real.sqrt (M * Tg * (D + K))) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Continuous (fun Tg => 2 * Real.sqrt (M * Tg * (D + K))) := by fun_prop
      have h0 := h.tendsto 0
      simp only [mul_zero, zero_mul, Real.sqrt_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with Tg (hTg : 0 < Tg)
      exact mul_pos two_pos (Real.sqrt_pos.2 (by positivity))
  have h := Filter.Tendsto.pos_mul_atTop hM hnum (tendsto_inv_nhdsGT_zero.comp hden)
  refine h.congr' ?_
  filter_upwards with Tg
  simp [dampingRatio, div_eq_mul_inv]

/-! ### The reduced model, transfer function and stability -/

@[powerlib_foundation] theorem reduced_field_apply (x : EuclideanSpace ℝ (Fin 1)) :
    (reducedPlant M D K).inputField (load ΔPL) x =
      WithLp.toLp 2 ![-(K + D) / M * x 0 + -1 / M * ΔPL] := by
  rw [LTI.inputField_apply]
  congr 1
  ext i
  fin_cases i
  simp [reducedPlant, load, dotProduct]

/-- On the quasi-steady-state line `ΔP_m = −K_R Δω` the governor row vanishes and the swing row is
the first-order field: `M Δω̇ = −(K_R + D) Δω − ΔP_L`. -/
@[powerlib_foundation] theorem field_quasiSteady (w : ℝ) :
    (plant M D K Tg).inputField (load ΔPL) (WithLp.toLp 2 ![w, -K * w]) 0 =
        (reducedPlant M D K).inputField (load ΔPL) (WithLp.toLp 2 ![w]) 0 ∧
      (plant M D K Tg).inputField (load ΔPL) (WithLp.toLp 2 ![w, -K * w]) 1 = 0 := by
  rw [field_apply, reduced_field_apply]
  constructor
  · simp
    ring
  · simp
    ring

/-- Transfer function of the first-order model: `Δω(s)/ΔP_L(s) = −1/(M s + K_R + D)` (both
sides `0` at the pole). -/
@[powerlib_foundation] theorem reduced_transfer_apply (hM : M ≠ 0) (s : ℂ) :
    Linear.transfer (reducedPlant M D K) s 0 0 = -1 / ((M : ℂ) * s + (K + D)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hdet : (Linear.characteristicMatrix (reducedPlant M D K).A s).det = s + (K + D) / M := by
    simp [reducedPlant, Linear.characteristicMatrix]
    ring
  have hadj : (Linear.complexify (reducedPlant M D K).C *
      (Linear.characteristicMatrix (reducedPlant M D K).A s).adjugate *
        Linear.complexify (reducedPlant M D K).B) 0 0 = -1 / M := by
    simp [reducedPlant, Matrix.adjugate_fin_one, Matrix.mul_apply, Linear.complexify]
  have hD : Linear.complexify (reducedPlant M D K).D 0 0 = 0 := by simp [reducedPlant]
  rw [Linear.transfer_eq_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, hadj, hD, smul_eq_mul, add_zero, hdet]
  have key : (M : ℂ) * s + (K + D) = M * (s + (K + D) / M) := by field_simp
  rw [key]
  by_cases h : s + ((K : ℂ) + D) / M = 0
  · rw [h]; simp
  · field_simp

/-- **Transfer function limit**: off the first-order pole, the load-to-frequency transfer
function of the swing + governor model tends to that of the first-order model as `T_g → 0`. -/
@[powerlib_foundation] theorem tendsto_transfer (hM : M ≠ 0) {s : ℂ}
    (hs : (M : ℂ) * s + (K + D) ≠ 0) :
    Tendsto (fun Tg => Linear.transfer (plant M D K Tg) s 0 0) (𝓝[≠] 0)
      (𝓝 (Linear.transfer (reducedPlant M D K) s 0 0)) := by
  rw [reduced_transfer_apply hM]
  have hc : ContinuousAt (fun Tg : ℝ => -(1 + (Tg : ℂ) * s) /
      ((M : ℂ) * Tg * s ^ 2 + (M + D * Tg) * s + (D + K))) 0 := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero, zero_add]
    rwa [add_comm (D : ℂ) K]
  have h := hc.tendsto
  have e : -(1 + ((0 : ℝ) : ℂ) * s) / ((M : ℂ) * ((0 : ℝ) : ℂ) * s ^ 2 +
      (M + D * ((0 : ℝ) : ℂ)) * s + (D + K)) = -1 / ((M : ℂ) * s + (K + D)) := by
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero, zero_add]
    rw [add_comm (D : ℂ) K]
  rw [e] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Tg hTg
  exact (transfer_apply hM hTg s).symm

/-- The first-order model is Hurwitz iff `0 < K_R + D`. -/
@[powerlib_foundation] theorem reduced_isHurwitz_iff (hM : 0 < M) :
    IsHurwitz (reducedPlant M D K).A ↔ 0 < K + D := by
  change IsHurwitz !![-(K + D) / M] ↔ _
  rw [Linear.isHurwitz_one_iff, neg_div, neg_lt_zero, div_pos_iff_of_pos_right hM]

/-- **Stability is inherited from the first-order model** whenever `0 < M + D T_g` (in particular
for every `T_g` when `0 ≤ D`, and for every small `T_g`). -/
@[powerlib_foundation] theorem isHurwitz_iff_reduced (hM : 0 < M) (hTg : 0 < Tg)
    (h : 0 < M + D * Tg) :
    IsHurwitz (plant M D K Tg).A ↔ IsHurwitz (reducedPlant M D K).A := by
  rw [isHurwitz_iff hM hTg, reduced_isHurwitz_iff hM]
  exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

@[powerlib_foundation] theorem eventually_isHurwitz_iff_reduced (hM : 0 < M) :
    ∀ᶠ Tg in 𝓝[>] 0, IsHurwitz (plant M D K Tg).A ↔ IsHurwitz (reducedPlant M D K).A := by
  have hc : Continuous (fun Tg : ℝ => M + D * Tg) := by fun_prop
  have h : ∀ᶠ Tg in 𝓝 0, 0 < M + D * Tg := (hc.tendsto' 0 M (by simp)).eventually_const_lt hM
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with Tg h1 (h2 : 0 < Tg)
  exact isHurwitz_iff_reduced hM h2 h1

/-- The rate margin of the swing + governor model: `A + aI` Hurwitz iff
`T_g (2 a M − D) < M` and `0 < K_R + D − a M + a T_g (a M − D)`. -/
@[powerlib_foundation] theorem rateMargin_iff (hM : 0 < M) (hTg : 0 < Tg) (a : ℝ) :
    Linear.RateMargin (plant M D K Tg).A a ↔
      Tg * (2 * a * M - D) < M ∧ 0 < K + D - a * M + a * Tg * (a * M - D) := by
  unfold Linear.RateMargin
  have hA : (plant M D K Tg).A + a • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-D / M + a, 1 / M; -K / Tg, -1 / Tg + a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [plant]
  have hMT : 0 < M * Tg := mul_pos hM hTg
  have htr : -D / M + a + (-1 / Tg + a) = (Tg * (2 * a * M - D) - M) / (M * Tg) := by
    field_simp
    ring
  have hdet : (-D / M + a) * (-1 / Tg + a) - 1 / M * (-K / Tg) =
      (K + D - a * M + a * Tg * (a * M - D)) / (M * Tg) := by
    field_simp
    ring
  rw [hA, Criteria.isHurwitz_fin_two_of_iff, htr, hdet, div_lt_iff₀ hMT, zero_mul, sub_neg,
    div_pos_iff_of_pos_right hMT]

/-- The rate margin of the first-order model: `a M < K_R + D`. -/
@[powerlib_foundation] theorem reduced_rateMargin_iff (hM : 0 < M) (a : ℝ) :
    Linear.RateMargin (reducedPlant M D K).A a ↔ a * M < K + D := by
  unfold Linear.RateMargin
  have hA : (reducedPlant M D K).A + a • (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      !![(a * M - (K + D)) / M] := by
    ext i j
    fin_cases i; fin_cases j
    simp [reducedPlant]
    field_simp
    ring
  rw [hA, Linear.isHurwitz_one_iff, div_lt_iff₀ hM, zero_mul, sub_neg]

/-- **Rate margins converge**: off the first-order pole (`a M ≠ K_R + D`), for small `T_g` the
swing + governor model has the rate margin `a` exactly when the first-order model has it. -/
@[powerlib_foundation] theorem eventually_rateMargin_iff_reduced (hM : 0 < M) {a : ℝ}
    (ha : a * M ≠ K + D) :
    ∀ᶠ Tg in 𝓝[>] 0, Linear.RateMargin (plant M D K Tg).A a ↔
      Linear.RateMargin (reducedPlant M D K).A a := by
  have hc1 : Continuous (fun Tg : ℝ => Tg * (2 * a * M - D)) := by fun_prop
  have hc2 : Continuous (fun Tg : ℝ => K + D - a * M + a * Tg * (a * M - D)) := by fun_prop
  have h1 := hc1.tendsto' 0 0 (by simp)
  have h2 := hc2.tendsto' 0 (K + D - a * M) (by simp)
  have e1 : ∀ᶠ Tg in 𝓝 0, Tg * (2 * a * M - D) < M := h1.eventually_lt_const hM
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · have e2 : ∀ᶠ Tg in 𝓝 0, 0 < K + D - a * M + a * Tg * (a * M - D) :=
      h2.eventually_const_lt (by linarith)
    filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
      with Tg h1 h2 (h3 : 0 < Tg)
    rw [rateMargin_iff hM h3, reduced_rateMargin_iff hM]
    exact iff_of_true ⟨h1, h2⟩ hlt
  · have e2 : ∀ᶠ Tg in 𝓝 0, K + D - a * M + a * Tg * (a * M - D) < 0 :=
      h2.eventually_lt_const (by linarith)
    filter_upwards [nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with Tg h2 (h3 : 0 < Tg)
    rw [rateMargin_iff hM h3, reduced_rateMargin_iff hM]
    exact iff_of_false (fun h => by linarith [h.2]) (by linarith)

/-! ### The first-order family and the connection conclusions of the limit -/

/-- A first-order swing model: inertia `M > 0`, damping `D`, droop gain `K_R`. It is the
reduction `T_g → 0` of a swing + governor model (`Model.reduce`). -/
structure ReducedModel where
  /-- Inertia `M_eff = 2 H_eff` [s]. -/
  M : ℝ
  /-- Damping `D_eff`. -/
  D : ℝ
  /-- Aggregate droop gain `K_R`. -/
  K : ℝ
  M_pos : 0 < M

/-- The plant of a first-order model. -/
def ReducedModel.plant (r : ReducedModel) : Linear.Plant 1 1 := reducedPlant r.M r.D r.K

/-- The first-order reduction of a swing + governor model (forget `T_g`). -/
def Model.reduce (m : Model) : ReducedModel := ⟨m.M, m.D, m.K, m.M_pos⟩

/-- Requirements on the first-order models, all static. -/
inductive ReducedRequirement
  /-- `0 < K_R + D`. -/
  | stable
  /-- `K_R + D < 0`. -/
  | unstable
  /-- `a M ≤ K_R + D`: the rate `a` does not exceed the pole magnitude `(K_R + D)/M`. -/
  | rate (a : ℝ)

/-- Satisfaction of a requirement by a first-order model. -/
def ReducedMeets (r : ReducedModel) : ReducedRequirement → Prop
  | .stable => 0 < r.K + r.D
  | .unstable => r.K + r.D < 0
  | .rate a => a * r.M ≤ r.K + r.D

/-- Lyapunov stability, the attractive sentences and sampled contraction into `stable`,
instability into `unstable`, a decay rate into `rate`; conservation and passivity into the whole
(inconsistent) language. -/
def reducedTranslate : Sentence → Set ReducedRequirement
  | .flow .unstable => {.unstable}
  | .flow (.decay a) => {.rate a}
  | .flow .conservative => Set.univ
  | .flow _ => {.stable}
  | .passive => Set.univ
  | .envelope _ => ∅

/-- The first-order family: every model read as the port system of its plant (load deviation
in, frequency deviation out). -/
def reducedFamily : Family ReducedModel ReducedRequirement 1 1 :=
  ⟨fun r => r.plant.system, ReducedMeets, reducedTranslate⟩

@[powerlib_foundation] theorem reducedFamily_isLinear :
    reducedFamily.IsLinear ReducedModel.plant := fun _ => rfl

@[powerlib_foundation] theorem reduce_plant (m : Model) :
    m.reduce.plant = reducedPlant m.M m.D m.K := rfl

/-- No first-order model is both stable and unstable. -/
@[tmio M, powerlib_foundation] theorem reduced_realize_univ :
    connection% (realize ReducedMeets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.realize_univ_eq_empty_of .stable .unstable fun r (h1 : 0 < r.K + r.D)
    (h2 : r.K + r.D < 0) => absurd (lt_trans h1 h2) (lt_irrefl _)

private theorem reduced_mem_den_decay_iff (r : ReducedModel) (a : ℝ) :
    connection% (r ∈ reducedFamily.den (.flow (.decay a)) ↔ a * r.M ≤ r.K + r.D) := by
  change r ∈ reducedFamily.den (.flow (.decay a)) ↔ a * r.M ≤ r.K + r.D
  rw [(connection_proof% reducedFamily_isLinear.mem_den_flow)]
  have hA : r.plant.A = !![-((r.K + r.D) / r.M)] := by
    change !![-(r.K + r.D) / r.M] = _
    rw [neg_div]
  change Flow.Decay (affineLinearVectorField r.plant.A 0) 0 a ↔ _
  rw [hA, Linear.decay_scalar_iff, le_div_iff₀ r.M_pos]

/-- The first-order translation is the linear table of `theorem/Spectral/LinearNamed.lean`. -/
private theorem reducedTranslate_eq_linearTable (s : Sentence) :
    reducedTranslate s =
      Spectral.linearTable {.stable} {.unstable} univ univ (fun a => {.rate a}) s := by
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- Every translation of the first-order family is sound (the linear table,
`Spectral.chain_le_semantics_of_linearTable_univ`). -/
@[tmio TM, powerlib_domain] theorem reduced_chain_le_semantics :
    connection% (∀ P, reducedFamily.chain P ≤ reducedFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_linearTable_univ (F := reducedFamily)
    reducedFamily_isLinear reducedTranslate_eq_linearTable
    (fun r hm => (reduced_isHurwitz_iff r.M_pos).mpr ((mem_realize _ _ _).mp hm .stable rfl))
    (fun r hm => ?_) fun a r hm => (reduced_mem_den_decay_iff r a).2
      ((mem_realize _ _ _).mp hm (.rate a) rfl)
  have hu : r.K + r.D < 0 := (mem_realize _ _ _).mp hm .unstable rfl
  refine ⟨((-(r.K + r.D) / r.M : ℝ) : ℂ), ?_, ?_⟩
  · simp [ReducedModel.plant, reducedPlant, Linear.characteristicMatrix]
  · simp only [Complex.ofReal_re]
    exact div_pos (by linarith) r.M_pos

/-- On the attractive sentences and sampled contraction the first-order translation is exact
(`0 < K_R + D`). -/
@[tmio TM, powerlib_domain] theorem reduced_exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (reducedFamily.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.exact_of_linearTable (F := reducedFamily) reducedFamily_isLinear
    reducedTranslate_eq_linearTable
    (fun r => Spectral.mem_realize_singleton.trans (reduced_isHurwitz_iff r.M_pos).symm) hP

/-- The first-order decay translation is exact at every rate: the model decays at the rate `a`
exactly when `a M ≤ K_R + D` (its solutions are `e^{−(K_R + D) t/M}`). -/
@[tmio TM, powerlib_domain] theorem reduced_exact_decay (a : ℝ) :
    connection% (reducedFamily.Exact (.flow (.decay a))) := by
  unfold powerlib.TMIO.Statement
  unfold Family.Exact
  ext r
  change r ∈ realize ReducedMeets {.rate a} ↔ _
  rw [(connection_proof% reduced_mem_den_decay_iff)]
  simp [mem_realize, ReducedMeets]

/-- **Stability is preserved by the reduction `T_g → 0`**: whenever `0 < M + D T_g`, a swing +
governor model satisfies an attractive sentence (or sampled contraction) exactly when its
first-order reduction does. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_reduce (m : Model) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) (h : 0 < m.M + m.D * m.Tg) :
    connection% (m ∈ family.den (.flow P) ↔ m.reduce ∈ reducedFamily.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz hP, reducedFamily_isLinear.den_hurwitz hP]
  exact isHurwitz_iff_reduced m.M_pos m.Tg_pos h

/-- With nonnegative damping the reduction preserves the attractive sentences for every `T_g`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_reduce_of_nonneg (m : Model) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) (hD : 0 ≤ m.D) :
    connection% (m ∈ family.den (.flow P) ↔ m.reduce ∈ reducedFamily.den (.flow P)) :=
  mem_den_iff_reduce m hP (by nlinarith [m.M_pos, m.Tg_pos])

/-- Boundary of the reduction: with negative damping a large `T_g` breaks it. `M = 1`, `D = −1`,
`K_R = 2`, `T_g = 2` is unstable (`M + D T_g = −1 < 0`) while its first-order reduction
(`K_R + D = 1 > 0`) is globally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem exists_unstable_reduce_globallyExponentiallyStable :
    connection% (∃ m : Model, m ∈ family.den (.flow .unstable) ∧
      m.reduce ∈ reducedFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine ⟨⟨1, -1, 2, 2, one_pos, two_pos⟩, ?_, ?_⟩
  · exact mem_den_unstable ⟨1, -1, 2, 2, one_pos, two_pos⟩ (Or.inr (by norm_num))
  · rw [reducedFamily_isLinear.den_hurwitz (Or.inl (by simp))]
    exact (reduced_isHurwitz_iff one_pos).2 (by change (0 : ℝ) < 2 + -1; norm_num)

/-- The slow root bounds every decay rate: if `−a < λ_s` (real roots, `M + D T_g + √disc ≠ 0`),
the model does not decay at the rate `a` (its slow eigenmode decays like `e^{λ_s t}`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_decay_of_slowEig (m : Model) {a : ℝ}
    (hΔ : 0 ≤ eigDisc m.M m.D m.K m.Tg)
    (hS : m.M + m.D * m.Tg + Real.sqrt (eigDisc m.M m.D m.K m.Tg) ≠ 0)
    (h : -a < slowEig m.M m.D m.K m.Tg) :
    connection% (m ∉ family.den (.flow (.decay a))) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isLinear.mem_den_flow)]
  refine LTI.not_decay_of_eigenvector (A := m.plant.A)
    (v := WithLp.toLp 2 ![1, m.M * slowEig m.M m.D m.K m.Tg + m.D]) ?_ ?_ h
  · intro h0
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h0
    simp at this
  · rw [Matrix.toEuclideanCLM_toLp]
    change WithLp.toLp 2 ((plant m.M m.D m.K m.Tg).A *ᵥ _) = _
    rw [plant_mulVec_slowEigvec m.M_pos.ne' m.Tg_pos.ne' hΔ hS]
    rfl

/-- **Decay rates in the limit `T_g → 0`.** For fixed `M > 0`, `D`, `K_R` and a rate off the
first-order pole (`a M ≠ K_R + D`) there is a threshold `τ > 0` such that every swing + governor
model with these parameters and `T_g < τ` decays at the rate `a` exactly when its first-order
reduction does (i.e. exactly when `a M ≤ K_R + D`). -/
@[tmio TM, powerlib_domain] theorem exists_threshold_mem_den_decay_iff_reduce (M D K a : ℝ) (hM : 0 < M)
    (ha : a * M ≠ K + D) :
    connection% (∃ τ : ℝ, 0 < τ ∧ ∀ m : Model, m.M = M → m.D = D → m.K = K →
      m.Tg < τ → (m ∈ family.den (.flow (.decay a)) ↔
        m.reduce ∈ reducedFamily.den (.flow (.decay a)))) := by
  unfold powerlib.TMIO.Statement
  -- the eventual facts as `T_g → 0⁺`
  have hev : ∀ᶠ Tg in 𝓝[>] 0, (Linear.RateMargin (plant M D K Tg).A a ↔
        Linear.RateMargin (reducedPlant M D K).A a) ∧ 0 < eigDisc M D K Tg ∧
      0 < M + D * Tg + Real.sqrt (eigDisc M D K Tg) ∧
      (K + D < a * M → -a < slowEig M D K Tg) := by
    have hslow : ∀ᶠ Tg in 𝓝 0, K + D < a * M → -a < slowEig M D K Tg := by
      rcases lt_or_ge (K + D) (a * M) with hgt | hle
      · have hlim : -a < -(K + D) / M := by
          rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hM]
          linarith
        filter_upwards [(tendsto_slowEig (D := D) (K := K) hM).eventually_const_lt hlim]
          with Tg h _ using h
      · exact Eventually.of_forall fun _ h => absurd h (not_lt.2 hle)
    filter_upwards [eventually_rateMargin_iff_reduced (D := D) (K := K) hM ha,
      nhdsWithin_le_nhds (eventually_eigDisc_pos (D := D) (K := K) hM.ne'),
      nhdsWithin_le_nhds (eventually_rootSum_pos (D := D) (K := K) hM),
      nhdsWithin_le_nhds hslow] with Tg h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨τ, hτ, hτP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨τ, hτ, fun m hMm hDm hKm hTm => ?_⟩
  obtain ⟨hrate, hΔ, hS, hslow⟩ := hτP ⟨m.Tg_pos, hTm⟩
  subst hMm hDm hKm
  rw [(connection_proof% reduced_mem_den_decay_iff)]
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · refine iff_of_true ?_ hlt.le
    refine family_isLinear.mem_den_decay_of_rateMargin ?_
    exact hrate.2 ((reduced_rateMargin_iff m.M_pos a).2 hlt)
  · refine iff_of_false ?_ (not_le.2 hgt)
    exact not_mem_den_decay_of_slowEig m hΔ.le hS.ne' (hslow hgt)

/-! ### Implementation evidence (private, trajectory level): solutions converge -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
**Solutions converge to the first-order model as `T_g → 0`** (Tikhonov's theorem, finite
horizon, from the generic `SingularPerturbation.LinearSP.exists_finiteHorizon_error` applied to
`twoTimeScale`). For every horizon `T` there are `ε₀ > 0` and `C` such that for every
`T_g ∈ (0, ε₀]`, every solution `x = (Δω, ΔP_m)` of the swing + governor model under the load
`ΔP_L` and the solution `x̄` of the first-order model under the same load from the same frequency
deviation, on `[0, T]`:
`|Δω(t) − Δω̄(t)|² ≤ C T_g² |x(0) − x^∞|²` and
`|ΔP_m(t) − (−K_R Δω̄(t) + e^{−t/T_g} (ΔP_m(0) + K_R Δω(0)))|² ≤ C T_g² |x(0) − x^∞|²`
(`x^∞` the quasi-steady state; the second bound includes the governor's initial layer). -/
private theorem finiteHorizon_reduce (hKD : K + D ≠ 0) (T : ℝ) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ Tg, 0 < Tg → Tg ≤ ε₀ →
      ∀ (x : ℝ → ℝ²) (xbar : ℝ → EuclideanSpace ℝ (Fin 1)),
      (∀ t, HasDerivAt x ((plant M D K Tg).inputField (load ΔPL) (x t)) t) →
      (∀ t, HasDerivAt xbar ((reducedPlant M D K).inputField (load ΔPL) (xbar t)) t) →
      xbar 0 0 = x 0 0 →
      ∀ t ∈ Icc 0 T,
        (x t 0 - xbar t 0) ^ 2 ≤ C * Tg ^ 2 *
          ((x 0 0 - steadyState D K ΔPL 0) ^ 2 + (x 0 1 - steadyState D K ΔPL 1) ^ 2) ∧
        (x t 1 - (-K * xbar t 0 + Real.exp (-(t / Tg)) * (x 0 1 + K * x 0 0))) ^ 2 ≤
          C * Tg ^ 2 *
            ((x 0 0 - steadyState D K ΔPL 0) ^ 2 + (x 0 1 - steadyState D K ΔPL 1) ^ 2) := by
  obtain ⟨ε₀, hε₀, C, H⟩ :=
    (twoTimeScale M D K).exists_finiteHorizon_error twoTimeScale_A22_isHurwitz T
  refine ⟨ε₀, hε₀, C, fun Tg hTg hTgε x xbar hx hxbar h0 t ht => ?_⟩
  set w := steadyState D K ΔPL 0 with hw
  set q := steadyState D K ΔPL 1 with hq
  have hwq : q + K * w = 0 := by
    rw [hw, hq, steadyState_zero, steadyState_one]
    ring
  have hrow0 : -D / M * w + 1 / M * q + -1 / M * ΔPL = 0 := by
    rw [hw, hq, steadyState_zero, steadyState_one]
    field_simp
    ring
  have hred : -(K + D) / M * w + -1 / M * ΔPL = 0 := by
    rw [hw, steadyState_zero]
    field_simp
    ring
  set sp := twoTimeScale M D K
  let X : ℝ → Fin 1 → ℝ := fun s _ => x s 0 - w
  let Z : ℝ → Fin 1 → ℝ := fun s _ => x s 1 - q
  let Xb : ℝ → Fin 1 → ℝ := fun s _ => xbar s 0 - w
  let Zb : ℝ → Fin 1 → ℝ := fun τ _ => Real.exp (-τ) * (x 0 1 + K * x 0 0)
  have hX : ∀ s, HasDerivAt X (sp.A11 *ᵥ X s + sp.A12 *ᵥ Z s) s := by
    intro s
    refine hasDerivAt_pi.2 fun i => ?_
    have h := (Dynamics.hasDerivAt_iff_coords.mp (hx s) 0).sub_const w
    rw [field_apply] at h
    convert h using 1
    simp [sp, twoTimeScale, X, Z, dotProduct]
    linear_combination -hrow0
  have hZ : ∀ s, HasDerivAt Z (Tg⁻¹ • (sp.A21 *ᵥ X s + sp.A22 *ᵥ Z s)) s := by
    intro s
    refine hasDerivAt_pi.2 fun i => ?_
    have h := (Dynamics.hasDerivAt_iff_coords.mp (hx s) 1).sub_const q
    rw [field_apply] at h
    convert h using 1
    simp [sp, twoTimeScale, X, Z, dotProduct]
    field_simp
    linear_combination hwq
  have hXb : ∀ s, HasDerivAt Xb (sp.reducedMatrix *ᵥ Xb s) s := by
    intro s
    refine hasDerivAt_pi.2 fun i => ?_
    have h := (Dynamics.hasDerivAt_iff_coords.mp (hxbar s) 0).sub_const w
    rw [reduced_field_apply] at h
    convert h using 1
    rw [twoTimeScale_reducedMatrix]
    simp [Xb, reducedPlant, Matrix.mulVec, dotProduct]
    linear_combination -hred
  have hXb0 : Xb 0 = X 0 := by
    funext i
    simp [Xb, X, h0]
  have hZb : ∀ τ, HasDerivAt Zb (sp.A22 *ᵥ Zb τ) τ := by
    intro τ
    refine hasDerivAt_pi.2 fun i => ?_
    have h := ((hasDerivAt_id τ).neg.exp).mul_const (x 0 1 + K * x 0 0)
    convert h using 1 <;> simp [sp, twoTimeScale, Zb, Matrix.mulVec, dotProduct]
  have hZb0 : Zb 0 = Z 0 + sp.gain *ᵥ X 0 := by
    funext i
    rw [twoTimeScale_gain]
    simp [Zb, Z, X, dotProduct]
    linear_combination hwq
  obtain ⟨h1, h2⟩ := H Tg hTg hTgε X Z Xb Zb hX hZ hXb hXb0 hZb hZb0 t ht
  rw [twoTimeScale_gain] at h2
  simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Pi.sub_apply, Pi.add_apply, Pi.neg_apply, X, Z, Xb, Zb] at h1 h2
  simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one] at h2
  constructor
  · convert h1 using 1 <;> ring
  · convert h2 using 1
    · linear_combination ((x t 1 - (-K * xbar t 0 + Real.exp (-(t / Tg)) * (x 0 1 + K * x 0 0)))
        + (x t 1 - q - (-(K * (xbar t 0 - w)) + Real.exp (-(t / Tg)) * (x 0 1 + K * x 0 0)))) * hwq
    · ring

end powerlib.Frequency.SwingGovernor
