import theorem.Frequency.Basic
import theorem.Criteria.Hurwitz2
import theorem.Linear.Rate
import theorem.TMIO.ClaimElab

/-! # Single-area swing + first-order governor (two-state frequency model)

Source: work-sync `theory/T-frequency-stability.md` §1.4–§1.8 (model §1.7/§1.8, RoCoF §1.5,
quasi-steady-state deviation §1.6, characteristic polynomial / `ω_n` / `ζ_n` §1.7, damping trend
§2.5).

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

Static results (foundation).
* `field_swing`, `field_governor`: the state equations are exactly the §1.7 pair.
* `transfer_apply`: `Linear.transfer` from `ΔP_L` to `Δω` is
  `−(1 + T_g s)/(M T_g s² + (M + D T_g) s + (D + K_R))` (§1.7).
* `det_characteristicMatrix_eq`: `det(sI − A) = s² + 2 ζ_n ω_n s + ω_n²` with the §1.7 boxed
  `ω_n`, `ζ_n`; `dampingRatio_strictAntiOn`: `ζ_n` strictly decreases in `K_R` (§2.5).
* `isEquilibrium_iff`: the unique equilibrium for the step `ΔP_L` is
  `(−ΔP_L/(K_R + D), K_R ΔP_L/(K_R + D))` (§1.6).
* `isHurwitz_iff`: for `0 < M`, `0 < T_g` the state matrix is Hurwitz iff `0 < M + D T_g` and
  `0 < K_R + D`; with `0 ≤ D` this is `0 < K_R + D` (`isHurwitz_iff_of_nonneg`).

Family and connection conclusions.
* System map: a model (`Model`: `M, D, K_R, T_g` with `0 < M`, `0 < T_g`) is read as the port
  system of its plant (`Family.IsLinear`): port input the load deviation `ΔP_L`, port output
  `Δω`. The flow sentences therefore speak about the zero-load operating point; since the plant is
  linear, the same attractive sentences hold at the quasi-steady state of every constant load
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
* Implementation evidence (private, trajectory level, outside the sentence language): the
  initial RoCoF `Δω̇(0⁺) = −ΔP_L / M_eff` (`rocof`, `rocof_hz`, §1.5), the global exponential
  stability of the quasi-steady state of the load step (`exponentiallyConvergesTo_steadyState`)
  and the convergence `Δω(t) → −ΔP_L/(K_R + D)` of every forward solution under the load step
  (`tendsto_freq`, §1.6). The former `@[powerlib_domain]` labels of `isEquilibrium_iff` and
  `steadyState_isEquilibrium` are now `@[powerlib_foundation]` (static evidence).
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

@[simp, powerlib_foundation] theorem steadyState_zero (D K ΔPL : ℝ) :
    steadyState D K ΔPL 0 = -ΔPL / (K + D) := rfl

@[simp, powerlib_foundation] theorem steadyState_one (D K ΔPL : ℝ) :
    steadyState D K ΔPL 1 = K * ΔPL / (K + D) := rfl

@[powerlib_foundation] theorem field_apply (x : ℝ²) :
    (plant M D K Tg).inputField (load ΔPL) x =
      WithLp.toLp 2 ![-D / M * x 0 + 1 / M * x 1 + -1 / M * ΔPL,
        -K / Tg * x 0 + -1 / Tg * x 1] := by
  rw [inputField_apply]
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

/-- The swing + governor family: every model read as the port system of its plant (load
deviation in, frequency deviation out). -/
def family : Family Model Requirement 2 1 := ⟨fun m => m.plant.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear Model.plant := fun _ => rfl

/-- No model is both stable and unstable: the whole requirement language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨h1, h2⟩ : Meets m .stable := h .stable
  rcases (h .unstable : Meets m .unstable) with h3 | h3 <;> linarith

/-- The attractive sentences and sampled contraction denote the members satisfying `stable`. -/
private theorem den_hurwitz {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    family.den (.flow P) = {m | Meets m .stable} := by
  rw [family_isLinear.den_hurwitz hP]
  ext m
  exact isHurwitz_iff m.M_pos m.Tg_pos

private theorem stable_mem_den {m : Model} (h : Meets m .stable) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) : m ∈ family.den (.flow P) := by
  rw [den_hurwitz hP]
  exact h

/-- Every translation of the swing + governor family is sound: its translation chain lies below
its semantics connection. `stable` is the Hurwitz condition of the plant (the linear hub), a
right-half-plane root gives instability, a spectral margin gives the decay rate. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ realize Meets Set.univ := (mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · cases P
    case lyapunovStable =>
      have h := stable_mem_den (P := .globallyExponentiallyStable) (hm .stable rfl) (by simp)
      rw [family_isLinear.mem_den_flow] at h ⊢
      exact h.lyapunovStable
    case unstable =>
      obtain ⟨s, hs, hre⟩ := exists_root_of_unstable m.M_pos m.Tg_pos (hm .unstable rfl)
      exact family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 hs hre)
    case decay a =>
      exact family_isLinear.mem_den_decay_of_rateMargin (hm (.rate a) rfl)
    case conservative => exact (hnone fun q => hm q trivial).elim
    case contractive => exact stable_mem_den (hm .stable rfl) (Or.inr rfl)
    all_goals exact stable_mem_den (hm .stable rfl) (Or.inl (by simp))
  · exact (hnone fun q => hm q trivial).elim

/-- On the attractive sentences and sampled contraction the chain agrees with the semantics:
`stable` (`0 < M + D T_g`, `0 < K_R + D`) is their exact translation. -/
@[powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  unfold Family.Exact
  rw [den_hurwitz hP]
  have hs : translate (.flow P) = {.stable} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact absurd hP (by simp [Flow.Property.Attractive])
    · rfl
  change realize Meets (translate (.flow P)) = _
  rw [hs]
  ext m
  simp [mem_realize]

/-- The member characterization: a model satisfies an attractive sentence exactly when
`0 < M + D T_g` and `0 < K_R + D`. -/
@[powerlib_domain] theorem mem_den_attractive_iff (m : Model) {P : Flow.Property}
    (hP : P.Attractive) :
    connection% (m ∈ family.den (.flow P) ↔ m ∈ {m : Model | 0 < m.M + m.D * m.Tg ∧ 0 < m.K + m.D}) := by
  unfold powerlib.TMIO.Statement
  rw [den_hurwitz (Or.inl hP)]
  rfl

/-- §1.6: with nonnegative damping, `0 < K_R + D` makes the zero-load operating point globally
exponentially stable; by linearity so is the quasi-steady state of every constant load step. -/
@[powerlib_domain] theorem mem_den_globallyExponentiallyStable (m : Model) (hD : 0 ≤ m.D)
    (hKD : 0 < m.K + m.D) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine stable_mem_den ⟨?_, hKD⟩ (Or.inl (by simp))
  nlinarith [m.M_pos, m.Tg_pos]

/-- A negative determinant (`K_R + D < 0`) or a positive trace (`M + D T_g < 0`) places a model
in instability. -/
@[powerlib_domain] theorem mem_den_unstable (m : Model) (h : m.K + m.D < 0 ∨ m.M + m.D * m.Tg < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨s, hs, hre⟩ := exists_root_of_unstable m.M_pos m.Tg_pos h
  exact family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 hs hre)

/-- With `0 < K_R + D` the model is not passive on its `(ΔP_L, Δω)` port: under the constant
load `ΔP_L = 1` the quasi-steady state is an equilibrium at which the port supplies
`ΔP_L Δω^∞ = −1/(K_R + D) < 0`. -/
@[powerlib_domain] theorem not_mem_den_passive (m : Model) (hKD : 0 < m.K + m.D) :
    connection% (m ∉ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den, Sentence.holds_passive]
  refine Port.System.not_passive_of_equilibrium _ (x₀ := steadyState m.D m.K 1) (u₀ := load 1)
    (steadyState_isEquilibrium m.M_pos.ne' m.Tg_pos.ne' hKD.ne') ?_
  have hsupply : (family.system m).supply (steadyState m.D m.K 1) (load 1) = -1 / (m.K + m.D) := by
    simp [Port.System.supply, family, Model.plant, plant, Linear.Plant.system, load, steadyState,
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
  have h := hasDerivWithinAt_apply_zero hx 0
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
  have h := tendsto_apply_of_isHurwitz m.plant
    (steadyState_isEquilibrium m.M_pos.ne' m.Tg_pos.ne' hKD.ne') hA hx 0
  simpa using h

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.6 at the trajectory level (formerly `exponentiallyConvergesTo_steadyState`): every solution
under the load step converges exponentially to the quasi-steady state, read from the connection
theorem `mem_den_globallyExponentiallyStable` and linearity (`Linear.holds_input_iff`). -/
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

end powerlib.Frequency.SwingGovernor
