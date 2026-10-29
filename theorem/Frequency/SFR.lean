import theorem.Spectral.Local
import theorem.Frequency.SwingNadir
import theorem.Criteria.Routh3
import theorem.Linear.Rate
import theorem.TMIO.ClaimElab
import theorem.SpecialFunctions.Elementary
import theorem.Spectral.LinearNamed

/-! # Reheat-turbine system frequency response (SFR) model

The third-order reheat-turbine SFR model and its second-order reduction as linear families: the
corrected state matrix, a Routh–Hurwitz stability condition, and the exact nadir of the reduced
model.

Model boundary.
Common to both models:
* Continuous-time, linear, small-signal single-area model (the note's "one equivalent machine"
  premise), Kundur per-unit: `Δω` per-unit, `M = M_eff = 2 H_eq` [s], powers in system-base
  per-unit, generation-side balance `M Δω̇ = ΔP_m − ΔP_L − D Δω` (load increase positive).
* Input (one port): load step `ΔP_L` (`Frequency.load`); output `Δω`. No AGC
  (`ΔP_C = 0`), dead-band, rate limit, valve saturation, PLL, delay, PWM, voltage dynamics.
* Reheat steam turbine with `T_CH` neglected: `G_turb(s) = (1 + s F T_R)/(1 + s T_R)`
  (`F = F_HP`, `T_R = T_RH`); governor `T_g ΔṖ_v = −ΔP_v − K_R Δω`.
* Third-order model (`plant`, state `x = (Δω, ΔP_m, ΔP_v)` in `EuclideanSpace ℝ (Fin 3)`),
  state matrix (corrected §1.8)
  `A = [[−D/M, 1/M, 0], [−F K_R/T_g, −1/T_R, 1/T_R − F/T_g], [−K_R/T_g, 0, −1/T_g]]`.
* Second-order reduction (`reducedPlant`, `T_g → 0`, state `x = (Δω, ΔP_RH)`): the governor is
  static (`ΔP_v = −K_R Δω`) and `G_turb` is realised with the reheat (low pressure) state
  `ΔP_RH = ΔP_m + F K_R Δω`, `T_R ΔṖ_RH = −ΔP_RH − (1 − F) K_R Δω`. The reduction `T_g → 0`
  itself (a singular-perturbation limit) is not formalized: the reduced model is a separate
  model, checked against the note's §1.5 equations and transfer function. It is
  `SwingGovernor.plant M (D + F K_R) ((1 − F) K_R) T_R`, so the exact nadir closed form of
  `Frequency.SwingNadir` applies, and with `0 < M`, `0 < T_R` it is a member of
  `SwingGovernor.family` (`reducedModel`).

Source: work-sync `theory/T-sfr-model.md` §1.2–§1.8 (turbine `G_turb`, governor, third-order
SFR transfer function §1.4, second-order reduction §1.5, nadir §1.6, RoCoF / steady state §1.7,
state-space form §1.8).

Results.
Third-order model:
* `field_swing`, `field_governor`, `field_turbine`: the three rows are the swing equation, the
  governor, and the time-domain form `T_R ΔṖ_m + ΔP_m = ΔP_v + F T_R ΔṖ_v` of `G_turb`.
* `transfer_apply` (foundation): `Linear.transfer` equals the §1.4 third-order transfer
  function.
* `routhQuantity_eq`, `isHurwitz_iff`, `isHurwitz_of_hp_fraction`: with
  `a₃ = M T_g T_R`, `a₂ = M (T_g + T_R) + D T_g T_R`, `a₁ = M + D (T_g + T_R) + K_R F T_R`,
  `a₀ = D + K_R`, the Routh quantity is
  `a₂ a₁ − a₃ a₀ = M²(T_g+T_R) + M D (T_g+T_R)² + M K_R T_R [F (T_g+T_R) − T_g]
     + D² T_g T_R (T_g+T_R) + D K_R F T_g T_R²`,
  so `F ≥ T_g/(T_g + T_R)` (with `D, K_R ≥ 0`, `K_R + D > 0`) makes the model Hurwitz. The
  note states no stability condition; this one is added.
* `isEquilibrium_iff` (foundation, static): unique equilibrium
  `(−ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D))` for the load step.
* `rocof`, `tendsto_freq` (private implementation evidence): initial RoCoF `−ΔP_L/M`;
  `Δω → −ΔP_L/(K_R + D)` along every forward solution (§1.7).
Second-order reduction:
* `reduced_field_swing`, `reduced_field_turbine`, `reduced_transfer_apply`,
  `reduced_natFreq_sq`, `reduced_two_mul_dampingRatio_mul_natFreq`: the §1.5 equations,
  transfer function, `ω_n² = (K_R + D)/(M T_R)` and `2 ζ ω_n = (M + (D + K_R F) T_R)/(M T_R)`.
* `reduced_nadir` (private implementation evidence): for `ζ < 1` and a load increase, `Δω` has
  its global minimum over `t ≥ 0` at `t_n = atan2(ω_d T_R, ζ ω_n T_R − 1)/ω_d`
  (`atan2(y, x) = arg (x + j y)`), is strictly decreasing before it, and the exact minimum is
  `−ΔP_L/(K_R + D) · [1 + √(1 − 2 ζ ω_n T_R + ω_n² T_R²) e^{−ζ ω_n t_n}]`.

Family and connection conclusions.
* Constant-input families below preserve the symbolic input and the selected steady state;
  their autonomous system is the translated forced field.
* System map: a third-order model (`Model`: `M, D, K_R, F, T_g, T_R` with `M, T_g, T_R > 0`) is
  read as the port system of its plant (`Family.IsLinear`): port input the load deviation,
  port output `Δω`. Flow sentences concern the zero-load operating point; by linearity the
  attractive sentences hold at the steady state of every constant load step exactly when they
  hold there (`Linear.holds_input_iff`).
* Requirements (static): `stable` (`a₂ > 0`, `a₀ = K_R + D > 0`, `a₂ a₁ − a₃ a₀ > 0`, the
  Routh–Hurwitz conditions), `unstable` (`a₀ < 0` or `a₂ < 0`: determinant `> 0` or trace `> 0`
  of the state matrix), `rate a`. Translation as in `SwingGovernor`: Lyapunov stability and the
  attractive sentences into `stable`, instability into `unstable`, decay into its margin,
  conservation and passivity into the whole (inconsistent) language.
* Connection theorems: `chain_le_semantics`, `exact_hurwitz` (Routh–Hurwitz is the exact
  translation of the attractive sentences and sampled contraction), `mem_den_attractive_iff`,
  `mem_den_globallyExponentiallyStable` (the added condition `F ≥ T_g/(T_g + T_R)`),
  `mem_den_unstable`, `not_mem_den_passive` and, for the reduced model as a member of
  `SwingGovernor.family`, `reduced_mem_den_globallyExponentiallyStable`.
* Static evidence: `isEquilibrium_iff`, `steadyState_isEquilibrium`. Private implementation
  evidence (trajectory level, Rules §3a): `rocof`, `exponentiallyConvergesTo_steadyState`,
  `tendsto_freq`, `reduced_nadir`, `reduced_rocof`, `reduced_tendsto_freq`.

Corrections.
* §1.8 state matrix: the note's second row `[−F K_R/(T_R T_g), −1/T_R, (1 − F)/T_R]` does not
  realise `G_turb`: its static gain is `−1/(D + K_R (1 − F + F/T_g))`
  (`notePlant_transfer_zero`) instead of the §1.4/§1.7 value `−1/(K_R + D)` (`transfer_zero`),
  so its transfer function differs from §1.4 whenever `K_R F (1 − T_g) ≠ 0`
  (`notePlant_transfer_ne`; `F/T_g` is also dimensionally inconsistent). The corrected second
  row is `[−F K_R/T_g, −1/T_R, 1/T_R − F/T_g]` (`field_turbine`, `transfer_apply`).
* §1.6 nadir time: the note's `t_n = arctan(ω_d T_R/(1 − ζ ω_n T_R))/ω_d` has the wrong sign
  in the denominator; whenever `ζ ω_n T_R > 1` it equals `−t_n < 0`
  (`noteNadirTime_eq_neg`). (Typical parameters `2H = 8 s`, `T_R = 7 s`, `F = 0.3`,
  `K_R = 20`, `D = 1` give `ζ ω_n T_R ≈ 3.6`; RK4 gives `t_n ≈ +2.20 s`, the note `−2.20 s`.)
* §1.6 states that the closed form needs the approximation `ζ ω_n ≪ 1/T_RH`; it does not:
  `reduced_nadir` is exact for the reduced model. The note's amplitude
  `α e^{−ζω_n t_n} sin(ω_d t_n + φ)` with `φ = ω_d t_n` is replaced by the exact
  `√(1 − 2 ζ ω_n T_R + ω_n² T_R²) e^{−ζ ω_n t_n}`.
-/

noncomputable section
namespace powerlib.Frequency.SFR
open Set Filter Matrix LinearSystems TMIO
open scoped Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Corrected third-order reheat SFR plant, state `(Δω, ΔP_m, ΔP_v)`. -/
def plant (M D K F Tg TR : ℝ) : Linear.Plant 3 1 where
  A := !![-D / M, 1 / M, 0; -(F * K) / Tg, -1 / TR, 1 / TR - F / Tg; -K / Tg, 0, -1 / Tg]
  B := !![-1 / M; 0; 0]
  C := !![1, 0, 0]
  D := 0

/-- The state matrix printed in the note's §1.8 (second row as in the note). -/
def notePlant (M D K F Tg TR : ℝ) : Linear.Plant 3 1 where
  A := !![-D / M, 1 / M, 0; F / TR * (1 / Tg) * (-K), -1 / TR, (1 - F) / TR; -K / Tg, 0, -1 / Tg]
  B := !![-1 / M; 0; 0]
  C := !![1, 0, 0]
  D := 0

/-- Steady state `(−ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D))`. -/
def steadyState (D K ΔPL : ℝ) : ℝ³ :=
  WithLp.toLp 2 ![-ΔPL / (K + D), K * ΔPL / (K + D), K * ΔPL / (K + D)]

/-- Third-order denominator coefficients (`a₃ s³ + a₂ s² + a₁ s + a₀`). -/
def coeff3 (M Tg TR : ℝ) : ℝ := M * Tg * TR
def coeff2 (M D Tg TR : ℝ) : ℝ := M * (Tg + TR) + D * Tg * TR
def coeff1 (M D K F Tg TR : ℝ) : ℝ := M + D * (Tg + TR) + K * F * TR
def coeff0 (D K : ℝ) : ℝ := D + K

/-- Routh quantity `a₂ a₁ − a₃ a₀`. -/
def routhQuantity (M D K F Tg TR : ℝ) : ℝ :=
  coeff2 M D Tg TR * coeff1 M D K F Tg TR - coeff3 M Tg TR * coeff0 D K

variable {M D K F Tg TR ΔPL : ℝ}

@[tmio M, simp, powerlib_foundation] theorem steadyState_zero (D K ΔPL : ℝ) :
    steadyState D K ΔPL 0 = -ΔPL / (K + D) := rfl

@[powerlib_foundation] theorem field_apply (x : ℝ³) :
    (plant M D K F Tg TR).inputField (load ΔPL) x =
      WithLp.toLp 2 ![-D / M * x 0 + 1 / M * x 1 + -1 / M * ΔPL,
        -(F * K) / Tg * x 0 + -1 / TR * x 1 + (1 / TR - F / Tg) * x 2,
        -K / Tg * x 0 + -1 / Tg * x 2] := by
  rw [LTI.inputField_apply]
  congr 1
  ext i
  fin_cases i <;> simp [plant, load, dotProduct, Fin.sum_univ_three]

/-- Swing row: `M Δω̇ = ΔP_m − ΔP_L − D Δω`. -/
@[powerlib_foundation] theorem field_swing (hM : M ≠ 0) (x : ℝ³) :
    M * (plant M D K F Tg TR).inputField (load ΔPL) x 0 = x 1 - ΔPL - D * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  field_simp
  ring

/-- Governor row: `T_g ΔṖ_v = −ΔP_v − K_R Δω`. -/
@[powerlib_foundation] theorem field_governor (hTg : Tg ≠ 0) (x : ℝ³) :
    Tg * (plant M D K F Tg TR).inputField (load ΔPL) x 2 = -x 2 - K * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  field_simp
  ring

/-- Turbine row: `T_R ΔṖ_m + ΔP_m = ΔP_v + F T_R ΔṖ_v`, the time-domain form of
`ΔP_m = (1 + s F T_R)/(1 + s T_R) ΔP_v`. -/
@[powerlib_foundation] theorem field_turbine (hTg : Tg ≠ 0) (hTR : TR ≠ 0) (x : ℝ³) :
    TR * (plant M D K F Tg TR).inputField (load ΔPL) x 1 + x 1 =
      x 2 + F * TR * (plant M D K F Tg TR).inputField (load ΔPL) x 2 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-! ## Transfer function (§1.4) -/

@[powerlib_foundation] theorem det_characteristicMatrix (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hTR : TR ≠ 0) (s : ℂ) :
    (M : ℂ) * Tg * TR * (Linear.characteristicMatrix (plant M D K F Tg TR).A s).det =
      M * s * (1 + Tg * s) * (1 + TR * s) + D * (1 + Tg * s) * (1 + TR * s) +
        K * (1 + F * TR * s) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  have hR' : (TR : ℂ) ≠ 0 := by exact_mod_cast hTR
  simp [plant, Linear.characteristicMatrix, Matrix.det_fin_three]
  field_simp
  ring

/-- §1.4: `Δω(s)/ΔP_L(s) = −(1 + s T_g)(1 + s T_R) /
(M s (1 + s T_g)(1 + s T_R) + D (1 + s T_g)(1 + s T_R) + K_R (1 + s F T_R))`
(both sides are `0` at the poles). -/
@[powerlib_foundation] theorem transfer_apply (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0)
    (s : ℂ) :
    Linear.transfer (plant M D K F Tg TR) s 0 0 =
      -((1 + Tg * s) * (1 + TR * s)) /
        (M * s * (1 + Tg * s) * (1 + TR * s) + D * (1 + Tg * s) * (1 + TR * s) +
          K * (1 + F * TR * s)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  have hR' : (TR : ℂ) ≠ 0 := by exact_mod_cast hTR
  have hadj : (Linear.complexify (plant M D K F Tg TR).C *
      (Linear.characteristicMatrix (plant M D K F Tg TR).A s).adjugate *
        Linear.complexify (plant M D K F Tg TR).B) 0 0 =
      -((s + 1 / TR) * (s + 1 / Tg)) / M := by
    simp [plant, Linear.characteristicMatrix, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_three]
    field_simp
    ring
  have hD : Linear.complexify (plant M D K F Tg TR).D 0 0 = 0 := by simp [plant]
  rw [← det_characteristicMatrix hM hTg hTR, Linear.transfer_eq_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, hadj, hD, smul_eq_mul, add_zero]
  generalize (Linear.characteristicMatrix (plant M D K F Tg TR).A s).det = d
  by_cases h : d = 0
  · simp [h]
  · field_simp
    ring

/-! ## Stability (Routh–Hurwitz) -/

@[powerlib_foundation] theorem routhQuantity_eq :
    routhQuantity M D K F Tg TR =
      M ^ 2 * (Tg + TR) + M * D * (Tg + TR) ^ 2 + M * K * TR * (F * (Tg + TR) - Tg) +
        D ^ 2 * Tg * TR * (Tg + TR) + D * K * F * Tg * TR ^ 2 := by
  unfold routhQuantity coeff3 coeff2 coeff1 coeff0
  ring

@[powerlib_foundation] theorem trace_A (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    (plant M D K F Tg TR).A.trace = -coeff2 M D Tg TR / coeff3 M Tg TR := by
  simp only [plant, Matrix.trace_fin_three_of, coeff2, coeff3]
  field_simp
  ring

@[powerlib_foundation] theorem det_A (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    (plant M D K F Tg TR).A.det = -coeff0 D K / coeff3 M Tg TR := by
  simp only [plant, Matrix.det_fin_three, coeff0, coeff3, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  field_simp
  ring

@[powerlib_foundation] theorem principalMinorSum_A (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    Criteria.principalMinorSum (plant M D K F Tg TR).A =
      coeff1 M D K F Tg TR / coeff3 M Tg TR := by
  simp only [plant, Criteria.principalMinorSum, coeff1, coeff3, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.head_fin_const]
  field_simp
  ring

/-- A third-order reheat SFR model: inertia `M > 0`, damping `D`, droop gain `K_R`, HP fraction
`F`, governor and reheat time constants `T_g, T_R > 0`. -/
structure Model where
  M : ℝ
  D : ℝ
  K : ℝ
  F : ℝ
  Tg : ℝ
  TR : ℝ
  M_pos : 0 < M
  Tg_pos : 0 < Tg
  TR_pos : 0 < TR

/-- The plant of a model. -/
def Model.plant (m : Model) : Linear.Plant 3 1 := SFR.plant m.M m.D m.K m.F m.Tg m.TR

/-- Requirements on the SFR models, all static. -/
inductive Requirement
  /-- The Routh–Hurwitz conditions `a₂ > 0`, `a₀ > 0`, `a₂ a₁ − a₃ a₀ > 0`. -/
  | stable
  /-- `a₀ < 0` (determinant `> 0`) or `a₂ < 0` (trace `> 0`). -/
  | unstable
  /-- A strict spectral margin at the rate `a`. -/
  | rate (a : ℝ)

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .stable => 0 < coeff2 m.M m.D m.Tg m.TR ∧ 0 < coeff0 m.D m.K ∧
      0 < routhQuantity m.M m.D m.K m.F m.Tg m.TR
  | .unstable => coeff0 m.D m.K < 0 ∨ coeff2 m.M m.D m.Tg m.TR < 0
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

/-- The SFR family: every model read as the port system of its plant (load deviation in,
frequency deviation out). -/
def family : Family Model Requirement 3 1 := ⟨fun m => m.plant.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear Model.plant := fun _ => rfl

/-- Routh–Hurwitz for the corrected SFR plant: for `M, T_g, T_R > 0` it is Hurwitz iff
`a₂ > 0`, `a₀ = K_R + D > 0` and `a₂ a₁ > a₃ a₀`. -/
@[tmio TM, powerlib_foundation] theorem isHurwitz_iff (hM : 0 < M) (hTg : 0 < Tg) (hTR : 0 < TR) :
    connection% ((⟨M, D, K, F, Tg, TR, hM, hTg, hTR⟩ : Model) ∈ family.den (.flow .globallyExponentiallyStable) ↔
      0 < coeff2 M D Tg TR ∧ 0 < coeff0 D K ∧ 0 < routhQuantity M D K F Tg TR) := by
  unfold TMIO.Statement
  rw [(connection_proof% SFR.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial))]
  change IsHurwitz (plant M D K F Tg TR).A ↔
      0 < coeff2 M D Tg TR ∧ 0 < coeff0 D K ∧ 0 < routhQuantity M D K F Tg TR
  have h3 : 0 < coeff3 M Tg TR := by unfold coeff3; positivity
  rw [Criteria.isHurwitz_fin_three_iff, trace_A hM.ne' hTg.ne' hTR.ne',
    det_A hM.ne' hTg.ne' hTR.ne', principalMinorSum_A hM.ne' hTg.ne' hTR.ne']
  have e : -coeff2 M D Tg TR / coeff3 M Tg TR * (coeff1 M D K F Tg TR / coeff3 M Tg TR) <
      -coeff0 D K / coeff3 M Tg TR ↔ 0 < routhQuantity M D K F Tg TR := by
    unfold routhQuantity
    rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) h3]
    constructor <;> intro h <;> nlinarith
  rw [e, neg_div, neg_div, neg_lt_zero, neg_lt_zero, div_pos_iff_of_pos_right h3,
    div_pos_iff_of_pos_right h3]

/-- Added stability condition: `F ≥ T_g/(T_g + T_R)` with `D, K_R ≥ 0`, `K_R + D > 0`. -/
@[tmio M, powerlib_foundation] theorem routh_of_hp_fraction (hM : 0 < M) (hTg : 0 < Tg)
    (hTR : 0 < TR) (hD : 0 ≤ D) (hK : 0 ≤ K) (hKD : 0 < K + D) (hF : Tg / (Tg + TR) ≤ F) :
    connection% ((⟨M, D, K, F, Tg, TR, hM, hTg, hTR⟩ : Model) ∈ realize Meets {.stable}) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets]
  change 0 < coeff2 M D Tg TR ∧ 0 < coeff0 D K ∧ 0 < routhQuantity M D K F Tg TR
  rw [routhQuantity_eq]
  have hsum : 0 < Tg + TR := by linarith
  have hF' : Tg ≤ F * (Tg + TR) := by rwa [div_le_iff₀ hsum] at hF
  have hF0 : 0 ≤ F := le_trans (div_nonneg hTg.le hsum.le) hF
  refine ⟨by unfold coeff2; positivity, by unfold coeff0; linarith, ?_⟩
  have h1 : 0 < M ^ 2 * (Tg + TR) := by positivity
  have h2 : 0 ≤ M * D * (Tg + TR) ^ 2 := by positivity
  have h3 : 0 ≤ M * K * TR * (F * (Tg + TR) - Tg) :=
    mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ D ^ 2 * Tg * TR * (Tg + TR) := by positivity
  have h5 : 0 ≤ D * K * F * Tg * TR ^ 2 := by positivity
  linarith

/-- Added stability condition, matrix form. -/
@[tmio TM, powerlib_foundation] theorem isHurwitz_of_hp_fraction (hM : 0 < M) (hTg : 0 < Tg)
    (hTR : 0 < TR) (hD : 0 ≤ D) (hK : 0 ≤ K) (hKD : 0 < K + D) (hF : Tg / (Tg + TR) ≤ F) :
    connection% ((⟨M, D, K, F, Tg, TR, hM, hTg, hTR⟩ : Model) ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% SFR.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial))]
  change IsHurwitz (plant M D K F Tg TR).A
  exact (((connection_proof% SFR.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) (x := (⟨M, D, K, F, Tg, TR, hM, hTg, hTR⟩ : Model))).symm.trans (isHurwitz_iff hM hTg hTR))).2 (((Spectral.mem_realize_singleton (meets := Meets)).mp (routh_of_hp_fraction hM hTg hTR hD hK hKD hF)))

/-- `a₀ < 0` (determinant `> 0`) or `a₂ < 0` (trace `> 0`): a characteristic root in the open
right half plane. -/
@[powerlib_foundation] theorem exists_root_of_unstable (hM : 0 < M) (hTg : 0 < Tg)
    (hTR : 0 < TR) (h : coeff0 D K < 0 ∨ coeff2 M D Tg TR < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix (plant M D K F Tg TR).A s).det = 0 ∧ 0 < s.re := by
  have h3 : 0 < coeff3 M Tg TR := by unfold coeff3; positivity
  have key : ∃ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 ∧
      (plant M D K F Tg TR).A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
    rcases h with h | h
    · refine Criteria.exists_eigenvalue_re_pos_of_det_pos_fin_three _ ?_
      rw [det_A hM.ne' hTg.ne' hTR.ne', neg_div]
      exact neg_pos.2 (div_neg_of_neg_of_pos h h3)
    · refine Criteria.exists_eigenvalue_re_pos_of_trace_pos_fin_three _ ?_
      rw [trace_A hM.ne' hTg.ne' hTR.ne', neg_div]
      exact neg_pos.2 (div_neg_of_neg_of_pos h h3)
  obtain ⟨μ, v, hv, heig, hre⟩ := key
  exact ⟨μ, Criteria.det_characteristicMatrix_eq_zero_of_eigenpair _ hv heig, hre⟩

/-! ## Steady state (§1.7) -/

/-- The equilibria for the load step are exactly the steady state. Static evidence on the
model, not a connection conclusion. -/
@[powerlib_foundation] theorem isEquilibrium_iff (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0)
    (hKD : K + D ≠ 0) (e : ℝ³) :
    IsEquilibrium ((plant M D K F Tg TR).inputField (load ΔPL)) e ↔ e = steadyState D K ΔPL := by
  unfold IsEquilibrium
  rw [field_apply]
  constructor
  · intro h
    have h0 := congrArg (fun v : ℝ³ => v 0) h
    have h1 := congrArg (fun v : ℝ³ => v 1) h
    have h2 := congrArg (fun v : ℝ³ => v 2) h
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, PiLp.zero_apply] at h0 h1 h2
    field_simp at h0 h1 h2
    have e2 : e 2 = -(K * e 0) := by linarith
    have e1 : e 1 = e 2 := by
      rw [e2] at h1
      have : Tg * (e 1 + K * e 0) = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hTg
      · linarith
    have e0 : e 0 = -ΔPL / (K + D) := by
      field_simp
      rw [e1, e2] at h0
      linarith
    ext i; fin_cases i
    · simpa [steadyState] using e0
    · simp only [steadyState, Fin.mk_one, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [e1, e2, e0]; ring
    · simp only [steadyState, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [e2, e0]; ring
  · rintro rfl
    ext i; fin_cases i <;> simp [steadyState] <;> field_simp <;> ring

/-- The steady state is an equilibrium of the load step. Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem steadyState_isEquilibrium (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hTR : TR ≠ 0) (hKD : K + D ≠ 0) :
    IsEquilibrium ((plant M D K F Tg TR).inputField (load ΔPL)) (steadyState D K ΔPL) :=
  (isEquilibrium_iff hM hTg hTR hKD _).2 rfl

/-! ## The family -/

/-- No model is both stable and unstable: the whole requirement language is inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  obtain ⟨h1, h2, -⟩ : Meets m .stable := h .stable
  rcases (h .unstable : Meets m .unstable) with h3 | h3 <;> linarith

@[tmio TM] private theorem den_hurwitz {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.den (.flow P) = {m | Meets m .stable}) := by
  change family.den (.flow P) = {m | Meets m .stable}
  rw [family_isLinear.den_hurwitz hP]
  ext m
  exact ((connection_proof% SFR.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (isHurwitz_iff m.M_pos m.Tg_pos m.TR_pos))

@[tmio TM] private theorem stable_mem_den {m : Model} (h : Meets m .stable) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ family.den (.flow P)) := by
  change m ∈ family.den (.flow P)
  rw [den_hurwitz hP]
  exact h

/-- The SFR translation is the linear table of `theorem/Spectral/LinearNamed.lean`. -/
private theorem translate_eq_linearTable (s : Sentence) :
    translate s = Spectral.linearTable {.stable} {.unstable} univ univ (fun a => {.rate a}) s := by
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- Every translation of the SFR family is sound: its translation chain lies below its semantics
connection (the linear table with the 3×3 Routh–Hurwitz criterion, right-half-plane roots, rate
margins, `Spectral.chain_le_semantics_of_linearTable_univ`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.chain_le_semantics_of_linearTable_univ (F := family) family_isLinear
    translate_eq_linearTable
    (fun m hm => (((connection_proof% SFR.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (isHurwitz_iff m.M_pos m.Tg_pos m.TR_pos))).mpr
      ((mem_realize _ _ _).mp hm .stable rfl))
    (fun m hm => exists_root_of_unstable m.M_pos m.Tg_pos m.TR_pos
      ((mem_realize _ _ _).mp hm .unstable rfl))
    fun a m hm => family_isLinear.mem_den_decay_of_rateMargin
      ((mem_realize _ _ _).mp hm (.rate a) rfl)

/-- On the attractive sentences and sampled contraction the chain agrees with the semantics: the
Routh–Hurwitz conditions are their exact translation. -/
@[tmio TM, powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.exact_of_linearTable (F := family) family_isLinear translate_eq_linearTable
    (fun m => Spectral.mem_realize_singleton.trans (((connection_proof% SFR.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (isHurwitz_iff m.M_pos m.Tg_pos m.TR_pos))).symm)
    hP

/-- The member characterization: a model satisfies an attractive sentence exactly when the
Routh–Hurwitz conditions hold. -/
@[tmio TM, powerlib_domain] theorem mem_den_attractive_iff (m : Model) {P : Flow.Property}
    (hP : P.Attractive) :
    connection% (m ∈ family.den (.flow P) ↔ m ∈ {m : Model | 0 < coeff2 m.M m.D m.Tg m.TR ∧
      0 < coeff0 m.D m.K ∧ 0 < routhQuantity m.M m.D m.K m.F m.Tg m.TR}) := by
  unfold powerlib.TMIO.Statement
  rw [den_hurwitz (Or.inl hP)]
  rfl

/-- §1.7 with the added sufficient condition `F ≥ T_g/(T_g + T_R)` (and `D, K_R ≥ 0`,
`K_R + D > 0`): the operating point is globally exponentially stable; by linearity so is the
steady state of every constant load step. -/
@[tmio TM, powerlib_domain] theorem mem_den_globallyExponentiallyStable (m : Model) (hD : 0 ≤ m.D)
    (hK : 0 ≤ m.K) (hKD : 0 < m.K + m.D) (hF : m.Tg / (m.Tg + m.TR) ≤ m.F) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact isHurwitz_of_hp_fraction m.M_pos m.Tg_pos m.TR_pos hD hK hKD hF

/-- `a₀ = K_R + D < 0` or `a₂ < 0` places a model in instability. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model)
    (h : coeff0 m.D m.K < 0 ∨ coeff2 m.M m.D m.Tg m.TR < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨s, hs, hre⟩ := exists_root_of_unstable m.M_pos m.Tg_pos m.TR_pos h
  exact family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 hs hre)

/-- With `0 < K_R + D` the model is not passive on its `(ΔP_L, Δω)` port: under the constant
load `ΔP_L = 1` the steady state is an equilibrium at which the port supplies
`−1/(K_R + D) < 0`. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_passive (m : Model) (hKD : 0 < m.K + m.D) :
    connection% (m ∉ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den), family_isLinear m, Sentence.holds_passive]
  refine Port.System.not_passive_of_equilibrium _ (x₀ := steadyState m.D m.K 1) (u₀ := load 1)
    (steadyState_isEquilibrium m.M_pos.ne' m.Tg_pos.ne' m.TR_pos.ne' hKD.ne') ?_
  have hsupply : m.plant.system.supply (steadyState m.D m.K 1) (load 1) =
      -1 / (m.K + m.D) := by
    simp [Port.System.supply, Model.plant, plant, Linear.Plant.system, load,
      steadyState, dotProduct, Fin.sum_univ_three]
  rw [hsupply]
  exact div_neg_of_neg_of_pos (by norm_num) hKD

/-! ## Correction: the note's §1.8 state matrix -/

/-- Transfer function of the corrected plant at `s = 0` (static gain `−1/(K_R + D)`). -/
@[powerlib_foundation] theorem transfer_zero (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    Linear.transfer (plant M D K F Tg TR) 0 0 0 = -1 / ((D + K : ℝ) : ℂ) := by
  rw [transfer_apply hM hTg hTR]
  push_cast
  ring_nf

/-- The note's §1.8 matrix has static gain `−1/(D + K_R (1 − F + F/T_g))`. -/
@[powerlib_foundation] theorem notePlant_transfer_zero (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hTR : TR ≠ 0) :
    Linear.transfer (notePlant M D K F Tg TR) 0 0 0 =
      -1 / ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  have hR' : (TR : ℂ) ≠ 0 := by exact_mod_cast hTR
  have hdet : (Linear.characteristicMatrix (notePlant M D K F Tg TR).A 0).det =
      ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) / (M * Tg * TR) := by
    simp [notePlant, Linear.characteristicMatrix, Matrix.det_fin_three]
    field_simp
    ring
  have hadj : (Linear.complexify (notePlant M D K F Tg TR).C *
      (Linear.characteristicMatrix (notePlant M D K F Tg TR).A 0).adjugate *
        Linear.complexify (notePlant M D K F Tg TR).B) 0 0 = -1 / (M * Tg * TR) := by
    simp [notePlant, Linear.characteristicMatrix, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_three]
    field_simp
  have hD : Linear.complexify (notePlant M D K F Tg TR).D 0 0 = 0 := by simp [notePlant]
  rw [Linear.transfer_eq_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, hadj, hD, smul_eq_mul, add_zero, hdet]
  by_cases h : ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) = 0
  · rw [h]; simp
  · field_simp

/-- Correction (§1.8): whenever `K_R F (1 − T_g) ≠ 0` the note's state matrix and the corrected
one have different transfer functions (already at `s = 0`), so the note's matrix does not
realise the §1.4 transfer function. -/
@[powerlib_foundation] theorem notePlant_transfer_ne (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0)
    (hK : K ≠ 0) (hF : F ≠ 0) (hT1 : Tg ≠ 1) :
    Linear.transfer (notePlant M D K F Tg TR) 0 0 0 ≠
      Linear.transfer (plant M D K F Tg TR) 0 0 0 := by
  rw [notePlant_transfer_zero hM hTg hTR, transfer_zero hM hTg hTR]
  intro h
  have h1 : ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) = ((D + K : ℝ) : ℂ) := by
    rwa [neg_div, neg_div, neg_inj, one_div, one_div, _root_.inv_inj] at h
  have h2 : D + K * (1 - F + F / Tg) = D + K := by exact_mod_cast h1
  have h3 : K * F * (1 - Tg) = 0 := by
    field_simp at h2
    linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact hK h
    · exact hF h
  · exact hT1 (by linarith)

/-! ## Second-order reduction (§1.5) and exact nadir (§1.6) -/

/-- Reduced SFR (`T_g → 0`), state `(Δω, ΔP_RH)` with `ΔP_RH = ΔP_m + F K_R Δω`. -/
def reducedPlant (M D K F TR : ℝ) : Linear.Plant 2 1 :=
  SwingGovernor.plant M (D + F * K) ((1 - F) * K) TR

/-- Reduced swing row: `M Δω̇ = ΔP_m − ΔP_L − D Δω` with `ΔP_m = ΔP_RH − F K_R Δω`. -/
@[powerlib_foundation] theorem reduced_field_swing (hM : M ≠ 0) (x : EuclideanSpace ℝ (Fin 2)) :
    M * (reducedPlant M D K F TR).inputField (load ΔPL) x 0 =
      (x 1 - F * K * x 0) - ΔPL - D * x 0 := by
  rw [reducedPlant, SwingGovernor.field_swing hM]
  ring

/-- Reduced turbine: with `ΔP_v = −K_R Δω` (static governor) and `ΔP_m = ΔP_RH − F K_R Δω`,
the field satisfies `T_R ΔṖ_m + ΔP_m = ΔP_v + F T_R ΔṖ_v`, i.e. `G_turb`. -/
@[powerlib_foundation] theorem reduced_field_turbine (hTR : TR ≠ 0)
    (x : EuclideanSpace ℝ (Fin 2)) :
    let f := (reducedPlant M D K F TR).inputField (load ΔPL) x
    TR * (f 1 - F * K * f 0) + (x 1 - F * K * x 0) = -K * x 0 + F * TR * (-K * f 0) := by
  intro f
  have h := SwingGovernor.field_governor (M := M) (D := D + F * K) (K := (1 - F) * K)
    (ΔPL := ΔPL) hTR x
  change TR * ((SwingGovernor.plant M (D + F * K) ((1 - F) * K) TR).inputField (load ΔPL) x 1 -
      F * K * (SwingGovernor.plant M (D + F * K) ((1 - F) * K) TR).inputField (load ΔPL) x 0) +
      (x 1 - F * K * x 0) = -K * x 0 + F * TR * (-K *
        (SwingGovernor.plant M (D + F * K) ((1 - F) * K) TR).inputField (load ΔPL) x 0)
  linear_combination h

/-- §1.5 transfer function `−(1 + T_R s)/(M T_R s² + (M + (D + K_R F) T_R) s + (K_R + D))`. -/
@[powerlib_foundation] theorem reduced_transfer_apply (hM : M ≠ 0) (hTR : TR ≠ 0) (s : ℂ) :
    Linear.transfer (reducedPlant M D K F TR) s 0 0 =
      -(1 + (TR : ℂ) * s) / ((M : ℂ) * TR * s ^ 2 + (M + (D + K * F) * TR) * s + (K + D)) := by
  rw [reducedPlant, SwingGovernor.transfer_apply hM hTR]
  push_cast
  ring_nf

/-- §1.5 boxed: `ω_n² = (K_R + D)/(M T_R)`. -/
@[powerlib_foundation] theorem reduced_natFreq_sq (hM : 0 < M) (hTR : 0 < TR)
    (hKD : 0 ≤ K + D) :
    SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR ^ 2 = (K + D) / (M * TR) := by
  rw [SwingGovernor.natFreq_sq hM hTR (by linarith)]
  ring_nf

/-- §1.5 boxed: `2 ζ ω_n = (M + (D + K_R F) T_R)/(M T_R)`. -/
@[powerlib_foundation] theorem reduced_two_mul_dampingRatio_mul_natFreq (hM : 0 < M)
    (hTR : 0 < TR) (hKD : 0 < K + D) :
    2 * SwingGovernor.dampingRatio M (D + F * K) ((1 - F) * K) TR *
        SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR =
      (M + (D + K * F) * TR) / (M * TR) := by
  rw [SwingGovernor.two_mul_dampingRatio_mul_natFreq hM hTR (by linarith)]
  ring_nf

/-- The reduced model as a member of the swing + governor family. -/
def reducedModel (M D K F TR : ℝ) (hM : 0 < M) (hTR : 0 < TR) : SwingGovernor.Model :=
  ⟨M, D + F * K, (1 - F) * K, TR, hM, hTR⟩

@[powerlib_foundation] theorem reducedModel_plant (hM : 0 < M) (hTR : 0 < TR) :
    (reducedModel M D K F TR hM hTR).plant = reducedPlant M D K F TR := rfl

/-- The reduced SFR model (`0 ≤ D + F K_R`, `0 < K_R + D`) is globally exponentially stable as a
member of the swing + governor family. -/
@[tmio TM, powerlib_domain] theorem reduced_mem_den_globallyExponentiallyStable (hM : 0 < M)
    (hTR : 0 < TR) (hD : 0 ≤ D + F * K) (hKD : 0 < K + D) :
    connection% (reducedModel M D K F TR hM hTR ∈
      SwingGovernor.family.den (.flow .globallyExponentiallyStable)) :=
  SwingGovernor.mem_den_globallyExponentiallyStable _ hD (by
    change 0 < (1 - F) * K + (D + F * K)
    linarith)

/-- `arg (σ − 1/T_R + j ω_d) = arg (σ T_R − 1 + j ω_d T_R)` for `T_R > 0`. -/
@[powerlib_foundation] theorem arg_scale {σ ωd : ℝ} (hTR : 0 < TR) :
    Complex.arg ⟨σ - 1 / TR, ωd⟩ = Complex.arg ⟨σ * TR - 1, ωd * TR⟩ := by
  have h : (⟨σ - 1 / TR, ωd⟩ : ℂ) = ((1 / TR : ℝ) : ℂ) * ⟨σ * TR - 1, ωd * TR⟩ := by
    apply Complex.ext <;> simp <;> field_simp
  rw [h, Complex.arg_real_mul _ (by positivity)]

/-- The note's §1.6 nadir time `arctan(ω_d T_R/(1 − σ T_R))/ω_d`. -/
def noteNadirTime (σ ωd TR : ℝ) : ℝ := Real.arctan (ωd * TR / (1 - σ * TR)) / ωd

/-- Correction (§1.6): for `σ T_R > 1` (`σ = ζ ω_n`) the note's formula is the negative of the
true first-minimum time `arg (σ − 1/T_R + j ω_d)/ω_d`. -/
@[powerlib_foundation] theorem noteNadirTime_eq_neg {σ ωd : ℝ} (hTR : 0 < TR) (hωd : 0 < ωd)
    (h : 1 < σ * TR) :
    noteNadirTime σ ωd TR = -(Complex.arg ⟨σ - 1 / TR, ωd⟩ / ωd) ∧
      noteNadirTime σ ωd TR < 0 := by
  have harg : Complex.arg ⟨σ - 1 / TR, ωd⟩ = Real.arctan (ωd * TR / (σ * TR - 1)) := by
    rw [arg_scale hTR, SpecialFunctions.arg_eq_arctan (by linarith)]
  have heq : noteNadirTime σ ωd TR = -(Complex.arg ⟨σ - 1 / TR, ωd⟩ / ωd) := by
    rw [harg, noteNadirTime, show ωd * TR / (1 - σ * TR) = -(ωd * TR / (σ * TR - 1)) by
      rw [← div_neg, neg_sub], Real.arctan_neg, neg_div]
  refine ⟨heq, ?_⟩
  rw [heq, neg_neg_iff_pos]
  exact SwingGovernor.tCrit_pos hωd

/-- Exact nadir value of the reduced model with the §1.5 parameters substituted. -/
@[powerlib_foundation] theorem reduced_nadirValue_eq :
    SwingGovernor.nadirValue M (D + F * K) ((1 - F) * K) TR ΔPL =
      -ΔPL / (K + D) * (1 + Real.sqrt (1 -
        2 * SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR * TR +
          SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR ^ 2 * TR ^ 2) *
        Real.exp (-(SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR *
          SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR))) := by
  unfold SwingGovernor.nadirValue
  rw [show (1 - F) * K + (D + F * K) = K + D by ring]

/-- The reduced model's nadir time in the corrected §1.6 form
`t_n = atan2(ω_d T_R, ζ ω_n T_R − 1)/ω_d`. -/
@[powerlib_foundation] theorem reduced_nadirTime_eq (hTR : 0 < TR) :
    SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR =
      Complex.arg ⟨SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR * TR - 1,
        SwingGovernor.dampedFreq M (D + F * K) ((1 - F) * K) TR * TR⟩ /
        SwingGovernor.dampedFreq M (D + F * K) ((1 - F) * K) TR := by
  unfold SwingGovernor.nadirTime
  rw [arg_scale hTR]

/-! ## Implementation evidence (private, trajectory level) -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.7: from rest, `Δω̇(0⁺) = −ΔP_L/M` (the turbine zero does not change the initial slope). -/
private theorem rocof {x : ℝ → ℝ³}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K F Tg TR).inputField (load ΔPL) y)
      (Ici 0)) (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => x t 0) (-ΔPL / M) (Ici 0) 0 := by
  have h := LTI.hasDerivWithinAt_apply_zero hx 0
  rw [field_apply, h0] at h
  convert h using 1
  simp only [Fin.isValue, Matrix.cons_val_zero, PiLp.zero_apply]
  ring

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.7 with the added sufficient condition `F ≥ T_g/(T_g + T_R)`: `Δω(t) → −ΔP_L/(K_R + D)` along
every forward solution under the load step. -/
private theorem tendsto_freq (hM : 0 < M) (hTg : 0 < Tg) (hTR : 0 < TR)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hKD : 0 < K + D) (hF : Tg / (Tg + TR) ≤ F) {x : ℝ → ℝ³}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K F Tg TR).inputField (load ΔPL) y)
      (Ici 0)) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ΔPL / (K + D))) := by
  have h := LTI.tendsto_apply_of_isHurwitz (plant M D K F Tg TR)
    (steadyState_isEquilibrium hM.ne' hTg.ne' hTR.ne' hKD.ne')
    (((connection_proof% SFR.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) (x := (⟨M, D, K, F, Tg, TR, hM, hTg, hTR⟩ : Model))).mp (isHurwitz_of_hp_fraction hM hTg hTR hD hK hKD hF))) hx 0
  simpa using h

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.6 corrected and exact: for the reduced SFR model with `ζ < 1` and a load increase, from rest,
`Δω` decreases strictly up to `t_n = atan2(ω_d T_R, ζ ω_n T_R − 1)/ω_d > 0`, attains its minimum
over `t ≥ 0` there, and the minimum is
`−ΔP_L/(K_R + D)·[1 + √(1 − 2 ζ ω_n T_R + ω_n² T_R²) e^{−ζ ω_n t_n}]`. -/
private theorem reduced_nadir (hM : 0 < M) (hTR : 0 < TR) (hD : 0 ≤ D + F * K)
    (hKD : 0 < K + D) (hP : 0 < ΔPL)
    (hζ : SwingGovernor.dampingRatio M (D + F * K) ((1 - F) * K) TR < 1)
    {x : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hx : IsIntegralCurveOn x (fun _ y => (reducedPlant M D K F TR).inputField (load ΔPL) y)
      (Ici 0)) (h0 : x 0 = 0) :
    0 < SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR ∧
      StrictAntiOn (fun t => x t 0)
        (Icc 0 (SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR)) ∧
      IsMinOn (fun t => x t 0) (Ici 0)
        (SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR) ∧
      x (SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR) 0 =
        -ΔPL / (K + D) * (1 + Real.sqrt (1 -
          2 * SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR * TR +
            SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR ^ 2 * TR ^ 2) *
          Real.exp (-(SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR *
            SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR))) := by
  set D' := D + F * K
  set K' := (1 - F) * K
  have hKD' : 0 < K' + D' := by simp only [K', D']; linarith
  have hsum : K' + D' = K + D := by simp only [K', D']; ring
  have hωd := SwingGovernor.dampedFreq_pos hM hTR hD hKD' hζ
  have hσ := SwingGovernor.decayRate_nonneg hM hTR hD hKD'
  have hc : 0 < ΔPL / (K' + D') := div_pos hP hKD'
  have hT : SwingGovernor.nadirTime M D' K' TR =
      SwingGovernor.tCrit (SwingGovernor.decayRate M D' K' TR)
        (SwingGovernor.dampedFreq M D' K' TR) TR := rfl
  have hfreq : ∀ {t : ℝ}, 0 ≤ t → x t 0 = SwingGovernor.respC (ΔPL / (K' + D'))
      (SwingGovernor.decayRate M D' K' TR) (SwingGovernor.dampedFreq M D' K' TR) TR t := by
    intro t ht
    rw [LTI.trajectory_eq_osc2 (SwingGovernor.plant M D' K' TR)
      (SwingGovernor.steadyState_isEquilibrium hM.ne' hTR.ne' hKD'.ne')
      (SwingGovernor.trace_A hM hTR hKD') (SwingGovernor.det_A hM hTR hD hKD' hζ) hωd.ne' hx ht,
      h0]
    exact SwingGovernor.osc2_freq hM hTR hD hKD' hζ t
  have hT0 : 0 < SwingGovernor.nadirTime M D' K' TR := hT ▸ SwingGovernor.tCrit_pos hωd
  refine ⟨hT0, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only
    rw [hfreq ha.1, hfreq hb.1]
    exact SwingGovernor.respC_strictAntiOn hωd hTR hc (hT ▸ ha) (hT ▸ hb) hab
  · intro t ht
    simp only [Set.mem_ofPred_eq]
    rw [hfreq ht, hfreq hT0.le, hT]
    exact SwingGovernor.respC_isMinOn hωd hTR hσ hc ht
  · rw [hfreq hT0.le, SwingGovernor.respC_nadirTime hM hTR hD hKD' hζ]
    exact reduced_nadirValue_eq

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Reduced model: from rest, `Δω̇(0⁺) = −ΔP_L/M` (§1.7). -/
private theorem reduced_rocof {x : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hx : IsIntegralCurveOn x (fun _ y => (reducedPlant M D K F TR).inputField (load ΔPL) y)
      (Ici 0)) (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => x t 0) (-ΔPL / M) (Ici 0) 0 := by
  have h := LTI.hasDerivWithinAt_apply_zero hx 0
  rw [reducedPlant, SwingGovernor.field_apply, h0] at h
  convert h using 1
  simp only [Fin.isValue, Matrix.cons_val_zero, PiLp.zero_apply]
  ring

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Reduced model: `Δω → −ΔP_L/(K_R + D)` along every forward solution (`0 ≤ D + F K_R`). -/
private theorem reduced_tendsto_freq (hM : 0 < M) (hTR : 0 < TR) (hD : 0 ≤ D + F * K)
    (hKD : 0 < K + D) {x : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hx : IsIntegralCurveOn x (fun _ y => (reducedPlant M D K F TR).inputField (load ΔPL) y)
      (Ici 0)) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ΔPL / (K + D))) := by
  have hKD' : 0 < (1 - F) * K + (D + F * K) := by linarith
  have h := LTI.tendsto_apply_of_isHurwitz (reducedPlant M D K F TR)
    (SwingGovernor.steadyState_isEquilibrium hM.ne' hTR.ne' hKD'.ne')
    ((((connection_proof% SwingGovernor.family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).symm.trans (SwingGovernor.isHurwitz_iff_of_nonneg hM hTR hD))).2 hKD') hx 0
  rw [SwingGovernor.steadyState_zero, show (1 - F) * K + (D + F * K) = K + D by ring] at h
  exact h

/-- The same models under the symbolic constant input, translated about its selected
steady state. Its system map reads the forced field with the symbolic input held constant. -/
def loadStepFamily (ΔPL : ℝ) : Family Model Requirement 3 0 :=
  ⟨fun m => Port.System.autonomous (fun z => m.plant.inputField (load ΔPL) (z + (steadyState m.D m.K ΔPL))),
    family.meets, family.translate⟩

/-- Connection for the forced field at its selected steady state.
Under the Routh–Hurwitz conditions every solution under the load step converges exponentially to
the steady state (the connection theorem `mem_den_attractive_iff` and linearity,
`Linear.holds_input_iff`). -/
@[tmio TM] private theorem exponentiallyConvergesTo_steadyState (m : Model)
    (h2 : 0 < coeff2 m.M m.D m.Tg m.TR) (hKD : 0 < m.K + m.D)
    (hR : 0 < routhQuantity m.M m.D m.K m.F m.Tg m.TR) (ΔPL : ℝ) :
    connection% (m ∈ (loadStepFamily ΔPL).den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.plant.inputField (load ΔPL)) (pt := fun m : Model => steadyState m.D m.K ΔPL)
    (show (loadStepFamily ΔPL).IsAutonomous (fun m z => m.plant.inputField (load ΔPL) (z + (steadyState m.D m.K ΔPL))) from fun _ => rfl))]
  change Flow.GloballyExponentiallyStable (m.plant.inputField (load ΔPL))
      (steadyState m.D m.K ΔPL)
  have hmem := (mem_den_attractive_iff m (P := .globallyExponentiallyStable) (by simp)).2
    ⟨h2, by unfold coeff0; linarith, hR⟩
  rw [family_isLinear.den_hurwitz (Or.inl (by simp))] at hmem
  exact (Linear.holds_input_iff m.plant
    (steadyState_isEquilibrium m.M_pos.ne' m.Tg_pos.ne' m.TR_pos.ne' hKD.ne')
    (P := .globallyExponentiallyStable) (by simp)).2 hmem

end powerlib.Frequency.SFR
