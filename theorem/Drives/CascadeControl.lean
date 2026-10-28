import theorem.Spectral.Family
import theorem.CurrentControl.IMC
import theorem.Transform.SpaceVector
import theorem.Criteria.Hurwitz2
import theorem.Numerics.StabilityFunctions

/-! # Machine-drive cascade loops: IMC current loop, speed loop, forward-Euler limit

The IMC-tuned stator current loop of a machine drive as a linear family, with the speed-loop
transfer function, the forward-Euler stability limit and the complex-vector current equation.

Model boundary.
The IMC current-loop family:
* Plant: one axis of the decoupled stator current loop, an RL load
  `L di/dt = v − R i` with `L > 0`, `R > 0` (for a machine: `L = σL_s` or `L_d`/`L_q`,
  `R = r_s'`, after ideal cross-coupling and back-EMF feedforward, see
  `decoupled_axis_eq_rl`). Single real axis, continuous time.
* Controller: PI on the error `e = i* − i`, `v = K_p e + K_i ξ`, `ξ̇ = e`, with the IMC tuning
  `K_p = L α`, `K_i = R α`, bandwidth `α > 0`. Constant reference `i*`.
* State order `(i, ξ) ∈ EuclideanSpace ℝ (Fin 2)`; the closed loop is the linear plant `imcModel`
  with input `i*` and output `i`. No PWM, sampling, delay, voltage saturation or anti-windup;
  parameters exact (controller `L, R` equal the plant's).
* The speed loop and the complex-vector equation are static transfer-function / algebra results
  (ideal transparent current loop, rigid mechanics `J ω̇ = K_t i_q`).

Source: work-sync `theory/T-field-oriented-control.md` §1.5 (IMC tuning), §1.8 (speed loop),
§1.9 (forward Euler, complex-vector form); `theory/T-gfl-control.md` (same IMC rule).

Results (foundation).
* `siso2_transfer`: transfer function of a two-state SISO realization (adjugate formula).
* `imcModel_transfer`: the IMC closed loop is **exactly** `α/(s + α)` at every `s` that is not
  a closed-loop eigenvalue (`s ≠ −α`, `s ≠ −R/L`); the plant pole `−R/L` is cancelled by the
  PI zero, so it stays an (unobservable from the transfer function) eigenvalue of the
  realization.
* `imcModel_isHurwitz_iff`, `imcModel_exists_root`: the loop is Hurwitz iff the monic
  coefficients `α + R/L`, `Rα/L` are positive; a negative one gives a right-half-plane root.
* `speedLoop_transfer`: speed PI around an ideal (transparent) current loop and the rigid
  mechanics `J ω̇ = K_t i_q`: `ω/ω* = K_t (K_p s + K_i) / (J s² + K_t K_p s + K_t K_i)`;
  `speedLoop_denominator_tuned`: pole placement with `K_p = 2ζω_n J/K_t`, `K_i = ω_n² J/K_t`.
* Forward-Euler discretization of the target first-order loop `ė = −α e` with period `T_s`
  converges for every initial error iff `0 < α T_s < 2`
  (`Numerics.eulerFirstOrder_tendsto_zero_iff`, `theorem/Numerics/StabilityFunctions.lean`).
* `complexVector_iff`: the complex-vector current equation
  `σL_s di/dt = v − r' i − jω_e σL_s i + e` is the pair of real dq equations of FOC note §1.5.

Family and connection conclusions.
* `family : Family IMCLoop Spectral.Requirement 2 1` reads a parameter triple `(L, R, α)` as the
  port system of `imcModel` (`Family.IsLinear`, `Spectral.linearFamily`); a flow sentence speaks
  about the loop at the equilibrium `(i*, i*/α)` of every constant reference
  (`Linear.holds_input_iff`). Requirements: the monic characteristic coefficients `α + R/L` and
  `R α / L` positive (`stable`) or one of them negative (`unstable`).
* `chain_le_semantics`, `exact`: every translation sound; the attractive sentences and sampled
  contraction carved out exactly.
* `mem_den`: for `L, R, α > 0` the loop satisfies every attractive sentence (closed-loop
  eigenvalues `−α`, `−R/L`).
* The exponential tracking estimate of every closed-loop trajectory and `i(t) → i*`
  (`imcLoop_exponentiallyStable_tracking`, `imcLoop_current_tendsto`) are trajectory-level
  results outside the sentence language, kept as private implementation evidence.
* The same IMC rule on the converter current loop (IN-positive R–L branch, bandwidth `ω_b`) is
  `CurrentControl.imc` in `theorem/CurrentControl/IMC.lean` (`imc_transfer_eq`,
  `imc_mem_den_iff`), read through the single-axis PI-loop family `CurrentControl.PIParams.family`
  of `theorem/CurrentControl/PILoop.lean`; `IMCLoop` is the machine-drive form of that loop. For
  `L ≠ 0` the two are the same plant (`imcModel_eq`), so every sentence of the drive loop is read
  through the converter family (`mem_den_iff_imc`, a connection statement), and `mem_den` is the
  converter result `imc_mem_den_iff` read back. Scaffold: `theorem/IMCCurrentLoop.agda`.

Corrections.
* FOC note §1.8: the "bandwidth-separated" speed loop
  `(K_p s + K_i)/(J s + K_p s + K_i) · K_t/K_t` is not a valid transfer function of the stated
  loop; with an ideal current loop the closed loop is
  `K_t (K_p s + K_i)/(J s² + K_t K_p s + K_t K_i)` (`speedLoop_transfer`), consistent with the
  note's gain rule `K_p = 2ζω_n J/K_t`, `K_i = ω_n² J/K_t`.
* FOC note §1.9: the complex form is written with `− e` although §1.5 has `+ e_d, + e_q`;
  the complex equation equivalent to §1.5 has `+ e` (`complexVector_iff`).
* "IMC closed loop ≈ α/(s+α)" (§1.5) is in fact exact (`imcModel_transfer`).
-/

noncomputable section
namespace powerlib.Drives.CascadeControl

open Matrix Filter Topology Linear LinearSystems

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Two-state SISO transfer functions -/

/-- Two-state single-input single-output realization `(A, B, C, 0)`. -/
def siso2 (a b c d b1 b2 c1 c2 : ℝ) : Plant 2 1 :=
  ⟨!![a, b; c, d], !![b1; b2], !![c1, c2], 0⟩

@[tmio T, powerlib_foundation] theorem siso2_det_characteristicMatrix (a b c d b1 b2 c1 c2 : ℝ) (s : ℂ) :
    (characteristicMatrix (siso2 a b c d b1 b2 c1 c2).A s).det =
      (s - a) * (s - d) - b * c := by
  simp [characteristicMatrix, siso2, Matrix.det_fin_two]

@[tmio T, powerlib_foundation] theorem siso2_transfer (a b c d b1 b2 c1 c2 : ℝ) (s : ℂ)
    (hdet : (s - a) * (s - d) - b * c ≠ 0) :
    transfer (siso2 a b c d b1 b2 c1 c2) s 0 0 =
      ((c1 : ℂ) * ((s - d) * b1 + b * b2) + c2 * (c * b1 + (s - a) * b2)) /
        ((s - a) * (s - d) - b * c) := by
  rw [transfer_eq_adjugate, siso2_det_characteristicMatrix]
  simp [siso2, Matrix.adjugate_fin_two, characteristicMatrix, Matrix.mul_apply,
    Fin.sum_univ_two]
  field_simp
  ring

/-! ## IMC current loop -/

/-- RL plant `L di/dt = v − R i`, solved for `di/dt`. -/
def rlField (L R i v : ℝ) : ℝ := (v - R * i) / L

/-- PI controller output `K_p e + K_i ξ`. -/
def piOutput (Kp Ki e ξ : ℝ) : ℝ := Kp * e + Ki * ξ

/-- Closed loop of the RL plant and the IMC-tuned PI (`K_p = Lα`, `K_i = Rα`), state
`(i, ξ)`, constant reference `iref`. -/
def imcField (L R α iref : ℝ) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![rlField L R (x 0) (piOutput (L * α) (R * α) (iref - x 0) (x 1)), iref - x 0]

/-- The IMC closed loop as a linear plant with input `i*` and output `i`. -/
def imcModel (L R α : ℝ) : Plant 2 1 :=
  siso2 (-(α + R / L)) (R * α / L) (-1) 0 α 1 1 0

/-- The closed-loop field is exactly the plant's field with input `i*`. -/
@[powerlib_foundation] theorem imcField_eq_model (L R α iref : ℝ) (hL : L ≠ 0) (x : ℝ²) :
    imcField L R α iref x = (imcModel L R α).inputField (fun _ => iref) x := by
  ext j
  fin_cases j
  · simp [imcField, imcModel, siso2, Plant.inputField, op, Matrix.mulVec, rlField, piOutput,
      dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [imcField, imcModel, siso2, Plant.inputField, op, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    ring

/-- **The IMC current loop is exactly first order**: `i(s)/i*(s) = α/(s + α)` at every `s`
that is not a closed-loop eigenvalue. -/
@[powerlib_foundation] theorem imcModel_transfer (L R α : ℝ) (s : ℂ)
    (h1 : s + α ≠ 0) (h2 : s + (R / L : ℝ) ≠ 0) :
    transfer (imcModel L R α) s 0 0 = α / (s + α) := by
  have hdet : ((s - ((-(α + R / L) : ℝ) : ℂ)) * (s - ((0 : ℝ) : ℂ)) -
      ((R * α / L : ℝ) : ℂ) * ((-1 : ℝ) : ℂ)) = (s + α) * (s + (R / L : ℝ)) := by
    push_cast
    field_simp
    ring
  unfold imcModel
  rw [siso2_transfer _ _ _ _ _ _ _ _ s (by rw [hdet]; exact mul_ne_zero h1 h2), hdet]
  push_cast
  push_cast at h2
  field_simp
  ring

/-- Closed-loop state matrix `[[−(α + R/L), Rα/L], [−1, 0]]`. -/
@[powerlib_foundation] theorem imcModel_A (L R α : ℝ) :
    (imcModel L R α).A = !![-(α + R / L), R * α / L; -1, 0] := rfl

/-- Hurwitz criterion of the IMC loop: the monic characteristic coefficients `α + R/L` and
`Rα/L` are positive. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem imcModel_isHurwitz_iff (L R α : ℝ) :
    IsHurwitz (imcModel L R α).A ↔ 0 < α + R / L ∧ 0 < R * α / L := by
  rw [imcModel_A, Criteria.isHurwitz_fin_two_of_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- A negative monic coefficient gives a characteristic root in the open right half plane. -/
@[powerlib_foundation] theorem imcModel_exists_root (L R α : ℝ)
    (h : α + R / L < 0 ∨ R * α / L < 0) :
    ∃ s : ℂ, (characteristicMatrix (imcModel L R α).A s).det = 0 ∧ 0 < s.re := by
  rw [imcModel_A]
  rcases h with h | h
  · refine Criteria.exists_characteristic_root_re_pos_of_trace_pos _ ?_
    rw [Matrix.trace_fin_two_of]
    linarith
  · refine Criteria.exists_characteristic_root_re_pos_of_det_neg _ ?_
    rw [Matrix.det_fin_two_of]
    linarith

/-- Closed-loop equilibrium `(i*, i*/α)`. -/
def imcEquilibrium (α iref : ℝ) : ℝ² := WithLp.toLp 2 ![iref, iref / α]

@[powerlib_foundation] theorem imc_isEquilibrium (L R α iref : ℝ) (hL : L ≠ 0) (hα : α ≠ 0) :
    IsEquilibrium ((imcModel L R α).inputField fun _ => iref) (imcEquilibrium α iref) := by
  rw [IsEquilibrium, ← imcField_eq_model L R α iref hL]
  ext j
  fin_cases j
  · have h : R * α * (iref / α) - R * iref = 0 := by field_simp; ring
    simp [imcField, imcEquilibrium, rlField, piOutput, h]
  · simp [imcField, imcEquilibrium]

/-! ### The IMC current-loop family -/

/-- An IMC-tuned current loop: plant inductance and resistance, bandwidth. The converter-side
form of the same loop is `CurrentControl.imc` (`theorem/CurrentControl/IMC.lean`) on
`CurrentControl.PIParams` (`theorem/CurrentControl/PILoop.lean`). -/
@[ext] structure IMCLoop where
  L : ℝ
  R : ℝ
  α : ℝ

/-- The plant of the loop. -/
def IMCLoop.plant (m : IMCLoop) : Plant 2 1 := imcModel m.L m.R m.α

/-- Stability condition: positive monic coefficients `α + R/L`, `Rα/L`. -/
def IMCLoop.Stable (m : IMCLoop) : Prop := 0 < m.α + m.R / m.L ∧ 0 < m.R * m.α / m.L

/-- Instability condition: a negative monic coefficient. -/
def IMCLoop.Unstable (m : IMCLoop) : Prop := m.α + m.R / m.L < 0 ∨ m.R * m.α / m.L < 0

/-- The IMC current-loop family: every loop read as the port system of its plant (input `i*`,
output `i`). -/
def family : Family IMCLoop Spectral.Requirement 2 1 :=
  Spectral.linearFamily IMCLoop.plant IMCLoop.Stable IMCLoop.Unstable

@[powerlib_foundation] theorem family_isLinear : family.IsLinear IMCLoop.plant :=
  Spectral.linearFamily_isLinear _ _ _

/-! ### The converter PI-loop reading -/

/-- The IMC loop is the converter PI loop with IMC tuning: for `L ≠ 0` its plant is the plant of
`CurrentControl.imc L R α` (`K_p = Lα`, `K_i = Rα`). Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem imcModel_eq (L R α : ℝ) (hL : L ≠ 0) :
    imcModel L R α = (CurrentControl.imc L R α).model := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [imcModel, siso2, CurrentControl.PIParams.model, CurrentControl.imc] <;> field_simp
  ring

/-- For `L ≠ 0` an IMC current loop satisfies exactly the sentences of the converter PI loop with
IMC tuning `CurrentControl.imc L R α`: the two families read the same plant (`imcModel_eq`). A
comparison of the two semantics connections at the two members. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_imc (m : IMCLoop) (hL : m.L ≠ 0) (s : Sentence) :
    connection% (m ∈ family.den s ↔
      CurrentControl.imc m.L m.R m.α ∈ CurrentControl.PIParams.family.den s) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den, Family.mem_den, family_isLinear m, CurrentControl.PIParams.family_isLinear _]
  simp only [IMCLoop.plant, imcModel_eq _ _ _ hL]

/-- Every translation of the IMC family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_chain_le_semantics (fun m h => (imcModel_isHurwitz_iff _ _ _).mpr h)
    (fun m h => imcModel_exists_root _ _ _ h)

/-- The attractive sentences and sampled contraction of the IMC loop are carved out exactly by
positive monic coefficients. -/
@[tmio TM, powerlib_domain] theorem exact {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.linear_exact (fun m => (imcModel_isHurwitz_iff _ _ _).symm) hP

/-- For `L, R, α > 0` the IMC current loop satisfies every attractive sentence (closed-loop
eigenvalues `−α`, `−R/L`), in particular global exponential stability; read from the converter
loop (`mem_den_iff_imc`, `CurrentControl.imc_mem_den_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den (L R α : ℝ) (hL : 0 < L) (hR : 0 < R) (hα : 0 < α)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (⟨L, R, α⟩ ∈ family.den (.flow P)) := by
  have hr := mem_den_iff_imc ⟨L, R, α⟩ hL.ne' (.flow P)
  have hc := CurrentControl.imc_mem_den_iff (R := R) hL hα hP
  unfold powerlib.TMIO.Statement at hr hc ⊢
  exact hr.mpr (hc.mpr (div_pos hR hL))

/-- **IMC current loop: exponential tracking of a constant reference.** For `L, R, α > 0` there
are uniform constants `K, rate > 0` such that every closed-loop trajectory satisfies
`‖(i(t) − i*, ξ(t) − i*/α)‖ ≤ K e^{−rate t} ‖(i(0) − i*, ξ(0) − i*/α)‖` for `t ≥ 0`;
in particular `|i(t) − i*|` obeys the same bound.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem imcLoop_exponentiallyStable_tracking (L R α iref : ℝ) (hL : 0 < L)
    (hR : 0 < R) (hα : 0 < α) :
    ∃ K > 0, ∃ rate > 0, ∀ x : ℝ → ℝ²,
      (∀ t, HasDerivAt x (imcField L R α iref (x t)) t) → ∀ t, 0 ≤ t →
        ‖x t - imcEquilibrium α iref‖ ≤
            K * Real.exp (-(rate * t)) * ‖x 0 - imcEquilibrium α iref‖ ∧
          |x t 0 - iref| ≤ K * Real.exp (-(rate * t)) * ‖x 0 - imcEquilibrium α iref‖ := by
  have hA : IsHurwitz (imcModel L R α).A := by
    rw [imcModel_isHurwitz_iff]
    have : 0 < R / L := div_pos hR hL
    exact ⟨by linarith, by positivity⟩
  set e := imcEquilibrium α iref
  have he := imc_isEquilibrium L R α iref hL.ne' hα.ne'
  obtain ⟨-, -, K, rate, hK, hrate, hbound⟩ := globallyExponentiallyStable_of_isHurwitz e hA
  refine ⟨K, by linarith, rate, hrate, fun x hx t ht => ?_⟩
  have htraj : IsTrajectoryOn x (affineLinearVectorField (imcModel L R α).A e) 0 t :=
    fun s _ => by
      have h := hx s
      rw [imcField_eq_model L R α iref hL.ne', (imcModel L R α).inputField_eq he] at h
      exact h.hasDerivWithinAt
  have h := hbound 0 t x htraj t ⟨ht, le_rfl⟩
  rw [sub_zero, neg_mul] at h
  refine ⟨h, le_trans ?_ h⟩
  have hc : |x t 0 - iref| = ‖(x t - e) 0‖ := by
    simp [e, imcEquilibrium, Real.norm_eq_abs]
  rw [hc]
  exact PiLp.norm_apply_le _ 0

/-- Every closed-loop current converges to the reference.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem imcLoop_current_tendsto (L R α iref : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hα : 0 < α) {x : ℝ → ℝ²} (hx : ∀ t, HasDerivAt x (imcField L R α iref (x t)) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 iref) := by
  obtain ⟨K, hK, rate, hrate, hbound⟩ := imcLoop_exponentiallyStable_tracking L R α iref hL hR hα
  set c := ‖x 0 - imcEquilibrium α iref‖
  have hexp : Tendsto (fun t : ℝ => K * Real.exp (-(rate * t)) * c) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hrate)
    simpa using (h1.const_mul K).mul_const c
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hexp
  filter_upwards [eventually_ge_atTop 0] with t ht
  simpa [Real.norm_eq_abs] using (hbound x hx t ht).2

/-! ## Ideal decoupling of the dq current loop -/

/-- With exact cross-coupling and back-EMF feedforward
(`v = −ω σL i_q − ê + u`, `ê = e`), the d-axis of FOC note §1.5,
`σL_s di_d/dt = v_d − r' i_d + ω σL_s i_q + e_d`, reduces to the RL plant driven by the PI
output `u`. -/
@[powerlib_foundation] theorem decoupled_axis_eq_rl (σL r' ω id iq ed u : ℝ) :
    ((-ω * σL * iq - ed + u) - r' * id + ω * σL * iq + ed) / σL = rlField σL r' id u := by
  unfold rlField
  congr 1
  ring

/-! ## Speed loop -/

/-- Speed PI around an ideal current loop: `J ω̇ = K_t (K_p (ω* − ω) + K_i ξ)`,
`ξ̇ = ω* − ω`; state `(ω, ξ)`, input `ω*`, output `ω`. -/
def speedLoopModel (J Kt Kp Ki : ℝ) : Plant 2 1 :=
  siso2 (-(Kt * Kp / J)) (Kt * Ki / J) (-1) 0 (Kt * Kp / J) 1 1 0

@[powerlib_foundation] theorem speedLoop_transfer (J Kt Kp Ki : ℝ) (hJ : J ≠ 0) (s : ℂ)
    (hden : (J : ℂ) * s ^ 2 + Kt * Kp * s + Kt * Ki ≠ 0) :
    transfer (speedLoopModel J Kt Kp Ki) s 0 0 =
      Kt * (Kp * s + Ki) / (J * s ^ 2 + Kt * Kp * s + Kt * Ki) := by
  have hJ' : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have hdet : ((s - ((-(Kt * Kp / J) : ℝ) : ℂ)) * (s - ((0 : ℝ) : ℂ)) -
      ((Kt * Ki / J : ℝ) : ℂ) * ((-1 : ℝ) : ℂ)) =
      (J * s ^ 2 + Kt * Kp * s + Kt * Ki) / J := by
    push_cast
    field_simp
    ring
  unfold speedLoopModel
  rw [siso2_transfer _ _ _ _ _ _ _ _ s (by rw [hdet]; exact div_ne_zero hden hJ'), hdet]
  push_cast
  field_simp
  ring

/-- Pole placement of the speed loop: with `K_p = 2ζω_n J/K_t`, `K_i = ω_n² J/K_t` the
denominator is `J (s² + 2ζω_n s + ω_n²)`. -/
@[powerlib_foundation] theorem speedLoop_denominator_tuned (J Kt ζ ωn : ℝ) (hKt : Kt ≠ 0) (s : ℂ) :
    (J : ℂ) * s ^ 2 + Kt * ((2 * ζ * ωn * J / Kt : ℝ) : ℂ) * s + Kt * ((ωn ^ 2 * J / Kt : ℝ) : ℂ) =
      J * (s ^ 2 + 2 * ζ * ωn * s + ωn ^ 2) := by
  have : (Kt : ℂ) ≠ 0 := by exact_mod_cast hKt
  push_cast
  field_simp

/-! ## Complex-vector form of the stator current equation -/

/-- `σL_s di/dt = v − r' i − jω_e σL_s i + e` (complex) is equivalent to the real pair
`σL_s di_d/dt = v_d − r' i_d + ω_e σL_s i_q + e_d`,
`σL_s di_q/dt = v_q − r' i_q − ω_e σL_s i_d + e_q` (FOC note §1.5). -/
@[powerlib_foundation] theorem complexVector_iff (σL r' ωe : ℝ) (i di v e : ℂ) :
    (σL : ℂ) * di = v - r' * i - Complex.I * ωe * σL * i + e ↔
      σL * di.re = v.re - r' * i.re + ωe * σL * i.im + e.re ∧
      σL * di.im = v.im - r' * i.im - ωe * σL * i.re + e.im := by
  rw [Complex.ext_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

end powerlib.Drives.CascadeControl
