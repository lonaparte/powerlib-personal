import theorem.GridTiedConverter.GFM.DCLink.OpenLoop
import theorem.Criteria.Routh4
import theorem.SpecialFunctions.Sinusoid

/-! # Grid-forming VSM with a DC link and a DC-voltage PI loop (four states)

Model boundary.
* State `x = (δ, ω, V, ζ) : Dynamics.State 4`, in this order: power angle of the internal EMF
  relative to the stiff grid (rad), angular-frequency deviation (rad/s), DC-link voltage, and the
  integral of the DC-voltage error `ζ = ∫ (V − V*) dt`.
* The plant of `theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean` (`Plant`: quasi-static line
  `P_e(δ) = c₀ + A sin(δ − α)`, constant EMF magnitude, affine DC source
  `P_src(V) = P_s + I_s V`, DC node `Plant.nodeRate`) with a DC-voltage PI loop acting on the
  VSM power reference (`Params.field`):
  `δ̇ = ω`, `M ω̇ = P_ref − P_e(δ) − D ω`, `P_ref = P_ff + K_p (V − V*) + K_i ζ`,
  `C V̇ = (P_src(V) − P_e(δ))/V`, `ζ̇ = V − V*`. Positive `K_p, K_i` raise the exported power
  when the DC link is overcharged.
* Continuous time, autonomous, no input; active power export-positive, source power positive
  into the DC node. Parameters are arbitrary reals. The field contains `1/V` and is used on the
  open set `V ≠ 0`, which contains every equilibrium when `V* ≠ 0`; selected points on the
  singular plane `V = 0` (`V* = 0`) are treated in
  `theorem/GridTiedConverter/GFM/DCLink/VSMDCPlane.lean`.
* Excluded, as for the open loop: reactive-power and amplitude loops, inner voltage and current
  loops, line dynamics, limits, PLL, delay, PWM, DC-link losses.
* Level: equilibria and local exponential stability or instability of an equilibrium, from the
  Jacobian computed by `fderiv` and the quartic Routh–Hurwitz criterion; Lyapunov and local
  asymptotic stability in `theorem/GridTiedConverter/GFM/DCLink/VSMDCBoundary.lean`.

Source: GFM counterpart study, note T7 (`t7-dcside`, part (a): characteristic polynomial,
DC-PI threshold, the bounds `b < D/M`, `b < k/D`, the upper gain window and the existence of
stabilizing gains; derivations and numerical checks are notes outside the repository). GFL
counterparts: `theorem/GridTiedConverter/GFL/DCLink/VoltageControl.lean` (DC-PI loop) and
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean` (four-state Routh). Quartic
Routh–Hurwitz: `Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic`
(`theorem/Criteria/Routh4.lean`).

Results.
* `Params.field_eq_zero_iff`: the equilibria are `ω = 0`, `V = V*`, `P_ff + K_i ζ = P_e(δ)`
  and `P_src(V*) = P_e(δ)` (`M, C, V* ≠ 0`); `Params.exists_equilibrium_iff`: an equilibrium
  exists iff `|P_src(V*) − c₀| ≤ |A|` (`K_i ≠ 0`, `SpecialFunctions.exists_sinusoid_zero_iff_abs`).
* `VSMDC.Model.point_mem`, `VSMDC.Model.fderiv_point`, `VSMDC.Model.field_point_of_balanced`:
  with `V* ≠ 0` the selected point lies off the singular plane, the Jacobian there is
  `Params.jacobian`, and a balanced point is an equilibrium.
* `Params.hasFDerivAt_field`: on `V ≠ 0` the Jacobian is `Params.jacobian`
  `[[0, 1, 0, 0], [−k/M, −D/M, K_p/M, K_i/M], [−k/(C V), 0, j, 0], [0, 0, 1, 0]]`,
  `k = A cos(δ − α)`, `j = Plant.nodeSlope`.
* `Model.det_characteristicMatrix`: at an equilibrium `(δ*, 0, V*, ζ*)` with `V* ≠ 0`,
  `det(sI − J) = s (s − b)(s² + (D/M) s + k/M) + k (K_p s + K_i)/(M C V*)` with
  `b = I_s/(C V*) = P_src'(V*)/(C V*)` (`Model.b`). Expanded
  (`Model.det_characteristicMatrix_quartic`): `s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀`, `a₃ = D/M − b`,
  `a₂ = k/M − b D/M`, `a₁ = (k/M)(K_p/(C V*) − b)`, `a₀ = k K_i/(M C V*)`. Without a DC loop
  (`K_p = K_i = 0`) it is `s (s − b)(s² + (D/M) s + k/M)`: the open-loop block structure with the
  neutral integrator root `s = 0`.
* Coefficient signs (static): `Model.a1_pos_iff` (`a₁ > 0 ⇔ K_p > I_s = P_src'(V*)`, for
  `k/M > 0`, `C V* > 0`: the power threshold of the GFL DC-PI loop), `Model.a2_pos_iff`
  (`a₂ > 0 ⇔ b < k/D`, `M, D > 0`), `Model.a1_lt_iff` (`a₁ < a₃ a₂ ⇔ K_p < K_p,max`,
  `K_p,max = C V* D (k − b D + M b²)/(M k)`, `Model.KpMax`); `a₃ > 0 ⇔ b < D/M` by definition.

Family and connection conclusions.
* `VSMDC.family := Spectral.localFamily Model.field Model.Stable Model.Unstable` reads a model
  (`VSMDC.Model`: parameters with a selected angle `δ*` and integrator value `ζ*`) as the field
  translated so that `(δ*, 0, V*, ζ*)` is the origin. `Model.Stable`: `V* ≠ 0`, balance
  (`P_ff + K_i ζ* = P_e(δ*) = P_src(V*)`) and the quartic Routh conditions
  `a₃, a₁, a₀ > 0`, `a₁² + a₃² a₀ < a₃ a₂ a₁`; `Model.Unstable`: `V* ≠ 0`, balance and a strict
  violation. Soundness `VSMDC.chain_le_semantics`.
* `VSMDC.mem_den_locallyExponentiallyStable_iff` (`V* ≠ 0`): locally exponentially stable iff
  balanced with the quartic Routh conditions (converse linearization for the field `C¹` on
  `V ≠ 0`); within `V* ≠ 0` the local exponential translation is exact
  (`VSMDC.realize_eq_den_inter`).
* Instability: `VSMDC.mem_den_unstable_of_Kp_lt` (`K_p < P_src'(V*)`, for `k/M > 0`, `C V* > 0`;
  with `K_p = 0` a constant-current source exporting power is unstable without a DC loop),
  `VSMDC.mem_den_unstable_of_damping_lt` (`D/M < b`, whatever the DC gains),
  `VSMDC.mem_den_unstable_of_sync_lt` (`k/D < b`: a large damping `D` destroys export-mode DC
  stability), `VSMDC.mem_den_unstable_of_Kp_gt` (`K_p > K_p,max`). Boundaries included:
  `VSMDC.not_mem_den_locallyExponentiallyStable` (`K_p ≤ I_s`, `D/M ≤ b`, `k/D ≤ b` or
  `K_p,max ≤ K_p` excludes local exponential stability).
* `VSMDC.exists_gains_mem_den_locallyExponentiallyStable_iff`: for `M, D, C, V* > 0` at a
  balanced angle with `k > 0`, DC-loop gains `K_p, K_i` (with the matching integrator value)
  making the equilibrium locally exponentially stable exist iff `b < D/M` and `b < k/D`.
* Static evidence on the model: the equilibrium, Jacobian, characteristic-polynomial and
  coefficient identities above.
* Lyapunov and local asymptotic stability (`V* ≠ 0`) are in
  `theorem/GridTiedConverter/GFM/DCLink/VSMDCBoundary.lean`: the closed Routh conditions are
  necessary (`VSMDC.closedRouth_of_mem_den_lyapunovStable`), both sentences are exact off the
  Routh boundary (`VSMDC.mem_den_lyapunovStable_iff_of_offBoundary`,
  `VSMDC.mem_den_locallyAsymptoticallyStable_iff_of_offBoundary`), and on it a Lyapunov stable
  and an unstable witness (`VSMDC.flatOpen`, `VSMDC.flatIntegral`) make the Lyapunov and the
  instability sentences inexpressible in the requirement language; two Hopf points of the
  boundary (`theorem/GridTiedConverter/GFM/DCLink/VSMDCHopf.lean`, `VSMDC.hopfSup`,
  `VSMDC.hopfSub`) do the same for local asymptotic stability. The singular plane `V* = 0`
  is decided for local exponential and asymptotic stability in
  `theorem/GridTiedConverter/GFM/DCLink/VSMDCPlane.lean`
  (`VSMDC.mem_den_locallyExponentiallyStable_iff_of_V_eq_zero`), and for Lyapunov stability
  except at the balance `P_s = P_e(δ*)` of an invariant plane with DC gains
  (`VSMDC.mem_den_lyapunovStable_iff_of_invariant`).
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter
open powerlib.Dynamics (State)

/-- Parameters of the VSM–DC converter with a DC-voltage PI loop on the power reference. -/
structure Params extends Plant where
  /-- DC-voltage reference `V*`. -/
  Vref : ℝ
  /-- Proportional gain `K_p` of the DC-voltage loop. -/
  Kp : ℝ
  /-- Integral gain `K_i` of the DC-voltage loop. -/
  Ki : ℝ

namespace Params

variable (p : Params)

/-- Power reference `P_ref = P_ff + K_p (V − V*) + K_i ζ`. -/
def Pref (V ζ : ℝ) : ℝ := p.Pff + p.Kp * (V - p.Vref) + p.Ki * ζ

/-- The closed-loop field on `(δ, ω, V, ζ)`. -/
def field (x : State 4) : State 4 :=
  WithLp.toLp 2 ![x 1, p.swingRate (p.Pref (x 2) (x 3)) (x 0) (x 1), p.nodeRate (x 0) (x 2),
    x 2 - p.Vref]

/-- The Jacobian of the closed loop at a state (valid where `V = x 2 ≠ 0`). -/
def jacobian (x : State 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
    -p.k (x 0) / p.M, -p.D / p.M, p.Kp / p.M, p.Ki / p.M;
    -p.k (x 0) / (p.C * x 2), 0, p.nodeSlope (x 0) (x 2), 0;
    0, 0, 1, 0]

@[tmio M, simp, powerlib_domain] theorem field_apply_zero (x : State 4) : p.field x 0 = x 1 := by
  simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_one (x : State 4) :
    p.field x 1 = p.swingRate (p.Pref (x 2) (x 3)) (x 0) (x 1) := by
  simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_two (x : State 4) :
    p.field x 2 = p.nodeRate (x 0) (x 2) := by
  simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_three (x : State 4) :
    p.field x 3 = x 2 - p.Vref := by
  simp [field]

/-- The Jacobian of the closed loop, computed from the field: `D field (x) = jacobian x`
wherever `V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field {x : State 4} (hx : x 2 ≠ 0) :
    HasFDerivAt p.field (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (p.jacobian x)) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h1 := Dynamics.hasFDerivAt_coord (1 : Fin 4) x
  have h2 := Dynamics.hasFDerivAt_coord (2 : Fin 4) x
  have h3 := Dynamics.hasFDerivAt_coord (3 : Fin 4) x
  fin_cases i
  · refine (h1.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · ext v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
    · simp
  · have h := ((((((h2.sub_const p.Vref).const_mul p.Kp).const_add p.Pff).add
      (h3.const_mul p.Ki)).sub (p.hasFDerivAt_Pe_comp 0 x)).sub (h1.const_mul p.D)).mul_const
      p.M⁻¹
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · ext v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
      ring
    · simp [Plant.swingRate, Pref, div_eq_mul_inv]
  · have h := p.hasFDerivAt_nodeRate_comp (0 : Fin 4) (2 : Fin 4) hx
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · ext v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
    · simp
  · refine ((h2.sub_const p.Vref).congr_fderiv ?_).congr_of_eventuallyEq
      (Eventually.of_forall fun y => ?_)
    · ext v
      simp [jacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
    · simp

@[tmio M, powerlib_domain] theorem fderiv_field {x : State 4} (hx : x 2 ≠ 0) :
    fderiv ℝ p.field x = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (p.jacobian x) :=
  (p.hasFDerivAt_field hx).fderiv

/-- The closed loop is `C¹` on `V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem field_contDiffOn : ContDiffOn ℝ 1 p.field (nonzeroDC 2) := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  · simpa using (Dynamics.contDiff_coord (n := 4) (k := 1) 1).contDiffOn
  · simp only [Fin.mk_one, field_apply_one]
    apply ContDiff.contDiffOn
    unfold Plant.swingRate Pref Plant.Pe
    fun_prop
  · simp only [Fin.reduceFinMk, field_apply_two]
    have hP : ContDiff ℝ 1 (fun y : State 4 => p.Ps - p.Pe (y 0)) := by
      unfold Plant.Pe
      fun_prop
    exact GFL.DCLink.contDiffOn_nodeRate p.C contDiffOn_const hP.contDiffOn
      (Dynamics.contDiff_coord (n := 4) (k := 1) 2).contDiffOn fun y hy => hy
  · simp only [Fin.reduceFinMk, field_apply_three]
    apply ContDiff.contDiffOn
    fun_prop

/-- Equilibria of the closed loop: `ω = 0`, `V = V*`, `P_ff + K_i ζ = P_e(δ)` and
`P_src(V*) = P_e(δ)` (`M, C, V* ≠ 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hM : p.M ≠ 0) (hC : p.C ≠ 0)
    (hV : p.Vref ≠ 0) (x : State 4) :
    p.field x = 0 ↔ x 1 = 0 ∧ x 2 = p.Vref ∧ p.Pff + p.Ki * x 3 = p.Pe (x 0) ∧
      p.Psrc p.Vref = p.Pe (x 0) := by
  constructor
  · intro h
    have e0 := congrArg (fun y : State 4 => y 0) h
    have e1 := congrArg (fun y : State 4 => y 1) h
    have e2 := congrArg (fun y : State 4 => y 2) h
    have e3 := congrArg (fun y : State 4 => y 3) h
    simp only [field_apply_zero, field_apply_one, field_apply_two, field_apply_three,
      PiLp.zero_apply] at e0 e1 e2 e3
    have hx2 : x 2 = p.Vref := by linarith
    rw [hx2] at e1 e2
    rw [Plant.swingRate, Pref, e0, div_eq_zero_iff, or_iff_left hM] at e1
    refine ⟨e0, hx2, by linarith, (p.nodeRate_eq_zero_iff hC hV).mp e2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    ext i
    fin_cases i
    · simp [h1]
    · simp [Plant.swingRate, Pref, h1, h2, h3]
    · simp [h2, p.nodeRate_of_balance hV h4]
    · simp [h2]

/-- Equilibria exist iff `|P_src(V*) − c₀| ≤ |A|` (`M, C, V*, K_i ≠ 0`): the angle solves
`P_e(δ) = P_src(V*)` (`SpecialFunctions.exists_sinusoid_zero_iff_abs`) and the integrator absorbs
the power reference. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_equilibrium_iff (hM : p.M ≠ 0) (hC : p.C ≠ 0)
    (hV : p.Vref ≠ 0) (hKi : p.Ki ≠ 0) :
    (∃ x, p.field x = 0) ↔ |p.Psrc p.Vref - p.c0| ≤ |p.A| := by
  rw [← SpecialFunctions.exists_sinusoid_zero_iff_abs (φ := -p.α)]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨-, -, -, h4⟩ := (p.field_eq_zero_iff hM hC hV x).mp hx
    refine ⟨x 0, ?_⟩
    rw [h4, Plant.Pe, ← sub_eq_add_neg]
    ring
  · rintro ⟨δ, hδ⟩
    refine ⟨WithLp.toLp 2 ![δ, 0, p.Vref, (p.Pe δ - p.Pff) / p.Ki],
      (p.field_eq_zero_iff hM hC hV _).mpr ⟨by simp, by simp, ?_, ?_⟩⟩
    · simp only [Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val_zero,
        Matrix.head_cons]
      field_simp
      ring
    · simp only [Matrix.cons_val_zero, Plant.Pe]
      rw [← sub_eq_add_neg] at hδ
      linarith

end Params

namespace VSMDC

/-- A VSM–DC converter with its DC-voltage loop, read about a selected angle `δ*` and integrator
value `ζ*`: the operating point is `(δ*, 0, V*, ζ*)`. -/
structure Model where
  /-- The parameters. -/
  p : Params
  /-- The selected angle `δ*`. -/
  δ : ℝ
  /-- The selected integrator value `ζ*`. -/
  ζ : ℝ

/-- The selected point `(δ*, 0, V*, ζ*)`. -/
def Model.point (m : Model) : State 4 := WithLp.toLp 2 ![m.δ, 0, m.p.Vref, m.ζ]

/-- The closed-loop field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 4) : State 4 := m.p.field (z + m.point)

/-- The synchronizing coefficient `k = A cos(δ* − α)` at the selected angle. -/
def Model.k (m : Model) : ℝ := m.p.k m.δ

/-- The DC-node pole `b = I_s/(C V*) = P_src'(V*)/(C V*)`. -/
def Model.b (m : Model) : ℝ := m.p.Is / (m.p.C * m.p.Vref)

/-- Characteristic coefficient `a₃ = D/M − b`. -/
def Model.a3 (m : Model) : ℝ := m.p.D / m.p.M - m.b

/-- Characteristic coefficient `a₂ = k/M − b D/M`. -/
def Model.a2 (m : Model) : ℝ := m.k / m.p.M - m.b * (m.p.D / m.p.M)

/-- Characteristic coefficient `a₁ = (k/M)(K_p/(C V*) − b)`. -/
def Model.a1 (m : Model) : ℝ := m.k / m.p.M * (m.p.Kp / (m.p.C * m.p.Vref) - m.b)

/-- Characteristic coefficient `a₀ = k K_i/(M C V*)`. -/
def Model.a0 (m : Model) : ℝ := m.k * m.p.Ki / (m.p.M * m.p.C * m.p.Vref)

/-- The upper end of the proportional-gain window, `K_p,max = C V* D (k − b D + M b²)/(M k)`. -/
def Model.KpMax (m : Model) : ℝ :=
  m.p.C * m.p.Vref * m.p.D * (m.k - m.b * m.p.D + m.p.M * m.b ^ 2) / (m.p.M * m.k)

/-- Power balance at the selected point: `P_ff + K_i ζ* = P_e(δ*)` and `P_src(V*) = P_e(δ*)`. -/
def Model.Balanced (m : Model) : Prop :=
  m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ ∧ m.p.Psrc m.p.Vref = m.p.Pe m.δ

/-- Stability condition: `V* ≠ 0`, balance and the quartic Routh conditions. -/
def Model.Stable (m : Model) : Prop :=
  m.p.Vref ≠ 0 ∧ m.Balanced ∧ 0 < m.a3 ∧ 0 < m.a1 ∧ 0 < m.a0 ∧
    m.a1 ^ 2 + m.a3 ^ 2 * m.a0 < m.a3 * m.a2 * m.a1

/-- Instability condition: `V* ≠ 0`, balance and a strict violation of the quartic Routh
conditions. -/
def Model.Unstable (m : Model) : Prop :=
  m.p.Vref ≠ 0 ∧ m.Balanced ∧ (m.a3 < 0 ∨ m.a2 < 0 ∨ m.a1 < 0 ∨ m.a0 < 0 ∨
    m.a3 * m.a2 * m.a1 < m.a1 ^ 2 + m.a3 ^ 2 * m.a0)

/-- The VSM–DC family with the DC-voltage PI loop. -/
def family : Family Model Spectral.Requirement 4 0 :=
  Spectral.localFamily Model.field Model.Stable Model.Unstable

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)

/-- The selected point lies off the singular plane when `V* ≠ 0`. -/
@[tmio M, powerlib_domain] theorem Model.point_mem (m : Model) (hV : m.p.Vref ≠ 0) :
    m.point ∈ nonzeroDC (2 : Fin 4) := by
  simpa [Model.point, nonzeroDC] using hV

/-- The Jacobian at the selected point, from the field (`V* ≠ 0`). -/
@[tmio M, powerlib_domain] theorem Model.fderiv_point (m : Model) (hV : m.p.Vref ≠ 0) :
    fderiv ℝ m.p.field m.point =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (m.p.jacobian m.point) :=
  m.p.fderiv_field (by simpa [Model.point] using hV)

/-- A balanced selected point with `V* ≠ 0` is an equilibrium. -/
@[tmio M, powerlib_domain] theorem Model.field_point_of_balanced {m : Model}
    (hV : m.p.Vref ≠ 0) (hb : m.Balanced) : m.p.field m.point = 0 := by
  ext i
  fin_cases i
  · simp [Model.point]
  · simp [Model.point, Plant.swingRate, Params.Pref, hb.1]
  · simp [Model.point, m.p.nodeRate_of_balance hV hb.2]
  · simp [Model.point]

/-- At an equilibrium the DC-node slope is the pole `b`. -/
@[tmio M, powerlib_domain] private theorem nodeSlope_point {m : Model} (hV : m.p.Vref ≠ 0)
    (hx : m.p.field m.point = 0) : m.p.nodeSlope m.δ m.p.Vref = m.b := by
  by_cases hC : m.p.C = 0
  · simp [Plant.nodeSlope, Model.b, hC]
  · have h2 := congrArg (fun y : State 4 => y 2) hx
    simp only [Params.field_apply_two, PiLp.zero_apply] at h2
    simp only [Model.point, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at h2
    exact m.p.nodeSlope_of_balance hV ((m.p.nodeRate_eq_zero_iff hC hV).mp h2)

/-- **Characteristic polynomial**, derived from the field: at an equilibrium `(δ*, 0, V*, ζ*)`
with `V* ≠ 0`, `det(sI − J) = s (s − b)(s² + (D/M) s + k/M) + k (K_p s + K_i)/(M C V*)`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix (m : Model)
    (hV : m.p.Vref ≠ 0) (hx : m.p.field m.point = 0) (s : ℂ) :
    (Linear.characteristicMatrix (m.p.jacobian m.point) s).det =
      s * (s - (m.b : ℂ)) * (s ^ 2 + ((m.p.D / m.p.M : ℝ) : ℂ) * s + ((m.k / m.p.M : ℝ) : ℂ)) +
        ((m.k / (m.p.M * m.p.C * m.p.Vref) : ℝ) : ℂ) * ((m.p.Kp : ℂ) * s + (m.p.Ki : ℂ)) := by
  have hj := nodeSlope_point hV hx
  rw [Criteria.det_characteristicMatrix_fin_four]
  simp only [Matrix.trace, Fin.sum_univ_four, Matrix.diag_apply, Criteria.principalMinorSum2Fin4,
    Criteria.principalMinorSum3Fin4, Criteria.det_fin_four]
  simp [Params.jacobian, Model.point, hj, Model.k]
  ring

/-- The characteristic polynomial expanded: `s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀`. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix_quartic (m : Model)
    (hV : m.p.Vref ≠ 0) (hx : m.p.field m.point = 0) (s : ℂ) :
    (Linear.characteristicMatrix (m.p.jacobian m.point) s).det =
      s ^ 4 + (m.a3 : ℂ) * s ^ 3 + (m.a2 : ℂ) * s ^ 2 + (m.a1 : ℂ) * s + (m.a0 : ℂ) := by
  rw [m.det_characteristicMatrix hV hx]
  simp only [Model.a3, Model.a2, Model.a1, Model.a0, Model.b]
  push_cast
  ring

/-- `a₁ > 0` iff the proportional gain exceeds the source slope, `K_p > I_s = P_src'(V*)`
(`k/M > 0`, `C V* > 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.a1_pos_iff (m : Model) (hk : 0 < m.k / m.p.M)
    (hCV : 0 < m.p.C * m.p.Vref) : 0 < m.a1 ↔ m.p.Is < m.p.Kp := by
  rw [Model.a1, Model.b, ← sub_div, mul_pos_iff_of_pos_left hk, div_pos_iff_of_pos_right hCV,
    sub_pos]

/-- `a₂ > 0` iff `b < k/D` (`M, D > 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.a2_pos_iff (m : Model) (hM : 0 < m.p.M)
    (hD : 0 < m.p.D) : 0 < m.a2 ↔ m.b < m.k / m.p.D := by
  rw [Model.a2, lt_div_iff₀ hD, show m.k / m.p.M - m.b * (m.p.D / m.p.M) =
    (m.k - m.b * m.p.D) / m.p.M by ring, div_pos_iff_of_pos_right hM, sub_pos]

/-- `a₁ < a₃ a₂` iff `K_p < K_p,max = C V* D (k − b D + M b²)/(M k)` (`M, k > 0`, `C V* > 0`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] private theorem Model.a3_mul_a2_sub_a1 (m : Model) (hM : m.p.M ≠ 0)
    (hk : m.k ≠ 0) (hCV : m.p.C * m.p.Vref ≠ 0) :
    m.a3 * m.a2 - m.a1 = m.k / (m.p.M * (m.p.C * m.p.Vref)) * (m.KpMax - m.p.Kp) := by
  have hC : m.p.C ≠ 0 := left_ne_zero_of_mul hCV
  have hV : m.p.Vref ≠ 0 := right_ne_zero_of_mul hCV
  simp only [Model.a3, Model.a2, Model.a1, Model.KpMax]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem Model.a1_lt_iff (m : Model) (hM : 0 < m.p.M) (hk : 0 < m.k)
    (hCV : 0 < m.p.C * m.p.Vref) : m.a1 < m.a3 * m.a2 ↔ m.p.Kp < m.KpMax := by
  rw [← sub_pos, m.a3_mul_a2_sub_a1 hM.ne' hk.ne' hCV.ne',
    mul_pos_iff_of_pos_left (by positivity), sub_pos]

/-- **Local exponential stability.** At a balanced point with `V* ≠ 0` whose characteristic
coefficients satisfy the quartic Routh conditions, the VSM–DC converter with its DC-voltage loop
is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (h : m.Stable) : connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨hV, hb, h3, h1, h0, hg⟩ := h
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hx := Model.field_point_of_balanced hV hb
  exact Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_nonzeroDC 2)
    (m.point_mem hV) _ m.p.field_contDiffOn hx (m.fderiv_point hV)
    ((Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
      (m.det_characteristicMatrix_quartic hV hx)).2 ⟨h3, h1, h0, hg⟩)

/-- **Instability.** At a balanced point with `V* ≠ 0`, a strict violation of the quartic Routh
conditions (a negative coefficient or `a₃ a₂ a₁ < a₁² + a₃² a₀`) places a characteristic root in
the open right half plane: the converter is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (h : m.Unstable) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨hV, hb, hu⟩ := h
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hx := Model.field_point_of_balanced hV hb
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_nonzeroDC 2)
    (m.point_mem hV) _ m.p.field_contDiffOn hx (m.fderiv_point hV)
    (Criteria.exists_eigenvalue_re_pos_of_det_characteristicMatrix_quartic_violation _
      (m.det_characteristicMatrix_quartic hV hx) hu)

/-- Soundness of every translation of the VSM–DC family. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m h => ?_) (fun m h => ?_)
  · exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (mem_den_flow_iff.mp (mem_den_locallyExponentiallyStable m h))
  · exact (Flow.Property.holds_shift_iff .unstable).mpr
      (mem_den_flow_iff.mp (mem_den_unstable m h))

/-- **Exact local exponential stability.** With `V* ≠ 0`, the selected point is locally
exponentially stable iff it is balanced and the quartic Routh conditions hold (converse
linearization for the field `C¹` on `V ≠ 0`,
`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hV : m.p.Vref ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ ∧ m.p.Psrc m.p.Vref = m.p.Pe m.δ ∧ 0 < m.a3 ∧
        0 < m.a1 ∧ 0 < m.a0 ∧ m.a1 ^ 2 + m.a3 ^ 2 * m.a0 < m.a3 * m.a2 * m.a1) := by
  unfold TMIO.Statement
  constructor
  · intro h
    rw [mem_den_flow_iff] at h
    change LocallyExponentiallyStable _ _ at h
    rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local (isOpen_nonzeroDC 2)
      (m.point_mem hV) _ m.p.field_contDiffOn (m.fderiv_point hV)] at h
    obtain ⟨hx, hH⟩ := h
    obtain ⟨h3, h1, h0, hg⟩ := (Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
      (m.det_characteristicMatrix_quartic hV hx)).1 hH
    have hM : m.p.M ≠ 0 := fun h => by simp [Model.a0, h] at h0
    have hC : m.p.C ≠ 0 := fun h => by simp [Model.a0, h] at h0
    obtain ⟨-, -, e1, e2⟩ := (m.p.field_eq_zero_iff hM hC hV m.point).mp hx
    simp only [Model.point, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons] at e1 e2
    exact ⟨e1, e2, h3, h1, h0, hg⟩
  · rintro ⟨e1, e2, h3, h1, h0, hg⟩
    exact mem_den_locallyExponentiallyStable m ⟨hV, ⟨e1, e2⟩, h3, h1, h0, hg⟩

/-- Within `V* ≠ 0` the local exponential translation is exact: the generated space of the
stability condition is the locally exponentially stable models with `V* ≠ 0`. -/
@[tmio TM, powerlib_domain] theorem realize_eq_den_inter :
    connection% (TMIO.realize family.meets (family.translate (.flow .locallyExponentiallyStable)) =
      family.den (.flow .locallyExponentiallyStable) ∩ {m : Model | m.p.Vref ≠ 0}) :=
  Spectral.local_realize_eq_den_inter_of_iff (Or.inr (Or.inr rfl)) (fun m h => h.1)
    fun m hV => by
      have h := mem_den_locallyExponentiallyStable_iff m hV
      unfold TMIO.Statement at h
      show m.Stable ↔ m ∈ family.den (.flow .locallyExponentiallyStable)
      rw [h]
      exact ⟨fun ⟨_, hb, h3, h1, h0, hg⟩ => ⟨hb.1, hb.2, h3, h1, h0, hg⟩,
        fun ⟨e1, e2, h3, h1, h0, hg⟩ => ⟨hV, ⟨e1, e2⟩, h3, h1, h0, hg⟩⟩

/-- **The DC-PI threshold.** At a balanced point (`V* ≠ 0`, `k/M > 0`, `C V* > 0`), a
proportional gain below the source slope, `K_p < I_s = P_src'(V*)`, gives `a₁ < 0`: unstable.
With `K_p = 0` (no DC loop) a constant-current source exporting power (`I_s = P₀/V* > 0`) is
unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_Kp_lt (m : Model) (hV : m.p.Vref ≠ 0)
    (hb : m.Balanced) (hk : 0 < m.k / m.p.M) (hCV : 0 < m.p.C * m.p.Vref)
    (h : m.p.Kp < m.p.Is) : connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m ⟨hV, hb, Or.inr (Or.inr (Or.inl ?_))⟩
  have h1 : ¬ 0 < m.a1 := by rw [m.a1_pos_iff hk hCV]; exact not_lt.mpr h.le
  have h1' : m.a1 ≠ 0 := by
    rw [Model.a1, Model.b, ← sub_div]
    exact mul_ne_zero hk.ne' (div_ne_zero (sub_ne_zero.mpr h.ne) hCV.ne')
  exact lt_of_le_of_ne (not_lt.mp h1) h1'

/-- **Damping bound.** At a balanced point with `V* ≠ 0`, a DC node pole faster than the swing
damping, `D/M < b`, gives `a₃ < 0`: unstable for every DC-loop gain. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_damping_lt (m : Model)
    (hV : m.p.Vref ≠ 0) (hb : m.Balanced) (h : m.p.D / m.p.M < m.b) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  mem_den_unstable m ⟨hV, hb, Or.inl (sub_neg.mpr h)⟩

/-- **Synchronization bound.** At a balanced point (`V* ≠ 0`, `M, D > 0`), `k/D < b` gives
`a₂ < 0`: unstable for every DC-loop gain. The swing loop is a lag of bandwidth about `k/D` in the
DC actuator: a large damping destroys export-mode DC stability. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_sync_lt (m : Model) (hV : m.p.Vref ≠ 0)
    (hb : m.Balanced) (hM : 0 < m.p.M) (hD : 0 < m.p.D) (h : m.k / m.p.D < m.b) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m ⟨hV, hb, Or.inr (Or.inl ?_)⟩
  have e : m.a2 = (m.k - m.b * m.p.D) / m.p.M := by simp only [Model.a2]; ring
  rw [e]
  refine div_neg_of_neg_of_pos ?_ hM
  rw [div_lt_iff₀ hD] at h
  linarith

/-- **Upper gain window.** At a balanced point (`V* ≠ 0`, `M, k > 0`, `C V* > 0`), a proportional
gain above `K_p,max = C V* D (k − b D + M b²)/(M k)` gives `a₃ a₂ < a₁`, a strict violation of
the quartic Routh conditions: unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_Kp_gt (m : Model) (hV : m.p.Vref ≠ 0)
    (hb : m.Balanced) (hM : 0 < m.p.M) (hk : 0 < m.k) (hCV : 0 < m.p.C * m.p.Vref)
    (h : m.KpMax < m.p.Kp) : connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m ⟨hV, hb, ?_⟩
  have hlt : m.a3 * m.a2 < m.a1 := by
    have e := m.a3_mul_a2_sub_a1 hM.ne' hk.ne' hCV.ne'
    have : m.k / (m.p.M * (m.p.C * m.p.Vref)) * (m.KpMax - m.p.Kp) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr h)
    linarith
  by_contra hn
  push Not at hn
  obtain ⟨h3, h2, h1, h0, hg⟩ := hn
  have ha1 : 0 < m.a1 := lt_of_le_of_lt (mul_nonneg h3 h2) hlt
  nlinarith [mul_lt_mul_of_pos_right hlt ha1, mul_nonneg (sq_nonneg m.a3) h0]

/-- **Necessary conditions, boundaries included.** At any selected point with `V* ≠ 0`,
`M, D, k > 0` and `C V* > 0`, local exponential stability fails if `K_p ≤ I_s`, `D/M ≤ b`,
`k/D ≤ b` or `K_p,max ≤ K_p`: the quartic Routh conditions force `a₁ > 0`, `a₃ > 0`, `a₂ > 0`
(`Criteria.quartic_routh_a2_pos`) and `a₁ < a₃ a₂` (`Criteria.quartic_routh_a1_lt`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable (m : Model)
    (hV : m.p.Vref ≠ 0) (hM : 0 < m.p.M) (hD : 0 < m.p.D) (hk : 0 < m.k)
    (hCV : 0 < m.p.C * m.p.Vref)
    (h : m.p.Kp ≤ m.p.Is ∨ m.p.D / m.p.M ≤ m.b ∨ m.k / m.p.D ≤ m.b ∨ m.KpMax ≤ m.p.Kp) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have hiff := mem_den_locallyExponentiallyStable_iff m hV
  unfold TMIO.Statement at hiff ⊢
  rw [hiff]
  rintro ⟨-, -, h3, h1, h0, hg⟩
  have h2 := Criteria.quartic_routh_a2_pos h3 h1 h0 hg
  have h13 := Criteria.quartic_routh_a1_lt h3 h1 h0 hg
  rcases h with h | h | h | h
  · exact not_lt.mpr h ((m.a1_pos_iff (div_pos hk hM) hCV).mp h1)
  · exact not_lt.mpr h (sub_pos.mp h3)
  · exact not_lt.mpr h ((m.a2_pos_iff hM hD).mp h2)
  · exact not_lt.mpr h ((m.a1_lt_iff hM hk hCV).mp h13)

/-- The gain choice of the existence theorem: for `a₃, a₂, κ, c > 0` and any `b`, the gains
`K_p = c (b + a₃ a₂/(2κ))` and `K_i = c a₂²/(8κ)` give `a₁ = κ (K_p/c − b) = a₃ a₂/2` and
`a₀ = κ K_i/c = a₂²/8`, which meet the quartic Routh conditions. -/
@[tmio T, powerlib_foundation] private theorem routh_of_gains {a3 a2 κ c b : ℝ} (h3 : 0 < a3)
    (h2 : 0 < a2) (hκ : 0 < κ) (hc : 0 < c) :
    0 < κ * (c * (b + a3 * a2 / (2 * κ)) / c - b) ∧
      0 < κ * (c * a2 ^ 2 / (8 * κ)) / c ∧
      (κ * (c * (b + a3 * a2 / (2 * κ)) / c - b)) ^ 2 + a3 ^ 2 * (κ * (c * a2 ^ 2 / (8 * κ)) / c) <
        a3 * a2 * (κ * (c * (b + a3 * a2 / (2 * κ)) / c - b)) := by
  have e1 : κ * (c * (b + a3 * a2 / (2 * κ)) / c - b) = a3 * a2 / 2 := by
    field_simp
    ring
  have e0 : κ * (c * a2 ^ 2 / (8 * κ)) / c = a2 ^ 2 / 8 := by
    field_simp
  rw [e1, e0]
  refine ⟨by positivity, by positivity, ?_⟩
  have h32 : 0 < a3 * a2 := mul_pos h3 h2
  nlinarith [mul_pos h32 h32, sq_nonneg a3, sq_nonneg a2]

/-- **Existence of stabilizing DC-loop gains.** For a plant with `M, D, C > 0`, a reference
`V* > 0` and a balanced angle `δ*` (`P_src(V*) = P_e(δ*)`) with `k = A cos(δ* − α) > 0`, there
are gains `K_p, K_i` and an integrator value `ζ*` making `(δ*, 0, V*, ζ*)` locally exponentially
stable iff `b < D/M` and `b < k/D`. (`⇐`: `K_p` in the middle of the window `(I_s, K_p,max)`,
which is nonempty since `a₃ a₂ − a₁ = (D − b M)(k − b D)/M²` at `K_p = I_s`, and a small
`K_i > 0`.) -/
@[tmio TM, powerlib_domain] theorem exists_gains_mem_den_locallyExponentiallyStable_iff
    (q : Plant) (Vref δ : ℝ) (hM : 0 < q.M) (hD : 0 < q.D) (hC : 0 < q.C) (hV : 0 < Vref)
    (hk : 0 < q.k δ) (hbal : q.Psrc Vref = q.Pe δ) :
    connection% ((∃ Kp Ki ζ : ℝ,
        (⟨{ toPlant := q, Vref := Vref, Kp := Kp, Ki := Ki }, δ, ζ⟩ : Model) ∈
          family.den (.flow .locallyExponentiallyStable)) ↔
      q.Is / (q.C * Vref) < q.D / q.M ∧ q.Is / (q.C * Vref) < q.k δ / q.D) := by
  unfold TMIO.Statement
  constructor
  · rintro ⟨Kp, Ki, ζ, hm⟩
    have hiff := mem_den_locallyExponentiallyStable_iff
      ⟨{ toPlant := q, Vref := Vref, Kp := Kp, Ki := Ki }, δ, ζ⟩ hV.ne'
    unfold TMIO.Statement at hiff
    obtain ⟨-, -, h3, h1, h0, hg⟩ := hiff.mp hm
    exact ⟨sub_pos.mp h3, (Model.a2_pos_iff _ hM hD).mp (Criteria.quartic_routh_a2_pos h3 h1 h0 hg)⟩
  · rintro ⟨hb3, hb2⟩
    have hc0 : 0 < q.C * Vref := mul_pos hC hV
    have hκ0 : 0 < q.k δ / q.M := div_pos hk hM
    have hA3 : 0 < q.D / q.M - q.Is / (q.C * Vref) := sub_pos.mpr hb3
    have hA2 : 0 < q.k δ / q.M - q.Is / (q.C * Vref) * (q.D / q.M) := by
      have e : q.k δ / q.M - q.Is / (q.C * Vref) * (q.D / q.M) =
          (q.k δ - q.Is / (q.C * Vref) * q.D) / q.M := by ring
      rw [e]
      refine div_pos ?_ hM
      rw [lt_div_iff₀ hD] at hb2
      linarith
    obtain ⟨h1, h0, hg⟩ := routh_of_gains (b := q.Is / (q.C * Vref)) hA3 hA2 hκ0 hc0
    set Kp := q.C * Vref * (q.Is / (q.C * Vref) + (q.D / q.M - q.Is / (q.C * Vref)) *
      (q.k δ / q.M - q.Is / (q.C * Vref) * (q.D / q.M)) / (2 * (q.k δ / q.M)))
    set Ki := q.C * Vref * (q.k δ / q.M - q.Is / (q.C * Vref) * (q.D / q.M)) ^ 2 /
      (8 * (q.k δ / q.M))
    have hKi0 : Ki ≠ 0 :=
      div_ne_zero (mul_ne_zero hc0.ne' (pow_ne_zero 2 hA2.ne')) (by positivity)
    let m : Model := ⟨{ toPlant := q, Vref := Vref, Kp := Kp, Ki := Ki }, δ, (q.Pe δ - q.Pff) / Ki⟩
    have e0 : m.a0 = q.k δ / q.M * Ki / (q.C * Vref) := by
      change q.k δ * Ki / (q.M * q.C * Vref) = _
      ring
    have hiff := mem_den_locallyExponentiallyStable_iff m hV.ne'
    unfold TMIO.Statement at hiff
    refine ⟨Kp, Ki, (q.Pe δ - q.Pff) / Ki, hiff.mpr ⟨?_, hbal, hA3, h1, e0 ▸ h0, ?_⟩⟩
    · change q.Pff + Ki * ((q.Pe δ - q.Pff) / Ki) = q.Pe δ
      field_simp
      ring
    · rw [e0]
      exact hg

end VSMDC

end powerlib.GFM.DCLink
