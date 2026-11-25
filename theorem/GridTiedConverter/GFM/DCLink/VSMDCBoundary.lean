import theorem.GridTiedConverter.GFM.DCLink.VSMDC

/-! # The VSM–DC model with its DC-voltage loop: Lyapunov and local asymptotic stability

Model boundary.
The VSM–DC family `VSMDC.family` of `theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`: state
`x = (δ, ω, V, ζ)` (power angle, frequency deviation, DC-link voltage, integral of `V − V*`),
continuous time, autonomous; quasi-static line `P_e(δ) = c₀ + A sin(δ − α)`, constant EMF
magnitude, affine DC source `P_src(V) = P_s + I_s V`, DC-voltage PI loop on the VSM power
reference, `P_ref = P_ff + K_p (V − V*) + K_i ζ`; export-positive power; parameters arbitrary
reals; read at the selected point `(δ*, 0, V*, ζ*)` with `V* ≠ 0` (the field is `C¹` on `V ≠ 0`;
the singular plane is `theorem/GridTiedConverter/GFM/DCLink/VSMDCPlane.lean`). Excluded as in
`VSMDC.lean`: reactive-power and amplitude loops, inner loops, line dynamics, limits, PLL, delay,
PWM, DC-link losses. Level: local behaviour (Lyapunov stability, local asymptotic and exponential
stability, instability) at the selected point; not a basin estimate.

The quartic `s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` of `VSMDC.Model.det_characteristicMatrix_quartic`
decides local exponential stability exactly (`VSMDC.mem_den_locallyExponentiallyStable_iff`).
For the Lyapunov and the local asymptotic sentences the linearization decides everything off the
Routh boundary (`Model.Routh` or a strict violation `Model.RouthViolation`) and nothing on it.

Source: GFM counterpart study, note T7 part (a) (`t7-dcside`; notes outside the repository); the
GFL counterparts are `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Boundary.lean` (exactness off
the Routh boundary, boundary witnesses, inexpressibility) and
`theorem/GridTiedConverter/GFL/DCLink/FourStateBoundary.lean` (closed Routh conditions necessary).
Lyapunov's and Chetaev's theorems: Khalil, *Nonlinear Systems* (3rd ed.), Theorems 4.1 and 4.3
(`lyapunov_stable` of LeanForControl, `Dynamics.unstable_of_chetaev_local`). The conserved
quantities of the flat power curve were derived and their Lie derivatives checked with exact
computer algebra (SymPy, untrusted); Lean checks them.

Results.
* Degenerate parameters (`V* ≠ 0`): `VSMDC.mem_den_unstable_of_M_eq_zero` (no inertia: the
  frequency is frozen, Lean's `x / 0 = 0`, and drives the angle) and
  `VSMDC.mem_den_unstable_of_C_eq_zero` (no capacitance: `V` is frozen and drives the integrator
  `ζ`), both from `Dynamics.unstable_of_conserved_drive_local`.
* **Closed Routh conditions are necessary.** `VSMDC.closedRouth_of_mem_den_lyapunovStable`: a
  Lyapunov stable point (`V* ≠ 0`) is balanced with `a₃, a₂, a₁, a₀ ≥ 0` and
  `a₁² + a₃² a₀ ≤ a₃ a₂ a₁` (a strict violation is unstable, `VSMDC.mem_den_unstable`);
  `VSMDC.closedRouth_of_mem_den_locallyAsymptoticallyStable`: a locally asymptotically stable
  point in addition has `K_i ≠ 0` (`K_i = 0` leaves a line of equilibria in `ζ`,
  `VSMDC.not_mem_den_locallyAsymptoticallyStable_of_Ki_eq_zero`) and `A ≠ 0` (a flat power curve
  leaves a line of equilibria in `δ`,
  `VSMDC.not_mem_den_locallyAsymptoticallyStable_of_A_eq_zero`).
* **Exactness off the Routh boundary.** `VSMDC.mem_den_lyapunovStable_iff_of_offBoundary`,
  `VSMDC.mem_den_locallyAsymptoticallyStable_iff_of_offBoundary`: when the quartic meets the
  Routh conditions or violates them strictly, Lyapunov stability and local asymptotic stability
  each hold iff the point is balanced and Routh (iff local exponential stability).
* **The flat power curve** (`A = 0`, `k = 0`: `a₁ = a₀ = 0`, on the Routh boundary when
  `b < 0 < D/M`):
  - `VSMDC.mem_den_unstable_of_flat`: with an integral DC gain `K_i ≠ 0` (`M, C, I_s ≠ 0`) every
    balanced point is unstable. Off the plane `c = ζ − C V²/(2 I_s)` is conserved
    (`Params.flatQ_lie`) and `Φ = M ω + D δ − K_p C V²/(2 I_s) − K_i C² (V³/3 + V* V²/2)/(2 I_s²)`
    drifts at the constant rate `K_i (c − c*)` (`Params.flatPhi_lie`): Chetaev's function
    `K_i (c − c*)(Φ − Φ*)` grows at the rate `K_i² (c − c*)²` (the angle drifts at the frequency
    `K_i (ζ∞ − ζ*)/D` set by the integrator).
  - `VSMDC.mem_den_unstable_of_flat_constPower`: with a constant-power source (`I_s = 0`) `V` is
    frozen and drives `ζ`: unstable for every DC gain.
  - `VSMDC.mem_den_lyapunovStable_of_flat`: without DC gains (`K_p = K_i = 0`), `0 < D/M` and
    `b < 0`, every balanced point is Lyapunov stable: `(M ω + D (δ − δ*))² + ω² + (V − V*)² +
    (c − c*)²` decreases at the rate `2 (D/M) ω² − 2 I_s (V − V*)²/(C V) ≥ 0`
    (`Params.flatEnergy_lie`); it is not locally asymptotically stable (the line in `δ`).
* Two boundary witnesses with the characteristic polynomial `s² (s + 1)²` (`a₃ = 2`, `a₂ = 1`,
  `a₁ = a₀ = 0`): `flatOpen` (`K_p = K_i = 0`; Lyapunov stable,
  `flatOpen_mem_den_lyapunovStable`, not locally asymptotically stable,
  `flatOpen_not_mem_den_locallyAsymptoticallyStable`) and `flatIntegral` (`K_i = 1`; unstable,
  `flatIntegral_mem_den_unstable`). Both are balanced with `V* = 1` and meet neither
  requirement (`flatOpen_not_meets`, `flatIntegral_not_meets`).

Family and connection conclusions.
Connection conclusions on `VSMDC.family`: the memberships above, and
* REFUTED exactness within `V* ≠ 0`: `VSMDC.realize_ne_den_inter_lyapunovStable` (witness
  `flatOpen`: Lyapunov stable, not Routh);
* inexpressibility in the requirement language `{stable, unstable}`: for every requirement set
  `T`, `TMIO.realize family.meets T` differs from the Lyapunov
  (`VSMDC.realize_ne_den_lyapunovStable`) and the instability
  (`VSMDC.realize_ne_den_unstable`) denotations: `flatOpen` and
  `flatIntegral` meet the same requirements (none) and differ on both sentences
  (`Spectral.realize_ne_den_of_indistinguishable`).

Boundary Hopf points: `theorem/GridTiedConverter/GFM/DCLink/VSMDCHopf.lean` exhibits a
supercritical Hopf point of the Routh boundary (locally asymptotically stable, not Routh: REFUTED
exactness of the local asymptotic translation within `V* ≠ 0`,
`VSMDC.realize_ne_den_inter_locallyAsymptoticallyStable`) and a subcritical one (unstable:
inexpressibility, `VSMDC.realize_ne_den_locallyAsymptoticallyStable`), by the Hopf laws for
fields smooth near the point (`theorem/Dynamics/HopfLocal.lean`).
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter
open powerlib.Dynamics (State coord)

namespace VSMDC

/-- The quartic Routh conditions `a₃, a₁, a₀ > 0`, `a₁² + a₃² a₀ < a₃ a₂ a₁`. -/
def Model.Routh (m : Model) : Prop :=
  0 < m.a3 ∧ 0 < m.a1 ∧ 0 < m.a0 ∧ m.a1 ^ 2 + m.a3 ^ 2 * m.a0 < m.a3 * m.a2 * m.a1

/-- A strict violation: a negative coefficient or `a₃ a₂ a₁ < a₁² + a₃² a₀`. -/
def Model.RouthViolation (m : Model) : Prop :=
  m.a3 < 0 ∨ m.a2 < 0 ∨ m.a1 < 0 ∨ m.a0 < 0 ∨ m.a3 * m.a2 * m.a1 < m.a1 ^ 2 + m.a3 ^ 2 * m.a0

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)

@[tmio M, powerlib_domain] private theorem point_apply (m : Model) :
    m.point 0 = m.δ ∧ m.point 1 = 0 ∧ m.point 2 = m.p.Vref ∧ m.point 3 = m.ζ := by
  simp [Model.point]

/-! ## Degenerate parameters -/

/-- **No inertia.** With `M = 0` the frequency is frozen (Lean's `x / 0 = 0`) and drives the
angle: every selected point with `V* ≠ 0` is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_M_eq_zero (m : Model)
    (hV : m.p.Vref ≠ 0) (hM : m.p.M = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  refine Dynamics.unstable_of_conserved_drive_local (i := 1) (j := 0) (g := id)
    (isOpen_nonzeroDC 2) (m.point_mem hV) m.p.field_contDiffOn (by decide) contDiff_id
    (fun ε hε => ⟨ε / 2, ?_, (half_pos hε).ne'⟩) (fun x _ => ?_) (fun x _ => ?_)
  · rw [(point_apply m).2.1, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  · simp [Plant.swingRate, hM]
  · simp

/-- **No capacitance.** With `C = 0` the DC voltage is frozen (Lean's `x / 0 = 0`) and drives the
integrator: every selected point with `V* ≠ 0` is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_C_eq_zero (m : Model)
    (hV : m.p.Vref ≠ 0) (hC : m.p.C = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  refine Dynamics.unstable_of_conserved_drive_local (i := 2) (j := 3)
    (g := fun s => s - m.p.Vref) (isOpen_nonzeroDC 2) (m.point_mem hV) m.p.field_contDiffOn
    (by decide) (contDiff_id.sub contDiff_const)
    (fun ε hε => ⟨m.p.Vref + ε / 2, ?_, ?_⟩) (fun x _ => ?_) (fun x _ => ?_)
  · rw [(point_apply m).2.2.1, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  · simp only [add_sub_cancel_left]
    exact (half_pos hε).ne'
  · simp [Plant.nodeRate, GFL.DCLink.nodeRate, hC]
  · simp

/-! ## Closed Routh conditions -/

/-- **Necessity, boundaries included.** A Lyapunov stable selected point with `V* ≠ 0` is
balanced and its quartic lies in the closed Routh region `a₃, a₂, a₁, a₀ ≥ 0`,
`a₁² + a₃² a₀ ≤ a₃ a₂ a₁`: otherwise `M = 0`, `C = 0`, it is not an equilibrium, or it violates
the Routh conditions strictly, and each case is unstable. -/
@[tmio TM, powerlib_domain] theorem closedRouth_of_mem_den_lyapunovStable (m : Model)
    (hV : m.p.Vref ≠ 0) (h : m ∈ family.den (.flow .lyapunovStable)) :
    m.Balanced ∧ 0 ≤ m.a3 ∧ 0 ≤ m.a2 ∧ 0 ≤ m.a1 ∧ 0 ≤ m.a0 ∧
      m.a1 ^ 2 + m.a3 ^ 2 * m.a0 ≤ m.a3 * m.a2 * m.a1 := by
  have hnu : m ∉ family.den (.flow .unstable) := fun hu => by
    have hn := Spectral.not_mem_den_lyapunovStable_of_unstable hu
    unfold TMIO.Statement at hn
    exact hn h
  have hM : m.p.M ≠ 0 := fun hM => hnu (by
    have hu := mem_den_unstable_of_M_eq_zero m hV hM
    unfold TMIO.Statement at hu
    exact hu)
  have hC : m.p.C ≠ 0 := fun hC => hnu (by
    have hu := mem_den_unstable_of_C_eq_zero m hV hC
    unfold TMIO.Statement at hu
    exact hu)
  have heq := Dynamics.isEquilibrium_of_lyapunovStable_local (isOpen_nonzeroDC 2)
    (m.point_mem hV) m.p.field_contDiffOn (mem_den_flow_iff.mp h)
  obtain ⟨-, -, e1, e2⟩ := (m.p.field_eq_zero_iff hM hC hV m.point).mp heq
  obtain ⟨p0, -, -, p3⟩ := point_apply m
  rw [p0, p3] at e1
  rw [p0] at e2
  have hb : m.Balanced := ⟨e1, e2⟩
  have hv : ¬ m.RouthViolation := fun hv => hnu (by
    have hu := mem_den_unstable m ⟨hV, hb, hv⟩
    unfold TMIO.Statement at hu
    exact hu)
  unfold Model.RouthViolation at hv
  push Not at hv
  exact ⟨hb, hv⟩

/-- **No integral DC gain.** With `K_i = 0` the field does not read `ζ`: at a balanced point with
`V* ≠ 0` every `(δ*, 0, V*, ζ)` is an equilibrium, so it is not locally asymptotically stable. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_Ki_eq_zero
    (m : Model) (hV : m.p.Vref ≠ 0) (hb : m.Balanced) (hKi : m.p.Ki = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  change ¬ LocalAsymptoticStable _ _
  have heq := Model.field_point_of_balanced hV hb
  refine Dynamics.not_localAsymptoticStable_of_line (v := EuclideanSpace.single 3 1)
    (by simp) fun t _ => ?_
  rw [← heq]
  ext i
  fin_cases i <;> simp [Params.field, Params.Pref, hKi, Model.point]

/-- **A flat power curve.** With `A = 0` the field does not read `δ`: at a balanced point with
`V* ≠ 0` every `(δ, 0, V*, ζ*)` is an equilibrium, so it is not locally asymptotically stable. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_A_eq_zero
    (m : Model) (hV : m.p.Vref ≠ 0) (hb : m.Balanced) (hA : m.p.A = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  change ¬ LocalAsymptoticStable _ _
  have heq := Model.field_point_of_balanced hV hb
  refine Dynamics.not_localAsymptoticStable_of_line (v := EuclideanSpace.single 0 1)
    (by simp) fun t _ => ?_
  rw [← heq]
  ext i
  fin_cases i <;>
    simp [Params.field, Plant.swingRate, Plant.nodeRate, Plant.Pe, hA, Model.point]

/-- **Necessity for local asymptotic stability.** A locally asymptotically stable selected point
with `V* ≠ 0` is balanced, its quartic lies in the closed Routh region, and `K_i ≠ 0`,
`A ≠ 0`. -/
@[tmio TM, powerlib_domain] theorem closedRouth_of_mem_den_locallyAsymptoticallyStable
    (m : Model) (hV : m.p.Vref ≠ 0) (h : m ∈ family.den (.flow .locallyAsymptoticallyStable)) :
    m.Balanced ∧ 0 ≤ m.a3 ∧ 0 ≤ m.a2 ∧ 0 ≤ m.a1 ∧ 0 ≤ m.a0 ∧
      m.a1 ^ 2 + m.a3 ^ 2 * m.a0 ≤ m.a3 * m.a2 * m.a1 ∧ m.p.Ki ≠ 0 ∧ m.p.A ≠ 0 := by
  obtain ⟨hb, hc⟩ :=
    closedRouth_of_mem_den_lyapunovStable m hV (Spectral.den_las_subset_lyapunovStable h)
  refine ⟨hb, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, fun hKi => ?_, fun hA => ?_⟩
  · have hn := not_mem_den_locallyAsymptoticallyStable_of_Ki_eq_zero m hV hb hKi
    unfold TMIO.Statement at hn
    exact hn h
  · have hn := not_mem_den_locallyAsymptoticallyStable_of_A_eq_zero m hV hb hA
    unfold TMIO.Statement at hn
    exact hn h

/-! ## Exactness off the Routh boundary -/

/-- **Lyapunov stability off the Routh boundary.** With `V* ≠ 0`, when the quartic meets the
Routh conditions or violates them strictly, the selected point is Lyapunov stable iff it is
balanced and Routh (iff locally exponentially stable). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_offBoundary (m : Model)
    (hV : m.p.Vref ≠ 0) (hoff : m.Routh ∨ m.RouthViolation) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔ m.Balanced ∧ m.Routh) := by
  unfold TMIO.Statement
  constructor
  · intro h
    obtain ⟨hb, hc⟩ := closedRouth_of_mem_den_lyapunovStable m hV h
    refine ⟨hb, hoff.resolve_right fun hv => ?_⟩
    obtain ⟨h3, h2, h1, h0, hg⟩ := hc
    rcases hv with hv | hv | hv | hv | hv <;> linarith
  · rintro ⟨hb, hR⟩
    have hl := mem_den_locallyExponentiallyStable m ⟨hV, hb, hR⟩
    unfold TMIO.Statement at hl
    exact Spectral.den_locallyExponentiallyStable_subset_lyapunovStable hl

/-- **Local asymptotic stability off the Routh boundary.** With `V* ≠ 0`, when the quartic meets
the Routh conditions or violates them strictly, the selected point is locally asymptotically
stable iff it is balanced and Routh (iff locally exponentially stable). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_offBoundary
    (m : Model) (hV : m.p.Vref ≠ 0) (hoff : m.Routh ∨ m.RouthViolation) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m.Balanced ∧ m.Routh) := by
  have hls := mem_den_lyapunovStable_iff_of_offBoundary m hV hoff
  unfold TMIO.Statement at hls ⊢
  constructor
  · exact fun h => hls.mp (Spectral.den_las_subset_lyapunovStable h)
  · rintro ⟨hb, hR⟩
    have hl := mem_den_locallyExponentiallyStable m ⟨hV, hb, hR⟩
    unfold TMIO.Statement at hl
    exact Spectral.den_locallyExponentiallyStable_subset_las hl

/-! ## The flat power curve -/

end VSMDC

namespace Params

variable (p : Params)

/-- The quantity `c = ζ − C V²/(2 I_s)`, conserved on the flat curve. -/
def flatQ (y : State 4) : ℝ := y 3 - p.C / (2 * p.Is) * y 2 ^ 2

/-- Its drifting partner `Φ = M ω + D δ − K_p C V²/(2 I_s) − K_i C² (V³/3 + V* V²/2)/(2 I_s²)`. -/
def flatPhi (y : State 4) : ℝ :=
  p.M * y 1 + p.D * y 0 - p.Kp * p.C / (2 * p.Is) * y 2 ^ 2 -
    p.Ki * p.C ^ 2 / (2 * p.Is ^ 2) * (1 / 3 * y 2 ^ 3 + p.Vref / 2 * y 2 ^ 2)

@[tmio M, powerlib_domain] theorem hasFDerivAt_flatQ (y : State 4) :
    HasFDerivAt p.flatQ (coord 3 - (p.C * y 2 / p.Is) • coord 2) y := by
  have h := (Dynamics.hasFDerivAt_coord 3 y).sub
    (((Dynamics.hasFDerivAt_coord 2 y).pow 2).const_mul (p.C / (2 * p.Is)))
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

@[tmio M, powerlib_domain] theorem hasFDerivAt_flatPhi (y : State 4) :
    HasFDerivAt p.flatPhi (p.M • coord 1 + p.D • coord 0 -
      (p.Kp * p.C * y 2 / p.Is + p.Ki * p.C ^ 2 * (y 2 ^ 2 + p.Vref * y 2) / (2 * p.Is ^ 2)) •
        coord 2) y := by
  have h2 := Dynamics.hasFDerivAt_coord 2 y
  have h := ((((Dynamics.hasFDerivAt_coord 1 y).const_mul p.M).add
    ((Dynamics.hasFDerivAt_coord 0 y).const_mul p.D)).sub
    ((h2.pow 2).const_mul (p.Kp * p.C / (2 * p.Is)))).sub
    ((((h2.pow 3).const_mul (1 / 3)).add ((h2.pow 2).const_mul (p.Vref / 2))).const_mul
      (p.Ki * p.C ^ 2 / (2 * p.Is ^ 2)))
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

/-- The DC-node rate on the flat curve at a balanced source: `V̇ = I_s (V − V*)/(C V)`. -/
@[tmio M, powerlib_domain] private theorem nodeRate_flat (hA : p.A = 0)
    (hs : p.Psrc p.Vref = p.c0) (δ V : ℝ) :
    p.nodeRate δ V = (p.Is + (-(p.Is * p.Vref)) / V) / p.C := by
  have hPs : p.Ps - p.Pe δ = -(p.Is * p.Vref) := by
    simp only [Plant.Psrc] at hs
    simp only [Plant.Pe, hA, zero_mul, add_zero]
    linarith
  rw [Plant.nodeRate, GFL.DCLink.nodeRate, hPs]

/-- **`c` is conserved on the flat curve** (`A = 0`, balanced source `P_src(V*) = c₀`,
`C, I_s ≠ 0`), off the singular plane. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem flatQ_lie (hA : p.A = 0) (hs : p.Psrc p.Vref = p.c0)
    (hC : p.C ≠ 0) (hI : p.Is ≠ 0) {y : State 4} (hy : y 2 ≠ 0) :
    fderiv ℝ p.flatQ y (p.field y) = 0 := by
  rw [(p.hasFDerivAt_flatQ y).fderiv]
  simp only [p.nodeRate_flat hA hs, field_apply_two, field_apply_three, Dynamics.coord_apply,
    FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  field_simp
  ring

/-- **`Φ` drifts at the rate `K_i (c − c*)`** on the flat curve (`A = 0`, balance at
`(δ*, ζ*)`: `P_ff + K_i ζ* = c₀ = P_src(V*)`, `M, C, I_s ≠ 0`), off the singular plane. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem flatPhi_lie (hA : p.A = 0) (hs : p.Psrc p.Vref = p.c0)
    {ζs : ℝ} (hf : p.Pff + p.Ki * ζs = p.c0) (hM : p.M ≠ 0) (hC : p.C ≠ 0) (hI : p.Is ≠ 0)
    {y : State 4} (hy : y 2 ≠ 0) :
    fderiv ℝ p.flatPhi y (p.field y) =
      p.Ki * ((y 3 - ζs) - p.C * (y 2 ^ 2 - p.Vref ^ 2) / (2 * p.Is)) := by
  rw [(p.hasFDerivAt_flatPhi y).fderiv]
  simp only [FunLike.coe_sub, FunLike.coe_add,
    FunLike.coe_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Dynamics.coord_apply, field_apply_zero, field_apply_one, field_apply_two, smul_eq_mul,
    p.nodeRate_flat hA hs, Plant.swingRate, Pref, Plant.Pe, hA, zero_mul, add_zero]
  rw [show p.Pff = p.c0 - p.Ki * ζs by linarith]
  field_simp
  ring

end Params

namespace VSMDC

/-- **The flat power curve with an integral DC gain is unstable.** With `A = 0`, `K_i ≠ 0` and
`M, C, I_s ≠ 0`, a balanced selected point with `V* ≠ 0` is unstable: Chetaev's function
`K_i (c − c*)(Φ − Φ*)` grows at the rate `K_i² (c − c*)²` (`Params.flatQ_lie`,
`Params.flatPhi_lie`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_flat (m : Model) (hV : m.p.Vref ≠ 0)
    (hb : m.Balanced) (hA : m.p.A = 0) (hKi : m.p.Ki ≠ 0) (hM : m.p.M ≠ 0) (hC : m.p.C ≠ 0)
    (hI : m.p.Is ≠ 0) : connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  obtain ⟨p0, p1, p2, p3⟩ := point_apply m
  have hf : m.p.Pff + m.p.Ki * m.ζ = m.p.c0 := by
    rw [hb.1]; simp [Plant.Pe, hA]
  have hs : m.p.Psrc m.p.Vref = m.p.c0 := by
    rw [hb.2]; simp [Plant.Pe, hA]
  set c0 := m.p.flatQ m.point with hc0
  set f0 := m.p.flatPhi m.point with hf0
  have hc0' : c0 = m.ζ - m.p.C * m.p.Vref ^ 2 / (2 * m.p.Is) := by
    rw [hc0, Params.flatQ, p2, p3]
    ring
  refine Dynamics.unstable_of_chetaev_local (U := nonzeroDC 2)
    (W := fun y => m.p.Ki * (m.p.flatQ y - c0) * (m.p.flatPhi y - f0)) (r := 1)
    (isOpen_nonzeroDC 2) (m.point_mem hV) m.p.field_contDiffOn
    (by unfold Params.flatQ Params.flatPhi; fun_prop) one_pos (fun ε hε => ?_)
    (fun y hy _ hW => ?_)
  · -- a seed: shift `ζ` by `η` and `ω` by `η K_i M`
    set η := ε / (2 * (1 + |m.p.Ki * m.p.M|)) with hη
    have hη0 : 0 < η := by positivity
    refine ⟨m.point + EuclideanSpace.single 3 η + EuclideanSpace.single 1 (η * (m.p.Ki * m.p.M)),
      ?_, ?_⟩
    · rw [add_assoc, add_sub_cancel_left]
      refine (norm_add_le _ _).trans_lt ?_
      rw [EuclideanSpace.single, EuclideanSpace.single, PiLp.norm_single, PiLp.norm_single,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hη0]
      have h1 : η * (1 + |m.p.Ki * m.p.M|) = ε / 2 := by
        rw [hη]; field_simp
      nlinarith [abs_nonneg (m.p.Ki * m.p.M)]
    · have hq : m.p.flatQ (m.point + EuclideanSpace.single 3 η +
          EuclideanSpace.single 1 (η * (m.p.Ki * m.p.M))) - c0 = η := by
        rw [hc0]; simp [Params.flatQ]
      have hφ : m.p.flatPhi (m.point + EuclideanSpace.single 3 η +
          EuclideanSpace.single 1 (η * (m.p.Ki * m.p.M))) - f0 =
          m.p.M * (η * (m.p.Ki * m.p.M)) := by
        rw [hf0]; simp [Params.flatPhi]; ring
      simp only [hq, hφ]
      have : m.p.Ki * η * (m.p.M * (η * (m.p.Ki * m.p.M))) = (m.p.Ki * m.p.M * η) ^ 2 := by ring
      rw [this]
      exact lt_of_le_of_ne (sq_nonneg _)
        (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hKi hM) hη0.ne')).symm
  · -- the Lie derivative is `K_i² (c − c*)²`
    have hy2 : y 2 ≠ 0 := hy
    have hd : HasFDerivAt (fun y => m.p.Ki * (m.p.flatQ y - c0) * (m.p.flatPhi y - f0))
        (m.p.Ki • ((m.p.flatQ y - c0) • (coord 1 - coord 1 + (m.p.M • coord 1 + m.p.D • coord 0 -
          (m.p.Kp * m.p.C * y 2 / m.p.Is + m.p.Ki * m.p.C ^ 2 * (y 2 ^ 2 + m.p.Vref * y 2) /
            (2 * m.p.Is ^ 2)) • coord 2)) +
          (m.p.flatPhi y - f0) • (coord 3 - (m.p.C * y 2 / m.p.Is) • coord 2))) y := by
      have h := (((m.p.hasFDerivAt_flatQ y).sub_const c0).const_mul m.p.Ki).mul
        ((m.p.hasFDerivAt_flatPhi y).sub_const f0)
      refine h.congr_fderiv ?_
      ext v
      simp
      ring
    have hq := m.p.flatQ_lie hA hs hC hI hy2
    have hφ := m.p.flatPhi_lie hA hs hf hM hC hI hy2
    rw [(m.p.hasFDerivAt_flatQ y).fderiv] at hq
    rw [(m.p.hasFDerivAt_flatPhi y).fderiv] at hφ
    rw [hd.fderiv]
    have hqne : m.p.flatQ y - c0 ≠ 0 := fun h0 => by
      simp only [h0, mul_zero, zero_mul] at hW
      exact lt_irrefl 0 hW
    simp only [FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply,
      Pi.add_apply, sub_self, zero_add, smul_eq_mul] at hq hφ ⊢
    rw [hq, hφ]
    have e : (y 3 - m.ζ) - m.p.C * (y 2 ^ 2 - m.p.Vref ^ 2) / (2 * m.p.Is) =
        m.p.flatQ y - c0 := by
      rw [hc0', Params.flatQ]; ring
    rw [e]
    have : m.p.Ki * ((m.p.flatQ y - c0) * (m.p.Ki * (m.p.flatQ y - c0)) +
        (m.p.flatPhi y - f0) * 0) = (m.p.Ki * (m.p.flatQ y - c0)) ^ 2 := by ring
    rw [this]
    exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (mul_ne_zero hKi hqne)).symm

/-- **The flat power curve with a constant-power source is unstable.** With `A = 0` and `I_s = 0`
the DC voltage is frozen at a balanced point (the node power vanishes) and drives the integrator
`ζ`: every balanced selected point with `V* ≠ 0` is unstable, whatever the DC gains. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_flat_constPower (m : Model)
    (hV : m.p.Vref ≠ 0) (hb : m.Balanced) (hA : m.p.A = 0) (hI : m.p.Is = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hPs : m.p.Ps = m.p.c0 := by
    have h := hb.2
    simp [Plant.Psrc, Plant.Pe, hA, hI] at h
    exact h
  refine Dynamics.unstable_of_conserved_drive_local (i := 2) (j := 3)
    (g := fun s => s - m.p.Vref) (isOpen_nonzeroDC 2) (m.point_mem hV) m.p.field_contDiffOn
    (by decide) (contDiff_id.sub contDiff_const)
    (fun ε hε => ⟨m.p.Vref + ε / 2, ?_, ?_⟩) (fun x _ => ?_) (fun x _ => ?_)
  · rw [(point_apply m).2.2.1, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  · simp only [add_sub_cancel_left]
    exact (half_pos hε).ne'
  · simp [Plant.nodeRate, GFL.DCLink.nodeRate, Plant.Pe, hA, hI, hPs]
  · simp

end VSMDC

namespace Params

variable (p : Params)

/-- The energy of the flat curve without DC gains about `(δ*, ζ*)`:
`(M ω + D (δ − δ*))² + ω² + (V − V*)² + (c − c*)²`, `c = flatQ`. -/
def flatEnergy (δs ζs : ℝ) (y : State 4) : ℝ :=
  (p.M * y 1 + p.D * (y 0 - δs)) ^ 2 + y 1 ^ 2 + (y 2 - p.Vref) ^ 2 +
    (p.flatQ y - (ζs - p.C * p.Vref ^ 2 / (2 * p.Is))) ^ 2

@[tmio M, powerlib_domain] theorem contDiff_flatEnergy (δs ζs : ℝ) :
    ContDiff ℝ 1 (p.flatEnergy δs ζs) := by
  unfold flatEnergy flatQ
  fun_prop

/-- **The energy decreases** on the flat curve without DC gains (`A = 0`, `K_p = K_i = 0`,
`P_ff = c₀ = P_src(V*)`, `M, C, I_s ≠ 0`), off the singular plane:
`d/dt flatEnergy = −2 (D/M) ω² + 2 I_s (V − V*)²/(C V)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem flatEnergy_lie (hA : p.A = 0) (hKp : p.Kp = 0)
    (hKi : p.Ki = 0) (hs : p.Psrc p.Vref = p.c0) (hf : p.Pff = p.c0) (hM : p.M ≠ 0)
    (hC : p.C ≠ 0) (hI : p.Is ≠ 0) (δs ζs : ℝ) {y : State 4} (hy : y 2 ≠ 0) :
    fderiv ℝ (p.flatEnergy δs ζs) y (p.field y) =
      -2 * (p.D / p.M) * y 1 ^ 2 + 2 * p.Is * (y 2 - p.Vref) ^ 2 / (p.C * y 2) := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h2 := Dynamics.hasFDerivAt_coord 2 y
  have hq := (p.hasFDerivAt_flatQ y).sub_const (ζs - p.C * p.Vref ^ 2 / (2 * p.Is))
  have h := ((((h1.const_mul p.M).add ((h0.sub_const δs).const_mul p.D)).pow 2).add
    (h1.pow 2)).add ((h2.sub_const p.Vref).pow 2) |>.add (hq.pow 2)
  have hlq := p.flatQ_lie hA hs hC hI hy
  rw [(p.hasFDerivAt_flatQ y).fderiv] at hlq
  have hE : HasFDerivAt (p.flatEnergy δs ζs) _ y := h
  rw [hE.fderiv]
  simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
    Pi.smul_apply, Dynamics.coord_apply, smul_eq_mul] at hlq
  simp only [FunLike.coe_sub, FunLike.coe_add,
    FunLike.coe_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Dynamics.coord_apply, smul_eq_mul, hlq, mul_zero, add_zero, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [field_apply_zero, field_apply_one, field_apply_two, p.nodeRate_flat hA hs,
    Plant.swingRate, Pref, Plant.Pe, hA, hKp, hKi, hf, zero_mul, add_zero]
  field_simp
  ring

end Params

namespace VSMDC

/-- **The flat curve without DC gains is Lyapunov stable.** With `A = 0`, `K_p = K_i = 0`,
`0 < D/M` and a stable DC-node pole `b = I_s/(C V*) < 0`, a balanced selected point with
`V* ≠ 0` is Lyapunov stable: `Params.flatEnergy` is positive definite and does not increase on
the ball of radius `|V*|/2` (`Params.flatEnergy_lie`, `V V* > 0` there). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_of_flat (m : Model)
    (hV : m.p.Vref ≠ 0) (hb : m.Balanced) (hA : m.p.A = 0) (hKp : m.p.Kp = 0) (hKi : m.p.Ki = 0)
    (hDM : 0 < m.p.D / m.p.M) (hbn : m.b < 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  obtain ⟨p0, p1, p2, p3⟩ := point_apply m
  have hM : m.p.M ≠ 0 := fun h => by simp [h] at hDM
  have hD : m.p.D ≠ 0 := fun h => by simp [h] at hDM
  have hCV : m.p.C * m.p.Vref ≠ 0 := fun h => by simp [Model.b, h] at hbn
  have hC : m.p.C ≠ 0 := left_ne_zero_of_mul hCV
  have hI : m.p.Is ≠ 0 := fun h => by simp [Model.b, h] at hbn
  have hf : m.p.Pff = m.p.c0 := by
    have h := hb.1; simp [Plant.Pe, hA, hKi] at h; exact h
  have hs : m.p.Psrc m.p.Vref = m.p.c0 := by rw [hb.2]; simp [Plant.Pe, hA]
  have hVpos : 0 < |m.p.Vref| / 2 := by positivity
  change LyapunovStable m.p.field m.point
  refine lyapunov_stable (V := m.p.flatEnergy m.δ m.ζ) (D := Metric.ball m.point (|m.p.Vref| / 2))
    (by norm_num) ⟨Metric.isOpen_ball, Metric.mem_ball_self hVpos,
      (m.p.contDiff_flatEnergy _ _).continuous,
      (m.p.contDiff_flatEnergy _ _).differentiable one_ne_zero, ?_, fun y hy hne => ?_,
      fun y hy => ?_⟩
  · simp [Params.flatEnergy, Params.flatQ, p0, p1, p2, p3]
    ring
  · -- positive definite
    by_contra hle
    push Not at hle
    have q1 := sq_nonneg (m.p.M * y 1 + m.p.D * (y 0 - m.δ))
    have q2 := sq_nonneg (y 1)
    have q3 := sq_nonneg (y 2 - m.p.Vref)
    have q4 := sq_nonneg (m.p.flatQ y - (m.ζ - m.p.C * m.p.Vref ^ 2 / (2 * m.p.Is)))
    simp only [Params.flatEnergy] at hle
    have e1 : y 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e2 : y 2 = m.p.Vref := by
      have : (y 2 - m.p.Vref) ^ 2 = 0 := by linarith
      linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this]
    have e0 : y 0 = m.δ := by
      have h4 : (m.p.M * y 1 + m.p.D * (y 0 - m.δ)) ^ 2 = 0 := by linarith
      have h5 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
      rw [e1, mul_zero, zero_add] at h5
      have := (mul_eq_zero.mp h5).resolve_left hD
      linarith
    have e3 : y 3 = m.ζ := by
      have h4 : (m.p.flatQ y - (m.ζ - m.p.C * m.p.Vref ^ 2 / (2 * m.p.Is))) ^ 2 = 0 := by
        linarith
      have h5 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
      simp only [Params.flatQ, e2] at h5
      have h6 : y 3 - m.ζ = 0 := by rw [← h5]; ring
      linarith
    apply hne
    ext i
    fin_cases i
    · simpa [p0] using e0
    · simpa [p1] using e1
    · simpa [p2] using e2
    · simpa [p3] using e3
  · -- the Lie derivative is nonpositive on the ball
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have b2 := (Dynamics.abs_coord_sub_le m.point y 2).trans_lt hy
    rw [p2] at b2
    have hpos : 0 < y 2 * m.p.Vref := by
      have h := abs_lt.mp b2
      rcases lt_or_gt_of_ne hV with hn | hp
      · rw [abs_of_neg hn] at h; nlinarith
      · rw [abs_of_pos hp] at h; nlinarith
    have hy2 : y 2 ≠ 0 := fun h => by rw [h, zero_mul] at hpos; exact lt_irrefl 0 hpos
    rw [m.p.flatEnergy_lie hA hKp hKi hs hf hM hC hI _ _ hy2]
    have hterm : m.p.Is / (m.p.C * y 2) ≤ 0 := by
      have e : m.p.Is / (m.p.C * y 2) = m.b * (m.p.Vref * y 2) / (y 2) ^ 2 := by
        rw [Model.b]; field_simp
      rw [e]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hbn.le (by nlinarith)) (sq_nonneg _)
    have e2 : 2 * m.p.Is * (y 2 - m.p.Vref) ^ 2 / (m.p.C * y 2) =
        2 * (y 2 - m.p.Vref) ^ 2 * (m.p.Is / (m.p.C * y 2)) := by ring
    rw [e2]
    nlinarith [sq_nonneg (y 1), sq_nonneg (y 2 - m.p.Vref)]

/-! ## Two boundary witnesses -/

/-- The flat-curve plant of the witnesses: `M = D = C = 1`, no power curve (`c₀ = A = α = 0`), a
power reference `P_ff = 0`, the source `P_src(V) = 1 − V`. -/
def flatPlant : Plant := ⟨1, 1, 1, 0, 0, 0, 0, 1, -1⟩

/-- The flat curve without DC gains (`V* = 1`, `K_p = K_i = 0`) at `(0, 0, 1, 0)`. -/
def flatOpen : Model := ⟨{ toPlant := flatPlant, Vref := 1, Kp := 0, Ki := 0 }, 0, 0⟩

/-- The flat curve with an integral DC gain (`V* = 1`, `K_p = 0`, `K_i = 1`) at `(0, 0, 1, 0)`. -/
def flatIntegral : Model := ⟨{ toPlant := flatPlant, Vref := 1, Kp := 0, Ki := 1 }, 0, 0⟩

@[tmio M, powerlib_domain] private theorem flat_coeffs (Ki : ℝ) :
    let m : Model := ⟨{ toPlant := flatPlant, Vref := 1, Kp := 0, Ki := Ki }, 0, 0⟩
    m.Balanced ∧ m.b = -1 ∧ m.a3 = 2 ∧ m.a2 = 1 ∧ m.a1 = 0 ∧ m.a0 = 0 := by
  simp only [Model.Balanced, Model.b, Model.a3, Model.a2, Model.a1, Model.a0, Model.k,
    flatPlant, Plant.Pe, Plant.Psrc, Plant.k]
  norm_num

/-- Both witnesses lie on the Routh boundary: their quartic is `s² (s + 1)²` (`a₃ = 2`, `a₂ = 1`,
`a₁ = a₀ = 0`), neither Routh nor a strict violation, so they meet neither requirement. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem flat_not_meets (Ki : ℝ) :
    let m : Model := ⟨{ toPlant := flatPlant, Vref := 1, Kp := 0, Ki := Ki }, 0, 0⟩
    ¬ m.Stable ∧ ¬ m.Unstable := by
  intro m
  obtain ⟨-, -, h3, h2, h1, h0⟩ := flat_coeffs Ki
  refine ⟨fun ⟨_, _, _, ha1, _⟩ => ?_, fun ⟨_, _, hv⟩ => ?_⟩
  · change 0 < m.a1 at ha1
    rw [h1] at ha1
    exact lt_irrefl 0 ha1
  · change m.a3 < 0 ∨ m.a2 < 0 ∨ m.a1 < 0 ∨ m.a0 < 0 ∨
      m.a3 * m.a2 * m.a1 < m.a1 ^ 2 + m.a3 ^ 2 * m.a0 at hv
    rw [h3, h2, h1, h0] at hv
    norm_num at hv

@[tmio TM, powerlib_domain] theorem flatOpen_mem_den_lyapunovStable :
    connection% (flatOpen ∈ family.den (.flow .lyapunovStable)) :=
  mem_den_lyapunovStable_of_flat flatOpen one_ne_zero (flat_coeffs 0).1 rfl rfl rfl
    (by norm_num [flatOpen, flatPlant]) (by norm_num [flatOpen, flatPlant, Model.b])

@[tmio TM, powerlib_domain] theorem flatOpen_not_mem_den_locallyAsymptoticallyStable :
    connection% (flatOpen ∉ family.den (.flow .locallyAsymptoticallyStable)) :=
  not_mem_den_locallyAsymptoticallyStable_of_Ki_eq_zero flatOpen one_ne_zero (flat_coeffs 0).1
    rfl

@[tmio TM, powerlib_domain] theorem flatIntegral_mem_den_unstable :
    connection% (flatIntegral ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_flat flatIntegral one_ne_zero (flat_coeffs 1).1 rfl one_ne_zero one_ne_zero
    one_ne_zero (by norm_num [flatIntegral, flatPlant])

/-- **The Lyapunov translation is not exact within `V* ≠ 0`.** `flatOpen` is Lyapunov stable,
has `V* = 1` and does not meet the stability condition. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_inter_lyapunovStable :
    connection% (¬ TMIO.realize family.meets (family.translate (.flow .lyapunovStable)) =
      family.den (.flow .lyapunovStable) ∩ {m : Model | m.p.Vref ≠ 0}) :=
  Spectral.local_realize_ne_den_inter_of_witness (Or.inl rfl)
    flatOpen_mem_den_lyapunovStable (show flatOpen.p.Vref ≠ 0 from one_ne_zero)
    (flat_not_meets 0).1

@[tmio M, powerlib_domain] private theorem flat_meets_iff (q : Spectral.Requirement) :
    family.meets flatOpen q ↔ family.meets flatIntegral q := by
  have h0 := flat_not_meets 0
  have h1 := flat_not_meets 1
  cases q
  · exact ⟨fun h => absurd h h0.1, fun h => absurd h h1.1⟩
  · exact ⟨fun h => absurd h h0.2, fun h => absurd h h1.2⟩

/-- **Lyapunov stability is inexpressible in the requirement language**: `flatOpen` and
`flatIntegral` meet the same requirements, the first is Lyapunov stable and the second not. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_lyapunovStable :
    connection% (∀ T, TMIO.realize family.meets T ≠ family.den (.flow .lyapunovStable)) :=
  Spectral.realize_ne_den_of_indistinguishable flat_meets_iff flatOpen_mem_den_lyapunovStable
    (Spectral.not_mem_den_lyapunovStable_of_unstable flatIntegral_mem_den_unstable)

/-- **Instability is inexpressible in the requirement language**: `flatIntegral` is unstable,
`flatOpen` (Lyapunov stable) is not, and they meet the same requirements. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_unstable :
    connection% (∀ T, TMIO.realize family.meets T ≠ family.den (.flow .unstable)) :=
  Spectral.realize_ne_den_of_indistinguishable (fun q => (flat_meets_iff q).symm)
    flatIntegral_mem_den_unstable fun hu =>
      Spectral.not_mem_den_lyapunovStable_of_unstable hu flatOpen_mem_den_lyapunovStable

end VSMDC

end powerlib.GFM.DCLink
