import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Coordinates
import theorem.Spectral.Family
import theorem.TMIO.ClaimElab
import theorem.GridTiedConverter.GFL.DCLink.PowerBalance
import theorem.Dynamics.Degenerate.PlaneCollapse
import theorem.Dynamics.Instability

/-! # Grid-forming VSM with a DC link, DC-voltage loop open (three states)

Model boundary.
* State `x = (δ, ω, V) : Dynamics.State 3`, in this order: power angle of the internal EMF
  relative to the stiff grid (rad), angular-frequency deviation (rad/s), DC-link voltage.
* Continuous time, autonomous, no input. Quasi-static line: the converter exports
  `P_e(δ) = c₀ + A sin(δ − α)` (`Plant.Pe`; for an EMF `E` behind `R + jX` on a stiff grid
  `V_g`, `c₀ = E²R/|Z|²`, `A = E V_g/|Z|`, `α = atan2(R, X)`; that phasor reduction is not
  derived here). Constant EMF magnitude `E` (the modulation compensates `V`).
* VSM synchronization with a constant power reference `P_ff` (no DC-voltage loop):
  `δ̇ = ω`, `M ω̇ = P_ff − P_e(δ) − D ω`.
* DC link: capacitor `C` fed by an affine DC source `P_src(V) = P_s + I_s V` (`Plant.Psrc`;
  constant current `P_s = 0`, constant power `I_s = 0`) and discharged by the exported power
  through a lossless bridge: `C V̇ = (P_src(V) − P_e(δ)) / V` (`Plant.nodeRate`, the DC-node
  law `GFL.DCLink.nodeRate` of `theorem/GridTiedConverter/GFL/DCLink/PowerBalance.lean` with
  source current `I_s` and node power `P_s − P_e(δ)`).
* Signs: active power export-positive (the GFM convention of
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`); source power positive into the DC node.
* Excluded: the DC-voltage loop (`theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`), reactive
  power and amplitude loops, inner voltage and current loops, line dynamics, limits, PLL, delay,
  PWM, DC-link losses. Parameters are arbitrary reals. The field contains `1/V` and is `C¹` on
  the open set `V ≠ 0`; on the singular plane `V = 0` the power term is read with Lean's
  `x / 0 = 0` (`V̇ = I_s/C`, `Plant.nodeRate_zero`) and only the collapse, repulsion and
  degenerate-balance statements below are made there (the physical limit, overmodulation, is
  reached before `V = 0` and is not modelled).
* Level: equilibria and local exponential stability or instability of an equilibrium, from the
  Jacobian computed by `fderiv`.

Source: GFM counterpart study, note T7 (`t7-dcside`: part (a), the VSM + DC-link model, its
Jacobian and the open-DC sign obstruction; part (c), the singular plane, there derived and not
tested; derivations and numerical checks are notes outside the repository); the GFL counterparts
are `theorem/GridTiedConverter/GFL/DCLink/Cascade.lean` (`mem_den_unstable_of_inverter`) and
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean` (the collapse pattern); the analysis
of the degenerate balance `P_s = P_e(δ*)` is new and follows
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Collapse.lean` and `CollapseDegenerate.lean`.
Routh–Hurwitz for 2×2 matrices and the extra-pole factorization are
`Criteria.isHurwitz_fin_two_iff` and `Linear.spectrallyStable_iff_of_extra_pole`.

Results.
* `Plant.openField_eq_zero_iff`: `(δ, ω, V)` is an equilibrium iff `ω = 0`,
  `P_ff = P_e(δ)` and `P_src(V) = P_e(δ)` (`M, C, V ≠ 0`).
* `Plant.hasFDerivAt_openField`: on `V ≠ 0` the Jacobian is `Plant.openJacobian δ V`
  `= [[0, 1, 0], [−k/M, −D/M, 0], [−k/(C V), 0, j]]`, `k = P_e'(δ) = A cos(δ − α)`,
  `j = (P_e(δ) − P_s)/(C V²)` (`Plant.nodeSlope`); it is block triangular.
* `Plant.det_characteristicMatrix_openJacobian`: `det(sI − J) = (s² + (D/M) s + k/M)(s − j)`;
  at a balanced point `j = b = I_s/(C V) = P_src'(V)/(C V)` (`Plant.nodeSlope_of_balance`).
  `Plant.isHurwitz_openJacobian_iff`: Hurwitz iff `0 < D/M`, `0 < k/M` and `j < 0`.

Family and connection conclusions.
* `OpenLoop.family := Spectral.localFamily Model.field Model.Stable Model.Unstable`: a model
  (`OpenLoop.Model`) is a plant with a selected angle `δ*` and DC voltage `V*`, read as the field
  translated so that `(δ*, 0, V*)` is the origin. `Model.Stable`: `V* ≠ 0`, balance
  `P_ff = P_e(δ*) = P_src(V*)`, `0 < D/M`, `0 < k/M`, `b < 0`; `Model.Unstable`: `V* ≠ 0`,
  balance, and `0 < b`, `D/M < 0` or `k/M < 0`. Soundness `OpenLoop.chain_le_semantics`
  (`Spectral.local_chain_le_semantics`).
* `OpenLoop.mem_den_locallyExponentiallyStable_iff` (`V* ≠ 0`): locally exponentially stable
  iff balanced with `0 < D/M`, `0 < k/M` and `I_s/(C V*) < 0` (converse linearization for a field
  `C¹` on `V ≠ 0`); within `V* ≠ 0` the local exponential translation is exact
  (`OpenLoop.realize_eq_den_inter`).
* Constant current (`P_s = 0`, `C > 0`):
  `OpenLoop.mem_den_locallyExponentiallyStable_iff_of_constCurrent` — locally exponentially
  stable iff balanced, `0 < D/M`, `0 < k/M` and `P_e(δ*) < 0` (import, rectifier operation);
  `OpenLoop.mem_den_unstable_of_export` — exporting (`P_e(δ*) > 0`) it is unstable for every
  inertia and damping: the DC node pole `b = P₀/(C V*²) > 0` is an eigenvalue
  with eigenvector `e_V` whatever `M, D` (`OpenLoop.mem_den_unstable`, the GFM analog of the GFL
  `mem_den_unstable_of_inverter`). Constant power (`I_s = 0`): never locally exponentially
  stable (`OpenLoop.not_mem_den_locallyExponentiallyStable_of_constPower`: `b = 0`, the
  equilibria form a line in `V`).
* Selected points on the singular plane `V* = 0` (not equilibria):
  `OpenLoop.mem_den_locallyExponentiallyStable_of_collapse` — if `(P_s − P_e(δ*))/C < 0` and
  `I_s/C ≠ 0`, the segment-based local exponential estimate holds because solutions reach the
  plane in finite time (`d(V²)/dt = 2 (I_s V + P_s − P_e(δ))/C ≤ −a` nearby,
  `Plant.two_mul_nodeRate`; generic `Dynamics.Degenerate.locallyExponentiallyStable_of_collapse`),
  not because they converge; `OpenLoop.mem_den_unstable_of_repel` — `(P_s − P_e(δ*))/C > 0` is
  unstable (`Dynamics.Degenerate.unstable_of_repel`, with the regularized fields
  `Plant.exists_contDiff_eq_openField_of_sign`, equal to the model on `σ V ≥ s`). For a
  constant-current source with `C > 0`: export collapses, import repels.
* The degenerate balance `P_s = P_e(δ*)` on the plane (the GFL counterparts are
  `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Collapse.lean` and `CollapseDegenerate.lean`). With
  `q = (I_s V + P_s − P_e(δ))/C` (`Plant.planeQ`), off the plane `V V̇ = q`
  (`Plant.openField_two_eq_planeQ_div`) and `q̇ = G + H q / V` (`Plant.planeQ_lie`),
  `G = −k(δ) ω / C` (`Plant.planeG`), `H = I_s/C`; at `(δ*, 0, 0)` `G = 0`, so the discriminant
  `H² + 4G = H²` is never negative (no focus, unlike the GFL PLL–DC model).
  `OpenLoop.mem_den_unstable_of_degenerate` — `I_s/C ≠ 0` ⇒ unstable (invariant cone,
  `Dynamics.Degenerate.unstable_of_cone`);
  `OpenLoop.not_mem_den_locallyExponentiallyStable_of_degenerate_of_drift` — `I_s/C = 0` and an
  unbalanced swing `(P_ff − P_e(δ*))/M ≠ 0` ⇒ not locally exponentially stable (nilpotent point
  with drift, `Dynamics.Degenerate.not_locallyExponentiallyStable_of_nilpotent`);
  `OpenLoop.not_mem_den_locallyAsymptoticallyStable_of_degenerate_of_rest` — `I_s/C = 0` and a
  balanced swing ⇒ a line of equilibria `(δ*, 0, V)`, not locally asymptotically stable. Hence
  `OpenLoop.not_mem_den_locallyExponentiallyStable_of_degenerate`: the degenerate balance is never
  locally exponentially stable, and `OpenLoop.mem_den_locallyExponentiallyStable_iff_of_V_eq_zero`:
  for `I_s/C ≠ 0` a point of the plane is locally exponentially stable iff
  `(P_s − P_e(δ*))/C < 0`. Not decided: `I_s/C = 0` with `(P_s − P_e(δ*))/C < 0` (the plane is
  then invariant and carries the swing dynamics; the collapse law needs a crossing current).
* Static evidence on the model: the equilibrium, Jacobian, characteristic-polynomial and Hurwitz
  identities above.
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)

/-- Parameters of the VSM with a DC link and an affine DC source; the DC-voltage loop is open
(constant power reference `P_ff`). -/
structure Plant where
  /-- Virtual inertia `M`. -/
  M : ℝ
  /-- Damping `D`. -/
  D : ℝ
  /-- DC-link capacitance `C`. -/
  C : ℝ
  /-- Power reference (feed-forward) `P_ff`. -/
  Pff : ℝ
  /-- Offset `c₀` of the power characteristic `P_e(δ) = c₀ + A sin(δ − α)`. -/
  c0 : ℝ
  /-- Amplitude `A` of the power characteristic. -/
  A : ℝ
  /-- Loss angle `α` of the power characteristic. -/
  α : ℝ
  /-- Constant part `P_s` of the DC source `P_src(V) = P_s + I_s V`. -/
  Ps : ℝ
  /-- Current part `I_s` of the DC source. -/
  Is : ℝ

namespace Plant

variable (q : Plant)

/-- Exported power, quasi-static line: `P_e(δ) = c₀ + A sin(δ − α)`. -/
def Pe (δ : ℝ) : ℝ := q.c0 + q.A * Real.sin (δ - q.α)

/-- Synchronizing coefficient `k(δ) = P_e'(δ) = A cos(δ − α)`. -/
def k (δ : ℝ) : ℝ := q.A * Real.cos (δ - q.α)

/-- Source power into the DC node: `P_src(V) = P_s + I_s V`. -/
def Psrc (V : ℝ) : ℝ := q.Ps + q.Is * V

/-- Swing rate `ω̇ = (P_ref − P_e(δ) − D ω) / M`. -/
def swingRate (Pref δ ω : ℝ) : ℝ := (Pref - q.Pe δ - q.D * ω) / q.M

/-- DC-node rate `V̇ = (I_s + (P_s − P_e(δ))/V)/C`, i.e. `C V̇ = (P_src(V) − P_e(δ))/V` for
`V ≠ 0`: the DC-node law `GFL.DCLink.nodeRate` with source current `I_s` and node power
`P_s − P_e(δ)`. -/
def nodeRate (δ V : ℝ) : ℝ := GFL.DCLink.nodeRate q.C q.Is (q.Ps - q.Pe δ) V

/-- DC-node slope `∂V̇/∂V = (P_e(δ) − P_s) / (C V²)`. -/
def nodeSlope (δ V : ℝ) : ℝ := (q.Pe δ - q.Ps) / (q.C * V ^ 2)

/-- The open-loop field on `(δ, ω, V)`. -/
def openField (x : State 3) : State 3 :=
  mk3 (x 1) (q.swingRate q.Pff (x 0) (x 1)) (q.nodeRate (x 0) (x 2))

/-- The swing block `[[0, 1], [−k/M, −D/M]]` at the angle `δ`. -/
def swingJacobian (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -q.k δ / q.M, -q.D / q.M]

/-- The open-loop Jacobian at angle `δ` and DC voltage `V`. -/
def openJacobian (δ V : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; -q.k δ / q.M, -q.D / q.M, 0; -q.k δ / (q.C * V), 0, q.nodeSlope δ V]

@[tmio M, powerlib_domain] theorem hasDerivAt_Pe (δ : ℝ) : HasDerivAt q.Pe (q.k δ) δ := by
  have h := (((hasDerivAt_id δ).sub_const q.α).sin.const_mul q.A).const_add q.c0
  unfold Pe k
  simpa using h

/-- The angle component of the exported power as a function of the state. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_Pe_comp {n : ℕ} (i : Fin n) (x : State n) :
    HasFDerivAt (fun y : State n => q.Pe (y i)) (q.k (x i) • Dynamics.coord i) x := by
  have h := (q.hasDerivAt_Pe (x i)).comp_hasFDerivAt x (Dynamics.hasFDerivAt_coord i x)
  refine h.congr_fderiv ?_
  ext v
  simp

/-- The DC node is at rest iff the source power balances the exported power
(`C ≠ 0`, `V ≠ 0`). -/
@[tmio M, powerlib_domain] theorem nodeRate_eq_zero_iff (hC : q.C ≠ 0) {δ V : ℝ} (hV : V ≠ 0) :
    q.nodeRate δ V = 0 ↔ q.Psrc V = q.Pe δ := by
  rw [nodeRate, GFL.DCLink.nodeRate, div_eq_zero_iff, or_iff_left hC, Psrc]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [show q.Ps - q.Pe δ = -(q.Is * V) by linarith, neg_div, mul_div_cancel_right₀ _ hV,
      add_neg_cancel]

/-- At a balanced point (`P_src(V) = P_e(δ)`, `V ≠ 0`) the DC node is at rest, for every `C`. -/
@[tmio M, powerlib_domain] theorem nodeRate_of_balance {δ V : ℝ} (hV : V ≠ 0)
    (hb : q.Psrc V = q.Pe δ) : q.nodeRate δ V = 0 := by
  have hP : q.Ps - q.Pe δ = -(q.Is * V) := by rw [← hb, Psrc]; ring
  rw [nodeRate, GFL.DCLink.nodeRate, hP, neg_div, mul_div_cancel_right₀ _ hV, add_neg_cancel,
    zero_div]

/-- The DC-node rate as a function of the state, off the singular plane `V = 0`
(`GFL.DCLink.hasFDerivAt_nodeRate`). -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_nodeRate_comp {n : ℕ} (i j : Fin n)
    {x : State n} (hx : x j ≠ 0) :
    HasFDerivAt (fun y : State n => q.nodeRate (y i) (y j))
      ((-q.k (x i) / (q.C * x j)) • Dynamics.coord i +
        q.nodeSlope (x i) (x j) • Dynamics.coord j) x := by
  have hP : HasFDerivAt (fun y : State n => q.Ps - q.Pe (y i))
      (-(q.k (x i) • Dynamics.coord i)) x := (q.hasFDerivAt_Pe_comp i x).const_sub q.Ps
  have h := GFL.DCLink.hasFDerivAt_nodeRate q.C (hasFDerivAt_const q.Is x) hP
    (Dynamics.hasFDerivAt_coord j x) hx
  refine h.congr_fderiv ?_
  ext v
  simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply, _root_.neg_apply,
    Dynamics.coord_apply, smul_eq_mul, nodeSlope, _root_.zero_apply]
  by_cases hC : q.C = 0
  · simp [hC]
  · field_simp
    ring

/-- The open-loop Jacobian, computed from the field: `D openField (x) = openJacobian (x 0) (x 2)`
wherever `V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_openField {x : State 3} (hx : x 2 ≠ 0) :
    HasFDerivAt q.openField
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (q.openJacobian (x 0) (x 2))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  fin_cases i
  · have h := Dynamics.hasFDerivAt_coord (1 : Fin 3) x
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · ext v
      simp [openJacobian, toEuclideanCLM_apply3]
    · simp [openField]
  · have h := ((((hasFDerivAt_const q.Pff x).sub (q.hasFDerivAt_Pe_comp 0 x)).sub
      ((Dynamics.hasFDerivAt_coord (1 : Fin 3) x).const_mul q.D)).mul_const q.M⁻¹)
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · ext v
      simp [openJacobian, toEuclideanCLM_apply3]
      ring
    · simp [openField, swingRate, div_eq_mul_inv]
  · have h := q.hasFDerivAt_nodeRate_comp (0 : Fin 3) (2 : Fin 3) hx
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · ext v
      simp [openJacobian, toEuclideanCLM_apply3]
    · simp [openField]

@[tmio M, powerlib_domain] theorem fderiv_openField {x : State 3} (hx : x 2 ≠ 0) :
    fderiv ℝ q.openField x =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (q.openJacobian (x 0) (x 2)) :=
  (q.hasFDerivAt_openField hx).fderiv

end Plant

/-- The states whose DC-link voltage, coordinate `k`, is nonzero. -/
def nonzeroDC {n : ℕ} (k : Fin n) : Set (State n) := {x | x k ≠ 0}

@[tmio M, powerlib_domain] theorem isOpen_nonzeroDC {n : ℕ} (k : Fin n) :
    IsOpen (nonzeroDC k) :=
  isOpen_ne_fun (EuclideanSpace.proj k).continuous continuous_const

namespace Plant

variable (q : Plant)

/-- The open-loop field is `C¹` on `V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem openField_contDiffOn :
    ContDiffOn ℝ 1 q.openField (nonzeroDC 2) := by
  rw [contDiffOn_euclidean]
  intro i
  fin_cases i
  · simpa [openField] using (Dynamics.contDiff_coord (n := 3) (k := 1) 1).contDiffOn
  · simp only [openField, Fin.mk_one, Fin.isValue, mk3_one]
    apply ContDiff.contDiffOn
    unfold swingRate Pe
    fun_prop
  · simp only [openField, Fin.reduceFinMk, Fin.isValue, mk3_two]
    have hP : ContDiff ℝ 1 (fun y : State 3 => q.Ps - q.Pe (y 0)) := by
      unfold Pe
      fun_prop
    exact GFL.DCLink.contDiffOn_nodeRate q.C contDiffOn_const hP.contDiffOn
      (Dynamics.contDiff_coord (n := 3) (k := 1) 2).contDiffOn fun y hy => hy

/-- Equilibria of the open loop: `ω = 0`, `P_ff = P_e(δ)` and `P_src(V) = P_e(δ)`
(`M, C, V ≠ 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem openField_eq_zero_iff (hM : q.M ≠ 0) (hC : q.C ≠ 0)
    {x : State 3} (hx : x 2 ≠ 0) :
    q.openField x = 0 ↔ x 1 = 0 ∧ q.Pff = q.Pe (x 0) ∧ q.Psrc (x 2) = q.Pe (x 0) := by
  constructor
  · intro h
    have e0 := congrArg (fun y : State 3 => y 0) h
    have e1 := congrArg (fun y : State 3 => y 1) h
    have e2 := congrArg (fun y : State 3 => y 2) h
    simp only [openField, mk3_zero, mk3_one, mk3_two, PiLp.zero_apply] at e0 e1 e2
    rw [swingRate, e0, mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM, sub_eq_zero] at e1
    exact ⟨e0, e1, (q.nodeRate_eq_zero_iff hC hx).mp e2⟩
  · rintro ⟨h1, h2, h3⟩
    apply state3_ext <;> simp [openField, swingRate, h1, h2, q.nodeRate_of_balance hx h3]

/-- At a balanced point (`P_src(V) = P_e(δ)`, `V ≠ 0`) the DC-node slope is
`b = I_s/(C V) = P_src'(V)/(C V)`. -/
@[tmio M, powerlib_domain] theorem nodeSlope_of_balance {δ V : ℝ} (hV : V ≠ 0)
    (hb : q.Psrc V = q.Pe δ) : q.nodeSlope δ V = q.Is / (q.C * V) := by
  rw [nodeSlope, ← hb, Psrc, show q.Ps + q.Is * V - q.Ps = q.Is * V by ring, sq, ← mul_assoc]
  exact mul_div_mul_right _ _ hV

/-- Block-triangular characteristic polynomial: `det(sI − J) = det(sI − S)(s − j)`, `S` the
swing block, `det(sI − S) = s² + (D/M) s + k/M`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_openJacobian (δ V : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (q.openJacobian δ V) s).det =
      (Linear.characteristicMatrix (q.swingJacobian δ) s).det *
        (s + ((-q.nodeSlope δ V : ℝ) : ℂ)) := by
  simp [Linear.characteristicMatrix, openJacobian, swingJacobian, Matrix.det_fin_three,
    Matrix.det_fin_two]
  ring

/-- The open-loop Jacobian is Hurwitz iff `0 < D/M`, `0 < k/M` and `j < 0`. Static evidence on
the model. -/
@[tmio TM, powerlib_domain] theorem isHurwitz_openJacobian_iff (δ V : ℝ) :
    LinearSystems.IsHurwitz (q.openJacobian δ V) ↔
      0 < q.D / q.M ∧ 0 < q.k δ / q.M ∧ q.nodeSlope δ V < 0 := by
  rw [← Linear.spectrallyStable_iff_isHurwitz,
    Linear.spectrallyStable_iff_of_extra_pole (q.det_characteristicMatrix_openJacobian δ V),
    Linear.spectrallyStable_iff_isHurwitz, Criteria.isHurwitz_fin_two_iff]
  simp [swingJacobian, Matrix.trace_fin_two, Matrix.det_fin_two, neg_div, and_assoc]


/-! ## Near the singular plane `V = 0` -/

/-- Off the singular plane, `2 V V̇ = 2 (I_s V + P_s − P_e(δ))/C`, a smooth function of the
state. -/
@[tmio M, powerlib_domain] theorem two_mul_nodeRate {δ V : ℝ} (hV : V ≠ 0) :
    2 * V * q.nodeRate δ V = 2 * (q.Is * V + q.Ps - q.Pe δ) / q.C := by
  have h : 2 * V * (q.Is + (q.Ps - q.Pe δ) / V) = 2 * (q.Is * V + q.Ps - q.Pe δ) := by
    field_simp
    ring
  rw [nodeRate, GFL.DCLink.nodeRate, ← mul_div_assoc, h]

/-- On the singular plane the DC component is read with Lean's `x / 0 = 0`: `V̇ = I_s / C`. -/
@[tmio M, powerlib_domain] theorem nodeRate_zero (δ : ℝ) : q.nodeRate δ 0 = q.Is / q.C := by
  simp [nodeRate, GFL.DCLink.nodeRate]

/-- A `C¹` field equal to the open loop on the half space `σ V ≥ s` (`σ = ±1`, `s > 0`): the
denominator `V` is replaced by `σ Dynamics.regDen s (σ V)`. -/
@[tmio M, powerlib_domain] theorem exists_contDiff_eq_openField_of_sign {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hs : 0 < s) :
    ∃ g : State 3 → State 3, ContDiff ℝ 1 g ∧
      ∀ y : State 3, s ≤ σ * y 2 → g y = q.openField y := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨fun y => mk3 (y 1) (q.swingRate q.Pff (y 0) (y 1))
    (GFL.DCLink.nodeRate q.C q.Is (q.Ps - q.Pe (y 0)) (σ * Dynamics.regDen s (σ * y 2))), ?_,
    ?_⟩
  · have hden : ∀ y ∈ (Set.univ : Set (State 3)), σ * Dynamics.regDen s (σ * y 2) ≠ 0 :=
      fun y _ => by
        have h2 : 0 < Dynamics.regDen s (σ * y 2) :=
          lt_of_lt_of_le (by positivity) (Dynamics.half_le_regDen hs (σ * y 2))
        rcases hσ with rfl | rfl
        · positivity
        · intro h; linarith
    have hP : ContDiff ℝ 1 (fun y : State 3 => q.Ps - q.Pe (y 0)) := by
      unfold Pe
      fun_prop
    have hR : ContDiff ℝ 1 (fun y : State 3 => σ * Dynamics.regDen s (σ * y 2)) :=
      contDiff_const.mul ((Dynamics.contDiff_regDen s).comp
        (contDiff_const.mul (Dynamics.contDiff_coord 2)))
    rw [contDiff_euclidean]
    intro i
    fin_cases i
    · simpa using Dynamics.contDiff_coord (n := 3) (k := 1) 1
    · simp only [Fin.mk_one, Fin.isValue, mk3_one]
      unfold swingRate Pe
      fun_prop
    · simp only [Fin.reduceFinMk, Fin.isValue, mk3_two]
      exact contDiffOn_univ.mp (GFL.DCLink.contDiffOn_nodeRate q.C contDiffOn_const
        hP.contDiffOn hR.contDiffOn hden)
  · intro y hy
    have hr : σ * Dynamics.regDen s (σ * y 2) = y 2 := by
      rw [Dynamics.regDen_eq hs (by linarith), ← mul_assoc, hσ2, one_mul]
    simp only [openField, nodeRate, hr]

/-- `q = (I_s V + P_s − P_e(δ))/C`: off the singular plane `V V̇ = q`
(`Plant.openField_two_eq_planeQ_div`). -/
def planeQ (y : State 3) : ℝ := (q.Is * y 2 + q.Ps - q.Pe (y 0)) / q.C

/-- The part `G = −k(δ) ω / C` of `dq/dt` that does not involve `V̇`: off the plane
`dq/dt = G + (I_s/C) q / V` (`Plant.planeQ_lie`). -/
def planeG (y : State 3) : ℝ := -(q.k (y 0) * y 1) / q.C

@[tmio M, powerlib_domain] theorem hasFDerivAt_planeQ (y : State 3) :
    HasFDerivAt q.planeQ ((-q.k (y 0) / q.C) • Dynamics.coord 0 +
      (q.Is / q.C) • Dynamics.coord 2) y := by
  have h := ((((Dynamics.hasFDerivAt_coord (2 : Fin 3) y).const_mul q.Is).add_const q.Ps).sub
    (q.hasFDerivAt_Pe_comp 0 y)).mul_const q.C⁻¹
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  · ext v
    simp [div_eq_mul_inv]
    ring
  · simp [planeQ, div_eq_mul_inv]

@[tmio M, powerlib_domain] theorem contDiff_planeQ : ContDiff ℝ 1 q.planeQ := by
  unfold planeQ Pe
  fun_prop

@[tmio M, powerlib_domain] theorem contDiff_planeG : ContDiff ℝ 1 q.planeG := by
  unfold planeG k
  fun_prop

/-- Off the singular plane the DC component of the field is `q / V`. -/
@[tmio M, powerlib_domain] theorem openField_two_eq_planeQ_div {y : State 3} (hy : y 2 ≠ 0) :
    q.openField y 2 = q.planeQ y / y 2 := by
  rw [eq_div_iff hy, mul_comm]
  simp only [openField, mk3_two]
  have h := q.two_mul_nodeRate (δ := y 0) hy
  rw [planeQ]
  linear_combination h / 2

/-- `dq/dt = G + (I_s/C) q / V` off the singular plane. -/
@[tmio M, powerlib_domain] theorem planeQ_lie {y : State 3} (hy : y 2 ≠ 0) :
    fderiv ℝ q.planeQ y (q.openField y) = q.planeG y + q.Is / q.C * (q.planeQ y / y 2) := by
  rw [(q.hasFDerivAt_planeQ y).fderiv, ← q.openField_two_eq_planeQ_div hy]
  simp [planeG, openField]
  ring

/-- Off the DC component the field is the smooth field `(ω, ω̇, 0)`. -/
@[tmio M, powerlib_domain] theorem openField_sub_single (y : State 3) :
    q.openField y - q.openField y 2 • EuclideanSpace.single 2 (1 : ℝ) =
      mk3 (y 1) (q.swingRate q.Pff (y 0) (y 1)) 0 := by
  apply state3_ext <;> simp [openField]

@[tmio M, powerlib_domain] theorem continuous_openField_sub_single :
    Continuous fun y => q.openField y - q.openField y 2 • EuclideanSpace.single 2 (1 : ℝ) := by
  have h : ContDiff ℝ 1 (fun y : State 3 => mk3 (y 1) (q.swingRate q.Pff (y 0) (y 1)) 0) := by
    rw [contDiff_euclidean]
    intro i
    fin_cases i
    · simpa using Dynamics.contDiff_coord (n := 3) (k := 1) 1
    · simp only [Fin.mk_one, Fin.isValue, mk3_one]
      unfold swingRate Pe
      fun_prop
    · simp only [Fin.reduceFinMk, Fin.isValue, mk3_two]
      exact contDiff_const
  simpa only [q.openField_sub_single] using h.continuous

end Plant

namespace OpenLoop

/-- A VSM–DC plant with its DC-voltage loop open, read about a selected angle `δ*` and DC
voltage `V*`: the operating point is `(δ*, 0, V*)`. -/
structure Model where
  /-- The plant. -/
  q : Plant
  /-- The selected angle `δ*`. -/
  δ : ℝ
  /-- The selected DC voltage `V*`. -/
  V : ℝ

/-- The selected point `(δ*, 0, V*)`. -/
def Model.point (m : Model) : State 3 := mk3 m.δ 0 m.V

/-- The open-loop field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 3) : State 3 := m.q.openField (z + m.point)

/-- The DC-node pole `b = I_s/(C V*)` at the selected point. -/
def Model.b (m : Model) : ℝ := m.q.Is / (m.q.C * m.V)

/-- Power balance at the selected point: `P_ff = P_e(δ*)` and `P_src(V*) = P_e(δ*)`. -/
def Model.Balanced (m : Model) : Prop := m.q.Pff = m.q.Pe m.δ ∧ m.q.Psrc m.V = m.q.Pe m.δ

/-- Stability condition: nonzero `V*`, balance, `0 < D/M`, `0 < k/M` and `b < 0`. -/
def Model.Stable (m : Model) : Prop :=
  m.V ≠ 0 ∧ m.Balanced ∧ 0 < m.q.D / m.q.M ∧ 0 < m.q.k m.δ / m.q.M ∧ m.b < 0

/-- Instability condition: nonzero `V*`, balance and `0 < b`, `D/M < 0` or `k/M < 0`. -/
def Model.Unstable (m : Model) : Prop :=
  m.V ≠ 0 ∧ m.Balanced ∧ (0 < m.b ∨ m.q.D / m.q.M < 0 ∨ m.q.k m.δ / m.q.M < 0)

/-- The VSM–DC family with the DC-voltage loop open. -/
def family : Family Model Spectral.Requirement 3 0 :=
  Spectral.localFamily Model.field Model.Stable Model.Unstable

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.q.openField m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.openField) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)

@[tmio M, powerlib_domain] private theorem point_mem (m : Model) (hV : m.V ≠ 0) :
    m.point ∈ nonzeroDC (2 : Fin 3) := by
  simpa [Model.point, nonzeroDC] using hV

@[tmio M, powerlib_domain] private theorem fderiv_point (m : Model) (hV : m.V ≠ 0) :
    fderiv ℝ m.q.openField m.point =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (m.q.openJacobian m.δ m.V) := by
  simpa [Model.point] using m.q.fderiv_openField (x := m.point) (by simpa [Model.point] using hV)

@[tmio M, powerlib_domain] private theorem field_point_of_balanced {m : Model}
    (hV : m.V ≠ 0) (hb : m.Balanced) : m.q.openField m.point = 0 := by
  apply state3_ext <;>
    simp [Model.point, Plant.openField, Plant.swingRate, hb.1, m.q.nodeRate_of_balance hV hb.2]

/-- **Open DC loop, local exponential stability.** At a balanced point with `V* ≠ 0`,
`0 < D/M`, `0 < k/M` and a stable DC node `b = I_s/(C V*) < 0`, the VSM–DC converter without
DC-voltage loop is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (h : m.Stable) : connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨hV, hb, hD, hk, hj⟩ := h
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  refine Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian_local (isOpen_nonzeroDC 2)
    (point_mem m hV) _ m.q.openField_contDiffOn (field_point_of_balanced hV hb) (fderiv_point m hV)
    ((m.q.isHurwitz_openJacobian_iff _ _).2 ⟨hD, hk, ?_⟩)
  rw [m.q.nodeSlope_of_balance hV hb.2]
  exact hj

/-- **Open DC loop, instability.** At a balanced point with `V* ≠ 0`, a DC node pole
`b = I_s/(C V*) > 0` (an eigenvalue with eigenvector `e_V`, whatever `M, D`), negative damping
`D/M < 0` or a saddle angle `k/M < 0` makes the converter unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (h : m.Unstable) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨hV, hb, hu⟩ := h
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  refine Dynamics.unstable_of_jacobian_eigenvalue_re_pos_local (isOpen_nonzeroDC 2)
    (point_mem m hV) _ m.q.openField_contDiffOn (field_point_of_balanced hV hb) (fderiv_point m hV)
    ?_
  have hj : m.q.nodeSlope m.δ m.V = m.b := m.q.nodeSlope_of_balance hV hb.2
  obtain ⟨s, hs, hre⟩ := Linear.exists_root_re_pos_of_extra_pole
    (m.q.det_characteristicMatrix_openJacobian m.δ m.V) (by
      rcases hu with hu | hu | hu
      · exact Or.inr (by rw [hj]; linarith)
      · refine Or.inl (Criteria.exists_root_re_pos_of_violation_fin_two _ (Or.inl ?_))
        simp [Plant.swingJacobian, Matrix.trace_fin_two, neg_div]
        linarith
      · refine Or.inl (Criteria.exists_root_re_pos_of_violation_fin_two _ (Or.inr ?_))
        simp [Plant.swingJacobian, Matrix.det_fin_two, neg_div]
        linarith)
  exact Criteria.exists_eigenpair_re_pos_of_characteristic_root _ hs hre

/-- Soundness of every translation of the open-loop family. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m h => ?_) (fun m h => ?_)
  · exact (Flow.Property.holds_shift_iff .locallyExponentiallyStable).mpr
      (mem_den_flow_iff.mp (mem_den_locallyExponentiallyStable m h))
  · exact (Flow.Property.holds_shift_iff .unstable).mpr
      (mem_den_flow_iff.mp (mem_den_unstable m h))

/-- **Open DC loop, exact local exponential stability.** With `V* ≠ 0`, the selected point is
locally exponentially stable iff it is balanced (`P_ff = P_e(δ*) = P_src(V*)`) with `0 < D/M`,
`0 < k/M` and `I_s/(C V*) < 0` (converse linearization for the field `C¹` on `V ≠ 0`,
`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hV : m.V ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.q.Pff = m.q.Pe m.δ ∧ m.q.Psrc m.V = m.q.Pe m.δ ∧ 0 < m.q.D / m.q.M ∧
        0 < m.q.k m.δ / m.q.M ∧ m.q.Is / (m.q.C * m.V) < 0) := by
  unfold TMIO.Statement
  constructor
  · intro h
    rw [mem_den_flow_iff] at h
    change LocallyExponentiallyStable _ _ at h
    rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local (isOpen_nonzeroDC 2)
      (point_mem m hV) _ m.q.openField_contDiffOn (fderiv_point m hV),
      Plant.isHurwitz_openJacobian_iff] at h
    obtain ⟨hf, hD, hk, hj⟩ := h
    have hM : m.q.M ≠ 0 := fun h0 => by simp [h0] at hk
    have hC : m.q.C ≠ 0 := fun h0 => by simp [Plant.nodeSlope, h0] at hj
    obtain ⟨-, h1, h2⟩ := (m.q.openField_eq_zero_iff hM hC (x := m.point)
      (by simpa [Model.point] using hV)).mp hf
    simp only [Model.point, mk3_zero, mk3_two] at h1 h2
    refine ⟨h1, h2, hD, hk, ?_⟩
    rw [← m.q.nodeSlope_of_balance hV h2]
    exact hj
  · rintro ⟨h1, h2, hD, hk, hj⟩
    exact mem_den_locallyExponentiallyStable m ⟨hV, ⟨h1, h2⟩, hD, hk, hj⟩

/-- Within `V* ≠ 0` the local exponential translation is exact: the generated space of the
stability condition is the locally exponentially stable models with `V* ≠ 0`. -/
@[tmio TM, powerlib_domain] theorem realize_eq_den_inter :
    connection% (TMIO.realize family.meets (family.translate (.flow .locallyExponentiallyStable)) =
      family.den (.flow .locallyExponentiallyStable) ∩ {m : Model | m.V ≠ 0}) :=
  Spectral.local_realize_eq_den_inter_of_iff (Or.inr (Or.inr rfl)) (fun m h => h.1)
    fun m hV => by
      have h := mem_den_locallyExponentiallyStable_iff m hV
      unfold TMIO.Statement at h
      show m.Stable ↔ m ∈ family.den (.flow .locallyExponentiallyStable)
      rw [h]
      exact ⟨fun ⟨_, hb, hD, hk, hj⟩ => ⟨hb.1, hb.2, hD, hk, hj⟩,
        fun ⟨h1, h2, hD, hk, hj⟩ => ⟨hV, ⟨h1, h2⟩, hD, hk, hj⟩⟩

/-- **Constant-current source, open DC loop.** With `P_s = 0`, `C > 0` and `V* ≠ 0`, the
selected point is locally exponentially stable iff it is balanced with `0 < D/M`, `0 < k/M` and
`P_e(δ*) < 0`: the converter must import power (rectifier operation), the sign obstruction of the
GFL cascade. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_constCurrent
    (m : Model) (hPs : m.q.Ps = 0) (hC : 0 < m.q.C) (hV : m.V ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.q.Pff = m.q.Pe m.δ ∧ m.q.Psrc m.V = m.q.Pe m.δ ∧ 0 < m.q.D / m.q.M ∧
        0 < m.q.k m.δ / m.q.M ∧ m.q.Pe m.δ < 0) := by
  have h := mem_den_locallyExponentiallyStable_iff m hV
  unfold TMIO.Statement at h ⊢
  rw [h]
  have key : m.q.Psrc m.V = m.q.Pe m.δ →
      (m.q.Is / (m.q.C * m.V) < 0 ↔ m.q.Pe m.δ < 0) := fun h2 => by
    have hP : m.q.Pe m.δ = m.q.Is * m.V := by rw [← h2, Plant.Psrc, hPs, zero_add]
    have hb : m.q.Is / (m.q.C * m.V) = m.q.Pe m.δ / (m.q.C * m.V ^ 2) := by
      rw [hP, sq, ← mul_assoc, mul_div_mul_right _ _ hV]
    rw [hb, div_lt_iff₀ (by positivity), zero_mul]
  exact ⟨fun ⟨h1, h2, hD, hk, hj⟩ => ⟨h1, h2, hD, hk, (key h2).1 hj⟩,
    fun ⟨h1, h2, hD, hk, hj⟩ => ⟨h1, h2, hD, hk, (key h2).2 hj⟩⟩

/-- **Constant-current source exporting power is unstable for every inertia and damping.** With
`P_s = 0`, `C > 0`, `V* ≠ 0`, a balanced point that exports power (`P_e(δ*) > 0`) has the DC node
pole `b = P₀/(C V*²) > 0` and is unstable, whatever `M` and `D` (GFM analog of the GFL
`mem_den_unstable_of_inverter`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_export (m : Model) (hPs : m.q.Ps = 0)
    (hC : 0 < m.q.C) (hV : m.V ≠ 0) (hb : m.Balanced) (hP : 0 < m.q.Pe m.δ) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable m ⟨hV, hb, Or.inl ?_⟩
  have hI : m.q.Pe m.δ = m.q.Is * m.V := by rw [← hb.2, Plant.Psrc, hPs, zero_add]
  have e : m.b = m.q.Pe m.δ / (m.q.C * m.V ^ 2) := by
    rw [Model.b, hI, sq, ← mul_assoc, mul_div_mul_right _ _ hV]
  rw [e]
  positivity

/-- **Constant-power source, open DC loop: never locally exponentially stable.** With `I_s = 0`
the DC node pole is `b = 0` (the balance `P_src = P_s` fixes no voltage: the equilibria form a
line in `V`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_constPower
    (m : Model) (hIs : m.q.Is = 0) (hV : m.V ≠ 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_iff m hV
  unfold TMIO.Statement at h ⊢
  rw [h, hIs, zero_div]
  exact fun h => lt_irrefl _ h.2.2.2.2

/-! ### Selected points on the singular plane `V* = 0` -/

/-- **Collapse onto the singular plane.** A selected point with `V* = 0` at which the DC node is
driven into the plane from both sides (`(P_s − P_e(δ*))/C < 0`: for a constant-current source
with `C > 0`, export `P_e(δ*) > 0`) and the source current crosses it (`I_s / C ≠ 0`) satisfies the
segment-based local exponential estimate although it is not an equilibrium: near it
`d(V²)/dt = 2 (I_s V + P_s − P_e(δ))/C` is bounded below zero, so solution segments end before
reaching the plane (generic `Dynamics.Degenerate.locallyExponentiallyStable_of_collapse`). The
estimate holds because solutions cease, not because they converge. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_collapse (m : Model)
    (hV : m.V = 0) (hP : (m.q.Ps - m.q.Pe m.δ) / m.q.C < 0) (hI : m.q.Is / m.q.C ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  set g : State 3 → ℝ := fun y => 2 * (m.q.Is * y 2 + m.q.Ps - m.q.Pe (y 0)) / m.q.C with hg
  have hgc : Continuous g := by
    simp only [hg, Plant.Pe]
    fun_prop
  have hx2 : m.point 2 = 0 := by simp [Model.point, hV]
  have hgx : g m.point = 2 * ((m.q.Ps - m.q.Pe m.δ) / m.q.C) := by
    simp only [hg, Model.point, mk3_zero, mk3_two, hV]
    ring
  set a := -(g m.point) / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuous_iff.mp hgc m.point a ha0
  obtain ⟨B, hB⟩ := (isCompact_closedBall m.point 1).exists_bound_of_continuousOn
    m.q.continuous_openField_sub_single.continuousOn
  refine Dynamics.Degenerate.locallyExponentiallyStable_of_collapse 2 hx2 (ρ := min ρ₁ 1) (a := a)
    (M := B) (lt_min hρ₁ one_pos) ha0 ?_ ?_ ?_
  · intro y hy hy2
    rw [show m.q.openField y 2 = m.q.nodeRate (y 0) (y 2) by simp [Plant.openField],
      m.q.two_mul_nodeRate hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_left _ _))
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    show g y ≤ -a
    linarith
  · intro y _ hy2
    simpa [Plant.openField, hy2, Plant.nodeRate_zero] using hI
  · intro y hy
    exact hB y (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (lt_of_lt_of_le hy (min_le_right _ _)).le)

/-- **Repulsion from the singular plane.** A selected point with `V* = 0` at which
`(P_s − P_e(δ*))/C > 0` (for a constant-current source with `C > 0`: import `P_e(δ*) < 0`) is
unstable: `V²` grows near it (generic `Dynamics.Degenerate.unstable_of_repel`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_repel (m : Model) (hV : m.V = 0)
    (hP : 0 < (m.q.Ps - m.q.Pe m.δ) / m.q.C) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  set g : State 3 → ℝ := fun y => 2 * (m.q.Is * y 2 + m.q.Ps - m.q.Pe (y 0)) / m.q.C with hg
  have hgc : Continuous g := by
    simp only [hg, Plant.Pe]
    fun_prop
  have hx2 : m.point 2 = 0 := by simp [Model.point, hV]
  have hgx : g m.point = 2 * ((m.q.Ps - m.q.Pe m.δ) / m.q.C) := by
    simp only [hg, Model.point, mk3_zero, mk3_two, hV]
    ring
  set a := g m.point / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.mp hgc m.point a ha0
  refine Dynamics.Degenerate.unstable_of_repel 2 hx2 hρ ha0 (fun y hy hy2 => ?_)
    (fun s hs => ?_)
  · rw [show m.q.openField y 2 = m.q.nodeRate (y 0) (y 2) by simp [Plant.openField],
      m.q.two_mul_nodeRate hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact hy)
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).1
    show a ≤ g y
    linarith
  · obtain ⟨g, hg, hgf⟩ := m.q.exists_contDiff_eq_openField_of_sign (Or.inl rfl) hs
    exact ⟨g, hg, fun y _ hy2 => hgf y (by rw [one_mul]; exact hy2)⟩

/-! ### The degenerate balance `P_s = P_e(δ*)` on the singular plane

With `q = (I_s V + P_s − P_e(δ))/C` (`Plant.planeQ`) the field satisfies, off the plane,
`V V̇ = q` and `q̇ = G + H q / V` with `G = −k(δ) ω / C` (`Plant.planeG`) and `H = I_s/C`; at a
selected point `(δ*, 0, 0)` the degenerate balance is `q = 0`, and `G = 0` because `ω* = 0`. In the
time `dτ = dt / V` the pair `(V, q)` is the linear system `[[0, 1], [G, H]]`, of discriminant
`H² + 4G = H² ≥ 0`: a node with the roots `0` and `H`, never a focus. -/

/-- **Degenerate balance, crossing source current: instability.** A selected point on the
singular plane (`V* = 0`) at which the source balances the exported power (`P_s = P_e(δ*)`) and
the source current crosses the plane (`H = I_s / C ≠ 0`) is unstable: on the side
`σ = sign H` the cone `{σ V > 0, q ≥ (|H|/2) σ V}` is entered by the field through its boundary,
where `dq/dt − (|H|/2) σ V̇ = G + H²/4 > 0` near the point, and in it `σ V̇ ≥ |H|/2`
(generic `Dynamics.Degenerate.unstable_of_cone`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_degenerate (m : Model) (hV : m.V = 0)
    (hP : m.q.Ps = m.q.Pe m.δ) (hI : m.q.Is / m.q.C ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  set H := m.q.Is / m.q.C with hH
  obtain ⟨σ, hσ, hσH⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * H = |H| := by
    by_cases h : 0 ≤ H
    · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg (not_le.mp h)]; ring⟩
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hHa : 0 < |H| := abs_pos.mpr hI
  set μ := |H| / 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hx0 : m.point 0 = m.δ := by simp [Model.point]
  have hx1 : m.point 1 = 0 := by simp [Model.point]
  have hx2 : m.point 2 = 0 := by simp [Model.point, hV]
  have hGx : m.q.planeG m.point = 0 := by simp [Plant.planeG, hx1]
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.mp m.q.contDiff_planeG.continuous m.point
    (μ ^ 2) (by positivity)
  set W : State 3 → ℝ := fun y => m.q.planeQ y - μ * σ * y 2 with hW
  have hWc : ContDiff ℝ 1 W :=
    m.q.contDiff_planeQ.sub (contDiff_const.mul (Dynamics.contDiff_coord 2))
  have hWd : ∀ y : State 3, HasFDerivAt W ((-m.q.k (y 0) / m.q.C) • Dynamics.coord 0 +
      (H - μ * σ) • Dynamics.coord 2) y := by
    intro y
    have h := (m.q.hasFDerivAt_planeQ y).sub
      ((Dynamics.hasFDerivAt_coord (2 : Fin 3) y).const_mul (μ * σ))
    refine h.congr_fderiv ?_
    ext v
    simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply, Dynamics.coord_apply,
      smul_eq_mul, hH]
    ring
  have hW0 : W m.point = 0 := by simp [hW, Plant.planeQ, hx0, hx2, hP]
  have hy2 : ∀ y : State 3, 0 < σ * y 2 → y 2 ≠ 0 := fun y hy h => by
    rw [h, mul_zero] at hy
    exact lt_irrefl _ hy
  refine Dynamics.Degenerate.unstable_of_cone 2 hσ hρ hμ0 hWc hx2 hW0 ?_ ?_
    (mk3 (-m.q.k m.δ / m.q.C) 0 σ) ?_ ?_ ?_
  · intro y _ hy hWy
    rw [m.q.openField_two_eq_planeQ_div (hy2 y hy)]
    have hq : μ * σ * y 2 ≤ m.q.planeQ y := by simp only [hW] at hWy; linarith
    have hσy : σ * (m.q.planeQ y / y 2) * (σ * y 2) = m.q.planeQ y := by
      field_simp [hy2 y hy]
      linear_combination m.q.planeQ y * hσ2
    have h1 : μ * (σ * y 2) ≤ σ * (m.q.planeQ y / y 2) * (σ * y 2) := by
      rw [hσy]; linarith
    exact le_of_mul_le_mul_right h1 hy
  · intro y hyx hy hWy
    rw [(hWd y).fderiv]
    have hq : m.q.planeQ y = μ * σ * y 2 := by simp only [hW] at hWy; linarith
    have hf2 : m.q.openField y 2 = μ * σ := by
      rw [m.q.openField_two_eq_planeQ_div (hy2 y hy), hq]
      field_simp [hy2 y hy]
    have hrate := hball y (by rw [dist_eq_norm]; exact hyx)
    rw [Real.dist_eq, hGx, sub_zero] at hrate
    have hrate' := (abs_lt.mp hrate).1
    have hlie : ((-m.q.k (y 0) / m.q.C) • Dynamics.coord 0 + (H - μ * σ) • Dynamics.coord 2 :
        State 3 →L[ℝ] ℝ) (m.q.openField y) = m.q.planeG y + μ ^ 2 := by
      simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul, hf2]
      have h0 : m.q.openField y 0 = y 1 := by simp [Plant.openField]
      rw [h0, Plant.planeG]
      have : H * σ = 2 * μ := by rw [mul_comm, hσH, hμ]; ring
      linear_combination μ * this - μ ^ 2 * hσ2
    rw [hlie]
    linarith
  · simp [hσ2]
  · rw [(hWd m.point).fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul, mk3_zero,
      mk3_two, hx0]
    have : (H - μ * σ) * σ = |H| / 2 := by
      rw [sub_mul, mul_assoc, hσ2, mul_comm, hσH, hμ]; ring
    rw [this]
    nlinarith [sq_nonneg (-m.q.k m.δ / m.q.C)]
  · intro s hs
    obtain ⟨g, hg, hgf⟩ := m.q.exists_contDiff_eq_openField_of_sign hσ hs
    exact ⟨g, hg, fun y _ hy => hgf y hy⟩

/-- **Degenerate balance with a drifting swing: no local exponential estimate.** A selected point
on the singular plane with `P_s = P_e(δ*)`, a source current that does not cross the plane
(`I_s / C = 0`, so `H = G = 0`: the reduced system is nilpotent) and an unbalanced swing
(`(P_ff − P_e(δ*))/M ≠ 0`, a nonzero drift of `ω`) is not locally exponentially stable
(generic `Dynamics.Degenerate.not_locallyExponentiallyStable_of_nilpotent`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_degenerate_of_drift
    (m : Model) (hV : m.V = 0) (hP : m.q.Ps = m.q.Pe m.δ) (hI : m.q.Is / m.q.C = 0)
    (hw : (m.q.Pff - m.q.Pe m.δ) / m.q.M ≠ 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hx2 : m.point 2 = 0 := by simp [Model.point, hV]
  refine Dynamics.Degenerate.not_locallyExponentiallyStable_of_nilpotent 2 hx2
    m.q.contDiff_planeQ (by simp [Plant.planeQ, Model.point, hV, hP]) m.q.contDiff_planeG
    (h := fun _ => m.q.Is / m.q.C) contDiff_const (by simp [Plant.planeG, Model.point]) hI
    one_pos (fun y _ hy => ?_) (fun y _ hy => m.q.planeQ_lie hy) (fun y => ?_)
    m.q.continuous_openField_sub_single.continuousAt ?_ (fun s hs => ?_)
  · rw [m.q.openField_two_eq_planeQ_div hy]
    field_simp
  · rw [(m.q.hasFDerivAt_planeQ y).fderiv]
    simp
  · rw [m.q.openField_sub_single]
    intro h0
    have h1 := congrArg (fun v : State 3 => v 1) h0
    simp [Model.point, Plant.swingRate] at h1
    exact hw (div_eq_zero_iff.mpr h1)
  · obtain ⟨g, hg, hgf⟩ := m.q.exists_contDiff_eq_openField_of_sign (Or.inl rfl) hs
    exact ⟨g, hg, fun y _ hy => hgf y (by rw [one_mul]; exact hy)⟩

/-- **Degenerate balance at rest: not locally asymptotically stable.** A selected point on the
singular plane with `P_s = P_e(δ*)`, `I_s / C = 0` and a balanced swing
(`(P_ff − P_e(δ*))/M = 0`) is an equilibrium, and so is every `(δ*, 0, V)`: the DC node is at
rest along the whole line (`Dynamics.not_localAsymptoticStable_of_line`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_degenerate_of_rest
    (m : Model) (hV : m.V = 0) (hP : m.q.Ps = m.q.Pe m.δ) (hI : m.q.Is / m.q.C = 0)
    (hw : (m.q.Pff - m.q.Pe m.δ) / m.q.M = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  refine Dynamics.not_localAsymptoticStable_of_line (v := EuclideanSpace.single 2 1) ?_
    fun t _ => ?_
  · intro h
    have := congrArg (fun v : State 3 => v 2) h
    simp at this
  · apply state3_ext <;>
      simp [Plant.openField, Plant.swingRate, Plant.nodeRate, GFL.DCLink.nodeRate, Model.point,
        hV, hP, hw, hI]

/-- **The degenerate balance on the singular plane is never locally exponentially stable.** With
`V* = 0` and `P_s = P_e(δ*)`: if `I_s / C ≠ 0` the point is unstable
(`mem_den_unstable_of_degenerate`); if `I_s / C = 0` it is not locally exponentially stable,
by the drift of an unbalanced swing
(`not_mem_den_locallyExponentiallyStable_of_degenerate_of_drift`) or the line of equilibria of a
balanced one (`not_mem_den_locallyAsymptoticallyStable_of_degenerate_of_rest`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_degenerate
    (m : Model) (hV : m.V = 0) (hP : m.q.Ps = m.q.Pe m.δ) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  intro hm
  by_cases hI : m.q.Is / m.q.C = 0
  · by_cases hw : (m.q.Pff - m.q.Pe m.δ) / m.q.M = 0
    · have h := not_mem_den_locallyAsymptoticallyStable_of_degenerate_of_rest m hV hP hI hw
      unfold TMIO.Statement at h
      exact h (Spectral.den_locallyExponentiallyStable_subset_las hm)
    · have h := not_mem_den_locallyExponentiallyStable_of_degenerate_of_drift m hV hP hI hw
      unfold TMIO.Statement at h
      exact h hm
  · have h := mem_den_unstable_of_degenerate m hV hP hI
    unfold TMIO.Statement at h
    exact (mem_den_flow_iff.mp h) (mem_den_flow_iff.mp hm).lyapunovStable

/-- **Local exponential stability on the singular plane, crossing source current.** For a
selected point with `V* = 0` and `I_s / C ≠ 0`, the segment-based local exponential estimate
holds exactly when the power term drives `V` into the plane, `(P_s − P_e(δ*))/C < 0`
(`mem_den_locallyExponentiallyStable_of_collapse`; `> 0` repels, `mem_den_unstable_of_repel`;
`= 0` is the degenerate balance, `not_mem_den_locallyExponentiallyStable_of_degenerate`). Such a
point is never an equilibrium. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_V_eq_zero
    (m : Model) (hV : m.V = 0) (hI : m.q.Is / m.q.C ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      (m.q.Ps - m.q.Pe m.δ) / m.q.C < 0) := by
  have hC : m.q.C ≠ 0 := fun h => hI (by rw [h, div_zero])
  have hcol := mem_den_locallyExponentiallyStable_of_collapse m hV
  have hdeg := not_mem_den_locallyExponentiallyStable_of_degenerate m hV
  unfold TMIO.Statement at hcol hdeg ⊢
  refine ⟨fun hm => ?_, fun h => hcol h hI⟩
  rcases lt_trichotomy ((m.q.Ps - m.q.Pe m.δ) / m.q.C) 0 with h | h | h
  · exact h
  · rw [div_eq_zero_iff, or_iff_left hC, sub_eq_zero] at h
    exact absurd hm (hdeg h)
  · have hr := mem_den_unstable_of_repel m hV h
    unfold TMIO.Statement at hr
    exact absurd (mem_den_flow_iff.mp hm).lyapunovStable (mem_den_flow_iff.mp hr)

end OpenLoop

end powerlib.GFM.DCLink
