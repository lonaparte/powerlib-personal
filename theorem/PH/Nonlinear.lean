import dependencies.Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import theorem.Dynamics.State
import theorem.Family.Basic
import theorem.Dynamics.Shift

/-! # Nonlinear port-Hamiltonian systems

Nonlinear input-state-output port-Hamiltonian systems with a general, not necessarily quadratic,
Hamiltonian, read in the Port semantics of the library (`theorem/Port/Defs.lean`); the generic
framework on which concrete pH families are built.

Scope.
* State: `x : State n = EuclideanSpace ℝ (Fin n)`, the state space of the Flow and Port
  semantics. The order and physical meaning of the coordinates is fixed by each concrete
  instance; this module is coordinate-agnostic.
* Input: `u : Fin m → ℝ`, an arbitrary (possibly time-varying) port effort.
  Output: `y = g(x)ᵀ ∇H(x)`, the collocated conjugate flow.
* Dynamics, continuous time: `ẋ = (J(x) − R(x)) ∇H(x) + g(x) u`.
  `J(x)` is pointwise skew-symmetric, `R(x)` is pointwise symmetric positive semidefinite
  (`Matrix.PosSemidef`), `g(x)` is an arbitrary `n × m` input matrix.
  No continuity of `J`, `R`, `g` in `x` is assumed by the pointwise and trajectory results.
* Hamiltonian: `H : State n → ℝ` is differentiable everywhere with the explicitly
  supplied gradient field `dH` (`HasGradientAt H (dH x) x`). `H` may be non-quadratic and
  is **not** assumed bounded below or nonnegative. Passivity is stated only under an explicit
  lower bound, with the storage shifted by that constant so that it is nonnegative, as the Port
  semantics requires (`Port.System.PassiveWith`).
* Power sign: the supply rate `uᵀ y` is the power delivered *into* the system through the
  port (incoming-positive, matching work-sync `conventions.md` §D). `∇Hᵀ R ∇H ≥ 0` is
  the internally dissipated power.
* Excluded: implicit / Dirac-structure pH, pH-DAE algebraic constraints, interconnection
  theorems, PBC / IDA-PBC, shifted passivity about a forced equilibrium, LaSalle invariance,
  delay, PWM, PLL, saturation, and any discretization. Stability results are equilibrium-level
  (Lyapunov stability of a strict local minimum of `H` under zero input).

Source: work-sync `theory/T-ph.md` §1.1 (form (1.1), structure assumptions 1–2, 4),
§1.2 (power balance (1.2), integral balance (1.3), passivity (1.4), zero-input corollary);
`theory/T-grid-disturbance.md` (1.1), §1.5 (1.2) (disturbance channels).

Results (generic foundation for every nonlinear pH system).
* Power balance (1.2) and its integral (1.3) (`power_balance`, `integral_power_balance`,
  `trajectory_energy_derivative`), the dissipation inequality (`dissipation_inequality`,
  `integral_dissipation`) and the zero-input corollary (`zeroInput_power_balance`,
  `zeroInput_energy_antitone`), along the finite solution segments of the Port semantics
  (`Port.System.IsTrajectoryOn`).
* Passivity with storage `H − c` under a lower bound `c ≤ H` (`passiveWith_sub`,
  `passive_of_bddBelow`); Lyapunov stability of a strict local minimum of `H` under zero input
  (`IsStrictLocalMin.lyapunovStable`).
* Shift to an operating point (`shift`, `shift_field`, `shift_H`, `holds_flow_shift_iff`,
  `holds_passive_shift`, `isStrictLocalMin_shift_iff`).
* Deterministic disturbance channels (`gridDisturbance_field`, `gridDisturbance_power_balance`):
  a nonlinear pH model driven by its own control port `u_S` and three further deterministic
  input channels, a constant frequency channel `B_ω u_ω`, a state-dependent voltage channel
  `B_v(x) u_v` and a constant channel `B_T u_T` (T-grid-disturbance (1.1)). Result: the
  pointwise energy balance (T-grid-disturbance §1.5 (1.2)) split by channel,
  `Ḣ = −∇Hᵀ R ∇H + y_Sᵀ u_S + y_ωᵀ u_ω + y_vᵀ u_v + y_Tᵀ u_T`, `y_k = B_kᵀ ∇H`; no noise (the
  σ → 0 limit of the note), no Itô correction. A static identity for every nonlinear pH model;
  the linear diagonal special case of (1.2) is `powerlib.PH.DiagonalPH.power_balance`.

Family and connection conclusions.
* `NonlinearModel` is a generic framework — the class of all nonlinear pH systems — not a model
  family. Its system map `NonlinearModel.system : Port.System n m` (state dynamics `field`,
  output `y = g(x)ᵀ ∇H(x)`, supply `uᵀ y`) reads it in the Port semantics, and the theorems here
  are generic implications for every pH system, hence foundation results (Rules §3, port
  policy §4).
* Downstream concrete models (GFL, PLL, VSC, synchronous machines, …) build their own `Family`
  on this framework and publish connection statements; **no `Family` may take
  `NonlinearModel n m` itself as its model type**, since admission would then treat every
  generic theorem here as model-specific. The pattern is:
  1. a structure `Model` (parameters, a selected operating point `point`, smoothness), and a map
     `toPH : Model → NonlinearModel n m`;
  2. `family : Family Model Requirement n m` with system map
     `fun m => ((toPH m).shift m.point).system` — the pH system in coordinates centred at the
     operating point, because the library reads flow sentences at the origin
     (`Sentence.holds (.flow P) s = P.holds s.zeroInput 0`); without an operating point use
     `(toPH m).system`;
  3. `Family.IsNonlinearPH family (fun m => (toPH m).shift m.point)` holds by `fun _ => rfl`;
  4. connection conclusions from the generic theorems:
     * passivity — `connection% (m ∈ family.den .passive)` by
       `hF.mem_den_passive (bddBelow_range_shift_H.mpr hH)` or
       `hF.mem_den_passive_of_lowerBound c hc` (a lower bound on the Hamiltonian; the `.passive`
       sentence is translation-invariant, so the bound may be stated on `toPH m` itself);
     * Lyapunov stability — `connection% (m ∈ family.den (.flow .lyapunovStable))` by
       `hF.mem_den_lyapunovStable_shift h` with `h : (toPH m).IsStrictLocalMin m.point`;
     * any other flow sentence — `hF.mem_den_flow_shift` reduces `m ∈ family.den (.flow P)` to
       `P.holds (toPH m).zeroInputField m.point`, the operating point of the untranslated
       field;
     * refutation of passivity — `Port.System.not_passive_of_equilibrium` /
       `Port.System.not_passive_of_cycle` on `(toPH m).system`, published as
       `connection% (m ∉ family.den .passive)`.

Correction.
* §1.0/§1.1 list `H ≥ H_min > −∞` as a structural assumption. It is not needed for (1.2), (1.3),
  the dissipation inequality, or Lyapunov stability; it is used here only for the passivity
  statement (1.4), where the storage is `H − H_min`. The §1.2 corollary claim "global asymptotic
  stability by LaSalle" is not formalized here (LaSalle is out of scope).
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
open powerlib.Dynamics (State)

variable {n m : ℕ}

/-- The Euclidean inner product written as a dot product of coordinate vectors. -/
@[tmio T, powerlib_foundation] theorem inner_eq_dotProduct (x y : State n) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- A skew-symmetric matrix does no work: `vᵀ J v = 0`. -/
@[powerlib_foundation] theorem dotProduct_mulVec_self_eq_zero_of_skew
    {ι : Type*} [Fintype ι] {J : Matrix ι ι ℝ} (hJ : Jᵀ = -J) (v : ι → ℝ) :
    v ⬝ᵥ (J *ᵥ v) = 0 := by
  have h : v ⬝ᵥ (J *ᵥ v) = -(v ⬝ᵥ (J *ᵥ v)) := by
    calc v ⬝ᵥ (J *ᵥ v) = (Jᵀ *ᵥ v) ⬝ᵥ v := by rw [dotProduct_mulVec, mulVec_transpose]
      _ = -(v ⬝ᵥ (J *ᵥ v)) := by rw [hJ, neg_mulVec, neg_dotProduct, dotProduct_comm]
  linarith

/-- The planar symplectic matrix `[[0, 1], [−1, 0]]` is skew-symmetric. -/
@[powerlib_foundation] theorem transpose_symplectic_two :
    (!![(0 : ℝ), 1; -1, 0])ᵀ = -!![(0 : ℝ), 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Builds a gradient from a Fréchet derivative given in dot-product form. -/
@[powerlib_foundation] theorem hasGradientAt_of_hasFDerivAt {H : State n → ℝ}
    {L : State n →L[ℝ] ℝ} {x d : State n} (hH : HasFDerivAt H L x)
    (hL : ∀ v, L v = WithLp.ofLp d ⬝ᵥ WithLp.ofLp v) : HasGradientAt H d x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hH using 1
  ext v
  rw [InnerProductSpace.toDual_apply_apply, hL, inner_eq_dotProduct]

/-- A nonlinear input-state-output port-Hamiltonian system on `ℝⁿ` with `m` ports.
`dH` is the explicitly supplied gradient of `H`. -/
structure NonlinearModel (n m : ℕ) where
  /-- Interconnection matrix, pointwise skew-symmetric. -/
  J : State n → Matrix (Fin n) (Fin n) ℝ
  /-- Dissipation matrix, pointwise symmetric positive semidefinite. -/
  R : State n → Matrix (Fin n) (Fin n) ℝ
  /-- Port input matrix. -/
  g : State n → Matrix (Fin n) (Fin m) ℝ
  /-- Hamiltonian (stored energy); no lower bound is assumed. -/
  H : State n → ℝ
  /-- Gradient (co-energy) field of `H`. -/
  dH : State n → State n
  skew : ∀ x, (J x)ᵀ = -J x
  dissipation_posSemidef : ∀ x, (R x).PosSemidef
  hasGradient : ∀ x, HasGradientAt H (dH x) x

namespace NonlinearModel

variable (M : NonlinearModel n m)

/-- The vector field `(J(x) − R(x)) ∇H(x) + g(x) u`. -/
def field (x : State n) (u : Fin m → ℝ) : State n :=
  WithLp.toLp 2 ((M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x) + M.g x *ᵥ u)

/-- The collocated output `y = g(x)ᵀ ∇H(x)`. -/
def output (x : State n) : Fin m → ℝ :=
  (M.g x)ᵀ *ᵥ WithLp.ofLp (M.dH x)

/-- Port power `uᵀ y`, positive when power flows into the system. -/
def supply (x : State n) (u : Fin m → ℝ) : ℝ :=
  u ⬝ᵥ M.output x

/-- Internally dissipated power `∇Hᵀ R ∇H`. -/
def dampingPower (x : State n) : ℝ :=
  WithLp.ofLp (M.dH x) ⬝ᵥ (M.R x *ᵥ WithLp.ofLp (M.dH x))

/-- The autonomous zero-input field `(J(x) − R(x)) ∇H(x)`. -/
def zeroInputField (x : State n) : State n :=
  M.field x 0

@[simp, powerlib_foundation] theorem ofLp_field (x : State n) (u : Fin m → ℝ) :
    WithLp.ofLp (M.field x u) =
      (M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x) + M.g x *ᵥ u := rfl

@[simp, powerlib_foundation] theorem zeroInputField_apply (x : State n) :
    M.zeroInputField x = WithLp.toLp 2 ((M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x)) := by
  simp [zeroInputField, field]

@[powerlib_foundation] theorem hasFDerivAt_H (x : State n) :
    HasFDerivAt M.H (InnerProductSpace.toDual ℝ (State n) (M.dH x)) x :=
  (M.hasGradient x).hasFDerivAt

@[powerlib_foundation] theorem gradient_H (x : State n) : gradient M.H x = M.dH x :=
  (M.hasGradient x).gradient

@[powerlib_foundation] theorem differentiable_H : Differentiable ℝ M.H :=
  fun x => (M.hasFDerivAt_H x).differentiableAt

@[powerlib_foundation] theorem continuous_H : Continuous M.H :=
  M.differentiable_H.continuous

@[powerlib_foundation] theorem fderiv_H_apply (x v : State n) :
    fderiv ℝ M.H x v = WithLp.ofLp (M.dH x) ⬝ᵥ WithLp.ofLp v := by
  rw [(M.hasFDerivAt_H x).fderiv, InnerProductSpace.toDual_apply_apply, inner_eq_dotProduct]

@[powerlib_foundation] theorem dampingPower_nonneg (x : State n) : 0 ≤ M.dampingPower x := by
  simpa [dampingPower, star_trivial] using
    (M.dissipation_posSemidef x).dotProduct_mulVec_nonneg (WithLp.ofLp (M.dH x))

@[powerlib_foundation] theorem gradient_dotProduct_input (x : State n) (u : Fin m → ℝ) :
    WithLp.ofLp (M.dH x) ⬝ᵥ (M.g x *ᵥ u) = M.supply x u := by
  rw [supply, output, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- Power balance (T-ph (1.2)): `Ḣ = uᵀ y − ∇Hᵀ R ∇H` at every state and input. -/
@[powerlib_foundation] theorem power_balance (x : State n) (u : Fin m → ℝ) :
    fderiv ℝ M.H x (M.field x u) = M.supply x u - M.dampingPower x := by
  rw [M.fderiv_H_apply, ofLp_field, sub_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_mulVec_self_eq_zero_of_skew (M.skew x), gradient_dotProduct_input, dampingPower]
  ring

/-- Dissipation inequality: `Ḣ ≤ uᵀ y`. -/
@[powerlib_foundation] theorem dissipation_inequality (x : State n) (u : Fin m → ℝ) :
    fderiv ℝ M.H x (M.field x u) ≤ M.supply x u := by
  rw [M.power_balance]
  linarith [M.dampingPower_nonneg x]

/-- Zero-input energy balance: `Ḣ = −∇Hᵀ R ∇H`. -/
@[powerlib_foundation] theorem zeroInput_power_balance (x : State n) :
    fderiv ℝ M.H x (M.zeroInputField x) = -M.dampingPower x := by
  simpa [zeroInputField, supply] using M.power_balance x 0

/-- Zero-input energy is nonincreasing: `Ḣ ≤ 0`. -/
@[powerlib_foundation] theorem zeroInput_lie_nonpos (x : State n) :
    fderiv ℝ M.H x (M.zeroInputField x) ≤ 0 := by
  rw [M.zeroInput_power_balance]
  linarith [M.dampingPower_nonneg x]

/-! ### The port system -/

/-- The system map: the pH system read as a system with `m` ports, input `u` and collocated
output `y = g(x)ᵀ ∇H(x)`. -/
def system : Port.System n m :=
  ⟨M.field, fun x _ => M.output x⟩

@[simp, powerlib_foundation] theorem system_field (x : State n) (u : Fin m → ℝ) :
    M.system.field x u = M.field x u := rfl

@[simp, powerlib_foundation] theorem system_output (x : State n) (u : Fin m → ℝ) :
    M.system.output x u = M.output x := rfl

@[simp, powerlib_foundation] theorem system_supply (x : State n) (u : Fin m → ℝ) :
    M.system.supply x u = M.supply x u := rfl

/-- With the ports at zero, the port system is the zero-input field. -/
@[simp, powerlib_foundation] theorem system_zeroInput : M.system.zeroInput = M.zeroInputField :=
  rfl

/-! ### Energy along solutions -/

/-- Along every solution under an input signal, on any time set,
`d/dt H(x(t)) = uᵀ y − ∇Hᵀ R ∇H`. -/
@[powerlib_foundation] theorem trajectory_energy_derivative
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → State n} {s : Set ℝ}
    (hx : IsIntegralCurveOn x (fun t y => M.field y (u t)) s) {t : ℝ} (ht : t ∈ s) :
    HasDerivWithinAt (fun τ => M.H (x τ))
      (M.supply (x t) (u t) - M.dampingPower (x t)) s t := by
  rw [← M.power_balance]
  exact (M.differentiable_H (x t)).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)

/-- Integral energy balance (T-ph (1.3)) on every solution segment:
`H(x(t₁)) − H(x(t₀)) = ∫_{t₀}^{t₁} (uᵀ y − ∇Hᵀ R ∇H)`. -/
@[powerlib_foundation] theorem integral_power_balance
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → State n} {t₀ t₁ : ℝ}
    (hx : M.system.IsTrajectoryOn u x t₀ t₁) (hle : t₀ ≤ t₁)
    (hint : IntervalIntegrable
      (fun τ => M.supply (x τ) (u τ) - M.dampingPower (x τ)) volume t₀ t₁) :
    M.H (x t₁) - M.H (x t₀) =
      ∫ τ in t₀..t₁, (M.supply (x τ) (u τ) - M.dampingPower (x τ)) := by
  have hd := fun τ (hτ : τ ∈ Icc t₀ t₁) => M.trajectory_energy_derivative hx hτ
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hle
    (fun τ hτ => (hd τ hτ).continuousWithinAt)
    (fun τ hτ => ((hd τ (Ioo_subset_Icc_self hτ)).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)).hasDerivWithinAt)
    hint]

/-- Integral dissipation inequality on every solution segment:
`H(x(t₁)) − H(x(t₀)) ≤ ∫_{t₀}^{t₁} uᵀ y`, with no sign condition on `H`. -/
@[powerlib_foundation] theorem integral_dissipation
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → State n} {t₀ t₁ : ℝ}
    (hx : M.system.IsTrajectoryOn u x t₀ t₁) (hle : t₀ ≤ t₁)
    (hsupply : IntervalIntegrable (fun τ => M.supply (x τ) (u τ)) volume t₀ t₁) :
    M.H (x t₁) - M.H (x t₀) ≤ ∫ τ in t₀..t₁, M.supply (x τ) (u τ) := by
  have hd : ∀ τ ∈ Icc t₀ t₁, HasDerivWithinAt (fun τ => M.H (x τ))
      (fderiv ℝ M.H (x τ) (M.field (x τ) (u τ))) (Icc t₀ t₁) τ := fun τ hτ =>
    (M.differentiable_H (x τ)).hasFDerivAt.comp_hasDerivWithinAt τ (hx τ hτ)
  apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hle
    (fun τ hτ => (hd τ hτ).continuousWithinAt)
    (fun τ hτ => ((hd τ (Ioo_subset_Icc_self hτ)).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hsupply)
  intro τ _
  exact M.dissipation_inequality (x τ) (u τ)

/-- Under zero input the Hamiltonian is antitone along every solution on a convex time set. -/
@[powerlib_foundation] theorem energy_antitoneOn_of_isIntegralCurveOn {φ : ℝ → State n}
    {s : Set ℝ} (hs : Convex ℝ s) (hφ : IsIntegralCurveOn φ (fun _ x => M.zeroInputField x) s) :
    AntitoneOn (M.H ∘ φ) s :=
  antitoneOn_V_comp_traj M.differentiable_H M.continuous_H hs hφ
    (fun t _ => M.zeroInput_lie_nonpos (φ t))

/-- Under zero input the Hamiltonian is antitone along every forward solution. -/
@[powerlib_foundation] theorem zeroInput_energy_antitone {x : ℝ → State n} {t₀ : ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => M.zeroInputField y) (Ici t₀)) :
    AntitoneOn (fun t => M.H (x t)) (Ici t₀) :=
  M.energy_antitoneOn_of_isIntegralCurveOn (convex_Ici t₀) hx

/-- Under zero input the Hamiltonian is antitone along every finite solution segment of the
zero-input field. -/
@[powerlib_foundation] theorem energy_antitoneOn_of_isTrajectoryOn {φ : ℝ → State n} {a b : ℝ}
    (hφ : IsTrajectoryOn φ M.zeroInputField a b) :
    AntitoneOn (M.H ∘ φ) (Icc a b) :=
  M.energy_antitoneOn_of_isIntegralCurveOn (convex_Icc a b) hφ

/-! ### Passivity -/

/-- Passivity with the nonnegative storage `H − c` when `H` is bounded below by `c`
(T-ph (1.4)). -/
@[powerlib_foundation] theorem passiveWith_sub {c : ℝ} (hH : ∀ x, c ≤ M.H x) :
    M.system.PassiveWith (fun x => M.H x - c) :=
  M.system.passiveWith_of_rate _ (fun x => sub_nonneg.mpr (hH x))
    (fun x u => fderiv ℝ M.H x (M.field x u))
    (fun _ x _ _ t hx ht =>
      ((M.differentiable_H (x t)).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)).sub_const c)
    (fun x u => M.dissipation_inequality x u)

/-- Passivity with storage `H` when `H` is nonnegative. -/
@[powerlib_foundation] theorem passiveWith (hH : ∀ x, 0 ≤ M.H x) : M.system.PassiveWith M.H := by
  simpa using M.passiveWith_sub hH

/-- A Hamiltonian bounded below makes the pH system passive. -/
@[powerlib_foundation] theorem passive_of_bddBelow (hH : BddBelow (range M.H)) :
    M.system.Passive := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨_, M.passiveWith_sub fun x => hc (mem_range_self x)⟩

/-- The passivity sentence of the library holds for a pH system whose Hamiltonian is bounded
below. -/
@[powerlib_foundation] theorem holds_passive (hH : BddBelow (range M.H)) :
    Sentence.passive.holds (.continuous M.system) :=
  M.passive_of_bddBelow hH

/-! ### Equilibria and Lyapunov stability at a strict minimum of `H` -/

/-- At a local minimum of `H` the gradient vanishes. -/
@[powerlib_foundation] theorem dH_eq_zero_of_isLocalMin {xs : State n}
    (h : IsLocalMin M.H xs) : M.dH xs = 0 := by
  have h0 := h.hasFDerivAt_eq_zero (M.hasFDerivAt_H xs)
  exact (InnerProductSpace.toDual ℝ (State n)).injective (by rw [h0, map_zero])

/-- A point with vanishing gradient is an equilibrium of the zero-input field. -/
@[powerlib_foundation] theorem zeroInputField_eq_zero_of_dH_eq_zero {xs : State n}
    (h : M.dH xs = 0) : M.zeroInputField xs = 0 := by
  rw [zeroInputField_apply, h, WithLp.ofLp_zero, mulVec_zero, WithLp.toLp_zero]

/-- A strict local minimum: `H x* < H x` for all `x ≠ x*` near `x*`. -/
def IsStrictLocalMin (M : NonlinearModel n m) (xs : State n) : Prop :=
  ∀ᶠ x in 𝓝[≠] xs, M.H xs < M.H x

@[powerlib_foundation] theorem IsStrictLocalMin.isLocalMin {xs : State n}
    (h : M.IsStrictLocalMin xs) : IsLocalMin M.H xs := by
  have h' := eventually_nhdsWithin_iff.mp h
  filter_upwards [h'] with x hx
  by_cases hxs : x = xs
  · rw [hxs]
  · exact (hx hxs).le

@[powerlib_foundation] theorem IsStrictLocalMin.exists_open {xs : State n}
    (h : M.IsStrictLocalMin xs) :
    ∃ D : Set (State n), IsOpen D ∧ xs ∈ D ∧ ∀ x ∈ D, x ≠ xs → M.H xs < M.H x := by
  obtain ⟨D, hD, hDopen, hxs⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
  exact ⟨D, hDopen, hxs, fun x hx hne => hD x hx hne⟩

/-- A strict local minimum of `H` is an equilibrium of the zero-input field. -/
@[powerlib_foundation] theorem IsStrictLocalMin.isEquilibrium {xs : State n}
    (h : M.IsStrictLocalMin xs) : IsEquilibrium M.zeroInputField xs :=
  M.zeroInputField_eq_zero_of_dH_eq_zero (M.dH_eq_zero_of_isLocalMin h.isLocalMin)

/-- `H − H(x*)` is a local Lyapunov function of the zero-input field at a strict local
minimum `x*` of `H`. -/
@[powerlib_foundation] theorem IsStrictLocalMin.exists_isLocalLyapunovFunction {xs : State n}
    (h : M.IsStrictLocalMin xs) :
    ∃ D : Set (State n), IsLocalLyapunovFunction M.zeroInputField
      (fun x => M.H x - M.H xs) xs D := by
  obtain ⟨D, hDopen, hxs, hD⟩ := h.exists_open
  exact ⟨D,
    { hD_open := hDopen
      hD_mem := hxs
      hcont := M.continuous_H.sub continuous_const
      hV_diff := M.differentiable_H.sub_const _
      hzero := sub_self _
      hpos := fun x hx hne => sub_pos.mpr (hD x hx hne)
      hLie_nonpos := fun x _ => by
        rw [fderiv_sub_const]
        exact M.zeroInput_lie_nonpos x }⟩

/-- Lyapunov stability of a strict local minimum of the Hamiltonian under zero input
(T-ph §1.2 corollary, stability part). No lower bound on `H`, no strict damping,
and no hypothesis on `∇H(x*)` is needed; `∇H(x*) = 0` is derived. -/
@[powerlib_foundation] theorem IsStrictLocalMin.lyapunovStable {xs : State n}
    (h : M.IsStrictLocalMin xs) : LyapunovStable M.zeroInputField xs := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro ε hε
    refine ⟨1, one_pos, fun t₀ t₁ φ _ _ t _ => ?_⟩
    rw [Subsingleton.elim (φ t) xs, sub_self, norm_zero]
    exact hε
  · obtain ⟨D, hV⟩ := h.exists_isLocalLyapunovFunction
    exact lyapunov_stable hn hV

/-- Equilibrium and Lyapunov stability of a strict local minimum of `H` under zero input. -/
@[powerlib_foundation] theorem IsStrictLocalMin.isEquilibrium_and_lyapunovStable {xs : State n}
    (h : M.IsStrictLocalMin xs) :
    IsEquilibrium M.zeroInputField xs ∧ LyapunovStable M.zeroInputField xs :=
  ⟨h.isEquilibrium, h.lyapunovStable⟩

/-! ### Coordinates centred at an operating point

The library reads flow sentences at the origin. `M.shift xs` is the same pH system in the
coordinates `z = x − xs`: every structure matrix and the Hamiltonian are composed with the
translation `z ↦ z + xs`, and the ports are unchanged. -/

/-- The pH system in the coordinates `z = x − xs`. -/
def shift (xs : State n) : NonlinearModel n m where
  J z := M.J (z + xs)
  R z := M.R (z + xs)
  g z := M.g (z + xs)
  H z := M.H (z + xs)
  dH z := M.dH (z + xs)
  skew z := M.skew (z + xs)
  dissipation_posSemidef z := M.dissipation_posSemidef (z + xs)
  hasGradient z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have h := (M.hasFDerivAt_H (z + xs)).comp z ((hasFDerivAt_id z).add_const xs)
    rwa [ContinuousLinearMap.comp_id] at h

@[simp, powerlib_foundation] theorem shift_H (xs z : State n) : (M.shift xs).H z = M.H (z + xs) :=
  rfl

@[simp, powerlib_foundation] theorem shift_field (xs z : State n) (u : Fin m → ℝ) :
    (M.shift xs).field z u = M.field (z + xs) u := rfl

@[simp, powerlib_foundation] theorem shift_output (xs z : State n) :
    (M.shift xs).output z = M.output (z + xs) := rfl

@[simp, powerlib_foundation] theorem shift_supply (xs z : State n) (u : Fin m → ℝ) :
    (M.shift xs).supply z u = M.supply (z + xs) u := rfl

@[powerlib_foundation] theorem shift_zeroInputField (xs : State n) :
    (M.shift xs).zeroInputField = fun z => M.zeroInputField (z + xs) := rfl

@[simp, powerlib_foundation] theorem range_shift_H (xs : State n) :
    range (M.shift xs).H = range M.H := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z + xs, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x - xs, by simp⟩

@[powerlib_foundation] theorem bddBelow_range_shift_H {xs : State n} :
    BddBelow (range (M.shift xs).H) ↔ BddBelow (range M.H) := by
  rw [range_shift_H]

/-- A strict local minimum moves to the origin. -/
@[powerlib_foundation] theorem isStrictLocalMin_shift_iff {xs : State n} :
    (M.shift xs).IsStrictLocalMin 0 ↔ M.IsStrictLocalMin xs := by
  unfold IsStrictLocalMin
  have hmap := (Homeomorph.addRight xs).map_punctured_nhds_eq (0 : State n)
  simp only [Homeomorph.coe_addRight, zero_add] at hmap
  rw [← hmap, Filter.eventually_map]
  simp

/-- Every flow sentence of the centred system at the origin is the sentence of the zero-input
field at the operating point. -/
@[powerlib_foundation] theorem holds_flow_shift_iff (P : Flow.Property) (xs : State n) :
    (Sentence.flow P).holds (.continuous (M.shift xs).system) ↔ P.holds M.zeroInputField xs := by
  rw [Sentence.holds_flow, system_zeroInput, shift_zeroInputField]
  exact Flow.Property.holds_shift_iff P

/-- Passivity does not depend on the centre of the coordinates. -/
@[powerlib_foundation] theorem holds_passive_shift (xs : State n) (hH : BddBelow (range M.H)) :
    Sentence.passive.holds (.continuous (M.shift xs).system) :=
  (M.shift xs).holds_passive ((M.bddBelow_range_shift_H).mpr hH)

/-- Lyapunov stability of a strict local minimum, as the library sentence of the centred
system. -/
@[powerlib_foundation] theorem IsStrictLocalMin.holds_lyapunovStable {xs : State n}
    (h : M.IsStrictLocalMin xs) :
    (Sentence.flow .lyapunovStable).holds (.continuous (M.shift xs).system) :=
  (M.holds_flow_shift_iff .lyapunovStable xs).mpr h.lyapunovStable

end NonlinearModel

/-! ## Deterministic disturbance channels on a nonlinear pH model -/

section GridDisturbance

variable {n m a b c : ℕ}

/-- Field (1.1) of T-grid-disturbance: the pH drift and control port of `M`, plus a constant
frequency channel `Bω uω`, a state-dependent voltage channel `Bv(x) uv`, and a constant
channel `BT uT`. -/
def gridDisturbance_field (M : NonlinearModel n m) (Bω : Matrix (Fin n) (Fin a) ℝ)
    (Bv : State n → Matrix (Fin n) (Fin b) ℝ) (BT : Matrix (Fin n) (Fin c) ℝ)
    (x : State n) (uS : Fin m → ℝ) (uω : Fin a → ℝ) (uv : Fin b → ℝ)
    (uT : Fin c → ℝ) : State n :=
  M.field x uS + WithLp.toLp 2 (Bω *ᵥ uω + Bv x *ᵥ uv + BT *ᵥ uT)

/-- Energy balance (1.2) split by channel:
`Ḣ = y_Sᵀ u_S + y_ωᵀ u_ω + y_vᵀ u_v + y_Tᵀ u_T − ∇Hᵀ R ∇H`, `y_k = B_kᵀ ∇H`. -/
@[powerlib_foundation] theorem gridDisturbance_power_balance (M : NonlinearModel n m)
    (Bω : Matrix (Fin n) (Fin a) ℝ) (Bv : State n → Matrix (Fin n) (Fin b) ℝ)
    (BT : Matrix (Fin n) (Fin c) ℝ) (x : State n) (uS : Fin m → ℝ)
    (uω : Fin a → ℝ) (uv : Fin b → ℝ) (uT : Fin c → ℝ) :
    fderiv ℝ M.H x (gridDisturbance_field M Bω Bv BT x uS uω uv uT) =
      M.supply x uS + uω ⬝ᵥ (Bωᵀ *ᵥ WithLp.ofLp (M.dH x)) +
        uv ⬝ᵥ ((Bv x)ᵀ *ᵥ WithLp.ofLp (M.dH x)) + uT ⬝ᵥ (BTᵀ *ᵥ WithLp.ofLp (M.dH x)) -
        M.dampingPower x := by
  have hport : ∀ {k : ℕ} (G : Matrix (Fin n) (Fin k) ℝ) (v : Fin k → ℝ),
      WithLp.ofLp (M.dH x) ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ (Gᵀ *ᵥ WithLp.ofLp (M.dH x)) := by
    intro k G v
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  rw [gridDisturbance_field, map_add, M.power_balance, M.fderiv_H_apply, WithLp.ofLp_toLp,
    dotProduct_add, dotProduct_add, hport, hport, hport]
  ring

end GridDisturbance

end powerlib.PH

/-! ## Families of nonlinear port-Hamiltonian systems -/

namespace powerlib.Family

open Set PH

variable {X Y Q R : Type*} {n m : ℕ}

/-- Every complete system of the family is the port system of a nonlinear pH system. -/
def IsNonlinearPH (F : Family X Q n m) (model : X → NonlinearModel n m) : Prop :=
  ∀ x, F.system x = (model x).system

variable {F : Family X Q n m} {model : X → NonlinearModel n m}

/-- A flow sentence holds for a member exactly when it holds for the zero-input field of its pH
system at the origin. -/
@[powerlib_foundation] theorem IsNonlinearPH.mem_den_flow (hF : F.IsNonlinearPH model)
    {P : Flow.Property} {x : X} :
    x ∈ F.den (.flow P) ↔ P.holds (model x).zeroInputField 0 := by
  rw [mem_den, hF x, Sentence.holds_flow, NonlinearModel.system_zeroInput]

/-- A lower bound on the Hamiltonian places a member in the passivity denotation. -/
@[tmio TM, powerlib_foundation] theorem IsNonlinearPH.mem_den_passive (hF : F.IsNonlinearPH model) {x : X}
    (hH : BddBelow (range (model x).H)) : connection% (x ∈ F.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den, hF x]
  exact (model x).holds_passive hH

/-- An explicit lower bound `c ≤ H` places a member in the passivity denotation. -/
@[powerlib_foundation] theorem IsNonlinearPH.mem_den_passive_of_lowerBound
    (hF : F.IsNonlinearPH model) {x : X} (c : ℝ) (hc : ∀ z, c ≤ (model x).H z) :
    x ∈ F.den .passive :=
  hF.mem_den_passive ⟨c, by rintro _ ⟨z, rfl⟩; exact hc z⟩

/-- A strict local minimum of the Hamiltonian at the origin places a member in Lyapunov
stability. -/
@[powerlib_foundation] theorem IsNonlinearPH.mem_den_lyapunovStable (hF : F.IsNonlinearPH model)
    {x : X} (h : (model x).IsStrictLocalMin 0) : x ∈ F.den (.flow .lyapunovStable) :=
  hF.mem_den_flow.mpr h.lyapunovStable

/-- For pH systems centred at operating points, a flow sentence holds for a member exactly when
it holds for the zero-input field of the uncentred system at the operating point. -/
@[powerlib_foundation] theorem IsNonlinearPH.mem_den_flow_shift {base : X → NonlinearModel n m}
    {point : X → EuclideanSpace ℝ (Fin n)}
    (hF : F.IsNonlinearPH fun x => (base x).shift (point x)) {P : Flow.Property} {x : X} :
    x ∈ F.den (.flow P) ↔ P.holds (base x).zeroInputField (point x) := by
  rw [mem_den, hF x]
  exact (base x).holds_flow_shift_iff P (point x)

/-- A strict local minimum of the Hamiltonian at the operating point places a member of a centred
pH family in Lyapunov stability. -/
@[powerlib_foundation] theorem IsNonlinearPH.mem_den_lyapunovStable_shift
    {base : X → NonlinearModel n m} {point : X → EuclideanSpace ℝ (Fin n)}
    (hF : F.IsNonlinearPH fun x => (base x).shift (point x)) {x : X}
    (h : (base x).IsStrictLocalMin (point x)) : x ∈ F.den (.flow .lyapunovStable) :=
  hF.mem_den_flow_shift.mpr h.lyapunovStable

/-- A family read in another representation stays port-Hamiltonian. -/
@[powerlib_foundation] theorem IsNonlinearPH.comap (hF : F.IsNonlinearPH model) (g : Y → X) :
    (F.comap g).IsNonlinearPH (model ∘ g) := fun y => hF (g y)

/-- A family with an extended requirement language stays port-Hamiltonian. -/
@[powerlib_foundation] theorem IsNonlinearPH.extend (hF : F.IsNonlinearPH model) (g : Y → X)
    (extra : Y → R → Prop) : (F.extend g extra).IsNonlinearPH (model ∘ g) := fun y => hF (g y)

end powerlib.Family
