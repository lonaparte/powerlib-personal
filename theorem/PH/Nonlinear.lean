import dependencies.Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import theorem.Dynamics.Autonomous
import theorem.Passivity

/-! Nonlinear input-state-output port-Hamiltonian systems with a general,
not necessarily quadratic, Hamiltonian.

Model boundary.
* State: `x : State n = EuclideanSpace ℝ (Fin n)`, the same state space as
  `powerlib.Dynamics`. The order and physical meaning of the coordinates is fixed by
  each concrete instance; this module is coordinate-agnostic.
* Input: `u : Fin m → ℝ`, an arbitrary (possibly time-varying) port effort.
  Output: `y = g(x)ᵀ ∇H(x)`, the collocated conjugate flow.
* Dynamics, continuous time: `ẋ = (J(x) − R(x)) ∇H(x) + g(x) u`.
  `J(x)` is pointwise skew-symmetric, `R(x)` is pointwise symmetric positive semidefinite
  (`Matrix.PosSemidef`), `g(x)` is an arbitrary `n × m` input matrix.
  No continuity of `J`, `R`, `g` in `x` is assumed by the pointwise and trajectory results.
* Hamiltonian: `H : State n → ℝ` is differentiable everywhere with the explicitly
  supplied gradient field `dH` (`HasGradientAt H (dH x) x`). `H` may be non-quadratic and
  is **not** assumed bounded below or nonnegative. `PassiveWithStorage` is stated only
  under an explicit lower bound.
* Power sign: the supply rate `uᵀ y` is the power delivered *into* the system through the
  port (incoming-positive, matching work-sync `conventions.md` §D). `∇Hᵀ R ∇H ≥ 0` is
  the internally dissipated power.
* Excluded: implicit / Dirac-structure pH, pH-DAE algebraic constraints, interconnection
  theorems, PBC / IDA-PBC, LaSalle invariance, delay, PWM, PLL, saturation, and any
  discretization. Stability results are equilibrium-level (Lyapunov stability of a strict
  local minimum of `H` under zero input), using `powerlib.Dynamics.LyapunovStable`
  (finite forward solution segments).

Source: work-sync `theory/T-ph.md` §1.1 (form (1.1), structure assumptions 1–2, 4),
§1.2 (power balance (1.2), integral balance (1.3), passivity (1.4), zero-input corollary).
Correction: §1.0/§1.1 list `H ≥ H_min > −∞` as a structural assumption. It is not needed
for (1.2), (1.3), the dissipation inequality, or Lyapunov stability; it is used here only for
the passivity statement (1.4), where the storage is `H − H_min`. The §1.2 corollary claim
"global asymptotic stability by LaSalle" is not formalized here (LaSalle is out of scope).
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
open powerlib.Dynamics (State)

variable {n m : ℕ}

/-- The Euclidean inner product written as a dot product of coordinate vectors. -/
@[powerlib_foundation] theorem inner_eq_dotProduct (x y : State n) :
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

/-! ### Trajectories and the `Passivity.System` interface -/

/-- The input-output system of the model, for the `powerlib.Passivity` interface. -/
def toSystem : Passivity.System (State n) (Fin m) :=
  ⟨M.field, fun x _ => M.output x⟩

@[simp, powerlib_foundation] theorem toSystem_field (x : State n) (u : Fin m → ℝ) :
    M.toSystem.field x u = M.field x u := rfl

@[simp, powerlib_foundation] theorem supply_toSystem (x : State n) (u : Fin m → ℝ) :
    Passivity.supply M.toSystem x u = M.supply x u := rfl

/-- `H` is a dissipative storage of the port-Hamiltonian system, without any sign condition. -/
def storage : Passivity.DissipativeStorage M.toSystem where
  energy := M.H
  rate x u := fderiv ℝ M.H x (M.field x u)
  energyDerivative := fun {_} {x} hx {t} ht =>
    (M.differentiable_H (x t)).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
  dissipation x u := by
    rw [supply_toSystem]
    exact M.dissipation_inequality x u

@[simp, powerlib_foundation] theorem storage_energy : M.storage.energy = M.H := rfl

/-- Along every input/state trajectory, `d/dt H(x(t)) = uᵀ y − ∇Hᵀ R ∇H`. -/
@[powerlib_domain] theorem trajectory_energy_derivative
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → State n}
    (hx : Passivity.IsTrajectory M.toSystem u x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => M.H (x τ))
      (M.supply (x t) (u t) - M.dampingPower (x t)) (Ici 0) t := by
  rw [← M.power_balance]
  exact M.storage.energyDerivative hx ht

/-- Integral energy balance (T-ph (1.3)):
`H(x(t)) − H(x(0)) = ∫₀ᵗ (uᵀ y − ∇Hᵀ R ∇H)`. -/
@[powerlib_domain] theorem integral_power_balance
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → State n}
    (hx : Passivity.IsTrajectory M.toSystem u x) {t : ℝ} (ht : 0 ≤ t)
    (hint : IntervalIntegrable
      (fun τ => M.supply (x τ) (u τ) - M.dampingPower (x τ)) volume 0 t) :
    M.H (x t) - M.H (x 0) =
      ∫ τ in (0 : ℝ)..t, (M.supply (x τ) (u τ) - M.dampingPower (x τ)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (fun τ hτ => (M.trajectory_energy_derivative hx hτ.1).continuousWithinAt.mono
      (fun _ h => h.1))
    (fun τ hτ => (M.trajectory_energy_derivative hx hτ.1.le).mono
      (fun r hr => hτ.1.le.trans hr.le))
    hint]

/-- Integral dissipation inequality: `H(x(t)) − H(x(0)) ≤ ∫₀ᵗ uᵀ y`. -/
@[powerlib_domain] theorem integral_dissipation
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → State n}
    (hx : Passivity.IsTrajectory M.toSystem u x) {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun τ => M.supply (x τ) (u τ)) volume 0 t) :
    M.H (x t) - M.H (x 0) ≤ ∫ τ in (0 : ℝ)..t, M.supply (x τ) (u τ) :=
  M.storage.integral_dissipation hx ht hsupply

/-- Passivity with storage `H − c` when `H` is bounded below by `c` (T-ph (1.4)). -/
@[powerlib_domain] theorem passiveWithStorage_sub {c : ℝ} (hH : ∀ x, c ≤ M.H x) :
    Passivity.PassiveWithStorage M.toSystem (fun x => M.H x - c) := by
  refine ⟨fun y => sub_nonneg.mpr (hH y), ?_⟩
  intro u x hx t ht hsupply
  have h := M.storage.integral_dissipation hx ht hsupply
  rw [storage_energy] at h
  linarith

/-- Passivity with storage `H` when `H` is nonnegative. -/
@[powerlib_domain] theorem passiveWithStorage (hH : ∀ x, 0 ≤ M.H x) :
    Passivity.PassiveWithStorage M.toSystem M.H := by
  simpa using M.passiveWithStorage_sub hH

/-- Under zero input the Hamiltonian is antitone along `Passivity` trajectories. -/
@[powerlib_domain] theorem zeroInput_energy_antitone {x : ℝ → State n}
    (hx : Passivity.IsTrajectory M.toSystem (fun _ => 0) x) :
    AntitoneOn (fun t => M.H (x t)) (Ici 0) :=
  M.storage.zeroInput_energy_antitone hx

/-- Under zero input the Hamiltonian is antitone along every finite solution segment
of the autonomous field, in the `powerlib.Dynamics` trajectory semantics. -/
@[powerlib_domain] theorem energy_antitoneOn_of_isTrajectoryOn {φ : ℝ → State n} {a b : ℝ}
    (hφ : Dynamics.IsTrajectoryOn φ M.zeroInputField a b) :
    AntitoneOn (M.H ∘ φ) (Icc a b) :=
  Dynamics.antitoneOn_V_comp_traj M.differentiable_H M.continuous_H (convex_Icc a b) hφ
    (fun t _ => M.zeroInput_lie_nonpos (φ t))

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
@[powerlib_domain] theorem IsStrictLocalMin.isEquilibrium {xs : State n}
    (h : M.IsStrictLocalMin xs) : Dynamics.IsEquilibrium M.zeroInputField xs :=
  M.zeroInputField_eq_zero_of_dH_eq_zero (M.dH_eq_zero_of_isLocalMin h.isLocalMin)

/-- `H − H(x*)` is a local Lyapunov function of the zero-input field at a strict local
minimum `x*` of `H`. -/
@[powerlib_foundation] theorem IsStrictLocalMin.exists_isLocalLyapunovFunction {xs : State n}
    (h : M.IsStrictLocalMin xs) :
    ∃ D : Set (State n), Dynamics.IsLocalLyapunovFunction M.zeroInputField
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
@[powerlib_domain] theorem IsStrictLocalMin.lyapunovStable {xs : State n}
    (h : M.IsStrictLocalMin xs) : Dynamics.LyapunovStable M.zeroInputField xs := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro ε hε
    refine ⟨1, one_pos, fun t₀ t₁ φ _ _ t _ => ?_⟩
    rw [Subsingleton.elim (φ t) xs, sub_self, norm_zero]
    exact hε
  · obtain ⟨D, hV⟩ := h.exists_isLocalLyapunovFunction
    exact Dynamics.lyapunov_stable hn hV

/-- Equilibrium and Lyapunov stability of a strict local minimum of `H` under zero input. -/
@[powerlib_domain] theorem IsStrictLocalMin.isEquilibrium_and_lyapunovStable {xs : State n}
    (h : M.IsStrictLocalMin xs) :
    Dynamics.IsEquilibrium M.zeroInputField xs ∧ Dynamics.LyapunovStable M.zeroInputField xs :=
  ⟨h.isEquilibrium, h.lyapunovStable⟩

end NonlinearModel

end powerlib.PH
