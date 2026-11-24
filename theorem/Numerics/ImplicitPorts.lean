import theorem.Numerics.EulerPorts
import theorem.Numerics.PeriodicInput

/-! # Implicit implementations of linear plants with ports: passivity (foundation)

Two implicit one-step methods for a plant `ẋ = A x + B u`, `y = C x + D u`, with the input held
over the step. The implicit midpoint (Tustin) rule `x⁺ − x = h (A x̄ + B u)`, output at the
midpoint `x̄ = (x + x⁺)/2`, is `Numerics.midpointSystem` (`theorem/Numerics/EulerPorts.lean`),
which keeps a KYP certificate; the backward Euler rule `x⁺ − x = h (A x⁺ + B u)`, output at the end
of the step `C x⁺ + D u` (`backwardEulerSystem`), keeps one too. Both maps are linear and, with a
well-posed step, their step is the unique solution of its relation (`midpointStep_eq_of_sub`,
`backwardEulerStep_eq_of_sub`). A sinusoidal steady state of the plant is a sampled sinusoid of
each scheme. For the midpoint rule: a phasor `(X, U)` of the plant at the frequency `w`,
`i w X = A X + B U`, with `h w (1 + cos θ) = 2 sin θ` (`w = (2/h) tan(θ/2)`, the bilinear
transform), is the midpoint phasor at the discrete frequency `θ`; the discrete state phasor is
`e^{−iθ/2} X / cos(θ/2)`, in real form `X_r + t X_i`, `X_i − t X_r`, `t = tan(θ/2)`, and the
midpoint output is `C X + D U`. For backward Euler: a phasor at the complex frequency
`s = σ + i ω`, `s X = A X + B U`, with `h s = 1 − e^{−iθ}`, is the end-of-step phasor; the
discrete state phasor is `e^{−iθ} X` and the output `C X + D U`. A negative mean supplied power
`Re(Ū (C X + D U)) < 0` at a closing frequency (`cos(N θ) = 1`, `sin θ ≠ 0`) refutes passivity
of the discretization (`Map.System.not_passive_of_periodic_input`). Backward Euler dissipates
more than the plant: the storage `xᵀ P x / 2` changes over a step by
`h (x⁺ᵀ P A x⁺ + (C x⁺) · u) − (h²/2) vᵀ P v`, `v = A x⁺ + B u`, so a storage matrix with
`Bᵀ P = C` and `ξᵀ P A ξ ≤ (h/2) vᵀ P v` for all `ξ, u` certifies passivity
(`backwardEulerSystem_passiveWith_of`) — a KYP certificate does at every step
(`backwardEulerSystem_passiveWith`), and a plant that is not passive can have a passive
backward Euler discretization.

Scope.
* A generic template, not a model: arbitrary plants `Linear.Plant n p`
  (`theorem/Linear/Plant.lean`), steps `h ≥ 0` (`h > 0` for the refutations) with
  `I − (h/2) A` (midpoint) or `I − h A` (backward Euler) invertible; discrete time, exact
  arithmetic, fixed step. The implementation families are over an arbitrary type `Y` with a
  design model `design y` and a step `step y`, requirements and translation of the design
  model, as `Numerics.eulerPortFamily`. The instances are in
  `theorem/GridTiedConverter/GFM/Discrete/LinearPort.lean`.

Source: `theorem/Numerics/EulerPorts.lean` (`midpointStep`, `midpointSystem`,
`midpointStep_sub`, `midpointSystem_passiveWith`, `midpointPortFamily`),
`theorem/Numerics/PeriodicInput.lean` (`Map.System.not_passive_of_periodic_input`),
`theorem/Port/Linear.lean` (KYP certificates), `theorem/Stack/Implementation.lean`
(`Implementation.ofDesign`); Brogliato, Lozano, Maschke and Egeland, *Dissipative Systems Analysis
and Control* (2007), §3 (KYP lemma, positive real transfer functions, the bilinear transform);
Hairer, Lubich and Wanner, *Geometric Numerical Integration* (2006), §VI (the implicit midpoint
rule); work-sync `theory/T-numerical-integration.md` §2.7.

Results.
* Midpoint: `midpointStep_eq_of_sub` (with `I − (h/2) A` invertible the midpoint step is the only
  solution of its relation), `midpointSystem_not_passive_of_phasor` (a plant phasor at `w` with
  `h w (1 + cos θ) = 2 sin θ` and negative mean supplied power refutes passivity of the midpoint
  discretization at step `h`).
* Backward Euler: `backwardEulerStep` (`x⁺` from `(I − h A) x⁺ = x + h B u`),
  `backwardEulerSystem` (output `C x⁺ + D u`, step length `h`), `backwardEulerStep_sub`,
  `backwardEulerStep_eq_of_sub` (the step solves, and with `I − h A` invertible is the only
  solution of, `x⁺ − x = h (A x⁺ + B u)`), `backwardEulerSystem_passiveWith_of` (a storage matrix
  with `Bᵀ P = C` and the step-dependent dissipation inequality certifies passivity),
  `backwardEulerSystem_passiveWith` (a KYP certificate does, at every step `h ≥ 0`),
  `backwardEulerSystem_not_passive_of_phasor` (a plant phasor at `s` with `h s = 1 − e^{−iθ}` and
  negative mean supplied power refutes passivity).

Family and connection conclusions.
* The realization `midpointPorts F plant design step` of the midpoint family
  `Numerics.midpointPortFamily` (`Implementation.ofDesign design`).
* The backward Euler template `backwardEulerPortFamily F plant design step : Family Y Q n p`
  (requirements and translation of the design model), its realization `backwardEulerPorts`, and
  the passivity law `backwardEulerPortFamily_mem_den_passive` (a KYP certificate of the design
  plant and a well-posed step `h ≥ 0` place the implementation in passivity). These are
  connection statements over families of `Type`. Scaffold: `theorem/Numerics/EulerPorts.agda`.
-/

noncomputable section

namespace powerlib.Numerics

open Matrix LinearSystems TMIO

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The implicit midpoint rule -/

/-- **The midpoint step is the only solution of its relation.** With `I − (h/2) A` invertible, a
state `y` with `y − x = h (A x̄ + B u)`, `x̄ = (x + y)/2`, is the midpoint step from `x`. -/
@[tmio T, powerlib_foundation] theorem midpointStep_eq_of_sub (M : Linear.Plant n p) {h : ℝ}
    (hw : IsUnit (1 - (h / 2) • M.A).det) {x y : ℝⁿ} {u : Fin p → ℝ}
    (hy : WithLp.ofLp y - WithLp.ofLp x = h • (M.A *ᵥ ((1 / 2 : ℝ) •
      (WithLp.ofLp x + WithLp.ofLp y)) + M.B *ᵥ u)) :
    midpointStep M h x u = y := by
  have key : (1 + (h / 2) • M.A) *ᵥ WithLp.ofLp x + h • (M.B *ᵥ u) =
      (1 - (h / 2) • M.A) *ᵥ WithLp.ofLp y := by
    ext i
    have hi := congrFun hy i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_smul,
      Matrix.mulVec_add] at hi
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  rw [midpointStep, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hw, Matrix.one_mulVec]

/-- The midpoint step is linear in the state and the input. -/
@[tmio T, powerlib_foundation] private theorem midpointStep_linear (M : Linear.Plant n p)
    (h a b : ℝ) (x x' : ℝⁿ) (u u' : Fin p → ℝ) :
    midpointStep M h (a • x + b • x') (a • u + b • u') =
      a • midpointStep M h x u + b • midpointStep M h x' u' := by
  simp only [midpointStep, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  module

/-- **A sinusoidal steady state of the plant that draws energy refutes passivity of its
midpoint discretization.** For a step `h > 0` with `I − (h/2) A` invertible, a discrete frequency
`θ` with `cos(N θ) = 1` (`N > 0`) and `sin θ ≠ 0`, and a phasor `(X_r + i X_i, U_r + i U_i)` of the
plant at the frequency `w`, `A X + B U = i w X`, related by the bilinear transform
`h w (1 + cos θ) = 2 sin θ`: if the mean supplied power `U_r · Y_r + U_i · Y_i`,
`Y = C X + D U`, is negative, the midpoint discretization is not passive. The input
`u_k = cos(θ k) U_r − sin(θ k) U_i` holds the closed orbit with state phasor
`(X_r + t X_i) + i (X_i − t X_r)`, `t = sin θ/(1 + cos θ)`, whose midpoints are the plant's
phasor (`Map.System.not_passive_of_periodic_input`). -/
@[tmio T, powerlib_foundation] theorem midpointSystem_not_passive_of_phasor
    (M : Linear.Plant n p) {h : ℝ} (hh : 0 < h) (hw : IsUnit (1 - (h / 2) • M.A).det)
    {θ : ℝ} {N : ℕ} (hN : 0 < N) (hper : Real.cos (N * θ) = 1) (hθ : Real.sin θ ≠ 0) {w : ℝ}
    (hwθ : h * w * (1 + Real.cos θ) = 2 * Real.sin θ) {Xr Xi : Fin n → ℝ} {Ur Ui : Fin p → ℝ}
    (hr : M.A *ᵥ Xr + M.B *ᵥ Ur = (-w) • Xi) (hi : M.A *ᵥ Xi + M.B *ᵥ Ui = w • Xr)
    (hneg : Ur ⬝ᵥ (M.C *ᵥ Xr + M.D *ᵥ Ur) + Ui ⬝ᵥ (M.C *ᵥ Xi + M.D *ᵥ Ui) < 0) :
    ¬ (midpointSystem M h).Passive := by
  set c := Real.cos θ
  set s := Real.sin θ
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hc1 : 1 + c ≠ 0 := by
    intro h0
    have : c = -1 := by linarith
    rw [this] at hsc
    exact hθ (pow_eq_zero_iff two_ne_zero |>.mp (by linarith))
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, t * (1 + c) = s ∧ t * s = 1 - c := by
    refine ⟨s / (1 + c), div_mul_cancel₀ s hc1, ?_⟩
    have : s / (1 + c) * s * (1 + c) = (1 - c) * (1 + c) := by
      rw [mul_right_comm, div_mul_cancel₀ s hc1]
      linear_combination hsc
    exact mul_right_cancel₀ hc1 this
  have hhw : h * w = 2 * t := by
    apply mul_right_cancel₀ hc1
    rw [hwθ, mul_assoc, ht1]
  set Yr : ℝⁿ := WithLp.toLp 2 (Xr + t • Xi)
  set Yi : ℝⁿ := WithLp.toLp 2 (Xi - t • Xr)
  have hmidr : (1 / 2 : ℝ) • (WithLp.ofLp Yr + WithLp.ofLp (c • Yr - s • Yi)) = Xr := by
    ext i
    simp only [Yr, Yi, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    linear_combination (Xr i / 2) * ht2 + (Xi i / 2) * ht1
  have hmidi : (1 / 2 : ℝ) • (WithLp.ofLp Yi + WithLp.ofLp (s • Yr + c • Yi)) = Xi := by
    ext i
    simp only [Yr, Yi, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    linear_combination (Xi i / 2) * ht2 - (Xr i / 2) * ht1
  have hstepr : midpointStep M h Yr Ur = c • Yr - s • Yi := by
    apply midpointStep_eq_of_sub M hw
    rw [hmidr, hr]
    ext i
    simp only [Yr, Yi, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    linear_combination (Xr i) * ht2 + (Xi i) * hhw + (Xi i) * ht1
  have hstepi : midpointStep M h Yi Ui = s • Yr + c • Yi := by
    apply midpointStep_eq_of_sub M hw
    rw [hmidi, hi]
    ext i
    simp only [Yr, Yi, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    linear_combination (Xi i) * ht2 - (Xr i) * ht1 - (Xr i) * hhw
  refine Map.System.not_passive_of_periodic_input (midpointSystem M h) hh hN hper hθ
    (Xr := Yr) (Xi := Yi) (Ur := Ur) (Ui := Ui) (fun a b => midpointStep_linear M h a b _ _ _ _)
    (fun a b => ?_) hstepr hstepi ?_
  · change M.C *ᵥ ((1 / 2 : ℝ) • (WithLp.ofLp (a • Yr + b • Yi) +
        WithLp.ofLp (midpointStep M h (a • Yr + b • Yi) (a • Ur + b • Ui)))) +
        M.D *ᵥ (a • Ur + b • Ui) = a • (M.C *ᵥ ((1 / 2 : ℝ) • (WithLp.ofLp Yr +
        WithLp.ofLp (midpointStep M h Yr Ur))) + M.D *ᵥ Ur) + b • (M.C *ᵥ ((1 / 2 : ℝ) •
        (WithLp.ofLp Yi + WithLp.ofLp (midpointStep M h Yi Ui))) + M.D *ᵥ Ui)
    rw [midpointStep_linear]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      smul_add]
    module
  · change Ur ⬝ᵥ (M.C *ᵥ ((1 / 2 : ℝ) • (WithLp.ofLp Yr +
        WithLp.ofLp (midpointStep M h Yr Ur))) + M.D *ᵥ Ur) + Ui ⬝ᵥ (M.C *ᵥ ((1 / 2 : ℝ) •
        (WithLp.ofLp Yi + WithLp.ofLp (midpointStep M h Yi Ui))) + M.D *ᵥ Ui) < 0
    rw [hstepr, hstepi, hmidr, hmidi]
    exact hneg

/-! ## The backward Euler rule -/

/-- One step of the backward Euler rule for a plant with step `h`: the solution `x⁺` of
`(I − h A) x⁺ = x + h B u` through the inverse of `I − h A`. -/
def backwardEulerStep (M : Linear.Plant n p) (h : ℝ) (x : ℝⁿ) (u : Fin p → ℝ) : ℝⁿ :=
  WithLp.toLp 2 ((1 - h • M.A)⁻¹ *ᵥ (WithLp.ofLp x + h • (M.B *ᵥ u)))

/-- The backward Euler discretization of a plant with step `h`: the step `backwardEulerStep`,
the plant's output at the end of the step with the input held, `C x⁺ + D u`, and step length
`h`. -/
def backwardEulerSystem (M : Linear.Plant n p) (h : ℝ) : Map.System n p :=
  ⟨backwardEulerStep M h, fun x u => M.C *ᵥ WithLp.ofLp (backwardEulerStep M h x u) +
    M.D *ᵥ u, h⟩

/-- With `I − h A` invertible the backward Euler step solves `x⁺ − x = h (A x⁺ + B u)`. -/
@[tmio T, powerlib_foundation] theorem backwardEulerStep_sub (M : Linear.Plant n p) {h : ℝ}
    (hw : IsUnit (1 - h • M.A).det) (x : ℝⁿ) (u : Fin p → ℝ) :
    WithLp.ofLp (backwardEulerStep M h x u) - WithLp.ofLp x =
      h • (M.A *ᵥ WithLp.ofLp (backwardEulerStep M h x u) + M.B *ᵥ u) := by
  have hy : (1 - h • M.A) *ᵥ WithLp.ofLp (backwardEulerStep M h x u) =
      WithLp.ofLp x + h • (M.B *ᵥ u) := by
    simp only [backwardEulerStep, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hw, Matrix.one_mulVec]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hy
  ext i
  have hi := congrFun hy i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- **The backward Euler step is the only solution of its relation.** With `I − h A`
invertible, a state `y` with `y − x = h (A y + B u)` is the backward Euler step from `x`. -/
@[tmio T, powerlib_foundation] theorem backwardEulerStep_eq_of_sub (M : Linear.Plant n p) {h : ℝ}
    (hw : IsUnit (1 - h • M.A).det) {x y : ℝⁿ} {u : Fin p → ℝ}
    (hy : WithLp.ofLp y - WithLp.ofLp x = h • (M.A *ᵥ WithLp.ofLp y + M.B *ᵥ u)) :
    backwardEulerStep M h x u = y := by
  have key : WithLp.ofLp x + h • (M.B *ᵥ u) = (1 - h • M.A) *ᵥ WithLp.ofLp y := by
    ext i
    have hi := congrFun hy i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  rw [backwardEulerStep, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hw,
    Matrix.one_mulVec]

/-- The backward Euler step is linear in the state and the input. -/
@[tmio T, powerlib_foundation] private theorem backwardEulerStep_linear (M : Linear.Plant n p)
    (h a b : ℝ) (x x' : ℝⁿ) (u u' : Fin p → ℝ) :
    backwardEulerStep M h (a • x + b • x') (a • u + b • u') =
      a • backwardEulerStep M h x u + b • backwardEulerStep M h x' u' := by
  simp only [backwardEulerStep, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  module

/-- **A storage certificate of the backward Euler discretization.** For a step `h ≥ 0` with
`I − h A` invertible, a symmetric positive semidefinite `P` with `Bᵀ P = C`, a feedthrough with
`uᵀ D u ≥ 0`, and the step-dependent dissipation inequality `ξᵀ P A ξ ≤ (h/2) vᵀ P v`,
`v = A ξ + B u`, for all `ξ, u`: the backward Euler discretization is passive with the storage
`xᵀ P x / 2`. Over a step the storage changes by `x⁺ᵀ P (x⁺ − x) − (x⁺ − x)ᵀ P (x⁺ − x)/2`,
that is `h (x⁺ᵀ P A x⁺ + (C x⁺) · u) − (h²/2) vᵀ P v` with `v = A x⁺ + B u`. -/
@[tmio T, powerlib_foundation] theorem backwardEulerSystem_passiveWith_of {M : Linear.Plant n p}
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P) (hnonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x))
    (hout : M.Bᵀ * P = M.C) (hD : ∀ u : Fin p → ℝ, 0 ≤ u ⬝ᵥ (M.D *ᵥ u)) {h : ℝ} (hh : 0 ≤ h)
    (hw : IsUnit (1 - h • M.A).det)
    (hdiss : ∀ (ξ : Fin n → ℝ) (u : Fin p → ℝ), ξ ⬝ᵥ (P *ᵥ (M.A *ᵥ ξ)) ≤
      h / 2 * ((M.A *ᵥ ξ + M.B *ᵥ u) ⬝ᵥ (P *ᵥ (M.A *ᵥ ξ + M.B *ᵥ u)))) :
    (backwardEulerSystem M h).PassiveWith (Linear.quadraticEnergy P) := by
  refine ⟨fun x => mul_nonneg (by norm_num) (hnonneg _), fun x u => ?_⟩
  set y := WithLp.ofLp (backwardEulerStep M h x u)
  set x0 := WithLp.ofLp x
  set v := M.A *ᵥ y + M.B *ᵥ u
  have hstep : y - x0 = h • v := backwardEulerStep_sub M hw x u
  have hx0 : x0 = y - h • v := by rw [← hstep]; abel
  have hB : y ⬝ᵥ (P *ᵥ (M.B *ᵥ u)) = (M.C *ᵥ y) ⬝ᵥ u := by
    rw [← hout, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose, hP]
  have hsym := Criteria.dotProduct_mulVec_comm_of_symm hP y v
  have hd := hdiss y u
  have hDu := hD u
  change (1 / 2 : ℝ) * (y ⬝ᵥ (P *ᵥ y)) - (1 / 2 : ℝ) * (x0 ⬝ᵥ (P *ᵥ x0)) ≤
    h * (u ⬝ᵥ (M.C *ᵥ y + M.D *ᵥ u))
  rw [hx0]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_add]
  have hv : y ⬝ᵥ (P *ᵥ v) = y ⬝ᵥ (P *ᵥ (M.A *ᵥ y)) + (M.C *ᵥ y) ⬝ᵥ u := by
    simp only [v, Matrix.mulVec_add, dotProduct_add, hB]
  rw [dotProduct_comm u (M.C *ᵥ y)]
  nlinarith [mul_nonneg hh hDu, mul_nonneg hh (mul_nonneg hh (hnonneg v))]

/-- **Backward Euler keeps the passivity of a KYP certificate.** For a step `h ≥ 0` with `I − h A`
invertible, the backward Euler discretization of a plant with a KYP certificate is passive with
the same storage: `ξᵀ P A ξ ≤ 0 ≤ (h/2) vᵀ P v` (`backwardEulerSystem_passiveWith_of`). -/
@[tmio T, powerlib_foundation] theorem backwardEulerSystem_passiveWith {M : Linear.Plant n p}
    (c : Linear.KYP M) {h : ℝ} (hh : 0 ≤ h) (hw : IsUnit (1 - h • M.A).det) :
    (backwardEulerSystem M h).PassiveWith c.storage :=
  backwardEulerSystem_passiveWith_of c.symmetric c.nonneg c.output c.feedthrough hh hw
    fun ξ u => by
      have hd := c.dissipation ξ
      rw [Linear.quadratic_sym c.symmetric] at hd
      have := mul_nonneg (div_nonneg hh zero_le_two) (c.nonneg (M.A *ᵥ ξ + M.B *ᵥ u))
      linarith

/-- **A plant phasor that draws energy refutes passivity of the backward Euler discretization.**
For a step `h > 0` with `I − h A` invertible, a discrete frequency `θ` with `cos(N θ) = 1`
(`N > 0`) and `sin θ ≠ 0`, and a phasor `(X_r + i X_i, U_r + i U_i)` of the plant at the complex
frequency `s = σ + i ω`, `A X + B U = s X`, with `h σ = 1 − cos θ` and `h ω = sin θ`
(`h s = 1 − e^{−iθ}`): if the mean supplied power `U_r · Y_r + U_i · Y_i`, `Y = C X + D U`, is
negative, the backward Euler discretization is not passive. The input
`u_k = cos(θ k) U_r − sin(θ k) U_i` holds the closed orbit with state phasor `e^{−iθ} X`, whose
end-of-step states are the plant's phasor (`Map.System.not_passive_of_periodic_input`). -/
@[tmio T, powerlib_foundation] theorem backwardEulerSystem_not_passive_of_phasor
    (M : Linear.Plant n p) {h : ℝ} (hh : 0 < h) (hw : IsUnit (1 - h • M.A).det)
    {θ : ℝ} {N : ℕ} (hN : 0 < N) (hper : Real.cos (N * θ) = 1) (hθ : Real.sin θ ≠ 0)
    {σ ω : ℝ} (hσ : h * σ = 1 - Real.cos θ) (hω : h * ω = Real.sin θ)
    {Xr Xi : Fin n → ℝ} {Ur Ui : Fin p → ℝ}
    (hr : M.A *ᵥ Xr + M.B *ᵥ Ur = σ • Xr - ω • Xi)
    (hi : M.A *ᵥ Xi + M.B *ᵥ Ui = ω • Xr + σ • Xi)
    (hneg : Ur ⬝ᵥ (M.C *ᵥ Xr + M.D *ᵥ Ur) + Ui ⬝ᵥ (M.C *ᵥ Xi + M.D *ᵥ Ui) < 0) :
    ¬ (backwardEulerSystem M h).Passive := by
  set c := Real.cos θ
  set s := Real.sin θ
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  set Yr : ℝⁿ := WithLp.toLp 2 (c • Xr + s • Xi)
  set Yi : ℝⁿ := WithLp.toLp 2 (c • Xi - s • Xr)
  have hendr : c • Yr - s • Yi = WithLp.toLp 2 Xr := by
    ext i
    simp only [Yr, Yi, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply]
    linear_combination (Xr i) * hsc
  have hendi : s • Yr + c • Yi = WithLp.toLp 2 Xi := by
    ext i
    simp only [Yr, Yi, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply]
    linear_combination (Xi i) * hsc
  have hstepr : backwardEulerStep M h Yr Ur = c • Yr - s • Yi := by
    apply backwardEulerStep_eq_of_sub M hw
    rw [hendr, WithLp.ofLp_toLp, hr]
    ext i
    simp only [Yr, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(Xr i)) * hσ + (Xi i) * hω
  have hstepi : backwardEulerStep M h Yi Ui = s • Yr + c • Yi := by
    apply backwardEulerStep_eq_of_sub M hw
    rw [hendi, WithLp.ofLp_toLp, hi]
    ext i
    simp only [Yi, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(Xi i)) * hσ - (Xr i) * hω
  refine Map.System.not_passive_of_periodic_input (backwardEulerSystem M h) hh hN hper hθ
    (Xr := Yr) (Xi := Yi) (Ur := Ur) (Ui := Ui)
    (fun a b => backwardEulerStep_linear M h a b _ _ _ _) (fun a b => ?_) hstepr hstepi ?_
  · change M.C *ᵥ WithLp.ofLp (backwardEulerStep M h (a • Yr + b • Yi) (a • Ur + b • Ui)) +
        M.D *ᵥ (a • Ur + b • Ui) = a • (M.C *ᵥ WithLp.ofLp (backwardEulerStep M h Yr Ur) +
        M.D *ᵥ Ur) + b • (M.C *ᵥ WithLp.ofLp (backwardEulerStep M h Yi Ui) + M.D *ᵥ Ui)
    rw [backwardEulerStep_linear]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      smul_add]
    module
  · change Ur ⬝ᵥ (M.C *ᵥ WithLp.ofLp (backwardEulerStep M h Yr Ur) + M.D *ᵥ Ur) +
        Ui ⬝ᵥ (M.C *ᵥ WithLp.ofLp (backwardEulerStep M h Yi Ui) + M.D *ᵥ Ui) < 0
    rw [hstepr, hstepi, hendr, hendi, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
    exact hneg

/-! ## The implementation families -/

section Template

variable {X Y Q : Type*}

/-- The implicit midpoint realization of a family of plants: every midpoint implementation
(`midpointPortFamily`) realizes its design model. -/
def midpointPorts (F : Family X Q n p) (plant : X → Linear.Plant n p) (design : Y → X)
    (step : Y → ℝ) : Implementation X Q Y Q n p n p :=
  { model := F, impl := midpointPortFamily F plant design step,
    realizes := Implementation.ofDesign design }

/-- The backward Euler implementation family of a family of plants, over an implementation type
`Y` whose members carry a design model `design y` and a step `step y`: every implementation read
as the backward Euler discretization of its design's plant with its step; requirements and
translation are those of its design model. -/
def backwardEulerPortFamily (F : Family X Q n p) (plant : X → Linear.Plant n p)
    (design : Y → X) (step : Y → ℝ) : Family Y Q n p where
  system y := .discrete (backwardEulerSystem (plant (design y)) (step y))
  meets y := F.meets (design y)
  translate := F.translate

/-- The backward Euler realization of a family of plants: every backward Euler implementation
realizes its design model. -/
def backwardEulerPorts (F : Family X Q n p) (plant : X → Linear.Plant n p) (design : Y → X)
    (step : Y → ℝ) : Implementation X Q Y Q n p n p :=
  { model := F, impl := backwardEulerPortFamily F plant design step,
    realizes := Implementation.ofDesign design }

end Template

variable {X Y Q : Type} {F : Family X Q n p} {plant : X → Linear.Plant n p} {design : Y → X}
  {step : Y → ℝ}

/-- **A KYP certificate places a backward Euler implementation in passivity.** A backward Euler
implementation with a step `h ≥ 0` (`I − h A` invertible) of a plant with a KYP certificate is
passive with the certificate's storage (`backwardEulerSystem_passiveWith`). -/
@[tmio TM, powerlib_foundation] theorem backwardEulerPortFamily_mem_den_passive {y : Y}
    (c : Linear.KYP (plant (design y))) (hh : 0 ≤ step y)
    (hw : IsUnit (1 - step y • (plant (design y)).A).det) :
    connection% (y ∈ (backwardEulerPortFamily F plant design step).den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  exact ⟨_, backwardEulerSystem_passiveWith c hh hw⟩

end powerlib.Numerics
