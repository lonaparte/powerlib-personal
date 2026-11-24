import theorem.Dynamics.State
import theorem.Dynamics.Shift
import theorem.Linear.Transfer

/-! # Transport of the Flow sentences under changes of coordinates and of time scale

Every behavioural sentence of the library is invariant under invertible affine changes of
coordinates. Under a constant positive time scaling every sentence keeps its form with its time
parameters rescaled: decay rates scale with the time base, sampling horizons inversely. Both are
instances of the one space-time law `holds_spaceTime_iff` (`theorem/Dynamics/SpaceTime.lean`),
where every sentence is transported once.

Scope.
* Generic foundation, independent of any model. Autonomous continuous-time fields
  `f : State n → State n` on `State n = EuclideanSpace ℝ (Fin n)`, read through the Flow semantics
  (`theorem/Flow/Defs.lean`: LeanForControl's finite forward solution segments, and the global
  notions `Flow.ForwardComplete`, `Flow.GloballyAsymptoticallyStable`,
  `Flow.GloballyExponentiallyStable`). No linearization is involved.
* Excluded: time-varying coordinate changes (e.g. the rotating abc → dq Park transform `T(θ(t))`),
  nonlinear diffeomorphisms, state-dependent time scaling, and transport of non-autonomous or
  forced systems (port passivity under linear coordinates is `Port.System.passive_conjugate`).
* These are transport laws (foundation results); they do not by themselves assert a property of
  any particular power system. A model family whose field is the transport of another family's
  field uses `holds_transport_iff` to identify the denotations of the two families sentence by
  sentence.

Source: work-sync `theory/T-PU.md` §1.2 / §1.5 (per-unit scaling of states = constant diagonal
change of coordinates), §1.6 (time base `t̂ = ω_B t`, `d/dt = ω_B d/dt̂`, i.e. the per-unit-time
field is `ω_B⁻¹ • f`); equilibrium shift to error coordinates as used in
`theory/T-pll-dynamics.md` / `theory/T-invariant-coordinates.md`.

Results.
* Affine coordinate change `y = φ(x) = T x + c` (`affineCoord`, `theorem/Dynamics/SpaceTime.lean`),
  `T : State n ≃L[ℝ] State n` invertible (every invertible linear map of `ℝⁿ` is continuous), `c`
  arbitrary. The field in the new coordinates is `g(y) = T f(φ⁻¹ y) = T f(T⁻¹ (y − c))`
  (`transportField`). Solutions, equilibria, smoothness and the Jacobian (`T ∘ Df(x*) ∘ T⁻¹`) are
  transported, and **every** behavioural sentence of the library holds for `f` at `x*` exactly
  when it holds for `g` at `φ(x*)` (`holds_transport_iff`, read for one sentence as
  `holds_transport_iff T c P`; `P.holds` unfolds to the sentence). Scaffold:
  `theorem/Flow/FlowSemantics.agda` (satisfaction of the sentences by a field at a point, invariant
  under affine changes of coordinates: its Agda definitions transportSystem and invariant).
* Matrix form: `T = P` for an invertible matrix `P` (`IsUnit P`), acting through
  `Matrix.toEuclideanCLM` (`matrixCoord`). Example: the
  planar scaling `(θ, v) ↦ (θ, η v)`, `η ≠ 0` (`scaleMatrix`, `scaleMatrix_mul_inv`, `scaleCoord`,
  `scaleCoord_apply`, `scaleCoord_symm_apply`). Sign changes `x ↦ (σᵢ xᵢ)ᵢ`, `σ : Fin n → ℤˣ`
  (`signMatrix`, an involution: `signMatrix_mul_self`, `signMatrix_isUnit`, `signMatrix_inv`;
  `signCoord`, `signCoord_apply`, `signCoord_symm`). A field is the transport of `g` by `T` about
  the origin exactly when `T` conjugates them (`transportField_zero_eq_iff_comp`). Linear fields:
  the field of `T A S` (`S = T⁻¹`) is that of `A` in the coordinates `x' = T x`, so every sentence
  at the origin is invariant (`Linear.holds_conj`), and similar plants satisfy the same sentences
  (`Linear.Similar.holds_iff`).
* Time scaling `τ = t / c`, `c > 0` (e.g. a per-unit time base): `holds_timeScale_iff` (`P` of `f`
  is `P.timeScale c` of `c • f`, every `P` but sampled contraction; `Flow.Property.timeScale c` is
  the sentence with its decay rate scaled by `c`). Sampled contraction of `c • f` is contraction of
  `f` over a horizon `c k`, `k` a positive integer (`sampledContraction_spaceTime_iff`); `c k` need
  not be an integer, so this is not the sentence `contractive` of `f` in general. For linear fields
  every sentence, sampled contraction included (it is the Hurwitz property):
  `holds_timeScale_linear_iff`.

Reuse. `holds_transport_iff` (`c = 1`) and `holds_timeScale_iff` (`T = 1`, `b = 0`) are instances
of `holds_spaceTime_iff`, as is the equilibrium shift `Flow.Property.holds_shift_iff`
(`theorem/Dynamics/Shift.lean`); the per-sentence transports (`*_of_spaceTime`) are not restated.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology

variable {n : ℕ}

/-! ### Affine coordinate changes -/

section Affine

variable (T : State n ≃L[ℝ] State n) (c : State n)

@[tmio T, simp, powerlib_foundation] theorem transportField_affineCoord (f : State n → State n)
    (x : State n) : transportField T c f (affineCoord T c x) = T (f x) := by
  simp [transportField, affineCoord]

@[tmio T, simp, powerlib_foundation] theorem affineCoord_affineCoord_symm (y : State n) :
    affineCoord T c (affineCoord T.symm (-(T.symm c)) y) = y := by
  simp [affineCoord]

/-- Transporting back by the inverse coordinate change recovers the original field. -/
@[tmio T, simp, powerlib_foundation] theorem transportField_symm_transportField
    (f : State n → State n) :
    transportField T.symm (-(T.symm c)) (transportField T c f) = f := by
  funext y
  simp [transportField]

@[tmio T, powerlib_foundation] theorem continuous_affineCoord : Continuous (affineCoord T c) :=
  T.continuous.add continuous_const

/-- Solutions are mapped to solutions by the affine coordinate change, on any time set. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_transport {f : State n → State n}
    {φ : ℝ → State n} {s : Set ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) s) :
    IsIntegralCurveOn (fun t => affineCoord T c (φ t))
      (fun _ y => transportField T c f y) s := by
  intro t ht
  show HasDerivWithinAt _ (transportField T c f (affineCoord T c (φ t))) s t
  rw [transportField_affineCoord]
  exact (T.hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)).add_const c

/-- Equilibria correspond under the affine coordinate change. -/
@[tmio T, powerlib_foundation] theorem transportField_affineCoord_eq_zero_iff
    (f : State n → State n) (x : State n) :
    transportField T c f (affineCoord T c x) = 0 ↔ f x = 0 := by
  rw [transportField_affineCoord, map_eq_zero_iff T T.injective]

@[tmio T, powerlib_foundation] theorem contDiff_transportField {f : State n → State n} {k : WithTop ℕ∞}
    (hf : ContDiff ℝ k f) : ContDiff ℝ k (transportField T c f) :=
  T.contDiff.comp (hf.comp (T.symm.contDiff.comp (contDiff_id.sub contDiff_const)))

/-- The Jacobian in the new coordinates is `T ∘ Df(x) ∘ T⁻¹`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_transportField {f : State n → State n}
    {f' : State n →L[ℝ] State n} {x : State n} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (transportField T c f)
      ((T : State n →L[ℝ] State n).comp (f'.comp (T.symm : State n →L[ℝ] State n)))
      (affineCoord T c x) := by
  have hin : HasFDerivAt (fun y => T.symm (y - c)) (T.symm : State n →L[ℝ] State n)
      (affineCoord T c x) := by
    have h := T.symm.hasFDerivAt.comp (affineCoord T c x)
      ((hasFDerivAt_id (affineCoord T c x)).sub_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hx : T.symm (affineCoord T c x - c) = x := by simp [affineCoord]
  have hf' : HasFDerivAt f f' (T.symm (affineCoord T c x - c)) := by rwa [hx]
  exact T.hasFDerivAt.comp (affineCoord T c x) (hf'.comp (affineCoord T c x) hin)

@[tmio T, powerlib_foundation] theorem fderiv_transportField {f : State n → State n} {x : State n}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (transportField T c f) (affineCoord T c x) =
      (T : State n →L[ℝ] State n).comp
        ((fderiv ℝ f x).comp (T.symm : State n →L[ℝ] State n)) :=
  (hasFDerivAt_transportField T c hf.hasFDerivAt).fderiv

end Affine

/-! ### Linear conjugation at the origin

`transportField T 0 g` is the conjugate field `y ↦ T g(T⁻¹ y)`; its sentences at the origin are
those of `g` (`holds_transport_iff T 0`). -/

section Conj

variable {T : State n ≃L[ℝ] State n}

@[tmio T, simp, powerlib_foundation] theorem transportField_zero_apply (g : State n → State n)
    (y : State n) : transportField T 0 g y = T (g (T.symm y)) := by
  simp [transportField]

@[tmio T, simp, powerlib_foundation] theorem affineCoord_zero_apply (x : State n) :
    affineCoord T 0 x = T x := by
  simp [affineCoord]

@[tmio T, simp, powerlib_foundation] theorem transportField_symm_zero (g : State n → State n) :
    transportField T.symm 0 (transportField T 0 g) = g := by
  funext y
  simp

/-- A field is the transport of `g` by `T` about the origin exactly when `T` conjugates them:
`f ∘ T = T ∘ g`. -/
@[tmio T, powerlib_foundation] theorem transportField_zero_eq_iff_comp {f g : State n → State n} :
    f = transportField T 0 g ↔ ∀ x, f (T x) = T (g x) := by
  constructor
  · rintro rfl x
    simp
  · intro h
    funext y
    rw [transportField_zero_apply, ← h, ContinuousLinearEquiv.apply_symm_apply]

end Conj

/-! ### Every sentence under affine coordinate changes -/

section Transport

variable (T : State n ≃L[ℝ] State n) (c : State n)

/-- **Transport law.** Every behavioural sentence of the library holds for `f` at `x` exactly
when it holds for the field in the coordinates `y = T x + c` at the image of `x`: the instance
`c = 1` (no time scaling) of the space-time law `holds_spaceTime_iff`. -/
@[tmio T, powerlib_foundation] theorem holds_transport_iff (P : Flow.Property) {f : State n → State n}
    {x : State n} :
    P.holds (transportField T c f) (affineCoord T c x) ↔ P.holds f x := by
  simpa only [one_smul, Flow.Property.timeScale_one] using
    holds_spaceTime_iff one_pos T c (P := P) (Or.inr rfl) (f := f) (x := x)

end Transport

/-! ### Invertible matrices as coordinate changes -/

/-- The coordinate change `x ↦ P x` for an invertible matrix `P`. -/
def matrixCoord (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P) : State n ≃L[ℝ] State n :=
  ContinuousLinearEquiv.unitsEquiv ℝ (State n)
    (hP.map (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))).unit

section MatrixCoord

variable (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P)

@[tmio T, simp, powerlib_foundation] theorem matrixCoord_apply (x : State n) :
    matrixCoord P hP x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x := rfl

@[tmio T, simp, powerlib_foundation] theorem ofLp_matrixCoord (x : State n) :
    WithLp.ofLp (matrixCoord P hP x) = P.mulVec (WithLp.ofLp x) := rfl

@[tmio T, powerlib_foundation] theorem coe_matrixCoord :
    (matrixCoord P hP : State n →L[ℝ] State n) = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P :=
  rfl

@[tmio T, powerlib_foundation] theorem coe_matrixCoord_symm :
    ((matrixCoord P hP).symm : State n →L[ℝ] State n) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P⁻¹ := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  ext1 y
  apply (matrixCoord P hP).injective
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  apply WithLp.ofLp_injective
  rw [ofLp_matrixCoord, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv P hdet, Matrix.one_mulVec]

@[tmio T, simp, powerlib_foundation] theorem matrixCoord_symm_apply (y : State n) :
    (matrixCoord P hP).symm y = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P⁻¹ y := by
  rw [← coe_matrixCoord_symm P hP, ContinuousLinearEquiv.coe_coe]

end MatrixCoord

/-! ### Sign changes of coordinates: `x ↦ (σᵢ xᵢ)ᵢ`, every `σᵢ = ±1` -/

section Sign

/-- The diagonal sign matrix `diag(σ₀, …, σₙ₋₁)` of a sign vector `σ : Fin n → ℤˣ` (every entry
`±1`). -/
def signMatrix (σ : Fin n → ℤˣ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => ((σ i : ℤ) : ℝ)

variable (σ : Fin n → ℤˣ)

/-- A sign matrix is an involution. -/
@[tmio T, powerlib_foundation] theorem signMatrix_mul_self :
    signMatrix σ * signMatrix σ = 1 := by
  rw [signMatrix, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

@[tmio T, powerlib_foundation] theorem signMatrix_isUnit : IsUnit (signMatrix σ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (signMatrix_mul_self σ))

@[tmio T, powerlib_foundation] theorem signMatrix_inv : (signMatrix σ)⁻¹ = signMatrix σ :=
  Matrix.inv_eq_left_inv (signMatrix_mul_self σ)

/-- The sign change of coordinates `x ↦ (σᵢ xᵢ)ᵢ`. -/
def signCoord : State n ≃L[ℝ] State n :=
  matrixCoord (signMatrix σ) (signMatrix_isUnit σ)

@[tmio T, simp, powerlib_foundation] theorem signCoord_apply (x : State n) :
    signCoord σ x = WithLp.toLp 2 fun i => ((σ i : ℤ) : ℝ) * x i := by
  apply WithLp.ofLp_injective
  funext i
  rw [signCoord, ofLp_matrixCoord, signMatrix, Matrix.mulVec_diagonal]

/-- A sign change of coordinates is its own inverse. -/
@[tmio T, simp, powerlib_foundation] theorem signCoord_symm : (signCoord σ).symm = signCoord σ :=
  ContinuousLinearEquiv.ext <| funext fun y => by
    rw [signCoord, matrixCoord_symm_apply, signMatrix_inv, matrixCoord_apply]

end Sign

/-! ### Scaling one coordinate: `(θ, v) ↦ (θ, η v)` -/

section Scale

open Matrix

/-- Scaling matrix `(θ, v) ↦ (θ, η v)`. -/
def scaleMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, η]

@[tmio T, powerlib_foundation] theorem scaleMatrix_isUnit {η : ℝ} (hη : η ≠ 0) :
    IsUnit (scaleMatrix η) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simpa [scaleMatrix, Matrix.det_fin_two] using hη

/-- `diag(1, η)` and `diag(1, η⁻¹)` are inverse to each other (`η ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem scaleMatrix_mul_inv {η : ℝ} (hη : η ≠ 0) :
    scaleMatrix η * scaleMatrix η⁻¹ = 1 ∧ scaleMatrix η⁻¹ * scaleMatrix η = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [scaleMatrix, hη]

@[tmio T, powerlib_foundation] private lemma scaleMatrix_inv {η : ℝ} (hη : η ≠ 0) :
    (scaleMatrix η)⁻¹ = !![1, 0; 0, η⁻¹] :=
  Matrix.inv_eq_left_inv (scaleMatrix_mul_inv hη).2

/-- The coordinate change `(θ, v) ↦ (θ, η v)`. -/
def scaleCoord {η : ℝ} (hη : η ≠ 0) : State 2 ≃L[ℝ] State 2 :=
  matrixCoord (scaleMatrix η) (scaleMatrix_isUnit hη)

@[tmio T, simp, powerlib_foundation] theorem scaleCoord_apply {η : ℝ} (hη : η ≠ 0) (x : State 2) :
    scaleCoord hη x = WithLp.toLp 2 ![x 0, η * x 1] := by
  ext i
  fin_cases i <;>
    simp [scaleCoord, scaleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[tmio T, simp, powerlib_foundation] theorem scaleCoord_symm_apply {η : ℝ} (hη : η ≠ 0) (y : State 2) :
    (scaleCoord hη).symm y = WithLp.toLp 2 ![y 0, y 1 / η] := by
  ext i
  fin_cases i <;>
    simp [scaleCoord, scaleMatrix_inv hη, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      div_eq_inv_mul]

end Scale

/-! ### Time scaling -/

section TimeScale

/-- **Time scaling law.** For `c > 0`, every behavioural sentence `P` other than sampled
contraction holds for `f` at `x` exactly when its time-scaled form `P.timeScale c` holds for
`c • f` (the field in the time `τ = t / c`): Lyapunov stability, instability, local and global
asymptotic and exponential stability and conservation are invariant, and decay at the rate `a`
is decay at the rate `c a`. The instance `T = 1`, `b = 0` of the space-time law
`holds_spaceTime_iff`; sampled contraction: `sampledContraction_spaceTime_iff`. -/
@[tmio T, powerlib_foundation] theorem holds_timeScale_iff {f : State n → State n} {x : State n} {c : ℝ}
    (hc : 0 < c) {P : Flow.Property} (hP : P ≠ .contractive) :
    (P.timeScale c).holds (c • f) x ↔ P.holds f x := by
  have h := holds_spaceTime_iff hc (ContinuousLinearEquiv.refl ℝ (State n)) 0 (Or.inl hP)
    (f := f) (x := x)
  have hf : transportField (ContinuousLinearEquiv.refl ℝ (State n)) 0 f = f := by
    funext y
    simp [transportField]
  have hx : affineCoord (ContinuousLinearEquiv.refl ℝ (State n)) 0 x = x := by
    simp [affineCoord]
  rwa [hf, hx] at h

/-- **Time scaling of linear fields.** For `c > 0` every flow sentence `P` holds for the linear
field of `A` at its centre exactly when `P.timeScale c` holds for the linear field of `c A`;
sampled contraction is invariant here, since for linear fields it is the Hurwitz property. -/
@[tmio T, powerlib_foundation] theorem holds_timeScale_linear_iff {c : ℝ} (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℝ) (e : State n) (P : Flow.Property) :
    (P.timeScale c).holds (LinearSystems.affineLinearVectorField (c • A) e) e ↔
      P.holds (LinearSystems.affineLinearVectorField A e) e := by
  have hfield : LinearSystems.affineLinearVectorField (c • A) e =
      c • LinearSystems.affineLinearVectorField A e := by
    funext y
    simp [LinearSystems.affineLinearVectorField]
  by_cases hP : P = .contractive
  · subst hP
    change Flow.SampledContraction _ e ↔ Flow.SampledContraction _ e
    rw [Linear.sampledContraction_iff_isHurwitz, Linear.sampledContraction_iff_isHurwitz,
      ← Linear.holds_iff_isHurwitz e Flow.Property.attractive_locallyExponentiallyStable,
      ← Linear.holds_iff_isHurwitz e Flow.Property.attractive_locallyExponentiallyStable, hfield]
    exact holds_timeScale_iff hc (P := .locallyExponentiallyStable) fun h => by cases h
  · rw [hfield]
    exact holds_timeScale_iff hc hP

end TimeScale

end powerlib.Dynamics

/-! ### Linear fields in matrix coordinates

The linear field of `T A S` (`T S = S T = 1`) is the field of `A` in the coordinates `x' = T x`
(`matrixCoord T`), so every sentence at the origin is read through the transport law. -/

namespace powerlib.Linear

open LinearSystems

variable {n p : ℕ}

/-- A coordinate change preserves every behavioural sentence at the origin: the linear field of
`T A S` is the transport of that of `A` by `x' = T x` (`Dynamics.holds_transport_iff`). -/
@[tmio T, powerlib_foundation] theorem holds_conj (P : Flow.Property)
    {T S : Matrix (Fin n) (Fin n) ℝ} (hTS : T * S = 1) (hST : S * T = 1)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    P.holds (affineLinearVectorField (T * A * S) 0) 0 ↔
      P.holds (affineLinearVectorField A 0) 0 := by
  have hT : IsUnit T :=
    (Matrix.isUnit_iff_isUnit_det T).mpr (Matrix.isUnit_det_of_left_inverse hST)
  have hf : affineLinearVectorField (T * A * S) 0 =
      Dynamics.transportField (Dynamics.matrixCoord T hT) 0 (affineLinearVectorField A 0) := by
    funext y
    rw [Dynamics.transportField_zero_apply, Dynamics.matrixCoord_symm_apply,
      Matrix.inv_eq_right_inv hTS, affine_apply, affine_apply, sub_zero, sub_zero, op_mul_apply,
      op_mul_apply]
    rfl
  have h := Dynamics.holds_transport_iff (Dynamics.matrixCoord T hT) 0 P
    (f := affineLinearVectorField A 0) (x := 0)
  rw [Dynamics.affineCoord_zero_apply, map_zero] at h
  rw [hf, h]

/-- Similar plants of the same dimension satisfy the same behavioural sentences. -/
@[tmio T, powerlib_foundation] theorem Similar.holds_iff {m m' : Plant n p} (h : Similar m m')
    (P : Flow.Property) :
    P.holds (affineLinearVectorField m'.A 0) 0 ↔ P.holds (affineLinearVectorField m.A 0) 0 := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  exact holds_conj P hTS hST m.A

end powerlib.Linear
