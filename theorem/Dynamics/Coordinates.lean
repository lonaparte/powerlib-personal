import theorem.Dynamics.State

/-! # Coordinates on `Dynamics.State n`

Calculus utilities on the Euclidean state space `Dynamics.State n = EuclideanSpace ℝ (Fin n)`.
The linearization theorems (`Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian`,
`Criteria.locallyExponentiallyStable_of_jacobian_fin_two`, …) take a field
`f : Dynamics.State n → Dynamics.State n` (`EuclideanSpace ℝ (Fin n)`), the hypothesis
`ContDiff ℝ 1 f`, and the identification
`fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A`; this module reduces both to the
scalar component functions `fun y => f y i`.

Scope.
* Every statement is generic calculus about an arbitrary field or about the explicit example
  fields; no model is fixed, no model family is involved and no behavioural sentence is stated
  (foundation results, Rules §3).

Source: library infrastructure (no work-sync note): the shared criteria interface of the
work-sync formalization.

Results.
* `hasFDerivAt_toEuclideanCLM_of_components` / `fderiv_eq_toEuclideanCLM_of_components`:
  if each component has derivative `L i` with `L i v = ∑ j, A i j * v j`, the Jacobian is `A`
  (any dimension); `toEuclideanCLM_apply`: a matrix acts on a state coordinatewise,
  `(A v) i = ∑ j, A i j * v j` (any dimension); `toEuclideanCLM_injective_fin_two`: a planar
  Jacobian determines its matrix.
* `coord`, `hasFDerivAt_coord`, `contDiff_coord` (`fun_prop`): coordinates are smooth linear maps.
* `contDiff_of_components`: smoothness of `f` from smoothness of its components.
* `contDiff_field_mk_two_example`: a `fun_prop` demonstration for a planar field built from
  `Real.sin` / `Real.cos` (pendulum / swing / PLL shape); `fderiv_field_mk_two_example_zero`
  computes the Jacobian of such a field with the component helper.
* Three states: `mk3` (the state `(a, b, c)`, with `mk3_zero`, `mk3_one`, `mk3_two`),
  `state3_ext` (extensionality by coordinates), `toEuclideanCLM_apply3` (the instance of
  `toEuclideanCLM_apply` for a `3 × 3` matrix).
* `lift F`: a field on plain coordinates `Fin n → ℝ` transported to `Dynamics.State n`; its
  Fréchet derivative is `toEuclideanCLM A` whenever the coordinate field has derivative
  `toLin' A` (`hasFDerivAt_lift`, `fderiv_lift`, `contDiff_lift`); `hasFDerivAt_of_eq` replaces a
  function and its derivative by provably equal ones.
* Norms and coordinates: `abs_apply_le_norm`, `abs_coord_sub_le`, `norm_le_sum_abs` with its
  instances `norm_le_abs_add_abs_two`, `norm_le_abs_add_abs_three`, `sqrt_sq_add_sq_le`, and the
  projection
  removing one coordinate (`norm_sub_smul_single_le`, `norm_le_norm_sub_smul_single_add`).
* Curves in `State n`: `fderiv_apply_eq_of_hasDerivAt_line` (a directional derivative is the
  derivative along the line), `hasDerivWithinAt_euclidean_of_coord`,
  `HasDerivWithinAt.euclidean_coord`, `tendsto_euclidean_of_coord` (curves are differentiated,
  and converge, coordinatewise); `hasDerivAt_of_coords`, `hasDerivAt_iff_coords` (the same for
  `HasDerivAt`).
-/

noncomputable section
namespace powerlib.Dynamics

section Jacobian

open Matrix

variable {n : ℕ}

/-- The `i`-th coordinate of `Dynamics.State n` as a continuous linear functional. -/
def coord (i : Fin n) : Dynamics.State n →L[ℝ] ℝ := EuclideanSpace.proj i

@[simp, powerlib_foundation] theorem coord_apply (i : Fin n) (x : Dynamics.State n) :
    coord i x = x i := rfl

@[powerlib_foundation] theorem hasFDerivAt_coord (i : Fin n) (x : Dynamics.State n) :
    HasFDerivAt (fun y : Dynamics.State n => y i) (coord i) x :=
  (coord i).hasFDerivAt

@[fun_prop, powerlib_foundation] theorem contDiff_coord {k : WithTop ℕ∞} (i : Fin n) :
    ContDiff ℝ k (fun y : Dynamics.State n => y i) :=
  (coord i).contDiff

/-- Componentwise derivatives determine the Jacobian matrix (any dimension). -/
@[powerlib_foundation] theorem hasFDerivAt_toEuclideanCLM_of_components
    {f : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n}
    (A : Matrix (Fin n) (Fin n) ℝ) (L : Fin n → Dynamics.State n →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivAt (fun y => f y i) (L i) x)
    (hA : ∀ i (v : Dynamics.State n), L i v = ∑ j, A i j * v j) :
    HasFDerivAt f (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  convert hL i using 1
  ext v
  simp [hA, Matrix.mulVec, dotProduct]

@[powerlib_foundation] theorem fderiv_eq_toEuclideanCLM_of_components
    {f : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n}
    (A : Matrix (Fin n) (Fin n) ℝ) (L : Fin n → Dynamics.State n →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivAt (fun y => f y i) (L i) x)
    (hA : ∀ i (v : Dynamics.State n), L i v = ∑ j, A i j * v j) :
    fderiv ℝ f x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A :=
  (hasFDerivAt_toEuclideanCLM_of_components A L hL hA).fderiv

/-- A matrix acts on a state coordinatewise (any dimension). -/
@[powerlib_foundation] theorem toEuclideanCLM_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Dynamics.State n) (i : Fin n) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A v) i = ∑ j, A i j * v j := by
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]

@[powerlib_foundation] theorem toEuclideanCLM_injective_fin_two :
    Function.Injective (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) :=
  Matrix.toEuclideanCLM.injective

/-- Smoothness of a field on `Dynamics.State n` from smoothness of its components. -/
@[powerlib_foundation] theorem contDiff_of_components {f : Dynamics.State n → Dynamics.State n}
    {k : WithTop ℕ∞} (h : ∀ i, ContDiff ℝ k (fun y => f y i)) : ContDiff ℝ k f :=
  contDiff_euclidean.2 h

/-- `fun_prop` demonstration: a planar field with trigonometric terms (the shape of a
pendulum, swing equation or reduced PLL in `(angle, rate)` coordinates) is smooth. -/
@[powerlib_foundation] theorem contDiff_field_mk_two_example (a b c d : ℝ) :
    ContDiff ℝ 1 (fun y : Dynamics.State 2 =>
      (WithLp.toLp 2 ![y 1, c - a * Real.sin (y 0) - b * y 1 + d * Real.cos (y 0)] :
        Dynamics.State 2)) := by
  apply contDiff_of_components
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- Worked use of `fderiv_eq_toEuclideanCLM_of_components`: the planar field
`(y₀, y₁) ↦ (y₁, -a sin y₀ - b y₁)` has Jacobian `!![0, 1; -a, -b]` at the origin. -/
@[powerlib_foundation] theorem fderiv_field_mk_two_example_zero (a b : ℝ) :
    fderiv ℝ (fun y : Dynamics.State 2 =>
        (WithLp.toLp 2 ![y 1, -a * Real.sin (y 0) - b * y 1] : Dynamics.State 2)) 0 =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![0, 1; -a, -b] := by
  refine fderiv_eq_toEuclideanCLM_of_components _ ![coord 1, (-a) • coord 0 - b • coord 1]
    ?_ ?_
  · intro i
    fin_cases i
    · simpa using hasFDerivAt_coord (1 : Fin 2) (0 : Dynamics.State 2)
    · have h := (((Real.hasDerivAt_sin _).comp_hasFDerivAt (0 : Dynamics.State 2)
        (hasFDerivAt_coord (0 : Fin 2) 0)).const_mul (-a)).sub
        ((hasFDerivAt_coord (1 : Fin 2) (0 : Dynamics.State 2)).const_mul b)
      convert h using 1
      · funext y
        simp
      · ext v
        simp
  · intro i v
    fin_cases i <;> simp [Fin.sum_univ_two]
    ring

/-- The reciprocal of a coordinate, `y ↦ (y i)⁻¹`, at a point where the coordinate is nonzero. -/
@[powerlib_foundation] theorem hasFDerivAt_inv_coord (i : Fin n) {x : Dynamics.State n}
    (hx : x i ≠ 0) :
    HasFDerivAt (fun y : Dynamics.State n => (y i)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((x i) ^ 2)⁻¹)).comp (coord i)) x :=
  (hasFDerivAt_inv hx).comp x (hasFDerivAt_coord i x)

end Jacobian

/-! ## Three-dimensional states -/

section Three

open Matrix

/-- The state `(a, b, c)`. -/
def mk3 (a b c : ℝ) : State 3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![a, b, c]

@[simp, powerlib_foundation] theorem mk3_zero (a b c : ℝ) : mk3 a b c 0 = a := by simp [mk3]
@[simp, powerlib_foundation] theorem mk3_one (a b c : ℝ) : mk3 a b c 1 = b := by simp [mk3]
@[simp, powerlib_foundation] theorem mk3_two (a b c : ℝ) : mk3 a b c 2 = c := by simp [mk3]

@[powerlib_foundation] theorem state3_ext {x y : State 3} (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

@[powerlib_foundation] theorem toEuclideanCLM_apply3 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (v : State 3) (i : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A v) i =
      A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 := by
  rw [toEuclideanCLM_apply, Fin.sum_univ_three]

end Three

/-! ## Fields on plain coordinates -/

section Lift

open Set Filter Topology Matrix

variable {n : ℕ}

/-- A field on plain coordinates, transported to `Dynamics.State n`. -/
def lift (F : (Fin n → ℝ) → (Fin n → ℝ)) (x : Dynamics.State n) : Dynamics.State n :=
  WithLp.toLp 2 (F (WithLp.ofLp x))

@[simp, powerlib_foundation] theorem lift_toLp (F : (Fin n → ℝ) → (Fin n → ℝ))
    (v : Fin n → ℝ) : lift F (WithLp.toLp 2 v) = WithLp.toLp 2 (F v) := rfl

@[powerlib_foundation] theorem lift_toLp_eq_zero {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {v : Fin n → ℝ} (h : F v = 0) : lift F (WithLp.toLp 2 v) = 0 := by
  rw [lift_toLp, h]
  rfl

@[powerlib_foundation] theorem hasFDerivAt_lift {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} {x : Dynamics.State n}
    (h : HasFDerivAt F (Matrix.toLin' A).toContinuousLinearMap (WithLp.ofLp x)) :
    HasFDerivAt (lift F) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have h1 : HasFDerivAt (fun y : Dynamics.State n => F (e y))
      ((Matrix.toLin' A).toContinuousLinearMap.comp (e : Dynamics.State n →L[ℝ] (Fin n → ℝ)))
      x := h.comp x e.hasFDerivAt
  have h2 := (e.symm.hasFDerivAt (x := F (e x))).comp x h1
  have hfun : lift F = (⇑e.symm ∘ fun y => F (e y)) := rfl
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext v i
  simp [e]
  rfl

@[powerlib_foundation] theorem fderiv_lift {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} {x : Dynamics.State n}
    (h : HasFDerivAt F (Matrix.toLin' A).toContinuousLinearMap (WithLp.ofLp x)) :
    fderiv ℝ (lift F) x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A :=
  (hasFDerivAt_lift h).fderiv

@[powerlib_foundation] theorem contDiff_lift {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {k : WithTop ℕ∞} (h : ContDiff ℝ k F) : ContDiff ℝ k (lift F) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  exact e.symm.contDiff.comp (h.comp e.contDiff)

/-- Replace a function and its derivative by provably equal ones. -/
@[powerlib_foundation] theorem hasFDerivAt_of_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g g' : E → ℝ} {L L' : E →L[ℝ] ℝ} {y : E} (h : HasFDerivAt g L y)
    (hg : ∀ z, g' z = g z) (hL : L = L') : HasFDerivAt g' L' y := by
  rw [show g' = g from funext hg, ← hL]
  exact h

@[powerlib_foundation] theorem abs_coord_sub_le (x y : Dynamics.State n) (i : Fin n) :
    |y i - x i| ≤ ‖y - x‖ := by
  have := PiLp.norm_apply_le (y - x) i
  simpa [Real.norm_eq_abs] using this

end Lift

/-! ## Norms and coordinates -/

section Blocks

variable {m k : ℕ}

/-- A state of `ℝ^{m+k}` is determined by its two blocks of coordinates. -/
@[powerlib_foundation] theorem state_ext_blocks {z z' : State (m + k)}
    (h₁ : ∀ i : Fin m, z (Fin.castAdd k i) = z' (Fin.castAdd k i))
    (h₂ : ∀ j : Fin k, z (Fin.natAdd m j) = z' (Fin.natAdd m j)) : z = z' := by
  ext r
  refine Fin.addCases (fun i => ?_) (fun j => ?_) r
  · exact h₁ i
  · exact h₂ j

end Blocks

section Norms

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A coordinate is bounded by the norm. -/
@[powerlib_foundation] theorem abs_apply_le_norm (x : ℝⁿ) (i : Fin n) : |x i| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le x i

/-- The norm of a vector of `State n` is at most the sum of the absolute values of its
coordinates. -/
@[powerlib_foundation] theorem norm_le_sum_abs (v : State n) : ‖v‖ ≤ ∑ i, |v i| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

/-- The Euclidean norm of a planar state is bounded by the sum of the absolute coordinates. -/
@[powerlib_foundation] theorem norm_le_abs_add_abs_two (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ≤ |x 0| + |x 1| :=
  (norm_le_sum_abs x).trans_eq (Fin.sum_univ_two _)

/-- The Euclidean norm of a three-dimensional state is bounded by the sum of the absolute
coordinates. -/
@[powerlib_foundation] theorem norm_le_abs_add_abs_three (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ≤ |x 0| + |x 1| + |x 2| :=
  (norm_le_sum_abs x).trans_eq (Fin.sum_univ_three _)

/-- The coordinate projection killing the `k`-th coordinate does not increase the norm. -/
@[powerlib_foundation] theorem norm_sub_smul_single_le (k : Fin n) (v : State n) :
    ‖v - v k • EuclideanSpace.single k (1 : ℝ)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = k
  · subst hi; simp [sq_nonneg]
  · simp [hi]

/-- A vector is bounded by its part off the `k`-th coordinate plus that coordinate. -/
@[powerlib_foundation] theorem norm_le_norm_sub_smul_single_add (k : Fin n) (v : State n) :
    ‖v‖ ≤ ‖v - v k • EuclideanSpace.single k (1 : ℝ)‖ + |v k| := by
  have h := norm_add_le (v - v k • EuclideanSpace.single k (1 : ℝ))
    (v k • EuclideanSpace.single k (1 : ℝ))
  rw [sub_add_cancel, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs] at h
  exact h

/-- `√(a² + b²) ≤ |a| + |b|`. -/
@[powerlib_foundation] theorem sqrt_sq_add_sq_le (a b : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

end Norms

/-! ## Curves in `State n` -/

section Curves

open Set Filter Topology Metric

/-- The derivative of a differentiable map in a direction is the derivative along the line. -/
@[powerlib_foundation] theorem fderiv_apply_eq_of_hasDerivAt_line {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {P : State n → F} {x v : State n} {d : F}
    (hP : DifferentiableAt ℝ P x) (h : HasDerivAt (fun t : ℝ => P (x + t • v)) d 0) :
    fderiv ℝ P x v = d := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hP' : HasFDerivAt P (fderiv ℝ P x) (x + (0 : ℝ) • v) := by
    simpa using hP.hasFDerivAt
  exact (hP'.comp_hasDerivAt (0 : ℝ) hl).unique h

/-- A curve in `State n` has the derivative whose coordinates are the derivatives of its
coordinates. -/
@[powerlib_foundation] theorem hasDerivWithinAt_euclidean_of_coord {n : ℕ} {φ : ℝ → State n}
    {φ' : State n} {s : Set ℝ} {t : ℝ}
    (h : ∀ i, HasDerivWithinAt (fun τ => φ τ i) (φ' i) s t) : HasDerivWithinAt φ φ' s t := by
  have h1 : HasDerivWithinAt (fun τ => (φ τ).ofLp) φ'.ofLp s t := hasDerivWithinAt_pi.mpr h
  have h2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.hasFDerivAt.comp_hasDerivWithinAt
      t h1
  have e :
      (⇑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm ∘ fun τ => (φ τ).ofLp) = φ := by
    funext τ
    simp
  rw [e] at h2
  simpa using h2

/-- The coordinates of a curve in `State n` have the coordinates of its derivative. -/
@[powerlib_foundation] theorem HasDerivWithinAt.euclidean_coord {n : ℕ} {φ : ℝ → State n}
    {φ' : State n} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt φ φ' s t) (i : Fin n) :
    HasDerivWithinAt (fun τ => φ τ i) (φ' i) s t :=
  (PiLp.proj 2 (fun _ : Fin n => ℝ) i : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

/-- A family in `State n` converges when every coordinate converges. -/
@[powerlib_foundation] theorem tendsto_euclidean_of_coord {n : ℕ} {α : Type*} {l : Filter α}
    {φ : α → State n} {y : State n} (h : ∀ i, Tendsto (fun t => φ t i) l (𝓝 (y i))) :
    Tendsto φ l (𝓝 y) := by
  have h1 : Tendsto (fun t => (φ t).ofLp) l (𝓝 y.ofLp) := tendsto_pi_nhds.mpr h
  have h2 := ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).tendsto y.ofLp).comp h1
  simpa [Function.comp_def] using h2

end Curves

/-! ## Curves in `ℝⁿ` through `HasDerivAt` -/

section CurvesAt

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Coordinatewise derivatives give the derivative of a curve in `ℝⁿ`. -/
@[powerlib_foundation] theorem hasDerivAt_of_coords {x : ℝ → ℝⁿ} {v : ℝⁿ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s => x s i) (v i) t) : HasDerivAt x v t := by
  have hpi : HasDerivAt (fun s => WithLp.ofLp (x s)) (WithLp.ofLp v) t := hasDerivAt_pi.2 h
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
    t hpi
  simpa [Function.comp_def] using h2

/-- A curve in `ℝⁿ` has the derivative `v` iff each coordinate has the derivative `v i`. -/
@[powerlib_foundation] theorem hasDerivAt_iff_coords {x : ℝ → ℝⁿ} {v : ℝⁿ} {t : ℝ} :
    HasDerivAt x v t ↔ ∀ i, HasDerivAt (fun s => x s i) (v i) t :=
  ⟨fun h i => (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h,
    hasDerivAt_of_coords⟩

end CurvesAt

end powerlib.Dynamics
