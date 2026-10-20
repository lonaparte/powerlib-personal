import theorem.PhasePlane.Planar

/-! # Bogdanov–Takens: Jordan structure and the truncated normal form

Linear algebra of the double-zero eigenvalue and equilibrium-level facts of the truncated planar
Bogdanov–Takens normal form.

Model boundary.
* Linear algebra: any real `2 × 2` matrix `J`.
* Truncated BT normal form: state `y = (y₁, y₂) = (y 0, y 1)` in `State 2`, constant parameters
  `β₁, β₂` and coefficients `a, b`, continuous time, no remainder term:
  `ẏ₁ = y₂`, `ẏ₂ = β₁ + β₂ y₁ + a y₁² + b y₁ y₂`. Conclusions are about equilibria, their
  Jacobians and the local stability of hyperbolic equilibria; the homoclinic curve `P` and the
  limit-cycle statements of the source note are not formalized.
* A truncated normal form, not an engineering model, so no model family is defined; all results
  remain public foundation support. Behaviour is LeanForControl's predicates and the
  linearization theorems of `powerlib.Criteria` / `powerlib.Flow`.

Source: work-sync theory/T-bogdanov-takens-bifurcation.md §1.1–1.5 (§1.6, the GFL-PLL model, is
not included).

Results.
* `trace_det_zero_iff_similar_jordanBlock`: `tr J = det J = 0 ∧ J ≠ 0` iff `J` is similar to the
  single Jordan block `!![0, 1; 0, 0]` (`jordanBlock`; `J P = P N` with `det P ≠ 0`); together
  with `powerlib.Criteria` this is also equivalent to `J` being nonzero nilpotent
  (`isNilpotent_ne_zero_iff_similar_jordanBlock`).
* Structural form `!![g₁, g₂; g₃, 0]`: `tr = g₁`, `det = −g₂ g₃` (`structural_trace_det`). For the
  special shape `!![k g, κ; g, 0]` with `κ ≠ 0` both vanish exactly at `g = 0`, where the matrix is
  a single Jordan block (`proportional_trace_det_zero_iff`, `proportional_jordan_at_zero`).
* Equilibria (`field_eq_zero_iff`): `y₂ = 0` and `a y₁² + β₂ y₁ + β₁ = 0`; one exists iff
  `β₂² − 4 a β₁ ≥ 0` (`a ≠ 0`, `exists_equilibrium_iff`), and the equilibrium is unique iff
  `(β₁, β₂)` lies on the curve `T : β₂² = 4 a β₁` (`existsUnique_equilibrium_iff`), in which case
  it is `y₁ = −β₂ / (2a)` (`equilibrium_on_T_iff`) and its Jacobian is singular
  (`det_jacobian_on_T`).
* Jacobian at `(y₁, 0)`: `!![0, 1; β₂ + 2 a y₁, b y₁]`, `tr = b y₁`, `det = −(β₂ + 2 a y₁)`
  (`fderiv_field`, `trace_jacobian`, `det_jacobian`).
* (`b ≠ 0`) an equilibrium with `tr = 0, det > 0` exists iff `β₁ = 0 ∧ β₂ < 0` (the Hopf line
  `H`, `hopf_condition_iff`); `tr = det = 0` at an equilibrium iff `β₁ = β₂ = 0` and the
  equilibrium is the origin (`bt_point_iff`), whose Jacobian is the Jordan block
  (`jacobian_bt_point`).
* Equilibria with `β₂ + 2 a y₁ > 0` are saddles (unstable, `saddle_unstable`); with
  `β₂ + 2 a y₁ < 0` and `b y₁ < 0` they are locally exponentially stable
  (`node_or_focus_stable`).

Corrections. (T-bogdanov-takens-bifurcation §1.3(a)): on `T` the equilibrium is the double root
`y₁ = −β₂ / (2a)`, not `y₁ = ±√(|β₁| / a)` (`equilibrium_on_T_iff`). The sign of the first
Lyapunov coefficient and the region table (sign `l₁ = sign(a b)` versus the stability labels)
are not formalized here.
-/

noncomputable section
namespace powerlib.NormalForm.BogdanovTakens
open Set Matrix
open powerlib.Dynamics (State)
open powerlib.PhasePlane

/-! ## The double-zero Jordan block -/

/-- The single `2 × 2` Jordan block with eigenvalue `0`. -/
def jordanBlock : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

@[powerlib_foundation] theorem jordanBlock_sq : jordanBlock ^ 2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jordanBlock, pow_two]

@[powerlib_foundation] theorem jordanBlock_ne_zero : jordanBlock ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [jordanBlock] at this

@[powerlib_foundation] theorem trace_jordanBlock : jordanBlock.trace = 0 := by
  simp [jordanBlock, Matrix.trace_fin_two]

@[powerlib_foundation] theorem det_jordanBlock : jordanBlock.det = 0 := by
  simp [jordanBlock, Matrix.det_fin_two]

/-- A real `2 × 2` matrix has `tr = det = 0` and is nonzero iff it is similar to the single
Jordan block. -/
@[powerlib_foundation] theorem trace_det_zero_iff_similar_jordanBlock
    (J : Matrix (Fin 2) (Fin 2) ℝ) :
    (J.trace = 0 ∧ J.det = 0 ∧ J ≠ 0) ↔
      ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧ J * P = P * jordanBlock := by
  constructor
  · rintro ⟨htr, hdet, hJ⟩
    rw [Matrix.trace_fin_two] at htr
    rw [Matrix.det_fin_two] at hdet
    by_cases hcol : J 0 1 = 0 ∧ J 1 1 = 0
    · obtain ⟨hb, hd⟩ := hcol
      have ha : J 0 0 = 0 := by linarith
      have hc : J 1 0 ≠ 0 := by
        intro hc; apply hJ
        ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
      refine ⟨!![0, 1; J 1 0, 0], by simp [Matrix.det_fin_two, hc], ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [jordanBlock, Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hd]
    · have hb : J 0 1 ≠ 0 := by
        intro hb
        have hd : J 1 1 ≠ 0 := fun hd => hcol ⟨hb, hd⟩
        have : J 0 0 * J 1 1 = 0 := by rw [hb, zero_mul, sub_zero] at hdet; exact hdet
        have ha : J 0 0 = 0 := (mul_eq_zero.mp this).resolve_right hd
        exact hd (by linarith)
      refine ⟨!![J 0 1, 0; J 1 1, 1], by simp [Matrix.det_fin_two, hb], ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [jordanBlock, Matrix.mul_apply, Fin.sum_univ_two]
      · have : J 0 0 = -J 1 1 := by linarith
        rw [this]; ring
      · have : J 0 0 = -J 1 1 := by linarith
        rw [this] at hdet
        nlinarith
  · rintro ⟨P, hP, hJP⟩
    have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
    have hJ : J = P * jordanBlock * P⁻¹ := by
      calc J = J * P * P⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv P hu, Matrix.mul_one]
        _ = P * jordanBlock * P⁻¹ := by rw [hJP]
    refine ⟨?_, ?_, ?_⟩
    · rw [hJ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hu,
        Matrix.one_mul, trace_jordanBlock]
    · have := congrArg Matrix.det hJP
      rw [Matrix.det_mul, Matrix.det_mul, det_jordanBlock, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hP
    · intro h0
      apply jordanBlock_ne_zero
      have : P * jordanBlock = 0 := by rw [← hJP, h0, Matrix.zero_mul]
      calc jordanBlock = P⁻¹ * (P * jordanBlock) := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hu, Matrix.one_mul]
        _ = 0 := by rw [this, Matrix.mul_zero]

/-- Equivalently: `J` is nonzero nilpotent iff it is similar to the single Jordan block. -/
@[powerlib_foundation] theorem isNilpotent_ne_zero_iff_similar_jordanBlock
    (J : Matrix (Fin 2) (Fin 2) ℝ) :
    (IsNilpotent J ∧ J ≠ 0) ↔
      ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧ J * P = P * jordanBlock := by
  rw [Criteria.isNilpotent_iff_trace_det_eq_zero_fin_two, and_assoc]
  exact trace_det_zero_iff_similar_jordanBlock J

/-! ## Structural trace / determinant formulas -/

@[powerlib_foundation] theorem structural_trace_det (g₁ g₂ g₃ : ℝ) :
    (!![g₁, g₂; g₃, 0] : Matrix (Fin 2) (Fin 2) ℝ).trace = g₁ ∧
      (!![g₁, g₂; g₃, 0] : Matrix (Fin 2) (Fin 2) ℝ).det = -(g₂ * g₃) := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]

/-- For `!![k g, κ; g, 0]` with `κ ≠ 0`, trace and determinant are both proportional to `g`
and vanish together exactly at `g = 0`. -/
@[powerlib_foundation] theorem proportional_trace_det_zero_iff {k κ g : ℝ} (hκ : κ ≠ 0) :
    ((!![k * g, κ; g, 0] : Matrix (Fin 2) (Fin 2) ℝ).trace = 0 ∧
      (!![k * g, κ; g, 0] : Matrix (Fin 2) (Fin 2) ℝ).det = 0) ↔ g = 0 := by
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨-, h⟩
    have : κ * g = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hκ
  · rintro rfl; simp

/-- At `g = 0` the proportional structure is a single Jordan block when `κ ≠ 0`. -/
@[powerlib_foundation] theorem proportional_jordan_at_zero {k κ : ℝ} (hκ : κ ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      (!![k * 0, κ; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * P = P * jordanBlock := by
  apply (trace_det_zero_iff_similar_jordanBlock _).mp
  refine ⟨by simp [Matrix.trace_fin_two], by simp [Matrix.det_fin_two], ?_⟩
  intro h
  have := congrFun (congrFun h 0) 1
  simp at this
  exact hκ this

/-! ## The truncated normal form -/

/-- Unfolding parameters `β₁, β₂` and normal-form coefficients `a, b`. -/
structure Params where
  β₁ : ℝ
  β₂ : ℝ
  a : ℝ
  b : ℝ

/-- `ẏ₁ = y₂`, `ẏ₂ = β₁ + β₂ y₁ + a y₁² + b y₁ y₂`. -/
def field (p : Params) (y : State 2) : State 2 :=
  mk (y 1) (p.β₁ + p.β₂ * y 0 + p.a * y 0 ^ 2 + p.b * y 0 * y 1)

/-- Jacobian of the truncated normal form at `(y₁, y₂)`. -/
def jacobian (p : Params) (y₁ y₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; p.β₂ + 2 * p.a * y₁ + p.b * y₂, p.b * y₁]

@[powerlib_foundation] theorem field_contDiff (p : Params) {k : WithTop ℕ∞} :
    ContDiff ℝ k (field p) := by
  refine Dynamics.contDiff_of_components (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simpa [field] using Dynamics.contDiff_coord (n := 2) 1
  · simp only [field, mk_apply_one]; fun_prop

@[powerlib_foundation] theorem hasFDerivAt_field (p : Params) (y : State 2) :
    HasFDerivAt (field p)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian p (y 0) (y 1))) y := by
  refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
    ![Dynamics.coord 1,
      (p.β₂ + 2 * p.a * y 0 + p.b * y 1) • Dynamics.coord 0 + (p.b * y 0) • Dynamics.coord 1]
    ?_ ?_
  · intro i; fin_cases i
    · show HasFDerivAt (fun y => field p y 0) (Dynamics.coord 1) y
      simpa [field] using Dynamics.hasFDerivAt_coord 1 y
    · show HasFDerivAt (fun y => field p y 1)
        ((p.β₂ + 2 * p.a * y 0 + p.b * y 1) • Dynamics.coord 0 + (p.b * y 0) • Dynamics.coord 1) y
      have h0 := Dynamics.hasFDerivAt_coord 0 y
      have h1 := Dynamics.hasFDerivAt_coord 1 y
      have h : HasFDerivAt
          (fun x : State 2 => p.β₁ + p.β₂ * x 0 + p.a * x 0 ^ 2 + p.b * x 0 * x 1) _ y :=
        ((((hasFDerivAt_const p.β₁ y).add (h0.const_mul p.β₂)).add
          ((h0.pow 2).const_mul p.a)).add ((h0.const_mul p.b).mul h1))
      have hf : (fun x => field p x 1) =
          fun x : State 2 => p.β₁ + p.β₂ * x 0 + p.a * x 0 ^ 2 + p.b * x 0 * x 1 := by
        funext x; simp [field]
      rw [hf]
      convert h using 1
      ext v
      simp
      ring
  · intro i v; rw [Fin.sum_univ_two]; fin_cases i <;> simp [jacobian]

@[powerlib_foundation] theorem fderiv_field (p : Params) (y : State 2) :
    fderiv ℝ (field p) y = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian p (y 0) (y 1)) :=
  (hasFDerivAt_field p y).fderiv

@[powerlib_foundation] theorem field_eq_zero_iff (p : Params) (y : State 2) :
    field p y = 0 ↔ y 1 = 0 ∧ p.a * y 0 ^ 2 + p.β₂ * y 0 + p.β₁ = 0 := by
  rw [field, mk_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1] at h2; linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1]; linarith⟩

/-- An equilibrium exists iff the discriminant `β₂² − 4 a β₁` is nonnegative. -/
@[powerlib_foundation] theorem exists_equilibrium_iff (p : Params) (ha : p.a ≠ 0) :
    (∃ y, field p y = 0) ↔ 0 ≤ p.β₂ ^ 2 - 4 * p.a * p.β₁ := by
  constructor
  · rintro ⟨y, hy⟩
    rw [field_eq_zero_iff] at hy
    have : p.β₂ ^ 2 - 4 * p.a * p.β₁ = (2 * p.a * y 0 + p.β₂) ^ 2 := by
      linear_combination (-4 * p.a) * hy.2
    rw [this]; exact sq_nonneg _
  · intro hd
    set s := √(p.β₂ ^ 2 - 4 * p.a * p.β₁)
    have hs : s ^ 2 = p.β₂ ^ 2 - 4 * p.a * p.β₁ := Real.sq_sqrt hd
    refine ⟨mk ((-p.β₂ + s) / (2 * p.a)) 0, ?_⟩
    rw [field_eq_zero_iff]
    refine ⟨rfl, ?_⟩
    simp only [mk_apply_zero]
    field_simp
    nlinarith [hs]

/-- On the saddle-node curve `T : β₂² = 4 a β₁` the unique equilibrium is `(−β₂ / (2a), 0)`. -/
@[powerlib_foundation] theorem equilibrium_on_T_iff (p : Params) (ha : p.a ≠ 0)
    (hT : p.β₂ ^ 2 = 4 * p.a * p.β₁) (y : State 2) :
    field p y = 0 ↔ y = mk (-p.β₂ / (2 * p.a)) 0 := by
  rw [field_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hsq : (2 * p.a * y 0 + p.β₂) ^ 2 = 0 := by linear_combination (4 * p.a) * h2 + hT
    have hlin : 2 * p.a * y 0 + p.β₂ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    rw [← mk_coords y, mk_eq_iff]
    refine ⟨?_, h1⟩
    field_simp
    linarith
  · rintro rfl
    refine ⟨rfl, ?_⟩
    simp only [mk_apply_zero]
    field_simp
    nlinarith [hT]

/-- The equilibrium is unique iff the parameters lie on `T`. -/
@[powerlib_foundation] theorem existsUnique_equilibrium_iff (p : Params) (ha : p.a ≠ 0) :
    (∃! y, field p y = 0) ↔ p.β₂ ^ 2 = 4 * p.a * p.β₁ := by
  constructor
  · rintro ⟨y, hy, huniq⟩
    have hd : 0 ≤ p.β₂ ^ 2 - 4 * p.a * p.β₁ := (exists_equilibrium_iff p ha).mp ⟨y, hy⟩
    by_contra hne
    have hpos : 0 < p.β₂ ^ 2 - 4 * p.a * p.β₁ := lt_of_le_of_ne hd (fun h => hne (by linarith))
    set s := √(p.β₂ ^ 2 - 4 * p.a * p.β₁)
    have hs : s ^ 2 = p.β₂ ^ 2 - 4 * p.a * p.β₁ := Real.sq_sqrt hd
    have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
    have hroot : ∀ r, p.a * r ^ 2 + p.β₂ * r + p.β₁ = 0 → mk r 0 = y := fun r hr =>
      huniq _ ((field_eq_zero_iff p _).mpr ⟨rfl, by simpa using hr⟩)
    have h1 := hroot ((-p.β₂ + s) / (2 * p.a)) (by field_simp; nlinarith [hs])
    have h2 := hroot ((-p.β₂ - s) / (2 * p.a)) (by field_simp; nlinarith [hs])
    have := (mk_eq_iff.mp (h1.trans h2.symm)).1
    field_simp at this
    linarith
  · intro hT
    refine ⟨mk (-p.β₂ / (2 * p.a)) 0, (equilibrium_on_T_iff p ha hT _).mpr rfl, fun y hy =>
      (equilibrium_on_T_iff p ha hT y).mp hy⟩

@[powerlib_foundation] theorem trace_jacobian (p : Params) (y₁ : ℝ) :
    (jacobian p y₁ 0).trace = p.b * y₁ := by
  simp [jacobian, Matrix.trace_fin_two]

@[powerlib_foundation] theorem det_jacobian (p : Params) (y₁ : ℝ) :
    (jacobian p y₁ 0).det = -(p.β₂ + 2 * p.a * y₁) := by
  simp [jacobian, Matrix.det_fin_two]

/-- The Jacobian at the equilibrium on `T` is singular (saddle-node). -/
@[powerlib_foundation] theorem det_jacobian_on_T (p : Params) (ha : p.a ≠ 0) :
    (jacobian p (-p.β₂ / (2 * p.a)) 0).det = 0 := by
  rw [det_jacobian]; field_simp; ring

/-- (`b ≠ 0`) An equilibrium with `tr = 0` and `det > 0` exists iff `β₁ = 0 ∧ β₂ < 0`. -/
@[powerlib_foundation] theorem hopf_condition_iff (p : Params) (hb : p.b ≠ 0) :
    (∃ y, field p y = 0 ∧ (jacobian p (y 0) (y 1)).trace = 0 ∧ 0 < (jacobian p (y 0) (y 1)).det) ↔
      p.β₁ = 0 ∧ p.β₂ < 0 := by
  constructor
  · rintro ⟨y, hy, htr, hdet⟩
    rw [field_eq_zero_iff] at hy
    rw [hy.1, trace_jacobian] at htr
    rw [hy.1, det_jacobian] at hdet
    have hy0 : y 0 = 0 := (mul_eq_zero.mp htr).resolve_left hb
    have := hy.2
    rw [hy0] at this hdet
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [field_eq_zero_iff]; simp [h1]
    · simp only [PiLp.zero_apply]; rw [trace_jacobian]; ring
    · simp only [PiLp.zero_apply]; rw [det_jacobian]; linarith

/-- (`b ≠ 0`) `tr = det = 0` at an equilibrium only at the BT point, and only at the origin. -/
@[powerlib_foundation] theorem bt_point_iff (p : Params) (hb : p.b ≠ 0) (y : State 2) :
    (field p y = 0 ∧ (jacobian p (y 0) (y 1)).trace = 0 ∧ (jacobian p (y 0) (y 1)).det = 0) ↔
      p.β₁ = 0 ∧ p.β₂ = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨hy, htr, hdet⟩
    rw [field_eq_zero_iff] at hy
    rw [hy.1, trace_jacobian] at htr
    rw [hy.1, det_jacobian] at hdet
    have hy0 : y 0 = 0 := (mul_eq_zero.mp htr).resolve_left hb
    have := hy.2
    rw [hy0] at this hdet
    refine ⟨by linarith, by linarith, eq_zero_iff.mpr ⟨hy0, hy.1⟩⟩
  · rintro ⟨h1, h2, rfl⟩
    refine ⟨(field_eq_zero_iff p 0).mpr (by simp [h1]), ?_, ?_⟩
    · simp only [PiLp.zero_apply]; rw [trace_jacobian]; ring
    · simp only [PiLp.zero_apply]; rw [det_jacobian, h2]; ring

/-- At the BT point the Jacobian of the truncated normal form is the Jordan block. -/
@[powerlib_foundation] theorem jacobian_bt_point (a b : ℝ) :
    jacobian ⟨0, 0, a, b⟩ 0 0 = jordanBlock := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jacobian, jordanBlock]

/-- An equilibrium `(y₁, 0)` with `β₂ + 2 a y₁ > 0` is a saddle, hence unstable. -/
@[powerlib_foundation] theorem saddle_unstable (p : Params) {y₁ : ℝ}
    (heq : p.a * y₁ ^ 2 + p.β₂ * y₁ + p.β₁ = 0) (hs : 0 < p.β₂ + 2 * p.a * y₁) :
    Unstable (field p) (mk y₁ 0) :=
  Criteria.unstable_of_jacobian_det_neg_fin_two (jacobian p y₁ 0) (field_contDiff p)
    ((field_eq_zero_iff p _).mpr ⟨rfl, by simpa using heq⟩)
    (by simpa using fderiv_field p (mk y₁ 0)) (by rw [det_jacobian]; linarith)

/-- An equilibrium `(y₁, 0)` with `β₂ + 2 a y₁ < 0` and `b y₁ < 0` is locally exponentially
stable. -/
@[powerlib_foundation] theorem node_or_focus_stable (p : Params) {y₁ : ℝ}
    (heq : p.a * y₁ ^ 2 + p.β₂ * y₁ + p.β₁ = 0) (hs : p.β₂ + 2 * p.a * y₁ < 0)
    (htr : p.b * y₁ < 0) :
    LocallyExponentiallyStable (field p) (mk y₁ 0) :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two (jacobian p y₁ 0) (field_contDiff p)
    ((field_eq_zero_iff p _).mpr ⟨rfl, by simpa using heq⟩)
    (by simpa using fderiv_field p (mk y₁ 0)) (by rw [trace_jacobian]; exact htr)
    (by rw [det_jacobian]; linarith)

end powerlib.NormalForm.BogdanovTakens
