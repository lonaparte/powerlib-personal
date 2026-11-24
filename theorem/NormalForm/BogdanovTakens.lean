import theorem.PhasePlane.Planar

/-! # Bogdanov–Takens: Jordan structure and the truncated normal form

Linear algebra of the double-zero eigenvalue, equilibrium-level facts of the truncated planar
Bogdanov–Takens normal form, and the generic normal-form coefficients of a double zero (and of a
simple zero) eigenvalue of a field.

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
* Normal-form coefficients: any field `f : E → E` on a real inner product space, a point `x`,
  `A = Df(x)` and `B = D²f(x)` (`fderiv` of `fderiv`). The coefficients are Kuznetsov's
  projection formulas, taken as definitions: the centre-manifold reduction and the normal-form
  transformation they summarise are not formalized, so no statement says that a field is locally
  equivalent to its normal form.

Source: work-sync theory/T-bogdanov-takens-bifurcation.md §1.1–1.5 (§1.6, the GFL-PLL model, is
not included); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §3.2 and §5.4
(fold: `a = ½⟨p, B(q, q)⟩`, transversality `⟨p, f_μ⟩`), §8.4 and §8.7 (Bogdanov–Takens: the
Jordan and adjoint chains, `a = ½⟨p₁, B(q₀, q₀)⟩`, `b = ⟨p₀, B(q₀, q₀)⟩ + ⟨p₁, B(q₀, q₁)⟩`).

Results.
* `trace_det_zero_iff_similar_jordanBlock`: `tr J = det J = 0 ∧ J ≠ 0` iff `J` is similar to the
  single Jordan block `!![0, 1; 0, 0]` (`jordanBlock`; `J P = P N` with `det P ≠ 0`); together
  with `Criteria.isNilpotent_iff_trace_det_eq_zero_fin_two` this is also equivalent to `J` being
  nonzero nilpotent.
* The proportional structure `proportionalMatrix k κ g = !![k g, κ; g, 0]` (the PI-PLL Jacobian
  is an instance) has `tr = k g`, `det = −κ g` (`trace_proportionalMatrix`,
  `det_proportionalMatrix`); with `κ ≠ 0` both vanish exactly at `g = 0`, where the matrix is a
  single Jordan block (`proportional_trace_det_zero_iff`, `proportional_jordan_at_zero`).
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
* Normal-form coefficients of a double zero eigenvalue. `IsBTChain A q₀ q₁ p₀ p₁`: the Jordan chain
  `A q₀ = 0`, `A q₁ = q₀`, the adjoint chain `⟨p₁, A v⟩ = 0`, `⟨p₀, A v⟩ = ⟨p₁, v⟩`, normalised
  by `⟨p₁, q₁⟩ = 1`, `⟨p₀, q₁⟩ = 0`; the other two normalisations follow
  (`IsBTChain.inner_p₀_q₀`, `IsBTChain.inner_p₁_q₀`). The coefficients of
  `ẇ₀ = w₁`, `ẇ₁ = a w₀² + b w₀ w₁`: `coeffA f x q₀ p₁ = ½⟨p₁, B(q₀, q₀)⟩`,
  `coeffB f x q₀ q₁ p₀ p₁ = ⟨p₀, B(q₀, q₀)⟩ + ⟨p₁, B(q₀, q₁)⟩` (`fderiv_fderiv_apply`: `B(u, v)`
  is the derivative of `y ↦ Df(y) v` along `u`).
* Normalisation laws. The shift `(q₀, q₁ + t q₀, p₀ − t p₁, p₁)` and the scaling
  `(s q₀, s q₁, s⁻¹ p₀, s⁻¹ p₁)` are chains (`IsBTChain.shift`, `IsBTChain.smul`); `b` is
  shift-invariant (`coeffB_shift`) and both coefficients scale by `s` (`coeffA_smul`,
  `coeffB_smul`), so the sign of `a b` does not depend on the normalisation. From the Jordan
  chain alone: `B(q₀, q₀) = A y + c q₁` gives `a = c/2` (`IsBTChain.coeffA_eq`) and, with
  `y + B(q₀, q₁) = A z + d q₁`, `b = d` (`IsBTChain.coeffB_eq`), for every adjoint chain. If every
  null vector of `A` is a multiple of `q₀`, every chain has `q₀' = s q₀`, `q₁' = s q₁ + t q₀`
  (`IsBTChain.exists_smul`) and coefficients `s a`, `s b` (`IsBTChain.coeff_eq_of_isBTChain`): the
  coefficients depend only on the normalisation of `q₀`. In finite dimension a normalised left
  null vector `p₁` completes to a chain (`IsBTChain.exists_of_left`). Matrix reading on `ℝⁿ`:
  `isBTChain_toEuclideanCLM_iff`.
* The truncated normal form reproduces its coefficients: `B(u, v) = (0, 2a u₁v₁ + b(u₁v₂ +
  u₂v₁))` (`fderiv_fderiv_field`), `(e₁, e₂, e₁, e₂)` is a chain at the origin of
  `ẏ₁ = y₂`, `ẏ₂ = a y₁² + b y₁ y₂` (`isBTChain_field`), and the formulas give `a` and `b`
  (`coeffA_coeffB_field`).
* The fold (simple zero eigenvalue). `IsNullPair A q p` (`A q = 0`, `⟨p, A v⟩ = 0`,
  `⟨p, q⟩ = 1`); the coefficient `foldCoeff f x q p = ½⟨p, B(q, q)⟩` and the transversality
  `foldTransversality F μ x p = ⟨p, ∂F/∂μ⟩` of a one-parameter family `F μ`. Scaling laws
  (`IsNullPair.smul`, `foldCoeff_smul`, `foldTransversality_smul`: `a ↦ s a`, the
  transversality `↦ s⁻¹ ·`), the values from the null vector alone (`IsNullPair.foldCoeff_eq`,
  `IsNullPair.foldTransversality_eq`), matrix reading `isNullPair_toEuclideanCLM_iff`.

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

@[tmio T, powerlib_foundation] theorem jordanBlock_sq : jordanBlock ^ 2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jordanBlock, pow_two]

@[tmio T, powerlib_foundation] theorem jordanBlock_ne_zero : jordanBlock ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [jordanBlock] at this

@[tmio T, powerlib_foundation] theorem trace_jordanBlock : jordanBlock.trace = 0 := by
  simp [jordanBlock, Matrix.trace_fin_two]

@[tmio T, powerlib_foundation] theorem det_jordanBlock : jordanBlock.det = 0 := by
  simp [jordanBlock, Matrix.det_fin_two]

/-- A real `2 × 2` matrix has `tr = det = 0` and is nonzero iff it is similar to the single
Jordan block. -/
@[tmio T, powerlib_foundation] theorem trace_det_zero_iff_similar_jordanBlock
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

/-! ## The proportional structure -/

/-- The proportional structure `!![k g, κ; g, 0]`: trace `k g` and determinant `−κ g` are both
proportional to the gain `g` (the PI-PLL Jacobian is an instance). -/
def proportionalMatrix (k κ g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![k * g, κ; g, 0]

@[tmio T, simp, powerlib_foundation] theorem trace_proportionalMatrix (k κ g : ℝ) :
    (proportionalMatrix k κ g).trace = k * g := by
  simp [proportionalMatrix, Matrix.trace_fin_two]

@[tmio T, simp, powerlib_foundation] theorem det_proportionalMatrix (k κ g : ℝ) :
    (proportionalMatrix k κ g).det = -(κ * g) := by
  simp [proportionalMatrix, Matrix.det_fin_two]

/-- For `κ ≠ 0` the trace and determinant of the proportional structure vanish together exactly
at `g = 0`. -/
@[tmio T, powerlib_foundation] theorem proportional_trace_det_zero_iff {k κ g : ℝ} (hκ : κ ≠ 0) :
    ((proportionalMatrix k κ g).trace = 0 ∧ (proportionalMatrix k κ g).det = 0) ↔ g = 0 := by
  rw [trace_proportionalMatrix, det_proportionalMatrix, neg_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h hκ
    · exact h
  · rintro rfl; simp

/-- At `g = 0` the proportional structure is a single Jordan block when `κ ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem proportional_jordan_at_zero {k κ : ℝ} (hκ : κ ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      proportionalMatrix k κ 0 * P = P * jordanBlock := by
  apply (trace_det_zero_iff_similar_jordanBlock _).mp
  refine ⟨by simp, by simp, fun h => hκ ?_⟩
  simpa [proportionalMatrix] using congrFun (congrFun h 0) 1

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

@[tmio M, powerlib_foundation] theorem field_contDiff (p : Params) {k : WithTop ℕ∞} :
    ContDiff ℝ k (field p) := by
  refine contDiff_euclidean.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simpa [field] using Dynamics.contDiff_coord (n := 2) 1
  · simp only [field, mk_apply_one]; fun_prop

@[tmio M, powerlib_foundation] theorem hasFDerivAt_field (p : Params) (y : State 2) :
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

@[tmio M, powerlib_foundation] theorem fderiv_field (p : Params) (y : State 2) :
    fderiv ℝ (field p) y = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian p (y 0) (y 1)) :=
  (hasFDerivAt_field p y).fderiv

@[tmio M, powerlib_foundation] theorem field_eq_zero_iff (p : Params) (y : State 2) :
    field p y = 0 ↔ y 1 = 0 ∧ p.a * y 0 ^ 2 + p.β₂ * y 0 + p.β₁ = 0 := by
  rw [field, mk_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1] at h2; linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1]; linarith⟩

/-- An equilibrium exists iff the discriminant `β₂² − 4 a β₁` is nonnegative. -/
@[tmio M, powerlib_foundation] theorem exists_equilibrium_iff (p : Params) (ha : p.a ≠ 0) :
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
@[tmio M, powerlib_foundation] theorem equilibrium_on_T_iff (p : Params) (ha : p.a ≠ 0)
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
@[tmio M, powerlib_foundation] theorem existsUnique_equilibrium_iff (p : Params) (ha : p.a ≠ 0) :
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

@[tmio M, powerlib_foundation] theorem trace_jacobian (p : Params) (y₁ : ℝ) :
    (jacobian p y₁ 0).trace = p.b * y₁ := by
  simp [jacobian, Matrix.trace_fin_two]

@[tmio M, powerlib_foundation] theorem det_jacobian (p : Params) (y₁ : ℝ) :
    (jacobian p y₁ 0).det = -(p.β₂ + 2 * p.a * y₁) := by
  simp [jacobian, Matrix.det_fin_two]

/-- The Jacobian at the equilibrium on `T` is singular (saddle-node). -/
@[tmio M, powerlib_foundation] theorem det_jacobian_on_T (p : Params) (ha : p.a ≠ 0) :
    (jacobian p (-p.β₂ / (2 * p.a)) 0).det = 0 := by
  rw [det_jacobian]; field_simp; ring

/-- (`b ≠ 0`) An equilibrium with `tr = 0` and `det > 0` exists iff `β₁ = 0 ∧ β₂ < 0`. -/
@[tmio M, powerlib_foundation] theorem hopf_condition_iff (p : Params) (hb : p.b ≠ 0) :
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
@[tmio M, powerlib_foundation] theorem bt_point_iff (p : Params) (hb : p.b ≠ 0) (y : State 2) :
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
@[tmio M, powerlib_foundation] theorem jacobian_bt_point (a b : ℝ) :
    jacobian ⟨0, 0, a, b⟩ 0 0 = jordanBlock := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jacobian, jordanBlock]

/-- An equilibrium `(y₁, 0)` with `β₂ + 2 a y₁ > 0` is a saddle, hence unstable. -/
@[tmio TM, powerlib_foundation] theorem saddle_unstable (p : Params) {y₁ : ℝ}
    (heq : p.a * y₁ ^ 2 + p.β₂ * y₁ + p.β₁ = 0) (hs : 0 < p.β₂ + 2 * p.a * y₁) :
    Unstable (field p) (mk y₁ 0) :=
  Criteria.unstable_of_jacobian_det (jacobian p y₁ 0) (field_contDiff p)
    ((field_eq_zero_iff p _).mpr ⟨rfl, by simpa using heq⟩)
    (by simpa using fderiv_field p (mk y₁ 0))
    (by rw [neg_one_sq, one_mul, det_jacobian]; linarith)

/-- An equilibrium `(y₁, 0)` with `β₂ + 2 a y₁ < 0` and `b y₁ < 0` is locally exponentially
stable. -/
@[tmio TM, powerlib_foundation] theorem node_or_focus_stable (p : Params) {y₁ : ℝ}
    (heq : p.a * y₁ ^ 2 + p.β₂ * y₁ + p.β₁ = 0) (hs : p.β₂ + 2 * p.a * y₁ < 0)
    (htr : p.b * y₁ < 0) :
    LocallyExponentiallyStable (field p) (mk y₁ 0) :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two (jacobian p y₁ 0) (field_contDiff p)
    ((field_eq_zero_iff p _).mpr ⟨rfl, by simpa using heq⟩)
    (by simpa using fderiv_field p (mk y₁ 0)) (by rw [trace_jacobian]; exact htr)
    (by rw [det_jacobian]; linarith)

/-! ## Normal-form coefficients of a double zero eigenvalue -/

section Coefficients

open scoped RealInnerProductSpace

/-- The second derivative applied to `(u, v)` is the derivative of `y ↦ Df(y) v` in the
direction `u`. -/
@[tmio T, powerlib_foundation] theorem fderiv_fderiv_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (u v : E) :
    fderiv ℝ (fderiv ℝ f) x u v = fderiv ℝ (fun y => fderiv ℝ f y v) x u := by
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A normalised Bogdanov–Takens basis of a linear map `A`: the Jordan chain `A q₀ = 0`,
`A q₁ = q₀`, the adjoint chain `Aᵀ p₁ = 0`, `Aᵀ p₀ = p₁` (stated as `⟨p₁, A v⟩ = 0`,
`⟨p₀, A v⟩ = ⟨p₁, v⟩` for every `v`), normalised by `⟨p₁, q₁⟩ = 1` and `⟨p₀, q₁⟩ = 0`. The two
other normalisations of the source, `⟨p₀, q₀⟩ = 1` and `⟨p₁, q₀⟩ = 0`, follow
(`IsBTChain.inner_p₀_q₀`, `IsBTChain.inner_p₁_q₀`). -/
structure IsBTChain (A : E →L[ℝ] E) (q₀ q₁ p₀ p₁ : E) : Prop where
  map_q₀ : A q₀ = 0
  map_q₁ : A q₁ = q₀
  inner_p₁_map : ∀ v, ⟪p₁, A v⟫ = 0
  inner_p₀_map : ∀ v, ⟪p₀, A v⟫ = ⟪p₁, v⟫
  inner_p₁_q₁ : ⟪p₁, q₁⟫ = 1
  inner_p₀_q₁ : ⟪p₀, q₁⟫ = 0

/-- Kuznetsov's quadratic Bogdanov–Takens coefficient `a = ½ ⟨p₁, B(q₀, q₀)⟩` of the field `f`
at `x`, `B = D²f(x)`. -/
def coeffA (f : E → E) (x q₀ p₁ : E) : ℝ := ⟪p₁, fderiv ℝ (fderiv ℝ f) x q₀ q₀⟫ / 2

/-- Kuznetsov's Bogdanov–Takens coefficient `b = ⟨p₀, B(q₀, q₀)⟩ + ⟨p₁, B(q₀, q₁)⟩` of the
field `f` at `x`, `B = D²f(x)`. -/
def coeffB (f : E → E) (x q₀ q₁ p₀ p₁ : E) : ℝ :=
  ⟪p₀, fderiv ℝ (fderiv ℝ f) x q₀ q₀⟫ + ⟪p₁, fderiv ℝ (fderiv ℝ f) x q₀ q₁⟫

variable {A : E →L[ℝ] E} {q₀ q₁ p₀ p₁ : E}

/-- `⟨p₁, q₀⟩ = 0` follows from the chains. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.inner_p₁_q₀ (h : IsBTChain A q₀ q₁ p₀ p₁) :
    ⟪p₁, q₀⟫ = 0 := by
  rw [← h.map_q₁]; exact h.inner_p₁_map q₁

/-- `⟨p₀, q₀⟩ = 1` follows from the chains and `⟨p₁, q₁⟩ = 1`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.inner_p₀_q₀ (h : IsBTChain A q₀ q₁ p₀ p₁) :
    ⟪p₀, q₀⟫ = 1 := by
  rw [← h.map_q₁, h.inner_p₀_map, h.inner_p₁_q₁]

/-- The shifted basis `(q₀, q₁ + t q₀, p₀ − t p₁, p₁)` is again a normalised chain. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.shift (h : IsBTChain A q₀ q₁ p₀ p₁) (t : ℝ) :
    IsBTChain A q₀ (q₁ + t • q₀) (p₀ - t • p₁) p₁ where
  map_q₀ := h.map_q₀
  map_q₁ := by rw [map_add, map_smul, h.map_q₁, h.map_q₀, smul_zero, add_zero]
  inner_p₁_map := h.inner_p₁_map
  inner_p₀_map v := by
    rw [inner_sub_left, inner_smul_left, h.inner_p₀_map, h.inner_p₁_map]; simp
  inner_p₁_q₁ := by rw [inner_add_right, inner_smul_right, h.inner_p₁_q₁, h.inner_p₁_q₀]; ring
  inner_p₀_q₁ := by
    simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      h.inner_p₀_q₁, h.inner_p₀_q₀, h.inner_p₁_q₁, h.inner_p₁_q₀]
    ring

/-- The rescaled basis `(s q₀, s q₁, s⁻¹ p₀, s⁻¹ p₁)` (`s ≠ 0`) is again a normalised chain. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.smul (h : IsBTChain A q₀ q₁ p₀ p₁) {s : ℝ}
    (hs : s ≠ 0) : IsBTChain A (s • q₀) (s • q₁) (s⁻¹ • p₀) (s⁻¹ • p₁) where
  map_q₀ := by rw [map_smul, h.map_q₀, smul_zero]
  map_q₁ := by rw [map_smul, h.map_q₁]
  inner_p₁_map v := by rw [inner_smul_left, h.inner_p₁_map]; simp
  inner_p₀_map v := by rw [inner_smul_left, inner_smul_left, h.inner_p₀_map]
  inner_p₁_q₁ := by
    rw [real_inner_smul_left, real_inner_smul_right, h.inner_p₁_q₁]; field_simp
  inner_p₀_q₁ := by rw [inner_smul_left, inner_smul_right, h.inner_p₀_q₁]; simp

/-- **`b` does not see the shift** `q₁ ↦ q₁ + t q₀`, `p₀ ↦ p₀ − t p₁` (`a` does not involve
`q₁, p₀`): bilinearity of `B` alone. -/
@[tmio T, powerlib_foundation] theorem coeffB_shift (f : E → E) (x q₀ q₁ p₀ p₁ : E) (t : ℝ) :
    coeffB f x q₀ (q₁ + t • q₀) (p₀ - t • p₁) p₁ = coeffB f x q₀ q₁ p₀ p₁ := by
  simp only [coeffB, map_add, map_smul, inner_sub_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-- **Scaling law of `a`**: `(s q₀, s⁻¹ p₁)` multiplies `a` by `s`. -/
@[tmio T, powerlib_foundation] theorem coeffA_smul (f : E → E) (x q₀ p₁ : E) {s : ℝ}
    (hs : s ≠ 0) : coeffA f x (s • q₀) (s⁻¹ • p₁) = s * coeffA f x q₀ p₁ := by
  simp only [coeffA, map_smul, _root_.smul_apply, real_inner_smul_left, real_inner_smul_right]
  field_simp

/-- **Scaling law of `b`**: `(s q₀, s q₁, s⁻¹ p₀, s⁻¹ p₁)` multiplies `b` by `s`. -/
@[tmio T, powerlib_foundation] theorem coeffB_smul (f : E → E) (x q₀ q₁ p₀ p₁ : E) {s : ℝ}
    (hs : s ≠ 0) :
    coeffB f x (s • q₀) (s • q₁) (s⁻¹ • p₀) (s⁻¹ • p₁) = s * coeffB f x q₀ q₁ p₀ p₁ := by
  simp only [coeffB, map_smul, _root_.smul_apply, real_inner_smul_left, real_inner_smul_right]
  field_simp

/-- **The coefficient `a` from the Jordan chain alone.** If `B(q₀, q₀) = A y + c q₁`, then
`a = c/2` for every normalised adjoint chain. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.coeffA_eq {f : E → E} {x : E}
    (h : IsBTChain (fderiv ℝ f x) q₀ q₁ p₀ p₁) {y : E} {c : ℝ}
    (hy : fderiv ℝ (fderiv ℝ f) x q₀ q₀ = fderiv ℝ f x y + c • q₁) :
    coeffA f x q₀ p₁ = c / 2 := by
  rw [coeffA, hy, inner_add_right, inner_smul_right, h.inner_p₁_map, h.inner_p₁_q₁]
  ring

/-- **The coefficient `b` from the Jordan chain alone.** If `B(q₀, q₀) = A y + c q₁` and
`y + B(q₀, q₁) = A z + d q₁`, then `b = d` for every normalised adjoint chain. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.coeffB_eq {f : E → E} {x : E}
    (h : IsBTChain (fderiv ℝ f x) q₀ q₁ p₀ p₁) {y z : E} {c d : ℝ}
    (hy : fderiv ℝ (fderiv ℝ f) x q₀ q₀ = fderiv ℝ f x y + c • q₁)
    (hz : y + fderiv ℝ (fderiv ℝ f) x q₀ q₁ = fderiv ℝ f x z + d • q₁) :
    coeffB f x q₀ q₁ p₀ p₁ = d := by
  have e : ⟪p₁, y + fderiv ℝ (fderiv ℝ f) x q₀ q₁⟫ = d := by
    rw [hz, inner_add_right, inner_smul_right, h.inner_p₁_map, h.inner_p₁_q₁]; ring
  rw [coeffB, hy, inner_add_right, inner_smul_right, h.inner_p₀_map, h.inner_p₀_q₁, ← e,
    inner_add_right]
  ring

/-- **The right chain is unique up to `(s, t)`.** If every null vector of `A` is a multiple of
`q₀`, a second normalised chain has `q₀' = s q₀` and `q₁' = s q₁ + t q₀` with `s ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.exists_smul {q₀' q₁' p₀' p₁' : E}
    (h : IsBTChain A q₀ q₁ p₀ p₁) (h' : IsBTChain A q₀' q₁' p₀' p₁')
    (hker : ∀ v, A v = 0 → ∃ s : ℝ, v = s • q₀) :
    ∃ s t : ℝ, s ≠ 0 ∧ q₀' = s • q₀ ∧ q₁' = s • q₁ + t • q₀ := by
  obtain ⟨s, hs⟩ := hker _ h'.map_q₀
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := h'.inner_p₀_q₀
    rw [hs, zero_smul, inner_zero_right] at this
    exact zero_ne_one this
  obtain ⟨t, ht⟩ := hker (q₁' - s • q₁) (by
    rw [map_sub, map_smul, h.map_q₁, h'.map_q₁, hs, sub_self])
  exact ⟨s, t, hs0, hs, by rw [← ht]; abel⟩

/-- **The coefficients depend only on the normalisation of `q₀`.** If every null vector of
`D f(x)` is a multiple of `q₀` and the Jordan chain decomposes `B(q₀, q₀) = A y + c q₁`,
`y + B(q₀, q₁) = A z + d q₁`, then every normalised chain has `q₀' = s q₀` (`s ≠ 0`),
`a' = s c/2` and `b' = s d`; for `q₀' = q₀` the coefficients are those of the first chain. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.coeff_eq_of_isBTChain {f : E → E} {x : E}
    {q₀' q₁' p₀' p₁' : E} (h : IsBTChain (fderiv ℝ f x) q₀ q₁ p₀ p₁)
    (h' : IsBTChain (fderiv ℝ f x) q₀' q₁' p₀' p₁')
    (hker : ∀ v, fderiv ℝ f x v = 0 → ∃ s : ℝ, v = s • q₀) {y z : E} {c d : ℝ}
    (hy : fderiv ℝ (fderiv ℝ f) x q₀ q₀ = fderiv ℝ f x y + c • q₁)
    (hz : y + fderiv ℝ (fderiv ℝ f) x q₀ q₁ = fderiv ℝ f x z + d • q₁) :
    ∃ s : ℝ, s ≠ 0 ∧ q₀' = s • q₀ ∧ coeffA f x q₀' p₁' = s * (c / 2) ∧
      coeffB f x q₀' q₁' p₀' p₁' = s * d := by
  obtain ⟨s, t, hs, h0, h1⟩ := h.exists_smul h' hker
  have hB01 : fderiv ℝ (fderiv ℝ f) x q₀ q₁ = fderiv ℝ f x z + d • q₁ - y := by
    rw [← hz]; abel
  have hy' : fderiv ℝ (fderiv ℝ f) x q₀' q₀' =
      fderiv ℝ f x (s ^ 2 • y - (s * t * c) • q₁) + (s * c) • q₁' := by
    rw [h0, h1]
    simp only [map_smul, map_sub, _root_.smul_apply, hy, h.map_q₁]
    module
  have hz' : (s ^ 2 • y - (s * t * c) • q₁) + fderiv ℝ (fderiv ℝ f) x q₀' q₁' =
      fderiv ℝ f x (s ^ 2 • z + (s * t) • y - (s * d * t) • q₁) + (s * d) • q₁' := by
    rw [h0, h1]
    simp only [map_smul, map_add, map_sub, _root_.smul_apply, hy, hB01, h.map_q₁]
    module
  exact ⟨s, hs, h0, by rw [h'.coeffA_eq hy']; ring, h'.coeffB_eq hy' hz'⟩


/-- **Existence of the adjoint chain** (finite dimension). If every null vector of `A` is a
multiple of `q₀` and `p₁` is a left null vector with `⟨p₁, q₁⟩ = 1`, then some `p₀` completes a
normalised chain: `p₁ ⊥ ker A = range Aᵀ`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.exists_of_left [FiniteDimensional ℝ E]
    (h₀ : A q₀ = 0) (h₁ : A q₁ = q₀) (hker : ∀ v, A v = 0 → ∃ s : ℝ, v = s • q₀)
    (hp : ∀ v, ⟪p₁, A v⟫ = 0) (hn : ⟪p₁, q₁⟫ = 1) : ∃ p₀, IsBTChain A q₀ q₁ p₀ p₁ := by
  have hperp : p₁ ∈ A.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨s, rfl⟩ := hker u hu
    rw [real_inner_smul_left, real_inner_comm, ← h₁, hp, mul_zero]
  rw [ContinuousLinearMap.orthogonal_ker,
    IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)] at hperp
  obtain ⟨p, hp'⟩ := hperp
  have hadj : ∀ v, ⟪p, A v⟫ = ⟪p₁, v⟫ := fun v => by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun w => ⟪w, v⟫) hp'
  refine ⟨p - ⟪p, q₁⟫ • p₁, h₀, h₁, hp, fun v => ?_, hn, ?_⟩
  · rw [inner_sub_left, real_inner_smul_left, hadj, hp, mul_zero, sub_zero]
  · rw [inner_sub_left, real_inner_smul_left, hn, mul_one, sub_self]

/-- **Matrix reading of a chain** on `ℝⁿ`: for `A = J` the conditions are `J q₀ = 0`,
`J q₁ = q₀`, `p₁ᵀ J = 0`, `p₀ᵀ J = p₁ᵀ`, `p₁ · q₁ = 1`, `p₀ · q₁ = 0`. -/
@[tmio T, powerlib_foundation] theorem isBTChain_toEuclideanCLM_iff {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℝ) (q₀ q₁ p₀ p₁ : Fin n → ℝ) :
    IsBTChain (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J) (WithLp.toLp 2 q₀)
        (WithLp.toLp 2 q₁) (WithLp.toLp 2 p₀) (WithLp.toLp 2 p₁) ↔
      J *ᵥ q₀ = 0 ∧ J *ᵥ q₁ = q₀ ∧ p₁ ᵥ* J = 0 ∧ p₀ ᵥ* J = p₁ ∧ p₁ ⬝ᵥ q₁ = 1 ∧
        p₀ ⬝ᵥ q₁ = 0 := by
  have hin : ∀ a b : Fin n → ℝ, ⟪(WithLp.toLp 2 a : State n), WithLp.toLp 2 b⟫ = a ⬝ᵥ b :=
    fun a b => by rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have hJ : ∀ (a : Fin n → ℝ) (v : State n),
      ⟪(WithLp.toLp 2 a : State n), Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J v⟫ =
        (a ᵥ* J) ⬝ᵥ v.ofLp := fun a v => by
    rw [Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec]
  have hl : ∀ a : Fin n → ℝ, (∀ v : State n, (a ᵥ* J) ⬝ᵥ v.ofLp = 0) ↔ a ᵥ* J = 0 := fun a =>
    ⟨fun h => dotProduct_eq_zero_iff.mp fun w => h (WithLp.toLp 2 w),
      fun h v => by rw [h, zero_dotProduct]⟩
  have hl' : ∀ a b : Fin n → ℝ,
      (∀ v : State n, (a ᵥ* J) ⬝ᵥ v.ofLp = b ⬝ᵥ v.ofLp) ↔ a ᵥ* J = b := fun a b => by
    constructor
    · intro h
      exact sub_eq_zero.mp (dotProduct_eq_zero_iff.mp fun w => by
        rw [sub_dotProduct, h (WithLp.toLp 2 w), sub_self])
    · intro h v; rw [h]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, (hl p₁).mp fun v => ?_, (hl' p₀ p₁).mp fun v => ?_, ?_, ?_⟩
    · simpa using h0
    · simpa using h1
    · rw [← hJ]; exact h2 v
    · rw [← hJ, h3 v]; exact (hin p₁ v.ofLp).symm ▸ rfl
    · rw [← hin]; exact h4
    · rw [← hin]; exact h5
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    refine ⟨by simp [h0], by simp [h1], fun v => ?_, fun v => ?_, by rw [hin, h4],
      by rw [hin, h5]⟩
    · rw [hJ]; exact (hl p₁).mpr h2 v
    · rw [hJ, (hl' p₀ p₁).mpr h3 v]; exact (hin p₁ v.ofLp).symm ▸ rfl

/-! ### The fold coefficient of a simple zero eigenvalue -/

/-- A normalised null pair of `A`: `A q = 0`, `Aᵀ p = 0` (`⟨p, A v⟩ = 0` for every `v`) and
`⟨p, q⟩ = 1`. -/
structure IsNullPair (A : E →L[ℝ] E) (q p : E) : Prop where
  map_q : A q = 0
  inner_p_map : ∀ v, ⟪p, A v⟫ = 0
  inner_p_q : ⟪p, q⟫ = 1

/-- Kuznetsov's fold (saddle-node) coefficient `a = ½ ⟨p, B(q, q)⟩` of the field `f` at `x`,
`B = D²f(x)`. -/
def foldCoeff (f : E → E) (x q p : E) : ℝ := ⟪p, fderiv ℝ (fderiv ℝ f) x q q⟫ / 2

/-- The transversality coefficient `⟨p, ∂F/∂μ⟩` of a one-parameter family of fields `F μ` at
`(μ, x)`. -/
def foldTransversality (F : ℝ → E → E) (μ : ℝ) (x p : E) : ℝ := ⟪p, deriv (fun ν => F ν x) μ⟫

/-- The rescaled pair `(s q, s⁻¹ p)` (`s ≠ 0`) is again a normalised null pair. -/
@[tmio T, powerlib_foundation] theorem IsNullPair.smul {q p : E} (h : IsNullPair A q p) {s : ℝ}
    (hs : s ≠ 0) : IsNullPair A (s • q) (s⁻¹ • p) where
  map_q := by rw [map_smul, h.map_q, smul_zero]
  inner_p_map v := by rw [real_inner_smul_left, h.inner_p_map, mul_zero]
  inner_p_q := by rw [real_inner_smul_left, real_inner_smul_right, h.inner_p_q]; field_simp

/-- **Scaling laws.** `(s q, s⁻¹ p)` multiplies the fold coefficient by `s` and the
transversality coefficient by `s⁻¹`; their product is invariant. -/
@[tmio T, powerlib_foundation] theorem foldCoeff_smul (f : E → E) (x q p : E) {s : ℝ}
    (hs : s ≠ 0) : foldCoeff f x (s • q) (s⁻¹ • p) = s * foldCoeff f x q p := by
  simp only [foldCoeff, map_smul, _root_.smul_apply, real_inner_smul_left, real_inner_smul_right]
  field_simp

@[tmio T, powerlib_foundation] theorem foldTransversality_smul (F : ℝ → E → E) (μ : ℝ)
    (x p : E) (s : ℝ) :
    foldTransversality F μ x (s⁻¹ • p) = s⁻¹ * foldTransversality F μ x p := by
  simp only [foldTransversality, real_inner_smul_left]

/-- **The fold coefficient from the null vector alone.** If `B(q, q) = A y + c q`, then
`a = c/2` for every normalised left null vector `p`. -/
@[tmio T, powerlib_foundation] theorem IsNullPair.foldCoeff_eq {f : E → E} {x q p : E}
    (h : IsNullPair (fderiv ℝ f x) q p) {y : E} {c : ℝ}
    (hy : fderiv ℝ (fderiv ℝ f) x q q = fderiv ℝ f x y + c • q) : foldCoeff f x q p = c / 2 := by
  rw [foldCoeff, hy, inner_add_right, real_inner_smul_right, h.inner_p_map, h.inner_p_q]
  ring

/-- **The transversality coefficient from the null vector alone.** If `∂F/∂μ = A y + τ q`
(`A = D_x F(μ, x)`), then `⟨p, ∂F/∂μ⟩ = τ` for every normalised left null vector `p`. -/
@[tmio T, powerlib_foundation] theorem IsNullPair.foldTransversality_eq {F : ℝ → E → E}
    {μ : ℝ} {x q p : E} (h : IsNullPair (fderiv ℝ (F μ) x) q p) {y : E} {τ : ℝ}
    (hy : deriv (fun ν => F ν x) μ = fderiv ℝ (F μ) x y + τ • q) :
    foldTransversality F μ x p = τ := by
  rw [foldTransversality, hy, inner_add_right, real_inner_smul_right, h.inner_p_map, h.inner_p_q]
  ring

/-- **Matrix reading of a null pair** on `ℝⁿ`: `J q = 0`, `pᵀ J = 0`, `p · q = 1`. -/
@[tmio T, powerlib_foundation] theorem isNullPair_toEuclideanCLM_iff {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℝ) (q p : Fin n → ℝ) :
    IsNullPair (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J) (WithLp.toLp 2 q)
        (WithLp.toLp 2 p) ↔ J *ᵥ q = 0 ∧ p ᵥ* J = 0 ∧ p ⬝ᵥ q = 1 := by
  have hin : ⟪(WithLp.toLp 2 p : State n), WithLp.toLp 2 q⟫ = p ⬝ᵥ q := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have hJ : ∀ v : State n,
      ⟪(WithLp.toLp 2 p : State n), Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J v⟫ =
        (p ᵥ* J) ⬝ᵥ v.ofLp := fun v => by
    rw [Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by simpa using h0, dotProduct_eq_zero_iff.mp fun w => ?_, by rw [← hin]; exact h2⟩
    rw [← hJ]; exact h1 (WithLp.toLp 2 w)
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by simp [h0], fun v => by rw [hJ, h1, zero_dotProduct], by rw [hin, h2]⟩

/-! ### The truncated normal form reproduces its coefficients -/

/-- The second derivative of the truncated normal form:
`B(u, v) = (0, 2a u₁v₁ + b (u₁v₂ + u₂v₁))`. -/
@[tmio M, powerlib_foundation] theorem fderiv_fderiv_field (p : Params) (x u v : State 2) :
    fderiv ℝ (fderiv ℝ (field p)) x u v =
      mk 0 (2 * p.a * u 0 * v 0 + p.b * (u 0 * v 1 + u 1 * v 0)) := by
  have hd : fderiv ℝ (field p) =
      fun y => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian p (y 0) (y 1)) :=
    funext (fderiv_field p)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (field p)) x :=
    ((field_contDiff p (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x
  rw [fderiv_fderiv_apply hdiff, hd]
  have hG : HasFDerivAt
      (fun y : State 2 => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian p (y 0) (y 1)) v)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        !![0, 0; 2 * p.a * v 0 + p.b * v 1, p.b * v 0]) x := by
    refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
      ![0, (2 * p.a * v 0 + p.b * v 1) • Dynamics.coord 0 + (p.b * v 0) • Dynamics.coord 1]
      (fun i => ?_) (fun i w => ?_)
    · fin_cases i
      · show HasFDerivAt (fun y : State 2 =>
            Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian p (y 0) (y 1)) v 0) 0 x
        have : (fun y : State 2 =>
            Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian p (y 0) (y 1)) v 0) =
            fun _ => v 1 := by
          funext y; simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_two]
        rw [this]; exact hasFDerivAt_const _ _
      · have h0 := Dynamics.hasFDerivAt_coord 0 x
        have h1 := Dynamics.hasFDerivAt_coord 1 x
        have h := ((((hasFDerivAt_const p.β₂ x).add (h0.const_mul (2 * p.a))).add
          (h1.const_mul p.b)).mul_const (v 0)).add ((h0.const_mul p.b).mul_const (v 1))
        convert h using 1
        · funext y; simp [Dynamics.toEuclideanCLM_apply, jacobian, Fin.sum_univ_two]
        · ext w; simp; ring
    · fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hG.fderiv]
  ext i; fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two]
  ring

/-- At the Bogdanov–Takens point of the truncated normal form, `(e₁, e₂, e₁, e₂)` is a normalised
chain. -/
@[tmio M, powerlib_foundation] theorem isBTChain_field (a b : ℝ) :
    IsBTChain (fderiv ℝ (field ⟨0, 0, a, b⟩) 0) (mk 1 0) (mk 0 1) (mk 1 0) (mk 0 1) := by
  rw [fderiv_field]
  simp only [PiLp.zero_apply]
  rw [jacobian_bt_point]
  refine (isBTChain_toEuclideanCLM_iff _ ![1, 0] ![0, 1] ![1, 0] ![0, 1]).mpr ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (ext i; fin_cases i <;> simp [jordanBlock, Matrix.mulVec, Matrix.vecMul, dotProduct])
    | simp [dotProduct]

/-- **The projection formulas reproduce the normal form**: for the truncated Bogdanov–Takens
normal form `ẏ₁ = y₂`, `ẏ₂ = a y₁² + b y₁ y₂` at the origin, with the chain `isBTChain_field`,
Kuznetsov's coefficients are `a` and `b`. -/
@[tmio M, powerlib_foundation] theorem coeffA_coeffB_field (a b : ℝ) :
    coeffA (field ⟨0, 0, a, b⟩) 0 (mk 1 0) (mk 0 1) = a ∧
      coeffB (field ⟨0, 0, a, b⟩) 0 (mk 1 0) (mk 0 1) (mk 1 0) (mk 0 1) = b := by
  simp only [coeffA, coeffB, fderiv_fderiv_field, mk, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_two]

end Coefficients

end powerlib.NormalForm.BogdanovTakens
