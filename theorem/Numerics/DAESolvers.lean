import theorem.Numerics.BDF
import theorem.Criteria.Hurwitz2
import theorem.LTI.Decay
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Algebra of DAE solvers: BDF/Newton Jacobian, Schur-complement determinant, stabilization

The Newton Jacobian of one BDF step on a DAE and its Schur-complement determinant, Baumgarte and
GGL stabilization, and exactness of BDF on an index-2 example.

Model boundary.
* Fully implicit DAE `F(z, ż) = 0` on a real normed space, one BDF step with
  `ż_{n+k} = c z_{n+k} + d`, `c = α_k/(hβ_k)`, `d = r_n/(hβ_k)` (history term). Semi-explicit
  DAE `ẋ = f(x, y)`, `0 = g(x, y)`. Only the algebra of one Newton step is formalized; no
  step-size control, no error estimate, no convergence of the time stepping.
* Baumgarte: the constraint residual `e(t) = g(q(t))` of one scalar constraint obeys
  `ë + 2αė + β²e = 0` (continuous time, exact solution); conclusion at trajectory level
  (exponential decay of `(e, ė)`), via the 2×2 state matrix `baumgarteModel`, whose affine
  linear field is globally exponentially stable (Flow semantics); the coordinate decay of
  `(e, ė)` uses `LTI.linear_decay_of_isHurwitz`. The multibody model behind it
  (`M q̈ + Gᵀλ = F`, `G q̈ = −Ġq̇ − 2αGq̇ − β²g`) is used only to show that `λ` is an algebraic
  function of `(q, q̇)` (`baumgarte_index_one`).
* GGL: exact solutions of `q̇ = v − G(q)ᵀμ`, `g(q) = 0`, `G(q)v = 0` on real inner-product
  spaces (complete, for the adjoint `Gᵀ`).
* All results are general mathematics.

Source: work-sync theory/T-dae-solvers.md §1.2 (BDF residual, Newton Jacobian, Schur
determinant), §1.3 (order vs. index), §1.6 (Baumgarte), §1.7 (GGL), §2.4 (comparison table).

Results.
* `bdfResidual_hasFDerivAt` — `∂Φ/∂z = ∂F/∂z + c ∂F/∂ż` for `Φ(z) = F(z, cz + d)`.
* `semiExplicitBDFResidual_hasFDerivAt` — for the semi-explicit DAE the Newton Jacobian is
  `(u, w) ↦ (c u − f'(u, w), g'(u, w))`, i.e. `[[cI − f_x, −f_y], [g_x, g_y]]`.
* `daeJacobian_det` — wrapper of Mathlib `Matrix.det_fromBlocks₂₂`:
  `det 𝒥 = det A_yy · det(cI − (A_xx − A_xy A_yy⁻¹ A_yx))`; `daeJacobian_isUnit_iff`.
* `baumgarteModel_isHurwitz`, `baumgarteModel_exponentiallyStable`,
  `baumgarte_constraint_exponentialDecay`, `baumgarte_constraint_tendsto_zero` — for `α > 0`,
  `β ≠ 0` the constraint residual decays exponentially.
* `baumgarte_index_one` — for `M ≻ 0` and `G` of full row rank, the stabilized acceleration
  constraint determines the multiplier `λ` uniquely and algebraically from `(q, q̇)`.
* `ggl_projection_vanishes`, `ggl_multiplier_eq_zero` — along exact GGL solutions
  `G(q)ᵀμ = 0` (so `q̇ = v`, the original kinematics), and `μ = 0` when `G(q)ᵀ` is injective.
* `bdf_index2_exact` — on the index-2 DAE `ẋ = y`, `0 = x − p(t)`, BDF`k` of order `k`
  reproduces the algebraic variable exactly, `y_k = p'(t_k)`, for every polynomial `p` of
  degree `≤ k` (no order reduction); it applies to BDF1–BDF6 through the exact-order facts of
  `theorem/Numerics/BDF.lean` (`bdf2_exactOrder.1`, …), e.g. `bdf2_index2_exact`.

Corrections.
* §1.3: "BDF`k` has order `p = k` **if and only if** index `≤ 1`" is wrong in the "only if"
  direction: `bdf_index2_exact` shows BDF`k` without order reduction on an index-2 DAE (the
  note's own next sentence also keeps `O(hᵏ)` on index-2 differential variables).
* §2.4 table: "Baumgarte: still index 3" is wrong. After Baumgarte stabilization the
  multiplier solves the linear equation `(G M⁻¹ Gᵀ) λ = …` with an invertible matrix
  (`baumgarte_index_one`), so the stabilized DAE has index 1.
-/

noncomputable section
namespace powerlib.Numerics
open Filter Matrix
open scoped Topology

/-! ### Newton Jacobian of a BDF step -/

section Jacobian

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- BDF-substituted residual `Φ(z) = F(z, c z + d)`. -/
def bdfResidual (F : Z × Z → W) (c : ℝ) (d z : Z) : W := F (z, c • z + d)

/-- `∂Φ/∂z = ∂F/∂z + c · ∂F/∂ż` (`c = α_k/(hβ_k)`). -/
@[powerlib_foundation] theorem bdfResidual_hasFDerivAt {F : Z × Z → W} {F' : Z × Z →L[ℝ] W}
    {c : ℝ} {d z : Z} (hF : HasFDerivAt F F' (z, c • z + d)) :
    HasFDerivAt (bdfResidual F c d)
      (F'.comp (ContinuousLinearMap.inl ℝ Z Z) +
        c • F'.comp (ContinuousLinearMap.inr ℝ Z Z)) z := by
  have hpath : HasFDerivAt (fun z : Z => (z, c • z + d))
      ((ContinuousLinearMap.id ℝ Z).prod (c • ContinuousLinearMap.id ℝ Z)) z :=
    (hasFDerivAt_id z).prodMk (((hasFDerivAt_id z).const_smul c).add_const d)
  have h := hF.comp z hpath
  have heq : F'.comp (ContinuousLinearMap.inl ℝ Z Z) + c • F'.comp (ContinuousLinearMap.inr ℝ Z Z) =
      F'.comp ((ContinuousLinearMap.id ℝ Z).prod (c • ContinuousLinearMap.id ℝ Z)) := by
    ext v
    have hv : ((ContinuousLinearMap.id ℝ Z).prod (c • ContinuousLinearMap.id ℝ Z)) v =
        (ContinuousLinearMap.inl ℝ Z Z) v + c • (ContinuousLinearMap.inr ℝ Z Z) v := by
      ext <;> simp
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply, hv, map_add,
      map_smul]
  rw [heq]
  exact h

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- Semi-explicit DAE `ẋ = f(x, y)`, `0 = g(x, y)` after BDF substitution `ẋ = c x + d`:
`Φ(x, y) = (c x + d − f(x, y), g(x, y))`. -/
def semiExplicitBDFResidual (f : X × Y → X) (g : X × Y → W) (c : ℝ) (d : X) (p : X × Y) :
    X × W :=
  (c • p.1 + d - f p, g p)

/-- Newton Jacobian of the semi-explicit BDF step:
`𝒥 (u, w) = (c u − f'(u, w), g'(u, w))`, i.e. `[[cI − f_x, −f_y], [g_x, g_y]]`. -/
@[powerlib_foundation] theorem semiExplicitBDFResidual_hasFDerivAt {f : X × Y → X}
    {g : X × Y → W} {f' : X × Y →L[ℝ] X} {g' : X × Y →L[ℝ] W} {c : ℝ} {d : X} {p : X × Y}
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) :
    HasFDerivAt (semiExplicitBDFResidual f g c d)
      ((c • ContinuousLinearMap.fst ℝ X Y - f').prod g') p :=
  (((hasFDerivAt_fst.const_smul c).add_const d).sub hf).prodMk hg

end Jacobian

/-! ### Schur-complement determinant -/

section Schur

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- `det 𝒥 = det A_yy · det(cI − A_red)`, `A_red = A_xx − A_xy A_yy⁻¹ A_yx`
(wrapper of Mathlib `Matrix.det_fromBlocks₂₂`). -/
@[powerlib_foundation] theorem daeJacobian_det (c : ℝ) (Axx : Matrix n n ℝ) (Axy : Matrix n m ℝ)
    (Ayx : Matrix m n ℝ) (Ayy : Matrix m m ℝ) [Invertible Ayy] :
    (fromBlocks (c • (1 : Matrix n n ℝ) - Axx) (-Axy) Ayx Ayy).det =
      Ayy.det * (c • (1 : Matrix n n ℝ) - (Axx - Axy * Ayy⁻¹ * Ayx)).det := by
  rw [det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 2
  simp only [Matrix.neg_mul]
  abel

/-- With `A_yy` invertible, the Newton matrix is invertible iff `cI − A_red` is. -/
@[powerlib_foundation] theorem daeJacobian_isUnit_iff (c : ℝ) (Axx : Matrix n n ℝ)
    (Axy : Matrix n m ℝ) (Ayx : Matrix m n ℝ) (Ayy : Matrix m m ℝ) [Invertible Ayy] :
    IsUnit (fromBlocks (c • (1 : Matrix n n ℝ) - Axx) (-Axy) Ayx Ayy).det ↔
      IsUnit (c • (1 : Matrix n n ℝ) - (Axx - Axy * Ayy⁻¹ * Ayx)).det := by
  rw [daeJacobian_det, IsUnit.mul_iff]
  exact ⟨fun h => h.2, fun h => ⟨isUnit_det_of_invertible Ayy, h⟩⟩

end Schur

/-! ### Baumgarte stabilization -/

section Baumgarte

/-- Constraint-residual dynamics `ë + 2αė + β²e = 0`, state `(e, ė)`. -/
def baumgarteModel (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -(β ^ 2), -(2 * α)]

@[powerlib_foundation] theorem baumgarteModel_isHurwitz {α β : ℝ} (hα : 0 < α)
    (hβ : β ≠ 0) : LinearSystems.IsHurwitz (baumgarteModel α β) := by
  rw [Criteria.isHurwitz_fin_two_iff]
  simp only [baumgarteModel, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  constructor
  · linarith
  · have := pow_pos (abs_pos.mpr hβ) 2
    rw [sq_abs] at this
    linarith

@[powerlib_foundation] theorem baumgarteModel_exponentiallyStable {α β : ℝ} (hα : 0 < α)
    (hβ : β ≠ 0) :
    Flow.GloballyExponentiallyStable
      (LinearSystems.affineLinearVectorField (baumgarteModel α β) 0) 0 :=
  Linear.globallyExponentiallyStable_of_isHurwitz 0 (baumgarteModel_isHurwitz hα hβ)

/-- A solution of `ë + 2αė + β²e = 0` gives a trajectory `(e, ė)` of `baumgarteModel`. -/
@[powerlib_foundation] theorem baumgarte_isTrajectory {α β : ℝ} {e e' : ℝ → ℝ}
    (he : ∀ t, HasDerivAt e (e' t) t)
    (he' : ∀ t, HasDerivAt e' (-(2 * α) * e' t - β ^ 2 * e t) t) :
    ∀ t, HasDerivAt (fun t => ![e t, e' t]) (baumgarteModel α β *ᵥ ![e t, e' t]) t := by
  intro t
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [baumgarteModel, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he t
  · have h := he' t
    simp [baumgarteModel, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    convert h using 1
    ring

/-- **Baumgarte stabilization: the constraint residual decays exponentially.** For `α > 0`,
`β ≠ 0` there are uniform `K, rate > 0` such that every solution of `ë + 2αė + β²e = 0`
satisfies `|e(t)| ≤ K e^{−rate t} ‖(e(0), ė(0))‖` for `t ≥ 0`. -/
@[powerlib_foundation] theorem baumgarte_constraint_exponentialDecay {α β : ℝ} (hα : 0 < α)
    (hβ : β ≠ 0) :
    ∃ K > 0, ∃ rate > 0, ∀ e e' : ℝ → ℝ, (∀ t, HasDerivAt e (e' t) t) →
      (∀ t, HasDerivAt e' (-(2 * α) * e' t - β ^ 2 * e t) t) → ∀ t, 0 ≤ t →
        |e t| ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 ![e 0, e' 0]‖ := by
  obtain ⟨K, hK, rate, hrate, hbound⟩ :=
    LTI.linear_decay_of_isHurwitz (baumgarteModel_isHurwitz hα hβ)
  refine ⟨K, hK, rate, hrate, fun e e' he he' t ht => ?_⟩
  have h := hbound _ (baumgarte_isTrajectory he he') t ht
  refine le_trans ?_ h
  have hc : |e t| = ‖(WithLp.toLp 2 ![e t, e' t]) 0‖ := by
    simp [Real.norm_eq_abs]
  rw [hc]
  exact PiLp.norm_apply_le _ 0

/-- The constraint residual converges to zero. -/
@[powerlib_foundation] theorem baumgarte_constraint_tendsto_zero {α β : ℝ} (hα : 0 < α)
    (hβ : β ≠ 0) {e e' : ℝ → ℝ} (he : ∀ t, HasDerivAt e (e' t) t)
    (he' : ∀ t, HasDerivAt e' (-(2 * α) * e' t - β ^ 2 * e t) t) :
    Tendsto e atTop (𝓝 0) := by
  obtain ⟨K, hK, rate, hrate, hbound⟩ := baumgarte_constraint_exponentialDecay hα hβ
  set c := ‖WithLp.toLp 2 ![e 0, e' 0]‖
  have hexp : Tendsto (fun t : ℝ => K * Real.exp (-(rate * t)) * c) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hrate)
    simpa using (h1.const_mul K).mul_const c
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hexp
  filter_upwards [eventually_ge_atTop 0] with t ht
  simpa [Real.norm_eq_abs] using hbound e e' he he' t ht

variable {k l : ℕ}

/-- **Baumgarte-stabilized multibody DAE has index 1.** With `M ≻ 0` and `G` of full row rank
(`λ ↦ Gᵀλ` injective), the stabilized constraint
`G M⁻¹ (F − Gᵀλ) + c = 0` (`c = Ġq̇ + 2αGq̇ + β²g(q)`, obtained by substituting
`q̈ = M⁻¹(F − Gᵀλ)` into `G q̈ + Ġq̇ + 2αGq̇ + β²g = 0`) has exactly one solution `λ`:
the multiplier is an algebraic function of `(q, q̇)`. -/
@[powerlib_foundation] theorem baumgarte_index_one (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.PosDef)
    (G : Matrix (Fin l) (Fin k) ℝ) (hG : Function.Injective G.vecMul) (Fv : Fin k → ℝ)
    (c : Fin l → ℝ) : ∃! lam : Fin l → ℝ, G *ᵥ (M⁻¹ *ᵥ (Fv - Gᵀ *ᵥ lam)) + c = 0 := by
  have hS : (G * M⁻¹ * Gᵀ).PosDef := by
    have := hM.inv.mul_mul_conjTranspose_same hG
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hdet : IsUnit (G * M⁻¹ * Gᵀ).det := (hS.det_pos).ne'.isUnit
  have hkey : ∀ lam : Fin l → ℝ, G *ᵥ (M⁻¹ *ᵥ (Fv - Gᵀ *ᵥ lam)) + c =
      (G *ᵥ (M⁻¹ *ᵥ Fv) + c) - (G * M⁻¹ * Gᵀ) *ᵥ lam := by
    intro lam
    rw [mulVec_sub, mulVec_sub, ← mulVec_mulVec, ← mulVec_mulVec]
    abel
  refine ⟨(G * M⁻¹ * Gᵀ)⁻¹ *ᵥ (G *ᵥ (M⁻¹ *ᵥ Fv) + c), ?_, ?_⟩
  · simp only
    rw [hkey, mulVec_mulVec _ (G * M⁻¹ * Gᵀ) (G * M⁻¹ * Gᵀ)⁻¹, mul_nonsing_inv _ hdet,
      one_mulVec, sub_self]
  · intro lam hlam
    rw [hkey, sub_eq_zero] at hlam
    rw [hlam, mulVec_mulVec _ (G * M⁻¹ * Gᵀ)⁻¹ (G * M⁻¹ * Gᵀ), nonsing_inv_mul _ hdet,
      one_mulVec]

end Baumgarte

/-! ### GGL stabilization -/

section GGL

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

open scoped RealInnerProductSpace

/-- **GGL: the projection term vanishes on exact solutions.** If `q̇ = v − G(q)ᵀμ`,
`g(q(t)) = 0` for all `t` and `G(q)v = 0`, then `G(q)ᵀμ = 0`; hence `q̇ = v` and the GGL
solution solves the original kinematics. -/
@[powerlib_foundation] theorem ggl_projection_vanishes {g : E → V} {G : E → E →L[ℝ] V}
    (hg : ∀ x, HasFDerivAt g (G x) x) {q v : ℝ → E} {μ : ℝ → V}
    (hq : ∀ t, HasDerivAt q (v t - ContinuousLinearMap.adjoint (G (q t)) (μ t)) t)
    (hcon : ∀ t, g (q t) = 0) (hvel : ∀ t, G (q t) (v t) = 0) (t : ℝ) :
    ContinuousLinearMap.adjoint (G (q t)) (μ t) = 0 ∧ HasDerivAt q (v t) t := by
  set w := ContinuousLinearMap.adjoint (G (q t)) (μ t)
  have hchain := (hg (q t)).comp_hasDerivAt t (hq t)
  have hconst : (g ∘ q) = fun _ => (0 : V) := funext hcon
  have hzero : HasDerivAt (g ∘ q) (0 : V) t := by rw [hconst]; exact hasDerivAt_const t 0
  have h0 : G (q t) (v t - w) = 0 := hchain.unique hzero
  rw [map_sub, hvel t, zero_sub, neg_eq_zero] at h0
  have hw : ‖w‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪w, ContinuousLinearMap.adjoint (G (q t)) (μ t)⟫ = 0
    rw [ContinuousLinearMap.adjoint_inner_right, h0, inner_zero_left]
  have hw0 : w = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hw
    exact norm_eq_zero.mp this
  refine ⟨hw0, ?_⟩
  have := hq t
  rwa [show v t - ContinuousLinearMap.adjoint (G (q t)) (μ t) = v t by
    change v t - w = v t; rw [hw0, sub_zero]] at this

/-- **GGL multiplier is zero** when `G(q)ᵀ` is injective (full row rank constraint
Jacobian). -/
@[powerlib_foundation] theorem ggl_multiplier_eq_zero {g : E → V} {G : E → E →L[ℝ] V}
    (hg : ∀ x, HasFDerivAt g (G x) x) {q v : ℝ → E} {μ : ℝ → V}
    (hq : ∀ t, HasDerivAt q (v t - ContinuousLinearMap.adjoint (G (q t)) (μ t)) t)
    (hcon : ∀ t, g (q t) = 0) (hvel : ∀ t, G (q t) (v t) = 0)
    (hrank : ∀ x, Function.Injective (ContinuousLinearMap.adjoint (G x))) (t : ℝ) :
    μ t = 0 := by
  have h := (ggl_projection_vanishes hg hq hcon hvel t).1
  exact hrank (q t) (by rw [h, map_zero])

end GGL

/-! ### BDF on an index-2 DAE: no order reduction -/

section Index2

open Finset

/-- **BDF`k` on the index-2 DAE `ẋ = y`, `0 = x − p(t)`.**  The constraint forces
`x_i = p(t_i)` on the grid `t_i = i h`; the BDF equation `Σ αᵢ xᵢ = h β_k y_k` then gives
`y_k = p'(t_k)` exactly for every polynomial `p(t) = Σ_{q ≤ k} a_q t^q`, provided the method
has order `k`.  (The grid origin is arbitrary: shift `t`.) -/
@[powerlib_foundation] theorem bdf_index2_exact {k : ℕ} (α : Fin (k + 1) → ℚ) (βk : ℚ)
    (hord : (bdf k α βk).HasOrder k) (hβ : βk ≠ 0) {h : ℝ} (hh : h ≠ 0) (a : ℕ → ℝ) (y : ℝ)
    (hstep : ∑ i : Fin (k + 1), (α i : ℝ) * ∑ q ∈ range (k + 1), a q * ((i : ℝ) * h) ^ q =
      h * (βk : ℝ) * y) :
    y = ∑ q ∈ range (k + 1), a q * ((q : ℝ) * ((k : ℝ) * h) ^ (q - 1)) := by
  have hmono : ∀ q ∈ range (k + 1), ∑ i : Fin (k + 1), (α i : ℝ) * ((i : ℝ) * h) ^ q =
      h * (βk : ℝ) * ((q : ℝ) * ((k : ℝ) * h) ^ (q - 1)) := by
    intro q hq
    have hqk : q ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hq)
    have hC : (bdf k α βk).C q = 0 := hord q hqk
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · have : (bdf k α βk).C 0 = ∑ i, α i := by simp [LMM.C, bdf]
      rw [this] at hC
      simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, mul_zero]
      exact_mod_cast hC
    · have hres := LMM.residual_monomial (bdf k α βk) q hq1 h
      rw [hC] at hres
      simp only [Rat.cast_zero, zero_mul] at hres
      have hβsum : ∑ i : Fin (k + 1), ((bdf k α βk).β i : ℝ) * ((q : ℝ) * ((i : ℝ) * h) ^ (q - 1)) =
          (βk : ℝ) * ((q : ℝ) * ((k : ℝ) * h) ^ (q - 1)) := by
        rw [Finset.sum_eq_single (Fin.last k)]
        · simp [bdf]
        · intro b _ hb
          have : (b : ℕ) ≠ k := fun h' => hb (Fin.ext (by simp [h']))
          simp [bdf, this]
        · simp
      rw [hβsum] at hres
      have hα : (bdf k α βk).α = α := rfl
      rw [hα] at hres
      linarith
  have hsum : ∑ i : Fin (k + 1), (α i : ℝ) * ∑ q ∈ range (k + 1), a q * ((i : ℝ) * h) ^ q =
      h * (βk : ℝ) * ∑ q ∈ range (k + 1), a q * ((q : ℝ) * ((k : ℝ) * h) ^ (q - 1)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    calc ∑ i : Fin (k + 1), (α i : ℝ) * (a q * ((i : ℝ) * h) ^ q) =
          a q * ∑ i : Fin (k + 1), (α i : ℝ) * ((i : ℝ) * h) ^ q := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [hmono q hq]; ring
  rw [hsum] at hstep
  have hne : h * (βk : ℝ) ≠ 0 := mul_ne_zero hh (by exact_mod_cast hβ)
  exact (mul_left_cancel₀ hne hstep).symm

/-- BDF2 instance of `bdf_index2_exact`. -/
@[powerlib_foundation] theorem bdf2_index2_exact {h : ℝ} (hh : h ≠ 0) (a : ℕ → ℝ) (y : ℝ)
    (hstep : ∑ i : Fin (2 + 1), (((![1/3, -4/3, 1] : Fin 3 → ℚ) i : ℚ) : ℝ) *
        ∑ q ∈ range (2 + 1), a q * ((i : ℝ) * h) ^ q = h * ((2 / 3 : ℚ) : ℝ) * y) :
    y = ∑ q ∈ range (2 + 1), a q * ((q : ℝ) * (((2 : ℕ) : ℝ) * h) ^ (q - 1)) :=
  bdf_index2_exact _ _ bdf2_exactOrder.1 (by norm_num) hh a y hstep

end Index2

end powerlib.Numerics
