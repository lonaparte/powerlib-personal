import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Invariant sets and invariant manifolds: the provable core

Invariance and tangency, the homological (Sylvester) equations of centre-manifold and normal-form
computations, and heteroclinic orbits as intersections of stable and unstable sets.

Scope.
* Generic statements about autonomous ODEs `ẋ = f(x)` on a normed space; no engineering model,
  so no model family is defined; all results remain public foundation support. Solution segments
  are Mathlib integral curves on `Icc`; uniqueness is LeanForControl's
  `eqOn_of_isIntegralCurveOn_Icc`, applied directly.
* Invariant-set definitions are already available: LeanForControl's `IsPositivelyInvariant` and
  Mathlib's `IsInvariant` / `IsForwardInvariant` for flows. The real spectral decomposition
  `ℝⁿ = E^s ⊕ E^c ⊕ E^u`, the stable/unstable/center manifold theorems and NHIM persistence are
  not formalized.

Source: work-sync theory/T-invariant-manifolds.md §1.1 (invariance ⇔ tangency), §1.5.1
(order-by-order solvability under the spectral gap), §1.8 (heteroclinic ⇔ `W^u ∩ W^s`).

Results.
* Invariance ⇒ tangency (`vectorField_mem_tangentCone`): if a forward solution segment starting
  at `p` stays in a set `S` (in particular if `S` is positively invariant and a solution through
  `p` exists), then `f(p)` lies in the tangent cone of `S` at `p`. For an embedded submanifold the
  tangent cone is the tangent space, so this is `f(p) ∈ T_p𝓜`.
* Homological (Sylvester) equations (`sylvester_eq_zero`, `sylvester_unique`): for complex
  matrices `T`, `S` with disjoint spectra, `T X − X S = R` has exactly one solution `X` for every
  `R`. This generalizes LeanForControl's `MatrixAlgebra.bilinear_eq_zero_of_no_resonance` (one
  operator acting on both arguments) to two operators; it is the solvability statement for the
  order-by-order equations of center-manifold / normal-form computations.
* Order-`α` coefficient equations (`homological_coeff_unique`): if `σ(A_c) ⊂ jℝ` (eigenvalues
  `λᵢ` with `Re λᵢ = 0`) and the hyperbolic block `A_h` has no eigenvalue on `jℝ` (spectral gap),
  then `(A_h − (α·λ) I) h_α = R_α` is uniquely solvable for every multi-index `α`.
* Heteroclinic orbits (`heteroclinic_iff`): with the global stable/unstable sets `W^s(b)`,
  `W^u(a)` read through global solutions (initial states of global solutions converging to `b`
  forwards, resp. to `a` backwards; written out in the statements), a global solution `γ` is
  heteroclinic from `a` to `b` iff `γ(0) ∈ W^u(a) ∩ W^s(b)`, for a globally Lipschitz field
  (uniqueness in both time directions); the forward implication needs no uniqueness, and then
  every point of the orbit lies in `W^u(a) ∩ W^s(b)` (`heteroclinic_mem`).

Corrections. (T-invariant-manifolds.md, recorded only): the NHIM rate inequalities of §1.7 are
inconsistent as written (`α_s, α_u > rβ` together with `0 < α_s < β < α_u`), and the reduction
principle of §1.5 needs `E^u = {0}` for "the local asymptotic behaviour is determined by the
reduced field".
-/

noncomputable section
namespace powerlib.NormalForm

open Set Filter Topology Polynomial

/-! ## Invariance implies tangency -/

/-- If a solution starting at `p` stays in `S` on `(0, T)`, then `f(p) ∈ tangentConeAt ℝ S p`. -/
@[tmio T, powerlib_foundation] theorem vectorField_mem_tangentCone {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} {S : Set E} {φ : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Icc 0 T)) (hS : ∀ t ∈ Ioo 0 T, φ t ∈ S) :
    f (φ 0) ∈ tangentConeAt ℝ S (φ 0) := by
  have hd : HasDerivWithinAt φ (f (φ 0)) (Icc 0 T) 0 := hφ 0 ⟨le_rfl, hT.le⟩
  have hd' : HasDerivWithinAt φ (f (φ 0)) (Ioi 0) 0 :=
    (hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)).mono Ioi_subset_Ici_self
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp hd')
  rw [sdiff_singleton_eq_self (by simp)] at hslope
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => t⁻¹) (fun t => φ t - φ 0)
    ?_ ?_ ?_
  · have hc : ContinuousWithinAt φ (Ici 0) 0 :=
      (hd.continuousWithinAt.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT))
    simpa using (hc.mono Ioi_subset_Ici_self).tendsto.sub_const (φ 0)
  · filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    simpa using hS t ht
  · refine hslope.congr' ?_
    filter_upwards with t
    simp [slope_def_module]

/-! ## Sylvester / homological equations -/

section Sylvester

open Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- If `T X = X S`, then `q(T) X = X q(S)` for every polynomial `q`. -/
@[powerlib_foundation] theorem aeval_mul_intertwine {T : Matrix m m ℂ} {S : Matrix n n ℂ}
    {Y : Matrix m n ℂ} (h : T * Y = Y * S) (q : ℂ[X]) :
    aeval T q * Y = Y * aeval S q := by
  induction q using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k a ih =>
    have : aeval T (C a * X ^ (k + 1)) = aeval T (C a * X ^ k) * T := by
      simp [pow_succ, mul_assoc]
    have h2 : aeval S (C a * X ^ (k + 1)) = aeval S (C a * X ^ k) * S := by
      simp [pow_succ, mul_assoc]
    rw [this, h2, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- Disjoint spectra: the only solution of `T X − X S = 0` is `X = 0`. -/
@[powerlib_foundation] theorem sylvester_eq_zero {T : Matrix m m ℂ} {S : Matrix n n ℂ}
    (hdisj : ∀ z : ℂ, z ∈ spectrum ℂ T → z ∉ spectrum ℂ S) {Y : Matrix m n ℂ}
    (h : T * Y - Y * S = 0) : Y = 0 := by
  have hTX : T * Y = Y * S := sub_eq_zero.mp h
  rcases isEmpty_or_nonempty n with hn | hn
  · ext i j; exact (IsEmpty.false j).elim
  set p := S.charpoly
  have hp : aeval T p * Y = 0 := by
    rw [aeval_mul_intertwine hTX, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  -- `p(T)` is invertible
  have hdeg : 0 < degree p := by
    rw [Matrix.charpoly_degree_eq_dim]
    exact_mod_cast Fintype.card_pos
  have hunit : IsUnit (aeval T p) := by
    rw [← spectrum.zero_notMem_iff ℂ, spectrum.map_polynomial_aeval_of_degree_pos T p hdeg]
    rintro ⟨z, hz, hz0⟩
    apply hdisj z hz
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact hz0
  obtain ⟨u, hu⟩ := hunit
  have : (↑u⁻¹ : Matrix m m ℂ) * (aeval T p * Y) = Y := by
    rw [← Matrix.mul_assoc, ← hu, Units.inv_mul, Matrix.one_mul]
  rw [← this, hp, Matrix.mul_zero]

/-- Disjoint spectra: `T X − X S = R` has exactly one solution for every `R`. -/
@[powerlib_foundation] theorem sylvester_unique {T : Matrix m m ℂ} {S : Matrix n n ℂ}
    (hdisj : ∀ z : ℂ, z ∈ spectrum ℂ T → z ∉ spectrum ℂ S) (R : Matrix m n ℂ) :
    ∃! Y : Matrix m n ℂ, T * Y - Y * S = R := by
  let L : Matrix m n ℂ →ₗ[ℂ] Matrix m n ℂ :=
    { toFun := fun Y => T * Y - Y * S
      map_add' := fun Y Z => by rw [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c Y => by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    exact sylvester_eq_zero hdisj hY
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨Y, hY⟩ := hsurj R
  exact ⟨Y, hY, fun Z hZ => hinj (hZ.trans hY.symm)⟩

/-- Order-`α` coefficient equation with a spectral gap: if every eigenvalue of `A_h` has nonzero
real part and `Re λᵢ = 0`, then `(A_h − (Σ αᵢ λᵢ) I) h = R` is uniquely solvable. -/
@[powerlib_foundation] theorem homological_coeff_unique {k : ℕ} {A : Matrix m m ℂ}
    (hgap : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) (lam : Fin k → ℂ) (hlam : ∀ i, (lam i).re = 0)
    (α : Fin k → ℕ) (R : m → ℂ) :
    ∃! h : m → ℂ, (A - (∑ i, (α i : ℂ) * lam i) • (1 : Matrix m m ℂ)) *ᵥ h = R := by
  set c := ∑ i, (α i : ℂ) * lam i
  have hc : c.re = 0 := by
    simp [c, Complex.re_sum, hlam]
  have hnot : c ∉ spectrum ℂ A := fun hmem => hgap c hmem hc
  rw [spectrum.notMem_iff] at hnot
  have hunit : IsUnit (A - c • (1 : Matrix m m ℂ)) := by
    have : A - c • (1 : Matrix m m ℂ) = -(algebraMap ℂ (Matrix m m ℂ) c - A) := by
      rw [Algebra.algebraMap_eq_smul_one]; abel
    rw [this]; exact hnot.neg
  obtain ⟨u, hu⟩ := hunit
  refine ⟨(↑u⁻¹ : Matrix m m ℂ) *ᵥ R, ?_, fun h hh => ?_⟩
  · simp only
    rw [← hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rw [← hh, ← hu, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

end Sylvester

/-! ## Heteroclinic orbits -/

section Heteroclinic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! The behavioural notions of this section are written out in each statement (behaviour is
defined only in the semantic layer):
* a *global solution* of `ẋ = f(x)` is a curve `γ : ℝ → E` with `∀ t, HasDerivAt γ (f (γ t)) t`;
* the *global stable set* `W^s(b)` is the set of initial states `ψ 0` of global solutions `ψ`
  converging to `b` as `t → +∞` (`Tendsto ψ atTop (𝓝 b)`); the *global unstable set* `W^u(a)` is
  the set of initial states of global solutions converging to `a` backwards
  (`Tendsto ψ atBot (𝓝 a)`);
* a *heteroclinic orbit* from `a` to `b` is a global solution `γ` with `γ → a` as `t → −∞` and
  `γ → b` as `t → +∞`. -/

/-- A time shift of a global solution of `ẋ = f(x)` (a curve with
`∀ t, HasDerivAt γ (f (γ t)) t`) is again a global solution. -/
@[powerlib_foundation] theorem IsGlobalSolution.shift {f : E → E} {γ : ℝ → E}
    (h : ∀ t, HasDerivAt γ (f (γ t)) t) (c : ℝ) :
    ∀ t, HasDerivAt (fun t => γ (t + c)) (f (γ (t + c))) t :=
  fun t => (h (t + c)).comp_add_const t c

/-- Every point of a heteroclinic orbit from `a` to `b` (a global solution `γ` with `γ → a` as
`t → −∞` and `γ → b` as `t → +∞`) lies in `W^u(a) ∩ W^s(b)`: it is the initial state of a global
solution converging to `a` backwards and of one converging to `b` forwards. -/
@[powerlib_foundation] theorem heteroclinic_mem {f : E → E} {a b : E} {γ : ℝ → E}
    (h : (∀ t, HasDerivAt γ (f (γ t)) t) ∧ Tendsto γ atBot (𝓝 a) ∧ Tendsto γ atTop (𝓝 b))
    (t₀ : ℝ) :
    γ t₀ ∈ {x | ∃ ψ : ℝ → E, (∀ t, HasDerivAt ψ (f (ψ t)) t) ∧ ψ 0 = x ∧
          Tendsto ψ atBot (𝓝 a)} ∩
        {x | ∃ ψ : ℝ → E, (∀ t, HasDerivAt ψ (f (ψ t)) t) ∧ ψ 0 = x ∧
          Tendsto ψ atTop (𝓝 b)} := by
  obtain ⟨hγ, ha, hb⟩ := h
  have hshift := IsGlobalSolution.shift hγ t₀
  have hT : Tendsto (fun t : ℝ => t + t₀) atTop atTop :=
    tendsto_atTop_add_const_right _ t₀ tendsto_id
  have hB : Tendsto (fun t : ℝ => t + t₀) atBot atBot :=
    tendsto_atBot_add_const_right _ t₀ tendsto_id
  exact ⟨⟨_, hshift, by simp, ha.comp hB⟩, ⟨_, hshift, by simp, hb.comp hT⟩⟩

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- Uniqueness of global solutions (`∀ t, HasDerivAt γ (f (γ t)) t`) for a globally Lipschitz
field (both time directions). -/
@[powerlib_foundation] theorem globalSolution_unique {f : E → E} {K : NNReal}
    (hf : LipschitzWith K f) {γ ψ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (f (γ t)) t)
    (hψ : ∀ t, HasDerivAt ψ (f (ψ t)) t) (h0 : γ 0 = ψ 0) : γ = ψ := by
  funext t
  rcases le_total 0 t with ht | ht
  · exact _root_.eqOn_of_isIntegralCurveOn_Icc (f := fun _ x => f x) (fun _ => hf)
      (fun s _ => (hγ s).hasDerivWithinAt) (fun s _ => (hψ s).hasDerivWithinAt) h0 ⟨ht, le_rfl⟩
  · -- reverse time: `s ↦ γ(−s)` solves `ẏ = −f(y)`
    have hrev : ∀ φ : ℝ → E, (∀ t, HasDerivAt φ (f (φ t)) t) →
        IsIntegralCurveOn (fun s => φ (-s)) (fun _ x => -f x) (Icc 0 (-t)) := by
      intro φ hφ s _
      have := (hφ (-s)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this.hasDerivWithinAt
    have := _root_.eqOn_of_isIntegralCurveOn_Icc (f := fun _ x => -f x) (K := K)
      (fun _ => hf.neg) (hrev γ hγ) (hrev ψ hψ) (by simpa using h0)
      (show -t ∈ Icc 0 (-t) from ⟨by linarith, le_rfl⟩)
    simpa using this

omit [CompleteSpace E] in
/-- For a globally Lipschitz field, a global solution `γ` is heteroclinic from `a` to `b`
(`γ → a` as `t → −∞` and `γ → b` as `t → +∞`) iff `γ(0) ∈ W^u(a) ∩ W^s(b)`, i.e. `γ(0)` is the
initial state of a global solution converging to `a` backwards and of one converging to `b`
forwards. -/
@[powerlib_foundation] theorem heteroclinic_iff {f : E → E} {K : NNReal} (hf : LipschitzWith K f)
    {a b : E} {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (f (γ t)) t) :
    ((∀ t, HasDerivAt γ (f (γ t)) t) ∧ Tendsto γ atBot (𝓝 a) ∧ Tendsto γ atTop (𝓝 b)) ↔
      γ 0 ∈ {x | ∃ ψ : ℝ → E, (∀ t, HasDerivAt ψ (f (ψ t)) t) ∧ ψ 0 = x ∧
          Tendsto ψ atBot (𝓝 a)} ∩
        {x | ∃ ψ : ℝ → E, (∀ t, HasDerivAt ψ (f (ψ t)) t) ∧ ψ 0 = x ∧
          Tendsto ψ atTop (𝓝 b)} := by
  constructor
  · intro h; exact heteroclinic_mem h 0
  · rintro ⟨⟨ψ₁, hψ₁, h₁, ha⟩, ⟨ψ₂, hψ₂, h₂, hb⟩⟩
    have e₁ := globalSolution_unique hf hγ hψ₁ h₁.symm
    have e₂ := globalSolution_unique hf hγ hψ₂ h₂.symm
    exact ⟨hγ, e₁ ▸ ha, e₂ ▸ hb⟩

end Heteroclinic

end powerlib.NormalForm
