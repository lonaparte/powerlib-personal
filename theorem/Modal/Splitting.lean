import theorem.Attributes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.DirectSum.Module

/-! # Real spectral splitting `ℝⁿ = E^s ⊕ E^c ⊕ E^u` (foundation)

Foundation layer (category B; linear algebra of a real state matrix, no dynamics, no Family).

Source: work-sync `theory/T-invariant-manifolds.md` §1.2 (spectral splitting
`ℝⁿ = E^s ⊕ E^c ⊕ E^u` of the linearization, `σ(A|_{E^s}) ⊂ {Re λ < 0}` etc., `n_s + n_c + n_u = n`),
`theory/T-eigenvalue-analysis.md` §1.1 (algebraic multiplicities).

Setting: a real square matrix `A : Matrix (Fin n) (Fin n) ℝ` acting on `ℝⁿ = Fin n → ℝ` by
`x ↦ A *ᵥ x`. Eigenvalues are complex: `A_ℂ = A.map (algebraMap ℝ ℂ)` acts on `ℂⁿ` as the
endomorphism `endC A`, with generalized eigenspaces `V_μ = ker (A_ℂ − μ)^∞`
(`Module.End.maxGenEigenspace`). For a set `S ⊆ ℂ`:
* `cSpec A S = ⨆_{μ ∈ S} V_μ` (complex spectral subspace);
* `rSpec A S = {x ∈ ℝⁿ | x_ℂ ∈ cSpec A S}` (its real part).
The **stable / center / unstable subspaces** are `rSpec` of `{Re μ < 0}`, `{Re μ = 0}`,
`{Re μ > 0}` (`stableSubspace`, `centerSubspace`, `unstableSubspace`). The algebraic multiplicity of
`μ` is its root multiplicity in `charpoly A_ℂ` (`= (charpoly A).map`).

Results.
* `stableSubspace_invariant`, `centerSubspace_invariant`, `unstableSubspace_invariant`:
  each is `A`-invariant (generic: `mulVec_mem_rSpec`).
* `stable_sup_center_sup_unstable`: `E^s + E^c + E^u = ℝⁿ`;
  `isInternal_stable_center_unstable`: `ℝⁿ = E^s ⊕ E^c ⊕ E^u` is an internal direct sum
  (`DirectSum.IsInternal`: independent and spanning).
* `finrank_stableSubspace`, `finrank_centerSubspace`, `finrank_unstableSubspace`:
  `dim E^s = Σ_{Re μ < 0} m_a(μ)`, and likewise for `E^c`, `E^u` (sums over the distinct complex
  eigenvalues in the half-plane / axis of their algebraic multiplicities).
* `re_lt_of_eigvec_mem_stable`, `re_eq_of_eigvec_mem_center`, `re_gt_of_eigvec_mem_unstable`:
  `σ(A|_{E^s}) ⊂ {Re λ < 0}`, `σ(A|_{E^c}) ⊂ {Re λ = 0}`, `σ(A|_{E^u}) ⊂ {Re λ > 0}` — every
  eigenvector of `A_ℂ` in the complexification `span_ℂ E^•` has its eigenvalue in the corresponding
  set (`span_rSpec_eq_cSpec`: the complexification of `rSpec A S` is `cSpec A S`;
  `mem_of_eigvec_mem_cSpec`).
* Generic tools: `rSpec_union` (for conjugation-closed `S`, `T`:
  `rSpec A S + rSpec A T = rSpec A (S ∪ T)`; proof by taking real parts, since `cSpec A S` is
  closed under entrywise conjugation: `star_mem_cSpec`), `rSpec_disjoint` (disjoint eigenvalue
  sets give independent subspaces, Mathlib `Module.End.independent_maxGenEigenspace`),
  `rSpec_univ` (`= ℝⁿ`, Mathlib `Module.End.iSup_maxGenEigenspace_eq_top` over `ℂ`),
  `finrank_cSpec` (`dim_ℂ = Σ m_a`, Mathlib `LinearMap.finrank_maxGenEigenspace_eq`),
  `finrank_rSpec` (`dim_ℝ rSpec = dim_ℂ cSpec` for conjugation-closed `S`: real independence
  persists over `ℂ` (`linearIndependent_ofRealVec`) and the two complementary dimension counts both
  add up to `n`), `finrank_biSup_finset`.

Architecture: static linear-algebra foundation; definitions are subspaces (no behaviour, no time),
all theorems public `@[powerlib_foundation]`. The dynamical meaning (solutions of `ẋ = A x` in
`E^s` decay, etc.) is not stated here.
-/

noncomputable section
namespace powerlib.Modal
open Matrix Module Polynomial ComplexConjugate

variable {n : ℕ}

/-- The real-linear embedding `ℝⁿ → ℂⁿ`. -/
def ofRealVec (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun x i := (x i : ℂ)
  map_add' x y := by funext i; simp
  map_smul' c x := by funext i; simp

@[simp, powerlib_foundation] theorem ofRealVec_apply (x : Fin n → ℝ) (i : Fin n) : ofRealVec n x i = (x i : ℂ) := rfl

@[powerlib_foundation] theorem ofRealVec_injective : Function.Injective (ofRealVec n) := by
  intro x y h
  funext i
  have := congrFun h i
  simp only [ofRealVec_apply] at this
  exact_mod_cast this

/-- The complexified matrix as an endomorphism of `ℂⁿ`. -/
def endC (A : Matrix (Fin n) (Fin n) ℝ) : Module.End ℂ (Fin n → ℂ) :=
  Matrix.toLin' (A.map (algebraMap ℝ ℂ))

@[powerlib_foundation] theorem endC_apply (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) :
    endC A v = A.map (algebraMap ℝ ℂ) *ᵥ v := Matrix.toLin'_apply _ _

/-- The complex spectral subspace of a real matrix `A` for a set `S` of eigenvalues: the sum of the
generalized eigenspaces `ker (A − μ)^∞`, `μ ∈ S`, of the complexification. -/
def cSpec (A : Matrix (Fin n) (Fin n) ℝ) (S : Set ℂ) : Submodule ℂ (Fin n → ℂ) :=
  ⨆ μ ∈ S, (endC A).maxGenEigenspace μ

/-- The real spectral subspace: real vectors whose complexification lies in `cSpec A S`. -/
def rSpec (A : Matrix (Fin n) (Fin n) ℝ) (S : Set ℂ) : Submodule ℝ (Fin n → ℝ) :=
  ((cSpec A S).restrictScalars ℝ).comap (ofRealVec n)

@[powerlib_foundation] theorem mem_rSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ} {x : Fin n → ℝ} :
    x ∈ rSpec A S ↔ ofRealVec n x ∈ cSpec A S := Iff.rfl

/-! ## Conjugation -/

@[powerlib_foundation] theorem complexify_mulVec_star (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) :
    A.map (algebraMap ℝ ℂ) *ᵥ star v = star (A.map (algebraMap ℝ ℂ) *ᵥ v) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

@[powerlib_foundation] theorem pow_sub_star (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) (k : ℕ) (v : Fin n → ℂ) :
    ((endC A - μ • 1) ^ k) (star v) =
      star (((endC A - conj μ • 1) ^ k) v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply]
    have h1 : (endC A - μ • 1) (star v) = star ((endC A - conj μ • 1) v) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        endC_apply, complexify_mulVec_star, star_sub, star_smul]
      simp
    rw [h1, ih]

@[powerlib_foundation] theorem star_mem_maxGenEigenspace {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℂ} {v : Fin n → ℂ}
    (hv : v ∈ (endC A).maxGenEigenspace μ) :
    star v ∈ (endC A).maxGenEigenspace (conj μ) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  rw [pow_sub_star, Complex.conj_conj, hk, star_zero]

@[powerlib_foundation] theorem star_mem_cSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ}
    (hS : ∀ μ ∈ S, conj μ ∈ S) {v : Fin n → ℂ} (hv : v ∈ cSpec A S) : star v ∈ cSpec A S := by
  unfold cSpec at hv ⊢
  refine Submodule.iSup_induction _ (motive := fun v => star v ∈ ⨆ μ ∈ S,
    (endC A).maxGenEigenspace μ) hv (fun μ x hx => ?_) ?_ fun x y hx hy => ?_
  · by_cases hμ : μ ∈ S
    · rw [iSup_pos hμ] at hx
      exact (le_biSup (fun μ => (endC A).maxGenEigenspace μ)
        (hS μ hμ)) (star_mem_maxGenEigenspace hx)
    · rw [iSup_neg hμ, Submodule.mem_bot] at hx
      simp only [hx, star_zero]
      exact Submodule.zero_mem _
  · simp only [star_zero]; exact Submodule.zero_mem _
  · simp only [star_add]; exact Submodule.add_mem _ hx hy

/-! ## Invariance -/

@[powerlib_foundation] theorem mulVec_mem_cSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ} {v : Fin n → ℂ}
    (hv : v ∈ cSpec A S) : A.map (algebraMap ℝ ℂ) *ᵥ v ∈ cSpec A S := by
  unfold cSpec at hv ⊢
  refine Submodule.iSup_induction _ (motive := fun v => A.map (algebraMap ℝ ℂ) *ᵥ v ∈ ⨆ μ ∈ S,
    (endC A).maxGenEigenspace μ) hv (fun μ x hx => ?_) ?_ fun x y hx hy => ?_
  · by_cases hμ : μ ∈ S
    · rw [iSup_pos hμ] at hx
      have := Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl (endC A)) μ hx
      rw [endC_apply] at this
      exact (le_biSup (fun μ => (endC A).maxGenEigenspace μ) hμ) this
    · rw [iSup_neg hμ, Submodule.mem_bot] at hx
      simp only [hx, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · simp only [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · simp only [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy

@[powerlib_foundation] theorem ofRealVec_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ofRealVec n (A *ᵥ x) = A.map (algebraMap ℝ ℂ) *ᵥ ofRealVec n x := by
  funext i
  have := RingHom.map_mulVec (algebraMap ℝ ℂ) A x i
  exact this

/-- `rSpec A S` is `A`-invariant. -/
@[powerlib_foundation] theorem mulVec_mem_rSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ} {x : Fin n → ℝ}
    (hx : x ∈ rSpec A S) : A *ᵥ x ∈ rSpec A S := by
  rw [mem_rSpec, ofRealVec_mulVec]
  exact mulVec_mem_cSpec hx

/-! ## Real parts -/

@[powerlib_foundation] theorem ofRealVec_re (v : Fin n → ℂ) :
    ofRealVec n (fun i => (v i).re) = (2 : ℂ)⁻¹ • (v + star v) := by
  funext i
  simp only [ofRealVec_apply, Pi.smul_apply, Pi.add_apply, Pi.star_apply, smul_eq_mul]
  rw [Complex.re_eq_add_conj]
  simp [div_eq_inv_mul]

@[powerlib_foundation] theorem ofRealVec_im (v : Fin n → ℂ) :
    ofRealVec n (fun i => (v i).im) = (2 * Complex.I)⁻¹ • (v - star v) := by
  funext i
  simp only [ofRealVec_apply, Pi.smul_apply, Pi.sub_apply, Pi.star_apply, smul_eq_mul]
  rw [Complex.im_eq_sub_conj]
  simp [div_eq_inv_mul]

@[powerlib_foundation] theorem re_mem_rSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ} (hS : ∀ μ ∈ S, conj μ ∈ S)
    {v : Fin n → ℂ} (hv : v ∈ cSpec A S) : (fun i => (v i).re) ∈ rSpec A S := by
  rw [mem_rSpec, ofRealVec_re]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hv (star_mem_cSpec hS hv))

/-! ## Lattice structure -/

@[powerlib_foundation] theorem cSpec_mono {A : Matrix (Fin n) (Fin n) ℝ} {S T : Set ℂ} (h : S ⊆ T) :
    cSpec A S ≤ cSpec A T :=
  biSup_mono fun _ hμ => h hμ

@[powerlib_foundation] theorem rSpec_mono {A : Matrix (Fin n) (Fin n) ℝ} {S T : Set ℂ} (h : S ⊆ T) :
    rSpec A S ≤ rSpec A T := fun _ hx => cSpec_mono (A := A) h hx

@[powerlib_foundation] theorem cSpec_union (A : Matrix (Fin n) (Fin n) ℝ) (S T : Set ℂ) :
    cSpec A (S ∪ T) = cSpec A S ⊔ cSpec A T := iSup_union

/-- For conjugation-closed sets, real spectral subspaces add like the eigenvalue sets. -/
@[powerlib_foundation] theorem rSpec_union {A : Matrix (Fin n) (Fin n) ℝ} {S T : Set ℂ} (hS : ∀ μ ∈ S, conj μ ∈ S)
    (hT : ∀ μ ∈ T, conj μ ∈ T) : rSpec A S ⊔ rSpec A T = rSpec A (S ∪ T) := by
  refine le_antisymm (sup_le (rSpec_mono Set.subset_union_left)
    (rSpec_mono Set.subset_union_right)) fun x hx => ?_
  rw [mem_rSpec, cSpec_union, Submodule.mem_sup] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := hx
  refine Submodule.mem_sup.mpr ⟨_, re_mem_rSpec hS hy, _, re_mem_rSpec hT hz, ?_⟩
  funext i
  have := congrArg Complex.re (congrFun hyz i)
  simpa using this

@[powerlib_foundation] theorem cSpec_disjoint (A : Matrix (Fin n) (Fin n) ℝ) {S T : Set ℂ} (h : Disjoint S T) :
    Disjoint (cSpec A S) (cSpec A T) :=
  (Module.End.independent_maxGenEigenspace (endC A)).disjoint_biSup_biSup h

@[powerlib_foundation] theorem rSpec_disjoint (A : Matrix (Fin n) (Fin n) ℝ) {S T : Set ℂ} (h : Disjoint S T) :
    Disjoint (rSpec A S) (rSpec A T) := by
  rw [Submodule.disjoint_def]
  intro x hxS hxT
  have h0 := (Submodule.disjoint_def.mp (cSpec_disjoint A h)) _ hxS hxT
  exact ofRealVec_injective (by rw [h0, map_zero])

@[powerlib_foundation] theorem cSpec_univ (A : Matrix (Fin n) (Fin n) ℝ) : cSpec A Set.univ = ⊤ := by
  rw [cSpec]
  simp only [Set.mem_univ, iSup_pos]
  exact Module.End.iSup_maxGenEigenspace_eq_top _

@[powerlib_foundation] theorem rSpec_univ (A : Matrix (Fin n) (Fin n) ℝ) : rSpec A Set.univ = ⊤ := by
  rw [rSpec, cSpec_univ]
  rfl

/-! ## Dimensions -/

/-- The dimension of a finite independent supremum of subspaces is the sum of the dimensions. -/
@[powerlib_foundation] theorem finrank_biSup_finset {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] {f : ι → Submodule K V} (hf : iSupIndep f)
    (s : Finset ι) : finrank K ↥(⨆ i ∈ s, f i) = ∑ i ∈ s, finrank K ↥(f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (f a) (⨆ i ∈ (s : Set ι), f i) := hf.disjoint_biSup (by simpa using ha)
    simp only [Finset.mem_coe] at hd
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, hd.eq_bot, finrank_bot, add_zero]

@[powerlib_foundation] theorem finrank_maxGenEigenspace_endC (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) :
    finrank ℂ ↥((endC A).maxGenEigenspace μ) =
      (A.map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity μ := by
  rw [LinearMap.finrank_maxGenEigenspace_eq, endC, Matrix.charpoly_toLin']

@[powerlib_foundation] theorem maxGenEigenspace_endC_eq_bot {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℂ}
    (hμ : ¬ (A.map (algebraMap ℝ ℂ)).charpoly.IsRoot μ) : (endC A).maxGenEigenspace μ = ⊥ := by
  rw [← Submodule.finrank_eq_zero, finrank_maxGenEigenspace_endC]
  exact rootMultiplicity_eq_zero hμ

/-- `cSpec A S` is the sum over the (finitely many) eigenvalues in `S`. -/
@[powerlib_foundation] theorem cSpec_eq_finset (A : Matrix (Fin n) (Fin n) ℝ) (S : Set ℂ) [DecidablePred (· ∈ S)] :
    cSpec A S = ⨆ μ ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots.toFinset.filter (· ∈ S),
      (endC A).maxGenEigenspace μ := by
  have hχ : (A.map (algebraMap ℝ ℂ)).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  apply le_antisymm
  · refine iSup₂_le fun μ hμ => ?_
    by_cases hr : (A.map (algebraMap ℝ ℂ)).charpoly.IsRoot μ
    · exact le_biSup (fun μ => (endC A).maxGenEigenspace μ)
        (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ((mem_roots hχ).mpr hr), hμ⟩)
    · rw [maxGenEigenspace_endC_eq_bot hr]
      exact bot_le
  · refine iSup₂_le fun μ hμ => ?_
    exact le_biSup (fun μ => (endC A).maxGenEigenspace μ) (Finset.mem_filter.mp hμ).2

/-- `dim_ℂ cSpec A S = Σ_{μ ∈ σ(A) ∩ S} m_a(μ)` (algebraic multiplicities). -/
@[powerlib_foundation] theorem finrank_cSpec (A : Matrix (Fin n) (Fin n) ℝ) (S : Set ℂ) [DecidablePred (· ∈ S)] :
    finrank ℂ ↥(cSpec A S) =
      ∑ μ ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots.toFinset.filter (· ∈ S),
        (A.map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity μ := by
  rw [cSpec_eq_finset, finrank_biSup_finset (Module.End.independent_maxGenEigenspace (endC A))]
  exact Finset.sum_congr rfl fun μ _ => finrank_maxGenEigenspace_endC A μ

/-- Real vectors that are linearly independent over `ℝ` stay independent over `ℂ`. -/
@[powerlib_foundation] theorem linearIndependent_ofRealVec {ι : Type*} [Fintype ι] {b : ι → Fin n → ℝ}
    (hb : LinearIndependent ℝ b) : LinearIndependent ℂ fun i => ofRealVec n (b i) := by
  rw [Fintype.linearIndependent_iff] at hb ⊢
  intro g hg i
  have hre : ∑ j, (g j).re • b j = 0 := by
    funext k
    have := congrArg Complex.re (congrFun hg k)
    simpa [Finset.sum_apply, Complex.re_sum] using this
  have him : ∑ j, (g j).im • b j = 0 := by
    funext k
    have := congrArg Complex.im (congrFun hg k)
    simpa [Finset.sum_apply, Complex.im_sum] using this
  exact Complex.ext (hb _ hre i) (hb _ him i)

/-- `dim_ℝ rSpec A S ≤ dim_ℂ cSpec A S`. -/
@[powerlib_foundation] theorem finrank_rSpec_le (A : Matrix (Fin n) (Fin n) ℝ) (S : Set ℂ) :
    finrank ℝ ↥(rSpec A S) ≤ finrank ℂ ↥(cSpec A S) := by
  set b := Module.finBasis ℝ ↥(rSpec A S)
  have hli : LinearIndependent ℝ fun i => (b i : Fin n → ℝ) :=
    b.linearIndependent.map' (rSpec A S).subtype (Submodule.ker_subtype _)
  have hc := linearIndependent_ofRealVec hli
  have hspan : Submodule.span ℂ (Set.range fun i => ofRealVec n (b i : Fin n → ℝ)) ≤ cSpec A S :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => (b i).2)
  calc finrank ℝ ↥(rSpec A S) = Fintype.card (Fin (finrank ℝ ↥(rSpec A S))) := by simp
    _ = finrank ℂ ↥(Submodule.span ℂ (Set.range fun i => ofRealVec n (b i : Fin n → ℝ))) :=
        (finrank_span_eq_card hc).symm
    _ ≤ finrank ℂ ↥(cSpec A S) := Submodule.finrank_mono hspan

/-- For a conjugation-closed set `S`, `dim_ℝ rSpec A S = dim_ℂ cSpec A S`. -/
@[powerlib_foundation] theorem finrank_rSpec (A : Matrix (Fin n) (Fin n) ℝ) {S : Set ℂ} (hS : ∀ μ ∈ S, conj μ ∈ S) :
    finrank ℝ ↥(rSpec A S) = finrank ℂ ↥(cSpec A S) := by
  have hSc : ∀ μ ∈ Sᶜ, conj μ ∈ Sᶜ := fun μ hμ h => hμ (by simpa using hS _ h)
  have hd : Disjoint S Sᶜ := disjoint_compl_right
  have hr : finrank ℝ ↥(rSpec A S) + finrank ℝ ↥(rSpec A Sᶜ) = n := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, (rSpec_disjoint A hd).eq_bot, finrank_bot,
      add_zero, rSpec_union hS hSc, Set.union_compl_self, rSpec_univ, finrank_top,
      Module.finrank_fin_fun]
  have hc : finrank ℂ ↥(cSpec A S) + finrank ℂ ↥(cSpec A Sᶜ) = n := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, (cSpec_disjoint A hd).eq_bot, finrank_bot,
      add_zero, ← cSpec_union, Set.union_compl_self, cSpec_univ, finrank_top,
      Module.finrank_fin_fun]
  have h1 := finrank_rSpec_le A S
  have h2 := finrank_rSpec_le A Sᶜ
  omega

/-! ## The stable / center / unstable splitting -/

/-- The real **stable subspace** `E^s`: real parts of the generalized eigenspaces for `Re λ < 0`. -/
def stableSubspace (A : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  rSpec A {μ | μ.re < 0}

/-- The real **center subspace** `E^c`: generalized eigenspaces for `Re λ = 0`. -/
def centerSubspace (A : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  rSpec A {μ | μ.re = 0}

/-- The real **unstable subspace** `E^u`: generalized eigenspaces for `Re λ > 0`. -/
def unstableSubspace (A : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  rSpec A {μ | 0 < μ.re}

@[powerlib_foundation] theorem conj_mem_re_lt {μ : ℂ} (h : μ ∈ {μ : ℂ | μ.re < 0}) : conj μ ∈ {μ : ℂ | μ.re < 0} := by
  simpa using h

@[powerlib_foundation] theorem conj_mem_re_eq {μ : ℂ} (h : μ ∈ {μ : ℂ | μ.re = 0}) : conj μ ∈ {μ : ℂ | μ.re = 0} := by
  simpa using h

@[powerlib_foundation] theorem conj_mem_re_gt {μ : ℂ} (h : μ ∈ {μ : ℂ | 0 < μ.re}) : conj μ ∈ {μ : ℂ | 0 < μ.re} := by
  simpa using h

/-- `E^s`, `E^c`, `E^u` are `A`-invariant. -/
@[powerlib_foundation] theorem stableSubspace_invariant {A : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ stableSubspace A) : A *ᵥ x ∈ stableSubspace A := mulVec_mem_rSpec hx

@[powerlib_foundation] theorem centerSubspace_invariant {A : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ centerSubspace A) : A *ᵥ x ∈ centerSubspace A := mulVec_mem_rSpec hx

@[powerlib_foundation] theorem unstableSubspace_invariant {A : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ unstableSubspace A) : A *ᵥ x ∈ unstableSubspace A := mulVec_mem_rSpec hx

/-- `E^s + E^c + E^u = ℝⁿ`. -/
@[powerlib_foundation] theorem stable_sup_center_sup_unstable (A : Matrix (Fin n) (Fin n) ℝ) :
    stableSubspace A ⊔ centerSubspace A ⊔ unstableSubspace A = ⊤ := by
  rw [stableSubspace, centerSubspace, unstableSubspace,
    rSpec_union (fun _ => conj_mem_re_lt) (fun _ => conj_mem_re_eq),
    rSpec_union (fun _ h => h.elim (fun h => Or.inl (conj_mem_re_lt h))
      (fun h => Or.inr (conj_mem_re_eq h))) (fun _ => conj_mem_re_gt)]
  convert rSpec_univ A
  ext μ
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rcases lt_trichotomy μ.re 0 with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **Real spectral splitting** `ℝⁿ = E^s ⊕ E^c ⊕ E^u`: the three subspaces are independent and
span `ℝⁿ` (an internal direct sum). -/
@[powerlib_foundation] theorem isInternal_stable_center_unstable (A : Matrix (Fin n) (Fin n) ℝ) :
    DirectSum.IsInternal
      (fun k : Fin 3 => ![stableSubspace A, centerSubspace A, unstableSubspace A] k) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [centerSubspace, unstableSubspace, rSpec_union (fun _ => conj_mem_re_eq)
        (fun _ => conj_mem_re_gt)]
      refine rSpec_disjoint A (Set.disjoint_left.mpr fun μ h1 h2 => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union] at h1 h2
      rcases h2 with h2 | h2 <;> linarith
    · rw [unstableSubspace, stableSubspace, rSpec_union (fun _ => conj_mem_re_gt)
        (fun _ => conj_mem_re_lt)]
      refine rSpec_disjoint A (Set.disjoint_left.mpr fun μ h1 h2 => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union] at h1 h2
      rcases h2 with h2 | h2 <;> linarith
    · rw [stableSubspace, centerSubspace, rSpec_union (fun _ => conj_mem_re_lt)
        (fun _ => conj_mem_re_eq)]
      refine rSpec_disjoint A (Set.disjoint_left.mpr fun μ h1 h2 => ?_)
      simp only [Set.mem_ofPred_eq, Set.mem_union] at h1 h2
      rcases h2 with h2 | h2 <;> linarith
  · rw [iSup_fin_three]
    simpa using stable_sup_center_sup_unstable A

/-- `dim E^s = Σ_{Re λ < 0} m_a(λ)`: the sum of the algebraic multiplicities (root multiplicities
in the characteristic polynomial) of the eigenvalues with negative real part. -/
@[powerlib_foundation] theorem finrank_stableSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    finrank ℝ ↥(stableSubspace A) =
      ∑ μ ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots.toFinset.filter (fun μ => μ.re < 0),
        (A.map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity μ := by
  classical
  rw [stableSubspace, finrank_rSpec A (fun _ => conj_mem_re_lt), finrank_cSpec]
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

/-- `dim E^c = Σ_{Re λ = 0} m_a(λ)`. -/
@[powerlib_foundation] theorem finrank_centerSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    finrank ℝ ↥(centerSubspace A) =
      ∑ μ ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots.toFinset.filter (fun μ => μ.re = 0),
        (A.map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity μ := by
  classical
  rw [centerSubspace, finrank_rSpec A (fun _ => conj_mem_re_eq), finrank_cSpec]
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

/-- `dim E^u = Σ_{Re λ > 0} m_a(λ)`. -/
@[powerlib_foundation] theorem finrank_unstableSubspace (A : Matrix (Fin n) (Fin n) ℝ) :
    finrank ℝ ↥(unstableSubspace A) =
      ∑ μ ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots.toFinset.filter (fun μ => 0 < μ.re),
        (A.map (algebraMap ℝ ℂ)).charpoly.rootMultiplicity μ := by
  classical
  rw [unstableSubspace, finrank_rSpec A (fun _ => conj_mem_re_gt), finrank_cSpec]
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

/-! ## Complexification and the spectrum of the restriction -/

@[powerlib_foundation] theorem im_mem_rSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ} (hS : ∀ μ ∈ S, conj μ ∈ S)
    {v : Fin n → ℂ} (hv : v ∈ cSpec A S) : (fun i => (v i).im) ∈ rSpec A S := by
  rw [mem_rSpec, ofRealVec_im]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hv (star_mem_cSpec hS hv))

/-- For a conjugation-closed `S`, `cSpec A S` is the complexification of `rSpec A S`. -/
@[powerlib_foundation] theorem span_rSpec_eq_cSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ}
    (hS : ∀ μ ∈ S, conj μ ∈ S) :
    Submodule.span ℂ (ofRealVec n '' (rSpec A S : Set (Fin n → ℝ))) = cSpec A S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro v hv
    have hdec : v = ofRealVec n (fun i => (v i).re) + Complex.I • ofRealVec n (fun i => (v i).im) := by
      funext i
      simp [Complex.ext_iff]
    rw [hdec]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨_, re_mem_rSpec hS hv, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, im_mem_rSpec hS hv, rfl⟩))

/-- An eigenvector of `A_ℂ` lying in `cSpec A S` has its eigenvalue in `S`. -/
@[powerlib_foundation] theorem mem_of_eigvec_mem_cSpec {A : Matrix (Fin n) (Fin n) ℝ} {S : Set ℂ} {ν : ℂ}
    {v : Fin n → ℂ} (hv0 : v ≠ 0) (hAv : A.map (algebraMap ℝ ℂ) *ᵥ v = ν • v)
    (hv : v ∈ cSpec A S) : ν ∈ S := by
  by_contra hν
  have hgen : v ∈ (endC A).maxGenEigenspace ν := by
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, endC_apply, hAv,
      sub_self]
  have hd : Disjoint ((endC A).maxGenEigenspace ν) (cSpec A S) :=
    (Module.End.independent_maxGenEigenspace (endC A)).disjoint_biSup hν
  exact hv0 ((Submodule.disjoint_def.mp hd) v hgen hv)

/-- **Spectrum of `A` on `E^s`, `E^c`, `E^u`**: an eigenvector of `A_ℂ` in the complexification
`span_ℂ E^s` (resp. `E^c`, `E^u`) has eigenvalue with `Re < 0` (resp. `= 0`, `> 0`). -/
@[powerlib_foundation] theorem re_lt_of_eigvec_mem_stable {A : Matrix (Fin n) (Fin n) ℝ} {ν : ℂ} {v : Fin n → ℂ}
    (hv0 : v ≠ 0) (hAv : A.map (algebraMap ℝ ℂ) *ᵥ v = ν • v)
    (hv : v ∈ Submodule.span ℂ (ofRealVec n '' (stableSubspace A : Set (Fin n → ℝ)))) :
    ν.re < 0 := by
  rw [stableSubspace, span_rSpec_eq_cSpec (fun _ => conj_mem_re_lt)] at hv
  exact mem_of_eigvec_mem_cSpec hv0 hAv hv

@[powerlib_foundation] theorem re_eq_of_eigvec_mem_center {A : Matrix (Fin n) (Fin n) ℝ} {ν : ℂ} {v : Fin n → ℂ}
    (hv0 : v ≠ 0) (hAv : A.map (algebraMap ℝ ℂ) *ᵥ v = ν • v)
    (hv : v ∈ Submodule.span ℂ (ofRealVec n '' (centerSubspace A : Set (Fin n → ℝ)))) :
    ν.re = 0 := by
  rw [centerSubspace, span_rSpec_eq_cSpec (fun _ => conj_mem_re_eq)] at hv
  exact mem_of_eigvec_mem_cSpec hv0 hAv hv

@[powerlib_foundation] theorem re_gt_of_eigvec_mem_unstable {A : Matrix (Fin n) (Fin n) ℝ} {ν : ℂ} {v : Fin n → ℂ}
    (hv0 : v ≠ 0) (hAv : A.map (algebraMap ℝ ℂ) *ᵥ v = ν • v)
    (hv : v ∈ Submodule.span ℂ (ofRealVec n '' (unstableSubspace A : Set (Fin n → ℝ)))) :
    0 < ν.re := by
  rw [unstableSubspace, span_rSpec_eq_cSpec (fun _ => conj_mem_re_gt)] at hv
  exact mem_of_eigvec_mem_cSpec hv0 hAv hv

end powerlib.Modal
