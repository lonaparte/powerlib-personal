import dependencies.Mathlib
import theorem.Attributes

/-! # Weighted graph Laplacians and grounded Laplacians

Static foundation for network models: weighted and grounded Laplacians and the discrete minimum
principle, no-shunt bus admittance matrices, the signed incidence matrix and Kron reduction.

Scope.
* A network is a finite node set `ι` with an edge-weight matrix `W` (`W i j ≥ 0`, symmetric
  where stated); the diagonal of `W` is irrelevant. The Laplacian is `L = diag(∑ⱼ Wᵢⱼ) - W`, so
  `(L x)ᵢ = ∑ⱼ Wᵢⱼ (xᵢ - xⱼ)`. A grounding vector `g ≥ 0` (shunt conductance or, for the
  frequency divider, the coupling to machine buses) gives the grounded Laplacian `L + diag g`.
* Connectivity is the reflexive-transitive closure of the relation `0 < W i j`.
* These are algebraic statements; no power-flow or dynamic claim is made here (the lossless
  power-flow map and its Laplacian Jacobian are in `theorem/Grid/PowerFlow.lean`).

Source: work-sync `theory/T-synchronization-manifold.md` §1.1 (weighted Laplacian, `L𝟙 = 0`,
positive semidefinite), `theory/T-local-frequency.md` §1.4 and §2.7 (nonsingularity of `B_bb`),
`theory/T-telegrapher-bergeron.md` §1.4.1 (EMTP nodal matrix), `theory/T-dae-systems.md` §2.1
(no-shunt admittance matrix), `theory/T-ph.md` §1.6.bis (signed incidence),
`theory/T-power-system-ph.md` §1.7 (Kron reduction).

Results.
* Discrete minimum principle (absent from Mathlib): if every node reaches a grounded node
  through positive-weight edges then `(L + diag g) x ≥ 0` forces `x ≥ 0`
  (`nonneg_of_grounded_mulVec_nonneg`). Consequences: `L + diag g` is invertible
  (`grounded_isUnit`, `grounded_det_ne_zero`), its inverse is entrywise nonnegative (the
  M-matrix special case, `grounded_inv_nonneg`), and, for symmetric weights, it is positive
  definite exactly when every node has such a path to ground (`grounded_posDef_iff`). Without
  such a path the indicator of the node's component lies in the kernel
  (`grounded_mulVec_component_eq_zero`), so for symmetric weights `L + diag g` is nonsingular
  exactly when every node reaches ground (`grounded_det_ne_zero_iff`).
* Null directions of a nonnegative Laplacian form with weights of any sign satisfy every node
  balance `(L g)ᵢ = 0` (`node_balance_eq_zero_of_form_eq_zero`).
* The Laplacian over any commutative ring: rows `(L x)ᵢ = ∑ⱼ Wᵢⱼ (xᵢ − xⱼ)`
  (`laplacian_mulVec_apply`), `L𝟙 = 0` (`laplacian_mulVec_const`), zero column sums for symmetric
  weights (`sum_laplacian_mulVec`), and `laplacian_map` (real weights read as complex ones: the
  eigenvector manipulations of the networked swing Jacobian).
* A bus admittance matrix built from branch admittances with no shunt (ground) branch
  (`ybusNoShunt`, the Laplacian of the branch admittances) has `Y 𝟏 = 0`
  (`laplacian_mulVec_const`), hence is singular for every topology
  (`ybusNoShunt_det_eq_zero`; two-bus counterexample `ybus_two_bus_singular`, the correction of
  `theory/T-dae-systems.md` §2.1).
* The signed node–branch incidence matrix `signedIncidence tail head` of a directed multigraph
  (`+1` at the tail, `−1` at the head) satisfies KVL, `(𝓑ᵀ v)_k = v(tail k) − v(head k)`
  (`signedIncidence_transpose_mulVec`), and KCL, `(𝓑 c)_j` is the total current leaving node `j`
  (`signedIncidence_mulVec`); every column sums to zero
  (`signedIncidence_col_sum`). The RL-network pH models built on it are in
  `theorem/Grid/RLNetwork.lean`, the multi-area tie-line graph in
  `theorem/PowerSystem/Frequency/LFCNetwork.lean`.
* Kron reduction: eliminating internal nodes with zero injection from a linear resistive network
  `Y` gives `i_b = (Y_bb − Y_bi Y_ii⁻¹ Y_ib) v_b` (`kron_current`), conserves the port power
  (`kron_power`), and (Mathlib Schur complement) keeps a PSD network PSD (`kron_posSemidef`).
-/

noncomputable section
namespace powerlib.Network
open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted Laplacian `diag(∑ⱼ Wᵢⱼ) - W`, with weights in any commutative ring (real line
weights, complex branch admittances). -/
def laplacian {R : Type*} [CommRing R] (W : Matrix ι ι R) : Matrix ι ι R :=
  diagonal (fun i => ∑ j, W i j) - W

/-- Reachability through edges of positive weight. -/
def Reach (W : Matrix ι ι ℝ) : ι → ι → Prop := Relation.ReflTransGen fun a b => 0 < W a b

section Ring

variable {R : Type*} [CommRing R]

@[tmio T, powerlib_foundation] theorem laplacian_mulVec_apply (W : Matrix ι ι R) (x : ι → R)
    (i : ι) :
    (laplacian W *ᵥ x) i = ∑ j, W i j * (x i - x j) := by
  rw [laplacian, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
  simp only [mulVec, dotProduct, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

@[tmio T, powerlib_foundation] theorem laplacian_apply (W : Matrix ι ι R) (i j : ι) :
    laplacian W i j = (if i = j then ∑ k, W i k else 0) - W i j := by
  simp [laplacian, diagonal_apply]

@[tmio T, powerlib_foundation] theorem laplacian_mulVec_const (W : Matrix ι ι R) (c : R) :
    laplacian W *ᵥ (fun _ => c) = 0 := by
  ext i
  simp [laplacian_mulVec_apply]

@[tmio T, powerlib_foundation] theorem laplacian_transpose {W : Matrix ι ι R}
    (hW : ∀ i j, W i j = W j i) : (laplacian W)ᵀ = laplacian W := by
  ext i j
  by_cases h : i = j
  · subst h; rfl
  · simp [laplacian, h, Ne.symm h, hW i j]

/-- Column sums of a symmetric Laplacian vanish: `𝟙ᵀ L x = 0`. -/
@[tmio T, powerlib_foundation] theorem sum_laplacian_mulVec {W : Matrix ι ι R}
    (hW : ∀ i j, W i j = W j i) (x : ι → R) : ∑ i, (laplacian W *ᵥ x) i = 0 := by
  simp only [laplacian_mulVec_apply, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hW]

/-- A ring homomorphism of the weights commutes with the Laplacian (e.g. real line weights read
as complex weights). -/
@[tmio T, powerlib_foundation] theorem laplacian_map {S : Type*} [CommRing S] (f : R →+* S)
    (W : Matrix ι ι R) : (laplacian W).map f = laplacian (W.map f) := by
  ext i j
  simp [laplacian_apply, apply_ite f, map_sum]

end Ring

omit [Fintype ι] [DecidableEq ι] in
/-- Propagation of an edge relation along positive-weight paths. -/
@[tmio T, powerlib_foundation] theorem eq_of_reach {α : Type*} {W : Matrix ι ι ℝ} {x : ι → α}
    (hx : ∀ a b, 0 < W a b → x a = x b) {i k : ι} (h : Reach W i k) : x i = x k := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hx _ _ hbc)

omit [DecidableEq ι] in
/-- Complex Hermitian form of a symmetric real Laplacian: `uᴴ L u = ½ ∑ Wᵢⱼ |uᵢ - uⱼ|²`. -/
@[tmio T, powerlib_foundation] theorem star_dotProduct_laplacian_mulVec {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (u : ι → ℂ) :
    ∑ i, star (u i) * ∑ j, (W i j : ℂ) * (u i - u j) =
      (((∑ i, ∑ j, W i j * Complex.normSq (u i - u j)) / 2 : ℝ) : ℂ) := by
  have h2 : ∑ i, ∑ j, (W i j : ℂ) * (star (u i) * (u i - u j)) =
      ∑ i, ∑ j, (W i j : ℂ) * (star (u j) * (u j - u i)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hW]
  have h3 : ((∑ i, ∑ j, W i j * Complex.normSq (u i - u j) : ℝ) : ℂ) =
      ∑ i, ∑ j, (W i j : ℂ) * (star (u i) * (u i - u j)) +
        ∑ i, ∑ j, (W i j : ℂ) * (star (u j) * (u j - u i)) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sub, Complex.star_def]
    ring
  have h1 : ∑ i, star (u i) * ∑ j, (W i j : ℂ) * (u i - u j) =
      ∑ i, ∑ j, (W i j : ℂ) * (star (u i) * (u i - u j)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  push_cast
  rw [show ((∑ i, ∑ j, W i j * Complex.normSq (u i - u j) : ℝ) : ℂ) =
      ∑ i, ∑ j, (W i j : ℂ) * (Complex.normSq (u i - u j) : ℂ) by push_cast; rfl] at h3
  rw [h3, ← h2]
  ring

/-- Quadratic form of a symmetric weighted Laplacian (the real reading of
`star_dotProduct_laplacian_mulVec`). -/
@[tmio T, powerlib_foundation] theorem dotProduct_laplacian_mulVec {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (x : ι → ℝ) :
    dotProduct x (laplacian W *ᵥ x) = (∑ i, ∑ j, W i j * (x i - x j) ^ 2) / 2 := by
  have h := star_dotProduct_laplacian_mulVec hW fun i => (x i : ℂ)
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_sum, Complex.ofReal_inj, Complex.normSq_ofReal] at h
  simp only [dotProduct, laplacian_mulVec_apply, h, sq]

@[tmio T, powerlib_foundation] theorem laplacian_posSemidef_form {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (x : ι → ℝ) :
    0 ≤ dotProduct x (laplacian W *ᵥ x) := by
  rw [dotProduct_laplacian_mulVec hW]
  apply div_nonneg _ zero_le_two
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hpos i j) (sq_nonneg _)

/-- A zero Laplacian quadratic form forces equality across every positive edge. -/
@[tmio T, powerlib_foundation] theorem edge_eq_of_form_zero {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) {x : ι → ℝ}
    (h0 : dotProduct x (laplacian W *ᵥ x) = 0) : ∀ a b, 0 < W a b → x a = x b := by
  rw [dotProduct_laplacian_mulVec hW] at h0
  have hsum : ∑ i, ∑ j, W i j * (x i - x j) ^ 2 = 0 := by linarith
  have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∑ j, W i j * (x i - x j) ^ 2 :=
    fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hpos i j) (sq_nonneg _)
  intro a b hab
  have ha := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
  have hb := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hpos a j) (sq_nonneg (x a - x j)))).mp ha b (Finset.mem_univ b)
  have : (x a - x b) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact absurd h hab.ne'
    · exact h
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- Null directions of a nonnegative Laplacian form, weights of any sign: if
`x ↦ ∑ᵢⱼ Wᵢⱼ (xᵢ − xⱼ)²` (`W` symmetric) is nonnegative and vanishes at `g`, every node balance
`(L g)ᵢ = ∑ⱼ Wᵢⱼ (gᵢ − gⱼ)` vanishes (Mathlib `PosSemidef.dotProduct_mulVec_zero_iff`). -/
@[tmio T, powerlib_foundation] theorem node_balance_eq_zero_of_form_eq_zero {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (hQ : ∀ x : ι → ℝ, 0 ≤ ∑ i, ∑ j, W i j * (x i - x j) ^ 2)
    {g : ι → ℝ} (hg : ∑ i, ∑ j, W i j * (g i - g j) ^ 2 = 0) (i : ι) :
    ∑ j, W i j * (g i - g j) = 0 := by
  have hL : (laplacian W).PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, laplacian_transpose hW]
    · rw [star_trivial, dotProduct_laplacian_mulVec hW]
      exact div_nonneg (hQ x) zero_le_two
  have h := hL.dotProduct_mulVec_zero_iff.1
    (by rw [star_trivial, dotProduct_laplacian_mulVec hW, hg, zero_div])
  rw [← laplacian_mulVec_apply, h, Pi.zero_apply]

/-- Kernel of a connected symmetric Laplacian: `L x = 0` forces `x` constant. -/
@[tmio T, powerlib_foundation] theorem eq_of_laplacian_mulVec_eq_zero {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hconn : ∀ i j, Reach W i j)
    {x : ι → ℝ} (hx : laplacian W *ᵥ x = 0) (i j : ι) : x i = x j := by
  have h0 : dotProduct x (laplacian W *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
  exact eq_of_reach (edge_eq_of_form_zero hW hpos h0) (hconn i j)


/-! ## Grounded Laplacians -/

/-- Grounded Laplacian `L + diag g`. -/
def grounded (W : Matrix ι ι ℝ) (g : ι → ℝ) : Matrix ι ι ℝ := laplacian W + diagonal g

/-- Every node reaches, through positive-weight edges, a node with positive grounding. -/
def GroundReachable (W : Matrix ι ι ℝ) (g : ι → ℝ) : Prop := ∀ i, ∃ k, Reach W i k ∧ 0 < g k

@[tmio T, powerlib_foundation] theorem grounded_mulVec_apply (W : Matrix ι ι ℝ) (g : ι → ℝ)
    (x : ι → ℝ) (i : ι) :
    (grounded W g *ᵥ x) i = g i * x i + ∑ j, W i j * (x i - x j) := by
  simp [grounded, add_mulVec, laplacian_mulVec_apply, mulVec_diagonal, add_comm]

/-- Discrete minimum principle for grounded Laplacians. -/
@[tmio T, powerlib_foundation] theorem nonneg_of_grounded_mulVec_nonneg {W : Matrix ι ι ℝ}
    {g : ι → ℝ} (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i)
    (hreach : GroundReachable W g) {x : ι → ℝ} (hx : ∀ i, 0 ≤ (grounded W g *ᵥ x) i) :
    ∀ i, 0 ≤ x i := by
  by_contra hneg
  push Not at hneg
  obtain ⟨i₀, hi₀⟩ := hneg
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨m, hm⟩ := Finite.exists_min x
  have hmneg : x m < 0 := (hm i₀).trans_lt hi₀
  -- the minimum set is closed under positive edges and contains no grounded node
  have hclosed : ∀ a, x a = x m → (g a = 0 ∧ ∀ b, 0 < W a b → x b = x m) := by
    intro a ha
    have hb := hx a
    rw [grounded_mulVec_apply] at hb
    have hterm : ∀ j ∈ (Finset.univ : Finset ι), W a j * (x a - x j) ≤ 0 := by
      intro j _
      apply mul_nonpos_of_nonneg_of_nonpos (hpos a j)
      rw [ha]; linarith [hm j]
    have hgx : g a * x a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hg a) (by rw [ha]; exact hmneg.le)
    have hs : ∑ j, W a j * (x a - x j) ≤ 0 := Finset.sum_nonpos hterm
    have hgx0 : g a * x a = 0 := by linarith
    have hs0 : ∑ j, W a j * (x a - x j) = 0 := by linarith
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp hgx0 with h | h
      · exact h
      · exact absurd (ha ▸ h) hmneg.ne
    · intro b hab
      have hz := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hs0 b (Finset.mem_univ b)
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hab.ne'
      · linarith
  have key : ∀ b, Reach W m b → x b = x m := fun b hb => by
    induction hb with
    | refl => rfl
    | tail _ hbc ih => exact (hclosed _ ih).2 _ hbc
  obtain ⟨k, hk, hgk⟩ := hreach m
  exact absurd (hclosed k (key k hk)).1 hgk.ne'

@[tmio T, powerlib_foundation] theorem grounded_mulVec_injective {W : Matrix ι ι ℝ}
    {g : ι → ℝ} (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i)
    (hreach : GroundReachable W g) : Function.Injective (grounded W g *ᵥ ·) := by
  intro x y hxy
  have hz : grounded W g *ᵥ (x - y) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hxy
  have h1 := nonneg_of_grounded_mulVec_nonneg hpos hg hreach (x := x - y)
    (fun i => by rw [hz]; rfl)
  have h2 := nonneg_of_grounded_mulVec_nonneg hpos hg hreach (x := y - x)
    (fun i => by rw [← neg_sub, mulVec_neg, hz, neg_zero]; rfl)
  funext i
  have := h1 i; have := h2 i
  simp only [Pi.sub_apply] at *
  linarith

/-- A grounded Laplacian whose every node reaches ground is invertible. -/
@[tmio T, powerlib_foundation] theorem grounded_isUnit {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g) :
    IsUnit (grounded W g) :=
  mulVec_injective_iff_isUnit.mp (grounded_mulVec_injective hpos hg hreach)

@[tmio T, powerlib_foundation] theorem grounded_det_ne_zero {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g) :
    (grounded W g).det ≠ 0 :=
  ((isUnit_iff_isUnit_det _).mp (grounded_isUnit hpos hg hreach)).ne_zero

/-- Inverse nonnegativity: the solution of `(L + diag g) x = b` with `b ≥ 0` is `≥ 0`. -/
@[tmio T, powerlib_foundation] theorem grounded_inv_mulVec_nonneg {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g)
    {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) : ∀ i, 0 ≤ ((grounded W g)⁻¹ *ᵥ b) i := by
  apply nonneg_of_grounded_mulVec_nonneg hpos hg hreach
  intro i
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp
    (grounded_isUnit hpos hg hreach)), one_mulVec]
  exact hb i

/-- The inverse of a ground-reachable grounded Laplacian is entrywise nonnegative. -/
@[tmio T, powerlib_foundation] theorem grounded_inv_nonneg {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g)
    (i j : ι) : 0 ≤ (grounded W g)⁻¹ i j := by
  have h := grounded_inv_mulVec_nonneg hpos hg hreach (b := Pi.single j 1)
    (fun k => by by_cases hk : k = j <;> simp [hk]) i
  simpa [mulVec_single] using h

open scoped Classical in
/-- If node `i` has no positive-weight path to a grounded node, the indicator of its
component lies in the kernel of the grounded Laplacian. -/
@[tmio T, powerlib_foundation] theorem grounded_mulVec_component_eq_zero {W : Matrix ι ι ℝ}
    {g : ι → ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) {i : ι}
    (hnot : ∀ k, Reach W i k → g k ≤ 0) :
    grounded W g *ᵥ (fun a => if Reach W i a then (1 : ℝ) else 0) = 0 := by
  classical
  funext a
  rw [grounded_mulVec_apply, Pi.zero_apply]
  have hgx : g a * (if Reach W i a then (1 : ℝ) else 0) = 0 := by
    by_cases ha : Reach W i a
    · simp [ha, le_antisymm (hnot a ha) (hg a)]
    · simp [ha]
  rw [hgx, zero_add]
  apply Finset.sum_eq_zero
  intro b _
  rcases (hpos a b).lt_or_eq with hab | hab
  · by_cases ha : Reach W i a
    · have hb : Reach W i b := ha.tail hab
      simp [ha, hb]
    · have hb : ¬ Reach W i b := fun hb => ha (hb.tail (by rw [hW]; exact hab))
      simp [ha, hb]
  · rw [← hab, zero_mul]

open scoped Classical in
/-- For symmetric nonnegative weights and nonnegative grounding, the grounded Laplacian
is nonsingular exactly when every node reaches a grounded node. -/
@[tmio T, powerlib_foundation] theorem grounded_det_ne_zero_iff {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) :
    (grounded W g).det ≠ 0 ↔ GroundReachable W g := by
  constructor
  · intro hdet i
    by_contra hnot
    push Not at hnot
    apply hdet
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun a => if Reach W i a then 1 else 0, ?_,
      grounded_mulVec_component_eq_zero hW hpos hg hnot⟩
    intro h
    have := congrFun h i
    simp only [Pi.zero_apply] at this
    rw [ite_eq_left (show Reach W i i from Relation.ReflTransGen.refl)] at this
    exact one_ne_zero this
  · exact grounded_det_ne_zero hpos hg

/-- For symmetric weights, `L + diag g` is positive definite iff every node has a
positive-weight path to a grounded node. -/
@[tmio T, powerlib_foundation] theorem grounded_posDef_iff {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) :
    (grounded W g).PosDef ↔ GroundReachable W g := by
  have hherm : (grounded W g).IsHermitian := by
    unfold IsHermitian
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [grounded, laplacian, h, Ne.symm h, hW i j]
  have hform : ∀ x : ι → ℝ, dotProduct x (grounded W g *ᵥ x) =
      dotProduct x (laplacian W *ᵥ x) + ∑ i, g i * x i ^ 2 := by
    intro x
    rw [grounded, add_mulVec, dotProduct_add]
    congr 1
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor
  · intro hPD
    exact (grounded_det_ne_zero_iff hW hpos hg).mp hPD.det_pos.ne'
  · intro hreach
    refine posDef_iff_dotProduct_mulVec.mpr ⟨hherm, fun x hx => ?_⟩
    simp only [star_trivial]
    rw [hform]
    have hL := laplacian_posSemidef_form hW hpos x
    have hG : 0 ≤ ∑ i, g i * x i ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (sq_nonneg _)
    rcases (add_nonneg hL hG).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hx
      have hL0 : dotProduct x (laplacian W *ᵥ x) = 0 := by linarith
      have hG0 : ∑ i, g i * x i ^ 2 = 0 := by linarith
      have hedge := edge_eq_of_form_zero hW hpos hL0
      have hgx := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hg i) (sq_nonneg (x i)))).mp hG0
      funext i
      obtain ⟨k, hk, hgk⟩ := hreach i
      have hxk : x k = 0 := by
        have := hgx k (Finset.mem_univ k)
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hgk.ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      rw [eq_of_reach hedge hk, hxk]
      rfl

/-! ## Bus admittance matrices without shunt branches are singular -/

section Ybus

/-- Bus admittance matrix built from branch admittances `y i j` with no shunt (ground)
elements: `Y_ii = Σ_{j ≠ i} y_ij`, `Y_ij = -y_ij`. (The diagonal of `y` cancels.) -/
abbrev ybusNoShunt {ι : Type*} [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  laplacian y

/-- Laplacian-type admittance matrices are singular, whatever the topology. -/
@[tmio T, powerlib_foundation] theorem ybusNoShunt_det_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (y : Matrix ι ι ℂ) : (ybusNoShunt y).det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  exact ⟨fun _ => 1, fun h => one_ne_zero (congrFun h (Classical.arbitrary ι)),
    laplacian_mulVec_const y 1⟩

/-- Counterexample to "connected ⇒ nonsingular": two buses joined by one line. -/
@[tmio T, powerlib_foundation] theorem ybus_two_bus_singular :
    ybusNoShunt (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = !![1, -1; -1, 1] ∧
      (ybusNoShunt (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  refine ⟨?_, ybusNoShunt_det_eq_zero _⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ybusNoShunt, laplacian_apply, Fin.sum_univ_two]

end Ybus

/-! ## Signed incidence matrix -/

section Incidence

variable {β ν : Type*} [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]

/-- Signed node–branch incidence matrix: `+1` if branch `k` leaves node `i` (tail),
`−1` if it enters node `i` (head). -/
def signedIncidence (tail head : β → ν) : Matrix ν β ℝ :=
  Matrix.of fun i k => (if i = tail k then 1 else 0) - (if i = head k then 1 else 0)

omit [Fintype β] [DecidableEq β] in
/-- KVL: the branch voltage `(𝓑ᵀ v)_k` is the potential difference `v(tail k) − v(head k)`. -/
@[tmio T, powerlib_foundation] theorem signedIncidence_transpose_mulVec (tail head : β → ν)
    (v : ν → ℝ) (k : β) :
    ((signedIncidence tail head)ᵀ *ᵥ v) k = v (tail k) - v (head k) := by
  simp [signedIncidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

omit [Fintype ν] [DecidableEq β] in
/-- KCL: `(𝓑 i)_j` is the total current leaving node `j` through the branches. -/
@[tmio T, powerlib_foundation] theorem signedIncidence_mulVec (tail head : β → ν) (c : β → ℝ)
    (j : ν) :
    (signedIncidence tail head *ᵥ c) j =
      (∑ k with tail k = j, c k) - ∑ k with head k = j, c k := by
  simp [signedIncidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul,
    Finset.sum_filter, eq_comm]

end Incidence

section IncidenceSum

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]

omit [Fintype β] in
@[tmio T, powerlib_foundation] theorem signedIncidence_col_sum (tail head : β → α) (ℓ : β) :
    ∑ a, Network.signedIncidence tail head a ℓ = 0 := by
  have h := Network.signedIncidence_transpose_mulVec tail head (fun _ => (1 : ℝ)) ℓ
  simpa [mulVec, dotProduct] using h

end IncidenceSum

/-! ## Kron reduction -/

section Kron

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
/-- Kron reduction: if the internal nodes inject no current (`Y_ii v_i + Y_ib v_b = 0`) and
`Y_ii` is invertible, the boundary injections are `(Y_bb − Y_bi Y_ii⁻¹ Y_ib) v_b`. -/
@[tmio T, powerlib_foundation] theorem kron_current {Yii : Matrix ι ι ℝ} {Yib : Matrix ι β ℝ}
    {Ybi : Matrix β ι ℝ} {Ybb : Matrix β β ℝ} (hinv : IsUnit Yii.det) {vi : ι → ℝ}
    {vb : β → ℝ} (hint : Yii *ᵥ vi + Yib *ᵥ vb = 0) :
    Ybi *ᵥ vi + Ybb *ᵥ vb = (Ybb - Ybi * Yii⁻¹ * Yib) *ᵥ vb := by
  have hvi : vi = -((Yii⁻¹ * Yib) *ᵥ vb) := by
    have h1 : Yii *ᵥ vi = -(Yib *ᵥ vb) := eq_neg_of_add_eq_zero_left hint
    have h2 := congrArg (fun z => Yii⁻¹ *ᵥ z) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec, mulVec_neg] at h2
    exact h2
  rw [hvi, sub_mulVec, mulVec_neg, mulVec_mulVec, Matrix.mul_assoc]
  abel

omit [DecidableEq ι] [DecidableEq β] in
/-- Kron reduction conserves port power: with zero internal injection, the network power
`vᵀ Y v` equals the boundary port power `v_bᵀ i_b`. -/
@[tmio T, powerlib_foundation] theorem kron_power (Yii : Matrix ι ι ℝ) (Yib : Matrix ι β ℝ)
    (Ybi : Matrix β ι ℝ) (Ybb : Matrix β β ℝ) {vi : ι → ℝ} {vb : β → ℝ}
    (hint : Yii *ᵥ vi + Yib *ᵥ vb = 0) :
    Sum.elim vi vb ⬝ᵥ (fromBlocks Yii Yib Ybi Ybb *ᵥ Sum.elim vi vb) =
      vb ⬝ᵥ (Ybi *ᵥ vi + Ybb *ᵥ vb) := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, hint, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]

omit [DecidableEq β] in
/-- Kron reduction of a positive semidefinite network with positive definite internal block is
positive semidefinite (passivity is preserved). Wrapper of Mathlib
`Matrix.PosDef.fromBlocks₁₁` (Schur complement). -/
@[tmio T, powerlib_foundation] theorem kron_posSemidef {Yii : Matrix ι ι ℝ} {Yib : Matrix ι β ℝ}
    {Ybb : Matrix β β ℝ} (hY : (fromBlocks Yii Yib Yibᵀ Ybb).PosSemidef) (hii : Yii.PosDef) :
    (Ybb - Yibᵀ * Yii⁻¹ * Yib).PosSemidef := by
  have := hii.isUnit.invertible
  have h := (PosDef.fromBlocks₁₁ Yib Ybb hii).mp
  simp only [conjTranspose_eq_transpose_of_trivial] at h
  exact h hY

end Kron

end powerlib.Network
