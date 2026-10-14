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
  power-flow map and its Laplacian Jacobian are in `theorem/Network/PowerFlow.lean`).

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
  definite exactly when every node has such a path to ground (`grounded_posDef_iff`).
* On `Fin (n + 1)` the complex row identity `∑ₗ Lₖₗ ζₗ = ∑ₗ Wₖₗ (ζₖ − ζₗ)`
  (`complex_laplacian_sum`) and, for symmetric weights, `∑ₖ ∑ₗ Wₖₗ (ζₖ − ζₗ) = 0`
  (`complex_laplacian_total`) are the eigenvector manipulations of the networked swing Jacobian.
* A bus admittance matrix built from branch admittances with no shunt (ground) branch
  (`ybusNoShunt`) is Laplacian-type, `Y 𝟏 = 0`, hence singular for every topology
  (`ybusNoShunt_det_eq_zero`; two-bus counterexample `ybus_two_bus_singular`, the correction of
  `theory/T-dae-systems.md` §2.1).
* The signed node–branch incidence matrix `signedIncidence tail head` of a directed multigraph
  (`+1` at the tail, `−1` at the head) satisfies KVL, `(𝓑ᵀ v)_k = v(tail k) − v(head k)`
  (`signedIncidence_transpose_mulVec`), and every column sums to zero
  (`signedIncidence_col_sum`). The RL-network pH models built on it are in
  `theorem/PH/Models/RLNetwork.lean`, the multi-area tie-line graph in
  `theorem/Frequency/LFCNetwork.lean`.
* Kron reduction: eliminating internal nodes with zero injection from a linear resistive network
  `Y` gives `i_b = (Y_bb − Y_bi Y_ii⁻¹ Y_ib) v_b` (`kron_current`), conserves the port power
  (`kron_power`), and (Mathlib Schur complement) keeps a PSD network PSD (`kron_posSemidef`).
-/

noncomputable section
namespace powerlib.Network
open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted Laplacian `diag(∑ⱼ Wᵢⱼ) - W`. -/
def laplacian (W : Matrix ι ι ℝ) : Matrix ι ι ℝ := diagonal (fun i => ∑ j, W i j) - W

/-- Reachability through edges of positive weight. -/
def Reach (W : Matrix ι ι ℝ) : ι → ι → Prop := Relation.ReflTransGen fun a b => 0 < W a b

@[powerlib_foundation] theorem laplacian_mulVec_apply (W : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    (laplacian W *ᵥ x) i = ∑ j, W i j * (x i - x j) := by
  rw [laplacian, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
  simp only [mulVec, dotProduct, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

@[powerlib_foundation] theorem laplacian_apply (W : Matrix ι ι ℝ) (i j : ι) :
    laplacian W i j = (if i = j then ∑ k, W i k else 0) - W i j := by
  simp [laplacian, diagonal_apply]

@[powerlib_foundation] theorem laplacian_mulVec_const (W : Matrix ι ι ℝ) (c : ℝ) :
    laplacian W *ᵥ (fun _ => c) = 0 := by
  ext i
  simp [laplacian_mulVec_apply]

@[powerlib_foundation] theorem laplacian_transpose {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) : (laplacian W)ᵀ = laplacian W := by
  ext i j
  by_cases h : i = j
  · subst h; rfl
  · simp [laplacian, diagonal_apply, h, Ne.symm h, hW i j]

/-- Column sums of a symmetric Laplacian vanish: `𝟙ᵀ L x = 0`. -/
@[powerlib_foundation] theorem sum_laplacian_mulVec {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (x : ι → ℝ) : ∑ i, (laplacian W *ᵥ x) i = 0 := by
  simp only [laplacian_mulVec_apply, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hW]

/-- Propagation of an edge relation along positive-weight paths. -/
@[powerlib_foundation] theorem eq_of_reach {α : Type*} {W : Matrix ι ι ℝ} {x : ι → α}
    (hx : ∀ a b, 0 < W a b → x a = x b) {i k : ι} (h : Reach W i k) : x i = x k := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hx _ _ hbc)

/-- Quadratic form of a symmetric weighted Laplacian. -/
@[powerlib_foundation] theorem dotProduct_laplacian_mulVec {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (x : ι → ℝ) :
    dotProduct x (laplacian W *ᵥ x) = (∑ i, ∑ j, W i j * (x i - x j) ^ 2) / 2 := by
  have h1 : dotProduct x (laplacian W *ᵥ x) = ∑ i, ∑ j, W i j * (x i * (x i - x j)) := by
    simp only [dotProduct, laplacian_mulVec_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, W i j * (x i * (x i - x j)) = ∑ i, ∑ j, W i j * (x j * (x j - x i)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hW]
  have h3 : ∑ i, ∑ j, W i j * (x i - x j) ^ 2 =
      ∑ i, ∑ j, W i j * (x i * (x i - x j)) + ∑ i, ∑ j, W i j * (x j * (x j - x i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3, ← h2, h1]
  ring

/-- Complex Hermitian form of a symmetric real Laplacian: `uᴴ L u = ½ ∑ Wᵢⱼ |uᵢ - uⱼ|²`. -/
@[powerlib_foundation] theorem star_dotProduct_laplacian_mulVec {W : Matrix ι ι ℝ}
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

@[powerlib_foundation] theorem laplacian_posSemidef_form {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (x : ι → ℝ) :
    0 ≤ dotProduct x (laplacian W *ᵥ x) := by
  rw [dotProduct_laplacian_mulVec hW]
  apply div_nonneg _ zero_le_two
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hpos i j) (sq_nonneg _)

/-- A zero Laplacian quadratic form forces equality across every positive edge. -/
@[powerlib_foundation] theorem edge_eq_of_form_zero {W : Matrix ι ι ℝ}
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

/-- Kernel of a connected symmetric Laplacian: `L x = 0` forces `x` constant. -/
@[powerlib_foundation] theorem eq_of_laplacian_mulVec_eq_zero {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hconn : ∀ i j, Reach W i j)
    {x : ι → ℝ} (hx : laplacian W *ᵥ x = 0) (i j : ι) : x i = x j := by
  have h0 : dotProduct x (laplacian W *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
  exact eq_of_reach (edge_eq_of_form_zero hW hpos h0) (hconn i j)

/-- Complex kernel of a connected symmetric Laplacian. -/
@[powerlib_foundation] theorem complex_eq_of_laplacian_eq_zero {W : Matrix ι ι ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hconn : ∀ i j, Reach W i j)
    {u : ι → ℂ} (hu : ∀ i, ∑ j, (W i j : ℂ) * (u i - u j) = 0) (i j : ι) : u i = u j := by
  have hform := star_dotProduct_laplacian_mulVec hW u
  simp only [hu, mul_zero, Finset.sum_const_zero] at hform
  have hsum : ∑ i, ∑ j, W i j * Complex.normSq (u i - u j) = 0 := by
    have := congrArg Complex.re hform
    simp only [Complex.zero_re, Complex.ofReal_re] at this
    linarith
  have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∑ j, W i j * Complex.normSq (u i - u j) :=
    fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hpos i j) (Complex.normSq_nonneg _)
  have hedge : ∀ a b, 0 < W a b → u a = u b := by
    intro a b hab
    have ha := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hpos a j) (Complex.normSq_nonneg (u a - u j)))).mp ha b
      (Finset.mem_univ b)
    rcases mul_eq_zero.mp hb with h | h
    · exact absurd h hab.ne'
    · exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp h)
  exact eq_of_reach hedge (hconn i j)

section ComplexLaplacian

variable {n : ℕ}

@[powerlib_foundation] theorem complex_laplacian_sum (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ζ : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    ∑ l, ((laplacian W k l : ℝ) : ℂ) * ζ l = ∑ l, (W k l : ℂ) * (ζ k - ζ l) := by
  simp only [laplacian_apply, Complex.ofReal_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

@[powerlib_foundation] theorem complex_laplacian_total {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hW : ∀ i j, W i j = W j i) (ζ : Fin (n + 1) → ℂ) :
    ∑ k, ∑ l, (W k l : ℂ) * (ζ k - ζ l) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hW]

end ComplexLaplacian

/-! ## Grounded Laplacians -/

/-- Grounded Laplacian `L + diag g`. -/
def grounded (W : Matrix ι ι ℝ) (g : ι → ℝ) : Matrix ι ι ℝ := laplacian W + diagonal g

/-- Every node reaches, through positive-weight edges, a node with positive grounding. -/
def GroundReachable (W : Matrix ι ι ℝ) (g : ι → ℝ) : Prop := ∀ i, ∃ k, Reach W i k ∧ 0 < g k

@[powerlib_foundation] theorem grounded_mulVec_apply (W : Matrix ι ι ℝ) (g : ι → ℝ)
    (x : ι → ℝ) (i : ι) :
    (grounded W g *ᵥ x) i = g i * x i + ∑ j, W i j * (x i - x j) := by
  simp [grounded, add_mulVec, laplacian_mulVec_apply, mulVec_diagonal, add_comm]

/-- Discrete minimum principle for grounded Laplacians. -/
@[powerlib_foundation] theorem nonneg_of_grounded_mulVec_nonneg {W : Matrix ι ι ℝ}
    {g : ι → ℝ} (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i)
    (hreach : GroundReachable W g) {x : ι → ℝ} (hx : ∀ i, 0 ≤ (grounded W g *ᵥ x) i) :
    ∀ i, 0 ≤ x i := by
  by_contra hneg
  push Not at hneg
  obtain ⟨i₀, hi₀⟩ := hneg
  haveI : Nonempty ι := ⟨i₀⟩
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

@[powerlib_foundation] theorem grounded_mulVec_injective {W : Matrix ι ι ℝ}
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
@[powerlib_foundation] theorem grounded_isUnit {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g) :
    IsUnit (grounded W g) :=
  mulVec_injective_iff_isUnit.mp (grounded_mulVec_injective hpos hg hreach)

@[powerlib_foundation] theorem grounded_det_ne_zero {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g) :
    (grounded W g).det ≠ 0 :=
  ((isUnit_iff_isUnit_det _).mp (grounded_isUnit hpos hg hreach)).ne_zero

/-- Inverse nonnegativity: the solution of `(L + diag g) x = b` with `b ≥ 0` is `≥ 0`. -/
@[powerlib_foundation] theorem grounded_inv_mulVec_nonneg {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g)
    {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) : ∀ i, 0 ≤ ((grounded W g)⁻¹ *ᵥ b) i := by
  apply nonneg_of_grounded_mulVec_nonneg hpos hg hreach
  intro i
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp
    (grounded_isUnit hpos hg hreach)), one_mulVec]
  exact hb i

/-- The inverse of a ground-reachable grounded Laplacian is entrywise nonnegative. -/
@[powerlib_foundation] theorem grounded_inv_nonneg {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) (hreach : GroundReachable W g)
    (i j : ι) : 0 ≤ (grounded W g)⁻¹ i j := by
  have h := grounded_inv_mulVec_nonneg hpos hg hreach (b := Pi.single j 1)
    (fun k => by by_cases hk : k = j <;> simp [hk]) i
  simpa [mulVec_single] using h

/-- For symmetric weights, `L + diag g` is positive definite iff every node has a
positive-weight path to a grounded node. -/
@[powerlib_foundation] theorem grounded_posDef_iff {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) :
    (grounded W g).PosDef ↔ GroundReachable W g := by
  have hherm : (grounded W g).IsHermitian := by
    unfold IsHermitian
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [grounded, laplacian, diagonal_apply, h, Ne.symm h, hW i j]
  have hform : ∀ x : ι → ℝ, dotProduct x (grounded W g *ᵥ x) =
      dotProduct x (laplacian W *ᵥ x) + ∑ i, g i * x i ^ 2 := by
    intro x
    rw [grounded, add_mulVec, dotProduct_add]
    congr 1
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor
  · intro hPD i
    by_contra hnot
    push Not at hnot
    classical
    -- indicator of the component of `i`
    let x : ι → ℝ := fun a => if Reach W i a then 1 else 0
    have hx0 : x ≠ 0 := by
      intro h
      have := congrFun h i
      simp only [x, Pi.zero_apply] at this
      rw [if_pos (show Reach W i i from Relation.ReflTransGen.refl)] at this
      exact one_ne_zero this
    have hgx : ∀ a, g a * x a ^ 2 = 0 := by
      intro a
      by_cases ha : Reach W i a
      · have : g a ≤ 0 := hnot a ha
        have : g a = 0 := le_antisymm this (hg a)
        simp [this]
      · simp [x, ha]
    have hedge : ∀ a b, 0 < W a b → x a = x b := by
      intro a b hab
      by_cases ha : Reach W i a
      · have hb : Reach W i b := ha.tail hab
        simp [x, ha, hb]
      · have hb : ¬ Reach W i b := fun hb => ha (hb.tail (by rw [hW]; exact hab))
        simp [x, ha, hb]
    have hL : dotProduct x (laplacian W *ᵥ x) = 0 := by
      rw [dotProduct_laplacian_mulVec hW]
      have : ∀ a b, W a b * (x a - x b) ^ 2 = 0 := by
        intro a b
        rcases (hpos a b).lt_or_eq with h | h
        · rw [hedge a b h]; ring
        · rw [← h]; ring
      simp [this]
    have hpd := (posDef_iff_dotProduct_mulVec.mp hPD).2 hx0
    simp only [star_trivial] at hpd
    rw [hform, hL, Finset.sum_eq_zero fun a _ => hgx a] at hpd
    simp at hpd
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
def ybusNoShunt {ι : Type*} [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ∑ j, y i j) - y

@[powerlib_foundation] theorem ybusNoShunt_mulVec_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : Matrix ι ι ℂ) : ybusNoShunt y *ᵥ (fun _ => 1) = 0 := by
  ext i
  rw [ybusNoShunt, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
  simp [mulVec, dotProduct]

/-- Laplacian-type admittance matrices are singular, whatever the topology. -/
@[powerlib_foundation] theorem ybusNoShunt_det_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (y : Matrix ι ι ℂ) : (ybusNoShunt y).det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  exact ⟨fun _ => 1, fun h => one_ne_zero (congrFun h (Classical.arbitrary ι)),
    ybusNoShunt_mulVec_one y⟩

/-- Counterexample to "connected ⇒ nonsingular": two buses joined by one line. -/
@[powerlib_foundation] theorem ybus_two_bus_singular :
    ybusNoShunt (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = !![1, -1; -1, 1] ∧
      (ybusNoShunt (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  refine ⟨?_, ybusNoShunt_det_eq_zero _⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ybusNoShunt, Fin.sum_univ_two]

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
@[powerlib_foundation] theorem signedIncidence_transpose_mulVec (tail head : β → ν)
    (v : ν → ℝ) (k : β) :
    ((signedIncidence tail head)ᵀ *ᵥ v) k = v (tail k) - v (head k) := by
  simp [signedIncidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

end Incidence

section IncidenceSum

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]

omit [Fintype β] in
@[powerlib_foundation] theorem signedIncidence_col_sum (tail head : β → α) (ℓ : β) :
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
@[powerlib_foundation] theorem kron_current {Yii : Matrix ι ι ℝ} {Yib : Matrix ι β ℝ}
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
@[powerlib_foundation] theorem kron_power (Yii : Matrix ι ι ℝ) (Yib : Matrix ι β ℝ)
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
@[powerlib_foundation] theorem kron_posSemidef {Yii : Matrix ι ι ℝ} {Yib : Matrix ι β ℝ}
    {Ybb : Matrix β β ℝ} (hY : (fromBlocks Yii Yib Yibᵀ Ybb).PosSemidef) (hii : Yii.PosDef) :
    (Ybb - Yibᵀ * Yii⁻¹ * Yib).PosSemidef := by
  have := hii.isUnit.invertible
  have h := (PosDef.fromBlocks₁₁ Yib Ybb hii).mp
  simp only [conjTranspose_eq_transpose_of_trivial] at h
  exact h hY

end Kron

end powerlib.Network
