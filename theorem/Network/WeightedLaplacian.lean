import dependencies.Mathlib
import theorem.Attributes

/-! # Weighted graph Laplacians and grounded Laplacians

Foundation layer for network models. A network is a finite node set `ι` with an
edge-weight matrix `W` (`W i j ≥ 0`, symmetric where stated); the diagonal of `W`
is irrelevant. The Laplacian is `L = diag(∑ⱼ Wᵢⱼ) - W`, so
`(L x)ᵢ = ∑ⱼ Wᵢⱼ (xᵢ - xⱼ)`. A grounding vector `g ≥ 0` (shunt conductance or,
for the frequency divider, the coupling to machine buses) gives the grounded
Laplacian `L + diag g`.

Sources: work-sync `theory/T-synchronization-manifold.md` §1.1 (weighted
Laplacian, `L𝟙 = 0`, positive semidefinite), `theory/T-local-frequency.md` §1.4 and
§2.7 (nonsingularity of `B_bb`), `theory/T-telegrapher-bergeron.md` §1.4.1 (EMTP
nodal matrix). The key fact proved here, absent from Mathlib, is the discrete
minimum principle: if every node reaches a grounded node through positive-weight
edges then `(L + diag g) x ≥ 0` forces `x ≥ 0`. Consequences: `L + diag g` is
invertible, its inverse is entrywise nonnegative (the M-matrix special case), and,
for symmetric weights, it is positive definite exactly when every node has such a
path to ground.

A bus admittance matrix built from branch admittances with no shunt (ground) branch
(`ybusNoShunt`) is Laplacian-type, `Y 𝟏 = 0`, hence singular for every topology
(`ybusNoShunt_det_eq_zero`; two-bus counterexample `ybus_two_bus_singular`, the correction of
`theory/T-dae-systems.md` §2.1).

Connectivity is the reflexive-transitive closure of the relation `0 < W i j`.
These are algebraic statements; no power-flow or dynamic claim is made here.
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

/-! ## Linearized power flow -/

/-- Lossless active-power injections `Pᵢ(θ) = ∑ⱼ bᵢⱼ sin(θᵢ - θⱼ)` (voltage magnitudes,
held constant, are absorbed into `bᵢⱼ = VᵢVⱼ/Xᵢⱼ`). -/
def powerInjection (b : Matrix ι ι ℝ) (θ : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, b i j * Real.sin (θ i - θ j)

/-- Linearization weights `bᵢⱼ cos(θᵢ⁰ - θⱼ⁰)`. -/
def flowWeights (b : Matrix ι ι ℝ) (θ : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => b i j * Real.cos (θ i - θ j)

/-- The Jacobian of the lossless power-flow map is the weighted Laplacian of
`bᵢⱼ cos(θᵢ - θⱼ)`. -/
@[powerlib_foundation] theorem hasFDerivAt_powerInjection (b : Matrix ι ι ℝ) (θ : ι → ℝ) :
    HasFDerivAt (powerInjection b)
      (Matrix.toLin' (laplacian (flowWeights b θ))).toContinuousLinearMap θ := by
  rw [hasFDerivAt_pi']
  intro i
  have hterm : ∀ j ∈ (Finset.univ : Finset ι), HasFDerivAt
      (fun φ : ι → ℝ => b i j * Real.sin (φ i - φ j))
      ((b i j * Real.cos (θ i - θ j)) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)) θ := by
    intro j _
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) i θ).sub
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) j θ)).sin.const_mul (b i j)
    convert hd using 1
    ext v
    simp [smul_eq_mul]
    ring
  convert HasFDerivAt.fun_sum hterm using 1
  · rfl
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, laplacian_mulVec_apply,
      flowWeights, of_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_sub', Pi.sub_apply,
      smul_eq_mul]

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

end powerlib.Network
