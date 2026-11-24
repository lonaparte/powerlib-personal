import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.LocallyConvex.Separation

/-! # Lagrangian strong duality for convex programs with a Slater point (foundation)

A convex program: maximize a concave function `f` over the points of a convex set `K` that satisfy
finitely many convex constraints `g j x ≤ 0` (`j : ι`, `ι` finite). Its Lagrangian with
multipliers `μ j` is `f x − ∑ j μ j g j x`. Weak duality: for `μ ≥ 0`, any bound `d` of the
Lagrangian on `K` bounds the program. Strong duality: if some `x₀ ∈ K` satisfies every constraint
strictly (Slater's condition), every bound `p` of the program is certified this way, by some
`μ ≥ 0` with `f x − ∑ j μ j g j x ≤ p` on all of `K`. With a greatest value `p` of the program
and a greatest value `D μ` of the Lagrangian on `K` for each `μ ≥ 0`, `p` is the least of the
`D μ`: the program and its dual have the same value, and both are attained.

The certificate is obtained by separating, in `(ι → ℝ) × ℝ`, the open convex set
`{(u, v) | u j < 0 for all j, v > p}` from the convex set
`{(u, v) | ∃ x ∈ K, g j x ≤ u j for all j, v ≤ f x}`. The separating functional has nonnegative
weights on the constraints and a nonpositive weight on the objective (the first set is unbounded
in those directions); Slater's point excludes a zero objective weight, and normalizing it gives
the multipliers.

Scope.
* Generic convex analysis in a real vector space `E` (no topology on `E`): a concave objective
  and finitely many convex constraints on a convex set; no model family and no engineering object.
  No compactness, continuity or finite dimension of `E` is assumed for the certificate; the
  `IsLeast` form assumes that the primal and the Lagrangian maxima are attained.

Source: Lagrangian duality of convex programs under Slater's condition (M. Slater, 1950; e.g.
S. Boyd and L. Vandenberghe, *Convex Optimization*, 2004, §5.3.2), proved with the separation
theorem `geometric_hahn_banach_open` of Mathlib (`Mathlib/Analysis/LocallyConvex/Separation.lean`).

Results.
* `le_of_forall_lagrangian_le` (weak duality: for `μ ≥ 0`, if `f x − ∑ j μ j g j x ≤ d` on `K`,
  every feasible `x ∈ K` has `f x ≤ d`).
* `exists_lagrangian_le` (strong duality, certificate form: with a Slater point, every upper
  bound `p` of `f` on the feasible points of `K` is a bound `f x − ∑ j μ j g j x ≤ p` on all of
  `K` for some `μ ≥ 0`).
* `isLeast_dual` (strong duality, value form: if `p` is the greatest value of `f` on the feasible
  points and `D μ` the greatest value of the Lagrangian on `K` for each `μ ≥ 0`, then `p` is the
  least value of `D` over `μ ≥ 0`).
-/

namespace powerlib.SpecialFunctions

/-- **Weak duality**: for multipliers `μ ≥ 0`, a bound `d` of the Lagrangian
`f x − ∑ j μ j g j x` on `K` bounds `f` at every feasible point `x ∈ K`, `g j x ≤ 0`. -/
@[tmio T, powerlib_foundation] theorem le_of_forall_lagrangian_le {E ι : Type*} [Fintype ι]
    {K : Set E} {f : E → ℝ} {g : ι → E → ℝ} {μ : ι → ℝ} {d : ℝ} {x : E}
    (hμ : ∀ j, 0 ≤ μ j) (hd : ∀ y ∈ K, f y - ∑ j, μ j * g j y ≤ d) (hx : x ∈ K)
    (hgx : ∀ j, g j x ≤ 0) : f x ≤ d := by
  have : ∑ j, μ j * g j x ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hgx j)
  linarith [hd x hx]

/-- `c + s d < u` for all `s ≥ 0` forces `d ≤ 0`. -/
@[tmio T, powerlib_foundation] private theorem nonpos_of_forall_lt {c d u : ℝ}
    (h : ∀ s : ℝ, 0 ≤ s → c + s * d < u) : d ≤ 0 := by
  by_contra hd
  push Not at hd
  have h0 := h 0 le_rfl
  have := h ((u - c) / d) (div_nonneg (by linarith) hd.le)
  rw [div_mul_cancel₀ _ hd.ne'] at this
  linarith

/-- `c + ε d < u` for all `ε > 0` forces `c ≤ u`. -/
@[tmio T, powerlib_foundation] private theorem le_of_forall_pos_lt {c d u : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → c + ε * d < u) : c ≤ u := by
  by_contra hcu
  push Not at hcu
  set ε := (c - u) / (2 * (|d| + 1))
  have hd1 : 0 < |d| + 1 := by positivity
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have h1 := h ε hε
  have h2 : -(ε * |d|) ≤ ε * d := by nlinarith [neg_abs_le d]
  have h3 : ε * |d| ≤ (c - u) / 2 := by
    rw [show ε * |d| = (c - u) / 2 * (|d| / (|d| + 1)) by
      simp only [ε]; field_simp]
    have : |d| / (|d| + 1) ≤ 1 := by rw [div_le_one hd1]; linarith
    nlinarith
  linarith

/-- A linear functional on `(ι → ℝ) × ℝ` is `φ (u, v) = ∑ j u j φ(e_j, 0) + v φ(0, 1)`. -/
@[tmio T, powerlib_foundation] private theorem linear_apply_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (φ : StrongDual ℝ ((ι → ℝ) × ℝ)) (z : (ι → ℝ) × ℝ) :
    φ z = ∑ j, z.1 j * φ (Pi.single j 1, 0) + z.2 * φ (0, 1) := by
  have hz : z = ∑ j, z.1 j • ((Pi.single j 1 : ι → ℝ), (0 : ℝ)) + z.2 • ((0 : ι → ℝ), (1 : ℝ)) := by
    ext i
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  conv_lhs => rw [hz]
  rw [map_add, map_sum, map_smul, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]

/-- **Strong duality with a Slater point**, certificate form: if `f` is concave and every `g j`
convex on the convex set `K`, some `x₀ ∈ K` has `g j x₀ < 0` for all `j`, and `p` bounds `f` on
the feasible points of `K`, then some multipliers `μ ≥ 0` give
`f x − ∑ j μ j g j x ≤ p` for every `x ∈ K`. -/
@[tmio T, powerlib_foundation] theorem exists_lagrangian_le {E ι : Type*} [AddCommGroup E]
    [Module ℝ E] [Fintype ι] {K : Set E} {f : E → ℝ} {g : ι → E → ℝ} {p : ℝ} {x₀ : E}
    (hf : ConcaveOn ℝ K f) (hg : ∀ j, ConvexOn ℝ K (g j)) (hx₀ : x₀ ∈ K)
    (hs : ∀ j, g j x₀ < 0) (hp : ∀ x ∈ K, (∀ j, g j x ≤ 0) → f x ≤ p) :
    ∃ μ : ι → ℝ, (∀ j, 0 ≤ μ j) ∧ ∀ x ∈ K, f x - ∑ j, μ j * g j x ≤ p := by
  classical
  set A : Set ((ι → ℝ) × ℝ) := {z | ∃ x ∈ K, (∀ j, g j x ≤ z.1 j) ∧ z.2 ≤ f x}
  set B : Set ((ι → ℝ) × ℝ) := {z | ∀ j, z.1 j < 0} ∩ {z | p < z.2}
  have hBc : Convex ℝ B := by
    refine Convex.inter ?_ ?_
    · rintro z hz z' hz' a b ha hb hab j
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := hz j
      have h2 := hz' j
      rcases eq_or_lt_of_le ha with rfl | ha'
      · rw [zero_add] at hab
        subst hab
        linarith
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos hb h2.le]
    · exact convex_halfSpace_gt (f := Prod.snd) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ p
  have hBo : IsOpen B := by
    refine IsOpen.inter ?_ (isOpen_lt continuous_const continuous_snd)
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_apply j).comp continuous_fst) continuous_const
  have hAc : Convex ℝ A := by
    rintro z ⟨x, hx, hgx, hfx⟩ z' ⟨x', hx', hgx', hfx'⟩ a b ha hb hab
    refine ⟨a • x + b • x', hf.1 hx hx' ha hb hab, fun j => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := (hg j).2 hx hx' ha hb hab
      simp only [smul_eq_mul] at this
      nlinarith [mul_le_mul_of_nonneg_left (hgx j) ha, mul_le_mul_of_nonneg_left (hgx' j) hb]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have := hf.2 hx hx' ha hb hab
      simp only [smul_eq_mul] at this
      nlinarith [mul_le_mul_of_nonneg_left hfx ha, mul_le_mul_of_nonneg_left hfx' hb]
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    rintro z ⟨hz1, hz2⟩ ⟨x, hx, hgx, hfx⟩
    have := hp x hx fun j => (hgx j).trans (hz1 j).le
    simp only [Set.mem_ofPred_eq] at hz2
    linarith
  obtain ⟨φ, u, hφB, hφA⟩ := geometric_hahn_banach_open hBc hBo hAc hdisj
  set lam : ι → ℝ := fun j => φ (Pi.single j 1, 0)
  set κ := φ (0, 1)
  have hrep : ∀ z, φ z = ∑ j, z.1 j * lam j + z.2 * κ := linear_apply_eq φ
  have hone : ∀ s : ℝ, 0 ≤ s → ((fun _ => -1 : ι → ℝ), p + 1 + s) ∈ B := fun s hs =>
    ⟨fun _ => by norm_num, by simp only [Set.mem_ofPred_eq]; linarith⟩
  -- the weight of the objective is nonpositive
  have hκ : κ ≤ 0 := by
    refine nonpos_of_forall_lt (c := φ ((fun _ => -1 : ι → ℝ), p + 1)) (u := u) fun s hs => ?_
    have := hφB _ (hone s hs)
    have e : ((fun _ => -1 : ι → ℝ), p + 1 + s) =
        ((fun _ => -1 : ι → ℝ), p + 1) + s • ((0 : ι → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [e, map_add, map_smul, smul_eq_mul] at this
    exact this
  -- the weights of the constraints are nonnegative
  have hlam : ∀ j, 0 ≤ lam j := by
    intro j
    have : -lam j ≤ 0 := by
      refine nonpos_of_forall_lt (c := φ ((fun _ => -1 : ι → ℝ), p + 1)) (u := u) fun s hs => ?_
      have hmem :
          ((fun _ => -1 : ι → ℝ), p + 1) + s • (-(Pi.single j 1 : ι → ℝ), (0 : ℝ)) ∈ B := by
        refine ⟨fun i => ?_, ?_⟩
        · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            smul_eq_mul]
          have : 0 ≤ (Pi.single j 1 : ι → ℝ) i := by
            rw [Pi.single_apply]; split_ifs <;> norm_num
          nlinarith
        · simp only [Set.mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero,
            add_zero]
          linarith
      have := hφB _ hmem
      rw [map_add, map_smul, smul_eq_mul, show (-(Pi.single j 1 : ι → ℝ), (0 : ℝ)) =
        -((Pi.single j 1 : ι → ℝ), (0 : ℝ)) by simp, map_neg] at this
      exact this
    linarith
  -- the separating value lies above `p κ`
  have hpu : p * κ ≤ u := by
    refine le_of_forall_pos_lt (d := φ ((fun _ => -1 : ι → ℝ), 1)) fun ε hε => ?_
    have hmem : ((fun _ => -ε : ι → ℝ), p + ε) ∈ B :=
      ⟨fun _ => by simp only; linarith, by simp only [Set.mem_ofPred_eq]; linarith⟩
    have := hφB _ hmem
    have e : ((fun _ => -ε : ι → ℝ), p + ε) =
        p • ((0 : ι → ℝ), (1 : ℝ)) + ε • ((fun _ => -1 : ι → ℝ), (1 : ℝ)) := by
      ext <;> simp [add_comm]
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact this
  have hA : ∀ x ∈ K, u ≤ ∑ j, g j x * lam j + f x * κ := fun x hx => by
    have := hφA ((fun j => g j x), f x) ⟨x, hx, fun j => le_rfl, le_rfl⟩
    rwa [hrep] at this
  -- Slater's point excludes a zero objective weight
  have hκ' : κ < 0 := by
    refine lt_of_le_of_ne hκ fun h0 => ?_
    have h1 := hA x₀ hx₀
    rw [h0, mul_zero, add_zero] at h1
    rw [h0, mul_zero] at hpu
    have hb := hφB _ (hone 0 le_rfl)
    rw [hrep, h0, mul_zero, add_zero] at hb
    simp only [neg_one_mul, Finset.sum_neg_distrib] at hb
    have hg0 : ∑ i, g i x₀ * lam i ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hs i).le (hlam i)
    obtain ⟨j, hj⟩ : ∃ j, 0 < lam j := by
      by_contra hall
      push Not at hall
      have : ∑ j, lam j ≤ 0 := Finset.sum_nonpos fun j _ => hall j
      linarith
    have : ∑ i, g i x₀ * lam i < ∑ _i : ι, (0 : ℝ) :=
      Finset.sum_lt_sum (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hs i).le (hlam i))
        ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos (hs j) hj⟩
    rw [Finset.sum_const_zero] at this
    linarith
  refine ⟨fun j => lam j / -κ, fun j => div_nonneg (hlam j) (by linarith), fun x hx => ?_⟩
  have h1 := hA x hx
  have hk : 0 < -κ := by linarith
  have e : ∑ j, lam j / -κ * g j x = (∑ j, g j x * lam j) / -κ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hk]
  nlinarith

/-- **Strong duality**, value form: if `f` is concave and every `g j` convex on the convex set
`K`, some `x₀ ∈ K` satisfies every constraint strictly, `p` is the greatest value of `f` on the
feasible points of `K`, and for each `μ ≥ 0` `D μ` is the greatest value of the Lagrangian
`f x − ∑ j μ j g j x` on `K`, then `p` is the least value of `D` over `μ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem isLeast_dual {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] {K : Set E} {f : E → ℝ} {g : ι → E → ℝ} {p : ℝ} {x₀ : E} {D : (ι → ℝ) → ℝ}
    (hf : ConcaveOn ℝ K f) (hg : ∀ j, ConvexOn ℝ K (g j)) (hx₀ : x₀ ∈ K)
    (hs : ∀ j, g j x₀ < 0) (hp : IsGreatest (f '' {x | x ∈ K ∧ ∀ j, g j x ≤ 0}) p)
    (hD : ∀ μ : ι → ℝ, (∀ j, 0 ≤ μ j) →
      IsGreatest ((fun x => f x - ∑ j, μ j * g j x) '' K) (D μ)) :
    IsLeast (D '' {μ | ∀ j, 0 ≤ μ j}) p := by
  obtain ⟨⟨xp, ⟨hxp, hgp⟩, rfl⟩, hpub⟩ := hp
  have lower : ∀ μ : ι → ℝ, (∀ j, 0 ≤ μ j) → f xp ≤ D μ := fun μ hμ =>
    le_of_forall_lagrangian_le hμ (fun y hy => (hD μ hμ).2 ⟨y, hy, rfl⟩) hxp hgp
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, hμ, hL⟩ := exists_lagrangian_le hf hg hx₀ hs
      (fun x hx hgx => hpub ⟨x, ⟨hx, hgx⟩, rfl⟩)
    obtain ⟨⟨y, hy, hDy⟩, -⟩ := hD μ hμ
    exact ⟨μ, hμ, le_antisymm (hDy ▸ hL y hy) (lower μ hμ)⟩
  · rintro d ⟨μ, hμ, rfl⟩
    exact lower μ hμ

end powerlib.SpecialFunctions
