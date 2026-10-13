import theorem.DAE.Weierstrass
import theorem.DAE.Linear
import theorem.DAE.Pryce

/-! # Kronecker index = differentiation index for linear constant-coefficient DAEs

Foundation layer (category B of the work-sync formalization).

Object: the linear DAE `E x' = A x + f` with `E A : Matrix ι ι K` (`K` a field, `ι` finite).

Index definitions used. Neither `theorem.DAE.Linear` nor `theorem.DAE.Pryce` defines a
differentiation index for general linear DAEs: `Linear` treats the semi-explicit index-1 case
(`IsUnit Ayy.det`, one differentiation of the constraint, with the correction "index `k` = `k`
differentiations"), and `Pryce` defines structural index formulas (`noteIndex`, `pryceIndex`) of a
signature. The differentiation index here is Campbell's derivative-array index:
* The derivative array of order `μ` consists of the DAE and its first `μ` derivatives,
  `E x^(r+1) = A x^(r) + f^(r)`, `r = 0, …, μ`, viewed as linear equations for
  `x', …, x^(μ+1)` given `x` and `f, …, f^(μ)`. It is *1-full* (`OneFull E A μ`) when it determines
  `x'` uniquely: every solution `w` of the homogeneous array (`E w₀ = 0`,
  `E w_{r+1} = A w_r` for `r < μ`) has `w₀ = 0`.
* `IsDiffIndex E A ν`: the array is 1-full at order `ν` and at no smaller order (the number of
  differentiations needed to determine `x'`; index `0` = explicit ODE, `isDiffIndex_zero_iff`).
Solution-level meaning over `ℝ` (`oneFull_iff_velocity_determined`): the array of order `μ` is
1-full iff, for all solutions that are `μ + 1` times differentiable with `μ` times
differentiable inputs, equal states and equal input jets `f^(r)(t)`, `r ≤ μ`, at an instant
force equal velocities there (`velocity_eq_of_oneFull`); otherwise a polynomial solution with the
data of the zero solution and nonzero velocity exists (`exists_solution_of_not_oneFull`).

Results.
* `oneFull_equiv_iff`: 1-fullness is invariant under `(E, A) ↦ (P E Q, P A Q)` with invertible
  `P`, `Q` (rectangular index sets allowed).
* `oneFull_blocks_iff`: on the Weierstrass form `(diag(I, N), diag(J, I))`, 1-fullness of
  order `μ` holds iff `N ^ μ = 0`.
* **`WeierstrassForm.isDiffIndex_iff`** (Kronecker index = differentiation index): for every
  Weierstrass form of `(E, A)`, `IsDiffIndex E A ν ↔ ν = nilpotencyClass N`.
  `kroneckerIndex_eq` (the nilpotency class does not depend on the chosen Weierstrass form) and
  `exists_isDiffIndex` (every regular pencil over an infinite field has a differentiation index).
* On solutions (`WeierstrassForm.velocity_determined_iff`): state and input jet of order `μ`
  determine the velocity iff `μ ≥ nilpotencyClass N`; the Kronecker index is the least number of
  differentiations of the DAE that determines `x'`.
* Alignment with `theorem.DAE.Linear`: a semi-explicit linear DAE with invertible `Ayy` and
  `m > 0` algebraic variables has differentiation index exactly `1`
  (`LinearDAE.isDiffIndex_one`), matching the corrected count of that module.
* Alignment with `theorem.DAE.Pryce`: the correction example `ẋ₁ = y, ẋ₂ = x₁ - y,
  ẋ₁ + 2ẋ₂ = 0` (as the linear DAE `pryceExampleE`, `pryceExampleA`, whose signature is
  `exampleSig`) has differentiation index `1` (`pryceExample_isDiffIndex`), equal to Pryce's
  corrected formula and not to the note's formula (`pryceExample_index_vs_formulas`).

Source claim (T-pantelides-index-reduction §1.1, §1.6): "`ν` (the nilpotency index of `N`) is the
Kronecker index, and for linear DAEs it coincides with the differentiation index." Formalized
with the regularity premise of `theorem.DAE.Weierstrass` and the derivative-array definition
above.

Model boundary: constant coefficients, regular square pencils; the index is the
derivative-array (1-fullness) index; no claim about time-varying or nonlinear DAEs, about the
geometric index, or about consistent initialization beyond the determination of `x'`.

Architecture: generic mathematical support (no `Family`). `OneFull` and `IsDiffIndex` are static
linear-algebra conditions on matrices (sequences indexed by `ℕ`, not by time); the solution-level
statements write the trajectories and their derivatives out in the theorems.

Source: work-sync theory/T-pantelides-index-reduction.md §1.1, §1.6;
theory/T-dae-systems.md §1.3 (index as number of differentiations), §1.6.2.
-/

noncomputable section
namespace powerlib.DAE
open Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Derivative-array index -/

/-- The derivative array of `E x' = A x + f` of order `μ` determines `x'` (1-fullness): every
homogeneous solution `w` (`w r` standing for the difference of `x^(r+1)`) with `E w₀ = 0` and
`E w_{r+1} = A w_r` for `r < μ` has `w₀ = 0`. -/
def OneFull (E A : Matrix ι ι K) (μ : ℕ) : Prop :=
  ∀ w : ℕ → ι → K, E *ᵥ w 0 = 0 → (∀ r < μ, E *ᵥ w (r + 1) = A *ᵥ w r) → w 0 = 0

/-- Differentiation index `ν`: the derivative array is 1-full at order `ν` and at no smaller
order. -/
def IsDiffIndex (E A : Matrix ι ι K) (ν : ℕ) : Prop :=
  OneFull E A ν ∧ ∀ μ < ν, ¬ OneFull E A μ

omit [DecidableEq ι] in
@[powerlib_foundation] theorem oneFull_mono {E A : Matrix ι ι K} {μ μ' : ℕ}
    (h : OneFull E A μ) (hle : μ ≤ μ') : OneFull E A μ' :=
  fun w h0 hr => h w h0 fun r hr' => hr r (by omega)

omit [DecidableEq ι] in
@[powerlib_foundation] theorem isDiffIndex_unique {E A : Matrix ι ι K} {ν ν' : ℕ}
    (h : IsDiffIndex E A ν) (h' : IsDiffIndex E A ν') : ν = ν' := by
  rcases lt_trichotomy ν ν' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 ν hlt)
  · exact heq
  · exact absurd h'.1 (h.2 ν' hgt)

omit [DecidableEq ι] in
/-- The differentiation index is the least order at which the derivative array is 1-full. -/
@[powerlib_foundation] theorem isDiffIndex_iff_least {E A : Matrix ι ι K} {ν : ℕ} :
    IsDiffIndex E A ν ↔ OneFull E A ν ∧ ∀ μ, OneFull E A μ → ν ≤ μ := by
  constructor
  · rintro ⟨h, hmin⟩
    exact ⟨h, fun μ hμ => not_lt.mp fun hlt => hmin μ hlt hμ⟩
  · rintro ⟨h, hmin⟩
    exact ⟨h, fun μ hlt hμ => absurd (hmin μ hμ) (not_le.mpr hlt)⟩

omit [DecidableEq ι] in
/-- Some order is 1-full iff the differentiation index exists. -/
@[powerlib_foundation] theorem exists_isDiffIndex_iff {E A : Matrix ι ι K} :
    (∃ ν, IsDiffIndex E A ν) ↔ ∃ μ, OneFull E A μ := by
  classical
  constructor
  · rintro ⟨ν, h⟩; exact ⟨ν, h.1⟩
  · intro h
    exact ⟨Nat.find h, Nat.find_spec h, fun μ hlt hμ => Nat.find_min h hlt hμ⟩

/-- Index `0` means an explicit ODE: `IsDiffIndex E A 0` iff `E` is invertible. -/
@[powerlib_foundation] theorem isDiffIndex_zero_iff {E A : Matrix ι ι K} :
    IsDiffIndex E A 0 ↔ IsUnit E.det := by
  have h0 : OneFull E A 0 ↔ ∀ v, E *ᵥ v = 0 → v = 0 := by
    constructor
    · intro h v hv
      exact h (fun _ => v) hv fun r hr => absurd hr (Nat.not_lt_zero r)
    · intro h w hw _
      exact h _ hw
  rw [IsDiffIndex, h0, isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨h, -⟩ ⟨v, hv, hEv⟩
    exact hv (h v hEv)
  · intro h
    exact ⟨fun v hv => by_contra fun hne => h ⟨v, hne, hv⟩, fun μ hμ => absurd hμ (Nat.not_lt_zero μ)⟩

/-! ## Invariance under equivalence transformations -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- 1-fullness is invariant under `(E, A) ↦ (P E Q, P A Q)` with `P` left-invertible and `Q`
invertible. -/
@[powerlib_foundation] theorem oneFull_equiv_iff {E A : Matrix ι ι K} {P : Matrix κ ι K}
    {P' : Matrix ι κ K} {Q : Matrix ι κ K} {Q' : Matrix κ ι K} (hP : P' * P = 1)
    (hQ : Q * Q' = 1) (hQ' : Q' * Q = 1) (μ : ℕ) :
    OneFull (P * E * Q) (P * A * Q) μ ↔ OneFull E A μ := by
  have cancelP : ∀ v v' : ι → K, P *ᵥ v = P *ᵥ v' → v = v' := fun v v' h => by
    have := congrArg (P' *ᵥ ·) h
    simpa [mulVec_mulVec, hP] using this
  constructor
  · intro h w h0 hr
    have hQw : ∀ r, Q *ᵥ (Q' *ᵥ w r) = w r := fun r => by simp [mulVec_mulVec, hQ]
    have := h (fun r => Q' *ᵥ w r) (by simp [← mulVec_mulVec, hQw, h0])
      (fun r hlt => by simp only [← mulVec_mulVec, hQw, hr r hlt])
    rw [← hQw 0, this, mulVec_zero]
  · intro h w h0 hr
    have h0' : E *ᵥ (Q *ᵥ w 0) = 0 := cancelP _ _ (by
      rw [mulVec_mulVec, mulVec_mulVec, h0, mulVec_zero])
    have hr' : ∀ r < μ, E *ᵥ (Q *ᵥ w (r + 1)) = A *ᵥ (Q *ᵥ w r) := fun r hlt =>
      cancelP _ _ (by
        rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hr r hlt])
    have := h (fun r => Q *ᵥ w r) h0' hr'
    have h2 : Q' *ᵥ (Q *ᵥ w 0) = w 0 := by simp [mulVec_mulVec, hQ']
    rw [← h2, this, mulVec_zero]

/-! ## The Weierstrass form -/

private theorem eq_zero_of_forall_mulVec {m n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix m n K} (h : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-- On the Weierstrass block form `(diag(I, N), diag(J, I))` with `N` nilpotent, the derivative
array of order `μ` is 1-full iff `N ^ μ = 0`. -/
@[powerlib_foundation] theorem oneFull_blocks_iff {k l : ℕ} (J : Matrix (Fin k) (Fin k) K)
    {N : Matrix (Fin l) (Fin l) K} (hN : IsNilpotent N) (μ : ℕ) :
    OneFull (fromBlocks 1 0 0 N) (fromBlocks J 0 0 1) μ ↔ N ^ μ = 0 := by
  constructor
  · intro h
    have hker : ∀ v : Fin l → K, (N ^ (μ + 1)) *ᵥ v = 0 → (N ^ μ) *ᵥ v = 0 := by
      intro v hv
      have hw := h (fun r => Sum.elim 0 ((N ^ (μ - r)) *ᵥ v)) ?_ ?_
      · funext i
        simpa using congrFun hw (Sum.inr i)
      · rw [fromBlocks_mulVec]
        ext (i | i)
        · simp
        · have := congrFun hv i
          simp only [Nat.sub_zero, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
          simpa [mulVec_mulVec, ← pow_succ'] using this
      · intro r hr
        rw [fromBlocks_mulVec, fromBlocks_mulVec]
        ext (i | i)
        · simp
        · have he : μ - r = μ - (r + 1) + 1 := by omega
          simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
          simp [mulVec_mulVec, ← pow_succ', ← he]
    have hall : ∀ j v, (N ^ (μ + j)) *ᵥ v = 0 → (N ^ μ) *ᵥ v = 0 := by
      intro j
      induction j with
      | zero => intro v hv; simpa using hv
      | succ j ih =>
        intro v hv
        apply hker
        have h1 : (N ^ (μ + j)) *ᵥ (N *ᵥ v) = 0 := by
          rw [mulVec_mulVec, ← pow_succ, ← hv]; congr 2
        have h2 := ih _ h1
        rwa [mulVec_mulVec, ← pow_succ] at h2
    obtain ⟨m, hm⟩ := hN
    exact eq_zero_of_forall_mulVec fun v => hall m v (by rw [pow_add, hm, mul_zero, zero_mulVec])
  · intro h w h0 hr
    have ha0 : ∀ i, w 0 (Sum.inl i) = 0 := by
      intro i
      have := congrFun h0 (Sum.inl i)
      simpa [fromBlocks_mulVec, Function.comp_def] using this
    have hb : ∀ r < μ, N *ᵥ (fun i => w (r + 1) (Sum.inr i)) = fun i => w r (Sum.inr i) := by
      intro r hlt
      funext i
      have := congrFun (hr r hlt) (Sum.inr i)
      simpa [fromBlocks_mulVec, Function.comp_def] using this
    have hpow : ∀ r ≤ μ, (fun i => w 0 (Sum.inr i)) = (N ^ r) *ᵥ fun i => w r (Sum.inr i) := by
      intro r
      induction r with
      | zero => intro _; simp
      | succ r ih =>
        intro hle
        rw [ih (by omega), ← hb r (by omega), mulVec_mulVec, ← pow_succ]
    have hb0' := hpow μ le_rfl
    rw [h, zero_mulVec] at hb0'
    funext x
    rcases x with i | i
    · exact ha0 i
    · exact congrFun hb0' i

/-- `N ^ μ = 0` for all `μ ≥ ν` and for no smaller `μ` iff `ν` is the nilpotency class. -/
private theorem pow_eq_zero_iff_class {R : Type*} [MonoidWithZero R] {N : R} (hN : IsNilpotent N)
    (ν : ℕ) : (N ^ ν = 0 ∧ ∀ μ < ν, N ^ μ ≠ 0) ↔ ν = nilpotencyClass N := by
  constructor
  · rintro ⟨h, hmin⟩
    refine le_antisymm ?_ (Nat.sInf_le h)
    by_contra hlt
    exact hmin _ (not_le.mp hlt) (pow_nilpotencyClass hN)
  · rintro rfl
    exact ⟨pow_nilpotencyClass hN, fun μ hlt h => (not_le.mpr hlt) (Nat.sInf_le h)⟩

/-- Differentiation index of the Weierstrass block form = nilpotency class of `N`. -/
@[powerlib_foundation] theorem isDiffIndex_blocks_iff {k l : ℕ} (J : Matrix (Fin k) (Fin k) K)
    {N : Matrix (Fin l) (Fin l) K} (hN : IsNilpotent N) (ν : ℕ) :
    IsDiffIndex (fromBlocks 1 0 0 N) (fromBlocks J 0 0 1) ν ↔ ν = nilpotencyClass N := by
  rw [IsDiffIndex, oneFull_blocks_iff J hN, ← pow_eq_zero_iff_class hN]
  simp only [oneFull_blocks_iff J hN, ne_eq]

namespace WeierstrassForm

variable {E A : Matrix ι ι K} (W : WeierstrassForm E A)

/-- For a pencil in Weierstrass form, 1-fullness of order `μ` is `N ^ μ = 0`. -/
@[powerlib_foundation] theorem oneFull_iff (μ : ℕ) : OneFull E A μ ↔ W.N ^ μ = 0 := by
  rw [← oneFull_equiv_iff W.P'_mul_P W.Q_mul_Q' W.Q'_mul_Q μ, W.E_eq, W.A_eq,
    oneFull_blocks_iff W.J W.nilpotent]

/-- **Kronecker index = differentiation index.** For every Weierstrass form
`P (s E - A) Q = diag(s I - J, s N - I)`, the differentiation index of `E x' = A x + f` is the
nilpotency class of `N` (the least `ν` with `N ^ ν = 0`). -/
@[powerlib_foundation] theorem isDiffIndex_iff (ν : ℕ) :
    IsDiffIndex E A ν ↔ ν = nilpotencyClass W.N := by
  rw [IsDiffIndex, W.oneFull_iff, ← pow_eq_zero_iff_class W.nilpotent]
  simp only [W.oneFull_iff, ne_eq]

@[powerlib_foundation] theorem isDiffIndex : IsDiffIndex E A (nilpotencyClass W.N) :=
  (W.isDiffIndex_iff _).mpr rfl

end WeierstrassForm

/-- The Kronecker index is well defined: two Weierstrass forms of the same pencil have nilpotent
blocks of the same nilpotency class. -/
@[powerlib_foundation] theorem kroneckerIndex_eq {E A : Matrix ι ι K} (W W' : WeierstrassForm E A) :
    nilpotencyClass W.N = nilpotencyClass W'.N :=
  isDiffIndex_unique W.isDiffIndex W'.isDiffIndex

/-- Every regular pencil over an infinite field has a differentiation index, equal to the
Kronecker index of any of its Weierstrass forms. -/
@[powerlib_foundation] theorem exists_isDiffIndex [Infinite K] {E A : Matrix ι ι K}
    (h : Regular E A) : ∃ ν, IsDiffIndex E A ν ∧ ∀ W : WeierstrassForm E A, ν = nilpotencyClass W.N := by
  obtain ⟨W⟩ := weierstrass h
  exact ⟨_, W.isDiffIndex, fun W' => kroneckerIndex_eq W W'⟩

/-! ## Meaning on solutions -/

private theorem hasDerivAt_mulVec {M : Matrix ι ι ℝ} {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : HasDerivAt x v t) : HasDerivAt (fun s => M *ᵥ x s) (M *ᵥ v) t :=
  (LinearMap.toContinuousLinearMap (Matrix.toLin' M)).hasFDerivAt.comp_hasDerivAt t h

/-- Along a solution of `E x' = A x + f` with `x 0 = x`, `x (r + 1) = (x r)'` (`r ≤ μ`) and
`f (r + 1) = (f r)'` (`r < μ`), the derivative array of order `μ` holds:
`E x^(r+1) = A x^(r) + f^(r)` for `r ≤ μ`. -/
@[powerlib_foundation] theorem derivArray_of_solution {E A : Matrix ι ι ℝ} {μ : ℕ}
    {x f : ℕ → ℝ → ι → ℝ} (hx : ∀ r ≤ μ, ∀ t, HasDerivAt (x r) (x (r + 1) t) t)
    (hf : ∀ r < μ, ∀ t, HasDerivAt (f r) (f (r + 1) t) t)
    (hs : ∀ t, E *ᵥ x 1 t = A *ᵥ x 0 t + f 0 t) :
    ∀ r ≤ μ, ∀ t, E *ᵥ x (r + 1) t = A *ᵥ x r t + f r t := by
  intro r
  induction r with
  | zero => intro _; exact hs
  | succ r ih =>
    intro hr t
    have hfun : (fun s => E *ᵥ x (r + 1) s) = fun s => A *ᵥ x r s + f r s :=
      funext (ih (by omega))
    have h1 : HasDerivAt (fun s => E *ᵥ x (r + 1) s) (E *ᵥ x (r + 2) t) t :=
      hasDerivAt_mulVec (hx (r + 1) hr t)
    have h2 : HasDerivAt (fun s => A *ᵥ x r s + f r s) (A *ᵥ x (r + 1) t + f (r + 1) t) t :=
      (hasDerivAt_mulVec (hx r (by omega) t)).add (hf r (by omega) t)
    rw [hfun] at h1
    exact h1.unique h2

/-- Meaning of 1-fullness for `E x' = A x + f`: if the derivative array of order `μ` is 1-full,
two solutions that are `μ + 1` times differentiable (`x r` the `r`-th derivative), driven by
inputs `f`, `g` that are `μ` times differentiable, with equal states and equal input jets
`f^(r)(t) = g^(r)(t)`, `r ≤ μ`, at an instant `t`, have the same velocity at `t`. -/
@[powerlib_foundation] theorem velocity_eq_of_oneFull {E A : Matrix ι ι ℝ} {μ : ℕ}
    (h : OneFull E A μ) {x y f g : ℕ → ℝ → ι → ℝ} {t : ℝ}
    (hx : ∀ r ≤ μ, ∀ s, HasDerivAt (x r) (x (r + 1) s) s)
    (hy : ∀ r ≤ μ, ∀ s, HasDerivAt (y r) (y (r + 1) s) s)
    (hf : ∀ r < μ, ∀ s, HasDerivAt (f r) (f (r + 1) s) s)
    (hg : ∀ r < μ, ∀ s, HasDerivAt (g r) (g (r + 1) s) s)
    (hxs : ∀ s, E *ᵥ x 1 s = A *ᵥ x 0 s + f 0 s) (hys : ∀ s, E *ᵥ y 1 s = A *ᵥ y 0 s + g 0 s)
    (h0 : x 0 t = y 0 t) (hfg : ∀ r ≤ μ, f r t = g r t) : x 1 t = y 1 t := by
  have hX := derivArray_of_solution hx hf hxs
  have hY := derivArray_of_solution hy hg hys
  have hw := h (fun r => x (r + 1) t - y (r + 1) t) ?_ ?_
  · exact sub_eq_zero.mp hw
  · simp only [mulVec_sub, hX 0 (Nat.zero_le _) t, hY 0 (Nat.zero_le _) t, h0,
      hfg 0 (Nat.zero_le _)]
    abel
  · intro r hr
    simp only [mulVec_sub, hX (r + 1) hr t, hY (r + 1) hr t, hfg (r + 1) hr]
    abel

/-- Polynomial jet `t ↦ Σ_{r ≤ μ, k ≤ r + 1} t^(r+1-k)/(r+1-k)! • w r`; `jetPoly w μ (k + 1)` is
the derivative of `jetPoly w μ k`. -/
private def jetPoly (w : ℕ → ι → ℝ) (μ k : ℕ) (t : ℝ) : ι → ℝ :=
  ∑ r ∈ Finset.range (μ + 1),
    if k ≤ r + 1 then (t ^ (r + 1 - k) / ((r + 1 - k).factorial : ℝ)) • w r else 0

private theorem hasDerivAt_monomial (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ (m + 1) / ((m + 1).factorial : ℝ))
      (t ^ m / (m.factorial : ℝ)) t := by
  have h := (hasDerivAt_pow (m + 1) t).div_const ((m + 1).factorial : ℝ)
  convert h using 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
  have : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp

omit [DecidableEq ι] in
private theorem hasDerivAt_jetPoly (w : ℕ → ι → ℝ) (μ k : ℕ) (t : ℝ) :
    HasDerivAt (jetPoly w μ k) (jetPoly w μ (k + 1) t) t := by
  unfold jetPoly
  have : (fun s => ∑ r ∈ Finset.range (μ + 1),
      if k ≤ r + 1 then (s ^ (r + 1 - k) / ((r + 1 - k).factorial : ℝ)) • w r else 0) =
      fun s => ∑ r ∈ Finset.range (μ + 1),
      (fun r s => if k ≤ r + 1 then (s ^ (r + 1 - k) / ((r + 1 - k).factorial : ℝ)) • w r
        else 0) r s := rfl
  rw [this]
  refine HasDerivAt.fun_sum fun r _ => ?_
  by_cases h1 : k + 1 ≤ r + 1
  · have hk : k ≤ r + 1 := by omega
    obtain ⟨m, hm⟩ : ∃ m, r + 1 - k = m + 1 := ⟨r - k, by omega⟩
    have hm' : r + 1 - (k + 1) = m := by omega
    simp only [hk, h1, ite_true, hm, hm']
    exact (hasDerivAt_monomial m t).smul_const (w r)
  · simp only [h1, ite_false]
    by_cases hk : k ≤ r + 1
    · have he : r + 1 - k = 0 := by omega
      simp only [hk, ite_true, he, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
      exact hasDerivAt_const t (w r)
    · simp only [hk, ite_false]
      exact hasDerivAt_const t 0

omit [Fintype ι] [DecidableEq ι] in
private theorem jetPoly_zero_succ (w : ℕ → ι → ℝ) (μ k : ℕ) (hk : k ≤ μ) :
    jetPoly w μ (k + 1) 0 = w k := by
  unfold jetPoly
  rw [Finset.sum_eq_single k]
  · simp
  · intro r _ hr
    by_cases h : k + 1 ≤ r + 1
    · have hpos : r + 1 - (k + 1) ≠ 0 := by omega
      simp only [h, ite_true, zero_pow hpos, zero_div, zero_smul]
    · simp [h]
  · intro hk'
    exact absurd (Finset.mem_range.mpr (by omega)) hk'

omit [Fintype ι] [DecidableEq ι] in
private theorem jetPoly_zero_zero (w : ℕ → ι → ℝ) (μ : ℕ) : jetPoly w μ 0 0 = 0 := by
  unfold jetPoly
  refine Finset.sum_eq_zero fun r _ => ?_
  simp

/-- Converse: if the derivative array of order `μ` is not 1-full, `μ` differentiations do not
determine the velocity. There is a polynomial solution `x` of `E x' = A x + f` with the data of
the zero solution at `t = 0` — `x(0) = 0` and input jet `f^(r)(0) = 0` for `r ≤ μ` — but
`x'(0) ≠ 0` (`x r` and `f r` are the `r`-th derivatives, defined for all `r`). -/
@[powerlib_foundation] theorem exists_solution_of_not_oneFull {E A : Matrix ι ι ℝ} {μ : ℕ}
    (h : ¬ OneFull E A μ) :
    ∃ x f : ℕ → ℝ → ι → ℝ, (∀ r t, HasDerivAt (x r) (x (r + 1) t) t) ∧
      (∀ r t, HasDerivAt (f r) (f (r + 1) t) t) ∧ (∀ t, E *ᵥ x 1 t = A *ᵥ x 0 t + f 0 t) ∧
      x 0 0 = 0 ∧ (∀ r ≤ μ, f r 0 = 0) ∧ x 1 0 ≠ 0 := by
  simp only [OneFull, not_forall] at h
  obtain ⟨w, h0, hr, hw⟩ := h
  refine ⟨jetPoly w μ, fun k t => E *ᵥ jetPoly w μ (k + 1) t - A *ᵥ jetPoly w μ k t,
    hasDerivAt_jetPoly w μ, fun k t => ?_, fun t => (add_sub_cancel _ _).symm, jetPoly_zero_zero w μ,
    ?_, ?_⟩
  · exact (hasDerivAt_mulVec (hasDerivAt_jetPoly w μ (k + 1) t)).sub
      (hasDerivAt_mulVec (hasDerivAt_jetPoly w μ k t))
  · intro r hrμ
    rcases r with _ | r
    · simp only [jetPoly_zero_succ w μ 0 (Nat.zero_le _), jetPoly_zero_zero, h0, mulVec_zero,
        sub_zero]
    · simp only [jetPoly_zero_succ w μ (r + 1) hrμ, jetPoly_zero_succ w μ r (by omega),
        hr r (by omega), sub_self]
  · rw [jetPoly_zero_succ w μ 0 (Nat.zero_le _)]
    exact hw

/-- **Solution-level characterization of 1-fullness.** The derivative array of order `μ` is
1-full iff, for all solutions of `E x' = A x + f` that are `μ + 1` times differentiable with
inputs `μ` times differentiable, equal states and equal input jets of order `μ` at an instant
force equal velocities there. -/
@[powerlib_foundation] theorem oneFull_iff_velocity_determined {E A : Matrix ι ι ℝ} {μ : ℕ} :
    OneFull E A μ ↔ ∀ (x y f g : ℕ → ℝ → ι → ℝ) (t : ℝ),
      (∀ r ≤ μ, ∀ s, HasDerivAt (x r) (x (r + 1) s) s) →
      (∀ r ≤ μ, ∀ s, HasDerivAt (y r) (y (r + 1) s) s) →
      (∀ r < μ, ∀ s, HasDerivAt (f r) (f (r + 1) s) s) →
      (∀ r < μ, ∀ s, HasDerivAt (g r) (g (r + 1) s) s) →
      (∀ s, E *ᵥ x 1 s = A *ᵥ x 0 s + f 0 s) → (∀ s, E *ᵥ y 1 s = A *ᵥ y 0 s + g 0 s) →
      x 0 t = y 0 t → (∀ r ≤ μ, f r t = g r t) → x 1 t = y 1 t := by
  constructor
  · intro h x y f g t hx hy hf hg hxs hys h0 hfg
    exact velocity_eq_of_oneFull h hx hy hf hg hxs hys h0 hfg
  · intro H
    by_contra h
    obtain ⟨x, f, hx, hf, hxs, hx0, hf0, hx1⟩ := exists_solution_of_not_oneFull h
    exact hx1 (H x (fun _ _ => 0) f (fun _ _ => 0) 0 (fun r _ => hx r)
      (fun _ _ s => hasDerivAt_const s 0) (fun r _ => hf r) (fun _ _ s => hasDerivAt_const s 0)
      hxs (fun _ => by simp) hx0 hf0)

/-- **Kronecker index = differentiation index, on solutions.** For a pencil in Weierstrass form,
equal states and input jets of order `μ` determine the velocity of `μ + 1` times differentiable
solutions iff `μ ≥ nilpotencyClass N`: the Kronecker index is the least number of
differentiations of the DAE that determines `x'`. -/
@[powerlib_foundation] theorem WeierstrassForm.velocity_determined_iff {E A : Matrix ι ι ℝ}
    (W : WeierstrassForm E A) (μ : ℕ) :
    (∀ (x y f g : ℕ → ℝ → ι → ℝ) (t : ℝ),
      (∀ r ≤ μ, ∀ s, HasDerivAt (x r) (x (r + 1) s) s) →
      (∀ r ≤ μ, ∀ s, HasDerivAt (y r) (y (r + 1) s) s) →
      (∀ r < μ, ∀ s, HasDerivAt (f r) (f (r + 1) s) s) →
      (∀ r < μ, ∀ s, HasDerivAt (g r) (g (r + 1) s) s) →
      (∀ s, E *ᵥ x 1 s = A *ᵥ x 0 s + f 0 s) → (∀ s, E *ᵥ y 1 s = A *ᵥ y 0 s + g 0 s) →
      x 0 t = y 0 t → (∀ r ≤ μ, f r t = g r t) → x 1 t = y 1 t) ↔
      nilpotencyClass W.N ≤ μ := by
  rw [← oneFull_iff_velocity_determined, W.oneFull_iff]
  constructor
  · exact fun h => Nat.sInf_le h
  · intro h
    exact pow_eq_zero_of_le h (pow_nilpotencyClass W.nilpotent)

/-! ## Alignment with `theorem.DAE.Linear`: semi-explicit index 1 -/

namespace LinearDAE

variable {n m p : ℕ} (d : LinearDAE n m p)

/-- Index-1 semi-explicit DAE (`Ayy` invertible): one differentiation determines the
velocity. -/
@[powerlib_foundation] theorem oneFull_one (hA : IsUnit d.Ayy.det) :
    OneFull (massMatrix n m) d.jacobian 1 := by
  intro w h0 hr
  have h1 := hr 0 Nat.zero_lt_one
  have hx : ∀ i, w 0 (Sum.inl i) = 0 := by
    intro i
    have := congrFun h0 (Sum.inl i)
    simpa [massMatrix, fromBlocks_mulVec, Function.comp_def] using this
  have hy : d.Ayy *ᵥ (fun i => w 0 (Sum.inr i)) = 0 := by
    funext i
    have := congrFun h1 (Sum.inr i)
    have hx' : (fun j => w 0 (Sum.inl j)) = 0 := funext hx
    simp only [massMatrix, jacobian, fromBlocks_mulVec, Function.comp_def, Sum.elim_inr,
      zero_mulVec, add_zero, Pi.zero_apply, hx', mulVec_zero, zero_add] at this
    simpa using this.symm
  have hy0 : (fun i => w 0 (Sum.inr i)) = 0 := by
    calc (fun i => w 0 (Sum.inr i)) = (d.Ayy⁻¹ * d.Ayy) *ᵥ (fun i => w 0 (Sum.inr i)) := by
          rw [nonsing_inv_mul _ hA, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, hy, mulVec_zero]
  funext x
  rcases x with i | i
  · exact hx i
  · exact congrFun hy0 i

/-- With `m > 0` algebraic variables, the undifferentiated system does not determine the
velocity of the algebraic variables. -/
@[powerlib_foundation] theorem not_oneFull_zero (hm : 0 < m) :
    ¬ OneFull (massMatrix n m) d.jacobian 0 := by
  intro h
  have := h (fun _ => Sum.elim 0 fun _ => 1) ?_ fun r hr => absurd hr (Nat.not_lt_zero r)
  · have h' := congrFun this (Sum.inr ⟨0, hm⟩)
    simp at h'
  · funext x
    rcases x with i | i <;> simp [massMatrix, fromBlocks_mulVec, Function.comp_def]

/-- A semi-explicit linear DAE with invertible `Ayy` and `m > 0` has differentiation index
exactly `1` (one differentiation of the constraint, as corrected in `theorem.DAE.Linear`). -/
@[powerlib_foundation] theorem isDiffIndex_one (hA : IsUnit d.Ayy.det) (hm : 0 < m) :
    IsDiffIndex (massMatrix n m) d.jacobian 1 :=
  ⟨d.oneFull_one hA, fun μ hμ => by
    obtain rfl : μ = 0 := by omega
    exact d.not_oneFull_zero hm⟩

end LinearDAE

/-! ## Alignment with `theorem.DAE.Pryce`: the index-formula counterexample -/

/-- `ẋ₁ = y, ẋ₂ = x₁ - y, ẋ₁ + 2ẋ₂ = 0` as `E z' = A z`, `z = (x₁, x₂, y)`: the matrix `E` of
derivative coefficients. -/
def pryceExampleE : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 1, 2, 0]

/-- The matrix `A` of the counterexample: `ẋ₁ = y`, `ẋ₂ = x₁ - y`, `ẋ₁ + 2ẋ₂ = 0`. -/
def pryceExampleA : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, -1; 0, 0, 0]

/-- The signature `exampleSig` of `theorem.DAE.Pryce` is the occurrence/order pattern of this
linear DAE. -/
@[powerlib_foundation] theorem pryceExample_signature (i j : Fin 3) :
    (exampleSig.occurs i j = true ↔ pryceExampleE i j ≠ 0 ∨ pryceExampleA i j ≠ 0) ∧
      exampleSig.order i j = if pryceExampleE i j ≠ 0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [exampleSig, pryceExampleE, pryceExampleA]

/-- The counterexample has differentiation index `1`. -/
@[powerlib_foundation] theorem pryceExample_isDiffIndex :
    IsDiffIndex pryceExampleE pryceExampleA 1 := by
  refine ⟨fun w h0 hr => ?_, fun μ hμ hμ' => ?_⟩
  · have h1 := hr 0 Nat.zero_lt_one
    have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    have f0 := congrFun h1 0
    have f1 := congrFun h1 1
    have f2 := congrFun h1 2
    simp [pryceExampleE, pryceExampleA, mulVec, dotProduct, Fin.sum_univ_three] at e0 e1 f0 f1 f2
    funext i
    fin_cases i <;> simp <;> linarith
  · obtain rfl : μ = 0 := by omega
    have := hμ' (fun _ => ![0, 0, 1]) (by
      funext i
      fin_cases i <;> simp [pryceExampleE, mulVec, dotProduct, Fin.sum_univ_three])
      fun r hr => absurd hr (Nat.not_lt_zero r)
    have h2 := congrFun this 2
    simp at h2

/-- The differentiation index `1` of the counterexample equals Pryce's corrected formula and
differs from the note's formula (`0`). -/
@[powerlib_foundation] theorem pryceExample_index_vs_formulas :
    IsDiffIndex pryceExampleE pryceExampleA (exampleSig.pryceIndex exampleC exampleD) ∧
      ¬ IsDiffIndex pryceExampleE pryceExampleA (exampleSig.noteIndex exampleC) := by
  rw [example_pryceIndex, example_noteIndex]
  exact ⟨pryceExample_isDiffIndex, fun h =>
    absurd (isDiffIndex_unique h pryceExample_isDiffIndex) (by norm_num)⟩

end powerlib.DAE
