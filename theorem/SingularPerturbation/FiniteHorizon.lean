import theorem.SingularPerturbation.FrozenFast

/-! # Linear singular perturbation: the finite-horizon `O(ε)` error (Tikhonov, linear case)

Foundation layer (category B).

System (continuous time, constant real matrices, `n` slow states `x`, `m` fast states `z`,
small parameter `ε > 0`, no input; the same `LinearSP` data as
`theorem.SingularPerturbation.Linear`):
```
ẋ = A₁₁ x + A₁₂ z,        ε ż = A₂₁ x + A₂₂ z .
```
Quasi-steady state `z = h(x) = −L x`, `L = A₂₂⁻¹A₂₁` (`LinearSP.gain`); reduced (slow) system
`x̄' = A₀ x̄`, `A₀ = A₁₁ − A₁₂A₂₂⁻¹A₂₁` (`LinearSP.reducedMatrix`), `x̄(0) = x(0)`; boundary-layer
system in the fast time `τ = t/ε`: `dz_b/dτ = A₂₂ z_b`, `z_b(0) = z(0) − h(x(0)) = z(0) + L x(0)`.
Solutions are global coordinate solutions (`∀ t, HasDerivAt x (…) t`, which every solution of
these linear equations is); `|v|² = v ⬝ᵥ v`.

Main result (`LinearSP.exists_finiteHorizon_error`): if the boundary-layer matrix `A₂₂` is
Hurwitz, then for every horizon `T` there are `ε₀ > 0` and `C` such that for all
`ε ∈ (0, ε₀]`, all solutions and all `t ∈ [0, T]`
```
|x(t) − x̄(t)|²                       ≤ C ε² (|x(0)|² + |z(0)|²),
|z(t) − (h(x̄(t)) + z_b(t/ε))|²        ≤ C ε² (|x(0)|² + |z(0)|²),
```
i.e. both errors are `O(ε)` uniformly on `[0, T]`, including the initial layer. Stability of
the reduced matrix `A₀` is **not** assumed (finite horizon); `ε₀ = 1/(K + 1)` and `C` are
explicit in the proof (`K` from the Lyapunov solution of `A₂₂`).

This is the corrected form of `T-tikhonov` §1.1 (see `theorem.SingularPerturbation.Tikhonov`,
Correction 1: without the boundary-layer term the bound fails at `t = 0`), proved here for the
general linear system rather than the scalar test system.

Proof (energy estimates, no matrix exponentials): coordinates `η = z + L x`
(`LinearSP.coords_hasDerivAt`: `ẋ = A₀x + A₁₂η`, `η̇ = A₂₂η/ε + L ẋ`); with `P` the Lyapunov
solution of `A₂₂` (`BoundedCertificate`, from LeanForControl's Lyapunov equation):
1. `apriori_le`: `V = |x|² + ηᵀPη` has `V̇ ≤ (K + 1) V` once `ε K ≤ 1`, so `x`, `η` are bounded on
   `[0, T]` uniformly in `ε`;
2. `layer_error_le`: `e = η − η_b`, `η_b(t) = z_b(t/ε)`, has `e(0) = 0` and
   `d/dt (eᵀPe) ≤ −eᵀPe/(2 hi ε) + O(ε)`, so `|e|² = O(ε²)`; `layer_le` bounds `η_b`;
3. `slow_error_le`: `d = x − x̄ − ε A₁₂A₂₂⁻¹ η_b` absorbs the boundary layer
   (`d' = A₀ d + A₀A₁₂A₂₂⁻¹(ε η_b) + A₁₂ e`) and Grönwall gives `|x − x̄|² = O(ε²)`;
4. `z − (h(x̄) + η_b) = e − L (x − x̄)`.
The scalar comparison lemmas (`comparison_of_deriv_le`, `le_of_deriv_le_neg`,
`le_of_deriv_le_pos`) and quadratic-form calculus are generic support.

Model boundary: linear, time invariant, autonomous, constant `ε`, finite horizon `[0, T]`;
deterministic; no inputs. Nonlinear Tikhonov estimates are not claimed here.

Architecture: generic mathematical support (no `Family`, no definitions); every statement is
about arbitrary matrices and their solutions, so the results are public foundation.

Source: work-sync theory/T-tikhonov.md §1.1 (main statement, boundary-layer term),
theory/T-singular-perturbation.md §1.5 (finite-horizon approximation); the linear estimate is
Kokotović–Khalil–O'Reilly (1986) Ch. 2 / Khalil, *Nonlinear Systems*, Thm. 11.1, cited in both
notes.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix Set

/-- Comparison lemma: `f' ≤ k f + β` on `[0, T]` with `k ≠ 0` gives
`f t + β/k ≤ e^{k t} (f 0 + β/k)` on `[0, T]`. -/
@[powerlib_foundation] theorem comparison_of_deriv_le {f f' : ℝ → ℝ} {k β T : ℝ} (hk : k ≠ 0)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t ∈ Icc 0 T, f' t ≤ k * f t + β) :
    ∀ t ∈ Icc 0 T, f t + β / k ≤ Real.exp (k * t) * (f 0 + β / k) := by
  set g : ℝ → ℝ := fun s => Real.exp (-(k * s)) * (f s + β / k) with hg
  have hgd : ∀ s, HasDerivAt g (Real.exp (-(k * s)) * (f' s - k * f s - β)) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (-(k * s))) (Real.exp (-(k * s)) * (-k)) s := by
      have := ((hasDerivAt_id s).const_mul k).neg.exp
      simpa using this
    have h2 := (hf s).add_const (β / k)
    convert h1.mul h2 using 1
    field_simp
    ring
  have hanti : AntitoneOn g (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun s _ => (hgd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hgd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hgd s).deriv]
      have := hb s (Ioo_subset_Icc_self hs)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  intro t ht
  have h := hanti (left_mem_Icc.mpr (le_trans ht.1 ht.2)) ht ht.1
  simp only [g, mul_zero, neg_zero, Real.exp_zero, one_mul] at h
  have := mul_le_mul_of_nonneg_left h (Real.exp_pos (k * t)).le
  rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this

/-- Decay form: `f' ≤ -α f + β` (`α > 0`, `β ≥ 0`) gives `f t ≤ e^{-αt} f 0 + β/α`. -/
@[powerlib_foundation] theorem le_of_deriv_le_neg {f f' : ℝ → ℝ} {α β T : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t ∈ Icc 0 T, f' t ≤ -α * f t + β) :
    ∀ t ∈ Icc 0 T, f t ≤ Real.exp (-α * t) * f 0 + β / α := by
  intro t ht
  have h := comparison_of_deriv_le (neg_ne_zero.mpr hα.ne') hf hb t ht
  have he : 0 < Real.exp (-α * t) := Real.exp_pos _
  have he1 : Real.exp (-α * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [ht.1]
  have hq : 0 ≤ β / α := div_nonneg hβ hα.le
  rw [div_neg] at h
  nlinarith

/-- Growth form: `f' ≤ k f + β` (`k > 0`, `β ≥ 0`) gives `f t ≤ e^{k t} (f 0 + β/k)`. -/
@[powerlib_foundation] theorem le_of_deriv_le_pos {f f' : ℝ → ℝ} {k β T : ℝ} (hk : 0 < k) (hβ : 0 ≤ β)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t ∈ Icc 0 T, f' t ≤ k * f t + β) :
    ∀ t ∈ Icc 0 T, f t ≤ Real.exp (k * t) * (f 0 + β / k) := by
  intro t ht
  have h := comparison_of_deriv_le hk.ne' hf hb t ht
  have hq : 0 ≤ β / k := div_nonneg hβ hk.le
  linarith

/-- `|u + w|² ≤ 2|u|² + 2|w|²`. -/
@[powerlib_foundation] theorem dotProduct_add_self_le {k : Type*} [Fintype k] (u w : k → ℝ) :
    (u + w) ⬝ᵥ (u + w) ≤ 2 * (u ⬝ᵥ u) + 2 * (w ⬝ᵥ w) := by
  have h := dotProduct_self_nonneg' (u - w)
  simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub] at h ⊢
  rw [dotProduct_comm w u] at h ⊢
  linarith

/-- Every entry is bounded by `Σᵢⱼ |Nᵢⱼ|`. -/
@[powerlib_foundation] theorem le_absSum {k l : Type*} [Fintype k] [Fintype l] (N : Matrix k l ℝ) (i : k) (j : l) :
    |N i j| ≤ absSum N := by
  unfold absSum
  calc |N i j| ≤ ∑ j', |N i j'| :=
        Finset.single_le_sum (f := fun j' => |N i j'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |N i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |N i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- `|N v|² ≤ |N|₁² |v|²`. -/
@[powerlib_foundation] theorem mulVec_dotProduct_self_le {k l : Type*} [Fintype k] [Fintype l]
    (N : Matrix k l ℝ) (v : l → ℝ) :
    (N *ᵥ v) ⬝ᵥ (N *ᵥ v) ≤ absSum N ^ 2 * (v ⬝ᵥ v) := by
  rcases (absSum_nonneg N).eq_or_lt with h0 | hpos
  · have hN : N = 0 := by
      ext i j
      have := le_absSum N i j
      rw [← h0] at this
      simpa using le_antisymm this (abs_nonneg _)
    simp only [hN, zero_mulVec, zero_dotProduct]
    exact mul_nonneg (sq_nonneg _) (dotProduct_self_nonneg' v)
  · have h := abs_dotProduct_mulVec_le N (N *ᵥ v) v (inv_pos.mpr hpos)
    have e : absSum N * ((absSum N)⁻¹ * ((N *ᵥ v) ⬝ᵥ (N *ᵥ v)) + (v ⬝ᵥ v) / (absSum N)⁻¹) / 2 =
        ((N *ᵥ v) ⬝ᵥ (N *ᵥ v) + absSum N ^ 2 * (v ⬝ᵥ v)) / 2 := by
      field_simp
    rw [e] at h
    linarith [le_abs_self ((N *ᵥ v) ⬝ᵥ (N *ᵥ v))]

/-- Derivative of `yᵀ P y` for symmetric `P`: `2 yᵀ P ẏ`. -/
@[powerlib_foundation] theorem hasDerivAt_quadratic_of_symm {k : ℕ} {P : Matrix (Fin k) (Fin k) ℝ} (hP : Pᵀ = P)
    {y : ℝ → Fin k → ℝ} {dy : Fin k → ℝ} {t : ℝ} (hy : HasDerivAt y dy t) :
    HasDerivAt (fun s => y s ⬝ᵥ (P *ᵥ y s)) (2 * (y t ⬝ᵥ (P *ᵥ dy))) t := by
  convert hasDerivAt_quadratic P hy using 1
  rw [dotProduct_mulVec_comm_of_symm hP dy (y t)]
  ring

/-- Derivative of `|y|²`: `2 yᵀ ẏ`. -/
@[powerlib_foundation] theorem hasDerivAt_dotProduct_self {k : ℕ} {y : ℝ → Fin k → ℝ} {dy : Fin k → ℝ} {t : ℝ}
    (hy : HasDerivAt y dy t) :
    HasDerivAt (fun s => y s ⬝ᵥ y s) (2 * (y t ⬝ᵥ dy)) t := by
  have := hasDerivAt_quadratic_of_symm (P := (1 : Matrix (Fin k) (Fin k) ℝ)) (by simp) hy
  simpa using this


variable {n m : ℕ}

/-- The quadratic form of a bounded Lyapunov certificate is nonnegative. -/
@[powerlib_foundation] theorem quadratic_nonneg {A22 : Matrix (Fin m) (Fin m) ℝ} (c : BoundedCertificate A22)
    (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ (c.P *ᵥ v) :=
  le_trans (mul_nonneg c.lower_pos.le (dotProduct_self_nonneg' v)) (c.lower_bound v)

/-- The energy derivative of the a-priori estimate. -/
@[powerlib_foundation] theorem growth_deriv_le {A0 : Matrix (Fin n) (Fin n) ℝ} {A12 : Matrix (Fin n) (Fin m) ℝ}
    {L : Matrix (Fin m) (Fin n) ℝ} {A22 : Matrix (Fin m) (Fin m) ℝ} (c : BoundedCertificate A22)
    {ε : ℝ} (hε : 0 < ε)
    (hεk : ε * (2 * (absSum A0 + absSum A12 + absSum (c.P * L * A0) +
      absSum (c.P * L * A12))) ≤ 1) (x : Fin n → ℝ) (η : Fin m → ℝ) :
    2 * (x ⬝ᵥ (A0 *ᵥ x + A12 *ᵥ η)) +
        2 * (η ⬝ᵥ (c.P *ᵥ (ε⁻¹ • (A22 *ᵥ η) + L *ᵥ (A0 *ᵥ x + A12 *ᵥ η)))) ≤
      (2 * (absSum A0 + absSum A12 + absSum (c.P * L * A0) + absSum (c.P * L * A12)) + 1) *
        (x ⬝ᵥ x + η ⬝ᵥ (c.P *ᵥ η)) + 0 := by
  set K := 2 * (absSum A0 + absSum A12 + absSum (c.P * L * A0) + absSum (c.P * L * A12))
    with hK
  have hP := c.symmetric
  have hlyap : c.P * A22 + A22ᵀ * c.P = -1 := by rw [add_comm]; exact c.lyapunov
  have a0 := absSum_nonneg A0
  have a12 := absSum_nonneg A12
  have n1 := absSum_nonneg (c.P * L * A0)
  have n2 := absSum_nonneg (c.P * L * A12)
  have hK0 : 0 ≤ K := by positivity
  have hKε : K ≤ ε⁻¹ := by
    rw [← one_div, le_div_iff₀ hε]; linarith [mul_comm ε K]
  have e1 : x ⬝ᵥ (A0 *ᵥ x + A12 *ᵥ η) = x ⬝ᵥ (A0 *ᵥ x) + x ⬝ᵥ (A12 *ᵥ η) :=
    dotProduct_add _ _ _
  have e2 : η ⬝ᵥ (c.P *ᵥ (ε⁻¹ • (A22 *ᵥ η) + L *ᵥ (A0 *ᵥ x + A12 *ᵥ η))) =
      ε⁻¹ * (η ⬝ᵥ (c.P *ᵥ (A22 *ᵥ η))) + η ⬝ᵥ ((c.P * L * A0) *ᵥ x) +
        η ⬝ᵥ ((c.P * L * A12) *ᵥ η) := by
    simp only [Matrix.mul_assoc, ← mulVec_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    ring
  have hl := dotProduct_mulVec_lyapunov hP hlyap η
  have b1 := le_of_abs_le (abs_dotProduct_mulVec_le A0 x x one_pos)
  have b2 := le_of_abs_le (abs_dotProduct_mulVec_le A12 x η one_pos)
  have b3 := le_of_abs_le (abs_dotProduct_mulVec_le (c.P * L * A0) η x one_pos)
  have b4 := le_of_abs_le (abs_dotProduct_mulVec_le (c.P * L * A12) η η one_pos)
  simp only [one_mul, div_one] at b1 b2 b3 b4
  have hX := dotProduct_self_nonneg' x
  have hY := dotProduct_self_nonneg' η
  have hQ := quadratic_nonneg c η
  have hKY : K * (η ⬝ᵥ η) ≤ ε⁻¹ * (η ⬝ᵥ η) := mul_le_mul_of_nonneg_right hKε hY
  rw [e1, e2, hl]
  have hsum : 2 * (x ⬝ᵥ (A0 *ᵥ x) + x ⬝ᵥ (A12 *ᵥ η)) +
      2 * (ε⁻¹ * (-(η ⬝ᵥ η) / 2) + η ⬝ᵥ ((c.P * L * A0) *ᵥ x) +
        η ⬝ᵥ ((c.P * L * A12) *ᵥ η)) ≤ K * (x ⬝ᵥ x) + K * (η ⬝ᵥ η) - ε⁻¹ * (η ⬝ᵥ η) := by
    rw [hK]; nlinarith
  have hKX : K * (x ⬝ᵥ x) ≤ (K + 1) * (x ⬝ᵥ x + η ⬝ᵥ (c.P *ᵥ η)) := by nlinarith
  linarith


/-- Derivative of `N y(t)`. -/
@[powerlib_foundation] theorem hasDerivAt_mulVec {k l : ℕ} (N : Matrix (Fin k) (Fin l) ℝ) {y : ℝ → Fin l → ℝ}
    {dy : Fin l → ℝ} {t : ℝ} (hy : HasDerivAt y dy t) :
    HasDerivAt (fun s => N *ᵥ y s) (N *ᵥ dy) t :=
  (LinearMap.toContinuousLinearMap (Matrix.toLin' N)).hasFDerivAt.comp_hasDerivAt t hy

/-- `|a v|² = a² |v|²`. -/
@[powerlib_foundation] theorem smul_dotProduct_smul_self {k : Type*} [Fintype k] (a : ℝ) (v : k → ℝ) :
    (a • v) ⬝ᵥ (a • v) = a ^ 2 * (v ⬝ᵥ v) := by
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Boundary-layer error: `e = η - η_b` with `ė = A₂₂e/ε + L(A₀x + A₁₂η)`, `e(0) = 0`, and
`|x|², |η|² ≤ R` on `[0, T]` give `|e|² ≤ 4 (hi/lo) S (S+1) R ε²`. -/
@[powerlib_foundation] theorem layer_error_le {A0 : Matrix (Fin n) (Fin n) ℝ} {A12 : Matrix (Fin n) (Fin m) ℝ}
    {L : Matrix (Fin m) (Fin n) ℝ} {A22 : Matrix (Fin m) (Fin m) ℝ} (c : BoundedCertificate A22)
    {ε R T : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    {x : ℝ → Fin n → ℝ} {η e : ℝ → Fin m → ℝ}
    (he : ∀ t, HasDerivAt e (ε⁻¹ • (A22 *ᵥ e t) + L *ᵥ (A0 *ᵥ x t + A12 *ᵥ η t)) t)
    (he0 : e 0 = 0)
    (hxR : ∀ t ∈ Icc 0 T, x t ⬝ᵥ x t ≤ R) (hηR : ∀ t ∈ Icc 0 T, η t ⬝ᵥ η t ≤ R) :
    ∀ t ∈ Icc 0 T, e t ⬝ᵥ e t ≤
      4 * (c.upper / c.lower) * (absSum (c.P * L * A0) + absSum (c.P * L * A12)) *
        (absSum (c.P * L * A0) + absSum (c.P * L * A12) + 1) * R * ε ^ 2 := by
  set n1 := absSum (c.P * L * A0) with hn1d
  set n2 := absSum (c.P * L * A12) with hn2d
  set S := n1 + n2 with hS
  have hn1 : 0 ≤ n1 := absSum_nonneg _
  have hn2 : 0 ≤ n2 := absSum_nonneg _
  have hS0 : 0 ≤ S := add_nonneg hn1 hn2
  have hP := c.symmetric
  have hlyap : c.P * A22 + A22ᵀ * c.P = -1 := by rw [add_comm]; exact c.lyapunov
  have hlo := c.lower_pos
  have hhi := c.upper_pos
  set δ := ε⁻¹ / (2 * (S + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set α := ε⁻¹ / (2 * c.upper) with hα
  have hαpos : 0 < α := by positivity
  set β := 2 * S * (S + 1) * R * ε with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hV : ∀ s, HasDerivAt (fun s => e s ⬝ᵥ (c.P *ᵥ e s))
      (2 * (e s ⬝ᵥ (c.P *ᵥ (ε⁻¹ • (A22 *ᵥ e s) + L *ᵥ (A0 *ᵥ x s + A12 *ᵥ η s))))) s :=
    fun s => hasDerivAt_quadratic_of_symm hP (he s)
  have k1 : S * δ ≤ ε⁻¹ / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
    nlinarith
  have k2 : δ⁻¹ = 2 * (S + 1) * ε := by
    rw [hδ, inv_div, div_inv_eq_mul]
  have hb : ∀ s ∈ Icc 0 T,
      2 * (e s ⬝ᵥ (c.P *ᵥ (ε⁻¹ • (A22 *ᵥ e s) + L *ᵥ (A0 *ᵥ x s + A12 *ᵥ η s)))) ≤
        -α * (e s ⬝ᵥ (c.P *ᵥ e s)) + β := by
    intro s hs
    have e2 : e s ⬝ᵥ (c.P *ᵥ (ε⁻¹ • (A22 *ᵥ e s) + L *ᵥ (A0 *ᵥ x s + A12 *ᵥ η s))) =
        ε⁻¹ * (e s ⬝ᵥ (c.P *ᵥ (A22 *ᵥ e s))) + e s ⬝ᵥ ((c.P * L * A0) *ᵥ x s) +
          e s ⬝ᵥ ((c.P * L * A12) *ᵥ η s) := by
      simp only [Matrix.mul_assoc, ← mulVec_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [e2, dotProduct_mulVec_lyapunov hP hlyap]
    have b1 := le_of_abs_le (abs_dotProduct_mulVec_le (c.P * L * A0) (e s) (x s) hδpos)
    have b2 := le_of_abs_le (abs_dotProduct_mulVec_le (c.P * L * A12) (e s) (η s) hδpos)
    rw [← hn1d] at b1
    rw [← hn2d] at b2
    have hE := dotProduct_self_nonneg' (e s)
    have hup := c.upper_bound (e s)
    have hx := hxR s hs
    have hη := hηR s hs
    have h1 : S * δ * (e s ⬝ᵥ e s) ≤ ε⁻¹ / 2 * (e s ⬝ᵥ e s) := mul_le_mul_of_nonneg_right k1 hE
    have hxd : (x s ⬝ᵥ x s) / δ ≤ R * δ⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hx (inv_pos.mpr hδpos).le
    have hηd : (η s ⬝ᵥ η s) / δ ≤ R * δ⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hη (inv_pos.mpr hδpos).le
    have h2 : n1 * ((x s ⬝ᵥ x s) / δ) ≤ n1 * (R * δ⁻¹) := mul_le_mul_of_nonneg_left hxd hn1
    have h3 : n2 * ((η s ⬝ᵥ η s) / δ) ≤ n2 * (R * δ⁻¹) := mul_le_mul_of_nonneg_left hηd hn2
    have h4 : α * (e s ⬝ᵥ (c.P *ᵥ e s)) ≤ ε⁻¹ / 2 * (e s ⬝ᵥ e s) := by
      calc α * (e s ⬝ᵥ (c.P *ᵥ e s)) ≤ α * (c.upper * (e s ⬝ᵥ e s)) :=
            mul_le_mul_of_nonneg_left hup hαpos.le
        _ = ε⁻¹ / 2 * (e s ⬝ᵥ e s) := by rw [hα]; field_simp
    have h5 : (n1 + n2) * (R * δ⁻¹) = β := by rw [k2, hβ, hS]; ring
    have h6 : S * δ * (e s ⬝ᵥ e s) = n1 * δ * (e s ⬝ᵥ e s) + n2 * δ * (e s ⬝ᵥ e s) := by
      rw [hS]; ring
    nlinarith
  have hdec := le_of_deriv_le_neg hαpos hβ0 hV hb
  intro t ht
  have h := hdec t ht
  rw [he0, mulVec_zero, dotProduct_zero, mul_zero, zero_add] at h
  have hlow := c.lower_bound (e t)
  have hβα : β / α = 4 * c.upper * S * (S + 1) * R * ε ^ 2 := by
    rw [hβ, hα]; field_simp; ring
  rw [hβα] at h
  have hfin : 4 * (c.upper / c.lower) * S * (S + 1) * R * ε ^ 2 =
      (4 * c.upper * S * (S + 1) * R * ε ^ 2) / c.lower := by field_simp
  rw [hfin, le_div_iff₀ hlo]
  nlinarith

/-- Slow error with the boundary-layer correction `ε A₁₂A₂₂⁻¹ η_b` removed. -/
@[powerlib_foundation] theorem slow_error_le {A0 : Matrix (Fin n) (Fin n) ℝ} {A12 : Matrix (Fin n) (Fin m) ℝ}
    {A22 : Matrix (Fin m) (Fin m) ℝ} (hA22 : IsUnit A22.det)
    {ε Rb E T : ℝ} (hε : 0 < ε) (hRb : 0 ≤ Rb) (hE : 0 ≤ E)
    {x xbar : ℝ → Fin n → ℝ} {η ηb : ℝ → Fin m → ℝ}
    (hx : ∀ t, HasDerivAt x (A0 *ᵥ x t + A12 *ᵥ η t) t)
    (hxbar : ∀ t, HasDerivAt xbar (A0 *ᵥ xbar t) t) (h0 : xbar 0 = x 0)
    (hηb : ∀ t, HasDerivAt ηb (ε⁻¹ • (A22 *ᵥ ηb t)) t)
    (hbR : ∀ t ∈ Icc 0 T, ηb t ⬝ᵥ ηb t ≤ Rb)
    (heE : ∀ t ∈ Icc 0 T, (η t - ηb t) ⬝ᵥ (η t - ηb t) ≤ E) :
    ∀ t ∈ Icc 0 T, (x t - xbar t) ⬝ᵥ (x t - xbar t) ≤
      2 * Real.exp ((2 * absSum A0 + absSum (A0 * (A12 * A22⁻¹)) + absSum A12 + 1) * t) *
        (ε ^ 2 * absSum (A12 * A22⁻¹) ^ 2 * Rb +
          (absSum (A0 * (A12 * A22⁻¹)) * ε ^ 2 * Rb + absSum A12 * E) /
            (2 * absSum A0 + absSum (A0 * (A12 * A22⁻¹)) + absSum A12 + 1)) +
        2 * (ε ^ 2 * absSum (A12 * A22⁻¹) ^ 2 * Rb) := by
  set G := A12 * A22⁻¹ with hG
  set a0 := absSum A0
  set a0g := absSum (A0 * G) with ha0g
  set a12 := absSum A12 with ha12
  set g := absSum G with hg
  set k := 2 * a0 + a0g + a12 + 1 with hk
  have ha0 : 0 ≤ a0 := absSum_nonneg _
  have ha0g0 : 0 ≤ a0g := absSum_nonneg _
  have ha120 : 0 ≤ a12 := absSum_nonneg _
  have hkpos : 0 < k := by positivity
  have hGA : G * A22 = A12 := by
    rw [hG, Matrix.mul_assoc, nonsing_inv_mul _ hA22, Matrix.mul_one]
  set d : ℝ → Fin n → ℝ := fun s => x s - xbar s - ε • (G *ᵥ ηb s) with hd
  have hdd : ∀ s, HasDerivAt d
      (A0 *ᵥ d s + (A0 * G) *ᵥ (ε • ηb s) + A12 *ᵥ (η s - ηb s)) s := by
    intro s
    have h := ((hx s).sub (hxbar s)).sub ((hasDerivAt_mulVec G (hηb s)).const_smul ε)
    convert h using 1
    have : ε • (G *ᵥ (ε⁻¹ • (A22 *ᵥ ηb s))) = A12 *ᵥ ηb s := by
      rw [mulVec_smul, smul_smul, mul_inv_cancel₀ hε.ne', one_smul, mulVec_mulVec, hGA]
    rw [this]
    simp only [hd, mulVec_sub, mulVec_smul, ← mulVec_mulVec]
    abel
  set β := a0g * ε ^ 2 * Rb + a12 * E with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hW : ∀ s, HasDerivAt (fun s => d s ⬝ᵥ d s)
      (2 * (d s ⬝ᵥ (A0 *ᵥ d s + (A0 * G) *ᵥ (ε • ηb s) + A12 *ᵥ (η s - ηb s)))) s :=
    fun s => hasDerivAt_dotProduct_self (hdd s)
  have hb : ∀ s ∈ Icc 0 T,
      2 * (d s ⬝ᵥ (A0 *ᵥ d s + (A0 * G) *ᵥ (ε • ηb s) + A12 *ᵥ (η s - ηb s))) ≤
        k * (d s ⬝ᵥ d s) + β := by
    intro s hs
    rw [dotProduct_add, dotProduct_add]
    have b1 := le_of_abs_le (abs_dotProduct_mulVec_le A0 (d s) (d s) one_pos)
    have b2 := le_of_abs_le (abs_dotProduct_mulVec_le (A0 * G) (d s) (ε • ηb s) one_pos)
    have b3 := le_of_abs_le (abs_dotProduct_mulVec_le A12 (d s) (η s - ηb s) one_pos)
    simp only [one_mul, div_one] at b1 b2 b3
    rw [smul_dotProduct_smul_self, ← ha0g] at b2
    rw [← ha12] at b3
    have hD := dotProduct_self_nonneg' (d s)
    have hb1 := hbR s hs
    have he1 := heE s hs
    have t1 : a0g * (ε ^ 2 * (ηb s ⬝ᵥ ηb s)) ≤ a0g * (ε ^ 2 * Rb) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 (by positivity)) ha0g0
    have t2 : a12 * ((η s - ηb s) ⬝ᵥ (η s - ηb s)) ≤ a12 * E :=
      mul_le_mul_of_nonneg_left he1 ha120
    nlinarith
  have hgrow := le_of_deriv_le_pos hkpos hβ0 hW hb
  intro t ht
  have h := hgrow t ht
  have hd0 : d 0 ⬝ᵥ d 0 ≤ ε ^ 2 * g ^ 2 * Rb := by
    have : d 0 = -(ε • (G *ᵥ ηb 0)) := by simp [hd, h0]
    rw [this, neg_dotProduct, dotProduct_neg, neg_neg, ← mulVec_smul]
    calc (G *ᵥ (ε • ηb 0)) ⬝ᵥ (G *ᵥ (ε • ηb 0)) ≤ g ^ 2 * ((ε • ηb 0) ⬝ᵥ (ε • ηb 0)) :=
          mulVec_dotProduct_self_le G _
      _ = g ^ 2 * (ε ^ 2 * (ηb 0 ⬝ᵥ ηb 0)) := by rw [smul_dotProduct_smul_self]
      _ ≤ g ^ 2 * (ε ^ 2 * Rb) := by
          gcongr
          exact hbR 0 ⟨le_rfl, le_trans ht.1 ht.2⟩
      _ = ε ^ 2 * g ^ 2 * Rb := by ring
  have hcorr : (ε • (G *ᵥ ηb t)) ⬝ᵥ (ε • (G *ᵥ ηb t)) ≤ ε ^ 2 * g ^ 2 * Rb := by
    rw [smul_dotProduct_smul_self]
    calc ε ^ 2 * ((G *ᵥ ηb t) ⬝ᵥ (G *ᵥ ηb t)) ≤ ε ^ 2 * (g ^ 2 * (ηb t ⬝ᵥ ηb t)) := by
          gcongr; exact mulVec_dotProduct_self_le G _
      _ ≤ ε ^ 2 * (g ^ 2 * Rb) := by gcongr; exact hbR t ht
      _ = ε ^ 2 * g ^ 2 * Rb := by ring
  have hsplit : x t - xbar t = d t + ε • (G *ᵥ ηb t) := by simp [hd]
  have hadd := dotProduct_add_self_le (d t) (ε • (G *ᵥ ηb t))
  rw [← hsplit] at hadd
  have hexp : 0 ≤ Real.exp (k * t) := (Real.exp_pos _).le
  have hW0 : Real.exp (k * t) * (d 0 ⬝ᵥ d 0 + β / k) ≤
      Real.exp (k * t) * (ε ^ 2 * g ^ 2 * Rb + β / k) := by gcongr
  linarith


/-- The a-priori bound on `[0, T]`: `|x|², |η|² ≤ e^{(K+1)T} V(0) (1 + 1/lo)`. -/
@[powerlib_foundation] theorem apriori_le {A0 : Matrix (Fin n) (Fin n) ℝ} {A12 : Matrix (Fin n) (Fin m) ℝ}
    {L : Matrix (Fin m) (Fin n) ℝ} {A22 : Matrix (Fin m) (Fin m) ℝ} (c : BoundedCertificate A22)
    {ε : ℝ} (hε : 0 < ε)
    (hεk : ε * (2 * (absSum A0 + absSum A12 + absSum (c.P * L * A0) +
      absSum (c.P * L * A12))) ≤ 1)
    {x : ℝ → Fin n → ℝ} {η : ℝ → Fin m → ℝ}
    (hx : ∀ t, HasDerivAt x (A0 *ᵥ x t + A12 *ᵥ η t) t)
    (hη : ∀ t, HasDerivAt η (ε⁻¹ • (A22 *ᵥ η t) + L *ᵥ (A0 *ᵥ x t + A12 *ᵥ η t)) t)
    {T V0 : ℝ} (hV0 : x 0 ⬝ᵥ x 0 + η 0 ⬝ᵥ (c.P *ᵥ η 0) ≤ V0) :
    ∀ t ∈ Icc 0 T, x t ⬝ᵥ x t ≤ Real.exp ((2 * (absSum A0 + absSum A12 +
        absSum (c.P * L * A0) + absSum (c.P * L * A12)) + 1) * T) * V0 * (1 + 1 / c.lower) ∧
      η t ⬝ᵥ η t ≤ Real.exp ((2 * (absSum A0 + absSum A12 +
        absSum (c.P * L * A0) + absSum (c.P * L * A12)) + 1) * T) * V0 * (1 + 1 / c.lower) := by
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * (absSum A0 + absSum A12 + absSum (c.P * L * A0) +
      absSum (c.P * L * A12)) := ⟨_, rfl⟩
  rw [← hK] at hεk ⊢
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := absSum_nonneg A0; have := absSum_nonneg A12
    have := absSum_nonneg (c.P * L * A0); have := absSum_nonneg (c.P * L * A12)
    positivity
  have hlo := c.lower_pos
  have hVd : ∀ s, HasDerivAt (fun s => x s ⬝ᵥ x s + η s ⬝ᵥ (c.P *ᵥ η s))
      (2 * (x s ⬝ᵥ (A0 *ᵥ x s + A12 *ᵥ η s)) +
        2 * (η s ⬝ᵥ (c.P *ᵥ (ε⁻¹ • (A22 *ᵥ η s) + L *ᵥ (A0 *ᵥ x s + A12 *ᵥ η s))))) s :=
    fun s => (hasDerivAt_dotProduct_self (hx s)).add
      (hasDerivAt_quadratic_of_symm c.symmetric (hη s))
  have hgrowth := le_of_deriv_le_pos (T := T) (by positivity : (0 : ℝ) < K + 1) le_rfl hVd
    (fun s _ => by
      have := growth_deriv_le c hε (by rw [← hK]; exact hεk) (x s) (η s)
      rwa [← hK] at this)
  intro s hs
  have hgs := hgrowth s hs
  rw [zero_div, add_zero] at hgs
  have hV00 : 0 ≤ x 0 ⬝ᵥ x 0 + η 0 ⬝ᵥ (c.P *ᵥ η 0) :=
    add_nonneg (dotProduct_self_nonneg' _) (quadratic_nonneg c _)
  have he : Real.exp ((K + 1) * s) ≤ Real.exp ((K + 1) * T) :=
    Real.exp_le_exp.mpr (by nlinarith [hs.2])
  have hVs : x s ⬝ᵥ x s + η s ⬝ᵥ (c.P *ᵥ η s) ≤ Real.exp ((K + 1) * T) * V0 :=
    hgs.trans (mul_le_mul he hV0 hV00 (Real.exp_pos _).le)
  have hq := quadratic_nonneg c (η s)
  have hxs := dotProduct_self_nonneg' (x s)
  have hlow := c.lower_bound (η s)
  obtain ⟨W, hW⟩ : ∃ W, W = Real.exp ((K + 1) * T) * V0 := ⟨_, rfl⟩
  rw [← hW] at hVs ⊢
  have hW0 : 0 ≤ W := by linarith
  have hWl : 0 ≤ W * (1 / c.lower) := by positivity
  constructor
  · nlinarith
  · have hηs : η s ⬝ᵥ η s ≤ W / c.lower := by
      rw [le_div_iff₀ hlo]; nlinarith
    have : W / c.lower ≤ W * (1 + 1 / c.lower) := by
      rw [mul_add, mul_one, mul_one_div]; linarith
    linarith

/-- Decay of the boundary layer in the original time: `|η_b(t)|² ≤ (hi/lo) |η_b(0)|²`. -/
@[powerlib_foundation] theorem layer_le {A22 : Matrix (Fin m) (Fin m) ℝ} (c : BoundedCertificate A22) {ε T : ℝ}
    (hε : 0 < ε) {ηb : ℝ → Fin m → ℝ} (hηb : ∀ t, HasDerivAt ηb (ε⁻¹ • (A22 *ᵥ ηb t)) t) :
    ∀ t ∈ Icc 0 T, ηb t ⬝ᵥ ηb t ≤ c.upper / c.lower * (ηb 0 ⬝ᵥ ηb 0) := by
  have hP := c.symmetric
  have hlyap : c.P * A22 + A22ᵀ * c.P = -1 := by rw [add_comm]; exact c.lyapunov
  have hlo := c.lower_pos
  have hhi := c.upper_pos
  have hV : ∀ s, HasDerivAt (fun s => ηb s ⬝ᵥ (c.P *ᵥ ηb s))
      (2 * (ηb s ⬝ᵥ (c.P *ᵥ (ε⁻¹ • (A22 *ᵥ ηb s))))) s :=
    fun s => hasDerivAt_quadratic_of_symm hP (hηb s)
  have hα : 0 < ε⁻¹ / c.upper := by positivity
  have hdec := le_of_deriv_le_neg (T := T) hα le_rfl hV (fun s _ => by
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul, dotProduct_mulVec_lyapunov hP hlyap]
    have hup := c.upper_bound (ηb s)
    have h1 : ε⁻¹ / c.upper * (ηb s ⬝ᵥ (c.P *ᵥ ηb s)) ≤ ε⁻¹ * (ηb s ⬝ᵥ ηb s) := by
      calc ε⁻¹ / c.upper * (ηb s ⬝ᵥ (c.P *ᵥ ηb s)) ≤ ε⁻¹ / c.upper * (c.upper * (ηb s ⬝ᵥ ηb s)) :=
            mul_le_mul_of_nonneg_left hup hα.le
        _ = ε⁻¹ * (ηb s ⬝ᵥ ηb s) := by field_simp
    linarith)
  intro t ht
  have h := hdec t ht
  rw [zero_div, add_zero] at h
  have hexp : Real.exp (-(ε⁻¹ / c.upper) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  have hq := quadratic_nonneg c (ηb 0)
  have hlow := c.lower_bound (ηb t)
  have hup0 := c.upper_bound (ηb 0)
  have h2 : ηb t ⬝ᵥ (c.P *ᵥ ηb t) ≤ c.upper * (ηb 0 ⬝ᵥ ηb 0) := by nlinarith [Real.exp_pos (-(ε⁻¹ / c.upper) * t)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlo]
  linarith


/-- Arithmetic of the final slow estimate. -/
@[powerlib_foundation] theorem slow_combine {D ε N0 t T kC g a0g a12 Rb0 Ce : ℝ} (hkC : 0 < kC) (ht : t ≤ T)
    (hN : 0 ≤ ε ^ 2 * N0) (hRb : 0 ≤ Rb0) (ha0g : 0 ≤ a0g) (ha12 : 0 ≤ a12) (hCe : 0 ≤ Ce)
    (h : D ≤ 2 * Real.exp (kC * t) * (ε ^ 2 * g ^ 2 * (Rb0 * N0) +
        (a0g * ε ^ 2 * (Rb0 * N0) + a12 * (Ce * (ε ^ 2 * N0))) / kC) +
        2 * (ε ^ 2 * g ^ 2 * (Rb0 * N0))) :
    D ≤ (2 * Real.exp (kC * T) * (g ^ 2 * Rb0 + (a0g * Rb0 + a12 * Ce) / kC) +
      2 * (g ^ 2 * Rb0)) * (ε ^ 2 * N0) := by
  have hid : 2 * Real.exp (kC * t) * (ε ^ 2 * g ^ 2 * (Rb0 * N0) +
      (a0g * ε ^ 2 * (Rb0 * N0) + a12 * (Ce * (ε ^ 2 * N0))) / kC) +
      2 * (ε ^ 2 * g ^ 2 * (Rb0 * N0)) =
      (2 * Real.exp (kC * t) * (g ^ 2 * Rb0 + (a0g * Rb0 + a12 * Ce) / kC) +
        2 * (g ^ 2 * Rb0)) * (ε ^ 2 * N0) := by
    ring
  rw [hid] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hN)
  have hexp : Real.exp (kC * t) ≤ Real.exp (kC * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hkC.le)
  have : 0 ≤ g ^ 2 * Rb0 + (a0g * Rb0 + a12 * Ce) / kC := by positivity
  nlinarith

namespace LinearSP

variable (sp : LinearSP n m)

/-- Slow/fast coordinates `η = z + L x`: the full system reads
`ẋ = A₀x + A₁₂η`, `η̇ = A₂₂η/ε + L(A₀x + A₁₂η)`. -/
@[powerlib_foundation] theorem coords_hasDerivAt (hU : IsUnit sp.A22.det) {ε : ℝ} {x : ℝ → Fin n → ℝ}
    {z : ℝ → Fin m → ℝ} (hx : ∀ t, HasDerivAt x (sp.A11 *ᵥ x t + sp.A12 *ᵥ z t) t)
    (hz : ∀ t, HasDerivAt z (ε⁻¹ • (sp.A21 *ᵥ x t + sp.A22 *ᵥ z t)) t) (t : ℝ) :
    HasDerivAt x (sp.reducedMatrix *ᵥ x t + sp.A12 *ᵥ (z t + sp.gain *ᵥ x t)) t ∧
      HasDerivAt (fun s => z s + sp.gain *ᵥ x s)
        (ε⁻¹ • (sp.A22 *ᵥ (z t + sp.gain *ᵥ x t)) +
          sp.gain *ᵥ (sp.reducedMatrix *ᵥ x t + sp.A12 *ᵥ (z t + sp.gain *ᵥ x t))) t := by
  have hslow : sp.A11 *ᵥ x t + sp.A12 *ᵥ z t =
      sp.reducedMatrix *ᵥ x t + sp.A12 *ᵥ (z t + sp.gain *ᵥ x t) := by
    simp only [reducedMatrix, gain, mulVec_add, sub_mulVec, ← mulVec_mulVec, Matrix.mul_assoc]
    abel
  have hAL : sp.A22 *ᵥ (sp.gain *ᵥ x t) = sp.A21 *ᵥ x t := by
    rw [mulVec_mulVec, gain, ← Matrix.mul_assoc, mul_nonsing_inv _ hU, Matrix.one_mul]
  have hx' : HasDerivAt x (sp.reducedMatrix *ᵥ x t + sp.A12 *ᵥ (z t + sp.gain *ᵥ x t)) t := by
    rw [← hslow]; exact hx t
  refine ⟨hx', ?_⟩
  have h := (hz t).add (hasDerivAt_mulVec sp.gain hx')
  rw [mulVec_add, hAL, add_comm (sp.A22 *ᵥ z t)]
  exact h

/-- **Finite-horizon `O(ε)` approximation** (Tikhonov's theorem, linear case). -/
@[powerlib_foundation] theorem exists_finiteHorizon_error (hA22 : LinearSystems.IsHurwitz sp.A22) (T : ℝ) :
    ∃ ε₀ > 0, ∃ C : ℝ, ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ (x : ℝ → Fin n → ℝ) (z : ℝ → Fin m → ℝ) (xbar : ℝ → Fin n → ℝ)
        (zb : ℝ → Fin m → ℝ),
      (∀ t, HasDerivAt x (sp.A11 *ᵥ x t + sp.A12 *ᵥ z t) t) →
      (∀ t, HasDerivAt z (ε⁻¹ • (sp.A21 *ᵥ x t + sp.A22 *ᵥ z t)) t) →
      (∀ t, HasDerivAt xbar (sp.reducedMatrix *ᵥ xbar t) t) → xbar 0 = x 0 →
      (∀ τ, HasDerivAt zb (sp.A22 *ᵥ zb τ) τ) → zb 0 = z 0 + sp.gain *ᵥ x 0 →
      ∀ t ∈ Icc 0 T,
        (x t - xbar t) ⬝ᵥ (x t - xbar t) ≤ C * ε ^ 2 * (x 0 ⬝ᵥ x 0 + z 0 ⬝ᵥ z 0) ∧
        (z t - (-(sp.gain *ᵥ xbar t) + zb (t / ε))) ⬝ᵥ
            (z t - (-(sp.gain *ᵥ xbar t) + zb (t / ε))) ≤
          C * ε ^ 2 * (x 0 ⬝ᵥ x 0 + z 0 ⬝ᵥ z 0) := by
  obtain ⟨c⟩ := nonempty_boundedCertificate_of_isHurwitz hA22
  have hU := isUnit_det_of_isHurwitz hA22
  have hlo := c.lower_pos
  have hhi := c.upper_pos
  -- constants, all independent of `ε`
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * (absSum sp.reducedMatrix + absSum sp.A12 +
      absSum (c.P * sp.gain * sp.reducedMatrix) + absSum (c.P * sp.gain * sp.A12)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := absSum_nonneg sp.reducedMatrix; have := absSum_nonneg sp.A12
    have := absSum_nonneg (c.P * sp.gain * sp.reducedMatrix)
    have := absSum_nonneg (c.P * sp.gain * sp.A12)
    positivity
  obtain ⟨l, hl⟩ : ∃ l, l = absSum sp.gain := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := hl ▸ absSum_nonneg _
  obtain ⟨S, hS⟩ : ∃ S, S = absSum (c.P * sp.gain * sp.reducedMatrix) +
      absSum (c.P * sp.gain * sp.A12) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]; exact add_nonneg (absSum_nonneg _) (absSum_nonneg _)
  obtain ⟨g, hg⟩ : ∃ g, g = absSum (sp.A12 * sp.A22⁻¹) := ⟨_, rfl⟩
  obtain ⟨a0g, ha0g⟩ : ∃ a, a = absSum (sp.reducedMatrix * (sp.A12 * sp.A22⁻¹)) := ⟨_, rfl⟩
  obtain ⟨a12, ha12⟩ : ∃ a, a = absSum sp.A12 := ⟨_, rfl⟩
  obtain ⟨kC, hkC⟩ : ∃ k, k = 2 * absSum sp.reducedMatrix +
      absSum (sp.reducedMatrix * (sp.A12 * sp.A22⁻¹)) + absSum sp.A12 + 1 := ⟨_, rfl⟩
  have ha0g0 : 0 ≤ a0g := ha0g ▸ absSum_nonneg _
  have ha120 : 0 ≤ a12 := ha12 ▸ absSum_nonneg _
  have hkC0 : 0 < kC := by
    rw [hkC, ← ha0g, ← ha12]; have := absSum_nonneg sp.reducedMatrix; positivity
  obtain ⟨c1, hc1⟩ : ∃ c1, c1 = 2 * (1 + l ^ 2) := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  obtain ⟨R0, hR0⟩ : ∃ R, R = Real.exp ((K + 1) * T) * ((1 + c.upper * c1)) *
      (1 + 1 / c.lower) := ⟨_, rfl⟩
  have hR00 : 0 ≤ R0 := by rw [hR0]; positivity
  obtain ⟨Rb0, hRb0⟩ : ∃ R, R = c.upper / c.lower * c1 := ⟨_, rfl⟩
  have hRb00 : 0 ≤ Rb0 := by rw [hRb0]; positivity
  obtain ⟨Ce, hCe⟩ : ∃ C, C = 4 * (c.upper / c.lower) * S * (S + 1) * R0 := ⟨_, rfl⟩
  have hCe0 : 0 ≤ Ce := by rw [hCe]; positivity
  obtain ⟨Cx, hCx⟩ : ∃ C, C = 2 * Real.exp (kC * T) * (g ^ 2 * Rb0 +
      (a0g * Rb0 + a12 * Ce) / kC) + 2 * (g ^ 2 * Rb0) := ⟨_, rfl⟩
  have hCx0 : 0 ≤ Cx := by rw [hCx]; positivity
  obtain ⟨Cz, hCz⟩ : ∃ C, C = 2 * Ce + 2 * l ^ 2 * Cx := ⟨_, rfl⟩
  refine ⟨1 / (K + 1), by positivity, max Cx Cz, ?_⟩
  intro ε hε hεle x z xbar zb hx hz hxbar h0 hzb hzb0 t ht
  obtain ⟨N0, hN0⟩ : ∃ N, N = x 0 ⬝ᵥ x 0 + z 0 ⬝ᵥ z 0 := ⟨_, rfl⟩
  rw [← hN0]
  have hN00 : 0 ≤ N0 := hN0 ▸ add_nonneg (dotProduct_self_nonneg' _) (dotProduct_self_nonneg' _)
  have hεK : ε * K ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hεle
    nlinarith
  have hε2N : 0 ≤ ε ^ 2 * N0 := by positivity
  -- slow/fast coordinates `η = z + L x`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ → Fin m → ℝ, η = fun s => z s + sp.gain *ᵥ x s := ⟨_, rfl⟩
  have hηs : ∀ s, η s = z s + sp.gain *ᵥ x s := fun s => by rw [hηdef]
  have hxη : ∀ s, HasDerivAt x (sp.reducedMatrix *ᵥ x s + sp.A12 *ᵥ η s) s := fun s => by
    rw [hηs]; exact (sp.coords_hasDerivAt hU hx hz s).1
  have hη : ∀ s, HasDerivAt η (ε⁻¹ • (sp.A22 *ᵥ η s) +
      sp.gain *ᵥ (sp.reducedMatrix *ᵥ x s + sp.A12 *ᵥ η s)) s := fun s => by
    rw [hηs, hηdef]; exact (sp.coords_hasDerivAt hU hx hz s).2
  -- the boundary layer in the original time
  obtain ⟨ηb, hηbdef⟩ : ∃ ηb : ℝ → Fin m → ℝ, ηb = fun s => zb (s / ε) := ⟨_, rfl⟩
  have hηb : ∀ s, HasDerivAt ηb (ε⁻¹ • (sp.A22 *ᵥ ηb s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s / ε) (1 / ε) s := (hasDerivAt_id s).div_const ε
    have h2 := (hzb (s / ε)).scomp s h1
    rw [hηbdef, one_div] at *
    exact h2
  have hηb0 : ηb 0 = η 0 := by
    rw [hηs, hηbdef]; simp only [zero_div, hzb0]
  -- initial sizes
  have hη0 : η 0 ⬝ᵥ η 0 ≤ c1 * N0 := by
    have h1 := dotProduct_add_self_le (z 0) (sp.gain *ᵥ x 0)
    have h2 := mulVec_dotProduct_self_le sp.gain (x 0)
    rw [← hl] at h2
    rw [← hηs] at h1
    have hx0 := dotProduct_self_nonneg' (x 0)
    have hz0 := dotProduct_self_nonneg' (z 0)
    have h3 : l ^ 2 * (z 0 ⬝ᵥ z 0) ≥ 0 := by positivity
    have h4 : c1 * N0 = 2 * (x 0 ⬝ᵥ x 0) + 2 * (z 0 ⬝ᵥ z 0) + 2 * (l ^ 2 * (x 0 ⬝ᵥ x 0)) +
        2 * (l ^ 2 * (z 0 ⬝ᵥ z 0)) := by rw [hc1, hN0]; ring
    linarith
  have hV0 : x 0 ⬝ᵥ x 0 + η 0 ⬝ᵥ (c.P *ᵥ η 0) ≤ (1 + c.upper * c1) * N0 := by
    have h1 := c.upper_bound (η 0)
    have h2 : c.upper * (η 0 ⬝ᵥ η 0) ≤ c.upper * (c1 * N0) :=
      mul_le_mul_of_nonneg_left hη0 hhi.le
    have hz0 := dotProduct_self_nonneg' (z 0)
    have h3 : x 0 ⬝ᵥ x 0 ≤ N0 := by rw [hN0]; linarith
    have h4 : (1 + c.upper * c1) * N0 = N0 + c.upper * (c1 * N0) := by ring
    linarith
  -- a-priori bound
  have hapr := apriori_le c hε (by rw [← hK]; exact hεK) hxη hη (T := T) hV0
  rw [← hK] at hapr
  have hRR : Real.exp ((K + 1) * T) * ((1 + c.upper * c1) * N0) * (1 + 1 / c.lower) =
      R0 * N0 := by rw [hR0]; ring
  rw [hRR] at hapr
  -- the boundary-layer error
  obtain ⟨e, hedef⟩ : ∃ e : ℝ → Fin m → ℝ, e = fun s => η s - ηb s := ⟨_, rfl⟩
  have he : ∀ s, HasDerivAt e (ε⁻¹ • (sp.A22 *ᵥ e s) +
      sp.gain *ᵥ (sp.reducedMatrix *ᵥ x s + sp.A12 *ᵥ η s)) s := by
    intro s
    have h := (hη s).sub (hηb s)
    rw [hedef]
    convert h using 1
    simp only [mulVec_sub, smul_sub]
    abel
  have he0 : e 0 = 0 := by rw [hedef]; simp [hηb0]
  have hlay := layer_error_le c hε (mul_nonneg hR00 hN00) he he0
    (fun s hs => (hapr s hs).1) (fun s hs => (hapr s hs).2)
  rw [← hS] at hlay
  have hEE : 4 * (c.upper / c.lower) * S * (S + 1) * (R0 * N0) * ε ^ 2 = Ce * (ε ^ 2 * N0) := by
    rw [hCe]; ring
  rw [hEE] at hlay
  -- boundary-layer size
  have hbl := layer_le c (T := T) hε hηb
  have hbR : ∀ s ∈ Icc 0 T, ηb s ⬝ᵥ ηb s ≤ Rb0 * N0 := by
    intro s hs
    have h := hbl s hs
    rw [hηb0] at h
    have : c.upper / c.lower * (η 0 ⬝ᵥ η 0) ≤ c.upper / c.lower * (c1 * N0) :=
      mul_le_mul_of_nonneg_left hη0 (by positivity)
    rw [hRb0]
    linarith
  -- slow error
  have hslow := slow_error_le hU hε (mul_nonneg hRb00 hN00)
    (mul_nonneg hCe0 hε2N) hxη hxbar h0 hηb hbR
    (fun s hs => by have := hlay s hs; rwa [hedef] at this) t ht
  rw [← hkC, ← hg, ← ha0g, ← ha12] at hslow
  have hX : (x t - xbar t) ⬝ᵥ (x t - xbar t) ≤ Cx * (ε ^ 2 * N0) := by
    rw [hCx]
    exact slow_combine hkC0 ht.2 hε2N hRb00 ha0g0 ha120 hCe0 hslow
  -- fast error: `z - (h(x̄) + η_b) = e - L (x - x̄)`
  have hZ : (z t - (-(sp.gain *ᵥ xbar t) + zb (t / ε))) ⬝ᵥ
      (z t - (-(sp.gain *ᵥ xbar t) + zb (t / ε))) ≤ Cz * (ε ^ 2 * N0) := by
    have hsplit : z t - (-(sp.gain *ᵥ xbar t) + zb (t / ε)) =
        e t + (-(sp.gain *ᵥ (x t - xbar t))) := by
      have h1 : e t = η t - ηb t := by rw [hedef]
      have h2 : ηb t = zb (t / ε) := by rw [hηbdef]
      rw [h1, h2, hηs, mulVec_sub]
      abel
    rw [hsplit]
    have h1 := dotProduct_add_self_le (e t) (-(sp.gain *ᵥ (x t - xbar t)))
    have h2 := mulVec_dotProduct_self_le sp.gain (x t - xbar t)
    rw [neg_dotProduct, dotProduct_neg, neg_neg] at h1
    rw [← hl] at h2
    have h3 := hlay t ht
    have h4 : l ^ 2 * ((x t - xbar t) ⬝ᵥ (x t - xbar t)) ≤ l ^ 2 * (Cx * (ε ^ 2 * N0)) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have h5 : Cz * (ε ^ 2 * N0) = 2 * (Ce * (ε ^ 2 * N0)) + 2 * (l ^ 2 * (Cx * (ε ^ 2 * N0))) := by
      rw [hCz]; ring
    linarith
  have hm1 : Cx * (ε ^ 2 * N0) ≤ max Cx Cz * ε ^ 2 * N0 := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hε2N
  have hm2 : Cz * (ε ^ 2 * N0) ≤ max Cx Cz * ε ^ 2 * N0 := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hε2N
  exact ⟨hX.trans hm1, hZ.trans hm2⟩

end LinearSP

end powerlib.SingularPerturbation
