import theorem.Network.Synchronization
import theorem.Hurwitz

/-! # Linear node networks: exponential synchronization ⇔ transverse blocks Hurwitz

Foundation layer (category B).

Source: work-sync `theory/T-synchronization-manifold.md` §1.3 (variational equation decoupled by
the Laplacian spectrum), §1.4–§1.5 (synchronization ⇔ every transverse mode `k ≥ 2` stable; for
linear nodes the Master Stability Function reduces to the Hurwitz property of
`A − σ μ_k Γ`).

Model boundary: `N` identical linear nodes `ẋᵢ = A xᵢ − σ Σⱼ Lᵢⱼ Γ xⱼ` (`xᵢ ∈ ℝᵈ`), constant
matrices, symmetric coupling matrix `L` with an orthonormal eigenbasis `V` (`L V = V diag μ`,
`V Vᵀ = I`) one of whose columns (`k₀`, the synchronous mode, `μ_{k₀} = 0` for a Laplacian) is
constant; continuous time. Synchronization is measured by the pairwise differences in the
Euclidean norm.

Result (`expSync_iff`): the network synchronizes exponentially (uniformly over all solutions,
`‖xᵢ(t) − xⱼ(t)‖ ≤ K e^{−rt} Σₗ ‖xₗ(0)‖`) iff `A − σ μ_k Γ` is Hurwitz for every transverse
mode `k ≠ k₀`. Together with `transverse_isHurwitz_of_threshold` (`Γ = I`) this gives the
threshold `σ μ₂ > a`.
-/

noncomputable section
namespace powerlib.Network.Sync
open Matrix Finset

variable {N d : ℕ}

/-- Linear network field `Fᵢ(X) = A Xᵢ − σ Σⱼ Lᵢⱼ Γ Xⱼ`. -/
def linNetField (A Γ : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin N) (Fin N) ℝ) (σ : ℝ)
    (X : Fin N → Fin d → ℝ) : Fin N → Fin d → ℝ :=
  fun i => A *ᵥ X i - σ • ∑ j, L i j • (Γ *ᵥ X j)

/-- Global solution of the linear network. -/
def IsNetSolution (A Γ : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin N) (Fin N) ℝ) (σ : ℝ)
    (X : ℝ → Fin N → Fin d → ℝ) : Prop :=
  ∀ t, HasDerivAt X (linNetField A Γ L σ (X t)) t

/-- Uniform exponential synchronization. -/
def ExpSync (A Γ : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin N) (Fin N) ℝ) (σ : ℝ) : Prop :=
  ∃ K > 0, ∃ r > 0, ∀ X, IsNetSolution A Γ L σ X → ∀ t, 0 ≤ t → ∀ i j,
    ‖LTI.euclidean (X t i - X t j)‖ ≤ K * Real.exp (-(r * t)) * ∑ l, ‖LTI.euclidean (X 0 l)‖

/-- Orthonormal eigenbasis of the coupling matrix with a constant (synchronous) column `k₀`. -/
structure SpectralData (L : Matrix (Fin N) (Fin N) ℝ) where
  V : Matrix (Fin N) (Fin N) ℝ
  μ : Fin N → ℝ
  k0 : Fin N
  eig : L * V = V * diagonal μ
  orth : V * Vᵀ = 1
  const : ∀ i j, V i k0 = V j k0

/-! ## Euclidean-norm helpers -/

@[powerlib_foundation] theorem euclidean_sub (x y : Fin d → ℝ) :
    LTI.euclidean (x - y) = LTI.euclidean x - LTI.euclidean y := rfl

@[powerlib_foundation] theorem euclidean_smul (c : ℝ) (x : Fin d → ℝ) :
    LTI.euclidean (c • x) = c • LTI.euclidean x := rfl

@[powerlib_foundation] theorem euclidean_sum {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℝ) :
    LTI.euclidean (∑ k ∈ s, f k) = ∑ k ∈ s, LTI.euclidean (f k) := by
  simp [LTI.euclidean]

@[powerlib_foundation] theorem norm_euclidean_sum_smul_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → Fin d → ℝ) :
    ‖LTI.euclidean (∑ k ∈ s, c k • f k)‖ ≤ ∑ k ∈ s, |c k| * ‖LTI.euclidean (f k)‖ := by
  rw [euclidean_sum]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [euclidean_smul, norm_smul, Real.norm_eq_abs]

/-! ## Spectral facts -/

namespace SpectralData

variable {L : Matrix (Fin N) (Fin N) ℝ} (D : SpectralData L)

@[powerlib_foundation] theorem orth' : D.Vᵀ * D.V = 1 := mul_eq_one_comm.mp D.orth

@[powerlib_foundation] theorem col_eig (i k : Fin N) : ∑ j, L i j * D.V j k = D.μ k * D.V i k := by
  have := congrFun (congrFun D.eig i) k
  rw [mul_apply, mul_diagonal] at this
  rw [this, mul_comm]

@[powerlib_foundation] theorem colsq (k : Fin N) : ∑ i, D.V i k ^ 2 = 1 := by
  have := congrFun (congrFun D.orth' k) k
  simpa [mul_apply, one_apply_eq, sq] using this

@[powerlib_foundation] theorem colorth {k l : Fin N} (h : k ≠ l) : ∑ i, D.V i k * D.V i l = 0 := by
  have := congrFun (congrFun D.orth' k) l
  simpa [mul_apply, one_apply_ne h] using this

@[powerlib_foundation] theorem abs_le_one (i k : Fin N) : |D.V i k| ≤ 1 := by
  have h := D.colsq k
  have hle : D.V i k ^ 2 ≤ 1 := by
    rw [← h]; exact Finset.single_le_sum (fun j _ => sq_nonneg (D.V j k)) (Finset.mem_univ i)
  exact (sq_le_one_iff_abs_le_one _).mp hle

/-- A transverse column is not constant. -/
@[powerlib_foundation] theorem exists_ne {k : Fin N} (hk : k ≠ D.k0) :
    ∃ i j, D.V i k ≠ D.V j k := by
  by_contra hcon
  push Not at hcon
  have hc : ∀ i, D.V i k = D.V D.k0 k := fun i => hcon i D.k0
  have hc0 : ∀ i, D.V i D.k0 = D.V D.k0 D.k0 := fun i => D.const i D.k0
  have horth := D.colorth hk
  simp only [hc, hc0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at horth
  have hsq0 := D.colsq D.k0
  simp only [hc0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsq0
  have hsqk := D.colsq k
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsqk
  have hN : (N : ℝ) ≠ 0 := by intro h; rw [h, zero_mul] at hsq0; exact zero_ne_one hsq0
  have hv0 : D.V D.k0 D.k0 ≠ 0 := by intro h; rw [h] at hsq0; simp at hsq0
  have : D.V D.k0 k = 0 := by
    rcases mul_eq_zero.mp horth with h | h
    · exact absurd h hN
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hv0
  rw [this] at hsqk
  simp at hsqk

end SpectralData

/-! ## The equivalence -/

/-- **Linear network synchronization**: exponential synchronization ⇔ every transverse block
`A − σ μ_k Γ` (`k ≠ k₀`) is Hurwitz. -/
@[powerlib_foundation] theorem expSync_iff {A Γ : Matrix (Fin d) (Fin d) ℝ}
    {L : Matrix (Fin N) (Fin N) ℝ} (hL : Lᵀ = L) (D : SpectralData L) (σ : ℝ) :
    ExpSync A Γ L σ ↔ ∀ k, k ≠ D.k0 → LinearSystems.IsHurwitz (A - (σ * D.μ k) • Γ) := by
  constructor
  · -- a transverse trajectory lifts to a network solution
    rintro ⟨K, hK, r, hr, hsync⟩ k hk
    apply LTI.isHurwitz_of_exponentiallyStable (m := ⟨A - (σ * D.μ k) • Γ⟩)
    obtain ⟨i₀, j₀, hij⟩ := D.exists_ne hk
    have hdpos : 0 < |D.V i₀ k - D.V j₀ k| := abs_pos.mpr (sub_ne_zero.mpr hij)
    set S := ∑ l, |D.V l k|
    have hS : 0 ≤ S := Finset.sum_nonneg fun l _ => abs_nonneg _
    refine ⟨K * (S + 1) / |D.V i₀ k - D.V j₀ k|, by positivity, r, hr, fun y hy t ht => ?_⟩
    set X : ℝ → Fin N → Fin d → ℝ := fun τ i => D.V i k • y τ
    have hX : IsNetSolution A Γ L σ X := by
      intro τ
      refine hasDerivAt_pi.mpr fun i => ?_
      have hyt := (hy τ).const_smul (D.V i k)
      convert hyt using 1
      simp only [linNetField, X, LTI.AutonomousModel.field, generated.linearField_spec,
        mulVec_smul, smul_smul]
      have : ∑ j, (L i j * D.V j k) • Γ *ᵥ y τ = (D.μ k * D.V i k) • Γ *ᵥ y τ := by
        rw [← Finset.sum_smul, D.col_eig i k]
      rw [this, sub_mulVec, smul_mulVec, smul_sub, smul_smul, smul_smul]
      congr 2
      ring
    have hb := hsync X hX t ht i₀ j₀
    simp only [X, ← sub_smul, euclidean_smul, norm_smul, Real.norm_eq_abs] at hb
    have hsum : ∑ l, |D.V l k| * ‖LTI.euclidean (y 0)‖ = S * ‖LTI.euclidean (y 0)‖ := by
      rw [← Finset.sum_mul]
    rw [hsum] at hb
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hdpos]
    calc ‖LTI.euclidean (y t)‖ * |D.V i₀ k - D.V j₀ k|
        = |D.V i₀ k - D.V j₀ k| * ‖LTI.euclidean (y t)‖ := mul_comm _ _
      _ ≤ K * Real.exp (-(r * t)) * (S * ‖LTI.euclidean (y 0)‖) := hb
      _ ≤ K * (S + 1) * Real.exp (-(r * t)) * ‖LTI.euclidean (y 0)‖ := by
          have h0 := mul_nonneg (mul_nonneg hK.le (Real.exp_pos (-(r * t))).le)
            (norm_nonneg (LTI.euclidean (y 0)))
          have : K * (S + 1) * Real.exp (-(r * t)) * ‖LTI.euclidean (y 0)‖ =
              K * Real.exp (-(r * t)) * (S * ‖LTI.euclidean (y 0)‖) +
                K * Real.exp (-(r * t)) * ‖LTI.euclidean (y 0)‖ := by ring
          linarith
  · -- modal decomposition and uniform constants
    intro hH
    have hW : D.Vᵀ * L = diagonal D.μ * D.Vᵀ := by
      have := congrArg transpose D.eig
      rwa [transpose_mul, transpose_mul, hL, diagonal_transpose] at this
    -- per-mode exponential stability
    have hstab : ∀ k, k ≠ D.k0 → LTI.ExponentiallyStable ⟨A - (σ * D.μ k) • Γ⟩ :=
      fun k hk => LTI.exponentiallyStable_of_isHurwitz (m := ⟨A - (σ * D.μ k) • Γ⟩) (hH k hk)
    choose! Kf hKf rf hrf hbound using hstab
    have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨D.k0, Finset.mem_univ _⟩
    set r := Finset.univ.inf' hne (fun k => if k = D.k0 then 1 else rf k)
    have hr : 0 < r := by
      rw [Finset.lt_inf'_iff]
      intro k _
      split_ifs with h
      · exact one_pos
      · exact hrf k h
    have hrle : ∀ k, k ≠ D.k0 → r ≤ rf k := by
      intro k hk
      have := Finset.inf'_le (fun k => if k = D.k0 then 1 else rf k) (Finset.mem_univ k)
      simpa [hk] using this
    set K := ∑ k, 2 * (if k = D.k0 then 1 else Kf k) + 1
    have hKpos : 0 < K := by
      have : 0 ≤ ∑ k, 2 * (if k = D.k0 then 1 else Kf k) := Finset.sum_nonneg fun k _ => by
        split_ifs with h
        · norm_num
        · exact (mul_pos two_pos (hKf k h)).le
      linarith
    refine ⟨K, hKpos, r, hr, fun X hX t ht i j => ?_⟩
    -- modal coordinates
    set ξ : ℝ → Fin N → Fin d → ℝ := fun τ k => ∑ l, D.Vᵀ k l • X τ l
    have hξ : ∀ k, k ≠ D.k0 → LTI.IsTrajectory ⟨A - (σ * D.μ k) • Γ⟩ (fun τ => ξ τ k) := by
      intro k hk τ
      have := variational_decouple hW σ (fun _ => A) (fun _ => Γ) (δX := X) hX τ
      have := (hasDerivAt_pi.mp this) k
      simpa [LTI.AutonomousModel.field, generated.linearField_spec, ξ] using this
    -- reconstruction `Xᵢ = Σₖ Vᵢₖ ξₖ`
    have hrec : ∀ τ i, X τ i = ∑ k, D.V i k • ξ τ k := by
      intro τ i
      simp only [ξ, Finset.smul_sum, smul_smul, transpose_apply]
      rw [Finset.sum_comm]
      have : ∀ l, ∑ k, D.V i k * D.V l k = if i = l then 1 else 0 := by
        intro l
        have := congrFun (congrFun D.orth i) l
        simpa [mul_apply, one_apply] using this
      simp only [← Finset.sum_smul, this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
    have hdiff : X t i - X t j = ∑ k, (D.V i k - D.V j k) • ξ t k := by
      rw [hrec t i, hrec t j, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => (sub_smul _ _ _).symm
    -- bound each transverse mode
    have hmode : ∀ k, |D.V i k - D.V j k| * ‖LTI.euclidean (ξ t k)‖ ≤
        2 * (if k = D.k0 then 1 else Kf k) * Real.exp (-(r * t)) *
          ∑ l, ‖LTI.euclidean (X 0 l)‖ := by
      intro k
      by_cases hk : k = D.k0
      · rw [hk, D.const i j, sub_self, abs_zero, zero_mul]
        simp only [↓reduceIte]
        positivity
      · have h1 := hbound k hk _ (hξ k hk) t ht
        have h2 : ‖LTI.euclidean (ξ 0 k)‖ ≤ ∑ l, ‖LTI.euclidean (X 0 l)‖ := by
          refine (norm_euclidean_sum_smul_le _ _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          have := D.abs_le_one l k
          simp only [transpose_apply]
          nlinarith [norm_nonneg (LTI.euclidean (X 0 l))]
        have h3 : |D.V i k - D.V j k| ≤ 2 := by
          have := D.abs_le_one i k; have := D.abs_le_one j k
          calc |D.V i k - D.V j k| ≤ |D.V i k| + |D.V j k| := abs_sub _ _
            _ ≤ 2 := by linarith
        have h4 : Real.exp (-(rf k * t)) ≤ Real.exp (-(r * t)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hrle k hk]
        simp only [hk, ↓reduceIte]
        have hKk := hKf k hk
        have hn0 := norm_nonneg (LTI.euclidean (ξ t k))
        have hS0 : 0 ≤ ∑ l, ‖LTI.euclidean (X 0 l)‖ :=
          Finset.sum_nonneg fun l _ => norm_nonneg _
        calc |D.V i k - D.V j k| * ‖LTI.euclidean (ξ t k)‖
            ≤ 2 * (Kf k * Real.exp (-(rf k * t)) * ‖LTI.euclidean (ξ 0 k)‖) := by
              apply mul_le_mul h3 h1 hn0 (by norm_num)
          _ ≤ 2 * (Kf k * Real.exp (-(r * t)) * ∑ l, ‖LTI.euclidean (X 0 l)‖) := by
              gcongr
          _ = 2 * Kf k * Real.exp (-(r * t)) * ∑ l, ‖LTI.euclidean (X 0 l)‖ := by ring
    rw [hdiff]
    calc ‖LTI.euclidean (∑ k, (D.V i k - D.V j k) • ξ t k)‖
        ≤ ∑ k, |D.V i k - D.V j k| * ‖LTI.euclidean (ξ t k)‖ :=
          norm_euclidean_sum_smul_le _ _ _
      _ ≤ ∑ k, 2 * (if k = D.k0 then 1 else Kf k) * Real.exp (-(r * t)) *
            ∑ l, ‖LTI.euclidean (X 0 l)‖ := Finset.sum_le_sum fun k _ => hmode k
      _ = (∑ k, 2 * (if k = D.k0 then 1 else Kf k)) * Real.exp (-(r * t)) *
            ∑ l, ‖LTI.euclidean (X 0 l)‖ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ K * Real.exp (-(r * t)) * ∑ l, ‖LTI.euclidean (X 0 l)‖ := by
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun l _ => norm_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          simp only [K]; linarith

end powerlib.Network.Sync
