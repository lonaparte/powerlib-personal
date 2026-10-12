import theorem.DAE.Linear
import theorem.Linear.Stability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Method of lines: the 1-D heat Laplacian, stencils, boundary closures, port coupling

Foundation layer (category B).

Source: work-sync `theory/T-method-of-lines.md` §1.2 + §1.2.1 (central-difference MoL of
`u_t = ν u_xx` with Dirichlet data, tridiagonal `T`, eigenvalues `−4 sin²(kπ/2N)`, stiffness
ratio `O(N²)`), §1.4.1 (stencil table), §1.7.2 (Neumann ghost cell / one-sided closure), §1.7.4
(port coupling ⇒ DAE), §2.3 (Cauer RC chain = lumped 1-D heat MoL).

Model boundary.
* Grid `x_j = jΔx`, `j = 0, …, N`, `N = M + 1`, `Δx = ℓ/N`; the `M` interior values
  `(u₁, …, u_M)` are the state (index `j : Fin M` is node `j + 1`), Dirichlet values at nodes
  `0` and `N`. `lapT M` is the `M × M` tridiagonal matrix `tridiag(1, −2, 1)`;
  `heatMOL ν Δx M` is the state matrix `(ν/Δx²) T` of the zero-Dirichlet autonomous model
  `u̇ = (ν/Δx²) T u` (continuous time; inhomogeneous boundary data enter as an additive input and
  do not affect stability).
* Statements concern the semi-discrete system only; no claim of convergence to the PDE.

Results.
* `lapT_mulVec_eigvec`: `T vₖ = μₖ vₖ`, `(vₖ)_j = sin((j+1)kπ/N)`, `μₖ = −4 sin²(kπ/2N)`;
  `eigenvalue_lapT`: every complex eigenvalue of `T` is one of `μ₁, …, μ_M` (the `M`
  eigenvectors have distinct eigenvalues, so no further eigenvalue fits in dimension `M`);
  `lapT_isHurwitz`, `heatMOL_exponentiallyStable` (`ν > 0`; global exponential stability of the
  linear field `u ↦ (ν/Δx²) T u` in the Flow semantics, formerly `LTI.ExponentiallyStable`).
* `stiffness_ratio_bounds`: `|μ_M|/|μ₁| = cot²(π/2N)` lies in `[2N²/π², 4N²/π²]` (`N ≥ 2`).
* Stencils (`T-method-of-lines` §1.4.1): exactness on polynomials of the stated degree and a
  monomial of the next degree on which each stencil fails, i.e. the precise polynomial order.
  Correction: the second-order upwind stencil `(3u_j − 4u_{j−1} + u_{j−2})/(2Δx)` listed in the
  "fourth-order" column is only second order (`upwind2_cubic`: error `−2Δx²` on `x³`).
* Ghost cell (`§1.7.2`). Correction: the central closure is `(u₁ − u₋₁)/(2Δx) = h`, i.e.
  `u₋₁ = u₁ − 2Δx h` (`ghost_iff`), not `(u₁ − u₀)/(2Δx) = h`: the latter quotient tends to
  `u'(0)/2` (`note_ghost_tendsto`), so it would impose `u'(0) = 2h`. The one-sided closure
  `u₀ = (4u₁ − u₂ − 2Δx h)/3` is correct and exact on quadratics.
* `cauer_eq_mol`: a uniform Cauer RC chain (`C = ρc_p AΔx`, `R = Δx/(κA)`) has exactly the MoL
  dynamics `Ṫ_j = (κ/ρc_p)(T_{j+1} − 2T_j + T_{j−1})/Δx²`.
* `portCoupled_isSolution_iff`: interior MoL ODE + linear port constraint
  `0 = G_x x + G_b u_bnd + G_e u_ext` is an index-1 DAE when `det G_b ≠ 0` (one-to-one with the
  Schur-reduced ODE; `theorem.DAE.Linear`).

No family: every result is a foundation of the discretization (category B), all public foundation
as before. The only change of statement is `heatMOL`, now the state matrix itself, with
stability concluded in the Flow semantics through the linear hub
(`Linear.globallyExponentiallyStable_of_isHurwitz`).
-/

noncomputable section
namespace powerlib.Line.MethodOfLines
open Matrix Finset Real

/-! ## The tridiagonal heat Laplacian -/

/-- `tridiag(1, −2, 1)` on the `M` interior nodes. -/
def lapT (M : ℕ) : Matrix (Fin M) (Fin M) ℝ := fun i j =>
  if (j : ℕ) = i then -2 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 1 else 0

/-- Extension of an interior vector to all grid nodes `0, …, N` by the zero Dirichlet values:
node `k` carries `w_{k−1}` for `1 ≤ k ≤ M`, and `0` otherwise. -/
def gridExt {M : ℕ} (w : Fin M → ℝ) (k : ℕ) : ℝ :=
  if h : 1 ≤ k ∧ k ≤ M then w ⟨k - 1, by omega⟩ else 0

private lemma sum_shift {M : ℕ} (w : Fin M → ℝ) (k : ℕ) :
    ∑ j : Fin M, (if (j : ℕ) + 1 = k then w j else 0) = gridExt w k := by
  unfold gridExt
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · simp; omega
    · intro b _ hb
      have hbk : ¬ ((b : ℕ) + 1 = k) := by intro hbk; apply hb; ext; simp; omega
      simp only [hbk]; simp
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have hjk : ¬ ((j : ℕ) + 1 = k) := by omega
    simp only [hjk]; simp

/-- `(T w)_j = w_{j−1} − 2w_j + w_{j+1}` with the Dirichlet zeros. -/
@[powerlib_foundation] theorem lapT_mulVec_apply {M : ℕ} (w : Fin M → ℝ) (i : Fin M) :
    (lapT M *ᵥ w) i = gridExt w i - 2 * gridExt w (i + 1) + gridExt w (i + 2) := by
  have hsplit : ∀ j : Fin M, lapT M i j * w j =
      -2 * (if j = i then w j else 0) + (if (j : ℕ) + 1 = i then w j else 0) +
        (if (j : ℕ) + 1 = (i : ℕ) + 2 then w j else 0) := by
    intro j
    simp only [lapT]
    by_cases h1 : j = i
    · subst h1; simp
    · have h1' : (j : ℕ) ≠ i := fun h => h1 (Fin.ext h)
      simp only [h1', h1]
      by_cases h2 : (j : ℕ) + 1 = i
      · have h4 : ¬ ((j : ℕ) + 1 = (i : ℕ) + 2) := by omega
        simp only [h2]; simp
      · by_cases h3 : (i : ℕ) + 1 = j
        · have h4 : (j : ℕ) + 1 = (i : ℕ) + 2 := by omega
          simp only [h3, h4]; simp
        · have h4 : ¬ ((j : ℕ) + 1 = (i : ℕ) + 2) := by omega
          simp only [h2, h3, h4]; simp
  simp only [mulVec, dotProduct, hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_shift]
  have : gridExt w ((i : ℕ) + 1) = w i := by
    have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ M := by omega
    unfold gridExt; simp only [hi]; simp
  rw [this]
  ring

/-- A grid function `s` that matches `w` at the interior nodes and vanishes at `0` and `N`. -/
@[powerlib_foundation] theorem lapT_mulVec_of_grid {M : ℕ} (w : Fin M → ℝ) (s : ℕ → ℝ)
    (hs0 : s 0 = 0) (hsN : s (M + 1) = 0) (hw : ∀ j : Fin M, w j = s (j + 1)) (i : Fin M) :
    (lapT M *ᵥ w) i = s i - 2 * s (i + 1) + s (i + 2) := by
  have hg : ∀ k, k ≤ M + 1 → gridExt w k = s k := by
    intro k hk
    unfold gridExt
    split_ifs with h
    · rw [hw]; congr 1; simp; omega
    · rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact hs0.symm
      · have : k = M + 1 := by omega
        rw [this, hsN]
  rw [lapT_mulVec_apply, hg _ (by omega), hg _ (by omega), hg _ (by omega)]

/-- Eigenvector `(vₖ)_j = sin((j+1)kπ/N)`, `N = M + 1`. -/
def eigvec (M k : ℕ) (j : Fin M) : ℝ := Real.sin (((j : ℕ) + 1 : ℝ) * (k * π / (M + 1)))

/-- Eigenvalue `μₖ = −4 sin²(kπ/2N)`. -/
def eigval (M k : ℕ) : ℝ := -4 * Real.sin (k * π / (2 * (M + 1))) ^ 2

@[powerlib_foundation] theorem lapT_mulVec_eigvec (M k : ℕ) :
    lapT M *ᵥ eigvec M k = eigval M k • eigvec M k := by
  set θ : ℝ := k * π / (M + 1) with hθ
  funext i
  rw [lapT_mulVec_of_grid (eigvec M k) (fun n => Real.sin (n * θ)) (by simp) ?_ ?_ i]
  · simp only [Pi.smul_apply, smul_eq_mul, eigvec, eigval]
    push_cast
    have hs : Real.sin (((i : ℕ) : ℝ) * θ) + Real.sin (((i : ℕ) + 2 : ℝ) * θ) =
        2 * Real.sin (((i : ℕ) + 1 : ℝ) * θ) * Real.cos θ := by
      have h1 : (((i : ℕ) : ℝ)) * θ = ((i : ℕ) + 1 : ℝ) * θ - θ := by ring
      have h2 : (((i : ℕ) + 2 : ℝ)) * θ = ((i : ℕ) + 1 : ℝ) * θ + θ := by ring
      rw [h1, h2, Real.sin_sub, Real.sin_add]; ring
    have hc : Real.cos θ = 1 - 2 * Real.sin (k * π / (2 * (M + 1))) ^ 2 := by
      have : θ = 2 * (k * π / (2 * (M + 1))) := by rw [hθ]; field_simp
      rw [this, Real.cos_two_mul, Real.cos_sq']; ring
    rw [← hθ]
    linear_combination hs + (2 * Real.sin (((i : ℕ) + 1 : ℝ) * θ)) * hc
  · simp only [Nat.cast_add, Nat.cast_one]
    rw [hθ]
    have : ((M : ℝ) + 1) * (k * π / (M + 1)) = (k : ℕ) * π := by field_simp
    rw [this, Real.sin_nat_mul_pi]
  · intro j; simp [eigvec, hθ]

@[powerlib_foundation] theorem eigvec_ne_zero {M k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    eigvec M k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  simp only [eigvec, Pi.zero_apply, Nat.cast_zero, zero_add, one_mul] at h0
  have hpos : 0 < (k : ℝ) * π / (M + 1) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    positivity
  have hlt : (k : ℝ) * π / (M + 1) < π := by
    rw [div_lt_iff₀ (by positivity)]
    have : (k : ℝ) ≤ M := by exact_mod_cast hkM
    nlinarith [Real.pi_pos]
  exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne' h0

@[powerlib_foundation] theorem eigval_neg {M k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    eigval M k < 0 := by
  have hpos : 0 < (k : ℝ) * π / (2 * (M + 1)) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    positivity
  have hlt : (k : ℝ) * π / (2 * (M + 1)) < π := by
    rw [div_lt_iff₀ (by positivity)]
    have : (k : ℝ) ≤ M := by exact_mod_cast hkM
    nlinarith [Real.pi_pos]
  have := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  unfold eigval
  nlinarith [sq_pos_of_pos this]

/-- The eigenvalues `μ₁ > μ₂ > ⋯ > μ_M` are distinct. -/
@[powerlib_foundation] theorem eigval_strictAnti {M : ℕ} {k l : ℕ} (hk1 : 1 ≤ k) (hkl : k < l)
    (hlM : l ≤ M) : eigval M l < eigval M k := by
  have hN : (0 : ℝ) < 2 * (M + 1) := by positivity
  have ha : 0 ≤ (k : ℝ) * π / (2 * (M + 1)) := by positivity
  have hb : (l : ℝ) * π / (2 * (M + 1)) ≤ π / 2 := by
    rw [div_le_iff₀ hN]
    have : (l : ℝ) ≤ M := by exact_mod_cast hlM
    nlinarith [Real.pi_pos]
  have hab : (k : ℝ) * π / (2 * (M + 1)) < (l : ℝ) * π / (2 * (M + 1)) := by
    apply div_lt_div_of_pos_right _ hN
    have : (k : ℝ) < l := by exact_mod_cast hkl
    nlinarith [Real.pi_pos]
  have hsin := Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], by linarith⟩
    ⟨by linarith [Real.pi_pos], hb⟩ hab
  have hpos : 0 < Real.sin ((k : ℝ) * π / (2 * (M + 1))) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      positivity
    · linarith [Real.pi_pos]
  unfold eigval
  nlinarith

/-- **Spectrum of `T`**: every complex eigenvalue of `T` is one of `μ₁, …, μ_M`. -/
@[powerlib_foundation] theorem eigenvalue_lapT {M : ℕ} {lam : ℂ} {x : Fin M → ℂ} (hx : x ≠ 0)
    (heig : (lapT M).map (algebraMap ℝ ℂ) *ᵥ x = lam • x) :
    ∃ k : Fin M, lam = (eigval M (k + 1) : ℂ) := by
  by_contra hne
  push Not at hne
  set f := Matrix.toLin' ((lapT M).map (algebraMap ℝ ℂ))
  let μs : Option (Fin M) → ℂ := fun o => o.elim lam fun k => (eigval M (k + 1) : ℂ)
  let vs : Option (Fin M) → (Fin M → ℂ) :=
    fun o => o.elim x fun k => fun j => (eigvec M (k + 1) j : ℂ)
  have hinj : Function.Injective μs := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exact absurd hab (hne b)
    · exact absurd hab.symm (hne a)
    · simp only [μs, Option.elim, Complex.ofReal_inj] at hab
      congr 1
      by_contra hab'
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab') with h | h
      · exact (eigval_strictAnti (by omega) (by omega) (by omega)).ne' hab
      · exact (eigval_strictAnti (by omega) (by omega) (by omega)).ne hab
  have heigs : ∀ o, Module.End.HasEigenvector f (μs o) (vs o) := by
    intro o
    rcases o with _ | k
    · exact ⟨Module.End.mem_eigenspace_iff.mpr (by
        simp only [f, Matrix.toLin'_apply, vs, μs, Option.elim]; exact heig), hx⟩
    · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · simp only [f, Matrix.toLin'_apply, vs, μs, Option.elim]
        funext i
        have := congrFun (lapT_mulVec_eigvec M (k + 1)) i
        have hmap := (RingHom.map_mulVec (algebraMap ℝ ℂ) (lapT M) (eigvec M (k + 1)) i).symm
        simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [show (fun j => ((eigvec M (k + 1) j : ℝ) : ℂ)) = (algebraMap ℝ ℂ) ∘ eigvec M (k + 1)
          from rfl, hmap, this]
        simp
      · intro h0
        apply eigvec_ne_zero (M := M) (k := k + 1) (by omega) (by omega)
        funext j
        have := congrFun h0 j
        simpa [vs] using this
  have hli := Module.End.eigenvectors_linearIndependent' f μs hinj vs heigs
  have hcard := hli.fintype_card_le_finrank
  simp at hcard

@[powerlib_foundation] theorem lapT_isHurwitz (M : ℕ) : LinearSystems.IsHurwitz (lapT M) := by
  intro lam x hx heig
  obtain ⟨k, rfl⟩ := eigenvalue_lapT hx heig
  simpa using eigval_neg (M := M) (k := k + 1) (by omega) (by omega)

/-- The state matrix of the zero-Dirichlet MoL of `u_t = ν u_xx`: `u̇ = (ν/Δx²) T u`. -/
def heatMOL (ν Δx : ℝ) (M : ℕ) : Matrix (Fin M) (Fin M) ℝ := (ν / Δx ^ 2) • lapT M

@[powerlib_foundation] theorem heatMOL_isHurwitz {ν Δx : ℝ} (hν : 0 < ν) (hΔ : Δx ≠ 0) (M : ℕ) :
    LinearSystems.IsHurwitz (heatMOL ν Δx M) := by
  intro lam x hx heig
  have hc : (0 : ℝ) < ν / Δx ^ 2 := by positivity
  have hc' : ((ν / Δx ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hmap : ((ν / Δx ^ 2) • lapT M).map (algebraMap ℝ ℂ) =
      ((ν / Δx ^ 2 : ℝ) : ℂ) • (lapT M).map (algebraMap ℝ ℂ) := by
    ext i j; simp
  have heig' : (lapT M).map (algebraMap ℝ ℂ) *ᵥ x = (lam / (ν / Δx ^ 2 : ℝ)) • x := by
    have h := heig
    simp only [heatMOL] at h
    rw [hmap, smul_mulVec] at h
    rw [← inv_smul_smul₀ hc' ((lapT M).map (algebraMap ℝ ℂ) *ᵥ x), h, smul_smul,
      ← div_eq_inv_mul]
  obtain ⟨k, hk⟩ := eigenvalue_lapT hx heig'
  have hneg := eigval_neg (M := M) (k := k + 1) (by omega) (by omega)
  have hlam : lam = ((ν / Δx ^ 2 * eigval M (k + 1) : ℝ) : ℂ) := by
    rw [div_eq_iff hc'] at hk
    rw [hk]; push_cast; ring
  rw [hlam, Complex.ofReal_re]
  simpa using mul_neg_of_pos_of_neg hc hneg

/-- The zero-Dirichlet semi-discrete heat equation is globally exponentially stable. -/
@[powerlib_foundation] theorem heatMOL_exponentiallyStable {ν Δx : ℝ} (hν : 0 < ν) (hΔ : Δx ≠ 0)
    (M : ℕ) :
    Flow.GloballyExponentiallyStable (LinearSystems.affineLinearVectorField (heatMOL ν Δx M) 0)
      0 :=
  Linear.globallyExponentiallyStable_of_isHurwitz 0 (heatMOL_isHurwitz hν hΔ M)

/-! ## Stiffness ratio -/

/-- `|μ_M| / |μ₁| = cot²(π/2N)` and `2N²/π² ≤ cot²(π/2N) ≤ 4N²/π²` (`N = M + 1 ≥ 2`). -/
@[powerlib_foundation] theorem stiffness_ratio_bounds {M : ℕ} (hM : 1 ≤ M) :
    eigval M M / eigval M 1 = (Real.cos (π / (2 * (M + 1))) / Real.sin (π / (2 * (M + 1)))) ^ 2 ∧
      2 * ((M : ℝ) + 1) ^ 2 / π ^ 2 ≤ eigval M M / eigval M 1 ∧
      eigval M M / eigval M 1 ≤ 4 * ((M : ℝ) + 1) ^ 2 / π ^ 2 := by
  set x := π / (2 * ((M : ℝ) + 1)) with hx
  have hxpos : 0 < x := by positivity
  have hx4 : x ≤ π / 4 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [Real.pi_pos]
  have hxπ2 : x < π / 2 := by linarith [Real.pi_pos]
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxπ2⟩
  have hM' : Real.sin ((M : ℝ) * π / (2 * (M + 1))) = Real.cos x := by
    rw [← Real.sin_pi_div_two_sub, hx]; congr 1; field_simp; ring
  have h1 : Real.sin ((1 : ℕ) * π / (2 * (M + 1))) = Real.sin x := by rw [hx]; simp
  have hratio : eigval M M / eigval M 1 = (Real.cos x / Real.sin x) ^ 2 := by
    unfold eigval
    rw [hM', h1]
    field_simp
  refine ⟨hratio, ?_, ?_⟩
  · rw [hratio]
    -- `sin x ≤ x` and `cos x ≥ cos(π/4) = √2/2`
    have hsx : Real.sin x ≤ x := Real.sin_le hxpos.le
    have hc4 : Real.cos (π / 4) ≤ Real.cos x :=
      Real.cos_le_cos_of_nonneg_of_le_pi hxpos.le (by linarith [Real.pi_pos]) hx4
    rw [Real.cos_pi_div_four] at hc4
    have hsq2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hcos2 : 1 / 2 ≤ Real.cos x ^ 2 := by
      rw [← hsq2]; exact pow_le_pow_left₀ (by positivity) hc4 2
    have hxval : x ^ 2 = π ^ 2 / (4 * ((M : ℝ) + 1) ^ 2) := by rw [hx]; field_simp; ring
    rw [div_pow, le_div_iff₀ (by positivity)]
    calc 2 * ((M : ℝ) + 1) ^ 2 / π ^ 2 * Real.sin x ^ 2
        ≤ 2 * ((M : ℝ) + 1) ^ 2 / π ^ 2 * x ^ 2 := by
          gcongr
    _ = 1 / 2 := by rw [hxval]; field_simp; ring
    _ ≤ Real.cos x ^ 2 := hcos2
  · rw [hratio]
    -- `x ≤ tan x`, i.e. `cot x ≤ 1/x`
    have htan := Real.le_tan hxpos.le hxπ2
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos] at htan
    have hcot : Real.cos x / Real.sin x ≤ 1 / x := by
      rw [div_le_div_iff₀ hsin hxpos]; linarith
    have hxval : 1 / x = 2 * ((M : ℝ) + 1) / π := by rw [hx]; field_simp
    calc (Real.cos x / Real.sin x) ^ 2 ≤ (1 / x) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hcot 2
    _ = 4 * ((M : ℝ) + 1) ^ 2 / π ^ 2 := by rw [hxval]; ring

/-! ## Finite-difference stencils (§1.4.1) -/

/-- Central first difference. -/
def central1 (u : ℝ → ℝ) (x h : ℝ) : ℝ := (u (x + h) - u (x - h)) / (2 * h)
/-- Fourth-order central first difference. -/
def central1o4 (u : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (-u (x + 2 * h) + 8 * u (x + h) - 8 * u (x - h) + u (x - 2 * h)) / (12 * h)
/-- First-order upwind (`a > 0`). -/
def upwind1 (u : ℝ → ℝ) (x h : ℝ) : ℝ := (u x - u (x - h)) / h
/-- Second-order upwind (`a > 0`). -/
def upwind2 (u : ℝ → ℝ) (x h : ℝ) : ℝ := (3 * u x - 4 * u (x - h) + u (x - 2 * h)) / (2 * h)
/-- Central second difference. -/
def central2 (u : ℝ → ℝ) (x h : ℝ) : ℝ := (u (x + h) - 2 * u x + u (x - h)) / h ^ 2
/-- Fourth-order central second difference. -/
def central2o4 (u : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (-u (x + 2 * h) + 16 * u (x + h) - 30 * u x + 16 * u (x - h) - u (x - 2 * h)) / (12 * h ^ 2)

@[powerlib_foundation] theorem central1_exact {h : ℝ} (hh : h ≠ 0) (a b c x : ℝ) :
    central1 (fun t => a + b * t + c * t ^ 2) x h = b + 2 * c * x := by
  unfold central1; field_simp; ring

@[powerlib_foundation] theorem central1_cubic {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    central1 (fun t => t ^ 3) x h = 3 * x ^ 2 + h ^ 2 := by
  unfold central1; field_simp; ring

@[powerlib_foundation] theorem central1o4_exact {h : ℝ} (hh : h ≠ 0) (a b c d e x : ℝ) :
    central1o4 (fun t => a + b * t + c * t ^ 2 + d * t ^ 3 + e * t ^ 4) x h =
      b + 2 * c * x + 3 * d * x ^ 2 + 4 * e * x ^ 3 := by
  unfold central1o4; field_simp; ring

@[powerlib_foundation] theorem central1o4_quintic {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    central1o4 (fun t => t ^ 5) x h = 5 * x ^ 4 - 4 * h ^ 4 := by
  unfold central1o4; field_simp; ring

@[powerlib_foundation] theorem upwind1_exact {h : ℝ} (hh : h ≠ 0) (a b x : ℝ) :
    upwind1 (fun t => a + b * t) x h = b := by
  unfold upwind1; field_simp; ring

@[powerlib_foundation] theorem upwind1_quadratic {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    upwind1 (fun t => t ^ 2) x h = 2 * x - h := by
  unfold upwind1; field_simp; ring

@[powerlib_foundation] theorem upwind2_exact {h : ℝ} (hh : h ≠ 0) (a b c x : ℝ) :
    upwind2 (fun t => a + b * t + c * t ^ 2) x h = b + 2 * c * x := by
  unfold upwind2; field_simp; ring

/-- Correction: the second-order upwind stencil is not fourth order — it already fails on `x³`
with error `−2h²`. -/
@[powerlib_foundation] theorem upwind2_cubic {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    upwind2 (fun t => t ^ 3) x h = 3 * x ^ 2 - 2 * h ^ 2 := by
  unfold upwind2; field_simp; ring

@[powerlib_foundation] theorem central2_exact {h : ℝ} (hh : h ≠ 0) (a b c d x : ℝ) :
    central2 (fun t => a + b * t + c * t ^ 2 + d * t ^ 3) x h = 2 * c + 6 * d * x := by
  unfold central2; field_simp; ring

@[powerlib_foundation] theorem central2_quartic {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    central2 (fun t => t ^ 4) x h = 12 * x ^ 2 + 2 * h ^ 2 := by
  unfold central2; field_simp; ring

@[powerlib_foundation] theorem central2o4_exact {h : ℝ} (hh : h ≠ 0) (a b c d e f x : ℝ) :
    central2o4 (fun t => a + b * t + c * t ^ 2 + d * t ^ 3 + e * t ^ 4 + f * t ^ 5) x h =
      2 * c + 6 * d * x + 12 * e * x ^ 2 + 20 * f * x ^ 3 := by
  unfold central2o4; field_simp; ring

@[powerlib_foundation] theorem central2o4_sextic {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    central2o4 (fun t => t ^ 6) x h = 30 * x ^ 4 - 8 * h ^ 4 := by
  unfold central2o4; field_simp; ring

/-! ## Neumann boundary closures (§1.7.2) -/

/-- Central ghost-cell closure at node `0`: `(u₁ − u₋₁)/(2Δx) = h ⇔ u₋₁ = u₁ − 2Δx h`. -/
@[powerlib_foundation] theorem ghost_iff {Δx : ℝ} (hΔ : Δx ≠ 0) (u1 um1 h : ℝ) :
    (u1 - um1) / (2 * Δx) = h ↔ um1 = u1 - 2 * Δx * h := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero hΔ)]
  constructor <;> intro H <;> linarith

/-- With the ghost value eliminated, the boundary row of the central second difference is
`2(u₁ − u₀ − Δx h)/Δx²`. -/
@[powerlib_foundation] theorem ghost_boundary_row {Δx : ℝ} (u0 u1 h : ℝ) :
    (u1 - 2 * u0 + (u1 - 2 * Δx * h)) / Δx ^ 2 = 2 * (u1 - u0 - Δx * h) / Δx ^ 2 := by
  ring

/-- Correction: the note's closure `(u₁ − u₀)/(2Δx) = h` uses a quotient that tends to
`u'(0)/2`, so it imposes `u'(0) = 2h`, not `u'(0) = h`. -/
@[powerlib_foundation] theorem note_ghost_tendsto {u : ℝ → ℝ} {d : ℝ} (hu : HasDerivAt u d 0) :
    Filter.Tendsto (fun Δx => (u Δx - u 0) / (2 * Δx)) (nhdsWithin 0 {0}ᶜ) (nhds (d / 2)) := by
  have h := hu.tendsto_slope_zero
  have h' := h.div_const 2
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, smul_eq_mul]
  field_simp

/-- The central closure quotient tends to `u'(0)`. -/
@[powerlib_foundation] theorem ghost_central_tendsto {u : ℝ → ℝ} {d : ℝ} (hu : HasDerivAt u d 0) :
    Filter.Tendsto (fun Δx => (u Δx - u (-Δx)) / (2 * Δx)) (nhdsWithin 0 {0}ᶜ) (nhds d) := by
  have h1 := hu.tendsto_slope_zero
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have hu' : HasDerivAt u d (-0) := by rwa [neg_zero]
  have h2 := (hu'.comp (0 : ℝ) hn).tendsto_slope_zero
  have := (h1.sub h2).div_const 2
  rw [show (d - d * -1) / 2 = d by ring] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, smul_eq_mul, Function.comp_apply, neg_zero]
  field_simp
  ring

/-- One-sided second-order closure `(−3u₀ + 4u₁ − u₂)/(2Δx) = h ⇔ u₀ = (4u₁ − u₂ − 2Δx h)/3`. -/
@[powerlib_foundation] theorem oneSided_iff {Δx : ℝ} (hΔ : Δx ≠ 0) (u0 u1 u2 h : ℝ) :
    (-3 * u0 + 4 * u1 - u2) / (2 * Δx) = h ↔ u0 = (4 * u1 - u2 - 2 * Δx * h) / 3 := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero hΔ)]
  constructor <;> intro H <;> linarith

@[powerlib_foundation] theorem oneSided_exact {Δx : ℝ} (hΔ : Δx ≠ 0) (a b c : ℝ) :
    (-3 * (a + b * 0 + c * 0 ^ 2) + 4 * (a + b * Δx + c * Δx ^ 2) -
        (a + b * (2 * Δx) + c * (2 * Δx) ^ 2)) / (2 * Δx) = b := by
  field_simp; ring

/-! ## Cauer RC chain (§2.3) -/

/-- A uniform Cauer chain with node capacitance `C = ρc_p A Δx` and link resistance
`R = Δx/(κA)` has the MoL heat dynamics. -/
@[powerlib_foundation] theorem cauer_eq_mol {ρcp A Δx κ : ℝ} (hρ : ρcp ≠ 0) (hA : A ≠ 0)
    (hΔ : Δx ≠ 0) (hκ : κ ≠ 0) (Tm T0 Tp : ℝ) :
    ((Tm - T0) / (Δx / (κ * A)) - (T0 - Tp) / (Δx / (κ * A))) / (ρcp * A * Δx) =
      κ / ρcp * ((Tp - 2 * T0 + Tm) / Δx ^ 2) := by
  field_simp
  ring

/-! ## Port coupling (§1.7.4) -/

/-- Interior MoL ODE `ẋ = A_ii x + A_ib u_bnd + B u_ext` with the linear port constraint
`0 = G_x x + G_b u_bnd + G_e u_ext`. -/
def portCoupled {n m p : ℕ} (Aii : Matrix (Fin n) (Fin n) ℝ) (Aib : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (Gx : Matrix (Fin m) (Fin n) ℝ) (Gb : Matrix (Fin m) (Fin m) ℝ)
    (Ge : Matrix (Fin m) (Fin p) ℝ) : DAE.LinearDAE n m p :=
  ⟨Aii, Aib, Gx, Gb, B, Ge⟩

/-- With `det G_b ≠ 0` (the boundary Jacobian `∂g/∂u_bnd` is nonsingular) the port-coupled MoL
system is an index-1 DAE: its solutions — pairs `(x, u_bnd)` with `ẋ = A_ii x + A_ib u_bnd +
B u_ext` and `0 = G_x x + G_b u_bnd + G_e u_ext` at every time (left-hand side, the DAE solution
notion of `theorem.DAE.Linear` for `portCoupled`) — are exactly the reduced ODE solutions with
`u_bnd = −G_b⁻¹(G_x x + G_e u_ext)`. -/
@[powerlib_foundation] theorem portCoupled_isSolution_iff {n m p : ℕ}
    (Aii : Matrix (Fin n) (Fin n) ℝ) (Aib : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (Gx : Matrix (Fin m) (Fin n) ℝ) (Gb : Matrix (Fin m) (Fin m) ℝ) (Ge : Matrix (Fin m) (Fin p) ℝ)
    (hGb : Gb.det ≠ 0) (u : ℝ → Fin p → ℝ) (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) :
    (∀ t, HasDerivAt x (Aii *ᵥ x t + Aib *ᵥ y t + B *ᵥ u t) t ∧
      Gx *ᵥ x t + Gb *ᵥ y t + Ge *ᵥ u t = 0) ↔
      (∀ t, HasDerivAt x ((Aii - Aib * Gb⁻¹ * Gx) *ᵥ x t + (B - Aib * Gb⁻¹ * Ge) *ᵥ u t) t) ∧
        ∀ t, y t = -(Gb⁻¹ *ᵥ (Gx *ᵥ x t + Ge *ᵥ u t)) :=
  (portCoupled Aii Aib B Gx Gb Ge).isSolution_iff (isUnit_iff_ne_zero.mpr hGb) u x y

end powerlib.Line.MethodOfLines
