import theorem.Periodic.OrbitalStability
import theorem.Dynamics.ConverseLinearization
import theorem.Map.Linearization

/-! # Instability of a solution from a Floquet multiplier outside the unit circle

A solution `x_*` of `ẋ = G(t, x)` whose linearization `J(t)` is continuous and `T`-periodic with
a Floquet multiplier `|μ| > 1` is not Lyapunov stable: from every initial time `s` there is
`ε > 0` such that solutions starting arbitrarily close to `x_*(s)` reach the distance `ε` from
`x_*`. With `Periodic.exp_stable_of_floquet` (multipliers inside the unit circle give local
exponential stability) the multipliers of the linearization along the periodic solution decide
the local stability of the nonlinear solution whenever no multiplier lies on the unit circle.

The proof samples the deviation once per period (the period map, whose derivative is the
monodromy matrix `D = Φ(s + T, s)`), certifies the expanding multiplier by a discrete Lyapunov
(Stein) equation `Dᵀ H D − a² H = I` with `1 < a < |μ|`, and runs a discrete Chetaev argument on
`V(e) = eᵀ H e`: while the sampled deviation `e_k` stays small, one period changes it into
`D e_k + r_k` with `‖r_k‖ ≤ C ‖e_k‖²` (Lipschitz and linear Grönwall estimates over one period), so
`V(e_{k+1}) ≥ a² V(e_k)`; since `V ≤ |X| ‖H‖ ‖e‖²`, a deviation started along a direction with
`V > 0` must leave every small ball.

Scope.
* Finite state space `ℝ^X` with the sup norm. On the tube `‖x − x_*(t)‖ ≤ ρ` the field `G` is
  continuous, `K`-Lipschitz in the state uniformly in time, and has the quadratic remainder
  `‖G(t, x_* + e) − G(t, x_*) − J(t) e‖ ≤ L ‖e‖²` (the hypotheses of `exp_stable_of_floquet`
  plus the Lipschitz bound, which gives existence); `x_*` is a differentiable solution. Only `J`
  is assumed periodic, not `G`.
* Solutions are integral curves on segments `[s, t]` (Mathlib `IsIntegralCurveOn`). The escaping
  solutions are constructed with LeanForControl's Picard–Lindelöf theorem
  `exists_isIntegralCurveOn_Ici` for the field clamped to the tube (`clampField`), which agrees
  with `G` while the solution is in the tube. The escape radius `ε` may depend on `s`.
* The boundary case `max |μ| = 1` is not decided by the linearization and is not treated.
* Maps: `F : ℝⁿ → ℝⁿ` on `EuclideanSpace ℝ (Fin n)` (Euclidean norm), differentiable at the fixed
  point with Jacobian `Linear.op A`; instability in the sense of the map semantics
  (`theorem/Map/Defs.lean`).
* The equilibrium case (a constant solution of an autonomous `C¹` field, whose monodromy
  `e^{T Df(x*)}` has a multiplier outside the unit circle exactly when `Df(x*)` has an eigenvalue
  with positive real part) is LeanForControl's indirect method, available as
  `Dynamics.unstable_of_characteristic_root_re_pos` (`theorem/Dynamics/Linearization.lean`); it is
  not restated here.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.2 (the Floquet multipliers of the forced trajectory as its stability
criterion; here the direction of a multiplier outside the unit circle, for the nonlinear
trajectory); Hahn, *Stability of Motion* (Chetaev's method); the discrete counterpart of
LeanForControl's quadratic certificate
`LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos`.

Results.
* `bilin_eq_zero_on_genEigenspaces_of_mul`, `bilin_eq_zero_of_no_mul_resonance` — a bilinear
  form with `B(T x, T y) = c B(x, y)` vanishes when no product of two eigenvalues of `T` equals
  `c` (the multiplicative counterpart of LeanForControl's
  `MatrixAlgebra.bilinear_eq_zero_of_no_resonance`).
* `steinOp`, `steinOp_injective`, `dotProduct_mulVec_conj`, `mulVec_re_im` — the Stein operator
  `H ↦ Dᵀ H D − c H` is injective without resonance; `exists_stein_certificate` — a real `D`
  with a complex eigenvalue `|μ| > 1` has `a > 1`, a symmetric `H` and `w` with
  `Dᵀ H D − a² H = I` and `wᵀ H w > 0`.
* `abs_dotProduct_le_card`, `gronwallBound_zero_one_nonneg` — elementary bounds for the sup norm
  and the Grönwall factor (with `Dynamics.gronwallBound_zero_eq_mul`).
* `clampVec`, `clampField`, `clampVec_of_norm_le`, `norm_clampVec_le`, `norm_clampVec_sub_le`,
  `continuous_clampVec`, `clampField_eq`, `continuous_clampField`, `lipschitz_clampField` — the
  field clamped to the tube is continuous and globally Lipschitz and equals `G` on the tube.
* `unstable_of_floquet` — a Floquet multiplier `|μ| > 1` of the linearization makes the periodic
  (or any) solution `x_*` unstable from every initial time.
* `Map.unstable_of_eigenvalue` — the same certificate for maps: a map on `ℝⁿ` differentiable at a
  fixed point whose Jacobian matrix has one complex eigenvalue `|μ| > 1` is unstable
  (`Map.Unstable`). `theorem/Map/Linearization.lean` proves instability when every eigenvalue lies
  outside the closed unit disk (`Map.unstable_of_inverse_schurStable`) and leaves the
  single-eigenvalue case open; the Stein certificate closes it without a spectral splitting.

Corrections.
None: an extension (the instability direction of the multiplier criterion, for the nonlinear
solution).

Family and connection conclusions.
None: static evidence on nonautonomous ODEs (instability of a solution).
-/

noncomputable section
namespace powerlib.Periodic
open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator

/-! ## A multiplicative no-resonance lemma -/

section Resonance

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A bilinear form with `B(T x, T y) = c B(x, y)` vanishes on a pair of generalized eigenspaces
of `T` whose eigenvalues satisfy `ξ ν ≠ c` (induction on the sum of the orders). -/
@[tmio T, powerlib_foundation] theorem bilin_eq_zero_on_genEigenspaces_of_mul
    (T : Module.End ℂ V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (c ξ ν : ℂ)
    (hB : ∀ x y, B (T x) (T y) = c * B x y) (hres : ξ * ν ≠ c) :
    ∀ (k l : ℕ) (x y : V), x ∈ T.genEigenspace ξ k → y ∈ T.genEigenspace ν l → B x y = 0 := by
  intro k l
  induction hsum : k + l using Nat.strong_induction_on generalizing k l with
  | h s ih =>
      intro x y hx hy
      rcases k with _ | k
      · have hx' : x ∈ T.genEigenspace ξ (0 : ℕ∞) := by simpa using hx
        rw [Module.End.mem_genEigenspace_zero] at hx'
        subst hx'
        simp
      rcases l with _ | l
      · have hy' : y ∈ T.genEigenspace ν (0 : ℕ∞) := by simpa using hy
        rw [Module.End.mem_genEigenspace_zero] at hy'
        subst hy'
        simp
      set Nx := (T - ξ • (1 : Module.End ℂ V)) x with hNx
      set Ny := (T - ν • (1 : Module.End ℂ V)) y with hNy
      have hxN : Nx ∈ T.genEigenspace ξ k := by
        rw [Module.End.mem_genEigenspace_nat] at hx ⊢
        simpa only [Nx, LinearMap.mem_ker, pow_succ, Module.End.mul_apply] using hx
      have hyN : Ny ∈ T.genEigenspace ν l := by
        rw [Module.End.mem_genEigenspace_nat] at hy ⊢
        simpa only [Ny, LinearMap.mem_ker, pow_succ, Module.End.mul_apply] using hy
      have h1 : B Nx Ny = 0 := ih (k + l) (by omega) k l rfl Nx Ny hxN hyN
      have h2 : B Nx y = 0 := ih (k + (l + 1)) (by omega) k (l + 1) rfl Nx y hxN hy
      have h3 : B x Ny = 0 := ih ((k + 1) + l) (by omega) (k + 1) l rfl x Ny hx hyN
      have hrec := hB x y
      have hTx : T x = Nx + ξ • x := by simp [Nx]
      have hTy : T y = Ny + ν • y := by simp [Ny]
      rw [hTx, hTy] at hrec
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1,
        h2, h3] at hrec
      have : (ξ * ν - c) * B x y = 0 := by linear_combination hrec
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hres)

/-- A bilinear form with `B(T x, T y) = c B(x, y)` on a finite-dimensional complex space vanishes
when no product of two eigenvalues of `T` equals `c`. -/
@[tmio T, powerlib_foundation] theorem bilin_eq_zero_of_no_mul_resonance [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (c : ℂ)
    (hB : ∀ x y, B (T x) (T y) = c * B x y)
    (hres : ∀ ξ ν, T.HasEigenvalue ξ → T.HasEigenvalue ν → ξ * ν ≠ c) : B = 0 := by
  apply LinearMap.ext
  intro x
  change B x = 0
  rw [← LinearMap.mem_ker]
  have hxall : (⊤ : Submodule ℂ V) ≤ LinearMap.ker B := by
    rw [← T.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun ξ x hx => ?_
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    have hyall : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (B x) := by
      rw [← T.iSup_maxGenEigenspace_eq_top]
      refine iSup_le fun ν y hy => ?_
      rw [LinearMap.mem_ker]
      by_cases hx0 : x = 0
      · simp [hx0]
      by_cases hy0 : y = 0
      · simp [hy0]
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T ξ x).mp hx
      obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace T ν y).mp hy
      exact bilin_eq_zero_on_genEigenspaces_of_mul T B c ξ ν hB
        (hres ξ ν (MatrixAlgebra.hasEigenvalue_of_mem_maxGenEigenspace_ne_zero T hx hx0)
          (MatrixAlgebra.hasEigenvalue_of_mem_maxGenEigenspace_ne_zero T hy hy0))
        k l x y (Module.End.mem_genEigenspace_nat.mpr hk) (Module.End.mem_genEigenspace_nat.mpr hl)
    exact LinearMap.mem_ker.mp (hyall Submodule.mem_top)
  exact hxall Submodule.mem_top

end Resonance

/-! ## The discrete Lyapunov (Stein) certificate of an expanding multiplier -/

section Stein

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The Stein operator `H ↦ Dᵀ H D − c H`. -/
def steinOp (D : Matrix X X ℝ) (c : ℝ) : Matrix X X ℝ →ₗ[ℝ] Matrix X X ℝ where
  toFun H := Dᵀ * H * D - c • H
  map_add' H K := by simp only [Matrix.mul_add, Matrix.add_mul, smul_add]; abel
  map_smul' r H := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub, smul_comm r c]

omit [DecidableEq X] in
/-- `(D u)ᵀ H (D v) = uᵀ (Dᵀ H D) v`. -/
@[tmio T, powerlib_foundation] theorem dotProduct_mulVec_conj {R : Type*} [CommRing R]
    (D H : Matrix X X R) (u v : X → R) :
    (D *ᵥ u) ⬝ᵥ (H *ᵥ (D *ᵥ v)) = u ⬝ᵥ ((Dᵀ * H * D) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Dᵀ,
    Matrix.vecMul_transpose]

/-- The Stein operator is injective when no product of two eigenvalues of `D` equals `c`. -/
@[tmio T, powerlib_foundation] theorem steinOp_injective (D : Matrix X X ℝ) (c : ℝ)
    (hres : ∀ ξ ν, Module.End.HasEigenvalue (D.map (algebraMap ℝ ℂ)).mulVecLin ξ →
      Module.End.HasEigenvalue (D.map (algebraMap ℝ ℂ)).mulVecLin ν → ξ * ν ≠ (c : ℂ)) :
    Function.Injective (steinOp D c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro H hH
  set DC : Matrix X X ℂ := D.map (algebraMap ℝ ℂ) with hDC
  set HC : Matrix X X ℂ := H.map (algebraMap ℝ ℂ) with hHC
  have hreal : Dᵀ * H * D = c • H := sub_eq_zero.mp hH
  have hcomplex : DCᵀ * HC * DC = (c : ℂ) • HC := by
    have := congrArg (fun M : Matrix X X ℝ => M.map (algebraMap ℝ ℂ)) hreal
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext i j
    simp [HC]
  set B : (X → ℂ) →ₗ[ℂ] (X → ℂ) →ₗ[ℂ] ℂ := Matrix.toBilin' HC with hB
  have hBT : ∀ x y, B (DC.mulVecLin x) (DC.mulVecLin y) = (c : ℂ) * B x y := by
    intro x y
    simp only [hB, Matrix.mulVecLin_apply, Matrix.toBilin'_apply']
    rw [dotProduct_mulVec_conj, hcomplex, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hB0 : B = 0 := bilin_eq_zero_of_no_mul_resonance _ B _ hBT hres
  have hHC0 : HC = 0 := Matrix.toBilin'.injective (by rw [← hB, hB0, map_zero])
  have h0 : H.map (algebraMap ℝ ℂ) = (0 : Matrix X X ℝ).map (algebraMap ℝ ℂ) := by
    rw [← hHC, hHC0, Matrix.map_zero _ (map_zero _)]
  exact Matrix.map_injective Complex.ofReal_injective h0

omit [DecidableEq X] in
/-- A real matrix commutes with the real and imaginary parts of a complex vector. -/
@[tmio T, powerlib_foundation] theorem mulVec_re_im (D : Matrix X X ℝ) (z : X → ℂ) :
    D *ᵥ (fun i => (z i).re) = (fun i => ((D.map (algebraMap ℝ ℂ) *ᵥ z) i).re) ∧
      D *ᵥ (fun i => (z i).im) = (fun i => ((D.map (algebraMap ℝ ℂ) *ᵥ z) i).im) := by
  constructor <;> funext i <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum]

/-- **Discrete Lyapunov (Stein) certificate of an expanding multiplier.** A real matrix `D` with a
complex eigenvalue `|μ| > 1` admits `a > 1`, a symmetric `H` and a direction `w` with
`Dᵀ H D − a² H = I` and `wᵀ H w > 0`: along `e ↦ D e` the form `V(e) = eᵀ H e` obeys
`V(D e) = a² V(e) + |e|²`. The factor `a ∈ (1, |μ|)` avoids the finitely many products of two
eigenvalues (no resonance), so the Stein operator is invertible; symmetry follows from uniqueness,
and the real or imaginary part of an eigenvector of `μ` gives `w`. -/
@[tmio T, powerlib_foundation] theorem exists_stein_certificate (D : Matrix X X ℝ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (D.map (algebraMap ℝ ℂ))) (h1 : 1 < ‖μ‖) :
    ∃ (a : ℝ) (H : Matrix X X ℝ) (w : X → ℝ), 1 < a ∧ Hᵀ = H ∧
      Dᵀ * H * D - a ^ 2 • H = 1 ∧ 0 < w ⬝ᵥ (H *ᵥ w) := by
  obtain ⟨v, hv, hDv⟩ := LTI.mem_spectrum_iff_exists_eigvec.1 hμ
  set T : Module.End ℂ (X → ℂ) := (D.map (algebraMap ℝ ℂ)).mulVecLin with hTdef
  set S : Set ℝ := (fun z : ℂ × ℂ => Real.sqrt ((z.1 * z.2).re)) ''
    (spectrum ℂ T ×ˢ spectrum ℂ T) with hSdef
  have hS : S.Finite := (T.finite_spectrum.prod T.finite_spectrum).image _
  obtain ⟨a, ⟨ha1, haμ⟩, haS⟩ := (Set.Ioo_infinite h1).exists_notMem_finite hS
  have hres : ∀ ξ ν, T.HasEigenvalue ξ → T.HasEigenvalue ν → ξ * ν ≠ ((a ^ 2 : ℝ) : ℂ) := by
    intro ξ ν hξ hν heq
    apply haS
    refine ⟨(ξ, ν), ⟨hξ.mem_spectrum, hν.mem_spectrum⟩, ?_⟩
    show Real.sqrt ((ξ * ν).re) = a
    rw [heq, Complex.ofReal_re, Real.sqrt_sq (by linarith)]
  have hinj := steinOp_injective D (a ^ 2) hres
  obtain ⟨H, hH⟩ := LinearMap.injective_iff_surjective.mp hinj 1
  have hst : Dᵀ * H * D - a ^ 2 • H = 1 := hH
  have hHt : steinOp D (a ^ 2) Hᵀ = 1 := by
    have h := congrArg Matrix.transpose hst
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at h
    show Dᵀ * Hᵀ * D - a ^ 2 • Hᵀ = 1
    rw [← h, Matrix.mul_assoc]
  have hsym : Hᵀ = H := hinj (hHt.trans hH.symm)
  set q : (X → ℝ) → ℝ := fun z => z ⬝ᵥ (H *ᵥ z) with hqdef
  have hq : ∀ z, q (D *ᵥ z) = a ^ 2 * q z + z ⬝ᵥ z := by
    intro z
    simp only [hqdef]
    rw [dotProduct_mulVec_conj, show Dᵀ * H * D = a ^ 2 • H + 1 by rw [← hst]; abel,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  have hsymm : ∀ u z : X → ℝ, u ⬝ᵥ (H *ᵥ z) = z ⬝ᵥ (H *ᵥ u) := by
    intro u z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]
  set x : X → ℝ := fun i => (v i).re with hx
  set y : X → ℝ := fun i => (v i).im with hy
  have hDx : D *ᵥ x = μ.re • x - μ.im • y := by
    rw [(mulVec_re_im D v).1, hDv]; funext i; simp [x, y, Complex.mul_re]
  have hDy : D *ᵥ y = μ.im • x + μ.re • y := by
    rw [(mulVec_re_im D v).2, hDv]; funext i; simp [x, y, Complex.mul_im]; ring
  have hrot : q (μ.re • x - μ.im • y) + q (μ.im • x + μ.re • y) =
      (μ.re ^ 2 + μ.im ^ 2) * (q x + q y) := by
    simp only [hqdef, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [hsymm y x]; ring
  have hnorm : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : 0 < x ⬝ᵥ x + y ⬝ᵥ y := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hsum : x ⬝ᵥ x + y ⬝ᵥ y = ∑ j, Complex.normSq (v j) := by
      simp only [x, y, dotProduct, ← Finset.sum_add_distrib, Complex.normSq_apply]
    rw [hsum]
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
      (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i))
  have hsum : (‖μ‖ ^ 2 - a ^ 2) * (q x + q y) = x ⬝ᵥ x + y ⬝ᵥ y := by
    have h1 := hq x
    have h2 := hq y
    rw [hDx] at h1
    rw [hDy] at h2
    linear_combination (q x + q y) * hnorm - hrot + h1 + h2
  have hgap : 0 < ‖μ‖ ^ 2 - a ^ 2 := by nlinarith
  have hqpos : 0 < q x + q y := by
    by_contra hc
    push Not at hc
    nlinarith
  rcases lt_or_ge 0 (q x) with hqx | hqx
  · exact ⟨a, H, x, ha1, hsym, hst, hqx⟩
  · exact ⟨a, H, y, ha1, hsym, hst, by linarith⟩

end Stein

/-! ## Norm bounds on `ℝ^X` with the sup norm -/

section Bounds

variable {X : Type*} [Fintype X]

/-- `|u ⬝ v| ≤ |X| ‖u‖ ‖v‖` for the sup norm. -/
@[tmio T, powerlib_foundation] theorem abs_dotProduct_le_card (u v : X → ℝ) :
    |u ⬝ᵥ v| ≤ Fintype.card X * ‖u‖ * ‖v‖ := by
  unfold dotProduct
  calc |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : X, ‖u‖ * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm v i) (norm_nonneg _)
          (norm_nonneg _)
    _ = Fintype.card X * ‖u‖ * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- `‖u‖² ≤ u ⬝ u` for the sup norm (on `Fin m → ℝ` this is
`SingularPerturbation.norm_sq_le_dotProduct_self`). -/
@[tmio T, powerlib_foundation] private theorem sq_norm_le_dotProduct_self (u : X → ℝ) :
    ‖u‖ ^ 2 ≤ u ⬝ᵥ u := by
  have h0 : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have h : ‖u‖ ≤ Real.sqrt (u ⬝ᵥ u) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  calc ‖u‖ ^ 2 ≤ Real.sqrt (u ⬝ᵥ u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = u ⬝ᵥ u := Real.sq_sqrt h0

@[tmio T, powerlib_foundation] theorem gronwallBound_zero_one_nonneg {K x : ℝ} (hK : 0 ≤ K)
    (hx : 0 ≤ x) : 0 ≤ gronwallBound 0 K 1 x := by
  unfold gronwallBound
  split_ifs with h
  · linarith
  · have hKp : 0 < K := lt_of_le_of_ne hK (Ne.symm h)
    have : 1 ≤ Real.exp (K * x) := Real.one_le_exp (by positivity)
    have : 0 ≤ 1 / K * (Real.exp (K * x) - 1) := mul_nonneg (by positivity) (by linarith)
    linarith

end Bounds

/-! ## Clamping the field outside the tube -/

section Clamp

variable {X : Type*} [Fintype X]

/-- Coordinatewise clamp to `[−ρ, ρ]`, the identity on the sup-norm ball of radius `ρ`. -/
def clampVec (ρ : ℝ) (e : X → ℝ) : X → ℝ := fun i => max (-ρ) (min ρ (e i))

@[tmio T, powerlib_foundation] theorem clampVec_of_norm_le {ρ : ℝ} {e : X → ℝ} (he : ‖e‖ ≤ ρ) :
    clampVec ρ e = e := by
  funext i
  have hi : |e i| ≤ ρ := by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm e i).trans he
  rw [abs_le] at hi
  simp only [clampVec, min_eq_right hi.2, max_eq_right hi.1]

@[tmio T, powerlib_foundation] theorem norm_clampVec_le {ρ : ℝ} (hρ : 0 ≤ ρ) (e : X → ℝ) :
    ‖clampVec ρ e‖ ≤ ρ := by
  refine (pi_norm_le_iff_of_nonneg hρ).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

@[tmio T, powerlib_foundation] theorem norm_clampVec_sub_le (ρ : ℝ) (e e' : X → ℝ) :
    ‖clampVec ρ e - clampVec ρ e'‖ ≤ ‖e - e'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [Pi.sub_apply, clampVec]
  have h1 := abs_max_sub_max_le_max (-ρ) (min ρ (e i)) (-ρ) (min ρ (e' i))
  have h2 := abs_min_sub_min_le_max ρ (e i) ρ (e' i)
  simp only [sub_self, abs_zero] at h1 h2
  replace h1 := h1.trans (max_le (abs_nonneg _) le_rfl)
  replace h2 := h2.trans (max_le (abs_nonneg _) le_rfl)
  have h3 : |e i - e' i| ≤ ‖e - e'‖ := by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (e - e') i
  linarith

omit [Fintype X] in
@[tmio T, powerlib_foundation] theorem continuous_clampVec (ρ : ℝ) :
    Continuous (clampVec (X := X) ρ) :=
  continuous_pi fun i => continuous_const.max (continuous_const.min (continuous_apply i))

/-- The field `G` read through the clamp around the solution `x_*`: equal to `G` on the tube
`‖x − x_*(t)‖ ≤ ρ`, globally Lipschitz when `G` is Lipschitz on the tube. -/
def clampField (G : ℝ → (X → ℝ) → X → ℝ) (xs : ℝ → X → ℝ) (ρ t : ℝ) (x : X → ℝ) : X → ℝ :=
  G t (xs t + clampVec ρ (x - xs t))

@[tmio T, powerlib_foundation] theorem clampField_eq {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} {ρ t : ℝ} {x : X → ℝ} (h : ‖x - xs t‖ ≤ ρ) :
    clampField G xs ρ t x = G t x := by
  rw [clampField, clampVec_of_norm_le h, add_sub_cancel]

@[tmio T, powerlib_foundation] theorem continuous_clampField {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} (hxs : Continuous xs) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGc : ContinuousOn (fun p : ℝ × (X → ℝ) => G p.1 p.2) {p | ‖p.2 - xs p.1‖ ≤ ρ}) :
    Continuous (uncurry (clampField G xs ρ)) := by
  have hφ : Continuous fun p : ℝ × (X → ℝ) => (p.1, xs p.1 + clampVec ρ (p.2 - xs p.1)) :=
    continuous_fst.prodMk ((hxs.comp continuous_fst).add
      ((continuous_clampVec ρ).comp (continuous_snd.sub (hxs.comp continuous_fst))))
  exact hGc.comp_continuous hφ fun p => by
    show ‖xs p.1 + clampVec ρ (p.2 - xs p.1) - xs p.1‖ ≤ ρ
    rw [add_sub_cancel_left]; exact norm_clampVec_le hρ _

@[tmio T, powerlib_foundation] theorem lipschitz_clampField {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {K : NNReal}
    (hGl : ∀ t, LipschitzOnWith K (G t) (Metric.closedBall (xs t) ρ)) (t : ℝ) :
    LipschitzWith K (clampField G xs ρ t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hmem : ∀ z, xs t + clampVec ρ (z - xs t) ∈ Metric.closedBall (xs t) ρ := fun z => by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact norm_clampVec_le hρ _
  refine ((hGl t).dist_le_mul _ (hmem x) _ (hmem y)).trans ?_
  gcongr
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub]
  refine (norm_clampVec_sub_le ρ _ _).trans_eq ?_
  rw [sub_sub_sub_cancel_right]

end Clamp

/-! ## One period near the solution, and the instability theorem -/

section Instability

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- One period of a solution of the clamped field that starts close to `x_*`: the deviation stays
within `e^{KT}` times its initial size, and it differs from the linear prediction
`Φ(τ + T, τ) e(τ)` by at most `L e^{2KT} g(T) ‖e(τ)‖²` (`g` the Grönwall factor of `‖J‖ ≤ M`). -/
@[tmio T, powerlib_foundation] private theorem clamp_step {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} {J : ℝ → Matrix X X ℝ} (hJc : Continuous J) {M : ℝ}
    (hM : ∀ t, ‖J t‖ ≤ M) (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {ρ L : ℝ} {K : NNReal}
    (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (hlip : ∀ t, LipschitzWith K (clampField G xs ρ t))
    (hR : ∀ t e, ‖e‖ ≤ ρ → ‖G t (xs t + e) - G t (xs t) - J t *ᵥ e‖ ≤ L * ‖e‖ ^ 2)
    {s : ℝ} {x : ℝ → X → ℝ} (hx : IsIntegralCurveOn x (clampField G xs ρ) (Ici s))
    {τ T : ℝ} (hsτ : s ≤ τ) (hT : 0 ≤ T) (hsmall : Real.exp (K * T) * ‖x τ - xs τ‖ ≤ ρ) :
    (∀ t ∈ Icc τ (τ + T), ‖x t - xs t‖ ≤ Real.exp (K * T) * ‖x τ - xs τ‖) ∧
      ‖x (τ + T) - xs (τ + T) - transition J (τ + T) τ *ᵥ (x τ - xs τ)‖ ≤
        L * Real.exp (K * T) ^ 2 * gronwallBound 0 M 1 T * ‖x τ - xs τ‖ ^ 2 := by
  set e0 := x τ - xs τ with he0
  set C1 := Real.exp (K * T) with hC1
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hxsF : ∀ t, clampField G xs ρ t (xs t) = G t (xs t) := fun t =>
    clampField_eq (by rw [sub_self, norm_zero]; exact hρ)
  have hxd : ∀ t, τ ≤ t → HasDerivWithinAt x (clampField G xs ρ t (x t)) (Ici t) t := fun t ht =>
    (hx t (hsτ.trans ht)).mono (Ici_subset_Ici.2 (hsτ.trans ht))
  have hxc : ContinuousOn x (Icc τ (τ + T)) :=
    hx.continuousOn.mono fun t ht => hsτ.trans ht.1
  have hdist := dist_le_of_trajectories_ODE (v := clampField G xs ρ) (K := K) (f := x) (g := xs)
    (a := τ) (b := τ + T) (δ := ‖e0‖) hlip hxc (fun t ht => hxd t ht.1) hxsc.continuousOn
    (fun t _ => by rw [hxsF]; exact (hxs t).hasDerivWithinAt) (by rw [dist_eq_norm])
  have hbound : ∀ t ∈ Icc τ (τ + T), ‖x t - xs t‖ ≤ C1 * ‖e0‖ := by
    intro t ht
    have h := hdist t ht
    rw [dist_eq_norm] at h
    refine h.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have : t - τ ≤ T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_left this K.2
  refine ⟨hbound, ?_⟩
  set w : ℝ → X → ℝ := fun t => x t - xs t - transition J t τ *ᵥ e0 with hw
  have hΦd : ∀ t, HasDerivAt (fun z => transition J z τ *ᵥ e0)
      (J t *ᵥ (transition J t τ *ᵥ e0)) t := by
    intro t
    set Lm : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
      LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip e0) with hLm
    have hLa : ∀ A : Matrix X X ℝ, Lm A = A *ᵥ e0 := fun A => rfl
    have h := (Lm.hasFDerivAt (x := transition J t τ)).comp_hasDerivAt t
      (Dynamics.stm_hasDerivAt hJc t τ)
    have h2 : HasDerivAt (fun z => transition J z τ *ᵥ e0) (Lm (J t * transition J t τ)) t := h
    rwa [hLa, ← Matrix.mulVec_mulVec] at h2
  have hwc : ContinuousOn w (Icc τ (τ + T)) :=
    (hxc.sub hxsc.continuousOn).sub
      (continuous_iff_continuousAt.2 fun t => (hΦd t).continuousAt).continuousOn
  have hwd : ∀ t ∈ Ico τ (τ + T), HasDerivWithinAt w
      (G t (x t) - G t (xs t) - J t *ᵥ (transition J t τ *ᵥ e0)) (Ici t) t := by
    intro t ht
    have h1 := hxd t ht.1
    rw [clampField_eq ((hbound t (Ico_subset_Icc_self ht)).trans hsmall)] at h1
    exact (h1.sub (hxs t).hasDerivWithinAt).sub (hΦd t).hasDerivWithinAt
  have hw0 : ‖w τ‖ ≤ 0 := by
    simp [hw, he0, LinearSystems.stateTransitionMatrix_self]
  have hwb : ∀ t ∈ Ico τ (τ + T),
      ‖G t (x t) - G t (xs t) - J t *ᵥ (transition J t τ *ᵥ e0)‖ ≤
        M * ‖w t‖ + L * C1 ^ 2 * ‖e0‖ ^ 2 := by
    intro t ht
    set et := x t - xs t with het
    have hbt := hbound t (Ico_subset_Icc_self ht)
    have hR' := hR t et (hbt.trans hsmall)
    have hxe : xs t + et = x t := by rw [het]; abel
    rw [hxe] at hR'
    have hsplit : G t (x t) - G t (xs t) - J t *ᵥ (transition J t τ *ᵥ e0) =
        (G t (x t) - G t (xs t) - J t *ᵥ et) + J t *ᵥ w t := by
      simp only [hw, het, Matrix.mulVec_sub]; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖J t *ᵥ w t‖ ≤ M * ‖w t‖ :=
      (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _))
    have h3 : L * ‖et‖ ^ 2 ≤ L * C1 ^ 2 * ‖e0‖ ^ 2 := by
      have : ‖et‖ ^ 2 ≤ (C1 * ‖e0‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbt 2
      calc L * ‖et‖ ^ 2 ≤ L * (C1 * ‖e0‖) ^ 2 := mul_le_mul_of_nonneg_left this hL
        _ = L * C1 ^ 2 * ‖e0‖ ^ 2 := by ring
    linarith
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hwc hwd hw0 hwb (τ + T)
    ⟨by linarith, le_rfl⟩
  rw [show τ + T - τ = T by ring, Dynamics.gronwallBound_zero_eq_mul] at hgr
  calc ‖x (τ + T) - xs (τ + T) - transition J (τ + T) τ *ᵥ e0‖ = ‖w (τ + T)‖ := rfl
    _ ≤ L * C1 ^ 2 * ‖e0‖ ^ 2 * gronwallBound 0 M 1 T := hgr
    _ = L * C1 ^ 2 * gronwallBound 0 M 1 T * ‖e0‖ ^ 2 := by ring

/-- **A Floquet multiplier outside the unit circle makes a periodic solution of a nonlinear
periodic system unstable.** `xs` solves `ẋ = G(t, x)`; `J(t)` is continuous, `T`-periodic, with a
Floquet multiplier `|μ| > 1` (`FloquetUnstable J T`), and linearizes `G` along `xs` with the
quadratic remainder `L‖e‖²` on the tube `‖e‖ ≤ ρ`, where `G` is continuous and `K`-Lipschitz in
the state. Then from every initial time `s` there is `ε > 0` such that solutions starting
arbitrarily close to `xs(s)` reach the distance `ε` from `xs`: for every `δ > 0` a solution `x` of
`ẋ = G(t, x)` on some `[s, t]` has `‖x(s) − xs(s)‖ < δ` and `‖x(t) − xs(t)‖ ≥ ε`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_floquet {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} {J : ℝ → Matrix X X ℝ} {T : ℝ} (hT : 0 < T) (hJc : Continuous J)
    (hJp : Periodic J T) (hun : FloquetUnstable J T)
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {ρ L : ℝ} {K : NNReal} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hGc : ContinuousOn (fun p : ℝ × (X → ℝ) => G p.1 p.2) {p | ‖p.2 - xs p.1‖ ≤ ρ})
    (hGl : ∀ t, LipschitzOnWith K (G t) (Metric.closedBall (xs t) ρ))
    (hR : ∀ t e, ‖e‖ ≤ ρ → ‖G t (xs t + e) - G t (xs t) - J t *ᵥ e‖ ≤ L * ‖e‖ ^ 2) (s : ℝ) :
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∃ (x : ℝ → X → ℝ) (t : ℝ), s ≤ t ∧
      IsIntegralCurveOn x G (Icc s t) ∧ ‖x s - xs s‖ < δ ∧ ε ≤ ‖x t - xs t‖ := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hJc hJp hT
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨μ, hμ, hμ1⟩ := hun
  set D := monodromy J T s with hD
  have hμD : μ ∈ spectrum ℂ (D.map (algebraMap ℝ ℂ)) := by
    rw [hD, spectrum_monodromy hJc hM hT.le hJp s]; exact hμ
  obtain ⟨a, H, w, ha, hHs, hst, hw⟩ := exists_stein_certificate D hμD hμ1
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hcont := continuous_clampField hxsc hρ.le hGc
  have hlip := lipschitz_clampField hρ.le hGl
  -- constants
  set C1 := Real.exp (K * T) with hC1
  have hC1p : 1 ≤ C1 := Real.one_le_exp (by positivity)
  set g := gronwallBound 0 M 1 T with hg
  have hg0 : 0 ≤ g := gronwallBound_zero_one_nonneg hM0 hT.le
  set C2 := L * C1 ^ 2 * g with hC2
  have hC20 : 0 ≤ C2 := by positivity
  set Q := (Fintype.card X : ℝ) * ‖H‖ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set C3 := Q * C2 * (2 * ‖D‖ + C2) with hC3
  have hC30 : 0 ≤ C3 := by positivity
  set η := min (ρ / C1) (min 1 (1 / (C3 + 1))) with hη
  have hη0 : 0 < η := lt_min (div_pos hρ (by linarith)) (lt_min one_pos (by positivity))
  have hηρ : C1 * η ≤ ρ := by
    have h : η ≤ ρ / C1 := min_le_left _ _
    rw [le_div_iff₀ (by linarith)] at h; linarith
  have hηρ' : η ≤ ρ := le_trans (le_mul_of_one_le_left hη0.le hC1p) hηρ
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηC3 : C3 * η ≤ 1 := by
    have h : η ≤ 1 / (C3 + 1) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h
    nlinarith
  -- the quadratic form
  set V : (X → ℝ) → ℝ := fun z => z ⬝ᵥ (H *ᵥ z) with hV
  have hB : ∀ u v : X → ℝ, |u ⬝ᵥ (H *ᵥ v)| ≤ Q * ‖u‖ * ‖v‖ := fun u v => by
    refine (abs_dotProduct_le_card u (H *ᵥ v)).trans ?_
    calc (Fintype.card X : ℝ) * ‖u‖ * ‖H *ᵥ v‖ ≤ Fintype.card X * ‖u‖ * (‖H‖ * ‖v‖) := by
          gcongr; exact Matrix.linfty_opNorm_mulVec _ _
      _ = Q * ‖u‖ * ‖v‖ := by rw [hQ]; ring
  have hVle : ∀ z, V z ≤ Q * ‖z‖ ^ 2 := fun z => by
    have := hB z z
    calc V z ≤ |V z| := le_abs_self _
      _ ≤ Q * ‖z‖ * ‖z‖ := this
      _ = Q * ‖z‖ ^ 2 := by ring
  have hVD : ∀ z, V (D *ᵥ z) = a ^ 2 * V z + z ⬝ᵥ z := fun z => by
    simp only [hV]
    rw [dotProduct_mulVec_conj, show Dᵀ * H * D = a ^ 2 • H + 1 by rw [← hst]; abel,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  have hVstep : ∀ e r : X → ℝ, ‖e‖ ≤ η → ‖r‖ ≤ C2 * ‖e‖ ^ 2 → a ^ 2 * V e ≤ V (D *ᵥ e + r) := by
    intro e r he hr
    have hexp : V (D *ᵥ e + r) = V (D *ᵥ e) + ((D *ᵥ e) ⬝ᵥ (H *ᵥ r) + r ⬝ᵥ (H *ᵥ (D *ᵥ e)) +
        r ⬝ᵥ (H *ᵥ r)) := by
      simp only [hV, Matrix.mulVec_add, dotProduct_add, add_dotProduct]; ring
    have hDe : ‖D *ᵥ e‖ ≤ ‖D‖ * ‖e‖ := Matrix.linfty_opNorm_mulVec _ _
    have hee := sq_norm_le_dotProduct_self e
    have he0 : 0 ≤ ‖e‖ := norm_nonneg _
    have hcross : |(D *ᵥ e) ⬝ᵥ (H *ᵥ r)| + |r ⬝ᵥ (H *ᵥ (D *ᵥ e))| + |r ⬝ᵥ (H *ᵥ r)| ≤
        ‖e‖ ^ 2 := by
      have h1 := hB (D *ᵥ e) r
      have h2 := hB r (D *ᵥ e)
      have h3 := hB r r
      calc _ ≤ Q * ‖D *ᵥ e‖ * ‖r‖ + Q * ‖r‖ * ‖D *ᵥ e‖ + Q * ‖r‖ * ‖r‖ := by linarith
        _ ≤ Q * (‖D‖ * ‖e‖) * (C2 * ‖e‖ ^ 2) + Q * (C2 * ‖e‖ ^ 2) * (‖D‖ * ‖e‖) +
            Q * (C2 * ‖e‖ ^ 2) * (C2 * ‖e‖ ^ 2) := by gcongr
        _ = Q * C2 * (2 * ‖D‖ + C2 * ‖e‖) * ‖e‖ * ‖e‖ ^ 2 := by ring
        _ ≤ Q * C2 * (2 * ‖D‖ + C2) * η * ‖e‖ ^ 2 := by
            have h4 : C2 * ‖e‖ ≤ C2 := mul_le_of_le_one_right hC20 (he.trans hη1)
            gcongr
        _ = C3 * η * ‖e‖ ^ 2 := by rw [hC3]
        _ ≤ 1 * ‖e‖ ^ 2 := by gcongr
        _ = ‖e‖ ^ 2 := one_mul _
    have n1 := neg_abs_le ((D *ᵥ e) ⬝ᵥ (H *ᵥ r))
    have n2 := neg_abs_le (r ⬝ᵥ (H *ᵥ (D *ᵥ e)))
    have n3 := neg_abs_le (r ⬝ᵥ (H *ᵥ r))
    rw [hexp, hVD]
    linarith
  refine ⟨η, hη0, fun δ hδ => ?_⟩
  -- the initial deviation along the positive direction of the certificate
  have hwne : w ≠ 0 := by rintro rfl; simp at hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hm : 0 < min δ η := lt_min hδ hη0
  set θ := min δ η / (2 * ‖w‖) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθw : ‖θ • w‖ = min δ η / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hθ0.le, hθ]; field_simp
  obtain ⟨x, hx0, hx, -⟩ := exists_isIntegralCurveOn_Ici hcont hlip s (xs s + θ • w)
  set e : ℕ → X → ℝ := fun k => x (s + k * T) - xs (s + k * T) with he
  have he0 : e 0 = θ • w := by simp [he, hx0]
  have he0η : ‖e 0‖ ≤ η := by
    rw [he0, hθw]; linarith [min_le_right δ η]
  have hstep : ∀ k : ℕ, ‖e k‖ ≤ η →
      (∀ t ∈ Icc (s + k * T) (s + k * T + T), ‖x t - xs t‖ ≤ ρ) ∧
        a ^ 2 * V (e k) ≤ V (e (k + 1)) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ k * T := by positivity
    have hsk : s ≤ s + k * T := by linarith
    have hsmall : C1 * ‖e k‖ ≤ ρ := (mul_le_mul_of_nonneg_left hk (by linarith)).trans hηρ
    obtain ⟨hb, hr⟩ := clamp_step hJc hM hxs hρ.le hL hlip hR hx hsk hT.le hsmall
    refine ⟨fun t ht => (hb t ht).trans hsmall, ?_⟩
    have hΦ : transition J (s + k * T + T) (s + k * T) = D := by
      rw [hD, monodromy, show s + k * T + T = s + T + k * T by ring]
      exact transition_add_period hJc hM (hJp.nat_mul k) (by linarith)
    have hidx : s + ((k + 1 : ℕ) : ℝ) * T = s + k * T + T := by push_cast; ring
    have hek1 : e (k + 1) = D *ᵥ e k + (e (k + 1) - D *ᵥ e k) := by abel
    rw [hek1]
    refine hVstep _ _ hk ?_
    have : e (k + 1) - D *ᵥ e k = x (s + k * T + T) - xs (s + k * T + T) -
        transition J (s + k * T + T) (s + k * T) *ᵥ (x (s + k * T) - xs (s + k * T)) := by
      rw [hΦ, he]; simp only; rw [hidx]
    rw [this]
    exact hr
  have hgrow : ∀ k : ℕ, (∀ j ≤ k, ‖e j‖ ≤ η) → (a ^ 2) ^ k * V (e 0) ≤ V (e k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro h
      have h1 := ih fun j hj => h j (by omega)
      have h2 := (hstep k (h k (by omega))).2
      calc (a ^ 2) ^ (k + 1) * V (e 0) = a ^ 2 * ((a ^ 2) ^ k * V (e 0)) := by ring
        _ ≤ a ^ 2 * V (e k) := by gcongr
        _ ≤ V (e (k + 1)) := h2
  have hV0 : 0 < V (e 0) := by
    rw [he0]
    simp only [hV, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    exact mul_pos hθ0 (mul_pos hθ0 hw)
  have hex : ∃ k, η < ‖e k‖ := by
    by_contra hcon
    push Not at hcon
    have hbd : ∀ k, (a ^ 2) ^ k * V (e 0) ≤ Q * η ^ 2 := fun k =>
      (hgrow k fun j _ => hcon j).trans ((hVle _).trans (by gcongr; exact hcon k))
    have ha2 : 1 < a ^ 2 := by nlinarith
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt ha2).eventually_gt_atTop
      (Q * η ^ 2 / V (e 0))).exists
    have h := hbd k
    rw [div_lt_iff₀ hV0] at hk
    linarith
  classical
  set k0 := Nat.find hex with hk0def
  have hk0 : η < ‖e k0‖ := Nat.find_spec hex
  have hmin : ∀ j < k0, ‖e j‖ ≤ η := fun j hj => not_lt.mp (Nat.find_min hex hj)
  have hdev : ∀ k ≤ k0, ∀ t ∈ Icc s (s + k * T), ‖x t - xs t‖ ≤ ρ := by
    intro k
    induction k with
    | zero =>
      intro _ t ht
      have hts : t = s := by
        simp only [CharP.cast_eq_zero, zero_mul, add_zero, Icc_self, mem_singleton_iff] at ht
        exact ht
      have h0 : e 0 = x s - xs s := by simp [he]
      rw [hts, ← h0]
      exact he0η.trans hηρ'
    | succ k ih =>
      intro hk t ht
      by_cases hts : t ≤ s + k * T
      · exact ih (by omega) t ⟨ht.1, hts⟩
      · push Not at hts
        refine (hstep k (hmin k (by omega))).1 t ⟨hts.le, ?_⟩
        have := ht.2
        push_cast at this
        linarith
  have hk0T : (0 : ℝ) ≤ k0 * T := by positivity
  refine ⟨x, s + k0 * T, by linarith, fun t ht => ?_, ?_, hk0.le⟩
  · have h1 := (hx t ht.1).mono (Icc_subset_Ici_self : Icc s (s + k0 * T) ⊆ Ici s)
    rwa [clampField_eq (hdev k0 le_rfl t ht)] at h1
  · rw [hx0, add_sub_cancel_left, hθw]
    linarith [min_le_left δ η]

end Instability

end powerlib.Periodic

/-! ## Maps: one expanding eigenvalue gives instability -/

namespace powerlib.Map
open Filter Topology Matrix
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **A map is unstable at a fixed point whose Jacobian has one eigenvalue outside the unit
circle.** `F` is differentiable at the fixed point `x` with Jacobian matrix `A`, and `A` has a
complex eigenvalue `|μ| > 1`. With the Stein certificate of `A`
(`Periodic.exists_stein_certificate`), `V(e) = ⟨e, H e⟩` grows at least by `a² > 1` per step on
a small ball, while `V ≤ ‖H‖ ‖e‖²`. No spectral splitting and no smoothness beyond
differentiability at `x` is used. -/
@[tmio T, powerlib_foundation] theorem unstable_of_eigenvalue {F : ℝⁿ → ℝⁿ}
    {A : Matrix (Fin n) (Fin n) ℝ} {x : ℝⁿ} (hF : HasFDerivAt F (Linear.op A) x) (hx : F x = x)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) (h1 : 1 < ‖μ‖) : Unstable F x := by
  obtain ⟨a, H, w, ha, hHs, hst, hw⟩ := Periodic.exists_stein_certificate A hμ h1
  set V : ℝⁿ → ℝ := fun z => ⟪z, Linear.op H z⟫ with hV
  set h := ‖Linear.op H‖ with hh
  set d := ‖Linear.op A‖ with hd
  have hB : ∀ u v : ℝⁿ, |⟪u, Linear.op H v⟫| ≤ h * ‖u‖ * ‖v‖ := fun u v => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖u‖ * ‖Linear.op H v‖ ≤ ‖u‖ * (h * ‖v‖) :=
          mul_le_mul_of_nonneg_left ((Linear.op H).le_opNorm v) (norm_nonneg _)
      _ = h * ‖u‖ * ‖v‖ := by ring
  have hVA : ∀ z : ℝⁿ, V (Linear.op A z) = a ^ 2 * V z + ‖z‖ ^ 2 := fun z => by
    simp only [hV, Matrix.inner_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
    rw [Periodic.dotProduct_mulVec_conj, show Aᵀ * H * A = a ^ 2 • H + 1 by rw [← hst]; abel,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp
  set c : ℝ := min 1 (1 / (h * (2 * d + 1) + 1)) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcb : h * (2 * d + 1) * c ≤ 1 := by
    have h2 : c ≤ 1 / (h * (2 * d + 1) + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith [hc0]
  have hstep : ∀ e r : ℝⁿ, ‖r‖ ≤ c * ‖e‖ → a ^ 2 * V e ≤ V (Linear.op A e + r) := by
    intro e r hr
    have hexp : V (Linear.op A e + r) = V (Linear.op A e) + (⟪Linear.op A e, Linear.op H r⟫ +
        ⟪r, Linear.op H (Linear.op A e)⟫ + ⟪r, Linear.op H r⟫) := by
      simp only [hV, map_add, inner_add_left, inner_add_right]; ring
    have hAe : ‖Linear.op A e‖ ≤ d * ‖e‖ := (Linear.op A).le_opNorm e
    have h1' := hB (Linear.op A e) r
    have h2' := hB r (Linear.op A e)
    have h3' := hB r r
    have he0 := norm_nonneg e
    have hcross : |⟪Linear.op A e, Linear.op H r⟫| + |⟪r, Linear.op H (Linear.op A e)⟫| +
        |⟪r, Linear.op H r⟫| ≤ ‖e‖ ^ 2 := by
      calc _ ≤ h * ‖Linear.op A e‖ * ‖r‖ + h * ‖r‖ * ‖Linear.op A e‖ + h * ‖r‖ * ‖r‖ := by
            linarith
        _ ≤ h * (d * ‖e‖) * (c * ‖e‖) + h * (c * ‖e‖) * (d * ‖e‖) +
            h * (c * ‖e‖) * (c * ‖e‖) := by gcongr
        _ = h * (2 * d + c) * c * ‖e‖ ^ 2 := by ring
        _ ≤ h * (2 * d + 1) * c * ‖e‖ ^ 2 := by gcongr
        _ ≤ 1 * ‖e‖ ^ 2 := by gcongr
        _ = ‖e‖ ^ 2 := one_mul _
    have n1 := neg_abs_le (⟪Linear.op A e, Linear.op H r⟫)
    have n2 := neg_abs_le (⟪r, Linear.op H (Linear.op A e)⟫)
    have n3 := neg_abs_le (⟪r, Linear.op H r⟫)
    rw [hexp, hVA]
    linarith
  obtain ⟨r0, hr0, hball⟩ := Metric.eventually_nhds_iff.mp (hF.isLittleO.def hc0)
  intro hstab
  obtain ⟨δ, hδ, hb⟩ := hstab r0 hr0
  set w' : ℝⁿ := WithLp.toLp 2 w with hw'
  have hVw : 0 < V w' := by
    simp only [hV, hw', Matrix.inner_toEuclideanCLM]
    simpa using hw
  have hwne : w' ≠ 0 := by rintro h0; rw [h0] at hVw; simp [hV] at hVw
  have hwpos : 0 < ‖w'‖ := norm_pos_iff.mpr hwne
  set θ := δ / (2 * ‖w'‖) with hθ
  have hθ0 : 0 < θ := by positivity
  set y := x + θ • w' with hy
  have hy0 : ‖y - x‖ < δ := by
    rw [hy, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hθ0.le, hθ]
    field_simp
    linarith
  have hin : ∀ k, ‖F^[k] y - x‖ < r0 := hb y hy0
  have hgrow : ∀ k : ℕ, (a ^ 2) ^ k * V (y - x) ≤ V (F^[k] y - x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      set e := F^[k] y - x with he
      have hr := hball (show dist (F^[k] y) x < r0 by rw [dist_eq_norm]; exact hin k)
      rw [hx] at hr
      have heq : F (F^[k] y) - x = Linear.op A e + (F (F^[k] y) - x - Linear.op A e) := by abel
      rw [heq]
      calc (a ^ 2) ^ (k + 1) * V (y - x) = a ^ 2 * ((a ^ 2) ^ k * V (y - x)) := by ring
        _ ≤ a ^ 2 * V e := by gcongr
        _ ≤ _ := hstep e _ hr
  have hV0 : 0 < V (y - x) := by
    rw [hy, add_sub_cancel_left]
    simp only [hV, map_smul, inner_smul_left, inner_smul_right]
    simp only [hV] at hVw
    simp only [conj_trivial]
    exact mul_pos hθ0 (mul_pos hθ0 hVw)
  have hVle : ∀ z : ℝⁿ, V z ≤ h * ‖z‖ ^ 2 := fun z =>
    (le_abs_self _).trans ((hB z z).trans_eq (by ring))
  have ha2 : 1 < a ^ 2 := by nlinarith
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt ha2).eventually_gt_atTop
    (h * r0 ^ 2 / V (y - x))).exists
  rw [div_lt_iff₀ hV0] at hk
  have h1 := hgrow k
  have h2 := hVle (F^[k] y - x)
  have h3 : ‖F^[k] y - x‖ ^ 2 ≤ r0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hin k).le 2
  have hh0 : 0 ≤ h := norm_nonneg _
  nlinarith

end powerlib.Map
