import theorem.Periodic.RobustThreshold
import theorem.Periodic.OrbitalInstability

/-! # Small-signal instability survives every small modulation, uniformly in the period

`Periodic.Robust.exists_floquetUnstable_of_norm_le` shows that an eigenvalue `Re λ > 0` of the
constant matrix `A₀` keeps `ẋ = (A₀ + B(t)) x` Floquet unstable for every waveform of size
`sup ‖B‖ ≤ b₀(T)`, with a radius obtained by continuity of the monodromy matrix at the period
`T`. This module removes the dependence on `T`: one `b₀ > 0`, fixed by `A₀` alone, serves every
period, every waveform and even non-periodic modulations.

The route is an indefinite Lyapunov function (inertia), with no exponential dichotomy. LeanForControl
`LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos` chooses a
shift `0 < α` avoiding the finitely many resonances `λᵢ + λⱼ = 2α`, solves the shifted Lyapunov
(Sylvester) equation, and returns a symmetric `H` with a positive direction `wᵀ H w > 0` and
`S = H A₀ + A₀ᵀ H − 2αH ≻ 0`. Along every solution of `ẋ = (A₀ + B(t)) x`, `V = xᵀ H x` has
`V̇ = 2αV + xᵀ S x + 2 xᵀ H B x`; if `xᵀ S x ≥ q |x|²` and `2 n ‖H‖ ‖B(t)‖ ≤ q` the last two terms
are nonnegative, so `V(x(t)) ≥ e^{2α(t − s)} V(x(s))` for every continuous `B`, periodic or not.
For the monodromy matrix `M = Φ(T, 0)` this says `Mᵀ H M ⪰ e^{2αT} H`; iterating from the
positive direction, `V(Mᵏ w) ≥ e^{2αkT} V(w)` while `|V(y)| ≤ n ‖H‖ ‖y‖²`, so `M` has an eigenvalue
of modulus at least `e^{αT}` (otherwise `e^{−αT} M` would be Schur stable and its powers would
decay). The threshold `b₀ = q / (2 n ‖H‖)` and the rate `α` do not involve `T`.

Consequence for the separation of small-signal and parametric instability: the small-signal class
is an open set in the space of modulations whose radius is uniform over all pump periods; a pump
of any frequency must have size at least `b₀` to change the verdict "unstable" of the frozen
analysis, and below `b₀` every Floquet multiplier bound `|μ| ≥ e^{αT}` holds, so the growth rate
`ln |μ| / T ≥ α` is bounded below uniformly in `T` too.

Scope.
* `ẋ = (A₀ + B(t)) x` on `ℝⁿ` (`Fin n`), constant real `A₀`, continuous real `B`; no periodicity
  of `B` is assumed. Vectors carry the sup norm and matrices the `L∞` operator norm
  (`Matrix.Norms.Operator`), as in `theorem/Periodic/RobustThreshold.lean`; quadratic forms are
  `xᵀ H x = x ⬝ᵥ H x` and `|x|² = x ⬝ᵥ x`.
* Transition and monodromy matrices of `theorem/Periodic/Transition.lean`; multipliers are the
  complex spectrum of the complexified monodromy; `Periodic.FloquetUnstable`.
* The Lyapunov certificate is the one of LeanForControl's
  `LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos`
  (`MatrixAlgebra.quadraticForm` on `EuclideanSpace ℝ (Fin n)`, transferred to `Fin n → ℝ`).
* Generic mathematics; no model family.

Source: the inertia theorem for Lyapunov equations and Chetaev's instability argument with an
indefinite quadratic form (Hahn, *Stability of Motion*, 1967; Coppel, *Stability and Asymptotic
Behavior of Differential Equations*, 1965, on the roughness of instability); LeanForControl's
quadratic certificate
`LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos`; the
`T`-dependent statement `Periodic.Robust.exists_floquetUnstable_of_norm_le` it makes uniform.

Results.
* `quadratic_smul`, `abs_quadratic_le` — `V(a y) = a² V(y)` and `|V(y)| ≤ n ‖H‖ ‖y‖²`.
* `exists_norm_ge_of_expansion` — a real matrix with `V(M x) ≥ c V(x)` for all `x` (`c > 0`) and
  a direction `V(w) > 0` has an eigenvalue `|μ| ≥ √c`.
* `quadratic_growth` — with `xᵀ S x ≥ q |x|²` and `2 n ‖H‖ b ≤ q`, every solution of
  `ẋ = (A₀ + B(t)) x` with `‖B(t)‖ ≤ b` has `V(x(t)) ≥ e^{2α(t − s)} V(x(s))`.
* `norm_multiplier_ge` — under the same certificate every `Φ(T, 0)` (`T ≥ 0`) has a multiplier
  `|μ| ≥ e^{αT}`.
* `exists_uniform_instability` — an eigenvalue `Re λ > 0` of `A₀`: there are `b₀ > 0`, `α > 0`,
  `w` and `C > 0` such that for every continuous `B` with `sup ‖B‖ ≤ b₀` and every `T > 0` the
  system is Floquet unstable with a multiplier `|μ| ≥ e^{αT}`, and every solution from `w`
  satisfies `‖x(t)‖ ≥ C e^{αt}`.
* `exists_floquetUnstable_uniform` — the period-uniform form of
  `Periodic.Robust.exists_floquetUnstable_of_norm_le`: `∃ b₀ > 0, ∀ T > 0`, every continuous `B`
  with `sup ‖B‖ ≤ b₀` is Floquet unstable.
-/

noncomputable section
namespace powerlib.Periodic.Robust

open Set Matrix Function Filter Topology
open powerlib.Periodic
open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-! ## The quadratic form of a symmetric matrix -/

section Quadratic

variable {H : Matrix (Fin n) (Fin n) ℝ}

/-- `V(a y) = a² V(y)` for `V(y) = yᵀ H y`. -/
@[tmio T, powerlib_foundation] theorem quadratic_smul (a : ℝ) (y : Fin n → ℝ) :
    (a • y) ⬝ᵥ (H *ᵥ (a • y)) = a ^ 2 * (y ⬝ᵥ (H *ᵥ y)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- `|V(y)| ≤ n ‖H‖ ‖y‖²` (sup norm, `L∞` operator norm). -/
@[tmio T, powerlib_foundation] theorem abs_quadratic_le (y : Fin n → ℝ) :
    |y ⬝ᵥ (H *ᵥ y)| ≤ n * ‖H‖ * ‖y‖ ^ 2 := by
  have h := abs_dotProduct_le_card y (H *ᵥ y)
  rw [Fintype.card_fin] at h
  calc |y ⬝ᵥ (H *ᵥ y)| ≤ n * ‖y‖ * ‖H *ᵥ y‖ := h
    _ ≤ n * ‖y‖ * (‖H‖ * ‖y‖) := by
        gcongr
        exact Matrix.linfty_opNorm_mulVec _ _
    _ = n * ‖H‖ * ‖y‖ ^ 2 := by ring

end Quadratic

/-! ## A multiplier outside a disk from an expanding indefinite form -/

/-- **An expanding indefinite form forces a large eigenvalue.** If a real matrix `M` expands the
quadratic form `V(x) = xᵀ H x` by the factor `c > 0`, `V(M x) ≥ c V(x)` for every `x`, and `V`
has a positive direction `V(w) > 0`, then `M` has a complex eigenvalue `|μ| ≥ √c`. Otherwise
`N = M / √c` is Schur stable, `‖Nᵏ‖ ≤ C ρᵏ` with `ρ < 1` (`LTI.SchurStable.exists_pow_bound`),
while `V(Nᵏ w) = c⁻ᵏ V(Mᵏ w) ≥ V(w) > 0` and `V(Nᵏ w) ≤ n ‖H‖ ‖Nᵏ w‖² → 0`. -/
@[tmio T, powerlib_foundation] theorem exists_norm_ge_of_expansion {M H : Matrix (Fin n) (Fin n) ℝ}
    {c : ℝ} (hc : 0 < c) (hM : ∀ x, c * (x ⬝ᵥ (H *ᵥ x)) ≤ (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x)))
    {w : Fin n → ℝ} (hw : 0 < w ⬝ᵥ (H *ᵥ w)) :
    ∃ μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), √c ≤ ‖μ‖ := by
  by_contra hcon
  push Not at hcon
  set s := √c with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hc
  have hss : s ^ 2 = c := Real.sq_sqrt hc.le
  set N : Matrix (Fin n) (Fin n) ℝ := s⁻¹ • M with hN
  have hMN : M = s • N := by rw [hN, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  have hNs : LTI.SchurStable N := by
    intro μ v hv hNv
    have hMv : M.map (algebraMap ℝ ℂ) *ᵥ v = ((s : ℂ) * μ) • v := by
      have e : M.map (algebraMap ℝ ℂ) *ᵥ v = (s : ℂ) • (N.map (algebraMap ℝ ℂ) *ᵥ v) := by
        rw [hMN]
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [e, hNv, smul_smul]
    have hmem : (s : ℂ) * μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) :=
      LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, hMv⟩
    have h := hcon _ hmem
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at h
    have : s * ‖μ‖ < s * 1 := by rw [mul_one]; exact h
    exact lt_of_mul_lt_mul_left this hs0.le
  obtain ⟨C, hC, ρ, hρ0, hρ1, hpow⟩ := hNs.exists_pow_bound
  -- the expansion along the powers of `M`
  have hexp : ∀ k : ℕ, c ^ k * (w ⬝ᵥ (H *ᵥ w)) ≤ (M ^ k *ᵥ w) ⬝ᵥ (H *ᵥ (M ^ k *ᵥ w)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show M ^ (k + 1) = M * M ^ k from pow_succ' M k, ← Matrix.mulVec_mulVec]
      calc c ^ (k + 1) * (w ⬝ᵥ (H *ᵥ w)) = c * (c ^ k * (w ⬝ᵥ (H *ᵥ w))) := by ring
        _ ≤ c * ((M ^ k *ᵥ w) ⬝ᵥ (H *ᵥ (M ^ k *ᵥ w))) := mul_le_mul_of_nonneg_left ih hc.le
        _ ≤ _ := hM (M ^ k *ᵥ w)
  have hlow : ∀ k : ℕ, w ⬝ᵥ (H *ᵥ w) ≤ (N ^ k *ᵥ w) ⬝ᵥ (H *ᵥ (N ^ k *ᵥ w)) := by
    intro k
    have h := hexp k
    rw [hMN, smul_pow, Matrix.smul_mulVec, quadratic_smul, ← pow_mul, mul_comm k 2, pow_mul,
      hss] at h
    exact le_of_mul_le_mul_left h (pow_pos hc k)
  -- but the powers of `N` decay
  set K := (n : ℝ) * ‖H‖ * (C * ‖w‖) ^ 2 with hK
  have hup : ∀ k : ℕ, w ⬝ᵥ (H *ᵥ w) ≤ K * (ρ ^ k) ^ 2 := by
    intro k
    have hN' : ‖N ^ k *ᵥ w‖ ≤ C * ρ ^ k * ‖w‖ :=
      (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hpow k) (norm_nonneg _))
    have h1 := (le_abs_self _).trans (abs_quadratic_le (H := H) (N ^ k *ᵥ w))
    calc w ⬝ᵥ (H *ᵥ w) ≤ _ := hlow k
      _ ≤ n * ‖H‖ * ‖N ^ k *ᵥ w‖ ^ 2 := h1
      _ ≤ n * ‖H‖ * (C * ρ ^ k * ‖w‖) ^ 2 := by
          gcongr
      _ = K * (ρ ^ k) ^ 2 := by rw [hK]; ring
  have hlim : Tendsto (fun k : ℕ => K * (ρ ^ k) ^ 2) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).pow 2).const_mul K
    simpa using this
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hw)).exists
  linarith [hup k]

/-! ## Growth of the indefinite form along the perturbed system -/

section Growth

variable {A₀ H : Matrix (Fin n) (Fin n) ℝ} {α q b : ℝ}

/-- **The indefinite form grows along every small perturbation.** Let `H = Hᵀ` satisfy
`xᵀ (H A₀ + A₀ᵀ H − 2αH) x ≥ q |x|²` and let the continuous or arbitrary `B` satisfy
`‖B(t)‖ ≤ b` with `2 n ‖H‖ b ≤ q`. Every solution of `ẋ = (A₀ + B(t)) x` satisfies
`V(x(t)) ≥ e^{2α(t − s)} V(x(s))` for `s ≤ t`: `V̇ = 2αV + xᵀ S x + 2 xᵀ H B x` and
`2 |xᵀ H B x| ≤ 2 n ‖H‖ ‖B‖ ‖x‖² ≤ q |x|²`. No periodicity of `B` is used. -/
@[tmio T, powerlib_foundation] theorem quadratic_growth (hHs : Hᵀ = H)
    (hq : ∀ x, q * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((H * A₀ + A₀ᵀ * H - (2 * α) • H) *ᵥ x))
    (hb : 2 * n * ‖H‖ * b ≤ q) {B : ℝ → Matrix (Fin n) (Fin n) ℝ} (hBb : ∀ t, ‖B t‖ ≤ b)
    {x : ℝ → Fin n → ℝ} (hx : ∀ t, HasDerivAt x ((A₀ + B t) *ᵥ x t) t) {s t : ℝ}
    (hst : s ≤ t) :
    Real.exp (2 * α * (t - s)) * (x s ⬝ᵥ (H *ᵥ x s)) ≤ x t ⬝ᵥ (H *ᵥ x t) := by
  set V : ℝ → ℝ := fun r => x r ⬝ᵥ (H *ᵥ x r) with hV
  have hVd : ∀ r, HasDerivAt V (2 * (x r ⬝ᵥ (H *ᵥ ((A₀ + B r) *ᵥ x r)))) r := fun r =>
    SingularPerturbation.hasDerivAt_quadratic_of_symm hHs (hx r)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hBb 0)
  -- the derivative dominates `2αV`
  have hge : ∀ r, 2 * α * V r ≤ 2 * (x r ⬝ᵥ (H *ᵥ ((A₀ + B r) *ᵥ x r))) := by
    intro r
    set y := x r
    have hsym : y ⬝ᵥ ((H * A₀ + A₀ᵀ * H - (2 * α) • H) *ᵥ y) =
        2 * (y ⬝ᵥ (H *ᵥ (A₀ *ᵥ y))) - 2 * α * (y ⬝ᵥ (H *ᵥ y)) := by
      rw [sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add, ← mulVec_mulVec,
        ← mulVec_mulVec, dotProduct_mulVec y A₀ᵀ, vecMul_transpose,
        Criteria.dotProduct_mulVec_comm_of_symm hHs (A₀ *ᵥ y) y, smul_mulVec, dotProduct_smul,
        smul_eq_mul]
      ring
    have h1 := hq y
    rw [hsym] at h1
    have h2 : |y ⬝ᵥ (H *ᵥ (B r *ᵥ y))| ≤ n * ‖H‖ * b * (y ⬝ᵥ y) := by
      have hc := abs_dotProduct_le_card y (H *ᵥ (B r *ᵥ y))
      rw [Fintype.card_fin] at hc
      have hHB : ‖H *ᵥ (B r *ᵥ y)‖ ≤ ‖H‖ * (b * ‖y‖) :=
        (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left
          ((Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right (hBb r)
            (norm_nonneg _))) (norm_nonneg _))
      have hy2 := SingularPerturbation.norm_sq_le_dotProduct_self y
      calc |y ⬝ᵥ (H *ᵥ (B r *ᵥ y))| ≤ n * ‖y‖ * ‖H *ᵥ (B r *ᵥ y)‖ := hc
        _ ≤ n * ‖y‖ * (‖H‖ * (b * ‖y‖)) := by gcongr
        _ = n * ‖H‖ * b * ‖y‖ ^ 2 := by ring
        _ ≤ n * ‖H‖ * b * (y ⬝ᵥ y) := by gcongr
    have hyy : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
    have h3 : 2 * (n * ‖H‖ * b) * (y ⬝ᵥ y) ≤ q * (y ⬝ᵥ y) :=
      mul_le_mul_of_nonneg_right (by linarith) hyy
    have hsplit : y ⬝ᵥ (H *ᵥ ((A₀ + B r) *ᵥ y)) =
        y ⬝ᵥ (H *ᵥ (A₀ *ᵥ y)) + y ⬝ᵥ (H *ᵥ (B r *ᵥ y)) := by
      rw [add_mulVec, mulVec_add, dotProduct_add]
    rw [hsplit]
    have := neg_abs_le (y ⬝ᵥ (H *ᵥ (B r *ᵥ y)))
    simp only [hV]
    nlinarith
  -- `e^{−2α(r − s)} V(r)` is nondecreasing
  set φ : ℝ → ℝ := fun r => Real.exp (-(2 * α) * (r - s)) * V r with hφ
  have hφd : ∀ r, HasDerivAt φ (Real.exp (-(2 * α) * (r - s)) *
      (2 * (x r ⬝ᵥ (H *ᵥ ((A₀ + B r) *ᵥ x r))) - 2 * α * V r)) r := by
    intro r
    have he : HasDerivAt (fun r => Real.exp (-(2 * α) * (r - s)))
        (Real.exp (-(2 * α) * (r - s)) * (-(2 * α))) r := by
      have h := ((hasDerivAt_id r).sub_const s).const_mul (-(2 * α))
      simpa using h.exp
    convert he.mul (hVd r) using 1
    ring
  have hmono : Monotone φ := monotone_of_hasDerivAt_nonneg hφd fun r =>
    mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hge r))
  have h := hmono hst
  simp only [hφ, sub_self, mul_zero, Real.exp_zero, one_mul] at h
  have hE : Real.exp (2 * α * (t - s)) * Real.exp (-(2 * α) * (t - s)) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (2 * α * (t - s)) * V s
      ≤ Real.exp (2 * α * (t - s)) * (Real.exp (-(2 * α) * (t - s)) * V t) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = V t := by rw [← mul_assoc, hE, one_mul]

/-- **Every monodromy matrix inherits the expansion.** Under the certificate of
`quadratic_growth`, for every continuous `B` with `‖B(t)‖ ≤ b` and every `T ≥ 0` the matrix
`Φ(T, 0)` of `ẋ = (A₀ + B(t)) x` has a complex eigenvalue `|μ| ≥ e^{αT}`
(`exists_norm_ge_of_expansion` with `c = e^{2αT}`). -/
@[tmio T, powerlib_foundation] theorem norm_multiplier_ge (hHs : Hᵀ = H)
    (hq : ∀ x, q * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((H * A₀ + A₀ᵀ * H - (2 * α) • H) *ᵥ x))
    (hb : 2 * n * ‖H‖ * b ≤ q) {w : Fin n → ℝ} (hw : 0 < w ⬝ᵥ (H *ᵥ w))
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} (hB : Continuous B) (hBb : ∀ t, ‖B t‖ ≤ b) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ μ ∈ spectrum ℂ ((monodromy (fun t => A₀ + B t) T 0).map (algebraMap ℝ ℂ)),
      Real.exp (α * T) ≤ ‖μ‖ := by
  have hAc : Continuous fun t => A₀ + B t := continuous_const.add hB
  have hexp : ∀ x₀, Real.exp (2 * α * T) * (x₀ ⬝ᵥ (H *ᵥ x₀)) ≤
      (monodromy (fun t => A₀ + B t) T 0 *ᵥ x₀) ⬝ᵥ
        (H *ᵥ (monodromy (fun t => A₀ + B t) T 0 *ᵥ x₀)) := by
    intro x₀
    have h := quadratic_growth hHs hq hb hBb (hasDerivAt_transition_mulVec hAc x₀) hT
    simpa [monodromy, LinearSystems.stateTransitionMatrix_self] using h
  obtain ⟨μ, hμ, hle⟩ := exists_norm_ge_of_expansion (Real.exp_pos _) hexp hw
  refine ⟨μ, hμ, le_trans (le_of_eq ?_) hle⟩
  rw [show 2 * α * T = α * T + α * T by ring, Real.exp_add,
    Real.sqrt_mul_self (Real.exp_pos _).le]

end Growth

/-! ## The uniform instability theorem -/

/-- **Small-signal instability is uniformly rough.** If `A₀` has an eigenvalue with `Re λ > 0`,
there are `b₀ > 0`, a rate `α > 0`, a direction `w` and `C > 0`, all fixed by `A₀`, such that for
every continuous `B` with `sup ‖B‖ ≤ b₀` (periodic or not):
* for every period `T > 0`, the system `ẋ = (A₀ + B(t)) x` is Floquet unstable, with a multiplier
  `|μ| ≥ e^{αT}` (growth rate `ln |μ| / T ≥ α`);
* every solution starting at `w` grows: `‖x(t)‖ ≥ C e^{αt}` for `t ≥ 0`.
The certificate is LeanForControl's indefinite quadratic form
(`LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos`), and
`b₀ = q / (2n‖H‖)` with `q` the coercivity constant of `H A₀ + A₀ᵀ H − 2αH ≻ 0`. -/
@[tmio T, powerlib_foundation] theorem exists_uniform_instability {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ))) (hre : 0 < lam.re) :
    ∃ b₀ > 0, ∃ α > 0, ∃ w : Fin n → ℝ, ∃ C > 0,
      ∀ B : ℝ → Matrix (Fin n) (Fin n) ℝ, Continuous B → (∀ t, ‖B t‖ ≤ b₀) →
        (∀ T, 0 < T → FloquetUnstable (fun t => A₀ + B t) T ∧
          ∃ μ ∈ spectrum ℂ ((monodromy (fun t => A₀ + B t) T 0).map (algebraMap ℝ ℂ)),
            Real.exp (α * T) ≤ ‖μ‖) ∧
        ∀ x : ℝ → Fin n → ℝ, (∀ t, HasDerivAt x ((A₀ + B t) *ᵥ x t) t) → x 0 = w →
          ∀ t, 0 ≤ t → C * Real.exp (α * t) ≤ ‖x t‖ := by
  obtain ⟨v, hv, hAv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hlam
  have hn : n ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim _ _)
  have : NeZero n := ⟨hn⟩
  obtain ⟨α, H, wE, hα, hHh, -, hwE, hS⟩ :=
    LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos A₀ hv hAv hre
  obtain ⟨q, hq0, hqS⟩ := MatrixAlgebra.exists_pos_mul_norm_sq_le_quadraticForm _ hS
  have hHs : Hᵀ = H := by
    have h := hHh
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  -- transfer to `Fin n → ℝ`
  have hquad : ∀ (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ),
      MatrixAlgebra.quadraticForm P (WithLp.toLp 2 x) = x ⬝ᵥ (P *ᵥ x) := by
    intro P x
    rw [MatrixAlgebra.quadraticForm, Matrix.inner_toEuclideanCLM]
  have hq : ∀ x : Fin n → ℝ, q * (x ⬝ᵥ x) ≤
      x ⬝ᵥ ((H * A₀ + A₀ᵀ * H - (2 * α) • H) *ᵥ x) := by
    intro x
    have h := hqS (WithLp.toLp 2 x)
    rw [hquad, EuclideanSpace.norm_sq_eq] at h
    convert h using 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, sq]
  set w : Fin n → ℝ := WithLp.ofLp wE with hw
  have hwpos : 0 < w ⬝ᵥ (H *ᵥ w) := by
    have h := hwE
    rwa [show wE = WithLp.toLp 2 w by simp [hw], hquad] at h
  have hH0 : 0 < ‖H‖ := by
    refine norm_pos_iff.mpr fun h0 => ?_
    rw [h0] at hwpos
    simp at hwpos
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  set b₀ := q / (2 * n * ‖H‖) with hb₀
  have hb₀pos : 0 < b₀ := by positivity
  have hb : 2 * n * ‖H‖ * b₀ ≤ q := by
    rw [hb₀, mul_div_cancel₀ _ (by positivity)]
  set V₀ := w ⬝ᵥ (H *ᵥ w)
  set C := √(V₀ / (n * ‖H‖)) with hC
  refine ⟨b₀, hb₀pos, α, hα, w, C, Real.sqrt_pos.mpr (by positivity), fun B hB hBb => ⟨?_, ?_⟩⟩
  · intro T hT
    obtain ⟨μ, hμ, hle⟩ := norm_multiplier_ge hHs hq hb hwpos hB hBb hT.le
    refine ⟨⟨μ, hμ, lt_of_lt_of_le ?_ hle⟩, μ, hμ, hle⟩
    exact Real.one_lt_exp_iff.mpr (mul_pos hα hT)
  · intro x hx hx0 t ht
    have hg := quadratic_growth hHs hq hb hBb hx ht
    rw [hx0, sub_zero] at hg
    have hup := (le_abs_self _).trans (abs_quadratic_le (H := H) (x t))
    have hsq : (C * Real.exp (α * t)) ^ 2 ≤ ‖x t‖ ^ 2 := by
      rw [mul_pow, hC, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * (α * t) = 2 * α * t := by push_cast; ring
      rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- **The robust instability radius does not depend on the period.** The `T`-uniform form of
`exists_floquetUnstable_of_norm_le`: for an eigenvalue `Re λ > 0` of `A₀` there is one `b₀ > 0`
such that, for every period `T > 0` and every continuous `B` with `sup ‖B‖ ≤ b₀`, the system
`ẋ = (A₀ + B(t)) x` is Floquet unstable (`exists_uniform_instability`). -/
@[tmio T, powerlib_foundation] theorem exists_floquetUnstable_uniform
    {A₀ : Matrix (Fin n) (Fin n) ℝ} {lam : ℂ} (hlam : lam ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ)))
    (hre : 0 < lam.re) :
    ∃ b₀ > 0, ∀ T, 0 < T → ∀ B : ℝ → Matrix (Fin n) (Fin n) ℝ, Continuous B →
      (∀ t, ‖B t‖ ≤ b₀) → FloquetUnstable (fun t => A₀ + B t) T := by
  obtain ⟨b₀, hb₀, _, _, _, _, _, h⟩ := exists_uniform_instability hlam hre
  exact ⟨b₀, hb₀, fun T hT B hB hBb => ((h B hB hBb).1 T hT).1⟩

end powerlib.Periodic.Robust
