import theorem.Periodic.Persistence
import theorem.Dynamics.VariationOfConstants
import theorem.ParametricResonance.UniversalThreshold
import theorem.SingularPerturbation.BoundaryLayer

/-! # A robust threshold separating small-signal instability from parametric instability

Small-signal analysis judges the periodic system `ẋ = (A₀ + B(t)) x` by its constant matrix `A₀`
alone. This module makes the separation between the two kinds of instability quantitative in any
dimension, for every period and every waveform of the modulation `B`:

* below a threshold every periodic modulation is harmless. If `‖e^{τA₀}‖ ≤ K e^{−ατ}` (such
  `K, α > 0` exist exactly when `A₀` is Hurwitz) and `sup_t ‖B(t)‖ = b < α/K`, variation of
  constants and Grönwall's inequality give `‖Φ(t, s)‖ ≤ K e^{−(α − Kb)(t − s)}`, so the monodromy
  matrix is Schur stable for every period `T` and every continuous waveform (no averaging, no
  smallness in any other sense). A Lyapunov form uses `A₀ᵀP + PA₀ = −Q` instead: the threshold is
  `sup_t λ_max(PB(t) + B(t)ᵀP) < λ_min(Q)`;
* above zero modulation a small-signal instability persists. If `A₀` has an eigenvalue with
  `Re λ > 0`, every modulation with `sup ‖B‖ ≤ b₀` (some `b₀ > 0`, depending on `A₀` and `T`, not
  on the waveform) is Floquet unstable.

Hence, in the plane (spectral data of `A₀`, modulation size `b`), the small-signal class
(`Re λ > 0`: unstable already at `b = 0` and for all small `b`) and the parametric class (`A₀`
Hurwitz and Floquet unstable) are separated by the explicit curve `b = α/K`: a parametric
instability needs `b ≥ α/K` (and `β ≥ λ_min(Q)` in the Lyapunov form). The rate of every
exponential bound satisfies `nα ≤ −tr A₀` and `K ≥ 1`, so the threshold never exceeds the mean
eigenvalue margin `−tr A₀/n`.

For the second-order model `m δ̈ + D δ̇ + K(t) δ = 0` with `|K − K̄| ≤ εK̄` the perturbation has
size `‖B(t)‖ ≤ εK̄/m` in the state `(δ, δ̇)`, and the robust condition `K_c εK̄/m < α` forces
`2εK̄ < D`. The two-state universal threshold `ε/√(1 − ε) < D/√(mK̄)` of
`theorem/ParametricResonance/UniversalThreshold.lean` is the sharper certificate for stiffness
modulation whenever `m + 2D ≤ 4K̄` (in the time unit `ω₀ = 1`: damping ratio `ξ ≤ 3/4`; at small
`ξ` it allows `ε ≈ 2ξ`, the robust one at most `ε < ξ`); the robust threshold covers what the
universal one does not — any perturbation matrix (damping and cross-coupling modulation), any
dimension, and modulations that are not periodic. For the Lyapunov form of the robust threshold
the comparison holds in every region, `m + 2D > 4K̄` included (it is the universal curve
evaluated at `D/(m + K̄)` instead of `ξ = D/(2√(mK̄))`, equal exactly when `K̄ = m`), and the
uniform-in-period instability under small perturbations is
`theorem/Periodic/UniformRoughness.lean`; see
`theorem/ParametricResonance/RobustVsUniversal.lean`. For the exponential-bound form itself the
comparison also holds in every region (`theorem/Periodic/ExponentialRobustComparison.lean`,
`secondOrder_robust_imp_universal`).

Scope.
* `ẋ = (A₀ + B(t)) x` on `ℝ^X` (finite `X`; `Fin n` where Hurwitz or Schur stability is used),
  constant real `A₀`, continuous real `B`; `T`-periodic `B`, `T > 0`, for the Floquet statements.
  Vectors carry the sup norm and matrices the `L∞` operator norm (`Matrix.Norms.Operator`); the
  constants `K, α, b` refer to this norm. Transition and monodromy matrices are those of
  `theorem/Periodic/Transition.lean`; `LTI.SchurStable`, `Periodic.FloquetUnstable` and
  `LinearSystems.IsHurwitz` are the library's notions.
* The Lyapunov form uses quadratic-form bounds `p₁|x|² ≤ xᵀPx ≤ p₂|x|²`, `xᵀQx ≥ q|x|²`,
  `xᵀ(PB + BᵀP)x ≤ β|x|²` (Euclidean `|x|² = x ⬝ᵥ x`) with `P = Pᵀ`, which are the spectral
  quantities `λ_min, λ_max` without naming eigenvalues.
* The second-order comparison uses the state `(δ, δ̇)` and `Periodic.oscMatrix` of
  `theorem/Periodic/TwoStateBoundary.lean`, constants `m > 0`, `D`, `K̄ > 0`.
* Generic mathematics; no model family.

Source: the roughness of exponential stability under bounded perturbations (Coppel, *Stability
and Asymptotic Behavior of Differential Equations*, 1965, perturbations of linear systems;
Khalil, *Nonlinear Systems*, 3rd ed., §9.1 (vanishing perturbations, Lyapunov form) and Lemma A.1
(Gronwall–Bellman, LeanForControl `gronwall_const`)); variation of constants
`Dynamics.eq_variationOfConstants_of_hasDerivAt`; the Floquet criterion
`Periodic.uniformlyExponentiallyStable_of_spectralRadius_lt_one`; the persistence results of
`theorem/Periodic/Persistence.lean` (`norm_transition_sub_le`, `exists_norm_gt_of_norm_det_lt`,
`schurStable_of_pow_norm_lt_one`); the two-state threshold
`ParametricResonance.UniversalThreshold.schurStable_of_threshold`.

Results.
* `exp_bound_nonneg`, `one_le_of_exp_bound`, `re_le_of_exp_bound`, `card_mul_le_neg_trace` — an
  exponential bound `‖e^{τA₀}‖ ≤ K e^{−ατ}` has `K ≥ 0` (`K ≥ 1` with a state), every eigenvalue
  has `Re μ ≤ −α`, and `nα ≤ −tr A₀`.
* `isHurwitz_iff_exists_exp_bound` — `A₀` Hurwitz iff such a bound with `α > 0` exists.
* `norm_transition_le` — `‖B(t)‖ ≤ b`: `‖Φ_{A₀+B}(t, s)‖ ≤ K e^{(Kb − α)(t − s)}`.
* `schurStable_of_transition_decay` — `‖Φ(t, 0)‖ ≤ C e^{−γt}`, `γ > 0`, for a periodic system
  gives a Schur-stable monodromy (converse of the Floquet criterion);
  `not_floquetUnstable_of_schurStable`.
* `schurStable_of_mul_lt` — `Kb < α`: Schur-stable monodromy and uniform decay for every period
  and waveform; `schurStable_of_lyapunov` — the Lyapunov form `β < q`, with
  `V(x(t)) ≤ e^{−((q − β)/p₂)(t − s)} V(x(s))`.
* `exists_floquetUnstable_of_norm_le` — an eigenvalue `Re λ > 0`: Floquet unstable for every
  continuous `B` with `sup ‖B‖ ≤ b₀` (uniform in the waveform).
* `separation` — both directions in one statement: the small-signal class is unstable for all
  small `b`; a Floquet instability with Hurwitz `A₀` forces `α ≤ Kb`, and `q ≤ β` in the Lyapunov
  form.
* `norm_oscMatrix_sub_le`, `secondOrder_schurStable` — the robust threshold for
  `m δ̈ + D δ̇ + K(t) δ = 0`; `secondOrder_robust_le_universal` — the robust condition forces
  `2εK̄ < D`, and for `m + 2D ≤ 4K̄` implies the universal condition `ε/√(1 − ε) < D/√(mK̄)`.
-/

noncomputable section
namespace powerlib.Periodic.Robust

open Set Matrix Function Filter Topology
open powerlib.Periodic
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The perturbation bound -/

section Bound

variable {A₀ : Matrix X X ℝ} {B : ℝ → Matrix X X ℝ} {K α b : ℝ}

/-- The constant of an exponential bound on `e^{τA₀}` is nonnegative (`τ = 0`). -/
@[tmio T, powerlib_foundation] theorem exp_bound_nonneg
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ))) : 0 ≤ K := by
  have h := hexp 0 le_rfl
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  exact (norm_nonneg _).trans h

/-- **Grönwall bound for a perturbed constant matrix.** If `‖e^{τA₀}‖ ≤ K e^{−ατ}` for `τ ≥ 0`
and the continuous perturbation satisfies `‖B(t)‖ ≤ b`, the transition matrix of
`ẋ = (A₀ + B(t)) x` satisfies `‖Φ(t, s)‖ ≤ K e^{(Kb − α)(t − s)}` for `s ≤ t`. Every solution
satisfies `x(t) = e^{(t−s)A₀} x(s) + ∫ₛᵗ e^{(t−r)A₀} B(r) x(r) dr`
(`Dynamics.eq_variationOfConstants_of_hasDerivAt`), so `y(t) = e^{α(t−s)} ‖x(t)‖` satisfies
`y(t) ≤ K ‖x(s)‖ + ∫ₛᵗ K b y`, and Grönwall's inequality (LeanForControl `gronwall_const`)
gives `y(t) ≤ K ‖x(s)‖ e^{Kb(t−s)}`. No periodicity of `B` is used. -/
@[tmio T, powerlib_foundation] theorem norm_transition_le
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ)))
    (hB : Continuous B) (hb : ∀ t, ‖B t‖ ≤ b) {s t : ℝ} (hst : s ≤ t) :
    ‖transition (fun r => A₀ + B r) t s‖ ≤ K * Real.exp ((K * b - α) * (t - s)) := by
  have hK : 0 ≤ K := exp_bound_nonneg hexp
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have hAc : Continuous fun r => A₀ + B r := continuous_const.add hB
  have hΦ0 : ∀ r τ, τ ≤ r → ‖transition (fun _ => A₀) r τ‖ ≤ K * Real.exp (-(α * (r - τ))) :=
    fun r τ hτr => by
      rw [transition_const A₀ hτr]; exact hexp _ (sub_nonneg.mpr hτr)
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  show ‖transition (fun r => A₀ + B r) t s *ᵥ v‖ ≤ _
  set x : ℝ → X → ℝ := fun r => transition (fun r => A₀ + B r) r s *ᵥ v with hxdef
  have hx : ∀ r, HasDerivAt x ((A₀ + B r) *ᵥ x r) r := by
    intro r
    let L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun N => N *ᵥ v
          map_add' := fun N N' => Matrix.add_mulVec N N' v
          map_smul' := fun c N => Matrix.smul_mulVec c N v }
    refine (L.hasFDerivAt.comp_hasDerivAt r (Dynamics.stm_hasDerivAt hAc r s)).congr_deriv ?_
    show ((A₀ + B r) * transition (fun r => A₀ + B r) r s) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec]
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun r => (hx r).continuousAt
  have hxs : x s = v := by simp [hxdef, LinearSystems.stateTransitionMatrix_self]
  have hvoc : ∀ r, x r = transition (fun _ => A₀) r s *ᵥ x s +
      ∫ τ in s..r, transition (fun _ => A₀) r τ *ᵥ (B τ *ᵥ x τ) := fun r =>
    Dynamics.eq_variationOfConstants_of_hasDerivAt (A := fun _ => A₀) continuous_const hB hxc
      (fun r => by simpa only [Matrix.add_mulVec] using hx r) s r
  -- the integral inequality for `y(r) = e^{α(r − s)} ‖x(r)‖`
  set y : ℝ → ℝ := fun r => Real.exp (α * (r - s)) * ‖x r‖ with hydef
  have hyc : Continuous y := by fun_prop
  have hineq : ∀ r ∈ Icc s t, y r ≤ K * ‖v‖ + ∫ τ in s..r, (K * b) * y τ := by
    intro r hr
    have hsr : s ≤ r := hr.1
    have hint : ‖∫ τ in s..r, transition (fun _ => A₀) r τ *ᵥ (B τ *ᵥ x τ)‖ ≤
        ∫ τ in s..r, K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖ := by
      have hgc : Continuous fun τ => K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖ := by fun_prop
      refine intervalIntegral.norm_integral_le_of_norm_le hsr
        (Eventually.of_forall fun τ hτ => ?_) (hgc.intervalIntegrable s r)
      calc ‖transition (fun _ => A₀) r τ *ᵥ (B τ *ᵥ x τ)‖
          ≤ ‖transition (fun _ => A₀) r τ‖ * (‖B τ‖ * ‖x τ‖) :=
            (Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) (norm_nonneg _))
        _ ≤ K * Real.exp (-(α * (r - τ))) * (b * ‖x τ‖) := by
            gcongr
            · exact hΦ0 r τ hτ.2
            · exact hb τ
        _ = K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖ := by ring
    have h1 : ‖x r‖ ≤ K * Real.exp (-(α * (r - s))) * ‖v‖ +
        ∫ τ in s..r, K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖ := by
      calc ‖x r‖ = ‖transition (fun _ => A₀) r s *ᵥ x s +
            ∫ τ in s..r, transition (fun _ => A₀) r τ *ᵥ (B τ *ᵥ x τ)‖ := by rw [← hvoc r]
        _ ≤ ‖transition (fun _ => A₀) r s *ᵥ x s‖ +
            ‖∫ τ in s..r, transition (fun _ => A₀) r τ *ᵥ (B τ *ᵥ x τ)‖ := norm_add_le _ _
        _ ≤ K * Real.exp (-(α * (r - s))) * ‖v‖ +
            ∫ τ in s..r, K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖ := by
          gcongr
          rw [hxs]
          exact (Matrix.linfty_opNorm_mulVec _ _).trans
            (mul_le_mul_of_nonneg_right (hΦ0 r s hsr) (norm_nonneg _))
    have hmul : Real.exp (α * (r - s)) *
        ∫ τ in s..r, K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖ =
          ∫ τ in s..r, (K * b) * y τ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun τ _ => ?_
      simp only [hydef]
      have e : Real.exp (α * (r - s)) * Real.exp (-(α * (r - τ))) = Real.exp (α * (τ - s)) := by
        rw [← Real.exp_add]; ring_nf
      calc Real.exp (α * (r - s)) * (K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖) =
            K * b * ((Real.exp (α * (r - s)) * Real.exp (-(α * (r - τ)))) * ‖x τ‖) := by ring
        _ = K * b * (Real.exp (α * (τ - s)) * ‖x τ‖) := by rw [e]
    have hE : Real.exp (α * (r - s)) * Real.exp (-(α * (r - s))) = 1 := by
      rw [← Real.exp_add]; simp
    calc y r = Real.exp (α * (r - s)) * ‖x r‖ := rfl
      _ ≤ Real.exp (α * (r - s)) * (K * Real.exp (-(α * (r - s))) * ‖v‖ +
            ∫ τ in s..r, K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = K * ‖v‖ * (Real.exp (α * (r - s)) * Real.exp (-(α * (r - s)))) +
            Real.exp (α * (r - s)) *
              ∫ τ in s..r, K * Real.exp (-(α * (r - τ))) * b * ‖x τ‖ := by ring
      _ = K * ‖v‖ + ∫ τ in s..r, (K * b) * y τ := by rw [hE, hmul, mul_one]
  have hg := gronwall_const (mul_nonneg hK hb0) hyc.continuousOn hineq t ⟨hst, le_rfl⟩
  have hE : Real.exp (-(α * (t - s))) * Real.exp (α * (t - s)) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖x t‖ = Real.exp (-(α * (t - s))) * y t := by
        simp only [hydef]; rw [← mul_assoc, hE, one_mul]
    _ ≤ Real.exp (-(α * (t - s))) * (K * ‖v‖ * Real.exp (K * b * (t - s))) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
    _ = K * Real.exp ((K * b - α) * (t - s)) * ‖v‖ := by
        rw [show (K * b - α) * (t - s) = -(α * (t - s)) + K * b * (t - s) by ring, Real.exp_add]
        ring


/-- **The rate of an exponential bound is below every eigenvalue.** If `‖e^{τA₀}‖ ≤ K e^{−ατ}` for
`τ ≥ 0`, every complex eigenvalue of `A₀` has `Re μ ≤ −α` (`e^{τA₀} v = e^{μτ} v`, so
`e^{(Re μ + α)τ} ≤ K` for all `τ ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem re_le_of_exp_bound
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ)))
    {μ : ℂ} {v : X → ℂ} (hv : v ≠ 0) (hAv : A₀.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    μ.re ≤ -α := by
  have hK := exp_bound_nonneg hexp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have key : ∀ τ, 0 ≤ τ → Real.exp ((μ.re + α) * τ) ≤ K := by
    intro τ hτ
    have h := monodromy_const_mulVec_eigen A₀ hτ 0 hAv
    rw [monodromy_const A₀ hτ] at h
    have hle : Real.exp (μ.re * τ) * ‖v‖ ≤ K * Real.exp (-(α * τ)) * ‖v‖ := by
      calc Real.exp (μ.re * τ) * ‖v‖ = ‖Complex.exp (μ * τ) • v‖ := by
            rw [norm_smul, norm_exp_mul_eq]
        _ = ‖(NormedSpace.exp (τ • A₀)).map (algebraMap ℝ ℂ) *ᵥ v‖ := by rw [h]
        _ ≤ ‖(NormedSpace.exp (τ • A₀)).map (algebraMap ℝ ℂ)‖ * ‖v‖ :=
            Matrix.linfty_opNorm_mulVec _ _
        _ = ‖NormedSpace.exp (τ • A₀)‖ * ‖v‖ := by rw [LTI.norm_map_algebraMap]
        _ ≤ K * Real.exp (-(α * τ)) * ‖v‖ := mul_le_mul_of_nonneg_right (hexp τ hτ) hvpos.le
    have h2 := le_of_mul_le_mul_right hle hvpos
    calc Real.exp ((μ.re + α) * τ) = Real.exp (μ.re * τ) * Real.exp (α * τ) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ K * Real.exp (-(α * τ)) * Real.exp (α * τ) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = K := by rw [mul_assoc, ← Real.exp_add]; simp
  by_contra hcon
  push Not at hcon
  have hc : 0 < μ.re + α := by linarith
  have h1 := key (K / (μ.re + α)) (div_nonneg hK hc.le)
  have h2 := Real.add_one_le_exp ((μ.re + α) * (K / (μ.re + α)))
  have e : (μ.re + α) * (K / (μ.re + α)) = K := by field_simp
  rw [e] at h1 h2
  linarith

/-- **Mean-trace margin.** The rate of every exponential bound `‖e^{τA₀}‖ ≤ K e^{−ατ}` satisfies
`n α ≤ −tr A₀` (`n` states): the trace is the sum of the eigenvalues, each with `Re μ ≤ −α`. -/
@[tmio T, powerlib_foundation] theorem card_mul_le_neg_trace
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ))) :
    Fintype.card X * α ≤ -A₀.trace := by
  set N := A₀.map (algebraMap ℝ ℂ) with hN
  have htr : N.trace.re = A₀.trace := by
    simp [hN, Matrix.trace, Complex.re_sum]
  rw [Matrix.trace_eq_sum_roots_charpoly N] at htr
  have hre : (N.charpoly.roots.sum).re = (N.charpoly.roots.map Complex.re).sum :=
    map_multiset_sum Complex.reAddGroupHom N.charpoly.roots
  have hle : (N.charpoly.roots.map Complex.re).sum ≤
      (N.charpoly.roots.map fun _ => -α).sum :=
    Multiset.sum_map_le_sum_map _ _ fun μ hμ => by
      obtain ⟨v, hv, hNv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp (mem_spectrum_of_mem_roots hμ)
      exact re_le_of_exp_bound hexp hv hNv
  rw [Multiset.map_const', Multiset.sum_replicate, card_roots_charpoly, nsmul_eq_mul] at hle
  linarith

/-- The constant of an exponential bound is at least one when there is a state (`τ = 0`). -/
@[tmio T, powerlib_foundation] theorem one_le_of_exp_bound [Nonempty X]
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ))) : 1 ≤ K := by
  have h := hexp 0 le_rfl
  simpa using h

end Bound

/-! ## Hurwitz matrices have exponential bounds -/

/-- **Hurwitz iff an exponential bound.** A real matrix is Hurwitz iff
`‖e^{τA₀}‖ ≤ K e^{−ατ}` (`L∞` operator norm) for some `K` and `α > 0`. The bound is the Floquet
criterion `uniformlyExponentiallyStable_of_spectralRadius_lt_one` for the constant matrix (any
period, `ρ(e^{A₀}) < 1` by `LTI.isHurwitz_iff_schurStable_exp`); the converse is
`re_le_of_exp_bound`. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_exists_exp_bound {n : ℕ}
    (A₀ : Matrix (Fin n) (Fin n) ℝ) :
    LinearSystems.IsHurwitz A₀ ↔ ∃ K α : ℝ, 0 < α ∧
      ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ)) := by
  constructor
  · intro hH
    obtain ⟨K, β, hβ, hK⟩ := uniformlyExponentiallyStable_of_spectralRadius_lt_one
      (A := fun _ => A₀) continuous_const (fun _ => rfl : Periodic (fun _ : ℝ => A₀) 1) one_pos
      (ParametricResonance.Signature.spectralRadius_monodromy_const_lt_one hH one_pos)
    refine ⟨K, β, hβ, fun τ hτ => ?_⟩
    have h := hK 0 τ hτ
    rwa [transition_const A₀ hτ, sub_zero] at h
  · rintro ⟨K, α, hα, hexp⟩ μ v hv hAv
    have := re_le_of_exp_bound hexp hv hAv
    show μ.re < -0
    linarith

/-! ## Uniform decay gives Floquet stability -/

/-- **Converse of the Floquet criterion.** A continuous `T`-periodic system whose transition
matrix decays uniformly, `‖Φ(t, 0)‖ ≤ C e^{−γt}` (`γ > 0`, `t ≥ 0`), has a Schur-stable monodromy
matrix: `M^k = Φ(kT, 0)` is contractive for large `k` (`schurStable_of_pow_norm_lt_one`). -/
@[tmio T, powerlib_foundation] theorem schurStable_of_transition_decay {n : ℕ}
    {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {T C γ : ℝ} (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) (hγ : 0 < γ)
    (hb : ∀ t, 0 ≤ t → ‖transition A t 0‖ ≤ C * Real.exp (-(γ * t))) :
    LTI.SchurStable (monodromy A T 0) := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  have h1 : Tendsto (fun k : ℕ => γ * (k * T)) atTop atTop :=
    Tendsto.const_mul_atTop hγ (tendsto_natCast_atTop_atTop.atTop_mul_const hT)
  have hlim : Tendsto (fun k : ℕ => C * Real.exp (-(γ * (k * T)))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
  obtain ⟨k, hk1, hk0⟩ := ((hlim.eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine schurStable_of_pow_norm_lt_one hk0 ?_
  rw [← transition_add_nat_mul_period hA hM hT.le hP 0 k, zero_add]
  exact (hb _ (by positivity)).trans_lt hk1

/-- `Schur stable` excludes `Floquet unstable`. -/
@[tmio T, powerlib_foundation] theorem not_floquetUnstable_of_schurStable {n : ℕ}
    {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {T : ℝ} (h : LTI.SchurStable (monodromy A T 0)) :
    ¬ FloquetUnstable A T := by
  rintro ⟨μ, hμ, hμ1⟩
  obtain ⟨v, hv, hMv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
  exact absurd (h μ v hv hMv) (not_lt.mpr hμ1.le)

/-! ## The robust threshold -/

section Threshold

variable {n : ℕ} {A₀ : Matrix (Fin n) (Fin n) ℝ} {K α b T : ℝ}

/-- **The robust threshold.** If `‖e^{τA₀}‖ ≤ K e^{−ατ}` and `K b < α` (that is `b < α/K`), then for
every period `T > 0` and every continuous `T`-periodic modulation with `‖B(t)‖ ≤ b` — any
waveform, any frequency — the system `ẋ = (A₀ + B(t)) x` has a Schur-stable monodromy matrix and
decays uniformly, `‖Φ(t, s)‖ ≤ K e^{−(α − Kb)(t − s)}` (`norm_transition_le`,
`schurStable_of_transition_decay`). -/
@[tmio T, powerlib_foundation] theorem schurStable_of_mul_lt
    (hexp : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ)))
    (hlt : K * b < α) (hT : 0 < T) {B : ℝ → Matrix (Fin n) (Fin n) ℝ} (hB : Continuous B)
    (hBP : Periodic B T) (hb : ∀ t, ‖B t‖ ≤ b) :
    LTI.SchurStable (monodromy (fun t => A₀ + B t) T 0) ∧
      ∀ s t, s ≤ t → ‖transition (fun r => A₀ + B r) t s‖ ≤
        K * Real.exp (-((α - K * b) * (t - s))) := by
  have hdec : ∀ s t, s ≤ t → ‖transition (fun r => A₀ + B r) t s‖ ≤
      K * Real.exp (-((α - K * b) * (t - s))) := fun s t hst => by
    have h := norm_transition_le hexp hB hb hst
    rwa [show (K * b - α) * (t - s) = -((α - K * b) * (t - s)) by ring] at h
  refine ⟨schurStable_of_transition_decay (C := K) (γ := α - K * b) (continuous_const.add hB)
    (fun t => by simp only [hBP t]) hT (by linarith) fun t ht => ?_, hdec⟩
  simpa using hdec 0 t ht

/-- **Lyapunov form of the robust threshold.** Let `P = Pᵀ` and `Q` satisfy the Lyapunov
equation `A₀ᵀ P + P A₀ = −Q` with `p₁ |x|² ≤ xᵀPx ≤ p₂ |x|²` and `xᵀQx ≥ q |x|²`, and let the
modulation satisfy `xᵀ (P B(t) + B(t)ᵀ P) x ≤ β |x|²` with `β < q` (in spectral terms
`sup_t λ_max(PB + BᵀP) < λ_min(Q)`). Then for every period and waveform the monodromy matrix of
`ẋ = (A₀ + B(t)) x` is Schur stable, and along every solution
`V(x(t)) ≤ e^{−((q − β)/p₂)(t − s)} V(x(s))`, `V(x) = xᵀPx`. -/
@[tmio T, powerlib_foundation] theorem schurStable_of_lyapunov {P Q : Matrix (Fin n) (Fin n) ℝ}
    {p₁ p₂ q β : ℝ} (hPs : Pᵀ = P) (hlyap : A₀ᵀ * P + P * A₀ = -Q) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hP₁ : ∀ x, p₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) (hP₂ : ∀ x, x ⬝ᵥ (P *ᵥ x) ≤ p₂ * (x ⬝ᵥ x))
    (hQ : ∀ x, q * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x)) (hβq : β < q) (hT : 0 < T)
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} (hB : Continuous B) (hBP : Periodic B T)
    (hβ : ∀ t x, x ⬝ᵥ ((P * B t + (B t)ᵀ * P) *ᵥ x) ≤ β * (x ⬝ᵥ x)) :
    LTI.SchurStable (monodromy (fun t => A₀ + B t) T 0) ∧
      ∀ x : ℝ → Fin n → ℝ, (∀ t, HasDerivAt x ((A₀ + B t) *ᵥ x t) t) → ∀ s t, s ≤ t →
        x t ⬝ᵥ (P *ᵥ x t) ≤ Real.exp (-((q - β) / p₂ * (t - s))) * (x s ⬝ᵥ (P *ᵥ x s)) := by
  set c := (q - β) / p₂ with hc
  have hc0 : 0 < c := div_pos (by linarith) hp₂
  -- `xᵀ (Nᵀ P + P N) x = 2 xᵀ P N x` for symmetric `P`
  have hsym : ∀ (N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ),
      x ⬝ᵥ ((Nᵀ * P + P * N) *ᵥ x) = 2 * (x ⬝ᵥ (P *ᵥ (N *ᵥ x))) := by
    intro N x
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Nᵀ,
      vecMul_transpose, Criteria.dotProduct_mulVec_comm_of_symm hPs (N *ᵥ x) x]
    ring
  have hdecay : ∀ x : ℝ → Fin n → ℝ, (∀ t, HasDerivAt x ((A₀ + B t) *ᵥ x t) t) → ∀ s t, s ≤ t →
      x t ⬝ᵥ (P *ᵥ x t) ≤ Real.exp (-(c * (t - s))) * (x s ⬝ᵥ (P *ᵥ x s)) := by
    intro x hx s t hst
    have hV : ∀ r, HasDerivAt (fun r => x r ⬝ᵥ (P *ᵥ x r))
        (2 * (x r ⬝ᵥ (P *ᵥ ((A₀ + B r) *ᵥ x r)))) r := fun r =>
      SingularPerturbation.hasDerivAt_quadratic_of_symm hPs (hx r)
    have hle : ∀ r, 2 * (x r ⬝ᵥ (P *ᵥ ((A₀ + B r) *ᵥ x r))) ≤ -c * (x r ⬝ᵥ (P *ᵥ x r)) := by
      intro r
      have e : 2 * (x r ⬝ᵥ (P *ᵥ ((A₀ + B r) *ᵥ x r))) =
          -(x r ⬝ᵥ (Q *ᵥ x r)) + x r ⬝ᵥ ((P * B r + (B r)ᵀ * P) *ᵥ x r) := by
        rw [← hsym, transpose_add,
          show (A₀ᵀ + (B r)ᵀ) * P + P * (A₀ + B r) =
            (A₀ᵀ * P + P * A₀) + (P * B r + (B r)ᵀ * P) by noncomm_ring, hlyap, add_mulVec,
          dotProduct_add, neg_mulVec, dotProduct_neg]
      rw [e]
      have h1 := hQ (x r)
      have h2 := hβ r (x r)
      have h3 := hP₂ (x r)
      have h4 : c * (x r ⬝ᵥ (P *ᵥ x r)) ≤ (q - β) * (x r ⬝ᵥ x r) := by
        calc c * (x r ⬝ᵥ (P *ᵥ x r)) ≤ c * (p₂ * (x r ⬝ᵥ x r)) :=
              mul_le_mul_of_nonneg_left h3 hc0.le
          _ = (q - β) * (x r ⬝ᵥ x r) := by rw [hc]; field_simp
      nlinarith
    have h := Dynamics.le_exp_mul_of_hasDerivWithinAt (g := fun r => x r ⬝ᵥ (P *ᵥ x r))
      (ρ := c) (t₀ := s) (t₁ := t) (fun r _ => (hV r).hasDerivWithinAt) (fun r _ => hle r) t
      ⟨hst, le_rfl⟩
    simpa only [neg_mul] using h
  refine ⟨?_, hdecay⟩
  -- the transition matrix decays in the sup norm
  set C := (n : ℝ) * (p₂ / p₁) with hC
  have hC0 : 0 ≤ C := by positivity
  have hAc : Continuous fun t => A₀ + B t := continuous_const.add hB
  refine schurStable_of_transition_decay hAc (fun t => by simp only [hBP t]) hT
    (half_pos hc0) (C := √C) fun t ht => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  show ‖transition (fun t => A₀ + B t) t 0 *ᵥ w‖ ≤ _
  have hsol := hasDerivAt_transition_mulVec hAc w
  have hd := hdecay _ hsol 0 t ht
  simp only [LinearSystems.stateTransitionMatrix_self, Matrix.one_mulVec, sub_zero] at hd
  set y := transition (fun t => A₀ + B t) t 0 *ᵥ w
  have hy1 := SingularPerturbation.norm_sq_le_dotProduct_self y
  have hy2 := hP₁ y
  have hw1 := hP₂ w
  have hw2 := SingularPerturbation.dotProduct_self_le_card_mul_norm_sq w
  have hE : 0 < Real.exp (-(c * t)) := Real.exp_pos _
  have hsq : ‖y‖ ^ 2 ≤ (√C * Real.exp (-(c / 2 * t)) * ‖w‖) ^ 2 := by
    have e1 : (√C * Real.exp (-(c / 2 * t)) * ‖w‖) ^ 2 = C * Real.exp (-(c * t)) * ‖w‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC0, ← Real.exp_nat_mul]
      ring_nf
    rw [e1]
    have : p₁ * ‖y‖ ^ 2 ≤ p₁ * (C * Real.exp (-(c * t)) * ‖w‖ ^ 2) := by
      calc p₁ * ‖y‖ ^ 2 ≤ p₁ * (y ⬝ᵥ y) := mul_le_mul_of_nonneg_left hy1 hp₁.le
        _ ≤ y ⬝ᵥ (P *ᵥ y) := hy2
        _ ≤ Real.exp (-(c * t)) * (w ⬝ᵥ (P *ᵥ w)) := hd
        _ ≤ Real.exp (-(c * t)) * (p₂ * (n * ‖w‖ ^ 2)) := by
            gcongr
            exact hw1.trans (mul_le_mul_of_nonneg_left hw2 hp₂.le)
        _ = p₁ * (C * Real.exp (-(c * t)) * ‖w‖ ^ 2) := by rw [hC]; field_simp
    exact le_of_mul_le_mul_left this hp₁
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end Threshold

/-! ## Small-signal instability persists, uniformly in the waveform -/

/-- **Small-signal instability is robust.** If `A₀` has an eigenvalue with `Re λ > 0`, then for every
`T > 0` there is `b₀ > 0` such that `ẋ = (A₀ + B(t)) x` is Floquet unstable for every continuous
`B` with `‖B(t)‖ ≤ b₀`, whatever its waveform (the Grönwall estimate `norm_transition_sub_le`
makes `‖M_B − e^{TA₀}‖ ≤ b₀ T ‖I‖ e^{(2‖A₀‖ + b₀)T}` uniform in `B`, and
`exists_norm_gt_of_norm_det_lt` turns `det(e^{λT} I − M_B) ≈ 0` into a multiplier outside the unit
circle). This is the waveform-uniform form of `Periodic.exists_floquetUnstable_of_re_pos`. -/
@[tmio T, powerlib_foundation] theorem exists_floquetUnstable_of_norm_le {A₀ : Matrix X X ℝ}
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ))) (hre : 0 < lam.re) {T : ℝ}
    (hT : 0 < T) :
    ∃ b₀ > 0, ∀ B : ℝ → Matrix X X ℝ, Continuous B → (∀ t, ‖B t‖ ≤ b₀) →
      FloquetUnstable (fun t => A₀ + B t) T := by
  set z := Complex.exp (lam * T) with hz
  have hz1 : 1 < ‖z‖ := by
    rw [hz, norm_exp_mul_eq]; exact Real.one_lt_exp_iff.mpr (mul_pos hre hT)
  obtain ⟨v, hv, hAv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hlam
  set N₀ := monodromy (fun _ => A₀) T 0 with hN₀
  have hz0 : (Matrix.scalar X z - N₀.map (algebraMap ℝ ℂ)).det = 0 := by
    have h := monodromy_const_mulVec_eigen A₀ hT.le 0 hAv
    have hmem : z ∈ spectrum ℂ (N₀.map (algebraMap ℝ ℂ)) :=
      LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, h⟩
    rw [← Matrix.eval_charpoly]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hmem
  set f : Matrix X X ℝ → ℂ := fun N => (Matrix.scalar X z - N.map (algebraMap ℝ ℂ)).det with hf
  have hcont : Continuous f :=
    (continuous_const.sub (continuous_id.matrix_map (continuous_algebraMap ℝ ℂ))).matrix_det
  have hpos : 0 < (‖z‖ - 1) ^ Fintype.card X := pow_pos (by linarith) _
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcont N₀ _ hpos
  set C := T * ‖(1 : Matrix X X ℝ)‖ * Real.exp ((2 * ‖A₀‖ + 1) * T) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨min 1 (δ / (C + 1)), lt_min one_pos (div_pos hδ (by linarith)), fun B hB hb => ?_⟩
  set b₀ := min 1 (δ / (C + 1)) with hb₀
  have hb1 : b₀ ≤ 1 := min_le_left _ _
  have hb2 : b₀ ≤ δ / (C + 1) := min_le_right _ _
  have hb0 : 0 ≤ b₀ := (norm_nonneg _).trans (hb 0)
  have hdiff := norm_transition_sub_le (A := fun t => A₀ + B t) (B := fun _ => A₀)
    (MA := ‖A₀‖ + b₀) (MB := ‖A₀‖) (η := b₀) (continuous_const.add hB) continuous_const
    (fun t => (norm_add_le _ _).trans (add_le_add le_rfl (hb t))) (fun _ => le_rfl)
    (fun t => by rw [add_sub_cancel_left]; exact hb t) (s := 0) (t := 0 + T) (by linarith)
  have hM : dist (monodromy (fun t => A₀ + B t) T 0) N₀ < δ := by
    rw [dist_eq_norm, hN₀]
    simp only [monodromy]
    refine hdiff.trans_lt ?_
    have hexp : Real.exp ((‖A₀‖ + b₀ + ‖A₀‖) * (0 + T - 0)) ≤
        Real.exp ((2 * ‖A₀‖ + 1) * T) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc b₀ * (0 + T - 0) * ‖(1 : Matrix X X ℝ)‖ *
          Real.exp ((‖A₀‖ + b₀ + ‖A₀‖) * (0 + T - 0)) ≤ b₀ * C := by
          rw [hC, show (0 : ℝ) + T - 0 = T by ring]
          have : 0 ≤ b₀ * T * ‖(1 : Matrix X X ℝ)‖ := by positivity
          calc b₀ * T * ‖(1 : Matrix X X ℝ)‖ * Real.exp ((‖A₀‖ + b₀ + ‖A₀‖) * T)
              ≤ b₀ * T * ‖(1 : Matrix X X ℝ)‖ * Real.exp ((2 * ‖A₀‖ + 1) * T) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) this
            _ = b₀ * (T * ‖(1 : Matrix X X ℝ)‖ * Real.exp ((2 * ‖A₀‖ + 1) * T)) := by ring
      _ ≤ δ / (C + 1) * C := mul_le_mul_of_nonneg_right hb2 hC0
      _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
  have hfM := hball _ hM
  rw [dist_eq_norm] at hfM
  have hf0 : f N₀ = 0 := hz0
  rw [hf0, sub_zero] at hfM
  exact exists_norm_gt_of_norm_det_lt hz1 hfM

/-! ## The separation in (spectrum, modulation size) space -/

/-- **Separation of small-signal and parametric instability, `n` states.** For a constant matrix
`A₀` and a pump period `T > 0`:
* (small-signal class) if `A₀` has an eigenvalue with `Re λ > 0`, every modulation of size
  `sup ‖B‖ ≤ b₀` is Floquet unstable, for some `b₀ > 0` and every waveform;
* (parametric class) if `‖e^{τA₀}‖ ≤ K e^{−ατ}` (possible with `α > 0` exactly when `A₀` is
  Hurwitz, `isHurwitz_iff_exists_exp_bound`), a Floquet instability of a continuous `T`-periodic
  modulation with `sup ‖B‖ ≤ b` forces `α ≤ K b`, i.e. `b ≥ α/K`;
* (Lyapunov form) with `A₀ᵀP + PA₀ = −Q` as in `schurStable_of_lyapunov`, a Floquet instability
  forces `β ≥ q`: the modulation `PB + BᵀP` reaches `λ_min(Q)`.
The two classes are disjoint (`re_le_of_exp_bound`), and in the plane (spectral abscissa of
`A₀`, `b`) the parametric class lies on or above the curve `b = α/K`. -/
@[tmio T, powerlib_foundation] theorem separation {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ) {T : ℝ}
    (hT : 0 < T) :
    ((∃ lam ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ)), 0 < lam.re) →
      ∃ b₀ > 0, ∀ B : ℝ → Matrix (Fin n) (Fin n) ℝ, Continuous B → (∀ t, ‖B t‖ ≤ b₀) →
        FloquetUnstable (fun t => A₀ + B t) T) ∧
    (∀ K α b : ℝ, (∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • A₀)‖ ≤ K * Real.exp (-(α * τ))) →
      ∀ B : ℝ → Matrix (Fin n) (Fin n) ℝ, Continuous B → Periodic B T → (∀ t, ‖B t‖ ≤ b) →
        FloquetUnstable (fun t => A₀ + B t) T → α ≤ K * b) ∧
    (∀ (P Q : Matrix (Fin n) (Fin n) ℝ) (p₁ p₂ q β : ℝ), Pᵀ = P → A₀ᵀ * P + P * A₀ = -Q →
      0 < p₁ → 0 < p₂ → (∀ x, p₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) →
      (∀ x, x ⬝ᵥ (P *ᵥ x) ≤ p₂ * (x ⬝ᵥ x)) → (∀ x, q * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x)) →
      ∀ B : ℝ → Matrix (Fin n) (Fin n) ℝ, Continuous B → Periodic B T →
        (∀ t x, x ⬝ᵥ ((P * B t + (B t)ᵀ * P) *ᵥ x) ≤ β * (x ⬝ᵥ x)) →
        FloquetUnstable (fun t => A₀ + B t) T → q ≤ β) := by
  refine ⟨fun ⟨lam, hlam, hre⟩ => exists_floquetUnstable_of_norm_le hlam hre hT, ?_, ?_⟩
  · intro K α b hexp B hB hBP hb hun
    by_contra hlt
    push Not at hlt
    exact not_floquetUnstable_of_schurStable (schurStable_of_mul_lt hexp hlt hT hB hBP hb).1 hun
  · intro P Q p₁ p₂ q β hPs hlyap hp₁ hp₂ hP₁ hP₂ hQ B hB hBP hβ hun
    by_contra hlt
    push Not at hlt
    exact not_floquetUnstable_of_schurStable
      (schurStable_of_lyapunov hPs hlyap hp₁ hp₂ hP₁ hP₂ hQ hlt hT hB hBP hβ).1 hun

/-! ## Comparison with the two-state universal threshold -/

section SecondOrder

/-- A change of stiffness is a perturbation of size `|k − k'|`:
`‖oscMatrix c k − oscMatrix c k'‖ ≤ |k − k'|` (`L∞` operator norm). -/
@[tmio T, powerlib_foundation] theorem norm_oscMatrix_sub_le (c k k' : ℝ) :
    ‖oscMatrix c k - oscMatrix c k'‖ ≤ |k - k'| := by
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun v => ?_
  show ‖(oscMatrix c k - oscMatrix c k') *ᵥ v‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hv0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  fin_cases i
  · simp [oscMatrix, Matrix.mulVec, dotProduct]; positivity
  · simp only [oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
    simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, sub_self, zero_mul,
      add_zero, Real.norm_eq_abs]
    rw [show -k - -k' = -(k - k') by ring, abs_mul, abs_neg]
    rw [Real.norm_eq_abs] at hv0
    exact mul_le_mul_of_nonneg_left hv0 (abs_nonneg _)

variable {m D Kbar ε Kc α : ℝ}

/-- **The robust threshold for the second-order model.** For `m δ̈ + D δ̇ + K(t) δ = 0` in the
state `(δ, δ̇)` with `|K(t) − K̄| ≤ εK̄`, the state matrix is `A₀ + B(t)` with
`A₀ = oscMatrix (D/(2m)) (K̄/m)` and `‖B(t)‖ ≤ εK̄/m`; any exponential bound
`‖e^{τA₀}‖ ≤ K_c e^{−ατ}` with `K_c εK̄/m < α` gives a Schur-stable monodromy for every period
and waveform (`schurStable_of_mul_lt`). -/
@[tmio T, powerlib_foundation] theorem secondOrder_schurStable {T : ℝ} {K : ℝ → ℝ} (hm : 0 < m)
    (hexp : ∀ τ, 0 ≤ τ →
      ‖NormedSpace.exp (τ • oscMatrix (D / (2 * m)) (Kbar / m))‖ ≤ Kc * Real.exp (-(α * τ)))
    (hrob : Kc * (ε * Kbar / m) < α) (hT : 0 < T) (hK : Continuous K) (hKP : Periodic K T)
    (hdev : ∀ t, |K t - Kbar| ≤ ε * Kbar) :
    LTI.SchurStable (monodromy (fun t => oscMatrix (D / (2 * m)) (K t / m)) T 0) := by
  set A₀ := oscMatrix (D / (2 * m)) (Kbar / m)
  have hAc : Continuous fun t => oscMatrix (D / (2 * m)) (K t / m) := by
    simp only [oscMatrix]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hBc : Continuous fun t => oscMatrix (D / (2 * m)) (K t / m) - A₀ :=
    hAc.sub continuous_const
  have h := (schurStable_of_mul_lt hexp hrob hT hBc (fun t => by simp only [hKP t])
    (fun t => (norm_oscMatrix_sub_le _ _ _).trans (by
      rw [← sub_div, abs_div, abs_of_pos hm]
      exact div_le_div_of_nonneg_right (hdev t) hm.le))).1
  simpa only [add_sub_cancel] using h

/-- **Which threshold is sharper for the second-order model.** In the state `(δ, δ̇)`, every
exponential bound of `A₀ = oscMatrix (D/(2m)) (K̄/m)` has `K_c ≥ 1` and `α ≤ D/(2m)`
(`one_le_of_exp_bound`, `card_mul_le_neg_trace`: `2α ≤ −tr A₀ = D/m`), so the robust condition
`K_c εK̄/m < α` certifies only depths `2εK̄ < D` (`ε < ξ/ω₀` with `ξ = D/(2√(mK̄))`,
`ω₀ = √(K̄/m)`). If moreover `m + 2D ≤ 4K̄` (in the time unit `ω₀ = 1`: `ξ ≤ 3/4`), every such
depth also satisfies the universal two-state condition `ε/√(1 − ε) < D/√(mK̄)` of
`ParametricResonance.UniversalThreshold.schurStable_of_threshold`: there the universal threshold
is the sharper one (at small `ξ` it allows `ε ≈ 2ξ`, the robust one at most `ε < ξ`). The robust
threshold instead covers every perturbation matrix (damping modulation included), every
dimension and non-periodic modulations. -/
@[tmio T, powerlib_foundation] theorem secondOrder_robust_le_universal (hm : 0 < m)
    (hKbar : 0 < Kbar) (hε : 0 ≤ ε)
    (hexp : ∀ τ, 0 ≤ τ →
      ‖NormedSpace.exp (τ • oscMatrix (D / (2 * m)) (Kbar / m))‖ ≤ Kc * Real.exp (-(α * τ)))
    (hrob : Kc * (ε * Kbar / m) < α) :
    2 * ε * Kbar < D ∧ (m + 2 * D ≤ 4 * Kbar → ε / √(1 - ε) < D / √(m * Kbar)) := by
  have hK1 := one_le_of_exp_bound hexp
  have htr := card_mul_le_neg_trace hexp
  rw [trace_oscMatrix, Fintype.card_fin] at htr
  have hb0 : 0 ≤ ε * Kbar / m := by positivity
  have h1 : ε * Kbar / m ≤ Kc * (ε * Kbar / m) := le_mul_of_one_le_left hb0 hK1
  have hlt : ε * Kbar / m < D / (2 * m) := by push_cast at htr; linarith
  have hmain : 2 * ε * Kbar < D := by
    rw [div_lt_div_iff₀ hm (by positivity)] at hlt
    nlinarith
  refine ⟨hmain, fun hmD => ?_⟩
  have hD : 0 < D := by nlinarith
  have h1ε : m < 4 * Kbar * (1 - ε) := by nlinarith
  have hε1 : 0 < 1 - ε := by
    by_contra h; push Not at h; nlinarith
  have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr hε1
  have hs2 : 0 < √(m * Kbar) := Real.sqrt_pos.mpr (by positivity)
  rw [div_lt_div_iff₀ hs1 hs2]
  have hsq : ε ^ 2 * (m * Kbar) < D ^ 2 * (1 - ε) := by
    have hA : 0 < 4 * Kbar * (1 - ε) - m := by linarith
    have hB : 0 ≤ D ^ 2 - 4 * ε ^ 2 * Kbar ^ 2 := by
      have h2 : 0 ≤ 2 * ε * Kbar := by positivity
      have := pow_le_pow_left₀ h2 hmain.le 2
      nlinarith
    have hC : 4 * Kbar * (ε ^ 2 * (m * Kbar)) < 4 * Kbar * (D ^ 2 * (1 - ε)) := by
      nlinarith [mul_pos hA (pow_pos hD 2), mul_nonneg hm.le hB]
    exact lt_of_mul_lt_mul_left hC (by positivity)
  have hl : 0 ≤ ε * √(m * Kbar) := by positivity
  have hr : 0 ≤ D * √(1 - ε) := by positivity
  refine (pow_lt_pow_iff_left₀ hl hr two_ne_zero).mp ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hε1.le]
  exact hsq

end SecondOrder

end powerlib.Periodic.Robust
