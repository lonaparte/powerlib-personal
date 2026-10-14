import theorem.Flow.Certificate
import theorem.Dynamics.Linearization
import theorem.Linear.Stability
import theorem.Dynamics.Locality

/-! # Converse linearization: local exponential stability forces a Hurwitz Jacobian

Generic foundation, independent of any model. Setting: an autonomous continuous-time field
`f : ℝⁿ → ℝⁿ` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `C¹` on all of `ℝⁿ` (`ContDiff ℝ 1 f`), a point
`x*` and a matrix `A` with `fderiv ℝ f x* = A` (acting through `Matrix.toEuclideanCLM`). Local
exponential stability is LeanForControl's `LocallyExponentiallyStable` — the Flow sentence
`.locallyExponentiallyStable`, quantified over finite forward solution segments. No `C²`
hypothesis and no Lipschitz bound on the Jacobian are needed.

* `isEquilibrium_of_lyapunovStable`, `isEquilibrium_of_locallyExponentiallyStable`: a Lyapunov
  stable (in particular a locally exponentially stable) point of a `C¹` field is an equilibrium;
  `unstable_of_ne_zero`: every other point is unstable (instability is the failure of Lyapunov
  stability).
* `norm_exp_le_of_locallyExponentiallyStable`: the exponential estimate
  `‖φ(t) − x*‖ ≤ C e^{−a (t − t₀)} ‖φ(t₀) − x*‖` passes, with the same `C` and `a`, to every
  solution of the linearization: `‖e^{T A} w‖ ≤ C e^{−a T} ‖w‖` for all `w` and `T ≥ 0`.
* `isHurwitz_of_locallyExponentiallyStable` (**converse linearization**): local exponential
  stability gives a Hurwitz Jacobian.
* `locallyExponentiallyStable_iff_isHurwitz_jacobian`: with the direct theorem
  (`Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian`, LeanForControl), local exponential
  stability holds exactly when `x*` is an equilibrium with a Hurwitz Jacobian;
  `locallyExponentiallyStable_iff_isHurwitz_of_eq` at a known equilibrium.
* `not_locallyExponentiallyStable_of_firstIntegral`: a `C¹` field with a nonzero linear first
  integral (`ℓ ∘ f = 0`) has no locally exponentially stable point (its Jacobian is singular,
  `mulVec_ne_zero_of_isHurwitz`, `toEuclideanCLM_injective_of_isHurwitz`).
* `fderiv_injective_of_locallyExponentiallyStable`: the Jacobian at a locally exponentially
  stable point is injective.
* Fields that are `C¹` only on an open neighbourhood `U` of the point (e.g. power-balance fields
  with a `1/V_dc` factor): `isHurwitz_of_locallyExponentiallyStable_local`,
  `locallyExponentiallyStable_iff_isHurwitz_jacobian_local`, and
  `not_locallyExponentiallyStable_of_fderiv_apply_eq_zero_local` (a direction killed by the
  Jacobian), through the locality lemmas `locallyExponentiallyStable_congr_nhds` and
  `exists_contDiff_eventuallyEq` of `theorem/Dynamics/Locality.lean`.

Proof (no converse Lyapunov theorem). A smooth cutoff makes `f` globally Lipschitz without changing
it within distance one of `x*` (`Flow.exists_lipschitz_cutoff`), so the solution `ψ_ε` through
`x* + ε w` exists for all forward time (`Flow.forwardComplete_of_lipschitzWith`, LeanForControl's
Picard–Lindelöf). Grönwall's comparison of exact solutions (Mathlib's
`dist_le_of_trajectories_ODE`) keeps it within `ε ‖w‖ e^{K T}` of `x*` on `[0, T]`, so for small
`ε` it is a solution segment of `f` itself and lies where `f(x) = A (x − x*) + o(‖x − x*‖)` is within
`η ‖x − x*‖` of its linear part. Grönwall's comparison of approximate solutions (Mathlib's
`dist_le_of_approx_trajectories_ODE`) then bounds the distance from `ψ_ε(T)` to the linear solution
`x* + ε e^{T A} w` by `ε η` times a constant independent of `ε`. Dividing the exponential estimate
for `ψ_ε` by `ε` and letting `η → 0` gives the estimate for `e^{T A} w`. The linear field
`y' = A (y − x*)` is then locally exponentially stable, hence `A` is Hurwitz by the linear hub
(`Linear.holds_iff_isHurwitz`, a non-decaying eigenmode).

Boundaries. Only local exponential stability is decided by the linearization: local asymptotic
stability is not (the cubic field `x' = −x³` is globally asymptotically stable with Jacobian `0`),
and neither is instability at a spectrum on the imaginary axis. Model families publish the
resulting exactness of their local exponential translations as connection statements.

Source: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.15 (the converse part: exponential
stability of `x*` implies that the linearization is Hurwitz); the proof here replaces the converse
Lyapunov function of Khalil by a direct Grönwall comparison. -/

noncomputable section

namespace powerlib.Dynamics

open Set Filter Topology Metric Matrix LinearSystems NormedSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- With no initial offset the Grönwall bound is linear in the forcing. -/
@[powerlib_foundation] theorem gronwallBound_zero_eq_mul (K ε x : ℝ) :
    gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  unfold gronwallBound
  split_ifs <;> ring

/-- A smooth cutoff of a `C¹` field: globally Lipschitz and equal to the field within distance one
of a given point. -/
@[powerlib_foundation] theorem exists_lipschitz_cutoff_near {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 1 f)
    (x_eq : ℝⁿ) :
    ∃ (g : ℝⁿ → ℝⁿ) (K : NNReal), LipschitzWith K g ∧ ∀ x, dist x x_eq ≤ 1 → g x = f x := by
  obtain ⟨χ, -, hχ, K, hK⟩ := Flow.exists_lipschitz_cutoff hf (‖x_eq‖ + 1)
  refine ⟨fun x => χ x • f x, K, hK, fun x hx => ?_⟩
  have hx' : ‖x‖ ≤ ‖x_eq‖ + 1 := by
    have h := norm_le_norm_add_norm_sub' x x_eq
    rw [← dist_eq_norm] at h
    linarith
  simp only [hχ x hx', one_smul]

/-- A solution of the cutoff field that stays within distance one of the point is a solution
segment of the field itself. -/
@[powerlib_foundation] theorem isTrajectoryOn_of_cutoff {f g : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (hg : ∀ x, dist x x_eq ≤ 1 → g x = f x) {ψ : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ x => g x) (Ici t₀))
    (hin : ∀ t ∈ Icc t₀ t₁, dist (ψ t) x_eq ≤ 1) : IsTrajectoryOn ψ f t₀ t₁ := by
  intro t ht
  have h := (hψ t ht.1).mono (Icc_subset_Ici_self : Icc t₀ t₁ ⊆ Ici t₀)
  show HasDerivWithinAt ψ (f (ψ t)) (Icc t₀ t₁) t
  rw [← hg _ (hin t ht)]
  exact h

/-- A Lyapunov stable point of a `C¹` field is an equilibrium: the solution through it exists for
a short time and stays in every neighbourhood of the point. -/
@[powerlib_foundation] theorem isEquilibrium_of_lyapunovStable {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (h : LyapunovStable f x_eq) : IsEquilibrium f x_eq := by
  obtain ⟨g, K, hK, hg⟩ := exists_lipschitz_cutoff_near hf x_eq
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hK 0 x_eq
  have hc : ContinuousWithinAt ψ (Ici 0) 0 := hψ.continuousWithinAt self_mem_Ici
  obtain ⟨τ, hτ, hτb⟩ := Metric.continuousWithinAt_iff.mp hc 1 one_pos
  set s := τ / 2 with hs_def
  have hs : 0 < s := half_pos hτ
  have hs0 : (0 : ℝ) ∈ Icc 0 s := left_mem_Icc.mpr hs.le
  have hin : ∀ t ∈ Icc 0 s, dist (ψ t) x_eq ≤ 1 := fun t ht => by
    rw [← hψ0]
    refine (hτb ht.1 ?_).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  have htraj := isTrajectoryOn_of_cutoff hg hψ hin
  have hconst : ∀ t ∈ Icc 0 s, ψ t = x_eq := fun t ht => by
    by_contra hne
    have hpos : 0 < ‖ψ t - x_eq‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨δ, hδ, hb⟩ := h _ hpos
    exact lt_irrefl _ (hb 0 s ψ htraj (by rw [hψ0, sub_self, norm_zero]; exact hδ) t ht)
  have hd1 : HasDerivWithinAt ψ (f x_eq) (Icc 0 s) 0 := by
    have := htraj 0 hs0
    rwa [hψ0] at this
  have hd2 : HasDerivWithinAt ψ 0 (Icc 0 s) 0 :=
    (hasDerivWithinAt_const 0 (Icc 0 s) x_eq).congr (fun t ht => hconst t ht) (hconst 0 hs0)
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hs 0 hs0) hd1 hd2

/-- A point of a `C¹` field that is not an equilibrium is unstable: in this semantics instability
is the failure of Lyapunov stability, and the solution through the point leaves it. -/
@[powerlib_foundation] theorem unstable_of_ne_zero {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (h : f x_eq ≠ 0) : Unstable f x_eq :=
  fun hs => h (isEquilibrium_of_lyapunovStable hf hs)

/-- A locally exponentially stable point of a `C¹` field is an equilibrium. -/
@[powerlib_foundation] theorem isEquilibrium_of_locallyExponentiallyStable {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} (hf : ContDiff ℝ 1 f) (h : LocallyExponentiallyStable f x_eq) :
    IsEquilibrium f x_eq :=
  isEquilibrium_of_lyapunovStable hf h.lyapunovStable

/-- The exponential estimate of a locally exponentially stable equilibrium of a `C¹` field passes
to its linearization: every solution of `y' = A y` obeys the same estimate. -/
@[powerlib_foundation] theorem norm_exp_le_of_locallyExponentiallyStable {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {r C a : ℝ} (hr : 0 < r)
    (hb : ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
      ‖φ t₀ - x_eq‖ < r → ∀ t ∈ Icc t₀ t₁,
        ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖)
    (w : ℝⁿ) {T : ℝ} (hT : 0 ≤ T) :
    ‖exp (T • Linear.op A) w‖ ≤ C * Real.exp (-a * T) * ‖w‖ := by
  obtain ⟨g, K, hK, hg⟩ := exists_lipschitz_cutoff_near hf x_eq
  have hg0 : g x_eq = 0 := by rw [hg x_eq (by simp)]; exact heq
  have hderiv : HasFDerivAt f (Linear.op A) x_eq := by
    have h := (hf.differentiable one_ne_zero x_eq).hasFDerivAt
    rwa [hJac] at h
  set E : ℝ := Real.exp (K * T) with hE_def
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg K.coe_nonneg hT)
  set G : ℝ := gronwallBound 0 ‖Linear.op A‖₊ 1 T with hG_def
  have hG : 0 ≤ G := by
    have h := gronwallBound_mono (δ := 0) (ε := 1) (K := ‖Linear.op A‖₊) le_rfl zero_le_one
      (NNReal.coe_nonneg _) hT
    rwa [gronwallBound_x0] at h
  set M : ℝ := ‖w‖ * E * G with hM_def
  have hM : 0 ≤ M := by positivity
  set y := exp (T • Linear.op A) w
  refine le_of_forall_pos_le_add fun η hη => ?_
  set η' : ℝ := η / (M + 1) with hη'_def
  have hη' : 0 < η' := by positivity
  have hηM : η' * M ≤ η := by
    rw [hη'_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨δ, hδ, hsmall⟩ : ∃ δ > 0, ∀ {x : ℝⁿ}, dist x x_eq < δ →
      ‖f x - f x_eq - Linear.op A (x - x_eq)‖ ≤ η' * ‖x - x_eq‖ :=
    Metric.eventually_nhds_iff.mp (hderiv.isLittleO.def hη')
  set ρ : ℝ := min (min δ 1) r with hρ_def
  have hρ : 0 < ρ := lt_min (lt_min hδ one_pos) hr
  have hρδ : ρ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hρr : ρ ≤ r := min_le_right _ _
  set ε : ℝ := ρ / (2 * ((‖w‖ + 1) * E)) with hε_def
  have hε : 0 < ε := by positivity
  have hεwE : ε * ‖w‖ * E < ρ := by
    rw [hε_def]
    have hpos : 0 < (‖w‖ + 1) * E := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have : ρ * ‖w‖ * E < ρ * ((‖w‖ + 1) * E) := by
      have : ‖w‖ * E < (‖w‖ + 1) * E := by nlinarith
      nlinarith
    nlinarith
  have hεw : ε * ‖w‖ < r := by
    have : ε * ‖w‖ ≤ ε * ‖w‖ * E := le_mul_of_one_le_right (by positivity) hE1
    linarith
  -- the solution of the cutoff field through `x_eq + ε w`
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hK 0 (x_eq + ε • w)
  have hψc : ContinuousOn ψ (Icc 0 T) := hψ.continuousOn.mono Icc_subset_Ici_self
  have hψ' : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt ψ (g (ψ t)) (Ici t) t := fun t ht =>
    (hψ t ht.1).mono (Ici_subset_Ici.mpr ht.1)
  have hψ0w : ‖ψ 0 - x_eq‖ = ε * ‖w‖ := by
    rw [hψ0, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
  -- a priori bound: the cutoff solution stays within `ε ‖w‖ e^{K T}` of the equilibrium
  have hapriori : ∀ t ∈ Icc (0 : ℝ) T, dist (ψ t) x_eq ≤ ε * ‖w‖ * E := by
    intro t ht
    have h := dist_le_of_trajectories_ODE (v := fun _ => g) (K := K) (fun _ => hK) hψc hψ'
      (g := fun _ => x_eq) continuousOn_const
      (fun t _ => by
        simp only [hg0]
        exact hasDerivWithinAt_const t _ x_eq)
      (δ := ε * ‖w‖) (by rw [dist_eq_norm, hψ0w]) t ht
    have hexp : Real.exp (K * (t - 0)) ≤ E := by
      rw [sub_zero]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)
    calc dist (ψ t) x_eq ≤ ε * ‖w‖ * Real.exp (K * (t - 0)) := h
      _ ≤ ε * ‖w‖ * E := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hnear : ∀ t ∈ Icc (0 : ℝ) T, dist (ψ t) x_eq < ρ := fun t ht =>
    (hapriori t ht).trans_lt hεwE
  have hin : ∀ t ∈ Icc (0 : ℝ) T, dist (ψ t) x_eq ≤ 1 := fun t ht =>
    ((hnear t ht).trans_le hρ1).le
  have htraj : IsTrajectoryOn ψ f 0 T := isTrajectoryOn_of_cutoff hg hψ hin
  -- the exponential estimate on the nonlinear solution
  have hles : ‖ψ T - x_eq‖ ≤ C * Real.exp (-a * T) * (ε * ‖w‖) := by
    have h := hb 0 T ψ htraj (by rw [hψ0w]; linarith [hεw]) T (right_mem_Icc.mpr hT)
    rwa [hψ0w, sub_zero] at h
  -- comparison with the linear solution through the same initial state
  set sol := Linear.solution A x_eq 0 (x_eq + ε • w) with hsol_def
  have hcomp := dist_le_of_approx_trajectories_ODE
    (v := fun _ => affineLinearVectorField A x_eq) (K := ‖Linear.op A‖₊)
    (fun _ => Linear.affine_lipschitzWith A x_eq) hψc hψ'
    (εf := η' * (ε * ‖w‖ * E))
    (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
      rw [hg _ (hin t ht'), dist_eq_norm, Linear.affine_apply]
      have h1 := hsmall ((hnear t ht').trans_le hρδ)
      rw [heq, sub_zero] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hη'.le)
      rw [← dist_eq_norm]
      exact hapriori t ht')
    (g := sol) (g' := fun t => affineLinearVectorField A x_eq (sol t)) (εg := 0)
    (fun t _ => (Linear.solution_hasDerivAt A x_eq 0 _ t).continuousAt.continuousWithinAt)
    (fun t _ => (Linear.solution_hasDerivAt A x_eq 0 _ t).hasDerivWithinAt)
    (fun t _ => by rw [dist_self])
    (δ := 0) (by rw [hψ0, hsol_def, Linear.solution_initial, dist_self])
    T (right_mem_Icc.mpr hT)
  rw [add_zero, sub_zero, gronwallBound_zero_eq_mul] at hcomp
  have hsolT : sol T - x_eq = ε • y := by
    rw [hsol_def, Linear.solution, sub_zero, add_sub_cancel_left, add_sub_cancel_left, map_smul]
  have hkey : ε * ‖y‖ ≤ ε * (C * Real.exp (-a * T) * ‖w‖ + η' * M) := by
    have h1 : ‖sol T - x_eq‖ ≤ dist (ψ T) (sol T) + ‖ψ T - x_eq‖ := by
      rw [dist_comm, dist_eq_norm]
      calc ‖sol T - x_eq‖ = ‖(sol T - ψ T) + (ψ T - x_eq)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [hsolT, norm_smul, Real.norm_of_nonneg hε.le] at h1
    calc ε * ‖y‖ ≤ η' * (ε * ‖w‖ * E) * G + C * Real.exp (-a * T) * (ε * ‖w‖) :=
          h1.trans (add_le_add hcomp hles)
      _ = ε * (C * Real.exp (-a * T) * ‖w‖ + η' * M) := by rw [hM_def]; ring
  have := le_of_mul_le_mul_left hkey hε
  linarith

/-- **Converse linearization.** A locally exponentially stable equilibrium of a `C¹` field has a
Hurwitz Jacobian. -/
@[powerlib_foundation] theorem isHurwitz_of_locallyExponentiallyStable {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (h : LocallyExponentiallyStable f x_eq) : IsHurwitz A := by
  have heq : f x_eq = 0 := isEquilibrium_of_locallyExponentiallyStable hf h
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ := h
  have hlin : LocallyExponentiallyStable (affineLinearVectorField A x_eq) x_eq := by
    refine ⟨1, C, a, one_pos, hC, ha, fun t₀ t₁ φ hφ _ t ht => ?_⟩
    rw [Linear.trajectory_eq_solution hφ t ht, Linear.solution, add_sub_cancel_left]
    exact norm_exp_le_of_locallyExponentiallyStable A hf heq hJac hr hb _ (sub_nonneg.mpr ht.1)
  exact (Linear.holds_iff_isHurwitz x_eq (P := .locallyExponentiallyStable) trivial).mp hlin

/-- Local exponential stability of a point of a `C¹` field is decided by its linearization: the
point is an equilibrium and the Jacobian is Hurwitz. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_iff_isHurwitz_jacobian
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) :
    LocallyExponentiallyStable f x_eq ↔ f x_eq = 0 ∧ IsHurwitz A :=
  ⟨fun h => ⟨isEquilibrium_of_locallyExponentiallyStable hf h,
      isHurwitz_of_locallyExponentiallyStable A hf hJac h⟩,
    fun h => Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hf h.1 hJac h.2⟩

/-- At an equilibrium of a `C¹` field, local exponential stability is equivalent to a Hurwitz
Jacobian. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_iff_isHurwitz_of_eq
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiff ℝ 1 f)
    (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) :
    LocallyExponentiallyStable f x_eq ↔ IsHurwitz A := by
  rw [locallyExponentiallyStable_iff_isHurwitz_jacobian A hf hJac]
  exact and_iff_right heq

/-! ## Degenerate linearizations -/

/-- A Hurwitz matrix has no nonzero real null vector. -/
@[powerlib_foundation] theorem mulVec_ne_zero_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {v : Fin n → ℝ} (hv : v ≠ 0) : A *ᵥ v ≠ 0 := by
  intro h0
  have h := hA 0 (fun i => (v i : ℂ))
    (fun h => hv (funext fun i => by simpa using congrFun h i)) ?_
  · simp at h
  · funext i
    have hi := congrFun h0 i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, zero_smul,
      Complex.coe_algebraMap]
    have : ((∑ j, A i j * v j : ℝ) : ℂ) = 0 := by rw [hi]; simp
    push_cast at this
    exact this

/-- A Hurwitz matrix acts injectively on `ℝⁿ`. -/
@[powerlib_foundation] theorem toEuclideanCLM_injective_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    Function.Injective (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) := by
  intro x y hxy
  by_contra hne
  have hv : (x - y).ofLp ≠ 0 := by
    intro h
    apply hne
    rw [← sub_eq_zero]
    exact (WithLp.ofLp_eq_zero 2).mp h
  apply mulVec_ne_zero_of_isHurwitz hA hv
  have h := congrArg WithLp.ofLp (sub_eq_zero.mpr hxy)
  rw [← map_sub, Matrix.ofLp_toEuclideanCLM] at h
  simpa using h

/-- A `C¹` field with a nonzero linear first integral — a linear functional `ℓ` with
`ℓ (f x) = 0` everywhere — has no locally exponentially stable point: its Jacobian is singular. -/
@[powerlib_foundation] theorem not_locallyExponentiallyStable_of_firstIntegral
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} (hf : ContDiff ℝ 1 f) (ℓ : ℝⁿ →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hcons : ∀ x, ℓ (f x) = 0) : ¬ LocallyExponentiallyStable f x_eq := by
  intro h
  set D := fderiv ℝ f x_eq with hD
  set A := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm D with hA_def
  have hJac : D = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
    rw [hA_def, StarAlgEquiv.apply_symm_apply]
  have hA := isHurwitz_of_locallyExponentiallyStable A hf hJac h
  have hd : HasFDerivAt (fun x => ℓ (f x)) (ℓ.comp D) x_eq :=
    ℓ.hasFDerivAt.comp x_eq (hf.differentiable one_ne_zero x_eq).hasFDerivAt
  have hzero : ℓ.comp D = 0 := by
    have h2 : HasFDerivAt (fun x => ℓ (f x)) (0 : ℝⁿ →L[ℝ] ℝ) x_eq := by
      simp only [hcons]
      exact hasFDerivAt_const 0 x_eq
    exact hd.unique h2
  have hinj : Function.Injective (D : ℝⁿ →ₗ[ℝ] ℝⁿ) := by
    rw [hJac]
    exact toEuclideanCLM_injective_of_isHurwitz hA
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  apply hℓ
  ext y
  obtain ⟨x, hx⟩ := hsurj y
  have := congrArg (fun L : ℝⁿ →L[ℝ] ℝ => L x) hzero
  simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply] at this
  rw [← hx]
  simpa using this

/-- A singular Jacobian excludes local exponential stability: at a locally exponentially stable
point of a `C¹` field the Jacobian is injective. -/
@[powerlib_foundation] theorem fderiv_injective_of_locallyExponentiallyStable {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} (hf : ContDiff ℝ 1 f) (h : LocallyExponentiallyStable f x_eq) :
    Function.Injective (fderiv ℝ f x_eq) := by
  set A := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (fderiv ℝ f x_eq) with hA_def
  have hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
    rw [hA_def, StarAlgEquiv.apply_symm_apply]
  rw [hJac]
  exact toEuclideanCLM_injective_of_isHurwitz (isHurwitz_of_locallyExponentiallyStable A hf hJac h)

/-! ## Fields that are `C¹` only near the point

Local exponential stability depends only on the field near the point
(`locallyExponentiallyStable_congr_nhds`), and a field that is `C¹` on an open
neighbourhood agrees near the point with a globally `C¹` field
(`exists_contDiff_eventuallyEq`). The converse linearization therefore holds for fields
that are `C¹` only on an open neighbourhood of the point, e.g. power-balance fields with a
`1/V_dc` factor. -/

/-- Converse linearization for a field that is `C¹` on an open neighbourhood of the point. -/
@[powerlib_foundation] theorem isHurwitz_of_locallyExponentiallyStable_local {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {U : Set ℝⁿ} (hU : IsOpen U) (hx : x_eq ∈ U) (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiffOn ℝ 1 f U)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (h : LocallyExponentiallyStable f x_eq) : IsHurwitz A := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  exact isHurwitz_of_locallyExponentiallyStable A hg (by rw [hgf.fderiv_eq, hJac])
    (locallyExponentiallyStable_congr_nhds hgf h)

/-- Local exponential stability of a point of a field that is `C¹` on an open neighbourhood holds
exactly when the point is an equilibrium with a Hurwitz Jacobian. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_iff_isHurwitz_jacobian_local
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {U : Set ℝⁿ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiffOn ℝ 1 f U)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) :
    LocallyExponentiallyStable f x_eq ↔ f x_eq = 0 ∧ IsHurwitz A := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  constructor
  · intro h
    have hgl := locallyExponentiallyStable_congr_nhds hgf h
    refine ⟨?_, isHurwitz_of_locallyExponentiallyStable A hg (by rw [hgf.fderiv_eq, hJac]) hgl⟩
    rw [← hgf.eq_of_nhds]
    exact isEquilibrium_of_locallyExponentiallyStable hg hgl
  · rintro ⟨heq, hA⟩
    exact locallyExponentiallyStable_of_isHurwitz_jacobian_local hU hx A hf heq hJac hA

/-- A direction killed by the Jacobian excludes local exponential stability, for a field that
is `C¹` on an open neighbourhood of the point. -/
@[powerlib_foundation] theorem not_locallyExponentiallyStable_of_fderiv_apply_eq_zero_local
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {U : Set ℝⁿ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (hf : ContDiffOn ℝ 1 f U) {v : ℝⁿ} (hv : v ≠ 0) (hker : fderiv ℝ f x_eq v = 0) :
    ¬ LocallyExponentiallyStable f x_eq := by
  intro h
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  have hinj := fderiv_injective_of_locallyExponentiallyStable hg
    (locallyExponentiallyStable_congr_nhds hgf h)
  rw [hgf.fderiv_eq] at hinj
  exact hv (hinj (by rw [hker, map_zero]))

end powerlib.Dynamics
