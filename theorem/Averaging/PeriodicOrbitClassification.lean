import theorem.Averaging.PerturbedPeriodicOrbits
import theorem.PH.Composition

/-! # All periodic solutions in a region: the Bogoliubov orbits are the only ones

Bogoliubov's second theorem (`Averaging.exists_periodic_orbit`,
`Averaging.exists_periodic_point_perturbed`) gives near each nondegenerate zero `y*` of the averaged
field `f̄ = Averaging.fieldAverage f T` a `T`-periodic solution of `ẋ = ε f(x, t) + ε² r(x, t)`,
unique among the solutions that return after one period and start in a ball of radius `r₀` around
`y*`. Here all periodic solutions starting in a region `K` are classified. Integrating over one
period, `x(T) = x(0)` forces `T‖f̄(x(0))‖ ≤ εC_S` (`Averaging.period_step_le`): a periodic solution
starts `O(ε)`-close to the zero set of `f̄`. If on `K` the field `f̄` vanishes only at
`y₁*, …, y_m*` and `‖f̄(y)‖ ≥ c · min(ρ_K, min_i ‖y − y_i*‖)` there — automatic on a compact `K`
when every `y_i*` has an invertible derivative (`lower_bound_of_isCompact`) — then for all small
`ε` every periodic solution starting in `K` starts in one of the uniqueness balls and is one of the
`m` Bogoliubov orbits. The same holds for the fixed points of the period map of a perturbed family
(`ẋ = ε f(x, t) + q(t)`, `‖q‖ ≤ ηM_q`, `ε² ≤ η ≤ θε`).

Scope.
* `ẋ = ε f(x, t) + ε² r(x, t)` on a real Banach space `E`, `0 < ε ≤ 1`, with the hypotheses of
  `Averaging.exists_periodic_orbit` at every zero `y_i*` (`i : ι`): `f` and `r` satisfy those of
  `Averaging.kbm_first_order` (period `T > 0`, continuity, `T`-periodicity, global Lipschitz
  constants `ℓ`, `ℓ_r`, bounds `M`, `M_r`), `f(·, t)` has a derivative `Df` that is
  `L₂(i)`-Lipschitz on the ball `‖x − y_i*‖ ≤ ρ(i)`, `Df(y_i*, ·)` is continuous, `f̄(y_i*) = 0`,
  and `Df̄(y_i*) = A(i)` has a two-sided continuous linear inverse `B(i)`. The remainder `r` may
  depend on `ε` (its constants do not). Solutions are global `C¹` curves; a solution is periodic
  when it returns after one period, `x(T) = x(0)` (then `x(t + T) = x(t)` for all `t`).
* The region: a set `K` on which `c ρ_K ≤ ‖f̄(y)‖` or `c ‖y − y_i*‖ ≤ ‖f̄(y)‖` for some `i`, i.e.
  `c · min(ρ_K, min_i ‖y − y_i*‖) ≤ ‖f̄(y)‖`, with `c > 0`. For a compact `K`, finitely many
  `y_i*` with invertible derivatives and no other zero of `f̄` in `K`, some `c, ρ_K > 0` exist
  (`lower_bound_of_isCompact`); in finite dimension every closed bounded `K` is compact. The
  zeros `y_i*` need not lie in `K`.
* Perturbed families as in `Averaging.exists_periodic_point_perturbed`: curves `X y` with
  `X y 0 = y` and `Ẋ = ε f(X, t) + Q y t` on `[0, T]`, `‖Q y‖ ≤ ηM_q` on `K` and near the zeros,
  `ηℓ_q`-Lipschitz along pairs of curves near each zero, `ε² ≤ η ≤ ε`; the curves need not solve a
  common differential equation.
* Smallness is stated by explicit inequalities (`periodic_orbit_classification`,
  `periodic_point_classification_perturbed`) and, for compact `K` and finite `ι`, by the
  existence of `ε₀` (and `θ` with `η ≤ θε`) depending only on the data.
* Generic mathematics, no model family.

Source: Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*
(the second theorem of Bogoliubov: periodic solutions and the hyperbolic equilibria of the averaged
system); Hale, *Ordinary Differential Equations*, Ch. V (periodic solutions by averaging: the
periodic solutions near a compact set correspond to the zeros of the averaged field);
Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*, Ch. 6 (periodic
averaging); the one-period estimates `Averaging.period_step_le`,
`Averaging.perturbed_period_step_le` and the orbits `Averaging.exists_periodic_orbit`,
`Averaging.exists_periodic_point_perturbed`.

Sharpenings.
* `Averaging.exists_periodic_orbit` and `Averaging.exists_periodic_point_perturbed` claim
  uniqueness only in a ball of radius `r₀` around each zero. Here, on a region containing only
  finitely many nondegenerate zeros, the Bogoliubov orbits are all periodic solutions starting
  there, with the initial state within `εC_S/(cT)` (resp. `ηC_S/(cεT)`) of a zero.

Results.
* `periodic_fieldAverage_le`, `perturbed_periodic_fieldAverage_le` — a solution that returns
  after one period starts near the zero set: `T‖f̄(x(τ))‖ ≤ εC_S`, resp. `εT‖f̄(x(τ))‖ ≤ ηC_S`.
* `zeros_finite_of_isCompact` — nondegenerate zeros on a compact set are finitely many.
* `lower_bound_of_isCompact` — finitely many nondegenerate zeros on a compact set:
  `c · min(ρ_K, min_i ‖y − y_i*‖) ≤ ‖F(y)‖` for some `c, ρ_K > 0`.
* `periodic_orbit_classification` — explicit smallness conditions: the orbits `x_i` of
  `Averaging.exists_periodic_orbit` exist, each unique within `r₀(i)` of `y_i*`, and every
  periodic solution `z` with `z(0) ∈ K` is one of them, `cT‖z(0) − y_i*‖ ≤ εC_S`.
* `periodic_orbit_classification_compact` — compact `K`, finitely many nondegenerate zeros of
  `f̄` in `K`: there are `ε₀ > 0`, `C ≥ 0`, `r₀ > 0` such that for `0 < ε ≤ ε₀` and every
  admissible `r` every periodic solution starting in `K` is one of the orbits `x_i`,
  `‖x_i(t) − y_i*‖ ≤ Cε`, each the only periodic solution starting within `r₀` of `y_i*`.
* `periodic_point_classification_perturbed`, `periodic_point_classification_perturbed_compact`
  — the fixed points in `K` of the period map of a perturbed family are its fixed points near
  the zeros, `‖y_ε − y_i*‖ ≤ Cη/ε`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f r : E → ℝ → E} {T ℓ M ℓr Mr : ℝ}

/-! ## A periodic solution starts near the zero set of the averaged field -/

section Average

/-- **A periodic solution starts near a zero of the averaged field.** If `x` solves
`ẋ = ε f(x, t) + ε² r(x, t)` (`0 < ε ≤ 1`) and returns after one period, `x(τ + T) = x(τ)`, then
`T ‖f̄(x(τ))‖ ≤ ε C_S`, `C_S = stroboConst ℓ M M_r T` (`period_step_le`). -/
@[tmio T, powerlib_foundation] theorem periodic_fieldAverage_le [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hrc : Continuous (Function.uncurry r)) (hrM : ∀ x t, ‖r x t‖ ≤ Mr)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) {τ : ℝ}
    (hper : x (τ + T) = x τ) :
    T * ‖fieldAverage f T (x τ)‖ ≤ ε * stroboConst ℓ M Mr T := by
  have h := period_step_le hf hrc hrM hε.le hε1 hx τ
  rw [hper, sub_self, zero_sub, norm_neg, norm_smul,
    Real.norm_of_nonneg (mul_pos hε hf.1).le] at h
  have h' : ε * (T * ‖fieldAverage f T (x τ)‖) ≤ ε * (ε * stroboConst ℓ M Mr T) := by
    calc ε * (T * ‖fieldAverage f T (x τ)‖) = ε * T * ‖fieldAverage f T (x τ)‖ := by ring
      _ ≤ ε ^ 2 * (ℓ * (M + Mr) * T ^ 2 + Mr * T) := h
      _ = ε * (ε * stroboConst ℓ M Mr T) := by rw [stroboConst]; ring
  exact le_of_mul_le_mul_left h' hε

/-- **A periodic perturbed curve starts near a zero of the averaged field.** If
`ẋ = ε f(x, t) + q(t)` on `[τ, τ + T]` with `‖q‖ ≤ ηM_q`, `ε² ≤ η ≤ ε`, and `x(τ + T) = x(τ)`,
then `ε T ‖f̄(x(τ))‖ ≤ η C_S`, `C_S = stroboConst ℓ M M_q T` (`perturbed_period_step_le`). -/
@[tmio T, powerlib_foundation] theorem perturbed_periodic_fieldAverage_le [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ε η Mq : ℝ} (hε : 0 ≤ ε) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hMq : 0 ≤ Mq) {x q : ℝ → E}
    {τ : ℝ} (hx : ∀ t ∈ Icc τ (τ + T), HasDerivAt x (ε • f (x t) t + q t) t)
    (hq : ∀ t ∈ Icc τ (τ + T), ‖q t‖ ≤ η * Mq) (hper : x (τ + T) = x τ) :
    ε * (T * ‖fieldAverage f T (x τ)‖) ≤ η * stroboConst ℓ M Mq T := by
  have h := perturbed_period_step_le hf hε hηε hεη hMq hx hq
  rw [hper, sub_self, zero_sub, norm_neg, norm_smul,
    Real.norm_of_nonneg (mul_nonneg hε hf.1.le)] at h
  calc ε * (T * ‖fieldAverage f T (x τ)‖) = ε * T * ‖fieldAverage f T (x τ)‖ := by ring
    _ ≤ η * stroboConst ℓ M Mq T := h

end Average

/-! ## Nondegenerate zeros on a compact set -/

section LowerBound

@[tmio T, powerlib_foundation] private theorem exists_ge_all {ι : Type*} [Finite ι]
    (g : ι → ℝ) : ∃ C, 0 ≤ C ∧ ∀ i, g i ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range g).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun i => (hC ⟨i, rfl⟩).trans (le_max_left _ _)⟩

/-- The linear lower bound near a zero with a left-invertible derivative. -/
@[tmio T, powerlib_foundation] private theorem local_lower_bound {F : E → E} {y₀ : E}
    {A B : E →L[ℝ] E} (h0 : F y₀ = 0) (hA : HasFDerivAt F A y₀) (hBA : ∀ v, B (A v) = v)
    {C : ℝ} (hC : ‖B‖ + 1 ≤ C) :
    ∃ δ > 0, ∀ y, ‖y - y₀‖ < δ → 1 / (2 * C) * ‖y - y₀‖ ≤ ‖F y‖ := by
  have hC0 : 0 < C := by linarith [norm_nonneg B]
  set c₁ := 1 / (2 * C) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hCc : C * c₁ = 1 / 2 := by rw [hc₁]; field_simp
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (hA.isLittleO.def hc₁0)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h1 := hδ' (show dist y y₀ < δ by rwa [dist_eq_norm])
  simp only [h0, sub_zero] at h1
  have h2 : ‖y - y₀‖ ≤ C * ‖A (y - y₀)‖ := by
    calc ‖y - y₀‖ = ‖B (A (y - y₀))‖ := by rw [hBA]
      _ ≤ ‖B‖ * ‖A (y - y₀)‖ := B.le_opNorm _
      _ ≤ C * ‖A (y - y₀)‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have h3 : ‖A (y - y₀)‖ ≤ ‖F y‖ + ‖F y - A (y - y₀)‖ := by
    have := norm_sub_le (F y) (F y - A (y - y₀))
    rwa [sub_sub_cancel] at this
  have h4 : ‖y - y₀‖ ≤ 2 * C * ‖F y‖ := by
    have h5 : ‖y - y₀‖ ≤ C * ‖F y‖ + C * c₁ * ‖y - y₀‖ := by
      calc ‖y - y₀‖ ≤ C * ‖A (y - y₀)‖ := h2
        _ ≤ C * (‖F y‖ + c₁ * ‖y - y₀‖) :=
            mul_le_mul_of_nonneg_left (h3.trans (by linarith)) hC0.le
        _ = C * ‖F y‖ + C * c₁ * ‖y - y₀‖ := by ring
    rw [hCc] at h5
    linarith
  calc c₁ * ‖y - y₀‖ ≤ c₁ * (2 * C * ‖F y‖) := mul_le_mul_of_nonneg_left h4 hc₁0.le
    _ = ‖F y‖ := by rw [hc₁]; field_simp

/-- **Nondegenerate zeros on a compact set are finitely many.** If `F` is continuous on a compact
set `K` and has at each of its zeros in `K` a derivative with a left inverse, then `F` has only
finitely many zeros in `K` (each is isolated by the linear lower bound near it). -/
@[tmio T, powerlib_foundation] theorem zeros_finite_of_isCompact {F : E → E} {K : Set E}
    (hK : IsCompact K) (hFc : ContinuousOn F K)
    (hnd : ∀ y ∈ K, F y = 0 → ∃ A B : E →L[ℝ] E, HasFDerivAt F A y ∧ ∀ v, B (A v) = v) :
    {y | y ∈ K ∧ F y = 0}.Finite := by
  set S : Set E := {y | y ∈ K ∧ F y = 0} with hS
  have hSc : IsClosed S := hFc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  have hSk : IsCompact S := hK.of_isClosed_subset hSc fun y hy => hy.1
  have hloc : ∀ y : S, ∃ δ > 0, ∀ y' : E, ‖y' - (y : E)‖ < δ → F y' = 0 → y' = y := by
    rintro ⟨y, hyK, hy0⟩
    obtain ⟨A, B, hA, hBA⟩ := hnd y hyK hy0
    obtain ⟨δ, hδ, hδl⟩ := local_lower_bound hy0 hA hBA (le_refl (‖B‖ + 1))
    refine ⟨δ, hδ, fun y' hy' hF => ?_⟩
    have h := hδl y' hy'
    rw [hF, norm_zero] at h
    have hC : 0 < 1 / (2 * (‖B‖ + 1)) := by positivity
    have : ‖y' - y‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (y' - y)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  choose δ hδ hδl using hloc
  obtain ⟨t, ht⟩ := hSk.elim_finite_subcover (fun y : S => Metric.ball (y : E) (δ y))
    (fun _ => Metric.isOpen_ball)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hδ _)⟩)
  refine ((t.finite_toSet).image Subtype.val).subset fun y hy => ?_
  obtain ⟨i, hi⟩ := mem_iUnion₂.mp (ht hy)
  rw [Metric.mem_ball, dist_eq_norm] at hi
  exact ⟨i, by simpa using hi.1, (hδl i y hi.2 hy.2).symm⟩

/-- **Nondegenerate zeros on a compact set give a linear lower bound.** Let `K` be compact, `F`
continuous on `K`, and let the zeros of `F` in `K` be among finitely many points `y_i*`, each a
zero of `F` with a derivative `A(i)` that has a left inverse `B(i)`. Then there are `c, ρ_K > 0`
with `c ρ_K ≤ ‖F(y)‖` or `c ‖y − y_i*‖ ≤ ‖F(y)‖` for some `i`, for every `y ∈ K`; that is,
`‖F(y)‖ ≥ c · min(ρ_K, min_i ‖y − y_i*‖)` on `K`. -/
@[tmio T, powerlib_foundation] theorem lower_bound_of_isCompact {F : E → E} {K : Set E}
    (hK : IsCompact K) (hFc : ContinuousOn F K) {ι : Type*} [Finite ι] {ystar : ι → E}
    {A B : ι → E →L[ℝ] E} (h0 : ∀ i, F (ystar i) = 0) (hA : ∀ i, HasFDerivAt F (A i) (ystar i))
    (hBA : ∀ i v, B i (A i v) = v) (hzero : ∀ y ∈ K, F y = 0 → ∃ i, y = ystar i) :
    ∃ c ρK : ℝ, 0 < c ∧ 0 < ρK ∧
      ∀ y ∈ K, c * ρK ≤ ‖F y‖ ∨ ∃ i, c * ‖y - ystar i‖ ≤ ‖F y‖ := by
  -- a common bound for the inverses
  obtain ⟨CB, hCB0, hCB⟩ := exists_ge_all fun i => ‖B i‖
  set C := CB + 1 with hC
  have hC0 : 0 < C := by positivity
  set c₁ := 1 / (2 * C) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  -- the linear lower bound near each zero
  have hloc : ∀ i, ∃ δ > 0, ∀ y, ‖y - ystar i‖ < δ → c₁ * ‖y - ystar i‖ ≤ ‖F y‖ := fun i =>
    local_lower_bound (h0 i) (hA i) (hBA i) (by rw [hC]; linarith [hCB i])
  choose δ hδ hδl using hloc
  -- a common radius
  obtain ⟨ρK, hρK0, hρK⟩ := PH.exists_pos_lower _ fun i => half_pos (hδ i)
  have hρKδ : ∀ i, ρK < δ i := fun i => (hρK i).trans_lt (half_lt_self (hδ i))
  set S : Set E := {y | ∀ i, ρK ≤ ‖y - ystar i‖} with hS
  have hSc : IsClosed S := by
    have e : S = ⋂ i, {y : E | ρK ≤ ‖y - ystar i‖} := by ext y; simp [hS]
    rw [e]
    exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  have hK' : IsCompact (K ∩ S) := hK.inter_right hSc
  have hnear : ∀ y ∈ K, y ∉ K ∩ S → ∃ i, c₁ * ‖y - ystar i‖ ≤ ‖F y‖ := by
    intro y hy hy'
    have : ∃ i, ‖y - ystar i‖ < ρK := by
      by_contra h
      push Not at h
      exact hy' ⟨hy, h⟩
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hδl i y (hi.trans (hρKδ i))⟩
  rcases (K ∩ S).eq_empty_or_nonempty with hE | hne
  · refine ⟨c₁, ρK, hc₁0, hρK0, fun y hy => Or.inr (hnear y hy ?_)⟩
    rw [hE]
    exact notMem_empty y
  · obtain ⟨y₀, hy₀, hmin⟩ := hK'.exists_isMinOn hne ((hFc.mono inter_subset_left).norm)
    have hm : 0 < ‖F y₀‖ := by
      rcases (norm_nonneg (F y₀)).lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨i, hi⟩ := hzero y₀ hy₀.1 (norm_eq_zero.mp h.symm)
        have := hy₀.2 i
        rw [hi, sub_self, norm_zero] at this
        linarith
    refine ⟨min c₁ (‖F y₀‖ / ρK), ρK, lt_min hc₁0 (by positivity), hρK0, fun y hy => ?_⟩
    by_cases hy' : y ∈ K ∩ S
    · left
      calc min c₁ (‖F y₀‖ / ρK) * ρK ≤ ‖F y₀‖ / ρK * ρK :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hρK0.le
        _ = ‖F y₀‖ := by field_simp
        _ ≤ ‖F y‖ := isMinOn_iff.mp hmin y hy'
    · right
      obtain ⟨i, hi⟩ := hnear y hy hy'
      exact ⟨i, (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)).trans hi⟩

end LowerBound

/-! ## The classification of the periodic solutions -/

section Classification

variable {Df : E → ℝ → E →L[ℝ] E}

/-- **The periodic solutions starting in a region are the Bogoliubov orbits.** Let `f`, `r` be as
in `Averaging.exists_periodic_orbit` at each of the zeros `y_i*` (`i : ι`) of `f̄`, with radii
`ρ(i)`, Lipschitz constants `L₂(i)` of `Df`, derivatives `A(i) = Df̄(y_i*)` with inverses `B(i)`,
and uniqueness radii `r₀(i)` (`2r₀ ≤ ρ`, `4‖B‖L₂r₀ ≤ 1`), and let `K` satisfy the lower bound
`c ρ_K ≤ ‖f̄(y)‖ ∨ ∃ i, c ‖y − y_i*‖ ≤ ‖f̄(y)‖` on `K`. If `ε` satisfies the smallness conditions
of `Averaging.exists_periodic_orbit` at every `y_i*` and `εC_S < cρ_K T`, `εC_S ≤ c r₀(i) T`, then
there are `T`-periodic solutions `x_i` with `‖x_i(t) − y_i*‖ ≤ ε(2‖B(i)‖C_S/T + (M + M_r)T)`,
`x_i` is the only solution with `z(T) = z(0)` and `‖z(0) − y_i*‖ ≤ r₀(i)`, and every solution `z`
with `z(T) = z(0)` and `z(0) ∈ K` is one of them, `z = x_i` with `cT ‖z(0) − y_i*‖ ≤ εC_S`
(`periodic_fieldAverage_le` and the uniqueness of `Averaging.exists_periodic_orbit`). -/
@[tmio T, powerlib_foundation] theorem periodic_orbit_classification [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hr : 0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
      (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr)
    {ι : Type*} {ystar : ι → E} {ρ L₂ r₀ : ι → ℝ} (hρ : ∀ i, 0 < ρ i) (hL₂ : ∀ i, 0 ≤ L₂ i)
    (hD : ∀ i x, ‖x - ystar i‖ ≤ ρ i → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ i x y, ‖x - ystar i‖ ≤ ρ i → ‖y - ystar i‖ ≤ ρ i → ∀ t,
      ‖Df x t - Df y t‖ ≤ L₂ i * ‖x - y‖)
    (hDc : ∀ i, Continuous (Df (ystar i))) (h0 : ∀ i, fieldAverage f T (ystar i) = 0)
    {A B : ι → E →L[ℝ] E} (hA : ∀ i, HasFDerivAt (fieldAverage f T) (A i) (ystar i))
    (hAB : ∀ i v, A i (B i v) = v) (hBA : ∀ i v, B i (A i v) = v)
    (hr₀ : ∀ i, 0 < r₀ i) (hr₀ρ : ∀ i, 2 * r₀ i ≤ ρ i) (hr₀L : ∀ i, 4 * ‖B i‖ * L₂ i * r₀ i ≤ 1)
    {K : Set E} {c ρK : ℝ} (hc : 0 < c)
    (hK : ∀ y ∈ K, c * ρK ≤ ‖fieldAverage f T y‖ ∨
      ∃ i, c * ‖y - ystar i‖ ≤ ‖fieldAverage f T y‖)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hερ : ∀ i, 2 * ε * (M + Mr) * T ≤ ρ i)
    (hεL : ∀ i, 4 * ε * ‖B i‖ * stroboLip ℓ ℓr (L₂ i) M Mr T ≤ T)
    (hεC : ∀ i, 2 * ε * ‖B i‖ * stroboConst ℓ M Mr T ≤ r₀ i * T)
    (hεK : ε * stroboConst ℓ M Mr T < c * ρK * T)
    (hεr : ∀ i, ε * stroboConst ℓ M Mr T ≤ c * r₀ i * T) :
    ∃ x : ι → ℝ → E,
      (∀ i, (∀ t, HasDerivAt (x i) (ε • f (x i t) t + ε ^ 2 • r (x i t) t) t) ∧
        (∀ t, x i (t + T) = x i t) ∧
        ∀ t, ‖x i t - ystar i‖ ≤ ε * (2 * ‖B i‖ * stroboConst ℓ M Mr T / T + (M + Mr) * T)) ∧
      (∀ z : ℝ → E, (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) → z T = z 0 →
        ∀ i, ‖z 0 - ystar i‖ ≤ r₀ i → z = x i) ∧
      ∀ z : ℝ → E, (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) → z T = z 0 →
        z 0 ∈ K → ∃ i, z = x i ∧ c * T * ‖z 0 - ystar i‖ ≤ ε * stroboConst ℓ M Mr T := by
  have hT := hf.1
  have hex : ∀ i, ∃ x : ℝ → E, (∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) ∧
      (∀ t, x (t + T) = x t) ∧
      (∀ t, ‖x t - ystar i‖ ≤ ε * (2 * ‖B i‖ * stroboConst ℓ M Mr T / T + (M + Mr) * T)) ∧
      ∀ z : ℝ → E, (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) →
        z T = z 0 → ‖z 0 - ystar i‖ ≤ r₀ i → z = x := fun i =>
    exists_periodic_orbit hf hr (hρ i) (hL₂ i) (hD i) (hDl i) (hDc i) (h0 i) (hA i) (hAB i)
      (hBA i) (hr₀ i) (hr₀ρ i) (hr₀L i) hε hε1 (hερ i) (hεL i) (hεC i)
  choose x hx hxper hxb hxu using hex
  refine ⟨x, fun i => ⟨hx i, hxper i, hxb i⟩, fun z hz hzT i hi => hxu i z hz hzT hi,
    fun z hz hzT hzK => ?_⟩
  have hav := periodic_fieldAverage_le hf hr.2.2.1 hr.2.2.2.2.2 hε hε1 hz (τ := 0)
    (by rw [zero_add]; exact hzT)
  rcases hK _ hzK with h | ⟨i, hi⟩
  · exfalso
    have h1 : c * ρK * T ≤ T * ‖fieldAverage f T (z 0)‖ := by
      rw [mul_comm T]; exact mul_le_mul_of_nonneg_right h hT.le
    linarith
  · have h1 : c * T * ‖z 0 - ystar i‖ ≤ ε * stroboConst ℓ M Mr T := by
      calc c * T * ‖z 0 - ystar i‖ = T * (c * ‖z 0 - ystar i‖) := by ring
        _ ≤ T * ‖fieldAverage f T (z 0)‖ := mul_le_mul_of_nonneg_left hi hT.le
        _ ≤ ε * stroboConst ℓ M Mr T := hav
    refine ⟨i, hxu i z hz hzT ?_, h1⟩
    have h2 : c * T * ‖z 0 - ystar i‖ ≤ c * T * r₀ i := by linarith [hεr i]
    exact le_of_mul_le_mul_left h2 (mul_pos hc hT)

@[tmio T, powerlib_foundation] private theorem mul_le_of_le_div_add_one {ε a b : ℝ} (hε : 0 ≤ ε)
    (ha : 0 ≤ a) (h : ε ≤ b / (a + 1)) : ε * a ≤ b := by
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

@[tmio T, powerlib_foundation] private theorem mul_lt_of_le_div_add_one {ε a b : ℝ} (hε : 0 < ε)
    (ha : 0 ≤ a) (h : ε ≤ b / (a + 1)) : ε * a < b := by
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- **For all small `ε`, the periodic solutions starting in a compact region are the Bogoliubov
orbits.** Let `f` be as in `Averaging.exists_periodic_orbit` at finitely many zeros `y_i*` of `f̄`
(radii `ρ(i)`, Lipschitz constants `L₂(i)`, invertible `Df̄(y_i*)`), let `K` be compact, and let
`f̄` have no other zero in `K`. There are `ε₀ > 0` and `C ≥ 0` such that for every `0 < ε ≤ ε₀`
and every remainder `r` with the constants `ℓ_r, M_r`, the system `ẋ = ε f(x, t) + ε² r(x, t)` has
`T`-periodic solutions `x_i` with `‖x_i(t) − y_i*‖ ≤ Cε`, `x_i` is the only solution with
`z(T) = z(0)` and `‖z(0) − y_i*‖ ≤ r₀` (`r₀ > 0` independent of `ε`), and every solution `z` with
`z(T) = z(0)` and `z(0) ∈ K` is one of them, `z = x_i`, `‖z(0) − y_i*‖ ≤ Cε`
(`lower_bound_of_isCompact`, `periodic_orbit_classification`). -/
@[tmio T, powerlib_foundation] theorem periodic_orbit_classification_compact [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hℓr : 0 ≤ ℓr) (hMr : 0 ≤ Mr) {ι : Type*} [Finite ι] {ystar : ι → E} {ρ L₂ : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) (hL₂ : ∀ i, 0 ≤ L₂ i)
    (hD : ∀ i x, ‖x - ystar i‖ ≤ ρ i → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ i x y, ‖x - ystar i‖ ≤ ρ i → ‖y - ystar i‖ ≤ ρ i → ∀ t,
      ‖Df x t - Df y t‖ ≤ L₂ i * ‖x - y‖)
    (hDc : ∀ i, Continuous (Df (ystar i))) (h0 : ∀ i, fieldAverage f T (ystar i) = 0)
    {A B : ι → E →L[ℝ] E} (hA : ∀ i, HasFDerivAt (fieldAverage f T) (A i) (ystar i))
    (hAB : ∀ i v, A i (B i v) = v) (hBA : ∀ i v, B i (A i v) = v) {K : Set E}
    (hK : IsCompact K) (hzero : ∀ y ∈ K, fieldAverage f T y = 0 → ∃ i, y = ystar i) :
    ∃ ε₀ C r₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < r₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ r : E → ℝ → E,
      (0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
        (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr) →
      ∃ x : ι → ℝ → E,
        (∀ i, (∀ t, HasDerivAt (x i) (ε • f (x i t) t + ε ^ 2 • r (x i t) t) t) ∧
          (∀ t, x i (t + T) = x i t) ∧ ∀ t, ‖x i t - ystar i‖ ≤ C * ε) ∧
        (∀ z : ℝ → E, (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) → z T = z 0 →
          ∀ i, ‖z 0 - ystar i‖ ≤ r₀ → z = x i) ∧
        ∀ z : ℝ → E, (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) → z T = z 0 →
          z 0 ∈ K → ∃ i, z = x i ∧ ‖z 0 - ystar i‖ ≤ C * ε := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 0 0)
  obtain ⟨c, ρK, hc, hρK, hK'⟩ := lower_bound_of_isCompact hK
    (fieldAverage_continuous hf).continuousOn h0 hA hBA hzero
  obtain ⟨CB, hCB0, hCB⟩ := exists_ge_all fun i => ‖B i‖
  set CS := stroboConst ℓ M Mr T with hCS
  have hCS0 : 0 ≤ CS := by rw [hCS, stroboConst]; positivity
  set LS : ι → ℝ := fun i => stroboLip ℓ ℓr (L₂ i) M Mr T with hLS
  have hLS0 : ∀ i, 0 ≤ LS i := fun i => by
    simp only [hLS, stroboLip]; have := hL₂ i; positivity
  set r₀ : ι → ℝ := fun i => min (ρ i / 2) (1 / (4 * ‖B i‖ * L₂ i + 1)) with hr₀
  have hr₀0 : ∀ i, 0 < r₀ i := fun i => by
    have := hL₂ i; have := hρ i
    exact lt_min (by positivity) (by positivity)
  have hr₀ρ : ∀ i, 2 * r₀ i ≤ ρ i := fun i => by
    have := min_le_left (ρ i / 2) (1 / (4 * ‖B i‖ * L₂ i + 1)); simp only [hr₀]; linarith
  have hr₀L : ∀ i, 4 * ‖B i‖ * L₂ i * r₀ i ≤ 1 := fun i => by
    have h := min_le_right (ρ i / 2) (1 / (4 * ‖B i‖ * L₂ i + 1))
    have := hL₂ i
    have := mul_le_of_le_div_add_one (hr₀0 i).le (by positivity) h
    simp only [hr₀]; linarith
  -- the smallness bound at each zero
  set e : ι → ℝ := fun i => min (min (ρ i / (2 * (M + Mr) * T + 1)) (T / (4 * ‖B i‖ * LS i + 1)))
    (min (r₀ i * T / (2 * ‖B i‖ * CS + 1)) (c * r₀ i * T / (CS + 1))) with he
  have he0 : ∀ i, 0 < e i := fun i => by
    have := hρ i; have := hr₀0 i; have := hLS0 i
    exact lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  obtain ⟨e₀, he₀0, he₀⟩ := PH.exists_pos_lower _ he0
  obtain ⟨R₀, hR₀0, hR₀⟩ := PH.exists_pos_lower _ hr₀0
  set ε₀ := min (min 1 (c * ρK * T / (CS + 1))) e₀ with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (lt_min one_pos (by positivity)) he₀0
  refine ⟨ε₀, max (2 * CB * CS / T + (M + Mr) * T) (CS / (c * T)), R₀, hε₀0,
    le_max_of_le_left (by positivity), hR₀0, fun ε hε hεε₀ r hr => ?_⟩
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεe : ∀ i, ε ≤ e i := fun i => (hεε₀.trans (min_le_right _ _)).trans (he₀ i)
  have hερ : ∀ i, 2 * ε * (M + Mr) * T ≤ ρ i := fun i => by
    have h := mul_le_of_le_div_add_one hε.le (by positivity : 0 ≤ 2 * (M + Mr) * T)
      ((hεe i).trans ((min_le_left _ _).trans (min_le_left _ _)))
    linarith
  have hεL : ∀ i, 4 * ε * ‖B i‖ * LS i ≤ T := fun i => by
    have := hLS0 i
    have h := mul_le_of_le_div_add_one hε.le (by positivity : 0 ≤ 4 * ‖B i‖ * LS i)
      ((hεe i).trans ((min_le_left _ _).trans (min_le_right _ _)))
    linarith
  have hεC : ∀ i, 2 * ε * ‖B i‖ * CS ≤ r₀ i * T := fun i => by
    have h := mul_le_of_le_div_add_one hε.le (by positivity : 0 ≤ 2 * ‖B i‖ * CS)
      ((hεe i).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hεr : ∀ i, ε * CS ≤ c * r₀ i * T := fun i =>
    (mul_le_of_le_div_add_one hε.le hCS0
      ((hεe i).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hεK : ε * CS < c * ρK * T :=
    mul_lt_of_le_div_add_one hε hCS0 (hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨x, hx, hun, hcl⟩ := periodic_orbit_classification hf hr hρ hL₂ hD hDl hDc h0 hA hAB hBA
    hr₀0 hr₀ρ hr₀L hc hK' hε hε1 hερ hεL hεC hεK hεr
  have hbd : ∀ i t, ‖x i t - ystar i‖ ≤
      max (2 * CB * CS / T + (M + Mr) * T) (CS / (c * T)) * ε := fun i t => by
    refine ((hx i).2.2 t).trans ?_
    rw [mul_comm ε]
    refine mul_le_mul_of_nonneg_right (le_max_of_le_left ?_) hε.le
    gcongr
    exact hCB i
  refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.1, hbd i⟩,
    fun z hz hzT i hi => hun z hz hzT i (hi.trans (hR₀ i)), fun z hz hzT hzK => ?_⟩
  obtain ⟨i, hzi, hi⟩ := hcl z hz hzT hzK
  refine ⟨i, hzi, ?_⟩
  rw [hzi]
  exact hbd i 0

/-- **The fixed points in a region of the period map of a perturbed family are its fixed points
near the zeros.** Let `f` be as in `Averaging.exists_periodic_point_perturbed` at each zero `y_i*`
(`i : ι`) of `f̄`, with uniqueness radii `r₀(i)`, let `K` satisfy the lower bound
`c ρ_K ≤ ‖f̄(y)‖ ∨ ∃ i, c ‖y − y_i*‖ ≤ ‖f̄(y)‖` on `K`, and let `X y` be curves with `X y 0 = y`
solving `Ẋ = ε f(X, t) + Q y t` on `[0, T]` for `y ∈ K` and near each `y_i*`, with `‖Q y‖ ≤ ηM_q`
there and `‖Q y − Q y'‖ ≤ ηℓ_q ‖X y − X y'‖` near each `y_i*`. Under the smallness conditions of
`Averaging.exists_periodic_point_perturbed` at every `y_i*` and `ηC_S < cρ_K εT`,
`ηC_S ≤ c r₀(i) εT`, the period map `y ↦ X y T` has fixed points `y_ε(i)` with
`‖y_ε(i) − y_i*‖ ≤ 2η‖B(i)‖C_S/(εT)`, the only fixed points within `r₀(i)` of `y_i*`, and its
fixed points in `K` are among them, `y = y_ε(i)` with `cεT ‖y − y_i*‖ ≤ ηC_S`
(`perturbed_periodic_fieldAverage_le`). -/
@[tmio T, powerlib_foundation] theorem periodic_point_classification_perturbed [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ι : Type*} {ystar : ι → E} {ρ L₂ r₀ : ι → ℝ} (hρ : ∀ i, 0 < ρ i) (hL₂ : ∀ i, 0 ≤ L₂ i)
    (hD : ∀ i x, ‖x - ystar i‖ ≤ ρ i → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ i x y, ‖x - ystar i‖ ≤ ρ i → ‖y - ystar i‖ ≤ ρ i → ∀ t,
      ‖Df x t - Df y t‖ ≤ L₂ i * ‖x - y‖)
    (hDc : ∀ i, Continuous (Df (ystar i))) (h0 : ∀ i, fieldAverage f T (ystar i) = 0)
    {A B : ι → E →L[ℝ] E} (hA : ∀ i, HasFDerivAt (fieldAverage f T) (A i) (ystar i))
    (hAB : ∀ i v, A i (B i v) = v) (hBA : ∀ i v, B i (A i v) = v)
    (hr₀ : ∀ i, 0 < r₀ i) (hr₀ρ : ∀ i, 2 * r₀ i ≤ ρ i) (hr₀L : ∀ i, 4 * ‖B i‖ * L₂ i * r₀ i ≤ 1)
    {K : Set E} {c ρK : ℝ} (hc : 0 < c)
    (hK : ∀ y ∈ K, c * ρK ≤ ‖fieldAverage f T y‖ ∨
      ∃ i, c * ‖y - ystar i‖ ≤ ‖fieldAverage f T y‖)
    {ε η ℓq Mq : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hℓq : 0 ≤ ℓq)
    (hMq : 0 ≤ Mq) (hερ : ∀ i, 2 * ε * (M + Mq) * T ≤ ρ i)
    (hηL : ∀ i, 4 * η * ‖B i‖ * stroboLip ℓ ℓq (L₂ i) M Mq T ≤ ε * T)
    (hηC : ∀ i, 2 * η * ‖B i‖ * stroboConst ℓ M Mq T ≤ ε * r₀ i * T)
    (hηK : η * stroboConst ℓ M Mq T < c * ρK * (ε * T))
    (hηr : ∀ i, η * stroboConst ℓ M Mq T ≤ c * r₀ i * (ε * T))
    {X Q : E → ℝ → E} (hX0 : ∀ y, X y 0 = y)
    (hXK : ∀ y ∈ K, ∀ t ∈ Icc 0 T, HasDerivAt (X y) (ε • f (X y t) t + Q y t) t)
    (hQK : ∀ y ∈ K, ∀ t ∈ Icc 0 T, ‖Q y t‖ ≤ η * Mq)
    (hX : ∀ i y, ‖y - ystar i‖ ≤ r₀ i → ∀ t ∈ Icc 0 T,
      HasDerivAt (X y) (ε • f (X y t) t + Q y t) t)
    (hQ : ∀ i y, ‖y - ystar i‖ ≤ r₀ i → ∀ t ∈ Icc 0 T, ‖Q y t‖ ≤ η * Mq)
    (hQl : ∀ i y y', ‖y - ystar i‖ ≤ r₀ i → ‖y' - ystar i‖ ≤ r₀ i → ∀ t ∈ Icc 0 T,
      ‖Q y t - Q y' t‖ ≤ η * ℓq * ‖X y t - X y' t‖) :
    ∃ yε : ι → E,
      (∀ i, ‖yε i - ystar i‖ ≤ 2 * η * ‖B i‖ * stroboConst ℓ M Mq T / (ε * T) ∧
        X (yε i) T = yε i) ∧
      (∀ i y, ‖y - ystar i‖ ≤ r₀ i → X y T = y → y = yε i) ∧
      ∀ y ∈ K, X y T = y → ∃ i, y = yε i ∧ c * (ε * T) * ‖y - ystar i‖ ≤
        η * stroboConst ℓ M Mq T := by
  have hT := hf.1
  have hεT : 0 < ε * T := mul_pos hε hT
  have hex : ∀ i, ∃ y, ‖y - ystar i‖ ≤ 2 * η * ‖B i‖ * stroboConst ℓ M Mq T / (ε * T) ∧
      X y T = y ∧ ∀ y', ‖y' - ystar i‖ ≤ r₀ i → X y' T = y' → y' = y := fun i =>
    exists_periodic_point_perturbed hf (hρ i) (hL₂ i) (hD i) (hDl i) (hDc i) (h0 i) (hA i)
      (hAB i) (hBA i) (hr₀ i) (hr₀ρ i) (hr₀L i) hε hε1 hηε hεη hℓq hMq (hερ i) (hηL i) (hηC i)
      hX0 (hX i) (hQ i) (hQl i)
  choose yε hyεb hyεf hyεu using hex
  refine ⟨yε, fun i => ⟨hyεb i, hyεf i⟩, fun i y hy hyT => hyεu i y hy hyT,
    fun y hy hyT => ?_⟩
  have hav := perturbed_periodic_fieldAverage_le hf hε.le hηε hεη hMq (τ := 0)
    (by rw [zero_add]; exact hXK y hy) (by rw [zero_add]; exact hQK y hy)
    (by rw [zero_add, hX0]; exact hyT)
  rw [hX0] at hav
  rcases hK _ hy with h | ⟨i, hi⟩
  · exfalso
    have h1 : c * ρK * (ε * T) ≤ ε * (T * ‖fieldAverage f T y‖) := by
      calc c * ρK * (ε * T) = ε * T * (c * ρK) := by ring
        _ ≤ ε * T * ‖fieldAverage f T y‖ := mul_le_mul_of_nonneg_left h hεT.le
        _ = ε * (T * ‖fieldAverage f T y‖) := by ring
    linarith
  · have h1 : c * (ε * T) * ‖y - ystar i‖ ≤ η * stroboConst ℓ M Mq T := by
      calc c * (ε * T) * ‖y - ystar i‖ = ε * T * (c * ‖y - ystar i‖) := by ring
        _ ≤ ε * T * ‖fieldAverage f T y‖ := mul_le_mul_of_nonneg_left hi hεT.le
        _ = ε * (T * ‖fieldAverage f T y‖) := by ring
        _ ≤ η * stroboConst ℓ M Mq T := hav
    refine ⟨i, hyεu i y ?_ hyT, h1⟩
    have h2 : c * (ε * T) * ‖y - ystar i‖ ≤ c * (ε * T) * r₀ i := by linarith [hηr i]
    exact le_of_mul_le_mul_left h2 (mul_pos hc hεT)

/-- **For all small `ε` and `η ≤ θε`, the fixed points in a compact region of the period map of a
perturbed family are its fixed points near the zeros.** Let `f` be as in
`Averaging.exists_periodic_point_perturbed` at finitely many zeros `y_i*` of `f̄` (radii `ρ(i)`),
let `K` be compact and contain no other zero of `f̄`. There are `ε₀, θ > 0` and `C ≥ 0` such that
for every `0 < ε ≤ ε₀`, `ε² ≤ η ≤ θε`, and every family `X y` (`X y 0 = y`) solving
`Ẋ = ε f(X, t) + Q y t` on `[0, T]` for `y ∈ K` and in the balls `‖y − y_i*‖ ≤ ρ(i)/2`, with
`‖Q y‖ ≤ ηM_q` there and `ηℓ_q`-Lipschitz along pairs of curves in each ball, the period map
`y ↦ X y T` has fixed points `y_ε(i)` with `‖y_ε(i) − y_i*‖ ≤ Cη/ε`, the only fixed points within
`r₀ > 0` of `y_i*`, and every fixed point in `K` is one of them
(`periodic_point_classification_perturbed`). -/
@[tmio T, powerlib_foundation] theorem periodic_point_classification_perturbed_compact
    [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ℓq Mq : ℝ} (hℓq : 0 ≤ ℓq) (hMq : 0 ≤ Mq) {ι : Type*} [Finite ι] {ystar : ι → E}
    {ρ L₂ : ι → ℝ} (hρ : ∀ i, 0 < ρ i) (hL₂ : ∀ i, 0 ≤ L₂ i)
    (hD : ∀ i x, ‖x - ystar i‖ ≤ ρ i → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ i x y, ‖x - ystar i‖ ≤ ρ i → ‖y - ystar i‖ ≤ ρ i → ∀ t,
      ‖Df x t - Df y t‖ ≤ L₂ i * ‖x - y‖)
    (hDc : ∀ i, Continuous (Df (ystar i))) (h0 : ∀ i, fieldAverage f T (ystar i) = 0)
    {A B : ι → E →L[ℝ] E} (hA : ∀ i, HasFDerivAt (fieldAverage f T) (A i) (ystar i))
    (hAB : ∀ i v, A i (B i v) = v) (hBA : ∀ i v, B i (A i v) = v) {K : Set E}
    (hK : IsCompact K) (hzero : ∀ y ∈ K, fieldAverage f T y = 0 → ∃ i, y = ystar i) :
    ∃ ε₀ θ C r₀ : ℝ, 0 < ε₀ ∧ 0 < θ ∧ 0 ≤ C ∧ 0 < r₀ ∧
      ∀ ε η, 0 < ε → ε ≤ ε₀ → ε ^ 2 ≤ η → η ≤ θ * ε →
      ∀ X Q : E → ℝ → E, (∀ y, X y 0 = y) →
      (∀ y ∈ K, ∀ t ∈ Icc 0 T, HasDerivAt (X y) (ε • f (X y t) t + Q y t) t) →
      (∀ y ∈ K, ∀ t ∈ Icc 0 T, ‖Q y t‖ ≤ η * Mq) →
      (∀ i y, ‖y - ystar i‖ ≤ ρ i / 2 → ∀ t ∈ Icc 0 T,
        HasDerivAt (X y) (ε • f (X y t) t + Q y t) t) →
      (∀ i y, ‖y - ystar i‖ ≤ ρ i / 2 → ∀ t ∈ Icc 0 T, ‖Q y t‖ ≤ η * Mq) →
      (∀ i y y', ‖y - ystar i‖ ≤ ρ i / 2 → ‖y' - ystar i‖ ≤ ρ i / 2 → ∀ t ∈ Icc 0 T,
        ‖Q y t - Q y' t‖ ≤ η * ℓq * ‖X y t - X y' t‖) →
      ∃ yε : ι → E, (∀ i, ‖yε i - ystar i‖ ≤ C * (η / ε) ∧ X (yε i) T = yε i) ∧
        (∀ i y, ‖y - ystar i‖ ≤ r₀ → X y T = y → y = yε i) ∧
        ∀ y ∈ K, X y T = y → ∃ i, y = yε i := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 0 0)
  obtain ⟨c, ρK, hc, hρK, hK'⟩ := lower_bound_of_isCompact hK
    (fieldAverage_continuous hf).continuousOn h0 hA hBA hzero
  obtain ⟨CB, hCB0, hCB⟩ := exists_ge_all fun i => ‖B i‖
  set CS := stroboConst ℓ M Mq T with hCS
  have hCS0 : 0 ≤ CS := by rw [hCS, stroboConst]; positivity
  set LS : ι → ℝ := fun i => stroboLip ℓ ℓq (L₂ i) M Mq T with hLS
  have hLS0 : ∀ i, 0 ≤ LS i := fun i => by
    simp only [hLS, stroboLip]; have := hL₂ i; positivity
  set r₀ : ι → ℝ := fun i => min (ρ i / 2) (1 / (4 * ‖B i‖ * L₂ i + 1)) with hr₀
  have hr₀0 : ∀ i, 0 < r₀ i := fun i => by
    have := hL₂ i; have := hρ i
    exact lt_min (by positivity) (by positivity)
  have hr₀2 : ∀ i, r₀ i ≤ ρ i / 2 := fun i => min_le_left _ _
  have hr₀ρ : ∀ i, 2 * r₀ i ≤ ρ i := fun i => by linarith [hr₀2 i]
  have hr₀L : ∀ i, 4 * ‖B i‖ * L₂ i * r₀ i ≤ 1 := fun i => by
    have h := min_le_right (ρ i / 2) (1 / (4 * ‖B i‖ * L₂ i + 1))
    have := hL₂ i
    have := mul_le_of_le_div_add_one (hr₀0 i).le (by positivity) h
    simp only [hr₀]; linarith
  -- the bounds on the depth and on the relative size of the perturbation at each zero
  set e : ι → ℝ := fun i => ρ i / (2 * (M + Mq) * T + 1) with he
  have he0 : ∀ i, 0 < e i := fun i => by have := hρ i; positivity
  set g : ι → ℝ := fun i => min (T / (4 * ‖B i‖ * LS i + 1))
    (min (r₀ i * T / (2 * ‖B i‖ * CS + 1)) (c * r₀ i * T / (CS + 1))) with hg
  have hg0 : ∀ i, 0 < g i := fun i => by
    have := hr₀0 i; have := hLS0 i
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  obtain ⟨e₀, he₀0, he₀⟩ := PH.exists_pos_lower _ he0
  obtain ⟨g₀, hg₀0, hg₀⟩ := PH.exists_pos_lower _ hg0
  obtain ⟨R₀, hR₀0, hR₀⟩ := PH.exists_pos_lower _ hr₀0
  set θ := min (min 1 (c * ρK * T / (CS + 1))) g₀ with hθ
  have hθ0 : 0 < θ := lt_min (lt_min one_pos (by positivity)) hg₀0
  refine ⟨min 1 e₀, θ, 2 * CB * CS / T, R₀, lt_min one_pos he₀0, hθ0, by positivity, hR₀0,
    fun ε η hε hεε₀ hεη hηθ X Q hX0 hXK hQK hX hQ hQl => ?_⟩
  have hε1 : ε ≤ 1 := hεε₀.trans (min_le_left _ _)
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hη0 : 0 ≤ η := (sq_nonneg ε).trans hεη
  have hηε : η ≤ ε := hηθ.trans (by nlinarith)
  -- `η = (η/ε) ε` with `η/ε ≤ θ`
  set τ := η / ε with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hη0 hε.le
  have hτθ : τ ≤ θ := by rw [hτ, div_le_iff₀ hε]; linarith
  have hητ : η = τ * ε := by rw [hτ]; field_simp
  have hτg : ∀ i, τ ≤ g i := fun i => (hτθ.trans (min_le_right _ _)).trans (hg₀ i)
  have hερ : ∀ i, 2 * ε * (M + Mq) * T ≤ ρ i := fun i => by
    have h := mul_le_of_le_div_add_one hε.le (by positivity : 0 ≤ 2 * (M + Mq) * T)
      ((hεε₀.trans (min_le_right _ _)).trans (he₀ i))
    linarith
  have hηL : ∀ i, 4 * η * ‖B i‖ * LS i ≤ ε * T := fun i => by
    have := hLS0 i
    have h := mul_le_of_le_div_add_one hτ0 (by positivity : 0 ≤ 4 * ‖B i‖ * LS i)
      ((hτg i).trans (min_le_left _ _))
    rw [hητ]
    nlinarith
  have hηC : ∀ i, 2 * η * ‖B i‖ * CS ≤ ε * r₀ i * T := fun i => by
    have h := mul_le_of_le_div_add_one hτ0 (by positivity : 0 ≤ 2 * ‖B i‖ * CS)
      ((hτg i).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [hητ]
    nlinarith
  have hηr : ∀ i, η * CS ≤ c * r₀ i * (ε * T) := fun i => by
    have h := mul_le_of_le_div_add_one hτ0 hCS0
      ((hτg i).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [hητ]
    nlinarith
  have hηK : η * CS < c * ρK * (ε * T) := by
    have h : τ * CS ≤ c * ρK * T * (CS / (CS + 1)) := by
      have h1 : τ ≤ c * ρK * T / (CS + 1) := hτθ.trans ((min_le_left _ _).trans (min_le_right _ _))
      calc τ * CS ≤ c * ρK * T / (CS + 1) * CS := mul_le_mul_of_nonneg_right h1 hCS0
        _ = c * ρK * T * (CS / (CS + 1)) := by ring
    have h2 : CS / (CS + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have h3 : 0 < c * ρK * T := by positivity
    rw [hητ]
    calc τ * ε * CS = ε * (τ * CS) := by ring
      _ ≤ ε * (c * ρK * T * (CS / (CS + 1))) := mul_le_mul_of_nonneg_left h hε.le
      _ < ε * (c * ρK * T * 1) := by gcongr
      _ = c * ρK * (ε * T) := by ring
  obtain ⟨yε, hyε, hun, hcl⟩ := periodic_point_classification_perturbed hf hρ hL₂ hD hDl hDc h0 hA
    hAB hBA hr₀0 hr₀ρ hr₀L hc hK' hε hε1 hηε hεη hℓq hMq hερ hηL hηC hηK hηr hX0 hXK hQK
    (fun i y hy => hX i y (hy.trans (hr₀2 i))) (fun i y hy => hQ i y (hy.trans (hr₀2 i)))
    (fun i y y' hy hy' => hQl i y y' (hy.trans (hr₀2 i)) (hy'.trans (hr₀2 i)))
  refine ⟨yε, fun i => ⟨((hyε i).1).trans ?_, (hyε i).2⟩,
    fun i y hy hyT => hun i y (hy.trans (hR₀ i)) hyT, fun y hy hyT => ?_⟩
  · have e1 : 2 * η * ‖B i‖ * CS / (ε * T) = 2 * ‖B i‖ * CS / T * (η / ε) := by
      field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ hτ0
    gcongr
    exact hCB i
  · obtain ⟨i, hyi, -⟩ := hcl y hy hyT
    exact ⟨i, hyi⟩

end Classification

end powerlib.Averaging
