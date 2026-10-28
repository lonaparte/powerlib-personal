import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Locality

/-! # Local Lyapunov criteria (foundation)

Lyapunov theorems for local asymptotic and Lyapunov stability in the local forms needed near
degenerate points: punctured-ball and eventual hypotheses, fields regular only near the point,
and composite energies.

Scope.
* Autonomous continuous-time ODE `ẋ = f x` on `Dynamics.State n = EuclideanSpace ℝ (Fin n)`; no
  input, delay, switching or time variation. Solutions are `IsIntegralCurveOn` curves,
  `V̇ x = fderiv ℝ V x (f x)`.
* Nothing here describes a physical system: every statement is a generic implication about an
  arbitrary field and function, a foundation result.

Source: Khalil, *Nonlinear Systems* (3rd ed.), Theorems 4.1 and 4.3 (local forms); the Hopf and
saddle-node normal forms (Guckenheimer–Holmes, §3.4, §3.1) only motivate the eventual form of the
hypotheses; infrastructure for work-sync `projects/vsc-parametric-oscillation` (four-state GFL weak
focus) and `theory/T-vsc-dc-voltage-control.md` §1.4.

Results.
* `localAsymptoticStable_of_lie_neg`: a `C¹` function `V` vanishing at the point, positive on the
  punctured ball `0 < ‖x − x₀‖ < R` and strictly decreasing along a field that is only continuous
  on that ball makes the point locally asymptotically stable. Unlike LeanForControl's
  `lyapunov_local_asymptotic_stable` (`IsStrictLocalLyapunovFunction`), no global sublevel set of
  `V` has to be compact, no equilibrium hypothesis is needed and `f` need not be continuous
  outside the ball: this is the form needed for a composite Lyapunov function (a cascade energy
  plus an averaging correction plus a quadratic form on the slaved coordinates) that is only valid
  near the point, and for a physical field with a `1 / V` term regularized away from `V = 0`. The
  Lyapunov stability part is LeanForControl's `lyapunov_stable`; attractivity is the uniform-decay
  argument on a compact annulus (`antitoneOn_V_add_linear`).
* `localAsymptoticStable_of_eventually_lyapunov`: the same with the hypotheses on a punctured
  neighbourhood (`∀ᶠ x in 𝓝[≠] x_eq`), the form in which normal-form computations at a Hopf point
  deliver them (`exists_radius_of_eventually` turns such a hypothesis into a ball).
* `isEquilibrium_of_lyapunovStable_local`: a Lyapunov stable point of a field that is `C¹` on an
  open neighbourhood is an equilibrium (`isEquilibrium_of_lyapunovStable` for globally `C¹`
  fields is in `theorem/Dynamics/ConverseLinearization.lean`).
* `exists_forward_of_lyapunovStable`: near a Lyapunov stable point of a `C¹` field every state has
  a solution on the whole forward ray (smooth cutoff, LeanForControl's Picard–Lindelöf, first
  sphere hit).
* `lyapunovStable_of_inner_nonpos`: a quadratic energy `‖T x‖²` (`T` injective linear) that does
  not increase gives Lyapunov stability, also with a singular Jacobian.
* Composite energies: `hasDerivAt_sq_max_zero`, `contDiff_one_sq_max_zero` (`t ↦ (max t 0)²` is
  `C¹` with derivative `2 max t 0`, the building block of the "practical" Lyapunov functions
  `((g − λ E)⁺)² + E` used for cascades of a centre with a contracting state) and the chain rules
  `fderiv_sq_sub_add_apply`, `fderiv_sq_max_add_apply` for `(V − c)² + E` and `(max g 0)² + E`.

The instability counterparts (Chetaev in its classical, local, eventual and exponential forms, and
the obstructions to local asymptotic stability) are in `theorem/Dynamics/Instability.lean`.
-/

noncomputable section
namespace powerlib.Dynamics

/-! ## Strict Lyapunov functions on a ball and on a punctured neighbourhood -/

section Strict

open Set Filter Topology Metric Asymptotics

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- A radius on which an eventual punctured-neighbourhood property holds. -/
@[tmio T, powerlib_foundation] theorem exists_radius_of_eventually {x_eq : ℝⁿ} {P : ℝⁿ → Prop}
    (h : ∀ᶠ x in 𝓝[≠] x_eq, P x) :
    ∃ r > 0, ∀ x, ‖x - x_eq‖ < r → x ≠ x_eq → P x := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨r, hr, h⟩ := h
  exact ⟨r, hr, fun x hx hne => h (by rwa [dist_eq_norm]) hne⟩

/-- **Local strict Lyapunov function.** A `C¹` function that vanishes at the point, is positive on
a punctured ball around it and strictly decreases along a field continuous on that ball makes the
point locally asymptotically stable. No hypothesis is made on the field outside the ball, and no
global sublevel set needs to be compact. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_lie_neg (hn : 0 < n)
    {f : State n → State n} {x : State n}
    {V : State n → ℝ} {R : ℝ} (hR : 0 < R) (hV : ContDiff ℝ 1 V)
    (hf : ContinuousOn f (Metric.ball x R)) (hV0 : V x = 0)
    (hpos : ∀ y, ‖y - x‖ < R → y ≠ x → 0 < V y)
    (hLie : ∀ y, ‖y - x‖ < R → y ≠ x → fderiv ℝ V y (f y) < 0) :
    LocalAsymptoticStable f x := by
  have hVd : Differentiable ℝ V := hV.differentiable one_ne_zero
  have hmin : IsLocalMin V x := by
    filter_upwards [Metric.ball_mem_nhds x hR] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rcases eq_or_ne y x with rfl | hne
    · exact le_rfl
    · rw [hV0]; exact (hpos y hy hne).le
  have hfd0 : fderiv ℝ V x = 0 := hmin.fderiv_eq_zero
  have hLS : LyapunovStable f x := by
    refine lyapunov_stable (D := Metric.ball x R) hn
      ⟨Metric.isOpen_ball, Metric.mem_ball_self hR, hV.continuous, hVd, hV0,
        fun y hy hne => hpos y (by rwa [Metric.mem_ball, dist_eq_norm] at hy) hne,
        fun y hy => ?_⟩
    rcases eq_or_ne y x with rfl | hne
    · rw [hfd0]; simp
    · exact (hLie y (by rwa [Metric.mem_ball, dist_eq_norm] at hy) hne).le
  refine ⟨hLS, ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hLS (R / 2) (by positivity)
  refine ⟨δ, hδ, fun t₀ φ hφ h0 => ?_⟩
  have hin : ∀ t, t₀ ≤ t → ‖φ t - x‖ < R / 2 := fun t ht =>
    hb t₀ t φ (hφ.mono Icc_subset_Ici_self) h0 t ⟨ht, le_rfl⟩
  have hLc : ContinuousOn (fun y => fderiv ℝ V y (f y)) (Metric.ball x R) :=
    ((hV.continuous_fderiv one_ne_zero).continuousOn).clm_apply hf
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δη, hδη, hbη⟩ := hLS η hη
  -- the solution enters the ball of radius `δη`
  have henter : ∃ T, t₀ ≤ T ∧ ‖φ T - x‖ < δη := by
    by_contra hno
    push Not at hno
    set K := {y : State n | δη ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ R / 2} with hK
    have hKc : IsCompact K := by
      refine (isCompact_closedBall x (R / 2)).of_isClosed_subset ?_ fun y hy => ?_
      · exact (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right x))).inter
          (isClosed_le (continuous_norm.comp (continuous_sub_right x)) continuous_const)
      · rw [Metric.mem_closedBall, dist_eq_norm]; exact hy.2
    have hKR : K ⊆ Metric.ball x R := fun y hy => by
      rw [Metric.mem_ball, dist_eq_norm]; linarith [hy.2]
    have hφK : ∀ t, t₀ ≤ t → φ t ∈ K := fun t ht => ⟨hno t ht, (hin t ht).le⟩
    obtain ⟨ym, hymK, hmax⟩ := hKc.exists_isMaxOn ⟨φ t₀, hφK t₀ le_rfl⟩ (hLc.mono hKR)
    have hym0 : ym ≠ x := fun h => by
      have := hymK.1; rw [h, sub_self, norm_zero] at this; linarith
    have hγ : fderiv ℝ V ym (f ym) < 0 := hLie ym (by linarith [hymK.2]) hym0
    set γ := -fderiv ℝ V ym (f ym) with hγdef
    have hγ0 : 0 < γ := by linarith
    have hanti := antitoneOn_V_add_linear (c := γ) hVd hV.continuous (convex_Ici t₀) hφ
      (fun t ht => by
        have := hmax (hφK t (interior_subset ht))
        simp only [Set.mem_ofPred_eq] at this
        linarith)
    set T := t₀ + V (φ t₀) / γ + 1 with hT
    have hVφ0 : 0 ≤ V (φ t₀) := by
      rcases eq_or_ne (φ t₀) x with h | h
      · rw [h, hV0]
      · exact (hpos _ (by linarith [hin t₀ le_rfl]) h).le
    have hT0 : t₀ ≤ T := by
      have : 0 ≤ V (φ t₀) / γ := div_nonneg hVφ0 hγ0.le
      linarith
    have h1 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT0) hT0
    simp only at h1
    have hVT : 0 ≤ V (φ T) := by
      rcases eq_or_ne (φ T) x with h | h
      · rw [h, hV0]
      · exact (hpos _ (by linarith [hin T hT0]) h).le
    have : γ * T = γ * t₀ + V (φ t₀) + γ := by
      rw [hT, mul_add, mul_add, mul_div_cancel₀ _ hγ0.ne', mul_one]
    linarith
  obtain ⟨T, hT, hTδ⟩ := henter
  refine ⟨T, fun t ht => ?_⟩
  rw [dist_eq_norm]
  exact hbη T t φ (hφ.mono fun u hu => le_trans hT hu.1) hTδ t ⟨ht, le_rfl⟩

/-- **Local asymptotic stability from a local strict Lyapunov function.** A `C¹` function that
vanishes at an equilibrium of a `C¹` field and is positive with negative derivative along the
field on a punctured neighbourhood makes the equilibrium locally asymptotically stable. No
global compactness of sublevel sets is needed. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_eventually_lyapunov (hn : 0 < n)
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {W : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (_hfx : f x_eq = 0)
    (hW : ContDiff ℝ 1 W) (hW0 : W x_eq = 0) (hpos : ∀ᶠ x in 𝓝[≠] x_eq, 0 < W x)
    (hLie : ∀ᶠ x in 𝓝[≠] x_eq, fderiv ℝ W x (f x) < 0) :
    LocalAsymptoticStable f x_eq := by
  obtain ⟨r, hr, hball⟩ := exists_radius_of_eventually (hpos.and hLie)
  exact localAsymptoticStable_of_lie_neg hn hr hW hf.continuous.continuousOn hW0
    (fun x hx hne => (hball x hx hne).1) fun x hx hne => (hball x hx hne).2

end Strict

/-! ## Lyapunov stability -/

section Stable

open Set Filter Topology Metric

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A Lyapunov stable point of a field that is `C¹` on an open neighbourhood is an equilibrium. -/
@[tmio T, powerlib_foundation] theorem isEquilibrium_of_lyapunovStable_local {f : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    {U : Set ℝⁿ} (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ 1 f U)
    (h : LyapunovStable f x) : f x = 0 := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  have hgx : g x = 0 := isEquilibrium_of_lyapunovStable hg (lyapunovStable_congr_nhds hgf h)
  rw [← hgf.eq_of_nhds]
  exact hgx

/-- Near a Lyapunov stable point of a `C¹` field every state has a solution on the whole forward
ray, which stays within distance `1/2` of the point. -/
@[tmio T, powerlib_foundation] theorem exists_forward_of_lyapunovStable {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (h : LyapunovStable f x_eq) :
    ∃ δ > 0, ∀ y : ℝⁿ, ‖y - x_eq‖ < δ → ∃ φ : ℝ → ℝⁿ, φ 0 = y ∧
      IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) ∧ ∀ t, 0 ≤ t → ‖φ t - x_eq‖ < 1 / 2 := by
  obtain ⟨g, K, hK, hg⟩ := exists_lipschitz_cutoff_near hf x_eq
  obtain ⟨δ, hδ, hb⟩ := h (1 / 2) (by norm_num)
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun y hy => ?_⟩
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hK 0 y
  have h0 : ‖ψ 0 - x_eq‖ < 1 / 2 := by rw [hψ0]; exact hy.trans_le (min_le_right _ _)
  have hstay : ∀ t, 0 ≤ t → ‖ψ t - x_eq‖ < 1 / 2 := by
    intro t ht
    by_contra hfar0
    have hfar := not_lt.mp hfar0
    obtain ⟨τ, hτ, hτeq, hτin⟩ := exists_first_sphere_hit
      (hψ.continuousOn.mono (Icc_subset_Ici_self : Icc (0 : ℝ) t ⊆ Ici 0)) h0
      ⟨ht, le_rfl⟩ hfar
    have htraj : IsTrajectoryOn ψ f 0 τ := isTrajectoryOn_of_cutoff hg hψ fun s hs => by
      rw [dist_eq_norm]; linarith [hτin s hs]
    have hlt := hb 0 τ ψ htraj (by rw [hψ0]; exact hy.trans_le (min_le_left _ _)) τ
      ⟨hτ.1, le_rfl⟩
    linarith
  refine ⟨ψ, hψ0, fun t ht => ?_, hstay⟩
  have hd := hψ t ht
  have hgt : g (ψ t) = f (ψ t) := hg _ (by rw [dist_eq_norm]; linarith [hstay t ht])
  simp only at hd ⊢
  rw [← hgt]
  exact hd

/-- A quadratic energy `‖T x‖²` of an injective linear map `T` that does not increase along the
field makes the origin Lyapunov stable. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_inner_nonpos {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hn : 0 < n) {f : ℝⁿ → ℝⁿ} (T : ℝⁿ →L[ℝ] E)
    (hT : Function.Injective T) (h : ∀ x, inner ℝ (T x) (T (f x)) ≤ 0) :
    LyapunovStable f 0 := by
  have hd : ∀ x, HasFDerivAt (fun x => ‖T x‖ ^ 2) (2 • (innerSL ℝ (T x)).comp T) x :=
    fun x => T.hasFDerivAt.norm_sq
  refine lyapunov_stable (V := fun x => ‖T x‖ ^ 2) (D := univ) hn
    ⟨isOpen_univ, mem_univ _, by fun_prop, fun x => (hd x).differentiableAt, by simp,
      fun x _ hx => ?_, fun x _ => ?_⟩
  · have : T x ≠ 0 := fun h0 => hx (hT (by rw [h0, map_zero]))
    positivity
  · rw [(hd x).fderiv]
    show (2 : ℕ) • inner ℝ (T x) (T (f x)) ≤ 0
    rw [nsmul_eq_mul]
    nlinarith [h x]

/-! ## Composite energies -/

/-- `t ↦ (max t 0)²` has derivative `2 max t 0` everywhere. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_sq_max_zero (t : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [max_eq_right (le_of_lt (mem_Iio.mp hs))]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst ht
    rw [max_self, mul_zero, hasDerivAt_iff_isLittleO]
    simp only [max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      smul_zero]
    refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with s hs
    rw [Metric.mem_ball, dist_zero_right] at hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : max s 0 ^ 2 ≤ s ^ 2 := by
      rcases le_total s 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg s]
      · rw [max_eq_left h]
    have h2 : s ^ 2 = |s| * |s| := by rw [← sq_abs, sq]
    calc max s 0 ^ 2 ≤ |s| * |s| := h2 ▸ h1
      _ ≤ c * |s| := mul_le_mul_of_nonneg_right hs.le (abs_nonneg s)
  · have hev : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 t] fun s => s ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [max_eq_left (le_of_lt (mem_Ioi.mp hs))]
    rw [max_eq_left ht.le]
    have h : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
    exact h.congr_of_eventuallyEq hev

/-- `t ↦ (max t 0)²` is `C¹`. -/
@[tmio T, powerlib_foundation] theorem contDiff_one_sq_max_zero :
    ContDiff ℝ 1 (fun s : ℝ => max s 0 ^ 2) := by
  rw [contDiff_one_iff_deriv]
  have hd : deriv (fun s : ℝ => max s 0 ^ 2) = fun t => 2 * max t 0 :=
    funext fun t => (hasDerivAt_sq_max_zero t).deriv
  refine ⟨fun t => (hasDerivAt_sq_max_zero t).differentiableAt, ?_⟩
  rw [hd]
  fun_prop

/-- The derivative of `(V − c)² + E` in the direction `v`. -/
@[tmio T, powerlib_foundation] theorem fderiv_sq_sub_add_apply {V E : ℝⁿ → ℝ} {x : ℝⁿ}
    (hV : DifferentiableAt ℝ V x) (hE : DifferentiableAt ℝ E x) (c : ℝ) (v : ℝⁿ) :
    fderiv ℝ (fun y => (V y - c) ^ 2 + E y) x v =
      2 * (V x - c) * fderiv ℝ V x v + fderiv ℝ E x v := by
  have h := ((hV.hasFDerivAt.sub_const c).pow 2).add hE.hasFDerivAt
  rw [show (fun y => (V y - c) ^ 2 + E y) = (fun y => (V y - c) ^ 2) + E from rfl, h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The derivative of `(max g 0)² + E` in the direction `v`. -/
@[tmio T, powerlib_foundation] theorem fderiv_sq_max_add_apply {g E : ℝⁿ → ℝ} {x : ℝⁿ}
    (hg : DifferentiableAt ℝ g x) (hE : DifferentiableAt ℝ E x) (v : ℝⁿ) :
    fderiv ℝ (fun y => max (g y) 0 ^ 2 + E y) x v =
      2 * max (g x) 0 * fderiv ℝ g x v + fderiv ℝ E x v := by
  have h := ((hasDerivAt_sq_max_zero (g x)).comp_hasFDerivAt x hg.hasFDerivAt).add
    hE.hasFDerivAt
  rw [show (fun y => max (g y) 0 ^ 2 + E y) = (fun s : ℝ => max s 0 ^ 2) ∘ g + E from rfl,
    h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]

end Stable

end powerlib.Dynamics
