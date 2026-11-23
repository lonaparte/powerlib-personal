import theorem.Flow.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import theorem.Dynamics.Calculus

/-! # Lyapunov certificates for nonlinear fields

A certificate is data whose conditions imply Flow sentences for a complete nonlinear field
`f : ℝⁿ → ℝⁿ`; it never introduces a semantics of its own.

Neither certificate presupposes that solutions exist for all time. For a C¹ field, forward
completeness follows from compact energy sublevels: a smooth cutoff makes the field globally
Lipschitz without changing it on the initial sublevel, which the cutoff solution never leaves.
The field need not be globally Lipschitz.

Scope.
* Generic: an arbitrary autonomous field on `ℝⁿ = EuclideanSpace ℝ (Fin n)` with an equilibrium
  `e`, read by the flow semantics (`theorem/Flow/Defs.lean`); no model.
* Two certificates. A quadratic-decay certificate (`QuadraticDecay`): a C¹ energy, not
  necessarily quadratic, between two positive multiples of the squared distance to the
  equilibrium and decaying at a uniform exponential rate along the field. LeanForControl's strict
  Lyapunov function (`IsStrictLyapunovFunction`).

Source: LeanForControl (`IsStrictLyapunovFunction`, Picard–Lindelöf on the forward ray,
`LeanForControl.ODEs.PicardLindelof`); Mathlib's smooth bump functions
(`Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension`) for the cutoff.

Results.
* Forward completeness: `exists_lipschitz_cutoff`, `forwardComplete_of_lipschitzWith`,
  `forwardComplete_of_compact_sublevel` (a C¹ field with a nonincreasing differentiable energy of
  compact sublevels).
* Energy estimates: `quadratic_bounds` (a continuous, quadratically homogeneous function
  positive away from the origin lies between two positive multiples of the squared norm; halves
  `quadratic_lower_bound`, `quadratic_upper_bound`),
  `energy_lower_bound`, `energy_bound_of_dissipation` (the linear Grönwall inequality
  `Dynamics.le_exp_mul_of_hasDerivWithinAt` along the solution) and `norm_bound_of_dissipation`
  (at any rate, negative rates giving growth bounds).
* `nonempty_quadraticDecay_of_homogeneous`: a C¹ quadratically homogeneous energy whose
  dissipation is bounded by a continuous homogeneous positive function is a quadratic-decay
  certificate.
* The quadratic-decay certificate proves decay at half the energy rate
  (`QuadraticDecay.decay`); with a C¹ field it proves global exponential stability, hence every
  attractive sentence, Lyapunov stability and sampled contraction
  (`QuadraticDecay.globallyExponentiallyStable`, every attractive sentence through
  `GloballyExponentiallyStable.holds`, `QuadraticDecay.forwardComplete`); also
  `QuadraticDecay.compact_sublevel` (the energy and state estimates are
  `energy_bound_of_dissipation` and `norm_bound_of_dissipation` with the certificate's fields).
* A strict Lyapunov function with compact sublevels proves global asymptotic stability of a C¹
  field, including a solution through every state
  (`globallyAsymptoticallyStable_of_strictLyapunov`).
  With `V = ‖x‖²`: `isStrictLyapunovFunction_norm_sq` and
  `globallyAsymptoticallyStable_of_inner_neg` (`f 0 = 0`, `⟪x, f x⟫ < 0` for `x ≠ 0`).
-/

noncomputable section

namespace powerlib.Flow

open Set Metric

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Forward completeness -/

/-- A smooth nonnegative cutoff makes a C¹ field globally Lipschitz without changing it on a
ball. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitz_cutoff {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 1 f)
    (R : ℝ) :
    ∃ χ : ℝⁿ → ℝ, (∀ x, 0 ≤ χ x) ∧ (∀ x, ‖x‖ ≤ R → χ x = 1) ∧
      ∃ K, LipschitzWith K (fun x => χ x • f x) := by
  let b : ContDiffBump (0 : ℝⁿ) :=
    ⟨max R 1, max R 1 + 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), by linarith⟩
  refine ⟨b, fun x => b.nonneg' x, fun x hx => ?_, ?_⟩
  · apply b.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right]
    exact hx.trans (le_max_left _ _)
  · exact ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport.smul_right
      (b.contDiff.smul hf) (by norm_num)

/-- A globally Lipschitz field is forward complete (LeanForControl's Picard–Lindelöf on the
forward ray). -/
@[tmio T, powerlib_foundation] theorem forwardComplete_of_lipschitzWith {f : ℝⁿ → ℝⁿ} {K : NNReal}
    (hf : LipschitzWith K f) : ForwardComplete f := by
  intro a x₀
  obtain ⟨φ, hφ₀, hφ, _⟩ := exists_isIntegralCurveOn_Ici
    (f := fun _ x => f x) (hf.continuous.comp continuous_snd) (fun _ => hf) a x₀
  exact ⟨φ, hφ₀, hφ⟩

/-- A C¹ field with a differentiable energy that never increases along the field and has
compact sublevels is forward complete. -/
@[tmio T, powerlib_foundation] theorem forwardComplete_of_compact_sublevel {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hf : ContDiff ℝ 1 f) (hV : Differentiable ℝ V) (hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0)
    (hsub : ∀ c : ℝ, IsCompact {x : ℝⁿ | V x ≤ c}) : ForwardComplete f := by
  intro a x₀
  obtain ⟨R, hR⟩ := (hsub (V x₀)).isBounded.subset_closedBall (0 : ℝⁿ)
  obtain ⟨χ, hχnonneg, hχone, K, hχlip⟩ := exists_lipschitz_cutoff hf R
  have hgdec : ∀ x, fderiv ℝ V x (χ x • f x) ≤ 0 := fun x => by
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hχnonneg x) (hdec x)
  obtain ⟨φ, hφa, hφ⟩ := forwardComplete_of_lipschitzWith hχlip a x₀
  have hanti : AntitoneOn (V ∘ φ) (Ici a) :=
    antitoneOn_V_comp_traj hV hV.continuous (convex_Ici a) hφ fun t _ => hgdec (φ t)
  have hstate : ∀ t ∈ Ici a, χ (φ t) = 1 := by
    intro t ht
    have hlevel : V (φ t) ≤ V x₀ := by
      simpa [Function.comp_def, hφa] using hanti (mem_Ici.mpr le_rfl) ht ht
    have hnorm : ‖φ t‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hR hlevel
    exact hχone (φ t) hnorm
  refine ⟨φ, hφa, fun t ht => ?_⟩
  simpa only [hstate t ht, one_smul] using hφ t ht

/-! ## Quadratic bounds -/

/-- **Two-sided quadratic bounds.** A continuous, quadratically homogeneous function that is
positive away from the origin of a finite-dimensional space lies between two positive multiples
of the squared norm (its minimum and maximum on the unit sphere). -/
@[tmio T, powerlib_foundation] theorem quadratic_bounds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V : E → ℝ) (hc : Continuous V)
    (hh : ∀ (a : ℝ) (x : E), V (a • x) = a ^ 2 * V x) (hp : ∀ x ≠ 0, 0 < V x) :
    ∃ α > 0, ∃ β ≥ α, ∀ x, α * ‖x‖ ^ 2 ≤ V x ∧ V x ≤ β * ‖x‖ ^ 2 := by
  have hzero : V 0 = 0 := by simpa using hh 0 0
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, 1, le_rfl, fun x => ?_⟩
    rw [Subsingleton.elim x 0, hzero, norm_zero]
    norm_num
  have hne : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v, ?_⟩
    simp [norm_smul, inv_mul_cancel₀ hn]
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hc.continuousOn
  obtain ⟨w, -, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne hc.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
  have hα : 0 < V v := hp v (by intro h; simp [h] at hvnorm)
  refine ⟨V v, hα, V w, hmax hv, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hzero]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let z := ‖x‖⁻¹ • x
    have hz : z ∈ Metric.sphere (0 : E) 1 := by
      simp [z, norm_smul, inv_mul_cancel₀ hn]
    have hs : ‖x‖ • z = x := by simp [z, smul_smul, hn]
    have he : V x = ‖x‖ ^ 2 * V z := by rw [← hh ‖x‖ z, hs]
    rw [he]
    exact ⟨by simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmin hz) (sq_nonneg ‖x‖),
      by simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmax hz) (sq_nonneg ‖x‖)⟩

/-- The lower half of `quadratic_bounds`. -/
@[tmio T, powerlib_foundation] theorem quadratic_lower_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V : E → ℝ) (hc : Continuous V)
    (hh : ∀ (a : ℝ) (x : E), V (a • x) = a ^ 2 * V x) (hp : ∀ x ≠ 0, 0 < V x) :
    ∃ α > 0, ∀ x, α * ‖x‖ ^ 2 ≤ V x :=
  let ⟨α, hα, _, _, h⟩ := quadratic_bounds V hc hh hp
  ⟨α, hα, fun x => (h x).1⟩

/-- The upper half of `quadratic_bounds`. -/
@[tmio T, powerlib_foundation] theorem quadratic_upper_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V : E → ℝ) (hc : Continuous V)
    (hh : ∀ (a : ℝ) (x : E), V (a • x) = a ^ 2 * V x) (hp : ∀ x ≠ 0, 0 < V x) :
    ∃ β > 0, ∀ x, V x ≤ β * ‖x‖ ^ 2 :=
  let ⟨_, hα, β, hβ, h⟩ := quadratic_bounds V hc hh hp
  ⟨β, hα.trans_le hβ, fun x => (h x).2⟩

/-! ## Energy comparison -/

/-- A lower bound `-ρ V` on the Lie derivative of a C¹ energy along a solution segment bounds the
energy's decay on that segment from below. -/
@[tmio T, powerlib_foundation] theorem energy_lower_bound {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV : ContDiff ℝ 1 V) {ρ : ℝ} {φ : ℝ → ℝⁿ} {a b t : ℝ} (hφ : IsTrajectoryOn φ f a b)
    (hlie : ∀ s ∈ Icc a b, -ρ * V (φ s) ≤ fderiv ℝ V (φ s) (f (φ s))) (ht : t ∈ Icc a b) :
    Real.exp (-(ρ * (t - a))) * V (φ a) ≤ V (φ t) := by
  have h := Dynamics.le_exp_mul_of_hasDerivWithinAt (g := fun s => -V (φ s))
    (g' := fun s => -fderiv ℝ V (φ s) (f (φ s))) (ρ := ρ)
    (fun s hs => (((hV.differentiable (by norm_num)) (φ s)).hasFDerivAt.comp_hasDerivWithinAt s
      (hφ s hs)).neg) (fun s hs => by linarith [hlie s hs]) t ht
  rw [neg_mul] at h
  linarith

/-! ## Quadratic-decay certificates -/

/-- Quadratic bounds on a C¹ energy and its uniform exponential decay along the field. -/
structure QuadraticDecay (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (e : ℝⁿ) where
  lower : ℝ
  upper : ℝ
  rate : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  rate_pos : 0 < rate
  smooth : ContDiff ℝ 1 V
  equilibrium : f e = 0
  lower_bound : ∀ x, lower * ‖x - e‖ ^ 2 ≤ V x
  upper_bound : ∀ x, V x ≤ upper * ‖x - e‖ ^ 2
  dissipation : ∀ x, fderiv ℝ V x (f x) ≤ -rate * V x

attribute [powerlib_foundation]
  QuadraticDecay.lower_pos QuadraticDecay.upper_pos QuadraticDecay.rate_pos
  QuadraticDecay.smooth QuadraticDecay.equilibrium QuadraticDecay.lower_bound
  QuadraticDecay.upper_bound QuadraticDecay.dissipation

/-- **Quadratic decay from homogeneous energy and dissipation.** A C¹ energy `V` and a continuous
dissipation `W ≤ −V'(x)(f x)`, both quadratically homogeneous and positive away from the
equilibrium `0`, give a quadratic-decay certificate (rate `α / β` from the bounds of
`quadratic_bounds`). -/
@[tmio T, powerlib_foundation] theorem nonempty_quadraticDecay_of_homogeneous {f : ℝⁿ → ℝⁿ}
    {V W : ℝⁿ → ℝ} (hV : ContDiff ℝ 1 V) (hVh : ∀ (a : ℝ) (x : ℝⁿ), V (a • x) = a ^ 2 * V x)
    (hVp : ∀ x ≠ 0, 0 < V x) (hWc : Continuous W)
    (hWh : ∀ (a : ℝ) (x : ℝⁿ), W (a • x) = a ^ 2 * W x) (hWp : ∀ x ≠ 0, 0 < W x)
    (he : f 0 = 0) (hdiss : ∀ x, fderiv ℝ V x (f x) ≤ -W x) :
    Nonempty (QuadraticDecay f V 0) := by
  obtain ⟨a, ha, b, hab, hVb⟩ := quadratic_bounds V hV.continuous hVh hVp
  obtain ⟨α, hα, hW⟩ := quadratic_lower_bound W hWc hWh hWp
  have hb : 0 < b := ha.trans_le hab
  refine ⟨⟨a, b, α / b, ha, hb, div_pos hα hb, hV, he, fun x => by simpa using (hVb x).1,
    fun x => by simpa using (hVb x).2, fun x => (hdiss x).trans ?_⟩⟩
  have h : α / b * V x ≤ α * ‖x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb]
    nlinarith [(hVb x).2, sq_nonneg ‖x‖]
  linarith [hW x]

/-- Integrating an energy inequality needs no positivity assumption on its rate.
Negative rates give growth bounds, and zero gives a bounded energy. -/
@[tmio T, powerlib_foundation] theorem energy_bound_of_dissipation {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    {rate : ℝ} (smooth : ContDiff ℝ 1 V)
    (dissipation : ∀ x, fderiv ℝ V x (f x) ≤ -rate * V x)
    {φ : ℝ → ℝⁿ} {a b t : ℝ} (hφ : IsTrajectoryOn φ f a b) (ht : t ∈ Icc a b) :
    V (φ t) ≤ Real.exp (-(rate * (t - a))) * V (φ a) := by
  have h := Dynamics.le_exp_mul_of_hasDerivWithinAt (g := fun s => V (φ s))
    (g' := fun s => fderiv ℝ V (φ s) (f (φ s))) (ρ := rate)
    (fun s hs => ((smooth.differentiable (by norm_num)) (φ s)).hasFDerivAt.comp_hasDerivWithinAt s
      (hφ s hs)) (fun s _ => dissipation (φ s)) t ht
  rwa [neg_mul] at h

/-- Quadratic bounds convert the arbitrary-rate energy estimate to a state estimate. -/
@[tmio T, powerlib_foundation] theorem norm_bound_of_dissipation {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    {e : ℝⁿ} {rate lower upper : ℝ} (smooth : ContDiff ℝ 1 V)
    (hlo : 0 < lower) (hup : 0 < upper)
    (lower_bound : ∀ x, lower * ‖x - e‖ ^ 2 ≤ V x)
    (upper_bound : ∀ x, V x ≤ upper * ‖x - e‖ ^ 2)
    (dissipation : ∀ x, fderiv ℝ V x (f x) ≤ -rate * V x)
    {φ : ℝ → ℝⁿ} {a b t : ℝ} (hφ : IsTrajectoryOn φ f a b) (ht : t ∈ Icc a b) :
    ‖φ t - e‖ ≤ Real.sqrt (upper / lower) * Real.exp (-(rate / 2) * (t - a)) * ‖φ a - e‖ := by
  have henergy := (lower_bound (φ t)).trans
    ((energy_bound_of_dissipation smooth dissipation hφ ht).trans
      (mul_le_mul_of_nonneg_left (upper_bound (φ a)) (Real.exp_nonneg _)))
  have hsquared : ‖φ t - e‖ ^ 2 ≤
      (upper / lower) * Real.exp (-(rate * (t - a))) * ‖φ a - e‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hlo).mp
    convert! henergy using 1
    field_simp [hlo.ne']
  have hratio : 0 ≤ upper / lower := (div_pos hup hlo).le
  have hexp : Real.exp (-(rate / 2) * (t - a)) ^ 2 = Real.exp (-(rate * (t - a))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hratio, hexp] using hsquared

namespace QuadraticDecay

/-- Quadratic coercivity and continuity make every energy sublevel compact. -/
@[tmio T, powerlib_foundation] theorem compact_sublevel {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) (level : ℝ) :
    IsCompact {x : ℝⁿ | V x ≤ level} := by
  apply (isCompact_closedBall e (Real.sqrt (level / c.lower))).of_isClosed_subset
    (isClosed_le c.smooth.continuous continuous_const)
  intro x hx
  have hsquared : ‖x - e‖ ^ 2 ≤ level / c.lower := by
    apply (le_div_iff₀ c.lower_pos).mpr
    simpa only [mul_comm] using (c.lower_bound x).trans hx
  simpa only [mem_closedBall, dist_eq_norm] using Real.le_sqrt_of_sq_le hsquared

/-- With a C¹ field, the certificate supplies a solution through every state. -/
@[tmio T, powerlib_foundation, aesop unsafe 80% apply]
theorem forwardComplete {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) (hf : ContDiff ℝ 1 f) :
    ForwardComplete f := by
  refine forwardComplete_of_compact_sublevel hf (c.smooth.differentiable (by norm_num))
    (fun x => (c.dissipation x).trans ?_) c.compact_sublevel
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr c.rate_pos.le)
    ((mul_nonneg c.lower_pos.le (sq_nonneg _)).trans (c.lower_bound x))

/-- The certificate proves decay at half its energy rate. -/
@[tmio T, powerlib_foundation] theorem decay {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) : Decay f e (c.rate / 2) :=
  ⟨_, fun _ _ _ hφ _ ht => norm_bound_of_dissipation c.smooth c.lower_pos c.upper_pos
    c.lower_bound c.upper_bound c.dissipation hφ ht⟩

/-- The certificate proves global exponential stability. -/
@[tmio T, powerlib_foundation, aesop unsafe 80% apply]
theorem globallyExponentiallyStable {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e)
    (hf : ContDiff ℝ 1 f) : GloballyExponentiallyStable f e :=
  ⟨c.equilibrium, c.forwardComplete hf, c.rate / 2, half_pos c.rate_pos, c.decay⟩

end QuadraticDecay

/-! ## Strict Lyapunov functions -/

/-- A strict Lyapunov function with compact sublevels proves global asymptotic stability of a
C¹ field, including a solution through every state. -/
@[tmio T, powerlib_foundation] theorem globallyAsymptoticallyStable_of_strictLyapunov {f : ℝⁿ → ℝⁿ}
    {V : ℝⁿ → ℝ} {e : ℝⁿ} (hn : 0 < n) (hf : ContDiff ℝ 1 f)
    (hV : IsStrictLyapunovFunction f V e) : GloballyAsymptoticallyStable f e := by
  have hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0 := by
    intro x
    by_cases hx : x = e
    · subst hx
      simp [hV.hequil]
    · exact (hV.hLie_neg x hx).le
  exact ⟨hV.hequil, forwardComplete_of_compact_sublevel hf
    (hV.hV_c1.differentiable (by norm_num)) hdec hV.hbounded_sublevel,
    lyapunov_asymptotic_stable hn hV hf.continuous⟩

/-- **The squared norm as a strict Lyapunov function.** If `f 0 = 0` and `⟪x, f x⟫ < 0` for every
`x ≠ 0`, then `‖x‖²` is a strict Lyapunov function of `f` at `0` (its sublevels are balls). -/
@[tmio T, powerlib_foundation] theorem isStrictLyapunovFunction_norm_sq {f : ℝⁿ → ℝⁿ}
    (hf0 : f 0 = 0) (hneg : ∀ x, x ≠ 0 → inner ℝ x (f x) < 0) :
    IsStrictLyapunovFunction f (fun x => ‖x‖ ^ 2) 0 where
  hcont := continuous_norm.pow 2
  hV_c1 := contDiff_norm_sq ℝ
  hzero := by simp
  hpos := fun x hx => by positivity
  hequil := hf0
  hLie_neg := fun x hx => by
    rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
    simpa using mul_neg_of_pos_of_neg two_pos (hneg x hx)
  hbounded_sublevel := fun c => by
    refine (isCompact_closedBall (0 : ℝⁿ) (Real.sqrt (max c 0))).of_isClosed_subset
      (isClosed_le (continuous_norm.pow 2) continuous_const) fun x hx => ?_
    rw [mem_closedBall, dist_zero_right]
    exact Real.le_sqrt_of_sq_le ((Set.mem_ofPred_eq ▸ hx).trans (le_max_left _ _))

/-- **Global asymptotic stability from an inward field.** A `C¹` field with `f 0 = 0` and
`⟪x, f x⟫ < 0` for every `x ≠ 0` is globally asymptotically stable at `0`
(`isStrictLyapunovFunction_norm_sq`). -/
@[tmio T, powerlib_foundation] theorem globallyAsymptoticallyStable_of_inner_neg {f : ℝⁿ → ℝⁿ}
    (hn : 0 < n) (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    (hneg : ∀ x, x ≠ 0 → inner ℝ x (f x) < 0) : GloballyAsymptoticallyStable f 0 :=
  globallyAsymptoticallyStable_of_strictLyapunov hn hf (isStrictLyapunovFunction_norm_sq hf0 hneg)

end powerlib.Flow
