import theorem.Flow.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Lyapunov certificates for nonlinear fields

A certificate is data whose conditions imply Flow sentences for a complete nonlinear field
`f : ℝⁿ → ℝⁿ`; it never introduces a semantics of its own.

* A quadratic-decay certificate (`QuadraticDecay`): a C¹ energy, not necessarily quadratic,
  between two positive multiples of the squared distance to the equilibrium and decaying at a
  uniform exponential rate along the field. It proves decay at half the energy rate; with a C¹
  field it proves global exponential stability, hence every attractive sentence, Lyapunov
  stability and sampled contraction.
* LeanForControl's strict Lyapunov function (`IsStrictLyapunovFunction`) proves global asymptotic
  stability.

Neither certificate presupposes that solutions exist for all time. For a C¹ field, forward
completeness follows from compact energy sublevels: a smooth cutoff makes the field globally
Lipschitz without changing it on the initial sublevel, which the cutoff solution never leaves.
The field need not be globally Lipschitz. -/

noncomputable section

namespace powerlib.Flow

open Set Metric

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Forward completeness -/

/-- A smooth nonnegative cutoff makes a C¹ field globally Lipschitz without changing it on a
ball. -/
@[powerlib_foundation] theorem exists_lipschitz_cutoff {f : ℝⁿ → ℝⁿ} (hf : ContDiff ℝ 1 f)
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
@[powerlib_foundation] theorem forwardComplete_of_lipschitzWith {f : ℝⁿ → ℝⁿ} {K : NNReal}
    (hf : LipschitzWith K f) : ForwardComplete f := by
  intro a x₀
  obtain ⟨φ, hφ₀, hφ, _⟩ := exists_isIntegralCurveOn_Ici
    (f := fun _ x => f x) (hf.continuous.comp continuous_snd) (fun _ => hf) a x₀
  exact ⟨φ, hφ₀, hφ⟩

/-- A C¹ field with a differentiable energy that never increases along the field and has
compact sublevels is forward complete. -/
@[powerlib_foundation] theorem forwardComplete_of_compact_sublevel {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
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

/-- A continuous, quadratically homogeneous function that is positive away from the origin of a
finite-dimensional space lies between two positive multiples of the squared norm. -/
@[powerlib_foundation] theorem quadratic_bounds {E : Type*} [NormedAddCommGroup E]
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
  obtain ⟨w, hw, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne hc.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
  have hα : 0 < V v := hp v (by intro h; simp [h] at hvnorm)
  refine ⟨V v, hα, V w, hmin hw, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, hzero]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let z := ‖x‖⁻¹ • x
    have hz : z ∈ Metric.sphere (0 : E) 1 := by
      simp [z, norm_smul, inv_mul_cancel₀ hn]
    have hs : ‖x‖ • z = x := by simp [z, smul_smul, hn]
    have he : V x = ‖x‖ ^ 2 * V z := by rw [← hh ‖x‖ z, hs]
    rw [he]
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmin hz) (sq_nonneg ‖x‖)
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmax hz) (sq_nonneg ‖x‖)

/-! ## Energy comparison -/

/-- A lower bound `-ρ V` on the Lie derivative of a C¹ energy along a solution segment bounds the
energy's decay on that segment from below. -/
@[powerlib_foundation] theorem energy_lower_bound {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV : ContDiff ℝ 1 V) {ρ : ℝ} {φ : ℝ → ℝⁿ} {a b t : ℝ} (hφ : IsTrajectoryOn φ f a b)
    (hlie : ∀ s ∈ Icc a b, -ρ * V (φ s) ≤ fderiv ℝ V (φ s) (f (φ s))) (ht : t ∈ Icc a b) :
    Real.exp (-(ρ * (t - a))) * V (φ a) ≤ V (φ t) := by
  let W : ℝ → ℝ := fun s => Real.exp (ρ * (s - a)) * V (φ s)
  let W' : ℝ → ℝ := fun s =>
    Real.exp (ρ * (s - a)) * (ρ * V (φ s) + fderiv ℝ V (φ s) (f (φ s)))
  have hW : ∀ s ∈ Icc a b, HasDerivWithinAt W (W' s) (Icc a b) s := by
    intro s hs
    have hexp : HasDerivAt (fun u => Real.exp (ρ * (u - a))) (Real.exp (ρ * (s - a)) * ρ) s := by
      simpa only [id_eq, mul_one, mul_comm] using
        (((hasDerivAt_id s).sub_const a).const_mul ρ).exp
    have hVd : HasDerivWithinAt (fun s => V (φ s)) (fderiv ℝ V (φ s) (f (φ s))) (Icc a b) s :=
      ((hV.differentiable (by norm_num)) (φ s)).hasFDerivAt.comp_hasDerivWithinAt s (hφ s hs)
    convert! hexp.hasDerivWithinAt.mul hVd using 1
    dsimp [W']
    ring
  have hmono : MonotoneOn W (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun s hs => (hW s hs).continuousWithinAt)
    · exact fun s hs => (hW s (interior_subset hs)).mono interior_subset
    · intro s hs
      apply mul_nonneg (Real.exp_nonneg _)
      linarith [hlie s (interior_subset hs)]
  have hbound := hmono (left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-(ρ * (t - a))))
  have hcancel : Real.exp (-(ρ * (t - a))) * Real.exp (ρ * (t - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa [W, mul_assoc, ← mul_assoc, hcancel] using hmul

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

namespace QuadraticDecay

/-- Integrating the decay inequality along any solution segment. -/
@[powerlib_foundation] theorem energy_bound {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) {φ : ℝ → ℝⁿ} {a b t : ℝ}
    (hφ : IsTrajectoryOn φ f a b) (ht : t ∈ Icc a b) :
    V (φ t) ≤ Real.exp (-(c.rate * (t - a))) * V (φ a) := by
  let W : ℝ → ℝ := fun s => Real.exp (c.rate * (s - a)) * V (φ s)
  let W' : ℝ → ℝ := fun s =>
    Real.exp (c.rate * (s - a)) * (c.rate * V (φ s) + fderiv ℝ V (φ s) (f (φ s)))
  have hW : ∀ s ∈ Icc a b, HasDerivWithinAt W (W' s) (Icc a b) s := by
    intro s hs
    have hexp : HasDerivAt (fun u => Real.exp (c.rate * (u - a)))
        (Real.exp (c.rate * (s - a)) * c.rate) s := by
      simpa only [id_eq, mul_one, mul_comm] using
        (((hasDerivAt_id s).sub_const a).const_mul c.rate).exp
    have hV : HasDerivWithinAt (fun s => V (φ s)) (fderiv ℝ V (φ s) (f (φ s))) (Icc a b) s :=
      ((c.smooth.differentiable (by norm_num)) (φ s)).hasFDerivAt.comp_hasDerivWithinAt s
        (hφ s hs)
    convert! hexp.hasDerivWithinAt.mul hV using 1
    dsimp [W']
    ring
  have hmono : AntitoneOn W (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun s hs => (hW s hs).continuousWithinAt)
    · exact fun s hs => (hW s (interior_subset hs)).mono interior_subset
    · intro s _
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      linarith [c.dissipation (φ s)]
  have hbound := hmono (left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-(c.rate * (t - a))))
  have hcancel : Real.exp (-(c.rate * (t - a))) * Real.exp (c.rate * (t - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa [W, mul_assoc, ← mul_assoc, hcancel] using hmul

/-- The energy estimate as an estimate on the state. -/
@[powerlib_foundation] theorem norm_bound {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) {φ : ℝ → ℝⁿ} {a b t : ℝ}
    (hφ : IsTrajectoryOn φ f a b) (ht : t ∈ Icc a b) :
    ‖φ t - e‖ ≤ Real.sqrt (c.upper / c.lower) * Real.exp (-(c.rate / 2) * (t - a)) * ‖φ a - e‖ := by
  have henergy := (c.lower_bound (φ t)).trans ((c.energy_bound hφ ht).trans
    (mul_le_mul_of_nonneg_left (c.upper_bound (φ a)) (Real.exp_nonneg _)))
  have hsquared : ‖φ t - e‖ ^ 2 ≤
      (c.upper / c.lower) * Real.exp (-(c.rate * (t - a))) * ‖φ a - e‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ c.lower_pos).mp
    convert! henergy using 1
    field_simp [c.lower_pos.ne']
  have hratio : 0 ≤ c.upper / c.lower := (div_pos c.upper_pos c.lower_pos).le
  have hexp : Real.exp (-(c.rate / 2) * (t - a)) ^ 2 = Real.exp (-(c.rate * (t - a))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hratio, hexp] using hsquared

/-- Quadratic coercivity and continuity make every energy sublevel compact. -/
@[powerlib_foundation] theorem compact_sublevel {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
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
@[powerlib_foundation, aesop unsafe 80% apply]
theorem forwardComplete {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) (hf : ContDiff ℝ 1 f) :
    ForwardComplete f := by
  refine forwardComplete_of_compact_sublevel hf (c.smooth.differentiable (by norm_num))
    (fun x => (c.dissipation x).trans ?_) c.compact_sublevel
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr c.rate_pos.le)
    ((mul_nonneg c.lower_pos.le (sq_nonneg _)).trans (c.lower_bound x))

/-- The certificate proves global exponential stability. -/
@[powerlib_foundation, aesop unsafe 80% apply]
theorem globallyExponentiallyStable {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e)
    (hf : ContDiff ℝ 1 f) : GloballyExponentiallyStable f e :=
  ⟨c.equilibrium, c.forwardComplete hf, max 1 (Real.sqrt (c.upper / c.lower)), c.rate / 2,
    le_max_left _ _, half_pos c.rate_pos, fun _ _ _ hφ _ ht => (c.norm_bound hφ ht).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.exp_nonneg _)) (norm_nonneg _))⟩

/-- The certificate proves every attractive sentence. -/
@[powerlib_foundation] theorem holds {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) (hf : ContDiff ℝ 1 f)
    {P : Property} (hP : P.Attractive) : P.holds f e :=
  (c.globallyExponentiallyStable hf).holds hP

/-- The certificate proves decay at half its energy rate. -/
@[powerlib_foundation] theorem decay {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {e : ℝⁿ}
    (c : QuadraticDecay f V e) : Decay f e (c.rate / 2) :=
  ⟨_, fun _ _ _ hφ _ ht => c.norm_bound hφ ht⟩

end QuadraticDecay

/-! ## Strict Lyapunov functions -/

/-- A strict Lyapunov function with compact sublevels proves global asymptotic stability of a
C¹ field, including a solution through every state. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_of_strictLyapunov {f : ℝⁿ → ℝⁿ}
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

end powerlib.Flow
