import theorem.Dynamics.Calculus
import theorem.Dynamics.Locality
import theorem.Dynamics.Lyapunov

/-! # Instability criteria (foundation)

Chetaev-type instability criteria and obstructions to local asymptotic stability. Where the
Jacobian is not Hurwitz the linearization does not decide local asymptotic or Lyapunov stability;
these are the tools for the degenerate members of model families.

Scope.
* Autonomous continuous-time ODE `ẋ = f x` on `Dynamics.State n = EuclideanSpace ℝ (Fin n)`
  (`ℝⁿ = EuclideanSpace ℝ (Fin n)`, the library's segment semantics); no input, delay, switching
  or time variation. `V̇ x = fderiv ℝ V x (f x)`.
* Every statement is a generic implication about an arbitrary field and function, a foundation
  result.

Source: Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.3 (Chetaev) and Theorem 4.1, stated for
`C¹` fields on a domain; Hahn, *Stability of Motion*, Chetaev's method (exponential form, from
LeanForControl); needed by work-sync `theory/T-vsc-dc-voltage-control.md` §1.4.

Results.
* Classical forms for `C¹` fields: `unstable_of_chetaev` (Chetaev's instability theorem in its
  classical, non-exponential form, for degenerate points where LeanForControl's exponential
  criterion does not apply); `unstable_of_lie_nonpos_of_lie_pos` (its variant on the sublevel set
  of a dissipated energy below the level of the point: fold points of dissipative mechanical
  systems); `not_localAsymptoticStable_of_lie_nonpos` (a function that does not increase along the
  field near the point and takes values below its value at the point arbitrarily close to it rules
  out local asymptotic stability: conserved energies, fold points with a monotone coordinate);
  `not_localAsymptoticStable_of_equilibria` (accumulating equilibria rule it out).
* `unstable_of_exponential_chetaev`: LeanForControl's exponential Chetaev criterion
  (`NonlinearInstability.unstable_of_exponential_chetaev`: `2 α V ≤ V̇` near the base point, with
  `|V| ≤ C ‖x − x_eq‖²` and positive values of `V` accumulating at the base point).
* Fields that are `C¹` only on an open set `U` containing the point (typically power-balance fields
  with a `1/V_dc` factor, smooth on `V_dc > 0` only):
  `not_localAsymptoticStable_of_lie_nonpos_local`, `unstable_of_chetaev_local`,
  `unstable_of_lie_nonpos_of_lie_pos_local`. The field is replaced near the point by a globally
  `C¹` field (`exists_contDiff_ball`, a smooth bump) and the conclusions are transported back with
  the locality lemmas of `theorem/Dynamics/Locality.lean`.
* Hypotheses on a punctured neighbourhood (`∀ᶠ x in 𝓝[≠] x_eq`), as delivered by normal-form
  computations at a Hopf point or a saddle-node: `unstable_of_eventually_chetaev`,
  `not_localAsymptoticStable_of_eventually_lie_nonpos`, `unstable_of_eventually_lie_neg` (`Ė < 0`
  on a punctured neighbourhood of an equilibrium and `E < E(x*)` arbitrarily close to it: the
  saddle-node criterion).
* `not_globallyAsymptoticallyStable_of_equilibrium_ne`: a field with an equilibrium `y ≠ x` has
  no globally asymptotically stable point `x` (the constant solution at `y` does not converge to
  `x`); with `2π`-periodic fields this rules out global attraction of any selected point.

The Lyapunov (stability) counterparts are in `theorem/Dynamics/Lyapunov.lean`.
-/

noncomputable section
namespace powerlib.Dynamics

/-! ## Classical Chetaev criteria and obstructions to attraction -/

section Classical

open Set Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A function that does not increase along the field near a point, and takes values below its
value at the point arbitrarily close to it, rules out local asymptotic stability of a `C¹`
field: a solution through such a state keeps the function below its value at the point. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_lie_nonpos {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {V : ℝⁿ → ℝ} {ρ : ℝ} (hf : ContDiff ℝ 1 f) (hV : Differentiable ℝ V)
    (hρ : 0 < ρ) (hLie : ∀ x, ‖x - x_eq‖ < ρ → fderiv ℝ V x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ V x < V x_eq) :
    ¬ LocalAsymptoticStable f x_eq := by
  rintro ⟨hLS, c, hc, hconv⟩
  obtain ⟨δ₁, hδ₁, hex⟩ := exists_forward_of_lyapunovStable hf hLS
  obtain ⟨δ₂, hδ₂, hb⟩ := hLS ρ hρ
  obtain ⟨x, hx, hVx⟩ := hseed (min c (min δ₁ δ₂)) (lt_min hc (lt_min hδ₁ hδ₂))
  obtain ⟨φ, hφ0, hφ, -⟩ := hex x (hx.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hlim : Tendsto φ atTop (𝓝 x_eq) :=
    hconv 0 φ hφ (by rw [hφ0]; exact hx.trans_le (min_le_left _ _))
  have hmono : ∀ t, 0 ≤ t → V (φ t) ≤ V x := by
    intro t ht
    have hseg : IsTrajectoryOn φ f 0 t := hφ.mono Icc_subset_Ici_self
    have hin : ∀ s ∈ Icc 0 t, ‖φ s - x_eq‖ < ρ := fun s hs =>
      hb 0 t φ hseg (by rw [hφ0]; exact hx.trans_le ((min_le_right _ _).trans
        (min_le_right _ _))) s hs
    have hanti := antitoneOn_V_comp_traj hV hV.continuous (convex_Icc 0 t) hseg
      (fun s hs => hLie _ (hin s (interior_subset hs)))
    have := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    simpa [hφ0] using this
  have hlimV : Tendsto (fun t => V (φ t)) atTop (𝓝 (V x_eq)) :=
    (hV.continuous.tendsto x_eq).comp hlim
  have : V x_eq ≤ V x := le_of_tendsto hlimV (eventually_atTop.mpr ⟨0, hmono⟩)
  linarith

/-- Equilibria accumulating at a point rule out its local asymptotic stability: the constant
solution at a nearby equilibrium does not converge to the point. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_equilibria {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} (h : ∀ ε > 0, ∃ x, x ≠ x_eq ∧ ‖x - x_eq‖ < ε ∧ f x = 0) :
    ¬ LocalAsymptoticStable f x_eq := by
  rintro ⟨-, c, hc, hconv⟩
  obtain ⟨x, hne, hx, hfx⟩ := h c hc
  have hcurve : IsIntegralCurveOn (fun _ : ℝ => x) (fun _ y => f y) (Ici 0) := fun t _ => by
    simp only [hfx]
    exact hasDerivWithinAt_const _ _ _
  exact hne (tendsto_nhds_unique tendsto_const_nhds (hconv 0 _ hcurve hx))

/-- **Chetaev's instability theorem** (classical form). A `C¹` function `W` that is positive at
states arbitrarily close to the point and strictly increases along the field wherever it is
positive within distance `r` makes the point of a `C¹` field unstable. -/
@[powerlib_foundation] theorem unstable_of_chetaev {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {W : ℝⁿ → ℝ}
    {r : ℝ} (hf : ContDiff ℝ 1 f) (hW : ContDiff ℝ 1 W) (hr : 0 < r)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ 0 < W x)
    (hLie : ∀ x, ‖x - x_eq‖ ≤ r → 0 < W x → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  intro hLS
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hLc : Continuous fun x => fderiv ℝ W x (f x) :=
    (hW.continuous_fderiv one_ne_zero).clm_apply hf.continuous
  obtain ⟨δ₁, hδ₁, hex⟩ := exists_forward_of_lyapunovStable hf hLS
  obtain ⟨δ₂, hδ₂, hb⟩ := hLS r hr
  obtain ⟨x₀, hx₀, hW₀⟩ := hseed (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  obtain ⟨φ, hφ0, hφ, -⟩ := hex x₀ (hx₀.trans_le (min_le_left _ _))
  have hin : ∀ t, 0 ≤ t → ‖φ t - x_eq‖ < r := fun t ht =>
    hb 0 t φ (hφ.mono Icc_subset_Ici_self) (by rw [hφ0]; exact hx₀.trans_le (min_le_right _ _))
      t ⟨ht, le_rfl⟩
  -- the solution keeps `W ≥ W x₀`
  have hkeep : ∀ T, 0 ≤ T → ∀ t ∈ Icc 0 T, W x₀ ≤ W (φ t) := by
    intro T hT
    have hc : ContinuousOn φ (Icc 0 T) := hφ.continuousOn.mono Icc_subset_Ici_self
    refine forall_mem_Icc_of_local_step (Ω := {x | W x₀ ≤ W x}) hc
      (isClosed_le continuous_const hW.continuous) (by simp [hφ0]) ?_
    intro s hs hsΩ
    have hpos : 0 < fderiv ℝ W (φ s) (f (φ s)) :=
      hLie _ (hin s hs.1).le (hW₀.trans_le hsΩ)
    obtain ⟨y, hsy, hyT, hy⟩ := exists_Icc_mem_of_isOpen hc
      (isOpen_lt continuous_const hLc) hs hpos
    have hseg : IsIntegralCurveOn φ (fun _ x => f x) (Icc s y) :=
      hφ.mono fun t ht => le_trans hs.1 ht.1
    have hanti := antitoneOn_V_comp_traj (V := fun x => -W x) hWd.neg hWd.continuous.neg
      (convex_Icc s y) hseg fun t ht => by
        have := hy t (interior_subset ht)
        show fderiv ℝ (fun x => -W x) (φ t) (f (φ t)) ≤ 0
        rw [fderiv_fun_neg]
        simpa using this.le
    refine ⟨y, hsy, fun t ht => ?_⟩
    have := hanti ⟨le_rfl, hsy.le⟩ (Ioo_subset_Icc_self ht) ht.1.le
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact (show W x₀ ≤ W (φ s) from hsΩ).trans this
  -- a uniform rate on the compact set `{‖x − x_eq‖ ≤ r, W x ≥ W x₀}`
  set K := {x | ‖x - x_eq‖ ≤ r ∧ W x₀ ≤ W x} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x_eq r).of_isClosed_subset ?_ fun x hx => ?_
    · exact (isClosed_le (continuous_norm.comp (continuous_sub_right x_eq)) continuous_const).inter
        (isClosed_le continuous_const hW.continuous)
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.1
  have hx₀K : x₀ ∈ K := ⟨by simpa [hφ0] using (hin 0 le_rfl).le, le_rfl⟩
  have hφK : ∀ t, 0 ≤ t → φ t ∈ K := fun t ht =>
    ⟨(hin t ht).le, hkeep t ht t ⟨ht, le_rfl⟩⟩
  obtain ⟨xm, hxmK, hmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀K⟩ hLc.continuousOn
  obtain ⟨xM, -, hmax⟩ := hKc.exists_isMaxOn ⟨x₀, hx₀K⟩ hW.continuous.continuousOn
  have hγ : 0 < fderiv ℝ W xm (f xm) := hLie xm hxmK.1 (hW₀.trans_le hxmK.2)
  set γ := fderiv ℝ W xm (f xm)
  set T := (W xM - W x₀) / γ + 1 with hT
  have hT0 : 0 ≤ T := by
    have hle : W x₀ ≤ W xM := hmax hx₀K
    have : 0 ≤ (W xM - W x₀) / γ := div_nonneg (by linarith) hγ.le
    linarith
  have hanti := antitoneOn_V_add_linear (V := fun x => -W x) (c := γ) hWd.neg
    hWd.continuous.neg (convex_Icc 0 T) (hφ.mono Icc_subset_Ici_self) fun t ht => by
      have hmt : γ ≤ fderiv ℝ W (φ t) (f (φ t)) := hmin (hφK t (interior_subset ht).1)
      show fderiv ℝ (fun x => -W x) (φ t) (f (φ t)) ≤ -γ
      rw [fderiv_fun_neg]
      simpa using hmt
  have h1 := hanti ⟨le_rfl, hT0⟩ ⟨hT0, le_rfl⟩ hT0
  simp only [hφ0, mul_zero, add_zero] at h1
  have h2 : W (φ T) ≤ W xM := hmax (hφK T hT0)
  have h3 : γ * T = W xM - W x₀ + γ := by rw [hT]; field_simp
  linarith

/-- **Chetaev's theorem on a dissipated level set.** A `C¹` energy `E` that does not increase
along the field near the point and takes values below `E x*` arbitrarily close to it, together with
a `C¹` function `W` that strictly increases along the field wherever `E < E x*` near the point,
makes the point of a `C¹` field unstable: a solution started below the level of `x*` stays there,
and `W` grows at a uniform rate on the compact part of that sublevel near `x*`. -/
@[powerlib_foundation] theorem unstable_of_lie_nonpos_of_lie_pos {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {E W : ℝⁿ → ℝ} {r : ℝ} (hf : ContDiff ℝ 1 f) (hE : ContDiff ℝ 1 E) (hW : ContDiff ℝ 1 W)
    (hr : 0 < r) (hELie : ∀ x, ‖x - x_eq‖ ≤ r → fderiv ℝ E x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ E x < E x_eq)
    (hWLie : ∀ x, ‖x - x_eq‖ ≤ r → E x < E x_eq → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  intro hLS
  have hEd : Differentiable ℝ E := hE.differentiable one_ne_zero
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hLc : Continuous fun x => fderiv ℝ W x (f x) :=
    (hW.continuous_fderiv one_ne_zero).clm_apply hf.continuous
  obtain ⟨δ₁, hδ₁, hex⟩ := exists_forward_of_lyapunovStable hf hLS
  obtain ⟨δ₂, hδ₂, hb⟩ := hLS r hr
  obtain ⟨x₀, hx₀, hE₀⟩ := hseed (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  obtain ⟨φ, hφ0, hφ, -⟩ := hex x₀ (hx₀.trans_le (min_le_left _ _))
  have hin : ∀ t, 0 ≤ t → ‖φ t - x_eq‖ < r := fun t ht =>
    hb 0 t φ (hφ.mono Icc_subset_Ici_self) (by rw [hφ0]; exact hx₀.trans_le (min_le_right _ _))
      t ⟨ht, le_rfl⟩
  have hlev : ∀ t, 0 ≤ t → E (φ t) ≤ E x₀ := by
    intro t ht
    have hanti := antitoneOn_V_comp_traj hEd hEd.continuous (convex_Icc 0 t)
      (hφ.mono Icc_subset_Ici_self) fun s hs => hELie _ (hin s (interior_subset hs).1).le
    have := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    simpa [hφ0] using this
  set K := {x | ‖x - x_eq‖ ≤ r ∧ E x ≤ E x₀} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x_eq r).of_isClosed_subset ?_ fun x hx => ?_
    · exact (isClosed_le (continuous_norm.comp (continuous_sub_right x_eq)) continuous_const).inter
        (isClosed_le hE.continuous continuous_const)
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.1
  have hφK : ∀ t, 0 ≤ t → φ t ∈ K := fun t ht => ⟨(hin t ht).le, hlev t ht⟩
  have hx₀K : x₀ ∈ K := by simpa [hφ0] using hφK 0 le_rfl
  obtain ⟨xm, hxmK, hmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀K⟩ hLc.continuousOn
  obtain ⟨xM, -, hmax⟩ := hKc.exists_isMaxOn ⟨x₀, hx₀K⟩ hW.continuous.continuousOn
  have hγ : 0 < fderiv ℝ W xm (f xm) := hWLie xm hxmK.1 (hxmK.2.trans_lt hE₀)
  set γ := fderiv ℝ W xm (f xm)
  set T := (W xM - W x₀) / γ + 1 with hT
  have hT0 : 0 ≤ T := by
    have hle : W x₀ ≤ W xM := hmax hx₀K
    have : 0 ≤ (W xM - W x₀) / γ := div_nonneg (by linarith) hγ.le
    linarith
  have hanti := antitoneOn_V_add_linear (V := fun x => -W x) (c := γ) hWd.neg
    hWd.continuous.neg (convex_Icc 0 T) (hφ.mono Icc_subset_Ici_self) fun t ht => by
      have hmt : γ ≤ fderiv ℝ W (φ t) (f (φ t)) := hmin (hφK t (interior_subset ht).1)
      show fderiv ℝ (fun x => -W x) (φ t) (f (φ t)) ≤ -γ
      rw [fderiv_fun_neg]
      simpa using hmt
  have h1 := hanti ⟨le_rfl, hT0⟩ ⟨hT0, le_rfl⟩ hT0
  simp only [hφ0, mul_zero, add_zero] at h1
  have h2 : W (φ T) ≤ W xM := hmax (hφK T hT0)
  have h3 : γ * T = W xM - W x₀ + γ := by rw [hT]; field_simp
  linarith

end Classical

section Exponential

open Set Filter Topology

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- Exponential Chetaev instability criterion.
Upstream: `NonlinearInstability.unstable_of_exponential_chetaev`. -/
@[powerlib_foundation] theorem unstable_of_exponential_chetaev
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    {ρ α C : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖x - x_eq‖ ≤ ρ → |V x| ≤ C * ‖x - x_eq‖ ^ 2)
    (hgrowth : ∀ x, ‖x - x_eq‖ ≤ ρ → 2 * α * V x ≤ fderiv ℝ V x (f x))
    (hseed : ∀ δ > 0, ∃ x, ‖x - x_eq‖ < min δ ρ ∧ 0 < V x) :
    Unstable f x_eq :=
  NonlinearInstability.unstable_of_exponential_chetaev hf hV hρ hα hC hbound hgrowth hseed

end Exponential

/-! ## Fields that are `C¹` only near the point -/

section Local

open Set Filter Topology Metric

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A function that does not increase along a locally `C¹` field near a point, and takes values
below its value at the point arbitrarily close to it, rules out local asymptotic stability. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_lie_nonpos_local {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {U : Set ℝⁿ} {V : ℝⁿ → ℝ} {ρ : ℝ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hV : Differentiable ℝ V) (hρ : 0 < ρ)
    (hLie : ∀ x ∈ U, ‖x - x_eq‖ < ρ → fderiv ℝ V x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ V x < V x_eq) :
    ¬ LocalAsymptoticStable f x_eq := by
  obtain ⟨g, hg, hgf, σ, hσ, hball⟩ := exists_contDiff_ball hU hx hf
  intro h
  refine not_localAsymptoticStable_of_lie_nonpos (ρ := min ρ σ) hg hV (lt_min hρ hσ)
    (fun y hy => ?_) hseed (localAsymptoticStable_congr_nhds hgf h)
  obtain ⟨hgy, hyU⟩ := hball y (hy.trans_le (min_le_right _ _))
  rw [hgy]
  exact hLie y hyU (hy.trans_le (min_le_left _ _))

/-- **Chetaev's instability theorem** for a field that is `C¹` on an open neighbourhood `U` of the
point: a `C¹` function positive at states arbitrarily close to the point and strictly increasing
along the field wherever it is positive, within `U` and distance `r`. -/
@[powerlib_foundation] theorem unstable_of_chetaev_local {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {U : Set ℝⁿ} {W : ℝⁿ → ℝ} {r : ℝ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hW : ContDiff ℝ 1 W) (hr : 0 < r)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ 0 < W x)
    (hLie : ∀ x ∈ U, ‖x - x_eq‖ ≤ r → 0 < W x → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  obtain ⟨g, hg, hgf, σ, hσ, hball⟩ := exists_contDiff_ball hU hx hf
  rw [unstable_congr_nhds hgf.symm]
  refine unstable_of_chetaev (r := min r (σ / 2)) hg hW (lt_min hr (by positivity)) hseed
    (fun y hy hWy => ?_)
  obtain ⟨hgy, hyU⟩ := hball y (hy.trans_lt ((min_le_right _ _).trans_lt (by linarith)))
  rw [hgy]
  exact hLie y hyU (hy.trans (min_le_left _ _)) hWy

/-- **Chetaev's theorem on a non-increasing level set**, for a field that is `C¹` on an open
neighbourhood `U` of the point: an energy `E` that does not increase along the field near the
point and takes values below `E x*` arbitrarily close to it, and a function `W` that strictly
increases wherever `E < E x*` near the point. -/
@[powerlib_foundation] theorem unstable_of_lie_nonpos_of_lie_pos_local {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {U : Set ℝⁿ} {E W : ℝⁿ → ℝ} {r : ℝ} (hU : IsOpen U) (hx : x_eq ∈ U)
    (hf : ContDiffOn ℝ 1 f U) (hE : ContDiff ℝ 1 E) (hW : ContDiff ℝ 1 W) (hr : 0 < r)
    (hELie : ∀ x ∈ U, ‖x - x_eq‖ ≤ r → fderiv ℝ E x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ E x < E x_eq)
    (hWLie : ∀ x ∈ U, ‖x - x_eq‖ ≤ r → E x < E x_eq → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  obtain ⟨g, hg, hgf, σ, hσ, hball⟩ := exists_contDiff_ball hU hx hf
  rw [unstable_congr_nhds hgf.symm]
  have hmem : ∀ y, ‖y - x_eq‖ ≤ min r (σ / 2) → g y = f y ∧ y ∈ U := fun y hy =>
    hball y (hy.trans_lt ((min_le_right _ _).trans_lt (by linarith)))
  refine unstable_of_lie_nonpos_of_lie_pos (r := min r (σ / 2)) hg hE hW
    (lt_min hr (by positivity)) (fun y hy => ?_) hseed (fun y hy hEy => ?_)
  · obtain ⟨hgy, hyU⟩ := hmem y hy
    rw [hgy]
    exact hELie y hyU (hy.trans (min_le_left _ _))
  · obtain ⟨hgy, hyU⟩ := hmem y hy
    rw [hgy]
    exact hWLie y hyU (hy.trans (min_le_left _ _)) hEy

end Local

/-! ## Criteria on a punctured neighbourhood -/

section Eventually

open Set Filter Topology Metric Asymptotics

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- States arbitrarily close to a point of a nontrivial Euclidean space with an eventual
punctured-neighbourhood property. -/
private theorem exists_near_of_eventually (hn : 0 < n) {x_eq : ℝⁿ} {P : ℝⁿ → Prop}
    (h : ∀ᶠ x in 𝓝[≠] x_eq, P x) (ε : ℝ) (hε : 0 < ε) :
    ∃ x, ‖x - x_eq‖ < ε ∧ x ≠ x_eq ∧ P x := by
  obtain ⟨r, hr, hP⟩ := exists_radius_of_eventually h
  set e : ℝⁿ := EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1 with he
  have hen : ‖e‖ = 1 := by rw [he, EuclideanSpace.single, PiLp.norm_single, norm_one]
  set t := min ε r / 2 with ht
  have htpos : 0 < t := by positivity
  have hnorm : ‖(x_eq + t • e) - x_eq‖ = t := by
    rw [add_sub_cancel_left, norm_smul, hen, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
  have htε : t < ε := by
    have := min_le_left ε r
    linarith
  have htr : t < r := by
    have := min_le_right ε r
    linarith
  have hne : x_eq + t • e ≠ x_eq := fun h => by
    rw [h, sub_self, norm_zero] at hnorm
    linarith
  exact ⟨x_eq + t • e, by rw [hnorm]; exact htε, hne, hP _ (by rw [hnorm]; exact htr) hne⟩

/-- **Chetaev on a punctured neighbourhood.** A `C¹` function vanishing at the point, positive
with positive derivative along a `C¹` field on a punctured neighbourhood, makes the point
unstable. -/
@[powerlib_foundation] theorem unstable_of_eventually_chetaev (hn : 0 < n) {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {W : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (hW : ContDiff ℝ 1 W) (hW0 : W x_eq = 0)
    (hpos : ∀ᶠ x in 𝓝[≠] x_eq, 0 < W x) (hLie : ∀ᶠ x in 𝓝[≠] x_eq, 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  obtain ⟨r, hr, hball⟩ := exists_radius_of_eventually hLie
  refine unstable_of_chetaev hf hW (half_pos hr) (fun ε hε => ?_) (fun x hx hWx => ?_)
  · obtain ⟨x, hx, -, hWx⟩ := exists_near_of_eventually hn hpos ε hε
    exact ⟨x, hx, hWx⟩
  · have hne : x ≠ x_eq := fun h => by rw [h, hW0] at hWx; exact lt_irrefl 0 hWx
    exact hball x (by linarith) hne

/-- **No attraction from a non-increasing function with lower values nearby** (eventual form). -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_eventually_lie_nonpos
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {V : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (hV : Differentiable ℝ V)
    (hLie : ∀ᶠ x in 𝓝 x_eq, fderiv ℝ V x (f x) ≤ 0) (hseed : ∃ᶠ x in 𝓝 x_eq, V x < V x_eq) :
    ¬ LocalAsymptoticStable f x_eq := by
  rw [Metric.eventually_nhds_iff] at hLie
  obtain ⟨ρ, hρ, hLieρ⟩ := hLie
  refine not_localAsymptoticStable_of_lie_nonpos hf hV hρ
    (fun x hx => hLieρ (by rwa [dist_eq_norm])) fun ε hε => ?_
  obtain ⟨x, hx, hVx⟩ := (hseed.and_eventually (Metric.ball_mem_nhds x_eq hε)).exists
  exact ⟨x, by rw [← dist_eq_norm]; exact hVx, hx⟩

/-- **Instability from a strictly decreasing function with lower values nearby.** If a `C¹`
function decreases strictly along a `C¹` field on a punctured neighbourhood of an equilibrium and
takes values below its value at the equilibrium at states arbitrarily close to it, the equilibrium
is unstable (`Dynamics.unstable_of_lie_nonpos_of_lie_pos` with `W = −E`). -/
@[powerlib_foundation] theorem unstable_of_eventually_lie_neg {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {E : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (hfx : f x_eq = 0) (hE : ContDiff ℝ 1 E)
    (hLie : ∀ᶠ x in 𝓝[≠] x_eq, fderiv ℝ E x (f x) < 0) (hseed : ∃ᶠ x in 𝓝 x_eq, E x < E x_eq) :
    Unstable f x_eq := by
  obtain ⟨r, hr, hball⟩ := exists_radius_of_eventually hLie
  have hLie0 : fderiv ℝ E x_eq (f x_eq) = 0 := by rw [hfx, map_zero]
  refine unstable_of_lie_nonpos_of_lie_pos (W := fun x => -E x) hf hE hE.neg (half_pos hr)
    (fun x hx => ?_) (fun ε hε => ?_) (fun x hx hEx => ?_)
  · by_cases hne : x = x_eq
    · rw [hne, hLie0]
    · exact (hball x (by linarith) hne).le
  · obtain ⟨x, hx, hEx⟩ := (hseed.and_eventually (Metric.ball_mem_nhds x_eq hε)).exists
    exact ⟨x, by rw [← dist_eq_norm]; exact hEx, hx⟩
  · have hne : x ≠ x_eq := fun h => by rw [h] at hEx; exact lt_irrefl _ hEx
    rw [fderiv_fun_neg]
    simp only [neg_apply, neg_pos]
    exact hball x (by linarith) hne

end Eventually

/-! ## Obstructions to global attraction -/

section Global

open Filter Topology

/-- A field with an equilibrium `y ≠ x` has no globally asymptotically stable point `x`: the
constant solution at `y` does not converge to `x`. Generic. -/
@[powerlib_foundation] theorem not_globallyAsymptoticallyStable_of_equilibrium_ne {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {x y : EuclideanSpace ℝ (Fin n)}
    (hy : f y = 0) (hne : y ≠ x) : ¬ Flow.GloballyAsymptoticallyStable f x := by
  rintro ⟨-, -, -, hconv⟩
  have hc : IsIntegralCurveOn (fun _ : ℝ => y) (fun _ z => f z) (Set.Ici 0) := by
    intro t _
    show HasDerivWithinAt (fun _ => y) (f y) (Set.Ici 0) t
    rw [hy]
    exact hasDerivWithinAt_const t (Set.Ici 0) y
  exact hne (tendsto_nhds_unique tendsto_const_nhds (hconv 0 _ hc))

end Global

end powerlib.Dynamics
