import theorem.Periodic.OrbitalInstability

/-! # A uniform escape radius for unstable periodic solutions

`Periodic.unstable_of_floquet` shows that a solution `x_*` of `ẋ = G(t, x)` whose linearization
`J(t)` (continuous, `T`-periodic) has a Floquet multiplier `|μ| > 1` is unstable from every
initial time `s`, with an escape radius `ε(s)` that may depend on `s` (its Stein certificate is
built from the monodromy matrix `Φ(s + T, s)`). When the whole problem is periodic — `G(·, x)`
and `x_*` are `T`-periodic, as for the linearization along a periodic orbit of a periodically
forced system — one radius serves every initial time: the instability is uniform, the escape
does not shrink for late or badly phased initial times.

The proof derives the uniform statement from `unstable_of_floquet` at the single initial time
`0`; no certificate is redone. Periodicity transports the escaping solutions from time `0` to the
times `kT`, and an initial time `s ∈ [kT, kT + T)` is reached by restricting a transported
solution: started very close to `x_*`, it stays in the tube for longer than one period
(first-exit time and Grönwall's estimate `dist_le_of_trajectories_ODE_of_mem` with the Lipschitz
constant `K` of `G` on the tube), so at time `s` it is still within `δ` of `x_*(s)`.

Scope.
* The hypotheses of `Periodic.unstable_of_floquet` (finite state space `ℝ^X` with the sup norm;
  `G` continuous and `K`-Lipschitz in the state on the tube `‖x − x_*(t)‖ ≤ ρ`, quadratic
  remainder `L‖e‖²` of the linearization `J`, `J` continuous `T`-periodic with
  `Periodic.FloquetUnstable J T`, `x_*` a differentiable solution), plus
  `Function.Periodic G T` and `Function.Periodic x_* T`.
* Solutions are Mathlib integral curves on segments `[s, t]`, as in `unstable_of_floquet`.
* Generic mathematics; no model family.

Source: uniformity in the initial time for periodic systems (W. Hahn, *Stability of Motion*,
1967: for periodic right-hand sides the stability notions are uniform in the initial time);
the instability theorem `Periodic.unstable_of_floquet` of
`theorem/Periodic/OrbitalInstability.lean`, applied once and transported by periodicity.

Results.
* `unstable_of_floquet_uniform` — with `G` and `x_*` `T`-periodic: `∃ ε > 0, ∀ s, ∀ δ > 0`, a
  solution on some `[s, t]` starts within `δ` of `x_*(s)` and reaches the distance `ε`
  (`ε = min(ε₀, ρ)`, `ε₀` the radius of `unstable_of_floquet` at time `0`).
-/

noncomputable section
namespace powerlib.Periodic
open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The escape radius does not depend on the initial time** when the whole problem is
periodic. In the setting of `unstable_of_floquet`, assume in addition that the field and the
solution are `T`-periodic in time, `G(t + T, ·) = G(t, ·)` and `x_*(t + T) = x_*(t)`. Then one
`ε > 0` serves every initial time: for every `s` and every `δ > 0` a solution `x` of
`ẋ = G(t, x)` on some `[s, t]` has `‖x(s) − x_*(s)‖ < δ` and `‖x(t) − x_*(t)‖ ≥ ε`.

The radius is `ε = min(ε₀, ρ)` with `ε₀` the radius of `unstable_of_floquet` at the initial time
`0`. For an initial time `s`, let `τ = ⌊s/T⌋ T ≤ s < τ + T`. An escaping solution from time `0`
started within `δ' = min(δ, ε) e^{−KT}/2` of `x_*(0)` stays in the tube until its first exit
time `t₁` from the ball of radius `ε`, so there Grönwall's estimate (Lipschitz constant `K`)
gives `‖y(u) − x_*(u)‖ ≤ δ' e^{Ku}`; hence `t₁ > T`. Shifted by `τ` (periodicity) and restricted
to `[s, τ + t₁]` it starts within `δ' e^{KT} < δ` of `x_*(s)` and reaches the distance `ε`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_floquet_uniform {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} {J : ℝ → Matrix X X ℝ} {T : ℝ} (hT : 0 < T) (hJc : Continuous J)
    (hJp : Periodic J T) (hun : FloquetUnstable J T)
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {ρ L : ℝ} {K : NNReal} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hGc : ContinuousOn (fun p : ℝ × (X → ℝ) => G p.1 p.2) {p | ‖p.2 - xs p.1‖ ≤ ρ})
    (hGl : ∀ t, LipschitzOnWith K (G t) (Metric.closedBall (xs t) ρ))
    (hR : ∀ t e, ‖e‖ ≤ ρ → ‖G t (xs t + e) - G t (xs t) - J t *ᵥ e‖ ≤ L * ‖e‖ ^ 2)
    (hGp : Periodic G T) (hxsp : Periodic xs T) :
    ∃ ε, 0 < ε ∧ ∀ s δ, 0 < δ → ∃ (x : ℝ → X → ℝ) (t : ℝ), s ≤ t ∧
      IsIntegralCurveOn x G (Icc s t) ∧ ‖x s - xs s‖ < δ ∧ ε ≤ ‖x t - xs t‖ := by
  obtain ⟨ε₀, hε₀, hesc⟩ :=
    unstable_of_floquet hT hJc hJp hun hxs hρ hL hGc hGl hR 0
  set ε := min ε₀ ρ with hεdef
  have hε : 0 < ε := lt_min hε₀ hρ
  have hερ : ε ≤ ρ := min_le_right _ _
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  refine ⟨ε, hε, fun s δ hδ => ?_⟩
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  -- the period window containing `s`
  set k : ℤ := ⌊s / T⌋ with hk
  set τ : ℝ := k * T with hτ
  have hτs : τ ≤ s := by
    have := Int.floor_le (s / T)
    calc τ = (k : ℝ) * T := rfl
      _ ≤ s / T * T := mul_le_mul_of_nonneg_right this hT.le
      _ = s := by field_simp
  have hsτ : s < τ + T := by
    have := Int.lt_floor_add_one (s / T)
    calc s = s / T * T := by field_simp
      _ < ((k : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
      _ = τ + T := by rw [hτ]; ring
  -- an escaping solution from time `0`, started very close
  set C := Real.exp (K * T) with hC
  have hC0 : 0 < C := Real.exp_pos _
  set δ' := min δ ε / C / 2 with hδ'
  have hmin : 0 < min δ ε := lt_min hδ hε
  have hδ'0 : 0 < δ' := by positivity
  have hδ'C : δ' * C = min δ ε / 2 := by rw [hδ']; field_simp
  obtain ⟨y, t₀, ht₀, hy, hy0, hyt₀⟩ := hesc δ' hδ'0
  have hyc : ContinuousOn y (Icc 0 t₀) := hy.continuousOn
  -- the first exit time from the ball of radius `ε`
  set Z := Icc 0 t₀ ∩ (fun u => ‖y u - xs u‖) ⁻¹' Ici ε with hZ
  have hZc : IsClosed Z :=
    ((hyc.sub hxsc.continuousOn).norm).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hZne : Z.Nonempty := ⟨t₀, ⟨⟨ht₀, le_rfl⟩, hεε₀.trans hyt₀⟩⟩
  have hZb : BddBelow Z := ⟨0, fun u hu => hu.1.1⟩
  set t₁ := sInf Z with ht₁
  have ht₁Z : t₁ ∈ Z := hZc.csInf_mem hZne hZb
  have ht₁0 : 0 ≤ t₁ := ht₁Z.1.1
  have ht₁t₀ : t₁ ≤ t₀ := ht₁Z.1.2
  have hbefore : ∀ u ∈ Ico 0 t₁, ‖y u - xs u‖ < ε := by
    intro u hu
    by_contra hcon
    push Not at hcon
    have : t₁ ≤ u := csInf_le hZb ⟨⟨hu.1, hu.2.le.trans ht₁t₀⟩, hcon⟩
    linarith [hu.2]
  -- Grönwall up to the exit time
  have hgr : ∀ u ∈ Icc 0 t₁, ‖y u - xs u‖ ≤ δ' * Real.exp (K * u) := by
    have h := dist_le_of_trajectories_ODE_of_mem (v := G) (s := fun u => Metric.closedBall (xs u) ρ)
      (K := K) (f := y) (g := xs) (a := 0) (b := t₁) (δ := δ') (fun u _ => hGl u)
      (hyc.mono (Icc_subset_Icc_right ht₁t₀))
      (fun u hu => (hy u ⟨hu.1, hu.2.le.trans ht₁t₀⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE (hu.2.trans_le ht₁t₀))
          (Icc_subset_Icc_left hu.1)))
      (fun u hu => by
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact (hbefore u hu).le.trans hερ)
      hxsc.continuousOn (fun u _ => (hxs u).hasDerivWithinAt)
      (fun u _ => Metric.mem_closedBall_self hρ.le) (by rw [dist_eq_norm]; exact hy0.le)
    intro u hu
    have := h u hu
    rwa [dist_eq_norm, sub_zero] at this
  -- the exit happens after one period
  have hTt₁ : T < t₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := hgr t₁ ⟨ht₁0, le_rfl⟩
    have h2 : Real.exp (K * t₁) ≤ C := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcon K.2)
    have h3 : ε ≤ δ' * C := ht₁Z.2.trans (h1.trans (mul_le_mul_of_nonneg_left h2 hδ'0.le))
    rw [hδ'C] at h3
    linarith [min_le_right δ ε]
  -- shift by `τ` and restrict to `[s, τ + t₁]`
  have hGτ : ∀ u, G (u - τ) = G u := fun u => hGp.sub_int_mul_eq k
  have hxsτ : ∀ u, xs (u - τ) = xs u := fun u => hxsp.sub_int_mul_eq k
  refine ⟨fun u => y (u - τ), τ + t₁, by linarith, fun u hu => ?_, ?_, ?_⟩
  · have hmem : u - τ ∈ Icc 0 t₀ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hmaps : MapsTo (fun u => u - τ) (Icc s (τ + t₁)) (Icc 0 t₀) :=
      fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have h := (hy (u - τ) hmem).scomp u ((hasDerivAt_id u).sub_const τ).hasDerivWithinAt hmaps
    simp only [one_smul] at h
    rw [← hGτ u]
    exact h
  · show ‖y (s - τ) - xs s‖ < δ
    rw [← hxsτ s]
    have h1 := hgr (s - τ) ⟨by linarith, by linarith⟩
    have h2 : Real.exp (K * (s - τ)) ≤ C :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) K.2)
    have h3 : ‖y (s - τ) - xs (s - τ)‖ ≤ δ' * C :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hδ'0.le)
    rw [hδ'C] at h3
    linarith [min_le_left δ ε]
  · show ε ≤ ‖y (τ + t₁ - τ) - xs (τ + t₁)‖
    rw [← hxsτ (τ + t₁), add_sub_cancel_left]
    exact ht₁Z.2

end powerlib.Periodic
