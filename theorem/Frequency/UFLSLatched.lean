import theorem.Frequency.UFLS
import theorem.Frequency.SFR

/-! # Latched single-stage UFLS in closed loop with a linear frequency-response model

Source: work-sync `theory/T-ufls.md` §1.1 (single-stage shedding added to the swing equation),
with the corrected latched trip rule of `Frequency.UFLS` (`∃ τ ∈ [0, t], Δω(τ) ≤ −θ`,
`latchedTrip_iff_sInf`), and §1.4 (state after shedding).

Model boundary.
* Plant: any continuous-time linear plant `m : Linear.Plant n 1` (states in
  `EuclideanSpace ℝ (Fin n)`) whose single input is the load step (`Frequency.load`) and whose
  coordinate `i₀` is the frequency deviation `Δω` (per-unit); instances below: the two-state
  swing + governor plant and the third-order reheat SFR plant (`i₀ = 0`).
* Protection: a single latched stage. At the first instant `Δω(τ) ≤ −θ`
  (`θ = Δf_th/f₀ > 0` in per-unit) the load `shed = p P⁰` is disconnected for good: the input is
  `ΔP_L − shed · 1[min_{0≤τ≤t} Δω(τ) ≤ −θ]`. No confirmation delay, no relay or breaker delay,
  no multi-stage scheme, no RoCoF stage, no reconnection.
* Solution concept (latched trajectory): `x` is continuous on `[0, ∞)` and, at every `t ≥ 0`,
  has the right derivative `A x(t) + B (ΔP_L − shed · 1[∃ τ ∈ [0, t], x(τ)_{i₀} ≤ −θ])`
  (the input jumps at the trip instant, so two-sided derivatives do not exist there). This
  condition is written out in the statements as the hypothesis `hx` (behavioural notions are
  defined only in the semantic layer):
  `ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t → HasDerivWithinAt x (m.inputField (load (ΔPL −
  {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t`.

Results.
* `latched_representation_noTrip`, `latched_representation_trip` (foundation, any plant): every
  latched trajectory equals the unshed response (`Linear.solution`) until the first time that
  response reaches `−θ`, and the post-shedding response from that state afterwards.
* `latched_unique`, `latched_exists` (foundation, any plant): the closed loop has exactly one
  solution from every initial state (piecewise solution exists and is unique).
* `latched_tendsto_of_trip`, `latched_tendsto_of_noTrip` (foundation, any plant): with a Hurwitz
  state matrix, a trajectory that trips converges to the post-shedding equilibrium, one that
  never trips to the pre-shedding equilibrium.
* `swingGovernor_latched_trip` (private): two-state swing + governor plant from rest,
  underdamped, `ΔP_L > 0`: if the unprotected nadir is at or below `−θ`, the relay trips and
  `Δω(t) → −(ΔP_L − p P⁰)/(K_R + D)` (§1.4 post-shedding steady state).
* `sfr_latched_tendsto` (private): the third-order SFR plant with the stability condition of
  `SFR.isHurwitz_of_hp_fraction`: a trajectory that trips converges to
  `Δω = −(ΔP_L − p P⁰)/(K_R + D)`.

Family and connection conclusions. The latched closed loop is a switched system with a
state-dependent, latched input; it is outside the sentence language (no family). The
representation, existence, uniqueness and convergence statements are generic implications about
an arbitrary caller-supplied plant (formerly `@[powerlib_domain]`, now `@[powerlib_foundation]`,
Rules §3). The two instances on the swing + governor and SFR plants are trajectory-level results
about specific engineering models: private implementation evidence (Rules §3a), derived from the
generic statements, the generic closed form `LTI.trajectory_eq_osc2` and static facts of
`SwingGovernor`, `SwingNadir` and `SFR`. The stability of the two plants themselves is published
by `SwingGovernor.family` and `SFR.family`.
-/

noncomputable section
namespace powerlib.Frequency.UFLS
open Set Filter Matrix LinearSystems
open scoped Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

variable {m : Linear.Plant n 1} {i₀ : Fin n} {ΔPL shed θ : ℝ}

/-! ## Auxiliary facts -/

/-- The field of a plant under a constant input is globally Lipschitz. -/
@[powerlib_foundation] theorem inputField_lipschitzWith (m : Linear.Plant n 1) (u : Fin 1 → ℝ) :
    LipschitzWith ‖Linear.op m.A‖₊ (m.inputField u) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp only [Linear.Plant.inputField, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub,
      coe_nnnorm]
    exact (Linear.op m.A).le_opNorm _

/-- Uniqueness of right-derivative solutions of `ẋ = A x + B u` (constant `u`). -/
@[powerlib_foundation] theorem rightODE_unique (m : Linear.Plant n 1) (u : Fin 1 → ℝ)
    {f g : ℝ → ℝⁿ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (m.inputField u (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (m.inputField u (g t)) (Ici t) t) (ha : f a = g a) :
    EqOn f g (Icc a b) :=
  ODE_solution_unique (v := fun _ x => m.inputField u x)
    (fun _ => inputField_lipschitzWith m u) hf hf' hg hg' ha

/-- First crossing time of a threshold for a signal continuous on `[0, ∞)`. -/
@[powerlib_foundation] theorem exists_first_crossing {z : ℝ → ℝ} (hz : ContinuousOn z (Ici 0))
    (h : ∃ τ ≥ 0, z τ ≤ -θ) : ∃ T ≥ 0, z T ≤ -θ ∧ ∀ s ∈ Ico 0 T, -θ < z s := by
  set S := {s | 0 ≤ s ∧ z s ≤ -θ}
  have hS : S = Ici 0 ∩ z ⁻¹' Iic (-θ) := rfl
  have hcl : IsClosed S := by
    rw [hS]; exact hz.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  obtain ⟨τ, hτ, hτz⟩ := h
  have hne : S.Nonempty := ⟨τ, hτ, hτz⟩
  have hbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  obtain ⟨hT0, hTz⟩ := hcl.csInf_mem hne hbdd
  refine ⟨sInf S, hT0, hTz, fun s hs => ?_⟩
  by_contra hc
  push Not at hc
  exact absurd (csInf_le hbdd ⟨hs.1, hc⟩) (not_le.2 hs.2)

/-- With first crossing time `T`, the latched trip at `t ≥ 0` is `T ≤ t`. -/
@[powerlib_foundation] theorem latchedTrip_iff_of_first {z : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hzT : z T ≤ -θ) (hfirst : ∀ s ∈ Ico 0 T, -θ < z s) {t : ℝ} :
    (∃ τ ∈ Icc 0 t, z τ ≤ -θ) ↔ T ≤ t := by
  constructor
  · rintro ⟨τ, hτ, hτz⟩
    by_contra hc
    push Not at hc
    exact absurd hτz (not_le.2 (hfirst τ ⟨hτ.1, lt_of_le_of_lt hτ.2 hc⟩))
  · intro h
    exact ⟨T, ⟨hT, h⟩, hzT⟩

@[powerlib_foundation] theorem latched_input_of_not {x : ℝ → ℝⁿ} {t : ℝ}
    (h : ¬ ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ) :
    load (ΔPL - {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t) =
      load ΔPL := by
  rw [Set.indicator_of_notMem (show t ∉ {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ} from h),
    sub_zero]

@[powerlib_foundation] theorem latched_input_of {x : ℝ → ℝⁿ} {t : ℝ}
    (h : ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ) :
    load (ΔPL - {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t) =
      load (ΔPL - shed) := by
  rw [Set.indicator_of_mem (show t ∈ {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ} from h)]

private theorem coord_continuous (i : Fin n) : Continuous (fun y : ℝⁿ => y i) :=
  PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i

/-! ## Representation of latched trajectories -/

section Representation

variable {e₁ e₂ : EuclideanSpace ℝ (Fin n)} (he₁ : IsEquilibrium (m.inputField (load ΔPL)) e₁)
  (he₂ : IsEquilibrium (m.inputField (load (ΔPL - shed))) e₂)
include he₁

/-- Before the first trip, a latched trajectory is the unshed response. -/
@[powerlib_foundation] theorem latched_eqOn_unshed {x : ℝ → ℝⁿ}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x (m.inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    {b : ℝ}
    (hun : ∀ t ∈ Ico 0 b, ¬ ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ) :
    EqOn x (Linear.solution m.A e₁ 0 (x 0)) (Icc 0 b) := by
  refine rightODE_unique m (load ΔPL) (hx.1.mono Icc_subset_Ici_self) (fun t ht => ?_)
    (LTI.solution_continuous m.A e₁ 0 _).continuousOn
    (fun t _ => (LTI.solution_hasDerivAt m he₁ 0 _ t).hasDerivWithinAt) (by simp)
  have h := hx.2 t ht.1
  rwa [latched_input_of_not (hun t ht)] at h

/-- If the unshed response never reaches `−θ`, the latched trajectory is the unshed response. -/
@[powerlib_foundation] theorem latched_representation_noTrip {x : ℝ → ℝⁿ}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x (m.inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    (hφ : ∀ t ≥ 0, -θ < Linear.solution m.A e₁ 0 (x 0) t i₀) :
    ∀ t ≥ 0, x t = Linear.solution m.A e₁ 0 (x 0) t := by
  have hnever : ∀ t ≥ 0, ¬ ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ := by
    intro t ht htrip
    obtain ⟨τ, hτ, hτz⟩ := htrip
    obtain ⟨T, hT0, hTz, hfirst⟩ := exists_first_crossing (z := fun τ => x τ i₀)
      ((coord_continuous i₀).comp_continuousOn hx.1) ⟨τ, hτ.1, hτz⟩
    have hun : ∀ s ∈ Ico 0 T, ¬ ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ := fun s hs h' =>
      absurd ((latchedTrip_iff_of_first hT0 hTz hfirst).1 h') (not_le.2 hs.2)
    have heq := latched_eqOn_unshed he₁ hx hun ⟨hT0, le_rfl⟩
    have := hφ T hT0
    have hTz' : x T i₀ ≤ -θ := hTz
    rw [heq] at hTz'
    linarith
  intro t ht
  exact latched_eqOn_unshed he₁ hx (fun s hs => hnever s hs.1) ⟨ht, le_rfl⟩

include he₂ in
/-- If the unshed response first reaches `−θ` at `T`, the latched trajectory equals it on
`[0, T]` and equals the post-shedding response from its state at `T` afterwards. -/
@[powerlib_foundation] theorem latched_representation_trip {x : ℝ → ℝⁿ}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x (m.inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    {T : ℝ} (hT0 : 0 ≤ T)
    (hTz : Linear.solution m.A e₁ 0 (x 0) T i₀ ≤ -θ)
    (hfirst : ∀ s ∈ Ico 0 T, -θ < Linear.solution m.A e₁ 0 (x 0) s i₀) :
    ∀ t ≥ 0, x t = if t ≤ T then Linear.solution m.A e₁ 0 (x 0) t
      else Linear.solution m.A e₂ 0 (Linear.solution m.A e₁ 0 (x 0) T) (t - T) := by
  set φ := Linear.solution m.A e₁ 0 (x 0)
  have hxc : ContinuousOn (fun τ => x τ i₀) (Ici 0) :=
    (coord_continuous i₀).comp_continuousOn hx.1
  -- no trip before `T`
  have hun : ∀ s ∈ Ico 0 T, ¬ ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ := by
    intro s hs htrip
    obtain ⟨τ, hτ, hτz⟩ := htrip
    obtain ⟨Tx, hTx0, hTxz, hfx⟩ := exists_first_crossing hxc ⟨τ, hτ.1, hτz⟩
    have hTxs : Tx ≤ s := (latchedTrip_iff_of_first hTx0 hTxz hfx).1 ⟨τ, hτ, hτz⟩
    have hunx : ∀ r ∈ Ico 0 Tx, ¬ ∃ τ ∈ Icc 0 r, x τ i₀ ≤ -θ := fun r hr h' =>
      absurd ((latchedTrip_iff_of_first hTx0 hTxz hfx).1 h') (not_le.2 hr.2)
    have heq := latched_eqOn_unshed he₁ hx hunx ⟨hTx0, le_rfl⟩
    have := hfirst Tx ⟨hTx0, lt_of_le_of_lt hTxs hs.2⟩
    have hTxz' : x Tx i₀ ≤ -θ := hTxz
    rw [heq] at hTxz'
    linarith
  have hbefore := latched_eqOn_unshed he₁ hx hun
  have hxT : x T = φ T := hbefore ⟨hT0, le_rfl⟩
  have htrip : ∀ t ≥ T, ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ := fun t ht =>
    ⟨T, ⟨hT0, ht⟩, by rw [hxT]; exact hTz⟩
  -- after `T`: post-shedding dynamics
  set ψ := fun t => Linear.solution m.A e₂ 0 (φ T) (t - T)
  have hψd : ∀ t, HasDerivAt ψ (m.inputField (load (ΔPL - shed)) (ψ t)) t := fun t => by
    have h := (LTI.solution_hasDerivAt m he₂ 0 (φ T) (t - T)).comp_sub_const t T
    exact h
  have hafter : ∀ b ≥ T, EqOn x ψ (Icc T b) := by
    intro b _
    refine rightODE_unique m (load (ΔPL - shed))
      (hx.1.mono fun s hs => le_trans hT0 hs.1) (fun t ht => ?_)
      (continuous_iff_continuousAt.2 fun t => (hψd t).continuousAt).continuousOn
      (fun t _ => (hψd t).hasDerivWithinAt) (by simp [ψ, hxT])
    have h := hx.2 t (le_trans hT0 ht.1)
    rwa [latched_input_of (htrip t ht.1)] at h
  intro t ht
  split_ifs with h
  · exact hbefore ⟨ht, h⟩
  · exact hafter t (le_of_lt (not_le.1 h)) ⟨le_of_lt (not_le.1 h), le_rfl⟩

include he₂ in
/-- Uniqueness of the closed-loop solution. -/
@[powerlib_foundation] theorem latched_unique {x y : ℝ → ℝⁿ}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x (m.inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    (hy : (ContinuousOn y (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt y (m.inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, y τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (y t)) (Ici t) t))
    (h0 : x 0 = y 0) : EqOn x y (Ici 0) := by
  intro t ht
  by_cases hφ : ∀ t ≥ 0, -θ < Linear.solution m.A e₁ 0 (x 0) t i₀
  · rw [latched_representation_noTrip he₁ hx hφ t ht,
      latched_representation_noTrip he₁ hy (h0 ▸ hφ) t ht, h0]
  · push Not at hφ
    obtain ⟨T, hT0, hTz, hfirst⟩ := exists_first_crossing (z := fun τ =>
      Linear.solution m.A e₁ 0 (x 0) τ i₀)
      ((coord_continuous i₀).comp (LTI.solution_continuous m.A e₁ 0 _)).continuousOn hφ
    rw [latched_representation_trip he₁ he₂ hx hT0 hTz hfirst t ht,
      latched_representation_trip he₁ he₂ hy hT0 (h0 ▸ hTz) (h0 ▸ hfirst) t ht, h0]

include he₂ in
/-- Existence of the closed-loop solution from every initial state. -/
@[powerlib_foundation] theorem latched_exists (x₀ : ℝⁿ) :
    ∃ x : ℝ → ℝⁿ, (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
      HasDerivWithinAt x (m.inputField (load (ΔPL -
        {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t) ∧
      x 0 = x₀ := by
  set φ := Linear.solution m.A e₁ 0 x₀
  have hφc : Continuous φ := LTI.solution_continuous m.A e₁ 0 x₀
  by_cases hφ : ∀ t ≥ 0, -θ < φ t i₀
  · refine ⟨φ, ⟨hφc.continuousOn, fun t _ => ?_⟩, by simp [φ]⟩
    have hnot : ¬ ∃ τ ∈ Icc 0 t, φ τ i₀ ≤ -θ := by
      rintro ⟨τ, hτ, hτz⟩
      exact absurd hτz (not_le.2 (hφ τ hτ.1))
    rw [latched_input_of_not hnot]
    exact (LTI.solution_hasDerivAt m he₁ 0 x₀ t).hasDerivWithinAt
  · push Not at hφ
    obtain ⟨T, hT0, hTz, hfirst⟩ :=
      exists_first_crossing (z := fun τ => φ τ i₀)
        ((coord_continuous i₀).comp hφc).continuousOn hφ
    set ψ := fun t => Linear.solution m.A e₂ 0 (φ T) (t - T)
    have hψd : ∀ t, HasDerivAt ψ (m.inputField (load (ΔPL - shed)) (ψ t)) t := fun t =>
      (LTI.solution_hasDerivAt m he₂ 0 (φ T) (t - T)).comp_sub_const t T
    have hψc : Continuous ψ :=
      continuous_iff_continuousAt.2 fun t => (hψd t).continuousAt
    have hψT : ψ T = φ T := by simp [ψ]
    set x := fun t => if t ≤ T then φ t else ψ t
    have hxc : Continuous x :=
      Continuous.if_le hφc hψc continuous_id continuous_const (fun t ht => by rw [ht, hψT])
    have hx0 : x 0 = x₀ := by simp [x, hT0, φ]
    have hxle : ∀ t ≤ T, x t = φ t := fun t ht => ite_eq_left ht
    have hxge : ∀ t ≥ T, x t = ψ t := by
      intro t ht
      by_cases h : t ≤ T
      · have : t = T := le_antisymm h ht
        rw [show x t = φ t from ite_eq_left h, this, hψT]
      · exact ite_eq_right h
    refine ⟨x, ⟨hxc.continuousOn, fun t ht => ?_⟩, hx0⟩
    rcases lt_or_ge t T with hlt | hge
    · -- before the trip: no shedding, `x = φ` near `t`
      have hnot : ¬ ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ := by
        rintro ⟨τ, hτ, hτz⟩
        rw [hxle τ (hτ.2.trans hlt.le)] at hτz
        exact absurd hτz (not_le.2 (hfirst τ ⟨hτ.1, lt_of_le_of_lt hτ.2 hlt⟩))
      rw [latched_input_of_not hnot, hxle t hlt.le]
      have hev : x =ᶠ[𝓝 t] φ := by
        filter_upwards [Iio_mem_nhds hlt] with s hs using hxle s (le_of_lt hs)
      exact ((LTI.solution_hasDerivAt m he₁ 0 x₀ t).congr_of_eventuallyEq hev).hasDerivWithinAt
    · -- after the trip: shedding, `x = ψ` on `[t, ∞)`
      have htrip : ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ :=
        ⟨T, ⟨hT0, hge⟩, by rw [hxle T le_rfl]; exact hTz⟩
      rw [latched_input_of htrip, hxge t hge]
      exact (hψd t).hasDerivWithinAt.congr (fun s hs => hxge s (le_trans hge hs)) (hxge t hge)

end Representation

/-! ## Convergence -/

section Convergence

variable {e₁ e₂ : EuclideanSpace ℝ (Fin n)} (he₁ : IsEquilibrium (m.inputField (load ΔPL)) e₁)
  (he₂ : IsEquilibrium (m.inputField (load (ΔPL - shed))) e₂) (hA : IsHurwitz m.A)
include he₁ he₂ hA

/-- A latched trajectory that trips converges to the post-shedding equilibrium. -/
@[powerlib_foundation] theorem latched_tendsto_of_trip {x : ℝ → ℝⁿ}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x (m.inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    (htrip : ∃ t ≥ 0, x t i₀ ≤ -θ) :
    Tendsto x atTop (𝓝 e₂) := by
  set φ := Linear.solution m.A e₁ 0 (x 0)
  by_cases hφ : ∀ t ≥ 0, -θ < φ t i₀
  · obtain ⟨t, ht, htz⟩ := htrip
    have := latched_representation_noTrip he₁ hx hφ t ht
    rw [this] at htz
    exact absurd htz (not_le.2 (hφ t ht))
  · push Not at hφ
    obtain ⟨T, hT0, hTz, hfirst⟩ :=
      exists_first_crossing (z := fun τ => φ τ i₀)
        ((coord_continuous i₀).comp (LTI.solution_continuous m.A e₁ 0 _)).continuousOn hφ
    have hrep := latched_representation_trip he₁ he₂ hx hT0 hTz hfirst
    have hψ : Tendsto (Linear.solution m.A e₂ 0 (φ T)) atTop (𝓝 e₂) :=
      LTI.tendsto_equilibrium m hA he₂ (t₀ := 0)
        (fun t _ => (LTI.solution_hasDerivAt m he₂ 0 (φ T) t).hasDerivWithinAt)
    have hψ' : Tendsto (fun t => Linear.solution m.A e₂ 0 (φ T) (t - T)) atTop (𝓝 e₂) :=
      hψ.comp (tendsto_atTop_add_const_right _ (-T) tendsto_id |>.congr fun t => by
        simp only [id]; ring)
    refine hψ'.congr' ?_
    filter_upwards [eventually_gt_atTop T] with t ht
    rw [hrep t (hT0.trans ht.le), ite_eq_right (not_le.2 ht)]

omit he₂ in
/-- A latched trajectory that never trips converges to the pre-shedding equilibrium. -/
@[powerlib_foundation] theorem latched_tendsto_of_noTrip {x : ℝ → ℝⁿ}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x (m.inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ i₀ ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    (hno : ∀ t ≥ 0, -θ < x t i₀) :
    Tendsto x atTop (𝓝 e₁) := by
  have hun : ∀ t ≥ 0, ¬ ∃ τ ∈ Icc 0 t, x τ i₀ ≤ -θ := by
    rintro t - ⟨τ, hτ, hτz⟩
    exact absurd hτz (not_le.2 (hno τ hτ.1))
  have hrep : ∀ t ≥ 0, x t = Linear.solution m.A e₁ 0 (x 0) t := fun t ht =>
    latched_eqOn_unshed he₁ hx (fun s hs => hun s hs.1) ⟨ht, le_rfl⟩
  have hφ := LTI.tendsto_equilibrium m hA he₁ (t₀ := 0)
    (fun t _ => (LTI.solution_hasDerivAt m he₁ 0 (x 0) t).hasDerivWithinAt)
  refine hφ.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact (hrep t ht).symm

end Convergence

/-! ## Instances (implementation evidence, private) -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Swing + governor plant from rest, underdamped, load increase: if the unprotected nadir is at or
below `−θ`, the latched relay trips and `Δω → −(ΔP_L − p P⁰)/(K_R + D)`. -/
private theorem swingGovernor_latched_trip {M D K Tg : ℝ} (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) (_hP : 0 < ΔPL)
    (hζ : SwingGovernor.dampingRatio M D K Tg < 1)
    (hnadir : SwingGovernor.nadirValue M D K Tg ΔPL ≤ -θ) {x : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x ((SwingGovernor.plant M D K Tg).inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ 0 ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    (h0 : x 0 = 0) :
    (∃ t ≥ 0, x t 0 ≤ -θ) ∧
      Tendsto (fun t => x t 0) atTop (𝓝 (-(ΔPL - shed) / (K + D))) := by
  have he₁ := SwingGovernor.steadyState_isEquilibrium (ΔPL := ΔPL) hM.ne' hTg.ne' hKD.ne'
  have he₂ := SwingGovernor.steadyState_isEquilibrium (ΔPL := ΔPL - shed) hM.ne' hTg.ne'
    hKD.ne'
  have hA := (SwingGovernor.isHurwitz_iff_of_nonneg hM hTg hD).2 hKD
  have htrip : ∃ t ≥ 0, x t 0 ≤ -θ := by
    by_contra hno
    push Not at hno
    have hun : ∀ t ≥ 0, ¬ ∃ τ ∈ Icc 0 t, x τ 0 ≤ -θ := by
      rintro t - ⟨τ, hτ, hτz⟩
      exact absurd hτz (not_le.2 (hno τ hτ.1))
    set φ := Linear.solution (SwingGovernor.plant M D K Tg).A
      (SwingGovernor.steadyState D K ΔPL) 0 (x 0)
    have hrep : ∀ t ≥ 0, x t = φ t := fun t ht =>
      latched_eqOn_unshed he₁ hx (fun s hs => hun s hs.1) ⟨ht, le_rfl⟩
    have hφ : IsIntegralCurveOn φ
        (fun _ y => (SwingGovernor.plant M D K Tg).inputField (load ΔPL) y) (Ici 0) :=
      fun t _ => (LTI.solution_hasDerivAt _ he₁ 0 (x 0) t).hasDerivWithinAt
    have hωd := SwingGovernor.dampedFreq_pos hM hTg hD hKD hζ
    have hT0 : 0 < SwingGovernor.nadirTime M D K Tg := SwingGovernor.tCrit_pos hωd
    have hφ0 : φ 0 = 0 := by simp [φ, h0]
    have hval : φ (SwingGovernor.nadirTime M D K Tg) 0 = SwingGovernor.nadirValue M D K Tg ΔPL := by
      rw [LTI.trajectory_eq_osc2 _ he₁ (SwingGovernor.trace_A hM hTg hKD)
        (SwingGovernor.det_A hM hTg hD hKD hζ) hωd.ne' hφ hT0.le, hφ0,
        SwingGovernor.osc2_freq hM hTg hD hKD hζ, SwingGovernor.respC_nadirTime hM hTg hD hKD hζ]
    have := hno _ hT0.le
    rw [hrep _ hT0.le, hval] at this
    linarith
  refine ⟨htrip, ?_⟩
  have h := latched_tendsto_of_trip he₁ he₂ hA hx htrip
  have := ((coord_continuous 0).tendsto _).comp h
  simpa [Function.comp_def] using this

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Third-order reheat SFR plant under the added stability condition: a latched trajectory that
trips converges to `Δω = −(ΔP_L − p P⁰)/(K_R + D)`. -/
private theorem sfr_latched_tendsto {M D K F Tg TR : ℝ} (hM : 0 < M) (hTg : 0 < Tg)
    (hTR : 0 < TR) (hD : 0 ≤ D) (hK : 0 ≤ K) (hKD : 0 < K + D) (hF : Tg / (Tg + TR) ≤ F)
    {x : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : (ContinuousOn x (Ici 0) ∧ ∀ t, 0 ≤ t →
        HasDerivWithinAt x ((SFR.plant M D K F Tg TR).inputField (load (ΔPL -
          {s | ∃ τ ∈ Icc 0 s, x τ 0 ≤ -θ}.indicator (fun _ => shed) t)) (x t)) (Ici t) t))
    (htrip : ∃ t ≥ 0, x t 0 ≤ -θ) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-(ΔPL - shed) / (K + D))) := by
  have he₁ := SFR.steadyState_isEquilibrium (F := F) (ΔPL := ΔPL) hM.ne' hTg.ne' hTR.ne' hKD.ne'
  have he₂ := SFR.steadyState_isEquilibrium (F := F) (ΔPL := ΔPL - shed) hM.ne' hTg.ne'
    hTR.ne' hKD.ne'
  have hA := SFR.isHurwitz_of_hp_fraction hM hTg hTR hD hK hKD hF
  have h := latched_tendsto_of_trip he₁ he₂ hA hx htrip
  have := ((coord_continuous 0).tendsto _).comp h
  simpa [Function.comp_def] using this

end powerlib.Frequency.UFLS
