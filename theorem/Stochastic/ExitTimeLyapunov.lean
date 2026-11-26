import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ExitTimeLower

/-! # Exit from a sublevel domain of a Lyapunov function: the lower bound for the exit time

For the solution `x^ε = S(x₀, √ε B)` of `x(t) = x₀ + √ε N B(t) + ∫₀ᵗ b(x)` and a compact `K ∋ x₀`,
the lower bounds `liminf_{ε→0⁺} ε log E τ_ε ≥ a (v_t − V(x₀))` and
`P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}` (every `β < a (v_t − V(x₀))`, some `γ > 0`) from three
deterministic properties of a continuous function `V` (a Lyapunov function of the noiseless flow
that certifies the Hamilton–Jacobi inequality):
* (Hamilton–Jacobi) the quasi-potential of the Freidlin–Wentzell rate is at least
  `a (V(x) − V(y))` from `y` to `x` (a subsolution `a V`, `a > 0`);
* (level) a path from `y ∈ K` in the closure of the paths leaving `K` reaches the level `V ≥ v_t`;
* (drop) away from `x₀` the noiseless flow loses a uniform amount of `V` over the unit time.
The drop survives driving paths of small sup norm (tube lemma, compactness and the joint
continuity of the solution map), hence paths of small Schilder rate, while a path of rate
`≥ c₁` pays `(1 − θ) c₁` beyond its gain at the full rate `a`: this is the moment inequality of
the generic deterministic-time chain `Stochastic.LDP.le_liminf_log_lintegral_exitTime`
(`theorem/Stochastic/ExitTimeLower.lean`) for `θ a V`, with `θ → 1` and the bottom level
`V(x₀) + ζ`, `ζ → 0`.

Scope.
* Generic: `E` a real Banach space, `b` globally Lipschitz, one noise column
  `N : (Fin 1 → ℝ) →L[ℝ] E`, `B` a Brownian motion all of whose paths are continuous, `K`
  compact, the exit time `Stochastic.LDP.exitTime` (`⊤` if the path never leaves `K`), its
  expectation the lower Lebesgue integral. The three properties are hypotheses (deterministic
  statements, checked model by model: the Hamilton–Jacobi bound from a verification theorem, the
  drop from LaSalle's argument); blocks of unit length.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2 (Thm 4.2.1, lower bound for the exit time; the quasi-potential and its Hamilton–Jacobi
characterization, Ch. 4 §3); A. Dembo, O. Zeitouni, *Large Deviations Techniques and
Applications*, 2nd ed. (1998), Thm 5.7.11(a); J. P. LaSalle, *The Stability of Dynamical Systems*
(1976) (the uniform decrease of a Lyapunov function away from the invariant set).

Results.
* `eq_of_pushRate_ne_top` (a path of finite rate from `y` starts at `y`).
* `exists_drop_of_lt` (a strict drop over a compact set is uniform), `exists_tube_drop` (**the
  drop survives small driving paths**).
* `pushRate_moment_ge` (**the moment inequality** for `θ a V`).
* `le_liminf_log_lintegral_exitTime_of_lyapunov` (**`liminf ε log E τ_ε ≥ a (v_t − V(x₀))`**),
  `eventually_measure_exitTime_le_of_lyapunov` (**`P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}`**,
  `β < a (v_t − V(x₀))`).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A path of finite Freidlin–Wentzell rate from `y` starts at `y`. -/
@[tmio T, powerlib_foundation] theorem eq_of_pushRate_ne_top {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {y : E} {T : ℝ≥0}
    {φ : C(Icc (0 : ℝ) T, E)} (h : pushRate (solMap b N y) (schilderRate T) φ ≠ ⊤) :
    φ ⟨0, le_rfl, T.coe_nonneg⟩ = y := by
  obtain ⟨w, hw⟩ := iInf_lt_iff.mp (lt_top_iff_ne_top.mpr h)
  obtain ⟨hwφ, hwr⟩ := iInf_lt_iff.mp hw
  have hw0 := pathExt_zero_of_schilderRate_ne_top (ne_top_of_lt hwr)
  rw [← hwφ, solMap_spec hb]
  have : w ⟨0, le_rfl, T.coe_nonneg⟩ = 0 := by
    ext j; fin_cases j
    rw [← pathExt_of_mem w ⟨le_rfl, T.coe_nonneg⟩]
    exact hw0
  simp [this]

/-- **A strict drop on a compact set is uniform**: if over the unit time the noiseless flow lowers
the continuous `V` at every state of a compact `C`, it lowers it by a uniform `c > 0` there. -/
@[tmio T, powerlib_foundation] theorem exists_drop_of_lt {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {C : Set E} (hC : IsCompact C)
    {V : E → ℝ} (hV : Continuous V)
    (hlt : ∀ y ∈ C, V (pathExt (solMap b N y
      (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1) < V y) :
    ∃ c > 0, ∀ y ∈ C, V (pathExt (solMap b N y
      (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1) ≤ V y - c := by
  have hcont : Continuous fun y => pathExt (solMap b N y
      (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1 :=
    (continuous_eval_const _).comp ((continuous_solMap_uncurry hb N (T := 1)).comp
      (continuous_id.prodMk continuous_const))
  set d : E → ℝ := fun y => V y - V (pathExt (solMap b N y
    (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1) with hd
  have hdc : Continuous d := hV.sub (hV.comp hcont)
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨1, one_pos, fun y hy => absurd (hCe ▸ hy) (notMem_empty y)⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hC.exists_isMinOn hCne hdc.continuousOn
  have hd0 : 0 < d y₀ := by have := hlt y₀ hy₀; simp only [hd]; linarith
  refine ⟨d y₀, hd0, fun y hy => ?_⟩
  have h := hmin hy
  change d y₀ ≤ d y at h
  simp only [hd] at h ⊢
  linarith

/-- **The drop survives small driving paths**: if on a compact `C` the noiseless flow over the
unit time lowers the continuous `V` by at least `c`, there is `ρ > 0` such that every solution
from `C` driven by a path of sup norm `< ρ` lowers it by at least `c/2`. -/
@[tmio T, powerlib_foundation] theorem exists_tube_drop {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {C : Set E} (hC : IsCompact C)
    {V : E → ℝ} (hV : Continuous V) {c : ℝ} (hc : 0 < c)
    (hdrop : ∀ y ∈ C, V (pathExt (solMap b N y
      (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1) ≤ V y - c) :
    ∃ ρ > 0, ∀ y ∈ C, ∀ w : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ), ‖w‖ < ρ →
      V (pathExt (solMap b N y w) 1) ≤ V y - c / 2 := by
  set g : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ) → E → ℝ := fun w y =>
    V (pathExt (solMap b N y w) 1) - V y with hg_def
  have hg : Continuous fun z : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ) × E => g z.1 z.2 := by
    have h := (continuous_solMap_uncurry hb N (T := 1)).comp (continuous_snd.prodMk continuous_fst)
    exact (hV.comp ((continuous_pathExt_apply 1).comp h)).sub (hV.comp continuous_snd)
  have hev : ∀ᶠ w in 𝓝 (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ)), ∀ y ∈ C,
      g w y < -(c / 2) := by
    refine hC.eventually_forall_of_forall_eventually fun y hy => ?_
    have h0' : g 0 y < -(c / 2) := by
      have := hdrop y hy
      simp only [hg_def]
      linarith
    exact (hg.tendsto (0, y)).eventually (gt_mem_nhds h0')
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun y hy w hw => ?_⟩
  have := hball (show dist w 0 < ρ by rwa [dist_zero_right]) y hy
  simp only [hg_def] at this
  linarith

/-- **The moment inequality** (unit block): with the Hamilton–Jacobi bound `a (V(x) − V(y))` for
the quasi-potential of the rate, `θ ∈ (0, 1)`, the drop `c` of `V` for driving paths of norm
`< ρ` from states of `K` at distance `≥ r` from `x₀`, and `V ≤ V(x₀) + ζ` within distance `r`,
every path from `y ∈ K` satisfies
`J_y(φ) ≥ θ a V(φ(1)) − max(θ a V(y) − δ, θ a (V(x₀) + ζ))`, `δ = min(θ a c, (1 − θ) ρ²/4)`. -/
@[tmio T, powerlib_foundation] theorem pushRate_moment_ge {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {K : Set E} {x₀ : E} {V : E → ℝ}
    {a θ c ρ ζ r : ℝ} (ha : 0 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hρ : 0 < ρ)
    (hqp : ∀ y x : E, ENNReal.ofReal (a * (V x - V y)) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, E)) (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        pushRate (solMap b N y) (schilderRate T) φ)
    (htube : ∀ y ∈ K, r ≤ dist y x₀ → ∀ w : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ),
      ‖w‖ < ρ → V (pathExt (solMap b N y w) 1) ≤ V y - c)
    (hnear : ∀ y, dist y x₀ < r → V y ≤ V x₀ + ζ) {y : E} (hy : y ∈ K)
    (φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), E)) :
    ENNReal.ofReal (θ * a * V (pathExt φ ((1 : ℝ≥0) : ℝ)) -
      max (θ * a * V y - min (θ * a * c) ((1 - θ) * (ρ ^ 2 / 4))) (θ * a * (V x₀ + ζ))) ≤
      pushRate (solMap b N y) (schilderRate 1) φ := by
  set δ := min (θ * a * c) ((1 - θ) * (ρ ^ 2 / 4)) with hδ
  set J := pushRate (solMap b N y) (schilderRate 1) φ with hJ
  set Vφ := V (pathExt φ ((1 : ℝ≥0) : ℝ)) with hVφ
  rcases eq_or_ne J ⊤ with htop | htop
  · rw [htop]; exact le_top
  -- the Hamilton–Jacobi bound at the end point
  have hend : φ ⟨((1 : ℝ≥0) : ℝ), (1 : ℝ≥0).coe_nonneg, le_rfl⟩ = pathExt φ ((1 : ℝ≥0) : ℝ) :=
    (pathExt_of_mem _ ⟨(1 : ℝ≥0).coe_nonneg, le_rfl⟩).symm
  have hHJ : ENNReal.ofReal (a * (Vφ - V y)) ≤ J := by
    have hq := iInf_pushRate_le_of_le hb N y φ (t := 1) le_rfl
    have h := (hqp y (φ ⟨((1 : ℝ≥0) : ℝ), (1 : ℝ≥0).coe_nonneg, le_rfl⟩)).trans hq
    rw [hend] at h
    exact h
  have hJr : a * (Vφ - V y) ≤ J.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).mp hHJ
  by_cases hry : dist y x₀ < r
  · -- near `x₀`
    have hVy := hnear y hry
    refine le_trans ?_ hHJ
    refine ENNReal.ofReal_le_ofReal_iff'.mpr ?_
    have hm : θ * a * (V x₀ + ζ) ≤ max (θ * a * V y - δ) (θ * a * (V x₀ + ζ)) :=
      le_max_right _ _
    have hθa : 0 ≤ θ * a := by positivity
    have h1 : θ * a * Vφ - max (θ * a * V y - δ) (θ * a * (V x₀ + ζ)) ≤
        θ * a * (Vφ - V y) := by nlinarith
    by_cases hle : V y ≤ Vφ
    · left
      refine h1.trans ?_
      have h2 : 0 ≤ Vφ - V y := by linarith
      have h3 : θ * a ≤ a := by nlinarith
      exact mul_le_mul_of_nonneg_right h3 h2
    · right
      refine h1.trans ?_
      have h2 : Vφ - V y ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos hθa h2
  rw [not_lt] at hry
  have hmax : θ * a * V y - δ ≤ max (θ * a * V y - δ) (θ * a * (V x₀ + ζ)) := le_max_left _ _
  by_cases hJc : J < ENNReal.ofReal (ρ ^ 2 / 4)
  · -- a small rate: `V` drops
    obtain ⟨w, hw⟩ := iInf_lt_iff.mp hJc
    obtain ⟨hwφ, hwr⟩ := iInf_lt_iff.mp hw
    have hwn := norm_le_of_schilderRate_lt hwr
    have hwρ : ‖w‖ < ρ := by
      refine lt_of_le_of_lt hwn ?_
      rw [Real.sqrt_lt' hρ]
      push_cast
      nlinarith
    have hdrop := htube y hy hry w hwρ
    rw [hwφ] at hdrop
    have hδc : δ ≤ θ * a * c := min_le_left _ _
    rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · have : θ * a * Vφ ≤ θ * a * (V y - c) :=
        mul_le_mul_of_nonneg_left hdrop (by positivity)
      nlinarith
  · -- a large rate: it pays for the gain
    rw [not_lt] at hJc
    have hc₁ : ρ ^ 2 / 4 ≤ J.toReal := (ENNReal.ofReal_le_iff_le_toReal htop).mp hJc
    have hδ1 : δ ≤ (1 - θ) * (ρ ^ 2 / 4) := min_le_right _ _
    rw [← ENNReal.ofReal_toReal htop]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : θ * (a * (Vφ - V y)) ≤ θ * J.toReal :=
      mul_le_mul_of_nonneg_left hJr hθ0.le
    have h2 : (1 - θ) * (ρ ^ 2 / 4) ≤ (1 - θ) * J.toReal :=
      mul_le_mul_of_nonneg_left hc₁ (by linarith)
    nlinarith

/-- The data of the chain for `θ a V`: for `β < a (v_t − V(x₀))`, a contraction `δ > 0` and a
bottom level `v_b ≥ θ a V(x₀)` with `β < θ a v_t − v_b`, and the exit and moment inequalities of
`Stochastic.LDP.le_liminf_log_lintegral_exitTime` for `θ a V` on unit blocks. -/
@[tmio T, powerlib_foundation] private theorem exists_chain_data {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {K : Set E} (hK : IsCompact K) {x₀ : E}
    {V : E → ℝ} (hV : Continuous V) {a vt : ℝ} (ha : 0 < a) (hvt : V x₀ < vt)
    (hqp : ∀ y x : E, ENNReal.ofReal (a * (V x - V y)) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, E)) (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        pushRate (solMap b N y) (schilderRate T) φ)
    (hlevel : ∀ y ∈ K, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), E) | ∃ t, φ t ∉ K},
      φ ⟨0, le_rfl, zero_le_one⟩ = y → ∃ t, vt ≤ V (φ t))
    (hdrop : ∀ r > 0, ∃ c > 0, ∀ y ∈ K, r ≤ dist y x₀ →
      V (pathExt (solMap b N y (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1) ≤ V y - c)
    {β : ℝ} (hβ : β < a * (vt - V x₀)) :
    ∃ θ vb δ : ℝ, 0 < δ ∧ θ * a * V x₀ ≤ vb ∧ β < θ * a * vt - vb ∧ vb < θ * a * vt ∧
      (∀ y ∈ K, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), E) | ∃ t, φ t ∉ K},
        ENNReal.ofReal (θ * a * vt - θ * a * V y) ≤ pushRate (solMap b N y) (schilderRate 1) φ) ∧
      ∀ y ∈ K, ∀ φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), E), pathExt φ ((1 : ℝ≥0) : ℝ) ∈ K →
        ENNReal.ofReal (θ * a * V (pathExt φ ((1 : ℝ≥0) : ℝ)) - max (θ * a * V y - δ) vb) ≤
          pushRate (solMap b N y) (schilderRate 1) φ := by
  set v := a * (vt - V x₀) with hv
  have hv0 : 0 < v := mul_pos ha (by linarith)
  set g := v - max β 0 with hg
  have hg0 : 0 < g := by have := max_lt hβ hv0; linarith
  have hgv : g ≤ v := by have := le_max_right β 0; linarith
  set θ := 1 - g / (4 * v) with hθ
  have hgv4 : g / (4 * v) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hθ0 : 0 < θ := by linarith
  have hθ1 : θ < 1 := by have : 0 < g / (4 * v) := by positivity
                         linarith
  set ζ := min ((vt - V x₀) / 2) (g / (4 * a)) with hζ
  have hζ0 : 0 < ζ := lt_min (by linarith) (by positivity)
  have hζ1 : ζ ≤ (vt - V x₀) / 2 := min_le_left _ _
  have hζ2 : ζ ≤ g / (4 * a) := min_le_right _ _
  obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp (hV.continuousAt (x := x₀)) ζ hζ0
  have hnear' : ∀ y, dist y x₀ < r → V y ≤ V x₀ + ζ := by
    intro y hy
    have := hnear hy
    rw [Real.dist_eq, abs_lt] at this
    linarith
  obtain ⟨c, hc, hdr⟩ := hdrop r hr
  obtain ⟨ρ, hρ, htube⟩ := exists_tube_drop hb N (hK.inter_right (isClosed_le continuous_const
    (continuous_id.dist continuous_const))) hV hc (C := K ∩ {y | r ≤ dist y x₀})
    fun y hy => hdr y hy.1 hy.2
  have htube' : ∀ y ∈ K, r ≤ dist y x₀ → ∀ w : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ),
      ‖w‖ < ρ → V (pathExt (solMap b N y w) 1) ≤ V y - c / 2 :=
    fun y hy hry w hw => htube y ⟨hy, hry⟩ w hw
  set δ := min (θ * a * (c / 2)) ((1 - θ) * (ρ ^ 2 / 4)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (mul_pos (by linarith) (by positivity))
  have hθa : 0 < θ * a := mul_pos hθ0 ha
  refine ⟨θ, θ * a * (V x₀ + ζ), δ, hδ0, mul_le_mul_of_nonneg_left (by linarith) hθa.le,
    ?_, mul_lt_mul_of_pos_left (by linarith) hθa, fun y hy φ hφ => ?_,
    fun y hy φ _ => pushRate_moment_ge hb N ha hθ0 hθ1 hρ hqp htube' hnear' hy φ⟩
  · -- `θ a v_t − θ a (V(x₀) + ζ) ≥ v − g/2 > β`
    have h1 : a * ζ ≤ g / 4 := by
      calc a * ζ ≤ a * (g / (4 * a)) := mul_le_mul_of_nonneg_left hζ2 ha.le
        _ = g / 4 := by field_simp
    have h2 : θ * v = v - g / 4 := by rw [hθ]; field_simp
    have h3 : θ * a * vt - θ * a * (V x₀ + ζ) = θ * v - θ * (a * ζ) := by rw [hv]; ring
    rw [h3, h2]
    have h4 : θ * (a * ζ) ≤ g / 4 := by
      have : θ * (a * ζ) ≤ 1 * (a * ζ) :=
        mul_le_mul_of_nonneg_right hθ1.le (mul_nonneg ha.le hζ0.le)
      linarith
    have := le_max_left β 0
    linarith
  · -- the exit inequality
    rcases eq_or_ne (pushRate (solMap b N y) (schilderRate 1) φ) ⊤ with htop | htop
    · rw [htop]; exact le_top
    have hφ0 := eq_of_pushRate_ne_top hb N htop
    obtain ⟨t, ht⟩ := hlevel y hy φ hφ hφ0
    have hq := iInf_pushRate_le_of_le hb N y φ (t := ⟨t, t.2.1⟩) t.2.2
    refine le_trans ?_ ((hqp y (φ t)).trans hq)
    refine ENNReal.ofReal_le_ofReal_iff'.mpr ?_
    by_cases hle : V y ≤ vt
    · left
      have h2 : θ * (a * (vt - V y)) ≤ 1 * (a * (vt - V y)) :=
        mul_le_mul_of_nonneg_right hθ1.le (mul_nonneg ha.le (by linarith))
      have h3 : a * (vt - V y) ≤ a * (V (φ t) - V y) :=
        mul_le_mul_of_nonneg_left (by linarith) ha.le
      linarith
    · right
      rw [not_le] at hle
      nlinarith

/-- **Freidlin–Wentzell lower bound for the exit from a Lyapunov sublevel domain**: `K`
compact, `x₀ ∈ K`, `V` continuous with `V(x₀) < v_t`, `a > 0`, and (Hamilton–Jacobi) the
quasi-potential of the rate is at least `a (V(x) − V(y))`; (level) every path from `y ∈ K` in
the closure of the unit-time paths leaving `K` reaches `V ≥ v_t`; (drop) for every `r > 0` the
noiseless flow lowers `V` over the unit time by a uniform `c > 0` at the states of `K` at distance
`≥ r` from `x₀`. Then `liminf_{ε→0⁺} ε log E τ_ε ≥ a (v_t − V(x₀))`. -/
@[tmio T, powerlib_foundation] theorem le_liminf_log_lintegral_exitTime_of_lyapunov
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω)
    {K : Set E} (hK : IsCompact K) {x₀ : E} (hx₀ : x₀ ∈ K) {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {V : E → ℝ} (hV : Continuous V)
    {a vt : ℝ} (ha : 0 < a) (hvt : V x₀ < vt)
    (hqp : ∀ y x : E, ENNReal.ofReal (a * (V x - V y)) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, E)) (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        pushRate (solMap b N y) (schilderRate T) φ)
    (hlevel : ∀ y ∈ K, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), E) | ∃ t, φ t ∉ K},
      φ ⟨0, le_rfl, zero_le_one⟩ = y → ∃ t, vt ≤ V (φ t))
    (hdrop : ∀ r > 0, ∃ c > 0, ∀ y ∈ K, r ≤ dist y x₀ →
      V (pathExt (solMap b N y (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1) ≤ V y - c) :
    ((a * (vt - V x₀) : ℝ) : EReal) ≤ liminf (fun ε : ℝ => (ε : EReal) *
        ENNReal.log (∫⁻ ω, exitTime b N x₀ K (√ε) B hBc ω ∂P)) (𝓝[>] 0) := by
  refine le_of_forall_lt_imp_le_of_dense fun β₀ hβ₀ => ?_
  induction β₀ using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hβ₀ not_top_lt
  | coe β₀ =>
  have hβ₀' : β₀ < a * (vt - V x₀) := EReal.coe_lt_coe_iff.mp hβ₀
  obtain ⟨θ, vb, δ, hδ, hx₀V, hβ, hvb, hexit, hmom⟩ :=
    exists_chain_data hb N hK hV ha hvt hqp hlevel hdrop hβ₀'
  have hT1 : (0 : ℝ) < ((1 : ℝ≥0) : ℝ) := by norm_num
  have hgen := le_liminf_log_lintegral_exitTime hB hBc hK hx₀ hT1 hb N
    (V := fun x => θ * a * V x) (hV.const_mul _) hδ hvb hx₀V hexit hmom
  exact le_trans (EReal.coe_le_coe_iff.mpr hβ.le) hgen

/-- **The exit time from a Lyapunov sublevel domain is exponentially large in probability**:
under the hypotheses of `le_liminf_log_lintegral_exitTime_of_lyapunov`, for every
`β < a (v_t − V(x₀))` there is `γ > 0` with `P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}` for all small
`ε > 0`. -/
@[tmio T, powerlib_foundation] theorem eventually_measure_exitTime_le_of_lyapunov
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω)
    {K : Set E} (hK : IsCompact K) {x₀ : E} (hx₀ : x₀ ∈ K) {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {V : E → ℝ} (hV : Continuous V)
    {a vt : ℝ} (ha : 0 < a) (hvt : V x₀ < vt)
    (hqp : ∀ y x : E, ENNReal.ofReal (a * (V x - V y)) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, E)) (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        pushRate (solMap b N y) (schilderRate T) φ)
    (hlevel : ∀ y ∈ K, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), E) | ∃ t, φ t ∉ K},
      φ ⟨0, le_rfl, zero_le_one⟩ = y → ∃ t, vt ≤ V (φ t))
    (hdrop : ∀ r > 0, ∃ c > 0, ∀ y ∈ K, r ≤ dist y x₀ →
      V (pathExt (solMap b N y (0 : C(Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ), Fin 1 → ℝ))) 1) ≤ V y - c)
    {β : ℝ} (hβ : β < a * (vt - V x₀)) :
    ∃ γ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | exitTime b N x₀ K (√ε) B hBc ω ≤
      ENNReal.ofReal (Real.exp (β / ε))} ≤ ENNReal.ofReal (Real.exp (-γ / ε)) := by
  obtain ⟨θ, vb, δ, hδ, hx₀V, hβ', hvb, hexit, hmom⟩ :=
    exists_chain_data hb N hK hV ha hvt hqp hlevel hdrop hβ
  have hT1 : (0 : ℝ) < ((1 : ℝ≥0) : ℝ) := by norm_num
  exact eventually_measure_exitTime_le hB hBc hK hx₀ hT1 hb N (V := fun x => θ * a * V x)
    (hV.const_mul _) hδ hvb hx₀V hexit hmom hβ'

end powerlib.Stochastic.LDP
