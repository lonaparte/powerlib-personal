import theorem.ParametricResonance.SmoothForcedOrbit
import theorem.Periodic.OrbitalStability

/-! # The forced orbit of a smooth field is exponentially stable when its multipliers are inside

`SmoothForcedOrbit` gives, for a `C³` field `F(x, w)` with input `w₀ + εV̂ cos ωt` and state
perturbation `εA₀'`, the forced orbit and the Floquet multipliers of its variational equation.
Composed with `Periodic.OrbitalStability`, the stable case becomes a statement about the
nonlinear solutions: every solution of the driven system that starts close to the orbit converges
to it exponentially.

Model boundary.
* The hypotheses of `smooth_orbit_floquet_stable` (general modal coordinates with
  `ρ(e^{TA_s}) < 1`) or of `smooth_orbit_floquet_three_stable` (three-state eigen-data); deviation
  coordinates `x = state − x₀`; solutions are integral curves on `[s, ∞)`.
* The conclusion holds for all small `ε > 0`, with `δ`, `K`, `β` depending on `ε`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.2 (stability of the forced trajectory decided by its Floquet multipliers).

Results.
* `exists_lipschitz_ball`, `quad_remainder` — a `C²` field has a quadratic Taylor remainder,
  uniform over base points of a ball.
* `spectralRadius_lt_one_of_eig` — eigenvalues inside the unit circle give spectral radius below
  one.
* `smooth_orbit_exp_stable`, `smooth_orbit_exp_three_stable` — the forced orbit exists and is
  locally exponentially stable for the nonlinear driven system.

Corrections.
None: an extension (orbital stability of the actual forced orbit).

Family and connection conclusions.
None: static evidence on smooth periodically forced ODEs (local exponential stability).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix Set Filter Topology Metric
open scoped Matrix.Norms.Operator
open TwoToOne (base)
open BlockAveraging (expS physLeft physRight modalP modalQ modal_three norm_expS_one)

section Quad

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- A `C²` map has, on a closed ball, a Lipschitz derivative. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitz_ball {G : P → V} {q0 : P}
    (hG : ContDiffAt ℝ 2 G q0) :
    ∃ R K, 0 < R ∧ 0 ≤ K ∧ (∀ q ∈ closedBall q0 R, HasFDerivAt G (fderiv ℝ G q) q) ∧
      ∀ q ∈ closedBall q0 R, ∀ q' ∈ closedBall q0 R,
        ‖fderiv ℝ G q - fderiv ℝ G q'‖ ≤ K * ‖q - q'‖ := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ G) q0 := hG.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have h2 : ∀ᶠ q in 𝓝 q0, ContDiffAt ℝ 2 G q := hG.eventually (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht h2)
  have hsub : closedBall q0 (δ / 2) ⊆ ball q0 δ := closedBall_subset_ball (by linarith)
  refine ⟨δ / 2, K, by positivity, K.2, fun q hq => ?_, fun q hq q' hq' => ?_⟩
  · have hc : ContDiffAt ℝ 2 G q := (hball (hsub hq)).2
    exact (hc.differentiableAt (by norm_num)).hasFDerivAt
  · have := hK.dist_le_mul q (hball (hsub hq)).1 q' (hball (hsub hq')).1
    rwa [dist_eq_norm, dist_eq_norm] at this

/-- The quadratic Taylor remainder at any base point of the ball. -/
@[tmio T, powerlib_foundation] theorem quad_remainder {G : P → V} {q0 : P} {R K : ℝ} (hK : 0 ≤ K)
    (hd : ∀ q ∈ closedBall q0 R, HasFDerivAt G (fderiv ℝ G q) q)
    (hl : ∀ q ∈ closedBall q0 R, ∀ q' ∈ closedBall q0 R,
      ‖fderiv ℝ G q - fderiv ℝ G q'‖ ≤ K * ‖q - q'‖)
    {a h : P} (hsub : closedBall a ‖h‖ ⊆ closedBall q0 R) :
    ‖G (a + h) - G a - fderiv ℝ G a h‖ ≤ K * ‖h‖ ^ 2 := by
  have ha : a ∈ closedBall q0 R := hsub (mem_closedBall_self (norm_nonneg h))
  have h := taylor_sub (G := G) (q0 := a) (r := ‖h‖) (L := K) hK
    (fun q hq => hd q (hsub hq)) (fun q hq => hl q (hsub hq) a ha) le_rfl
    (q1 := a + h) (q2 := a) (by simp [mem_closedBall, dist_eq_norm])
    (mem_closedBall_self (norm_nonneg h))
  simpa [sq, mul_assoc] using h

end Quad

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Eigenvalues inside the unit circle give a spectral radius below one. -/
@[tmio T, powerlib_foundation] theorem spectralRadius_lt_one_of_eig (M : Matrix X X ℂ)
    (h : ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 → M *ᵥ v = μ • v → ‖μ‖ < 1) :
    spectralRadius ℂ M < 1 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [Subsingleton.elim M 0, spectrum.spectralRadius_zero]
    exact zero_lt_one
  · have h1 : ((1 : NNReal) : ENNReal) = 1 := rfl
    rw [← h1]
    apply spectrum.spectralRadius_lt_of_forall_lt
    intro z hz
    rw [LTI.mem_spectrum_iff_exists_eigvec] at hz
    obtain ⟨v, hv, hMv⟩ := hz
    have := h z v hv hMv
    exact_mod_cast this

/-- End-to-end with orbital stability: under the hypotheses of `smooth_orbit_floquet_stable`, for
all small `ε > 0` the forced periodic orbit `y` exists and is locally exponentially stable for the
nonlinear driven system: every solution starting within `δ` of `y(s)` approaches `y` with
`‖x(t) − y(t)‖ ≤ K e^{−β(t − s)} ‖x(s) − y(s)‖` (deviation coordinates `x = state − x₀`). -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_exp_stable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh z *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
        ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨c, hc, hex, hfl⟩ := smooth_orbit_floquet_stable hF hF0 hω hPQ hQP As hA0 hsr hz A0'
    hs hg
  obtain ⟨-, ρ, ε0, -, -, -, hρ, hε0, -, -, -, -, -, -, hJc, -⟩ := smooth_estimates hF hF0 Vh ω A0'
  obtain ⟨R, KL, hR, hKL, hd, hl⟩ :=
    exists_lipschitz_ball (hF.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  refine ⟨c, hc, ?_⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ ε0 ∧ c * ε ≤ ρ ∧ c * ε ≤ R / 3 ∧ ε * |Vh| ≤ R / 3 := by
    have hlim : Tendsto (fun ε : ℝ => (ε, c * ε, c * ε, ε * |Vh|)) (𝓝[>] 0)
        (𝓝 (0, 0, 0, 0)) := by
      have hcont : Continuous (fun ε : ℝ => (ε, c * ε, c * ε, ε * |Vh|)) := by fun_prop
      have h0 := hcont.tendsto 0
      simp only [mul_zero, zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hopen : ∀ᶠ p : ℝ × ℝ × ℝ × ℝ in 𝓝 (0, 0, 0, 0),
        p.1 < ε0 ∧ p.2.1 < ρ ∧ p.2.2.1 < R / 3 ∧ p.2.2.2 < R / 3 := by
      refine ((continuous_fst.tendsto _).eventually (gt_mem_nhds hε0)).and
        (((continuous_fst.comp continuous_snd).tendsto _).eventually (gt_mem_nhds hρ) |>.and
        ((((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).eventually
          (gt_mem_nhds (by positivity : (0 : ℝ) < R / 3))).and
        (((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).eventually
          (gt_mem_nhds (by positivity : (0 : ℝ) < R / 3)))))
    filter_upwards [hlim.eventually hopen] with ε hε
    exact ⟨hε.1.le, hε.2.1.le, hε.2.2.1.le, hε.2.2.2.le⟩
  filter_upwards [hex, hfl, hsmall, self_mem_nhdsWithin] with ε hεex hεfl ⟨hε0', hcρ, hcR, hVR⟩
    hεpos
  obtain ⟨y, hper, hbd, hode⟩ := hεex
  refine ⟨y, hper, hbd, hode, ?_⟩
  have hεpos' : 0 < ε := hεpos
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hode t).continuousAt
  have hJcont : Continuous fun t => smJ F q0 Vh ω A0' ε t (y t) :=
    (hJc ε hεpos'.le hε0').comp_continuous (continuous_id.prodMk hyc) fun t =>
      Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hbd t).trans hcρ))
  have hJp : Function.Periodic (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) := by
    intro t
    have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
    simp only [smJ, hper t, e, Real.cos_add_two_pi]
  have hsr' := spectralRadius_lt_one_of_eig _ (hεfl y hper hbd hode)
  have hpt : ∀ t (v : X → ℝ), ‖v - y t‖ ≤ R / 3 →
      ‖((q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) - q0‖ ≤ 2 * R / 3 := by
    intro t v hv
    have h1 : ‖v‖ ≤ 2 * R / 3 := by
      have := norm_le_insert' v (y t)
      have h2 : ‖v‖ ≤ ‖y t‖ + ‖v - y t‖ := by
        have := norm_add_le (y t) (v - y t); simpa using this
      linarith [hbd t]
    have h3 : |ε * (Vh * Real.cos (ω * t))| ≤ 2 * R / 3 := by
      rw [abs_mul, abs_mul, abs_of_pos hεpos']
      have := Real.abs_cos_le_one (ω * t)
      have : ε * (|Vh| * |Real.cos (ω * t)|) ≤ ε * |Vh| := by
        have := mul_le_mul_of_nonneg_left this (abs_nonneg Vh)
        nlinarith
      linarith
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left, Real.norm_eq_abs]
    exact max_le h1 h3
  have hGc : ContinuousOn (fun p : ℝ × (X → ℝ) =>
      F (q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) + ε • (A0' *ᵥ p.2))
      {p | ‖p.2 - y p.1‖ ≤ R / 3} := by
    intro p hp
    have hφ : Continuous fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ) := by fun_prop
    have hmem : ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ) ∈
        closedBall q0 R := by
      rw [mem_closedBall, dist_eq_norm]; have := hpt p.1 p.2 hp; linarith
    refine ContinuousWithinAt.add ?_ ?_
    · have hca := ContinuousAt.comp (g := F) (x := p) (f := fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ))
        (hd _ hmem).continuousAt hφ.continuousAt
      exact hca.continuousWithinAt
    · exact (by fun_prop : Continuous fun p : ℝ × (X → ℝ) => ε • (A0' *ᵥ p.2)).continuousWithinAt
  have hRem : ∀ t (e : X → ℝ), ‖e‖ ≤ R / 3 →
      ‖(F (q0.1 + (y t + e), q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ (y t + e))) -
        (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) -
        smJ F q0 Vh ω A0' ε t (y t) *ᵥ e‖ ≤ KL * ‖e‖ ^ 2 := by
    intro t e he
    set a : (X → ℝ) × ℝ := (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) with had
    have ha : ‖a - q0‖ ≤ 2 * R / 3 := hpt t (y t) (by simp; positivity)
    have hsub : closedBall a ‖((e, (0 : ℝ)) : (X → ℝ) × ℝ)‖ ⊆ closedBall q0 R := by
      intro q hq
      rw [mem_closedBall, dist_eq_norm] at hq ⊢
      rw [norm_prod_zero] at hq
      have := norm_sub_le_norm_sub_add_norm_sub q a q0
      linarith
    have hq := quad_remainder hKL hd hl hsub
    rw [norm_prod_zero] at hq
    have e1 : ((q0.1 + (y t + e), q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) =
        a + (e, 0) := by
      rw [had]; ext <;> simp [add_assoc]
    have e2 : smJ F q0 Vh ω A0' ε t (y t) *ᵥ e = fderiv ℝ F a (e, 0) + ε • (A0' *ᵥ e) := by
      rw [smJ, Matrix.add_mulVec, Matrix.smul_mulVec, matX_mulVec]
    rw [e1, e2, Matrix.mulVec_add, smul_add]
    convert hq using 2
    abel
  exact Periodic.exp_stable_of_floquet hT hJcont hJp hsr' hode (by positivity) hKL hGc hRem

/-- Three-state `C³` vector fields (pair `±jΩ`, real pole `λ₃ < 0`, drive at `2Ω`): the forced
orbit exists and is locally exponentially stable. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_exp_three_stable
    {F : ((Fin 3) → ℝ) × ℝ → (Fin 3) → ℝ}
    {q0 : ((Fin 3) → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX F q0).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX F q0).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX F q0 *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX F q0 = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ (smA1 F q0 Vh z *ᵥ star r) / 2‖ ^ 2 <
      ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (2 * Ω * t))) +
        ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (2 * Ω * t))) +
          ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * matX F q0 * modalP r r3 =
      fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact smooth_orbit_exp_stable hF hF0 hω hPQ hQP _ hA0
    (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) hz A0'
    (by rw [hLu, hRr]; exact hs) (by rw [hLu, hRr]; exact hg)

end powerlib.ParametricResonance.ForcedOrbit
