import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.LDPContraction

/-! # Exponentially good approximations transfer the large-deviation principle

If random elements `Zₙ(ε)` of a metric space satisfy the large-deviation principle with rates
`Iₙ ≥ I`, approximate `Z(ε)` exponentially well (`P(d(Zₙ(ε), Z(ε)) > δ)` decays faster than any
`e^{−M/ε}` once `n` is large), and every point of finite `I`-rate is the limit of points `y` with
`Iₙ(y) ≤ I(x)`, then `Z(ε)` satisfies the principle with the good rate `I`. This is the form of
Dembo–Zeitouni Thm 4.2.16 used for Schilder's theorem (`Zₙ` the polygonal interpolations).

Scope.
* Probability theory, not an engineering result. `X` a pseudo-metric, second-countable space
  with its Borel sets; `Z(ε)`, `Zₙ(ε)` measurable on one probability space; speed `ε → 0⁺`.
* The rate `I` is good and lower semicontinuous (hypotheses); `Iₙ ≥ I` replaces the
  `limsup` condition of Dembo–Zeitouni for closed sets.

Source: A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998),
Def. 4.2.14 (exponentially good approximations), Thm 4.2.16, Lemma 4.1.6 (goodness and closed
thickenings).

Results.
* `exists_cthickening_lt`: for a good lower semicontinuous rate and a closed `F` with `I > b` on
  `F` (`b < ∞`), `I > b` on a closed thickening of `F`.
* `isLDP_of_expApprox`: the transfer theorem.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X]

/-- **Closed thickenings**: if `I` is good and lower semicontinuous, `F` closed and `b < I` on
`F` (`b < ∞`), then `b < I` on the closed `δ`-thickening of `F` for some `δ > 0`. -/
@[tmio T, powerlib_foundation] theorem exists_cthickening_lt {I : X → ℝ≥0∞} (hI : IsGoodRate I)
    (hlsc : LowerSemicontinuous I) {F : Set X} (hF : IsClosed F) {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (h : ∀ x ∈ F, b < I x) : ∃ δ > 0, ∀ y ∈ cthickening δ F, b < I y := by
  by_contra hcon
  push Not at hcon
  set K : ℕ → Set X := fun k => I ⁻¹' Iic b ∩ cthickening (1 / ((k : ℝ) + 1)) F with hK
  have hKne : ∀ k, (K k).Nonempty := fun k => by
    obtain ⟨y, hy, hIy⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨y, hIy, hy⟩
  have hKmono : ∀ k, K (k + 1) ⊆ K k := fun k y hy => by
    refine ⟨hy.1, cthickening_mono ?_ F hy.2⟩
    push_cast
    gcongr
    linarith
  have hK0 : IsCompact (K 0) := (hI b hb).inter_right isClosed_cthickening
  have hKcl : ∀ k, IsClosed (K k) := fun k =>
    (hlsc.isClosed_preimage b).inter isClosed_cthickening
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKmono hKne hK0 hKcl
  rw [mem_iInter] at hx
  have hxF : x ∈ F := by
    rw [← hF.closure_eq, closure_eq_iInter_cthickening]
    refine mem_iInter₂.mpr fun δ hδ => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    exact cthickening_mono hk.le F (hx k).2
  exact absurd (h x hxF) (not_lt.mpr (hx 0).1)

/-- **Transfer by exponentially good approximations** (Dembo–Zeitouni Thm 4.2.16): if each
`Zₙ(ε)` satisfies the large-deviation principle with rate `Iₙ ≥ I`, every point `x` of finite
rate is approached by points `y` with `Iₙ(y) ≤ I(x)` for all large `n`, and
`P(d(Zₙ(ε), Z(ε)) > δ) ≤ e^{M/ε}` eventually in `ε` once `n` is large (every `δ > 0`, every
`M`), then `Z(ε)` satisfies the principle with the good lower semicontinuous rate `I`. -/
@[tmio T, powerlib_foundation] theorem isLDP_of_expApprox {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {Z : ℝ → Ω → X} {Zn : ℕ → ℝ → Ω → X}
    (hZ : ∀ ε, Measurable (Z ε)) (hZn : ∀ n ε, Measurable (Zn n ε)) {I : X → ℝ≥0∞}
    {In : ℕ → X → ℝ≥0∞} (hlsc : LowerSemicontinuous I) (hgood : IsGoodRate I)
    (hLDP : ∀ n, IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map (Zn n ε)) (In n))
    (hle : ∀ n x, I x ≤ In n x)
    (happ : ∀ x, I x ≠ ⊤ → ∀ δ > 0, ∃ n₀, ∀ n ≥ n₀, ∃ y, dist y x < δ ∧ In n y ≤ I x)
    (hexp : ∀ δ > 0, ∀ M : ℝ, ∃ n₀, ∀ n ≥ n₀, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((ε : ℝ) : EReal) * ENNReal.log (P {ω | δ < dist (Zn n ε ω) (Z ε ω)}) ≤ M) :
    IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map (Z ε)) I := by
  have hdm : ∀ n ε δ, MeasurableSet {ω | δ < dist (Zn n ε ω) (Z ε ω)} := fun n ε δ =>
    measurableSet_lt measurable_const ((hZn n ε).dist (hZ ε))
  have hlog2 : Tendsto (fun ε : ℝ => ε * Real.log 2) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => ε * Real.log 2 := continuous_id.mul continuous_const
    have := hc.tendsto 0
    simp only [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ⟨hlsc, fun A hA => ?_, fun G hG => ?_⟩
  · -- upper bound
    have hmap : (fun ε : ℝ => ((id ε : ℝ) : EReal) * ENNReal.log (P.map (Z ε) A)) =
        fun ε : ℝ => (ε : EReal) * ENNReal.log (P (Z ε ⁻¹' A)) := by
      funext ε; rw [Measure.map_apply (hZ ε) hA]; rfl
    rw [hmap]
    set c := ⨅ x ∈ closure A, ((I x : ℝ≥0∞) : EReal) with hc
    refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
    induction b using EReal.rec with
    | bot => exact absurd hb not_lt_bot
    | top => exact le_top
    | coe r =>
      refine limsup_le_of_le (by isBoundedDefault) ?_
      by_cases hr : 0 ≤ r
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        have h : ENNReal.log (P (Z ε ⁻¹' A)) ≤ 0 := by
          rw [← ENNReal.log_one]; exact ENNReal.log_le_log prob_le_one
        have := mul_le_mul_of_nonneg_left h (by exact_mod_cast hε.le : (0 : EReal) ≤ ε)
        rw [mul_zero] at this
        exact this.trans (EReal.coe_nonneg.mpr hr)
      push Not at hr
      have hrc : ((-r : ℝ) : EReal) < c := by
        rw [EReal.coe_neg]; exact EReal.neg_lt_comm.mp hb
      obtain ⟨e, he1, he2⟩ := exists_between hrc
      have he_top : e ≠ ⊤ := ne_top_of_lt he2
      have he_bot : e ≠ ⊥ := ne_bot_of_gt he1
      set a := e.toReal with ha
      have hae : (a : EReal) = e := EReal.coe_toReal he_top he_bot
      have har : -r < a := by rw [← hae] at he1; exact_mod_cast he1
      have ha0 : 0 < a := by linarith
      have hFI : ∀ x ∈ closure A, ENNReal.ofReal a < I x := by
        intro x hx
        have h1 : c ≤ ((I x : ℝ≥0∞) : EReal) := iInf₂_le x hx
        rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left ha0.le]
        exact (hae ▸ he2).trans_le h1
      obtain ⟨δ, hδ, hthick⟩ :=
        exists_cthickening_lt hgood hlsc isClosed_closure ENNReal.ofReal_ne_top hFI
      set C := cthickening δ (closure A) with hC
      have hCm : MeasurableSet C := isClosed_cthickening.measurableSet
      set r₁ := (r - a) / 2 with hr₁
      have hr₁a : -a < r₁ := by rw [hr₁]; linarith
      have hr₁r : r₁ < r := by rw [hr₁]; linarith
      obtain ⟨n, hn⟩ := hexp δ hδ r₁
      have hup := (hLDP n).2.1 C hCm
      rw [isClosed_cthickening.closure_eq] at hup
      have hinf : (a : EReal) ≤ ⨅ y ∈ C, ((In n y : ℝ≥0∞) : EReal) := by
        refine le_iInf₂ fun y hy => ?_
        have h1 : ENNReal.ofReal a ≤ In n y := ((hthick y hy).trans_le (hle n y)).le
        have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
        rwa [EReal.coe_ennreal_ofReal, max_eq_left ha0.le] at h2
      have hlt : limsup (fun ε : ℝ => ((id ε : ℝ) : EReal) * ENNReal.log (P.map (Zn n ε) C))
          (𝓝[>] 0) < r₁ := by
        refine hup.trans_lt ((EReal.neg_le_neg_iff.mpr hinf).trans_lt ?_)
        rw [← EReal.coe_neg]; exact_mod_cast hr₁a
      filter_upwards [self_mem_nhdsWithin, eventually_lt_of_limsup_lt hlt, hn n le_rfl,
        hlog2.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r - r₁))]
        with ε (hε : 0 < ε) h1 h2 h3
      have hsub : Z ε ⁻¹' A ⊆ Zn n ε ⁻¹' C ∪ {ω | δ < dist (Zn n ε ω) (Z ε ω)} := by
        intro ω hω
        by_cases hd : δ < dist (Zn n ε ω) (Z ε ω)
        · exact Or.inr hd
        · exact Or.inl (mem_cthickening_of_dist_le _ _ _ _ (subset_closure hω) (not_lt.mp hd))
      have hP1 : P (Zn n ε ⁻¹' C) ≤ ENNReal.ofReal (Real.exp (r₁ / ε)) := by
        rw [← Measure.map_apply (hZn n ε) hCm]
        exact le_exp_of_mul_log_le hε h1.le
      have hP2 := le_exp_of_mul_log_le hε h2
      have htot : P (Z ε ⁻¹' A) ≤ ENNReal.ofReal (Real.exp ((r₁ + ε * Real.log 2) / ε)) := by
        calc P (Z ε ⁻¹' A) ≤ P (Zn n ε ⁻¹' C) + P {ω | δ < dist (Zn n ε ω) (Z ε ω)} :=
              (measure_mono hsub).trans (measure_union_le _ _)
          _ ≤ ENNReal.ofReal (Real.exp (r₁ / ε)) + ENNReal.ofReal (Real.exp (r₁ / ε)) :=
              add_le_add hP1 hP2
          _ = ENNReal.ofReal (Real.exp ((r₁ + ε * Real.log 2) / ε)) := by
              rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
              congr 1
              rw [add_div, Real.exp_add, mul_div_cancel_left₀ _ hε.ne',
                Real.exp_log two_pos]
              ring
      refine (mul_log_le_of_le_exp hε htot).trans ?_
      exact_mod_cast (by linarith : r₁ + ε * Real.log 2 ≤ r)
  · -- lower bound
    have hmap : (fun ε : ℝ => ((id ε : ℝ) : EReal) * ENNReal.log (P.map (Z ε) G)) =
        fun ε : ℝ => (ε : EReal) * ENNReal.log (P (Z ε ⁻¹' G)) := by
      funext ε; rw [Measure.map_apply (hZ ε) hG]; rfl
    rw [hmap, EReal.neg_le]
    refine le_iInf₂ fun x hx => ?_
    rw [EReal.neg_le]
    by_cases hIx : I x = ⊤
    · simp [hIx]
    rw [← EReal.coe_ennreal_toReal hIx, ← EReal.coe_neg]
    refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    induction b using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hb not_top_lt
    | coe r =>
      have hr : r < -(I x).toReal := by exact_mod_cast hb
      obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
      set δ := δ₀ / 2 with hδ
      have hδpos : 0 < δ := half_pos hδ₀
      set r₁ := (r + -(I x).toReal) / 2 with hr₁
      have hrr₁ : r < r₁ := by rw [hr₁]; linarith
      have hr₁I : r₁ < -(I x).toReal := by rw [hr₁]; linarith
      obtain ⟨n₁, hn₁⟩ := happ x hIx δ hδpos
      obtain ⟨n₂, hn₂⟩ := hexp δ hδpos (r₁ - 1)
      set n := max n₁ n₂
      obtain ⟨y, hy, hIny⟩ := hn₁ n (le_max_left _ _)
      have hyU : y ∈ ball x δ := mem_ball.mpr hy
      have hlow := (hLDP n).2.2 (ball x δ) isOpen_ball.measurableSet
      rw [isOpen_ball.interior_eq] at hlow
      have hinf : (⨅ z ∈ ball x δ, ((In n z : ℝ≥0∞) : EReal)) ≤ ((I x : ℝ≥0∞) : EReal) :=
        iInf₂_le_of_le y hyU (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hIny)
      have hlt : (r₁ : EReal) < liminf (fun ε : ℝ => ((id ε : ℝ) : EReal) *
          ENNReal.log (P.map (Zn n ε) (ball x δ))) (𝓝[>] 0) := by
        refine lt_of_lt_of_le ?_ ((EReal.neg_le_neg_iff.mpr hinf).trans hlow)
        rw [← EReal.coe_ennreal_toReal hIx, ← EReal.coe_neg]
        exact_mod_cast hr₁I
      have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * Real.log 2 < min (r₁ - r) 1 :=
        hlog2.eventually (gt_mem_nhds (lt_min (by linarith) one_pos))
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [self_mem_nhdsWithin, eventually_lt_of_lt_liminf hlt,
        hn₂ n (le_max_right _ _), hsmall] with ε (hε : 0 < ε) h1 h2 h3
      have hq : ENNReal.ofReal (Real.exp (r₁ / ε)) ≤ P (Zn n ε ⁻¹' ball x δ) := by
        rw [← Measure.map_apply (hZn n ε) isOpen_ball.measurableSet]
        exact exp_le_of_le_mul_log hε h1.le
      have hd := le_exp_of_mul_log_le hε h2
      have hsub : Zn n ε ⁻¹' ball x δ ⊆ Z ε ⁻¹' G ∪ {ω | δ < dist (Zn n ε ω) (Z ε ω)} := by
        intro ω hω
        by_cases hdω : δ < dist (Zn n ε ω) (Z ε ω)
        · exact Or.inr hdω
        · left
          show Z ε ω ∈ G
          refine interior_subset (hball (mem_ball.mpr ?_))
          have h1' : dist (Zn n ε ω) x < δ := mem_ball.mp hω
          calc dist (Z ε ω) x ≤ dist (Z ε ω) (Zn n ε ω) + dist (Zn n ε ω) x := dist_triangle _ _ _
            _ < δ + δ := by rw [dist_comm]; linarith [not_lt.mp hdω]
            _ = δ₀ := by rw [hδ]; ring
      set e₁ := Real.exp (r₁ / ε) with he₁
      set e₂ := Real.exp ((r₁ - 1) / ε) with he₂
      have he₂le : e₂ ≤ e₁ / 2 := by
        have h4 : e₂ = e₁ * Real.exp (-1 / ε) := by
          rw [he₁, he₂, ← Real.exp_add]; congr 1; ring
        have h5 : Real.exp (-1 / ε) ≤ 1 / 2 := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
          refine Real.exp_le_exp.mpr ?_
          rw [div_le_iff₀ hε, one_div, Real.log_inv]
          linarith [min_le_right (r₁ - r) 1]
        rw [h4]
        nlinarith [Real.exp_pos (r₁ / ε)]
      have hPG : ENNReal.ofReal (e₁ - e₂) ≤ P (Z ε ⁻¹' G) := by
        rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, tsub_le_iff_right]
        calc ENNReal.ofReal e₁ ≤ P (Zn n ε ⁻¹' ball x δ) := hq
          _ ≤ P (Z ε ⁻¹' G) + P {ω | δ < dist (Zn n ε ω) (Z ε ω)} :=
              (measure_mono hsub).trans (measure_union_le _ _)
          _ ≤ P (Z ε ⁻¹' G) + ENNReal.ofReal e₂ := add_le_add le_rfl hd
      have hhalf : ENNReal.ofReal (Real.exp ((r₁ - ε * Real.log 2) / ε)) ≤ P (Z ε ⁻¹' G) := by
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hPG
        have : Real.exp ((r₁ - ε * Real.log 2) / ε) = e₁ / 2 := by
          rw [sub_div, Real.exp_sub, mul_div_cancel_left₀ _ hε.ne', Real.exp_log two_pos]
        linarith
      refine le_trans ?_ (le_mul_log_of_exp_le hε hhalf)
      exact_mod_cast (by linarith [min_le_left (r₁ - r) 1] : r ≤ r₁ - ε * Real.log 2)

end powerlib.Stochastic.LDP
