import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.LargeDeviations

/-! # Large deviations: the principle as a predicate, good rate functions, contraction

The large-deviation principle of `theorem/Stochastic/LargeDeviations.lean` (written out there in
the statement of `dirac_satisfiesLDP`) as a predicate `IsLDP` on a family of measures indexed by
an arbitrary filter, and its transport by continuous maps (the contraction principle).

Scope.
* Probability theory, not an engineering result; arbitrary topological spaces with a measurable
  structure (Borel sets where measurability of a continuous map is needed).
* The index is an arbitrary filter `l` on a type `ι` with a speed `s : ι → ℝ`; the principle
  of `LargeDeviations.lean` is the case `l = 𝓝[>] 0`, `s = id` (`isLDP_dirac`). Bounds are stated
  for measurable sets and the rate function is lower semicontinuous, as there.

Source: work-sync theory/T-large-deviations.md (LDP with rate `I`, upper bound over `cl A`, lower
bound over `int A`); A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*,
2nd ed. (1998), §1.2 (good rate functions) and Thm 4.2.1 (contraction principle).

Results.
* `IsLDP`, `IsGoodRate` (compact sublevel sets at every finite level), `pushRate`
  (`I_F(y) = inf {I(x) : F x = y}`); `isLDP_dirac` (the point-mass instance, from
  `dirac_satisfiesLDP`); `IsLDP.congr` (only the eventual family matters);
  `mul_log_le_of_le_exp`, `le_mul_log_of_exp_le`, `le_exp_of_mul_log_le`, `exp_le_of_le_mul_log`
  (`ε log p ≤ y ⇔ p ≤ e^{y/ε}` and `y ≤ ε log p ⇔ e^{y/ε} ≤ p` for `ε > 0`).
* `pushRate_le`, `pushRate_eq_of_leftInverse` (with a left inverse `G`, `I_F(y) = I(G y)` on the
  range of `F` and `∞` off it).
* `isGoodRate_pushRate`, `lowerSemicontinuous_pushRate`: a good lower semicontinuous rate is
  pushed forward by a continuous map into a Hausdorff space to a good lower semicontinuous rate
  (the infimum is attained, `{I_F ≤ a} = F '' {I ≤ a}`);
  `lowerSemicontinuous_pushRate_of_leftInverse`: no goodness is needed when `F` has a continuous
  left inverse.
* **Contraction principle**: `IsLDP.map_upper`, `IsLDP.map_lower` (the two bounds transport for
  every continuous `F`, no goodness needed), `IsLDP.map` (good rate, Dembo–Zeitouni Thm 4.2.1)
  and `IsLDP.map_of_leftInverse` (continuous left inverse): the image laws `P_i ∘ F⁻¹` satisfy
  the principle with rate `pushRate F I`.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology
open scoped ENNReal Classical

variable {ι X Y : Type*}

/-- **Large-deviation principle** along the filter `l` with speed `s`: the rate `I` is lower
semicontinuous and, for every measurable `A`,
`limsup_l s log P(A) ≤ −inf_{cl A} I` and `−inf_{int A} I ≤ liminf_l s log P(A)`. -/
def IsLDP [TopologicalSpace X] [MeasurableSpace X] (l : Filter ι) (s : ι → ℝ)
    (P : ι → Measure X) (I : X → ℝ≥0∞) : Prop :=
  LowerSemicontinuous I ∧
    (∀ A : Set X, MeasurableSet A →
      limsup (fun i => (s i : EReal) * ENNReal.log (P i A)) l ≤
        -(⨅ x ∈ closure A, ((I x : ℝ≥0∞) : EReal))) ∧
    (∀ A : Set X, MeasurableSet A →
      -(⨅ x ∈ interior A, ((I x : ℝ≥0∞) : EReal)) ≤
        liminf (fun i => (s i : EReal) * ENNReal.log (P i A)) l)

/-- **Good rate function**: every sublevel set `{I ≤ a}`, `a < ∞`, is compact. -/
def IsGoodRate [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop :=
  ∀ a : ℝ≥0∞, a ≠ ⊤ → IsCompact (I ⁻¹' Iic a)

/-- **Pushed-forward rate** `I_F(y) = inf {I(x) : F x = y}` (`∞` off the range of `F`). -/
def pushRate (F : X → Y) (I : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ := ⨅ (x) (_ : F x = y), I x

/-- The principle depends on the family only eventually along `l`. -/
@[tmio T, powerlib_foundation] theorem IsLDP.congr [TopologicalSpace X] [MeasurableSpace X]
    {l : Filter ι} {s : ι → ℝ} {P Q : ι → Measure X} {I : X → ℝ≥0∞} (h : IsLDP l s P I)
    (hPQ : ∀ᶠ i in l, P i = Q i) : IsLDP l s Q I := by
  refine ⟨h.1, fun A hA => ?_, fun A hA => ?_⟩
  · rw [limsup_congr (u := fun i => (s i : EReal) * ENNReal.log (Q i A))
      (v := fun i => (s i : EReal) * ENNReal.log (P i A)) (hPQ.mono fun i hi => by rw [hi])]
    exact h.2.1 A hA
  · rw [liminf_congr (u := fun i => (s i : EReal) * ENNReal.log (Q i A))
      (v := fun i => (s i : EReal) * ENNReal.log (P i A)) (hPQ.mono fun i hi => by rw [hi])]
    exact h.2.2 A hA

/-- The principle of `LargeDeviations.lean` is the case `l = 𝓝[>] 0`, `s = id`: the point mass
`δ_{x₀}` satisfies it with rate `diracRate x₀`. -/
@[tmio T, powerlib_foundation] theorem isLDP_dirac {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (x₀ : E) :
    IsLDP (𝓝[>] (0 : ℝ)) id (fun _ => Measure.dirac x₀) (diracRate x₀) :=
  dirac_satisfiesLDP x₀

@[tmio T, powerlib_foundation] theorem pushRate_le (F : X → Y) (I : X → ℝ≥0∞) (x : X) :
    pushRate F I (F x) ≤ I x := by
  unfold pushRate
  exact iInf₂_le (f := fun x' (_ : F x' = F x) => I x') x rfl

/-- With a left inverse `G` (`G (F x) = x`), the pushed rate is `I ∘ G` on the range of `F` and
`∞` off it. -/
@[tmio T, powerlib_foundation] theorem pushRate_eq_of_leftInverse {F : X → Y} {G : Y → X}
    (hG : ∀ x, G (F x) = x) (I : X → ℝ≥0∞) (y : Y) :
    pushRate F I y = if F (G y) = y then I (G y) else ⊤ := by
  unfold pushRate
  split_ifs with h
  · refine le_antisymm (iInf₂_le (G y) h) (le_iInf₂ fun x hx => ?_)
    rw [← hx, hG]
  · refine le_antisymm le_top (le_iInf₂ fun x hx => ?_)
    exact absurd (by rw [← hx, hG]) h

/-- An extended-real lower bound for every member of a family bounds the coerced infimum. -/
@[tmio T, powerlib_foundation] private theorem le_coe_biInf {α : Type*} {L : EReal}
    (h0 : 0 ≤ L) {p : α → Prop} {f : α → ℝ≥0∞} (h : ∀ a, p a → L ≤ f a) :
    L ≤ ((⨅ (a) (_ : p a), f a : ℝ≥0∞) : EReal) := by
  rw [← EReal.coe_toENNReal h0, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine le_iInf₂ fun a ha => ?_
  have := EReal.toENNReal_le_toENNReal (h a ha)
  rwa [EReal.toENNReal_coe] at this

/-! ## Bounds on probabilities and bounds on `ε log P` -/

/-- `p ≤ e^{y/ε}` gives `ε log p ≤ y` (`ε > 0`). -/
@[tmio T, powerlib_foundation] theorem mul_log_le_of_le_exp {ε y : ℝ} (hε : 0 < ε)
    {p : ℝ≥0∞} (h : p ≤ ENNReal.ofReal (Real.exp (y / ε))) :
    (ε : EReal) * ENNReal.log p ≤ y := by
  have hε' : (0 : EReal) ≤ ε := by exact_mod_cast hε.le
  calc (ε : EReal) * ENNReal.log p ≤ (ε : EReal) * ((y / ε : ℝ) : EReal) := by
        refine mul_le_mul_of_nonneg_left ?_ hε'
        refine (ENNReal.log_le_log h).trans_eq ?_
        rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    _ = y := by
        rw [← EReal.coe_mul]
        congr 1
        field_simp

/-- `e^{y/ε} ≤ p` gives `y ≤ ε log p` (`ε > 0`). -/
@[tmio T, powerlib_foundation] theorem le_mul_log_of_exp_le {ε y : ℝ} (hε : 0 < ε)
    {p : ℝ≥0∞} (h : ENNReal.ofReal (Real.exp (y / ε)) ≤ p) :
    (y : EReal) ≤ (ε : EReal) * ENNReal.log p := by
  have hε' : (0 : EReal) ≤ ε := by exact_mod_cast hε.le
  calc (y : EReal) = (ε : EReal) * ((y / ε : ℝ) : EReal) := by
        rw [← EReal.coe_mul]
        congr 1
        field_simp
    _ ≤ (ε : EReal) * ENNReal.log p := by
        refine mul_le_mul_of_nonneg_left ?_ hε'
        refine le_trans (le_of_eq ?_) (ENNReal.log_le_log h)
        rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]

/-- Converse: `ε log p ≤ y` gives `p ≤ e^{y/ε}` (`ε > 0`). -/
@[tmio T, powerlib_foundation] theorem le_exp_of_mul_log_le {ε y : ℝ} (hε : 0 < ε)
    {p : ℝ≥0∞} (h : (ε : EReal) * ENNReal.log p ≤ y) :
    p ≤ ENNReal.ofReal (Real.exp (y / ε)) := by
  rcases eq_or_ne p 0 with rfl | h0
  · exact zero_le
  rcases eq_or_ne p ⊤ with rfl | htop
  · rw [ENNReal.log_top, EReal.mul_top_of_pos (by exact_mod_cast hε)] at h
    exact absurd h (by simp)
  rw [ENNReal.log_pos_real h0 htop, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h
  rw [← ENNReal.ofReal_toReal htop]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_log (ENNReal.toReal_pos h0 htop)]
  refine Real.exp_le_exp.mpr ?_
  rw [le_div_iff₀ hε]
  linarith

/-- Converse: `y ≤ ε log p` gives `e^{y/ε} ≤ p` (`ε > 0`). -/
@[tmio T, powerlib_foundation] theorem exp_le_of_le_mul_log {ε y : ℝ} (hε : 0 < ε)
    {p : ℝ≥0∞} (h : (y : EReal) ≤ (ε : EReal) * ENNReal.log p) :
    ENNReal.ofReal (Real.exp (y / ε)) ≤ p := by
  rcases eq_or_ne p 0 with rfl | h0
  · rw [ENNReal.log_zero, EReal.mul_bot_of_pos (by exact_mod_cast hε)] at h
    exact absurd h (by simp)
  rcases eq_or_ne p ⊤ with rfl | htop
  · exact le_top
  rw [ENNReal.log_pos_real h0 htop, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h
  rw [← ENNReal.ofReal_toReal htop]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_log (ENNReal.toReal_pos h0 htop)]
  refine Real.exp_le_exp.mpr ?_
  rw [div_le_iff₀ hε]
  linarith

/-! ## Transport of the bounds -/

variable [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]

/-- **Upper bound transported** by a continuous map (no goodness needed):
`limsup s log P_i(F⁻¹ A) ≤ −inf_{cl A} I_F`. -/
@[tmio T, powerlib_foundation] theorem IsLDP.map_upper [OpensMeasurableSpace X] [BorelSpace Y]
    {l : Filter ι} {s : ι → ℝ} {P : ι → Measure X} {I : X → ℝ≥0∞} (h : IsLDP l s P I)
    {F : X → Y} (hF : Continuous F) (A : Set Y) (hA : MeasurableSet A) :
    limsup (fun i => (s i : EReal) * ENNReal.log ((P i).map F A)) l ≤
      -(⨅ y ∈ closure A, ((pushRate F I y : ℝ≥0∞) : EReal)) := by
  simp only [Measure.map_apply hF.measurable hA]
  refine (h.2.1 _ (hF.measurable hA)).trans (EReal.neg_le_neg_iff.mpr ?_)
  refine le_iInf₂ fun x hx => iInf₂_le_of_le (F x) (hF.closure_preimage_subset A hx) ?_
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (pushRate_le F I x)

/-- **Lower bound transported** by a continuous map (no goodness needed):
`−inf_{int A} I_F ≤ liminf s log P_i(F⁻¹ A)`. -/
@[tmio T, powerlib_foundation] theorem IsLDP.map_lower [OpensMeasurableSpace X] [BorelSpace Y]
    {l : Filter ι} {s : ι → ℝ} {P : ι → Measure X} {I : X → ℝ≥0∞} (h : IsLDP l s P I)
    {F : X → Y} (hF : Continuous F) (A : Set Y) (hA : MeasurableSet A) :
    -(⨅ y ∈ interior A, ((pushRate F I y : ℝ≥0∞) : EReal)) ≤
      liminf (fun i => (s i : EReal) * ENNReal.log ((P i).map F A)) l := by
  simp only [Measure.map_apply hF.measurable hA]
  refine le_trans (EReal.neg_le_neg_iff.mpr ?_) (h.2.2 _ (hF.measurable hA))
  refine le_iInf₂ fun y hy => le_coe_biInf (le_iInf₂ fun _ _ => EReal.coe_ennreal_nonneg _)
    fun x hx => iInf₂_le_of_le x ?_ le_rfl
  exact preimage_interior_subset_interior_preimage hF (by simpa [mem_preimage, hx] using hy)

/-! ## Lower semicontinuity and goodness of the pushed rate -/

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The infimum defining `I_F(y)` is attained when `I` is good and lower semicontinuous, so
`{I_F ≤ a} = F '' {I ≤ a}` for every finite `a`. -/
@[tmio T, powerlib_foundation] theorem pushRate_preimage_Iic [T1Space Y] {I : X → ℝ≥0∞}
    (hI : IsGoodRate I) (hlsc : LowerSemicontinuous I) {F : X → Y} (hF : Continuous F)
    {a : ℝ≥0∞} (ha : a ≠ ⊤) : pushRate F I ⁻¹' Iic a = F '' (I ⁻¹' Iic a) := by
  ext y
  simp only [mem_preimage, mem_Iic, mem_image]
  constructor
  · intro hy
    have ha1 : a < a + 1 := ENNReal.lt_add_right ha one_ne_zero
    set K := F ⁻¹' {y} ∩ I ⁻¹' Iic (a + 1) with hK
    have hKc : IsCompact K :=
      (hI (a + 1) (ENNReal.add_ne_top.mpr ⟨ha, ENNReal.one_ne_top⟩)).inter_left
        (isClosed_singleton.preimage hF)
    obtain ⟨x₁, hx₁⟩ : ∃ x, F x = y ∧ I x < a + 1 := by
      have : pushRate F I y < a + 1 := hy.trans_lt ha1
      simp only [pushRate, iInf_lt_iff] at this
      obtain ⟨x, hx, hlt⟩ := this
      exact ⟨x, hx, hlt⟩
    have hKne : K.Nonempty := ⟨x₁, hx₁.1, hx₁.2.le⟩
    obtain ⟨x, hxK, hmin⟩ := (hlsc.lowerSemicontinuousOn K).exists_isMinOn hKne hKc
    refine ⟨x, ?_, hxK.1⟩
    by_contra hgt
    push Not at hgt
    have : pushRate F I y < I x := hy.trans_lt hgt
    simp only [pushRate, iInf_lt_iff] at this
    obtain ⟨x', hx', hlt⟩ := this
    have hx'K : x' ∈ K := ⟨hx', (hlt.trans_le (hxK.2 : I x ≤ a + 1)).le⟩
    exact absurd (hmin hx'K) (not_le.mpr hlt)
  · rintro ⟨x, hx, rfl⟩
    exact (pushRate_le F I x).trans hx

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- **Goodness is pushed forward**: `{I_F ≤ a}` is the continuous image of the compact
`{I ≤ a}`. -/
@[tmio T, powerlib_foundation] theorem isGoodRate_pushRate [T1Space Y] {I : X → ℝ≥0∞}
    (hI : IsGoodRate I) (hlsc : LowerSemicontinuous I) {F : X → Y} (hF : Continuous F) :
    IsGoodRate (pushRate F I) := fun a ha => by
  rw [pushRate_preimage_Iic hI hlsc hF ha]
  exact (hI a ha).image hF

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- **Lower semicontinuity is pushed forward** for a good rate into a Hausdorff space. -/
@[tmio T, powerlib_foundation] theorem lowerSemicontinuous_pushRate [T2Space Y]
    {I : X → ℝ≥0∞} (hI : IsGoodRate I) (hlsc : LowerSemicontinuous I) {F : X → Y}
    (hF : Continuous F) : LowerSemicontinuous (pushRate F I) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.mpr fun a => ?_
  by_cases ha : a = ⊤
  · subst ha; simp
  · exact (isGoodRate_pushRate hI hlsc hF a ha).isClosed

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- **Lower semicontinuity without goodness**: if `F` has a continuous left inverse `G`, then
`{I_F ≤ a} = {y | F (G y) = y} ∩ G⁻¹ {I ≤ a}` is closed. -/
@[tmio T, powerlib_foundation] theorem lowerSemicontinuous_pushRate_of_leftInverse [T2Space Y]
    {I : X → ℝ≥0∞} (hlsc : LowerSemicontinuous I) {F : X → Y} {G : Y → X} (hF : Continuous F)
    (hGc : Continuous G) (hG : ∀ x, G (F x) = x) : LowerSemicontinuous (pushRate F I) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.mpr fun a => ?_
  by_cases ha : a = ⊤
  · subst ha; simp
  have e : pushRate F I ⁻¹' Iic a = {y | F (G y) = y} ∩ G ⁻¹' (I ⁻¹' Iic a) := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_inter_iff, mem_ofPred_eq,
      pushRate_eq_of_leftInverse hG I y]
    split_ifs with h
    · exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
    · exact ⟨fun h' => absurd (top_le_iff.mp h') ha, fun h' => absurd h'.1 h⟩
  rw [e]
  exact (isClosed_eq (hF.comp hGc) continuous_id).inter
    ((hlsc.isClosed_preimage a).preimage hGc)

/-! ## The contraction principle -/

/-- **Contraction principle** (Dembo–Zeitouni Thm 4.2.1): if `P_i` satisfies the principle with a
good rate `I` and `F` is continuous into a Hausdorff space, the image laws `P_i ∘ F⁻¹` satisfy it
with the rate `I_F(y) = inf {I(x) : F x = y}`. -/
@[tmio T, powerlib_foundation] theorem IsLDP.map [OpensMeasurableSpace X] [T2Space Y]
    [BorelSpace Y] {l : Filter ι} {s : ι → ℝ} {P : ι → Measure X} {I : X → ℝ≥0∞}
    (h : IsLDP l s P I) (hI : IsGoodRate I) {F : X → Y} (hF : Continuous F) :
    IsLDP l s (fun i => (P i).map F) (pushRate F I) :=
  ⟨lowerSemicontinuous_pushRate hI h.1 hF, h.map_upper hF, h.map_lower hF⟩

/-- **Contraction principle with a continuous left inverse** (no goodness needed): if `G` is
continuous with `G (F x) = x`, the image laws `P_i ∘ F⁻¹` satisfy the principle with the rate
`pushRate F I` (`= I ∘ G` on the range of `F`, `∞` off it). -/
@[tmio T, powerlib_foundation] theorem IsLDP.map_of_leftInverse [OpensMeasurableSpace X]
    [T2Space Y] [BorelSpace Y] {l : Filter ι} {s : ι → ℝ} {P : ι → Measure X}
    {I : X → ℝ≥0∞} (h : IsLDP l s P I) {F : X → Y} {G : Y → X} (hF : Continuous F)
    (hGc : Continuous G) (hG : ∀ x, G (F x) = x) :
    IsLDP l s (fun i => (P i).map F) (pushRate F I) :=
  ⟨lowerSemicontinuous_pushRate_of_leftInverse h.1 hF hGc hG, h.map_upper hF, h.map_lower hF⟩

end powerlib.Stochastic.LDP
