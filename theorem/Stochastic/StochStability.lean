import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.ODE.Gronwall

/-! # Stochastic stability notions, moment Lyapunov exponents and the a.s. exponent bound

Source: work-sync `theory/T-lyapunov-stability-stochastic.md` §1.1 (three stability notions),
§1.2 (`L V ≤ −c V ⇒ E V(X_t) ≤ V(X₀) e^{−ct}`, "by Itô + Gronwall"), §1.3 (`Λ(p) = limsup (1/t)
log E‖X_t‖^p` is convex in `p`), §1.4 (`λ_a.s. ≤ Λ(p)/p`).

Scope (Rules §3).  The process is an arbitrary family of random variables `X : T → Ω → E`
(continuous or discrete time); no SDE is involved.  The stability notions are definitions; the
theorems are measure-theoretic or ODE facts.  The Itô step of §1.2 (`d/dt E V(X_t) =
E LV(X_t)`) is **not** formalized: only the deterministic Gronwall step from
`m' ≤ −c m` is (wrapper of Mathlib `le_gronwallBound_of_liminf_deriv_right_le`).  Foundation
results, not a stability theorem for a particular power system.

Main results.
* Definitions `StableInProbability`, `ASAttractive`, `ASAsymptoticallyStable` (= stable in
  probability **and** a.s. attractive), `MomentStable`.
* Correction (§1.1): the note defines a.s. stability by attractivity alone.
  `attractive_not_stableInProbability`: a (deterministic) family whose every member tends to `0`
  but with unit excursions from arbitrarily small initial states — attractivity does not give
  stability in probability, so the standard a.s. asymptotic stability needs both halves.
* `moment_exp_decay` (§1.2, Gronwall step).
* `moment_holder`, `moment_growth_convex` (§1.3): `E f^{θp+(1−θ)q} ≤ (E f^p)^θ (E f^q)^{1−θ}`
  (Lyapunov's inequality, from Mathlib's Hölder `ENNReal.lintegral_mul_le_Lp_mul_Lq`); hence
  exponential growth bounds of moments are convex in `p` — the content of "`Λ(p)` is convex"
  (stated with eventual bounds, which avoids `limsup` arithmetic in `EReal`).
* `as_exponent_le` (§1.4, discrete time): if `E‖X_n‖^p ≤ e^{an}` eventually, then almost surely
  `‖X_n‖ ≤ e^{γn}` eventually for every rational `γ > a/p` — i.e. `λ_a.s. ≤ Λ(p)/p` (Markov's
  inequality + first Borel–Cantelli lemma).

The explicit GBM example where `λ_as < 0 < Λ(2)/2` (a.s. stable, second-moment unstable) is
`GBMSeparation.lean`.
-/

noncomputable section
namespace powerlib.Stochastic.StochStab

open MeasureTheory Filter Real Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Stability notions -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] {S : Type*} [Norm S]

/-- **Stability in probability** of the zero solution for a family `X x₀` of processes indexed
by the initial state: small initial states keep the whole path in a ball with high probability. -/
def StableInProbability (P : Measure Ω) (X : S → ℝ≥0 → Ω → E) : Prop :=
  ∀ ε > (0 : ℝ≥0∞), ∀ r > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x₀ : S, ‖x₀‖ < δ →
    P {ω | ∃ t, r ≤ ‖X x₀ t ω‖} ≤ ε

/-- **Almost-sure attractivity** of the path started at `x₀`. -/
def ASAttractive (P : Measure Ω) (X : S → ℝ≥0 → Ω → E) (x₀ : S) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun t => X x₀ t ω) atTop (𝓝 0)

/-- **Almost-sure asymptotic stability** (Khasminskii / Mao): stable in probability and a.s.
attractive for all small initial states. -/
def ASAsymptoticallyStable (P : Measure Ω) (X : S → ℝ≥0 → Ω → E) : Prop :=
  StableInProbability P X ∧ ∃ δ > (0 : ℝ), ∀ x₀ : S, ‖x₀‖ < δ → ASAttractive P X x₀

/-- **`p`-th moment stability**: `E‖X_t‖^p → 0`. -/
def MomentStable (P : Measure Ω) (X : S → ℝ≥0 → Ω → E) (p : ℝ) (x₀ : S) : Prop :=
  Tendsto (fun t => ∫⁻ ω, ‖X x₀ t ω‖ₑ ^ p ∂P) atTop (𝓝 0)

end Defs

/-- Unit bump `t e^{1−t}` (peak `1` at `t = 1`, tends to `0`). -/
def bump (t : ℝ) : ℝ := t * exp (1 - t)

@[powerlib_foundation] theorem bump_one : bump 1 = 1 := by simp [bump]

@[powerlib_foundation] theorem bump_tendsto : Tendsto bump atTop (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have : bump = fun t => exp 1 * (t ^ 1 * exp (-t)) := by
    funext t; simp only [bump, pow_one]; rw [sub_eq_add_neg, exp_add]; ring
  rw [this]
  simpa using h.const_mul (exp 1)

/-- **Correction (§1.1)**: attractivity does not imply stability in probability.  The
deterministic family `X x₀ t = bump t` for `x₀ ≠ 0` (and `0` for `x₀ = 0`) is a.s. attractive for
every initial state, but every nonzero initial state produces an excursion of size `1`. -/
@[powerlib_foundation] theorem attractive_not_stableInProbability [IsProbabilityMeasure P] :
    let X : ℝ → ℝ≥0 → Ω → ℝ := fun x₀ t _ => if x₀ = 0 then 0 else bump t
    (∀ x₀, ASAttractive P X x₀) ∧ ¬ StableInProbability P X := by
  intro X
  constructor
  · intro x₀
    refine Eventually.of_forall fun ω => ?_
    by_cases h : x₀ = 0
    · simp [X, h]
    · simp only [X, h, ↓reduceIte]
      exact bump_tendsto.comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  · intro hs
    obtain ⟨δ, hδ, hδX⟩ := hs (1 / 2) (by norm_num) (1 / 2) (by norm_num)
    have h := hδX (δ / 2) (by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith)
    have hne : δ / 2 ≠ 0 := by positivity
    have hall : {ω | ∃ t : ℝ≥0, (1 / 2 : ℝ) ≤ ‖X (δ / 2) t ω‖} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      refine ⟨1, ?_⟩
      simp only [X, hne, ↓reduceIte, NNReal.coe_one, bump_one, norm_one]
      norm_num
    rw [hall, measure_univ] at h
    norm_num at h

/-! ## Gronwall step (§1.2) -/

/-- **Exponential decay of a moment** (deterministic Gronwall step): if `m` is continuous on
`[0, T]`, right-differentiable with `m' ≤ −c m`, then `m(t) ≤ m(0) e^{−ct}` (Mathlib
`le_gronwallBound_of_liminf_deriv_right_le`). -/
@[powerlib_foundation] theorem moment_exp_decay {m m' : ℝ → ℝ} {c T : ℝ}
    (hcont : ContinuousOn m (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt m (m' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 T, m' t ≤ -c * m t) :
    ∀ t ∈ Icc 0 T, m t ≤ m 0 * exp (-c * t) := by
  intro t ht
  have := le_gronwallBound_of_liminf_deriv_right_le (K := -c) (ε := 0) hcont
    (fun x hx r hr => (hderiv x hx).liminf_right_slope_le hr) le_rfl
    (fun x hx => by rw [add_zero]; exact hbound x hx) t ht
  rwa [gronwallBound_ε0, sub_zero] at this

/-! ## Moment Lyapunov exponents: convexity (§1.3) -/

/-- **Lyapunov's inequality** (Hölder): for `f ≥ 0`, `θ ∈ (0, 1)`, `p, q ≥ 0`,
`∫ f^{θp+(1−θ)q} ≤ (∫ f^p)^θ (∫ f^q)^{1−θ}`. -/
@[powerlib_foundation] theorem moment_holder {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {θ p q : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∫⁻ ω, f ω ^ (θ * p + (1 - θ) * q) ∂P ≤
      (∫⁻ ω, f ω ^ p ∂P) ^ θ * (∫⁻ ω, f ω ^ q ∂P) ^ (1 - θ) := by
  have hpq : (1 / θ).HolderConjugate (1 / (1 - θ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [lt_div_iff₀ hθ0]; linarith, by field_simp; ring⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (f := fun ω => f ω ^ (θ * p))
    (g := fun ω => f ω ^ ((1 - θ) * q)) (hf.pow_const _) (hf.pow_const _)
  have e1 : ∀ ω, f ω ^ (θ * p + (1 - θ) * q) = f ω ^ (θ * p) * f ω ^ ((1 - θ) * q) := by
    intro ω
    rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by nlinarith)]
  have e2 : ∀ ω, (f ω ^ (θ * p)) ^ (1 / θ) = f ω ^ p := by
    intro ω; rw [← ENNReal.rpow_mul]; congr 1; field_simp
  have e3 : ∀ ω, (f ω ^ ((1 - θ) * q)) ^ (1 / (1 - θ)) = f ω ^ q := by
    intro ω; rw [← ENNReal.rpow_mul]; congr 1; field_simp [(by linarith : (1 - θ) ≠ 0)]
  simp_rw [e1]
  simp_rw [e2, e3] at h
  simpa [one_div, inv_inv] using h

/-- **Convexity of moment growth rates (§1.3)**: if `E‖X_t‖^p ≤ e^{at}` and `E‖X_t‖^q ≤ e^{bt}`
eventually, then `E‖X_t‖^{θp+(1−θ)q} ≤ e^{(θa+(1−θ)b)t}` eventually; i.e. `Λ(θp+(1−θ)q) ≤
θΛ(p) + (1−θ)Λ(q)`. -/
@[powerlib_foundation] theorem moment_growth_convex {ι : Type*} {l : Filter ι}
    {F : ι → Ω → ℝ≥0∞} (hF : ∀ i, AEMeasurable (F i) P) {θ p q a b : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) {τ : ι → ℝ}
    (hpa : ∀ᶠ i in l, ∫⁻ ω, F i ω ^ p ∂P ≤ ENNReal.ofReal (exp (a * τ i)))
    (hqb : ∀ᶠ i in l, ∫⁻ ω, F i ω ^ q ∂P ≤ ENNReal.ofReal (exp (b * τ i))) :
    ∀ᶠ i in l, ∫⁻ ω, F i ω ^ (θ * p + (1 - θ) * q) ∂P ≤
      ENNReal.ofReal (exp ((θ * a + (1 - θ) * b) * τ i)) := by
  filter_upwards [hpa, hqb] with i h1 h2
  refine le_trans (moment_holder (hF i) hθ0 hθ1 hp hq) ?_
  have e : ENNReal.ofReal (exp ((θ * a + (1 - θ) * b) * τ i)) =
      ENNReal.ofReal (exp (a * τ i)) ^ θ * ENNReal.ofReal (exp (b * τ i)) ^ (1 - θ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hθ0.le,
      ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by linarith), ← ENNReal.ofReal_mul (by positivity),
      ← exp_mul, ← exp_mul, ← exp_add]
    congr 2; ring
  rw [e]
  gcongr

/-! ## `λ_a.s. ≤ Λ(p)/p` in discrete time (§1.4) -/

/-- **Almost-sure exponent bound** (discrete time): if `E‖X_n‖^p ≤ e^{an}` for all large `n`
(`p > 0`), then almost surely, for every rational `γ > a/p`, `‖X_n‖ ≤ e^{γn}` for all large `n`
(so `limsup (1/n) log‖X_n‖ ≤ a/p`). -/
@[powerlib_foundation] theorem as_exponent_le {E : Type*} [NormedAddCommGroup E] {X : ℕ → Ω → E}
    (hX : ∀ n, AEStronglyMeasurable (X n) P) {p a : ℝ} (hp : 0 < p)
    (hmom : ∀ᶠ n in atTop, ∫⁻ ω, ‖X n ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal (exp (a * n))) :
    ∀ᵐ ω ∂P, ∀ γ : ℚ, a / p < γ → ∀ᶠ n in atTop, ‖X n ω‖ ≤ exp (γ * n) := by
  rw [ae_all_iff]
  intro γ
  by_cases hγ : a / p < γ
  · obtain ⟨N, hN⟩ := eventually_atTop.mp hmom
    -- exceedance events after `N`
    set s : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (exp (γ * n)) < ‖X n ω‖ₑ ∧ N ≤ n}
    set r : ℝ := exp (a - p * γ) with hr
    have hr0 : 0 ≤ r := (exp_pos _).le
    have hr1 : r < 1 := by
      rw [hr, Real.exp_lt_one_iff]
      have := (div_lt_iff₀ hp).mp hγ
      linarith
    have hs : ∀ n, P (s n) ≤ ENNReal.ofReal (r ^ n) := by
      intro n
      by_cases hn : N ≤ n
      · have hsub : s n ⊆ {ω | ENNReal.ofReal (exp (γ * n)) ^ p ≤ ‖X n ω‖ₑ ^ p} := by
          intro ω hω
          exact ENNReal.rpow_le_rpow hω.1.le hp.le
        have hpos : ENNReal.ofReal (exp (γ * n)) ^ p ≠ 0 := by
          rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hp.le]
          exact (ENNReal.ofReal_pos.mpr (rpow_pos_of_pos (exp_pos _) _)).ne'
        have hfin : ENNReal.ofReal (exp (γ * n)) ^ p ≠ ⊤ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hp.le]; exact ENNReal.ofReal_ne_top
        calc P (s n) ≤ P {ω | ENNReal.ofReal (exp (γ * n)) ^ p ≤ ‖X n ω‖ₑ ^ p} := measure_mono hsub
          _ ≤ (∫⁻ ω, ‖X n ω‖ₑ ^ p ∂P) / ENNReal.ofReal (exp (γ * n)) ^ p :=
              meas_ge_le_lintegral_div ((hX n).enorm.pow_const p) hpos hfin
          _ ≤ ENNReal.ofReal (exp (a * n)) / ENNReal.ofReal (exp (γ * n)) ^ p := by
              gcongr; exact hN n hn
          _ = ENNReal.ofReal (r ^ n) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hp.le,
                ← ENNReal.ofReal_div_of_pos (rpow_pos_of_pos (exp_pos _) _)]
              congr 1
              rw [← exp_mul, ← exp_sub, hr, ← exp_nat_mul]
              congr 1; ring
      · have : s n = ∅ := by ext ω; simp [s, hn]
        rw [this, measure_empty]; exact zero_le
    have hsum : ∑' n, P (s n) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hr0 n)
        (summable_geometric_of_lt_one hr0 hr1)]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω _
    filter_upwards [hω, eventually_ge_atTop N] with n hn hNn
    have h1 : ¬ (ENNReal.ofReal (exp (γ * n)) < ‖X n ω‖ₑ) := fun hA => hn ⟨hA, hNn⟩
    push Not at h1
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (exp_pos _).le).mp h1
  · exact Eventually.of_forall fun ω h => absurd h hγ

end powerlib.Stochastic.StochStab
