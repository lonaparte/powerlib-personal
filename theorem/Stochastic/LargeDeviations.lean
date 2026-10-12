import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Order.LiminfLimsup

/-! # Large deviations: definitions, Chernoff bound, Freidlin–Wentzell action, quasi-potential

Source: work-sync `theory/T-large-deviations.md` (LDP definition with rate function `I`, upper
bound over `cl A`, lower bound over `int A`; Cramér / Chernoff), `theory/T-freidlin-wentzell.md`
(action `S_{0T}(φ) = ½ ∫₀ᵀ ‖φ̇ − b(φ)‖²_{a(φ)⁻¹} dt`, `a = σσᵀ`), `theory/T-quasi-potential.md`
(`V_qp(x) = inf_{T, φ(0) ∈ 𝒜, φ(T) = x} S_{0T}(φ)`).

Foundation (probability / calculus of variations), not an engineering result.  No statement here
asserts that a particular diffusion satisfies an LDP (Freidlin–Wentzell's theorem is not
formalized); the action and the quasi-potential are deterministic variational objects.

Main results.
* `SatisfiesLDP`: large-deviation principle with speed `ε → 0⁺` for a family of measures on a
  topological space, with the bounds stated for **Borel** sets `A` and a **lower semicontinuous**
  rate function (the hypotheses the note leaves implicit); `dirac_satisfiesLDP`: the constant
  family `δ_{x₀}` satisfies it with rate `0` at `x₀` and `∞` elsewhere (non-vacuity check).
* `chernoff_bound` (wrapper of Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf`) and
  `chernoff_iid`: `P(Σ_{i<n} Xᵢ ≥ n a) ≤ (e^{−ta} M(t))ⁿ` for independent summands with common
  moment generating function — the exponential (Cramér) upper bound.
* `fwAction`, `fwAction_nonneg`: the Freidlin–Wentzell action for `C¹` paths with a positive
  definite diffusion matrix (the note's hypothesis "`a` invertible, `φ` absolutely continuous"
  is replaced by the explicit `C¹`/positive-definite class used here).
* `gradient_action_identity`, `gradient_action_ge`, `gradient_action_eq_iff`: for a gradient drift
  `b = −∇U` and unit diffusion, completing the square gives
  `S_{0T}(φ) = ½∫‖φ̇ − ∇U(φ)‖² + 2(U(φ(T)) − U(φ(0)))`, hence `S ≥ 2ΔU` with equality iff `φ`
  follows the reversed gradient flow; `quasiPotential_ge`: `V_qp(x) ≥ 2(U(x) − U(x_𝒜))`.

UNPROVED here: the matching upper bound `V_qp(x) ≤ 2(U(x) − U(x_𝒜))` (needs near-optimal paths
leaving the attractor in infinite time) and the Cramér lower bound.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Real Set Topology Matrix
open scoped ENNReal Classical

/-! ## LDP definition -/

/-- **Large-deviation principle** with speed `ε → 0⁺` and rate function `I` (Borel sets,
lower semicontinuous rate). -/
structure SatisfiesLDP {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (P : ℝ → Measure E) (I : E → ℝ≥0∞) : Prop where
  lsc : LowerSemicontinuous I
  upper : ∀ A : Set E, MeasurableSet A →
    limsup (fun ε : ℝ => (ε : EReal) * ENNReal.log (P ε A)) (𝓝[>] 0) ≤
      -(⨅ x ∈ closure A, ((I x : ℝ≥0∞) : EReal))
  lower : ∀ A : Set E, MeasurableSet A →
    -(⨅ x ∈ interior A, ((I x : ℝ≥0∞) : EReal)) ≤
      liminf (fun ε : ℝ => (ε : EReal) * ENNReal.log (P ε A)) (𝓝[>] 0)

/-- Rate function of a point mass: `0` at `x₀`, `∞` elsewhere. -/
def diracRate {E : Type*} (x₀ : E) (x : E) : ℝ≥0∞ := if x = x₀ then 0 else ⊤

/-- **Non-vacuity**: the constant family `δ_{x₀}` satisfies the LDP with `diracRate x₀` (on a
T1 space). -/
@[powerlib_foundation] theorem dirac_satisfiesLDP {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (x₀ : E) :
    SatisfiesLDP (fun _ => Measure.dirac x₀) (diracRate x₀) := by
  have hval : ∀ A : Set E, MeasurableSet A → ∀ ε : ℝ, 0 < ε →
      (ε : EReal) * ENNReal.log (Measure.dirac x₀ A) = if x₀ ∈ A then 0 else ⊥ := by
    intro A hA ε hε
    rw [Measure.dirac_apply' _ hA]
    by_cases h : x₀ ∈ A
    · simp [h]
    · simp [h, EReal.coe_mul_bot_of_pos hε]
  have hinf : ∀ S : Set E, (⨅ x ∈ S, ((diracRate x₀ x : ℝ≥0∞) : EReal)) =
      if x₀ ∈ S then 0 else ⊤ := by
    intro S
    by_cases h : x₀ ∈ S
    · simp only [h, ↓reduceIte]
      refine le_antisymm (iInf₂_le_of_le x₀ h (by simp [diracRate])) ?_
      refine le_iInf₂ fun x _ => ?_
      unfold diracRate; split_ifs <;> simp
    · simp only [h, ↓reduceIte]
      refine le_antisymm le_top (le_iInf₂ fun x hx => ?_)
      have : x ≠ x₀ := fun e => h (e ▸ hx)
      simp [diracRate, this]
  refine ⟨?_, fun A hA => ?_, fun A hA => ?_⟩
  · -- lower semicontinuity: `{x | t < I x}` is open
    intro x t ht
    by_cases hx : x = x₀
    · subst hx; simp [diracRate] at ht
    · have hopen : IsOpen ({x₀}ᶜ : Set E) := isOpen_compl_singleton
      filter_upwards [hopen.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      simpa [diracRate, hy] using (lt_of_lt_of_le ht (by simp [diracRate, hx]) : t < ⊤)
  · have hev : (fun ε : ℝ => (ε : EReal) * ENNReal.log (Measure.dirac x₀ A)) =ᶠ[𝓝[>] 0]
        fun _ => if x₀ ∈ A then 0 else ⊥ :=
      eventually_nhdsWithin_of_forall fun ε hε => hval A hA ε hε
    rw [limsup_congr hev, limsup_const, hinf]
    by_cases h : x₀ ∈ A
    · simp [h, subset_closure h]
    · simp [h]
  · have hev : (fun ε : ℝ => (ε : EReal) * ENNReal.log (Measure.dirac x₀ A)) =ᶠ[𝓝[>] 0]
        fun _ => if x₀ ∈ A then 0 else ⊥ :=
      eventually_nhdsWithin_of_forall fun ε hε => hval A hA ε hε
    rw [liminf_congr hev, liminf_const, hinf]
    by_cases h : x₀ ∈ interior A
    · simp [h, interior_subset h]
    · simp [h]

/-! ## Chernoff / Cramér upper bound -/

/-- **Chernoff bound** (Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf`). -/
@[powerlib_foundation] theorem chernoff_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {t : ℝ} (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t :=
  measure_ge_le_exp_mul_mgf ε ht h_int

/-- **Exponential bound for i.i.d.-type sums**: independent summands with common moment
generating function `M(t)` satisfy `P(Σ_{i<n} Xᵢ ≥ n a) ≤ (e^{−ta} M(t))ⁿ`. -/
@[powerlib_foundation] theorem chernoff_iid {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) {t a M : ℝ} (ht : 0 ≤ t) (hM : ∀ i, mgf (X i) μ t = M)
    (hint : ∀ i, Integrable (fun ω => exp (t * X i ω)) μ) (n : ℕ) :
    μ.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} ≤ (exp (-t * a) * M) ^ n := by
  have hsum : Integrable (fun ω => exp (t * (∑ i ∈ Finset.range n, X i) ω)) μ := by
    have h := hindep.integrable_exp_mul_sum (s := Finset.range n) hmeas (fun i _ => hint i)
    simpa using h
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ Finset.range n, X i) (n * a) ht hsum
  rw [hindep.mgf_sum hmeas, Finset.prod_congr rfl (fun i _ => hM i), Finset.prod_const,
    Finset.card_range] at h
  have e : exp (-t * (n * a)) = exp (-t * a) ^ n := by rw [← exp_nat_mul]; ring_nf
  rw [e, ← mul_pow] at h
  simpa [Finset.sum_apply] using h

/-! ## Freidlin–Wentzell action -/

variable {n : ℕ}

/-- **Freidlin–Wentzell action** of a path `φ` with derivative `φd` on `[0, T]`, drift `b`,
diffusion matrix `a` (`a = σσᵀ`): `S = ½ ∫₀ᵀ (φ̇ − b(φ))ᵀ a(φ)⁻¹ (φ̇ − b(φ)) dt`. -/
def fwAction (b : (Fin n → ℝ) → Fin n → ℝ) (a : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (φ φd : ℝ → Fin n → ℝ) (T : ℝ) : ℝ :=
  1 / 2 * ∫ t in (0 : ℝ)..T,
    (φd t - b (φ t)) ⬝ᵥ ((a (φ t))⁻¹ *ᵥ (φd t - b (φ t)))

/-- The action is nonnegative when the diffusion matrix is positive definite along the path. -/
@[powerlib_foundation] theorem fwAction_nonneg {b : (Fin n → ℝ) → Fin n → ℝ}
    {a : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : ∀ t ∈ Icc 0 T, (a (φ t)).PosDef) : 0 ≤ fwAction b a φ φd T := by
  unfold fwAction
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg hT
  intro t ht
  have := (ha t ht).inv.posSemidef.dotProduct_mulVec_nonneg (φd t - b (φ t))
  simpa using this

/-! ## Gradient systems: completing the square -/

/-- Action with unit diffusion `a = I`: `½ ∫ ‖φ̇ − b(φ)‖²`. -/
def unitAction (b : (Fin n → ℝ) → Fin n → ℝ) (φ φd : ℝ → Fin n → ℝ) (T : ℝ) : ℝ :=
  1 / 2 * ∫ t in (0 : ℝ)..T, (φd t - b (φ t)) ⬝ᵥ (φd t - b (φ t))

/-- With `a = I` the Freidlin–Wentzell action is `unitAction`. -/
@[powerlib_foundation] theorem fwAction_one (b : (Fin n → ℝ) → Fin n → ℝ) (φ φd : ℝ → Fin n → ℝ)
    (T : ℝ) : fwAction b (fun _ => 1) φ φd T = unitAction b φ φd T := by
  simp [fwAction, unitAction]

/-- **Completing the square (gradient drift `b = −∇U`, unit diffusion)**: if `U ∘ φ` has
derivative `∇U(φ) · φ̇` along the path (chain rule) and the integrands are continuous,
`S_{0T}(φ) = ½∫₀ᵀ ‖φ̇ − ∇U(φ)‖² + 2 (U(φ(T)) − U(φ(0)))`. -/
@[powerlib_foundation] theorem gradient_action_identity {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ}
    (hchain : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t)
    (hcont : Continuous fun t => gU (φ t) ⬝ᵥ φd t)
    (hc1 : Continuous fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) :
    unitAction (fun x => -gU x) φ φd T =
      1 / 2 * (∫ t in (0 : ℝ)..T, (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) +
        2 * (U (φ T) - U (φ 0)) := by
  have hftc : ∫ t in (0 : ℝ)..T, gU (φ t) ⬝ᵥ φd t = U (φ T) - U (φ 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hchain (hcont.intervalIntegrable _ _)
  have hpt : ∀ t, (φd t - -gU (φ t)) ⬝ᵥ (φd t - -gU (φ t)) =
      (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) + 4 * (gU (φ t) ⬝ᵥ φd t) := by
    intro t
    simp only [sub_neg_eq_add, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
      dotProduct_comm (φd t) (gU (φ t))]
    ring
  unfold unitAction
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    ((hcont.const_mul 4).intervalIntegrable _ _), intervalIntegral.integral_const_mul, hftc]
  ring

/-- **`S ≥ 2ΔU`** along every admissible path (`T ≥ 0`). -/
@[powerlib_foundation] theorem gradient_action_ge {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hchain : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t)
    (hcont : Continuous fun t => gU (φ t) ⬝ᵥ φd t)
    (hc1 : Continuous fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) :
    2 * (U (φ T) - U (φ 0)) ≤ unitAction (fun x => -gU x) φ φd T := by
  rw [gradient_action_identity hchain hcont hc1]
  have : 0 ≤ ∫ t in (0 : ℝ)..T, (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) :=
    intervalIntegral.integral_nonneg hT fun t _ => by
      simpa using dotProduct_self_star_nonneg (φd t - gU (φ t))
  linarith

/-- **Equality case**: `S = 2ΔU` iff the path follows the reversed gradient flow `φ̇ = ∇U(φ)` on
`[0, T]` (`T > 0`). -/
@[powerlib_foundation] theorem gradient_action_eq_iff {U : (Fin n → ℝ) → ℝ}
    {gU : (Fin n → ℝ) → Fin n → ℝ} {φ φd : ℝ → Fin n → ℝ} {T : ℝ} (hT : 0 < T)
    (hchain : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t)
    (hcont : Continuous fun t => gU (φ t) ⬝ᵥ φd t)
    (hc1 : Continuous fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t))) :
    unitAction (fun x => -gU x) φ φd T = 2 * (U (φ T) - U (φ 0)) ↔
      ∀ t ∈ Icc 0 T, φd t = gU (φ t) := by
  rw [gradient_action_identity hchain hcont hc1]
  have hnn : ∀ t, 0 ≤ (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) := fun t => by
    simpa using dotProduct_self_star_nonneg (φd t - gU (φ t))
  set f : ℝ → ℝ := fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)) with hfdef
  constructor
  · intro h
    have hz : ∫ t in (0 : ℝ)..T, f t = 0 := by simp only [hfdef]; linarith
    intro t0 ht0
    by_contra hne
    have hpos0 : 0 < f t0 := by
      rcases (hnn t0).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (sub_eq_zero.mp (dotProduct_self_eq_zero.mp heq.symm)) hne
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc1 t0 (f t0 / 2) (by linarith)
    set c := max 0 (t0 - δ / 2)
    set d := min T (t0 + δ / 2)
    have hcd : c < d := by
      simp only [c, d, max_lt_iff, lt_min_iff]
      refine ⟨⟨by linarith [ht0.1, ht0.2], by linarith [ht0.1, ht0.2]⟩,
        ⟨by linarith [ht0.1, ht0.2], by linarith [ht0.1, ht0.2]⟩⟩
    have hfpos : ∀ t ∈ Ioo c d, 0 < f t := by
      intro t ht
      have h1 : dist t t0 < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2, le_max_right 0 (t0 - δ / 2),
          min_le_right T (t0 + δ / 2)]
      have := hball t h1
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hcd_pos : 0 < ∫ t in c..d, f t :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hc1.intervalIntegrable _ _) hfpos hcd
    have hmono : ∫ t in c..d, f t ≤ ∫ t in (0 : ℝ)..T, f t :=
      intervalIntegral.integral_mono_interval (le_max_left _ _) hcd.le (min_le_left _ _)
        (Eventually.of_forall hnn) (hc1.intervalIntegrable _ _)
    linarith
  · intro h
    have hz : ∫ t in (0 : ℝ)..T, f t = 0 := by
      have : ∫ t in (0 : ℝ)..T, f t = ∫ t in (0 : ℝ)..T, (0 : ℝ) :=
        intervalIntegral.integral_congr fun t ht => by
          rw [uIcc_of_le hT.le] at ht
          simp only [hfdef, h t ht, sub_self, dotProduct_zero]
      rw [this, intervalIntegral.integral_zero]
    simp only [hfdef] at hz
    rw [hz]; ring

/-! ## Quasi-potential -/

/-- **Quasi-potential** (unit diffusion) from an attractor point `xA`:
`V_qp(x) = inf { S_{0T}(φ) : T ≥ 0, φ(0) = xA, φ(T) = x }` over paths with continuous action
integrand along which the chain rule for `U` holds (`ℝ≥0∞`-valued, `∞` if no admissible path). -/
def quasiPotential (U : (Fin n → ℝ) → ℝ) (gU : (Fin n → ℝ) → Fin n → ℝ) (xA x : Fin n → ℝ) :
    ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → Fin n → ℝ) (φd : ℝ → Fin n → ℝ)
    (_ : 0 ≤ T ∧ φ 0 = xA ∧ φ T = x ∧
      (∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => U (φ s)) (gU (φ t) ⬝ᵥ φd t) t) ∧
      Continuous (fun t => gU (φ t) ⬝ᵥ φd t) ∧
      Continuous (fun t => (φd t - gU (φ t)) ⬝ᵥ (φd t - gU (φ t)))),
    ENNReal.ofReal (unitAction (fun y => -gU y) φ φd T)

/-- **Gradient systems (T-quasi-potential)**: `V_qp(x) ≥ 2 (U(x) − U(x_𝒜))`. -/
@[powerlib_foundation] theorem quasiPotential_ge (U : (Fin n → ℝ) → ℝ)
    (gU : (Fin n → ℝ) → Fin n → ℝ) (xA x : Fin n → ℝ) :
    ENNReal.ofReal (2 * (U x - U xA)) ≤ quasiPotential U gU xA x := by
  unfold quasiPotential
  refine le_iInf fun T => le_iInf fun φ => le_iInf fun φd => le_iInf fun h => ?_
  obtain ⟨hT, h0, hTx, hchain, hcont, hc1⟩ := h
  apply ENNReal.ofReal_le_ofReal
  have := gradient_action_ge hT hchain hcont hc1
  rwa [h0, hTx] at this

end powerlib.Stochastic.LDP
