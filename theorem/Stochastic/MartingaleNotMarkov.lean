import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Processes
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Prod

/-! # A martingale that is not Markov

Source: work-sync `theory/T-process-foundations-stochastic.md` §1.4 ("Markov and martingale are
independent notions: neither implies the other").  The direction "Markov ⇏ martingale" is
`Processes.deterministic_markov_not_martingale`; this module gives "martingale ⇏ Markov".

Foundation (probability), not an engineering result.

Construction (two fair coins, `Ω = Bool × Bool` with the uniform product law).  Let
`ξ₁ ∈ {0, 1}` and `ξ₂ ∈ {−1, 1}` be the two coordinates and
`X₀ = X₁ = 0`, `X_n = ξ₁ ξ₂` for `n ≥ 2`, with the filtration `𝓕₀ = {∅, Ω}`, `𝓕₁ = σ(ξ₁)`,
`𝓕_n = σ(ξ₁, ξ₂)` (`n ≥ 2`).
* `cm_martingale`: `X` is an `𝓕`-martingale (`E[ξ₁ ξ₂ | ξ₁] = ξ₁ E ξ₂ = 0`).
* `cm_not_markov`: `X` is not Markov w.r.t. `𝓕` (conditional-expectation form, written out in
  the statement: it is false that `E[g(X_{n+1}) | 𝓕_n] = E[g(X_{n+1}) | σ(X_n)]` a.s. for every
  `n` and every bounded measurable `g`): for the bounded test
  function `g = 1_{x ≠ 0}`, `E[g(X₂) | 𝓕₁] = ξ₁` while `E[g(X₂) | σ(X₁)] = E ξ₁ = 1/2`, since `X₁`
  is constant; the future of `X` depends on information (`ξ₁`) that its present value does not
  carry.
-/

noncomputable section
namespace powerlib.Stochastic.Proc

open MeasureTheory ProbabilityTheory Filter Set

/-- Fair coin on `Bool`. -/
def coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

/-- Two independent fair coins. -/
def coin2 : Measure (Bool × Bool) := coin.prod coin

instance : IsProbabilityMeasure coin2 := by unfold coin2; infer_instance

@[powerlib_foundation] theorem integral_coin (f : Bool → ℝ) :
    ∫ b, f b ∂coin = (f true + f false) / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp [coin, Measure.real, PMF.uniformOfFintype_apply]
  ring

/-- `ξ₁ ∈ {0, 1}`. -/
def bern (b : Bool) : ℝ := if b then 1 else 0

/-- `ξ₂ ∈ {−1, 1}`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The process `X₀ = X₁ = 0`, `X_n = ξ₁ ξ₂` (`n ≥ 2`). -/
def cmX (n : ℕ) (ω : Bool × Bool) : ℝ := if n ≤ 1 then 0 else bern ω.1 * sgn ω.2

/-- The filtration `⊥, σ(ξ₁), σ(ξ₁, ξ₂), …`. -/
def cmF : Filtration ℕ (inferInstance : MeasurableSpace (Bool × Bool)) where
  seq n := if n = 0 then ⊥ else if n = 1 then MeasurableSpace.comap Prod.fst inferInstance
    else inferInstance
  mono' := by
    intro i j hij
    dsimp only
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first
      | exact bot_le
      | exact le_rfl
      | exact measurable_fst.comap_le
      | exact absurd hij (by omega)
  le' := by
    intro i
    split_ifs
    · exact bot_le
    · exact measurable_fst.comap_le
    · exact le_rfl

@[powerlib_foundation] theorem cmF_apply (n : ℕ) :
    cmF n = if n = 0 then ⊥ else if n = 1 then MeasurableSpace.comap Prod.fst inferInstance
      else inferInstance := rfl

@[powerlib_foundation] theorem cmF_one :
    cmF 1 = MeasurableSpace.comap Prod.fst inferInstance := by
  rw [cmF_apply]; simp

@[powerlib_foundation] theorem cmF_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    cmF n = (inferInstance : MeasurableSpace (Bool × Bool)) := by
  rw [cmF_apply]; simp [show n ≠ 0 by omega, show n ≠ 1 by omega]

@[powerlib_foundation] theorem cmX_le_one {n : ℕ} (hn : n ≤ 1) : cmX n = fun _ => 0 := by
  funext ω; simp [cmX, hn]

/-- **`X` is a martingale** for `𝓕` under two fair coins. -/
@[powerlib_foundation] theorem cm_martingale : Martingale cmX cmF coin2 := by
  refine martingale_nat ?_ (fun i => Integrable.of_finite) ?_
  · intro n
    by_cases hn : n ≤ 1
    · rw [cmX_le_one hn]; exact stronglyMeasurable_const
    · rw [cmF_of_two_le (by omega)]
      exact (measurable_of_countable _).stronglyMeasurable
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
    · rw [cmX_le_one le_rfl, cmX_le_one (zero_le_one)]
      exact (condExp_zero (μ := coin2) (m := cmF 0)).symm.eventuallyEq
    · rw [cmX_le_one le_rfl]
      refine ae_eq_condExp_of_forall_setIntegral_eq (cmF.le 1) Integrable.of_finite
        (fun _ _ _ => Integrable.of_finite.integrableOn) (fun s hs _ => ?_)
        stronglyMeasurable_const.aestronglyMeasurable
      rw [cmF_one, MeasurableSpace.measurableSet_comap] at hs
      obtain ⟨B, hB, rfl⟩ := hs
      rw [integral_zero, ← integral_indicator (measurable_fst hB)]
      have e : (Prod.fst ⁻¹' B).indicator (cmX (1 + 1)) =
          fun ω : Bool × Bool => B.indicator bern ω.1 * sgn ω.2 := by
        funext ω
        by_cases h : ω.1 ∈ B <;> simp [Set.indicator, cmX, h]
      rw [e, coin2, integral_prod_mul, integral_coin sgn]
      simp [sgn]
    · have e : cmX (i + 1) = cmX i := by
        funext ω; simp only [cmX, show ¬ i + 1 ≤ 1 by omega, show ¬ i ≤ 1 by omega, ite_false]
      rw [e, condExp_of_stronglyMeasurable (cmF.le i) ?_ Integrable.of_finite]
      rw [cmF_of_two_le hi]
      exact (measurable_of_countable _).stronglyMeasurable

/-- **`X` is not Markov** for `𝓕`: martingale does not imply Markov. The negated statement is the
Markov property in conditional-expectation form: for bounded measurable test functions `g`,
`E[g(X_{n+1}) | 𝓕_n] = E[g(X_{n+1}) | σ(X_n)]` a.s. -/
@[powerlib_foundation] theorem cm_not_markov :
    ¬ ∀ (n : ℕ) (g : ℝ → ℝ), Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
      coin2[fun ω => g (cmX (n + 1) ω) | cmF n] =ᵐ[coin2]
        coin2[fun ω => g (cmX (n + 1) ω) | MeasurableSpace.comap (cmX n) inferInstance] := by
  intro h
  set g : ℝ → ℝ := fun x => if x = 0 then 0 else 1 with hg
  have hgm : Measurable g := by
    refine Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const
  have hgb : ∃ C, ∀ x, |g x| ≤ C := ⟨1, fun x => by by_cases hx : x = 0 <;> simp [hg, hx]⟩
  have h1 := h 1 g hgm hgb
  have e : (fun ω => g (cmX (1 + 1) ω)) = fun ω : Bool × Bool => bern ω.1 := by
    funext ω
    rcases ω with ⟨a, b⟩
    cases a <;> cases b <;> simp [hg, cmX, bern, sgn]
  rw [e, cmX_le_one le_rfl, MeasurableSpace.comap_const, condExp_bot] at h1
  have hsm : StronglyMeasurable[cmF 1] (fun ω : Bool × Bool => bern ω.1) := by
    rw [cmF_one]
    exact ((measurable_of_countable bern).comp (comap_measurable Prod.fst)).stronglyMeasurable
  rw [condExp_of_stronglyMeasurable (cmF.le 1) hsm Integrable.of_finite] at h1
  have hmean : ∫ ω, bern ω.1 ∂coin2 = 1 / 2 := by
    have := integral_prod_mul (μ := coin) (ν := coin) bern (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    rw [coin2, this, integral_coin bern, integral_coin]
    simp [bern]
  rw [hmean] at h1
  obtain ⟨ω, hω⟩ := h1.exists
  rcases ω with ⟨a, b⟩
  cases a <;> norm_num [bern] at hω

end powerlib.Stochastic.Proc
