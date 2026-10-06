import dependencies.LeanForControl
import theorem.Dynamics.Defs

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

@[powerlib_foundation] theorem exists_isIntegralCurveOn_Icc
    {f : ℝ → E → E} {K : NNReal}
    (hf_cont : Continuous (Function.uncurry f))
    (hf_lip : ∀ t, LipschitzWith K (f t))
    (t₀ t₁ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveOn α f (Icc t₀ t₁) :=
  _root_.exists_isIntegralCurveOn_Icc hf_cont hf_lip t₀ t₁ x₀

omit [CompleteSpace E] in
@[powerlib_foundation] lemma hasDerivWithinAt_Ici_of_isIntegralCurveOn
    {f : ℝ → E → E} {α : ℝ → E} {t₀ t₁ : ℝ}
    (hα : IsIntegralCurveOn α f (Icc t₀ t₁)) :
    ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt α (f s (α s)) (Ici s) s :=
  _root_.hasDerivWithinAt_Ici_of_isIntegralCurveOn hα

omit [CompleteSpace E] in
@[powerlib_foundation] lemma dist_le_of_isIntegralCurveOn_Icc
    {f : ℝ → E → E} {K : NNReal} (hf_lip : ∀ t, LipschitzWith K (f t))
    {α β : ℝ → E} {t₀ t₁ : ℝ}
    (hα : IsIntegralCurveOn α f (Icc t₀ t₁)) (hβ : IsIntegralCurveOn β f (Icc t₀ t₁)) :
    ∀ t ∈ Icc t₀ t₁, dist (α t) (β t) ≤ dist (α t₀) (β t₀) * Real.exp (K * (t - t₀)) :=
  _root_.dist_le_of_isIntegralCurveOn_Icc hf_lip hα hβ

omit [CompleteSpace E] in
@[powerlib_foundation] lemma eqOn_of_isIntegralCurveOn_Icc
    {f : ℝ → E → E} {K : NNReal} (hf_lip : ∀ t, LipschitzWith K (f t))
    {α β : ℝ → E} {t₀ t₁ : ℝ}
    (hα : IsIntegralCurveOn α f (Icc t₀ t₁)) (hβ : IsIntegralCurveOn β f (Icc t₀ t₁))
    (h₀ : α t₀ = β t₀) :
    EqOn α β (Icc t₀ t₁) :=
  _root_.eqOn_of_isIntegralCurveOn_Icc hf_lip hα hβ h₀

@[powerlib_foundation] theorem exists_isIntegralCurveOn_Ici
    {f : ℝ → E → E} {K : NNReal}
    (hf_cont : Continuous (Function.uncurry f))
    (hf_lip : ∀ t, LipschitzWith K (f t))
    (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveOn α f (Ici t₀) ∧
      ∀ β : ℝ → E, β t₀ = x₀ → IsIntegralCurveOn β f (Ici t₀) → EqOn β α (Ici t₀) :=
  _root_.exists_isIntegralCurveOn_Ici hf_cont hf_lip t₀ x₀

@[powerlib_foundation] theorem forwardComplete_of_lipschitzWith
    {f : E → E} {K : NNReal} (hf : LipschitzWith K f) : ForwardComplete f := by
  intro a x₀
  obtain ⟨φ, hφ₀, hφ, _⟩ := _root_.exists_isIntegralCurveOn_Ici
    (f := fun _ x => f x) (hf.continuous.comp continuous_snd) (fun _ => hf) a x₀
  exact ⟨φ, hφ₀, hφ⟩

end powerlib.Dynamics
