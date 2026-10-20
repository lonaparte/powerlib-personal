import theorem.TMIO.ClaimElab
import theorem.Family.Basic
import theorem.Flow.Certificate
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Cubic damping

The cubic term admits no global Lipschitz constant, so existence for all time is not available
from Picard–Lindelöf alone. The energy `‖x‖²` is a quadratic-decay certificate with rate `2α`; it
proves forward completeness and global exponential stability at every initial amplitude.

Model boundary.
* The autonomous fields `x' = -(α + ‖x‖²) x` on `ℝⁿ` with a positive linear damping gain `α`, in
  continuous time, without input, delay or switching; the equilibrium is the origin.
* A polynomial example family of generic mathematics, not an engineering model.

Source: the quadratic-decay certificates of `theorem/Flow/Certificate.lean` (forward
completeness from compact energy sublevels); the family interface of `theorem/Family/Basic.lean`.

Results.
* Static: `Gain`, `field`, `energy`, `field_smooth`, `not_lipschitzWith` (with a nonnegative gain
  the field admits no global Lipschitz constant), `energy_lie`, `certificate` (the energy is a
  quadratic-decay certificate with rate `2α`), `Requirement`, `Meets`, `translate`,
  `family_isAutonomous`.

Family and connection conclusions.
* `Nonlinear.Cubic.family : Family Gain Requirement n 0`: every gain read as its autonomous field.
  The requirement language bounds the decay rate from below (`decayRateAtLeast a`); decay at `a`
  translates into `a ≤ α`, instability and conservation into the whole language, which no model
  meets (`realize_univ`), every other sentence into no requirement.
* `mem_den_globallyExponentiallyStable`: every model is globally exponentially stable.
* On a nontrivial state space the family is faithful (`chain_eq_semantics`): every model
  satisfies the stability sentences, sampled contraction and passivity, none is unstable or
  conservative, and a model decays at the rate `a` exactly when `a ≤ α` — near the origin the
  cubic term vanishes and the gain alone sets the rate.
-/

noncomputable section

namespace powerlib.Nonlinear.Cubic

open Set TMIO

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A positive linear damping gain. -/
abbrev Gain := {α : ℝ // 0 < α}

/-- The cubic damping field with linear gain `α`. -/
def field (α : ℝ) (x : ℝⁿ) : ℝⁿ := (-(α + ‖x‖ ^ 2)) • x

/-- The energy `‖x‖²`. -/
def energy (x : ℝⁿ) : ℝ := ‖x‖ ^ 2

@[powerlib_foundation] theorem field_smooth (α : ℝ) : ContDiff ℝ 1 (field (n := n) α) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).neg.smul contDiff_id

/-- With a nonnegative gain the field admits no global Lipschitz constant. -/
@[powerlib_foundation] theorem not_lipschitzWith (hn : 0 < n) {α : ℝ} (hα : 0 ≤ α)
    (K : NNReal) : ¬ LipschitzWith K (field (n := n) α) := by
  intro h
  have hr : (0 : ℝ) < K + 1 := by positivity
  let x : ℝⁿ := EuclideanSpace.single ⟨0, hn⟩ ((K : ℝ) + 1)
  have hx : ‖x‖ = K + 1 := by simp [x, abs_of_pos hr]
  have h1 := h.norm_sub_le x 0
  simp only [field, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, smul_zero, sub_zero, norm_smul, norm_neg, hx] at h1
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  nlinarith [NNReal.coe_nonneg K]

/-- The Lie derivative of the energy. -/
@[powerlib_foundation] theorem energy_lie (α : ℝ) (x : ℝⁿ) :
    fderiv ℝ energy x (field α x) = -2 * (α + ‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  change fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ 2) x (field α x) = _
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp only [smul_apply, innerSL_apply_apply]
  rw [field, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- The energy is a quadratic-decay certificate with rate `2α`. -/
def certificate (α : Gain) : Flow.QuadraticDecay (field (n := n) α.1) energy 0 where
  lower := 1
  upper := 1
  rate := 2 * α.1
  lower_pos := one_pos
  upper_pos := one_pos
  rate_pos := by linarith [α.2]
  smooth := contDiff_norm_sq ℝ
  equilibrium := by simp [field]
  lower_bound x := by simp [energy]
  upper_bound x := by simp [energy]
  dissipation x := by
    rw [energy_lie]
    dsimp [energy]
    nlinarith [sq_nonneg (‖x‖ ^ 2)]

/-- Every model is globally exponentially stable, with a solution through every state. -/
@[powerlib_foundation] private theorem globallyExponentiallyStable (α : Gain) :
    Flow.GloballyExponentiallyStable (field (n := n) α.1) 0 :=
  (certificate α).globallyExponentiallyStable (field_smooth _)

/-- The energy never increases, so along a solution segment it decays no faster than at the rate
`2 (α + r₀)`, with `r₀` the initial energy. -/
@[powerlib_foundation] private theorem energy_lower (α : Gain) {φ : ℝ → ℝⁿ} {a b t : ℝ}
    (hφ : IsTrajectoryOn φ (field α.1) a b) (ht : t ∈ Icc a b) :
    Real.exp (-(2 * (α.1 + ‖φ a‖ ^ 2) * (t - a))) * ‖φ a‖ ^ 2 ≤ ‖φ t‖ ^ 2 := by
  have hdec : ∀ s ∈ Icc a b, ‖φ s‖ ^ 2 ≤ ‖φ a‖ ^ 2 := fun s hs => by
    have hb := (certificate α).energy_bound hφ hs
    have he : Real.exp (-((certificate (n := n) α).rate * (s - a))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (certificate (n := n) α).rate * (s - a) :=
        mul_nonneg (certificate α).rate_pos.le (by linarith [hs.1])
      linarith
    have hpos : 0 ≤ energy (φ a) := sq_nonneg _
    calc ‖φ s‖ ^ 2 = energy (φ s) := rfl
      _ ≤ Real.exp (-((certificate α).rate * (s - a))) * energy (φ a) := hb
      _ ≤ 1 * energy (φ a) := by gcongr
      _ = ‖φ a‖ ^ 2 := one_mul _
  exact Flow.energy_lower_bound (V := energy) (contDiff_norm_sq ℝ) hφ (fun s hs => by
    rw [energy_lie]
    dsimp [energy]
    nlinarith [hdec s hs, sq_nonneg ‖φ s‖, mul_le_mul_of_nonneg_left (hdec s hs)
      (sq_nonneg ‖φ s‖)]) ht

/-! ## The family -/

/-- A requirement on the cubic models: a lower bound on the decay rate. -/
inductive Requirement
  | decayRateAtLeast (a : ℝ)

/-- Satisfaction of a requirement by a model. -/
def Meets (α : Gain) : Requirement → Prop
  | .decayRateAtLeast a => a ≤ α.1

/-- The translation of the sentences: a decay rate bounds the gain from below; instability and
conservation are translated into the whole language, which no model meets; every other sentence
needs no requirement. -/
def translate : Sentence → Set Requirement
  | .flow (.decay a) => {.decayRateAtLeast a}
  | .flow .unstable | .flow .conservative => Set.univ
  | _ => ∅

/-- The cubic family: every gain read as its autonomous field. -/
def family : Family Gain Requirement n 0 :=
  ⟨fun α => .continuous (Port.System.autonomous (field α.1)), Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous :
    (family (n := n)).IsAutonomous fun α => field α.1 := fun _ => rfl

theorem mem_den_globallyExponentiallyStable (α : Gain) :
    connection% (α ∈ (family (n := n)).den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr (globallyExponentiallyStable α)

/-- No gain bounds every decay rate. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext α
  simp only [mem_realize, mem_univ, true_implies, mem_empty_iff_false, iff_false, not_forall]
  exact ⟨.decayRateAtLeast (α.1 + 1), by simp [Meets]⟩

/-- The cubic family is faithful on a nontrivial state space: its translation chain is its
semantics connection. Every model satisfies the stability sentences, sampled contraction and
passivity; none is unstable or conservative; and a model decays at the rate `a` exactly when
`a ≤ α`, since small solutions decay no faster than at the rate `α + ‖x₀‖²`. -/
@[powerlib_domain] theorem chain_eq_semantics (hn : 0 < n) :
    connection% ((family (n := n)).chain = (family (n := n)).semantics) := by
  unfold powerlib.TMIO.Statement
  have hges := globallyExponentiallyStable (n := n)
  have hall : ∀ {P : Flow.Property}, (∀ α : Gain, P.holds (field (n := n) α.1) 0) →
      (family (n := n)).den (.flow P) = univ := fun h => by
    ext α
    simp only [family_isAutonomous.mem_den_flow, mem_univ, iff_true]
    exact h α
  refine Family.chain_eq_semantics_iff.mpr fun s => ?_
  rcases s with P | _
  · cases P
    case lyapunovStable =>
      exact Family.exact_of_translate_eq_empty (F := family) rfl (hall fun α => (hges α).lyapunovStable)
    case contractive =>
      exact Family.exact_of_translate_eq_empty (F := family) rfl (hall fun α => (hges α).sampledContraction)
    case unstable =>
      refine Family.exact_of_translate_eq_univ (F := family) realize_univ rfl ?_
      ext α
      simp only [family_isAutonomous.mem_den_flow, mem_empty_iff_false, iff_false]
      exact not_not.mpr (hges α).lyapunovStable
    case conservative =>
      refine Family.exact_of_translate_eq_univ (F := family) realize_univ rfl ?_
      ext α
      simp only [family_isAutonomous.mem_den_flow, mem_empty_iff_false, iff_false]
      exact fun h => h.not_localAsymptoticStable hn (hges α).2.1
        ((hges α).holds (P := .locallyAsymptoticallyStable) trivial)
    case decay a =>
      ext α
      rw [Family.mem_den, mem_realize]
      change (∀ q ∈ ({.decayRateAtLeast a} : Set Requirement), Meets α q) ↔
        Flow.Decay (field α.1) 0 a
      simp only [mem_singleton_iff, forall_eq, Meets]
      constructor
      · intro ha
        have hd := (certificate (n := n) α).decay
        rw [show (certificate (n := n) α).rate / 2 = α.1 by simp [certificate]] at hd
        exact hd.mono ha
      · rintro ⟨C, hC⟩
        by_contra hlt
        push Not at hlt
        set ε := Real.sqrt ((a - α.1) / 2) with hε_def
        have hε : 0 < ε := Real.sqrt_pos.mpr (by linarith)
        have hε2 : ε ^ 2 = (a - α.1) / 2 := Real.sq_sqrt (by linarith)
        set x₀ : ℝⁿ := EuclideanSpace.single ⟨0, hn⟩ ε with hx₀_def
        have hx₀ : ‖x₀‖ = ε := by simp [hx₀_def, abs_of_pos hε]
        obtain ⟨φ, hφ0, hφ⟩ := (hges α).2.1 0 x₀
        have hgap : 0 < a - (α.1 + ε ^ 2) := by rw [hε2]; linarith
        set T := C ^ 2 / (2 * (a - (α.1 + ε ^ 2))) with hT_def
        have hT0 : 0 ≤ T := by positivity
        have hseg : IsTrajectoryOn φ (field α.1) 0 T := hφ.mono Icc_subset_Ici_self
        have hlow := energy_lower α hseg ⟨hT0, le_rfl⟩
        have hup := hC 0 T φ hseg T ⟨hT0, le_rfl⟩
        rw [hφ0, hx₀] at hlow
        rw [hφ0, sub_zero, sub_zero, sub_zero, hx₀] at hup
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hup 2
        have hE : Real.exp (-(2 * (α.1 + ε ^ 2) * (T - 0))) =
            Real.exp (-a * T) ^ 2 * Real.exp (C ^ 2) := by
          rw [pow_two (Real.exp (-a * T)), ← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hT_def]
          field_simp
          ring
        rw [hE] at hlow
        have hpos : 0 < Real.exp (-a * T) ^ 2 * ε ^ 2 := by positivity
        have hexp := Real.add_one_le_exp (C ^ 2)
        nlinarith
    all_goals
      exact Family.exact_of_translate_eq_empty (F := family) rfl (hall fun α => (hges α).holds trivial)
  · exact Family.exact_of_translate_eq_empty (F := family) rfl family_isAutonomous.den_passive

end powerlib.Nonlinear.Cubic
