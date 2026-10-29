import theorem.Envelope.Basic
import theorem.Stack.Implementation
import theorem.TMIO.ClaimElab
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Disturbed implementations of deterministic designs (M–I)

A deterministic design is read with its operating envelope and no disturbance: the same system for
every sample. An implementation adds a random perturbation `σ g ω` of size at most `σ W` to the
design's field, and is judged on its own safe set, which contains every state within the margin
`δ` of the design's safe set. The realization relation is the design map
(`Implementation.ofDesign`): the model layer is the design, the implementation layer the
disturbed system.

Finite horizons are realized under a small disturbance. While the perturbation stays below `W`,
a disturbed solution stays within the Grönwall bound `gronwallBound 0 K (|σ| W) t` of the nominal
solution from the same state (`K` the Lipschitz constant of the design's zero-input field), so a
design safe before `T₀` stays safe in the implementation's set when that bound at `T₀` is at most
the margin, with the probability that the perturbation exceeds `W` as the level.

The infinite horizon is not realized by any bound on the intensity. The drift design `ẋ = 0` from
the origin is safe over every horizon; its implementation `ẋ = σ ω₀`, `ω₀` standard Gaussian,
leaves its safe set, the unit ball, with probability one for every `σ ≠ 0`, while over each
finite horizon `T₀` it is safe at any positive level for `|σ|` below a threshold `σ₀(T₀)`. The two
limits, small disturbance and long horizon, do not commute.

Scope.
* A generic template, not a model. Model layer (M): an arbitrary family `F : Family X Q n p` whose
  models are designs with an envelope (`IsDesign`: the same system `sys x` for every sample,
  initial set `S x`, safe set `A x`, a probability law). Implementation layer (I): the structure
  `Noisy X n` of a design model, a safe set, a margin, an intensity `σ`, a law and a perturbation
  field `g ω`; its system for the sample `ω` is the design's system with `σ g ω` added to the
  field (`Port.System.perturb`), read under zero input.
* The disturbance is a random, time-invariant perturbation of the field (a bias or a parameter
  error); a time-varying disturbance enters through states of an exosystem, and white noise
  (stochastic integrals) is not represented.
* The safety-reading law is a universe-polymorphic foundation connection. The realization laws
  below use arbitrary families of `Type`.

Source: Grönwall's inequality for approximate solutions (Mathlib
`dist_le_of_approx_trajectories_ODE`); finite-time stability over a horizon (Dorato 1961; Amato,
Ariola and Dorato 2001); the engineering reading of stability as the exceedance of thresholds on a
few physical quantities (work-sync `theory/T-converter-stochastic-paradigm.md` §1.3, F3); the
envelope laws (`theorem/Envelope/Basic.lean`); implementations
(`theorem/Stack/Implementation.lean`). Scaffold: `theorem/DisturbedRealization.agda`.

Results.
* `erode A δ` (the states whose closed `δ`-ball lies in `A`); `Port.System.perturb`;
  `dist_le_gronwall_perturb` (the Grönwall deviation of a perturbed solution);
  `holds_safe_of_margin` (finite-horizon safety of the perturbed system from the margin).
* `IsDesign`, `IsDesign.mem_den_safe_iff` (a design is safe at a level below one exactly when its
  reachable set lies in its safe set).
* `gaussianSample` (independent standard Gaussian coordinates), `gaussianSample_zero`;
  `noisyDrift_exceeds` (the drift `ẋ = c`, `c ≠ 0`, leaves the unit ball).

Family and connection conclusions.
* Template: `Noisy`, `NoiseRequirement` (Lipschitz design, solvable design, margin, small
  intensity, bounded perturbation, intensity bound), `noisyFamily`, `noisy`.
* M–I laws: `noisy_realizationSoundUnder_safe` (scaffold `finite-sound`): within a Lipschitz
  solvable design, the margin, a small intensity and a perturbation bounded with probability
  `1 − ε`, the realization of safety before `T₀` at the level `ε < 1` is sound.
* The witness: `driftDesign`, `noisyDrift`, `driftImpl`; `mem_den_driftDesign`
  (the design is safe over every horizon); `noisyDrift_mem_den_finite` (scaffold `finite-small`):
  over every finite horizon a small intensity is safe at any positive level;
  `noisyDrift_not_mem_den_top` (scaffold `infinite-unsafe`): over the infinite horizon no nonzero
  intensity is; `not_driftImpl_realizationSoundUnder_top` (scaffold `infinite-not-sound`): no
  intensity bound makes the realization of infinite-horizon safety sound.
-/

noncomputable section

namespace powerlib.Envelope

open MeasureTheory Set TMIO Metric ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Finite horizons under a small perturbation -/

/-- The states whose closed `δ`-ball lies in `A`. -/
def erode (A : Set ℝⁿ) (δ : ℝ) : Set ℝⁿ := {y | closedBall y δ ⊆ A}

/-- The system with the field perturbed by `g`. -/
def _root_.powerlib.Port.System.perturb (s : Port.System n p) (g : ℝⁿ → ℝⁿ) : Port.System n p :=
  ⟨fun x u => s.field x u + g x, s.output⟩

/-- **Grönwall deviation.** While the perturbation stays below `W`, a solution of the perturbed
system stays within `gronwallBound 0 K (|σ| W) t` of the nominal solution from the same state. -/
@[tmio T, powerlib_foundation] theorem dist_le_gronwall_perturb {s : Port.System n p} {K : ℝ≥0}
    {σ W t : ℝ} (hK : LipschitzWith K s.zeroInput) {g : ℝⁿ → ℝⁿ} (hg : ∀ x, ‖g x‖ ≤ W)
    {x xn : ℝ → ℝⁿ} (hx : (s.perturb (σ • g)).IsTrajectoryOn 0 x 0 t)
    (hxn : s.IsTrajectoryOn 0 xn 0 t) (h0 : x 0 = xn 0) (ht : 0 ≤ t) :
    dist (x t) (xn t) ≤ gronwallBound 0 K (|σ| * W) t := by
  have h := dist_le_of_approx_trajectories_ODE (v := fun _ => s.zeroInput) (K := K)
    (fun _ => hK) (f' := fun τ => (s.perturb (σ • g)).field (x τ) 0)
    (g' := fun τ => s.field (xn τ) 0) (εf := |σ| * W) (εg := 0) (δ := 0)
    (fun τ hτ => (hx τ hτ).continuousWithinAt)
    (fun τ hτ => (hx τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hτ))
    (fun τ _ => by
      rw [dist_eq_norm]
      simp only [Port.System.perturb, Port.System.zeroInput, add_sub_cancel_left, Pi.smul_apply,
        norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hg _) (abs_nonneg σ))
    (fun τ hτ => (hxn τ hτ).continuousWithinAt)
    (fun τ hτ => (hxn τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hτ))
    (fun τ _ => by simp [Port.System.zeroInput])
    (by rw [h0, dist_self]) t ⟨ht, le_rfl⟩
  rwa [add_zero, sub_zero] at h

/-- **Finite-horizon safety from a margin.** A system whose zero-input field is `K`-Lipschitz,
whose initial states start solutions on `[0, T₀]`, and whose states reached before `T₀` lie at
least `δ` inside the safe set stays safe before `T₀` under every perturbation `σ g ω` that is
bounded by `W`, when `gronwallBound 0 K (|σ| W) T₀ ≤ δ`; the level is the probability that the
perturbation exceeds `W`. -/
@[powerlib_foundation] theorem holds_safe_of_margin {s : Port.System n p} {S A : Set ℝⁿ}
    {ν : Measure Sample} {g : Sample → ℝⁿ → ℝⁿ} {σ δ W T₀ : ℝ} {K : ℝ≥0} {ε : ℝ≥0∞}
    (hK : LipschitzWith K s.zeroInput) (hW : 0 ≤ W) (hsol : s.Solvable S T₀)
    (hreach : s.reach S (ENNReal.ofReal T₀) ⊆ erode A δ)
    (hsmall : gronwallBound 0 K (|σ| * W) T₀ ≤ δ) (hbound : ν {ω | ∃ x, W < ‖g ω x‖} ≤ ε) :
    (Sentence.envelope (.safe (ENNReal.ofReal T₀) ε)).holds
      (Behaviour.disturbed (fun ω => s.perturb (σ • g ω)) S A ν) := by
  rw [Sentence.holds_safe_disturbed]
  refine le_trans (measure_mono fun ω hω => ?_) hbound
  obtain ⟨x, t, ht, hT, hS, hx, hA⟩ := hω
  have htT : t < T₀ := (ENNReal.ofReal_lt_ofReal_iff'.mp hT).1
  show ∃ x, W < ‖g ω x‖
  by_contra hb
  push Not at hb
  obtain ⟨xn, hxn0, hxn⟩ := hsol (x 0) hS
  have hxnt : s.IsTrajectoryOn 0 xn 0 t := hxn.mono (Icc_subset_Icc le_rfl htT.le)
  have hd := dist_le_gronwall_perturb hK hb hx hxnt hxn0.symm ht
  have hmem : xn t ∈ erode A δ := hreach ⟨xn, t, ht, hT, hxn0 ▸ hS, hxnt, rfl⟩
  exact hA (hmem (mem_closedBall.mpr (hd.trans ((gronwallBound_mono le_rfl
    (mul_nonneg (abs_nonneg σ) hW) K.2 htT.le).trans hsmall))))

/-! ## Designs and their disturbed implementations -/

/-- A family of designs with an envelope: every model is read as its system, the same for every
sample, with an initial set, a safe set and a probability law. -/
def IsDesign {X Q : Type*} (F : Family X Q n p) (sys : X → Port.System n p) (S A : X → Set ℝⁿ)
    (ν : X → Measure Sample) : Prop :=
  ∀ x, F.system x = .disturbed (fun _ => sys x) (S x) (A x) (ν x)

/-- A design is safe at a level below one exactly when its reachable set lies in its safe set. -/
@[tmio TM, powerlib_foundation] theorem IsDesign.mem_den_safe_iff {X Q : Type*} {F : Family X Q n p}
    {sys : X → Port.System n p} {S A : X → Set ℝⁿ} {ν : X → Measure Sample}
    [∀ x, IsProbabilityMeasure (ν x)] (hF : IsDesign F sys S A ν) {x : X} {T ε : ℝ≥0∞}
    (hε : ε < 1) :
    connection% (x ∈ F.den (.envelope (.safe T ε)) ↔ (sys x).reach (S x) T ⊆ A x) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den), hF x]
  exact holds_safe_undisturbed_iff _ _ _ _ _ hε

/-- A disturbed implementation of a design: the design model, the implementation's safe set and
margin, the intensity `σ`, the law of the samples and the perturbation field `g ω`. -/
structure Noisy (X : Type*) (n : ℕ) where
  design : X
  safe : Set (EuclideanSpace ℝ (Fin n))
  margin : ℝ
  intensity : ℝ
  law : Measure Sample
  perturbation : Sample → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)

/-- The realistic constraints of a disturbed implementation. -/
inductive NoiseRequirement
  /-- The design's zero-input field is `K`-Lipschitz. -/
  | lipschitz (K : ℝ≥0)
  /-- Every initial state of the design starts a solution on `[0, T₀]`. -/
  | solvable (T₀ : ℝ)
  /-- Every state within the margin of the design's safe set lies in the implementation's. -/
  | margin
  /-- The Grönwall bound of the intensity times `W` at `T₀` is at most the margin. -/
  | small (K : ℝ≥0) (W T₀ : ℝ)
  /-- The perturbation exceeds `W` with probability at most `ε`. -/
  | bounded (W : ℝ) (ε : ℝ≥0∞)
  /-- The intensity is at most `σ₀`. -/
  | intensityAtMost (σ₀ : ℝ)
  /-- The inconsistent requirement. -/
  | impossible

/-- The constraints met by a disturbed implementation of a design `sys`, `S`, `A`. -/
def NoiseRequirement.Meets {X : Type*} (sys : X → Port.System n p) (S A : X → Set ℝⁿ)
    (y : Noisy X n) : NoiseRequirement → Prop
  | .lipschitz K => LipschitzWith K (sys y.design).zeroInput
  | .solvable T₀ => (sys y.design).Solvable (S y.design) T₀
  | .margin => A y.design ⊆ erode y.safe y.margin
  | .small K W T₀ => 0 ≤ W ∧ gronwallBound 0 K (|y.intensity| * W) T₀ ≤ y.margin
  | .bounded W ε => y.law {ω | ∃ x, W < ‖y.perturbation ω x‖} ≤ ε
  | .intensityAtMost σ₀ => |y.intensity| ≤ σ₀
  | .impossible => False

/-- The disturbed implementations of the designs `sys`, `S`, `A`: each read as the design's system
perturbed by `σ g ω` for the sample `ω`, on its own safe set. Every sentence is translated into
the whole language, which no implementation meets (no coverage claimed). -/
def noisyFamily {X : Type*} (sys : X → Port.System n p) (S A : X → Set ℝⁿ) :
    Family (Noisy X n) NoiseRequirement n p where
  system y := .disturbed (fun ω => (sys y.design).perturb (y.intensity • y.perturbation ω))
    (S y.design) y.safe y.law
  meets := NoiseRequirement.Meets sys S A
  translate _ := Set.univ

/-- The disturbed realization: every disturbed implementation realizes its design. -/
def noisy {X Q : Type*} (F : Family X Q n p) (sys : X → Port.System n p) (S A : X → Set ℝⁿ) :
    Implementation X Q (Noisy X n) NoiseRequirement n p n p :=
  { model := F, impl := noisyFamily sys S A, realizes := Implementation.ofDesign Noisy.design }

/-! ## The realization of finite-horizon safety

The laws are connection statements about arbitrary families of `Type`. -/

variable {X Q : Type} {F : Family X Q n p} {sys : X → Port.System n p}
  {S A : X → Set (EuclideanSpace ℝ (Fin n))} {ν : X → Measure Sample}

/-- **Small disturbances realize finite-horizon safety.** Within a Lipschitz design whose initial
states start solutions on `[0, T₀]`, the margin, an intensity whose Grönwall bound at `T₀` is at
most the margin, and a perturbation exceeding `W` with probability at most `ε < 1`, an
implementation whose design is safe before `T₀` is safe before `T₀` at the level `ε`. -/
@[tmio MI, powerlib_domain] theorem noisy_realizationSoundUnder_safe [∀ x, IsProbabilityMeasure (ν x)]
    (hF : IsDesign F sys S A ν) {K : ℝ≥0} {W T₀ : ℝ} {ε : ℝ≥0∞} (hε : ε < 1) :
    connection% ((noisy F sys S A).RealizationSoundUnder
      {.lipschitz K, .solvable T₀, .margin, .small K W T₀, .bounded W ε}
      (.envelope (.safe (ENNReal.ofReal T₀) ε))) := by
  unfold powerlib.TMIO.Statement
  rintro y ⟨hd, hΔ⟩
  rw [Implementation.certify_realizes_of_design (I := noisy F sys S A) rfl, mem_preimage] at hd
  rw [(connection_proof% TMIO.mem_realize)] at hΔ
  have hK : LipschitzWith K (sys y.design).zeroInput := hΔ (.lipschitz K) (by simp)
  have hsol : (sys y.design).Solvable (S y.design) T₀ := hΔ (.solvable T₀) (by simp)
  have hm : A y.design ⊆ erode y.safe y.margin := hΔ .margin (by simp)
  have hs : 0 ≤ W ∧ gronwallBound 0 K (|y.intensity| * W) T₀ ≤ y.margin :=
    hΔ (.small K W T₀) (by simp)
  have hb : y.law {ω | ∃ x, W < ‖y.perturbation ω x‖} ≤ ε := hΔ (.bounded W ε) (by simp)
  rw [(connection_proof% Family.mem_den)]
  exact holds_safe_of_margin hK hs.1 hsol ((hF.mem_den_safe_iff hε).mp hd |>.trans hm) hs.2 hb

/-! ## The drift: no intensity bound realizes the infinite horizon -/

/-- The samples with independent standard Gaussian coordinates. -/
def gaussianSample : Measure Sample := Measure.infinitePi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure gaussianSample := by
  unfold gaussianSample
  infer_instance

@[powerlib_foundation] theorem gaussianSample_zero : gaussianSample {ω | ω 0 = 0} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0).measure_preimage
    (measurableSet_singleton (0 : ℝ)).nullMeasurableSet
  rw [measure_singleton] at h
  exact h

/-- The fixed zero-drift design has its own model type, so the family inventory does not
identify unrelated uses of `Unit` as models. -/
inductive DriftDesign where
  | zero

/-- The drift design `ẋ = 0` from the origin with the safe set of radius `1/2`. -/
def driftDesign : Family DriftDesign Unit 1 1 :=
  ⟨fun _ => .disturbed (fun _ => drift 0) {0} (ball 0 (1 / 2)) (Measure.dirac (constSample 0)),
    fun _ _ => False, fun _ => Set.univ⟩

@[powerlib_foundation] theorem driftDesign_isDesign :
    IsDesign driftDesign (fun _ => drift 0) (fun _ => {0}) (fun _ => ball 0 (1 / 2))
      (fun _ => Measure.dirac (constSample 0)) := fun _ => rfl

/-- The disturbed drift `ẋ = σ ω₀`, `ω₀` standard Gaussian, on the unit ball with the margin
`1/2`. -/
def noisyDrift (σ : ℝ) : Noisy DriftDesign 1 :=
  ⟨.zero, ball 0 1, 1 / 2, σ, gaussianSample, fun ω _ => ω 0 • e₁⟩

/-- The disturbed realization of the drift design. -/
def driftImpl : Implementation DriftDesign Unit (Noisy DriftDesign 1) NoiseRequirement 1 1 1 1 :=
  noisy driftDesign (fun _ => drift 0) (fun _ => {0}) (fun _ => ball 0 (1 / 2))

@[powerlib_foundation] theorem norm_smul_e₁ (a : ℝ) : ‖a • e₁‖ = |a| := by
  simp [e₁, norm_smul]

@[powerlib_foundation] theorem drift_perturb (c : ℝ) :
    (drift 0).perturb (fun _ => c • e₁) = drift c := by
  simp only [drift, Port.System.perturb, zero_smul, zero_add]

/-- The drift design is safe over every horizon at every level. -/
@[tmio TM, powerlib_domain] theorem mem_den_driftDesign (T ε : ℝ≥0∞) :
    connection% (DriftDesign.zero ∈ driftDesign.den (.envelope (.safe T ε))) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change Measure.dirac (constSample 0) {_ω | (drift 0).Exceeds {0} (ball 0 (1 / 2)) T} ≤ ε
  have hE : {_ω : Sample | (drift 0).Exceeds {0} (ball 0 (1 / 2)) T} = ∅ := by
    refine eq_empty_of_forall_notMem fun _ h => ?_
    obtain ⟨t, -, -, ht⟩ := drift_exceeds_iff.mp h
    exact ht (by simp)
  rw [hE, measure_empty]
  exact zero_le

/-- The disturbed drift with a nonzero intensity leaves the unit ball with probability one. -/
@[powerlib_foundation] theorem noisyDrift_exceeds {σ : ℝ} (hσ : σ ≠ 0) {ω : Sample}
    (hω : ω 0 ≠ 0) : (drift (σ * ω 0)).Exceeds {0} (ball 0 1) ⊤ := by
  have hc : σ * ω 0 ≠ 0 := mul_ne_zero hσ hω
  refine drift_exceeds_iff.mpr ⟨2 / |σ * ω 0|, by positivity, ENNReal.ofReal_lt_top, ?_⟩
  rw [mem_ball, dist_zero_right, norm_smul_e₁, abs_mul, abs_div, abs_two, abs_abs,
    mul_div_cancel₀ _ (abs_ne_zero.mpr hc)]
  norm_num

/-- States within `1/2` of the ball of radius `1/2` lie in the unit ball. -/
@[powerlib_foundation] theorem ball_half_subset_erode :
    ball (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2) ⊆ erode (ball 0 1) (1 / 2) := by
  intro z hz w hw
  rw [mem_ball, dist_zero_right] at hz ⊢
  rw [mem_closedBall, dist_eq_norm] at hw
  calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ < 1 / 2 + 1 / 2 := add_lt_add_of_le_of_lt hw hz
    _ = 1 := by norm_num

/-- **Over the infinite horizon no nonzero intensity is safe.** The disturbed drift with `σ ≠ 0`
leaves the unit ball with probability one, so it is not safe at any level `ε < 1`. -/
@[tmio TM, powerlib_domain] theorem noisyDrift_not_mem_den_top {σ : ℝ} (hσ : σ ≠ 0) {ε : ℝ≥0∞}
    (hε1 : ε < 1) :
    connection% (noisyDrift σ ∉ driftImpl.impl.den (.envelope (.safe ⊤ ε))) := by
  unfold powerlib.TMIO.Statement
  intro hmem
  rw [(connection_proof% Family.mem_den)] at hmem
  change gaussianSample {ω | ((drift 0).perturb (σ • fun _ => ω 0 • e₁)).Exceeds {0}
    (ball 0 1) ⊤} ≤ ε at hmem
  have hsub : {ω : Sample | ω 0 = 0}ᶜ ⊆
      {ω | ((drift 0).perturb (σ • fun _ => ω 0 • e₁)).Exceeds {0} (ball 0 1) ⊤} := by
    intro ω hω
    have hp : (σ • fun _ : EuclideanSpace ℝ (Fin 1) => ω 0 • e₁) = fun _ => (σ * ω 0) • e₁ := by
      funext x
      simp [smul_smul]
    show ((drift 0).perturb (σ • fun _ => ω 0 • e₁)).Exceeds {0} (ball 0 1) ⊤
    rw [hp, drift_perturb]
    exact noisyDrift_exceeds hσ hω
  have h1 : (1 : ℝ≥0∞) ≤ gaussianSample {ω : Sample | ω 0 = 0}ᶜ := by
    have := measure_univ_le_add_compl (μ := gaussianSample) {ω : Sample | ω 0 = 0}
    rwa [measure_univ, gaussianSample_zero, zero_add] at this
  exact absurd (h1.trans ((measure_mono hsub).trans hmem)) (not_le.mpr hε1)

/-- **Over every finite horizon a small intensity is safe.** For every horizon `T₀` and positive
level `ε < 1` there is a threshold `σ₀ > 0` below which the disturbed drift is safe before `T₀`
at the level `ε` (`noisy_realizationSoundUnder_safe`: the design is Lipschitz and solvable, the
margin holds, the Gaussian coordinate exceeds some `k` with probability below `ε`, and
`|σ| k T₀ ≤ 1/2` for `|σ| ≤ σ₀`). With `noisyDrift_not_mem_den_top` the two limits do not
commute: `σ₀` depends on `T₀` and no positive threshold serves every horizon. -/
@[tmio TM, powerlib_domain] theorem noisyDrift_mem_den_finite {ε : ℝ≥0∞} (hε : 0 < ε) (hε1 : ε < 1) :
    connection% (∀ T₀ : ℝ, 0 ≤ T₀ → ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, |σ| ≤ σ₀ →
      noisyDrift σ ∈ driftImpl.impl.den (.envelope (.safe (ENNReal.ofReal T₀) ε))) := by
  unfold powerlib.TMIO.Statement
  intro T₀ hT₀
  -- A bound `k` on the Gaussian coordinate, exceeded with probability below `ε`.
  have hanti : Antitone fun k : ℕ => {ω : Sample | (k : ℝ) < |ω 0|} :=
    fun i j hij ω (hω : (j : ℝ) < |ω 0|) =>
      (show (i : ℝ) < |ω 0| from (Nat.cast_le.mpr hij).trans_lt hω)
  have hinter : ⋂ k : ℕ, {ω : Sample | (k : ℝ) < |ω 0|} = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    obtain ⟨k, hk⟩ := exists_nat_ge |ω 0|
    exact lt_irrefl _ ((mem_iInter.mp hω k).trans_le hk)
  have ht := tendsto_measure_iInter_atTop (μ := gaussianSample)
    (fun k => (measurableSet_lt measurable_const
      (by fun_prop : Measurable fun ω : Sample => |ω 0|)).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨1 / (2 * (k * T₀ + 1)), by positivity, fun σ hσ => ?_⟩
  have hsound := noisy_realizationSoundUnder_safe driftDesign_isDesign (K := 0) (W := k)
    (T₀ := T₀) hε1
  unfold powerlib.TMIO.Statement at hsound
  refine hsound ⟨?_, ?_⟩
  · change noisyDrift σ ∈ certify (Implementation.ofDesign Noisy.design) (driftDesign.den _)
    rw [Implementation.certify_ofDesign, mem_preimage]
    exact mem_den_driftDesign _ _
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact LipschitzWith.const _
    · intro x₀ hx₀
      refine ⟨fun _ => x₀, rfl, fun τ _ => ?_⟩
      rw [mem_singleton_iff.mp hx₀]
      simpa [drift] using hasDerivWithinAt_const τ (Icc 0 T₀) (0 : EuclideanSpace ℝ (Fin 1))
    · exact ball_half_subset_erode
    · refine ⟨Nat.cast_nonneg k, ?_⟩
      change gronwallBound 0 0 (|σ| * k) T₀ ≤ 1 / 2
      simp only [gronwallBound_K0, zero_add]
      have hk0 : (0 : ℝ) ≤ k * T₀ := mul_nonneg (Nat.cast_nonneg k) hT₀
      calc |σ| * k * T₀ = |σ| * (k * T₀) := by ring
        _ ≤ 1 / (2 * (k * T₀ + 1)) * (k * T₀) := by gcongr
        _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    · refine le_trans (measure_mono fun ω hω => ?_) hk.le
      obtain ⟨x, hx⟩ := hω
      simpa [noisyDrift, norm_smul_e₁] using hx

/-- **No intensity bound realizes infinite-horizon safety.** For every `σ₀ > 0` and level
`ε < 1`, the realization of safety over the infinite horizon is not sound within the Lipschitz
design, the margin and the intensity bound `σ₀`: the disturbed drift with intensity `σ₀` is a
witness (`noisyDrift_not_mem_den_top`). -/
@[tmio MI, powerlib_domain] theorem not_driftImpl_realizationSoundUnder_top {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {ε : ℝ≥0∞} (hε1 : ε < 1) :
    connection% (¬ driftImpl.RealizationSoundUnder {.lipschitz 0, .margin, .intensityAtMost σ₀}
      (.envelope (.safe ⊤ ε))) := by
  unfold powerlib.TMIO.Statement
  have hy := noisyDrift_not_mem_den_top hσ₀.ne' hε1
  have hd := mem_den_driftDesign ⊤ ε
  unfold powerlib.TMIO.Statement at hy hd
  refine Implementation.not_realizationSoundUnder_of_design (I := driftImpl) (y := noisyDrift σ₀)
    rfl hd ?_ hy
  rw [(connection_proof% TMIO.mem_realize)]
  intro q hq
  simp only [mem_insert_iff, mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact LipschitzWith.const _
  · exact ball_half_subset_erode
  · exact (abs_of_pos hσ₀).le

end powerlib.Envelope
