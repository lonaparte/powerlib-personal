import theorem.Criteria.Hurwitz2
import theorem.Linear.Family
import theorem.TMIO.ClaimElab

/-! # Single-input single-output plant helpers and spectral families (foundation)

Shared helpers for the converter current-loop, DC-link and feedforward modules
(`theorem/CurrentControl/`, `theorem/DCLink/`). Nothing here describes a physical system.

* `transfer_fin_one`, `transfer_fin_two`: closed forms of `Linear.transfer` for one- and
  two-state single-input single-output plants `⟨A, B, C, D⟩` (one port), off the
  characteristic roots. These are plain resolvent computations (adjugate of a 1×1 / 2×2
  matrix).
* `negOutput`, `transfer_negOutput`: reversing the output sign of a plant negates its transfer
  matrix. With the output read as a port current, this is the `Y^IN = −Y^OUT` translation
  between the IN-positive and OUT-positive current conventions (work-sync
  `theory/T-gfl-impedance.md` §1.4 / §2.2, `conventions.md` §D8).
* `tendsto_equilibrium`: under a constant input with an equilibrium `e`, every forward-complete
  solution of a plant with a Hurwitz state matrix converges to `e` (the hub's global asymptotic
  stability, `Linear.globallyAsymptoticallyStable_of_isHurwitz`, about the shifted
  equilibrium). It replaces the former `isTrajectory_sub_equilibrium`,
  `tendsto_of_exponentiallyStable` and `tendsto_equilibrium` on the deleted `LTI` models.

## Spectral families

Many model families of the converter modules are decided by the spectrum of one state matrix: a
static parameter condition makes it Hurwitz, another places a characteristic root in the open
right half plane. `Spectral` packages that shape once, for an arbitrary type `X` of complete
systems, with the generic requirement language `Spectral.Requirement` (`stable`, `unstable`)
whose satisfaction is supplied by the static conditions `S` and `U` of the model:
* `Spectral.linearFamily plant S U` reads every complete system as the port system of its linear
  plant (`Family.IsLinear`). Its translation sends the attractive sentences, sampled contraction
  and Lyapunov stability to `stable`, instability to `unstable`, and decay at a prescribed rate,
  conservation and passivity — which these conditions do not decide — to the whole (inconsistent)
  language: unavailable coverage, not a usable translation. `linear_chain_le_semantics` proves
  every translation sound when `S` gives a Hurwitz matrix and `U` a right-half-plane root;
  `linear_exact` proves the attractive and contractive translations exact when `S` is equivalent
  to the Hurwitz property.
* `Spectral.localFamily field S U` reads every complete system as the autonomous field `field x`
  (already translated so that the selected operating point is the origin). Its translation sends
  the local sentences to `stable`, instability to `unstable`, passivity to nothing and the global
  sentences, decay rates, sampled contraction and conservation to the whole language.
  `local_chain_le_semantics` proves every translation sound when `S` gives local exponential
  stability and `U` instability of the field at the origin; `local_exact_passive` is exact.

These are generic statements about arbitrary families of the two shapes: foundation results. A
model module instantiates them and publishes its conclusions as connection statements.

Source: standard state-space algebra, used by work-sync `theory/T-gfl-control.md` §1.4,
`theory/T-gfl-impedance.md` §1.4–§1.5, `theory/T-voltage-feedforward.md` §2.2,
`theory/T-vsc-dc-voltage-control.md` §1.4.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter Linear LinearSystems
open scoped Topology

/-- Transfer function of a one-state SISO plant `⟨[a], [b], [c], [d]⟩`:
`c b / (s − a) + d` for `s ≠ a`. -/
@[powerlib_foundation] theorem transfer_fin_one (a b c d : ℝ) {s : ℂ} (hs : s - a ≠ 0) :
    transfer (⟨!![a], !![b], !![c], !![d]⟩ : Plant 1 1) s 0 0 =
      (c : ℂ) * b / (s - a) + d := by
  simp [transfer, characteristicMatrix, Matrix.mul_apply]
  field_simp

/-- Characteristic determinant of a 2×2 state matrix in the literal form `!![a, b; c, d]`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_of (a b c d : ℝ) (s : ℂ) :
    (characteristicMatrix !![a, b; c, d] s).det = (s - a) * (s - d) - (b : ℂ) * c := by
  simp [characteristicMatrix, Matrix.det_fin_two]

/-- Transfer function of a two-state SISO plant, off the characteristic roots. -/
@[powerlib_foundation] theorem transfer_fin_two (a b c d b1 b2 c1 c2 d0 : ℝ) {s : ℂ}
    (hs : (s - a) * (s - d) - (b : ℂ) * c ≠ 0) :
    transfer (⟨!![a, b; c, d], !![b1; b2], !![c1, c2], !![d0]⟩ : Plant 2 1) s 0 0 =
      ((c1 : ℂ) * ((s - d) * b1 + b * b2) + c2 * (c * b1 + (s - a) * b2)) /
        ((s - a) * (s - d) - b * c) + d0 := by
  simp only [transfer, Matrix.inv_def, Ring.inverse_eq_inv', det_characteristicMatrix_of]
  simp [characteristicMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

section Sign

variable {n p : ℕ}

/-- The same plant with the output (and feedthrough) sign reversed. -/
def negOutput (m : Plant n p) : Plant n p := ⟨m.A, m.B, -m.C, -m.D⟩

/-- Reversing the output sign negates the transfer matrix. Read with the output as a port
current: `Y^IN(s) = −Y^OUT(s)`. -/
@[powerlib_foundation] theorem transfer_negOutput (m : Plant n p) (s : ℂ) :
    transfer (negOutput m) s = -transfer m s := by
  simp only [transfer, negOutput, complexify_neg, Matrix.neg_mul, neg_add]

@[powerlib_foundation] theorem negOutput_negOutput (m : Plant n p) :
    negOutput (negOutput m) = m := by
  simp [negOutput]

end Sign

section Trajectory

variable {n p : ℕ}

/-- Constant-input solutions of a plant with a Hurwitz state matrix converge to the
equilibrium: generic foundation, the hub's global asymptotic stability about `e`. -/
@[powerlib_foundation] theorem tendsto_equilibrium (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ : ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Set.Ici t₀)) :
    Tendsto x atTop (𝓝 e) := by
  rw [M.inputField_eq he] at hx
  exact (globallyAsymptoticallyStable_of_isHurwitz e hA).2.2.2 t₀ x hx

/-- Componentwise form, for a solution given by its derivative at every time. -/
@[powerlib_foundation] theorem tendsto_equilibrium_apply (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} (hx : ∀ t, HasDerivAt x (M.inputField u (x t)) t)
    (j : Fin n) : Tendsto (fun t => x t j) atTop (𝓝 (e j)) := by
  have h := tendsto_equilibrium M hA he (t₀ := 0) fun t _ => (hx t).hasDerivWithinAt
  exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.tendsto
    e).comp h

end Trajectory

end powerlib.CurrentControl

/-! ## Spectral families -/

namespace powerlib.Spectral

open Matrix Linear LinearSystems TMIO

/-- Requirements of a family decided by the spectrum of a state matrix. -/
inductive Requirement
  /-- The model's static stability condition. -/
  | stable
  /-- The model's static instability condition. -/
  | unstable

variable {X : Type*} {n p : ℕ}

/-- Satisfaction of the two requirements through the static conditions `S` and `U`. -/
def Meets (S U : X → Prop) (x : X) : Requirement → Prop
  | .stable => S x
  | .unstable => U x

@[simp, powerlib_foundation] theorem meets_stable {S U : X → Prop} {x : X} :
    Meets S U x .stable ↔ S x := Iff.rfl

@[simp, powerlib_foundation] theorem meets_unstable {S U : X → Prop} {x : X} :
    Meets S U x .unstable ↔ U x := Iff.rfl

/-- No member meets both requirements when they are mutually exclusive. -/
@[powerlib_foundation] theorem realize_univ_of {S U : X → Prop} (h : ∀ x, S x → U x → False) :
    realize (Meets S U) Set.univ = ∅ := by
  ext x
  simp only [mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact h x (hx .stable) (hx .unstable)

/-! ### Linear families -/

/-- The translation of a linear spectral family. -/
def linearTranslate : Sentence → Set Requirement
  | .flow .unstable => {.unstable}
  | .flow (.decay _) | .flow .conservative | .passive => Set.univ
  | .flow _ => {.stable}

/-- A linear spectral family: every complete system read as the port system of its plant. -/
def linearFamily (plant : X → Plant n p) (S U : X → Prop) : Family X Requirement n p :=
  ⟨fun x => (plant x).system, Meets S U, linearTranslate⟩

@[powerlib_foundation] theorem linearFamily_isLinear (plant : X → Plant n p) (S U : X → Prop) :
    (linearFamily plant S U).IsLinear plant := fun _ => rfl

variable {plant : X → Plant n p} {S U : X → Prop}

/-- A Hurwitz state matrix has no characteristic root in the closed right half plane. -/
@[powerlib_foundation] theorem not_root_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {s : ℂ} (hs : (characteristicMatrix A s).det = 0) : s.re < 0 :=
  (spectrallyStable_iff_isHurwitz A).mpr hA s hs

/-- Soundness of every translation of a linear spectral family: the stability condition gives a
Hurwitz state matrix, the instability condition a characteristic root in the open right half
plane. -/
@[powerlib_foundation] theorem linear_chain_le_semantics
    (hS : ∀ x, S x → IsHurwitz (plant x).A)
    (hU : ∀ x, U x → ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re) :
    ∀ P, (linearFamily plant S U).chain P ≤ (linearFamily plant S U).semantics P := by
  have hF := linearFamily_isLinear plant S U
  have hnone : realize (Meets S U) Set.univ = ∅ := realize_univ_of fun x h1 h2 => by
    obtain ⟨s, hs, hre⟩ := hU x h2
    exact absurd (not_root_of_isHurwitz (hS x h1) hs) (not_lt.mpr hre.le)
  refine Family.chain_le_semantics_iff.mpr fun s x hx => ?_
  rw [mem_realize] at hx
  change ∀ q ∈ linearTranslate s, Meets S U x q at hx
  have huniv : (∀ q, Meets S U x q) → False := fun h => by
    have hx' : x ∈ realize (Meets S U) Set.univ := (mem_realize _ _ _).mpr fun q _ => h q
    rw [hnone] at hx'
    exact hx'
  have hstab : linearTranslate s = {.stable} → IsHurwitz (plant x).A := fun h =>
    hS x (hx .stable (by rw [h]; rfl))
  rcases s with P | _
  · rw [hF.mem_den_flow]
    cases P
    case unstable =>
      obtain ⟨r, hr, hre⟩ := hU x (hx .unstable rfl)
      exact unstable_of_root 0 hr hre
    case lyapunovStable => exact (holds_of_isHurwitz 0 (P := .locallyExponentiallyStable)
      trivial (hstab rfl)).lyapunovStable
    case locallyAsymptoticallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case locallyExponentiallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case globallyAsymptoticallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case globallyExponentiallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case contractive => exact sampledContraction_of_isHurwitz 0 (hstab rfl)
    all_goals exact (huniv fun q => hx q trivial).elim
  · exact (huniv fun q => hx q trivial).elim

/-- With a stability condition equivalent to the Hurwitz property, the attractive sentences and
sampled contraction denote exactly the members meeting it. -/
@[powerlib_foundation] theorem linear_den (hS : ∀ x, S x ↔ IsHurwitz (plant x).A)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    (linearFamily plant S U).den (.flow P) = {x | S x} := by
  rw [(linearFamily_isLinear plant S U).den_hurwitz hP]
  ext x
  exact (hS x).symm

/-- With a stability condition equivalent to the Hurwitz property, the attractive and
contractive translations are exact. -/
@[powerlib_foundation] theorem linear_exact (hS : ∀ x, S x ↔ IsHurwitz (plant x).A)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    (linearFamily plant S U).Exact (.flow P) := by
  unfold Family.Exact
  rw [linear_den hS hP]
  have ht : (linearFamily plant S U).translate (.flow P) = {.stable} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact hP.elim
    · rfl
  rw [ht]
  ext x
  simp [mem_realize, linearFamily]

/-! ### Local families -/

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The translation of a local spectral family. -/
def localTranslate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.stable}
  | .flow .unstable => {.unstable}
  | .flow _ => Set.univ
  | .passive => ∅

/-- A local spectral family: every complete system read as its autonomous field about the
selected operating point. -/
def localFamily (field : X → ℝⁿ → ℝⁿ) (S U : X → Prop) : Family X Requirement n 0 :=
  ⟨fun x => Port.System.autonomous (field x), Meets S U, localTranslate⟩

@[powerlib_foundation] theorem localFamily_isAutonomous (field : X → ℝⁿ → ℝⁿ) (S U : X → Prop) :
    (localFamily field S U).IsAutonomous field := fun _ => rfl

/-- Soundness of every translation of a local spectral family: the stability condition gives
local exponential stability of the field at the origin, the instability condition instability. -/
@[powerlib_foundation] theorem local_chain_le_semantics {field : X → ℝⁿ → ℝⁿ}
    (hS : ∀ x, S x → LocallyExponentiallyStable (field x) 0)
    (hU : ∀ x, U x → Unstable (field x) 0) :
    ∀ P, (localFamily field S U).chain P ≤ (localFamily field S U).semantics P := by
  have hF := localFamily_isAutonomous field S U
  have hnone : realize (Meets S U) Set.univ = ∅ :=
    realize_univ_of fun x h1 h2 => hU x h2 (hS x h1).lyapunovStable
  refine Family.chain_le_semantics_iff.mpr fun s x hx => ?_
  rw [mem_realize] at hx
  change ∀ q ∈ localTranslate s, Meets S U x q at hx
  have huniv : (∀ q, Meets S U x q) → False := fun h => by
    have hx' : x ∈ realize (Meets S U) Set.univ := (mem_realize _ _ _).mpr fun q _ => h q
    rw [hnone] at hx'
    exact hx'
  rcases s with P | _
  · rw [hF.mem_den_flow]
    cases P
    case lyapunovStable => exact (hS x (hx .stable rfl)).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable (hS x (hx .stable rfl))
    case locallyExponentiallyStable => exact hS x (hx .stable rfl)
    case unstable => exact hU x (hx .unstable rfl)
    all_goals exact (huniv fun q => hx q trivial).elim
  · rw [hF.den_passive]
    trivial

/-- Passivity is translated exactly in a local spectral family: a system without ports is
passive. -/
@[powerlib_foundation] theorem local_exact_passive (field : X → ℝⁿ → ℝⁿ) (S U : X → Prop) :
    (localFamily field S U).Exact .passive :=
  Family.exact_of_translate_eq_empty rfl (localFamily_isAutonomous field S U).den_passive

end powerlib.Spectral
