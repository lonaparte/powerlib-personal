import theorem.Dynamics.ConverseLinearization
import theorem.Linear.Family
import theorem.TMIO.ClaimElab

/-! # Spectral families (foundation)

Many model families of the converter modules are decided by the spectrum of one state matrix: a
static parameter condition makes it Hurwitz, another places a characteristic root in the open
right half plane. `Spectral` packages that shape once, for an arbitrary type `X` of complete
systems, with the generic requirement language `Spectral.Requirement` (`stable`, `unstable`)
whose satisfaction is supplied by the static conditions `S` and `U` of the model.

Scope.
* A generic template, not a model: the families are parametrized by an arbitrary type `X` of
  complete systems, a plant or field map and the static conditions `S`, `U`; nothing here
  describes a physical system. These are generic statements about arbitrary families of the two
  shapes: foundation results.
* The single-input single-output plant algebra the converter modules use with these templates is
  in `theorem/LTI/Plant.lean`.

Source: generic `Family` templates for the converter modules (work-sync `theory/T-gfl-control.md`
§1.4, `theory/T-gfl-impedance.md` §1.4–§1.5, `theory/T-vsc-dc-voltage-control.md` §1.4).

Results.
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
  `local_exact_locallyExponentiallyStable` proves the local exponential translation exact when
  `S` is equivalent to local exponential stability at the origin, and `local_exact_of_jacobian`
  when, for `C¹` fields, `S` is equivalent to an equilibrium at the origin with a Hurwitz Jacobian
  (converse linearization, `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`). A
  stability condition that also fixes physical signs (positive inertia, capacitance, …) is not of
  this form; such families publish the exact membership within the physical range and a
  witness that the translation itself is not exact.
* Inexactness passes along translations (`Spectral.not_exact_of_den_subset`): if a sound
  translation of `s` is not exact and a sentence `s'` with the same translation has a larger
  denotation, the translation of `s'` is not exact either; for local families a boundary witness
  of the local exponential translation is one of the local asymptotic and Lyapunov translations
  (`Spectral.local_not_exact_of_not_exact_les`).

Family and connection conclusions.
* The module defines the two family templates `Spectral.linearFamily` and `Spectral.localFamily`
  and proves their soundness and exactness laws once; it states no `connection%` conclusion of
  its own. A model module instantiates them and publishes its conclusions as connection
  statements.
-/

noncomputable section

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

/-- With a stability condition equivalent to local exponential stability of the field at the
origin, the local exponential translation of a local spectral family is exact. -/
@[powerlib_foundation] theorem local_exact_locallyExponentiallyStable {field : X → ℝⁿ → ℝⁿ}
    {S U : X → Prop} (hS : ∀ x, S x ↔ LocallyExponentiallyStable (field x) 0) :
    (localFamily field S U).Exact (.flow .locallyExponentiallyStable) := by
  unfold Family.Exact
  ext x
  rw [mem_realize, (localFamily_isAutonomous field S U).mem_den_flow]
  change (∀ q ∈ ({.stable} : Set Requirement), Meets S U x q) ↔
    LocallyExponentiallyStable (field x) 0
  simp [hS x]

/-- With a stability condition equivalent to an equilibrium at the origin with a Hurwitz
Jacobian, for `C¹` fields, the local exponential translation of a local spectral family is exact
(converse linearization, `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`). -/
@[powerlib_foundation] theorem local_exact_of_jacobian {field : X → ℝⁿ → ℝⁿ} {S U : X → Prop}
    (jac : X → Matrix (Fin n) (Fin n) ℝ) (hC : ∀ x, ContDiff ℝ 1 (field x))
    (hJ : ∀ x, fderiv ℝ (field x) 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (jac x))
    (hS : ∀ x, S x ↔ field x 0 = 0 ∧ IsHurwitz (jac x)) :
    (localFamily field S U).Exact (.flow .locallyExponentiallyStable) :=
  local_exact_locallyExponentiallyStable fun x =>
    (hS x).trans (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (hC x) (hJ x)).symm

/-! ### Inexactness along translations -/

/-- Inexactness passes along translations: if the translation of `s` is sound but not exact, a
sentence `s'` with the same translation whose denotation contains that of `s` is not translated
exactly either (a member of `den s` outside the translated space lies in `den s'`). -/
@[powerlib_foundation] theorem not_exact_of_den_subset {Y Q : Type*} {m q : ℕ}
    {F : Family Y Q m q} {s s' : Sentence} (ht : F.translate s' = F.translate s)
    (hsound : F.Sound s) (hden : F.den s ⊆ F.den s') (h : ¬ F.Exact s) : ¬ F.Exact s' := by
  intro h'
  refine h (Set.Subset.antisymm hsound fun x hx => ?_)
  have hx' := hden hx
  unfold Family.Exact at h'
  rw [← h', ht] at hx'
  exact hx'

/-- In a local spectral family whose stability condition gives local exponential stability, a
boundary witness of the local exponential translation is one of the local asymptotic and Lyapunov
translations. -/
@[powerlib_foundation] theorem local_not_exact_of_not_exact_les {field : X → ℝⁿ → ℝⁿ}
    {S U : X → Prop} (hS : ∀ x, S x → LocallyExponentiallyStable (field x) 0)
    (h : ¬ (localFamily field S U).Exact (.flow .locallyExponentiallyStable))
    {P : Flow.Property} (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable) :
    ¬ (localFamily field S U).Exact (.flow P) := by
  have hF := localFamily_isAutonomous field S U
  refine not_exact_of_den_subset (by rcases hP with rfl | rfl <;> rfl) ?_ ?_ h
  · intro x hx
    rw [mem_realize] at hx
    rw [hF.mem_den_flow]
    exact hS x (hx .stable rfl)
  · intro x hx
    rw [hF.mem_den_flow] at hx ⊢
    rcases hP with rfl | rfl
    · exact hx.lyapunovStable
    · exact Flow.locallyExponentiallyStable_localAsymptoticStable hx

end powerlib.Spectral
