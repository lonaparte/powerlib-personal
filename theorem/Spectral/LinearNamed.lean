import theorem.Spectral.Global
import theorem.Linear.Family
import theorem.Linear.Rate

/-! # Linear families with named requirement languages (foundation)

`Spectral.linearFamily` (`theorem/Spectral/Family.lean`) reads every complete system as the port
system of its linear plant with the two-element language `{stable, unstable}`. The frequency,
current-loop and digital-platform families read their members the same way and re-proved the laws
of the linear table one by one, with requirement languages of their own. This module states those
laws once, as the instance of the table `Spectral.table` (`theorem/Spectral/Local.lean`) in which
a Hurwitz state matrix decides every attractive sentence. The families whose requirements are a
static stability condition, a static instability condition and a decay margin at each rate share
one language and one family constructor, `rateFamily`; the earlier choice to keep a separate
language per family (Routh–Hurwitz conditions in the parameters, a matrix language with a spectral
rate margin) is withdrawn: the frequency families are its instances (each keeps its conditions
`S`, `U`, `R`). Families with platform constraints or physical contexts keep named languages and
use the linear table directly.

Scope.
* A generic template, not a model: an arbitrary family `F : Family X Q n p` that is linear
  (`Family.IsLinear plant`: every member is the port system of its plant), an arbitrary
  requirement language `Q` and requirement sets. The obligations are static conditions on the
  state matrix (Hurwitz, a characteristic root in the open right half plane) and, for decay
  rates, conservation and passivity, on denotations.

Source: the linear hub `theorem/Linear/Stability.lean` (`holds_iff_isHurwitz`,
`sampledContraction_iff_isHurwitz`), `theorem/Linear/Family.lean` (`IsLinear.den_hurwitz`) and
strict rate margins (`theorem/Linear/Rate.lean`); the
families of `theorem/PowerSystem/Frequency/` and
`theorem/GridTiedConverter/CurrentControl/DigitalPI.lean` (audit of the library).

Results.
* The table: `linearTable Rs Ru Rc Rp Rd` — Lyapunov stability, the attractive sentences and
  sampled contraction to `Rs`, instability to `Ru`, conservation to `Rc`, passivity to `Rp`, decay
  at the rate `a` to `Rd a`; it is `globalTable Rs Rs Ru Rc Rp Rd`. The common table sends
  conservation and passivity to the whole language (`Rc = Rp = univ`, unavailable coverage)
  (`linearTable_flow`: the attractive and contractive values).
* Soundness: `chain_le_semantics_of_linearTable`, when `Rs` gives a Hurwitz state matrix, `Ru` a
  characteristic root in the open right half plane, `Rd a` decay at the rate `a`, `Rc`
  conservation and `Rp` passivity; `chain_le_semantics_of_linearTable_univ`, the common table, in
  which the whole language is inconsistent by itself (`realize_univ_of_linearTable`).
* Exactness: `exactUnder_of_linearTable` (within a context on which `Rs` is equivalent to the
  Hurwitz property, the attractive and contractive translations are exact) and
  `exact_of_linearTable` (without a context).
* Linear rate families: the language `RateRequirement` (`stable`, `unstable`, `rate a`), its
  satisfaction `RateMeets S U R`, the translation `rateTranslate` (the linear table on it) and the
  constructor `rateFamily plant S U R` (`rateFamily_isLinear`); `MeetsMatrix A`, the language read
  on a state matrix (Hurwitz, a right-half-plane root, a strict spectral margin). For every linear
  family with this language and translation: `realize_univ_of_rate` (inconsistency of the whole
  language), `chain_le_semantics_of_rate` (soundness of every translation when `stable` gives a
  Hurwitz matrix, `unstable` a right-half-plane root and `rate a` a strict margin at `a`) and
  `exact_of_rate` (with `stable` equivalent to the Hurwitz property, the attractive and
  contractive translations are exact).

Family and connection conclusions.
* `chain_le_semantics_of_linearTable` and `chain_le_semantics_of_rate` are generic foundation
  connections establishing translation soundness. Model modules instantiate them for their own
  engineering conclusions.
-/

noncomputable section

namespace powerlib.Spectral

open TMIO Set Matrix Linear LinearSystems

variable {X Q : Type*} {n p : ℕ}

/-- The table of a linear family with named requirements: Lyapunov stability, the attractive
sentences and sampled contraction to `Rs`, instability to `Ru`, conservation to `Rc`, passivity to
`Rp`, decay at the rate `a` to `Rd a`. -/
abbrev linearTable (Rs Ru Rc Rp : Set Q) (Rd : ℝ → Set Q) : Sentence → Set Q :=
  table Rs Rs Rs Ru Rc Rp Rd ∅

/-- The attractive sentences and sampled contraction are translated into `Rs`. -/
@[tmio T, powerlib_foundation] theorem linearTable_flow {Rs Ru Rc Rp : Set Q} {Rd : ℝ → Set Q}
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (generate (cover (TMIO.table (linearTable Rs Ru Rc Rp Rd))) {Sentence.flow P} =
      Rs) := by
  unfold TMIO.Statement
  rw [image_table_singleton]
  rcases hP with hP | rfl
  · cases P <;> first | rfl | exact hP.elim
  · rfl

section Linear

variable {F : Family X Q n p} {plant : X → Plant n p} {Rs Ru Rc Rp : Set Q} {Rd : ℝ → Set Q}

/-- A requirement set giving a Hurwitz state matrix and one giving a right-half-plane root are
mutually exclusive, so the whole language is inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ_of_linearTable
    (hS : ∀ x ∈ realize F.meets Rs, IsHurwitz (plant x).A)
    (hU : ∀ x ∈ realize F.meets Ru,
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re) :
    connection% (realize F.meets univ = ∅) := show realize F.meets univ = ∅ from
  realize_univ_eq_empty_of_forall fun x h => by
    have hx : x ∈ realize F.meets univ := (mem_realize _ _ _).mpr fun q _ => h q
    obtain ⟨s, hs, hre⟩ := hU x (realize_antitone _ (subset_univ _) hx)
    exact absurd ((spectrallyStable_iff_isHurwitz _).mpr
      (hS x (realize_antitone _ (subset_univ _) hx)) s hs) (not_lt.mpr hre.le)

/-- Soundness of every translation of a linear family with the linear table: `Rs` gives a
Hurwitz state matrix, `Ru` a characteristic root in the open right half plane, `Rd a` decay at
the rate `a`, `Rc` conservation and `Rp` passivity. -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics_of_linearTable (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru Rc Rp Rd s)
    (hS : ∀ x ∈ realize F.meets Rs, IsHurwitz (plant x).A)
    (hU : ∀ x ∈ realize F.meets Ru,
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re)
    (hD : ∀ a, realize F.meets (Rd a) ⊆ F.den (.flow (.decay a)))
    (hC : realize F.meets Rc ⊆ F.den (.flow .conservative))
    (hP : realize F.meets Rp ⊆ F.den .passive) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hG : realize F.meets Rs ⊆ F.den (.flow .globallyExponentiallyStable) := fun x hx =>
    hF.mem_den_flow.mpr (holds_of_isHurwitz 0 trivial (hS x hx))
  exact chain_le_semantics_of_globalTable ht
    (fun x hx => den_globallyExponentiallyStable_subset_les (hG hx)) hG hD
    (fun x hx => by
      obtain ⟨s, hs, hre⟩ := hU x hx
      exact hF.mem_den_flow.mpr (unstable_of_root 0 hs hre)) hC hP hF.den_envelope

/-- The common table: conservation and passivity are translated into the whole language, which
`Rs` and `Ru` make inconsistent. -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics_of_linearTable_univ (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru univ univ Rd s)
    (hS : ∀ x ∈ realize F.meets Rs, IsHurwitz (plant x).A)
    (hU : ∀ x ∈ realize F.meets Ru,
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re)
    (hD : ∀ a, realize F.meets (Rd a) ⊆ F.den (.flow (.decay a))) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := show ∀ P, F.chain P ≤ F.semantics P from
  chain_le_semantics_of_linearTable hF ht hS hU hD
    (realize_univ_subset_of_eq_empty (realize_univ_of_linearTable hS hU) _)
    (realize_univ_subset_of_eq_empty (realize_univ_of_linearTable hS hU) _)

/-- Exactness within a context: where `Rs` is equivalent to the Hurwitz property of the state
matrix, the attractive and contractive translations are exact. -/
@[tmio TM, powerlib_foundation] theorem exactUnder_of_linearTable (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru Rc Rp Rd s) (Δ : Set Q)
    (hS : ∀ x ∈ realize F.meets Δ, (x ∈ realize F.meets Rs ↔ IsHurwitz (plant x).A))
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (F.ExactUnder Δ (.flow P)) := by
  change F.ExactUnder Δ (.flow P)
  refine exactUnder_iff_forall.mpr fun x hΔ => ?_
  rw [ht, ← image_table_singleton (linearTable Rs Ru Rc Rp Rd) (.flow P),
    linearTable_flow hP, hF.den_hurwitz hP, mem_ofPred_eq]
  exact hS x hΔ

/-- Exactness: with `Rs` equivalent to the Hurwitz property of the state matrix, the attractive
and contractive translations are exact. -/
@[tmio TM, powerlib_foundation] theorem exact_of_linearTable (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru Rc Rp Rd s)
    (hS : ∀ x, x ∈ realize F.meets Rs ↔ IsHurwitz (plant x).A)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (F.Exact (.flow P)) := show F.Exact (.flow P) from
  exact_of_exactUnder_empty (exactUnder_of_linearTable hF ht ∅ (fun x _ => hS x) hP)

end Linear

/-! ## Linear rate families -/

/-- The requirements of a linear rate family: its static stability condition, its static
instability condition and a decay margin at each rate. -/
inductive RateRequirement
  /-- The model's static stability condition. -/
  | stable
  /-- The model's static instability condition. -/
  | unstable
  /-- A decay margin at the rate `a`. -/
  | rate (a : ℝ)

/-- Satisfaction of the rate requirements through the static conditions `S` and `U` and the rate
condition `R`. -/
def RateMeets (S U : X → Prop) (R : X → ℝ → Prop) (x : X) : RateRequirement → Prop
  | .stable => S x
  | .unstable => U x
  | .rate a => R x a

/-- The translation of a linear rate family, the linear table on the rate language: Lyapunov
stability, the attractive sentences and sampled contraction to `stable`, instability to
`unstable`, decay at the rate `a` to `rate a`, conservation and passivity to the whole
(inconsistent) language, the envelope sentences to nothing. -/
def rateTranslate : Sentence → Set RateRequirement :=
  linearTable {.stable} {.unstable} univ univ fun a => {.rate a}

/-- A linear rate family: every complete system read as the port system of its plant, with the
rate language satisfied through `S`, `U` and `R`. -/
def rateFamily (plant : X → Plant n p) (S U : X → Prop) (R : X → ℝ → Prop) :
    Family X RateRequirement n p :=
  ⟨fun x => (plant x).system, RateMeets S U R, rateTranslate⟩

@[tmio M, powerlib_foundation] theorem rateFamily_isLinear (plant : X → Plant n p)
    (S U : X → Prop) (R : X → ℝ → Prop) : (rateFamily plant S U R).IsLinear plant := fun _ => rfl

/-- The rate language read on a state matrix: the Hurwitz property, a characteristic root in the
open right half plane, a strict spectral margin (`Linear.RateMargin`). -/
def MeetsMatrix (A : Matrix (Fin n) (Fin n) ℝ) : RateRequirement → Prop :=
  RateMeets (fun A => IsHurwitz A)
    (fun A => ∃ s : ℂ, (characteristicMatrix A s).det = 0 ∧ 0 < s.re) RateMargin A

section Rate

variable {F : Family X RateRequirement n p} {plant : X → Plant n p}

/-- A stability condition giving a Hurwitz state matrix and an instability condition giving a
right-half-plane root make the rate language inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ_of_rate
    (hS : ∀ x, F.meets x .stable → IsHurwitz (plant x).A)
    (hU : ∀ x, F.meets x .unstable →
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re) :
    connection% (realize F.meets univ = ∅) :=
  realize_univ_of_linearTable (Rs := {.stable}) (Ru := {.unstable})
    (fun x hx => hS x (mem_realize_singleton.mp hx))
    (fun x hx => hU x (mem_realize_singleton.mp hx))

/-- Soundness of every translation of a linear family with the rate language and its table
(`rateFamily`, or any linear family read through it): `stable` gives a Hurwitz state matrix,
`unstable` a right-half-plane root, `rate a` a strict spectral margin at `a`. -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics_of_rate (hF : F.IsLinear plant)
    (htr : F.translate = rateTranslate) (hS : ∀ x, F.meets x .stable → IsHurwitz (plant x).A)
    (hU : ∀ x, F.meets x .unstable →
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re)
    (hR : ∀ x a, F.meets x (.rate a) → RateMargin (plant x).A a) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := show ∀ P, F.chain P ≤ F.semantics P from
  chain_le_semantics_of_linearTable_univ hF (congrFun htr)
    (fun x hx => hS x (mem_realize_singleton.mp hx))
    (fun x hx => hU x (mem_realize_singleton.mp hx))
    fun a x hx => hF.mem_den_decay_of_rateMargin (hR x a (mem_realize_singleton.mp hx))

/-- Exactness of the rate language: with `stable` equivalent to the Hurwitz property of the state
matrix, the attractive and contractive translations are exact. -/
@[tmio TM, powerlib_foundation] theorem exact_of_rate (hF : F.IsLinear plant)
    (htr : F.translate = rateTranslate) (hS : ∀ x, F.meets x .stable ↔ IsHurwitz (plant x).A)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (F.Exact (.flow P)) := show F.Exact (.flow P) from
  exact_of_linearTable hF (congrFun htr) (fun x => mem_realize_singleton.trans (hS x)) hP

end Rate

end powerlib.Spectral
