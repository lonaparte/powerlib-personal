import theorem.Spectral.Local
import theorem.Dynamics.Transport
import theorem.TMIO.ClaimElab

/-! # Hub families: a spoke family read through a hub family (foundation)

Several model families of the library are other families in disguise: the droop loop with a power
filter, the saturated converter and the classical machine are swing machines in other state
coordinates; the port-Hamiltonian PLL is the PI-PLL. The disguised family (the spoke) keeps its
own requirement language — balance, positive droop gains, a negative saturated slope — while the
laws are proved once on the other family (the hub). This module transfers them: a map of models
`g` from the spoke to the hub with, on a context, the same denotations (a reading) and
corresponding requirements carries exactness within a context, soundness and requirement
obligations from the hub to the spoke. A reading is usually an affine change of state
coordinates, under which every flow sentence is invariant (`Dynamics.holds_transport_iff`).

Scope.
* A generic template, not a model: arbitrary families `F : Family X Q n p` (the spoke) and
  `G : Family Y R m r` (the hub), continuous or discrete, with or without ports, with arbitrary
  requirement languages; the readings by conjugacy (`mem_den_flow_iff_of_transport`) need the same
  state dimension and read the flow sentences on a field at a point, as in
  `theorem/Spectral/Local.lean`.
* Readings and requirement correspondences are hypotheses on a context of the spoke, so a reading
  that needs nonzero gains (an invertible coordinate change) is used only where they hold.
* Families of `Type` (model and requirement types in `Type`): the transfer laws are connection
  statements about arbitrary families, and a connection statement binds types of `Type`.

Source: Agda scaffold `theorem/FamilyReading.agda`, the generic pattern (a spoke read through a hub:
univalence turns the readings into a path from the spoke's semantics to the hub's pulled back
along the map, and exactness and soundness pass under a correspondence of requirement languages on
a context); each reading has its own scaffold named after its two families, listed in the
scaffold table of `Architecture.md`. `Family.comap` (`theorem/Family/Basic.lean`) is the case of a
spoke that keeps the hub's language.

Results.
* `mem_den_flow_iff_of_transport` (an affine conjugacy of fields is a reading of the flow
  sentences; its hypotheses read the sentences on fields, so it stays a foundation lemma).

Family and connection conclusions.
* Transfer laws, connection statements about arbitrary families of `Type` (stated once; model
  modules instantiate them): `realize_subset_den_of_hub` (a requirement obligation
  `realize A ⊆ den s` of the spoke from the hub's), `sound_of_hub`, `exactUnder_of_hub`,
  `exact_of_hub` (exactness passes from the hub to the spoke), `mem_den_iff_of_flow` (a reading
  of the flow sentences of autonomous families is a reading of every sentence).
-/

noncomputable section

namespace powerlib.Spectral

open TMIO Set

variable {X Y Q R : Type} {n m p r : ℕ} {F : Family X Q n p} {G : Family Y R m r}

/-! ## Transfer along a map of models -/

/-- A requirement obligation of the spoke from one of the hub: the models of `A` map into the
models of `B`, which satisfy `s` in the hub, and a model satisfies `s` when its image does. -/
@[tmio TM, powerlib_domain] theorem realize_subset_den_of_hub (g : X → Y) {A : Set Q} {B : Set R}
    {s : Sentence} (hreq : ∀ x ∈ realize F.meets A, g x ∈ realize G.meets B)
    (hden : ∀ x ∈ realize F.meets A, g x ∈ G.den s → x ∈ F.den s)
    (hG : realize G.meets B ⊆ G.den s) : connection% (realize F.meets A ⊆ F.den s) := by
  unfold powerlib.TMIO.Statement
  exact fun x hx => hden x hx (hG (hreq x hx))

/-- Soundness passes from the hub to the spoke when the spoke's translated requirements give the
hub's. -/
@[tmio TM, powerlib_domain] theorem sound_of_hub (g : X → Y) {s : Sentence}
    (hreq : ∀ x ∈ realize F.meets (F.translate s), g x ∈ realize G.meets (G.translate s))
    (hden : ∀ x ∈ realize F.meets (F.translate s), g x ∈ G.den s → x ∈ F.den s)
    (hG : G.Sound s) : connection% (F.Sound s) := by
  unfold powerlib.TMIO.Statement
  exact realize_subset_den_of_hub g hreq hden hG

/-- Exactness within a context passes from the hub to the spoke: the spoke's context maps into
the hub's, and on it the map reads `s` and the translated requirements of the two families
correspond. -/
@[tmio TM, powerlib_domain] theorem exactUnder_of_hub (g : X → Y) {ΔF : Set Q} {ΔG : Set R}
    {s : Sentence} (hΔ : ∀ x ∈ realize F.meets ΔF, g x ∈ realize G.meets ΔG)
    (hden : ∀ x ∈ realize F.meets ΔF, (x ∈ F.den s ↔ g x ∈ G.den s))
    (hreq : ∀ x ∈ realize F.meets ΔF,
      (x ∈ realize F.meets (F.translate s) ↔ g x ∈ realize G.meets (G.translate s)))
    (hG : G.ExactUnder ΔG s) : connection% (F.ExactUnder ΔF s) := by
  unfold powerlib.TMIO.Statement
  rw [exactUnder_iff_forall] at hG ⊢
  intro x hx
  rw [hreq x hx, hden x hx]
  exact hG (g x) (hΔ x hx)

/-- Exactness of the hub within a context passes to exactness of the spoke when every spoke model
maps into that context. -/
@[tmio TM, powerlib_domain] theorem exact_of_hub (g : X → Y) {ΔG : Set R} {s : Sentence}
    (hΔ : ∀ x, g x ∈ realize G.meets ΔG) (hden : ∀ x, (x ∈ F.den s ↔ g x ∈ G.den s))
    (hreq : ∀ x, (x ∈ realize F.meets (F.translate s) ↔ g x ∈ realize G.meets (G.translate s)))
    (hG : G.ExactUnder ΔG s) : connection% (F.Exact s) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_exactUnder_empty
    (exactUnder_of_hub g (fun x _ => hΔ x) (fun x _ => hden x) (fun x _ => hreq x) hG)

/-! ## Readings -/

/-- For autonomous families a reading of the flow sentences reads every sentence: neither family
has a port, so both are passive, and neither has an envelope. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_of_flow {F : Family X Q n 0} {G : Family Y R m 0}
    {f : X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {φ : Y → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)} (hF : F.IsAutonomous f)
    (hG : G.IsAutonomous φ) {g : X → Y} {x : X}
    (h : ∀ P : Flow.Property, x ∈ F.den (.flow P) ↔ g x ∈ G.den (.flow P)) (s : Sentence) :
    connection% (x ∈ F.den s ↔ g x ∈ G.den s) := by
  unfold powerlib.TMIO.Statement
  rcases s with P | _ | E
  · exact h P
  · rw [hF.den_passive, hG.den_passive]
    exact iff_of_true trivial trivial
  · rw [hF.den_envelope, hG.den_envelope]
    exact iff_of_true trivial trivial

/-- An affine conjugacy of fields reads the flow sentences: when the spoke's field at `x` is the
hub's field at `g x` in the coordinates `y = T z + c`, and the spoke's point is the image of the
hub's, `x` and `g x` satisfy the same flow sentences. -/
@[tmio TM, powerlib_foundation] theorem mem_den_flow_iff_of_transport {G : Family Y R n r}
    {f : X → Dynamics.State n → Dynamics.State n} {pt : X → Dynamics.State n}
    {φ : Y → Dynamics.State n → Dynamics.State n} {ψ : Y → Dynamics.State n}
    (hdenF : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    (hdenG : ∀ y (P : Flow.Property), y ∈ G.den (.flow P) ↔ P.holds (φ y) (ψ y))
    {g : X → Y} {x : X} (T : Dynamics.State n ≃L[ℝ] Dynamics.State n) (c : Dynamics.State n)
    (hf : f x = Dynamics.transportField T c (φ (g x)))
    (hpt : pt x = Dynamics.affineCoord T c (ψ (g x))) (P : Flow.Property) :
    x ∈ F.den (.flow P) ↔ g x ∈ G.den (.flow P) := by
  rw [hdenF, hdenG, hf, hpt, Dynamics.holds_transport_iff]

end powerlib.Spectral
