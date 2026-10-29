import theorem.Dynamics.ConverseLinearization
import theorem.Map.Basic
import theorem.Dynamics.Shift
import theorem.Family.Basic
import theorem.TMIO.ClaimElab

/-! # Local families with named requirement languages (foundation)

Most model families of the library translate the local sentences in one shape, whatever their
requirement language: Lyapunov stability to one set of requirements, local asymptotic and local
exponential stability to a second (often the same), instability to a third, passivity to a fourth
(usually none), and the global sentences, decay rates, sampled contraction and conservation, which
the requirements do not decide, to the whole, inconsistent language. `Spectral.localFamily`
(`theorem/Spectral/Family.lean`) packages this shape for the two-element language
`{stable, unstable}`; the families that keep named requirements (balanced, physical,
synchronizing, …), so that they can state exactness within a physical context, re-proved its laws
one by one. This module states them once for an arbitrary requirement language.

Scope.
* A generic template, not a model: an arbitrary family `F : Family X Q n p` (continuous or
  discrete behaviour, with or without ports), an arbitrary requirement language `Q` and requirement
  sets. Obligations are stated on denotations, so each family discharges them with its own members
  (`m ∈ family.den …`) or private stability lemmas. Where a field is needed, the flow sentences
  are read on a field `f x` at a point `pt x` through a hypothesis `hden` (the translated field of
  an autonomous family at the origin, or the original field at the operating point); no new
  behavioural notion is defined.

Source: generic `Family` laws shared by the converter and machine families (audit of the library,
work-sync `theory/T-small-signal-stability.md` §1 for the local sentences, converse linearization
`theorem/Dynamics/ConverseLinearization.lean`).

Results.
* Denotations: `den_locallyExponentiallyStable_subset_las`, `den_las_subset_lyapunovStable`,
  `den_locallyExponentiallyStable_subset_lyapunovStable` (for every family, continuous or
  discrete); `mem_den_flow_iff_shift` (an autonomous family written in coordinates about selected
  points `pt x` reads its flow sentences on the original fields at those points, through
  `Flow.Property.holds_shift_iff`).
* The table: `localTable Rl Rs Ru Rp`. `chain_le_semantics_of_localTable` proves every translation
  sound from the inconsistency of the whole language and the three obligations (`Rl` gives
  Lyapunov stability, `Rs` local exponential stability, `Ru` instability) plus passivity on `Rp`;
  `chain_le_semantics_of_localTable_same` is the common case `Rl = Rs`, `Rp = ∅` with every member
  passive. Scaffold: `theorem/FlowSemantics.agda` (the sentence kinds and `localTable`).
* Exactness: `exactUnder_iff_forall` (within a context, by membership), `exactUnder_les_of_jacobian`
  and `exactUnder_les_of_jacobian_local` (converse linearization within a context: soundness of the
  translated requirements plus the converse algebra, an equilibrium with a Hurwitz Jacobian meets
  them), `exactUnder_les_of_jacobian_on` (the same away from degenerate members that are known not
  to be locally exponentially stable), `exact_of_exactUnder_empty`.
* Inconsistency: `realize_univ_eq_empty_of_forall`, `realize_univ_eq_empty_of` (two mutually
  exclusive requirements).
* Witnesses against exactness: `not_exact_of_witness`, `not_exactUnder_of_witness` (a member of
  the denotation that misses a translated requirement), `mem_den_unstable_of_ne_zero`,
  `mem_den_unstable_of_ne_zero_local` and `not_exact_unstable_of_ne_zero` (off-equilibrium
  points), `not_mem_den_lyapunovStable_of_unstable`, `not_exact_of_les_witness` and
  `not_exactUnder_of_les_witness` (a locally exponentially stable member refutes the Lyapunov and
  local asymptotic translations).

Family and connection conclusions.
* The local stability implication is a generic foundation connection between denotations.
  Model modules instantiate the generic laws for their own engineering conclusions.
-/

noncomputable section

namespace powerlib.Spectral

open TMIO Set

variable {X Q : Type*} {n p : ℕ}

/-! ## Denotations of the local sentences -/

section Denotation

variable {F : Family X Q n p}

/-- Local exponential stability gives local asymptotic stability, for every family. -/
@[tmio TM, powerlib_foundation] theorem den_locallyExponentiallyStable_subset_las :
    connection% (F.den (.flow .locallyExponentiallyStable) ⊆
      F.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro x hx
  rw [(connection_proof% Family.mem_den)] at hx ⊢
  cases h : F.system x with
  | continuous s =>
    rw [h, Sentence.holds_flow] at hx
    rw [Sentence.holds_flow]
    exact Flow.locallyExponentiallyStable_localAsymptoticStable hx
  | discrete s =>
    rw [h, Sentence.holds_flow_discrete] at hx
    rw [Sentence.holds_flow_discrete]
    exact Map.LocallyExponentiallyStable.localAsymptoticStable hx
  | disturbed s _ _ _ =>
    rw [h, Sentence.holds_flow_disturbed] at hx
    rw [Sentence.holds_flow_disturbed]
    exact fun ω => Flow.locallyExponentiallyStable_localAsymptoticStable (hx ω)

/-- Local asymptotic stability gives Lyapunov stability, for every family. -/
@[tmio TM, powerlib_foundation] theorem den_las_subset_lyapunovStable :
    connection% (F.den (.flow .locallyAsymptoticallyStable) ⊆ F.den (.flow .lyapunovStable)) := by
  change F.den (.flow .locallyAsymptoticallyStable) ⊆ F.den (.flow .lyapunovStable)
  intro x hx
  rw [(connection_proof% Family.mem_den)] at hx ⊢
  cases h : F.system x with
  | continuous s =>
    rw [h, Sentence.holds_flow] at hx
    rw [Sentence.holds_flow]
    exact hx.1
  | discrete s =>
    rw [h, Sentence.holds_flow_discrete] at hx
    rw [Sentence.holds_flow_discrete]
    exact hx.1
  | disturbed s _ _ _ =>
    rw [h, Sentence.holds_flow_disturbed] at hx
    rw [Sentence.holds_flow_disturbed]
    exact fun ω => (hx ω).1

@[tmio TM, powerlib_foundation] theorem den_locallyExponentiallyStable_subset_lyapunovStable :
    connection% (F.den (.flow .locallyExponentiallyStable) ⊆ F.den (.flow .lyapunovStable)) := show F.den (.flow .locallyExponentiallyStable) ⊆ F.den (.flow .lyapunovStable) from
  fun _ hx => den_las_subset_lyapunovStable (den_locallyExponentiallyStable_subset_las hx)

/-- A family read on fields translated to selected points: its flow sentences are those of the
untranslated fields at the points (`Flow.Property.holds_shift_iff`). -/
@[tmio TM, powerlib_foundation] theorem mem_den_flow_iff_shift {F : Family X Q n 0}
    {f : X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {pt : X → EuclideanSpace ℝ (Fin n)} (hF : F.IsAutonomous fun x z => f x (z + pt x))
    {x : X} {P : Flow.Property} :
    connection% (x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x)) := show x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x) from
  hF.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

end Denotation

/-! ## Inconsistency of the whole language -/

/-- The whole language is inconsistent when no system meets every requirement. -/
@[tmio T, powerlib_foundation] theorem realize_univ_eq_empty_of_forall {meets : X → Q → Prop}
    (h : ∀ x, (∀ q, meets x q) → False) :
    connection% (realize meets univ = ∅) := by
  change realize meets univ = ∅
  ext x
  simp only [mem_realize, mem_univ, true_implies, mem_empty_iff_false, iff_false]
  exact h x

/-- Two mutually exclusive requirements make the whole language inconsistent. -/
@[tmio T, powerlib_foundation] theorem realize_univ_eq_empty_of {meets : X → Q → Prop} (q₁ q₂ : Q)
    (h : ∀ x, meets x q₁ → meets x q₂ → False) :
    connection% (realize meets univ = ∅) := show realize meets univ = ∅ from
  realize_univ_eq_empty_of_forall fun x hx => h x (hx q₁) (hx q₂)

/-! ## The local table and soundness -/

/-- The local table: Lyapunov stability to `Rl`, local asymptotic and local exponential stability
to `Rs`, instability to `Ru`, passivity to `Rp`, every other flow sentence and every envelope
sentence to the whole language. -/
def localTable (Rl Rs Ru Rp : Set Q) : Sentence → Set Q
  | .flow .lyapunovStable => Rl
  | .flow .locallyAsymptoticallyStable | .flow .locallyExponentiallyStable => Rs
  | .flow .unstable => Ru
  | .flow _ => univ
  | .passive => Rp
  | .envelope _ => univ

section Table

variable {F : Family X Q n p} {Rl Rs Ru Rp : Set Q}

/-- Soundness of every translation of a family with the local table: the whole language is
inconsistent, and the requirement sets give Lyapunov stability, local exponential stability,
instability and passivity. -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics_of_localTable
    (ht : ∀ s, F.translate s = localTable Rl Rs Ru Rp s)
    (hinc : realize F.meets univ = ∅)
    (hL : realize F.meets Rl ⊆ F.den (.flow .lyapunovStable))
    (hS : realize F.meets Rs ⊆ F.den (.flow .locallyExponentiallyStable))
    (hU : realize F.meets Ru ⊆ F.den (.flow .unstable))
    (hP : realize F.meets Rp ⊆ F.den .passive) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := by
  change ∀ P, F.chain P ≤ F.semantics P
  refine Family.chain_le_semantics_iff.mpr fun s x hx => ?_
  change x ∈ realize F.meets (F.translate s) at hx
  rw [ht s] at hx
  have hnone : x ∈ realize F.meets univ → x ∈ F.den s := fun h => by
    rw [hinc] at h
    exact h.elim
  rcases s with P | _ | _
  · cases P
    case lyapunovStable => exact hL hx
    case locallyAsymptoticallyStable => exact den_locallyExponentiallyStable_subset_las (hS hx)
    case locallyExponentiallyStable => exact hS hx
    case unstable => exact hU hx
    all_goals exact hnone hx
  · exact hP hx
  · exact hnone hx

/-- The common case: Lyapunov stability shares the requirements of the attractive local
sentences, passivity has none, and every member is passive (a system without ports). -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics_of_localTable_same
    (ht : ∀ s, F.translate s = localTable Rs Rs Ru ∅ s)
    (hinc : realize F.meets univ = ∅)
    (hS : realize F.meets Rs ⊆ F.den (.flow .locallyExponentiallyStable))
    (hU : realize F.meets Ru ⊆ F.den (.flow .unstable))
    (hpas : F.den .passive = univ) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := show ∀ P, F.chain P ≤ F.semantics P from
  chain_le_semantics_of_localTable ht hinc
    (fun _ hx => den_locallyExponentiallyStable_subset_lyapunovStable (hS hx)) hS hU
    (fun x _ => by rw [hpas]; trivial)

end Table

/-! ## Exactness -/

section Exactness

variable {F : Family X Q n p}

/-- Exactness within a context, member by member. -/
@[tmio TM, powerlib_foundation] theorem exactUnder_iff_forall {Δ : Set Q} {s : Sentence} :
    connection% (F.ExactUnder Δ s ↔
      ∀ x ∈ realize F.meets Δ, (x ∈ realize F.meets (F.translate s) ↔ x ∈ F.den s)) := by
  change F.ExactUnder Δ s ↔
        ∀ x ∈ realize F.meets Δ, (x ∈ realize F.meets (F.translate s) ↔ x ∈ F.den s)
  unfold Family.ExactUnder TMIO.ExactUnder
  rw [realize_union]
  constructor
  · intro h x hΔ
    have := congrArg (x ∈ ·) h
    simp only [mem_inter_iff, eq_iff_iff] at this
    simpa [hΔ] using this
  · intro h
    ext x
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(h x h2).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(h x h2).mpr h1, h2⟩

/-- Exactness within the empty context is exactness. -/
@[tmio TM, powerlib_foundation] theorem exact_of_exactUnder_empty {s : Sentence}
    (h : F.ExactUnder ∅ s) :
    connection% (F.Exact s) := by
  change F.Exact s
  unfold Family.ExactUnder TMIO.ExactUnder at h
  unfold Family.Exact
  simpa [realize_empty] using h

variable {f : X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {pt : X → EuclideanSpace ℝ (Fin n)}

/-- Converse linearization within a context, away from degenerate members. The flow sentences
are read on `f x` at `pt x`; within `Δ` the translated requirements of local exponential stability
give it (soundness); members outside the guard `G` are not locally exponentially stable; on the
guard the fields are `C¹` with Jacobian `jac x` at the point, and an equilibrium with a Hurwitz
Jacobian meets the translated requirements (the converse algebra). Then the translation is exact
within `Δ`. -/
@[tmio TM, powerlib_foundation] theorem exactUnder_les_of_jacobian_on
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    (Δ : Set Q) (G : X → Prop) (jac : X → Matrix (Fin n) (Fin n) ℝ)
    (hsound : ∀ x ∈ realize F.meets Δ,
      x ∈ realize F.meets (F.translate (.flow .locallyExponentiallyStable)) →
        x ∈ F.den (.flow .locallyExponentiallyStable))
    (hdeg : ∀ x ∈ realize F.meets Δ, ¬ G x → x ∉ F.den (.flow .locallyExponentiallyStable))
    (hC : ∀ x ∈ realize F.meets Δ, G x → ContDiff ℝ 1 (f x))
    (hJ : ∀ x ∈ realize F.meets Δ, G x →
      fderiv ℝ (f x) (pt x) = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (jac x))
    (hcomplete : ∀ x ∈ realize F.meets Δ, G x → f x (pt x) = 0 →
      LinearSystems.IsHurwitz (jac x) →
        x ∈ realize F.meets (F.translate (.flow .locallyExponentiallyStable))) :
    connection% (F.ExactUnder Δ (.flow .locallyExponentiallyStable)) := show F.ExactUnder Δ (.flow .locallyExponentiallyStable) from
  exactUnder_iff_forall.mpr fun x hΔ => ⟨hsound x hΔ, fun hx => by
    by_cases hG : G x
    · have h := (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (hC x hΔ hG)
        (hJ x hΔ hG)).mp ((hden x .locallyExponentiallyStable).mp hx)
      exact hcomplete x hΔ hG h.1 h.2
    · exact absurd hx (hdeg x hΔ hG)⟩

/-- Converse linearization within a context. The flow sentences are read on `f x` at `pt x`;
within `Δ` the translated requirements of local exponential stability give it (soundness), the
fields are `C¹` with Jacobian `jac x` at the point, and an equilibrium with a Hurwitz Jacobian
meets the translated requirements (the converse algebra). Then the translation is exact within
`Δ`. -/
@[tmio TM, powerlib_foundation] theorem exactUnder_les_of_jacobian
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    (Δ : Set Q) (jac : X → Matrix (Fin n) (Fin n) ℝ)
    (hsound : ∀ x ∈ realize F.meets Δ,
      x ∈ realize F.meets (F.translate (.flow .locallyExponentiallyStable)) →
        x ∈ F.den (.flow .locallyExponentiallyStable))
    (hC : ∀ x ∈ realize F.meets Δ, ContDiff ℝ 1 (f x))
    (hJ : ∀ x ∈ realize F.meets Δ,
      fderiv ℝ (f x) (pt x) = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (jac x))
    (hcomplete : ∀ x ∈ realize F.meets Δ, f x (pt x) = 0 →
      LinearSystems.IsHurwitz (jac x) →
        x ∈ realize F.meets (F.translate (.flow .locallyExponentiallyStable))) :
    connection% (F.ExactUnder Δ (.flow .locallyExponentiallyStable)) := show F.ExactUnder Δ (.flow .locallyExponentiallyStable) from
  exactUnder_les_of_jacobian_on hden Δ (fun _ => True) jac hsound (fun _ _ h => absurd trivial h)
    (fun x hΔ _ => hC x hΔ) (fun x hΔ _ => hJ x hΔ) (fun x hΔ _ => hcomplete x hΔ)

/-- The same with fields that are `C¹` only on an open neighbourhood of the point. -/
@[tmio TM, powerlib_foundation] theorem exactUnder_les_of_jacobian_local
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    (Δ : Set Q) (jac : X → Matrix (Fin n) (Fin n) ℝ)
    (hsound : ∀ x ∈ realize F.meets Δ,
      x ∈ realize F.meets (F.translate (.flow .locallyExponentiallyStable)) →
        x ∈ F.den (.flow .locallyExponentiallyStable))
    (U : X → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ x ∈ realize F.meets Δ, IsOpen (U x))
    (hpt : ∀ x ∈ realize F.meets Δ, pt x ∈ U x)
    (hC : ∀ x ∈ realize F.meets Δ, ContDiffOn ℝ 1 (f x) (U x))
    (hJ : ∀ x ∈ realize F.meets Δ,
      fderiv ℝ (f x) (pt x) = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (jac x))
    (hcomplete : ∀ x ∈ realize F.meets Δ, f x (pt x) = 0 →
      LinearSystems.IsHurwitz (jac x) →
        x ∈ realize F.meets (F.translate (.flow .locallyExponentiallyStable))) :
    connection% (F.ExactUnder Δ (.flow .locallyExponentiallyStable)) := show F.ExactUnder Δ (.flow .locallyExponentiallyStable) from
  exactUnder_iff_forall.mpr fun x hΔ => ⟨hsound x hΔ, fun hx => by
    have h := (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local (hU x hΔ)
      (hpt x hΔ) _ (hC x hΔ) (hJ x hΔ)).mp ((hden x .locallyExponentiallyStable).mp hx)
    exact hcomplete x hΔ h.1 h.2⟩

end Exactness

/-! ## Witnesses against exactness -/

section Witness

variable {F : Family X Q n p} {s : Sentence} {x : X} {q : Q}

/-- A member of the denotation that misses a translated requirement refutes exactness. -/
@[tmio TM, powerlib_foundation] theorem not_exact_of_witness (hx : x ∈ F.den s) (hq : q ∈ F.translate s)
    (hn : ¬ F.meets x q) :
    connection% (¬ F.Exact s) := by
  change ¬ F.Exact s
  intro h
  unfold Family.Exact at h
  rw [← h] at hx
  exact hn ((mem_realize _ _ _).mp hx q hq)

/-- Within a context: a member of the context and of the denotation that misses a translated
requirement refutes exactness within the context. -/
@[tmio TM, powerlib_foundation] theorem not_exactUnder_of_witness {Δ : Set Q}
    (hΔ : x ∈ realize F.meets Δ) (hx : x ∈ F.den s) (hq : q ∈ F.translate s)
    (hn : ¬ F.meets x q) :
    connection% (¬ F.ExactUnder Δ s) := by
  change ¬ F.ExactUnder Δ s
  intro h
  have hx' := ((exactUnder_iff_forall.mp h) x hΔ).mpr hx
  exact hn ((mem_realize _ _ _).mp hx' q hq)

variable {f : X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {pt : X → EuclideanSpace ℝ (Fin n)}

/-- A point that is not an equilibrium of a `C¹` field is unstable. -/
@[tmio TM, powerlib_foundation] theorem mem_den_unstable_of_ne_zero
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    (hC : ContDiff ℝ 1 (f x)) (h0 : f x (pt x) ≠ 0) :
    connection% (x ∈ F.den (.flow .unstable)) := show x ∈ F.den (.flow .unstable) from
  (hden x .unstable).mpr (Dynamics.unstable_of_ne_zero hC h0)

/-- A point that is not an equilibrium of a field `C¹` on an open neighbourhood of it is
unstable. -/
@[tmio TM, powerlib_foundation] theorem mem_den_unstable_of_ne_zero_local
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hpt : pt x ∈ U)
    (hC : ContDiffOn ℝ 1 (f x) U) (h0 : f x (pt x) ≠ 0) :
    connection% (x ∈ F.den (.flow .unstable)) := by
  change x ∈ F.den (.flow .unstable)
  obtain ⟨g, hg, hgf⟩ := Dynamics.exists_contDiff_eventuallyEq hU hpt hC
  refine (hden x .unstable).mpr ((Dynamics.unstable_congr_nhds hgf).mp
    (Dynamics.unstable_of_ne_zero hg ?_))
  rw [hgf.eq_of_nhds]
  exact h0

/-- An off-equilibrium member that misses a translated requirement of instability refutes the
exactness of the instability translation. -/
@[tmio TM, powerlib_foundation] theorem not_exact_unstable_of_ne_zero
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    (hC : ContDiff ℝ 1 (f x)) (h0 : f x (pt x) ≠ 0) (hq : q ∈ F.translate (.flow .unstable))
    (hn : ¬ F.meets x q) :
    connection% (¬ F.Exact (.flow .unstable)) := show ¬ F.Exact (.flow .unstable) from
  not_exact_of_witness (mem_den_unstable_of_ne_zero hden hC h0) hq hn

/-- A locally exponentially stable member that misses a translated requirement of Lyapunov or
local asymptotic stability refutes the exactness of that translation. -/
@[tmio TM, powerlib_foundation] theorem not_exact_of_les_witness
    (hx : x ∈ F.den (.flow .locallyExponentiallyStable)) {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable)
    (hq : q ∈ F.translate (.flow P)) (hn : ¬ F.meets x q) :
    connection% (¬ F.Exact (.flow P)) := by
  change ¬ F.Exact (.flow P)
  refine not_exact_of_witness ?_ hq hn
  rcases hP with rfl | rfl
  · exact den_locallyExponentiallyStable_subset_lyapunovStable hx
  · exact den_locallyExponentiallyStable_subset_las hx

/-- The same within a context. -/
@[tmio TM, powerlib_foundation] theorem not_exactUnder_of_les_witness {Δ : Set Q}
    (hΔ : x ∈ realize F.meets Δ) (hx : x ∈ F.den (.flow .locallyExponentiallyStable))
    {P : Flow.Property} (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable)
    (hq : q ∈ F.translate (.flow P)) (hn : ¬ F.meets x q) :
    connection% (¬ F.ExactUnder Δ (.flow P)) := by
  change ¬ F.ExactUnder Δ (.flow P)
  refine not_exactUnder_of_witness hΔ ?_ hq hn
  rcases hP with rfl | rfl
  · exact den_locallyExponentiallyStable_subset_lyapunovStable hx
  · exact den_locallyExponentiallyStable_subset_las hx

/-- An unstable member is not Lyapunov stable, for every family. -/
@[tmio TM, powerlib_foundation] theorem not_mem_den_lyapunovStable_of_unstable
    (hx : x ∈ F.den (.flow .unstable)) :
    connection% (x ∉ F.den (.flow .lyapunovStable)) := by
  change x ∉ F.den (.flow .lyapunovStable)
  intro hl
  rw [(connection_proof% Family.mem_den)] at hx hl
  cases h : F.system x with
  | continuous s' =>
    rw [h, Sentence.holds_flow] at hx hl
    exact hx hl
  | discrete s' =>
    rw [h, Sentence.holds_flow_discrete] at hx hl
    exact hx hl
  | disturbed s' _ _ _ =>
    rw [h, Sentence.holds_flow_disturbed] at hx hl
    exact hx default (hl default)

end Witness

end powerlib.Spectral
