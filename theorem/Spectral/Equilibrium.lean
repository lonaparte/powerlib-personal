import theorem.Spectral.Local

/-! # Exactness of the local translations from equilibria (foundation)

A sentence that implies Lyapunov stability holds only at equilibria of a `C¹` field
(`Dynamics.isEquilibrium_of_lyapunovStable`). A family whose translation of such a sentence is "an
equilibrium with a guard condition" — power balance with a Hurwitz Jacobian, a balanced angle with
a negative slope — is therefore exact as soon as the translation is sound and every equilibrium
that fails the guard fails the sentence. Converse linearization
(`Spectral.exactUnder_les_of_jacobian` in `theorem/Spectral/Local.lean`) is the case of local
exponential stability with the Hurwitz guard; for Lyapunov and local asymptotic stability the
degenerate equilibria must be excluded by the model's structure, and this module states the
remaining bookkeeping once.

Scope.
* A generic template, not a model: an arbitrary family `F : Family X Q n p` whose flow sentences
  are read on a field `f x` at a point `pt x` (`hden`, as in `theorem/Spectral/Local.lean`), an
  arbitrary requirement language and context. No new behavioural notion is defined.

Source: the converse step `Dynamics.isEquilibrium_of_lyapunovStable`
(`theorem/Dynamics/ConverseLinearization.lean`); the network swing and PSC families (audit of the
library).

Results.
* `exactUnder_of_equilibrium`: within a context, the translation of Lyapunov, local asymptotic or
  local exponential stability is exact when it is sound, the fields are `C¹`, every equilibrium
  outside a guard `G` fails the sentence and every equilibrium on the guard meets the translated
  requirements; `exact_of_equilibrium`, the same without a context.

Family and connection conclusions.
* `exactUnder_of_equilibrium` is a generic foundation connection establishing translation
  exactness. Model modules instantiate it for their own engineering conclusions.
-/

noncomputable section

namespace powerlib.Spectral

open TMIO Set

variable {X Q : Type*} {n p : ℕ} {F : Family X Q n p}
  {f : X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {pt : X → EuclideanSpace ℝ (Fin n)}

/-- Exactness from equilibria within a context. The flow sentences are read on `f x` at `pt x`;
`P` is Lyapunov, local asymptotic or local exponential stability; within `Δ` the translated
requirements of `P` give it (soundness), the fields are `C¹`, an equilibrium outside the guard
`G` does not satisfy `P`, and an equilibrium on the guard meets the translated requirements. Then
the translation of `P` is exact within `Δ`. -/
@[tmio TM, powerlib_foundation] theorem exactUnder_of_equilibrium
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable)
    (Δ : Set Q) (G : X → Prop)
    (hsound : ∀ x ∈ realize F.meets Δ,
      x ∈ realize F.meets (F.translate (.flow P)) → x ∈ F.den (.flow P))
    (hC : ∀ x ∈ realize F.meets Δ, ContDiff ℝ 1 (f x))
    (hdeg : ∀ x ∈ realize F.meets Δ, f x (pt x) = 0 → ¬ G x → x ∉ F.den (.flow P))
    (hcomplete : ∀ x ∈ realize F.meets Δ, f x (pt x) = 0 → G x →
      x ∈ realize F.meets (F.translate (.flow P))) :
    connection% (F.ExactUnder Δ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact exactUnder_iff_forall.mpr fun x hΔ => ⟨hsound x hΔ, fun hx => by
    have hls : LyapunovStable (f x) (pt x) := by
      have h := (hden x P).mp hx
      rcases hP with rfl | rfl | rfl
      · exact h
      · exact h.1
      · exact h.lyapunovStable
    have heq : f x (pt x) = 0 := Dynamics.isEquilibrium_of_lyapunovStable (hC x hΔ) hls
    by_cases hG : G x
    · exact hcomplete x hΔ heq hG
    · exact absurd hx (hdeg x hΔ heq hG)⟩

/-- Exactness from equilibria, without a context. -/
@[tmio TM, powerlib_foundation] theorem exact_of_equilibrium
    (hden : ∀ x (P : Flow.Property), x ∈ F.den (.flow P) ↔ P.holds (f x) (pt x))
    {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable)
    (G : X → Prop)
    (hsound : realize F.meets (F.translate (.flow P)) ⊆ F.den (.flow P))
    (hC : ∀ x, ContDiff ℝ 1 (f x))
    (hdeg : ∀ x, f x (pt x) = 0 → ¬ G x → x ∉ F.den (.flow P))
    (hcomplete : ∀ x, f x (pt x) = 0 → G x → x ∈ realize F.meets (F.translate (.flow P))) :
    connection% (F.Exact (.flow P)) := show F.Exact (.flow P) from
  exact_of_exactUnder_empty (exactUnder_of_equilibrium hden hP ∅ G (fun _ _ hx => hsound hx)
    (fun x _ => hC x) (fun x _ => hdeg x) (fun x _ => hcomplete x))

end powerlib.Spectral
