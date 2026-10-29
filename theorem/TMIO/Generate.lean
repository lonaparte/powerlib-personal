import theorem.TMIO.ClaimSyntax
import theorem.Attributes

/-! # TMIO generation theorem (v0.3 §3)

Each TMIO edge stores exactly one semantic map `u : sInfHom B A`, an arbitrary-infimum preserving
map between complete lattices. Its lower adjoint is not supplied independently: `generate u`
constructs it as `a ↦ ⨅ {b | a ≤ u b}`, packaged as Mathlib's `LowerAdjoint u`, so Mathlib's
closure-operator and closed-element theory applies to it unchanged.

The forward map is therefore determined by `u` alone (`generate_unique`); a separately written
forward map either coincides with `generate u` or is not a lower adjoint of `u`.

Scope.
* Generic order theory: arbitrary complete lattices `A`, `B`, `C` and arbitrary-infimum
  preserving maps between them; no model and no semantics.

Source: TMIO v0.3 §3 (the generation theorem); Mathlib's `LowerAdjoint`, `GaloisConnection` and
`ClosureOperator` (`Mathlib.Order.Closure`, `Mathlib.Order.Hom.CompleteLattice`).

Results.
* `generate` (with `generate_apply`, `le_map_sInf_setOf`, `sInfHom_monotone`) and the generation
  theorem `gc_generate`: `generate u ⊣ u`.
* Uniqueness and optimality: `generate_unique`, `lowerAdjoint_eq_generate`, `generate_isLeast`.
* Preservation: `generate_sSup`, `generate_sup`, `generate_monotone`; whole equals parts,
  `generate_comp` (the generated adjoint of a composite is the composite of the generated
  adjoints, in reverse order).
* Closure and interior: `closure` (`closure_apply`), `generate_u_le`, `generate_u_idempotent`, and
  the fixed-point correspondence `fixedPointsIso`.
-/

namespace powerlib.TMIO

variable {A B C : Type*} [CompleteLattice A] [CompleteLattice B] [CompleteLattice C]

/-- An arbitrary-infimum preserving map is monotone. -/
@[tmio T, powerlib_foundation] theorem sInfHom_monotone (u : sInfHom B A) :
    connection% (Monotone u) := show Monotone u from
  OrderHomClass.mono u

@[tmio T, powerlib_foundation] theorem le_map_sInf_setOf (u : sInfHom B A) (a : A) :
    connection% (a ≤ u (sInf {b | a ≤ u b})) := by
  change a ≤ u (sInf {b | a ≤ u b})
  rw [map_sInf]
  exact le_sInf (by rintro _ ⟨b, hb, rfl⟩; exact hb)

@[tmio T, simp, powerlib_foundation] theorem generate_apply (u : sInfHom B A) (a : A) :
    connection% (generate u a = sInf {b | a ≤ u b}) := show generate u a = sInf {b | a ≤ u b} from rfl

/-- Generation theorem: `generate u ⊣ u`. -/
@[tmio T, powerlib_foundation] theorem gc_generate (u : sInfHom B A) :
    connection% (GaloisConnection (generate u) u) := show GaloisConnection (generate u) u from
  (generate u).gc

/-- Uniqueness: every lower adjoint of `u` is the generated one. -/
@[tmio T, powerlib_foundation] theorem generate_unique (u : sInfHom B A) {l : A → B}
    (h : GaloisConnection l u) :
    connection% (l = ⇑(generate u)) := show l = ⇑(generate u) from
  funext fun _ => h.l_unique (gc_generate u) fun _ => rfl

/-- Every bundled lower adjoint of `u` equals the generated one. -/
@[tmio T, powerlib_foundation] theorem lowerAdjoint_eq_generate (u : sInfHom B A) (l : LowerAdjoint u) :
    connection% (l = generate u) := show l = generate u from
  LowerAdjoint.ext _ _ (generate_unique u l.gc)

/-- Canonical optimality: `generate u a` is the least `b` with `a ≤ u b`. -/
@[tmio T, powerlib_foundation] theorem generate_isLeast (u : sInfHom B A) (a : A) :
    connection% (a ≤ u (generate u a) ∧ ∀ b, a ≤ u b → generate u a ≤ b) := show IsLeast {b | a ≤ u b} (generate u a) from
  (gc_generate u).isLeast_l

/-- The generated map preserves arbitrary suprema. -/
@[tmio T, powerlib_foundation] theorem generate_sSup (u : sInfHom B A) (s : Set A) :
    connection% (generate u (sSup s) = sSup (generate u '' s)) := show generate u (sSup s) = sSup (generate u '' s) from
  (gc_generate u).l_sSup_eq_sSup_image

@[tmio T, powerlib_foundation] theorem generate_sup (u : sInfHom B A) (a₁ a₂ : A) :
    connection% (generate u (a₁ ⊔ a₂) = generate u a₁ ⊔ generate u a₂) := show generate u (a₁ ⊔ a₂) = generate u a₁ ⊔ generate u a₂ from
  (gc_generate u).l_sup

@[tmio T, powerlib_foundation] theorem generate_monotone (u : sInfHom B A) :
    connection% (Monotone (generate u)) := show Monotone (generate u) from
  (gc_generate u).monotone_l

/-- Whole equals parts: the generated adjoint of a composite is the composite of the generated
adjoints, in reverse order. -/
@[tmio T, powerlib_foundation] theorem generate_comp (u : sInfHom B A) (v : sInfHom C B) :
    connection% (⇑(generate (u.comp v)) = generate v ∘ generate u) := show ⇑(generate (u.comp v)) = generate v ∘ generate u from
  (generate_unique (u.comp v) ((gc_generate u).compose (gc_generate v))).symm

@[tmio T, simp, powerlib_foundation] theorem closure_apply (u : sInfHom B A) (a : A) :
    connection% (closure u a = u (generate u a)) := show closure u a = u (generate u a) from rfl

/-- The interior operator `generate u ∘ u` on the target side is deflationary. -/
@[tmio T, powerlib_foundation] theorem generate_u_le (u : sInfHom B A) (b : B) :
    connection% (generate u (u b) ≤ b) := show generate u (u b) ≤ b from
  (gc_generate u).l_u_le b

/-- The interior operator `generate u ∘ u` is idempotent. -/
@[tmio T, powerlib_foundation] theorem generate_u_idempotent (u : sInfHom B A) (b : B) :
    connection% (generate u (u (generate u (u b))) = generate u (u b)) := by
  change generate u (u (generate u (u b))) = generate u (u b)
  rw [(connection_proof% (gc_generate u).u_l_u_eq_u)]

/-- Fixed-point correspondence: closed source elements and interior-stable target elements are
order isomorphic through `generate u` and `u`. -/
def fixedPointsIso (u : sInfHom B A) :
    {a : A // u (generate u a) = a} ≃o {b : B // generate u (u b) = b} where
  toFun a := ⟨generate u a, by rw [(connection_proof% (gc_generate u).l_u_l_eq_l)]⟩
  invFun b := ⟨u b, by rw [(connection_proof% (gc_generate u).u_l_u_eq_u)]⟩
  left_inv a := Subtype.ext a.2
  right_inv b := Subtype.ext b.2
  map_rel_iff' {a a'} := by
    constructor
    · intro h
      have h' : u (generate u a.1) ≤ u (generate u a'.1) := sInfHom_monotone u h
      rwa [a.2, a'.2] at h'
    · intro h
      exact generate_monotone u h

end powerlib.TMIO
