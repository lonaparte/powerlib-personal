import dependencies.Mathlib
import theorem.Attributes

/-! # TMIO generation theorem (v0.3 §3)

Each TMIO edge stores exactly one semantic map `u : sInfHom B A`, an arbitrary-infimum preserving
map between complete lattices. Its lower adjoint is not supplied independently: `generate u`
constructs it as `a ↦ ⨅ {b | a ≤ u b}`, packaged as Mathlib's `LowerAdjoint u`, so Mathlib's
closure-operator and closed-element theory applies to it unchanged.

The forward map is therefore determined by `u` alone (`generate_unique`); a separately written
forward map either coincides with `generate u` or is not a lower adjoint of `u`. -/

namespace powerlib.TMIO

variable {A B C : Type*} [CompleteLattice A] [CompleteLattice B] [CompleteLattice C]

/-- An arbitrary-infimum preserving map is monotone. -/
@[powerlib_foundation] theorem sInfHom_monotone (u : sInfHom B A) : Monotone u :=
  OrderHomClass.mono u

@[powerlib_foundation] theorem le_map_sInf_setOf (u : sInfHom B A) (a : A) :
    a ≤ u (sInf {b | a ≤ u b}) := by
  rw [map_sInf]
  exact le_sInf (by rintro _ ⟨b, hb, rfl⟩; exact hb)

/-- The generated lower adjoint of `u`: `a ↦ ⨅ {b | a ≤ u b}`. -/
def generate (u : sInfHom B A) : LowerAdjoint u where
  toFun a := sInf {b | a ≤ u b}
  gc' a _ := ⟨fun h => (le_map_sInf_setOf u a).trans (sInfHom_monotone u h),
    fun h => sInf_le h⟩

@[simp, powerlib_foundation] theorem generate_apply (u : sInfHom B A) (a : A) :
    generate u a = sInf {b | a ≤ u b} := rfl

/-- Generation theorem: `generate u ⊣ u`. -/
@[powerlib_foundation] theorem gc_generate (u : sInfHom B A) : GaloisConnection (generate u) u :=
  (generate u).gc

/-- Uniqueness: every lower adjoint of `u` is the generated one. -/
@[powerlib_foundation] theorem generate_unique (u : sInfHom B A) {l : A → B}
    (h : GaloisConnection l u) : l = ⇑(generate u) :=
  funext fun _ => h.l_unique (gc_generate u) fun _ => rfl

/-- Every bundled lower adjoint of `u` equals the generated one. -/
@[powerlib_foundation] theorem lowerAdjoint_eq_generate (u : sInfHom B A) (l : LowerAdjoint u) :
    l = generate u :=
  LowerAdjoint.ext _ _ (generate_unique u l.gc)

/-- Canonical optimality: `generate u a` is the least `b` with `a ≤ u b`. -/
@[powerlib_foundation] theorem generate_isLeast (u : sInfHom B A) (a : A) :
    IsLeast {b | a ≤ u b} (generate u a) :=
  (gc_generate u).isLeast_l

/-- The generated map preserves arbitrary suprema. -/
@[powerlib_foundation] theorem generate_sSup (u : sInfHom B A) (s : Set A) :
    generate u (sSup s) = sSup (generate u '' s) :=
  (gc_generate u).l_sSup_eq_sSup_image

@[powerlib_foundation] theorem generate_sup (u : sInfHom B A) (a₁ a₂ : A) :
    generate u (a₁ ⊔ a₂) = generate u a₁ ⊔ generate u a₂ :=
  (gc_generate u).l_sup

@[powerlib_foundation] theorem generate_monotone (u : sInfHom B A) : Monotone (generate u) :=
  (gc_generate u).monotone_l

/-- Whole equals parts: the generated adjoint of a composite is the composite of the generated
adjoints, in reverse order. -/
@[powerlib_foundation] theorem generate_comp (u : sInfHom B A) (v : sInfHom C B) :
    ⇑(generate (u.comp v)) = generate v ∘ generate u :=
  (generate_unique (u.comp v) ((gc_generate u).compose (gc_generate v))).symm

/-- The closure operator `u ∘ generate u` on the source side (Mathlib's
`LowerAdjoint.closureOperator`). -/
def closure (u : sInfHom B A) : ClosureOperator A := (generate u).closureOperator

@[simp, powerlib_foundation] theorem closure_apply (u : sInfHom B A) (a : A) :
    closure u a = u (generate u a) := rfl

/-- The interior operator `generate u ∘ u` on the target side is deflationary. -/
@[powerlib_foundation] theorem generate_u_le (u : sInfHom B A) (b : B) : generate u (u b) ≤ b :=
  (gc_generate u).l_u_le b

/-- The interior operator `generate u ∘ u` is idempotent. -/
@[powerlib_foundation] theorem generate_u_idempotent (u : sInfHom B A) (b : B) :
    generate u (u (generate u (u b))) = generate u (u b) := by
  rw [(gc_generate u).u_l_u_eq_u]

/-- Fixed-point correspondence: closed source elements and interior-stable target elements are
order isomorphic through `generate u` and `u`. -/
def fixedPointsIso (u : sInfHom B A) :
    {a : A // u (generate u a) = a} ≃o {b : B // generate u (u b) = b} where
  toFun a := ⟨generate u a, by rw [(gc_generate u).l_u_l_eq_l]⟩
  invFun b := ⟨u b, by rw [(gc_generate u).u_l_u_eq_u]⟩
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
