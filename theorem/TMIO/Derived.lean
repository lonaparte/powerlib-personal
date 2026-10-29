import theorem.TMIO.Generate

/-! # The TMIO chain generated from its seed (v0.3 §2, §5)

A `Seed` holds four complete lattices `T, M, I, O` (theories, models, implementations,
observations) and, per adjacent edge, one arbitrary-infimum preserving semantic map pointing back
to the earlier layer. The forward maps `l₁, l₂, l₃` are generated, never supplied.

Every composite of edges is again a seed edge, and the generated forward map of a composite is the
composite of the generated forward maps (`generate_uTO`). There is therefore no separate
cross-layer algorithm that could disagree with the layer-by-layer one.

Scope.
* Generic order theory: four arbitrary complete lattices and three semantic maps
  (`theorem/TMIO/Generate.lean`); no model and no semantics.

Source: TMIO v0.3 §2 (generation data) and §5 (whole equals parts); the generation theorem of
`theorem/TMIO/Generate.lean`.

Results.
* `Seed` (`u₁`, `u₂`, `u₃`), the generated forward maps `Seed.l₁`, `Seed.l₂`, `Seed.l₃` and their
  Galois connections `Seed.gc₁`, `Seed.gc₂`, `Seed.gc₃`.
* Composite semantic maps `Seed.uTI`, `Seed.uMO`, `Seed.uTO` and their generated forward maps
  `Seed.generate_uTI`, `Seed.generate_uMO`, `Seed.generate_uTO`.
* The whole chain: `Seed.gc_whole`, `Seed.whole_monotone` (stronger theory data never yields
  weaker observation data), `Seed.whole_sSup`.
-/

namespace powerlib.TMIO

namespace Seed

variable {T M I O : Type*} [CompleteLattice T] [CompleteLattice M] [CompleteLattice I]
  [CompleteLattice O] (S : Seed T M I O)

/-- Generated forward map from theories to models. -/
def l₁ : LowerAdjoint S.u₁ := generate S.u₁

/-- Generated forward map from models to implementations. -/
def l₂ : LowerAdjoint S.u₂ := generate S.u₂

/-- Generated forward map from implementations to observations. -/
def l₃ : LowerAdjoint S.u₃ := generate S.u₃

@[tmio T, powerlib_foundation] theorem gc₁ :
    connection% (GaloisConnection S.l₁ S.u₁) := show GaloisConnection S.l₁ S.u₁ from gc_generate S.u₁
@[tmio T, powerlib_foundation] theorem gc₂ :
    connection% (GaloisConnection S.l₂ S.u₂) := show GaloisConnection S.l₂ S.u₂ from gc_generate S.u₂
@[tmio T, powerlib_foundation] theorem gc₃ :
    connection% (GaloisConnection S.l₃ S.u₃) := show GaloisConnection S.l₃ S.u₃ from gc_generate S.u₃

/-- Composite semantic map from implementations back to theories. -/
def uTI : sInfHom I T := S.u₁.comp S.u₂

/-- Composite semantic map from observations back to models. -/
def uMO : sInfHom O M := S.u₂.comp S.u₃

/-- Whole-chain semantic map from observations back to theories. -/
def uTO : sInfHom O T := S.u₁.comp (S.u₂.comp S.u₃)

@[tmio T, powerlib_foundation] theorem generate_uTI :
    connection% (⇑(generate S.uTI) = S.l₂ ∘ S.l₁) := show ⇑(generate S.uTI) = S.l₂ ∘ S.l₁ from
  generate_comp S.u₁ S.u₂

@[tmio T, powerlib_foundation] theorem generate_uMO :
    connection% (⇑(generate S.uMO) = S.l₃ ∘ S.l₂) := show ⇑(generate S.uMO) = S.l₃ ∘ S.l₂ from
  generate_comp S.u₂ S.u₃

/-- Whole equals parts for the full chain (v0.3 §5). -/
@[tmio T, powerlib_foundation] theorem generate_uTO :
    connection% (⇑(generate S.uTO) = S.l₃ ∘ S.l₂ ∘ S.l₁) := by
  change ⇑(generate S.uTO) = S.l₃ ∘ S.l₂ ∘ S.l₁
  rw [uTO, generate_comp, generate_comp]
  rfl

/-- The whole-chain Galois connection. -/
@[tmio T, powerlib_foundation] theorem gc_whole :
    connection% (GaloisConnection (generate S.uTO) S.uTO) :=
  gc_generate S.uTO

/-- Monotone propagation: stronger theory data never yields weaker observation data. -/
@[tmio T, powerlib_foundation] theorem whole_monotone :
    connection% (Monotone (S.l₃ ∘ S.l₂ ∘ S.l₁)) := show Monotone (S.l₃ ∘ S.l₂ ∘ S.l₁) from
  ((S.gc₁.compose S.gc₂).compose S.gc₃).monotone_l

/-- The whole chain preserves arbitrary joins of theory data. -/
@[tmio T, powerlib_foundation] theorem whole_sSup (s : Set T) :
    connection% ((S.l₃ ∘ S.l₂ ∘ S.l₁) (sSup s) = sSup ((S.l₃ ∘ S.l₂ ∘ S.l₁) '' s)) := show (S.l₃ ∘ S.l₂ ∘ S.l₁) (sSup s) = sSup ((S.l₃ ∘ S.l₂ ∘ S.l₁) '' s) from
  ((S.gc₁.compose S.gc₂).compose S.gc₃).l_sSup_eq_sSup_image

end Seed

end powerlib.TMIO
