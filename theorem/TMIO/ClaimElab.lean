import theorem.TMIO.ClaimSyntax
import theorem.TMIO.Relation

/-! # Connection notation and semantic constructors

Public import for `connection%`. The elaborator is defined in `ClaimSyntax`, below the
public connection laws, so those laws can carry the same kernel-checked certificates.
This import also exposes the standard semantic constructors for existing consumers.

Scope.
* Re-export of generic syntax and semantic constructors; no additional declarations or model.

Source: `theorem/TMIO/ClaimSyntax.lean` and `theorem/TMIO/Relation.lean`.

Results.
* The public import for `connection%`, `connection_proof%` and the standard connection maps.
-/
