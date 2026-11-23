import theorem.Attributes
import theorem.GridTiedConverter.GFM.Limiting.Formulas
import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Adaptive fast/slow internal-voltage-source switching signal

Trigonometric model identities (domain) about the switching signal of the adaptive IVS scheme; the
switching logic itself is not modelled.

Model boundary.
Wu–Wang (2023) current magnitude of a grid-forming converter before current limiting
(work-sync T-dc-voltage-gfm §1.7): internal voltage `E∠δ` behind the total reactance
`X = X_f + X_g` against the grid `V_g∠0`,
`I_omag(δ) = √(E² + V_g² − 2 E V_g cos δ)/X` (`iMag`, `X > 0`); a static formula, no converter
dynamics.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.7.

Results.
* `iMag` is the current magnitude `currentMag` of
  `theorem/GridTiedConverter/GFM/Limiting/Formulas.lean` behind the inductive branch
  `⟨0, X, 0⟩ : Passive.SeriesRLC` at `s = j` (per-unit reactance, `ω = 1`), whose impedance is
  `jX`; the results below are instances of the `currentMag` laws there.
* `iMag_hasDerivAt`: `dI_omag/dδ = E V_g sin δ / (X² I_omag)` wherever `I_omag > 0` (the
  note's derivative).
* `iMag_strictMonoOn`: for `E, V_g, X > 0`, `I_omag` is strictly increasing in `δ` on
  `[0, π]` (in particular on `(0, π)`), so `I_omag` can replace the unmeasurable `δ` as the
  switching signal.
* `iMag_isLeast`: for `δ_th ∈ [0, π]` and `E ≥ 0`, `E sin δ_th/X ≤ I_omag(δ_th; V_g)` for
  every `V_g`, with equality at `V_g = E cos δ_th`: the note's threshold
  `I_omag,th,min = E sin δ_th/(X_f + X_g)` is exactly the minimum over the grid voltage.
  (It is attained by a positive grid voltage iff `cos δ_th > 0`, i.e. `δ_th < π/2`.)
-/

noncomputable section
namespace powerlib.Limiting

/-- `I_omag(δ) = √(E² + V² − 2 E V cos δ)/X` (for `X > 0`): the current magnitude `currentMag`
behind the inductive branch `⟨0, X, 0⟩` at `s = j`, i.e. `Z = jX`. -/
abbrev iMag (E V X δ : ℝ) : ℝ := currentMag E V ⟨0, X, 0⟩ 1 δ

@[tmio M, powerlib_domain] private lemma absSq_inductive (X : ℝ) :
    (⟨0, X, 0⟩ : Passive.SeriesRLC).absSq 1 = X ^ 2 := by
  simp [Passive.SeriesRLC.absSq, Passive.SeriesRLC.reactance]

/-- Derivative `E V sin δ/(X² I_omag)` (`currentMag_hasDerivAt`). -/
@[tmio M, powerlib_domain] theorem iMag_hasDerivAt {E V X δ : ℝ} (hX : X ≠ 0)
    (hu : 0 < E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ) :
    HasDerivAt (iMag E V X) (E * V * Real.sin δ / (X ^ 2 * iMag E V X δ)) δ := by
  simpa only [absSq_inductive] using
    currentMag_hasDerivAt (Z := ⟨0, X, 0⟩) (ω := 1) (by rw [absSq_inductive]; positivity) hu

/-- `I_omag` is strictly increasing in `δ` on `[0, π]` (`currentMag_strictMonoOn`). -/
@[tmio M, powerlib_domain] theorem iMag_strictMonoOn {E V X : ℝ} (hE : 0 < E) (hV : 0 < V)
    (hX : 0 < X) : StrictMonoOn (iMag E V X) (Set.Icc 0 Real.pi) :=
  currentMag_strictMonoOn hE hV (by rw [absSq_inductive]; positivity)

/-- The worst-case threshold `E sin δ_th/X` is a lower bound over all grid voltages, attained at
`V_g = E cos δ_th` (`currentMag_isLeast`). -/
@[tmio M, powerlib_domain] theorem iMag_isLeast {E X δ : ℝ} (hE : 0 ≤ E) (hX : 0 < X)
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    IsLeast (Set.range fun V => iMag E V X δ) (E * Real.sin δ / X) := by
  simpa only [absSq_inductive, Real.sqrt_sq hX.le] using
    currentMag_isLeast (Z := ⟨0, X, 0⟩) (ω := 1) hE hδ0 hδπ

end powerlib.Limiting
