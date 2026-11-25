import theorem.Dynamics.HopfDichotomy
import theorem.NormalForm.BiRidge

/-! # The Hopf laws for fields that are smooth only near the equilibrium

`Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly` and
`localAsymptoticStable_of_firstLyapunov_neg_of_charpoly` (`theorem/Dynamics/HopfDichotomy.lean`)
read a field that is `C¹` on the whole space and analytic at the equilibrium. Fields with a
singular set away from the equilibrium (a power balance `P/V` with `V ≠ 0` near the point) are
`C¹` only on an open neighbourhood. The laws below reduce them to the global ones: the field
agrees near the point with a globally `C¹` field (`Dynamics.exists_contDiff_eventuallyEq`), which
is analytic at the point, has the same Jacobian, forms, critical pairs and first Lyapunov
coefficient there (`NormalForm.LyapunovCoefficient.firstLyapunov_congr`,
`isCriticalPair_congr`), and the same local behaviour (the library's stability notions are local:
`Dynamics.unstable_congr_nhds`, `Dynamics.localAsymptoticStable_congr_nhds`).

Scope.
* Generic foundation, independent of any model: an arbitrary autonomous field `F : ℝⁿ → ℝⁿ`,
  `C¹` on an open set `U ∋ 0` and analytic at the equilibrium `0`; the hypotheses on the critical
  pair, the characteristic polynomial and `ℓ₁` as in `theorem/Dynamics/HopfDichotomy.lean`.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4; the
locality of Lyapunov stability, instability and local asymptotic stability
(`theorem/Dynamics/Locality.lean`).

Results.
* `CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly_local`: `ℓ₁ > 0` ⇒ unstable.
* `CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly_local`: `ℓ₁ < 0` ⇒
  locally asymptotically stable.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold
open Complex Polynomial
open powerlib.NormalForm.LyapunovCoefficient

variable {n : ℕ}

/-- **`ℓ₁ > 0` gives instability at a Hopf point of a field `C¹` near it.** -/
@[tmio T, powerlib_foundation] theorem unstable_of_firstLyapunov_pos_of_charpoly_local
    {F : State n → State n} {U : Set (State n)} (hU : IsOpen U) (h0 : (0 : State n) ∈ U)
    (hF : ContDiffOn ℝ 1 F U) (ha : AnalyticAt ℝ F 0) {ω : ℝ} {q p : Fin n → ℂ}
    (hcp : IsCriticalPair F 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (hl : 0 < firstLyapunov F 0 ω q p) :
    Unstable F 0 := by
  obtain ⟨G, hG, hGF⟩ := exists_contDiff_eventuallyEq hU h0 hF
  refine (unstable_congr_nhds hGF.symm).mpr ?_
  exact unstable_of_firstLyapunov_pos_of_charpoly hG (ha.congr hGF.symm)
    ((isCriticalPair_congr hGF).mpr hcp) (by rw [jacobianC_congr hGF]; exact hchar) hr
    (by rw [firstLyapunov_congr hGF]; exact hl)

/-- **`ℓ₁ < 0` gives local asymptotic stability at a Hopf point of a field `C¹` near it.** -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_firstLyapunov_neg_of_charpoly_local
    {F : State n → State n} {U : Set (State n)} (hU : IsOpen U) (h0 : (0 : State n) ∈ U)
    (hF : ContDiffOn ℝ 1 F U) (ha : AnalyticAt ℝ F 0) {ω : ℝ} {q p : Fin n → ℂ}
    (hcp : IsCriticalPair F 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (hl : firstLyapunov F 0 ω q p < 0) :
    LocalAsymptoticStable F 0 := by
  obtain ⟨G, hG, hGF⟩ := exists_contDiff_eventuallyEq hU h0 hF
  refine localAsymptoticStable_congr_nhds hGF.symm ?_
  exact localAsymptoticStable_of_firstLyapunov_neg_of_charpoly hG (ha.congr hGF.symm)
    ((isCriticalPair_congr hGF).mpr hcp) (by rw [jacobianC_congr hGF]; exact hchar) hr
    (by rw [firstLyapunov_congr hGF]; exact hl)

end powerlib.Dynamics.CenterManifold
