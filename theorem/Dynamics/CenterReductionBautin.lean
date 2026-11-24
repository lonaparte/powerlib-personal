import theorem.Dynamics.HopfDichotomy
import theorem.Dynamics.Degenerate.PlanarFocus2

/-! # The second Lyapunov coefficient through the centre manifold (foundation)

At a weak focus of the first order (`l₁ = 0`) of a field `ẋ = A x + f(x)` on `ℝⁿ` with a
two-dimensional centre subspace, the second Lyapunov coefficient `l₂` of the reduced field decides
stability, and the 5-jet of the reduced field needed for it is computable from any approximate
centre manifold `φ` with invariance defect `O(‖u‖⁵)` (for instance a polynomial of degree at most
four solving the homological equations of orders two to four): the chart field of every centre
manifold differs from the chart field of `φ` by `o(‖y‖⁵)`.

Scope.
* Generic: `State n = ℝⁿ`, `A`, `P` with `P² = P`, `AP = PA` (`IsCommutingProjection`), the
  dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}`, `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`) with the gap
  `5ε < β` (Carr's approximation of order five), `f` of class `C¹` with `f(0) = 0`, `Df(0) = 0`,
  a chart `ι : ℝ² → ℝⁿ`, `π` of `range P` (`IsChart`). The approximate manifold `φ` is `C¹` near
  `0`, `φ(0) = 0`, `Dφ(0) = 0`, with values in `ker P`, and its invariance defect is `O(‖u‖⁵)` on
  `range P` (Carr's hypothesis with `q = 5`). The 5-jet of the chart field of `φ` is a hypothesis
  in the rotation coordinates of a planar `L₂` with `L₂² = −ω²` (`Degenerate.PlanarFocus.Jet5`):
  no Taylor expansion of `f` is assumed beyond `C¹`.
* Behaviour is LeanForControl's `LocalAsymptoticStable` and `Unstable` of the full field at `0`.
* Nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), §2.4 (Theorem 2, the reduction
principle) and §2.5 (Theorem 3, the approximation of the centre manifold); Kuznetsov, *Elements of
Applied Bifurcation Theory* (3rd ed.), §5.1 (Theorem 5.2), §8.3 (the Bautin point: `l₁ = 0`, the
sign of `l₂`). The constructed centre manifold and its transfers are
`theorem/Dynamics/CenterReductionStability.lean` (`exists_centerManifold_stable`) and
`theorem/Dynamics/CenterReduction.lean`; the planar laws
`theorem/Dynamics/Degenerate/PlanarFocus2.lean`.

Results.
* `chartField_sub_isLittleO_of_isOrder`: if `h − φ = O(‖u‖^k)` on `range P` (`h`, `φ` tending to
  `0`) and `f` has strict derivative `0` at `0`, the chart fields of `h` and `φ` differ by
  `o(‖y‖^k)`.
* `exists_centerManifold_chartField_sub`: under the dichotomy with `5ε < β`, a locally invariant
  Lipschitz centre manifold `h` whose chart field differs from that of every approximate manifold
  `φ` (defect `O(‖u‖⁵)`) by `o(‖y‖⁵)`, in every chart: the 5-jet of the reduced field is that of
  the chart field of `φ`.
* `localAsymptoticStable_of_dichotomy_reduced_l2_neg`,
  `unstable_of_dichotomy_reduced_l2_pos`: if the chart field of `φ` has a 5-jet `J` in the
  rotation coordinates of `L₂` with `l₁ = 0`, then `l₂ < 0` gives local asymptotic stability and
  `l₂ > 0` instability of the full field (the planar laws
  `Degenerate.PlanarFocus.localAsymptoticStable_of_l2_neg`, `unstable_of_l2_pos` on the chart field
  of the constructed centre manifold, transferred by the reduction principle).
* At a Hopf point of a `C¹` field (`det(sI − DF(0)) = (s² + ω²) r(s)`, `r` Hurwitz, a critical
  pair `(q, p)`): `localAsymptoticStable_of_l2_neg_of_charpoly`, `unstable_of_l2_pos_of_charpoly`
  — the same laws in the critical chart `critι q`, `critπ p` (coordinates `y₀`, `y₁`,
  `frameY_rotL`), the dichotomy (with `ε = 0`) from `IsCritical.exists_dichotomy`
  (`theorem/Dynamics/HopfDichotomy.lean`).
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology Metric Asymptotics LyapunovPerron
open Degenerate.PlanarFocus (frameX frameY Jet5)

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **Chart fields of close graphs are close.** If `h − φ = O(‖u‖^k)` on `range P`, `h` and `φ`
tend to `0` at `0`, and `f` has strict derivative `0` at `0`, then
`chartField A f h ι π − chartField A f φ ι π = o(‖y‖^k)`. -/
@[tmio T, powerlib_foundation] theorem chartField_sub_isLittleO_of_isOrder {m k : ℕ}
    {f h φ : State n → State n} {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m}
    (hc : IsChart P ι π) (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0)
    (hh : Tendsto h (𝓝 0) (𝓝 0)) (hφ : Tendsto φ (𝓝 0) (𝓝 0))
    (hhφ : IsOrder P (fun u => h u - φ u) k) :
    (fun y => chartField A f h ι π y - chartField A f φ ι π y) =o[𝓝 0] fun y => ‖y‖ ^ k := by
  have hι : Tendsto ι (𝓝 0) (𝓝[Set.range P] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun y => ⟨ι y, hc.proj_ι y⟩⟩
    simpa using ι.continuous.tendsto 0
  have hι0 : Tendsto ι (𝓝 0) (𝓝 0) := by simpa using ι.continuous.tendsto 0
  -- the two lifts tend to `0`
  have h1 : Tendsto (fun y => ι y + h (ι y)) (𝓝 0) (𝓝 0) := by
    simpa using hι0.add (hh.comp hι0)
  have h2 : Tendsto (fun y => ι y + φ (ι y)) (𝓝 0) (𝓝 0) := by
    simpa using hι0.add (hφ.comp hι0)
  have hpair : Tendsto (fun y => (ι y + h (ι y), ι y + φ (ι y))) (𝓝 0) (𝓝 ((0 : State n), 0)) :=
    h1.prodMk_nhds h2
  have hs := hf.isLittleO.comp_tendsto hpair
  simp only [Function.comp_def, map_sub, zero_apply, sub_zero] at hs
  -- the distance of the lifts is `O(‖y‖^k)`
  have hd : (fun y => ι y + h (ι y) - (ι y + φ (ι y))) =O[𝓝 0] fun y => ‖y‖ ^ k := by
    have h3 := ((isOrder_natCast_iff _ k).mp hhφ).comp_tendsto hι
    refine (h3.trans ?_).congr_left fun y => by simp only [Function.comp_apply]; abel
    refine IsBigO.of_bound (‖ι‖ ^ k) (Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply, norm_pow, norm_norm]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ι.le_opNorm y) k
  refine ((π.isBigO_comp _ _).trans_isLittleO (hs.trans_isBigO hd)).congr_left fun y => ?_
  simp only [chartField, map_add, map_sub]
  abel

/-- **Every centre manifold has the 5-jet of an approximate one.** Under the centre–stable
dichotomy with `5ε < β` (`f` of class `C¹`, `f(0) = 0`, `Df(0) = 0`) there is a locally
invariant Lipschitz centre manifold `h` such that, for every `φ` (`C¹` near `0`, `φ(0) = 0`,
`Dφ(0) = 0`, values in `ker P`) with invariance defect `O(‖u‖⁵)` and every chart `ι`, `π` of
`range P`, the chart fields of `h` and `φ` differ by `o(‖y‖⁵)`; moreover the Lyapunov stability
and local asymptotic stability of the chart field are those of the full field. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_chartField_sub
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hgap : 5 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      (∀ φ : State n → State n, ContDiffAt ℝ 1 φ 0 → φ 0 = 0 → fderiv ℝ φ 0 = 0 →
        (∀ x, P (φ x) = 0) → IsOrder P (invarianceDefect A P f φ) 5 →
        ∀ {m : ℕ} (ι : State m →L[ℝ] State n) (π : State n →L[ℝ] State m), IsChart P ι π →
          (fun y => chartField A f h ι π y - chartField A f φ ι π y) =o[𝓝 0]
            fun y => ‖y‖ ^ 5) ∧
      (∀ {m : ℕ} (ι : State m →L[ℝ] State n) (π : State n →L[ℝ] State m), IsChart P ι π →
        LocalAsymptoticStable (chartField A f h ι π) 0 →
        LocalAsymptoticStable (fullField A f) 0) := by
  obtain ⟨ρ, hρ, h, L, hh, hL, -, hinv, happrox, -, -, hLAS⟩ :=
    exists_centerManifold_stable hP hε (q := 5) (by norm_num) (by exact_mod_cast hgap) hcen hst
      hf hf0 hDf
  have hs : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0 := by
    have := (hf.contDiffAt (x := 0)).hasStrictFDerivAt (by norm_num)
    rwa [hDf] at this
  refine ⟨ρ, hρ, h, L, hh, hL, hinv, fun φ hφ hφ0 hDφ hφP hdef m ι π hc => ?_, hLAS⟩
  have hd := happrox φ hφ hφ0 hDφ hφP (by exact_mod_cast hdef)
  refine chartField_sub_isLittleO_of_isOrder (k := 5) hc hs ?_ ?_ (by exact_mod_cast hd)
  · simpa [hh.map_zero] using hL.continuous.tendsto 0
  · simpa [hφ0] using hφ.continuousAt.tendsto

/-- The rotation coordinates of the chart field of the centre manifold inherit the quintic
expansion of the chart field of `φ`. -/
@[tmio T, powerlib_foundation] private theorem frame_expansion_transfer {ω : ℝ}
    {L₂ : State 2 →L[ℝ] State 2} {J : Jet5} {g g' : State 2 → State 2}
    (hgg : (fun y => g y - g' y) =o[𝓝 0] fun y => ‖y‖ ^ 5)
    (hx : (fun u => frameX (g' u) - (-ω * frameY L₂ ω u +
      Degenerate.poly3 J.F (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY L₂ ω (g' u) - (ω * frameX u +
      Degenerate.poly3 J.G (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5) :
    ((fun u => frameX (g u) - (-ω * frameY L₂ ω u +
      Degenerate.poly3 J.F (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5) ∧
    ((fun u => frameY L₂ ω (g u) - (ω * frameX u +
      Degenerate.poly3 J.G (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5) := by
  constructor
  · refine (((frameX.isBigO_comp _ _).trans_isLittleO hgg).add hx).congr_left fun u => ?_
    simp only [map_sub]
    abel
  · refine ((((frameY L₂ ω).isBigO_comp _ _).trans_isLittleO hgg).add hy).congr_left fun u => ?_
    simp only [map_sub]
    abel

/-- **The reduced `l₂ < 0` gives local asymptotic stability in any dimension** (a Bautin point
with `l₁ = 0`). Let `A` have a two-dimensional centre subspace `range P` (chart `ι`, `π`) with the
centre–stable dichotomy, `5ε < β`; `f` of class `C¹`, `f(0) = 0`, `Df(0) = 0`; `φ` an approximate
centre manifold (`C¹` near `0`, `φ(0) = 0`, `Dφ(0) = 0`, values in `ker P`, invariance defect
`O(‖u‖⁵)`), whose chart field has, in the rotation coordinates of `L₂` (`L₂² = −ω²`, `ω > 0`),
the quintic expansion of a jet `J`. If `l₁(J) = 0` and `l₂(J) < 0`, the origin is locally
asymptotically stable for `ẋ = A x + f x`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_dichotomy_reduced_l2_neg
    (hP : IsCommutingProjection A P) {K ε β ω : ℝ} (hε : 0 ≤ ε) (hgap : 5 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0)
    {φ : State n → State n} (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0) (hDφ : fderiv ℝ φ 0 = 0)
    (hφP : ∀ x, P (φ x) = 0) (hdef : IsOrder P (invarianceDefect A P f φ) 5)
    {ι : State 2 →L[ℝ] State n} {π : State n →L[ℝ] State 2} (hc : IsChart P ι π)
    {L₂ : State 2 →L[ℝ] State 2} {J : Jet5} (hω : 0 < ω)
    (hrot : ∀ y, L₂ (L₂ y) = -(ω ^ 2) • y)
    (hx : (fun u => frameX (chartField A f φ ι π u) - (-ω * frameY L₂ ω u +
      Degenerate.poly3 J.F (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY L₂ ω (chartField A f φ ι π u) - (ω * frameX u +
      Degenerate.poly3 J.G (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : J.l2 ω < 0) : LocalAsymptoticStable (fullField A f) 0 := by
  obtain ⟨ρ, hρ, h, L, hh, hL, -, hjet, hLAS⟩ :=
    exists_centerManifold_chartField_sub hP hε hgap hcen hst hf hf0 hDf
  obtain ⟨hx', hy'⟩ := frame_expansion_transfer (hjet φ hφ hφ0 hDφ hφP hdef ι π hc) hx hy
  have hcont : Continuous (chartField A f h ι π) :=
    π.continuous.comp ((A.continuous.comp ι.continuous).add
      (hf.continuous.comp (ι.continuous.add (hL.continuous.comp ι.continuous))))
  exact hLAS ι π hc (Degenerate.PlanarFocus.localAsymptoticStable_of_l2_neg hω hrot
    Filter.univ_mem hcont.continuousOn hx' hy' hl1 hl2)

/-- **The reduced `l₂ > 0` gives instability in any dimension** (a Bautin point with `l₁ = 0`;
hypotheses as `localAsymptoticStable_of_dichotomy_reduced_l2_neg`, `l₂(J) > 0`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_dichotomy_reduced_l2_pos
    (hP : IsCommutingProjection A P) {K ε β ω : ℝ} (hε : 0 ≤ ε) (hgap : 5 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0)
    {φ : State n → State n} (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0) (hDφ : fderiv ℝ φ 0 = 0)
    (hφP : ∀ x, P (φ x) = 0) (hdef : IsOrder P (invarianceDefect A P f φ) 5)
    {ι : State 2 →L[ℝ] State n} {π : State n →L[ℝ] State 2} (hc : IsChart P ι π)
    {L₂ : State 2 →L[ℝ] State 2} {J : Jet5} (hω : 0 < ω)
    (hrot : ∀ y, L₂ (L₂ y) = -(ω ^ 2) • y)
    (hx : (fun u => frameX (chartField A f φ ι π u) - (-ω * frameY L₂ ω u +
      Degenerate.poly3 J.F (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY L₂ ω (chartField A f φ ι π u) - (ω * frameX u +
      Degenerate.poly3 J.G (frameX u) (frameY L₂ ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : 0 < J.l2 ω) : Unstable (fullField A f) 0 := by
  obtain ⟨ρ, hρ, h, K', hh, hK, hinv, hjet, -⟩ :=
    exists_centerManifold_chartField_sub hP hε hgap hcen hst hf hf0 hDf
  obtain ⟨hx', hy'⟩ := frame_expansion_transfer (hjet φ hφ hφ0 hDφ hφP hdef ι π hc) hx hy
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf
  have hK1 : (0 : ℝ) < 1 + K' := by positivity
  set r₁ := R₀ / ((1 + K') * (‖ι‖ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁R : (1 + K') * ‖ι‖ * r₁ ≤ R₀ := by
    have : (1 + K') * ‖ι‖ * r₁ ≤ (1 + K') * (‖ι‖ + 1) * r₁ := by gcongr; linarith
    refine this.trans (le_of_eq ?_)
    rw [hr₁]; field_simp
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := A) (π := π) hh.map_zero hK hLf
    hr₁R
  exact unstable_of_unstable_chartField hP hh hK hc hf hρ hinv
    (Degenerate.PlanarFocus.unstable_of_l2_pos hω hrot (closedBall_mem_nhds 0 hr₁0) hLg hx' hy'
      hl1 hl2)

/-! ## At a Hopf point: the critical chart -/

section Charpoly

open Polynomial NormalForm.LyapunovCoefficient

/-- The reduction data at a Hopf point of a `C¹` field: `F = A x + f(x)` with `A = DF(0)`,
`f(0) = 0`, `Df(0) = 0`, and the dichotomy of `critP q p` with `ε = 0`. -/
@[tmio T, powerlib_foundation] private theorem exists_hopfData {F : State n → State n}
    (hF : ContDiff ℝ 1 F) {ω : ℝ} {q p : Fin n → ℂ} (hcp : IsCriticalPair F 0 ω q p)
    {r : ℂ[X]} (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ K β : ℝ, 0 < β ∧
      (∀ t, ‖expFlow (fderiv ℝ F 0) t * critP q p‖ ≤ K * Real.exp (0 * |t|)) ∧
      (∀ t, 0 ≤ t → ‖expFlow (fderiv ℝ F 0) t * (1 - critP q p)‖ ≤ K * Real.exp (-(β * t))) ∧
      fullField (fderiv ℝ F 0) (fun x => F x - fderiv ℝ F 0 x) = F ∧
      ContDiff ℝ 1 (fun x => F x - fderiv ℝ F 0 x) ∧ (fun x => F x - fderiv ℝ F 0 x) 0 = 0 ∧
      fderiv ℝ (fun x => F x - fderiv ℝ F 0 x) 0 = 0 ∧
      IsCommutingProjection (fderiv ℝ F 0) (critP q p) ∧
      IsChart (critP q p) (critι q) (critπ p) := by
  have hc : IsCritical (fderiv ℝ F 0) ω q p := IsCriticalPair.isCritical hcp rfl
  obtain ⟨K, β, hβ, hcen, hst⟩ := hc.exists_dichotomy hchar hr
  refine ⟨K, β, hβ, hcen, hst, by funext x; simp [fullField], hF.sub (fderiv ℝ F 0).contDiff,
    by simp [hcp.equilibrium], ?_, hc.isCommutingProjection, hc.isChart⟩
  have hd := ((hF.differentiable one_ne_zero 0).hasFDerivAt.sub
    (fderiv ℝ F 0).hasFDerivAt).fderiv
  rw [show (fun x => F x - fderiv ℝ F 0 x) = F - ⇑(fderiv ℝ F 0) from rfl, hd, sub_self]

/-- **`l₂ < 0` at a Hopf point of a `C¹` field, in any dimension.** Let `(q, p)` be a critical
pair of `F` at `0` with `det(sI − DF(0)) = (s² + ω²) r(s)`, `r` Hurwitz; let `φ` (`C¹` near `0`,
`φ(0) = 0`, `Dφ(0) = 0`, values in `ker critP`) have invariance defect `O(‖u‖⁵)` for
`A = DF(0)`, `f = F − A`, and let its chart field in the critical chart (`critι q`, `critπ p`;
coordinates `y₀`, `y₁`, `frameY_rotL`) have the quintic expansion of a jet `J`. If `l₁(J) = 0` and
`l₂(J) < 0`, `F` is locally asymptotically stable at `0`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_l2_neg_of_charpoly
    {F : State n → State n} (hF : ContDiff ℝ 1 F) {ω : ℝ} {q p : Fin n → ℂ}
    (hcp : IsCriticalPair F 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {φ : State n → State n}
    (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0) (hDφ : fderiv ℝ φ 0 = 0)
    (hφP : ∀ x, critP q p (φ x) = 0)
    (hdef : IsOrder (critP q p)
      (invarianceDefect (fderiv ℝ F 0) (critP q p) (fun x => F x - fderiv ℝ F 0 x) φ) 5)
    {J : Jet5}
    (hx : (fun u => frameX (chartField (fderiv ℝ F 0) (fun x => F x - fderiv ℝ F 0 x) φ
        (critι q) (critπ p) u) - (-ω * frameY (rotL ω) ω u +
      Degenerate.poly3 J.F (frameX u) (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY (rotL ω) ω (chartField (fderiv ℝ F 0) (fun x => F x - fderiv ℝ F 0 x)
        φ (critι q) (critπ p) u) - (ω * frameX u +
      Degenerate.poly3 J.G (frameX u) (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : J.l2 ω < 0) : LocalAsymptoticStable F 0 := by
  obtain ⟨K, β, hβ, hcen, hst, hFf, hf, hf0, hDf, hP, hc⟩ := exists_hopfData hF hcp hchar hr
  rw [← hFf]
  exact localAsymptoticStable_of_dichotomy_reduced_l2_neg hP le_rfl (by linarith) hcen hst hf
    hf0 hDf hφ hφ0 hDφ hφP hdef hc hcp.freq_pos (rotL_rotL ω) hx hy hl1 hl2

/-- **`l₂ > 0` at a Hopf point of a `C¹` field, in any dimension** (hypotheses as
`localAsymptoticStable_of_l2_neg_of_charpoly`, `l₂(J) > 0`): `F` is unstable at `0`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_l2_pos_of_charpoly
    {F : State n → State n} (hF : ContDiff ℝ 1 F) {ω : ℝ} {q p : Fin n → ℂ}
    (hcp : IsCriticalPair F 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {φ : State n → State n}
    (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0) (hDφ : fderiv ℝ φ 0 = 0)
    (hφP : ∀ x, critP q p (φ x) = 0)
    (hdef : IsOrder (critP q p)
      (invarianceDefect (fderiv ℝ F 0) (critP q p) (fun x => F x - fderiv ℝ F 0 x) φ) 5)
    {J : Jet5}
    (hx : (fun u => frameX (chartField (fderiv ℝ F 0) (fun x => F x - fderiv ℝ F 0 x) φ
        (critι q) (critπ p) u) - (-ω * frameY (rotL ω) ω u +
      Degenerate.poly3 J.F (frameX u) (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY (rotL ω) ω (chartField (fderiv ℝ F 0) (fun x => F x - fderiv ℝ F 0 x)
        φ (critι q) (critπ p) u) - (ω * frameX u +
      Degenerate.poly3 J.G (frameX u) (frameY (rotL ω) ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : 0 < J.l2 ω) : Unstable F 0 := by
  obtain ⟨K, β, hβ, hcen, hst, hFf, hf, hf0, hDf, hP, hc⟩ := exists_hopfData hF hcp hchar hr
  rw [← hFf]
  exact unstable_of_dichotomy_reduced_l2_pos hP le_rfl (by linarith) hcen hst hf hf0 hDf hφ hφ0
    hDφ hφP hdef hc hcp.freq_pos (rotL_rotL ω) hx hy hl1 hl2

end Charpoly

end powerlib.Dynamics.CenterManifold
