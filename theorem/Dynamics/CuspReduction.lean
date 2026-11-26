import theorem.Dynamics.SaddleNodeReduction
import theorem.Dynamics.HopfDichotomy

/-! # Stability at a cusp point: the cubic coefficient on a one-dimensional centre manifold
(foundation)

At an equilibrium of `ẋ = F(x)` on `ℝⁿ` whose linearization has a simple zero eigenvalue, the
rest of its spectrum in the open left half plane, and a vanishing fold coefficient
`a = ½⟨p, B(q, q)⟩ = 0` (a cusp point of the fold), the centre manifold is a curve carrying
`u̇ = c u³ + o(u³)` with Kuznetsov's cubic coefficient `c = (1/6)⟨p, C(q, q, q) + 3 B(q, w)⟩`,
`w` a solution of the homological equation `A w = −B(q, q)`. **If `c > 0` the equilibrium is
unstable; if `c < 0` it is locally asymptotically stable.**

Scope.
* Generic: `State n = ℝⁿ`, a field `F` of class `C¹` and analytic at the equilibrium `0`
  (`F(0) = 0`; analyticity gives the cubic Taylor expansion and the symmetry of `D²F(0)`, as in
  `theorem/Dynamics/HopfDichotomy.lean`), `A = DF(0)`, `B = D²F(0)`, `C = D³F(0)`, a normalised
  null pair `(q, p)` of `A` (`NormalForm.BogdanovTakens.IsNullPair`) and a complex polynomial
  `r` with `det(sI − A) = s r(s)` and every root of `r` in the open left half plane. The
  homological equation `A w = −B(q, q)` is a hypothesis: a solution exists exactly when `a = 0`,
  and every solution gives the same `c` (`cuspCoeff_add_smul`; `⟨p, w⟩ = 0` is not needed).
* Lyapunov instability and local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) of the equilibrium; `c = 0` is not decided, and the unfolding of the
  cusp (two-parameter families, the two fold curves and their tangency) is not stated. Nothing
  here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.2 (the cusp
normal form `u̇ = β₁ + β₂ u + s u³`), §8.7 (the projection formula
`c = (1/6)⟨p, C(q, q, q) + 3 B(q, h₂)⟩`, `A h₂ = −B(q, q)`) and §5.1 (Theorem 5.2, the reduction
principle); Carr, *Applications of Centre Manifold Theory* (1981), §2.4–§2.5. The centre manifold
with its quadratic part is `Dynamics.CenterManifold.exists_centerManifold_hasQuadraticPart`
(`theorem/Dynamics/CenterReduction.lean`), with attraction and the stability transfer
`Dynamics.CenterManifold.exists_centerManifold_stable`
(`theorem/Dynamics/CenterReductionStability.lean`); the reduced field at third order is
`Dynamics.CenterManifold.chartField_expansion`; the chart and the dichotomy of the centre line are
those of `theorem/Dynamics/SaddleNodeReduction.lean`.

Results.
* `NormalForm.BogdanovTakens.cuspCoeff` (the cubic coefficient),
  `IsNullPair.foldCoeff_eq_zero_of_homological` (a solution of the homological equation forces
  `a = 0`), `cuspCoeff_add_smul` (`c(w + s q) = c(w) + s a`).
* `IsNullPair.exists_dichotomy_zero`: the dichotomy of a simple zero eigenvalue with `ε = 0`
  (`e^{tA}P = P`), so every gap condition `kε < β` of the centre-manifold laws holds.
* The one-dimensional laws (namespace `Dynamics.CenterManifold`):
  `unstable_of_cubic_isLittleO` (`G(y) = c y₀³ e₀ + o(‖y‖³)`, `c > 0`, `G` Lipschitz near `0`:
  Chetaev with `W = y₀`), `localAsymptoticStable_of_cubic_isLittleO` (`c < 0`, `G` continuous near
  `0`: Lyapunov with `V = y₀²`).
* **`Dynamics.CenterManifold.unstable_of_cuspCoeff_pos_of_charpoly`**: `F` `C¹`, analytic at `0`,
  `F(0) = 0`, a normalised null pair of `DF(0)`, `det(sI − DF(0)) = s r(s)` with `r` Hurwitz,
  `DF(0) w = −D²F(0)(q, q)` and `cuspCoeff F 0 q p w > 0` ⇒ `Unstable F 0`;
  **`Dynamics.CenterManifold.localAsymptoticStable_of_cuspCoeff_neg_of_charpoly`**: the same with
  `cuspCoeff F 0 q p w < 0` ⇒ `LocalAsymptoticStable F 0`. The quadratic part of the centre
  manifold is `H₀(u, v) = ⟨p, u⟩⟨p, v⟩ w'/2`, `w' = w − ⟨p, w⟩ q` (private
  `exists_cuspData`).
-/

noncomputable section

namespace powerlib.NormalForm.BogdanovTakens
open Set Filter Topology Asymptotics Complex Polynomial Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient powerlib.Dynamics.LyapunovPerron

section Coefficient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Kuznetsov's cubic (cusp) coefficient `c = (1/6)⟨p, C(q, q, q) + 3 B(q, w)⟩` of the field `f`
at `x`, `B = D²f(x)`, `C = D³f(x)`, read with a vector `w` (the solution of the homological
equation `A w = −B(q, q)` of the centre line). -/
def cuspCoeff (f : E → E) (x q p w : E) : ℝ :=
  (⟪p, iteratedFDeriv ℝ 3 f x ![q, q, q]⟫ + 3 * ⟪p, fderiv ℝ (fderiv ℝ f) x q w⟫) / 6

/-- A solution of the homological equation `A w = −B(q, q)` forces the fold coefficient to
vanish: `⟨p, B(q, q)⟩ = −⟨p, A w⟩ = 0`. -/
@[tmio T, powerlib_foundation] theorem IsNullPair.foldCoeff_eq_zero_of_homological
    {f : E → E} {x q p w : E} (h : IsNullPair (fderiv ℝ f x) q p)
    (hw : fderiv ℝ f x w = -fderiv ℝ (fderiv ℝ f) x q q) : foldCoeff f x q p = 0 := by
  have h1 := h.inner_p_map w
  rw [hw, inner_neg_right, neg_eq_zero] at h1
  rw [foldCoeff, h1, zero_div]

/-- The cubic coefficient changes by the fold coefficient along the null vector:
`c(w + s q) = c(w) + s a`; at a cusp (`a = 0`) it does not depend on the solution `w`. -/
@[tmio T, powerlib_foundation] theorem cuspCoeff_add_smul (f : E → E) (x q p w : E) (s : ℝ) :
    cuspCoeff f x q p (w + s • q) = cuspCoeff f x q p w + s * foldCoeff f x q p := by
  simp only [cuspCoeff, foldCoeff, map_add, map_smul, inner_add_right, inner_smul_right]
  ring

end Coefficient

section Dichotomy

variable {n : ℕ} {A : State n →L[ℝ] State n} {q p : State n}

/-- **The dichotomy of a simple zero eigenvalue with `ε = 0`.** On the centre line `e^{tA}P = P`
(`AP = 0`), so the centre bound holds with `ε = 0`: `‖e^{tA}P‖ ≤ K`,
`‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`), `β > 0`. -/
@[tmio T, powerlib_foundation] theorem IsNullPair.exists_dichotomy_zero (hc : IsNullPair A q p)
    {r : ℂ[X]} (hchar : (cmat A).charpoly = X * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ K β : ℝ, 0 < β ∧ (∀ t, ‖expFlow A t * snP q p‖ ≤ K * Real.exp (0 * |t|)) ∧
      ∀ t, 0 ≤ t → ‖expFlow A t * (1 - snP q p)‖ ≤ K * Real.exp (-(β * t)) := by
  obtain ⟨K, ε, β, hε, hεβ, -, hst⟩ := hc.exists_dichotomy hchar hr
  have hAP : A * snP q p = 0 := hc.map_comp_snP
  refine ⟨max K ‖snP q p‖, β, hε.trans hεβ, fun t => ?_, fun t ht => ?_⟩
  · rw [expFlow_mul_eq_of_nilpotent (by rw [hAP, mul_zero]) t, hAP, smul_zero, add_zero,
      zero_mul, Real.exp_zero, mul_one]
    exact le_max_right _ _
  · exact (hst t ht).trans (by gcongr; exact le_max_left _ _)

end Dichotomy

end powerlib.NormalForm.BogdanovTakens

namespace powerlib.Dynamics.CenterManifold
open Set Filter Topology Asymptotics Complex Polynomial Matrix
open scoped RealInnerProductSpace
open powerlib.NormalForm.LyapunovCoefficient powerlib.Dynamics.LyapunovPerron

/-! ## The one-dimensional laws -/

/-- **A cubic scalar field with positive coefficient is unstable.** A field `G` on `State 1`,
Lipschitz near `0`, with `G(y) = c y₀³ e₀ + o(‖y‖³)` and `c > 0` is unstable at `0`: `W(y) = y₀`
is positive for `y₀ > 0` and `Ẇ = c y₀³ + o(y₀³) > 0` there (Chetaev). -/
@[tmio T, powerlib_foundation] theorem unstable_of_cubic_isLittleO {G : State 1 → State 1}
    {U : Set (State 1)} {K : NNReal} (hU : U ∈ 𝓝 0) (hG : LipschitzOnWith K G U) {c : ℝ}
    (hc : 0 < c)
    (hexp : (fun y => G y - (c * y 0 ^ 3) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =o[𝓝 0]
      fun y => ‖y‖ ^ 3) :
    Unstable G 0 := by
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (hexp.def hc2)
  have hW : ContDiff ℝ 1 (fun y : State 1 => y 0) := by fun_prop
  refine unstable_of_chetaev_lipschitzOn (W := fun y : State 1 => y 0) (r := r / 2) hU hG
    hW (half_pos hr) (fun ε hε => ?_) (fun y hy hWy => ?_)
  · refine ⟨(ε / 2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ), ?_, ?_⟩
    · rw [sub_zero, norm_smul]
      simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      linarith
    · simp only [PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, ite_true, mul_one]
      positivity
  · change 0 < y 0 at hWy
    have hd : HasFDerivAt (fun y : State 1 => y 0) (coord (n := 1) 0) y := hasFDerivAt_coord 0 y
    rw [hd.fderiv, coord_apply]
    have hyr : dist y 0 < r := by rw [dist_eq_norm]; linarith
    have hby := hb hyr
    have e2 : (G y - (c * y 0 ^ 3) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 =
        G y 0 - c * y 0 ^ 3 := by simp
    rw [norm_pow, norm_norm, NormalForm.norm_state1 y, NormalForm.norm_state1, e2,
      abs_of_pos hWy] at hby
    have h1 := neg_abs_le (G y 0 - c * y 0 ^ 3)
    have h3 : 0 < y 0 ^ 3 := pow_pos hWy 3
    nlinarith

/-- **A cubic scalar field with negative coefficient is locally asymptotically stable.** A field
`G` on `State 1`, continuous near `0`, with `G(y) = c y₀³ e₀ + o(‖y‖³)` and `c < 0` is locally
asymptotically stable at `0`: `V(y) = y₀²` has `V̇ = 2c y₀⁴ + o(y₀⁴) < 0` near `0`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_cubic_isLittleO
    {G : State 1 → State 1} {U : Set (State 1)} (hU : U ∈ 𝓝 0) (hG : ContinuousOn G U) {c : ℝ}
    (hc : c < 0)
    (hexp : (fun y => G y - (c * y 0 ^ 3) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =o[𝓝 0]
      fun y => ‖y‖ ^ 3) :
    LocalAsymptoticStable G 0 := by
  have hc2 : 0 < -c / 2 := by linarith
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (hexp.def hc2)
  obtain ⟨σ, hσ, hσU⟩ := Metric.mem_nhds_iff.mp hU
  have hy0 : ∀ y : State 1, y ≠ 0 → y 0 ≠ 0 := fun y hne h0 => hne (by
    ext i; fin_cases i; simpa using h0)
  refine Dynamics.localAsymptoticStable_of_lie_neg one_pos (V := fun y : State 1 => y 0 * y 0)
    (lt_min hr hσ) (by fun_prop)
    (hG.mono fun y hy => hσU (Metric.ball_subset_ball (min_le_right _ _) hy)) (by simp)
    (fun y _ hne => mul_self_pos.mpr (hy0 y (by simpa using hne))) (fun y hy hne => ?_)
  simp only [sub_zero] at hy hne
  have hd : HasFDerivAt (fun y : State 1 => y 0 * y 0)
      (y 0 • coord (n := 1) 0 + y 0 • coord (n := 1) 0) y :=
    (hasFDerivAt_coord 0 y).mul (hasFDerivAt_coord 0 y)
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, coord_apply,
    smul_eq_mul]
  have hyr : dist y 0 < r := by
    rw [dist_eq_norm, sub_zero]; exact hy.trans_le (min_le_left _ _)
  have hby := hb hyr
  have e2 : (G y - (c * y 0 ^ 3) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 =
      G y 0 - c * y 0 ^ 3 := by simp
  rw [norm_pow, norm_norm, NormalForm.norm_state1 y, NormalForm.norm_state1, e2] at hby
  set d := G y 0 - c * y 0 ^ 3 with hd'
  have hne0 := hy0 y hne
  have hpos : 0 < |y 0| := abs_pos.mpr hne0
  have h1 : |y 0| * |d| ≤ |y 0| * (-c / 2 * |y 0| ^ 3) := mul_le_mul_of_nonneg_left hby hpos.le
  have h2 := le_abs_self (y 0 * d)
  rw [abs_mul] at h2
  have h4 : |y 0| * (-c / 2 * |y 0| ^ 3) = -c / 2 * ((y 0 * y 0) * (y 0 * y 0)) := by
    rw [show |y 0| * (-c / 2 * |y 0| ^ 3) = -c / 2 * ((|y 0| * |y 0|) * (|y 0| * |y 0|)) by
      ring, abs_mul_abs_self]
  have h5 : 0 < (y 0 * y 0) * (y 0 * y 0) :=
    mul_pos (mul_self_pos.mpr hne0) (mul_self_pos.mpr hne0)
  have h6 : c * ((y 0 * y 0) * (y 0 * y 0)) < 0 := mul_neg_of_neg_of_pos hc h5
  have e3 : y 0 * G y 0 + y 0 * G y 0 = 2 * c * ((y 0 * y 0) * (y 0 * y 0)) + 2 * (y 0 * d) := by
    rw [hd']; ring
  rw [e3]
  linarith

/-! ## The cusp laws -/

section Cusp

open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff cuspCoeff snι snπ snP snι_apply
  snπ_apply)

variable {n : ℕ}

/-- The reduction data at a cusp point: `A = DF(0)`, `f = F − A`, `Q = D²F(0)/2`,
`C = D³F(0)/6`, the quadratic part `H₀(u, v) = ⟨p, u⟩⟨p, v⟩ w'/2` of the centre line
(`w' = w − ⟨p, w⟩ q`) solving the homological equation, the dichotomy with `ε = 0`, and the
reduced field `π[Q(ιy, ιy) + 2Q(ιy, H₀(ιy, ιy)) + C(ιy, ιy, ιy)] = c y₀³ e₀`. -/
@[tmio T, powerlib_foundation] private theorem exists_cuspData {F : State n → State n}
    (hF : ContDiff ℝ 1 F) (ha : AnalyticAt ℝ F 0) (hF0 : F 0 = 0) {q p w : State n}
    (hnp : IsNullPair (fderiv ℝ F 0) q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = X * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0)
    (hw : fderiv ℝ F 0 w = -fderiv ℝ (fderiv ℝ F) 0 q q) :
    ∃ (f : State n → State n) (Q H₀ : State n →L[ℝ] State n →L[ℝ] State n)
      (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)) (K β : ℝ),
      fullField (fderiv ℝ F 0) f = F ∧ 0 < β ∧
      (∀ t, ‖expFlow (fderiv ℝ F 0) t * snP q p‖ ≤ K * Real.exp (0 * |t|)) ∧
      (∀ t, 0 ≤ t → ‖expFlow (fderiv ℝ F 0) t * (1 - snP q p)‖ ≤ K * Real.exp (-(β * t))) ∧
      ContDiff ℝ 1 f ∧ f 0 = 0 ∧ fderiv ℝ f 0 = 0 ∧
      (fun x => f x - (Q x x + C ![x, x, x])) =o[𝓝 0] (fun x => ‖x‖ ^ 3) ∧
      IsHomological (fderiv ℝ F 0) (snP q p) Q H₀ ∧ (∀ u v, snP q p (H₀ u v) = 0) ∧
      ∀ y : State 1, snπ p (fderiv ℝ F 0 (snι q y)) + snπ p (Q (snι q y) (snι q y) +
        Q (snι q y) (H₀ (snι q y) (snι q y)) + Q (H₀ (snι q y) (snι q y)) (snι q y) +
        C ![snι q y, snι q y, snι q y]) =
        (cuspCoeff F 0 q p w * y 0 ^ 3) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  set A := fderiv ℝ F 0 with hAdef
  set B := fderiv ℝ (fderiv ℝ F) 0 with hBdef
  set f : State n → State n := fun x => F x - A x with hfdef
  have hFf : fullField A f = F := by funext x; simp [fullField, hfdef]
  obtain ⟨K, β, hβ, hcen, hst⟩ := hnp.exists_dichotomy_zero hchar hr
  have hDf : fderiv ℝ f 0 = 0 := by
    have h := (hF.differentiable one_ne_zero 0).hasFDerivAt.sub A.hasFDerivAt
    rw [← hAdef, sub_self] at h
    exact h.fderiv
  have hsym : ∀ u v, B u v = B v u :=
    ContDiffAt.isSymmSndFDerivAt (ha.contDiffAt (n := 2)) (by simp)
  have hfold : ⟪p, B q q⟫ = 0 := by
    have h1 := hnp.inner_p_map w
    rw [hw, inner_neg_right, neg_eq_zero] at h1
    exact h1
  set w' := w - ⟪p, w⟫ • q with hw'
  have hpw' : ⟪p, w'⟫ = 0 := by
    rw [hw', inner_sub_right, real_inner_smul_right, hnp.inner_p_q, mul_one, sub_self]
  have hAw' : A w' = -B q q := by
    rw [hw', map_sub, map_smul, hnp.map_q, smul_zero, sub_zero, hw]
  have hBw' : ⟪p, B q w'⟫ = ⟪p, B q w⟫ := by
    rw [hw', map_sub, map_smul, inner_sub_right, real_inner_smul_right, hfold, mul_zero,
      sub_zero]
  set H₀ : State n →L[ℝ] State n →L[ℝ] State n :=
    (innerSL ℝ p).smulRight ((innerSL ℝ p).smulRight ((1 / 2 : ℝ) • w')) with hH₀
  have hH₀ap : ∀ u v, H₀ u v = (⟪p, u⟫ * ⟪p, v⟫ / 2) • w' := by
    intro u v
    simp only [hH₀, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, _root_.smul_apply,
      smul_smul]
    congr 1
    ring
  have hPx : ∀ x, snP q p x = ⟪p, x⟫ • q := fun x => IsNullPair.snP_apply x
  refine ⟨f, (1 / 2 : ℝ) • B, H₀, (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0, K, β, hFf, hβ, hcen,
    hst, hF.sub A.contDiff, by simp [hfdef, hF0], hDf, ?_, ?_, ?_, ?_⟩
  · have hT := taylor3_isBigO ha
    have h43 : (fun x : State n => ‖x‖ ^ 4) =o[𝓝 0] fun x => ‖x‖ ^ 3 := by
      simpa using norm_pow_isLittleO (E := State n) (k := 3) (k' := 4) (by norm_num) Set.univ
    refine (hT.trans_isLittleO h43).congr_left fun x => ?_
    simp only [hfdef, hF0, zero_add]
    rw [_root_.smul_apply, _root_.smul_apply, _root_.smul_apply, ← hAdef, ← hBdef]
    abel
  · intro u hu
    have hu' : u = ⟪p, u⟫ • q := by rw [← hPx u, hu]
    obtain ⟨s, rfl⟩ : ∃ s : ℝ, u = s • q := ⟨_, hu'⟩
    have hPA : snP q p (A (s • q)) = 0 := by
      rw [map_smul, hnp.map_q, smul_zero, map_zero]
    have hsum : A (H₀ (s • q) (s • q)) + ((1 / 2 : ℝ) • B) (s • q) (s • q) = 0 := by
      simp only [hH₀ap, map_smul, hAw', hnp.inner_p_q, _root_.smul_apply]
      module
    rw [hPA, map_zero, map_zero, _root_.zero_apply, add_zero, ← map_add, hsum, map_zero]
  · intro u v
    rw [hPx, hH₀ap, real_inner_smul_right, hpw', mul_zero, zero_smul]
  · intro y
    have e3 : (![snι q y, snι q y, snι q y] : Fin 3 → State n) =
        fun i => (fun _ : Fin 3 => y 0) i • (![q, q, q] : Fin 3 → State n) i := by
      funext i; fin_cases i <;> simp [snι_apply]
    have hC3 : ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0) ![snι q y, snι q y, snι q y] =
        ((1 / 6 : ℝ) * y 0 ^ 3) • iteratedFDeriv ℝ 3 F 0 ![q, q, q] := by
      rw [e3, _root_.smul_apply, ContinuousMultilinearMap.map_smul_univ,
        smul_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hC3, ← map_add, snπ_apply]
    congr 1
    simp only [snι_apply, hH₀ap, map_smul, _root_.smul_apply, inner_add_right,
      real_inner_smul_right, hnp.map_q, inner_zero_right, hnp.inner_p_q, smul_zero]
    rw [hsym w' q, hBw', hfold, NormalForm.BogdanovTakens.cuspCoeff]
    ring

/-- **A cusp point with a positive cubic coefficient is unstable.** Let `F` be `C¹` and analytic
at the equilibrium `0` (`F(0) = 0`), let `(q, p)` be a normalised null pair of `A = DF(0)` and
let `det(sI − A) = s r(s)` with every root of `r` in the open left half plane. If `w` solves the
homological equation `A w = −D²F(0)(q, q)` (so the fold coefficient vanishes,
`IsNullPair.foldCoeff_eq_zero_of_homological`) and Kuznetsov's cubic coefficient
`c = (1/6)⟨p, D³F(0)(q, q, q) + 3 D²F(0)(q, w)⟩` (`NormalForm.BogdanovTakens.cuspCoeff`) is
positive, the origin is unstable: the centre manifold (`exists_centerManifold_hasQuadraticPart`)
carries `u̇ = c u³ + o(u³)` (`chartField_expansion`), unstable by `unstable_of_cubic_isLittleO`,
and instability transfers to the full field (`unstable_of_unstable_chartField`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_cuspCoeff_pos_of_charpoly
    {F : State n → State n} (hF : ContDiff ℝ 1 F) (ha : AnalyticAt ℝ F 0) (hF0 : F 0 = 0)
    {q p w : State n} (hnp : IsNullPair (fderiv ℝ F 0) q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = X * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0)
    (hw : fderiv ℝ F 0 w = -fderiv ℝ (fderiv ℝ F) 0 q q) (hc : 0 < cuspCoeff F 0 q p w) :
    Unstable F 0 := by
  obtain ⟨f, Q, H₀, C, K, β, hFf, hβ, hcen, hst, hf, hf0, hDf, hfQC, hhom, hPH, hred⟩ :=
    exists_cuspData hF ha hF0 hnp hchar hr hw
  have hP := hnp.isCommutingProjection
  have hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    have hCb : (fun x : State n => C ![x, x, x]) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
      (isBigO_trilin C (fun x => x) (fun x => x) fun x => x).congr_right fun x => by ring
    exact (hfQC.isBigO.add hCb).congr_left fun x => by abel
  obtain ⟨ρ, hρ, h, L, hh, hL, hH, hinv⟩ := exists_centerManifold_hasQuadraticPart hP le_rfl
    (by linarith) hcen hst hf hf0 hDf hf2 hhom hPH
  have hcI := hnp.isChart
  have hg : (fun y => chartField (fderiv ℝ F 0) f h (snι q) (snπ p) y -
      (cuspCoeff F 0 q p w * y 0 ^ 3) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =o[𝓝 0]
      fun y => ‖y‖ ^ 3 :=
    (chartField_expansion (A := fderiv ℝ F 0) hcI hfQC hH).congr_left fun y => by rw [hred y]
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf
  set r₁ := R₀ / ((1 + L) * (‖snι q‖ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁R : (1 + L) * ‖snι q‖ * r₁ ≤ R₀ := by
    have : (1 + L) * ‖snι q‖ * r₁ ≤ (1 + L) * (‖snι q‖ + 1) * r₁ := by gcongr; linarith
    refine this.trans (le_of_eq ?_)
    rw [hr₁]; field_simp
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := fderiv ℝ F 0) (π := snπ p)
    hh.map_zero hL hLf hr₁R
  have hredU : Unstable (chartField (fderiv ℝ F 0) f h (snι q) (snπ p)) 0 :=
    unstable_of_cubic_isLittleO (Metric.closedBall_mem_nhds 0 hr₁0) hLg hc hg
  rw [← hFf]
  exact unstable_of_unstable_chartField hP hh hL hcI hf hρ hinv hredU

/-- **A cusp point with a negative cubic coefficient is locally asymptotically stable** (the
stability counterpart of `unstable_of_cuspCoeff_pos_of_charpoly`): under the same hypotheses,
`cuspCoeff F 0 q p w < 0` gives local asymptotic stability of `F` at `0` (centre manifold with
attraction and Carr's approximation, `exists_centerManifold_stable`; reduced law
`localAsymptoticStable_of_cubic_isLittleO`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_cuspCoeff_neg_of_charpoly
    {F : State n → State n} (hF : ContDiff ℝ 1 F) (ha : AnalyticAt ℝ F 0) (hF0 : F 0 = 0)
    {q p w : State n} (hnp : IsNullPair (fderiv ℝ F 0) q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = X * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0)
    (hw : fderiv ℝ F 0 w = -fderiv ℝ (fderiv ℝ F) 0 q q) (hc : cuspCoeff F 0 q p w < 0) :
    LocalAsymptoticStable F 0 := by
  obtain ⟨f, Q, H₀, C, K, β, hFf, hβ, hcen, hst, hf, hf0, hDf, hfQC, hhom, hPH, hred⟩ :=
    exists_cuspData hF ha hF0 hnp hchar hr hw
  have hP := hnp.isCommutingProjection
  have hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    have hCb : (fun x : State n => C ![x, x, x]) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
      (isBigO_trilin C (fun x => x) (fun x => x) fun x => x).congr_right fun x => by ring
    exact (hfQC.isBigO.add hCb).congr_left fun x => by abel
  obtain ⟨ρ, hρ, h, L, hh, hL, -, -, happrox, -, -, hLAS⟩ :=
    exists_centerManifold_stable hP (ε := 0) le_rfl (q := 3) (by norm_num) (by linarith) hcen
      hst hf hf0 hDf
  have hH : HasQuadraticPart (snP q p) h H₀ := by
    have hd := happrox (quadGraph (snP q p) H₀) (contDiff_quadGraph (snP q p) H₀).contDiffAt
      (by simp [quadGraph]) (fderiv_quadGraph_zero (snP q p) H₀) (fun x => hPH _ _)
      (isOrder_invarianceDefect_quadGraph hP hhom hf2)
    refine hd.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with v hv
    obtain ⟨u, rfl⟩ := hv
    simp [quadGraph, hP.idem]
  have hcI := hnp.isChart
  have hg : (fun y => chartField (fderiv ℝ F 0) f h (snι q) (snπ p) y -
      (cuspCoeff F 0 q p w * y 0 ^ 3) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =o[𝓝 0]
      fun y => ‖y‖ ^ 3 :=
    (chartField_expansion (A := fderiv ℝ F 0) hcI hfQC hH).congr_left fun y => by rw [hred y]
  have hcont : Continuous (chartField (fderiv ℝ F 0) f h (snι q) (snπ p)) :=
    (snπ p).continuous.comp (((fderiv ℝ F 0).continuous.comp (snι q).continuous).add
      (hf.continuous.comp ((snι q).continuous.add (hL.continuous.comp (snι q).continuous))))
  rw [← hFf]
  exact hLAS (snι q) (snπ p) hcI
    (localAsymptoticStable_of_cubic_isLittleO Filter.univ_mem hcont.continuousOn hc hg)

end Cusp

end powerlib.Dynamics.CenterManifold
