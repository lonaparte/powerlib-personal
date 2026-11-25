import theorem.Dynamics.CenterReductionBT
import theorem.NormalForm.Scalar

/-! # Instability at a saddle-node point: reduction at a simple zero eigenvalue (foundation)

At an equilibrium of `ẋ = F(x)` on `ℝⁿ` whose linearization has a simple zero eigenvalue and the
rest of its spectrum in the open left half plane, the centre manifold is a curve and the field on
it is `u̇ = a u² + o(u²)`, `a` Kuznetsov's fold coefficient `½⟨p, B(q, q)⟩`
(`NormalForm.BogdanovTakens.foldCoeff`) of a normalised null pair `(q, p)`
(`NormalForm.BogdanovTakens.IsNullPair`). **If `a ≠ 0` the equilibrium is unstable** (Lyapunov):
solutions on one side of the centre manifold leave every small ball.

Scope.
* Generic: `State n = ℝⁿ`, a field `F` of class `C²` with `F(0) = 0`, `A = DF(0)`, a normalised
  null pair `(q, p)` of `A` (`A q = 0`, `⟨p, A v⟩ = 0`, `⟨p, q⟩ = 1`) and a complex polynomial
  `r` with `det(sI − A) = s r(s)` and every root of `r` in the open left half plane (so the zero
  eigenvalue is simple and no other eigenvalue lies on the imaginary axis). The chart of the
  centre line is `ι y = y₀ q`, `π x = ⟨p, x⟩`, the projection `P = ιπ`.
* Lyapunov instability only (LeanForControl's `Unstable`); the semistability of the reduced flow
  (attraction from one side) is not stated. Other eigenvalues in the open right half plane give
  instability by linearization already; eigenvalues on the imaginary axis besides the simple zero
  (zero–Hopf, Bogdanov–Takens) are not covered. Nothing here describes a physical system
  (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §3.2 (the fold
normal form), §5.1 (Theorem 5.2, the reduction principle) and §5.4 (the projection formula
`a = ½⟨p, B(q, q)⟩`); Carr, *Applications of Centre Manifold Theory* (1981), §2.4. The centre
manifold is `Dynamics.CenterManifold.exists_centerManifold`; the reduced field at second order is
`Dynamics.CenterManifold.chartField_expansion2` (`theorem/Dynamics/CenterReductionBT.lean`); the
instability transfer is `Dynamics.CenterManifold.unstable_of_unstable_chartField`
(`theorem/Dynamics/CenterReduction.lean`).

Results.
* **`Dynamics.CenterManifold.unstable_of_quadratic_isLittleO`**: a scalar field on `State 1`,
  Lipschitz near `0`, with `g(y) = a y₀² + o(‖y‖²)` and `a ≠ 0` is unstable at `0` (Chetaev with
  `W(y) = a y₀`).
* The chart of the centre line (namespace `NormalForm.BogdanovTakens`, next to `IsNullPair`):
  `snι`, `snπ`, `snP`, `snι_apply`, `snπ_apply`, `IsNullPair.snπ_snι`, `IsNullPair.isChart`,
  `IsNullPair.snP_apply`, `IsNullPair.isCommutingProjection`, `IsNullPair.map_comp_snP`
  (`AP = 0`), `IsNullPair.snP_q`.
* The dichotomy: `IsNullPair.stablePart_hurwitz` (the stable part `A(1 − P) − P` is Hurwitz),
  **`IsNullPair.exists_dichotomy`** (`‖e^{tA}P‖ ≤ K e^{ε|t|}`, `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}`,
  `0 < ε < β`).
* **`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`**: `F` of class `C²`,
  `F(0) = 0`, a normalised null pair `(q, p)` of `DF(0)`, `det(sI − DF(0)) = s r(s)` with `r`
  Hurwitz and `foldCoeff F 0 q p ≠ 0` ⇒ `Unstable F 0`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold
open Set Filter Topology Asymptotics Complex Polynomial Matrix
open scoped RealInnerProductSpace
open powerlib.NormalForm.LyapunovCoefficient powerlib.Dynamics.LyapunovPerron

/-! ## The one-dimensional law -/

/-- **A quadratic scalar field is unstable.** A field `G` on `State 1`, Lipschitz on a
neighbourhood of `0`, with `G(y) = a y₀² e₀ + o(‖y‖²)` and `a ≠ 0` is unstable at `0`: `W(y) = a y₀`
is positive on one side of `0` and `Ẇ = a² y₀² + o(y₀²) > 0` there (Chetaev). -/
@[tmio T, powerlib_foundation] theorem unstable_of_quadratic_isLittleO {G : State 1 → State 1}
    {U : Set (State 1)} {K : NNReal} (hU : U ∈ 𝓝 0) (hG : LipschitzOnWith K G U) {a : ℝ}
    (ha : a ≠ 0)
    (hexp : (fun y => G y - (a * y 0 ^ 2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =o[𝓝 0]
      fun y => ‖y‖ ^ 2) :
    Unstable G 0 := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hc : 0 < |a| / 2 := by positivity
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (hexp.def hc)
  have hW : ContDiff ℝ 1 (fun y : State 1 => a * y 0) := by fun_prop
  refine unstable_of_chetaev_lipschitzOn (W := fun y : State 1 => a * y 0) (r := r / 2) hU hG
    hW (half_pos hr) (fun ε hε => ?_) (fun y hy hWy => ?_)
  · set t := ε / (2 * (|a| + 1)) with ht
    have ht0 : 0 < t := by positivity
    have hn : ‖EuclideanSpace.single (0 : Fin 1) (1 : ℝ)‖ = 1 := by simp
    have e0 : ((a * t) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 = a * t := by simp
    refine ⟨(a * t) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ), ?_, ?_⟩
    · rw [sub_zero, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos ht0]
      have h1 : |a| * t ≤ (|a| + 1) * t := by nlinarith
      have h2 : (|a| + 1) * t = ε / 2 := by rw [ht]; field_simp
      linarith
    · show 0 < a * ((a * t) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0
      rw [e0]
      have : 0 < a * a := mul_self_pos.mpr ha
      nlinarith
  · have hd : HasFDerivAt (fun y : State 1 => a * y 0) (a • coord (n := 1) 0) y :=
      (hasFDerivAt_coord 0 y).const_mul a
    rw [hd.fderiv]
    simp only [_root_.smul_apply, coord_apply, smul_eq_mul]
    have hy0 : y 0 ≠ 0 := by
      rintro h0
      rw [h0, mul_zero] at hWy
      exact lt_irrefl 0 hWy
    have hyr : dist y 0 < r := by
      rw [dist_eq_norm]; linarith
    have hby := hb hyr
    have e2 : (G y - (a * y 0 ^ 2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 =
        G y 0 - a * y 0 ^ 2 := by simp
    rw [norm_pow, norm_norm, NormalForm.norm_state1 y, sq_abs, NormalForm.norm_state1, e2]
      at hby
    set dd := G y 0 - a * y 0 ^ 2 with hdd
    have h1 : -(|a| * |dd|) ≤ a * dd := by
      have := neg_abs_le (a * dd)
      rw [abs_mul] at this
      exact this
    have h2 : |a| * |dd| ≤ |a| * (|a| / 2 * y 0 ^ 2) :=
      mul_le_mul_of_nonneg_left hby (abs_nonneg a)
    have h3 : |a| * |a| = a * a := abs_mul_abs_self a
    have h4 : 0 < a * a * y 0 ^ 2 := by
      have := mul_self_pos.mpr ha
      positivity
    have e3 : a * G y 0 = a * a * y 0 ^ 2 + a * dd := by rw [hdd]; ring
    rw [e3]
    nlinarith

end powerlib.Dynamics.CenterManifold

/-! ## The chart of the centre line -/

namespace powerlib.NormalForm.BogdanovTakens
open Set Filter Topology Asymptotics Complex Polynomial Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State)
open powerlib.Dynamics.CenterManifold
open powerlib.NormalForm.LyapunovCoefficient powerlib.Dynamics.LyapunovPerron

section Chart

variable {n : ℕ}

/-- The chart `ι y = y₀ q` of the centre line. -/
def snι (q : State n) : State 1 →L[ℝ] State n := (EuclideanSpace.proj (0 : Fin 1)).smulRight q

/-- The coordinate `π x = ⟨p, x⟩` of the centre line. -/
def snπ (p : State n) : State n →L[ℝ] State 1 :=
  (innerSL ℝ p).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

/-- The spectral projection `P = ιπ`, `P x = ⟨p, x⟩ q`. -/
def snP (q p : State n) : State n →L[ℝ] State n := (snι q).comp (snπ p)

@[tmio T, powerlib_foundation] theorem snι_apply (q : State n) (y : State 1) :
    snι q y = y 0 • q := by
  simp [snι]

@[tmio T, powerlib_foundation] theorem snπ_apply (p x : State n) :
    snπ p x = ⟪p, x⟫ • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  simp [snπ]

@[tmio T, powerlib_foundation] private theorem state1_eq (y : State 1) :
    y = y 0 • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  ext i
  fin_cases i
  simp

variable {A : State n →L[ℝ] State n} {q p : State n}

@[tmio T, powerlib_foundation] theorem IsNullPair.snπ_snι (h : IsNullPair A q p) (y : State 1) :
    snπ p (snι q y) = y := by
  rw [snπ_apply, snι_apply, real_inner_smul_right, h.inner_p_q, mul_one, ← state1_eq]

/-- The chart of a normalised null pair is a chart of `range P`. -/
@[tmio T, powerlib_foundation] theorem IsNullPair.isChart (h : IsNullPair A q p) :
    IsChart (snP q p) (snι q) (snπ p) :=
  ⟨h.snπ_snι, fun _ => rfl⟩

@[tmio T, powerlib_foundation] theorem IsNullPair.snP_apply (x : State n) :
    snP q p x = ⟪p, x⟫ • q := by
  simp [snP, snι_apply, snπ_apply]

/-- `P = ιπ` is a projection commuting with `A` (both products vanish). -/
@[tmio T, powerlib_foundation] theorem IsNullPair.isCommutingProjection (h : IsNullPair A q p) :
    IsCommutingProjection A (snP q p) :=
  ⟨fun x => by simp [snP, h.snπ_snι],
    fun x => by rw [IsNullPair.snP_apply, IsNullPair.snP_apply, map_smul, h.map_q,
      h.inner_p_map, smul_zero, zero_smul]⟩

/-- `A P = 0`: the centre line is the kernel of `A`. -/
@[tmio T, powerlib_foundation] theorem IsNullPair.map_comp_snP (h : IsNullPair A q p) :
    A * snP q p = 0 := by
  ext1 x
  show A (snP q p x) = 0
  rw [IsNullPair.snP_apply, map_smul, h.map_q, smul_zero]

@[tmio T, powerlib_foundation] theorem IsNullPair.snP_q (h : IsNullPair A q p) :
    snP q p q = q := by
  rw [IsNullPair.snP_apply, h.inner_p_q, one_smul]

end Chart

/-! ## The centre–stable dichotomy of a simple zero eigenvalue -/

section Dichotomy

variable {n : ℕ} {A : State n →L[ℝ] State n} {q p : State n}

/-- **The stable part is Hurwitz.** If `χ_A = X r` with `r` Hurwitz, the complexified matrix of
`B = A(1 − P) − P` has the eigenvalues `−1` (on `range P`) and the roots of `r` (on
`range (1 − P)`). -/
@[tmio T, powerlib_foundation] theorem IsNullPair.stablePart_hurwitz (hc : IsNullPair A q p)
    {r : ℂ[X]} (hchar : (cmat A).charpoly = X * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0)
    (μ : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (he : cmat (A * (1 - snP q p) - snP q p) *ᵥ v = μ • v) : μ.re < 0 := by
  have hP := hc.isCommutingProjection
  set Pc := cmat (snP q p) with hPc
  set Ac := cmat A with hAc
  have hPP : Pc * Pc = Pc := by
    rw [hPc, ← cmat_comp]; congr 1; ext1 x; exact hP.idem x
  have hAP : Pc * Ac = Ac * Pc := by
    rw [hPc, hAc, ← cmat_comp, ← cmat_comp]; congr 1; ext1 x; exact (hP.comm x).symm
  have hB : cmat (A * (1 - snP q p) - snP q p) = Ac * (1 - Pc) - Pc := by
    rw [cmat_sub, show A * (1 - snP q p) = A.comp (1 - snP q p) from rfl,
      cmat_comp, cmat_sub, show (1 : State n →L[ℝ] State n) = ContinuousLinearMap.id ℝ _ from rfl,
      cmat_id]
  rw [hB] at he
  set w := (1 - Pc) *ᵥ v with hwdef
  have hw : Ac *ᵥ w = μ • w := by
    have h := congrArg ((1 - Pc) *ᵥ ·) he
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
    have hm : (1 - Pc) * (Ac * (1 - Pc) - Pc) = Ac * (1 - Pc) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
        ← Matrix.mul_assoc, hAP, hPP]
      rw [Matrix.mul_assoc Ac Pc Pc, hPP]
      abel
    rw [hm, ← Matrix.mulVec_mulVec] at h
    exact h
  have hu : (μ + 1) • (Pc *ᵥ v) = 0 := by
    have h := congrArg (Pc *ᵥ ·) he
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
    have hm : Pc * (Ac * (1 - Pc) - Pc) = -Pc := by
      simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAP, hPP]
      rw [Matrix.mul_assoc Ac Pc Pc, hPP]
      abel
    rw [hm, Matrix.neg_mulVec] at h
    rw [add_smul, one_smul, ← h, neg_add_cancel]
  have hPw : Pc *ᵥ w = 0 := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
      Matrix.zero_mulVec]
  by_cases hw0 : w = 0
  · have hvP : Pc *ᵥ v = v := by
      have h : v - Pc *ᵥ v = 0 := by
        rw [← hw0, hwdef, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (sub_eq_zero.mp h).symm
    rw [hvP] at hu
    have h1 : μ + 1 = 0 := (smul_eq_zero.mp hu).resolve_right hv
    have h2 : μ = -1 := by linear_combination h1
    rw [h2]; norm_num
  · have hdet : (cmat A).charpoly.eval μ = 0 := by
      rw [Matrix.eval_charpoly]
      refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, ?_⟩
      rw [Matrix.sub_mulVec, ← hAc, hw]
      ext i
      simp [Matrix.scalar_apply]
    rw [hchar, eval_mul] at hdet
    rcases mul_eq_zero.mp hdet with h2 | h2
    · exfalso
      have hμ : μ = 0 := by simpa using h2
      rw [hμ] at hw
      have hr0 : r.eval 0 ≠ 0 := fun h0 => by linarith [hr 0 h0, show (0 : ℂ).re = 0 from rfl]
      have hq0 : toC q ≠ 0 := by
        intro h0
        have hq : q = 0 := by
          ext k
          have := congrFun h0 k
          simpa [toC] using this
        have h1 := hc.inner_p_q
        rw [hq, inner_zero_right] at h1
        exact zero_ne_one h1
      have hAq : Ac *ᵥ toC q = (0 : ℂ) • toC q := by
        rw [hAc, cmat_mulVec_toC, hc.map_q, zero_smul]
        ext k
        simp [toC]
      have hchar' : (cmat A).charpoly = (X - C (0 : ℂ)) * r := by
        rw [hchar, map_zero, sub_zero]
      obtain ⟨c, hcw⟩ := eq_smul_of_charpoly hchar' hr0 hAq hq0 hw
      have hPq : Pc *ᵥ toC q = toC q := by rw [hPc, cmat_mulVec_toC, hc.snP_q]
      apply hw0
      rw [← hPw, hcw, Matrix.mulVec_smul, hPq]
    · exact hr μ h2

/-- **The centre–stable dichotomy of a simple zero eigenvalue.** If `(q, p)` is a normalised null
pair of `A` and `χ_A = X r` with `r` Hurwitz, the projection `P = ιπ` has the dichotomy of the
centre-manifold theorem: `‖e^{tA}P‖ ≤ K e^{ε|t|}` for all `t` and
`‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` for `t ≥ 0`, `0 < ε < β` (on the centre line `e^{tA}P = P`). -/
@[tmio T, powerlib_foundation] theorem IsNullPair.exists_dichotomy (hc : IsNullPair A q p)
    {r : ℂ[X]} (hchar : (cmat A).charpoly = X * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ K ε β : ℝ, 0 < ε ∧ ε < β ∧
      (∀ t, ‖expFlow A t * snP q p‖ ≤ K * Real.exp (ε * |t|)) ∧
      ∀ t, 0 ≤ t → ‖expFlow A t * (1 - snP q p)‖ ≤ K * Real.exp (-(β * t)) := by
  have hP := hc.isCommutingProjection
  set P := snP q p with hPdef
  have hPP : P * P = P := by ext1 x; exact hP.idem x
  have hAP : P * A = A * P := by ext1 x; exact (hP.comm x).symm
  have hAP0 : A * P = 0 := hc.map_comp_snP
  set B := A * (1 - P) - P with hB
  obtain ⟨K₂, a, ha, hK₂⟩ := norm_expFlow_le_of_hurwitz (B := B)
    (hc.stablePart_hurwitz hchar hr)
  have hε : 0 < a / 2 := by positivity
  set K₁ := ‖P‖ + ‖A * P‖ / (a / 2)
  have hcomm : Commute A B := by
    simp only [Commute, SemiconjBy, hB, mul_sub, sub_mul, mul_one, mul_assoc, hAP]
  have hBS : B * (1 - P) = A * (1 - P) := by
    simp only [hB, mul_sub, sub_mul, mul_one, mul_assoc, hPP, sub_self]
    abel
  refine ⟨max K₁ (K₂ * ‖1 - P‖), a / 2, a, hε, by linarith, fun t => ?_, fun t ht => ?_⟩
  · calc ‖expFlow A t * P‖ ≤ K₁ * Real.exp (a / 2 * |t|) :=
          norm_expFlow_mul_le_of_nilpotent (by rw [hAP0, mul_zero]) hε t
      _ ≤ max K₁ (K₂ * ‖1 - P‖) * Real.exp (a / 2 * |t|) := by
        gcongr; exact le_max_left _ _
  · rw [expFlow_mul_eq_of_mul_eq hcomm hBS t]
    calc ‖expFlow B t * (1 - P)‖ ≤ ‖expFlow B t‖ * ‖1 - P‖ := norm_mul_le _ _
      _ ≤ K₂ * Real.exp (-(a * t)) * ‖1 - P‖ := by gcongr; exact hK₂ t ht
      _ ≤ max K₁ (K₂ * ‖1 - P‖) * Real.exp (-(a * t)) := by
        rw [mul_right_comm]; gcongr; exact le_max_right _ _

end Dichotomy

end powerlib.NormalForm.BogdanovTakens

/-! ## The saddle-node law -/

namespace powerlib.Dynamics.CenterManifold
open Set Filter Topology Asymptotics Complex Polynomial Matrix
open scoped RealInnerProductSpace
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff snι snπ snP snι_apply snπ_apply)

/-- **A saddle-node point with a nonzero fold coefficient is unstable.** Let `F` be of class `C²`
with `F(0) = 0`, let `(q, p)` be a normalised null pair of `A = DF(0)` and let
`det(sI − A) = s r(s)` with every root of `r` in the open left half plane. If Kuznetsov's fold
coefficient `a = ½⟨p, D²F(0)(q, q)⟩` (`NormalForm.BogdanovTakens.foldCoeff`) is nonzero, the
origin is unstable: the centre manifold (`exists_centerManifold`, dichotomy
`IsNullPair.exists_dichotomy`) carries `u̇ = a u² + o(u²)` (`chartField_expansion2`), unstable by
`unstable_of_quadratic_isLittleO`, and instability transfers to the full field
(`unstable_of_unstable_chartField`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_foldCoeff_ne_zero_of_charpoly {n : ℕ}
    {F : State n → State n} (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0) {q p : State n}
    (hnp : IsNullPair (fderiv ℝ F 0) q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = X * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0)
    (ha : foldCoeff F 0 q p ≠ 0) : Unstable F 0 := by
  set A := fderiv ℝ F 0 with hAdef
  set f : State n → State n := fun x => F x - A x with hfdef
  have hFf : fullField A f = F := by funext x; simp [fullField, hfdef]
  have hP := hnp.isCommutingProjection
  obtain ⟨K, ε, β, hε, hεβ, hcen, hst⟩ := hnp.exists_dichotomy hchar hr
  have hf1 : ContDiff ℝ 1 f := (hF.of_le (by norm_num)).sub A.contDiff
  have hf0 : f 0 = 0 := by simp [hfdef, hF0]
  have hDf : fderiv ℝ f 0 = 0 := by
    have h := ((hF.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable one_ne_zero
      0).hasFDerivAt.sub A.hasFDerivAt
    rw [← hAdef, sub_self] at h
    exact h.fderiv
  obtain ⟨ρ, hρ, h, L, hgr, hL, htan, hinv⟩ :=
    exists_centerManifold hP hε.le hεβ hcen hst hf1 hf0 hDf
  have hc := hnp.isChart
  set Q : State n →L[ℝ] State n →L[ℝ] State n := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 with hQ
  have hfQ : (fun x => f x - Q x x) =o[𝓝 0] fun x => ‖x‖ ^ 2 :=
    (taylor2_isLittleO hF).congr_left fun x => by
      simp only [hfdef, hQ, hF0, zero_add, _root_.smul_apply, hAdef]
      abel
  have hexp := chartField_expansion2 (A := A) hc hfQ htan
  have hg : (fun y => chartField A f h (snι q) (snπ p) y -
      (foldCoeff F 0 q p * y 0 ^ 2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =o[𝓝 0]
      fun y => ‖y‖ ^ 2 := by
    refine hexp.congr_left fun y => ?_
    have hA0 : A (snι q y) = 0 := by rw [snι_apply, map_smul, hnp.map_q, smul_zero]
    have hQq : Q (snι q y) (snι q y) = (y 0 ^ 2 / 2) • fderiv ℝ (fderiv ℝ F) 0 q q := by
      simp only [hQ, snι_apply, map_smul, _root_.smul_apply, smul_smul]
      congr 1
      ring
    rw [hA0, map_zero, zero_add, hQq, snπ_apply, real_inner_smul_right, foldCoeff]
    congr 2
    ring
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf1
  set r₁ := R₀ / ((1 + L) * (‖snι q‖ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁R : (1 + L) * ‖snι q‖ * r₁ ≤ R₀ := by
    have : (1 + L) * ‖snι q‖ * r₁ ≤ (1 + L) * (‖snι q‖ + 1) * r₁ := by gcongr; linarith
    refine this.trans (le_of_eq ?_)
    rw [hr₁]; field_simp
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := A) (π := snπ p) hgr.map_zero hL
    hLf hr₁R
  have hred : Unstable (chartField A f h (snι q) (snπ p)) 0 :=
    unstable_of_quadratic_isLittleO (Metric.closedBall_mem_nhds 0 hr₁0) hLg ha hg
  rw [← hFf]
  exact unstable_of_unstable_chartField hP hgr hL hc hf1 hρ hinv hred

end powerlib.Dynamics.CenterManifold
