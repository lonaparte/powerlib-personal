import theorem.Dynamics.SaddleNodeReduction
import theorem.Dynamics.ZeroHopfNormalForm

/-! # Instability at a zero–Hopf point: reduction to the three-dimensional centre manifold
(foundation)

At an equilibrium of `ẋ = F(x)` on `ℝⁿ` whose linearization has simple eigenvalues `0, ±iω`
(`ω > 0`) and the rest of its spectrum in the open left half plane, the centre manifold is
three-dimensional; in the chart `ι w = w₀ q₀ + w₁ (a + b) + w₂ (a − b)` (`q₀` a normalised null
vector, `q = a + ib` a critical eigenvector) the field on it is
`ẇ = L w + G(w, w) + o(‖w‖²)`, `L w = (0, −ω w₂, ω w₁)`, `G(u, v) = ½ π D²F(0)(ιu, ιv)`, and the
normal-form coefficients of `G` are Kuznetsov's projection formulas
`a = ½⟨p₀, B(q₀, q₀)⟩` (`NormalForm.BogdanovTakens.foldCoeff`), `b = ½⟨p₀, B(q, q̄)⟩`
(`zhB`), `c = Re⟨p, B(q₀, q)⟩` (`zhC`). **Where `ZeroHopfDecided a b c` (`ab > 0`, or
`a(a − c) > 0`, or `a = 0` and `bc > 0`) the equilibrium is unstable** (Lyapunov).

Scope.
* Generic: `State n = ℝⁿ`, a field `F` of class `C²` with `F(0) = 0`, `A = DF(0)`, a normalised
  null pair `(q₀, p₀)` (`NormalForm.BogdanovTakens.IsNullPair`), a critical pair `(q, p)`
  (`IsCritical`: `A q = iωq`, `Aᵀp = −iωp`, `⟨p, q⟩ = 1`, `ω > 0`) and a complex polynomial `r`
  with `det(sI − A) = s (s² + ω²) r(s)`, every root of `r` in the open left half plane. The
  cross pairings `⟨p₀, q⟩ = 0`, `⟨p, q₀⟩ = 0` follow from the eigen-relations. The chart is
  `ι`, `π x = (⟨p₀, x⟩, Re⟨p, x⟩ − Im⟨p, x⟩, Re⟨p, x⟩ + Im⟨p, x⟩)`, the spectral projection
  `P = ιπ`, the sum of the projections of the centre line and of the critical plane.
* Lyapunov instability only, in the regimes `ZeroHopfDecided`
  (`theorem/Dynamics/ZeroHopfNormalForm.lean`); the other regimes (with `a > 0`: `b ≤ 0` and
  `c ≥ a`; and `a = 0`, `bc ≤ 0`) are not decided at second order and are not stated. Nothing
  here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.5 (the
zero–Hopf normal form) and §8.7 (the projection formulas `G₂₀₀ = ⟨p₀, B(q₀, q₀)⟩`,
`G₀₁₁ = ⟨p₀, B(q₁, q̄₁)⟩`, `G₁₁₀ = ⟨p₁, B(q₀, q₁)⟩`), §5.1 (Theorem 5.2, the reduction
principle); Carr, *Applications of Centre Manifold Theory* (1981), §2.4. The centre manifold is
`Dynamics.CenterManifold.exists_centerManifold` (`theorem/Dynamics/CenterManifold.lean`), the
reduced field at second order `Dynamics.CenterManifold.chartField_expansion2`
(`theorem/Dynamics/CenterReductionBT.lean`), the transfer
`Dynamics.CenterManifold.unstable_of_unstable_chartField` (`theorem/Dynamics/CenterReduction.lean`),
the flow bounds `norm_expFlow_mul_le_of_nilpotent`, `norm_expFlow_mul_le_of_rotation`,
`norm_expFlow_le_of_hurwitz` and the simplicity law `eq_smul_of_charpoly`
(`theorem/Dynamics/HopfDichotomy.lean`).

Results.
* The chart: `zhι`, `zhπ`, `zhP`, `zhι_apply`, `zhπ_apply`; cross pairings
  `inner_null_reV`, `inner_null_imV`, `inner_reV_null`, `inner_imV_null`; `zhπ_zhι`
  (`πι = 1`), `apply_zhι` (`Aι = ιL`), `zhπ_apply_map` (`πA = Lπ`), `zhπ_comp` (the reduced
  linear part is `zhL ω`), `isChart_zh`, `isCommutingProjection_zh`, `zhP_eq_add`
  (`P = P₀ + P_c`).
* The dichotomy: `zhP_q₀`, `cmat_zhP_mulVec_q`, `stablePart_hurwitz_zh`,
  **`exists_dichotomy_zh`** (`‖e^{tA}P‖ ≤ K e^{ε|t|}`, `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}`,
  `0 < ε < β`).
* The coefficients: `zhB`, `zhC` (real forms), `zhB_eq_pairing`, `zhC_eq_pairing` (Kuznetsov's
  complex forms `½ Re⟨p₀, B(q, q̄)⟩`, `Re⟨p, B(q₀, q)⟩` with `NormalForm.LyapunovCoefficient`'s
  `bilinC`, `pairing`); `zhQuad` (`G(u, v) = ½πB(ιu, ιv)`), `zhQuad_apply`,
  `zhCoeffA_zhQuad`, `zhCoeffB_zhQuad`, `zhCoeffC_zhQuad`.
* **`unstable_of_zeroHopf_of_charpoly`**: `F` of class `C²`, `F(0) = 0`, a normalised null
  pair and a critical pair of `DF(0)`, `det(sI − DF(0)) = s(s² + ω²) r(s)` with `r` Hurwitz and
  `ZeroHopfDecided (foldCoeff F 0 q₀ p₀) (zhB F p₀ q) (zhC F q₀ q p)` ⇒ `Unstable F 0`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold
open Set Filter Topology Asymptotics Complex Polynomial Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient powerlib.Dynamics.LyapunovPerron
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff snP)

/-! ## The chart of the centre space -/

section Chart

variable {n : ℕ}

/-- The chart `ι w = w₀ q₀ + w₁ (a + b) + w₂ (a − b)` (`q = a + ib`) of the centre space. -/
def zhι (q₀ : State n) (q : Fin n → ℂ) : State 3 →L[ℝ] State n :=
  (EuclideanSpace.proj (0 : Fin 3)).smulRight q₀ +
    (EuclideanSpace.proj (1 : Fin 3)).smulRight (reV q + imV q) +
    (EuclideanSpace.proj (2 : Fin 3)).smulRight (reV q - imV q)

/-- The coordinates `π x = (⟨p₀, x⟩, Re⟨p, x⟩ − Im⟨p, x⟩, Re⟨p, x⟩ + Im⟨p, x⟩)` of the centre
space (`⟨p, x⟩ = Σ p̄ₖ xₖ`, so `Re⟨p, x⟩ = ⟨Re p, x⟩`, `Im⟨p, x⟩ = −⟨Im p, x⟩`). -/
def zhπ (p₀ : State n) (p : Fin n → ℂ) : State n →L[ℝ] State 3 :=
  (innerSL ℝ p₀).smulRight (mk3 1 0 0) + (innerSL ℝ (reV p + imV p)).smulRight (mk3 0 1 0) +
    (innerSL ℝ (reV p - imV p)).smulRight (mk3 0 0 1)

/-- The spectral projection `P = ιπ` onto the centre space. -/
def zhP (q₀ p₀ : State n) (q p : Fin n → ℂ) : State n →L[ℝ] State n :=
  (zhι q₀ q).comp (zhπ p₀ p)

@[tmio T, powerlib_foundation] theorem zhι_apply (q₀ : State n) (q : Fin n → ℂ) (w : State 3) :
    zhι q₀ q w = w 0 • q₀ + w 1 • (reV q + imV q) + w 2 • (reV q - imV q) := by
  simp [zhι]

@[tmio T, powerlib_foundation] theorem zhπ_apply (p₀ : State n) (p : Fin n → ℂ) (x : State n) :
    zhπ p₀ p x = mk3 ⟪p₀, x⟫ (⟪reV p, x⟫ + ⟪imV p, x⟫) (⟪reV p, x⟫ - ⟪imV p, x⟫) := by
  refine state3_ext ?_ ?_ ?_ <;> simp [zhπ]

@[tmio T, powerlib_foundation] theorem zhπ_apply0 (p₀ : State n) (p : Fin n → ℂ) (x : State n) :
    zhπ p₀ p x 0 = ⟪p₀, x⟫ := by
  rw [zhπ_apply, mk3_zero]

@[tmio T, powerlib_foundation] theorem zhπ_apply1 (p₀ : State n) (p : Fin n → ℂ) (x : State n) :
    zhπ p₀ p x 1 = ⟪reV p, x⟫ + ⟪imV p, x⟫ := by
  rw [zhπ_apply, mk3_one]

@[tmio T, powerlib_foundation] theorem zhπ_apply2 (p₀ : State n) (p : Fin n → ℂ) (x : State n) :
    zhπ p₀ p x 2 = ⟪reV p, x⟫ - ⟪imV p, x⟫ := by
  rw [zhπ_apply, mk3_two]

variable {A : State n →L[ℝ] State n} {q₀ p₀ : State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation] theorem inner_null_reV (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : ⟪p₀, reV q⟫ = 0 := by
  have h := hn.inner_p_map (imV q)
  rw [hc.apply_im, real_inner_smul_right] at h
  exact (mul_eq_zero.mp h).resolve_left hc.freq_pos.ne'

@[tmio T, powerlib_foundation] theorem inner_null_imV (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : ⟪p₀, imV q⟫ = 0 := by
  have h := hn.inner_p_map (reV q)
  rw [hc.apply_re, real_inner_smul_right] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hc.freq_pos.ne')

@[tmio T, powerlib_foundation] theorem inner_reV_null (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : ⟪reV p, q₀⟫ = 0 := by
  have h := (hc.inner_apply q₀).2
  rw [hn.map_q, inner_zero_right] at h
  have : ω * ⟪reV p, q₀⟫ = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hc.freq_pos.ne'

@[tmio T, powerlib_foundation] theorem inner_imV_null (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : ⟪imV p, q₀⟫ = 0 := by
  have h := (hc.inner_apply q₀).1
  rw [hn.map_q, inner_zero_right] at h
  exact ((mul_eq_zero.mp h.symm).resolve_left hc.freq_pos.ne')

@[tmio T, powerlib_foundation] theorem zhπ_zhι (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) (w : State 3) : zhπ p₀ p (zhι q₀ q w) = w := by
  obtain ⟨h1, h2, h3, h4⟩ := hc.inner_values
  have e1 := inner_null_reV hn hc
  have e2 := inner_null_imV hn hc
  have e3 := inner_reV_null hn hc
  have e4 := inner_imV_null hn hc
  have e5 := hn.inner_p_q
  rw [zhπ_apply, zhι_apply]
  refine state3_ext ?_ ?_ ?_ <;>
    simp only [mk3_zero, mk3_one, mk3_two, inner_add_right, inner_sub_right,
      real_inner_smul_right, e1, e2, e3, e4, e5, h1, h2, h3, h4] <;> ring

@[tmio T, powerlib_foundation] theorem apply_zhι (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) (w : State 3) : A (zhι q₀ q w) = zhι q₀ q (zhL ω w) := by
  rw [zhι_apply, zhι_apply, zhL_apply, map_add, map_add, map_smul, map_smul, map_smul,
    hn.map_q, map_add, map_sub, hc.apply_re, hc.apply_im]
  simp only [mk3_zero, mk3_one, mk3_two, smul_zero, zero_smul, zero_add]
  module

@[tmio T, powerlib_foundation] theorem zhπ_apply_map (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) (x : State n) : zhπ p₀ p (A x) = zhL ω (zhπ p₀ p x) := by
  obtain ⟨h1, h2⟩ := hc.inner_apply x
  rw [zhπ_apply, zhπ_apply, zhL_apply, hn.inner_p_map, h1, h2]
  simp only [mk3_one, mk3_two]
  refine state3_ext ?_ ?_ ?_ <;> simp only [mk3_zero, mk3_one, mk3_two] <;> ring

/-- The reduced linear part is `zhL ω`. -/
@[tmio T, powerlib_foundation] theorem zhπ_comp (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) (w : State 3) : zhπ p₀ p (A (zhι q₀ q w)) = zhL ω w := by
  rw [apply_zhι hn hc, zhπ_zhι hn hc]

@[tmio T, powerlib_foundation] theorem isChart_zh (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : IsChart (zhP q₀ p₀ q p) (zhι q₀ q) (zhπ p₀ p) :=
  ⟨zhπ_zhι hn hc, fun _ => rfl⟩

@[tmio T, powerlib_foundation] theorem isCommutingProjection_zh (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : IsCommutingProjection A (zhP q₀ p₀ q p) :=
  ⟨fun x => by simp only [zhP, ContinuousLinearMap.comp_apply, zhπ_zhι hn hc],
    fun x => by simp only [zhP, ContinuousLinearMap.comp_apply, apply_zhι hn hc,
      zhπ_apply_map hn hc]⟩

/-- `P = P₀ + P_c`: the projection of the centre space is the sum of the projections of the
centre line and of the critical plane. -/
@[tmio T, powerlib_foundation] theorem zhP_eq_add (q₀ p₀ : State n) (q p : Fin n → ℂ) :
    zhP q₀ p₀ q p = snP q₀ p₀ + critP q p := by
  ext1 x
  rw [_root_.add_apply, NormalForm.BogdanovTakens.IsNullPair.snP_apply, critP,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, zhP,
    ContinuousLinearMap.comp_apply, zhι_apply, zhπ_apply, mk3_zero, mk3_one, mk3_two]
  abel

end Chart

/-! ## The centre–stable dichotomy of a zero–Hopf point -/

section Dichotomy

variable {n : ℕ} {A : State n →L[ℝ] State n} {q₀ p₀ : State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation] theorem zhP_q₀ (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : zhP q₀ p₀ q p q₀ = q₀ := by
  rw [zhP, ContinuousLinearMap.comp_apply, zhπ_apply, hn.inner_p_q, inner_reV_null hn hc,
    inner_imV_null hn hc]
  simp [zhι_apply]

/-- The projection of the centre space fixes the critical eigenvector. -/
@[tmio T, powerlib_foundation] theorem cmat_zhP_mulVec_q (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) : cmat (zhP q₀ p₀ q p) *ᵥ q = q := by
  have e := q_eq_comb q
  have h1 : zhP q₀ p₀ q p (reV q + imV q) = reV q + imV q := by
    have h : zhι q₀ q (mk3 0 1 0) = reV q + imV q := by simp [zhι_apply]
    conv_lhs => rw [← h]
    rw [zhP, ContinuousLinearMap.comp_apply, zhπ_zhι hn hc, h]
  have h2 : zhP q₀ p₀ q p (reV q - imV q) = reV q - imV q := by
    have h : zhι q₀ q (mk3 0 0 1) = reV q - imV q := by simp [zhι_apply]
    conv_lhs => rw [← h]
    rw [zhP, ContinuousLinearMap.comp_apply, zhπ_zhι hn hc, h]
  calc cmat (zhP q₀ p₀ q p) *ᵥ q = cmat (zhP q₀ p₀ q p) *ᵥ (((1 + I) / 2) •
        toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q)) := congrArg _ e
    _ = q := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, cmat_mulVec_toC,
        cmat_mulVec_toC, h1, h2]
      exact e.symm

@[tmio T, powerlib_foundation] private theorem sq_add_sq_eq' (ω : ℝ) :
    (X ^ 2 + C ((ω : ℂ) ^ 2) : ℂ[X]) = (X - C ((ω : ℂ) * I)) * (X + C ((ω : ℂ) * I)) := by
  have h : ((ω : ℂ) * I) ^ 2 = -((ω : ℂ) ^ 2) := by rw [mul_pow, I_sq]; ring
  rw [show (X - C ((ω : ℂ) * I)) * (X + C ((ω : ℂ) * I)) = X ^ 2 - C ((ω : ℂ) * I) ^ 2 by ring,
    ← map_pow, h, map_neg, sub_neg_eq_add]

/-- **The stable part is Hurwitz.** If `χ_A = X (X² + ω²) r` with `r` Hurwitz, the complexified
matrix of `B = A(1 − P) − P` (`P` the projection of the centre space) has the eigenvalue `−1`
(on `range P`) and the roots of `r` (on `range (1 − P)`): all in the open left half plane. -/
@[tmio T, powerlib_foundation] theorem stablePart_hurwitz_zh (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) {r : ℂ[X]}
    (hchar : (cmat A).charpoly = X * (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (μ : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (he : cmat (A * (1 - zhP q₀ p₀ q p) - zhP q₀ p₀ q p) *ᵥ v = μ • v) : μ.re < 0 := by
  have hP := isCommutingProjection_zh hn hc
  set Pc := cmat (zhP q₀ p₀ q p) with hPc
  set Ac := cmat A with hAc
  have hPP : Pc * Pc = Pc := by
    rw [hPc, ← cmat_comp]; congr 1; ext1 x; exact hP.idem x
  have hAP : Pc * Ac = Ac * Pc := by
    rw [hPc, hAc, ← cmat_comp, ← cmat_comp]; congr 1; ext1 x; exact (hP.comm x).symm
  have hB : cmat (A * (1 - zhP q₀ p₀ q p) - zhP q₀ p₀ q p) = Ac * (1 - Pc) - Pc := by
    rw [cmat_sub, show A * (1 - zhP q₀ p₀ q p) = A.comp (1 - zhP q₀ p₀ q p) from rfl,
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
  have hdet : (cmat A).charpoly.eval μ = 0 := by
    rw [Matrix.eval_charpoly]
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, ?_⟩
    rw [Matrix.sub_mulVec, ← hAc, hw]
    ext i
    simp [Matrix.scalar_apply]
  have hω : (ω : ℂ) ≠ 0 := by exact_mod_cast hc.freq_pos.ne'
  have hr0 : ∀ s : ℂ, s.re = 0 → r.eval s ≠ 0 := fun s hs h => by linarith [hr s h]
  rw [hchar, eval_mul] at hdet
  rcases mul_eq_zero.mp hdet with h2 | h2
  · exfalso
    rw [eval_mul, eval_X, eval_add, eval_pow, eval_X, eval_C] at h2
    -- an eigenvector of an imaginary-axis eigenvalue in `ker P` is zero
    have hcont : ∀ (u z : Fin n → ℂ), Pc *ᵥ z = z → Pc *ᵥ u = 0 → (∃ c : ℂ, u = c • z) →
        u = 0 := by
      rintro u z hz hPu ⟨c, rfl⟩
      rw [Matrix.mulVec_smul, hz] at hPu
      exact hPu
    rcases mul_eq_zero.mp h2 with h | h
    · -- `μ = 0`: a multiple of `q₀`
      rw [h] at hw
      have hq0 : toC q₀ ≠ 0 := by
        intro h0
        have hq : q₀ = 0 := by
          ext k
          have := congrFun h0 k
          simpa [toC] using this
        have h1 := hn.inner_p_q
        rw [hq, inner_zero_right] at h1
        exact zero_ne_one h1
      have hAq : Ac *ᵥ toC q₀ = (0 : ℂ) • toC q₀ := by
        rw [hAc, cmat_mulVec_toC, hn.map_q, zero_smul]
        ext k
        simp [toC]
      have hchar' : (cmat A).charpoly = (X - C (0 : ℂ)) * ((X ^ 2 + C ((ω : ℂ) ^ 2)) * r) := by
        rw [hchar, map_zero, sub_zero, mul_assoc]
      have hev : ((X ^ 2 + C ((ω : ℂ) ^ 2)) * r).eval 0 ≠ 0 := by
        rw [eval_mul, eval_add, eval_pow, eval_X, eval_C]
        refine mul_ne_zero ?_ (hr0 0 rfl)
        simpa using pow_ne_zero 2 hω
      have hPq : Pc *ᵥ toC q₀ = toC q₀ := by rw [hPc, cmat_mulVec_toC, zhP_q₀ hn hc]
      exact hw0 (hcont w _ hPq hPw (eq_smul_of_charpoly hchar' hev hAq hq0 hw))
    · -- `μ = ±iω`: a multiple of `q` or of `q̄`
      have hq0 : q ≠ 0 := hc.q_ne_zero
      have hchar' : (cmat A).charpoly =
          (X - C ((ω : ℂ) * I)) * ((X + C ((ω : ℂ) * I)) * X * r) := by
        rw [hchar, sq_add_sq_eq']; ring
      have hev : ((X + C ((ω : ℂ) * I)) * X * r).eval ((ω : ℂ) * I) ≠ 0 := by
        rw [eval_mul, eval_mul, eval_add, eval_X, eval_C]
        refine mul_ne_zero (mul_ne_zero ?_ (mul_ne_zero hω I_ne_zero)) (hr0 _ (by simp))
        rw [← two_mul]
        exact mul_ne_zero two_ne_zero (mul_ne_zero hω I_ne_zero)
      have hPq : Pc *ᵥ q = q := cmat_zhP_mulVec_q hn hc
      have hsplit : (μ - (ω : ℂ) * I) * (μ + (ω : ℂ) * I) = 0 := by
        have hI : (I : ℂ) ^ 2 = -1 := I_sq
        linear_combination h - (ω : ℂ) ^ 2 * hI
      rcases mul_eq_zero.mp hsplit with h' | h'
      · have hμ : μ = (ω : ℂ) * I := by linear_combination h'
        rw [hμ] at hw
        exact hw0 (hcont w q hPq hPw (eq_smul_of_charpoly hchar' hev hc.right hq0 hw))
      · have hμ : μ = -((ω : ℂ) * I) := by linear_combination h'
        have hsw : Ac *ᵥ star w = ((ω : ℂ) * I) • star w := by
          rw [hAc, ← cmat_mulVec_star, ← hAc, hw, hμ, star_smul]
          congr 1
          simp
        have hPsw : Pc *ᵥ star w = 0 := by rw [hPc, ← cmat_mulVec_star, ← hPc, hPw, star_zero]
        have h0 := hcont (star w) q hPq hPsw (eq_smul_of_charpoly hchar' hev hc.right hq0 hsw)
        exact hw0 (by simpa using congrArg star h0)
  · exact hr μ h2

/-- **The centre–stable dichotomy of a zero–Hopf point.** If `(q₀, p₀)` is a normalised null
pair and `(q, p)` a critical pair of `A`, and `χ_A = X (X² + ω²) r` with `r` Hurwitz, the
projection `P = ιπ` of the centre space has the dichotomy of the centre-manifold theorem:
`‖e^{tA}P‖ ≤ K e^{ε|t|}` for all `t` and `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` for `t ≥ 0`,
`0 < ε < β` (on the centre space `e^{tA}P = P₀ + e^{tA}P_c`, a rotation on the critical plane). -/
@[tmio T, powerlib_foundation] theorem exists_dichotomy_zh (hn : IsNullPair A q₀ p₀)
    (hc : IsCritical A ω q p) {r : ℂ[X]}
    (hchar : (cmat A).charpoly = X * (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ K ε β : ℝ, 0 < ε ∧ ε < β ∧
      (∀ t, ‖expFlow A t * zhP q₀ p₀ q p‖ ≤ K * Real.exp (ε * |t|)) ∧
      ∀ t, 0 ≤ t → ‖expFlow A t * (1 - zhP q₀ p₀ q p)‖ ≤ K * Real.exp (-(β * t)) := by
  have hP := isCommutingProjection_zh hn hc
  set P := zhP q₀ p₀ q p with hPdef
  have hPP : P * P = P := by ext1 x; exact hP.idem x
  have hAP : P * A = A * P := by ext1 x; exact (hP.comm x).symm
  set B := A * (1 - P) - P with hB
  obtain ⟨K₂, a, ha, hK₂⟩ := norm_expFlow_le_of_hurwitz (B := B)
    (stablePart_hurwitz_zh hn hc hchar hr)
  have hε : 0 < a / 2 := by positivity
  set P₀ := snP q₀ p₀
  set Pc := critP q p
  set K₁ := ‖P₀‖ + ‖A * P₀‖ / (a / 2)
  set K₃ := ‖Pc‖ + ‖(A + (0 : ℝ) • 1) * Pc‖ / |ω|
  have hK₃ : 0 ≤ K₃ := by positivity
  have hcomm : Commute A B := by
    simp only [Commute, SemiconjBy, hB, mul_sub, sub_mul, mul_one, mul_assoc, hAP]
  have hBS : B * (1 - P) = A * (1 - P) := by
    simp only [hB, mul_sub, sub_mul, mul_one, mul_assoc, hPP, sub_self]
    abel
  refine ⟨max (K₁ + K₃) (K₂ * ‖1 - P‖), a / 2, a, hε, by linarith, fun t => ?_, fun t ht => ?_⟩
  · have hsplit : expFlow A t * P = expFlow A t * P₀ + expFlow A t * Pc := by
      rw [hPdef, zhP_eq_add, mul_add]
    have h0 := NormalForm.BogdanovTakens.norm_expFlow_mul_le_of_nilpotent (A := A) (P := P₀)
      (by rw [NormalForm.BogdanovTakens.IsNullPair.map_comp_snP hn, mul_zero]) hε t
    have h1 := norm_expFlow_mul_le_of_rotation (A := A) (P := Pc) (c := 0) hc.freq_pos.ne'
      hc.rotation_critP t
    rw [zero_mul, neg_zero, Real.exp_zero, mul_one] at h1
    have he1 : 1 ≤ Real.exp (a / 2 * |t|) := Real.one_le_exp (by positivity)
    rw [hsplit]
    calc ‖expFlow A t * P₀ + expFlow A t * Pc‖
        ≤ ‖expFlow A t * P₀‖ + ‖expFlow A t * Pc‖ := norm_add_le _ _
      _ ≤ K₁ * Real.exp (a / 2 * |t|) + K₃ * Real.exp (a / 2 * |t|) := by
        gcongr
        exact h1.trans (le_mul_of_one_le_right hK₃ he1)
      _ = (K₁ + K₃) * Real.exp (a / 2 * |t|) := by ring
      _ ≤ max (K₁ + K₃) (K₂ * ‖1 - P‖) * Real.exp (a / 2 * |t|) := by
        gcongr; exact le_max_left _ _
  · rw [expFlow_mul_eq_of_mul_eq hcomm hBS t]
    calc ‖expFlow B t * (1 - P)‖ ≤ ‖expFlow B t‖ * ‖1 - P‖ := norm_mul_le _ _
      _ ≤ K₂ * Real.exp (-(a * t)) * ‖1 - P‖ := by gcongr; exact hK₂ t ht
      _ ≤ max (K₁ + K₃) (K₂ * ‖1 - P‖) * Real.exp (-(a * t)) := by
        rw [mul_right_comm]; gcongr; exact le_max_right _ _

end Dichotomy

/-! ## The coefficients and the reduction -/

section Reduction

variable {n : ℕ}

/-- Kuznetsov's coefficient `b = ½⟨p₀, B(q, q̄)⟩`, `B = D²F(0)`, in real form
(`B(q, q̄) = B(a, a) + B(b, b)` for `q = a + ib` and a symmetric `B`). -/
def zhB (F : State n → State n) (p₀ : State n) (q : Fin n → ℂ) : ℝ :=
  (⟪p₀, fderiv ℝ (fderiv ℝ F) 0 (reV q) (reV q)⟫ +
    ⟪p₀, fderiv ℝ (fderiv ℝ F) 0 (imV q) (imV q)⟫) / 2

/-- Kuznetsov's coefficient `c = Re⟨p, B(q₀, q)⟩`, `B = D²F(0)`, in real form. -/
def zhC (F : State n → State n) (q₀ : State n) (q p : Fin n → ℂ) : ℝ :=
  ⟪reV p, fderiv ℝ (fderiv ℝ F) 0 q₀ (reV q)⟫ + ⟪imV p, fderiv ℝ (fderiv ℝ F) 0 q₀ (imV q)⟫

@[tmio T, powerlib_foundation] private theorem reV_toC (a : State n) : reV (toC a) = a := by
  ext k; simp [toC]

@[tmio T, powerlib_foundation] private theorem imV_toC (a : State n) : imV (toC a) = 0 := by
  ext k; simp [toC]

@[tmio T, powerlib_foundation] private theorem bilinC_toC_fderiv (F : State n → State n)
    (a b : State n) :
    bilinC F 0 (toC a) (toC b) = toC (fderiv ℝ (fderiv ℝ F) 0 a b) := by
  rw [bilinC_toC, iteratedFDeriv_two_apply]
  rfl

/-- `b` in Kuznetsov's complex form: `zhB F p₀ q = ½ Re⟨p₀, B(q, q̄)⟩` (`bilinC`, `pairing`). -/
@[tmio T, powerlib_foundation] theorem zhB_eq_pairing (F : State n → State n) (p₀ : State n)
    (q : Fin n → ℂ) : zhB F p₀ q = (pairing (toC p₀) (bilinC F 0 q (star q))).re / 2 := by
  have e : bilinC F 0 q (star q) = bilinC F 0 (toC (reV q) + I • toC (imV q))
      (toC (reV q) - I • toC (imV q)) := by rw [toC_reV_add_imV, toC_reV_sub_imV]
  rw [e]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    bilinC_toC_fderiv, pairing_toC, reV_toC, imV_toC, inner_zero_left, smul_eq_mul]
  simp [zhB, Complex.mul_re]

/-- `c` in Kuznetsov's complex form: `zhC F q₀ q p = Re⟨p, B(q₀, q)⟩`. -/
@[tmio T, powerlib_foundation] theorem zhC_eq_pairing (F : State n → State n) (q₀ : State n)
    (q p : Fin n → ℂ) : zhC F q₀ q p = (pairing p (bilinC F 0 (toC q₀) q)).re := by
  have e : bilinC F 0 (toC q₀) q = bilinC F 0 (toC q₀) (toC (reV q) + I • toC (imV q)) := by
    rw [toC_reV_add_imV]
  rw [e]
  simp only [map_add, map_smul, bilinC_toC_fderiv, pairing_toC, smul_eq_mul]
  simp [zhC, Complex.mul_re]

/-- The quadratic part of the reduced field in the chart, `G(u, v) = ½ π D²F(0)(ιu, ιv)`. -/
def zhQuad (F : State n → State n) (q₀ : State n) (q : Fin n → ℂ) (p₀ : State n)
    (p : Fin n → ℂ) : State 3 →L[ℝ] State 3 →L[ℝ] State 3 :=
  (1 / 2 : ℝ) • ((ContinuousLinearMap.compL ℝ (State 3) (State n) (State 3) (zhπ p₀ p)).comp
    ((fderiv ℝ (fderiv ℝ F) 0).bilinearComp (zhι q₀ q) (zhι q₀ q)))

@[tmio T, powerlib_foundation] theorem zhQuad_apply (F : State n → State n) (q₀ p₀ : State n)
    (q p : Fin n → ℂ) (u v : State 3) :
    zhQuad F q₀ q p₀ p u v =
      (1 / 2 : ℝ) • zhπ p₀ p (fderiv ℝ (fderiv ℝ F) 0 (zhι q₀ q u) (zhι q₀ q v)) := by
  simp [zhQuad]

/-- The coefficient `a` of the chart quadratic part is Kuznetsov's fold coefficient. -/
@[tmio T, powerlib_foundation] theorem zhCoeffA_zhQuad (F : State n → State n)
    (q₀ p₀ : State n) (q p : Fin n → ℂ) :
    zhCoeffA (zhQuad F q₀ q p₀ p) = foldCoeff F 0 q₀ p₀ := by
  rw [zhCoeffA, zhQuad_apply, foldCoeff]
  simp [zhι_apply, zhπ_apply]
  ring

/-- For a symmetric second derivative the coefficient `b` of the chart quadratic part is
`zhB F p₀ q`. -/
@[tmio T, powerlib_foundation] theorem zhCoeffB_zhQuad {F : State n → State n}
    (hsym : ∀ u v, fderiv ℝ (fderiv ℝ F) 0 u v = fderiv ℝ (fderiv ℝ F) 0 v u)
    (q₀ p₀ : State n) (q p : Fin n → ℂ) :
    zhCoeffB (zhQuad F q₀ q p₀ p) = zhB F p₀ q := by
  rw [zhCoeffB, zhQuad_apply, zhQuad_apply, zhB]
  simp only [zhι_apply, mk3_zero, mk3_one, mk3_two, zero_smul, one_smul, zero_add, add_zero,
    PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, zhπ_apply0, smul_eq_mul, map_add, map_sub,
    _root_.add_apply, _root_.sub_apply]
  rw [hsym (imV q) (reV q)]
  ring

/-- For a symmetric second derivative the coefficient `c` of the chart quadratic part is
`zhC F q₀ q p`. -/
@[tmio T, powerlib_foundation] theorem zhCoeffC_zhQuad {F : State n → State n}
    (hsym : ∀ u v, fderiv ℝ (fderiv ℝ F) 0 u v = fderiv ℝ (fderiv ℝ F) 0 v u)
    (q₀ p₀ : State n) (q p : Fin n → ℂ) :
    zhCoeffC (zhQuad F q₀ q p₀ p) = zhC F q₀ q p := by
  rw [zhCoeffC, zhQuad_apply, zhQuad_apply, zhQuad_apply, zhQuad_apply, zhC]
  simp only [zhι_apply, mk3_zero, mk3_one, mk3_two, zero_smul, one_smul, zero_add, add_zero,
    PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, zhπ_apply1, zhπ_apply2, smul_eq_mul,
    map_add, map_sub, _root_.add_apply, _root_.sub_apply]
  rw [hsym (reV q) q₀, hsym (imV q) q₀]
  ring

/-- **A zero–Hopf point in a decided regime is unstable.** Let `F` be of class `C²` with
`F(0) = 0`, `(q₀, p₀)` a normalised null pair and `(q, p)` a critical pair of `A = DF(0)`
(eigenvalues `0`, `±iω`), and `det(sI − A) = s (s² + ω²) r(s)` with every root of `r` in the open
left half plane. If `ZeroHopfDecided a b c` for Kuznetsov's coefficients
`a = foldCoeff F 0 q₀ p₀`, `b = zhB F p₀ q`, `c = zhC F q₀ q p` (`ab > 0`, or `a(a − c) > 0`, or
`a = 0` and `bc > 0`), the origin is unstable: the three-dimensional centre manifold
(`exists_centerManifold`, dichotomy `exists_dichotomy_zh`) carries
`ẇ = zhL ω w + G(w, w) + o(‖w‖²)` (`chartField_expansion2`), unstable by
`unstable_of_zeroHopfDecided`, and instability transfers to the full field
(`unstable_of_unstable_chartField`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_zeroHopf_of_charpoly
    {F : State n → State n} (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0) {q₀ p₀ : State n}
    (hnp : IsNullPair (fderiv ℝ F 0) q₀ p₀) {ω : ℝ} {q p : Fin n → ℂ}
    (hcp : IsCritical (fderiv ℝ F 0) ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = X * (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0)
    (hdec : ZeroHopfDecided (foldCoeff F 0 q₀ p₀) (zhB F p₀ q) (zhC F q₀ q p)) :
    Unstable F 0 := by
  set A := fderiv ℝ F 0 with hAdef
  set f : State n → State n := fun x => F x - A x with hfdef
  have hFf : fullField A f = F := by funext x; simp [fullField, hfdef]
  have hP := isCommutingProjection_zh hnp hcp
  obtain ⟨K, ε, β, hε, hεβ, hcen, hst⟩ := exists_dichotomy_zh hnp hcp hchar hr
  have hf1 : ContDiff ℝ 1 f := (hF.of_le (by norm_num)).sub A.contDiff
  have hf0 : f 0 = 0 := by simp [hfdef, hF0]
  have hDf : fderiv ℝ f 0 = 0 := by
    have h := ((hF.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable one_ne_zero
      0).hasFDerivAt.sub A.hasFDerivAt
    rw [← hAdef, sub_self] at h
    exact h.fderiv
  obtain ⟨ρ, hρ, h, L, hgr, hL, htan, hinv⟩ :=
    exists_centerManifold hP hε.le hεβ hcen hst hf1 hf0 hDf
  have hc := isChart_zh hnp hcp
  have hsym : ∀ u v, fderiv ℝ (fderiv ℝ F) 0 u v = fderiv ℝ (fderiv ℝ F) 0 v u :=
    ContDiffAt.isSymmSndFDerivAt (hF.contDiffAt (x := 0)) (by simp)
  set Q : State n →L[ℝ] State n →L[ℝ] State n := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 with hQ
  have hfQ : (fun x => f x - Q x x) =o[𝓝 0] fun x => ‖x‖ ^ 2 :=
    (taylor2_isLittleO hF).congr_left fun x => by
      simp only [hfdef, hQ, hF0, zero_add, _root_.smul_apply, hAdef]
      abel
  have hexp := chartField_expansion2 (A := A) hc hfQ htan
  have hg : (fun y => chartField A f h (zhι q₀ q) (zhπ p₀ p) y -
      (zhL ω y + zhQuad F q₀ q p₀ p y y)) =o[𝓝 0] fun y => ‖y‖ ^ 2 := by
    refine hexp.congr_left fun y => ?_
    rw [zhπ_comp hnp hcp, zhQuad_apply, hQ, _root_.smul_apply, _root_.smul_apply, map_smul]
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf1
  set r₁ := R₀ / ((1 + L) * (‖zhι q₀ q‖ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁R : (1 + L) * ‖zhι q₀ q‖ * r₁ ≤ R₀ := by
    have : (1 + L) * ‖zhι q₀ q‖ * r₁ ≤ (1 + L) * (‖zhι q₀ q‖ + 1) * r₁ := by
      gcongr; linarith
    refine this.trans (le_of_eq ?_)
    rw [hr₁]; field_simp
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := A) (π := zhπ p₀ p) hgr.map_zero hL
    hLf hr₁R
  rw [← zhCoeffA_zhQuad F q₀ p₀ q p, ← zhCoeffB_zhQuad hsym q₀ p₀ q p,
    ← zhCoeffC_zhQuad hsym q₀ p₀ q p] at hdec
  have hred : Unstable (chartField A f h (zhι q₀ q) (zhπ p₀ p)) 0 :=
    unstable_of_zeroHopfDecided hcp.freq_pos.ne' (Metric.closedBall_mem_nhds 0 hr₁0) hLg hg hdec
  rw [← hFf]
  exact unstable_of_unstable_chartField hP hgr hL hc hf1 hρ hinv hred

end Reduction

end powerlib.Dynamics.CenterManifold
