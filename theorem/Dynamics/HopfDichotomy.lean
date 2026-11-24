import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.LinearAlgebra.Eigenspace.Zero
import theorem.Dynamics.CenterReduction
import theorem.Dynamics.CenterReductionStability
import theorem.Linear.Stability

/-! # The centre–stable dichotomy of a Hopf point and the projection-formula laws (foundation)

At a Hopf point the hypotheses of the centre-manifold reduction
(`CenterManifold.unstable_of_firstLyapunov_pos`, `theorem/Dynamics/CenterReduction.lean`;
`CenterManifold.localAsymptoticStable_of_firstLyapunov_neg`,
`theorem/Dynamics/CenterReductionStability.lean`) follow
from two algebraic facts: a critical pair `(q, p)` of `A = DF(0)` (`A q = iωq`, `Aᵀp = −iωp`,
`⟨p, q⟩ = 1`) and a factorization `det(sI − A) = (s² + ω²) r(s)` with `r` Hurwitz. Then the
spectral projection `P = ιπ` of the critical chart has the dichotomy of the centre-manifold
theorem with `ε = 0` (`‖e^{tA}P‖ ≤ K`, `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}`), `A` and `2iω − A` are
invertible, and for an analytic field the second and third derivatives are symmetric and give the
cubic Taylor expansion. Hence: **`ℓ₁ > 0` (Kuznetsov's projection formula) gives instability and
`ℓ₁ < 0` local asymptotic stability of every analytic field with such a Hopf point, in any
dimension.**

Scope.
* Generic: `State n = ℝⁿ`, a real linear map `A` (complexified matrix `cmat A`), a critical pair
  (`IsCritical`), a complex polynomial `r` with `charpoly(cmat A) = (X² + ω²) r` and every root of
  `r` in the open left half plane (so `±iω` are simple eigenvalues and no other eigenvalue lies on
  the imaginary axis). The field `F` is `C¹` and analytic at the equilibrium `0` (Mathlib's
  `AnalyticAt`; analyticity gives the symmetry of `D³F(0)` and the Taylor expansion, which Mathlib
  has for analytic maps only). Nothing here describes a physical system (foundation).
* The dichotomy is proved for the projection of the critical chart itself: the stable part
  `B = A(1 − P) − P` has the eigenvalues `−1` and the roots of `r` (the eigenvalues `±iω` are
  geometrically simple, Mathlib's `LinearMap.finrank_eigenspace_le`), so it is Hurwitz and its
  flow agrees with that of `A` on `range (1 − P)`; the centre bound is the rotation identity
  `(A² + ω²)P = 0`. No Bezout identity is needed.
* Lyapunov instability and local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) of the equilibrium; `ℓ₁ = 0` is not decided.

Source: Carr, *Applications of Centre Manifold Theory* (1981), §1.2 and §2.4 (the spectral
splitting and the reduction principle, both halves); Kuznetsov, *Elements of Applied Bifurcation
Theory* (3rd ed.), §3.5 and §5.4 (the critical pair, the projection formula);
Hirsch–Smale–Devaney, *Differential Equations, Dynamical Systems, and an Introduction to Chaos*,
§6 (exponential decay of a Hurwitz flow).

Results.
* Flows: `LyapunovPerron.norm_expFlow_le_of_hurwitz` (a map whose complexified matrix is Hurwitz
  has `‖e^{tB}‖ ≤ K e^{−at}`, `a > 0`, from `Linear.globallyExponentiallyStable_of_isHurwitz`),
  `LyapunovPerron.expFlow_mul_eq_of_mul_eq` (`AB = BA`, `BS = AS` give `e^{tA}S = e^{tB}S`).
* Linear algebra: `NormalForm.LyapunovCoefficient.cmat_sub`, `eq_smul_of_charpoly` (a simple
  root of the characteristic polynomial has a one-dimensional eigenspace),
  `isUnit_det_of_charpoly` (`A`, `2iω − A` invertible).
* The critical chart: `IsCritical.q_ne_zero`, `IsCritical.cmat_critP_mulVec` (`P q = q`),
  `IsCritical.rotation_critP` (`(A² + ω²) P = 0`), `IsCritical.eq_smul` (every eigenvector of
  `iω` is a multiple of `q`), `IsCritical.stablePart_hurwitz`,
  **`IsCritical.exists_dichotomy`** (the dichotomy of the centre-manifold theorem with `ε = 0`).
* The coefficient is well defined: `exists_isCritical_of_charpoly` (a critical pair exists),
  `sign_firstLyapunov_eq_of_charpoly` (its sign does not depend on the critical pair).
* Analytic fields: `taylor3_isBigO` (`F(x) − T₃F(x) = O(‖x‖⁴)`),
  `iteratedFDeriv_two_eq_of_analytic`, `iteratedFDeriv_three_eq_of_analytic` (the symmetric
  forms `Q = D²F(0)/2`, `C = D³F(0)/6`).
* **`unstable_of_firstLyapunov_pos_of_charpoly`**: `F` `C¹`, analytic at `0`, a critical pair at
  `0`, `charpoly = (s² + ω²) r(s)`, `r` Hurwitz, `firstLyapunov F 0 ω q p > 0` ⇒ `Unstable F 0`;
  **`localAsymptoticStable_of_firstLyapunov_neg_of_charpoly`**: the same with
  `firstLyapunov F 0 ω q p < 0` ⇒ `LocalAsymptoticStable F 0`.
-/

noncomputable section

open Set Filter Topology Asymptotics Complex Polynomial Matrix

namespace powerlib.Dynamics.LyapunovPerron

section Flows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Flows agreeing on a range.** If `AB = BA` and `BS = AS`, then `e^{tA}S = e^{tB}S`
(`e^{−sA}e^{sB}S` is constant). -/
@[tmio T, powerlib_foundation] theorem expFlow_mul_eq_of_mul_eq {A B S : E →L[ℝ] E}
    (hAB : Commute A B) (hBS : B * S = A * S) (t : ℝ) : expFlow A t * S = expFlow B t * S := by
  have hG : ∀ s, HasDerivAt (fun s => expFlow A (-s) * (expFlow B s * S)) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => expFlow A (-s)) (-(expFlow A (-s) * A)) s := by
      have := (hasDerivAt_expFlow (A := A) (-s)).scomp s (hasDerivAt_neg s)
      rw [neg_one_smul] at this
      exact this
    have h2 : HasDerivAt (fun s => expFlow B s * S) (expFlow B s * B * S) s :=
      (hasDerivAt_expFlow (A := B) s).mul_const S
    refine (h1.mul h2).congr_deriv ?_
    have hc : A * expFlow B s = expFlow B s * A :=
      ((expFlow_commute (A := B) (P := A) hAB.symm s).eq).symm
    rw [mul_assoc (expFlow B s) B S, hBS, neg_mul, mul_assoc, ← mul_assoc A, hc]
    noncomm_ring
  have hconst : ∀ s, expFlow A (-s) * (expFlow B s * S) = expFlow A (-0) * (expFlow B 0 * S) :=
    fun s => is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
      (fun s => (hG s).deriv) s 0
  have h0 : expFlow A (-0) * (expFlow B 0 * S) = S := by simp [expFlow_zero]
  calc expFlow A t * S = expFlow A t * (expFlow A (-t) * (expFlow B t * S)) := by
        rw [hconst, h0]
    _ = expFlow B t * S := by rw [← mul_assoc, expFlow_mul_neg, one_mul]

end Flows

open NormalForm.LyapunovCoefficient LinearSystems

variable {n : ℕ}

/-- **Exponential decay of a Hurwitz flow.** If every complex eigenvalue of the complexified
matrix of `B` has negative real part, `‖e^{tB}‖ ≤ K e^{−at}` for `t ≥ 0`, with `a > 0`. -/
@[tmio T, powerlib_foundation] theorem norm_expFlow_le_of_hurwitz {B : State n →L[ℝ] State n}
    (hB : ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → cmat B *ᵥ v = μ • v → μ.re < 0) :
    ∃ K a : ℝ, 0 < a ∧ ∀ t, 0 ≤ t → ‖expFlow B t‖ ≤ K * Real.exp (-(a * t)) := by
  set M := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm B with hM
  have hop : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M = B := by simp [hM]
  have hH : IsHurwitz M := by
    intro μ v hv he
    rw [neg_zero]
    refine hB μ v hv ?_
    rw [← hop, cmat_toEuclideanCLM]
    exact he
  obtain ⟨-, -, a, ha, C, hC⟩ := Linear.globallyExponentiallyStable_of_isHurwitz 0 hH
  refine ⟨|C|, a, ha, fun t ht => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have htr : IsTrajectoryOn (Linear.solution M 0 0 x) (affineLinearVectorField M 0) 0 t :=
    fun s _ => (Linear.solution_hasDerivAt M 0 0 x s).hasDerivWithinAt
  have h := hC 0 t _ htr t ⟨ht, le_rfl⟩
  have e : Linear.solution M 0 0 x t = expFlow B t x := by
    simp [Linear.solution, expFlow, hop]
  rw [e, Linear.solution_initial, sub_zero, sub_zero, sub_zero] at h
  calc ‖expFlow B t x‖ ≤ C * Real.exp (-a * t) * ‖x‖ := h
    _ ≤ |C| * Real.exp (-(a * t)) * ‖x‖ := by
      rw [neg_mul]; gcongr; exact le_abs_self C

end powerlib.Dynamics.LyapunovPerron

namespace powerlib.NormalForm.LyapunovCoefficient

open powerlib.Dynamics (State)

variable {n : ℕ}

/-- The complexified matrix of a difference. -/
@[tmio T, powerlib_foundation] theorem cmat_sub (L L' : State n →L[ℝ] State n) :
    cmat (L - L') = cmat L - cmat L' := by
  ext k j; simp [cmat]

end powerlib.NormalForm.LyapunovCoefficient

namespace powerlib.Dynamics.CenterManifold

open NormalForm.LyapunovCoefficient LyapunovPerron

variable {n : ℕ}

/-! ## Linear algebra -/

/-- **Geometric simplicity of a simple eigenvalue.** If `χ_M = (X − μ) r` with `r(μ) ≠ 0` and
`q ≠ 0` is an eigenvector of `μ`, every eigenvector of `μ` is a multiple of `q` (Mathlib's
`LinearMap.finrank_eigenspace_le`: geometric multiplicity at most algebraic multiplicity). -/
@[tmio T, powerlib_foundation] theorem eq_smul_of_charpoly {M : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    {r : ℂ[X]} (hchar : M.charpoly = (X - C μ) * r) (hr : r.eval μ ≠ 0) {q v : Fin n → ℂ}
    (hq : M *ᵥ q = μ • q) (hq0 : q ≠ 0) (hv : M *ᵥ v = μ • v) : ∃ c : ℂ, v = c • q := by
  set φ := Matrix.toLin' M
  have hne : (X - C μ) * r ≠ 0 := mul_ne_zero (X_sub_C_ne_zero μ) fun h => hr (by simp [h])
  have hmult : φ.charpoly.rootMultiplicity μ = 1 := by
    rw [Matrix.charpoly_toLin', hchar, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_self,
      rootMultiplicity_eq_zero (by simpa [IsRoot] using hr)]
  have hle := LinearMap.finrank_eigenspace_le φ μ
  rw [hmult] at hle
  have hqm : q ∈ Module.End.eigenspace φ μ :=
    Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hq)
  have hvm : v ∈ Module.End.eigenspace φ μ :=
    Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hv)
  obtain ⟨w, hw⟩ := finrank_le_one_iff.mp hle
  obtain ⟨a, ha⟩ := hw ⟨q, hqm⟩
  obtain ⟨b, hb⟩ := hw ⟨v, hvm⟩
  have ha' : a • (w : Fin n → ℂ) = q := congrArg Subtype.val ha
  have hb' : b • (w : Fin n → ℂ) = v := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha'; exact hq0 ha'.symm
  refine ⟨b / a, ?_⟩
  rw [← ha', ← hb', smul_smul, div_mul_cancel₀ b ha0]

@[tmio T, powerlib_foundation] private theorem sq_add_sq_eq (ω : ℝ) :
    (X ^ 2 + C ((ω : ℂ) ^ 2) : ℂ[X]) = (X - C ((ω : ℂ) * I)) * (X + C ((ω : ℂ) * I)) := by
  have h : ((ω : ℂ) * I) ^ 2 = -((ω : ℂ) ^ 2) := by rw [mul_pow, I_sq]; ring
  rw [show (X - C ((ω : ℂ) * I)) * (X + C ((ω : ℂ) * I)) = X ^ 2 - C ((ω : ℂ) * I) ^ 2 by ring,
    ← map_pow, h, map_neg, sub_neg_eq_add]

@[tmio T, powerlib_foundation] private theorem eval_ne_zero_of_re {r : ℂ[X]}
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {s : ℂ} (hs : s.re = 0) : r.eval s ≠ 0 :=
  fun h => by linarith [hr s h]

/-- **Invertibility at a Hopf point.** If `χ_M = (X² + ω²) r`, `ω ≠ 0`, `r` Hurwitz, then `M` and
`2iω − M` are invertible. -/
@[tmio T, powerlib_foundation] theorem isUnit_det_of_charpoly {M : Matrix (Fin n) (Fin n) ℂ}
    {ω : ℝ} (hω : ω ≠ 0) {r : ℂ[X]} (hchar : M.charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    IsUnit M.det ∧ IsUnit (shift2 M ω).det := by
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have hev : ∀ s : ℂ, (s • (1 : Matrix (Fin n) (Fin n) ℂ) - M).det =
      (s ^ 2 + (ω : ℂ) ^ 2) * r.eval s := by
    intro s
    have h := Matrix.eval_charpoly M s
    rw [hchar, eval_mul, eval_add, eval_pow, eval_X, eval_C, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at h
    exact h.symm
  constructor
  · have h := hev 0
    rw [zero_smul, zero_sub, Matrix.det_neg] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h
    have hr0 := eval_ne_zero_of_re hr (s := 0) rfl
    exact hr0 (by simpa [hω'] using h.symm)
  · refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h := hev ((2 * ω : ℂ) * I)
    rw [shift2] at h0
    rw [h0] at h
    have hr2 := eval_ne_zero_of_re hr (s := (2 * ω : ℂ) * I) (by simp)
    have hc : ((2 * ω : ℂ) * I) ^ 2 + (ω : ℂ) ^ 2 = -(3 * (ω : ℂ) ^ 2) := by
      rw [mul_pow, I_sq]; ring
    rw [hc] at h
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 2 hω'))) hr2
      h.symm

/-! ## The critical chart -/

variable {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation] theorem IsCritical.q_ne_zero (hc : IsCritical A ω q p) :
    q ≠ 0 := by
  rintro rfl
  have h := hc.normalized
  simp at h

/-- The projection of the critical chart fixes `q`. -/
@[tmio T, powerlib_foundation] theorem IsCritical.cmat_critP_mulVec (hc : IsCritical A ω q p) :
    cmat (critP q p) *ᵥ q = q := by
  have e := q_eq_comb q
  calc cmat (critP q p) *ᵥ q = cmat (critP q p) *ᵥ (((1 + I) / 2) • toC (reV q + imV q) +
        ((1 - I) / 2) • toC (reV q - imV q)) := congrArg _ e
    _ = q := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, cmat_mulVec_toC,
        cmat_mulVec_toC, hc.critP_v0, hc.critP_v1]
      exact e.symm

/-- `(A² + ω²) P = 0`: on the critical plane `A` is a rotation of frequency `ω` (the form of
`LyapunovPerron.norm_expFlow_mul_le_of_rotation` with `c = 0`). -/
@[tmio T, powerlib_foundation] theorem IsCritical.rotation_critP (hc : IsCritical A ω q p) :
    (A + (0 : ℝ) • 1) * ((A + (0 : ℝ) • 1) * critP q p) + ω ^ 2 • critP q p = 0 := by
  have h0 : A + (0 : ℝ) • (1 : State n →L[ℝ] State n) = A := by
    ext1 y; simp
  rw [h0]
  ext1 x
  show A (A (critι q (critπ p x))) + ω ^ 2 • critι q (critπ p x) = 0
  rw [hc.apply_critι, hc.apply_critι, rotL_rotL, map_smul]
  module

/-- **The critical eigenvalue is geometrically simple**: if `χ_A = (X² + ω²) r` with `r` Hurwitz,
every eigenvector of `iω` is a multiple of `q`. -/
@[tmio T, powerlib_foundation] theorem IsCritical.eq_smul (hc : IsCritical A ω q p) {r : ℂ[X]}
    (hchar : (cmat A).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {v : Fin n → ℂ}
    (hv : cmat A *ᵥ v = ((ω : ℂ) * I) • v) : ∃ c : ℂ, v = c • q := by
  refine eq_smul_of_charpoly (r := (X + C ((ω : ℂ) * I)) * r) ?_ ?_ hc.right hc.q_ne_zero hv
  · rw [hchar, sq_add_sq_eq, mul_assoc]
  · rw [eval_mul, eval_add, eval_X, eval_C]
    refine mul_ne_zero ?_ (eval_ne_zero_of_re hr (by simp))
    have hω : (ω : ℂ) ≠ 0 := by exact_mod_cast hc.freq_pos.ne'
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hω I_ne_zero)

/-- **The stable part is Hurwitz.** If `χ_A = (X² + ω²) r` with `r` Hurwitz, the complexified
matrix of `B = A(1 − P) − P` (`P` the projection of the critical chart) has the eigenvalues `−1`
(on `range P`) and the roots of `r` (on `range (1 − P)`): all in the open left half plane. -/
@[tmio T, powerlib_foundation] theorem IsCritical.stablePart_hurwitz (hc : IsCritical A ω q p)
    {r : ℂ[X]} (hchar : (cmat A).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (μ : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (he : cmat (A * (1 - critP q p) - critP q p) *ᵥ v = μ • v) : μ.re < 0 := by
  have hP := hc.isCommutingProjection
  set Pc := cmat (critP q p) with hPc
  set Ac := cmat A with hAc
  have hPP : Pc * Pc = Pc := by
    rw [hPc, ← cmat_comp]; congr 1; ext1 x; exact hP.idem x
  have hAP : Pc * Ac = Ac * Pc := by
    rw [hPc, hAc, ← cmat_comp, ← cmat_comp]; congr 1; ext1 x; exact (hP.comm x).symm
  have hB : cmat (A * (1 - critP q p) - critP q p) = Ac * (1 - Pc) - Pc := by
    rw [cmat_sub, show A * (1 - critP q p) = A.comp (1 - critP q p) from rfl, cmat_comp,
      cmat_sub, show (1 : State n →L[ℝ] State n) = ContinuousLinearMap.id ℝ _ from rfl, cmat_id]
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
      rw [sq_add_sq_eq, eval_mul, eval_sub, eval_add, eval_X, eval_C] at h2
      have hwq : ∀ u : Fin n → ℂ, u ≠ 0 → Pc *ᵥ u = 0 → Ac *ᵥ u = ((ω : ℂ) * I) • u →
          False := by
        intro u hu0 hPu hAu
        obtain ⟨c, rfl⟩ := hc.eq_smul hchar hr hAu
        rw [Matrix.mulVec_smul, hc.cmat_critP_mulVec] at hPu
        exact hu0 hPu
      rcases mul_eq_zero.mp h2 with h | h
      · have hμ : μ = (ω : ℂ) * I := by linear_combination h
        rw [hμ] at hw
        exact hwq w hw0 hPw hw
      · have hμ : μ = -((ω : ℂ) * I) := by linear_combination h
        refine hwq (star w) (by simpa using hw0) ?_ ?_
        · rw [← cmat_mulVec_star, hPw, star_zero]
        · rw [← cmat_mulVec_star, hw, hμ, star_smul]
          congr 1
          simp
    · exact hr μ h2

/-- **The centre–stable dichotomy of a Hopf point.** If `(q, p)` is a critical pair of `A` and
`χ_A = (X² + ω²) r` with `r` Hurwitz, the projection `P = ιπ` of the critical chart has the
dichotomy of the centre-manifold theorem with `ε = 0`: `‖e^{tA} P‖ ≤ K` for all `t` and
`‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` for `t ≥ 0`, `β > 0`. -/
@[tmio T, powerlib_foundation] theorem IsCritical.exists_dichotomy (hc : IsCritical A ω q p)
    {r : ℂ[X]} (hchar : (cmat A).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ K β : ℝ, 0 < β ∧ (∀ t, ‖expFlow A t * critP q p‖ ≤ K * Real.exp (0 * |t|)) ∧
      ∀ t, 0 ≤ t → ‖expFlow A t * (1 - critP q p)‖ ≤ K * Real.exp (-(β * t)) := by
  have hP := hc.isCommutingProjection
  set P := critP q p with hPdef
  have hPP : P * P = P := by ext1 x; exact hP.idem x
  have hAP : P * A = A * P := by ext1 x; exact (hP.comm x).symm
  set B := A * (1 - P) - P with hB
  obtain ⟨K₂, a, ha, hK₂⟩ := norm_expFlow_le_of_hurwitz (B := B) (hc.stablePart_hurwitz hchar hr)
  have hcen := norm_expFlow_mul_le_of_rotation (A := A) (P := P) (c := 0) hc.freq_pos.ne'
    hc.rotation_critP
  set K₁ := ‖P‖ + ‖(A + (0 : ℝ) • 1) * P‖ / |ω|
  have hcomm : Commute A B := by
    simp only [Commute, SemiconjBy, hB, mul_sub, sub_mul, mul_one, mul_assoc, hAP]
  have hBS : B * (1 - P) = A * (1 - P) := by
    simp only [hB, mul_sub, sub_mul, mul_one, mul_assoc, hPP, sub_self]
    abel
  refine ⟨max K₁ (K₂ * ‖1 - P‖), a, ha, fun t => ?_, fun t ht => ?_⟩
  · calc ‖expFlow A t * P‖ ≤ K₁ * Real.exp (-(0 * t)) := hcen t
      _ ≤ max K₁ (K₂ * ‖1 - P‖) * Real.exp (0 * |t|) := by
        simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
        exact le_max_left _ _
  · rw [expFlow_mul_eq_of_mul_eq hcomm hBS t]
    calc ‖expFlow B t * (1 - P)‖ ≤ ‖expFlow B t‖ * ‖1 - P‖ := norm_mul_le _ _
      _ ≤ K₂ * Real.exp (-(a * t)) * ‖1 - P‖ := by gcongr; exact hK₂ t ht
      _ ≤ max K₁ (K₂ * ‖1 - P‖) * Real.exp (-(a * t)) := by
        rw [mul_right_comm]; gcongr; exact le_max_right _ _

@[tmio T, powerlib_foundation] private theorem vecMul_aeval_of_eigen
    {M : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} {u : Fin n → ℂ} (h : u ᵥ* M = μ • u) (f : ℂ[X]) :
    u ᵥ* aeval M f = f.eval μ • u := by
  induction f using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one, Matrix.vecMul_smul]
  | add f g hf hg => simp [Matrix.vecMul_add, hf, hg, add_smul]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul,
      h, smul_smul]
    simp only [eval_mul, eval_C, eval_pow, eval_X]

/-- **A critical pair exists at a Hopf point.** If `χ_A = (X² + ω²) r`, `ω > 0`, `r` Hurwitz,
`A` has a critical pair `(q, p)`: a left eigenvector of the simple eigenvalue `iω` is not
orthogonal to the right one (`g(A)`, `χ_A = (X − iω) g`, maps every vector into the
one-dimensional eigenspace and multiplies the left eigenvector by `g(iω) ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem exists_isCritical_of_charpoly
    {A : State n →L[ℝ] State n} {ω : ℝ} (hω : 0 < ω) {r : ℂ[X]}
    (hchar : (cmat A).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) : ∃ q p : Fin n → ℂ, IsCritical A ω q p := by
  set Ac := cmat A with hAc
  set μ : ℂ := (ω : ℂ) * I with hμ
  set g : ℂ[X] := (X + C μ) * r with hgdef
  have hfac : Ac.charpoly = (X - C μ) * g := by rw [hchar, sq_add_sq_eq, mul_assoc]
  have hg : g.eval μ ≠ 0 := by
    rw [hgdef, eval_mul, eval_add, eval_X, eval_C]
    refine mul_ne_zero ?_ fun h => by linarith [hr μ h, show μ.re = 0 by simp [hμ]]
    have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hω' I_ne_zero)
  have hroot : (Ac.charpoly).eval μ = 0 := by rw [hfac]; simp
  obtain ⟨q, hq0, hq⟩ : ∃ q : Fin n → ℂ, q ≠ 0 ∧ Ac *ᵥ q = μ • q := by
    have h := hroot
    rw [Matrix.eval_charpoly] at h
    obtain ⟨q, hq0, hq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine ⟨q, hq0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hq
    rw [← hq]; ext i; simp [Matrix.scalar_apply]
  obtain ⟨u, hu0, hu⟩ : ∃ u : Fin n → ℂ, u ≠ 0 ∧ u ᵥ* Ac = μ • u := by
    have h : (Acᵀ.charpoly).eval μ = 0 := by rw [Matrix.charpoly_transpose]; exact hroot
    rw [Matrix.eval_charpoly] at h
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine ⟨u, hu0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hu
    rw [← Matrix.mulVec_transpose, ← hu]; ext i; simp [Matrix.scalar_apply]
  -- `g(A)` maps into the eigenspace of `μ`, and `u g(A) = g(μ) u`
  have hz : aeval Ac ((X - C μ) * g) = 0 := by rw [← hfac, Matrix.aeval_self_charpoly]
  have hE : ∀ v, Ac *ᵥ (aeval Ac g *ᵥ v) = μ • (aeval Ac g *ᵥ v) := by
    intro v
    have h := congrArg (· *ᵥ v) hz
    simp only [map_mul, map_sub, aeval_X, aeval_C, Matrix.zero_mulVec] at h
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact h
  have huE : ∀ v, u ⬝ᵥ (aeval Ac g *ᵥ v) = g.eval μ * (u ⬝ᵥ v) := by
    intro v
    rw [Matrix.dotProduct_mulVec, vecMul_aeval_of_eigen hu, smul_dotProduct, smul_eq_mul]
  have huq : u ⬝ᵥ q ≠ 0 := by
    intro h0
    apply hu0
    funext i
    obtain ⟨c, hc⟩ := eq_smul_of_charpoly hfac hg hq hq0 (hE (Pi.single i 1))
    have h := huE (Pi.single i 1)
    rw [hc, dotProduct_smul, h0, smul_zero, dotProduct_single, mul_one] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hg
  set s := u ⬝ᵥ q with hs
  refine ⟨q, (starRingEnd ℂ s)⁻¹ • star u, hω, hq, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, ← star_cmatT_mulVec, Matrix.mulVec_transpose, hu, star_smul,
      smul_comm]
    congr 1
    simp [hμ]
  · rw [star_smul, star_star, smul_dotProduct, smul_eq_mul]
    have e : star ((starRingEnd ℂ) s)⁻¹ = s⁻¹ := by simp
    rw [e, inv_mul_cancel₀ huq]

/-- **The sign of `ℓ₁` does not depend on the critical pair**: if `χ = (X² + ω²) r` with `r`
Hurwitz, the eigenvalues `±iω` are simple, every critical pair is a rescaling of any other, and
`firstLyapunov` has the same sign for all of them (`sign_firstLyapunov_eq`). -/
@[tmio T, powerlib_foundation] theorem sign_firstLyapunov_eq_of_charpoly {F : State n → State n}
    {x₀ : State n} {ω : ℝ} {q p q' p' : Fin n → ℂ} {r : ℂ[X]}
    (hchar : (jacobianC F x₀).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (h : IsCriticalPair F x₀ ω q p)
    (h' : IsCriticalPair F x₀ ω q' p') :
    SignType.sign (firstLyapunov F x₀ ω q' p') = SignType.sign (firstLyapunov F x₀ ω q p) := by
  have hc : IsCritical (fderiv ℝ F x₀) ω q p := ⟨h.freq_pos, h.right, h.left, h.normalized⟩
  refine sign_firstLyapunov_eq (fun v hv => hc.eq_smul hchar hr hv) (fun v hv => ?_) h h'
  have hp0 : p ≠ 0 := by
    rintro rfl
    have hn := h.normalized
    simp at hn
  refine eq_smul_of_charpoly (r := (X - C ((ω : ℂ) * I)) * r) ?_ ?_ h.left hp0 hv
  · rw [Matrix.charpoly_transpose, hchar, sq_add_sq_eq, map_neg, sub_neg_eq_add]
    ring
  · rw [eval_mul, eval_sub, eval_X, eval_C]
    refine mul_ne_zero ?_ (eval_ne_zero_of_re hr (by simp))
    have hω : (ω : ℂ) ≠ 0 := by exact_mod_cast h.freq_pos.ne'
    rw [show -((ω : ℂ) * I) - (ω : ℂ) * I = -(2 * ((ω : ℂ) * I)) by ring, neg_ne_zero]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hω I_ne_zero)

/-! ## Analytic fields -/

/-- **Cubic Taylor expansion of an analytic map**: `F(x) − (F(0) + DF(0)x + D²F(0)(x, x)/2 +
D³F(0)(x, x, x)/6) = O(‖x‖⁴)` (Mathlib's `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` and
`HasFPowerSeriesOnBall.factorial_smul`). -/
@[tmio T, powerlib_foundation] theorem taylor3_isBigO {F : State n → State n}
    (hF : AnalyticAt ℝ F 0) :
    (fun x => F x - (F 0 + fderiv ℝ F 0 x + (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 x x +
      (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0 ![x, x, x])) =O[𝓝 0] fun x => ‖x‖ ^ 4 := by
  obtain ⟨p, hp⟩ := hF
  have hO := HasFPowerSeriesAt.isBigO_sub_partialSum_pow hp 4
  obtain ⟨r, hr⟩ := hp
  refine hO.congr_left fun x => ?_
  have h0 := hr.factorial_smul x 0
  have h1 := hr.factorial_smul x 1
  have h2 := hr.factorial_smul x 2
  have h3 := hr.factorial_smul x 3
  rw [iteratedFDeriv_zero_apply] at h0
  rw [iteratedFDeriv_one_apply] at h1
  rw [iteratedFDeriv_two_apply] at h2
  have e3 : (![x, x, x] : Fin 3 → State n) = fun _ => x := by
    funext i; fin_cases i <;> rfl
  rw [e3, zero_add]
  have hs : p.partialSum 4 x = F 0 + fderiv ℝ F 0 x + (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 x x +
      (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0 (fun _ => x) := by
    rw [← h3, ← h2, ← h1, ← h0]
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, Nat.factorial, Nat.succ_eq_add_one]
    norm_num [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [hs]

/-- The second derivative of an analytic map is symmetric: `D²F(0)(u, w) = Q(u, w) + Q(w, u)`
with `Q = D²F(0)/2`. -/
@[tmio T, powerlib_foundation] theorem iteratedFDeriv_two_eq_of_analytic {F : State n → State n}
    (hF : AnalyticAt ℝ F 0) (u w : State n) :
    iteratedFDeriv ℝ 2 F 0 ![u, w] = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 u w +
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 w u := by
  have hs := ContDiffAt.iteratedFDeriv_comp_perm (hF.contDiffAt (n := ⊤)) (n := 2) ![u, w]
    (Equiv.swap 0 1)
  have e : (![u, w] : Fin 2 → State n) ∘ Equiv.swap 0 1 = ![w, u] := by
    funext i; fin_cases i <;> rfl
  rw [e, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply] at hs
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs ⊢
  rw [hs, ← add_smul]
  norm_num

/-- The third derivative of an analytic map is symmetric: `D³F(0)` is the sum of `C = D³F(0)/6`
over the six orders of its arguments. -/
@[tmio T, powerlib_foundation] theorem iteratedFDeriv_three_eq_of_analytic
    {F : State n → State n} (hF : AnalyticAt ℝ F 0) (u w z : State n) :
    iteratedFDeriv ℝ 3 F 0 ![u, w, z] =
      ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0) ![u, w, z] +
      ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0) ![u, z, w] +
      ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0) ![w, u, z] +
      ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0) ![w, z, u] +
      ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0) ![z, u, w] +
      ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0) ![z, w, u] := by
  have hp : ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → State n), v = ![u, w, z] ∘ σ →
      iteratedFDeriv ℝ 3 F 0 v = iteratedFDeriv ℝ 3 F 0 ![u, w, z] := by
    rintro σ v rfl
    exact ContDiffAt.iteratedFDeriv_comp_perm (hF.contDiffAt (n := ⊤)) _ σ
  simp only [_root_.smul_apply]
  rw [hp (Equiv.swap 1 2) ![u, z, w] (by funext i; fin_cases i <;> rfl),
    hp (Equiv.swap 0 1) ![w, u, z] (by funext i; fin_cases i <;> rfl),
    hp (finRotate 3) ![w, z, u] (by funext i; fin_cases i <;> rfl),
    hp (finRotate 3).symm ![z, u, w] (by funext i; fin_cases i <;> rfl),
    hp (Equiv.swap 0 2) ![z, w, u] (by funext i; fin_cases i <;> rfl)]
  module

/-! ## The projection-formula laws for analytic fields -/

/-- At a Hopf point of an analytic field, `A = DF(0)`, `f = F − A`, `Q = D²F(0)/2`,
`C = D³F(0)/6` satisfy every hypothesis of the reduction laws (`unstable_of_firstLyapunov_pos`,
`localAsymptoticStable_of_firstLyapunov_neg`) with `ε = 0`. -/
@[tmio T, powerlib_foundation] private theorem exists_reductionData {F : State n → State n}
    (hF : ContDiff ℝ 1 F) (ha : AnalyticAt ℝ F 0) {ω : ℝ} {q p : Fin n → ℂ}
    (hcp : IsCriticalPair F 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ (A : State n →L[ℝ] State n) (f : State n → State n)
      (Q : State n →L[ℝ] State n →L[ℝ] State n)
      (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)) (K β : ℝ),
      fullField A f = F ∧ 0 < β ∧ (∀ t, ‖expFlow A t * critP q p‖ ≤ K * Real.exp (0 * |t|)) ∧
      (∀ t, 0 ≤ t → ‖expFlow A t * (1 - critP q p)‖ ≤ K * Real.exp (-(β * t))) ∧
      ContDiff ℝ 1 f ∧ f 0 = 0 ∧ fderiv ℝ f 0 = 0 ∧
      (fun x => f x - (Q x x + C ![x, x, x])) =o[𝓝 0] (fun x => ‖x‖ ^ 3) ∧
      (∀ u w, iteratedFDeriv ℝ 2 (fullField A f) 0 ![u, w] = Q u w + Q w u) ∧
      (∀ u w z, iteratedFDeriv ℝ 3 (fullField A f) 0 ![u, w, z] = C ![u, w, z] +
        C ![u, z, w] + C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u]) ∧
      IsUnit (cmat A).det ∧ IsUnit (shift2 (cmat A) ω).det := by
  set A := fderiv ℝ F 0 with hAdef
  set f : State n → State n := fun x => F x - A x with hfdef
  have hFf : fullField A f = F := by funext x; simp [fullField, hfdef]
  have hc : IsCritical A ω q p := IsCriticalPair.isCritical hcp rfl
  have hF0 : F 0 = 0 := hcp.equilibrium
  obtain ⟨K, β, hβ, hcen, hst⟩ := hc.exists_dichotomy hchar hr
  have hDf : fderiv ℝ f 0 = 0 := by
    have h := (hF.differentiable one_ne_zero 0).hasFDerivAt.sub A.hasFDerivAt
    rw [← hAdef, sub_self] at h
    exact h.fderiv
  obtain ⟨hA, h2⟩ := isUnit_det_of_charpoly hc.freq_pos.ne' hchar hr
  refine ⟨A, f, (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0, (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F 0, K,
    β, hFf, hβ, hcen, hst, hF.sub A.contDiff, by simp [hfdef, hF0], hDf, ?_, ?_, ?_, hA, h2⟩
  · have hT := taylor3_isBigO ha
    have h43 : (fun x : State n => ‖x‖ ^ 4) =o[𝓝 0] fun x => ‖x‖ ^ 3 := by
      simpa using norm_pow_isLittleO (E := State n) (k := 3) (k' := 4) (by norm_num) Set.univ
    refine (hT.trans_isLittleO h43).congr_left fun x => ?_
    simp only [hfdef, hF0, zero_add]
    rw [_root_.smul_apply, _root_.smul_apply, _root_.smul_apply, ← hAdef]
    abel
  · intro u w
    rw [hFf, iteratedFDeriv_two_eq_of_analytic ha]
    rfl
  · intro u w z
    rw [hFf]
    exact iteratedFDeriv_three_eq_of_analytic ha u w z

/-- **`ℓ₁ > 0` gives instability at a Hopf point of an analytic field, in any dimension.** Let
`F` be `C¹` and analytic at the equilibrium `0`, let `(q, p)` be a critical pair of `F` at `0`,
and let the characteristic polynomial of `DF(0)` be `(s² + ω²) r(s)` with every root of `r` in
the open left half plane. If Kuznetsov's first Lyapunov coefficient
`firstLyapunov F 0 ω q p` is positive, the origin is unstable. (Dichotomy:
`IsCritical.exists_dichotomy`; invertibility: `isUnit_det_of_charpoly`; forms and expansion:
`iteratedFDeriv_two_eq_of_analytic`, `iteratedFDeriv_three_eq_of_analytic`, `taylor3_isBigO`;
reduction: `unstable_of_firstLyapunov_pos`.) -/
@[tmio T, powerlib_foundation] theorem unstable_of_firstLyapunov_pos_of_charpoly
    {F : State n → State n} (hF : ContDiff ℝ 1 F) (ha : AnalyticAt ℝ F 0) {ω : ℝ}
    {q p : Fin n → ℂ} (hcp : IsCriticalPair F 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (hl : 0 < firstLyapunov F 0 ω q p) :
    Unstable F 0 := by
  obtain ⟨A, f, Q, C, K, β, hFf, hβ, hcen, hst, hf, hf0, hDf, hfQC, hd2, hd3, hA, h2⟩ :=
    exists_reductionData hF ha hcp hchar hr
  rw [← hFf] at hl hcp ⊢
  exact unstable_of_firstLyapunov_pos hcp le_rfl (by linarith) hcen hst hf hf0 hDf hfQC hd2 hd3
    hA h2 hl

/-- **`ℓ₁ < 0` gives local asymptotic stability at a Hopf point of an analytic field, in any
dimension** (the stability counterpart of `unstable_of_firstLyapunov_pos_of_charpoly`, through
`localAsymptoticStable_of_firstLyapunov_neg`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_firstLyapunov_neg_of_charpoly
    {F : State n → State n} (hF : ContDiff ℝ 1 F) (ha : AnalyticAt ℝ F 0) {ω : ℝ}
    {q p : Fin n → ℂ} (hcp : IsCriticalPair F 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC F 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (hl : firstLyapunov F 0 ω q p < 0) :
    LocalAsymptoticStable F 0 := by
  obtain ⟨A, f, Q, C, K, β, hFf, hβ, hcen, hst, hf, hf0, hDf, hfQC, hd2, hd3, hA, h2⟩ :=
    exists_reductionData hF ha hcp hchar hr
  rw [← hFf] at hl hcp ⊢
  exact localAsymptoticStable_of_firstLyapunov_neg hcp le_rfl (by linarith) hcen hst hf hf0 hDf
    hfQC hd2 hd3 hA h2 hl

end powerlib.Dynamics.CenterManifold
