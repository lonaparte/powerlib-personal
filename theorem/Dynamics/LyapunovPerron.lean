import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The Lyapunov–Perron transform under an exponential dichotomy (foundation)

The analytic core of the centre-manifold theorem: for `ẋ = A x + b(t)` on a Banach space with a
projection `P` separating a slowly growing centre part from an exponentially decaying stable
part, the integral operator of Lyapunov and Perron, its weighted estimates, its fixed points for
a globally Lipschitz nonlinearity, and the converse (every solution of weighted growth is a
Lyapunov–Perron transform).

Scope.
* A real Banach space `E`, continuous linear maps `A`, `P`, the linear flow `e^{tA}`
  (`expFlow`, Mathlib's operator exponential). The dichotomy is a pair of theorem hypotheses,
  never a definition (semantic rule T): `‖e^{tA} P‖ ≤ K e^{ε|t|}` for all `t` (centre part) and
  `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` for `t ≥ 0` (stable part), with `0 ≤ ε < η < β`; functions are
  measured with the weight `e^{η|t|}`. There is no unstable part (the centre–stable case).
* Generic analysis, no model family (foundation). The centre manifolds built from it are in
  `theorem/Dynamics/CenterManifold.lean`.

Source: Vanderbauwhede, "Centre manifolds, normal forms and elementary bifurcations" (1989),
§2 (the Lyapunov–Perron operator on spaces of exponentially weighted functions); Carr,
*Applications of Centre Manifold Theory* (1981), Ch. 2; Kelley (1967).

Results.
* The linear flow: `expFlow`, `expFlow_zero`, `expFlow_add`, `expFlow_neg_mul`,
  `expFlow_mul_neg`, `expFlow_apply_neg_apply`, `expFlow_apply_apply`, `hasDerivAt_expFlow`,
  `expFlow_mul_comm`, `continuous_expFlow`, `expFlow_commute` (a map commuting with `A` commutes
  with `e^{tA}`), `hasDerivAt_expFlow_neg_apply`, `continuous_expFlow_neg_apply`;
  `nonneg_of_stable_bound` (the stable bound forces `K ≥ 0`).
* Dichotomy bounds from a polynomial identity: if `((A + c)² + ν²) P = 0`, `ν ≠ 0`, then
  `e^{tA} P = e^{−ct}(cos(νt) P + sin(νt) ν⁻¹ (A + c) P)` (`expFlow_mul_eq_of_rotation`, by
  constancy of `e^{−tA} F(t)`) and `‖e^{tA} P‖ ≤ (‖P‖ + ‖(A + c) P‖/|ν|) e^{−ct}`
  (`norm_expFlow_mul_le_of_rotation`): `c = 0` gives the centre bound with `ε = 0` for a pair of
  imaginary eigenvalues `±iν`, `c > 0` the stable bound for a pair `−c ± iν`.
* Scalar estimates: `norm_integral_le_center` (`|∫₀ᵗ e^{ε|t−s|} e^{η|s|}| ≤ e^{η|t|}/(η − ε)`),
  `integrableOn_Iic_stable` (`∫_{−∞}^t e^{−β(t−s)} e^{η|s|} ≤ 2e^{η|t|}/(β − η)`).
* The transform: `stableInit b = ∫_{−∞}^0 e^{−sA}(1 − P) b(s) ds`, `lpMap u b t =
  e^{tA}(P u + stableInit b + ∫₀ᵗ e^{−sA} b(s) ds)`; it solves `ẋ = A x + b`
  (`hasDerivAt_lpMap`, `continuous_lpMap`), splits into centre and stable parts (`lpMap_eq`),
  is affine (`lpMap_sub`) and satisfies the weighted estimate
  `‖lpMap u b t‖ ≤ K (‖u‖ + C κ) e^{η|t|}`, `κ = gapConst ε η β = 1/(η − ε) + 2/(β − η)`
  (`norm_lpMap_le`, `gapConst_pos`); integrability: `integrableOn_stable`,
  `integrableOn_stableInit`.
* Fixed points for a `δ`-Lipschitz `g` with `g 0 = 0` and `K δ κ < 1`: existence
  (`exists_fixedPoint`, the contraction principle on bounded continuous functions),
  Lipschitz dependence on the centre datum (`norm_sub_fixedPoint_le`) and uniqueness
  (`fixedPoint_unique`), with the iteration bound `le_of_contract` and the weight
  `continuous_weight`.
* The converse (`eq_lpMap_of_hasDerivAt`): a solution of `ẋ = A x + b` of weighted growth is
  the transform of its initial value (variation of constants on `[a, t]`, `a → −∞`).
-/

noncomputable section
namespace powerlib.Dynamics.LyapunovPerron

open Set Filter Topology MeasureTheory NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The operator exponential needs the `ℚ`-algebra structure of `E →L[ℝ] E`. -/
local instance : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _

/-- The linear flow `e^{tA}`. -/
def expFlow (A : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E := exp (t • A)

variable {A P : E →L[ℝ] E}

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem expFlow_zero : expFlow A 0 = 1 := by
  simp [expFlow]

@[tmio T, powerlib_foundation] theorem expFlow_add (s t : ℝ) :
    expFlow A (s + t) = expFlow A s * expFlow A t := by
  unfold expFlow
  rw [add_smul, exp_add_of_commute ((Commute.refl A).smul_left s |>.smul_right t)]

@[tmio T, powerlib_foundation] theorem expFlow_neg_mul (t : ℝ) :
    expFlow A (-t) * expFlow A t = 1 := by
  rw [← expFlow_add, neg_add_cancel, expFlow_zero]

@[tmio T, powerlib_foundation] theorem expFlow_mul_neg (t : ℝ) :
    expFlow A t * expFlow A (-t) = 1 := by
  rw [← expFlow_add, add_neg_cancel, expFlow_zero]

@[tmio T, powerlib_foundation] theorem expFlow_apply_neg_apply (t : ℝ) (x : E) :
    expFlow A t (expFlow A (-t) x) = x := by
  change (expFlow A t * expFlow A (-t)) x = x
  rw [expFlow_mul_neg]; rfl

@[tmio T, powerlib_foundation] theorem expFlow_apply_apply (s t : ℝ) (x : E) :
    expFlow A s (expFlow A t x) = expFlow A (s + t) x := by
  rw [expFlow_add]; rfl

@[tmio T, powerlib_foundation] theorem hasDerivAt_expFlow (t : ℝ) :
    HasDerivAt (expFlow A) (expFlow A t * A) t :=
  hasDerivAt_exp_smul_const A t

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem expFlow_mul_comm (t : ℝ) :
    expFlow A t * A = A * expFlow A t :=
  (((Commute.refl A).smul_left t).exp_left).eq

@[tmio T, powerlib_foundation] theorem continuous_expFlow : Continuous (expFlow A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_expFlow t).continuousAt

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem expFlow_commute (h : Commute A P) (t : ℝ) :
    Commute (expFlow A t) P :=
  (h.smul_left t).exp_left

/-! ## Dichotomy bounds from polynomial identities -/

/-- **The flow on a damped rotation block.** If `((A + c)² + ν²) P = 0` (`ν ≠ 0`), then
`e^{tA} P = e^{−ct}(cos(νt) P + sin(νt) ν⁻¹(A + c) P)`: on the range of `P` the flow is a
rotation of frequency `ν` damped at rate `c`. -/
@[tmio T, powerlib_foundation] theorem expFlow_mul_eq_of_rotation {c ν : ℝ} (hν : ν ≠ 0)
    (hq : (A + c • 1) * ((A + c • 1) * P) + ν ^ 2 • P = 0) (t : ℝ) :
    expFlow A t * P = Real.exp (-(c * t)) •
      (Real.cos (ν * t) • P + Real.sin (ν * t) • (ν⁻¹ • ((A + c • 1) * P))) := by
  set B := A + c • (1 : E →L[ℝ] E) with hB
  set W := ν⁻¹ • (B * P) with hW
  have hBP : B * P = ν • W := by rw [hW, smul_smul, mul_inv_cancel₀ hν, one_smul]
  have hBW : B * W = -(ν • P) := by
    have hBB : B * (B * P) = -(ν ^ 2 • P) := eq_neg_of_add_eq_zero_left hq
    rw [hW, mul_smul_comm, hBB, smul_neg, smul_smul, sq, ← mul_assoc, inv_mul_cancel₀ hν,
      one_mul]
  set F : ℝ → E →L[ℝ] E := fun s => Real.exp (-(c * s)) •
    (Real.cos (ν * s) • P + Real.sin (ν * s) • W) with hF
  have hFd : ∀ s, HasDerivAt F (A * F s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-(c * s))) (Real.exp (-(c * s)) * (-c)) s := by
      have := ((hasDerivAt_id' s).const_mul c).neg.exp
      simpa using this
    have hc : HasDerivAt (fun s => Real.cos (ν * s)) (-(Real.sin (ν * s)) * ν) s := by
      have := ((hasDerivAt_id' s).const_mul ν).cos
      simpa using this
    have hs : HasDerivAt (fun s => Real.sin (ν * s)) (Real.cos (ν * s) * ν) s := by
      have := ((hasDerivAt_id' s).const_mul ν).sin
      simpa using this
    have hin := (hc.smul_const P).add (hs.smul_const W)
    refine (he.smul hin).congr_deriv ?_
    have hAB : A = B - c • 1 := by rw [hB]; abel
    rw [hAB]
    simp only [hF, Pi.add_apply, sub_mul, mul_smul_comm, mul_add, smul_mul_assoc, one_mul, hBP,
      hBW]
    module
  -- `e^{−tA} F(t)` is constant
  have hG : ∀ s, HasDerivAt (fun s => expFlow A (-s) * F s) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => expFlow A (-s)) (-(expFlow A (-s) * A)) s := by
      have := (hasDerivAt_expFlow (A := A) (-s)).scomp s (hasDerivAt_neg s)
      rw [neg_one_smul] at this
      exact this
    refine (h1.mul (hFd s)).congr_deriv ?_
    rw [neg_mul, mul_assoc, neg_add_cancel]
  have hconst : ∀ s, expFlow A (-s) * F s = expFlow A (-0) * F 0 := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt) (fun s => (hG s).deriv) s 0
  have h0 : expFlow A (-0) * F 0 = P := by
    simp [hF, expFlow_zero]
  calc expFlow A t * P = expFlow A t * (expFlow A (-t) * F t) := by rw [hconst, h0]
    _ = F t := by rw [← mul_assoc, expFlow_mul_neg, one_mul]

/-- The bound of the damped rotation block: `‖e^{tA} P‖ ≤ (‖P‖ + ‖(A + c) P‖/|ν|) e^{−ct}`.
With `c = 0` it is the centre bound of the dichotomy with `ε = 0`; with `c = β > 0` the
stable bound. -/
@[tmio T, powerlib_foundation] theorem norm_expFlow_mul_le_of_rotation {c ν : ℝ} (hν : ν ≠ 0)
    (hq : (A + c • 1) * ((A + c • 1) * P) + ν ^ 2 • P = 0) (t : ℝ) :
    ‖expFlow A t * P‖ ≤ (‖P‖ + ‖(A + c • 1) * P‖ / |ν|) * Real.exp (-(c * t)) := by
  rw [expFlow_mul_eq_of_rotation hν hq t, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_comm]
  gcongr
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, ← div_eq_inv_mul]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one _)

/-! ## Scalar estimates -/

@[tmio T, powerlib_foundation] private theorem exp_mul_exp_eq {M a b c d : ℝ}
    (h : a + b = c + d) :
    M * Real.exp a * Real.exp b = M * Real.exp c * Real.exp d := by
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, h]

omit [CompleteSpace E] in
/-- `|∫₀ᵗ e^{ε|t−s|} e^{η|s|} ds| ≤ e^{η|t|}/(η − ε)` for `ε < η`, in the form of a bound on a
vector integrand. -/
@[tmio T, powerlib_foundation] theorem norm_integral_le_center {F : ℝ → E} {M ε η t : ℝ}
    (hM : 0 ≤ M) (hεη : ε < η)
    (hb : ∀ s, ‖F s‖ ≤ M * Real.exp (ε * |t - s|) * Real.exp (η * |s|)) :
    ‖∫ s in (0)..t, F s‖ ≤ M * Real.exp (η * |t|) / (η - ε) := by
  have hd : 0 < η - ε := sub_pos.2 hεη
  rcases le_total 0 t with ht | ht
  · -- `s ∈ [0, t]`: the bound is `M e^{εt} e^{(η−ε)s}`.
    set G : ℝ → ℝ := fun s => M * Real.exp (ε * t) * Real.exp ((η - ε) * s) / (η - ε)
    have hc : Continuous fun s => M * Real.exp (ε * t) * Real.exp ((η - ε) * s) := by fun_prop
    have hG : ∀ s, HasDerivAt G (M * Real.exp (ε * t) * Real.exp ((η - ε) * s)) s := by
      intro s
      have h := ((((hasDerivAt_id' s).const_mul (η - ε)).exp).const_mul
        (M * Real.exp (ε * t))).div_const (η - ε)
      refine h.congr_deriv ?_
      field_simp
    have hint : ∫ s in (0)..t, M * Real.exp (ε * t) * Real.exp ((η - ε) * s) = G t - G 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hG s) (hc.intervalIntegrable _ _)
    have hle := intervalIntegral.norm_integral_le_of_norm_le ht
      (ae_of_all volume fun s (hs : s ∈ Ioc 0 t) => by
        have h1 := hb s
        rw [abs_of_nonneg (sub_nonneg.2 hs.2), abs_of_nonneg hs.1.le] at h1
        exact h1.trans_eq (exp_mul_exp_eq (by ring)))
      (hc.intervalIntegrable _ _)
    rw [hint] at hle
    refine hle.trans ?_
    have hG0 : 0 ≤ G 0 := by positivity
    have hGt : G t = M * Real.exp (η * |t|) / (η - ε) := by
      simp only [G, abs_of_nonneg ht]
      rw [mul_assoc, ← Real.exp_add, show ε * t + (η - ε) * t = η * t by ring]
    linarith
  · -- `s ∈ [t, 0]`: the bound is `M e^{−εt} e^{(ε−η)s}`.
    set G : ℝ → ℝ := fun s => M * Real.exp (-(ε * t)) * Real.exp ((ε - η) * s) / (ε - η)
    have hc : Continuous fun s => M * Real.exp (-(ε * t)) * Real.exp ((ε - η) * s) := by
      fun_prop
    have hne : ε - η ≠ 0 := by linarith
    have hG : ∀ s, HasDerivAt G (M * Real.exp (-(ε * t)) * Real.exp ((ε - η) * s)) s := by
      intro s
      have h := ((((hasDerivAt_id' s).const_mul (ε - η)).exp).const_mul
        (M * Real.exp (-(ε * t)))).div_const (ε - η)
      refine h.congr_deriv ?_
      field_simp
    have hint : ∫ s in t..0, M * Real.exp (-(ε * t)) * Real.exp ((ε - η) * s) = G 0 - G t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hG s) (hc.intervalIntegrable _ _)
    have hle := intervalIntegral.norm_integral_le_of_norm_le ht
      (ae_of_all volume fun s (hs : s ∈ Ioc t 0) => by
        have h1 := hb s
        rw [abs_of_nonpos (sub_nonpos.2 hs.1.le), abs_of_nonpos hs.2] at h1
        exact h1.trans_eq (exp_mul_exp_eq (by ring)))
      (hc.intervalIntegrable _ _)
    rw [hint] at hle
    rw [intervalIntegral.integral_symm, norm_neg]
    refine hle.trans ?_
    have hG0 : G 0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hGt : -G t = M * Real.exp (η * |t|) / (η - ε) := by
      simp only [G, abs_of_nonpos ht]
      rw [mul_assoc, ← Real.exp_add, show -(ε * t) + (ε - η) * t = η * -t by ring,
        ← neg_sub η ε, div_neg, neg_neg]
    linarith

omit [CompleteSpace E] in
/-- The stable estimate on `(−∞, t]`: a continuous integrand bounded by
`M e^{−β(t−s)} e^{η|s|}` is integrable, with integral at most `2 M e^{η|t|}/(β − η)`. -/
@[tmio T, powerlib_foundation] theorem integrableOn_Iic_stable {F : ℝ → E} {M η β t : ℝ}
    (hF : Continuous F) (hM : 0 ≤ M) (hη : 0 ≤ η) (hηβ : η < β)
    (hb : ∀ s ≤ t, ‖F s‖ ≤ M * Real.exp (-(β * (t - s))) * Real.exp (η * |s|)) :
    IntegrableOn F (Iic t) ∧ ‖∫ s in Iic t, F s‖ ≤ 2 * M * Real.exp (η * |t|) / (β - η) := by
  have hd : 0 < β - η := sub_pos.2 hηβ
  have hs : 0 < β + η := by linarith
  set g : ℝ → ℝ := fun s => M * Real.exp (-(β * t)) *
    (Real.exp ((β + η) * s) + Real.exp ((β - η) * s))
  have hgi : IntegrableOn g (Iic t) :=
    ((integrableOn_exp_mul_Iic hs t).add (integrableOn_exp_mul_Iic hd t)).const_mul _
  have hFg : ∀ s ∈ Iic t, ‖F s‖ ≤ g s := by
    intro s hst
    have habs : Real.exp (η * |s|) ≤ Real.exp (η * s) + Real.exp (-(η * s)) := by
      rcases abs_cases s with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]; linarith [Real.exp_pos (-(η * s))]
      · rw [h1, mul_neg]; linarith [Real.exp_pos (η * s)]
    calc ‖F s‖ ≤ M * Real.exp (-(β * (t - s))) * Real.exp (η * |s|) := hb s hst
      _ ≤ M * Real.exp (-(β * (t - s))) * (Real.exp (η * s) + Real.exp (-(η * s))) := by
          gcongr
      _ = g s := by
          simp only [g, mul_add, mul_assoc, ← Real.exp_add]; ring_nf
  have hFi : IntegrableOn F (Iic t) :=
    hgi.mono' hF.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Iic hFg)
  refine ⟨hFi, ?_⟩
  have hle : ‖∫ s in Iic t, F s‖ ≤ ∫ s in Iic t, g s :=
    norm_integral_le_of_norm_le hgi (ae_restrict_of_forall_mem measurableSet_Iic hFg)
  have h1 : Real.exp (η * t) ≤ Real.exp (η * |t|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_abs_self t) hη)
  have h2 : Real.exp (-(η * t)) ≤ Real.exp (η * |t|) :=
    Real.exp_le_exp.2 (by rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs t) hη)
  have h3 : Real.exp (η * t) / (β + η) ≤ Real.exp (η * |t|) / (β - η) :=
    div_le_div₀ (Real.exp_pos _).le h1 hd (by linarith)
  have h4 : Real.exp (-(η * t)) / (β - η) ≤ Real.exp (η * |t|) / (β - η) :=
    div_le_div_of_nonneg_right h2 hd.le
  calc ‖∫ s in Iic t, F s‖ ≤ ∫ s in Iic t, g s := hle
    _ = M * (Real.exp (η * t) / (β + η) + Real.exp (-(η * t)) / (β - η)) := by
      simp only [g]
      rw [integral_const_mul, integral_add (integrableOn_exp_mul_Iic hs t)
        (integrableOn_exp_mul_Iic hd t), integral_exp_mul_Iic hs, integral_exp_mul_Iic hd,
        mul_assoc, mul_add, mul_div_assoc', mul_div_assoc', ← Real.exp_add, ← Real.exp_add,
        show -(β * t) + (β + η) * t = η * t by ring,
        show -(β * t) + (β - η) * t = -(η * t) by ring]
    _ ≤ M * (Real.exp (η * |t|) / (β - η) + Real.exp (η * |t|) / (β - η)) := by gcongr
    _ = 2 * M * Real.exp (η * |t|) / (β - η) := by ring

/-! ## The Lyapunov–Perron transform -/

/-- The stable initial value `∫_{−∞}^0 e^{−sA}(1 − P) b(s) ds` of the Lyapunov–Perron
transform. -/
def stableInit (A P : E →L[ℝ] E) (b : ℝ → E) : E :=
  ∫ s in Iic 0, expFlow A (-s) ((1 - P) (b s))

/-- The Lyapunov–Perron transform with centre datum `u` and forcing `b`:
`t ↦ e^{tA}(P u + stableInit b + ∫₀ᵗ e^{−sA} b(s) ds)`, the solution of `ẋ = A x + b` whose
centre component starts at `P u` and whose stable component starts at `stableInit b`. -/
def lpMap (A P : E →L[ℝ] E) (u : E) (b : ℝ → E) (t : ℝ) : E :=
  expFlow A t (P u + stableInit A P b + ∫ s in (0)..t, expFlow A (-s) (b s))

section Dichotomy

variable {K ε β η C : ℝ}

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem nonneg_of_stable_bound
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) : 0 ≤ K := by
  have h := (norm_nonneg _).trans (hst 0 le_rfl)
  simpa using h

/-- Under the stable bound, `s ↦ e^{(t−s)A}(1 − P) b(s)` is integrable on `(−∞, t]` with
integral at most `2 K C e^{η|t|}/(β − η)`. -/
@[tmio T, powerlib_foundation] theorem integrableOn_stable {b : ℝ → E} (hb : Continuous b)
    (hC : 0 ≤ C) (hbC : ∀ s, ‖b s‖ ≤ C * Real.exp (η * |s|)) (hη : 0 ≤ η) (hηβ : η < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) (t : ℝ) :
    IntegrableOn (fun s => expFlow A (t - s) ((1 - P) (b s))) (Iic t) ∧
      ‖∫ s in Iic t, expFlow A (t - s) ((1 - P) (b s))‖ ≤
        2 * (K * C) * Real.exp (η * |t|) / (β - η) := by
  have hK := nonneg_of_stable_bound hst
  refine integrableOn_Iic_stable
    ((continuous_expFlow.comp (continuous_const.sub continuous_id)).clm_apply
      ((1 - P).continuous.comp hb)) (mul_nonneg hK hC) hη hηβ fun s hs => ?_
  calc ‖expFlow A (t - s) ((1 - P) (b s))‖ = ‖(expFlow A (t - s) * (1 - P)) (b s)‖ := rfl
    _ ≤ ‖expFlow A (t - s) * (1 - P)‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * Real.exp (-(β * (t - s))) * (C * Real.exp (η * |s|)) :=
        mul_le_mul (hst _ (sub_nonneg.2 hs)) (hbC s) (norm_nonneg _)
          (mul_nonneg hK (Real.exp_pos _).le)
    _ = K * C * Real.exp (-(β * (t - s))) * Real.exp (η * |s|) := by ring

/-- The integrand of `stableInit` is integrable on every `(−∞, t]`. -/
@[tmio T, powerlib_foundation] theorem integrableOn_stableInit {b : ℝ → E} (hb : Continuous b)
    (hC : 0 ≤ C) (hbC : ∀ s, ‖b s‖ ≤ C * Real.exp (η * |s|)) (hη : 0 ≤ η) (hηβ : η < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) (t : ℝ) :
    IntegrableOn (fun s => expFlow A (-s) ((1 - P) (b s))) (Iic t) := by
  have h := ((expFlow A (-t)).integrable_comp (integrableOn_stable hb hC hbC hη hηβ hst t).1)
  have he : (fun s => expFlow A (-s) ((1 - P) (b s))) =
      fun s => expFlow A (-t) (expFlow A (t - s) ((1 - P) (b s))) := by
    funext s; rw [expFlow_apply_apply]; ring_nf
  rw [he]; exact h

@[tmio T, powerlib_foundation] theorem continuous_expFlow_neg_apply {b : ℝ → E}
    (hb : Continuous b) : Continuous fun s => expFlow A (-s) (b s) :=
  (continuous_expFlow.comp continuous_neg).clm_apply hb

/-- The transform solves `ẋ = A x + b`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_lpMap {b : ℝ → E} (hb : Continuous b) (u : E)
    (t : ℝ) : HasDerivAt (lpMap A P u b) (A (lpMap A P u b t) + b t) t := by
  have hY := ((continuous_expFlow_neg_apply (A := A) hb).integral_hasStrictDerivAt 0
    t).hasDerivAt.const_add (P u + stableInit A P b)
  have h := (hasDerivAt_expFlow (A := A) t).clm_apply hY
  refine h.congr_deriv ?_
  rw [expFlow_mul_comm, expFlow_apply_neg_apply]
  rfl

@[tmio T, powerlib_foundation] theorem continuous_lpMap {b : ℝ → E} (hb : Continuous b) (u : E) :
    Continuous (lpMap A P u b) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_lpMap hb u t).continuousAt

/-- The transform as the sum of its centre and stable parts. -/
@[tmio T, powerlib_foundation] theorem lpMap_eq {b : ℝ → E} (hb : Continuous b) (hC : 0 ≤ C)
    (hbC : ∀ s, ‖b s‖ ≤ C * Real.exp (η * |s|)) (hη : 0 ≤ η) (hηβ : η < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) (u : E) (t : ℝ) :
    lpMap A P u b t = expFlow A t (P u) + (∫ s in (0)..t, expFlow A (t - s) (P (b s))) +
      ∫ s in Iic t, expFlow A (t - s) ((1 - P) (b s)) := by
  have hI0 := integrableOn_stableInit hb hC hbC hη hηβ hst 0
  have hIt := (integrableOn_stable hb hC hbC hη hηβ hst t).1
  have hI0' : IntegrableOn (fun s => expFlow A (t - s) ((1 - P) (b s))) (Iic 0) := by
    have he : (fun s => expFlow A (t - s) ((1 - P) (b s))) =
        fun s => expFlow A t (expFlow A (-s) ((1 - P) (b s))) := by
      funext s; rw [expFlow_apply_apply]; ring_nf
    rw [he]; exact (expFlow A t).integrable_comp hI0
  have hcP : Continuous fun s => expFlow A (t - s) (P (b s)) :=
    (continuous_expFlow.comp (continuous_const.sub continuous_id)).clm_apply (P.continuous.comp hb)
  have hcQ : Continuous fun s => expFlow A (t - s) ((1 - P) (b s)) :=
    (continuous_expFlow.comp (continuous_const.sub continuous_id)).clm_apply
      ((1 - P).continuous.comp hb)
  have hstab : expFlow A t (stableInit A P b) =
      ∫ s in Iic 0, expFlow A (t - s) ((1 - P) (b s)) := by
    rw [stableInit, ← (expFlow A t).integral_comp_comm hI0]
    congr 1; funext s; rw [expFlow_apply_apply]; ring_nf
  have hint : expFlow A t (∫ s in (0)..t, expFlow A (-s) (b s)) =
      (∫ s in (0)..t, expFlow A (t - s) (P (b s))) +
        ∫ s in (0)..t, expFlow A (t - s) ((1 - P) (b s)) := by
    rw [← (expFlow A t).intervalIntegral_comp_comm
      ((continuous_expFlow_neg_apply hb).intervalIntegrable _ _),
      ← intervalIntegral.integral_add (hcP.intervalIntegrable _ _) (hcQ.intervalIntegrable _ _)]
    congr 1; funext s
    rw [expFlow_apply_apply, ← map_add, sub_apply, one_apply_eq_self, add_sub_cancel]
    ring_nf
  rw [lpMap, map_add, map_add, hstab, hint, ← intervalIntegral.integral_Iic_sub_Iic hI0' hIt]
  abel

/-- The constant `κ = 1/(η − ε) + 2/(β − η)` of the weighted estimate. -/
def gapConst (ε η β : ℝ) : ℝ := 1 / (η - ε) + 2 / (β - η)

@[tmio T, powerlib_foundation] theorem gapConst_pos {ε η β : ℝ} (hεη : ε < η) (hηβ : η < β) :
    0 < gapConst ε η β := by
  have h1 : 0 < η - ε := sub_pos.2 hεη
  have h2 : 0 < β - η := sub_pos.2 hηβ
  unfold gapConst; positivity

/-- The weighted estimate: `‖lpMap u b t‖ ≤ K (‖u‖ + C κ) e^{η|t|}` when
`‖b(s)‖ ≤ C e^{η|s|}`. -/
@[tmio T, powerlib_foundation] theorem norm_lpMap_le {b : ℝ → E} (hb : Continuous b)
    (hC : 0 ≤ C) (hbC : ∀ s, ‖b s‖ ≤ C * Real.exp (η * |s|)) (hε : 0 ≤ ε) (hεη : ε < η)
    (hηβ : η < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) (u : E) (t : ℝ) :
    ‖lpMap A P u b t‖ ≤ K * (‖u‖ + C * gapConst ε η β) * Real.exp (η * |t|) := by
  have hη : 0 ≤ η := hε.trans hεη.le
  have hK := nonneg_of_stable_bound hst
  rw [lpMap_eq hb hC hbC hη hηβ hst u t]
  have h1 : ‖expFlow A t (P u)‖ ≤ K * Real.exp (η * |t|) * ‖u‖ :=
    calc ‖expFlow A t (P u)‖ = ‖(expFlow A t * P) u‖ := rfl
      _ ≤ ‖expFlow A t * P‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (η * |t|) * ‖u‖ := by
        gcongr
        refine (hcen t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK)
        exact mul_le_mul_of_nonneg_right hεη.le (abs_nonneg t)
  have h2 : ‖∫ s in (0)..t, expFlow A (t - s) (P (b s))‖ ≤
      K * C * Real.exp (η * |t|) / (η - ε) := by
    refine norm_integral_le_center (mul_nonneg hK hC) hεη fun s => ?_
    calc ‖expFlow A (t - s) (P (b s))‖ = ‖(expFlow A (t - s) * P) (b s)‖ := rfl
      _ ≤ ‖expFlow A (t - s) * P‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (ε * |t - s|) * (C * Real.exp (η * |s|)) :=
          mul_le_mul (hcen _) (hbC s) (norm_nonneg _) (mul_nonneg hK (Real.exp_pos _).le)
      _ = K * C * Real.exp (ε * |t - s|) * Real.exp (η * |s|) := by ring
  have h3 := (integrableOn_stable hb hC hbC hη hηβ hst t).2
  calc _ ≤ ‖expFlow A t (P u)‖ + ‖∫ s in (0)..t, expFlow A (t - s) (P (b s))‖ +
        ‖∫ s in Iic t, expFlow A (t - s) ((1 - P) (b s))‖ := norm_add₃_le
    _ ≤ K * Real.exp (η * |t|) * ‖u‖ + K * C * Real.exp (η * |t|) / (η - ε) +
        2 * (K * C) * Real.exp (η * |t|) / (β - η) := by gcongr
    _ = K * (‖u‖ + C * gapConst ε η β) * Real.exp (η * |t|) := by
        unfold gapConst; ring

/-- The transform is affine in its data. -/
@[tmio T, powerlib_foundation] theorem lpMap_sub {b₁ b₂ : ℝ → E} {C₁ C₂ : ℝ}
    (hb₁ : Continuous b₁) (hb₂ : Continuous b₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbC₁ : ∀ s, ‖b₁ s‖ ≤ C₁ * Real.exp (η * |s|)) (hbC₂ : ∀ s, ‖b₂ s‖ ≤ C₂ * Real.exp (η * |s|))
    (hη : 0 ≤ η) (hηβ : η < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) (u v : E) (t : ℝ) :
    lpMap A P u b₁ t - lpMap A P v b₂ t = lpMap A P (u - v) (fun s => b₁ s - b₂ s) t := by
  have hs : stableInit A P (fun s => b₁ s - b₂ s) = stableInit A P b₁ - stableInit A P b₂ := by
    unfold stableInit
    rw [← integral_sub (integrableOn_stableInit hb₁ hC₁ hbC₁ hη hηβ hst 0)
      (integrableOn_stableInit hb₂ hC₂ hbC₂ hη hηβ hst 0)]
    congr 1; funext s; rw [map_sub, map_sub]
  have hi : (∫ s in (0)..t, expFlow A (-s) (b₁ s - b₂ s)) =
      (∫ s in (0)..t, expFlow A (-s) (b₁ s)) - ∫ s in (0)..t, expFlow A (-s) (b₂ s) := by
    rw [← intervalIntegral.integral_sub
      ((continuous_expFlow_neg_apply hb₁).intervalIntegrable _ _)
      ((continuous_expFlow_neg_apply hb₂).intervalIntegrable _ _)]
    congr 1; funext s; rw [map_sub]
  unfold lpMap
  rw [hs, hi, ← map_sub, map_sub P]
  congr 1; abel

/-- A bound improved by a contraction at every step is the fixed bound `M/(1 − k)`. -/
@[tmio T, powerlib_foundation] theorem le_of_contract {ι : Type*} {a w : ι → ℝ} {k M Z₀ : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (h0 : ∀ i, a i ≤ Z₀ * w i)
    (step : ∀ Z, (∀ i, a i ≤ Z * w i) → ∀ i, a i ≤ (k * Z + M) * w i) :
    ∀ i, a i ≤ M / (1 - k) * w i := by
  set c := M / (1 - k)
  have hc : k * c + M = c := by
    have : (1 - k) ≠ 0 := by linarith
    simp only [c]; field_simp; ring
  have hm : ∀ m : ℕ, ∀ i, a i ≤ (c + k ^ m * (Z₀ - c)) * w i := by
    intro m
    induction m with
    | zero => simpa using h0
    | succ m ih =>
      intro i
      have := step _ ih i
      calc a i ≤ (k * (c + k ^ m * (Z₀ - c)) + M) * w i := this
        _ = (c + k ^ (m + 1) * (Z₀ - c)) * w i := by linear_combination (w i) * hc
  intro i
  have ht : Tendsto (fun m : ℕ => (c + k ^ m * (Z₀ - c)) * w i) atTop
      (𝓝 ((c + 0 * (Z₀ - c)) * w i)) :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const (Z₀ - c)).const_add c).mul_const _
  simpa using ge_of_tendsto' ht fun m => hm m i

end Dichotomy

/-! ## The fixed point -/

section FixedPoint

variable {K ε β η : ℝ} {g : E → E} {δ : NNReal}

@[tmio T, powerlib_foundation] theorem continuous_weight (η : ℝ) :
    Continuous fun t : ℝ => Real.exp (η * |t|) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_abs)

/-- Existence of a fixed point `x = lpMap u (g ∘ x)` of weighted growth `e^{η|t|}`, by the
contraction principle in the space of bounded continuous functions `y = e^{−η|t|} x`. -/
@[tmio T, powerlib_foundation] theorem exists_fixedPoint (hε : 0 ≤ ε) (hεη : ε < η)
    (hηβ : η < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hg : LipschitzWith δ g) (hg0 : g 0 = 0) (hk : K * δ * gapConst ε η β < 1) (u : E) :
    ∃ x : ℝ → E, Continuous x ∧ (∃ C, 0 ≤ C ∧ ∀ t, ‖x t‖ ≤ C * Real.exp (η * |t|)) ∧
      ∀ t, x t = lpMap A P u (fun s => g (x s)) t := by
  have hK := nonneg_of_stable_bound hst
  have hκ := (gapConst_pos hεη hηβ).le
  set κ := gapConst ε η β
  let W : (BoundedContinuousFunction ℝ E) → ℝ → E := fun y t => Real.exp (η * |t|) • y t
  have hWc : ∀ y, Continuous (W y) := fun y => (continuous_weight η).smul y.continuous
  have hWb : ∀ y t, ‖W y t‖ ≤ ‖y‖ * Real.exp (η * |t|) := by
    intro y t
    simp only [W, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (y.norm_coe_le_norm t) (Real.exp_pos _).le
  have hgc : ∀ y, Continuous fun s => g (W y s) := fun y => hg.continuous.comp (hWc y)
  have hgb : ∀ y s, ‖g (W y s)‖ ≤ (δ * ‖y‖) * Real.exp (η * |s|) := by
    intro y s
    calc ‖g (W y s)‖ ≤ δ * ‖W y s‖ := hg.norm_le_mul hg0 _
      _ ≤ δ * (‖y‖ * Real.exp (η * |s|)) := by gcongr; exact hWb y s
      _ = _ := by ring
  let F : (BoundedContinuousFunction ℝ E) → ℝ → E := fun y t =>
    Real.exp (-(η * |t|)) • lpMap A P u (fun s => g (W y s)) t
  have hFc : ∀ y, Continuous (F y) := fun y =>
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg).smul
      (continuous_lpMap (hgc y) u)
  have hcancel : ∀ t, Real.exp (-(η * |t|)) * Real.exp (η * |t|) = 1 := fun t => by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hFb : ∀ y t, ‖F y t‖ ≤ K * (‖u‖ + δ * ‖y‖ * κ) := by
    intro y t
    have h := norm_lpMap_le (hgc y) (by positivity) (hgb y) hε hεη hηβ hcen hst u t
    simp only [F, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (-(η * |t|)) * (K * (‖u‖ + δ * ‖y‖ * κ) * Real.exp (η * |t|)) := by
          gcongr
      _ = K * (‖u‖ + δ * ‖y‖ * κ) := by
          rw [mul_comm, mul_assoc, mul_comm (Real.exp _), hcancel, mul_one]
  let S : (BoundedContinuousFunction ℝ E) → (BoundedContinuousFunction ℝ E) := fun y =>
    BoundedContinuousFunction.ofNormedAddCommGroup (F y) (hFc y) _ (hFb y)
  have hS : ContractingWith ⟨K * δ * κ, by positivity⟩ S := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_⟩
    change dist (S y₁) (S y₂) ≤ (K * δ * κ) * dist y₁ y₂
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro t
    have hd : ∀ s, ‖g (W y₁ s) - g (W y₂ s)‖ ≤ (δ * dist y₁ y₂) * Real.exp (η * |s|) := by
      intro s
      calc ‖g (W y₁ s) - g (W y₂ s)‖ ≤ δ * ‖W y₁ s - W y₂ s‖ := by
            simpa [dist_eq_norm] using hg.dist_le_mul (W y₁ s) (W y₂ s)
        _ = δ * (Real.exp (η * |s|) * dist (y₁ s) (y₂ s)) := by
            simp only [W, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              dist_eq_norm]
        _ ≤ δ * (Real.exp (η * |s|) * dist y₁ y₂) := by
            gcongr; exact BoundedContinuousFunction.dist_coe_le_dist s
        _ = _ := by ring
    have hsub := lpMap_sub (A := A) (P := P) (b₁ := fun s => g (W y₁ s))
      (b₂ := fun s => g (W y₂ s)) (hgc y₁) (hgc y₂) (by positivity) (by positivity)
      (hgb y₁) (hgb y₂) (hε.trans hεη.le) hηβ hst u u t
    have hbd := norm_lpMap_le (A := A) (P := P) (b := fun s => g (W y₁ s) - g (W y₂ s))
      ((hgc y₁).sub (hgc y₂)) (by positivity) hd hε hεη hηβ hcen hst (u - u) t
    change dist (F y₁ t) (F y₂ t) ≤ _
    rw [dist_eq_norm]
    simp only [F, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hsub]
    calc _ ≤ Real.exp (-(η * |t|)) *
          (K * (‖u - u‖ + δ * dist y₁ y₂ * κ) * Real.exp (η * |t|)) := by gcongr
      _ = K * δ * κ * dist y₁ y₂ := by
          rw [sub_self, norm_zero, zero_add, mul_comm, mul_assoc, mul_comm (Real.exp _),
            hcancel]; ring
  set y := ContractingWith.fixedPoint S hS
  have hy : S y = y := hS.fixedPoint_isFixedPt
  refine ⟨W y, hWc y, ⟨‖y‖, norm_nonneg _, hWb y⟩, fun t => ?_⟩
  have h := congrArg (fun z : BoundedContinuousFunction ℝ E => z t) hy
  change Real.exp (-(η * |t|)) • lpMap A P u (fun s => g (W y s)) t = y t at h
  change Real.exp (η * |t|) • y t = _
  rw [← h, smul_smul, mul_comm, hcancel, one_smul]

/-- Fixed points depend Lipschitz-continuously on the centre datum:
`‖x_u(t) − x_v(t)‖ ≤ K ‖u − v‖ e^{η|t|}/(1 − Kδκ)`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_fixedPoint_le (hε : 0 ≤ ε) (hεη : ε < η)
    (hηβ : η < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hg : LipschitzWith δ g) (hg0 : g 0 = 0) (hk : K * δ * gapConst ε η β < 1) {u v : E}
    {x y : ℝ → E} (hxc : Continuous x) (hyc : Continuous y) {Cx Cy : ℝ}
    (hxb : ∀ t, ‖x t‖ ≤ Cx * Real.exp (η * |t|)) (hyb : ∀ t, ‖y t‖ ≤ Cy * Real.exp (η * |t|))
    (hx : ∀ t, x t = lpMap A P u (fun s => g (x s)) t)
    (hy : ∀ t, y t = lpMap A P v (fun s => g (y s)) t) (t : ℝ) :
    ‖x t - y t‖ ≤ K * ‖u - v‖ / (1 - K * δ * gapConst ε η β) * Real.exp (η * |t|) := by
  have hK := nonneg_of_stable_bound hst
  have hη : 0 ≤ η := hε.trans hεη.le
  have hκ := (gapConst_pos hεη hηβ).le
  have hCx : 0 ≤ Cx := by
    have := (norm_nonneg _).trans (hxb 0); simpa using this
  have hCy : 0 ≤ Cy := by
    have := (norm_nonneg _).trans (hyb 0); simpa using this
  have hgx : ∀ s, ‖g (x s)‖ ≤ (δ * Cx) * Real.exp (η * |s|) := fun s =>
    (hg.norm_le_mul hg0 _).trans (by rw [mul_assoc]; gcongr; exact hxb s)
  have hgy : ∀ s, ‖g (y s)‖ ≤ (δ * Cy) * Real.exp (η * |s|) := fun s =>
    (hg.norm_le_mul hg0 _).trans (by rw [mul_assoc]; gcongr; exact hyb s)
  refine le_of_contract (a := fun t => ‖x t - y t‖) (w := fun t => Real.exp (η * |t|))
    (k := K * δ * gapConst ε η β) (Z₀ := Cx + Cy) (by positivity) hk
    (fun t => (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (hxb t) (hyb t)))
    (fun Z hZ t => ?_) t
  have hZ0 : 0 ≤ Z := by
    have := (norm_nonneg _).trans (hZ 0); simpa using this
  have hd : ∀ s, ‖g (x s) - g (y s)‖ ≤ (δ * Z) * Real.exp (η * |s|) := by
    intro s
    calc ‖g (x s) - g (y s)‖ ≤ δ * ‖x s - y s‖ := by
          simpa [dist_eq_norm] using hg.dist_le_mul (x s) (y s)
      _ ≤ δ * (Z * Real.exp (η * |s|)) := by gcongr; exact hZ s
      _ = _ := by ring
  have hsub := lpMap_sub (A := A) (P := P) (b₁ := fun s => g (x s)) (b₂ := fun s => g (y s))
    (hg.continuous.comp hxc) (hg.continuous.comp hyc)
    (by positivity) (by positivity) hgx hgy hη hηβ hst u v t
  have hbd := norm_lpMap_le (A := A) (P := P) (b := fun s => g (x s) - g (y s))
    ((hg.continuous.comp hxc).sub (hg.continuous.comp hyc)) (by positivity) hd hε hεη hηβ hcen
    hst (u - v) t
  change ‖x t - y t‖ ≤ (K * δ * gapConst ε η β * Z + K * ‖u - v‖) * Real.exp (η * |t|)
  rw [hx t, hy t, hsub]
  refine hbd.trans_eq ?_
  ring

/-- Uniqueness of the fixed point among functions of weighted growth `e^{η|t|}`. -/
@[tmio T, powerlib_foundation] theorem fixedPoint_unique (hε : 0 ≤ ε) (hεη : ε < η)
    (hηβ : η < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hg : LipschitzWith δ g) (hg0 : g 0 = 0) (hk : K * δ * gapConst ε η β < 1) {u : E}
    {x y : ℝ → E} (hxc : Continuous x) (hyc : Continuous y) {Cx Cy : ℝ}
    (hxb : ∀ t, ‖x t‖ ≤ Cx * Real.exp (η * |t|)) (hyb : ∀ t, ‖y t‖ ≤ Cy * Real.exp (η * |t|))
    (hx : ∀ t, x t = lpMap A P u (fun s => g (x s)) t)
    (hy : ∀ t, y t = lpMap A P u (fun s => g (y s)) t) : x = y := by
  funext t
  have h := norm_sub_fixedPoint_le hε hεη hηβ hcen hst hg hg0 hk hxc hyc hxb hyb hx hy t
  rw [sub_self, norm_zero, mul_zero, zero_div, zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

end FixedPoint

/-! ## Solutions of weighted growth are Lyapunov–Perron transforms -/

section Solutions

variable {K β η C : ℝ}

@[tmio T, powerlib_foundation] theorem hasDerivAt_expFlow_neg_apply {x : ℝ → E} {x' : E}
    {s : ℝ} (hx : HasDerivAt x x' s) :
    HasDerivAt (fun s => expFlow A (-s) (x s)) (expFlow A (-s) (x' - A (x s))) s := by
  have h1 : HasDerivAt (fun s => expFlow A (-s)) (-(expFlow A (-s) * A)) s := by
    have := (hasDerivAt_expFlow (A := A) (-s)).scomp s (hasDerivAt_neg s)
    rw [neg_one_smul] at this
    exact this
  refine (h1.clm_apply hx).congr_deriv ?_
  rw [map_sub]
  change -(expFlow A (-s) (A (x s))) + expFlow A (-s) x' = _
  abel

/-- **Variation of constants on the whole line.** A solution of `ẋ = A x + b(t)` of weighted
growth `e^{η|t|}` with forcing of the same growth is the Lyapunov–Perron transform of its own
initial value: its stable component at `0` is `stableInit b`. -/
@[tmio T, powerlib_foundation] theorem eq_lpMap_of_hasDerivAt (hAP : Commute A P) (hη : 0 ≤ η)
    (hηβ : η < β) (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {x b : ℝ → E} (hb : Continuous b) (hC : 0 ≤ C) (hbC : ∀ s, ‖b s‖ ≤ C * Real.exp (η * |s|))
    {C' : ℝ} (hxC : ∀ s, ‖x s‖ ≤ C' * Real.exp (η * |s|))
    (hx : ∀ t, HasDerivAt x (A (x t) + b t) t) (t : ℝ) : x t = lpMap A P (x 0) b t := by
  have hK := nonneg_of_stable_bound hst
  have hz : ∀ s, HasDerivAt (fun s => expFlow A (-s) (x s)) (expFlow A (-s) (b s)) s := by
    intro s
    refine (hasDerivAt_expFlow_neg_apply (hx s)).congr_deriv ?_
    rw [add_sub_cancel_left]
  have hftc : ∀ a c, ∫ s in a..c, expFlow A (-s) (b s) =
      expFlow A (-c) (x c) - expFlow A (-a) (x a) := fun a c =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hz s)
      ((continuous_expFlow_neg_apply hb).intervalIntegrable _ _)
  have hQc : Commute A (1 - P) := (Commute.one_right A).sub_right hAP
  have hcomm : ∀ s y, (1 - P) (expFlow A s y) = expFlow A s ((1 - P) y) := fun s y => by
    change ((1 - P) * expFlow A s) y = (expFlow A s * (1 - P)) y
    rw [(expFlow_commute hQc s).eq]
  have h00 : expFlow A (-0) (x 0) = x 0 := by rw [neg_zero, expFlow_zero]; rfl
  have key : ∀ a, (1 - P) (x 0) = expFlow A (-a) ((1 - P) (x a)) +
      ∫ s in a..0, expFlow A (-s) ((1 - P) (b s)) := by
    intro a
    have hcont : Continuous fun s => expFlow A (-s) (b s) := continuous_expFlow_neg_apply hb
    have hint : (1 - P) (∫ s in a..0, expFlow A (-s) (b s)) =
        ∫ s in a..0, expFlow A (-s) ((1 - P) (b s)) := by
      rw [← (1 - P).intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)]
      congr 1; funext s; rw [hcomm]
    rw [← hint, hftc, h00, map_sub, hcomm]
    abel
  have hlim1 : Tendsto (fun a => expFlow A (-a) ((1 - P) (x a))) atBot (𝓝 0) := by
    have hd : 0 < β - η := sub_pos.2 hηβ
    have ht : Tendsto (fun a : ℝ => K * C' * Real.exp ((β - η) * a)) atBot (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hd)).const_mul (K * C')
      simpa using this
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_le_atBot 0] with a ha
    calc ‖expFlow A (-a) ((1 - P) (x a))‖ = ‖(expFlow A (-a) * (1 - P)) (x a)‖ := rfl
      _ ≤ ‖expFlow A (-a) * (1 - P)‖ * ‖x a‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (-(β * -a)) * (C' * Real.exp (η * |a|)) :=
          mul_le_mul (hst _ (neg_nonneg.2 ha)) (hxC a) (norm_nonneg _)
            (mul_nonneg hK (Real.exp_pos _).le)
      _ = K * C' * Real.exp ((β - η) * a) := by
          rw [abs_of_nonpos ha, mul_mul_mul_comm, ← Real.exp_add]; ring_nf
  have hlim2 : Tendsto (fun a => ∫ s in a..0, expFlow A (-s) ((1 - P) (b s))) atBot
      (𝓝 (stableInit A P b)) :=
    intervalIntegral_tendsto_integral_Iic 0
      (integrableOn_stableInit hb hC hbC hη hηβ hst 0) tendsto_id
  have hQ : (1 - P) (x 0) = stableInit A P b := by
    have h := hlim1.add hlim2
    rw [zero_add] at h
    exact tendsto_nhds_unique (tendsto_const_nhds.congr key) h
  have hxt : x t = expFlow A t (x 0 + ∫ s in (0)..t, expFlow A (-s) (b s)) := by
    rw [hftc, h00, add_sub_cancel, expFlow_apply_neg_apply]
  rw [hxt, lpMap, ← hQ]
  congr 2
  rw [sub_apply, one_apply_eq_self]
  abel

end Solutions

end powerlib.Dynamics.LyapunovPerron
