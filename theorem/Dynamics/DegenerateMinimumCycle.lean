import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Degenerate strict minima of a cycle potential (foundation)

Model boundary. Pure static analysis of real functions; no dynamics, no model family. A cycle of
`m + 1` lines is described by line data `(Wₑ, fₑ)` (weight `W = B cos φ`, flow `f = B sin φ`,
amplitude `B = √(W² + f²)`). On closed-loop angle increments `x` (`∑ₑ xₑ = 0`) the cycle potential
is `∑ₑ Gₑ(xₑ)` with `G(x) = W (1 − cos x) + f (sin x − x)` (`edgeG`), the line potential increment
`B[cos φ − cos(φ + x) − x sin φ]` of a lossless line, and its critical points are the points with
equal flow increments `G'(x) = W sin x + f (cos x − 1)` (`edgeD`) on every line.

Results.
* Per line: `hasDerivAt_edgeG`, `hasDerivAt_edgeD`, the inverse flow increments `invPos` (positive
  weight) and `invNeg` (negative weight) with `edgeD_invPos`, `edgeD_invNeg`, `invPos_edgeD`,
  `invNeg_edgeD`, their derivatives `±1/√(W² − 2fμ − μ²)` (`hasDerivAt_invPos`,
  `hasDerivAt_invNeg`), and the supporting line of a positive-weight line potential
  (`edgeG_tangent`, mean value theorem).
* `cycle_strictMin`: if line `0` has negative weight, the others positive weight, and
  `∑ᵢ 1/√qᵢ(μ) < 1/√q₀(μ)` for `0 < |μ| ≤ ρ` (`qₑ(μ) = Wₑ² − 2fₑμ − μ²`), then `0` is a strict local
  minimum and an isolated critical point of the cycle potential. The Hessian at `0` may be
  singular (`∑ₑ 1/Wₑ = 0`). Proof: along the critical curve `xₑ = Xₑ(μ)` the closing angle
  `closure` decreases strictly (`closure_sign`) and the curve potential `curvePot` (derivative
  `−closure`) is positive (`curvePot_pos`); supporting lines bound the potential below by
  `curvePot` at `μ = G₀'(x₀)`.

Connection architecture. Foundation only: `theorem/Network/SwingDegenerateRing.lean` applies it to a
swing network whose coupling graph is a cycle.

Source: elementary calculus (mean value theorem, inverse sine); the loop-flow parametrization of
cycle equilibria follows the lossless power-flow literature (e.g. the winding-cell analysis of
meshed networks).
-/

noncomputable section
namespace powerlib.Dynamics.CycleMinimum
open Set Real

/-- Potential increment of one line, `G(x) = W (1 − cos x) + f (sin x − x)` (weight `W = B cos φ`,
flow `f = B sin φ`). -/
def edgeG (W f x : ℝ) : ℝ := W * (1 - Real.cos x) + f * (Real.sin x - x)

/-- Flow increment of one line, `G'(x) = W sin x + f (cos x − 1)`. -/
def edgeD (W f x : ℝ) : ℝ := W * Real.sin x + f * (Real.cos x - 1)

/-- `W² − 2 f μ − μ² = B² − (f + μ)²`. -/
def edgeQ (W f μ : ℝ) : ℝ := W ^ 2 - 2 * f * μ - μ ^ 2

/-- The line amplitude `B = √(W² + f²)`. -/
def amp (W f : ℝ) : ℝ := √(W ^ 2 + f ^ 2)

/-- Base angle `arcsin(f / B)`. -/
def base (W f : ℝ) : ℝ := Real.arcsin (f / amp W f)

/-- Inverse of the flow increment on a line with positive weight. -/
def invPos (W f μ : ℝ) : ℝ := Real.arcsin ((f + μ) / amp W f) - base W f

/-- Inverse of the flow increment on a line with negative weight. -/
def invNeg (W f μ : ℝ) : ℝ := base W f - Real.arcsin ((f + μ) / amp W f)

@[powerlib_foundation] theorem hasDerivAt_edgeG (W f x : ℝ) :
    HasDerivAt (edgeG W f) (edgeD W f x) x := by
  show HasDerivAt (fun x => W * (1 - Real.cos x) + f * (Real.sin x - x)) _ x
  have h := (((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x)).const_mul W).add
    (((Real.hasDerivAt_sin x).sub (hasDerivAt_id x)).const_mul f)
  refine h.congr_deriv ?_
  unfold edgeD
  ring

@[powerlib_foundation] theorem hasDerivAt_edgeD (W f x : ℝ) :
    HasDerivAt (edgeD W f) (W * Real.cos x - f * Real.sin x) x := by
  show HasDerivAt (fun x => W * Real.sin x + f * (Real.cos x - 1)) _ x
  have h := ((Real.hasDerivAt_sin x).const_mul W).add
    (((Real.hasDerivAt_cos x).sub (hasDerivAt_const x (1 : ℝ))).const_mul f)
  refine h.congr_deriv ?_
  ring

@[powerlib_foundation] theorem amp_pos {W f : ℝ} (hW : W ≠ 0) : 0 < amp W f := by
  unfold amp; positivity

@[powerlib_foundation] theorem amp_sq (W f : ℝ) : amp W f ^ 2 = W ^ 2 + f ^ 2 := by
  unfold amp; rw [sq_sqrt (by positivity)]

/-- `|f + μ| < B` exactly when `edgeQ > 0`. -/
@[powerlib_foundation] theorem abs_div_amp_lt {W f μ : ℝ} (hW : W ≠ 0) (hq : 0 < edgeQ W f μ) :
    |(f + μ) / amp W f| < 1 := by
  have hB := amp_pos (f := f) hW
  rw [abs_div, abs_of_pos hB, div_lt_one hB]
  have h2 : (f + μ) ^ 2 < amp W f ^ 2 := by
    rw [amp_sq]; unfold edgeQ at hq; nlinarith
  exact abs_lt_of_sq_lt_sq h2 hB.le

@[powerlib_foundation] theorem cos_base_pos {W f : ℝ} (hW : W ≠ 0) :
    amp W f * Real.cos (base W f) = |W| := by
  have hB := amp_pos (f := f) hW
  unfold base
  rw [Real.cos_arcsin]
  have : 1 - (f / amp W f) ^ 2 = W ^ 2 / amp W f ^ 2 := by
    have h2 := amp_sq W f
    rw [eq_div_iff (by positivity), sub_mul, div_pow, div_mul_cancel₀ _ (by positivity)]
    linarith
  rw [this, sqrt_div' _ (sq_nonneg _), sqrt_sq hB.le, sqrt_sq_eq_abs]
  field_simp

@[powerlib_foundation] theorem sin_base {W f : ℝ} (hW : W ≠ 0) :
    amp W f * Real.sin (base W f) = f := by
  have hB := amp_pos (f := f) hW
  have h1 : |f / amp W f| ≤ 1 := by
    rw [abs_div, abs_of_pos hB, div_le_one hB]
    have : f ^ 2 ≤ amp W f ^ 2 := by rw [amp_sq]; nlinarith
    exact abs_le_of_sq_le_sq' this hB.le |>.2 |> fun h => by
      rw [abs_le]; exact ⟨by nlinarith [abs_le_of_sq_le_sq' this hB.le], h⟩
  unfold base
  rw [Real.sin_arcsin (abs_le.mp h1).1 (abs_le.mp h1).2]
  field_simp

/-- `f + G'(x) = B sin(a + x)` on a line with positive weight. -/
@[powerlib_foundation] theorem add_edgeD_pos {W f : ℝ} (hW : 0 < W) (x : ℝ) :
    f + edgeD W f x = amp W f * Real.sin (base W f + x) := by
  have hc := cos_base_pos (f := f) hW.ne'
  have hs := sin_base (f := f) hW.ne'
  rw [abs_of_pos hW] at hc
  rw [Real.sin_add, mul_add, ← mul_assoc, ← mul_assoc, hs, hc]
  unfold edgeD; ring

/-- `f + G'(x) = B sin(a − x)` on a line with negative weight. -/
@[powerlib_foundation] theorem add_edgeD_neg {W f : ℝ} (hW : W < 0) (x : ℝ) :
    f + edgeD W f x = amp W f * Real.sin (base W f - x) := by
  have hc := cos_base_pos (f := f) hW.ne
  have hs := sin_base (f := f) hW.ne
  rw [abs_of_neg hW] at hc
  rw [Real.sin_sub, mul_sub, ← mul_assoc, ← mul_assoc, hs, hc]
  unfold edgeD; ring

@[powerlib_foundation] theorem arcsin_mem_Ioo {y : ℝ} (hy : |y| < 1) :
    Real.arcsin y ∈ Ioo (-(π / 2)) (π / 2) :=
  ⟨Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hy).1, Real.arcsin_lt_pi_div_two.mpr
    (abs_lt.mp hy).2⟩

@[powerlib_foundation] theorem edgeQ_zero (W f : ℝ) : edgeQ W f 0 = W ^ 2 := by
  unfold edgeQ; ring

@[powerlib_foundation] theorem base_mem {W f : ℝ} (hW : W ≠ 0) :
    base W f ∈ Ioo (-(π / 2)) (π / 2) := by
  have h := abs_div_amp_lt (W := W) (f := f) (μ := 0) hW (by rw [edgeQ_zero]; positivity)
  rw [add_zero] at h
  exact arcsin_mem_Ioo h

/-- The flow increment is inverted by `invPos` on a line with positive weight. -/
@[powerlib_foundation] theorem edgeD_invPos {W f μ : ℝ} (hW : 0 < W) (hq : 0 < edgeQ W f μ) :
    edgeD W f (invPos W f μ) = μ := by
  have h := abs_div_amp_lt (f := f) hW.ne' hq
  have hB := amp_pos (f := f) hW.ne'
  have e := add_edgeD_pos (f := f) hW (invPos W f μ)
  rw [invPos, add_sub_cancel, Real.sin_arcsin (abs_le.mp h.le).1 (abs_le.mp h.le).2,
    mul_div_cancel₀ _ hB.ne'] at e
  rw [invPos]; linarith

/-- The flow increment is inverted by `invNeg` on a line with negative weight. -/
@[powerlib_foundation] theorem edgeD_invNeg {W f μ : ℝ} (hW : W < 0) (hq : 0 < edgeQ W f μ) :
    edgeD W f (invNeg W f μ) = μ := by
  have h := abs_div_amp_lt (f := f) hW.ne hq
  have hB := amp_pos (f := f) hW.ne
  have e := add_edgeD_neg (f := f) hW (invNeg W f μ)
  rw [invNeg, sub_sub_cancel, Real.sin_arcsin (abs_le.mp h.le).1 (abs_le.mp h.le).2,
    mul_div_cancel₀ _ hB.ne'] at e
  rw [invNeg]; linarith

/-- `invPos` is a left inverse of the flow increment on the arc `|a + x| < π/2`. -/
@[powerlib_foundation] theorem invPos_edgeD {W f x : ℝ} (hW : 0 < W)
    (hx : base W f + x ∈ Ioo (-(π / 2)) (π / 2)) : invPos W f (edgeD W f x) = x := by
  have hB := amp_pos (f := f) hW.ne'
  rw [invPos, add_edgeD_pos hW, mul_div_cancel_left₀ _ hB.ne',
    Real.arcsin_sin hx.1.le hx.2.le]
  ring

/-- `invNeg` is a left inverse of the flow increment on the arc `|a − x| < π/2`. -/
@[powerlib_foundation] theorem invNeg_edgeD {W f x : ℝ} (hW : W < 0)
    (hx : base W f - x ∈ Ioo (-(π / 2)) (π / 2)) : invNeg W f (edgeD W f x) = x := by
  have hB := amp_pos (f := f) hW.ne
  rw [invNeg, add_edgeD_neg hW, mul_div_cancel_left₀ _ hB.ne',
    Real.arcsin_sin hx.1.le hx.2.le]
  ring

/-- `invPos` stays on the arc. -/
@[powerlib_foundation] theorem base_add_invPos {W f μ : ℝ} (hW : 0 < W) (hq : 0 < edgeQ W f μ) :
    base W f + invPos W f μ ∈ Ioo (-(π / 2)) (π / 2) := by
  rw [invPos, add_sub_cancel]
  exact arcsin_mem_Ioo (abs_div_amp_lt hW.ne' hq)

/-- `invNeg` stays on the arc. -/
@[powerlib_foundation] theorem base_sub_invNeg {W f μ : ℝ} (hW : W < 0) (hq : 0 < edgeQ W f μ) :
    base W f - invNeg W f μ ∈ Ioo (-(π / 2)) (π / 2) := by
  rw [invNeg, sub_sub_cancel]
  exact arcsin_mem_Ioo (abs_div_amp_lt hW.ne hq)

@[powerlib_foundation] theorem invPos_zero (W f : ℝ) : invPos W f 0 = 0 := by
  simp [invPos, base]

@[powerlib_foundation] theorem invNeg_zero (W f : ℝ) : invNeg W f 0 = 0 := by
  simp [invNeg, base]

/-- `√q = B √(1 − ((f + μ)/B)²)`. -/
@[powerlib_foundation] theorem sqrt_edgeQ {W f μ : ℝ} (hW : W ≠ 0) :
    √(edgeQ W f μ) = amp W f * √(1 - ((f + μ) / amp W f) ^ 2) := by
  have hB := amp_pos (f := f) hW
  have e : edgeQ W f μ = amp W f ^ 2 * (1 - ((f + μ) / amp W f) ^ 2) := by
    rw [mul_sub, mul_one, div_pow, mul_div_cancel₀ _ (by positivity), amp_sq]
    unfold edgeQ; ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hB.le]

@[powerlib_foundation] theorem hasDerivAt_invPos {W f μ : ℝ} (hW : W ≠ 0)
    (hq : 0 < edgeQ W f μ) : HasDerivAt (invPos W f) (1 / √(edgeQ W f μ)) μ := by
  have h := abs_div_amp_lt (f := f) hW hq
  have hB := amp_pos (f := f) hW
  have h1 : (f + μ) / amp W f ≠ -1 := fun e => by rw [e] at h; norm_num at h
  have h2 : (f + μ) / amp W f ≠ 1 := fun e => by rw [e] at h; norm_num at h
  have hlin : HasDerivAt (fun μ => (f + μ) / amp W f) (1 / amp W f) μ :=
    ((hasDerivAt_id μ).const_add f).div_const (amp W f)
  have hd := ((Real.hasDerivAt_arcsin h1 h2).comp μ hlin).sub_const (base W f)
  refine hd.congr_deriv ?_
  rw [sqrt_edgeQ hW]
  field_simp

@[powerlib_foundation] theorem hasDerivAt_invNeg {W f μ : ℝ} (hW : W ≠ 0)
    (hq : 0 < edgeQ W f μ) : HasDerivAt (invNeg W f) (-(1 / √(edgeQ W f μ))) μ := by
  have h := abs_div_amp_lt (f := f) hW hq
  have hB := amp_pos (f := f) hW
  have h1 : (f + μ) / amp W f ≠ -1 := fun e => by rw [e] at h; norm_num at h
  have h2 : (f + μ) / amp W f ≠ 1 := fun e => by rw [e] at h; norm_num at h
  have hlin : HasDerivAt (fun μ => (f + μ) / amp W f) (1 / amp W f) μ :=
    ((hasDerivAt_id μ).const_add f).div_const (amp W f)
  have hd := ((Real.hasDerivAt_arcsin h1 h2).comp μ hlin).const_sub (base W f)
  refine hd.congr_deriv ?_
  rw [sqrt_edgeQ hW]
  field_simp

/-- **Supporting line of a convex line potential.** On the arc where `B cos(a + x) > 0` the line
potential lies above its tangents, strictly away from the contact point. -/
@[powerlib_foundation] theorem edgeG_tangent {W f x X : ℝ} (hW : 0 < W)
    (hx : base W f + x ∈ Ioo (-(π / 2)) (π / 2)) (hX : base W f + X ∈ Ioo (-(π / 2)) (π / 2))
    (hne : x ≠ X) : edgeG W f X + edgeD W f X * (x - X) < edgeG W f x := by
  set I := Ioo (-(π / 2) - base W f) (π / 2 - base W f) with hI
  have hmemI : ∀ y, base W f + y ∈ Ioo (-(π / 2)) (π / 2) ↔ y ∈ I := fun y => by
    simp only [hI, mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hB := amp_pos (f := f) hW.ne'
  have hc := cos_base_pos (f := f) hW.ne'
  have hs := sin_base (f := f) hW.ne'
  rw [abs_of_pos hW] at hc
  have hD2 : ∀ y ∈ I, W * Real.cos y - f * Real.sin y = amp W f * Real.cos (base W f + y) := by
    intro y _
    rw [Real.cos_add, mul_sub, ← mul_assoc, ← mul_assoc, hc, hs]
  have hmono : StrictMonoOn (edgeD W f) I := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun y _ =>
      (hasDerivAt_edgeD W f y).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_edgeD W f y).deriv, hD2 y hy]
    exact mul_pos hB (Real.cos_pos_of_mem_Ioo ((hmemI y).mpr hy))
  have hxI := (hmemI x).mp hx
  have hXI := (hmemI X).mp hX
  have hcont : ContinuousOn (edgeG W f) (Icc (min x X) (max x X)) := fun y _ =>
    (hasDerivAt_edgeG W f y).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (edgeG W f) (edgeD W f) hlt
      (fun y hy => (hasDerivAt_edgeG W f y).continuousAt.continuousWithinAt)
      (fun y _ => hasDerivAt_edgeG W f y)
    have hcI : c ∈ I := ⟨hxI.1.trans hc.1, hc.2.trans hXI.2⟩
    have hlt' : edgeD W f c < edgeD W f X := hmono hcI hXI hc.2
    rw [eq_div_iff (sub_ne_zero.mpr hlt.ne')] at hcd
    nlinarith
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (edgeG W f) (edgeD W f) hgt
      (fun y hy => (hasDerivAt_edgeG W f y).continuousAt.continuousWithinAt)
      (fun y _ => hasDerivAt_edgeG W f y)
    have hcI : c ∈ I := ⟨hXI.1.trans hc.1, hc.2.trans hxI.2⟩
    have hlt' : edgeD W f X < edgeD W f c := hmono hXI hcI hc.1
    rw [eq_div_iff (sub_ne_zero.mpr hgt.ne')] at hcd
    nlinarith

@[powerlib_foundation] theorem edgeG_zero (W f : ℝ) : edgeG W f 0 = 0 := by simp [edgeG]

@[powerlib_foundation] theorem abs_edgeD_le (W f : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |edgeD W f x| ≤ (|W| + |f|) * |x| := by
  have h1 : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
  have h2 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have h3 : Real.cos x ≤ 1 := Real.cos_le_one x
  have hx2 : x ^ 2 ≤ |x| := by
    rw [← sq_abs]; nlinarith [abs_nonneg x]
  have h4 : |Real.cos x - 1| ≤ |x| := by
    rw [abs_le]; constructor <;> nlinarith
  unfold edgeD
  calc |W * Real.sin x + f * (Real.cos x - 1)| ≤ |W| * |Real.sin x| + |f| * |Real.cos x - 1| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
    _ ≤ |W| * |x| + |f| * |x| := by gcongr
    _ = (|W| + |f|) * |x| := by ring

/-! ## A cycle with one negative-weight line -/

section Cycle

variable {m : ℕ} (W f : Fin (m + 1) → ℝ)

/-- Total angle of the critical curve: the sum over the cycle of the inverse flow increments at
the common flow shift `μ` (line `0` has negative weight, the others positive weight). -/
def closure (μ : ℝ) : ℝ := invNeg (W 0) (f 0) μ + ∑ i : Fin m, invPos (W i.succ) (f i.succ) μ

/-- The potential along the critical curve, corrected by `μ` times its total angle. -/
def curvePot (μ : ℝ) : ℝ :=
  (edgeG (W 0) (f 0) (invNeg (W 0) (f 0) μ) - μ * invNeg (W 0) (f 0) μ) +
    ∑ i : Fin m, (edgeG (W i.succ) (f i.succ) (invPos (W i.succ) (f i.succ) μ) -
      μ * invPos (W i.succ) (f i.succ) μ)

variable {W f}

@[powerlib_foundation] theorem closure_zero : closure W f 0 = 0 := by
  simp [closure, invNeg_zero, invPos_zero]

@[powerlib_foundation] theorem curvePot_zero : curvePot W f 0 = 0 := by
  simp [curvePot, invNeg_zero, invPos_zero, edgeG_zero]

variable (hW0 : W 0 < 0) (hW : ∀ i : Fin m, 0 < W i.succ) {ρ : ℝ}
  (hq : ∀ e μ, |μ| ≤ ρ → 0 < edgeQ (W e) (f e) μ)

include hW0 hW hq in
@[powerlib_foundation] theorem hasDerivAt_closure {μ : ℝ} (hμ : |μ| ≤ ρ) :
    HasDerivAt (closure W f) (-(1 / √(edgeQ (W 0) (f 0) μ)) +
      ∑ i : Fin m, 1 / √(edgeQ (W i.succ) (f i.succ) μ)) μ := by
  unfold closure
  exact (hasDerivAt_invNeg hW0.ne (hq 0 μ hμ)).add
    (HasDerivAt.fun_sum fun i _ => hasDerivAt_invPos (hW i).ne' (hq i.succ μ hμ))

include hW0 hW hq in
@[powerlib_foundation] theorem hasDerivAt_curvePot {μ : ℝ} (hμ : |μ| ≤ ρ) :
    HasDerivAt (curvePot W f) (-closure W f μ) μ := by
  have hterm : ∀ {Wₑ fₑ : ℝ} {X : ℝ → ℝ} {X' : ℝ}, HasDerivAt X X' μ → edgeD Wₑ fₑ (X μ) = μ →
      HasDerivAt (fun μ => edgeG Wₑ fₑ (X μ) - μ * X μ) (-X μ) μ := by
    intro Wₑ fₑ X X' hX hspec
    have h := ((hasDerivAt_edgeG Wₑ fₑ (X μ)).comp μ hX).sub ((hasDerivAt_id μ).mul hX)
    refine h.congr_deriv ?_
    simp only [id, one_mul] at *
    rw [hspec]; ring
  unfold curvePot closure
  have h0 := hterm (hasDerivAt_invNeg hW0.ne (hq 0 μ hμ)) (edgeD_invNeg hW0 (hq 0 μ hμ))
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun (i : Fin m) _ =>
    hterm (hasDerivAt_invPos (hW i).ne' (hq i.succ μ hμ)) (edgeD_invPos (hW i) (hq i.succ μ hμ))
  refine (h0.add hs).congr_deriv ?_
  rw [Finset.sum_neg_distrib]; ring

variable (hΓ : ∀ μ, μ ≠ 0 → |μ| ≤ ρ →
  ∑ i : Fin m, 1 / √(edgeQ (W i.succ) (f i.succ) μ) < 1 / √(edgeQ (W 0) (f 0) μ))

include hW0 hW hq hΓ in
/-- The total angle of the critical curve is strictly decreasing near `μ = 0`. -/
@[powerlib_foundation] theorem closure_sign {μ : ℝ} (hμ : |μ| ≤ ρ) :
    (0 < μ → closure W f μ < 0) ∧ (μ < 0 → 0 < closure W f μ) := by
  have hderiv : ∀ ν ∈ Icc (-ρ) ρ, HasDerivAt (closure W f) (-(1 / √(edgeQ (W 0) (f 0) ν)) +
      ∑ i : Fin m, 1 / √(edgeQ (W i.succ) (f i.succ) ν)) ν := fun ν hν =>
    hasDerivAt_closure hW0 hW hq (abs_le.mpr hν)
  have hneg : ∀ ν, ν ≠ 0 → |ν| ≤ ρ → deriv (closure W f) ν < 0 := by
    intro ν hν0 hν
    rw [(hasDerivAt_closure hW0 hW hq hν).deriv]
    linarith [hΓ ν hν0 hν]
  have hcont : ∀ a b, -ρ ≤ a → b ≤ ρ → ContinuousOn (closure W f) (Icc a b) := fun a b ha hb ν hν =>
    (hderiv ν ⟨ha.trans hν.1, hν.2.trans hb⟩).continuousAt.continuousWithinAt
  have hρ : 0 ≤ ρ := (abs_nonneg μ).trans hμ
  refine ⟨fun hpos => ?_, fun hneg' => ?_⟩
  · have hanti : StrictAntiOn (closure W f) (Icc 0 ρ) :=
      strictAntiOn_of_deriv_neg (convex_Icc 0 ρ) (hcont 0 ρ (by linarith) le_rfl)
        fun ν hν => by
          rw [interior_Icc] at hν
          exact hneg ν hν.1.ne' (by rw [abs_of_pos hν.1]; exact hν.2.le)
    have := hanti ⟨le_rfl, hρ⟩ ⟨hpos.le, (le_abs_self μ).trans hμ⟩ hpos
    rwa [closure_zero] at this
  · have hanti : StrictAntiOn (closure W f) (Icc (-ρ) 0) :=
      strictAntiOn_of_deriv_neg (convex_Icc (-ρ) 0) (hcont (-ρ) 0 le_rfl hρ)
        fun ν hν => by
          rw [interior_Icc] at hν
          exact hneg ν hν.2.ne (by rw [abs_of_neg hν.2]; linarith [hν.1])
    have := hanti ⟨by linarith [neg_abs_le μ], hneg'.le⟩ ⟨by linarith, le_rfl⟩ hneg'
    rwa [closure_zero] at this

include hW0 hW hq hΓ in
/-- The potential along the critical curve is positive away from the degenerate point. -/
@[powerlib_foundation] theorem curvePot_pos {μ : ℝ} (hμ0 : μ ≠ 0) (hμ : |μ| ≤ ρ) :
    0 < curvePot W f μ := by
  have hderiv : ∀ ν ∈ Icc (-ρ) ρ, HasDerivAt (curvePot W f) (-closure W f ν) ν := fun ν hν =>
    hasDerivAt_curvePot hW0 hW hq (abs_le.mpr hν)
  have hcont : ∀ a b, -ρ ≤ a → b ≤ ρ → ContinuousOn (curvePot W f) (Icc a b) :=
    fun a b ha hb ν hν =>
      (hderiv ν ⟨ha.trans hν.1, hν.2.trans hb⟩).continuousAt.continuousWithinAt
  have hρ : 0 ≤ ρ := (abs_nonneg μ).trans hμ
  rcases lt_or_gt_of_ne hμ0 with hneg | hpos
  · have hanti : StrictAntiOn (curvePot W f) (Icc (-ρ) 0) :=
      strictAntiOn_of_deriv_neg (convex_Icc (-ρ) 0) (hcont (-ρ) 0 le_rfl hρ) fun ν hν => by
        rw [interior_Icc] at hν
        have hν' : |ν| ≤ ρ := by rw [abs_of_neg hν.2]; linarith [hν.1]
        rw [(hasDerivAt_curvePot hW0 hW hq hν').deriv]
        linarith [(closure_sign hW0 hW hq hΓ hν').2 hν.2]
    have := hanti ⟨by linarith [neg_abs_le μ], hneg.le⟩ ⟨by linarith, le_rfl⟩ hneg
    rwa [curvePot_zero] at this
  · have hmono : StrictMonoOn (curvePot W f) (Icc 0 ρ) :=
      strictMonoOn_of_deriv_pos (convex_Icc 0 ρ) (hcont 0 ρ (by linarith) le_rfl) fun ν hν => by
        rw [interior_Icc] at hν
        have hν' : |ν| ≤ ρ := by rw [abs_of_pos hν.1]; exact hν.2.le
        rw [(hasDerivAt_curvePot hW0 hW hq hν').deriv]
        linarith [(closure_sign hW0 hW hq hΓ hν').1 hν.1]
    have := hmono ⟨le_rfl, hρ⟩ ⟨hpos.le, (le_abs_self μ).trans hμ⟩ hpos
    rwa [curvePot_zero] at this

include hW0 hW hq hΓ in
/-- **Degenerate strict minimum on a cycle.** For a cycle of lines whose line `0` has negative
weight and the others positive weight, if `∑ᵢ 1/√qᵢ(μ) < 1/√q₀(μ)` for small `μ ≠ 0`, the cycle
potential `∑ₑ Gₑ(xₑ)` on the closed-loop angle increments (`∑ₑ xₑ = 0`) has a strict local
minimum at `0` that is an isolated critical point (equal flow increments on every line). No
condition is put on the Hessian at `0`, which may be singular. -/
@[powerlib_foundation] theorem cycle_strictMin (hρ : 0 < ρ) :
    ∃ r > 0, ∀ x : Fin (m + 1) → ℝ, ∑ e, x e = 0 → x ≠ 0 → (∀ e, |x e| < r) →
      0 < ∑ e, edgeG (W e) (f e) (x e) ∧
        ¬ ∀ e, edgeD (W e) (f e) (x e) = edgeD (W 0) (f 0) (x 0) := by
  have hWne : ∀ e, W e ≠ 0 := fun e => by
    refine Fin.cases hW0.ne (fun i => (hW i).ne') e
  -- the arc radius
  obtain ⟨e₀, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun e => π / 2 - |base (W e) (f e)|) Finset.univ_nonempty
  set r₁ := π / 2 - |base (W e₀) (f e₀)| with hr₁
  have hr₁pos : 0 < r₁ := by
    have := base_mem (f := f e₀) (hWne e₀)
    rw [hr₁, sub_pos, abs_lt]; exact ⟨this.1, this.2⟩
  set r := min r₁ (min 1 (ρ / (|W 0| + |f 0| + 1))) with hr
  have hrpos : 0 < r := lt_min hr₁pos (lt_min one_pos (by positivity))
  refine ⟨r, hrpos, fun x hsum hx0 hx => ?_⟩
  have harcP : ∀ e, base (W e) (f e) + x e ∈ Ioo (-(π / 2)) (π / 2) := fun e => by
    have h1 : r₁ ≤ π / 2 - |base (W e) (f e)| := hmin e (Finset.mem_univ e)
    have h3 := abs_lt.mp ((hx e).trans_le (min_le_left _ _) : |x e| < r₁)
    constructor <;> linarith [neg_abs_le (base (W e) (f e)), le_abs_self (base (W e) (f e))]
  have harcN : base (W 0) (f 0) - x 0 ∈ Ioo (-(π / 2)) (π / 2) := by
    have h1 : r₁ ≤ π / 2 - |base (W 0) (f 0)| := hmin 0 (Finset.mem_univ 0)
    have h3 := abs_lt.mp ((hx 0).trans_le (min_le_left _ _) : |x 0| < r₁)
    constructor <;> linarith [neg_abs_le (base (W 0) (f 0)), le_abs_self (base (W 0) (f 0))]
  set μ := edgeD (W 0) (f 0) (x 0) with hμdef
  have hμ : |μ| ≤ ρ := by
    have h1 : |x 0| ≤ 1 := ((hx 0).trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
    have h2 : |x 0| ≤ ρ / (|W 0| + |f 0| + 1) :=
      ((hx 0).trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    have h3 := abs_edgeD_le (W 0) (f 0) h1
    have h4 : (|W 0| + |f 0|) * |x 0| ≤ ρ := by
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith [abs_nonneg (W 0), abs_nonneg (f 0), abs_nonneg (x 0)]
    exact h3.trans h4
  have hx0eq : x 0 = invNeg (W 0) (f 0) μ := (invNeg_edgeD hW0 harcN).symm
  -- tangent inequalities on the positive lines
  have htan : ∀ i : Fin m, edgeG (W i.succ) (f i.succ) (invPos (W i.succ) (f i.succ) μ) +
      μ * (x i.succ - invPos (W i.succ) (f i.succ) μ) ≤ edgeG (W i.succ) (f i.succ) (x i.succ) ∧
      (x i.succ ≠ invPos (W i.succ) (f i.succ) μ →
        edgeG (W i.succ) (f i.succ) (invPos (W i.succ) (f i.succ) μ) +
          μ * (x i.succ - invPos (W i.succ) (f i.succ) μ) <
        edgeG (W i.succ) (f i.succ) (x i.succ)) := by
    intro i
    have hspec := edgeD_invPos (hW i) (hq i.succ μ hμ)
    have hstrict : x i.succ ≠ invPos (W i.succ) (f i.succ) μ →
        edgeG (W i.succ) (f i.succ) (invPos (W i.succ) (f i.succ) μ) +
          μ * (x i.succ - invPos (W i.succ) (f i.succ) μ) <
        edgeG (W i.succ) (f i.succ) (x i.succ) := fun hne => by
      have := edgeG_tangent (hW i) (harcP i.succ) (base_add_invPos (hW i) (hq i.succ μ hμ)) hne
      rwa [hspec] at this
    refine ⟨?_, hstrict⟩
    by_cases hne : x i.succ = invPos (W i.succ) (f i.succ) μ
    · rw [hne, sub_self, mul_zero, add_zero]
    · exact (hstrict hne).le
  have hlower : curvePot W f μ ≤ ∑ e, edgeG (W e) (f e) (x e) := by
    rw [Fin.sum_univ_succ, curvePot]
    have hs : ∑ i : Fin m, x i.succ = -invNeg (W 0) (f 0) μ := by
      rw [Fin.sum_univ_succ] at hsum; rw [← hx0eq]; linarith
    have hsumtan := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (htan i).1
    rw [hx0eq]
    simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hs] at hsumtan ⊢
    linarith
  refine ⟨?_, fun hcrit => ?_⟩
  · by_cases hμ0 : μ = 0
    · -- `x₀ = 0`, so some positive line moves off its contact point `0`
      have hx00 : x 0 = 0 := by rw [hx0eq, hμ0, invNeg_zero]
      obtain ⟨i, hi⟩ : ∃ i : Fin m, x i.succ ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hx0
        funext e
        exact Fin.cases hx00 (fun i => hall i) e
      have hinv0 : invPos (W i.succ) (f i.succ) μ = 0 := by rw [hμ0, invPos_zero]
      have hstrict := (htan i).2 (by rw [hinv0]; exact hi)
      have hsumtan : ∑ j : Fin m, (edgeG (W j.succ) (f j.succ) (invPos (W j.succ) (f j.succ) μ) +
          μ * (x j.succ - invPos (W j.succ) (f j.succ) μ)) <
          ∑ j : Fin m, edgeG (W j.succ) (f j.succ) (x j.succ) :=
        Finset.sum_lt_sum (fun j _ => (htan j).1) ⟨i, Finset.mem_univ _, hstrict⟩
      rw [Fin.sum_univ_succ, hx00, edgeG_zero, zero_add]
      simp only [hμ0, zero_mul, add_zero, invPos_zero, edgeG_zero, Finset.sum_const_zero]
        at hsumtan
      exact hsumtan
    · exact (curvePot_pos hW0 hW hq hΓ hμ0 hμ).trans_le hlower
  · -- equal flow increments: the point lies on the critical curve and closes the cycle
    have hxi : ∀ i : Fin m, x i.succ = invPos (W i.succ) (f i.succ) μ := fun i => by
      rw [← hcrit i.succ, invPos_edgeD (hW i) (harcP i.succ)]
    have hcl : closure W f μ = 0 := by
      rw [closure, ← hx0eq, ← Finset.sum_congr rfl fun i _ => hxi i, ← Fin.sum_univ_succ]
      exact hsum
    have hμ0 : μ = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · linarith [(closure_sign hW0 hW hq hΓ hμ).2 h]
      · linarith [(closure_sign hW0 hW hq hΓ hμ).1 h]
    apply hx0
    funext e
    refine Fin.cases ?_ (fun i => ?_) e
    · rw [hx0eq, hμ0, invNeg_zero]; rfl
    · rw [hxi i, hμ0, invPos_zero]; rfl

end Cycle

end powerlib.Dynamics.CycleMinimum
