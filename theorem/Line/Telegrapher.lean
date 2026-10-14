import theorem.Line.Bergeron
import theorem.PDE.Partial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Telegrapher equations: second-order form and the distortionless line

The second-order (damped wave) form of the lossy telegrapher equations, and the factorization
of the operator on a distortionless line with its undistorted attenuated travelling waves.

Model boundary.
* Single uniform conductor, constant `L', C' > 0`, `R', G' ≥ 0`, unknowns
  `v, i : ℝ × ℝ → ℝ` of `(x, t)` on the whole plane (current along `+x`, the through convention
  of `theorem/Line/Bergeron.lean`), continuous time, no frequency dependence.

Source: work-sync `theory/T-telegrapher-bergeron.md` §1.1 (elimination of `i` gives the
second-order lossy hyperbolic equation), §1.1.2 (distortionless line `R'/L' = G'/C'`,
factorization and undistorted attenuated travelling waves); `theory/T-pde-systems.md` §1.4.5.

Results.
* `dx F`, `dt F` are the partial derivatives `fderiv ℝ F p (1,0)`, `fderiv ℝ F p (0,1)`
  (`PDE.dx`, `PDE.dt`, with the mixed-partial lemmas, in `theorem/PDE/Partial.lean`).
* `second_order_v` / `second_order_i`: if `v, i ∈ C²` solve `∂ₓv = −L'∂ₜi − R'i`,
  `∂ₓi = −C'∂ₜv − G'v`, then
  `∂ₓₓv = L'C' ∂ₜₜv + (L'G' + R'C') ∂ₜv + R'G' v` and the same for `i`. (The proof uses the
  symmetry of second derivatives of `C²` functions, Mathlib `ContDiffAt.isSymmSndFDerivAt`.)
* `factor_distortionless`: for `v ∈ C²`, `(∂ₜ + c∂ₓ + τ_d)(∂ₜ − c∂ₓ + τ_d) v =
  ∂ₜₜv − c²∂ₓₓv + 2τ_d ∂ₜv + τ_d² v`; with `R' = τ_d L'`, `G' = τ_d C'`, `c² L'C' = 1` this is
  `c²` times the second-order telegrapher operator (`distortionless_iff`), i.e. the operator
  factors.
* `distortionless_isSolution`: on a distortionless line every attenuated travelling-wave pair
  `v = e^{−τ_d t}(f(x − ct) + g(x + ct))`, `i = e^{−τ_d t}(f(x − ct) − g(x + ct))/Z_c` solves the
  lossy first-order system: waves decay as `e^{−τ_d t}` without changing shape.
-/

set_option linter.unnecessarySeqFocus false

noncomputable section
namespace powerlib.Line.Telegrapher
open Set
open powerlib.PDE (dx dt hasFDerivAt_fderiv_apply differentiable_dx differentiable_dt dx_dt_comm
  fderiv_combo)

/-- **Second-order telegrapher equation** obtained by eliminating `i`. -/
@[powerlib_foundation] theorem second_order_v (L C R G : ℝ) {v i : ℝ × ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ContDiff ℝ 2 i)
    (h1 : ∀ p, dx v p = -L * dt i p - R * i p) (h2 : ∀ p, dx i p = -C * dt v p - G * v p)
    (p : ℝ × ℝ) :
    dx (dx v) p = L * C * dt (dt v) p + (L * G + R * C) * dt v p + R * G * v p := by
  have e1 : dx v = fun q => -L * dt i q - R * i q := funext h1
  have e2 : dx i = fun q => -C * dt v q - G * v q := funext h2
  have hdi : Differentiable ℝ i := hi.differentiable (by norm_num)
  have hdv : Differentiable ℝ v := hv.differentiable (by norm_num)
  have step1 : dx (dx v) p = -L * dx (dt i) p - R * dx i p := by
    rw [e1]; exact fderiv_combo (differentiable_dt hi) hdi (-L) R (1, 0) p
  have step2 : dt (dx i) p = -C * dt (dt v) p - G * dt v p := by
    rw [e2]; exact fderiv_combo (differentiable_dt hv) hdv (-C) G (0, 1) p
  rw [step1, dx_dt_comm hi, step2, h2 p]
  ring

/-- The current satisfies the same second-order equation. -/
@[powerlib_foundation] theorem second_order_i (L C R G : ℝ) {v i : ℝ × ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hi : ContDiff ℝ 2 i)
    (h1 : ∀ p, dx v p = -L * dt i p - R * i p) (h2 : ∀ p, dx i p = -C * dt v p - G * v p)
    (p : ℝ × ℝ) :
    dx (dx i) p = L * C * dt (dt i) p + (L * G + R * C) * dt i p + R * G * i p := by
  have := second_order_v C L G R hi hv h2 h1 p
  rw [this]; ring

/-- The first-order factor `(∂ₜ + κ∂ₓ + τ) F`. -/
def factorOp (κ τ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := dt F p + κ * dx F p + τ * F p

/-- `(∂ₜ + c∂ₓ + τ)(∂ₜ − c∂ₓ + τ) v = ∂ₜₜv − c²∂ₓₓv + 2τ∂ₜv + τ²v` for `v ∈ C²`. -/
@[powerlib_foundation] theorem factor_distortionless (c τ : ℝ) {v : ℝ × ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (p : ℝ × ℝ) :
    factorOp c τ (factorOp (-c) τ v) p =
      dt (dt v) p - c ^ 2 * dx (dx v) p + 2 * τ * dt v p + τ ^ 2 * v p := by
  have hdv : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hdt := differentiable_dt hv
  have hdx := differentiable_dx hv
  have H : HasFDerivAt (factorOp (-c) τ v)
      (fderiv ℝ (dt v) p + (-c) • fderiv ℝ (dx v) p + τ • fderiv ℝ v p) p :=
    ((hdt p).hasFDerivAt.add ((hdx p).hasFDerivAt.const_mul (-c))).add
      ((hdv p).hasFDerivAt.const_mul τ)
  have hlin : ∀ w : ℝ × ℝ, fderiv ℝ (factorOp (-c) τ v) p w =
      fderiv ℝ (dt v) p w + -c * fderiv ℝ (dx v) p w + τ * fderiv ℝ v p w := by
    intro w
    rw [H.fderiv]
    simp
  simp only [factorOp]
  unfold dt dx at *
  rw [hlin, hlin]
  have hc := dx_dt_comm hv p
  unfold dt dx at hc
  rw [hc]
  ring

/-- On a distortionless line (`R' = τ_d L'`, `G' = τ_d C'`, `c² L'C' = 1`) the second-order
telegrapher operator is `1/c²` times the factored operator. -/
@[powerlib_foundation] theorem distortionless_iff {L C c τ : ℝ}
    (hc : c ^ 2 * (L * C) = 1) {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v) (p : ℝ × ℝ) :
    dx (dx v) p = L * C * dt (dt v) p + (L * (τ * C) + (τ * L) * C) * dt v p +
        (τ * L) * (τ * C) * v p ↔
      factorOp c τ (factorOp (-c) τ v) p = 0 := by
  rw [factor_distortionless c τ hv p]
  have hc2 : c ^ 2 ≠ 0 := by
    intro h; rw [h, zero_mul] at hc; exact zero_ne_one hc
  constructor
  · intro h
    rw [h]
    linear_combination (-(dt (dt v) p) - 2 * τ * dt v p - τ ^ 2 * v p) * hc
  · intro h
    apply mul_left_cancel₀ hc2
    linear_combination (-1 : ℝ) * h + (-(dt (dt v) p + 2 * τ * dt v p + τ ^ 2 * v p)) * hc

/-- **Distortionless line**: attenuated travelling waves `e^{−τ_d t}(f(x − ct) ± g(x + ct))`
solve the lossy telegrapher equations with `R' = τ_d L'`, `G' = τ_d C'`. -/
@[powerlib_foundation] theorem distortionless_isSolution (p : LosslessLine) (τ : ℝ)
    {f g f' g' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y) (hg : ∀ y, HasDerivAt g (g' y) y)
    (a b : ℝ) :
    IsTelegrapherSolution p.L p.C (τ * p.L) (τ * p.C) a b
      (fun q => Real.exp (-τ * q.2) * LosslessLine.travellingV p f g q)
      (fun q => Real.exp (-τ * q.2) * LosslessLine.travellingI p f g q) := by
  obtain ⟨vx, vt, ix, it, h⟩ := LosslessLine.travelling_isSolution (p := p) hf hg a b
  refine ⟨fun q => Real.exp (-τ * q.2) * vx q,
    fun q => -τ * Real.exp (-τ * q.2) * LosslessLine.travellingV p f g q +
      Real.exp (-τ * q.2) * vt q,
    fun q => Real.exp (-τ * q.2) * ix q,
    fun q => -τ * Real.exp (-τ * q.2) * LosslessLine.travellingI p f g q +
      Real.exp (-τ * q.2) * it q, fun q hq => ?_⟩
  obtain ⟨hV, hI, e1, e2⟩ := h q hq
  have hE : HasFDerivAt (fun q : ℝ × ℝ => Real.exp (-τ * q.2))
      ((-τ * Real.exp (-τ * q.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
    have := ((hasFDerivAt_snd (p := q)).const_mul (-τ)).exp
    convert this using 1
    ext <;> simp ; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hE.hasFDerivWithinAt.mul hV
    refine this.congr_fderiv ?_
    ext <;> simp <;> ring
  · have := hE.hasFDerivWithinAt.mul hI
    refine this.congr_fderiv ?_
    ext <;> simp <;> ring
  · simp only [zero_mul, sub_zero] at e1
    show Real.exp (-τ * q.2) * vx q = -p.L * (-τ * Real.exp (-τ * q.2) *
      LosslessLine.travellingI p f g q + Real.exp (-τ * q.2) * it q) -
      τ * p.L * (Real.exp (-τ * q.2) * LosslessLine.travellingI p f g q)
    rw [e1]
    ring
  · simp only [zero_mul, sub_zero] at e2
    show Real.exp (-τ * q.2) * ix q = -p.C * (-τ * Real.exp (-τ * q.2) *
      LosslessLine.travellingV p f g q + Real.exp (-τ * q.2) * vt q) -
      τ * p.C * (Real.exp (-τ * q.2) * LosslessLine.travellingV p f g q)
    rw [e2]
    ring

end powerlib.Line.Telegrapher
