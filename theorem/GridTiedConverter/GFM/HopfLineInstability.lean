import theorem.GridTiedConverter.GFM.HopfCoefficientLine
import theorem.Dynamics.Instability

/-! # Instability of the subcritical Hopf point of the VSM on a dynamic R–L line

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged, at
  the witness `Line.VSM.hopfWitness` of `theorem/GridTiedConverter/GFM/HopfCoefficientLine.lean`:
  `E = V = 1`, `R = 1/5`, `L = 1/10`, `ω₀ = 5` (`X = 1/2`), `M = 7/4`, `D = 1/4`, `P_ref = 0`,
  `δ* = 0` (operating point `0`, zero current); state `(δ, ω, i_d, i_q) : State 4`, grid dq frame
  at `ω₀`, export-positive power, constant `E`; no power filter, voltage loop, inner loops, PLL,
  delay or PWM.
* Level: Lyapunov instability (LeanForControl's `Unstable`) of the operating point at one
  exhibited parameter point, in exact rational arithmetic. Not stated: the bifurcating (unstable)
  cycle, the `ε = 1/ω_b` law of the source note, other parameter points.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, "Subcritical EXISTS: VSM without
filter on dynamic RL line"); Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.3 (Chetaev);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4 (normal form,
centre-manifold expansion, first Lyapunov coefficient) for the construction. The coordinates, the
centre-manifold quadratic `H`, the corrections `R₃, R₄`, the Lyapunov matrix `S` and the
polynomial lists were computed with SymPy (untrusted) and are checked by the kernel
(`norm_num; ring`).

Results.
* Coordinates `x = a Re q + b Im q + y₁ s₁ + y₂ s₂`, `q` the critical eigenvector
  (`hopfWitnessQ`), `s₁ = (0, 1, 7, 7)`, `s₂ = (1, 0, 50, −20)` (the stable subspace, the range of
  `J² + I` for the factorization `(s² + 1)(s² + 29s/7 + 200/7)` of
  `Line.VSM.hopfWitness_charpoly`): the linear part is `ȧ = b`, `ḃ = −a`,
  `ẏ₁ = −(29/7) y₁ − (200/7) y₂`, `ẏ₂ = y₁`, and the field is affine in `cos δ − 1` and `sin δ`,
  `δ = a + y₂`.
* `Line.VSM.hopfChetaev`: `W = a² + b² + R₃(a, b) + R₄(a, b) − c (y − H(a, b))ᵀ S (y − H(a, b))`
  with `c = 250000`. Along the Taylor truncation (`cos δ − 1 ≈ −δ²/2`, `sin δ ≈ δ − δ³/6`) and in
  the weights `1` for `a, b`, `2` for `y`, its derivative has no term of weight below four; the
  weight-four part is `κ (a² + b²)² + q₁ v₁ + q₂ v₂ + c |v|²`, `v = y − H(a, b)`,
  `κ = ℓ₁/2 = 739091/156873665` (the coefficient of `Line.VSM.hopfWitness_firstLyapunov`,
  recovered through the normal form), at least `(κ/2) t⁴` for the weighted size
  `t⁴ = a⁴ + b⁴ + |v|²`. The terms of weight five and more and the remainders of `cos` and `sin`
  (`Real.cos_bound`, `Real.sin_bound`) are `O(t⁵)`. Hence `Line.VSM.hopfChetaev_lie_pos`: the
  derivative of `W` along the field is positive on a punctured neighbourhood of the operating
  point (at least `(ℓ₁/8) t⁴`), and `Line.VSM.hopfChetaev_seed`: `W` is positive at states
  arbitrarily close to it. The term `−c |v|²` absorbs the centre manifold: no centre-manifold
  theorem is used.

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* `Line.VSM.hopfWitness_mem_den_unstable`: the witness is unstable
  (`Dynamics.unstable_of_chetaev` with `hopfChetaev`): a subcritical Hopf point of a balanced
  physical model, where the linearization (eigenvalues `±i` and a stable pair) decides nothing.
* `Line.VSM.not_exactUnder_unstable`: the instability translation of `Line.VSM.family` (a strict
  violation of the quartic Routh conditions, `Line.VSM.mem_den_unstable`) is **not** exact within
  physical models: the witness lies on the Routh boundary (`a₃ a₂ a₁ = a₁² + a₃² a₀`) and is
  unstable.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Set Filter Topology Asymptotics
open powerlib.Dynamics (State coord)

namespace HopfLine

/-! ## Polynomials in four real variables

Private helpers, the four-variable form of the three-variable lists of
`theorem/Dynamics/Degenerate/WeakFocus.lean`. -/

/-- The polynomial `Σ κ a^i b^j c^k d^l` over a list of terms `(κ, i, j, k, l)`. -/
private def poly4 : List (ℝ × ℕ × ℕ × ℕ × ℕ) → ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _ => 0
  | t :: l, a, b, c, d =>
      t.1 * (a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2.1 * d ^ t.2.2.2.2) + poly4 l a b c d

/-- The derivative of `poly4 l` at `(a, b, c, d)` in the direction `(da, db, dc, dd)`. -/
private def dpoly4 : List (ℝ × ℕ × ℕ × ℕ × ℕ) → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _, _, _, _, _ => 0
  | t :: l, a, b, c, d, da, db, dc, dd =>
      t.1 * ((t.2.1 : ℝ) * a ^ (t.2.1 - 1) * b ^ t.2.2.1 * c ^ t.2.2.2.1 * d ^ t.2.2.2.2 * da +
        (t.2.2.1 : ℝ) * a ^ t.2.1 * b ^ (t.2.2.1 - 1) * c ^ t.2.2.2.1 * d ^ t.2.2.2.2 * db +
        (t.2.2.2.1 : ℝ) * a ^ t.2.1 * b ^ t.2.2.1 * c ^ (t.2.2.2.1 - 1) * d ^ t.2.2.2.2 * dc +
        (t.2.2.2.2 : ℝ) * a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2.1 * d ^ (t.2.2.2.2 - 1) * dd) +
      dpoly4 l a b c d da db dc dd

@[tmio T, simp, powerlib_foundation] private theorem poly4_nil (a b c d : ℝ) :
    poly4 [] a b c d = 0 := rfl

@[tmio T, simp, powerlib_foundation] private theorem poly4_cons (t : ℝ × ℕ × ℕ × ℕ × ℕ)
    (l : List (ℝ × ℕ × ℕ × ℕ × ℕ)) (a b c d : ℝ) :
    poly4 (t :: l) a b c d =
      t.1 * (a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2.1 * d ^ t.2.2.2.2) + poly4 l a b c d := rfl

@[tmio T, simp, powerlib_foundation] private theorem dpoly4_nil (a b c d da db dc dd : ℝ) :
    dpoly4 [] a b c d da db dc dd = 0 := rfl

@[tmio T, simp, powerlib_foundation] private theorem dpoly4_cons (t : ℝ × ℕ × ℕ × ℕ × ℕ)
    (l : List (ℝ × ℕ × ℕ × ℕ × ℕ)) (a b c d da db dc dd : ℝ) :
    dpoly4 (t :: l) a b c d da db dc dd =
      t.1 * ((t.2.1 : ℝ) * a ^ (t.2.1 - 1) * b ^ t.2.2.1 * c ^ t.2.2.2.1 * d ^ t.2.2.2.2 * da +
        (t.2.2.1 : ℝ) * a ^ t.2.1 * b ^ (t.2.2.1 - 1) * c ^ t.2.2.2.1 * d ^ t.2.2.2.2 * db +
        (t.2.2.2.1 : ℝ) * a ^ t.2.1 * b ^ t.2.2.1 * c ^ (t.2.2.2.1 - 1) * d ^ t.2.2.2.2 * dc +
        (t.2.2.2.2 : ℝ) * a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2.1 * d ^ (t.2.2.2.2 - 1) * dd) +
      dpoly4 l a b c d da db dc dd := rfl

/-- The derivative is linear in the direction. -/
@[tmio T, powerlib_foundation] private theorem dpoly4_add_smul (l : List (ℝ × ℕ × ℕ × ℕ × ℕ))
    (a b c d da db dc dd s ea eb ec ed : ℝ) :
    dpoly4 l a b c d (da + s * ea) (db + s * eb) (dc + s * ec) (dd + s * ed) =
      dpoly4 l a b c d da db dc dd + s * dpoly4 l a b c d ea eb ec ed := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [dpoly4_cons, ih]; ring

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `z ↦ poly4 l (ℓa z) (ℓb z) (ℓc z) (ℓd z)` has the derivative `dpoly4`. -/
@[tmio T, powerlib_foundation] private theorem hasFDerivAt_poly4
    (l : List (ℝ × ℕ × ℕ × ℕ × ℕ)) (ℓa ℓb ℓc ℓd : E →L[ℝ] ℝ) (z : E) :
    ∃ L : E →L[ℝ] ℝ, HasFDerivAt (fun z => poly4 l (ℓa z) (ℓb z) (ℓc z) (ℓd z)) L z ∧
      ∀ v, L v = dpoly4 l (ℓa z) (ℓb z) (ℓc z) (ℓd z) (ℓa v) (ℓb v) (ℓc v) (ℓd v) := by
  induction l with
  | nil => exact ⟨0, hasFDerivAt_const 0 z, fun v => by simp⟩
  | cons t l ih =>
    obtain ⟨L, hL, hLv⟩ := ih
    have hm := (((((ℓa.hasFDerivAt (x := z)).pow t.2.1).mul
      ((ℓb.hasFDerivAt (x := z)).pow t.2.2.1)).mul
        ((ℓc.hasFDerivAt (x := z)).pow t.2.2.2.1)).mul
          ((ℓd.hasFDerivAt (x := z)).pow t.2.2.2.2)).const_mul t.1
    refine ⟨_, hm.add hL, fun v => ?_⟩
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, hLv,
      dpoly4_cons]
    ring

@[tmio T, powerlib_foundation] private theorem contDiff_poly4 (l : List (ℝ × ℕ × ℕ × ℕ × ℕ))
    (ℓa ℓb ℓc ℓd : E →L[ℝ] ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun z => poly4 l (ℓa z) (ℓb z) (ℓc z) (ℓd z)) := by
  induction l with
  | nil => exact contDiff_const
  | cons t l ih =>
    exact (contDiff_const.mul ((((ℓa.contDiff.pow _).mul (ℓb.contDiff.pow _)).mul
      (ℓc.contDiff.pow _)).mul (ℓd.contDiff.pow _))).add ih

end Deriv

/-- A polynomial whose monomials `a^i b^j c^k d^l` all have weight `i + j + 2k + 2l ≥ k₀` is
`O(s^{k₀})` when `a, b = O(s)`, `c, d = O(s²)` and `s → 0`. -/
@[tmio T, powerlib_foundation] private theorem isBigO_poly4_weight {α : Type*} {l : Filter α}
    {s a b c d : α → ℝ} (hs : Tendsto s l (𝓝 0)) (ha : a =O[l] s) (hb : b =O[l] s)
    (hc : c =O[l] fun x => s x ^ 2) (hd : d =O[l] fun x => s x ^ 2)
    (L : List (ℝ × ℕ × ℕ × ℕ × ℕ)) {k : ℕ}
    (hL : ∀ t ∈ L, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2.1 + 2 * t.2.2.2.2) :
    (fun x => poly4 L (a x) (b x) (c x) (d x)) =O[l] fun x => s x ^ k := by
  induction L with
  | nil => simpa using isBigO_zero (fun x => s x ^ k) l
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')
    have hm : (fun x => a x ^ t.2.1 * b x ^ t.2.2.1 * c x ^ t.2.2.2.1 * d x ^ t.2.2.2.2) =O[l]
        fun x => s x ^ (t.2.1 + t.2.2.1 + 2 * t.2.2.2.1 + 2 * t.2.2.2.2) := by
      refine ((((ha.pow t.2.1).mul (hb.pow t.2.2.1)).mul (hc.pow t.2.2.2.1)).mul
        (hd.pow t.2.2.2.2)).congr_right fun x => ?_
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    simp only [poly4_cons]
    exact ((hm.trans (Dynamics.isBigO_pow_of_tendsto hs ht)).const_mul_left t.1).add ih'

/-! ## Centre and stable coordinates -/

/-- Centre coordinate `a` of `x = a Re q + b Im q + y₁ s₁ + y₂ s₂` (`Re q = (1, 0, 7/4, 3/4)`,
`Im q = (0, 1, −1/4, 1/4)`, `s₁ = (0, 1, 7, 7)`, `s₂ = (1, 0, 50, −20)`). -/
private def cA : State 4 →L[ℝ] ℝ :=
  (3860 / 3809 : ℝ) • coord 0 + (-28 / 3809 : ℝ) • coord 1 + (-54 / 3809 : ℝ) • coord 2 +
    (58 / 3809 : ℝ) • coord 3

/-- Centre coordinate `b`. -/
private def cB : State 4 →L[ℝ] ℝ :=
  (580 / 3809 : ℝ) • coord 0 + (3864 / 3809 : ℝ) • coord 1 + (-166 / 3809 : ℝ) • coord 2 +
    (-386 / 3809 : ℝ) • coord 3

/-- Stable coordinate `y₁`. -/
private def cY1 : State 4 →L[ℝ] ℝ :=
  (-580 / 3809 : ℝ) • coord 0 + (-55 / 3809 : ℝ) • coord 1 + (166 / 3809 : ℝ) • coord 2 +
    (386 / 3809 : ℝ) • coord 3

/-- Stable coordinate `y₂`. -/
private def cY2 : State 4 →L[ℝ] ℝ :=
  (-51 / 3809 : ℝ) • coord 0 + (28 / 3809 : ℝ) • coord 1 + (54 / 3809 : ℝ) • coord 2 +
    (-58 / 3809 : ℝ) • coord 3

@[tmio M, powerlib_domain] private theorem coords_apply (x : State 4) :
    cA x = (3860 * x 0 - 28 * x 1 - 54 * x 2 + 58 * x 3) / 3809 ∧
      cB x = (580 * x 0 + 3864 * x 1 - 166 * x 2 - 386 * x 3) / 3809 ∧
      cY1 x = (-580 * x 0 - 55 * x 1 + 166 * x 2 + 386 * x 3) / 3809 ∧
      cY2 x = (-51 * x 0 + 28 * x 1 + 54 * x 2 - 58 * x 3) / 3809 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cA, cB, cY1, cY2] <;> ring

/-- The state in centre and stable coordinates. -/
@[tmio M, powerlib_domain] private theorem state_eq (x : State 4) :
    x 0 = cA x + cY2 x ∧ x 1 = cB x + cY1 x ∧
      x 2 = 7 / 4 * cA x - 1 / 4 * cB x + 7 * cY1 x + 50 * cY2 x ∧
      x 3 = 3 / 4 * cA x + 1 / 4 * cB x + 7 * cY1 x - 20 * cY2 x := by
  obtain ⟨h1, h2, h3, h4⟩ := coords_apply x
  rw [h1, h2, h3, h4]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- First component of the quadratic map `H` solving the homological equation
`DH(a, b) (b, −a) = A_s H(a, b) + F₂(a, b)` (`F₂` the quadratic stable forcing at `y = 0`): the
second-order term of a centre-manifold expansion, used here only to shift the stable
coordinates. -/
private def cmH1 (a b : ℝ) : ℝ :=
  4591199 / 62749466 * a ^ 2 - 1267275 / 31374733 * (a * b) + 54469 / 62749466 * b ^ 2

/-- Second component of the quadratic map `H`. -/
private def cmH2 (a b : ℝ) : ℝ :=
  -(243882351 / 12549893200) * a ^ 2 + 54469 / 62749466 * (a * b) +
    16162249 / 12549893200 * b ^ 2

@[tmio M, powerlib_domain] private theorem abs_cmH_le (a b : ℝ) :
    |cmH1 a b| ≤ a ^ 2 + b ^ 2 ∧ |cmH2 a b| ≤ a ^ 2 + b ^ 2 := by
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> simp only [cmH1, cmH2] <;>
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-- The linear part of the field in the coordinates `(a, b, y₁, y₂)`. -/
private def dirLam (a b y1 y2 : ℝ) : Fin 4 → ℝ :=
  ![-(580 / 3809) * a + b - (580 / 3809) * y2,
    (51 / 3809) * a + (3860 / 3809) * y2,
    -(3860 / 3809) * a - (29 / 7) * y1 - (788820 / 26663) * y2,
    (580 / 3809) * a + y1 + (580 / 3809) * y2]

/-- The coefficient of `cos δ − 1` in the field, in the coordinates. -/
private def dirMu (a b y1 y2 : ℝ) : Fin 4 → ℝ :=
  ![(28 / 3809) * a - (4 / 3809) * b + (112 / 3809) * y1 + (800 / 3809) * y2 - 540 / 3809,
    -(3864 / 3809) * a + (552 / 3809) * b - (15456 / 3809) * y1 - (110400 / 3809) * y2 -
      1660 / 3809,
    (55 / 3809) * a - (55 / 26663) * b + (220 / 3809) * y1 + (11000 / 26663) * y2 + 1660 / 3809,
    -(28 / 3809) * a + (4 / 3809) * b - (112 / 3809) * y1 - (800 / 3809) * y2 + 540 / 3809]

/-- The coefficient of `sin δ` in the field, in the coordinates. -/
private def dirNu (a b y1 y2 : ℝ) : Fin 4 → ℝ :=
  ![(12 / 3809) * a + (4 / 3809) * b + (112 / 3809) * y1 - (320 / 3809) * y2 + 580 / 3809,
    -(1656 / 3809) * a - (552 / 3809) * b - (15456 / 3809) * y1 + (44160 / 3809) * y2 - 3860 / 3809,
    (165 / 26663) * a + (55 / 26663) * b + (220 / 3809) * y1 - (4400 / 26663) * y2 + 3860 / 3809,
    -(12 / 3809) * a - (4 / 3809) * b - (112 / 3809) * y1 + (320 / 3809) * y2 - 580 / 3809]

/-- The field of the witness in the coordinates: affine in `cos δ − 1` and `sin δ`. -/
@[tmio M, powerlib_domain] private theorem field_coords (x : State 4) (i : Fin 4) :
    ![cA, cB, cY1, cY2] i (hopfWitness.g.field x) =
      dirLam (cA x) (cB x) (cY1 x) (cY2 x) i +
        (Real.cos (x 0) - 1) * dirMu (cA x) (cB x) (cY1 x) (cY2 x) i +
        Real.sin (x 0) * dirNu (cA x) (cB x) (cY1 x) (cY2 x) i := by
  obtain ⟨h1, h2, h3, h4⟩ := coords_apply x
  obtain ⟨h1', h2', h3', h4'⟩ := coords_apply (hopfWitness.g.field x)
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, h1, h2, h3, h4, h1', h2', h3', h4', dirLam, dirMu,
      dirNu] <;>
    simp [field, hopfWitness, Network.power_eq, Network.rateD, Network.rateQ, Network.X] <;>
    ring

/-! ## The Chetaev function -/

/-- The cubic and quartic normal-form corrections `R₃ + R₄` (homological equations of the
rotation `ȧ = b`, `ḃ = −a`). -/
private def normalForm (a b : ℝ) : ℝ :=
  548 / 3809 * a ^ 3 + 564 / 3809 * (a ^ 2 * b) + 8 / 3809 * b ^ 3 -
    113459508199 / 1378919515350 * a ^ 4 - 547093925422 / 8962976849775 * (a ^ 3 * b) -
    64705188529 / 5975317899850 * (a ^ 2 * b ^ 2) + 15191183276 / 2987658949925 * (a * b ^ 3)

/-- The quadratic form `vᵀ S v` of the stable block, `A_sᵀ S + S A_s = −I` for
`A_s = [[−29/7, −200/7], [1, 0]]`. -/
private def stableForm (v1 v2 : ℝ) : ℝ :=
  1449 / 11600 * v1 ^ 2 + 7 / 200 * (v1 * v2) + 42241 / 11600 * v2 ^ 2

end HopfLine

open HopfLine in
/-- **The Chetaev function** of the witness. In the centre and stable coordinates
`(a, b, y₁, y₂)` of the state (`x = a Re q + b Im q + y₁ s₁ + y₂ s₂`, `q` the critical
eigenvector `hopfWitnessQ`, `s₁ = (0, 1, 7, 7)`, `s₂ = (1, 0, 50, −20)` spanning the stable
subspace), `W = a² + b² + R₃(a, b) + R₄(a, b) − c vᵀ S v` with `v = y − H(a, b)`: `R₃, R₄` the
normal-form corrections, `H` the quadratic solution of the centre-manifold homological equation,
`S` the Lyapunov matrix of the stable block and `c = 250000`. -/
def hopfChetaev (x : State 4) : ℝ :=
  cA x ^ 2 + cB x ^ 2 + normalForm (cA x) (cB x) -
    250000 * stableForm (cY1 x - cmH1 (cA x) (cB x)) (cY2 x - cmH2 (cA x) (cB x))

namespace HopfLine

/-- The Chetaev function as a list of monomials in `(a, b, y₁, y₂)`. -/
private def chetW : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((-21022277133164935901831 / 42161490097945670400 : ℝ), 4, 0, 0, 0),
    ((7118765499298561658879 / 34256210704580857200 : ℝ), 3, 1, 0, 0),
    ((548 / 3809 : ℝ), 3, 0, 0, 0),
    ((-32808613864103626597 / 3149996386628124800 : ℝ), 2, 2, 0, 0),
    ((564 / 3809 : ℝ), 2, 1, 0, 0), ((32025533823675 / 7278938056 : ℝ), 2, 0, 1, 0),
    ((-252885792729775 / 7278938056 : ℝ), 2, 0, 0, 1), ((1 : ℝ), 2, 0, 0, 0),
    ((239435308412561217 / 393749548328515600 : ℝ), 1, 3, 0, 0),
    ((-2288441089375 / 909867257 : ℝ), 1, 1, 1, 0), ((1116444611875 / 909867257 : ℝ), 1, 1, 0, 1),
    ((-2960768058681249 / 1918611608552704 : ℝ), 0, 4, 0, 0), ((8 / 3809 : ℝ), 0, 3, 0, 0),
    ((476651318675 / 7278938056 : ℝ), 0, 2, 1, 0), ((17123025035225 / 7278938056 : ℝ), 0, 2, 0, 1),
    ((1 : ℝ), 0, 2, 0, 0), ((-905625 / 29 : ℝ), 0, 0, 2, 0), ((-8750 : ℝ), 0, 0, 1, 1),
    ((-26400625 / 29 : ℝ), 0, 0, 0, 2)]

@[tmio M, powerlib_domain] private theorem hopfChetaev_eq (x : State 4) :
    hopfChetaev x = poly4 chetW (cA x) (cB x) (cY1 x) (cY2 x) := by
  simp only [hopfChetaev, normalForm, stableForm, cmH1, cmH2, chetW, poly4_cons, poly4_nil]
  norm_num
  ring

@[tmio M, powerlib_domain] private theorem contDiff_hopfChetaev : ContDiff ℝ 1 hopfChetaev := by
  rw [show hopfChetaev = fun x => poly4 chetW (cA x) (cB x) (cY1 x) (cY2 x) from
    funext hopfChetaev_eq]
  exact contDiff_poly4 _ _ _ _ _

@[tmio M, powerlib_domain] private theorem hopfChetaev_zero : hopfChetaev 0 = 0 := by
  simp [hopfChetaev, normalForm, stableForm, cmH1, cmH2]

/-! ## Its derivative along the field -/

/-- The derivative of `W` along the linear part `dirLam`. -/
private def lieG0 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((4998756179560016352444283 / 16310238321718560634350 : ℝ), 4, 0, 0, 0),
    ((-272663069124440286996993589 / 130481906573748485074800 : ℝ), 3, 1, 0, 0),
    ((894739029644111362376325 / 1739758754316646467664 : ℝ), 3, 0, 0, 1),
    ((-33786760942071863 / 3465684381913 : ℝ), 3, 0, 0, 0),
    ((1090176015303608145705213 / 1739758754316646467664 : ℝ), 2, 2, 0, 0),
    ((-34807124472966246568737 / 299958405916663184080 : ℝ), 2, 1, 0, 1),
    ((9482260021373988 / 3465684381913 : ℝ), 2, 1, 0, 0),
    ((-188336598315186625 / 3465684381913 : ℝ), 2, 0, 1, 0),
    ((-432722506064409040 / 3465684381913 : ℝ), 2, 0, 0, 1), ((-1160 / 3809 : ℝ), 2, 0, 0, 0),
    ((-913640099912632958737063 / 43493968857916161691600 : ℝ), 1, 3, 0, 0),
    ((301196395268499389977 / 59991681183332636816 : ℝ), 1, 2, 0, 1),
    ((1012461676439573 / 3465684381913 : ℝ), 1, 2, 0, 0),
    ((72194152556870125 / 3465684381913 : ℝ), 1, 1, 1, 0),
    ((17288823322111855 / 3465684381913 : ℝ), 1, 1, 0, 1), ((7720 / 3809 : ℝ), 1, 1, 0, 0),
    ((-13477085009420375 / 3465684381913 : ℝ), 1, 0, 1, 1),
    ((6844250000 / 110461 : ℝ), 1, 0, 1, 0), ((40977916147654875 / 3465684381913 : ℝ), 1, 0, 0, 2),
    ((-1022251160 / 3809 : ℝ), 1, 0, 0, 1),
    ((239435308412561217 / 393749548328515600 : ℝ), 0, 4, 0, 0),
    ((-55219714086368789586813 / 8698793771583232338320 : ℝ), 0, 3, 0, 1),
    ((-13617250000 / 31374733 : ℝ), 0, 2, 1, 0),
    ((-1220165550498405 / 3465684381913 : ℝ), 0, 2, 0, 1),
    ((1787264354358875 / 3465684381913 : ℝ), 0, 1, 1, 1),
    ((15876181284104625 / 3465684381913 : ℝ), 0, 1, 0, 2), ((7720 / 3809 : ℝ), 0, 1, 0, 1),
    ((250000 : ℝ), 0, 0, 2, 0), ((6844250000 / 110461 : ℝ), 0, 0, 1, 1),
    ((-70000000 / 3809 : ℝ), 0, 0, 0, 2)]

/-- The derivative of `W` along `dirMu` (the coefficient of `cos δ − 1`). -/
private def lieGC : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((-29419937108407651416975077 / 130481906573748485074800 : ℝ), 4, 0, 0, 0),
    ((7558125986652026368235921 / 130481906573748485074800 : ℝ), 3, 1, 0, 0),
    ((-29419937108407651416975077 / 32620476643437121268700 : ℝ), 3, 0, 1, 0),
    ((-4202848158343950202425011 / 652409532868742425374 : ℝ), 3, 0, 0, 1),
    ((13334208124919495006012363 / 26096381314749697014960 : ℝ), 3, 0, 0, 0),
    ((-18994290158014144282489 / 3345689912147397053200 : ℝ), 2, 2, 0, 0),
    ((111842594276935872193697 / 1087349221447904042290 : ℝ), 2, 1, 1, 0),
    ((79887567340668480138355 / 108734922144790404229 : ℝ), 2, 1, 0, 1),
    ((-1480351305133575724192783 / 8698793771583232338320 : ℝ), 2, 1, 0, 0),
    ((26971560135585499 / 6931368763826 : ℝ), 2, 0, 1, 0),
    ((25480607196906750 / 3465684381913 : ℝ), 2, 0, 0, 1),
    ((-10424877492632858 / 3465684381913 : ℝ), 2, 0, 0, 0),
    ((876916062173622876815 / 133827596485895882128 : ℝ), 1, 3, 0, 0),
    ((-3005194392167135013643 / 374948007395828980100 : ℝ), 1, 2, 1, 0),
    ((-429313484595305001949 / 7498960147916579602 : ℝ), 1, 2, 0, 1),
    ((-67144409962410082343687 / 8698793771583232338320 : ℝ), 1, 2, 0, 0),
    ((-2448235197434397 / 3465684381913 : ℝ), 1, 1, 1, 0),
    ((-20129480358789875 / 3465684381913 : ℝ), 1, 1, 0, 1),
    ((-3203116353371912 / 3465684381913 : ℝ), 1, 1, 0, 0),
    ((36266860424442900 / 3465684381913 : ℝ), 1, 0, 2, 0),
    ((234712432914161300 / 3465684381913 : ℝ), 1, 0, 1, 1),
    ((-3427025252646807 / 3465684381913 : ℝ), 1, 0, 1, 0),
    ((-173832643696955000 / 3465684381913 : ℝ), 1, 0, 0, 2),
    ((78235369515842075 / 3465684381913 : ℝ), 1, 0, 0, 1), ((-1080 / 3809 : ℝ), 1, 0, 0, 0),
    ((-19467687796654542136311 / 21746984428958080845800 : ℝ), 0, 4, 0, 0),
    ((136273814576581794954177 / 5436746107239520211450 : ℝ), 0, 3, 1, 0),
    ((19467687796654542136311 / 108734922144790404229 : ℝ), 0, 3, 0, 1),
    ((42973173080231740046241 / 8698793771583232338320 : ℝ), 0, 3, 0, 0),
    ((-303542802802099 / 6931368763826 : ℝ), 0, 2, 1, 0),
    ((739204192587125 / 3465684381913 : ℝ), 0, 2, 0, 1),
    ((1255704315254158 / 3465684381913 : ℝ), 0, 2, 0, 0),
    ((-2098086097370200 / 3465684381913 : ℝ), 0, 1, 2, 0),
    ((-81024656206509400 / 3465684381913 : ℝ), 0, 1, 1, 1),
    ((1424478389375241 / 3465684381913 : ℝ), 0, 1, 1, 0),
    ((-471702335282710000 / 3465684381913 : ℝ), 0, 1, 0, 2),
    ((-14473781279722725 / 3465684381913 : ℝ), 0, 1, 0, 1), ((-3320 / 3809 : ℝ), 0, 1, 0, 0),
    ((-370055000 / 110461 : ℝ), 0, 0, 2, 0), ((3214665000 / 110461 : ℝ), 0, 0, 1, 1),
    ((-3143700000 / 110461 : ℝ), 0, 0, 1, 0), ((41842250000 / 110461 : ℝ), 0, 0, 0, 2),
    ((-28933900000 / 110461 : ℝ), 0, 0, 0, 1)]

/-- The derivative of `W` along `dirNu` (the coefficient of `sin δ`). -/
private def lieGS : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((-4202848158343950202425011 / 43493968857916161691600 : ℝ), 4, 0, 0, 0),
    ((-2764871946211917559934621 / 130481906573748485074800 : ℝ), 3, 1, 0, 0),
    ((-29419937108407651416975077 / 32620476643437121268700 : ℝ), 3, 0, 1, 0),
    ((4202848158343950202425011 / 1631023832171856063435 : ℝ), 3, 0, 0, 1),
    ((-657058486874233505941539 / 1739758754316646467664 : ℝ), 3, 0, 0, 0),
    ((122424861521545425107147 / 43493968857916161691600 : ℝ), 2, 2, 0, 0),
    ((111842594276935872193697 / 1087349221447904042290 : ℝ), 2, 1, 1, 0),
    ((-31955026936267392055342 / 108734922144790404229 : ℝ), 2, 1, 0, 1),
    ((1236529107595632406372603 / 8698793771583232338320 : ℝ), 2, 1, 0, 0),
    ((16609600014316099 / 6931368763826 : ℝ), 2, 0, 1, 0),
    ((-15233389545974395 / 3465684381913 : ℝ), 2, 0, 0, 1),
    ((33786269613753083 / 3465684381913 : ℝ), 2, 0, 0, 0),
    ((20871207145332681552269 / 8698793771583232338320 : ℝ), 1, 3, 0, 0),
    ((-3005194392167135013643 / 374948007395828980100 : ℝ), 1, 2, 1, 0),
    ((429313484595305001949 / 18747400369791449005 : ℝ), 1, 2, 0, 1),
    ((-32195426388788243729491 / 1739758754316646467664 : ℝ), 1, 2, 0, 0),
    ((441981418221553 / 3465684381913 : ℝ), 1, 1, 1, 0),
    ((-473005654674885 / 266591106301 : ℝ), 1, 1, 0, 1),
    ((-9483770401020608 / 3465684381913 : ℝ), 1, 1, 0, 0),
    ((36266860424442900 / 3465684381913 : ℝ), 1, 0, 2, 0),
    ((-127956171330267700 / 3465684381913 : ℝ), 1, 0, 1, 1),
    ((421838616367317 / 119506357997 : ℝ), 1, 0, 1, 0),
    ((69533057478782000 / 3465684381913 : ℝ), 1, 0, 0, 2),
    ((-21286657134660605 / 3465684381913 : ℝ), 1, 0, 0, 1), ((1160 / 3809 : ℝ), 1, 0, 0, 0),
    ((19467687796654542136311 / 21746984428958080845800 : ℝ), 0, 4, 0, 0),
    ((136273814576581794954177 / 5436746107239520211450 : ℝ), 0, 3, 1, 0),
    ((-38935375593309084272622 / 543674610723952021145 : ℝ), 0, 3, 0, 1),
    ((34897578106386428499003 / 8698793771583232338320 : ℝ), 0, 3, 0, 0),
    ((-603269388140699 / 6931368763826 : ℝ), 0, 2, 1, 0),
    ((-1710788682882980 / 3465684381913 : ℝ), 0, 2, 0, 1),
    ((-1012461676439573 / 3465684381913 : ℝ), 0, 2, 0, 0),
    ((-2098086097370200 / 3465684381913 : ℝ), 0, 1, 2, 0),
    ((-60043795232807400 / 3465684381913 : ℝ), 0, 1, 1, 1),
    ((-2230046486018509 / 3465684381913 : ℝ), 0, 1, 1, 0),
    ((188680934113084000 / 3465684381913 : ℝ), 0, 1, 0, 2),
    ((-9231874698620135 / 3465684381913 : ℝ), 0, 1, 0, 1), ((-7720 / 3809 : ℝ), 0, 1, 0, 0),
    ((-370055000 / 110461 : ℝ), 0, 0, 2, 0), ((6915215000 / 110461 : ℝ), 0, 0, 1, 1),
    ((-6844250000 / 110461 : ℝ), 0, 0, 1, 0), ((-16736900000 / 110461 : ℝ), 0, 0, 0, 2),
    ((1022250000 / 3809 : ℝ), 0, 0, 0, 1)]

/-- The weight-four part of the derivative along the Taylor truncation. -/
private def lieP4 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((564152925125757701233 / 393749548328515600 : ℝ), 4, 0, 0, 0),
    ((-36546251613140888648 / 24609346770532225 : ℝ), 3, 1, 0, 0),
    ((3362279392593058305 / 7874990966570312 : ℝ), 2, 2, 0, 0),
    ((-1147797904912 / 31374733 : ℝ), 2, 0, 1, 0), ((304856760718 / 31374733 : ℝ), 2, 0, 0, 1),
    ((-418220123720533048 / 24609346770532225 : ℝ), 1, 3, 0, 0),
    ((633382877856 / 31374733 : ℝ), 1, 1, 1, 0), ((-12889626368 / 31374733 : ℝ), 1, 1, 0, 1),
    ((239435308412561217 / 393749548328515600 : ℝ), 0, 4, 0, 0),
    ((-13617250000 / 31374733 : ℝ), 0, 2, 1, 0), ((-20211904898 / 31374733 : ℝ), 0, 2, 0, 1),
    ((250000 : ℝ), 0, 0, 2, 0), ((250000 : ℝ), 0, 0, 0, 2)]

/-- Monomials of weight 5 of the derivative along the Taylor truncation. -/
private def lieP5w5 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((-171967401617889206355115827 / 86987937715832323383200 : ℝ), 5, 0, 0, 0),
    ((135695831350709602142088103 / 260963813147496970149600 : ℝ), 4, 1, 0, 0),
    ((14448001226975021189401787 / 260963813147496970149600 : ℝ), 3, 2, 0, 0),
    ((137423196068069359 / 10397053145739 : ℝ), 3, 0, 1, 0),
    ((-122136545969078235 / 2132728850408 : ℝ), 3, 0, 0, 1),
    ((-1230758789566376941703 / 17397587543166464676640 : ℝ), 2, 3, 0, 0),
    ((-540515552932135 / 6931368763826 : ℝ), 2, 1, 1, 0),
    ((35079467128540747 / 27725475055304 : ℝ), 2, 1, 0, 1),
    ((19467687796654542136311 / 21746984428958080845800 : ℝ), 1, 4, 0, 0),
    ((-603269388140699 / 6931368763826 : ℝ), 1, 2, 1, 0),
    ((-24105823356851467 / 27725475055304 : ℝ), 1, 2, 0, 1),
    ((-370055000 / 110461 : ℝ), 1, 0, 2, 0), ((10019272746 / 110461 : ℝ), 1, 0, 1, 1),
    ((442228650 / 3809 : ℝ), 1, 0, 0, 2), ((-64772299353057 / 27725475055304 : ℝ), 0, 3, 0, 1),
    ((-14112698 / 110461 : ℝ), 0, 1, 1, 1), ((211820670 / 110461 : ℝ), 0, 1, 0, 2)]

/-- Monomials of weight 6 of the derivative along the Taylor truncation. -/
private def lieP5w6 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((2865399955016468066594597 / 16310238321718560634350 : ℝ), 6, 0, 0, 0),
    ((-1717596440578773550012367 / 32620476643437121268700 : ℝ), 5, 1, 0, 0),
    ((772831487941128860127173 / 130481906573748485074800 : ℝ), 4, 2, 0, 0),
    ((-28019426671376466203426513 / 8155119160859280317175 : ℝ), 4, 0, 1, 0),
    ((-45323034814163455779024773 / 8155119160859280317175 : ℝ), 4, 0, 0, 1),
    ((-8579008759593453728247 / 2174698442895808084580 : ℝ), 3, 3, 0, 0),
    ((1837554232823499744611591 / 3262047664343712126870 : ℝ), 3, 1, 1, 0),
    ((149122146892415977370490281 / 32620476643437121268700 : ℝ), 3, 1, 0, 1),
    ((19467687796654542136311 / 43493968857916161691600 : ℝ), 2, 4, 0, 0),
    ((37734680606710195929632 / 2718373053619760105725 : ℝ), 2, 2, 1, 0),
    ((121878089031506804639387 / 1672844956073698526600 : ℝ), 2, 2, 0, 1),
    ((42072048834600400 / 3465684381913 : ℝ), 2, 0, 2, 0),
    ((-118571431865120687 / 6931368763826 : ℝ), 2, 0, 1, 1),
    ((-1140174403228477101 / 3465684381913 : ℝ), 2, 0, 0, 2),
    ((136273814576581794954177 / 5436746107239520211450 : ℝ), 1, 3, 1, 0),
    ((-12405153373612392439537 / 167284495607369852660 : ℝ), 1, 3, 0, 1),
    ((-2098086097370200 / 3465684381913 : ℝ), 1, 1, 2, 0),
    ((-61026292203961088 / 3465684381913 : ℝ), 1, 1, 1, 1),
    ((198610712146331196 / 3465684381913 : ℝ), 1, 1, 0, 2),
    ((19467687796654542136311 / 21746984428958080845800 : ℝ), 0, 4, 0, 1),
    ((-603269388140699 / 6931368763826 : ℝ), 0, 2, 1, 1),
    ((-2338640840510059 / 3465684381913 : ℝ), 0, 2, 0, 2), ((-370055000 / 110461 : ℝ), 0, 0, 2, 1),
    ((8487065000 / 110461 : ℝ), 0, 0, 1, 2), ((-2269950000 / 110461 : ℝ), 0, 0, 0, 3)]

/-- Monomials of weight 7 of the derivative along the Taylor truncation. -/
private def lieP5w7 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((4202848158343950202425011 / 260963813147496970149600 : ℝ), 7, 0, 0, 0),
    ((2764871946211917559934621 / 782891439442490910448800 : ℝ), 6, 1, 0, 0),
    ((-122424861521545425107147 / 260963813147496970149600 : ℝ), 5, 2, 0, 0),
    ((38664929012752439432721 / 749896014791657960200 : ℝ), 5, 0, 1, 0),
    ((379955434759049334483060593 / 86987937715832323383200 : ℝ), 5, 0, 0, 1),
    ((-20871207145332681552269 / 52192762629499394029920 : ℝ), 4, 3, 0, 0),
    ((-474198272707433218784581 / 6524095328687424253740 : ℝ), 4, 1, 1, 0),
    ((-4027619504375705989109299 / 20074139472884382319200 : ℝ), 4, 1, 0, 1),
    ((-6489229265551514045437 / 43493968857916161691600 : ℝ), 3, 4, 0, 0),
    ((1207822711117930624105291 / 65240953286874242537400 : ℝ), 3, 2, 1, 0),
    ((32836481501392595665394567 / 260963813147496970149600 : ℝ), 3, 2, 0, 1),
    ((-48595102226506850 / 10397053145739 : ℝ), 3, 0, 2, 0),
    ((-552963389508683261981365159 / 10873492214479040422900 : ℝ), 3, 0, 1, 1),
    ((756759668028353503732752743 / 17397587543166464676640 : ℝ), 3, 0, 0, 2),
    ((-136273814576581794954177 / 10873492214479040422900 : ℝ), 2, 3, 1, 0),
    ((-1706311689921320773389833 / 17397587543166464676640 : ℝ), 2, 3, 0, 1),
    ((1049043048685100 / 3465684381913 : ℝ), 2, 1, 2, 0),
    ((240352417078383137598624 / 18747400369791449005 : ℝ), 2, 1, 1, 1),
    ((1328355333896694435910007583 / 17397587543166464676640 : ℝ), 2, 1, 0, 2),
    ((19467687796654542136311 / 21746984428958080845800 : ℝ), 1, 4, 0, 1),
    ((389028082226528482832703 / 10873492214479040422900 : ℝ), 1, 2, 1, 1),
    ((-703968962635487573146921 / 17397587543166464676640 : ℝ), 1, 2, 0, 2),
    ((47877237244757900 / 3465684381913 : ℝ), 1, 0, 2, 1),
    ((-239467313191528593 / 6931368763826 : ℝ), 1, 0, 1, 2),
    ((-10484580760741102345 / 20794106291478 : ℝ), 1, 0, 0, 3),
    ((136273814576581794954177 / 5436746107239520211450 : ℝ), 0, 3, 1, 1),
    ((-257781038413224487354029 / 3479517508633292935328 : ℝ), 0, 3, 0, 2),
    ((-2098086097370200 / 3465684381913 : ℝ), 0, 1, 2, 1),
    ((-121512068854990041 / 6931368763826 : ℝ), 0, 1, 1, 2),
    ((1175513972692896215 / 20794106291478 : ℝ), 0, 1, 0, 3)]

/-- Monomials of weight 8 of the derivative along the Taylor truncation. -/
private def lieP5w8 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((29419937108407651416975077 / 195722859860622727612200 : ℝ), 6, 0, 1, 0),
    ((-298402219242420464372175781 / 782891439442490910448800 : ℝ), 6, 0, 0, 1),
    ((-111842594276935872193697 / 6524095328687424253740 : ℝ), 5, 1, 1, 0),
    ((5182294240239624794023807 / 86987937715832323383200 : ℝ), 5, 1, 0, 1),
    ((3005194392167135013643 / 2249688044374973880600 : ℝ), 4, 2, 1, 0),
    ((-1363281868825743879843121 / 260963813147496970149600 : ℝ), 4, 2, 0, 1),
    ((-6044476737407150 / 3465684381913 : ℝ), 4, 0, 2, 0),
    ((47766335060357640734671888 / 8155119160859280317175 : ℝ), 4, 0, 1, 1),
    ((730369188680652660402018451 / 130481906573748485074800 : ℝ), 4, 0, 0, 2),
    ((-45424604858860598318059 / 10873492214479040422900 : ℝ), 3, 3, 1, 0),
    ((37356825870463153580343 / 3479517508633292935328 : ℝ), 3, 3, 0, 1),
    ((1049043048685100 / 10397053145739 : ℝ), 3, 1, 2, 0),
    ((1479292783505713176205779 / 543674610723952021145 : ℝ), 3, 1, 1, 1),
    ((-392375191449360362667613161 / 43493968857916161691600 : ℝ), 3, 1, 0, 2),
    ((-19467687796654542136311 / 43493968857916161691600 : ℝ), 2, 4, 0, 1),
    ((280168018436270927177411 / 5436746107239520211450 : ℝ), 2, 2, 1, 1),
    ((1718878944439343443078377 / 5436746107239520211450 : ℝ), 2, 2, 0, 2),
    ((-30461672014285400 / 3465684381913 : ℝ), 2, 0, 2, 1),
    ((-1424213980066725085 / 13862737527652 : ℝ), 2, 0, 1, 2),
    ((1285987524312169241 / 10397053145739 : ℝ), 2, 0, 0, 3),
    ((-136273814576581794954177 / 5436746107239520211450 : ℝ), 1, 3, 1, 1),
    ((-1603363584806199328650869 / 8698793771583232338320 : ℝ), 1, 3, 0, 2),
    ((2098086097370200 / 3465684381913 : ℝ), 1, 1, 2, 1),
    ((284518078662921 / 11828274341 : ℝ), 1, 1, 1, 2),
    ((1463890923634755319 / 10397053145739 : ℝ), 1, 1, 0, 3),
    ((19467687796654542136311 / 43493968857916161691600 : ℝ), 0, 4, 0, 2),
    ((303542802802099 / 13862737527652 : ℝ), 0, 2, 1, 2),
    ((-602575450660901 / 10397053145739 : ℝ), 0, 2, 0, 3), ((185027500 / 110461 : ℝ), 0, 0, 2, 2),
    ((-107682500 / 25491 : ℝ), 0, 0, 1, 3), ((-25862000000 / 110461 : ℝ), 0, 0, 0, 4)]

/-- Monomials of weight 9 of the derivative along the Taylor truncation. -/
private def lieP5w9 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((29419937108407651416975077 / 65240953286874242537400 : ℝ), 5, 0, 1, 1),
    ((-323619308192484165586725847 / 260963813147496970149600 : ℝ), 5, 0, 0, 2),
    ((-111842594276935872193697 / 2174698442895808084580 : ℝ), 4, 1, 1, 1),
    ((41110904269732788026345021 / 260963813147496970149600 : ℝ), 4, 1, 0, 2),
    ((3005194392167135013643 / 749896014791657960200 : ℝ), 3, 2, 1, 1),
    ((-1118432145782653029628827 / 86987937715832323383200 : ℝ), 3, 2, 0, 2),
    ((-18133430212221450 / 3465684381913 : ℝ), 3, 0, 2, 1),
    ((1155628885612334255665220027 / 65240953286874242537400 : ℝ), 3, 0, 1, 2),
    ((-47494760248638191142392693 / 10438552525899878805984 : ℝ), 3, 0, 0, 3),
    ((-136273814576581794954177 / 10873492214479040422900 : ℝ), 2, 3, 1, 1),
    ((602094802347612666809683 / 17397587543166464676640 : ℝ), 2, 3, 0, 2),
    ((1049043048685100 / 3465684381913 : ℝ), 2, 1, 2, 1),
    ((18588067353206488679844813 / 2174698442895808084580 : ℝ), 2, 1, 1, 2),
    ((-1394862758963126698933058203 / 52192762629499394029920 : ℝ), 2, 1, 0, 3),
    ((-19467687796654542136311 / 43493968857916161691600 : ℝ), 1, 4, 0, 2),
    ((1033521436372236793313997 / 21746984428958080845800 : ℝ), 1, 2, 1, 2),
    ((2907423442621128576814315 / 10438552525899878805984 : ℝ), 1, 2, 0, 3),
    ((-12328241802063950 / 3465684381913 : ℝ), 1, 0, 2, 2),
    ((-35057940805254387 / 533182212602 : ℝ), 1, 0, 1, 3),
    ((2118131894468625605 / 20794106291478 : ℝ), 1, 0, 0, 4),
    ((-136273814576581794954177 / 10873492214479040422900 : ℝ), 0, 3, 1, 2),
    ((-1569047549767825513737881 / 17397587543166464676640 : ℝ), 0, 3, 0, 3),
    ((1049043048685100 / 3465684381913 : ℝ), 0, 1, 2, 2),
    ((18869539623503593 / 1599546637806 : ℝ), 0, 1, 1, 3),
    ((1424338880546750135 / 20794106291478 : ℝ), 0, 1, 0, 4)]

/-- Monomials of weight 10 of the derivative along the Taylor truncation. -/
private def lieP5w10 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((29419937108407651416975077 / 65240953286874242537400 : ℝ), 4, 0, 1, 2),
    ((-332025004509172065991575869 / 260963813147496970149600 : ℝ), 4, 0, 0, 3),
    ((-111842594276935872193697 / 2174698442895808084580 : ℝ), 3, 1, 1, 2),
    ((117802968916774528959165821 / 782891439442490910448800 : ℝ), 3, 1, 0, 3),
    ((3005194392167135013643 / 749896014791657960200 : ℝ), 2, 2, 1, 2),
    ((-3110446714304868238672187 / 260963813147496970149600 : ℝ), 2, 2, 0, 3),
    ((-18133430212221450 / 3465684381913 : ℝ), 2, 0, 2, 2),
    ((57779032920560777 / 3199093275612 : ℝ), 2, 0, 1, 3),
    ((-193365782890371605 / 20794106291478 : ℝ), 2, 0, 0, 4),
    ((-136273814576581794954177 / 10873492214479040422900 : ℝ), 1, 3, 1, 2),
    ((1848026821333503363533587 / 52192762629499394029920 : ℝ), 1, 3, 0, 3),
    ((1049043048685100 / 3465684381913 : ℝ), 1, 1, 2, 2),
    ((179689404280200647 / 20794106291478 : ℝ), 1, 1, 1, 3),
    ((-186631242942826165 / 6931368763826 : ℝ), 1, 1, 0, 4),
    ((-6489229265551514045437 / 43493968857916161691600 : ℝ), 0, 4, 0, 3),
    ((603269388140699 / 41588212582956 : ℝ), 0, 2, 1, 3),
    ((855394341441490 / 10397053145739 : ℝ), 0, 2, 0, 4), ((185027500 / 331383 : ℝ), 0, 0, 2, 3),
    ((-3457607500 / 331383 : ℝ), 0, 0, 1, 4), ((8368450000 / 331383 : ℝ), 0, 0, 0, 5)]

/-- Monomials of weight 11 of the derivative along the Taylor truncation. -/
private def lieP5w11 : List (ℝ × ℕ × ℕ × ℕ × ℕ) := [
  ((29419937108407651416975077 / 195722859860622727612200 : ℝ), 3, 0, 1, 3),
    ((-4202848158343950202425011 / 9786142993031136380610 : ℝ), 3, 0, 0, 4),
    ((-111842594276935872193697 / 6524095328687424253740 : ℝ), 2, 1, 1, 3),
    ((15977513468133696027671 / 326204766434371212687 : ℝ), 2, 1, 0, 4),
    ((3005194392167135013643 / 2249688044374973880600 : ℝ), 1, 2, 1, 3),
    ((-429313484595305001949 / 112484402218748694030 : ℝ), 1, 2, 0, 4),
    ((-6044476737407150 / 3465684381913 : ℝ), 1, 0, 2, 3),
    ((63978085665133850 / 10397053145739 : ℝ), 1, 0, 1, 4),
    ((-34766528739391000 / 10397053145739 : ℝ), 1, 0, 0, 5),
    ((-45424604858860598318059 / 10873492214479040422900 : ℝ), 0, 3, 1, 3),
    ((6489229265551514045437 / 543674610723952021145 : ℝ), 0, 3, 0, 4),
    ((1049043048685100 / 10397053145739 : ℝ), 0, 1, 2, 3),
    ((10007299205467900 / 3465684381913 : ℝ), 0, 1, 1, 4),
    ((-94340467056542000 / 10397053145739 : ℝ), 0, 1, 0, 5)]

/-- The monomials of weight five and more of the derivative along the Taylor truncation. -/
private def lieP5 (a b y1 y2 : ℝ) : ℝ :=
  poly4 lieP5w5 a b y1 y2 + poly4 lieP5w6 a b y1 y2 + poly4 lieP5w7 a b y1 y2 +
    poly4 lieP5w8 a b y1 y2 + poly4 lieP5w9 a b y1 y2 + poly4 lieP5w10 a b y1 y2 +
    poly4 lieP5w11 a b y1 y2

@[tmio M, powerlib_domain] private theorem lieG0_eq (a b y1 y2 : ℝ) :
    dpoly4 chetW a b y1 y2 (dirLam a b y1 y2 0) (dirLam a b y1 y2 1) (dirLam a b y1 y2 2)
      (dirLam a b y1 y2 3) = poly4 lieG0 a b y1 y2 := by
  simp only [chetW, lieG0, dirLam, dpoly4_cons, dpoly4_nil, poly4_cons, poly4_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  norm_num
  ring

@[tmio M, powerlib_domain] private theorem lieGC_eq (a b y1 y2 : ℝ) :
    dpoly4 chetW a b y1 y2 (dirMu a b y1 y2 0) (dirMu a b y1 y2 1) (dirMu a b y1 y2 2)
      (dirMu a b y1 y2 3) = poly4 lieGC a b y1 y2 := by
  simp only [chetW, lieGC, dirMu, dpoly4_cons, dpoly4_nil, poly4_cons, poly4_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  norm_num
  ring

@[tmio M, powerlib_domain] private theorem lieGS_eq (a b y1 y2 : ℝ) :
    dpoly4 chetW a b y1 y2 (dirNu a b y1 y2 0) (dirNu a b y1 y2 1) (dirNu a b y1 y2 2)
      (dirNu a b y1 y2 3) = poly4 lieGS a b y1 y2 := by
  simp only [chetW, lieGS, dirNu, dpoly4_cons, dpoly4_nil, poly4_cons, poly4_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  norm_num
  ring

/-- Along the Taylor truncation `cos δ − 1 ≈ −δ²/2`, `sin δ ≈ δ − δ³/6` (`δ = a + y₂`) the
derivative has no monomial of weight below four (weights `1` for `a, b` and `2` for `y`). -/
@[tmio M, powerlib_domain] private theorem lie_poly_eq (a b y1 y2 : ℝ) :
    poly4 lieG0 a b y1 y2 - (a + y2) ^ 2 / 2 * poly4 lieGC a b y1 y2 +
      ((a + y2) - (a + y2) ^ 3 / 6) * poly4 lieGS a b y1 y2 =
      poly4 lieP4 a b y1 y2 + lieP5 a b y1 y2 := by
  simp only [lieG0, lieGC, lieGS, lieP4, lieP5, lieP5w5, lieP5w6, lieP5w7, lieP5w8, lieP5w9,
    lieP5w10, lieP5w11, poly4_cons, poly4_nil]
  norm_num
  ring

/-- **The derivative of the Chetaev function along the field**: the weight-four part, the
monomials of weight five and more, and the Taylor remainders of `cos` and `sin`. -/
@[tmio M, powerlib_domain] private theorem lie_eq (x : State 4) :
    fderiv ℝ hopfChetaev x (hopfWitness.g.field x) =
      poly4 lieP4 (cA x) (cB x) (cY1 x) (cY2 x) + lieP5 (cA x) (cB x) (cY1 x) (cY2 x) +
        (Real.cos (x 0) - (1 - x 0 ^ 2 / 2)) * poly4 lieGC (cA x) (cB x) (cY1 x) (cY2 x) +
        (Real.sin (x 0) - (x 0 - x 0 ^ 3 / 6)) * poly4 lieGS (cA x) (cB x) (cY1 x) (cY2 x) := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_poly4 chetW cA cB cY1 cY2 x
  rw [show hopfChetaev = fun x => poly4 chetW (cA x) (cB x) (cY1 x) (cY2 x) from
    funext hopfChetaev_eq, hL.fderiv, hLv]
  have e0 := field_coords x 0
  have e1 := field_coords x 1
  have e2 := field_coords x 2
  have e3 := field_coords x 3
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e0 e1 e2 e3
  rw [e0, e1, e2, e3, dpoly4_add_smul, dpoly4_add_smul, lieG0_eq, lieGC_eq, lieGS_eq]
  have hP := lie_poly_eq (cA x) (cB x) (cY1 x) (cY2 x)
  rw [(state_eq x).1]
  linear_combination hP

/-! ## The weight-four part is positive definite -/

/-- The weight-four part: `κ (a² + b²)² + q₁(a, b) v₁ + q₂(a, b) v₂ + c |v|²`, `v = y − H(a, b)`,
`κ = ℓ₁/2 = 739091/156873665`. -/
@[tmio M, powerlib_domain] private theorem lieP4_eq (a b y1 y2 : ℝ) :
    poly4 lieP4 a b y1 y2 = 739091 / 156873665 * (a ^ 2 + b ^ 2) ^ 2 +
      (224 / 3809 * a ^ 2 - 30912 / 3809 * (a * b)) * (y1 - cmH1 a b) +
      (464 / 3809 * a ^ 2 + 88336 / 3809 * (a * b) - 1104 / 3809 * b ^ 2) * (y2 - cmH2 a b) +
      250000 * ((y1 - cmH1 a b) ^ 2 + (y2 - cmH2 a b) ^ 2) := by
  simp only [lieP4, cmH1, cmH2, poly4_cons, poly4_nil]
  norm_num
  ring

@[tmio M, powerlib_domain] private theorem quad_nonneg {ρ q v : ℝ} (hq : q ^ 2 ≤ 169 * ρ ^ 2) :
    0 ≤ 739091 / 156873665 / 4 * ρ ^ 2 + q * v +
      (250000 - 739091 / 156873665 / 2) * v ^ 2 := by
  nlinarith [sq_nonneg (2 * (250000 - 739091 / 156873665 / 2) * v + q), sq_nonneg ρ]

@[tmio M, powerlib_domain] private theorem lieP4_ge (a b y1 y2 : ℝ) :
    739091 / 156873665 / 2 * (a ^ 4 + b ^ 4 + (y1 - cmH1 a b) ^ 2 + (y2 - cmH2 a b) ^ 2) ≤
      poly4 lieP4 a b y1 y2 := by
  rw [lieP4_eq]
  have hρ : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hq1 : (224 / 3809 * a ^ 2 - 30912 / 3809 * (a * b)) ^ 2 ≤ 169 * (a ^ 2 + b ^ 2) ^ 2 := by
    have h : |224 / 3809 * a ^ 2 - 30912 / 3809 * (a * b)| ≤ 13 * (a ^ 2 + b ^ 2) :=
      abs_le.mpr ⟨by nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)],
        by nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]⟩
    have := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at this
    nlinarith
  have hq2 : (464 / 3809 * a ^ 2 + 88336 / 3809 * (a * b) - 1104 / 3809 * b ^ 2) ^ 2 ≤
      169 * (a ^ 2 + b ^ 2) ^ 2 := by
    have h : |464 / 3809 * a ^ 2 + 88336 / 3809 * (a * b) - 1104 / 3809 * b ^ 2| ≤
        13 * (a ^ 2 + b ^ 2) :=
      abs_le.mpr ⟨by nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)],
        by nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]⟩
    have := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at this
    nlinarith
  have h1 := quad_nonneg (v := y1 - cmH1 a b) hq1
  have h2 := quad_nonneg (v := y2 - cmH2 a b) hq2
  have h4 : a ^ 4 + b ^ 4 ≤ (a ^ 2 + b ^ 2) ^ 2 := by nlinarith [sq_nonneg (a * b)]
  nlinarith

/-! ## The weighted size -/

/-- `t⁴ = a⁴ + b⁴ + v₁² + v₂²`, `v = y − H(a, b)`. -/
private def theta (x : State 4) : ℝ :=
  cA x ^ 4 + cB x ^ 4 + (cY1 x - cmH1 (cA x) (cB x)) ^ 2 + (cY2 x - cmH2 (cA x) (cB x)) ^ 2

/-- The weighted size `t = θ^{1/4}`: `a, b = O(t)`, `y = O(t²)`. -/
private def size (x : State 4) : ℝ := √(√(theta x))

@[tmio M, powerlib_domain] private theorem size_bounds (x : State 4) :
    0 ≤ size x ∧ size x ^ 4 = theta x ∧ |cA x| ≤ size x ∧ |cB x| ≤ size x ∧
      |cY1 x| ≤ 3 * size x ^ 2 ∧ |cY2 x| ≤ 3 * size x ^ 2 := by
  have hθ : 0 ≤ theta x := by unfold theta; positivity
  have hs0 : 0 ≤ size x := Real.sqrt_nonneg _
  have h4 : size x ^ 4 = theta x := by
    rw [size, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hθ]
  have hle4 : ∀ u : ℝ, u ^ 4 ≤ theta x → |u| ≤ size x := fun u hu => by
    rw [← pow_le_pow_iff_left₀ (abs_nonneg u) hs0 (by norm_num : (4 : ℕ) ≠ 0), h4,
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    exact hu
  have hle2 : ∀ u : ℝ, u ^ 2 ≤ theta x → |u| ≤ size x ^ 2 := fun u hu => by
    rw [← pow_le_pow_iff_left₀ (abs_nonneg u) (by positivity) (by norm_num : (2 : ℕ) ≠ 0),
      sq_abs, ← pow_mul, h4]
    exact hu
  have hA : |cA x| ≤ size x := hle4 _ (by unfold theta; nlinarith [sq_nonneg (cB x ^ 2)])
  have hB : |cB x| ≤ size x := hle4 _ (by unfold theta; nlinarith [sq_nonneg (cA x ^ 2)])
  have hv1 := hle2 (cY1 x - cmH1 (cA x) (cB x)) (by
    unfold theta; nlinarith [sq_nonneg (cA x ^ 2), sq_nonneg (cB x ^ 2)])
  have hv2 := hle2 (cY2 x - cmH2 (cA x) (cB x)) (by
    unfold theta; nlinarith [sq_nonneg (cA x ^ 2), sq_nonneg (cB x ^ 2)])
  obtain ⟨hH1, hH2⟩ := abs_cmH_le (cA x) (cB x)
  have ha2 : cA x ^ 2 ≤ size x ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hb2 : cB x ^ 2 ≤ size x ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  have t1 := abs_sub_abs_le_abs_sub (cY1 x) (cmH1 (cA x) (cB x))
  have t2 := abs_sub_abs_le_abs_sub (cY2 x) (cmH2 (cA x) (cB x))
  exact ⟨hs0, h4, hA, hB, by linarith, by linarith⟩

@[tmio M, powerlib_domain] private theorem tendsto_size : Tendsto size (𝓝 0) (𝓝 0) := by
  have hc : Continuous size := by
    unfold size theta cmH1 cmH2
    fun_prop
  have h0 : size 0 = 0 := by simp [size, theta, cmH1, cmH2]
  simpa [h0] using hc.tendsto 0

@[tmio M, powerlib_domain] private theorem size_pos {x : State 4} (hx : x ≠ 0) : 0 < size x := by
  obtain ⟨hs0, h4, -⟩ := size_bounds x
  refine lt_of_le_of_ne hs0 fun h => hx ?_
  have hθ : theta x = 0 := by rw [← h4, ← h, zero_pow (by norm_num)]
  unfold theta at hθ
  have p1 : 0 ≤ cA x ^ 4 := by positivity
  have p2 : 0 ≤ cB x ^ 4 := by positivity
  have p3 : 0 ≤ (cY1 x - cmH1 (cA x) (cB x)) ^ 2 := by positivity
  have p4 : 0 ≤ (cY2 x - cmH2 (cA x) (cB x)) ^ 2 := by positivity
  have ha : cA x = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp (by linarith)
  have hb : cB x = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp (by linarith)
  have hy1 : cY1 x - cmH1 (cA x) (cB x) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (by linarith)
  have hy2 : cY2 x - cmH2 (cA x) (cB x) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (by linarith)
  rw [ha, hb] at hy1 hy2
  simp only [cmH1, cmH2] at hy1 hy2
  norm_num at hy1 hy2
  obtain ⟨e0, e1, e2, e3⟩ := state_eq x
  ext i
  fin_cases i <;> simp [e0, e1, e2, e3, ha, hb, hy1, hy2]

/-! ## The derivative is positive near the operating point -/

@[tmio M, powerlib_domain] private theorem eventually_lie_ge :
    ∀ᶠ x in 𝓝 (0 : State 4), 739091 / 156873665 / 4 * size x ^ 4 ≤
      fderiv ℝ hopfChetaev x (hopfWitness.g.field x) := by
  have hs := tendsto_size
  have hbd := fun x => size_bounds x
  have hsn : ∀ x, ‖size x‖ = size x := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbd x).1]
  have ha : (fun x => cA x) =O[𝓝 0] size := IsBigO.of_bound 1 (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, hsn, one_mul]; exact (hbd x).2.2.1)
  have hb : (fun x => cB x) =O[𝓝 0] size := IsBigO.of_bound 1 (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, hsn, one_mul]; exact (hbd x).2.2.2.1)
  have hy1 : (fun x => cY1 x) =O[𝓝 0] fun x => size x ^ 2 := IsBigO.of_bound 3
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, norm_pow, hsn]; exact (hbd x).2.2.2.2.1)
  have hy2 : (fun x => cY2 x) =O[𝓝 0] fun x => size x ^ 2 := IsBigO.of_bound 3
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, norm_pow, hsn]; exact (hbd x).2.2.2.2.2)
  have w := fun (L : List (ℝ × ℕ × ℕ × ℕ × ℕ)) {k : ℕ}
    (hL : ∀ t ∈ L, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2.1 + 2 * t.2.2.2.2) =>
    isBigO_poly4_weight hs ha hb hy1 hy2 L hL
  have hP5 : (fun x => lieP5 (cA x) (cB x) (cY1 x) (cY2 x)) =O[𝓝 0] fun x => size x ^ 5 :=
    ((((((w lieP5w5 (by simp [lieP5w5])).add (w lieP5w6 (by simp [lieP5w6]))).add
      (w lieP5w7 (by simp [lieP5w7]))).add (w lieP5w8 (by simp [lieP5w8]))).add
      (w lieP5w9 (by simp [lieP5w9]))).add (w lieP5w10 (by simp [lieP5w10]))).add
      (w lieP5w11 (by simp [lieP5w11]))
  have hGC : (fun x => poly4 lieGC (cA x) (cB x) (cY1 x) (cY2 x)) =O[𝓝 0]
      fun x => size x ^ 1 := w lieGC (by simp [lieGC])
  have hGS : (fun x => poly4 lieGS (cA x) (cB x) (cY1 x) (cY2 x)) =O[𝓝 0]
      fun x => size x ^ 1 := w lieGS (by simp [lieGS])
  have hδ : (fun x : State 4 => x 0) =O[𝓝 0] fun x => size x ^ 1 := by
    have h2 : (fun x => cY2 x) =O[𝓝 0] fun x => size x ^ 1 :=
      hy2.trans (Dynamics.isBigO_pow_of_tendsto hs (by norm_num))
    refine ((ha.congr_right fun x => (pow_one (size x)).symm).add h2).congr_left fun x => ?_
    exact ((state_eq x).1).symm
  have hball : ∀ᶠ x in 𝓝 (0 : State 4), |x 0| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : State 4) one_pos] with x hx
    have h1 := PiLp.norm_apply_le x 0
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [Real.norm_eq_abs] at h1
    linarith
  have hEc : (fun x : State 4 => Real.cos (x 0) - (1 - x 0 ^ 2 / 2)) =O[𝓝 0]
      fun x => size x ^ 4 := by
    refine (IsBigO.of_bound (5 / 96) (hball.mono fun x hx => ?_)).trans
      ((hδ.pow 4).congr_right fun x => by rw [← pow_mul])
    rw [Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
    have := Real.cos_bound hx
    linarith
  have hEs : (fun x : State 4 => Real.sin (x 0) - (x 0 - x 0 ^ 3 / 6)) =O[𝓝 0]
      fun x => size x ^ 4 := by
    refine (IsBigO.of_bound (1 / 100) (hball.mono fun x hx => ?_)).trans
      ((hδ.pow 4).congr_right fun x => by rw [← pow_mul])
    rw [Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
    have h1 := Real.sin_bound hx
    have h2 : |x 0| ^ 5 ≤ |x 0| ^ 4 := pow_le_pow_of_le_one (abs_nonneg _) hx (by norm_num)
    linarith
  have hR : (fun x => lieP5 (cA x) (cB x) (cY1 x) (cY2 x) +
      (Real.cos (x 0) - (1 - x 0 ^ 2 / 2)) * poly4 lieGC (cA x) (cB x) (cY1 x) (cY2 x) +
      (Real.sin (x 0) - (x 0 - x 0 ^ 3 / 6)) * poly4 lieGS (cA x) (cB x) (cY1 x) (cY2 x))
      =O[𝓝 0] fun x => size x ^ 5 :=
    (hP5.add ((hEc.mul hGC).congr_right fun x => by ring)).add
      ((hEs.mul hGS).congr_right fun x => by ring)
  have hRo := hR.trans_isLittleO (Dynamics.isLittleO_pow_of_tendsto hs (by norm_num : 4 < 5))
  filter_upwards [hRo.bound (by norm_num : (0 : ℝ) < 739091 / 156873665 / 4)] with x hx
  rw [lie_eq]
  have h1 := lieP4_ge (cA x) (cB x) (cY1 x) (cY2 x)
  have h4 := (hbd x).2.1
  unfold theta at h4
  rw [norm_pow, hsn] at hx
  have h5 := neg_abs_le (lieP5 (cA x) (cB x) (cY1 x) (cY2 x) +
      (Real.cos (x 0) - (1 - x 0 ^ 2 / 2)) * poly4 lieGC (cA x) (cB x) (cY1 x) (cY2 x) +
      (Real.sin (x 0) - (x 0 - x 0 ^ 3 / 6)) * poly4 lieGS (cA x) (cB x) (cY1 x) (cY2 x))
  rw [Real.norm_eq_abs] at hx
  nlinarith

end HopfLine

open HopfLine

/-! ## Instability of the witness -/

@[tmio M, powerlib_domain] private theorem hopfWitness_field_eq :
    hopfWitness.field = hopfWitness.g.field := by
  funext z
  simp [Model.field, hopfWitness_point]

/-- **The Chetaev function increases near the operating point**: its derivative along the field
of the witness is positive on a punctured neighbourhood of the origin (it is at least
`(ℓ₁/8) t⁴` for the weighted size `t⁴ = a⁴ + b⁴ + |y − H(a, b)|²`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem hopfChetaev_lie_pos :
    ∀ᶠ x in 𝓝[≠] (0 : State 4), 0 < fderiv ℝ hopfChetaev x (hopfWitness.field x) := by
  rw [hopfWitness_field_eq]
  filter_upwards [nhdsWithin_le_nhds eventually_lie_ge, self_mem_nhdsWithin] with x hx hne
  have := size_pos hne
  have : 0 < 739091 / 156873665 / 4 * size x ^ 4 := by positivity
  linarith

/-- The Chetaev function takes positive values arbitrarily close to the operating point (on the
centre direction `x = s Re q`, `W = s² + O(s³)`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfChetaev_seed :
    ∀ ε > 0, ∃ x : State 4, ‖x‖ < ε ∧ 0 < hopfChetaev x := by
  intro ε hε
  set e : State 4 := WithLp.toLp 2 ![1, 0, 7 / 4, 3 / 4] with he
  set s := min (ε / (‖e‖ + 1)) (1 / 1000) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by norm_num)
  have hs1 : s ≤ 1 / 1000 := min_le_right _ _
  have hs2 : s * (‖e‖ + 1) ≤ ε := by
    have := min_le_left (ε / (‖e‖ + 1)) (1 / 1000)
    rwa [← hs, le_div_iff₀ (by positivity)] at this
  refine ⟨s • e, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith [norm_nonneg e]
  · obtain ⟨h1, h2, h3, h4⟩ := coords_apply (s • e)
    have ea : cA (s • e) = s := by rw [h1]; simp [he]; ring
    have eb : cB (s • e) = 0 := by rw [h2]; simp [he]; ring
    have ey1 : cY1 (s • e) = 0 := by rw [h3]; simp [he]; ring
    have ey2 : cY2 (s • e) = 0 := by rw [h4]; simp [he]; ring
    rw [hopfChetaev_eq, ea, eb, ey1, ey2]
    simp only [chetW, poly4_cons, poly4_nil]
    norm_num
    have q1 : s ^ 2 ≤ 1 / 1000000 := by nlinarith
    have q2 : s ^ 4 ≤ s ^ 2 / 1000000 := by nlinarith [sq_nonneg s]
    have q3 : 0 < s ^ 3 := by positivity
    have q4 : 0 < s ^ 2 := by positivity
    nlinarith

/-- The operating point of the witness is unstable for its field (Chetaev). -/
@[tmio TM, powerlib_domain] private theorem unstable_witness :
    Unstable hopfWitness.g.field hopfWitness.point := by
  rw [hopfWitness_point]
  have hlie := hopfChetaev_lie_pos
  rw [hopfWitness_field_eq] at hlie
  obtain ⟨r, hr, hball⟩ := Dynamics.exists_radius_of_eventually hlie
  refine Dynamics.unstable_of_chetaev hopfWitness.g.contDiff_field contDiff_hopfChetaev
    (half_pos hr) (fun ε hε => ?_) fun x hx hWx => ?_
  · obtain ⟨x, hx, hW⟩ := hopfChetaev_seed ε hε
    exact ⟨x, by rwa [sub_zero], hW⟩
  · have hne : x ≠ 0 := by
      rintro rfl
      rw [hopfChetaev_zero] at hWx
      exact lt_irrefl 0 hWx
    exact hball x (by linarith) hne

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.g.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.g.field) (pt := Model.point)
    family_isAutonomous

/-- **The subcritical Hopf point is unstable**: the witness (`E = V = 1`, `R = 1/5`, `L = 1/10`,
`ω₀ = 5`, `M = 7/4`, `D = 1/4`, `P_ref = 0`), whose linearization has the eigenvalues `±i` and a
stable pair and whose first Lyapunov coefficient is `ℓ₁ = 1478182/156873665 > 0`, is unstable
(Chetaev's theorem with `hopfChetaev`). -/
@[tmio TM, powerlib_domain] theorem hopfWitness_mem_den_unstable :
    connection% (hopfWitness ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff']
  exact unstable_witness

@[tmio M, powerlib_domain] private theorem hopfWitness_not_routhViolation :
    ¬ hopfWitness.RouthViolation := by
  have hQ : hopfWitness.Q = 0 := by
    norm_num [Model.Q, Network.qssReactive, hopfWitness, Network.is, Network.reactive_eq]
  have h3 : hopfWitness.g.coeff3 = 29 / 7 := by
    norm_num [coeff3, hopfWitness, Network.σ]
  have h2 : hopfWitness.g.coeff2 hopfWitness.Q = 207 / 7 := by
    rw [hQ]; norm_num [coeff2, hopfWitness, Network.ρ, Network.σ, Network.X]
  have h1 : hopfWitness.g.coeff1 hopfWitness.Q = 29 / 7 := by
    rw [hQ]; norm_num [coeff1, hopfWitness, Network.ρ, Network.σ, Network.X]
  have h0 : hopfWitness.g.coeff0 hopfWitness.Q = 200 / 7 := by
    rw [hQ]; norm_num [coeff0, hopfWitness, Network.ρ, Network.σ, Network.X]
  rw [Model.RouthViolation, h3, h2, h1, h0]
  norm_num

/-- **The instability translation is not exact within physical models**: it asks for a strict
violation of the quartic Routh conditions, but the witness lies on the Routh boundary
(`a₃ a₂ a₁ = a₁² + a₃² a₀`) and is unstable (`hopfWitness_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_unstable :
    connection% (¬ family.ExactUnder {.physical} (.flow .unstable)) := by
  have hmem := hopfWitness_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine Spectral.not_exactUnder_of_witness ?_ hmem (q := .destabilizing) ?_ ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hopfWitness_meets.2
  · simp [family, translate, Spectral.localTable, Spectral.table]
  · exact hopfWitness_not_routhViolation

end VSM
end powerlib.GFM.Line
