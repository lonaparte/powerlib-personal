import theorem.Criteria.RouthComplex

/-! # The Bilharz determinants of complex cubics, quartics and quintics (foundation)

Routh–Hurwitz for complex polynomials in determinant form (Bilharz): a complex polynomial is
Hurwitz iff the even-order leading principal minors `Δ₂, Δ₄, …, Δ_{2n}` of its Bilharz matrix are
positive. The determinants are given here as explicit polynomials in the real and imaginary parts
of the coefficients, so that the criterion of a model with symbolic parameters is a list of
explicit polynomial inequalities in those parameters.

Scope.
* Static algebra of complex polynomials of degree 3 and 4 (any nonzero complex leading
  coefficient) and 5 (monic). "Hurwitz" means every root has negative real part. No model family
  is defined.

Source: H. Bilharz, *Z. Angew. Math. Mech.* 24 (1944) 77–82 (the determinant criterion for complex
coefficients); E. Frank, *Bull. Amer. Math. Soc.* 52 (1946) 144–157; M. Marden, *Geometry of
Polynomials* (1966), §40. The Bilharz matrix of `f` of degree `n`: write `j^{−n} f(j y) = P(y) +
j Q(y)` with real `P, Q`; its rows are the coefficient rows of `P` and `−Q` (leading coefficient
first), the `k`-th pair shifted by `k − 1` places. The determinants were expanded by exact
fraction-free elimination over `ℤ[x, y]` (computer algebra, discovery evidence) and every identity
used below is checked here by `ring`. The proof is the complex Routh step
(`Criteria.hurwitz_iff_routhStepC`): it is a row elimination of the Bilharz matrix, so the
determinants of `f` are those of its Routh-reduced polynomial times powers of `Re a_{n−1}`, and
multiplying a polynomial by `c ≠ 0` multiplies `Δ_{2k}` by `|c|^{2k}`.

Results.
* Polynomials (`BilharzPoly`, in the parts `cr, ci, x_k, y_k` of `c` and `a_k = x_k + j y_k`):
  `cubic2`, `cubic4`, `cubic6` (`c s³ + a₂ s² + a₁ s + a₀`; 2, 11, 34 terms), `quartic2`, …,
  `quartic8` (`c s⁴ + a₃ s³ + … + a₀`; 2, 11, 72, 219 terms), `quintic2`, …, `quintic10`
  (`s⁵ + a₄ s⁴ + … + a₀`; 1, 4, 28, 181, 549 terms; the larger ones are sums of parts of at most
  40 terms). Their complex forms `cubicBilharz2` … `quinticBilharz10`.
* **Complex cubic, complex leading coefficient**: `complexCubicHom_roots_re_neg_iff` (`c ≠ 0`);
  for `c = 1` the three determinants are the conditions of
  `Criteria.complexCubic_roots_re_neg_iff` (`Δ₆ = complexCubicDet`).
* **Complex quartic**: `complexQuartic_roots_re_neg_iff` (monic: `Δ₂ = Re a₃`, `Δ₄`, `Δ₆`, `Δ₈`
  positive) and `complexQuarticHom_roots_re_neg_iff` (`c ≠ 0`).
* **Complex quintic**: `complexQuintic_roots_re_neg_iff` (monic: `Δ₂ = Re a₄`, `Δ₄`, …, `Δ₁₀`
  positive).

Family and connection conclusions.
* None: static algebra. Model families read the criteria through their characteristic
  polynomials (`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayerRouth.lean`).
-/

noncomputable section
namespace powerlib.Criteria
open Polynomial
open scoped ComplexConjugate

/-! ## The determinants as polynomials -/

namespace BilharzPoly

/-- The Bilharz determinant `Δ₂` of the cubic `c s³ + a₂ s² + a₁ s + a₀`, `c = cr + j ci`,
in the real and imaginary parts of the coefficients (2 terms). -/
def cubic2 (cr ci x2 y2 _x1 _y1 _x0 _y0 : ℝ) : ℝ :=
  cr * x2 + ci * y2

/-- The Bilharz determinant `Δ₄` of the cubic `c s³ + a₂ s² + a₁ s + a₀`, `c = cr + j ci`,
in the real and imaginary parts of the coefficients (11 terms). -/
def cubic4 (cr ci x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -cr ^ 2 * x2 * x0 - cr ^ 2 * y1 ^ 2 - cr * ci * x2 * y0 - cr * ci * y2 * x0
  + 2 * cr * ci * x1 * y1 + cr * x2 ^ 2 * x1 + cr * x2 * y2 * y1 - ci ^ 2 * y2 * y0
  - ci ^ 2 * x1 ^ 2 + ci * x2 * y2 * x1 + ci * y2 ^ 2 * y1

/-- The Bilharz determinant `Δ₆` of the cubic `c s³ + a₂ s² + a₁ s + a₀`, `c = cr + j ci`,
in the real and imaginary parts of the coefficients (34 terms). -/
def cubic6 (cr ci x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  cr ^ 3 * x0 ^ 3 + 3 * cr ^ 2 * ci * x0 ^ 2 * y0 - 2 * cr ^ 2 * x2 * x1 * x0 ^ 2
  - 3 * cr ^ 2 * x2 * y1 * x0 * y0 + cr ^ 2 * y2 * y1 * x0 ^ 2 - cr ^ 2 * x1 * y1 ^ 2 * x0
  - cr ^ 2 * y1 ^ 3 * y0 + 3 * cr * ci ^ 2 * x0 * y0 ^ 2 - cr * ci * x2 * x1 * x0 * y0
  - 3 * cr * ci * x2 * y1 * y0 ^ 2 - 3 * cr * ci * y2 * x1 * x0 ^ 2
  - cr * ci * y2 * y1 * x0 * y0 + 2 * cr * ci * x1 ^ 2 * y1 * x0
  + 2 * cr * ci * x1 * y1 ^ 2 * y0 - cr * x2 ^ 3 * y0 ^ 2 + 2 * cr * x2 ^ 2 * y2 * x0 * y0
  + cr * x2 ^ 2 * x1 ^ 2 * x0 + cr * x2 ^ 2 * x1 * y1 * y0 - cr * x2 * y2 ^ 2 * x0 ^ 2
  + cr * x2 * y2 * x1 * y1 * x0 + cr * x2 * y2 * y1 ^ 2 * y0 + ci ^ 3 * y0 ^ 3
  + ci ^ 2 * x2 * x1 * y0 ^ 2 - 3 * ci ^ 2 * y2 * x1 * x0 * y0 - 2 * ci ^ 2 * y2 * y1 * y0 ^ 2
  - ci ^ 2 * x1 ^ 3 * x0 - ci ^ 2 * x1 ^ 2 * y1 * y0 - ci * x2 ^ 2 * y2 * y0 ^ 2
  + 2 * ci * x2 * y2 ^ 2 * x0 * y0 + ci * x2 * y2 * x1 ^ 2 * x0 + ci * x2 * y2 * x1 * y1 * y0
  - ci * y2 ^ 3 * x0 ^ 2 + ci * y2 ^ 2 * x1 * y1 * x0 + ci * y2 ^ 2 * y1 ^ 2 * y0

/-- The Bilharz determinant `Δ₂` of the quartic `c s⁴ + a₃ s³ + … + a₀`, `c = cr + j ci`,
in the real and imaginary parts of the coefficients (2 terms). -/
def quartic2 (cr ci x3 y3 _x2 _y2 _x1 _y1 _x0 _y0 : ℝ) : ℝ :=
  cr * x3 + ci * y3

/-- The Bilharz determinant `Δ₄` of the quartic `c s⁴ + a₃ s³ + … + a₀`, `c = cr + j ci`,
in the real and imaginary parts of the coefficients (11 terms). -/
def quartic4 (cr ci x3 y3 x2 y2 x1 y1 _x0 _y0 : ℝ) : ℝ :=
  -cr ^ 2 * x3 * x1 - cr ^ 2 * y2 ^ 2 - cr * ci * x3 * y1 - cr * ci * y3 * x1
  + 2 * cr * ci * x2 * y2 + cr * x3 ^ 2 * x2 + cr * x3 * y3 * y2 - ci ^ 2 * y3 * y1
  - ci ^ 2 * x2 ^ 2 + ci * x3 * y3 * x2 + ci * y3 ^ 2 * y2

/-- Terms 1–40 of `quartic6`. -/
def quartic6_0 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -cr ^ 3 * x3 * y0 ^ 2 + 2 * cr ^ 3 * y2 * x1 * y0 + cr ^ 3 * x1 ^ 3
  + 2 * cr ^ 2 * ci * x3 * x0 * y0 - cr ^ 2 * ci * y3 * y0 ^ 2 - 2 * cr ^ 2 * ci * x2 * x1 * y0
  - 2 * cr ^ 2 * ci * y2 * x1 * x0 + 2 * cr ^ 2 * ci * y2 * y1 * y0
  + 3 * cr ^ 2 * ci * x1 ^ 2 * y1 + cr ^ 2 * x3 ^ 2 * x1 * x0 + 2 * cr ^ 2 * x3 ^ 2 * y1 * y0
  - cr ^ 2 * x3 * y3 * x1 * y0 - 2 * cr ^ 2 * x3 * x2 * x1 ^ 2 + cr ^ 2 * x3 * y2 ^ 2 * x0
  - 3 * cr ^ 2 * x3 * y2 * x1 * y1 + cr ^ 2 * y3 * y2 ^ 2 * y0 + cr ^ 2 * y3 * y2 * x1 ^ 2
  - cr ^ 2 * x2 * y2 ^ 2 * x1 - cr ^ 2 * y2 ^ 3 * y1 - cr * ci ^ 2 * x3 * x0 ^ 2
  + 2 * cr * ci ^ 2 * y3 * x0 * y0 + 2 * cr * ci ^ 2 * x2 * x1 * x0
  - 2 * cr * ci ^ 2 * x2 * y1 * y0 - 2 * cr * ci ^ 2 * y2 * y1 * x0
  + 3 * cr * ci ^ 2 * x1 * y1 ^ 2 - cr * ci * x3 ^ 2 * y1 * x0 + 3 * cr * ci * x3 * y3 * x1 * x0
  + 3 * cr * ci * x3 * y3 * y1 * y0 - 2 * cr * ci * x3 * x2 * y2 * x0
  - cr * ci * x3 * x2 * x1 * y1 - 3 * cr * ci * x3 * y2 * y1 ^ 2 - cr * ci * y3 ^ 2 * x1 * y0
  - 2 * cr * ci * y3 * x2 * y2 * y0 - 3 * cr * ci * y3 * x2 * x1 ^ 2
  - cr * ci * y3 * y2 * x1 * y1 + 2 * cr * ci * x2 ^ 2 * y2 * x1
  + 2 * cr * ci * x2 * y2 ^ 2 * y1 - cr * x3 ^ 3 * x2 * x0 - cr * x3 ^ 3 * y1 ^ 2
  - cr * x3 ^ 2 * y3 * x2 * y0

/-- Terms 41–72 of `quartic6`. -/
def quartic6_1 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -cr * x3 ^ 2 * y3 * y2 * x0 + 2 * cr * x3 ^ 2 * y3 * x1 * y1 + cr * x3 ^ 2 * x2 ^ 2 * x1
  + cr * x3 ^ 2 * x2 * y2 * y1 - cr * x3 * y3 ^ 2 * y2 * y0 - cr * x3 * y3 ^ 2 * x1 ^ 2
  + cr * x3 * y3 * x2 * y2 * x1 + cr * x3 * y3 * y2 ^ 2 * y1 - ci ^ 3 * y3 * x0 ^ 2
  + 2 * ci ^ 3 * x2 * y1 * x0 + ci ^ 3 * y1 ^ 3 - ci ^ 2 * x3 * y3 * y1 * x0
  + ci ^ 2 * x3 * x2 ^ 2 * x0 + ci ^ 2 * x3 * x2 * y1 ^ 2 + 2 * ci ^ 2 * y3 ^ 2 * x1 * x0
  + ci ^ 2 * y3 ^ 2 * y1 * y0 + ci ^ 2 * y3 * x2 ^ 2 * y0 - 3 * ci ^ 2 * y3 * x2 * x1 * y1
  - 2 * ci ^ 2 * y3 * y2 * y1 ^ 2 - ci ^ 2 * x2 ^ 3 * x1 - ci ^ 2 * x2 ^ 2 * y2 * y1
  - ci * x3 ^ 2 * y3 * x2 * x0 - ci * x3 ^ 2 * y3 * y1 ^ 2 - ci * x3 * y3 ^ 2 * x2 * y0
  - ci * x3 * y3 ^ 2 * y2 * x0 + 2 * ci * x3 * y3 ^ 2 * x1 * y1 + ci * x3 * y3 * x2 ^ 2 * x1
  + ci * x3 * y3 * x2 * y2 * y1 - ci * y3 ^ 3 * y2 * y0 - ci * y3 ^ 3 * x1 ^ 2
  + ci * y3 ^ 2 * x2 * y2 * x1 + ci * y3 ^ 2 * y2 ^ 2 * y1

/-- The Bilharz determinant `Δ₆` of the quartic `c s⁴ + a₃ s³ + … + a₀`, `c = cr + j ci`,
in the real and imaginary parts of the coefficients (72 terms, 2 parts). -/
def quartic6 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  quartic6_0 cr ci x3 y3 x2 y2 x1 y1 x0 y0 + quartic6_1 cr ci x3 y3 x2 y2 x1 y1 x0 y0

/-- Terms 1–40 of `quartic8`. -/
def quartic8_0 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  cr ^ 4 * y0 ^ 4 - 4 * cr ^ 3 * ci * x0 * y0 ^ 3 - 4 * cr ^ 3 * x3 * x1 * x0 * y0 ^ 2
  - 3 * cr ^ 3 * x3 * y1 * y0 ^ 3 - cr ^ 3 * y3 * x1 * y0 ^ 3 - 2 * cr ^ 3 * x2 * y2 * y0 ^ 3
  - cr ^ 3 * x2 * x1 ^ 2 * y0 ^ 2 + 2 * cr ^ 3 * y2 ^ 2 * x0 * y0 ^ 2
  + 4 * cr ^ 3 * y2 * x1 ^ 2 * x0 * y0 + 3 * cr ^ 3 * y2 * x1 * y1 * y0 ^ 2
  + cr ^ 3 * x1 ^ 4 * x0 + cr ^ 3 * x1 ^ 3 * y1 * y0 + 6 * cr ^ 2 * ci ^ 2 * x0 ^ 2 * y0 ^ 2
  + 8 * cr ^ 2 * ci * x3 * x1 * x0 ^ 2 * y0 + 5 * cr ^ 2 * ci * x3 * y1 * x0 * y0 ^ 2
  - cr ^ 2 * ci * y3 * x1 * x0 * y0 ^ 2 - 4 * cr ^ 2 * ci * y3 * y1 * y0 ^ 3
  + 2 * cr ^ 2 * ci * x2 ^ 2 * y0 ^ 3 + 2 * cr ^ 2 * ci * x2 * y2 * x0 * y0 ^ 2
  - 2 * cr ^ 2 * ci * x2 * x1 ^ 2 * x0 * y0 - 5 * cr ^ 2 * ci * x2 * x1 * y1 * y0 ^ 2
  - 4 * cr ^ 2 * ci * y2 ^ 2 * x0 ^ 2 * y0 - 4 * cr ^ 2 * ci * y2 * x1 ^ 2 * x0 ^ 2
  + 2 * cr ^ 2 * ci * y2 * x1 * y1 * x0 * y0 + 3 * cr ^ 2 * ci * y2 * y1 ^ 2 * y0 ^ 2
  + 3 * cr ^ 2 * ci * x1 ^ 3 * y1 * x0 + 3 * cr ^ 2 * ci * x1 ^ 2 * y1 ^ 2 * y0
  + 3 * cr ^ 2 * x3 ^ 2 * x2 * x0 * y0 ^ 2 - 4 * cr ^ 2 * x3 ^ 2 * y2 * x0 ^ 2 * y0
  + 2 * cr ^ 2 * x3 ^ 2 * x1 ^ 2 * x0 ^ 2 + 5 * cr ^ 2 * x3 ^ 2 * x1 * y1 * x0 * y0
  + 3 * cr ^ 2 * x3 ^ 2 * y1 ^ 2 * y0 ^ 2 + 3 * cr ^ 2 * x3 * y3 * x2 * y0 ^ 3
  - 5 * cr ^ 2 * x3 * y3 * y2 * x0 * y0 ^ 2 - cr ^ 2 * x3 * y3 * x1 ^ 2 * x0 * y0
  - cr ^ 2 * x3 * y3 * x1 * y1 * y0 ^ 2 + 2 * cr ^ 2 * x3 * x2 ^ 2 * x1 * y0 ^ 2
  - 4 * cr ^ 2 * x3 * x2 * y2 * x1 * x0 * y0 + cr ^ 2 * x3 * x2 * y2 * y1 * y0 ^ 2
  - 2 * cr ^ 2 * x3 * x2 * x1 ^ 3 * x0

/-- Terms 41–80 of `quartic8`. -/
def quartic8_1 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -2 * cr ^ 2 * x3 * x2 * x1 ^ 2 * y1 * y0 + 4 * cr ^ 2 * x3 * y2 ^ 2 * x1 * x0 ^ 2
  + cr ^ 2 * x3 * y2 ^ 2 * y1 * x0 * y0 - 3 * cr ^ 2 * x3 * y2 * x1 ^ 2 * y1 * x0
  - 3 * cr ^ 2 * x3 * y2 * x1 * y1 ^ 2 * y0 - cr ^ 2 * y3 ^ 2 * y2 * y0 ^ 3
  - cr ^ 2 * y3 * x2 * y2 * x1 * y0 ^ 2 + 3 * cr ^ 2 * y3 * y2 ^ 2 * x1 * x0 * y0
  + 2 * cr ^ 2 * y3 * y2 ^ 2 * y1 * y0 ^ 2 + cr ^ 2 * y3 * y2 * x1 ^ 3 * x0
  + cr ^ 2 * y3 * y2 * x1 ^ 2 * y1 * y0 + cr ^ 2 * x2 ^ 2 * y2 ^ 2 * y0 ^ 2
  - 2 * cr ^ 2 * x2 * y2 ^ 3 * x0 * y0 - cr ^ 2 * x2 * y2 ^ 2 * x1 ^ 2 * x0
  - cr ^ 2 * x2 * y2 ^ 2 * x1 * y1 * y0 + cr ^ 2 * y2 ^ 4 * x0 ^ 2
  - cr ^ 2 * y2 ^ 3 * x1 * y1 * x0 - cr ^ 2 * y2 ^ 3 * y1 ^ 2 * y0
  - 4 * cr * ci ^ 3 * x0 ^ 3 * y0 - 4 * cr * ci ^ 2 * x3 * x1 * x0 ^ 3
  - cr * ci ^ 2 * x3 * y1 * x0 ^ 2 * y0 + 5 * cr * ci ^ 2 * y3 * x1 * x0 ^ 2 * y0
  + 8 * cr * ci ^ 2 * y3 * y1 * x0 * y0 ^ 2 - 4 * cr * ci ^ 2 * x2 ^ 2 * x0 * y0 ^ 2
  + 2 * cr * ci ^ 2 * x2 * y2 * x0 ^ 2 * y0 + 3 * cr * ci ^ 2 * x2 * x1 ^ 2 * x0 ^ 2
  + 2 * cr * ci ^ 2 * x2 * x1 * y1 * x0 * y0 - 4 * cr * ci ^ 2 * x2 * y1 ^ 2 * y0 ^ 2
  + 2 * cr * ci ^ 2 * y2 ^ 2 * x0 ^ 3 - 5 * cr * ci ^ 2 * y2 * x1 * y1 * x0 ^ 2
  - 2 * cr * ci ^ 2 * y2 * y1 ^ 2 * x0 * y0 + 3 * cr * ci ^ 2 * x1 ^ 2 * y1 ^ 2 * x0
  + 3 * cr * ci ^ 2 * x1 * y1 ^ 3 * y0 - 2 * cr * ci * x3 ^ 2 * x2 * x0 ^ 2 * y0
  + 4 * cr * ci * x3 ^ 2 * y2 * x0 ^ 3 - cr * ci * x3 ^ 2 * x1 * y1 * x0 ^ 2
  - cr * ci * x3 ^ 2 * y1 ^ 2 * x0 * y0 + 2 * cr * ci * x3 * y3 * x2 * x0 * y0 ^ 2
  + 2 * cr * ci * x3 * y3 * y2 * x0 ^ 2 * y0 + 5 * cr * ci * x3 * y3 * x1 ^ 2 * x0 ^ 2

/-- Terms 81–120 of `quartic8`. -/
def quartic8_2 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  10 * cr * ci * x3 * y3 * x1 * y1 * x0 * y0 + 5 * cr * ci * x3 * y3 * y1 ^ 2 * y0 ^ 2
  + cr * ci * x3 * x2 ^ 2 * y1 * y0 ^ 2 - 4 * cr * ci * x3 * x2 * y2 * x1 * x0 ^ 2
  - 8 * cr * ci * x3 * x2 * y2 * y1 * x0 * y0 - cr * ci * x3 * x2 * x1 ^ 2 * y1 * x0
  - cr * ci * x3 * x2 * x1 * y1 ^ 2 * y0 + 3 * cr * ci * x3 * y2 ^ 2 * y1 * x0 ^ 2
  - 3 * cr * ci * x3 * y2 * x1 * y1 ^ 2 * x0 - 3 * cr * ci * x3 * y2 * y1 ^ 3 * y0
  + 4 * cr * ci * y3 ^ 2 * x2 * y0 ^ 3 - 2 * cr * ci * y3 ^ 2 * y2 * x0 * y0 ^ 2
  - cr * ci * y3 ^ 2 * x1 ^ 2 * x0 * y0 - cr * ci * y3 ^ 2 * x1 * y1 * y0 ^ 2
  + 3 * cr * ci * y3 * x2 ^ 2 * x1 * y0 ^ 2 - 8 * cr * ci * y3 * x2 * y2 * x1 * x0 * y0
  - 4 * cr * ci * y3 * x2 * y2 * y1 * y0 ^ 2 - 3 * cr * ci * y3 * x2 * x1 ^ 3 * x0
  - 3 * cr * ci * y3 * x2 * x1 ^ 2 * y1 * y0 + cr * ci * y3 * y2 ^ 2 * x1 * x0 ^ 2
  - cr * ci * y3 * y2 * x1 ^ 2 * y1 * x0 - cr * ci * y3 * y2 * x1 * y1 ^ 2 * y0
  - 2 * cr * ci * x2 ^ 3 * y2 * y0 ^ 2 + 4 * cr * ci * x2 ^ 2 * y2 ^ 2 * x0 * y0
  + 2 * cr * ci * x2 ^ 2 * y2 * x1 ^ 2 * x0 + 2 * cr * ci * x2 ^ 2 * y2 * x1 * y1 * y0
  - 2 * cr * ci * x2 * y2 ^ 3 * x0 ^ 2 + 2 * cr * ci * x2 * y2 ^ 2 * x1 * y1 * x0
  + 2 * cr * ci * x2 * y2 ^ 2 * y1 ^ 2 * y0 + cr * x3 ^ 4 * x0 ^ 3
  + 3 * cr * x3 ^ 3 * y3 * x0 ^ 2 * y0 - 2 * cr * x3 ^ 3 * x2 * x1 * x0 ^ 2
  - 3 * cr * x3 ^ 3 * x2 * y1 * x0 * y0 + cr * x3 ^ 3 * y2 * y1 * x0 ^ 2
  - cr * x3 ^ 3 * x1 * y1 ^ 2 * x0 - cr * x3 ^ 3 * y1 ^ 3 * y0
  + 3 * cr * x3 ^ 2 * y3 ^ 2 * x0 * y0 ^ 2 - cr * x3 ^ 2 * y3 * x2 * x1 * x0 * y0
  - 3 * cr * x3 ^ 2 * y3 * x2 * y1 * y0 ^ 2 - 3 * cr * x3 ^ 2 * y3 * y2 * x1 * x0 ^ 2

/-- Terms 121–160 of `quartic8`. -/
def quartic8_3 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -cr * x3 ^ 2 * y3 * y2 * y1 * x0 * y0 + 2 * cr * x3 ^ 2 * y3 * x1 ^ 2 * y1 * x0
  + 2 * cr * x3 ^ 2 * y3 * x1 * y1 ^ 2 * y0 - cr * x3 ^ 2 * x2 ^ 3 * y0 ^ 2
  + 2 * cr * x3 ^ 2 * x2 ^ 2 * y2 * x0 * y0 + cr * x3 ^ 2 * x2 ^ 2 * x1 ^ 2 * x0
  + cr * x3 ^ 2 * x2 ^ 2 * x1 * y1 * y0 - cr * x3 ^ 2 * x2 * y2 ^ 2 * x0 ^ 2
  + cr * x3 ^ 2 * x2 * y2 * x1 * y1 * x0 + cr * x3 ^ 2 * x2 * y2 * y1 ^ 2 * y0
  + cr * x3 * y3 ^ 3 * y0 ^ 3 + cr * x3 * y3 ^ 2 * x2 * x1 * y0 ^ 2
  - 3 * cr * x3 * y3 ^ 2 * y2 * x1 * x0 * y0 - 2 * cr * x3 * y3 ^ 2 * y2 * y1 * y0 ^ 2
  - cr * x3 * y3 ^ 2 * x1 ^ 3 * x0 - cr * x3 * y3 ^ 2 * x1 ^ 2 * y1 * y0
  - cr * x3 * y3 * x2 ^ 2 * y2 * y0 ^ 2 + 2 * cr * x3 * y3 * x2 * y2 ^ 2 * x0 * y0
  + cr * x3 * y3 * x2 * y2 * x1 ^ 2 * x0 + cr * x3 * y3 * x2 * y2 * x1 * y1 * y0
  - cr * x3 * y3 * y2 ^ 3 * x0 ^ 2 + cr * x3 * y3 * y2 ^ 2 * x1 * y1 * x0
  + cr * x3 * y3 * y2 ^ 2 * y1 ^ 2 * y0 + ci ^ 4 * x0 ^ 4 - ci ^ 3 * x3 * y1 * x0 ^ 3
  - 3 * ci ^ 3 * y3 * x1 * x0 ^ 3 - 4 * ci ^ 3 * y3 * y1 * x0 ^ 2 * y0
  + 2 * ci ^ 3 * x2 ^ 2 * x0 ^ 2 * y0 - 2 * ci ^ 3 * x2 * y2 * x0 ^ 3
  + 3 * ci ^ 3 * x2 * x1 * y1 * x0 ^ 2 + 4 * ci ^ 3 * x2 * y1 ^ 2 * x0 * y0
  - ci ^ 3 * y2 * y1 ^ 2 * x0 ^ 2 + ci ^ 3 * x1 * y1 ^ 3 * x0 + ci ^ 3 * y1 ^ 4 * y0
  - ci ^ 2 * x3 ^ 2 * x2 * x0 ^ 3 - 5 * ci ^ 2 * x3 * y3 * x2 * x0 ^ 2 * y0
  + 3 * ci ^ 2 * x3 * y3 * y2 * x0 ^ 3 - ci ^ 2 * x3 * y3 * x1 * y1 * x0 ^ 2
  - ci ^ 2 * x3 * y3 * y1 ^ 2 * x0 * y0 + 2 * ci ^ 2 * x3 * x2 ^ 2 * x1 * x0 ^ 2

/-- Terms 161–200 of `quartic8`. -/
def quartic8_4 (_cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  3 * ci ^ 2 * x3 * x2 ^ 2 * y1 * x0 * y0 - ci ^ 2 * x3 * x2 * y2 * y1 * x0 ^ 2
  + ci ^ 2 * x3 * x2 * x1 * y1 ^ 2 * x0 + ci ^ 2 * x3 * x2 * y1 ^ 3 * y0
  - 4 * ci ^ 2 * y3 ^ 2 * x2 * x0 * y0 ^ 2 + 3 * ci ^ 2 * y3 ^ 2 * y2 * x0 ^ 2 * y0
  + 3 * ci ^ 2 * y3 ^ 2 * x1 ^ 2 * x0 ^ 2 + 5 * ci ^ 2 * y3 ^ 2 * x1 * y1 * x0 * y0
  + 2 * ci ^ 2 * y3 ^ 2 * y1 ^ 2 * y0 ^ 2 + ci ^ 2 * y3 * x2 ^ 2 * x1 * x0 * y0
  + 4 * ci ^ 2 * y3 * x2 ^ 2 * y1 * y0 ^ 2 + ci ^ 2 * y3 * x2 * y2 * x1 * x0 ^ 2
  - 4 * ci ^ 2 * y3 * x2 * y2 * y1 * x0 * y0 - 3 * ci ^ 2 * y3 * x2 * x1 ^ 2 * y1 * x0
  - 3 * ci ^ 2 * y3 * x2 * x1 * y1 ^ 2 * y0 + 2 * ci ^ 2 * y3 * y2 ^ 2 * y1 * x0 ^ 2
  - 2 * ci ^ 2 * y3 * y2 * x1 * y1 ^ 2 * x0 - 2 * ci ^ 2 * y3 * y2 * y1 ^ 3 * y0
  + ci ^ 2 * x2 ^ 4 * y0 ^ 2 - 2 * ci ^ 2 * x2 ^ 3 * y2 * x0 * y0
  - ci ^ 2 * x2 ^ 3 * x1 ^ 2 * x0 - ci ^ 2 * x2 ^ 3 * x1 * y1 * y0
  + ci ^ 2 * x2 ^ 2 * y2 ^ 2 * x0 ^ 2 - ci ^ 2 * x2 ^ 2 * y2 * x1 * y1 * x0
  - ci ^ 2 * x2 ^ 2 * y2 * y1 ^ 2 * y0 + ci * x3 ^ 3 * y3 * x0 ^ 3
  + 3 * ci * x3 ^ 2 * y3 ^ 2 * x0 ^ 2 * y0 - 2 * ci * x3 ^ 2 * y3 * x2 * x1 * x0 ^ 2
  - 3 * ci * x3 ^ 2 * y3 * x2 * y1 * x0 * y0 + ci * x3 ^ 2 * y3 * y2 * y1 * x0 ^ 2
  - ci * x3 ^ 2 * y3 * x1 * y1 ^ 2 * x0 - ci * x3 ^ 2 * y3 * y1 ^ 3 * y0
  + 3 * ci * x3 * y3 ^ 3 * x0 * y0 ^ 2 - ci * x3 * y3 ^ 2 * x2 * x1 * x0 * y0
  - 3 * ci * x3 * y3 ^ 2 * x2 * y1 * y0 ^ 2 - 3 * ci * x3 * y3 ^ 2 * y2 * x1 * x0 ^ 2
  - ci * x3 * y3 ^ 2 * y2 * y1 * x0 * y0 + 2 * ci * x3 * y3 ^ 2 * x1 ^ 2 * y1 * x0
  + 2 * ci * x3 * y3 ^ 2 * x1 * y1 ^ 2 * y0 - ci * x3 * y3 * x2 ^ 3 * y0 ^ 2

/-- Terms 201–219 of `quartic8`. -/
def quartic8_5 (_cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  2 * ci * x3 * y3 * x2 ^ 2 * y2 * x0 * y0 + ci * x3 * y3 * x2 ^ 2 * x1 ^ 2 * x0
  + ci * x3 * y3 * x2 ^ 2 * x1 * y1 * y0 - ci * x3 * y3 * x2 * y2 ^ 2 * x0 ^ 2
  + ci * x3 * y3 * x2 * y2 * x1 * y1 * x0 + ci * x3 * y3 * x2 * y2 * y1 ^ 2 * y0
  + ci * y3 ^ 4 * y0 ^ 3 + ci * y3 ^ 3 * x2 * x1 * y0 ^ 2 - 3 * ci * y3 ^ 3 * y2 * x1 * x0 * y0
  - 2 * ci * y3 ^ 3 * y2 * y1 * y0 ^ 2 - ci * y3 ^ 3 * x1 ^ 3 * x0
  - ci * y3 ^ 3 * x1 ^ 2 * y1 * y0 - ci * y3 ^ 2 * x2 ^ 2 * y2 * y0 ^ 2
  + 2 * ci * y3 ^ 2 * x2 * y2 ^ 2 * x0 * y0 + ci * y3 ^ 2 * x2 * y2 * x1 ^ 2 * x0
  + ci * y3 ^ 2 * x2 * y2 * x1 * y1 * y0 - ci * y3 ^ 2 * y2 ^ 3 * x0 ^ 2
  + ci * y3 ^ 2 * y2 ^ 2 * x1 * y1 * x0 + ci * y3 ^ 2 * y2 ^ 2 * y1 ^ 2 * y0

/-- The Bilharz determinant `Δ₈` of the quartic `c s⁴ + a₃ s³ + … + a₀`, `c = cr + j ci`,
in the real and imaginary parts of the coefficients (219 terms, 6 parts). -/
def quartic8 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  quartic8_0 cr ci x3 y3 x2 y2 x1 y1 x0 y0 + quartic8_1 cr ci x3 y3 x2 y2 x1 y1 x0 y0
    + quartic8_2 cr ci x3 y3 x2 y2 x1 y1 x0 y0 + quartic8_3 cr ci x3 y3 x2 y2 x1 y1 x0 y0
    + quartic8_4 cr ci x3 y3 x2 y2 x1 y1 x0 y0 + quartic8_5 cr ci x3 y3 x2 y2 x1 y1 x0 y0

/-- The Bilharz determinant `Δ₂` of the monic quintic `s⁵ + a₄ s⁴ + … + a₀`,
in the real and imaginary parts of the coefficients (1 terms). -/
def quintic2 (x4 _y4 _x3 _y3 _x2 _y2 _x1 _y1 _x0 _y0 : ℝ) : ℝ :=
  x4

/-- The Bilharz determinant `Δ₄` of the monic quintic `s⁵ + a₄ s⁴ + … + a₀`,
in the real and imaginary parts of the coefficients (4 terms). -/
def quintic4 (x4 y4 x3 y3 x2 _y2 _x1 _y1 _x0 _y0 : ℝ) : ℝ :=
  x4 ^ 2 * x3 + x4 * y4 * y3 - x4 * x2 - y3 ^ 2

/-- The Bilharz determinant `Δ₆` of the monic quintic `s⁵ + a₄ s⁴ + … + a₀`,
in the real and imaginary parts of the coefficients (28 terms). -/
def quintic6 (x4 y4 x3 y3 x2 y2 x1 y1 x0 _y0 : ℝ) : ℝ :=
  -x4 ^ 3 * x3 * x1 - x4 ^ 3 * y2 ^ 2 - x4 ^ 2 * y4 * x3 * y1 - x4 ^ 2 * y4 * y3 * x1
  + 2 * x4 ^ 2 * y4 * x2 * y2 + x4 ^ 2 * x3 ^ 2 * x2 + x4 ^ 2 * x3 * y3 * y2
  - x4 * y4 ^ 2 * y3 * y1 - x4 * y4 ^ 2 * x2 ^ 2 + x4 * y4 * x3 * y3 * x2
  + x4 * y4 * y3 ^ 2 * y2 + x4 ^ 2 * x3 * x0 + x4 ^ 2 * x2 * x1 + 2 * x4 ^ 2 * y2 * y1
  + x4 * y4 * y3 * x0 - x4 * y4 * x2 * y1 - 2 * x4 * x3 * x2 ^ 2 + x4 * y3 ^ 2 * x1
  - 3 * x4 * y3 * x2 * y2 + y4 * y3 ^ 2 * y1 + y4 * y3 * x2 ^ 2 - x3 * y3 ^ 2 * x2 - y3 ^ 3 * y2
  - x4 * x2 * x0 - x4 * y1 ^ 2 - y3 ^ 2 * x0 + 2 * y3 * x2 * y1 + x2 ^ 3

/-- Terms 1–40 of `quintic8`. -/
def quintic8_0 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -x4 ^ 4 * x3 * y0 ^ 2 + 2 * x4 ^ 4 * y2 * x1 * y0 + x4 ^ 4 * x1 ^ 3
  + 2 * x4 ^ 3 * y4 * x3 * x0 * y0 - x4 ^ 3 * y4 * y3 * y0 ^ 2 - 2 * x4 ^ 3 * y4 * x2 * x1 * y0
  - 2 * x4 ^ 3 * y4 * y2 * x1 * x0 + 2 * x4 ^ 3 * y4 * y2 * y1 * y0
  + 3 * x4 ^ 3 * y4 * x1 ^ 2 * y1 + x4 ^ 3 * x3 ^ 2 * x1 * x0 + 2 * x4 ^ 3 * x3 ^ 2 * y1 * y0
  - x4 ^ 3 * x3 * y3 * x1 * y0 - 2 * x4 ^ 3 * x3 * x2 * x1 ^ 2 + x4 ^ 3 * x3 * y2 ^ 2 * x0
  - 3 * x4 ^ 3 * x3 * y2 * x1 * y1 + x4 ^ 3 * y3 * y2 ^ 2 * y0 + x4 ^ 3 * y3 * y2 * x1 ^ 2
  - x4 ^ 3 * x2 * y2 ^ 2 * x1 - x4 ^ 3 * y2 ^ 3 * y1 - x4 ^ 2 * y4 ^ 2 * x3 * x0 ^ 2
  + 2 * x4 ^ 2 * y4 ^ 2 * y3 * x0 * y0 + 2 * x4 ^ 2 * y4 ^ 2 * x2 * x1 * x0
  - 2 * x4 ^ 2 * y4 ^ 2 * x2 * y1 * y0 - 2 * x4 ^ 2 * y4 ^ 2 * y2 * y1 * x0
  + 3 * x4 ^ 2 * y4 ^ 2 * x1 * y1 ^ 2 - x4 ^ 2 * y4 * x3 ^ 2 * y1 * x0
  + 3 * x4 ^ 2 * y4 * x3 * y3 * x1 * x0 + 3 * x4 ^ 2 * y4 * x3 * y3 * y1 * y0
  - 2 * x4 ^ 2 * y4 * x3 * x2 * y2 * x0 - x4 ^ 2 * y4 * x3 * x2 * x1 * y1
  - 3 * x4 ^ 2 * y4 * x3 * y2 * y1 ^ 2 - x4 ^ 2 * y4 * y3 ^ 2 * x1 * y0
  - 2 * x4 ^ 2 * y4 * y3 * x2 * y2 * y0 - 3 * x4 ^ 2 * y4 * y3 * x2 * x1 ^ 2
  - x4 ^ 2 * y4 * y3 * y2 * x1 * y1 + 2 * x4 ^ 2 * y4 * x2 ^ 2 * y2 * x1
  + 2 * x4 ^ 2 * y4 * x2 * y2 ^ 2 * y1 - x4 ^ 2 * x3 ^ 3 * x2 * x0 - x4 ^ 2 * x3 ^ 3 * y1 ^ 2
  - x4 ^ 2 * x3 ^ 2 * y3 * x2 * y0

/-- Terms 41–80 of `quintic8`. -/
def quintic8_1 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -x4 ^ 2 * x3 ^ 2 * y3 * y2 * x0 + 2 * x4 ^ 2 * x3 ^ 2 * y3 * x1 * y1
  + x4 ^ 2 * x3 ^ 2 * x2 ^ 2 * x1 + x4 ^ 2 * x3 ^ 2 * x2 * y2 * y1
  - x4 ^ 2 * x3 * y3 ^ 2 * y2 * y0 - x4 ^ 2 * x3 * y3 ^ 2 * x1 ^ 2
  + x4 ^ 2 * x3 * y3 * x2 * y2 * x1 + x4 ^ 2 * x3 * y3 * y2 ^ 2 * y1 - x4 * y4 ^ 3 * y3 * x0 ^ 2
  + 2 * x4 * y4 ^ 3 * x2 * y1 * x0 + x4 * y4 ^ 3 * y1 ^ 3 - x4 * y4 ^ 2 * x3 * y3 * y1 * x0
  + x4 * y4 ^ 2 * x3 * x2 ^ 2 * x0 + x4 * y4 ^ 2 * x3 * x2 * y1 ^ 2
  + 2 * x4 * y4 ^ 2 * y3 ^ 2 * x1 * x0 + x4 * y4 ^ 2 * y3 ^ 2 * y1 * y0
  + x4 * y4 ^ 2 * y3 * x2 ^ 2 * y0 - 3 * x4 * y4 ^ 2 * y3 * x2 * x1 * y1
  - 2 * x4 * y4 ^ 2 * y3 * y2 * y1 ^ 2 - x4 * y4 ^ 2 * x2 ^ 3 * x1
  - x4 * y4 ^ 2 * x2 ^ 2 * y2 * y1 - x4 * y4 * x3 ^ 2 * y3 * x2 * x0
  - x4 * y4 * x3 ^ 2 * y3 * y1 ^ 2 - x4 * y4 * x3 * y3 ^ 2 * x2 * y0
  - x4 * y4 * x3 * y3 ^ 2 * y2 * x0 + 2 * x4 * y4 * x3 * y3 ^ 2 * x1 * y1
  + x4 * y4 * x3 * y3 * x2 ^ 2 * x1 + x4 * y4 * x3 * y3 * x2 * y2 * y1
  - x4 * y4 * y3 ^ 3 * y2 * y0 - x4 * y4 * y3 ^ 3 * x1 ^ 2 + x4 * y4 * y3 ^ 2 * x2 * y2 * x1
  + x4 * y4 * y3 ^ 2 * y2 ^ 2 * y1 + x4 ^ 3 * x2 * y0 ^ 2 - 2 * x4 ^ 3 * y2 * x0 * y0
  - 3 * x4 ^ 3 * x1 ^ 2 * x0 - 2 * x4 ^ 3 * x1 * y1 * y0 + 2 * x4 ^ 2 * y4 * y2 * x0 ^ 2
  - 4 * x4 ^ 2 * y4 * x1 * y1 * x0 - 2 * x4 ^ 2 * y4 * y1 ^ 2 * y0 - x4 ^ 2 * x3 ^ 2 * x0 ^ 2

/-- Terms 81–120 of `quintic8`. -/
def quintic8_2 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -x4 ^ 2 * x3 * y3 * x0 * y0 + 2 * x4 ^ 2 * x3 * x2 * x1 * x0 - 4 * x4 ^ 2 * x3 * x2 * y1 * y0
  + x4 ^ 2 * x3 * y2 * y1 * x0 + 3 * x4 ^ 2 * x3 * x1 * y1 ^ 2 + x4 ^ 2 * y3 ^ 2 * y0 ^ 2
  + 3 * x4 ^ 2 * y3 * x2 * x1 * y0 - 4 * x4 ^ 2 * y3 * y2 * y1 * y0
  - 4 * x4 ^ 2 * y3 * x1 ^ 2 * y1 + 2 * x4 ^ 2 * x2 ^ 2 * x1 ^ 2
  + 5 * x4 ^ 2 * x2 * y2 * x1 * y1 + 3 * x4 ^ 2 * y2 ^ 2 * y1 ^ 2 - x4 * y4 ^ 2 * x2 * x0 ^ 2
  - x4 * y4 ^ 2 * y1 ^ 2 * x0 - x4 * y4 * x3 * y3 * x0 ^ 2 + 5 * x4 * y4 * x3 * x2 * y1 * x0
  + 3 * x4 * y4 * x3 * y1 ^ 3 - 3 * x4 * y4 * y3 ^ 2 * x0 * y0 - x4 * y4 * y3 * x2 * x1 * x0
  + 3 * x4 * y4 * y3 * x2 * y1 * y0 + 5 * x4 * y4 * y3 * y2 * y1 * x0
  - 5 * x4 * y4 * y3 * x1 * y1 ^ 2 - x4 * y4 * x2 ^ 2 * x1 * y1 - x4 * y4 * x2 * y2 * y1 ^ 2
  + 2 * x4 * x3 ^ 2 * x2 ^ 2 * x0 + 2 * x4 * x3 ^ 2 * x2 * y1 ^ 2 - x4 * x3 * y3 ^ 2 * x1 * x0
  - 2 * x4 * x3 * y3 ^ 2 * y1 * y0 + 2 * x4 * x3 * y3 * x2 ^ 2 * y0
  + 3 * x4 * x3 * y3 * x2 * y2 * x0 - 4 * x4 * x3 * y3 * x2 * x1 * y1
  + x4 * x3 * y3 * y2 * y1 ^ 2 - 2 * x4 * x3 * x2 ^ 3 * x1 - 2 * x4 * x3 * x2 ^ 2 * y2 * y1
  + x4 * y3 ^ 3 * x1 * y0 + 3 * x4 * y3 ^ 2 * x2 * y2 * y0 + 4 * x4 * y3 ^ 2 * x2 * x1 ^ 2
  + x4 * y3 ^ 2 * y2 * x1 * y1 - 3 * x4 * y3 * x2 ^ 2 * y2 * x1 - 3 * x4 * y3 * x2 * y2 ^ 2 * y1

/-- Terms 121–160 of `quintic8`. -/
def quintic8_3 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  y4 ^ 2 * y3 ^ 2 * x0 ^ 2 - 2 * y4 ^ 2 * y3 * x2 * y1 * x0 - y4 ^ 2 * y3 * y1 ^ 3
  + y4 * x3 * y3 ^ 2 * y1 * x0 - y4 * x3 * y3 * x2 ^ 2 * x0 - y4 * x3 * y3 * x2 * y1 ^ 2
  - 2 * y4 * y3 ^ 3 * x1 * x0 - y4 * y3 ^ 3 * y1 * y0 - y4 * y3 ^ 2 * x2 ^ 2 * y0
  + 3 * y4 * y3 ^ 2 * x2 * x1 * y1 + 2 * y4 * y3 ^ 2 * y2 * y1 ^ 2 + y4 * y3 * x2 ^ 3 * x1
  + y4 * y3 * x2 ^ 2 * y2 * y1 + x3 ^ 2 * y3 ^ 2 * x2 * x0 + x3 ^ 2 * y3 ^ 2 * y1 ^ 2
  + x3 * y3 ^ 3 * x2 * y0 + x3 * y3 ^ 3 * y2 * x0 - 2 * x3 * y3 ^ 3 * x1 * y1
  - x3 * y3 ^ 2 * x2 ^ 2 * x1 - x3 * y3 ^ 2 * x2 * y2 * y1 + y3 ^ 4 * y2 * y0 + y3 ^ 4 * x1 ^ 2
  - y3 ^ 3 * x2 * y2 * x1 - y3 ^ 3 * y2 ^ 2 * y1 + 3 * x4 ^ 2 * x1 * x0 ^ 2
  + 2 * x4 ^ 2 * y1 * x0 * y0 + x4 * y4 * y1 * x0 ^ 2 - 2 * x4 * x3 * y1 ^ 2 * x0
  - x4 * y3 * x2 * x0 * y0 - x4 * y3 * y2 * x0 ^ 2 + 6 * x4 * y3 * x1 * y1 * x0
  + 3 * x4 * y3 * y1 ^ 2 * y0 - 3 * x4 * x2 ^ 2 * x1 * x0 + 2 * x4 * x2 ^ 2 * y1 * y0
  - 3 * x4 * x2 * y2 * y1 * x0 - 4 * x4 * x2 * x1 * y1 ^ 2 - 3 * x4 * y2 * y1 ^ 3
  + 2 * y4 * y3 * x2 * x0 ^ 2 + y4 * y3 * y1 ^ 2 * x0 - 2 * y4 * x2 ^ 2 * y1 * x0

/-- Terms 161–181 of `quintic8`. -/
def quintic8_4 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -y4 * x2 * y1 ^ 3 + x3 * y3 ^ 2 * x0 ^ 2 - 2 * x3 * y3 * x2 * y1 * x0 - 2 * x3 * y3 * y1 ^ 3
  - x3 * x2 ^ 3 * x0 - x3 * x2 ^ 2 * y1 ^ 2 + y3 ^ 3 * x0 * y0 - 3 * y3 ^ 2 * x2 * x1 * x0
  - 2 * y3 ^ 2 * x2 * y1 * y0 - 3 * y3 ^ 2 * y2 * y1 * x0 + 2 * y3 ^ 2 * x1 * y1 ^ 2
  - y3 * x2 ^ 3 * y0 + 4 * y3 * x2 ^ 2 * x1 * y1 + 3 * y3 * x2 * y2 * y1 ^ 2 + x2 ^ 4 * x1
  + x2 ^ 3 * y2 * y1 - x4 * x0 ^ 3 - 2 * y3 * y1 * x0 ^ 2 + x2 ^ 2 * x0 ^ 2
  + 3 * x2 * y1 ^ 2 * x0 + y1 ^ 4

/-- The Bilharz determinant `Δ₈` of the monic quintic `s⁵ + a₄ s⁴ + … + a₀`,
in the real and imaginary parts of the coefficients (181 terms, 5 parts). -/
def quintic8 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  quintic8_0 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic8_1 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic8_2 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic8_3 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic8_4 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0

/-- Terms 1–40 of `quintic10`. -/
def quintic10_0 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  x4 ^ 5 * y0 ^ 4 - 4 * x4 ^ 4 * y4 * x0 * y0 ^ 3 - 4 * x4 ^ 4 * x3 * x1 * x0 * y0 ^ 2
  - 3 * x4 ^ 4 * x3 * y1 * y0 ^ 3 - x4 ^ 4 * y3 * x1 * y0 ^ 3 - 2 * x4 ^ 4 * x2 * y2 * y0 ^ 3
  - x4 ^ 4 * x2 * x1 ^ 2 * y0 ^ 2 + 2 * x4 ^ 4 * y2 ^ 2 * x0 * y0 ^ 2
  + 4 * x4 ^ 4 * y2 * x1 ^ 2 * x0 * y0 + 3 * x4 ^ 4 * y2 * x1 * y1 * y0 ^ 2
  + x4 ^ 4 * x1 ^ 4 * x0 + x4 ^ 4 * x1 ^ 3 * y1 * y0 + 6 * x4 ^ 3 * y4 ^ 2 * x0 ^ 2 * y0 ^ 2
  + 8 * x4 ^ 3 * y4 * x3 * x1 * x0 ^ 2 * y0 + 5 * x4 ^ 3 * y4 * x3 * y1 * x0 * y0 ^ 2
  - x4 ^ 3 * y4 * y3 * x1 * x0 * y0 ^ 2 - 4 * x4 ^ 3 * y4 * y3 * y1 * y0 ^ 3
  + 2 * x4 ^ 3 * y4 * x2 ^ 2 * y0 ^ 3 + 2 * x4 ^ 3 * y4 * x2 * y2 * x0 * y0 ^ 2
  - 2 * x4 ^ 3 * y4 * x2 * x1 ^ 2 * x0 * y0 - 5 * x4 ^ 3 * y4 * x2 * x1 * y1 * y0 ^ 2
  - 4 * x4 ^ 3 * y4 * y2 ^ 2 * x0 ^ 2 * y0 - 4 * x4 ^ 3 * y4 * y2 * x1 ^ 2 * x0 ^ 2
  + 2 * x4 ^ 3 * y4 * y2 * x1 * y1 * x0 * y0 + 3 * x4 ^ 3 * y4 * y2 * y1 ^ 2 * y0 ^ 2
  + 3 * x4 ^ 3 * y4 * x1 ^ 3 * y1 * x0 + 3 * x4 ^ 3 * y4 * x1 ^ 2 * y1 ^ 2 * y0
  + 3 * x4 ^ 3 * x3 ^ 2 * x2 * x0 * y0 ^ 2 - 4 * x4 ^ 3 * x3 ^ 2 * y2 * x0 ^ 2 * y0
  + 2 * x4 ^ 3 * x3 ^ 2 * x1 ^ 2 * x0 ^ 2 + 5 * x4 ^ 3 * x3 ^ 2 * x1 * y1 * x0 * y0
  + 3 * x4 ^ 3 * x3 ^ 2 * y1 ^ 2 * y0 ^ 2 + 3 * x4 ^ 3 * x3 * y3 * x2 * y0 ^ 3
  - 5 * x4 ^ 3 * x3 * y3 * y2 * x0 * y0 ^ 2 - x4 ^ 3 * x3 * y3 * x1 ^ 2 * x0 * y0
  - x4 ^ 3 * x3 * y3 * x1 * y1 * y0 ^ 2 + 2 * x4 ^ 3 * x3 * x2 ^ 2 * x1 * y0 ^ 2
  - 4 * x4 ^ 3 * x3 * x2 * y2 * x1 * x0 * y0 + x4 ^ 3 * x3 * x2 * y2 * y1 * y0 ^ 2
  - 2 * x4 ^ 3 * x3 * x2 * x1 ^ 3 * x0

/-- Terms 41–80 of `quintic10`. -/
def quintic10_1 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -2 * x4 ^ 3 * x3 * x2 * x1 ^ 2 * y1 * y0 + 4 * x4 ^ 3 * x3 * y2 ^ 2 * x1 * x0 ^ 2
  + x4 ^ 3 * x3 * y2 ^ 2 * y1 * x0 * y0 - 3 * x4 ^ 3 * x3 * y2 * x1 ^ 2 * y1 * x0
  - 3 * x4 ^ 3 * x3 * y2 * x1 * y1 ^ 2 * y0 - x4 ^ 3 * y3 ^ 2 * y2 * y0 ^ 3
  - x4 ^ 3 * y3 * x2 * y2 * x1 * y0 ^ 2 + 3 * x4 ^ 3 * y3 * y2 ^ 2 * x1 * x0 * y0
  + 2 * x4 ^ 3 * y3 * y2 ^ 2 * y1 * y0 ^ 2 + x4 ^ 3 * y3 * y2 * x1 ^ 3 * x0
  + x4 ^ 3 * y3 * y2 * x1 ^ 2 * y1 * y0 + x4 ^ 3 * x2 ^ 2 * y2 ^ 2 * y0 ^ 2
  - 2 * x4 ^ 3 * x2 * y2 ^ 3 * x0 * y0 - x4 ^ 3 * x2 * y2 ^ 2 * x1 ^ 2 * x0
  - x4 ^ 3 * x2 * y2 ^ 2 * x1 * y1 * y0 + x4 ^ 3 * y2 ^ 4 * x0 ^ 2
  - x4 ^ 3 * y2 ^ 3 * x1 * y1 * x0 - x4 ^ 3 * y2 ^ 3 * y1 ^ 2 * y0
  - 4 * x4 ^ 2 * y4 ^ 3 * x0 ^ 3 * y0 - 4 * x4 ^ 2 * y4 ^ 2 * x3 * x1 * x0 ^ 3
  - x4 ^ 2 * y4 ^ 2 * x3 * y1 * x0 ^ 2 * y0 + 5 * x4 ^ 2 * y4 ^ 2 * y3 * x1 * x0 ^ 2 * y0
  + 8 * x4 ^ 2 * y4 ^ 2 * y3 * y1 * x0 * y0 ^ 2 - 4 * x4 ^ 2 * y4 ^ 2 * x2 ^ 2 * x0 * y0 ^ 2
  + 2 * x4 ^ 2 * y4 ^ 2 * x2 * y2 * x0 ^ 2 * y0 + 3 * x4 ^ 2 * y4 ^ 2 * x2 * x1 ^ 2 * x0 ^ 2
  + 2 * x4 ^ 2 * y4 ^ 2 * x2 * x1 * y1 * x0 * y0 - 4 * x4 ^ 2 * y4 ^ 2 * x2 * y1 ^ 2 * y0 ^ 2
  + 2 * x4 ^ 2 * y4 ^ 2 * y2 ^ 2 * x0 ^ 3 - 5 * x4 ^ 2 * y4 ^ 2 * y2 * x1 * y1 * x0 ^ 2
  - 2 * x4 ^ 2 * y4 ^ 2 * y2 * y1 ^ 2 * x0 * y0 + 3 * x4 ^ 2 * y4 ^ 2 * x1 ^ 2 * y1 ^ 2 * x0
  + 3 * x4 ^ 2 * y4 ^ 2 * x1 * y1 ^ 3 * y0 - 2 * x4 ^ 2 * y4 * x3 ^ 2 * x2 * x0 ^ 2 * y0
  + 4 * x4 ^ 2 * y4 * x3 ^ 2 * y2 * x0 ^ 3 - x4 ^ 2 * y4 * x3 ^ 2 * x1 * y1 * x0 ^ 2
  - x4 ^ 2 * y4 * x3 ^ 2 * y1 ^ 2 * x0 * y0 + 2 * x4 ^ 2 * y4 * x3 * y3 * x2 * x0 * y0 ^ 2
  + 2 * x4 ^ 2 * y4 * x3 * y3 * y2 * x0 ^ 2 * y0 + 5 * x4 ^ 2 * y4 * x3 * y3 * x1 ^ 2 * x0 ^ 2

/-- Terms 81–120 of `quintic10`. -/
def quintic10_2 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  10 * x4 ^ 2 * y4 * x3 * y3 * x1 * y1 * x0 * y0 + 5 * x4 ^ 2 * y4 * x3 * y3 * y1 ^ 2 * y0 ^ 2
  + x4 ^ 2 * y4 * x3 * x2 ^ 2 * y1 * y0 ^ 2 - 4 * x4 ^ 2 * y4 * x3 * x2 * y2 * x1 * x0 ^ 2
  - 8 * x4 ^ 2 * y4 * x3 * x2 * y2 * y1 * x0 * y0 - x4 ^ 2 * y4 * x3 * x2 * x1 ^ 2 * y1 * x0
  - x4 ^ 2 * y4 * x3 * x2 * x1 * y1 ^ 2 * y0 + 3 * x4 ^ 2 * y4 * x3 * y2 ^ 2 * y1 * x0 ^ 2
  - 3 * x4 ^ 2 * y4 * x3 * y2 * x1 * y1 ^ 2 * x0 - 3 * x4 ^ 2 * y4 * x3 * y2 * y1 ^ 3 * y0
  + 4 * x4 ^ 2 * y4 * y3 ^ 2 * x2 * y0 ^ 3 - 2 * x4 ^ 2 * y4 * y3 ^ 2 * y2 * x0 * y0 ^ 2
  - x4 ^ 2 * y4 * y3 ^ 2 * x1 ^ 2 * x0 * y0 - x4 ^ 2 * y4 * y3 ^ 2 * x1 * y1 * y0 ^ 2
  + 3 * x4 ^ 2 * y4 * y3 * x2 ^ 2 * x1 * y0 ^ 2 - 8 * x4 ^ 2 * y4 * y3 * x2 * y2 * x1 * x0 * y0
  - 4 * x4 ^ 2 * y4 * y3 * x2 * y2 * y1 * y0 ^ 2 - 3 * x4 ^ 2 * y4 * y3 * x2 * x1 ^ 3 * x0
  - 3 * x4 ^ 2 * y4 * y3 * x2 * x1 ^ 2 * y1 * y0 + x4 ^ 2 * y4 * y3 * y2 ^ 2 * x1 * x0 ^ 2
  - x4 ^ 2 * y4 * y3 * y2 * x1 ^ 2 * y1 * x0 - x4 ^ 2 * y4 * y3 * y2 * x1 * y1 ^ 2 * y0
  - 2 * x4 ^ 2 * y4 * x2 ^ 3 * y2 * y0 ^ 2 + 4 * x4 ^ 2 * y4 * x2 ^ 2 * y2 ^ 2 * x0 * y0
  + 2 * x4 ^ 2 * y4 * x2 ^ 2 * y2 * x1 ^ 2 * x0 + 2 * x4 ^ 2 * y4 * x2 ^ 2 * y2 * x1 * y1 * y0
  - 2 * x4 ^ 2 * y4 * x2 * y2 ^ 3 * x0 ^ 2 + 2 * x4 ^ 2 * y4 * x2 * y2 ^ 2 * x1 * y1 * x0
  + 2 * x4 ^ 2 * y4 * x2 * y2 ^ 2 * y1 ^ 2 * y0 + x4 ^ 2 * x3 ^ 4 * x0 ^ 3
  + 3 * x4 ^ 2 * x3 ^ 3 * y3 * x0 ^ 2 * y0 - 2 * x4 ^ 2 * x3 ^ 3 * x2 * x1 * x0 ^ 2
  - 3 * x4 ^ 2 * x3 ^ 3 * x2 * y1 * x0 * y0 + x4 ^ 2 * x3 ^ 3 * y2 * y1 * x0 ^ 2
  - x4 ^ 2 * x3 ^ 3 * x1 * y1 ^ 2 * x0 - x4 ^ 2 * x3 ^ 3 * y1 ^ 3 * y0
  + 3 * x4 ^ 2 * x3 ^ 2 * y3 ^ 2 * x0 * y0 ^ 2 - x4 ^ 2 * x3 ^ 2 * y3 * x2 * x1 * x0 * y0
  - 3 * x4 ^ 2 * x3 ^ 2 * y3 * x2 * y1 * y0 ^ 2 - 3 * x4 ^ 2 * x3 ^ 2 * y3 * y2 * x1 * x0 ^ 2

/-- Terms 121–160 of `quintic10`. -/
def quintic10_3 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -x4 ^ 2 * x3 ^ 2 * y3 * y2 * y1 * x0 * y0 + 2 * x4 ^ 2 * x3 ^ 2 * y3 * x1 ^ 2 * y1 * x0
  + 2 * x4 ^ 2 * x3 ^ 2 * y3 * x1 * y1 ^ 2 * y0 - x4 ^ 2 * x3 ^ 2 * x2 ^ 3 * y0 ^ 2
  + 2 * x4 ^ 2 * x3 ^ 2 * x2 ^ 2 * y2 * x0 * y0 + x4 ^ 2 * x3 ^ 2 * x2 ^ 2 * x1 ^ 2 * x0
  + x4 ^ 2 * x3 ^ 2 * x2 ^ 2 * x1 * y1 * y0 - x4 ^ 2 * x3 ^ 2 * x2 * y2 ^ 2 * x0 ^ 2
  + x4 ^ 2 * x3 ^ 2 * x2 * y2 * x1 * y1 * x0 + x4 ^ 2 * x3 ^ 2 * x2 * y2 * y1 ^ 2 * y0
  + x4 ^ 2 * x3 * y3 ^ 3 * y0 ^ 3 + x4 ^ 2 * x3 * y3 ^ 2 * x2 * x1 * y0 ^ 2
  - 3 * x4 ^ 2 * x3 * y3 ^ 2 * y2 * x1 * x0 * y0 - 2 * x4 ^ 2 * x3 * y3 ^ 2 * y2 * y1 * y0 ^ 2
  - x4 ^ 2 * x3 * y3 ^ 2 * x1 ^ 3 * x0 - x4 ^ 2 * x3 * y3 ^ 2 * x1 ^ 2 * y1 * y0
  - x4 ^ 2 * x3 * y3 * x2 ^ 2 * y2 * y0 ^ 2 + 2 * x4 ^ 2 * x3 * y3 * x2 * y2 ^ 2 * x0 * y0
  + x4 ^ 2 * x3 * y3 * x2 * y2 * x1 ^ 2 * x0 + x4 ^ 2 * x3 * y3 * x2 * y2 * x1 * y1 * y0
  - x4 ^ 2 * x3 * y3 * y2 ^ 3 * x0 ^ 2 + x4 ^ 2 * x3 * y3 * y2 ^ 2 * x1 * y1 * x0
  + x4 ^ 2 * x3 * y3 * y2 ^ 2 * y1 ^ 2 * y0 + x4 * y4 ^ 4 * x0 ^ 4
  - x4 * y4 ^ 3 * x3 * y1 * x0 ^ 3 - 3 * x4 * y4 ^ 3 * y3 * x1 * x0 ^ 3
  - 4 * x4 * y4 ^ 3 * y3 * y1 * x0 ^ 2 * y0 + 2 * x4 * y4 ^ 3 * x2 ^ 2 * x0 ^ 2 * y0
  - 2 * x4 * y4 ^ 3 * x2 * y2 * x0 ^ 3 + 3 * x4 * y4 ^ 3 * x2 * x1 * y1 * x0 ^ 2
  + 4 * x4 * y4 ^ 3 * x2 * y1 ^ 2 * x0 * y0 - x4 * y4 ^ 3 * y2 * y1 ^ 2 * x0 ^ 2
  + x4 * y4 ^ 3 * x1 * y1 ^ 3 * x0 + x4 * y4 ^ 3 * y1 ^ 4 * y0
  - x4 * y4 ^ 2 * x3 ^ 2 * x2 * x0 ^ 3 - 5 * x4 * y4 ^ 2 * x3 * y3 * x2 * x0 ^ 2 * y0
  + 3 * x4 * y4 ^ 2 * x3 * y3 * y2 * x0 ^ 3 - x4 * y4 ^ 2 * x3 * y3 * x1 * y1 * x0 ^ 2
  - x4 * y4 ^ 2 * x3 * y3 * y1 ^ 2 * x0 * y0 + 2 * x4 * y4 ^ 2 * x3 * x2 ^ 2 * x1 * x0 ^ 2

/-- Terms 161–200 of `quintic10`. -/
def quintic10_4 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  3 * x4 * y4 ^ 2 * x3 * x2 ^ 2 * y1 * x0 * y0 - x4 * y4 ^ 2 * x3 * x2 * y2 * y1 * x0 ^ 2
  + x4 * y4 ^ 2 * x3 * x2 * x1 * y1 ^ 2 * x0 + x4 * y4 ^ 2 * x3 * x2 * y1 ^ 3 * y0
  - 4 * x4 * y4 ^ 2 * y3 ^ 2 * x2 * x0 * y0 ^ 2 + 3 * x4 * y4 ^ 2 * y3 ^ 2 * y2 * x0 ^ 2 * y0
  + 3 * x4 * y4 ^ 2 * y3 ^ 2 * x1 ^ 2 * x0 ^ 2 + 5 * x4 * y4 ^ 2 * y3 ^ 2 * x1 * y1 * x0 * y0
  + 2 * x4 * y4 ^ 2 * y3 ^ 2 * y1 ^ 2 * y0 ^ 2 + x4 * y4 ^ 2 * y3 * x2 ^ 2 * x1 * x0 * y0
  + 4 * x4 * y4 ^ 2 * y3 * x2 ^ 2 * y1 * y0 ^ 2 + x4 * y4 ^ 2 * y3 * x2 * y2 * x1 * x0 ^ 2
  - 4 * x4 * y4 ^ 2 * y3 * x2 * y2 * y1 * x0 * y0 - 3 * x4 * y4 ^ 2 * y3 * x2 * x1 ^ 2 * y1 * x0
  - 3 * x4 * y4 ^ 2 * y3 * x2 * x1 * y1 ^ 2 * y0 + 2 * x4 * y4 ^ 2 * y3 * y2 ^ 2 * y1 * x0 ^ 2
  - 2 * x4 * y4 ^ 2 * y3 * y2 * x1 * y1 ^ 2 * x0 - 2 * x4 * y4 ^ 2 * y3 * y2 * y1 ^ 3 * y0
  + x4 * y4 ^ 2 * x2 ^ 4 * y0 ^ 2 - 2 * x4 * y4 ^ 2 * x2 ^ 3 * y2 * x0 * y0
  - x4 * y4 ^ 2 * x2 ^ 3 * x1 ^ 2 * x0 - x4 * y4 ^ 2 * x2 ^ 3 * x1 * y1 * y0
  + x4 * y4 ^ 2 * x2 ^ 2 * y2 ^ 2 * x0 ^ 2 - x4 * y4 ^ 2 * x2 ^ 2 * y2 * x1 * y1 * x0
  - x4 * y4 ^ 2 * x2 ^ 2 * y2 * y1 ^ 2 * y0 + x4 * y4 * x3 ^ 3 * y3 * x0 ^ 3
  + 3 * x4 * y4 * x3 ^ 2 * y3 ^ 2 * x0 ^ 2 * y0 - 2 * x4 * y4 * x3 ^ 2 * y3 * x2 * x1 * x0 ^ 2
  - 3 * x4 * y4 * x3 ^ 2 * y3 * x2 * y1 * x0 * y0 + x4 * y4 * x3 ^ 2 * y3 * y2 * y1 * x0 ^ 2
  - x4 * y4 * x3 ^ 2 * y3 * x1 * y1 ^ 2 * x0 - x4 * y4 * x3 ^ 2 * y3 * y1 ^ 3 * y0
  + 3 * x4 * y4 * x3 * y3 ^ 3 * x0 * y0 ^ 2 - x4 * y4 * x3 * y3 ^ 2 * x2 * x1 * x0 * y0
  - 3 * x4 * y4 * x3 * y3 ^ 2 * x2 * y1 * y0 ^ 2 - 3 * x4 * y4 * x3 * y3 ^ 2 * y2 * x1 * x0 ^ 2
  - x4 * y4 * x3 * y3 ^ 2 * y2 * y1 * x0 * y0 + 2 * x4 * y4 * x3 * y3 ^ 2 * x1 ^ 2 * y1 * x0
  + 2 * x4 * y4 * x3 * y3 ^ 2 * x1 * y1 ^ 2 * y0 - x4 * y4 * x3 * y3 * x2 ^ 3 * y0 ^ 2

/-- Terms 201–240 of `quintic10`. -/
def quintic10_5 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  2 * x4 * y4 * x3 * y3 * x2 ^ 2 * y2 * x0 * y0 + x4 * y4 * x3 * y3 * x2 ^ 2 * x1 ^ 2 * x0
  + x4 * y4 * x3 * y3 * x2 ^ 2 * x1 * y1 * y0 - x4 * y4 * x3 * y3 * x2 * y2 ^ 2 * x0 ^ 2
  + x4 * y4 * x3 * y3 * x2 * y2 * x1 * y1 * x0 + x4 * y4 * x3 * y3 * x2 * y2 * y1 ^ 2 * y0
  + x4 * y4 * y3 ^ 4 * y0 ^ 3 + x4 * y4 * y3 ^ 3 * x2 * x1 * y0 ^ 2
  - 3 * x4 * y4 * y3 ^ 3 * y2 * x1 * x0 * y0 - 2 * x4 * y4 * y3 ^ 3 * y2 * y1 * y0 ^ 2
  - x4 * y4 * y3 ^ 3 * x1 ^ 3 * x0 - x4 * y4 * y3 ^ 3 * x1 ^ 2 * y1 * y0
  - x4 * y4 * y3 ^ 2 * x2 ^ 2 * y2 * y0 ^ 2 + 2 * x4 * y4 * y3 ^ 2 * x2 * y2 ^ 2 * x0 * y0
  + x4 * y4 * y3 ^ 2 * x2 * y2 * x1 ^ 2 * x0 + x4 * y4 * y3 ^ 2 * x2 * y2 * x1 * y1 * y0
  - x4 * y4 * y3 ^ 2 * y2 ^ 3 * x0 ^ 2 + x4 * y4 * y3 ^ 2 * y2 ^ 2 * x1 * y1 * x0
  + x4 * y4 * y3 ^ 2 * y2 ^ 2 * y1 ^ 2 * y0 + 4 * x4 ^ 3 * x3 * x0 ^ 2 * y0 ^ 2
  + 5 * x4 ^ 3 * y3 * x0 * y0 ^ 3 + 6 * x4 ^ 3 * x2 * x1 * x0 * y0 ^ 2
  + 5 * x4 ^ 3 * x2 * y1 * y0 ^ 3 - 8 * x4 ^ 3 * y2 * x1 * x0 ^ 2 * y0
  - 7 * x4 ^ 3 * y2 * y1 * x0 * y0 ^ 2 - 4 * x4 ^ 3 * x1 ^ 3 * x0 ^ 2
  - 7 * x4 ^ 3 * x1 ^ 2 * y1 * x0 * y0 - 3 * x4 ^ 3 * x1 * y1 ^ 2 * y0 ^ 2
  - 8 * x4 ^ 2 * y4 * x3 * x0 ^ 3 * y0 - 11 * x4 ^ 2 * y4 * y3 * x0 ^ 2 * y0 ^ 2
  - 4 * x4 ^ 2 * y4 * x2 * x1 * x0 ^ 2 * y0 - 2 * x4 ^ 2 * y4 * x2 * y1 * x0 * y0 ^ 2
  + 8 * x4 ^ 2 * y4 * y2 * x1 * x0 ^ 3 + 6 * x4 ^ 2 * y4 * y2 * y1 * x0 ^ 2 * y0
  - 5 * x4 ^ 2 * y4 * x1 ^ 2 * y1 * x0 ^ 2 - 8 * x4 ^ 2 * y4 * x1 * y1 ^ 2 * x0 * y0
  - 3 * x4 ^ 2 * y4 * y1 ^ 3 * y0 ^ 2 - 4 * x4 ^ 2 * x3 ^ 2 * x1 * x0 ^ 3
  - x4 ^ 2 * x3 ^ 2 * y1 * x0 ^ 2 * y0 - 6 * x4 ^ 2 * x3 * y3 * x1 * x0 ^ 2 * y0

/-- Terms 241–280 of `quintic10`. -/
def quintic10_6 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  x4 ^ 2 * x3 * y3 * y1 * x0 * y0 ^ 2 - 8 * x4 ^ 2 * x3 * x2 ^ 2 * x0 * y0 ^ 2
  + 12 * x4 ^ 2 * x3 * x2 * y2 * x0 ^ 2 * y0 + 2 * x4 ^ 2 * x3 * x2 * x1 ^ 2 * x0 ^ 2
  - 2 * x4 ^ 2 * x3 * x2 * x1 * y1 * x0 * y0 - 7 * x4 ^ 2 * x3 * x2 * y1 ^ 2 * y0 ^ 2
  - 4 * x4 ^ 2 * x3 * y2 ^ 2 * x0 ^ 3 - 2 * x4 ^ 2 * x3 * y2 * x1 * y1 * x0 ^ 2
  + x4 ^ 2 * x3 * y2 * y1 ^ 2 * x0 * y0 + 3 * x4 ^ 2 * x3 * x1 ^ 2 * y1 ^ 2 * x0
  + 3 * x4 ^ 2 * x3 * x1 * y1 ^ 3 * y0 + x4 ^ 2 * y3 ^ 2 * x1 * x0 * y0 ^ 2
  + 5 * x4 ^ 2 * y3 ^ 2 * y1 * y0 ^ 3 - 5 * x4 ^ 2 * y3 * x2 ^ 2 * y0 ^ 3
  + 4 * x4 ^ 2 * y3 * x2 * y2 * x0 * y0 ^ 2 + 3 * x4 ^ 2 * y3 * x2 * x1 ^ 2 * x0 * y0
  + 7 * x4 ^ 2 * y3 * x2 * x1 * y1 * y0 ^ 2 + x4 ^ 2 * y3 * y2 ^ 2 * x0 ^ 2 * y0
  + x4 ^ 2 * y3 * y2 * x1 ^ 2 * x0 ^ 2 - 10 * x4 ^ 2 * y3 * y2 * x1 * y1 * x0 * y0
  - 7 * x4 ^ 2 * y3 * y2 * y1 ^ 2 * y0 ^ 2 - 4 * x4 ^ 2 * y3 * x1 ^ 3 * y1 * x0
  - 4 * x4 ^ 2 * y3 * x1 ^ 2 * y1 ^ 2 * y0 - 2 * x4 ^ 2 * x2 ^ 3 * x1 * y0 ^ 2
  + 4 * x4 ^ 2 * x2 ^ 2 * y2 * x1 * x0 * y0 - 3 * x4 ^ 2 * x2 ^ 2 * y2 * y1 * y0 ^ 2
  + 2 * x4 ^ 2 * x2 ^ 2 * x1 ^ 3 * x0 + 2 * x4 ^ 2 * x2 ^ 2 * x1 ^ 2 * y1 * y0
  - 2 * x4 ^ 2 * x2 * y2 ^ 2 * x1 * x0 ^ 2 + 6 * x4 ^ 2 * x2 * y2 ^ 2 * y1 * x0 * y0
  + 5 * x4 ^ 2 * x2 * y2 * x1 ^ 2 * y1 * x0 + 5 * x4 ^ 2 * x2 * y2 * x1 * y1 ^ 2 * y0
  - 3 * x4 ^ 2 * y2 ^ 3 * y1 * x0 ^ 2 + 3 * x4 ^ 2 * y2 ^ 2 * x1 * y1 ^ 2 * x0
  + 3 * x4 ^ 2 * y2 ^ 2 * y1 ^ 3 * y0 + 4 * x4 * y4 ^ 2 * x3 * x0 ^ 4
  + 7 * x4 * y4 ^ 2 * y3 * x0 ^ 3 * y0 - 2 * x4 * y4 ^ 2 * x2 * x1 * x0 ^ 3
  - 3 * x4 * y4 ^ 2 * x2 * y1 * x0 ^ 2 * y0 + x4 * y4 ^ 2 * y2 * y1 * x0 ^ 3

/-- Terms 281–320 of `quintic10`. -/
def quintic10_7 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -x4 * y4 ^ 2 * x1 * y1 ^ 2 * x0 ^ 2 - x4 * y4 ^ 2 * y1 ^ 3 * x0 * y0
  - 3 * x4 * y4 * x3 ^ 2 * y1 * x0 ^ 3 - 2 * x4 * y4 * x3 * y3 * x1 * x0 ^ 3
  - 10 * x4 * y4 * x3 * y3 * y1 * x0 ^ 2 * y0 + 4 * x4 * y4 * x3 * x2 ^ 2 * x0 ^ 2 * y0
  - 4 * x4 * y4 * x3 * x2 * y2 * x0 ^ 3 + 8 * x4 * y4 * x3 * x2 * x1 * y1 * x0 ^ 2
  + 11 * x4 * y4 * x3 * x2 * y1 ^ 2 * x0 * y0 - 3 * x4 * y4 * x3 * y2 * y1 ^ 2 * x0 ^ 2
  + 3 * x4 * y4 * x3 * x1 * y1 ^ 3 * x0 + 3 * x4 * y4 * x3 * y1 ^ 4 * y0
  - 8 * x4 * y4 * y3 ^ 2 * x1 * x0 ^ 2 * y0 - 13 * x4 * y4 * y3 ^ 2 * y1 * x0 * y0 ^ 2
  + 3 * x4 * y4 * y3 * x2 ^ 2 * x0 * y0 ^ 2 + 2 * x4 * y4 * y3 * x2 * y2 * x0 ^ 2 * y0
  - 2 * x4 * y4 * y3 * x2 * x1 ^ 2 * x0 ^ 2 + 7 * x4 * y4 * y3 * x2 * y1 ^ 2 * y0 ^ 2
  - 5 * x4 * y4 * y3 * y2 ^ 2 * x0 ^ 3 + 10 * x4 * y4 * y3 * y2 * x1 * y1 * x0 ^ 2
  + 5 * x4 * y4 * y3 * y2 * y1 ^ 2 * x0 * y0 - 5 * x4 * y4 * y3 * x1 ^ 2 * y1 ^ 2 * x0
  - 5 * x4 * y4 * y3 * x1 * y1 ^ 3 * y0 + x4 * y4 * x2 ^ 3 * y1 * y0 ^ 2
  - 2 * x4 * y4 * x2 ^ 2 * y2 * y1 * x0 * y0 - x4 * y4 * x2 ^ 2 * x1 ^ 2 * y1 * x0
  - x4 * y4 * x2 ^ 2 * x1 * y1 ^ 2 * y0 + x4 * y4 * x2 * y2 ^ 2 * y1 * x0 ^ 2
  - x4 * y4 * x2 * y2 * x1 * y1 ^ 2 * x0 - x4 * y4 * x2 * y2 * y1 ^ 3 * y0
  - 2 * x4 * x3 ^ 3 * x2 * x0 ^ 3 - 6 * x4 * x3 ^ 2 * y3 * x2 * x0 ^ 2 * y0
  - x4 * x3 ^ 2 * y3 * y2 * x0 ^ 3 + 4 * x4 * x3 ^ 2 * x2 ^ 2 * x1 * x0 ^ 2
  + 6 * x4 * x3 ^ 2 * x2 ^ 2 * y1 * x0 * y0 - 2 * x4 * x3 ^ 2 * x2 * y2 * y1 * x0 ^ 2
  + 2 * x4 * x3 ^ 2 * x2 * x1 * y1 ^ 2 * x0 + 2 * x4 * x3 ^ 2 * x2 * y1 ^ 3 * y0
  - 9 * x4 * x3 * y3 ^ 2 * x2 * x0 * y0 ^ 2 + x4 * x3 * y3 ^ 2 * y2 * x0 ^ 2 * y0

/-- Terms 321–360 of `quintic10`. -/
def quintic10_8 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -2 * x4 * x3 * y3 ^ 2 * x1 ^ 2 * x0 ^ 2 - 5 * x4 * x3 * y3 ^ 2 * x1 * y1 * x0 * y0
  - 3 * x4 * x3 * y3 ^ 2 * y1 ^ 2 * y0 ^ 2 + 2 * x4 * x3 * y3 * x2 ^ 2 * x1 * x0 * y0
  + 6 * x4 * x3 * y3 * x2 ^ 2 * y1 * y0 ^ 2 + 8 * x4 * x3 * y3 * x2 * y2 * x1 * x0 ^ 2
  + 5 * x4 * x3 * y3 * x2 * y2 * y1 * x0 * y0 - 4 * x4 * x3 * y3 * x2 * x1 ^ 2 * y1 * x0
  - 4 * x4 * x3 * y3 * x2 * x1 * y1 ^ 2 * y0 - x4 * x3 * y3 * y2 ^ 2 * y1 * x0 ^ 2
  + x4 * x3 * y3 * y2 * x1 * y1 ^ 2 * x0 + x4 * x3 * y3 * y2 * y1 ^ 3 * y0
  + 2 * x4 * x3 * x2 ^ 4 * y0 ^ 2 - 4 * x4 * x3 * x2 ^ 3 * y2 * x0 * y0
  - 2 * x4 * x3 * x2 ^ 3 * x1 ^ 2 * x0 - 2 * x4 * x3 * x2 ^ 3 * x1 * y1 * y0
  + 2 * x4 * x3 * x2 ^ 2 * y2 ^ 2 * x0 ^ 2 - 2 * x4 * x3 * x2 ^ 2 * y2 * x1 * y1 * x0
  - 2 * x4 * x3 * x2 ^ 2 * y2 * y1 ^ 2 * y0 - 5 * x4 * y3 ^ 3 * x2 * y0 ^ 3
  + 2 * x4 * y3 ^ 3 * y2 * x0 * y0 ^ 2 + x4 * y3 ^ 3 * x1 ^ 2 * x0 * y0
  + x4 * y3 ^ 3 * x1 * y1 * y0 ^ 2 - 4 * x4 * y3 ^ 2 * x2 ^ 2 * x1 * y0 ^ 2
  + 11 * x4 * y3 ^ 2 * x2 * y2 * x1 * x0 * y0 + 6 * x4 * y3 ^ 2 * x2 * y2 * y1 * y0 ^ 2
  + 4 * x4 * y3 ^ 2 * x2 * x1 ^ 3 * x0 + 4 * x4 * y3 ^ 2 * x2 * x1 ^ 2 * y1 * y0
  - x4 * y3 ^ 2 * y2 ^ 2 * x1 * x0 ^ 2 + x4 * y3 ^ 2 * y2 * x1 ^ 2 * y1 * x0
  + x4 * y3 ^ 2 * y2 * x1 * y1 ^ 2 * y0 + 3 * x4 * y3 * x2 ^ 3 * y2 * y0 ^ 2
  - 6 * x4 * y3 * x2 ^ 2 * y2 ^ 2 * x0 * y0 - 3 * x4 * y3 * x2 ^ 2 * y2 * x1 ^ 2 * x0
  - 3 * x4 * y3 * x2 ^ 2 * y2 * x1 * y1 * y0 + 3 * x4 * y3 * x2 * y2 ^ 3 * x0 ^ 2
  - 3 * x4 * y3 * x2 * y2 ^ 2 * x1 * y1 * x0 - 3 * x4 * y3 * x2 * y2 ^ 2 * y1 ^ 2 * y0
  - y4 ^ 3 * y3 * x0 ^ 4 + y4 ^ 2 * x3 * y3 * y1 * x0 ^ 3

/-- Terms 361–400 of `quintic10`. -/
def quintic10_9 (_x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  3 * y4 ^ 2 * y3 ^ 2 * x1 * x0 ^ 3 + 4 * y4 ^ 2 * y3 ^ 2 * y1 * x0 ^ 2 * y0
  - 2 * y4 ^ 2 * y3 * x2 ^ 2 * x0 ^ 2 * y0 + 2 * y4 ^ 2 * y3 * x2 * y2 * x0 ^ 3
  - 3 * y4 ^ 2 * y3 * x2 * x1 * y1 * x0 ^ 2 - 4 * y4 ^ 2 * y3 * x2 * y1 ^ 2 * x0 * y0
  + y4 ^ 2 * y3 * y2 * y1 ^ 2 * x0 ^ 2 - y4 ^ 2 * y3 * x1 * y1 ^ 3 * x0
  - y4 ^ 2 * y3 * y1 ^ 4 * y0 + y4 * x3 ^ 2 * y3 * x2 * x0 ^ 3
  + 5 * y4 * x3 * y3 ^ 2 * x2 * x0 ^ 2 * y0 - 3 * y4 * x3 * y3 ^ 2 * y2 * x0 ^ 3
  + y4 * x3 * y3 ^ 2 * x1 * y1 * x0 ^ 2 + y4 * x3 * y3 ^ 2 * y1 ^ 2 * x0 * y0
  - 2 * y4 * x3 * y3 * x2 ^ 2 * x1 * x0 ^ 2 - 3 * y4 * x3 * y3 * x2 ^ 2 * y1 * x0 * y0
  + y4 * x3 * y3 * x2 * y2 * y1 * x0 ^ 2 - y4 * x3 * y3 * x2 * x1 * y1 ^ 2 * x0
  - y4 * x3 * y3 * x2 * y1 ^ 3 * y0 + 4 * y4 * y3 ^ 3 * x2 * x0 * y0 ^ 2
  - 3 * y4 * y3 ^ 3 * y2 * x0 ^ 2 * y0 - 3 * y4 * y3 ^ 3 * x1 ^ 2 * x0 ^ 2
  - 5 * y4 * y3 ^ 3 * x1 * y1 * x0 * y0 - 2 * y4 * y3 ^ 3 * y1 ^ 2 * y0 ^ 2
  - y4 * y3 ^ 2 * x2 ^ 2 * x1 * x0 * y0 - 4 * y4 * y3 ^ 2 * x2 ^ 2 * y1 * y0 ^ 2
  - y4 * y3 ^ 2 * x2 * y2 * x1 * x0 ^ 2 + 4 * y4 * y3 ^ 2 * x2 * y2 * y1 * x0 * y0
  + 3 * y4 * y3 ^ 2 * x2 * x1 ^ 2 * y1 * x0 + 3 * y4 * y3 ^ 2 * x2 * x1 * y1 ^ 2 * y0
  - 2 * y4 * y3 ^ 2 * y2 ^ 2 * y1 * x0 ^ 2 + 2 * y4 * y3 ^ 2 * y2 * x1 * y1 ^ 2 * x0
  + 2 * y4 * y3 ^ 2 * y2 * y1 ^ 3 * y0 - y4 * y3 * x2 ^ 4 * y0 ^ 2
  + 2 * y4 * y3 * x2 ^ 3 * y2 * x0 * y0 + y4 * y3 * x2 ^ 3 * x1 ^ 2 * x0
  + y4 * y3 * x2 ^ 3 * x1 * y1 * y0 - y4 * y3 * x2 ^ 2 * y2 ^ 2 * x0 ^ 2
  + y4 * y3 * x2 ^ 2 * y2 * x1 * y1 * x0 + y4 * y3 * x2 ^ 2 * y2 * y1 ^ 2 * y0

/-- Terms 401–440 of `quintic10`. -/
def quintic10_10 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -x3 ^ 3 * y3 ^ 2 * x0 ^ 3 - 3 * x3 ^ 2 * y3 ^ 3 * x0 ^ 2 * y0
  + 2 * x3 ^ 2 * y3 ^ 2 * x2 * x1 * x0 ^ 2 + 3 * x3 ^ 2 * y3 ^ 2 * x2 * y1 * x0 * y0
  - x3 ^ 2 * y3 ^ 2 * y2 * y1 * x0 ^ 2 + x3 ^ 2 * y3 ^ 2 * x1 * y1 ^ 2 * x0
  + x3 ^ 2 * y3 ^ 2 * y1 ^ 3 * y0 - 3 * x3 * y3 ^ 4 * x0 * y0 ^ 2
  + x3 * y3 ^ 3 * x2 * x1 * x0 * y0 + 3 * x3 * y3 ^ 3 * x2 * y1 * y0 ^ 2
  + 3 * x3 * y3 ^ 3 * y2 * x1 * x0 ^ 2 + x3 * y3 ^ 3 * y2 * y1 * x0 * y0
  - 2 * x3 * y3 ^ 3 * x1 ^ 2 * y1 * x0 - 2 * x3 * y3 ^ 3 * x1 * y1 ^ 2 * y0
  + x3 * y3 ^ 2 * x2 ^ 3 * y0 ^ 2 - 2 * x3 * y3 ^ 2 * x2 ^ 2 * y2 * x0 * y0
  - x3 * y3 ^ 2 * x2 ^ 2 * x1 ^ 2 * x0 - x3 * y3 ^ 2 * x2 ^ 2 * x1 * y1 * y0
  + x3 * y3 ^ 2 * x2 * y2 ^ 2 * x0 ^ 2 - x3 * y3 ^ 2 * x2 * y2 * x1 * y1 * x0
  - x3 * y3 ^ 2 * x2 * y2 * y1 ^ 2 * y0 - y3 ^ 5 * y0 ^ 3 - y3 ^ 4 * x2 * x1 * y0 ^ 2
  + 3 * y3 ^ 4 * y2 * x1 * x0 * y0 + 2 * y3 ^ 4 * y2 * y1 * y0 ^ 2 + y3 ^ 4 * x1 ^ 3 * x0
  + y3 ^ 4 * x1 ^ 2 * y1 * y0 + y3 ^ 3 * x2 ^ 2 * y2 * y0 ^ 2
  - 2 * y3 ^ 3 * x2 * y2 ^ 2 * x0 * y0 - y3 ^ 3 * x2 * y2 * x1 ^ 2 * x0
  - y3 ^ 3 * x2 * y2 * x1 * y1 * y0 + y3 ^ 3 * y2 ^ 3 * x0 ^ 2 - y3 ^ 3 * y2 ^ 2 * x1 * y1 * x0
  - y3 ^ 3 * y2 ^ 2 * y1 ^ 2 * y0 - 5 * x4 ^ 2 * x2 * x0 ^ 2 * y0 ^ 2
  + 4 * x4 ^ 2 * y2 * x0 ^ 3 * y0 + 6 * x4 ^ 2 * x1 ^ 2 * x0 ^ 3
  + 11 * x4 ^ 2 * x1 * y1 * x0 ^ 2 * y0 + 5 * x4 ^ 2 * y1 ^ 2 * x0 * y0 ^ 2
  + 6 * x4 * y4 * x2 * x0 ^ 3 * y0

/-- Terms 441–480 of `quintic10`. -/
def quintic10_11 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -4 * x4 * y4 * y2 * x0 ^ 4 + x4 * y4 * x1 * y1 * x0 ^ 3 + x4 * y4 * y1 ^ 2 * x0 ^ 2 * y0
  + 2 * x4 * x3 ^ 2 * x0 ^ 4 + 7 * x4 * x3 * y3 * x0 ^ 3 * y0 + 2 * x4 * x3 * x2 * x1 * x0 ^ 3
  - 4 * x4 * x3 * x2 * y1 * x0 ^ 2 * y0 + 5 * x4 * x3 * y2 * y1 * x0 ^ 3
  - 2 * x4 * x3 * x1 * y1 ^ 2 * x0 ^ 2 - 2 * x4 * x3 * y1 ^ 3 * x0 * y0
  + 5 * x4 * y3 ^ 2 * x0 ^ 2 * y0 ^ 2 + 2 * x4 * y3 * x2 * x1 * x0 ^ 2 * y0
  - 5 * x4 * y3 * x2 * y1 * x0 * y0 ^ 2 - 5 * x4 * y3 * y2 * x1 * x0 ^ 3
  + x4 * y3 * y2 * y1 * x0 ^ 2 * y0 + 8 * x4 * y3 * x1 ^ 2 * y1 * x0 ^ 2
  + 13 * x4 * y3 * x1 * y1 ^ 2 * x0 * y0 + 5 * x4 * y3 * y1 ^ 3 * y0 ^ 2
  + 5 * x4 * x2 ^ 3 * x0 * y0 ^ 2 - 8 * x4 * x2 ^ 2 * y2 * x0 ^ 2 * y0
  - 4 * x4 * x2 ^ 2 * x1 ^ 2 * x0 ^ 2 - 3 * x4 * x2 ^ 2 * x1 * y1 * x0 * y0
  + 5 * x4 * x2 ^ 2 * y1 ^ 2 * y0 ^ 2 + 3 * x4 * x2 * y2 ^ 2 * x0 ^ 3
  - 2 * x4 * x2 * y2 * x1 * y1 * x0 ^ 2 - 9 * x4 * x2 * y2 * y1 ^ 2 * x0 * y0
  - 4 * x4 * x2 * x1 ^ 2 * y1 ^ 2 * x0 - 4 * x4 * x2 * x1 * y1 ^ 3 * y0
  + 3 * x4 * y2 ^ 2 * y1 ^ 2 * x0 ^ 2 - 3 * x4 * y2 * x1 * y1 ^ 3 * x0
  - 3 * x4 * y2 * y1 ^ 4 * y0 - y4 ^ 2 * x2 * x0 ^ 4 - 3 * y4 * x3 * y3 * x0 ^ 4
  + y4 * x3 * x2 * y1 * x0 ^ 3 - 3 * y4 * y3 ^ 2 * x0 ^ 3 * y0 + 5 * y4 * y3 * x2 * x1 * x0 ^ 3
  + 7 * y4 * y3 * x2 * y1 * x0 ^ 2 * y0 - y4 * y3 * y2 * y1 * x0 ^ 3
  + y4 * y3 * x1 * y1 ^ 2 * x0 ^ 2 + y4 * y3 * y1 ^ 3 * x0 * y0

/-- Terms 481–520 of `quintic10`. -/
def quintic10_12 (_x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  -2 * y4 * x2 ^ 3 * x0 ^ 2 * y0 + 2 * y4 * x2 ^ 2 * y2 * x0 ^ 3
  - 3 * y4 * x2 ^ 2 * x1 * y1 * x0 ^ 2 - 4 * y4 * x2 ^ 2 * y1 ^ 2 * x0 * y0
  + y4 * x2 * y2 * y1 ^ 2 * x0 ^ 2 - y4 * x2 * x1 * y1 ^ 3 * x0 - y4 * x2 * y1 ^ 4 * y0
  + 2 * x3 ^ 2 * y3 * y1 * x0 ^ 3 + x3 ^ 2 * x2 ^ 2 * x0 ^ 3 + 3 * x3 * y3 ^ 2 * x1 * x0 ^ 3
  + 7 * x3 * y3 ^ 2 * y1 * x0 ^ 2 * y0 + 3 * x3 * y3 * x2 ^ 2 * x0 ^ 2 * y0
  - x3 * y3 * x2 * y2 * x0 ^ 3 - 4 * x3 * y3 * x2 * x1 * y1 * x0 ^ 2
  - 6 * x3 * y3 * x2 * y1 ^ 2 * x0 * y0 + 2 * x3 * y3 * y2 * y1 ^ 2 * x0 ^ 2
  - 2 * x3 * y3 * x1 * y1 ^ 3 * x0 - 2 * x3 * y3 * y1 ^ 4 * y0 - 2 * x3 * x2 ^ 3 * x1 * x0 ^ 2
  - 3 * x3 * x2 ^ 3 * y1 * x0 * y0 + x3 * x2 ^ 2 * y2 * y1 * x0 ^ 2
  - x3 * x2 ^ 2 * x1 * y1 ^ 2 * x0 - x3 * x2 ^ 2 * y1 ^ 3 * y0 + 3 * y3 ^ 3 * x1 * x0 ^ 2 * y0
  + 5 * y3 ^ 3 * y1 * x0 * y0 ^ 2 + 5 * y3 ^ 2 * x2 ^ 2 * x0 * y0 ^ 2
  - 7 * y3 ^ 2 * x2 * y2 * x0 ^ 2 * y0 - 4 * y3 ^ 2 * x2 * x1 ^ 2 * x0 ^ 2
  - 7 * y3 ^ 2 * x2 * x1 * y1 * x0 * y0 - 5 * y3 ^ 2 * x2 * y1 ^ 2 * y0 ^ 2
  + 3 * y3 ^ 2 * y2 ^ 2 * x0 ^ 3 - 5 * y3 ^ 2 * y2 * x1 * y1 * x0 ^ 2
  - 3 * y3 ^ 2 * y2 * y1 ^ 2 * x0 * y0 + 2 * y3 ^ 2 * x1 ^ 2 * y1 ^ 2 * x0
  + 2 * y3 ^ 2 * x1 * y1 ^ 3 * y0 - y3 * x2 ^ 3 * x1 * x0 * y0 - 5 * y3 * x2 ^ 3 * y1 * y0 ^ 2
  - y3 * x2 ^ 2 * y2 * x1 * x0 ^ 2 + 6 * y3 * x2 ^ 2 * y2 * y1 * x0 * y0
  + 4 * y3 * x2 ^ 2 * x1 ^ 2 * y1 * x0

/-- Terms 521–549 of `quintic10`. -/
def quintic10_13 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  4 * y3 * x2 ^ 2 * x1 * y1 ^ 2 * y0 - 3 * y3 * x2 * y2 ^ 2 * y1 * x0 ^ 2
  + 3 * y3 * x2 * y2 * x1 * y1 ^ 2 * x0 + 3 * y3 * x2 * y2 * y1 ^ 3 * y0 - x2 ^ 5 * y0 ^ 2
  + 2 * x2 ^ 4 * y2 * x0 * y0 + x2 ^ 4 * x1 ^ 2 * x0 + x2 ^ 4 * x1 * y1 * y0
  - x2 ^ 3 * y2 ^ 2 * x0 ^ 2 + x2 ^ 3 * y2 * x1 * y1 * x0 + x2 ^ 3 * y2 * y1 ^ 2 * y0
  - 4 * x4 * x1 * x0 ^ 4 - 5 * x4 * y1 * x0 ^ 3 * y0 + y4 * y1 * x0 ^ 4 - 2 * x3 * x2 * x0 ^ 4
  - x3 * y1 ^ 2 * x0 ^ 3 - 5 * y3 * x2 * x0 ^ 3 * y0 + 3 * y3 * y2 * x0 ^ 4
  - 4 * y3 * x1 * y1 * x0 ^ 3 - 5 * y3 * y1 ^ 2 * x0 ^ 2 * y0 + 2 * x2 ^ 2 * x1 * x0 ^ 3
  + 5 * x2 ^ 2 * y1 * x0 ^ 2 * y0 - 3 * x2 * y2 * y1 * x0 ^ 3 + 4 * x2 * x1 * y1 ^ 2 * x0 ^ 2
  + 5 * x2 * y1 ^ 3 * x0 * y0 - y2 * y1 ^ 3 * x0 ^ 2 + x1 * y1 ^ 4 * x0 + y1 ^ 5 * y0 + x0 ^ 5

/-- The Bilharz determinant `Δ₁₀` of the monic quintic `s⁵ + a₄ s⁴ + … + a₀`,
in the real and imaginary parts of the coefficients (549 terms, 14 parts). -/
def quintic10 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  quintic10_0 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic10_1 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic10_2 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic10_3 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic10_4 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic10_5 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic10_6 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic10_7 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic10_8 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic10_9 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic10_10 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic10_11 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0
    + quintic10_12 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 + quintic10_13 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0

end BilharzPoly

/-! ## The determinants of complex coefficients -/

/-- The Bilharz determinant `Δ₂` of `c s³ + a₂ s² + a₁ s + a₀` (`BilharzPoly.cubic2`). -/
def cubicBilharz2 (c a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.cubic2 c.re c.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₄` of `c s³ + a₂ s² + a₁ s + a₀` (`BilharzPoly.cubic4`). -/
def cubicBilharz4 (c a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.cubic4 c.re c.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₆` of `c s³ + a₂ s² + a₁ s + a₀` (`BilharzPoly.cubic6`). -/
def cubicBilharz6 (c a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.cubic6 c.re c.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₂` of `c s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` (`BilharzPoly.quartic2`). -/
def quarticBilharz2 (c a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quartic2 c.re c.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₄` of `c s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` (`BilharzPoly.quartic4`). -/
def quarticBilharz4 (c a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quartic4 c.re c.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₆` of `c s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` (`BilharzPoly.quartic6`). -/
def quarticBilharz6 (c a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quartic6 c.re c.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₈` of `c s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` (`BilharzPoly.quartic8`). -/
def quarticBilharz8 (c a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quartic8 c.re c.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₂` of `s⁵ + a₄ s⁴ + … + a₀` (`BilharzPoly.quintic2`). -/
def quinticBilharz2 (a4 a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quintic2 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₄` of `s⁵ + a₄ s⁴ + … + a₀` (`BilharzPoly.quintic4`). -/
def quinticBilharz4 (a4 a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quintic4 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₆` of `s⁵ + a₄ s⁴ + … + a₀` (`BilharzPoly.quintic6`). -/
def quinticBilharz6 (a4 a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quintic6 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₈` of `s⁵ + a₄ s⁴ + … + a₀` (`BilharzPoly.quintic8`). -/
def quinticBilharz8 (a4 a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quintic8 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-- The Bilharz determinant `Δ₁₀` of `s⁵ + a₄ s⁴ + … + a₀` (`BilharzPoly.quintic10`). -/
def quinticBilharz10 (a4 a3 a2 a1 a0 : ℂ) : ℝ :=
  BilharzPoly.quintic10 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im

/-! ## Polynomial identities -/

section Identities

open BilharzPoly

/-- For a monic cubic the determinants are the conditions of `complexCubic_roots_re_neg_iff`. -/
@[tmio T, powerlib_foundation] private theorem cubic_one (h2 h1 h0 : ℂ) :
    cubic2 1 0 h2.re h2.im h1.re h1.im h0.re h0.im = h2.re ∧
      cubic4 1 0 h2.re h2.im h1.re h1.im h0.re h0.im =
        h2.re * (h1.re * h2.re + h1.im * h2.im - h0.re) - h1.im ^ 2 ∧
      cubic6 1 0 h2.re h2.im h1.re h1.im h0.re h0.im = complexCubicDet h2 h1 h0 := by
  simp only [cubic2, cubic4, cubic6, complexCubicDet]
  exact ⟨by ring, by ring, by ring⟩

@[tmio T, powerlib_foundation] private theorem cubic_scale2 (cr ci x2 y2 x1 y1 x0 y0 : ℝ) :
    cubic2 cr ci (cr * x2 - ci * y2) (cr * y2 + ci * x2) (cr * x1 - ci * y1) (cr * y1 + ci * x1)
      (cr * x0 - ci * y0) (cr * y0 + ci * x0) =
      (cr * cr + ci * ci) ^ 1 * cubic2 1 0 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.cubic2]
  ring

@[tmio T, powerlib_foundation] private theorem cubic_scale4 (cr ci x2 y2 x1 y1 x0 y0 : ℝ) :
    cubic4 cr ci (cr * x2 - ci * y2) (cr * y2 + ci * x2) (cr * x1 - ci * y1) (cr * y1 + ci * x1)
      (cr * x0 - ci * y0) (cr * y0 + ci * x0) =
      (cr * cr + ci * ci) ^ 2 * cubic4 1 0 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.cubic4]
  ring

@[tmio T, powerlib_foundation] private theorem cubic_scale6 (cr ci x2 y2 x1 y1 x0 y0 : ℝ) :
    cubic6 cr ci (cr * x2 - ci * y2) (cr * y2 + ci * x2) (cr * x1 - ci * y1) (cr * y1 + ci * x1)
      (cr * x0 - ci * y0) (cr * y0 + ci * x0) =
      (cr * cr + ci * ci) ^ 3 * cubic6 1 0 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.cubic6]
  ring

@[tmio T, powerlib_foundation] private theorem quartic_scale2 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic2 cr ci (cr * x3 - ci * y3) (cr * y3 + ci * x3) (cr * x2 - ci * y2) (cr * y2 + ci * x2)
      (cr * x1 - ci * y1) (cr * y1 + ci * x1) (cr * x0 - ci * y0) (cr * y0 + ci * x0) =
      (cr * cr + ci * ci) ^ 1 * quartic2 1 0 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic2]
  ring

@[tmio T, powerlib_foundation] private theorem quartic_scale4 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic4 cr ci (cr * x3 - ci * y3) (cr * y3 + ci * x3) (cr * x2 - ci * y2) (cr * y2 + ci * x2)
      (cr * x1 - ci * y1) (cr * y1 + ci * x1) (cr * x0 - ci * y0) (cr * y0 + ci * x0) =
      (cr * cr + ci * ci) ^ 2 * quartic4 1 0 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic4]
  ring

@[tmio T, powerlib_foundation] private theorem quartic_scale6 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic6 cr ci (cr * x3 - ci * y3) (cr * y3 + ci * x3) (cr * x2 - ci * y2) (cr * y2 + ci * x2)
      (cr * x1 - ci * y1) (cr * y1 + ci * x1) (cr * x0 - ci * y0) (cr * y0 + ci * x0) =
      (cr * cr + ci * ci) ^ 3 * quartic6 1 0 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic6_0, BilharzPoly.quartic6_1, BilharzPoly.quartic6]
  ring

@[tmio T, powerlib_foundation] private theorem quartic_scale8 (cr ci x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic8 cr ci (cr * x3 - ci * y3) (cr * y3 + ci * x3) (cr * x2 - ci * y2) (cr * y2 + ci * x2)
      (cr * x1 - ci * y1) (cr * y1 + ci * x1) (cr * x0 - ci * y0) (cr * y0 + ci * x0) =
      (cr * cr + ci * ci) ^ 4 * quartic8 1 0 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic8_0, BilharzPoly.quartic8_1, BilharzPoly.quartic8_2,
    BilharzPoly.quartic8_3, BilharzPoly.quartic8_4, BilharzPoly.quartic8_5, BilharzPoly.quartic8]
  ring

@[tmio T, powerlib_foundation] private theorem quartic_step4 (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    cubic2 (x3 * x3) (x3 * y3 - y2) (x3 * x2 - x1) (x3 * y2) (x3 * x1) (x3 * y1 - y0) (x3 * x0)
      (x3 * y0) =
      x3 ^ 1 * quartic4 1 0 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.cubic2, BilharzPoly.quartic4]
  ring

@[tmio T, powerlib_foundation] private theorem quartic_step6 (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    cubic4 (x3 * x3) (x3 * y3 - y2) (x3 * x2 - x1) (x3 * y2) (x3 * x1) (x3 * y1 - y0) (x3 * x0)
      (x3 * y0) =
      x3 ^ 3 * quartic6 1 0 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.cubic4, BilharzPoly.quartic6_0, BilharzPoly.quartic6_1,
    BilharzPoly.quartic6]
  ring

@[tmio T, powerlib_foundation] private theorem quartic_step8 (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    cubic6 (x3 * x3) (x3 * y3 - y2) (x3 * x2 - x1) (x3 * y2) (x3 * x1) (x3 * y1 - y0) (x3 * x0)
      (x3 * y0) =
      x3 ^ 5 * quartic8 1 0 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.cubic6, BilharzPoly.quartic8_0, BilharzPoly.quartic8_1,
    BilharzPoly.quartic8_2, BilharzPoly.quartic8_3, BilharzPoly.quartic8_4, BilharzPoly.quartic8_5,
    BilharzPoly.quartic8]
  ring

@[tmio T, powerlib_foundation] private theorem quintic_step4 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic2 (x4 * x4) (x4 * y4 - y3) (x4 * x3 - x2) (x4 * y3) (x4 * x2) (x4 * y2 - y1)
      (x4 * x1 - x0) (x4 * y1) (x4 * x0) (x4 * y0) =
      x4 ^ 1 * quintic4 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic2, BilharzPoly.quintic4]
  ring

@[tmio T, powerlib_foundation] private theorem quintic_step6 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic4 (x4 * x4) (x4 * y4 - y3) (x4 * x3 - x2) (x4 * y3) (x4 * x2) (x4 * y2 - y1)
      (x4 * x1 - x0) (x4 * y1) (x4 * x0) (x4 * y0) =
      x4 ^ 3 * quintic6 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic4, BilharzPoly.quintic6]
  ring

@[tmio T, powerlib_foundation] private theorem quintic_step8 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic6 (x4 * x4) (x4 * y4 - y3) (x4 * x3 - x2) (x4 * y3) (x4 * x2) (x4 * y2 - y1)
      (x4 * x1 - x0) (x4 * y1) (x4 * x0) (x4 * y0) =
      x4 ^ 5 * quintic8 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic6_0, BilharzPoly.quartic6_1, BilharzPoly.quartic6,
    BilharzPoly.quintic8_0, BilharzPoly.quintic8_1, BilharzPoly.quintic8_2, BilharzPoly.quintic8_3,
    BilharzPoly.quintic8_4, BilharzPoly.quintic8]
  ring

@[tmio T, powerlib_foundation] private theorem quintic_step10 (x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    quartic8 (x4 * x4) (x4 * y4 - y3) (x4 * x3 - x2) (x4 * y3) (x4 * x2) (x4 * y2 - y1)
      (x4 * x1 - x0) (x4 * y1) (x4 * x0) (x4 * y0) =
      x4 ^ 7 * quintic10 x4 y4 x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [BilharzPoly.quartic8_0, BilharzPoly.quartic8_1, BilharzPoly.quartic8_2,
    BilharzPoly.quartic8_3, BilharzPoly.quartic8_4, BilharzPoly.quartic8_5, BilharzPoly.quartic8,
    BilharzPoly.quintic10_0, BilharzPoly.quintic10_1, BilharzPoly.quintic10_2,
    BilharzPoly.quintic10_3, BilharzPoly.quintic10_4, BilharzPoly.quintic10_5,
    BilharzPoly.quintic10_6, BilharzPoly.quintic10_7, BilharzPoly.quintic10_8,
    BilharzPoly.quintic10_9, BilharzPoly.quintic10_10, BilharzPoly.quintic10_11,
    BilharzPoly.quintic10_12, BilharzPoly.quintic10_13, BilharzPoly.quintic10]
  ring

end Identities

/-! ## The complex cubic with a complex leading coefficient -/

section Cubic

open BilharzPoly

/-- The determinants of `c h` for a monic `h`: `|c|^{2k}` times those of `h`, which are the three
conditions of `complexCubic_roots_re_neg_iff`. -/
@[tmio T, powerlib_foundation] private theorem cubicBilharz_mul (c h2 h1 h0 : ℂ) :
    cubicBilharz2 c (c * h2) (c * h1) (c * h0) = Complex.normSq c * h2.re ∧
      cubicBilharz4 c (c * h2) (c * h1) (c * h0) = Complex.normSq c ^ 2 *
        (h2.re * (h1.re * h2.re + h1.im * h2.im - h0.re) - h1.im ^ 2) ∧
      cubicBilharz6 c (c * h2) (c * h1) (c * h0) =
        Complex.normSq c ^ 3 * complexCubicDet h2 h1 h0 := by
  obtain ⟨o2, o4, o6⟩ := cubic_one h2 h1 h0
  simp only [cubicBilharz2, cubicBilharz4, cubicBilharz6, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply, cubic_scale2, cubic_scale4, cubic_scale6, o2, o4, o6, pow_one,
    and_self]

/-- The roots of `c s³ + …` are those of the monic cubic with coefficients `aₖ/c`. -/
@[tmio T, powerlib_foundation] private theorem cubic_roots_div {c : ℂ} (hc : c ≠ 0)
    (a2 a1 a0 : ℂ) :
    (∀ s : ℂ, c * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 = 0 → s.re < 0) ↔
      ∀ s : ℂ, s ^ 3 + a2 / c * s ^ 2 + a1 / c * s + a0 / c = 0 → s.re < 0 := by
  refine forall_congr' fun s => imp_congr_left ?_
  constructor
  · intro h; field_simp; linear_combination h
  · intro h; field_simp at h; linear_combination h

/-- **Bilharz for the complex cubic with a complex leading coefficient.** For `c ≠ 0`, every root
of `c s³ + a₂ s² + a₁ s + a₀` has negative real part iff its Bilharz determinants `Δ₂, Δ₄, Δ₆` are
positive. -/
@[tmio T, powerlib_foundation] theorem complexCubicHom_roots_re_neg_iff {c : ℂ} (hc : c ≠ 0)
    (a2 a1 a0 : ℂ) :
    (∀ s : ℂ, c * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 = 0 → s.re < 0) ↔
      0 < cubicBilharz2 c a2 a1 a0 ∧ 0 < cubicBilharz4 c a2 a1 a0 ∧
        0 < cubicBilharz6 c a2 a1 a0 := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have e : ∀ a : ℂ, c * (a / c) = a := fun a => by field_simp
  obtain ⟨m2, m4, m6⟩ := cubicBilharz_mul c (a2 / c) (a1 / c) (a0 / c)
  rw [e, e, e] at m2 m4 m6
  rw [cubic_roots_div hc, complexCubic_roots_re_neg_iff, m2, m4, m6, mul_pos_iff_of_pos_left hN,
    mul_pos_iff_of_pos_left (pow_pos hN 2), mul_pos_iff_of_pos_left (pow_pos hN 3)]

end Cubic

/-! ## The complex quartic -/

section Quartic

open BilharzPoly

/-- The monic complex quartic `X⁴ + a₃ X³ + a₂ X² + a₁ X + a₀`. -/
private def quarticC (a3 a2 a1 a0 : ℂ) : ℂ[X] :=
  X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

@[tmio T, powerlib_foundation] private theorem quarticC_natDegree (a3 a2 a1 a0 : ℂ) :
    (quarticC a3 a2 a1 a0).natDegree = 4 := by
  unfold quarticC; compute_degree!

@[tmio T, powerlib_foundation] private theorem quarticC_monic (a3 a2 a1 a0 : ℂ) :
    (quarticC a3 a2 a1 a0).Monic := by
  unfold quarticC; monicity!

@[tmio T, powerlib_foundation] private theorem quarticC_nextCoeff (a3 a2 a1 a0 : ℂ) :
    (quarticC a3 a2 a1 a0).nextCoeff = a3 := by
  rw [nextCoeff_of_natDegree_pos (by rw [quarticC_natDegree]; norm_num), quarticC_natDegree]
  simp [quarticC, coeff_X_pow]

@[tmio T, powerlib_foundation] private theorem quarticC_eval (a3 a2 a1 a0 s : ℂ) :
    (quarticC a3 a2 a1 a0).eval s = s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 := by
  simp [quarticC]

/-- The Bilharz step of the quartic, multiplied by `x₃ = Re a₃`: the cubic with coefficients
`x₃ a₃ − j Im a₂`, `x₃ a₂ − Re a₁`, `x₃ a₁ − j Im a₀`, `x₃ a₀`. -/
@[tmio T, powerlib_foundation] private theorem eval_routhStepC_quarticC {a3 a2 a1 a0 : ℂ}
    (hx : a3.re ≠ 0) (s : ℂ) :
    (routhStepC (quarticC a3 a2 a1 a0)).eval s * a3.re =
      ⟨a3.re * a3.re, a3.re * a3.im - a2.im⟩ * s ^ 3
        + ⟨a3.re * a2.re - a1.re, a3.re * a2.im⟩ * s ^ 2
        + ⟨a3.re * a1.re, a3.re * a1.im - a0.im⟩ * s + ⟨a3.re * a0.re, a3.re * a0.im⟩ := by
  have k3 : (⟨a3.re * a3.re, a3.re * a3.im - a2.im⟩ : ℂ) = a3.re * a3 - a2.im * Complex.I := by
    apply Complex.ext <;> simp
  have k2 : (⟨a3.re * a2.re - a1.re, a3.re * a2.im⟩ : ℂ) = a3.re * a2 - a1.re := by
    apply Complex.ext <;> simp
  have k1 : (⟨a3.re * a1.re, a3.re * a1.im - a0.im⟩ : ℂ) = a3.re * a1 - a0.im * Complex.I := by
    apply Complex.ext <;> simp
  have k0 : (⟨a3.re * a0.re, a3.re * a0.im⟩ : ℂ) = a3.re * a0 := by
    apply Complex.ext <;> simp
  rw [k3, k2, k1, k0, eval_routhStepC, quarticC_natDegree,
    (quarticC_monic a3 a2 a1 a0).leadingCoeff, quarticC_nextCoeff, quarticC_eval, quarticC_eval]
  simp only [map_add, map_mul, map_pow, map_neg, Complex.conj_conj, Complex.one_re]
  have e3 : conj a3 = 2 * (a3.re : ℂ) - a3 := by
    have := Complex.add_conj a3; push_cast at this; linear_combination this
  have e2 : conj a2 = a2 - 2 * (a2.im : ℂ) * Complex.I := by
    have := Complex.sub_conj a2; push_cast at this; linear_combination -this
  have e1 : conj a1 = 2 * (a1.re : ℂ) - a1 := by
    have := Complex.add_conj a1; push_cast at this; linear_combination this
  have e0 : conj a0 = a0 - 2 * (a0.im : ℂ) * Complex.I := by
    have := Complex.sub_conj a0; push_cast at this; linear_combination -this
  have hx' : (a3.re : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [e3, e2, e1, e0]
  push_cast
  field_simp
  ring

/-- **Bilharz for the monic complex quartic.** Every root of `s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` has
negative real part iff its Bilharz determinants `Δ₂ = Re a₃`, `Δ₄`, `Δ₆`, `Δ₈` are positive. -/
@[tmio T, powerlib_foundation] theorem complexQuartic_roots_re_neg_iff (a3 a2 a1 a0 : ℂ) :
    (∀ s : ℂ, s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 = 0 → s.re < 0) ↔
      0 < quarticBilharz2 1 a3 a2 a1 a0 ∧ 0 < quarticBilharz4 1 a3 a2 a1 a0 ∧
        0 < quarticBilharz6 1 a3 a2 a1 a0 ∧ 0 < quarticBilharz8 1 a3 a2 a1 a0 := by
  have hstep := hurwitz_iff_routhStepC (f := quarticC a3 a2 a1 a0)
    (by rw [quarticC_natDegree]; norm_num) one_pos
    (by rw [(quarticC_monic a3 a2 a1 a0).leadingCoeff, Complex.ofReal_one])
  simp only [quarticC_eval, quarticC_nextCoeff] at hstep
  have h2 : quarticBilharz2 1 a3 a2 a1 a0 = a3.re := by
    simp only [quarticBilharz2, quartic2, Complex.one_re, Complex.one_im]; ring
  rw [hstep, h2]
  refine and_congr_right fun hx => ?_
  have hG : (⟨a3.re * a3.re, a3.re * a3.im - a2.im⟩ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.zero_re] at this
    nlinarith
  have hroots : (∀ s, (routhStepC (quarticC a3 a2 a1 a0)).eval s = 0 → s.re < 0) ↔
      ∀ s : ℂ, ⟨a3.re * a3.re, a3.re * a3.im - a2.im⟩ * s ^ 3 +
        ⟨a3.re * a2.re - a1.re, a3.re * a2.im⟩ * s ^ 2 +
        ⟨a3.re * a1.re, a3.re * a1.im - a0.im⟩ * s + ⟨a3.re * a0.re, a3.re * a0.im⟩ = 0 →
          s.re < 0 := by
    refine forall_congr' fun s => imp_congr_left ?_
    rw [← eval_routhStepC_quarticC hx.ne' s]
    constructor
    · intro h; rw [h, zero_mul]
    · intro h; exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast hx.ne')
  rw [hroots, complexCubicHom_roots_re_neg_iff hG]
  have i4 : cubicBilharz2 ⟨a3.re * a3.re, a3.re * a3.im - a2.im⟩
      ⟨a3.re * a2.re - a1.re, a3.re * a2.im⟩ ⟨a3.re * a1.re, a3.re * a1.im - a0.im⟩
      ⟨a3.re * a0.re, a3.re * a0.im⟩ = a3.re ^ 1 * quarticBilharz4 1 a3 a2 a1 a0 :=
    quartic_step4 a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im
  have i6 : cubicBilharz4 ⟨a3.re * a3.re, a3.re * a3.im - a2.im⟩
      ⟨a3.re * a2.re - a1.re, a3.re * a2.im⟩ ⟨a3.re * a1.re, a3.re * a1.im - a0.im⟩
      ⟨a3.re * a0.re, a3.re * a0.im⟩ = a3.re ^ 3 * quarticBilharz6 1 a3 a2 a1 a0 :=
    quartic_step6 a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im
  have i8 : cubicBilharz6 ⟨a3.re * a3.re, a3.re * a3.im - a2.im⟩
      ⟨a3.re * a2.re - a1.re, a3.re * a2.im⟩ ⟨a3.re * a1.re, a3.re * a1.im - a0.im⟩
      ⟨a3.re * a0.re, a3.re * a0.im⟩ = a3.re ^ 5 * quarticBilharz8 1 a3 a2 a1 a0 :=
    quartic_step8 a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im
  rw [i4, i6, i8, mul_pos_iff_of_pos_left (pow_pos hx 1), mul_pos_iff_of_pos_left (pow_pos hx 3),
    mul_pos_iff_of_pos_left (pow_pos hx 5)]

/-- The determinants of `c h` for a monic quartic `h`: `|c|^{2k}` times those of `h`. -/
@[tmio T, powerlib_foundation] private theorem quarticBilharz_mul (c h3 h2 h1 h0 : ℂ) :
    quarticBilharz2 c (c * h3) (c * h2) (c * h1) (c * h0) =
        Complex.normSq c * quarticBilharz2 1 h3 h2 h1 h0 ∧
      quarticBilharz4 c (c * h3) (c * h2) (c * h1) (c * h0) =
        Complex.normSq c ^ 2 * quarticBilharz4 1 h3 h2 h1 h0 ∧
      quarticBilharz6 c (c * h3) (c * h2) (c * h1) (c * h0) =
        Complex.normSq c ^ 3 * quarticBilharz6 1 h3 h2 h1 h0 ∧
      quarticBilharz8 c (c * h3) (c * h2) (c * h1) (c * h0) =
        Complex.normSq c ^ 4 * quarticBilharz8 1 h3 h2 h1 h0 := by
  simp only [quarticBilharz2, quarticBilharz4, quarticBilharz6, quarticBilharz8, Complex.mul_re,
    Complex.mul_im, Complex.normSq_apply, Complex.one_re, Complex.one_im]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [quartic_scale2, pow_one]
  · rw [quartic_scale4]
  · rw [quartic_scale6]
  · rw [quartic_scale8]

/-- **Bilharz for the complex quartic with a complex leading coefficient.** For `c ≠ 0`, every
root of `c s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` has negative real part iff its Bilharz determinants
`Δ₂, Δ₄, Δ₆, Δ₈` are positive. -/
@[tmio T, powerlib_foundation] theorem complexQuarticHom_roots_re_neg_iff {c : ℂ} (hc : c ≠ 0)
    (a3 a2 a1 a0 : ℂ) :
    (∀ s : ℂ, c * s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 = 0 → s.re < 0) ↔
      0 < quarticBilharz2 c a3 a2 a1 a0 ∧ 0 < quarticBilharz4 c a3 a2 a1 a0 ∧
        0 < quarticBilharz6 c a3 a2 a1 a0 ∧ 0 < quarticBilharz8 c a3 a2 a1 a0 := by
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have e : ∀ a : ℂ, c * (a / c) = a := fun a => by field_simp
  have hroots : (∀ s : ℂ, c * s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 = 0 → s.re < 0) ↔
      ∀ s : ℂ, s ^ 4 + a3 / c * s ^ 3 + a2 / c * s ^ 2 + a1 / c * s + a0 / c = 0 → s.re < 0 := by
    refine forall_congr' fun s => imp_congr_left ?_
    constructor
    · intro h; field_simp; linear_combination h
    · intro h; field_simp at h; linear_combination h
  obtain ⟨m2, m4, m6, m8⟩ := quarticBilharz_mul c (a3 / c) (a2 / c) (a1 / c) (a0 / c)
  rw [e, e, e, e] at m2 m4 m6 m8
  rw [hroots, complexQuartic_roots_re_neg_iff, m2, m4, m6, m8, mul_pos_iff_of_pos_left hN,
    mul_pos_iff_of_pos_left (pow_pos hN 2), mul_pos_iff_of_pos_left (pow_pos hN 3),
    mul_pos_iff_of_pos_left (pow_pos hN 4)]

end Quartic

/-! ## The complex quintic -/

section Quintic

open BilharzPoly

/-- The monic complex quintic `X⁵ + a₄ X⁴ + a₃ X³ + a₂ X² + a₁ X + a₀`. -/
private def quinticC (a4 a3 a2 a1 a0 : ℂ) : ℂ[X] :=
  X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

@[tmio T, powerlib_foundation] private theorem quinticC_natDegree (a4 a3 a2 a1 a0 : ℂ) :
    (quinticC a4 a3 a2 a1 a0).natDegree = 5 := by
  unfold quinticC; compute_degree!

@[tmio T, powerlib_foundation] private theorem quinticC_monic (a4 a3 a2 a1 a0 : ℂ) :
    (quinticC a4 a3 a2 a1 a0).Monic := by
  unfold quinticC; monicity!

@[tmio T, powerlib_foundation] private theorem quinticC_nextCoeff (a4 a3 a2 a1 a0 : ℂ) :
    (quinticC a4 a3 a2 a1 a0).nextCoeff = a4 := by
  rw [nextCoeff_of_natDegree_pos (by rw [quinticC_natDegree]; norm_num), quinticC_natDegree]
  simp [quinticC, coeff_X_pow]

@[tmio T, powerlib_foundation] private theorem quinticC_eval (a4 a3 a2 a1 a0 s : ℂ) :
    (quinticC a4 a3 a2 a1 a0).eval s =
      s ^ 5 + a4 * s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 := by
  simp [quinticC]

/-- The Bilharz step of the quintic, multiplied by `x₄ = Re a₄`: the quartic with coefficients
`x₄ a₄ − j Im a₃`, `x₄ a₃ − Re a₂`, `x₄ a₂ − j Im a₁`, `x₄ a₁ − Re a₀`, `x₄ a₀`. -/
@[tmio T, powerlib_foundation] private theorem eval_routhStepC_quinticC {a4 a3 a2 a1 a0 : ℂ}
    (hx : a4.re ≠ 0) (s : ℂ) :
    (routhStepC (quinticC a4 a3 a2 a1 a0)).eval s * a4.re =
      ⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩ * s ^ 4
        + ⟨a4.re * a3.re - a2.re, a4.re * a3.im⟩ * s ^ 3
        + ⟨a4.re * a2.re, a4.re * a2.im - a1.im⟩ * s ^ 2
        + ⟨a4.re * a1.re - a0.re, a4.re * a1.im⟩ * s + ⟨a4.re * a0.re, a4.re * a0.im⟩ := by
  have k4 : (⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩ : ℂ) = a4.re * a4 - a3.im * Complex.I := by
    apply Complex.ext <;> simp
  have k3 : (⟨a4.re * a3.re - a2.re, a4.re * a3.im⟩ : ℂ) = a4.re * a3 - a2.re := by
    apply Complex.ext <;> simp
  have k2 : (⟨a4.re * a2.re, a4.re * a2.im - a1.im⟩ : ℂ) = a4.re * a2 - a1.im * Complex.I := by
    apply Complex.ext <;> simp
  have k1 : (⟨a4.re * a1.re - a0.re, a4.re * a1.im⟩ : ℂ) = a4.re * a1 - a0.re := by
    apply Complex.ext <;> simp
  have k0 : (⟨a4.re * a0.re, a4.re * a0.im⟩ : ℂ) = a4.re * a0 := by
    apply Complex.ext <;> simp
  rw [k4, k3, k2, k1, k0, eval_routhStepC, quinticC_natDegree,
    (quinticC_monic a4 a3 a2 a1 a0).leadingCoeff, quinticC_nextCoeff, quinticC_eval,
    quinticC_eval]
  simp only [map_add, map_mul, map_pow, map_neg, Complex.conj_conj, Complex.one_re]
  have e4 : conj a4 = 2 * (a4.re : ℂ) - a4 := by
    have := Complex.add_conj a4; push_cast at this; linear_combination this
  have e3 : conj a3 = a3 - 2 * (a3.im : ℂ) * Complex.I := by
    have := Complex.sub_conj a3; push_cast at this; linear_combination -this
  have e2 : conj a2 = 2 * (a2.re : ℂ) - a2 := by
    have := Complex.add_conj a2; push_cast at this; linear_combination this
  have e1 : conj a1 = a1 - 2 * (a1.im : ℂ) * Complex.I := by
    have := Complex.sub_conj a1; push_cast at this; linear_combination -this
  have e0 : conj a0 = 2 * (a0.re : ℂ) - a0 := by
    have := Complex.add_conj a0; push_cast at this; linear_combination this
  have hx' : (a4.re : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [e4, e3, e2, e1, e0]
  push_cast
  field_simp
  ring

/-- **Bilharz for the monic complex quintic.** Every root of
`s⁵ + a₄ s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` has negative real part iff its Bilharz determinants
`Δ₂ = Re a₄`, `Δ₄`, `Δ₆`, `Δ₈`, `Δ₁₀` are positive. -/
@[tmio T, powerlib_foundation] theorem complexQuintic_roots_re_neg_iff (a4 a3 a2 a1 a0 : ℂ) :
    (∀ s : ℂ, s ^ 5 + a4 * s ^ 4 + a3 * s ^ 3 + a2 * s ^ 2 + a1 * s + a0 = 0 → s.re < 0) ↔
      0 < quinticBilharz2 a4 a3 a2 a1 a0 ∧ 0 < quinticBilharz4 a4 a3 a2 a1 a0 ∧
        0 < quinticBilharz6 a4 a3 a2 a1 a0 ∧ 0 < quinticBilharz8 a4 a3 a2 a1 a0 ∧
        0 < quinticBilharz10 a4 a3 a2 a1 a0 := by
  have hstep := hurwitz_iff_routhStepC (f := quinticC a4 a3 a2 a1 a0)
    (by rw [quinticC_natDegree]; norm_num) one_pos
    (by rw [(quinticC_monic a4 a3 a2 a1 a0).leadingCoeff, Complex.ofReal_one])
  simp only [quinticC_eval, quinticC_nextCoeff] at hstep
  have h2 : quinticBilharz2 a4 a3 a2 a1 a0 = a4.re := by
    simp only [quinticBilharz2, quintic2]
  rw [hstep, h2]
  refine and_congr_right fun hx => ?_
  have hG : (⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.zero_re] at this
    nlinarith
  have hroots : (∀ s, (routhStepC (quinticC a4 a3 a2 a1 a0)).eval s = 0 → s.re < 0) ↔
      ∀ s : ℂ, ⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩ * s ^ 4 +
        ⟨a4.re * a3.re - a2.re, a4.re * a3.im⟩ * s ^ 3 +
        ⟨a4.re * a2.re, a4.re * a2.im - a1.im⟩ * s ^ 2 +
        ⟨a4.re * a1.re - a0.re, a4.re * a1.im⟩ * s + ⟨a4.re * a0.re, a4.re * a0.im⟩ = 0 →
          s.re < 0 := by
    refine forall_congr' fun s => imp_congr_left ?_
    rw [← eval_routhStepC_quinticC hx.ne' s]
    constructor
    · intro h; rw [h, zero_mul]
    · intro h; exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast hx.ne')
  rw [hroots, complexQuarticHom_roots_re_neg_iff hG]
  have i4 : quarticBilharz2 ⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩
      ⟨a4.re * a3.re - a2.re, a4.re * a3.im⟩ ⟨a4.re * a2.re, a4.re * a2.im - a1.im⟩
      ⟨a4.re * a1.re - a0.re, a4.re * a1.im⟩ ⟨a4.re * a0.re, a4.re * a0.im⟩ =
        a4.re ^ 1 * quinticBilharz4 a4 a3 a2 a1 a0 :=
    quintic_step4 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im
  have i6 : quarticBilharz4 ⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩
      ⟨a4.re * a3.re - a2.re, a4.re * a3.im⟩ ⟨a4.re * a2.re, a4.re * a2.im - a1.im⟩
      ⟨a4.re * a1.re - a0.re, a4.re * a1.im⟩ ⟨a4.re * a0.re, a4.re * a0.im⟩ =
        a4.re ^ 3 * quinticBilharz6 a4 a3 a2 a1 a0 :=
    quintic_step6 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im
  have i8 : quarticBilharz6 ⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩
      ⟨a4.re * a3.re - a2.re, a4.re * a3.im⟩ ⟨a4.re * a2.re, a4.re * a2.im - a1.im⟩
      ⟨a4.re * a1.re - a0.re, a4.re * a1.im⟩ ⟨a4.re * a0.re, a4.re * a0.im⟩ =
        a4.re ^ 5 * quinticBilharz8 a4 a3 a2 a1 a0 :=
    quintic_step8 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im
  have i10 : quarticBilharz8 ⟨a4.re * a4.re, a4.re * a4.im - a3.im⟩
      ⟨a4.re * a3.re - a2.re, a4.re * a3.im⟩ ⟨a4.re * a2.re, a4.re * a2.im - a1.im⟩
      ⟨a4.re * a1.re - a0.re, a4.re * a1.im⟩ ⟨a4.re * a0.re, a4.re * a0.im⟩ =
        a4.re ^ 7 * quinticBilharz10 a4 a3 a2 a1 a0 :=
    quintic_step10 a4.re a4.im a3.re a3.im a2.re a2.im a1.re a1.im a0.re a0.im
  rw [i4, i6, i8, i10, mul_pos_iff_of_pos_left (pow_pos hx 1),
    mul_pos_iff_of_pos_left (pow_pos hx 3), mul_pos_iff_of_pos_left (pow_pos hx 5),
    mul_pos_iff_of_pos_left (pow_pos hx 7)]

end Quintic

end powerlib.Criteria
