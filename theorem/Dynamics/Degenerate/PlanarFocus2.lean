import theorem.Dynamics.Degenerate.PlanarFocus

/-! # The planar weak focus of order five: the second Lyapunov coefficient (foundation)

At a planar centre `u̇ = g(u)` whose first Lyapunov coefficient vanishes (a weak focus of the
first order, a Bautin point), the second Lyapunov coefficient `l₂`, computed from the quintic
Taylor expansion of `g` in the rotation coordinates of its linear part, decides stability:
`l₂ < 0` gives local asymptotic stability, `l₂ > 0` instability.

Scope.
* Autonomous continuous-time ODE `u̇ = g u` on `State 2 = EuclideanSpace ℝ (Fin 2)`; no input,
  delay, switching or time variation. Behaviour is LeanForControl's `LocalAsymptoticStable` and
  `Unstable` (finite forward solution segments).
* The data: a linear map `L` with `L (L u) = −ω² u`, `ω > 0`, and a quintic jet `J : Jet5` (the
  Taylor coefficients of orders two to five, `a_{ij}`, `b_{ij}`, `2 ≤ i + j ≤ 5`) in the rotation
  coordinates `x = frameX u`, `y = frameY L ω u` of `L`
  (`theorem/Dynamics/Degenerate/PlanarFocus.lean`).
  Only the expansion of the two coordinates of `g` is assumed:
  `x(g u) = −ωy + F(x, y) + o(‖u‖⁵)`, `y(g u) = ωx + G(x, y) + o(‖u‖⁵)`; `g` need not be
  differentiable. Stability needs `g` continuous near `0`, instability `g` Lipschitz near `0`, so
  the laws apply to the chart field of a Lipschitz centre manifold
  (`theorem/Dynamics/CenterReductionBautin.lean`).
* The laws assume `l₁ = 0` (`Jet.l1` of the quadratic and cubic part). For `l₁ ≠ 0` the
  coefficient `l₂` defined here depends on the normalisation of the quartic correction and is not
  used.
* Nothing here describes a physical system: every statement is a generic identity or
  implication about arbitrary planar data, a foundation result; no model family is defined.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.3 (the Bautin
bifurcation: the normal form `ż = iωz + c₁ z|z|² + c₂ z|z|⁴`, `l₂ = Re c₂/ω`, and the formula for
`l₂(0)` in the complex Taylor coefficients `g_{kl}`); Andronov–Leontovich–Gordon–Maier, *Theory of
Bifurcations of Dynamic Systems on a Plane* (1973), §24 (focal values by the Lyapunov-function
method); Khalil, *Nonlinear Systems* (3rd ed.), Theorems 4.1 and 4.3 (local Lyapunov theorem,
Chetaev). The coefficients of the corrections `V₅`, `V₆` (the inverses of the rotation operator
on quintic and sextic forms) were computed with SymPy (untrusted) and are checked by the kernel
(`field_simp; ring`); SymPy also checked on random rational jets with `l₁ = 0` that `l₂` is the
`Re c₂/ω` of a Poincaré normal-form computation (discovery evidence only).

Results.
* The jet: `Jet5` (extends `Jet` by the quartic and quintic coefficients), `Jet5.F`, `Jet5.G` (the
  nonlinear parts of the two coordinates of the field, orders two to five).
* The Lyapunov polynomial `Jet5.W = x² + y² + V₃ + V₄ + V₅ + V₆` (`V₃`, `V₄` those of
  `PlanarFocus`; `V₅` solves the quintic homological equation, `V₆` the sextic one up to its
  kernel `(x² + y²)³`, normalised by a vanishing `y⁶` coefficient): the residuals `R₅`, `R₆`
  (`Jet5.r50` … `Jet5.r06`), the corrections (`Jet5.e50` … `Jet5.e05`, `Jet5.f60` … `Jet5.f15`),
  the obstruction `Jet5.k6` and **the second Lyapunov coefficient** `Jet5.l2 = 2 k₆/ω`.
  The homological equations order by order: `Jet5.deg3`, `Jet5.deg4` (the obstruction
  `ω l₁ (x² + y²)²`), `Jet5.deg5_residual`, `Jet5.deg5_solve`, `Jet5.deg6_residual`,
  `Jet5.deg6_solve`; together `Jet5.lie_identity` (along the quintic truncation
  `V̇ = ω l₁ (x² + y²)² + k₆ (x² + y²)³` plus ten products of degree at least seven).
* `lyap5` (`W` in the coordinates of `L`), `lyap5_sub_isBigO`, `lie5_sub_isLittleO`
  (`V̇ − ω l₁ r⁴ − k₆ r⁶ = o(‖u‖⁶)` along `g`, `r² = x² + y²`).
* Laws: `localAsymptoticStable_of_l2_neg` (`l₁ = 0`, `l₂ < 0`), `unstable_of_l2_pos` (`l₁ = 0`,
  `l₂ > 0`; Chetaev for fields Lipschitz near the point,
  `Dynamics.unstable_of_chetaev_lipschitzOn`).
* Agreement with Kuznetsov's formula: `Jet5.g20` … `Jet5.g32` (the complex Taylor coefficients
  `g_{kl}` in the coordinate `z = ⟨critVec, (x, y)⟩`, `PlanarFocus.critVec`), `Jet5.l2Kuz`
  (Kuznetsov's formula for `l₂(0)`), `Jet5.l2_sub_l2Kuz_one` (at `ω = 1` the two differ by an
  explicit multiple of `l₁`), the time rescaling `τ = ωt` (`Jet5.nrm`, the jet divided by `ω`;
  `Jet5.l1_nrm`, `Jet5.l2_nrm`, `Jet5.l2Kuz_nrm`: the three coefficients are invariant) and
  `Jet5.l2_eq_l2Kuz` (equal at every weak focus of the first order, any `ω ≠ 0`).
-/

noncomputable section

namespace powerlib.Dynamics.Degenerate.PlanarFocus

/-! ## The quintic jet and its Lyapunov polynomial -/

/-- The Taylor coefficients of orders two to five of a planar field in rotation coordinates:
`ẋ = −ωy + Σ a_{ij} xⁱ yʲ`, `ẏ = ωx + Σ b_{ij} xⁱ yʲ` (`2 ≤ i + j ≤ 5`); the orders two and three
are those of `Jet`. -/
structure Jet5 extends Jet where
  /-- Coefficient of `x⁴` in `ẋ`. -/
  a40 : ℝ
  /-- Coefficient of `x³y` in `ẋ`. -/
  a31 : ℝ
  /-- Coefficient of `x²y²` in `ẋ`. -/
  a22 : ℝ
  /-- Coefficient of `xy³` in `ẋ`. -/
  a13 : ℝ
  /-- Coefficient of `y⁴` in `ẋ`. -/
  a04 : ℝ
  /-- Coefficient of `x⁴` in `ẏ`. -/
  b40 : ℝ
  /-- Coefficient of `x³y` in `ẏ`. -/
  b31 : ℝ
  /-- Coefficient of `x²y²` in `ẏ`. -/
  b22 : ℝ
  /-- Coefficient of `xy³` in `ẏ`. -/
  b13 : ℝ
  /-- Coefficient of `y⁴` in `ẏ`. -/
  b04 : ℝ
  /-- Coefficient of `x⁵` in `ẋ`. -/
  a50 : ℝ
  /-- Coefficient of `x⁴y` in `ẋ`. -/
  a41 : ℝ
  /-- Coefficient of `x³y²` in `ẋ`. -/
  a32 : ℝ
  /-- Coefficient of `x²y³` in `ẋ`. -/
  a23 : ℝ
  /-- Coefficient of `xy⁴` in `ẋ`. -/
  a14 : ℝ
  /-- Coefficient of `y⁵` in `ẋ`. -/
  a05 : ℝ
  /-- Coefficient of `x⁵` in `ẏ`. -/
  b50 : ℝ
  /-- Coefficient of `x⁴y` in `ẏ`. -/
  b41 : ℝ
  /-- Coefficient of `x³y²` in `ẏ`. -/
  b32 : ℝ
  /-- Coefficient of `x²y³` in `ẏ`. -/
  b23 : ℝ
  /-- Coefficient of `xy⁴` in `ẏ`. -/
  b14 : ℝ
  /-- Coefficient of `y⁵` in `ẏ`. -/
  b05 : ℝ
namespace Jet5

variable (J : Jet5) (ω : ℝ)

/-- The quartic part of `ẋ`. -/
def F4 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.a40, 4, 0, 0), (J.a31, 3, 1, 0), (J.a22, 2, 2, 0), (J.a13, 1, 3, 0), (J.a04, 0, 4, 0)]

/-- The quintic part of `ẋ`. -/
def F5 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.a50, 5, 0, 0), (J.a41, 4, 1, 0), (J.a32, 3, 2, 0), (J.a23, 2, 3, 0), (J.a14, 1, 4, 0),
    (J.a05, 0, 5, 0)]

/-- The quartic part of `ẏ`. -/
def G4 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.b40, 4, 0, 0), (J.b31, 3, 1, 0), (J.b22, 2, 2, 0), (J.b13, 1, 3, 0), (J.b04, 0, 4, 0)]

/-- The quintic part of `ẏ`. -/
def G5 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.b50, 5, 0, 0), (J.b41, 4, 1, 0), (J.b32, 3, 2, 0), (J.b23, 2, 3, 0), (J.b14, 1, 4, 0),
    (J.b05, 0, 5, 0)]

/-- The nonlinear part of `ẋ`, orders two to five. -/
def F : List (ℝ × ℕ × ℕ × ℕ) := J.F2 ++ J.F3 ++ J.F4 ++ J.F5

/-- The nonlinear part of `ẏ`, orders two to five. -/
def G : List (ℝ × ℕ × ℕ × ℕ) := J.G2 ++ J.G3 ++ J.G4 ++ J.G5

/-- Coefficient of `x^5 y^0` in the quintic residual `R₅`. -/
def r50 : ℝ := 4 * J.a20 * J.d40 ω + 3 * J.a30 * J.c30 ω + 2 * J.a40 + J.b20 * J.d31 ω +
  J.b30 * J.c21 ω
/-- Coefficient of `x^4 y^1` in the quintic residual `R₅`. -/
def r41 : ℝ := 4 * J.a11 * J.d40 ω + 3 * J.a20 * J.d31 ω + 3 * J.a21 * J.c30 ω +
  2 * J.a30 * J.c21 ω + 2 * J.a31 + J.b11 * J.d31 ω + 2 * J.b20 * J.d22 ω + J.b21 * J.c21 ω +
  2 * J.b30 * J.c12 ω + 2 * J.b40
/-- Coefficient of `x^3 y^2` in the quintic residual `R₅`. -/
def r32 : ℝ := 4 * J.a02 * J.d40 ω + 3 * J.a11 * J.d31 ω + 3 * J.a12 * J.c30 ω +
  2 * J.a20 * J.d22 ω + 2 * J.a21 * J.c21 ω + 2 * J.a22 + J.a30 * J.c12 ω + J.b02 * J.d31 ω +
  2 * J.b11 * J.d22 ω + J.b12 * J.c21 ω + 3 * J.b20 * J.d13 ω + 2 * J.b21 * J.c12 ω +
  3 * J.b30 * J.c03 ω + 2 * J.b31
/-- Coefficient of `x^2 y^3` in the quintic residual `R₅`. -/
def r23 : ℝ := 3 * J.a02 * J.d31 ω + 3 * J.a03 * J.c30 ω + 2 * J.a11 * J.d22 ω +
  2 * J.a12 * J.c21 ω + 2 * J.a13 + J.a20 * J.d13 ω + J.a21 * J.c12 ω + 2 * J.b02 * J.d22 ω +
  J.b03 * J.c21 ω + 3 * J.b11 * J.d13 ω + 2 * J.b12 * J.c12 ω + 3 * J.b21 * J.c03 ω + 2 * J.b22
/-- Coefficient of `x^1 y^4` in the quintic residual `R₅`. -/
def r14 : ℝ := 2 * J.a02 * J.d22 ω + 2 * J.a03 * J.c21 ω + 2 * J.a04 + J.a11 * J.d13 ω +
  J.a12 * J.c12 ω + 3 * J.b02 * J.d13 ω + 2 * J.b03 * J.c12 ω + 3 * J.b12 * J.c03 ω + 2 * J.b13
/-- Coefficient of `x^0 y^5` in the quintic residual `R₅`. -/
def r05 : ℝ := J.a02 * J.d13 ω + J.a03 * J.c12 ω + 3 * J.b03 * J.c03 ω + 2 * J.b04
/-- Coefficient of `x^5 y^0` in the quintic correction `V₅`. -/
def e50 : ℝ := (8 * J.r05 ω + 2 * J.r23 ω + 3 * J.r41 ω) / (15 * ω)
/-- Coefficient of `x^4 y^1` in the quintic correction `V₅`. -/
def e41 : ℝ := -J.r50 ω / ω
/-- Coefficient of `x^3 y^2` in the quintic correction `V₅`. -/
def e32 : ℝ := (4 * J.r05 ω + J.r23 ω) / (3 * ω)
/-- Coefficient of `x^2 y^3` in the quintic correction `V₅`. -/
def e23 : ℝ := (-J.r32 ω - 4 * J.r50 ω) / (3 * ω)
/-- Coefficient of `x^1 y^4` in the quintic correction `V₅`. -/
def e14 : ℝ := J.r05 ω / ω
/-- Coefficient of `x^0 y^5` in the quintic correction `V₅`. -/
def e05 : ℝ := (-3 * J.r14 ω - 2 * J.r32 ω - 8 * J.r50 ω) / (15 * ω)
/-- Coefficient of `x^6 y^0` in the sextic residual `R₆`. -/
def r60 : ℝ := 5 * J.a20 * J.e50 ω + 4 * J.a30 * J.d40 ω + 3 * J.a40 * J.c30 ω + 2 * J.a50 +
  J.b20 * J.e41 ω + J.b30 * J.d31 ω + J.b40 * J.c21 ω
/-- Coefficient of `x^5 y^1` in the sextic residual `R₆`. -/
def r51 : ℝ := 5 * J.a11 * J.e50 ω + 4 * J.a20 * J.e41 ω + 4 * J.a21 * J.d40 ω +
  3 * J.a30 * J.d31 ω + 3 * J.a31 * J.c30 ω + 2 * J.a40 * J.c21 ω + 2 * J.a41 + J.b11 * J.e41 ω +
  2 * J.b20 * J.e32 ω + J.b21 * J.d31 ω + 2 * J.b30 * J.d22 ω + J.b31 * J.c21 ω +
  2 * J.b40 * J.c12 ω + 2 * J.b50
/-- Coefficient of `x^4 y^2` in the sextic residual `R₆`. -/
def r42 : ℝ := 5 * J.a02 * J.e50 ω + 4 * J.a11 * J.e41 ω + 4 * J.a12 * J.d40 ω +
  3 * J.a20 * J.e32 ω + 3 * J.a21 * J.d31 ω + 3 * J.a22 * J.c30 ω + 2 * J.a30 * J.d22 ω +
  2 * J.a31 * J.c21 ω + 2 * J.a32 + J.a40 * J.c12 ω + J.b02 * J.e41 ω + 2 * J.b11 * J.e32 ω +
  J.b12 * J.d31 ω + 3 * J.b20 * J.e23 ω + 2 * J.b21 * J.d22 ω + J.b22 * J.c21 ω +
  3 * J.b30 * J.d13 ω + 2 * J.b31 * J.c12 ω + 3 * J.b40 * J.c03 ω + 2 * J.b41
/-- Coefficient of `x^3 y^3` in the sextic residual `R₆`. -/
def r33 : ℝ := 4 * J.a02 * J.e41 ω + 4 * J.a03 * J.d40 ω + 3 * J.a11 * J.e32 ω +
  3 * J.a12 * J.d31 ω + 3 * J.a13 * J.c30 ω + 2 * J.a20 * J.e23 ω + 2 * J.a21 * J.d22 ω +
  2 * J.a22 * J.c21 ω + 2 * J.a23 + J.a30 * J.d13 ω + J.a31 * J.c12 ω + 2 * J.b02 * J.e32 ω +
  J.b03 * J.d31 ω + 3 * J.b11 * J.e23 ω + 2 * J.b12 * J.d22 ω + J.b13 * J.c21 ω +
  4 * J.b20 * J.e14 ω + 3 * J.b21 * J.d13 ω + 2 * J.b22 * J.c12 ω + 3 * J.b31 * J.c03 ω + 2 * J.b32
/-- Coefficient of `x^2 y^4` in the sextic residual `R₆`. -/
def r24 : ℝ := 3 * J.a02 * J.e32 ω + 3 * J.a03 * J.d31 ω + 3 * J.a04 * J.c30 ω +
  2 * J.a11 * J.e23 ω + 2 * J.a12 * J.d22 ω + 2 * J.a13 * J.c21 ω + 2 * J.a14 + J.a20 * J.e14 ω +
  J.a21 * J.d13 ω + J.a22 * J.c12 ω + 3 * J.b02 * J.e23 ω + 2 * J.b03 * J.d22 ω + J.b04 * J.c21 ω +
  4 * J.b11 * J.e14 ω + 3 * J.b12 * J.d13 ω + 2 * J.b13 * J.c12 ω + 5 * J.b20 * J.e05 ω +
  3 * J.b22 * J.c03 ω + 2 * J.b23
/-- Coefficient of `x^1 y^5` in the sextic residual `R₆`. -/
def r15 : ℝ := 2 * J.a02 * J.e23 ω + 2 * J.a03 * J.d22 ω + 2 * J.a04 * J.c21 ω + 2 * J.a05 +
  J.a11 * J.e14 ω + J.a12 * J.d13 ω + J.a13 * J.c12 ω + 4 * J.b02 * J.e14 ω + 3 * J.b03 * J.d13 ω +
  2 * J.b04 * J.c12 ω + 5 * J.b11 * J.e05 ω + 3 * J.b13 * J.c03 ω + 2 * J.b14
/-- Coefficient of `x^0 y^6` in the sextic residual `R₆`. -/
def r06 : ℝ := J.a02 * J.e14 ω + J.a03 * J.d13 ω + J.a04 * J.c12 ω + 5 * J.b02 * J.e05 ω +
  3 * J.b04 * J.c03 ω + 2 * J.b05
/-- Coefficient of `x^6 y^0` in the sextic correction `V₆`. -/
def f60 : ℝ := (2 * J.r15 ω + J.r33 ω + 2 * J.r51 ω) / (12 * ω)
/-- Coefficient of `x^5 y^1` in the sextic correction `V₆`. -/
def f51 : ℝ := (5 * J.r06 ω + J.r24 ω + J.r42 ω - 11 * J.r60 ω) / (16 * ω)
/-- Coefficient of `x^4 y^2` in the sextic correction `V₆`. -/
def f42 : ℝ := (2 * J.r15 ω + J.r33 ω) / (4 * ω)
/-- Coefficient of `x^3 y^3` in the sextic correction `V₆`. -/
def f33 : ℝ := (5 * J.r06 ω + J.r24 ω - J.r42 ω - 5 * J.r60 ω) / (6 * ω)
/-- Coefficient of `x^2 y^4` in the sextic correction `V₆`. -/
def f24 : ℝ := J.r15 ω / (2 * ω)
/-- Coefficient of `x^1 y^5` in the sextic correction `V₆`. -/
def f15 : ℝ := (11 * J.r06 ω - J.r24 ω - J.r42 ω - 5 * J.r60 ω) / (16 * ω)
/-- The obstruction `K₆`: the coefficient of `(x² + y²)³` in `V̇`. -/
def k6 : ℝ := (5 * J.r06 ω + J.r24 ω + J.r42 ω + 5 * J.r60 ω) / 16
/-- **The second Lyapunov coefficient** `l₂ = 2K₆/ω`: along the quintic truncation
`V̇ = ω l₁ (x² + y²)² + (ω l₂/2)(x² + y²)³ + (degree ≥ 7)`. At `l₁ = 0` it is Kuznetsov's
`Re c₂/ω` of the Poincaré normal form `ż = iωz + c₁ z|z|² + c₂ z|z|⁴` in the coordinate
`z = ⟨critVec, (x, y)⟩` (`x² + y² = 2|z|²`). -/
def l2 : ℝ := 2 * J.k6 ω / ω

/-- The quintic residual `R₅`. -/
def R5 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.r50 ω, 5, 0, 0), (J.r41 ω, 4, 1, 0), (J.r32 ω, 3, 2, 0), (J.r23 ω, 2, 3, 0),
    (J.r14 ω, 1, 4, 0), (J.r05 ω, 0, 5, 0)]

/-- The sextic residual `R₆`. -/
def R6 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.r60 ω, 6, 0, 0), (J.r51 ω, 5, 1, 0), (J.r42 ω, 4, 2, 0), (J.r33 ω, 3, 3, 0),
    (J.r24 ω, 2, 4, 0), (J.r15 ω, 1, 5, 0), (J.r06 ω, 0, 6, 0)]

/-- The quintic correction `V₅`. -/
def V5 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.e50 ω, 5, 0, 0), (J.e41 ω, 4, 1, 0), (J.e32 ω, 3, 2, 0), (J.e23 ω, 2, 3, 0),
    (J.e14 ω, 1, 4, 0), (J.e05 ω, 0, 5, 0)]

/-- The sextic correction `V₆` (the coefficient of `y⁶` is normalised to `0`). -/
def V6 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.f60 ω, 6, 0, 0), (J.f51 ω, 5, 1, 0), (J.f42 ω, 4, 2, 0), (J.f33 ω, 3, 3, 0),
    (J.f24 ω, 2, 4, 0), (J.f15 ω, 1, 5, 0)]

/-- `∂V₅/∂x`. -/
def V5x : List (ℝ × ℕ × ℕ × ℕ) :=
  [(5 * J.e50 ω, 4, 0, 0), (4 * J.e41 ω, 3, 1, 0), (3 * J.e32 ω, 2, 2, 0),
    (2 * J.e23 ω, 1, 3, 0), (J.e14 ω, 0, 4, 0)]

/-- `∂V₅/∂y`. -/
def V5y : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.e41 ω, 4, 0, 0), (2 * J.e32 ω, 3, 1, 0), (3 * J.e23 ω, 2, 2, 0),
    (4 * J.e14 ω, 1, 3, 0), (5 * J.e05 ω, 0, 4, 0)]

/-- `∂V₆/∂x`. -/
def V6x : List (ℝ × ℕ × ℕ × ℕ) :=
  [(6 * J.f60 ω, 5, 0, 0), (5 * J.f51 ω, 4, 1, 0), (4 * J.f42 ω, 3, 2, 0),
    (3 * J.f33 ω, 2, 3, 0), (2 * J.f24 ω, 1, 4, 0), (J.f15 ω, 0, 5, 0)]

/-- `∂V₆/∂y`. -/
def V6y : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.f51 ω, 5, 0, 0), (2 * J.f42 ω, 4, 1, 0), (3 * J.f33 ω, 3, 2, 0),
    (4 * J.f24 ω, 2, 3, 0), (5 * J.f15 ω, 1, 4, 0)]

/-- The Lyapunov polynomial `W = x² + y² + V₃ + V₄ + V₅ + V₆`. -/
def W : List (ℝ × ℕ × ℕ × ℕ) :=
  [(1, 2, 0, 0), (1, 0, 2, 0)] ++ J.V3 ω ++ J.V4 ω ++ J.V5 ω ++ J.V6 ω

/-- `∂W/∂x`. -/
def Wx : List (ℝ × ℕ × ℕ × ℕ) := [(2, 1, 0, 0)] ++ J.V3x ω ++ J.V4x ω ++ J.V5x ω ++ J.V6x ω

/-- `∂W/∂y`. -/
def Wy : List (ℝ × ℕ × ℕ × ℕ) := [(2, 0, 1, 0)] ++ J.V3y ω ++ J.V4y ω ++ J.V5y ω ++ J.V6y ω

/-- The derivative of `W` in the plane: `dW(x, y)(dx, dy) = W_x dx + W_y dy`. -/
@[tmio T, powerlib_foundation] theorem dpoly3_W (x y da db : ℝ) :
    dpoly3 (J.W ω) x y 0 da db 0 = poly3 (J.Wx ω) x y 0 * da + poly3 (J.Wy ω) x y 0 * db := by
  simp [W, Jet.V3, Jet.V4, V5, V6, Wx, Wy, Jet.V3x, Jet.V3y, Jet.V4x, Jet.V4y, V5x, V5y, V6x, V6y]
  ring

/-- The cubic homological equation: `L V₃ + 2(x F₂ + y G₂) = 0`. -/
@[tmio T, powerlib_foundation] theorem deg3 (hω : ω ≠ 0) (x y : ℝ) :
    2 * x * poly3 J.F2 x y 0 + 2 * y * poly3 J.G2 x y 0 +
      poly3 (J.V3x ω) x y 0 * (-ω * y) + poly3 (J.V3y ω) x y 0 * (ω * x) = 0 := by
  simp [Jet.F2, Jet.G2, Jet.V3x, Jet.V3y, Jet.c30, Jet.c21, Jet.c12, Jet.c03]
  field_simp
  ring

/-- The quartic homological equation: the residual of order four is `ω l₁ (x² + y²)²`. -/
@[tmio T, powerlib_foundation] theorem deg4 (hω : ω ≠ 0) (x y : ℝ) :
    2 * x * poly3 J.F3 x y 0 + 2 * y * poly3 J.G3 x y 0 +
      poly3 (J.V3x ω) x y 0 * poly3 J.F2 x y 0 + poly3 (J.V3y ω) x y 0 * poly3 J.G2 x y 0 +
      poly3 (J.V4x ω) x y 0 * (-ω * y) + poly3 (J.V4y ω) x y 0 * (ω * x) =
      ω * J.l1 ω * (x ^ 2 + y ^ 2) ^ 2 := by
  simp [Jet.F2, Jet.G2, Jet.F3, Jet.G3, Jet.V3x, Jet.V3y, Jet.V4x, Jet.V4y, Jet.c30, Jet.c21,
    Jet.c12, Jet.c03, Jet.d40, Jet.d31, Jet.d22, Jet.d13, Jet.l1]
  field_simp
  ring

/-- The quintic residual: the terms of order five of `V̇` from `V₂, V₃, V₄` are `R₅`. -/
@[tmio T, powerlib_foundation] theorem deg5_residual (x y : ℝ) :
    2 * x * poly3 J.F4 x y 0 + 2 * y * poly3 J.G4 x y 0 +
      poly3 (J.V3x ω) x y 0 * poly3 J.F3 x y 0 + poly3 (J.V3y ω) x y 0 * poly3 J.G3 x y 0 +
      poly3 (J.V4x ω) x y 0 * poly3 J.F2 x y 0 + poly3 (J.V4y ω) x y 0 * poly3 J.G2 x y 0 =
      poly3 (J.R5 ω) x y 0 := by
  simp only [F4, G4, Jet.F3, Jet.G3, Jet.F2, Jet.G2, Jet.V3x, Jet.V3y, Jet.V4x, Jet.V4y, R5,
    r50, r41, r32, r23, r14, r05, poly3_cons, poly3_nil]
  ring

/-- The quintic homological equation `L V₅ + R₅ = 0` (`L` invertible in odd degree). -/
@[tmio T, powerlib_foundation] theorem deg5_solve (hω : ω ≠ 0) (x y : ℝ) :
    poly3 (J.V5x ω) x y 0 * (-ω * y) + poly3 (J.V5y ω) x y 0 * (ω * x) +
      poly3 (J.R5 ω) x y 0 = 0 := by
  simp only [V5x, V5y, R5, e50, e41, e32, e23, e14, e05, poly3_cons, poly3_nil]
  field_simp
  ring

/-- The sextic residual: the terms of order six of `V̇` from `V₂, …, V₅` are `R₆`. -/
@[tmio T, powerlib_foundation] theorem deg6_residual (x y : ℝ) :
    2 * x * poly3 J.F5 x y 0 + 2 * y * poly3 J.G5 x y 0 +
      poly3 (J.V3x ω) x y 0 * poly3 J.F4 x y 0 + poly3 (J.V3y ω) x y 0 * poly3 J.G4 x y 0 +
      poly3 (J.V4x ω) x y 0 * poly3 J.F3 x y 0 + poly3 (J.V4y ω) x y 0 * poly3 J.G3 x y 0 +
      poly3 (J.V5x ω) x y 0 * poly3 J.F2 x y 0 + poly3 (J.V5y ω) x y 0 * poly3 J.G2 x y 0 =
      poly3 (J.R6 ω) x y 0 := by
  simp only [F5, G5, F4, G4, Jet.F3, Jet.G3, Jet.F2, Jet.G2, Jet.V3x, Jet.V3y, Jet.V4x, Jet.V4y,
    V5x, V5y, R6, r60, r51, r42, r33, r24, r15, r06, poly3_cons, poly3_nil]
  ring

/-- The sextic homological equation `L V₆ + R₆ = K₆ (x² + y²)³` (`(x² + y²)³` spans the kernel
of `L` in degree six). -/
@[tmio T, powerlib_foundation] theorem deg6_solve (hω : ω ≠ 0) (x y : ℝ) :
    poly3 (J.V6x ω) x y 0 * (-ω * y) + poly3 (J.V6y ω) x y 0 * (ω * x) +
      poly3 (J.R6 ω) x y 0 = J.k6 ω * (x ^ 2 + y ^ 2) ^ 3 := by
  simp only [V6x, V6y, R6, f60, f51, f42, f33, f24, f15, k6, poly3_cons, poly3_nil]
  field_simp
  ring

/-- `poly3` of a concatenation. -/
@[tmio T, powerlib_foundation] theorem poly3_append (l₁ l₂ : List (ℝ × ℕ × ℕ × ℕ)) (a b c : ℝ) :
    poly3 (l₁ ++ l₂) a b c = poly3 l₁ a b c + poly3 l₂ a b c := by
  induction l₁ with
  | nil => simp
  | cons t l ih => simp only [List.cons_append, poly3_cons, ih]; ring

/-- **The homological identity of order six.** Along the quintic truncation `ẋ = −ωy + F`,
`ẏ = ωx + G` the derivative of `W` is `ω l₁ (x² + y²)² + K₆ (x² + y²)³` plus ten products of
degree at least seven. -/
@[tmio T, powerlib_foundation] theorem lie_identity (hω : ω ≠ 0) (x y : ℝ) :
    dpoly3 (J.W ω) x y 0 (-ω * y + poly3 J.F x y 0) (ω * x + poly3 J.G x y 0) 0 -
        ω * J.l1 ω * (x ^ 2 + y ^ 2) ^ 2 - J.k6 ω * (x ^ 2 + y ^ 2) ^ 3 =
      poly3 (J.V3x ω) x y 0 * poly3 J.F5 x y 0 + poly3 (J.V3y ω) x y 0 * poly3 J.G5 x y 0 +
        poly3 (J.V4x ω) x y 0 * poly3 (J.F4 ++ J.F5) x y 0 +
        poly3 (J.V4y ω) x y 0 * poly3 (J.G4 ++ J.G5) x y 0 +
        poly3 (J.V5x ω) x y 0 * poly3 (J.F3 ++ J.F4 ++ J.F5) x y 0 +
        poly3 (J.V5y ω) x y 0 * poly3 (J.G3 ++ J.G4 ++ J.G5) x y 0 +
        poly3 (J.V6x ω) x y 0 * poly3 J.F x y 0 + poly3 (J.V6y ω) x y 0 * poly3 J.G x y 0 := by
  rw [dpoly3_W]
  simp only [Wx, Wy, F, G, poly3_append, poly3_cons, poly3_nil, pow_one, pow_zero, mul_one]
  linear_combination J.deg3 ω hω x y + J.deg4 ω hω x y + J.deg5_residual ω x y +
    J.deg5_solve ω hω x y + J.deg6_residual ω x y + J.deg6_solve ω hω x y

end Jet5

/-! ## The planar weak focus of order five -/

section Focus5

open Set Filter Topology Metric Asymptotics

variable {L : State 2 →L[ℝ] State 2} {ω : ℝ} {J : Jet5}

/-- The Lyapunov polynomial `W = x² + y² + V₃ + … + V₆` of a quintic jet in the rotation
coordinates of `L`. -/
def lyap5 (L : State 2 →L[ℝ] State 2) (ω : ℝ) (J : Jet5) (u : State 2) : ℝ :=
  poly3 (J.W ω) (frameX u) (frameY L ω u) ((0 : State 2 →L[ℝ] ℝ) u)

@[tmio T, powerlib_foundation] theorem contDiff_lyap5 : ContDiff ℝ 1 (lyap5 L ω J) :=
  contDiff_poly3 _ _ _ _

@[tmio T, powerlib_foundation] theorem lyap5_zero : lyap5 L ω J 0 = 0 := by
  simp [lyap5, Jet5.W, Jet.V3, Jet.V4, Jet5.V5, Jet5.V6]

/-- The derivative of `lyap5`: `dW(u) v = W_x · frameX v + W_y · frameY v`. -/
@[tmio T, powerlib_foundation] theorem fderiv_lyap5 (u v : State 2) :
    fderiv ℝ (lyap5 L ω J) u v =
      poly3 (J.Wx ω) (frameX u) (frameY L ω u) 0 * frameX v +
        poly3 (J.Wy ω) (frameX u) (frameY L ω u) 0 * frameY L ω v := by
  unfold lyap5
  rw [fderiv_poly3_apply, zero_apply, zero_apply, Jet5.dpoly3_W]

/-- `W − (x² + y²) = O(‖u‖³)`. -/
@[tmio T, powerlib_foundation] theorem lyap5_sub_isBigO :
    (fun u => lyap5 L ω J u - (frameX u ^ 2 + frameY L ω u ^ 2)) =O[𝓝 0] fun u => ‖u‖ ^ 3 := by
  refine (isBigO_poly3_weight (c := fun _ => 0) tendsto_norm_zero
    (frameX.isBigO_id _).norm_right ((frameY L ω).isBigO_id _).norm_right (isBigO_zero _ _)
    (J.V3 ω ++ J.V4 ω ++ J.V5 ω ++ J.V6 ω) (k := 3)
    (by simp [Jet.V3, Jet.V4, Jet5.V5, Jet5.V6])).congr_left fun u => ?_
  simp only [lyap5, Jet5.W, zero_apply, List.cons_append, List.nil_append, poly3_cons,
    List.append_assoc]
  ring

/-- **The Lie derivative at a weak focus of order five.** Along a field whose rotation
coordinates have the quintic expansion of `J` (`ẋ = −ωy + F + o(‖u‖⁵)`, `ẏ = ωx + G + o(‖u‖⁵)`),
`V̇ − ω l₁ (x² + y²)² − K₆ (x² + y²)³ = o(‖u‖⁶)`. -/
@[tmio T, powerlib_foundation] theorem lie5_sub_isLittleO (hω : ω ≠ 0) {g : State 2 → State 2}
    (hx : (fun u => frameX (g u) - (-ω * frameY L ω u +
      poly3 J.F (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY L ω (g u) - (ω * frameX u +
      poly3 J.G (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5) :
    (fun u => fderiv ℝ (lyap5 L ω J) u (g u) -
        ω * J.l1 ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2 -
        J.k6 ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 3) =o[𝓝 0] fun u => ‖u‖ ^ 6 := by
  have pO : ∀ (l : List (ℝ × ℕ × ℕ × ℕ)) {k : ℕ},
      (∀ t ∈ l, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) →
      (fun u : State 2 => poly3 l (frameX u) (frameY L ω u) 0) =O[𝓝 0] fun u => ‖u‖ ^ k :=
    fun l k hl => isBigO_poly3_weight (c := fun _ => 0) tendsto_norm_zero
      (frameX.isBigO_id _).norm_right ((frameY L ω).isBigO_id _).norm_right (isBigO_zero _ _)
      l hl
  have p7 : ∀ {l₁ l₂ : List (ℝ × ℕ × ℕ × ℕ)} {i j : ℕ},
      (∀ t ∈ l₁, i ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) →
      (∀ t ∈ l₂, j ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) → i + j = 7 →
      (fun u : State 2 => poly3 l₁ (frameX u) (frameY L ω u) 0 *
        poly3 l₂ (frameX u) (frameY L ω u) 0) =O[𝓝 0] fun u => ‖u‖ ^ 7 :=
    fun h₁ h₂ hij => ((pO _ h₁).mul (pO _ h₂)).congr_right fun u => by rw [← pow_add, hij]
  have key : ∀ u, fderiv ℝ (lyap5 L ω J) u (g u) -
      ω * J.l1 ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2 -
      J.k6 ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 3 =
      (poly3 (J.V3x ω) (frameX u) (frameY L ω u) 0 * poly3 J.F5 (frameX u) (frameY L ω u) 0 +
        poly3 (J.V3y ω) (frameX u) (frameY L ω u) 0 * poly3 J.G5 (frameX u) (frameY L ω u) 0 +
        poly3 (J.V4x ω) (frameX u) (frameY L ω u) 0 *
          poly3 (J.F4 ++ J.F5) (frameX u) (frameY L ω u) 0 +
        poly3 (J.V4y ω) (frameX u) (frameY L ω u) 0 *
          poly3 (J.G4 ++ J.G5) (frameX u) (frameY L ω u) 0 +
        poly3 (J.V5x ω) (frameX u) (frameY L ω u) 0 *
          poly3 (J.F3 ++ J.F4 ++ J.F5) (frameX u) (frameY L ω u) 0 +
        poly3 (J.V5y ω) (frameX u) (frameY L ω u) 0 *
          poly3 (J.G3 ++ J.G4 ++ J.G5) (frameX u) (frameY L ω u) 0 +
        poly3 (J.V6x ω) (frameX u) (frameY L ω u) 0 * poly3 J.F (frameX u) (frameY L ω u) 0 +
        poly3 (J.V6y ω) (frameX u) (frameY L ω u) 0 * poly3 J.G (frameX u) (frameY L ω u) 0) +
      (poly3 (J.Wx ω) (frameX u) (frameY L ω u) 0 * (frameX (g u) - (-ω * frameY L ω u +
          poly3 J.F (frameX u) (frameY L ω u) 0)) +
        poly3 (J.Wy ω) (frameX u) (frameY L ω u) 0 * (frameY L ω (g u) - (ω * frameX u +
          poly3 J.G (frameX u) (frameY L ω u) 0))) := by
    intro u
    have hid := J.lie_identity ω hω (frameX u) (frameY L ω u)
    rw [Jet5.dpoly3_W] at hid
    rw [fderiv_lyap5]
    linear_combination hid
  have hR := (((((((p7 (l₁ := J.V3x ω) (l₂ := J.F5) (i := 2) (j := 5) (by simp [Jet.V3x])
    (by simp [Jet5.F5]) rfl).add (p7 (l₁ := J.V3y ω) (l₂ := J.G5) (i := 2) (j := 5)
      (by simp [Jet.V3y]) (by simp [Jet5.G5]) rfl)).add
    (p7 (l₁ := J.V4x ω) (l₂ := J.F4 ++ J.F5) (i := 3) (j := 4) (by simp [Jet.V4x])
      (by simp [Jet5.F4, Jet5.F5]) rfl)).add
    (p7 (l₁ := J.V4y ω) (l₂ := J.G4 ++ J.G5) (i := 3) (j := 4) (by simp [Jet.V4y])
      (by simp [Jet5.G4, Jet5.G5]) rfl)).add
    (p7 (l₁ := J.V5x ω) (l₂ := J.F3 ++ J.F4 ++ J.F5) (i := 4) (j := 3) (by simp [Jet5.V5x])
      (by simp [Jet.F3, Jet5.F4, Jet5.F5]) rfl)).add
    (p7 (l₁ := J.V5y ω) (l₂ := J.G3 ++ J.G4 ++ J.G5) (i := 4) (j := 3) (by simp [Jet5.V5y])
      (by simp [Jet.G3, Jet5.G4, Jet5.G5]) rfl)).add
    (p7 (l₁ := J.V6x ω) (l₂ := J.F) (i := 5) (j := 2) (by simp [Jet5.V6x])
      (by simp [Jet5.F, Jet.F2, Jet.F3, Jet5.F4, Jet5.F5]) rfl)).add
    (p7 (l₁ := J.V6y ω) (l₂ := J.G) (i := 5) (j := 2) (by simp [Jet5.V6y])
      (by simp [Jet5.G, Jet.G2, Jet.G3, Jet5.G4, Jet5.G5]) rfl)
  have hT := (((pO (J.Wx ω) (k := 1)
    (by simp [Jet5.Wx, Jet.V3x, Jet.V4x, Jet5.V5x, Jet5.V6x])).mul_isLittleO hx).add
    ((pO (J.Wy ω) (k := 1)
      (by simp [Jet5.Wy, Jet.V3y, Jet.V4y, Jet5.V5y, Jet5.V6y])).mul_isLittleO hy)).congr_right
    fun u => by rw [← pow_add]
  exact ((hR.trans_isLittleO (Dynamics.isLittleO_pow_of_tendsto tendsto_norm_zero
    (by norm_num : 6 < 7))).add hT).congr_left fun u => (key u).symm

/-- Positivity of `x² + y²` and of `W` near the centre, and, at `l₁ = 0`, the Lie-derivative
asymptotics `V̇ − K₆ (x² + y²)³ = o((x² + y²)³)`. -/
@[tmio T, powerlib_foundation] private theorem focus5_core (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2}
    (hx : (fun u => frameX (g u) - (-ω * frameY L ω u +
      poly3 J.F (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY L ω (g u) - (ω * frameX u +
      poly3 J.G (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) :
    (∀ᶠ u in 𝓝[≠] (0 : State 2), 0 < frameX u ^ 2 + frameY L ω u ^ 2) ∧
    (∀ᶠ u in 𝓝[≠] (0 : State 2), 0 < lyap5 L ω J u) ∧
    (fun u => fderiv ℝ (lyap5 L ω J) u (g u) -
        J.k6 ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 3) =o[𝓝 0]
      fun u => (frameX u ^ 2 + frameY L ω u ^ 2) ^ 3 := by
  set M := ‖frameVec0 L‖ ^ 2 + ‖frameVec1 L ω‖ ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hN : ∀ᶠ u in 𝓝[≠] (0 : State 2), 0 < frameX u ^ 2 + frameY L ω u ^ 2 := by
    refine eventually_nhdsWithin_of_forall fun u hu => ?_
    refine lt_of_le_of_ne (by positivity) fun h => hu ?_
    have := norm_sq_le hω hL u
    rw [← h, mul_zero] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))
  have hs2 : (fun u : State 2 => ‖u‖ ^ 2) =O[𝓝 0] fun u => frameX u ^ 2 + frameY L ω u ^ 2 := by
    refine IsBigO.of_bound M (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    exact norm_sq_le hω hL u
  have hs6 : (fun u : State 2 => ‖u‖ ^ 6) =O[𝓝 0]
      fun u => (frameX u ^ 2 + frameY L ω u ^ 2) ^ 3 := by
    refine IsBigO.of_bound (M ^ 3) (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    calc ‖u‖ ^ 6 = (‖u‖ ^ 2) ^ 3 := by ring
      _ ≤ (M * (frameX u ^ 2 + frameY L ω u ^ 2)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (norm_sq_le hω hL u) 3
      _ = _ := by ring
  refine ⟨hN, ?_, ((lie5_sub_isLittleO hω hx hy).trans_isBigO hs6).congr_left fun u => ?_⟩
  · exact Dynamics.eventually_pos_of_isLittleO hN
      ((lyap5_sub_isBigO.trans_isLittleO ((Dynamics.isLittleO_pow_of_tendsto tendsto_norm_zero
        (by norm_num : 2 < 3)).trans_isBigO hs2)).mono nhdsWithin_le_nhds)
  · rw [hl1]; ring

/-- **Supercritical weak focus of order five.** A planar field `g`, continuous near `0`, whose
rotation coordinates (`L² = −ω²`, `ω > 0`) have the quintic expansion of a jet `J`
(`ẋ = −ωy + F + o(‖u‖⁵)`, `ẏ = ωx + G + o(‖u‖⁵)`) with `l₁ = 0` and `l₂ < 0` is locally
asymptotically stable at `0`: `lyap5` is a strict Lyapunov function near `0`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_l2_neg (hω : 0 < ω)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} {U : Set (State 2)}
    (hU : U ∈ 𝓝 0) (hg : ContinuousOn g U)
    (hx : (fun u => frameX (g u) - (-ω * frameY L ω u +
      poly3 J.F (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY L ω (g u) - (ω * frameX u +
      poly3 J.G (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : J.l2 ω < 0) : LocalAsymptoticStable g 0 := by
  obtain ⟨hN, hpos, hlie⟩ := focus5_core hω.ne' hL hx hy hl1
  have hk : J.k6 ω < 0 := by
    have h := hl2
    rw [Jet5.l2, div_neg_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (not_lt.mpr hω.le)
    · linarith
  have hneg : ∀ᶠ u in 𝓝[≠] (0 : State 2), fderiv ℝ (lyap5 L ω J) u (g u) < 0 :=
    Dynamics.eventually_neg_of_isLittleO
      (q := fun u => -J.k6 ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 3)
      (hN.mono fun u hu => mul_pos (neg_pos.mpr hk) (pow_pos hu 3))
      (((hlie.const_mul_right (neg_ne_zero.mpr hk.ne)).mono nhdsWithin_le_nhds).congr_left
        fun u => by ring)
  obtain ⟨r, hr, hball⟩ := Dynamics.exists_radius_of_eventually (hpos.and hneg)
  obtain ⟨σ, hσ, hσU⟩ := Metric.mem_nhds_iff.mp hU
  exact Dynamics.localAsymptoticStable_of_lie_neg two_pos (lt_min hr hσ) contDiff_lyap5
    (hg.mono fun u hu => hσU (Metric.ball_subset_ball (min_le_right _ _) hu)) lyap5_zero
    (fun u hu hne => (hball u (hu.trans_le (min_le_left _ _)) hne).1)
    (fun u hu hne => (hball u (hu.trans_le (min_le_left _ _)) hne).2)

/-- **Subcritical weak focus of order five.** A planar field `g`, Lipschitz near `0`, whose
rotation coordinates have the quintic expansion of a jet `J` with `l₁ = 0` and `l₂ > 0` is
unstable at `0`: Chetaev with `lyap5` (`Dynamics.unstable_of_chetaev_lipschitzOn`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_l2_pos (hω : 0 < ω)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} {U : Set (State 2)}
    {K : NNReal} (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    (hx : (fun u => frameX (g u) - (-ω * frameY L ω u +
      poly3 J.F (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hy : (fun u => frameY L ω (g u) - (ω * frameX u +
      poly3 J.G (frameX u) (frameY L ω u) 0)) =o[𝓝 0] fun u => ‖u‖ ^ 5)
    (hl1 : J.l1 ω = 0) (hl2 : 0 < J.l2 ω) : Unstable g 0 := by
  obtain ⟨hN, hpos, hlie⟩ := focus5_core hω.ne' hL hx hy hl1
  have hk : 0 < J.k6 ω := by
    have h := hl2
    rw [Jet5.l2, div_pos_iff] at h
    rcases h with ⟨h, -⟩ | ⟨-, h⟩
    · linarith
    · exact absurd h (not_lt.mpr hω.le)
  have hgrow : ∀ᶠ u in 𝓝[≠] (0 : State 2), 0 < fderiv ℝ (lyap5 L ω J) u (g u) :=
    Dynamics.eventually_pos_of_isLittleO
      (q := fun u => J.k6 ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 3)
      (hN.mono fun u hu => mul_pos hk (pow_pos hu 3))
      ((hlie.const_mul_right hk.ne').mono nhdsWithin_le_nhds)
  obtain ⟨r, hr, hball⟩ := Dynamics.exists_radius_of_eventually (hpos.and hgrow)
  refine Dynamics.unstable_of_chetaev_lipschitzOn (W := lyap5 L ω J) hU hg contDiff_lyap5
    (half_pos hr) (fun ε hε => ?_) fun u hu hWu => ?_
  · set t := min ε r / 2 with ht
    have htpos : 0 < t := by positivity
    have hnorm : ‖t • e0 - 0‖ = t := by
      rw [sub_zero, norm_smul, e0, PiLp.norm_single, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos htpos]
    have hne : t • e0 ≠ 0 := fun h => by rw [h, sub_zero, norm_zero] at hnorm; linarith
    refine ⟨t • e0, ?_, (hball _ ?_ hne).1⟩
    · rw [hnorm]; linarith [min_le_left ε r]
    · rw [hnorm]; linarith [min_le_right ε r]
  · have hne : u ≠ 0 := fun h => by rw [h, lyap5_zero] at hWu; exact lt_irrefl 0 hWu
    exact (hball u (by linarith) hne).2

end Focus5

/-! ## Agreement with Kuznetsov's formula for `l₂` -/

namespace Jet5

open ComplexConjugate

variable (J : Jet5) (ω : ℝ)

/-- `g₂₀`: the complex Taylor coefficients `g_{kl}` of `ż = ⟨critVec, (ẋ, ẏ)⟩` at
`(x, y) = z critVec + z̄ critVec‾` (`ż = iωz + Σ g_{kl} zᵏ z̄ˡ/(k! l!)`; `critVec` is the
critical vector of the rotation, `PlanarFocus.critVec`). -/
def g20 : ℂ :=
  ⟨(-J.a02 + J.a11 + J.a20 + J.b02 + J.b11 - J.b20) / 2,
    (-J.a02 - J.a11 + J.a20 - J.b02 + J.b11 + J.b20) / 2⟩

/-- `g₁₁`. -/
def g11 : ℂ :=
  ⟨(J.a02 + J.a20 + J.b02 + J.b20) / 2, (-J.a02 - J.a20 + J.b02 + J.b20) / 2⟩

/-- `g₀₂`. -/
def g02 : ℂ :=
  ⟨(J.a02 + J.a11 - J.a20 - J.b02 + J.b11 + J.b20) / 2,
    (J.a02 - J.a11 - J.a20 + J.b02 + J.b11 - J.b20) / 2⟩

/-- `g₃₀`. -/
def g30 : ℂ :=
  ⟨(-3 * J.a03 + 3 * J.a21 + 3 * J.b12 - 3 * J.b30) / 2,
    (-3 * J.a12 + 3 * J.a30 - 3 * J.b03 + 3 * J.b21) / 2⟩

/-- `g₂₁`. -/
def g21 : ℂ :=
  ⟨(J.a12 + 3 * J.a30 + 3 * J.b03 + J.b21) / 2, (-3 * J.a03 - J.a21 + J.b12 + 3 * J.b30) / 2⟩

/-- `g₁₂`. -/
def g12 : ℂ :=
  ⟨(3 * J.a03 + J.a21 + J.b12 + 3 * J.b30) / 2, (-J.a12 - 3 * J.a30 + 3 * J.b03 + J.b21) / 2⟩

/-- `g₀₃`. -/
def g03 : ℂ :=
  ⟨(3 * J.a12 - 3 * J.a30 - 3 * J.b03 + 3 * J.b21) / 2,
    (3 * J.a03 - 3 * J.a21 + 3 * J.b12 - 3 * J.b30) / 2⟩

/-- `g₄₀`. -/
def g40 : ℂ :=
  ⟨-3 * J.a04 - 3 * J.a13 + 3 * J.a22 + 3 * J.a31 - 3 * J.a40 - 3 * J.b04 + 3 * J.b13 +
      3 * J.b22 - 3 * J.b31 - 3 * J.b40,
    3 * J.a04 - 3 * J.a13 - 3 * J.a22 + 3 * J.a31 + 3 * J.a40 - 3 * J.b04 - 3 * J.b13 +
      3 * J.b22 + 3 * J.b31 - 3 * J.b40⟩

/-- `g₃₁`. -/
def g31 : ℂ :=
  ⟨(-6 * J.a04 + 3 * J.a13 + 3 * J.a31 + 6 * J.a40 + 6 * J.b04 + 3 * J.b13 + 3 * J.b31 -
      6 * J.b40) / 2,
    (-6 * J.a04 - 3 * J.a13 - 3 * J.a31 + 6 * J.a40 - 6 * J.b04 + 3 * J.b13 + 3 * J.b31 +
      6 * J.b40) / 2⟩

/-- `g₂₂`. -/
def g22 : ℂ :=
  ⟨3 * J.a04 + J.a22 + 3 * J.a40 + 3 * J.b04 + J.b22 + 3 * J.b40,
    -3 * J.a04 - J.a22 - 3 * J.a40 + 3 * J.b04 + J.b22 + 3 * J.b40⟩

/-- `g₁₃`. -/
def g13 : ℂ :=
  ⟨(6 * J.a04 + 3 * J.a13 + 3 * J.a31 - 6 * J.a40 - 6 * J.b04 + 3 * J.b13 + 3 * J.b31 +
      6 * J.b40) / 2,
    (6 * J.a04 - 3 * J.a13 - 3 * J.a31 - 6 * J.a40 + 6 * J.b04 + 3 * J.b13 + 3 * J.b31 -
      6 * J.b40) / 2⟩

/-- `g₃₂`. -/
def g32 : ℂ :=
  ⟨3 * J.a14 + 3 * J.a32 + 15 * J.a50 + 15 * J.b05 + 3 * J.b23 + 3 * J.b41,
    -15 * J.a05 - 3 * J.a23 - 3 * J.a41 + 3 * J.b14 + 3 * J.b32 + 15 * J.b50⟩

/-- **Kuznetsov's formula for the second Lyapunov coefficient** (Elements, §8.3, the formula
for `l₂(0)` in the complex Taylor coefficients `g_{kl}`), with the real and imaginary parts
distributed over its sums:
`12 l₂ = Re g₃₂/ω + Im[g₂₀ḡ₃₁ − g₁₁(4g₃₁ + 3ḡ₂₂) − g₀₂(g₄₀ + ḡ₁₃)/3 − g₃₀g₁₂]/ω²
  + {Re[g₂₀(ḡ₁₁(3g₁₂ − ḡ₃₀) + g₀₂(ḡ₁₂ − g₃₀/3) + ḡ₀₂g₀₃/3)
    + g₁₁(ḡ₀₂(5ḡ₃₀/3 + 3g₁₂) + g₀₂ḡ₀₃/3 − 4g₁₁g₃₀)] + 3 Im(g₂₀g₁₁) Im g₂₁}/ω³
  + {Im[g₁₁ḡ₀₂(ḡ₂₀² − 3ḡ₂₀g₁₁ − 4g₁₁²)] + Im(g₂₀g₁₁)[3 Re(g₂₀g₁₁) − 2|g₀₂|²]}/ω⁴`. -/
def l2Kuz : ℝ :=
  ((J.g32).re / ω +
    ((J.g20 * conj J.g31).im - 4 * (J.g11 * J.g31).im - 3 * (J.g11 * conj J.g22).im -
      (J.g02 * J.g40).im / 3 - (J.g02 * conj J.g13).im / 3 - (J.g30 * J.g12).im) / ω ^ 2 +
    (3 * (J.g20 * conj J.g11 * J.g12).re - (J.g20 * conj J.g11 * conj J.g30).re +
      (J.g20 * J.g02 * conj J.g12).re - (J.g20 * J.g02 * J.g30).re / 3 +
      (J.g20 * conj J.g02 * J.g03).re / 3 + 5 * (J.g11 * conj J.g02 * conj J.g30).re / 3 +
      3 * (J.g11 * conj J.g02 * J.g12).re + (J.g11 * J.g02 * conj J.g03).re / 3 -
      4 * (J.g11 * J.g11 * J.g30).re + 3 * (J.g20 * J.g11).im * (J.g21).im) / ω ^ 3 +
    ((J.g11 * conj J.g02 * (conj J.g20 * conj J.g20)).im -
      3 * (J.g11 * conj J.g02 * (conj J.g20 * J.g11)).im -
      4 * (J.g11 * conj J.g02 * (J.g11 * J.g11)).im +
      (J.g20 * J.g11).im * (3 * (J.g20 * J.g11).re - 2 * Complex.normSq J.g02)) / ω ^ 4) / 12

/-- The jet of the time-rescaled field (`τ = ωt`): every coefficient divided by `ω`. -/
def nrm (J : Jet5) (ω : ℝ) : Jet5 where
  a20 := J.a20 / ω
  a11 := J.a11 / ω
  a02 := J.a02 / ω
  b20 := J.b20 / ω
  b11 := J.b11 / ω
  b02 := J.b02 / ω
  a30 := J.a30 / ω
  a21 := J.a21 / ω
  a12 := J.a12 / ω
  a03 := J.a03 / ω
  b30 := J.b30 / ω
  b21 := J.b21 / ω
  b12 := J.b12 / ω
  b03 := J.b03 / ω
  a40 := J.a40 / ω
  a31 := J.a31 / ω
  a22 := J.a22 / ω
  a13 := J.a13 / ω
  a04 := J.a04 / ω
  b40 := J.b40 / ω
  b31 := J.b31 / ω
  b22 := J.b22 / ω
  b13 := J.b13 / ω
  b04 := J.b04 / ω
  a50 := J.a50 / ω
  a41 := J.a41 / ω
  a32 := J.a32 / ω
  a23 := J.a23 / ω
  a14 := J.a14 / ω
  a05 := J.a05 / ω
  b50 := J.b50 / ω
  b41 := J.b41 / ω
  b32 := J.b32 / ω
  b23 := J.b23 / ω
  b14 := J.b14 / ω
  b05 := J.b05 / ω

@[tmio T, powerlib_foundation] private theorem c30_nrm (hω : ω ≠ 0) :
    (J.nrm ω).c30 1 = J.c30 ω := by
  simp only [Jet.c30, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem c21_nrm (hω : ω ≠ 0) :
    (J.nrm ω).c21 1 = J.c21 ω := by
  simp only [Jet.c21, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem c12_nrm (hω : ω ≠ 0) :
    (J.nrm ω).c12 1 = J.c12 ω := by
  simp only [Jet.c12, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem c03_nrm (hω : ω ≠ 0) :
    (J.nrm ω).c03 1 = J.c03 ω := by
  simp only [Jet.c03, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem d40_nrm (hω : ω ≠ 0) :
    (J.nrm ω).d40 1 = J.d40 ω := by
  simp only [Jet.d40, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem d31_nrm (hω : ω ≠ 0) :
    (J.nrm ω).d31 1 = J.d31 ω := by
  simp only [Jet.d31, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem d22_nrm (hω : ω ≠ 0) :
    (J.nrm ω).d22 1 = J.d22 ω := by
  simp only [Jet.d22, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem d13_nrm (hω : ω ≠ 0) :
    (J.nrm ω).d13 1 = J.d13 ω := by
  simp only [Jet.d13, nrm]
  field_simp

/-- `l₁` is invariant under the time rescaling. -/
@[tmio T, powerlib_foundation] theorem l1_nrm (hω : ω ≠ 0) :
    (J.nrm ω).l1 1 = J.l1 ω := by
  simp only [Jet.l1, nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r50_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r50 1 = J.r50 ω / ω := by
  simp only [r50]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, d40_nrm J ω hω, d31_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r41_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r41 1 = J.r41 ω / ω := by
  simp only [r41]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, c12_nrm J ω hω, d40_nrm J ω hω, d31_nrm J ω hω,
    d22_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r32_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r32 1 = J.r32 ω / ω := by
  simp only [r32]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, c12_nrm J ω hω, c03_nrm J ω hω, d40_nrm J ω hω,
    d31_nrm J ω hω, d22_nrm J ω hω, d13_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r23_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r23 1 = J.r23 ω / ω := by
  simp only [r23]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, c12_nrm J ω hω, c03_nrm J ω hω, d31_nrm J ω hω,
    d22_nrm J ω hω, d13_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r14_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r14 1 = J.r14 ω / ω := by
  simp only [r14]
  simp only [c21_nrm J ω hω, c12_nrm J ω hω, c03_nrm J ω hω, d22_nrm J ω hω, d13_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r05_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r05 1 = J.r05 ω / ω := by
  simp only [r05]
  simp only [c12_nrm J ω hω, c03_nrm J ω hω, d13_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem e50_nrm (hω : ω ≠ 0) :
    (J.nrm ω).e50 1 = J.e50 ω := by
  simp only [e50]
  simp only [r05_nrm J ω hω, r23_nrm J ω hω, r41_nrm J ω hω]
  field_simp

@[tmio T, powerlib_foundation] private theorem e41_nrm (hω : ω ≠ 0) :
    (J.nrm ω).e41 1 = J.e41 ω := by
  simp only [e41]
  simp only [r50_nrm J ω hω]
  field_simp

@[tmio T, powerlib_foundation] private theorem e32_nrm (hω : ω ≠ 0) :
    (J.nrm ω).e32 1 = J.e32 ω := by
  simp only [e32]
  simp only [r05_nrm J ω hω, r23_nrm J ω hω]
  field_simp

@[tmio T, powerlib_foundation] private theorem e23_nrm (hω : ω ≠ 0) :
    (J.nrm ω).e23 1 = J.e23 ω := by
  simp only [e23]
  simp only [r32_nrm J ω hω, r50_nrm J ω hω]
  field_simp

@[tmio T, powerlib_foundation] private theorem e14_nrm (hω : ω ≠ 0) :
    (J.nrm ω).e14 1 = J.e14 ω := by
  simp only [e14]
  simp only [r05_nrm J ω hω]
  field_simp

@[tmio T, powerlib_foundation] private theorem e05_nrm (hω : ω ≠ 0) :
    (J.nrm ω).e05 1 = J.e05 ω := by
  simp only [e05]
  simp only [r14_nrm J ω hω, r32_nrm J ω hω, r50_nrm J ω hω]
  field_simp

@[tmio T, powerlib_foundation] private theorem r60_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r60 1 = J.r60 ω / ω := by
  simp only [r60]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, d40_nrm J ω hω, d31_nrm J ω hω, e50_nrm J ω hω,
    e41_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r51_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r51 1 = J.r51 ω / ω := by
  simp only [r51]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, c12_nrm J ω hω, d40_nrm J ω hω, d31_nrm J ω hω,
    d22_nrm J ω hω, e50_nrm J ω hω, e41_nrm J ω hω, e32_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r42_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r42 1 = J.r42 ω / ω := by
  simp only [r42]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, c12_nrm J ω hω, c03_nrm J ω hω, d40_nrm J ω hω,
    d31_nrm J ω hω, d22_nrm J ω hω, d13_nrm J ω hω, e50_nrm J ω hω, e41_nrm J ω hω,
    e32_nrm J ω hω, e23_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r33_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r33 1 = J.r33 ω / ω := by
  simp only [r33]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, c12_nrm J ω hω, c03_nrm J ω hω, d40_nrm J ω hω,
    d31_nrm J ω hω, d22_nrm J ω hω, d13_nrm J ω hω, e41_nrm J ω hω, e32_nrm J ω hω,
    e23_nrm J ω hω, e14_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r24_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r24 1 = J.r24 ω / ω := by
  simp only [r24]
  simp only [c30_nrm J ω hω, c21_nrm J ω hω, c12_nrm J ω hω, c03_nrm J ω hω, d31_nrm J ω hω,
    d22_nrm J ω hω, d13_nrm J ω hω, e32_nrm J ω hω, e23_nrm J ω hω, e14_nrm J ω hω,
    e05_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r15_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r15 1 = J.r15 ω / ω := by
  simp only [r15]
  simp only [c21_nrm J ω hω, c12_nrm J ω hω, c03_nrm J ω hω, d22_nrm J ω hω, d13_nrm J ω hω,
    e23_nrm J ω hω, e14_nrm J ω hω, e05_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem r06_nrm (hω : ω ≠ 0) :
    (J.nrm ω).r06 1 = J.r06 ω / ω := by
  simp only [r06]
  simp only [c12_nrm J ω hω, c03_nrm J ω hω, d13_nrm J ω hω, e14_nrm J ω hω, e05_nrm J ω hω]
  simp only [nrm]
  field_simp

@[tmio T, powerlib_foundation] private theorem k6_nrm (hω : ω ≠ 0) :
    (J.nrm ω).k6 1 = J.k6 ω / ω := by
  simp only [k6]
  simp only [r06_nrm J ω hω, r24_nrm J ω hω, r42_nrm J ω hω, r60_nrm J ω hω]
  field_simp

/-- `l₂` is invariant under the time rescaling. -/
@[tmio T, powerlib_foundation] theorem l2_nrm (hω : ω ≠ 0) :
    (J.nrm ω).l2 1 = J.l2 ω := by
  simp only [l2]
  simp only [k6_nrm J ω hω]
  field_simp

@[tmio T, powerlib_foundation] private theorem g_nrm :
    (J.nrm ω).g20 = ((ω⁻¹ : ℝ) : ℂ) * J.g20 ∧ (J.nrm ω).g11 = ((ω⁻¹ : ℝ) : ℂ) * J.g11 ∧
      (J.nrm ω).g02 = ((ω⁻¹ : ℝ) : ℂ) * J.g02 ∧ (J.nrm ω).g30 = ((ω⁻¹ : ℝ) : ℂ) * J.g30 ∧
      (J.nrm ω).g21 = ((ω⁻¹ : ℝ) : ℂ) * J.g21 ∧ (J.nrm ω).g12 = ((ω⁻¹ : ℝ) : ℂ) * J.g12 ∧
      (J.nrm ω).g03 = ((ω⁻¹ : ℝ) : ℂ) * J.g03 ∧ (J.nrm ω).g40 = ((ω⁻¹ : ℝ) : ℂ) * J.g40 ∧
      (J.nrm ω).g31 = ((ω⁻¹ : ℝ) : ℂ) * J.g31 ∧ (J.nrm ω).g22 = ((ω⁻¹ : ℝ) : ℂ) * J.g22 ∧
      (J.nrm ω).g13 = ((ω⁻¹ : ℝ) : ℂ) * J.g13 ∧ (J.nrm ω).g32 = ((ω⁻¹ : ℝ) : ℂ) * J.g32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply Complex.ext <;>
    simp [g20, g11, g02, g30, g21, g12, g03, g40, g31, g22, g13, g32, nrm] <;>
    ring

/-- Kuznetsov's `l₂` is invariant under the time rescaling. -/
@[tmio T, powerlib_foundation] theorem l2Kuz_nrm (hω : ω ≠ 0) :
    (J.nrm ω).l2Kuz 1 = J.l2Kuz ω := by
  obtain ⟨h20, h11, h02, h30, h21, h12, h03, h40, h31, h22, h13, h32⟩ := J.g_nrm ω
  simp only [l2Kuz, h20, h11, h02, h30, h21, h12, h03, h40, h31, h22, h13, h32, map_mul,
    Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  field_simp
  ring

/-- **The two coefficients differ by a multiple of `l₁`** (`ω = 1`):
`l₂ − l2Kuz = −N l₁/12` with an explicit polynomial `N` of the jet. -/
@[tmio T, powerlib_foundation] theorem l2_sub_l2Kuz_one :
    J.l2 1 - J.l2Kuz 1 = -(20 * J.a02 ^ 2 + 116 * J.a02 * J.a20 + 46 * J.a02 * J.b11 -
      15 * J.a03 + 2 * J.a11 ^ 2 + 26 * J.a11 * J.b02 + 22 * J.a11 * J.b20 + 128 * J.a20 ^ 2 +
      98 * J.a20 * J.b11 - 9 * J.a21 + 80 * J.b02 ^ 2 + 68 * J.b02 * J.b20 + 26 * J.b11 ^ 2 -
      15 * J.b12 + 20 * J.b20 ^ 2 - 9 * J.b30) * J.l1 1 / 12 := by
  simp only [l2Kuz, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  simp only [g20, g11, g02, g30, g21, g12, g03, g40, g31, g22, g13, g32]
  simp only [l2, k6, r60, r42, r24, r06]
  simp only [e50, e41, e32, e23, e14, e05]
  simp only [r50, r41, r32, r23, r14, r05]
  simp only [Jet.c30, Jet.c21, Jet.c12, Jet.c03, Jet.d40, Jet.d31, Jet.d22, Jet.d13, Jet.l1]
  ring

/-- **Agreement with Kuznetsov's `l₂`** at a weak focus of the first order (`l₁ = 0`): the
time rescaling `τ = ωt` (`l1_nrm`, `l2_nrm`, `l2Kuz_nrm`) reduces it to `ω = 1`
(`l2_sub_l2Kuz_one`). -/
@[tmio T, powerlib_foundation] theorem l2_eq_l2Kuz (hω : ω ≠ 0) (hl : J.l1 ω = 0) :
    J.l2 ω = J.l2Kuz ω := by
  have h := (J.nrm ω).l2_sub_l2Kuz_one
  rw [l2_nrm J ω hω, l2Kuz_nrm J ω hω, l1_nrm J ω hω, hl, mul_zero, zero_div] at h
  linarith

end Jet5

end powerlib.Dynamics.Degenerate.PlanarFocus
