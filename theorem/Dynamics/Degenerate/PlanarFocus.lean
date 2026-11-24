import theorem.NormalForm.LyapunovCoefficient
import theorem.Dynamics.Instability

/-! # The planar weak focus from a cubic Taylor expansion (foundation)

The first Lyapunov coefficient decides the stability of a planar centre `u̇ = g(u)` when `g` is
known only through its expansion `g(u) = L u + Q(u, u) + C(u, u, u) + o(‖u‖³)` at the
equilibrium `0`: `l₁ < 0` gives local asymptotic stability, `l₁ > 0` instability.

Scope.
* Autonomous continuous-time ODE `u̇ = g u` on `State 2 = EuclideanSpace ℝ (Fin 2)`; no input,
  delay, switching or time variation. Behaviour is LeanForControl's `LocalAsymptoticStable` and
  `Unstable` (finite forward solution segments).
* The data: a linear map `L` with `L (L u) = −ω² u` (on the plane: `tr L = 0`, `det L = ω²`, i.e.
  the eigenvalues `±iω`), `ω > 0`; a continuous bilinear map `Q` and a continuous trilinear map `C`
  (`ContinuousMultilinearMap`, written `C ![u, w, z]`), neither assumed symmetric. Only the
  remainder `g u − (L u + Q u u + C ![u, u, u]) = o(‖u‖³)` is assumed; `g` need not be
  differentiable. Stability needs `g` continuous on a neighbourhood of `0`, instability `g`
  Lipschitz on a neighbourhood of `0`. So the laws apply to a reduced field built from a centre
  manifold that is only Lipschitz with a second-order tangency
  (`theorem/Dynamics/CenterReduction.lean`).
* Nothing here describes a physical system: every statement is a generic identity or
  implication about arbitrary planar data, a foundation result; no model family is defined.
  The sine–Liénard law `Dynamics.Degenerate.localAsymptoticStable_of_sineLienard`
  (`theorem/Dynamics/Degenerate/WeakFocus.lean`) is the special case of an explicit `C¹` normal
  form.

Source: Guckenheimer–Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of
Vector Fields* (1983), §3.4, eq. (3.4.11) (the planar coefficient `a`; here `l₁ = 2a/ω`, the
normalisation `⟨q, q⟩ = 1`); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5
(eq. (3.20)) and §5.4 (the projection formula); Khalil, *Nonlinear Systems* (3rd ed.), Theorems
4.1 and 4.3 (local Lyapunov theorem, Chetaev). The coefficients of the cubic and quartic parts of
the Lyapunov polynomial were computed with SymPy (untrusted) and are checked by the kernel
(`field_simp; ring`).

Results.
* The instability law reads Chetaev's theorem for fields Lipschitz near the point,
  `Dynamics.unstable_of_chetaev_lipschitzOn` (`theorem/Dynamics/Instability.lean`): LeanForControl's
  exponential criterion needs `V̇ ≥ 2αV`, which fails at a weak focus (`V̇ = O(V²)`).
* Rotation coordinates of `L`: `frameX u = u₀`, `frameY L ω u = −(L u)₀/ω`, the dual vectors
  `frameVec0 L = L e₁/(L e₁)₀`, `frameVec1 L ω = −(ω/(L e₁)₀) e₁`; `frame_decomp`
  (`u = x P₀ + y P₁`), `frameX_L`, `frameY_L` (`L` acts as `(x, y) ↦ (−ωy, ωx)`), `norm_sq_le`
  (`‖u‖² ≤ M (x² + y²)`).
* The planar jet: `Jet` (the fourteen quadratic and cubic Taylor coefficients of a field in
  rotation coordinates), `Jet.l1` (the planar formula
  `l₁ = (ω(3a₃₀ + a₁₂ + b₂₁ + 3b₀₃) + a₁₁(a₂₀ + a₀₂) − b₁₁(b₂₀ + b₀₂) − 2a₂₀b₂₀ + 2a₀₂b₀₂)/(4ω²)`),
  `jet L Q C ω` (the jet of `u ↦ Q(u, u) + C(u, u, u)` in the rotation coordinates of `L`) and
  `l1 L Q C ω`; `frameX_cubic`, `frameY_cubic` (the expansion in rotation coordinates).
* The Lyapunov polynomial `Jet.V = x² + y² + V₃ + V₄` (`V₃`, `V₄` solve the homological equations
  of the cubic and quartic orders, with the normalisation `d₀₄ = 0`): `Jet.lie_identity` (along
  the cubic truncation `V̇ = ω l₁ (x² + y²)²` plus products of degree at least five), `lyap`
  (`V` in the coordinates of `L`), `lyap_sub_isBigO`, `lie_sub_isLittleO`
  (`V̇ − ω l₁ (x² + y²)² = o(‖u‖⁴)` along `g`).
* Laws: `localAsymptoticStable_of_l1_neg` (`l₁ < 0`), `unstable_of_l1_pos` (`l₁ > 0`).
* Agreement with Kuznetsov's projection formula `NormalForm.Hopf.lyap1`: `lyap1_rot` (in rotation
  coordinates, with `q = p = ((1 + i)/2, (1 − i)/2)` = `critVec` and the Jacobian `ω J` =
  `rotC ω`, `lyap1 = Jet.l1`), `firstLyapunov_rot` (the same for a field given by its
  derivatives); `frameT`, `frameS` (the rotation coordinates as a linear map and its inverse),
  `critQ`, `critP` (the critical pair of `L`), `firstLyapunov_eq_l1` (a field with `Dg(0) = L`,
  `D²g(0)(u, w) = Q(u, w) + Q(w, u)` and `D³g(0)` the sum of `C` over the six orders of its
  arguments has `NormalForm.LyapunovCoefficient.firstLyapunov g 0 ω critQ critP = l1 L Q C ω`),
  `isCriticalPair_crit`, `crit_spans` (the critical eigenspaces are lines, so the sign does not
  depend on the critical pair), and the laws in Kuznetsov's form for every critical pair:
  `localAsymptoticStable_of_expansion_firstLyapunov_neg`,
  `unstable_of_expansion_firstLyapunov_pos`. `sq_eq_neg_of_trace_det`: a planar matrix with
  trace `0` and determinant `ω²` satisfies the hypothesis on `L`.
-/

noncomputable section


namespace powerlib.Dynamics.Degenerate.PlanarFocus

/-! ## The planar jet and its Lyapunov polynomial -/

/-- The quadratic and cubic Taylor coefficients of a planar field in rotation coordinates:
`ẋ = −ωy + Σ a_{ij} xⁱ yʲ`, `ẏ = ωx + Σ b_{ij} xⁱ yʲ` (`i + j ∈ {2, 3}`). -/
structure Jet where
  /-- Coefficient of `x²` in `ẋ`. -/
  a20 : ℝ
  /-- Coefficient of `xy` in `ẋ`. -/
  a11 : ℝ
  /-- Coefficient of `y²` in `ẋ`. -/
  a02 : ℝ
  /-- Coefficient of `x³` in `ẋ`. -/
  a30 : ℝ
  /-- Coefficient of `x²y` in `ẋ`. -/
  a21 : ℝ
  /-- Coefficient of `xy²` in `ẋ`. -/
  a12 : ℝ
  /-- Coefficient of `y³` in `ẋ`. -/
  a03 : ℝ
  /-- Coefficient of `x²` in `ẏ`. -/
  b20 : ℝ
  /-- Coefficient of `xy` in `ẏ`. -/
  b11 : ℝ
  /-- Coefficient of `y²` in `ẏ`. -/
  b02 : ℝ
  /-- Coefficient of `x³` in `ẏ`. -/
  b30 : ℝ
  /-- Coefficient of `x²y` in `ẏ`. -/
  b21 : ℝ
  /-- Coefficient of `xy²` in `ẏ`. -/
  b12 : ℝ
  /-- Coefficient of `y³` in `ẏ`. -/
  b03 : ℝ

namespace Jet

variable (J : Jet) (ω : ℝ)

/-- The quadratic part of `ẋ`, as a list of monomials `(κ, i, j, 0) ↦ κ xⁱ yʲ`. -/
def F2 : List (ℝ × ℕ × ℕ × ℕ) := [(J.a20, 2, 0, 0), (J.a11, 1, 1, 0), (J.a02, 0, 2, 0)]

/-- The cubic part of `ẋ`. -/
def F3 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.a30, 3, 0, 0), (J.a21, 2, 1, 0), (J.a12, 1, 2, 0), (J.a03, 0, 3, 0)]

/-- The quadratic part of `ẏ`. -/
def G2 : List (ℝ × ℕ × ℕ × ℕ) := [(J.b20, 2, 0, 0), (J.b11, 1, 1, 0), (J.b02, 0, 2, 0)]

/-- The cubic part of `ẏ`. -/
def G3 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.b30, 3, 0, 0), (J.b21, 2, 1, 0), (J.b12, 1, 2, 0), (J.b03, 0, 3, 0)]

/-- **The planar first Lyapunov coefficient** (Guckenheimer–Holmes (3.4.11) `a`, `l₁ = 2a/ω`). -/
def l1 : ℝ :=
  (ω * (3 * J.a30 + J.a12 + J.b21 + 3 * J.b03) + J.a11 * (J.a20 + J.a02) -
    J.b11 * (J.b20 + J.b02) - 2 * J.a20 * J.b20 + 2 * J.a02 * J.b02) / (4 * ω ^ 2)

/-- Coefficient of `x³` in `V₃`. -/
def c30 : ℝ := (2 * J.a11 + 4 * J.b02 + 2 * J.b20) / (3 * ω)
/-- Coefficient of `x²y` in `V₃`. -/
def c21 : ℝ := -2 * J.a20 / ω
/-- Coefficient of `xy²` in `V₃`. -/
def c12 : ℝ := 2 * J.b02 / ω
/-- Coefficient of `y³` in `V₃`. -/
def c03 : ℝ := -(2 * J.a02 + 4 * J.a20 + 2 * J.b11) / (3 * ω)

/-- Coefficient of `x⁴` in `V₄`. -/
def d40 : ℝ := -(2 * J.a02 * J.a20 + J.a02 * J.b11 - J.a03 * ω - J.a11 ^ 2 - 3 * J.a11 * J.b02 -
  J.a11 * J.b20 + 2 * J.a20 ^ 2 + 3 * J.a20 * J.b11 - J.a21 * ω - 2 * J.b02 ^ 2 -
  2 * J.b02 * J.b20 + J.b11 ^ 2 - J.b12 * ω - J.b30 * ω) / (2 * ω ^ 2)
/-- Coefficient of `x³y` in `V₄`. -/
def d31 : ℝ := (J.a02 * J.a11 + 2 * J.a02 * J.b02 - 7 * J.a11 * J.a20 + J.a12 * ω -
  16 * J.a20 * J.b02 - 2 * J.a20 * J.b20 - 5 * J.a30 * ω - J.b02 * J.b11 + 3 * J.b03 * ω -
  J.b11 * J.b20 + J.b21 * ω) / (4 * ω ^ 2)
/-- Coefficient of `x²y²` in `V₄`. -/
def d22 : ℝ := -(2 * J.a02 * J.a20 + J.a02 * J.b11 - J.a03 * ω - J.a11 * J.b02 +
  2 * J.a20 * J.b11 - 2 * J.b02 ^ 2 + J.b11 ^ 2 - J.b12 * ω) / ω ^ 2
/-- Coefficient of `xy³` in `V₄` (the coefficient of `y⁴` is normalised to `0`). -/
def d13 : ℝ := -(J.a02 * J.a11 + 2 * J.a02 * J.b02 + J.a11 * J.a20 + J.a12 * ω +
  16 * J.a20 * J.b02 - 2 * J.a20 * J.b20 + 3 * J.a30 * ω + 7 * J.b02 * J.b11 -
  5 * J.b03 * ω - J.b11 * J.b20 + J.b21 * ω) / (4 * ω ^ 2)

/-- The cubic correction `V₃`. -/
def V3 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.c30 ω, 3, 0, 0), (J.c21 ω, 2, 1, 0), (J.c12 ω, 1, 2, 0), (J.c03 ω, 0, 3, 0)]

/-- The quartic correction `V₄`. -/
def V4 : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.d40 ω, 4, 0, 0), (J.d31 ω, 3, 1, 0), (J.d22 ω, 2, 2, 0), (J.d13 ω, 1, 3, 0)]

/-- The Lyapunov polynomial `V = x² + y² + V₃ + V₄`. -/
def V : List (ℝ × ℕ × ℕ × ℕ) := [(1, 2, 0, 0), (1, 0, 2, 0)] ++ J.V3 ω ++ J.V4 ω

/-- `∂V₃/∂x`. -/
def V3x : List (ℝ × ℕ × ℕ × ℕ) :=
  [(3 * J.c30 ω, 2, 0, 0), (2 * J.c21 ω, 1, 1, 0), (J.c12 ω, 0, 2, 0)]

/-- `∂V₃/∂y`. -/
def V3y : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.c21 ω, 2, 0, 0), (2 * J.c12 ω, 1, 1, 0), (3 * J.c03 ω, 0, 2, 0)]

/-- `∂V₄/∂x`. -/
def V4x : List (ℝ × ℕ × ℕ × ℕ) :=
  [(4 * J.d40 ω, 3, 0, 0), (3 * J.d31 ω, 2, 1, 0), (2 * J.d22 ω, 1, 2, 0), (J.d13 ω, 0, 3, 0)]

/-- `∂V₄/∂y`. -/
def V4y : List (ℝ × ℕ × ℕ × ℕ) :=
  [(J.d31 ω, 3, 0, 0), (2 * J.d22 ω, 2, 1, 0), (3 * J.d13 ω, 1, 2, 0)]

/-- `∂V/∂x`. -/
def Vx : List (ℝ × ℕ × ℕ × ℕ) := [(2, 1, 0, 0)] ++ J.V3x ω ++ J.V4x ω

/-- `∂V/∂y`. -/
def Vy : List (ℝ × ℕ × ℕ × ℕ) := [(2, 0, 1, 0)] ++ J.V3y ω ++ J.V4y ω

/-- The derivative of `V` in the plane: `dV(x, y)(dx, dy) = V_x dx + V_y dy`. -/
@[tmio T, powerlib_foundation] theorem dpoly3_V (x y da db : ℝ) :
    dpoly3 (J.V ω) x y 0 da db 0 = poly3 (J.Vx ω) x y 0 * da + poly3 (J.Vy ω) x y 0 * db := by
  simp [V, V3, V4, Vx, Vy, V3x, V3y, V4x, V4y]
  ring

/-- **The homological identity.** Along the cubic truncation `ẋ = −ωy + F₂ + F₃`,
`ẏ = ωx + G₂ + G₃` the derivative of `V` is `ω l₁ (x² + y²)²` plus four products of degree at
least five. -/
@[tmio T, powerlib_foundation] theorem lie_identity (hω : ω ≠ 0) (x y : ℝ) :
    dpoly3 (J.V ω) x y 0 (-ω * y + poly3 (J.F2 ++ J.F3) x y 0)
        (ω * x + poly3 (J.G2 ++ J.G3) x y 0) 0 - ω * J.l1 ω * (x ^ 2 + y ^ 2) ^ 2 =
      poly3 (J.V3x ω) x y 0 * poly3 J.F3 x y 0 + poly3 (J.V3y ω) x y 0 * poly3 J.G3 x y 0 +
        poly3 (J.V4x ω) x y 0 * poly3 (J.F2 ++ J.F3) x y 0 +
        poly3 (J.V4y ω) x y 0 * poly3 (J.G2 ++ J.G3) x y 0 := by
  rw [dpoly3_V]
  simp [Vx, Vy, V3x, V3y, V4x, V4y, F2, F3, G2, G3, l1, c30, c21, c12, c03, d40, d31, d22, d13]
  field_simp
  ring

end Jet

/-! ## Rotation coordinates of a planar centre -/

section Frame

open Set Filter Topology Metric

variable {L : State 2 →L[ℝ] State 2} {ω : ℝ}

/-- The basis vector `e₀ = (1, 0)`. -/
def e0 : State 2 := EuclideanSpace.single 0 1

/-- The basis vector `e₁ = (0, 1)`. -/
def e1 : State 2 := EuclideanSpace.single 1 1

@[tmio T, simp, powerlib_foundation] theorem e0_apply0 : e0 0 = 1 := by simp [e0]
@[tmio T, simp, powerlib_foundation] theorem e0_apply1 : e0 1 = 0 := by simp [e0]
@[tmio T, simp, powerlib_foundation] theorem e1_apply0 : e1 0 = 0 := by simp [e1]
@[tmio T, simp, powerlib_foundation] theorem e1_apply1 : e1 1 = 1 := by simp [e1]

/-- The first rotation coordinate `x = u₀`. -/
def frameX : State 2 →L[ℝ] ℝ := Dynamics.coord 0

/-- The second rotation coordinate `y = −(L u)₀ / ω`. -/
def frameY (L : State 2 →L[ℝ] State 2) (ω : ℝ) : State 2 →L[ℝ] ℝ :=
  (-ω⁻¹) • (Dynamics.coord 0).comp L

@[tmio T, simp, powerlib_foundation] theorem frameX_apply (u : State 2) : frameX u = u 0 := rfl

@[tmio T, simp, powerlib_foundation] theorem frameY_apply (u : State 2) :
    frameY L ω u = -ω⁻¹ * (L u) 0 := rfl

/-- The first vector of the rotation frame, `P₀ = L e₁ / (L e₁)₀`. -/
def frameVec0 (L : State 2 →L[ℝ] State 2) : State 2 := ((L e1) 0)⁻¹ • L e1

/-- The second vector of the rotation frame, `P₁ = −(ω / (L e₁)₀) e₁`. -/
def frameVec1 (L : State 2 →L[ℝ] State 2) (ω : ℝ) : State 2 := (-(ω / (L e1) 0)) • e1

@[tmio T, powerlib_foundation] theorem state2_eq (u : State 2) : u = u 0 • e0 + u 1 • e1 := by
  ext i; fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem apply_eq (L : State 2 →L[ℝ] State 2) (u : State 2) :
    L u = u 0 • L e0 + u 1 • L e1 := by
  conv_lhs => rw [state2_eq u]
  rw [map_add, map_smul, map_smul]

/-- `L² = −ω²` (`ω ≠ 0`) forces `(L e₁)₀ ≠ 0` and `tr L = 0`. -/
@[tmio T, powerlib_foundation] theorem frame_coeffs (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) : (L e1) 0 ≠ 0 ∧ (L e0) 0 + (L e1) 1 = 0 := by
  have h := hL e1
  rw [apply_eq L (L e1)] at h
  have h0 := congrArg (fun v : State 2 => v 0) h
  have h1 := congrArg (fun v : State 2 => v 1) h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, e1_apply0, e1_apply1, mul_zero,
    mul_one] at h0 h1
  have hc : (L e1) 0 ≠ 0 := by
    intro hc
    rw [hc, zero_mul, zero_add] at h1
    nlinarith [sq_nonneg ((L e1) 1), sq_pos_of_ne_zero hω]
  refine ⟨hc, ?_⟩
  have : (L e1) 0 * ((L e0) 0 + (L e1) 1) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hc
  · exact h'

/-- **Rotation coordinates.** `u = x P₀ + y P₁` with `x = frameX u`, `y = frameY L ω u`. -/
@[tmio T, powerlib_foundation] theorem frame_decomp (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) (u : State 2) :
    u = frameX u • frameVec0 L + frameY L ω u • frameVec1 L ω := by
  obtain ⟨hc, htr⟩ := frame_coeffs hω hL
  have h0 := congrArg (fun v : State 2 => v 0) (apply_eq L u)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0
  ext i
  fin_cases i
  · simp only [frameX_apply, frameY_apply, frameVec0, frameVec1, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, e1_apply0, Fin.zero_eta, Fin.isValue]
    field_simp
    ring
  · simp only [frameX_apply, frameY_apply, frameVec0, frameVec1, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, e1_apply1, Fin.mk_one, Fin.isValue, h0]
    field_simp
    linear_combination (-(u 0)) * htr

/-- In rotation coordinates `L` acts as `(x, y) ↦ (−ωy, ωx)`: the first coordinate. -/
@[tmio T, powerlib_foundation] theorem frameX_L (hω : ω ≠ 0) (u : State 2) :
    frameX (L u) = -ω * frameY L ω u := by
  simp only [frameX_apply, frameY_apply]
  field_simp

/-- In rotation coordinates `L` acts as `(x, y) ↦ (−ωy, ωx)`: the second coordinate. -/
@[tmio T, powerlib_foundation] theorem frameY_L (hω : ω ≠ 0) (hL : ∀ u, L (L u) = -(ω ^ 2) • u)
    (u : State 2) : frameY L ω (L u) = ω * frameX u := by
  simp only [frameX_apply, frameY_apply, hL, PiLp.smul_apply, smul_eq_mul]
  field_simp

/-- A planar matrix with trace `0` and determinant `ω²` squares to `−ω²`. -/
@[tmio T, powerlib_foundation] theorem sq_eq_neg_of_trace_det {a b c d : ℝ} (htr : a + d = 0)
    (hdet : a * d - b * c = ω ^ 2) (u : State 2) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![a, b; c, d]
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![a, b; c, d] u) = -(ω ^ 2) • u := by
  have hd : d = -a := by linarith
  subst hd
  ext i
  fin_cases i
  · simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two]
    linear_combination (-(u 0)) * hdet
  · simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two]
    linear_combination (-(u 1)) * hdet

end Frame

/-! ## The planar weak focus -/

section Focus

open Set Filter Topology Metric Asymptotics

variable (L : State 2 →L[ℝ] State 2) (Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2)
  (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)) (ω : ℝ)

/-- The Taylor coefficients of `u ↦ Q(u, u) + C(u, u, u)` in the rotation coordinates of `L`:
`a_{ij}`, `b_{ij}` are the `frameX`, `frameY` components of the sum of `Q`, `C` over the
arrangements of `i` copies of `P₀` and `j` copies of `P₁`. -/
def jet : Jet where
  a20 := frameX (Q (frameVec0 L) (frameVec0 L))
  a11 := frameX (Q (frameVec0 L) (frameVec1 L ω) + Q (frameVec1 L ω) (frameVec0 L))
  a02 := frameX (Q (frameVec1 L ω) (frameVec1 L ω))
  a30 := frameX (C ![frameVec0 L, frameVec0 L, frameVec0 L])
  a21 := frameX (C ![frameVec0 L, frameVec0 L, frameVec1 L ω] +
    C ![frameVec0 L, frameVec1 L ω, frameVec0 L] + C ![frameVec1 L ω, frameVec0 L, frameVec0 L])
  a12 := frameX (C ![frameVec0 L, frameVec1 L ω, frameVec1 L ω] +
    C ![frameVec1 L ω, frameVec0 L, frameVec1 L ω] +
    C ![frameVec1 L ω, frameVec1 L ω, frameVec0 L])
  a03 := frameX (C ![frameVec1 L ω, frameVec1 L ω, frameVec1 L ω])
  b20 := frameY L ω (Q (frameVec0 L) (frameVec0 L))
  b11 := frameY L ω (Q (frameVec0 L) (frameVec1 L ω) + Q (frameVec1 L ω) (frameVec0 L))
  b02 := frameY L ω (Q (frameVec1 L ω) (frameVec1 L ω))
  b30 := frameY L ω (C ![frameVec0 L, frameVec0 L, frameVec0 L])
  b21 := frameY L ω (C ![frameVec0 L, frameVec0 L, frameVec1 L ω] +
    C ![frameVec0 L, frameVec1 L ω, frameVec0 L] + C ![frameVec1 L ω, frameVec0 L, frameVec0 L])
  b12 := frameY L ω (C ![frameVec0 L, frameVec1 L ω, frameVec1 L ω] +
    C ![frameVec1 L ω, frameVec0 L, frameVec1 L ω] +
    C ![frameVec1 L ω, frameVec1 L ω, frameVec0 L])
  b03 := frameY L ω (C ![frameVec1 L ω, frameVec1 L ω, frameVec1 L ω])

/-- **The first Lyapunov coefficient** of `u̇ = L u + Q(u, u) + C(u, u, u)`: the planar formula
`Jet.l1` applied to the jet in the rotation coordinates of `L`. -/
def l1 : ℝ := (jet L Q C ω).l1 ω

/-- The Lyapunov polynomial `x² + y² + V₃ + V₄` in the rotation coordinates of `L`. -/
def lyap (u : State 2) : ℝ :=
  poly3 ((jet L Q C ω).V ω) (frameX u) (frameY L ω u) ((0 : State 2 →L[ℝ] ℝ) u)

variable {L Q C ω}

/-- The expansion of `ℓ(Q(u, u) + C(u, u, u))` at `u = a P₀ + b P₁`, for any functional `ℓ`. -/
@[tmio T, powerlib_foundation] theorem functional_cubic (ℓ : State 2 →L[ℝ] ℝ) (P0 P1 : State 2)
    (a b : ℝ) :
    ℓ (Q (a • P0 + b • P1) (a • P0 + b • P1) +
        C ![a • P0 + b • P1, a • P0 + b • P1, a • P0 + b • P1]) =
      ℓ (Q P0 P0) * a ^ 2 + ℓ (Q P0 P1 + Q P1 P0) * (a * b) + ℓ (Q P1 P1) * b ^ 2 +
        ℓ (C ![P0, P0, P0]) * a ^ 3 +
        ℓ (C ![P0, P0, P1] + C ![P0, P1, P0] + C ![P1, P0, P0]) * (a ^ 2 * b) +
        ℓ (C ![P0, P1, P1] + C ![P1, P0, P1] + C ![P1, P1, P0]) * (a * b ^ 2) +
        ℓ (C ![P1, P1, P1]) * b ^ 3 := by
  -- multilinearity of `C` in each of its three slots
  have upd : ∀ (v : Fin 3 → State 2) (k : Fin 3) (x : State 2), Function.update v k x =
      ![if k = 0 then x else v 0, if k = 1 then x else v 1, if k = 2 then x else v 2] := by
    intro v k x; funext i; fin_cases i <;> fin_cases k <;> simp
  have add0 : ∀ x y v w : State 2, C ![x + y, v, w] = C ![x, v, w] + C ![y, v, w] := by
    intro x y v w; simpa [upd] using C.map_update_add ![x, v, w] 0 x y
  have add1 : ∀ x y v w : State 2, C ![v, x + y, w] = C ![v, x, w] + C ![v, y, w] := by
    intro x y v w; simpa [upd] using C.map_update_add ![v, x, w] 1 x y
  have add2 : ∀ x y v w : State 2, C ![v, w, x + y] = C ![v, w, x] + C ![v, w, y] := by
    intro x y v w; simpa [upd] using C.map_update_add ![v, w, x] 2 x y
  have smul0 : ∀ (t : ℝ) (x v w : State 2), C ![t • x, v, w] = t • C ![x, v, w] := by
    intro t x v w; simpa [upd] using C.map_update_smul ![x, v, w] 0 t x
  have smul1 : ∀ (t : ℝ) (x v w : State 2), C ![v, t • x, w] = t • C ![v, x, w] := by
    intro t x v w; simpa [upd] using C.map_update_smul ![v, x, w] 1 t x
  have smul2 : ∀ (t : ℝ) (x v w : State 2), C ![v, w, t • x] = t • C ![v, w, x] := by
    intro t x v w; simpa [upd] using C.map_update_smul ![v, w, x] 2 t x
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, add0, add1, add2, smul0,
    smul1, smul2, smul_eq_mul]
  ring

/-- The first rotation coordinate of `Q(u, u) + C(u, u, u)` is the polynomial `F₂ + F₃` of the
jet. -/
@[tmio T, powerlib_foundation] theorem frameX_cubic (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) (u : State 2) :
    frameX (Q u u + C ![u, u, u]) =
      poly3 ((jet L Q C ω).F2 ++ (jet L Q C ω).F3) (frameX u) (frameY L ω u) 0 := by
  have h := functional_cubic (Q := Q) (C := C) frameX (frameVec0 L) (frameVec1 L ω)
    (frameX u) (frameY L ω u)
  rw [← frame_decomp hω hL u] at h
  rw [h]
  simp only [jet, Jet.F2, Jet.F3, List.cons_append, List.nil_append, poly3_cons, poly3_nil]
  ring

/-- The second rotation coordinate of `Q(u, u) + C(u, u, u)` is the polynomial `G₂ + G₃` of the
jet. -/
@[tmio T, powerlib_foundation] theorem frameY_cubic (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) (u : State 2) :
    frameY L ω (Q u u + C ![u, u, u]) =
      poly3 ((jet L Q C ω).G2 ++ (jet L Q C ω).G3) (frameX u) (frameY L ω u) 0 := by
  have h := functional_cubic (Q := Q) (C := C) (frameY L ω) (frameVec0 L) (frameVec1 L ω)
    (frameX u) (frameY L ω u)
  rw [← frame_decomp hω hL u] at h
  rw [h]
  simp only [jet, Jet.G2, Jet.G3, List.cons_append, List.nil_append, poly3_cons, poly3_nil]
  ring

/-- The rotation coordinates control the norm: `‖u‖² ≤ (‖P₀‖² + ‖P₁‖²)(x² + y²)`. -/
@[tmio T, powerlib_foundation] theorem norm_sq_le (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) (u : State 2) :
    ‖u‖ ^ 2 ≤ (‖frameVec0 L‖ ^ 2 + ‖frameVec1 L ω‖ ^ 2) * (frameX u ^ 2 + frameY L ω u ^ 2) := by
  set x := frameX u
  set y := frameY L ω u
  have hn : ‖u‖ ≤ |x| * ‖frameVec0 L‖ + |y| * ‖frameVec1 L ω‖ := by
    calc ‖u‖ = ‖x • frameVec0 L + y • frameVec1 L ω‖ := by rw [← frame_decomp hω hL u]
      _ ≤ ‖x • frameVec0 L‖ + ‖y • frameVec1 L ω‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ‖u‖ ^ 2 ≤ (|x| * ‖frameVec0 L‖ + |y| * ‖frameVec1 L ω‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg u) hn 2
  nlinarith [sq_nonneg (|x| * ‖frameVec1 L ω‖ - |y| * ‖frameVec0 L‖), sq_abs x, sq_abs y]

@[tmio T, powerlib_foundation] private theorem poly_isBigO (L : State 2 →L[ℝ] State 2) (ω : ℝ)
    (l : List (ℝ × ℕ × ℕ × ℕ)) {k : ℕ} (hl : ∀ t ∈ l, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) :
    (fun u : State 2 => poly3 l (frameX u) (frameY L ω u) 0) =O[𝓝 0] fun u => ‖u‖ ^ k :=
  isBigO_poly3_weight (c := fun _ => 0) tendsto_norm_zero
    (frameX.isBigO_id _).norm_right ((frameY L ω).isBigO_id _).norm_right (isBigO_zero _ _) l hl

@[tmio T, powerlib_foundation] theorem contDiff_lyap : ContDiff ℝ 1 (lyap L Q C ω) :=
  contDiff_poly3 _ _ _ _

@[tmio T, powerlib_foundation] theorem lyap_zero : lyap L Q C ω 0 = 0 := by
  simp [lyap, Jet.V, Jet.V3, Jet.V4]

/-- The derivative of the Lyapunov polynomial: `dV(u) v = V_x · frameX v + V_y · frameY v`. -/
@[tmio T, powerlib_foundation] theorem fderiv_lyap (u v : State 2) :
    fderiv ℝ (lyap L Q C ω) u v =
      poly3 ((jet L Q C ω).Vx ω) (frameX u) (frameY L ω u) 0 * frameX v +
        poly3 ((jet L Q C ω).Vy ω) (frameX u) (frameY L ω u) 0 * frameY L ω v := by
  unfold lyap
  rw [fderiv_poly3_apply, zero_apply, zero_apply, Jet.dpoly3_V]

/-- `V − (x² + y²) = O(‖u‖³)`. -/
@[tmio T, powerlib_foundation] theorem lyap_sub_isBigO :
    (fun u => lyap L Q C ω u - (frameX u ^ 2 + frameY L ω u ^ 2)) =O[𝓝 0] fun u => ‖u‖ ^ 3 := by
  refine (poly_isBigO L ω ((jet L Q C ω).V3 ω ++ (jet L Q C ω).V4 ω) (k := 3)
    (by simp [Jet.V3, Jet.V4])).congr_left fun u => ?_
  simp only [lyap, Jet.V, zero_apply, List.cons_append, List.nil_append, poly3_cons]
  ring

/-- **The Lie derivative at a weak focus.** Along a field with the cubic expansion,
`V̇ − ω l₁ (x² + y²)² = o(‖u‖⁴)`. -/
@[tmio T, powerlib_foundation] theorem lie_sub_isLittleO (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2}
    (hexp : (fun u => g u - (L u + Q u u + C ![u, u, u])) =o[𝓝 0] fun u => ‖u‖ ^ 3) :
    (fun u => fderiv ℝ (lyap L Q C ω) u (g u) -
        ω * l1 L Q C ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2) =o[𝓝 0] fun u => ‖u‖ ^ 4 := by
  set J := jet L Q C ω with hJ
  set r : State 2 → State 2 := fun u => g u - (L u + Q u u + C ![u, u, u]) with hr
  have hgu : ∀ u, g u = L u + (Q u u + C ![u, u, u]) + r u := fun u => by
    simp only [hr]; abel
  have key : ∀ u, fderiv ℝ (lyap L Q C ω) u (g u) -
      ω * l1 L Q C ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2 =
      (poly3 (J.V3x ω) (frameX u) (frameY L ω u) 0 * poly3 J.F3 (frameX u) (frameY L ω u) 0 +
        poly3 (J.V3y ω) (frameX u) (frameY L ω u) 0 * poly3 J.G3 (frameX u) (frameY L ω u) 0 +
        poly3 (J.V4x ω) (frameX u) (frameY L ω u) 0 *
          poly3 (J.F2 ++ J.F3) (frameX u) (frameY L ω u) 0 +
        poly3 (J.V4y ω) (frameX u) (frameY L ω u) 0 *
          poly3 (J.G2 ++ J.G3) (frameX u) (frameY L ω u) 0) +
      (poly3 (J.Vx ω) (frameX u) (frameY L ω u) 0 * frameX (r u) +
        poly3 (J.Vy ω) (frameX u) (frameY L ω u) 0 * frameY L ω (r u)) := by
    intro u
    have hid := J.lie_identity ω hω (frameX u) (frameY L ω u)
    rw [Jet.dpoly3_V] at hid
    have hx : frameX (g u) = -ω * frameY L ω u +
        poly3 (J.F2 ++ J.F3) (frameX u) (frameY L ω u) 0 + frameX (r u) := by
      rw [hgu u, frameX.map_add, frameX.map_add, frameX_L hω, frameX_cubic hω hL]
    have hy : frameY L ω (g u) = ω * frameX u +
        poly3 (J.G2 ++ J.G3) (frameX u) (frameY L ω u) 0 + frameY L ω (r u) := by
      rw [hgu u, (frameY L ω).map_add, (frameY L ω).map_add, frameY_L hω hL,
        frameY_cubic hω hL]
    rw [fderiv_lyap, hx, hy]
    unfold l1
    linear_combination hid
  -- the four products of degree five
  have p5 : ∀ {l₁ l₂ : List (ℝ × ℕ × ℕ × ℕ)} {i j : ℕ},
      (∀ t ∈ l₁, i ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) →
      (∀ t ∈ l₂, j ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) → i + j = 5 →
      (fun u : State 2 => poly3 l₁ (frameX u) (frameY L ω u) 0 *
        poly3 l₂ (frameX u) (frameY L ω u) 0) =O[𝓝 0] fun u => ‖u‖ ^ 5 :=
    fun h₁ h₂ hij => ((poly_isBigO L ω _ h₁).mul (poly_isBigO L ω _ h₂)).congr_right
      fun u => by rw [← pow_add, hij]
  have hR := (((p5 (l₁ := J.V3x ω) (l₂ := J.F3) (i := 2) (j := 3) (by simp [Jet.V3x])
    (by simp [Jet.F3]) rfl).add (p5 (l₁ := J.V3y ω) (l₂ := J.G3) (i := 2) (j := 3)
      (by simp [Jet.V3y]) (by simp [Jet.G3]) rfl)).add
    (p5 (l₁ := J.V4x ω) (l₂ := J.F2 ++ J.F3) (i := 3) (j := 2) (by simp [Jet.V4x])
      (by simp [Jet.F2, Jet.F3]) rfl)).add
    (p5 (l₁ := J.V4y ω) (l₂ := J.G2 ++ J.G3) (i := 3) (j := 2) (by simp [Jet.V4y])
      (by simp [Jet.G2, Jet.G3]) rfl)
  -- the remainder of the field against the gradient
  have hrx : (fun u => frameX (r u)) =o[𝓝 0] fun u => ‖u‖ ^ 3 :=
    (frameX.isBigO_comp r _).trans_isLittleO hexp
  have hry : (fun u => frameY L ω (r u)) =o[𝓝 0] fun u => ‖u‖ ^ 3 :=
    ((frameY L ω).isBigO_comp r _).trans_isLittleO hexp
  have hT := (((poly_isBigO L ω (J.Vx ω) (k := 1)
    (by simp [Jet.Vx, Jet.V3x, Jet.V4x])).mul_isLittleO hrx).add
    ((poly_isBigO L ω (J.Vy ω) (k := 1)
      (by simp [Jet.Vy, Jet.V3y, Jet.V4y])).mul_isLittleO hry)).congr_right
    fun u => by rw [← pow_add]
  exact ((hR.trans_isLittleO (Dynamics.isLittleO_pow_of_tendsto tendsto_norm_zero
    (by norm_num : 4 < 5))).add hT).congr_left fun u => (key u).symm

/-- Positivity of `x² + y²` and of `V` near the centre, and the Lie-derivative asymptotics
relative to `(x² + y²)²`. -/
@[tmio T, powerlib_foundation] private theorem focus_core (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2}
    (hexp : (fun u => g u - (L u + Q u u + C ![u, u, u])) =o[𝓝 0] fun u => ‖u‖ ^ 3) :
    (∀ᶠ u in 𝓝[≠] (0 : State 2), 0 < frameX u ^ 2 + frameY L ω u ^ 2) ∧
    (∀ᶠ u in 𝓝[≠] (0 : State 2), 0 < lyap L Q C ω u) ∧
    (fun u => fderiv ℝ (lyap L Q C ω) u (g u) -
        ω * l1 L Q C ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2) =o[𝓝 0]
      fun u => (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2 := by
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
  have hs4 : (fun u : State 2 => ‖u‖ ^ 4) =O[𝓝 0]
      fun u => (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2 := by
    refine IsBigO.of_bound (M ^ 2) (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    calc ‖u‖ ^ 4 = (‖u‖ ^ 2) ^ 2 := by ring
      _ ≤ (M * (frameX u ^ 2 + frameY L ω u ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (norm_sq_le hω hL u) 2
      _ = _ := by ring
  refine ⟨hN, ?_, (lie_sub_isLittleO hω hL hexp).trans_isBigO hs4⟩
  exact Dynamics.eventually_pos_of_isLittleO hN
    ((lyap_sub_isBigO.trans_isLittleO ((Dynamics.isLittleO_pow_of_tendsto tendsto_norm_zero
      (by norm_num : 2 < 3)).trans_isBigO hs2)).mono nhdsWithin_le_nhds)

/-- **Supercritical planar weak focus.** A planar field `g`, continuous near `0`, with
`g(u) = L u + Q(u, u) + C(u, u, u) + o(‖u‖³)`, `L² = −ω²`, `ω > 0`, and `l₁ < 0` is locally
asymptotically stable at `0`: `lyap` is a strict Lyapunov function near `0`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_l1_neg (hω : 0 < ω)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} {U : Set (State 2)}
    (hU : U ∈ 𝓝 0) (hg : ContinuousOn g U)
    (hexp : (fun u => g u - (L u + Q u u + C ![u, u, u])) =o[𝓝 0] fun u => ‖u‖ ^ 3)
    (hl : l1 L Q C ω < 0) : LocalAsymptoticStable g 0 := by
  obtain ⟨hN, hpos, hlie⟩ := focus_core hω.ne' hL hexp
  have hc : 0 < -(ω * l1 L Q C ω) := by nlinarith
  have hneg : ∀ᶠ u in 𝓝[≠] (0 : State 2), fderiv ℝ (lyap L Q C ω) u (g u) < 0 :=
    Dynamics.eventually_neg_of_isLittleO
      (q := fun u => -(ω * l1 L Q C ω) * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2)
      (hN.mono fun u hu => by positivity)
      (((hlie.const_mul_right hc.ne').mono nhdsWithin_le_nhds).congr_left fun u => by ring)
  obtain ⟨r, hr, hball⟩ := Dynamics.exists_radius_of_eventually (hpos.and hneg)
  obtain ⟨σ, hσ, hσU⟩ := Metric.mem_nhds_iff.mp hU
  exact Dynamics.localAsymptoticStable_of_lie_neg two_pos (lt_min hr hσ) contDiff_lyap
    (hg.mono fun u hu => hσU (Metric.ball_subset_ball (min_le_right _ _) hu)) lyap_zero
    (fun u hu hne => (hball u (hu.trans_le (min_le_left _ _)) hne).1)
    (fun u hu hne => (hball u (hu.trans_le (min_le_left _ _)) hne).2)

/-- **Subcritical planar weak focus.** A planar field `g`, Lipschitz near `0`, with
`g(u) = L u + Q(u, u) + C(u, u, u) + o(‖u‖³)`, `L² = −ω²`, `ω > 0`, and `l₁ > 0` is unstable at
`0`: Chetaev with `lyap` (`unstable_of_chetaev_lipschitzOn`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_l1_pos (hω : 0 < ω)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} {U : Set (State 2)}
    {K : NNReal} (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    (hexp : (fun u => g u - (L u + Q u u + C ![u, u, u])) =o[𝓝 0] fun u => ‖u‖ ^ 3)
    (hl : 0 < l1 L Q C ω) : Unstable g 0 := by
  obtain ⟨hN, hpos, hlie⟩ := focus_core hω.ne' hL hexp
  have hc : 0 < ω * l1 L Q C ω := mul_pos hω hl
  have hgrow : ∀ᶠ u in 𝓝[≠] (0 : State 2), 0 < fderiv ℝ (lyap L Q C ω) u (g u) :=
    Dynamics.eventually_pos_of_isLittleO
      (q := fun u => ω * l1 L Q C ω * (frameX u ^ 2 + frameY L ω u ^ 2) ^ 2)
      (hN.mono fun u hu => by positivity)
      ((hlie.const_mul_right hc.ne').mono nhdsWithin_le_nhds)
  obtain ⟨r, hr, hball⟩ := Dynamics.exists_radius_of_eventually (hpos.and hgrow)
  refine Dynamics.unstable_of_chetaev_lipschitzOn (W := lyap L Q C ω) hU hg contDiff_lyap
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
  · have hne : u ≠ 0 := fun h => by rw [h, lyap_zero] at hWu; exact lt_irrefl 0 hWu
    exact (hball u (by linarith) hne).2

end Focus

/-! ## Agreement with Kuznetsov's projection formula -/

section Agreement

open Filter Topology Asymptotics Complex Matrix NormalForm.LyapunovCoefficient

variable {ω : ℝ}

/-- The normalized critical vector `q = ((1 + i)/2, (1 − i)/2)` of the rotation `ω J`
(`⟨q, q⟩ = 1`, Kuznetsov's normalisation). -/
def critVec : Fin 2 → ℂ := ![(1 + I) / 2, (1 - I) / 2]

/-- The complexified rotation generator `ω J`, `J (x, y) = (−y, x)`. -/
def rotC (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, -(ω : ℂ); (ω : ℂ), 0]

@[tmio T, powerlib_foundation] theorem star_critVec :
    star critVec = ![(1 - I) / 2, (1 + I) / 2] := by
  ext i; fin_cases i <;> simp [critVec, Complex.ext_iff]

/-- **Kuznetsov's formula in rotation coordinates.** With the Jacobian `ω J`, the bilinear and
trilinear forms `B`, `C` of the second and third derivatives of the canonical cubic field of a
jet `J`, and `q = p = critVec`, the projection formula `NormalForm.Hopf.lyap1` is the planar
`Jet.l1`. -/
@[tmio T, powerlib_foundation] theorem lyap1_rot (J : Jet) (hω : 0 < ω)
    (B : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (C : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (hB : ∀ u w, B u w = ![2 * J.a20 * u 0 * w 0 + J.a11 * (u 0 * w 1 + u 1 * w 0) +
        2 * J.a02 * u 1 * w 1, 2 * J.b20 * u 0 * w 0 + J.b11 * (u 0 * w 1 + u 1 * w 0) +
        2 * J.b02 * u 1 * w 1])
    (hC : ∀ u w z, C u w z = ![6 * J.a30 * u 0 * w 0 * z 0 +
        2 * J.a21 * (u 0 * w 0 * z 1 + u 0 * w 1 * z 0 + u 1 * w 0 * z 0) +
        2 * J.a12 * (u 0 * w 1 * z 1 + u 1 * w 0 * z 1 + u 1 * w 1 * z 0) +
        6 * J.a03 * u 1 * w 1 * z 1, 6 * J.b30 * u 0 * w 0 * z 0 +
        2 * J.b21 * (u 0 * w 0 * z 1 + u 0 * w 1 * z 0 + u 1 * w 0 * z 0) +
        2 * J.b12 * (u 0 * w 1 * z 1 + u 1 * w 0 * z 1 + u 1 * w 1 * z 0) +
        6 * J.b03 * u 1 * w 1 * z 1]) :
    NormalForm.Hopf.lyap1 B C (rotC ω)⁻¹.mulVecLin (shift2 (rotC ω) ω)⁻¹.mulVecLin
      (pairing critVec) ω critVec (star critVec) = J.l1 ω := by
  have hω0 : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  set r : Fin 2 → ℂ := ![(J.b20 + J.b02 : ℂ) / ω, -(J.a20 + J.a02 : ℂ) / ω] with hr
  set β0 : ℂ := J.a11 + I * (J.a20 - J.a02)
  set β1 : ℂ := J.b11 + I * (J.b20 - J.b02)
  set s : Fin 2 → ℂ := ![(-2 * I * β0 + β1) / (3 * ω), (-2 * I * β1 - β0) / (3 * ω)] with hs
  have hBqq : B critVec (star critVec) = ![(J.a20 + J.a02 : ℂ), (J.b20 + J.b02 : ℂ)] := by
    rw [hB, star_critVec]
    ext i; fin_cases i <;> simp [critVec] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have hBq : B critVec critVec = ![β0, β1] := by
    rw [hB]
    ext i; fin_cases i <;> simp [critVec, β0, β1] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have hdet : (rotC ω).det = (ω : ℂ) ^ 2 := by
    simp [rotC, Matrix.det_fin_two]; ring
  have hdet2 : (shift2 (rotC ω) ω).det = -3 * (ω : ℂ) ^ 2 := by
    simp [shift2, rotC, Matrix.det_fin_two]; ring_nf; simp [Complex.I_sq]; ring
  have hu1 : IsUnit (rotC ω).det := by
    rw [hdet]; exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hω0)
  have hu2 : IsUnit (shift2 (rotC ω) ω).det := by
    rw [hdet2]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 2 hω0))
  -- `A r = B(q, q̄)` and `(2iω − A) s = B(q, q)`
  have hrr : rotC ω *ᵥ r = B critVec (star critVec) := by
    rw [hBqq]
    ext i; fin_cases i <;> simp [rotC, Matrix.mulVec, dotProduct, Fin.sum_univ_two, r]
    · field_simp
      ring
    · field_simp
  have hss : shift2 (rotC ω) ω *ᵥ s = B critVec critVec := by
    rw [hBq]
    ext i; fin_cases i <;>
      simp [shift2, rotC, Matrix.mulVec, dotProduct, Fin.sum_univ_two, s] <;>
      field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have e1 : (rotC ω)⁻¹ *ᵥ B critVec (star critVec) = r := by
    rw [← hrr, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu1, Matrix.one_mulVec]
  have e2 : (shift2 (rotC ω) ω)⁻¹ *ᵥ B critVec critVec = s := by
    rw [← hss, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu2, Matrix.one_mulVec]
  simp only [NormalForm.Hopf.lyap1, Matrix.mulVecLin_apply, e1, e2]
  rw [hC, hB, hB, star_critVec]
  simp [pairing_apply, Fin.sum_univ_two, critVec, r, s, β0, β1, Jet.l1, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]
  field_simp
  ring

/-- The coefficients `∂²f_k/∂x_i∂x_j` of the canonical field of a jet. -/
def Jet.hessCoeff (J : Jet) : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  ![![![2 * J.a20, J.a11], ![J.a11, 2 * J.a02]], ![![2 * J.b20, J.b11], ![J.b11, 2 * J.b02]]]

/-- The coefficients `∂³f_k/∂x_i∂x_j∂x_l` of the canonical field of a jet. -/
def Jet.thirdCoeff (J : Jet) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  ![![![![6 * J.a30, 2 * J.a21], ![2 * J.a21, 2 * J.a12]],
      ![![2 * J.a21, 2 * J.a12], ![2 * J.a12, 6 * J.a03]]],
    ![![![6 * J.b30, 2 * J.b21], ![2 * J.b21, 2 * J.b12]],
      ![![2 * J.b21, 2 * J.b12], ![2 * J.b12, 6 * J.b03]]]]

/-- **Agreement in rotation coordinates.** A planar field whose complexified Jacobian at `0` is
`ω J` and whose second and third derivatives at `0` are those of the jet `J` has Kuznetsov's
`ℓ₁` at `q = p = critVec` equal to the planar formula `Jet.l1`. -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_rot (J : Jet) (hω : 0 < ω)
    {g : State 2 → State 2} (hA : jacobianC g 0 = rotC ω)
    (hB : ∀ k i j, hess g 0 k i j = J.hessCoeff k i j)
    (hC : ∀ k i j l, third g 0 k i j l = J.thirdCoeff k i j l) :
    firstLyapunov g 0 ω critVec critVec = J.l1 ω := by
  unfold firstLyapunov
  rw [hA]
  refine lyap1_rot J hω _ _ (fun u w => ?_) fun u w z => ?_
  · ext k
    rw [bilinC_apply]
    fin_cases k <;> simp [Fin.sum_univ_two, hB, Jet.hessCoeff] <;> ring
  · ext k
    rw [trilinC_apply]
    fin_cases k <;> simp [Fin.sum_univ_two, hC, Jet.thirdCoeff] <;> ring

variable {L : State 2 →L[ℝ] State 2} {Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
  {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)}

/-- The rotation coordinates as a linear map, `T u = (x, y)`. -/
def frameT (L : State 2 →L[ℝ] State 2) (ω : ℝ) : State 2 →L[ℝ] State 2 :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 0; -((L e0) 0 / ω), -((L e1) 0 / ω)]

/-- The inverse of `frameT`: `S w = w₀ P₀ + w₁ P₁`. -/
def frameS (L : State 2 →L[ℝ] State 2) (ω : ℝ) : State 2 →L[ℝ] State 2 :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
    !![(frameVec0 L) 0, (frameVec1 L ω) 0; (frameVec0 L) 1, (frameVec1 L ω) 1]

/-- The critical right eigenvector of `L`: `q = S critVec`. -/
def critQ (L : State 2 →L[ℝ] State 2) (ω : ℝ) : Fin 2 → ℂ := cmat (frameS L ω) *ᵥ critVec

/-- The critical left eigenvector of `L`: `p = Tᵀ critVec`. -/
def critP (L : State 2 →L[ℝ] State 2) (ω : ℝ) : Fin 2 → ℂ :=
  (cmat (frameT L ω))ᵀ *ᵥ critVec

@[tmio T, powerlib_foundation] theorem frameT_apply0 (u : State 2) :
    frameT L ω u 0 = frameX u := by
  simp [frameT, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] theorem frameT_apply1 (u : State 2) :
    frameT L ω u 1 = frameY L ω u := by
  have h0 := congrArg (fun v : State 2 => v 0) (apply_eq L u)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0
  simp only [frameT, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two, frameY_apply, h0]
  simp
  ring

@[tmio T, powerlib_foundation] theorem frameS_apply (w : State 2) :
    frameS L ω w = w 0 • frameVec0 L + w 1 • frameVec1 L ω := by
  ext i
  fin_cases i <;> simp [frameS, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two] <;> ring

/-- `P₀, P₁` is the dual basis of `x, y`. -/
@[tmio T, powerlib_foundation] theorem frame_dual (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) :
    frameX (frameVec0 L) = 1 ∧ frameX (frameVec1 L ω) = 0 ∧ frameY L ω (frameVec0 L) = 0 ∧
      frameY L ω (frameVec1 L ω) = 1 := by
  obtain ⟨hc, -⟩ := frame_coeffs hω hL
  have h := hL e1
  have h0 := congrArg (fun v : State 2 => v 0) h
  simp only [PiLp.smul_apply, smul_eq_mul, e1_apply0, mul_zero] at h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [frameVec0, hc]
  · simp [frameVec1]
  · simp [frameVec0, h0]
  · simp [frameVec1]
    field_simp

@[tmio T, powerlib_foundation] theorem frameS_frameT (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) (u : State 2) : frameS L ω (frameT L ω u) = u := by
  rw [frameS_apply, frameT_apply0, frameT_apply1, ← frame_decomp hω hL u]

@[tmio T, powerlib_foundation] theorem frameT_frameS (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) (w : State 2) : frameT L ω (frameS L ω w) = w := by
  obtain ⟨h1, h2, h3, h4⟩ := frame_dual hω hL
  ext i
  fin_cases i
  · simp [frameT_apply0, frameS_apply, h1, h2]
  · simp [frameT_apply1, frameS_apply, h3, h4]

@[tmio T, powerlib_foundation] theorem cmat_frame (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) :
    cmat (frameT L ω) * cmat (frameS L ω) = 1 ∧ cmat (frameS L ω) * cmat (frameT L ω) = 1 := by
  constructor <;> rw [← cmat_comp, ← cmat_id] <;> congr 1 <;> ext1 w
  · exact frameT_frameS hω hL w
  · exact frameS_frameT hω hL w

@[tmio T, powerlib_foundation] theorem frameS_basisVec0 :
    frameS L ω (basisVec 0) = frameVec0 L := by
  simp [frameS_apply, basisVec]

@[tmio T, powerlib_foundation] theorem frameS_basisVec1 :
    frameS L ω (basisVec 1) = frameVec1 L ω := by
  simp [frameS_apply, basisVec]

/-- `T L S` is the rotation `ω J`. -/
@[tmio T, powerlib_foundation] theorem frameT_comp_L_comp_frameS (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) :
    (frameT L ω).comp (L.comp (frameS L ω)) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![0, -ω; ω, 0] := by
  ext1 w
  have c0 : (frameT L ω (L (frameS L ω w))) 0 = -(ω * w 1) := by
    rw [frameT_apply0, frameX_L hω, ← frameT_apply1, frameT_frameS hω hL]
    ring
  have c1 : (frameT L ω (L (frameS L ω w))) 1 = ω * w 0 := by
    rw [frameT_apply1, frameY_L hω hL, ← frameT_apply0, frameT_frameS hω hL]
  ext i
  fin_cases i
  · simpa [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two] using c0
  · simpa [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_two] using c1

/-- The conjugate of a field with Jacobian `L` by the rotation coordinates has Jacobian `ω J`. -/
@[tmio T, powerlib_foundation] theorem jacobianC_frame (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} (hd1 : fderiv ℝ g 0 = L) :
    cmat (frameT L ω) * jacobianC g 0 * cmat (frameS L ω) = rotC ω := by
  rw [jacobianC, hd1, ← cmat_comp, ← cmat_comp, ContinuousLinearMap.comp_assoc,
    frameT_comp_L_comp_frameS hω hL, cmat_toEuclideanCLM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotC]

/-- **Agreement with Kuznetsov's `ℓ₁`.** For a field `g` whose derivatives at `0` are those of
`u ↦ L u + Q(u, u) + C(u, u, u)` (`Dg(0) = L`, `D²g(0)(u, w) = Q(u, w) + Q(w, u)`, `D³g(0)` the
sum of `C` over the six orders of its arguments), Kuznetsov's first Lyapunov coefficient at the
critical pair `critQ`, `critP` is the planar `l1` (`firstLyapunov_conj` to the rotation
coordinates, then `firstLyapunov_rot`). -/
@[tmio T, powerlib_foundation] theorem firstLyapunov_eq_l1 (hω : 0 < ω)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} (hd1 : fderiv ℝ g 0 = L)
    (hd2 : ∀ u w, iteratedFDeriv ℝ 2 g 0 ![u, w] = Q u w + Q w u)
    (hd3 : ∀ u w z, iteratedFDeriv ℝ 3 g 0 ![u, w, z] = C ![u, w, z] + C ![u, z, w] +
      C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u]) :
    firstLyapunov g 0 ω (critQ L ω) (critP L ω) = l1 L Q C ω := by
  have hω0 := hω.ne'
  set T : State 2 ≃L[ℝ] State 2 := ContinuousLinearEquiv.equivOfInverse (frameT L ω)
    (frameS L ω) (frameS_frameT hω0 hL) (frameT_frameS hω0 hL) with hT
  have hTc : (T : State 2 →L[ℝ] State 2) = frameT L ω := rfl
  have hSc : (T.symm : State 2 →L[ℝ] State 2) = frameS L ω := rfl
  have hTS := (cmat_frame hω0 hL).1
  rw [← firstLyapunov_conj T g 0 ω (critQ L ω) (critP L ω)]
  have hq : cmat (T : State 2 →L[ℝ] State 2) *ᵥ critQ L ω = critVec := by
    rw [hTc, critQ, Matrix.mulVec_mulVec, hTS, Matrix.one_mulVec]
  have hp : (cmat (T.symm : State 2 →L[ℝ] State 2))ᵀ *ᵥ critP L ω = critVec := by
    rw [hSc, critP, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hTS, Matrix.transpose_one,
      Matrix.one_mulVec]
  have hS0 : T.symm (basisVec 0) = frameVec0 L := frameS_basisVec0
  have hS1 : T.symm (basisVec 1) = frameVec1 L ω := frameS_basisVec1
  have hT0 : ∀ v, T v 0 = frameX v := fun v => frameT_apply0 v
  have hT1 : ∀ v, T v 1 = frameY L ω v := fun v => frameT_apply1 v
  rw [hq, hp, map_zero]
  refine firstLyapunov_rot (jet L Q C ω) hω ?_ ?_ ?_
  · have h := jacobianC_conj T g 0
    rw [map_zero] at h
    rw [h, hTc, hSc, jacobianC_frame hω0 hL hd1]
  · intro k i j
    rw [hess, iteratedFDeriv_conj, map_zero]
    have e : (fun i' => T.symm (![basisVec i, basisVec j] i')) =
        ![T.symm (basisVec i), T.symm (basisVec j)] := by
      funext i'; fin_cases i' <;> rfl
    rw [e, hd2]
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [hS0, hS1, hT0, hT1, jet, Jet.hessCoeff] <;> ring
  · intro k i j l
    rw [third, iteratedFDeriv_conj, map_zero]
    have e : (fun i' => T.symm (![basisVec i, basisVec j, basisVec l] i')) =
        ![T.symm (basisVec i), T.symm (basisVec j), T.symm (basisVec l)] := by
      funext i'; fin_cases i' <;> rfl
    rw [e, hd3]
    fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [hS0, hS1, hT0, hT1, jet, Jet.thirdCoeff] <;> ring

/-- `(critQ, critP)` is a critical pair of every field with `g 0 = 0` and `Dg(0) = L`. -/
@[tmio T, powerlib_foundation] theorem isCriticalPair_crit (hω : 0 < ω)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} (hg0 : g 0 = 0)
    (hd1 : fderiv ℝ g 0 = L) : IsCriticalPair g 0 ω (critQ L ω) (critP L ω) := by
  have hω0 := hω.ne'
  set T : State 2 ≃L[ℝ] State 2 := ContinuousLinearEquiv.equivOfInverse (frameT L ω)
    (frameS L ω) (frameS_frameT hω0 hL) (frameT_frameS hω0 hL) with hT
  have hJ : jacobianC (fun z => T (g (T.symm z))) 0 = rotC ω := by
    have h := jacobianC_conj T g 0
    rw [map_zero] at h
    rw [h]
    exact jacobianC_frame hω0 hL hd1
  have h' : IsCriticalPair (fun z => T (g (T.symm z))) 0 ω critVec critVec := by
    refine ⟨by simp [hg0], hω, ?_, ?_, ?_⟩
    · rw [hJ]
      ext i; fin_cases i <;>
        simp [rotC, critVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring_nf <;>
        simp [Complex.I_sq] <;> ring
    · rw [hJ]
      ext i; fin_cases i <;>
        simp [rotC, critVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring_nf <;>
        simp [Complex.I_sq] <;> ring
    · rw [star_critVec]
      simp [critVec, dotProduct, Fin.sum_univ_two]
      ring_nf
      simp [Complex.I_sq]
      ring
  have h'' := isCriticalPair_conj T.symm h'
  have e : (fun z => T.symm ((fun z => T (g (T.symm z))) (T.symm.symm z))) = g := by
    funext z; simp
  rw [e, map_zero] at h''
  exact h''

/-- The critical eigenspaces of the Jacobian `L` are the lines spanned by `critQ` and `critP`. -/
@[tmio T, powerlib_foundation] theorem crit_spans (hω : ω ≠ 0)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} (hd1 : fderiv ℝ g 0 = L) :
    (∀ v, jacobianC g 0 *ᵥ v = ((ω : ℂ) * I) • v → ∃ c : ℂ, v = c • critQ L ω) ∧
    (∀ v, (jacobianC g 0)ᵀ *ᵥ v = (-((ω : ℂ) * I)) • v → ∃ c : ℂ, v = c • critP L ω) := by
  obtain ⟨hTS, hST⟩ := cmat_frame hω hL
  have hJ := jacobianC_frame hω hL hd1
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  constructor
  · intro v hv
    set v' := cmat (frameT L ω) *ᵥ v with hv'
    have hrot : rotC ω *ᵥ v' = ((ω : ℂ) * I) • v' := by
      rw [← hJ, hv', Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hST,
        Matrix.mul_one, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
    have h0 := congrFun hrot 0
    simp [rotC, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    refine ⟨(1 - I) * v' 0, ?_⟩
    have hvv : v = cmat (frameS L ω) *ᵥ v' := by
      rw [hv', Matrix.mulVec_mulVec, hST, Matrix.one_mulVec]
    rw [hvv, critQ, ← Matrix.mulVec_smul]
    congr 1
    ext i; fin_cases i
    · simp [critVec]; ring_nf; simp [Complex.I_sq]; ring
    · simp [critVec]
      have : v' 1 = -I * v' 0 := by
        apply mul_left_cancel₀ hω'
        linear_combination (-1 : ℂ) * h0
      rw [this]; ring_nf; simp [Complex.I_sq]
  · intro v hv
    set v' := (cmat (frameS L ω))ᵀ *ᵥ v with hv'
    have hrot : (rotC ω)ᵀ *ᵥ v' = (-((ω : ℂ) * I)) • v' := by
      have hTSt : (cmat (frameT L ω))ᵀ * (cmat (frameS L ω))ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hST, Matrix.transpose_one]
      rw [← hJ, Matrix.transpose_mul, Matrix.transpose_mul, hv', Matrix.mulVec_mulVec,
        Matrix.mul_assoc, Matrix.mul_assoc, hTSt, Matrix.mul_one, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_smul]
    have h0 := congrFun hrot 0
    simp [rotC, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    refine ⟨(1 - I) * v' 0, ?_⟩
    have hvv : v = (cmat (frameT L ω))ᵀ *ᵥ v' := by
      rw [hv', Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hST, Matrix.transpose_one,
        Matrix.one_mulVec]
    rw [hvv, critP, ← Matrix.mulVec_smul]
    congr 1
    ext i; fin_cases i
    · simp [critVec]; ring_nf; simp [Complex.I_sq]; ring
    · simp [critVec]
      have : v' 1 = -I * v' 0 := by
        apply mul_left_cancel₀ hω'
        linear_combination h0
      rw [this]; ring_nf; simp [Complex.I_sq]

/-- The sign of Kuznetsov's `ℓ₁` at any critical pair is the sign of the planar `l1`. -/
@[tmio T, powerlib_foundation] private theorem sign_firstLyapunov_eq_l1 (hω : 0 < ω)
    (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2} (hd1 : fderiv ℝ g 0 = L)
    (hd2 : ∀ u w, iteratedFDeriv ℝ 2 g 0 ![u, w] = Q u w + Q w u)
    (hd3 : ∀ u w z, iteratedFDeriv ℝ 3 g 0 ![u, w, z] = C ![u, w, z] + C ![u, z, w] +
      C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u])
    {q p : Fin 2 → ℂ} (hc : IsCriticalPair g 0 ω q p) :
    SignType.sign (firstLyapunov g 0 ω q p) = SignType.sign (l1 L Q C ω) := by
  obtain ⟨h1, h2⟩ := crit_spans hω.ne' hL hd1
  rw [sign_firstLyapunov_eq h1 h2 (isCriticalPair_crit hω hL hc.equilibrium hd1) hc,
    firstLyapunov_eq_l1 hω hL hd1 hd2 hd3]

/-- **Planar weak focus from Kuznetsov's `ℓ₁ < 0`.** A planar field, continuous near `0`, with
the cubic expansion of `localAsymptoticStable_of_l1_neg` and derivatives at `0` matching it
(`Dg(0) = L`, `D²g(0)`, `D³g(0)` from `Q`, `C`) whose first Lyapunov coefficient is negative
for some critical pair is locally asymptotically stable. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_expansion_firstLyapunov_neg
    (hω : 0 < ω) (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2}
    {U : Set (State 2)} (hU : U ∈ 𝓝 0) (hg : ContinuousOn g U)
    (hexp : (fun u => g u - (L u + Q u u + C ![u, u, u])) =o[𝓝 0] fun u => ‖u‖ ^ 3)
    (hd1 : fderiv ℝ g 0 = L) (hd2 : ∀ u w, iteratedFDeriv ℝ 2 g 0 ![u, w] = Q u w + Q w u)
    (hd3 : ∀ u w z, iteratedFDeriv ℝ 3 g 0 ![u, w, z] = C ![u, w, z] + C ![u, z, w] +
      C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u])
    {q p : Fin 2 → ℂ} (hc : IsCriticalPair g 0 ω q p) (hl : firstLyapunov g 0 ω q p < 0) :
    LocalAsymptoticStable g 0 := by
  have hs := sign_firstLyapunov_eq_l1 hω hL hd1 hd2 hd3 hc
  rw [sign_neg hl, eq_comm, sign_eq_neg_one_iff] at hs
  exact localAsymptoticStable_of_l1_neg hω hL hU hg hexp hs

/-- **Planar unstable focus from Kuznetsov's `ℓ₁ > 0`.** A planar field, Lipschitz near `0`,
with the cubic expansion and matching derivatives whose first Lyapunov coefficient is positive
for some critical pair is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_expansion_firstLyapunov_pos
    (hω : 0 < ω) (hL : ∀ u, L (L u) = -(ω ^ 2) • u) {g : State 2 → State 2}
    {U : Set (State 2)} {K : NNReal} (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    (hexp : (fun u => g u - (L u + Q u u + C ![u, u, u])) =o[𝓝 0] fun u => ‖u‖ ^ 3)
    (hd1 : fderiv ℝ g 0 = L) (hd2 : ∀ u w, iteratedFDeriv ℝ 2 g 0 ![u, w] = Q u w + Q w u)
    (hd3 : ∀ u w z, iteratedFDeriv ℝ 3 g 0 ![u, w, z] = C ![u, w, z] + C ![u, z, w] +
      C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u])
    {q p : Fin 2 → ℂ} (hc : IsCriticalPair g 0 ω q p) (hl : 0 < firstLyapunov g 0 ω q p) :
    Unstable g 0 := by
  have hs := sign_firstLyapunov_eq_l1 hω hL hd1 hd2 hd3 hc
  rw [sign_pos hl, eq_comm, sign_eq_one_iff] at hs
  exact unstable_of_l1_pos hω hL hU hg hexp hs

end Agreement

end powerlib.Dynamics.Degenerate.PlanarFocus
