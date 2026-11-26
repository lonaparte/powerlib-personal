import theorem.Dynamics.CenterReductionBT
import theorem.Dynamics.Instability

/-! # The zero–Hopf normal form at second order and its instability laws (foundation)

A field on `ℝ³` whose linear part is `L w = (0, −ω w₂, ω w₁)` (`ω ≠ 0`: the eigenvalues `0, ±iω`)
and whose quadratic part is a bilinear `G` is carried by Kuznetsov's quadratic change of
coordinates `Φ(w) = w + H(w, w)` to the truncated zero–Hopf normal form
`u̇ = a u² + b r²`, `ż = (iω + (c + id) u) z` up to `o(‖w‖²)` (`u = w₀`, `z = w₁ + i w₂`,
`r = |z|`), with `a = G(e₀, e₀)₀`, `b = (G(e₁, e₁)₀ + G(e₂, e₂)₀)/2` and
`c = ((G(e₀, e₁) + G(e₁, e₀))₁ + (G(e₀, e₂) + G(e₂, e₀))₂)/2`. Three Chetaev functions of the
normal form, read through `Φ`, decide **instability robustly to every term of order three**:
* `ab > 0`: `W = a u` (`Ẇ = a²u² + ab r²`, positive definite);
* `a(a − c) > 0`: the cone `r² < k u²` around the half axis on which `u̇ = a u²` escapes, which
  attracts its neighbours (`W = k u² − r²`, cut to the side `a u > 0`);
* `a = 0`, `bc > 0`: the cone around the invariant cone `r² = (c/b) u²` of the truncation
  (`W = α u⁴ − (r² − (c/b) u²)²`, cut to the side `b u > 0`).

Scope.
* Generic: `State 3 = ℝ³`, any bilinear `G`, a field `g` Lipschitz on a neighbourhood of `0` with
  `g(w) = Lw + G(w, w) + o(‖w‖²)`; the general Chetaev law (`unstable_of_quadMap_chetaev`) is
  stated on `State n` for any quadratic change of coordinates, linear part and quadratic normal
  form. Stability notion: LeanForControl's `Unstable` (Lyapunov instability). Nothing here
  describes a physical system (foundation).
* **Decided regimes**: `ZeroHopfDecided a b c` (`ab > 0`, or `a(a − c) > 0`, or `a = 0` and
  `bc > 0`). In the truncated normal form `u̇ = a u² + b r²`, `ṙ = c u r` (on `r ≥ 0`) these are
  exactly the coefficients with `ab > 0` or with an invariant ray that is outgoing and
  attracts its neighbours (for `a ≠ 0` the interior rays `r² = ((c − a)/b) u²` add nothing to
  `ab > 0 ∨ a(a − c) > 0`; for `a = 0` the interior ray is the only one). **Not decided** here:
  `a ≠ 0`, `ab ≤ 0`, `a(a − c) ≤ 0` (with `a > 0`: `b ≤ 0 ≤ c − a`; for `b < 0 < c − a` every
  orbit of the truncation is a loop through `0`, `u² − b r²/(c − a) = C r^{2a/c}`, an elliptic
  sector: the truncation is unstable, but the escaping orbits start in a horn
  `r ≲ |u|^{c/a}`, so a proof needs the normal form to order `> c/a`), and `a = 0`, `bc ≤ 0`
  (for `bc < 0` the truncation has the first integral `u² − (b/c) r²`, positive definite: a
  centre-type second-order part, decided only by higher-order terms).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.5 (the
zero–Hopf normal form `ξ̇ = ξ² + s r²`, `ṙ = r(θ ξ + …)`, its quadratic part and the averaging
of the non-resonant terms) and §8.7 (the projection formulas); Guckenheimer–Holmes, *Nonlinear
Oscillations, Dynamical Systems, and Bifurcations of Vector Fields* (1983), §7.4 (the
truncated normal form in cylindrical coordinates); Khalil, *Nonlinear Systems* (3rd ed.),
Theorem 4.3 (Chetaev). The quadratic change of coordinates and its conjugation law are
`Dynamics.CenterManifold.quadMap`, `quadMap_conj_isLittleO`
(`theorem/Dynamics/CenterReductionBT.lean`); the Chetaev law is
`Dynamics.unstable_of_chetaev_lipschitzOn` (`theorem/Dynamics/Instability.lean`).

Results.
* Monomials and the diagonal: `spaceMono`, `spaceMono_apply`, `space_bilin_diag`.
* The linear part and the normal form: `zhL`, `zhL_apply`, `zhNF` (`N(w, w) =
  (a w₀² + b(w₁² + w₂²), w₀(c w₁ − d w₂), w₀(d w₁ + c w₂))`), `zhNF_apply`; the coefficients of
  a bilinear map `zhCoeffA`, `zhCoeffB`, `zhCoeffC`, `zhCoeffD`.
* **`zhTransform_homological`**: `H = zhTransform G ω` solves
  `G(w, w) + H(w, Lw) + H(Lw, w) = L H(w, w) + N(w, w)` with `N = zhNF a b c d` of `G`;
  **`zhNormalForm_isLittleO`**: every `g(w) = Lw + G(w, w) + o(‖w‖²)` is carried by
  `Φ = quadMap (zhTransform G ω)` to `Ly + N(y, y)` up to `o(‖w‖²)`.
* **`unstable_of_quadMap_chetaev`** (any dimension): if
  `DΦ(w) g(w) − (LΦ(w) + N(Φ(w), Φ(w))) = o(‖w‖²)` for `Φ = quadMap H`, and a `C¹` function
  `W` with `W(0) = 0`, positive arbitrarily close to `0`, satisfies
  `DW(v)(Lv + N(v, v)) ≥ γ ‖v‖^{m+2}` and `‖DW(v)‖ ≤ C ‖v‖^m` where it is positive near `0`,
  then `0` is unstable for `g` (Chetaev with `W ∘ Φ`; seeds through the local inverse of `Φ`).
* The cut-off `minSq t = (min t 0)²`: `hasDerivAt_minSq`, `contDiff_minSq`.
* **`unstable_of_zhCoeff_mul_pos`** (`ab > 0`), **`unstable_of_zhCoeff_sub_pos`**
  (`a(a − c) > 0`), **`unstable_of_zhCoeff_zero`** (`a = 0`, `bc > 0`), and
  **`unstable_of_zeroHopfDecided`**: `ZeroHopfDecided (zhCoeffA G) (zhCoeffB G) (zhCoeffC G)`
  gives `Unstable g 0`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold
open Set Filter Topology Asymptotics
open powerlib.Dynamics (mk3 mk3_zero mk3_one mk3_two state3_ext)

/-! ## Monomials on `ℝ³` -/

section Monomials

/-- The monomial bilinear map `(u, v) ↦ uᵢ vⱼ e` on `ℝ³`. -/
def spaceMono (i j : Fin 3) (e : State 3) : State 3 →L[ℝ] State 3 →L[ℝ] State 3 :=
  (EuclideanSpace.proj i).smulRight ((EuclideanSpace.proj j).smulRight e)

@[tmio T, powerlib_foundation] theorem spaceMono_apply (i j : Fin 3) (e u v : State 3) :
    spaceMono i j e u v = (u i * v j) • e := by
  simp [spaceMono, mul_smul]

/-- A bilinear map on `ℝ³` on the diagonal through its values on the basis. -/
@[tmio T, powerlib_foundation] theorem space_bilin_diag (G : State 3 →L[ℝ] State 3 →L[ℝ] State 3)
    (w : State 3) :
    G w w = (w 0 * w 0) • G (mk3 1 0 0) (mk3 1 0 0) + (w 1 * w 1) • G (mk3 0 1 0) (mk3 0 1 0) +
      (w 2 * w 2) • G (mk3 0 0 1) (mk3 0 0 1) +
      (w 0 * w 1) • (G (mk3 1 0 0) (mk3 0 1 0) + G (mk3 0 1 0) (mk3 1 0 0)) +
      (w 0 * w 2) • (G (mk3 1 0 0) (mk3 0 0 1) + G (mk3 0 0 1) (mk3 1 0 0)) +
      (w 1 * w 2) • (G (mk3 0 1 0) (mk3 0 0 1) + G (mk3 0 0 1) (mk3 0 1 0)) := by
  have hw : w = w 0 • mk3 1 0 0 + w 1 • mk3 0 1 0 + w 2 • mk3 0 0 1 := by
    refine state3_ext ?_ ?_ ?_ <;> simp
  conv_lhs => rw [hw]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_add, smul_smul]
  module

end Monomials

/-! ## The linear part, the normal form and the homological equation -/

section NormalForm

/-- The linear part `w ↦ (0, −ω w₂, ω w₁)` of a zero–Hopf point (eigenvalues `0, ±iω`). -/
def zhL (ω : ℝ) : State 3 →L[ℝ] State 3 :=
  (EuclideanSpace.proj (2 : Fin 3)).smulRight (mk3 0 (-ω) 0) +
    (EuclideanSpace.proj (1 : Fin 3)).smulRight (mk3 0 0 ω)

@[tmio T, powerlib_foundation] theorem zhL_apply (ω : ℝ) (w : State 3) :
    zhL ω w = mk3 0 (-(ω * w 2)) (ω * w 1) := by
  refine state3_ext ?_ ?_ ?_ <;> simp [zhL] <;> ring

/-- The quadratic part of the zero–Hopf normal form,
`N(w, w) = (a w₀² + b (w₁² + w₂²), w₀ (c w₁ − d w₂), w₀ (d w₁ + c w₂))`: in `u = w₀`,
`z = w₁ + i w₂`, `u̇ = a u² + b |z|²`, `ż = (c + id) u z`. -/
def zhNF (a b c d : ℝ) : State 3 →L[ℝ] State 3 →L[ℝ] State 3 :=
  spaceMono 0 0 (mk3 a 0 0) + spaceMono 1 1 (mk3 b 0 0) + spaceMono 2 2 (mk3 b 0 0) +
    spaceMono 0 1 (mk3 0 c d) + spaceMono 0 2 (mk3 0 (-d) c)

@[tmio T, powerlib_foundation] theorem zhNF_apply (a b c d : ℝ) (w : State 3) :
    zhNF a b c d w w = mk3 (a * w 0 ^ 2 + b * (w 1 ^ 2 + w 2 ^ 2)) (w 0 * (c * w 1 - d * w 2))
      (w 0 * (d * w 1 + c * w 2)) := by
  refine state3_ext ?_ ?_ ?_ <;> simp [zhNF, spaceMono_apply] <;> ring

/-- The coefficient `a = G(e₀, e₀)₀` of a bilinear map on `ℝ³`. -/
def zhCoeffA (G : State 3 →L[ℝ] State 3 →L[ℝ] State 3) : ℝ := G (mk3 1 0 0) (mk3 1 0 0) 0

/-- The coefficient `b = (G(e₁, e₁)₀ + G(e₂, e₂)₀)/2` (the mean of the `u̇` part over the circle
`|z| = 1`). -/
def zhCoeffB (G : State 3 →L[ℝ] State 3 →L[ℝ] State 3) : ℝ :=
  (G (mk3 0 1 0) (mk3 0 1 0) 0 + G (mk3 0 0 1) (mk3 0 0 1) 0) / 2

/-- The coefficient `c = ((G(e₀, e₁) + G(e₁, e₀))₁ + (G(e₀, e₂) + G(e₂, e₀))₂)/2` (the radial
growth rate of `z` per unit `u`). -/
def zhCoeffC (G : State 3 →L[ℝ] State 3 →L[ℝ] State 3) : ℝ :=
  (G (mk3 1 0 0) (mk3 0 1 0) 1 + G (mk3 0 1 0) (mk3 1 0 0) 1 + G (mk3 1 0 0) (mk3 0 0 1) 2 +
    G (mk3 0 0 1) (mk3 1 0 0) 2) / 2

/-- The coefficient `d = ((G(e₀, e₁) + G(e₁, e₀))₂ − (G(e₀, e₂) + G(e₂, e₀))₁)/2` (the
frequency shift of `z` per unit `u`). -/
def zhCoeffD (G : State 3 →L[ℝ] State 3 →L[ℝ] State 3) : ℝ :=
  (G (mk3 1 0 0) (mk3 0 1 0) 2 + G (mk3 0 1 0) (mk3 1 0 0) 2 - G (mk3 1 0 0) (mk3 0 0 1) 1 -
    G (mk3 0 0 1) (mk3 1 0 0) 1) / 2

/-- Kuznetsov's quadratic change of coordinates of the zero–Hopf normal form: the solution
`H(w, w) = Σ_{j ≤ k} wⱼ wₖ hⱼₖ` of the homological equation with `(h₀₀)₀ = (h₂₂)₀ = (h₀₁)₂ =
(h₀₂)₂ = 0` (SymPy, exact; the identity is `zhTransform_homological`), written with the diagonal
values `dⱼ = G(eⱼ, eⱼ)` and the symmetric values `sⱼₖ = G(eⱼ, eₖ) + G(eₖ, eⱼ)`. -/
def zhTransform (G : State 3 →L[ℝ] State 3 →L[ℝ] State 3) (ω : ℝ) :
    State 3 →L[ℝ] State 3 →L[ℝ] State 3 :=
  let d0 := G (mk3 1 0 0) (mk3 1 0 0)
  let d1 := G (mk3 0 1 0) (mk3 0 1 0)
  let d2 := G (mk3 0 0 1) (mk3 0 0 1)
  let s01 := G (mk3 1 0 0) (mk3 0 1 0) + G (mk3 0 1 0) (mk3 1 0 0)
  let s02 := G (mk3 1 0 0) (mk3 0 0 1) + G (mk3 0 0 1) (mk3 1 0 0)
  let s12 := G (mk3 0 1 0) (mk3 0 0 1) + G (mk3 0 0 1) (mk3 0 1 0)
  spaceMono 0 0 (mk3 0 (d0 2 / ω) (-(d0 1 / ω))) +
    spaceMono 0 1 (mk3 (s02 0 / ω) ((s02 1 + s01 2) / (2 * ω)) 0) +
    spaceMono 0 2 (mk3 (-(s01 0 / ω)) ((s02 2 - s01 1) / (2 * ω)) 0) +
    spaceMono 1 1 (mk3 (s12 0 / (2 * ω)) ((s12 1 + d1 2 + 2 * d2 2) / (3 * ω))
      ((s12 2 - d1 1 - 2 * d2 1) / (3 * ω))) +
    spaceMono 1 2 (mk3 ((d2 0 - d1 0) / (2 * ω)) ((2 * d2 1 - 2 * d1 1 - s12 2) / (3 * ω))
      ((s12 1 - 2 * d1 2 + 2 * d2 2) / (3 * ω))) +
    spaceMono 2 2 (mk3 0 ((2 * d1 2 + d2 2 - s12 1) / (3 * ω))
      ((-2 * d1 1 - d2 1 - s12 2) / (3 * ω)))

/-- **The homological equation of the zero–Hopf normal form** is solved by `zhTransform G ω`
(`ω ≠ 0`): `G(w, w) + H(w, Lw) + H(Lw, w) = L H(w, w) + N(w, w)` with `L = zhL ω` and
`N = zhNF a b c d`, `a, b, c, d` the coefficients of `G`. -/
@[tmio T, powerlib_foundation] theorem zhTransform_homological
    (G : State 3 →L[ℝ] State 3 →L[ℝ] State 3) {ω : ℝ} (hω : ω ≠ 0) (w : State 3) :
    G w w + zhTransform G ω w (zhL ω w) + zhTransform G ω (zhL ω w) w =
      zhL ω (zhTransform G ω w w) +
        zhNF (zhCoeffA G) (zhCoeffB G) (zhCoeffC G) (zhCoeffD G) w w := by
  rw [space_bilin_diag G w, zhNF_apply]
  refine state3_ext ?_ ?_ ?_ <;>
    simp [zhTransform, spaceMono_apply, zhL_apply, zhCoeffA, zhCoeffB, zhCoeffC,
      zhCoeffD] <;> field_simp <;> ring

/-- **The zero–Hopf normal form at second order.** A field `g(w) = Lw + G(w, w) + o(‖w‖²)` on
`ℝ³` with `L = zhL ω`, `ω ≠ 0`, is carried by `Φ = quadMap (zhTransform G ω)` to
`y ↦ Ly + N(y, y)`, `N = zhNF a b c d` of `G`, up to `o(‖w‖²)`. -/
@[tmio T, powerlib_foundation] theorem zhNormalForm_isLittleO
    {G : State 3 →L[ℝ] State 3 →L[ℝ] State 3} {ω : ℝ} (hω : ω ≠ 0) {g : State 3 → State 3}
    (hg : (fun w => g w - (zhL ω w + G w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2) :
    (fun w => fderiv ℝ (quadMap (zhTransform G ω)) w (g w) -
      (zhL ω (quadMap (zhTransform G ω) w) +
        zhNF (zhCoeffA G) (zhCoeffB G) (zhCoeffC G) (zhCoeffD G)
          (quadMap (zhTransform G ω) w) (quadMap (zhTransform G ω) w)))
      =o[𝓝 0] fun w => ‖w‖ ^ 2 :=
  quadMap_conj_isLittleO (zhTransform_homological G hω) hg

end NormalForm

/-! ## Chetaev functions read through a quadratic change of coordinates -/

section Chetaev

variable {n m : ℕ}

@[tmio T, powerlib_foundation] private theorem contDiff_quadMap
    (H : State n →L[ℝ] State n →L[ℝ] State n) : ContDiff ℝ 1 (quadMap H) :=
  contDiff_id.add (H.contDiff.clm_apply contDiff_id)

/-- **Chetaev through a quadratic change of coordinates.** Let `g` be Lipschitz on a
neighbourhood of `0` and carried by `Φ = quadMap H` to `y ↦ Ly + N(y, y)` up to `o(‖w‖²)`. Let `W`
be `C¹` with `W(0) = 0`, positive at states arbitrarily close to `0`, and, for some `m`, wherever
`W(v) > 0` with `‖v‖ < ρ`: `DW(v)(Lv + N(v, v)) ≥ γ ‖v‖^{m+2}` (`γ > 0`) and
`‖DW(v)‖ ≤ C ‖v‖^m`. Then `0` is unstable for `g`: `W ∘ Φ` is a Chetaev function (the remainder
`DW(v)(o(‖w‖²)) = o(‖v‖^{m+2})` since `‖w‖ ≤ 2‖Φ(w)‖` near `0`), and the seeds of `W` are carried
back by the local inverse of `Φ` (`DΦ(0) = 1`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_quadMap_chetaev {g : State n → State n}
    {U : Set (State n)} {K : NNReal} (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    {L : State n →L[ℝ] State n} {H N : State n →L[ℝ] State n →L[ℝ] State n}
    (hE : (fun w => fderiv ℝ (quadMap H) w (g w) -
      (L (quadMap H w) + N (quadMap H w) (quadMap H w))) =o[𝓝 0] fun w => ‖w‖ ^ 2)
    {W : State n → ℝ} (hW : ContDiff ℝ 1 W) (hW0 : W 0 = 0) {ρ γ C : ℝ} (hρ : 0 < ρ)
    (hγ : 0 < γ)
    (hdec : ∀ v, ‖v‖ < ρ → 0 < W v →
      γ * ‖v‖ ^ (m + 2) ≤ fderiv ℝ W v (L v + N v v) ∧ ‖fderiv ℝ W v‖ ≤ C * ‖v‖ ^ m)
    (hseed : ∀ ε > 0, ∃ v, ‖v‖ < ε ∧ 0 < W v) : Unstable g 0 := by
  set Φ := quadMap H with hΦ
  have hΦc : ContDiff ℝ 1 Φ := contDiff_quadMap H
  have hΦ0 : Φ 0 = 0 := by simp [hΦ, quadMap]
  have hd0 : HasStrictFDerivAt Φ
      ((ContinuousLinearEquiv.refl ℝ (State n)) : State n →L[ℝ] State n) 0 := by
    have h1 := (hΦc.contDiffAt (x := 0)).hasStrictFDerivAt one_ne_zero
    have h2 : fderiv ℝ Φ 0 = ContinuousLinearMap.id ℝ (State n) := by
      rw [(hasFDerivAt_quadMap H 0).fderiv]; ext x; simp
    rw [h2] at h1
    exact h1
  -- the seeds of `W ∘ Φ`, through the local inverse of `Φ`
  have hseedV : ∀ ε > 0, ∃ x, ‖x - 0‖ < ε ∧ 0 < W (Φ x) := by
    intro ε hε
    have hev := hd0.eventually_right_inverse
    have hli := hd0.localInverse_tendsto
    rw [hΦ0] at hev hli
    have hb : ∀ᶠ y in 𝓝 (0 : State n), ‖hd0.localInverse Φ _ 0 y‖ < ε :=
      ((Metric.tendsto_nhds.mp hli) ε hε).mono fun y hy => by simpa using hy
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hb)
    obtain ⟨v, hv, hWv⟩ := hseed δ hδ
    obtain ⟨h1, h2⟩ := hball (by simpa using hv)
    exact ⟨_, by simpa using h2, by rw [h1]; exact hWv⟩
  -- the comparison `‖w‖/2 ≤ ‖Φ w‖ ≤ 2‖w‖` and the remainder
  have hH : ∀ w, ‖Φ w - w‖ ≤ ‖H‖ * ‖w‖ ^ 2 := fun w => by
    simp only [hΦ, quadMap, add_sub_cancel_left]
    calc ‖H w w‖ ≤ ‖H w‖ * ‖w‖ := (H w).le_opNorm w
      _ ≤ ‖H‖ * ‖w‖ * ‖w‖ := by gcongr; exact H.le_opNorm w
      _ = ‖H‖ * ‖w‖ ^ 2 := by ring
  set η := γ / (8 * (|C| + 1)) with hη
  have hη0 : 0 < η := by positivity
  have h4η : 4 * η * |C| ≤ γ / 2 := by
    rw [hη, show 4 * (γ / (8 * (|C| + 1))) * |C| = γ / 2 * (|C| / (|C| + 1)) by
      field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  obtain ⟨r₀, hr₀, hr₀E⟩ := Metric.eventually_nhds_iff.mp (hE.def hη0)
  set r := min (r₀ / 2) (min (ρ / 4) (1 / (2 * (‖H‖ + 1)))) with hr
  have hr0 : 0 < r := by positivity
  have hV : ContDiff ℝ 1 (fun x => W (Φ x)) := hW.comp hΦc
  refine unstable_of_chetaev_lipschitzOn hU hg hV hr0 hseedV fun x hx hWx => ?_
  rw [sub_zero] at hx
  have hxr₀ : ‖x‖ < r₀ := by
    have := min_le_left (r₀ / 2) (min (ρ / 4) (1 / (2 * (‖H‖ + 1))))
    linarith
  have hxρ : ‖x‖ ≤ ρ / 4 := hx.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hxH : ‖H‖ * ‖x‖ ≤ 1 / 2 := by
    have h1 : ‖x‖ ≤ 1 / (2 * (‖H‖ + 1)) :=
      hx.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : ‖H‖ * ‖x‖ ≤ (‖H‖ + 1) * ‖x‖ := by nlinarith [norm_nonneg x]
    have h3 : (‖H‖ + 1) * ‖x‖ ≤ (‖H‖ + 1) * (1 / (2 * (‖H‖ + 1))) := by gcongr
    have h4 : (‖H‖ + 1) * (1 / (2 * (‖H‖ + 1))) = 1 / 2 := by field_simp
    linarith
  set v := Φ x with hv
  have hvx : ‖v - x‖ ≤ ‖x‖ / 2 := by
    refine (hH x).trans ?_
    have : ‖H‖ * ‖x‖ ^ 2 = (‖H‖ * ‖x‖) * ‖x‖ := by ring
    rw [this]
    nlinarith [norm_nonneg x]
  have hv_le : ‖v‖ ≤ 2 * ‖x‖ := by
    have := norm_le_norm_add_norm_sub' v x
    linarith [norm_sub_rev v x, norm_nonneg x]
  have hx_le : ‖x‖ ≤ 2 * ‖v‖ := by
    have := norm_le_norm_add_norm_sub' x v
    rw [norm_sub_rev] at this
    linarith
  have hvρ : ‖v‖ < ρ := by linarith
  obtain ⟨hlow, hDW⟩ := hdec v hvρ hWx
  have hv0 : v ≠ 0 := fun h => by rw [h, hW0] at hWx; exact lt_irrefl _ hWx
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hderiv : fderiv ℝ (fun x => W (Φ x)) x (g x) = fderiv ℝ W v (fderiv ℝ Φ x (g x)) := by
    rw [fderiv_fun_comp x ((hW.differentiable one_ne_zero) _) ((hΦc.differentiable one_ne_zero) _)]
    rfl
  set e := fderiv ℝ Φ x (g x) - (L v + N v v) with he_def
  have he : ‖e‖ ≤ η * ‖x‖ ^ 2 := by
    have h := hr₀E (by simpa using hxr₀)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h
  have hsplit : fderiv ℝ Φ x (g x) = (L v + N v v) + e := by rw [he_def]; abel
  rw [hderiv, hsplit, map_add]
  have hC0 : 0 ≤ C * ‖v‖ ^ m := (norm_nonneg _).trans hDW
  have hbound : |fderiv ℝ W v e| ≤ C * ‖v‖ ^ m * (η * ‖x‖ ^ 2) := by
    calc |fderiv ℝ W v e| ≤ ‖fderiv ℝ W v‖ * ‖e‖ := by
          rw [← Real.norm_eq_abs]; exact (fderiv ℝ W v).le_opNorm e
      _ ≤ C * ‖v‖ ^ m * (η * ‖x‖ ^ 2) := by gcongr
  have hx2 : ‖x‖ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hCabs : C * ‖v‖ ^ m ≤ |C| * ‖v‖ ^ m := by
    gcongr; exact le_abs_self C
  have hpow : ‖v‖ ^ (m + 2) = ‖v‖ ^ m * ‖v‖ ^ 2 := pow_add _ _ _
  have hvm : 0 < ‖v‖ ^ m := pow_pos hvpos m
  have hrem : C * ‖v‖ ^ m * (η * ‖x‖ ^ 2) ≤ γ / 2 * ‖v‖ ^ (m + 2) := by
    calc C * ‖v‖ ^ m * (η * ‖x‖ ^ 2) ≤ |C| * ‖v‖ ^ m * (η * (4 * ‖v‖ ^ 2)) := by
          gcongr
      _ = (4 * η * |C|) * (‖v‖ ^ m * ‖v‖ ^ 2) := by ring
      _ ≤ γ / 2 * (‖v‖ ^ m * ‖v‖ ^ 2) := by gcongr
      _ = γ / 2 * ‖v‖ ^ (m + 2) := by rw [hpow]
  have hpos : 0 < γ / 2 * ‖v‖ ^ (m + 2) := by positivity
  have := neg_abs_le (fderiv ℝ W v e)
  linarith

end Chetaev

/-! ## The three Chetaev functions of the zero–Hopf normal form -/

section ZeroHopfChetaev

@[tmio T, powerlib_foundation] private theorem norm_sq_three (v : State 3) :
    ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

@[tmio T, powerlib_foundation] private theorem norm_le_of_sq_le {v : State 3} {s : ℝ}
    (hs : 0 ≤ s) (h : ‖v‖ ^ 2 ≤ s ^ 2) : ‖v‖ ≤ s :=
  le_of_pow_le_pow_left₀ two_ne_zero hs h

/-- The cut-off `t ↦ (min t 0)²`: `t²` for `t ≤ 0`, zero for `t ≥ 0`. -/
def minSq (t : ℝ) : ℝ := min t 0 ^ 2

@[tmio T, powerlib_foundation] theorem hasDerivAt_minSq (t : ℝ) :
    HasDerivAt minSq (2 * min t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : minSq =ᶠ[𝓝 t] fun s => s ^ 2 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [minSq, min_eq_left (Set.mem_Iio.mp hs).le]
    rw [min_eq_left ht.le]
    have h := hasDerivAt_pow 2 t
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h
    exact h.congr_of_eventuallyEq hev
  · subst ht
    rw [min_self, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have hb : (fun h : ℝ => minSq (0 + h) - minSq 0 - h • (0 : ℝ)) =O[𝓝 0]
        fun h : ℝ => h ^ 2 := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
      have hm : min h 0 ^ 2 ≤ h ^ 2 := by
        rcases le_total h 0 with hh | hh
        · rw [min_eq_left hh]
        · rw [min_eq_right hh, zero_pow two_ne_zero]; positivity
      have e : minSq (0 + h) - minSq 0 - h • (0 : ℝ) = min h 0 ^ 2 := by
        simp [minSq]
      rw [e, one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      exact hm
    exact hb.trans_isLittleO (isLittleO_pow_id (by norm_num))
  · have hev : minSq =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [minSq, min_eq_right (Set.mem_Ioi.mp hs).le]
    rw [min_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev

@[tmio T, powerlib_foundation] theorem contDiff_minSq : ContDiff ℝ 1 minSq := by
  refine contDiff_one_iff_deriv.mpr ⟨fun t => (hasDerivAt_minSq t).differentiableAt, ?_⟩
  have h : deriv minSq = fun t => 2 * min t 0 := funext fun t => (hasDerivAt_minSq t).deriv
  rw [h]
  exact continuous_const.mul (continuous_id.min continuous_const)

@[tmio T, powerlib_foundation] private theorem minSq_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    minSq t = t ^ 2 := by
  simp [minSq, min_eq_left ht]

@[tmio T, powerlib_foundation] private theorem minSq_of_pos {t : ℝ} (ht : 0 < t) :
    minSq t = 0 := by
  simp [minSq, min_eq_right ht.le]

variable {G : State 3 →L[ℝ] State 3 →L[ℝ] State 3} {ω : ℝ} {g : State 3 → State 3}
  {U : Set (State 3)} {K : NNReal}

/-- **Zero–Hopf instability, `ab > 0`.** If `g(w) = Lw + G(w, w) + o(‖w‖²)` on `ℝ³`
(`L = zhL ω`, `ω ≠ 0`), `g` is Lipschitz near `0` and `a b > 0` for the coefficients `a, b` of
`G`, then `0` is unstable: `W = a u` has `Ẇ = a²u² + ab r²` on the normal form. -/
@[tmio T, powerlib_foundation] theorem unstable_of_zhCoeff_mul_pos (hω : ω ≠ 0)
    (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    (hexp : (fun w => g w - (zhL ω w + G w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2)
    (hab : 0 < zhCoeffA G * zhCoeffB G) : Unstable g 0 := by
  set a := zhCoeffA G with ha_def
  set b := zhCoeffB G with hb_def
  have ha : a ≠ 0 := left_ne_zero_of_mul hab.ne'
  have ha2 : 0 < a ^ 2 := by positivity
  set W : State 3 → ℝ := fun v => a * v 0 with hW
  have hWd : ∀ v, HasFDerivAt W (a • (EuclideanSpace.proj (0 : Fin 3) : State 3 →L[ℝ] ℝ)) v := by
    intro v
    have h := ((EuclideanSpace.proj (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := v)).const_mul a
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp [hW])
  refine unstable_of_quadMap_chetaev (m := 0) hU hg (zhNormalForm_isLittleO hω hexp)
    (W := W) (ρ := 1) (γ := min (a ^ 2) (a * b)) (C := |a|) (by fun_prop) (by simp [hW])
    one_pos (lt_min ha2 hab) (fun v _ _ => ?_) (fun ε hε => ?_)
  · rw [(hWd v).fderiv]
    refine ⟨?_, ?_⟩
    · simp only [smul_apply, zhL_apply, zhNF_apply, smul_eq_mul, ← ha_def, ← hb_def]
      simp only [EuclideanSpace.proj, zero_add]
      simp
      rw [norm_sq_three]
      have h1 := min_le_left (a ^ 2) (a * b)
      have h2 := min_le_right (a ^ 2) (a * b)
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    · rw [pow_zero, mul_one]
      refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a) fun x => ?_
      simpa [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_left (abs_apply_le_norm x 0) (abs_nonneg a)
  · set t := ε / (2 * (|a| + 1)) with ht
    have ht0 : 0 < t := by positivity
    refine ⟨mk3 (a * t) 0 0, ?_, ?_⟩
    · have hn : ‖mk3 (a * t) 0 0‖ ^ 2 = (|a| * t) ^ 2 := by
        rw [norm_sq_three]; simp [mul_pow, sq_abs]
      refine lt_of_pow_lt_pow_left₀ 2 hε.le (hn.trans_lt ?_)
      have h1 : |a| * t < ε := by
        have : |a| * t ≤ (|a| + 1) * t := by nlinarith
        have h2 : (|a| + 1) * t = ε / 2 := by rw [ht]; field_simp
        linarith
      exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    · simp only [hW, mk3_zero]
      nlinarith

/-- The seed `(t, 0, 0)` has norm `|t|`. -/
@[tmio T, powerlib_foundation] private theorem norm_mk3_axis (t : ℝ) : ‖mk3 t 0 0‖ = |t| := by
  have h : ‖mk3 t 0 0‖ ^ 2 = |t| ^ 2 := by rw [norm_sq_three]; simp [sq_abs]
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg t) two_ne_zero).mp h

/-- The cone estimate on the escaping half axis: for `a u > 0`, `r² < k u²` (`0 < k ≤ 1/2`,
`μ ≤ a²`, `μ + k|ab| ≤ a(a − c)`), `2u(k a u² + (k b − c) r²) ≥ (kμ/(4|a|)) ‖v‖³`. -/
@[tmio T, powerlib_foundation] private theorem cone_lower {a b c k μ : ℝ} {v : State 3}
    (haa : 0 < |a|) (hk0 : 0 < k) (hk1 : k ≤ 1 / 2) (hμ0 : 0 < μ) (hμa : μ ≤ a ^ 2)
    (hμδ : μ + k * |a * b| ≤ a * (a - c)) (hav : 0 < a * v 0)
    (hcone : v 1 ^ 2 + v 2 ^ 2 < k * v 0 ^ 2) :
    k * μ / (4 * |a|) * ‖v‖ ^ (1 + 2) ≤
      2 * (v 0 * (k * a * v 0 ^ 2 + (k * b - c) * (v 1 ^ 2 + v 2 ^ 2))) := by
  set r2 := v 1 ^ 2 + v 2 ^ 2 with hr2
  set X := k * a * v 0 ^ 2 + (k * b - c) * r2 with hX
  have hr0 : 0 ≤ r2 := by positivity
  have hu2 : 0 ≤ v 0 ^ 2 := sq_nonneg _
  have hku : 0 ≤ k * v 0 ^ 2 := by positivity
  have haX : k * v 0 ^ 2 * μ ≤ a * X := by
    have e : a * X = k * v 0 ^ 2 * a ^ 2 + (k * (a * b) - a * c) * r2 := by rw [hX]; ring
    rw [e]
    rcases le_total 0 (k * (a * b) - a * c) with h | h
    · have h1 : k * v 0 ^ 2 * μ ≤ k * v 0 ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left hμa hku
      have h2 : 0 ≤ (k * (a * b) - a * c) * r2 := mul_nonneg h hr0
      linarith
    · have h1 : (k * (a * b) - a * c) * (k * v 0 ^ 2) ≤ (k * (a * b) - a * c) * r2 :=
        mul_le_mul_of_nonpos_left hcone.le h
      have h2 : -(k * |a * b|) ≤ k * (a * b) := by
        have h6 := mul_le_mul_of_nonneg_left (neg_abs_le (a * b)) hk0.le
        linarith
      have h3 : μ ≤ a ^ 2 + k * (a * b) - a * c := by nlinarith
      have h4 : k * v 0 ^ 2 * μ ≤ k * v 0 ^ 2 * (a ^ 2 + k * (a * b) - a * c) :=
        mul_le_mul_of_nonneg_left h3 hku
      have e2 : k * v 0 ^ 2 * (a ^ 2 + k * (a * b) - a * c) =
          k * v 0 ^ 2 * a ^ 2 + (k * (a * b) - a * c) * (k * v 0 ^ 2) := by ring
      linarith
  have hv0 : |a| * |v 0| = a * v 0 := by rw [← abs_mul, abs_of_pos hav]
  have hu3 : k * μ * |v 0| ^ 3 / |a| ≤ v 0 * X := by
    have e1 : v 0 * X * a ^ 2 = (a * v 0) * (a * X) := by ring
    have e2 : (a * v 0) * (k * v 0 ^ 2 * μ) = k * μ * |v 0| ^ 3 * |a| := by
      rw [← hv0, ← sq_abs (v 0)]; ring
    have h1 : (a * v 0) * (k * v 0 ^ 2 * μ) ≤ (a * v 0) * (a * X) :=
      mul_le_mul_of_nonneg_left haX hav.le
    rw [div_le_iff₀ haa]
    have ha2' : a ^ 2 = |a| * |a| := by rw [← sq_abs a]; ring
    have h2 : (k * μ * |v 0| ^ 3) * |a| ≤ (v 0 * X * |a|) * |a| := by
      have e3 : (v 0 * X * |a|) * |a| = v 0 * X * a ^ 2 := by rw [ha2']; ring
      rw [e3, e1, ← e2]
      exact h1
    exact le_of_mul_le_mul_right h2 haa
  have hn : ‖v‖ ≤ 2 * |v 0| := by
    refine norm_le_of_sq_le (by positivity) ?_
    rw [norm_sq_three, mul_pow, sq_abs]
    have : k * v 0 ^ 2 ≤ 1 / 2 * v 0 ^ 2 := mul_le_mul_of_nonneg_right hk1 hu2
    linarith
  have hn3 : ‖v‖ ^ (1 + 2) ≤ 8 * |v 0| ^ 3 := by
    calc ‖v‖ ^ (1 + 2) ≤ (2 * |v 0|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hn 3
      _ = 8 * |v 0| ^ 3 := by ring
  have hc0 : 0 ≤ k * μ / (4 * |a|) := by positivity
  calc k * μ / (4 * |a|) * ‖v‖ ^ (1 + 2) ≤ k * μ / (4 * |a|) * (8 * |v 0| ^ 3) :=
        mul_le_mul_of_nonneg_left hn3 hc0
    _ = 2 * (k * μ * |v 0| ^ 3 / |a|) := by field_simp; ring
    _ ≤ 2 * (v 0 * X) := by linarith

/-- The derivative of the cone function `k u² − r²` is bounded by `5 ‖v‖` (`0 < k ≤ 1/2`). -/
@[tmio T, powerlib_foundation] private theorem norm_cone_deriv_le {k : ℝ} {v : State 3}
    (hk0 : 0 < k) (hk1 : k ≤ 1 / 2) {ℓ : State 3 →L[ℝ] ℝ}
    (hℓ : ∀ h, ℓ h = 2 * k * v 0 * h 0 - 2 * v 1 * h 1 - 2 * v 2 * h 2) :
    ‖ℓ‖ ≤ 5 * ‖v‖ ^ 1 := by
  rw [pow_one]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [hℓ, Real.norm_eq_abs]
  have e0 := abs_apply_le_norm v 0
  have e1 := abs_apply_le_norm v 1
  have e2 := abs_apply_le_norm v 2
  have f0 := abs_apply_le_norm h 0
  have f1 := abs_apply_le_norm h 1
  have f2 := abs_apply_le_norm h 2
  have hvh : 0 ≤ ‖v‖ * ‖h‖ := mul_nonneg (norm_nonneg v) (norm_nonneg h)
  have g0 : |v 0| * |h 0| ≤ ‖v‖ * ‖h‖ := mul_le_mul e0 f0 (abs_nonneg _) (norm_nonneg _)
  have g1 : |v 1| * |h 1| ≤ ‖v‖ * ‖h‖ := mul_le_mul e1 f1 (abs_nonneg _) (norm_nonneg _)
  have g2 : |v 2| * |h 2| ≤ ‖v‖ * ‖h‖ := mul_le_mul e2 f2 (abs_nonneg _) (norm_nonneg _)
  have habs : |2 * k * v 0 * h 0 - 2 * v 1 * h 1 - 2 * v 2 * h 2| ≤
      2 * k * (|v 0| * |h 0|) + 2 * (|v 1| * |h 1|) + 2 * (|v 2| * |h 2|) := by
    have t1 := abs_sub (2 * k * v 0 * h 0 - 2 * v 1 * h 1) (2 * v 2 * h 2)
    have t2 := abs_sub (2 * k * v 0 * h 0) (2 * v 1 * h 1)
    have q0 : |2 * k * v 0 * h 0| = 2 * k * (|v 0| * |h 0|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hk0]; ring
    have q1 : |2 * v 1 * h 1| = 2 * (|v 1| * |h 1|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    have q2 : |2 * v 2 * h 2| = 2 * (|v 2| * |h 2|) := by
      rw [abs_mul, abs_mul, abs_two]; ring
    linarith
  have hk' : 2 * k * (|v 0| * |h 0|) ≤ 2 * k * (‖v‖ * ‖h‖) :=
    mul_le_mul_of_nonneg_left g0 (by positivity)
  have hk'' : 2 * k * (‖v‖ * ‖h‖) ≤ ‖v‖ * ‖h‖ := by
    have := mul_le_mul_of_nonneg_right hk1 hvh
    linarith
  linarith

/-- The cone function `k u² − r² − M (min(a u, 0))²` is `C¹`. -/
@[tmio T, powerlib_foundation] private theorem contDiff_coneW (k M a : ℝ) :
    ContDiff ℝ 1 (fun v : State 3 => k * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2) - M * minSq (a * v 0)) :=
  ((contDiff_const.mul ((EuclideanSpace.proj (0 : Fin 3)).contDiff.pow 2)).sub
    (((EuclideanSpace.proj (1 : Fin 3)).contDiff.pow 2).add
      ((EuclideanSpace.proj (2 : Fin 3)).contDiff.pow 2))).sub
    (contDiff_const.mul (contDiff_minSq.comp
      (contDiff_const.mul (EuclideanSpace.proj (0 : Fin 3)).contDiff)))

/-- On the side `a u > 0` the cone function has the derivative of `k u² − r²`. -/
@[tmio T, powerlib_foundation] private theorem fderiv_coneW_apply {k M a : ℝ} {v : State 3}
    (hav : 0 < a * v 0) (h : State 3) :
    fderiv ℝ (fun v : State 3 => k * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2) - M * minSq (a * v 0)) v h =
      2 * k * v 0 * h 0 - 2 * v 1 * h 1 - 2 * v 2 * h 2 := by
  have hc : ∀ i : Fin 3, HasFDerivAt (fun x : State 3 => x i)
      (EuclideanSpace.proj i : State 3 →L[ℝ] ℝ) v := fun i =>
    (EuclideanSpace.proj i : State 3 →L[ℝ] ℝ).hasFDerivAt
  have hd : HasFDerivAt (fun v : State 3 => k * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2)) _ v :=
    (((hc 0).pow 2).const_mul k).sub (((hc 1).pow 2).add ((hc 2).pow 2))
  have hev : (fun v : State 3 => k * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2) - M * minSq (a * v 0)) =ᶠ[𝓝 v]
      fun v : State 3 => k * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2) := by
    have ho : IsOpen {x : State 3 | 0 < a * x 0} :=
      isOpen_lt continuous_const (continuous_const.mul (EuclideanSpace.proj 0).continuous)
    filter_upwards [ho.mem_nhds hav] with x hx
    simp only [minSq_of_pos hx, mul_zero, sub_zero]
  rw [hev.fderiv_eq, hd.fderiv]
  simp
  ring

/-- **Zero–Hopf instability, `a(a − c) > 0`.** If `g(w) = Lw + G(w, w) + o(‖w‖²)` on `ℝ³`
(`L = zhL ω`, `ω ≠ 0`), `g` is Lipschitz near `0` and `a(a − c) > 0` for the coefficients
`a, c` of `G`, then `0` is unstable: on the normal form the half axis `a u > 0`, where
`u̇ = a u²` escapes, attracts the cone `r² < k u²`, and
`W = k u² − r² − M (min(a u, 0))²` (`M a² = k + 1`) has `Ẇ = 2u(k a u² + (k b − c) r²)` there. -/
@[tmio T, powerlib_foundation] theorem unstable_of_zhCoeff_sub_pos (hω : ω ≠ 0)
    (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    (hexp : (fun w => g w - (zhL ω w + G w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2)
    (hac : 0 < zhCoeffA G * (zhCoeffA G - zhCoeffC G)) : Unstable g 0 := by
  set a := zhCoeffA G with ha_def
  set b := zhCoeffB G with hb_def
  set c := zhCoeffC G with hc_def
  clear_value a b c
  have ha : a ≠ 0 := left_ne_zero_of_mul hac.ne'
  have haa : 0 < |a| := abs_pos.mpr ha
  obtain ⟨k, hk0, hk1, hkab⟩ : ∃ k : ℝ, 0 < k ∧ k ≤ 1 / 2 ∧ k * |a * b| ≤ a * (a - c) / 2 := by
    refine ⟨a * (a - c) / (2 * (|a * b| + a * (a - c))), by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (a * b)]
    · rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg (a * b), mul_nonneg (abs_nonneg (a * b)) hac.le]
  obtain ⟨μ, hμ0, hμa, hμδ⟩ : ∃ μ : ℝ, 0 < μ ∧ μ ≤ a ^ 2 ∧ μ + k * |a * b| ≤ a * (a - c) :=
    ⟨min (a ^ 2) (a * (a - c) / 2), lt_min (by positivity) (by positivity), min_le_left _ _,
      by linarith [min_le_right (a ^ 2) (a * (a - c) / 2)]⟩
  obtain ⟨M, hMa⟩ : ∃ M : ℝ, M * a ^ 2 = k + 1 := ⟨(k + 1) / a ^ 2, by field_simp⟩
  have hreg : ∀ v : State 3, 0 < k * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2) - M * minSq (a * v 0) →
      0 < a * v 0 ∧ v 1 ^ 2 + v 2 ^ 2 < k * v 0 ^ 2 := by
    intro v hv
    by_cases h : 0 < a * v 0
    · refine ⟨h, ?_⟩
      rw [minSq_of_pos h, mul_zero, sub_zero] at hv
      linarith
    · exfalso
      rw [minSq_of_nonpos (not_lt.mp h)] at hv
      have : M * (a * v 0) ^ 2 = (k + 1) * v 0 ^ 2 := by rw [mul_pow, ← mul_assoc, hMa]
      nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 0)]
  refine unstable_of_quadMap_chetaev (m := 1) hU hg (zhNormalForm_isLittleO hω hexp)
    (W := fun v : State 3 => k * v 0 ^ 2 - (v 1 ^ 2 + v 2 ^ 2) - M * minSq (a * v 0)) (ρ := 1)
    (γ := k * μ / (4 * |a|)) (C := 5) (contDiff_coneW k M a) (by simp [minSq]) one_pos
    (by positivity) (fun v _ hv => ?_) (fun ε hε => ?_)
  · obtain ⟨hav, hcone⟩ := hreg v hv
    refine ⟨?_, norm_cone_deriv_le hk0 hk1 (fderiv_coneW_apply hav)⟩
    rw [fderiv_coneW_apply hav]
    simp only [PiLp.add_apply, zhL_apply, zhNF_apply, mk3_zero, mk3_one, mk3_two, ← ha_def,
      ← hb_def, ← hc_def]
    refine (cone_lower haa hk0 hk1 hμ0 hμa hμδ hav hcone).trans (le_of_eq ?_)
    ring
  · set t := ε / (2 * (|a| + 1)) with ht
    have ht0 : 0 < t := by positivity
    refine ⟨mk3 (a * t) 0 0, ?_, ?_⟩
    · rw [norm_mk3_axis, abs_mul, abs_of_pos ht0]
      have : |a| * t ≤ (|a| + 1) * t := by nlinarith
      have h2 : (|a| + 1) * t = ε / 2 := by rw [ht]; field_simp
      linarith
    · have hpos : 0 < a * (a * t) := by nlinarith [sq_pos_of_ne_zero ha]
      simp only [mk3_zero, mk3_one, mk3_two, minSq_of_pos hpos]
      have h1 : 0 < (a * t) ^ 2 := by positivity
      nlinarith

/-- The ray estimate of the invariant cone `r² = κ u²` (`a = 0`): for `b u > 0` and
`(r² − κ u²)² < α u⁴`, `α = κ²/4`, `4α b u³ r² ≥ (2ακ|b|/(1 + 2κ)⁵) ‖v‖⁵`. -/
@[tmio T, powerlib_foundation] private theorem ray_lower {b κ α : ℝ} {v : State 3}
    (hκ : 0 < κ) (hα : α = κ ^ 2 / 4) (hbv : 0 < b * v 0)
    (hξ : (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 < α * v 0 ^ 4) :
    2 * α * κ * |b| / (1 + 2 * κ) ^ 5 * ‖v‖ ^ (3 + 2) ≤
      4 * α * b * v 0 ^ 3 * (v 1 ^ 2 + v 2 ^ 2) := by
  set r2 := v 1 ^ 2 + v 2 ^ 2 with hr2
  set ξ := r2 - κ * v 0 ^ 2 with hξdef
  have hu2 : 0 ≤ v 0 ^ 2 := sq_nonneg _
  have hab : |ξ| < κ / 2 * v 0 ^ 2 := by
    refine abs_lt_of_sq_lt_sq ?_ (by positivity)
    calc ξ ^ 2 < α * v 0 ^ 4 := hξ
      _ = (κ / 2 * v 0 ^ 2) ^ 2 := by rw [hα]; ring
  have hr_lo : κ / 2 * v 0 ^ 2 ≤ r2 := by
    have := neg_abs_le ξ
    have e : r2 = ξ + κ * v 0 ^ 2 := by rw [hξdef]; ring
    linarith
  have hr_hi : r2 ≤ 3 * κ / 2 * v 0 ^ 2 := by
    have := le_abs_self ξ
    have e : r2 = ξ + κ * v 0 ^ 2 := by rw [hξdef]; ring
    linarith
  have hbv' : |b| * |v 0| = b * v 0 := by rw [← abs_mul, abs_of_pos hbv]
  have hα0 : 0 < α := by rw [hα]; positivity
  have hmain : 2 * α * κ * |b| * |v 0| ^ 5 ≤ 4 * α * b * v 0 ^ 3 * r2 := by
    have e : 4 * α * b * v 0 ^ 3 * r2 = 4 * α * (|b| * |v 0|) * |v 0| ^ 2 * r2 := by
      rw [hbv', sq_abs]; ring
    rw [e]
    have h1 : 0 ≤ 4 * α * (|b| * |v 0|) * |v 0| ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hr_lo h1
    have e2 : 4 * α * (|b| * |v 0|) * |v 0| ^ 2 * (κ / 2 * v 0 ^ 2) =
        2 * α * κ * |b| * |v 0| ^ 5 := by rw [← sq_abs (v 0)]; ring
    linarith
  have hn : ‖v‖ ≤ (1 + 2 * κ) * |v 0| := by
    refine norm_le_of_sq_le (by positivity) ?_
    rw [norm_sq_three, mul_pow, sq_abs]
    have : 1 + 3 * κ / 2 ≤ (1 + 2 * κ) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right this hu2
    have e : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = v 0 ^ 2 + r2 := by rw [hr2]; ring
    rw [e]
    nlinarith
  have hn5 : ‖v‖ ^ (3 + 2) ≤ (1 + 2 * κ) ^ 5 * |v 0| ^ 5 := by
    calc ‖v‖ ^ (3 + 2) ≤ ((1 + 2 * κ) * |v 0|) ^ 5 := pow_le_pow_left₀ (norm_nonneg _) hn 5
      _ = (1 + 2 * κ) ^ 5 * |v 0| ^ 5 := by ring
  have hc0 : 0 ≤ 2 * α * κ * |b| / (1 + 2 * κ) ^ 5 := by positivity
  calc 2 * α * κ * |b| / (1 + 2 * κ) ^ 5 * ‖v‖ ^ (3 + 2) ≤
        2 * α * κ * |b| / (1 + 2 * κ) ^ 5 * ((1 + 2 * κ) ^ 5 * |v 0| ^ 5) :=
        mul_le_mul_of_nonneg_left hn5 hc0
    _ = 2 * α * κ * |b| * |v 0| ^ 5 := by field_simp
    _ ≤ _ := hmain

/-- The derivative of the ray function is bounded by `(4α + 2κ² + 4κ) ‖v‖³` where
`|r² − κ u²| ≤ (κ/2) u²`. -/
@[tmio T, powerlib_foundation] private theorem norm_ray_deriv_le {κ α : ℝ} {v : State 3}
    (hκ : 0 < κ) (hα : 0 < α)
    (hξ : |v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2| ≤ κ / 2 * v 0 ^ 2) {ℓ : State 3 →L[ℝ] ℝ}
    (hℓ : ∀ h, ℓ h = (4 * α * v 0 ^ 3 + 4 * κ * v 0 * (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2)) * h 0 -
      4 * (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) * v 1 * h 1 -
      4 * (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) * v 2 * h 2) :
    ‖ℓ‖ ≤ (4 * α + 2 * κ ^ 2 + 4 * κ) * ‖v‖ ^ 3 := by
  set ξ := v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2 with hξdef
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [hℓ, Real.norm_eq_abs]
  have e0 := abs_apply_le_norm v 0
  have e1 := abs_apply_le_norm v 1
  have e2 := abs_apply_le_norm v 2
  have f0 := abs_apply_le_norm h 0
  have f1 := abs_apply_le_norm h 1
  have f2 := abs_apply_le_norm h 2
  have hn0 := norm_nonneg v
  have hh0 := norm_nonneg h
  have hu2 : v 0 ^ 2 ≤ ‖v‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e0 2
  have hξn : |ξ| ≤ κ / 2 * ‖v‖ ^ 2 := hξ.trans (by gcongr)
  have hu3 : |v 0| ^ 3 ≤ ‖v‖ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) e0 3
  have t1 : |(4 * α * v 0 ^ 3 + 4 * κ * v 0 * ξ) * h 0| ≤
      (4 * α + 2 * κ ^ 2) * ‖v‖ ^ 3 * ‖h‖ := by
    rw [abs_mul]
    have : |4 * α * v 0 ^ 3 + 4 * κ * v 0 * ξ| ≤ (4 * α + 2 * κ ^ 2) * ‖v‖ ^ 3 := by
      refine (abs_add_le _ _).trans ?_
      have q1 : |4 * α * v 0 ^ 3| = 4 * α * |v 0| ^ 3 := by
        rw [abs_mul, abs_mul, abs_of_pos hα, abs_pow]; norm_num
      have q2 : |4 * κ * v 0 * ξ| = 4 * κ * |v 0| * |ξ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hκ]; norm_num
      rw [q1, q2]
      have g1 : 4 * α * |v 0| ^ 3 ≤ 4 * α * ‖v‖ ^ 3 := by gcongr
      have g2 : 4 * κ * |v 0| * |ξ| ≤ 4 * κ * ‖v‖ * (κ / 2 * ‖v‖ ^ 2) := by gcongr
      nlinarith
    exact mul_le_mul this f0 (abs_nonneg _) (by positivity)
  have t2 : |4 * ξ * v 1 * h 1| ≤ 2 * κ * ‖v‖ ^ 3 * ‖h‖ := by
    rw [abs_mul, abs_mul, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
    have : 4 * |ξ| * |v 1| * |h 1| ≤ 4 * (κ / 2 * ‖v‖ ^ 2) * ‖v‖ * ‖h‖ := by gcongr
    nlinarith
  have t3 : |4 * ξ * v 2 * h 2| ≤ 2 * κ * ‖v‖ ^ 3 * ‖h‖ := by
    rw [abs_mul, abs_mul, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
    have : 4 * |ξ| * |v 2| * |h 2| ≤ 4 * (κ / 2 * ‖v‖ ^ 2) * ‖v‖ * ‖h‖ := by gcongr
    nlinarith
  have hs := abs_sub ((4 * α * v 0 ^ 3 + 4 * κ * v 0 * ξ) * h 0 - 4 * ξ * v 1 * h 1)
    (4 * ξ * v 2 * h 2)
  have hs2 := abs_sub ((4 * α * v 0 ^ 3 + 4 * κ * v 0 * ξ) * h 0) (4 * ξ * v 1 * h 1)
  nlinarith

/-- The ray function `α u⁴ − (r² − κ u²)² − M (min(b u, 0))⁴` is `C¹`. -/
@[tmio T, powerlib_foundation] private theorem contDiff_rayW (α κ M b : ℝ) :
    ContDiff ℝ 1 (fun v : State 3 => α * v 0 ^ 4 - (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 -
      M * minSq (b * v 0) ^ 2) := by
  have hp : ∀ i : Fin 3, ContDiff ℝ 1 (fun v : State 3 => v i) := fun i =>
    (EuclideanSpace.proj i : State 3 →L[ℝ] ℝ).contDiff
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have hξ : ContDiff ℝ 1 (fun v : State 3 => v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) :=
    ((h1.pow 2).add (h2.pow 2)).sub (contDiff_const.mul (h0.pow 2))
  have hm : ContDiff ℝ 1 (fun v : State 3 => minSq (b * v 0)) :=
    contDiff_minSq.comp (contDiff_const.mul h0)
  exact ((contDiff_const.mul (h0.pow 4)).sub (hξ.pow 2)).sub (contDiff_const.mul (hm.pow 2))

/-- On the side `b u > 0` the ray function has the derivative of `α u⁴ − (r² − κ u²)²`. -/
@[tmio T, powerlib_foundation] private theorem fderiv_rayW_apply {α κ M b : ℝ} {v : State 3}
    (hbv : 0 < b * v 0) (h : State 3) :
    fderiv ℝ (fun v : State 3 => α * v 0 ^ 4 - (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 -
      M * minSq (b * v 0) ^ 2) v h =
      (4 * α * v 0 ^ 3 + 4 * κ * v 0 * (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2)) * h 0 -
        4 * (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) * v 1 * h 1 -
        4 * (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) * v 2 * h 2 := by
  have hc : ∀ i : Fin 3, HasFDerivAt (fun x : State 3 => x i)
      (EuclideanSpace.proj i : State 3 →L[ℝ] ℝ) v := fun i =>
    (EuclideanSpace.proj i : State 3 →L[ℝ] ℝ).hasFDerivAt
  have hd : HasFDerivAt
      (fun v : State 3 => α * v 0 ^ 4 - (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2) _ v :=
    (((hc 0).pow 4).const_mul α).sub
      (((((hc 1).pow 2).add ((hc 2).pow 2)).sub (((hc 0).pow 2).const_mul κ)).pow 2)
  have hev : (fun v : State 3 => α * v 0 ^ 4 - (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 -
      M * minSq (b * v 0) ^ 2) =ᶠ[𝓝 v]
      fun v : State 3 => α * v 0 ^ 4 - (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 := by
    have ho : IsOpen {x : State 3 | 0 < b * x 0} :=
      isOpen_lt continuous_const (continuous_const.mul (EuclideanSpace.proj 0).continuous)
    filter_upwards [ho.mem_nhds hbv] with x hx
    simp only [minSq_of_pos hx]
    ring
  rw [hev.fderiv_eq, hd.fderiv]
  simp
  ring

/-- **Zero–Hopf instability, `a = 0`, `bc > 0`.** If `g(w) = Lw + G(w, w) + o(‖w‖²)` on `ℝ³`
(`L = zhL ω`, `ω ≠ 0`), `g` is Lipschitz near `0`, `a = 0` and `b c > 0` for the coefficients
of `G`, then `0` is unstable: on the normal form the cone `r² = κ u²` (`κ = c/b`) is invariant
on the side `b u > 0`, where `u̇ = b r² > 0`, and `W = α u⁴ − (r² − κ u²)² − M (min(b u, 0))⁴`
(`α = κ²/4`, `M b⁴ = α + 1`) has `Ẇ = 4α b u³ r²` there. -/
@[tmio T, powerlib_foundation] theorem unstable_of_zhCoeff_zero (hω : ω ≠ 0)
    (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    (hexp : (fun w => g w - (zhL ω w + G w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2)
    (ha0 : zhCoeffA G = 0) (hbc : 0 < zhCoeffB G * zhCoeffC G) : Unstable g 0 := by
  set b := zhCoeffB G with hb_def
  set c := zhCoeffC G with hc_def
  clear_value b c
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc.ne'
  have hb2 : 0 < b ^ 2 := by positivity
  obtain ⟨κ, hκ, hκb⟩ : ∃ κ : ℝ, 0 < κ ∧ κ * b = c :=
    ⟨c / b, by
      have : c / b = b * c / b ^ 2 := by field_simp
      rw [this]; positivity, by field_simp⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = κ ^ 2 / 4 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨M, hMb⟩ : ∃ M : ℝ, M * b ^ 4 = α + 1 := ⟨(α + 1) / b ^ 4, by field_simp⟩
  have hreg : ∀ v : State 3, 0 < α * v 0 ^ 4 - (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 -
      M * minSq (b * v 0) ^ 2 →
      0 < b * v 0 ∧ (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 < α * v 0 ^ 4 := by
    intro v hv
    by_cases h : 0 < b * v 0
    · refine ⟨h, ?_⟩
      rw [minSq_of_pos h] at hv
      linarith
    · exfalso
      rw [minSq_of_nonpos (not_lt.mp h)] at hv
      have : M * ((b * v 0) ^ 2) ^ 2 = (α + 1) * v 0 ^ 4 := by
        rw [← hMb]; ring
      have h4 : 0 ≤ v 0 ^ 4 := by positivity
      nlinarith [sq_nonneg (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2)]
  refine unstable_of_quadMap_chetaev (m := 3) hU hg (zhNormalForm_isLittleO hω hexp)
    (W := fun v : State 3 => α * v 0 ^ 4 - (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 -
      M * minSq (b * v 0) ^ 2) (ρ := 1)
    (γ := 2 * α * κ * |b| / (1 + 2 * κ) ^ 5) (C := 4 * α + 2 * κ ^ 2 + 4 * κ)
    (contDiff_rayW α κ M b) (by simp [minSq]) one_pos (by positivity) (fun v _ hv => ?_)
    (fun ε hε => ?_)
  · obtain ⟨hbv, hξ⟩ := hreg v hv
    have hξ' : |v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2| ≤ κ / 2 * v 0 ^ 2 := by
      refine (abs_lt_of_sq_lt_sq ?_ (by positivity)).le
      calc (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) ^ 2 < α * v 0 ^ 4 := hξ
        _ = (κ / 2 * v 0 ^ 2) ^ 2 := by rw [hα]; ring
    refine ⟨?_, norm_ray_deriv_le hκ hα0 hξ' (fderiv_rayW_apply hbv)⟩
    rw [fderiv_rayW_apply hbv]
    simp only [PiLp.add_apply, zhL_apply, zhNF_apply, mk3_zero, mk3_one, mk3_two, ha0,
      ← hb_def, ← hc_def]
    refine (ray_lower hκ hα hbv hξ).trans (le_of_eq ?_)
    linear_combination (-4 * v 0 * (v 1 ^ 2 + v 2 ^ 2 - κ * v 0 ^ 2) *
      (v 1 ^ 2 + v 2 ^ 2)) * hκb
  · set t := ε / (2 * (|b| * (1 + κ) + 1)) with ht
    have ht0 : 0 < t := by positivity
    have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
    refine ⟨mk3 (b * t) (b * t * Real.sqrt κ) 0, ?_, ?_⟩
    · have hn : ‖mk3 (b * t) (b * t * Real.sqrt κ) 0‖ ≤ |b| * t * (1 + κ) := by
        refine norm_le_of_sq_le (by positivity) ?_
        rw [norm_sq_three]
        simp only [mk3_zero, mk3_one, mk3_two]
        rw [mul_pow (b * t) (Real.sqrt κ), hsq, mul_pow (|b| * t), mul_pow |b|, sq_abs,
          ← mul_pow]
        have h1 : (b * t) ^ 2 * (1 + κ) ≤ (b * t) ^ 2 * (1 + κ) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
        nlinarith
      refine hn.trans_lt ?_
      have : |b| * t * (1 + κ) ≤ (|b| * (1 + κ) + 1) * t := by nlinarith
      have h2 : (|b| * (1 + κ) + 1) * t = ε / 2 := by rw [ht]; field_simp
      linarith
    · have hpos : 0 < b * (b * t) := by nlinarith
      simp only [mk3_zero, mk3_one, mk3_two, minSq_of_pos hpos]
      have e : (b * t * Real.sqrt κ) ^ 2 + 0 ^ 2 - κ * (b * t) ^ 2 = 0 := by
        rw [mul_pow (b * t), hsq]; ring
      rw [e]
      have h1 : 0 < (b * t) ^ 4 := by positivity
      nlinarith

/-- The zero–Hopf coefficients decided by the Chetaev functions of the normal form: `ab > 0`,
or `a(a − c) > 0`, or `a = 0` and `bc > 0`. -/
def ZeroHopfDecided (a b c : ℝ) : Prop := 0 < a * b ∨ 0 < a * (a - c) ∨ (a = 0 ∧ 0 < b * c)

/-- **Zero–Hopf instability in the decided regimes.** If `g(w) = Lw + G(w, w) + o(‖w‖²)` on
`ℝ³` (`L = zhL ω`, `ω ≠ 0`), `g` is Lipschitz near `0` and the coefficients of `G` satisfy
`ZeroHopfDecided a b c`, then `0` is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_zeroHopfDecided (hω : ω ≠ 0)
    (hU : U ∈ 𝓝 0) (hg : LipschitzOnWith K g U)
    (hexp : (fun w => g w - (zhL ω w + G w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2)
    (hdec : ZeroHopfDecided (zhCoeffA G) (zhCoeffB G) (zhCoeffC G)) : Unstable g 0 := by
  rcases hdec with h | h | ⟨h0, h⟩
  · exact unstable_of_zhCoeff_mul_pos hω hU hg hexp h
  · exact unstable_of_zhCoeff_sub_pos hω hU hg hexp h
  · exact unstable_of_zhCoeff_zero hω hU hg hexp h0 h

end ZeroHopfChetaev

end powerlib.Dynamics.CenterManifold
