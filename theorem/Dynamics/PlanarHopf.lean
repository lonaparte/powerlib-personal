import theorem.Dynamics.CenterReductionHopf
import theorem.Dynamics.PlanarReturn
import theorem.Dynamics.Degenerate.PlanarFocus2

/-! # Hopf cycles of a planar family

The cycle half of the Hopf theorem for a planar family `u̇ = g(μ, u)` known only through its
unfolded cubic expansion `g(μ, u) = R u + μ M u + Q(u, u) + C(u, u, u) + o(‖u‖³)`, uniformly for
`|μ| ≤ K‖u‖²` (`R = rotL ω`): if `tr M ≠ 0` and `l₁ ≠ 0`, then for small `μ` with
`μ · tr M · l₁ < 0` there is a nonconstant periodic orbit with `‖γ‖² ≍ |μ|`.

Scope.
* A family of autonomous planar ODEs `u̇ = g(μ, u)` on `State 2 = EuclideanSpace ℝ (Fin 2)`,
  `μ ∈ ℝ` constant; no input, delay or time variation. The data: the rotation `rotL ω`
  (`ω > 0`; the linear part at `μ = 0` in rotation coordinates), a linear map `M` (the
  parameter derivative of the linear part), a bilinear `Q` and a trilinear `C` (as in
  `theorem/Dynamics/Degenerate/PlanarFocus.lean`). The remainder `unfoldRem` is assumed
  `o(‖u‖³)` along `nhdsW K` (`(μ, u) → 0`, `|μ| ≤ K‖u‖²`) for every `K`: the parameter
  has weight two, so `μ²`, `μ‖u‖²` and `μ²‖u‖` terms are part of the remainder. Each `g μ` is
  Lipschitz on a fixed disc for `|μ|` small (as a reduced field of a centre manifold is).
* Periodic orbits are written out as in `theorem/Dynamics/PlanarReturn.lean`. Existence with
  amplitude bounds is proved from the expansion along `nhdsW K`; when the remainder is
  `o(|μ| ‖u‖ + ‖u‖³)` on a full neighbourhood of `0`, also the absence of small cycles for
  `μ tr M l₁ ≥ 0` and the amplitude `(1 + o(1)) ν` of every small cycle. Uniqueness and stability
  of the cycle are not proved (they need derivative bounds on the remainder).
* Generic foundation, independent of any model; no model family is defined.

Source: Guckenheimer–Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of
Vector Fields* (1983), §3.4 (Theorem 3.4.2 and the computation of `a`, `d`); Kuznetsov,
*Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Lemma 3.2, Theorem 3.3);
Marsden–McCracken, *The Hopf Bifurcation and Its Applications* (1976), §3. The polynomial
identity of the unfolded Lyapunov function was derived with SymPy (untrusted) and is checked by
the kernel (`field_simp`, `linear_combination`).

Results.
* `lie_identity_unfold`: along `ẋ = −ωy + μ(ax + by) + F₂ + F₃ + D₀`,
  `ẏ = ωx + μ(cx + dy) + G₂ + G₃ + D₁`, the polynomial `V + μW` (`V` of `PlanarFocus`,
  `W = ((d − a)/ω) xy − ((b + c)/ω) y²`) has
  `V̇ = μ(a + d)(x² + y²) + ω l₁ (x² + y²)²` plus products of weight at least five plus `D`
  against the gradient.
* `hopfV` (`V + μW`), `fderiv_hopfV`, `hopfV_axis`; `field_apply_zero`, `field_apply_one`
  (the family in coordinates); `paramTrace` (`tr M`), `m00`, `m01`, `m10`, `m11`.
* `nhdsW`, `isLittleO_angNum` (`u₀g₁ − u₁g₀ − ω‖u‖² = o(‖u‖²)`), `isLittleO_radNum`
  (`u₀g₀ + u₁g₁ = o(‖u‖²)`), `isLittleO_lie` (`V̇ − μ tr M ‖u‖² − ω l₁ ‖u‖⁴ = o(‖u‖⁴)`),
  `exists_bound_of_isLittleO`.
* `exists_strictMonoOn_quartic`, `inner_sign`, `outer_sign`, `band_lo`, `band_hi`,
  `band_lo_sq`, `band_hi_sq`: elementary inequalities of the annulus argument.
* `exists_periodicOrbit`: for every small `μ` with `μ tr M l₁ < 0` a nonconstant periodic orbit
  of `g μ`, period at most `4π/ω`, with `ν/8 ≤ ‖γ‖² ≤ 8ν`, `ν = −μ tr M/(ω l₁)` (the annulus
  `ν/8 ≤ ‖u‖² ≤ 8ν`, `PlanarReturn.exists_periodicOrbit_of_annulus`, with `σ = −l₁`).
* `lie_sub_eq` (the identity behind `isLittleO_lie`), `isBigO_poly3_mixed`, `isLittleO_lie_full`
  (`V̇ − μ tr M ‖u‖² − ω l₁ ‖u‖⁴ = o(|μ| ‖u‖² + ‖u‖⁴)` on a full neighbourhood),
  `isLittleO_hopfV_sub` (`V + μW = ‖u‖²(1 + o(1))`).
* `periodic_amplitude`: for every `η > 0` and small `μ`, every periodic orbit in a small disc
  avoiding `0` has `μ tr M l₁ < 0` and `(1 − η) ν ≤ ‖γ(t)‖² ≤ (1 + η) ν` (at the maximum and the
  minimum of `V` along the orbit `V̇ = 0`, which outside the annulus `(1 ± a) ν` is excluded).
-/

noncomputable section
namespace powerlib.Dynamics.PlanarHopf
open Set Filter Topology Asymptotics
open powerlib.Dynamics.Degenerate.PlanarFocus
open powerlib.Dynamics.Degenerate (poly3 dpoly3 poly3_cons poly3_nil dpoly3_cons dpoly3_nil
  contDiff_poly3 hasFDerivAt_poly3 isBigO_poly3_weight)

/-! ## The polynomial identity of the unfolding -/

section Poly

variable (ω a b c d : ℝ)

/-- `μ(a x + b y)`: the parameter term of `ẋ` (third variable `μ`, weight `2`). -/
def mx : List (ℝ × ℕ × ℕ × ℕ) := [(a, 1, 0, 1), (b, 0, 1, 1)]

/-- `μ(c x + d y)`: the parameter term of `ẏ`. -/
def my : List (ℝ × ℕ × ℕ × ℕ) := [(c, 1, 0, 1), (d, 0, 1, 1)]

/-- The correction `W = q x y + r y²`, `q = (d − a)/ω`, `r = −(b + c)/ω`. -/
def wl : List (ℝ × ℕ × ℕ × ℕ) := [((d - a) / ω, 1, 1, 0), (-(b + c) / ω, 0, 2, 0)]

/-- `μ ∂W/∂x = μ q y`. -/
def wx : List (ℝ × ℕ × ℕ × ℕ) := [((d - a) / ω, 0, 1, 1)]

/-- `μ ∂W/∂y = μ (q x + 2 r y)`. -/
def wy : List (ℝ × ℕ × ℕ × ℕ) := [((d - a) / ω, 1, 0, 1), (2 * (-(b + c) / ω), 0, 1, 1)]

variable (J : Jet)

/-- **The homological identity of the unfolding.** Along `ẋ = −ωy + μ(ax + by) + F₂ + F₃ + D₀`,
`ẏ = ωx + μ(cx + dy) + G₂ + G₃ + D₁`, the derivative of `V + μW` is
`μ(a + d)(x² + y²) + ω l₁ (x² + y²)²`, plus products of weight at least five, plus the remainder
`D` against the gradient. -/
@[tmio T, powerlib_foundation] theorem lie_identity_unfold (hω : ω ≠ 0) (x y μ D0 D1 : ℝ) :
    poly3 (J.Vx ω) x y 0 * (-ω * y + poly3 (mx a b ++ J.F2 ++ J.F3) x y μ + D0) +
        poly3 (J.Vy ω) x y 0 * (ω * x + poly3 (my c d ++ J.G2 ++ J.G3) x y μ + D1) +
        μ * dpoly3 (wl ω a b c d) x y 0 (-ω * y + poly3 (mx a b ++ J.F2 ++ J.F3) x y μ + D0)
          (ω * x + poly3 (my c d ++ J.G2 ++ J.G3) x y μ + D1) 0 -
        μ * (a + d) * (x ^ 2 + y ^ 2) - ω * J.l1 ω * (x ^ 2 + y ^ 2) ^ 2 =
      (poly3 (J.V3x ω) x y μ * poly3 J.F3 x y μ + poly3 (J.V3y ω) x y μ * poly3 J.G3 x y μ +
        poly3 (J.V4x ω) x y μ * poly3 (J.F2 ++ J.F3) x y μ +
        poly3 (J.V4y ω) x y μ * poly3 (J.G2 ++ J.G3) x y μ) +
      (poly3 (J.V3x ω ++ J.V4x ω) x y μ * poly3 (mx a b) x y μ +
        poly3 (J.V3y ω ++ J.V4y ω) x y μ * poly3 (my c d) x y μ +
        poly3 (wx ω a d) x y μ * poly3 (mx a b ++ J.F2 ++ J.F3) x y μ +
        poly3 (wy ω a b c d) x y μ * poly3 (my c d ++ J.G2 ++ J.G3) x y μ) +
      ((poly3 (J.Vx ω) x y 0 + poly3 (wx ω a d) x y μ) * D0 +
        (poly3 (J.Vy ω) x y 0 + poly3 (wy ω a b c d) x y μ) * D1) := by
  have hid := J.lie_identity ω hω x y
  rw [Jet.dpoly3_V] at hid
  simp only [Jet.Vx, Jet.Vy, Jet.V3x, Jet.V3y, Jet.V4x, Jet.V4y, Jet.F2, Jet.F3, Jet.G2,
    Jet.G3, mx, my, wl, wx, wy, List.cons_append, List.nil_append, poly3_cons, poly3_nil,
    dpoly3_cons, dpoly3_nil, pow_zero, mul_one, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    pow_one] at hid ⊢
  field_simp
  linear_combination ω * hid

end Poly

/-! ## The unfolding of a planar centre -/

section Field

open powerlib.Dynamics.CenterManifold (rotL rotL_apply0 rotL_apply1 rotL_rotL frameY_rotL)

variable (M : State 2 →L[ℝ] State 2)

/-- The entry `M₀₀ = (M e₀)₀`. -/
def m00 : ℝ := M e0 0
/-- The entry `M₀₁ = (M e₁)₀`. -/
def m01 : ℝ := M e1 0
/-- The entry `M₁₀ = (M e₀)₁`. -/
def m10 : ℝ := M e0 1
/-- The entry `M₁₁ = (M e₁)₁`. -/
def m11 : ℝ := M e1 1

/-- The trace `tr M = M₀₀ + M₁₁` of the parameter derivative of the linear part. -/
def paramTrace : ℝ := m00 M + m11 M

@[tmio T, powerlib_foundation] theorem apply_zero_eq (u : State 2) :
    M u 0 = m00 M * u 0 + m01 M * u 1 := by
  conv_lhs => rw [state2_eq u]
  simp [m00, m01]
  ring

@[tmio T, powerlib_foundation] theorem apply_one_eq (u : State 2) :
    M u 1 = m10 M * u 0 + m11 M * u 1 := by
  conv_lhs => rw [state2_eq u]
  simp [m10, m11]
  ring

variable (Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2)
  (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)) (ω : ℝ)

/-- The remainder `D(μ, u) = g(μ, u) − (Ru + μMu + Q(u, u) + C(u, u, u))` of a planar family
against its unfolded cubic truncation (`R = rotL ω`). -/
def unfoldRem (g : ℝ → State 2 → State 2) (μ : ℝ) (u : State 2) : State 2 :=
  g μ u - (rotL ω u + μ • M u + Q u u + C ![u, u, u])

/-- The Lyapunov function of the unfolding: `V + μW`, `W = q x y + r y²`. -/
def hopfV (μ : ℝ) (u : State 2) : ℝ :=
  lyap (rotL ω) Q C ω u + μ * poly3 (wl ω (m00 M) (m01 M) (m10 M) (m11 M)) (frameX u)
    (frameY (rotL ω) ω u) ((0 : State 2 →L[ℝ] ℝ) u)

variable {M Q C ω}

@[tmio T, powerlib_foundation] theorem field_apply_zero (hω : ω ≠ 0) (g : ℝ → State 2 → State 2)
    (μ : ℝ) (u : State 2) :
    g μ u 0 = -ω * u 1 + poly3 (mx (m00 M) (m01 M) ++ (jet (rotL ω) Q C ω).F2 ++
      (jet (rotL ω) Q C ω).F3) (u 0) (u 1) μ + unfoldRem M Q C ω g μ u 0 := by
  have h : g μ u = rotL ω u + μ • M u + (Q u u + C ![u, u, u]) + unfoldRem M Q C ω g μ u := by
    simp only [unfoldRem]; abel
  have hc := frameX_cubic hω (rotL_rotL ω) (Q := Q) (C := C) u
  rw [frameY_rotL hω, frameX_apply, frameX_apply] at hc
  conv_lhs => rw [h]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, rotL_apply0, apply_zero_eq M u, hc]
  simp only [mx, Jet.F2, Jet.F3, List.cons_append, List.nil_append, poly3_cons, poly3_nil,
    pow_zero, mul_one, pow_one]
  ring

@[tmio T, powerlib_foundation] theorem field_apply_one (hω : ω ≠ 0) (g : ℝ → State 2 → State 2)
    (μ : ℝ) (u : State 2) :
    g μ u 1 = ω * u 0 + poly3 (my (m10 M) (m11 M) ++ (jet (rotL ω) Q C ω).G2 ++
      (jet (rotL ω) Q C ω).G3) (u 0) (u 1) μ + unfoldRem M Q C ω g μ u 1 := by
  have h : g μ u = rotL ω u + μ • M u + (Q u u + C ![u, u, u]) + unfoldRem M Q C ω g μ u := by
    simp only [unfoldRem]; abel
  have hc := frameY_cubic hω (rotL_rotL ω) (Q := Q) (C := C) u
  rw [frameY_rotL hω, frameY_rotL hω, frameX_apply] at hc
  conv_lhs => rw [h]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, rotL_apply1, apply_one_eq M u, hc]
  simp only [my, Jet.G2, Jet.G3, List.cons_append, List.nil_append, poly3_cons, poly3_nil,
    pow_zero, mul_one, pow_one]
  ring

@[tmio T, powerlib_foundation] theorem differentiable_hopfV (μ : ℝ) :
    Differentiable ℝ (hopfV M Q C ω μ) :=
  (contDiff_lyap.differentiable one_ne_zero).add
    ((contDiff_poly3 _ _ _ _ (k := 1)).differentiable one_ne_zero |>.const_mul μ)

@[tmio T, powerlib_foundation] theorem fderiv_hopfV (hω : ω ≠ 0) (μ : ℝ) (u v : State 2) :
    fderiv ℝ (hopfV M Q C ω μ) u v =
      poly3 ((jet (rotL ω) Q C ω).Vx ω) (u 0) (u 1) 0 * v 0 +
        poly3 ((jet (rotL ω) Q C ω).Vy ω) (u 0) (u 1) 0 * v 1 +
        μ * dpoly3 (wl ω (m00 M) (m01 M) (m10 M) (m11 M)) (u 0) (u 1) 0 (v 0) (v 1) 0 := by
  have h1 : HasFDerivAt (lyap (rotL ω) Q C ω) (fderiv ℝ (lyap (rotL ω) Q C ω) u) u :=
    ((contDiff_lyap.differentiable one_ne_zero) u).hasFDerivAt
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_poly3 (wl ω (m00 M) (m01 M) (m10 M) (m11 M)) frameX
    (frameY (rotL ω) ω) 0 u
  have h : HasFDerivAt (fun u => lyap (rotL ω) Q C ω u + μ * poly3
      (wl ω (m00 M) (m01 M) (m10 M) (m11 M)) (frameX u) (frameY (rotL ω) ω u)
      ((0 : State 2 →L[ℝ] ℝ) u)) (fderiv ℝ (lyap (rotL ω) Q C ω) u + μ • L) u :=
    h1.add (hL.const_mul μ)
  have e : hopfV M Q C ω μ = fun u => lyap (rotL ω) Q C ω u + μ * poly3
      (wl ω (m00 M) (m01 M) (m10 M) (m11 M)) (frameX u) (frameY (rotL ω) ω u)
      ((0 : State 2 →L[ℝ] ℝ) u) := rfl
  rw [e, h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hLv, fderiv_lyap,
    frameY_rotL hω, frameX_apply, zero_apply]

/-- On the first axis `V + μW` is the quartic `s² + c₃₀ s³ + d₄₀ s⁴`. -/
@[tmio T, powerlib_foundation] theorem hopfV_axis (hω : ω ≠ 0) (μ s : ℝ) :
    hopfV M Q C ω μ (PhasePlane.mk s 0) =
      s ^ 2 + (jet (rotL ω) Q C ω).c30 ω * s ^ 3 + (jet (rotL ω) Q C ω).d40 ω * s ^ 4 := by
  simp only [hopfV, lyap, frameY_rotL hω, frameX_apply, PhasePlane.mk_apply_zero,
    PhasePlane.mk_apply_one, zero_apply, Jet.V, Jet.V3, Jet.V4, wl, List.cons_append,
    List.nil_append, poly3_cons, poly3_nil]
  ring

end Field

/-! ## Asymptotics with the parameter of weight two -/

section Asymptotics

open powerlib.Dynamics.CenterManifold (rotL frameY_rotL)

/-- The filter of `(μ, u) → 0` restricted to `|μ| ≤ K‖u‖²`. -/
def nhdsW (K : ℝ) : Filter (ℝ × State 2) := 𝓝 0 ⊓ 𝓟 {p | |p.1| ≤ K * ‖p.2‖ ^ 2}

@[tmio T, powerlib_foundation] theorem tendsto_nhdsW (K : ℝ) :
    Tendsto (fun p : ℝ × State 2 => ‖p.2‖) (nhdsW K) (𝓝 0) := by
  have h : Tendsto (fun p : ℝ × State 2 => ‖p.2‖) (𝓝 0) (𝓝 0) := by
    have := (continuous_norm.comp continuous_snd).tendsto (0 : ℝ × State 2)
    simpa [Function.comp_def] using this
  exact h.mono_left inf_le_left

@[tmio T, powerlib_foundation] theorem isBigO_nhdsW_fst (K : ℝ) :
    (fun p : ℝ × State 2 => p.1) =O[nhdsW K] fun p => ‖p.2‖ ^ 2 := by
  refine IsBigO.of_bound K ?_
  have : ∀ᶠ p in nhdsW K, p ∈ {p : ℝ × State 2 | |p.1| ≤ K * ‖p.2‖ ^ 2} :=
    mem_inf_of_right (mem_principal_self _)
  filter_upwards [this] with p hp
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  exact hp

@[tmio T, powerlib_foundation] theorem isBigO_nhdsW_coord (K : ℝ) (i : Fin 2) :
    (fun p : ℝ × State 2 => p.2 i) =O[nhdsW K] fun p => ‖p.2‖ :=
  ((EuclideanSpace.proj i : State 2 →L[ℝ] ℝ).isBigO_comp (fun p : ℝ × State 2 => p.2) _).norm_right

@[tmio T, powerlib_foundation] theorem isBigO_nhdsW_poly (K : ℝ) (l : List (ℝ × ℕ × ℕ × ℕ)) {k : ℕ}
    (hl : ∀ t ∈ l, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) :
    (fun p : ℝ × State 2 => poly3 l (p.2 0) (p.2 1) p.1) =O[nhdsW K] fun p => ‖p.2‖ ^ k :=
  isBigO_poly3_weight (tendsto_nhdsW K) (isBigO_nhdsW_coord K 0) (isBigO_nhdsW_coord K 1)
    (isBigO_nhdsW_fst K) l hl

@[tmio T, powerlib_foundation] theorem isBigO_nhdsW_poly0 (K : ℝ) (l : List (ℝ × ℕ × ℕ × ℕ)) {k : ℕ}
    (hl : ∀ t ∈ l, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) :
    (fun p : ℝ × State 2 => poly3 l (p.2 0) (p.2 1) 0) =O[nhdsW K] fun p => ‖p.2‖ ^ k :=
  isBigO_poly3_weight (c := fun _ => 0) (tendsto_nhdsW K) (isBigO_nhdsW_coord K 0)
    (isBigO_nhdsW_coord K 1) (isBigO_zero _ _) l hl

/-- Products of weights `i` and `j` with `i + j > m` are `o(‖u‖^m)`. -/
@[tmio T, powerlib_foundation] theorem isLittleO_nhdsW_mul {K : ℝ} {a b : ℝ × State 2 → ℝ}
    {i j m : ℕ} (ha : a =O[nhdsW K] fun p => ‖p.2‖ ^ i) (hb : b =O[nhdsW K] fun p => ‖p.2‖ ^ j)
    (h : m < i + j) : (fun p => a p * b p) =o[nhdsW K] fun p => ‖p.2‖ ^ m :=
  ((ha.mul hb).congr_right fun p => by rw [← pow_add]).trans_isLittleO
    (Dynamics.isLittleO_pow_of_tendsto (tendsto_nhdsW K) h)

/-- A weight-`i` factor against an `o(‖u‖^j)` factor is `o(‖u‖^m)` for `m ≤ i + j`. -/
@[tmio T, powerlib_foundation] theorem isLittleO_nhdsW_mul' {K : ℝ} {a b : ℝ × State 2 → ℝ}
    {i j m : ℕ} (ha : a =O[nhdsW K] fun p => ‖p.2‖ ^ i) (hb : b =o[nhdsW K] fun p => ‖p.2‖ ^ j)
    (h : m ≤ i + j) : (fun p => a p * b p) =o[nhdsW K] fun p => ‖p.2‖ ^ m :=
  ((ha.mul_isLittleO hb).congr_right fun p => by rw [← pow_add]).trans_isBigO
    (Dynamics.isBigO_pow_of_tendsto (tendsto_nhdsW K) h)

/-- Explicit form of an `o`-estimate on `nhdsW K`. -/
@[tmio T, powerlib_foundation] theorem exists_bound_of_isLittleO {F : ℝ × State 2 → ℝ} {K : ℝ}
    {k : ℕ} (h : F =o[nhdsW K] fun p => ‖p.2‖ ^ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ μ u, |μ| < δ → ‖u‖ < δ → |μ| ≤ K * ‖u‖ ^ 2 → |F (μ, u)| ≤ ε * ‖u‖ ^ k := by
  have h1 := h.def hε
  rw [nhdsW, eventually_inf_principal] at h1
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp h1
  refine ⟨δ, hδ, fun μ u hμ hu hK => ?_⟩
  have hd : dist (μ, u) (0 : ℝ × State 2) < δ := by
    rw [Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right]
    exact max_lt hμ hu
  have := hb hd hK
  rwa [Real.norm_eq_abs, norm_pow, norm_norm] at this

variable {M : State 2 →L[ℝ] State 2} {Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
  {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)} {ω : ℝ}
  {g : ℝ → State 2 → State 2} {K : ℝ}

@[tmio T, powerlib_foundation] theorem isLittleO_unfoldRem_coord
    (h : (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2) =o[nhdsW K] fun p => ‖p.2‖ ^ 3)
    (i : Fin 2) :
    (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2 i) =o[nhdsW K] fun p => ‖p.2‖ ^ 3 :=
  ((EuclideanSpace.proj i : State 2 →L[ℝ] ℝ).isBigO_comp _ _).trans_isLittleO h

/-- The angle speed: `u₀ g₁ − u₁ g₀ − ω‖u‖² = o(‖u‖²)`. -/
@[tmio T, powerlib_foundation] theorem isLittleO_angNum (hω : ω ≠ 0)
    (h : (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2) =o[nhdsW K] fun p => ‖p.2‖ ^ 3) :
    (fun p : ℝ × State 2 => PlanarReturn.angNum (g p.1) p.2 - ω * ‖p.2‖ ^ 2) =o[nhdsW K]
      fun p => ‖p.2‖ ^ 2 := by
  set J := jet (rotL ω) Q C ω
  have key : ∀ p : ℝ × State 2, PlanarReturn.angNum (g p.1) p.2 - ω * ‖p.2‖ ^ 2 =
      (p.2 0 * poly3 (my (m10 M) (m11 M) ++ J.G2 ++ J.G3) (p.2 0) (p.2 1) p.1 -
        p.2 1 * poly3 (mx (m00 M) (m01 M) ++ J.F2 ++ J.F3) (p.2 0) (p.2 1) p.1) +
      (p.2 0 * unfoldRem M Q C ω g p.1 p.2 1 - p.2 1 * unfoldRem M Q C ω g p.1 p.2 0) := by
    intro p
    rw [PlanarReturn.angNum, field_apply_zero hω, field_apply_one hω, PhasePlane.norm_sq_eq]
    ring
  have hx : (fun p : ℝ × State 2 => p.2 0) =O[nhdsW K] fun p => ‖p.2‖ ^ 1 := by
    simpa using isBigO_nhdsW_coord K 0
  have hy : (fun p : ℝ × State 2 => p.2 1) =O[nhdsW K] fun p => ‖p.2‖ ^ 1 := by
    simpa using isBigO_nhdsW_coord K 1
  have hP := ((isLittleO_nhdsW_mul (m := 2) hx (isBigO_nhdsW_poly K
      (my (m10 M) (m11 M) ++ J.G2 ++ J.G3) (k := 2) (by simp [my, Jet.G2, Jet.G3]))
      (by norm_num)).sub
    (isLittleO_nhdsW_mul (m := 2) hy (isBigO_nhdsW_poly K
      (mx (m00 M) (m01 M) ++ J.F2 ++ J.F3) (k := 2) (by simp [mx, Jet.F2, Jet.F3]))
      (by norm_num)))
  have hR := (isLittleO_nhdsW_mul' (m := 2) hx (isLittleO_unfoldRem_coord h 1) (by norm_num)).sub
    (isLittleO_nhdsW_mul' (m := 2) hy (isLittleO_unfoldRem_coord h 0) (by norm_num))
  exact ((hP.congr_right fun p => by ring).add hR).congr_left fun p => (key p).symm

/-- The radial rate: `u₀ g₀ + u₁ g₁ = o(‖u‖²)`. -/
@[tmio T, powerlib_foundation] theorem isLittleO_radNum (hω : ω ≠ 0)
    (h : (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2) =o[nhdsW K] fun p => ‖p.2‖ ^ 3) :
    (fun p : ℝ × State 2 => PlanarReturn.radNum (g p.1) p.2) =o[nhdsW K] fun p => ‖p.2‖ ^ 2 := by
  set J := jet (rotL ω) Q C ω
  have key : ∀ p : ℝ × State 2, PlanarReturn.radNum (g p.1) p.2 =
      (p.2 0 * poly3 (mx (m00 M) (m01 M) ++ J.F2 ++ J.F3) (p.2 0) (p.2 1) p.1 +
        p.2 1 * poly3 (my (m10 M) (m11 M) ++ J.G2 ++ J.G3) (p.2 0) (p.2 1) p.1) +
      (p.2 0 * unfoldRem M Q C ω g p.1 p.2 0 + p.2 1 * unfoldRem M Q C ω g p.1 p.2 1) := by
    intro p
    rw [PlanarReturn.radNum, field_apply_zero hω, field_apply_one hω]
    ring
  have hx : (fun p : ℝ × State 2 => p.2 0) =O[nhdsW K] fun p => ‖p.2‖ ^ 1 := by
    simpa using isBigO_nhdsW_coord K 0
  have hy : (fun p : ℝ × State 2 => p.2 1) =O[nhdsW K] fun p => ‖p.2‖ ^ 1 := by
    simpa using isBigO_nhdsW_coord K 1
  have hP := (isLittleO_nhdsW_mul (m := 2) hx (isBigO_nhdsW_poly K
      (mx (m00 M) (m01 M) ++ J.F2 ++ J.F3) (k := 2) (by simp [mx, Jet.F2, Jet.F3]))
      (by norm_num)).add
    (isLittleO_nhdsW_mul (m := 2) hy (isBigO_nhdsW_poly K
      (my (m10 M) (m11 M) ++ J.G2 ++ J.G3) (k := 2) (by simp [my, Jet.G2, Jet.G3]))
      (by norm_num))
  have hR := (isLittleO_nhdsW_mul' (m := 2) hx (isLittleO_unfoldRem_coord h 0) (by norm_num)).add
    (isLittleO_nhdsW_mul' (m := 2) hy (isLittleO_unfoldRem_coord h 1) (by norm_num))
  exact (hP.add hR).congr_left fun p => (key p).symm

/-- **The Lie derivative of `V + μW` in coordinates**: `V̇ − μ tr M ‖u‖² − ω l₁ ‖u‖⁴` is the sum
of the products of weight at least five of `lie_identity_unfold` and the remainder `D` against the
gradient. -/
@[tmio T, powerlib_foundation] theorem lie_sub_eq (hω : ω ≠ 0) (μ : ℝ) (u : State 2) :
    fderiv ℝ (hopfV M Q C ω μ) u (g μ u) - μ * paramTrace M * ‖u‖ ^ 2 -
        ω * l1 (rotL ω) Q C ω * ‖u‖ ^ 4 =
      (poly3 ((jet (rotL ω) Q C ω).V3x ω) (u 0) (u 1) μ *
          poly3 (jet (rotL ω) Q C ω).F3 (u 0) (u 1) μ +
        poly3 ((jet (rotL ω) Q C ω).V3y ω) (u 0) (u 1) μ *
          poly3 (jet (rotL ω) Q C ω).G3 (u 0) (u 1) μ +
        poly3 ((jet (rotL ω) Q C ω).V4x ω) (u 0) (u 1) μ *
          poly3 ((jet (rotL ω) Q C ω).F2 ++ (jet (rotL ω) Q C ω).F3) (u 0) (u 1) μ +
        poly3 ((jet (rotL ω) Q C ω).V4y ω) (u 0) (u 1) μ *
          poly3 ((jet (rotL ω) Q C ω).G2 ++ (jet (rotL ω) Q C ω).G3) (u 0) (u 1) μ) +
      (poly3 ((jet (rotL ω) Q C ω).V3x ω ++ (jet (rotL ω) Q C ω).V4x ω) (u 0) (u 1) μ *
          poly3 (mx (m00 M) (m01 M)) (u 0) (u 1) μ +
        poly3 ((jet (rotL ω) Q C ω).V3y ω ++ (jet (rotL ω) Q C ω).V4y ω) (u 0) (u 1) μ *
          poly3 (my (m10 M) (m11 M)) (u 0) (u 1) μ +
        poly3 (wx ω (m00 M) (m11 M)) (u 0) (u 1) μ *
          poly3 (mx (m00 M) (m01 M) ++ (jet (rotL ω) Q C ω).F2 ++ (jet (rotL ω) Q C ω).F3)
            (u 0) (u 1) μ +
        poly3 (wy ω (m00 M) (m01 M) (m10 M) (m11 M)) (u 0) (u 1) μ *
          poly3 (my (m10 M) (m11 M) ++ (jet (rotL ω) Q C ω).G2 ++ (jet (rotL ω) Q C ω).G3)
            (u 0) (u 1) μ) +
      ((poly3 ((jet (rotL ω) Q C ω).Vx ω) (u 0) (u 1) 0 +
          poly3 (wx ω (m00 M) (m11 M)) (u 0) (u 1) μ) * unfoldRem M Q C ω g μ u 0 +
        (poly3 ((jet (rotL ω) Q C ω).Vy ω) (u 0) (u 1) 0 +
          poly3 (wy ω (m00 M) (m01 M) (m10 M) (m11 M)) (u 0) (u 1) μ) *
            unfoldRem M Q C ω g μ u 1) := by
  have hid := lie_identity_unfold ω (m00 M) (m01 M) (m10 M) (m11 M) (jet (rotL ω) Q C ω) hω
    (u 0) (u 1) μ (unfoldRem M Q C ω g μ u 0) (unfoldRem M Q C ω g μ u 1)
  rw [fderiv_hopfV hω, ← field_apply_zero hω, ← field_apply_one hω] at *
  have hn : ‖u‖ ^ 4 = (u 0 ^ 2 + u 1 ^ 2) ^ 2 := by
    rw [← PhasePlane.norm_sq_eq]; ring
  rw [hn, PhasePlane.norm_sq_eq]
  have hl : l1 (rotL ω) Q C ω = (jet (rotL ω) Q C ω).l1 ω := rfl
  simp only [paramTrace, hl]
  linear_combination hid

/-- **The Lie derivative of `V + μW`**: `V̇ − μ tr M ‖u‖² − ω l₁ ‖u‖⁴ = o(‖u‖⁴)` on `nhdsW K`. -/
@[tmio T, powerlib_foundation] theorem isLittleO_lie (hω : ω ≠ 0)
    (h : (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2) =o[nhdsW K] fun p => ‖p.2‖ ^ 3) :
    (fun p : ℝ × State 2 => fderiv ℝ (hopfV M Q C ω p.1) p.2 (g p.1 p.2) -
        p.1 * paramTrace M * ‖p.2‖ ^ 2 - ω * l1 (rotL ω) Q C ω * ‖p.2‖ ^ 4) =o[nhdsW K]
      fun p => ‖p.2‖ ^ 4 := by
  set J := jet (rotL ω) Q C ω
  set a := m00 M
  set b := m01 M
  set c := m10 M
  set d := m11 M
  have key : ∀ p : ℝ × State 2, fderiv ℝ (hopfV M Q C ω p.1) p.2 (g p.1 p.2) -
      p.1 * paramTrace M * ‖p.2‖ ^ 2 - ω * l1 (rotL ω) Q C ω * ‖p.2‖ ^ 4 =
      (poly3 (J.V3x ω) (p.2 0) (p.2 1) p.1 * poly3 J.F3 (p.2 0) (p.2 1) p.1 +
        poly3 (J.V3y ω) (p.2 0) (p.2 1) p.1 * poly3 J.G3 (p.2 0) (p.2 1) p.1 +
        poly3 (J.V4x ω) (p.2 0) (p.2 1) p.1 * poly3 (J.F2 ++ J.F3) (p.2 0) (p.2 1) p.1 +
        poly3 (J.V4y ω) (p.2 0) (p.2 1) p.1 * poly3 (J.G2 ++ J.G3) (p.2 0) (p.2 1) p.1) +
      (poly3 (J.V3x ω ++ J.V4x ω) (p.2 0) (p.2 1) p.1 * poly3 (mx a b) (p.2 0) (p.2 1) p.1 +
        poly3 (J.V3y ω ++ J.V4y ω) (p.2 0) (p.2 1) p.1 * poly3 (my c d) (p.2 0) (p.2 1) p.1 +
        poly3 (wx ω a d) (p.2 0) (p.2 1) p.1 *
          poly3 (mx a b ++ J.F2 ++ J.F3) (p.2 0) (p.2 1) p.1 +
        poly3 (wy ω a b c d) (p.2 0) (p.2 1) p.1 *
          poly3 (my c d ++ J.G2 ++ J.G3) (p.2 0) (p.2 1) p.1) +
      ((poly3 (J.Vx ω) (p.2 0) (p.2 1) 0 + poly3 (wx ω a d) (p.2 0) (p.2 1) p.1) *
          unfoldRem M Q C ω g p.1 p.2 0 +
        (poly3 (J.Vy ω) (p.2 0) (p.2 1) 0 + poly3 (wy ω a b c d) (p.2 0) (p.2 1) p.1) *
          unfoldRem M Q C ω g p.1 p.2 1) := fun p => lie_sub_eq hω p.1 p.2
  have p5 : ∀ {l₁ l₂ : List (ℝ × ℕ × ℕ × ℕ)} {i j : ℕ},
      (∀ t ∈ l₁, i ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) →
      (∀ t ∈ l₂, j ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) → 4 < i + j →
      (fun p : ℝ × State 2 => poly3 l₁ (p.2 0) (p.2 1) p.1 * poly3 l₂ (p.2 0) (p.2 1) p.1)
        =o[nhdsW K] fun p => ‖p.2‖ ^ 4 :=
    fun h₁ h₂ hij => isLittleO_nhdsW_mul (isBigO_nhdsW_poly K _ h₁) (isBigO_nhdsW_poly K _ h₂) hij
  have hA := ((p5 (l₁ := J.V3x ω) (l₂ := J.F3) (i := 2) (j := 3) (by simp [Jet.V3x])
    (by simp [Jet.F3]) (by norm_num)).add (p5 (l₁ := J.V3y ω) (l₂ := J.G3) (i := 2) (j := 3)
      (by simp [Jet.V3y]) (by simp [Jet.G3]) (by norm_num))).add
    (p5 (l₁ := J.V4x ω) (l₂ := J.F2 ++ J.F3) (i := 3) (j := 2) (by simp [Jet.V4x])
      (by simp [Jet.F2, Jet.F3]) (by norm_num)) |>.add
    (p5 (l₁ := J.V4y ω) (l₂ := J.G2 ++ J.G3) (i := 3) (j := 2) (by simp [Jet.V4y])
      (by simp [Jet.G2, Jet.G3]) (by norm_num))
  have hB := ((p5 (l₁ := J.V3x ω ++ J.V4x ω) (l₂ := mx a b) (i := 2) (j := 3)
    (by simp [Jet.V3x, Jet.V4x]) (by simp [mx]) (by norm_num)).add
    (p5 (l₁ := J.V3y ω ++ J.V4y ω) (l₂ := my c d) (i := 2) (j := 3)
      (by simp [Jet.V3y, Jet.V4y]) (by simp [my]) (by norm_num))).add
    (p5 (l₁ := wx ω a d) (l₂ := mx a b ++ J.F2 ++ J.F3) (i := 3) (j := 2) (by simp [wx])
      (by simp [mx, Jet.F2, Jet.F3]) (by norm_num)) |>.add
    (p5 (l₁ := wy ω a b c d) (l₂ := my c d ++ J.G2 ++ J.G3) (i := 3) (j := 2) (by simp [wy])
      (by simp [my, Jet.G2, Jet.G3]) (by norm_num))
  have hgx : (fun p : ℝ × State 2 => poly3 (J.Vx ω) (p.2 0) (p.2 1) 0 +
      poly3 (wx ω a d) (p.2 0) (p.2 1) p.1) =O[nhdsW K] fun p => ‖p.2‖ ^ 1 :=
    (isBigO_nhdsW_poly0 K _ (by simp [Jet.Vx, Jet.V3x, Jet.V4x])).add
      ((isBigO_nhdsW_poly K _ (k := 3) (by simp [wx])).trans
        (Dynamics.isBigO_pow_of_tendsto (tendsto_nhdsW K) (by norm_num)))
  have hgy : (fun p : ℝ × State 2 => poly3 (J.Vy ω) (p.2 0) (p.2 1) 0 +
      poly3 (wy ω a b c d) (p.2 0) (p.2 1) p.1) =O[nhdsW K] fun p => ‖p.2‖ ^ 1 :=
    (isBigO_nhdsW_poly0 K _ (by simp [Jet.Vy, Jet.V3y, Jet.V4y])).add
      ((isBigO_nhdsW_poly K _ (k := 3) (by simp [wy])).trans
        (Dynamics.isBigO_pow_of_tendsto (tendsto_nhdsW K) (by norm_num)))
  have hC := (isLittleO_nhdsW_mul' (m := 4) hgx (isLittleO_unfoldRem_coord h 0) (by norm_num)).add
    (isLittleO_nhdsW_mul' (m := 4) hgy (isLittleO_unfoldRem_coord h 1) (by norm_num))
  exact ((hA.add hB).add hC).congr_left fun p => (key p).symm

end Asymptotics

/-! ## Asymptotics on a full neighbourhood -/

section Full

open powerlib.Dynamics.CenterManifold (rotL frameY_rotL)

/-- A polynomial whose monomials have degree at least `m` in `(x, y)` and at least `k` in `μ` is
`O(s^m c^k)` along any filter with `x, y = O(s)` and `s, c → 0`. -/
@[tmio T, powerlib_foundation] theorem isBigO_poly3_mixed {α : Type*} {l : Filter α}
    {s a b c : α → ℝ} (hs : Tendsto s l (𝓝 0)) (hc : Tendsto c l (𝓝 0)) (ha : a =O[l] s)
    (hb : b =O[l] s) (L : List (ℝ × ℕ × ℕ × ℕ)) {m k : ℕ}
    (hL : ∀ t ∈ L, m ≤ t.2.1 + t.2.2.1 ∧ k ≤ t.2.2.2) :
    (fun x => poly3 L (a x) (b x) (c x)) =O[l] fun x => s x ^ m * c x ^ k := by
  induction L with
  | nil => simpa using isBigO_zero (fun x => s x ^ m * c x ^ k) l
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have hrest := ih fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')
    simp only [poly3_cons]
    refine IsBigO.add ?_ hrest
    have h1 : (fun x => a x ^ t.2.1 * b x ^ t.2.2.1) =O[l]
        fun x => s x ^ t.2.1 * s x ^ t.2.2.1 := (ha.pow _).mul (hb.pow _)
    have h2 : (fun x => s x ^ t.2.1 * s x ^ t.2.2.1) =O[l] fun x => s x ^ m :=
      (Dynamics.isBigO_pow_of_tendsto hs ht.1).congr_left fun x => pow_add _ _ _
    have h3 : (fun x => c x ^ t.2.2.2) =O[l] fun x => c x ^ k :=
      Dynamics.isBigO_pow_of_tendsto hc ht.2
    refine (((h1.trans h2).mul h3).const_mul_left t.1).congr_left fun x => by ring

variable {M : State 2 →L[ℝ] State 2} {Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
  {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)} {ω : ℝ}
  {g : ℝ → State 2 → State 2}

/-- **The Lie derivative of `V + μW` on a full neighbourhood.** If the remainder is
`o(|μ| ‖u‖ + ‖u‖³)` as `(μ, u) → 0` (no restriction on `μ`), then
`V̇ − μ tr M ‖u‖² − ω l₁ ‖u‖⁴ = o(|μ| ‖u‖² + ‖u‖⁴)`: every product of `lie_identity_unfold` has
degree at least two in `u` and weight at least five. -/
@[tmio T, powerlib_foundation] theorem isLittleO_lie_full (hω : ω ≠ 0)
    (h : (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2) =o[𝓝 0]
      fun p => |p.1| * ‖p.2‖ + ‖p.2‖ ^ 3) :
    (fun p : ℝ × State 2 => fderiv ℝ (hopfV M Q C ω p.1) p.2 (g p.1 p.2) -
        p.1 * paramTrace M * ‖p.2‖ ^ 2 - ω * l1 (rotL ω) Q C ω * ‖p.2‖ ^ 4) =o[𝓝 0]
      fun p => |p.1| * ‖p.2‖ ^ 2 + ‖p.2‖ ^ 4 := by
  set J := jet (rotL ω) Q C ω
  set a := m00 M
  set b := m01 M
  set c := m10 M
  set d := m11 M
  set Φ : ℝ × State 2 → ℝ := fun p => |p.1| * ‖p.2‖ ^ 2 + ‖p.2‖ ^ 4 with hΦ
  have hs : Tendsto (fun p : ℝ × State 2 => ‖p.2‖) (𝓝 0) (𝓝 0) := by
    have := (continuous_norm.comp continuous_snd).tendsto (0 : ℝ × State 2)
    simpa [Function.comp_def] using this
  have hμ : Tendsto (fun p : ℝ × State 2 => p.1) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_fst.tendsto (0 : ℝ × State 2))
  have hx : (fun p : ℝ × State 2 => p.2 0) =O[𝓝 0] fun p => ‖p.2‖ :=
    ((EuclideanSpace.proj (0 : Fin 2) : State 2 →L[ℝ] ℝ).isBigO_comp
      (fun p : ℝ × State 2 => p.2) _).norm_right
  have hy : (fun p : ℝ × State 2 => p.2 1) =O[𝓝 0] fun p => ‖p.2‖ :=
    ((EuclideanSpace.proj (1 : Fin 2) : State 2 →L[ℝ] ℝ).isBigO_comp
      (fun p : ℝ × State 2 => p.2) _).norm_right
  have hP := fun (L : List (ℝ × ℕ × ℕ × ℕ)) {m k : ℕ}
      (hL : ∀ t ∈ L, m ≤ t.2.1 + t.2.2.1 ∧ k ≤ t.2.2.2) =>
    isBigO_poly3_mixed hs hμ hx hy L hL
  -- small factors against `Φ`
  have hsmall : ∀ {f : ℝ × State 2 → ℝ}, Tendsto f (𝓝 0) (𝓝 0) →
      (fun p => f p * Φ p) =o[𝓝 0] Φ := fun hf =>
    (((isLittleO_one_iff ℝ).mpr hf).mul_isBigO (isBigO_refl Φ _)).congr_right
      fun p => one_mul _
  have hΦ0 : ∀ p : ℝ × State 2, 0 ≤ Φ p := fun p => by positivity
  have o5 : (fun p : ℝ × State 2 => ‖p.2‖ ^ 5 * p.1 ^ 0) =o[𝓝 0] Φ := by
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun p => ?_))
      (hsmall hs)
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hΦ]
    simp only
    nlinarith [abs_nonneg p.1, pow_nonneg (norm_nonneg p.2) 3]
  have o31 : (fun p : ℝ × State 2 => ‖p.2‖ ^ 3 * p.1 ^ 1) =o[𝓝 0] Φ := by
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun p => ?_))
      (hsmall hs)
    rw [one_mul, norm_mul, norm_pow, norm_norm, pow_one, Real.norm_eq_abs,
      Real.norm_of_nonneg (by positivity), hΦ]
    simp only
    nlinarith [abs_nonneg p.1, pow_nonneg (norm_nonneg p.2) 5]
  have o22 : (fun p : ℝ × State 2 => ‖p.2‖ ^ 2 * p.1 ^ 2) =o[𝓝 0] Φ := by
    have hμa : Tendsto (fun p : ℝ × State 2 => |p.1|) (𝓝 0) (𝓝 0) := by
      have := (continuous_abs.comp continuous_fst).tendsto (0 : ℝ × State 2)
      simpa [Function.comp_def] using this
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun p => ?_))
      (hsmall hμa)
    rw [one_mul, norm_mul, norm_pow, norm_norm, norm_pow, Real.norm_eq_abs,
      Real.norm_of_nonneg (by positivity), hΦ]
    simp only
    nlinarith [abs_nonneg p.1, pow_nonneg (norm_nonneg p.2) 4, sq_abs p.1]
  have prod : ∀ {l₁ l₂ : List (ℝ × ℕ × ℕ × ℕ)} {m₁ k₁ m₂ k₂ : ℕ},
      (∀ t ∈ l₁, m₁ ≤ t.2.1 + t.2.2.1 ∧ k₁ ≤ t.2.2.2) →
      (∀ t ∈ l₂, m₂ ≤ t.2.1 + t.2.2.1 ∧ k₂ ≤ t.2.2.2) →
      (fun p : ℝ × State 2 => ‖p.2‖ ^ (m₁ + m₂) * p.1 ^ (k₁ + k₂)) =o[𝓝 0] Φ →
      (fun p : ℝ × State 2 => poly3 l₁ (p.2 0) (p.2 1) p.1 * poly3 l₂ (p.2 0) (p.2 1) p.1)
        =o[𝓝 0] Φ := fun h₁ h₂ ho =>
    ((hP _ h₁).mul (hP _ h₂)).trans_isLittleO (ho.congr_left fun p => by ring)
  have hA := ((prod (l₁ := J.V3x ω) (l₂ := J.F3) (m₁ := 2) (k₁ := 0) (m₂ := 3) (k₂ := 0)
    (by simp [Jet.V3x]) (by simp [Jet.F3]) o5).add
    (prod (l₁ := J.V3y ω) (l₂ := J.G3) (m₁ := 2) (k₁ := 0) (m₂ := 3) (k₂ := 0)
      (by simp [Jet.V3y]) (by simp [Jet.G3]) o5)).add
    (prod (l₁ := J.V4x ω) (l₂ := J.F2 ++ J.F3) (m₁ := 3) (k₁ := 0) (m₂ := 2) (k₂ := 0)
      (by simp [Jet.V4x]) (by simp [Jet.F2, Jet.F3]) o5) |>.add
    (prod (l₁ := J.V4y ω) (l₂ := J.G2 ++ J.G3) (m₁ := 3) (k₁ := 0) (m₂ := 2) (k₂ := 0)
      (by simp [Jet.V4y]) (by simp [Jet.G2, Jet.G3]) o5)
  have hsplit : ∀ (w l₀ l₂ l₃ : List (ℝ × ℕ × ℕ × ℕ)) (p : ℝ × State 2),
      poly3 w (p.2 0) (p.2 1) p.1 * poly3 (l₀ ++ l₂ ++ l₃) (p.2 0) (p.2 1) p.1 =
        poly3 w (p.2 0) (p.2 1) p.1 * poly3 l₀ (p.2 0) (p.2 1) p.1 +
          poly3 w (p.2 0) (p.2 1) p.1 * poly3 (l₂ ++ l₃) (p.2 0) (p.2 1) p.1 := by
    intro w l₀ l₂ l₃ p
    rw [List.append_assoc, Jet5.poly3_append]; ring
  have hB := ((prod (l₁ := J.V3x ω ++ J.V4x ω) (l₂ := mx a b) (m₁ := 2) (k₁ := 0) (m₂ := 1)
    (k₂ := 1) (by simp [Jet.V3x, Jet.V4x]) (by simp [mx]) o31).add
    (prod (l₁ := J.V3y ω ++ J.V4y ω) (l₂ := my c d) (m₁ := 2) (k₁ := 0) (m₂ := 1) (k₂ := 1)
      (by simp [Jet.V3y, Jet.V4y]) (by simp [my]) o31)).add
    (((prod (l₁ := wx ω a d) (l₂ := mx a b) (m₁ := 1) (k₁ := 1) (m₂ := 1) (k₂ := 1)
      (by simp [wx]) (by simp [mx]) o22).add
      (prod (l₁ := wx ω a d) (l₂ := J.F2 ++ J.F3) (m₁ := 1) (k₁ := 1) (m₂ := 2) (k₂ := 0)
        (by simp [wx]) (by simp [Jet.F2, Jet.F3]) o31)).congr_left
      fun p => (hsplit _ _ _ _ p).symm) |>.add
    (((prod (l₁ := wy ω a b c d) (l₂ := my c d) (m₁ := 1) (k₁ := 1) (m₂ := 1) (k₂ := 1)
      (by simp [wy]) (by simp [my]) o22).add
      (prod (l₁ := wy ω a b c d) (l₂ := J.G2 ++ J.G3) (m₁ := 1) (k₁ := 1) (m₂ := 2) (k₂ := 0)
        (by simp [wy]) (by simp [Jet.G2, Jet.G3]) o31)).congr_left
      fun p => (hsplit _ _ _ _ p).symm)
  have hgrad : ∀ (l w : List (ℝ × ℕ × ℕ × ℕ)), (∀ t ∈ l, 1 ≤ t.2.1 + t.2.2.1 ∧ 0 ≤ t.2.2.2) →
      (∀ t ∈ w, 1 ≤ t.2.1 + t.2.2.1 ∧ 1 ≤ t.2.2.2) →
      (fun p : ℝ × State 2 => poly3 l (p.2 0) (p.2 1) 0 + poly3 w (p.2 0) (p.2 1) p.1)
        =O[𝓝 0] fun p => ‖p.2‖ := by
    intro l w hl hw
    have h1 := (isBigO_poly3_mixed (c := fun _ => (0 : ℝ)) hs tendsto_const_nhds hx hy l hl)
    have h2 := hP w hw
    have hb : (fun p : ℝ × State 2 => ‖p.2‖ ^ 1 * p.1 ^ 1) =O[𝓝 0] fun p => ‖p.2‖ := by
      have := (isBigO_refl (fun p : ℝ × State 2 => ‖p.2‖) (𝓝 0)).mul
        (hμ.isBigO_one ℝ)
      exact (this.congr_left fun p => by ring).congr_right fun p => mul_one _
    exact ((h1.congr_right fun p => by ring).add (h2.trans hb))
  have hrem : ∀ i : Fin 2, (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2 i) =o[𝓝 0]
      fun p => |p.1| * ‖p.2‖ + ‖p.2‖ ^ 3 := fun i =>
    ((EuclideanSpace.proj i : State 2 →L[ℝ] ℝ).isBigO_comp _ _).trans_isLittleO h
  have hC : (fun p : ℝ × State 2 =>
      (poly3 (J.Vx ω) (p.2 0) (p.2 1) 0 + poly3 (wx ω a d) (p.2 0) (p.2 1) p.1) *
        unfoldRem M Q C ω g p.1 p.2 0 +
      (poly3 (J.Vy ω) (p.2 0) (p.2 1) 0 + poly3 (wy ω a b c d) (p.2 0) (p.2 1) p.1) *
        unfoldRem M Q C ω g p.1 p.2 1) =o[𝓝 0] Φ := by
    have e : ∀ p : ℝ × State 2, ‖p.2‖ * (|p.1| * ‖p.2‖ + ‖p.2‖ ^ 3) = Φ p := fun p => by
      rw [hΦ]; ring
    refine ((((hgrad _ _ (by simp [Jet.Vx, Jet.V3x, Jet.V4x]) (by simp [wx])).mul_isLittleO
      (hrem 0)).add ((hgrad _ _ (by simp [Jet.Vy, Jet.V3y, Jet.V4y]) (by simp [wy])).mul_isLittleO
        (hrem 1))).congr_right fun p => ?_)
    · exact e p
  have hsum := (hA.add hB).add hC
  refine hsum.congr_left fun p => (lie_sub_eq hω p.1 p.2).symm

/-- `V + μW = ‖u‖² + o(‖u‖²)` as `(μ, u) → 0`. -/
@[tmio T, powerlib_foundation] theorem isLittleO_hopfV_sub (hω : ω ≠ 0) :
    (fun p : ℝ × State 2 => hopfV M Q C ω p.1 p.2 - ‖p.2‖ ^ 2) =o[𝓝 0]
      fun p => ‖p.2‖ ^ 2 := by
  set J := jet (rotL ω) Q C ω
  have hs : Tendsto (fun p : ℝ × State 2 => ‖p.2‖) (𝓝 0) (𝓝 0) := by
    have := (continuous_norm.comp continuous_snd).tendsto (0 : ℝ × State 2)
    simpa [Function.comp_def] using this
  have hμ : Tendsto (fun p : ℝ × State 2 => p.1) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_fst.tendsto (0 : ℝ × State 2))
  have hx : (fun p : ℝ × State 2 => p.2 0) =O[𝓝 0] fun p => ‖p.2‖ :=
    ((EuclideanSpace.proj (0 : Fin 2) : State 2 →L[ℝ] ℝ).isBigO_comp
      (fun p : ℝ × State 2 => p.2) _).norm_right
  have hy : (fun p : ℝ × State 2 => p.2 1) =O[𝓝 0] fun p => ‖p.2‖ :=
    ((EuclideanSpace.proj (1 : Fin 2) : State 2 →L[ℝ] ℝ).isBigO_comp
      (fun p : ℝ × State 2 => p.2) _).norm_right
  have e : ∀ p : ℝ × State 2, hopfV M Q C ω p.1 p.2 - ‖p.2‖ ^ 2 =
      poly3 (J.V3 ω ++ J.V4 ω) (p.2 0) (p.2 1) 0 +
        p.1 * poly3 (wl ω (m00 M) (m01 M) (m10 M) (m11 M)) (p.2 0) (p.2 1) 0 := by
    intro p
    simp only [hopfV, lyap, frameY_rotL hω, frameX_apply, zero_apply, Jet.V,
      List.append_assoc, Jet5.poly3_append, poly3_cons, poly3_nil]
    rw [PhasePlane.norm_sq_eq]
    ring
  have h1 := isBigO_poly3_mixed (c := fun _ => (0 : ℝ)) hs tendsto_const_nhds hx hy
    (J.V3 ω ++ J.V4 ω) (m := 3) (k := 0) (by simp [Jet.V3, Jet.V4])
  have h2 := isBigO_poly3_mixed (c := fun _ => (0 : ℝ)) hs tendsto_const_nhds hx hy
    (wl ω (m00 M) (m01 M) (m10 M) (m11 M)) (m := 2) (k := 0) (by simp [wl])
  have o1 : (fun p : ℝ × State 2 => ‖p.2‖ ^ 3 * (0 : ℝ) ^ 0) =o[𝓝 0] fun p => ‖p.2‖ ^ 2 :=
    (Dynamics.isLittleO_pow_of_tendsto hs (by norm_num : 2 < 3)).congr_left fun p => by ring
  have o2 : (fun p : ℝ × State 2 => p.1 * poly3 (wl ω (m00 M) (m01 M) (m10 M) (m11 M))
      (p.2 0) (p.2 1) 0) =o[𝓝 0] fun p => ‖p.2‖ ^ 2 := by
    have := ((isLittleO_one_iff ℝ).mpr hμ).mul_isBigO (h2.congr_right fun p => by ring :
      _ =O[𝓝 0] fun p : ℝ × State 2 => ‖p.2‖ ^ 2)
    exact this.congr_right fun p => one_mul _
  exact ((h1.trans_isLittleO o1).add o2).congr_left fun p => (e p).symm

end Full

/-! ## Elementary inequalities -/

/-- `s ↦ s² + A s³ + B s⁴` is strictly increasing on `[0, δ]` for some `δ > 0`. -/
@[tmio T, powerlib_foundation] theorem exists_strictMonoOn_quartic (A B : ℝ) :
    ∃ δ > 0, StrictMonoOn (fun s : ℝ => s ^ 2 + A * s ^ 3 + B * s ^ 4) (Icc 0 δ) := by
  set δ := 1 / (2 * (|A| + |B| + 1)) with hδ
  have hD : 0 < |A| + |B| + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]; linarith [abs_nonneg A, abs_nonneg B]
  have hδD : (|A| + |B| + 1) * δ = 1 / 2 := by rw [hδ]; field_simp
  refine ⟨δ, hδ0, strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
    (Continuous.continuousOn (by fun_prop)) fun s hs => ?_⟩
  rw [interior_Icc] at hs
  have hd : HasDerivAt (fun s : ℝ => s ^ 2 + A * s ^ 3 + B * s ^ 4)
      (2 * s + 3 * A * s ^ 2 + 4 * B * s ^ 3) s := by
    have := (((hasDerivAt_pow 2 s).add ((hasDerivAt_pow 3 s).const_mul A)).add
      ((hasDerivAt_pow 4 s).const_mul B))
    convert this using 1
    push_cast
    ring
  rw [hd.deriv]
  have hs0 := hs.1
  have hs1 : s ≤ 1 := le_trans hs.2.le hδ1
  have h1 : |3 * A * s + 4 * B * s ^ 2| ≤ 4 * (|A| + |B|) * s := by
    calc |3 * A * s + 4 * B * s ^ 2| ≤ |3 * A * s| + |4 * B * s ^ 2| := abs_add_le _ _
      _ = 3 * |A| * s + 4 * |B| * s ^ 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hs0, abs_of_nonneg (sq_nonneg s)]
          norm_num
      _ ≤ 4 * (|A| + |B|) * s := by
          have hss : s ^ 2 ≤ s := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hss (abs_nonneg B),
            mul_nonneg (abs_nonneg A) hs0.le]
  have h2 : 4 * (|A| + |B|) * s < 2 := by
    have : (|A| + |B| + 1) * s < (|A| + |B| + 1) * δ := mul_lt_mul_of_pos_left hs.2 hD
    nlinarith [abs_nonneg A, abs_nonneg B]
  have h3 : 0 < 2 + 3 * A * s + 4 * B * s ^ 2 := by
    have := (abs_le.mp h1).1
    linarith
  nlinarith

/-- Inside the cycle (`ρ ≤ 4ν/9`) the Lyapunov derivative has the sign of `−ℓ₁`. -/
@[tmio T, powerlib_foundation] theorem inner_sign {ω ℓ ν ρ E : ℝ} (hω : 0 < ω) (hℓ : ℓ ≠ 0)
    (hρ : 0 < ρ) (hρν : 9 * ρ ≤ 4 * ν) (hE : |E| ≤ ω * |ℓ| / 4 * ρ ^ 2) :
    0 < -ℓ * (-(ν * ω * ℓ) * ρ + ω * ℓ * ρ ^ 2 + E) := by
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have h1 : -(ℓ * E) ≥ -(|ℓ| * |E|) := by
    have := le_abs_self (ℓ * E); rw [abs_mul] at this; linarith
  have h2 : |ℓ| * |E| ≤ |ℓ| * (ω * |ℓ| / 4 * ρ ^ 2) := mul_le_mul_of_nonneg_left hE (abs_nonneg _)
  have h3 : |ℓ| * |ℓ| = ℓ ^ 2 := by rw [abs_mul_abs_self, sq]
  have h4 : ω * ℓ ^ 2 * ρ * (9 * ρ) ≤ ω * ℓ ^ 2 * ρ * (4 * ν) :=
    mul_le_mul_of_nonneg_left hρν (by positivity)
  have h5 : 0 < ω * ℓ ^ 2 * ρ ^ 2 := by positivity
  nlinarith

/-- Outside the cycle (`ρ ≥ 9ν/4`) the Lyapunov derivative has the sign of `ℓ₁`. -/
@[tmio T, powerlib_foundation] theorem outer_sign {ω ℓ ν ρ E : ℝ} (hω : 0 < ω) (hℓ : ℓ ≠ 0)
    (hρ : 0 < ρ) (hρν : 9 * ν ≤ 4 * ρ) (hE : |E| ≤ ω * |ℓ| / 4 * ρ ^ 2) :
    -ℓ * (-(ν * ω * ℓ) * ρ + ω * ℓ * ρ ^ 2 + E) < 0 := by
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have h1 : -(ℓ * E) ≤ |ℓ| * |E| := by
    have := neg_abs_le (ℓ * E); rw [abs_mul] at this
    have := le_abs_self (ℓ * E); rw [abs_mul] at this; linarith
  have h2 : |ℓ| * |E| ≤ |ℓ| * (ω * |ℓ| / 4 * ρ ^ 2) := mul_le_mul_of_nonneg_left hE (abs_nonneg _)
  have h3 : |ℓ| * |ℓ| = ℓ ^ 2 := by rw [abs_mul_abs_self, sq]
  have h4 : ω * ℓ ^ 2 * ρ * (9 * ν) ≤ ω * ℓ ^ 2 * ρ * (4 * ρ) :=
    mul_le_mul_of_nonneg_left hρν (by positivity)
  have h5 : 0 < ω * ℓ ^ 2 * ρ ^ 2 := by positivity
  nlinarith

@[tmio T, powerlib_foundation] theorem band_lo {a x Λ : ℝ} (hx : 0 ≤ x) (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ ≤ 4 / 3) (h : a / Λ ≤ x) : 3 * a ≤ 4 * x := by
  rw [div_le_iff₀ (by linarith)] at h
  nlinarith

@[tmio T, powerlib_foundation] theorem band_hi {a x Λ : ℝ} (ha : 0 ≤ a) (hΛ : Λ ≤ 4 / 3)
    (h : x ≤ a * Λ) : 3 * x ≤ 4 * a := by
  nlinarith

@[tmio T, powerlib_foundation] theorem band_lo_sq {a x Λ : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hΛ1 : 1 ≤ Λ) (hΛ : Λ ≤ 4 / 3) (h : a / Λ ≤ x) : 9 * a ^ 2 ≤ 16 * x ^ 2 := by
  have h1 := band_lo hx hΛ1 hΛ h
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  nlinarith

@[tmio T, powerlib_foundation] theorem band_hi_sq {a x Λ : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hΛ : Λ ≤ 4 / 3) (h : x ≤ a * Λ) : 9 * x ^ 2 ≤ 16 * a ^ 2 := by
  have h1 := band_hi ha hΛ h
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  nlinarith

/-! ## The Hopf cycle of a planar family -/

section Main

open powerlib.Dynamics.CenterManifold (rotL)

variable {M : State 2 →L[ℝ] State 2} {Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
  {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)} {ω : ℝ}

/-- **Hopf cycles of a planar family.** Let `g(μ, u) = R u + μ M u + Q(u, u) + C(u, u, u) +
D(μ, u)` with `R = rotL ω` the rotation by `ω > 0`, and the remainder `D = o(‖u‖³)` as
`(μ, u) → 0` with `|μ| ≤ K‖u‖²`, for every `K` (the parameter has weight two); let each `g μ`,
`|μ|` small, be Lipschitz on a fixed disc. If `tr M ≠ 0` (transversality: the real part of the
critical eigenvalues moves at speed `tr M / 2`) and `l₁ ≠ 0`, then for every small `μ` with
`μ · tr M · l₁ < 0` the field `g μ` has a nonconstant periodic orbit, of period at most `4π/ω`,
with `ν/8 ≤ ‖γ‖² ≤ 8ν`, `ν = −μ tr M/(ω l₁) > 0`: the amplitude is of order `|μ|^{1/2}`. -/
@[tmio T, powerlib_foundation] theorem exists_periodicOrbit (hω : 0 < ω)
    {g : ℝ → State 2 → State 2}
    (hexp : ∀ K, (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2) =o[nhdsW K]
      fun p => ‖p.2‖ ^ 3)
    (hlip : ∃ ρ > 0, ∀ μ, |μ| < ρ → ∃ L, LipschitzOnWith L (g μ) (Metric.closedBall 0 ρ))
    (hτ : paramTrace M ≠ 0) (hl : l1 (rotL ω) Q C ω ≠ 0) :
    ∃ δ > 0, ∀ μ, |μ| < δ → μ * paramTrace M * l1 (rotL ω) Q C ω < 0 →
      ∃ γ : ℝ → State 2, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
        (∀ t, HasDerivAt γ (g μ (γ t)) t) ∧ (∀ t, γ (t + T) = γ t) ∧ (∃ t, γ t ≠ γ 0) ∧
        ∀ t, -(μ * paramTrace M) / (ω * l1 (rotL ω) Q C ω) / 8 ≤ ‖γ t‖ ^ 2 ∧
          ‖γ t‖ ^ 2 ≤ 8 * (-(μ * paramTrace M) / (ω * l1 (rotL ω) Q C ω)) := by
  set τ := paramTrace M with hτdef
  set ℓ := l1 (rotL ω) Q C ω with hℓdef
  set J := jet (rotL ω) Q C ω
  have hω0 : ω ≠ 0 := hω.ne'
  have hτa : 0 < |τ| := abs_pos.mpr hτ
  have hℓa : 0 < |ℓ| := abs_pos.mpr hl
  set K₀ := 8 * ω * |ℓ| / |τ| with hK₀
  set β := ω / (32 * Real.pi) with hβ
  have hβ0 : 0 < β := by positivity
  obtain ⟨δ₁, hδ₁, hE1⟩ :=
    exists_bound_of_isLittleO (isLittleO_angNum hω0 (hexp K₀)) (half_pos hω)
  obtain ⟨δ₂, hδ₂, hE2⟩ := exists_bound_of_isLittleO (isLittleO_radNum hω0 (hexp K₀)) hβ0
  obtain ⟨δ₃, hδ₃, hE3⟩ := exists_bound_of_isLittleO (isLittleO_lie hω0 (hexp K₀))
    (show 0 < ω * |ℓ| / 4 by positivity)
  obtain ⟨δ₄, hδ₄, hmono⟩ := exists_strictMonoOn_quartic (J.c30 ω) (J.d40 ω)
  obtain ⟨ρ, hρ, hlipρ⟩ := hlip
  set Δ := min (min (min δ₁ δ₂) (min δ₃ δ₄)) ρ with hΔ
  have hΔ0 : 0 < Δ := lt_min (lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄)) hρ
  have hΔ1 : Δ ≤ δ₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hΔ2 : Δ ≤ δ₂ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hΔ3 : Δ ≤ δ₃ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔ4 : Δ ≤ δ₄ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hΔρ : Δ ≤ ρ := min_le_right _ _
  refine ⟨min Δ (Δ ^ 2 * ω * |ℓ| / (16 * |τ|)), lt_min hΔ0 (by positivity),
    fun μ hμ hsgn => ?_⟩
  have hμΔ : |μ| < Δ := lt_of_lt_of_le hμ (min_le_left _ _)
  have hμ2 : |μ| < Δ ^ 2 * ω * |ℓ| / (16 * |τ|) := lt_of_lt_of_le hμ (min_le_right _ _)
  set ν := -(μ * τ) / (ω * ℓ) with hνdef
  have hνω : ν * ω * ℓ = -(μ * τ) := by rw [hνdef]; field_simp
  have hν0 : 0 < ν := by
    have e : ν = -(μ * τ * ℓ) / (ω * ℓ ^ 2) := by rw [hνdef]; field_simp
    rw [e]
    exact div_pos (by linarith) (by positivity)
  have hνabs : ν * (ω * |ℓ|) = |μ| * |τ| := by
    have h1 : |ν * ω * ℓ| = |μ * τ| := by rw [hνω, abs_neg]
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hν0, abs_of_pos hω] at h1
    linarith
  have hνΔ : 16 * ν < Δ ^ 2 := by
    have h1 : |μ| * |τ| < Δ ^ 2 * ω * |ℓ| / 16 := by
      calc |μ| * |τ| < Δ ^ 2 * ω * |ℓ| / (16 * |τ|) * |τ| := mul_lt_mul_of_pos_right hμ2 hτa
        _ = Δ ^ 2 * ω * |ℓ| / 16 := by field_simp
    have hωℓ : 0 < ω * |ℓ| := by positivity
    have h2 : 16 * ν * (ω * |ℓ|) < Δ ^ 2 * (ω * |ℓ|) := by linarith
    exact lt_of_mul_lt_mul_right h2 hωℓ.le
  -- the annulus
  set c := ω / 2 with hc
  have hc0 : 0 < c := by positivity
  set s₁ := √ν / 2 with hs₁
  set s₂ := 2 * √ν with hs₂
  have hsq : √ν ^ 2 = ν := Real.sq_sqrt hν0.le
  have hsν : 0 < √ν := Real.sqrt_pos.mpr hν0
  have hs₁sq : s₁ ^ 2 = ν / 4 := by rw [hs₁, div_pow, hsq]; norm_num
  have hs₂sq : s₂ ^ 2 = 4 * ν := by rw [hs₂, mul_pow, hsq]; norm_num
  have hsΔ : 4 * √ν < Δ := by
    have h1 : (4 * √ν) ^ 2 < Δ ^ 2 := by rw [mul_pow, hsq]; linarith
    exact (pow_lt_pow_iff_left₀ (by positivity) hΔ0.le two_ne_zero).mp h1
  set Λ := PlanarReturn.bandFactor β c with hΛdef
  have hΛe : Λ = Real.exp (1 / 4) := by
    rw [hΛdef, PlanarReturn.bandFactor, hβ, hc]; congr 1; field_simp; ring
  have hΛ1 : 1 ≤ Λ := by rw [hΛe]; exact Real.one_le_exp (by norm_num)
  have hΛ43 : Λ ≤ 4 / 3 := by
    rw [hΛe]
    have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 4) (by norm_num) (by norm_num)
    norm_num at this ⊢
    linarith
  -- squares on the bands
  have hlo : ∀ u : State 2, s₁ / Λ ≤ ‖u‖ → 9 * ν ≤ 64 * ‖u‖ ^ 2 := by
    intro u h
    have := band_lo_sq (by positivity) (norm_nonneg u) hΛ1 hΛ43 h
    linarith
  have hhi : ∀ u : State 2, ‖u‖ ≤ s₂ * Λ → 9 * ‖u‖ ^ 2 ≤ 64 * ν := by
    intro u h
    have := band_hi_sq (by positivity) (norm_nonneg u) hΛ43 h
    linarith
  have hin_hi : ∀ u : State 2, ‖u‖ ≤ s₁ * Λ → 9 * ‖u‖ ^ 2 ≤ 4 * ν := by
    intro u h
    have := band_hi_sq (by positivity) (norm_nonneg u) hΛ43 h
    linarith
  have hout_lo : ∀ u : State 2, s₂ / Λ ≤ ‖u‖ → 9 * ν ≤ 4 * ‖u‖ ^ 2 := by
    intro u h
    have := band_lo_sq (by positivity) (norm_nonneg u) hΛ1 hΛ43 h
    linarith
  have hs₂Λ : 3 * (s₂ * Λ) ≤ 4 * s₂ := band_hi (by positivity) hΛ43 le_rfl
  have hsmall : ∀ u : State 2, ‖u‖ ≤ s₂ * Λ → ‖u‖ < Δ := by
    intro u h
    linarith
  have hμK : ∀ u : State 2, s₁ / Λ ≤ ‖u‖ → |μ| ≤ K₀ * ‖u‖ ^ 2 := by
    intro u h
    have h1 := hlo u h
    have h2 : ν ≤ 8 * ‖u‖ ^ 2 := by linarith
    have h3 : ν * (ω * |ℓ|) ≤ 8 * ‖u‖ ^ 2 * (ω * |ℓ|) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    rw [hK₀, show 8 * ω * |ℓ| / |τ| * ‖u‖ ^ 2 = 8 * ‖u‖ ^ 2 * (ω * |ℓ|) / |τ| by ring,
      le_div_iff₀ hτa]
    linarith
  -- the hypotheses of the annulus theorem
  have hang : ∀ u, s₁ / Λ ≤ ‖u‖ → ‖u‖ ≤ s₂ * Λ →
      c * ‖u‖ ^ 2 ≤ PlanarReturn.angNum (g μ) u := by
    intro u h1 h2
    have h := hE1 μ u (lt_of_lt_of_le hμΔ hΔ1) (lt_of_lt_of_le (hsmall u h2) hΔ1) (hμK u h1)
    simp only at h
    have := (abs_le.mp h).1
    have e : ω * ‖u‖ ^ 2 = 2 * (c * ‖u‖ ^ 2) := by rw [hc]; ring
    linarith
  have hrad : ∀ u, s₁ / Λ ≤ ‖u‖ → ‖u‖ ≤ s₂ * Λ →
      |PlanarReturn.radNum (g μ) u| ≤ β * ‖u‖ ^ 2 := by
    intro u h1 h2
    have h := hE2 μ u (lt_of_lt_of_le hμΔ hΔ2) (lt_of_lt_of_le (hsmall u h2) hΔ2) (hμK u h1)
    simpa only using h
  have hlie : ∀ u, s₁ / Λ ≤ ‖u‖ → ‖u‖ ≤ s₂ * Λ →
      |fderiv ℝ (hopfV M Q C ω μ) u (g μ u) - μ * τ * ‖u‖ ^ 2 - ω * ℓ * ‖u‖ ^ 4| ≤
        ω * |ℓ| / 4 * (‖u‖ ^ 2) ^ 2 := by
    intro u h1 h2
    have h := hE3 μ u (lt_of_lt_of_le hμΔ hΔ3) (lt_of_lt_of_le (hsmall u h2) hΔ3) (hμK u h1)
    simp only at h
    rw [← pow_mul]
    exact h
  have hsplit : ∀ u, fderiv ℝ (hopfV M Q C ω μ) u (g μ u) =
      -(ν * ω * ℓ) * ‖u‖ ^ 2 + ω * ℓ * (‖u‖ ^ 2) ^ 2 +
        (fderiv ℝ (hopfV M Q C ω μ) u (g μ u) - μ * τ * ‖u‖ ^ 2 - ω * ℓ * ‖u‖ ^ 4) := by
    intro u
    rw [hνω]
    ring
  have hs₁Λ : s₁ * Λ ≤ s₂ * Λ := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hs₁₂ : s₁ / Λ ≤ s₂ / Λ := div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hin : ∀ u, s₁ / Λ ≤ ‖u‖ → ‖u‖ ≤ s₁ * Λ →
      0 < -ℓ * fderiv ℝ (hopfV M Q C ω μ) u (g μ u) := by
    intro u h1 h2
    have hpos : 0 < ‖u‖ ^ 2 := by
      have := hlo u h1; linarith
    rw [hsplit u]
    exact inner_sign hω hl hpos (hin_hi u h2) (hlie u h1 (h2.trans hs₁Λ))
  have hout : ∀ u, s₂ / Λ ≤ ‖u‖ → ‖u‖ ≤ s₂ * Λ →
      -ℓ * fderiv ℝ (hopfV M Q C ω μ) u (g μ u) < 0 := by
    intro u h1 h2
    have hpos : 0 < ‖u‖ ^ 2 := by
      have := hout_lo u h1; linarith
    rw [hsplit u]
    exact outer_sign hω hl hpos (hout_lo u h1) (hlie u (hs₁₂.trans h1) h2)
  have hVm : StrictMonoOn (fun s => hopfV M Q C ω μ (PhasePlane.mk s 0))
      (Icc (s₁ / Λ) (s₂ * Λ)) := by
    have e : (fun s => hopfV M Q C ω μ (PhasePlane.mk s 0)) =
        fun s : ℝ => s ^ 2 + J.c30 ω * s ^ 3 + J.d40 ω * s ^ 4 :=
      funext fun s => hopfV_axis hω0 μ s
    rw [e]
    refine hmono.mono (Icc_subset_Icc (by positivity) ?_)
    linarith
  obtain ⟨L, hL⟩ := hlipρ μ (lt_of_lt_of_le hμΔ hΔρ)
  have hR : s₂ * Λ ≤ ρ := by linarith
  obtain ⟨γ, T, hT0, hT, hγd, hγT, hγnc, -, hγb⟩ :=
    PlanarReturn.exists_periodicOrbit_of_annulus hL hc0 hβ0 (by positivity)
      (by rw [hs₁, hs₂]; linarith) hR hang hrad (differentiable_hopfV μ) hVm hin hout
  refine ⟨γ, T, hT0, ?_, hγd, hγT, hγnc, fun t => ?_⟩
  · calc T ≤ 2 * Real.pi / c := hT
      _ = 4 * Real.pi / ω := by rw [hc]; field_simp; ring
  · have h1 := hlo (γ t) (hγb t).1
    have h2 := hhi (γ t) (hγb t).2
    constructor <;> linarith

end Main


/-! ## Every small cycle has the Hopf amplitude -/

section Amplitude

open powerlib.Dynamics.CenterManifold (rotL)

/-- On the side `μ τ l₁ ≥ 0` the Lie derivative has the sign of `l₁` away from `0`. -/
@[tmio T, powerlib_foundation] private theorem lie_pos_of_nonneg {ω τ ℓ μ ε r L : ℝ}
    (hℓ : ℓ ≠ 0) (hs : 0 ≤ μ * τ * ℓ) (hr : 0 < r) (hετ : ε ≤ |τ|) (hεℓ : ε < ω * |ℓ|)
    (hE : |L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4| ≤ ε * (|μ| * r ^ 2 + r ^ 4)) : 0 < ℓ * L := by
  have hℓa : 0 < |ℓ| := abs_pos.mpr hℓ
  have h1 : ℓ * μ * τ * r ^ 2 = |μ| * |τ| * |ℓ| * r ^ 2 := by
    have : μ * τ * ℓ = |μ| * |τ| * |ℓ| := by
      rw [← abs_mul, ← abs_mul, abs_of_nonneg hs]
    rw [show ℓ * μ * τ = μ * τ * ℓ by ring, this]
  have h2 : ω * ℓ ^ 2 * r ^ 4 = ω * |ℓ| ^ 2 * r ^ 4 := by rw [sq_abs]
  have h3 : -(|ℓ| * (ε * (|μ| * r ^ 2 + r ^ 4))) ≤
      ℓ * (L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4) := by
    have := mul_le_mul_of_nonneg_left hE hℓa.le
    rw [← abs_mul] at this
    exact neg_le_of_abs_le this
  have k1 : 0 < |ℓ| * ((ω * |ℓ| - ε) * r ^ 4) := by
    have : 0 < ω * |ℓ| - ε := by linarith
    positivity
  have k2 : 0 ≤ |ℓ| * ((|τ| - ε) * (|μ| * r ^ 2)) := by
    have : 0 ≤ |τ| - ε := by linarith
    positivity
  have e : ℓ * L = ℓ * μ * τ * r ^ 2 + ω * ℓ ^ 2 * r ^ 4 +
      ℓ * (L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4) := by ring
  rw [e, h1, h2]
  nlinarith [h3, k1, k2]

/-- On the side `μ τ l₁ < 0`, outside the annulus (`r² ≥ (1 + a) ν`), the Lie derivative has the
sign of `l₁`. -/
@[tmio T, powerlib_foundation] private theorem lie_pos_of_outer {ω τ ℓ μ ε r L ν a : ℝ}
    (hω : 0 < ω) (hℓ : ℓ ≠ 0) (hτ : τ ≠ 0) (hν : 0 < ν) (hμτ : μ * τ = -(ω * ℓ * ν))
    (ha : 0 < a) (ha1 : a ≤ 1) (hr : (1 + a) * ν ≤ r ^ 2) (hε0 : 0 ≤ ε)
    (hε : ε * (ω * |ℓ| / |τ| + 1) ≤ ω * |ℓ| * a / 4)
    (hE : |L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4| ≤ ε * (|μ| * r ^ 2 + r ^ 4)) : 0 < ℓ * L := by
  have hℓa : 0 < |ℓ| := abs_pos.mpr hℓ
  have hτa : 0 < |τ| := abs_pos.mpr hτ
  have hμ : |μ| = ω * |ℓ| * ν / |τ| := by
    rw [eq_div_iff hτa.ne', ← abs_mul, hμτ, abs_neg, abs_mul, abs_mul, abs_of_pos hω,
      abs_of_pos hν]
  have hr2 : 0 < r ^ 2 := lt_of_lt_of_le (by positivity) hr
  have hνr : ν ≤ r ^ 2 := le_trans (by nlinarith) hr
  have hgap : a / 2 * r ^ 2 ≤ r ^ 2 - ν := by nlinarith
  have hμr : |μ| * r ^ 2 ≤ ω * |ℓ| / |τ| * r ^ 4 := by
    rw [hμ, show r ^ 4 = r ^ 2 * r ^ 2 by ring]
    have : 0 ≤ ω * |ℓ| / |τ| := by positivity
    calc ω * |ℓ| * ν / |τ| * r ^ 2 = ω * |ℓ| / |τ| * ν * r ^ 2 := by ring
      _ ≤ ω * |ℓ| / |τ| * r ^ 2 * r ^ 2 := by gcongr
      _ = _ := by ring
  have hEb : ε * (|μ| * r ^ 2 + r ^ 4) ≤ ω * |ℓ| * a / 4 * r ^ 4 := by
    calc ε * (|μ| * r ^ 2 + r ^ 4) ≤ ε * (ω * |ℓ| / |τ| * r ^ 4 + r ^ 4) := by gcongr
      _ = ε * (ω * |ℓ| / |τ| + 1) * r ^ 4 := by ring
      _ ≤ _ := by gcongr
  have h3 : -(|ℓ| * (ω * |ℓ| * a / 4 * r ^ 4)) ≤
      ℓ * (L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4) := by
    have := mul_le_mul_of_nonneg_left (hE.trans hEb) hℓa.le
    rw [← abs_mul] at this
    exact neg_le_of_abs_le this
  have e : ℓ * L = ω * |ℓ| ^ 2 * r ^ 2 * (r ^ 2 - ν) +
      ℓ * (L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4) := by
    have : ℓ * (μ * τ) = -(ω * ℓ ^ 2 * ν) := by rw [hμτ]; ring
    rw [sq_abs]; linear_combination r ^ 2 * this
  have k : ω * |ℓ| ^ 2 * r ^ 2 * (a / 2 * r ^ 2) ≤ ω * |ℓ| ^ 2 * r ^ 2 * (r ^ 2 - ν) := by
    gcongr
  have hr4 : 0 < r ^ 4 := by rw [show r ^ 4 = r ^ 2 * r ^ 2 by ring]; exact mul_pos hr2 hr2
  have k2 : 0 < ω * |ℓ| ^ 2 * a / 4 * r ^ 4 := by apply mul_pos _ hr4; positivity
  rw [e]
  nlinarith [h3, k, k2]

/-- On the side `μ τ l₁ < 0`, inside the annulus (`r² ≤ (1 − a) ν`, `r > 0`), the Lie derivative
has the sign of `−l₁`. -/
@[tmio T, powerlib_foundation] private theorem lie_neg_of_inner {ω τ ℓ μ ε r L ν a : ℝ}
    (hω : 0 < ω) (hℓ : ℓ ≠ 0) (hτ : τ ≠ 0) (hν : 0 < ν) (hμτ : μ * τ = -(ω * ℓ * ν))
    (ha : 0 < a) (hr0 : 0 < r) (hr : r ^ 2 ≤ (1 - a) * ν) (hε0 : 0 ≤ ε)
    (hε : ε * (ω * |ℓ| / |τ| + 1) ≤ ω * |ℓ| * a / 4)
    (hE : |L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4| ≤ ε * (|μ| * r ^ 2 + r ^ 4)) : ℓ * L < 0 := by
  have hℓa : 0 < |ℓ| := abs_pos.mpr hℓ
  have hτa : 0 < |τ| := abs_pos.mpr hτ
  have hμ : |μ| = ω * |ℓ| * ν / |τ| := by
    rw [eq_div_iff hτa.ne', ← abs_mul, hμτ, abs_neg, abs_mul, abs_mul, abs_of_pos hω,
      abs_of_pos hν]
  have hr2 : 0 < r ^ 2 := by positivity
  have hrν : r ^ 2 ≤ ν := le_trans hr (by nlinarith)
  have hgap : a * ν ≤ ν - r ^ 2 := by linarith
  have hμr : |μ| * r ^ 2 ≤ ω * |ℓ| / |τ| * (ν * r ^ 2) := by
    rw [hμ]; apply le_of_eq; ring
  have hEb : ε * (|μ| * r ^ 2 + r ^ 4) ≤ ω * |ℓ| * a / 4 * (ν * r ^ 2) := by
    have hr4 : r ^ 4 ≤ ν * r ^ 2 := by
      rw [show r ^ 4 = r ^ 2 * r ^ 2 by ring]; gcongr
    calc ε * (|μ| * r ^ 2 + r ^ 4) ≤ ε * (ω * |ℓ| / |τ| * (ν * r ^ 2) + ν * r ^ 2) := by
          gcongr
      _ = ε * (ω * |ℓ| / |τ| + 1) * (ν * r ^ 2) := by ring
      _ ≤ _ := by gcongr
  have h3 : ℓ * (L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4) ≤
      |ℓ| * (ω * |ℓ| * a / 4 * (ν * r ^ 2)) := by
    have := mul_le_mul_of_nonneg_left (hE.trans hEb) hℓa.le
    rw [← abs_mul] at this
    exact (le_abs_self _).trans this
  have e : ℓ * L = -(ω * |ℓ| ^ 2 * r ^ 2 * (ν - r ^ 2)) +
      ℓ * (L - μ * τ * r ^ 2 - ω * ℓ * r ^ 4) := by
    have : ℓ * (μ * τ) = -(ω * ℓ ^ 2 * ν) := by rw [hμτ]; ring
    rw [sq_abs]; linear_combination r ^ 2 * this
  have k : ω * |ℓ| ^ 2 * r ^ 2 * (a * ν) ≤ ω * |ℓ| ^ 2 * r ^ 2 * (ν - r ^ 2) := by gcongr
  have k2 : 0 < ω * |ℓ| ^ 2 * a * (ν * r ^ 2) := by positivity
  rw [e]
  nlinarith [h3, k, k2]

/-- The amplitude bounds from the extremal values of `V` along a cycle. -/
@[tmio T, powerlib_foundation] private theorem amplitude_bounds {a η ν R R₁ R₀ v V₁ V₀ : ℝ}
    (ha : 0 < a) (ha8 : a ≤ 1 / 8) (haη : 8 * a ≤ η) (hν : 0 < ν) (hv1 : (1 - a) * R ≤ v)
    (hv2 : v ≤ (1 + a) * R) (hV₁ : v ≤ V₁) (hV₁R : V₁ ≤ (1 + a) * R₁)
    (hR₁ : R₁ < (1 + a) * ν) (hV₀ : V₀ ≤ v) (hV₀R : (1 - a) * R₀ ≤ V₀)
    (hR₀ : (1 - a) * ν < R₀) : (1 - η) * ν ≤ R ∧ R ≤ (1 + η) * ν := by
  have h1a : 0 < 1 - a := by linarith
  have h1a' : 0 < 1 + a := by linarith
  constructor
  · have k1 : (1 - a) ^ 2 * ν < (1 + a) * R := by
      have := mul_lt_mul_of_pos_left hR₀ h1a
      nlinarith
    have k2 : (1 - η) * (1 + a) * ν ≤ (1 - a) ^ 2 * ν := by
      have : (1 - η) * (1 + a) ≤ (1 - a) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hν.le
    by_contra hc
    have := mul_lt_mul_of_pos_left (not_le.mp hc) h1a'
    nlinarith
  · have k1 : (1 - a) * R < (1 + a) ^ 2 * ν := by
      have := mul_lt_mul_of_pos_left hR₁ h1a'
      nlinarith
    have k2 : (1 + a) ^ 2 * ν ≤ (1 + η) * (1 - a) * ν := by
      have : (1 + a) ^ 2 ≤ (1 + η) * (1 - a) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hν.le
    by_contra hc
    have := mul_lt_mul_of_pos_left (not_le.mp hc) h1a
    nlinarith

variable {M : State 2 →L[ℝ] State 2} {Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
  {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)} {ω : ℝ}
  {g : ℝ → State 2 → State 2}

/-- **Every small cycle of the planar family has the Hopf amplitude.** Let the remainder of
`g(μ, u) = R u + μ M u + Q(u, u) + C(u, u, u) + D(μ, u)` be `o(|μ| ‖u‖ + ‖u‖³)` as
`(μ, u) → 0` (no restriction on `μ`), `tr M ≠ 0`, `l₁ ≠ 0`. For every `η > 0` there is `δ > 0`
such that every periodic solution of `g μ`, `|μ| < δ`, staying in the disc of radius `δ` and
avoiding `0`, has `μ tr M l₁ < 0` (there is none for `μ tr M l₁ ≥ 0`, in particular at
`μ = 0`) and `(1 − η) ν ≤ ‖γ(t)‖² ≤ (1 + η) ν`, `ν = −μ tr M/(ω l₁)`. Proof: `V + μW` has, by
`isLittleO_lie_full`, `V̇ ≠ 0` with the sign of `l₁` outside the annulus and of `−l₁` inside; at
the maximum and the minimum of `V` along the cycle `V̇ = 0`, and `V = ‖u‖²(1 + o(1))`. -/
@[tmio T, powerlib_foundation] theorem periodic_amplitude (hω : 0 < ω)
    (h : (fun p : ℝ × State 2 => unfoldRem M Q C ω g p.1 p.2) =o[𝓝 0]
      fun p => |p.1| * ‖p.2‖ + ‖p.2‖ ^ 3)
    (hτ : paramTrace M ≠ 0) (hl : l1 (rotL ω) Q C ω ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ μ, |μ| < δ → ∀ (γ : ℝ → State 2) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt γ (g μ (γ t)) t) → (∀ t, γ (t + T) = γ t) → (∀ t, γ t ≠ 0) →
      (∀ t, ‖γ t‖ < δ) →
      μ * paramTrace M * l1 (rotL ω) Q C ω < 0 ∧ ∀ t,
        (1 - η) * (-(μ * paramTrace M) / (ω * l1 (rotL ω) Q C ω)) ≤ ‖γ t‖ ^ 2 ∧
        ‖γ t‖ ^ 2 ≤ (1 + η) * (-(μ * paramTrace M) / (ω * l1 (rotL ω) Q C ω)) := by
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = paramTrace M := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓd⟩ : ∃ ℓ, ℓ = l1 (rotL ω) Q C ω := ⟨_, rfl⟩
  rw [← hτd] at hτ ⊢
  rw [← hℓd] at hl ⊢
  have hℓa : 0 < |ℓ| := abs_pos.mpr hl
  have hτa : 0 < |τ| := abs_pos.mpr hτ
  obtain ⟨a, ha⟩ : ∃ a, a = min η 1 / 8 := ⟨_, rfl⟩
  have ha0 : 0 < a := ha ▸ by positivity
  have ha8 : a ≤ 1 / 8 := ha ▸ by have := min_le_right η 1; linarith
  have haη : 8 * a ≤ η := ha ▸ by have := min_le_left η 1; linarith
  obtain ⟨K, hK⟩ : ∃ K, K = ω * |ℓ| / |τ| + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := hK ▸ by positivity
  obtain ⟨ε, hε⟩ : ∃ e, e = min (min |τ| (ω * |ℓ|) / 2) (ω * |ℓ| * a / (4 * K)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ min |τ| (ω * |ℓ|) / 2 := hε ▸ min_le_left _ _
  have hετ : ε ≤ |τ| := by
    have := min_le_left |τ| (ω * |ℓ|); linarith
  have hεℓ : ε < ω * |ℓ| := by
    have h1 := min_le_right |τ| (ω * |ℓ|)
    have h2 : 0 < ω * |ℓ| := by positivity
    linarith
  have hεK : ε * (ω * |ℓ| / |τ| + 1) ≤ ω * |ℓ| * a / 4 := by
    have h1 : ε ≤ ω * |ℓ| * a / (4 * K) := hε ▸ min_le_right _ _
    rw [← hK]
    calc ε * K ≤ ω * |ℓ| * a / (4 * K) * K := mul_le_mul_of_nonneg_right h1 hK0.le
      _ = ω * |ℓ| * a / 4 := by field_simp
  -- the two estimates near `0`
  have hlie := isLittleO_lie_full (M := M) (Q := Q) (C := C) (g := g) hω.ne' h
  rw [← hτd, ← hℓd] at hlie
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.eventually_nhds_iff.mp (hlie.def hε0)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.eventually_nhds_iff.mp
    ((isLittleO_hopfV_sub (M := M) (Q := Q) (C := C) hω.ne').def ha0)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun μ hμ γ T hT hγ hγT hγ0 hγδ => ?_⟩
  have hpt : ∀ t, dist (μ, γ t) (0 : ℝ × State 2) < δ₁ ∧
      dist (μ, γ t) (0 : ℝ × State 2) < δ₂ := by
    intro t
    rw [dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
    have h1 := lt_min_iff.mp hμ
    have h2 := lt_min_iff.mp (hγδ t)
    exact ⟨max_lt h1.1 h2.1, max_lt h1.2 h2.2⟩
  have hL : ∀ t, |fderiv ℝ (hopfV M Q C ω μ) (γ t) (g μ (γ t)) - μ * τ * ‖γ t‖ ^ 2 -
      ω * ℓ * ‖γ t‖ ^ 4| ≤ ε * (|μ| * ‖γ t‖ ^ 2 + ‖γ t‖ ^ 4) := by
    intro t
    have := h₁ (hpt t).1
    beta_reduce at this
    rwa [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at this
  have hV : ∀ t, |hopfV M Q C ω μ (γ t) - ‖γ t‖ ^ 2| ≤ a * ‖γ t‖ ^ 2 := by
    intro t
    have := h₂ (hpt t).2
    beta_reduce at this
    rwa [Real.norm_eq_abs, norm_pow, norm_norm] at this
  -- `V` along the cycle and its extremal values
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ, v = fun t => hopfV M Q C ω μ (γ t) := ⟨_, rfl⟩
  have hvd : ∀ t, HasDerivAt v (fderiv ℝ (hopfV M Q C ω μ) (γ t) (g μ (γ t))) t := fun t =>
    hv ▸ ((differentiable_hopfV μ (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t))
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun t => (hvd t).continuousAt
  have hper : Function.Periodic v T := fun t => by rw [hv]; simp only [hγT]
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT.le)
    hvc.continuousOn
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT.le)
    hvc.continuousOn
  have hmax' : ∀ s, v s ≤ v t₁ := fun s => by
    obtain ⟨y, hy, hys⟩ := hper.exists_mem_Ico₀ hT s
    rw [hys]; exact hmax (Ico_subset_Icc_self hy)
  have hmin' : ∀ s, v t₀ ≤ v s := fun s => by
    obtain ⟨y, hy, hys⟩ := hper.exists_mem_Ico₀ hT s
    rw [hys]; exact hmin (Ico_subset_Icc_self hy)
  have hd₁ : fderiv ℝ (hopfV M Q C ω μ) (γ t₁) (g μ (γ t₁)) = 0 :=
    IsLocalMax.hasDerivAt_eq_zero ((isMaxOn_iff.mpr fun s _ => hmax' s).isLocalMax univ_mem)
      (hvd t₁)
  have hd₀ : fderiv ℝ (hopfV M Q C ω μ) (γ t₀) (g μ (γ t₀)) = 0 :=
    IsLocalMin.hasDerivAt_eq_zero ((isMinOn_iff.mpr fun s _ => hmin' s).isLocalMin univ_mem)
      (hvd t₀)
  have hr₁ : 0 < ‖γ t₁‖ := norm_pos_iff.mpr (hγ0 t₁)
  have hr₀ : 0 < ‖γ t₀‖ := norm_pos_iff.mpr (hγ0 t₀)
  -- the side of the bifurcation
  have hside : μ * τ * ℓ < 0 := by
    by_contra hs
    have := lie_pos_of_nonneg hl (not_lt.mp hs) hr₁ hετ hεℓ (hL t₁)
    rw [hd₁, mul_zero] at this
    exact lt_irrefl 0 this
  refine ⟨hside, fun t => ?_⟩
  obtain ⟨ν, hνd⟩ : ∃ ν, ν = -(μ * τ) / (ω * ℓ) := ⟨_, rfl⟩
  rw [← hνd]
  have hν : 0 < ν := by
    have e : ν = -(μ * τ * ℓ) / (ω * ℓ ^ 2) := by rw [hνd]; field_simp
    rw [e]
    exact div_pos (neg_pos.mpr hside) (by positivity)
  have hμτ : μ * τ = -(ω * ℓ * ν) := by rw [hνd]; field_simp
  -- at the maximum and at the minimum of `V`
  have hup : ‖γ t₁‖ ^ 2 < (1 + a) * ν := by
    by_contra hc
    have := lie_pos_of_outer hω hl hτ hν hμτ ha0 (by linarith) (not_lt.mp hc) hε0.le hεK
      (hL t₁)
    rw [hd₁, mul_zero] at this
    exact lt_irrefl 0 this
  have hlo : (1 - a) * ν < ‖γ t₀‖ ^ 2 := by
    by_contra hc
    have := lie_neg_of_inner hω hl hτ hν hμτ ha0 hr₀ (not_lt.mp hc) hε0.le hεK (hL t₀)
    rw [hd₀, mul_zero] at this
    exact lt_irrefl 0 this
  have hVt := abs_le.mp (hV t)
  have hV1 := abs_le.mp (hV t₁)
  have hV0 := abs_le.mp (hV t₀)
  have hm1 := hmax' t
  have hm0 := hmin' t
  rw [hv] at hm1 hm0
  exact amplitude_bounds ha0 ha8 haη hν (by linarith) (by linarith) hm1 (by linarith) hup hm0
    (by linarith) hlo

end Amplitude

end powerlib.Dynamics.PlanarHopf
