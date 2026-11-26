import theorem.Dynamics.CenterReductionBT

/-! # Instability at a Bogdanov–Takens point (foundation)

At an equilibrium of `ẋ = F(x)` on `ℝⁿ` whose linearization has a double zero eigenvalue with a
single Jordan block and the rest of its spectrum in the open left half plane, **Kuznetsov's
coefficient `a = ½⟨p₁, B(q₀, q₀)⟩ ≠ 0` makes the equilibrium Lyapunov unstable**, whatever the
coefficient `b` and the terms of order three and higher: on the centre manifold the field is the
cusp `ẏ₀ = y₁`, `ẏ₁ = a y₀² + b y₀ y₁ + o(‖y‖²)` (in Kuznetsov's transformed coordinates), and
the quadrant `{a y₀ > 0, a y₁ > 0}` repels.

Scope.
* Generic: `State n = ℝⁿ`, a field `F` of class `C²` with `F(0) = 0`, a normalised
  Bogdanov–Takens chain `(q₀, q₁, p₀, p₁)` of `A = DF(0)`
  (`NormalForm.BogdanovTakens.IsBTChain`), every real null vector of `A` a multiple of `q₀` (a
  single Jordan block) and `det(sI − A) = s² r(s)` with `r` Hurwitz; the hypotheses of
  `NormalForm.BogdanovTakens.IsBTChain.exists_centerManifold_btNormalForm`.
* Lyapunov instability only (LeanForControl's `Unstable`). The case `a = 0` (a codimension-three
  degeneracy) is not decided here; eigenvalues in the open right half plane give instability by
  linearization already; other eigenvalues on the imaginary axis are not covered. The planar law
  needs only `o(‖w‖²)` accuracy of the normal form, which is what the reduction delivers: the
  quasi-homogeneous weights `(2, 3)` of `(y₀, y₁)` make `y₁² + a y₀³` dominate every
  remainder. Nothing here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.4 (Lemma 8.7,
the normal form at second order; the cusp of the unfolding at `β = 0`) and §8.7 (the projection
formula for `a`); Takens, "Forced oscillations and bifurcations" (1974) (the 2-jet `(y₁, a y₀²)`,
`a ≠ 0`, is a cusp); Carr, *Applications of Centre Manifold Theory* (1981), §2.4 (the reduction
principle); Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.3 (Chetaev). The centre manifold and
the normal form are `NormalForm.BogdanovTakens.IsBTChain.exists_centerManifold_btNormalForm`
(`theorem/Dynamics/CenterReductionBT.lean`), the Chetaev law is
`Dynamics.unstable_of_chetaev_lipschitzOn` (`theorem/Dynamics/Instability.lean`) and the
instability transfer is `Dynamics.CenterManifold.unstable_of_unstable_chartField`
(`theorem/Dynamics/CenterReduction.lean`).

Results.
* `Dynamics.CenterManifold.btChetaev_pos`: the real inequality behind the Chetaev function: for
  `u, v > 0` small, `v² + |a| u³ − |b| u² v − (u + v) E > 0` whenever `E ≤ (|a|/8)(u² + v²)`.
* **`Dynamics.CenterManifold.unstable_of_btNormalForm_isLittleO`** (the planar law): a planar
  field `G`, Lipschitz near `0`, carried by a quadratic near-identity map `Φ(w) = w + H(w, w)` to
  the truncated normal form up to `o(‖w‖²)` (`DΦ(w) G(w) − N_{a,b}(Φ(w)) = o(‖w‖²)`), with
  `a ≠ 0`, is unstable at `0`. Chetaev function `V(w) = (a Φ(w)₀)₊² (a Φ(w)₁)₊²` (`C¹` by
  `Dynamics.contDiff_one_sq_max_zero`, `theorem/Dynamics/Lyapunov.lean`): positive exactly
  where `Φ(w)` lies in the open quadrant `{a y₀ > 0, a y₁ > 0}`, where
  `V̇ = 2a⁴ y₀ y₁ (y₁² + a y₀³ + b y₀² y₁ + o(‖y‖³)) > 0`; the transformed coordinates enter only
  through `V = W ∘ Φ`, no inverse of `Φ` is needed.
* **`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`** (the law in `ℝⁿ`): under
  the hypotheses of the reduction, `coeffA F 0 q₀ p₁ ≠ 0` ⇒ `Unstable F 0`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold
open Set Filter Topology Asymptotics
open powerlib.PhasePlane (mk mk_apply_zero mk_apply_one norm_sq_eq)

/-! ## The planar law -/

/-- **The Chetaev inequality of the cusp.** For `A > 0`, `u, v > 0` with `u, v ≤ δ`,
`2 (A/8) δ ≤ 1/4`, `(B + A/8)² δ ≤ A/4` and `E ≤ (A/8)(u² + v²)`:
`v² + A u³ − B u² v − (u + v) E > 0` (`v²` and `A u³` dominate). -/
@[tmio T, powerlib_foundation] theorem btChetaev_pos {A B δ u v E : ℝ} (hA : 0 < A)
    (hδ1 : 2 * (A / 8) * δ ≤ 1 / 4) (hδ2 : (B + A / 8) ^ 2 * δ ≤ A / 4)
    (hu : 0 < u) (hv : 0 < v) (huδ : u ≤ δ) (hvδ : v ≤ δ)
    (hE : E ≤ A / 8 * (u ^ 2 + v ^ 2)) :
    0 < v ^ 2 + A * u ^ 3 - B * u ^ 2 * v - (u + v) * E := by
  set c := A / 8 with hc
  have hc0 : 0 < c := by positivity
  have h1 : (u + v) * E ≤ c * u ^ 3 + c * u ^ 2 * v + c * v ^ 2 * (u + v) := by
    have := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ u + v)
    nlinarith
  have h2 : c * v ^ 2 * (u + v) ≤ v ^ 2 / 4 := by
    have : c * (u + v) ≤ 1 / 4 := by nlinarith
    nlinarith [sq_nonneg v]
  have h3 : (B + c) * u ^ 2 * v ≤ v ^ 2 / 4 + (B + c) ^ 2 * u ^ 4 := by
    nlinarith [sq_nonneg (v / 2 - (B + c) * u ^ 2)]
  have h4 : (B + c) ^ 2 * u ^ 4 ≤ A / 4 * u ^ 3 := by
    have : (B + c) ^ 2 * u ≤ A / 4 := (mul_le_mul_of_nonneg_left huδ (sq_nonneg _)).trans hδ2
    nlinarith [pow_pos hu 3]
  have h5 : 0 < v ^ 2 / 2 + 5 * A / 8 * u ^ 3 := by positivity
  nlinarith

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_btW (a : ℝ) (y : State 2) :
    HasFDerivAt (fun y : State 2 => max (a * y 0) 0 ^ 2 * max (a * y 1) 0 ^ 2)
      (max (a * y 0) 0 ^ 2 • ((2 * max (a * y 1) 0) • (a • coord 1)) +
        max (a * y 1) 0 ^ 2 • ((2 * max (a * y 0) 0) • (a • coord 0))) y := by
  have h0 := (hasDerivAt_sq_max_zero (a * y 0)).comp_hasFDerivAt y
    ((hasFDerivAt_coord 0 y).const_mul a)
  have h1 := (hasDerivAt_sq_max_zero (a * y 1)).comp_hasFDerivAt y
    ((hasFDerivAt_coord 1 y).const_mul a)
  exact h0.mul h1

@[tmio T, powerlib_foundation] private theorem contDiff_btW (a : ℝ) :
    ContDiff ℝ 1 (fun y : State 2 => max (a * y 0) 0 ^ 2 * max (a * y 1) 0 ^ 2) := by
  have h0 : ContDiff ℝ 1 (fun y : State 2 => a * y 0) := by fun_prop
  have h1 : ContDiff ℝ 1 (fun y : State 2 => a * y 1) := by fun_prop
  exact (contDiff_one_sq_max_zero.comp h0).mul (contDiff_one_sq_max_zero.comp h1)

@[tmio T, powerlib_foundation] private theorem contDiff_quadMap
    (H : State 2 →L[ℝ] State 2 →L[ℝ] State 2) : ContDiff ℝ 1 (quadMap H) :=
  contDiff_id.add (H.contDiff.clm_apply contDiff_id)

/-- **Instability of the Bogdanov–Takens cusp in transformed coordinates** (the planar law). Let
`G` be a planar field, Lipschitz on a neighbourhood of `0`, and `Φ(w) = w + H(w, w)` a quadratic
near-identity map carrying it to the truncated normal form up to `o(‖w‖²)`:
`DΦ(w) G(w) − N_{a,b}(Φ(w)) = o(‖w‖²)`, `N_{a,b}(y) = (y₁, a y₀² + b y₀ y₁)`. If `a ≠ 0`, `0`
is unstable: `V(w) = (a Φ(w)₀)₊² (a Φ(w)₁)₊²` is positive at points `t (1/a, 1/a)`, `t ↓ 0`, and
`V̇ = 2a² (aΦ₀)(aΦ₁) (y₁² + a y₀³ + b y₀² y₁ + ⟨(y₁, y₀), o(‖y‖²)⟩) > 0` wherever `V > 0` near
`0` (`btChetaev_pos`; Chetaev, `Dynamics.unstable_of_chetaev_lipschitzOn`). -/
@[tmio T, powerlib_foundation] theorem unstable_of_btNormalForm_isLittleO
    {G : State 2 → State 2} {U : Set (State 2)} {K : NNReal} (hU : U ∈ 𝓝 0)
    (hG : LipschitzOnWith K G U) (H : State 2 →L[ℝ] State 2 →L[ℝ] State 2) {a b : ℝ}
    (ha : a ≠ 0)
    (hexp : (fun w => fderiv ℝ (quadMap H) w (G w) -
      NormalForm.BogdanovTakens.field ⟨0, 0, a, b⟩ (quadMap H w)) =o[𝓝 0]
        fun w => ‖w‖ ^ 2) :
    Unstable G 0 := by
  set A := |a| with hAdef
  have hA : 0 < A := abs_pos.mpr ha
  set B := |b| with hBdef
  have hBc : 0 < B + A / 8 := by positivity
  set δ := min (1 / A) (A / (4 * (B + A / 8) ^ 2)) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : 2 * (A / 8) * δ ≤ 1 / 4 := by
    have : δ ≤ 1 / A := min_le_left _ _
    calc 2 * (A / 8) * δ ≤ 2 * (A / 8) * (1 / A) := by gcongr
      _ = 1 / 4 := by field_simp; norm_num
  have hδ2 : (B + A / 8) ^ 2 * δ ≤ A / 4 := by
    have : δ ≤ A / (4 * (B + A / 8) ^ 2) := min_le_right _ _
    have hBc2 : (B + A / 8) ^ 2 ≠ 0 := by positivity
    have h8 : B * 8 + A ≠ 0 := by positivity
    calc (B + A / 8) ^ 2 * δ ≤ (B + A / 8) ^ 2 * (A / (4 * (B + A / 8) ^ 2)) := by gcongr
      _ = A / 4 := by field_simp
  obtain ⟨r₁, hr₁, hb⟩ := Metric.eventually_nhds_iff.mp (hexp.def (by positivity : 0 < A / 32))
  set r₀ := 1 / (2 * (‖H‖ + 1)) with hr₀
  have hr₀0 : 0 < r₀ := by positivity
  set r := min (r₁ / 2) (min r₀ (δ / 2)) with hrdef
  have hr : 0 < r := lt_min (by positivity) (lt_min hr₀0 (by positivity))
  set W : State 2 → ℝ := fun y => max (a * y 0) 0 ^ 2 * max (a * y 1) 0 ^ 2 with hWdef
  have hWc : ContDiff ℝ 1 W := contDiff_btW a
  have hΦc := contDiff_quadMap H
  have hpos : ∀ y : State 2, 0 < W y → 0 < a * y 0 ∧ 0 < a * y 1 := by
    intro y hy
    by_contra hne
    rw [not_and_or, not_lt, not_lt] at hne
    rcases hne with h | h
    · have : W y = 0 := by simp [hWdef, max_eq_right h]
      linarith
    · have : W y = 0 := by simp [hWdef, max_eq_right h]
      linarith
  refine unstable_of_chetaev_lipschitzOn (W := fun w => W (quadMap H w)) (r := r) hU hG
    (hWc.comp hΦc) hr (fun ε hε => ?_) (fun w hw hWw => ?_)
  · -- seeds `t (1/a, 1/a)`
    set z : State 2 := mk (1 / a) (1 / a) with hz
    set c₀ := a * H z z 0
    set c₁ := a * H z z 1
    set t := min (ε / (‖z‖ + 1)) (1 / (|c₀| + |c₁| + 1)) / 2 with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t < ε / (‖z‖ + 1) := by
      have := min_le_left (ε / (‖z‖ + 1)) (1 / (|c₀| + |c₁| + 1))
      have : 0 < ε / (‖z‖ + 1) := by positivity
      linarith
    have ht2 : t * (|c₀| + |c₁| + 1) < 1 := by
      have h1 := min_le_right (ε / (‖z‖ + 1)) (1 / (|c₀| + |c₁| + 1))
      have h2 : t < 1 / (|c₀| + |c₁| + 1) := by
        have : 0 < 1 / (|c₀| + |c₁| + 1) := by positivity
        linarith
      rwa [lt_div_iff₀ (by positivity)] at h2
    have hq : quadMap H (t • z) = t • z + (t * t) • H z z := by
      simp only [quadMap, map_smul, smul_apply, smul_smul]
    have hc0 : 0 < a * quadMap H (t • z) 0 := by
      rw [hq]
      have e : a * (t • z + (t * t) • H z z) 0 = t + t * t * c₀ := by
        simp [hz, c₀]; field_simp
      rw [e]
      have : -(t * |c₀|) ≤ t * c₀ := by
        have := neg_abs_le c₀; nlinarith
      nlinarith [abs_nonneg c₁]
    have hc1 : 0 < a * quadMap H (t • z) 1 := by
      rw [hq]
      have e : a * (t • z + (t * t) • H z z) 1 = t + t * t * c₁ := by
        simp [hz, c₁]; field_simp
      rw [e]
      have : -(t * |c₁|) ≤ t * c₁ := by
        have := neg_abs_le c₁; nlinarith
      nlinarith [abs_nonneg c₀]
    refine ⟨t • z, ?_, ?_⟩
    · rw [sub_zero, norm_smul, Real.norm_of_nonneg ht0.le]
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖z‖ + 1)).mp ht1
      nlinarith [norm_nonneg z]
    · show 0 < max (a * quadMap H (t • z) 0) 0 ^ 2 * max (a * quadMap H (t • z) 1) 0 ^ 2
      rw [max_eq_left hc0.le, max_eq_left hc1.le]
      positivity
  · -- the Lie derivative
    rw [sub_zero] at hw
    set y := quadMap H w with hy
    obtain ⟨hp, hq⟩ := hpos y hWw
    have hd : fderiv ℝ (fun w => W (quadMap H w)) w (G w) =
        fderiv ℝ W y (fderiv ℝ (quadMap H) w (G w)) := by
      have h := fderiv_comp (g := W) (f := quadMap H) w
        ((hWc.differentiable one_ne_zero) _) ((hΦc.differentiable one_ne_zero) w)
      rw [show (fun w => W (quadMap H w)) = W ∘ quadMap H from rfl, h]
      rfl
    set v := fderiv ℝ (quadMap H) w (G w) with hv
    set e := v - NormalForm.BogdanovTakens.field ⟨0, 0, a, b⟩ y with he
    have hv0 : v 0 = y 1 + e 0 := by
      simp [he, NormalForm.BogdanovTakens.field]
    have hv1 : v 1 = a * y 0 ^ 2 + b * y 0 * y 1 + e 1 := by
      simp [he, NormalForm.BogdanovTakens.field]
    rw [hd, (hasFDerivAt_btW a y).fderiv]
    simp only [add_apply, smul_apply, coord_apply, smul_eq_mul]
    rw [max_eq_left hp.le, max_eq_left hq.le, hv0, hv1]
    -- the bounds
    have hrw : ‖w‖ ≤ r := hw
    have hHw : ‖H w w‖ ≤ ‖w‖ / 2 := by
      have h1 := H.le_opNorm₂ w w
      have h2 : ‖w‖ ≤ r₀ :=
        hrw.trans ((min_le_right (r₁ / 2) (min r₀ (δ / 2))).trans (min_le_left r₀ (δ / 2)))
      have h3 : ‖H‖ * ‖w‖ ≤ 1 / 2 := by
        have : (‖H‖ + 1) * ‖w‖ ≤ 1 / 2 := by
          calc (‖H‖ + 1) * ‖w‖ ≤ (‖H‖ + 1) * r₀ := by gcongr
            _ = 1 / 2 := by rw [hr₀]; field_simp
        linarith [norm_nonneg w]
      calc ‖H w w‖ ≤ ‖H‖ * ‖w‖ * ‖w‖ := h1
        _ ≤ 1 / 2 * ‖w‖ := by gcongr
        _ = ‖w‖ / 2 := by ring
    have hyw : ‖y‖ ≤ 3 / 2 * ‖w‖ := by
      calc ‖y‖ = ‖w + H w w‖ := rfl
        _ ≤ ‖w‖ + ‖H w w‖ := norm_add_le _ _
        _ ≤ 3 / 2 * ‖w‖ := by linarith
    have hwy : ‖w‖ ≤ 2 * ‖y‖ := by
      have : ‖w‖ ≤ ‖y‖ + ‖H w w‖ := by
        calc ‖w‖ = ‖y - H w w‖ := by rw [hy, quadMap, add_sub_cancel_right]
          _ ≤ ‖y‖ + ‖H w w‖ := norm_sub_le _ _
      linarith
    have hyδ : ‖y‖ ≤ δ := by
      have : ‖w‖ ≤ δ / 2 :=
        hrw.trans ((min_le_right (r₁ / 2) (min r₀ (δ / 2))).trans (min_le_right r₀ (δ / 2)))
      linarith [norm_nonneg w]
    have he' : ‖e‖ ≤ A / 32 * ‖w‖ ^ 2 := by
      have h : ‖fderiv ℝ (quadMap H) w (G w) -
          NormalForm.BogdanovTakens.field ⟨0, 0, a, b⟩ (quadMap H w)‖ ≤ A / 32 * ‖‖w‖ ^ 2‖ :=
        hb (show dist w 0 < r₁ by
          rw [dist_zero_right]
          have : ‖w‖ ≤ r₁ / 2 := hrw.trans (min_le_left (r₁ / 2) (min r₀ (δ / 2)))
          linarith)
      rw [norm_pow, norm_norm] at h
      exact h
    have hyn := norm_sq_eq y
    have heA : ‖e‖ ≤ A / 8 * (|y 0| ^ 2 + |y 1| ^ 2) := by
      rw [sq_abs, sq_abs, ← hyn]
      have h4 : ‖w‖ ^ 2 ≤ 4 * ‖y‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg w) hwy 2
        linarith
      calc ‖e‖ ≤ A / 32 * ‖w‖ ^ 2 := he'
        _ ≤ A / 32 * (4 * ‖y‖ ^ 2) := by gcongr
        _ = A / 8 * ‖y‖ ^ 2 := by ring
    have hu : 0 < |y 0| := abs_pos.mpr (fun h => by rw [h, mul_zero] at hp; exact lt_irrefl 0 hp)
    have hv' : 0 < |y 1| := abs_pos.mpr (fun h => by rw [h, mul_zero] at hq; exact lt_irrefl 0 hq)
    have hS := btChetaev_pos (B := B) hA hδ1 hδ2 hu hv' ((abs_apply_le_norm y 0).trans hyδ)
      ((abs_apply_le_norm y 1).trans hyδ) heA
    -- `S = y₁ v₀ + y₀ v₁` dominates the Chetaev bound
    have ha3 : a * y 0 ^ 3 = A * |y 0| ^ 3 := by
      have : a * y 0 = A * |y 0| := by rw [hAdef, ← abs_mul, abs_of_pos hp]
      have e3 : |y 0| ^ 3 = |y 0| * y 0 ^ 2 := by rw [pow_succ', sq_abs]
      rw [e3]; linear_combination y 0 ^ 2 * this
    have hb3 : -(B * |y 0| ^ 2 * |y 1|) ≤ b * y 0 ^ 2 * y 1 := by
      have := neg_abs_le (b * y 0 ^ 2 * y 1)
      rwa [abs_mul, abs_mul, abs_pow] at this
    have he0 : -(|y 1| * ‖e‖) ≤ y 1 * e 0 := by
      have h1 := neg_abs_le (y 1 * e 0)
      have h2 : |y 1 * e 0| ≤ |y 1| * ‖e‖ := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_apply_le_norm e 0) (abs_nonneg _)
      linarith
    have he1 : -(|y 0| * ‖e‖) ≤ y 0 * e 1 := by
      have h1 := neg_abs_le (y 0 * e 1)
      have h2 : |y 0 * e 1| ≤ |y 0| * ‖e‖ := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_apply_le_norm e 1) (abs_nonneg _)
      linarith
    have hS' : 0 < y 1 * (y 1 + e 0) + y 0 * (a * y 0 ^ 2 + b * y 0 * y 1 + e 1) := by
      have e1 : y 1 * (y 1 + e 0) + y 0 * (a * y 0 ^ 2 + b * y 0 * y 1 + e 1) =
          |y 1| ^ 2 + a * y 0 ^ 3 + b * y 0 ^ 2 * y 1 + (y 1 * e 0 + y 0 * e 1) := by
        rw [sq_abs]; ring
      rw [e1, ha3]
      linarith
    have hpq : 0 < a * y 0 * (a * y 1) := mul_pos hp hq
    have hfin : 2 * a * ((a * y 0) ^ 2 * (a * y 1) * (a * y 0 ^ 2 + b * y 0 * y 1 + e 1) +
        (a * y 1) ^ 2 * (a * y 0) * (y 1 + e 0)) =
        2 * a ^ 2 * (a * y 0 * (a * y 1)) *
          (y 1 * (y 1 + e 0) + y 0 * (a * y 0 ^ 2 + b * y 0 * y 1 + e 1)) := by ring
    have ha2 : 0 < a ^ 2 := by positivity
    linarith [mul_pos (mul_pos (mul_pos two_pos ha2) hpq) hS']

end powerlib.Dynamics.CenterManifold

/-! ## The law in `ℝⁿ` -/

namespace powerlib.NormalForm.BogdanovTakens
open Set Filter Topology Asymptotics Polynomial
open powerlib.Dynamics (State)
open powerlib.Dynamics.CenterManifold
open powerlib.NormalForm.LyapunovCoefficient (cmat)

variable {n : ℕ} {q₀ q₁ p₀ p₁ : State n}

/-- **A Bogdanov–Takens point with `a ≠ 0` is unstable.** Let `F` be of class `C²` with
`F(0) = 0`, `(q₀, q₁, p₀, p₁)` a normalised Bogdanov–Takens chain of `A = DF(0)`, every real null
vector of `A` a multiple of `q₀`, and `det(sI − A) = s² r(s)` with every root of `r` in the open
left half plane. If Kuznetsov's coefficient `a = ½⟨p₁, D²F(0)(q₀, q₀)⟩` (`coeffA`) is nonzero, the
origin is unstable, for every value of `b` and every term of order three: the centre manifold
carries the truncated normal form after Kuznetsov's change of coordinates
(`IsBTChain.exists_centerManifold_btNormalForm`), the reduced field is unstable
(`Dynamics.CenterManifold.unstable_of_btNormalForm_isLittleO`) and instability transfers to the
full field (`Dynamics.CenterManifold.unstable_of_unstable_chartField`). -/
@[tmio T, powerlib_foundation] theorem IsBTChain.unstable_of_coeffA_ne_zero
    {F : State n → State n} (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (hc : IsBTChain (fderiv ℝ F 0) q₀ q₁ p₀ p₁)
    (hker : ∀ v, fderiv ℝ F 0 v = 0 → ∃ s : ℝ, v = s • q₀) {r : ℂ[X]}
    (hchar : (cmat (fderiv ℝ F 0)).charpoly = X ^ 2 * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (ha : coeffA F 0 q₀ p₁ ≠ 0) :
    Unstable F 0 := by
  obtain ⟨ρ, hρ, h, L, hgm, hL, -, -, -, hinv, hnf⟩ :=
    hc.exists_centerManifold_btNormalForm hF hF0 hker hchar hr
  set A := fderiv ℝ F 0 with hAdef
  set f : State n → State n := fun x => F x - A x with hfdef
  have hFf : fullField A f = F := by funext x; simp [fullField, hfdef]
  have hP := hc.isCommutingProjection
  have hcc := hc.isChart
  have hf1 : ContDiff ℝ 1 f := (hF.of_le (by norm_num)).sub A.contDiff
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf1
  set r₁ := R₀ / ((1 + L) * (‖btι q₀ q₁‖ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁R : (1 + L) * ‖btι q₀ q₁‖ * r₁ ≤ R₀ := by
    have : (1 + L) * ‖btι q₀ q₁‖ * r₁ ≤ (1 + L) * (‖btι q₀ q₁‖ + 1) * r₁ := by
      gcongr; linarith
    refine this.trans (le_of_eq ?_)
    rw [hr₁]; field_simp
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := A) (π := btπ p₀ p₁) hgm.map_zero
    hL hLf hr₁R
  have hπh : ∀ u, btπ p₀ p₁ (h u) = 0 := fun u => by
    rw [← hcc.π_proj, hgm.proj_apply, map_zero]
  have hcf : ∀ w, chartField A f h (btι q₀ q₁) (btπ p₀ p₁) w =
      btπ p₀ p₁ (F (btι q₀ q₁ w + h (btι q₀ q₁ w))) := by
    intro w
    simp only [chartField, hfdef, map_add, map_sub]
    rw [hc.btπ_map (h (btι q₀ q₁ w)), hπh, map_zero]
    abel
  have hred : Unstable (chartField A f h (btι q₀ q₁) (btπ p₀ p₁)) 0 := by
    refine unstable_of_btNormalForm_isLittleO (b := coeffB F 0 q₀ q₁ p₀ p₁)
      (Metric.closedBall_mem_nhds 0 hr₁0) hLg (btTransform (btQuad F q₀ q₁ p₀ p₁)) ha
      (hnf.congr_left fun w => ?_)
    rw [hcf]
    rfl
  rw [← hFf]
  refine unstable_of_unstable_chartField hP hgm hL hcc hf1 hρ ?_ hred
  rw [hFf]
  exact hinv

end powerlib.NormalForm.BogdanovTakens
