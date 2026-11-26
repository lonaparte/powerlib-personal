import theorem.GridTiedConverter.GFM.DCLink.VSMDCPlane
import theorem.NormalForm.DynamicFold

/-! # The VSM–DC model at the balance of its invariant singular plane: escape along a cone

Model boundary.
The VSM–DC family `VSMDC.family` of `theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`, read at
selected points `(δ*, 0, V*, ζ*)` with `V* = 0` as in
`theorem/GridTiedConverter/GFM/DCLink/VSMDCPlane.lean`: state `x = (δ, ω, V, ζ)`, continuous
time, autonomous; quasi-static line `P_e(δ) = c₀ + A sin(δ − α)`, constant EMF magnitude, affine
DC source `P_src(V) = P_s + I_s V`, DC node `C V̇ = (P_src(V) − P_e(δ))/V` (read with Lean's
`x / 0 = 0` on the plane `V = 0`), DC-voltage PI loop `P_ref = P_ff + K_p (V − V*) + K_i ζ`,
`ζ̇ = V − V*`; export-positive power; parameters arbitrary reals. The module treats the plane when
it is invariant (`I_s/C = 0`), in particular at the degenerate balance
`P_s = P_e(δ*) = P_ff + K_i ζ*` with `C ≠ 0` (so `I_s = 0`). The physical limit (overmodulation,
reached before `V = 0`) is not modelled; excluded as in `VSMDC.lean`. Level: Lyapunov stability
and instability of the selected point.

Source: GFM counterpart study, note T7 part (c) (`t7-dcside`, the singular plane; notes outside
the repository). The escape is found by a quasi-homogeneous (weighted) blow-up of the degenerate
point, weights `θ : 5`, `ω : 4`, `V : 3`, time `1` (Dumortier, Llibre and Artés, *Qualitative
Theory of Planar Differential Systems*, Springer, 2006, Chapter 3); the normalisation and the
rate identity were derived with exact rational computer algebra (sympy, outside the repository) and
are proved here. Instability from a trapping region: `Dynamics.Degenerate.unstable_of_barriers`
(`theorem/Dynamics/Degenerate/PlaneCollapse.lean`; Khalil, *Nonlinear Systems*, 3rd ed., 2002,
Theorem 4.3, Chetaev's argument).

Results.
* Implementation evidence (private): the smooth cutoff `coneCut` and the `C¹` radius
  `coneRadius` (`(σ V)^{1/3}` where `σ V ≥ 2c`), the barrier `coneW`
  `1/100 − 4 ξ² − 5 η² − 10 ν²` in the normalised coordinates
  `ξ = θ/(X* r⁵) − 1`, `η = ω/(Y* r⁴) − 1`, `ν = (K_i/K_p) σ (ζ − ζ*)/r³` (`θ = δ − δ*`,
  `r = (σ V)^{1/3}`), its rate `coneRate` (`fderiv_coneW`), the rate identity and inequality
  (`coneRate_pos`, `cone_ineq`: the blown-up field is a hyperbolic sink in `(ξ, η, ν)` with
  eigenvalues `−1`, `−7/3 ± i √11/3` after normalisation while `r` grows; damping, the curvature of
  the power curve and the integrator enter at `O(r)`, `pert_*`), the normalisation
  `cone_constants` (`a > 0`, `a³ = −(9/20) σ (K_p/M)(k(δ*)/C)`, `X* = −a C/k(δ*)`,
  `Y* = (5/3) a X*`, so `K_p = σ (20/9) a² X* M`; cube roots from
  `NormalForm.DynamicFold.cbrt_pow`) and the trapping region `cone_region`.

Family and connection conclusions (selected points with `V* = 0`, `VSMDC.family`).
* `VSMDC.mem_den_unstable_of_invariant_cone`: at the degenerate balance of the invariant plane
  (`I_s/C = 0`, `C ≠ 0`, `P_s = P_e(δ*) = P_ff + K_i ζ*`) with `M ≠ 0`, `k(δ*) ≠ 0` and a
  proportional DC gain `K_p ≠ 0` the point is unstable, whatever `D` and `K_i` (in particular for
  DC gains of opposite signs, `K_p K_i < 0`, the case left open in `VSMDCPlane.lean`): on the side
  `σ V > 0` with `σ K_p k(δ*)/(M C) < 0` solutions starting on the self-similar curve
  `(δ* + X* s⁵, Y* s⁴, σ s³, ζ*)` stay in the cone `coneW ≥ 0` while `σ V` grows at a uniform rate.
* `VSMDC.mem_den_unstable_of_invariant_balance`: with `V* = 0`, `I_s/C = 0` and
  `(P_s − P_e(δ*))/C = 0` every selected point is unstable (the cone together with the cases of
  `VSMDCPlane.lean`).
* **Complete decision on the invariant plane.**
  `VSMDC.mem_den_lyapunovStable_iff_of_invariant_plane`: with `V* = 0` and `I_s/C = 0`, Lyapunov
  stable iff `(P_s − P_e(δ*))/C < 0`, `(P_ff + K_i ζ* − P_e(δ*))/M = 0` and either `0 ≤ D/M`,
  `0 < k(δ*)/M` or `A = 0`, `K_i = 0`, `0 < D/M`. With
  `VSMDC.mem_den_lyapunovStable_iff_of_V_eq_zero` (`I_s/C ≠ 0`) Lyapunov stability is decided at
  every selected point of the singular plane.
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter Topology
open powerlib.Dynamics (State coord)

namespace VSMDC

/-- A negative number has a negative cube root. -/
@[tmio T, powerlib_foundation] private theorem exists_cube_root_of_neg {p : ℝ} (hp : p < 0) :
    ∃ m : ℝ, m < 0 ∧ m ^ 3 = p := by
  refine ⟨-((-p) ^ ((1 : ℝ) / 3)), neg_neg_of_pos (Real.rpow_pos_of_pos (by linarith) _), ?_⟩
  rw [neg_pow, (NormalForm.DynamicFold.cbrt_pow (by linarith)).1]
  ring

/-- A smooth lower cutoff at level `c > 0`: `c + (v − c) S((v − c)/c)` with Mathlib's smooth
transition `S`; it is `≥ c` everywhere and equals `v` for `v ≥ 2c`. -/
private def coneCut (c v : ℝ) : ℝ := c + (v - c) * Real.smoothTransition ((v - c) / c)

@[tmio T, powerlib_foundation] private theorem contDiff_coneCut (c : ℝ) :
    ContDiff ℝ 1 (coneCut c) := by
  unfold coneCut
  have h1 : ContDiff ℝ 1 (fun v : ℝ => (v - c) / c) :=
    (contDiff_id.sub contDiff_const).div_const c
  have h2 : ContDiff ℝ 1 (fun v : ℝ => Real.smoothTransition ((v - c) / c)) :=
    Real.smoothTransition.contDiff.comp h1
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul h2)

@[tmio T, powerlib_foundation] private theorem le_coneCut {c : ℝ} (hc : 0 < c) (v : ℝ) :
    c ≤ coneCut c v := by
  unfold coneCut
  rcases le_or_gt v c with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      hc.le)]
    simp
  · have := Real.smoothTransition.nonneg ((v - c) / c)
    nlinarith

@[tmio T, powerlib_foundation] private theorem coneCut_eq {c v : ℝ} (hc : 0 < c)
    (hv : 2 * c ≤ v) : coneCut c v = v := by
  unfold coneCut
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc]; linarith)]
  ring

/-- The radius `r = (σ V)^{1/3}`, cut off below at `c^{1/3}`: a `C¹` positive function of the
state that equals `(σ y_V)^{1/3}` where `σ y_V ≥ 2c`. -/
private def coneRadius (σ c : ℝ) (y : State 4) : ℝ := coneCut c (σ * y 2) ^ ((1 : ℝ) / 3)

@[tmio T, powerlib_foundation] private theorem coneRadius_pos {σ c : ℝ} (hc : 0 < c)
    (y : State 4) : 0 < coneRadius σ c y :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le hc (le_coneCut hc _)) _

@[tmio T, powerlib_foundation] private theorem contDiff_coneRadius (σ : ℝ) {c : ℝ}
    (hc : 0 < c) : ContDiff ℝ 1 (coneRadius σ c) := by
  unfold coneRadius
  have h1 : ContDiff ℝ 1 (fun y : State 4 => coneCut c (σ * y 2)) :=
    (contDiff_coneCut c).comp (contDiff_const.mul (Dynamics.contDiff_coord 2))
  exact h1.rpow_const_of_ne fun y => (lt_of_lt_of_le hc (le_coneCut hc _)).ne'

/-- Where `σ y_V > 2c` the radius is `(σ y_V)^{1/3}`, with derivative `σ dV/(3 r²)`. -/
@[tmio T, powerlib_foundation] private theorem hasFDerivAt_coneRadius {σ c : ℝ} (hc : 0 < c)
    {y : State 4} (hy : 2 * c < σ * y 2) :
    HasFDerivAt (coneRadius σ c)
      ((σ / (3 * ((σ * y 2) ^ ((1 : ℝ) / 3)) ^ 2)) • coord 2) y ∧
      coneRadius σ c y = (σ * y 2) ^ ((1 : ℝ) / 3) := by
  have hpos : 0 < σ * y 2 := by linarith
  set r := (σ * y 2) ^ ((1 : ℝ) / 3) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hpos _
  have hr3 : r ^ 3 = σ * y 2 := (NormalForm.DynamicFold.cbrt_pow hpos.le).1
  have hev : coneRadius σ c =ᶠ[𝓝 y] fun y : State 4 => (σ * y 2) ^ ((1 : ℝ) / 3) := by
    have ho : IsOpen {y : State 4 | 2 * c < σ * y 2} :=
      isOpen_lt continuous_const (continuous_const.mul (coord (2 : Fin 4)).continuous)
    filter_upwards [ho.mem_nhds hy] with z hz
    simp only [coneRadius, coneCut_eq hc (le_of_lt hz)]
  have h2 : HasFDerivAt (fun y : State 4 => σ * y 2) (σ • coord 2) y :=
    (Dynamics.hasFDerivAt_coord 2 y).const_mul σ
  have h3 := h2.rpow_const (p := ((1 : ℝ) / 3)) (Or.inl hpos.ne')
  have hd : 1 / 3 * (σ * y 2) ^ ((1 : ℝ) / 3 - 1) = 1 / (3 * r ^ 2) := by
    rw [Real.rpow_sub hpos, Real.rpow_one, ← hr, ← hr3]
    field_simp
  refine ⟨(h3.congr_of_eventuallyEq hev).congr_fderiv ?_, by
    rw [coneRadius, coneCut_eq hc hy.le]⟩
  rw [hd, smul_smul]
  congr 1
  field_simp

/-- The barrier of the cone: `1/100 − 4 (ξ)² − 5 (η)² − 10 ν²` in the normalised coordinates
`ξ = θ/(X* r⁵) − 1`, `η = ω/(Y* r⁴) − 1`, `ν = q σ (ζ − ζ*)/r³`, `r = g(y)`. -/
private def coneW (Xs Ys qs δs ζs : ℝ) (g : State 4 → ℝ) (y : State 4) : ℝ :=
  1 / 100 - 4 * ((y 0 - δs) / (Xs * g y ^ 5) - 1) ^ 2 - 5 * (y 1 / (Ys * g y ^ 4) - 1) ^ 2 -
    10 * (qs * (y 3 - ζs) / g y ^ 3) ^ 2

/-- The rate of `coneW` along a vector `v`, with `L` the rate of the radius `r`. -/
private def coneRate (Xs Ys qs r θ ω z v0 v1 v3 L : ℝ) : ℝ :=
  -8 * (θ / (Xs * r ^ 5) - 1) * (v0 / (Xs * r ^ 5) - 5 * (θ / (Xs * r ^ 5)) * L / r) -
    10 * (ω / (Ys * r ^ 4) - 1) * (v1 / (Ys * r ^ 4) - 4 * (ω / (Ys * r ^ 4)) * L / r) -
    20 * (qs * z / r ^ 3) * (qs * v3 / r ^ 3 - 3 * (qs * z / r ^ 3) * L / r)

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_div_aux {c d : State 4 → ℝ}
    {c' d' : State 4 →L[ℝ] ℝ} {y : State 4} (hc : HasFDerivAt c c' y) (hd : HasFDerivAt d d' y)
    (hy : d y ≠ 0) :
    HasFDerivAt (fun y => c y / d y) ((d y)⁻¹ • c' - (c y / d y ^ 2) • d') y := by
  have hinv := (hasDerivAt_inv hy).comp_hasFDerivAt y hd
  have h := hc.mul hinv
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  · ext v
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
      _root_.sub_apply]
    simp
    field_simp
    ring
  · simp [div_eq_mul_inv]

@[tmio T, powerlib_foundation] private theorem fderiv_coneW {Xs Ys qs δs ζs : ℝ}
    {g : State 4 → ℝ} {Lg : State 4 →L[ℝ] ℝ} {y : State 4} (hg : HasFDerivAt g Lg y)
    (hr : g y ≠ 0) (hXs : Xs ≠ 0) (hYs : Ys ≠ 0) (v : State 4) :
    fderiv ℝ (coneW Xs Ys qs δs ζs g) y v =
      coneRate Xs Ys qs (g y) (y 0 - δs) (y 1) (y 3 - ζs) (v 0) (v 1) (v 3) (Lg v) := by
  have h0 := (Dynamics.hasFDerivAt_coord 0 y).sub_const δs
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h3 := ((Dynamics.hasFDerivAt_coord 3 y).sub_const ζs).const_mul qs
  have hA1 := hasFDerivAt_div_aux h0 ((hg.pow 5).const_mul Xs) (by positivity)
  have hA2 := hasFDerivAt_div_aux h1 ((hg.pow 4).const_mul Ys) (by positivity)
  have hA3 := hasFDerivAt_div_aux h3 (hg.pow 3) (by positivity)
  have hW := ((((hA1.sub_const 1).pow 2).const_mul 4).const_sub (1 / 100)).sub
    (((hA2.sub_const 1).pow 2).const_mul 5) |>.sub (((hA3.pow 2).const_mul 10))
  have hW' : HasFDerivAt (coneW Xs Ys qs δs ζs g) _ y := hW
  rw [hW'.fderiv]
  simp only [coneRate, _root_.smul_apply,
    smul_eq_mul, _root_.sub_apply, Dynamics.coord_apply, _root_.neg_apply]
  simp
  field_simp
  ring

/-- The rate inequality of the cone barrier in normalised coordinates: on the ellipsoid
`4 ξ² + 5 η² + 10 ν² = 1/100`, with perturbations `|a₁|, |a₂|, |a₃| ≤ 1/1000`, the normalised
rate of `4 ξ² + 5 η² + 10 ν²` is negative (its quadratic part is at most `−(4/3)/100`). -/
@[tmio T, powerlib_foundation] private theorem cone_ineq {ξ η ν a1 a2 a3 : ℝ}
    (hG : 4 * ξ ^ 2 + 5 * η ^ 2 + 10 * ν ^ 2 = 1 / 100)
    (h1 : |a1| ≤ 1 / 1000) (h2 : |a2| ≤ 1 / 1000) (h3 : |a3| ≤ 1 / 1000) :
    -(40 / 3) * (2 * ξ ^ 2 + η ^ 2 + ξ ^ 3 + ξ * η ^ 2 - η * ν) - 20 * ν ^ 2 * (1 + ξ - a1) +
      (40 / 3) * (ξ * (1 + ξ) + η * (1 + η)) * a1 - 10 * η * a2 + 20 * a3 * ν < 0 := by
  have hξ2 : ξ ^ 2 ≤ 1 / 400 := by nlinarith [sq_nonneg η, sq_nonneg ν]
  have hη2 : η ^ 2 ≤ 1 / 500 := by nlinarith [sq_nonneg ξ, sq_nonneg ν]
  have hν2 : ν ^ 2 ≤ 1 / 1000 := by nlinarith [sq_nonneg ξ, sq_nonneg η]
  have hξ : |ξ| ≤ 1 / 20 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  have hη : |η| ≤ 1 / 20 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  have hν : |ν| ≤ 1 / 30 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  rw [abs_le] at hξ hη hν h1 h2 h3
  obtain ⟨hξa, hξb⟩ := hξ
  obtain ⟨hηa, hηb⟩ := hη
  obtain ⟨hνa, hνb⟩ := hν
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨h3a, h3b⟩ := h3
  -- leading part
  have hlead : -(40 / 3) * (2 * ξ ^ 2 + η ^ 2 - η * ν) - 20 * ν ^ 2 ≤ -(4 / 3) * (1 / 100) := by
    nlinarith [sq_nonneg (η - ν)]
  -- cubic part
  have hcub : -(40 / 3) * (ξ ^ 3 + ξ * η ^ 2) ≤ (40 / 3) * (1 / 20) * (9 / 2000) := by
    have e : ξ ^ 3 + ξ * η ^ 2 = ξ * (ξ ^ 2 + η ^ 2) := by ring
    rw [e]
    have hs : ξ ^ 2 + η ^ 2 ≤ 9 / 2000 := by linarith
    have hs0 : 0 ≤ ξ ^ 2 + η ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (show -ξ ≤ 1 / 20 by linarith) hs0]
  have hnu : -20 * ν ^ 2 * (ξ - a1) ≤ 20 * (1 / 1000) * (1 / 20 + 1 / 1000) := by
    have hs0 : 0 ≤ ν ^ 2 := sq_nonneg _
    have : -(ξ - a1) ≤ 1 / 20 + 1 / 1000 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hs0]
  have hp1 : (40 / 3) * (ξ * (1 + ξ) + η * (1 + η)) * a1 ≤ (40 / 3) * (21 / 200) * (1 / 1000) := by
    have hb : |ξ * (1 + ξ) + η * (1 + η)| ≤ 21 / 200 := by
      rw [abs_le]; constructor <;> nlinarith
    have := abs_mul (ξ * (1 + ξ) + η * (1 + η)) a1
    have h1' : |a1| ≤ 1 / 1000 := abs_le.mpr ⟨h1a, h1b⟩
    have := le_abs_self ((ξ * (1 + ξ) + η * (1 + η)) * a1)
    nlinarith [mul_le_mul hb h1' (abs_nonneg _) (by norm_num)]
  have hp2 : -10 * η * a2 ≤ 10 * (1 / 20) * (1 / 1000) := by nlinarith
  have hp3 : 20 * a3 * ν ≤ 20 * (1 / 1000) * (1 / 30) := by nlinarith
  nlinarith

/-- The rate of the cone barrier is positive on its boundary: with `r > 0`, the normalisation
`Y* = (5/3) a X*`, `k = −a C/X*`, `K_p = σ (20/9) a² X* M` (`a > 0`), `V = σ r³`, the field
components `v` of the model at the balance, the boundary `4 ξ² + 5 η² + 10 ν² = 1/100` and
perturbations at most `1/1000`, `coneRate > 0`: the rate equals `(a/r)` times minus the
expression of `cone_ineq`. -/
@[tmio T, powerlib_foundation] private theorem coneRate_pos
    {Xs Ys am r σ k Kp Ki M D C V θ ω z R v0 v1 v2 v3 : ℝ}
    (hr : 0 < r) (ham : 0 < am) (hXs : Xs ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0)
    (hσ : σ = 1 ∨ σ = -1) (hYs : Ys = 5 / 3 * am * Xs) (hk : k = -(am * C) / Xs)
    (hKp : Kp = σ * (20 / 9 * am ^ 2 * Xs * M)) (hV : V = σ * r ^ 3) (hv0 : v0 = ω)
    (hv1 : v1 = (Kp * V + Ki * z - (k * θ + R) - D * ω) / M)
    (hv2 : v2 = -(k * θ + R) / V / C) (hv3 : v3 = V)
    (hW : 4 * (θ / (Xs * r ^ 5) - 1) ^ 2 + 5 * (ω / (Ys * r ^ 4) - 1) ^ 2 +
      10 * (Ki / Kp * σ * z / r ^ 3) ^ 2 = 1 / 100)
    (h0 : |R / (am * C * r ^ 5)| ≤ 1 / 1000)
    (h1 : |k / M * (Xs / Ys) * r ^ 2 * (θ / (Xs * r ^ 5)) / am + R / (M * Ys * r ^ 3 * am) +
      D / M * r * (ω / (Ys * r ^ 4)) / am| ≤ 1 / 1000)
    (h2 : |r * (Ki / (Kp * am))| ≤ 1 / 1000) :
    0 < coneRate Xs Ys (Ki / Kp * σ) r θ ω z v0 v1 v3 (σ / (3 * r ^ 2) * v2) := by
  have hN := cone_ineq hW h0 h1 h2
  have key : coneRate Xs Ys (Ki / Kp * σ) r θ ω z v0 v1 v3 (σ / (3 * r ^ 2) * v2) =
      am / r * -(-(40 / 3) * (2 * (θ / (Xs * r ^ 5) - 1) ^ 2 + (ω / (Ys * r ^ 4) - 1) ^ 2 +
        (θ / (Xs * r ^ 5) - 1) ^ 3 + (θ / (Xs * r ^ 5) - 1) * (ω / (Ys * r ^ 4) - 1) ^ 2 -
        (ω / (Ys * r ^ 4) - 1) * (Ki / Kp * σ * z / r ^ 3)) -
        20 * (Ki / Kp * σ * z / r ^ 3) ^ 2 * (1 + (θ / (Xs * r ^ 5) - 1) - R / (am * C * r ^ 5)) +
        (40 / 3) * ((θ / (Xs * r ^ 5) - 1) * (1 + (θ / (Xs * r ^ 5) - 1)) +
          (ω / (Ys * r ^ 4) - 1) * (1 + (ω / (Ys * r ^ 4) - 1))) * (R / (am * C * r ^ 5)) -
        10 * (ω / (Ys * r ^ 4) - 1) * (k / M * (Xs / Ys) * r ^ 2 * (θ / (Xs * r ^ 5)) / am +
          R / (M * Ys * r ^ 3 * am) + D / M * r * (ω / (Ys * r ^ 4)) / am) +
        20 * (r * (Ki / (Kp * am))) * (Ki / Kp * σ * z / r ^ 3)) := by
    subst hYs hk hKp hV hv0 hv1 hv2 hv3
    rcases hσ with rfl | rfl <;>
    · simp only [coneRate]
      field_simp
      ring
  rw [key]
  exact mul_pos (div_pos ham hr) (neg_pos.mpr hN)

/-- The remainder of the power curve at `θ = a₁ X* r⁵`, `|a₁| ≤ 21/20`. -/
@[tmio T, powerlib_foundation] private theorem pert_R {A Xs r θ R a1 : ℝ} (hr : 0 < r)
    (hθ : θ = a1 * Xs * r ^ 5) (ha1 : |a1| ≤ 21 / 20)
    (hR : |R| ≤ |A| * θ ^ 2) : |R| ≤ 2 * |A| * Xs ^ 2 * r ^ 10 := by
  have ha1sq : a1 ^ 2 ≤ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg a1]
  have hA0 : 0 ≤ |A| := abs_nonneg _
  calc |R| ≤ |A| * θ ^ 2 := hR
    _ = |A| * (a1 ^ 2 * (Xs ^ 2 * r ^ 10)) := by rw [hθ]; ring
    _ ≤ |A| * (2 * (Xs ^ 2 * r ^ 10)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha1sq (by positivity)) hA0
    _ = 2 * |A| * Xs ^ 2 * r ^ 10 := by ring

/-- The perturbation `R/(a C r⁵)` is `O(r)`. -/
@[tmio T, powerlib_foundation] private theorem pert_e0 {A Xs am C r R : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (ham : 0 < am) (hC : C ≠ 0)
    (hR : |R| ≤ 2 * |A| * Xs ^ 2 * r ^ 10) :
    |R / (am * C * r ^ 5)| ≤ 2 * |A| * Xs ^ 2 / (am * |C|) * r := by
  have hC0 : 0 < |C| := abs_pos.mpr hC
  have hr10 : r ^ 10 ≤ r ^ 6 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
  rw [abs_div, abs_mul, abs_mul, abs_of_pos ham, abs_of_pos (pow_pos hr 5),
    div_le_iff₀ (by positivity)]
  have e : 2 * |A| * Xs ^ 2 / (am * |C|) * r * (am * |C| * r ^ 5) =
      2 * |A| * Xs ^ 2 * r ^ 6 := by field_simp
  rw [e]
  exact hR.trans (mul_le_mul_of_nonneg_left hr10 (by positivity))

/-- The synchronising term of the perturbation `e₁` is `O(r)`. -/
@[tmio T, powerlib_foundation] private theorem pert_f1 {Xs am k M r a1 : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (ham : 0 < am) (hXs : Xs ≠ 0)
    (ha1 : |a1| ≤ 21 / 20) :
    |k / M * (Xs / (5 / 3 * am * Xs)) * r ^ 2 * a1 / am| ≤ |k / M| / am ^ 2 * r := by
  have e : k / M * (Xs / (5 / 3 * am * Xs)) * r ^ 2 * a1 / am =
      k / M / am ^ 2 * (3 / 5 * r ^ 2 * a1) := by field_simp
  rw [e, abs_mul, abs_div, abs_of_pos (pow_pos ham 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5), abs_of_pos (pow_pos hr 2)]
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have h0 : 0 ≤ r ^ 2 * |a1| := by positivity
  nlinarith [abs_nonneg a1]

/-- The remainder term of the perturbation `e₁` is `O(r)`. -/
@[tmio T, powerlib_foundation] private theorem pert_f2 {A Xs am M r R : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (ham : 0 < am) (hXs : Xs ≠ 0)
    (hM : M ≠ 0) (hR : |R| ≤ 2 * |A| * Xs ^ 2 * r ^ 10) :
    |R / (M * (5 / 3 * am * Xs) * r ^ 3 * am)| ≤ 2 * |A| * |Xs| / (|M| * am ^ 2) * r := by
  have hXs0 : 0 < |Xs| := abs_pos.mpr hXs
  have hM0 : 0 < |M| := abs_pos.mpr hM
  have hab : |M * (5 / 3 * am * Xs) * r ^ 3 * am| = |M| * (5 / 3 * am * |Xs|) * r ^ 3 * am := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos ham,
      abs_of_pos (pow_pos hr 3), abs_of_pos (by norm_num : (0 : ℝ) < 5 / 3)]
  rw [abs_div, hab, div_le_iff₀ (by positivity)]
  have e : 2 * |A| * |Xs| / (|M| * am ^ 2) * r * (|M| * (5 / 3 * am * |Xs|) * r ^ 3 * am) =
      10 / 3 * |A| * |Xs| ^ 2 * r ^ 4 := by field_simp; ring
  rw [e, sq_abs]
  have hr6 : r ^ 10 ≤ r ^ 4 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
  have h1 := mul_le_mul_of_nonneg_left hr6 (by positivity : (0 : ℝ) ≤ 2 * |A| * Xs ^ 2)
  have h2 : 0 ≤ |A| * Xs ^ 2 * r ^ 4 := by positivity
  calc |R| ≤ 2 * |A| * Xs ^ 2 * r ^ 10 := hR
    _ ≤ 2 * |A| * Xs ^ 2 * r ^ 4 := h1
    _ ≤ 10 / 3 * |A| * Xs ^ 2 * r ^ 4 := by linarith

/-- The damping term of the perturbation `e₁` is `O(r)`. -/
@[tmio T, powerlib_foundation] private theorem pert_f3 {am D M r a2 : ℝ} (hr : 0 < r)
    (ham : 0 < am) (ha2 : |a2| ≤ 21 / 20) :
    |D / M * r * a2 / am| ≤ 2 * |D / M| / am * r := by
  rw [abs_div, abs_mul, abs_mul, abs_of_pos ham, abs_of_pos hr, div_le_iff₀ ham]
  have e : 2 * |D / M| / am * r * am = 2 * |D / M| * r := by field_simp
  rw [e]
  have h0 : 0 ≤ |D / M| * r := mul_nonneg (abs_nonneg _) hr.le
  nlinarith [abs_nonneg a2]

/-- The norm of a perturbation of the angle, the frequency and the DC voltage. -/
@[tmio T, powerlib_foundation] private theorem norm_cone_seed_le (a b c : ℝ) :
    ‖(EuclideanSpace.single 0 a + EuclideanSpace.single 1 b + EuclideanSpace.single 2 c :
      State 4)‖ ≤ |a| + |b| + |c| := by
  have t1 := norm_add_le (EuclideanSpace.single 0 a + EuclideanSpace.single 1 b : State 4)
    (EuclideanSpace.single 2 c)
  have t2 := norm_add_le (EuclideanSpace.single 0 a : State 4) (EuclideanSpace.single 1 b)
  simp only [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs] at t1 t2
  linarith

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)

/-- The field at the degenerate balance of the invariant plane (`V* = 0`, `I_s = 0`,
`P_s = P_e(δ*) = P_ff + K_i ζ*`), with `θ = δ − δ*` and the remainder
`R = P_e(δ* + θ) − P_e(δ*) − k(δ*) θ`. -/
@[tmio M, powerlib_domain] private theorem field_cone (m : Model) (hV : m.p.Vref = 0)
    (hIs : m.p.Is = 0) (hP : m.p.Ps = m.p.Pe m.δ) (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ)
    (y : State 4) :
    m.p.field y 0 = y 1 ∧
      m.p.field y 1 = (m.p.Kp * y 2 + m.p.Ki * (y 3 - m.ζ) - (m.p.k m.δ * (y 0 - m.δ) +
        (m.p.Pe (m.δ + (y 0 - m.δ)) - m.p.Pe m.δ - m.p.k m.δ * (y 0 - m.δ))) -
        m.p.D * y 1) / m.p.M ∧
      m.p.field y 2 = -(m.p.k m.δ * (y 0 - m.δ) +
        (m.p.Pe (m.δ + (y 0 - m.δ)) - m.p.Pe m.δ - m.p.k m.δ * (y 0 - m.δ))) / y 2 / m.p.C ∧
      m.p.field y 3 = y 2 := by
  have hy0 : m.δ + (y 0 - m.δ) = y 0 := by ring
  refine ⟨Params.field_apply_zero _ _, ?_, ?_, by rw [Params.field_apply_three, hV, sub_zero]⟩
  · rw [Params.field_apply_one, hy0]
    simp only [Plant.swingRate, Params.Pref, hV, sub_zero]
    congr 1
    linarith
  · rw [Params.field_apply_two, hy0]
    simp only [Plant.nodeRate, GFL.DCLink.nodeRate, hIs, hP, zero_add]
    ring

/-- The DC rate in the cone: `σ V̇ = a r² (θ/(X* r⁵) − R/(a C r⁵))` for `V = σ r³`,
`k = −a C/X*`. -/
@[tmio T, powerlib_foundation] private theorem cone_node {Xs am r σ k C θ R V : ℝ}
    (hr : 0 < r) (ham : 0 < am) (hXs : Xs ≠ 0) (hC : C ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (hk : k = -(am * C) / Xs) (hV : V = σ * r ^ 3) :
    σ * (-(k * θ + R) / V / C) = am * r ^ 2 * (θ / (Xs * r ^ 5) - R / (am * C * r ^ 5)) := by
  subst hk hV
  rcases hσ with rfl | rfl <;>
  · field_simp
    ring

/-- Inside the barrier ellipsoid `4 ξ² + 5 η² + 10 ν² ≤ 1/100`: `|ξ|, |η| ≤ 1/20`. -/
@[tmio T, powerlib_foundation] private theorem ellipse_bounds {ξ η ν : ℝ}
    (h : 0 ≤ 1 / 100 - (4 * ξ ^ 2 + 5 * η ^ 2 + 10 * ν ^ 2)) : |ξ| ≤ 1 / 20 ∧ |η| ≤ 1 / 20 := by
  constructor
  · rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
    nlinarith [sq_nonneg η, sq_nonneg ν]
  · rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
    nlinarith [sq_nonneg ξ, sq_nonneg ν]

/-- The perturbation budget: `(c₀ + c₁ + c₂ + c₃ + c₄ + 1) r ≤ 1/1000` with `cᵢ, r ≥ 0` bounds
`c₀ r`, `(c₁ + c₂ + c₃) r` and `c₄ r` by `1/1000`. -/
@[tmio T, powerlib_foundation] private theorem cone_budget {c0 c1 c2 c3 c4 r : ℝ} (hr : 0 ≤ r)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
    (h : (c0 + c1 + c2 + c3 + c4 + 1) * r ≤ 1 / 1000) :
    c0 * r ≤ 1 / 1000 ∧ (c1 + c2 + c3) * r ≤ 1 / 1000 ∧ c4 * r ≤ 1 / 1000 := by
  have e : (c0 + c1 + c2 + c3 + c4 + 1) * r = c0 * r + (c1 + c2 + c3) * r + c4 * r + r := by ring
  have t0 := mul_nonneg h0 hr
  have t1 := mul_nonneg (add_nonneg (add_nonneg h1 h2) h3) hr
  have t4 := mul_nonneg h4 hr
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The normalisation of the cone: on the side `σ` with `σ K_p k(δ*)/(M C) < 0` there are
`a > 0` (`a = −m`, `m³ = (9/20) σ (K_p/M) (k(δ*)/C)`) and `X* = m C/k(δ*) ≠ 0` with
`k(δ*) = −a C/X*` and `K_p = σ (20/9) a² X* M`. -/
@[tmio M, powerlib_domain] private theorem cone_constants (m : Model) (hM : m.p.M ≠ 0)
    (hC : m.p.C ≠ 0) {σ : ℝ} (hσ2 : σ * σ = 1)
    (hside : σ * m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C) < 0) :
    ∃ am Xs : ℝ, 0 < am ∧ Xs ≠ 0 ∧ m.p.k m.δ = -(am * m.p.C) / Xs ∧
      m.p.Kp = σ * (20 / 9 * am ^ 2 * Xs * m.p.M) := by
  obtain ⟨mm, hmm, hmm3⟩ := exists_cube_root_of_neg
    (p := 9 * (σ * m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C)) / 20) (by linarith)
  have hκ0 : m.p.k m.δ / m.p.C ≠ 0 := fun h => by rw [h, mul_zero] at hside; exact lt_irrefl _ hside
  have hk0 : m.p.k m.δ ≠ 0 := fun h => hκ0 (by rw [h, zero_div])
  have hmm0 : mm ≠ 0 := hmm.ne
  refine ⟨-mm, mm / (m.p.k m.δ / m.p.C), by linarith, div_ne_zero hmm0 hκ0, by field_simp, ?_⟩
  have e : (-mm) ^ 2 * (mm / (m.p.k m.δ / m.p.C)) = mm ^ 3 / (m.p.k m.δ / m.p.C) := by ring
  rw [show σ * (20 / 9 * (-mm) ^ 2 * (mm / (m.p.k m.δ / m.p.C)) * m.p.M) =
    σ * (20 / 9 * ((-mm) ^ 2 * (mm / (m.p.k m.δ / m.p.C))) * m.p.M) by ring, e, hmm3]
  field_simp
  linear_combination -m.p.Kp * hσ2

/-- The trapping region of the cone. With the normalisation of `cone_constants`, `B` the
perturbation constant, `r₀ ≤ 1`, `B r₀ ≤ 1/1000`, a seed radius `r_s ≤ 1` and the cutoff
`c = r_s³/8`: at every state `y` with `‖y − x*‖ < r₀³`, `σ V ≥ r_s³/2` inside the barrier
`coneW ≥ 0`, `σ V` grows at the rate `≥ a (r_s/2)² (9/10)` and the field enters the barrier. -/
@[tmio TM, powerlib_domain] private theorem cone_region (m : Model) (hV : m.p.Vref = 0)
    (hIs : m.p.Is = 0) (hC : m.p.C ≠ 0) (hP : m.p.Ps = m.p.Pe m.δ)
    (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ) (hM : m.p.M ≠ 0) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {am Xs Ys B r₀ rs c : ℝ} (ham0 : 0 < am) (hXs : Xs ≠ 0)
    (hYs : Ys = 5 / 3 * am * Xs) (hkX : m.p.k m.δ = -(am * m.p.C) / Xs)
    (hKpX : m.p.Kp = σ * (20 / 9 * am ^ 2 * Xs * m.p.M))
    (hB : B = 2 * |m.p.A| * Xs ^ 2 / (am * |m.p.C|) + |m.p.k m.δ / m.p.M| / am ^ 2 +
      2 * |m.p.A| * |Xs| / (|m.p.M| * am ^ 2) + 2 * |m.p.D / m.p.M| / am +
      |m.p.Ki / m.p.Kp| / am + 1)
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hr₀B : B * r₀ ≤ 1 / 1000) (hrs0 : 0 < rs)
    (hc : c = rs ^ 3 / 8) {y : State 4} (hy : ‖y - m.point‖ < r₀ ^ 3)
    (hσy : rs ^ 3 / 2 ≤ σ * y 2)
    (hW1 : 0 ≤ coneW Xs Ys (m.p.Ki / m.p.Kp * σ) m.δ m.ζ (coneRadius σ c) y) :
    am * (rs / 2) ^ 2 * (9 / 10) ≤ σ * m.p.field y 2 ∧
      (coneW Xs Ys (m.p.Ki / m.p.Kp * σ) m.δ m.ζ (coneRadius σ c) y = 0 →
        0 < fderiv ℝ (coneW Xs Ys (m.p.Ki / m.p.Kp * σ) m.δ m.ζ (coneRadius σ c)) y
          (m.p.field y)) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have p2 : m.point 2 = 0 := by simp [Model.point, hV]
  have hYs0 : Ys ≠ 0 := by rw [hYs]; exact mul_ne_zero (by positivity) hXs
  have hB0 : 0 < B := by rw [hB]; positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hy2c : 2 * c < σ * y 2 := by rw [hc]; nlinarith [pow_pos hrs0 3]
  have hVpos : 0 < σ * y 2 := by linarith
  obtain ⟨hg, hgy⟩ := hasFDerivAt_coneRadius hc0 hy2c
  obtain ⟨r, hrd⟩ : ∃ r, r = (σ * y 2) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  rw [← hrd] at hg hgy
  have hr0 : 0 < r := by rw [hrd]; exact Real.rpow_pos_of_pos hVpos _
  have hr3 : r ^ 3 = σ * y 2 := by rw [hrd]; exact (NormalForm.DynamicFold.cbrt_pow hVpos.le).1
  have hVy : y 2 = σ * r ^ 3 := by rw [hr3, ← mul_assoc, hσ2, one_mul]
  have hrr₀ : r ≤ r₀ := by
    have h1 := Dynamics.abs_coord_sub_le m.point y 2
    rw [p2, sub_zero] at h1
    have h2 : σ * y 2 ≤ |y 2| := by
      rcases hσ with rfl | rfl
      · rw [one_mul]; exact le_abs_self _
      · rw [neg_one_mul]; exact neg_le_abs _
    have : r ^ 3 ≤ r₀ ^ 3 := by linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hr₀0.le this
  have hr1 : r ≤ 1 := hrr₀.trans hr₀1
  have hrB : B * r ≤ 1 / 1000 := (mul_le_mul_of_nonneg_left hrr₀ hB0.le).trans hr₀B
  have hrs2 : rs / 2 ≤ r := by
    have : (rs / 2) ^ 3 ≤ r ^ 3 := by rw [hr3]; nlinarith [pow_pos hrs0 3]
    exact le_of_pow_le_pow_left₀ (by norm_num) hr0.le this
  -- the barrier in the normalised coordinates
  have hWy : coneW Xs Ys (m.p.Ki / m.p.Kp * σ) m.δ m.ζ (coneRadius σ c) y =
      1 / 100 - (4 * ((y 0 - m.δ) / (Xs * r ^ 5) - 1) ^ 2 + 5 * (y 1 / (Ys * r ^ 4) - 1) ^ 2 +
        10 * (m.p.Ki / m.p.Kp * σ * (y 3 - m.ζ) / r ^ 3) ^ 2) := by
    simp only [coneW, hgy]; ring
  rw [hWy] at hW1
  obtain ⟨hξ, hη⟩ := ellipse_bounds hW1
  have ha1 : |(y 0 - m.δ) / (Xs * r ^ 5)| ≤ 21 / 20 := by
    have := abs_sub_abs_le_abs_sub ((y 0 - m.δ) / (Xs * r ^ 5)) 1; rw [abs_one] at this
    linarith
  have ha2 : |y 1 / (Ys * r ^ 4)| ≤ 21 / 20 := by
    have := abs_sub_abs_le_abs_sub (y 1 / (Ys * r ^ 4)) 1; rw [abs_one] at this; linarith
  -- the remainder and the perturbations
  obtain ⟨R, hRd⟩ : ∃ R, R = m.p.Pe (m.δ + (y 0 - m.δ)) - m.p.Pe m.δ -
      m.p.k m.δ * (y 0 - m.δ) := ⟨_, rfl⟩
  have hR := m.p.abs_Pe_add_sub_le m.δ (y 0 - m.δ)
  rw [← hRd] at hR
  have hθ : y 0 - m.δ = (y 0 - m.δ) / (Xs * r ^ 5) * Xs * r ^ 5 := by
    field_simp
  have hR' := pert_R hr0 hθ ha1 hR
  have hp0 := pert_e0 hr0 hr1 ham0 hC hR'
  have hp1 := pert_f1 (k := m.p.k m.δ) (M := m.p.M) hr0 hr1 ham0 hXs ha1
  have hp2 := pert_f2 hr0 hr1 ham0 hXs hM hR'
  have hp3 := pert_f3 (D := m.p.D) (M := m.p.M) hr0 ham0 (hYs ▸ ha2)
  rw [← hYs] at hp1 hp2 hp3
  have q0 : 0 ≤ 2 * |m.p.A| * Xs ^ 2 / (am * |m.p.C|) := by positivity
  have q1 : 0 ≤ |m.p.k m.δ / m.p.M| / am ^ 2 := by positivity
  have q2 : 0 ≤ 2 * |m.p.A| * |Xs| / (|m.p.M| * am ^ 2) := by positivity
  have q3 : 0 ≤ 2 * |m.p.D / m.p.M| / am := by positivity
  have q4 : 0 ≤ |m.p.Ki / m.p.Kp| / am := by positivity
  rw [hB] at hrB
  obtain ⟨b0, b1, b2⟩ := cone_budget hr0.le q0 q1 q2 q3 q4 hrB
  have he0 : |R / (am * m.p.C * r ^ 5)| ≤ 1 / 1000 := hp0.trans b0
  have he1 : |m.p.k m.δ / m.p.M * (Xs / Ys) * r ^ 2 * ((y 0 - m.δ) / (Xs * r ^ 5)) / am +
      R / (m.p.M * Ys * r ^ 3 * am) + m.p.D / m.p.M * r * (y 1 / (Ys * r ^ 4)) / am| ≤
      1 / 1000 := by
    have t1 := abs_add_le (m.p.k m.δ / m.p.M * (Xs / Ys) * r ^ 2 * ((y 0 - m.δ) / (Xs * r ^ 5)) /
      am + R / (m.p.M * Ys * r ^ 3 * am)) (m.p.D / m.p.M * r * (y 1 / (Ys * r ^ 4)) / am)
    have t2 := abs_add_le (m.p.k m.δ / m.p.M * (Xs / Ys) * r ^ 2 * ((y 0 - m.δ) / (Xs * r ^ 5)) /
      am) (R / (m.p.M * Ys * r ^ 3 * am))
    have e : (|m.p.k m.δ / m.p.M| / am ^ 2 + 2 * |m.p.A| * |Xs| / (|m.p.M| * am ^ 2) +
        2 * |m.p.D / m.p.M| / am) * r = |m.p.k m.δ / m.p.M| / am ^ 2 * r +
        2 * |m.p.A| * |Xs| / (|m.p.M| * am ^ 2) * r + 2 * |m.p.D / m.p.M| / am * r := by ring
    linarith
  have he2 : |r * (m.p.Ki / (m.p.Kp * am))| ≤ 1 / 1000 := by
    rw [abs_mul, abs_of_pos hr0, abs_div, abs_mul, abs_of_pos ham0]
    have : r * (|m.p.Ki| / (|m.p.Kp| * am)) = |m.p.Ki / m.p.Kp| / am * r := by
      rw [abs_div]; field_simp
    rw [this]
    exact b2
  obtain ⟨f0, f1, f2, f3⟩ := field_cone m hV hIs hP hb y
  rw [← hRd] at f1 f2
  have hnode := cone_node (θ := y 0 - m.δ) (R := R) hr0 ham0 hXs hC hσ hkX hVy
  rw [← f2] at hnode
  have hxi : 19 / 20 ≤ (y 0 - m.δ) / (Xs * r ^ 5) := by
    have := (abs_le.mp hξ).1; linarith
  refine ⟨?_, fun hW0 => ?_⟩
  · rw [hnode]
    have he0' := (abs_le.mp he0).2
    have hrr : (rs / 2) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hrs2 2
    have : 9 / 10 ≤ (y 0 - m.δ) / (Xs * r ^ 5) - R / (am * m.p.C * r ^ 5) := by linarith
    calc am * (rs / 2) ^ 2 * (9 / 10) ≤ am * r ^ 2 * (9 / 10) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrr ham0.le) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  · rw [fderiv_coneW hg (by rw [hgy]; exact hr0.ne') hXs hYs0, hgy]
    have hL : ((σ / (3 * r ^ 2)) • coord (2 : Fin 4)) (m.p.field y) =
        σ / (3 * r ^ 2) * m.p.field y 2 := by simp
    rw [hL]
    have hW0' : 4 * ((y 0 - m.δ) / (Xs * r ^ 5) - 1) ^ 2 + 5 * (y 1 / (Ys * r ^ 4) - 1) ^ 2 +
        10 * (m.p.Ki / m.p.Kp * σ * (y 3 - m.ζ) / r ^ 3) ^ 2 = 1 / 100 := by
      rw [hWy] at hW0; linarith
    exact coneRate_pos hr0 ham0 hXs hM hC hσ hYs hkX hKpX hVy f0 f1 f2 f3 hW0' he0 he1 he2

/-- The core of `mem_den_unstable_of_invariant_cone` on the side `σ` with
`σ K_p k(δ*)/(M C) < 0`. -/
@[tmio TM, powerlib_domain] private theorem unstable_cone_core (m : Model) (hV : m.p.Vref = 0)
    (hIs : m.p.Is = 0) (hC : m.p.C ≠ 0) (hP : m.p.Ps = m.p.Pe m.δ)
    (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ) (hM : m.p.M ≠ 0) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hside : σ * m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C) < 0) :
    Unstable m.p.field m.point := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have p0 : m.point 0 = m.δ := by simp [Model.point]
  have p1 : m.point 1 = 0 := by simp [Model.point]
  have p2 : m.point 2 = 0 := by simp [Model.point, hV]
  have p3 : m.point 3 = m.ζ := by simp [Model.point]
  obtain ⟨am, Xs, ham0, hXs, hkX, hKpX⟩ := cone_constants m hM hC hσ2 hside
  obtain ⟨Ys, hYs⟩ : ∃ Ys, Ys = 5 / 3 * am * Xs := ⟨_, rfl⟩
  have hYs0 : Ys ≠ 0 := by rw [hYs]; exact mul_ne_zero (by positivity) hXs
  -- the perturbation constant `B` and the radii
  obtain ⟨B, hB⟩ : ∃ B, B = 2 * |m.p.A| * Xs ^ 2 / (am * |m.p.C|) + |m.p.k m.δ / m.p.M| / am ^ 2 +
      2 * |m.p.A| * |Xs| / (|m.p.M| * am ^ 2) + 2 * |m.p.D / m.p.M| / am +
      |m.p.Ki / m.p.Kp| / am + 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = min 1 (1 / (1000 * B)) := ⟨_, rfl⟩
  have hr₀0 : 0 < r₀ := by rw [hr₀]; exact lt_min one_pos (by positivity)
  have hr₀1 : r₀ ≤ 1 := by rw [hr₀]; exact min_le_left _ _
  have hr₀B : B * r₀ ≤ 1 / 1000 := by
    have : r₀ ≤ 1 / (1000 * B) := by rw [hr₀]; exact min_le_right _ _
    calc B * r₀ ≤ B * (1 / (1000 * B)) := mul_le_mul_of_nonneg_left this hB0.le
      _ = 1 / 1000 := by field_simp
  have hρ : 0 < r₀ ^ 3 := pow_pos hr₀0 3
  refine Dynamics.Degenerate.unstable_of_barriers 2 (σ := σ) hρ (fun s hs => ?_)
    fun δ' hδ' => ?_
  · obtain ⟨G, hG, hGf⟩ := m.p.exists_contDiff_eq_field_of_sign hσ hs
    exact ⟨G, hG, fun y _ hy => hGf y hy⟩
  -- the seed `(δ* + X* r_s⁵, Y* r_s⁴, σ r_s³, ζ*)` on the self-similar curve
  have hS : 0 < |Xs| + |Ys| + 1 := by positivity
  obtain ⟨rs, hrs⟩ : ∃ rs, rs = min (r₀ / 2) (δ' / (2 * (|Xs| + |Ys| + 1))) := ⟨_, rfl⟩
  have hrs0 : 0 < rs := by rw [hrs]; exact lt_min (by positivity) (by positivity)
  have hrs1 : rs ≤ 1 := by
    have : rs ≤ r₀ / 2 := by rw [hrs]; exact min_le_left _ _
    linarith
  have hrsδ : rs * (|Xs| + |Ys| + 1) < δ' := by
    have : rs ≤ δ' / (2 * (|Xs| + |Ys| + 1)) := by rw [hrs]; exact min_le_right _ _
    calc rs * (|Xs| + |Ys| + 1) ≤ δ' / (2 * (|Xs| + |Ys| + 1)) * (|Xs| + |Ys| + 1) :=
          mul_le_mul_of_nonneg_right this hS.le
      _ = δ' / 2 := by field_simp
      _ < δ' := by linarith
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : State 4, y₀ = m.point + (EuclideanSpace.single 0 (Xs * rs ^ 5) +
      EuclideanSpace.single 1 (Ys * rs ^ 4) + EuclideanSpace.single 2 (σ * rs ^ 3)) :=
    ⟨_, rfl⟩
  have c0 : y₀ 0 = m.δ + Xs * rs ^ 5 := by simp [hy₀, p0]
  have c1 : y₀ 1 = Ys * rs ^ 4 := by simp [hy₀, p1]
  have c2 : y₀ 2 = σ * rs ^ 3 := by simp [hy₀, p2]
  have c3 : y₀ 3 = m.ζ := by simp [hy₀, p3]
  have hσy₀ : σ * y₀ 2 = rs ^ 3 := by rw [c2, ← mul_assoc, hσ2, one_mul]
  obtain ⟨c, hc⟩ : ∃ c, c = rs ^ 3 / 8 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  -- at the seed the radius is `r_s` and the barrier is `1/100`
  have hseed2 : 2 * c < σ * y₀ 2 := by rw [hσy₀, hc]; nlinarith [pow_pos hrs0 3]
  obtain ⟨-, hg₀⟩ := hasFDerivAt_coneRadius hc0 hseed2
  have hcbrt : (rs ^ 3) ^ ((1 : ℝ) / 3) = rs := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrs0.le]; norm_num
  rw [hσy₀, hcbrt] at hg₀
  have hμ0 : 0 < am * (rs / 2) ^ 2 * (9 / 10) := by positivity
  refine ⟨y₀, ?_, by rw [hσy₀]; positivity, coneW Xs Ys (m.p.Ki / m.p.Kp * σ) m.δ m.ζ
    (coneRadius σ c), fun _ => 1, fun _ => 1, fun y => σ * y 2,
    am * (rs / 2) ^ 2 * (9 / 10), r₀ ^ 3, hμ0, ?_, contDiff_const, contDiff_const,
    by fun_prop, ?_, one_pos, one_pos, fun y hy => ?_, fun y hy hσy hW1 _ _ => ?_⟩
  · -- the seed is close to the point
    rw [hy₀, add_sub_cancel_left]
    refine (norm_cone_seed_le _ _ _).trans_lt ?_
    have h5 : rs ^ 5 ≤ rs := pow_le_of_le_one hrs0.le hrs1 (by norm_num)
    have h4 : rs ^ 4 ≤ rs := pow_le_of_le_one hrs0.le hrs1 (by norm_num)
    have h3 : rs ^ 3 ≤ rs := pow_le_of_le_one hrs0.le hrs1 (by norm_num)
    have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hrs0 5), abs_of_pos (pow_pos hrs0 4),
      abs_of_pos (pow_pos hrs0 3), hσa, one_mul]
    calc |Xs| * rs ^ 5 + |Ys| * rs ^ 4 + rs ^ 3 ≤ |Xs| * rs + |Ys| * rs + rs := by
          have := mul_le_mul_of_nonneg_left h5 (abs_nonneg Xs)
          have := mul_le_mul_of_nonneg_left h4 (abs_nonneg Ys)
          linarith
      _ = rs * (|Xs| + |Ys| + 1) := by ring
      _ < δ' := hrsδ
  · -- the barrier is `C¹`
    unfold coneW
    have hr := contDiff_coneRadius σ hc0
    have hd1 : ∀ y : State 4, Xs * coneRadius σ c y ^ 5 ≠ 0 := fun y =>
      mul_ne_zero hXs (pow_ne_zero 5 (coneRadius_pos hc0 y).ne')
    have hd2 : ∀ y : State 4, Ys * coneRadius σ c y ^ 4 ≠ 0 := fun y =>
      mul_ne_zero hYs0 (pow_ne_zero 4 (coneRadius_pos hc0 y).ne')
    have hd3 : ∀ y : State 4, coneRadius σ c y ^ 3 ≠ 0 := fun y =>
      pow_ne_zero 3 (coneRadius_pos hc0 y).ne'
    have e1 : ContDiff ℝ 1 (fun y : State 4 => (y 0 - m.δ) / (Xs * coneRadius σ c y ^ 5)) :=
      ((Dynamics.contDiff_coord 0).sub contDiff_const).div (contDiff_const.mul (hr.pow 5)) hd1
    have e2 : ContDiff ℝ 1 (fun y : State 4 => y 1 / (Ys * coneRadius σ c y ^ 4)) :=
      (Dynamics.contDiff_coord 1).div (contDiff_const.mul (hr.pow 4)) hd2
    have e3 : ContDiff ℝ 1
        (fun y : State 4 => m.p.Ki / m.p.Kp * σ * (y 3 - m.ζ) / coneRadius σ c y ^ 3) :=
      (contDiff_const.mul ((Dynamics.contDiff_coord 3).sub contDiff_const)).div (hr.pow 3) hd3
    exact ((contDiff_const.sub (contDiff_const.mul ((e1.sub contDiff_const).pow 2))).sub
      (contDiff_const.mul ((e2.sub contDiff_const).pow 2))).sub
      (contDiff_const.mul (e3.pow 2))
  · -- the barrier is `1/100` at the seed
    simp only [coneW, hg₀, c0, c1, c3, sub_self, mul_zero, zero_div]
    have e1 : (m.δ + Xs * rs ^ 5 - m.δ) / (Xs * rs ^ 5) = 1 := by
      rw [add_sub_cancel_left]; exact div_self (mul_ne_zero hXs (pow_ne_zero 5 hrs0.ne'))
    have e2 : Ys * rs ^ 4 / (Ys * rs ^ 4) = 1 :=
      div_self (mul_ne_zero hYs0 (pow_ne_zero 4 hrs0.ne'))
    rw [e1, e2]
    norm_num
  · -- `σ V` is bounded by `r₀³` near the point
    have h1 := Dynamics.abs_coord_sub_le m.point y 2
    rw [p2, sub_zero] at h1
    have : σ * y 2 ≤ |y 2| := by
      rcases hσ with rfl | rfl
      · rw [one_mul]; exact le_abs_self _
      · rw [neg_one_mul]; exact neg_le_abs _
    show σ * y 2 ≤ r₀ ^ 3
    linarith
  -- the trapping region
  rw [hσy₀] at hσy
  obtain ⟨hgrow, hbar⟩ := cone_region m hV hIs hC hP hb hM hσ ham0 hXs hYs hkX hKpX hB hr₀0
    hr₀1 hr₀B hrs0 hc hy hσy hW1
  refine ⟨by linarith, ?_, hbar, fun h => absurd h one_ne_zero, fun h => absurd h one_ne_zero⟩
  have hd : fderiv ℝ (fun y : State 4 => σ * y 2) y (m.p.field y) = σ * m.p.field y 2 := by
    rw [((Dynamics.hasFDerivAt_coord 2 y).const_mul σ).fderiv]
    simp
  rw [hd]; exact hgrow

/-- **Invariant singular plane, degenerate balance, proportional DC gain: escape along a
self-similar cone.** With `V* = 0`, `I_s/C = 0`, `C ≠ 0`, `P_s = P_e(δ*)`, the frozen swing
balanced (`P_ff + K_i ζ* = P_e(δ*)`), `M ≠ 0`, `k(δ*) ≠ 0` and a proportional DC gain `K_p ≠ 0`,
every selected point is unstable, whatever the damping `D` and the integral gain `K_i` (in
particular for DC gains of opposite signs, `K_p K_i < 0`). On the side `σ V > 0` with
`σ K_p k(δ*)/(M C) < 0` the leading part of the field (`θ̇ = ω`, `M ω̇ = K_p V`,
`C V V̇ = −k θ`) has the self-similar solutions `V = σ a t³`, `θ ∝ t⁵`, `ω ∝ t⁴`, the integrator
term `K_i (ζ − ζ*) = O(t⁴)`: in the coordinates `ξ = θ/(X* r⁵) − 1`, `η = ω/(Y* r⁴) − 1`,
`ν = (K_i/K_p)(ζ − ζ*)/V` (`r = (σ V)^{1/3}`, `X*³ = (9/20)(σ K_p/M)/(k/C)²`,
`Y* = −(5/3)(k/C) X*²`) the blown-up field has a hyperbolic sink in `(ξ, η, ν)` (eigenvalues
`−1`, `−7/3 ± i √11/3` after normalisation) while `r` grows; damping, the curvature of the power
curve and the integrator are `O(r)`. The barrier `1/100 − 4 ξ² − 5 η² − 10 ν²` is crossed
inwards near the point and `σ V` grows at a uniform rate inside it
(`Dynamics.Degenerate.unstable_of_barriers`; seeds `(δ* + X* s⁵, Y* s⁴, σ s³, ζ*)`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_invariant_cone (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hC : m.p.C ≠ 0)
    (hP : m.p.Ps = m.p.Pe m.δ) (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ)
    (hM : m.p.M ≠ 0) (hk : m.p.k m.δ ≠ 0) (hKp : m.p.Kp ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hIs : m.p.Is = 0 := by rwa [div_eq_zero_iff, or_iff_left hC] at hI
  have hs0 : m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C) ≠ 0 :=
    mul_ne_zero (div_ne_zero hKp hM) (div_ne_zero hk hC)
  rcases hs0.lt_or_gt with h | h
  · exact unstable_cone_core m hV hIs hC hP hb hM (Or.inl rfl) (by
      rw [show (1 : ℝ) * m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C) =
        m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C) by ring]; exact h)
  · exact unstable_cone_core m hV hIs hC hP hb hM (Or.inr rfl) (by
      rw [show (-1 : ℝ) * m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C) =
        -(m.p.Kp / m.p.M * (m.p.k m.δ / m.p.C)) by ring]; exact neg_neg_of_pos h)

/-- **The balance of the invariant singular plane is never stable.** With `V* = 0`,
`I_s/C = 0` and `(P_s − P_e(δ*))/C = 0`, every selected point is unstable, whatever the swing and
the DC gains: `C = 0` (`mem_den_unstable_of_V_eq_zero_of_C_eq_zero`), an unbalanced frozen swing,
`M = 0`, a negatively damped, saddle or fold swing (`mem_den_unstable_of_invariant`), a flat
curve (`mem_den_unstable_of_invariant_flat`, `…_flat_degenerate`), no DC gains
(`mem_den_unstable_of_invariant_degenerate`), a stiff swing with `K_p = 0 ≠ K_i`
(`mem_den_unstable_of_invariant_stiff_degenerate`) and `K_p ≠ 0`, `k(δ*) ≠ 0`
(`mem_den_unstable_of_invariant_cone`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_invariant_balance (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hP : (m.p.Ps - m.p.Pe m.δ) / m.p.C = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases hC : m.p.C = 0
  · exact mem_den_unstable_of_V_eq_zero_of_C_eq_zero m hV hC
  have hP' : m.p.Ps = m.p.Pe m.δ := by
    rwa [div_eq_zero_iff, or_iff_left hC, sub_eq_zero] at hP
  by_cases hM : m.p.M = 0
  · exact mem_den_unstable_of_invariant m hV hI (Or.inr (Or.inr ⟨by simp [hM], Or.inr (by
      simp [hM])⟩))
  by_cases hb : (m.p.Pff + m.p.Ki * m.ζ - m.p.Pe m.δ) / m.p.M ≠ 0
  · exact mem_den_unstable_of_invariant m hV hI (Or.inl hb)
  push Not at hb
  have hb' : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ := by
    rwa [div_eq_zero_iff, or_iff_left hM, sub_eq_zero] at hb
  by_cases hKp : m.p.Kp = 0
  · by_cases hKi : m.p.Ki = 0
    · exact mem_den_unstable_of_invariant_degenerate m hV hI hP hKp hKi
    by_cases hst : 0 < m.p.k m.δ / m.p.M ∧ 0 ≤ m.p.D / m.p.M
    · exact mem_den_unstable_of_invariant_stiff_degenerate m hV hI hC hP' hb' hst.1 hst.2
        (Or.inr hKi) (by rw [hKp, zero_mul])
    rw [not_and_or, not_lt, not_le] at hst
    rcases hst with hk | hD
    · by_cases hA : m.p.A ≠ 0 ∨ m.p.D / m.p.M ≤ 0
      · exact mem_den_unstable_of_invariant m hV hI (Or.inr (Or.inr ⟨hk, hA⟩))
      push Not at hA
      exact mem_den_unstable_of_invariant_flat m hV hI hA.1 hKi
    · exact mem_den_unstable_of_invariant m hV hI (Or.inr (Or.inl hD))
  by_cases hk : m.p.k m.δ = 0
  · by_cases hA : m.p.A = 0
    · by_cases hKi : m.p.Ki = 0
      · by_cases hD : m.p.D = 0
        · exact mem_den_unstable_of_invariant m hV hI (Or.inr (Or.inr ⟨by simp [hk],
            Or.inr (by simp [hD])⟩))
        · exact mem_den_unstable_of_invariant_flat_degenerate m hV hI hP hA hKi hD
      · exact mem_den_unstable_of_invariant_flat m hV hI hA hKi
    · exact mem_den_unstable_of_invariant m hV hI (Or.inr (Or.inr ⟨by simp [hk], Or.inl hA⟩))
  exact mem_den_unstable_of_invariant_cone m hV hI hC hP' hb' hM hk hKp

/-- **Lyapunov stability on the invariant singular plane: complete decision.** For a selected
point with `V* = 0` and a source current that does not cross the plane (`I_s/C = 0`), Lyapunov
stability holds exactly when the DC node is driven into the plane, `(P_s − P_e(δ*))/C < 0`, and
the swing with the integrator frozen at `ζ*` is balanced, `(P_ff + K_i ζ* − P_e(δ*))/M = 0`, and
either stiff and not negatively damped (`0 ≤ D/M`, `0 < k(δ*)/M`) or flat, undriven by the
integrator and damped (`A = 0`, `K_i = 0`, `0 < D/M`): the collapse is
`mem_den_lyapunovStable_iff_of_invariant`, the repulsion `mem_den_unstable_of_repel`, the balance
`mem_den_unstable_of_invariant_balance`. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_invariant_plane (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      (m.p.Ps - m.p.Pe m.δ) / m.p.C < 0 ∧ (m.p.Pff + m.p.Ki * m.ζ - m.p.Pe m.δ) / m.p.M = 0 ∧
        ((0 ≤ m.p.D / m.p.M ∧ 0 < m.p.k m.δ / m.p.M) ∨
          (m.p.A = 0 ∧ m.p.Ki = 0 ∧ 0 < m.p.D / m.p.M))) := by
  unfold TMIO.Statement
  rcases lt_trichotomy ((m.p.Ps - m.p.Pe m.δ) / m.p.C) 0 with h | h | h
  · have hc := mem_den_lyapunovStable_iff_of_invariant m hV hI h
    unfold TMIO.Statement at hc
    rw [hc]
    exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · have hu := mem_den_unstable_of_invariant_balance m hV hI h
    unfold TMIO.Statement at hu
    exact ⟨fun hs => absurd hs (Spectral.not_mem_den_lyapunovStable_of_unstable hu),
      fun h' => absurd h'.1 (by rw [h]; exact lt_irrefl 0)⟩
  · have hu := mem_den_unstable_of_repel m hV h
    unfold TMIO.Statement at hu
    exact ⟨fun hs => absurd hs (Spectral.not_mem_den_lyapunovStable_of_unstable hu),
      fun h' => absurd h'.1 (not_lt.mpr h.le)⟩

end VSMDC

end powerlib.GFM.DCLink
