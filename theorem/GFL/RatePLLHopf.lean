import theorem.GFL.RatePLL
import theorem.Dynamics.Calculus
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.Dynamics.Degenerate.WeakFocus

/-! # Rate-coupled GFL PLL at the boundary angle: Hopf normal form

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold: `theorem/CurrentDirection.agda`.

Model boundary.
The model of `theorem/GFL/RatePLL.lean`, unchanged: a single
grid-following converter on an infinite bus of amplitude `V` behind a lossless inductive line
`X_g = ω_s L_g`; three-phase balanced averaged dq model in the PLL frame, continuous time. States,
in order: `θ` (PLL error angle), `x` (PLL integrator). Ideal current loop with the d-axis current
`i_d` (into the converter) a frozen parameter, `I_q = 0`; the only line dynamics kept is the
speed-EMF coupling `−L_g u i_d`, `v_q = −V sin θ − X_g i_d − L_g u i_d`; SRF-PLL
`u = k_p v_q + k_i x`, `D₀ = 1 + k_p L_g i_d`. No PWM, delay,
limiter, dc link, outer loop, line resistance or `L_f`. Every parameter is an arbitrary real, as
in `RatePLL.family`. All statements are local, about the full nonlinear field translated to the
selected point `(θ*, 0)` (`RatePLL.Model.field`).

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (推论二 `tan θ_H`, 推论五 GFL 速率耦合 Hopf 全参数亚临界,
lyap1 网格); model `GFLRate` in `.../archive/simulation/src/gfl_gfm_contrast_sim/models.py`.
Normal form and `κ` derived in SymPy (Kuznetsov's planar `l₁` formula cross-checked numerically).

Results.
Normal form (static). Write `A = V cos θ*`, `B = V sin θ*`, `b = −L_g i_d`, `α = k_i/D₀`,
`β = k_p/D₀`, `φ = θ − θ*`, `w = x − b φ` and `N(φ) = A(φ − sin φ) + B(1 − cos φ)` (`hopfN`). At a
balanced point the corrected integrator obeys `ẇ = −Aφ + N(φ)` exactly, and on the boundary
`tr J = 0` (i.e. `k_i b = k_p A`, the angle `tan θ* = ω_s k_p/k_i` of `RatePLL`) the angle obeys
`φ̇ = αw + βN(φ)`: a sinusoidal Liénard system with `det J = αA > 0`. The normal-form
polynomials and their identities are generic, in `Dynamics.Degenerate`
(`theorem/Dynamics/Degenerate/WeakFocus.lean`):
* `hopf_lie_poly`: for the explicit polynomial `hopfW` (quadratic part `(φ² + (α/A) w²)/2`, six
  cubic/quartic monomials) the derivative along the cubic truncation `N₃ = Bφ²/2 + Aφ³/6` is
  `−κ (φ² + (α/A) w²)²` plus eight monomials of degree five and six, with
  `κ = −β(A² + B²)/(16A) = −k_p V²/(16 D₀ V cos θ*)` (`hopfκ`; first Lyapunov quantity, computed in
  SymPy and checked here by `field_simp; ring`).
* `hopfN_sub_hopfN3_isBigO`: `N − N₃ = O(φ⁴)` (Mathlib's `Real.sin_bound`, `Real.cos_bound`).
* `hasFDerivAt_lyapPoly`, `contDiff_lyapPoly`: derivative and smoothness of the polynomial in the
  coordinates `(φ, w)`.
Since `α/A = det J/A² > 0`, `κ > 0 ⇔ k_p k_i < 0`.

Family and connection conclusions.
* `mem_den_locallyAsymptoticallyStable_of_hopf`: on the boundary (balanced, `D₀ ≠ 0`, `tr J = 0`,
  `det J > 0`) with `k_p k_i < 0` the point is locally asymptotically stable — a supercritical
  Hopf point, decided by `hopfW` through `Dynamics.localAsymptoticStable_of_eventually_lyapunov`.
* `mem_den_unstable_of_hopf`: on the boundary with `k_p k_i > 0` it is unstable (subcritical;
  Chetaev with the same polynomial, `Dynamics.unstable_of_eventually_chetaev`).
* `mem_den_unstable_of_tan_eq`: with physical gains (`V, k_p, k_i, ω_s > 0`, `D₀ > 0`,
  `cos θ > 0`) the point exactly at the boundary angle `tan θ = ω_s k_p/k_i` is unstable;
  `mem_den_locallyAsymptoticallyStable_iff_tan_lt`: with physical gains the point is locally
  asymptotically stable iff `tan θ < ω_s k_p/k_i`.
* `mem_den_locallyAsymptoticallyStable_iff`: **complete membership** — locally asymptotically
  stable iff balanced with `D₀ ≠ 0`, `det J > 0` and (`tr J < 0` or (`tr J = 0` and
  `k_p k_i < 0`)). The remaining cases fail: non-equilibrium (unstable); `D₀ = 0` (frozen angle);
  `det J < 0` or `tr J > 0` (linear instability); `det J = 0` (a line of equilibria for `k_i = 0`
  or `V = 0`, `Dynamics.not_localAsymptoticStable_of_equilibria`; the fold `cos θ* = 0`, where
  `x + L_g i_d θ` is monotone along the flow, `ẇ = V sin θ*(1 − cos φ)`); `tr J = 0` with `k_p = 0`
  (conserved energy `α w²/2 + A(1 − cos φ) − B(φ − sin φ)`) or `k_p k_i > 0` (subcritical).
* `not_exact_locallyAsymptoticallyStable`: the local asymptotic translation of `RatePLL.family`
  (`{equilibrium, jacobianStable}`) is **not exact**. Witness `supercriticalPLL`
  (`V = √2`, `X_g = ω_s = 1`, `k_p = −1/2`, `k_i = 1/2`, `i_d = 1`, `θ* = −π/4`; `D₀ = 1/2`,
  `tr J = 0`, `det J = 1`), locally asymptotically stable
  (`supercriticalPLL_mem_den_locallyAsymptoticallyStable`) with a trace-zero Jacobian.

Scope note: the source's numerical finding that the rate-coupled Hopf is subcritical over its whole
(physical) parameter grid is proved here for every `k_p k_i > 0`; it does not extend to gains of
opposite signs, which give a supercritical boundary.
-/

noncomputable section
namespace powerlib.GFL.RatePLL
open Filter Topology Asymptotics
open powerlib.Dynamics.Degenerate (hopfN hopfN3 lyapPoly lyapPolyφ lyapPolyw hopfκ hopfW hopfWφ
  hopfWw hopf_lie_poly hopfN_sub_hopfN3_isBigO hasFDerivAt_lyapPoly contDiff_lyapPoly)

/-! ## Local analysis of the normal form (implementation evidence) -/

section NormalForm

private theorem coord0_isBigO (b : ℝ) :
    (fun z : Dynamics.State 2 => z 0) =O[𝓝 0] fun z => |z 0| + |z 1 - b * z 0| :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (le_abs_self _))

private theorem coord1_isBigO (b : ℝ) :
    (fun z : Dynamics.State 2 => z 1 - b * z 0) =O[𝓝 0] fun z => |z 0| + |z 1 - b * z 0| :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (le_abs_self _))

private theorem size_tendsto (b : ℝ) :
    Tendsto (fun z : Dynamics.State 2 => |z 0| + |z 1 - b * z 0|) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun z : Dynamics.State 2 => |z 0| + |z 1 - b * z 0|) := by fun_prop
  simpa using hc.tendsto 0

private theorem mono_isBigO {f : Dynamics.State 2 → ℝ} (b c : ℝ) (i j k : ℕ) (h : k ≤ i + j)
    (hf : ∀ z, f z = c * (z 0 ^ i * (z 1 - b * z 0) ^ j)) :
    f =O[𝓝 0] fun z => (|z 0| + |z 1 - b * z 0|) ^ k := by
  have := ((Dynamics.isBigO_monomial (coord0_isBigO b) (coord1_isBigO b) i j).trans
    (Dynamics.isBigO_pow_of_tendsto (size_tendsto b) h)).const_mul_left c
  exact this.congr_left fun z => (hf z).symm

private theorem lyapPolyφ_isBigO (b c₂ c₃ c₄ c₅ c₆ : ℝ) :
    (fun z : Dynamics.State 2 => lyapPolyφ c₂ c₃ c₄ c₅ c₆ (z 0) (z 1 - b * z 0)) =O[𝓝 0]
      fun z => (|z 0| + |z 1 - b * z 0|) ^ 1 := by
  unfold lyapPolyφ
  exact (((((mono_isBigO b 1 1 0 1 le_rfl fun z => by ring).add
    (mono_isBigO b (2 * c₂) 1 1 1 (by norm_num) fun z => by ring)).add
    (mono_isBigO b (3 * c₃) 2 0 1 (by norm_num) fun z => by ring)).add
    (mono_isBigO b c₄ 0 3 1 (by norm_num) fun z => by ring)).add
    (mono_isBigO b (3 * c₅) 2 1 1 (by norm_num) fun z => by ring)).add
    (mono_isBigO b (4 * c₆) 3 0 1 (by norm_num) fun z => by ring)

private theorem lyapPolyw_isBigO (b q c₀ c₂ c₄ c₅ : ℝ) :
    (fun z : Dynamics.State 2 => lyapPolyw q c₀ c₂ c₄ c₅ (z 0) (z 1 - b * z 0)) =O[𝓝 0]
      fun z => (|z 0| + |z 1 - b * z 0|) ^ 1 := by
  unfold lyapPolyw
  exact ((((mono_isBigO b q 0 1 1 le_rfl fun z => by ring).add
    (mono_isBigO b (3 * c₀) 0 2 1 (by norm_num) fun z => by ring)).add
    (mono_isBigO b c₂ 2 0 1 (by norm_num) fun z => by ring)).add
    (mono_isBigO b (3 * c₄) 1 2 1 (by norm_num) fun z => by ring)).add
    (mono_isBigO b c₅ 3 0 1 (by norm_num) fun z => by ring)

/-- The cubic and quartic part of `lyapPoly` is `O(s³)`. -/
private theorem lyapPoly_sub_isBigO (b q c₀ c₂ c₃ c₄ c₅ c₆ : ℝ) :
    (fun z : Dynamics.State 2 => lyapPoly q c₀ c₂ c₃ c₄ c₅ c₆ (z 0) (z 1 - b * z 0) -
        1 / 2 * (z 0 ^ 2 + q * (z 1 - b * z 0) ^ 2)) =O[𝓝 0]
      fun z => (|z 0| + |z 1 - b * z 0|) ^ 3 := by
  have := (((((mono_isBigO (f := fun z => c₀ * (z 1 - b * z 0) ^ 3) b c₀ 0 3 3 le_rfl
      fun z => by ring).add
    (mono_isBigO (f := fun z => c₂ * (z 0 ^ 2 * (z 1 - b * z 0))) b c₂ 2 1 3 le_rfl
      fun z => by ring)).add
    (mono_isBigO (f := fun z => c₃ * z 0 ^ 3) b c₃ 3 0 3 le_rfl fun z => by ring)).add
    (mono_isBigO (f := fun z => c₄ * (z 0 * (z 1 - b * z 0) ^ 3)) b c₄ 1 3 3 (by norm_num)
      fun z => by ring)).add
    (mono_isBigO (f := fun z => c₅ * (z 0 ^ 3 * (z 1 - b * z 0))) b c₅ 3 1 3 (by norm_num)
      fun z => by ring)).add
    (mono_isBigO (f := fun z => c₆ * z 0 ^ 4) b c₆ 4 0 3 (by norm_num) fun z => by ring)
  refine this.congr_left fun z => ?_
  unfold lyapPoly
  ring

/-- `s² ≤ 2(1 + 1/ρ)(φ² + ρw²)` for `ρ > 0`. -/
private theorem size_sq_le {ρ : ℝ} (hρ : 0 < ρ) (φ w : ℝ) :
    (|φ| + |w|) ^ 2 ≤ 2 * (1 + 1 / ρ) * (φ ^ 2 + ρ * w ^ 2) := by
  have h1 : (|φ| + |w|) ^ 2 ≤ 2 * φ ^ 2 + 2 * w ^ 2 := by
    nlinarith [sq_abs φ, sq_abs w, sq_nonneg (|φ| - |w|)]
  have h2 : 2 * (1 + 1 / ρ) * (φ ^ 2 + ρ * w ^ 2) =
      2 * φ ^ 2 + 2 * w ^ 2 + 2 * ρ * w ^ 2 + 2 / ρ * φ ^ 2 := by
    field_simp
    ring
  have h3 : 0 ≤ 2 * ρ * w ^ 2 := by positivity
  have h4 : 0 ≤ 2 / ρ * φ ^ 2 := by positivity
  linarith

/-- The quadratic form `φ² + ρ w²` vanishes only at the origin. -/
private theorem quad_pos {ρ b : ℝ} (hρ : 0 < ρ) {z : Dynamics.State 2} (hz : z ≠ 0) :
    0 < z 0 ^ 2 + ρ * (z 1 - b * z 0) ^ 2 := by
  by_contra h
  push Not at h
  have h0 : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 - b * z 0)]
  have h1 : z 1 - b * z 0 = 0 := by
    have : ρ * (z 1 - b * z 0) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (z 0)]
    have : (z 1 - b * z 0) ^ 2 ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
  apply hz
  ext i
  fin_cases i
  · simpa using h0
  · simp only [Fin.mk_one, PiLp.zero_apply]
    rw [h0, mul_zero, sub_zero] at h1
    exact h1

variable {A B α β b : ℝ}

/-- The Lie derivative of the normal-form Lyapunov polynomial along a field in normal form. -/
private theorem hopf_lie_eq {g : Dynamics.State 2 → Dynamics.State 2}
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) (z : Dynamics.State 2) :
    fderiv ℝ (fun z : Dynamics.State 2 => hopfW A B α β (z 0) (z 1 - b * z 0)) z (g z) =
      hopfWφ A B α β (z 0) (z 1 - b * z 0) * (α * (z 1 - b * z 0) + β * hopfN A B (z 0)) +
        hopfWw A B α β (z 0) (z 1 - b * z 0) * (-A * z 0 + hopfN A B (z 0)) := by
  have hd : HasFDerivAt (fun z : Dynamics.State 2 => hopfW A B α β (z 0) (z 1 - b * z 0))
      (hopfWφ A B α β (z 0) (z 1 - b * z 0) •
          (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ) +
        hopfWw A B α β (z 0) (z 1 - b * z 0) •
          ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : Dynamics.State 2 →L[ℝ] ℝ) -
            b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ))) z :=
    hasFDerivAt_lyapPoly _ _ _ _ _ _ _ b z
  rw [hd.fderiv, ← hg0 z, ← hg1 z]
  simp

/-- Normal form: `V̇ + κ Q² = o(Q²)`, `Q = φ² + (α/A) w²`. -/
private theorem hopf_lie_isLittleO (hA : A ≠ 0) (hα : α ≠ 0) (hq : 0 < α / A)
    {g : Dynamics.State 2 → Dynamics.State 2}
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) :
    (fun z => fderiv ℝ (fun z : Dynamics.State 2 => hopfW A B α β (z 0) (z 1 - b * z 0)) z (g z) +
        hopfκ A B β * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) ^ 2) =o[𝓝 0]
      fun z => (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) ^ 2 := by
  set s : Dynamics.State 2 → ℝ := fun z => |z 0| + |z 1 - b * z 0| with hs
  -- the eight monomials of degree five and six
  have hR : (fun z : Dynamics.State 2 =>
      B * α * β ^ 2 * (A ^ 2 + B ^ 2) / (32 * A ^ 3) * (z 0 ^ 2 * (z 1 - b * z 0) ^ 3) +
      B * α * β * (25 * A ^ 2 + 9 * B ^ 2) / (96 * A ^ 3) * (z 0 ^ 3 * (z 1 - b * z 0) ^ 2) +
      α * β ^ 2 * (A ^ 2 + B ^ 2) / (96 * A ^ 2) * (z 0 ^ 3 * (z 1 - b * z 0) ^ 3) +
      B * β ^ 2 * (31 * A ^ 2 - 9 * B ^ 2) / (96 * A ^ 2) * (z 0 ^ 4 * (z 1 - b * z 0) ^ 1) +
      α * β * (A ^ 2 + B ^ 2) / (32 * A ^ 2) * (z 0 ^ 4 * (z 1 - b * z 0) ^ 2) +
      -B * β * (A ^ 2 * α + 8 * A * B ^ 2 * β ^ 2 + B ^ 2 * α) / (32 * A ^ 2 * α) *
        (z 0 ^ 5 * (z 1 - b * z 0) ^ 0) +
      β ^ 2 * (5 * A ^ 2 - 3 * B ^ 2) / (96 * A) * (z 0 ^ 5 * (z 1 - b * z 0) ^ 1) +
      -β * (A ^ 2 * α + 8 * A * B ^ 2 * β ^ 2 + B ^ 2 * α) / (96 * A * α) *
        (z 0 ^ 6 * (z 1 - b * z 0) ^ 0)) =O[𝓝 0] fun z => s z ^ 5 :=
    ((((((((mono_isBigO b _ 2 3 5 le_rfl fun z => rfl).add
      (mono_isBigO b _ 3 2 5 le_rfl fun z => rfl)).add
      (mono_isBigO b _ 3 3 5 (by norm_num) fun z => rfl)).add
      (mono_isBigO b _ 4 1 5 le_rfl fun z => rfl)).add
      (mono_isBigO b _ 4 2 5 (by norm_num) fun z => rfl)).add
      (mono_isBigO b _ 5 0 5 le_rfl fun z => rfl)).add
      (mono_isBigO b _ 5 1 5 (by norm_num) fun z => rfl)).add
      (mono_isBigO b _ 6 0 5 (by norm_num) fun z => rfl))
  -- the Taylor remainder of `N` times the gradient
  have hN : (fun z : Dynamics.State 2 => hopfN A B (z 0) - hopfN3 A B (z 0)) =O[𝓝 0]
      fun z => s z ^ 4 := by
    have h1 := (hopfN_sub_hopfN3_isBigO A B).comp_tendsto
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
        Dynamics.State 2 →L[ℝ] ℝ).continuous.tendsto' 0 0 (by simp))
    exact h1.trans ((coord0_isBigO b).pow 4)
  have hG : (fun z : Dynamics.State 2 =>
      β * hopfWφ A B α β (z 0) (z 1 - b * z 0) + hopfWw A B α β (z 0) (z 1 - b * z 0)) =O[𝓝 0]
      fun z => s z ^ 1 :=
    ((lyapPolyφ_isBigO b _ _ _ _ _).const_mul_left β).add (lyapPolyw_isBigO b _ _ _ _ _)
  have hNG := (hN.mul hG).congr_right (fun z => by rw [← pow_add])
  have htot : (fun z => fderiv ℝ (fun z : Dynamics.State 2 => hopfW A B α β (z 0)
      (z 1 - b * z 0)) z (g z) + hopfκ A B β * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) ^ 2)
      =O[𝓝 0] fun z => s z ^ 5 := by
    refine (hR.add hNG).congr_left fun z => ?_
    rw [hopf_lie_eq hg0 hg1 z]
    linear_combination (-1 : ℝ) * hopf_lie_poly (B := B) (β := β) hA hα (z 0) (z 1 - b * z 0)
  have hs4 : (fun z => s z ^ 4) =O[𝓝 0]
      fun z => (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) ^ 2 := by
    refine IsBigO.of_bound ((2 * (1 + 1 / (α / A))) ^ 2) (Eventually.of_forall fun z => ?_)
    have h := size_sq_le hq (z 0) (z 1 - b * z 0)
    have hQ : 0 ≤ z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    calc s z ^ 4 = (s z ^ 2) ^ 2 := by ring
      _ ≤ (2 * (1 + 1 / (α / A)) * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h 2
      _ = _ := by ring
  exact htot.trans_isLittleO ((Dynamics.isLittleO_pow_of_tendsto (size_tendsto b)
    (by norm_num : 4 < 5)).trans_isBigO hs4)

/-- `W − Q/2 = o(Q/2)`. -/
private theorem hopfW_isLittleO (hq : 0 < α / A) :
    (fun z : Dynamics.State 2 => hopfW A B α β (z 0) (z 1 - b * z 0) -
        1 / 2 * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2)) =o[𝓝 0]
      fun z => 1 / 2 * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) := by
  have hs2 : (fun z : Dynamics.State 2 => (|z 0| + |z 1 - b * z 0|) ^ 2) =O[𝓝 0]
      fun z => 1 / 2 * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) := by
    refine IsBigO.of_bound (4 * (1 + 1 / (α / A))) (Eventually.of_forall fun z => ?_)
    have h := size_sq_le hq (z 0) (z 1 - b * z 0)
    have hQ : 0 ≤ 1 / 2 * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (|z 0| + |z 1 - b * z 0|)),
      abs_of_nonneg hQ]
    linarith
  exact (lyapPoly_sub_isBigO b _ _ _ _ _ _ _).trans_isLittleO
    ((Dynamics.isLittleO_pow_of_tendsto (size_tendsto b) (by norm_num : 2 < 3)).trans_isBigO hs2)

/-- A field in normal form vanishes at the origin. -/
private theorem hopf_field_zero {g : Dynamics.State 2 → Dynamics.State 2}
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) : g 0 = 0 := by
  have h0 := hg0 0
  have h1 := hg1 0
  simp only [PiLp.zero_apply, mul_zero, hopfN, Real.sin_zero, Real.cos_zero,
    sub_self, add_zero] at h0 h1
  ext i
  fin_cases i
  · simpa using h0
  · simp only [Fin.mk_one, PiLp.zero_apply]
    rw [h0, mul_zero, sub_zero] at h1
    exact h1

/-- **Supercritical boundary.** A `C¹` field in normal form with `κ > 0` is locally
asymptotically stable at the origin. -/
private theorem hopf_las (hA : A ≠ 0) (hα : α ≠ 0) (hq : 0 < α / A) (hκ : 0 < hopfκ A B β)
    {g : Dynamics.State 2 → Dynamics.State 2} (hgc : ContDiff ℝ 1 g)
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) :
    LocalAsymptoticStable g 0 := by
  have hQ : ∀ᶠ z in 𝓝[≠] (0 : Dynamics.State 2), 0 < z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2 :=
    eventually_nhdsWithin_of_forall fun z hz => quad_pos hq hz
  refine Dynamics.localAsymptoticStable_of_eventually_lyapunov
    (W := fun z => hopfW A B α β (z 0) (z 1 - b * z 0)) two_pos hgc (hopf_field_zero hg0 hg1)
    (contDiff_lyapPoly _ _ _ _ _ _ _ b) (by simp [hopfW, lyapPoly]) ?_ ?_
  · exact Dynamics.eventually_pos_of_isLittleO
      (q := fun z => 1 / 2 * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2))
      (hQ.mono fun z hz => by positivity) ((hopfW_isLittleO hq).mono nhdsWithin_le_nhds)
  · exact Dynamics.eventually_neg_of_isLittleO
      (q := fun z => hopfκ A B β * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) ^ 2)
      (hQ.mono fun z hz => by positivity)
      (((hopf_lie_isLittleO hA hα hq hg0 hg1).const_mul_right hκ.ne').mono nhdsWithin_le_nhds)

/-- **Subcritical boundary.** A `C¹` field in normal form with `κ < 0` is unstable at the
origin (Chetaev with the same polynomial). -/
private theorem hopf_unstable (hA : A ≠ 0) (hα : α ≠ 0) (hq : 0 < α / A)
    (hκ : hopfκ A B β < 0) {g : Dynamics.State 2 → Dynamics.State 2} (hgc : ContDiff ℝ 1 g)
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + β * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) :
    Unstable g 0 := by
  have hQ : ∀ᶠ z in 𝓝[≠] (0 : Dynamics.State 2), 0 < z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2 :=
    eventually_nhdsWithin_of_forall fun z hz => quad_pos hq hz
  have hκ' : 0 < -hopfκ A B β := neg_pos.mpr hκ
  refine Dynamics.unstable_of_eventually_chetaev
    (W := fun z => hopfW A B α β (z 0) (z 1 - b * z 0)) two_pos hgc
    (contDiff_lyapPoly _ _ _ _ _ _ _ b) (by simp [hopfW, lyapPoly]) ?_ ?_
  · exact Dynamics.eventually_pos_of_isLittleO
      (q := fun z => 1 / 2 * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2))
      (hQ.mono fun z hz => by positivity) ((hopfW_isLittleO hq).mono nhdsWithin_le_nhds)
  · refine Dynamics.eventually_pos_of_isLittleO
      (q := fun z => -hopfκ A B β * (z 0 ^ 2 + α / A * (z 1 - b * z 0) ^ 2) ^ 2)
      (hQ.mono fun z hz => by positivity) ?_
    refine (((hopf_lie_isLittleO hA hα hq hg0 hg1).const_mul_right hκ'.ne').mono
      nhdsWithin_le_nhds).congr_left fun z => ?_
    ring

/-- **Conservative boundary.** With `β = 0` the normal form conserves
`E = α w²/2 + A(1 − cos φ) − B(φ − sin φ)`, so the origin is not locally asymptotically
stable. -/
private theorem hopf_conservative_not_las (hα : α ≠ 0) {g : Dynamics.State 2 → Dynamics.State 2}
    (hgc : ContDiff ℝ 1 g)
    (hg0 : ∀ z, g z 0 = α * (z 1 - b * z 0) + 0 * hopfN A B (z 0))
    (hg1 : ∀ z, g z 1 - b * g z 0 = -A * z 0 + hopfN A B (z 0)) :
    ¬ LocalAsymptoticStable g 0 := by
  set E : Dynamics.State 2 → ℝ := fun z => -α * (α / 2 * (z 1 - b * z 0) ^ 2 +
    A * (1 - Real.cos (z 0)) - B * (z 0 - Real.sin (z 0))) with hE
  have hd : ∀ z : Dynamics.State 2, HasFDerivAt E
      ((-α * (A * Real.sin (z 0) - B * (1 - Real.cos (z 0)))) •
          (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ) +
        (-α * (α * (z 1 - b * z 0))) •
          ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : Dynamics.State 2 →L[ℝ] ℝ) -
            b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ))) z := by
    intro z
    have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
    have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
    have hw := h1.sub (h0.const_mul b)
    have hc := (Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z h0
    have hs := (Real.hasDerivAt_sin (z 0)).comp_hasFDerivAt z h0
    have h := ((((hw.pow 2).const_mul (α / 2)).add ((hc.const_sub 1).const_mul A)).sub
      ((h0.sub hs).const_mul B)).const_mul (-α)
    refine h.congr_fderiv ?_
    ext v
    simp
    ring
  have hEd : Differentiable ℝ E := fun z => (hd z).differentiableAt
  refine Dynamics.not_localAsymptoticStable_of_eventually_lie_nonpos hgc hEd
    (Eventually.of_forall fun z => ?_) ?_
  · rw [(hd z).fderiv]
    have key : (-α * (A * Real.sin (z 0) - B * (1 - Real.cos (z 0)))) * (g z) 0 +
        (-α * (α * (z 1 - b * z 0))) * ((g z) 1 - b * (g z) 0) = 0 := by
      rw [hg1 z, hg0 z]
      unfold hopfN
      ring
    simp only [add_apply, smul_apply, sub_apply, PiLp.proj_apply, smul_eq_mul]
    linarith [key]
  · rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨EuclideanSpace.single 1 (ε / 2), hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.single, PiLp.norm_single,
        Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    · simp only [hE, PiLp.zero_apply]
      simp
      have h2 : 0 < α ^ 2 * ε ^ 2 := by positivity
      nlinarith [h2]

end NormalForm

/-! ## The rate-coupled PLL at the boundary angle -/

section Boundary

private theorem gridQ_shift (p : Params) {θ : ℝ} (heq : p.V * Real.sin θ = -(p.Xg * p.Id))
    (φ : ℝ) : gridQ p (φ + θ) =
      -(p.V * Real.cos θ) * φ + hopfN (p.V * Real.cos θ) (p.V * Real.sin θ) φ := by
  unfold gridQ hopfN
  rw [Real.sin_add]
  linear_combination -heq

private theorem model_field0 (m : Model) (z : Dynamics.State 2) :
    m.field z 0 = (m.params.kp * gridQ m.params (z 0 + m.θ) + m.params.ki * z 1) / m.params.D0 := by
  simp [Model.field, RatePLL.field, Dynamics.lift, coordField, equilibrium, pllOut]

private theorem model_field1 (m : Model) (z : Dynamics.State 2) :
    m.field z 1 = gridQ m.params (z 0 + m.θ) - m.params.Lg * m.field z 0 * m.params.Id := by
  simp [Model.field, RatePLL.field, Dynamics.lift, coordField, equilibrium, pllOut, vq]

/-- `ẇ = ḣ`: the PLL integrator corrected by the speed-EMF term, `w = x + L_g i_d θ`, is driven by
the grid q-voltage alone. -/
private theorem model_hg1 {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (z : Dynamics.State 2) :
    m.field z 1 - -(m.params.Lg * m.params.Id) * m.field z 0 =
      -(m.params.V * Real.cos m.θ) * z 0 +
        hopfN (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ) (z 0) := by
  rw [model_field1, ← gridQ_shift m.params heq]
  ring

/-- On the boundary (`tr J = 0`) the angle equation is `θ̇ = α w + β N(φ)`. -/
private theorem model_hg0 {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id))
    (hD0 : m.params.D0 ≠ 0) (htr : (jac m.params m.θ).trace = 0) (z : Dynamics.State 2) :
    m.field z 0 = m.params.ki / m.params.D0 * (z 1 - -(m.params.Lg * m.params.Id) * z 0) +
      m.params.kp / m.params.D0 *
        hopfN (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ) (z 0) := by
  have htr' : -m.params.kp * m.params.V * Real.cos m.θ - m.params.ki * m.params.Lg * m.params.Id
      = 0 := by
    rw [trace_jac, div_eq_zero_iff] at htr
    exact htr.resolve_right hD0
  rw [model_field0, gridQ_shift m.params heq]
  field_simp
  linear_combination (z 0) * htr'

/-- `α / A = det J / A² > 0` on the boundary. -/
private theorem model_ratio_pos {m : Model} (hD0 : m.params.D0 ≠ 0)
    (hdet : 0 < (jac m.params m.θ).det) :
    m.params.V * Real.cos m.θ ≠ 0 ∧ m.params.ki / m.params.D0 ≠ 0 ∧
      0 < m.params.ki / m.params.D0 / (m.params.V * Real.cos m.θ) := by
  rw [det_jac m.params hD0] at hdet
  have hA : m.params.V * Real.cos m.θ ≠ 0 := by
    intro h
    rw [mul_assoc, h, mul_zero, zero_div] at hdet
    exact lt_irrefl 0 hdet
  have hα : m.params.ki / m.params.D0 ≠ 0 := by
    intro h
    have : m.params.ki = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hD0
    rw [this, zero_mul, zero_mul, zero_div] at hdet
    exact lt_irrefl 0 hdet
  refine ⟨hA, hα, ?_⟩
  have : m.params.ki / m.params.D0 / (m.params.V * Real.cos m.θ) =
      m.params.ki * m.params.V * Real.cos m.θ / m.params.D0 /
        (m.params.V * Real.cos m.θ) ^ 2 := by
    field_simp
  rw [this]
  positivity

/-- The sign of the normal-form coefficient: `κ > 0 ↔ k_p k_i < 0`. -/
private theorem model_kappa_sign {m : Model} (hD0 : m.params.D0 ≠ 0)
    (hdet : 0 < (jac m.params m.θ).det) :
    (m.params.kp * m.params.ki < 0 →
      0 < hopfκ (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ)
        (m.params.kp / m.params.D0)) ∧
    (0 < m.params.kp * m.params.ki →
      hopfκ (m.params.V * Real.cos m.θ) (m.params.V * Real.sin m.θ)
        (m.params.kp / m.params.D0) < 0) := by
  obtain ⟨hA, -, hq⟩ := model_ratio_pos hD0 hdet
  set A := m.params.V * Real.cos m.θ
  set B := m.params.V * Real.sin m.θ
  have hAB : 0 < A ^ 2 + B ^ 2 := by positivity
  have hκ : hopfκ A B (m.params.kp / m.params.D0) =
      -(A ^ 2 + B ^ 2) / 16 * (m.params.kp / m.params.D0 / A) := by
    unfold hopfκ; field_simp
  have hprod : m.params.kp / m.params.D0 / A * (m.params.ki / m.params.D0 / A) =
      m.params.kp * m.params.ki / (m.params.D0 * A) ^ 2 := by
    field_simp
  have hDA : 0 < (m.params.D0 * A) ^ 2 := by positivity
  rw [hκ]
  constructor
  · intro hk
    have h1 : m.params.kp / m.params.D0 / A * (m.params.ki / m.params.D0 / A) < 0 := by
      rw [hprod]; exact div_neg_of_neg_of_pos hk hDA
    have h2 : m.params.kp / m.params.D0 / A < 0 := by
      by_contra hc; push Not at hc; nlinarith
    have h3 : -(A ^ 2 + B ^ 2) / 16 < 0 := by linarith
    nlinarith
  · intro hk
    have h1 : 0 < m.params.kp / m.params.D0 / A * (m.params.ki / m.params.D0 / A) := by
      rw [hprod]; exact div_pos hk hDA
    have h2 : 0 < m.params.kp / m.params.D0 / A := by
      by_contra hc; push Not at hc; nlinarith
    have h3 : -(A ^ 2 + B ^ 2) / 16 < 0 := by linarith
    nlinarith

/-- Membership through the sound translation. -/
private theorem mem_den_of_meets {m : Model} {s : Sentence}
    (h : ∀ q ∈ translate s, Meets m q) : m ∈ family.den s := by
  have hs := chain_le_semantics
  unfold powerlib.TMIO.Statement at hs
  exact (Family.chain_le_semantics_iff.mp hs s) ((TMIO.mem_realize _ _ _).mpr h)

end Boundary

/-! ## Members of the local asymptotic denotation -/

section Members

/-- States `t e_i` (`t > 0`) accumulate at the origin. -/
private theorem frequently_single (i : Fin 2) {c : ℝ} (hc : c ≠ 0) {P : Dynamics.State 2 → Prop}
    (h : ∀ t : ℝ, 0 < t → P (EuclideanSpace.single i (c * t))) :
    ∃ᶠ z in 𝓝 (0 : Dynamics.State 2), P z := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hc' : 0 < |c| := abs_pos.mpr hc
  refine ⟨EuclideanSpace.single i (c * (ε / (2 * |c|))), hball ?_, h _ (by positivity)⟩
  rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.single, PiLp.norm_single,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < ε / (2 * |c|))]
  field_simp
  linarith

/-- An equilibrium of the translated field with a nondegenerate loop is balanced. -/
private theorem balance_of_model_field_zero {m : Model} (h : m.field 0 = 0) :
    m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id) := by
  have h0 := congrArg (fun y : Dynamics.State 2 => y 0) h
  have h1 := congrArg (fun y : Dynamics.State 2 => y 1) h
  simp only [PiLp.zero_apply] at h0 h1
  rw [model_field1, h0] at h1
  simp only [PiLp.zero_apply, zero_add, mul_zero, zero_mul, sub_zero] at h1
  unfold gridQ at h1
  linarith

/-- With a degenerate loop `D₀ = 0` the angle is frozen. -/
private theorem not_las_of_D0_eq_zero {m : Model} (hD0 : m.params.D0 = 0) :
    ¬ LocalAsymptoticStable m.field 0 := by
  have hd : ∀ z : Dynamics.State 2, HasFDerivAt (fun z : Dynamics.State 2 => -(z 0))
      (-(PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ)) z := fun z =>
    ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)).neg
  refine Dynamics.not_localAsymptoticStable_of_eventually_lie_nonpos m.field_contDiff
    (fun z => (hd z).differentiableAt) (Eventually.of_forall fun z => ?_)
    (frequently_single 0 one_ne_zero fun t ht => ?_)
  · rw [(hd z).fderiv]
    simp [model_field0, hD0]
  · simp only [PiLp.zero_apply, neg_zero, one_mul]
    simp [ht]

/-- A singular Jacobian (`det J = 0`) at a balanced point with `D₀ ≠ 0`: no local asymptotic
stability (a line of equilibria for `k_i = 0` or `V = 0`, the fold `cos θ* = 0` otherwise). -/
private theorem not_las_of_det_eq_zero {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (hdet : (jac m.params m.θ).det = 0) : ¬ LocalAsymptoticStable m.field 0 := by
  rw [det_jac m.params hD0, div_eq_zero_iff] at hdet
  have hkvc : m.params.ki * m.params.V * Real.cos m.θ = 0 := hdet.resolve_right hD0
  have hq0 : gridQ m.params m.θ = 0 := by unfold gridQ; linarith
  by_cases hV : m.params.V = 0
  · -- `V = 0`: the line `x = 0` of equilibria
    have hq : ∀ φ, gridQ m.params φ = 0 := fun φ => by
      unfold gridQ; rw [hV] at heq ⊢; linarith
    refine Dynamics.not_localAsymptoticStable_of_equilibria fun ε hε => ?_
    refine ⟨EuclideanSpace.single 0 (ε / 2), ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun y : Dynamics.State 2 => y 0) h
      simp at this
      linarith
    · rw [sub_zero, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    · have h0 : m.field (EuclideanSpace.single 0 (ε / 2)) 0 = 0 := by
        rw [model_field0]; simp [hq]
      ext i
      fin_cases i
      · simpa using h0
      · simp only [Fin.mk_one, PiLp.zero_apply]
        rw [model_field1, h0]; simp [hq]
  by_cases hki : m.params.ki = 0
  · -- `k_i = 0`: the line `θ = θ*` of equilibria
    refine Dynamics.not_localAsymptoticStable_of_equilibria fun ε hε => ?_
    refine ⟨EuclideanSpace.single 1 (ε / 2), ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun y : Dynamics.State 2 => y 1) h
      simp at this
      linarith
    · rw [sub_zero, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    · have h0 : m.field (EuclideanSpace.single 1 (ε / 2)) 0 = 0 := by
        rw [model_field0]; simp [hki, hq0]
      ext i
      fin_cases i
      · simpa using h0
      · simp only [Fin.mk_one, PiLp.zero_apply]
        rw [model_field1, h0]; simp [hq0]
  -- the fold `cos θ* = 0`: `w = x + L_g i_d θ` is monotone, `ẇ = V sin θ* (1 − cos φ)`
  have hc : Real.cos m.θ = 0 := by
    rcases mul_eq_zero.mp hkvc with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hki
      · exact absurd h hV
    · exact h
  set B := m.params.V * Real.sin m.θ with hB
  set b := -(m.params.Lg * m.params.Id) with hb
  have hBne : B ≠ 0 := by
    intro h
    have hs : Real.sin m.θ = 0 := (mul_eq_zero.mp h).resolve_left hV
    have := Real.sin_sq_add_cos_sq m.θ
    rw [hs, hc] at this
    norm_num at this
  have hd : ∀ z : Dynamics.State 2, HasFDerivAt (fun z : Dynamics.State 2 => -B * (z 1 - b * z 0))
      ((-B) • ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : Dynamics.State 2 →L[ℝ] ℝ) -
        b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ))) z := fun z => by
    have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
    have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
      Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
    exact ((h1.sub (h0.const_mul b)).const_mul (-B)).congr_fderiv (by ext v; simp)
  refine Dynamics.not_localAsymptoticStable_of_eventually_lie_nonpos m.field_contDiff
    (fun z => (hd z).differentiableAt) (Eventually.of_forall fun z => ?_)
    (frequently_single 1 hBne fun t ht => ?_)
  · rw [(hd z).fderiv]
    have h1 := model_hg1 heq z
    rw [hc, mul_zero, neg_zero, zero_mul, zero_add] at h1
    have hcos := Real.cos_le_one (z 0)
    simp only [smul_apply, sub_apply, PiLp.proj_apply, smul_eq_mul]
    rw [h1]
    unfold hopfN
    nlinarith [sq_nonneg B]
  · simp only [PiLp.zero_apply, mul_zero, sub_zero]
    simp
    nlinarith [sq_pos_of_ne_zero hBne]

/-- A supercritical boundary point (`k_p k_i < 0`) is locally asymptotically stable. -/
private theorem las_of_hopf {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hk : m.params.kp * m.params.ki < 0) : LocalAsymptoticStable m.field 0 := by
  obtain ⟨hA, hα, hq⟩ := model_ratio_pos hD0 hdet
  exact hopf_las hA hα hq ((model_kappa_sign hD0 hdet).1 hk) m.field_contDiff
    (model_hg0 heq hD0 htr) (model_hg1 heq)

/-- A subcritical boundary point (`k_p k_i > 0`) is unstable. -/
private theorem unstable_of_hopf {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hk : 0 < m.params.kp * m.params.ki) : Unstable m.field 0 := by
  obtain ⟨hA, hα, hq⟩ := model_ratio_pos hD0 hdet
  exact hopf_unstable hA hα hq ((model_kappa_sign hD0 hdet).2 hk) m.field_contDiff
    (model_hg0 heq hD0 htr) (model_hg1 heq)

/-- A boundary point without proportional gain (`k_p = 0`) conserves an energy. -/
private theorem not_las_of_hopf_kp_eq_zero {m : Model}
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hkp : m.params.kp = 0) : ¬ LocalAsymptoticStable m.field 0 := by
  obtain ⟨-, hα, -⟩ := model_ratio_pos hD0 hdet
  exact hopf_conservative_not_las hα m.field_contDiff
    (fun z => by rw [model_hg0 heq hD0 htr z, hkp, zero_div]) (model_hg1 heq)

end Members

/-! ### Connection conclusions at the boundary angle -/

/-- Rate-coupled GFL PLL on the boundary `tr J = 0` (balanced point, `D₀ ≠ 0`, `det J > 0`)
with gains of opposite signs, `k_p k_i < 0`: a supercritical Hopf point. The Jacobian has the
imaginary pair `± j √det J`, yet the operating point is locally asymptotically stable: the
normal-form polynomial `hopfW` has derivative `−κ (φ² + (α/A) w²)² + O(s⁵)` with
`κ = −k_p V² / (16 D₀ V cos θ*) > 0`. -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_hopf (m : Model)
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hk : m.params.kp * m.params.ki < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  exact las_of_hopf heq hD0 htr hdet hk

/-- Rate-coupled GFL PLL on the boundary `tr J = 0` with gains of equal signs, `k_p k_i > 0`: a
subcritical Hopf point, unstable (Chetaev with the normal-form polynomial, `κ < 0`). -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_unstable_of_hopf (m : Model)
    (heq : m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id)) (hD0 : m.params.D0 ≠ 0)
    (htr : (jac m.params m.θ).trace = 0) (hdet : 0 < (jac m.params m.θ).det)
    (hk : 0 < m.params.kp * m.params.ki) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  exact unstable_of_hopf heq hD0 htr hdet hk

/-- Rate-coupled GFL PLL with physical gains (`V, k_p, k_i, ω_s > 0`, `D₀ > 0`, `cos θ > 0`)
exactly at the boundary angle `tan θ = ω_s k_p / k_i`: the operating point is unstable
(subcritical Hopf). -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_unstable_of_tan_eq (p : Params) (hD0 : 0 < p.D0)
    (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (heq : p.V * Real.sin θ = -(p.Xg * p.Id))
    (htan : Real.tan θ = p.ωs * p.kp / p.ki) :
    connection% (Model.mk p θ ∈ family.den (.flow .unstable)) := by
  obtain ⟨htr, hdet, -⟩ := imaginary_pair_at_boundary p hD0 hV hki hωs hcos heq htan
  exact mem_den_unstable_of_hopf (Model.mk p θ) heq hD0.ne' htr hdet (mul_pos hkp hki)

/-- With physical gains the operating point is locally asymptotically stable exactly below the
boundary angle: `tan θ < ω_s k_p / k_i` (`V, k_p, k_i, ω_s > 0`, `D₀ > 0`, `cos θ > 0`,
`V sin θ = −X_g i_d`). -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_tan_lt (p : Params)
    (hD0 : 0 < p.D0) (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hωs : 0 < p.ωs) {θ : ℝ}
    (hcos : 0 < Real.cos θ) (heq : p.V * Real.sin θ = -(p.Xg * p.Id)) :
    connection% (Model.mk p θ ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      Model.mk p θ ∈ {m : Model | Real.tan m.θ < m.params.ωs * m.params.kp / m.params.ki}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hu : Model.mk p θ ∈ family.den (.flow .unstable) := by
      rcases hc.lt_or_eq with hc | hc
      · have := mem_den_unstable_of_tan_gt p hD0 hV hki hωs hcos heq hc
        unfold powerlib.TMIO.Statement at this
        exact this
      · have := mem_den_unstable_of_tan_eq p hD0 hV hkp hki hωs hcos heq hc.symm
        unfold powerlib.TMIO.Statement at this
        exact this
    rw [family_isAutonomous.mem_den_flow] at h hu
    exact hu h.1
  · intro h
    have := mem_den_locallyExponentiallyStable_of_tan_lt p hD0 hV hki hωs hcos heq h
    unfold powerlib.TMIO.Statement at this
    rw [family_isAutonomous.mem_den_flow] at this ⊢
    exact Flow.locallyExponentiallyStable_localAsymptoticStable this

/-- **Complete membership of the local asymptotic sentence.** A rate-coupled PLL model is locally
asymptotically stable at `(θ*, 0)` exactly when the point is balanced with a nondegenerate loop
(`V sin θ* = −X_g i_d`, `D₀ ≠ 0`), `det J > 0`, and either `tr J < 0` (Hurwitz) or `tr J = 0` with
gains of opposite signs (`k_p k_i < 0`, supercritical Hopf). Everything else fails: a
non-equilibrium or `D₀ = 0` (frozen angle); `det J < 0` or `tr J > 0` (linear instability);
`det J = 0` (a line of equilibria for `k_i = 0` or `V = 0`, the monotone fold coordinate
`x + L_g i_d θ` for `cos θ* = 0`); `tr J = 0` with `k_p = 0` (conserved energy) or `k_p k_i > 0`
(subcritical Hopf). -/
@[tmio TM]
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (m : Model) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | (m.params.V * Real.sin m.θ = -(m.params.Xg * m.params.Id) ∧
        m.params.D0 ≠ 0) ∧ 0 < (jac m.params m.θ).det ∧ ((jac m.params m.θ).trace < 0 ∨
          ((jac m.params m.θ).trace = 0 ∧ m.params.kp * m.params.ki < 0))}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  have hden : ∀ s, (∀ q ∈ translate s, Meets m q) → m ∈ family.den s := fun s h =>
    mem_den_of_meets h
  constructor
  · intro hLAS
    rw [family_isAutonomous.mem_den_flow] at hLAS
    change LocalAsymptoticStable m.field 0 at hLAS
    have hunst : Meets m .equilibrium → Meets m .jacobianUnstable → False := by
      intro he hu
      have h := hden (.flow .unstable) (by
        intro q hq
        simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · exact he
        · exact hu)
      rw [family_isAutonomous.mem_den_flow] at h
      exact h hLAS.1
    have hf0 : m.field 0 = 0 := by
      by_contra h
      exact Dynamics.unstable_of_ne_zero m.field_contDiff h hLAS.1
    have hD0 : m.params.D0 ≠ 0 := fun h => not_las_of_D0_eq_zero h hLAS
    have heq := balance_of_model_field_zero hf0
    have he : Meets m .equilibrium := ⟨heq, hD0⟩
    have hdet : 0 < (jac m.params m.θ).det := by
      rcases lt_trichotomy (jac m.params m.θ).det 0 with h | h | h
      · exact (hunst he (Or.inr h)).elim
      · exact (not_las_of_det_eq_zero heq hD0 h hLAS).elim
      · exact h
    refine ⟨he, hdet, ?_⟩
    rcases lt_trichotomy (jac m.params m.θ).trace 0 with htr | htr | htr
    · exact Or.inl htr
    · refine Or.inr ⟨htr, ?_⟩
      rcases lt_trichotomy (m.params.kp * m.params.ki) 0 with hk | hk | hk
      · exact hk
      · have hki : m.params.ki ≠ 0 := (model_ratio_pos hD0 hdet).2.1 ∘ fun h => by
          rw [h, zero_div]
        have hkp : m.params.kp = 0 := (mul_eq_zero.mp hk).resolve_right hki
        exact (not_las_of_hopf_kp_eq_zero heq hD0 htr hdet hkp hLAS).elim
      · exact ((unstable_of_hopf heq hD0 htr hdet hk) hLAS.1).elim
    · exact (hunst he (Or.inl htr)).elim
  · rintro ⟨he, hdet, htr | ⟨htr, hk⟩⟩
    · exact hden (.flow .locallyAsymptoticallyStable) (by
        intro q hq
        simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · exact he
        · exact ⟨htr, hdet⟩)
    · rw [family_isAutonomous.mem_den_flow]
      exact las_of_hopf he.1 he.2 htr hdet hk

/-! ### The local asymptotic translation is not exact -/

/-- A supercritical boundary PLL: `V = √2`, `X_g = ω_s = 1`, `k_p = −1/2`, `k_i = 1/2`,
`i_d = 1` (so `L_g i_d = 1`, `D₀ = 1/2`; the OUT-positive source point `I_d = −1`) at
`θ* = −π/4`. Balanced (`V sin θ* = −1 = −X_g i_d`), `tr J = 0`, `det J = 1`, `k_p k_i = −1/4`. -/
def supercriticalPLL : Model := ⟨⟨Real.sqrt 2, 1, 1, -1 / 2, 1 / 2, 1⟩, -(Real.pi / 4)⟩

private theorem supercriticalPLL_data :
    supercriticalPLL.params.V * Real.sin supercriticalPLL.θ =
        -(supercriticalPLL.params.Xg * supercriticalPLL.params.Id) ∧
      supercriticalPLL.params.D0 ≠ 0 ∧ (jac supercriticalPLL.params supercriticalPLL.θ).trace = 0 ∧
      0 < (jac supercriticalPLL.params supercriticalPLL.θ).det ∧
      supercriticalPLL.params.kp * supercriticalPLL.params.ki < 0 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hD0 : supercriticalPLL.params.D0 = 1 / 2 := by
    simp [supercriticalPLL, Params.D0, Params.Lg]; norm_num
  refine ⟨?_, by rw [hD0]; norm_num, ?_, ?_, by simp [supercriticalPLL]; norm_num⟩
  · simp only [supercriticalPLL, Real.sin_neg, Real.sin_pi_div_four]
    linear_combination (-1 / 2 : ℝ) * h2
  · rw [trace_jac, hD0]
    simp only [supercriticalPLL, Real.cos_neg, Real.cos_pi_div_four, Params.Lg]
    linear_combination (1 / 2 : ℝ) * h2
  · rw [det_jac _ (by rw [hD0]; norm_num), hD0]
    simp only [supercriticalPLL, Real.cos_neg, Real.cos_pi_div_four]
    nlinarith [h2]

/-- The supercritical boundary PLL is locally asymptotically stable. -/
@[tmio TM]
@[powerlib_domain] theorem supercriticalPLL_mem_den_locallyAsymptoticallyStable :
    connection% (supercriticalPLL ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨heq, hD0, htr, hdet, hk⟩ := supercriticalPLL_data
  exact mem_den_locallyAsymptoticallyStable_of_hopf supercriticalPLL heq hD0 htr hdet hk

/-- **The local asymptotic translation is not exact.** The supercritical boundary PLL is locally
asymptotically stable, but its Jacobian has trace `0`, so it meets no stable-Jacobian
requirement. -/
@[tmio TM]
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := supercriticalPLL_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : Meets supercriticalPLL .jacobianStable :=
    hmem .jacobianStable (by simp [family, translate])
  have := hs.1
  rw [supercriticalPLL_data.2.2.1] at this
  exact lt_irrefl 0 this


end powerlib.GFL.RatePLL
