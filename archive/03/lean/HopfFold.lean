/-
  F-H / F-fold — the parametrically-provable slices of the two GFL-VSC weak-grid boundaries.

  HONEST LAYERING (matches the problem statement):
  * F-H full (10×10 Hurwitz sign chart Σ_H, H1 Routh–Hurwitz, H3 crossing dRe λ/dg>0):
    needs the general Routh–Hurwitz criterion (ABSENT from Mathlib) + a CAS-scale 10×10 symbolic
    Hurwitz computation + eigenvalue perturbation.  NOT done.  The provable pieces are the
    *building blocks* — `stable_deg2_of_pos`, `hopf_deg2` — for the 2×2 current-loop / PLL sub-blocks.
  * F-fold full (F1/F2 existence/fold of limit cycles, Floquet): beyond current provers.  The problem
    identifies the provable sub-block = F3's algebraic part ("angle saddle + no equilibrium beyond the
    fold ⟹ unbounded drift"), which is `R2/Σ₂`-isomorphic — proved here on the single-harmonic angle
    map `G(θ) = A·sinθ + B·cosθ + D` (the PLL q-axis projection `v_cqc` on the sync manifold), reusing
    `GFL/SyncEquilibrium.lean`.  NEW here: the **saddle-node tangency** at the fold `D² = A²+B²`.

  Nothing numeric enters any statement (parametric requirement).  No `sorry`.
-/
import GFL.SyncEquilibrium

namespace GFL

open Real

-- the cofactor/`simp only` extractions below share lemma lists across `congrArg re/im` calls; the
-- unused-arg style linter conflicts with that and would fail the build (proofs are unaffected).
set_option linter.unusedSimpArgs false

/-! ### F-fold sub-block (F3, algebraic): the angle map `G(θ) = A·sinθ + B·cosθ + D`

`A,B` are the in-phase / quadrature voltage-projection amplitudes and `D` the bias (grid-impedance
drop vs source) of the PLL q-axis projection on the synchronisation manifold; equilibria are zeros
of `G`.  The angle-fold boundary is `Σ_fold,angle := {D² = A²+B²}`. -/

/-- **F-fold (angle) — saddle-node tangency at the fold `D² = A²+B²`.**
At the fold boundary (bias = amplitude, `D>0`) the equilibrium is *degenerate*: there is an angle
`θ*` with `G(θ*) = 0` **and** `G'(θ*) = A·cosθ* − B·sinθ* = 0` simultaneously — the two equilibria
(stable node + index-1 saddle) merge.  This is the algebraic saddle-node of the angle map (the
`∂(displacement)/∂(amplitude) = 0` condition of Σ_fold, restricted to the angle dynamics). -/
theorem angle_fold_tangency (A B D : ℝ) (hD : 0 < D) (hfold : D ^ 2 = A ^ 2 + B ^ 2) :
    ∃ θ : ℝ, A * sin θ + B * cos θ + D = 0 ∧ A * cos θ - B * sin θ = 0 := by
  set z : ℂ := ⟨B, A⟩ with hz_def
  set α := Complex.arg z with hα
  have hN2 : ‖z‖ ^ 2 = A ^ 2 + B ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hz_def, Complex.normSq_mk]; ring
  have hsinα : A = ‖z‖ * sin α := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have hA : A = 0 := by rw [show A = z.im from rfl, hz0]; rfl
      rw [hz0, norm_zero, zero_mul]; exact hA
    · rw [hα, Complex.sin_arg, show z.im = A from rfl]; field_simp
  have hcosα : B = ‖z‖ * cos α := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have hB : B = 0 := by rw [show B = z.re from rfl, hz0]; rfl
      rw [hz0, norm_zero, zero_mul]; exact hB
    · rw [hα, Complex.cos_arg hz0, show z.re = B from rfl]; field_simp
  have hND : ‖z‖ = D := by
    have h2 : ‖z‖ ^ 2 = D ^ 2 := by rw [hN2, ← hfold]
    have h1 : ‖z‖ = |D| := by rw [← Real.sqrt_sq (norm_nonneg z), h2, Real.sqrt_sq_eq_abs]
    rwa [abs_of_pos hD] at h1
  -- the minimum of `A·sinθ + B·cosθ` is attained at `α + π`, value `−‖z‖ = −D`, derivative `0`
  refine ⟨α + π, ?_, ?_⟩
  · rw [Real.sin_add_pi, Real.cos_add_pi]
    have hmax : A * sin α + B * cos α = D := by
      rw [hsinα, hcosα, ← hND]; linear_combination ‖z‖ * sin_sq_add_cos_sq α
    linear_combination -hmax
  · rw [Real.sin_add_pi, Real.cos_add_pi, hsinα, hcosα]; ring

/-- **F-fold (angle) — within the sync window an equilibrium exists.**  If `D² ≤ A²+B²` (bias ≤
amplitude) the angle map `G` has a zero: a synchronous equilibrium (the node, plus a saddle).
(Reuse of `sync_equilibrium_of_amp_ge`.)  Together with `angle_fold_tangency` and the drift result
below, `D² = A²+B²` is exactly the angle-fold boundary `Σ_fold,angle`. -/
theorem sync_window_equilibrium (A B D : ℝ) (hle : D ^ 2 ≤ A ^ 2 + B ^ 2) :
    ∃ θ : ℝ, A * sin θ + B * cos θ + D = 0 :=
  sync_equilibrium_of_amp_ge A B D hle

/-- **F3 — loss of synchronism beyond the fold.**  If the bias exceeds the amplitude
(`A²+B² < D²`, `D>0` — `p` beyond `Σ_fold,angle`), the angle map `G` has no zero, so along any
trajectory of the PLL integrator `η' = G(θ_e)` the state `η` (hence `θ_e`) drifts unboundedly: the
converter cannot synchronise.  This is the algebraic, model-agnostic core of F3 (it holds
independently of any local modal damping).  (Reuse of `sync_loss_of_bias_gt_amp`.) -/
theorem F3_drift_beyond_fold (A B D : ℝ) (hD : 0 < D) (hbeyond : A ^ 2 + B ^ 2 < D ^ 2)
    (η θe : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (A * sin (θe t) + B * cos (θe t) + D) t) :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < η t :=
  sync_loss_of_bias_gt_amp A B D hD hbeyond η θe hη

/-! ### F-H building blocks: stability and Hopf onset of a 2×2 sub-block `s² + a₁ s + a₂`

The current-loop and PLL blocks of `J(p)` are 2×2; their characteristic factors are real quadratics.
For these, Routh–Hurwitz is `a₁>0 ∧ a₂>0` (stability) and the Hopf-onset (pure-imaginary pair) is the
marginal `a₁ = 0` with frequency `ω = √a₂`.  Both are proved completely below.

The sympy Schur derivation (`derive_hopf.py`, parametric) gives the controller block factor
`det(Mkk) = λ²·(λ² + (Kp_pll·v_cdc)·λ + (Ki_pll·v_cdc))`, `v_cdc := cosθ_e*·v_cd − sinθ_e*·v_cq`.
Its PLL factor is exactly `s²+a₁s+a₂` with `a₁ = Kp_pll·v_cdc`, `a₂ = Ki_pll·v_cdc`, so `hopf_deg2` /
`stable_deg2_of_pos` give the PLL Hopf onset `v_cdc = 0` and stability `v_cdc > 0` directly. -/

/-- **Routh–Hurwitz, degree 2 (sufficiency).**  If `a₁>0` and `a₂>0` then every root of
`s² + a₁ s + a₂` has strictly negative real part (the 2×2 block is Hurwitz). -/
theorem stable_deg2_of_pos (a₁ a₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    (z : ℂ) (hz : z ^ 2 + (a₁ : ℂ) * z + (a₂ : ℂ) = 0) : z.re < 0 := by
  have hre : z.re ^ 2 - z.im ^ 2 + a₁ * z.re + a₂ = 0 := by
    have := congrArg Complex.re hz
    simpa [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] using this
  have him : z.im * (2 * z.re + a₁) = 0 := by
    have := congrArg Complex.im hz
    have h' : z.re * z.im + z.im * z.re + a₁ * z.im = 0 := by
      simpa [pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im] using this
    linear_combination h'
  by_contra hpos
  rw [not_lt] at hpos
  rcases mul_eq_zero.mp him with h | h
  · nlinarith [hre, h, sq_nonneg z.re, mul_nonneg hpos h₁.le]
  · linarith

/-- **Hopf onset, degree 2 (marginal).**  For `a₂>0`, the quadratic `s² + a₁ s + a₂` has a
pure-imaginary root iff `a₁ = 0`; the onset frequency is `ω = √a₂` (`(i√a₂)² + a₂ = 0`), with real
part `0`.  This is the 2×2 Hopf condition `Σ_H` (and pins the natural frequency). -/
theorem hopf_deg2 (a₁ a₂ : ℝ) (h₂ : 0 < a₂) :
    (∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 2 + (a₁ : ℂ) * ((ω : ℂ) * Complex.I) + (a₂ : ℂ) = 0)
      ↔ a₁ = 0 := by
  constructor
  · rintro ⟨ω, hω, hroot⟩
    have him : a₁ * ω = 0 := by
      have := congrArg Complex.im hroot
      simpa [pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] using this
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h (ne_of_gt hω)
  · intro ha
    refine ⟨Real.sqrt a₂, Real.sqrt_pos.mpr h₂, ?_⟩
    have hsq : (Real.sqrt a₂ : ℝ) ^ 2 = a₂ := Real.sq_sqrt h₂.le
    rw [ha]
    rw [Complex.ext_iff]
    constructor
    · push_cast
      simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [hsq]
    · simp [pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

/-! ### F-H deg-3 block (cubic factor `s³ + a₁s² + a₂s + a₃`)

For a 3×3 Schur block the characteristic factor is a real cubic.  Routh–Hurwitz here is
`a₁,a₂,a₃ > 0 ∧ a₁a₂ > a₃` (Hurwitz minor `Δ₂ = a₁a₂ − a₃ > 0`); the Hopf onset is the marginal
`a₁a₂ = a₃` with frequency `ω = √a₂`.  Both proved completely (parametric in the coefficients). -/

/-- **Routh–Hurwitz, degree 3 (sufficiency).**  If `a₁,a₂,a₃ > 0` and `a₁a₂ > a₃` then every root of
`s³ + a₁s² + a₂s + a₃` has strictly negative real part. -/
theorem stable_deg3_of_pos (a₁ a₂ a₃ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h₃ : 0 < a₃)
    (hRH : a₃ < a₁ * a₂) (z : ℂ)
    (hz : z ^ 3 + (a₁ : ℂ) * z ^ 2 + (a₂ : ℂ) * z + (a₃ : ℂ) = 0) : z.re < 0 := by
  have hre : z.re ^ 3 - 3 * z.re * z.im ^ 2 + a₁ * (z.re ^ 2 - z.im ^ 2) + a₂ * z.re + a₃ = 0 := by
    have h := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, one_mul, Complex.zero_re] at h
    linear_combination h
  have him : z.im * (3 * z.re ^ 2 - z.im ^ 2 + 2 * a₁ * z.re + a₂) = 0 := by
    have h := congrArg Complex.im hz
    simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      pow_succ, pow_zero, Complex.one_re, Complex.one_im, one_mul, Complex.zero_im] at h
    linear_combination h
  by_contra hpos
  rw [not_lt] at hpos
  rcases mul_eq_zero.mp him with hy0 | hcond
  · rw [hy0] at hre
    nlinarith [hre, hpos, h₁, h₂, h₃, mul_nonneg (mul_nonneg hpos hpos) hpos,
      mul_nonneg h₁.le (mul_nonneg hpos hpos), mul_nonneg h₂.le hpos]
  · have hy2 : z.im ^ 2 = 3 * z.re ^ 2 + 2 * a₁ * z.re + a₂ := by linarith [hcond]
    rw [hy2] at hre
    nlinarith [hre, hpos, h₁, h₂, hRH, mul_nonneg (mul_nonneg hpos hpos) hpos,
      mul_nonneg h₁.le (mul_nonneg hpos hpos), mul_nonneg h₂.le hpos,
      mul_nonneg (mul_nonneg h₁.le h₁.le) hpos]

/-- **Hopf onset, degree 3 (marginal).**  For `a₁,a₂ > 0`, the cubic `s³ + a₁s² + a₂s + a₃` has a
pure-imaginary root iff the Hurwitz minor vanishes, `a₃ = a₁a₂`; onset frequency `ω = √a₂`
(`χ(iω) = (a₃ − a₁ω²) + iω(a₂ − ω²)`). -/
theorem hopf_deg3 (a₁ a₂ a₃ : ℝ) (h₂ : 0 < a₂) :
    (∃ ω : ℝ, 0 < ω ∧ ((ω : ℂ) * Complex.I) ^ 3 + (a₁ : ℂ) * ((ω : ℂ) * Complex.I) ^ 2
        + (a₂ : ℂ) * ((ω : ℂ) * Complex.I) + (a₃ : ℂ) = 0) ↔ a₃ = a₁ * a₂ := by
  constructor
  · rintro ⟨ω, hω, hroot⟩
    have hre : a₃ - a₁ * ω ^ 2 = 0 := by
      have h := congrArg Complex.re hroot
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, Complex.one_re,
        Complex.one_im, one_mul, Complex.zero_re] at h
      linear_combination h
    have him : ω * (a₂ - ω ^ 2) = 0 := by
      have h := congrArg Complex.im hroot
      simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, Complex.one_re,
        Complex.one_im, one_mul, Complex.zero_im] at h
      linear_combination h
    have hω2 : ω ^ 2 = a₂ := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h (ne_of_gt hω)
      · linarith
    rw [hω2] at hre; linarith
  · intro hcrit
    refine ⟨Real.sqrt a₂, Real.sqrt_pos.mpr h₂, ?_⟩
    have hsq : ((Real.sqrt a₂ : ℝ) : ℂ) ^ 2 = (a₂ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt h₂.le]
    have e2 : ((Real.sqrt a₂ : ℂ) * Complex.I) ^ 2 = -(a₂ : ℂ) := by
      rw [mul_pow, Complex.I_sq, hsq]; ring
    have e3 : ((Real.sqrt a₂ : ℂ) * Complex.I) ^ 3
        = -(a₂ : ℂ) * ((Real.sqrt a₂ : ℂ) * Complex.I) := by rw [pow_succ, e2]
    have hc : (a₃ : ℂ) = (a₁ : ℂ) * (a₂ : ℂ) := by exact_mod_cast hcrit
    rw [e3, e2, hc]; ring

end GFL
