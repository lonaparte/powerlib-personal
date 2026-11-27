import theorem.Periodic.RobustThreshold

/-! # Robust Lyapunov thresholds against the universal threshold for stiffness modulation

For `m δ̈ + D δ̇ + K(t) δ = 0` with `|K(t) − K̄| ≤ εK̄` (state `(δ, δ̇)`, `k = K̄/m`, `d = D/m`,
`ξ = D/(2√(mK̄))`) three waveform-free stability thresholds are compared, each valid for every
pump period:
* the universal threshold of `theorem/ParametricResonance/UniversalThreshold.lean`,
  `ε/√(1 − ε) < 2ξ`, which reads `ε < thresholdCurve ξ` with
  `thresholdCurve x = 2x(√(1 + x²) − x)`;
* the robust threshold in the Lyapunov form of `Periodic.Robust.schurStable_of_lyapunov`
  (`β < q`: perturbation bounded by `β |x|²`, dissipation by `λ_min(Q) |x|²`) with the energy-like
  certificate `P = [[k + dγ, γ], [γ, 1]]`, `Q = diag(2kγ, 2(d − γ))`, `0 < γ < d`: here
  `q = 2 min(kγ, d − γ)`, `β = εk(γ + √(1 + γ²))`, and the best `γ = D/(m + K̄)` gives exactly
  `ε < thresholdCurve (D/(m + K̄))`;
* the exact quadratic threshold, the best any common quadratic Lyapunov function for the stiffness
  interval `[K̄(1 − ε), K̄(1 + ε)]` can certify: `2ε/(√(1 + ε) + √(1 − ε)) < 2ξ`, reached by the
  energy-like matrix with the cross term `γ = d/2` and a shift `σ` of its `δ²` coefficient.
Results of the comparison, in every parameter region (in particular for `m + 2D > 4K̄`, left open
by `Periodic.Robust.secondOrder_robust_le_universal`):
* robust (Lyapunov form, energy-like `P`) `⇒` universal. Both thresholds are the same curve at
  two effective damping ratios, `D/(m + K̄)` (arithmetic mean of `m, K̄`) and `D/(2√(mK̄))`
  (geometric mean), so the universal threshold is at least as large, with equality exactly when
  `K̄ = m` (the time unit `ω₀ = 1`, in which the Euclidean norm of `(δ, δ̇)` is the energy norm).
  The switching curve degenerates to this contact set: the robust Lyapunov form is never sharper.
* universal `⇒` quadratic, strictly: for every `ε ∈ (0, 1)`,
  `2ε/(√(1 + ε) + √(1 − ε)) < ε/√(1 − ε)`, so the quadratic certificate covers strictly deeper
  modulations at every damping ratio (the two agree to first order, `ε ≈ 2ξ`).
The order of the three is fixed by how the certificate treats the perturbation: the `β < q` form
bounds the stiffness term by its spectral norm and the dissipation by `λ_min(Q)` separately and
loses the sign structure; the matrix-inequality form keeps it. The robust thresholds cover more
than stiffness modulation (any perturbation matrix in the `β < q` form, any dimension); the
comparison concerns stiffness modulation only.

Not decided here: the exponential-bound form `K_c εK̄/m < α` of
`Periodic.Robust.secondOrder_robust_le_universal` (sup norm, `‖e^{τA₀}‖ ≤ K_c e^{−ατ}`) for
`m + 2D > 4K̄`; its best constant `K_c(α)` (the transient growth of `e^{τA₀}` in the sup norm) has
no closed form, and only `K_c ≥ 1`, `2α ≤ d` are used there.

Scope.
* The scalar real equation `m δ̈ + D δ̇ + K(t) δ = 0` in the state `(δ, δ̇)` with the state matrix
  `Periodic.oscMatrix (D/(2m)) (K(t)/m)` of `theorem/Periodic/TwoStateBoundary.lean`, constants
  `m > 0`, `K̄ > 0`, `0 ≤ ε < 1`, continuous `T`-periodic `K` (`T > 0`) for the Floquet
  statements; Schur stability of the monodromy matrix as in
  `Periodic.Robust.schurStable_of_lyapunov` and
  `ParametricResonance.UniversalThreshold.schurStable_of_threshold`.
* Quadratic forms `x ⬝ᵥ P x` on `Fin 2 → ℝ`, `|x|² = x ⬝ᵥ x`; a common quadratic Lyapunov function
  is a symmetric `P ≻ 0` with `xᵀ (Aᵀ P + P A) x < 0` for `x ≠ 0` at both extreme stiffnesses.
* Generic mathematics; no model family.

Source: Khalil, *Nonlinear Systems*, 3rd ed., §9.1 (Lyapunov robustness of exponential stability
under vanishing perturbations) and §4.6 (quadratic Lyapunov functions); the energy Lyapunov
function of the damped oscillator with a cross term (Khalil, Ch. 4, the pendulum examples); the
quadratic stability of interval systems (common quadratic Lyapunov functions for a polytope of
matrices, Boyd–El Ghaoui–Feron–Balakrishnan, *Linear Matrix Inequalities in System and Control
Theory*, 1994, §5.1); the robust threshold `Periodic.Robust.schurStable_of_lyapunov` and the
universal threshold `ParametricResonance.UniversalThreshold.schurStable_of_threshold`.

Results.
* `energyP`, `energyQ`, `energyS`, `lyapunov_oscMatrix`, `perturbation_energy` — the energy-like
  certificate: `A_{k'}ᵀ P + P A_{k'} = −Q + (k' − k) S`; `det_div_trace_le`,
  `dotProduct_mulVec_fin_two`, `energyP_bounds`, `abs_energyS_le` — the quadratic-form bounds.
* `energy_robust_schurStable` — the explicit robust threshold `εk(γ + √(1 + γ²)) < 2 min(kγ, d − γ)`
  gives Schur stability for every period and waveform.
* `thresholdCurve`, `lt_thresholdCurve_iff`, `thresholdCurve_lt` — the common threshold curve.
* `energy_robust_universal` — the robust condition implies `ε < 1` and the universal condition.
* `exists_energy_robust_iff` — some `γ` satisfies the robust condition iff
  `ε < thresholdCurve (D/(m + K̄))`.
* `energy_threshold_le_universal` — `thresholdCurve (D/(m + K̄)) ≤ thresholdCurve ξ`, with
  equality iff `K̄ = m`, and the universal condition is `ε < thresholdCurve ξ`.
* `quadratic_schurStable` — `2ε√(mK̄) < D(√(1 + ε) + √(1 − ε))` gives Schur stability for every
  period and waveform; `quadratic_threshold_converse` — no common quadratic Lyapunov function
  exists beyond it.
* `universal_lt_quadratic` — the universal condition implies the quadratic one, strictly.
-/

noncomputable section
namespace powerlib.ParametricResonance.RobustVsUniversal

open Set Function Matrix
open powerlib.Periodic

/-! ## The energy-like Lyapunov matrices of the oscillator -/

/-- The energy-like Lyapunov matrix `[[k + 2cγ + σ, γ], [γ, 1]]` of `oscMatrix c k` (state
`(δ, δ̇)`): `V = (k + 2cγ + σ) δ² + 2γ δ δ̇ + δ̇²`; `σ = 0` is twice the energy plus the cross term
`2γ δ δ̇`. -/
def energyP (c k γ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![k + 2 * c * γ + σ, γ; γ, 1]

/-- Its dissipation matrix `[[2kγ, −σ], [−σ, 2(2c − γ)]]`. -/
def energyQ (c k γ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2 * k * γ, -σ; -σ, 2 * (2 * c - γ)]

/-- The direction `[[−2γ, −1], [−1, 0]]` in which a stiffness change moves the Lie derivative. -/
def energyS (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2 * γ, -1; -1, 0]

/-- **Lie derivative of the energy-like form.** For every stiffness `k'`,
`(oscMatrix c k')ᵀ P + P (oscMatrix c k') = −Q + (k' − k) S` with `P = energyP c k γ σ`,
`Q = energyQ c k γ σ`, `S = energyS γ`: along `δ̈ + 2c δ̇ + k' δ = 0`,
`V̇ = −xᵀ Q x + (k' − k) xᵀ S x`. -/
@[tmio T, powerlib_foundation] theorem lyapunov_oscMatrix (c k k' γ σ : ℝ) :
    (oscMatrix c k')ᵀ * energyP c k γ σ + energyP c k γ σ * oscMatrix c k' =
      -energyQ c k γ σ + (k' - k) • energyS γ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oscMatrix, energyP, energyQ, energyS, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Determinant-over-trace bound.** For `p + e > 0`,
`((pe − r²)/(p + e)) (x₀² + x₁²) ≤ p x₀² + 2r x₀x₁ + e x₁²`: `(p + e) xᵀMx − det M |x|²` is
`(p x₀ + r x₁)² + (r x₀ + e x₁)²`. -/
@[tmio T, powerlib_foundation] theorem det_div_trace_le {p r e : ℝ} (hpe : 0 < p + e)
    (x₀ x₁ : ℝ) :
    (p * e - r ^ 2) / (p + e) * (x₀ ^ 2 + x₁ ^ 2) ≤ p * x₀ ^ 2 + 2 * r * x₀ * x₁ + e * x₁ ^ 2 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hpe]
  nlinarith [sq_nonneg (p * x₀ + r * x₁), sq_nonneg (r * x₀ + e * x₁)]

/-- The quadratic form of a symmetric `2 × 2` matrix. -/
@[tmio T, powerlib_foundation] theorem dotProduct_mulVec_fin_two (M : Matrix (Fin 2) (Fin 2) ℝ)
    (x : Fin 2 → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = M 0 0 * x 0 ^ 2 + (M 0 1 + M 1 0) * x 0 * x 1 + M 1 1 * x 1 ^ 2 := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- **Bounds of the energy-like form.** With `a = k + 2cγ + σ > γ²`,
`((a − γ²)/(a + 1)) |x|² ≤ xᵀ P x ≤ (a + 1) |x|²`. -/
@[tmio T, powerlib_foundation] theorem energyP_bounds {c k γ σ : ℝ}
    (ha : γ ^ 2 < k + 2 * c * γ + σ) (x : Fin 2 → ℝ) :
    (k + 2 * c * γ + σ - γ ^ 2) / (k + 2 * c * γ + σ + 1) * (x ⬝ᵥ x) ≤
        x ⬝ᵥ (energyP c k γ σ *ᵥ x) ∧
      x ⬝ᵥ (energyP c k γ σ *ᵥ x) ≤ (k + 2 * c * γ + σ + 1) * (x ⬝ᵥ x) := by
  have hxx : x ⬝ᵥ x = x 0 ^ 2 + x 1 ^ 2 := by simp [dotProduct, Fin.sum_univ_two, sq]
  rw [dotProduct_mulVec_fin_two, hxx]
  simp only [energyP, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  have hpos : 0 < k + 2 * c * γ + σ + 1 := by nlinarith [sq_nonneg γ]
  constructor
  · have h := det_div_trace_le (p := k + 2 * c * γ + σ) (r := γ) (e := 1) hpos (x 0) (x 1)
    rw [mul_one] at h
    linarith
  · nlinarith [sq_nonneg (x 0 - γ * x 1), sq_nonneg (x 1)]

/-- `|−2γ x₀² − 2 x₀ x₁| ≤ (γ + √(1 + γ²)) |x|²` for `γ ≥ 0`: the extreme eigenvalues of
`energyS γ` are `−γ ± √(1 + γ²)`. -/
@[tmio T, powerlib_foundation] theorem abs_energyS_le {γ : ℝ} (hγ : 0 ≤ γ) (x : Fin 2 → ℝ) :
    |x ⬝ᵥ (energyS γ *ᵥ x)| ≤ (γ + √(1 + γ ^ 2)) * (x ⬝ᵥ x) := by
  have hxx : x ⬝ᵥ x = x 0 ^ 2 + x 1 ^ 2 := by simp [dotProduct, Fin.sum_univ_two, sq]
  rw [dotProduct_mulVec_fin_two, hxx]
  simp only [energyS, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  set s := √(1 + γ ^ 2) with hs
  have hs2 : s ^ 2 = 1 + γ ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsγ : 0 < γ + s := by nlinarith
  rw [abs_le]
  constructor
  · -- `(γ + s)(x₀² + x₁²) + w = ((x₀ − (s + γ) x₁)²) / (s + γ)`
    have h : 0 ≤ (γ + s) * ((γ + s) * (x 0 ^ 2 + x 1 ^ 2) +
        (-2 * γ * x 0 ^ 2 + (-1 + -1) * x 0 * x 1 + 0 * x 1 ^ 2)) := by
      nlinarith [sq_nonneg (x 0 - (s + γ) * x 1)]
    have := (mul_nonneg_iff_of_pos_left hsγ).mp h
    linarith
  · have h : 0 ≤ (γ + s) * ((γ + s) * (x 0 ^ 2 + x 1 ^ 2) -
        (-2 * γ * x 0 ^ 2 + (-1 + -1) * x 0 * x 1 + 0 * x 1 ^ 2)) := by
      nlinarith [sq_nonneg ((γ + s) * x 1 + x 0), sq_nonneg (x 0), mul_nonneg hγ hs0,
        mul_nonneg hγ hγ]
    have := (mul_nonneg_iff_of_pos_left hsγ).mp h
    linarith

/-- A stiffness change `k → k'` perturbs the Lie derivative by `(k' − k) S`:
`P B + Bᵀ P = (k' − k) S` for `B = oscMatrix c k' − oscMatrix c k`. -/
@[tmio T, powerlib_foundation] theorem perturbation_energy (c k k' γ σ : ℝ) :
    energyP c k γ σ * (oscMatrix c k' - oscMatrix c k) +
        (oscMatrix c k' - oscMatrix c k)ᵀ * energyP c k γ σ = (k' - k) • energyS γ := by
  have h1 := lyapunov_oscMatrix c k k' γ σ
  have h0 := lyapunov_oscMatrix c k k γ σ
  rw [sub_self, zero_smul, add_zero] at h0
  rw [Matrix.mul_sub, transpose_sub, Matrix.sub_mul]
  have e : energyP c k γ σ * oscMatrix c k' - energyP c k γ σ * oscMatrix c k +
      ((oscMatrix c k')ᵀ * energyP c k γ σ - (oscMatrix c k)ᵀ * energyP c k γ σ) =
      ((oscMatrix c k')ᵀ * energyP c k γ σ + energyP c k γ σ * oscMatrix c k') -
        ((oscMatrix c k)ᵀ * energyP c k γ σ + energyP c k γ σ * oscMatrix c k) := by abel
  rw [e, h1, h0]
  abel

/-! ## The robust threshold of the energy-like certificate -/

section Energy

variable {m D Kbar ε T : ℝ} {K : ℝ → ℝ}

/-- **The robust (Lyapunov-form) threshold of the energy-like certificate.** For
`m δ̈ + D δ̇ + K(t) δ = 0` (state `(δ, δ̇)`, `k = K̄/m`, `d = D/m`), the matrices
`P = energyP (d/2) k γ 0`, `Q = energyQ (d/2) k γ 0` (`0 < γ < d`) solve
`A₀ᵀ P + P A₀ = −Q` with `q = λ_min(Q) = 2 min(kγ, d − γ)`, and a stiffness deviation
`|K − K̄| ≤ εK̄` gives `xᵀ (P B + Bᵀ P) x ≤ β |x|²` with `β = εk (γ + √(1 + γ²))`. The robust
condition `β < q` of `Periodic.Robust.schurStable_of_lyapunov` therefore certifies a Schur-stable
monodromy for every period and every continuous periodic waveform. -/
@[tmio T, powerlib_foundation] theorem energy_robust_schurStable (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < D / m)
    (hrob : ε * (Kbar / m) * (γ + √(1 + γ ^ 2)) < 2 * min (Kbar / m * γ) (D / m - γ))
    (hT : 0 < T) (hK : Continuous K) (hKP : Periodic K T) (hdev : ∀ t, |K t - Kbar| ≤ ε * Kbar) :
    LTI.SchurStable (monodromy (fun t => oscMatrix (D / (2 * m)) (K t / m)) T 0) := by
  set c := D / (2 * m) with hc
  set k := Kbar / m with hk
  have h2c : 2 * c = D / m := by rw [hc]; field_simp
  have hk0 : 0 < k := div_pos hKbar hm
  set A₀ := oscMatrix c k with hA₀
  set P := energyP c k γ 0 with hP
  set Q := energyQ c k γ 0 with hQ
  have hPs : Pᵀ = P := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hP, energyP]
  have hlyap : A₀ᵀ * P + P * A₀ = -Q := by
    rw [hA₀, hP, hQ, lyapunov_oscMatrix, sub_self, zero_smul, add_zero]
  have ha : γ ^ 2 < k + 2 * c * γ + 0 := by rw [h2c]; nlinarith [mul_lt_mul_of_pos_left hγd hγ]
  have hP₁ := fun x => (energyP_bounds ha x).1
  have hP₂ := fun x => (energyP_bounds ha x).2
  have hp₁ : 0 < (k + 2 * c * γ + 0 - γ ^ 2) / (k + 2 * c * γ + 0 + 1) := by
    apply div_pos <;> nlinarith [sq_nonneg γ]
  have hp₂ : 0 < k + 2 * c * γ + 0 + 1 := by nlinarith [sq_nonneg γ]
  set q := 2 * min (k * γ) (D / m - γ) with hq
  have hQb : ∀ x, q * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x) := by
    intro x
    have hxx : x ⬝ᵥ x = x 0 ^ 2 + x 1 ^ 2 := by simp [dotProduct, Fin.sum_univ_two, sq]
    rw [dotProduct_mulVec_fin_two, hxx]
    simp only [hQ, energyQ, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, neg_zero, add_zero, zero_mul]
    have h1 : min (k * γ) (D / m - γ) ≤ k * γ := min_le_left _ _
    have h2 : min (k * γ) (D / m - γ) ≤ D / m - γ := min_le_right _ _
    rw [h2c] at *
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  set β := ε * k * (γ + √(1 + γ ^ 2)) with hβ
  have hBc : Continuous fun t => oscMatrix c (K t / m) - A₀ := by
    refine Continuous.sub ?_ continuous_const
    simp only [oscMatrix]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hβb : ∀ t x, x ⬝ᵥ ((P * (oscMatrix c (K t / m) - A₀) +
      (oscMatrix c (K t / m) - A₀)ᵀ * P) *ᵥ x) ≤ β * (x ⬝ᵥ x) := by
    intro t x
    rw [hP, hA₀, perturbation_energy, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hκ : |K t / m - k| ≤ ε * k := by
      rw [hk, ← sub_div, abs_div, abs_of_pos hm, mul_div_assoc']
      exact div_le_div_of_nonneg_right (hdev t) hm.le
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    calc (K t / m - k) * (x ⬝ᵥ (energyS γ *ᵥ x)) ≤ |K t / m - k| * |x ⬝ᵥ (energyS γ *ᵥ x)| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ (ε * k) * ((γ + √(1 + γ ^ 2)) * (x ⬝ᵥ x)) :=
          mul_le_mul hκ (abs_energyS_le hγ.le x) (abs_nonneg _) (by positivity)
      _ = β * (x ⬝ᵥ x) := by rw [hβ]; ring
  have h := (Periodic.Robust.schurStable_of_lyapunov hPs hlyap hp₁ hp₂ hP₁ hP₂ hQb hrob hT hBc
    (fun t => by simp only [hKP t]) hβb).1
  simpa only [hA₀, add_sub_cancel] using h

end Energy

/-! ## The robust threshold against the universal one -/

/-- The threshold curve `x ↦ 2x (√(1 + x²) − x) = 2x / (x + √(1 + x²))`, increasing from `0` to `1`:
the universal threshold is `ε < thresholdCurve ξ` (`ξ = D/(2√(mK̄))`), the robust threshold of the
energy-like certificate `ε < thresholdCurve (D/(m + K̄))`. -/
def thresholdCurve (x : ℝ) : ℝ := 2 * x * (√(1 + x ^ 2) - x)

@[tmio T, powerlib_foundation] private theorem sqrt_one_add_sq (x : ℝ) :
    √(1 + x ^ 2) ^ 2 = 1 + x ^ 2 ∧ 0 ≤ √(1 + x ^ 2) ∧ x < √(1 + x ^ 2) := by
  refine ⟨Real.sq_sqrt (by positivity), Real.sqrt_nonneg _, ?_⟩
  rcases lt_or_ge x 0 with hx | hx
  · exact hx.trans_le (Real.sqrt_nonneg _)
  · calc x = √(x ^ 2) := (Real.sqrt_sq hx).symm
      _ < √(1 + x ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

/-- `ε (x + √(1 + x²)) < 2x ↔ ε < thresholdCurve x`, since `(√(1 + x²) − x)(√(1 + x²) + x) = 1`. -/
@[tmio T, powerlib_foundation] theorem lt_thresholdCurve_iff {ε x : ℝ} :
    ε * (x + √(1 + x ^ 2)) < 2 * x ↔ ε < thresholdCurve x := by
  obtain ⟨hs2, hs0, hxs⟩ := sqrt_one_add_sq x
  set s := √(1 + x ^ 2)
  have hsx : 0 < s - x := by linarith
  have hsx' : 0 < x + s := by nlinarith
  have hprod : (s - x) * (x + s) = 1 := by nlinarith
  unfold thresholdCurve
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h hsx
    nlinarith
  · intro h
    have := mul_lt_mul_of_pos_right h hsx'
    nlinarith

/-- The threshold curve is strictly increasing on `[0, ∞)`. -/
@[tmio T, powerlib_foundation] theorem thresholdCurve_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    thresholdCurve x < thresholdCurve y := by
  obtain ⟨hs2, hs0, hxs⟩ := sqrt_one_add_sq x
  obtain ⟨ht2, ht0, hyt⟩ := sqrt_one_add_sq y
  set s := √(1 + x ^ 2)
  set u := √(1 + y ^ 2)
  have hy : 0 < y := hx.trans_lt hxy
  -- `x u < y s`
  have hxu : x * u < y * s := by
    have h1 : 0 ≤ x * u := mul_nonneg hx ht0
    have h2 : 0 ≤ y * s := mul_nonneg hy.le hs0
    refine (pow_lt_pow_iff_left₀ h1 h2 two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, hs2, ht2]
    nlinarith [mul_lt_mul_of_pos_left hxy hy, mul_le_mul_of_nonneg_left hxy.le hx]
  -- `thresholdCurve x = 2x/(x + s)`
  have hxs' : 0 < x + s := by nlinarith
  have hyu' : 0 < y + u := by nlinarith
  have ex : thresholdCurve x = 2 * x / (x + s) := by
    unfold thresholdCurve; field_simp; nlinarith
  have ey : thresholdCurve y = 2 * y / (y + u) := by
    unfold thresholdCurve; field_simp; nlinarith
  rw [ex, ey, div_lt_div_iff₀ hxs' hyu']
  nlinarith

variable {m D Kbar ε : ℝ}

/-- **The robust certificate never beats the universal threshold.** For every `γ ∈ (0, D/m)`, the
robust condition `εk(γ + √(1 + γ²)) < 2 min(kγ, d − γ)` of `energy_robust_schurStable`
(`k = K̄/m`, `d = D/m`) implies `ε < 1` and the universal condition `ε/√(1 − ε) < D/√(mK̄)` of
`ParametricResonance.UniversalThreshold.schurStable_of_threshold` — in every parameter region, in
particular for `m + 2D > 4K̄`, the case left open by
`Periodic.Robust.secondOrder_robust_le_universal`. Proof: `ε < 2γ(s − γ)`,
`s = √(1 + γ²)`, gives `(1 − ε)(γ + s)² > 1`; the two robust inequalities multiply to
`ε²k(γ + s)² < 4γ(d − γ) ≤ d²`; hence `ε²k < d²(1 − ε)`. -/
@[tmio T, powerlib_foundation] theorem energy_robust_universal (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < D / m)
    (hrob : ε * (Kbar / m) * (γ + √(1 + γ ^ 2)) < 2 * min (Kbar / m * γ) (D / m - γ)) :
    ε < 1 ∧ ε / √(1 - ε) < D / √(m * Kbar) := by
  set k := Kbar / m with hk
  set d := D / m with hd
  have hk0 : 0 < k := div_pos hKbar hm
  obtain ⟨hs2, hs0, hγs⟩ := sqrt_one_add_sq γ
  set s := √(1 + γ ^ 2)
  have h1 : ε * k * (γ + s) < 2 * (k * γ) := hrob.trans_le
    (mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le_two)
  have h2 : ε * k * (γ + s) < 2 * (d - γ) := hrob.trans_le
    (mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le_two)
  have h1' : ε * (γ + s) < 2 * γ := by
    have : k * (ε * (γ + s)) < k * (2 * γ) := by linarith
    exact lt_of_mul_lt_mul_left this hk0.le
  have hsγ : 0 < s - γ := by linarith
  have hprod : (s - γ) * (γ + s) = 1 := by nlinarith
  -- `1 − ε > (s − γ)²`
  have key1 : (s - γ) ^ 2 < 1 - ε := by
    have := mul_lt_mul_of_pos_right h1' hsγ
    nlinarith
  have hε1 : ε < 1 := by nlinarith [sq_nonneg (s - γ)]
  -- `(1 − ε)(γ + s)² > 1`
  have key2 : 1 < (1 - ε) * (γ + s) ^ 2 := by
    have hpos : 0 < (γ + s) ^ 2 := by positivity
    have := mul_lt_mul_of_pos_right key1 hpos
    calc (1 : ℝ) = ((s - γ) * (γ + s)) ^ 2 := by rw [hprod]; norm_num
      _ = (s - γ) ^ 2 * (γ + s) ^ 2 := by ring
      _ < _ := this
  -- the product of the two robust inequalities
  have hβ0 : 0 ≤ ε * k * (γ + s) := by positivity
  have key3 : (ε * k * (γ + s)) ^ 2 < 2 * (k * γ) * (2 * (d - γ)) := by
    rw [sq]; exact mul_lt_mul'' h1 h2 hβ0 hβ0
  have key4 : ε ^ 2 * k * (γ + s) ^ 2 < 4 * γ * (d - γ) := by
    have : k * (ε ^ 2 * k * (γ + s) ^ 2) < k * (4 * γ * (d - γ)) := by nlinarith
    exact lt_of_mul_lt_mul_left this hk0.le
  have hmain : ε ^ 2 * k < d ^ 2 * (1 - ε) := by
    have hA : ε ^ 2 * k ≤ ε ^ 2 * k * ((1 - ε) * (γ + s) ^ 2) :=
      le_mul_of_one_le_right (by positivity) key2.le
    have hB : ε ^ 2 * k * (γ + s) ^ 2 * (1 - ε) < 4 * γ * (d - γ) * (1 - ε) :=
      mul_lt_mul_of_pos_right key4 (by linarith)
    have hC : 4 * γ * (d - γ) ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 2 * γ)]
    nlinarith
  refine ⟨hε1, ?_⟩
  have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
  have hs3 : 0 < √(m * Kbar) := Real.sqrt_pos.mpr (by positivity)
  have hD : 0 < D := by
    have : 0 < d := hγ.trans hγd
    rw [hd] at this
    exact (div_pos_iff_of_pos_right hm).mp this
  rw [div_lt_div_iff₀ hs1 hs3]
  have hl : 0 ≤ ε * √(m * Kbar) := by positivity
  have hr : 0 ≤ D * √(1 - ε) := by positivity
  refine (pow_lt_pow_iff_left₀ hl hr two_ne_zero).mp ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)]
  have e1 : ε ^ 2 * k = ε ^ 2 * (m * Kbar) / m ^ 2 := by rw [hk]; field_simp
  have e2 : d ^ 2 * (1 - ε) = D ^ 2 * (1 - ε) / m ^ 2 := by rw [hd]; field_simp
  rw [e1, e2] at hmain
  exact (div_lt_div_iff_of_pos_right (by positivity)).mp hmain

@[tmio T, powerlib_foundation] private theorem thresholdCurve_pos {x : ℝ} (hx : 0 < x) :
    0 < thresholdCurve x := by
  have h := thresholdCurve_lt le_rfl hx
  simpa [thresholdCurve] using h

/-- **The best energy-like robust threshold.** Over all `γ ∈ (0, D/m)`, the robust condition of
`energy_robust_schurStable` holds for some `γ` exactly when `ε < thresholdCurve (D/(m + K̄))`: the
optimum is `γ* = D/(m + K̄)`, where `kγ* = d − γ*` balances the two entries of `λ_min(Q)`
(`2γ/(γ + √(1 + γ²))` increases, `2(d − γ)/(k(γ + √(1 + γ²)))` decreases in `γ`). -/
@[tmio T, powerlib_foundation] theorem exists_energy_robust_iff (hm : 0 < m) (hKbar : 0 < Kbar)
    (hD : 0 < D) :
    (∃ γ, 0 < γ ∧ γ < D / m ∧
      ε * (Kbar / m) * (γ + √(1 + γ ^ 2)) < 2 * min (Kbar / m * γ) (D / m - γ)) ↔
      ε < thresholdCurve (D / (m + Kbar)) := by
  set k := Kbar / m with hk
  set d := D / m with hd
  have hk0 : 0 < k := div_pos hKbar hm
  have hd0 : 0 < d := div_pos hD hm
  set g := D / (m + Kbar) with hg
  have hg' : g = d / (1 + k) := by rw [hg, hd, hk]; field_simp
  have hg0 : 0 < g := by rw [hg']; positivity
  have hkg : k * g = d - g := by rw [hg']; field_simp; ring
  have hgd : g < d := by nlinarith
  constructor
  · rintro ⟨γ, hγ, hγd, hrob⟩
    obtain ⟨hs2, hs0, hγs⟩ := sqrt_one_add_sq γ
    by_cases hc : k * γ ≤ d - γ
    · rw [min_eq_left hc] at hrob
      have h1 : ε * (γ + √(1 + γ ^ 2)) < 2 * γ := by
        have : k * (ε * (γ + √(1 + γ ^ 2))) < k * (2 * γ) := by linarith
        exact lt_of_mul_lt_mul_left this hk0.le
      have hγg : γ ≤ g := by
        rw [hg', le_div_iff₀ (by positivity)]; linarith
      refine (lt_thresholdCurve_iff.mp h1).trans_le ?_
      rcases hγg.eq_or_lt with h | h
      · rw [h]
      · exact (thresholdCurve_lt hγ.le h).le
    · push Not at hc
      rw [min_eq_right hc.le] at hrob
      rcases lt_or_ge ε 0 with hε | hε
      · exact hε.trans (thresholdCurve_pos hg0)
      refine lt_thresholdCurve_iff.mp ?_
      have hgγ : g < γ := by
        by_contra hcon
        push Not at hcon
        have : k * γ ≤ k * g := mul_le_mul_of_nonneg_left hcon hk0.le
        linarith
      have hss : √(1 + g ^ 2) ≤ √(1 + γ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      have h3 : ε * k * (g + √(1 + g ^ 2)) ≤ ε * k * (γ + √(1 + γ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h4 : ε * k * (g + √(1 + g ^ 2)) < k * (2 * g) := by linarith
      have : k * (ε * (g + √(1 + g ^ 2))) < k * (2 * g) := by linarith
      exact lt_of_mul_lt_mul_left this hk0.le
  · intro h
    refine ⟨g, hg0, hgd, ?_⟩
    rw [show d - g = k * g by rw [hkg], min_self]
    have h1 := lt_thresholdCurve_iff.mpr h
    nlinarith

/-- **Universal against robust: the same curve at two effective damping ratios.** With
`ξ = D/(2√(mK̄))` (the universal damping ratio, the geometric mean `√(mK̄)`) and
`D/(m + K̄)` (the arithmetic mean): for `0 ≤ ε < 1` the universal condition
`ε/√(1 − ε) < D/√(mK̄)` is `ε < thresholdCurve ξ`; the best robust threshold of the energy-like
certificate (`exists_energy_robust_iff`) is `thresholdCurve (D/(m + K̄))`; and since
`2√(mK̄) ≤ m + K̄`, the universal threshold is at least as large, with equality exactly when
`K̄ = m` (in the time unit `ω₀ = √(K̄/m) = 1`, where the Euclidean norm of `(δ, δ̇)` is the energy
norm). There is no region where the robust certificate is sharper: the switching curve
degenerates to the contact set `K̄ = m`. -/
@[tmio T, powerlib_foundation] theorem energy_threshold_le_universal (hm : 0 < m)
    (hKbar : 0 < Kbar) (hD : 0 < D) :
    thresholdCurve (D / (m + Kbar)) ≤ thresholdCurve (D / (2 * √(m * Kbar))) ∧
      (thresholdCurve (D / (m + Kbar)) = thresholdCurve (D / (2 * √(m * Kbar))) ↔ Kbar = m) ∧
      ∀ ε, 0 ≤ ε → ε < 1 →
        (ε / √(1 - ε) < D / √(m * Kbar) ↔ ε < thresholdCurve (D / (2 * √(m * Kbar)))) := by
  have hsm : √(m * Kbar) = √m * √Kbar := Real.sqrt_mul hm.le _
  have hm2 : √m ^ 2 = m := Real.sq_sqrt hm.le
  have hK2 : √Kbar ^ 2 = Kbar := Real.sq_sqrt hKbar.le
  have hsmp : 0 < √(m * Kbar) := Real.sqrt_pos.mpr (by positivity)
  have hamgm : 2 * √(m * Kbar) ≤ m + Kbar := by
    rw [hsm]; nlinarith [sq_nonneg (√m - √Kbar)]
  have hle : D / (m + Kbar) ≤ D / (2 * √(m * Kbar)) :=
    div_le_div_of_nonneg_left hD.le (by positivity) hamgm
  have hstrict : Kbar ≠ m → D / (m + Kbar) < D / (2 * √(m * Kbar)) := by
    intro hne
    refine div_lt_div_of_pos_left hD (by positivity) (lt_of_le_of_ne hamgm fun h => hne ?_)
    have hs : √m = √Kbar := by
      rw [hsm] at h
      nlinarith [sq_nonneg (√m - √Kbar), Real.sqrt_nonneg m, Real.sqrt_nonneg Kbar]
    rw [← hm2, ← hK2, hs]
  have hg0 : 0 ≤ D / (m + Kbar) := by positivity
  refine ⟨?_, ⟨fun heq => ?_, fun h => ?_⟩, ?_⟩
  · rcases hle.eq_or_lt with h | h
    · rw [h]
    · exact (thresholdCurve_lt hg0 h).le
  · by_contra hne
    exact (thresholdCurve_lt hg0 (hstrict hne)).ne heq
  · rw [h, show m * m = m ^ 2 by ring, Real.sqrt_sq hm.le]; ring_nf
  · intro ε hε hε1
    set x := D / (2 * √(m * Kbar)) with hx
    have hx0 : 0 < x := by positivity
    have h2x : D / √(m * Kbar) = 2 * x := by rw [hx]; field_simp
    obtain ⟨hs2, hs0, hxs⟩ := sqrt_one_add_sq x
    set s := √(1 + x ^ 2)
    have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
    rw [h2x, div_lt_iff₀ hs1]
    have hl : 0 ≤ ε := hε
    have hr : 0 ≤ 2 * x * √(1 - ε) := by positivity
    rw [← pow_lt_pow_iff_left₀ hl hr two_ne_zero, mul_pow, Real.sq_sqrt (by linarith)]
    unfold thresholdCurve
    -- `ε² < 4x²(1 − ε)` iff `ε` lies below the positive root `2x(s − x)`
    have hfac : (ε - 2 * x * (s - x)) * (ε + 2 * x * (s + x)) =
        ε ^ 2 - (2 * x) ^ 2 * (1 - ε) := by nlinarith
    have hpos : 0 < ε + 2 * x * (s + x) := by nlinarith
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg (sub_nonneg.mpr hcon) hpos.le]
    · intro h
      nlinarith [mul_pos (sub_pos.mpr h) hpos]

/-! ## The exact quadratic threshold -/

section Quadratic

variable {m D Kbar ε T : ℝ} {K : ℝ → ℝ}

@[tmio T, powerlib_foundation] private theorem affine_ge_min {f₀ g κ b : ℝ} (hκ : |κ| ≤ b) :
    min (f₀ - b * g) (f₀ + b * g) ≤ f₀ - κ * g := by
  rw [abs_le] at hκ
  rcases le_total 0 g with hg | hg
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

/-- The Lie-derivative form `F − κG` (`F = xᵀQx`, `G = xᵀSx` for `γ = d/2`) dominates the
smaller determinant-over-trace margin of its two extreme matrices `κ = ∓εk`. -/
@[tmio T, powerlib_foundation] private theorem lie_margin {d k ε σ κ x₀ x₁ : ℝ} (hd : 0 < d)
    (hk : 0 < k) (hε1 : ε < 1) (hε : 0 ≤ ε) (hκ : |κ| ≤ ε * k) :
    min ((d * k * (1 - ε) * d - (σ + ε * k) ^ 2) / (d * k * (1 - ε) + d))
        ((d * k * (1 + ε) * d - (ε * k - σ) ^ 2) / (d * k * (1 + ε) + d)) * (x₀ ^ 2 + x₁ ^ 2) ≤
      (d * k * x₀ ^ 2 - 2 * σ * x₀ * x₁ + d * x₁ ^ 2) - κ * (-d * x₀ ^ 2 - 2 * x₀ * x₁) := by
  have hmin := affine_ge_min (f₀ := d * k * x₀ ^ 2 - 2 * σ * x₀ * x₁ + d * x₁ ^ 2)
    (g := -d * x₀ ^ 2 - 2 * x₀ * x₁) hκ
  have hdk := mul_pos hd hk
  have hL := det_div_trace_le (p := d * k * (1 - ε)) (r := -(σ + ε * k)) (e := d)
    (by nlinarith [mul_pos hdk (by linarith : (0 : ℝ) < 1 - ε)]) x₀ x₁
  have hU := det_div_trace_le (p := d * k * (1 + ε)) (r := ε * k - σ) (e := d)
    (by nlinarith [mul_pos hdk (by linarith : (0 : ℝ) < 1 + ε)]) x₀ x₁
  rw [neg_sq] at hL
  have hxx : 0 ≤ x₀ ^ 2 + x₁ ^ 2 := by positivity
  refine le_trans ?_ hmin
  refine le_min ?_ ?_
  · refine (mul_le_mul_of_nonneg_right (min_le_right _ _) hxx).trans ?_
    linarith
  · refine (mul_le_mul_of_nonneg_right (min_le_left _ _) hxx).trans ?_
    linarith

/-- **The exact quadratic (common Lyapunov function) threshold, sufficiency.** For
`m δ̈ + D δ̇ + K(t) δ = 0` with `|K(t) − K̄| ≤ εK̄`, `0 ≤ ε < 1`, the condition
`2ε √(mK̄) < D (√(1 + ε) + √(1 − ε))` — in damping-ratio form
`2ε / (√(1 + ε) + √(1 − ε)) < 2ξ` — gives a Schur-stable monodromy for every period and every
continuous periodic waveform. The certificate is the energy-like matrix with the cross term
`γ = d/2` and the shift `σ = εk (a − b)/(a + b)`, `a = d√(k(1 − ε))`, `b = d√(k(1 + ε))`: the
Lie-derivative matrices at the two extreme stiffnesses have determinants
`a²(1 − (2εk/(a + b))²)`, `b²(1 − (2εk/(a + b))²) > 0`, and the Lie derivative is affine in the
stiffness, so `V̇ ≤ −η |x|²` uniformly (`Periodic.Robust.schurStable_of_lyapunov` with `A₀ = 0`). -/
@[tmio T, powerlib_foundation] theorem quadratic_schurStable (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hq : 2 * ε * √(m * Kbar) < D * (√(1 + ε) + √(1 - ε)))
    (hT : 0 < T) (hK : Continuous K) (hKP : Periodic K T) (hdev : ∀ t, |K t - Kbar| ≤ ε * Kbar) :
    LTI.SchurStable (monodromy (fun t => oscMatrix (D / (2 * m)) (K t / m)) T 0) := by
  set c := D / (2 * m) with hc
  set k := Kbar / m with hk
  set d := D / m with hd
  have h2c : 2 * c = d := by rw [hc, hd]; field_simp
  have hk0 : 0 < k := div_pos hKbar hm
  have hsk : 0 < √k := Real.sqrt_pos.mpr hk0
  have hsk2 : √k ^ 2 = k := Real.sq_sqrt hk0.le
  have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : 0 < √(1 + ε) := Real.sqrt_pos.mpr (by linarith)
  have hmK : √(m * Kbar) = m * √k := by
    rw [show m * Kbar = m ^ 2 * k by rw [hk]; field_simp, Real.sqrt_mul (sq_nonneg m),
      Real.sqrt_sq hm.le]
  have hD : 0 < D := by
    by_contra hD; push Not at hD
    have : D * (√(1 + ε) + √(1 - ε)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD (by positivity)
    have : 0 ≤ 2 * ε * √(m * Kbar) := by positivity
    linarith
  have hd0 : 0 < d := div_pos hD hm
  -- the certificate
  obtain ⟨a, ha⟩ : ∃ a, a = d * √k * √(1 - ε) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = d * √k * √(1 + ε) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : 2 * ε * k < a + b := by
    rw [hmK] at hq
    have h1 : 2 * ε * k * m = √k * (2 * ε * (m * √k)) := by
      linear_combination (-2 * ε * m) * hsk2
    have h2 : (a + b) * m = √k * (D * (√(1 + ε) + √(1 - ε))) := by
      rw [ha, hb, hd]; field_simp; ring
    have : 2 * ε * k * m < (a + b) * m := by
      rw [h1, h2]; exact mul_lt_mul_of_pos_left hq hsk
    exact lt_of_mul_lt_mul_right this hm.le
  have ha2 : a ^ 2 = d ^ 2 * k * (1 - ε) := by
    rw [ha, mul_pow, mul_pow, hsk2, Real.sq_sqrt (by linarith)]
  have hb2 : b ^ 2 = d ^ 2 * k * (1 + ε) := by
    rw [hb, mul_pow, mul_pow, hsk2, Real.sq_sqrt (by linarith)]
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ε * k * (a - b) / (a + b) := ⟨_, rfl⟩
  have hσ1 : σ + ε * k = 2 * ε * k * a / (a + b) := by rw [hσ]; field_simp; ring
  have hσ2 : ε * k - σ = 2 * ε * k * b / (a + b) := by rw [hσ]; field_simp; ring
  have hσlow : -(ε * k) ≤ σ := by
    have : 0 ≤ 2 * ε * k * a / (a + b) := by positivity
    linarith
  set P := energyP c k c σ with hP
  have hPs : Pᵀ = P := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hP, energyP]
  have hPa : c ^ 2 < k + 2 * c * c + σ := by nlinarith [sq_nonneg c]
  have hP₁ := fun x => (energyP_bounds hPa x).1
  have hP₂ := fun x => (energyP_bounds hPa x).2
  have hp₁ : 0 < (k + 2 * c * c + σ - c ^ 2) / (k + 2 * c * c + σ + 1) := by
    apply div_pos <;> nlinarith [sq_nonneg c]
  have hp₂ : 0 < k + 2 * c * c + σ + 1 := by nlinarith [sq_nonneg c]
  -- the uniform margin at the two extreme stiffnesses
  obtain ⟨r, hr⟩ : ∃ r, r = 2 * ε * k / (a + b) := ⟨_, rfl⟩
  have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; exact hab
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  obtain ⟨eL, heL⟩ : ∃ e, e = (d * k * (1 - ε) * d - (σ + ε * k) ^ 2) / (d * k * (1 - ε) + d) :=
    ⟨_, rfl⟩
  obtain ⟨eU, heU⟩ : ∃ e, e = (d * k * (1 + ε) * d - (ε * k - σ) ^ 2) / (d * k * (1 + ε) + d) :=
    ⟨_, rfl⟩
  have heL0 : 0 < eL := by
    have hra : σ + ε * k = r * a := by rw [hσ1, hr]; field_simp
    have hnum : d * k * (1 - ε) * d - (σ + ε * k) ^ 2 = a ^ 2 * (1 - r ^ 2) := by
      rw [hra, mul_pow, ha2]; ring
    rw [heL, hnum]
    have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 two_ne_zero
    apply div_pos (mul_pos (pow_pos ha0 2) (by linarith))
    have := mul_pos (mul_pos hd0 hk0) (by linarith : (0 : ℝ) < 1 - ε)
    linarith
  have heU0 : 0 < eU := by
    have hrb : ε * k - σ = r * b := by rw [hσ2, hr]; field_simp
    have hnum : d * k * (1 + ε) * d - (ε * k - σ) ^ 2 = b ^ 2 * (1 - r ^ 2) := by
      rw [hrb, mul_pow, hb2]; ring
    rw [heU, hnum]
    have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 two_ne_zero
    apply div_pos (mul_pos (pow_pos hb0 2) (by linarith))
    have := mul_pos (mul_pos hd0 hk0) (by linarith : (0 : ℝ) < 1 + ε)
    linarith
  obtain ⟨η, hη⟩ : ∃ η, η = min eL eU := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min heL0 heU0
  have hBc : Continuous fun t => oscMatrix c (K t / m) := by
    simp only [oscMatrix]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hβb : ∀ t x, x ⬝ᵥ ((P * oscMatrix c (K t / m) + (oscMatrix c (K t / m))ᵀ * P) *ᵥ x) ≤
      -η * (x ⬝ᵥ x) := by
    intro t x
    have hκ : |K t / m - k| ≤ ε * k := by
      rw [hk, ← sub_div, abs_div, abs_of_pos hm, mul_div_assoc']
      exact div_le_div_of_nonneg_right (hdev t) hm.le
    rw [add_comm, hP, lyapunov_oscMatrix, add_mulVec, neg_mulVec, smul_mulVec, dotProduct_add,
      dotProduct_neg, dotProduct_smul, smul_eq_mul, dotProduct_mulVec_fin_two,
      dotProduct_mulVec_fin_two]
    have hxx : x ⬝ᵥ x = x 0 ^ 2 + x 1 ^ 2 := by simp [dotProduct, Fin.sum_univ_two, sq]
    rw [hxx]
    simp only [energyQ, energyS, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    have key := lie_margin (σ := σ) (x₀ := x 0) (x₁ := x 1) hd0 hk0 hε1 hε hκ
    have hc2 : c = d / 2 := by linarith
    calc _ = -((d * k * x 0 ^ 2 - 2 * σ * x 0 * x 1 + d * x 1 ^ 2) -
          (K t / m - k) * (-d * x 0 ^ 2 - 2 * x 0 * x 1)) := by rw [hc2]; ring
      _ ≤ -η * (x 0 ^ 2 + x 1 ^ 2) := by rw [hη]; rw [heL, heU] at *; linarith
  have hlyap : (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * P + P * 0 = -0 := by simp
  have h := (Periodic.Robust.schurStable_of_lyapunov (A₀ := 0) (Q := 0) (q := 0) hPs hlyap hp₁
    hp₂ hP₁ hP₂ (fun x => by simp) (by linarith : -η < 0) hT hBc
    (fun t => by simp only [hKP t]) hβb).1
  simpa only [zero_add] using h

/-- One extreme stiffness: if `xᵀ ((oscMatrix c k')ᵀ P + P oscMatrix c k') x < 0` for every
`x ≠ 0` (`k' > 0`, `P` symmetric with `P₁₁ > 0`), then `|P₀₀ − 2c P₀₁ − k' P₁₁| < 2c P₁₁ √k'`. -/
@[tmio T, powerlib_foundation] private theorem lie_negDef_bound {c k' : ℝ} (hk' : 0 < k')
    {P : Matrix (Fin 2) (Fin 2) ℝ} (hPs : Pᵀ = P) (he : 0 < P 1 1)
    (hneg : ∀ x : Fin 2 → ℝ, x ≠ 0 →
      x ⬝ᵥ (((oscMatrix c k')ᵀ * P + P * oscMatrix c k') *ᵥ x) < 0) :
    0 < c ∧ |P 0 0 - 2 * c * P 0 1 - k' * P 1 1| < 2 * c * P 1 1 * √k' := by
  have h10 : P 1 0 = P 0 1 := by
    have := congrFun (congrFun hPs 0) 1
    simpa [Matrix.transpose_apply] using this
  have hform : ∀ x : Fin 2 → ℝ, x ⬝ᵥ (((oscMatrix c k')ᵀ * P + P * oscMatrix c k') *ᵥ x) =
      -2 * k' * P 0 1 * x 0 ^ 2 + 2 * (P 0 0 - 2 * c * P 0 1 - k' * P 1 1) * x 0 * x 1 +
        (2 * P 0 1 - 4 * c * P 1 1) * x 1 ^ 2 := by
    intro x
    rw [dotProduct_mulVec_fin_two]
    simp [oscMatrix, Matrix.mul_apply, Fin.sum_univ_two, h10]
    ring
  set p := P 0 0
  set r := P 0 1
  set e := P 1 1
  have h1 := hneg ![1, 0] (by intro h; simpa using congrFun h 0)
  have h2 := hneg ![0, 1] (by intro h; simpa using congrFun h 1)
  rw [hform] at h1 h2
  simp at h1 h2
  have hr : 0 < r := by nlinarith
  have hc : 0 < c := by nlinarith
  set α := 2 * k' * r
  set β := -(p - 2 * c * r - k' * e)
  have hα : 0 < α := by positivity
  have h3 := hneg ![β, -α] (by intro h; have := congrFun h 1; simp at this; linarith)
  rw [hform] at h3
  simp at h3
  -- `α (α (4ce − 2r) − β²) > 0`
  have hdet : β ^ 2 < α * (4 * c * e - 2 * r) := by
    have : 0 < α * (α * (4 * c * e - 2 * r) - β ^ 2) := by nlinarith
    have := (mul_pos_iff_of_pos_left hα).mp this
    linarith
  have hsq : (p - 2 * c * r - k' * e) ^ 2 < (2 * c * e * √k') ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hk'.le]
    have hβ2 : β ^ 2 = (p - 2 * c * r - k' * e) ^ 2 := by rw [neg_sq]
    nlinarith [sq_nonneg (2 * c * e - 2 * r)]
  refine ⟨hc, abs_lt_of_sq_lt_sq hsq (by positivity)⟩

/-- **The exact quadratic threshold, necessity.** If some symmetric `P ≻ 0` makes the Lie
derivative negative definite at both extreme stiffnesses `K̄(1 ∓ ε)` — a common quadratic Lyapunov
function for the stiffness interval, the only certificate the Lyapunov route can give — then
`2ε √(mK̄) < D (√(1 + ε) + √(1 − ε))`. Hence `quadratic_schurStable` is the exact threshold of
quadratic robust certificates: no quadratic certificate covers a larger depth. Proof: each
extreme gives `|P₀₀ − 2cP₀₁ − k'P₁₁| < 2cP₁₁√k'` (`2c = D/m`), and the two differ by `2εkP₁₁`. -/
@[tmio T, powerlib_foundation] theorem quadratic_threshold_converse (hm : 0 < m)
    (hKbar : 0 < Kbar) (hε : 0 ≤ ε) (hε1 : ε < 1) {P : Matrix (Fin 2) (Fin 2) ℝ} (hPs : Pᵀ = P)
    (hP : ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x))
    (hlo : ∀ x : Fin 2 → ℝ, x ≠ 0 →
      x ⬝ᵥ (((oscMatrix (D / (2 * m)) (Kbar * (1 - ε) / m))ᵀ * P +
        P * oscMatrix (D / (2 * m)) (Kbar * (1 - ε) / m)) *ᵥ x) < 0)
    (hhi : ∀ x : Fin 2 → ℝ, x ≠ 0 →
      x ⬝ᵥ (((oscMatrix (D / (2 * m)) (Kbar * (1 + ε) / m))ᵀ * P +
        P * oscMatrix (D / (2 * m)) (Kbar * (1 + ε) / m)) *ᵥ x) < 0) :
    2 * ε * √(m * Kbar) < D * (√(1 + ε) + √(1 - ε)) := by
  have he : 0 < P 1 1 := by
    have := hP ![0, 1] (by intro h; simpa using congrFun h 1)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two] using this
  have hklo : 0 < Kbar * (1 - ε) / m := div_pos (mul_pos hKbar (by linarith)) hm
  have hkhi : 0 < Kbar * (1 + ε) / m := div_pos (mul_pos hKbar (by linarith)) hm
  obtain ⟨hc, hL⟩ := lie_negDef_bound hklo hPs he hlo
  obtain ⟨-, hU⟩ := lie_negDef_bound hkhi hPs he hhi
  set c := D / (2 * m)
  set k := Kbar / m with hk
  have hk0 : 0 < k := div_pos hKbar hm
  have hsk : 0 < √k := Real.sqrt_pos.mpr hk0
  have hsk2 : √k ^ 2 = k := Real.sq_sqrt hk0.le
  have hlo' : √(Kbar * (1 - ε) / m) = √k * √(1 - ε) := by
    rw [show Kbar * (1 - ε) / m = k * (1 - ε) by rw [hk]; ring, Real.sqrt_mul hk0.le]
  have hhi' : √(Kbar * (1 + ε) / m) = √k * √(1 + ε) := by
    rw [show Kbar * (1 + ε) / m = k * (1 + ε) by rw [hk]; ring, Real.sqrt_mul hk0.le]
  rw [hlo'] at hL
  rw [hhi'] at hU
  -- the two extreme stiffnesses differ by `2εk P₁₁`
  have hdiff : 2 * ε * k * P 1 1 < 2 * c * P 1 1 * (√k * √(1 - ε)) +
      2 * c * P 1 1 * (√k * √(1 + ε)) := by
    have e1 : 2 * ε * k * P 1 1 = (P 0 0 - 2 * c * P 0 1 - Kbar * (1 - ε) / m * P 1 1) -
        (P 0 0 - 2 * c * P 0 1 - Kbar * (1 + ε) / m * P 1 1) := by rw [hk]; ring
    rw [e1]
    have := abs_sub _ _ |>.trans_lt (add_lt_add hL hU)
    exact (le_abs_self _).trans_lt (by simpa using this)
  have h1 : 2 * ε * k < 2 * c * (√k * (√(1 - ε) + √(1 + ε))) := by
    have : P 1 1 * (2 * ε * k) < P 1 1 * (2 * c * (√k * (√(1 - ε) + √(1 + ε)))) := by
      linarith
    exact lt_of_mul_lt_mul_left this he.le
  have h2 : 2 * ε * √k < 2 * c * (√(1 - ε) + √(1 + ε)) := by
    have : √k * (2 * ε * √k) < √k * (2 * c * (√(1 - ε) + √(1 + ε))) := by
      have e : √k * (2 * ε * √k) = 2 * ε * k := by linear_combination (2 * ε) * hsk2
      rw [e]; linarith
    exact lt_of_mul_lt_mul_left this hsk.le
  have hmK : √(m * Kbar) = m * √k := by
    rw [show m * Kbar = m ^ 2 * k by rw [hk]; field_simp, Real.sqrt_mul (sq_nonneg m),
      Real.sqrt_sq hm.le]
  have h2c : 2 * c * m = D := by simp only [c]; field_simp
  rw [hmK]
  have := mul_lt_mul_of_pos_left h2 hm
  calc 2 * ε * (m * √k) = m * (2 * ε * √k) := by ring
    _ < m * (2 * c * (√(1 - ε) + √(1 + ε))) := this
    _ = D * (√(1 + ε) + √(1 - ε)) := by rw [← h2c]; ring

/-- **The universal threshold lies strictly inside the quadratic one.** For `0 ≤ ε < 1`, the
universal condition `ε/√(1 − ε) < D/√(mK̄)` implies the quadratic condition of
`quadratic_schurStable`, and for `0 < ε < 1` the quadratic threshold function is strictly smaller,
`2ε / (√(1 + ε) + √(1 − ε)) < ε / √(1 − ε)`: at every damping ratio the quadratic certificate
covers strictly deeper modulations than the universal bound (both agree to first order,
`ε ≈ 2ξ`, as `ε → 0`). -/
@[tmio T, powerlib_foundation] theorem universal_lt_quadratic (hm : 0 < m) (hKbar : 0 < Kbar)
    (hε : 0 ≤ ε) (hε1 : ε < 1) :
    (ε / √(1 - ε) < D / √(m * Kbar) → 2 * ε * √(m * Kbar) < D * (√(1 + ε) + √(1 - ε))) ∧
      (0 < ε → 2 * ε / (√(1 + ε) + √(1 - ε)) < ε / √(1 - ε)) := by
  have hs1 : 0 < √(1 - ε) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : 0 < √(1 + ε) := Real.sqrt_pos.mpr (by linarith)
  have hs3 : 0 < √(m * Kbar) := Real.sqrt_pos.mpr (by positivity)
  have hlt : √(1 - ε) ≤ √(1 + ε) := Real.sqrt_le_sqrt (by linarith)
  constructor
  · intro h
    rw [div_lt_div_iff₀ hs1 hs3] at h
    have hD : 0 < D := by
      by_contra hD; push Not at hD
      have : D * √(1 - ε) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD hs1.le
      have : 0 ≤ ε * √(m * Kbar) := by positivity
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hlt hD.le]
  · intro hε0
    have hlt' : √(1 - ε) < √(1 + ε) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    rw [div_lt_div_iff₀ (by positivity) hs1]
    nlinarith

end Quadratic

end powerlib.ParametricResonance.RobustVsUniversal
