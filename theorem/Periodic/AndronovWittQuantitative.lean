import theorem.Periodic.AndronovWitt

/-! # The Andronov–Witt theorem with explicit constants

`theorem/Periodic/AndronovWitt.lean` proves that a periodic orbit of `ẋ = f(x)` whose deflated
monodromy `D = M − f(p) wᵀ` (`w ⬝ f(p) = 1`, `p = x_*(0)`) is Schur stable is orbitally
exponentially stable with asymptotic phase, with constants `δ`, `C`, `λ` that are not explicit
(the return time of a section from the implicit function theorem, and a non-quantitative
contraction of the Poincaré map). This module gives `δ`, `C`, `λ` as closed-form expressions in
the data `K` (Lipschitz constant of `f`), `L₂` (Lipschitz constant of `Df`), `T`, `V = ‖f(p)‖`,
`W = ∑ᵢ |wᵢ|` (the dual norm of `w`, `W ≤ n ‖w‖`), and a **contraction datum** `‖D^N‖ ≤ q < 1`,
`N ≥ 1`, which holds for some `N` exactly when `D` is Schur stable
(`schurStable_iff_exists_pow_norm_lt_one`). With `q' = (1 + q)/2`:

* `B = V e^{KT}` (`speed`: `‖f(x_*(t))‖ ≤ B`), `a = e^{3KT/2} + B W` (`growth`),
  `c₂ = L₂ T e^{3KT} + K W a` (`curvature`);
* `δ = (1 − q) T / (2 a^{2N} (W + N T c₂))` (`radius`);
* `C₁ = a^N / q'`, `C_θ = 2 N W C₁ / (1 − q)`, `C = e^{3KT/2} (C₁ + (B + 1) C_θ) / q'` (`gain`);
* `λ = −log q' / (N · 3T/2) = 2 log(2/(1 + q)) / (3 N T)` (`rate`);
* from an arbitrary point `x_*(σ)` of the orbit: `δ' = δ e^{−KT}` (`orbitRadius`) and
  `C' = (1 + (1 + B) C) e^{KT} e^{λT}` (`orbitGain`).

Every solution with `‖x(0) − p‖ ≤ δ` has a phase `θ`, `|θ| ≤ C ‖x(0) − p‖`, with
`‖x(t) − x_*(t + θ)‖ ≤ C e^{−λt} ‖x(0) − p‖` (`asymptoticPhase_explicit`); the same holds with
`δ'`, `C'` from every point `x_*(σ)` (`asymptoticPhase_uniform_explicit`), and
`dist(x(t), x_*(ℝ)) ≤ C' e^{−λt} dist(x(0), x_*(ℝ))` when `dist(x(0), x_*(ℝ)) ≤ δ'`
(`infDist_orbit_le_explicit`).

The route avoids the implicit function theorem. Instead of the return time to a section, the
solution from `ξ` is read at the **explicit** time `τ(ξ) = T − w ⬝ (ξ − p)` (`returnTime`): the
map `F(ξ) = x(τ(ξ); ξ)` (`PoincareSection.poincareMap` with this time) fixes `p` and has the
derivative `M − f(p) wᵀ = D` there, and its iterates are the solution sampled at the accumulated
times (`AndronovWitt.iterate_poincareMap`). Then:
1. `step_bounds`: on `W ‖ξ − p‖ ≤ T/2`, `|τ(ξ) − T| ≤ W ‖ξ − p‖`, `‖F(ξ) − p‖ ≤ a ‖ξ − p‖` and
   `‖F(ξ) − p − D(ξ − p)‖ ≤ c₂ ‖ξ − p‖²` — the first variation with the quadratic remainder
   `L₂ T e^{3KT}` of `FlowDerivative.norm_solution_sub_le_sq` at the time `T`, and the mean value
   inequality for the time shift `τ(ξ) − T`;
2. `block_contraction`, `iterate_contraction`: on `‖ξ − p‖ ≤ δ` the block `F^N` contracts by `q'`
   (the linear part by `q`, the accumulated quadratic remainders by `N c₂ a^{2N} δ ≤ (1 − q)/2`),
   so `‖F^k(ξ) − p‖ ≤ a^N q'^{⌊k/N⌋} ‖ξ − p‖`;
3. `phase_of_samples`: with the rate per step `ϑ = q'^{1/N}` the samples converge like `ϑ^k`, the
   phase `θ = −∑ₖ (τ_k − T)` converges with a geometric tail, and Grönwall interpolates between
   the samples; Bernoulli's inequality `1 − ϑ^N ≤ N (1 − ϑ)` turns `1/(1 − ϑ)` into
   `2N/(1 − q)`.

Scope.
* `ẋ = f(x)` on `ℝ^{Fin n}` with the sup norm (operator `L∞` norm on matrices), continuous time,
  solutions on `[0, ∞)` (Mathlib `IsIntegralCurveOn`); `f` differentiable and globally
  `K`-Lipschitz, `Df` globally `L₂`-Lipschitz in the operator norm (so `f` is `C^{1,1}`); `x_*`
  a global `T`-periodic solution, `T > 0`, `T` not necessarily minimal; `w ⬝ f(p) = 1` (which
  forces `f(p) ≠ 0`).
* The constants are explicit but crude: the rate `−log((1 + q)/2)/(N · 3T/2)` is below the
  optimal `−log ρ(D)/T` (the factor `(1 + q)/2` absorbs the quadratic remainder, the window
  `3T/2` bounds the sampling times); no attempt is made at sharp constants. The critical case
  (a nontrivial multiplier on the unit circle) is not treated. A field that is only locally
  Lipschitz would first be cut off near the orbit (`theorem/Periodic/LocalField.lean`); the
  constants would then be those of the cut-off field, which is not done here.
* Generic mathematics; no model family.

Source: A. A. Andronov and A. A. Witt, "Zur Stabilität nach Liapounoff", Phys. Z. Sowjetunion 4
(1933); Coddington and Levinson, *Theory of Ordinary Differential Equations*, Ch. 13 §2 (orbital
asymptotic stability with asymptotic phase); Hartman, *Ordinary Differential Equations*, Ch. V
(the first variation) and the Grönwall inequality; the open item of
`theorem/Periodic/AndronovWitt.lean` (Scope: "The constants `δ`, `C`, `λ` are not explicit").

Results.
* The constants: `speed`, `growth`, `curvature`, `radius`, `sampleGain`, `phaseGain`, `gain`,
  `rate`, `orbitRadius`, `orbitGain`; `radius_pos`, `rate_pos`.
* `step_bounds` — one step of the time-shift map `F`, with explicit growth and remainder.
* `block_contraction`, `iterate_contraction` — a map with an explicit second-order remainder at a
  fixed point and a contraction datum `‖D^N‖ ≤ q < 1` for its linear part: the block `F^N`
  contracts by `(1 + q)/2` on an explicit ball, and the iterates decay geometrically.
* `phase_of_samples` — the asymptotic phase, with explicit constants, from geometrically
  converging samples of a solution at accumulated times.
* `schurStable_iff_exists_pow_norm_lt_one` — Schur stability ⇔ `‖D^N‖ < 1` for some `N ≥ 1`.
* **The theorem**: `asymptoticPhase_explicit` (from `x_*(0)`), `asymptoticPhase_uniform_explicit`
  (from every `x_*(σ)`), `infDist_orbit_le_explicit` (orbital exponential stability), and
  `andronov_witt_explicit` (all of it, with the positivity of `δ'` and `λ`).

Corrections.
None: an extension (explicit constants for `theorem/Periodic/AndronovWitt.lean`, whose Scope left
them non-explicit).

Family and connection conclusions.
None: static evidence on autonomous ODEs (orbital stability of a periodic orbit, quantitatively).
-/

noncomputable section
namespace powerlib.Periodic.AndronovWittQuantitative

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative FlipOrbit PoincareSection AndronovWitt

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {K L₂ : NNReal}

/-! ## The explicit constants -/

/-- The speed bound `B = V e^{KT}` of the orbit (`V = ‖f(p)‖`). -/
def speed (K T V : ℝ) : ℝ := V * Real.exp (K * T)

/-- The one-step growth factor `a = e^{3KT/2} + B W` (`W = ∑ᵢ |wᵢ|`). -/
def growth (K T V W : ℝ) : ℝ := Real.exp (K * (3 * T / 2)) + speed K T V * W

/-- The second-order constant `c₂ = L₂ T e^{3KT} + K W a`. -/
def curvature (K L₂ T V W : ℝ) : ℝ :=
  L₂ * T * Real.exp (3 * (K * T)) + K * W * growth K T V W

/-- The radius `δ = (1 − q) T / (2 a^{2N} (W + N T c₂))`. -/
def radius (K L₂ T V W : ℝ) (N : ℕ) (q : ℝ) : ℝ :=
  (1 - q) * T / (2 * growth K T V W ^ (2 * N) * (W + N * T * curvature K L₂ T V W))

/-- The sampling gain `C₁ = a^N / q'`, `q' = (1 + q)/2`. -/
def sampleGain (K T V W : ℝ) (N : ℕ) (q : ℝ) : ℝ := growth K T V W ^ N / ((1 + q) / 2)

/-- The phase gain `C_θ = 2 N W C₁ / (1 − q)`. -/
def phaseGain (K T V W : ℝ) (N : ℕ) (q : ℝ) : ℝ := 2 * N * W * sampleGain K T V W N q / (1 - q)

/-- The gain `C = e^{3KT/2} (C₁ + (B + 1) C_θ) / q'` of the solution and of the phase. -/
def gain (K T V W : ℝ) (N : ℕ) (q : ℝ) : ℝ :=
  Real.exp (K * (3 * T / 2)) *
    (sampleGain K T V W N q + (speed K T V + 1) * phaseGain K T V W N q) / ((1 + q) / 2)

/-- The rate `λ = −log((1 + q)/2) / (N · 3T/2)`. -/
def rate (T : ℝ) (N : ℕ) (q : ℝ) : ℝ := -Real.log ((1 + q) / 2) / (N * (3 * T / 2))

/-- The radius from an arbitrary point of the orbit, `δ e^{−KT}`. -/
def orbitRadius (K L₂ T V W : ℝ) (N : ℕ) (q : ℝ) : ℝ :=
  radius K L₂ T V W N q / Real.exp (K * T)

/-- The gain from an arbitrary point of the orbit, `(1 + (1 + B) C) e^{KT} e^{λT}`. -/
def orbitGain (K T V W : ℝ) (N : ℕ) (q : ℝ) : ℝ :=
  (1 + (1 + speed K T V) * gain K T V W N q) * Real.exp (K * T) * Real.exp (rate T N q * T)

/-- The explicit return time `τ(ξ) = T − w ⬝ (ξ − p)`. -/
def returnTime (T : ℝ) (w p : Fin n → ℝ) (ξ : Fin n → ℝ) : ℝ := T - w ⬝ᵥ (ξ - p)

/-! ## Elementary bounds -/

/-- `|w ⬝ y| ≤ (∑ᵢ |wᵢ|) ‖y‖` in the sup norm. -/
@[tmio T, powerlib_foundation] private theorem abs_dot_le (w y : Fin n → ℝ) :
    |w ⬝ᵥ y| ≤ (∑ i, |w i|) * ‖y‖ := by
  rw [dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i)
    (abs_nonneg _)

/-- The speed along the orbit: `‖f(x_*(t))‖ ≤ ‖f(x_*(0))‖ e^{KT}` (Grönwall for the velocity
`ż = Df(x_*) z`). -/
@[tmio T, powerlib_foundation] private theorem norm_velocity_le (hfd : Differentiable ℝ f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (t : ℝ) :
    ‖f (xs t)‖ ≤ speed K T ‖f (xs 0)‖ := by
  have hz : ∀ r, HasDerivAt (fun r => f (xs r)) (fderiv ℝ f (xs r) (f (xs r))) r := fun r =>
    (hfd (xs r)).hasFDerivAt.comp_hasDerivAt r (hxs r)
  have hb := norm_le_of_hasDerivWithinAt (w := fun r => f (xs r)) (s := 0) (t := T) K.2 le_rfl
    (fun r _ => (hz r).hasDerivWithinAt)
    (fun r _ => by
      calc ‖fderiv ℝ f (xs r) (f (xs r))‖ ≤ ‖fderiv ℝ f (xs r)‖ * ‖f (xs r)‖ :=
            (fderiv ℝ f (xs r)).le_opNorm _
        _ ≤ K * ‖f (xs r)‖ :=
            mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hfK) (norm_nonneg _)
        _ = K * ‖f (xs r)‖ + 0 := (add_zero _).symm)
    le_rfl
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hT t
  rw [hty]
  have h := hb y (Ico_subset_Icc_self hy)
  simp only [zero_mul, add_zero, sub_zero] at h
  exact h

/-- The orbit moves with speed at most `B`: `‖x_*(a) − x_*(b)‖ ≤ B |a − b|`. -/
@[tmio T, powerlib_foundation] private theorem norm_sub_le_speed (hfd : Differentiable ℝ f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (a b : ℝ) :
    ‖xs a - xs b‖ ≤ speed K T ‖f (xs 0)‖ * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
    (fun t _ => (hxs t).hasDerivWithinAt)
    (fun t _ => norm_velocity_le hfd hfK hxs hT hper t) convex_univ (mem_univ b) (mem_univ a)
  rwa [Real.norm_eq_abs] at h

/-- The monodromy grows at most like `e^{KT}`: `‖M e‖ ≤ e^{KT} ‖e‖`. -/
@[tmio T, powerlib_foundation] private theorem norm_monodromy_mulVec_le (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxc : Continuous xs) {T : ℝ} (hT : 0 ≤ T)
    (e : Fin n → ℝ) :
    ‖monodromy (variationalMatrix f xs) T 0 *ᵥ e‖ ≤ Real.exp (K * T) * ‖e‖ := by
  have hA := variationalMatrix_continuous hf hxc
  have h := norm_le_of_hasDerivWithinAt
    (w := fun r => transition (variationalMatrix f xs) r 0 *ᵥ e) (s := 0) (t := T) (δ := ‖e‖)
    K.2 le_rfl
    (fun r _ => (FlowDerivative.hasDerivAt_transition_mulVec hA 0 e r).hasDerivWithinAt)
    (fun r _ => by
      rw [variationalMatrix_mulVec]
      calc ‖fderiv ℝ f (xs r) (transition (variationalMatrix f xs) r 0 *ᵥ e)‖
          ≤ ‖fderiv ℝ f (xs r)‖ * ‖transition (variationalMatrix f xs) r 0 *ᵥ e‖ :=
            (fderiv ℝ f (xs r)).le_opNorm _
        _ ≤ K * ‖transition (variationalMatrix f xs) r 0 *ᵥ e‖ :=
            mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hfK) (norm_nonneg _)
        _ = _ + 0 := (add_zero _).symm)
    (le_of_eq (by simp [LinearSystems.stateTransitionMatrix_self])) T ⟨hT, le_rfl⟩
  simp only [zero_mul, add_zero, sub_zero] at h
  rw [monodromy, zero_add, mul_comm]
  exact h

/-! ## One step of the time-shift map -/

/-- **One step of the time-shift map, with explicit constants.** Let `F(ξ) = x(τ(ξ); ξ)` be the
solution from `ξ` read at the explicit time `τ(ξ) = T − w ⬝ (ξ − p)`, `p = x_*(0)`
(`PoincareSection.poincareMap` with this return time). If `W ‖ξ − p‖ ≤ T/2`, `W = ∑ᵢ |wᵢ|`, then
`|τ(ξ) − T| ≤ W ‖ξ − p‖`, `‖F(ξ) − p‖ ≤ a ‖ξ − p‖` and the second-order remainder
`‖F(ξ) − p − D(ξ − p)‖ ≤ c₂ ‖ξ − p‖²` of the deflated monodromy `D = M − f(p) wᵀ` hold, with
`a = growth`, `c₂ = curvature`. -/
@[tmio T, powerlib_foundation] theorem step_bounds (hfd : Differentiable ℝ f)
    (hfK : LipschitzWith K f) (hL : LipschitzWith L₂ (fderiv ℝ f)) {xs : ℝ → Fin n → ℝ}
    (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T) (hper : Periodic xs T)
    (w : Fin n → ℝ) {ξ : Fin n → ℝ} (hξ : (∑ i, |w i|) * ‖ξ - xs 0‖ ≤ T / 2) :
    |returnTime T w (xs 0) ξ - T| ≤ (∑ i, |w i|) * ‖ξ - xs 0‖ ∧
    ‖poincareMap hfK (returnTime T w (xs 0)) ξ - xs 0‖ ≤
      growth K T ‖f (xs 0)‖ (∑ i, |w i|) * ‖ξ - xs 0‖ ∧
    ‖poincareMap hfK (returnTime T w (xs 0)) ξ - xs 0 -
        (monodromy (variationalMatrix f xs) T 0 - vecMulVec (f (xs 0)) w) *ᵥ (ξ - xs 0)‖ ≤
      curvature K L₂ T ‖f (xs 0)‖ (∑ i, |w i|) * ‖ξ - xs 0‖ ^ 2 := by
  have hf : ContDiff ℝ 1 f := contDiff_one_iff_fderiv.2 ⟨hfd, hL.continuous⟩
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  set p := xs 0 with hp
  set v := f p with hv
  set W := ∑ i, |w i| with hW
  set e := ξ - p with he
  set τ := returnTime T w p with hτdef
  set B := speed K T ‖v‖ with hB
  set E := Real.exp (K * (3 * T / 2)) with hE
  have hB0 : 0 ≤ B := by rw [hB, speed]; positivity
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hGc : Continuous (uncurry fun _ : ℝ => f) := hfK.continuous.comp continuous_snd
  set φ := flow (G := fun _ => f) hGc (fun _ => hfK) 0 ξ with hφdef
  have hφ : IsIntegralCurveOn φ (fun _ => f) (Ici 0) := flow_solution _ _ 0 ξ
  have hφ0 : φ 0 = ξ := flow_start _ _ 0 ξ
  have hFξ : poincareMap hfK τ ξ = φ (τ ξ) := rfl
  have hτT : τ ξ - T = -(w ⬝ᵥ e) := by
    simp only [hτdef, returnTime]; ring
  have hs : |τ ξ - T| ≤ W * ‖e‖ := by
    rw [hτT, abs_neg]; exact abs_dot_le w e
  have hτ1 : T / 2 ≤ τ ξ := by have := (abs_le.1 (hs.trans hξ)).1; linarith
  have hτ2 : τ ξ ≤ 3 * T / 2 := by have := (abs_le.1 (hs.trans hξ)).2; linarith
  have hxsI : ∀ a b : ℝ, IsIntegralCurveOn xs (fun _ => f) (Icc a b) :=
    fun _ _ r _ => (hxs r).hasDerivWithinAt
  have hsep : ∀ r, 0 ≤ r → r ≤ 3 * T / 2 → ‖φ r - xs r‖ ≤ E * ‖e‖ := by
    intro r hr0 hr
    have h := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK) (hφ.mono Icc_subset_Ici_self)
      (hxsI 0 r) r ⟨hr0, le_rfl⟩
    rw [dist_eq_norm, dist_eq_norm, hφ0, sub_zero] at h
    calc ‖φ r - xs r‖ ≤ ‖e‖ * Real.exp (K * r) := h
      _ ≤ ‖e‖ * E :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr K.2))
            (norm_nonneg _)
      _ = E * ‖e‖ := mul_comm _ _
  have hspeed : ∀ a b, ‖xs a - xs b‖ ≤ B * |a - b| := norm_sub_le_speed hfd hfK hxs hT hper
  have hpT : xs T = p := by simpa using hper 0
  have hBW : B * |τ ξ - T| ≤ B * W * ‖e‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hs hB0
  -- the growth bound
  have h2 : ‖φ (τ ξ) - p‖ ≤ growth K T ‖v‖ W * ‖e‖ := by
    calc ‖φ (τ ξ) - p‖ = ‖(φ (τ ξ) - xs (τ ξ)) + (xs (τ ξ) - xs T)‖ := by
          rw [hpT]; abel_nf
      _ ≤ ‖φ (τ ξ) - xs (τ ξ)‖ + ‖xs (τ ξ) - xs T‖ := norm_add_le _ _
      _ ≤ E * ‖e‖ + B * |τ ξ - T| :=
          add_le_add (hsep _ (by linarith) hτ2) (hspeed _ _)
      _ ≤ E * ‖e‖ + B * W * ‖e‖ := by linarith
      _ = growth K T ‖v‖ W * ‖e‖ := by rw [growth, ← hB, ← hE]; ring
  -- the first-variation remainder at the time `T`
  have hA := variationalMatrix_continuous hf hxc
  have h3a : ‖φ T - xs T - monodromy (variationalMatrix f xs) T 0 *ᵥ e‖ ≤
      L₂ * T * Real.exp (3 * (K * T)) * ‖e‖ ^ 2 := by
    have h := norm_solution_sub_le_sq (G := fun _ => f) (fun _ x => hfd x) (fun _ => hfK) hA
      hT.le (x₀ := xs) (x₁ := φ) (fun r _ v => variationalMatrix_mulVec r v) (hxsI 0 T)
      (hφ.mono Icc_subset_Ici_self) (L₂ := L₂) (fun _ _ ζ ζ' => hL.norm_sub_le ζ ζ')
    rw [hφ0, sub_zero] at h
    rw [monodromy, zero_add]
    exact h
  -- the time-shift remainder
  have hsub : uIcc T (τ ξ) ⊆ Icc (T / 2) (3 * T / 2) := by
    exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨hτ1, hτ2⟩
  have h3b : ‖φ (τ ξ) - φ T - (τ ξ - T) • v‖ ≤ K * growth K T ‖v‖ W * ‖e‖ * |τ ξ - T| := by
    have hder : ∀ r ∈ uIcc T (τ ξ), HasDerivWithinAt (fun r => φ r - r • v)
        (f (φ r) - (1 : ℝ) • v) (uIcc T (τ ξ)) r := fun r hr => by
      have hr0 : r ∈ Ici (0 : ℝ) := by have := (hsub hr).1; simp only [mem_Ici]; linarith
      exact ((hφ r hr0).mono (hsub.trans fun y hy => by
        simp only [mem_Ici]; linarith [hy.1])).sub
        ((hasDerivAt_id r).smul_const v).hasDerivWithinAt
    have hbd : ∀ r ∈ uIcc T (τ ξ), ‖f (φ r) - (1 : ℝ) • v‖ ≤ K * growth K T ‖v‖ W * ‖e‖ :=
      fun r hr => by
        have hr' := hsub hr
        have hrT : |r - T| ≤ |τ ξ - T| := abs_sub_left_of_mem_uIcc hr
        rw [one_smul, hv]
        calc ‖f (φ r) - f p‖ ≤ K * ‖φ r - p‖ := hfK.norm_sub_le _ _
          _ ≤ K * (growth K T ‖v‖ W * ‖e‖) := by
              refine mul_le_mul_of_nonneg_left ?_ K.2
              calc ‖φ r - p‖ = ‖(φ r - xs r) + (xs r - xs T)‖ := by rw [hpT]; abel_nf
                _ ≤ ‖φ r - xs r‖ + ‖xs r - xs T‖ := norm_add_le _ _
                _ ≤ E * ‖e‖ + B * |r - T| :=
                    add_le_add (hsep _ (by linarith [hr'.1]) hr'.2) (hspeed _ _)
                _ ≤ E * ‖e‖ + B * W * ‖e‖ := by
                    have := mul_le_mul_of_nonneg_left hrT hB0; linarith
                _ = growth K T ‖v‖ W * ‖e‖ := by rw [growth, ← hB, ← hE]; ring
          _ = K * growth K T ‖v‖ W * ‖e‖ := by ring
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc _ _)
      left_mem_uIcc right_mem_uIcc
    rw [Real.norm_eq_abs] at h
    calc ‖φ (τ ξ) - φ T - (τ ξ - T) • v‖ = ‖(φ (τ ξ) - τ ξ • v) - (φ T - T • v)‖ := by
          rw [sub_smul]; abel_nf
      _ ≤ _ := h
  refine ⟨hs, by rw [hFξ]; exact h2, ?_⟩
  -- the second-order remainder
  have key : poincareMap hfK τ ξ - p -
      (monodromy (variationalMatrix f xs) T 0 - vecMulVec v w) *ᵥ e =
      (φ T - xs T - monodromy (variationalMatrix f xs) T 0 *ᵥ e) +
        (φ (τ ξ) - φ T - (τ ξ - T) • v) := by
    rw [hFξ, hτT, sub_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hpT, neg_smul]
    abel
  rw [key]
  have hK0 : (0 : ℝ) ≤ K * growth K T ‖v‖ W * ‖e‖ := by
    have : 0 ≤ growth K T ‖v‖ W := by rw [growth]; positivity
    positivity
  calc _ ≤ ‖φ T - xs T - monodromy (variationalMatrix f xs) T 0 *ᵥ e‖ +
        ‖φ (τ ξ) - φ T - (τ ξ - T) • v‖ := norm_add_le _ _
    _ ≤ L₂ * T * Real.exp (3 * (K * T)) * ‖e‖ ^ 2 +
        K * growth K T ‖v‖ W * ‖e‖ * (W * ‖e‖) :=
        add_le_add h3a (h3b.trans (mul_le_mul_of_nonneg_left hs hK0))
    _ = curvature K L₂ T ‖v‖ W * ‖e‖ ^ 2 := by rw [curvature]; ring

/-! ## Block contraction of a map with an explicit second-order remainder -/

section Block

variable {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ} {D : Matrix (Fin n) (Fin n) ℝ}
  {a c₂ ρ q δ : ℝ} {N : ℕ}

/-- **Block contraction.** Let a map `F` satisfy, on the ball `‖ξ − p‖ ≤ ρ`, the growth bound
`‖F(ξ) − p‖ ≤ a ‖ξ − p‖` and the second-order remainder `‖F(ξ) − p − D(ξ − p)‖ ≤ c₂ ‖ξ − p‖²`,
with `‖D e‖ ≤ a ‖e‖`, `a ≥ 1`, and let `‖D^N‖ ≤ q`. If `a^N δ ≤ ρ` and
`N c₂ a^{2N} δ ≤ (1 − q)/2`, every `ξ` with `‖ξ − p‖ ≤ δ` satisfies
`‖F^j(ξ) − p‖ ≤ a^j ‖ξ − p‖` for `j ≤ N` and `‖F^N(ξ) − p‖ ≤ ((1 + q)/2) ‖ξ − p‖`. -/
@[tmio T, powerlib_foundation] theorem block_contraction (ha : 1 ≤ a) (hc₂ : 0 ≤ c₂)
    (hD : ∀ e, ‖D *ᵥ e‖ ≤ a * ‖e‖) (hDN : ‖D ^ N‖ ≤ q)
    (hF : ∀ ξ, ‖ξ - p‖ ≤ ρ →
      ‖F ξ - p‖ ≤ a * ‖ξ - p‖ ∧ ‖F ξ - p - D *ᵥ (ξ - p)‖ ≤ c₂ * ‖ξ - p‖ ^ 2)
    (hδρ : a ^ N * δ ≤ ρ) (hδq : N * c₂ * a ^ (2 * N) * δ ≤ (1 - q) / 2)
    {ξ : Fin n → ℝ} (hξ : ‖ξ - p‖ ≤ δ) :
    (∀ j ≤ N, ‖F^[j] ξ - p‖ ≤ a ^ j * ‖ξ - p‖) ∧
      ‖F^[N] ξ - p‖ ≤ (1 + q) / 2 * ‖ξ - p‖ := by
  set d := ‖ξ - p‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have ha0 : 0 ≤ a := by linarith
  -- the growth along the block
  have hgrow : ∀ j ≤ N, ‖F^[j] ξ - p‖ ≤ a ^ j * d := by
    intro j
    induction j with
    | zero => intro _; simp [hd]
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      have hρ : ‖F^[j] ξ - p‖ ≤ ρ := by
        calc ‖F^[j] ξ - p‖ ≤ a ^ j * d := h
          _ ≤ a ^ N * δ := mul_le_mul (pow_le_pow_right₀ ha (by omega)) hξ hd0 (by positivity)
          _ ≤ ρ := hδρ
      rw [Function.iterate_succ_apply']
      calc ‖F (F^[j] ξ) - p‖ ≤ a * ‖F^[j] ξ - p‖ := (hF _ hρ).1
        _ ≤ a * (a ^ j * d) := mul_le_mul_of_nonneg_left h ha0
        _ = a ^ (j + 1) * d := by ring
  refine ⟨hgrow, ?_⟩
  -- the deviation from the linear iterates
  have hdev : ∀ j ≤ N, ‖F^[j] ξ - p - (D ^ j) *ᵥ (ξ - p)‖ ≤ j * c₂ * a ^ (2 * j) * d ^ 2 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      have hj' := hgrow j (by omega)
      have hρ : ‖F^[j] ξ - p‖ ≤ ρ := by
        calc ‖F^[j] ξ - p‖ ≤ a ^ j * d := hj'
          _ ≤ a ^ N * δ := mul_le_mul (pow_le_pow_right₀ ha (by omega)) hξ hd0 (by positivity)
          _ ≤ ρ := hδρ
      have hr := (hF _ hρ).2
      have he : F^[j + 1] ξ - p - (D ^ (j + 1)) *ᵥ (ξ - p) =
          (F (F^[j] ξ) - p - D *ᵥ (F^[j] ξ - p)) +
            D *ᵥ (F^[j] ξ - p - (D ^ j) *ᵥ (ξ - p)) := by
        rw [Function.iterate_succ_apply', pow_succ', ← mulVec_mulVec]
        simp only [mulVec_sub]
        abel
      rw [he]
      have hsq : ‖F^[j] ξ - p‖ ^ 2 ≤ (a ^ j * d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hj' 2
      have h1 : (1 : ℝ) ≤ a ^ 2 := one_le_pow₀ ha
      have hp0 : 0 ≤ a ^ (2 * j) := by positivity
      calc _ ≤ ‖F (F^[j] ξ) - p - D *ᵥ (F^[j] ξ - p)‖ +
            ‖D *ᵥ (F^[j] ξ - p - (D ^ j) *ᵥ (ξ - p))‖ := norm_add_le _ _
        _ ≤ c₂ * (a ^ j * d) ^ 2 + a * (j * c₂ * a ^ (2 * j) * d ^ 2) :=
            add_le_add (hr.trans (mul_le_mul_of_nonneg_left hsq hc₂))
              ((hD _).trans (mul_le_mul_of_nonneg_left h ha0))
        _ = c₂ * a ^ (2 * j) * d ^ 2 * (1 + j * a) := by ring
        _ ≤ c₂ * a ^ (2 * j) * d ^ 2 * ((j + 1) * a ^ 2) := by
            have hc : 0 ≤ c₂ * a ^ (2 * j) * d ^ 2 := by positivity
            refine mul_le_mul_of_nonneg_left ?_ hc
            have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            have haa : a ≤ a ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left haa hj0]
        _ = ((j + 1 : ℕ) : ℝ) * c₂ * a ^ (2 * (j + 1)) * d ^ 2 := by push_cast; ring
  have hN := hdev N le_rfl
  have hlin : ‖(D ^ N) *ᵥ (ξ - p)‖ ≤ q * d :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right hDN hd0)
  have hquad : (N : ℝ) * c₂ * a ^ (2 * N) * d ^ 2 ≤ (1 - q) / 2 * d := by
    have h1 : (N : ℝ) * c₂ * a ^ (2 * N) * d ≤ (1 - q) / 2 := by
      have : 0 ≤ (N : ℝ) * c₂ * a ^ (2 * N) := by positivity
      exact (mul_le_mul_of_nonneg_left hξ this).trans hδq
    nlinarith
  calc ‖F^[N] ξ - p‖ = ‖(D ^ N) *ᵥ (ξ - p) + (F^[N] ξ - p - (D ^ N) *ᵥ (ξ - p))‖ := by
        abel_nf
    _ ≤ ‖(D ^ N) *ᵥ (ξ - p)‖ + ‖F^[N] ξ - p - (D ^ N) *ᵥ (ξ - p)‖ := norm_add_le _ _
    _ ≤ q * d + (1 - q) / 2 * d := add_le_add hlin (hN.trans hquad)
    _ = (1 + q) / 2 * d := by ring

/-- **Geometric decay of the iterates.** Under the hypotheses of `block_contraction`, with
`N ≥ 1` and `q < 1`, every `ξ` with `‖ξ − p‖ ≤ δ` satisfies
`‖F^k(ξ) − p‖ ≤ a^N ((1 + q)/2)^{⌊k/N⌋} ‖ξ − p‖` for every `k`. -/
@[tmio T, powerlib_foundation] theorem iterate_contraction (ha : 1 ≤ a) (hc₂ : 0 ≤ c₂)
    (hD : ∀ e, ‖D *ᵥ e‖ ≤ a * ‖e‖) (hN : 1 ≤ N) (hDN : ‖D ^ N‖ ≤ q) (hq : q < 1)
    (hF : ∀ ξ, ‖ξ - p‖ ≤ ρ →
      ‖F ξ - p‖ ≤ a * ‖ξ - p‖ ∧ ‖F ξ - p - D *ᵥ (ξ - p)‖ ≤ c₂ * ‖ξ - p‖ ^ 2)
    (hδρ : a ^ N * δ ≤ ρ) (hδq : N * c₂ * a ^ (2 * N) * δ ≤ (1 - q) / 2)
    {ξ : Fin n → ℝ} (hξ : ‖ξ - p‖ ≤ δ) (k : ℕ) :
    ‖F^[k] ξ - p‖ ≤ a ^ N * ((1 + q) / 2) ^ (k / N) * ‖ξ - p‖ := by
  set d := ‖ξ - p‖ with hd
  set q' := (1 + q) / 2 with hq'
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hDN
  have hq'0 : 0 ≤ q' := by rw [hq']; linarith
  have hq'1 : q' ≤ 1 := by rw [hq']; linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  -- the block starts
  have hblock : ∀ m : ℕ, ‖F^[N * m] ξ - p‖ ≤ q' ^ m * d := by
    intro m
    induction m with
    | zero => simp [hd]
    | succ m ih =>
      have hm : ‖F^[N * m] ξ - p‖ ≤ δ :=
        ih.trans ((mul_le_of_le_one_left hd0 (pow_le_one₀ hq'0 hq'1)).trans hξ)
      have h := (block_contraction ha hc₂ hD hDN hF hδρ hδq hm).2
      rw [show N * (m + 1) = N + N * m by ring, Function.iterate_add_apply]
      calc ‖F^[N] (F^[N * m] ξ) - p‖ ≤ q' * ‖F^[N * m] ξ - p‖ := h
        _ ≤ q' * (q' ^ m * d) := mul_le_mul_of_nonneg_left ih hq'0
        _ = q' ^ (m + 1) * d := by ring
  have hNpos : 0 < N := hN
  have hm : ‖F^[N * (k / N)] ξ - p‖ ≤ δ :=
    (hblock _).trans ((mul_le_of_le_one_left hd0 (pow_le_one₀ hq'0 hq'1)).trans hξ)
  have hj := (block_contraction ha hc₂ hD hDN hF hδρ hδq hm).1 (k % N) (Nat.mod_lt k hNpos).le
  have hk : F^[k] ξ = F^[k % N] (F^[N * (k / N)] ξ) := by
    rw [← Function.iterate_add_apply, Nat.mod_add_div]
  rw [hk]
  calc ‖F^[k % N] (F^[N * (k / N)] ξ) - p‖ ≤ a ^ (k % N) * ‖F^[N * (k / N)] ξ - p‖ := hj
    _ ≤ a ^ N * (q' ^ (k / N) * d) :=
        mul_le_mul (pow_le_pow_right₀ ha (Nat.mod_lt k hNpos).le) (hblock _) (norm_nonneg _)
          (by positivity)
    _ = a ^ N * q' ^ (k / N) * d := by ring

end Block

/-! ## The asymptotic phase from geometrically converging samples -/

/-- **The asymptotic phase from the samples, with explicit constants.** Let `x` be a solution on
`[0, ∞)` of `ẋ = f(x)` and `F = PoincareSection.poincareMap hfK τ` for an arbitrary time map `τ`,
so that `F^k(x(0)) = x(t_k)`, `t_k = τ₀ + ⋯ + τ_{k−1}` (`AndronovWitt.iterate_poincareMap`). If
the samples converge geometrically, `‖F^k(x(0)) − p‖ ≤ C₁ ϑ^k d` (`p = x_*(0)`, `0 < ϑ < 1`), and
the times satisfy `T/2 ≤ τ_k ≤ c₀` and `|τ_k − T| ≤ L ‖F^k(x(0)) − p‖`, then the phase
`θ = −∑ₖ (τ_k − T)` satisfies `|θ| ≤ (L C₁/(1 − ϑ)) d` and
`‖x(t) − x_*(t + θ)‖ ≤ (e^{K c₀} (C₁ + B L C₁/(1 − ϑ))/ϑ) e^{−λt} d` with `λ = −log ϑ / c₀`. -/
@[tmio T, powerlib_foundation] theorem phase_of_samples (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ}
    (hper : Periodic xs T) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ a b, ‖xs a - xs b‖ ≤ B * |a - b|)
    (τ : (Fin n → ℝ) → ℝ) {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    {C₁ ϑ L c₀ d : ℝ} (hC₁ : 0 ≤ C₁) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hL0 : 0 ≤ L) (hd0 : 0 ≤ d)
    (hT : 0 < T)
    (hy : ∀ k : ℕ, ‖(poincareMap hfK τ)^[k] (x 0) - xs 0‖ ≤ C₁ * ϑ ^ k * d)
    (hτpos : ∀ k : ℕ, T / 2 ≤ τ ((poincareMap hfK τ)^[k] (x 0)))
    (hτup : ∀ k : ℕ, τ ((poincareMap hfK τ)^[k] (x 0)) ≤ c₀)
    (hτL : ∀ k : ℕ, |τ ((poincareMap hfK τ)^[k] (x 0)) - T| ≤
      L * ‖(poincareMap hfK τ)^[k] (x 0) - xs 0‖) :
    ∃ θ : ℝ, |θ| ≤ L * C₁ / (1 - ϑ) * d ∧ ∀ t, 0 ≤ t →
      ‖x t - xs (t + θ)‖ ≤ Real.exp (K * c₀) * (C₁ + B * (L * C₁ / (1 - ϑ))) / ϑ *
        Real.exp (-(-Real.log ϑ / c₀ * t)) * d := by
  set P := poincareMap hfK τ with hP
  set p := xs 0 with hp
  set ξ := x 0 with hξ
  have hc₀0 : 0 < c₀ := by have := hτpos 0; have := hτup 0; linarith
  set lam := -Real.log ϑ / c₀ with hlam
  have h1q : 0 < 1 - ϑ := by linarith
  set Cθ := L * C₁ / (1 - ϑ) with hCθ
  have hτT : ∀ k : ℕ, |τ (P^[k] ξ) - T| ≤ L * C₁ * d * ϑ ^ k := fun k => by
    refine (hτL k).trans ?_
    calc L * ‖P^[k] ξ - p‖ ≤ L * (C₁ * ϑ ^ k * d) := mul_le_mul_of_nonneg_left (hy k) hL0
      _ = L * C₁ * d * ϑ ^ k := by ring
  -- the accumulated return times
  set tt : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, τ (P^[j] ξ) with htt
  have htt_iter : ∀ k : ℕ, P^[k] ξ = x (tt k) := fun k =>
    iterate_poincareMap hfK τ hx k fun j _ => le_trans (by linarith) (hτpos j)
  have htt_succ : ∀ k : ℕ, tt (k + 1) = tt k + τ (P^[k] ξ) := fun k =>
    Finset.sum_range_succ _ _
  have htt_ge : ∀ k : ℕ, (k : ℝ) * (T / 2) ≤ tt k := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτpos k]
  have htt_le : ∀ k : ℕ, tt k ≤ k * c₀ := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτup k]
  -- the phase
  set u : ℕ → ℝ := fun j => τ (P^[j] ξ) - T with hu
  have hgeom : HasSum (fun j : ℕ => L * C₁ * d * ϑ ^ j) (L * C₁ * d * (1 - ϑ)⁻¹) :=
    (hasSum_geometric_of_lt_one hϑ0.le hϑ1).mul_left _
  have husum : Summable u :=
    Summable.of_norm_bounded hgeom.summable fun j => by rw [Real.norm_eq_abs]; exact hτT j
  set θ' := ∑' j, u j with hθ'
  have htail : ∀ k : ℕ, |tt k - k * T - θ'| ≤ Cθ * d * ϑ ^ k := fun k => by
    have hsplit := husum.sum_add_tsum_nat_add k
    have hsum : tt k - k * T = ∑ j ∈ Finset.range k, u j := by
      simp only [htt, hu, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have he : tt k - k * T - θ' = -∑' j, u (j + k) := by
      rw [hsum, hθ', ← hsplit]; ring
    rw [he, abs_neg]
    have hg : HasSum (fun j : ℕ => L * C₁ * d * ϑ ^ k * ϑ ^ j)
        (L * C₁ * d * ϑ ^ k * (1 - ϑ)⁻¹) :=
      (hasSum_geometric_of_lt_one hϑ0.le hϑ1).mul_left _
    have hb := tsum_of_norm_bounded hg fun j => by
      rw [Real.norm_eq_abs]
      calc |u (j + k)| ≤ L * C₁ * d * ϑ ^ (j + k) := hτT (j + k)
        _ = L * C₁ * d * ϑ ^ k * ϑ ^ j := by rw [pow_add]; ring
    rw [Real.norm_eq_abs] at hb
    calc |∑' j, u (j + k)| ≤ L * C₁ * d * ϑ ^ k * (1 - ϑ)⁻¹ := hb
      _ = Cθ * d * ϑ ^ k := by rw [hCθ]; field_simp
  refine ⟨-θ', ?_, fun t ht => ?_⟩
  · have h := htail 0
    simp only [htt, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, sub_zero,
      zero_sub, abs_neg, pow_zero, mul_one] at h
    rw [abs_neg]
    exact h
  -- the period containing `t`
  have hex : ∃ k : ℕ, t < tt (k + 1) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (t / (T / 2))
    refine ⟨k, lt_of_lt_of_le ?_ (htt_ge (k + 1))⟩
    rw [div_lt_iff₀ (by positivity)] at hk
    push_cast; nlinarith
  classical
  set k := Nat.find hex with hk
  have hk1 : t < tt (k + 1) := Nat.find_spec hex
  have hk0 : tt k ≤ t := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simpa [htt] using ht
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel hpos] at this
      exact not_lt.1 this
  -- Grönwall on `[t_k, t]`
  have hxs' : IsIntegralCurveOn (fun r => xs (r + -θ')) (fun _ => f) (Icc (tt k) t) :=
    fun r _ => ((hxs (r + -θ')).comp_add_const r (-θ')).hasDerivWithinAt
  have htk0 : 0 ≤ tt k := le_trans (by positivity) (htt_ge k)
  have hxI : IsIntegralCurveOn x (fun _ => f) (Icc (tt k) t) :=
    hx.mono fun q hq => mem_Ici.2 (htk0.trans hq.1)
  have hgr := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK) hxI hxs' t ⟨hk0, le_rfl⟩
  rw [dist_eq_norm, dist_eq_norm] at hgr
  -- the deviation at the crossing `t_k`
  have hdev : ‖x (tt k) - xs (tt k + -θ')‖ ≤ (C₁ + B * Cθ) * ϑ ^ k * d := by
    have hpk : xs (k * T) = p := hper.nat_mul_eq k
    calc ‖x (tt k) - xs (tt k + -θ')‖ = ‖(P^[k] ξ - p) + (xs (k * T) - xs (tt k + -θ'))‖ := by
          rw [htt_iter, hpk]; abel_nf
      _ ≤ ‖P^[k] ξ - p‖ + ‖xs (k * T) - xs (tt k + -θ')‖ := norm_add_le _ _
      _ ≤ C₁ * ϑ ^ k * d + B * |k * T - (tt k + -θ')| := add_le_add (hy k) (hB _ _)
      _ = C₁ * ϑ ^ k * d + B * |tt k - k * T - θ'| := by
          rw [abs_sub_comm]; ring_nf
      _ ≤ C₁ * ϑ ^ k * d + B * (Cθ * d * ϑ ^ k) := by gcongr; exact htail k
      _ = (C₁ + B * Cθ) * ϑ ^ k * d := by ring
  -- the rate
  have hqk : ϑ ^ k ≤ Real.exp (-(lam * t)) / ϑ := by
    rw [le_div_iff₀ hϑ0, ← pow_succ]
    have h1 : t ≤ (k + 1 : ℕ) * c₀ := (hk1.le.trans (htt_le (k + 1)))
    have h2 : Real.exp (-(lam * ((k + 1 : ℕ) * c₀))) = ϑ ^ (k + 1) := by
      rw [hlam, show -(-Real.log ϑ / c₀ * ((k + 1 : ℕ) * c₀)) = (k + 1 : ℕ) * Real.log ϑ by
        field_simp, Real.exp_nat_mul, Real.exp_log hϑ0]
    rw [← h2]
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith [Real.log_neg hϑ0 hϑ1]) hc₀0.le
    exact Real.exp_le_exp.2 (by nlinarith)
  have hgap : t - tt k ≤ c₀ := by
    have := htt_succ k; linarith [hτup k]
  have hC0 : 0 ≤ C₁ + B * Cθ := by positivity
  calc ‖x t - xs (t + -θ')‖ ≤ ‖x (tt k) - xs (tt k + -θ')‖ * Real.exp (K * (t - tt k)) := hgr
    _ ≤ (C₁ + B * Cθ) * ϑ ^ k * d * Real.exp (K * c₀) := by
        have he : Real.exp (K * (t - tt k)) ≤ Real.exp (K * c₀) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hgap K.2)
        exact mul_le_mul hdev he (Real.exp_pos _).le (by positivity)
    _ ≤ (C₁ + B * Cθ) * (Real.exp (-(lam * t)) / ϑ) * d * Real.exp (K * c₀) := by gcongr
    _ = Real.exp (K * c₀) * (C₁ + B * Cθ) / ϑ * Real.exp (-(lam * t)) * d := by
        field_simp

/-! ## The contraction datum and Schur stability -/

/-- **The contraction datum is Schur stability.** A real matrix `D` is Schur stable exactly when
some power is a contraction in the operator `L∞` norm: `‖D^N‖ < 1` for some `N ≥ 1`
(`LTI.exists_pow_norm_lt_one`, Gelfand's formula, in one direction; `|μ|^N ≤ ‖D^N‖` for every
eigenvalue `μ` in the other). So the contraction datum `‖D^N‖ ≤ q < 1` of
`asymptoticPhase_explicit` holds, for a suitable `N`, exactly under the hypothesis of
`AndronovWitt.andronov_witt`. -/
@[tmio T, powerlib_foundation] theorem schurStable_iff_exists_pow_norm_lt_one
    (D : Matrix (Fin n) (Fin n) ℝ) : LTI.SchurStable D ↔ ∃ N : ℕ, 1 ≤ N ∧ ‖D ^ N‖ < 1 := by
  constructor
  · intro h
    obtain ⟨N, hN, hlt⟩ :=
      LTI.exists_pow_norm_lt_one D ((LTI.schurStable_iff_spectralRadius_lt_one D).1 h)
    exact ⟨N, hN, hlt⟩
  · rintro ⟨N, hN, hlt⟩ μ v hv hμv
    set Dc := D.map (algebraMap ℝ ℂ) with hDc
    have hpow : ∀ k : ℕ, Dc ^ k *ᵥ v = μ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hμv, smul_smul, ← pow_succ]
    have hmap : (D ^ N).map (algebraMap ℝ ℂ) = Dc ^ N := by
      have h := map_pow ((algebraMap ℝ ℂ).mapMatrix (m := Fin n)) D N
      simpa [hDc, RingHom.mapMatrix_apply] using h
    have hnorm : ‖Dc ^ N‖ = ‖D ^ N‖ := by rw [← hmap, LTI.norm_map_algebraMap]
    have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 : ‖μ‖ ^ N * ‖v‖ ≤ ‖D ^ N‖ * ‖v‖ := by
      calc ‖μ‖ ^ N * ‖v‖ = ‖μ ^ N • v‖ := by rw [norm_smul, norm_pow]
        _ = ‖Dc ^ N *ᵥ v‖ := by rw [hpow]
        _ ≤ ‖Dc ^ N‖ * ‖v‖ := Matrix.linfty_opNorm_mulVec _ _
        _ = ‖D ^ N‖ * ‖v‖ := by rw [hnorm]
    have h2 : ‖μ‖ ^ N < 1 :=
      lt_of_le_of_lt (le_of_mul_le_mul_right h1 hv0) hlt
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h2

/-! ## The explicit constants: positivity and the conditions they meet -/

@[tmio T, powerlib_foundation] private theorem speed_nonneg {K T V : ℝ} (hV : 0 ≤ V) :
    0 ≤ speed K T V := by
  rw [speed]; positivity

@[tmio T, powerlib_foundation] private theorem one_le_growth {K T V W : ℝ} (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W) : 1 ≤ growth K T V W := by
  rw [growth]
  have h1 : 1 ≤ Real.exp (K * (3 * T / 2)) := Real.one_le_exp (by positivity)
  have h2 : 0 ≤ speed K T V * W := mul_nonneg (speed_nonneg hV) hW
  linarith

@[tmio T, powerlib_foundation] private theorem curvature_nonneg {K L₂ T V W : ℝ} (hK : 0 ≤ K)
    (hL₂ : 0 ≤ L₂) (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W) : 0 ≤ curvature K L₂ T V W := by
  rw [curvature]
  have := one_le_growth hK hT hV hW
  exact add_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith))

/-- The radius is positive: `0 < δ` for `T > 0`, `W > 0`, `q < 1` (and `K, L₂, V ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem radius_pos {K L₂ T V W q : ℝ} (N : ℕ) (hK : 0 ≤ K)
    (hL₂ : 0 ≤ L₂) (hT : 0 < T) (hV : 0 ≤ V) (hW : 0 < W) (hq : q < 1) :
    0 < radius K L₂ T V W N q := by
  have ha := one_le_growth hK hT.le hV hW.le
  have hc := curvature_nonneg hK hL₂ hT.le hV hW.le
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < W + N * T * curvature K L₂ T V W := by positivity
  have h3 : 0 < growth K T V W := by linarith
  rw [radius]
  positivity

/-- The rate is positive: `0 < λ` for `T > 0`, `N ≥ 1`, `−1 < q < 1`. -/
@[tmio T, powerlib_foundation] theorem rate_pos {T q : ℝ} {N : ℕ} (hT : 0 < T) (hN : 1 ≤ N)
    (hq0 : -1 < q) (hq : q < 1) : 0 < rate T N q := by
  rw [rate]
  have hlog : Real.log ((1 + q) / 2) < 0 := Real.log_neg (by linarith) (by linarith)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_pos (by linarith) (by positivity)

/-- The radius meets the two conditions of `block_contraction` with `ρ = T/(2W)`:
`a^N δ ≤ T/(2W)` and `N c₂ a^{2N} δ ≤ (1 − q)/2`. -/
@[tmio T, powerlib_foundation] private theorem radius_le {K L₂ T V W q : ℝ} {N : ℕ}
    (hK : 0 ≤ K) (hL₂ : 0 ≤ L₂) (hT : 0 < T) (hV : 0 ≤ V) (hW : 0 < W) (hq0 : 0 ≤ q)
    (hq : q < 1) :
    growth K T V W ^ N * radius K L₂ T V W N q ≤ T / (2 * W) ∧
      N * curvature K L₂ T V W * growth K T V W ^ (2 * N) * radius K L₂ T V W N q ≤
        (1 - q) / 2 := by
  have ha1 := one_le_growth hK hT.le hV hW.le
  have hc₂0 := curvature_nonneg hK hL₂ hT.le hV hW.le
  have hδ0 := (radius_pos N hK hL₂ hT hV hW hq).le
  set a := growth K T V W with ha
  set c₂ := curvature K L₂ T V W with hc₂
  set δ := radius K L₂ T V W N q with hδ
  set S := W + N * T * c₂ with hS
  have hNTc : 0 ≤ (N : ℝ) * T * c₂ := by positivity
  have hS0 : 0 < S := by positivity
  have hA1 : 1 ≤ a ^ (2 * N) := one_le_pow₀ ha1
  have haN : a ^ N ≤ a ^ (2 * N) := pow_le_pow_right₀ ha1 (by omega)
  have hδdef : δ = (1 - q) * T / (2 * a ^ (2 * N) * S) := rfl
  have hAδ : a ^ (2 * N) * δ = (1 - q) * T / (2 * S) := by
    rw [hδdef]; field_simp
  have h1q : 0 ≤ 1 - q := by linarith
  constructor
  · calc a ^ N * δ ≤ a ^ (2 * N) * δ := mul_le_mul_of_nonneg_right haN hδ0
      _ = (1 - q) * T / (2 * S) := hAδ
      _ ≤ T / (2 * W) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (1 - q) * W ≤ S := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h1 hT.le]
  · calc (N : ℝ) * c₂ * a ^ (2 * N) * δ = N * c₂ * (a ^ (2 * N) * δ) := by ring
      _ = (1 - q) * (N * T * c₂) / (2 * S) := by rw [hAδ]; ring
      _ ≤ (1 - q) / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_le_mul_of_nonneg_left (show N * T * c₂ ≤ S by linarith) h1q]

/-- The gain dominates the constants of `phase_of_samples` for the rate per step `ϑ`,
`ϑ^N = (1 + q)/2`: `W C₁/(1 − ϑ) ≤ C` and `e^{3KT/2} (C₁ + B W C₁/(1 − ϑ))/ϑ ≤ C`, by
Bernoulli's inequality `1 − ϑ^N ≤ N (1 − ϑ)` and `ϑ ≥ ϑ^N`. -/
@[tmio T, powerlib_foundation] private theorem gain_ge {K T V W q ϑ : ℝ} {N : ℕ} (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W) (hq0 : 0 ≤ q) (hq : q < 1) (hN : 1 ≤ N)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hϑN : ϑ ^ N = (1 + q) / 2) :
    W * sampleGain K T V W N q / (1 - ϑ) ≤ gain K T V W N q ∧
      Real.exp (K * (3 * T / 2)) * (sampleGain K T V W N q +
        speed K T V * (W * sampleGain K T V W N q / (1 - ϑ))) / ϑ ≤ gain K T V W N q := by
  have ha1 := one_le_growth hK hT hV hW
  have hB0 : 0 ≤ speed K T V := speed_nonneg hV
  set q' := (1 + q) / 2 with hq'
  have hq'0 : 0 < q' := by rw [hq']; linarith
  set a := growth K T V W with ha
  set B := speed K T V with hB
  set E := Real.exp (K * (3 * T / 2)) with hE
  set C₁ := sampleGain K T V W N q with hC₁
  have hC₁def : C₁ = a ^ N / q' := rfl
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁def]; have : 0 ≤ a := by linarith
                           positivity
  set Cθ := phaseGain K T V W N q with hCθ
  have hCθdef : Cθ = 2 * N * W * C₁ / (1 - q) := rfl
  have hgain : gain K T V W N q = E * (C₁ + (B + 1) * Cθ) / q' := rfl
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hq'ϑ : q' ≤ ϑ := hϑN ▸ pow_le_of_le_one hϑ0.le hϑ1.le (by omega)
  have hBern : (1 - q) / 2 ≤ N * (1 - ϑ) := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ ϑ - 1 by linarith) N
    rw [add_sub_cancel, hϑN] at h
    linarith
  have h1q : 0 < 1 - q := by linarith
  have h1ϑ : 0 < 1 - ϑ := by linarith
  have hθC : W * C₁ / (1 - ϑ) ≤ Cθ := by
    rw [hCθdef, div_le_div_iff₀ h1ϑ h1q]
    have : 0 ≤ W * C₁ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hBern this]
  have hCθ0 : 0 ≤ Cθ := le_trans (by positivity) hθC
  have hEq : 1 ≤ E / q' := by rw [le_div_iff₀ hq'0]; linarith
  constructor
  · rw [hgain]
    calc W * C₁ / (1 - ϑ) ≤ Cθ := hθC
      _ ≤ C₁ + (B + 1) * Cθ := by nlinarith
      _ ≤ E / q' * (C₁ + (B + 1) * Cθ) := le_mul_of_one_le_left (by positivity) hEq
      _ = E * (C₁ + (B + 1) * Cθ) / q' := by ring
  · rw [hgain]
    have h1 : C₁ + B * (W * C₁ / (1 - ϑ)) ≤ C₁ + (B + 1) * Cθ := by
      nlinarith [mul_le_mul_of_nonneg_left hθC hB0]
    have h2 : 0 ≤ C₁ + B * (W * C₁ / (1 - ϑ)) := by positivity
    calc E * (C₁ + B * (W * C₁ / (1 - ϑ))) / ϑ ≤ E * (C₁ + B * (W * C₁ / (1 - ϑ))) / q' :=
          div_le_div_of_nonneg_left (by positivity) hq'0 hq'ϑ
      _ ≤ E * (C₁ + (B + 1) * Cθ) / q' := by gcongr

@[tmio T, powerlib_foundation] private theorem gain_nonneg {K T V W q : ℝ} {N : ℕ} (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W) (hq0 : 0 ≤ q) (hq : q < 1) :
    0 ≤ gain K T V W N q := by
  have ha := one_le_growth hK hT hV hW
  have hB := speed_nonneg (K := K) (T := T) hV
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < (1 + q) / 2 := by linarith
  have h3 : 0 ≤ sampleGain K T V W N q := by
    rw [sampleGain]; have : 0 ≤ growth K T V W := by linarith
    positivity
  have h4 : 0 ≤ phaseGain K T V W N q := by rw [phaseGain]; positivity
  rw [gain]
  positivity

/-! ## The Andronov–Witt theorem with explicit constants -/

/-- **The Andronov–Witt theorem with explicit constants, from `x_*(0)`.** Let `x_*` be a
`T`-periodic solution of `ẋ = f(x)` on `ℝ^{Fin n}` (sup norm), `f` differentiable and globally
`K`-Lipschitz with `Df` globally `L₂`-Lipschitz, `p = x_*(0)`, `V = ‖f(p)‖`, `w ⬝ f(p) = 1`,
`W = ∑ᵢ |wᵢ|`, `M` the monodromy, and let the deflated monodromy `D = M − f(p) wᵀ` satisfy the
contraction datum `‖D^N‖ ≤ q < 1` for some `N ≥ 1`. Then every solution `x` on `[0, ∞)` with
`‖x(0) − p‖ ≤ δ`, `δ = radius = (1 − q) T / (2 a^{2N} (W + N T c₂))`, has an asymptotic phase
`θ`, `|θ| ≤ C ‖x(0) − p‖`, with `‖x(t) − x_*(t + θ)‖ ≤ C e^{−λt} ‖x(0) − p‖` for all `t ≥ 0`,
where `C = gain`, `λ = rate = −log((1 + q)/2)/(N · 3T/2)`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_explicit (hfd : Differentiable ℝ f)
    (hfK : LipschitzWith K f) (hL : LipschitzWith L₂ (fderiv ℝ f)) {xs : ℝ → Fin n → ℝ}
    (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T) (hper : Periodic xs T)
    {w : Fin n → ℝ} (hw : w ⬝ᵥ f (xs 0) = 1) {N : ℕ} (hN : 1 ≤ N) {q : ℝ} (hq : q < 1)
    (hDN : ‖(monodromy (variationalMatrix f xs) T 0 - vecMulVec (f (xs 0)) w) ^ N‖ ≤ q)
    {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    (hx0 : ‖x 0 - xs 0‖ ≤ radius K L₂ T ‖f (xs 0)‖ (∑ i, |w i|) N q) :
    ∃ θ : ℝ, |θ| ≤ gain K T ‖f (xs 0)‖ (∑ i, |w i|) N q * ‖x 0 - xs 0‖ ∧
      ∀ t, 0 ≤ t → ‖x t - xs (t + θ)‖ ≤
        gain K T ‖f (xs 0)‖ (∑ i, |w i|) N q * Real.exp (-(rate T N q * t)) * ‖x 0 - xs 0‖ := by
  have hf : ContDiff ℝ 1 f := contDiff_one_iff_fderiv.2 ⟨hfd, hL.continuous⟩
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  set p := xs 0 with hp
  set v := f p with hv
  set W := ∑ i, |w i| with hW
  set V := ‖v‖ with hV
  set a := growth K T V W with ha
  set c₂ := curvature K L₂ T V W with hc₂
  set B := speed K T V with hB
  set E := Real.exp (K * (3 * T / 2)) with hE
  set δ := radius K L₂ T V W N q with hδ
  set q' := (1 + q) / 2 with hq'
  set τ := returnTime T w p with hτ
  set F := poincareMap hfK τ with hF
  set ξ := x 0 with hξ
  set d := ‖ξ - p‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hDN
  have hq'0 : 0 < q' := by rw [hq']; linarith
  have hq'1 : q' < 1 := by rw [hq']; linarith
  have hN0 : 0 < N := hN
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hWV : 1 ≤ W * V := by
    have h := abs_dot_le w v
    rwa [hw, abs_one] at h
  have hWpos : 0 < W := by
    rcases hW0.eq_or_lt with h | h
    · rw [← h, zero_mul] at hWV; linarith
    · exact h
  have hV0 : 0 ≤ V := norm_nonneg _
  have hB0 : 0 ≤ B := speed_nonneg hV0
  have hET : Real.exp (K * T) ≤ E :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) K.2)
  have ha1 : 1 ≤ a := one_le_growth K.coe_nonneg hT.le hV0 hW0
  have hc₂0 : 0 ≤ c₂ := curvature_nonneg K.coe_nonneg L₂.coe_nonneg hT.le hV0 hW0
  -- the deflated monodromy grows at most by `a`
  have hD : ∀ e, ‖(monodromy (variationalMatrix f xs) T 0 - vecMulVec v w) *ᵥ e‖ ≤ a * ‖e‖ := by
    intro e
    rw [sub_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
    have hM := norm_monodromy_mulVec_le hf hfK hxc hT.le e
    have h1 : ‖(w ⬝ᵥ e) • v‖ ≤ W * ‖e‖ * V := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_dot_le w e) hV0
    have h2 : W * V ≤ B * W := by
      rw [hB, speed]
      have h := Real.one_le_exp (mul_nonneg K.2 hT.le)
      calc W * V = V * 1 * W := by ring
        _ ≤ V * Real.exp (K * T) * W :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hV0) hW0
    have he := norm_nonneg e
    calc _ ≤ ‖monodromy (variationalMatrix f xs) T 0 *ᵥ e‖ + ‖(w ⬝ᵥ e) • v‖ := norm_sub_le _ _
      _ ≤ Real.exp (K * T) * ‖e‖ + W * ‖e‖ * V := add_le_add hM h1
      _ ≤ E * ‖e‖ + B * W * ‖e‖ := by
          nlinarith [mul_le_mul_of_nonneg_right hET he, mul_le_mul_of_nonneg_right h2 he]
      _ = a * ‖e‖ := by rw [ha, growth, ← hE, ← hB]; ring
  -- the one-step bounds on the ball of radius `T/(2W)`
  have hstep : ∀ ζ, ‖ζ - p‖ ≤ T / (2 * W) →
      ‖F ζ - p‖ ≤ a * ‖ζ - p‖ ∧
        ‖F ζ - p - (monodromy (variationalMatrix f xs) T 0 - vecMulVec v w) *ᵥ (ζ - p)‖ ≤
          c₂ * ‖ζ - p‖ ^ 2 := fun ζ hζ => by
    have h : W * ‖ζ - p‖ ≤ T / 2 := by
      rw [le_div_iff₀ (by positivity)] at hζ
      linarith
    have h3 := step_bounds hfd hfK hL hxs hT hper w h
    exact ⟨h3.2.1, h3.2.2⟩
  obtain ⟨hδρ, hδq⟩ := radius_le (N := N) K.coe_nonneg L₂.coe_nonneg hT hV0 hWpos hq0 hq
  rw [← ha, ← hδ] at hδρ
  rw [← ha, ← hδ, ← hc₂] at hδq
  -- the iterates
  have hiter := iterate_contraction ha1 hc₂0 hD hN hDN hq hstep hδρ hδq hx0
  have hball : ∀ k : ℕ, ‖F^[k] ξ - p‖ ≤ a ^ N * d := fun k => by
    refine (hiter k).trans ?_
    have h1 : q' ^ (k / N) ≤ 1 := pow_le_one₀ hq'0.le hq'1.le
    have h2 : 0 ≤ a ^ N := by positivity
    calc a ^ N * q' ^ (k / N) * d ≤ a ^ N * 1 * d := by gcongr
      _ = a ^ N * d := by ring
  have hdom : ∀ k : ℕ, W * ‖F^[k] ξ - p‖ ≤ T / 2 := fun k => by
    have h1 : a ^ N * d ≤ a ^ N * δ := mul_le_mul_of_nonneg_left hx0 (by positivity)
    have h2 := hδρ
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith [mul_le_mul_of_nonneg_left ((hball k).trans h1) hW0]
  have hτT : ∀ k : ℕ, |τ (F^[k] ξ) - T| ≤ W * ‖F^[k] ξ - p‖ := fun k =>
    (step_bounds hfd hfK hL hxs hT hper w (hdom k)).1
  have hτpos : ∀ k : ℕ, T / 2 ≤ τ (F^[k] ξ) := fun k => by
    have := (abs_le.1 ((hτT k).trans (hdom k))).1; linarith
  have hτup : ∀ k : ℕ, τ (F^[k] ξ) ≤ 3 * T / 2 := fun k => by
    have := (abs_le.1 ((hτT k).trans (hdom k))).2; linarith
  -- the rate per step `ϑ = q'^{1/N}`
  set ϑ := Real.exp (Real.log q' / N) with hϑ
  have hϑ0 : 0 < ϑ := Real.exp_pos _
  have hlog : Real.log q' < 0 := Real.log_neg hq'0 hq'1
  have hϑ1 : ϑ < 1 := Real.exp_lt_one_iff.2 (div_neg_of_neg_of_pos hlog (by positivity))
  have hϑN : ϑ ^ N = q' := by
    rw [hϑ, ← Real.exp_nat_mul, show (N : ℝ) * (Real.log q' / N) = Real.log q' by field_simp,
      Real.exp_log hq'0]
  set C₁ := sampleGain K T V W N q with hC₁
  have hC₁def : C₁ = a ^ N / q' := rfl
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁def]; positivity
  have hy : ∀ k : ℕ, ‖F^[k] ξ - p‖ ≤ C₁ * ϑ ^ k * d := fun k => by
    refine (hiter k).trans ?_
    have hk : k ≤ N * (k / N + 1) := by
      have h1 := Nat.mod_add_div k N
      have h2 := Nat.mod_lt k hN0
      nlinarith
    have hpow : q' ^ (k / N) * q' ≤ ϑ ^ k := by
      rw [← pow_succ, ← hϑN, ← pow_mul]
      exact pow_le_pow_of_le_one hϑ0.le hϑ1.le hk
    have : q' ^ (k / N) ≤ ϑ ^ k / q' := by rw [le_div_iff₀ hq'0]; exact hpow
    calc a ^ N * q' ^ (k / N) * d ≤ a ^ N * (ϑ ^ k / q') * d := by gcongr
      _ = C₁ * ϑ ^ k * d := by rw [hC₁def]; ring
  obtain ⟨θ, hθ, hθt⟩ := phase_of_samples hfK hxs hper hB0
    (norm_sub_le_speed hfd hfK hxs hT hper) τ hx hC₁0 hϑ0 hϑ1 hW0 hd0 hT hy hτpos hτup hτT
  obtain ⟨hG1, hG2⟩ := gain_ge K.coe_nonneg hT.le hV0 hW0 hq0 hq hN hϑ0 hϑ1 hϑN
  have hrate : -Real.log ϑ / (3 * T / 2) = rate T N q := by
    rw [rate, hϑ, Real.log_exp, ← hq']
    field_simp
  refine ⟨θ, hθ.trans (mul_le_mul_of_nonneg_right hG1 hd0), fun t ht => ?_⟩
  refine (hθt t ht).trans ?_
  rw [hrate]
  have hexp : 0 ≤ Real.exp (-(rate T N q * t)) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG2 hexp) hd0

/-- **The Andronov–Witt theorem with explicit constants, uniformly along the orbit.** Under the
hypotheses of `asymptoticPhase_explicit`, every solution `x` on `[0, ∞)` with
`‖x(0) − x_*(σ)‖ ≤ δ'`, `δ' = orbitRadius = δ e^{−KT}`, for any point `x_*(σ)` of the orbit, has an
asymptotic phase `θ`, `|θ| ≤ C' ‖x(0) − x_*(σ)‖`, with
`‖x(t) − x_*(t + σ + θ)‖ ≤ C' e^{−λt} ‖x(0) − x_*(σ)‖` for `t ≥ 0`, where
`C' = orbitGain = (1 + (1 + B) C) e^{KT} e^{λT}`, `B = ‖f(p)‖ e^{KT}`, and `C`, `λ` are those of
`asymptoticPhase_explicit`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_uniform_explicit
    (hfd : Differentiable ℝ f) (hfK : LipschitzWith K f) (hL : LipschitzWith L₂ (fderiv ℝ f))
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {w : Fin n → ℝ} (hw : w ⬝ᵥ f (xs 0) = 1) {N : ℕ} (hN : 1 ≤ N)
    {q : ℝ} (hq : q < 1)
    (hDN : ‖(monodromy (variationalMatrix f xs) T 0 - vecMulVec (f (xs 0)) w) ^ N‖ ≤ q)
    (σ : ℝ) {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    (hx0 : ‖x 0 - xs σ‖ ≤ orbitRadius K L₂ T ‖f (xs 0)‖ (∑ i, |w i|) N q) :
    ∃ θ : ℝ, |θ| ≤ orbitGain K T ‖f (xs 0)‖ (∑ i, |w i|) N q * ‖x 0 - xs σ‖ ∧
      ∀ t, 0 ≤ t → ‖x t - xs (t + σ + θ)‖ ≤ orbitGain K T ‖f (xs 0)‖ (∑ i, |w i|) N q *
        Real.exp (-(rate T N q * t)) * ‖x 0 - xs σ‖ := by
  set V := ‖f (xs 0)‖ with hV
  set W := ∑ i, |w i| with hW
  set C₀ := gain K T V W N q with hC₀def
  set lam := rate T N q with hlamdef
  set B := speed K T V with hBdef
  set δ₀ := radius K L₂ T V W N q with hδ₀
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hDN
  have hV0 : 0 ≤ V := norm_nonneg _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hC₀ : 0 ≤ C₀ := gain_nonneg K.coe_nonneg hT.le hV0 hW0 hq0 hq
  have hlam : 0 < lam := rate_pos hT hN (by linarith) hq
  have hB0 : 0 ≤ B := speed_nonneg hV0
  have hB := norm_sub_le_speed hfd hfK hxs hT hper
  have hmain := fun {y : ℝ → Fin n → ℝ} (hy : IsIntegralCurveOn y (fun _ => f) (Ici 0))
      (hy0 : ‖y 0 - xs 0‖ ≤ δ₀) =>
    asymptoticPhase_explicit hfd hfK hL hxs hT hper hw hN hq hDN hy hy0
  set E := Real.exp (K * T) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg K.2 hT.le)
  have hE0 : 0 < E := by linarith
  set F := Real.exp (lam * T) with hF
  have hF1 : 1 ≤ F := Real.one_le_exp (mul_nonneg hlam.le hT.le)
  set C := orbitGain K T V W N q with hC
  have hCdef : C = (1 + (1 + B) * C₀) * E * F := rfl
  set d₀ := ‖x 0 - xs σ‖ with hd₀
  have hd0 : 0 ≤ d₀ := norm_nonneg _
  have hx0' : d₀ ≤ δ₀ / E := hx0
  -- the phase of `σ` in `[0, T)`
  set σ' := toIcoMod hT 0 σ with hσ'
  have hσ'I : σ' ∈ Ico 0 T := by simpa using toIcoMod_mem_Ico hT 0 σ
  have hshift : ∀ a, xs (a + σ) = xs (a + σ') := fun a => by
    have h := toIcoMod_add_toIcoDiv_zsmul hT 0 σ
    rw [← h, ← add_assoc]
    exact (hper.zsmul _) _
  set u := T - σ' with hu
  have hu0 : 0 < u := by have := hσ'I.2; linarith
  have huT : u ≤ T := by have := hσ'I.1; linarith
  -- up to the time `u` the solution follows `x_*(· + σ')`
  have hxs' : ∀ a b : ℝ, IsIntegralCurveOn (fun r => xs (r + σ')) (fun _ => f) (Icc a b) :=
    fun _ _ r _ => ((hxs (r + σ')).comp_add_const r σ').hasDerivWithinAt
  have hfollow : ∀ r ∈ Icc 0 u, ‖x r - xs (r + σ')‖ ≤ E * d₀ := fun r hr => by
    have h := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK)
      (hx.mono fun q hq => mem_Ici.2 hq.1) (hxs' 0 u) r hr
    have hσσ' : xs σ = xs σ' := by have := hshift 0; rwa [zero_add, zero_add] at this
    rw [dist_eq_norm, dist_eq_norm, zero_add, ← hσσ', sub_zero] at h
    rw [mul_comm] at h
    refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hd0)
    exact mul_le_mul_of_nonneg_left (hr.2.trans huT) K.2
  have hxu : ‖x u - xs 0‖ ≤ E * d₀ := by
    have h := hfollow u ⟨hu0.le, le_rfl⟩
    rwa [hu, sub_add_cancel, show xs T = xs 0 by simpa using hper 0] at h
  -- from the time `u` on, the phase of `asymptoticPhase_explicit`
  set y : ℝ → Fin n → ℝ := fun r => x (r + u) with hy
  have hyI : IsIntegralCurveOn y (fun _ => f) (Ici 0) :=
    (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
      (Ici_subset_Ici.2 (by linarith))
  have hy0' : ‖y 0 - xs 0‖ ≤ E * d₀ := by simpa [hy] using hxu
  have hy0 : ‖y 0 - xs 0‖ ≤ δ₀ := by
    refine hy0'.trans ?_
    calc E * d₀ ≤ E * (δ₀ / E) := mul_le_mul_of_nonneg_left hx0' hE0.le
      _ = δ₀ := by field_simp
  obtain ⟨θ, hθ, hyθ⟩ := hmain hyI hy0
  have hθd : |θ| ≤ C₀ * E * d₀ :=
    hθ.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hy0' hC₀)
  have hθC : |θ| ≤ C * d₀ := by
    refine hθd.trans (mul_le_mul_of_nonneg_right ?_ hd0)
    rw [hCdef]
    have h1 : C₀ ≤ 1 + (1 + B) * C₀ := by
      have : (1 + B) * C₀ = C₀ + B * C₀ := by ring
      have := mul_nonneg hB0 hC₀
      linarith
    have h2 : C₀ * E ≤ (1 + (1 + B) * C₀) * E := mul_le_mul_of_nonneg_right h1 hE0.le
    have h3 : 0 ≤ (1 + (1 + B) * C₀) * E := by positivity
    calc C₀ * E ≤ (1 + (1 + B) * C₀) * E := h2
      _ = (1 + (1 + B) * C₀) * E * 1 := (mul_one _).symm
      _ ≤ (1 + (1 + B) * C₀) * E * F := mul_le_mul_of_nonneg_left hF1 h3
  refine ⟨θ, hθC, fun t ht => ?_⟩
  have hphase : xs (t + σ + θ) = xs (t + θ + σ') := by
    rw [show t + σ + θ = (t + θ) + σ by ring, hshift]
  rw [hphase]
  rcases le_or_gt u t with hut | htu
  · -- after the time `u`
    have h := hyθ (t - u) (by linarith)
    simp only [hy, sub_add_cancel] at h
    have hper' : xs (t - u + θ) = xs (t + θ + σ') := by
      rw [hu, show t - (T - σ') + θ = (t + θ + σ') - T by ring]
      exact hper.sub_eq _
    rw [hper'] at h
    refine h.trans ?_
    have hexp : Real.exp (-(lam * (t - u))) ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      have : lam * u ≤ lam * T := mul_le_mul_of_nonneg_left huT hlam.le
      exact Real.exp_le_exp.2 (by linarith)
    calc C₀ * Real.exp (-(lam * (t - u))) * ‖y 0 - xs 0‖
        ≤ C₀ * (F * Real.exp (-(lam * t))) * (E * d₀) := by gcongr
      _ = C₀ * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ C * Real.exp (-(lam * t)) * d₀ := by
          have h1 : C₀ ≤ 1 + (1 + B) * C₀ := by
            have : (1 + B) * C₀ = C₀ + B * C₀ := by ring
            have := mul_nonneg hB0 hC₀
            linarith
          have hk : C₀ * E * F ≤ C := by
            rw [hCdef]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hE0.le) (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le) hd0
  · -- before the time `u`
    have h1 := hfollow t ⟨ht, htu.le⟩
    have h2 : ‖xs (t + σ') - xs (t + θ + σ')‖ ≤ B * |θ| := by
      refine (hB _ _).trans_eq ?_
      congr 1
      rw [show t + σ' - (t + θ + σ') = -θ by ring, abs_neg]
    have hexp : 1 ≤ F * Real.exp (-(lam * t)) := by
      rw [hF, ← Real.exp_add]
      have : lam * t ≤ lam * T := mul_le_mul_of_nonneg_left (by linarith) hlam.le
      exact Real.one_le_exp (by linarith)
    calc ‖x t - xs (t + θ + σ')‖ = ‖(x t - xs (t + σ')) + (xs (t + σ') - xs (t + θ + σ'))‖ := by
          abel_nf
      _ ≤ ‖x t - xs (t + σ')‖ + ‖xs (t + σ') - xs (t + θ + σ')‖ := norm_add_le _ _
      _ ≤ E * d₀ + B * (C₀ * E * d₀) := add_le_add h1 (h2.trans (by gcongr))
      _ = (1 + B * C₀) * E * d₀ * 1 := by ring
      _ ≤ (1 + B * C₀) * E * d₀ * (F * Real.exp (-(lam * t))) := by gcongr
      _ = (1 + B * C₀) * E * F * Real.exp (-(lam * t)) * d₀ := by ring
      _ ≤ C * Real.exp (-(lam * t)) * d₀ := by
          have h1 : 1 + B * C₀ ≤ 1 + (1 + B) * C₀ := by
            have : (1 + B) * C₀ = C₀ + B * C₀ := by ring
            linarith
          have hk : (1 + B * C₀) * E * F ≤ C := by
            rw [hCdef]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hE0.le) (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le) hd0

/-- **Orbital exponential stability with explicit constants.** Under the hypotheses of
`asymptoticPhase_explicit`, every solution `x` on `[0, ∞)` with `dist(x(0), x_*(ℝ)) ≤ δ'` satisfies
`dist(x(t), x_*(ℝ)) ≤ C' e^{−λt} dist(x(0), x_*(ℝ))` for `t ≥ 0` (`Metric.infDist` to the range
of `x_*`), with `δ' = orbitRadius`, `C' = orbitGain`, `λ = rate`. -/
@[tmio T, powerlib_foundation] theorem infDist_orbit_le_explicit
    (hfd : Differentiable ℝ f) (hfK : LipschitzWith K f) (hL : LipschitzWith L₂ (fderiv ℝ f))
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {w : Fin n → ℝ} (hw : w ⬝ᵥ f (xs 0) = 1) {N : ℕ} (hN : 1 ≤ N)
    {q : ℝ} (hq : q < 1)
    (hDN : ‖(monodromy (variationalMatrix f xs) T 0 - vecMulVec (f (xs 0)) w) ^ N‖ ≤ q)
    {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    (hx0 : Metric.infDist (x 0) (range xs) ≤ orbitRadius K L₂ T ‖f (xs 0)‖ (∑ i, |w i|) N q)
    (t : ℝ) (ht : 0 ≤ t) :
    Metric.infDist (x t) (range xs) ≤ orbitGain K T ‖f (xs 0)‖ (∑ i, |w i|) N q *
      Real.exp (-(rate T N q * t)) * Metric.infDist (x 0) (range xs) := by
  have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ :=
    (hper.compact_of_continuous hT.ne' hxc).exists_infDist_eq_dist (range_nonempty xs) (x 0)
  rw [dist_eq_norm] at hσ
  obtain ⟨θ, -, hθ⟩ :=
    asymptoticPhase_uniform_explicit hfd hfK hL hxs hT hper hw hN hq hDN σ hx (hσ ▸ hx0)
  rw [hσ]
  calc Metric.infDist (x t) (range xs) ≤ dist (x t) (xs (t + σ + θ)) :=
        Metric.infDist_le_dist_of_mem (mem_range_self _)
    _ = ‖x t - xs (t + σ + θ)‖ := dist_eq_norm _ _
    _ ≤ _ := hθ t ht

/-- **The Andronov–Witt theorem with explicit constants.** Let `x_*` be a `T`-periodic solution of
`ẋ = f(x)` on `ℝ^{Fin n}` (sup norm), `f` differentiable and globally `K`-Lipschitz with `Df`
globally `L₂`-Lipschitz, `p = x_*(0)`, `w ⬝ f(p) = 1`, and let the deflated monodromy
`D = M − f(p) wᵀ` satisfy `‖D^N‖ ≤ q < 1` for some `N ≥ 1`. Then the explicit radius `δ'`
(`orbitRadius`) and rate `λ = −log((1 + q)/2)/(N · 3T/2)` (`rate`) are positive, every solution
starting within `δ'` of a point `x_*(σ)` has an asymptotic phase `θ` with
`|θ| ≤ C' ‖x(0) − x_*(σ)‖` and `‖x(t) − x_*(t + σ + θ)‖ ≤ C' e^{−λt} ‖x(0) − x_*(σ)‖`, and every
solution starting within `δ'` of the orbit satisfies
`dist(x(t), x_*(ℝ)) ≤ C' e^{−λt} dist(x(0), x_*(ℝ))`, with the explicit gain `C'` (`orbitGain`). -/
@[tmio T, powerlib_foundation] theorem andronov_witt_explicit
    (hfd : Differentiable ℝ f) (hfK : LipschitzWith K f) (hL : LipschitzWith L₂ (fderiv ℝ f))
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {w : Fin n → ℝ} (hw : w ⬝ᵥ f (xs 0) = 1) {N : ℕ} (hN : 1 ≤ N)
    {q : ℝ} (hq : q < 1)
    (hDN : ‖(monodromy (variationalMatrix f xs) T 0 - vecMulVec (f (xs 0)) w) ^ N‖ ≤ q) :
    0 < orbitRadius K L₂ T ‖f (xs 0)‖ (∑ i, |w i|) N q ∧ 0 < rate T N q ∧
    (∀ (σ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      ‖x 0 - xs σ‖ ≤ orbitRadius K L₂ T ‖f (xs 0)‖ (∑ i, |w i|) N q →
      ∃ θ : ℝ, |θ| ≤ orbitGain K T ‖f (xs 0)‖ (∑ i, |w i|) N q * ‖x 0 - xs σ‖ ∧
        ∀ t, 0 ≤ t → ‖x t - xs (t + σ + θ)‖ ≤ orbitGain K T ‖f (xs 0)‖ (∑ i, |w i|) N q *
          Real.exp (-(rate T N q * t)) * ‖x 0 - xs σ‖) ∧
    ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      Metric.infDist (x 0) (range xs) ≤ orbitRadius K L₂ T ‖f (xs 0)‖ (∑ i, |w i|) N q →
      ∀ t, 0 ≤ t → Metric.infDist (x t) (range xs) ≤
        orbitGain K T ‖f (xs 0)‖ (∑ i, |w i|) N q * Real.exp (-(rate T N q * t)) *
          Metric.infDist (x 0) (range xs) := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hDN
  have hW0 : 0 ≤ ∑ i, |w i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hWV : 1 ≤ (∑ i, |w i|) * ‖f (xs 0)‖ := by
    have h := abs_dot_le w (f (xs 0))
    rwa [hw, abs_one] at h
  have hWpos : 0 < ∑ i, |w i| := by
    rcases hW0.eq_or_lt with h | h
    · rw [← h, zero_mul] at hWV; linarith
    · exact h
  refine ⟨div_pos (radius_pos N K.coe_nonneg L₂.coe_nonneg hT (norm_nonneg _) hWpos hq)
      (Real.exp_pos _), rate_pos hT hN (by linarith) hq,
    fun σ x hx hx0 => asymptoticPhase_uniform_explicit hfd hfK hL hxs hT hper hw hN hq hDN σ hx hx0,
    fun x hx hx0 t ht => infDist_orbit_le_explicit hfd hfK hL hxs hT hper hw hN hq hDN hx hx0 t ht⟩

end powerlib.Periodic.AndronovWittQuantitative
