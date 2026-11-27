import theorem.ParametricResonance.ComplexPumpAveraging
import theorem.ParametricResonance.FirstOrderAveragingFails

/-! # First-order averaging fails: existence of the solutions it is stated for

`FirstOrderFails.first_order_fails` (first-order averaging misses the quadratic stiffness on the
time scale `1/ε`) assumes, as `QuadraticCubic.second_order_averaging` does, a solution `x` of the
oscillator `ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u` defined on all of `ℝ`, and the
first- and second-order averaged amplitudes `W₁`, `W₂` given on `[0, L/ε]` inside the disc of
radius `R`. These hypotheses are discharged here.
* The averaged fields: a solution of the cubic amplitude equation moves at speed at most
  `εM`, `M = ampBound … R`, while it is in the disc of radius `R`, so it stays there up to the
  explicit escape time `L < (R − |W(0)|)/M` (`norm_lt_of_speed`, `norm_lt_of_escape`), and such
  solutions exist (`exists_averaged_solution`: the clamped field is globally Lipschitz and its
  global solution never meets the clamp before the escape time).
* The oscillator: the polynomial field read through a clip `[−ρ, ρ]` of the position
  (`cutOsc`) is globally Lipschitz (`lipschitzWith_cutOsc`), so it has a global solution
  (`DuffingMathieu.exists_global_solution`); for `ρ = 2(R + 1)` the clip is inactive while the
  scaled amplitude is in the disc `2(R + 1)`, so this solution solves the true oscillator with an
  input that equals `u` there, and the a-priori bound of `ComplexPump.second_order_from` keeps it
  in that disc on `[0, L/ε]`. Every solution on `[0, L/ε]` from the same initial state is this
  one (uniqueness for the field clipped at a radius above both, Mathlib's
  `ODE_solution_unique_of_mem_Icc_right`).
Hence first-order averaging fails for the solution of every initial state with the escape and
smallness conditions (`first_order_fails_solution`, `first_order_fails_initial`).

Scope.
* The oscillator, scaling and constants of `FirstOrderFails.first_order_fails` (`ν > 0`,
  `0 < ε ≤ 1`, `R, L ≥ 0`, the branch condition, `errSecond … < 1`, `L/ε ≥ π/(2ν)`), with a
  continuous input `u(t)`, `|u| ≤ ε²M_u` on `[0, L/ε]` (a function of time only), an arbitrary
  initial state `(x₀, v₀)` at `t = 0`, solutions on the window `[0, L/ε]` with one-sided
  derivatives at its ends; continuous time, state `(x, ẋ) ∈ ℝ × ℝ`.
* The escape conditions `|W_i(0)| + L M_i < R` replace the disc hypotheses; they hold for `L`
  small against `(R − |W_i(0)|)/M_i`, which is also the regime where `FirstOrderFails.failConst`
  is positive (`FirstOrderFails.failConst_pos`).
* Generic mathematics, no model family.

Source: the failure of first-order averaging `FirstOrderFails.first_order_fails` and the bounds
`FirstOrderFails.norm_ampField_le`, `FirstOrderFails.norm_ampField_sub_le`
(`theorem/ParametricResonance/FirstOrderAveragingFails.lean`); the a-priori bound of
second-order averaging `ComplexPump.second_order_from`
(`theorem/ParametricResonance/ComplexPumpAveraging.lean`); the clamp and the global solutions
`DuffingMathieu.clampC`, `DuffingMathieu.exists_global_solution`; Mathlib's
`norm_image_sub_le_of_norm_deriv_le_segment'` and `ODE_solution_unique_of_mem_Icc_right`;
existence on bounded sets by a cut-off (Hale, *Ordinary Differential Equations*, Ch. I;
Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*, Ch. 2).

Results.
* `norm_lt_of_speed`, `norm_lt_of_escape` — first exit at bounded speed; an averaged solution
  stays in the disc `R` while `|W(0)| + εtM < R`.
* `exists_averaged_solution` — the cubic amplitude equation has a solution up to the escape time.
* `clip`, `clip_of_abs_le`, `abs_clip_le`, `abs_clip_sub_le`, `continuous_clip` — the clip onto
  `[−ρ, ρ]`.
* `cutOsc`, `cutOsc_of_abs_le`, `lipschitzWith_cutOsc`, `continuous_cutOsc` — the cut-off
  oscillator, equal to the oscillator on `|x| ≤ ρ`, globally Lipschitz, continuous.
* `first_order_fails_solution` — the oscillator has a solution on `[0, L/ε]` from `(x₀, v₀)`, and
  for every such solution `|x(t) − √ε Re(W₁(t) e^{jνt})| ≥ √ε (failConst − failErr)` at some
  `t ∈ [0, L/ε]`, for every pair of averaged solutions below the escape times.
* `first_order_fails_initial` — the same from the initial state alone: `W₁`, `W₂` and the
  solution exist, and every solution fails first-order averaging.
-/

noncomputable section
namespace powerlib.ParametricResonance.FirstOrderFailsExistence

open Complex Set
open DuffingMathieu (vdp accel)
open QuadraticCubic (phase nearId errSecond)
open Saturation (ampField)
open FirstOrderFails (ampBound failConst failErr)

/-! ## Averaged solutions stay in a disc up to an explicit escape time -/

/-- **First exit from a disc at bounded speed.** A curve on `[0, T]` in a normed space whose
speed is at most `C` while it is in the open disc of radius `R` stays in that disc as long as
`|W(0)| + CT < R`. (At the first time with `|W| ≥ R` the speed has been at most `C` before, so
`|W| ≤ |W(0)| + Ct < R` there.) -/
@[tmio T, powerlib_foundation] theorem norm_lt_of_speed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T R C : ℝ} {W W' : ℝ → E}
    (hW : ∀ t ∈ Icc 0 T, HasDerivWithinAt W (W' t) (Icc 0 T) t)
    (hC : ∀ t ∈ Icc 0 T, ‖W t‖ < R → ‖W' t‖ ≤ C) (hC0 : 0 ≤ C) (h0 : ‖W 0‖ + C * T < R) :
    ∀ t ∈ Icc 0 T, ‖W t‖ < R := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hsR⟩ := hcon
  have hcW : ContinuousOn W (Icc 0 T) := fun t ht => (hW t ht).continuousWithinAt
  set A := Icc 0 T ∩ (fun t => ‖W t‖) ⁻¹' Ici R with hA
  have hAc : IsClosed A := hcW.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hAne : A.Nonempty := ⟨s, hs, hsR⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set t₀ := sInf A with ht₀
  have ht₀A : t₀ ∈ A := hAc.csInf_mem hAne hAbdd
  have hbefore : ∀ t ∈ Ico 0 t₀, ‖W t‖ < R := by
    intro t ht
    by_contra hge
    push Not at hge
    have : t₀ ≤ t := csInf_le hAbdd ⟨⟨ht.1, ht.2.le.trans ht₀A.1.2⟩, hge⟩
    linarith [ht.2]
  have hsub : Icc 0 t₀ ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht₀A.1.2
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := W) (C := C)
    (fun y hy => (hW y (hsub hy)).mono hsub)
    (fun y hy => hC y (hsub (Ico_subset_Icc_self hy)) (hbefore y hy)) t₀ ⟨ht₀A.1.1, le_rfl⟩
  rw [sub_zero] at hmv
  have h1 : C * t₀ ≤ C * T := mul_le_mul_of_nonneg_left ht₀A.1.2 hC0
  have h2 := norm_le_norm_add_norm_sub' (W t₀) (W 0)
  have h3 : R ≤ ‖W t₀‖ := ht₀A.2
  linarith

variable {σ Δ β : ℝ} {c : ℂ}

/-- **An explicit escape time for the cubic amplitude equation.** A solution of
`Ẇ = ε ampField σ Δ c 0 β W` on `[0, T]` with `|W(0)| + εT M < R`, `M = ampBound σ Δ |c| β R` the
bound of the field on the disc of radius `R` (`FirstOrderFails.norm_ampField_le`), stays in the
open disc: `|W(t)| < R` on `[0, T]`. In the slow time `εT = L` this is the escape-time bound
`L < (R − |W(0)|)/M` (`norm_lt_of_speed`). -/
@[tmio T, powerlib_foundation] theorem norm_lt_of_escape {ε T R : ℝ} (hε : 0 ≤ ε) (hR : 0 ≤ R)
    {W : ℝ → ℂ}
    (hW : ∀ t ∈ Icc 0 T, HasDerivWithinAt W (ε • ampField σ Δ c 0 β (W t)) (Icc 0 T) t)
    (h0 : ‖W 0‖ + ε * T * ampBound σ Δ ‖c‖ β R < R) : ∀ t ∈ Icc 0 T, ‖W t‖ < R := by
  have hM : 0 ≤ ampBound σ Δ ‖c‖ β R := by unfold ampBound; positivity
  refine norm_lt_of_speed hW (fun t _ ht => ?_) (mul_nonneg hε hM)
    (by linarith [show ε * T * ampBound σ Δ ‖c‖ β R = ε * ampBound σ Δ ‖c‖ β R * T by ring])
  rw [norm_smul, Real.norm_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (FirstOrderFails.norm_ampField_le ht.le) hε

/-- **Averaged solutions exist up to the escape time.** From every `W₀` with
`|W₀| + εT M < R` (`M = ampBound σ Δ |c| β R`, `ε, R ≥ 0`) the cubic amplitude equation
`Ẇ = ε ampField σ Δ c 0 β W` has a solution on `[0, T]`, and it stays in the open disc of radius
`R` (the field clamped onto the square of half-side `R`, `DuffingMathieu.clampC`, is globally
Lipschitz; its global solution, `DuffingMathieu.exists_global_solution`, never meets the clamp
before the escape time, `norm_lt_of_speed`). -/
@[tmio T, powerlib_foundation] theorem exists_averaged_solution {ε T R : ℝ} (hε : 0 ≤ ε)
    (hR : 0 ≤ R) {W₀ : ℂ} (h0 : ‖W₀‖ + ε * T * ampBound σ Δ ‖c‖ β R < R) :
    ∃ W : ℝ → ℂ, W 0 = W₀ ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt W (ε • ampField σ Δ c 0 β (W t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ‖W t‖ < R := by
  have hM : 0 ≤ ampBound σ Δ ‖c‖ β R := by unfold ampBound; positivity
  have h2R : 0 ≤ 2 * R := by positivity
  have hℓ : 0 ≤ FirstOrderFails.ampLip σ Δ ‖c‖ β (2 * R) := by
    unfold FirstOrderFails.ampLip; positivity
  set g : ℂ → ℂ := fun V => ε • ampField σ Δ c 0 β (DuffingMathieu.clampC R V) with hg
  have hlip : LipschitzWith (Real.toNNReal (ε * FirstOrderFails.ampLip σ Δ ‖c‖ β (2 * R))) g := by
    refine LipschitzWith.of_dist_le_mul fun V V' => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hε hℓ), hg, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hε, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hε
    exact (FirstOrderFails.norm_ampField_sub_le (DuffingMathieu.norm_clampC_le hR V)
      (DuffingMathieu.norm_clampC_le hR V')).trans
      (mul_le_mul_of_nonneg_left (DuffingMathieu.norm_clampC_sub_le R V V') hℓ)
  have hcont : Continuous (Function.uncurry fun (_ : ℝ) (V : ℂ) => g V) :=
    hlip.continuous.comp continuous_snd
  obtain ⟨W, hW0, hW⟩ := DuffingMathieu.exists_global_solution hcont (fun _ => hlip) W₀
  have hin : ∀ t ∈ Icc 0 T, ‖W t‖ < R := by
    refine norm_lt_of_speed (W' := fun t => g (W t)) (fun t _ => (hW t).hasDerivWithinAt)
      (fun t _ ht => ?_) (mul_nonneg hε hM)
      (by rw [hW0]; linarith [show ε * T * ampBound σ Δ ‖c‖ β R =
        ε * ampBound σ Δ ‖c‖ β R * T by ring])
    simp only [hg, DuffingMathieu.clampC_of_norm_le ht.le, norm_smul, Real.norm_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (FirstOrderFails.norm_ampField_le ht.le) hε
  refine ⟨W, hW0, fun t ht => ?_, hin⟩
  have h := (hW t).hasDerivWithinAt (s := Icc 0 T)
  simp only [hg, DuffingMathieu.clampC_of_norm_le (hin t ht).le] at h
  exact h

/-! ## The cut-off oscillator and its global solutions -/

/-- The clip of a real number onto `[−ρ, ρ]`. -/
def clip (ρ x : ℝ) : ℝ := max (-ρ) (min ρ x)

@[tmio T, powerlib_foundation] theorem clip_of_abs_le {ρ x : ℝ} (h : |x| ≤ ρ) : clip ρ x = x := by
  have h' := abs_le.mp h
  rw [clip, min_eq_right h'.2, max_eq_right h'.1]

@[tmio T, powerlib_foundation] theorem abs_clip_le {ρ : ℝ} (hρ : 0 ≤ ρ) (x : ℝ) :
    |clip ρ x| ≤ ρ :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

@[tmio T, powerlib_foundation] theorem abs_clip_sub_le (ρ x y : ℝ) :
    |clip ρ x - clip ρ y| ≤ |x - y| := by
  have h1 := abs_max_sub_max_le_max (-ρ) (min ρ x) (-ρ) (min ρ y)
  have h2 := abs_min_sub_min_le_max ρ x ρ y
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (min ρ x - min ρ y))] at h1
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] at h2
  exact h1.trans h2

@[tmio T, powerlib_foundation] theorem continuous_clip (ρ : ℝ) : Continuous (clip ρ) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The oscillator `ẍ = accel b k₀ k₁ α₃ ν t x ẋ − α₂x² + u(t)` as a first-order field on the
state `(x, ẋ) ∈ ℝ × ℝ`, with the nonlinear terms read through the clip onto `[−ρ, ρ]`. -/
def cutOsc (b k₀ k₁ α₂ α₃ ν ρ : ℝ) (u : ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, accel b k₀ k₁ 0 ν t p.1 p.2 - α₃ * clip ρ p.1 ^ 3 - α₂ * clip ρ p.1 ^ 2 + u t)

variable {b k₀ k₁ α₂ α₃ ν ρ : ℝ} {u : ℝ → ℝ}

/-- On `|x| ≤ ρ` the cut-off field is the oscillator. -/
@[tmio T, powerlib_foundation] theorem cutOsc_of_abs_le {t : ℝ} {p : ℝ × ℝ} (h : |p.1| ≤ ρ) :
    cutOsc b k₀ k₁ α₂ α₃ ν ρ u t p =
      (p.2, accel b k₀ k₁ α₃ ν t p.1 p.2 - α₂ * p.1 ^ 2 + u t) := by
  simp only [cutOsc, clip_of_abs_le h, accel]
  congr 1
  ring

/-- The cut-off field is Lipschitz in the state, uniformly in time:
`K = 1 + |b| + |k₀| + |k₁| + 3|α₃|ρ² + 2|α₂|ρ`. -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_cutOsc (hρ : 0 ≤ ρ) (t : ℝ) :
    LipschitzWith (Real.toNNReal (1 + |b| + |k₀| + |k₁| + 3 * |α₃| * ρ ^ 2 + 2 * |α₂| * ρ))
      (cutOsc b k₀ k₁ α₂ α₃ ν ρ u t) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  set K := 1 + |b| + |k₀| + |k₁| + 3 * |α₃| * ρ ^ 2 + 2 * |α₂| * ρ with hK
  simp only [Prod.dist_eq, Real.dist_eq, cutOsc]
  set m := max |p.1 - q.1| |p.2 - q.2| with hm
  have h1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have h2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm0 : 0 ≤ m := (abs_nonneg _).trans h1
  set cp := clip ρ p.1
  set cq := clip ρ q.1
  have hcp : |cp| ≤ ρ := abs_clip_le hρ _
  have hcq : |cq| ≤ ρ := abs_clip_le hρ _
  have hcl : |cp - cq| ≤ m := (abs_clip_sub_le ρ _ _).trans h1
  have hcos := Real.abs_cos_le_one (2 * ν * t)
  have e : accel b k₀ k₁ 0 ν t p.1 p.2 - α₃ * cp ^ 3 - α₂ * cp ^ 2 + u t -
      (accel b k₀ k₁ 0 ν t q.1 q.2 - α₃ * cq ^ 3 - α₂ * cq ^ 2 + u t) =
      -(b * (p.2 - q.2)) - (k₀ + k₁ * Real.cos (2 * ν * t)) * (p.1 - q.1) -
        α₃ * ((cp - cq) * (cp ^ 2 + cp * cq + cq ^ 2)) - α₂ * ((cp - cq) * (cp + cq)) := by
    simp only [accel]; ring
  have t1 : |-(b * (p.2 - q.2))| ≤ |b| * m := by
    rw [abs_neg, abs_mul]; gcongr
  have t2 : |(k₀ + k₁ * Real.cos (2 * ν * t)) * (p.1 - q.1)| ≤ (|k₀| + |k₁|) * m := by
    rw [abs_mul]
    have : |k₀ + k₁ * Real.cos (2 * ν * t)| ≤ |k₀| + |k₁| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_left hcos (abs_nonneg k₁)
      linarith
    exact mul_le_mul this h1 (abs_nonneg _) (by positivity)
  have t3 : |α₃ * ((cp - cq) * (cp ^ 2 + cp * cq + cq ^ 2))| ≤ |α₃| * (m * (3 * ρ ^ 2)) := by
    rw [abs_mul, abs_mul]
    have : |cp ^ 2 + cp * cq + cq ^ 2| ≤ 3 * ρ ^ 2 := by
      have a1 : |cp ^ 2| ≤ ρ ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hcp 2
      have a2 : |cq ^ 2| ≤ ρ ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hcq 2
      have a3 : |cp * cq| ≤ ρ ^ 2 := by
        rw [abs_mul, sq]; exact mul_le_mul hcp hcq (abs_nonneg _) hρ
      calc |cp ^ 2 + cp * cq + cq ^ 2| ≤ |cp ^ 2 + cp * cq| + |cq ^ 2| := abs_add_le _ _
        _ ≤ |cp ^ 2| + |cp * cq| + |cq ^ 2| := by gcongr; exact abs_add_le _ _
        _ ≤ 3 * ρ ^ 2 := by linarith
    gcongr
  have t4 : |α₂ * ((cp - cq) * (cp + cq))| ≤ |α₂| * (m * (2 * ρ)) := by
    rw [abs_mul, abs_mul]
    have : |cp + cq| ≤ 2 * ρ := (abs_add_le _ _).trans (by linarith)
    gcongr
  refine max_le ?_ ?_
  · have : 1 ≤ K := by
      have := abs_nonneg b; have := abs_nonneg k₀; have := abs_nonneg k₁
      have : 0 ≤ 3 * |α₃| * ρ ^ 2 := by positivity
      have : 0 ≤ 2 * |α₂| * ρ := by positivity
      rw [hK]; linarith
    nlinarith
  · rw [e]
    have hsum : |-(b * (p.2 - q.2)) - (k₀ + k₁ * Real.cos (2 * ν * t)) * (p.1 - q.1) -
        α₃ * ((cp - cq) * (cp ^ 2 + cp * cq + cq ^ 2)) - α₂ * ((cp - cq) * (cp + cq))| ≤
        |-(b * (p.2 - q.2))| + |(k₀ + k₁ * Real.cos (2 * ν * t)) * (p.1 - q.1)| +
          |α₃ * ((cp - cq) * (cp ^ 2 + cp * cq + cq ^ 2))| + |α₂ * ((cp - cq) * (cp + cq))| := by
      refine (abs_sub _ _).trans ?_
      gcongr
      refine (abs_sub _ _).trans ?_
      gcongr
      exact abs_sub _ _
    refine hsum.trans ?_
    have : |b| * m + (|k₀| + |k₁|) * m + |α₃| * (m * (3 * ρ ^ 2)) + |α₂| * (m * (2 * ρ)) ≤
        K * m := by
      rw [hK]; nlinarith
    linarith

/-- The cut-off field is jointly continuous for a continuous input. -/
@[tmio T, powerlib_foundation] theorem continuous_cutOsc (hu : Continuous u) :
    Continuous (Function.uncurry (cutOsc b k₀ k₁ α₂ α₃ ν ρ u)) := by
  have hc := continuous_clip ρ
  simp only [Function.uncurry_def, cutOsc, accel]
  fun_prop

@[tmio T, powerlib_foundation] private theorem hasDerivAt_fst' {P : ℝ → ℝ × ℝ} {v : ℝ × ℝ}
    {t : ℝ} (h : HasDerivAt P v t) : HasDerivAt (fun s => (P s).1) v.1 t := by
  exact (hasFDerivAt_fst (𝕜 := ℝ) (p := P t)).comp_hasDerivAt t h

@[tmio T, powerlib_foundation] private theorem hasDerivAt_snd' {P : ℝ → ℝ × ℝ} {v : ℝ × ℝ}
    {t : ℝ} (h : HasDerivAt P v t) : HasDerivAt (fun s => (P s).2) v.2 t := by
  exact (hasFDerivAt_snd (𝕜 := ℝ) (p := P t)).comp_hasDerivAt t h

/-! ## First-order averaging fails, for the solution itself -/

@[tmio T, powerlib_foundation] private theorem norm_pump' {ν : ℝ} (hν : 0 < ν) (k₁ : ℝ) :
    ‖I * ((k₁ / (4 * ν) : ℝ) : ℂ)‖ = |k₁| / (4 * ν) := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 4 * ν)]

/-- **First-order averaging fails on the time scale `1/ε`, without existence hypotheses.** For
`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u(t)` (`ν > 0`, `0 < ε ≤ 1`) with a continuous
input `|u| ≤ ε²M_u` on `[0, L/ε]` and an arbitrary initial state `(x₀, v₀)`, scaled initial
amplitude `w₀ = e^{0}(x₀ − jv₀/ν)/√ε`: let `W₂` solve the second-order averaged equation from the
transformed value `w₀ − √ε u(w₀, 0)` and `W₁` the first-order one (`β₁ = 3α₃/(8ν)`) from `w₀`, on
`[0, L/ε]`, and let `L` be below the explicit escape times,
`|W_i(0)| + L M_i < R` with `M_i = ampBound (b/2) (d/(2ν)) (|k₁|/(4ν)) β_i R`
(`norm_lt_of_escape`: then `W₁`, `W₂` stay in the disc of radius `R`); assume the branch
condition, `errSecond … < 1` and `L/ε ≥ π/(2ν)`. Then
* the oscillator has a solution on `[0, L/ε]` from `(x₀, v₀)` (a global solution of the cut-off
  field `cutOsc` that never meets the cut-off: by the a-priori bound of
  `ComplexPump.second_order_from` its scaled amplitude stays in the disc `2(R + 1)`);
* every solution on `[0, L/ε]` from `(x₀, v₀)` (it is that one, by uniqueness for the field
  clipped at a radius above both) has a time `t ∈ [0, L/ε]` with
  `|x(t) − √ε Re(W₁(t) e^{jνt})| ≥ √ε (failConst … |w₀| − failErr …)`.
This is `FirstOrderFails.first_order_fails` with its hypotheses on the solution (`x` defined on
all of `ℝ`) and on the averaged solutions (in the disc) discharged. -/
@[tmio T, powerlib_foundation] theorem first_order_fails_solution {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {u : ℝ → ℝ} (huc : Continuous u)
    (hu : ∀ t ∈ Icc 0 (L / ε), |u t| ≤ ε ^ 2 * Mu) (x₀ v₀ : ℝ) {W₁ W₂ : ℝ → ℂ}
    (hW₂ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₂
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (W₂ t)) (Icc 0 (L / ε)) t)
    (h0₂ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀ -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀) 0 = W₂ 0)
    (hW₁ : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₁
      (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
        (3 * α₃ / (8 * ν)) (W₁ t)) (Icc 0 (L / ε)) t)
    (h0₁ : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀ = W₁ 0)
    (hesc₁ : ‖W₁ 0‖ + L * ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R <
      R)
    (hesc₂ : ‖W₂ 0‖ + L * ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
      (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R < R)
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R L ε Mu < 1) (hT : Real.pi / (2 * ν) ≤ L / ε) :
    (∃ x x' : ℝ → ℝ, x 0 = x₀ ∧ x' 0 = v₀ ∧ ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt x (x' t) (Icc 0 (L / ε)) t ∧
      HasDerivWithinAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) -
        α₂ * x t ^ 2 + u t) (Icc 0 (L / ε)) t) ∧
    ∀ x x' : ℝ → ℝ, x 0 = x₀ → x' 0 = v₀ → (∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt x (x' t) (Icc 0 (L / ε)) t ∧
      HasDerivWithinAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) -
        α₂ * x t ^ 2 + u t) (Icc 0 (L / ε)) t) →
      ∃ t ∈ Icc 0 (L / ε), √ε * (failConst b d k₁ α₂ α₃ ν R L ‖W₁ 0‖ -
        failErr b d k₁ α₂ α₃ ν R L ε Mu ‖W₁ 0‖) ≤ |x t - √ε * (W₁ t * phase ν t).re| := by
  have hT0 : 0 ≤ L / ε := div_nonneg hL hε.le
  have hεT : ε * (L / ε) = L := by field_simp
  have hs0 : 0 < √ε := Real.sqrt_pos.mpr hε
  have hs1 : √ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  set ρ := 2 * (R + 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hnc := norm_pump' hν k₁
  -- the averaged solutions stay in the disc of radius `R`
  have hb₁ : ∀ t ∈ Icc 0 (L / ε), ‖W₁ t‖ ≤ R := fun t ht =>
    (norm_lt_of_escape hε.le hR hW₁ (by rw [hnc, hεT]; exact hesc₁) t ht).le
  have hb₂ : ∀ t ∈ Icc 0 (L / ε), ‖W₂ t‖ ≤ R := fun t ht =>
    (norm_lt_of_escape hε.le hR hW₂ (by rw [hnc, hεT]; exact hesc₂) t ht).le
  -- the global solution of the cut-off oscillator
  obtain ⟨P, hP0, hP⟩ := DuffingMathieu.exists_global_solution
    (f := cutOsc (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₂ α₃ ν ρ u) (continuous_cutOsc huc)
    (lipschitzWith_cutOsc hρ0) (x₀, v₀)
  set xg : ℝ → ℝ := fun t => (P t).1 with hxg
  set vg : ℝ → ℝ := fun t => (P t).2 with hvg
  have hxgd : ∀ t, HasDerivAt xg (vg t) t := fun t => hasDerivAt_fst' (hP t)
  set ueff : ℝ → ℝ := fun t => (cutOsc (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₂ α₃ ν ρ u t (P t)).2 -
    (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (xg t) (vg t) - α₂ * xg t ^ 2) with hueff
  have hvgd : ∀ t, HasDerivAt vg (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (xg t) (vg t) -
      α₂ * xg t ^ 2 + ueff t) t := by
    intro t
    have h := hasDerivAt_snd' (hP t)
    convert h using 1
    simp only [hueff]; ring
  have hueq : ∀ t, |xg t| ≤ ρ → ueff t = u t := by
    intro t h
    simp only [hueff, cutOsc_of_abs_le (b := ε * b) (k₀ := ν ^ 2 - ε * d) (k₁ := ε * k₁)
      (α₂ := α₂) (α₃ := α₃) (ν := ν) (u := u) (t := t) (p := P t) h]
    ring
  -- in the disc `|w| ≤ 2(R + 1)` the cut-off is inactive
  have habs : ∀ t, ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (xg t) (vg t)‖ ≤ 2 * (R + 1) → |xg t| ≤ ρ := by
    intro t hw
    calc |xg t| ≤ √ε * ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (xg t) (vg t)‖ :=
          ForcedPump.abs_le_scaled hε ν t (xg t) (vg t)
      _ ≤ 1 * ρ := mul_le_mul hs1 hw (norm_nonneg _) zero_le_one
      _ = ρ := one_mul _
  have hu' : ∀ t ∈ Icc 0 (L / ε), ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν t (xg t) (vg t)‖ ≤ 2 * (R + 1) →
      |ueff t| ≤ ε ^ 2 * Mu := by
    intro t ht hw
    rw [hueq t (habs t hw)]
    exact hu t ht
  have hxg0 : xg 0 = x₀ := by simp only [hxg, hP0]
  have hvg0 : vg 0 = v₀ := by simp only [hvg, hP0]
  have h0₂' : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (xg 0) (vg 0) -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (xg 0) (vg 0)) 0 = W₂ 0 := by
    rw [hxg0, hvg0]; exact h0₂
  have h0₁' : ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (xg 0) (vg 0) = W₁ 0 := by
    rw [hxg0, hvg0]; exact h0₁
  have hw0 : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 (xg 0) (vg 0)‖ < 2 * (R + 1) := by
    rw [h0₁']; have := hb₁ 0 ⟨le_rfl, hT0⟩; linarith
  -- the a-priori bound: the scaled amplitude stays in the disc `2(R + 1)` on the window
  have hap := ComplexPump.second_order_from (s₁ := 0) hν hR hL hε hε1 hMu hxgd hvgd
    (by rw [zero_add]; exact hu') (by rw [zero_add]; exact hW₂) (by rw [zero_add]; exact hb₂)
    h0₂' hw0 hbranch hsmall
  have hin : ∀ t ∈ Icc 0 (L / ε), |xg t| ≤ ρ := fun t ht =>
    habs t (hap t (by rw [zero_add]; exact ht)).2.1.le
  -- first-order averaging fails for the global solution
  obtain ⟨t, ht, hfail⟩ := FirstOrderFails.first_order_fails hν hR hL hε hε1 hMu hxgd hvgd hu'
    hW₂ hb₂ h0₂' hW₁ hb₁ h0₁' hbranch hsmall hT
  refine ⟨⟨xg, vg, hxg0, hvg0, fun s hs => ⟨(hxgd s).hasDerivWithinAt, ?_⟩⟩,
    fun x x' hx0 hx'0 hsol => ?_⟩
  · rw [← hueq s (hin s hs)]
    exact (hvgd s).hasDerivWithinAt
  -- every solution on the window is the global one
  have hxc : ContinuousOn x (Icc 0 (L / ε)) := fun s hs => (hsol s hs).1.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  have hρ'0 : 0 ≤ max B ρ := hρ0.trans (le_max_right _ _)
  have hlip' := lipschitzWith_cutOsc (b := ε * b) (k₀ := ν ^ 2 - ε * d) (k₁ := ε * k₁)
    (α₂ := α₂) (α₃ := α₃) (ν := ν) (u := u) hρ'0
  have hEq : EqOn (fun s => (x s, x' s)) P (Icc 0 (L / ε)) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := cutOsc (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₂ α₃ ν (max B ρ) u) (s := fun _ => univ)
      (fun s _ => (hlip' s).lipschitzOnWith) ?_ ?_ (fun _ _ => mem_univ _)
      (fun s _ => (hP s).continuousAt.continuousWithinAt) ?_ (fun _ _ => mem_univ _) ?_
    · exact fun s hs => ((hsol s hs).1.continuousWithinAt).prodMk
        ((hsol s hs).2.continuousWithinAt)
    · intro s hs
      have hs' := Ico_subset_Icc_self hs
      have h1 := ((hsol s hs').1.prodMk (hsol s hs').2).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs)
      have hc : |x s| ≤ max B ρ := by
        have := hB s hs'
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      rw [cutOsc_of_abs_le (p := (x s, x' s)) hc]
      exact h1
    · intro s hs
      have h := (hP s).hasDerivWithinAt (s := Ici s)
      have hc : |(P s).1| ≤ ρ := hin s (Ico_subset_Icc_self hs)
      have hc' : |(P s).1| ≤ max B ρ := hc.trans (le_max_right _ _)
      rw [cutOsc_of_abs_le hc] at h
      rw [cutOsc_of_abs_le hc']
      exact h
    · show (x 0, x' 0) = P 0
      rw [hP0, hx0, hx'0]
  refine ⟨t, ht, ?_⟩
  have hxt : x t = xg t := congrArg Prod.fst (hEq ht)
  rw [hxt]
  exact hfail

/-- **First-order averaging fails, from the initial state alone.** For
`ẍ + εbẋ + (ν² − εd + εk₁ cos 2νt)x + α₂x² + α₃x³ = u(t)` (`ν > 0`, `0 < ε ≤ 1`, a continuous input
`|u| ≤ ε²M_u` on `[0, L/ε]`) and an initial state `(x₀, v₀)` with scaled amplitude
`w₀ = (x₀ − jv₀/ν)/√ε`: if `L` is below the two explicit escape times,
`|w₀| + L M₁ < R` and `|w₀ − √ε u(w₀, 0)| + L M₂ < R` (`M_i = ampBound … β_i R`), the branch
condition, `errSecond … < 1` and `L/ε ≥ π/(2ν)` hold, then the first-order prediction `W₁` (from
`w₀`) and the second-order averaged amplitude `W₂` (from the transformed value) exist on
`[0, L/ε]` (`exists_averaged_solution`), the oscillator has a solution on `[0, L/ε]` from
`(x₀, v₀)`, and every such solution has a time `t` with
`|x(t) − √ε Re(W₁(t) e^{jνt})| ≥ √ε (failConst … |w₀| − failErr …)`
(`first_order_fails_solution`). No solution is assumed. -/
@[tmio T, powerlib_foundation] theorem first_order_fails_initial {ν : ℝ} (hν : 0 < ν)
    {b d k₁ α₂ α₃ R L ε Mu : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hMu : 0 ≤ Mu) {u : ℝ → ℝ} (huc : Continuous u)
    (hu : ∀ t ∈ Icc 0 (L / ε), |u t| ≤ ε ^ 2 * Mu) (x₀ v₀ : ℝ)
    (hesc₁ : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀‖ +
      L * ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν)) (3 * α₃ / (8 * ν)) R < R)
    (hesc₂ : ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀ -
        (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀) 0‖ +
      L * ampBound (b / 2) (d / (2 * ν)) (|k₁| / (4 * ν))
        (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) R < R)
    (hbranch : 4 * (R + 1) * (√ε * (5 * |α₂| / (6 * ν ^ 2))) < 1)
    (hsmall : errSecond b d k₁ α₂ α₃ ν R L ε Mu < 1) (hT : Real.pi / (2 * ν) ≤ L / ε) :
    ∃ W₁ W₂ : ℝ → ℂ,
      W₁ 0 = ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀ ∧
      (∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₁
        (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
          (3 * α₃ / (8 * ν)) (W₁ t)) (Icc 0 (L / ε)) t) ∧
      W₂ 0 = ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀ -
        (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀) 0 ∧
      (∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt W₂
        (ε • ampField (b / 2) (d / (2 * ν)) (I * ((k₁ / (4 * ν) : ℝ) : ℂ)) 0
          (3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3)) (W₂ t)) (Icc 0 (L / ε)) t) ∧
      (∃ x x' : ℝ → ℝ, x 0 = x₀ ∧ x' 0 = v₀ ∧ ∀ t ∈ Icc 0 (L / ε),
        HasDerivWithinAt x (x' t) (Icc 0 (L / ε)) t ∧
        HasDerivWithinAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) -
          α₂ * x t ^ 2 + u t) (Icc 0 (L / ε)) t) ∧
      ∀ x x' : ℝ → ℝ, x 0 = x₀ → x' 0 = v₀ → (∀ t ∈ Icc 0 (L / ε),
        HasDerivWithinAt x (x' t) (Icc 0 (L / ε)) t ∧
        HasDerivWithinAt x' (accel (ε * b) (ν ^ 2 - ε * d) (ε * k₁) α₃ ν t (x t) (x' t) -
          α₂ * x t ^ 2 + u t) (Icc 0 (L / ε)) t) →
        ∃ t ∈ Icc 0 (L / ε), √ε * (failConst b d k₁ α₂ α₃ ν R L ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀‖ -
          failErr b d k₁ α₂ α₃ ν R L ε Mu ‖((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀‖) ≤
            |x t - √ε * (W₁ t * phase ν t).re| := by
  have hεT : ε * (L / ε) = L := by field_simp
  have hnc := norm_pump' hν k₁
  obtain ⟨W₁, hW₁0, hW₁, -⟩ := exists_averaged_solution (σ := b / 2) (Δ := d / (2 * ν))
    (c := I * ((k₁ / (4 * ν) : ℝ) : ℂ)) (β := 3 * α₃ / (8 * ν)) (T := L / ε) hε.le hR
    (W₀ := ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀) (by rw [hnc, hεT]; exact hesc₁)
  obtain ⟨W₂, hW₂0, hW₂, -⟩ := exists_averaged_solution (σ := b / 2) (Δ := d / (2 * ν))
    (c := I * ((k₁ / (4 * ν) : ℝ) : ℂ)) (β := 3 * α₃ / (8 * ν) - 5 * α₂ ^ 2 / (12 * ν ^ 3))
    (T := L / ε) hε.le hR (W₀ := ((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀ -
      (√ε : ℂ) * nearId α₂ ν (((√ε : ℝ) : ℂ)⁻¹ * vdp ν 0 x₀ v₀) 0)
    (by rw [hnc, hεT]; exact hesc₂)
  obtain ⟨hex, hall⟩ := first_order_fails_solution hν hR hL hε hε1 hMu huc hu x₀ v₀ hW₂
    hW₂0.symm hW₁ hW₁0.symm (by rw [hW₁0]; exact hesc₁) (by rw [hW₂0]; exact hesc₂) hbranch
    hsmall hT
  refine ⟨W₁, W₂, hW₁0, hW₁, hW₂0, hW₂, hex, fun x x' hx0 hx'0 hsol => ?_⟩
  obtain ⟨t, ht, h⟩ := hall x x' hx0 hx'0 hsol
  rw [hW₁0] at h
  exact ⟨t, ht, h⟩

end powerlib.ParametricResonance.FirstOrderFailsExistence
