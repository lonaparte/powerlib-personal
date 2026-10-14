import theorem.Asymptotics.GaussianMoments

/-! # Fold slow passage: the inner Riccati problem and its solvability condition

The rescaled scalar inner problems of the fold slow-passage note, written as explicit real ODEs
in the inner time `τ`, their exact linearization along the separatrix, the solvability functional
and the escape threshold.

Scope.
* The objects are
  the grazing (quadratic-tangency) inner problem `X' = λ - τ² + X²` (`riccatiGraze`) and
  the constant-rate ramp inner problem `X' = λ + τ + X²` (`riccatiRamp`).
* `λ` is the rescaled margin parameter (not an eigenvalue), `X` the rescaled fast variable.
  These are formal scalar ODEs; their derivation from a particular converter fold, the
  `ν`-expansion `ε_c/ε_qs = 1 + ν + C₂ ν² + O(ν³)` and the value `C₂ = 3/8` are **not**
  formalized here. The escape threshold `λ^{(0)} = 1` of the unperturbed grazing problem is
  (last item of the results below).
* Two different `λ*` values appear in the note and must not be confused. `λ* = 1` is the escape
  threshold of the **unperturbed** inner problem `X' = λ − τ² + X²` (the first-order term `1` of
  the expansion); the solvability functional also returns `1` for every odd perturbation
  (`solvabilityShift_odd`). `λ* = 1/2` is the value of the solvability functional for the **even
  test perturbation** `φ = τ²` (`solvabilityShift_sq`), i.e. the shifted threshold of a perturbed
  inner problem; it is not a threshold of the unperturbed problem.
* Foundation results; no model family.

Source: work-sync theory/T-fold-slow-passage.md §1.1–§1.3, §2.3;
projects/basin-guard/notes/concepts/fold-slow-passage.md §2 and "作用域 (a)".
The note's error-propagation remark (§1.5: a 0.2 % error on `F ≈ 1.1` at `ν = 0.1`) is
arithmetic, not a theorem; it is not stated here.

Results.
* `X = τ` solves the grazing problem iff `λ = 1` (`id_solves_riccatiGraze_iff`).
* Exact linearization along the separatrix: `X = τ + η` solves it iff
  `η' = 2τη + (λ - 1) + η²` (`riccatiGraze_shift_iff`; so in the pure inner problem `φ = η²`).
* The adjoint weight `ζ = e^{-τ²}` solves `ζ' = -2τζ` (`hasDerivAt_adjointWeight`),
  `∫ e^{-τ²} = √π`.
* The solvability functional `λ* = 1 - π^{-1/2} ∫ e^{-τ²} φ(τ) dτ` (`solvabilityShift`): equals
  `1` for every odd `φ`, equals `1/2` for `φ = τ²`.
* Constant-rate ramp: time translation `τ ↦ τ + λ` maps solutions of `X' = τ + X²` onto
  solutions of `X' = λ + τ + X²` and back (`riccatiRamp_shift`, `riccatiRamp_unshift`), so `λ`
  cannot act as a threshold parameter.
* Riccati–Schrödinger link: if `u ≠ 0` solves `-u'' + τ² u = λ u`, then `X = -u'/u` solves the
  grazing problem (`riccatiGraze_of_schrodinger`); the ground state `u = e^{-τ²/2}` has `λ = 1`
  and gives `X = τ` (`groundState_schrodinger`, `groundState_logDeriv`).
* Escape threshold `λ* = 1` (trajectory level). Along every solution the adjoint-weighted
  deviation obeys `(e^{−τ²}(X − τ))' = e^{−τ²}(λ − 1 + (X − τ)²)` (`hasDerivAt_weighted_deviation`).
  For a solution leaving the attracting branch (`X(τ) − τ → 0` as `τ → −∞`):
  `λ > 1` ⇒ `X > τ` and escape before `τ = π/(2√(λ − 1))` (`riccatiGraze_escape`);
  `λ < 1` ⇒ `X < τ` for as long as it exists (`riccatiGraze_below`, no crossing of the
  separatrix); `λ = 1` ⇒ a global such solution is exactly the separatrix `X = τ`
  (`riccatiGraze_critical_eq`); a global such solution forces `λ ≤ 1`
  (`le_one_of_global_branch`). Existence of the branch solution for `λ < 1` is not formalized.

Related fold modules: `theorem/NormalForm/DynamicFold.lean` rescales the linearly swept fold
`ẋ = μ₀ − εt − x²` to `y' = −s − y²`, which is the ramp problem `X' = τ + X²` (`λ = 0`) for
`X = −y`; `theorem/Stochastic/NoiseFold.lean` is the noisy swept fold.
-/

noncomputable section
namespace powerlib.NormalForm

open Real MeasureTheory

/-- Right-hand side of the grazing inner problem `X' = λ - τ² + X²`. -/
def riccatiGraze (lam τ X : ℝ) : ℝ := lam - τ ^ 2 + X ^ 2

/-- Right-hand side of the constant-rate ramp inner problem `X' = λ + τ + X²`. -/
def riccatiRamp (lam τ X : ℝ) : ℝ := lam + τ + X ^ 2

/-- Solvability shift `λ* = 1 - π^{-1/2} ∫ e^{-τ²} φ(τ) dτ` of a perturbation `φ`
evaluated on the separatrix. -/
def solvabilityShift (φ : ℝ → ℝ) : ℝ :=
  1 - (Real.sqrt π)⁻¹ * ∫ τ : ℝ, Real.exp (-τ ^ 2) * φ τ

/-- The unperturbed separatrix `X = τ` is an exact solution exactly when `λ = 1`. -/
@[powerlib_foundation] theorem id_solves_riccatiGraze_iff (lam : ℝ) :
    (∀ τ, HasDerivAt (fun τ : ℝ => τ) (riccatiGraze lam τ τ) τ) ↔ lam = 1 := by
  constructor
  · intro h
    have h0 := (h 0).unique (hasDerivAt_id' 0)
    simpa [riccatiGraze] using h0
  · rintro rfl τ
    simpa [riccatiGraze] using hasDerivAt_id' τ

/-- Exact linearization along the separatrix: `X = τ + η` solves `X' = λ - τ² + X²` at `τ`
iff `η' = 2τη + (λ - 1) + η²` there. -/
@[powerlib_foundation] theorem riccatiGraze_shift_iff (lam : ℝ) {η : ℝ → ℝ} {η' τ : ℝ} :
    HasDerivAt (fun s => s + η s) (riccatiGraze lam τ (τ + η τ)) τ ∧ HasDerivAt η η' τ ↔
      HasDerivAt η η' τ ∧ η' = 2 * τ * η τ + (lam - 1) + η τ ^ 2 := by
  constructor
  · rintro ⟨hX, hη⟩
    refine ⟨hη, ?_⟩
    have h2 := (hasDerivAt_id' τ).add hη
    have := hX.unique h2
    simp only [riccatiGraze] at this
    linarith
  · rintro ⟨hη, rfl⟩
    refine ⟨?_, hη⟩
    have h2 := (hasDerivAt_id' τ).add hη
    convert h2 using 1
    simp only [riccatiGraze]
    ring

/-- The adjoint of `η' = 2τη` is solved by the Gaussian weight: `ζ = e^{-τ²}`, `ζ' = -2τζ`. -/
@[powerlib_foundation] theorem hasDerivAt_adjointWeight (τ : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2)) (-2 * τ * Real.exp (-τ ^ 2)) τ := by
  have h := ((hasDerivAt_pow 2 τ).neg).exp
  convert h using 1
  simp; ring

/-- Parity: every odd perturbation leaves the threshold at `λ* = 1`. -/
@[powerlib_foundation] theorem solvabilityShift_odd {φ : ℝ → ℝ} (hφ : ∀ τ, φ (-τ) = -φ τ) :
    solvabilityShift φ = 1 := by
  rw [solvabilityShift, Asymptotics.integral_exp_neg_sq_mul_odd hφ, mul_zero, sub_zero]

/-- The even test perturbation `φ = τ²` gives `λ* = 1/2`. -/
@[powerlib_foundation] theorem solvabilityShift_sq :
    solvabilityShift (fun τ => τ ^ 2) = 1 / 2 := by
  have h : ∫ τ : ℝ, Real.exp (-τ ^ 2) * τ ^ 2 = Real.sqrt π / 2 := by
    rw [← Asymptotics.integral_sq_mul_exp_neg_sq]
    congr 1
    funext τ
    ring
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  rw [solvabilityShift, h]
  field_simp
  ring

/-- A constant perturbation `φ = c` shifts the threshold by exactly `-c`
(normalization `∫ e^{-τ²} = √π`). -/
@[powerlib_foundation] theorem solvabilityShift_const (c : ℝ) :
    solvabilityShift (fun _ => c) = 1 - c := by
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  rw [solvabilityShift, integral_mul_const, Asymptotics.integral_exp_neg_sq]
  field_simp

/-- Constant-rate ramp: if `X` solves `X' = τ + X²`, then `Y(τ) = X(τ + λ)` solves
`Y' = λ + τ + Y²`. The margin parameter is absorbed by a time translation. -/
@[powerlib_foundation] theorem riccatiRamp_shift {X : ℝ → ℝ}
    (hX : ∀ τ, HasDerivAt X (riccatiRamp 0 τ (X τ)) τ) (lam : ℝ) :
    ∀ τ, HasDerivAt (fun s => X (s + lam)) (riccatiRamp lam τ (X (τ + lam))) τ := by
  intro τ
  have h := (hX (τ + lam)).comp τ ((hasDerivAt_id' τ).add_const lam)
  rw [show riccatiRamp lam τ (X (τ + lam)) = riccatiRamp 0 (τ + lam) (X (τ + lam)) * 1 by
    simp only [riccatiRamp]; ring]
  exact h

/-- Converse of `riccatiRamp_shift`: every solution of the ramp problem with parameter `λ` is
a time translate of a solution with `λ = 0`. -/
@[powerlib_foundation] theorem riccatiRamp_unshift {Y : ℝ → ℝ} (lam : ℝ)
    (hY : ∀ τ, HasDerivAt Y (riccatiRamp lam τ (Y τ)) τ) :
    ∀ τ, HasDerivAt (fun s => Y (s - lam)) (riccatiRamp 0 τ (Y (τ - lam))) τ := by
  intro τ
  have h := (hY (τ - lam)).comp τ ((hasDerivAt_id' τ).sub_const lam)
  rw [show riccatiRamp 0 τ (Y (τ - lam)) = riccatiRamp lam (τ - lam) (Y (τ - lam)) * 1 by
    simp only [riccatiRamp]; ring]
  exact h

/-- Riccati–Schrödinger link: a nonvanishing solution of `-u'' + τ² u = λ u` gives the
solution `X = -u'/u` of the grazing inner problem. -/
@[powerlib_foundation] theorem riccatiGraze_of_schrodinger {lam : ℝ} {u u' : ℝ → ℝ} {τ : ℝ}
    (hu : ∀ s, HasDerivAt u (u' s) s) (hu' : HasDerivAt u' ((τ ^ 2 - lam) * u τ) τ)
    (hne : u τ ≠ 0) :
    HasDerivAt (fun s => -u' s / u s) (riccatiGraze lam τ (-u' τ / u τ)) τ := by
  have h := (hu'.neg).div (hu τ) hne
  convert h using 1
  simp only [riccatiGraze, Pi.neg_apply]
  field_simp
  ring

/-- The Gaussian ground state `u = e^{-τ²/2}` solves `-u'' + τ² u = u` (eigenvalue `λ = 1`). -/
@[powerlib_foundation] theorem groundState_schrodinger (τ : ℝ) :
    HasDerivAt (fun s : ℝ => -s * Real.exp (-s ^ 2 / 2))
      ((τ ^ 2 - 1) * Real.exp (-τ ^ 2 / 2)) τ ∧
    (∀ s, HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2)) (-s * Real.exp (-s ^ 2 / 2)) s) := by
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2))
      (-s * Real.exp (-s ^ 2 / 2)) s := by
    intro s
    have h := (((hasDerivAt_pow 2 s).neg).div_const 2).exp
    convert h using 1
    simp; ring
  refine ⟨?_, hg⟩
  have h := ((hasDerivAt_id' τ).neg).mul (hg τ)
  convert h using 1
  simp; ring

/-- The ground state reproduces the separatrix: `-u'/u = τ` for `u = e^{-τ²/2}`. -/
@[powerlib_foundation] theorem groundState_logDeriv (τ : ℝ) :
    -(-τ * Real.exp (-τ ^ 2 / 2)) / Real.exp (-τ ^ 2 / 2) = τ := by
  have := Real.exp_pos (-τ ^ 2 / 2)
  field_simp

/-! ## The escape threshold `λ* = 1` of the grazing inner problem -/

section Threshold

open Set Filter Topology

variable {lam T : ℝ} {X : ℝ → ℝ}

/-- Along any solution of `X' = λ − τ² + X²`, the deviation `η = X − τ` from the separatrix,
weighted by the adjoint weight `ζ = e^{−τ²}`, obeys `(e^{−τ²} η)' = e^{−τ²} (λ − 1 + η²)`. -/
@[powerlib_foundation] theorem hasDerivAt_weighted_deviation {τ : ℝ}
    (hX : HasDerivAt X (riccatiGraze lam τ (X τ)) τ) :
    HasDerivAt (fun s => Real.exp (-s ^ 2) * (X s - s))
      (Real.exp (-τ ^ 2) * (lam - 1 + (X τ - τ) ^ 2)) τ := by
  have h := (hasDerivAt_adjointWeight τ).mul (hX.sub (hasDerivAt_id' τ))
  convert h using 1
  simp only [riccatiGraze, Pi.sub_apply]; ring

@[powerlib_foundation] private theorem weighted_deviation_tendsto
    (hbranch : Tendsto (fun τ => X τ - τ) atBot (𝓝 0)) :
    Tendsto (fun s => Real.exp (-s ^ 2) * (X s - s)) atBot (𝓝 0) := by
  apply squeeze_zero_norm (a := fun s => ‖X s - s‖) _ (by simpa using hbranch.norm)
  intro s
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have : Real.exp (-s ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg s])
  nlinarith [norm_nonneg (X s - s), Real.exp_pos (-s ^ 2)]

@[powerlib_foundation] private theorem continuousOn_weighted_Iic
    (hX : ∀ τ ≤ T, HasDerivAt X (riccatiGraze lam τ (X τ)) τ) :
    ContinuousOn (fun s => Real.exp (-s ^ 2) * (X s - s)) (Iic T) := fun τ hτ =>
  (hasDerivAt_weighted_deviation (hX τ hτ)).continuousAt.continuousWithinAt

/-- **Escape above the threshold (`λ > 1`).** A solution of the grazing inner problem that leaves
the attracting branch (`X(τ) − τ → 0` as `τ → −∞`) and exists on `(−∞, T]` satisfies
`X > τ` there, and `T < π / (2√(λ − 1))`: it escapes in finite time. -/
@[powerlib_foundation] theorem riccatiGraze_escape (hlam : 1 < lam)
    (hX : ∀ τ ≤ T, HasDerivAt X (riccatiGraze lam τ (X τ)) τ)
    (hbranch : Tendsto (fun τ => X τ - τ) atBot (𝓝 0)) :
    (∀ τ ≤ T, τ < X τ) ∧ T < π / (2 * √(lam - 1)) := by
  set g : ℝ → ℝ := fun s => Real.exp (-s ^ 2) * (X s - s) with hgdef
  have hmono : StrictMonoOn g (Iic T) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic T) (continuousOn_weighted_Iic hX) ?_
    intro τ hτ
    rw [interior_Iic] at hτ
    rw [(hasDerivAt_weighted_deviation (hX τ hτ.le)).deriv]
    have : 0 < lam - 1 + (X τ - τ) ^ 2 := by nlinarith [sq_nonneg (X τ - τ)]
    positivity
  have hlim : Tendsto g atBot (𝓝 0) := weighted_deviation_tendsto hbranch
  have hpos : ∀ τ ≤ T, τ < X τ := by
    intro τ hτ
    have h0 : 0 ≤ g (τ - 1) := by
      refine le_of_tendsto hlim (eventually_atBot.2 ⟨τ - 1, fun σ hσ => ?_⟩)
      exact hmono.monotoneOn (show σ ∈ Iic T from by simp only [mem_Iic]; linarith)
        (show τ - 1 ∈ Iic T from by simp only [mem_Iic]; linarith) hσ
    have h1 : g (τ - 1) < g τ := hmono (show τ - 1 ∈ Iic T from by simp only [mem_Iic]; linarith)
      hτ (by linarith)
    have : 0 < Real.exp (-τ ^ 2) * (X τ - τ) := lt_of_le_of_lt h0 h1
    have := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp this
    linarith
  refine ⟨hpos, ?_⟩
  set c := √(lam - 1) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = lam - 1 := Real.sq_sqrt (by linarith)
  have hgoal : 0 < π / (2 * c) := by positivity
  rcases lt_or_ge T 0 with hT | hT
  · linarith
  -- `F(τ) = arctan(η(τ)/c) − cτ` is nondecreasing on `[0, T]`
  set F : ℝ → ℝ := fun s => Real.arctan ((X s - s) / c) - c * s with hFdef
  have hF : ∀ τ ≤ T, HasDerivAt F (1 / (1 + ((X τ - τ) / c) ^ 2) *
      (riccatiGraze lam τ (X τ) - 1) / c - c) τ := by
    intro τ hτ
    have h := (((hX τ hτ).sub (hasDerivAt_id' τ)).div_const c).arctan.sub
      ((hasDerivAt_id' τ).const_mul c)
    convert h using 1
    simp only [Pi.sub_apply]; ring
  have hmonoF : MonotoneOn F (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact fun τ hτ => (hF τ hτ.2).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (hF τ hτ.2.le).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [(hF τ hτ.2.le).deriv]
      have hη := hpos τ hτ.2.le
      set η := X τ - τ
      have hD : 0 < c ^ 2 + η ^ 2 := by positivity
      have e : 1 / (1 + (η / c) ^ 2) * (riccatiGraze lam τ (X τ) - 1) / c - c =
          c * (2 * τ * η) / (c ^ 2 + η ^ 2) := by
        have hX' : X τ = τ + η := by simp only [η]; ring
        rw [hX']
        simp only [riccatiGraze]
        field_simp
        rw [hc2]; ring
      rw [e]
      have : 0 ≤ 2 * τ * η := by have := hτ.1; have := hη; nlinarith
      positivity
  have hFT := hmonoF ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  simp only [hFdef, mul_zero, sub_zero] at hFT
  have hη0 : 0 < X 0 / c := div_pos (by linarith [hpos 0 hT]) hc
  have ha0 : 0 < Real.arctan (X 0 / c) := by
    have := Real.arctan_strictMono hη0; rwa [Real.arctan_zero] at this
  have hlt := Real.arctan_lt_pi_div_two ((X T - T) / c)
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- **No escape below the threshold (`λ < 1`).** A solution that leaves the attracting branch
stays strictly below the separatrix `X = τ` for as long as it exists. -/
@[powerlib_foundation] theorem riccatiGraze_below (hlam : lam < 1)
    (hX : ∀ τ ≤ T, HasDerivAt X (riccatiGraze lam τ (X τ)) τ)
    (hbranch : Tendsto (fun τ => X τ - τ) atBot (𝓝 0)) :
    ∀ τ ≤ T, X τ < τ := by
  set g : ℝ → ℝ := fun s => Real.exp (-s ^ 2) * (X s - s) with hgdef
  -- near `−∞` the deviation is small: `η² < 1 − λ`
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀, ∀ σ ≤ τ₀, (X σ - σ) ^ 2 < 1 - lam := by
    have hnhds : {y : ℝ | y ^ 2 < 1 - lam} ∈ 𝓝 (0 : ℝ) := by
      have hc : Continuous fun y : ℝ => y ^ 2 := continuous_pow 2
      exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp; linarith))
    exact eventually_atBot.1 (hbranch.eventually hnhds)
  set τ₁ := min τ₀ T with hτ₁def
  have hτ₁T : τ₁ ≤ T := min_le_right _ _
  have hanti : StrictAntiOn g (Iic τ₁) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic τ₁)
      ((continuousOn_weighted_Iic hX).mono (Iic_subset_Iic.2 hτ₁T)) ?_
    intro τ hτ
    rw [interior_Iic] at hτ
    rw [(hasDerivAt_weighted_deviation (hX τ (hτ.le.trans hτ₁T))).deriv]
    have h1 := hτ₀ τ (hτ.le.trans (min_le_left _ _))
    have : lam - 1 + (X τ - τ) ^ 2 < 0 := by linarith
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) this
  have hlim : Tendsto g atBot (𝓝 0) := weighted_deviation_tendsto hbranch
  -- below `τ₁` the weighted deviation is negative
  have hneg : ∀ τ ≤ τ₁, X τ < τ := by
    intro τ hτ
    have h0 : g (τ - 1) ≤ 0 := by
      refine ge_of_tendsto hlim (eventually_atBot.2 ⟨τ - 1, fun σ hσ => ?_⟩)
      exact hanti.antitoneOn (show σ ∈ Iic τ₁ from by simp only [mem_Iic]; linarith)
        (show τ - 1 ∈ Iic τ₁ from by simp only [mem_Iic]; linarith) hσ
    have h1 : g τ < g (τ - 1) := hanti (show τ - 1 ∈ Iic τ₁ from by simp only [mem_Iic]; linarith)
      hτ (by linarith)
    have : Real.exp (-τ ^ 2) * (X τ - τ) < 0 := lt_of_lt_of_le h1 h0
    have := neg_of_mul_neg_right this (Real.exp_pos _).le
    linarith
  -- on `[τ₁, T]`: the separatrix is a strict supersolution, so `η ≤ 0` …
  have hη : ∀ τ ≤ T, HasDerivAt (fun s => X s - s) (riccatiGraze lam τ (X τ) - 1) τ :=
    fun τ hτ => (hX τ hτ).sub (hasDerivAt_id' τ)
  have hle : ∀ τ ∈ Icc τ₁ T, X τ - τ ≤ 0 := by
    have := image_le_of_deriv_right_lt_deriv_boundary (f := fun s => X s - s)
      (f' := fun s => riccatiGraze lam s (X s) - 1) (a := τ₁) (b := T) (B := fun _ => 0)
      (B' := fun _ => 0)
      (fun τ hτ => (hη τ hτ.2).continuousAt.continuousWithinAt)
      (fun τ hτ => (hη τ hτ.2.le).hasDerivWithinAt)
      (by have := hneg τ₁ le_rfl; linarith)
      (fun _ => hasDerivAt_const _ _)
      (by
        intro τ _ h0
        have hXτ : X τ = τ := by linarith
        simp only [riccatiGraze, hXτ]
        linarith)
    exact fun τ hτ => this hτ
  -- … and strictly: at a touching point the slope `λ − 1 < 0` would push `η` above `0` before it
  intro τ hτ
  rcases le_or_gt τ τ₁ with h | h
  · exact hneg τ h
  have hle' := hle τ ⟨h.le, hτ⟩
  rcases lt_or_eq_of_le hle' with hlt | heq
  · linarith
  exfalso
  have hd := (hη τ hτ).tendsto_slope_zero_left
  have hslope : riccatiGraze lam τ (X τ) - 1 < 0 := by
    have hXτ : X τ = τ := by linarith
    simp only [riccatiGraze, hXτ]; linarith
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), t⁻¹ • ((X (τ + t) - (τ + t)) - (X τ - τ)) < 0 :=
    hd.eventually (gt_mem_nhds hslope)
  have hev2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), τ₁ - τ < t :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by linarith))
  obtain ⟨t, ht, ht2, htneg⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
  have htn : t < 0 := htneg
  rw [heq, sub_zero, smul_eq_mul] at ht
  have hpos : 0 < X (τ + t) - (τ + t) := by
    by_contra hc
    push Not at hc
    have : 0 ≤ t⁻¹ * (X (τ + t) - (τ + t)) :=
      mul_nonneg_of_nonpos_of_nonpos (inv_lt_zero.mpr htn).le hc
    linarith
  have := hle (τ + t) ⟨by linarith, by linarith⟩
  linarith

/-- **The critical value `λ = 1`.** The only solution of `X' = 1 − τ² + X²` that leaves the
attracting branch and exists for all `τ ∈ ℝ` is the separatrix `X = τ`. -/
@[powerlib_foundation] theorem riccatiGraze_critical_eq
    (hX : ∀ τ, HasDerivAt X (riccatiGraze 1 τ (X τ)) τ)
    (hbranch : Tendsto (fun τ => X τ - τ) atBot (𝓝 0)) :
    ∀ τ, X τ = τ := by
  set g : ℝ → ℝ := fun s => Real.exp (-s ^ 2) * (X s - s) with hgdef
  have hg : ∀ τ, HasDerivAt g (Real.exp (-τ ^ 2) * (1 - 1 + (X τ - τ) ^ 2)) τ :=
    fun τ => hasDerivAt_weighted_deviation (hX τ)
  have hmono : Monotone g := by
    apply monotone_of_deriv_nonneg (fun τ => (hg τ).differentiableAt)
    intro τ; rw [(hg τ).deriv]; positivity
  have hlim : Tendsto g atBot (𝓝 0) := weighted_deviation_tendsto hbranch
  have hg0 : ∀ τ, 0 ≤ g τ := fun τ =>
    le_of_tendsto hlim (eventually_atBot.2 ⟨τ, fun σ hσ => hmono hσ⟩)
  have hnonneg : ∀ τ, 0 ≤ X τ - τ := fun τ =>
    (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (hg0 τ)
  -- a positive deviation blows up in finite time
  have hnpos : ∀ τ, ¬ 0 < X τ - τ := by
    intro τ₁ h₁
    have hposafter : ∀ τ, τ₁ ≤ τ → 0 < X τ - τ := by
      intro τ hτ
      have : 0 < g τ₁ := mul_pos (Real.exp_pos _) h₁
      exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (this.trans_le (hmono hτ))
    set τ₂ := max τ₁ 0 with hτ₂def
    have hη₂ := hposafter τ₂ (le_max_left _ _)
    set τ₃ := τ₂ + 1 / (X τ₂ - τ₂) + 1 with hτ₃def
    have h23 : τ₂ ≤ τ₃ := by
      have : 0 < 1 / (X τ₂ - τ₂) := by positivity
      simp only [hτ₃def]; linarith
    -- `F = −1/η − τ` is nondecreasing on `[τ₂, τ₃]`
    set F : ℝ → ℝ := fun s => -(X s - s)⁻¹ - s with hFdef
    have hF : ∀ τ, τ₁ ≤ τ → HasDerivAt F
        (-(-(riccatiGraze 1 τ (X τ) - 1) / (X τ - τ) ^ 2) - 1) τ := by
      intro τ hτ
      exact (((hX τ).sub (hasDerivAt_id' τ)).inv (hposafter τ hτ).ne').neg.sub (hasDerivAt_id' τ)
    have hmonoF : MonotoneOn F (Icc τ₂ τ₃) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc τ₂ τ₃)
      · exact fun τ hτ =>
          (hF τ ((le_max_left _ _).trans hτ.1)).continuousAt.continuousWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        exact (hF τ ((le_max_left _ _).trans hτ.1.le)).differentiableAt.differentiableWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        have hτ1 : τ₁ ≤ τ := (le_max_left _ _).trans hτ.1.le
        rw [(hF τ hτ1).deriv]
        have hη := hposafter τ hτ1
        have hτ0 : 0 ≤ τ := (le_max_right _ _).trans hτ.1.le
        have e : -(-(riccatiGraze 1 τ (X τ) - 1) / (X τ - τ) ^ 2) - 1 =
            2 * τ / (X τ - τ) := by
          simp only [riccatiGraze]
          field_simp
          ring
        rw [e]
        positivity
    have h := hmonoF ⟨le_rfl, h23⟩ ⟨h23, le_rfl⟩ h23
    simp only [hFdef] at h
    have hη₃ := hposafter τ₃ ((le_max_left _ _).trans h23)
    have hinv : 0 < (X τ₃ - τ₃)⁻¹ := inv_pos.mpr hη₃
    have : τ₃ - τ₂ = 1 / (X τ₂ - τ₂) + 1 := by simp only [hτ₃def]; ring
    rw [one_div] at this
    linarith
  intro τ
  have h1 := hnonneg τ
  have h2 := hnpos τ
  push Not at h2
  linarith

/-- Consequently a global solution leaving the attracting branch exists only for `λ ≤ 1`, and at
`λ = 1` it is the separatrix itself. -/
@[powerlib_foundation] theorem le_one_of_global_branch
    (hX : ∀ τ, HasDerivAt X (riccatiGraze lam τ (X τ)) τ)
    (hbranch : Tendsto (fun τ => X τ - τ) atBot (𝓝 0)) : lam ≤ 1 := by
  by_contra h
  push Not at h
  have hc : 0 < π / (2 * √(lam - 1)) := by
    have := Real.sqrt_pos.mpr (show 0 < lam - 1 by linarith)
    positivity
  have := (riccatiGraze_escape (T := π / (2 * √(lam - 1))) h (fun τ _ => hX τ) hbranch).2
  linarith

end Threshold

end powerlib.NormalForm
