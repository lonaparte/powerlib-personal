import theorem.Periodic.Transition
import Mathlib.Analysis.ODE.Gronwall

/-! # Middlebrook–Ćuk state-space averaging: the switched model stays `O(T_sw)` close

The trajectory of an ideal two-topology switched linear converter stays within `O(T_sw)` of the
state-space averaged LTI model, at every instant of a finite horizon.

Model boundary.
* An ideal two-topology switched linear converter in continuous conduction mode: the state
  `x ∈ ℝ^X` (inductor currents / capacitor voltages, any fixed order; sup norm) obeys `ẋ = A₁ x`
  during the ON interval `[kT, kT + dT]` and `ẋ = A₂ x` during the OFF interval
  `[kT + dT, (k+1)T]` of every switching period, with a fixed duty ratio `d ∈ [0, 1]` and
  switching period `T = T_sw ∈ (0, 1]`.
* CCM is the statement that only these two topologies occur (no discontinuous-conduction third
  topology). Switches are ideal (instantaneous, lossless transitions); continuous time; no PWM
  carrier or modulator dynamics beyond the fixed duty ratio, no control loop, no delay.
* A constant input `u` is covered by appending `u` as a state with `u̇ = 0`, which turns
  `ẋ = A_i x + B_i u` into the homogeneous form used here (the augmented averaged matrix is the
  augmentation of `d A₁ + (1 − d) A₂`, `d B₁ + (1 − d) B₂`).
* The state-space averaged model is the LTI system `x̄̇ = Ā x̄`, `Ā = d A₁ + (1 − d) A₂`.
* Every statement holds for arbitrary matrices `A₁`, `A₂`, duty ratio and state index (no
  particular converter is formalized).
* Switched trajectories are Mathlib integral curves on each closed subinterval; uniqueness is
  LeanForControl's `eqOn_of_isIntegralCurveOn_Icc`. A trajectory of the ideal two-topology
  switched system with duty ratio `d` and period `T` (`ẋ = A₁ x` on `[kT, kT + dT]`, `ẋ = A₂ x`
  on `[kT + dT, (k + 1)T]`, one-sided derivatives at the switching instants) is written out in
  the statements as
  `∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
  IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))` (behaviour is
  defined only in the semantic layer).

Source: work-sync theory/T-averaging-method.md §1.5 (state-space averaging, `O(ε)` agreement on
the slow time scale; the intra-period ripple bound completes the `O(T)` comparison at every
instant).

Results.
* `norm_exp_smul_le`, `norm_exp_smul_sub_one_le` (Banach algebras with `‖1‖ = 1`) —
  `‖e^{sX}‖ ≤ e^{‖X‖s}`, `‖e^{sX} − 1‖ ≤ ‖X‖ s e^{‖X‖s}` (Grönwall / mean value).
* `periodMap_sub_exp_le` — one period of the switched system versus the averaged one,
  `‖e^{(1−d)TA₂} e^{dTA₁} − e^{TĀ}‖ ≤ c T²` for `0 ≤ T ≤ 1` (first-order agreement).
* `norm_pow_sub_pow_le` — `‖M^k − P^k‖ ≤ k B^k ‖M − P‖` when `‖M‖, ‖P‖ ≤ B`, `B ≥ 1`.
* `switched_sample` — every switched trajectory satisfies
  `x(kT) = (e^{(1−d)TA₂} e^{dTA₁})^k x(0)` (uniqueness of linear ODE solutions on each
  subinterval).
* `averaged_solves` — `x̄(t) = e^{tĀ} x₀` solves the averaged model.
* `stateSpaceAveraging_error` — for every horizon `L ≥ 0` there is `C` such that for all
  `T ∈ (0, 1]`, every switched trajectory with `x(0) = x₀`, and every switching instant
  `kT ≤ L`: `‖x(kT) − x̄(kT)‖ ≤ C T ‖x₀‖`.
* `switched_ripple` — intra-period ripple: there is `c`, depending only on `A₁`, `A₂`, such that
  for every `T ∈ (0, 1]`, every switched trajectory, every period `k` and every
  `t ∈ [kT, (k + 1)T]`: `‖x(t) − x(kT)‖ ≤ c T ‖x(kT)‖` (from `norm_exp_smul_sub_one_le` on the
  ON and OFF subintervals).
* `stateSpaceAveraging_error_uniform` — the averaging error is `O(T)` at **every** instant, not
  only at the switching instants: for every horizon `L ≥ 0` there is `C` with
  `‖x(t) − x̄(t)‖ ≤ C T ‖x₀‖` for all `t ∈ [0, L]` (sampled error + ripple + the drift
  `‖e^{sĀ} − 1‖ = O(s)` of the averaged model within the partial period). Auxiliary:
  `norm_avgMatrix_le`, `norm_periodMap_le`, `exp_smul_bounds`, `exp_add_smul`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology Matrix
open scoped Matrix.Norms.Operator

/-! ## Norm estimates for exponentials in a Banach algebra -/

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

omit [NormOneClass 𝔸] in
@[tmio T, powerlib_foundation] theorem hasDerivAt_exp_smul (X : 𝔸) (r : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X)) (X * NormedSpace.exp (r • X)) r :=
  hasDerivAt_exp_smul_const' X r

/-- `‖e^{sX}‖ ≤ e^{‖X‖ s}` for `s ≥ 0` (Grönwall). -/
@[powerlib_foundation] theorem norm_exp_smul_le (X : 𝔸) {s : ℝ} (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • X)‖ ≤ Real.exp (‖X‖ * s) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun r : ℝ => NormedSpace.exp (r • X))
    (f' := fun r => X * NormedSpace.exp (r • X)) (δ := 1) (K := ‖X‖) (ε := 0) (a := 0) (b := s)
    (fun r _ => (hasDerivAt_exp_smul X r).continuousAt.continuousWithinAt)
    (fun r _ => (hasDerivAt_exp_smul X r).hasDerivWithinAt)
    (by simp) (fun r _ => by simpa using norm_mul_le X (NormedSpace.exp (r • X)))
    s ⟨hs, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero, one_mul] at h
  exact h

/-- `‖e^{sX} − 1‖ ≤ ‖X‖ s e^{‖X‖ s}` for `s ≥ 0`. -/
@[powerlib_foundation] theorem norm_exp_smul_sub_one_le (X : 𝔸) {s : ℝ} (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • X) - 1‖ ≤ ‖X‖ * s * Real.exp (‖X‖ * s) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := s)
    (f := fun r : ℝ => NormedSpace.exp (r • X)) (f' := fun r => X * NormedSpace.exp (r • X))
    (C := ‖X‖ * Real.exp (‖X‖ * s))
    (fun r _ => (hasDerivAt_exp_smul X r).hasDerivWithinAt)
    (fun r hr => by
      calc ‖X * NormedSpace.exp (r • X)‖ ≤ ‖X‖ * ‖NormedSpace.exp (r • X)‖ := norm_mul_le _ _
        _ ≤ ‖X‖ * Real.exp (‖X‖ * s) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg X)
          exact (norm_exp_smul_le X hr.1).trans
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2.le (norm_nonneg X))))
    s ⟨hs, le_rfl⟩
  simp only [zero_smul, NormedSpace.exp_zero, sub_zero] at h
  linarith [h]

/-- Averaged matrix `Ā = d A₁ + (1 − d) A₂`. -/
def avgMatrix (d : ℝ) (A₁ A₂ : 𝔸) : 𝔸 := d • A₁ + (1 - d) • A₂

/-- One switching period: OFF interval after ON interval, `e^{(1−d)TA₂} e^{dTA₁}`. -/
def periodMap (d T : ℝ) (A₁ A₂ : 𝔸) : 𝔸 :=
  NormedSpace.exp (((1 - d) * T) • A₂) * NormedSpace.exp ((d * T) • A₁)

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- Telescoping: `‖M^k − P^k‖ ≤ k B^k ‖M − P‖` if `‖M‖, ‖P‖ ≤ B` and `1 ≤ B`. -/
@[powerlib_foundation] theorem norm_pow_sub_pow_le {M P : 𝔸} {B : ℝ} (hB : 1 ≤ B)
    (hM : ‖M‖ ≤ B) (hP : ‖P‖ ≤ B) (k : ℕ) :
    ‖M ^ k - P ^ k‖ ≤ k * B ^ k * ‖M - P‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdecomp : M ^ (k + 1) - P ^ (k + 1) = M * (M ^ k - P ^ k) + (M - P) * P ^ k := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have hPk : ‖P ^ k‖ ≤ B ^ k := (norm_pow_le P k).trans (pow_le_pow_left₀ (norm_nonneg _) hP k)
    have hB0 : 0 ≤ B := by linarith
    have hBk : B ^ k ≤ B ^ (k + 1) := pow_le_pow_right₀ hB (Nat.le_succ k)
    rw [hdecomp]
    calc ‖M * (M ^ k - P ^ k) + (M - P) * P ^ k‖
        ≤ ‖M‖ * ‖M ^ k - P ^ k‖ + ‖M - P‖ * ‖P ^ k‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ B * (k * B ^ k * ‖M - P‖) + ‖M - P‖ * B ^ k := by
          apply add_le_add
          · exact mul_le_mul hM ih (norm_nonneg _) hB0
          · exact mul_le_mul_of_nonneg_left hPk (norm_nonneg _)
      _ ≤ ((k + 1 : ℕ) : ℝ) * B ^ (k + 1) * ‖M - P‖ := by
          push_cast
          have := norm_nonneg (M - P)
          rw [pow_succ]
          have h2 : ‖M - P‖ * B ^ k ≤ ‖M - P‖ * (B ^ k * B) :=
            mul_le_mul_of_nonneg_left (by rw [← pow_succ]; exact hBk) this
          have e : ((k : ℝ) + 1) * (B ^ k * B) * ‖M - P‖ =
              B * (k * B ^ k * ‖M - P‖) + ‖M - P‖ * (B ^ k * B) := by ring
          rw [e]; linarith

/-- One period: `‖e^{(1−d)TA₂} e^{dTA₁} − e^{TĀ}‖ ≤ c T²` for `0 ≤ T ≤ 1`. -/
@[powerlib_foundation] theorem periodMap_sub_exp_le {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : 𝔸) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T ∈ Icc (0 : ℝ) 1,
      ‖periodMap d T A₁ A₂ - NormedSpace.exp (T • avgMatrix d A₁ A₂)‖ ≤ c * T ^ 2 := by
  set a := ‖A₁‖ + ‖A₂‖ with ha
  set Ab := avgMatrix d A₁ A₂
  have ha1 : ‖A₁‖ ≤ a := by linarith [norm_nonneg A₂]
  have ha2 : ‖A₂‖ ≤ a := by linarith [norm_nonneg A₁]
  have hd1' : 0 ≤ 1 - d := by linarith
  have hab : ‖Ab‖ ≤ a := by
    calc ‖Ab‖ ≤ ‖d • A₁‖ + ‖(1 - d) • A₂‖ := norm_add_le _ _
      _ = d * ‖A₁‖ + (1 - d) * ‖A₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hd0, Real.norm_of_nonneg hd1']
      _ ≤ d * a + (1 - d) * a := by gcongr
      _ = a := by ring
  have ha0 : 0 ≤ a := by positivity
  set K := Real.exp a with hK
  have hK1 : 1 ≤ K := Real.one_le_exp ha0
  -- uniform bounds on `[0, 1]`
  have hE : ∀ (X : 𝔸) (r : ℝ), ‖X‖ ≤ a → 0 ≤ r → r ≤ 1 →
      ‖NormedSpace.exp (r • X)‖ ≤ K ∧ ‖NormedSpace.exp (r • X) - 1‖ ≤ a * r * K := by
    intro X r hX hr0 hr1
    have hexp : Real.exp (‖X‖ * r) ≤ K :=
      Real.exp_le_exp.mpr (by nlinarith [norm_nonneg X])
    refine ⟨(norm_exp_smul_le X hr0).trans hexp, ?_⟩
    calc ‖NormedSpace.exp (r • X) - 1‖ ≤ ‖X‖ * r * Real.exp (‖X‖ * r) :=
          norm_exp_smul_sub_one_le X hr0
      _ ≤ a * r * K := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hX hr0) hexp (Real.exp_pos _).le
          positivity
  set c := a ^ 2 * (2 * K ^ 2 + 3 * K)
  refine ⟨c, by positivity, fun T hT => ?_⟩
  -- the error function and its derivative
  set E₁ : ℝ → 𝔸 := fun s => NormedSpace.exp ((d * s) • A₁)
  set E₂ : ℝ → 𝔸 := fun s => NormedSpace.exp (((1 - d) * s) • A₂)
  set Eb : ℝ → 𝔸 := fun s => NormedSpace.exp (s • Ab)
  have hE₁ : ∀ s, HasDerivAt E₁ (d • (A₁ * E₁ s)) s := by
    intro s
    have h := (hasDerivAt_exp_smul A₁ (d * s)).scomp s ((hasDerivAt_id s).const_mul d)
    simpa [E₁, Function.comp_def] using h
  have hE₂ : ∀ s, HasDerivAt E₂ ((1 - d) • (A₂ * E₂ s)) s := by
    intro s
    have h := (hasDerivAt_exp_smul A₂ ((1 - d) * s)).scomp s ((hasDerivAt_id s).const_mul (1 - d))
    simpa [E₂, Function.comp_def] using h
  have hEb : ∀ s, HasDerivAt Eb (Ab * Eb s) s := fun s => hasDerivAt_exp_smul Ab s
  set F' : ℝ → 𝔸 := fun s => (1 - d) • (A₂ * E₂ s) * E₁ s + E₂ s * (d • (A₁ * E₁ s)) -
    Ab * Eb s
  have hF : ∀ s, HasDerivAt (fun s => E₂ s * E₁ s - Eb s) (F' s) s :=
    fun s => ((hE₂ s).mul (hE₁ s)).sub (hEb s)
  -- rewrite `F'` using `F'(0) = 0`
  have hF'eq : ∀ s, F' s = (1 - d) • (A₂ * (E₂ s * E₁ s - 1)) + d • (E₂ s * A₁ * E₁ s - A₁) -
      Ab * (Eb s - 1) := by
    intro s
    simp only [F', Ab, avgMatrix]
    simp only [mul_sub, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, mul_one,
      smul_sub]
    abel
  have hbound : ∀ s ∈ Ico (0 : ℝ) T, ‖F' s‖ ≤ c * T := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := (hs.2.le).trans hT.2
    have hsT : s ≤ T := hs.2.le
    obtain ⟨h1K, h1d⟩ := hE A₁ (d * s) ha1 (by positivity) (by nlinarith)
    obtain ⟨h2K, h2d⟩ := hE A₂ ((1 - d) * s) ha2 (by positivity) (by nlinarith)
    obtain ⟨hbK, hbd⟩ := hE Ab s hab hs0 hs1
    have hds : d * s ≤ s := by nlinarith
    have hds' : (1 - d) * s ≤ s := by nlinarith
    have h1d' : ‖E₁ s - 1‖ ≤ a * s * K := h1d.trans (by gcongr)
    have h2d' : ‖E₂ s - 1‖ ≤ a * s * K := h2d.trans (by gcongr)
    have hprod : ‖E₂ s * E₁ s - 1‖ ≤ a * s * K * K + a * s * K := by
      have : E₂ s * E₁ s - 1 = (E₂ s - 1) * E₁ s + (E₁ s - 1) := by noncomm_ring
      rw [this]
      calc ‖(E₂ s - 1) * E₁ s + (E₁ s - 1)‖ ≤ ‖E₂ s - 1‖ * ‖E₁ s‖ + ‖E₁ s - 1‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ a * s * K * K + a * s * K := by gcongr
    have hmid : ‖E₂ s * A₁ * E₁ s - A₁‖ ≤ a * s * K * a * K + a * (a * s * K) := by
      have : E₂ s * A₁ * E₁ s - A₁ = (E₂ s - 1) * A₁ * E₁ s + A₁ * (E₁ s - 1) := by noncomm_ring
      rw [this]
      calc ‖(E₂ s - 1) * A₁ * E₁ s + A₁ * (E₁ s - 1)‖
          ≤ ‖E₂ s - 1‖ * ‖A₁‖ * ‖E₁ s‖ + ‖A₁‖ * ‖E₁ s - 1‖ := by
            refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _))
        _ ≤ a * s * K * a * K + a * (a * s * K) := by gcongr
    rw [hF'eq]
    calc ‖(1 - d) • (A₂ * (E₂ s * E₁ s - 1)) + d • (E₂ s * A₁ * E₁ s - A₁) - Ab * (Eb s - 1)‖
        ≤ (1 - d) * (‖A₂‖ * ‖E₂ s * E₁ s - 1‖) + d * ‖E₂ s * A₁ * E₁ s - A₁‖ +
            ‖Ab‖ * ‖Eb s - 1‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add ?_ ?_)) (norm_mul_le _ _))
          · rw [norm_smul, Real.norm_of_nonneg hd1']
            exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) hd1'
          · rw [norm_smul, Real.norm_of_nonneg hd0]
      _ ≤ 1 * (a * (a * s * K * K + a * s * K)) + 1 * (a * s * K * a * K + a * (a * s * K)) +
            a * (a * s * K) := by
          gcongr
          · linarith
      _ = s * c := by simp only [c]; ring
      _ ≤ c * T := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hsT (by positivity)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := T)
    (f := fun s => E₂ s * E₁ s - Eb s) (f' := F') (C := c * T)
    (fun s _ => (hF s).hasDerivWithinAt) hbound T ⟨hT.1, le_rfl⟩
  simp only [E₁, E₂, Eb, mul_zero, zero_smul, NormedSpace.exp_zero, mul_one, sub_self,
    sub_zero] at hmv
  calc ‖periodMap d T A₁ A₂ - NormedSpace.exp (T • avgMatrix d A₁ A₂)‖ ≤ c * T * T := hmv
    _ = c * T ^ 2 := by ring

omit [CompleteSpace 𝔸] [NormOneClass 𝔸] in
/-- `‖Ā‖ ≤ ‖A₁‖ + ‖A₂‖` for `d ∈ [0, 1]`. -/
@[powerlib_foundation] theorem norm_avgMatrix_le {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : 𝔸) : ‖avgMatrix d A₁ A₂‖ ≤ ‖A₁‖ + ‖A₂‖ := by
  have hd1' : 0 ≤ 1 - d := by linarith
  calc ‖avgMatrix d A₁ A₂‖ ≤ ‖d • A₁‖ + ‖(1 - d) • A₂‖ := norm_add_le _ _
    _ = d * ‖A₁‖ + (1 - d) * ‖A₂‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hd0, Real.norm_of_nonneg hd1']
    _ ≤ ‖A₁‖ + ‖A₂‖ := by nlinarith [norm_nonneg A₁, norm_nonneg A₂]

/-- One switching period: `‖e^{(1−d)TA₂} e^{dTA₁}‖ ≤ e^{(‖A₁‖ + ‖A₂‖)T}`. -/
@[powerlib_foundation] theorem norm_periodMap_le {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : 𝔸) {T : ℝ} (hT : 0 ≤ T) :
    ‖periodMap d T A₁ A₂‖ ≤ Real.exp ((‖A₁‖ + ‖A₂‖) * T) := by
  have hd1' : 0 ≤ 1 - d := by linarith
  calc ‖periodMap d T A₁ A₂‖
      ≤ ‖NormedSpace.exp (((1 - d) * T) • A₂)‖ * ‖NormedSpace.exp ((d * T) • A₁)‖ :=
        norm_mul_le _ _
    _ ≤ Real.exp (‖A₂‖ * ((1 - d) * T)) * Real.exp (‖A₁‖ * (d * T)) :=
        mul_le_mul (norm_exp_smul_le _ (mul_nonneg hd1' hT))
          (norm_exp_smul_le _ (mul_nonneg hd0 hT)) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (‖A₂‖ * ((1 - d) * T) + ‖A₁‖ * (d * T)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((‖A₁‖ + ‖A₂‖) * T) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (norm_nonneg A₂) (mul_nonneg hd0 hT),
          mul_nonneg (norm_nonneg A₁) (mul_nonneg hd1' hT)]

/-- `‖e^{sX}‖ ≤ e^{a}` and `‖e^{sX} − 1‖ ≤ a s e^{a}` for `‖X‖ ≤ a`, `0 ≤ s ≤ 1`. -/
@[powerlib_foundation] theorem exp_smul_bounds {X : 𝔸} {a s : ℝ} (hX : ‖X‖ ≤ a) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖NormedSpace.exp (s • X)‖ ≤ Real.exp a ∧
      ‖NormedSpace.exp (s • X) - 1‖ ≤ a * s * Real.exp a := by
  have ha : 0 ≤ a := (norm_nonneg X).trans hX
  have hexp : Real.exp (‖X‖ * s) ≤ Real.exp a :=
    Real.exp_le_exp.mpr (by nlinarith [norm_nonneg X])
  refine ⟨(norm_exp_smul_le X hs0).trans hexp, ?_⟩
  calc ‖NormedSpace.exp (s • X) - 1‖ ≤ ‖X‖ * s * Real.exp (‖X‖ * s) :=
        norm_exp_smul_sub_one_le X hs0
    _ ≤ a * s * Real.exp a := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hX hs0) hexp (Real.exp_pos _).le
        positivity

omit [NormOneClass 𝔸] in
/-- `e^{(r + s)X} = e^{rX} e^{sX}`. -/
@[powerlib_foundation] theorem exp_add_smul (X : 𝔸) (r s : ℝ) :
    NormedSpace.exp ((r + s) • X) = NormedSpace.exp (r • X) * NormedSpace.exp (s • X) := by
  rw [add_smul]
  refine NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl X).smul_left r).smul_right s) ?_ ?_ <;>
  · rw [NormedSpace.expSeries_radius_eq_top]
    simp

end Algebra

/-! ## Switched trajectories -/

section Switched

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `t ↦ e^{(t − a)A} v` solves `ẋ = A x`. -/
@[powerlib_foundation] theorem hasDerivAt_exp_mulVec (A : Matrix X X ℝ) (a : ℝ) (v : X → ℝ)
    (t : ℝ) :
    HasDerivAt (fun t => NormedSpace.exp ((t - a) • A) *ᵥ v)
      (A *ᵥ (NormedSpace.exp ((t - a) • A) *ᵥ v)) t := by
  have h := (hasDerivAt_exp_smul A (t - a)).scomp t ((hasDerivAt_id t).sub_const a)
  simp only [Function.comp_def, id, one_smul] at h
  let L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun N => N *ᵥ v
        map_add' := fun N N' => Matrix.add_mulVec N N' v
        map_smul' := fun c N => Matrix.smul_mulVec c N v }
  have h2 := L.hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt (fun t => NormedSpace.exp ((t - a) • A) *ᵥ v)
    ((A * NormedSpace.exp ((t - a) • A)) *ᵥ v) t at h2
  rw [Matrix.mulVec_mulVec]
  exact h2

/-- On an interval with a constant matrix, a solution is `x(t) = e^{(t − a)A} x(a)`. -/
@[powerlib_foundation] theorem const_solution_eq {A : Matrix X X ℝ} {x : ℝ → X → ℝ} {a b : ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => A *ᵥ y) (Icc a b)) {t : ℝ}
    (ht : t ∈ Icc a b) : x t = NormedSpace.exp ((t - a) • A) *ᵥ x a := by
  have hy : IsIntegralCurveOn (fun t => NormedSpace.exp ((t - a) • A) *ᵥ x a)
      (fun _ y => A *ᵥ y) (Icc a b) :=
    fun r _ => (hasDerivAt_exp_mulVec A a (x a) r).hasDerivWithinAt
  have hlip := Periodic.vecField_lipschitz (A := fun _ : ℝ => A) (M := ‖A‖) (fun _ => le_rfl)
  exact _root_.eqOn_of_isIntegralCurveOn_Icc (f := Periodic.vecField fun _ => A) hlip hx hy
    (by simp) ht

/-- Sampled switched trajectory: every trajectory of the ideal two-topology switched system
with duty ratio `d` and period `T` (`ẋ = A₁ x` on `[kT, kT + dT]`, `ẋ = A₂ x` on
`[kT + dT, (k + 1)T]`, one-sided derivatives at the switching instants) satisfies
`x(kT) = (e^{(1−d)TA₂} e^{dTA₁})^k x(0)`. -/
@[powerlib_foundation] theorem switched_sample {A₁ A₂ : Matrix X X ℝ} {d T : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (hT : 0 ≤ T) {x : ℝ → X → ℝ}
    (hx : ∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
      IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T)))
    (k : ℕ) : x (k * T) = periodMap d T A₁ A₂ ^ k *ᵥ x 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := hx k
    have hdT : 0 ≤ d * T := mul_nonneg hd0 hT
    have hdT' : 0 ≤ (1 - d) * T := mul_nonneg (by linarith) hT
    have e1 := const_solution_eq h1 (t := k * T + d * T) ⟨by linarith, le_rfl⟩
    have e2 := const_solution_eq h2 (t := (k + 1) * T) ⟨by nlinarith, le_rfl⟩
    rw [show (k * T + d * T) - k * T = d * T by ring] at e1
    rw [show ((k : ℝ) + 1) * T - (k * T + d * T) = (1 - d) * T by ring] at e2
    push_cast
    rw [e2, e1, ih, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pow_succ']
    rfl

/-- The averaged model `x̄̇ = Ā x̄` is solved by `x̄(t) = e^{tĀ} x₀`. -/
@[powerlib_foundation] theorem averaged_solves (d : ℝ) (A₁ A₂ : Matrix X X ℝ) (x₀ : X → ℝ)
    (t : ℝ) :
    HasDerivAt (fun t => NormedSpace.exp (t • avgMatrix d A₁ A₂) *ᵥ x₀)
      (avgMatrix d A₁ A₂ *ᵥ (NormedSpace.exp (t • avgMatrix d A₁ A₂) *ᵥ x₀)) t := by
  simpa using hasDerivAt_exp_mulVec (avgMatrix d A₁ A₂) 0 x₀ t

/-- **State-space averaging error** (Middlebrook–Ćuk, ideal switches, fixed duty ratio, CCM):
for every horizon `L` there is `C` such that, for all switching periods `T ∈ (0, 1]`, every
switched trajectory and every switching instant `kT ≤ L`,
`‖x(kT) − x̄(kT)‖ ≤ C T ‖x(0)‖`, where `x̄(t) = e^{tĀ} x(0)` solves the averaged model. -/
@[powerlib_foundation] theorem stateSpaceAveraging_error [Nonempty X] {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (A₁ A₂ : Matrix X X ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Ioc (0 : ℝ) 1, ∀ x : ℝ → X → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ k : ℕ, (k : ℝ) * T ≤ L →
        ‖x (k * T) - NormedSpace.exp (((k : ℝ) * T) • avgMatrix d A₁ A₂) *ᵥ x 0‖ ≤
          C * T * ‖x 0‖ := by
  obtain ⟨c, hc, hper⟩ := periodMap_sub_exp_le hd0 hd1 A₁ A₂
  set a := ‖A₁‖ + ‖A₂‖
  have ha0 : 0 ≤ a := by positivity
  have hd1' : 0 ≤ 1 - d := by linarith
  refine ⟨c * L * Real.exp (2 * a * L), by positivity, fun T hT x hx k hk => ?_⟩
  have hT0 : 0 ≤ T := hT.1.le
  set M := periodMap d T A₁ A₂
  set P := NormedSpace.exp (T • avgMatrix d A₁ A₂)
  have hsample := switched_sample hd0 hd1 hT0 hx k
  have hPk : NormedSpace.exp (((k : ℝ) * T) • avgMatrix d A₁ A₂) = P ^ k := by
    rw [mul_smul, Nat.cast_smul_eq_nsmul ℝ]
    exact NormedSpace.exp_nsmul k _
  -- operator bounds
  set B := Real.exp (2 * a * T)
  have hB1 : 1 ≤ B := Real.one_le_exp (by positivity)
  have hM : ‖M‖ ≤ B := by
    calc ‖M‖ ≤ ‖NormedSpace.exp (((1 - d) * T) • A₂)‖ * ‖NormedSpace.exp ((d * T) • A₁)‖ :=
          norm_mul_le _ _
      _ ≤ Real.exp (‖A₂‖ * ((1 - d) * T)) * Real.exp (‖A₁‖ * (d * T)) :=
          mul_le_mul (norm_exp_smul_le _ (by positivity)) (norm_exp_smul_le _ (by positivity))
            (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (‖A₂‖ * ((1 - d) * T) + ‖A₁‖ * (d * T)) := (Real.exp_add _ _).symm
      _ ≤ B := by
          apply Real.exp_le_exp.mpr
          have h1 : ‖A₂‖ * ((1 - d) * T) ≤ a * T := by
            have : (1 - d) * T ≤ T := by nlinarith
            nlinarith [norm_nonneg A₁, norm_nonneg A₂]
          have h2 : ‖A₁‖ * (d * T) ≤ a * T := by
            have : d * T ≤ T := by nlinarith
            nlinarith [norm_nonneg A₁, norm_nonneg A₂]
          linarith
  have hP : ‖P‖ ≤ B := by
    have hab : ‖avgMatrix d A₁ A₂‖ ≤ a := by
      calc ‖avgMatrix d A₁ A₂‖ ≤ ‖d • A₁‖ + ‖(1 - d) • A₂‖ := norm_add_le _ _
        _ = d * ‖A₁‖ + (1 - d) * ‖A₂‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hd0, Real.norm_of_nonneg hd1']
        _ ≤ a := by nlinarith [norm_nonneg A₁, norm_nonneg A₂]
    calc ‖P‖ ≤ Real.exp (‖avgMatrix d A₁ A₂‖ * T) := norm_exp_smul_le _ hT0
      _ ≤ B := Real.exp_le_exp.mpr (by nlinarith [norm_nonneg (avgMatrix d A₁ A₂)])
  have hdiff := hper T ⟨hT0, hT.2⟩
  have htel := norm_pow_sub_pow_le hB1 hM hP k
  have hBk : B ^ k ≤ Real.exp (2 * a * L) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmat : ‖M ^ k - P ^ k‖ ≤ c * L * Real.exp (2 * a * L) * T := by
    calc ‖M ^ k - P ^ k‖ ≤ k * B ^ k * ‖M - P‖ := htel
      _ ≤ k * Real.exp (2 * a * L) * (c * T ^ 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hBk (Nat.cast_nonneg k)) hdiff
            (norm_nonneg _) (by positivity)
      _ = (k * T) * (c * Real.exp (2 * a * L) * T) := by ring
      _ ≤ L * (c * Real.exp (2 * a * L) * T) := by
          apply mul_le_mul_of_nonneg_right hk (by positivity)
      _ = c * L * Real.exp (2 * a * L) * T := by ring
  rw [hsample, hPk, ← Matrix.sub_mulVec]
  calc ‖(M ^ k - P ^ k) *ᵥ x 0‖ ≤ ‖M ^ k - P ^ k‖ * ‖x 0‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ c * L * Real.exp (2 * a * L) * T * ‖x 0‖ :=
        mul_le_mul_of_nonneg_right hmat (norm_nonneg _)

/-- **Intra-period ripple.** There is `c`, depending only on `A₁`, `A₂`, such that for every
switching period `T ∈ (0, 1]`, every switched trajectory, every period `k` and every instant
`t ∈ [kT, (k + 1)T]`: `‖x(t) − x(kT)‖ ≤ c T ‖x(kT)‖`. -/
@[powerlib_foundation] theorem switched_ripple [Nonempty X] {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : Matrix X X ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T ∈ Ioc (0 : ℝ) 1, ∀ x : ℝ → X → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ k : ℕ, ∀ t ∈ Icc ((k : ℝ) * T) ((k + 1) * T),
        ‖x t - x (k * T)‖ ≤ c * T * ‖x (k * T)‖ := by
  set a := ‖A₁‖ + ‖A₂‖ with hadef
  have ha0 : 0 ≤ a := by positivity
  set K := Real.exp a
  have hK1 : 1 ≤ K := Real.one_le_exp ha0
  have ha1 : ‖A₁‖ ≤ a := by linarith [norm_nonneg A₂]
  have ha2 : ‖A₂‖ ≤ a := by linarith [norm_nonneg A₁]
  refine ⟨a * K * (K + 1), by positivity, fun T hT x hx k t ht => ?_⟩
  have hT0 : 0 ≤ T := hT.1.le
  obtain ⟨h1, h2⟩ := hx k
  have hdT : d * T ≤ T := by nlinarith
  have hdT0 : 0 ≤ d * T := mul_nonneg hd0 hT0
  rcases le_or_gt t (k * T + d * T) with htd | htd
  · -- ON interval
    have e := const_solution_eq h1 ⟨ht.1, htd⟩
    have hs0 : 0 ≤ t - k * T := by linarith [ht.1]
    have hs1 : t - k * T ≤ T := by linarith
    obtain ⟨-, hb⟩ := exp_smul_bounds ha1 hs0 (hs1.trans hT.2)
    have hdiff : x t - x (k * T) =
        (NormedSpace.exp ((t - k * T) • A₁) - 1) *ᵥ x (k * T) := by
      rw [e, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hdiff]
    calc ‖(NormedSpace.exp ((t - k * T) • A₁) - 1) *ᵥ x (k * T)‖
        ≤ ‖NormedSpace.exp ((t - k * T) • A₁) - 1‖ * ‖x (k * T)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ ≤ a * T * K * ‖x (k * T)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          refine hb.trans ?_
          gcongr
      _ ≤ a * K * (K + 1) * T * ‖x (k * T)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          nlinarith [mul_nonneg (mul_nonneg ha0 hT0) (by positivity : (0 : ℝ) ≤ K)]
  · -- OFF interval
    have e2 := const_solution_eq h2 ⟨htd.le, ht.2⟩
    have e1 := const_solution_eq h1 (t := k * T + d * T) ⟨by linarith, le_rfl⟩
    rw [show (k : ℝ) * T + d * T - k * T = d * T by ring] at e1
    set E₁ := NormedSpace.exp ((d * T) • A₁)
    set E₂ := NormedSpace.exp ((t - (k * T + d * T)) • A₂)
    have hs0 : 0 ≤ t - (k * T + d * T) := by linarith
    have hs1 : t - (k * T + d * T) ≤ T := by linarith [ht.2]
    obtain ⟨hE₁, hb₁⟩ := exp_smul_bounds ha1 hdT0 (hdT.trans hT.2)
    obtain ⟨-, hb₂⟩ := exp_smul_bounds ha2 hs0 (hs1.trans hT.2)
    have hdiff : x t - x (k * T) = (E₂ * E₁ - 1) *ᵥ x (k * T) := by
      rw [e2, e1, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
    have hprod : ‖E₂ * E₁ - 1‖ ≤ a * T * K * K + a * T * K := by
      have : E₂ * E₁ - 1 = (E₂ - 1) * E₁ + (E₁ - 1) := by noncomm_ring
      rw [this]
      calc ‖(E₂ - 1) * E₁ + (E₁ - 1)‖ ≤ ‖E₂ - 1‖ * ‖E₁‖ + ‖E₁ - 1‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ a * T * K * K + a * T * K := by
            have h1' : ‖E₂ - 1‖ ≤ a * T * K := hb₂.trans (by gcongr)
            have h2' : ‖E₁ - 1‖ ≤ a * T * K := hb₁.trans (by gcongr)
            gcongr
            exact hE₁
    rw [hdiff]
    calc ‖(E₂ * E₁ - 1) *ᵥ x (k * T)‖ ≤ ‖E₂ * E₁ - 1‖ * ‖x (k * T)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ ≤ (a * T * K * K + a * T * K) * ‖x (k * T)‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = a * K * (K + 1) * T * ‖x (k * T)‖ := by ring

/-- **State-space averaging error, uniform in time** (Middlebrook–Ćuk, ideal switches, fixed duty
ratio, CCM): for every horizon `L` there is `C` such that for all switching periods `T ∈ (0, 1]`,
every switched trajectory and **every** instant `t ∈ [0, L]` (not only the switching instants),
`‖x(t) − x̄(t)‖ ≤ C T ‖x(0)‖` with `x̄(t) = e^{tĀ} x(0)`: the averaged model tracks the switched
state including its intra-period ripple to `O(T)`. -/
@[powerlib_foundation] theorem stateSpaceAveraging_error_uniform [Nonempty X] {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (A₁ A₂ : Matrix X X ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Ioc (0 : ℝ) 1, ∀ x : ℝ → X → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ t ∈ Icc (0 : ℝ) L,
        ‖x t - NormedSpace.exp (t • avgMatrix d A₁ A₂) *ᵥ x 0‖ ≤ C * T * ‖x 0‖ := by
  obtain ⟨C₀, hC₀, herr⟩ := stateSpaceAveraging_error hd0 hd1 A₁ A₂ hL
  obtain ⟨c, hc, hrip⟩ := switched_ripple hd0 hd1 A₁ A₂
  set a := ‖A₁‖ + ‖A₂‖ with hadef
  have ha0 : 0 ≤ a := by positivity
  refine ⟨c * Real.exp (a * L) + C₀ + a * Real.exp a * Real.exp (a * L), by positivity, ?_⟩
  intro T hT x hx t ht
  have hT0 : 0 < T := hT.1
  set k := ⌊t / T⌋₊ with hkdef
  have hk1 : (k : ℝ) * T ≤ t := by
    have := Nat.floor_le (div_nonneg ht.1 hT0.le)
    rwa [le_div_iff₀ hT0] at this
  have hk2 : t < ((k : ℝ) + 1) * T := by
    have := Nat.lt_floor_add_one (t / T)
    rwa [div_lt_iff₀ hT0] at this
  have hkL : (k : ℝ) * T ≤ L := hk1.trans ht.2
  set Ab := avgMatrix d A₁ A₂
  have hAb : ‖Ab‖ ≤ a := norm_avgMatrix_le hd0 hd1 A₁ A₂
  -- (1) ripple
  have h1 := hrip T hT x hx k t ⟨hk1, hk2.le⟩
  have hxk : ‖x (k * T)‖ ≤ Real.exp (a * L) * ‖x 0‖ := by
    rw [switched_sample hd0 hd1 hT0.le hx k]
    calc ‖periodMap d T A₁ A₂ ^ k *ᵥ x 0‖ ≤ ‖periodMap d T A₁ A₂ ^ k‖ * ‖x 0‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ ≤ ‖periodMap d T A₁ A₂‖ ^ k * ‖x 0‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _)
      _ ≤ Real.exp (a * T) ^ k * ‖x 0‖ :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (norm_periodMap_le hd0 hd1 A₁ A₂ hT0.le) k)
            (norm_nonneg _)
      _ ≤ Real.exp (a * L) * ‖x 0‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          nlinarith
  -- (2) sampled error
  have h2 := herr T hT x hx k hkL
  -- (3) averaged model across the partial period
  set s := t - k * T
  have hs0 : 0 ≤ s := by simp only [s]; linarith
  have hsT : s ≤ T := by simp only [s]; linarith
  have hsplit : NormedSpace.exp (t • Ab) =
      NormedSpace.exp (s • Ab) * NormedSpace.exp (((k : ℝ) * T) • Ab) := by
    have h := exp_add_smul Ab s ((k : ℝ) * T)
    rw [show s + (k : ℝ) * T = t by simp only [s]; ring] at h
    exact h
  obtain ⟨-, hbs⟩ := exp_smul_bounds hAb hs0 (hsT.trans hT.2)
  have hkexp : ‖NormedSpace.exp (((k : ℝ) * T) • Ab)‖ ≤ Real.exp (a * L) :=
    (norm_exp_smul_le Ab (by positivity)).trans
      (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg Ab, mul_nonneg (Nat.cast_nonneg k) hT0.le]))
  have h3 : ‖NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0‖ ≤
      a * Real.exp a * Real.exp (a * L) * T * ‖x 0‖ := by
    have : NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0 =
        -((NormedSpace.exp (s • Ab) - 1) * NormedSpace.exp (((k : ℝ) * T) • Ab)) *ᵥ x 0 := by
      rw [hsplit, Matrix.neg_mulVec, sub_mul, one_mul, Matrix.sub_mulVec]; abel
    rw [this]
    calc ‖-((NormedSpace.exp (s • Ab) - 1) * NormedSpace.exp (((k : ℝ) * T) • Ab)) *ᵥ x 0‖
        ≤ ‖-((NormedSpace.exp (s • Ab) - 1) * NormedSpace.exp (((k : ℝ) * T) • Ab))‖ * ‖x 0‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ ≤ (a * s * Real.exp a) * Real.exp (a * L) * ‖x 0‖ := by
          rw [norm_neg]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (norm_mul_le _ _).trans (mul_le_mul hbs hkexp (norm_nonneg _) (by positivity))
      _ ≤ a * Real.exp a * Real.exp (a * L) * T * ‖x 0‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have : 0 ≤ a * Real.exp a * Real.exp (a * L) := by positivity
          nlinarith
  -- combine
  have hsum : x t - NormedSpace.exp (t • Ab) *ᵥ x 0 =
      (x t - x (k * T)) + (x (k * T) - NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0) +
        (NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0) := by
    abel
  rw [hsum]
  calc ‖(x t - x (k * T)) + (x (k * T) - NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0) +
        (NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0)‖
      ≤ ‖x t - x (k * T)‖ + ‖x (k * T) - NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0‖ +
        ‖NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0‖ :=
        norm_add₃_le
    _ ≤ c * T * (Real.exp (a * L) * ‖x 0‖) + C₀ * T * ‖x 0‖ +
        a * Real.exp a * Real.exp (a * L) * T * ‖x 0‖ := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left hxk (by positivity))
    _ = (c * Real.exp (a * L) + C₀ + a * Real.exp a * Real.exp (a * L)) * T * ‖x 0‖ := by ring

end Switched

end powerlib.Averaging
