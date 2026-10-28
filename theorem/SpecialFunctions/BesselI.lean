import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Modified Bessel functions `I₀`, `I₁` (foundation)

Mathlib has no modified Bessel functions; they are defined here by their power series:
`besselI0 z = Σ_k (z/2)^{2k}/(k!)²`, `besselI1 z = Σ_k (z/2)^{2k+1}/(k!(k+1)!)`
(`besselI0_eq`, `besselI1_eq`), through the entire series `besselSeries0 w = Σ w^k/(k!)²` and
`besselSeries1 w = Σ w^k/(k!(k+1)!)` at `w = z²/4`.

Scope.
* Static special-function analysis; nothing here describes a physical system and no model family
  is defined.

Source: work-sync `theory/T-cable.md` §1.2.1 (the Bessel ratio `I₀(m r_c)/I₁(m r_c)` of the
solid-conductor surface impedance).

Results.
* `hasSum_exp_tail`, `norm_tsum_sub_two_le`: a series dominated termwise by the exponential series
  differs from its first two terms by at most `‖w‖²` (`‖w‖ ≤ 1`).
* `besselSeries0_sub_le`, `besselSeries1_sub_le`: `‖f₀(w) − 1 − w‖, ‖f₁(w) − 1 − w/2‖ ≤ ‖w‖²`;
  `besselRatio_sub_le`: `‖f₀(w)/f₁(w) − 1 − w/2‖ ≤ 6‖w‖²` for `‖w‖ ≤ 1/4`.
* Integral representation: Wallis integrals `integral_cos_pow_even` (`∫₀^π cos^{2k} =
  π(2k)!/(4^k(k!)²)`), `integral_cos_pow_odd` (`= 0`), termwise integration of the exponential
  series (`hasSum_integral_cexp_mul_cos`), hence `integral_cexp_cos` (`∫₀^π e^{z cos θ} dθ =
  π I₀(z)`) and `integral_cexp_cos_mul_cos` (`∫₀^π e^{z cos θ} cos θ dθ = π I₁(z)`), for every
  complex `z`.
* Laplace estimate (`x = Re z > 0`): `integral_cexp_neg_mul_one_sub_cos(_mul)` write
  `e^{−z}π I₀` and `e^{−z}π(I₀ − I₁)` as `∫₀^π e^{−z(1−cos θ)}(1, 1 − cos θ) dθ`;
  `norm_integral_cexp_one_sub_cos_mul_le` (the second is `O(x^{−3/2})`),
  `norm_integral_cexp_one_sub_cos_sub_gaussian_le` (the first differs from the complex Gaussian
  `∫₀^∞ e^{−zθ²/2} = (2π/z)^{1/2}/2` by `O(‖z‖ x^{−5/2} + e^{−xπ²/4} x^{−1/2})`),
  `norm_integral_gaussian_half`; elementary bounds `norm_cexp_sub_one_le_of_re_nonpos`,
  `norm_cexp_sub_cexp_le`, `sq_div_two_sub_one_sub_cos_le`, `sq_mul_exp_le`,
  `pow_four_mul_exp_le`, `integral_exp_neg_mul_sq_le`.
* **Laplace bounds in a sector**: `besselI_laplace_le` (for every `K > 0` there is `C ≥ 0` with
  `‖e^{−z}π I₀(z) − G(z)‖ ≤ (C/x)‖G(z)‖` and `‖e^{−z}π(I₀(z) − I₁(z))‖ ≤ (C/x)‖G(z)‖`,
  `G(z) = ∫₀^∞ e^{−zθ²/2}`, whenever `x = Re z > 0`, `‖z‖ ≤ K x`).
* **Large argument**: `besselI0_div_besselI1_sub_one_le` (for every `K > 0` there are `C`, `x₀`
  with `I₀(z), I₁(z) ≠ 0` and `‖I₀(z)/I₁(z) − 1‖ ≤ C/Re z` whenever `Re z ≥ x₀`,
  `‖z‖ ≤ K Re z`), `tendsto_besselI0_div_besselI1` (`I₀/I₁ → 1` as `z → ∞` in a sector);
  along the ray `(1 + i)s`: `one_add_I_mul_re`, `norm_one_add_I_mul_le`.

The second-kind functions `K₀`, `K₁` are in `theorem/SpecialFunctions/BesselK.lean`; the solid
conductor surface impedance built on `I₀/I₁` is in `theorem/Line/CableBessel.lean`.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Filter Topology Asymptotics
open scoped Nat

/-- Even series `I₀`: `besselSeries0 w = Σ_k w^k/(k!)²`, so `I₀(z) = besselSeries0 (z²/4)`. -/
def besselSeries0 (w : ℂ) : ℂ := ∑' k : ℕ, w ^ k / ((k ! : ℂ) ^ 2)

/-- Odd series `I₁`: `besselSeries1 w = Σ_k w^k/(k!(k+1)!)`, so
`I₁(z) = (z/2) besselSeries1 (z²/4)`. -/
def besselSeries1 (w : ℂ) : ℂ := ∑' k : ℕ, w ^ k / ((k ! : ℂ) * ((k + 1) ! : ℂ))

/-- The exponential tail `Σ_{k ≥ 2} x^k/k! = eˣ − 1 − x`. -/
@[tmio T, powerlib_foundation] theorem hasSum_exp_tail (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 2) / ((k + 2) ! : ℝ)) (Real.exp x - 1 - x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => x ^ n / (n ! : ℝ)) 2).mpr h
  simpa [Finset.sum_range_succ, sub_sub] using h2

/-- A series dominated termwise by `‖w‖^k/k!` from `k = 2` on: its value minus the first two
terms is at most `‖w‖²` for `‖w‖ ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem norm_tsum_sub_two_le {g : ℕ → ℂ} {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hg : ∀ k, ‖g k‖ ≤ ‖w‖ ^ k / (k ! : ℝ)) :
    ‖(∑' k, g k) - g 0 - g 1‖ ≤ ‖w‖ ^ 2 := by
  have hsum : Summable g :=
    Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖w‖) hg
  have hsplit := hsum.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  have htail : (∑' k, g k) - g 0 - g 1 = ∑' k, g (k + 2) := by
    rw [← hsplit]; ring
  rw [htail]
  have hs2 : Summable fun k => ‖g (k + 2)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hg (k + 2))
      (hasSum_exp_tail ‖w‖).summable
  calc ‖∑' k, g (k + 2)‖ ≤ ∑' k, ‖g (k + 2)‖ := norm_tsum_le_tsum_norm hs2
    _ ≤ ∑' k : ℕ, ‖w‖ ^ (k + 2) / ((k + 2) ! : ℝ) :=
        hs2.tsum_le_tsum (fun k => hg (k + 2)) (hasSum_exp_tail ‖w‖).summable
    _ = Real.exp ‖w‖ - 1 - ‖w‖ := (hasSum_exp_tail ‖w‖).tsum_eq
    _ ≤ ‖w‖ ^ 2 := by
        have := Real.abs_exp_sub_one_sub_id_le (x := ‖w‖) (by rw [abs_norm]; exact hw)
        exact (le_abs_self _).trans this

/-- `‖I₀-series(w) − 1 − w‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem besselSeries0_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖besselSeries0 w - 1 - w‖ ≤ ‖w‖ ^ 2 := by
  have h := norm_tsum_sub_two_le (g := fun k : ℕ => w ^ k / ((k ! : ℂ) ^ 2)) hw (fun k => by
    rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
    have hk : (1 : ℝ) ≤ (k ! : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity) hk0]
    have : (k ! : ℝ) ≤ (k ! : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity))
  simpa [besselSeries0] using h

/-- `‖I₁-series(w) − 1 − w/2‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem besselSeries1_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖besselSeries1 w - 1 - w / 2‖ ≤ ‖w‖ ^ 2 := by
  have h := norm_tsum_sub_two_le (g := fun k : ℕ => w ^ k / ((k ! : ℂ) * ((k + 1) ! : ℂ))) hw
    (fun k => by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
      have hk1 : (1 : ℝ) ≤ ((k + 1) ! : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
      rw [div_le_div_iff₀ (by positivity) hk0]
      have : (k ! : ℝ) ≤ (k ! : ℝ) * ((k + 1) ! : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity))
  have e : (∑' k : ℕ, w ^ k / ((k ! : ℂ) * ((k + 1) ! : ℂ))) -
        w ^ 0 / ((0 ! : ℂ) * ((0 + 1) ! : ℂ)) - w ^ 1 / ((1 ! : ℂ) * ((1 + 1) ! : ℂ)) =
      besselSeries1 w - 1 - w / 2 := by
    simp [besselSeries1, Nat.factorial]
  rw [e] at h
  exact h

/-- Modified Bessel function of the first kind, order zero: `I₀(z) = Σ_k (z/2)^{2k}/(k!)²`. -/
def besselI0 (z : ℂ) : ℂ := besselSeries0 (z ^ 2 / 4)

/-- Modified Bessel function of the first kind, order one: `I₁(z) = Σ_k (z/2)^{2k+1}/(k!(k+1)!)`. -/
def besselI1 (z : ℂ) : ℂ := z / 2 * besselSeries1 (z ^ 2 / 4)

/-- `I₀` is the standard power series. -/
@[tmio T, powerlib_foundation] theorem besselI0_eq (z : ℂ) :
    besselI0 z = ∑' k : ℕ, (z / 2) ^ (2 * k) / ((k ! : ℂ) ^ 2) := by
  unfold besselI0 besselSeries0
  congr 1; funext k
  rw [pow_mul]; ring

/-- `I₁` is the standard power series. -/
@[tmio T, powerlib_foundation] theorem besselI1_eq (z : ℂ) :
    besselI1 z = ∑' k : ℕ, (z / 2) ^ (2 * k + 1) / ((k ! : ℂ) * ((k + 1) ! : ℂ)) := by
  unfold besselI1 besselSeries1
  rw [← tsum_mul_left]
  congr 1; funext k
  rw [pow_add, pow_mul]; ring

/-- `I₀/I₁` series ratio: `‖f₀(w)/f₁(w) − 1 − w/2‖ ≤ 6 ‖w‖²` for `‖w‖ ≤ 1/4`. -/
@[tmio T, powerlib_foundation] theorem besselRatio_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    ‖besselSeries0 w / besselSeries1 w - 1 - w / 2‖ ≤ 6 * ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ ≤ 1 := by linarith
  have h0 := besselSeries0_sub_le hw1
  have h1 := besselSeries1_sub_le hw1
  set f0 := besselSeries0 w
  set f1 := besselSeries1 w
  have hn := norm_nonneg w
  have hf1 : 1 / 2 ≤ ‖f1‖ := by
    have : ‖(1 : ℂ) + w / 2‖ ≥ 1 - ‖w‖ / 2 := by
      have := norm_sub_norm_le (1 : ℂ) (-(w / 2))
      rw [sub_neg_eq_add, norm_neg, norm_div, Complex.norm_two, norm_one] at this
      linarith
    have := norm_sub_norm_le ((1 : ℂ) + w / 2) (-(f1 - 1 - w / 2))
    rw [norm_neg, sub_neg_eq_add, show (1 : ℂ) + w / 2 + (f1 - 1 - w / 2) = f1 by ring] at this
    nlinarith
  have hf1' : f1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hf1; linarith
  have hnum : ‖f0 - (1 + w / 2) * f1‖ ≤ 3 * ‖w‖ ^ 2 := by
    have e : f0 - (1 + w / 2) * f1 = (f0 - 1 - w) - w ^ 2 / 4 - (1 + w / 2) * (f1 - 1 - w / 2) := by
      ring
    rw [e]
    have hq : ‖(1 : ℂ) + w / 2‖ ≤ 1 + ‖w‖ / 2 := by
      have := norm_add_le (1 : ℂ) (w / 2)
      rwa [norm_one, norm_div, Complex.norm_two] at this
    calc ‖(f0 - 1 - w) - w ^ 2 / 4 - (1 + w / 2) * (f1 - 1 - w / 2)‖ ≤
          ‖f0 - 1 - w‖ + ‖w ^ 2 / 4‖ + ‖(1 + w / 2) * (f1 - 1 - w / 2)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 / 4 + (1 + ‖w‖ / 2) * ‖w‖ ^ 2 := by
          rw [norm_mul, norm_div, norm_pow, show ‖(4 : ℂ)‖ = 4 by simp]
          gcongr
      _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
  have e2 : f0 / f1 - 1 - w / 2 = (f0 - (1 + w / 2) * f1) / f1 := by
    field_simp
    ring
  rw [e2, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg ‖w‖]

/-! ## Integral representation (Wallis integrals, termwise integration) -/

open MeasureTheory Set intervalIntegral

/-- `∫₀^π cos^{n+2} = (n+1)/(n+2) ∫₀^π cosⁿ`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_pow_add_two (n : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (n + 2) =
      (n + 1) / (n + 2) * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ n := by
  rw [integral_cos_pow]; simp

/-- `∫₀^π cos^{2k+1} = 0`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_pow_odd (k : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (2 * k + 1) = 0 := by
  induction k with
  | zero => simp [integral_cos]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, integral_cos_pow_add_two, ih, mul_zero]

/-- Wallis: `∫₀^π cos^{2k} = π (2k)!/(4^k (k!)²)`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_pow_even (k : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (2 * k) =
      Real.pi * (2 * k)! / (4 ^ k * ((k ! : ℝ)) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_cos_pow_add_two, ih,
      show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ (2 * k),
      Nat.factorial_succ k]
    push_cast
    field_simp
    ring

/-- Termwise integration of the exponential series: for a continuous real `g` with `|g| ≤ 1`
on `[0, π]`, `∫₀^π e^{z cos θ} g(θ) dθ = Σ_n zⁿ/n! ∫₀^π cosⁿθ g(θ) dθ`. -/
@[tmio T, powerlib_foundation] theorem hasSum_integral_cexp_mul_cos {g : ℝ → ℝ} (hg : Continuous g)
    (hg1 : ∀ θ, |g θ| ≤ 1) (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n ! : ℂ) *
        ((∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ n * g θ : ℝ) : ℂ))
      (∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * Real.cos θ) * g θ) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := Real.pi)
    (F := fun (n : ℕ) (θ : ℝ) => (z * Real.cos θ) ^ n / (n ! : ℂ) * g θ)
    (f := fun θ => Complex.exp (z * Real.cos θ) * g θ)
    (fun n _ => ‖z‖ ^ n / (n ! : ℝ)) (fun n => by
      apply Continuous.aestronglyMeasurable; fun_prop)
    (fun n => Eventually.of_forall fun θ _ => by
      rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow]
      have h1 : |Real.cos θ| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ)
      have h2 := hg1 θ
      have hp : 0 ≤ ‖z‖ ^ n / (n ! : ℝ) := by positivity
      calc ‖z‖ ^ n * |Real.cos θ| ^ n / (n ! : ℝ) * |g θ| ≤ ‖z‖ ^ n * 1 / (n ! : ℝ) * 1 := by
            gcongr
        _ = ‖z‖ ^ n / (n ! : ℝ) := by ring)
    (Eventually.of_forall fun θ _ => Real.summable_pow_div_factorial ‖z‖)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ => by
      have := (NormedSpace.expSeries_div_hasSum_exp (z * Real.cos θ)).mul_right (g θ : ℂ)
      rwa [← Complex.exp_eq_exp_ℂ] at this)
  refine h.congr_fun fun n => ?_
  rw [← intervalIntegral.integral_ofReal]
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext θ
  push_cast
  ring

/-- **Integral representation of `I₀`**: `∫₀^π e^{z cos θ} dθ = π I₀(z)`. -/
@[tmio T, powerlib_foundation] theorem integral_cexp_cos (z : ℂ) :
    ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * Real.cos θ) = Real.pi * besselI0 z := by
  have h := hasSum_integral_cexp_mul_cos (g := fun _ => 1) continuous_const (by simp) z
  simp only [mul_one, Complex.ofReal_one] at h
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      z ^ n / (n ! : ℂ) * ((∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ n : ℝ) : ℂ) = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact absurd ⟨k, show 2 * k = n by omega⟩ hn
      · exact ⟨k, hk⟩
    rw [integral_cos_pow_odd]; simp
  have h2 := (Function.Injective.hasSum_iff (fun a b hab => by simpa using hab) hodd).mpr h
  have h3 : HasSum (fun k : ℕ => (Real.pi : ℂ) * ((z ^ 2 / 4) ^ k / ((k ! : ℂ) ^ 2)))
      (∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * Real.cos θ)) := by
    refine h2.congr_fun fun k => ?_
    simp only [Function.comp_apply]
    rw [integral_cos_pow_even]
    have hf : (((2 * k)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : ((k ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    rw [div_pow, ← pow_mul]
    field_simp
  rw [besselI0, besselSeries0, ← h3.tsum_eq, tsum_mul_left]

/-- **Integral representation of `I₁`**: `∫₀^π e^{z cos θ} cos θ dθ = π I₁(z)`. -/
@[tmio T, powerlib_foundation] theorem integral_cexp_cos_mul_cos (z : ℂ) :
    ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * Real.cos θ) * Real.cos θ =
      Real.pi * besselI1 z := by
  have h := hasSum_integral_cexp_mul_cos (g := Real.cos) Real.continuous_cos Real.abs_cos_le_one z
  simp only [← pow_succ] at h
  have heven : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1),
      z ^ n / (n ! : ℂ) * ((∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (n + 1) : ℝ) : ℂ) = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k, by omega⟩
      · exact absurd ⟨k, hk.symm⟩ hn
    rw [integral_cos_pow_odd]; simp
  have h2 := (Function.Injective.hasSum_iff (fun a b hab => by simpa using hab) heven).mpr h
  have h3 : HasSum (fun k : ℕ => (Real.pi : ℂ) * (z / 2) *
        ((z ^ 2 / 4) ^ k / ((k ! : ℂ) * ((k + 1) ! : ℂ))))
      (∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * Real.cos θ) * Real.cos θ) := by
    refine h2.congr_fun fun k => ?_
    simp only [Function.comp_apply]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, integral_cos_pow_even,
      show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ k]
    have hf : (((2 * k + 1)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : ((k ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    rw [div_pow, ← pow_mul]
    field_simp
    ring
  rw [besselI1, besselSeries1, ← h3.tsum_eq, tsum_mul_left, mul_assoc]

/-! ## Elementary bounds for the Laplace estimate -/

/-- `‖e^w − 1‖ ≤ ‖w‖` when `Re w ≤ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_cexp_sub_one_le_of_re_nonpos {w : ℂ} (hw : w.re ≤ 0) :
    ‖Complex.exp w - 1‖ ≤ ‖w‖ := by
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => Complex.exp (s * w))
      (w * Complex.exp (s * w)) (Icc 0 1) s := by
    intro s _
    have := ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const w).cexp
    simp only [Complex.ofRealCLM_apply] at this
    exact (this.congr_deriv (by push_cast; ring)).hasDerivWithinAt
  have hb : ∀ s ∈ Ico (0 : ℝ) 1, ‖w * Complex.exp (s * w)‖ ≤ ‖w‖ := by
    intro s hs
    rw [norm_mul, Complex.norm_exp]
    have : (s * w : ℂ).re = s * w.re := by simp
    rw [this]
    have : Real.exp (s * w.re) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs.1 hw)
    calc ‖w‖ * Real.exp (s * w.re) ≤ ‖w‖ * 1 := by gcongr
      _ = ‖w‖ := mul_one _
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb 1 ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- `‖e^a − e^b‖ ≤ ‖a − b‖ e^{Re a}` when `Re b ≤ Re a`. -/
@[tmio T, powerlib_foundation] theorem norm_cexp_sub_cexp_le {a b : ℂ} (h : b.re ≤ a.re) :
    ‖Complex.exp a - Complex.exp b‖ ≤ ‖a - b‖ * Real.exp a.re := by
  have e : Complex.exp a - Complex.exp b = -(Complex.exp a * (Complex.exp (b - a) - 1)) := by
    rw [Complex.exp_sub]; field_simp; ring
  rw [e, norm_neg, norm_mul, Complex.norm_exp, mul_comm]
  have := norm_cexp_sub_one_le_of_re_nonpos (w := b - a) (by simp; linarith)
  rw [norm_sub_rev b a] at this
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- `θ²/2 − (1 − cos θ) ≤ θ⁴/24` for `θ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem sq_div_two_sub_one_sub_cos_le {θ : ℝ} (hθ : 0 ≤ θ) :
    θ ^ 2 / 2 - (1 - Real.cos θ) ≤ θ ^ 4 / 24 := by
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    conv_lhs => rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  have h1 := Real.sin_le (show 0 ≤ θ / 2 by positivity)
  have h2 := Real.sin_ge_sub_cube (show 0 ≤ θ / 2 by positivity)
  have h3 : -(θ / 2) ≤ Real.sin (θ / 2) := by
    have := Real.abs_sin_le_abs (x := θ / 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ θ / 2)] at this
    linarith [(abs_le.mp this).1]
  rw [hc]
  have ha : 0 ≤ θ / 2 - Real.sin (θ / 2) := by linarith
  have hb : 0 ≤ θ / 2 + Real.sin (θ / 2) := by linarith
  have hab : (θ / 2 - Real.sin (θ / 2)) * (θ / 2 + Real.sin (θ / 2)) ≤ (θ / 2) ^ 3 / 6 * θ :=
    mul_le_mul (by linarith) (by linarith) hb (by positivity)
  nlinarith [hab]

/-- `θ² e^{−bθ²} ≤ (2/b) e^{−(b/2)θ²}` (`b > 0`). -/
@[tmio T, powerlib_foundation] theorem sq_mul_exp_le {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    θ ^ 2 * Real.exp (-b * θ ^ 2) ≤ 2 / b * Real.exp (-(b / 2) * θ ^ 2) := by
  have hv := Real.add_one_le_exp (b / 2 * θ ^ 2)
  have e : Real.exp (-b * θ ^ 2) = Real.exp (-(b / 2) * θ ^ 2) * Real.exp (-(b / 2 * θ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hE : 0 < Real.exp (-(b / 2) * θ ^ 2) := Real.exp_pos _
  have key : θ ^ 2 * Real.exp (-(b / 2 * θ ^ 2)) ≤ 2 / b := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hb]
    nlinarith [sq_nonneg θ]
  calc θ ^ 2 * (Real.exp (-(b / 2) * θ ^ 2) * Real.exp (-(b / 2 * θ ^ 2))) =
        (θ ^ 2 * Real.exp (-(b / 2 * θ ^ 2))) * Real.exp (-(b / 2) * θ ^ 2) := by ring
    _ ≤ 2 / b * Real.exp (-(b / 2) * θ ^ 2) := mul_le_mul_of_nonneg_right key hE.le

/-- `θ⁴ e^{−bθ²} ≤ (8/b²) e^{−(b/2)θ²}` (`b > 0`). -/
@[tmio T, powerlib_foundation] theorem pow_four_mul_exp_le {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    θ ^ 4 * Real.exp (-b * θ ^ 2) ≤ 8 / b ^ 2 * Real.exp (-(b / 2) * θ ^ 2) := by
  have hv := Real.quadratic_le_exp_of_nonneg (show 0 ≤ b / 2 * θ ^ 2 by positivity)
  have e : Real.exp (-b * θ ^ 2) = Real.exp (-(b / 2) * θ ^ 2) * Real.exp (-(b / 2 * θ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hE : 0 < Real.exp (-(b / 2) * θ ^ 2) := Real.exp_pos _
  have key : θ ^ 4 * Real.exp (-(b / 2 * θ ^ 2)) ≤ 8 / b ^ 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith [sq_nonneg θ, sq_nonneg (θ ^ 2), sq_nonneg (b * θ ^ 2)]
  calc θ ^ 4 * (Real.exp (-(b / 2) * θ ^ 2) * Real.exp (-(b / 2 * θ ^ 2))) =
        (θ ^ 4 * Real.exp (-(b / 2 * θ ^ 2))) * Real.exp (-(b / 2) * θ ^ 2) := by ring
    _ ≤ 8 / b ^ 2 * Real.exp (-(b / 2) * θ ^ 2) := mul_le_mul_of_nonneg_right key hE.le

/-- `∫₀^π e^{−βθ²} ≤ √(π/β)/2` (`β > 0`). -/
@[tmio T, powerlib_foundation] theorem integral_exp_neg_mul_sq_le {β : ℝ} (hβ : 0 < β) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-β * θ ^ 2) ≤ Real.sqrt (Real.pi / β) / 2 := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_gaussian_Ioi]
  exact setIntegral_mono_set (integrable_exp_neg_mul_sq hβ).integrableOn
    (Eventually.of_forall fun θ => (Real.exp_pos _).le) Ioc_subset_Ioi_self.eventuallyLE

/-! ## Large argument: `I₀(z)/I₁(z) → 1` in a sector -/

/-- `∫₀^π e^{−z(1−cos θ)} dθ = e^{−z} π I₀(z)`. -/
@[tmio T, powerlib_foundation] theorem integral_cexp_neg_mul_one_sub_cos (z : ℂ) :
    ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) =
      Complex.exp (-z) * (Real.pi * besselI0 z) := by
  rw [← integral_cexp_cos, ← intervalIntegral.integral_const_mul]
  congr 1; funext θ
  rw [← Complex.exp_add]; push_cast; ring_nf

/-- `∫₀^π e^{−z(1−cos θ)}(1 − cos θ) dθ = e^{−z} π (I₀(z) − I₁(z))`. -/
@[tmio T, powerlib_foundation] theorem integral_cexp_neg_mul_one_sub_cos_mul (z : ℂ) :
    ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) *
        ((1 - Real.cos θ : ℝ) : ℂ) =
      Complex.exp (-z) * (Real.pi * besselI0 z - Real.pi * besselI1 z) := by
  rw [← integral_cexp_cos, ← integral_cexp_cos_mul_cos, ← intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), ← intervalIntegral.integral_const_mul]
  congr 1; funext θ
  rw [show -z * ((1 - Real.cos θ : ℝ) : ℂ) = -z + z * Real.cos θ by push_cast; ring,
    Complex.exp_add]
  push_cast; ring

/-- Upper bound for the `I₀ − I₁` integral: `x = Re z > 0`,
`‖∫₀^π e^{−z(1−cos θ)}(1 − cos θ)‖ ≤ (π²/(2x)) · √(π/(x/π²))/2`. -/
@[tmio T, powerlib_foundation] theorem norm_integral_cexp_one_sub_cos_mul_le {z : ℂ} (hx : 0 < z.re) :
    ‖∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) *
        ((1 - Real.cos θ : ℝ) : ℂ)‖ ≤
      Real.pi ^ 2 / (2 * z.re) * (Real.sqrt (Real.pi / (z.re / Real.pi ^ 2)) / 2) := by
  set x := z.re
  set b := 2 * x / Real.pi ^ 2 with hbdef
  have hb : 0 < b := by positivity
  have hb2 : b / 2 = x / Real.pi ^ 2 := by rw [hbdef]; ring
  refine (intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
    (g := fun θ => 1 / b * Real.exp (-(b / 2) * θ ^ 2)) (Eventually.of_forall fun θ hθ => ?_)
    (Continuous.intervalIntegrable (by fun_prop) _ _)).trans ?_
  · have hθπ : |θ| ≤ Real.pi := by rw [abs_of_pos hθ.1]; exact hθ.2
    have hu0 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    have hulo : 2 / Real.pi ^ 2 * θ ^ 2 ≤ 1 - Real.cos θ := by
      linarith [Real.cos_le_one_sub_mul_cos_sq hθπ]
    have huhi : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    have hre : (-z * ((1 - Real.cos θ : ℝ) : ℂ)).re = -(x * (1 - Real.cos θ)) := by
      rw [Complex.re_mul_ofReal, Complex.neg_re]; ring
    rw [hre]
    have he : Real.exp (-(x * (1 - Real.cos θ))) ≤ Real.exp (-b * θ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have : b * θ ^ 2 ≤ x * (1 - Real.cos θ) := by
        rw [hbdef]
        have := mul_le_mul_of_nonneg_left hulo hx.le
        calc 2 * x / Real.pi ^ 2 * θ ^ 2 = x * (2 / Real.pi ^ 2 * θ ^ 2) := by ring
          _ ≤ _ := this
      linarith
    have hsq := sq_mul_exp_le hb θ
    calc Real.exp (-(x * (1 - Real.cos θ))) * (1 - Real.cos θ) ≤
          Real.exp (-b * θ ^ 2) * (θ ^ 2 / 2) :=
          mul_le_mul he huhi hu0 (Real.exp_pos _).le
      _ = (θ ^ 2 * Real.exp (-b * θ ^ 2)) / 2 := by ring
      _ ≤ (2 / b * Real.exp (-(b / 2) * θ ^ 2)) / 2 := by gcongr
      _ = 1 / b * Real.exp (-(b / 2) * θ ^ 2) := by ring
  · rw [intervalIntegral.integral_const_mul]
    have := integral_exp_neg_mul_sq_le (β := b / 2) (by positivity)
    rw [hb2] at this
    calc 1 / b * ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-(b / 2) * θ ^ 2) ≤
          1 / b * (Real.sqrt (Real.pi / (x / Real.pi ^ 2)) / 2) := by
          rw [hb2]; gcongr
      _ = _ := by rw [hbdef]; field_simp

/-- Comparison with the Gaussian: `x = Re z > 0`,
`‖∫₀^π e^{−z(1−cos θ)} − ∫₀^∞ e^{−zθ²/2}‖ ≤ ‖z‖π⁴/(12x²) · √(π/(x/π²))/2 + e^{−xπ²/4} √(π/(x/4))/2`.
-/
@[tmio T, powerlib_foundation] theorem norm_integral_cexp_one_sub_cos_sub_gaussian_le {z : ℂ}
    (hx : 0 < z.re) :
    ‖(∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))) -
        ∫ θ in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (θ : ℂ) ^ 2)‖ ≤
      ‖z‖ * Real.pi ^ 4 / (12 * z.re ^ 2) * (Real.sqrt (Real.pi / (z.re / Real.pi ^ 2)) / 2) +
        Real.exp (-(z.re * Real.pi ^ 2 / 4)) * (Real.sqrt (Real.pi / (z.re / 4)) / 2) := by
  set x := z.re with hxdef
  have hz2 : 0 < (z / 2).re := by simp [x] at hx ⊢; linarith
  have hint := integrable_cexp_neg_mul_sq hz2
  rw [← intervalIntegral.integral_interval_add_Ioi' (a := 0) (b := Real.pi)
    hint.intervalIntegrable hint.integrableOn]
  rw [show ∀ A G T : ℂ, A - (G + T) = (A - G) - T from fun A G T => by ring,
    ← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      hint.intervalIntegrable]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · -- the compact part
    set b := 2 * x / Real.pi ^ 2 with hbdef
    have hb : 0 < b := by positivity
    have hb2 : b / 2 = x / Real.pi ^ 2 := by rw [hbdef]; ring
    refine (intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
      (g := fun θ => ‖z‖ / 24 * (8 / b ^ 2) * Real.exp (-(b / 2) * θ ^ 2))
      (Eventually.of_forall fun θ hθ => ?_)
      (Continuous.intervalIntegrable (by fun_prop) _ _)).trans ?_
    · have hθπ : |θ| ≤ Real.pi := by rw [abs_of_pos hθ.1]; exact hθ.2
      have hulo : 2 / Real.pi ^ 2 * θ ^ 2 ≤ 1 - Real.cos θ := by
        linarith [Real.cos_le_one_sub_mul_cos_sq hθπ]
      have huhi : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
      have hd := sq_div_two_sub_one_sub_cos_le hθ.1.le
      have hrea : (-z * ((1 - Real.cos θ : ℝ) : ℂ)).re = -(x * (1 - Real.cos θ)) := by
        rw [Complex.re_mul_ofReal, Complex.neg_re]; ring
      have hreb : (-(z / 2) * (θ : ℂ) ^ 2).re = -(x * (θ ^ 2 / 2)) := by
        rw [← Complex.ofReal_pow, Complex.re_mul_ofReal, Complex.neg_re]; simp [x]; ring
      have hle := norm_cexp_sub_cexp_le (a := -z * ((1 - Real.cos θ : ℝ) : ℂ))
        (b := -(z / 2) * (θ : ℂ) ^ 2) (by rw [hrea, hreb]; nlinarith)
      have hdiff : -z * ((1 - Real.cos θ : ℝ) : ℂ) - -(z / 2) * (θ : ℂ) ^ 2 =
          z * ((θ ^ 2 / 2 - (1 - Real.cos θ) : ℝ) : ℂ) := by push_cast; ring
      rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ θ ^ 2 / 2 - (1 - Real.cos θ)), hrea] at hle
      refine hle.trans ?_
      have he : Real.exp (-(x * (1 - Real.cos θ))) ≤ Real.exp (-b * θ ^ 2) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hulo hx.le
        have : b * θ ^ 2 ≤ x * (1 - Real.cos θ) := by
          calc b * θ ^ 2 = x * (2 / Real.pi ^ 2 * θ ^ 2) := by rw [hbdef]; ring
            _ ≤ _ := this
        linarith
      have h4 := pow_four_mul_exp_le hb θ
      have hz0 := norm_nonneg z
      calc ‖z‖ * (θ ^ 2 / 2 - (1 - Real.cos θ)) * Real.exp (-(x * (1 - Real.cos θ))) ≤
            ‖z‖ * (θ ^ 4 / 24) * Real.exp (-b * θ ^ 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hd hz0) he (Real.exp_pos _).le
            positivity
        _ = ‖z‖ / 24 * (θ ^ 4 * Real.exp (-b * θ ^ 2)) := by ring
        _ ≤ ‖z‖ / 24 * (8 / b ^ 2 * Real.exp (-(b / 2) * θ ^ 2)) := by gcongr
        _ = _ := by ring
    · rw [intervalIntegral.integral_const_mul]
      have := integral_exp_neg_mul_sq_le (β := b / 2) (by positivity)
      rw [hb2] at this
      calc ‖z‖ / 24 * (8 / b ^ 2) * ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-(b / 2) * θ ^ 2) ≤
            ‖z‖ / 24 * (8 / b ^ 2) * (Real.sqrt (Real.pi / (x / Real.pi ^ 2)) / 2) := by
            rw [hb2]; gcongr
        _ = _ := by rw [hbdef]; field_simp; ring
  · -- the tail `θ > π`
    have hx4 : 0 < x / 4 := by positivity
    have hgi : Integrable (fun θ : ℝ => Real.exp (-(x * Real.pi ^ 2 / 4)) *
        Real.exp (-(x / 4) * θ ^ 2)) := (integrable_exp_neg_mul_sq hx4).const_mul _
    refine (MeasureTheory.norm_integral_le_of_norm_le hgi.integrableOn
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun θ hθ => ?_))).trans ?_
    · rw [Complex.norm_exp]
      have hreb : (-(z / 2) * (θ : ℂ) ^ 2).re = -(x * (θ ^ 2 / 2)) := by
        rw [← Complex.ofReal_pow, Complex.re_mul_ofReal, Complex.neg_re]; simp [x]; ring
      rw [hreb, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hθ' : Real.pi ^ 2 ≤ θ ^ 2 := by
        have := mem_Ioi.mp hθ
        nlinarith [Real.pi_pos]
      nlinarith
    · rw [MeasureTheory.integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [← integral_gaussian_Ioi]
      exact setIntegral_mono_set (integrable_exp_neg_mul_sq hx4).integrableOn
        (Eventually.of_forall fun θ => (Real.exp_pos _).le)
        (Ioi_subset_Ioi Real.pi_pos.le).eventuallyLE

/-- Modulus of the half-line Gaussian: `‖∫₀^∞ e^{−zθ²/2}‖ = √(π/(‖z‖/2))/2` (`Re z > 0`). -/
@[tmio T, powerlib_foundation] theorem norm_integral_gaussian_half {z : ℂ} (hx : 0 < z.re) :
    ‖∫ θ in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (θ : ℂ) ^ 2)‖ =
      Real.sqrt (Real.pi / (‖z‖ / 2)) / 2 := by
  have hz2 : 0 < (z / 2).re := by simp at hx ⊢; linarith
  rw [integral_gaussian_complex_Ioi hz2, norm_div, Complex.norm_two,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_div, Complex.norm_two,
    Real.sqrt_eq_rpow]

/-- **Laplace bounds for `I₀`, `I₁` in a sector**, relative to the half-line Gaussian
`G(z) = ∫₀^∞ e^{−zθ²/2} dθ = √(π/(2z))`: for every `K > 0` there is `C ≥ 0` with
`‖e^{−z}π I₀(z) − G(z)‖ ≤ (C/x)‖G(z)‖` and `‖e^{−z}π(I₀(z) − I₁(z))‖ ≤ (C/x)‖G(z)‖` whenever
`x = Re z > 0` and `‖z‖ ≤ K x`. Hence `π e^{−z} I_ν(z)/G(z) = 1 + O(1/x)`, `ν = 0, 1`. -/
@[tmio T, powerlib_foundation] theorem besselI_laplace_le {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.re → ‖z‖ ≤ K * z.re →
      ‖Complex.exp (-z) * (Real.pi * besselI0 z) -
          ∫ θ in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (θ : ℂ) ^ 2)‖ ≤
        C / z.re * ‖∫ θ in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (θ : ℂ) ^ 2)‖ ∧
      ‖Complex.exp (-z) * (Real.pi * besselI0 z - Real.pi * besselI1 z)‖ ≤
        C / z.re * ‖∫ θ in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (θ : ℂ) ^ 2)‖ := by
  set k₁ := Real.sqrt (K * Real.pi ^ 2 / 2) with hk₁
  set k₂ := Real.sqrt (2 * K) with hk₂
  set C₁ := Real.pi ^ 2 / 2 * k₁ with hC₁
  set C₂ := K * Real.pi ^ 4 / 12 * k₁ + 4 / Real.pi ^ 2 * k₂ with hC₂
  have hk₁0 : 0 ≤ k₁ := Real.sqrt_nonneg _
  have hk₂0 : 0 ≤ k₂ := Real.sqrt_nonneg _
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂, by positivity, fun z hx0 hzK => ?_⟩
  set x := z.re with hxdef
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hx0 (Complex.re_le_norm z)
  have hπ := Real.pi_pos
  set G := ∫ θ in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (θ : ℂ) ^ 2) with hGdef
  set γ₀ := Real.sqrt (Real.pi / (‖z‖ / 2)) / 2 with hγ₀def
  have hG : ‖G‖ = γ₀ := norm_integral_gaussian_half hx0
  rw [hG]
  have hγ₀ : 0 < γ₀ := by positivity
  -- the two auxiliary Gaussian widths relative to `γ₀`
  have hγ₁ : Real.sqrt (Real.pi / (x / Real.pi ^ 2)) / 2 ≤ k₁ * γ₀ := by
    have e : Real.pi / (x / Real.pi ^ 2) =
        (‖z‖ * Real.pi ^ 2 / (2 * x)) * (Real.pi / (‖z‖ / 2)) := by
      field_simp
    rw [e, Real.sqrt_mul (by positivity), hγ₀def]
    have : Real.sqrt (‖z‖ * Real.pi ^ 2 / (2 * x)) ≤ k₁ := by
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg Real.pi]
    have h0 : 0 ≤ Real.sqrt (Real.pi / (‖z‖ / 2)) := Real.sqrt_nonneg _
    nlinarith
  have hγ₂ : Real.sqrt (Real.pi / (x / 4)) / 2 ≤ k₂ * γ₀ := by
    have e : Real.pi / (x / 4) = (2 * ‖z‖ / x) * (Real.pi / (‖z‖ / 2)) := by
      field_simp; ring
    rw [e, Real.sqrt_mul (by positivity), hγ₀def]
    have : Real.sqrt (2 * ‖z‖ / x) ≤ k₂ := by
      apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ hx0]
      nlinarith
    have h0 : 0 ≤ Real.sqrt (Real.pi / (‖z‖ / 2)) := Real.sqrt_nonneg _
    nlinarith
  have hexp : Real.exp (-(x * Real.pi ^ 2 / 4)) ≤ 4 / Real.pi ^ 2 / x := by
    have hv : 0 < x * Real.pi ^ 2 / 4 := by positivity
    have h1 := Real.add_one_le_exp (x * Real.pi ^ 2 / 4)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    have : (4 / Real.pi ^ 2 / x)⁻¹ = x * Real.pi ^ 2 / 4 := by field_simp
    rw [this]; linarith
  have hB := norm_integral_cexp_one_sub_cos_mul_le hx0
  have hAG := norm_integral_cexp_one_sub_cos_sub_gaussian_le hx0
  rw [integral_cexp_neg_mul_one_sub_cos_mul] at hB
  rw [integral_cexp_neg_mul_one_sub_cos, ← hGdef] at hAG
  have hC₁le : C₁ / x * γ₀ ≤ (C₁ + C₂) / x * γ₀ := by gcongr; linarith
  have hC₂le : C₂ / x * γ₀ ≤ (C₁ + C₂) / x * γ₀ := by gcongr; linarith
  constructor
  · refine hAG.trans (le_trans ?_ hC₂le)
    have h1 : ‖z‖ * Real.pi ^ 4 / (12 * x ^ 2) ≤ K * Real.pi ^ 4 / 12 / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]
      have := mul_le_mul_of_nonneg_right hzK (by positivity : 0 ≤ Real.pi ^ 4 * x)
      nlinarith
    calc ‖z‖ * Real.pi ^ 4 / (12 * x ^ 2) * (Real.sqrt (Real.pi / (x / Real.pi ^ 2)) / 2) +
          Real.exp (-(x * Real.pi ^ 2 / 4)) * (Real.sqrt (Real.pi / (x / 4)) / 2) ≤
          K * Real.pi ^ 4 / 12 / x * (k₁ * γ₀) + 4 / Real.pi ^ 2 / x * (k₂ * γ₀) := by
          gcongr
      _ = C₂ / x * γ₀ := by rw [hC₂]; field_simp
  · refine hB.trans (le_trans ?_ hC₁le)
    calc Real.pi ^ 2 / (2 * x) * (Real.sqrt (Real.pi / (x / Real.pi ^ 2)) / 2) ≤
          Real.pi ^ 2 / (2 * x) * (k₁ * γ₀) := by gcongr
      _ = C₁ / x * γ₀ := by rw [hC₁]; field_simp

/-- **Large-argument limit of `I₀/I₁` in a sector**, with rate: for every `K > 0` there are
`C` and `x₀ > 0` such that `I₀(z) ≠ 0`, `I₁(z) ≠ 0` and `‖I₀(z)/I₁(z) − 1‖ ≤ C/Re z` whenever
`Re z ≥ x₀` and `‖z‖ ≤ K Re z` (the closed sector `|arg z| ≤ arccos(1/K)`). -/
@[tmio T, powerlib_foundation] theorem besselI0_div_besselI1_sub_one_le {K : ℝ} (hK : 0 < K) :
    ∃ C x₀ : ℝ, 0 < x₀ ∧ ∀ z : ℂ, x₀ ≤ z.re → ‖z‖ ≤ K * z.re →
      besselI0 z ≠ 0 ∧ besselI1 z ≠ 0 ∧ ‖besselI0 z / besselI1 z - 1‖ ≤ C / z.re := by
  obtain ⟨C, hC0, hC⟩ := besselI_laplace_le hK
  refine ⟨4 * C, max 1 (4 * C), lt_max_of_lt_left one_pos, ?_⟩
  intro z hx hzK
  set x := z.re with hxdef
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hxC : 4 * C ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hAG, hB⟩ := hC z hx0 hzK
  set G := ∫ θ in Ioi (0 : ℝ), Complex.exp (-(z / 2) * (θ : ℂ) ^ 2) with hGdef
  set A := Complex.exp (-z) * (Real.pi * besselI0 z) with hAdef
  set B := Complex.exp (-z) * (Real.pi * besselI0 z - Real.pi * besselI1 z) with hBdef
  set γ₀ := ‖G‖ with hγ₀def
  have hγ₀ : 0 < γ₀ := by
    rw [hγ₀def, hGdef, norm_integral_gaussian_half hx0]
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hx0 (Complex.re_le_norm z)
    positivity
  -- `‖A‖ ≥ γ₀/2`
  have hA : γ₀ / 2 ≤ ‖A‖ := by
    have h1 : C / x * γ₀ ≤ γ₀ / 2 := by
      have : C / x ≤ 1 / 2 := by rw [div_le_iff₀ hx0]; linarith
      nlinarith
    have := norm_sub_norm_le G (G - A)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hA0 : A ≠ 0 := by
    intro h; rw [h, norm_zero] at hA; linarith
  have hE : Complex.exp (-z) ≠ 0 := Complex.exp_ne_zero _
  have hπc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI0 : besselI0 z ≠ 0 := by
    intro h; apply hA0; rw [hAdef, h]; simp
  set q := B / A with hqdef
  have hq : ‖q‖ ≤ 2 * C / x := by
    rw [hqdef, norm_div, div_le_iff₀ (by linarith)]
    calc ‖B‖ ≤ C / x * γ₀ := hB
      _ = 2 * C / x * (γ₀ / 2) := by ring
      _ ≤ 2 * C / x * ‖A‖ := by gcongr
  have hq2 : ‖q‖ ≤ 1 / 2 := by
    refine hq.trans ?_
    rw [div_le_iff₀ hx0]; linarith
  have hqI : besselI1 z / besselI0 z = 1 - q := by
    rw [hqdef, hAdef, hBdef]
    field_simp
    ring
  have h1q : ‖1 - q‖ ≥ 1 / 2 := by
    have := norm_sub_norm_le (1 : ℂ) q
    rw [norm_one] at this
    linarith
  have h1q0 : (1 : ℂ) - q ≠ 0 := by
    intro h; rw [h, norm_zero] at h1q; linarith
  have hI1 : besselI1 z ≠ 0 := by
    intro h; apply h1q0; rw [← hqI, h, zero_div]
  refine ⟨hI0, hI1, ?_⟩
  have e : besselI0 z / besselI1 z - 1 = q / (1 - q) := by
    have : besselI0 z / besselI1 z = 1 / (1 - q) := by
      rw [← hqI]; field_simp
    rw [this]; field_simp; ring
  rw [e, norm_div]
  rw [div_le_iff₀ (by linarith)]
  calc ‖q‖ ≤ 2 * C / x := hq
    _ = 4 * C / x * (1 / 2) := by ring
    _ ≤ 4 * C / x * ‖1 - q‖ := by gcongr

/-- **`I₀(z)/I₁(z) → 1` as `z → ∞` in a sector**: along any `f` with `Re f → +∞` and eventually
`‖f‖ ≤ K Re f`. -/
@[tmio T, powerlib_foundation] theorem tendsto_besselI0_div_besselI1 {α : Type*} {l : Filter α}
    {f : α → ℂ} {K : ℝ} (hK : 0 < K) (hre : Tendsto (fun a => (f a).re) l atTop)
    (hsec : ∀ᶠ a in l, ‖f a‖ ≤ K * (f a).re) :
    Tendsto (fun a => besselI0 (f a) / besselI1 (f a)) l (𝓝 1) := by
  obtain ⟨C, x₀, -, hC⟩ := besselI0_div_besselI1_sub_one_le hK
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun a => C / (f a).re) l (𝓝 0) := tendsto_const_nhds.div_atTop hre
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hlim
  filter_upwards [hsec, hre.eventually_ge_atTop x₀] with a ha hx
  exact (hC (f a) hx ha).2.2

/-- `Re((1 + i)s) = s`. -/
@[tmio T, powerlib_foundation] theorem one_add_I_mul_re (s : ℝ) : ((1 + Complex.I) * s).re = s := by
  simp

/-- `‖(1 + i)s‖ ≤ 2 Re((1 + i)s)` for `s ≥ 0` (the ray `arg = π/4` lies in a sector). -/
@[tmio T, powerlib_foundation] theorem norm_one_add_I_mul_le {s : ℝ} (hs : 0 ≤ s) :
    ‖(1 + Complex.I) * s‖ ≤ 2 * ((1 + Complex.I) * s).re := by
  rw [one_add_I_mul_re, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have : ‖(1 + Complex.I)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    simp; norm_num
  nlinarith

end powerlib.SpecialFunctions
