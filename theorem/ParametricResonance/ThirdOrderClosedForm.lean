import theorem.ParametricResonance.ThirdOrderBoundary
import theorem.Periodic.Shift

/-! # The undetuned 2:1 boundary at third order in closed form

`ThirdOrder.full_boundary_third_order` decides the boundary `s > 0`, `d = 0` of the two-state
2:1 system (where the second-order quantity `mixedDet(M, N₂) = T d|g'|²/(4ω)` vanishes) by the
sign of the fourth-order coefficient `K = det N₂ + T mixedDet(M, N₃)` of `det(I − Φ_y)`, with `K`
left symbolic. This file computes it:

`K = T²/(64ω²) · Q`,  `Q = 128 s²|b|² − 16 Re(b̄² g g') − 8 s²|g'|² + |g'|⁴`

(`undetuned_coefficient`, `boundaryQuartic`), `g` the pump, `g' = SecondOrder.antiPump A` the
anti-resonant pump and `b = ThirdOrder.rotCoeff A` the rotational fundamental coefficient; the
scalar part `(a₀₀ + a₁₁)/2` of the modulation does not enter. For `g' = 0` this is
`Q = 128 s²|b|²` (`ThirdOrder.antiFree_coefficient` at `d = 0`), for `s = 0` it is `|g'|⁴`
(`ThirdOrder.zero_detuning_coefficient`).

* Method. On the boundary `mixedDet(M, N₃) = −mixedDet(M, ∫₀ᵀ P̃ F P̃)`
  (`ThirdOrder.mixedDet_thirdTerm_boundary`). `F` and the oscillating part `P̃` of its primitive
  are combinations of the five harmonics `1, cos ωt, sin ωt, cos 2ωt, sin 2ωt` (`harm`) with
  matrix coefficients `formCoeff`, `primCoeff` (`stdForm_harm`, `prim_harm`); the integral of a
  triple product of harmonic sums is the sum of the coefficient products weighted by the triple
  means (`integral_triple_sum`, `integral_harm`), `25` of the `125` means are non-zero
  (`sum_harmMean`), so `mixedDet(M, N₃)` is a finite sum (`mixedDet_thirdTerm_stdForm`, any `d`).
  With `N₂` from `SecondOrder.secondTerm_stdForm` the rest is algebra on the boundary.
* Verdict. `Q > 0`: Schur stable; `Q < 0`: Floquet unstable, for all small `ε > 0`
  (`undetuned_boundary`); `32 s|b|²(4s ∓ |g'|) + |g'|²(|g'|² − 8s²)` bound `Q` from below and
  above (`boundaryQuartic_bounds`). Without rotational coefficient (`b = 0`)
  `Q = |g'|²(|g'|² − 2|g|²)`: the threshold is `|g'| = √2|g|` (`undetuned_rotFree`). The branch
  depends on `g'` and `b`: for every boundary datum `(s, g)` explicit modulations
  (`boundaryModulation`, with prescribed `g, g', b`) give `Q = 128 s⁴`, `−16 s⁴`, `752 s⁴`
  (`undetuned_dependence`).
* The data. The monodromy of `TwoToOne.full s d ω A ε` depends on `A` only through
  `(g, g', b)`, for every `ε` (`monodromy_full_data`: the scalar part `Re{a e^{jωt}} I` commutes
  and integrates to zero over a period, `transition_add_scalar`). On the undetuned line the
  half-period shift of the undamped system is a quarter-turn conjugation
  (`stdForm_half_shift`), so `tr Φ₀(ε)` is even (`undetuned_trace_even`) and
  `e^{εsT} det(I + Φ_ε) = e^{−εsT} det(I + Φ_{−ε})` exactly (`undetuned_det_even`).
* `Q = 0`. For `g' = 0` it means `b = 0`, the exactly marginal monodromy of
  `ThirdOrder.antiFree_marginal`. Otherwise (`g' ≠ 0`, a real hypersurface, e.g. `b = 0`,
  `|g'|² = 2|g|²`) the verdict is not decided here. No pair of modulations with equal data
  `(s, g, g', b)` and opposite verdicts exists (`monodromy_full_data`), so the
  `ThirdOrder.antiFree_undecided` pattern does not apply; and since `e^{εsT} det(I + Φ_ε)` is
  even, the `ε⁵` coefficient of `det(I + Φ_ε)` is `−sTK`, which vanishes with `K`: the next
  deciding term is the `ε⁶` coefficient, which needs the fourth to sixth Picard terms
  (not derived).

Scope.
* Generic: the five harmonics `1, cos θ, sin θ, cos 2θ, sin 2θ` over one period `T = 2π/ω`,
  `ω > 0`; matrices on finite index types; `ẏ = (A(t) + α(t) I) y` with continuous bounded `A`,
  `α`.
* Two-state system: `TwoToOne.full s d ω A ε` (critical pair `−εs ± j(ω/2 − εd)` in real modal
  form, modulation `ε Re{A e^{jωt}}`, arbitrary complex `A`), its rotating-frame matrix
  `TwoToOne.stdForm`; the closed form and the verdicts on the undetuned first-order boundary
  `d = 0`, `s² = |g/2|²`, for all sufficiently small `ε > 0`; the identities of the data and of
  the symmetry for every `ε`.
* Generic mathematics; no model family.

Source: the wave-7 question of this library (the coefficient `K` left symbolic in
`ThirdOrder.full_boundary_third_order`, `theorem/ParametricResonance/ThirdOrderBoundary.lean`);
the small-parameter (Picard) expansion of the monodromy and the transition curves beyond first
order (Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic Coefficients*;
Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5); `ThirdOrder.mixedDet_thirdTerm_boundary`,
`SecondOrder.secondTerm_stdForm`, `SecondOrder.integral_cos_int_mul`, `TwoToOne.stdForm_eq`,
`Periodic.transition_unique`, `Periodic.monodromy_shift`, `Periodic.transition_sub_smul_one`.

Results.
* Harmonics: `kron`, `integral_cos_cos_cos`, `integral_cos_sin_sin`, `integral_cos_cos_sin`,
  `integral_sin_sin_sin`, `freq`, `isSin`, `harm`, `cssMean`, `harmMean`, `continuous_harm`,
  `integral_harm`, `integral_triple_sum`, `sum_harmMean`.
* `transition_add_scalar` — `Φ_{A + αI}(t, 0) = e^{∫₀ᵗ α} Φ_A(t, 0)`.
* Two-state system: `formCoeff`, `primCoeff`, `stdForm_harm`, `prim_harm`,
  `mixedDet_thirdTerm_stdForm`, `boundaryQuartic`, `undetuned_coefficient`,
  `boundaryModulation`, `boundaryModulation_data`, `monodromy_full_data`, `stdForm_half_shift`,
  `undetuned_trace_even`, `undetuned_det_even`, `undetuned_boundary`, `boundaryQuartic_bounds`,
  `undetuned_rotFree`, `undetuned_dependence`.

Corrections.
None: an extension (the closed form of the coefficient left symbolic in
`ThirdOrder.full_boundary_third_order`). The exploratory formula for `K` quoted in the question
is confirmed.

Family and connection conclusions.
None: static evidence on periodic linear systems.
-/

noncomputable section
namespace powerlib.ParametricResonance.ThirdOrderClosed

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator Interval
open Boundary (secondTerm mixedDet)
open ThirdOrder (thirdTerm rotCoeff)

/-! ## Triple products of the harmonics `0, ω, 2ω` over one period -/

section Harmonics

variable {ω : ℝ}

/-- The Kronecker symbol on `ℤ`: `1` at `0`, `0` elsewhere. -/
def kron (m : ℤ) : ℝ := if m = 0 then 1 else 0

@[tmio T, powerlib_foundation] private theorem cos_cos_cos (j k l : ℤ) (x : ℝ) :
    Real.cos (j * x) * Real.cos (k * x) * Real.cos (l * x) =
      (Real.cos (((j + k + l : ℤ) : ℝ) * x) + Real.cos (((j + k - l : ℤ) : ℝ) * x) +
        Real.cos (((j - k + l : ℤ) : ℝ) * x) + Real.cos (((-j + k + l : ℤ) : ℝ) * x)) / 4 := by
  push_cast
  simp only [add_mul, sub_mul, neg_mul, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub,
    Real.cos_neg, Real.sin_neg]
  ring

@[tmio T, powerlib_foundation] private theorem cos_sin_sin (j k l : ℤ) (x : ℝ) :
    Real.cos (j * x) * Real.sin (k * x) * Real.sin (l * x) =
      (Real.cos (((j + k - l : ℤ) : ℝ) * x) + Real.cos (((j - k + l : ℤ) : ℝ) * x) -
        Real.cos (((j + k + l : ℤ) : ℝ) * x) - Real.cos (((j - k - l : ℤ) : ℝ) * x)) / 4 := by
  push_cast
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
  ring

@[tmio T, powerlib_foundation] private theorem cos_cos_sin (j k l : ℤ) (x : ℝ) :
    Real.cos (j * x) * Real.cos (k * x) * Real.sin (l * x) =
      (Real.sin (((l + j - k : ℤ) : ℝ) * x) + Real.sin (((l - j + k : ℤ) : ℝ) * x) +
        Real.sin (((l + j + k : ℤ) : ℝ) * x) + Real.sin (((l - j - k : ℤ) : ℝ) * x)) / 4 := by
  push_cast
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
  ring

@[tmio T, powerlib_foundation] private theorem sin_sin_sin (j k l : ℤ) (x : ℝ) :
    Real.sin (j * x) * Real.sin (k * x) * Real.sin (l * x) =
      (Real.sin (((l + j - k : ℤ) : ℝ) * x) + Real.sin (((l - j + k : ℤ) : ℝ) * x) -
        Real.sin (((l + j + k : ℤ) : ℝ) * x) - Real.sin (((l - j - k : ℤ) : ℝ) * x)) / 4 := by
  push_cast
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
  ring

@[tmio T, powerlib_foundation] private theorem integral_cos_kron (hω : 0 < ω) (m : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (m * (ω * t)) = 2 * Real.pi / ω * kron m := by
  rw [SecondOrder.integral_cos_int_mul hω, kron]
  split_ifs <;> simp

@[tmio T, powerlib_foundation] private theorem integral_sin_zero (hω : 0 < ω) (m : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (m * (ω * t)) = 0 :=
  SecondOrder.integral_sin_int_mul hω m

/-- `∫₀ᵀ cos(jωt) cos(kωt) cos(lωt) dt = (T/4)(δ(j+k+l) + δ(j+k−l) + δ(j−k+l) + δ(−j+k+l))`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_cos_cos (hω : 0 < ω) (j k l : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω),
        Real.cos (j * (ω * t)) * Real.cos (k * (ω * t)) * Real.cos (l * (ω * t)) =
      2 * Real.pi / ω / 4 *
        (kron (j + k + l) + kron (j + k - l) + kron (j - k + l) + kron (-j + k + l)) := by
  simp_rw [cos_cos_cos]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_kron hω, integral_cos_kron hω, integral_cos_kron hω, integral_cos_kron hω]
  ring

/-- `∫₀ᵀ cos(jωt) sin(kωt) sin(lωt) dt = (T/4)(δ(j+k−l) + δ(j−k+l) − δ(j+k+l) − δ(j−k−l))`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_sin_sin (hω : 0 < ω) (j k l : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω),
        Real.cos (j * (ω * t)) * Real.sin (k * (ω * t)) * Real.sin (l * (ω * t)) =
      2 * Real.pi / ω / 4 *
        (kron (j + k - l) + kron (j - k + l) - kron (j + k + l) - kron (j - k - l)) := by
  simp_rw [cos_sin_sin]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_kron hω, integral_cos_kron hω, integral_cos_kron hω, integral_cos_kron hω]
  ring

/-- A triple product with one sine factor has mean zero. -/
@[tmio T, powerlib_foundation] theorem integral_cos_cos_sin (hω : 0 < ω) (j k l : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω),
        Real.cos (j * (ω * t)) * Real.cos (k * (ω * t)) * Real.sin (l * (ω * t)) = 0 := by
  simp_rw [cos_cos_sin]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_sin_zero hω, integral_sin_zero hω, integral_sin_zero hω, integral_sin_zero hω]
  ring

/-- A triple product of three sines has mean zero. -/
@[tmio T, powerlib_foundation] theorem integral_sin_sin_sin (hω : 0 < ω) (j k l : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω),
        Real.sin (j * (ω * t)) * Real.sin (k * (ω * t)) * Real.sin (l * (ω * t)) = 0 := by
  simp_rw [sin_sin_sin]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_sin_zero hω, integral_sin_zero hω, integral_sin_zero hω, integral_sin_zero hω]
  ring

/-- The frequencies of the five harmonics `1, cos θ, sin θ, cos 2θ, sin 2θ`. -/
def freq : Fin 5 → ℤ := ![0, 1, 1, 2, 2]

/-- Which of the five harmonics are sines. -/
def isSin : Fin 5 → Bool := ![false, false, true, false, true]

/-- The five harmonics `1, cos θ, sin θ, cos 2θ, sin 2θ`. -/
def harm (i : Fin 5) (θ : ℝ) : ℝ :=
  if isSin i then Real.sin (freq i * θ) else Real.cos (freq i * θ)

/-- `cos j · sin k · sin l` averaged: `(δ(j+k−l) + δ(j−k+l) − δ(j+k+l) − δ(j−k−l))/4`. -/
def cssMean (j k l : ℤ) : ℝ :=
  (kron (j + k - l) + kron (j - k + l) - kron (j + k + l) - kron (j - k - l)) / 4

/-- The mean over one period of the product of three harmonics. -/
def harmMean (i j k : Fin 5) : ℝ :=
  match isSin i, isSin j, isSin k with
  | false, false, false => (kron (freq i + freq j + freq k) + kron (freq i + freq j - freq k) +
      kron (freq i - freq j + freq k) + kron (-freq i + freq j + freq k)) / 4
  | false, true, true => cssMean (freq i) (freq j) (freq k)
  | true, false, true => cssMean (freq j) (freq i) (freq k)
  | true, true, false => cssMean (freq k) (freq i) (freq j)
  | _, _, _ => 0

/-- The harmonics are continuous. -/
@[tmio T, powerlib_foundation] theorem continuous_harm (i : Fin 5) : Continuous (harm i) := by
  unfold harm
  split_ifs <;> fun_prop

/-- **The triple products of the harmonics over one period:**
`∫₀ᵀ h_i(ωt) h_j(ωt) h_k(ωt) dt = T · harmMean i j k` (`T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_harm (hω : 0 < ω) (i j k : Fin 5) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), harm i (ω * t) * harm j (ω * t) * harm k (ω * t) =
      2 * Real.pi / ω * harmMean i j k := by
  unfold harm harmMean
  cases isSin i <;> cases isSin j <;> cases isSin k <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [integral_cos_cos_cos hω]; ring
  · rw [integral_cos_cos_sin hω, mul_zero]
  · have e : ∀ t, Real.cos (freq i * (ω * t)) * Real.sin (freq j * (ω * t)) *
        Real.cos (freq k * (ω * t)) = Real.cos (freq i * (ω * t)) * Real.cos (freq k * (ω * t)) *
          Real.sin (freq j * (ω * t)) := fun t => by ring
    simp_rw [e]; rw [integral_cos_cos_sin hω]; ring
  · rw [integral_cos_sin_sin hω, cssMean]; ring
  · have e : ∀ t, Real.sin (freq i * (ω * t)) * Real.cos (freq j * (ω * t)) *
        Real.cos (freq k * (ω * t)) = Real.cos (freq j * (ω * t)) * Real.cos (freq k * (ω * t)) *
          Real.sin (freq i * (ω * t)) := fun t => by ring
    simp_rw [e]; rw [integral_cos_cos_sin hω]; ring
  · have e : ∀ t, Real.sin (freq i * (ω * t)) * Real.cos (freq j * (ω * t)) *
        Real.sin (freq k * (ω * t)) = Real.cos (freq j * (ω * t)) * Real.sin (freq i * (ω * t)) *
          Real.sin (freq k * (ω * t)) := fun t => by ring
    simp_rw [e]; rw [integral_cos_sin_sin hω, cssMean]; ring
  · have e : ∀ t, Real.sin (freq i * (ω * t)) * Real.sin (freq j * (ω * t)) *
        Real.cos (freq k * (ω * t)) = Real.cos (freq k * (ω * t)) * Real.sin (freq i * (ω * t)) *
          Real.sin (freq j * (ω * t)) := fun t => by ring
    simp_rw [e]; rw [integral_cos_sin_sin hω, cssMean]; ring
  · rw [integral_sin_sin_sin hω]; ring

/-- **Expansion of a triple product of harmonic sums.** For continuous scalar functions `φ_i`
and matrices `X_i, Y_j, Z_k` (finite index type):
`∫ₐᵇ (∑ φ_i X_i)(∑ φ_j Y_j)(∑ φ_k Z_k) = ∑_{i,j,k} (∫ₐᵇ φ_i φ_j φ_k) X_i Y_j Z_k`. -/
@[tmio T, powerlib_foundation] theorem integral_triple_sum {ι X : Type*} [Fintype ι] [Fintype X]
    (φ : ι → ℝ → ℝ) (hφ : ∀ i, Continuous (φ i)) (P Q R : ι → Matrix X X ℝ) (a b : ℝ) :
    ∫ t in a..b, (∑ i, φ i t • P i) * (∑ j, φ j t • Q j) * (∑ k, φ k t • R k) =
      ∑ i, ∑ j, ∑ k, (∫ t in a..b, φ i t * φ j t * φ k t) • (P i * Q j * R k) := by
  have e : ∀ t, (∑ i, φ i t • P i) * (∑ j, φ j t • Q j) * (∑ k, φ k t • R k) =
      ∑ i, ∑ j, ∑ k, (φ i t * φ j t * φ k t) • (P i * Q j * R k) := fun t => by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum fun i _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      (((hφ i).mul (hφ j)).mul (hφ k)).smul continuous_const]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun k _ =>
      (((hφ i).mul (hφ j)).mul (hφ k)).smul continuous_const]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun k _ => by
    apply Continuous.intervalIntegrable
    exact (((hφ i).mul (hφ j)).mul (hφ k)).smul continuous_const]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact intervalIntegral.integral_smul_const _ _

/-- **The table of triple means.** Of the `125` triple means of the harmonics `1, cos θ, sin θ,
cos 2θ, sin 2θ` exactly `25` are non-zero: `⟨1·1·1⟩ = 1`; `⟨1·h·h⟩ = 1/2` for the four
non-constant harmonics in all positions; `⟨cos θ cos θ cos 2θ⟩ = ⟨cos θ sin θ sin 2θ⟩ = 1/4` and
`⟨sin θ sin θ cos 2θ⟩ = −1/4` in all orders. -/
@[tmio T, powerlib_foundation] theorem sum_harmMean (L : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ i, ∑ j, ∑ k, harmMean i j k * L i j k =
      L 0 0 0 + (L 0 1 1 + L 0 2 2 + L 0 3 3 + L 0 4 4 + L 1 0 1 + L 1 1 0 + L 2 0 2 + L 2 2 0 +
        L 3 0 3 + L 3 3 0 + L 4 0 4 + L 4 4 0) / 2 +
      (L 1 1 3 + L 1 2 4 + L 1 3 1 + L 1 4 2 + L 2 1 4 + L 2 4 1 + L 3 1 1 + L 4 1 2 +
        L 4 2 1) / 4 - (L 2 2 3 + L 2 3 2 + L 3 2 2) / 4 := by
  simp [Fin.sum_univ_five, harmMean, isSin, freq, cssMean, kron]
  ring

end Harmonics

/-! ## A scalar time-varying shift of a linear periodic system -/

section Scalar

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **A scalar time-varying shift rescales the transition matrix.** For continuous bounded `A`
and a continuous bounded scalar `α` with primitive `p` (`p' = α`, `p(0) = 0`):
`Φ_{A + αI}(t, 0) = e^{p(t)} Φ_A(t, 0)` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem transition_add_scalar {A : ℝ → Matrix X X ℝ} {M c : ℝ}
    (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) {α p : ℝ → ℝ} (hα : Continuous α)
    (hc : ∀ t, |α t| ≤ c) (hp : ∀ r, HasDerivAt p (α r) r) (hp0 : p 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    Periodic.transition (fun r => A r + α r • (1 : Matrix X X ℝ)) t 0 =
      Real.exp (p t) • Periodic.transition A t 0 := by
  have hY : IsIntegralCurveOn (fun r => Real.exp (p r) • Periodic.transition A r 0)
      (Periodic.matField (fun r => A r + α r • (1 : Matrix X X ℝ))) (Ici 0) := by
    intro r _
    have he : HasDerivAt (fun r => Real.exp (p r)) (Real.exp (p r) * α r) r := (hp r).exp
    have h := he.smul (Dynamics.stm_hasDerivAt hA r 0)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [Periodic.matField, add_mul, smul_mul_assoc, one_mul, mul_smul_comm,
      Periodic.transition]
    module
  have h := Periodic.transition_unique (A := fun r => A r + α r • (1 : Matrix X X ℝ))
    (M := M + c * ‖(1 : Matrix X X ℝ)‖) (hA.add (hα.smul continuous_const))
    (fun r => (norm_add_le _ _).trans (add_le_add (hM r) (by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hc r) (norm_nonneg _)))) hY t ht
  simp only [hp0, Real.exp_zero, one_smul, LinearSystems.stateTransitionMatrix_self, mul_one,
    Periodic.transition] at h ⊢
  exact h.symm

end Scalar

/-! ## The rotating-frame matrix of the two-state system on the five harmonics -/

section TwoState

open TwoToOne (full stdForm left right refl1 refl2)
open SecondOrder (antiPump stdSin stdCos)
open _root_.powerlib.ParametricResonance.NormalForm (quarter)

variable {ω : ℝ}

/-- The coefficients of `TwoToOne.stdForm s d ω A` on the harmonics `1, cos ωt, sin ωt, cos 2ωt,
sin 2ωt`: the slow-flow matrix `M` and the Fourier coefficients `stdCos A k`, `stdSin A k`. -/
def formCoeff (s d : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Fin 5 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![slowFlowMatrix s d (Element.pump A left right / 2), stdCos A 1, stdSin A 1, stdCos A 2,
    stdSin A 2]

/-- The coefficients of the oscillating part `P̃(t) = ∫₀ᵗ F − t M` of the primitive of
`TwoToOne.stdForm` on the same harmonics. -/
def primCoeff (ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Fin 5 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![(1 / ω) • stdSin A 1 + (1 / (2 * ω)) • stdSin A 2, (-(1 / ω)) • stdSin A 1,
    (1 / ω) • stdCos A 1, (-(1 / (2 * ω))) • stdSin A 2, (1 / (2 * ω)) • stdCos A 2]

/-- `F(t) = ∑ᵢ hᵢ(ωt) Fᵢ` for `F = TwoToOne.stdForm s d ω A` (`SecondOrder.stdForm_eq_trigPoly`). -/
@[tmio T, powerlib_foundation] theorem stdForm_harm (s d ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℝ) : stdForm s d ω A t = ∑ i, harm i (ω * t) • formCoeff s d A i := by
  rw [SecondOrder.stdForm_eq_trigPoly, SecondOrder.trigPoly, Finset.sum_pair (by norm_num),
    Fin.sum_univ_five]
  simp [harm, freq, isSin, formCoeff]
  abel

/-- `∫₀ʳ F − r M = ∑ᵢ hᵢ(ωr) Pᵢ` for `F = TwoToOne.stdForm s d ω A`, `M` its mean
(`SecondOrder.integral_trigPoly`). -/
@[tmio T, powerlib_foundation] theorem prim_harm (s d : ℝ) (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) :
    (∫ u in (0 : ℝ)..r, stdForm s d ω A u) -
        r • slowFlowMatrix s d (Element.pump A left right / 2) =
      ∑ i, harm i (ω * r) • primCoeff ω A i := by
  rw [SecondOrder.stdForm_eq_trigPoly, SecondOrder.integral_trigPoly hω (by simp),
    SecondOrder.trigPrim, Finset.sum_pair (by norm_num), Fin.sum_univ_five]
  simp [harm, freq, isSin, primCoeff]
  module

@[tmio T, powerlib_foundation] private theorem mixedDet_sum₂ {ι : Type*}
    (M : Matrix (Fin 2) (Fin 2) ℝ) (f : ι → Matrix (Fin 2) (Fin 2) ℝ) (S : Finset ι) :
    mixedDet M (∑ k ∈ S, f k) = ∑ k ∈ S, mixedDet M (f k) := by
  simp only [mixedDet, Matrix.trace_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

@[tmio T, powerlib_foundation] private theorem mixedDet_smul₂ (M N : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) : mixedDet M (c • N) = c * mixedDet M N := by
  simp [mixedDet, Matrix.trace_smul]; ring

/-- **The third Picard term of the two-state system on the first-order boundary as a finite
sum.** With `M = slowFlowMatrix s d (g/2)` on the boundary `s² + d² = |g/2|²`, `T = 2π/ω`, the
coefficients `F_j = formCoeff s d A j` of `F = TwoToOne.stdForm s d ω A` and `P_i = primCoeff ω A i`
of the oscillating part of its primitive:
`mixedDet(M, N₃) = −T ∑_{i,j,k} harmMean i j k · mixedDet(M, P_i F_j P_k)`
(`ThirdOrder.mixedDet_thirdTerm_boundary`, `integral_triple_sum`, `integral_harm`). -/
@[tmio T, powerlib_foundation] theorem mixedDet_thirdTerm_stdForm (s d : ℝ) (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
        (thirdTerm (stdForm s d ω A) (2 * Real.pi / ω)) =
      -(2 * Real.pi / ω * ∑ i, ∑ j, ∑ k, harmMean i j k *
        mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
          (primCoeff ω A i * formCoeff s d A j * primCoeff ω A k)) := by
  set M := slowFlowMatrix s d (Element.pump A left right / 2) with hM
  have hdet : M.det = 0 := by rw [hM, det_slowFlowMatrix, ← hb]; ring
  rw [ThirdOrder.mixedDet_thirdTerm_boundary (TwoToOne.continuous_stdForm s d ω A)
    (TwoToOne.integral_stdForm s d hω A) hdet]
  simp_rw [prim_harm s d hω A]
  simp_rw [stdForm_harm s d ω A]
  have hφ : ∀ i, Continuous fun t => harm i (ω * t) := fun i =>
    (continuous_harm i).comp (continuous_const.mul continuous_id)
  have h := integral_triple_sum (fun i t => harm i (ω * t)) hφ (primCoeff ω A) (formCoeff s d A)
    (primCoeff ω A) 0 (2 * Real.pi / ω)
  simp only at h
  rw [h]
  simp only [mixedDet_sum₂, mixedDet_smul₂, integral_harm hω]
  simp only [Finset.mul_sum, mul_assoc]
  rfl

/-- The fundamental and second-harmonic coefficients of `TwoToOne.stdForm` in the coordinates
`a = (a₀₀ + a₁₁)/2` (scalar part), `b = rotCoeff A` (rotational part) and `g' = antiPump A`. -/
@[tmio T, powerlib_foundation] private theorem std_coeff_explicit (A : Matrix (Fin 2) (Fin 2) ℂ) :
    stdCos A 1 = !![((A 0 0).re + (A 1 1).re) / 2, -(rotCoeff A).re;
      (rotCoeff A).re, ((A 0 0).re + (A 1 1).re) / 2] ∧
    stdSin A 1 = !![-(((A 0 0).im + (A 1 1).im) / 2), (rotCoeff A).im;
      -(rotCoeff A).im, -(((A 0 0).im + (A 1 1).im) / 2)] ∧
    stdCos A 2 = !![(antiPump A).re / 2, -(antiPump A).im / 2;
      -(antiPump A).im / 2, -((antiPump A).re / 2)] ∧
    stdSin A 2 = !![-(antiPump A).im / 2, -((antiPump A).re / 2);
      -((antiPump A).re / 2), -(-(antiPump A).im / 2)] := by
  rw [SecondOrder.antiPump_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [stdCos, stdSin, refl1, refl2, quarter, rotCoeff] <;> ring

/-- The quartic form deciding the undetuned 2:1 boundary at third order:
`128 s²|b|² − 16 Re(b̄² g g') − 8 s²|g'|² + |g'|⁴` (pump `g`, anti-resonant pump `g'`, rotational
fundamental coefficient `b`, damping `s`). -/
def boundaryQuartic (s : ℝ) (g g' b : ℂ) : ℝ :=
  128 * s ^ 2 * ‖b‖ ^ 2 - 16 * ((starRingEnd ℂ) b ^ 2 * g * g').re - 8 * s ^ 2 * ‖g'‖ ^ 2 +
    ‖g'‖ ^ 4

/-- **The fourth-order coefficient on the undetuned boundary in closed form.** For the two-state
2:1 system with `d = 0` on the first-order boundary `s² = |g/2|²` (`F = TwoToOne.stdForm s 0 ω A`,
`M = slowFlowMatrix s 0 (g/2)`, `T = 2π/ω`, `N₂`, `N₃` the second and third Picard terms):
`K = det N₂ + T mixedDet(M, N₃) = T²/(64ω²) · (128 s²|b|² − 16 Re(b̄² g g') − 8 s²|g'|² + |g'|⁴)`,
`g = Element.pump A left right`, `g' = antiPump A`, `b = rotCoeff A`. The scalar part
`(a₀₀ + a₁₁)/2` of the modulation does not enter. -/
@[tmio T, powerlib_foundation] theorem undetuned_coefficient (s : ℝ) (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hb : s ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    (secondTerm (stdForm s 0 ω A) (2 * Real.pi / ω)).det + 2 * Real.pi / ω *
        mixedDet (slowFlowMatrix s 0 (Element.pump A left right / 2))
          (thirdTerm (stdForm s 0 ω A) (2 * Real.pi / ω)) =
      (2 * Real.pi / ω) ^ 2 / (64 * ω ^ 2) *
        boundaryQuartic s (Element.pump A left right) (antiPump A) (rotCoeff A) := by
  obtain ⟨hC1, hS1, hC2, hS2⟩ := std_coeff_explicit A
  rw [SecondOrder.secondTerm_stdForm s 0 hω A,
    mixedDet_thirdTerm_stdForm s 0 hω A (by rw [← hb]; ring), sum_harmMean]
  simp only [primCoeff, formCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  rw [hC1, hS1, hC2, hS2]
  set g := Element.pump A left right
  set g' := antiPump A
  set b := rotCoeff A
  rw [Complex.sq_norm, Complex.normSq_apply] at hb
  rw [boundaryQuartic, show ‖g'‖ ^ 4 = (‖g'‖ ^ 2) ^ 2 by ring, Complex.sq_norm,
    Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply, sq ((starRingEnd ℂ) b)]
  simp [Matrix.det_fin_two, mixedDet, Matrix.trace_fin_two, slowFlowMatrix, quarter,
    Complex.mul_re, Complex.mul_im] at hb ⊢
  linear_combination (-2 * Real.pi ^ 2 * ((g'.re / 2) ^ 2 + (g'.im / 2) ^ 2 +
    2 * (((A 0 0).re + (A 1 1).re) / 2) ^ 2 - 2 * Real.pi ^ 2 * s ^ 2 +
    2 * Real.pi ^ 2 * (g.re / 2) ^ 2 + 2 * Real.pi ^ 2 * (g.im / 2) ^ 2 +
    6 * (((A 0 0).im + (A 1 1).im) / 2) ^ 2 + 2 * b.re ^ 2 - 2 * b.im ^ 2) / ω ^ 4) * hb

/-- A modulation with prescribed pump `g`, anti-resonant pump `g'` and rotational coefficient `b`
(and scalar part `(a₀₀ + a₁₁)/2 = 0`): `A₁ = ((g + g')/2) E₁ − j((g − g')/2) E₂ + b J`.
For `g' = 0` it is `ThirdOrder.antiFreeModulation g b`. -/
def boundaryModulation (g g' b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(g + g') / 2, -b - I * ((g - g') / 2); b - I * ((g - g') / 2), -((g + g') / 2)]

@[tmio T, powerlib_foundation] theorem boundaryModulation_data (g g' b : ℂ) :
    Element.pump (boundaryModulation g g' b) left right = g ∧
      antiPump (boundaryModulation g g' b) = g' ∧ rotCoeff (boundaryModulation g g' b) = b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [TwoToOne.pump_base]; simp [boundaryModulation]; ring_nf; simp [I_sq]; ring
  · rw [SecondOrder.antiPump_eq]; simp [boundaryModulation]; ring_nf; simp [I_sq]; ring
  · simp [rotCoeff, boundaryModulation]

/-- The rotating-frame matrix splits into that of `boundaryModulation g g' b` and the scalar part
`Re{a e^{jωt}} I`, `a = (a₀₀ + a₁₁)/2`. -/
@[tmio T, powerlib_foundation] private theorem stdForm_scalar_split (s d ω : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    stdForm s d ω A t = stdForm s d ω
        (boundaryModulation (Element.pump A left right) (antiPump A) (rotCoeff A)) t +
      (((A 0 0).re + (A 1 1).re) / 2 * Real.cos (ω * t) -
        ((A 0 0).im + (A 1 1).im) / 2 * Real.sin (ω * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨hp, -, -⟩ := boundaryModulation_data (Element.pump A left right) (antiPump A)
    (rotCoeff A)
  rw [TwoToOne.stdForm_eq, TwoToOne.stdForm_eq s d ω (boundaryModulation _ _ _), hp]
  simp only [boundaryModulation, TwoToOne.pump_base, SecondOrder.antiPump_eq, rotCoeff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarter, refl1, refl2] <;> ring

/-- **The Floquet data of the two-state system are `(s, d, g, g', b)`.** For every modulation
`A` and every `ε`, the monodromy of `TwoToOne.full s d ω A ε` over `T = 2π/ω` equals that of the
modulation `boundaryModulation g g' b` with the same pump `g`, anti-resonant pump `g'` and
rotational coefficient `b`: the scalar part `Re{a e^{jωt}} I` commutes and contributes the factor
`e^{ε∫₀ᵀ Re{a e^{jωt}} dt} = 1` (`transition_add_scalar`). In particular any two modulations with
the same `(g, g', b)` have the same Floquet multipliers for every `ε`. -/
@[tmio T, powerlib_foundation] theorem monodromy_full_data (s d : ℝ) (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0 =
      Periodic.monodromy (full s d ω
        (boundaryModulation (Element.pump A left right) (antiPump A) (rotCoeff A)) ε)
        (2 * Real.pi / ω) 0 := by
  set A' := boundaryModulation (Element.pump A left right) (antiPump A) (rotCoeff A) with hA'
  set c := ((A 0 0).re + (A 1 1).re) / 2 with hc
  set e := ((A 0 0).im + (A 1 1).im) / 2 with he
  rw [TwoToOne.monodromy_full s d hω A ε, TwoToOne.monodromy_full s d hω A' ε]
  congr 1
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm s d hω A'
  have hT : 0 ≤ 2 * Real.pi / ω := by positivity
  have hfun : (fun t => ε • stdForm s d ω A t) = fun t => ε • stdForm s d ω A' t +
      (ε * (c * Real.cos (ω * t) - e * Real.sin (ω * t))) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext t
    rw [stdForm_scalar_split s d ω A t, smul_add, smul_smul]
  have hcont : Continuous fun t => ε * (c * Real.cos (ω * t) - e * Real.sin (ω * t)) := by
    fun_prop
  have hbound : ∀ t, |ε * (c * Real.cos (ω * t) - e * Real.sin (ω * t))| ≤ |ε| * (|c| + |e|) :=
    fun t => by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hderiv : ∀ r, HasDerivAt
      (fun t => ε * ((c * Real.sin (ω * t) - e * (1 - Real.cos (ω * t))) / ω))
      (ε * (c * Real.cos (ω * r) - e * Real.sin (ω * r))) r := fun r => by
    have h1 : HasDerivAt (fun t => ω * t) ω r := by simpa using (hasDerivAt_id r).const_mul ω
    have h := ((((Real.hasDerivAt_sin (ω * r)).comp r h1).const_mul c).sub
      ((((Real.hasDerivAt_cos (ω * r)).comp r h1).const_sub 1).const_mul e)).div_const ω
      |>.const_mul ε
    refine h.congr_deriv ?_
    field_simp
  have h := transition_add_scalar (A := fun t => ε • stdForm s d ω A' t)
    ((TwoToOne.continuous_stdForm s d ω A').const_smul ε)
    (fun t => by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMF t) (abs_nonneg ε))
    hcont hbound hderiv (by simp) hT
  have hper : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp
  rw [hper, Real.sin_two_pi, Real.cos_two_pi] at h
  simp only [mul_zero, sub_self, zero_div, Real.exp_zero, one_smul] at h
  rw [Periodic.monodromy, Periodic.monodromy, zero_add, hfun, h]

/-! ## The half-period symmetry of the undetuned system -/

/-- A constant similarity `P Q = Q P = 1` conjugates the transition matrix of a `2 × 2`
system. -/
@[tmio T, powerlib_foundation] private theorem transition_conj₂
    {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F) {B : ℝ} (hB : ∀ t, ‖F t‖ ≤ B)
    {P Q : Matrix (Fin 2) (Fin 2) ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1) {t : ℝ} (ht : 0 ≤ t) :
    Periodic.transition (fun r => P * F r * Q) t 0 = P * Periodic.transition F t 0 * Q := by
  have hY : IsIntegralCurveOn (fun r => P * Periodic.transition F r 0 * Q)
      (Periodic.matField (fun r => P * F r * Q)) (Ici 0) := by
    intro r _
    have h := ((hasDerivAt_const r P).mul (Dynamics.stm_hasDerivAt hF r 0)).mul
      (hasDerivAt_const r Q)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [Periodic.matField, Periodic.transition, zero_mul, zero_add, mul_zero, add_zero,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have h := Periodic.transition_unique (A := fun r => P * F r * Q) (M := ‖P‖ * B * ‖Q‖)
    ((continuous_const.mul hF).mul continuous_const)
    (fun r => (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (hB r) (norm_nonneg _))) (norm_nonneg _))) hY t ht
  simp only [Periodic.transition, LinearSystems.stateTransitionMatrix_self, Matrix.mul_one, hPQ]
    at h ⊢
  exact h.symm

/-- **The half-period shift of the undamped, undetuned rotating-frame matrix is a quarter-turn
conjugation:** `F₀(t + T/2) = J F₀(t) J` for `F₀ = TwoToOne.stdForm 0 0 ω A`; the commuting
(`I`, `J`) part, carried by the fundamental only, changes sign and the reflection (`E₁`, `E₂`)
part — mean and second harmonic — is kept. -/
@[tmio T, powerlib_foundation] theorem stdForm_half_shift (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    stdForm 0 0 ω A (t + 2 * Real.pi / ω / 2) = quarter * stdForm 0 0 ω A t * quarter := by
  have h1 : ω * (t + 2 * Real.pi / ω / 2) = ω * t + Real.pi := by field_simp
  have h2 : 2 * (ω * (t + 2 * Real.pi / ω / 2)) = 2 * (ω * t) + 2 * Real.pi := by
    rw [h1]; ring
  rw [TwoToOne.stdForm_eq 0 0 ω A (t + _), h2, h1, Real.cos_add_pi, Real.sin_add_pi,
    Real.cos_add_two_pi, Real.sin_add_two_pi]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [TwoToOne.stdForm_eq]
  fin_cases i <;> fin_cases j <;> simp [quarter, refl1, refl2, slowFlowMatrix] <;> ring

/-- **The trace of the undamped, undetuned monodromy is even in `ε`.** For
`Φ₀(ε) = Φ(T, 0)` of `ẏ = ε TwoToOne.stdForm 0 0 ω A y`: `tr Φ₀(−ε) = tr Φ₀(ε)`. The system for
`−ε`, shifted by `T/2`, is the quarter-turn conjugate of the system for `ε`
(`stdForm_half_shift`), and a time shift does not change the trace of the monodromy. -/
@[tmio T, powerlib_foundation] theorem undetuned_trace_even (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    (Periodic.monodromy (fun t => (-ε) • stdForm 0 0 ω A t) (2 * Real.pi / ω) 0).trace =
      (Periodic.monodromy (fun t => ε • stdForm 0 0 ω A t) (2 * Real.pi / ω) 0).trace := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm 0 0 hω A
  have hc : ∀ c : ℝ, Continuous fun t => c • stdForm 0 0 ω A t := fun c =>
    (TwoToOne.continuous_stdForm 0 0 ω A).const_smul c
  have hb : ∀ c t, ‖c • stdForm 0 0 ω A t‖ ≤ |c| * MF := fun c t => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMF t) (abs_nonneg c)
  have hper : ∀ c : ℝ, Function.Periodic (fun t => c • stdForm 0 0 ω A t) T := fun c t => by
    show c • stdForm 0 0 ω A (t + T) = c • stdForm 0 0 ω A t
    rw [TwoToOne.periodic_stdForm 0 0 hω.ne' A t]
  have hJJ : quarter * -quarter = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quarter, Matrix.mul_apply, Fin.sum_univ_two]
  have hJJ' : -quarter * quarter = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quarter, Matrix.mul_apply, Fin.sum_univ_two]
  -- the shifted `−ε` system is the conjugate of the `ε` system
  have hfun : (fun t => (-ε) • stdForm 0 0 ω A (t + T / 2)) =
      fun t => quarter * (ε • stdForm 0 0 ω A t) * -quarter := by
    funext t
    rw [stdForm_half_shift hω A t]
    simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul, neg_smul]
  have e1 : Periodic.monodromy (fun t => (-ε) • stdForm 0 0 ω A (t + T / 2)) T 0 =
      quarter * Periodic.monodromy (fun t => ε • stdForm 0 0 ω A t) T 0 * -quarter := by
    rw [hfun, Periodic.monodromy, Periodic.monodromy, zero_add]
    exact transition_conj₂ (hc ε) (hb ε) hJJ hJJ' hT.le
  have e2 := Periodic.monodromy_shift (A := fun t => (-ε) • stdForm 0 0 ω A t) (hc (-ε))
    (hb (-ε)) (T / 2) hT.le 0
  rw [zero_add] at e2
  obtain ⟨s0, sh⟩ := Periodic.monodromy_eq_mul_swap (A := fun t => (-ε) • stdForm 0 0 ω A t)
    (hc (-ε)) (hb (-ε)) (hper (-ε)) (s := T / 2) (by positivity) (by linarith)
  have e3 : (Periodic.monodromy (fun t => (-ε) • stdForm 0 0 ω A t) T (T / 2)).trace =
      (Periodic.monodromy (fun t => (-ε) • stdForm 0 0 ω A t) T 0).trace := by
    rw [sh, s0, Matrix.trace_mul_comm]
  rw [← e3, ← e2, e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ', Matrix.one_mul]

/-- **On the undetuned line `e^{εsT} det(I + Φ_ε)` is even in `ε`.** For the complete two-state
system `TwoToOne.full s 0 ω A ε` (any damping `s`, any modulation `A`, every `ε`), with
`Φ_ε` its monodromy over `T = 2π/ω`: `e^{εsT} det(I + Φ_ε) = e^{−εsT} det(I + Φ_{−ε})`. Indeed
`Φ_ε = −e^{−εsT} Φ₀(ε)` with `det Φ₀ = 1` and `tr Φ₀` even (`undetuned_trace_even`), so both
sides equal `2 cosh(εsT) − tr Φ₀(ε)`. On the boundary `det(I + Φ_ε) = ε⁴K + O(ε⁵)`; the
evenness forces the `ε⁵` coefficient to be `−sTK`. -/
@[tmio T, powerlib_foundation] theorem undetuned_det_even (s : ℝ) (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Real.exp (ε * s * (2 * Real.pi / ω)) *
        (1 + Periodic.monodromy (full s 0 ω A ε) (2 * Real.pi / ω) 0).det =
      Real.exp (-(ε * s * (2 * Real.pi / ω))) *
        (1 + Periodic.monodromy (full s 0 ω A (-ε)) (2 * Real.pi / ω) 0).det := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm 0 0 hω A
  -- the damping factors out
  have hdamp : ∀ c : ℝ, Periodic.monodromy (full s 0 ω A c) T 0 =
      -(Real.exp (-(c * s * T)) • Periodic.monodromy (fun t => c • stdForm 0 0 ω A t) T 0) := by
    intro c
    rw [TwoToOne.monodromy_full s 0 hω A c]
    congr 1
    have hfun : (fun t => c • stdForm s 0 ω A t) =
        fun t => c • stdForm 0 0 ω A t - (c * s) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      funext t
      have : slowFlowMatrix s 0 (Element.pump A left right / 2) =
          slowFlowMatrix 0 0 (Element.pump A left right / 2) - s • 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [slowFlowMatrix] <;> ring
      rw [TwoToOne.stdForm_eq, TwoToOne.stdForm_eq 0, this]
      module
    have h := Periodic.transition_sub_smul_one (A := fun t => c • stdForm 0 0 ω A t)
      (M := |c| * MF) ((TwoToOne.continuous_stdForm 0 0 ω A).const_smul c)
      (fun t => by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMF t) (abs_nonneg c))
      (c * s) hT.le
    rw [Periodic.monodromy, Periodic.monodromy, zero_add, hfun, h, sub_zero]
  -- the undamped monodromy has determinant one
  have hdet1 : ∀ c : ℝ, (Periodic.monodromy (fun t => c • stdForm 0 0 ω A t) T 0).det = 1 := by
    intro c
    have h := (ZeroDamping.zero_damping_reciprocal 0 hω A c).1
    rw [TwoToOne.monodromy_full 0 0 hω A c, Matrix.det_neg, Fintype.card_fin] at h
    simpa using h
  have htr := undetuned_trace_even hω A ε
  -- `det(I − ρ Φ₀) = 1 − ρ tr Φ₀ + ρ² det Φ₀` for `2 × 2` matrices
  have hquad : ∀ (ρ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ),
      (1 + -(ρ • X)).det = 1 - ρ * X.trace + ρ ^ 2 * X.det := fun ρ X => by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
  rw [hdamp ε, hdamp (-ε), hquad, hquad, hdet1, hdet1, htr]
  have e : -(-ε * s * T) = ε * s * T := by ring
  rw [e]
  have hx : Real.exp (ε * s * T) * Real.exp (-(ε * s * T)) = 1 := by
    rw [← Real.exp_add]; simp
  set x := Real.exp (ε * s * T)
  set y := Real.exp (-(ε * s * T))
  linear_combination (y - x) * hx

/-! ## The verdict on the undetuned boundary -/

/-- **The undetuned boundary decided at third order, explicitly.** For `TwoToOne.full s 0 ω A ε`
with `s > 0` on the first-order boundary `s² = |g/2|²` (zero detuning, where the second-order
quantity `mixedDet(M, N₂) = T d|g'|²/(4ω)` vanishes): with
`Q = 128 s²|b|² − 16 Re(b̄² g g') − 8 s²|g'|² + |g'|⁴` (`boundaryQuartic`), `Q > 0` gives a Schur
stable monodromy and `Q < 0` Floquet instability for all small `ε > 0`
(`ThirdOrder.full_boundary_third_order`, `undetuned_coefficient`: `K = T²Q/(64ω²)`). -/
@[tmio T, powerlib_foundation] theorem undetuned_boundary {s : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    (0 < boundaryQuartic s (Element.pump A left right) (antiPump A) (rotCoeff A) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LTI.SchurStable (Periodic.monodromy (full s 0 ω A ε) (2 * Real.pi / ω) 0)) ∧
    (boundaryQuartic s (Element.pump A left right) (antiPump A) (rotCoeff A) < 0 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (full s 0 ω A ε) (2 * Real.pi / ω)) := by
  obtain ⟨h1, h2⟩ := ThirdOrder.full_boundary_third_order (d := 0) hω A hs
    (by rw [← hb]; ring) (by ring)
  rw [undetuned_coefficient s hω A hb] at h1 h2
  have hc : 0 < (2 * Real.pi / ω) ^ 2 / (64 * ω ^ 2) := by positivity
  exact ⟨fun h => h1 (mul_pos hc h), fun h => h2 (mul_neg_of_pos_of_neg hc h)⟩

/-- **Two-sided bounds of the quartic form.** On the boundary `|g| = 2s`:
`32 s|b|²(4s − |g'|) + |g'|²(|g'|² − 8s²) ≤ Q ≤ 32 s|b|²(4s + |g'|) + |g'|²(|g'|² − 8s²)`
(`|Re(b̄² g g')| ≤ 2s|b|²|g'|`). In particular `Q = |g'|²(|g'|² − 8s²)` for `b = 0`. -/
@[tmio T, powerlib_foundation] theorem boundaryQuartic_bounds {s : ℝ} {g g' b : ℂ}
    (hg : ‖g‖ = 2 * s) :
    32 * s * ‖b‖ ^ 2 * (4 * s - ‖g'‖) + ‖g'‖ ^ 2 * (‖g'‖ ^ 2 - 8 * s ^ 2) ≤
        boundaryQuartic s g g' b ∧
      boundaryQuartic s g g' b ≤
        32 * s * ‖b‖ ^ 2 * (4 * s + ‖g'‖) + ‖g'‖ ^ 2 * (‖g'‖ ^ 2 - 8 * s ^ 2) := by
  have hre : |((starRingEnd ℂ) b ^ 2 * g * g').re| ≤ 2 * s * ‖b‖ ^ 2 * ‖g'‖ := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj, hg]
    ring
  obtain ⟨h1, h2⟩ := abs_le.mp hre
  rw [boundaryQuartic]
  constructor <;> nlinarith

/-- **Without rotational coefficient the anti-resonant pump decides against `√2 |g|`.** For
`TwoToOne.full s 0 ω A ε`, `s > 0`, on the boundary `s² = |g/2|²` with `rotCoeff A = 0`:
`Q = |g'|²(|g'|² − 2|g|²)`, so `|g'| > √2|g|` gives Schur stability and `0 < |g'| < √2|g|`
Floquet instability for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem undetuned_rotFree {s : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) (hrot : rotCoeff A = 0) :
    (2 * ‖Element.pump A left right‖ ^ 2 < ‖antiPump A‖ ^ 2 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LTI.SchurStable (Periodic.monodromy (full s 0 ω A ε) (2 * Real.pi / ω) 0)) ∧
      (antiPump A ≠ 0 → ‖antiPump A‖ ^ 2 < 2 * ‖Element.pump A left right‖ ^ 2 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (full s 0 ω A ε) (2 * Real.pi / ω)) := by
  have hQ : boundaryQuartic s (Element.pump A left right) (antiPump A) (rotCoeff A) =
      ‖antiPump A‖ ^ 2 * (‖antiPump A‖ ^ 2 - 2 * ‖Element.pump A left right‖ ^ 2) := by
    rw [boundaryQuartic, hrot, norm_div, Complex.norm_ofNat] at *
    simp only [map_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      Complex.zero_re, mul_zero, norm_zero, sub_zero, zero_sub]
    rw [hb]
    ring
  obtain ⟨h1, h2⟩ := undetuned_boundary hω A hs hb
  refine ⟨fun h => h1 ?_, fun h0 h => h2 ?_⟩
  · rw [hQ]
    have : 0 < ‖antiPump A‖ ^ 2 := by nlinarith [sq_nonneg ‖Element.pump A left right‖]
    exact mul_pos this (by linarith)
  · rw [hQ]
    have : 0 < ‖antiPump A‖ ^ 2 := by have := norm_pos_iff.mpr h0; positivity
    exact mul_neg_of_pos_of_neg this (by linarith)

/-- **The undetuned verdict depends on `g'` and `b` at third order.** For every boundary datum
`s > 0`, `g` with `s² = |g/2|²` (zero detuning; the first- and second-order data `s`, `d = 0`, `g`
and `mixedDet(M, N₂) = 0` are common): `boundaryModulation g (2g) 0` (`Q = 128 s⁴`) is Schur stable,
`boundaryModulation g g 0` (`Q = −16 s⁴`) Floquet unstable, and `boundaryModulation g g (j g)`
(`Q = 752 s⁴`) again Schur stable, for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem undetuned_dependence {s : ℝ} (hω : 0 < ω) {g : ℂ}
    (hs : 0 < s) (hb : s ^ 2 = ‖g / 2‖ ^ 2) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable
        (Periodic.monodromy (full s 0 ω (boundaryModulation g (2 * g) 0) ε) (2 * Real.pi / ω) 0)) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
        (full s 0 ω (boundaryModulation g g 0) ε) (2 * Real.pi / ω)) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), LTI.SchurStable (Periodic.monodromy
        (full s 0 ω (boundaryModulation g g (I * g)) ε) (2 * Real.pi / ω) 0)) := by
  obtain ⟨p1, a1, r1⟩ := boundaryModulation_data g (2 * g) 0
  obtain ⟨p2, a2, r2⟩ := boundaryModulation_data g g 0
  obtain ⟨p3, a3, r3⟩ := boundaryModulation_data g g (I * g)
  have hg : ‖g‖ ^ 2 = 4 * s ^ 2 := by
    rw [hb, norm_div, Complex.norm_ofNat]; ring
  have hgg : g.re ^ 2 + g.im ^ 2 = 4 * s ^ 2 := by
    rw [← hg, Complex.sq_norm, Complex.normSq_apply]; ring
  have q1 : boundaryQuartic s g (2 * g) 0 = 128 * s ^ 4 := by
    rw [boundaryQuartic, norm_mul, Complex.norm_ofNat,
      show (2 * ‖g‖) ^ 4 = 16 * (‖g‖ ^ 2) ^ 2 by ring,
      show (2 * ‖g‖) ^ 2 = 4 * ‖g‖ ^ 2 by ring, hg]
    simp only [norm_zero, map_zero, zero_pow two_ne_zero, zero_mul, Complex.zero_re]
    ring
  have q2 : boundaryQuartic s g g 0 = -(16 * s ^ 4) := by
    rw [boundaryQuartic, show ‖g‖ ^ 4 = (‖g‖ ^ 2) ^ 2 by ring, hg]
    simp only [norm_zero, map_zero, zero_pow two_ne_zero, zero_mul, Complex.zero_re]
    ring
  have q3 : boundaryQuartic s g g (I * g) = 752 * s ^ 4 := by
    have hre : ((starRingEnd ℂ) (I * g) ^ 2 * g * g).re = -(4 * s ^ 2) ^ 2 := by
      rw [← hgg]
      simp [sq, Complex.mul_re, Complex.mul_im]
      ring
    rw [boundaryQuartic, show ‖g‖ ^ 4 = (‖g‖ ^ 2) ^ 2 by ring, norm_mul, Complex.norm_I, one_mul,
      hg, hre]
    ring
  have hs4 : 0 < s ^ 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (undetuned_boundary hω _ hs (by rw [p1]; exact hb)).1 ?_
    rw [p1, a1, r1, q1]; positivity
  · refine (undetuned_boundary hω _ hs (by rw [p2]; exact hb)).2 ?_
    rw [p2, a2, r2, q2]; linarith
  · refine (undetuned_boundary hω _ hs (by rw [p3]; exact hb)).1 ?_
    rw [p3, a3, r3, q3]; positivity

end TwoState

end powerlib.ParametricResonance.ThirdOrderClosed
