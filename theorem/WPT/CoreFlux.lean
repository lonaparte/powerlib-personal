import theorem.WPT.Gyrator
import theorem.SpecialFunctions.TripleEnvelope

/-! # The shared-core flux limit of the lossless resonant link

A coil pair wound on one magnetic core saturates on the flux in the core, not on the winding flux
linkages `ψ₁ = L₁I₁ + MI₂`, `ψ₂ = MI₁ + L₂I₂`, which also count the leakage flux closing outside
the core. With a turns ratio `a` (physically `N₁/N₂`) the pair is the T model of magnetizing
inductance `L_m = aM` and leakage inductances `L_l1 = L₁ − aM`, `L_l2 = L₂ − M/a`; the magnetizing
current is `I_m = I₁ + I₂/a` and the core flux linkage referred to the primary is
`ψ_m = L_m I_m = aM I₁ + M I₂`, so that `ψ₁ = L_l1 I₁ + ψ_m` and `ψ₂ = L_l2 I₂ + ψ_m/a`.

On the lossless resonant link the power is `P = ωM Im(I₁Ī₂)` (`Gyrator.power₁_eq`) and the bridges
are the bidisk `‖I₁‖ ≤ ρ₂/|ωM|`, `‖I₂‖ ≤ ρ₁/|ωM|` (`CurrentLimits.reachable_iff`). A further
condition on the currents that conjugation keeps leaves a set of cross terms `Im(I₁Ī₂)` symmetric
about zero, so the largest power is `|ωM|` times the largest cross term
(`isGreatest_power_of_cross`), and every flux limit is a bound `‖pI₁ + qI₂‖ ≤ |Ψ|` with real `p`,
`q`. Under the core flux limit and both bridges the complex form of `reactiveMax`
(`SpecialFunctions.isGreatest_im_mul_conj`) gives the exact limit
`P² ≤ ω²/(4a²M²) · reactiveMax(a²M²(ρ₂/|ωM|)², M²(ρ₁/|ωM|)², Ψ_m²)` (`coreLimit`), attained:
the primary-flux limit `ReactiveLimits.limit₁` with `L₁` replaced by `aM`.

Under both bridges, the core flux and both winding fluxes, five bounds `‖p_iI₁ + q_iI₂‖ ≤ r_i`,
Helly's theorem in `ℝ³` (`SpecialFunctions.isGreatest_im_mul_conj_of_triples`) reduces the
problem to the ten triples of bounds. A triple has the closed form `SpecialFunctions.tripleMax`
when its coefficient vectors `(p_i, q_i)` are pairwise independent; for the five bounds
(`(1, 0)`, `(0, 1)`, `(aM, M)`, `(L₁, M)`, `(M, L₂)`) the ten pairwise determinants are `1`, `M`,
`M`, `L₂`, `−aM`, `−L₁`, `−M`, `−M L_l1`, `aM L_l2` and `L₁L₂ − M²` (pairs in lexicographic
order). The exact power is `|ωM|` times the smallest of the ten triple values (`coreEnvelope`).
The triples containing both bridges are the problems of `isGreatest_power_core`,
`ReactiveLimits.isGreatest_power₁` and `ReactiveLimits.isGreatest_power₂`.

Model boundary.
* The lossless resonant link of `theorem/WPT/Gyrator.lean`: the coil pair `w : Passive.Coupled`
  with lossless windings `R₁ = R₂ = 0`, both coils resonant `X₁(ω) = X₂(ω) = 0`, `ωM ≠ 0`, both
  ports driven by the fundamental phasors `V₁`, `V₂` of two bridges (`CurrentLimits.Driven`) with
  `‖V_k‖ ≤ ρ_k` (`ρ_k ≥ 0` for attainment); RMS phasors in sinusoidal steady state,
  fundamental-harmonic approximation; no sign condition on the reactive power (soft switching is
  not required). Lossy windings are not covered.
* The T model holds for every turns ratio `a ≠ 0` as an exact rewriting of the inductance matrix;
  reading `ψ_m` as the core flux linkage (`ψ_m/N₁` the core flux) is the modelling assumption,
  for `a = N₁/N₂` and with all mutual flux in the core and all leakage flux outside it. The core
  limit bounds the fundamental phasor, `normSq ψ_m ≤ Ψ_m²`, the winding limits bound
  `normSq ψ_k ≤ Ψ_k²` (`Passive.Coupled.flux₁`, `flux₂`); only `Ψ²` enters, so the bounds may
  have either sign. Linear magnetics up to the limits: the nonlinear magnetization curve,
  hysteresis and core loss are not modelled.
* The five-bound result assumes `a, L₁, L₂ ≠ 0`, `L₁L₂ − M² ≠ 0` and nonzero leakage inductances
  `L_l1`, `L_l2`. A vanishing leakage (the core flux equals a winding flux) or `L₁L₂ = M²` makes
  two bounds parallel; that case is not covered here (the generic reduction
  `SpecialFunctions.isGreatest_im_mul_conj_of_three` still applies with other triple values).

Source: the T equivalent circuit of a transformer referred through a turns ratio (magnetizing and
leakage inductances; the case `a = 1` is `Passive.Coupled.impedanceMatrix_eq_tee`); the gyrator
law of `theorem/WPT/Gyrator.lean`, the reachable currents of `theorem/WPT/CurrentLimits.lean`;
the complex form of `reactiveMax` (`theorem/SpecialFunctions/ComplexProduct.lean`), the Helly
reduction and the triple values of `theorem/SpecialFunctions/TripleEnvelope.lean`.

Results.
* T model: `magnetizingInductance`, `leakageInductance₁`, `leakageInductance₂`,
  `magnetizingCurrent`, `coreFlux` (definitions); `coreFlux_eq_mul` (`ψ_m = L_m I_m`, `a ≠ 0`),
  `flux₁_eq_core` (`ψ₁ = L_l1 I₁ + ψ_m`), `flux₂_eq_core` (`ψ₂ = L_l2 I₂ + ψ_m/a`, `a ≠ 0`).
* `isGreatest_power_of_cross`: for any condition `C` on the currents kept by conjugation, if `m`
  is the largest cross term `Im(I₁Ī₂)` over the bridge bidisk under `C`, then `|ωM| m` is the
  largest power under both bridges and `C`.
* Core flux and both bridges: `coreLimit` (definition), `power_sq_le_coreLimit` (`P² ≤ coreLimit`),
  `isGreatest_power_core` (the largest power is `√coreLimit`).
* Both bridges, core flux and both winding fluxes: `constraintCoeff₁`, `constraintCoeff₂`,
  `constraintRadius` (the five bounds `‖p_iI₁ + q_iI₂‖ ≤ r_i`), `constraintTriples` (the ten
  triples), `coreEnvelope` (`|ωM|` times the smallest `tripleMax` of the triples)
  (definitions); `isGreatest_power_coreEnvelope` (the largest power is `coreEnvelope`).
-/

noncomputable section

namespace powerlib.WPT.CoreFlux

open Complex ComplexConjugate CurrentLimits

/-! ## The T model with a turns ratio -/

/-- The magnetizing inductance `L_m = aM` of the T model with turns ratio `a`. -/
def magnetizingInductance (w : Passive.Coupled) (a : ℝ) : ℝ := a * w.M

/-- The primary leakage inductance `L_l1 = L₁ − aM`. -/
def leakageInductance₁ (w : Passive.Coupled) (a : ℝ) : ℝ := w.primary.L - a * w.M

/-- The secondary leakage inductance `L_l2 = L₂ − M/a`. -/
def leakageInductance₂ (w : Passive.Coupled) (a : ℝ) : ℝ := w.secondary.L - w.M / a

/-- The magnetizing current `I_m = i₁ + i₂/a`. -/
def magnetizingCurrent (a : ℝ) (i₁ i₂ : ℂ) : ℂ := i₁ + i₂ / a

/-- The core flux linkage referred to the primary, `ψ_m = aM i₁ + M i₂`. -/
def coreFlux (w : Passive.Coupled) (a : ℝ) (i₁ i₂ : ℂ) : ℂ :=
  ((a * w.M : ℝ) : ℂ) * i₁ + w.M * i₂

variable {w : Passive.Coupled} {a ω : ℝ}

/-- The core flux linkage is the magnetizing inductance times the magnetizing current:
`ψ_m = L_m I_m`. -/
@[tmio M, powerlib_domain] theorem coreFlux_eq_mul (ha : a ≠ 0) (i₁ i₂ : ℂ) :
    coreFlux w a i₁ i₂ = (magnetizingInductance w a : ℂ) * magnetizingCurrent a i₁ i₂ := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  simp only [coreFlux, magnetizingInductance, magnetizingCurrent]
  push_cast
  field_simp

/-- The primary flux linkage is the primary leakage flux plus the core flux:
`ψ₁ = L_l1 i₁ + ψ_m`. -/
@[tmio M, powerlib_domain] theorem flux₁_eq_core (i₁ i₂ : ℂ) :
    w.flux₁ i₁ i₂ = (leakageInductance₁ w a : ℂ) * i₁ + coreFlux w a i₁ i₂ := by
  simp only [Passive.Coupled.flux₁, leakageInductance₁, coreFlux]
  push_cast
  ring

/-- The secondary flux linkage is the secondary leakage flux plus the core flux referred to the
secondary: `ψ₂ = L_l2 i₂ + ψ_m/a`. -/
@[tmio M, powerlib_domain] theorem flux₂_eq_core (ha : a ≠ 0) (i₁ i₂ : ℂ) :
    w.flux₂ i₁ i₂ = (leakageInductance₂ w a : ℂ) * i₂ + coreFlux w a i₁ i₂ / a := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  simp only [Passive.Coupled.flux₂, leakageInductance₂, coreFlux]
  push_cast
  field_simp
  ring

/-! ## Power and cross term -/

/-- A flux bound in squared form is a norm bound: `‖z‖ ≤ |Ψ| ↔ normSq z ≤ Ψ²`. -/
@[tmio T, powerlib_foundation] private theorem norm_le_abs_iff {z : ℂ} {Ψ : ℝ} :
    ‖z‖ ≤ |Ψ| ↔ normSq z ≤ Ψ ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, ← sq_abs Ψ]
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).symm

/-- Conjugating both currents conjugates the core flux. -/
@[tmio M, powerlib_domain] private theorem coreFlux_conj (i₁ i₂ : ℂ) :
    coreFlux w a (conj i₁) (conj i₂) = conj (coreFlux w a i₁ i₂) := by
  simp only [coreFlux, map_add, map_mul, Complex.conj_ofReal]

/-- Conjugating both currents conjugates the winding fluxes. -/
@[tmio M, powerlib_domain] private theorem flux_conj (i₁ i₂ : ℂ) :
    w.flux₁ (conj i₁) (conj i₂) = conj (w.flux₁ i₁ i₂) ∧
      w.flux₂ (conj i₁) (conj i₂) = conj (w.flux₂ i₁ i₂) := by
  simp only [Passive.Coupled.flux₁, Passive.Coupled.flux₂, map_add, map_mul,
    Complex.conj_ofReal, and_self]

/-- The largest power of the lossless resonant link under both bridges and any condition `C` on
the currents that conjugation keeps is `|ωM|` times the largest cross term `Im(I₁Ī₂)` over the
bridge bidisk `‖I₁‖ ≤ ρ₂/|ωM|`, `‖I₂‖ ≤ ρ₁/|ωM|` under `C`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_of_cross {ρ₁ ρ₂ m : ℝ} {C : ℂ → ℂ → Prop}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0)
    (hC : ∀ I₁ I₂, C I₁ I₂ → C (conj I₁) (conj I₂))
    (h : IsGreatest {x : ℝ | ∃ I₁ I₂ : ℂ, ‖I₁‖ ≤ ρ₂ / |ω * w.M| ∧ ‖I₂‖ ≤ ρ₁ / |ω * w.M| ∧
      C I₁ I₂ ∧ x = (I₁ * conj I₂).im} m) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      C I₁ I₂ ∧ P = (V₁ * conj I₁).re} (|ω * w.M| * m) := by
  have hconj : ∀ I₁ I₂ : ℂ, (conj I₁ * conj (conj I₂)).im = -(I₁ * conj I₂).im := by
    intro I₁ I₂
    simp only [Complex.conj_conj, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  constructor
  · obtain ⟨I₁, I₂, h₁, h₂, hc, rfl⟩ := h.1
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · -- `ωM < 0`: the conjugate currents
      obtain ⟨V₁, V₂, hV₁, hV₂, hd⟩ := (reachable_iff w ω (conj I₁) (conj I₂) hX₁ hX₂ hR₁ hR₂
        hm).mpr ⟨by rwa [Complex.norm_conj], by rwa [Complex.norm_conj]⟩
      refine ⟨V₁, V₂, conj I₁, conj I₂, hV₁, hV₂, hd, hC _ _ hc, ?_⟩
      rw [Gyrator.power₁_eq hX₁ hX₂ hR₁ hR₂ hd, hconj, abs_of_neg hneg]
      ring
    · obtain ⟨V₁, V₂, hV₁, hV₂, hd⟩ :=
        (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mpr ⟨h₁, h₂⟩
      refine ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, hd, hc, ?_⟩
      rw [Gyrator.power₁_eq hX₁ hX₂ hR₁ hR₂ hd, abs_of_pos hpos]
  · rintro P ⟨V₁, V₂, I₁, I₂, hV₁, hV₂, hd, hc, rfl⟩
    obtain ⟨h₁, h₂⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, hV₁, hV₂, hd⟩
    have u₁ : (I₁ * conj I₂).im ≤ m := h.2 ⟨I₁, I₂, h₁, h₂, hc, rfl⟩
    have u₂ : (conj I₁ * conj (conj I₂)).im ≤ m := h.2 ⟨conj I₁, conj I₂,
      by rwa [Complex.norm_conj], by rwa [Complex.norm_conj], hC _ _ hc, rfl⟩
    rw [hconj] at u₂
    rw [Gyrator.power₁_eq hX₁ hX₂ hR₁ hR₂ hd]
    rcases abs_cases (ω * w.M) with ⟨he, hs⟩ | ⟨he, hs⟩ <;> rw [he] <;> nlinarith

/-! ## The core flux limit -/

/-- The squared power limit under both bridges and the core flux bound `normSq ψ_m ≤ Ψ_m²`:
`ω²/(4a²M²) · reactiveMax(a²M²(ρ₂/|ωM|)², M²(ρ₁/|ωM|)², Ψ_m²)`. -/
def coreLimit (w : Passive.Coupled) (a ω ρ₁ ρ₂ Ψm : ℝ) : ℝ :=
  ω ^ 2 / (4 * (a * w.M) ^ 2) * SpecialFunctions.reactiveMax
    ((a * w.M) ^ 2 * (ρ₂ / |ω * w.M|) ^ 2) (w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) (Ψm ^ 2)

/-- Under both bridges and the core flux bound, whatever the reactive power:
`P² ≤ coreLimit`. -/
@[tmio M, powerlib_domain] theorem power_sq_le_coreLimit {ρ₁ ρ₂ Ψm : ℝ} {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0) (ha : a ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ : normSq (coreFlux w a I₁ I₂) ≤ Ψm ^ 2) :
    (V₁ * conj I₁).re ^ 2 ≤ coreLimit w a ω ρ₁ ρ₂ Ψm := by
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  obtain ⟨hI₁, hI₂⟩ := (reachable_iff w ω I₁ I₂ hX₁ hX₂ hR₁ hR₂ hm).mp ⟨V₁, V₂, h₁, h₂, h⟩
  have hR := SpecialFunctions.sq_im_mul_conj_le_reactiveMax (p := a * w.M) (q := w.M) hI₁ hI₂
    (norm_le_abs_iff.mpr hψ)
  rw [sq_abs] at hR
  rw [Gyrator.power₁_eq hX₁ hX₂ hR₁ hR₂ h, coreLimit, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  calc (ω * w.M * (I₁ * conj I₂).im) ^ 2 * (4 * (a * w.M) ^ 2) =
        ω ^ 2 * (4 * (a * w.M) ^ 2 * w.M ^ 2 * (I₁ * conj I₂).im ^ 2) := by ring
    _ ≤ ω ^ 2 * SpecialFunctions.reactiveMax ((a * w.M) ^ 2 * (ρ₂ / |ω * w.M|) ^ 2)
          (w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) (Ψm ^ 2) :=
        mul_le_mul_of_nonneg_left hR (sq_nonneg ω)

/-- The exact largest power under both bridges and the core flux bound, whatever the reactive
power: `√coreLimit`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_core {ρ₁ ρ₂ Ψm : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0) (ha : a ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (coreFlux w a I₁ I₂) ≤ Ψm ^ 2 ∧ P = (V₁ * conj I₁).re}
      (Real.sqrt (coreLimit w a ω ρ₁ ρ₂ Ψm)) := by
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hcross := SpecialFunctions.isGreatest_im_mul_conj (mul_ne_zero ha hM) hM
    (div_nonneg hρ₂ hma.le) (div_nonneg hρ₁ hma.le) (abs_nonneg Ψm)
  rw [sq_abs] at hcross
  set R := SpecialFunctions.reactiveMax ((a * w.M) ^ 2 * (ρ₂ / |ω * w.M|) ^ 2)
    (w.M ^ 2 * (ρ₁ / |ω * w.M|) ^ 2) (Ψm ^ 2) with hRdef
  have hR0 : 0 ≤ R := SpecialFunctions.reactiveMax_nonneg (by positivity) (by positivity)
    (sq_nonneg _)
  have h := isGreatest_power_of_cross (ρ₁ := ρ₁) (ρ₂ := ρ₂)
    (C := fun I₁ I₂ => normSq (coreFlux w a I₁ I₂) ≤ Ψm ^ 2) hX₁ hX₂ hR₁ hR₂ hm
    (fun I₁ I₂ hc => by
      show normSq (coreFlux w a (conj I₁) (conj I₂)) ≤ Ψm ^ 2
      rwa [coreFlux_conj, Complex.normSq_conj])
    (by simpa only [coreFlux, norm_le_abs_iff] using hcross)
  have hval : |ω * w.M| * (Real.sqrt R / (2 * |a * w.M * w.M|)) =
      Real.sqrt (coreLimit w a ω ρ₁ ρ₂ Ψm) := by
    have e : (|ω * w.M| * (Real.sqrt R / (2 * |a * w.M * w.M|))) ^ 2 =
        coreLimit w a ω ρ₁ ρ₂ Ψm := by
      rw [mul_pow, div_pow, Real.sq_sqrt hR0, mul_pow, sq_abs, sq_abs, coreLimit, ← hRdef]
      field_simp
      ring
    rw [← e, Real.sqrt_sq (by positivity)]
  rw [← hval]
  exact h

/-! ## Both bridges, the core flux and both winding fluxes -/

/-- The coefficients of `I₁` in the five bounds `‖p_iI₁ + q_iI₂‖ ≤ r_i`: the secondary bridge,
the primary bridge, the core flux, the primary and the secondary winding flux. -/
def constraintCoeff₁ (w : Passive.Coupled) (a : ℝ) : Fin 5 → ℝ :=
  ![1, 0, a * w.M, w.primary.L, w.M]

/-- The coefficients of `I₂` in the five bounds. -/
def constraintCoeff₂ (w : Passive.Coupled) : Fin 5 → ℝ := ![0, 1, w.M, w.M, w.secondary.L]

/-- The radii of the five bounds: `ρ₂/|ωM|`, `ρ₁/|ωM|`, `|Ψ_m|`, `|Ψ₁|`, `|Ψ₂|`. -/
def constraintRadius (w : Passive.Coupled) (ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ : ℝ) : Fin 5 → ℝ :=
  ![ρ₂ / |ω * w.M|, ρ₁ / |ω * w.M|, |Ψm|, |Ψ₁|, |Ψ₂|]

/-- The ten triples of the five bounds. -/
def constraintTriples : Finset (Fin 5 × Fin 5 × Fin 5) :=
  {(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 3), (0, 2, 4), (0, 3, 4), (1, 2, 3), (1, 2, 4),
    (1, 3, 4), (2, 3, 4)}

/-- The largest power under both bridges, the core flux and both winding fluxes: `|ωM|` times the
smallest over the ten triples of the largest cross term `tripleMax` under the three bounds. -/
def coreEnvelope (w : Passive.Coupled) (a ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ : ℝ) : ℝ :=
  |ω * w.M| * constraintTriples.inf' ⟨(0, 1, 2), by decide⟩ fun t =>
    SpecialFunctions.tripleMax
      (constraintCoeff₁ w a t.1) (constraintCoeff₂ w t.1) (constraintRadius w ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ t.1)
      (constraintCoeff₁ w a t.2.1) (constraintCoeff₂ w t.2.1)
        (constraintRadius w ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ t.2.1)
      (constraintCoeff₁ w a t.2.2) (constraintCoeff₂ w t.2.2)
        (constraintRadius w ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ t.2.2)

/-- The exact largest power under both bridges, the core flux bound and both winding flux bounds,
whatever the reactive power: `coreEnvelope`, for nonzero leakage inductances and
`L₁L₂ − M² ≠ 0`. -/
@[tmio M, powerlib_domain] theorem isGreatest_power_coreEnvelope {ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : w.primary.R = 0) (hR₂ : w.secondary.R = 0) (hm : ω * w.M ≠ 0) (ha : a ≠ 0)
    (hL₁ : w.primary.L ≠ 0) (hL₂ : w.secondary.L ≠ 0)
    (hD : w.primary.L * w.secondary.L - w.M ^ 2 ≠ 0) (hl₁ : leakageInductance₁ w a ≠ 0)
    (hl₂ : leakageInductance₂ w a ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        normSq (coreFlux w a I₁ I₂) ≤ Ψm ^ 2 ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
          normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = (V₁ * conj I₁).re}
      (coreEnvelope w a ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂) := by
  have hM : w.M ≠ 0 := right_ne_zero_of_mul hm
  have hma : 0 < |ω * w.M| := abs_pos.mpr hm
  have hr : ∀ i, 0 ≤ constraintRadius w ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ i := by
    intro i
    fin_cases i
    · exact div_nonneg hρ₂ hma.le
    · exact div_nonneg hρ₁ hma.le
    · exact abs_nonneg Ψm
    · exact abs_nonneg Ψ₁
    · exact abs_nonneg Ψ₂
  -- the ten pairwise determinants
  have d₁ : a * w.M * w.M - w.primary.L * w.M ≠ 0 := by
    have : -(w.M * leakageInductance₁ w a) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hM hl₁)
    rwa [leakageInductance₁, show -(w.M * (w.primary.L - a * w.M)) =
      a * w.M * w.M - w.primary.L * w.M by ring] at this
  have d₂ : a * w.M * w.secondary.L - w.M * w.M ≠ 0 := by
    have : a * w.M * leakageInductance₂ w a ≠ 0 := mul_ne_zero (mul_ne_zero ha hM) hl₂
    rwa [leakageInductance₂, show a * w.M * (w.secondary.L - w.M / a) =
      a * w.M * w.secondary.L - w.M * w.M by field_simp] at this
  have d₁' : w.primary.L * w.M - a * w.M * w.M ≠ 0 := fun h => d₁ (by linarith)
  have d₂' : w.M * w.M - a * w.M * w.secondary.L ≠ 0 := fun h => d₂ (by linarith)
  have d₃ : w.primary.L * w.secondary.L - w.M * w.M ≠ 0 := by rwa [← sq]
  have d₃' : w.M * w.M - w.primary.L * w.secondary.L ≠ 0 := fun h => d₃ (by linarith)
  have hdet : ∀ i j : Fin 5, i ≠ j →
      constraintCoeff₁ w a i * constraintCoeff₂ w j - constraintCoeff₁ w a j * constraintCoeff₂ w i
        ≠ 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [constraintCoeff₁, constraintCoeff₂] at hij ⊢ <;>
      first
        | exact hM | exact hL₁ | exact hL₂ | exact ⟨ha, hM⟩ | exact d₁ | exact d₁' | exact d₂
        | exact d₂' | exact d₃ | exact d₃'
  have hdistinct : ∀ t ∈ constraintTriples, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 := by
    intro t ht
    simp only [constraintTriples, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hcross := SpecialFunctions.isGreatest_im_mul_conj_of_triples hr (𝒯 := constraintTriples)
    ⟨(0, 1, 2), by decide⟩ (by decide) fun t ht =>
      SpecialFunctions.isGreatest_tripleMax (hdet _ _ (hdistinct t ht).1)
        (hdet _ _ (hdistinct t ht).2.1) (hdet _ _ (hdistinct t ht).2.2) (hr _) (hr _) (hr _)
  -- the five bounds are the bridges and the three flux limits
  have hS : {x : ℝ | ∃ z₁ z₂ : ℂ, (∀ i, ‖(constraintCoeff₁ w a i : ℂ) * z₁ +
      (constraintCoeff₂ w i : ℂ) * z₂‖ ≤ constraintRadius w ω ρ₁ ρ₂ Ψm Ψ₁ Ψ₂ i) ∧
        x = (z₁ * conj z₂).im} =
      {x : ℝ | ∃ I₁ I₂ : ℂ, ‖I₁‖ ≤ ρ₂ / |ω * w.M| ∧ ‖I₂‖ ≤ ρ₁ / |ω * w.M| ∧
        (normSq (coreFlux w a I₁ I₂) ≤ Ψm ^ 2 ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
          normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) ∧ x = (I₁ * conj I₂).im} := by
    have e₀ : ∀ I₁ I₂ : ℂ, ‖((1 : ℝ) : ℂ) * I₁ + ((0 : ℝ) : ℂ) * I₂‖ = ‖I₁‖ := by simp
    have e₁ : ∀ I₁ I₂ : ℂ, ‖((0 : ℝ) : ℂ) * I₁ + ((1 : ℝ) : ℂ) * I₂‖ = ‖I₂‖ := by simp
    ext x
    constructor
    · rintro ⟨I₁, I₂, h, rfl⟩
      have h₀ : ‖((1 : ℝ) : ℂ) * I₁ + ((0 : ℝ) : ℂ) * I₂‖ ≤ ρ₂ / |ω * w.M| := h 0
      have h₁ : ‖((0 : ℝ) : ℂ) * I₁ + ((1 : ℝ) : ℂ) * I₂‖ ≤ ρ₁ / |ω * w.M| := h 1
      rw [e₀] at h₀
      rw [e₁] at h₁
      exact ⟨I₁, I₂, h₀, h₁, ⟨norm_le_abs_iff.mp (h 2), norm_le_abs_iff.mp (h 3),
        norm_le_abs_iff.mp (h 4)⟩, rfl⟩
    · rintro ⟨I₁, I₂, h₀, h₁, ⟨h₂, h₃, h₄⟩, rfl⟩
      refine ⟨I₁, I₂, fun i => ?_, rfl⟩
      fin_cases i
      · show ‖((1 : ℝ) : ℂ) * I₁ + ((0 : ℝ) : ℂ) * I₂‖ ≤ ρ₂ / |ω * w.M|
        rwa [e₀]
      · show ‖((0 : ℝ) : ℂ) * I₁ + ((1 : ℝ) : ℂ) * I₂‖ ≤ ρ₁ / |ω * w.M|
        rwa [e₁]
      · exact norm_le_abs_iff.mpr h₂
      · exact norm_le_abs_iff.mpr h₃
      · exact norm_le_abs_iff.mpr h₄
  rw [hS] at hcross
  have h := isGreatest_power_of_cross (C := fun I₁ I₂ => normSq (coreFlux w a I₁ I₂) ≤ Ψm ^ 2 ∧
      normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2) hX₁ hX₂ hR₁ hR₂ hm
    (fun I₁ I₂ hc => by
      simp only [coreFlux_conj, (flux_conj I₁ I₂).1, (flux_conj I₁ I₂).2, Complex.normSq_conj]
      exact hc) hcross
  simp only [and_assoc] at h
  exact h

end powerlib.WPT.CoreFlux
