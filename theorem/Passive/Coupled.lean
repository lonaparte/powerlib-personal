import theorem.Passive.Series
import theorem.Grid.TwoPort
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Coupled windings: two series RLC branches linked by a mutual inductance

Two series RLC branches whose inductors share a magnetic flux. The mutual inductance `M` couples
them: the flux linkages are `ψ₁ = L₁ i₁ + M i₂`, `ψ₂ = M i₁ + L₂ i₂`, the symmetric inductance
matrix `[[L₁, M], [M, L₂]]` applied to the winding currents. A transformer, the coil pair of an
inductive wireless power link and the stator–rotor windings of an induction machine are all
`Passive.Coupled`; the series capacitor of a branch (`S = 1/C`, `theorem/Passive/Series.lean`) is
the compensation capacitor of a resonant coil, `S = 0` a plain winding. No series or parallel
combination of `Passive.SeriesRLC` and `Passive.ParallelRLC` has an off-diagonal inductance, so the
mutual inductance is an element of its own.

Model boundary.
* Two lumped windings, each a series element `primary`, `secondary : Passive.SeriesRLC`
  (`R_k`, self-inductance `L_k`, series elastance `S_k`), and one real mutual inductance `M`.
  Both currents enter the dotted terminals; `M < 0` reverses one winding.
* Element equations, with capacitor charges `q_k' = i_k` and terminal voltages `v_k`:
  `v₁ = R₁ i₁ + L₁ i₁' + M i₂' + S₁ q₁`, `v₂ = R₂ i₂ + M i₁' + L₂ i₂' + S₂ q₂`; at a complex
  frequency `s` the impedance matrix `[[Z₁(s), M s], [M s, Z₂(s)]]` with the branch impedances
  `Z_k(s) = R_k + L_k s + S_k / s` (`impedanceMatrix`).
* Linear magnetics with constant parameters: no saturation, hysteresis or core loss, no
  frequency dependence of the winding resistance (skin and proximity effect), no inter-winding
  capacitance, no radiation. A physical pair has `L₁, L₂ > 0` and `M² ≤ L₁ L₂`; each law states
  what it needs.
* No source, load, converter, controller or rotation: the space-vector use of the flux relations
  (rotor frame, slip) is `theorem/Drives/InductionMachine.lean`, the resonant power link is
  `theorem/WPT/Link.lean`.

Source: the coupled-inductor circuit model (symmetric inductance matrix, coupling coefficient
`k = M / √(L₁ L₂)`, leakage coefficient `σ = 1 − k²`, T equivalent and reflected impedance) of
standard circuit theory; the flux–current algebra of the induction machine (work-sync
`theory/T-field-oriented-control.md` §1.1–§1.4, `theory/T-direct-torque-control.md` §1.2,
`theory/T-sensorless-machine-control.md` §1.2), here for every coupled pair; the two-port algebra
of `theorem/Grid/TwoPort.lean`.

Results.
* `Coupled` (`primary`, `secondary`, `M`), `flux₁`, `flux₂` (on complex currents: phasors or
  space vectors), `magneticEnergy` (`L₁ i₁²/2 + M i₁ i₂ + L₂ i₂²/2`), `leakage`
  (`σ = 1 − M²/(L₁ L₂)`), `coupling` (`k = M/√(L₁ L₂)`), `impedanceMatrix`, `inputImpedance`, the
  T arms `teePrimary`, `teeSecondary`, `teeShunt`.
* Coupling: `coupling_sq` (`k² = M²/(L₁ L₂)`), `leakage_eq` (`σ = 1 − k²`), `abs_coupling_lt_one`
  (`|k| < 1` for a pair with `M² < L₁ L₂`).
* Energy: `two_mul_magneticEnergy` (`2 L₁ W = (L₁ i₁ + M i₂)² + (L₁ L₂ − M²) i₂²`),
  `magneticEnergy_pos_iff` (the stored energy is positive at every nonzero current pair **iff**
  `L₁ > 0` and `M² < L₁ L₂`), `hasDerivAt_magneticEnergy` (the stored energy changes at the
  power `e₁ i₁ + e₂ i₂` delivered by the inductive voltages).
* Flux–current algebra: `current₂_eq` (`i₂ = (ψ₂ − M i₁)/L₂`), `current₁_eq`
  (`i₁ = (ψ₁ − (M/L₂) ψ₂)/(σ L₁)`), `flux₂_eq_leakage` (`ψ₂ = (L₂/M)(ψ₁ − σ L₁ i₁)`),
  `im_conj_flux₁_mul` (`Im(ψ̄₁ i₁) = (M/L₂) Im(ψ̄₂ i₁)`), `normSq_flux₁`, `normSq_flux₂`
  (`|ψ₁|² = L₁²|i₁|² + M²|i₂|² + 2L₁M Re(i₁ ī₂)` and its secondary counterpart: in-phase
  currents add their flux, opposite currents cancel it).
* Frequency domain: `impedanceMatrix_eq_tee` (the pair is the T network of the arms
  `(R₁, L₁ − M, S₁)`, `(R₂, L₂ − M, S₂)` and the shunt inductor `M`), `inputImpedance_jω` (with
  port 2 terminated by `Z_L`, `Z_in(jω) = Z₁(jω) + (ωM)²/(Z₂(jω) + Z_L)`: the reflected
  impedance; the port relations themselves are `Grid.TwoPort.terminated_current`,
  `Grid.TwoPort.terminated_input`).
-/

noncomputable section

namespace powerlib.Passive

open ComplexConjugate

/-- Two coupled windings: two series RLC branches and the mutual inductance `M` between their
inductors. -/
@[ext] structure Coupled where
  /-- The primary winding. -/
  primary : SeriesRLC
  /-- The secondary winding. -/
  secondary : SeriesRLC
  /-- The mutual inductance. -/
  M : ℝ

namespace Coupled

variable (w : Coupled)

/-- The primary flux linkage `ψ₁ = L₁ i₁ + M i₂`. -/
def flux₁ (i₁ i₂ : ℂ) : ℂ := w.primary.L * i₁ + w.M * i₂

/-- The secondary flux linkage `ψ₂ = M i₁ + L₂ i₂`. -/
def flux₂ (i₁ i₂ : ℂ) : ℂ := w.M * i₁ + w.secondary.L * i₂

/-- The magnetic energy `L₁ i₁²/2 + M i₁ i₂ + L₂ i₂²/2`. -/
def magneticEnergy (i₁ i₂ : ℝ) : ℝ :=
  w.primary.L * i₁ ^ 2 / 2 + w.M * i₁ * i₂ + w.secondary.L * i₂ ^ 2 / 2

/-- The leakage coefficient `σ = 1 − M²/(L₁ L₂)`. -/
def leakage : ℝ := 1 - w.M ^ 2 / (w.primary.L * w.secondary.L)

/-- The coupling coefficient `k = M/√(L₁ L₂)`. -/
def coupling : ℝ := w.M / Real.sqrt (w.primary.L * w.secondary.L)

/-- The impedance matrix `[[Z₁(s), M s], [M s, Z₂(s)]]` at the complex frequency `s`. -/
def impedanceMatrix (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![w.primary.impedance s, w.M * s; w.M * s, w.secondary.impedance s]

/-- The input impedance at `s` with the secondary terminated by `Z_L`. -/
def inputImpedance (ZL s : ℂ) : ℂ := Grid.TwoPort.inputImpedance (w.impedanceMatrix s) ZL

/-- The primary arm `(R₁, L₁ − M, S₁)` of the T equivalent. -/
def teePrimary : SeriesRLC := ⟨w.primary.R, w.primary.L - w.M, w.primary.S⟩

/-- The secondary arm `(R₂, L₂ − M, S₂)` of the T equivalent. -/
def teeSecondary : SeriesRLC := ⟨w.secondary.R, w.secondary.L - w.M, w.secondary.S⟩

/-- The shunt inductor `M` of the T equivalent. -/
def teeShunt : SeriesRLC := ⟨0, w.M, 0⟩

/-! ## The coupling coefficient -/

/-- `k² = M²/(L₁ L₂)`. -/
@[tmio M, powerlib_domain] theorem coupling_sq {w : Coupled}
    (h : 0 < w.primary.L * w.secondary.L) :
    w.coupling ^ 2 = w.M ^ 2 / (w.primary.L * w.secondary.L) := by
  rw [coupling, div_pow, Real.sq_sqrt h.le]

/-- The leakage coefficient is `σ = 1 − k²`. -/
@[tmio M, powerlib_domain] theorem leakage_eq {w : Coupled}
    (h : 0 < w.primary.L * w.secondary.L) : w.leakage = 1 - w.coupling ^ 2 := by
  rw [coupling_sq h, leakage]

/-- A pair with `M² < L₁ L₂` has `|k| < 1`. -/
@[tmio M, powerlib_domain] theorem abs_coupling_lt_one {w : Coupled}
    (h : 0 < w.primary.L * w.secondary.L) (hM : w.M ^ 2 < w.primary.L * w.secondary.L) :
    |w.coupling| < 1 := by
  rw [← sq_lt_one_iff_abs_lt_one, coupling_sq h, div_lt_one h]
  exact hM

/-! ## The stored energy -/

/-- Completing the square: `2 L₁ W = (L₁ i₁ + M i₂)² + (L₁ L₂ − M²) i₂²`. -/
@[tmio M, powerlib_domain] theorem two_mul_magneticEnergy (i₁ i₂ : ℝ) :
    2 * w.primary.L * w.magneticEnergy i₁ i₂ =
      (w.primary.L * i₁ + w.M * i₂) ^ 2 + (w.primary.L * w.secondary.L - w.M ^ 2) * i₂ ^ 2 := by
  unfold magneticEnergy
  ring

/-- The stored energy is positive at every nonzero current pair **iff** `L₁ > 0` and
`M² < L₁ L₂`: the inductance matrix is positive definite exactly for a pair with `|k| < 1`. -/
@[tmio M, powerlib_domain] theorem magneticEnergy_pos_iff :
    (∀ i₁ i₂ : ℝ, (i₁ ≠ 0 ∨ i₂ ≠ 0) → 0 < w.magneticEnergy i₁ i₂) ↔
      0 < w.primary.L ∧ w.M ^ 2 < w.primary.L * w.secondary.L := by
  constructor
  · intro h
    have h1 := h 1 0 (Or.inl one_ne_zero)
    have hL : 0 < w.primary.L := by
      simp only [magneticEnergy] at h1
      linarith
    refine ⟨hL, ?_⟩
    have h2 := h (-w.M) w.primary.L (Or.inr hL.ne')
    have e : w.magneticEnergy (-w.M) w.primary.L =
        w.primary.L * (w.primary.L * w.secondary.L - w.M ^ 2) / 2 := by
      unfold magneticEnergy
      ring
    rw [e] at h2
    have : 0 < w.primary.L * (w.primary.L * w.secondary.L - w.M ^ 2) := by linarith
    nlinarith [(pos_iff_pos_of_mul_pos this).mp hL]
  · rintro ⟨hL, hM⟩ i₁ i₂ hi
    have key := w.two_mul_magneticEnergy i₁ i₂
    have hD : 0 < w.primary.L * w.secondary.L - w.M ^ 2 := by linarith
    rcases hi with hi | hi
    · by_cases h2 : i₂ = 0
      · subst h2
        have : 0 < w.primary.L * i₁ ^ 2 := by positivity
        unfold magneticEnergy
        nlinarith
      · have : 0 < (w.primary.L * w.secondary.L - w.M ^ 2) * i₂ ^ 2 := by positivity
        nlinarith [sq_nonneg (w.primary.L * i₁ + w.M * i₂)]
    · have : 0 < (w.primary.L * w.secondary.L - w.M ^ 2) * i₂ ^ 2 := by positivity
      nlinarith [sq_nonneg (w.primary.L * i₁ + w.M * i₂)]

/-- Energy balance of the windings: if `L₁ i₁' + M i₂' = e₁` and `M i₁' + L₂ i₂' = e₂` at `t`
(`e_k` the inductive voltage of winding `k`), the stored energy changes at `e₁ i₁ + e₂ i₂`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_magneticEnergy {i₁ i₂ : ℝ → ℝ} {t i₁' i₂' e₁ e₂ : ℝ}
    (h₁ : HasDerivAt i₁ i₁' t) (h₂ : HasDerivAt i₂ i₂' t)
    (he₁ : w.primary.L * i₁' + w.M * i₂' = e₁) (he₂ : w.M * i₁' + w.secondary.L * i₂' = e₂) :
    HasDerivAt (fun τ => w.magneticEnergy (i₁ τ) (i₂ τ)) (e₁ * i₁ t + e₂ * i₂ t) t := by
  unfold magneticEnergy
  have hA := ((h₁.fun_pow 2).const_mul w.primary.L).div_const 2
  have hB := (h₁.const_mul w.M).mul h₂
  have hC := ((h₂.fun_pow 2).const_mul w.secondary.L).div_const 2
  refine ((hA.add hB).add hC).congr_deriv ?_
  rw [← he₁, ← he₂]
  push_cast
  ring

/-! ## Flux–current algebra -/

/-- The secondary current from the secondary flux and the primary current:
`i₂ = (ψ₂ − M i₁)/L₂`. -/
@[tmio M, powerlib_domain] theorem current₂_eq {w : Coupled} (hL₂ : w.secondary.L ≠ 0)
    (i₁ i₂ : ℂ) : i₂ = (w.flux₂ i₁ i₂ - w.M * i₁) / w.secondary.L := by
  have : (w.secondary.L : ℂ) ≠ 0 := by exact_mod_cast hL₂
  unfold flux₂
  field_simp
  ring

/-- The primary current from the two fluxes: `i₁ = (ψ₁ − (M/L₂) ψ₂)/(σ L₁)`. -/
@[tmio M, powerlib_domain] theorem current₁_eq {w : Coupled} (hL₂ : w.secondary.L ≠ 0)
    (hσ : w.leakage * w.primary.L ≠ 0) (i₁ i₂ : ℂ) :
    i₁ = (w.flux₁ i₁ i₂ - (w.M / w.secondary.L : ℝ) * w.flux₂ i₁ i₂) /
      (w.leakage * w.primary.L : ℝ) := by
  have h3 : (w.secondary.L : ℂ) ≠ 0 := by exact_mod_cast hL₂
  have hσ' : ((w.leakage * w.primary.L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ
  rw [eq_div_iff hσ']
  have hs : w.leakage * w.primary.L = w.primary.L - w.M ^ 2 / w.secondary.L := by
    unfold leakage
    by_cases hL₁ : w.primary.L = 0
    · simp [hL₁, leakage] at hσ
    · field_simp
  rw [hs]
  unfold flux₁ flux₂
  push_cast
  field_simp
  ring

/-- The secondary flux from the primary flux and current (the voltage model of a machine):
`ψ₂ = (L₂/M)(ψ₁ − σ L₁ i₁)`. -/
@[tmio M, powerlib_domain] theorem flux₂_eq_leakage {w : Coupled} (hM : w.M ≠ 0)
    (hL₁ : w.primary.L ≠ 0) (hL₂ : w.secondary.L ≠ 0) (i₁ i₂ : ℂ) :
    w.flux₂ i₁ i₂ = (w.secondary.L / w.M : ℝ) *
      (w.flux₁ i₁ i₂ - (w.leakage * w.primary.L : ℝ) * i₁) := by
  have h1 : (w.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have h2 : (w.primary.L : ℂ) ≠ 0 := by exact_mod_cast hL₁
  have h3 : (w.secondary.L : ℂ) ≠ 0 := by exact_mod_cast hL₂
  unfold flux₁ flux₂ leakage
  push_cast
  field_simp
  ring

/-- `Im(ψ̄₁ i₁) = (M/L₂) Im(ψ̄₂ i₁)`: only the mutual flux crosses the primary current. -/
@[tmio M, powerlib_domain] theorem im_conj_flux₁_mul {w : Coupled} (hL₂ : w.secondary.L ≠ 0)
    (i₁ i₂ : ℂ) :
    (conj (w.flux₁ i₁ i₂) * i₁).im = w.M / w.secondary.L * (conj (w.flux₂ i₁ i₂) * i₁).im := by
  simp only [flux₁, flux₂, map_add, map_mul, Complex.conj_ofReal, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- The magnitude of the primary flux: `|ψ₁|² = L₁²|i₁|² + M²|i₂|² + 2 L₁ M Re(i₁ ī₂)`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₁ (i₁ i₂ : ℂ) :
    Complex.normSq (w.flux₁ i₁ i₂) = w.primary.L ^ 2 * Complex.normSq i₁ +
      w.M ^ 2 * Complex.normSq i₂ + 2 * w.primary.L * w.M * (i₁ * conj i₂).re := by
  simp only [flux₁, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The magnitude of the secondary flux: `|ψ₂|² = M²|i₁|² + L₂²|i₂|² + 2 M L₂ Re(i₁ ī₂)`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₂ (i₁ i₂ : ℂ) :
    Complex.normSq (w.flux₂ i₁ i₂) = w.M ^ 2 * Complex.normSq i₁ +
      w.secondary.L ^ 2 * Complex.normSq i₂ + 2 * w.M * w.secondary.L * (i₁ * conj i₂).re := by
  simp only [flux₂, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ## The frequency domain -/

/-- The coupled pair is the T network of the arms `(R₁, L₁ − M, S₁)`, `(R₂, L₂ − M, S₂)` and the
shunt inductor `M`, at every complex frequency. -/
@[tmio M, powerlib_domain] theorem impedanceMatrix_eq_tee (s : ℂ) :
    w.impedanceMatrix s = Grid.TwoPort.tee (w.teePrimary.impedance s)
      (w.teeSecondary.impedance s) (w.teeShunt.impedance s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [impedanceMatrix, Grid.TwoPort.tee, teePrimary, teeSecondary, teeShunt,
      SeriesRLC.impedance] <;> ring

/-- The reflected impedance: with the secondary terminated by `Z_L`, the input impedance at
`s = jω` is `Z₁(jω) + (ωM)²/(Z₂(jω) + Z_L)`. -/
@[tmio M, powerlib_domain] theorem inputImpedance_jω (ZL : ℂ) (ω : ℝ) :
    w.inputImpedance ZL (ω * Complex.I) =
      w.primary.impedance (ω * Complex.I) +
        ((ω * w.M : ℝ) : ℂ) ^ 2 / (w.secondary.impedance (ω * Complex.I) + ZL) := by
  have e : (w.M : ℂ) * (ω * Complex.I) * ((w.M : ℂ) * (ω * Complex.I)) =
      -(((ω * w.M : ℝ) : ℂ) ^ 2) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [inputImpedance, Grid.TwoPort.inputImpedance, impedanceMatrix, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [e, neg_div, sub_neg_eq_add]

end Coupled

end powerlib.Passive
