import theorem.GridTiedConverter.GFM.FullModel.BoundaryLayer
import theorem.Spectral.Family
import theorem.LTI.Plant
import theorem.Criteria.Routh4

/-! # The grid-forming inner voltage/current cascade, one axis (model layer)

Model boundary.
* System: one axis of the inner control of a grid-forming converter behind an LC filter, the
  cascade of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (PI voltage loop on the filter
  capacitor, PI current loop on the converter-side inductor) with its ideal design: full
  capacitor-voltage feed-forward and cross decoupling in the current loop (the `v_c` and
  `jω₀L_f i` terms cancelled), full capacitor-current decoupling (`k_dv = 1`) and full
  line-current feed-forward (`k_ff = 1`), no virtual impedance (`Z_v = 0`). Continuous time,
  linear.
* State order `(i, ξ, v, ζ) ∈ ℝ⁴ = EuclideanSpace ℝ (Fin 4)`: `i` the converter-side filter
  current (OUT of the converter positive, the GFM convention of
  `theorem/GridTiedConverter/GFM/FullModel/Basic.lean`), `ξ = ∫ (i* − i) dt` the current-loop
  integrator, `v` the capacitor voltage, `ζ = ∫ (v* − v) dt` the voltage-loop integrator.
* Plant: `L i̇ = −R i + u`, `C v̇ = i − i_g`, `u` the bridge voltage less the ideal feed-forward
  and decoupling terms. Controller: `i* = K_pv (v* − v) + K_iv ζ + i_g`, `ζ̇ = v* − v`;
  `u = K_pc (i* − i) + K_ic ξ`, `ξ̇ = i* − i` (`InnerCascade.field`). The load (line) current
  `i_g` is a disturbance with ideal feed-forward; the loop is studied at `i_g = 0` (zero-input
  behaviour about the equilibrium of every constant reference, `isEquilibrium`), the line
  dynamics excluded.
* Input the voltage reference `v*` (one port), output the capacitor voltage `v`.
* Parameters: `(L, R, C, K_pc, K_ic, K_pv, K_iv)` of any signs; the engineering range is
  `L, C > 0`, `R ≥ 0`.
* Excluded: the other axis and the decoupling errors, the sampling and computation delay
  (`theorem/GridTiedConverter/GFM/DigitalCascade.lean`), the modulation limit
  (`theorem/GridTiedConverter/GFM/LimitedCascade.lean`), the synchronization loop, the
  reactive-power loop, the line, DC-link dynamics, PWM.

Source: work-sync `theory/T-gfm-control.md` §1.9 (the inner-loop taxonomy: the cascaded voltage
and current loops of a grid-forming converter), `theory/T-droop-control.md`; S. D'Arco,
J. A. Suul and O. B. Fosso, Electr. Power Syst. Res. 122 (2015) 180–197 (the cascade of
`theorem/GridTiedConverter/GFM/FullModel/Basic.lean`, its current loop
`FullModel.Params.currentMatrix` and its exact current-loop criterion
`FullModel.Params.spectrallyStable_currentMatrix_iff` in
`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayer.lean`); the quartic Routh–Hurwitz criterion
`Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic`
(`theorem/Criteria/Routh4.lean`); the mirrored GFL current loop
`theorem/GridTiedConverter/CurrentControl/PILoop.lean`.

Results.
* `model_field` (the plant is the field), `isEquilibrium` (the equilibrium `(0, 0, v*, 0)` of a
  constant reference), `equilibrium_voltage` (every equilibrium has `v = v*`).
* `det_characteristicMatrix` (`L, C ≠ 0`): `det (sI − A) = s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` with
  `a₃ = (R + K_pc)/L`, `a₂ = (C K_ic + K_pc K_pv)/(C L)`, `a₁ = (K_ic K_pv + K_iv K_pc)/(C L)`,
  `a₀ = K_ic K_iv/(C L)`, i.e. `C s² (L s² + (R + K_pc) s + K_ic) + (K_pv s + K_iv)(K_pc s + K_ic)`
  over `C L`: the current loop closed around the capacitor and the voltage PI.
* `exists_root_of_unstable`: a strict violation of the quartic Routh conditions
  `0 < a₃, 0 < a₁, 0 < a₀, a₁² + a₃² a₀ < a₃ a₂ a₁` gives a characteristic root in the open right
  half plane.
* `currentBlock`, `currentBlock_eq`: the `(i, ξ)` block of the state matrix is the real part of
  the full model's current loop `FullModel.Params.currentMatrix` (`ofParams`).

Family and connection conclusions.
* `family : Family InnerCascade Spectral.Requirement 4 1` (`Spectral.linearFamily` of the plants,
  `Stable` the quartic Routh conditions, `Unstable` their strict violation): `exact` (the
  attractive sentences and sampled contraction are translated exactly), `chain_le_semantics`.
  `mem_den_iff_stable`: for every parameter value an attractive sentence holds iff the quartic
  Routh conditions hold (for `L = 0` or `C = 0` a row of the state matrix vanishes and neither
  holds).
  `mem_den_iff`: with `L, C > 0` an attractive sentence holds iff `R + K_pc > 0`,
  `K_ic K_pv + K_iv K_pc > 0`, `K_ic K_iv > 0` and
  `C L (K_ic K_pv + K_iv K_pc)² + C² (R + K_pc)² K_ic K_iv <
  C (R + K_pc)(C K_ic + K_pc K_pv)(K_ic K_pv + K_iv K_pc)`.
* IMC tuning of the current loop `K_pc = L ω_c`, `K_ic = R ω_c` (`imcTuned`): the characteristic
  polynomial factors as `(L s + R)(C s³ + C ω_c s² + ω_c K_pv s + ω_c K_iv)`, and
  `imcTuned_mem_den_iff`: with `L, R, C > 0` an attractive sentence holds iff `0 < ω_c`,
  `0 < K_iv` and `K_iv < ω_c K_pv` (the Routh determinant is
  `C ω_c (ω_c K_pv − K_iv)(C L R² ω_c + C R³ + K_iv L³ ω_c + K_pv L² R ω_c)`).
  `imcTuned_mem_den_iff_currentLoop`: for the cascade of a full-model parameter set with the IMC
  current gains, the same as the exact current-loop criterion of the full model
  (`FullModel.Params.spectrallyStable_currentMatrix_iff`) together with `0 < K_iv < ω_c K_pv`.
-/

noncomputable section
namespace powerlib.GFM
open Matrix Linear LinearSystems TMIO

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- One axis of the grid-forming inner cascade: the LC filter `(L, R, C)` and the gains of the
current loop `(K_pc, K_ic)` and of the voltage loop `(K_pv, K_iv)`. -/
@[ext] structure InnerCascade where
  /-- Converter-side filter inductance `L_f`. -/
  L : ℝ
  /-- Converter-side filter resistance `R_f`. -/
  R : ℝ
  /-- Filter capacitance `C_f`. -/
  C : ℝ
  /-- Current-loop proportional gain `K_pc`. -/
  Kpc : ℝ
  /-- Current-loop integral gain `K_ic`. -/
  Kic : ℝ
  /-- Voltage-loop proportional gain `K_pv`. -/
  Kpv : ℝ
  /-- Voltage-loop integral gain `K_iv`. -/
  Kiv : ℝ

namespace InnerCascade

variable (c : InnerCascade)

/-- The current reference of the voltage PI loop, `i* = K_pv (v* − v) + K_iv ζ` (the line-current
feed-forward at `i_g = 0`). -/
def currentRef (vref : ℝ) (x : ℝ⁴) : ℝ := c.Kpv * (vref - x 2) + c.Kiv * x 3

/-- The output of the current PI loop, `u = K_pc (i* − i) + K_ic ξ`. -/
def control (vref : ℝ) (x : ℝ⁴) : ℝ := c.Kpc * (c.currentRef vref x - x 0) + c.Kic * x 1

/-- The cascade field `(i̇, ξ̇, v̇, ζ̇)`: `L i̇ = −R i + u`, `ξ̇ = i* − i`, `C v̇ = i`,
`ζ̇ = v* − v`. -/
def field (vref : ℝ) (x : ℝ⁴) : ℝ⁴ :=
  WithLp.toLp 2 ![(-c.R * x 0 + c.control vref x) / c.L, c.currentRef vref x - x 0, x 0 / c.C,
    vref - x 2]

/-- The cascade as a linear plant: input `v*`, output `v`. -/
def model : Plant 4 1 :=
  ⟨!![-(c.R + c.Kpc) / c.L, c.Kic / c.L, -(c.Kpc * c.Kpv) / c.L, c.Kpc * c.Kiv / c.L;
      -1, 0, -c.Kpv, c.Kiv; 1 / c.C, 0, 0, 0; 0, 0, -1, 0],
    !![c.Kpc * c.Kpv / c.L; c.Kpv; 0; 1], !![0, 0, 1, 0], !![0]⟩

/-- The plant is exactly the cascade field. -/
@[tmio M, powerlib_domain] theorem model_field (vref : ℝ) (x : ℝ⁴) :
    c.model.inputField (fun _ => vref) x = c.field vref x := by
  ext j
  fin_cases j <;>
    simp [Plant.inputField, model, field, control, currentRef, op, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;> ring

/-- The equilibrium for a constant reference: `i = 0`, `ξ = 0`, `v = v*`, `ζ = 0`. -/
def equilibrium (vref : ℝ) : ℝ⁴ := WithLp.toLp 2 ![0, 0, vref, 0]

@[tmio M, powerlib_domain] theorem isEquilibrium (vref : ℝ) :
    IsEquilibrium (c.model.inputField fun _ => vref) (equilibrium vref) := by
  rw [IsEquilibrium, model_field]
  ext j
  fin_cases j <;> simp [field, control, currentRef, equilibrium]

/-- Every equilibrium of the cascade has zero voltage error `v = v*`. Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_voltage {vref : ℝ} {e : ℝ⁴}
    (he : IsEquilibrium (c.model.inputField fun _ => vref) e) : e 2 = vref := by
  rw [IsEquilibrium, model_field] at he
  have h := congrArg (fun z : ℝ⁴ => z 3) he
  simp [field] at h
  linarith

/-! ### The characteristic polynomial -/

/-- `a₃ = C (R + K_pc)/(C L)`, that is `(R + K_pc)/L` for `C ≠ 0`. -/
def a3 : ℝ := c.C * (c.R + c.Kpc) / (c.C * c.L)

/-- `a₂ = (C K_ic + K_pc K_pv)/(C L)`. -/
def a2 : ℝ := (c.C * c.Kic + c.Kpc * c.Kpv) / (c.C * c.L)

/-- `a₁ = (K_ic K_pv + K_iv K_pc)/(C L)`. -/
def a1 : ℝ := (c.Kic * c.Kpv + c.Kiv * c.Kpc) / (c.C * c.L)

/-- `a₀ = K_ic K_iv/(C L)`. -/
def a0 : ℝ := c.Kic * c.Kiv / (c.C * c.L)

/-- The characteristic polynomial of the cascade:
`det (sI − A) = s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix (hL : c.L ≠ 0) (hC : c.C ≠ 0)
    (s : ℂ) :
    (characteristicMatrix c.model.A s).det =
      s ^ 4 + (c.a3 : ℂ) * s ^ 3 + (c.a2 : ℂ) * s ^ 2 + (c.a1 : ℂ) * s + (c.a0 : ℂ) := by
  have hL' : (c.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hC' : (c.C : ℂ) ≠ 0 := by exact_mod_cast hC
  simp only [characteristicMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  simp [model, complexify, Fin.succAbove, Fin.lt_def, a3, a2, a1, a0]
  field_simp
  ring

/-- With `L = 0` or `C = 0` a row of the state matrix vanishes and `0` is a characteristic
root. -/
@[tmio M, powerlib_domain] private theorem det_characteristicMatrix_zero_of_degenerate
    (h : c.L = 0 ∨ c.C = 0) : (characteristicMatrix c.model.A 0).det = 0 := by
  rcases h with h | h
  · refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    fin_cases j <;> simp [characteristicMatrix, model, complexify, h]
  · refine Matrix.det_eq_zero_of_row_eq_zero 2 fun j => ?_
    fin_cases j <;> simp [characteristicMatrix, model, complexify, h]

/-- The stability condition: the quartic Routh conditions of the monic characteristic
polynomial. -/
def Stable (c : InnerCascade) : Prop :=
  0 < c.a3 ∧ 0 < c.a1 ∧ 0 < c.a0 ∧ c.a1 ^ 2 + c.a3 ^ 2 * c.a0 < c.a3 * c.a2 * c.a1

/-- The instability condition: a strict violation of the quartic Routh conditions. -/
def Unstable (c : InnerCascade) : Prop :=
  c.a3 < 0 ∨ c.a2 < 0 ∨ c.a1 < 0 ∨ c.a0 < 0 ∨ c.a3 * c.a2 * c.a1 < c.a1 ^ 2 + c.a3 ^ 2 * c.a0

/-- Routh–Hurwitz for the cascade, for every parameter value: the state matrix is Hurwitz iff
the quartic Routh conditions hold. -/
@[tmio M, powerlib_domain] private theorem isHurwitz_iff : IsHurwitz c.model.A ↔ c.Stable := by
  by_cases hd : c.L = 0 ∨ c.C = 0
  · have h0 := det_characteristicMatrix_zero_of_degenerate c hd
    have hS : ¬ c.Stable := by
      rintro ⟨-, -, h0', -⟩
      rcases hd with hd | hd <;> simp [a0, hd] at h0'
    refine ⟨fun hH => absurd (((spectrallyStable_iff_isHurwitz _).mpr hH) 0 h0) (by simp),
      fun h => absurd h hS⟩
  · push Not at hd
    exact Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
      (det_characteristicMatrix c hd.1 hd.2)

/-- A strict violation of the quartic Routh conditions gives a characteristic root in the open
right half plane. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_root_of_unstable (h : c.Unstable) :
    ∃ s : ℂ, (characteristicMatrix c.model.A s).det = 0 ∧ 0 < s.re := by
  have hd : c.L ≠ 0 ∧ c.C ≠ 0 := by
    by_contra hn
    rw [not_and_or, not_not, not_not] at hn
    rcases hn with hn | hn <;> simp [Unstable, a3, a2, a1, a0, hn] at h
  obtain ⟨s, hs, hre⟩ := Criteria.exists_quartic_root_re_pos_of_violation h
  exact ⟨s, by rw [det_characteristicMatrix c hd.1 hd.2]; exact hs, hre⟩

/-! ### The design family -/

/-- The cascades, each read as the port system of its plant (input `v*`, output `v`). -/
def family : Family InnerCascade Spectral.Requirement 4 1 :=
  Spectral.linearFamily model Stable Unstable

@[tmio M, powerlib_domain] theorem family_isLinear : family.IsLinear model :=
  Spectral.linearFamily_isLinear _ _ _

/-- The attractive sentences and sampled contraction of the cascade are translated exactly: the
stability condition is the Hurwitz property for every parameter value. -/
@[tmio TM, powerlib_domain] theorem exact {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) :=
  Spectral.linear_exact (fun c => c.isHurwitz_iff.symm) hP

/-- Every translation of the cascade family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) :=
  Spectral.linear_chain_le_semantics (fun c h => c.isHurwitz_iff.mpr h)
    (fun c h => c.exists_root_of_unstable h)

/-- **The cascade, exactly, for every parameter value**: an attractive sentence (or sampled
contraction) holds iff the quartic Routh conditions `Stable` hold (for `L = 0` or `C = 0` a row of
the state matrix vanishes and neither holds). -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_stable (c : InnerCascade) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (c ∈ family.den (.flow P) ↔ c ∈ {c : InnerCascade | c.Stable}) := by
  unfold TMIO.Statement
  rw [(connection_proof% (family_isLinear.mem_den_hurwitz hP))]
  exact c.isHurwitz_iff

/-- **The cascade, exactly**: with `L, C > 0` an attractive sentence (or sampled contraction)
holds iff `R + K_pc > 0`, `K_ic K_pv + K_iv K_pc > 0`, `K_ic K_iv > 0` and
`C L (K_ic K_pv + K_iv K_pc)² + C² (R + K_pc)² K_ic K_iv <
C (R + K_pc)(C K_ic + K_pc K_pv)(K_ic K_pv + K_iv K_pc)`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff (c : InnerCascade) (hL : 0 < c.L)
    (hC : 0 < c.C) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (c ∈ family.den (.flow P) ↔ c ∈ {c : InnerCascade | 0 < c.R + c.Kpc ∧
      0 < c.Kic * c.Kpv + c.Kiv * c.Kpc ∧ 0 < c.Kic * c.Kiv ∧
      c.C * c.L * (c.Kic * c.Kpv + c.Kiv * c.Kpc) ^ 2 +
          c.C ^ 2 * (c.R + c.Kpc) ^ 2 * (c.Kic * c.Kiv) <
        c.C * (c.R + c.Kpc) * (c.C * c.Kic + c.Kpc * c.Kpv) *
          (c.Kic * c.Kpv + c.Kiv * c.Kpc)}) := by
  unfold TMIO.Statement
  rw [(connection_proof% (mem_den_iff_stable c hP))]
  have hCL : 0 < c.C * c.L := mul_pos hC hL
  unfold Stable a3 a2 a1 a0
  simp only [Set.mem_ofPred_eq]
  rw [div_pos_iff_of_pos_right hCL, div_pos_iff_of_pos_right hCL, div_pos_iff_of_pos_right hCL,
    mul_pos_iff_of_pos_left hC]
  have key : ((c.Kic * c.Kpv + c.Kiv * c.Kpc) / (c.C * c.L)) ^ 2 +
      (c.C * (c.R + c.Kpc) / (c.C * c.L)) ^ 2 * (c.Kic * c.Kiv / (c.C * c.L)) <
      c.C * (c.R + c.Kpc) / (c.C * c.L) * ((c.C * c.Kic + c.Kpc * c.Kpv) / (c.C * c.L)) *
        ((c.Kic * c.Kpv + c.Kiv * c.Kpc) / (c.C * c.L)) ↔
      c.C * c.L * (c.Kic * c.Kpv + c.Kiv * c.Kpc) ^ 2 +
          c.C ^ 2 * (c.R + c.Kpc) ^ 2 * (c.Kic * c.Kiv) <
        c.C * (c.R + c.Kpc) * (c.C * c.Kic + c.Kpc * c.Kpv) *
          (c.Kic * c.Kpv + c.Kiv * c.Kpc) := by
    rw [← sub_pos, ← sub_pos (a := c.C * (c.R + c.Kpc) * (c.C * c.Kic + c.Kpc * c.Kpv) *
      (c.Kic * c.Kpv + c.Kiv * c.Kpc))]
    have e : c.C * (c.R + c.Kpc) / (c.C * c.L) * ((c.C * c.Kic + c.Kpc * c.Kpv) / (c.C * c.L)) *
        ((c.Kic * c.Kpv + c.Kiv * c.Kpc) / (c.C * c.L)) -
        (((c.Kic * c.Kpv + c.Kiv * c.Kpc) / (c.C * c.L)) ^ 2 +
          (c.C * (c.R + c.Kpc) / (c.C * c.L)) ^ 2 * (c.Kic * c.Kiv / (c.C * c.L))) =
        (c.C * (c.R + c.Kpc) * (c.C * c.Kic + c.Kpc * c.Kpv) * (c.Kic * c.Kpv + c.Kiv * c.Kpc) -
          (c.C * c.L * (c.Kic * c.Kpv + c.Kiv * c.Kpc) ^ 2 +
            c.C ^ 2 * (c.R + c.Kpc) ^ 2 * (c.Kic * c.Kiv))) / (c.C ^ 3 * c.L ^ 3) := by
      field_simp
    rw [e, div_pos_iff_of_pos_right (by positivity)]
  rw [key]

/-! ### IMC tuning of the current loop -/

/-- The cascade with the IMC current gains `K_pc = L ω_c`, `K_ic = R ω_c` and the voltage gains
`(K_pv, K_iv)`. -/
def imcTuned (L R C ωc Kpv Kiv : ℝ) : InnerCascade := ⟨L, R, C, L * ωc, R * ωc, Kpv, Kiv⟩

/-- **The IMC-tuned cascade**: with `L, R, C > 0` an attractive sentence holds iff `0 < ω_c`,
`0 < K_iv` and `K_iv < ω_c K_pv`. The Routh determinant is
`C ω_c (ω_c K_pv − K_iv)(C L R² ω_c + C R³ + K_iv L³ ω_c + K_pv L² R ω_c)`. -/
@[tmio TM, powerlib_domain] theorem imcTuned_mem_den_iff {L R C ωc Kpv Kiv : ℝ} (hL : 0 < L)
    (hR : 0 < R) (hC : 0 < C) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (imcTuned L R C ωc Kpv Kiv ∈ family.den (.flow P) ↔
      imcTuned L R C ωc Kpv Kiv ∈ {_c : InnerCascade | 0 < ωc ∧ 0 < Kiv ∧ Kiv < ωc * Kpv}) := by
  have h := mem_den_iff (imcTuned L R C ωc Kpv Kiv) hL hC hP
  unfold TMIO.Statement at h ⊢
  rw [h]
  simp only [Set.mem_ofPred_eq, imcTuned]
  have key : C * (R + L * ωc) * (C * (R * ωc) + L * ωc * Kpv) * (R * ωc * Kpv + Kiv * (L * ωc)) -
      (C * L * (R * ωc * Kpv + Kiv * (L * ωc)) ^ 2 + C ^ 2 * (R + L * ωc) ^ 2 * (R * ωc * Kiv)) =
      C * ωc * (ωc * Kpv - Kiv) *
        (C * L * R ^ 2 * ωc + C * R ^ 3 + Kiv * L ^ 3 * ωc + Kpv * L ^ 2 * R * ωc) := by ring
  have hFe : C * L * R ^ 2 * ωc + C * R ^ 3 + Kiv * L ^ 3 * ωc + Kpv * L ^ 2 * R * ωc =
      C * R ^ 2 * (R + L * ωc) + L ^ 2 * (R * ωc * Kpv + Kiv * (L * ωc)) := by ring
  constructor
  · rintro ⟨h3, h1, h0, hg⟩
    have hg' := sub_pos.mpr hg
    rw [key] at hg'
    have hF : 0 < C * L * R ^ 2 * ωc + C * R ^ 3 + Kiv * L ^ 3 * ωc + Kpv * L ^ 2 * R * ωc := by
      rw [hFe]; positivity
    have hgap : 0 < ωc * (ωc * Kpv - Kiv) := by
      have h' : 0 < C * (ωc * (ωc * Kpv - Kiv)) := by
        have := pos_of_mul_pos_left hg' hF.le
        linarith [show C * ωc * (ωc * Kpv - Kiv) = C * (ωc * (ωc * Kpv - Kiv)) by ring]
      exact pos_of_mul_pos_right h' hC.le
    have hωKiv : 0 < ωc * Kiv := by
      have : R * ωc * Kiv = R * (ωc * Kiv) := by ring
      rw [this] at h0
      exact pos_of_mul_pos_right h0 hR.le
    have hω : 0 < ωc := by
      by_contra hn
      push Not at hn
      have hn' : ωc < 0 := lt_of_le_of_ne hn (fun h => by rw [h] at hωKiv; simp at hωKiv)
      have hKiv : Kiv < 0 := by nlinarith
      have hlt : ωc * Kpv < Kiv := by nlinarith
      -- `−ω_c (R K_pv + L K_iv) > −K_iv (R + L ω_c) > 0`, against `h1`
      have : 0 < -ωc * (R * Kpv + L * Kiv) := by
        have e1 : -ωc * (R * Kpv + L * Kiv) = R * (-(ωc * Kpv)) + L * (-ωc) * Kiv := by ring
        have e2 : -Kiv * (R + L * ωc) = R * (-Kiv) + L * (-ωc) * Kiv := by ring
        have : 0 < -Kiv * (R + L * ωc) := mul_pos (by linarith) h3
        nlinarith
      nlinarith
    have hKiv : 0 < Kiv := pos_of_mul_pos_right hωKiv hω.le
    refine ⟨hω, hKiv, ?_⟩
    have := pos_of_mul_pos_right hgap hω.le
    linarith
  · rintro ⟨hω, hKiv, hg⟩
    have hKpv : 0 < Kpv := by nlinarith
    refine ⟨by positivity, by positivity, by positivity, ?_⟩
    rw [← sub_pos, key]
    have : 0 < ωc * Kpv - Kiv := by linarith
    positivity

/-! ### The current loop of the full model -/

/-- The cascade of a full-model parameter set: its filter and the gains of its two PI loops
(`theorem/GridTiedConverter/GFM/FullModel/Basic.lean`). -/
def ofParams (p : FullModel.Params) : InnerCascade := ⟨p.Lf, p.Rf, p.Cf, p.Kpc, p.Kic, p.Kpv, p.Kiv⟩

/-- The `(i, ξ)` block of the cascade state matrix, the current loop at rest of the voltage
level. -/
def currentBlock (c : InnerCascade) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c.model.A 0 0, c.model.A 0 1; c.model.A 1 0, c.model.A 1 1]

/-- The current loop of the cascade is the full model's current loop
`FullModel.Params.currentMatrix` (real entries). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem currentBlock_eq (p : FullModel.Params) :
    (ofParams p).currentBlock.map (fun r : ℝ => (r : ℂ)) = p.currentMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [currentBlock, ofParams, model, FullModel.Params.currentMatrix]
  ring

/-- **The IMC-tuned cascade of a full-model parameter set is stable exactly when the full
model's current loop is stable and `0 < K_iv < ω_c K_pv`**: with `L_f, R_f, C_f > 0` and the IMC
current gains `K_pc = L_f ω_c`, `K_ic = R_f ω_c`, the current loop condition of
`FullModel.Params.spectrallyStable_currentMatrix_iff` is `ω_c > 0`, and `imcTuned_mem_den_iff`
decides the cascade. -/
@[tmio TM, powerlib_domain] theorem imcTuned_mem_den_iff_currentLoop (p : FullModel.Params)
    {ωc : ℝ} (hL : 0 < p.Lf) (hR : 0 < p.Rf) (hC : 0 < p.Cf) (hpc : p.Kpc = p.Lf * ωc)
    (hic : p.Kic = p.Rf * ωc) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (ofParams p ∈ family.den (.flow P) ↔ ofParams p ∈
      {_c : InnerCascade | SingularPerturbation.realify p.currentMatrix ∈
        {A | Linear.SpectrallyStable A} ∧ 0 < p.Kiv ∧ p.Kiv < ωc * p.Kpv}) := by
  have h := imcTuned_mem_den_iff (L := p.Lf) (R := p.Rf) (C := p.Cf) (ωc := ωc) (Kpv := p.Kpv)
    (Kiv := p.Kiv) hL hR hC hP
  have he : ofParams p = imcTuned p.Lf p.Rf p.Cf ωc p.Kpv p.Kiv := by
    simp [ofParams, imcTuned, hpc, hic]
  unfold TMIO.Statement at h ⊢
  rw [he, h]
  simp only [Set.mem_ofPred_eq]
  rw [p.spectrallyStable_currentMatrix_iff, hpc, hic]
  constructor
  · rintro ⟨hω, hKiv, hg⟩
    exact ⟨⟨div_pos (by positivity) hL, div_pos (by positivity) hL⟩, hKiv, hg⟩
  · rintro ⟨⟨-, h0⟩, hKiv, hg⟩
    exact ⟨pos_of_mul_pos_right ((div_pos_iff_of_pos_right hL).mp h0) hR.le, hKiv, hg⟩

end InnerCascade
