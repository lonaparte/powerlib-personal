import theorem.PowerSystem.Synchronous.FluxDecayParametric

/-! # The flux-decay machine at 2:1, converse limit: weak demagnetization, fixed flux torque

`theorem/PowerSystem/Synchronous/FluxDecayParametric.lean` treats the linearized one-axis
(flux-decay) machine of Heffron–Phillips, `Δδ̇ = ω₀Δω`, `2HΔω̇ = −K₁Δδ − K₂ΔE'_q − DΔω`,
`T'_{d0}K₃ΔĖ'_q = −ΔE'_q − K₃K₄Δδ`, with the synchronizing coefficient pumped,
`K₁(t) = K₁(1 + η cos 2νt)`, in two distinguished limits (`Weak`: `K₂ = εK̂₂`, `K₄ = εK̂₄`;
`Driven`: `K₄` fixed, `K₂ = εK̂₂`). This file treats the converse limit `Converse`: the flux torque
`K₂` fixed and the demagnetizing coefficient small, `K₄ = εK̂₄`, with damping `D = εD̂`, detuning
`K₁ = (2H/ω₀)ν²(1 − 2εd̂)` and depth `εη̂`. The state matrix is exactly
`A₀c + ε(A₀' + Re{A₁ e^{j2νt}})` (`machine_stateMatrix`), and the field mode is a three-state block
core with the real stable mode `λ₃ = −1/τ`, `τ = K₃T'_{d0}`, decided on the first-order boundary
by the closed form `BlockCoreClosedForm.blockMixed` through `BlockCoreClosedForm.mixedDet_effSecond`
and `PhysicalBoundary.physical_boundary` (the physical-coordinate form of
`BlockCoreClosedForm.block_boundary`).

* Modal coordinates (`modal`). At `ε = 0` the field drives the torque (`K₂`) but the swing does
  not reach the field: the swing eigenvector is `r = (1, jν/ω₀, 0)`, the field's left eigenvector
  is `e₃ᵀ`, while the pair's left eigenvector `u` has the field component
  `jω₀K₂τ/(4Hν(1 + jντ))` and the field mode's right eigenvector `v` the swing components
  `(−ω₀K₂τ²/(2Hm), K₂τ/(2Hm))`, `m = 1 + ν²τ²`.
* First order (`shift_eq`, `pump_eq`, `firstOrder_stable`, `firstOrder_unstable`). The shift of the
  pair is `λ₁ = −s' − jd'` with `s' = D̂/(4H) + ω₀K₂K₃K̂₄τ/(4Hm)`, `d' = d̂ν + ω₀K₂K₃K̂₄/(4Hνm)`:
  the damping and synchronizing torque of the flux decay at the oscillation frequency, the same
  as in `Driven` with `K₄K̂₂` replaced by `K₂K̂₄`; the pump is `g = jη̂ν/2`; the threshold is
  `(η̂ν)²/16 ≶ s'² + d'²`.
* Modal core (`modalB_eq`, `modalA_eq`). The pump reaches the pair also through the field mode:
  `Q A₁ P` has, besides the critical block `[[0, 0], [η̂ν, 0]]`, the modulated coupling
  `A₁₂ = (0, η̂ν v₀)ᵀ` from the field into the pair through the angle component
  `v₀ = −ω₀K₂τ²/(2Hm)` of the field mode, and no modulated coupling out of the pair (`A₂₁ = 0`);
  the constant part has the couplings `β` (the torque perturbation on the swing components of the
  field mode) and `γ = (−K̂₄/T'_{d0}, 0)`.
* Second order (`blockMixed_eq`, `secondOrder_boundary`). In closed form
  `blockMixed = d'(s'² + d'² − 3(η̂ν)²/32)/ν + ω₀K₂K₃K̂₄τ²(s'² + d'² − (η̂ν)²/16)/(Hm²)`: the
  resolvent terms of the field mode, the constant coupling `βγ` and the modulated coupling `A₁₂`
  meeting `γ`, add up to a multiple of `s'² + d'² − |g/2|²`. On the boundary
  `s'² + d'² = (η̂ν)²/16`, `s' > 0`, they vanish and the verdict is the sign of `−d'`:
  `d' < 0` puts every Floquet multiplier inside the unit circle, `d' > 0` gives Floquet
  instability, for all small `ε > 0`.

Model boundary.
* One synchronous machine, the linearized one-axis model at an operating point in the state
  `(Δδ, Δω, ΔE'_q)` (rotor angle, per-unit speed, transient q-axis voltage), continuous time,
  constant field voltage: no AVR, exciter or PSS (`K₅`, `K₆` absent), no damper windings, no
  network or multi-machine dynamics, no saturation; `K₁ … K₄`, `H`, `D`, `T'_{d0}`, `ω₀` constant
  except the prescribed external modulation of `K₁` (`FluxDecayParametric.Params`,
  `Params.stateMatrix`, `Params.pumped`).
* The family `Converse` at the pump frequency `2ν`: `K₂`, `K₃`, `T'_{d0}` fixed, `K₄ = εK̂₄`,
  `D = εD̂`, detuning `εd̂` and depth `εη̂` of order `ε`; `H > 0`, `ν > 0`, `ω₀ ≠ 0`,
  `K₃T'_{d0} > 0`. Floquet statements for the periodic state matrix
  `(machine ε t).stateMatrix`, period `2π/(2ν)`, for all sufficiently small `ε > 0`; linearization
  about the equilibrium of the unpumped machine (the variational equation is exact for the
  linear model).
* Not covered: `d' = 0` on the boundary (next order); the location of the critical multipliers
  themselves (only the verdict inside/outside the unit circle is stated).
* The machine is a data model (as `ParametricSwing`'s `Params`), not a model family: no connection
  between families or representations is stated, so no scaffold is involved.

Source: W. G. Heffron, R. A. Phillips, "Effect of a modern amplidyne voltage regulator on
underexcited operation of large turbine generators", AIEE Trans. PAS-71 (1952); F. P. deMello,
C. Concordia, "Concepts of synchronous machine stability as affected by excitation control", IEEE
Trans. PAS-88 (1969) (the coefficients `K₁ … K₄`, the flux-decay block `K₃/(1 + sK₃T'_{d0})`);
P. Kundur, *Power System Stability and Control* (1994) §12.3; the open item of
`theorem/PowerSystem/Synchronous/FluxDecayParametric.lean` (Model boundary: "Not covered: the
converse limit `K₂` fixed, `K₄ = εK̂₄`"); `BlockCoreClosedForm.blockMixed`,
`BlockCoreClosedForm.mixedDet_effSecond`, `BlockCoreClosedForm.sylv_fin_one`,
`PhysicalBoundary.physical_boundary`, `BlockAveraging.modal_three`, `BlockAveraging.three_stable`,
`BlockAveraging.three_unstable`.

Results.
* `Converse`, `Converse.params`, `Converse.machine`, `Converse.machine_eq_pumped`,
  `Converse.tau`, `Converse.mden`, `Converse.critMatrix`, `Converse.shiftMatrix`,
  `Converse.pumpMatrix`, `Converse.machine_stateMatrix` — the converse family and its form
  `A₀c + ε(A₀' + Re{A₁ e^{j2νt}})`.
* `Converse.rightVec`, `Converse.leftVec`, `Converse.fieldRight`, `Converse.fieldPole`,
  `Converse.sD`, `Converse.dD`, `Converse.modal`, `Converse.shift_eq`, `Converse.pump_eq` —
  modal coordinates, `λ₁ = −s' − jd'`, `g = jη̂ν/2`.
* `Converse.firstOrder_stable`, `Converse.firstOrder_unstable` — the first-order threshold.
* `Converse.coupK`, `Converse.fieldAngle`, `Converse.modalB_eq`, `Converse.modalA_eq` — the
  modal core: the modulated coupling `A₁₂` through the field mode.
* `Converse.blockMixed_eq`, `Converse.secondOrder_boundary` — the decisive quantity in closed
  form and the boundary decided at second order.

Corrections and sharpenings.
* The pump does not reach the pair through the field's left eigenvector (it is `e₃ᵀ`: the field
  equation sees the swing only at order `ε`), but through the field mode's right eigenvector: its
  angle component `v₀ = −ω₀K₂τ²/(2Hm)` turns the pumped `K₁` into the modulated coupling
  `A₁₂ = (0, η̂ν v₀)ᵀ` (`modalA_eq`).
* The cancellation of the field mode's resolvent terms on the boundary found for `Driven` holds
  in the converse limit as well, although here `A₀'` acts through two equations (torque and
  field) and the pump enters a coupling block: in both limits in which one field coupling is of
  order one, the field mode moves the second-order boundary only through its first-order torque in
  `s'`, `d'`, and the verdict is the sign of `−d'`; only in `Weak` (both couplings small) do the
  resolvent terms survive.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers) of the selected machine
model.
-/

noncomputable section
namespace powerlib.Synchronous.FluxDecayConverse

open Complex Matrix Filter Topology
open scoped Matrix.Norms.Operator
open powerlib.ParametricResonance
open powerlib.ParametricResonance.BlockAveraging (physJ physLeft physRight modX expS modalP modalQ
  FzcB shiftRe shiftIm)
open powerlib.ParametricResonance.BlockCoreClosedForm
open powerlib.Synchronous.FluxDecayParametric (Params)

/-! ## Elementary complex identities -/

@[tmio T, powerlib_foundation] private theorem norm_sq_neg_sub' (a b : ℝ) :
    ‖-(a : ℂ) - (b : ℂ) * I‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

@[tmio T, powerlib_foundation] private theorem norm_sq_mul_I_half' (c : ℝ) :
    ‖(c : ℂ) * I / 2‖ ^ 2 = c ^ 2 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

@[tmio T, powerlib_foundation] private theorem norm_sq_mul_I_quarter' (c : ℝ) :
    ‖(c : ℂ) * I / 2 / 2‖ ^ 2 = c ^ 2 / 16 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

@[tmio T, powerlib_foundation] private theorem re_neg_sub' (a b : ℝ) :
    (-(a : ℂ) - (b : ℂ) * I).re = -a := by simp

/-! ## The decisive quantity of a core pumped through the pair with a modulated coupling -/

set_option maxHeartbeats 1000000 in
/-- `blockMixed` of a three-state core with one real stable mode `l`, the pump `[[0, 0], [a, 0]]`
on the pair and the modulated coupling `(0, ac)ᵀ` from the stable mode into the pair (no
modulated coupling out of the pair), and a constant perturbation with the critical block
`[[x, 0], [−2d, y]]`, the couplings `β = (b₀, b₁)ᵀ`, `γ = (g, 0)`: the critical part, the constant
coupling through `(l − jν)⁻¹` and the modulated coupling meeting `γ`. -/
@[tmio T, powerlib_foundation] private theorem blockMixed_core (x y d b₀ b₁ g e a c l ν : ℝ)
    (hν : 0 < ν) :
    blockMixed 0 0 (2 * ν) !![l]
        (fromBlocks !![0, 0; (a : ℂ), 0] !![0; ((a * c : ℝ) : ℂ)] 0 0)
        (fromBlocks !![x, 0; -(2 * d), y] !![b₀; b₁] !![g, 0] !![e]) =
      d * a ^ 2 / (32 * ν) + (-(a ^ 2 * d / 8) + d * ((x - y) ^ 2 / 4 + d ^ 2)) / ν +
        g * (-((x + y) / 2) * (b₀ * l - b₁ * ν) + d * (b₁ * l + b₀ * ν)) / (l ^ 2 + ν ^ 2) +
        g * a ^ 2 * c * l / (8 * (l ^ 2 + ν ^ 2)) := by
  set A : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ :=
    fromBlocks !![0, 0; (a : ℂ), 0] !![0; ((a * c : ℝ) : ℂ)] 0 0 with hA
  set B : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
    fromBlocks !![x, 0; -(2 * d), y] !![b₀; b₁] !![g, 0] !![e] with hB
  have hA21 : A.toBlocks₂₁ = 0 := toBlocks_fromBlocks₂₁ _ _ _ _
  have hlm : lowMinus A = 0 := by simp [lowMinus, hA21]
  have hl3 : lowThree A = 0 := by simp [lowThree, hA21]
  have hup : upPlus A = !![0; a * c / 2] := by
    have hre : A.toBlocks₁₂.map Complex.re = !![0; a * c] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hA]
    have him : A.toBlocks₁₂.map Complex.im = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hA]
    rw [upPlus, hre, him, Matrix.mul_zero, add_zero]
    ext i j; fin_cases i <;> fin_cases j <;> simp; ring
  have hs0 : ∀ μ : ℝ, sylv !![l] μ 0 = 0 := fun μ => by simp [sylv]
  have hD : l ^ 2 + ν ^ 2 ≠ 0 := by
    have : 0 < ν ^ 2 := by positivity
    positivity
  have h2 : 2 * ν / 2 = ν := by ring
  have hP : couplingP !![l] A B (2 * ν) =
      B.toBlocks₁₂ * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν) := by
    rw [couplingP, hlm, hl3, hs0, hs0, h2, sylv_fin_one hD]
    simp
  have hN : couplingN !![l] A B (2 * ν) =
      !![0; a * c / 2] * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν) := by
    rw [couplingN, hlm, hs0, hup, h2, sylv_fin_one hD]
    simp
  have hpc : projC (B.toBlocks₁₂ * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν)) =
      ⟨g * (b₀ * l - b₁ * ν) / (2 * (l ^ 2 + ν ^ 2)), g * (b₁ * l + b₀ * ν) / (2 * (l ^ 2 + ν ^ 2))⟩ := by
    apply Complex.ext <;> simp only [projC] <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] <;>
      simp [hB, ThreeStateCore.lamInv, NormalForm.quarter] <;>
      field_simp <;> ring
  have hac : antiShift (!![0; a * c / 2] * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν)) =
      ⟨g * a * c * ν / (4 * (l ^ 2 + ν ^ 2)), g * a * c * l / (4 * (l ^ 2 + ν ^ 2))⟩ := by
    apply Complex.ext <;> simp only [antiShift] <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] <;>
      simp [hB, ThreeStateCore.lamInv, NormalForm.quarter] <;>
      field_simp <;> ring
  have hpump : Element.pump A.toBlocks₁₁ TwoToOne.left TwoToOne.right = (a : ℂ) * I / 2 := by
    rw [TwoToOne.pump_base]; simp [hA]; ring
  have hanti : ‖SecondOrder.antiPump A.toBlocks₁₁‖ ^ 2 = a ^ 2 / 4 := by
    have h : SecondOrder.antiPump A.toBlocks₁₁ = -((a : ℂ) * I / 2) := by
      rw [SecondOrder.antiPump_eq]; simp [hA]; ring
    rw [h, norm_neg, norm_sq_mul_I_half']
  have hκ : fundSkew A.toBlocks₁₁ = ((a / 2 : ℝ) : ℂ) := by simp [fundSkew, hA]
  have hn : antiShift B.toBlocks₁₁ = ⟨(x - y) / 2, -d⟩ := by
    apply Complex.ext <;> simp [antiShift, hB] <;> ring
  have hsr : shiftRe B = (x + y) / 2 := by simp [shiftRe, hB]
  have hsi : shiftIm B = -d := by simp [shiftIm, hB]; ring
  rw [blockMixed, hP, hN, critMixed, hpc, hac, hpump, hanti, hκ, hn, hsr, hsi]
  simp [Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  field_simp
  ring

/-! ## The converse family -/

/-- The data of the converse family: the field flux acts on the torque at order one (`K₂` fixed),
the rotor angle demagnetizes the field at order `ε` (`K₄ = εK̂₄`); damping `εD̂`, detuning `εd̂`,
pump depth `εη̂`. -/
structure Converse where
  H : ℝ
  ω₀ : ℝ
  ν : ℝ
  K₂ : ℝ
  K₃ : ℝ
  Td0 : ℝ
  Dh : ℝ
  K4h : ℝ
  dh : ℝ
  ηh : ℝ

namespace Converse

variable (f : Converse)

/-- The machine at `ε`: `K₁ = (2H/ω₀) ν² (1 − 2εd̂)`, `K₄ = εK̂₄`, `D = εD̂`, `K₂`, `K₃` fixed. -/
def params (ε : ℝ) : Params :=
  ⟨2 * f.H / f.ω₀ * f.ν ^ 2 * (1 - 2 * ε * f.dh), f.K₂, f.K₃, ε * f.K4h, f.H, ε * f.Dh, f.Td0,
    f.ω₀⟩

/-- The machine of the family at `ε` and time `t`, with
`K₁(t) = (2H/ω₀) ν² (1 − 2εd̂ + εη̂ cos 2νt)`. -/
def machine (ε t : ℝ) : Params :=
  { f.params ε with
    K₁ := 2 * f.H / f.ω₀ * f.ν ^ 2 * (1 - 2 * ε * f.dh + ε * f.ηh * Real.cos (2 * f.ν * t)) }

/-- The family is the pumped machine `K₁(t) = K₁ (1 + η cos 2νt)` with the relative depth
`η = εη̂/(1 − 2εd̂)`. -/
@[tmio M, powerlib_domain] theorem machine_eq_pumped {ε : ℝ} (h : 1 - 2 * ε * f.dh ≠ 0) (t : ℝ) :
    f.machine ε t = (f.params ε).pumped (ε * f.ηh / (1 - 2 * ε * f.dh)) (2 * f.ν) t := by
  simp only [machine, params, Params.pumped]
  congr 1
  field_simp

/-- The field time constant `τ = K₃T'_{d0}`. -/
def tau : ℝ := f.K₃ * f.Td0

/-- `m = 1 + ν²τ² = |1 + jντ|²`. -/
def mden : ℝ := 1 + f.ν ^ 2 * f.tau ^ 2

/-- The critical state matrix: the undamped swing pair `±jν`, driven by the field pole
`−1/(K₃T'_{d0})` through the flux torque `K₂`. -/
def critMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, f.ω₀, 0; -(f.ν ^ 2 / f.ω₀), 0, -(f.K₂ / (2 * f.H)); 0, 0, -1 / (f.K₃ * f.Td0)]

/-- The first-order change: detuning, damping and the demagnetizing effect of the angle. -/
def shiftMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 2 * f.dh * f.ν ^ 2 / f.ω₀, -(f.Dh / (2 * f.H)), 0; -(f.K4h / f.Td0), 0, 0]

/-- The modulation `A₁`, `Re{A₁ e^{j2νt}} = A₁ cos 2νt`. -/
def pumpMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; -((f.ηh * f.ν ^ 2 / f.ω₀ : ℝ) : ℂ), 0, 0; 0, 0, 0]

/-- **The family's state matrix** is `A₀c + ε(A₀' + Re{A₁ e^{j2νt}})`. -/
@[tmio M, powerlib_domain] theorem machine_stateMatrix (hH : f.H ≠ 0) (hω : f.ω₀ ≠ 0)
    (ε t : ℝ) :
    (f.machine ε t).stateMatrix = physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Params.stateMatrix, machine, params, physJ, modX, critMatrix, shiftMatrix,
      pumpMatrix, -Complex.ofReal_mul, -Complex.ofReal_pow, -Complex.ofReal_div] <;>
    field_simp <;> ring

/-! ## Modal coordinates and the first-order threshold -/

/-- The right eigenvector of `jν`: `r = (1, jν/ω₀, 0)`; the swing does not reach the field at
order one. -/
def rightVec : Fin 3 → ℂ := ![1, ((f.ν / f.ω₀ : ℝ) : ℂ) * I, 0]

/-- The left eigenvector `u = (1/2, −jω₀/(2ν), jω₀K₂τ/(4Hν(1 + jντ)))`, `u r = 1`: through `K₂`
the left eigenvector of the pair has a field component. -/
def leftVec : Fin 3 → ℂ :=
  ![1 / 2, -(((f.ω₀ / (2 * f.ν) : ℝ) : ℂ) * I),
    ((f.ω₀ * f.K₂ * f.tau ^ 2 / (4 * f.H * f.mden) : ℝ) : ℂ) +
      ((f.ω₀ * f.K₂ * f.tau / (4 * f.H * f.ν * f.mden) : ℝ) : ℂ) * I]

/-- The right eigenvector of the field pole, `v = (−ω₀K₂τ²/(2Hm), K₂τ/(2Hm), 1)`: the field mode
moves the rotor through `K₂`. -/
def fieldRight : Fin 3 → ℝ :=
  ![-(f.ω₀ * f.K₂ * f.tau ^ 2 / (2 * f.H * f.mden)), f.K₂ * f.tau / (2 * f.H * f.mden), 1]

/-- The field pole `λ₃ = −1/(K₃ T'_{d0})`. -/
def fieldPole : ℝ := -1 / (f.K₃ * f.Td0)

/-- The first-order damping of the swing pair, `s' = D̂/(4H) + ω₀K₂K₃K̂₄τ/(4Hm)`: mechanical
damping plus the damping torque of the flux decay. -/
def sD : ℝ := f.Dh / (4 * f.H) + f.ω₀ * f.K₂ * f.K₃ * f.K4h * f.tau / (4 * f.H * f.mden)

/-- The first-order detuning `d' = d̂ν + ω₀K₂K₃K̂₄/(4Hνm)`: the detuning of `K₁` plus the
(negative) synchronizing torque of the flux decay. -/
def dD : ℝ := f.dh * f.ν + f.ω₀ * f.K₂ * f.K₃ * f.K4h / (4 * f.H * f.ν * f.mden)

@[tmio M, powerlib_domain] private theorem mden_pos : 0 < f.mden := by
  rw [mden]; positivity

@[tmio M, powerlib_domain] private theorem rightVec_parts :
    ((f.rightVec 0).re = 1 ∧ (f.rightVec 0).im = 0) ∧
      ((f.rightVec 1).re = 0 ∧ (f.rightVec 1).im = f.ν / f.ω₀) ∧
      ((f.rightVec 2).re = 0 ∧ (f.rightVec 2).im = 0) := by
  simp [rightVec, -Complex.ofReal_div]

@[tmio M, powerlib_domain] private theorem leftVec_parts :
    ((f.leftVec 0).re = 1 / 2 ∧ (f.leftVec 0).im = 0) ∧
      ((f.leftVec 1).re = 0 ∧ (f.leftVec 1).im = -(f.ω₀ / (2 * f.ν))) ∧
      ((f.leftVec 2).re = f.ω₀ * f.K₂ * f.tau ^ 2 / (4 * f.H * f.mden) ∧
        (f.leftVec 2).im = f.ω₀ * f.K₂ * f.tau / (4 * f.H * f.ν * f.mden)) := by
  simp [leftVec, -Complex.ofReal_div, -Complex.ofReal_mul, -Complex.ofReal_pow]

@[tmio M, powerlib_domain] private theorem eigen (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    f.critMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec = ((f.ν : ℂ) * I) • f.rightVec ∧
      f.leftVec ᵥ* f.critMatrix.map (algebraMap ℝ ℂ) = ((f.ν : ℂ) * I) • f.leftVec ∧
      f.leftVec ⬝ᵥ f.rightVec = 1 ∧ f.critMatrix *ᵥ f.fieldRight = f.fieldPole • f.fieldRight ∧
      FluxDecayParametric.Weak.fieldVec ᵥ* f.critMatrix =
        f.fieldPole • FluxDecayParametric.Weak.fieldVec ∧
      FluxDecayParametric.Weak.fieldVec ⬝ᵥ f.fieldRight = 1 := by
  have hK : f.K₃ ≠ 0 := by rintro h; rw [h, zero_mul] at hτ; exact lt_irrefl _ hτ
  have hT : f.Td0 ≠ 0 := by rintro h; rw [h, mul_zero] at hτ; exact lt_irrefl _ hτ
  have hm := f.mden_pos.ne'
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> apply Complex.ext <;>
      simp [critMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.mul_re,
        Complex.mul_im, r0, r0', r1, r1', r2, r2', -Complex.ofReal_div, -Complex.ofReal_mul,
        -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_inv] <;>
      field_simp
  · funext i; fin_cases i <;> apply Complex.ext <;>
      simp [critMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Complex.mul_re,
        Complex.mul_im, l0, l0', l1, l1', l2, l2', -Complex.ofReal_div, -Complex.ofReal_mul,
        -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_inv] <;>
      simp only [mden, tau] at * <;> field_simp <;> ring
  · apply Complex.ext <;>
      simp [dotProduct, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, r0, r0', r1, r1', r2,
        r2', l0, l0', l1, l1', l2, l2'] <;> field_simp <;> ring
  · funext i; fin_cases i <;>
      simp [critMatrix, fieldRight, fieldPole, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      simp only [mden, tau] at * <;> field_simp <;> ring
  · funext i; fin_cases i <;>
      simp [critMatrix, FluxDecayParametric.Weak.fieldVec, fieldPole, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three]
  · simp [fieldRight, FluxDecayParametric.Weak.fieldVec, dotProduct, Fin.sum_univ_three]

/-- **The modal form of the converse family** (`P = [Re r, −Im r, v]`, `Q = [2 Re u; 2 Im u; e₃ᵀ]`).
-/
@[tmio M, powerlib_domain] theorem modal (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * modalP f.rightVec f.fieldRight = 1 ∧
      modalP f.rightVec f.fieldRight * modalQ f.leftVec FluxDecayParametric.Weak.fieldVec = 1 ∧
      modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.critMatrix *
          modalP f.rightVec f.fieldRight =
        fromBlocks (TwoToOne.base 0 f.ν) 0 0 !![f.fieldPole] ∧
      physLeft (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) = f.leftVec ∧
      physRight (modalP f.rightVec f.fieldRight) = f.rightVec := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν hω hH hτ
  exact BlockAveraging.modal_three hν h1 h2 h3 h4 h5 h6

/-- The first-order eigenvalue shift `λ₁ = −s' − j d'`: the damping and synchronizing torque of
the flux decay enter at first order, through the field component of the left eigenvector. -/
@[tmio M, powerlib_domain] theorem shift_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec) =
      -(f.sD : ℂ) - (f.dD : ℂ) * I := by
  have hK : f.K₃ ≠ 0 := by rintro h; rw [h, zero_mul] at hτ; exact lt_irrefl _ hτ
  have hT : f.Td0 ≠ 0 := by rintro h; rw [h, mul_zero] at hτ; exact lt_irrefl _ hτ
  have hm := f.mden_pos.ne'
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  apply Complex.ext <;>
    simp [shiftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.mul_re,
      Complex.mul_im, r0, r0', r1, r1', l1, l1', l2, l2', sD, dD,
      -Complex.ofReal_div, -Complex.ofReal_mul, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_inv] <;>
    simp only [mden, tau] at * <;> field_simp <;> ring

/-- The pump `g = u A₁ r̄ = j η̂ν/2`. -/
@[tmio M, powerlib_domain] theorem pump_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) = ((f.ηh * f.ν / 2 : ℝ) : ℂ) * I := by
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  apply Complex.ext <;>
    simp [pumpMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.mul_re,
      Complex.mul_im, r0, r0', l1, l1', -Complex.ofReal_div, -Complex.ofReal_mul,
      -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_inv] <;>
    field_simp

@[tmio M, powerlib_domain] private theorem fieldPole_neg (hτ : 0 < f.K₃ * f.Td0) :
    f.fieldPole < 0 := by
  rw [fieldPole, neg_div]
  exact neg_neg_of_pos (one_div_pos.mpr hτ)

/-- **First-order threshold of the converse family, stability.** For `s' > 0` and
`(η̂ν)²/16 < s'² + d'²` every Floquet multiplier lies inside the unit circle for all small
`ε > 0`. -/
@[tmio M, powerlib_domain] theorem firstOrder_stable (hH : 0 < f.H) (hω : f.ω₀ ≠ 0)
    (hν : 0 < f.ν) (hτ : 0 < f.K₃ * f.Td0) (hs : 0 < f.sD)
    (hg : (f.ηh * f.ν) ^ 2 / 16 < f.sD ^ 2 + f.dD ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
      (Periodic.monodromy (fun t => (f.machine ε t).stateMatrix) (2 * Real.pi / (2 * f.ν)) 0).map
          (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν.ne' hω hH.ne' hτ
  have hs' : (f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)).re < 0 := by
    rw [f.shift_eq hν.ne' hω hH.ne' hτ, re_neg_sub']; linarith
  have hg' : ‖f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) / 2‖ ^ 2 <
      ‖f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)‖ ^ 2 := by
    rw [f.shift_eq hν.ne' hω hH.ne' hτ, f.pump_eq hν.ne' hω, norm_sq_neg_sub',
      norm_sq_mul_I_half']
    have : (f.ηh * f.ν / 2) ^ 2 / 4 = (f.ηh * f.ν) ^ 2 / 16 := by ring
    linarith
  have h := BlockAveraging.three_stable hν (f.fieldPole_neg hτ) h1 h2 h3 h4 h5 h6 f.shiftMatrix
    f.pumpMatrix hs' hg'
  filter_upwards [h] with ε hε
  rw [show (fun t => (f.machine ε t).stateMatrix) =
      physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
    funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
  exact hε

/-- **First-order threshold of the converse family, parametric instability**:
`s'² + d'² < (η̂ν)²/16` gives Floquet instability for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem firstOrder_unstable (hH : 0 < f.H) (hω : f.ω₀ ≠ 0)
    (hν : 0 < f.ν) (hτ : 0 < f.K₃ * f.Td0) (hg : f.sD ^ 2 + f.dD ^ 2 < (f.ηh * f.ν) ^ 2 / 16) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fun t => (f.machine ε t).stateMatrix)
      (2 * Real.pi / (2 * f.ν)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν.ne' hω hH.ne' hτ
  have hg' : ‖f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)‖ ^ 2 <
      ‖f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) / 2‖ ^ 2 := by
    rw [f.shift_eq hν.ne' hω hH.ne' hτ, f.pump_eq hν.ne' hω, norm_sq_neg_sub',
      norm_sq_mul_I_half']
    have : (f.ηh * f.ν / 2) ^ 2 / 4 = (f.ηh * f.ν) ^ 2 / 16 := by ring
    linarith
  have h := BlockAveraging.three_unstable hν (f.fieldPole_neg hτ) h1 h2 h3 h4 h5 h6 f.shiftMatrix
    f.pumpMatrix hg'
  filter_upwards [h] with ε hε
  rw [show (fun t => (f.machine ε t).stateMatrix) =
      physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
    funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
  exact hε

/-! ## The second-order boundary: the pump reaches the pair through the field mode -/

/-- The flux-decay gain `κ = ω₀K₂K₃K̂₄/(4Hm)` of the swing pair (`s' = D̂/(4H) + κτ`,
`d' = d̂ν + κ/ν`). -/
def coupK : ℝ := f.ω₀ * f.K₂ * f.K₃ * f.K4h / (4 * f.H * f.mden)

/-- The angle component `v₀ = −ω₀K₂τ²/(2Hm)` of the field mode's right eigenvector. -/
def fieldAngle : ℝ := -(f.ω₀ * f.K₂ * f.tau ^ 2 / (2 * f.H * f.mden))

/-- **The constant `O(ε)` part in modal coordinates**, `Q A₀' P`: the critical block
`[[−2κτ, 0], [−2d', −D̂/(2H)]]`, the coupling `β = (κω₀K₂τ³/(Hm), ω₀K₂τ(s' + ντd' − κτ)/(Hνm))ᵀ`
from the field into the pair (the torque perturbation acting on the swing components of the
field mode), `γ = (−K̂₄/T'_{d0}, 0)` from the pair into the field, and `B₂₂ = 2κτ`. -/
@[tmio M, powerlib_domain] theorem modalB_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.shiftMatrix *
        modalP f.rightVec f.fieldRight =
      fromBlocks !![-(2 * f.coupK * f.tau), 0; -(2 * f.dD), -(f.Dh / (2 * f.H))]
        !![f.coupK * f.ω₀ * f.K₂ * f.tau ^ 3 / (f.H * f.mden);
          f.ω₀ * f.K₂ * f.tau * (f.sD + f.ν * f.tau * f.dD - f.coupK * f.tau) /
            (f.H * f.ν * f.mden)]
        !![-(f.K4h / f.Td0), 0] !![2 * f.coupK * f.tau] := by
  have hK : f.K₃ ≠ 0 := by rintro h; rw [h, zero_mul] at hτ; exact lt_irrefl _ hτ
  have hT : f.Td0 ≠ 0 := by rintro h; rw [h, mul_zero] at hτ; exact lt_irrefl _ hτ
  have hm := f.mden_pos.ne'
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [modalQ, modalP, FluxDecayParametric.Weak.fieldVec, fieldRight, shiftMatrix,
      Matrix.mul_apply, Fin.sum_univ_three, r0, r0', r1, r1', r2, r2', l0, l0', l1, l1', l2, l2',
      sD, dD, coupK] <;> (try simp only [tau]) <;> field_simp <;> ring

/-- **The modulation in modal coordinates**, `Q A₁ P`: the critical block `[[0, 0], [η̂ν, 0]]`
and the modulated coupling `A₁₂ = (0, η̂ν v₀)ᵀ` from the field into the pair, through the angle
component `v₀` of the field mode; no modulated coupling out of the pair (`A₂₁ = 0`). -/
@[tmio M, powerlib_domain] theorem modalA_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec).map (algebraMap ℝ ℂ) * f.pumpMatrix *
        (modalP f.rightVec f.fieldRight).map (algebraMap ℝ ℂ) =
      fromBlocks !![0, 0; ((f.ηh * f.ν : ℝ) : ℂ), 0] !![0; ((f.ηh * f.ν * f.fieldAngle : ℝ) : ℂ)]
        0 0 := by
  have hm := f.mden_pos.ne'
  have hν' : (f.ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hω' : (f.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [modalQ, modalP, FluxDecayParametric.Weak.fieldVec, fieldRight, pumpMatrix,
      Matrix.mul_apply, Fin.sum_univ_three, r0, r0', r1, r1', r2, r2', l0, l0', l1, l1', l2, l2',
      fieldAngle] <;> field_simp <;> simp only [true_or]

set_option maxHeartbeats 1000000 in
/-- **The decisive quantity of the converse family in closed form**:
`blockMixed = d'(s'² + d'² − 3(η̂ν)²/32)/ν + ω₀K₂K₃K̂₄τ²(s'² + d'² − (η̂ν)²/16)/(Hm²)`
(`τ = K₃T'_{d0}`, `m = 1 + ν²τ²`). The swing pair alone gives the first term with the
first-order data `s'`, `d'` of the flux decay; the field mode enters through the constant
coupling `βγ` (the angle drives the flux through `K̂₄`, the flux acts on the swing through the
field mode's swing components) and through the modulated coupling `A₁₂`, both at the resolvent
`(λ₃ − jν)⁻¹`, and together they are proportional to `s'² + d'² − |g/2|²`. -/
@[tmio M, powerlib_domain] theorem blockMixed_eq (hν : 0 < f.ν) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    blockMixed 0 0 (2 * f.ν) !![f.fieldPole]
        ((modalQ f.leftVec FluxDecayParametric.Weak.fieldVec).map (algebraMap ℝ ℂ) *
          f.pumpMatrix * (modalP f.rightVec f.fieldRight).map (algebraMap ℝ ℂ))
        (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.shiftMatrix *
          modalP f.rightVec f.fieldRight) =
      f.dD * (f.sD ^ 2 + f.dD ^ 2 - 3 * (f.ηh * f.ν) ^ 2 / 32) / f.ν +
        f.ω₀ * f.K₂ * f.K₃ * f.K4h * f.tau ^ 2 * (f.sD ^ 2 + f.dD ^ 2 - (f.ηh * f.ν) ^ 2 / 16) /
          (f.H * f.mden ^ 2) := by
  have hK : f.K₃ ≠ 0 := by rintro h; rw [h, zero_mul] at hτ; exact lt_irrefl _ hτ
  have hT : f.Td0 ≠ 0 := by rintro h; rw [h, mul_zero] at hτ; exact lt_irrefl _ hτ
  have hm := f.mden_pos.ne'
  rw [f.modalA_eq hν.ne' hω, f.modalB_eq hν.ne' hω hH hτ, blockMixed_core _ _ _ _ _ _ _ _ _ _ _ hν]
  have hτ' : f.tau ≠ 0 := hτ.ne'
  have hml : f.fieldPole ^ 2 + f.ν ^ 2 = f.mden / f.tau ^ 2 := by
    simp only [fieldPole, mden, tau]; field_simp
  rw [hml]
  simp only [fieldPole, coupK, fieldAngle, sD, dD]
  simp only [mden, tau] at hm ⊢
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **The converse family on its first-order boundary, decided at second order.** On the
boundary `s'² + d'² = (η̂ν)²/16` with `s' > 0` (`s' = sD = D̂/(4H) + ω₀K₂K₃K̂₄τ/(4Hm)`,
`d' = dD = d̂ν + ω₀K₂K₃K̂₄/(4Hνm)`, `τ = K₃T'_{d0}`, `m = 1 + ν²τ²`): for all small `ε > 0`,
`d' < 0` puts every Floquet multiplier of the family inside the unit circle and `d' > 0` gives
Floquet instability. The second-order resolvent terms of the field mode — the constant coupling
through `K̂₄` and the field mode's swing components, and the modulated coupling `A₁₂` by which
the pump reaches the pair through the field mode — add up to
`ω₀K₂K₃K̂₄τ²(s'² + d'² − |g/2|²)/(Hm²)` (`blockMixed_eq`) and vanish on the boundary: the
verdict is the Mathieu-type sign of `−d'`, as in the opposite limit `FluxDecayParametric.Driven`
with `K₄K̂₂` replaced by `K₂K̂₄`. -/
@[tmio M, powerlib_domain] theorem secondOrder_boundary (hH : 0 < f.H) (hω : f.ω₀ ≠ 0)
    (hν : 0 < f.ν) (hτ : 0 < f.K₃ * f.Td0) (hs : 0 < f.sD)
    (hb : f.sD ^ 2 + f.dD ^ 2 = (f.ηh * f.ν) ^ 2 / 16) :
    (f.dD < 0 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
        (Periodic.monodromy (fun t => (f.machine ε t).stateMatrix) (2 * Real.pi / (2 * f.ν))
            0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (0 < f.dD →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fun t => (f.machine ε t).stateMatrix)
          (2 * Real.pi / (2 * f.ν))) := by
  obtain ⟨hQP, hPQ, hQAP, hL, hR⟩ := f.modal hν.ne' hω hH.ne' hτ
  have hω2 : 0 < 2 * f.ν := by linarith
  have hT : 0 < 2 * Real.pi / (2 * f.ν) := by positivity
  have hA0 : modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.critMatrix *
      modalP f.rightVec f.fieldRight =
      fromBlocks (TwoToOne.base 0 (2 * f.ν / 2)) 0 0 !![f.fieldPole] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hρ : spectralRadius ℂ ((expS (!![f.fieldPole] : Matrix (Fin 1) (Fin 1) ℝ)
      (2 * Real.pi / (2 * f.ν))).map (algebraMap ℝ ℂ)) < 1 := by
    have hq :
        ‖expS (!![f.fieldPole] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * f.ν))‖ < 1 := by
      rw [BlockAveraging.norm_expS_one, Real.exp_lt_one_iff]
      exact mul_neg_of_pos_of_neg hT (f.fieldPole_neg hτ)
    exact BlockAveraging.spectralRadius_lt_one_of_norm _ hq
  have hsh := f.shift_eq hν.ne' hω hH.ne' hτ
  have hs' : (physLeft (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) ⬝ᵥ
      (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ physRight (modalP f.rightVec f.fieldRight))).re < 0 := by
    rw [hL, hR, hsh, re_neg_sub']; linarith
  have hb' : ‖physLeft (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) ⬝ᵥ
        (f.pumpMatrix *ᵥ star (physRight (modalP f.rightVec f.fieldRight))) / 2‖ ^ 2 =
      ‖physLeft (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) ⬝ᵥ
        (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ physRight (modalP f.rightVec f.fieldRight))‖ ^ 2 := by
    rw [hL, hR, hsh, f.pump_eq hν.ne' hω, norm_sq_neg_sub', norm_sq_mul_I_half', hb]
    ring
  have h := PhysicalBoundary.physical_boundary hω2 hPQ hQP !![f.fieldPole] hA0 f.shiftMatrix
    f.pumpMatrix hs' hb' hρ
  have hconj := BlockAveraging.shift_conj (modalP f.rightVec f.fieldRight)
    (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) f.shiftMatrix
  have hpu := BlockAveraging.pump_conj (modalP f.rightVec f.fieldRight)
    (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) f.pumpMatrix
  rw [hL, hR, hsh] at hconj
  rw [hL, hR, f.pump_eq hν.ne' hω] at hpu
  have hsr : shiftRe (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.shiftMatrix *
      modalP f.rightVec f.fieldRight) = -f.sD := by
    have := congrArg Complex.re hconj; simp at this; linarith
  have hsi : shiftIm (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.shiftMatrix *
      modalP f.rightVec f.fieldRight) = -f.dD := by
    have := congrArg Complex.im hconj; simp at this; linarith
  have e1 : -(physLeft (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) ⬝ᵥ
      (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ physRight (modalP f.rightVec f.fieldRight))).re =
      0 - shiftRe (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.shiftMatrix *
        modalP f.rightVec f.fieldRight) := by
    rw [hL, hR, hsh, re_neg_sub', hsr]; ring
  have e2 : -(physLeft (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) ⬝ᵥ
      (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ physRight (modalP f.rightVec f.fieldRight))).im =
      0 - shiftIm (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec * f.shiftMatrix *
        modalP f.rightVec f.fieldRight) := by
    rw [hL, hR, hsh, hsi]; simp
  have hpu' : physLeft (modalQ f.leftVec FluxDecayParametric.Weak.fieldVec) ⬝ᵥ
      (f.pumpMatrix *ᵥ star (physRight (modalP f.rightVec f.fieldRight))) =
      Element.pump ((modalQ f.leftVec FluxDecayParametric.Weak.fieldVec).map (algebraMap ℝ ℂ) *
        f.pumpMatrix * (modalP f.rightVec f.fieldRight).map (algebraMap ℝ ℂ)).toBlocks₁₁
        TwoToOne.left TwoToOne.right := by
    rw [BlockAveraging.pump_conj]
  rw [e1, e2, hpu', mixedDet_effSecond 0 0 hω2 _ _ _ hρ, f.blockMixed_eq hν hω hH.ne' hτ, hsr,
    hsi, hpu, norm_sq_mul_I_half'] at h
  have hab : 0 < (f.ηh * f.ν) ^ 2 := by
    have : 0 < f.sD ^ 2 := by positivity
    nlinarith [sq_nonneg f.dD]
  have hval : -((0 - -f.sD) * (2 * Real.pi / (2 * f.ν)) ^ 2 *
        ((0 - -f.sD) ^ 2 + (0 - -f.dD) ^ 2 - (f.ηh * f.ν / 2) ^ 2 / 4)) +
      2 * Real.pi / (2 * f.ν) *
        (f.dD * (f.sD ^ 2 + f.dD ^ 2 - 3 * (f.ηh * f.ν) ^ 2 / 32) / f.ν +
          f.ω₀ * f.K₂ * f.K₃ * f.K4h * f.tau ^ 2 * (f.sD ^ 2 + f.dD ^ 2 - (f.ηh * f.ν) ^ 2 / 16) /
            (f.H * f.mden ^ 2)) =
      2 * Real.pi / (2 * f.ν) * -(f.dD * (f.ηh * f.ν) ^ 2 / (32 * f.ν)) := by
    have hm := f.mden_pos.ne'
    have e : (0 - -f.sD) ^ 2 + (0 - -f.dD) ^ 2 - (f.ηh * f.ν / 2) ^ 2 / 4 = 0 := by
      rw [sub_neg_eq_add, zero_add, sub_neg_eq_add, zero_add, hb]; ring
    have e' : f.sD ^ 2 + f.dD ^ 2 - (f.ηh * f.ν) ^ 2 / 16 = 0 := by rw [hb]; ring
    rw [e, e', hb, mul_zero, neg_zero, zero_add, mul_zero, zero_div, add_zero]
    field_simp
    ring
  rw [hval] at h
  refine ⟨fun hneg => ?_, fun hpos => ?_⟩
  · have hm : 0 < -(f.dD * (f.ηh * f.ν) ^ 2 / (32 * f.ν)) := by
      have : f.dD * (f.ηh * f.ν) ^ 2 / (32 * f.ν) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hab) (by positivity)
      linarith
    filter_upwards [h.1 (mul_pos hT hm)] with ε hε
    rw [show (fun t => (f.machine ε t).stateMatrix) =
        physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
      funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
    exact hε
  · have hm : -(f.dD * (f.ηh * f.ν) ^ 2 / (32 * f.ν)) < 0 := by
      have : 0 < f.dD * (f.ηh * f.ν) ^ 2 / (32 * f.ν) := by positivity
      linarith
    filter_upwards [h.2 (mul_neg_of_pos_of_neg hT hm)] with ε hε
    rw [show (fun t => (f.machine ε t).stateMatrix) =
        physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
      funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
    exact hε

end Converse

end powerlib.Synchronous.FluxDecayConverse
