import theorem.ParametricResonance.BlockCoreClosedForm
import theorem.ParametricResonance.PhysicalBoundary

/-! # The flux-decay machine under a pumped synchronizing coefficient: the field mode at 2:1

The linearized one-axis (flux-decay) machine of Heffron–Phillips with constant field voltage,
`Δδ̇ = ω₀Δω`, `2HΔω̇ = −K₁Δδ − K₂ΔE'_q − DΔω`, `T'_{d0}K₃ΔĖ'_q = −ΔE'_q − K₃K₄Δδ`
(`Params.stateMatrix`, `Params.stateMatrix_mulVec_iff`), with the synchronizing coefficient pumped,
`K₁(t) = K₁(1 + η cos 2νt)` (`Params.pumped`). Near the 2:1 resonance the averaging theory applies
in a distinguished limit: damping `D = εD̂`, detuning `K₁ = (2H/ω₀)ν²(1 − 2εd̂)` and depth `εη̂`
of order `ε`, and the flux-decay torque `K₂K₃K₄` small. Two limits are treated; in both the state
matrix is exactly `A₀c + ε(A₀' + Re{A₁ e^{j2νt}})` and the modal coordinates are explicit
(`BlockAveraging.modal_three`), so the field mode is a three-state block core with one real
stable mode `λ₃ = −1/τ`, `τ = K₃T'_{d0}`, decided on the first-order boundary by
`BlockCoreClosedForm.mixedDet_effSecond` through `PhysicalBoundary.physical_boundary`.

* Weak field coupling (`Weak`: `K₂ = εK̂₂`, `K₄ = εK̂₄`, flux-decay torque of order `ε²`). The
  first-order shift `λ₁ = −D̂/(4H) − jd̂ν` and pump `g = jη̂ν/2` do not see the field
  (`Weak.firstOrder_stable`, `Weak.firstOrder_unstable`: `H²η̂²ν² ≶ D̂² + 16H²d̂²ν²`). On the
  boundary `D̂² + 16H²d̂²ν² = H²η̂²ν²`, `D̂ > 0`, the verdict is the sign of
  `fieldMixed = −d̂η̂²ν²/32 + ω₀K₃K̂₂K̂₄(D̂τ + 4Hd̂)/(8H²(1 + ν²τ²))` (`Weak.secondOrder_boundary`,
  `Weak.blockMixed_eq`): the swing pair alone plus the field mode through its resolvent
  `(λ₃ − jν)⁻¹ = −τ/(1 + jντ)`, i.e. the flux-decay transfer function `K₃/(1 + jνK₃T'_{d0})` at
  the oscillation frequency, `(uβ)(λ₃ − jν)⁻¹(γr) = ω₀K₃K̂₂K̂₄(ντ + j)/(4Hν(1 + ν²τ²))`: the
  damping and synchronizing torque coefficients of the flux decay, weighted by the slow-flow
  damping `D̂/(4H)` and detuning `d̂ν`. `fieldMixed` is homogeneous of degree three in the
  first-order data, so in the machine's own coefficients (`δ = εd̂`, `η = εη̂`, `D`, `K₂K₄`) the
  sign is that of `−δη²ν²/32 + ω₀K₃K₂K₄(Dτ + 4Hδ)/(8H²(1 + ν²τ²))`.
* Driven field (`Driven`: `K₄` fixed, `K₂ = εK̂₂`; the rotor angle drives the flux at order one,
  the flux acts on the torque at order `ε`). The first-order shift already contains the
  flux-decay torque, `λ₁ = −s' − jd'`, `s' = D̂/(4H) + ω₀K₃K₄K̂₂τ/(4Hm)`,
  `d' = d̂ν + ω₀K₃K₄K̂₂/(4Hνm)`, `m = 1 + ν²τ²` (`Driven.shift_eq`, `Driven.firstOrder_stable`,
  `Driven.firstOrder_unstable`: `(η̂ν)²/16 ≶ s'² + d'²`). On the boundary `s'² + d'² = (η̂ν)²/16`,
  `s' > 0`, the field's second-order terms — the constant couplings `β`, `γ` and the modulated
  coupling `A₂₁` that the pump induces in the field through the modal coordinates, all through
  `(λ₃ − jν)⁻¹` — are proportional to `s'² + d'² − |g/2|²` and cancel exactly, because `A₀'` and
  `A₁` act through the same (torque) equation; the verdict is the sign of `−d'`
  (`Driven.secondOrder_boundary`).

Model boundary.
* One synchronous machine, the linearized one-axis model at an operating point in the state
  `(Δδ, Δω, ΔE'_q)` (rotor angle, per-unit speed, transient q-axis voltage), continuous time,
  constant field voltage: no AVR, exciter or PSS (`K₅`, `K₆` absent), no damper windings, no
  network or multi-machine dynamics, no saturation; `K₁ … K₄`, `H`, `D`, `T'_{d0}`, `ω₀` constant
  except the prescribed external modulation of `K₁` (a periodic variation of the operating point,
  as in `theorem/PowerSystem/Synchronous/ParametricSwing.lean`).
* The families `Weak`, `Driven` at the pump frequency `2ν`: `H > 0`, `ν > 0`, `ω₀ ≠ 0`,
  `K₃T'_{d0} > 0`; Floquet statements for the periodic state matrix `(machine ε t).stateMatrix`,
  period `2π/(2ν)`, for all sufficiently small `ε > 0`; linearization about the equilibrium of
  the unpumped machine (the variational equation is exact for the linear model).
* Not covered: the converse limit `K₂` fixed, `K₄ = εK̂₄` (the pump then reaches the pair through
  the field's left eigenvector as a modulated coupling `A₁₂`); `fieldMixed = 0`, `d' = 0` (next
  order).
* The machine is a data model (as `ParametricSwing`'s `Params`), not a model family: no
  connection between families or representations is stated, so no scaffold is involved.

Source: W. G. Heffron, R. A. Phillips, "Effect of a modern amplidyne voltage regulator on
underexcited operation of large turbine generators", AIEE Trans. PAS-71 (1952); F. P. deMello,
C. Concordia, "Concepts of synchronous machine stability as affected by excitation control", IEEE
Trans. PAS-88 (1969) (the coefficients `K₁ … K₄`, the flux-decay block `K₃/(1 + sK₃T'_{d0})`);
P. Kundur, *Power System Stability and Control* (1994) §12.3; the 2:1 theory of
`theorem/ParametricResonance/BlockCoreClosedForm.lean`, `PhysicalBoundary.physical_boundary`,
`BlockAveraging.three_stable`, `BlockAveraging.three_unstable`, `BlockAveraging.modal_three`.

Results.
* `Params`, `Params.stateMatrix`, `Params.stateMatrix_mulVec_iff`, `Params.pumped` — the model.
* `Weak`, `Weak.params`, `Weak.K1t`, `Weak.machine`, `Weak.machine_eq_pumped`,
  `Weak.critMatrix`, `Weak.shiftMatrix`, `Weak.pumpMatrix`, `Weak.machine_stateMatrix` — the
  weak-coupling family and its form `A₀c + ε(A₀' + Re{A₁ e^{j2νt}})`.
* `Weak.rightVec`, `Weak.leftVec`, `Weak.fieldVec`, `Weak.fieldPole`, `Weak.modal`,
  `Weak.shift_eq`, `Weak.pump_eq` — modal coordinates, `λ₁ = −D̂/(4H) − jd̂ν`, `g = jη̂ν/2`.
* `Weak.firstOrder_stable`, `Weak.firstOrder_unstable` — the first-order threshold.
* `Weak.modalB`, `Weak.modalA`, `Weak.modalB_eq`, `Weak.modalA_eq`, `Weak.pump_modalA`,
  `Weak.blockMixed_eq` — the modal core and its decisive quantity in closed form.
* `Weak.fieldMixed`, `Weak.secondOrder_boundary` — the boundary decided at second order.
* `Driven`, `Driven.params`, `Driven.machine`, `Driven.tau`, `Driven.mden`, `Driven.critMatrix`,
  `Driven.shiftMatrix`, `Driven.pumpMatrix`, `Driven.machine_stateMatrix`, `Driven.rightVec`,
  `Driven.leftVec`, `Driven.fieldLeft`, `Driven.fieldPole`, `Driven.sD`, `Driven.dD`,
  `Driven.modal`, `Driven.shift_eq`, `Driven.pump_eq`, `Driven.firstOrder_stable`,
  `Driven.firstOrder_unstable`, `Driven.coupB`, `Driven.coupRho`, `Driven.modalB_eq`,
  `Driven.modalA_eq`, `Driven.secondOrder_boundary` — the driven-field family: the flux-decay
  torque at first order, the cancellation of its resolvent terms on the boundary.

Corrections and sharpenings.
* Without the field (`K̂₂K̂₄ = 0`) the verdict on the boundary is the sign of `−d̂`: the boundary
  point with the natural frequency below half the pump frequency is unstable, the tongue bends
  toward lower stiffness, as Mathieu's transition curves
  `δ = 1/4 ± ε/2 − ε²/8` do. This is the
  opposite of the sign of `d|g'|²` in `SecondOrder.full_boundary_closed_form`, which concerns a
  modal pair detuned by a perturbation commuting with `J`; here the detuning (in `K₁`) and the
  damping (in `D`) act on one equation only, and their anticommuting part
  `n = D̂/(4H) − jd̂ν` (`BlockCoreClosedForm.critMixed`) reverses the verdict.
* With `ω₀K₂K₃K₄ > 0` the weakly coupled flux decay is stabilizing on the boundary wherever
  `D̂τ + 4Hd̂ > 0`; for `ω₀K₂K₃K₄ < 0` it is destabilizing there.
* The field mode does not change the parametric boundary at second order through the resolvent
  terms when it is driven at order one (`Driven`): its whole effect is its first-order damping
  and synchronizing torque in `s'`, `d'`. When both couplings are weak (`Weak`) its effect is
  only at second order, through the resolvent. The second-order effect of the flux decay
  therefore depends on the distinguished limit, not on the first-order data alone.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers) of the selected machine
model.
-/

noncomputable section
namespace powerlib.Synchronous.FluxDecayParametric

open Complex Matrix Filter Topology
open scoped Matrix.Norms.Operator
open powerlib.ParametricResonance
open powerlib.ParametricResonance.BlockAveraging (physJ physLeft physRight modX expS modalP modalQ
  FzcB shiftRe shiftIm)
open powerlib.ParametricResonance.BlockCoreClosedForm

/-! ## The linearized one-axis machine -/

/-- The linearized one-axis (flux-decay) machine of Heffron–Phillips with constant field voltage:
the coefficients `K₁ … K₄`, inertia `H`, damping `D`, open-circuit field time constant `T'_{d0}`
and synchronous frequency `ω₀`. -/
structure Params where
  /-- Synchronizing torque coefficient `K₁ = ∂T_e/∂δ` at constant `E'_q`. -/
  K₁ : ℝ
  /-- Torque coefficient `K₂ = ∂T_e/∂E'_q` of the field flux. -/
  K₂ : ℝ
  /-- Impedance factor `K₃` of the field circuit. -/
  K₃ : ℝ
  /-- Demagnetizing coefficient `K₄` of a rotor-angle change. -/
  K₄ : ℝ
  /-- Inertia constant `H`. -/
  H : ℝ
  /-- Damping coefficient `D`. -/
  D : ℝ
  /-- Open-circuit transient time constant `T'_{d0}` of the field. -/
  Td0 : ℝ
  /-- Synchronous angular frequency `ω₀`. -/
  ω₀ : ℝ

namespace Params

/-- The state matrix in the state `(Δδ, Δω, ΔE'_q)`. -/
def stateMatrix (p : Params) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, p.ω₀, 0;
     -p.K₁ / (2 * p.H), -p.D / (2 * p.H), -p.K₂ / (2 * p.H);
     -p.K₄ / p.Td0, 0, -1 / (p.K₃ * p.Td0)]

/-- **The state matrix is the model.** `ẋ = A x` in the state `x = (Δδ, Δω, ΔE'_q)` exactly when
`Δδ̇ = ω₀ Δω`, `2H Δω̇ = −K₁ Δδ − K₂ ΔE'_q − D Δω`, `T'_{d0} K₃ ΔĖ'_q = −ΔE'_q − K₃ K₄ Δδ`. -/
@[tmio M, powerlib_domain] theorem stateMatrix_mulVec_iff (p : Params) (hH : p.H ≠ 0)
    (hT : p.Td0 ≠ 0) (hK : p.K₃ ≠ 0) (x dx : Fin 3 → ℝ) :
    dx = p.stateMatrix *ᵥ x ↔
      dx 0 = p.ω₀ * x 1 ∧ 2 * p.H * dx 1 = -p.K₁ * x 0 - p.K₂ * x 2 - p.D * x 1 ∧
        p.Td0 * p.K₃ * dx 2 = -x 2 - p.K₃ * p.K₄ * x 0 := by
  have e0 : (p.stateMatrix *ᵥ x) 0 = p.ω₀ * x 1 := by
    simp [stateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e1 : 2 * p.H * (p.stateMatrix *ᵥ x) 1 = -p.K₁ * x 0 - p.K₂ * x 2 - p.D * x 1 := by
    simp [stateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  have e2 : p.Td0 * p.K₃ * (p.stateMatrix *ᵥ x) 2 = -x 2 - p.K₃ * p.K₄ * x 0 := by
    simp [stateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  constructor
  · rintro rfl
    exact ⟨e0, e1, e2⟩
  · rintro ⟨h0, h1, h2⟩
    have hH2 : 2 * p.H ≠ 0 := mul_ne_zero two_ne_zero hH
    have hTK : p.Td0 * p.K₃ ≠ 0 := mul_ne_zero hT hK
    funext i
    fin_cases i
    · exact h0.trans e0.symm
    · exact mul_left_cancel₀ hH2 (h1.trans e1.symm)
    · exact mul_left_cancel₀ hTK (h2.trans e2.symm)

/-- The machine with the synchronizing coefficient modulated: `K₁(t) = K₁ (1 + η cos Ωt)`. -/
def pumped (p : Params) (η Ω t : ℝ) : Params := { p with K₁ := p.K₁ * (1 + η * Real.cos (Ω * t)) }

end Params

/-! ## The weak-coupling family at the 2:1 resonance -/

/-- The data of the family: inertia `H`, frequency `ω₀`, half pump frequency `ν`, the field
constants `K₃`, `T'_{d0}`, and the first-order data `D̂, K̂₂, K̂₄, d̂, η̂` (damping, the two field
couplings, detuning and pump depth, all multiplied by `ε` in the machine). -/
structure Weak where
  H : ℝ
  ω₀ : ℝ
  ν : ℝ
  K₃ : ℝ
  Td0 : ℝ
  Dh : ℝ
  K2h : ℝ
  K4h : ℝ
  dh : ℝ
  ηh : ℝ

namespace Weak

variable (f : Weak)

/-- The machine at `ε`: `K₁ = (2H/ω₀) ν² (1 − 2εd̂)`, `K₂ = εK̂₂`, `K₄ = εK̂₄`, `D = εD̂`. -/
def params (ε : ℝ) : Params :=
  ⟨2 * f.H / f.ω₀ * f.ν ^ 2 * (1 - 2 * ε * f.dh), ε * f.K2h, f.K₃, ε * f.K4h, f.H, ε * f.Dh,
    f.Td0, f.ω₀⟩

/-- The pumped synchronizing coefficient `K₁(t) = (2H/ω₀) ν² (1 − 2εd̂ + εη̂ cos 2νt)`. -/
def K1t (ε t : ℝ) : ℝ :=
  2 * f.H / f.ω₀ * f.ν ^ 2 * (1 - 2 * ε * f.dh + ε * f.ηh * Real.cos (2 * f.ν * t))

/-- The machine of the family at `ε` and time `t`. -/
def machine (ε t : ℝ) : Params := { f.params ε with K₁ := f.K1t ε t }

/-- The family is the pumped machine `K₁(t) = K₁ (1 + η cos 2νt)` with the relative depth
`η = εη̂/(1 − 2εd̂)`. -/
@[tmio M, powerlib_domain] theorem machine_eq_pumped {ε : ℝ} (h : 1 - 2 * ε * f.dh ≠ 0) (t : ℝ) :
    f.machine ε t = (f.params ε).pumped (ε * f.ηh / (1 - 2 * ε * f.dh)) (2 * f.ν) t := by
  simp only [machine, params, Params.pumped, K1t]
  congr 1
  field_simp

/-- The critical state matrix `A₀c` (pair `±jν`, field pole `−1/(K₃T'_{d0})`, no coupling). -/
def critMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, f.ω₀, 0; -(f.ν ^ 2 / f.ω₀), 0, 0; 0, 0, -1 / (f.K₃ * f.Td0)]

/-- The first-order change `A₀'`: detuning, damping and the two field couplings. -/
def shiftMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 2 * f.dh * f.ν ^ 2 / f.ω₀, -(f.Dh / (2 * f.H)), -(f.K2h / (2 * f.H));
    -(f.K4h / f.Td0), 0, 0]

/-- The modulation `A₁`, `Re{A₁ e^{j2νt}} = A₁ cos 2νt`. -/
def pumpMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; -((f.ηh * f.ν ^ 2 / f.ω₀ : ℝ) : ℂ), 0, 0; 0, 0, 0]

/-- **The family's state matrix** is `A₀c + ε(A₀' + Re{A₁ e^{j2νt}})`. -/
@[tmio M, powerlib_domain] theorem machine_stateMatrix (hH : f.H ≠ 0) (hω : f.ω₀ ≠ 0) (ε t : ℝ) :
    (f.machine ε t).stateMatrix = physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Params.stateMatrix, machine, params, K1t, physJ, modX, critMatrix, shiftMatrix,
      pumpMatrix,
      -Complex.ofReal_mul, -Complex.ofReal_pow, -Complex.ofReal_div] <;>
    field_simp <;> ring

/-! ## Modal coordinates and the first-order threshold -/

@[tmio T, powerlib_foundation] private theorem norm_sq_neg_sub (a b : ℝ) :
    ‖-(a : ℂ) - (b : ℂ) * I‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

@[tmio T, powerlib_foundation] private theorem norm_sq_mul_I_half (c : ℝ) :
    ‖(c : ℂ) * I / 2‖ ^ 2 = c ^ 2 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

@[tmio T, powerlib_foundation] private theorem norm_sq_mul_I_quarter (c : ℝ) :
    ‖(c : ℂ) * I / 2 / 2‖ ^ 2 = c ^ 2 / 16 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

@[tmio T, powerlib_foundation] private theorem re_neg_sub (a b : ℝ) :
    (-(a : ℂ) - (b : ℂ) * I).re = -a := by simp

@[tmio T, powerlib_foundation] private theorem re_mul_mk (a b p q : ℝ) :
    (((a : ℂ) - (b : ℂ) * I) * (⟨p, q⟩ : ℂ)).re = a * p + b * q := by
  simp [Complex.mul_re]

@[tmio T, powerlib_foundation] private theorem re_crit (a c x y : ℝ) :
    ((a : ℂ) * ((c : ℂ) * I / 2 / 2) * star (⟨x, y⟩ : ℂ)).re = a * c * y / 4 := by
  simp [Complex.mul_re, Complex.mul_im]; ring

@[tmio T, powerlib_foundation] private theorem norm_sq_mk (x y : ℝ) :
    ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mk]; ring

/-- The right eigenvector `r = (1, jν/ω₀, 0)` of the swing pair `jν` of `A₀c`. -/
def rightVec : Fin 3 → ℂ := ![1, ((f.ν / f.ω₀ : ℝ) : ℂ) * I, 0]

/-- The left eigenvector `u = (1/2, −jω₀/(2ν), 0)`, `u r = 1`. -/
def leftVec : Fin 3 → ℂ := ![1 / 2, -(((f.ω₀ / (2 * f.ν) : ℝ) : ℂ) * I), 0]

/-- The field direction `e₃`, right and left eigenvector of the field pole. -/
def fieldVec : Fin 3 → ℝ := ![0, 0, 1]

/-- The field pole `λ₃ = −1/(K₃ T'_{d0})`. -/
def fieldPole : ℝ := -1 / (f.K₃ * f.Td0)

@[tmio M, powerlib_domain] private theorem rightVec_parts :
    ((f.rightVec 0).re = 1 ∧ (f.rightVec 0).im = 0) ∧
      ((f.rightVec 1).re = 0 ∧ (f.rightVec 1).im = f.ν / f.ω₀) ∧
      ((f.rightVec 2).re = 0 ∧ (f.rightVec 2).im = 0) := by
  simp [rightVec, -Complex.ofReal_div]

@[tmio M, powerlib_domain] private theorem leftVec_parts :
    ((f.leftVec 0).re = 1 / 2 ∧ (f.leftVec 0).im = 0) ∧
      ((f.leftVec 1).re = 0 ∧ (f.leftVec 1).im = -(f.ω₀ / (2 * f.ν))) ∧
      ((f.leftVec 2).re = 0 ∧ (f.leftVec 2).im = 0) := by
  simp [leftVec, -Complex.ofReal_div]

@[tmio M, powerlib_domain] private theorem eigen (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    f.critMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec = ((f.ν : ℂ) * I) • f.rightVec ∧
      f.leftVec ᵥ* f.critMatrix.map (algebraMap ℝ ℂ) = ((f.ν : ℂ) * I) • f.leftVec ∧
      f.leftVec ⬝ᵥ f.rightVec = 1 ∧ f.critMatrix *ᵥ fieldVec = f.fieldPole • fieldVec ∧
      fieldVec ᵥ* f.critMatrix = f.fieldPole • fieldVec ∧ fieldVec ⬝ᵥ fieldVec = 1 := by
  have hν' : (f.ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hω' : (f.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;>
      simp [critMatrix, rightVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      field_simp <;> ring_nf <;> simp [I_sq]
  · funext i; fin_cases i <;>
      simp [critMatrix, leftVec, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
      field_simp <;> ring_nf <;> simp [I_sq]
  · simp [leftVec, rightVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring_nf
    simp [I_sq]
    ring
  · funext i; fin_cases i <;>
      simp [critMatrix, Weak.fieldVec, fieldPole, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · funext i; fin_cases i <;>
      simp [critMatrix, Weak.fieldVec, fieldPole, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  · simp [Weak.fieldVec, dotProduct, Fin.sum_univ_three]

/-- **The modal form of the family.** With `P = [Re r, −Im r, e₃]`, `Q = [2 Re u; 2 Im u; e₃ᵀ]`:
`Q P = P Q = I`, `Q A₀c P = diag(base(0, ν), λ₃)`, and the physical eigenvectors are `u`, `r`. -/
@[tmio M, powerlib_domain] theorem modal (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    modalQ f.leftVec fieldVec * modalP f.rightVec fieldVec = 1 ∧
      modalP f.rightVec fieldVec * modalQ f.leftVec fieldVec = 1 ∧
      modalQ f.leftVec fieldVec * f.critMatrix * modalP f.rightVec fieldVec =
        fromBlocks (TwoToOne.base 0 f.ν) 0 0 !![f.fieldPole] ∧
      physLeft (modalQ f.leftVec fieldVec) = f.leftVec ∧
      physRight (modalP f.rightVec fieldVec) = f.rightVec := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν hω
  exact BlockAveraging.modal_three hν h1 h2 h3 h4 h5 h6

/-- The first-order eigenvalue shift of the swing pair: `λ₁ = u A₀' r = −D̂/(4H) − j d̂ν`. The
field couplings do not enter at first order. -/
@[tmio M, powerlib_domain] theorem shift_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0) :
    f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec) =
      -((f.Dh / (4 * f.H) : ℝ) : ℂ) - ((f.dh * f.ν : ℝ) : ℂ) * I := by
  have hν' : (f.ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hω' : (f.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω
  have hH' : (f.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp [leftVec, rightVec, shiftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- The pump coefficient `g = u A₁ r̄ = j η̂ν/2`. -/
@[tmio M, powerlib_domain] theorem pump_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) = ((f.ηh * f.ν / 2 : ℝ) : ℂ) * I := by
  have hν' : (f.ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hω' : (f.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω
  simp [leftVec, rightVec, pumpMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  field_simp

@[tmio M, powerlib_domain] private theorem fieldPole_neg (hτ : 0 < f.K₃ * f.Td0) :
    f.fieldPole < 0 := by
  rw [fieldPole, neg_div]
  exact neg_neg_of_pos (one_div_pos.mpr hτ)

/-- **First-order threshold, stability.** For `D̂ > 0` and `H²η̂²ν² < D̂² + 16H²d̂²ν²` every Floquet
multiplier of the family (state `(Δδ, Δω, ΔE'_q)`, period `2π/(2ν)`) lies inside the unit circle
for all small `ε > 0` (`BlockAveraging.three_stable`). -/
@[tmio M, powerlib_domain] theorem firstOrder_stable (hH : 0 < f.H) (hω : f.ω₀ ≠ 0) (hν : 0 < f.ν)
    (hτ : 0 < f.K₃ * f.Td0) (hD : 0 < f.Dh)
    (hg : f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2 < f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
      (Periodic.monodromy (fun t => (f.machine ε t).stateMatrix) (2 * Real.pi / (2 * f.ν)) 0).map
          (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν.ne' hω
  have hs : (f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)).re < 0 := by
    rw [f.shift_eq hν.ne' hω hH.ne', re_neg_sub]
    have : 0 < f.Dh / (4 * f.H) := by positivity
    linarith
  have hg' : ‖f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) / 2‖ ^ 2 <
      ‖f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)‖ ^ 2 := by
    rw [f.shift_eq hν.ne' hω hH.ne', f.pump_eq hν.ne' hω, norm_sq_neg_sub, norm_sq_mul_I_half]
    have e : (f.Dh / (4 * f.H)) ^ 2 + (f.dh * f.ν) ^ 2 - (f.ηh * f.ν / 2) ^ 2 / 4 =
        (f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2 - f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2) /
          (16 * f.H ^ 2) := by
      field_simp; ring
    have : 0 < (f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2 - f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2) /
        (16 * f.H ^ 2) := div_pos (by linarith) (by positivity)
    linarith
  have h := BlockAveraging.three_stable hν (f.fieldPole_neg hτ) h1 h2 h3 h4 h5 h6 f.shiftMatrix
    f.pumpMatrix hs hg'
  filter_upwards [h] with ε hε
  rw [show (fun t => (f.machine ε t).stateMatrix) =
      physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
    funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
  exact hε

/-- **First-order threshold, parametric instability.** For `D̂² + 16H²d̂²ν² < H²η̂²ν²` the family
is Floquet unstable for all small `ε > 0` (`BlockAveraging.three_unstable`). -/
@[tmio M, powerlib_domain] theorem firstOrder_unstable (hH : 0 < f.H) (hω : f.ω₀ ≠ 0)
    (hν : 0 < f.ν) (hτ : 0 < f.K₃ * f.Td0)
    (hg : f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2 < f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fun t => (f.machine ε t).stateMatrix)
      (2 * Real.pi / (2 * f.ν)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν.ne' hω
  have hg' : ‖f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)‖ ^ 2 <
      ‖f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) / 2‖ ^ 2 := by
    rw [f.shift_eq hν.ne' hω hH.ne', f.pump_eq hν.ne' hω, norm_sq_neg_sub, norm_sq_mul_I_half]
    have e : (f.Dh / (4 * f.H)) ^ 2 + (f.dh * f.ν) ^ 2 - (f.ηh * f.ν / 2) ^ 2 / 4 =
        (f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2 - f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2) /
          (16 * f.H ^ 2) := by
      field_simp; ring
    have : (f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2 - f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2) /
        (16 * f.H ^ 2) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  have h := BlockAveraging.three_unstable hν (f.fieldPole_neg hτ) h1 h2 h3 h4 h5 h6 f.shiftMatrix
    f.pumpMatrix hg'
  filter_upwards [h] with ε hε
  rw [show (fun t => (f.machine ε t).stateMatrix) =
      physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
    funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
  exact hε

/-! ## The second-order boundary: the field mode through its resolvent -/

/-- The constant `O(ε)` part in modal coordinates, `Q A₀' P`: the critical block
`[[0, 0], [−2d̂ν, −D̂/(2H)]]` (detuning and damping, not commuting with `J`), the coupling
`β = (0, ω₀K̂₂/(2Hν))ᵀ` from the field into the pair and `γ = (−K̂₄/T'_{d0}, 0)` from the pair
into the field. -/
def modalB : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  fromBlocks !![0, 0; -(2 * f.dh * f.ν), -(f.Dh / (2 * f.H))]
    !![0; f.ω₀ * f.K2h / (2 * f.H * f.ν)] !![-(f.K4h / f.Td0), 0] 0

/-- The modulation in modal coordinates, `Q A₁ P`: only the critical block, `[[0, 0], [η̂ν, 0]]`. -/
def modalA : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ :=
  fromBlocks !![0, 0; ((f.ηh * f.ν : ℝ) : ℂ), 0] 0 0 0

@[tmio M, powerlib_domain] theorem modalB_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    modalQ f.leftVec fieldVec * f.shiftMatrix * modalP f.rightVec fieldVec = f.modalB := by
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [modalQ, modalP, fieldVec, shiftMatrix, modalB, Matrix.mul_apply, Fin.sum_univ_three,
      r0, r0', r1, r1', r2, r2', l0, l0', l1, l1', l2, l2'] <;> field_simp

@[tmio M, powerlib_domain] theorem modalA_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    (modalQ f.leftVec fieldVec).map (algebraMap ℝ ℂ) * f.pumpMatrix *
        (modalP f.rightVec fieldVec).map (algebraMap ℝ ℂ) = f.modalA := by
  have hν' : (f.ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hω' : (f.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [modalQ, modalP, fieldVec, pumpMatrix, modalA, Matrix.mul_apply, Fin.sum_univ_three,
      r0, r0', r1, r1', r2, r2', l0, l0', l1, l1', l2, l2'] <;> field_simp

/-- The pump of the modal critical block: `g = u (Q A₁ P)₁₁ r̄ = j η̂ν/2`. -/
@[tmio M, powerlib_domain] theorem pump_modalA :
    Element.pump f.modalA.toBlocks₁₁ TwoToOne.left TwoToOne.right =
      ((f.ηh * f.ν : ℝ) : ℂ) * I / 2 := by
  rw [TwoToOne.pump_base]
  simp [modalA]
  try ring

@[tmio M, powerlib_domain] private theorem antiPump_modalA :
    ‖SecondOrder.antiPump f.modalA.toBlocks₁₁‖ ^ 2 = (f.ηh * f.ν) ^ 2 / 4 := by
  have h : SecondOrder.antiPump f.modalA.toBlocks₁₁ = -(((f.ηh * f.ν : ℝ) : ℂ) * I / 2) := by
    rw [SecondOrder.antiPump_eq]
    simp [modalA]
    try ring
  rw [h, norm_neg, norm_sq_mul_I_half]

@[tmio M, powerlib_domain] private theorem fundSkew_modalA :
    fundSkew f.modalA.toBlocks₁₁ = ((f.ηh * f.ν / 2 : ℝ) : ℂ) := by
  simp [fundSkew, modalA]

@[tmio M, powerlib_domain] private theorem antiShift_modalB :
    antiShift f.modalB.toBlocks₁₁ = ⟨f.Dh / (4 * f.H), -(f.dh * f.ν)⟩ := by
  apply Complex.ext <;> simp [antiShift, modalB] <;> ring

@[tmio M, powerlib_domain] private theorem shift_modalB :
    shiftRe f.modalB = -(f.Dh / (4 * f.H)) ∧ shiftIm f.modalB = -(f.dh * f.ν) := by
  constructor <;> simp [shiftRe, shiftIm, modalB] <;> ring

@[tmio T, powerlib_foundation] private theorem antiShift_zero :
    antiShift (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  apply Complex.ext <;> simp [antiShift]

@[tmio M, powerlib_domain] private theorem projC_modal (hν : f.ν ≠ 0) (hH : f.H ≠ 0)
    (hT : f.Td0 ≠ 0) (hD : f.fieldPole ^ 2 + f.ν ^ 2 ≠ 0) :
    projC (f.modalB.toBlocks₁₂ * (f.modalB.toBlocks₂₁ * ThreeStateCore.lamInv f.fieldPole f.ν)) =
      ⟨f.ω₀ * f.K2h * f.K4h / (4 * f.H * f.Td0 * (f.fieldPole ^ 2 + f.ν ^ 2)),
        -(f.ω₀ * f.K2h * f.K4h * f.fieldPole /
          (4 * f.H * f.ν * f.Td0 * (f.fieldPole ^ 2 + f.ν ^ 2)))⟩ := by
  apply Complex.ext <;> simp only [projC] <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] <;>
    simp [modalB, ThreeStateCore.lamInv, NormalForm.quarter] <;>
    field_simp <;> ring

set_option maxHeartbeats 1000000 in
/-- **The decisive quantity of the family in closed form**, with `τ = K₃T'_{d0}`:
`blockMixed = d̂(D̂²/(16H²) + d̂²ν² − 3η̂²ν²/32) + ω₀K₃K̂₂K̂₄(D̂τ + 4Hd̂)/(8H²(1 + ν²τ²))`.
The first term is the swing pair alone (`critMixed`: the anticommuting part of the damping and
detuning meets the pump); the second is the field mode through its resolvent
`(λ₃ − jν)⁻¹ = −τ/(1 + jντ)`: `(uβ)(λ₃ − jν)⁻¹(γr) = ω₀K₃K̂₂K̂₄(ντ + j)/(4Hν(1 + ν²τ²))`, the
damping and synchronizing torque of the flux decay at the oscillation frequency. -/
@[tmio M, powerlib_domain] theorem blockMixed_eq (hν : 0 < f.ν) (hH : f.H ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    blockMixed 0 0 (2 * f.ν) !![f.fieldPole] f.modalA f.modalB =
      f.dh * (f.Dh ^ 2 / (16 * f.H ^ 2) + f.dh ^ 2 * f.ν ^ 2 - 3 * f.ηh ^ 2 * f.ν ^ 2 / 32) +
        f.ω₀ * f.K₃ * f.K2h * f.K4h * (f.Dh * (f.K₃ * f.Td0) + 4 * f.H * f.dh) /
          (8 * f.H ^ 2 * (1 + f.ν ^ 2 * (f.K₃ * f.Td0) ^ 2)) := by
  have hK : f.K₃ ≠ 0 := by rintro h; rw [h, zero_mul] at hτ; exact lt_irrefl _ hτ
  have hT : f.Td0 ≠ 0 := by rintro h; rw [h, mul_zero] at hτ; exact lt_irrefl _ hτ
  have hA12 : f.modalA.toBlocks₁₂ = 0 := toBlocks_fromBlocks₁₂ _ _ _ _
  have hA21 : f.modalA.toBlocks₂₁ = 0 := toBlocks_fromBlocks₂₁ _ _ _ _
  have hup : upPlus f.modalA = 0 := by simp [upPlus, hA12]
  have hum : upMinus f.modalA = 0 := by simp [upMinus, hA12]
  have hlm : lowMinus f.modalA = 0 := by simp [lowMinus, hA21]
  have hl3 : lowThree f.modalA = 0 := by simp [lowThree, hA21]
  have hs0 : ∀ μ : ℝ, sylv !![f.fieldPole] μ 0 = 0 := fun μ => by simp [sylv]
  have h2 : 2 * f.ν / 2 = f.ν := by ring
  have hD : f.fieldPole ^ 2 + f.ν ^ 2 ≠ 0 := by
    have : 0 < f.ν ^ 2 := by positivity
    positivity
  have hP : couplingP !![f.fieldPole] f.modalA f.modalB (2 * f.ν) =
      f.modalB.toBlocks₁₂ * (f.modalB.toBlocks₂₁ * ThreeStateCore.lamInv f.fieldPole f.ν) := by
    rw [couplingP, hup, hum, hlm, hl3, hs0, hs0, h2, sylv_fin_one hD]
    simp
  have hN : couplingN !![f.fieldPole] f.modalA f.modalB (2 * f.ν) = 0 := by
    rw [couplingN, hup, hlm, hs0]
    simp
  obtain ⟨hsr, hsi⟩ := f.shift_modalB
  rw [blockMixed, hP, hN, critMixed, f.projC_modal hν.ne' hH hT hD, re_mul_mk, antiShift_zero,
    star_zero, mul_zero, Complex.zero_re, mul_zero, add_zero, f.antiPump_modalA, f.pump_modalA,
    f.fundSkew_modalA, f.antiShift_modalB, re_crit, norm_sq_mk, hsr, hsi]
  simp only [fieldPole]
  field_simp
  ring

/-- The decisive second-order quantity of the family on its first-order boundary
(`τ = K₃T'_{d0}`): `−d̂η̂²ν²/32 + ω₀K₃K̂₂K̂₄(D̂τ + 4Hd̂)/(8H²(1 + ν²τ²))`. -/
def fieldMixed : ℝ :=
  -(f.dh * f.ηh ^ 2 * f.ν ^ 2 / 32) + f.ω₀ * f.K₃ * f.K2h * f.K4h *
    (f.Dh * (f.K₃ * f.Td0) + 4 * f.H * f.dh) / (8 * f.H ^ 2 * (1 + f.ν ^ 2 * (f.K₃ * f.Td0) ^ 2))

set_option maxHeartbeats 1000000 in
/-- **The flux-decay machine on its first-order boundary, decided at second order.** On the
boundary `D̂² + 16H²d̂²ν² = H²η̂²ν²` of the first-order threshold with `D̂ > 0`: for all small
`ε > 0`, `fieldMixed > 0` puts every Floquet multiplier of the family inside the unit circle and
`fieldMixed < 0` gives Floquet instability. Without the field (`K̂₂K̂₄ = 0`) the verdict is the sign
of `−d̂`: the boundary point with the natural frequency below half the pump frequency is unstable,
as for Mathieu's equation; the flux decay adds `ω₀K₃K̂₂K̂₄(D̂τ + 4Hd̂)/(8H²(1 + ν²τ²))`,
stabilizing for `ω₀K₂K₃K₄ > 0` wherever `D̂τ + 4Hd̂ > 0` (`τ = K₃T'_{d0}`). -/
@[tmio M, powerlib_domain] theorem secondOrder_boundary (hH : 0 < f.H) (hω : f.ω₀ ≠ 0)
    (hν : 0 < f.ν) (hτ : 0 < f.K₃ * f.Td0) (hD : 0 < f.Dh)
    (hb : f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2 = f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2) :
    (0 < f.fieldMixed →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
        (Periodic.monodromy (fun t => (f.machine ε t).stateMatrix) (2 * Real.pi / (2 * f.ν)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (f.fieldMixed < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fun t => (f.machine ε t).stateMatrix)
          (2 * Real.pi / (2 * f.ν))) := by
  obtain ⟨hQP, hPQ, hQAP, hL, hR⟩ := f.modal hν.ne' hω
  have hω2 : 0 < 2 * f.ν := by linarith
  have hT : 0 < 2 * Real.pi / (2 * f.ν) := by positivity
  have hA0 : modalQ f.leftVec fieldVec * f.critMatrix * modalP f.rightVec fieldVec =
      fromBlocks (TwoToOne.base 0 (2 * f.ν / 2)) 0 0 !![f.fieldPole] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hρ : spectralRadius ℂ ((expS (!![f.fieldPole] : Matrix (Fin 1) (Fin 1) ℝ)
      (2 * Real.pi / (2 * f.ν))).map (algebraMap ℝ ℂ)) < 1 := by
    have hq :
        ‖expS (!![f.fieldPole] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * f.ν))‖ < 1 := by
      rw [BlockAveraging.norm_expS_one, Real.exp_lt_one_iff]
      exact mul_neg_of_pos_of_neg hT (f.fieldPole_neg hτ)
    exact BlockAveraging.spectralRadius_lt_one_of_norm _ hq
  have hs : (physLeft (modalQ f.leftVec fieldVec) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
      physRight (modalP f.rightVec fieldVec))).re < 0 := by
    rw [hL, hR, f.shift_eq hν.ne' hω hH.ne', re_neg_sub]
    have : 0 < f.Dh / (4 * f.H) := by positivity
    linarith
  have hb' : ‖physLeft (modalQ f.leftVec fieldVec) ⬝ᵥ
        (f.pumpMatrix *ᵥ star (physRight (modalP f.rightVec fieldVec))) / 2‖ ^ 2 =
      ‖physLeft (modalQ f.leftVec fieldVec) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
        physRight (modalP f.rightVec fieldVec))‖ ^ 2 := by
    rw [hL, hR, f.shift_eq hν.ne' hω hH.ne', f.pump_eq hν.ne' hω, norm_sq_neg_sub,
      norm_sq_mul_I_half]
    have e : (f.ηh * f.ν / 2) ^ 2 / 4 - ((f.Dh / (4 * f.H)) ^ 2 + (f.dh * f.ν) ^ 2) =
        (f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2 - (f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2)) /
          (16 * f.H ^ 2) := by
      field_simp; ring
    rw [hb, sub_self, zero_div] at e
    linarith
  have h := PhysicalBoundary.physical_boundary hω2 hPQ hQP !![f.fieldPole] hA0 f.shiftMatrix
    f.pumpMatrix hs hb' hρ
  have hsh := BlockAveraging.shift_conj (modalP f.rightVec fieldVec)
    (modalQ f.leftVec fieldVec) f.shiftMatrix
  have hpu := BlockAveraging.pump_conj (modalP f.rightVec fieldVec)
    (modalQ f.leftVec fieldVec) f.pumpMatrix
  have e1 : -(physLeft (modalQ f.leftVec fieldVec) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
      physRight (modalP f.rightVec fieldVec))).re =
      0 - shiftRe (modalQ f.leftVec fieldVec * f.shiftMatrix * modalP f.rightVec fieldVec) := by
    rw [hsh]; simp
  have e2 : -(physLeft (modalQ f.leftVec fieldVec) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
      physRight (modalP f.rightVec fieldVec))).im =
      0 - shiftIm (modalQ f.leftVec fieldVec * f.shiftMatrix * modalP f.rightVec fieldVec) := by
    rw [hsh]; simp
  rw [e1, e2, ← hpu, mixedDet_effSecond 0 0 hω2 _ _ _ hρ, f.modalB_eq hν.ne' hω,
    f.modalA_eq hν.ne' hω] at h
  have hbt : (0 - shiftRe f.modalB) ^ 2 + (0 - shiftIm f.modalB) ^ 2 -
      ‖Element.pump f.modalA.toBlocks₁₁ TwoToOne.left TwoToOne.right / 2‖ ^ 2 = 0 := by
    rw [f.pump_modalA, norm_sq_mul_I_quarter, f.shift_modalB.1, f.shift_modalB.2]
    have e : (0 - -(f.Dh / (4 * f.H))) ^ 2 + (0 - -(f.dh * f.ν)) ^ 2 - (f.ηh * f.ν) ^ 2 / 16 =
        (f.Dh ^ 2 + 16 * f.H ^ 2 * f.dh ^ 2 * f.ν ^ 2 - f.H ^ 2 * f.ηh ^ 2 * f.ν ^ 2) /
          (16 * f.H ^ 2) := by
      field_simp; ring
    rw [e, hb, sub_self, zero_div]
  have hfm : blockMixed 0 0 (2 * f.ν) !![f.fieldPole] f.modalA f.modalB = f.fieldMixed := by
    rw [f.blockMixed_eq hν hH.ne' hτ, fieldMixed]
    have hH2 : f.H ^ 2 ≠ 0 := by positivity
    have hd : f.Dh ^ 2 / (16 * f.H ^ 2) = f.ηh ^ 2 * f.ν ^ 2 / 16 - f.dh ^ 2 * f.ν ^ 2 := by
      field_simp
      linear_combination hb
    rw [hd]
    ring
  rw [hbt, mul_zero, neg_zero, zero_add, hfm] at h
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · filter_upwards [h.1 (mul_pos hT hpos)] with ε hε
    rw [show (fun t => (f.machine ε t).stateMatrix) =
        physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
      funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
    exact hε
  · filter_upwards [h.2 (mul_neg_of_pos_of_neg hT hneg)] with ε hε
    rw [show (fun t => (f.machine ε t).stateMatrix) =
        physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
      funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
    exact hε

end Weak

/-! ## The driven-field family: the flux-decay torque at first order -/

@[tmio T, powerlib_foundation] private theorem re_quarter_star (c x y : ℝ) :
    ((c : ℂ) * I / 2 / 2 * star (⟨x, y⟩ : ℂ)).re = c * y / 4 := by
  simp [Complex.mul_re, Complex.mul_im]; ring

set_option maxHeartbeats 1000000 in
/-- **A core whose perturbation and modulation act through one equation.** In modal coordinates
with the pair block `B₁₁ = [[0, 0], [−2d, −2s]]`, the coupling `β = (0, b)ᵀ`, `γ = ρ(−2d, −2s)`,
`A₁₁ = [[0, 0], [a, 0]]`, `A₂₁ = ρ(a, 0)`, `A₁₂ = 0` and one real stable mode `l`:
`blockMixed = d(s² + d² − 3a²/32)/ν − 2bρl(s² + d² − a²/16)/(l² + ν²)`; the resolvent terms
are proportional to `s² + d² − |g/2|²` (`g = ja`) and vanish on the first-order boundary. -/
@[tmio T, powerlib_foundation] private theorem sameRow_blockMixed (s d a b ρ l ν : ℝ)
    (hν : 0 < ν) :
    blockMixed 0 0 (2 * ν) !![l]
        (fromBlocks !![0, 0; (a : ℂ), 0] 0 !![((ρ * a : ℝ) : ℂ), 0] 0)
        (fromBlocks !![0, 0; -(2 * d), -(2 * s)] !![0; b] !![-(2 * ρ * d), -(2 * ρ * s)]
          !![ρ * b]) =
      d * (s ^ 2 + d ^ 2 - 3 * a ^ 2 / 32) / ν -
        2 * b * ρ * l * (s ^ 2 + d ^ 2 - a ^ 2 / 16) / (l ^ 2 + ν ^ 2) := by
  set A : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ :=
    fromBlocks !![0, 0; (a : ℂ), 0] 0 !![((ρ * a : ℝ) : ℂ), 0] 0 with hA
  set B : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
    fromBlocks !![0, 0; -(2 * d), -(2 * s)] !![0; b] !![-(2 * ρ * d), -(2 * ρ * s)] !![ρ * b]
    with hB
  have hA12 : A.toBlocks₁₂ = 0 := toBlocks_fromBlocks₁₂ _ _ _ _
  have hup : upPlus A = 0 := by simp [upPlus, hA12]
  have hum : upMinus A = 0 := by simp [upMinus, hA12]
  have hre : A.toBlocks₂₁.map Complex.re = !![ρ * a, 0] := by
    ext i j; fin_cases i; fin_cases j <;> simp [hA]
  have him : A.toBlocks₂₁.map Complex.im = 0 := by
    ext i j; fin_cases i; fin_cases j <;> simp [hA]
  have hlm : lowMinus A = !![ρ * a / 2, 0] := by
    rw [lowMinus, hre, him, Matrix.zero_mul, sub_zero]
    ext i j; fin_cases i; fin_cases j <;> simp; ring
  have hD : l ^ 2 + ν ^ 2 ≠ 0 := by
    have : 0 < ν ^ 2 := by positivity
    positivity
  have hD' : l ^ 2 + (-ν) ^ 2 ≠ 0 := by rw [neg_sq]; exact hD
  have h2 : 2 * ν / 2 = ν := by ring
  have hP : couplingP !![l] A B (2 * ν) =
      B.toBlocks₁₂ * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν) := by
    rw [couplingP, hup, hum, h2, sylv_fin_one hD]
    simp
  have hN : couplingN !![l] A B (2 * ν) =
      B.toBlocks₁₂ * (!![ρ * a / 2, 0] * ThreeStateCore.lamInv l (-ν)) := by
    rw [couplingN, hup, hlm, h2, sylv_fin_one hD']
    simp
  have hpump : Element.pump A.toBlocks₁₁ TwoToOne.left TwoToOne.right = (a : ℂ) * I / 2 := by
    rw [TwoToOne.pump_base]; simp [hA]; ring
  have hanti : ‖SecondOrder.antiPump A.toBlocks₁₁‖ ^ 2 = a ^ 2 / 4 := by
    have h : SecondOrder.antiPump A.toBlocks₁₁ = -((a : ℂ) * I / 2) := by
      rw [SecondOrder.antiPump_eq]; simp [hA]; ring
    rw [h, norm_neg, Weak.norm_sq_mul_I_half]
  have hκ : fundSkew A.toBlocks₁₁ = ((a / 2 : ℝ) : ℂ) := by simp [fundSkew, hA]
  have hn : antiShift B.toBlocks₁₁ = ⟨s, -d⟩ := by
    apply Complex.ext <;> simp [antiShift, hB] <;> ring
  have hsr : shiftRe B = -s := by simp [shiftRe, hB]; ring
  have hsi : shiftIm B = -d := by simp [shiftIm, hB]; ring
  have hpc : projC (B.toBlocks₁₂ * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν)) =
      ⟨b * ρ * (d * ν - s * l) / (l ^ 2 + ν ^ 2),
        -(b * ρ * (d * l + s * ν) / (l ^ 2 + ν ^ 2))⟩ := by
    apply Complex.ext <;> simp only [projC] <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] <;>
      simp [hB, ThreeStateCore.lamInv, NormalForm.quarter] <;>
      field_simp <;> ring
  have hac : antiShift (B.toBlocks₁₂ * (!![ρ * a / 2, 0] * ThreeStateCore.lamInv l (-ν))) =
      ⟨-(b * ρ * a * ν / (4 * (l ^ 2 + ν ^ 2))), b * ρ * a * l / (4 * (l ^ 2 + ν ^ 2))⟩ := by
    apply Complex.ext <;> simp only [antiShift] <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] <;>
      simp [hB, ThreeStateCore.lamInv, NormalForm.quarter] <;>
      field_simp <;> ring
  rw [blockMixed, hP, hN, critMixed, hpc, Weak.re_mul_mk, hac, hpump, re_quarter_star, hanti,
    hκ, hn,
    Weak.re_crit, Weak.norm_sq_mk, hsr, hsi]
  field_simp
  ring

/-- The data of the driven-field family: the angle drives the field at order one (`K₄` fixed),
the field acts on the torque at order `ε` (`K₂ = εK̂₂`); damping `εD̂`, detuning `εd̂`, depth
`εη̂`. -/
structure Driven where
  H : ℝ
  ω₀ : ℝ
  ν : ℝ
  K₃ : ℝ
  K₄ : ℝ
  Td0 : ℝ
  Dh : ℝ
  K2h : ℝ
  dh : ℝ
  ηh : ℝ

namespace Driven

variable (f : Driven)

/-- The machine at `ε`: `K₁ = (2H/ω₀) ν² (1 − 2εd̂)`, `K₂ = εK̂₂`, `D = εD̂`, `K₃`, `K₄` fixed. -/
def params (ε : ℝ) : Params :=
  ⟨2 * f.H / f.ω₀ * f.ν ^ 2 * (1 - 2 * ε * f.dh), ε * f.K2h, f.K₃, f.K₄, f.H, ε * f.Dh, f.Td0,
    f.ω₀⟩

/-- The machine of the family at `ε` and time `t`, with
`K₁(t) = (2H/ω₀) ν² (1 − 2εd̂ + εη̂ cos 2νt)`. -/
def machine (ε t : ℝ) : Params :=
  { f.params ε with
    K₁ := 2 * f.H / f.ω₀ * f.ν ^ 2 * (1 - 2 * ε * f.dh + ε * f.ηh * Real.cos (2 * f.ν * t)) }

/-- The field time constant `τ = K₃T'_{d0}`. -/
def tau : ℝ := f.K₃ * f.Td0

/-- `m = 1 + ν²τ² = |1 + jντ|²`. -/
def mden : ℝ := 1 + f.ν ^ 2 * f.tau ^ 2

/-- The critical state matrix: the undamped swing pair `±jν` driving the field pole
`−1/(K₃T'_{d0})` through `K₄`. -/
def critMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, f.ω₀, 0; -(f.ν ^ 2 / f.ω₀), 0, 0; -(f.K₄ / f.Td0), 0, -1 / (f.K₃ * f.Td0)]

/-- The first-order change: detuning, damping and the torque of the field flux. -/
def shiftMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 2 * f.dh * f.ν ^ 2 / f.ω₀, -(f.Dh / (2 * f.H)), -(f.K2h / (2 * f.H)); 0, 0, 0]

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

/-- The right eigenvector of `jν`: `r = (1, jν/ω₀, −K₃K₄/(1 + jντ))`; the swing drives the field. -/
def rightVec : Fin 3 → ℂ :=
  ![1, ((f.ν / f.ω₀ : ℝ) : ℂ) * I,
    ((-(f.K₃ * f.K₄ / f.mden) : ℝ) : ℂ) + ((f.K₃ * f.K₄ * f.ν * f.tau / f.mden : ℝ) : ℂ) * I]

/-- The left eigenvector `u = (1/2, −jω₀/(2ν), 0)`, `u r = 1`. -/
def leftVec : Fin 3 → ℂ := ![1 / 2, -(((f.ω₀ / (2 * f.ν) : ℝ) : ℂ) * I), 0]

/-- The left eigenvector of the field pole, `ℓ = (K₃K₄/m, −ω₀τK₃K₄/m, 1)`, `ℓ e₃ = 1`. -/
def fieldLeft : Fin 3 → ℝ :=
  ![f.K₃ * f.K₄ / f.mden, -(f.ω₀ * f.tau * f.K₃ * f.K₄ / f.mden), 1]

/-- The field pole `λ₃ = −1/(K₃ T'_{d0})`. -/
def fieldPole : ℝ := -1 / (f.K₃ * f.Td0)

/-- The first-order damping of the swing pair, `s' = D̂/(4H) + ω₀K₃K₄K̂₂τ/(4Hm)`: mechanical
damping plus the damping torque of the flux decay. -/
def sD : ℝ := f.Dh / (4 * f.H) + f.ω₀ * f.K₃ * f.K₄ * f.K2h * f.tau / (4 * f.H * f.mden)

/-- The first-order detuning `d' = d̂ν + ω₀K₃K₄K̂₂/(4Hνm)`: the detuning of `K₁` plus the
(negative) synchronizing torque of the flux decay. -/
def dD : ℝ := f.dh * f.ν + f.ω₀ * f.K₃ * f.K₄ * f.K2h / (4 * f.H * f.ν * f.mden)

@[tmio M, powerlib_domain] private theorem mden_pos : 0 < f.mden := by
  rw [mden]; positivity

@[tmio M, powerlib_domain] private theorem rightVec_parts :
    ((f.rightVec 0).re = 1 ∧ (f.rightVec 0).im = 0) ∧
      ((f.rightVec 1).re = 0 ∧ (f.rightVec 1).im = f.ν / f.ω₀) ∧
      ((f.rightVec 2).re = -(f.K₃ * f.K₄ / f.mden) ∧
        (f.rightVec 2).im = f.K₃ * f.K₄ * f.ν * f.tau / f.mden) := by
  simp [rightVec, -Complex.ofReal_div, -Complex.ofReal_mul, -Complex.ofReal_neg]

@[tmio M, powerlib_domain] private theorem leftVec_parts :
    ((f.leftVec 0).re = 1 / 2 ∧ (f.leftVec 0).im = 0) ∧
      ((f.leftVec 1).re = 0 ∧ (f.leftVec 1).im = -(f.ω₀ / (2 * f.ν))) ∧
      ((f.leftVec 2).re = 0 ∧ (f.leftVec 2).im = 0) := by
  simp [leftVec, -Complex.ofReal_div]

@[tmio M, powerlib_domain] private theorem eigen (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    f.critMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec = ((f.ν : ℂ) * I) • f.rightVec ∧
      f.leftVec ᵥ* f.critMatrix.map (algebraMap ℝ ℂ) = ((f.ν : ℂ) * I) • f.leftVec ∧
      f.leftVec ⬝ᵥ f.rightVec = 1 ∧ f.critMatrix *ᵥ Weak.fieldVec = f.fieldPole • Weak.fieldVec ∧
      f.fieldLeft ᵥ* f.critMatrix = f.fieldPole • f.fieldLeft ∧
      f.fieldLeft ⬝ᵥ Weak.fieldVec = 1 := by
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
      simp only [mden, tau] at * <;> field_simp <;> ring
  · funext i; fin_cases i <;> apply Complex.ext <;>
      simp [critMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Complex.mul_re,
        Complex.mul_im, l0, l0', l1, l1', l2, l2', -Complex.ofReal_div, -Complex.ofReal_mul,
        -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_inv] <;> field_simp
  · apply Complex.ext <;>
      simp [dotProduct, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, r0, r0', r1, r1', r2,
        r2', l0, l0', l1, l1', l2, l2'] <;> field_simp <;> ring
  · funext i; fin_cases i <;>
      simp [critMatrix, Weak.fieldVec, fieldPole, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · funext i; fin_cases i <;>
      simp [critMatrix, fieldLeft, fieldPole, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
      simp only [mden, tau] at * <;> field_simp <;> ring
  · simp [fieldLeft, Weak.fieldVec, dotProduct, Fin.sum_univ_three]

/-- **The modal form of the driven-field family** (`P = [Re r, −Im r, e₃]`,
`Q = [2 Re u; 2 Im u; ℓ]`). -/
@[tmio M, powerlib_domain] theorem modal (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0)
    (hτ : 0 < f.K₃ * f.Td0) :
    modalQ f.leftVec f.fieldLeft * modalP f.rightVec Weak.fieldVec = 1 ∧
      modalP f.rightVec Weak.fieldVec * modalQ f.leftVec f.fieldLeft = 1 ∧
      modalQ f.leftVec f.fieldLeft * f.critMatrix * modalP f.rightVec Weak.fieldVec =
        fromBlocks (TwoToOne.base 0 f.ν) 0 0 !![f.fieldPole] ∧
      physLeft (modalQ f.leftVec f.fieldLeft) = f.leftVec ∧
      physRight (modalP f.rightVec Weak.fieldVec) = f.rightVec := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν hω hτ
  exact BlockAveraging.modal_three hν h1 h2 h3 h4 h5 h6

/-- The first-order eigenvalue shift `λ₁ = −s' − j d'`: the damping and synchronizing torque of
the flux decay at the oscillation frequency enter at first order. -/
@[tmio M, powerlib_domain] theorem shift_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0) :
    f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec) =
      -(f.sD : ℂ) - (f.dD : ℂ) * I := by
  have hm := f.mden_pos.ne'
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  apply Complex.ext <;>
    simp [shiftMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.mul_re,
      Complex.mul_im, r0, r0', r1, r1', r2, r2', l1, l1', sD, dD, -Complex.ofReal_div,
      -Complex.ofReal_mul, -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_inv] <;>
    field_simp <;> ring

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

/-- **First-order threshold of the driven-field family, stability.** For `s' > 0` and
`(η̂ν)²/16 < s'² + d'²` every Floquet multiplier lies inside the unit circle for all small
`ε > 0`. -/
@[tmio M, powerlib_domain] theorem firstOrder_stable (hH : 0 < f.H) (hω : f.ω₀ ≠ 0)
    (hν : 0 < f.ν) (hτ : 0 < f.K₃ * f.Td0) (hs : 0 < f.sD)
    (hg : (f.ηh * f.ν) ^ 2 / 16 < f.sD ^ 2 + f.dD ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
      (Periodic.monodromy (fun t => (f.machine ε t).stateMatrix) (2 * Real.pi / (2 * f.ν)) 0).map
          (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν.ne' hω hτ
  have hs' : (f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)).re < 0 := by
    rw [f.shift_eq hν.ne' hω hH.ne', Weak.re_neg_sub]; linarith
  have hg' : ‖f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) / 2‖ ^ 2 <
      ‖f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)‖ ^ 2 := by
    rw [f.shift_eq hν.ne' hω hH.ne', f.pump_eq hν.ne' hω, Weak.norm_sq_neg_sub,
      Weak.norm_sq_mul_I_half]
    have : (f.ηh * f.ν / 2) ^ 2 / 4 = (f.ηh * f.ν) ^ 2 / 16 := by ring
    linarith
  have h := BlockAveraging.three_stable hν (f.fieldPole_neg hτ) h1 h2 h3 h4 h5 h6 f.shiftMatrix
    f.pumpMatrix hs' hg'
  filter_upwards [h] with ε hε
  rw [show (fun t => (f.machine ε t).stateMatrix) =
      physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
    funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
  exact hε

/-- **First-order threshold of the driven-field family, parametric instability**:
`s'² + d'² < (η̂ν)²/16` gives Floquet instability for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem firstOrder_unstable (hH : 0 < f.H) (hω : f.ω₀ ≠ 0)
    (hν : 0 < f.ν) (hτ : 0 < f.K₃ * f.Td0) (hg : f.sD ^ 2 + f.dD ^ 2 < (f.ηh * f.ν) ^ 2 / 16) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (fun t => (f.machine ε t).stateMatrix)
      (2 * Real.pi / (2 * f.ν)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f.eigen hν.ne' hω hτ
  have hg' : ‖f.leftVec ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ f.rightVec)‖ ^ 2 <
      ‖f.leftVec ⬝ᵥ (f.pumpMatrix *ᵥ star f.rightVec) / 2‖ ^ 2 := by
    rw [f.shift_eq hν.ne' hω hH.ne', f.pump_eq hν.ne' hω, Weak.norm_sq_neg_sub,
      Weak.norm_sq_mul_I_half]
    have : (f.ηh * f.ν / 2) ^ 2 / 4 = (f.ηh * f.ν) ^ 2 / 16 := by ring
    linarith
  have h := BlockAveraging.three_unstable hν (f.fieldPole_neg hτ) h1 h2 h3 h4 h5 h6 f.shiftMatrix
    f.pumpMatrix hg'
  filter_upwards [h] with ε hε
  rw [show (fun t => (f.machine ε t).stateMatrix) =
      physJ f.critMatrix f.shiftMatrix f.pumpMatrix (2 * f.ν) ε from
    funext fun t => f.machine_stateMatrix hH.ne' hω ε t]
  exact hε

/-- The field-to-pair coupling `b = ω₀K̂₂/(2Hν)` and the pair-to-field gain `ρ = K₃K₄ντ/m` in
modal coordinates. -/
def coupB : ℝ := f.ω₀ * f.K2h / (2 * f.H * f.ν)

/-- `ρ = K₃K₄ντ/m`. -/
def coupRho : ℝ := f.K₃ * f.K₄ * f.ν * f.tau / f.mden

@[tmio M, powerlib_domain] theorem modalB_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) (hH : f.H ≠ 0) :
    modalQ f.leftVec f.fieldLeft * f.shiftMatrix * modalP f.rightVec Weak.fieldVec =
      fromBlocks !![0, 0; -(2 * f.dD), -(2 * f.sD)] !![0; f.coupB]
        !![-(2 * f.coupRho * f.dD), -(2 * f.coupRho * f.sD)] !![f.coupRho * f.coupB] := by
  have hm := f.mden_pos.ne'
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [modalQ, modalP, Weak.fieldVec, fieldLeft, shiftMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, r0, r0', r1, r1', r2, r2', l0, l0', l1, l1', l2, l2', sD, dD, coupB,
      coupRho] <;> field_simp <;> ring

@[tmio M, powerlib_domain] theorem modalA_eq (hν : f.ν ≠ 0) (hω : f.ω₀ ≠ 0) :
    (modalQ f.leftVec f.fieldLeft).map (algebraMap ℝ ℂ) * f.pumpMatrix *
        (modalP f.rightVec Weak.fieldVec).map (algebraMap ℝ ℂ) =
      fromBlocks !![0, 0; ((f.ηh * f.ν : ℝ) : ℂ), 0] 0
        !![((f.coupRho * (f.ηh * f.ν) : ℝ) : ℂ), 0] 0 := by
  have hm := f.mden_pos.ne'
  have hν' : (f.ν : ℂ) ≠ 0 := by exact_mod_cast hν
  have hω' : (f.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω
  obtain ⟨⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩⟩ := f.rightVec_parts
  obtain ⟨⟨l0, l0'⟩, ⟨l1, l1'⟩, ⟨l2, l2'⟩⟩ := f.leftVec_parts
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [modalQ, modalP, Weak.fieldVec, fieldLeft, pumpMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, r0, r0', r1, r1', r2, r2', l0, l0', l1, l1', l2, l2', coupRho] <;>
    field_simp

set_option maxHeartbeats 1000000 in
/-- **The driven-field family on its first-order boundary, decided at second order.** On the
boundary `s'² + d'² = (η̂ν)²/16` with `s' > 0` (`s' = sD`, `d' = dD`, the slow-flow damping and
detuning with the flux-decay torque included): for all small `ε > 0`, `d' < 0` puts every Floquet
multiplier inside the unit circle and `d' > 0` gives Floquet instability. The resolvent terms of
the field mode (`(λ₃ ∓ jν)⁻¹`, through the constant and the modulated coupling of the field) are
proportional to `s'² + d'² − |g/2|²` and cancel exactly on the boundary: beyond its first-order
torque the field mode does not move the boundary at second order, and the verdict is the
Mathieu-type sign of `−d'`. -/
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
  obtain ⟨hQP, hPQ, hQAP, hL, hR⟩ := f.modal hν.ne' hω hτ
  have hω2 : 0 < 2 * f.ν := by linarith
  have hT : 0 < 2 * Real.pi / (2 * f.ν) := by positivity
  have hA0 : modalQ f.leftVec f.fieldLeft * f.critMatrix * modalP f.rightVec Weak.fieldVec =
      fromBlocks (TwoToOne.base 0 (2 * f.ν / 2)) 0 0 !![f.fieldPole] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hρ : spectralRadius ℂ ((expS (!![f.fieldPole] : Matrix (Fin 1) (Fin 1) ℝ)
      (2 * Real.pi / (2 * f.ν))).map (algebraMap ℝ ℂ)) < 1 := by
    have hq :
        ‖expS (!![f.fieldPole] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * f.ν))‖ < 1 := by
      rw [BlockAveraging.norm_expS_one, Real.exp_lt_one_iff]
      exact mul_neg_of_pos_of_neg hT (f.fieldPole_neg hτ)
    exact BlockAveraging.spectralRadius_lt_one_of_norm _ hq
  have hs' : (physLeft (modalQ f.leftVec f.fieldLeft) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
      physRight (modalP f.rightVec Weak.fieldVec))).re < 0 := by
    rw [hL, hR, f.shift_eq hν.ne' hω hH.ne', Weak.re_neg_sub]; linarith
  have hb' : ‖physLeft (modalQ f.leftVec f.fieldLeft) ⬝ᵥ
        (f.pumpMatrix *ᵥ star (physRight (modalP f.rightVec Weak.fieldVec))) / 2‖ ^ 2 =
      ‖physLeft (modalQ f.leftVec f.fieldLeft) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
        physRight (modalP f.rightVec Weak.fieldVec))‖ ^ 2 := by
    rw [hL, hR, f.shift_eq hν.ne' hω hH.ne', f.pump_eq hν.ne' hω, Weak.norm_sq_neg_sub,
      Weak.norm_sq_mul_I_half, hb]
    ring
  have h := PhysicalBoundary.physical_boundary hω2 hPQ hQP !![f.fieldPole] hA0 f.shiftMatrix
    f.pumpMatrix hs' hb' hρ
  have hsh := BlockAveraging.shift_conj (modalP f.rightVec Weak.fieldVec)
    (modalQ f.leftVec f.fieldLeft) f.shiftMatrix
  have hpu := BlockAveraging.pump_conj (modalP f.rightVec Weak.fieldVec)
    (modalQ f.leftVec f.fieldLeft) f.pumpMatrix
  have e1 : -(physLeft (modalQ f.leftVec f.fieldLeft) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
      physRight (modalP f.rightVec Weak.fieldVec))).re =
      0 - shiftRe (modalQ f.leftVec f.fieldLeft * f.shiftMatrix *
        modalP f.rightVec Weak.fieldVec) := by
    rw [hsh]; simp
  have e2 : -(physLeft (modalQ f.leftVec f.fieldLeft) ⬝ᵥ (f.shiftMatrix.map (algebraMap ℝ ℂ) *ᵥ
      physRight (modalP f.rightVec Weak.fieldVec))).im =
      0 - shiftIm (modalQ f.leftVec f.fieldLeft * f.shiftMatrix *
        modalP f.rightVec Weak.fieldVec) := by
    rw [hsh]; simp
  rw [e1, e2, ← hpu, mixedDet_effSecond 0 0 hω2 _ _ _ hρ, f.modalB_eq hν.ne' hω hH.ne',
    f.modalA_eq hν.ne' hω, sameRow_blockMixed _ _ _ _ _ _ _ hν] at h
  have hsr : shiftRe (fromBlocks !![0, 0; -(2 * f.dD), -(2 * f.sD)] !![0; f.coupB]
      !![-(2 * f.coupRho * f.dD), -(2 * f.coupRho * f.sD)] !![f.coupRho * f.coupB]) = -f.sD := by
    simp [shiftRe]; ring
  have hsi : shiftIm (fromBlocks !![0, 0; -(2 * f.dD), -(2 * f.sD)] !![0; f.coupB]
      !![-(2 * f.coupRho * f.dD), -(2 * f.coupRho * f.sD)] !![f.coupRho * f.coupB]) = -f.dD := by
    simp [shiftIm]; ring
  have hpump : Element.pump (fromBlocks !![0, 0; ((f.ηh * f.ν : ℝ) : ℂ), 0] 0
      !![((f.coupRho * (f.ηh * f.ν) : ℝ) : ℂ), 0] 0 : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ
        ).toBlocks₁₁ TwoToOne.left TwoToOne.right = ((f.ηh * f.ν : ℝ) : ℂ) * I / 2 := by
    rw [TwoToOne.pump_base]; simp; try ring
  rw [hsr, hsi, hpump, Weak.norm_sq_mul_I_quarter, sub_neg_eq_add, zero_add, zero_sub, neg_neg, hb,
    sub_self, mul_zero, neg_zero, zero_add] at h
  have hab : 0 < (f.ηh * f.ν) ^ 2 := by
    have : 0 < f.sD ^ 2 := by positivity
    nlinarith [sq_nonneg f.dD]
  have hval : f.dD * ((f.ηh * f.ν) ^ 2 / 16 - 3 * (f.ηh * f.ν) ^ 2 / 32) / f.ν -
      2 * f.coupB * f.coupRho * f.fieldPole * 0 / (f.fieldPole ^ 2 + f.ν ^ 2) =
        -(f.dD * (f.ηh * f.ν) ^ 2 / (32 * f.ν)) := by
    field_simp; ring
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

end Driven

end powerlib.Synchronous.FluxDecayParametric
