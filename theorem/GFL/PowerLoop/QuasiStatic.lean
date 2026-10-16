import theorem.Dynamics.Locality
import theorem.Criteria.Routh3
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Coordinates
import theorem.Spectral.Local
import theorem.Dynamics.Pendulum
import theorem.Dynamics.Transport
import theorem.SpecialFunctions.Sinusoid

/-! # Quasi-static three-state GFL: PLL + active-power dispatch loop

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold: `theorem/CurrentDirection.agda`.

Model boundary.
Single grid-following converter on an infinite bus of amplitude `V`
behind a lossless reactance `X_g`; three-phase balanced averaged dq model in the PLL frame,
algebraic (quasi-static) network, continuous time.
* States, in order: `θ` (PLL error angle), `x` (PLL integrator), `i_d` (d-axis current, into the
  converter).
* Power from `S̄ = V̄ Ī*` with `V̄ = v_d + j v_q`, `Ī = i_d + j 0` (`I_q = 0`, amplitude-invariant
  Park): `P = (3/2) Re(V̄ Ī*) = (3/2) v_d i_d`, the power absorbed by the converter. The reference
  `P_ref` is absorbed-positive as well: an exporting converter has `P_ref < 0`, `i_d < 0`.
* Network `v_pcc = v_g − j X_g i`: `v_q = −V sin θ − X_g i_d`, `v_d = V cos θ`; SRF-PLL
  `θ̇ = k_p v_q + k_i x`, `ẋ = v_q`; outer active-power loop (pure integral dispatch)
  `i̇_d = k_P (P_ref − P)`.
* Ideal current loop, no line dynamics, no line resistance, no dc link, no PWM, delay or
  limiter.  Results are at the equilibrium (linearization) level.

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (差别二 `P_SN = 3V_g²/(4X_g)`, 折叠角 45°;
推论二 准静态无 Hopf); model `GFLQuasiStatic` in `.../archive/simulation/src/
gfl_gfm_contrast_sim/models.py` (with `I_q = 0`). The source writes the model OUT-positive
(`I_d = −i_d`, converter → grid) with export-positive power and reference
(`P_exp = −P`, `P_ref,exp = −P_ref`); that form is `literatureField`, read through the current
reversal by `field_eq_transport_literatureField` (conventions §D8).

Results.
* `equilibrium_exists_iff`: an equilibrium exists iff `|P_ref| ≤ 3V²/(4X_g)`; the absorbed power
  curve is `P(θ) = −(3V²/(4X_g)) sin 2θ` (`power_of_isEq`), so the exported power `−P` is
  maximal exactly at the fold angle `θ = π/4` on the branch `|θ| < π/2` (`power_eq_PSN_iff`).
* `field_eq_transport_literatureField` (§D8 boundary translation): the field is the OUT-positive
  source field transported by the reversal `diag(1, 1, −1)` of the current coordinate, with the
  reference reversed.
* Characteristic polynomial of the Jacobian (derived with `fderiv`):
  `s³ + a₂ s² + a₁ s + a₀`, `a₂ = (V cos θ/2)(3k_P + 2k_p)`,
  `a₁ = (V/2)(3V k_P k_p cos 2θ + 2k_i cos θ)`, `a₀ = (3/2)V² k_P k_i cos 2θ`, and
  `a₂a₁ − a₀ =`
  `(V²/4)[(9V k_P² k_p + 6V k_P k_p²) cos θ cos 2θ + 4k_i k_p cos² θ + 6k_P k_i sin² θ]`.
* "No-Hopf theorem" (exact form): for all positive gains, `cos θ > 0`:
  `cos 2θ > 0` (i.e. `|θ| < 45°`) ⇒ locally exponentially stable;
  `cos 2θ < 0` (`45° < |θ| < 90°`) ⇒ a positive real eigenvalue, unstable;
  and the Jacobian never has a nonzero purely imaginary eigenvalue (`no_imaginary_eigenvalue`),
  so the equilibrium branch cannot lose stability through a Hopf pair.  Only this three-state
  model is covered; the generalisations claimed in the source (PI outer loop, resistance,
  normalised PLL) are not formalized.

Family and connection conclusions.
A complete system (`Model`) is a parameter set with a
selected operating point `(θ*, 0, i_d*)`; the system map reads it as the field translated so that
this point is the origin, `z ↦ field p (z + point θ* i_d*)` (every flow sentence is invariant
under this translation, `Flow.Property.holds_shift_iff`). The requirement language is static:
the point is an equilibrium (`IsEq p θ* i_d*`); the closed-form Jacobian `jac p θ* i_d*` (proved
to be the `fderiv`) satisfies the strict 3×3 Routh–Hurwitz conditions (`tr < 0`, `det < 0`,
`tr · m₂ < det`); or it has `det > 0` or `tr > 0`; and the context requirement `positiveGains`
(`k_p, k_i, k_P > 0`), into which no sentence is translated. The local sentences translate into the
first two, instability into the first and the third, passivity into nothing, and the global
sentences, decay rates, sampled contraction and conservation into the whole (inconsistent) language:
unavailable translation coverage. `chain_le_semantics` proves every translation sound;
`exact_passive` proves the passivity translation exact. The stability results are connection
memberships (`mem_den_locallyExponentiallyStable_of_cos_two_mul_pos`, `…_of_abs_lt`,
`mem_den_unstable_of_cos_two_mul_neg`, `…_of_pi_div_four_lt`, with
`not_mem_den_lyapunovStable_of_cos_two_mul_neg`); `equilibrium_exists_iff` is static evidence on the
model. The local exponential translation is exact (`exact_locallyExponentiallyStable`): by the
converse linearization theorem (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`) local
exponential stability of the selected point holds exactly when it is an equilibrium with a Hurwitz
Jacobian (the strict 3×3 Routh–Hurwitz conditions; a Hurwitz Jacobian has `k_P ≠ 0`, so the field's
equilibrium is an `IsEq` point). The instability translation is not exact (`not_exact_unstable`):
instability is the failure of Lyapunov stability, so a model whose selected point is not an
equilibrium (`offEquilibrium`) is unstable (`offEquilibrium_mem_den_unstable`). The Lyapunov
translation is not exact (`not_exact_lyapunovStable`): the undamped PLL with a frozen dispatch loop
`undampedPLL` (`k_p = k_P = 0`) is Lyapunov stable through the conserved energy
`1 − cos θ + x²/2 + i_d²/2` (`undampedPLL_mem_den_lyapunovStable`) with a trace-zero Jacobian. The
local asymptotic translation is not exact for gains of arbitrary sign
(`not_exact_locallyAsymptoticallyStable`, in `theorem/GFL/PowerLoop/QuasiStaticFoldHopf.lean`): the
witness `supercriticalQS` (`k_p = −1/4 < 0`) sits on the Hopf boundary `a₂a₁ = a₀` with eigenvalues
`±3i`, `−7/2` and is locally asymptotically stable (a supercritical weak focus, decided by an
explicit normal-form polynomial). Within positive gains both the local asymptotic and the Lyapunov
translations are exact (`exactUnder_locallyAsymptoticallyStable`, `exactUnder_lyapunovStable`, in
`theorem/GFL/PowerLoop/QuasiStaticFold.lean`): the boundary of the Routh–Hurwitz region is the fold
`cos 2θ* = 0` (no Hopf pair, `no_imaginary_eigenvalue`), a saddle-node that is unstable
(`mem_den_unstable_of_fold`, explicit fold function, no centre-manifold theorem), and every other
non-Hurwitz point with positive gains is unstable as well.

Correction: the source states the no-Hopf criterion as `cos θ_e / √(cos 2θ_e) ≥ 1`; the
formal statement used here is the direct one (`a₂a₁ − a₀ > 0` on `cos 2θ ≥ 0`, `a₀ < 0` on
`cos 2θ < 0`), valid for every positive gain triple.
-/

noncomputable section
namespace powerlib.GFL.PowerLoop.QuasiStatic
open Matrix

/-- Parameters of the quasi-static three-state GFL model. -/
structure Params where
  /-- grid voltage amplitude -/
  V : ℝ
  /-- grid reactance -/
  Xg : ℝ
  /-- PLL proportional gain -/
  kp : ℝ
  /-- PLL integral gain -/
  ki : ℝ
  /-- dispatch-loop integral gain -/
  kP : ℝ
  /-- active-power reference (absorbed-positive) -/
  Pref : ℝ

variable (p : Params)

/-- q-axis PCC voltage `v_q = −V sin θ − X_g i_d` (`v_pcc = v_g − j X_g i`, `i` IN-positive) -/
def vq (θ Id : ℝ) : ℝ := -p.V * Real.sin θ - p.Xg * Id

/-- absorbed active power `(3/2) Re(V̄ Ī*) = (3/2) v_d i_d` with `I_q = 0` -/
def power (θ Id : ℝ) : ℝ := 3 / 2 * (p.V * Real.cos θ) * Id

/-- Coordinate field, state `(θ, x, i_d)`. -/
def coordField (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p.kp * vq p (y 0) (y 2) + p.ki * y 1, vq p (y 0) (y 2), p.kP * (p.Pref - power p (y 0) (y 2))]

/-- The nonlinear three-state field. -/
def field : Dynamics.State 3 → Dynamics.State 3 := Dynamics.lift (coordField p)

/-- The state `(θ, 0, i_d)`. -/
def point (θ Id : ℝ) : Dynamics.State 3 := WithLp.toLp 2 ![θ, 0, Id]

/-- Equilibrium conditions at `(θ, 0, i_d)`: `−X_g i_d = V sin θ`, `P_ref = P`. -/
def IsEq (θ Id : ℝ) : Prop := -(p.Xg * Id) = p.V * Real.sin θ ∧ p.Pref = power p θ Id

/-- Closed-form Jacobian at `(θ, x, i_d)`. -/
def jac (θ Id : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-p.kp * p.V * Real.cos θ, p.ki, -(p.kp * p.Xg);
     -p.V * Real.cos θ, 0, -p.Xg;
     3 / 2 * p.kP * p.V * Real.sin θ * Id, 0, -(3 / 2) * p.kP * p.V * Real.cos θ]

/-- Transmission limit `P_SN = 3V²/(4X_g)`. -/
def PSN : ℝ := 3 * p.V ^ 2 / (4 * p.Xg)

@[powerlib_foundation] theorem field_point_eq_zero {θ Id : ℝ} (h : IsEq p θ Id) :
    field p (point θ Id) = 0 := by
  obtain ⟨h1, h2⟩ := h
  have hq : vq p θ Id = 0 := by unfold vq; linarith
  apply Dynamics.lift_toLp_eq_zero
  ext i
  fin_cases i <;> simp [coordField, hq, ← h2]

@[powerlib_foundation] theorem contDiff_field : ContDiff ℝ 1 (field p) := by
  apply Dynamics.contDiff_lift
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [coordField, vq, power] <;> fun_prop

@[powerlib_foundation] theorem hasFDerivAt_coordField (y : Fin 3 → ℝ) :
    HasFDerivAt (coordField p) (Matrix.toLin' (jac p (y 0) (y 2))).toContinuousLinearMap y := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) y
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) y
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) y
  have hq := (h0.sin.const_mul (-p.V)).sub (h2.const_mul p.Xg)
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine Dynamics.hasFDerivAt_of_eq ((hq.const_mul p.kp).add (h1.const_mul p.ki))
      (fun z => by simp [coordField, vq]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_three]
    ring
  · refine Dynamics.hasFDerivAt_of_eq hq (fun z => by simp [coordField, vq]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_three]
    ring
  · have hP := (((h0.cos.const_mul p.V).const_mul (3 / 2)).mul h2)
    refine Dynamics.hasFDerivAt_of_eq ((hP.const_sub p.Pref).const_mul p.kP)
      (fun z => by simp [coordField, power]) ?_
    ext v
    simp [jac, dotProduct, Fin.sum_univ_three]
    ring

@[powerlib_foundation] theorem fderiv_field (θ x Id : ℝ) :
    fderiv ℝ (field p) (WithLp.toLp 2 ![θ, x, Id]) =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (jac p θ Id) := by
  have := hasFDerivAt_coordField p ![θ, x, Id]
  exact Dynamics.fderiv_lift (by simpa using this)

/-! ## The OUT-positive form of the source (conventions §D8) -/

/-- The OUT-positive form of the source model `GFLQuasiStatic` (work-sync conventions §D8): state
`(θ, x, I_d)` with the current `I_d = −i_d` flowing converter → grid and `p.Pref` read as the
exported power reference; `v_q = −V sin θ + X_g I_d`, `P_exp = (3/2) V cos θ I_d`,
`İ_d = k_P (P_ref,exp − P_exp)`. A static definition only: the family reads `field`. -/
def literatureField : Dynamics.State 3 → Dynamics.State 3 :=
  Dynamics.lift fun y => ![p.kp * (-p.V * Real.sin (y 0) + p.Xg * y 2) + p.ki * y 1,
    -p.V * Real.sin (y 0) + p.Xg * y 2, p.kP * (p.Pref - 3 / 2 * (p.V * Real.cos (y 0)) * y 2)]

/-- The reversal `diag(1, 1, −1)` of the current coordinate. -/
def currentReversal : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, -1]

@[powerlib_foundation] theorem currentReversal_mul_self :
    currentReversal * currentReversal = 1 := by
  rw [currentReversal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> norm_num

@[powerlib_foundation] theorem currentReversal_isUnit : IsUnit currentReversal :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse currentReversal_mul_self)

/-- §D8 boundary translation: the IN-positive field is the OUT-positive source field transported
by the reversal of the current coordinate (`i_d = −I_d`), with the power reference reversed
(`P_ref = −P_ref,exp`); the dispatch law keeps its form since both sides of `İ_d = k_P(P_ref − P)`
change sign. -/
@[powerlib_foundation] theorem field_eq_transport_literatureField :
    field p = Dynamics.transportField (Dynamics.matrixCoord currentReversal currentReversal_isUnit)
      0 (literatureField { p with Pref := -p.Pref }) := by
  have hinv : currentReversal⁻¹ = currentReversal :=
    Matrix.inv_eq_left_inv currentReversal_mul_self
  funext y
  apply WithLp.ofLp_injective
  ext i
  simp only [Dynamics.transportField, sub_zero, Dynamics.ofLp_matrixCoord,
    Dynamics.matrixCoord_symm_apply, hinv]
  fin_cases i <;>
    simp [field, literatureField, Dynamics.lift, coordField, vq, power, currentReversal,
      Matrix.mulVec_diagonal, -mul_eq_mul_left_iff] <;> ring

/-! ## Equilibria and the transmission limit -/

@[powerlib_foundation] theorem power_of_isEq {θ Id : ℝ} (hX : p.Xg ≠ 0)
    (h : -(p.Xg * Id) = p.V * Real.sin θ) :
    power p θ Id = -(PSN p * Real.sin (2 * θ)) := by
  have hId : Id = -(p.V * Real.sin θ / p.Xg) := by field_simp; linarith
  rw [power, PSN, hId, Real.sin_two_mul]
  field_simp
  ring

/-- Quasi-static GFL: an equilibrium exists iff `|P_ref| ≤ 3V²/(4X_g)` (for either sign of the
absorbed reference; the zeros of the sinusoid `−P_ref − P_SN sin 2θ`,
`SpecialFunctions.exists_sinusoid_zero_iff`).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem equilibrium_exists_iff (hX : 0 < p.Xg)
    (hkP : p.kP ≠ 0) :
    (∃ z : Dynamics.State 3, field p z = 0) ↔ |p.Pref| ≤ PSN p := by
  have hPSN : 0 ≤ PSN p := by unfold PSN; positivity
  constructor
  · rintro ⟨z, hz⟩
    have hc : ∀ i, coordField p (WithLp.ofLp z) i = 0 := by
      intro i
      have := congrArg (fun w : Dynamics.State 3 => w i) hz
      simpa [field, Dynamics.lift] using this
    have hq : vq p (z 0) (z 2) = 0 := by simpa [coordField] using hc 1
    have hP : p.Pref = power p (z 0) (z 2) := by
      have := hc 2
      simp [coordField] at this
      rcases this with h | h
      · exact absurd h hkP
      · linarith
    have hXI : -(p.Xg * z 2) = p.V * Real.sin (z 0) := by unfold vq at hq; linarith
    rw [hP, power_of_isEq p hX.ne' hXI, abs_neg, abs_mul, abs_of_nonneg hPSN]
    exact mul_le_of_le_one_right hPSN (Real.abs_sin_le_one _)
  · intro h
    by_cases h0 : PSN p = 0
    · have hP0 : p.Pref = 0 := by rw [h0] at h; exact abs_nonpos_iff.mp h
      refine ⟨point 0 0, field_point_eq_zero p ⟨by simp, by simp [power, hP0]⟩⟩
    · -- a zero `φ` of the sinusoid `−P_ref − P_SN sin φ` gives the angle `θ = φ/2`
      obtain ⟨φ, hφ⟩ := (SpecialFunctions.exists_sinusoid_zero_iff (φ := 0)
        (lt_of_le_of_ne hPSN (Ne.symm h0))).mpr (by rwa [abs_neg])
      have hXI : -(p.Xg * -(p.V * Real.sin (φ / 2) / p.Xg)) = p.V * Real.sin (φ / 2) := by
        field_simp
      refine ⟨point (φ / 2) (-(p.V * Real.sin (φ / 2) / p.Xg)), field_point_eq_zero p ⟨hXI, ?_⟩⟩
      rw [power_of_isEq p hX.ne' hXI, show 2 * (φ / 2) = φ + 0 by ring]
      linarith

/-- On the branch `|θ| < π/2` the exported power `−P = P_SN sin 2θ` (`power_of_isEq`) reaches
`P_SN` exactly at the fold angle `θ = π/4`. -/
@[powerlib_foundation] theorem power_eq_PSN_iff (hX : 0 < p.Xg) (hV : p.V ≠ 0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    PSN p * Real.sin (2 * θ) = PSN p ↔ θ = Real.pi / 4 := by
  have hpos : 0 < PSN p := by unfold PSN; positivity
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  constructor
  · intro h
    have h1 : Real.sin (2 * θ) = 1 := by
      have := mul_left_cancel₀ hpos.ne' (h.trans (mul_one _).symm)
      exact this
    rw [Real.sin_two_mul] at h1
    have hsc : Real.sin θ = Real.cos θ := by
      have := Real.sin_sq_add_cos_sq θ
      nlinarith [sq_nonneg (Real.sin θ - Real.cos θ)]
    have htan : Real.tan θ = 1 := by
      rw [Real.tan_eq_sin_div_cos, hsc, div_self hcos.ne']
    rw [← Real.arctan_tan hθ.1 hθ.2, htan, Real.arctan_one]
  · rintro rfl
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two, mul_one]

/-! ## Characteristic polynomial -/

/-- `a₂ = (V cos θ/2)(3k_P + 2k_p)` -/
def a2 (θ : ℝ) : ℝ := p.V * Real.cos θ / 2 * (3 * p.kP + 2 * p.kp)

/-- `a₁ = (V/2)(3V k_P k_p cos 2θ + 2k_i cos θ)` -/
def a1 (θ : ℝ) : ℝ :=
  p.V / 2 * (3 * p.V * p.kP * p.kp * Real.cos (2 * θ) + 2 * p.ki * Real.cos θ)

/-- `a₀ = (3/2)V² k_P k_i cos 2θ` -/
def a0 (θ : ℝ) : ℝ := 3 / 2 * p.V ^ 2 * p.kP * p.ki * Real.cos (2 * θ)

@[powerlib_foundation] theorem trace_jac (θ Id : ℝ) : (jac p θ Id).trace = -a2 p θ := by
  simp [jac, Matrix.trace_fin_three, a2]
  ring

@[powerlib_foundation] theorem principalMinorSum_jac {θ Id : ℝ}
    (h : -(p.Xg * Id) = p.V * Real.sin θ) : Criteria.principalMinorSum (jac p θ Id) = a1 p θ := by
  simp [jac, Criteria.principalMinorSum, a1, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination (-(3 / 2) * p.kp * p.kP * p.V * Real.sin θ) * h +
    (-(3 / 2) * p.kp * p.kP * p.V ^ 2) * this

@[powerlib_foundation] theorem det_jac {θ Id : ℝ} (h : -(p.Xg * Id) = p.V * Real.sin θ) :
    (jac p θ Id).det = -a0 p θ := by
  simp [jac, Matrix.det_fin_three, a0, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination (3 / 2 * p.ki * p.kP * p.V * Real.sin θ) * h +
    (3 / 2 * p.ki * p.kP * p.V ^ 2) * this

/-- The characteristic polynomial of the Jacobian at an equilibrium. -/
@[powerlib_foundation] theorem det_characteristicMatrix_jac {θ Id : ℝ}
    (h : -(p.Xg * Id) = p.V * Real.sin θ) (s : ℂ) :
    (Linear.characteristicMatrix (jac p θ Id) s).det =
      s ^ 3 + (a2 p θ : ℂ) * s ^ 2 + (a1 p θ : ℂ) * s + (a0 p θ : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_three, trace_jac, principalMinorSum_jac p h,
    det_jac p h]
  push_cast
  ring

/-- The Hurwitz-determinant identity of the source. -/
@[powerlib_foundation] theorem a2_mul_a1_sub_a0 (θ : ℝ) :
    a2 p θ * a1 p θ - a0 p θ = p.V ^ 2 / 4 *
      ((9 * p.V * p.kP ^ 2 * p.kp + 6 * p.V * p.kP * p.kp ^ 2) * Real.cos θ *
          Real.cos (2 * θ) +
        4 * p.ki * p.kp * Real.cos θ ^ 2 + 6 * p.kP * p.ki * Real.sin θ ^ 2) := by
  have h2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul]; have := Real.sin_sq_add_cos_sq θ; linarith
  simp only [a2, a1, a0]
  rw [h2]
  ring

@[powerlib_foundation] theorem a2_mul_a1_sub_a0_pos (hV : 0 < p.V) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ : ℝ} (hcos : 0 < Real.cos θ)
    (hcos2 : 0 ≤ Real.cos (2 * θ)) : a0 p θ < a2 p θ * a1 p θ := by
  have h := a2_mul_a1_sub_a0 p θ
  have t1 : 0 ≤ (9 * p.V * p.kP ^ 2 * p.kp + 6 * p.V * p.kP * p.kp ^ 2) * Real.cos θ *
      Real.cos (2 * θ) := by positivity
  have t2 : 0 < 4 * p.ki * p.kp * Real.cos θ ^ 2 := by positivity
  have t3 : 0 ≤ 6 * p.kP * p.ki * Real.sin θ ^ 2 := by positivity
  have : 0 < p.V ^ 2 / 4 * ((9 * p.V * p.kP ^ 2 * p.kp + 6 * p.V * p.kP * p.kp ^ 2) *
      Real.cos θ * Real.cos (2 * θ) + 4 * p.ki * p.kp * Real.cos θ ^ 2 +
      6 * p.kP * p.ki * Real.sin θ ^ 2) := by positivity
  linarith

/-! ## The quasi-static GFL family -/

/-- A quasi-static three-state GFL model read about a selected operating point
`(θ*, 0, i_d*)`. -/
structure Model where
  /-- The parameters. -/
  params : Params
  /-- The selected angle `θ*`. -/
  θ : ℝ
  /-- The selected d-axis current `i_d*` (IN-positive). -/
  Id : ℝ

/-- The field translated so that the selected operating point is the origin. -/
def Model.field (m : Model) (z : Dynamics.State 3) : Dynamics.State 3 :=
  QuasiStatic.field m.params (z + point m.θ m.Id)

/-- Requirements on the quasi-static GFL models, all static. -/
inductive Requirement
  /-- `(θ*, 0, i_d*)` is an equilibrium (`IsEq`). -/
  | equilibrium
  /-- The closed-form Jacobian satisfies the strict 3×3 Routh–Hurwitz conditions. -/
  | jacobianStable
  /-- The closed-form Jacobian has `det > 0` or `tr > 0`. -/
  | jacobianUnstable
  /-- Positive gains `k_p, k_i, k_P > 0` (context requirement; no sentence is translated into
  it). -/
  | positiveGains

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => IsEq m.params m.θ m.Id
  | .jacobianStable => (jac m.params m.θ m.Id).trace < 0 ∧ (jac m.params m.θ m.Id).det < 0 ∧
      (jac m.params m.θ m.Id).trace * Criteria.principalMinorSum (jac m.params m.θ m.Id) <
        (jac m.params m.θ m.Id).det
  | .jacobianUnstable => 0 < (jac m.params m.θ m.Id).det ∨ 0 < (jac m.params m.θ m.Id).trace
  | .positiveGains => 0 < m.params.kp ∧ 0 < m.params.ki ∧ 0 < m.params.kP

/-- The translation of the sentences: the local ones into an equilibrium with a Routh–Hurwitz
Jacobian, instability into one with `det > 0` or `tr > 0`, passivity into nothing. The global
sentences, decay rates, sampled contraction and conservation are not decided by the
linearization and are translated into the whole language, which no model meets (unavailable
translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.equilibrium, .jacobianStable}
  | .flow .unstable => {.equilibrium, .jacobianUnstable}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The quasi-static GFL family: every model read as its field translated to the selected
operating point. -/
def family : Family Model Requirement 3 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

/-- A flow sentence of a model is the sentence of the untranslated field at the selected
point. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (QuasiStatic.field m.params) (point m.θ m.Id) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Linearization at the selected point: a Routh–Hurwitz Jacobian gives local exponential
stability. -/
private theorem les_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianStable) : m ∈ family.den (.flow .locallyExponentiallyStable) :=
  mem_den_flow_iff.mpr (Criteria.locallyExponentiallyStable_of_jacobian_fin_three
    (jac m.params m.θ m.Id) (contDiff_field m.params) (field_point_eq_zero m.params he)
    (fderiv_field m.params m.θ 0 m.Id) hs.1 hs.2.1 hs.2.2)

/-- Linearization at the selected point: `det > 0` or `tr > 0` gives instability. -/
private theorem unstable_of_meets {m : Model} (he : Meets m .equilibrium)
    (hs : Meets m .jacobianUnstable) : m ∈ family.den (.flow .unstable) := by
  refine mem_den_flow_iff.mpr ?_
  rcases hs with hdet | htr
  · exact Criteria.unstable_of_jacobian_det_pos_fin_three (jac m.params m.θ m.Id)
      (contDiff_field m.params) (field_point_eq_zero m.params he)
      (fderiv_field m.params m.θ 0 m.Id) hdet
  · exact Criteria.unstable_of_jacobian_trace_pos_fin_three (jac m.params m.θ m.Id)
      (contDiff_field m.params) (field_point_eq_zero m.params he)
      (fderiv_field m.params m.θ 0 m.Id) htr

/-! ### Soundness of the translation -/

/-- No model has both a Routh–Hurwitz Jacobian and `det > 0` or `tr > 0`: the whole requirement
language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .jacobianStable .jacobianUnstable fun m hs hu => ?_
  obtain ⟨h1, h2, -⟩ : Meets m .jacobianStable := hs
  rcases (hu : Meets m .jacobianUnstable) with h3 | h3 <;> linarith

/-- Every translation of the quasi-static GFL family is sound: its translation chain lies below
its semantics connection. A Routh–Hurwitz Jacobian at an equilibrium proves the local sentences,
`det > 0` or `tr > 0` proves instability (LeanForControl's linearization theorems at the selected
point, moved to the origin), and passivity holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same
    (Rs := {.equilibrium, .jacobianStable}) (Ru := {.equilibrium, .jacobianUnstable})
    (fun s => ?_) realize_univ (fun m hm => ?_) (fun m hm => ?_) family_isAutonomous.den_passive
  · rcases s with P | _
    · cases P <;> rfl
    · rfl
  · rw [TMIO.mem_realize] at hm
    exact les_of_meets (hm .equilibrium (by simp)) (hm .jacobianStable (by simp))
  · rw [TMIO.mem_realize] at hm
    exact unstable_of_meets (hm .equilibrium (by simp)) (hm .jacobianUnstable (by simp))

/-! ### Exactness of the local exponential translation -/

/-- With no dispatch gain the Jacobian is singular. -/
private theorem det_jac_of_kP_eq_zero {p : Params} (h : p.kP = 0) (θ Id : ℝ) :
    (jac p θ Id).det = 0 := by
  simp [jac, Matrix.det_fin_three, h]

/-- An equilibrium of the field at `(θ*, 0, i_d*)` with a nonzero dispatch gain is an `IsEq`
point. -/
@[powerlib_foundation] theorem isEq_of_field_eq_zero {p : Params} {θ Id : ℝ} (hkP : p.kP ≠ 0)
    (h : field p (point θ Id) = 0) : IsEq p θ Id := by
  have h1 := congrArg (fun y : Dynamics.State 3 => y 1) h
  have h2 := congrArg (fun y : Dynamics.State 3 => y 2) h
  simp [field, point, Dynamics.lift, coordField] at h1 h2
  rcases h2 with h2 | h2
  · exact absurd h2 hkP
  · refine ⟨by unfold vq at h1; linarith, by linarith⟩

/-- The local exponential translation is exact: a model is locally exponentially stable at its
selected point exactly when the point is an equilibrium (`IsEq`) and the closed-form Jacobian
satisfies the strict 3×3 Routh–Hurwitz conditions. Converse linearization: local exponential
stability of the `C¹` field forces an equilibrium with a Hurwitz Jacobian. -/
@[powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exact_of_exactUnder_empty (Spectral.exactUnder_les_of_jacobian
    (fun m P => mem_den_flow_iff) ∅ (fun m => jac m.params m.θ m.Id) (fun m _ hm => ?_)
    (fun m _ => contDiff_field m.params) (fun m _ => fderiv_field m.params m.θ 0 m.Id)
    fun m _ he hH => ?_)
  · rw [TMIO.mem_realize] at hm
    exact les_of_meets (hm .equilibrium (by simp [family, translate]))
      (hm .jacobianStable (by simp [family, translate]))
  rw [Criteria.isHurwitz_fin_three_iff] at hH
  have hkP : m.params.kP ≠ 0 := fun hkP => by
    have := hH.2.1
    rw [det_jac_of_kP_eq_zero hkP] at this
    exact lt_irrefl 0 this
  rw [TMIO.mem_realize]
  rintro q (rfl | rfl)
  · exact isEq_of_field_eq_zero hkP he
  · exact hH

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-! ### Stability and instability of the operating point -/

/-- Quasi-static GFL, `cos θ > 0` and `cos 2θ > 0` (i.e. `|θ| < 45°` on the branch): the
equilibrium is locally exponentially stable for every positive gain triple. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_cos_two_mul_pos (p : Params)
    (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ}
    (heq : IsEq p θ Id) (hcos : 0 < Real.cos θ) (hcos2 : 0 < Real.cos (2 * θ)) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine les_of_meets heq ⟨?_, ?_, ?_⟩
  · show (jac p θ Id).trace < 0
    rw [trace_jac]; unfold a2; have : 0 < p.V * Real.cos θ := mul_pos hV hcos
    nlinarith
  · show (jac p θ Id).det < 0
    rw [det_jac p heq.1]; unfold a0; have : 0 < p.V ^ 2 := by positivity
    have : 0 < p.V ^ 2 * p.kP * p.ki * Real.cos (2 * θ) := by positivity
    linarith
  · show (jac p θ Id).trace * Criteria.principalMinorSum (jac p θ Id) < (jac p θ Id).det
    rw [trace_jac, principalMinorSum_jac p heq.1, det_jac p heq.1]
    have := a2_mul_a1_sub_a0_pos p hV hkp hki hkP hcos hcos2.le
    linarith

/-- Same, stated with the angle: `|θ| < π/4`. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_abs_lt (p : Params)
    (hV : 0 < p.V) (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ}
    (heq : IsEq p θ Id) (hθ : |θ| < Real.pi / 4) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .locallyExponentiallyStable)) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hθ
  have hπ := Real.pi_pos
  exact mem_den_locallyExponentiallyStable_of_cos_two_mul_pos p hV hkp hki hkP heq
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

/-- Quasi-static GFL, `cos 2θ < 0` (`45° < |θ| < 135°`): a positive real eigenvalue, the
equilibrium is unstable (fold side of the branch). -/
@[powerlib_domain] theorem mem_den_unstable_of_cos_two_mul_neg (p : Params) (hV : p.V ≠ 0)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : IsEq p θ Id)
    (hcos2 : Real.cos (2 * θ) < 0) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine unstable_of_meets heq (Or.inl ?_)
  show 0 < (jac p θ Id).det
  rw [det_jac p heq.1]
  unfold a0
  have : 0 < p.V ^ 2 := by positivity
  have : 0 < p.V ^ 2 * p.kP * p.ki := by positivity
  nlinarith

/-- Same, stated with the angle: `π/4 < θ < π/2`. -/
@[powerlib_domain] theorem mem_den_unstable_of_pi_div_four_lt (p : Params) (hV : p.V ≠ 0)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : IsEq p θ Id) (h1 : Real.pi / 4 < θ)
    (h2 : θ < Real.pi / 2) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_cos_two_mul_neg p hV hki hkP heq
    (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos]))

/-- On the fold side of the branch (`cos 2θ < 0`) the equilibrium is not Lyapunov stable. -/
@[powerlib_domain] theorem not_mem_den_lyapunovStable_of_cos_two_mul_neg (p : Params)
    (hV : p.V ≠ 0) (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : IsEq p θ Id)
    (hcos2 : Real.cos (2 * θ) < 0) :
    connection% (Model.mk p θ Id ∉ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_mem_den_lyapunovStable_of_unstable
    (mem_den_unstable_of_cos_two_mul_neg p hV hki hkP heq hcos2)

/-! ## Absence of Hopf pairs -/

/-- No Hopf pair: for positive gains and `cos θ > 0`, the Jacobian at an equilibrium never has
a nonzero purely imaginary eigenvalue. -/
@[powerlib_foundation] theorem no_imaginary_eigenvalue (hV : 0 < p.V) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : -(p.Xg * Id) = p.V * Real.sin θ)
    (hcos : 0 < Real.cos θ) (ω : ℝ) (hω : ω ≠ 0) :
    (Linear.characteristicMatrix (jac p θ Id) (Complex.I * ω)).det ≠ 0 := by
  intro h
  rw [det_characteristicMatrix_jac p heq] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_succ, Complex.mul_re, Complex.mul_im] at hre him
  -- `hre : a0 - a2 ω² = 0`, `him : a1 ω - ω³ = 0`
  have hω2 : 0 < ω ^ 2 := by positivity
  have ha1 : a1 p θ = ω ^ 2 := by
    have : ω * (a1 p θ - ω ^ 2) = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hω
    · linarith
  have ha0 : a0 p θ = a2 p θ * ω ^ 2 := by linear_combination hre
  have ha2 : 0 < a2 p θ := by unfold a2; have : 0 < p.V * Real.cos θ := mul_pos hV hcos
                              nlinarith
  rcases le_or_gt 0 (Real.cos (2 * θ)) with hc2 | hc2
  · have := a2_mul_a1_sub_a0_pos p hV hkp hki hkP hcos hc2
    rw [ha1, ha0] at this
    linarith
  · have : a0 p θ < 0 := by
      unfold a0
      have : 0 < p.V ^ 2 * p.kP * p.ki := by positivity
      nlinarith
    nlinarith

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: `V = 0`, `X_g = 1`, all gains and the reference zero, at
`(θ*, 0, i_d*) = (0, 0, −1)` (the OUT-positive source point `I_d* = 1`). -/
def offEquilibrium : Model := ⟨⟨0, 1, 0, 0, 0, 0⟩, 0, -1⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff) (contDiff_field _)
    fun h => ?_
  have := congrArg (fun y : Dynamics.State 3 => y 1) h
  simp [offEquilibrium, QuasiStatic.field, Dynamics.lift, coordField, point, vq] at this

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for an equilibrium. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .equilibrium)
    (by simp [family, translate]) (by simp [family, Meets, IsEq, offEquilibrium])

/-! ### The Lyapunov translation -/

/-- An undamped PLL with a frozen dispatch loop: `V = k_i = 1`, `X_g = k_p = k_P = P_ref = 0` at
`(θ*, 0, i_d*) = (0, 0, 0)`; the field is the pendulum `θ̇ = x`, `ẋ = −sin θ` with `i_d`
constant. -/
def undampedPLL : Model := ⟨⟨1, 0, 0, 1, 0, 0⟩, 0, 0⟩

private theorem undampedPLL_field (z : Dynamics.State 3) :
    QuasiStatic.field undampedPLL.params z = WithLp.toLp 2 ![z 1, -Real.sin (z 0), 0] := by
  ext i
  fin_cases i <;> simp [QuasiStatic.field, Dynamics.lift, coordField, undampedPLL, vq, power]

/-- The energy `1 − cos θ + x²/2 + i_d²/2`. -/
private theorem pendulumEnergy_hasFDerivAt (z : Dynamics.State 3) :
    HasFDerivAt (fun y : Dynamics.State 3 => 1 - Real.cos (y 0) + 1 / 2 * y 1 ^ 2 + 1 / 2 * y 2 ^ 2)
      (Real.sin (z 0) • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 : Dynamics.State 3 →L[ℝ] ℝ) +
        z 1 • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1 : Dynamics.State 3 →L[ℝ] ℝ) +
        z 2 • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Dynamics.State 3 →L[ℝ] ℝ)) z := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) :
    Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) :
    Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) :
    Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have hc := (Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z h0
  have h := ((hc.const_sub 1).add ((h1.pow 2).const_mul (1 / 2 : ℝ))).add
    ((h2.pow 2).const_mul (1 / 2 : ℝ))
  refine h.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp
  ring

/-- The undamped PLL with a frozen dispatch loop is Lyapunov stable: the energy
`1 − cos θ + x²/2 + i_d²/2` is conserved and has a strict minimum on `|θ| < π`
(`Dynamics.pendulumEnergy_pos`). Its Jacobian has trace `0`, so it meets no Routh–Hurwitz
requirement. -/
@[powerlib_domain] theorem undampedPLL_mem_den_lyapunovStable :
    connection% (undampedPLL ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr ?_
  change LyapunovStable _ _
  have hpt : point undampedPLL.θ undampedPLL.Id = 0 := by
    ext i
    fin_cases i <;> simp [point, undampedPLL]
  rw [hpt]
  have hcont : Continuous fun y : Dynamics.State 3 => y 0 :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : Dynamics.State 3 →L[ℝ] ℝ).continuous
  refine lyapunov_stable
    (V := fun y : Dynamics.State 3 => 1 - Real.cos (y 0) + 1 / 2 * y 1 ^ 2 + 1 / 2 * y 2 ^ 2)
    (D := {y | |y 0| < Real.pi}) (by norm_num)
    ⟨isOpen_lt (continuous_abs.comp hcont) continuous_const, by simp [Real.pi_pos],
      continuous_iff_continuousAt.mpr fun y => (pendulumEnergy_hasFDerivAt y).continuousAt,
      fun y => (pendulumEnergy_hasFDerivAt y).differentiableAt, by simp,
      fun y hy hne => ?_, fun y _ => ?_⟩
  · have hy' : |y 0| < Real.pi := hy
    have hw : 1 / 2 * (‖y - 0‖ ^ 2 - y 0 ^ 2) ≤ 1 / 2 * y 1 ^ 2 + 1 / 2 * y 2 ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      linarith
    linarith [Dynamics.pendulumEnergy_pos 0 one_half_pos (by simp) hw
      (by linarith [Real.pi_pos]) hne]
  · rw [(pendulumEnergy_hasFDerivAt y).fderiv, undampedPLL_field]
    simp [mul_comm]

/-- The Lyapunov translation is sound but not exact: the undamped PLL with a frozen dispatch loop
is Lyapunov stable at an equilibrium whose Jacobian has trace `0`. -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness undampedPLL_mem_den_lyapunovStable (q := .jacobianStable)
    (by simp [family, translate]) fun hs => ?_
  have := (hs : Meets undampedPLL .jacobianStable).1
  simp [jac, Matrix.trace_fin_three, undampedPLL] at this

end powerlib.GFL.PowerLoop.QuasiStatic
