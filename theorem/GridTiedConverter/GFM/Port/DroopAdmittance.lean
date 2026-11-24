import theorem.GridTiedConverter.GFM.Port.Admittance

/-! # Small-signal dq admittance of the grid-forming VSM with Q–V droop on an R–L line

The Layer-0 VSM (`Line.VSM`) with a reactive-power–voltage droop: the EMF magnitude follows the
filtered reactive power, `E = E₀ − n_q (Q_f − Q_ref)`. Seen from its terminal (the PCC voltage
as input, the IN-positive current as output), the linearization at an operating point is a
`Linear.Plant` whose transfer matrix is a closed form with two synchronization channels (angle
and EMF magnitude), for powers measured at the source and for powers measured at the PCC.

Model boundary.
* State `x = (δ, ω, i_d, i_q, Q_f) : State 5` in this order: dq frame rotating at the nominal
  `ω₀`, `δ̇ = ω`, `M ω̇ = P_ref − P_m − D ω`, `L i̇ = E(Q_f) e^{jδ} − v − (R + jX) i`
  (`X = ω₀ L`), `Q̇_f = ω_q (Q_m − Q_f)`, droop EMF `E(Q_f) = E₀ − n_q (Q_f − Q_ref)`
  (`VSMQ.emfMag`; `Network.E` is the no-load `E₀`), line current `i` out of the converter, PCC
  voltage `v = (v_d, v_q)` the input. Powers per unit without `3/2`, export-positive
  (`Transform.pq`): source-measured `P_m + j Q_m = E(Q_f) e^{jδ} conj i` (`VSMQ.portField`, the
  library's `Network.power`, `Network.reactive` at the droop EMF, `VSMQ.net`), or PCC-measured
  `P_m + j Q_m = v conj i` (`VSMQ.pccField`). The active power is not filtered.
* Small signal at an operating point `(δ₀, i₀, Q_f0)` (and PCC voltage `v₀` for the
  PCC-measured law), at any such point, equilibrium or not: state matrix the Jacobian derived by
  `fderiv` (`hasFDerivAt_portField`, `hasFDerivAt_pccField`), input matrix the exact
  coefficient of `v` (the fields are affine in `v`: `portField_eq`, `pccField_eq`), output the
  IN-positive port current `−i` (as `Line.VSM.portC`), no feedthrough.
* Notation at the operating point: `E' = E(Q_f0)`, `v_c = E' (cos δ₀, sin δ₀)`,
  `u_c = (cos δ₀, sin δ₀)`, `J = [[0, −1], [1, 0]]`; channel input
  `B_c = [J v_c, −n_q u_c]` (`syncB`), source output rows `C_i = [v_cᵀ; v_cᵀ J]` (`syncCi`),
  current rows `C_v = [i₀ᵀ; (J i₀)ᵀ]` (`curC`), PCC rows `C_p = [v₀ᵀ; v₀ᵀ J]` (`pccCi`), channel
  gains `K_n = diag(1, −ω_q)` (`chanGain`).
* Parameters free reals; each theorem lists what it uses (`M ≠ 0`, `L ≠ 0` and nonsingularity
  off the poles). Frequency-wise statements at a fixed `s`; no time-domain or stability claim.
  Excluded: active-power filter, inner loops, virtual impedance, limits, PLL, delay, PWM.

Source: GFM port-structure study note (t1-port, §(a) closed form with Q–V droop and the
PCC-measured variant; the study's symbolic check was unfinished; the closed forms are derived
here, by the response-vector argument of `theorem/GridTiedConverter/GFM/Port/Admittance.lean`);
the droop law of `theorem/GridTiedConverter/GFM/QVDroop.lean` (quasi-static line there).

Results.
* Source-measured (`portField`, `jacobian`, `portB`, `portModel`): `portField_eq`,
  `hasFDerivAt_portField`; with the loop matrix
  `W(s) = diag(M s² + D s, s + ω_q) + K_n C_v B_c` (`chanW`) the synchronization impedance is
  `Z_c(s) = B_c W(s)⁻¹ K_n C_i` (`droopZc`) and off the poles (`det W ≠ 0`,
  `det (Z_oc + Z_c) ≠ 0`, `det (sI − A) ≠ 0`) the transfer matrix is
  `Y(s) = (Z_oc(s) + Z_c(s))⁻¹` (`droopY`, `transfer_portModel`; `Z_oc` the line's
  `Passive.SeriesRLC.dqImpedance`). At `n_q = 0` (and `s ≠ −ω_q`) the reactive channel
  decouples and `Z_oc + Z_c = Z_oc + g(s) J v_c v_cᵀ`, `g = 1/(M s² + D s − Q_c)`: the port
  impedance `Network.portZ` of the constant-EMF VSM (`droopZ_of_nq_eq_zero`).
* Traceless structure: `trace Z_c(s) = 0` at every `s` and every operating point
  (`trace_droopZc`), as for the rank-one constant-EMF term.
* PCC-measured (`pccField`, `pccJacobian`, `pccB`, `pccModel`): `pccField_eq`,
  `hasFDerivAt_pccField`; with `K(s) = diag(1/(M s² + D s), −ω_q/(s + ω_q))` (`pccGain`), off
  the poles the transfer matrix is
  `Y(s) = (Z_oc(s) + B_c K C_p)⁻¹ (I + B_c K C_v)` (`pccY`, `transfer_pccModel`): the powers do
  not see the EMF, so the loop does not close through `B_c`, and the PCC voltage enters the
  channels directly (`I + B_c K C_v`).

Family and connection conclusions.
* None: realization identities and frequency-wise static facts (static evidence). The model is
  not read as another family's member here.
-/

noncomputable section
namespace powerlib.GFM.Line
open Matrix Linear
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components)

/-- The VSM with Q–V droop on the line: the VSM data, the droop gain `n_q`, the reactive filter
bandwidth `ω_q` and the reactive set point `Q_ref` (`E` is the no-load EMF `E₀`). -/
structure VSMQ extends VSM where
  nq : ℝ
  ωq : ℝ
  Qref : ℝ

namespace VSMQ

variable (g : VSMQ)

/-! ## The model and its linearization -/

/-- The droop EMF magnitude `E(Q_f) = E₀ − n_q (Q_f − Q_ref)`. -/
def emfMag (qf : ℝ) : ℝ := g.E - g.nq * (qf - g.Qref)

/-- The network at the filtered reactive power `Q_f`: the line with the EMF magnitude `E(Q_f)`. -/
def net (qf : ℝ) : Network := { g.toNetwork with E := g.emfMag qf }

/-- The source-measured field on `(δ, ω, i_d, i_q, Q_f)` with the PCC voltage `v` as input. -/
def portField (x : State 5) (v : Fin 2 → ℝ) : State 5 :=
  WithLp.toLp 2 ![x 1, (g.Pref - (g.net (x 4)).power (x 0) (x 2) (x 3) - g.D * x 1) / g.M,
    (g.emfMag (x 4) * Real.cos (x 0) - v 0 - g.R * x 2 + g.X * x 3) / g.L,
    (g.emfMag (x 4) * Real.sin (x 0) - v 1 - g.R * x 3 - g.X * x 2) / g.L,
    g.ωq * ((g.net (x 4)).reactive (x 0) (x 2) (x 3) - x 4)]

/-- The input matrix `∂f/∂v`: `−1/L` on the two current rows. -/
def portB : Matrix (Fin 5) (Fin 2) ℝ :=
  !![0, 0; 0, 0; -(1 / g.L), 0; 0, -(1 / g.L); 0, 0]

/-- The output matrix: the IN-positive port current `−(i_d, i_q)`. -/
def portC : Matrix (Fin 2) (Fin 5) ℝ := !![0, 0, -1, 0, 0; 0, 0, 0, -1, 0]

/-- The voltage channel is affine: `f(x, v) = f(x, v') + B (v − v')`. -/
@[tmio M, powerlib_domain] theorem portField_eq (x : State 5) (v v' : Fin 2 → ℝ) :
    g.portField x v = g.portField x v' + WithLp.toLp 2 (g.portB *ᵥ (v - v')) := by
  ext i
  fin_cases i <;> simp [portField, portB, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The Jacobian at angle `δ`, current `(i_d, i_q)` and filtered reactive power `Q_f`, with
`E' = E(Q_f)`, `P = E' (cos δ i_d + sin δ i_q)`, `Q = E' (sin δ i_d − cos δ i_q)`. -/
def jacobian (δ id iq qf : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 0;
    g.emfMag qf * (Real.sin δ * id - Real.cos δ * iq) / g.M, -g.D / g.M,
      -(g.emfMag qf * Real.cos δ) / g.M, -(g.emfMag qf * Real.sin δ) / g.M,
      g.nq * (Real.cos δ * id + Real.sin δ * iq) / g.M;
    -(g.emfMag qf * Real.sin δ) / g.L, 0, -g.R / g.L, g.X / g.L, -(g.nq * Real.cos δ) / g.L;
    g.emfMag qf * Real.cos δ / g.L, 0, -g.X / g.L, -g.R / g.L, -(g.nq * Real.sin δ) / g.L;
    g.ωq * (g.emfMag qf * (Real.cos δ * id + Real.sin δ * iq)), 0,
      g.ωq * (g.emfMag qf * Real.sin δ), -(g.ωq * (g.emfMag qf * Real.cos δ)),
      -(g.ωq * (1 + g.nq * (Real.sin δ * id - Real.cos δ * iq)))]

/-- The droop EMF along the state: derivative `−n_q` in `Q_f`. -/
@[tmio M, powerlib_domain] private theorem hasFDerivAt_emfMag (x : State 5) :
    HasFDerivAt (fun y : State 5 => g.emfMag (y 4)) (-g.nq • coord 4) x := by
  have h := (hasFDerivAt_const g.E x).sub
    (((hasFDerivAt_coord 4 x).sub_const g.Qref).const_mul g.nq)
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · ext v; simp
  · simp [emfMag]

/-- At every PCC voltage the state Jacobian of the source-measured field is `jacobian`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_portField (x : State 5) (v : Fin 2 → ℝ) :
    HasFDerivAt (fun y => g.portField y v)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.jacobian (x 0) (x 2) (x 3) (x 4))) x := by
  have hE := g.hasFDerivAt_emfMag x
  have h0 := hasFDerivAt_coord 0 x
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  have h2 := hasFDerivAt_coord 2 x
  have h3 := hasFDerivAt_coord 3 x
  have hP := hE.mul ((hc.mul h2).add (hs.mul h3))
  have hQ := hE.mul ((hs.mul h2).sub (hc.mul h3))
  refine hasFDerivAt_toEuclideanCLM_of_components _
    (fun i => ∑ j, g.jacobian (x 0) (x 2) (x 3) (x 4) i j • coord j)
    (fun i => ?_) (fun i v => by simp)
  fin_cases i
  · refine ((hasFDerivAt_coord 1 x).congr_fderiv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [jacobian, Fin.sum_univ_five]
    · simp [portField]
  · have h := (((hasFDerivAt_const g.Pref x).sub hP).sub
      ((hasFDerivAt_coord 1 x).const_mul g.D)).mul_const g.M⁻¹
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [jacobian, Fin.sum_univ_five]; field_simp; ring
    · simp [portField, net, Network.power_eq, div_eq_mul_inv]
  · have h := ((((hE.mul hc).sub_const (v 0)).sub (h2.const_mul g.R)).add
      (h3.const_mul g.X)).mul_const g.L⁻¹
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [jacobian, Fin.sum_univ_five]; field_simp; ring
    · simp [portField, div_eq_mul_inv]
  · have h := ((((hE.mul hs).sub_const (v 1)).sub (h3.const_mul g.R)).sub
      (h2.const_mul g.X)).mul_const g.L⁻¹
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [jacobian, Fin.sum_univ_five]; field_simp; ring
    · simp [portField, div_eq_mul_inv]
  · have h := (hQ.sub (hasFDerivAt_coord 4 x)).const_mul g.ωq
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [jacobian, Fin.sum_univ_five]; ring
    · simp [portField, net, Network.reactive_eq]

/-- The source-measured small-signal port model at `(δ₀, i_d0, i_q0, Q_f0)`. -/
def portModel (δ id iq qf : ℝ) : Plant 5 2 := ⟨g.jacobian δ id iq qf, g.portB, portC, 0⟩

/-! ## The two-channel closed form -/

/-- The channel input `B_c = [J v_c, −n_q u_c]`: how the angle and the filtered reactive power
move the EMF vector. -/
def syncB (δ qf : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(g.emfMag qf * Real.sin δ), -(g.nq * Real.cos δ);
    g.emfMag qf * Real.cos δ, -(g.nq * Real.sin δ)]

/-- The source output rows `C_i = [v_cᵀ; v_cᵀ J]`: `(ΔP, ΔQ)` from the current at fixed EMF. -/
def syncCi (δ qf : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g.emfMag qf * Real.cos δ, g.emfMag qf * Real.sin δ;
    g.emfMag qf * Real.sin δ, -(g.emfMag qf * Real.cos δ)]

/-- The current rows `C_v = [i₀ᵀ; (J i₀)ᵀ]`: `(ΔP, ΔQ)` from the voltage at fixed current. -/
def curC (id iq : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![id, iq; -iq, id]

/-- The channel gains `K_n = diag(1, −ω_q)`. -/
def chanGain : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -(g.ωq : ℂ)]

/-- The loop matrix `W(s) = diag(M s² + D s, s + ω_q) + K_n C_v B_c`. -/
def chanW (δ id iq qf : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s, 0; 0, s + (g.ωq : ℂ)] +
    g.chanGain * complexify (curC id iq) * complexify (g.syncB δ qf)

/-- The synchronization impedance `Z_c(s) = B_c W(s)⁻¹ K_n C_i`. -/
def droopZc (δ id iq qf : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  complexify (g.syncB δ qf) * (g.chanW δ id iq qf s)⁻¹ * g.chanGain *
    complexify (g.syncCi δ qf)

/-- The port impedance `Z_oc(s) + Z_c(s)`. -/
def droopZ (δ id iq qf : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  g.branch.dqImpedance g.ω0 s + g.droopZc δ id iq qf s

/-- The closed-form port admittance `Y(s) = (Z_oc(s) + Z_c(s))⁻¹`. -/
def droopY (δ id iq qf : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (g.droopZ δ id iq qf s)⁻¹

/-- **The synchronization impedance is traceless**, at every `s` and operating point:
`trace (B_c W⁻¹ K_n C_i) = (det W)⁻¹ trace (B_c adj(W) K_n C_i) = 0`. -/
@[tmio M, powerlib_domain] theorem trace_droopZc (δ id iq qf : ℝ) (s : ℂ) :
    (g.droopZc δ id iq qf s).trace = 0 := by
  rw [droopZc, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_zero]
  right
  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  simp [chanW, chanGain, syncB, syncCi, curC, complexify, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.vecMul, dotProduct]
  ring

/-- Without droop the loop matrix is lower triangular: the angle channel sees `M s² + D s − Q_c`
alone (`Q_c = Q_e(δ₀, i₀)`), the reactive channel is driven by `P_c` but does not act back. -/
@[tmio M, powerlib_domain] private theorem chanW_of_nq_eq_zero (hn : g.nq = 0)
    (δ id iq qf : ℝ) (s : ℂ) :
    g.chanW δ id iq qf s = !![(g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ), 0;
      -((g.ωq : ℂ) * (g.power δ id iq : ℂ)), s + (g.ωq : ℂ)] := by
  have hE : g.emfMag qf = g.E := by simp [emfMag, hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chanW, chanGain, curC, syncB, complexify, Matrix.mul_apply, Fin.sum_univ_two, hn, hE,
      Network.reactive_eq, Network.power_eq, Matrix.vecMul, dotProduct] <;>
    first | ring1 | (left; ring1)

/-- **Constant EMF.** Without droop (`n_q = 0`) and off `s = −ω_q`, the port impedance is that
of the constant-EMF VSM, `Z_oc + g(s) J v_c v_cᵀ` with `g = 1/(M s² + D s − Q_c)`
(`Network.portZ`, `VSM.syncGain` of `theorem/GridTiedConverter/GFM/Port/Admittance.lean`):
the reactive channel decouples. -/
@[tmio M, powerlib_domain] theorem droopZ_of_nq_eq_zero (hn : g.nq = 0) {δ id iq qf : ℝ}
    {s : ℂ} (hq : s + (g.ωq : ℂ) ≠ 0) :
    g.droopZ δ id iq qf s = g.portZ δ (g.toVSM.syncGain δ id iq s) s := by
  have hE : g.emfMag qf = g.E := by simp [emfMag, hn]
  -- the first row of the inverse of a lower-triangular matrix with `d ≠ 0` is `(a⁻¹, 0)`
  have hinv : ∀ a b d : ℂ, d ≠ 0 → (!![a, 0; b, d])⁻¹ 0 0 = a⁻¹ ∧ (!![a, 0; b, d])⁻¹ 0 1 = 0 := by
    intro a b d hd
    rw [Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv]
    constructor
    · simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, zero_mul, sub_zero, mul_inv]
      exact inv_mul_cancel_right₀ hd _
    · simp
  obtain ⟨h00, h01⟩ := hinv ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ))
    (-((g.ωq : ℂ) * (g.power δ id iq : ℂ))) _ hq
  rw [droopZ, Network.portZ, droopZc, g.chanW_of_nq_eq_zero hn]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, syncB, syncCi, chanGain, complexify, hn, hE, h00,
      h01, Network.emfC, Transform.complexSymm, vecMulVec, VSM.syncGain, Matrix.vecHead,
      Matrix.vecTail] <;> ring

/-- The line impedance `Z_oc` has the entries `R + L s` and `∓X`
(`Passive.SeriesRLC.dqImpedance_of_noCap`). -/
@[tmio M, powerlib_domain] private theorem dqImpedance_apply (s : ℂ) :
    g.branch.dqImpedance g.ω0 s =
      !![(g.R : ℂ) + g.L * s, -(g.X : ℂ); (g.X : ℂ), g.R + g.L * s] := by
  rw [Passive.SeriesRLC.dqImpedance_of_noCap rfl]
  simp [Network.branch, Network.X]

/-- **The source-measured realization has the closed-form admittance.** Off the poles, the
transfer matrix of the port model is `(Z_oc + B_c W⁻¹ K_n C_i)⁻¹`. Proof: with
`Y = (Z_oc + Z_c)⁻¹` and the channel response `C = W⁻¹ K_n C_i Y` (angle and filtered reactive
power), the state response `(C₀, s C₀, −Y, C₁)` solves `(sI − A) X = B`
(`LTI.transfer_eq_of_solution`). -/
@[tmio M, powerlib_domain] theorem transfer_portModel (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq qf : ℝ} {s : ℂ} (hW : (g.chanW δ id iq qf s).det ≠ 0)
    (hZ : (g.droopZ δ id iq qf s).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq qf).A s).det ≠ 0) :
    transfer (g.portModel δ id iq qf) s = g.droopY δ id iq qf s := by
  set Y := g.droopY δ id iq qf s with hYdef
  set W := g.chanW δ id iq qf s with hWdef
  set Bc := complexify (g.syncB δ qf)
  set Cm := W⁻¹ * g.chanGain * complexify (g.syncCi δ qf) * Y with hCm
  have hY : g.droopZ δ id iq qf s * Y = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hZ)
  have hWC : W * Cm = g.chanGain * complexify (g.syncCi δ qf) * Y := by
    rw [hCm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hW), Matrix.one_mul]
  have hline : g.branch.dqImpedance g.ω0 s * Y + Bc * Cm = 1 := by
    rw [← hY, droopZ, droopZc, Matrix.add_mul, hCm]
    simp only [Bc, hWdef, Matrix.mul_assoc]
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have ew : ∀ i k : Fin 2, (W * Cm) i k = (g.chanGain * complexify (g.syncCi δ qf) * Y) i k :=
    fun i k => by rw [hWC]
  have el : ∀ i k : Fin 2, (g.branch.dqImpedance g.ω0 s * Y + Bc * Cm) i k =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i k := fun i k => by rw [hline]
  have ew00 := ew 0 0
  have ew01 := ew 0 1
  have ew10 := ew 1 0
  have ew11 := ew 1 1
  have el00 := el 0 0
  have el01 := el 0 1
  have el10 := el 1 0
  have el11 := el 1 1
  simp only [hWdef, chanW, chanGain, syncB, syncCi, curC, complexify, Bc, dqImpedance_apply,
    Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.one_apply_eq, Complex.coe_algebraMap,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    at ew00 ew01 ew10 ew11 el00 el01 el10 el11
  push_cast at ew00 ew01 ew10 ew11 el00 el01 el10 el11
  set X : Matrix (Fin 5) (Fin 2) ℂ :=
    Matrix.of fun i k => ![Cm 0 k, s * Cm 0 k, -Y 0 k, -Y 1 k, Cm 1 k] i with hX
  have hMX : characteristicMatrix (g.portModel δ id iq qf).A s * X =
      complexify (g.portModel δ id iq qf).B := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [characteristicMatrix, complexify, portModel, jacobian, portB, Matrix.mul_apply,
        Fin.sum_univ_five, hX]
    · linear_combination (norm := (field_simp; ring)) (1 / (g.M : ℂ)) * ew00
    · linear_combination (norm := (field_simp; ring)) (1 / (g.M : ℂ)) * ew01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el00
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el10
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el11
    · linear_combination ew10
    · linear_combination ew11
  rw [LTI.transfer_eq_of_solution _ _ _ hA hMX]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [portModel, portC, complexify, hX, Matrix.mul_apply, Fin.sum_univ_five]

/-! ## Powers measured at the PCC -/

/-- The PCC-measured field: `P_m + j Q_m = v conj i` (`Transform.pq` of the PCC voltage and the
export current). -/
def pccField (x : State 5) (v : Fin 2 → ℝ) : State 5 :=
  WithLp.toLp 2 ![x 1, (g.Pref - Transform.pq v ![x 2, x 3] 0 - g.D * x 1) / g.M,
    (g.emfMag (x 4) * Real.cos (x 0) - v 0 - g.R * x 2 + g.X * x 3) / g.L,
    (g.emfMag (x 4) * Real.sin (x 0) - v 1 - g.R * x 3 - g.X * x 2) / g.L,
    g.ωq * (Transform.pq v ![x 2, x 3] 1 - x 4)]

/-- The input matrix `∂f/∂v` of the PCC-measured field at the current `(i_d, i_q)`: the line
rows `−1/L` and the power rows `−i₀ᵀ/M`, `ω_q (J i₀)ᵀ`. -/
def pccB (id iq : ℝ) : Matrix (Fin 5) (Fin 2) ℝ :=
  !![0, 0; -(id / g.M), -(iq / g.M); -(1 / g.L), 0; 0, -(1 / g.L); -(g.ωq * iq), g.ωq * id]

/-- The PCC-measured field is affine in the voltage: `f(x, v) = f(x, v') + B(i) (v − v')`. -/
@[tmio M, powerlib_domain] theorem pccField_eq (x : State 5) (v v' : Fin 2 → ℝ) :
    g.pccField x v = g.pccField x v' + WithLp.toLp 2 (g.pccB (x 2) (x 3) *ᵥ (v - v')) := by
  ext i
  fin_cases i <;>
    simp [pccField, pccB, Transform.pq, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The state Jacobian of the PCC-measured field at angle `δ`, filtered reactive power `Q_f`
and PCC voltage `v` (it does not depend on the current). -/
def pccJacobian (δ qf : ℝ) (v : Fin 2 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 0;
    0, -g.D / g.M, -(v 0 / g.M), -(v 1 / g.M), 0;
    -(g.emfMag qf * Real.sin δ) / g.L, 0, -g.R / g.L, g.X / g.L, -(g.nq * Real.cos δ) / g.L;
    g.emfMag qf * Real.cos δ / g.L, 0, -g.X / g.L, -g.R / g.L, -(g.nq * Real.sin δ) / g.L;
    0, 0, g.ωq * v 1, -(g.ωq * v 0), -g.ωq]

/-- The state Jacobian of the PCC-measured field is `pccJacobian`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_pccField (x : State 5) (v : Fin 2 → ℝ) :
    HasFDerivAt (fun y => g.pccField y v)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.pccJacobian (x 0) (x 4) v)) x := by
  have hE := g.hasFDerivAt_emfMag x
  have h0 := hasFDerivAt_coord 0 x
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  have h2 := hasFDerivAt_coord 2 x
  have h3 := hasFDerivAt_coord 3 x
  refine hasFDerivAt_toEuclideanCLM_of_components _
    (fun i => ∑ j, g.pccJacobian (x 0) (x 4) v i j • coord j)
    (fun i => ?_) (fun i w => by simp)
  fin_cases i
  · refine ((hasFDerivAt_coord 1 x).congr_fderiv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [pccJacobian, Fin.sum_univ_five]
    · simp [pccField]
  · have h := (((hasFDerivAt_const g.Pref x).sub ((h2.const_mul (v 0)).add
      (h3.const_mul (v 1)))).sub ((hasFDerivAt_coord 1 x).const_mul g.D)).mul_const g.M⁻¹
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [pccJacobian, Fin.sum_univ_five]; field_simp; ring
    · simp [pccField, Transform.pq, div_eq_mul_inv]
  · have h := ((((hE.mul hc).sub_const (v 0)).sub (h2.const_mul g.R)).add
      (h3.const_mul g.X)).mul_const g.L⁻¹
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [pccJacobian, Fin.sum_univ_five]; field_simp; ring
    · simp [pccField, div_eq_mul_inv]
  · have h := ((((hE.mul hs).sub_const (v 1)).sub (h3.const_mul g.R)).sub
      (h2.const_mul g.X)).mul_const g.L⁻¹
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [pccJacobian, Fin.sum_univ_five]; field_simp; ring
    · simp [pccField, div_eq_mul_inv]
  · have h := (((h2.const_mul (v 1)).sub (h3.const_mul (v 0))).sub
      (hasFDerivAt_coord 4 x)).const_mul g.ωq
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext w; simp [pccJacobian, Fin.sum_univ_five]; ring
    · simp [pccField, Transform.pq]

/-- The PCC-measured small-signal port model at `(δ₀, i_d0, i_q0, Q_f0)` and PCC voltage `v₀`. -/
def pccModel (δ id iq qf : ℝ) (v : Fin 2 → ℝ) : Plant 5 2 :=
  ⟨g.pccJacobian δ qf v, g.pccB id iq, portC, 0⟩

/-- The PCC output rows `C_p = [v₀ᵀ; v₀ᵀ J]`: `(ΔP, ΔQ)` from the current at fixed voltage. -/
def pccCi (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![v 0, v 1; v 1, -v 0]

/-- The channel transfer `K(s) = diag(1/(M s² + D s), −ω_q/(s + ω_q))`. -/
def pccGain (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s), 0; 0, -(g.ωq : ℂ) / (s + (g.ωq : ℂ))]

/-- The closed-form PCC-measured admittance `Y(s) = (Z_oc + B_c K C_p)⁻¹ (I + B_c K C_v)`. -/
def pccY (δ id iq qf : ℝ) (v : Fin 2 → ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g.branch.dqImpedance g.ω0 s +
      complexify (g.syncB δ qf) * g.pccGain s * complexify (pccCi v))⁻¹ *
    (1 + complexify (g.syncB δ qf) * g.pccGain s * complexify (curC id iq))

/-- **The PCC-measured realization has the closed-form admittance.** Off the poles
(`M s² + D s ≠ 0`, `s + ω_q ≠ 0`, `det (Z_oc + B_c K C_p) ≠ 0`, `det (sI − A) ≠ 0`) the transfer
matrix of the PCC-measured port model is `(Z_oc + B_c K C_p)⁻¹ (I + B_c K C_v)`. Proof: with
`Y` the closed form and the channel response `C = K (C_p Y − C_v)`, the state response
`(C₀, s C₀, −Y, C₁)` solves `(sI − A) X = B` (`LTI.transfer_eq_of_solution`). -/
@[tmio M, powerlib_domain] theorem transfer_pccModel (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq qf : ℝ} {v : Fin 2 → ℝ} {s : ℂ}
    (hd : (g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s ≠ 0) (hq : s + (g.ωq : ℂ) ≠ 0)
    (hZ : (g.branch.dqImpedance g.ω0 s +
      complexify (g.syncB δ qf) * g.pccGain s * complexify (pccCi v)).det ≠ 0)
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A s).det ≠ 0) :
    transfer (g.pccModel δ id iq qf v) s = g.pccY δ id iq qf v s := by
  set Bc := complexify (g.syncB δ qf)
  set K := g.pccGain s with hK
  set Zp := g.branch.dqImpedance g.ω0 s + Bc * K * complexify (pccCi v) with hZp
  set Y := g.pccY δ id iq qf v s with hYdef
  set Cm := K * (complexify (pccCi v) * Y - complexify (curC id iq)) with hCm
  have hY : Zp * Y = 1 + Bc * K * complexify (curC id iq) := by
    rw [hYdef, pccY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hZ),
      Matrix.one_mul]
  have hline : g.branch.dqImpedance g.ω0 s * Y + Bc * Cm = 1 := by
    have e : Bc * Cm = Bc * K * complexify (pccCi v) * Y - Bc * K * complexify (curC id iq) := by
      rw [hCm, Matrix.mul_sub, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
    rw [e, ← add_sub_assoc, ← Matrix.add_mul, ← hZp, hY]
    abel
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have ec : ∀ i k : Fin 2, Cm i k =
      (K * (complexify (pccCi v) * Y - complexify (curC id iq))) i k := fun i k => by rw [hCm]
  have el : ∀ i k : Fin 2, (g.branch.dqImpedance g.ω0 s * Y + Bc * Cm) i k =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i k := fun i k => by rw [hline]
  have ec00 := ec 0 0
  have ec01 := ec 0 1
  have ec10 := ec 1 0
  have ec11 := ec 1 1
  have el00 := el 0 0
  have el01 := el 0 1
  have el10 := el 1 0
  have el11 := el 1 1
  simp only [hK, pccGain, syncB, pccCi, curC, complexify, Bc, dqImpedance_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply_eq, Complex.coe_algebraMap,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    at ec00 ec01 ec10 ec11 el00 el01 el10 el11
  push_cast at ec00 ec01 ec10 ec11 el00 el01 el10 el11
  have hc00 : ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) * Cm 0 0 =
      (v 0 : ℂ) * Y 0 0 + (v 1 : ℂ) * Y 1 0 - id := by
    rw [ec00, zero_mul, add_zero, ← mul_assoc, mul_one_div_cancel hd, one_mul]
  have hc01 : ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) * Cm 0 1 =
      (v 0 : ℂ) * Y 0 1 + (v 1 : ℂ) * Y 1 1 - iq := by
    rw [ec01, zero_mul, add_zero, ← mul_assoc, mul_one_div_cancel hd, one_mul]
  have hc10 : (s + (g.ωq : ℂ)) * Cm 1 0 =
      -(g.ωq : ℂ) * ((v 1 : ℂ) * Y 0 0 - (v 0 : ℂ) * Y 1 0 + iq) := by
    rw [ec10]; field_simp; ring
  have hc11 : (s + (g.ωq : ℂ)) * Cm 1 1 =
      -(g.ωq : ℂ) * ((v 1 : ℂ) * Y 0 1 - (v 0 : ℂ) * Y 1 1 - id) := by
    rw [ec11]; field_simp; ring
  set X : Matrix (Fin 5) (Fin 2) ℂ :=
    Matrix.of fun i k => ![Cm 0 k, s * Cm 0 k, -Y 0 k, -Y 1 k, Cm 1 k] i with hX
  have hMX : characteristicMatrix (g.pccModel δ id iq qf v).A s * X =
      complexify (g.pccModel δ id iq qf v).B := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [characteristicMatrix, complexify, pccModel, pccJacobian, pccB, Matrix.mul_apply,
        Fin.sum_univ_five, hX]
    · linear_combination (norm := (field_simp; ring)) (1 / (g.M : ℂ)) * hc00
    · linear_combination (norm := (field_simp; ring)) (1 / (g.M : ℂ)) * hc01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el00
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el10
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el11
    · linear_combination hc10
    · linear_combination hc11
  rw [LTI.transfer_eq_of_solution _ _ _ hA hMX]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pccModel, portC, complexify, hX, Matrix.mul_apply, Fin.sum_univ_five]

end VSMQ

end powerlib.GFM.Line
