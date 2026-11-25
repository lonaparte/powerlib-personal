import theorem.GridTiedConverter.GFM.Port.Admittance
import theorem.PH.PositiveRealFinTwo

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
  Excluded: active-power filter, limits, PLL, PWM; the inner cascade (virtual impedance, PI
  voltage and current loops, LC filter, delay) is
  `theorem/GridTiedConverter/GFM/Port/CascadeAdmittance.lean`, built on the same port law
  `PH.syncY`.

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
* The two-channel port law `PH.syncY` of `theorem/PH/PositiveRealFinTwo.lean`:
  the PCC-measured admittance is its instance `(N, T, B, K, C_i, C_v) =
  (Z_oc, I, B_c, pccGain, C_p, curC)` (`pccY_eq_syncY`, through which `transfer_pccModel` is
  proved), the source-measured one `(Z_oc, I, B_c, W⁻¹ K_n, C_i, 0)` (`droopY_eq_syncY`).
* **Positive-real criterion of the source-measured droop admittance** (exact, at every `s` off
  the poles, every operating point): with `P_c`, `Q_c` the powers at the source,
  `E' = E(Q_f)` and `ρ = R + L Re s`, the admittance is positive real at `s` iff `ρ ≥ 0` and
  `E'² ((2 n_q ω_q P_c)² + |n_q ω_q (M s² + D s − 2 Q_c) − E' (s̄ + ω_q)|²) ≤ 4 ρ² |det W(s)|²`
  (`hermDefect`, `positiveRealAt_droopZ_iff`, `positiveRealAt_transfer_iff`). In the frame of
  the source angle (`rot_droopZ`) `Z_c = (det W)⁻¹ N̂` with `det N̂ = n_q ω_q E'³ det W`; the
  proof reads the generic positive-real laws of `theorem/PH/PositiveRealFinTwo.lean`.
  Instances: `n_q = 0` gives `E² |g(s)| ≤ 2 ρ`, `g = 1/(M s² + D s − Q_c)`
  (`positiveRealAt_transfer_iff_of_nq_eq_zero`, at `s = jω` the constant-EMF criterion
  `Line.VSM.positiveRealAt_transfer_iff`); DC: `R ≥ 0` and `E'⁴ (E'² + 4 n_q σ) ≤ 4 R² σ²`,
  `σ = E' Q_c + n_q (P_c² + Q_c²)` (`dcSigma`, `positiveRealAt_transfer_zero_iff`; at `n_q = 0`
  `E'² ≤ 2R |Q_c|`); a lossless line is non-passive at every `jω ≠ 0` with
  `n_q ω_q D + E' ≠ 0` (`not_positiveRealAt_transfer_of_lossless`). The loop determinant in
  closed form: `det_chanW`.
* **The PCC-measured port in the frame of the source angle** (`chanDen`, `chanScaledB`,
  `pccA`, `pccN`, `pccA_apply`, `pccN_apply`): clearing the channel denominators
  `diag(s + ω_q, M s² + D s)` gives polynomial matrices `Â(s)`, `N̂(s)` in the PCC voltage
  `(v_a, v_b) = Rᵀ v₀` and the current `(i_a, i_b) = Rᵀ i₀` along and across the EMF;
  `det Â(s) = L² M det (sI − A)` (`det_pccA`), and with `E' ≠ 0`, `s + ω_q ≠ 0`,
  `det (sI − A) ≠ 0` the transfer matrix is
  `R Â(s)⁻¹ N̂(s) Rᵀ` (`transfer_pccModel_eq_rot`), at `s = 0` too, where `pccY` is not defined
  (`M s² + D s = 0`). Both realizations of the PCC-measured law go through one response
  argument (`transfer_pccModel_of_response`).
* **Positive-real criterion of the PCC-measured droop admittance** (exact, every operating
  point, off the poles): the admittance `A⁻¹ N` is not the inverse of an impedance; it is
  positive real at `s` iff `N̂(s) Â(s)ᴴ` is (`positiveRealAt_transfer_pcc_iff_mul`, by the
  generic laws `PH.positiveRealAt_orthogonal_iff` and `PH.positiveRealAt_inv_mul_iff` of
  `theorem/PH/PositiveRealFinTwo.lean`). At `s = jω`, with `x = ω²`, the Hermitian part has
  diagonal `h₀(x) = ω_q² (R − n_q (R i_b + X i_a − v_b) − n_q² P_p) + x (R + n_q ω_q L i_b)`,
  `h₁(x) = E'² P_p + x b₁ + x² M² R` and off-diagonal defect `β_r(x) + jω β_i(x)`
  (`pccHerm0`, `pccHerm1`, `pccHerm1Lin`, `pccDefRe`, `pccDefIm`; `P_p = pccPower` the PCC
  power), and the admittance is positive real at `jω` iff `h₀ + h₁ ≥ 0` and
  `β_r² + x β_i² ≤ 4 h₀ h₁` (`positiveRealAt_transfer_pcc_iff`, through the trace–determinant
  test `PH.positiveRealAt_fin_two_iff_trace`). Instance `n_q = 0` (`ω_q ≠ 0`): `R ≥ 0`,
  `h₁ ≥ 0` and `E² ((R i_a − X i_b + v_a)² + ω² L² i_a²) ≤ 4 R h₁`
  (`lineEmfD`, `positiveRealAt_transfer_pcc_iff_of_nq_eq_zero`).
* Passivity on the whole imaginary axis of both admittances (exact iff in the parameters):
  `theorem/GridTiedConverter/GFM/Port/DroopPassivity.lean`.

Family and connection conclusions.
* None: realization identities and frequency-wise static facts (static evidence). The model is
  not read as another family's member here.
-/

noncomputable section
namespace powerlib.GFM.Line
open Matrix Linear
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components)
open powerlib.PH (syncY syncY_spec positiveRealAt_orthogonal_iff
  positiveRealAt_complexSymm_add_iff normSq_mul_hermDefect)

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

/-- **Layer 0 of the port law, source-measured.** `droopY` is `syncY` with the bare line
`(N, T) = (Z_oc, I)`, `B = B_c`, `K = W⁻¹ K_n`, `C_i = C_i` and no voltage channel. -/
@[tmio M, powerlib_domain] theorem droopY_eq_syncY (δ id iq qf : ℝ) (s : ℂ) :
    g.droopY δ id iq qf s = syncY (g.branch.dqImpedance g.ω0 s) 1 (complexify (g.syncB δ qf))
      ((g.chanW δ id iq qf s)⁻¹ * g.chanGain) (complexify (g.syncCi δ qf)) 0 := by
  simp [droopY, droopZ, droopZc, syncY, Matrix.mul_assoc]

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

/-- **Layer 0 of the port law.** The PCC-measured admittance is `syncY` with the bare line
`(N, T) = (Z_oc, I)`, the channel input `B_c`, `K = pccGain`, `C_i = C_p`, `C_v = curC`. -/
@[tmio M, powerlib_domain] theorem pccY_eq_syncY (δ id iq qf : ℝ) (v : Fin 2 → ℝ) (s : ℂ) :
    g.pccY δ id iq qf v s = syncY (g.branch.dqImpedance g.ω0 s) 1 (complexify (g.syncB δ qf))
      (g.pccGain s) (complexify (pccCi v)) (complexify (curC id iq)) := rfl

/-- **The PCC-measured realization from a channel response.** If a port matrix `Y` and a
channel response `C` (angle and filtered reactive power) solve the line equation
`Z_oc Y + B_c C = I` and the channel equations
`diag(M s² + D s, s + ω_q) C = K_n (C_p Y − C_v)`, then `Y` is the transfer matrix (the state
response `(C₀, s C₀, −Y, C₁)` solves `(sI − A) X = B`, `LTI.transfer_eq_of_solution`). -/
@[tmio M, powerlib_domain] private theorem transfer_pccModel_of_response (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) {δ id iq qf : ℝ} {v : Fin 2 → ℝ} {s : ℂ}
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A s).det ≠ 0)
    {Y Cm : Matrix (Fin 2) (Fin 2) ℂ}
    (hline : g.branch.dqImpedance g.ω0 s * Y + complexify (g.syncB δ qf) * Cm = 1)
    (hch : !![(g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s, 0; 0, s + (g.ωq : ℂ)] * Cm =
      g.chanGain * (complexify (pccCi v) * Y - complexify (curC id iq))) :
    transfer (g.pccModel δ id iq qf v) s = Y := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have ec : ∀ i k : Fin 2, (!![(g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s, 0; 0, s + (g.ωq : ℂ)] * Cm) i k =
      (g.chanGain * (complexify (pccCi v) * Y - complexify (curC id iq))) i k :=
    fun i k => by rw [hch]
  have el : ∀ i k : Fin 2, (g.branch.dqImpedance g.ω0 s * Y + complexify (g.syncB δ qf) * Cm) i k =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i k := fun i k => by rw [hline]
  have ec00 := ec 0 0
  have ec01 := ec 0 1
  have ec10 := ec 1 0
  have ec11 := ec 1 1
  have el00 := el 0 0
  have el01 := el 0 1
  have el10 := el 1 0
  have el11 := el 1 1
  simp only [chanGain, syncB, pccCi, curC, complexify, dqImpedance_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply_eq, Complex.coe_algebraMap,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    at ec00 ec01 ec10 ec11 el00 el01 el10 el11
  push_cast at ec00 ec01 ec10 ec11 el00 el01 el10 el11
  set X : Matrix (Fin 5) (Fin 2) ℂ :=
    Matrix.of fun i k => ![Cm 0 k, s * Cm 0 k, -Y 0 k, -Y 1 k, Cm 1 k] i with hX
  have hMX : characteristicMatrix (g.pccModel δ id iq qf v).A s * X =
      complexify (g.pccModel δ id iq qf v).B := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [characteristicMatrix, complexify, pccModel, pccJacobian, pccB, Matrix.mul_apply,
        Fin.sum_univ_five, hX]
    · linear_combination (norm := (field_simp; ring)) (1 / (g.M : ℂ)) * ec00
    · linear_combination (norm := (field_simp; ring)) (1 / (g.M : ℂ)) * ec01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el00
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el10
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * el11
    · linear_combination ec10
    · linear_combination ec11
  rw [LTI.transfer_eq_of_solution _ _ _ hA hMX]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [pccModel, portC, complexify, hX, Matrix.mul_apply, Fin.sum_univ_five]

/-- **The PCC-measured realization has the closed-form admittance.** Off the poles
(`M s² + D s ≠ 0`, `s + ω_q ≠ 0`, `det (Z_oc + B_c K C_p) ≠ 0`, `det (sI − A) ≠ 0`) the transfer
matrix of the PCC-measured port model is `(Z_oc + B_c K C_p)⁻¹ (I + B_c K C_v)`. Proof: with
`Y` the closed form and the channel response `C = K (C_p Y − C_v)`, the state response
`(C₀, s C₀, −Y, C₁)` solves `(sI − A) X = B` (`transfer_pccModel_of_response`). -/
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
  have hY : Zp * Y = 1 + Bc * K * complexify (curC id iq) := by
    rw [hYdef, pccY_eq_syncY]
    exact syncY_spec hZ
  refine g.transfer_pccModel_of_response hM hL hA
    (Cm := K * (complexify (pccCi v) * Y - complexify (curC id iq))) ?_ ?_
  · have e : Bc * (K * (complexify (pccCi v) * Y - complexify (curC id iq))) =
        Bc * K * complexify (pccCi v) * Y - Bc * K * complexify (curC id iq) := by
      rw [Matrix.mul_sub, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
    rw [e, ← add_sub_assoc, ← Matrix.add_mul, ← hZp, hY]
    abel
  · have hd2 : s * ((g.M : ℂ) * s + (g.D : ℂ)) ≠ 0 := fun h => hd (by linear_combination h)
    rw [← Matrix.mul_assoc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hK, pccGain, chanGain]
    · field_simp
      exact div_self hd2
    · field_simp

/-! ## Positive realness of the source-measured admittance -/

/-- The loop matrix in closed form, with the current components along the EMF,
`i_a = cos δ i_d + sin δ i_q`, and across it, `i_b = cos δ i_q − sin δ i_d`:
`W = [[M s² + D s + E' i_b, −n_q i_a], [−ω_q E' i_a, s + ω_q − ω_q n_q i_b]]`. -/
@[tmio M, powerlib_domain] private theorem chanW_apply (δ id iq qf : ℝ) (s : ℂ) :
    g.chanW δ id iq qf s = !![(g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s +
        (g.emfMag qf : ℂ) * ((Real.cos δ : ℂ) * iq - (Real.sin δ : ℂ) * id),
      -((g.nq : ℂ) * ((Real.cos δ : ℂ) * id + (Real.sin δ : ℂ) * iq));
      -((g.ωq : ℂ) * ((g.emfMag qf : ℂ) * ((Real.cos δ : ℂ) * id + (Real.sin δ : ℂ) * iq))),
      s + (g.ωq : ℂ) - (g.ωq : ℂ) * ((g.nq : ℂ) * ((Real.cos δ : ℂ) * iq -
        (Real.sin δ : ℂ) * id))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chanW, chanGain, curC, syncB, complexify, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> first | ring1 | (left; ring1)

/-- The channel input in the frame of the source angle: `Rᵀ B_c = [[0, −n_q], [E', 0]]`. -/
@[tmio M, powerlib_domain] private theorem park_mul_syncB (δ qf : ℝ) :
    Transform.park δ * g.syncB δ qf = !![0, -g.nq; g.emfMag qf, 0] := by
  have h := Real.sin_sq_add_cos_sq δ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Transform.park, syncB, Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · linear_combination (-g.nq) * h
  · linear_combination g.emfMag qf * h
  · ring

/-- The source output rows in the frame of the source angle: `C_i R = diag(E', −E')`. -/
@[tmio M, powerlib_domain] private theorem syncCi_mul_rot (δ qf : ℝ) :
    g.syncCi δ qf * Transform.rot δ = !![g.emfMag qf, 0; 0, -g.emfMag qf] := by
  have h := Real.sin_sq_add_cos_sq δ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Transform.rot, syncCi, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination g.emfMag qf * h
  · ring
  · ring
  · linear_combination (-g.emfMag qf) * h

/-- The numerator of the synchronization impedance in the frame of the source angle:
`Rᵀ Z_c R = (det W)⁻¹ N̂`, `N̂ = [[n_q E' W₁₀, −n_q ω_q E' W₀₀], [E'² W₁₁, −ω_q E'² W₀₁]]`. -/
def rotZcNum (δ id iq qf : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![g.nq * g.emfMag qf * g.chanW δ id iq qf s 1 0,
      -(g.nq * g.ωq * g.emfMag qf * g.chanW δ id iq qf s 0 0);
    g.emfMag qf ^ 2 * g.chanW δ id iq qf s 1 1,
      -(g.ωq * g.emfMag qf ^ 2 * g.chanW δ id iq qf s 0 1)]

/-- **The port impedance in the frame of the source angle.** `Rᵀ (Z_oc + Z_c) R` is
`Z_oc + (det W)⁻¹ N̂` (`Z_oc` commutes with the rotation). -/
@[tmio M, powerlib_domain] private theorem rot_droopZ (δ id iq qf : ℝ) (s : ℂ) :
    complexify (Transform.rot δ)ᵀ * g.droopZ δ id iq qf s * complexify (Transform.rot δ) =
      Transform.complexSymm ((g.R : ℂ) + g.L * s) ((g.X : ℝ) : ℂ) +
        (g.chanW δ id iq qf s).det⁻¹ • g.rotZcNum δ id iq qf s := by
  have hcs : Complex.cos (δ : ℂ) ^ 2 + Complex.sin (δ : ℂ) ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  have hB : complexify (Transform.park δ) * complexify (g.syncB δ qf) =
      complexify !![0, -g.nq; g.emfMag qf, 0] := by
    rw [← Matrix.map_mul, park_mul_syncB]
  have hC : complexify (g.syncCi δ qf) * complexify (Transform.rot δ) =
      complexify !![g.emfMag qf, 0; 0, -g.emfMag qf] := by
    rw [← Matrix.map_mul, syncCi_mul_rot]
  rw [← Transform.park_eq_transpose_rot, droopZ, Matrix.mul_add, Matrix.add_mul]
  congr 1
  · rw [dqImpedance_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Transform.park, Transform.rot, Transform.complexSymm, Matrix.mul_apply,
        Fin.sum_univ_two]
    · linear_combination ((g.R : ℂ) + g.L * s) * hcs
    · linear_combination (-(g.X : ℂ)) * hcs
    · linear_combination (g.X : ℂ) * hcs
    · linear_combination ((g.R : ℂ) + g.L * s) * hcs
  · simp only [droopZc, Matrix.mul_assoc, hC]
    rw [← Matrix.mul_assoc (complexify (Transform.park δ)), hB, Matrix.inv_def,
      Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZcNum, chanGain, complexify, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two] <;> ring

/-- The Hermitian defect of the synchronization impedance in closed form,
`E'² ((2 n_q ω_q P_c)² + |n_q ω_q (M s² + D s − 2 Q_c) − E' (s̄ + ω_q)|²)` (`P_c`, `Q_c` the
powers at the source and `E' = E(Q_f)`). -/
def hermDefect (δ id iq qf : ℝ) (s : ℂ) : ℝ :=
  g.emfMag qf ^ 2 * ((2 * g.nq * g.ωq * (g.net qf).power δ id iq) ^ 2 +
    Complex.normSq (g.nq * g.ωq * (g.M * s ^ 2 + g.D * s - 2 * (g.net qf).reactive δ id iq) -
      g.emfMag qf * ((starRingEnd ℂ) s + g.ωq)))

/-- **Positive realness of the droop port impedance at one `s`.** Off `det W = 0`, the port
impedance `Z_oc(s) + Z_c(s)` of the Q–V droop VSM is positive real iff
`R + L Re s ≥ 0` and `hermDefect ≤ 4 (R + L Re s)² |det W(s)|²`: the Hermitian part is
`2 (R + L Re s) I` plus a traceless part whose eigenvalues are `± √hermDefect / |det W|`. -/
@[tmio M, powerlib_domain] theorem positiveRealAt_droopZ_iff {δ id iq qf : ℝ} {s : ℂ}
    (hW : (g.chanW δ id iq qf s).det ≠ 0) :
    PH.PositiveRealAt (g.droopZ δ id iq qf s) ↔ 0 ≤ g.R + g.L * s.re ∧
      g.hermDefect δ id iq qf s ≤
        4 * (g.R + g.L * s.re) ^ 2 * Complex.normSq (g.chanW δ id iq qf s).det := by
  set Δ := (g.chanW δ id iq qf s).det with hΔ
  set K := Δ⁻¹ • g.rotZcNum δ id iq qf s with hK
  have hW' := g.chanW_apply δ id iq qf s
  have e : ∀ i j, Δ * K i j = g.rotZcNum δ id iq qf s i j := fun i j => by
    rw [hK, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have hK11 : K 1 1 = -K 0 0 := by
    apply mul_left_cancel₀ hW
    rw [e11, mul_neg, e00]
    simp only [rotZcNum, hW', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [← positiveRealAt_orthogonal_iff (Q := Transform.rot δ)
    (by rw [← Transform.park_eq_transpose_rot, Transform.rot_mul_park]), rot_droopZ, ← hK,
    positiveRealAt_complexSymm_add_iff _ _ hK11]
  have hre : ((g.R : ℂ) + g.L * s).re = g.R + g.L * s.re := by simp
  rw [hre]
  have hP : (g.net qf).power δ id iq = g.emfMag qf * (Real.cos δ * id + Real.sin δ * iq) :=
    (g.net qf).power_eq δ id iq
  have hQ : (g.net qf).reactive δ id iq = g.emfMag qf * (Real.sin δ * id - Real.cos δ * iq) :=
    (g.net qf).reactive_eq δ id iq
  have hid : Complex.normSq Δ * (4 * (K 0 0).re ^ 2 +
      Complex.normSq (K 0 1 + (starRingEnd ℂ) (K 1 0))) = g.hermDefect δ id iq qf s := by
    rw [normSq_mul_hermDefect (r := -(g.nq * g.ωq * g.emfMag qf * (g.net qf).power δ id iq))
      (l := g.nq * g.ωq * g.emfMag qf ^ 3) ?_ ?_]
    · rw [e01, e10, hermDefect]
      have hin : g.rotZcNum δ id iq qf s 0 1 + (starRingEnd ℂ) (g.rotZcNum δ id iq qf s 1 0) =
          -((g.emfMag qf : ℂ) * (g.nq * g.ωq * (g.M * s ^ 2 + g.D * s -
            2 * ((g.net qf).reactive δ id iq : ℂ)) -
              g.emfMag qf * ((starRingEnd ℂ) s + g.ωq))) := by
        simp only [rotZcNum, hW', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_mul, map_add,
          map_sub, map_pow, Complex.conj_ofReal, hQ]
        push_cast
        ring
      rw [hin, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    · rw [e00]
      simp only [rotZcNum, hW', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hP]
      push_cast
      ring
    · have h2 : Δ * (K 0 0 ^ 2 + K 0 1 * K 1 0) * Δ =
          (Δ * K 0 0) ^ 2 + (Δ * K 0 1) * (Δ * K 1 0) := by
        ring
      apply mul_right_cancel₀ hW
      rw [h2, e00, e01, e10]
      simp only [rotZcNum, hΔ, Matrix.det_fin_two, hW', Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast
      ring
  have hpos : 0 < Complex.normSq Δ := Complex.normSq_pos.mpr hW
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    rw [← hid]
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    rw [← hid] at h1
    nlinarith

/-- **Positive realness of the source-measured realization at one `s`.** Off the poles, the
port admittance of the Q–V droop VSM is positive real at `s` iff `R + L Re s ≥ 0` and
`hermDefect ≤ 4 (R + L Re s)² |det W(s)|²` (`positiveRealAt_droopZ_iff` through
`PH.positiveRealAt_inv_iff`). -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq qf : ℝ} {s : ℂ} (hW : (g.chanW δ id iq qf s).det ≠ 0)
    (hZ : (g.droopZ δ id iq qf s).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq qf).A s).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.portModel δ id iq qf) s) ↔ 0 ≤ g.R + g.L * s.re ∧
      g.hermDefect δ id iq qf s ≤
        4 * (g.R + g.L * s.re) ^ 2 * Complex.normSq (g.chanW δ id iq qf s).det := by
  rw [g.transfer_portModel hM hL hW hZ hA, droopY,
    PH.positiveRealAt_inv_iff (isUnit_iff_ne_zero.mpr hZ)]
  exact g.positiveRealAt_droopZ_iff hW

/-- **The constant-EMF instance of the criterion.** Without droop (`n_q = 0`), off the poles
and `s ≠ −ω_q`, the port admittance is positive real at `s` iff
`E² |g(s)| ≤ 2 (R + L Re s)`, `g = 1/(M s² + D s − Q_c)` (`VSM.syncGain`): the reactive
channel drops out of `hermDefect` and `det W = (M s² + D s − Q_c)(s + ω_q)`. At `s = jω` this
is the criterion `VSM.positiveRealAt_transfer_iff` of the four-state constant-EMF port. -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_iff_of_nq_eq_zero (hn : g.nq = 0)
    (hM : g.M ≠ 0) (hL : g.L ≠ 0) {δ id iq qf : ℝ} {s : ℂ}
    (hden : (g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ) ≠ 0)
    (hq : s + (g.ωq : ℂ) ≠ 0) (hZ : (g.droopZ δ id iq qf s).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq qf).A s).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.portModel δ id iq qf) s) ↔
      g.E ^ 2 * ‖g.toVSM.syncGain δ id iq s‖ ≤ 2 * (g.R + g.L * s.re) := by
  have hE : g.emfMag qf = g.E := by simp [emfMag, hn]
  set w := (g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ) with hw_def
  have hdet : (g.chanW δ id iq qf s).det = w * (s + g.ωq) := by
    rw [g.chanW_of_nq_eq_zero hn, Matrix.det_fin_two_of]; ring
  have hW : (g.chanW δ id iq qf s).det ≠ 0 := by rw [hdet]; exact mul_ne_zero hden hq
  have hH : g.hermDefect δ id iq qf s = g.E ^ 4 * Complex.normSq (s + g.ωq) := by
    have hc : (starRingEnd ℂ) s + (g.ωq : ℂ) = (starRingEnd ℂ) (s + g.ωq) := by simp
    simp only [hermDefect, hn, hE, mul_zero, zero_mul, zero_sub, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_add, Complex.ofReal_zero, hc, Complex.normSq_neg,
      Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_conj]
    ring
  rw [g.positiveRealAt_transfer_iff hM hL hW hZ hA, hdet, hH, Complex.normSq_mul,
    Complex.normSq_eq_norm_sq w]
  have hsync : ‖g.toVSM.syncGain δ id iq s‖ = ‖w‖⁻¹ := by
    simp [VSM.syncGain, hw_def]
  rw [hsync]
  have hq' : 0 < Complex.normSq (s + g.ωq) := Complex.normSq_pos.mpr hq
  have hw : 0 < ‖w‖ := norm_pos_iff.mpr hden
  set ρ := g.R + g.L * s.re
  rw [mul_inv_le_iff₀ hw]
  constructor
  · rintro ⟨h0, h1⟩
    have h2 : (g.E ^ 2) ^ 2 ≤ (2 * ρ * ‖w‖) ^ 2 := by
      have := le_of_mul_le_mul_right (a := Complex.normSq (s + g.ωq))
        (by nlinarith [h1]) hq'
      nlinarith [this]
    have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2
    linarith
  · intro h
    have h0 : 0 ≤ ρ := by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith [sq_nonneg g.E, mul_pos (neg_pos.mpr hneg) hw]
    refine ⟨h0, ?_⟩
    have h2 : (g.E ^ 2) ^ 2 ≤ (2 * ρ * ‖w‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith [mul_le_mul_of_nonneg_right h2 hq'.le]

/-- The DC loop determinant factor `σ = E' Q_c + n_q (P_c² + Q_c²)` (`det W(0) = −ω_q σ/E'`). -/
def dcSigma (δ id iq qf : ℝ) : ℝ :=
  g.emfMag qf * (g.net qf).reactive δ id iq +
    g.nq * ((g.net qf).power δ id iq ^ 2 + (g.net qf).reactive δ id iq ^ 2)

/-- **DC passivity with Q–V droop.** At `s = 0`, with `E' = E(Q_f) ≠ 0`, `ω_q ≠ 0` and
`σ = E' Q_c + n_q (P_c² + Q_c²) ≠ 0` (`dcSigma`; then `det W(0) = −ω_q σ/E'`), the port
admittance is positive real iff `R ≥ 0` and `E'⁴ (E'² + 4 n_q σ) ≤ 4 R² σ²`, where
`E'² + 4 n_q σ = (E' + 2 n_q Q_c)² + (2 n_q P_c)² ≥ 0`. At `n_q = 0` it reads `E'² ≤ 2R |Q_c|`
(`Line.VSM.positiveRealAt_transfer_zero_iff`). -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_zero_iff (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) {δ id iq qf : ℝ} (hE : g.emfMag qf ≠ 0) (hq : g.ωq ≠ 0)
    (hσ : g.dcSigma δ id iq qf ≠ 0) (hZ : (g.droopZ δ id iq qf 0).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq qf).A 0).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.portModel δ id iq qf) 0) ↔ 0 ≤ g.R ∧
      g.emfMag qf ^ 4 * (g.emfMag qf ^ 2 + 4 * g.nq * g.dcSigma δ id iq qf) ≤
        4 * g.R ^ 2 * g.dcSigma δ id iq qf ^ 2 := by
  have hP : (g.net qf).power δ id iq = g.emfMag qf * (Real.cos δ * id + Real.sin δ * iq) :=
    (g.net qf).power_eq δ id iq
  have hQ : (g.net qf).reactive δ id iq = g.emfMag qf * (Real.sin δ * id - Real.cos δ * iq) :=
    (g.net qf).reactive_eq δ id iq
  have hE' : (g.emfMag qf : ℂ) ≠ 0 := by exact_mod_cast hE
  have hdet : (g.chanW δ id iq qf 0).det =
      ((-(g.ωq * g.dcSigma δ id iq qf / g.emfMag qf)) : ℝ) := by
    rw [Matrix.det_fin_two, g.chanW_apply]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, dcSigma, hP, hQ]
    push_cast
    field_simp
    ring
  have hW : (g.chanW δ id iq qf 0).det ≠ 0 := by
    rw [hdet]
    exact_mod_cast neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hq hσ) hE)
  have hH : g.hermDefect δ id iq qf 0 = g.emfMag qf ^ 2 * g.ωq ^ 2 *
      (g.emfMag qf ^ 2 + 4 * g.nq * g.dcSigma δ id iq qf) := by
    have hz : (g.nq : ℂ) * g.ωq * (g.M * 0 ^ 2 + g.D * 0 - 2 * ((g.net qf).reactive δ id iq : ℂ)) -
        g.emfMag qf * ((starRingEnd ℂ) 0 + g.ωq) =
        ((-(2 * g.nq * g.ωq * (g.net qf).reactive δ id iq) - g.emfMag qf * g.ωq : ℝ) : ℂ) := by
      simp only [map_zero]; push_cast; ring
    rw [hermDefect, hz, Complex.normSq_ofReal, dcSigma]
    ring
  rw [g.positiveRealAt_transfer_iff hM hL hW hZ hA, hdet, hH, Complex.normSq_ofReal]
  simp only [Complex.zero_re, mul_zero, add_zero]
  have e1 : 4 * g.R ^ 2 * (-(g.ωq * g.dcSigma δ id iq qf / g.emfMag qf) *
      -(g.ωq * g.dcSigma δ id iq qf / g.emfMag qf)) =
      g.ωq ^ 2 / g.emfMag qf ^ 2 * (4 * g.R ^ 2 * g.dcSigma δ id iq qf ^ 2) := by
    field_simp
  have e2 : g.emfMag qf ^ 2 * g.ωq ^ 2 * (g.emfMag qf ^ 2 + 4 * g.nq * g.dcSigma δ id iq qf) =
      g.ωq ^ 2 / g.emfMag qf ^ 2 *
        (g.emfMag qf ^ 4 * (g.emfMag qf ^ 2 + 4 * g.nq * g.dcSigma δ id iq qf)) := by
    field_simp
  rw [e1, e2, mul_le_mul_iff_of_pos_left (by positivity)]

/-- **A lossless line is non-passive at every nonzero frequency** unless the reactive channel
cancels: with `R = 0`, `E' ≠ 0`, `ω ≠ 0` and `n_q ω_q D + E' ≠ 0`, the port admittance is not
positive real at `jω` off the poles (`Im` of the defect's second term is
`ω (n_q ω_q D + E')`). -/
@[tmio M, powerlib_domain] theorem not_positiveRealAt_transfer_of_lossless (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) (hR : g.R = 0) {δ id iq qf ω : ℝ} (hω : ω ≠ 0) (hE : g.emfMag qf ≠ 0)
    (hD : g.nq * g.ωq * g.D + g.emfMag qf ≠ 0)
    (hW : (g.chanW δ id iq qf (ω * Complex.I)).det ≠ 0)
    (hZ : (g.droopZ δ id iq qf (ω * Complex.I)).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq qf).A (ω * Complex.I)).det ≠ 0) :
    ¬ PH.PositiveRealAt (transfer (g.portModel δ id iq qf) (ω * Complex.I)) := by
  rw [g.positiveRealAt_transfer_iff hM hL hW hZ hA]
  rintro ⟨-, h⟩
  set z : ℂ := g.nq * g.ωq * (g.M * (ω * Complex.I) ^ 2 + g.D * (ω * Complex.I) -
    2 * ((g.net qf).reactive δ id iq : ℂ)) - g.emfMag qf * ((starRingEnd ℂ) (ω * Complex.I) + g.ωq)
  have hz : z.im = ω * (g.nq * g.ωq * g.D + g.emfMag qf) := by
    simp [z, Complex.mul_im, Complex.mul_re, pow_two]
    ring
  have hzpos : 0 < Complex.normSq z := by
    rw [Complex.normSq_apply, hz]
    have : 0 < (ω * (g.nq * g.ωq * g.D + g.emfMag qf)) ^ 2 := by positivity
    nlinarith [sq_nonneg z.re]
  have hpos : 0 < g.hermDefect δ id iq qf (ω * Complex.I) := by
    rw [hermDefect]
    have : 0 < g.emfMag qf ^ 2 := by positivity
    have h2 := sq_nonneg (2 * g.nq * g.ωq * (g.net qf).power δ id iq)
    change 0 < g.emfMag qf ^ 2 * ((2 * g.nq * g.ωq * (g.net qf).power δ id iq) ^ 2 +
      Complex.normSq z)
    positivity
  simp [hR] at h
  linarith


/-! ## Positive realness of the PCC-measured admittance -/

/-- The channel denominators `diag(s + ω_q, M s² + D s)` (reactive filter, swing). -/
def chanDen (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![s + (g.ωq : ℂ), 0; 0, (g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s]

/-- The channel input in the frame of the source angle, cleared of the channel denominators:
`diag(s + ω_q, M s² + D s) Rᵀ B_c K(s) = [[0, n_q ω_q], [E', 0]]`. -/
def chanScaledB (qf : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (g.nq : ℂ) * g.ωq; (g.emfMag qf : ℂ), 0]

/-- **The PCC-measured port denominator in the frame of the source angle**, cleared of the
channel denominators: `Â(s) = diag(s + ω_q, M s² + D s) Z_oc(s) + [[0, n_q ω_q], [E', 0]] Ĉ_p`,
`Ĉ_p = C_p R` the PCC output rows at the PCC voltage `(v_a, v_b) = Rᵀ v₀` along and across the
EMF. A polynomial matrix in `s`. -/
def pccA (δ qf : ℝ) (v : Fin 2 → ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  g.chanDen s * g.branch.dqImpedance g.ω0 s + g.chanScaledB qf *
    complexify (pccCi ![Transform.parkD δ (v 0) (v 1), Transform.parkQ δ (v 0) (v 1)])

/-- The numerator in the same frame:
`N̂(s) = diag(s + ω_q, M s² + D s) + [[0, n_q ω_q], [E', 0]] Ĉ_v`, `Ĉ_v = C_v R` the current
rows at `(i_a, i_b) = Rᵀ i₀`. -/
def pccN (δ id iq qf : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  g.chanDen s + g.chanScaledB qf *
    complexify (curC (Transform.parkD δ id iq) (Transform.parkQ δ id iq))

/-- The entries of the cleared denominator `Â(s)`, with `(v_a, v_b) = Rᵀ v₀`. -/
@[tmio M, powerlib_domain] theorem pccA_apply (δ qf : ℝ) (v : Fin 2 → ℝ) (s : ℂ) :
    g.pccA δ qf v s = !![(s + g.ωq) * (g.R + g.L * s) +
        g.nq * g.ωq * Transform.parkQ δ (v 0) (v 1),
      -((s + g.ωq) * g.X) - g.nq * g.ωq * Transform.parkD δ (v 0) (v 1);
      (g.M * s ^ 2 + g.D * s) * g.X + g.emfMag qf * Transform.parkD δ (v 0) (v 1),
      (g.M * s ^ 2 + g.D * s) * (g.R + g.L * s) +
        g.emfMag qf * Transform.parkQ δ (v 0) (v 1)] := by
  rw [pccA, dqImpedance_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chanDen, chanScaledB, pccCi, complexify, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

/-- The entries of the numerator `N̂(s)`, with `(i_a, i_b) = Rᵀ i₀`. -/
@[tmio M, powerlib_domain] theorem pccN_apply (δ id iq qf : ℝ) (s : ℂ) :
    g.pccN δ id iq qf s = !![s + g.ωq - g.nq * g.ωq * Transform.parkQ δ id iq,
      g.nq * g.ωq * Transform.parkD δ id iq;
      g.emfMag qf * Transform.parkD δ id iq,
      g.M * s ^ 2 + g.D * s + g.emfMag qf * Transform.parkQ δ id iq] := by
  rw [pccN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chanDen, chanScaledB, curC, complexify, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

/-- **The cleared denominator is the characteristic polynomial**: for the PCC-measured port
model, `det Â(s) = L² M det (sI − A)` at every `s` (`M, L ≠ 0`; sympy-derived, here by
cofactor expansion and `ring`), so `det Â(s) ≠ 0` iff `s` is not a pole of the realization. -/
@[tmio M, powerlib_domain] theorem det_pccA (hM : g.M ≠ 0) (hL : g.L ≠ 0) (δ id iq qf : ℝ)
    (v : Fin 2 → ℝ) (s : ℂ) :
    (g.pccA δ qf v s).det =
      (g.L : ℂ) ^ 2 * g.M * (characteristicMatrix (g.pccModel δ id iq qf v).A s).det := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [pccA_apply, Matrix.det_fin_two_of]
  simp only [characteristicMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.submatrix_apply]
  simp [pccModel, pccJacobian, complexify, Fin.succAbove, Fin.lt_def, Transform.parkD,
    Transform.parkQ]
  field_simp
  ring

/-- Off the poles of the PCC-measured realization the cleared denominator is invertible. -/
@[tmio M, powerlib_domain] private theorem det_pccA_ne_zero (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq qf : ℝ} {v : Fin 2 → ℝ} {s : ℂ}
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A s).det ≠ 0) :
    (g.pccA δ qf v s).det ≠ 0 := by
  rw [g.det_pccA hM hL δ id iq qf v s]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hL)) (by exact_mod_cast hM))
    hA

/-- `R Rᵀ = I`, complexified. -/
@[tmio M, powerlib_domain] private theorem rot_mul_rotT (δ : ℝ) :
    complexify (Transform.rot δ) * complexify (Transform.rot δ)ᵀ = 1 := by
  rw [← Matrix.map_mul, ← Transform.park_eq_transpose_rot, Transform.rot_mul_park,
    Matrix.map_one _ (map_zero _) (map_one _)]

/-- The line impedance commutes with the rotation (both are complex-symmetric). -/
@[tmio M, powerlib_domain] private theorem dqImpedance_mul_rot (δ : ℝ) (s : ℂ) :
    g.branch.dqImpedance g.ω0 s * complexify (Transform.rot δ) =
      complexify (Transform.rot δ) * g.branch.dqImpedance g.ω0 s := by
  rw [dqImpedance_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Transform.rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The channel input is the rotated `B̂ = [[0, −n_q], [E', 0]]`: `B_c = R B̂`. -/
@[tmio M, powerlib_domain] private theorem syncB_eq_rot_mul (δ qf : ℝ) :
    complexify (g.syncB δ qf) =
      complexify (Transform.rot δ) * complexify !![0, -g.nq; g.emfMag qf, 0] := by
  rw [← park_mul_syncB, ← Matrix.map_mul, ← Matrix.mul_assoc, Transform.rot_mul_park,
    Matrix.one_mul]

/-- The PCC output rows in the frame of the source angle: `C_p R = Ĉ_p`. -/
@[tmio M, powerlib_domain] private theorem pccCi_mul_rot (δ : ℝ) (v : Fin 2 → ℝ) :
    pccCi v * Transform.rot δ =
      pccCi ![Transform.parkD δ (v 0) (v 1), Transform.parkQ δ (v 0) (v 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pccCi, Transform.rot, Transform.parkD, Transform.parkQ, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- The current rows in the frame of the source angle: `C_v R = Ĉ_v`. -/
@[tmio M, powerlib_domain] private theorem curC_mul_rot (δ id iq : ℝ) :
    curC id iq * Transform.rot δ =
      curC (Transform.parkD δ id iq) (Transform.parkQ δ id iq) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curC, Transform.rot, Transform.parkD, Transform.parkQ, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- **The PCC-measured realization in the frame of the source angle**, valid at `s = 0`: with
`E' ≠ 0`, `s + ω_q ≠ 0` and `det (sI − A) ≠ 0` (then `det Â(s) ≠ 0`, `det_pccA`), the transfer
matrix is
`R Â(s)⁻¹ N̂(s) Rᵀ`. Unlike `transfer_pccModel` it needs no `M s² + D s ≠ 0`: the swing
denominator is cleared into `Â`, `N̂`. Proof: with `Ŷ = Â⁻¹ N̂`, the channel response
`Ĉ = ((I − Z_oc Ŷ)₁ / E', −ω_q (Ĉ_p Ŷ − Ĉ_v)₁ / (s + ω_q))` solves the rotated line and channel
equations (the two rows of `Â Ŷ = N̂`); rotate back (`transfer_pccModel_of_response`). -/
@[tmio M, powerlib_domain] theorem transfer_pccModel_eq_rot (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq qf : ℝ} {v : Fin 2 → ℝ} {s : ℂ} (hE : g.emfMag qf ≠ 0) (hq : s + (g.ωq : ℂ) ≠ 0)
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A s).det ≠ 0) :
    transfer (g.pccModel δ id iq qf v) s = complexify (Transform.rot δ) *
      ((g.pccA δ qf v s)⁻¹ * g.pccN δ id iq qf s) * complexify (Transform.rot δ)ᵀ := by
  set Rc := complexify (Transform.rot δ) with hRc
  set Rt := complexify (Transform.rot δ)ᵀ with hRt
  set Z := g.branch.dqImpedance g.ω0 s with hZdef
  set Cp := complexify (pccCi ![Transform.parkD δ (v 0) (v 1), Transform.parkQ δ (v 0) (v 1)])
    with hCp
  set Cv := complexify (curC (Transform.parkD δ id iq) (Transform.parkQ δ id iq)) with hCv
  set Yh := (g.pccA δ qf v s)⁻¹ * g.pccN δ id iq qf s with hYh
  have hP := g.det_pccA_ne_zero hM hL hA
  have hAY : g.pccA δ qf v s * Yh = g.pccN δ id iq qf s := by
    rw [hYh, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP),
      Matrix.one_mul]
  -- the two rows of `Â Ŷ = N̂`: `diag(s + ω_q, M s² + D s) (I − Z Ŷ) = [[0, n_q ω_q], [E', 0]] Q`
  set Mm := 1 - Z * Yh with hMm
  set Q := Cp * Yh - Cv with hQ
  have key : g.chanDen s * Mm = g.chanScaledB qf * Q := by
    have h := hAY
    simp only [pccA, pccN, ← hZdef, ← hCp, ← hCv, Matrix.add_mul, Matrix.mul_assoc] at h
    rw [hMm, hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, sub_eq_sub_iff_add_eq_add, ← h]
    abel
  have ek : ∀ i k : Fin 2, (g.chanDen s * Mm) i k = (g.chanScaledB qf * Q) i k :=
    fun i k => by rw [key]
  have hE' : (g.emfMag qf : ℂ) ≠ 0 := by exact_mod_cast hE
  set Ch : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i k =>
    ![Mm 1 k / g.emfMag qf, -(g.ωq : ℂ) * Q 1 k / (s + g.ωq)] i with hCh
  -- the rotated line and channel equations
  have hl : Z * Yh + complexify !![0, -g.nq; g.emfMag qf, 0] * Ch = 1 := by
    have hB : complexify !![0, -g.nq; g.emfMag qf, 0] * Ch = Mm := by
      ext i k
      have e0 := ek 0 k
      have e1 := ek 1 k
      simp only [chanDen, chanScaledB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one] at e0 e1
      fin_cases i <;>
        simp [complexify, Matrix.mul_apply, Fin.sum_univ_two, hCh]
      · field_simp
        linear_combination -e0
      · field_simp
    rw [hB, hMm]
    abel
  have hc : !![(g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s, 0; 0, s + (g.ωq : ℂ)] * Ch =
      g.chanGain * Q := by
    ext i k
    have e1 := ek 1 k
    simp only [chanDen, chanScaledB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at e1
    fin_cases i <;> simp [chanGain, Matrix.mul_apply, Fin.sum_univ_two, hCh]
    · field_simp
      linear_combination e1
    · field_simp
  -- back to the system frame
  have hRR : Rc * Rt = 1 := rot_mul_rotT δ
  refine g.transfer_pccModel_of_response hM hL hA (Cm := Ch * Rt) ?_ ?_
  · rw [syncB_eq_rot_mul, ← hRc]
    calc Z * (Rc * Yh * Rt) + Rc * complexify !![0, -g.nq; g.emfMag qf, 0] * (Ch * Rt)
        = (Z * Rc) * Yh * Rt + Rc * complexify !![0, -g.nq; g.emfMag qf, 0] * Ch * Rt := by
          simp only [Matrix.mul_assoc]
      _ = Rc * (Z * Yh + complexify !![0, -g.nq; g.emfMag qf, 0] * Ch) * Rt := by
          rw [hZdef, g.dqImpedance_mul_rot δ s, ← hZdef, ← hRc]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hl, Matrix.mul_one, hRR]
  · have hp : complexify (pccCi v) * Rc = Cp := by
      rw [hRc, hCp, ← Matrix.map_mul, pccCi_mul_rot]
    have hv : Cv * Rt = complexify (curC id iq) := by
      rw [hCv, hRt, ← Matrix.map_mul, ← curC_mul_rot δ id iq, Matrix.mul_assoc,
        ← Transform.park_eq_transpose_rot, Transform.rot_mul_park, Matrix.mul_one]
    calc !![(g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s, 0; 0, s + (g.ωq : ℂ)] * (Ch * Rt)
        = (g.chanGain * Q) * Rt := by rw [← Matrix.mul_assoc, hc]
      _ = g.chanGain * (complexify (pccCi v) * (Rc * Yh * Rt) - complexify (curC id iq)) := by
          rw [← hv, hQ, ← hp]
          simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]

/-- The PCC active power in the frame of the source angle, `P_p = v_a i_a + v_b i_b`
(`(v_a, v_b) = Rᵀ v₀`, `(i_a, i_b) = Rᵀ i₀`; it equals `v₀ · i₀`). -/
def pccPower (δ id iq : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  Transform.parkD δ (v 0) (v 1) * Transform.parkD δ id iq +
    Transform.parkQ δ (v 0) (v 1) * Transform.parkQ δ id iq

/-- Along `s = jω`, `Re (N̂ Âᴴ)₀₀` as a polynomial in `x = ω²`:
`ω_q² (R − n_q (R i_b + X i_a − v_b) − n_q² P_p) + x (R + n_q ω_q L i_b)`, where
`(v_a, v_b) = Rᵀ v₀` and `(i_a, i_b) = Rᵀ i₀` are the PCC voltage and the current along and
across the EMF and `P_p` is the PCC power (`pccPower`). -/
def pccHerm0 (δ id iq : ℝ) (v : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  let vb := Transform.parkQ δ (v 0) (v 1)
  let ia := Transform.parkD δ id iq
  let ib := Transform.parkQ δ id iq
  g.ωq ^ 2 * (g.R - g.nq * (g.R * ib + g.X * ia - vb) - g.nq ^ 2 * pccPower δ id iq v) +
    x * (g.R + g.nq * g.ωq * g.L * ib)

/-- The coefficient of `x = ω²` in `Re (N̂ Âᴴ)₁₁`: `D² R − D E' L i_b − E' M (R i_b + X i_a + v_b)`
(`R i_b + X i_a + v_b` is the q-component of `v₀ + (R + jX) i₀` across the EMF, zero at an
equilibrium of the line). -/
def pccHerm1Lin (δ id iq qf : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  g.D ^ 2 * g.R - g.D * g.emfMag qf * g.L * Transform.parkQ δ id iq -
    g.emfMag qf * g.M * (g.R * Transform.parkQ δ id iq + g.X * Transform.parkD δ id iq +
      Transform.parkQ δ (v 0) (v 1))

/-- Along `s = jω`, `Re (N̂ Âᴴ)₁₁` as a polynomial in `x = ω²`:
`E'² P_p + x (D² R − D E' L i_b − E' M (R i_b + X i_a + v_b)) + x² M² R`. -/
def pccHerm1 (δ id iq qf : ℝ) (v : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  g.emfMag qf ^ 2 * pccPower δ id iq v + x * g.pccHerm1Lin δ id iq qf v + x ^ 2 * (g.M ^ 2 * g.R)

/-- Along `s = jω`, the real part of the off-diagonal defect `(N̂ Âᴴ)₀₁ + conj (N̂ Âᴴ)₁₀`:
`E' ω_q (R i_a − X i_b + v_a) + 2 E' n_q ω_q Q_p − x (L i_a (E' + n_q ω_q D) −
n_q ω_q M (v_a − R i_a + X i_b))`, `Q_p = v_b i_a − v_a i_b` the PCC reactive power. -/
def pccDefRe (δ id iq qf : ℝ) (v : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  let va := Transform.parkD δ (v 0) (v 1)
  let vb := Transform.parkQ δ (v 0) (v 1)
  let ia := Transform.parkD δ id iq
  let ib := Transform.parkQ δ id iq
  g.emfMag qf * g.ωq * (g.R * ia - g.X * ib + va) +
    2 * g.emfMag qf * g.nq * g.ωq * (vb * ia - va * ib) -
      x * (g.L * ia * (g.emfMag qf + g.nq * g.ωq * g.D) -
        g.nq * g.ωq * g.M * (va - g.R * ia + g.X * ib))

/-- Along `s = jω`, the imaginary part of the off-diagonal defect divided by `ω`:
`E' (R i_a − X i_b + v_a + L ω_q i_a) + n_q ω_q D (v_a − R i_a + X i_b) + x L M n_q ω_q i_a`. -/
def pccDefIm (δ id iq qf : ℝ) (v : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  let va := Transform.parkD δ (v 0) (v 1)
  let ia := Transform.parkD δ id iq
  let ib := Transform.parkQ δ id iq
  g.emfMag qf * (g.R * ia - g.X * ib + va + g.L * g.ωq * ia) +
    g.nq * g.ωq * g.D * (va - g.R * ia + g.X * ib) + x * (g.L * g.M * g.nq * g.ωq * ia)

/-- The Hermitian data of `N̂(jω) Â(jω)ᴴ` in closed form. -/
@[tmio M, powerlib_domain] private theorem pccHerm_apply (δ id iq qf ω : ℝ) (v : Fin 2 → ℝ)
    (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : G = g.pccN δ id iq qf (ω * Complex.I) * (g.pccA δ qf v (ω * Complex.I))ᴴ) :
    (G 0 0).re = g.pccHerm0 δ id iq v (ω ^ 2) ∧
      (G 1 1).re = g.pccHerm1 δ id iq qf v (ω ^ 2) ∧
        Complex.normSq (G 0 1 + (starRingEnd ℂ) (G 1 0)) =
          g.pccDefRe δ id iq qf v (ω ^ 2) ^ 2 + ω ^ 2 * g.pccDefIm δ id iq qf v (ω ^ 2) ^ 2 := by
  subst hG
  have hs2 : ((ω : ℂ) * Complex.I) ^ 2 = ((-ω ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [mul_pow, Complex.I_sq]; ring
  simp only [pccA_apply, pccN_apply, hs2, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Complex.star_def]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [pccHerm0, pccHerm1, pccHerm1Lin, pccPower, pccDefRe, pccDefIm,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, map_add, map_sub, map_mul, map_neg,
      Complex.conj_ofReal, Complex.conj_I]
    ring

/-- **Positive realness of the PCC-measured admittance at one `s`, reduced.** Under the
hypotheses of `transfer_pccModel_eq_rot`, the admittance is positive real at `s` iff
`N̂(s) Â(s)ᴴ` is: the frame of the source angle is orthogonal
(`PH.positiveRealAt_orthogonal_iff`) and `Ŷ = Â⁻¹ N̂` is not the inverse of an impedance
(`PH.positiveRealAt_inv_mul_iff`). -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_pcc_iff_mul (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) {δ id iq qf : ℝ} {v : Fin 2 → ℝ} {s : ℂ} (hE : g.emfMag qf ≠ 0)
    (hq : s + (g.ωq : ℂ) ≠ 0)
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A s).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.pccModel δ id iq qf v) s) ↔
      PH.PositiveRealAt (g.pccN δ id iq qf s * (g.pccA δ qf v s)ᴴ) := by
  have h := positiveRealAt_orthogonal_iff (Q := (Transform.rot δ)ᵀ)
    (by rw [Matrix.transpose_transpose, ← Transform.park_eq_transpose_rot,
      Transform.park_mul_rot]) ((g.pccA δ qf v s)⁻¹ * g.pccN δ id iq qf s)
  rw [Matrix.transpose_transpose] at h
  rw [g.transfer_pccModel_eq_rot hM hL hE hq hA, h,
    PH.positiveRealAt_inv_mul_iff (isUnit_iff_ne_zero.mpr (g.det_pccA_ne_zero hM hL hA))]

/-- **Positive-real criterion of the PCC-measured droop admittance at `jω`** (exact, at every
operating point and every frequency off the poles, `ω = 0` included): with `x = ω²` the port
admittance is positive real at `jω` iff the Hermitian part of `N̂ Âᴴ` has nonnegative trace and
determinant, `h₀(x) + h₁(x) ≥ 0` and `β_r(x)² + x β_i(x)² ≤ 4 h₀(x) h₁(x)` (`pccHerm0`,
`pccHerm1`, `pccDefRe`, `pccDefIm`: polynomials in `x` of degrees 1, 2, 1, 1 in the model data,
the PCC voltage and the current along and across the EMF). Generic laws:
`PH.positiveRealAt_inv_mul_iff`, `PH.positiveRealAt_fin_two_iff_trace`. -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_pcc_iff (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) {δ id iq qf ω : ℝ} {v : Fin 2 → ℝ} (hE : g.emfMag qf ≠ 0)
    (hq : (ω : ℂ) * Complex.I + (g.ωq : ℂ) ≠ 0)
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A (ω * Complex.I)).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.pccModel δ id iq qf v) (ω * Complex.I)) ↔
      0 ≤ g.pccHerm0 δ id iq v (ω ^ 2) + g.pccHerm1 δ id iq qf v (ω ^ 2) ∧
        g.pccDefRe δ id iq qf v (ω ^ 2) ^ 2 + ω ^ 2 * g.pccDefIm δ id iq qf v (ω ^ 2) ^ 2 ≤
          4 * g.pccHerm0 δ id iq v (ω ^ 2) * g.pccHerm1 δ id iq qf v (ω ^ 2) := by
  obtain ⟨h0, h1, h2⟩ := g.pccHerm_apply δ id iq qf ω v _ rfl
  rw [g.positiveRealAt_transfer_pcc_iff_mul hM hL hE hq hA,
    PH.positiveRealAt_fin_two_iff_trace, h0, h1, h2]

/-- The d-component, in the frame of the source angle, of `v₀ + (R + jX) i₀`:
`R i_a − X i_b + v_a`, the EMF the line drop implies along the source angle (`= E'` at an
equilibrium of the line). -/
def lineEmfD (δ id iq : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  g.R * Transform.parkD δ id iq - g.X * Transform.parkQ δ id iq + Transform.parkD δ (v 0) (v 1)

/-- **Constant EMF, PCC-measured, at `jω`.** Without droop (`n_q = 0`, `ω_q ≠ 0`) the
reactive channel decouples (`h₀ = R (ω_q² + ω²)` and the defect carries the factor
`ω_q² + ω²`): the admittance is positive real at `jω` iff `R ≥ 0`, `h₁(ω²) ≥ 0` and
`E² ((R i_a − X i_b + v_a)² + ω² L² i_a²) ≤ 4 R h₁(ω²)` (`lineEmfD`, `pccHerm1`). -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_pcc_iff_of_nq_eq_zero
    (hn : g.nq = 0) (hM : g.M ≠ 0) (hL : g.L ≠ 0) (hq : g.ωq ≠ 0) {δ id iq qf ω : ℝ}
    {v : Fin 2 → ℝ} (hE : g.E ≠ 0)
    (hA : (characteristicMatrix (g.pccModel δ id iq qf v).A (ω * Complex.I)).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.pccModel δ id iq qf v) (ω * Complex.I)) ↔
      0 ≤ g.R ∧ 0 ≤ g.pccHerm1 δ id iq qf v (ω ^ 2) ∧
        g.E ^ 2 * (g.lineEmfD δ id iq v ^ 2 + ω ^ 2 * g.L ^ 2 * Transform.parkD δ id iq ^ 2) ≤
          4 * g.R * g.pccHerm1 δ id iq qf v (ω ^ 2) := by
  have hEm : g.emfMag qf = g.E := by simp [emfMag, hn]
  have hq' : (ω : ℂ) * Complex.I + (g.ωq : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hq this
  rw [g.positiveRealAt_transfer_pcc_iff hM hL (by rw [hEm]; exact hE) hq' hA]
  have h0 : g.pccHerm0 δ id iq v (ω ^ 2) = g.R * (g.ωq ^ 2 + ω ^ 2) := by
    simp only [pccHerm0, hn]; ring
  have hd : g.pccDefRe δ id iq qf v (ω ^ 2) ^ 2 + ω ^ 2 * g.pccDefIm δ id iq qf v (ω ^ 2) ^ 2 =
      (g.ωq ^ 2 + ω ^ 2) * (g.E ^ 2 *
        (g.lineEmfD δ id iq v ^ 2 + ω ^ 2 * g.L ^ 2 * Transform.parkD δ id iq ^ 2)) := by
    simp only [pccDefRe, pccDefIm, lineEmfD, hn, hEm]; ring
  rw [h0, hd]
  have hτ : 0 < g.ωq ^ 2 + ω ^ 2 := by positivity
  set h1 := g.pccHerm1 δ id iq qf v (ω ^ 2)
  set c := g.E ^ 2 * (g.lineEmfD δ id iq v ^ 2 + ω ^ 2 * g.L ^ 2 * Transform.parkD δ id iq ^ 2)
  have hc : 0 ≤ c := by positivity
  constructor
  · rintro ⟨ht, hdet⟩
    have hdet' : c ≤ 4 * g.R * h1 := by
      have : (g.ωq ^ 2 + ω ^ 2) * c ≤ (g.ωq ^ 2 + ω ^ 2) * (4 * g.R * h1) := by linarith
      exact le_of_mul_le_mul_left this hτ
    have hRh : 0 ≤ g.R * h1 := by linarith
    have hR : 0 ≤ g.R := by
      by_contra hR
      push Not at hR
      have : h1 ≤ 0 := by nlinarith
      nlinarith
    have hh : 0 ≤ h1 := by
      by_contra hh
      push Not at hh
      have : g.R ≤ 0 := by nlinarith
      nlinarith
    exact ⟨hR, hh, hdet'⟩
  · rintro ⟨hR, hh, hdet⟩
    exact ⟨by positivity, by nlinarith⟩

/-- **The loop determinant in closed form**, with the current along and across the EMF,
`(i_a, i_b) = Rᵀ i₀`:
`det W(s) = (M s² + D s + E' i_b)(s + ω_q − ω_q n_q i_b) − n_q ω_q E' i_a²`. -/
@[tmio M, powerlib_domain] theorem det_chanW (δ id iq qf : ℝ) (s : ℂ) :
    (g.chanW δ id iq qf s).det = ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s +
        (g.emfMag qf : ℂ) * (Transform.parkQ δ id iq : ℂ)) *
      (s + (g.ωq : ℂ) - (g.ωq : ℂ) * ((g.nq : ℂ) * (Transform.parkQ δ id iq : ℂ))) -
        (g.nq : ℂ) * (g.ωq : ℂ) * (g.emfMag qf : ℂ) * (Transform.parkD δ id iq : ℂ) ^ 2 := by
  rw [Matrix.det_fin_two, g.chanW_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Transform.parkD, Transform.parkQ]
  push_cast
  ring

end VSMQ

end powerlib.GFM.Line
