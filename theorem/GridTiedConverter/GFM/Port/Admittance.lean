import theorem.GridTiedConverter.GFM.Line.Model
import theorem.Grid.GridImpedance
import theorem.LTI.Plant
import theorem.PH.PositiveReal
import theorem.PH.PositiveRealFinTwo

/-! # Small-signal dq admittance of the grid-forming VSM on an R–L line

The port of the Layer-0 grid-forming source (`Line.VSM`, `Line.VSMLPF`,
`theorem/GridTiedConverter/GFM/Line/Model.lean`) seen from its terminal: the PCC voltage replaces
the stiff grid as an input, the linearization at an operating point is a `Linear.Plant`, and its
transfer matrix is the closed-form admittance `Y(s) = (Z_oc(s) + g(s) J v_c v_cᵀ)⁻¹`: the
open-circuit line impedance plus a rank-one synchronization term.

Model boundary.
* The laws of `Line.VSM` (state `(δ, ω, i_d, i_q)`) and `Line.VSMLPF` (state
  `(δ, ω, P_f, i_d, i_q)`), in these orders: dq frame rotating at the nominal `ω₀`, constant EMF
  magnitude `E`, `δ̇ = ω`, `M ω̇ = P_ref − P_m − D ω` with `P_m = P_e` or the filtered
  `Ṗ_f = ω_c (P_e − P_f)`, `P_e = E (cos δ i_d + sin δ i_q)` (export-positive, per unit without
  `3/2`), line current `i` out of the converter. The stiff grid `V ∠ 0` is replaced by the PCC
  voltage `v = (v_d, v_q)` (`VSM.portField`, `VSMLPF.portField`):
  `L i̇ = E e^{jδ} − v − (R + jX) i`, `X = ω₀ L`; at `v = (V, 0)` this is the model's field
  (`portField_grid`).
* Small signal at an operating point `(δ₀, i₀)` (any PCC operating voltage: `v` enters affinely,
  `portField_eq`): state matrix the model's Jacobian (`Line.VSM.jacobian`,
  `Line.VSMLPF.jacobian`, derived by `fderiv` there; `hasFDerivAt_portField`), input matrix
  `portB` (`−1/L` on the current rows), output the IN-positive port current `−i` (`portC`,
  work-sync `conventions.md` §D1, as the GFL admittance), no feedthrough.
  `Q_c = Q_e(δ₀, i₀) = E (sin δ₀ i_d0 − cos δ₀ i_q0)` is the reactive power at the source,
  `v_c = E (cos δ₀, sin δ₀)` (`Network.emfC`), `J = [[0, −1], [1, 0]]`.
* Excluded: reactive / voltage loop (constant `E`; the Q–V droop law and the PCC-measured powers
  are `theorem/GridTiedConverter/GFM/Port/DroopAdmittance.lean`; this is Layer 0 of the port:
  virtual impedance, PI voltage and current loops, LC filter and delay are the 15-state
  realization of `theorem/GridTiedConverter/GFM/Port/CascadeAdmittance.lean`), limits, PLL,
  PWM. Frequency-domain statements at a fixed `s`; no time-domain or stability claim.

Source: GFM port-structure study note (t1-port, §(a) closed form, §(b) passivity; derivation and
symbolic checks `a1_closed_form.py`); the GFL counterpart
`theorem/GridTiedConverter/GFL/Impedance/Admittance.lean`; work-sync
`theory/T-gfl-impedance.md` §1.7 (network side).

Results.
* The two-channel port law `PH.syncY` of `theorem/PH/PositiveRealFinTwo.lean` (used by every
  layer of the port): a source behind its line with `N i + T v = B c` and channels
  `c = −K (C_i i + C_v v)` has the admittance `(N + B K C_i)⁻¹ (T + B K C_v)`
  (`PH.syncY_spec`). Layer 0 (this module)
  is the one-channel instance `N = Z_oc`, `T = I`, `B = J v_c v_cᵀ`, `K = g I`, `C_i = I`,
  `C_v = 0` (`Network.inv_portZ_eq_syncY`, `Network.portZ_mul_syncY`, through which
  `VSM.transfer_portModel` and `VSMLPF.transfer_portModel` are proved); the Q–V droop and the
  inner cascade are the instances of `theorem/GridTiedConverter/GFM/Port/DroopAdmittance.lean`
  and `theorem/GridTiedConverter/GFM/Port/CascadeAdmittance.lean`.
* `Network.portZ δ γ s = Z_oc(s) + γ J v_c v_cᵀ` (`Z_oc` the dq impedance of the line branch,
  `Passive.SeriesRLC.dqImpedance`). Passivity at one frequency (`PH.PositiveRealAt`,
  `Re uᴴ (Z + Zᴴ) u ≥ 0`): in the frame of the source angle the impedance is
  `Z_oc + γ E² J e₁ e₁ᵀ`, the Hermitian part at `jω` is `2R + (traceless part)` with eigenvalues
  `2R ± E² |γ|`, so `Network.portZ δ γ (jω)` is positive real iff `E² |γ| ≤ 2R`, for every `E`
  (`Network.positiveRealAt_portZ_iff`, from the generic laws `PH.positiveRealAt_orthogonal_iff`
  and `PH.positiveRealAt_complexSymm_add_iff` of `theorem/PH/PositiveRealFinTwo.lean`).
* VSM (four states): `VSM.portField_eq`, `VSM.portField_grid`, `VSM.hasFDerivAt_portField`;
  `VSM.portModel` and `VSM.transfer_portModel`: off the poles (`M s² + D s ≠ Q_c`,
  `det (Z_oc + Z_c) ≠ 0`, `det (sI − A) ≠ 0`) the transfer matrix is `VSM.portY`, the closed form
  with `g(s) = 1/(M s² + D s − Q_c)` (`VSM.syncGain`). On a network: `VSM.gfmOnNetwork`,
  `VSM.gfmOnNetwork_returnDifference` (with the network realization of
  `theorem/Grid/GridImpedance.lean` as source, the return difference is `det (I + Z_ext Y)`).
  Passivity: `Y(jω)` is positive real iff `E² |g(jω)| ≤ 2R` (`VSM.positiveRealAt_transfer_iff`);
  `g` depends on the operating point only through `Q_c`, not the exported power, so the
  non-passivity is load-sign independent (unlike the GFL's negative conductance when exporting).
  At DC `g(0) = −1/Q_c`: passive iff `E² ≤ 2R |Q_c|` (`VSM.positiveRealAt_transfer_zero_iff`); a
  lossless line is non-passive at every frequency (`VSM.not_positiveRealAt_transfer_of_lossless`).
* VSM + power filter (five states): `VSMLPF.portField_eq`, `VSMLPF.portField_grid`,
  `VSMLPF.hasFDerivAt_portField`, `VSMLPF.portModel`, `VSMLPF.transfer_portModel` with the filtered
  gain `g(s) = F/(M s² + D s − F Q_c)`, `F = ω_c/(s + ω_c)` (`VSMLPF.syncGain`), and
  `VSMLPF.positiveRealAt_transfer_iff`.

Family and connection conclusions.
* None: realization identities and frequency-wise static facts (static evidence). The behaviour
  of the source–network interconnection is that of `Grid.Interconnection.family`; the behaviour
  of the VSM itself is that of the families of `theorem/GridTiedConverter/GFM/Line/VSM.lean`.
-/

noncomputable section
namespace powerlib.GFM.Line
open Matrix Linear
open powerlib.Dynamics (State)
open powerlib.Grid (withNetwork networkModel networkModel_transfer Zext)
open powerlib.PH (syncY syncY_spec positiveRealAt_orthogonal_iff
  positiveRealAt_complexSymm_add_iff)

namespace Network

variable (N : Network)

/-! ## The port impedance of a power-synchronized source behind the line -/

/-- The source voltage `v_c = E (cos δ₀, sin δ₀)` as a complex vector. -/
def emfC (δ : ℝ) : Fin 2 → ℂ := ![(N.E * Real.cos δ : ℝ), (N.E * Real.sin δ : ℝ)]

/-- The port impedance `Z_oc(s) + γ J v_c v_cᵀ` of the source behind the line whose angle answers
the power through the gain `γ` (`J = [[0, −1], [1, 0]]`, `Z_oc` the dq impedance of the line
branch); the synchronization laws supply `γ = g(s)` (`VSM.syncGain`, `VSMLPF.syncGain`). -/
def portZ (δ : ℝ) (γ s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  N.branch.dqImpedance N.ω0 s +
    γ • (Transform.complexSymm (0 : ℂ) 1 * vecMulVec (N.emfC δ) (N.emfC δ))

/-- The entries of `Z_oc + γ J v_c v_cᵀ`. -/
@[tmio M, powerlib_domain] private theorem portZ_apply (δ : ℝ) (γ s : ℂ) :
    N.portZ δ γ s = !![N.R + N.L * s - γ *
        ((N.E * Real.sin δ : ℝ) * (N.E * Real.cos δ : ℝ)),
      -(N.X : ℂ) - γ * ((N.E * Real.sin δ : ℝ) * (N.E * Real.sin δ : ℝ));
      (N.X : ℂ) + γ * ((N.E * Real.cos δ : ℝ) * (N.E * Real.cos δ : ℝ)),
      N.R + N.L * s +
        γ * ((N.E * Real.cos δ : ℝ) * (N.E * Real.sin δ : ℝ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [portZ, emfC, Network.branch, Passive.SeriesRLC.dqImpedance,
      Transform.complexSymm, vecMulVec, Network.X, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- **Layer 0 of the port law.** The inverse port impedance is `syncY` with one channel:
`N = Z_oc`, `T = I`, `B = J v_c v_cᵀ`, `K = γ I`, `C_i = I`, `C_v = 0`. -/
@[tmio M, powerlib_domain] theorem inv_portZ_eq_syncY (δ : ℝ) (γ s : ℂ) :
    (N.portZ δ γ s)⁻¹ = syncY (N.branch.dqImpedance N.ω0 s) 1
      (Transform.complexSymm (0 : ℂ) 1 * vecMulVec (N.emfC δ) (N.emfC δ)) (γ • 1) 1 0 := by
  simp [portZ, syncY]

/-- The port equation of Layer 0, read from the port law (`PH.syncY_spec`). -/
@[tmio M, powerlib_domain] theorem portZ_mul_syncY {δ : ℝ} {γ s : ℂ}
    (hZ : (N.portZ δ γ s).det ≠ 0) :
    N.portZ δ γ s * syncY (N.branch.dqImpedance N.ω0 s) 1
      (Transform.complexSymm (0 : ℂ) 1 * vecMulVec (N.emfC δ) (N.emfC δ)) (γ • 1) 1 0 = 1 := by
  have e : N.branch.dqImpedance N.ω0 s + Transform.complexSymm (0 : ℂ) 1 *
      vecMulVec (N.emfC δ) (N.emfC δ) * (γ • 1) * 1 = N.portZ δ γ s := by
    simp [portZ]
  have h := syncY_spec (T := 1) (Cv := 0) (by rw [e]; exact hZ)
  rwa [e, Matrix.mul_zero, add_zero] at h

/-- **The port impedance in the frame of the source angle.** `Rᵀ (Z_oc + γ J v_c v_cᵀ) R` is
`Z_oc + γ E² J e₁ e₁ᵀ` (`Z_oc` commutes with the rotation, `Rᵀ v_c = E e₁`). -/
@[tmio M, powerlib_domain] private theorem rot_portZ (δ : ℝ) (γ s : ℂ) :
    complexify (Transform.rot δ)ᵀ * N.portZ δ γ s * complexify (Transform.rot δ) =
      Transform.complexSymm ((N.R : ℂ) + N.L * s) ((N.X : ℝ) : ℂ) + !![0, 0; γ * N.E ^ 2, 0] := by
  have hcs : Complex.cos (δ : ℂ) ^ 2 + Complex.sin (δ : ℂ) ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  rw [← Transform.park_eq_transpose_rot, portZ_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Transform.park, Transform.rot, Transform.complexSymm, Matrix.mul_apply,
      Fin.sum_univ_two]
  · linear_combination ((N.R : ℂ) + N.L * s) * hcs
  · linear_combination (-(N.X : ℂ)) * hcs
  · linear_combination ((N.X : ℂ) + γ * N.E ^ 2 *
      (Complex.cos (δ : ℂ) ^ 2 + Complex.sin (δ : ℂ) ^ 2 + 1)) * hcs
  · linear_combination ((N.R : ℂ) + N.L * s) * hcs

/-- **Passivity of the port impedance at one frequency.** The Hermitian part of
`Z_oc(jω) + γ J v_c v_cᵀ` has the eigenvalues `2R ± E² |γ|` (`Z_oc` contributes `2R`, the
rank-one term is traceless); it is positive real iff `E² |γ| ≤ 2R`. Read in the frame of the
source angle (`PH.positiveRealAt_orthogonal_iff`) through the generic law
`PH.positiveRealAt_complexSymm_add_iff`. -/
@[tmio M, powerlib_domain] theorem positiveRealAt_portZ_iff (δ : ℝ) (γ : ℂ) (ω : ℝ) :
    PH.PositiveRealAt (N.portZ δ γ (ω * Complex.I)) ↔ N.E ^ 2 * ‖γ‖ ≤ 2 * N.R := by
  rw [← positiveRealAt_orthogonal_iff (Q := Transform.rot δ)
    (by rw [← Transform.park_eq_transpose_rot, Transform.rot_mul_park]), N.rot_portZ,
    positiveRealAt_complexSymm_add_iff _ _ (by simp)]
  have hre : ((N.R : ℂ) + N.L * (ω * Complex.I)).re = N.R := by simp
  have hn : Complex.normSq ((0 : ℂ) + (starRingEnd ℂ) (γ * N.E ^ 2)) =
      (N.E ^ 2 * ‖γ‖) ^ 2 := by
    rw [zero_add, Complex.normSq_conj, Complex.normSq_mul, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_abs]
    rw [abs_of_nonneg (by positivity)]
    ring
  simp only [hre, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.zero_re, hn]
  have hg : 0 ≤ N.E ^ 2 * ‖γ‖ := by positivity
  constructor
  · rintro ⟨h0, h1⟩
    have h2 : (N.E ^ 2 * ‖γ‖) ^ 2 ≤ (2 * N.R) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hg (by linarith) two_ne_zero).mp h2
  · intro h
    have h0 : 0 ≤ N.R := by linarith
    exact ⟨h0, by nlinarith [pow_le_pow_left₀ hg h 2]⟩

end Network

namespace VSM

variable (g : VSM)

/-! ## The port field and its linearization -/

/-- The VSM field with the PCC voltage `v = (v_d, v_q)` in place of the stiff grid `V ∠ 0`. -/
def portField (x : State 4) (v : Fin 2 → ℝ) : State 4 :=
  WithLp.toLp 2 ![x 1, (g.Pref - g.power (x 0) (x 2) (x 3) - g.D * x 1) / g.M,
    (g.E * Real.cos (x 0) - v 0 - g.R * x 2 + g.X * x 3) / g.L,
    (g.E * Real.sin (x 0) - v 1 - g.R * x 3 - g.X * x 2) / g.L]

/-- The input matrix `∂f/∂v`: `−1/L` on the two current rows. -/
def portB : Matrix (Fin 4) (Fin 2) ℝ := !![0, 0; 0, 0; -(1 / g.L), 0; 0, -(1 / g.L)]

/-- The output matrix: the IN-positive port current `−(i_d, i_q)`. -/
def portC : Matrix (Fin 2) (Fin 4) ℝ := !![0, 0, -1, 0; 0, 0, 0, -1]

/-- The voltage channel is affine: `f(x, v) = f(x) + B (v − (V, 0))`. -/
@[tmio M, powerlib_domain] theorem portField_eq (x : State 4) (v : Fin 2 → ℝ) :
    g.portField x v = g.field x + WithLp.toLp 2 (g.portB *ᵥ (v - ![g.V, 0])) := by
  ext i
  fin_cases i <;>
    simp [portField, field, portB, Network.rateD, Network.rateQ, Matrix.vecHead,
      Matrix.vecTail] <;> ring

/-- At the stiff-grid voltage `(V, 0)` the port field is the model's field. -/
@[tmio M, powerlib_domain] theorem portField_grid (x : State 4) :
    g.portField x ![g.V, 0] = g.field x := by
  rw [portField_eq, sub_self, mulVec_zero]
  simp

/-- At every PCC voltage the state Jacobian of the port field is the model's Jacobian. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_portField (x : State 4) (v : Fin 2 → ℝ) :
    HasFDerivAt (fun y => g.portField y v)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (g.jacobian (x 0) (x 2) (x 3))) x := by
  simp only [portField_eq]
  exact (g.hasFDerivAt_field x).add_const _

/-- The small-signal port model at the operating point `(δ₀, i_d0, i_q0)`: input the PCC voltage
perturbation, output the IN-positive current perturbation. -/
def portModel (δ id iq : ℝ) : Plant 4 2 := ⟨g.jacobian δ id iq, g.portB, portC, 0⟩

/-- The realization is strictly proper. -/
@[tmio M, powerlib_domain] theorem portModel_D (δ id iq : ℝ) : (g.portModel δ id iq).D = 0 :=
  rfl

/-! ## The closed form -/

/-- The synchronization gain `g(s) = 1/(M s² + D s − Q_c)`, `Q_c = Q_e(δ₀, i₀)`. -/
def syncGain (δ id iq : ℝ) (s : ℂ) : ℂ :=
  1 / ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ))

/-- The closed-form port admittance `Y(s) = (Z_oc(s) + g(s) J v_c v_cᵀ)⁻¹`. -/
def portY (δ id iq : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g.portZ δ (g.syncGain δ id iq s) s)⁻¹

/-- **The realization has the closed-form admittance.** Off the poles, the transfer matrix of the
port model is `(Z_oc + Z_c)⁻¹`. Proof: the state response `(Δδ, s Δδ, −Y e_c)`,
`Δδ = g(s) v_cᵀ Y e_c`, solves `(sI − A) X = B` (`LTI.transfer_eq_of_solution`). -/
@[tmio M, powerlib_domain] theorem transfer_portModel (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq : ℝ} {s : ℂ}
    (hden : (g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ) ≠ 0)
    (hZ : (g.portZ δ (g.syncGain δ id iq s) s).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq).A s).det ≠ 0) :
    transfer (g.portModel δ id iq) s = g.portY δ id iq s := by
  set Y := g.portY δ id iq s with hYdef
  have hY : g.portZ δ (g.syncGain δ id iq s) s * Y = 1 := by
    rw [hYdef, portY, Network.inv_portZ_eq_syncY]
    exact g.portZ_mul_syncY hZ
  set γ := g.syncGain δ id iq s with hγ
  have hγd : γ * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ)) = 1 := by
    rw [hγ, syncGain, one_div, inv_mul_cancel₀ hden]
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  set c := ((g.E * Real.cos δ : ℝ) : ℂ) with hc
  set sn := ((g.E * Real.sin δ : ℝ) : ℂ) with hsn
  -- The four scalar port equations `(Z_oc + Z_c) Y = 1`.
  have e : ∀ i k : Fin 2,
      (g.portZ δ (g.syncGain δ id iq s) s * Y) i k = (1 : Matrix (Fin 2) (Fin 2) ℂ) i k :=
    fun i k => by rw [hY]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  rw [Network.portZ_apply] at e00 e01 e10 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), ← hc, ← hsn] at e00 e01 e10 e11
  rw [← hγ] at e00 e01 e10 e11
  simp only [Network.X, Complex.ofReal_mul] at e00 e01 e10 e11
  -- The state response along the input direction `e_k`.
  set dδ : Fin 2 → ℂ := fun k => γ * (c * Y 0 k + sn * Y 1 k) with hdδ
  set X : Matrix (Fin 4) (Fin 2) ℂ :=
    Matrix.of fun i k => ![dδ k, s * dδ k, -Y 0 k, -Y 1 k] i with hX
  have hMX : characteristicMatrix (g.portModel δ id iq).A s * X =
      complexify (g.portModel δ id iq).B := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [characteristicMatrix, complexify, portModel, jacobian, portB, Matrix.mul_apply,
        Fin.sum_univ_four, hX, hdδ, Network.X, ← hc, ← hsn]
    · linear_combination (norm := (field_simp; ring)) (c * Y 0 0 + sn * Y 1 0) / (g.M : ℂ) * hγd
    · linear_combination (norm := (field_simp; ring)) (c * Y 0 1 + sn * Y 1 1) / (g.M : ℂ) * hγd
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e00
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e10
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e11
  rw [LTI.transfer_eq_of_solution _ _ _ hA hMX]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [portModel, portC, complexify, hX, Matrix.mul_apply, Fin.sum_univ_four]

/-! ## On a network -/

/-- The GFM port model as the load of the grid-side network of `theorem/Grid/GridImpedance.lean`
(its input is the IN-positive converter current, its output `−v_PCC`). -/
def gfmOnNetwork (line : Passive.SeriesRLC) (shunt : Passive.ParallelRLC) (δ id iq : ℝ) :
    Grid.Interconnection 4 4 2 :=
  withNetwork line shunt g.ω0 (g.portModel δ id iq) (g.portModel_D δ id iq)

/-- Return difference of the GFM–network interconnection: `det (I + Z_ext Y_gfm)`. -/
@[tmio M, powerlib_domain] theorem gfmOnNetwork_returnDifference {line : Passive.SeriesRLC}
    {shunt : Passive.ParallelRLC} (hS : line.S = 0) (hΓ : shunt.Γ = 0) (hC : shunt.C ≠ 0)
    (hLg : line.L ≠ 0) (hM : g.M ≠ 0) (hL : g.L ≠ 0) {δ id iq : ℝ} {s : ℂ}
    (hMn : (characteristicMatrix (networkModel line shunt g.ω0).A s).det ≠ 0)
    (hYn : (shunt.dqAdmittance g.ω0 s).det ≠ 0) (hZn : (line.dqImpedance g.ω0 s).det ≠ 0)
    (hden : (g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s - (g.reactive δ id iq : ℂ) ≠ 0)
    (hZ : (g.portZ δ (g.syncGain δ id iq s) s).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq).A s).det ≠ 0) :
    (g.gfmOnNetwork line shunt δ id iq).returnDifference s =
      (1 + Zext line shunt g.ω0 s * g.portY δ id iq s).det := by
  change (1 + transfer (networkModel line shunt g.ω0) s * transfer (g.portModel δ id iq) s).det = _
  rw [networkModel_transfer hS hΓ hC hLg hMn hYn hZn, g.transfer_portModel hM hL hden hZ hA]

/-! ## Passivity at one frequency -/

/-- **Passivity of the realization at one frequency.** Off the poles, the port admittance of the
GFM at `jω` is positive real iff `E² |g(jω)| ≤ 2R` (`positiveRealAt_portZ_iff` through
`PH.positiveRealAt_inv_iff`). -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq ω : ℝ}
    (hden : (g.M : ℂ) * (ω * Complex.I) ^ 2 + (g.D : ℂ) * (ω * Complex.I) -
      (g.reactive δ id iq : ℂ) ≠ 0)
    (hZ : (g.portZ δ (g.syncGain δ id iq (ω * Complex.I)) (ω * Complex.I)).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq).A (ω * Complex.I)).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.portModel δ id iq) (ω * Complex.I)) ↔
      g.E ^ 2 * ‖g.syncGain δ id iq (ω * Complex.I)‖ ≤ 2 * g.R := by
  rw [g.transfer_portModel hM hL hden hZ hA, portY,
    PH.positiveRealAt_inv_iff (isUnit_iff_ne_zero.mpr hZ)]
  exact g.positiveRealAt_portZ_iff δ _ ω

/-- **DC passivity.** With `g(0) = −1/Q_c`, the port admittance at `s = 0` is positive real iff
`E² ≤ 2R |Q_c|`: the power regulation makes the port non-passive at DC unless the source carries
reactive power `|Q_c| ≥ E²/(2R)`, whatever the exported active power. -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_zero_iff (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) {δ id iq : ℝ} (hQ : g.reactive δ id iq ≠ 0)
    (hZ : (g.portZ δ (g.syncGain δ id iq 0) 0).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq).A 0).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.portModel δ id iq) 0) ↔
      g.E ^ 2 ≤ 2 * g.R * |g.reactive δ id iq| := by
  have h0 : ((0 : ℝ) : ℂ) * Complex.I = 0 := by simp
  have hden : (g.M : ℂ) * (((0 : ℝ) : ℂ) * Complex.I) ^ 2 +
      (g.D : ℂ) * (((0 : ℝ) : ℂ) * Complex.I) - (g.reactive δ id iq : ℂ) ≠ 0 := by
    simpa using hQ
  have h := g.positiveRealAt_transfer_iff hM hL hden (by rwa [h0]) (by rwa [h0])
  rw [h0] at h
  rw [h]
  have hg : ‖g.syncGain δ id iq 0‖ = 1 / |g.reactive δ id iq| := by
    simp [syncGain, Complex.norm_real]
  rw [hg]
  have hQa : 0 < |g.reactive δ id iq| := abs_pos.mpr hQ
  rw [mul_one_div, div_le_iff₀ hQa]

/-- **A lossless line is non-passive at every frequency.** With `R = 0` and `E ≠ 0`, the port
admittance is not positive real at any `jω` off the poles (`E² |g(jω)| > 0`). -/
@[tmio M, powerlib_domain] theorem not_positiveRealAt_transfer_of_lossless (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) (hE : g.E ≠ 0) (hR : g.R = 0) {δ id iq ω : ℝ}
    (hden : (g.M : ℂ) * (ω * Complex.I) ^ 2 + (g.D : ℂ) * (ω * Complex.I) -
      (g.reactive δ id iq : ℂ) ≠ 0)
    (hZ : (g.portZ δ (g.syncGain δ id iq (ω * Complex.I)) (ω * Complex.I)).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq).A (ω * Complex.I)).det ≠ 0) :
    ¬ PH.PositiveRealAt (transfer (g.portModel δ id iq) (ω * Complex.I)) := by
  rw [g.positiveRealAt_transfer_iff hM hL hden hZ hA, hR, mul_zero, not_le]
  have hγ : g.syncGain δ id iq (ω * Complex.I) ≠ 0 := by
    simp only [syncGain, one_div, ne_eq, inv_eq_zero]
    exact hden
  have : 0 < ‖g.syncGain δ id iq (ω * Complex.I)‖ := norm_pos_iff.mpr hγ
  positivity

end VSM

/-! ## The VSM with a power filter (five states) -/

namespace VSMLPF

variable (g : VSMLPF)

/-- The VSM + power-filter field with the PCC voltage `v` in place of the stiff grid. -/
def portField (x : State 5) (v : Fin 2 → ℝ) : State 5 :=
  WithLp.toLp 2 ![x 1, (g.Pref - x 2 - g.D * x 1) / g.M,
    g.ωc * (g.power (x 0) (x 3) (x 4) - x 2),
    (g.E * Real.cos (x 0) - v 0 - g.R * x 3 + g.X * x 4) / g.L,
    (g.E * Real.sin (x 0) - v 1 - g.R * x 4 - g.X * x 3) / g.L]

/-- The input matrix `∂f/∂v`: `−1/L` on the two current rows. -/
def portB : Matrix (Fin 5) (Fin 2) ℝ :=
  !![0, 0; 0, 0; 0, 0; -(1 / g.L), 0; 0, -(1 / g.L)]

/-- The output matrix: the IN-positive port current `−(i_d, i_q)`. -/
def portC : Matrix (Fin 2) (Fin 5) ℝ := !![0, 0, 0, -1, 0; 0, 0, 0, 0, -1]

/-- The voltage channel is affine: `f(x, v) = f(x) + B (v − (V, 0))`. -/
@[tmio M, powerlib_domain] theorem portField_eq (x : State 5) (v : Fin 2 → ℝ) :
    g.portField x v = g.field x + WithLp.toLp 2 (g.portB *ᵥ (v - ![g.V, 0])) := by
  ext i
  fin_cases i <;>
    simp [portField, field, portB, Network.rateD, Network.rateQ, Matrix.vecHead,
      Matrix.vecTail] <;> ring

/-- At the stiff-grid voltage `(V, 0)` the port field is the model's field. -/
@[tmio M, powerlib_domain] theorem portField_grid (x : State 5) :
    g.portField x ![g.V, 0] = g.field x := by
  rw [portField_eq, sub_self, mulVec_zero]
  simp

/-- At every PCC voltage the state Jacobian of the port field is the model's Jacobian. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_portField (x : State 5) (v : Fin 2 → ℝ) :
    HasFDerivAt (fun y => g.portField y v)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.jacobian (x 0) (x 3) (x 4))) x := by
  simp only [portField_eq]
  exact (g.hasFDerivAt_field x).add_const _

/-- The small-signal port model at `(δ₀, i_d0, i_q0)` (state `(δ, ω, P_f, i_d, i_q)`). -/
def portModel (δ id iq : ℝ) : Plant 5 2 := ⟨g.jacobian δ id iq, g.portB, portC, 0⟩

/-- The realization is strictly proper. -/
@[tmio M, powerlib_domain] theorem portModel_D (δ id iq : ℝ) : (g.portModel δ id iq).D = 0 :=
  rfl

/-- The synchronization gain through the filter `F = ω_c/(s + ω_c)`:
`g(s) = F/(M s² + D s − F Q_c) = ω_c/((s + ω_c)(M s² + D s) − ω_c Q_c)`. -/
def syncGain (δ id iq : ℝ) (s : ℂ) : ℂ :=
  (g.ωc : ℂ) / ((s + g.ωc) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) -
    (g.ωc : ℂ) * (g.reactive δ id iq : ℂ))

/-- The closed-form port admittance `Y(s) = (Z_oc(s) + g(s) J v_c v_cᵀ)⁻¹`. -/
def portY (δ id iq : ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g.portZ δ (g.syncGain δ id iq s) s)⁻¹

/-- **The five-state realization has the closed-form admittance** with the filtered gain. The
state response is `(Δδ, s Δδ, −(M s² + D s) Δδ, −Y e_c)`, `Δδ = g(s) v_cᵀ Y e_c`. -/
@[tmio M, powerlib_domain] theorem transfer_portModel (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq : ℝ} {s : ℂ}
    (hden : (s + g.ωc) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) -
      (g.ωc : ℂ) * (g.reactive δ id iq : ℂ) ≠ 0)
    (hZ : (g.portZ δ (g.syncGain δ id iq s) s).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq).A s).det ≠ 0) :
    transfer (g.portModel δ id iq) s = g.portY δ id iq s := by
  set Y := g.portY δ id iq s with hYdef
  have hY : g.portZ δ (g.syncGain δ id iq s) s * Y = 1 := by
    rw [hYdef, portY, Network.inv_portZ_eq_syncY]
    exact g.portZ_mul_syncY hZ
  set γ := g.syncGain δ id iq s with hγ
  have hγd : γ * ((s + g.ωc) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) -
      (g.ωc : ℂ) * (g.reactive δ id iq : ℂ)) = g.ωc := by
    rw [hγ, syncGain, div_mul_cancel₀ _ hden]
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  set c := ((g.E * Real.cos δ : ℝ) : ℂ) with hc
  set sn := ((g.E * Real.sin δ : ℝ) : ℂ) with hsn
  have e : ∀ i k : Fin 2, (g.portZ δ γ s * Y) i k = (1 : Matrix (Fin 2) (Fin 2) ℂ) i k :=
    fun i k => by rw [hY]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  rw [Network.portZ_apply] at e00 e01 e10 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), ← hc, ← hsn] at e00 e01 e10 e11
  simp only [Network.X, Complex.ofReal_mul] at e00 e01 e10 e11
  set dδ : Fin 2 → ℂ := fun k => γ * (c * Y 0 k + sn * Y 1 k) with hdδ
  set X : Matrix (Fin 5) (Fin 2) ℂ := Matrix.of fun i k =>
    ![dδ k, s * dδ k, -(((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) * dδ k), -Y 0 k, -Y 1 k] i with hX
  have hMX : characteristicMatrix (g.portModel δ id iq).A s * X =
      complexify (g.portModel δ id iq).B := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [characteristicMatrix, complexify, portModel, jacobian, portB, Matrix.mul_apply,
        Fin.sum_univ_five, hX, hdδ, Network.X, ← hc, ← hsn]
    · field_simp
      ring
    · field_simp
      ring
    · linear_combination -(c * Y 0 0 + sn * Y 1 0) * hγd
    · linear_combination -(c * Y 0 1 + sn * Y 1 1) * hγd
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e00
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e01
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e10
    · linear_combination (norm := (field_simp; ring)) (-1 / (g.L : ℂ)) * e11
  rw [LTI.transfer_eq_of_solution _ _ _ hA hMX]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [portModel, portC, complexify, hX, Matrix.mul_apply, Fin.sum_univ_five]

/-- **Passivity of the five-state realization at one frequency**: positive real at `jω` iff
`E² |g(jω)| ≤ 2R`, with the filtered gain (`Network.positiveRealAt_portZ_iff`). -/
@[tmio M, powerlib_domain] theorem positiveRealAt_transfer_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ id iq ω : ℝ}
    (hden : ((ω : ℂ) * Complex.I + g.ωc) * ((g.M : ℂ) * (ω * Complex.I) ^ 2 +
      (g.D : ℂ) * (ω * Complex.I)) - (g.ωc : ℂ) * (g.reactive δ id iq : ℂ) ≠ 0)
    (hZ : (g.portZ δ (g.syncGain δ id iq (ω * Complex.I)) (ω * Complex.I)).det ≠ 0)
    (hA : (characteristicMatrix (g.portModel δ id iq).A (ω * Complex.I)).det ≠ 0) :
    PH.PositiveRealAt (transfer (g.portModel δ id iq) (ω * Complex.I)) ↔
      g.E ^ 2 * ‖g.syncGain δ id iq (ω * Complex.I)‖ ≤ 2 * g.R := by
  rw [g.transfer_portModel hM hL hden hZ hA, portY,
    PH.positiveRealAt_inv_iff (isUnit_iff_ne_zero.mpr hZ)]
  exact g.positiveRealAt_portZ_iff δ _ ω

end VSMLPF

end powerlib.GFM.Line
