import theorem.GridTiedConverter.GFM.Port.DroopAdmittance
import theorem.PH.PositiveRealFinTwo
import theorem.GridTiedConverter.GFM.FullModel.Basic

/-! # Small-signal dq admittance of the grid-forming converter with its inner cascade

The port of the full-order grid-forming converter of
`theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (VSM synchronization with Q–V droop,
quasi-static virtual impedance, PI voltage loop, PI current loop, LC filter, R–L line) with a
Padé(1,1) delay on the bridge voltage, seen from the far end of its line: a 15-state
`Linear.Plant` whose transfer matrix is a closed form of the two-channel port law `PH.syncY` of
`theorem/PH/PositiveRealFinTwo.lean`.

Model boundary.
Small-signal, linear, continuous time; all quantities are perturbations around a fixed operating
point (equilibrium or not); system dq frame rotating at the nominal `ω₀`; per unit, powers
without `3/2`, export-positive (`Transform.pq`); currents out of the converter positive; the
port output is the IN-positive line current `−Δi_g` (work-sync `conventions.md` §D1, as the GFL
admittance and `theorem/GridTiedConverter/GFM/Port/Admittance.lean`), the port input the PCC
voltage `Δv` that replaces the stiff grid `V ∠ 0` of the full model. Parameters: the full-model
`FullModel.Params` (filter `R_f, L_f, C_f`, line `R_g, L_g`, virtual impedance `Z_v = R_v + jX_v`,
gains `K_pv, K_iv, K_pc, K_ic, k_ff, k_dv`, `M, D, n_q, ω_q`; `V, P_ref, E₀, Q_ref` are not
used), the half delay `a = τ_d/2`, the operating angle `δ₀` and the operating values `i₀, v_c0,
i_g0` (system frame) and `u₀` (bridge voltage) as free reals; at a state `x₀` of the full model
these are `convCurrent x₀`, `capVoltage x₀`, `lineCurrent x₀`, `uBridge x₀`.
* State order `(i_d, i_q, v_cd, v_cq, i_gd, i_gq, ξ_d, ξ_q, ζ_d, ζ_q, z_d, z_q, Δδ, Δω, ΔQ_f)`
  (`lin`): filter current, capacitor voltage, line current, current- and voltage-loop PI
  integrators (controller-frame perturbations rotated by the constant `e^{jδ₀}` into the system
  frame, a constant change of coordinates), the two Padé delay states, the angle, the frequency
  and the filtered reactive power. No feedthrough (`model_D`).
* Frame projections (first order in `Δδ`, the controller frame `e^{−jδ}` of the full model):
  `ĩ = Δi − Δδ J i₀`, `ṽ_c = Δv_c − Δδ J v_c0`, `ĩ_g = Δi_g − Δδ J i_g0` (`iT`, `vT`, `gT`),
  `Δu_cmd = e^{jδ₀} Δu^c + Δδ J u₀`.
* Controller (`FullModel.Params.vRef`, `iRef`, `uCtrl` linearized): `Δv* = ΔE e^{jδ₀} − Z_v ĩ_g`,
  `ΔE = −n_q ΔQ_f`; `Δi* = K_pv (Δv* − ṽ_c) + K_iv ζ + k_ff ĩ_g + k_dv jω₀C_f ṽ_c`,
  `ζ̇ = Δv* − ṽ_c`; `Δu^c = K_pc (Δi* − ĩ) + K_ic ξ + ṽ_c + jω₀L_f ĩ`, `ξ̇ = Δi* − ĩ`.
* Delay: `a ż = Δu_cmd − z`, bridge voltage `2 z − Δu_cmd`, i.e. `G_del = (1 − a s)/(1 + a s)`
  (`Gdel`). Plant: `L_f i̇ = u − v_c − Z_f i`, `C_f v̇_c = i − i_g − jω₀C_f v_c`,
  `L_g i̇_g = v_c − Δv − Z_g i_g` (`Z_f = R_f + jω₀L_f`, `Z_g = R_g + jω₀L_g`).
* Outer loop (VSM; the droop + low-pass law is the same field,
  `theorem/GridTiedConverter/GFM/DroopVSM.lean`): `Δδ̇ = Δω`, `M Δω̇ = −ΔP − D Δω`,
  `ΔQ̇_f = ω_q (ΔQ − ΔQ_f)`, powers at the capacitor `P + jQ = v_c conj i_g`:
  `ΔP = v_c0ᵀ Δi_g + i_g0ᵀ Δv_c`, `ΔQ = v_c0,q Δi_gd − v_c0,d Δi_gq + i_g0,d Δv_cq −
  i_g0,q Δv_cd` (`dP`, `dQ`).
* Excluded: current / modulation limits, PLL, DC link, sampling other than the Padé delay,
  frequency-dependent decoupling, unbalance; no stability claim.

Source: GFM port-structure study note (t1-port: closed form of the port admittance, extended
here to the inner cascade); the full-order model of `theorem/GridTiedConverter/GFM/FullModel/
Basic.lean` (D'Arco, Suul, Fosso, Electr. Power Syst. Res. 122 (2015)); work-sync
`theory/T-gfm-control.md` §1.9 (cascaded voltage + current inner loops), §1.12 (impedance
path), `theory/T-impedance-modeling.md` §1.6; the mirrored GFL realization
`theorem/GridTiedConverter/GFL/Impedance/Admittance.lean`.

Results.
* `lin_eq_mulVec`: `model` (`A`, `B`) is exactly the linear map `lin` of the block equations.
* Layers of the closed form (definitions): the inner cascade enters only through the
  complex-scalar Thevenin pair `N = α (I + Y_C Z_g) + β Z_g − G_del F_g`, `T = α Y_C + β`,
  `α = Z_f − G_del F_i`, `β = I − G_del F_v` (`innerN`, `innerT`; `Y_C` the capacitor's dq
  admittance `capY`, `F_i, F_v, F_g` the loop gains `Fi`, `Fv`, `Fg`, `G_v`, `G_c` the PI
  gains `Gv`, `Gc`), the angle through `w = u₀ − F_i i₀ − F_v v_c0 − F_g i_g0` (`angleW`), the
  EMF through `−n_q G_c G_v e^{jδ₀}`, both behind the delay (`chanB`). Along the state response
  the bridge row is `N Δi_g + T Δv = B (Δδ, ΔQ_f)` and the outer loop closes it into the port
  law (the proof of `transfer_eq_Ycasc`).
* `transfer_eq_Ycasc`: off the poles (`s ≠ 0`, `a ≠ 0`, `1 + a s ≠ 0`, `M s² + D s ≠ 0`,
  `s + ω_q ≠ 0`, `det (N + B K C_i) ≠ 0`, `det (sI − A) ≠ 0`, nonzero `L_f, C_f, L_g, M`) the
  transfer matrix of the realization is `Ycasc s = syncY N T B K C_i C_v`
  `= (N + B K C_i)⁻¹ (T + B K C_v)`, with `K = diag(1/(M s² + D s), −ω_q/(s + ω_q))`
  (`chanK`), `C_i = C_p + C_v Z_g` (`measCi`; powers measured inside the line).
* Layer 0 is the same law with the loops removed, `(N, T) = (Z_oc, I)`: the constant-EMF VSM
  (`Line.Network.inv_portZ_eq_syncY`, one channel), the Q–V droop VSM with powers at the source
  (`Line.VSMQ.droopY_eq_syncY`) and at the PCC (`Line.VSMQ.pccY_eq_syncY`,
  `(B, C_i) = (B_c, C_p)`); their realizations `Line.VSM.transfer_portModel`,
  `Line.VSMLPF.transfer_portModel`, `Line.VSMQ.transfer_pccModel` are proved through
  `PH.syncY_spec`, as `transfer_eq_Ycasc` is here.
* On a network: `cascOnNetwork`, `cascOnNetwork_returnDifference`.

Family and connection conclusions.
* None: realization identities (static evidence); no stability claim. The behaviour of the
  converter–network interconnection is that of `Grid.Interconnection.family`.
-/

noncomputable section
namespace powerlib.GFM.Port
open Matrix Linear
open powerlib.Grid (withNetwork networkModel networkModel_transfer Zext)
open powerlib.PH (syncY syncY_spec)

/-- The small-signal port of the full-order GFM: the full-model parameters, the Padé half delay
`a` and the operating point (angle, filter current, capacitor voltage, line current, bridge
voltage; system frame). -/
structure CascadeParams extends FullModel.Params where
  /-- Half of the computation + PWM delay, `a = τ_d/2` (Padé(1,1)). -/
  a : ℝ
  /-- Operating angle `δ₀` of the controller frame. -/
  δ0 : ℝ
  /-- Operating filter current. -/
  i0 : Fin 2 → ℝ
  /-- Operating capacitor voltage. -/
  vc0 : Fin 2 → ℝ
  /-- Operating line current. -/
  ig0 : Fin 2 → ℝ
  /-- Operating bridge voltage. -/
  u0 : Fin 2 → ℝ

namespace CascadeParams

variable (p : CascadeParams)

section Lin
variable {K : Type*} [Field K] [Algebra ℝ K]

/-- Measured filter current in the (rotated) controller frame, `ĩ = Δi − Δδ J i₀`. -/
def iT (x : Fin 15 → K) : Fin 2 → K :=
  ![x 0 + x 12 * algebraMap ℝ K (p.i0 1), x 1 - x 12 * algebraMap ℝ K (p.i0 0)]

/-- Measured capacitor voltage, `ṽ_c = Δv_c − Δδ J v_c0`. -/
def vT (x : Fin 15 → K) : Fin 2 → K :=
  ![x 2 + x 12 * algebraMap ℝ K (p.vc0 1), x 3 - x 12 * algebraMap ℝ K (p.vc0 0)]

/-- Measured line current, `ĩ_g = Δi_g − Δδ J i_g0`. -/
def gT (x : Fin 15 → K) : Fin 2 → K :=
  ![x 4 + x 12 * algebraMap ℝ K (p.ig0 1), x 5 - x 12 * algebraMap ℝ K (p.ig0 0)]

/-- Voltage reference with the virtual impedance, `Δv* = ΔE e^{jδ₀} − Z_v ĩ_g`,
`ΔE = −n_q ΔQ_f`. -/
def vRef (x : Fin 15 → K) : Fin 2 → K :=
  ![-(algebraMap ℝ K p.nq * x 14) * algebraMap ℝ K (Real.cos p.δ0) -
      (algebraMap ℝ K p.Rv * p.gT x 0 - algebraMap ℝ K p.Xv * p.gT x 1),
    -(algebraMap ℝ K p.nq * x 14) * algebraMap ℝ K (Real.sin p.δ0) -
      (algebraMap ℝ K p.Xv * p.gT x 0 + algebraMap ℝ K p.Rv * p.gT x 1)]

/-- Current reference of the PI voltage loop,
`Δi* = K_pv (Δv* − ṽ_c) + K_iv ζ + k_ff ĩ_g + k_dv jω₀C_f ṽ_c`. -/
def iRef (x : Fin 15 → K) : Fin 2 → K :=
  ![algebraMap ℝ K p.Kpv * (p.vRef x 0 - p.vT x 0) + algebraMap ℝ K p.Kiv * x 8 +
      algebraMap ℝ K p.kff * p.gT x 0 - algebraMap ℝ K (p.kdv * p.Bf) * p.vT x 1,
    algebraMap ℝ K p.Kpv * (p.vRef x 1 - p.vT x 1) + algebraMap ℝ K p.Kiv * x 9 +
      algebraMap ℝ K p.kff * p.gT x 1 + algebraMap ℝ K (p.kdv * p.Bf) * p.vT x 0]

/-- Bridge-voltage command in the system frame,
`Δu_cmd = K_pc (Δi* − ĩ) + K_ic ξ + ṽ_c + jω₀L_f ĩ + Δδ J u₀`. -/
def uCmd (x : Fin 15 → K) : Fin 2 → K :=
  ![algebraMap ℝ K p.Kpc * (p.iRef x 0 - p.iT x 0) + algebraMap ℝ K p.Kic * x 6 + p.vT x 0 -
      algebraMap ℝ K (p.ω0 * p.Lf) * p.iT x 1 - x 12 * algebraMap ℝ K (p.u0 1),
    algebraMap ℝ K p.Kpc * (p.iRef x 1 - p.iT x 1) + algebraMap ℝ K p.Kic * x 7 + p.vT x 1 +
      algebraMap ℝ K (p.ω0 * p.Lf) * p.iT x 0 + x 12 * algebraMap ℝ K (p.u0 0)]

/-- Active-power perturbation at the capacitor, `ΔP = v_c0ᵀ Δi_g + i_g0ᵀ Δv_c`. -/
def dP (x : Fin 15 → K) : K :=
  algebraMap ℝ K (p.vc0 0) * x 4 + algebraMap ℝ K (p.vc0 1) * x 5 +
    (algebraMap ℝ K (p.ig0 0) * x 2 + algebraMap ℝ K (p.ig0 1) * x 3)

/-- Reactive-power perturbation at the capacitor (`Q = v_q i_d − v_d i_q`). -/
def dQ (x : Fin 15 → K) : K :=
  algebraMap ℝ K (p.vc0 1) * x 4 - algebraMap ℝ K (p.vc0 0) * x 5 +
    (algebraMap ℝ K (p.ig0 0) * x 3 - algebraMap ℝ K (p.ig0 1) * x 2)

/-- The small-signal equations `ẋ = lin x u`, state order
`(i, v_c, i_g, ξ, ζ, z, Δδ, Δω, ΔQ_f)` in dq components, input the PCC voltage `Δv`. -/
def lin (x : Fin 15 → K) (u : Fin 2 → K) : Fin 15 → K :=
  ![algebraMap ℝ K p.Lf⁻¹ * (2 * x 10 - p.uCmd x 0 - x 2 - algebraMap ℝ K p.Rf * x 0 +
        algebraMap ℝ K (p.ω0 * p.Lf) * x 1),
    algebraMap ℝ K p.Lf⁻¹ * (2 * x 11 - p.uCmd x 1 - x 3 - algebraMap ℝ K p.Rf * x 1 -
        algebraMap ℝ K (p.ω0 * p.Lf) * x 0),
    algebraMap ℝ K p.Cf⁻¹ * (x 0 - x 4 + algebraMap ℝ K p.Bf * x 3),
    algebraMap ℝ K p.Cf⁻¹ * (x 1 - x 5 - algebraMap ℝ K p.Bf * x 2),
    algebraMap ℝ K p.Lg⁻¹ * (x 2 - u 0 - algebraMap ℝ K p.Rg * x 4 +
        algebraMap ℝ K (p.ω0 * p.Lg) * x 5),
    algebraMap ℝ K p.Lg⁻¹ * (x 3 - u 1 - algebraMap ℝ K p.Rg * x 5 -
        algebraMap ℝ K (p.ω0 * p.Lg) * x 4),
    p.iRef x 0 - p.iT x 0,
    p.iRef x 1 - p.iT x 1,
    p.vRef x 0 - p.vT x 0,
    p.vRef x 1 - p.vT x 1,
    algebraMap ℝ K p.a⁻¹ * (p.uCmd x 0 - x 10),
    algebraMap ℝ K p.a⁻¹ * (p.uCmd x 1 - x 11),
    x 13,
    algebraMap ℝ K p.M⁻¹ * (-p.dP x - algebraMap ℝ K p.D * x 13),
    algebraMap ℝ K p.ωq * (p.dQ x - x 14)]

end Lin

/-- State matrix: column `j` is `lin e_j 0`. -/
def A : Matrix (Fin 15) (Fin 15) ℝ := Matrix.of fun i j => p.lin (Pi.single j 1) 0 i

/-- Input matrix: column `j` is `lin 0 e_j`. -/
def B : Matrix (Fin 15) (Fin 2) ℝ := Matrix.of fun i j => p.lin 0 (Pi.single j 1) i

section LinAlg
variable {K : Type*} [Field K] [Algebra ℝ K]

/-! Each block of `lin` is additive, homogeneous and commutes with `algebraMap ℝ K`. -/

@[tmio M, powerlib_domain] private theorem blocks_add (x y : Fin 15 → K) :
    p.iT (x + y) = p.iT x + p.iT y ∧ p.vT (x + y) = p.vT x + p.vT y ∧
      p.gT (x + y) = p.gT x + p.gT y ∧ p.dP (x + y) = p.dP x + p.dP y ∧
      p.dQ (x + y) = p.dQ x + p.dQ y := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try ext k; try fin_cases k) <;>
    simp [iT, vT, gT, dP, dQ] <;> ring

@[tmio M, powerlib_domain] private theorem vRef_add (x y : Fin 15 → K) :
    p.vRef (x + y) = p.vRef x + p.vRef y := by
  ext k; fin_cases k <;> simp [vRef, (p.blocks_add x y).2.2.1] <;> ring

@[tmio M, powerlib_domain] private theorem iRef_add (x y : Fin 15 → K) :
    p.iRef (x + y) = p.iRef x + p.iRef y := by
  ext k; fin_cases k <;> simp [iRef, vRef_add, (p.blocks_add x y).2.1, (p.blocks_add x y).2.2.1] <;>
    ring

@[tmio M, powerlib_domain] private theorem uCmd_add (x y : Fin 15 → K) :
    p.uCmd (x + y) = p.uCmd x + p.uCmd y := by
  ext k; fin_cases k <;>
    simp [uCmd, iRef_add, (p.blocks_add x y).1, (p.blocks_add x y).2.1] <;> ring

@[tmio M, powerlib_domain] private theorem blocks_smul (c : K) (x : Fin 15 → K) :
    p.iT (c • x) = c • p.iT x ∧ p.vT (c • x) = c • p.vT x ∧ p.gT (c • x) = c • p.gT x ∧
      p.dP (c • x) = c * p.dP x ∧ p.dQ (c • x) = c * p.dQ x := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try ext k; try fin_cases k) <;>
    simp [iT, vT, gT, dP, dQ] <;> ring

@[tmio M, powerlib_domain] private theorem vRef_smul (c : K) (x : Fin 15 → K) :
    p.vRef (c • x) = c • p.vRef x := by
  ext k; fin_cases k <;> simp [vRef, (p.blocks_smul c x).2.2.1] <;> ring

@[tmio M, powerlib_domain] private theorem iRef_smul (c : K) (x : Fin 15 → K) :
    p.iRef (c • x) = c • p.iRef x := by
  ext k; fin_cases k <;>
    simp [iRef, vRef_smul, (p.blocks_smul c x).2.1, (p.blocks_smul c x).2.2.1] <;> ring

@[tmio M, powerlib_domain] private theorem uCmd_smul (c : K) (x : Fin 15 → K) :
    p.uCmd (c • x) = c • p.uCmd x := by
  ext k; fin_cases k <;>
    simp [uCmd, iRef_smul, (p.blocks_smul c x).1, (p.blocks_smul c x).2.1] <;> ring

@[tmio M, powerlib_domain] private theorem blocks_map (x : Fin 15 → ℝ) (k : Fin 2) :
    algebraMap ℝ K (p.iT x k) = p.iT (fun j => algebraMap ℝ K (x j)) k ∧
      algebraMap ℝ K (p.vT x k) = p.vT (fun j => algebraMap ℝ K (x j)) k ∧
      algebraMap ℝ K (p.gT x k) = p.gT (fun j => algebraMap ℝ K (x j)) k ∧
      algebraMap ℝ K (p.dP x) = p.dP (fun j => algebraMap ℝ K (x j)) ∧
      algebraMap ℝ K (p.dQ x) = p.dQ (fun j => algebraMap ℝ K (x j)) := by
  fin_cases k <;> simp [iT, vT, gT, dP, dQ]

@[tmio M, powerlib_domain] private theorem vRef_map (x : Fin 15 → ℝ) (k : Fin 2) :
    algebraMap ℝ K (p.vRef x k) = p.vRef (fun j => algebraMap ℝ K (x j)) k := by
  have h0 := p.blocks_map (K := K) x 0
  have h1 := p.blocks_map (K := K) x 1
  fin_cases k <;> simp [vRef, ← h0.2.2.1, ← h1.2.2.1]

@[tmio M, powerlib_domain] private theorem iRef_map (x : Fin 15 → ℝ) (k : Fin 2) :
    algebraMap ℝ K (p.iRef x k) = p.iRef (fun j => algebraMap ℝ K (x j)) k := by
  have h0 := p.blocks_map (K := K) x 0
  have h1 := p.blocks_map (K := K) x 1
  fin_cases k <;> simp [iRef, ← vRef_map, ← h0.2.1, ← h1.2.1, ← h0.2.2.1, ← h1.2.2.1]

@[tmio M, powerlib_domain] private theorem uCmd_map (x : Fin 15 → ℝ) (k : Fin 2) :
    algebraMap ℝ K (p.uCmd x k) = p.uCmd (fun j => algebraMap ℝ K (x j)) k := by
  have h0 := p.blocks_map (K := K) x 0
  have h1 := p.blocks_map (K := K) x 1
  fin_cases k <;> simp [uCmd, ← iRef_map, ← h0.1, ← h1.1, ← h0.2.1, ← h1.2.1]

@[tmio M, powerlib_domain] theorem lin_add (x y : Fin 15 → K) (u v : Fin 2 → K) :
    p.lin (x + y) (u + v) = p.lin x u + p.lin y v := by
  obtain ⟨-, -, -, hP, hQ⟩ := p.blocks_add x y
  ext i
  fin_cases i <;> simp [lin, uCmd_add, iRef_add, vRef_add, (p.blocks_add x y).1,
    (p.blocks_add x y).2.1, hP, hQ] <;> ring

@[tmio M, powerlib_domain] theorem lin_smul (c : K) (x : Fin 15 → K) (u : Fin 2 → K) :
    p.lin (c • x) (c • u) = c • p.lin x u := by
  obtain ⟨-, -, -, hP, hQ⟩ := p.blocks_smul c x
  ext i
  fin_cases i <;> simp [lin, uCmd_smul, iRef_smul, vRef_smul, (p.blocks_smul c x).1,
    (p.blocks_smul c x).2.1, hP, hQ] <;> ring

@[tmio M, powerlib_domain] theorem lin_algebraMap (x : Fin 15 → ℝ) (u : Fin 2 → ℝ)
    (i : Fin 15) :
    algebraMap ℝ K (p.lin x u i) =
      p.lin (fun j => algebraMap ℝ K (x j)) (fun j => algebraMap ℝ K (u j)) i := by
  have h0 := p.blocks_map (K := K) x 0
  have h1 := p.blocks_map (K := K) x 1
  fin_cases i <;> simp [lin, ← uCmd_map, ← iRef_map, ← vRef_map, ← h0.1, ← h1.1, ← h0.2.1,
    ← h1.2.1, ← h0.2.2.2.1, ← h0.2.2.2.2, map_ofNat]

/-- `x ↦ lin x 0` as a `K`-linear map. -/
def linX : (Fin 15 → K) →ₗ[K] (Fin 15 → K) where
  toFun x := p.lin x 0
  map_add' x y := by
    have := p.lin_add x y 0 0
    rwa [add_zero] at this
  map_smul' c x := by
    have := p.lin_smul c x 0
    rwa [smul_zero] at this

/-- `u ↦ lin 0 u` as a `K`-linear map. -/
def linU : (Fin 2 → K) →ₗ[K] (Fin 15 → K) where
  toFun u := p.lin 0 u
  map_add' u v := by
    have := p.lin_add 0 0 u v
    rwa [add_zero] at this
  map_smul' c u := by
    have := p.lin_smul c 0 u
    rwa [smul_zero] at this

/-- The realization is exactly the block equations: `lin x u = A x + B u`. -/
@[tmio M, powerlib_domain] theorem lin_eq_mulVec (x : Fin 15 → K) (u : Fin 2 → K) :
    p.lin x u = (p.A.map (algebraMap ℝ K)) *ᵥ x + (p.B.map (algebraMap ℝ K)) *ᵥ u := by
  have h1 : p.lin x u = p.linX x + p.linU u := by
    have := p.lin_add x 0 0 u
    simpa [linX, linU] using this
  rw [h1, LinearMap.pi_apply_eq_sum_univ p.linX x, LinearMap.pi_apply_eq_sum_univ p.linU u]
  ext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Matrix.map_apply, A, B, Matrix.of_apply, lin_algebraMap, linX, linU,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 2
    · funext k
      simp [Pi.single_apply, eq_comm]
    · funext k
      simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 2
    · funext k
      simp
    · funext k
      simp [Pi.single_apply, eq_comm]

end LinAlg

end CascadeParams

/-- Output matrix: the IN-positive port current `−(Δi_gd, Δi_gq)` (states `4`, `5`). -/
def cascOutput : Matrix (Fin 2) (Fin 15) ℝ :=
  Matrix.of fun i j => if (j : ℕ) = i + 4 then -1 else 0

namespace CascadeParams

variable (p : CascadeParams)

/-- The 15-state realization: input the PCC voltage, output the IN-positive line current. -/
def model : Plant 15 2 := ⟨p.A, p.B, cascOutput, 0⟩

/-- The realization is strictly proper. -/
@[tmio M, powerlib_domain] theorem model_D : p.model.D = 0 := rfl

/-! ## The closed form -/

/-- Voltage-loop PI `G_v = K_pv + K_iv/s`. -/
def Gv (s : ℂ) : ℂ := p.Kpv + p.Kiv / s

/-- Current-loop PI `G_c = K_pc + K_ic/s`. -/
def Gc (s : ℂ) : ℂ := p.Kpc + p.Kic / s

/-- Padé(1,1) delay, written `2/(1 + a s) − 1`. -/
def Gdel (s : ℂ) : ℂ := 2 / (1 + p.a * s) - 1

/-- The filter capacitor's dq admittance `Y_C = s C_f I + ω₀C_f J`. -/
def capY (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Transform.complexSymm (p.Cf * s) (p.Bf : ℂ)

/-- Loop gain on the filter current: `u_cmd ∋ F_i i`, `F_i = −G_c + jω₀L_f`. -/
def Fi (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Transform.complexSymm (-p.Gc s) ((p.ω0 * p.Lf : ℝ) : ℂ)

/-- Loop gain on the capacitor voltage: `F_v = 1 − G_c G_v + j G_c k_dv ω₀C_f`. -/
def Fv (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Transform.complexSymm (1 - p.Gc s * p.Gv s) (p.Gc s * ((p.kdv * p.Bf : ℝ) : ℂ))

/-- Loop gain on the line current: `F_g = G_c (k_ff − G_v Z_v)`. -/
def Fg (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Transform.complexSymm (p.Gc s * (p.kff - p.Gv s * p.Rv)) (-(p.Gc s * p.Gv s * p.Xv))

/-- `α = Z_f − G_del F_i`. -/
def innerA (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  p.filter.dqImpedance p.ω0 s - p.Gdel s • p.Fi s

/-- `β = I − G_del F_v`. -/
def innerB (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := 1 - p.Gdel s • p.Fv s

/-- The Thevenin numerator `N = α (I + Y_C Z_g) + β Z_g − G_del F_g`. -/
def innerN (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  p.innerA s * (1 + p.capY s * p.line.dqImpedance p.ω0 s) +
    p.innerB s * p.line.dqImpedance p.ω0 s - p.Gdel s • p.Fg s

/-- The Thevenin voltage factor `T = α Y_C + β`. -/
def innerT (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := p.innerA s * p.capY s + p.innerB s

/-- The angle-injection vector `w = u₀ − F_i i₀ − F_v v_c0 − F_g i_g0`. -/
def angleW (s : ℂ) : Fin 2 → ℂ := fun k =>
  (p.u0 k : ℂ) - (p.Fi s *ᵥ fun j => (p.i0 j : ℂ)) k - (p.Fv s *ᵥ fun j => (p.vc0 j : ℂ)) k -
    (p.Fg s *ᵥ fun j => (p.ig0 j : ℂ)) k

/-- The channel input before the delay, `[J w, −n_q G_c G_v e^{jδ₀}]`. -/
def chanB0 (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(p.angleW s 1), -(p.nq * p.Gc s * p.Gv s * Real.cos p.δ0);
    p.angleW s 0, -(p.nq * p.Gc s * p.Gv s * Real.sin p.δ0)]

/-- The channel input `B = G_del [J w, −n_q G_c G_v e^{jδ₀}]`. -/
def chanB (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := p.Gdel s • p.chanB0 s

/-- The power rows of the line current at fixed capacitor voltage, `C_p = [v_c0ᵀ; v_c0ᵀ J]`. -/
def measCp : Matrix (Fin 2) (Fin 2) ℂ := complexify (Line.VSMQ.pccCi p.vc0)

/-- The power rows of the capacitor voltage at fixed current, `C_v = [i_g0ᵀ; (J i_g0)ᵀ]`. -/
def measCv : Matrix (Fin 2) (Fin 2) ℂ := complexify (Line.VSMQ.curC (p.ig0 0) (p.ig0 1))

/-- The power rows of the line current at fixed port voltage, `C_i = C_p + C_v Z_g`. -/
def measCi (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  p.measCp + p.measCv * p.line.dqImpedance p.ω0 s

/-- The channel transfer `K = diag(1/(M s² + D s), −ω_q/(s + ω_q))`. -/
def chanK (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / ((p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s), 0; 0, -(p.ωq : ℂ) / (s + (p.ωq : ℂ))]

/-- The closed-form port admittance `Y = (N + B K C_i)⁻¹ (T + B K C_v)`. -/
def Ycasc (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  syncY (p.innerN s) (p.innerT s) (p.chanB s) (p.chanK s) (p.measCi s) p.measCv

/-! ## The state response -/

section Resp

variable (s : ℂ)

/-- Line-current response (column `c`: input `e_c`), `−Y`. -/
def RG : Matrix (Fin 2) (Fin 2) ℂ := -p.Ycasc s

/-- Capacitor-voltage response `I + Z_g (−Y)`. -/
def RV : Matrix (Fin 2) (Fin 2) ℂ := 1 + p.line.dqImpedance p.ω0 s * p.RG s

/-- Filter-current response `−Y + Y_C (I + Z_g (−Y))`. -/
def RI : Matrix (Fin 2) (Fin 2) ℂ := p.RG s + p.capY s * p.RV s

/-- Channel response `(Δδ, ΔQ_f) = −K (C_p (−Y) + C_v (I + Z_g (−Y)))`. -/
def RC : Matrix (Fin 2) (Fin 2) ℂ := -(p.chanK s * (p.measCp * p.RG s + p.measCv * p.RV s))

/-- Bridge-voltage command response `F_i RI + F_v RV + F_g RG + [J w, −n_q G_c G_v e^{jδ₀}] RC`. -/
def RU : Matrix (Fin 2) (Fin 2) ℂ :=
  p.Fi s * p.RI s + p.Fv s * p.RV s + p.Fg s * p.RG s + p.chanB0 s * p.RC s

variable (c : Fin 2)

/-- `ĩ` response. -/
def rIT : Fin 2 → ℂ := ![p.RI s 0 c + p.RC s 0 c * p.i0 1, p.RI s 1 c - p.RC s 0 c * p.i0 0]

/-- `ṽ_c` response. -/
def rVT : Fin 2 → ℂ :=
  ![p.RV s 0 c + p.RC s 0 c * p.vc0 1, p.RV s 1 c - p.RC s 0 c * p.vc0 0]

/-- `ĩ_g` response. -/
def rGT : Fin 2 → ℂ :=
  ![p.RG s 0 c + p.RC s 0 c * p.ig0 1, p.RG s 1 c - p.RC s 0 c * p.ig0 0]

/-- `Δv*` response. -/
def rVR : Fin 2 → ℂ :=
  ![-(p.nq * p.RC s 1 c) * Real.cos p.δ0 - (p.Rv * p.rGT s c 0 - p.Xv * p.rGT s c 1),
    -(p.nq * p.RC s 1 c) * Real.sin p.δ0 - (p.Xv * p.rGT s c 0 + p.Rv * p.rGT s c 1)]

/-- Voltage-loop error response `Δv* − ṽ_c`. -/
def rVE : Fin 2 → ℂ := fun k => p.rVR s c k - p.rVT s c k

/-- `Δi*` response. -/
def rIR : Fin 2 → ℂ :=
  ![p.Kpv * p.rVE s c 0 + p.Kiv * (p.rVE s c 0 / s) + p.kff * p.rGT s c 0 -
      ((p.kdv * p.Bf : ℝ) : ℂ) * p.rVT s c 1,
    p.Kpv * p.rVE s c 1 + p.Kiv * (p.rVE s c 1 / s) + p.kff * p.rGT s c 1 +
      ((p.kdv * p.Bf : ℝ) : ℂ) * p.rVT s c 0]

/-- Current-loop error response `Δi* − ĩ`. -/
def rIE : Fin 2 → ℂ := fun k => p.rIR s c k - p.rIT s c k

/-- Response of the fifteen states to a unit port-voltage perturbation along `e_c`. -/
def resp : Fin 15 → ℂ :=
  ![p.RI s 0 c, p.RI s 1 c, p.RV s 0 c, p.RV s 1 c, p.RG s 0 c, p.RG s 1 c,
    p.rIE s c 0 / s, p.rIE s c 1 / s, p.rVE s c 0 / s, p.rVE s c 1 / s,
    p.RU s 0 c / (1 + p.a * s), p.RU s 1 c / (1 + p.a * s), p.RC s 0 c, s * p.RC s 0 c,
    p.RC s 1 c]

@[tmio M, powerlib_domain] private theorem iT_resp : p.iT (p.resp s c) = p.rIT s c := by
  ext k; fin_cases k <;> simp [iT, resp, rIT]

@[tmio M, powerlib_domain] private theorem vT_resp : p.vT (p.resp s c) = p.rVT s c := by
  ext k; fin_cases k <;> simp [vT, resp, rVT]

@[tmio M, powerlib_domain] private theorem gT_resp : p.gT (p.resp s c) = p.rGT s c := by
  ext k; fin_cases k <;> simp [gT, resp, rGT]

@[tmio M, powerlib_domain] private theorem vRef_resp : p.vRef (p.resp s c) = p.rVR s c := by
  ext k; simp only [vRef, gT_resp]; fin_cases k <;> simp [rVR, resp]

@[tmio M, powerlib_domain] private theorem iRef_resp : p.iRef (p.resp s c) = p.rIR s c := by
  ext k; simp only [iRef, vRef_resp, vT_resp, gT_resp]; fin_cases k <;> simp [rIR, rVE, resp]

/-- The bridge-voltage command along the response is the `c` column of `RU`. -/
@[tmio M, powerlib_domain] private theorem uCmd_resp (k : Fin 2) :
    p.uCmd (p.resp s c) k = p.RU s k c := by
  simp only [uCmd, iRef_resp, iT_resp, vT_resp]
  fin_cases k <;>
    simp [RU, Fi, Fv, Fg, chanB0, angleW, Gc, Gv, Transform.complexSymm, Matrix.mulVec,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      rIR, rIE, rVE, rVR, rIT, rVT, rGT, resp] <;> ring

end Resp

/-- The channel response in the port-law form: `RC = −K (C_i (−Y) + C_v)`. -/
@[tmio M, powerlib_domain] private theorem RC_eq (s : ℂ) :
    p.RC s = -(p.chanK s * (p.measCi s * p.RG s + p.measCv)) := by
  rw [RC, RV, measCi]
  congr 2
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- **The filter row along the response.** With `Y = Ycasc s` solving the port law, the
response satisfies the bridge equation `Z_f RI + RV = G_del RU`: the inner layer gives
`Z_f RI + RV − G_del RU = N RG + T − B RC`, and the outer layer `RC = −K (C_i RG + C_v)`
turns it into `(N + B K C_i) RG + T + B K C_v = 0`. -/
@[tmio M, powerlib_domain] private theorem filter_resp (s : ℂ)
    (hN : (p.innerN s + p.chanB s * p.chanK s * p.measCi s).det ≠ 0) :
    p.filter.dqImpedance p.ω0 s * p.RI s + p.RV s = p.Gdel s • p.RU s := by
  have hY := syncY_spec (T := p.innerT s) (Cv := p.measCv) hN
  have key : p.filter.dqImpedance p.ω0 s * p.RI s + p.RV s - p.Gdel s • p.RU s =
      (p.innerN s + p.chanB s * p.chanK s * p.measCi s) * p.RG s +
        (p.innerT s + p.chanB s * p.chanK s * p.measCv) := by
    rw [RU, RC_eq, RI, RV, innerN, innerT, innerA, innerB, chanB]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, smul_add, smul_neg]
    abel
  rw [← sub_eq_zero, key, RG, Ycasc, Matrix.mul_neg, hY]
  abel

/-- If `Y = Ycasc s` solves its port law, `resp` solves `s x = lin x e_c`. -/
@[tmio M, powerlib_domain] theorem resp_lin {s : ℂ} (hs : s ≠ 0) (ha : p.a ≠ 0)
    (hda : 1 + (p.a : ℂ) * s ≠ 0) (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0)
    (hM : p.M ≠ 0) (hd : (p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s ≠ 0) (hq : s + (p.ωq : ℂ) ≠ 0)
    (hN : (p.innerN s + p.chanB s * p.chanK s * p.measCi s).det ≠ 0) (c : Fin 2) :
    s • p.resp s c = p.lin (p.resp s c) (Pi.single c 1) := by
  have hLf' : (p.Lf : ℂ) ≠ 0 := by exact_mod_cast hLf
  have hCf' : (p.Cf : ℂ) ≠ 0 := by exact_mod_cast hCf
  have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg
  have hM' : (p.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have ha' : (p.a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hda2 : 1 + s * (p.a : ℂ) ≠ 0 := by rwa [mul_comm] at hda
  have hF := p.filter_resp s hN
  rw [Passive.SeriesRLC.dqImpedance_of_noCap (b := p.filter) rfl] at hF
  have hF0 := congrFun (congrFun hF 0) c
  have hF1 := congrFun (congrFun hF 1) c
  have hC : p.RI s = p.RG s + p.capY s * p.RV s := rfl
  have hC0 := congrFun (congrFun hC 0) c
  have hC1 := congrFun (congrFun hC 1) c
  have hV : p.RV s = 1 + p.line.dqImpedance p.ω0 s * p.RG s := rfl
  rw [Passive.SeriesRLC.dqImpedance_of_noCap (b := p.line) rfl] at hV
  have hV0 := congrFun (congrFun hV 0) c
  have hV1 := congrFun (congrFun hV 1) c
  simp only [FullModel.Params.filter, FullModel.Params.line, capY, Transform.complexSymm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, smul_eq_mul,
    Matrix.one_eq_pi_single, Pi.single_comm] at hF0 hF1 hC0 hC1 hV0 hV1
  have hP : ((p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s) * p.RC s 0 c =
      -(p.vc0 0 * p.RG s 0 c + p.vc0 1 * p.RG s 1 c + (p.ig0 0 * p.RV s 0 c +
        p.ig0 1 * p.RV s 1 c)) := by
    have hd2 : (p.M : ℂ) * s + p.D ≠ 0 := fun h => hd (by linear_combination s * h)
    simp only [RC, chanK, measCp, measCv, Line.VSMQ.pccCi, Line.VSMQ.curC, Matrix.neg_apply,
      Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Complex.coe_algebraMap]
    field_simp
    ring
  have hQ : (s + (p.ωq : ℂ)) * p.RC s 1 c =
      p.ωq * (p.vc0 1 * p.RG s 0 c - p.vc0 0 * p.RG s 1 c + (p.ig0 0 * p.RV s 1 c -
        p.ig0 1 * p.RV s 0 c)) := by
    simp only [RC, chanK, measCp, measCv, Line.VSMQ.pccCi, Line.VSMQ.curC, Matrix.neg_apply,
      Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Complex.coe_algebraMap]
    field_simp
    push_cast
    ring
  have hU0 := p.uCmd_resp s c 0
  have hU1 := p.uCmd_resp s c 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases i <;>
    simp only [lin, dP, dQ, hU0, hU1, iRef_resp, iT_resp, vRef_resp, vT_resp, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, map_inv₀]
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hLf')]
    simp [resp, Gdel] at hF0 ⊢
    linear_combination hF0
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hLf')]
    simp [resp, Gdel] at hF1 ⊢
    linear_combination hF1
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hCf')]
    simp [resp, FullModel.Params.Bf] at hC0 ⊢
    linear_combination -hC0
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hCf')]
    simp [resp, FullModel.Params.Bf] at hC1 ⊢
    linear_combination -hC1
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hLg')]
    simp [resp] at hV0 ⊢
    linear_combination -hV0
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hLg')]
    simp [resp] at hV1 ⊢
    linear_combination -hV1
  · simp [resp, rIE]
    field_simp
  · simp [resp, rIE]
    field_simp
  · simp [resp, rVE]
    field_simp
  · simp [resp, rVE]
    field_simp
  · simp [resp]
    field_simp
    ring
  · simp [resp]
    field_simp
    ring
  · simp [resp]
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hM')]
    simp [resp] at hP ⊢
    linear_combination hP
  · simp [resp] at hQ ⊢
    linear_combination hQ

/-- **The 15-state realization has the closed-form admittance.** Off the poles the transfer
matrix of the cascade port model is `Ycasc s = (N + B K C_i)⁻¹ (T + B K C_v)`. -/
@[tmio M, powerlib_domain] theorem transfer_eq_Ycasc {s : ℂ} (hs : s ≠ 0) (ha : p.a ≠ 0)
    (hda : 1 + (p.a : ℂ) * s ≠ 0) (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0)
    (hM : p.M ≠ 0) (hd : (p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s ≠ 0) (hq : s + (p.ωq : ℂ) ≠ 0)
    (hN : (p.innerN s + p.chanB s * p.chanK s * p.measCi s).det ≠ 0)
    (hA : (characteristicMatrix p.model.A s).det ≠ 0) :
    transfer p.model s = p.Ycasc s := by
  set X : Matrix (Fin 15) (Fin 2) ℂ := Matrix.of fun i c => p.resp s c i with hX
  have hMX : characteristicMatrix p.model.A s * X = complexify p.model.B := by
    ext i c
    have h := congrFun (p.resp_lin hs ha hda hLf hCf hLg hM hd hq hN c) i
    rw [p.lin_eq_mulVec] at h
    have hB : (p.B.map (algebraMap ℝ ℂ) *ᵥ Pi.single c 1) i = p.B.map (algebraMap ℝ ℂ) i c := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hAX : (p.A.map (algebraMap ℝ ℂ) * X) i c =
        (p.A.map (algebraMap ℝ ℂ) *ᵥ p.resp s c) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, hB] at h
    simp only [characteristicMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, model, hAX]
    have hXic : X i c = p.resp s c i := by simp [hX]
    rw [hXic, h, add_sub_cancel_left]
  rw [LTI.transfer_eq_of_solution _ _ _ hA hMX]
  ext k c
  fin_cases k <;> simp [model, cascOutput, hX, Matrix.mul_apply, Fin.sum_univ_succ, resp, RG]

/-! ## On a network -/

/-- The cascade port model as the load of the grid-side network of
`theorem/Grid/GridImpedance.lean`. -/
def cascOnNetwork (line : Passive.SeriesRLC) (shunt : Passive.ParallelRLC) :
    Grid.Interconnection 4 15 2 :=
  withNetwork line shunt p.ω0 p.model p.model_D

/-- Return difference of the cascade–network interconnection: `det (I + Z_ext Y_casc)`. -/
@[tmio M, powerlib_domain] theorem cascOnNetwork_returnDifference {line : Passive.SeriesRLC}
    {shunt : Passive.ParallelRLC} (hS : line.S = 0) (hΓ : shunt.Γ = 0) (hC : shunt.C ≠ 0)
    (hLn : line.L ≠ 0) {s : ℂ}
    (hMn : (characteristicMatrix (networkModel line shunt p.ω0).A s).det ≠ 0)
    (hYn : (shunt.dqAdmittance p.ω0 s).det ≠ 0) (hZn : (line.dqImpedance p.ω0 s).det ≠ 0)
    (hs : s ≠ 0) (ha : p.a ≠ 0) (hda : 1 + (p.a : ℂ) * s ≠ 0) (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hM : p.M ≠ 0)
    (hd : (p.M : ℂ) * s ^ 2 + (p.D : ℂ) * s ≠ 0) (hq : s + (p.ωq : ℂ) ≠ 0)
    (hN : (p.innerN s + p.chanB s * p.chanK s * p.measCi s).det ≠ 0)
    (hA : (characteristicMatrix p.model.A s).det ≠ 0) :
    (p.cascOnNetwork line shunt).returnDifference s =
      (1 + Zext line shunt p.ω0 s * p.Ycasc s).det := by
  change (1 + transfer (networkModel line shunt p.ω0) s * transfer p.model s).det = _
  rw [networkModel_transfer hS hΓ hC hLn hMn hYn hZn,
    p.transfer_eq_Ycasc hs ha hda hLf hCf hLg hM hd hq hN hA]

end CascadeParams

end powerlib.GFM.Port
