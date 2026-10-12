import theorem.CurrentControl.Network
import theorem.CurrentControl.ComplexPower

/-! # 10-state small-signal GFL port realization and its closed-form dq admittance (foundation)

Realization of the block diagram of work-sync T-gfl-impedance §1.1–§1.5 as a `Linear.Plant`, and
proof that its transfer matrix is exactly the boxed closed form
`Y_dq^gfl = [I − G_id G_del Φ_full K]⁻¹ [Z_oc⁻¹ + G_id G_del Θ_full K]` with `K = I`.

Model (small-signal, linear, continuous time; all quantities are perturbations around a fixed
operating point; system dq frame rotating at the constant `ω = ω_s`; port current IN-positive,
work-sync `conventions.md` §D1; per-unit P/Q Jacobians without `3/2`):
* State order `(I_d, I_q, z_d, z_q, Δθ, η, ξcc_d, ξcc_q, ξpc_P, ξpc_Q)` (`lin`): filter current
  in the system frame, the two Padé(1,1) delay states, the PLL angle deviation and integrator,
  the current-loop and power-loop PI integrators. Input `ΔV^sys = (ΔV_d, ΔV_q)` (PCC voltage),
  output `ΔI^sys = (ΔI_d, ΔI_q)`; no feedthrough (`model_D`).
* Filter (§1.1): `L İ = ΔV − ΔV^c − R I − ω L J I` (single `L` with `R`; no LCL capacitor).
* PWM and delay (§1.1–§1.2): `ΔV^c = V_dc · y`, `y = G_del ΔD^sys` realized by
  `a ż = ΔD − z`, `y = 2 z − ΔD`, i.e. `G_del = (1 − a s)/(1 + a s)` (`Gdel_eq`), `a = τ_d/2`;
  `V_dc` constant (no DC-link dynamics).
* PLL (§1.3): linearized SRF-PLL `Δθ' = Kpl ΔV_q^pll + η`, `η' = Kil ΔV_q^pll`,
  `ΔV_q^pll = ΔV_q − V_d0 Δθ`, so `Δθ = G_pll ΔV_q`; first-order frame projections
  `ΔI^pll = ΔI − Δθ J I₀`, `ΔV^pll = ΔV − Δθ J V₀`, `ΔD^sys = ΔD^pll + Δθ J D₀`
  (`G_i^pll`, `G_v^pll`, `G_d^pll`; cf. `pllVoltage_proj`, `pllCurrent_proj`).
* Current loop (§1.4, IN-positive form): `ΔD^pll = −G_ci (ΔI_ref − ΔI^pll) − G_dei ΔI^pll`,
  `G_ci = Kpc + Kic/s`, `G_dei = gdei · J` (the note's value is `gdei = 3 ω L / V_dc`).
* Power loop (§1.5): `ΔI_ref = −G_cpq (G_i^pq ΔI^pll + G_v^pq ΔV^pll)`, `G_cpq = Kpp + Kip/s`,
  references `P*, Q*` frozen; `G_i^pq`, `G_v^pq` are the P/Q Jacobians of `ComplexPower.lean`.
* Excluded: current / modulation limits, DC-link and source dynamics, LCL resonance, grid
  frequency variation, large-signal PLL behaviour.

Results.
* `lin_eq_mulVec`: `model` (`A`, `B`) is exactly the linear map `lin` of these block equations.
* `Ygfl_spec`: the closed form `Ygfl` solves `Z_oc Y + V_dc G_del (Φ Y + Θ) = I`.
* `transfer_eq_Ygfl`: off the poles (`s ≠ 0`, `1 + a s ≠ 0`, PLL denominator, `det Z_oc`,
  `det [I − G_id G_del Φ]`, `det (sI − A)` nonzero) the transfer matrix of the realization is
  `Ygfl s`. This confirms the boxed §1.5 formula (with `K = I`) exactly; no correction needed.
* `gflOnNetwork`, `gflOnNetwork_returnDifference`: with the network realization of
  `Network.lean` as source (its input is the IN-positive converter current, its output `−v_PCC`),
  the GFL realization is an admissible strictly proper load of `Circuits.Interconnection`
  and the return difference of the GFL–grid interconnection is `det (I + Z_ext Y_gfl)`.
These are realization identities (foundation, static evidence); no stability claim is made. The
behaviour of the interconnection is that of the family `Circuits.Interconnection.family`.

Source: work-sync `theory/T-gfl-impedance.md` §1.1–§1.5, §1.7;
`theory/T-gfl-control.md` §1.5–§1.6; `theory/T-pll-dynamics.md` §1.11 (`G_pll`).
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Linear

/-- Parameters of the 10-state small-signal GFL port model. -/
@[ext] structure GFLParams where
  /-- Filter inductance. -/
  L : ℝ
  /-- Filter resistance. -/
  R : ℝ
  /-- Frame speed `ω_s`. -/
  ω : ℝ
  /-- DC-link voltage (constant). -/
  Vdc : ℝ
  /-- Half of the computation + PWM delay, `a = τ_d/2` (Padé(1,1)). -/
  a : ℝ
  /-- Current-loop PI gains. -/
  Kpc : ℝ
  Kic : ℝ
  /-- Power-loop PI gains. -/
  Kpp : ℝ
  Kip : ℝ
  /-- PLL PI gains. -/
  Kpl : ℝ
  Kil : ℝ
  /-- Delay-decoupling coefficient: `G_dei = gdei · J` (note: `3 ω L / V_dc`). -/
  gdei : ℝ
  /-- Operating PCC voltage, current and duty cycle `(d, q)`. -/
  V0 : Fin 2 → ℝ
  I0 : Fin 2 → ℝ
  D0 : Fin 2 → ℝ

namespace GFLParams

variable (p : GFLParams)

section Lin
variable {K : Type*} [Field K] [Algebra ℝ K]

/-- PLL-frame current `I^pll = I − Δθ J I₀`. -/
def ipll (x : Fin 10 → K) : Fin 2 → K :=
  ![x 0 + x 4 * algebraMap ℝ K (p.I0 1), x 1 - x 4 * algebraMap ℝ K (p.I0 0)]

/-- PLL-frame voltage `V^pll = V − Δθ J V₀`. -/
def vpll (x : Fin 10 → K) (u : Fin 2 → K) : Fin 2 → K :=
  ![u 0 + x 4 * algebraMap ℝ K (p.V0 1), u 1 - x 4 * algebraMap ℝ K (p.V0 0)]

/-- Power error `Δ(P, Q) = G_i^pq ΔI^pll + G_v^pq ΔV^pll`. -/
def epq (x : Fin 10 → K) (u : Fin 2 → K) : Fin 2 → K :=
  ![algebraMap ℝ K (p.V0 0) * p.ipll x 0 + algebraMap ℝ K (p.V0 1) * p.ipll x 1 +
      (algebraMap ℝ K (p.I0 0) * p.vpll x u 0 + algebraMap ℝ K (p.I0 1) * p.vpll x u 1),
    algebraMap ℝ K (p.V0 1) * p.ipll x 0 - algebraMap ℝ K (p.V0 0) * p.ipll x 1 +
      (-(algebraMap ℝ K (p.I0 1) * p.vpll x u 0) + algebraMap ℝ K (p.I0 0) * p.vpll x u 1)]

/-- Current reference from the P/Q PI: `ΔI_ref = −Kpp e − Kip ξ_pc`. -/
def iref (x : Fin 10 → K) (u : Fin 2 → K) : Fin 2 → K :=
  ![-(algebraMap ℝ K p.Kpp * p.epq x u 0) - algebraMap ℝ K p.Kip * x 8,
    -(algebraMap ℝ K p.Kpp * p.epq x u 1) - algebraMap ℝ K p.Kip * x 9]

/-- Duty cycle in the system frame:
`ΔD = −Kpc (ΔI_ref − ΔI^pll) − Kic ξ_cc − G_dei ΔI^pll + Δθ J D₀`. -/
def duty (x : Fin 10 → K) (u : Fin 2 → K) : Fin 2 → K :=
  ![-(algebraMap ℝ K p.Kpc * (p.iref x u 0 - p.ipll x 0)) - algebraMap ℝ K p.Kic * x 6 +
      algebraMap ℝ K p.gdei * p.ipll x 1 - x 4 * algebraMap ℝ K (p.D0 1),
    -(algebraMap ℝ K p.Kpc * (p.iref x u 1 - p.ipll x 1)) - algebraMap ℝ K p.Kic * x 7 -
      algebraMap ℝ K p.gdei * p.ipll x 0 + x 4 * algebraMap ℝ K (p.D0 0)]

/-- The small-signal equations `ẋ = lin x u`, state order
`(I_d, I_q, z_d, z_q, Δθ, η, ξcc_d, ξcc_q, ξpc_P, ξpc_Q)`, input `ΔV = (ΔV_d, ΔV_q)`. -/
def lin (x : Fin 10 → K) (u : Fin 2 → K) : Fin 10 → K :=
  ![algebraMap ℝ K p.L⁻¹ * (u 0 - algebraMap ℝ K p.R * x 0 +
        algebraMap ℝ K (p.ω * p.L) * x 1 - algebraMap ℝ K p.Vdc * (2 * x 2 - p.duty x u 0)),
    algebraMap ℝ K p.L⁻¹ * (u 1 - algebraMap ℝ K p.R * x 1 -
        algebraMap ℝ K (p.ω * p.L) * x 0 - algebraMap ℝ K p.Vdc * (2 * x 3 - p.duty x u 1)),
    algebraMap ℝ K p.a⁻¹ * (p.duty x u 0 - x 2),
    algebraMap ℝ K p.a⁻¹ * (p.duty x u 1 - x 3),
    algebraMap ℝ K p.Kpl * p.vpll x u 1 + x 5,
    algebraMap ℝ K p.Kil * p.vpll x u 1,
    p.iref x u 0 - p.ipll x 0,
    p.iref x u 1 - p.ipll x 1,
    p.epq x u 0,
    p.epq x u 1]

end Lin

/-- Coordinate vector `e_j`. -/
def unitVec {n : ℕ} {K : Type*} [Zero K] [One K] (j : Fin n) : Fin n → K :=
  fun k => if j = k then 1 else 0

/-- State matrix: column `j` is `lin e_j 0`. -/
def A : Matrix (Fin 10) (Fin 10) ℝ := Matrix.of fun i j => p.lin (unitVec j) 0 i

/-- Input matrix: column `j` is `lin 0 e_j`. -/
def B : Matrix (Fin 10) (Fin 2) ℝ := Matrix.of fun i j => p.lin 0 (unitVec j) i

section LinAlg
variable {K : Type*} [Field K] [Algebra ℝ K]

@[powerlib_foundation] theorem lin_add (x y : Fin 10 → K) (u v : Fin 2 → K) :
    p.lin (x + y) (u + v) = p.lin x u + p.lin y v := by
  ext i
  fin_cases i <;> simp [lin, duty, iref, epq, ipll, vpll] <;> ring

@[powerlib_foundation] theorem lin_smul (c : K) (x : Fin 10 → K) (u : Fin 2 → K) :
    p.lin (c • x) (c • u) = c • p.lin x u := by
  ext i
  fin_cases i <;> simp [lin, duty, iref, epq, ipll, vpll] <;> ring

@[powerlib_foundation] theorem lin_algebraMap (x : Fin 10 → ℝ) (u : Fin 2 → ℝ) (i : Fin 10) :
    algebraMap ℝ K (p.lin x u i) =
      p.lin (fun j => algebraMap ℝ K (x j)) (fun j => algebraMap ℝ K (u j)) i := by
  fin_cases i <;> simp [lin, duty, iref, epq, ipll, vpll, map_ofNat]

/-- `x ↦ lin x 0` as a `K`-linear map. -/
def linX : (Fin 10 → K) →ₗ[K] (Fin 10 → K) where
  toFun x := p.lin x 0
  map_add' x y := by
    have := p.lin_add x y 0 0
    rwa [add_zero] at this
  map_smul' c x := by
    have := p.lin_smul c x 0
    rwa [smul_zero] at this

/-- `u ↦ lin 0 u` as a `K`-linear map. -/
def linU : (Fin 2 → K) →ₗ[K] (Fin 10 → K) where
  toFun u := p.lin 0 u
  map_add' u v := by
    have := p.lin_add 0 0 u v
    rwa [add_zero] at this
  map_smul' c u := by
    have := p.lin_smul c 0 u
    rwa [smul_zero] at this

@[powerlib_foundation] theorem lin_eq_mulVec (x : Fin 10 → K) (u : Fin 2 → K) :
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
      simp [unitVec]
    · funext k
      simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 2
    · funext k
      simp
    · funext k
      simp [unitVec]

end LinAlg

end GFLParams

/-- Output matrix: the port current `(I_d, I_q)` (states `0`, `1`). -/
def gflOutput : Matrix (Fin 2) (Fin 10) ℝ := Matrix.of fun i j => if (j : ℕ) = i then 1 else 0

/-- The 10-state realization: input `ΔV^sys`, output `ΔI^sys` (IN-positive). -/
def GFLParams.model (p : GFLParams) : Plant 10 2 := ⟨p.A, p.B, gflOutput, 0⟩

/-- The realization is strictly proper. -/
@[powerlib_foundation] theorem GFLParams.model_D (p : GFLParams) : p.model.D = 0 := rfl

namespace GFLParams

variable (p : GFLParams)

/-! ## Closed-form blocks (T-gfl-impedance §1.1–§1.5) -/

/-- Padé(1,1) delay, written `2/(1 + a s) − 1`. -/
def Gdel (s : ℂ) : ℂ := 2 / (1 + p.a * s) - 1

@[powerlib_foundation] theorem Gdel_eq {s : ℂ} (h : 1 + (p.a : ℂ) * s ≠ 0) :
    p.Gdel s = (1 - p.a * s) / (1 + p.a * s) := by
  unfold Gdel
  field_simp
  ring

/-- Current-loop PI `G_ci = Kpc + Kic/s` (scalar part of `G_ci I₂`). -/
def Gci (s : ℂ) : ℂ := p.Kpc + p.Kic / s

/-- Power-loop PI `G_cpq = Kpp + Kip/s`. -/
def Gcpq (s : ℂ) : ℂ := p.Kpp + p.Kip / s

/-- PLL port transfer `G_pll = (Kpl s + Kil)/(s² + V_d0 Kpl s + V_d0 Kil)`. -/
def Gpll (s : ℂ) : ℂ := (p.Kpl * s + p.Kil) / (s ^ 2 + p.V0 0 * p.Kpl * s + p.V0 0 * p.Kil)

/-- Delay-decoupling correction `G_dei = gdei · J`. -/
def Gdei : Matrix (Fin 2) (Fin 2) ℂ := (p.gdei : ℂ) • Jc

/-- `G_i^pq = ∂(P,Q)/∂I`. -/
def GiPQ : Matrix (Fin 2) (Fin 2) ℂ := (Gi p.V0).map (algebraMap ℝ ℂ)

/-- `G_v^pq = ∂(P,Q)/∂V`. -/
def GvPQ : Matrix (Fin 2) (Fin 2) ℂ := (Gv p.I0).map (algebraMap ℝ ℂ)

/-- PLL frame projections `G_v^pll`, `G_i^pll`, `G_d^pll`. -/
def Gvpll (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, p.V0 1 * p.Gpll s; 0, 1 - p.V0 0 * p.Gpll s]

def Gipll (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -(p.I0 1 * p.Gpll s); 0, p.I0 0 * p.Gpll s]

def Gdpll (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -(p.D0 1 * p.Gpll s); 0, p.D0 0 * p.Gpll s]

/-- `Φ_full = G_ci G_cpq G_i^pq + G_ci − G_dei`. -/
def Phi (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (p.Gci s * p.Gcpq s) • p.GiPQ + p.Gci s • (1 : Matrix (Fin 2) (Fin 2) ℂ) - p.Gdei

/-- `Θ_full = G_d^pll + G_ci G_cpq G_v^pq G_v^pll − Φ_full G_i^pll`. -/
def Theta (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  p.Gdpll s + (p.Gci s * p.Gcpq s) • (p.GvPQ * p.Gvpll s) - p.Phi s * p.Gipll s

/-- The closed form `Y = [I − G_id G_del Φ]⁻¹ [Z_oc⁻¹ + G_id G_del Θ]` (`K = I`). -/
def Ygfl (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 - Gid p.L p.R p.ω p.Vdc s * (p.Gdel s • p.Phi s))⁻¹ *
    ((Zoc p.L p.R p.ω s)⁻¹ + Gid p.L p.R p.ω p.Vdc s * (p.Gdel s • p.Theta s))

/-- The closed form solves the port equation `Z_oc Y + V_dc G_del (Φ Y + Θ) = I`. -/
@[powerlib_foundation] theorem Ygfl_spec {s : ℂ} (hZ : (Zoc p.L p.R p.ω s).det ≠ 0)
    (hP : (1 - Gid p.L p.R p.ω p.Vdc s * (p.Gdel s • p.Phi s)).det ≠ 0) :
    Zoc p.L p.R p.ω s * p.Ygfl s +
      ((p.Vdc : ℂ) * p.Gdel s) • (p.Phi s * p.Ygfl s + p.Theta s) = 1 := by
  set Z := Zoc p.L p.R p.ω s with hZdef
  set P := 1 - Gid p.L p.R p.ω p.Vdc s * (p.Gdel s • p.Phi s) with hPdef
  set Y := p.Ygfl s with hYdef
  have hZu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hPY : P * Y = Z⁻¹ + Gid p.L p.R p.ω p.Vdc s * (p.Gdel s • p.Theta s) := by
    rw [hYdef, Ygfl, ← hPdef, ← hZdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu,
      Matrix.one_mul]
  have hZG : Z * Gid p.L p.R p.ω p.Vdc s = -((p.Vdc : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [Gid, ← hZdef, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hZu]
  have key := congrArg (fun M => Z * M) hPY
  simp only [hPdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_add, Matrix.mul_nonsing_inv _ hZu, ← Matrix.mul_assoc, hZG] at key
  simp only [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul] at key
  linear_combination (norm := module) key

/-! ## The state response along an input direction -/

section Resp

variable (Y : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (c : Fin 2)

/-- PLL angle response `Δθ = G_pll ΔV_q`. -/
def rθ : ℂ := p.Gpll s * unitVec c 1

/-- `ΔI^pll` response. -/
def rip : Fin 2 → ℂ := ![Y 0 c + p.rθ s c * p.I0 1, Y 1 c - p.rθ s c * p.I0 0]

/-- `ΔV^pll` response. -/
def rvp : Fin 2 → ℂ := ![unitVec c 0 + p.rθ s c * p.V0 1, unitVec c 1 - p.rθ s c * p.V0 0]

/-- Power error response `G_i^pq ΔI^pll + G_v^pq ΔV^pll`. -/
def rep : Fin 2 → ℂ :=
  ![p.V0 0 * p.rip Y s c 0 + p.V0 1 * p.rip Y s c 1 +
      (p.I0 0 * p.rvp s c 0 + p.I0 1 * p.rvp s c 1),
    p.V0 1 * p.rip Y s c 0 - p.V0 0 * p.rip Y s c 1 +
      (-(p.I0 1 * p.rvp s c 0) + p.I0 0 * p.rvp s c 1)]

/-- Current-loop error response `ΔI_ref − ΔI^pll`, `ΔI_ref = −G_cpq e`. -/
def rcc : Fin 2 → ℂ := ![-(p.Gcpq s * p.rep Y s c 0) - p.rip Y s c 0,
  -(p.Gcpq s * p.rep Y s c 1) - p.rip Y s c 1]

/-- Duty response. -/
def rd : Fin 2 → ℂ :=
  ![-(p.Gci s * p.rcc Y s c 0) + p.gdei * p.rip Y s c 1 - p.rθ s c * p.D0 1,
    -(p.Gci s * p.rcc Y s c 1) - p.gdei * p.rip Y s c 0 + p.rθ s c * p.D0 0]

/-- Response of the ten states to a unit port-voltage perturbation along `e_c`. -/
def resp : Fin 10 → ℂ :=
  ![Y 0 c, Y 1 c, p.rd Y s c 0 / (1 + p.a * s), p.rd Y s c 1 / (1 + p.a * s), p.rθ s c,
    (s + p.V0 0 * p.Kpl) * p.rθ s c - p.Kpl * unitVec c 1, p.rcc Y s c 0 / s,
    p.rcc Y s c 1 / s, p.rep Y s c 0 / s, p.rep Y s c 1 / s]

@[powerlib_foundation] theorem ipll_resp :
    p.ipll (p.resp Y s c) = p.rip Y s c := by
  ext k
  fin_cases k <;> simp [ipll, resp, rip]

@[powerlib_foundation] theorem vpll_resp :
    p.vpll (p.resp Y s c) (unitVec c) = p.rvp s c := by
  ext k
  fin_cases k <;> simp [vpll, resp, rvp]

@[powerlib_foundation] theorem epq_resp :
    p.epq (p.resp Y s c) (unitVec c) = p.rep Y s c := by
  ext k
  fin_cases k <;> simp [epq, ipll_resp, vpll_resp, rep]

@[powerlib_foundation] theorem iref_sub_resp (k : Fin 2) :
    p.iref (p.resp Y s c) (unitVec c) k - p.ipll (p.resp Y s c) k = p.rcc Y s c k := by
  simp only [iref, epq_resp, ipll_resp]
  fin_cases k <;> simp [rcc, Gcpq, resp] <;> ring

@[powerlib_foundation] theorem duty_resp :
    p.duty (p.resp Y s c) (unitVec c) = p.rd Y s c := by
  ext k
  fin_cases k
  · simp only [duty, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [p.iref_sub_resp Y s c 0, ipll_resp]
    simp [rd, resp, Gci]
    ring
  · simp only [duty, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [p.iref_sub_resp Y s c 1, ipll_resp]
    simp [rd, resp, Gci]
    ring

/-- The `(k, c)` entry of `Φ Y + Θ` is the duty response. -/
@[powerlib_foundation] theorem phiY_theta (k : Fin 2) :
    (p.Phi s * Y + p.Theta s) k c = p.rd Y s c k := by
  fin_cases k <;> fin_cases c <;>
    simp [Phi, Theta, GiPQ, GvPQ, Gi, Gv, Gvpll, Gipll, Gdpll, Gdei, Jc, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, rd, rcc, rep, rip, rvp, rθ, unitVec] <;> ring

end Resp

@[powerlib_foundation] theorem one_apply_eq_unitVec (k c : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) k c = unitVec c k := by
  simp [unitVec, Matrix.one_apply, eq_comm]

/-- If `Y` solves the port equation, `resp` solves `s x = lin x e_c`. -/
@[powerlib_foundation] theorem resp_lin {Y : Matrix (Fin 2) (Fin 2) ℂ} {s : ℂ} (hs : s ≠ 0)
    (ha : p.a ≠ 0) (hda : 1 + (p.a : ℂ) * s ≠ 0) (hL : p.L ≠ 0)
    (hpll : s ^ 2 + p.V0 0 * p.Kpl * s + p.V0 0 * p.Kil ≠ 0)
    (hY : Zoc p.L p.R p.ω s * Y + ((p.Vdc : ℂ) * p.Gdel s) • (p.Phi s * Y + p.Theta s) = 1)
    (c : Fin 2) :
    s • p.resp Y s c = p.lin (p.resp Y s c) (unitVec c) := by
  have hL' : (p.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have ha' : (p.a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hda2 : 1 + s * (p.a : ℂ) ≠ 0 := by rwa [mul_comm] at hda
  have hpll2 : s * (p.V0 0 : ℂ) * p.Kpl + s ^ 2 + p.V0 0 * p.Kil ≠ 0 := by
    intro h
    apply hpll
    linear_combination h
  have hk : ∀ k : Fin 2, (Zoc p.L p.R p.ω s * Y) k c +
      (p.Vdc * p.Gdel s) * p.rd Y s c k = unitVec c k := by
    intro k
    have := congrFun (congrFun hY k) c
    rw [Matrix.add_apply, Matrix.smul_apply, phiY_theta, smul_eq_mul,
      one_apply_eq_unitVec] at this
    exact this
  have h0 := hk 0
  have h1 := hk 1
  simp only [Zoc_eq, Matrix.mul_apply, Fin.sum_univ_two, Gdel, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at h0 h1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases i <;>
    simp only [lin, duty_resp, vpll_resp, epq_resp, iref_sub_resp, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val, map_inv₀]
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hL')]
    simp [resp]
    linear_combination h0
  · rw [eq_inv_mul_iff_mul_eq₀ (by simpa using hL')]
    simp [resp]
    linear_combination h1
  · simp [resp]
    field_simp
    ring
  · simp [resp]
    field_simp
    ring
  · simp [resp, rvp]
    ring
  · have hG : p.Gpll s * (s ^ 2 + p.V0 0 * p.Kpl * s + p.V0 0 * p.Kil) = p.Kpl * s + p.Kil :=
      div_mul_cancel₀ _ hpll
    simp [resp, rvp, rθ]
    linear_combination (unitVec c 1) * hG
  · simp [resp]
    field_simp
  · simp [resp]
    field_simp
  · simp [resp]
    field_simp
  · simp [resp]
    field_simp

/-- A solution of `(sI − A) X = B` gives the transfer matrix `C X + D`. -/
@[powerlib_foundation] theorem _root_.powerlib.CurrentControl.transfer_eq_of_solution
    {n k : ℕ} (m : Plant n k) (s : ℂ) (X : Matrix (Fin n) (Fin k) ℂ)
    (hM : (characteristicMatrix m.A s).det ≠ 0)
    (hX : characteristicMatrix m.A s * X = complexify m.B) :
    transfer m s = complexify m.C * X + complexify m.D := by
  rw [transfer, Matrix.mul_assoc, ← hX,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hM)]

/-- The 10-state realization has exactly the closed-form GFL port admittance. -/
@[powerlib_foundation] theorem transfer_eq_Ygfl {s : ℂ} (hs : s ≠ 0) (ha : p.a ≠ 0)
    (hda : 1 + (p.a : ℂ) * s ≠ 0) (hL : p.L ≠ 0) (hpll : s ^ 2 + p.V0 0 * p.Kpl * s + p.V0 0 * p.Kil ≠ 0)
    (hZ : (Zoc p.L p.R p.ω s).det ≠ 0)
    (hP : (1 - Gid p.L p.R p.ω p.Vdc s * (p.Gdel s • p.Phi s)).det ≠ 0)
    (hM : (characteristicMatrix p.model.A s).det ≠ 0) :
    transfer p.model s = p.Ygfl s := by
  have hY := p.Ygfl_spec hZ hP
  set X : Matrix (Fin 10) (Fin 2) ℂ := Matrix.of fun i c => p.resp (p.Ygfl s) s c i with hX
  have hMX : characteristicMatrix p.model.A s * X = complexify p.model.B := by
    ext i c
    have h := congrFun (p.resp_lin hs ha hda hL hpll hY c) i
    rw [p.lin_eq_mulVec] at h
    have hB : (p.B.map (algebraMap ℝ ℂ) *ᵥ unitVec c) i = p.B.map (algebraMap ℝ ℂ) i c := by
      simp [Matrix.mulVec, dotProduct, unitVec]
    have hAX : (p.A.map (algebraMap ℝ ℂ) * X) i c =
        (p.A.map (algebraMap ℝ ℂ) *ᵥ p.resp (p.Ygfl s) s c) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, hB] at h
    simp only [characteristicMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, model, hAX]
    have hXic : X i c = p.resp (p.Ygfl s) s c i := by simp [hX]
    rw [hXic, h, add_sub_cancel_left]
  rw [transfer_eq_of_solution _ _ _ hM hMX]
  ext k c
  fin_cases k <;> simp [model, gflOutput, hX, Matrix.mul_apply, Fin.sum_univ_succ, resp]

/-- The GFL realization as the load of the grid-side network of `Network.lean`. -/
def gflOnNetwork (Lg Rg Rl C : ℝ) : Circuits.Interconnection 4 10 2 :=
  withNetwork Lg Rg Rl C p.ω p.model p.model_D

/-- Return difference of the GFL–grid interconnection: `det (I + Z_ext Y_gfl)`. -/
@[powerlib_foundation] theorem gflOnNetwork_returnDifference {Lg Rg Rl C : ℝ} (hC : C ≠ 0)
    (hLg : Lg ≠ 0) {s : ℂ}
    (hMn : (characteristicMatrix (networkModel Lg Rg Rl C p.ω).A s).det ≠ 0)
    (hZn : (Zoc Lg Rg p.ω s).det ≠ 0) (hs : s ≠ 0) (ha : p.a ≠ 0)
    (hda : 1 + (p.a : ℂ) * s ≠ 0) (hL : p.L ≠ 0)
    (hpll : s ^ 2 + p.V0 0 * p.Kpl * s + p.V0 0 * p.Kil ≠ 0)
    (hZ : (Zoc p.L p.R p.ω s).det ≠ 0)
    (hP : (1 - Gid p.L p.R p.ω p.Vdc s * (p.Gdel s • p.Phi s)).det ≠ 0)
    (hM : (characteristicMatrix p.model.A s).det ≠ 0) :
    (p.gflOnNetwork Lg Rg Rl C).returnDifference s =
      (1 + Zext Lg Rg Rl C p.ω s * p.Ygfl s).det := by
  rw [gflOnNetwork, withNetwork_returnDifference hC hLg _ _ hMn hZn,
    p.transfer_eq_Ygfl hs ha hda hL hpll hZ hP hM]

end GFLParams

end powerlib.CurrentControl
