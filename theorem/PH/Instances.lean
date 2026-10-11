import theorem.PortHamiltonian
import theorem.PH.Nonlinear

/-! # Small port-Hamiltonian instances: DC-link capacitor, dq LC filter, disturbance channels

Three independent models; each one uses a single power-direction convention
(incoming-positive: `uᵀ y > 0` means power flows **into** the model).

## DC-link capacitor (`dcLink`)
* State `x = (q)`, `q = C_dc V_dc` the capacitor charge; `C_dc > 0`. `H = q² / (2 C_dc)
  = ½ C_dc V_dc²`.
* Inputs `u = (i_in, i_out)`: current into the positive rail from the source side and current
  drawn by the inverter side. Dynamics `C_dc V̇_dc = i_in − i_out`.
* pH data: `J = 0`, no damping (ideal capacitor, no leakage), `w = 1 / C_dc`, `B = (1, −1)`.
  Output `y = (V_dc, −V_dc)`, so `uᵀ y = V_dc (i_in − i_out)`.
* Lumped, continuous time; the converter switching, its controller and the AC side are not
  modelled (they only enter through the two current inputs).
Source: work-sync `theory/T-low-inertia-frequency.md` §1.4.

## dq LC filter (`dqLC`)
* Rotating dq frame at a **constant** angular frequency `ω` (any real number); `L_f, C_f > 0`;
  lossless (`R_f = 0`). Topology of the note: `C_f` from the PCC node to ground, `L_f` from
  the PCC to the converter terminal; the PCC voltage is the capacitor state.
* Energy variables: state order `x = (φ_d, φ_q, q_d, q_q) = (L_f I_d, L_f I_q, C_f V_d, C_f V_q)`.
  `H = ½ L_f |I|² + ½ C_f |V|²`.
* Inputs `u = (V_d^conv, V_q^conv, I_d^src, I_q^src)`. Dynamics (note §1.4):
  `L_f İ_d = V_d − V_d^conv + ω L_f I_q`, `L_f İ_q = V_q − V_q^conv − ω L_f I_d`,
  `C_f V̇_d = I_d^src − I_d + ω C_f V_q`, `C_f V̇_q = I_q^src − I_q − ω C_f V_d`.
* pH data: constant skew `J` containing the frame-rotation entries `± ω L_f`, `± ω C_f` and the
  inductor/capacitor coupling `± 1`; no damping; `B = diag(−1, −1, 1, 1)`.
  Result: `Ḣ = P_src − P_conv` with `P_src = V·I^src`, `P_conv = V^conv·I`.
* No PLL, no converter control, no switching, no grid impedance.
Source: work-sync `theory/T-invariant-coordinates.md` §1.4 and "跟端口哈密顿建模的关系".

## Disturbance channels (`gridDisturbance`)
* A nonlinear pH model (`NonlinearModel`, P0b) driven by its own control port `u_S` and three
  further deterministic input channels: a constant frequency channel `B_ω u_ω`, a
  state-dependent voltage channel `B_v(x) u_v`, and a constant channel `B_T u_T`
  (note (1.1)). Result: the pointwise energy balance (note (1.2)) split by channel,
  `Ḣ = −∇Hᵀ R ∇H + y_Sᵀ u_S + y_ωᵀ u_ω + y_vᵀ u_v + y_Tᵀ u_T`, `y_k = B_kᵀ ∇H`.
  No noise (the σ → 0 limit of the note), no Itô correction.
Source: work-sync `theory/T-grid-disturbance.md` (1.1), §1.5 (1.2).
The linear diagonal special case of (1.2) is `powerlib.PortHamiltonian.power_balance`.
-/

noncomputable section
namespace powerlib.PH
open Matrix Set MeasureTheory

/-! ## DC-link capacitor -/

/-- The DC-link capacitor as a one-state port-Hamiltonian model. -/
def dcLink (C : ℝ) (hC : 0 < C) : PortHamiltonian.Model (Fin 1) (Fin 2) where
  J := 0
  d := 0
  w := ![1 / C]
  B := !![1, -1]
  skew := by simp
  damping_nonneg := fun _ => le_rfl
  weights_pos := by
    intro i
    fin_cases i
    simp [hC]

/-- The pH field is `C_dc V̇_dc = i_in − i_out`, written for the charge `q = C_dc V_dc`. -/
@[powerlib_domain] theorem dcLink_field (C : ℝ) (hC : 0 < C) (x : Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    PortHamiltonian.field (dcLink C hC) x u = ![u 0 - u 1] := by
  ext i
  fin_cases i
  simp [PortHamiltonian.field, dcLink, dotProduct, Fin.sum_univ_two]
  ring

/-- The stored energy is `½ C_dc V_dc²` with `V_dc = q / C_dc`. -/
@[powerlib_foundation] theorem dcLink_energy (C : ℝ) (hC : 0 < C) (V : ℝ) :
    PortHamiltonian.energy (dcLink C hC) ![C * V] = C * V ^ 2 / 2 := by
  simp [PortHamiltonian.energy, dcLink]
  field_simp

/-- `ΔE_dc = ½ C_dc (V_dc² − V_dc,0²)`. -/
@[powerlib_foundation] theorem dcLink_energy_sub (C : ℝ) (hC : 0 < C) (V V₀ : ℝ) :
    PortHamiltonian.energy (dcLink C hC) ![C * V] -
        PortHamiltonian.energy (dcLink C hC) ![C * V₀] = C * (V ^ 2 - V₀ ^ 2) / 2 := by
  rw [dcLink_energy, dcLink_energy]
  ring

/-- Port power of the DC link: `uᵀ y = V_dc (i_in − i_out)`. -/
@[powerlib_domain] theorem dcLink_supply (C : ℝ) (hC : 0 < C) (x : Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    Passivity.supply (PortHamiltonian.system (dcLink C hC)) x u = (x 0 / C) * (u 0 - u 1) := by
  simp [Passivity.supply, PortHamiltonian.system, PortHamiltonian.output,
    PortHamiltonian.gradient, dcLink, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The DC link is lossless: along every trajectory the energy change equals the integral
of the port power `V_dc (i_in − i_out)` (equality, not only the passivity inequality). -/
@[powerlib_domain] theorem dcLink_energy_balance (C : ℝ) (hC : 0 < C)
    {u : ℝ → (Fin 2 → ℝ)} {x : ℝ → (Fin 1 → ℝ)}
    (hx : Passivity.IsTrajectory (PortHamiltonian.system (dcLink C hC)) u x) {t : ℝ} (ht : 0 ≤ t)
    (hint : IntervalIntegrable (fun τ => (x τ 0 / C) * (u τ 0 - u τ 1)) volume 0 t) :
    PortHamiltonian.energy (dcLink C hC) (x t) - PortHamiltonian.energy (dcLink C hC) (x 0) =
      ∫ τ in (0 : ℝ)..t, (x τ 0 / C) * (u τ 0 - u τ 1) := by
  have hderiv : ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => PortHamiltonian.energy (dcLink C hC) (x s))
      ((x τ 0 / C) * (u τ 0 - u τ 1)) (Ici 0) τ := by
    intro τ hτ
    have h := PortHamiltonian.trajectory_energy_derivative (dcLink C hC) hx hτ
    have hd : PortHamiltonian.dampingPower (dcLink C hC) (x τ) = 0 := by
      simp [PortHamiltonian.dampingPower, dcLink]
    rwa [hd, sub_zero, dcLink_supply] at h
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (fun τ hτ => (hderiv τ hτ.1).continuousWithinAt.mono (fun _ h => h.1))
    (fun τ hτ => (hderiv τ hτ.1.le).mono (fun r hr => hτ.1.le.trans hr.le)) hint]

/-- Passivity of the DC link with storage `½ C_dc V_dc²`. -/
@[powerlib_domain] theorem dcLink_passiveWithStorage (C : ℝ) (hC : 0 < C) :
    Passivity.PassiveWithStorage (PortHamiltonian.system (dcLink C hC))
      (PortHamiltonian.energy (dcLink C hC)) :=
  PortHamiltonian.passiveWithStorage (dcLink C hC)

/-! ## dq LC filter in energy variables -/

/-- Parameters of the lossless dq LC filter. -/
structure DqLCParams where
  L : ℝ
  C : ℝ
  ω : ℝ
  L_pos : 0 < L
  C_pos : 0 < C

/-- The dq LC filter as a constant-`J` port-Hamiltonian model, state
`(φ_d, φ_q, q_d, q_q)`, inputs `(V_d^conv, V_q^conv, I_d^src, I_q^src)`. -/
def dqLC (p : DqLCParams) : PortHamiltonian.Model (Fin 4) (Fin 4) where
  J := !![0, p.ω * p.L, 1, 0; -(p.ω * p.L), 0, 0, 1; -1, 0, 0, p.ω * p.C; 0, -1, -(p.ω * p.C), 0]
  d := 0
  w := ![1 / p.L, 1 / p.L, 1 / p.C, 1 / p.C]
  B := !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  skew := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  damping_nonneg := fun _ => le_rfl
  weights_pos := by
    intro i
    fin_cases i <;> simp [p.L_pos, p.C_pos]

/-- The rate equations of the note, in energy variables
(`φ = L_f I`, `q = C_f V`). -/
def dqLC_kirchhoffField (p : DqLCParams) (x u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 2 / p.C - u 0 + p.ω * x 1,
    x 3 / p.C - u 1 - p.ω * x 0,
    u 2 - x 0 / p.L + p.ω * x 3,
    u 3 - x 1 / p.L - p.ω * x 2]

/-- The pH field reproduces the dq LC rate equations exactly. -/
@[powerlib_domain] theorem dqLC_field_eq_kirchhoff (p : DqLCParams) (x u : Fin 4 → ℝ) :
    PortHamiltonian.field (dqLC p) x u = dqLC_kirchhoffField p x u := by
  have hL := p.L_pos.ne'
  have hC := p.C_pos.ne'
  ext i
  fin_cases i <;>
    simp [PortHamiltonian.field, PortHamiltonian.gradient, dqLC, dqLC_kirchhoffField,
      dotProduct, Fin.sum_univ_four]
  all_goals field_simp
  all_goals ring

/-- The pH energy in physical coordinates: `H = ½ L_f |I|² + ½ C_f |V|²`. -/
@[powerlib_foundation] theorem dqLC_energy (p : DqLCParams) (Id Iq Vd Vq : ℝ) :
    PortHamiltonian.energy (dqLC p) ![p.L * Id, p.L * Iq, p.C * Vd, p.C * Vq] =
      p.L * (Id ^ 2 + Iq ^ 2) / 2 + p.C * (Vd ^ 2 + Vq ^ 2) / 2 := by
  have hL := p.L_pos.ne'
  have hC := p.C_pos.ne'
  simp [PortHamiltonian.energy, dqLC, Fin.sum_univ_four]
  field_simp
  ring

/-- Energy balance of the dq LC filter: `Ḣ = P_src − P_conv`
(`P_src = V_d I_d^src + V_q I_q^src`, `P_conv = V_d^conv I_d + V_q^conv I_q`);
the frame-rotation terms cancel. -/
@[powerlib_domain] theorem dqLC_power_balance (p : DqLCParams) (x u : Fin 4 → ℝ) :
    dotProduct (PortHamiltonian.gradient (dqLC p) x) (PortHamiltonian.field (dqLC p) x u) =
      ((x 2 / p.C) * u 2 + (x 3 / p.C) * u 3) - (u 0 * (x 0 / p.L) + u 1 * (x 1 / p.L)) := by
  rw [PortHamiltonian.power_balance]
  simp [Passivity.supply, PortHamiltonian.system, PortHamiltonian.output,
    PortHamiltonian.dampingPower, PortHamiltonian.gradient, dqLC, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- Along every trajectory, `d/dt H = P_src − P_conv`. -/
@[powerlib_domain] theorem dqLC_trajectory_energy_derivative (p : DqLCParams)
    {u : ℝ → (Fin 4 → ℝ)} {x : ℝ → (Fin 4 → ℝ)}
    (hx : Passivity.IsTrajectory (PortHamiltonian.system (dqLC p)) u x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => PortHamiltonian.energy (dqLC p) (x τ))
      (((x t 2 / p.C) * u t 2 + (x t 3 / p.C) * u t 3) -
        (u t 0 * (x t 0 / p.L) + u t 1 * (x t 1 / p.L))) (Ici 0) t := by
  rw [← dqLC_power_balance]
  exact PortHamiltonian.energy_derivative (dqLC p) (hx t ht)

/-- Passivity of the dq LC filter with storage `H`. -/
@[powerlib_domain] theorem dqLC_passiveWithStorage (p : DqLCParams) :
    Passivity.PassiveWithStorage (PortHamiltonian.system (dqLC p))
      (PortHamiltonian.energy (dqLC p)) :=
  PortHamiltonian.passiveWithStorage (dqLC p)

/-- Lyapunov stability of the unforced lossless filter at the origin. -/
@[powerlib_domain] theorem dqLC_lyapunovStable (p : DqLCParams) :
    Passivity.LyapunovStable (PortHamiltonian.system (dqLC p)) :=
  PortHamiltonian.lyapunovStable (dqLC p)

/-! ## Deterministic disturbance channels on a nonlinear pH model -/

variable {n m a b c : ℕ}

/-- Field (1.1) of T-grid-disturbance: the pH drift and control port of `M`, plus a constant
frequency channel `Bω uω`, a state-dependent voltage channel `Bv(x) uv`, and a constant
channel `BT uT`. -/
def gridDisturbance_field (M : NonlinearModel n m) (Bω : Matrix (Fin n) (Fin a) ℝ)
    (Bv : Dynamics.State n → Matrix (Fin n) (Fin b) ℝ) (BT : Matrix (Fin n) (Fin c) ℝ)
    (x : Dynamics.State n) (uS : Fin m → ℝ) (uω : Fin a → ℝ) (uv : Fin b → ℝ)
    (uT : Fin c → ℝ) : Dynamics.State n :=
  M.field x uS + WithLp.toLp 2 (Bω *ᵥ uω + Bv x *ᵥ uv + BT *ᵥ uT)

/-- Energy balance (1.2) split by channel:
`Ḣ = y_Sᵀ u_S + y_ωᵀ u_ω + y_vᵀ u_v + y_Tᵀ u_T − ∇Hᵀ R ∇H`, `y_k = B_kᵀ ∇H`. -/
@[powerlib_foundation] theorem gridDisturbance_power_balance (M : NonlinearModel n m)
    (Bω : Matrix (Fin n) (Fin a) ℝ) (Bv : Dynamics.State n → Matrix (Fin n) (Fin b) ℝ)
    (BT : Matrix (Fin n) (Fin c) ℝ) (x : Dynamics.State n) (uS : Fin m → ℝ)
    (uω : Fin a → ℝ) (uv : Fin b → ℝ) (uT : Fin c → ℝ) :
    fderiv ℝ M.H x (gridDisturbance_field M Bω Bv BT x uS uω uv uT) =
      M.supply x uS + uω ⬝ᵥ (Bωᵀ *ᵥ WithLp.ofLp (M.dH x)) +
        uv ⬝ᵥ ((Bv x)ᵀ *ᵥ WithLp.ofLp (M.dH x)) + uT ⬝ᵥ (BTᵀ *ᵥ WithLp.ofLp (M.dH x)) -
        M.dampingPower x := by
  have hport : ∀ {k : ℕ} (G : Matrix (Fin n) (Fin k) ℝ) (v : Fin k → ℝ),
      WithLp.ofLp (M.dH x) ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ (Gᵀ *ᵥ WithLp.ofLp (M.dH x)) := by
    intro k G v
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  rw [gridDisturbance_field, map_add, M.power_balance, M.fderiv_H_apply, WithLp.ofLp_toLp,
    dotProduct_add, dotProduct_add, hport, hport, hport]
  ring

end powerlib.PH
