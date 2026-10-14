import theorem.PH.Composition
import theorem.PH.Nonlinear

/-! # Small port-Hamiltonian instances: DC-link capacitor, dq LC filter

Two independent lossless circuit models as diagonal port-Hamiltonian data, read through the
linear port-Hamiltonian family; each uses the incoming-positive power convention (`uᵀ y > 0`
means power flows **into** the model).

Model boundary.
DC-link capacitor (`dcLink`, T-low-inertia-frequency §1.4):
* State `x = (q)`, `q = C_dc V_dc` the capacitor charge; `C_dc > 0`. `H = q² / (2 C_dc)
  = ½ C_dc V_dc²`.
* Inputs `u = (i_in, i_out)`: current into the positive rail from the source side and current
  drawn by the inverter side. Dynamics `C_dc V̇_dc = i_in − i_out`.
* pH data: `J = 0`, no damping (ideal capacitor, no leakage), `w = 1 / C_dc`, `B = (1, −1)`.
  Output `y = (V_dc, −V_dc)`, so `uᵀ y = V_dc (i_in − i_out)`.
* Lumped, continuous time; the converter switching, its controller and the AC side are not
  modelled (they only enter through the two current inputs).
dq LC filter (`dqLC`, T-invariant-coordinates §1.4):
* Rotating dq frame at a **constant** angular frequency `ω` (any real number); `L_f, C_f > 0`;
  lossless (`R_f = 0`). Topology of the note: `C_f` from the PCC node to ground, `L_f` from
  the PCC to the converter terminal; the PCC voltage is the capacitor state.
* Energy variables: state order
  `x = (φ_d, φ_q, q_d, q_q) = (L_f I_d, L_f I_q, C_f V_d, C_f V_q)`.
  `H = ½ L_f |I|² + ½ C_f |V|²`.
* Inputs `u = (V_d^conv, V_q^conv, I_d^src, I_q^src)`. Dynamics (note §1.4):
  `L_f İ_d = V_d − V_d^conv + ω L_f I_q`, `L_f İ_q = V_q − V_q^conv − ω L_f I_d`,
  `C_f V̇_d = I_d^src − I_d + ω C_f V_q`, `C_f V̇_q = I_q^src − I_q − ω C_f V_d`.
* pH data: constant skew `J` containing the frame-rotation entries `± ω L_f`, `± ω C_f` and the
  inductor/capacitor coupling `± 1`; no damping; `B = diag(−1, −1, 1, 1)`.
* No PLL, no converter control, no switching, no grid impedance.

Source: work-sync `theory/T-low-inertia-frequency.md` §1.4 (DC link);
`theory/T-invariant-coordinates.md` §1.4 and "跟端口哈密顿建模的关系" (dq LC filter).

Results (static evidence on the models).
* `dcLink_field`, `dcLink_supply`, `dcLink_energy_sub` — the pH field is
  `C_dc V̇_dc = i_in − i_out`, the port power is `V_dc (i_in − i_out)`, and
  `ΔE_dc = ½ C_dc (V_dc² − V_dc,0²)`.
* `dqLC_field_eq_kirchhoff` — the pH field reproduces the dq LC rate equations exactly;
  `dqLC_power_balance` — `Ḣ = P_src − P_conv` with `P_src = V·I^src`, `P_conv = V^conv·I`.
* The deterministic disturbance-channel energy balance on a nonlinear pH model
  (`PH.gridDisturbance_field`, `PH.gridDisturbance_power_balance`) is in
  `theorem/PH/Nonlinear.lean`.

Family and connection conclusions.
* No new family. The DC link and the dq LC filter are diagonal port-Hamiltonian data
  (`DiagonalPH`, `theorem/PH/Composition.lean`), numbered in the state and port order above into
  linear port-Hamiltonian plants `dcLinkPH C hC : Port.PortHamiltonian 1 2` and
  `dqLCPH p : Port.PortHamiltonian 4 4`, members of the existing family
  `Port.PortHamiltonian.family` (system map: the plant's port system; sentences at the origin,
  the unforced state).
* Connection conclusions: passivity of both (`dcLinkPH_mem_den_passive`,
  `dqLCPH_mem_den_passive`), Lyapunov stability of the unforced filter
  (`dqLCPH_mem_den_lyapunovStable`), and conservation of the stored energy by both lossless
  models (`dcLinkPH_mem_den_conservative`, `dqLCPH_mem_den_conservative`).
* The rate equations, energies, supplies and power balances are static evidence; the
  trajectory-level energy balance of the DC link (`dcLink_energy_balance`) and the energy
  derivative of the filter along solutions (`dqLC_trajectory_energy_derivative`) are private
  implementation evidence.
-/

noncomputable section
namespace powerlib.PH.Models
open Matrix Set MeasureTheory
open powerlib.Dynamics (State)

/-! ## DC-link capacitor -/

/-- The DC-link capacitor as a one-state port-Hamiltonian model. -/
def dcLink (C : ℝ) (hC : 0 < C) : DiagonalPH (Fin 1) (Fin 2) where
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

/-- The pH field is `C_dc V̇_dc = i_in − i_out`, written for the charge `q = C_dc V_dc`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem dcLink_field (C : ℝ) (hC : 0 < C) (x : Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    (dcLink C hC).field x u = ![u 0 - u 1] := by
  ext i
  fin_cases i
  simp [DiagonalPH.field, dcLink, dotProduct, Fin.sum_univ_two]
  ring

/-- The stored energy is `½ C_dc V_dc²` with `V_dc = q / C_dc`. -/
@[powerlib_foundation] theorem dcLink_energy (C : ℝ) (hC : 0 < C) (V : ℝ) :
    (dcLink C hC).energy ![C * V] = C * V ^ 2 / 2 := by
  simp [DiagonalPH.energy, dcLink]
  field_simp

/-- `ΔE_dc = ½ C_dc (V_dc² − V_dc,0²)`. -/
@[powerlib_foundation] theorem dcLink_energy_sub (C : ℝ) (hC : 0 < C) (V V₀ : ℝ) :
    (dcLink C hC).energy ![C * V] - (dcLink C hC).energy ![C * V₀] =
      C * (V ^ 2 - V₀ ^ 2) / 2 := by
  rw [dcLink_energy, dcLink_energy]
  ring

/-- Port power of the DC link: `uᵀ y = V_dc (i_in − i_out)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem dcLink_supply (C : ℝ) (hC : 0 < C) (x : Fin 1 → ℝ)
    (u : Fin 2 → ℝ) : (dcLink C hC).supply x u = (x 0 / C) * (u 0 - u 1) := by
  simp [DiagonalPH.supply, DiagonalPH.output, DiagonalPH.gradient, dcLink, mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The DC link as a linear port-Hamiltonian plant (charge state, ports `(i_in, i_out)`). -/
def dcLinkPH (C : ℝ) (hC : 0 < C) : Port.PortHamiltonian 1 2 :=
  (dcLink C hC).toPH (Equiv.refl _) (Equiv.refl _)

/-- Along a solution segment of a lossless linear pH plant the stored energy has the supplied
power as derivative. -/
private theorem hasDerivWithinAt_storage_of_lossless {n p : ℕ} (h : Port.PortHamiltonian n p)
    (hR : h.R = 0) {u : ℝ → Fin p → ℝ} {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ t₁ t : ℝ}
    (hx : h.plant.system.IsTrajectoryOn u x t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    HasDerivWithinAt (fun τ => h.kyp.storage (x τ)) (h.plant.system.supply (x t) (u t))
      (Icc t₀ t₁) t := by
  have hd := ((storage_contDiff h).differentiable (by norm_num) (x t)).hasFDerivAt
    |>.comp_hasDerivWithinAt t (hx t ht)
  rw [Function.comp_def, fderiv_storage_field, hR] at hd
  simpa using hd

/-- The DC link is lossless, so along every solution segment the energy change equals the
integral of the port power `V_dc (i_in − i_out)` (equality, not only the passivity inequality).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem dcLink_energy_balance (C : ℝ) (hC : 0 < C)
    {u : ℝ → (Fin 2 → ℝ)} {x : ℝ → EuclideanSpace ℝ (Fin 1)} {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (hx : (dcLinkPH C hC).plant.system.IsTrajectoryOn u x t₀ t₁)
    (hint : IntervalIntegrable (fun τ => (x τ 0 / C) * (u τ 0 - u τ 1)) volume t₀ t₁) :
    (dcLink C hC).energy (WithLp.ofLp (x t₁)) - (dcLink C hC).energy (WithLp.ofLp (x t₀)) =
      ∫ τ in t₀..t₁, (x τ 0 / C) * (u τ 0 - u τ 1) := by
  have hR : (dcLinkPH C hC).R = 0 := DiagonalPH.toPH_R_eq_zero _ _ _ rfl
  have hderiv : ∀ τ ∈ Icc t₀ t₁, HasDerivWithinAt
      (fun s => (dcLink C hC).energy (WithLp.ofLp (x s))) ((x τ 0 / C) * (u τ 0 - u τ 1))
      (Icc t₀ t₁) τ := by
    intro τ hτ
    have h := hasDerivWithinAt_storage_of_lossless _ hR hx hτ
    simp only [dcLinkPH, DiagonalPH.toPH_storage, DiagonalPH.toPH_supply, dcLink_supply] at h
    simpa using h
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hle
    (fun τ hτ => (hderiv τ hτ).continuousWithinAt)
    (fun τ hτ => ((hderiv τ (Ioo_subset_Icc_self hτ)).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)).hasDerivWithinAt) hint]

/-- Passivity of the DC link; the storage is `½ C_dc V_dc²` (`toPH_storage`, `dcLink_energy`). -/
@[powerlib_domain] theorem dcLinkPH_mem_den_passive (C : ℝ) (hC : 0 < C) :
    connection% (dcLinkPH C hC ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- With both currents at zero the capacitor keeps its energy. -/
@[powerlib_domain] theorem dcLinkPH_mem_den_conservative (C : ℝ) (hC : 0 < C) :
    connection% (dcLinkPH C hC ∈ Port.PortHamiltonian.family.den (.flow .conservative)) :=
  mem_den_conservative_of_lossless _ (DiagonalPH.toPH_R_eq_zero _ _ _ rfl)

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
def dqLC (p : DqLCParams) : DiagonalPH (Fin 4) (Fin 4) where
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

/-- The pH field reproduces the dq LC rate equations exactly.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem dqLC_field_eq_kirchhoff (p : DqLCParams) (x u : Fin 4 → ℝ) :
    (dqLC p).field x u = dqLC_kirchhoffField p x u := by
  have hL := p.L_pos.ne'
  have hC := p.C_pos.ne'
  ext i
  fin_cases i <;>
    simp [DiagonalPH.field, DiagonalPH.gradient, dqLC, dqLC_kirchhoffField,
      dotProduct, Fin.sum_univ_four]
  all_goals field_simp
  all_goals ring

/-- The pH energy in physical coordinates: `H = ½ L_f |I|² + ½ C_f |V|²`. -/
@[powerlib_foundation] theorem dqLC_energy (p : DqLCParams) (Id Iq Vd Vq : ℝ) :
    (dqLC p).energy ![p.L * Id, p.L * Iq, p.C * Vd, p.C * Vq] =
      p.L * (Id ^ 2 + Iq ^ 2) / 2 + p.C * (Vd ^ 2 + Vq ^ 2) / 2 := by
  have hL := p.L_pos.ne'
  have hC := p.C_pos.ne'
  simp [DiagonalPH.energy, dqLC, Fin.sum_univ_four]
  field_simp
  ring

/-- Energy balance of the dq LC filter: `Ḣ = P_src − P_conv`
(`P_src = V_d I_d^src + V_q I_q^src`, `P_conv = V_d^conv I_d + V_q^conv I_q`);
the frame-rotation terms cancel.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem dqLC_power_balance (p : DqLCParams) (x u : Fin 4 → ℝ) :
    (dqLC p).gradient x ⬝ᵥ (dqLC p).field x u =
      ((x 2 / p.C) * u 2 + (x 3 / p.C) * u 3) - (u 0 * (x 0 / p.L) + u 1 * (x 1 / p.L)) := by
  rw [DiagonalPH.power_balance]
  simp [DiagonalPH.supply, DiagonalPH.output, DiagonalPH.dampingPower, DiagonalPH.gradient,
    dqLC, mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- The dq LC filter as a linear port-Hamiltonian plant, states `(φ_d, φ_q, q_d, q_q)` and
ports `(V_d^conv, V_q^conv, I_d^src, I_q^src)` numbered in order. -/
def dqLCPH (p : DqLCParams) : Port.PortHamiltonian 4 4 :=
  (dqLC p).toPH (Equiv.refl _) (Equiv.refl _)

/-- Along every solution segment, `d/dt H = P_src − P_conv`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem dqLC_trajectory_energy_derivative (p : DqLCParams)
    {u : ℝ → (Fin 4 → ℝ)} {x : ℝ → EuclideanSpace ℝ (Fin 4)} {t₀ t₁ t : ℝ}
    (hx : (dqLCPH p).plant.system.IsTrajectoryOn u x t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    HasDerivWithinAt (fun τ => (dqLC p).energy (WithLp.ofLp (x τ)))
      (((x t 2 / p.C) * u t 2 + (x t 3 / p.C) * u t 3) -
        (u t 0 * (x t 0 / p.L) + u t 1 * (x t 1 / p.L))) (Icc t₀ t₁) t := by
  have hR : (dqLCPH p).R = 0 := DiagonalPH.toPH_R_eq_zero _ _ _ rfl
  have h := hasDerivWithinAt_storage_of_lossless _ hR hx ht
  simp only [dqLCPH, DiagonalPH.toPH_storage, DiagonalPH.toPH_supply] at h
  have hb := dqLC_power_balance p (WithLp.ofLp (x t)) (u t)
  have hd : (dqLC p).dampingPower (WithLp.ofLp (x t)) = 0 := by
    simp [DiagonalPH.dampingPower, dqLC]
  rw [DiagonalPH.power_balance, hd, sub_zero] at hb
  exact h.congr_deriv (by rw [← hb]; rfl)

/-- Passivity of the dq LC filter; the storage is `H` (`toPH_storage`). -/
@[powerlib_domain] theorem dqLCPH_mem_den_passive (p : DqLCParams) :
    connection% (dqLCPH p ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- Lyapunov stability of the unforced lossless filter at the origin. -/
@[powerlib_domain] theorem dqLCPH_mem_den_lyapunovStable (p : DqLCParams) :
    connection% (dqLCPH p ∈ Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

/-- The unforced lossless filter conserves its stored energy. -/
@[powerlib_domain] theorem dqLCPH_mem_den_conservative (p : DqLCParams) :
    connection% (dqLCPH p ∈ Port.PortHamiltonian.family.den (.flow .conservative)) :=
  mem_den_conservative_of_lossless _ (DiagonalPH.toPH_R_eq_zero _ _ _ rfl)

end powerlib.PH.Models
