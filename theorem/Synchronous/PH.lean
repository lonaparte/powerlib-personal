import theorem.PH.Linear
import theorem.PH.Linearization
import theorem.Synchronous.Swing
import theorem.Dynamics.Transport
import theorem.Dynamics.ConverseLinearization
import theorem.TMIO.ClaimElab
import theorem.Spectral.Local
import theorem.Spectral.Hub

/-! # Synchronous machines as nonlinear port-Hamiltonian systems

The classical machine on an infinite bus and the seven-state dq machine as instances of
`powerlib.PH.NonlinearModel`, each with its family (`ClassicalSM.family`, `SyncMachine7.family`).
The classical machine is the canonical swing model of `theorem/Synchronous/Swing.lean` in momentum
coordinates with a mechanical-power port: its flow sentences are those of the swing family
`Swing.family` read through `ClassicalSM.Model.toSwing`, and only its port-Hamiltonian content
(Hamiltonian, structure matrices, passivity) is proved here.

Model boundary.
Classical machine (`classicalSM`, T-ph §1.7 (1.12)), continuous time:
* State order `x = (δ, p)`: rotor angle `δ` (electrical radians, relative to the infinite bus)
  and angular momentum `p = M ω` (`ω` the speed deviation). Parameters `M > 0`, `D ≥ 0`,
  synchronizing coefficient `b > 0` (`b = E V / X`), mechanical power `P_m ∈ ℝ`.
* Hamiltonian `H(δ, p) = p² / (2M) − P_m δ − b cos δ`, i.e. electrical potential
  `V_el(δ) = −b cos δ` so that `P_e = ∂V_el/∂δ = b sin δ`. Gradient `(b sin δ − P_m, p / M)`.
* pH data `J = !![0, 1; −1, 0]`, `R = diag(0, D)` (the note's `R₂₂ = D`, no `M⁻²`),
  `g = (0, 1)ᵀ`; external torque/power input `u`, output `y = ω`.
  Dynamics `δ̇ = ω`, `ṗ = P_m − b sin δ − D ω + u` (swing equation).
* Not modelled: flux dynamics, AVR, governor, network beyond the single infinite bus,
  saturation, delay. Equilibrium-level and trajectory-level results under zero input `u = 0`.
* Swing reading: the swing parameters `ClassicalSMParams.toSwing` are `M, D, P_m`, `k₁ = k₃ = 0`,
  `k₂ = b`; under zero input the pH field is that swing field in the coordinates
  `(δ, p) = (δ, M ω)` (`classicalSM_zeroInputField_eq_transport`, `T = diag(1, M)`). The swing
  family has free parameters and no port; the image of `ClassicalSM.Model.toSwing` is the part
  with `M > 0`, `D ≥ 0`, `k₁ = k₃ = 0`, `k₂ > 0`.
Seven-state dq machine (`syncMachine7`, T-sync-machine §1.13), continuous time:
* State order `x = (Ψ_d, Ψ_q, Ψ_f, Ψ_kd, Ψ_kq, p, δ) ∈ ℝ⁷` (`Ψ_0` omitted, three-wire);
  rotor dq frame; **absolute** rotor angle with `δ̇ = ω_r`; `p = M ω_r`.
* Direction convention: stator currents are **IN-positive** (motor convention), obtained from
  the Kundur generator convention of T-sync-machine §1.1–§1.5 by `i^IN = −i^Kun`
  (conventions.md §D2/§D8, as done in §1.13); terminal voltages unchanged; the electromagnetic
  torque is `T_e^em = i_q Ψ_d − i_d Ψ_q` (positive in motor mode).
* Magnetics linear: `Ψ = L i` with `L` symmetric positive definite; the model is parametrised
  by `Γ = L⁻¹` (any symmetric positive definite `5 × 5` matrix; the structured `L` of §1.13
  is `syncMachine7_inductance`). `H = ½ Ψᵀ Γ Ψ + p² / (2M)`; `∇H = (i, ω_r, 0)`.
* Inputs `u = (v_d, v_q, v_f, T_m^ext)`, outputs `y = (i_d, i_q, i_f, ω_r)`.
  `J(x)` state dependent and skew, `R = diag(r_s, r_s, r_f, r_kd, r_kq, D, 0) ⪰ 0`,
  damping acting on `ω_r` (not on `ω_r − ω_s`).
* Not modelled: network, AVR/exciter dynamics, governor, saturation, zero sequence.
  Not an instance of `Port.PortHamiltonian` (`J` depends on the state, `H` is not diagonal).

Scaffold of the reading of `ClassicalSM` through the swing family:
`theorem/ClassicalMachineSwing.agda`.

Source: work-sync `theory/T-ph.md` §1.7 (1.12); `theory/T-sync-machine.md` §1.13.

Results.
* Classical machine: `H` is not bounded below for `P_m ≠ 0`
  (`classicalSM_hamiltonian_not_bddBelow`), while the dissipation inequality
  `H(x(t₁)) − H(x(t₀)) ≤ ∫ u ω` holds on every solution segment (private
  `classicalSM_integral_dissipation`); energy balance `Ḣ = u ω − D ω²`
  (`classicalSM_power_balance`); equilibria `b sin δ = P_m`, `p = 0`
  (`classicalSM_isEquilibrium_iff`).
* Classical machine, local structure of `H`: `H − H(x*)` has a strict local minimum at a stable
  equilibrium `δ* ∈ (−π/2, π/2)`, `b sin δ* = P_m`, `p* = 0` (`classicalSM_isStrictLocalMin`,
  `classicalSM_potential_pos`). (`H − H(x*)` is in general **not** positive on all of
  `|δ − δ*| < π`: it changes sign beyond the unstable equilibrium `π − δ*`; positivity is only
  claimed on `|δ| < π/2`.) Hessian `diag(b cos δ, 1/M)` (`classicalSM_hasFDerivAt_dH`) and
  linearization `(J − R) ∇²H = [[0, 1/M], [−b cos δ*, −D/M]]` (`classicalSM_linearization`); at a
  fold `cos δ* = 0` the Hamiltonian and the accelerating power (`ClassicalSM.classicalSM_H_fold`,
  `ClassicalSM.classicalSM_accel_fold`).
* Seven-state machine: the pH field reproduces every rate equation of §1.13
  (`syncMachine7_field`); the energy balance (`syncMachine7_power_balance`)
  `Ḣ = (v_d i_d + v_q i_q + v_f i_f + T_m ω_r) − (r_s(i_d²+i_q²) + r_f i_f² + r_kd i_kd² +
  r_kq i_kq² + D ω_r²)`; `H ≥ 0` (`syncMachine7_H_nonneg`); passivity with storage `H`
  (`SyncMachine7.mem_den_passive`).

Family and connection conclusions.
* `ClassicalSM.family`: a complete system is the classical machine together with a selected
  rotor angle `δ*` (`ClassicalSM.Model`, operating point `x* = (δ*, 0)`); the system map reads
  the pH system in coordinates centred at `x*` (`NonlinearModel.shift`), because the library
  reads flow sentences at the origin, so every flow sentence speaks about `x*` itself. The
  requirements are static: `x*` is an equilibrium (`b sin δ* = P_m`), the stable branch
  `cos δ* > 0` (invariant under whole turns), strict damping with `cos δ* > 0`, the unstable
  branch `cos δ* < 0`, and zero mechanical power (`P_m = 0`, which bounds `H` below). Lyapunov
  stability translates into an equilibrium on the stable branch, the local attractive sentences
  into a damped equilibrium with `cos δ* > 0`, instability into an equilibrium on the unstable
  branch, passivity into `P_m = 0`; the global sentences, decay rates, sampled contraction and
  conservation have no translation (the whole, inconsistent, language).
* Equivalence with the swing family. The canonical family is `Swing.family`; on every flow
  sentence `ClassicalSM.family` is its pullback through `ClassicalSM.Model.toSwing`
  (`⟨⟨M, D, P_m, 0, b, 0⟩, δ*⟩`), for both connections: the denotations
  (`ClassicalSM.den_flow_eq_preimage`, member form `ClassicalSM.mem_den_flow_iff_swing`; every
  flow sentence is invariant under `diag(1, M)`, `Spectral.mem_den_flow_iff_of_transport`) and the
  translations (`ClassicalSM.realize_translate_flow_eq_preimage`: on the image positive inertia
  and nonnegative damping always hold, `locked` is `balanced`, `stableBranch` is `synchronizing`,
  `damped` is `damped` with `synchronizing`, `unstableBranch` is `destabilizing`). Hence a flow
  translation is exact exactly when it is for `Swing.family.comap ClassicalSM.Model.toSwing`
  (`ClassicalSM.exact_flow_iff`). Passivity is outside the equivalence: the pH family has a port
  and is passive exactly when `P_m = 0`, the swing family has none and every model is passive, so
  the sentence-by-sentence equivalence fails (`ClassicalSM.not_den_eq_preimage`).
* Flow conclusions, all read off the swing family through the equivalence by the hub transfers
  of `theorem/Spectral/Hub.lean`: chain soundness (`ClassicalSM.chain_le_semantics`, from
  `Swing.chain_le_semantics` by `Spectral.sound_of_hub`; passivity from
  `ClassicalSM.mem_den_passive_of_Pm_zero`); members `ClassicalSM.mem_den_lyapunovStable`,
  `ClassicalSM.mem_den_locallyExponentiallyStable`, `ClassicalSM.mem_den_unstable` (from
  `Swing.mem_den_*`). The local exponential and local asymptotic translations are exact
  (`ClassicalSM.exact_locallyExponentiallyStable`, `ClassicalSM.exact_locallyAsymptoticallyStable`,
  from `Swing.exactUnder_*` by `Spectral.exact_of_hub`: every swing reading has positive
  inertia; the degenerate cases, an undamped machine and a fold `cos δ* = 0`, are decided by the
  energy `H`). The Lyapunov translation is exact (`ClassicalSM.exact_lyapunovStable`, from
  `Swing.exactUnder_lyapunovStable` by `Spectral.exact_of_hub`: every swing reading has positive
  inertia and a curved power-angle curve, `k₂ = b > 0`), so the Lyapunov denotation is
  `ClassicalSM.mem_den_lyapunovStable_iff` (`b sin δ* = P_m`, `cos δ* > 0`, every `D ≥ 0`).
  The stable-branch requirement must be invariant under whole turns: with `|δ*| < π/2` instead
  of `cos δ* > 0` the Lyapunov translation would be sound but not exact (`M = b = 1`,
  `D = P_m = 0`, `δ* = 2π` is Lyapunov stable without meeting it). The instability translation is
  not exact (`ClassicalSM.not_exact_unstable`): the unbalanced machine `ClassicalSM.offEquilibrium`
  (`P_m = 2 > b = 1`) is unstable (`ClassicalSM.offEquilibrium_mem_den_unstable`, its swing
  reading is unbalanced, `Swing.mem_den_unstable_of_not_balanced`).
* Passivity, the port-Hamiltonian conclusion: the translation is exact
  (`ClassicalSM.exact_passive`): with `P_m = 0` the Hamiltonian is bounded below
  (`ClassicalSM.mem_den_passive_of_Pm_zero`); for `P_m ≠ 0` the machine is not passive
  (`ClassicalSM.not_mem_den_passive`) — a slow spin `ω₀ = P_m / (2 (D + 1))`, held at constant
  speed by the port, draws `2π |P_m|` minus the damping loss per revolution, so the energy drawn
  over many revolutions exceeds every nonnegative storage.
* `SyncMachine7.family`: a complete system is the seven-state machine (`SyncMachine7Params`),
  read as its pH port system at the origin (the unforced state, an equilibrium). Passivity is
  translated into no requirement and is exact (`H ≥ 0`, `SyncMachine7.mem_den_passive`); flow
  sentences have no translation; the chain lies below the semantics
  (`SyncMachine7.chain_le_semantics`). No machine is locally exponentially stable at the origin,
  whatever its parameters (`SyncMachine7.not_mem_den_locallyExponentiallyStable`): `H` does not
  depend on the rotor angle `δ` and `∇H(0) = 0`, so the Jacobian `(J(0) − R) ∇²H` of the
  zero-input field (`NonlinearModel.fderiv_zeroInputField_of_dH_eq_zero`) kills `e_δ`, while a
  locally exponentially stable point of a `C¹` field has an injective Jacobian (converse
  linearization, `Dynamics.fderiv_injective_of_locallyExponentiallyStable`).
* The rate equations, energies, damping powers, supplies, power balances, equilibrium
  characterization, unboundedness of `H`, the linearization and the swing reading are static
  evidence; the trajectory-level dissipation inequality of the classical machine, the energy
  derivative of the seven-state machine and the smoothness and Jacobian at the origin of its
  zero-input field are private implementation evidence.

Correction.
* T-ph §1.1, structural assumption 3 `H ≥ H_min > −∞`: the classical-machine `H` contains
  `−P_m δ` and is **not bounded below** whenever `P_m ≠ 0`
  (`classicalSM_hamiltonian_not_bddBelow`), so (1.12) violates assumption 3 and the global
  passivity inequality (1.4) with storage `H − H_min` is unavailable; the dissipation
  inequality (`classicalSM_integral_dissipation`) still holds.
-/

noncomputable section
namespace powerlib.Synchronous
open Matrix Set Filter
open scoped Topology
open powerlib.Dynamics (State)
open powerlib.PH

/-- Coordinate functional on `State n`. -/
abbrev smCoord {n : ℕ} (i : Fin n) : State n →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) i

/-! ## Classical machine -/

/-- Parameters of the classical machine on an infinite bus. -/
structure ClassicalSMParams where
  M : ℝ
  D : ℝ
  b : ℝ
  Pm : ℝ
  M_pos : 0 < M
  D_nonneg : 0 ≤ D
  b_pos : 0 < b

/-- `H(δ, p) = p² / (2M) − P_m δ − b cos δ`. -/
def classicalSM_H (p : ClassicalSMParams) (x : State 2) : ℝ :=
  1 / (2 * p.M) * x 1 ^ 2 - p.Pm * x 0 - p.b * Real.cos (x 0)

/-- `∇H = (b sin δ − P_m, p / M)`. -/
def classicalSM_dH (p : ClassicalSMParams) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![p.b * Real.sin (x 0) - p.Pm, x 1 / p.M]

@[tmio M, powerlib_foundation] theorem classicalSM_hasGradientAt (p : ClassicalSMParams) (x : State 2) :
    HasGradientAt (classicalSM_H p) (classicalSM_dH p x) x := by
  have h1 := (((smCoord 1).hasFDerivAt (x := x)).pow 2).const_mul (1 / (2 * p.M))
  have h0 := ((smCoord 0).hasFDerivAt (x := x)).const_mul p.Pm
  have hc := ((Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x
    ((smCoord 0).hasFDerivAt (x := x))).const_mul p.b
  refine hasGradientAt_of_hasFDerivAt ((h1.sub h0).sub hc) (fun v => ?_)
  simp [classicalSM_dH, dotProduct, Fin.sum_univ_two]
  ring

/-- The classical machine (T-ph (1.12)) as a nonlinear pH model. -/
def classicalSM (p : ClassicalSMParams) : NonlinearModel 2 1 where
  J _ := !![0, 1; -1, 0]
  R _ := diagonal ![0, p.D]
  g _ := !![0; 1]
  H := classicalSM_H p
  dH := classicalSM_dH p
  skew _ := PH.transpose_symplectic_two
  dissipation_posSemidef _ := PosSemidef.diagonal (fun i => by
    fin_cases i <;> simp [p.D_nonneg])
  hasGradient := classicalSM_hasGradientAt p

/-- (1.12) reproduces the swing equation: `δ̇ = p / M`, `ṗ = P_m − b sin δ − D (p / M) + u`. -/
@[powerlib_foundation] theorem classicalSM_field (p : ClassicalSMParams) (x : State 2)
    (u : Fin 1 → ℝ) :
    WithLp.ofLp ((classicalSM p).field x u) =
      ![x 1 / p.M, p.Pm - p.b * Real.sin (x 0) - p.D * (x 1 / p.M) + u 0] := by
  ext i
  fin_cases i <;>
    simp [NonlinearModel.field, classicalSM, classicalSM_dH, Matrix.diagonal_vec2,
      Matrix.vecHead, Matrix.vecTail]
  ring

/-- The damping power is `D ω²` with `ω = p / M` (`R₂₂ = D`, no `M⁻²` factor). -/
@[powerlib_foundation] theorem classicalSM_dampingPower (p : ClassicalSMParams) (x : State 2) :
    (classicalSM p).dampingPower x = p.D * (x 1 / p.M) ^ 2 := by
  simp [NonlinearModel.dampingPower, classicalSM, classicalSM_dH, Matrix.diagonal_vec2,
    Matrix.vecHead, Matrix.vecTail]
  ring

/-- Energy balance of the classical machine: `Ḣ = u ω − D ω²`. -/
@[powerlib_foundation] theorem classicalSM_power_balance (p : ClassicalSMParams) (x : State 2)
    (u : Fin 1 → ℝ) :
    fderiv ℝ (classicalSM p).H x ((classicalSM p).field x u) =
      u 0 * (x 1 / p.M) - p.D * (x 1 / p.M) ^ 2 := by
  rw [NonlinearModel.power_balance, classicalSM_dampingPower]
  simp [NonlinearModel.supply, NonlinearModel.output, classicalSM, classicalSM_dH, mulVec,
    dotProduct, Fin.sum_univ_two]

/-- Correction: the classical-machine Hamiltonian is unbounded below whenever `P_m ≠ 0`,
so T-ph §1.1 structural assumption 3 fails for (1.12). -/
@[powerlib_foundation] theorem classicalSM_hamiltonian_not_bddBelow (p : ClassicalSMParams)
    (hPm : p.Pm ≠ 0) : ¬ BddBelow (Set.range (classicalSM p).H) := by
  rintro ⟨c, hc⟩
  set δ : ℝ := (p.b - c + 1) / p.Pm
  have hx := hc ⟨WithLp.toLp 2 ![δ, 0], rfl⟩
  have hcos := Real.neg_one_le_cos δ
  have hPmδ : p.Pm * δ = p.b - c + 1 := by
    simp only [δ]
    field_simp
  simp only [classicalSM, classicalSM_H] at hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx
  nlinarith [p.b_pos]

/-- Dissipation inequality without any lower bound on `H`, `H(x(t₁)) − H(x(t₀)) ≤ ∫ u ω`, on
every solution segment.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem classicalSM_integral_dissipation (p : ClassicalSMParams)
    {u : ℝ → (Fin 1 → ℝ)} {x : ℝ → State 2} {t₀ t₁ : ℝ}
    (hx : (classicalSM p).system.IsTrajectoryOn u x t₀ t₁) (hle : t₀ ≤ t₁)
    (hsupply : IntervalIntegrable (fun τ => (classicalSM p).supply (x τ) (u τ))
      MeasureTheory.volume t₀ t₁) :
    (classicalSM p).H (x t₁) - (classicalSM p).H (x t₀) ≤
      ∫ τ in t₀..t₁, (classicalSM p).supply (x τ) (u τ) :=
  (classicalSM p).integral_dissipation hx hle hsupply

/-- Equilibria of the unforced classical machine: `b sin δ = P_m` and `p = 0`. -/
@[powerlib_foundation] theorem classicalSM_isEquilibrium_iff (p : ClassicalSMParams) (x : State 2) :
    IsEquilibrium (classicalSM p).zeroInputField x ↔
      p.b * Real.sin (x 0) = p.Pm ∧ x 1 = 0 := by
  have hM := p.M_pos.ne'
  have hfield := classicalSM_field p x 0
  constructor
  · intro h
    have h' : WithLp.ofLp ((classicalSM p).field x 0) = 0 := by
      simpa [NonlinearModel.zeroInputField] using congrArg WithLp.ofLp h
    rw [hfield] at h'
    have h0 := congrFun h' 0
    have h1 := congrFun h' 1
    simp at h0 h1
    rcases h0 with h0 | h0
    · refine ⟨?_, h0⟩
      rw [h0] at h1
      simp at h1
      linarith
    · exact absurd h0 hM
  · rintro ⟨hs, h1⟩
    show (classicalSM p).field x 0 = 0
    apply WithLp.ofLp_injective 2
    rw [hfield]
    ext i
    fin_cases i <;> simp [h1, hs]

/-- The equilibrium point `(δ*, 0)`. -/
def classicalSM_equilibrium (δs : ℝ) : State 2 := WithLp.toLp 2 ![δs, 0]

/-- The potential `−P_m (δ − δ*) − b (cos δ − cos δ*)` is positive on `|δ| < π/2`,
`δ ≠ δ*`, when `b sin δ* = P_m` and `|δ*| < π/2`. -/
@[powerlib_foundation] theorem classicalSM_potential_pos (p : ClassicalSMParams) {δs δ : ℝ}
    (hδs : δs ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (heq : p.b * Real.sin δs = p.Pm)
    (hδ : δ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hne : δ ≠ δs) :
    0 < -p.Pm * (δ - δs) - p.b * (Real.cos δ - Real.cos δs) := by
  set f : ℝ → ℝ := fun y => -p.Pm * (y - δs) - p.b * (Real.cos y - Real.cos δs) with hf
  have hderiv : ∀ y, HasDerivAt f (p.b * Real.sin y - p.Pm) y := by
    intro y
    have h := (((hasDerivAt_id y).sub_const δs).const_mul (-p.Pm)).sub
      (((Real.hasDerivAt_cos y).sub_const (Real.cos δs)).const_mul p.b)
    exact h.congr_deriv (by ring)
  have hcont : Continuous f := by
    simp only [hf]
    fun_prop
  have hfδs : f δs = 0 := by simp [hf]
  have hb := p.b_pos
  change 0 < f δ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hanti : StrictAntiOn f (Icc (-(Real.pi / 2)) δs) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn
      intro y hy
      rw [interior_Icc] at hy
      rw [(hderiv y).deriv, ← heq]
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two hy.1.le hδs.2.le hy.2
      nlinarith
    have := hanti ⟨hδ.1.le, hlt.le⟩ ⟨hδs.1.le, le_rfl⟩ hlt
    linarith
  · have hmono : StrictMonoOn f (Icc δs (Real.pi / 2)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn
      intro y hy
      rw [interior_Icc] at hy
      rw [(hderiv y).deriv, ← heq]
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two hδs.1.le hy.2.le hy.1
      nlinarith
    have := hmono ⟨le_rfl, hδs.2.le⟩ ⟨hgt.le, hδ.2.le⟩ hgt
    linarith

/-- `(δ*, 0)` with `b sin δ* = P_m`, `|δ*| < π/2` is a strict local minimum of `H`. -/
@[powerlib_foundation] theorem classicalSM_isStrictLocalMin (p : ClassicalSMParams) {δs : ℝ}
    (hδs : δs ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (heq : p.b * Real.sin δs = p.Pm) :
    (classicalSM p).IsStrictLocalMin (classicalSM_equilibrium δs) := by
  have hopen : IsOpen {x : State 2 | x 0 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)} :=
    isOpen_Ioo.preimage (smCoord 0).continuous
  have hmem : classicalSM_equilibrium δs ∈
      {x : State 2 | x 0 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)} := by
    simpa [classicalSM_equilibrium] using hδs
  have hev := hopen.mem_nhds hmem
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards [hev] with x hx hne
  have hM := p.M_pos
  have hpot : 0 ≤ -p.Pm * (x 0 - δs) - p.b * (Real.cos (x 0) - Real.cos δs) := by
    by_cases h0 : x 0 = δs
    · simp [h0]
    · exact (classicalSM_potential_pos p hδs heq hx h0).le
  have hdiff : (classicalSM p).H x - (classicalSM p).H (classicalSM_equilibrium δs) =
      (-p.Pm * (x 0 - δs) - p.b * (Real.cos (x 0) - Real.cos δs)) + 1 / (2 * p.M) * x 1 ^ 2 := by
    simp [classicalSM, classicalSM_H, classicalSM_equilibrium]
    ring
  rw [← sub_pos, hdiff]
  by_cases h0 : x 0 = δs
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hne
      ext i
      fin_cases i <;> simp [classicalSM_equilibrium, h0, h1]
    have : 0 < 1 / (2 * p.M) * x 1 ^ 2 := by positivity
    linarith
  · have := classicalSM_potential_pos p hδs heq hx h0
    have : 0 ≤ 1 / (2 * p.M) * x 1 ^ 2 := by positivity
    linarith

@[powerlib_foundation] theorem classicalSM_contDiff_dH (p : ClassicalSMParams) :
    ContDiff ℝ 1 (classicalSM p).dH := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [classicalSM, classicalSM_dH] using
      ((Real.contDiff_sin.comp (smCoord 0).contDiff).const_smul p.b).sub
        (contDiff_const (c := p.Pm))
  · simpa [classicalSM, classicalSM_dH, div_eq_mul_inv] using
      (smCoord (n := 2) 1).contDiff.mul (contDiff_const (c := p.M⁻¹))

/-- The Hessian of `H` at `(δ, p)`: `diag(b cos δ, 1/M)`. -/
@[powerlib_foundation] theorem classicalSM_hasFDerivAt_dH (p : ClassicalSMParams) (x : State 2) :
    HasFDerivAt (classicalSM p).dH
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![p.b * Real.cos (x 0), 0; 0, 1 / p.M]) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
  fin_cases i
  · have h := (((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x
      ((smCoord 0).hasFDerivAt (x := x))).const_mul p.b).sub_const p.Pm
    convert h using 1
    · funext y
      simp [classicalSM, classicalSM_dH]
    · ext v
      simp [Matrix.ofLp_toEuclideanCLM, mulVec, dotProduct, Fin.sum_univ_two]
      ring
  · have h := ((smCoord 1).hasFDerivAt (x := x)).mul_const (1 / p.M)
    convert h using 1
    · funext y
      simp [classicalSM, classicalSM_dH, div_eq_mul_inv]
    · ext v
      simp [Matrix.ofLp_toEuclideanCLM, mulVec, dotProduct, Fin.sum_univ_two]

/-- Linearization of the unforced classical machine at `(δ*, 0)`:
`A = (J − R) ∇²H = !![0, 1/M; −b cos δ*, −D/M]`. -/
@[powerlib_foundation] theorem classicalSM_linearization (p : ClassicalSMParams) (δs : ℝ) :
    ((classicalSM p).J (classicalSM_equilibrium δs) -
      (classicalSM p).R (classicalSM_equilibrium δs)) *
        !![p.b * Real.cos δs, 0; 0, 1 / p.M] =
      !![0, 1 / p.M; -(p.b * Real.cos δs), -(p.D / p.M)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [classicalSM, Matrix.diagonal_vec2]
  all_goals ring

/-! ### The swing reading -/

/-- The classical machine as the canonical swing model
`M ω̇ = P_m − (k₁ + k₂ sin(δ − k₃)) − D ω` (`theorem/Synchronous/Swing.lean`) with `k₁ = k₃ = 0`,
`k₂ = b`. -/
def ClassicalSMParams.toSwing (p : ClassicalSMParams) : SwingParams := ⟨p.M, p.D, p.Pm, 0, p.b, 0⟩

/-- Under zero input the pH field is the swing field of `toSwing` in the momentum coordinates
`(δ, p) = (δ, M ω)`: `f_pH = T ∘ f_swing ∘ T⁻¹` with `T = diag(1, M)` (`Dynamics.scaleCoord`).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem classicalSM_zeroInputField_eq_transport (p : ClassicalSMParams) :
    (classicalSM p).zeroInputField =
      Dynamics.transportField (Dynamics.scaleCoord p.M_pos.ne') 0 p.toSwing.field := by
  funext x
  have hM := p.M_pos.ne'
  apply WithLp.ofLp_injective 2
  rw [show WithLp.ofLp ((classicalSM p).zeroInputField x) =
    ![x 1 / p.M, p.Pm - p.b * Real.sin (x 0) - p.D * (x 1 / p.M) + 0] from
    classicalSM_field p x 0]
  ext i
  fin_cases i
  · simp [Dynamics.transportField, ClassicalSMParams.toSwing, SwingParams.field, PhasePlane.mk]
  · simp [Dynamics.transportField, ClassicalSMParams.toSwing, SwingParams.field, PhasePlane.mk,
      SwingParams.accel, SwingParams.Pe]
    field_simp

/-! ### The classical-machine family -/

namespace ClassicalSM

/-- The classical machine read about a selected rotor angle `δ*`, operating point `(δ*, 0)`. -/
structure Model where
  /-- The machine parameters. -/
  p : ClassicalSMParams
  /-- The selected rotor angle `δ*`. -/
  δs : ℝ

/-- The selected operating point `(δ*, 0)`. -/
def Model.point (m : Model) : State 2 := classicalSM_equilibrium m.δs

/-- The pH system centred at the operating point. -/
def Model.toPH (m : Model) : NonlinearModel 2 1 := (classicalSM m.p).shift m.point

/-- The swing reading: the canonical swing model `toSwing` about the same angle `δ*`. -/
def Model.toSwing (m : Model) : Swing.Model := ⟨m.p.toSwing, m.δs⟩

/-- Requirements on the classical machine, all static. -/
inductive Requirement
  /-- `(δ*, 0)` is an equilibrium: `b sin δ* = P_m`. -/
  | locked
  /-- The stable branch `cos δ* > 0`, invariant under whole turns `δ* ↦ δ* + 2π k`. -/
  | stableBranch
  /-- Strict damping on the stable side: `D > 0`, `cos δ* > 0`. -/
  | damped
  /-- The unstable branch `cos δ* < 0`. -/
  | unstableBranch
  /-- No mechanical power: `P_m = 0`. -/
  | noPower

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .locked => m.p.b * Real.sin m.δs = m.p.Pm
  | .stableBranch => 0 < Real.cos m.δs
  | .damped => 0 < m.p.D ∧ 0 < Real.cos m.δs
  | .unstableBranch => Real.cos m.δs < 0
  | .noPower => m.p.Pm = 0

/-- The translation of the sentences. The global sentences, decay rates, sampled contraction and
conservation are translated into the whole language, which no model meets (unavailable
translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable => {.locked, .stableBranch}
  | .flow .locallyAsymptoticallyStable | .flow .locallyExponentiallyStable => {.locked, .damped}
  | .flow .unstable => {.locked, .unstableBranch}
  | .flow _ => Set.univ
  | .passive => {.noPower}
  | .envelope _ => ∅

/-- The classical-machine family: every model read as its pH system centred at `(δ*, 0)`. -/
def family : Family Model Requirement 2 1 :=
  ⟨fun m => m.toPH.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isNonlinearPH :
    family.IsNonlinearPH fun m => (classicalSM m.p).shift m.point := fun _ => rfl

private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (classicalSM m.p).zeroInputField m.point :=
  family_isNonlinearPH.mem_den_flow_shift

/-- No model is both damped on the stable side and on the unstable branch: the whole requirement
language is inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  have h1 : Meets m .damped := h .damped
  have h2 : Meets m .unstableBranch := h .unstableBranch
  exact lt_asymm h1.2 h2

/-! #### Equivalence with the swing family -/

private theorem toSwing_Pe (m : Model) : m.toSwing.p.Pe m.toSwing.δ = m.p.b * Real.sin m.δs := by
  simp [Model.toSwing, ClassicalSMParams.toSwing, SwingParams.Pe]

private theorem toSwing_syncCoeff (m : Model) :
    m.toSwing.p.syncCoeff m.toSwing.δ = m.p.b * Real.cos m.δs := by
  simp [Model.toSwing, ClassicalSMParams.toSwing, SwingParams.syncCoeff]

/-- **Flow equivalence with the swing family.** A classical-machine model satisfies a flow
sentence exactly when its swing reading does: under zero input the pH field is the swing field in
the coordinates `(δ, M ω)` (`classicalSM_zeroInputField_eq_transport`), the operating point
`(δ*, 0)` is fixed by that change, and every flow sentence is invariant under it
(`Spectral.mem_den_flow_iff_of_transport`, `Dynamics.holds_transport_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_flow_iff_swing (m : Model) (P : Flow.Property) :
    connection% (m ∈ family.den (.flow P) ↔ m.toSwing ∈ Swing.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hdenG : ∀ (y : Swing.Model) (P : Flow.Property),
      y ∈ Swing.family.den (.flow P) ↔ P.holds y.p.field y.point := fun _ _ =>
    Spectral.mem_den_flow_iff_shift (f := fun y : Swing.Model => y.p.field)
      (pt := Swing.Model.point) Swing.family_isAutonomous
  have hpt : m.point =
      Dynamics.affineCoord (Dynamics.scaleCoord m.p.M_pos.ne') 0 m.toSwing.point := by
    ext i
    fin_cases i <;> simp [Model.point, classicalSM_equilibrium, Swing.Model.point,
      Model.toSwing, Dynamics.affineCoord, PhasePlane.mk]
  exact Spectral.mem_den_flow_iff_of_transport (g := Model.toSwing) (fun _ _ => mem_den_flow_iff)
    hdenG (Dynamics.scaleCoord m.p.M_pos.ne') 0 (classicalSM_zeroInputField_eq_transport m.p) hpt P

/-- Every flow sentence of the classical-machine family denotes the preimage of its swing
denotation under `Model.toSwing`: on the flow sentences the semantics connection of the family is
that of `Swing.family.comap Model.toSwing`. -/
@[tmio TM, powerlib_domain] theorem den_flow_eq_preimage :
    connection% (∀ P : Flow.Property,
      family.den (.flow P) = Model.toSwing ⁻¹' Swing.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  intro P
  ext m
  have h := mem_den_flow_iff_swing m P
  unfold powerlib.TMIO.Statement at h
  exact h

/-- The translation of every flow sentence carves out the preimage of the space of its swing
translation. On the image of `toSwing` positive inertia and nonnegative damping always hold;
`locked` is `balanced`, `stableBranch` is `synchronizing` (`b > 0`), `damped` is `damped` with
`synchronizing`, `unstableBranch` is `destabilizing` (`D ≥ 0`); the global sentences, decay rates,
sampled contraction and conservation have the empty space on both sides. -/
@[tmio TM, powerlib_foundation] theorem realize_translate_flow_eq_preimage :
    connection% (∀ P : Flow.Property, TMIO.realize family.meets (family.translate (.flow P)) =
      Model.toSwing ⁻¹' TMIO.realize Swing.family.meets (Swing.family.translate (.flow P))) := by
  unfold powerlib.TMIO.Statement
  intro P
  have hu := realize_univ
  have hsu := Swing.realize_univ
  unfold powerlib.TMIO.Statement at hu hsu
  ext m
  have hM := m.p.M_pos
  have hD := m.p.D_nonneg
  have hb := m.p.b_pos
  cases P
  case lyapunovStable =>
    simp only [Set.mem_preimage, TMIO.mem_realize, family, translate, Swing.family,
      Swing.translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      Meets, Swing.Meets, toSwing_Pe, toSwing_syncCoeff]
    constructor
    · rintro ⟨hl, hc⟩
      exact ⟨hl, hM, hD, mul_pos hb hc⟩
    · rintro ⟨hl, -, -, hK⟩
      exact ⟨hl, pos_of_mul_pos_right hK hb.le⟩
  case locallyAsymptoticallyStable | locallyExponentiallyStable =>
    simp only [Set.mem_preimage, TMIO.mem_realize, family, translate, Swing.family,
      Swing.translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      Meets, Swing.Meets, toSwing_Pe, toSwing_syncCoeff]
    constructor
    · rintro ⟨hl, hd, hc⟩
      exact ⟨hl, hM, hd, mul_pos hb hc⟩
    · rintro ⟨hl, -, hd, hK⟩
      exact ⟨hl, hd, pos_of_mul_pos_right hK hb.le⟩
  case unstable =>
    simp only [Set.mem_preimage, TMIO.mem_realize, family, translate, Swing.family,
      Swing.translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      Meets, Swing.Meets, toSwing_Pe, toSwing_syncCoeff]
    constructor
    · rintro ⟨hl, hc⟩
      exact ⟨hl, hM, Or.inl (mul_neg_of_pos_of_neg hb hc)⟩
    · rintro ⟨hl, -, hK | hDn⟩
      · exact ⟨hl, neg_of_mul_neg_right hK hb.le⟩
      · exact absurd hD (not_le.mpr hDn)
  all_goals
    change m ∈ TMIO.realize Meets Set.univ ↔ m.toSwing ∈ TMIO.realize Swing.Meets Set.univ
    rw [hu, hsu]
    simp

/-- On the flow sentences the classical-machine family is the swing family read through
`Model.toSwing` for both connections: a flow translation is exact exactly when the swing
translation is exact on the image of `toSwing`. -/
@[tmio TM, powerlib_domain] theorem exact_flow_iff :
    connection% (∀ P : Flow.Property,
      family.Exact (.flow P) ↔ (Swing.family.comap Model.toSwing).Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  intro P
  have hr := realize_translate_flow_eq_preimage
  have hd := den_flow_eq_preimage
  unfold powerlib.TMIO.Statement at hr hd
  unfold Family.Exact
  rw [Family.realize_comap, Family.den_comap, hr P, hd P]
  rfl

/-- Every swing reading has positive inertia and a curved power-angle curve (`k₂ = b > 0`): it
lies in the swing family's context `{inertia, curved}`. -/
private theorem toSwing_mem_context (m : Model) :
    connection% (m.toSwing ∈ TMIO.realize Swing.family.meets {.inertia, .curved}) := show m.toSwing ∈ TMIO.realize Swing.family.meets {.inertia, .curved} from
  (TMIO.mem_realize _ _ _).mpr fun q hq => by
    rcases hq with rfl | rfl
    · exact m.p.M_pos
    · exact m.p.b_pos.ne'

/-- A swing translation exact within a context of positive inertia and a curved power-angle curve
is exact for the classical machine (`Spectral.exact_of_hub`): every swing reading lies in that
context, and on every flow sentence the reading (`mem_den_flow_iff_swing`) and the requirement
correspondence (`realize_translate_flow_eq_preimage`) hold. -/
private theorem exact_of_exactUnder {Δ : Set Swing.Requirement} {P : Flow.Property}
    (hΔ : Δ ⊆ {.inertia, .curved}) (h : Swing.family.ExactUnder Δ (.flow P)) :
    connection% (family.Exact (.flow P)) := by
  change family.Exact (.flow P)
  have hr := realize_translate_flow_eq_preimage
  unfold powerlib.TMIO.Statement at hr
  exact Spectral.exact_of_hub Model.toSwing
    (fun m => (TMIO.mem_realize _ _ _).mpr fun q hq =>
      (TMIO.mem_realize _ _ _).mp (toSwing_mem_context m) q (hΔ hq))
    (fun m => mem_den_flow_iff_swing m P) (fun m => Set.ext_iff.mp (hr P) m) h

/-! #### Members of the flow denotations -/

/-- Lyapunov stability of the stable equilibrium `(δ*, 0)`, `b sin δ* = P_m`, `cos δ* > 0`, of
the unforced classical machine, for every `D ≥ 0`: the swing reading is balanced with a positive
synchronizing coefficient `b cos δ*` (`Swing.mem_den_lyapunovStable`, whose energy
`½ M ω² + U(δ)` is `H − H(x*)` in swing coordinates). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable (m : Model)
    (heq : m.p.b * Real.sin m.δs = m.p.Pm) (hcos : 0 < Real.cos m.δs) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  have hsw := mem_den_flow_iff_swing m .lyapunovStable
  have hs := Swing.mem_den_lyapunovStable m.toSwing m.p.M_pos m.p.D_nonneg
    ((toSwing_Pe m).trans heq) (by rw [toSwing_syncCoeff]; exact mul_pos m.p.b_pos hcos)
  unfold powerlib.TMIO.Statement at hsw hs ⊢
  exact hsw.mpr hs

/-- `D > 0`, `b sin δ* = P_m`, `cos δ* > 0`: the equilibrium `(δ*, 0)` of the full nonlinear
unforced classical machine is locally exponentially stable
(`Swing.mem_den_locallyExponentiallyStable` on the swing reading). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model) (hD : 0 < m.p.D)
    (heq : m.p.b * Real.sin m.δs = m.p.Pm) (hcos : 0 < Real.cos m.δs) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have hsw := mem_den_flow_iff_swing m .locallyExponentiallyStable
  have hs := Swing.mem_den_locallyExponentiallyStable m.toSwing m.p.M_pos hD
    ((toSwing_Pe m).trans heq) (by rw [toSwing_syncCoeff]; exact mul_pos m.p.b_pos hcos)
  unfold powerlib.TMIO.Statement at hsw hs ⊢
  exact hsw.mpr hs

/-- `b sin δ* = P_m`, `cos δ* < 0` (the unstable branch): the equilibrium `(δ*, 0)` of the full
nonlinear unforced classical machine is unstable, for every `D ≥ 0` (`Swing.mem_den_unstable` on
the swing reading, a saddle). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (heq : m.p.b * Real.sin m.δs = m.p.Pm)
    (hcos : Real.cos m.δs < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hsw := mem_den_flow_iff_swing m .unstable
  have hs := Swing.mem_den_unstable m.toSwing m.p.M_pos ((toSwing_Pe m).trans heq)
    (by rw [toSwing_syncCoeff]; exact mul_neg_of_pos_of_neg m.p.b_pos hcos)
  unfold powerlib.TMIO.Statement at hsw hs ⊢
  exact hsw.mpr hs

/-- With no mechanical power the Hamiltonian `p²/(2M) − b cos δ ≥ −b` is bounded below, so the
machine is passive. -/
@[tmio TM, powerlib_domain] theorem mem_den_passive_of_Pm_zero (m : Model) (hPm : m.p.Pm = 0) :
    connection% (m ∈ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  refine family_isNonlinearPH.mem_den_passive
    ((classicalSM m.p).bddBelow_range_shift_H.mpr ⟨-m.p.b, ?_⟩)
  rintro _ ⟨x, rfl⟩
  have hM := m.p.M_pos
  have hb := m.p.b_pos
  have hc := Real.cos_le_one (x 0)
  have hx : 0 ≤ 1 / (2 * m.p.M) * x 1 ^ 2 := by positivity
  simp only [classicalSM, classicalSM_H, hPm, zero_mul, sub_zero]
  nlinarith

/-- Every translation of the classical-machine family is sound: the flow translations are the
swing translations read through `toSwing` (`Spectral.sound_of_hub` from
`Swing.chain_le_semantics`, with `realize_translate_flow_eq_preimage` and
`mem_den_flow_iff_swing`); passivity from `P_m = 0`. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  have hs := Swing.chain_le_semantics
  have hr := realize_translate_flow_eq_preimage
  unfold powerlib.TMIO.Statement at hs hr ⊢
  refine Family.chain_le_semantics_iff.mpr fun s => ?_
  rcases s with P | _ | E
  · exact Spectral.sound_of_hub Model.toSwing (fun m hm => (Set.ext_iff.mp (hr P) m).mp hm)
      (fun m _ => (mem_den_flow_iff_swing m P).mpr) (Family.chain_le_semantics_iff.mp hs (.flow P))
  · intro m hm
    rw [(connection_proof% TMIO.mem_realize)] at hm
    exact mem_den_passive_of_Pm_zero m (hm .noPower rfl)
  · exact fun m _ => (Family.mem_den _).mpr trivial

/-! #### Exactness of the local translations -/

/-- The local exponential translation is exact: the classical machine is locally exponentially
stable at `(δ*, 0)` exactly when `b sin δ* = P_m`, `D > 0` and `cos δ* > 0`. Within positive
inertia the swing translation is exact (`Swing.exactUnder_locallyExponentiallyStable`, converse
linearization: the Jacobian `[[0, 1], [−K/M, −D/M]]`, conjugate by `diag(1, M)` to
`(J − R) ∇²H = [[0, 1/M], [−b cos δ*, −D/M]]`, `classicalSM_linearization`), and every swing
reading has positive inertia (`Spectral.exact_of_hub`). -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_exactUnder (by simp) Swing.exactUnder_locallyExponentiallyStable

/-! #### The local asymptotic and Lyapunov translations -/

/-- At a fold of the machine (`b sin δ* = P_m`, `cos δ* = 0`) the Hamiltonian relative to
`(δ*, 0)` is `p² / (2M) − P_m (s − sin s)` at `(δ* + s, p)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem classicalSM_H_fold (p : ClassicalSMParams) {δs : ℝ}
    (heq : p.b * Real.sin δs = p.Pm) (hcos : Real.cos δs = 0) (s w : ℝ) :
    classicalSM_H p (WithLp.toLp 2 ![δs + s, w]) - classicalSM_H p (classicalSM_equilibrium δs) =
      1 / (2 * p.M) * w ^ 2 - p.Pm * (s - Real.sin s) := by
  simp only [classicalSM_H, classicalSM_equilibrium]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [Real.cos_add, hcos, ← heq]
  ring

/-- At a fold the accelerating power is `P_m (1 − cos s)` at `δ* + s`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem classicalSM_accel_fold (p : ClassicalSMParams) {δs : ℝ}
    (heq : p.b * Real.sin δs = p.Pm) (hcos : Real.cos δs = 0) (s : ℝ) :
    p.Pm - p.b * Real.sin (δs + s) = p.Pm * (1 - Real.cos s) := by
  rw [Real.sin_add, hcos, ← heq]
  ring

/-- The local asymptotic translation is exact: the classical machine is locally asymptotically
stable at `(δ*, 0)` exactly when `b sin δ* = P_m`, `D > 0` and `cos δ* > 0`
(`Swing.exactUnder_locallyAsymptoticallyStable` on the swing readings, all of positive inertia,
`Spectral.exact_of_hub`).
The linearization does not decide the degenerate cases, the model's structure does: an undamped
machine conserves `H`, and at a fold (`cos δ* = 0`) the Hamiltonian `p²/(2M) − P_m (s − sin s)`
(`classicalSM_H_fold`; `Swing.potential_fold` in swing coordinates) is below its value at
`(δ*, 0)` on one side, where the dissipated energy keeps every solution away
(`Dynamics.not_localAsymptoticStable_of_lie_nonpos`). -/
@[tmio TM, powerlib_domain] theorem exact_locallyAsymptoticallyStable :
    connection% (family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_exactUnder (by simp) Swing.exactUnder_locallyAsymptoticallyStable

/-- The Lyapunov translation is exact: the classical machine is Lyapunov stable at `(δ*, 0)`
exactly when `b sin δ* = P_m` and `cos δ* > 0`, for every `D ≥ 0`. Within positive inertia and a
curved power-angle curve the swing translation is exact (`Swing.exactUnder_lyapunovStable`: the
unstable branch is a saddle, and a fold `cos δ* = 0` is unstable for every `D ≥ 0`, the
accelerating power being `P_m (1 − cos(δ − δ*))`, `classicalSM_accel_fold`; `Swing.Pe_fold` in
swing coordinates), and every swing reading lies in that context (`M > 0`, `k₂ = b > 0`;
`Spectral.exact_of_hub`). The stable-branch requirement `cos δ* > 0` is invariant under whole
turns; `|δ*| < π/2` would not be (at `δ* = 2π`, `M = b = 1`, `D = P_m = 0` the machine is Lyapunov
stable without meeting it, so that translation would be sound but not exact). -/
@[tmio TM, powerlib_domain] theorem exact_lyapunovStable :
    connection% (family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_exactUnder subset_rfl Swing.exactUnder_lyapunovStable

/-- Lyapunov stability holds exactly at the equilibria with `cos δ* > 0` (every damping
`D ≥ 0`): the stable branch up to whole turns. This is the exact Lyapunov translation
(`exact_lyapunovStable`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff (m : Model) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.p.b * Real.sin m.δs = m.p.Pm ∧ 0 < Real.cos m.δs}) := by
  have h := exact_lyapunovStable
  unfold powerlib.TMIO.Statement at h ⊢
  unfold Family.Exact at h
  rw [← h, (connection_proof% TMIO.mem_realize)]
  simp only [family, translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, Set.mem_ofPred_eq]
  rfl

/-! #### Exactness of the passivity translation -/

/-- The spinning motion in coordinates centred at the operating point: the rotor turns at the
constant speed `ω₀`, `(δ − δ*, p) = (ω₀ t, M ω₀)`. -/
private def spin (m : Model) (ω₀ t : ℝ) : State 2 := WithLp.toLp 2 ![ω₀ * t, m.p.M * ω₀]

/-- The port power that holds the speed constant: `u = −P_m + b sin δ + D ω₀`. -/
private def spinInput (m : Model) (ω₀ t : ℝ) : Fin 1 → ℝ :=
  fun _ => -m.p.Pm + m.p.b * Real.sin (ω₀ * t + m.δs) + m.p.D * ω₀

private theorem spin_hasDerivAt (m : Model) (ω₀ t : ℝ) :
    HasDerivAt (spin m ω₀) (WithLp.toLp 2 ![ω₀, 0]) t := by
  have h := ((hasDerivAt_id t).smul_const (WithLp.toLp 2 ![ω₀, (0 : ℝ)] : State 2)).const_add
    (WithLp.toLp 2 ![0, m.p.M * ω₀] : State 2)
  convert h using 1
  · funext s
    ext i
    fin_cases i <;> simp [spin, mul_comm]
  · simp

private theorem spin_field (m : Model) (ω₀ t : ℝ) :
    m.toPH.system.field (spin m ω₀ t) (spinInput m ω₀ t) = WithLp.toLp 2 ![ω₀, 0] := by
  apply WithLp.ofLp_injective 2
  change WithLp.ofLp ((classicalSM m.p).field (spin m ω₀ t + m.point) (spinInput m ω₀ t)) = _
  rw [classicalSM_field]
  have hM := m.p.M_pos.ne'
  ext i
  fin_cases i
  · simp [spin, Model.point, classicalSM_equilibrium]
    field_simp
  · simp [spin, spinInput, Model.point, classicalSM_equilibrium]
    field_simp
    ring_nf

private theorem spin_supply (m : Model) (ω₀ t : ℝ) :
    m.toPH.system.supply (spin m ω₀ t) (spinInput m ω₀ t) =
      ω₀ * (-m.p.Pm + m.p.b * Real.sin (ω₀ * t + m.δs) + m.p.D * ω₀) := by
  change (classicalSM m.p).supply (spin m ω₀ t + m.point) (spinInput m ω₀ t) = _
  have hM := m.p.M_pos.ne'
  simp [NonlinearModel.supply, NonlinearModel.output, classicalSM, classicalSM_dH, mulVec,
    dotProduct, spin, spinInput, Model.point, classicalSM_equilibrium]
  field_simp

/-- With mechanical power `P_m ≠ 0` the classical machine is not passive. The port holds a slow
spin `ω₀ = P_m / (2 (D + 1))` in the direction of `P_m` at constant speed; per unit time it draws
`κ = ω₀ (P_m − D ω₀) > 0` on average (the work of `P_m` minus the damping loss), so along one
solution segment from a fixed state the supplied energy falls below minus every storage value. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_passive (m : Model) (hPm : m.p.Pm ≠ 0) :
    connection% (m ∉ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  rintro ⟨V, hV0, hV⟩
  have hD := m.p.D_nonneg
  have hb := m.p.b_pos
  set ω₀ : ℝ := m.p.Pm / (2 * (m.p.D + 1)) with hω₀
  set κ : ℝ := ω₀ * (m.p.D * ω₀ - m.p.Pm) with hκ_def
  have hκ : κ < 0 := by
    have e : κ = -(m.p.Pm ^ 2 * (m.p.D + 2)) / (4 * (m.p.D + 1) ^ 2) := by
      rw [hκ_def, hω₀]
      field_simp
      ring
    rw [e, neg_div, neg_lt_zero]
    have : 0 < m.p.Pm ^ 2 := by positivity
    positivity
  set V₀ := V (spin m ω₀ 0)
  set T : ℝ := (V₀ + 2 * m.p.b + 1) / (-κ) with hT_def
  have hT : 0 ≤ T := by
    have := hV0 (spin m ω₀ 0)
    have : 0 < -κ := neg_pos.mpr hκ
    positivity
  have hκT : κ * T = -(V₀ + 2 * m.p.b + 1) := by
    have hκ0 : κ ≠ 0 := hκ.ne
    rw [hT_def]
    field_simp
  have htraj : m.toPH.system.IsTrajectoryOn (spinInput m ω₀) (spin m ω₀) 0 T := by
    intro t _
    show HasDerivWithinAt (spin m ω₀) (m.toPH.system.field (spin m ω₀ t) (spinInput m ω₀ t))
      (Set.Icc 0 T) t
    rw [spin_field]
    exact (spin_hasDerivAt m ω₀ t).hasDerivWithinAt
  have hsupply : (fun t => m.toPH.system.supply (spin m ω₀ t) (spinInput m ω₀ t)) =
      fun t => ω₀ * (-m.p.Pm + m.p.b * Real.sin (ω₀ * t + m.δs) + m.p.D * ω₀) :=
    funext (spin_supply m ω₀)
  have hcont : Continuous fun t : ℝ =>
      ω₀ * (-m.p.Pm + m.p.b * Real.sin (ω₀ * t + m.δs) + m.p.D * ω₀) := by fun_prop
  have hint : IntervalIntegrable
      (fun t => m.toPH.system.supply (spin m ω₀ t) (spinInput m ω₀ t)) MeasureTheory.volume
        0 T := by
    rw [hsupply]
    exact hcont.intervalIntegrable 0 T
  have h := hV _ _ 0 T hT htraj hint
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt
      (fun t => κ * t - m.p.b * Real.cos (ω₀ * t + m.δs))
      (ω₀ * (-m.p.Pm + m.p.b * Real.sin (ω₀ * t + m.δs) + m.p.D * ω₀)) t := by
    intro t _
    have h := ((hasDerivAt_id t).const_mul κ).sub
      ((((hasDerivAt_id t).const_mul ω₀).add_const m.δs).cos.const_mul m.p.b)
    refine h.congr_deriv ?_
    simp only [id, mul_one, hκ_def]
    ring
  rw [hsupply, intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable 0 T)]
    at h
  have hc1 := Real.neg_one_le_cos (ω₀ * T + m.δs)
  have hc2 := Real.cos_le_one (ω₀ * 0 + m.δs)
  have hVT := hV0 (spin m ω₀ T)
  have e1 : -(m.p.b * Real.cos (ω₀ * T + m.δs)) ≤ m.p.b := by nlinarith
  have e2 : m.p.b * Real.cos (ω₀ * 0 + m.δs) ≤ m.p.b := by nlinarith
  linarith

/-- The passivity translation is exact: the classical machine is passive exactly when it has no
mechanical power, `P_m = 0`. -/
@[tmio TM, powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [(connection_proof% TMIO.mem_realize)]
  change (∀ q ∈ ({.noPower} : Set Requirement), Meets m q) ↔ _
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact mem_den_passive_of_Pm_zero m h
  · intro h
    by_contra hPm
    exact not_mem_den_passive m hPm h

/-! #### Instability away from equilibrium -/

/-- A model whose selected point is not an equilibrium: `M = b = 1`, `D = 0`, `P_m = 2`,
`δ* = 0`. -/
def offEquilibrium : Model := ⟨⟨1, 0, 1, 2, one_pos, le_rfl, one_pos⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. Its swing
reading is unbalanced (`b sin 0 = 0 ≠ 2 = P_m`, `Swing.mem_den_unstable_of_not_balanced`). -/
@[tmio TM, powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  have hsw := mem_den_flow_iff_swing offEquilibrium .unstable
  have hs := Swing.mem_den_unstable_of_not_balanced offEquilibrium.toSwing
    offEquilibrium.p.M_pos.ne' (by rw [toSwing_Pe]; norm_num [offEquilibrium, Model.toSwing,
      ClassicalSMParams.toSwing])
  unfold powerlib.TMIO.Statement at hsw hs ⊢
  exact hsw.mpr hs

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for an equilibrium. -/
@[tmio TM, powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .locked)
    (by simp [family, translate]) (by simp [family, Meets, offEquilibrium])

/-! #### Boundary of the equivalence: passivity -/

/-- The equivalence with the swing family does not extend to passivity: the classical machine has
a mechanical-power port and is passive only for `P_m = 0` (`exact_passive`), while the swing family
has no port and every model is passive. The unbalanced machine `offEquilibrium` (`P_m = 2`) is
not passive although its swing reading is. -/
@[tmio TM, powerlib_domain] theorem not_den_eq_preimage :
    connection% (¬ ∀ s, family.den s = Model.toSwing ⁻¹' Swing.family.den s) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hn := not_mem_den_passive offEquilibrium (by norm_num [offEquilibrium])
  unfold powerlib.TMIO.Statement at hn
  apply hn
  rw [h .passive, Set.mem_preimage, Swing.family_isAutonomous.den_passive]
  trivial

end ClassicalSM

/-! ## Seven-state dq machine -/

/-- Parameters of the seven-state dq machine. `Γ = L⁻¹` is the inverse inductance matrix in
the IN-positive current convention, state order `(Ψ_d, Ψ_q, Ψ_f, Ψ_kd, Ψ_kq)`. -/
structure SyncMachine7Params where
  Γ : Matrix (Fin 5) (Fin 5) ℝ
  M : ℝ
  rs : ℝ
  rf : ℝ
  rkd : ℝ
  rkq : ℝ
  D : ℝ
  Γ_posDef : Γ.PosDef
  M_pos : 0 < M
  rs_nonneg : 0 ≤ rs
  rf_nonneg : 0 ≤ rf
  rkd_nonneg : 0 ≤ rkd
  rkq_nonneg : 0 ≤ rkq
  D_nonneg : 0 ≤ D

/-- The structured inductance matrix of T-sync-machine §1.13 (IN-positive currents),
order `(d, q, f, kd, kq)`. -/
def syncMachine7_inductance (Ld Lq Lad Laq Lff Lfkd Lkdkd Lkqkq : ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  !![Ld, 0, Lad, Lad, 0;
     0, Lq, 0, 0, Laq;
     Lad, 0, Lff, Lfkd, 0;
     Lad, 0, Lfkd, Lkdkd, 0;
     0, Laq, 0, 0, Lkqkq]

/-- The structured inductance matrix is symmetric (reciprocal mutual inductances). -/
@[powerlib_foundation] theorem syncMachine7_inductance_symm
    (Ld Lq Lad Laq Lff Lfkd Lkdkd Lkqkq : ℝ) :
    (syncMachine7_inductance Ld Lq Lad Laq Lff Lfkd Lkdkd Lkqkq)ᵀ =
      syncMachine7_inductance Ld Lq Lad Laq Lff Lfkd Lkdkd Lkqkq := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A positive definite inductance matrix `L` gives the admissible parameter `Γ = L⁻¹`. -/
@[powerlib_foundation] theorem syncMachine7_inv_posDef {L : Matrix (Fin 5) (Fin 5) ℝ}
    (hL : L.PosDef) : L⁻¹.PosDef :=
  hL.inv

/-- With `Γ = L⁻¹`, the currents `i = Γ Ψ` satisfy the flux law `Ψ = L i`. -/
@[powerlib_foundation] theorem syncMachine7_flux_eq {L : Matrix (Fin 5) (Fin 5) ℝ} (hL : L.PosDef)
    (Ψ : Fin 5 → ℝ) : L *ᵥ (L⁻¹ *ᵥ Ψ) = Ψ := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL.det_pos.ne'), one_mulVec]

/-- The storage matrix `blkdiag(Γ, 1/M, 0)` with `H = ½ xᵀ Q x`. -/
def syncMachine7_Q (p : SyncMachine7Params) : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.of fun i j =>
    if h : i.val < 5 ∧ j.val < 5 then p.Γ ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else if i = 5 ∧ j = 5 then 1 / p.M else 0

@[powerlib_foundation] theorem syncMachine7_Q_symm (p : SyncMachine7Params) :
    (syncMachine7_Q p)ᵀ = syncMachine7_Q p := by
  have hs : ∀ a b : Fin 5, p.Γ b a = p.Γ a b := fun a b => by
    simpa using congrFun (congrFun p.Γ_posDef.isHermitian.eq a) b
  ext i j
  fin_cases i <;> fin_cases j <;> simp [syncMachine7_Q, hs]

/-- Flux linkages `(Ψ_d, Ψ_q, Ψ_f, Ψ_kd, Ψ_kq)` of a state. -/
def syncMachine7_flux (x : State 7) : Fin 5 → ℝ := ![x 0, x 1, x 2, x 3, x 4]

/-- Winding currents `(i_d, i_q, i_f, i_kd, i_kq) = Γ Ψ` (IN-positive stator currents). -/
def syncMachine7_current (p : SyncMachine7Params) (x : State 7) : Fin 5 → ℝ :=
  p.Γ *ᵥ syncMachine7_flux x

/-- Rotor speed `ω_r = p / M`. -/
def syncMachine7_speed (p : SyncMachine7Params) (x : State 7) : ℝ := x 5 / p.M

/-- `Q x = (i, ω_r, 0)`. -/
@[powerlib_foundation] theorem syncMachine7_Q_mulVec (p : SyncMachine7Params) (x : State 7) :
    syncMachine7_Q p *ᵥ WithLp.ofLp x =
      ![syncMachine7_current p x 0, syncMachine7_current p x 1, syncMachine7_current p x 2,
        syncMachine7_current p x 3, syncMachine7_current p x 4, syncMachine7_speed p x, 0] := by
  ext i
  fin_cases i <;>
    simp [syncMachine7_Q, syncMachine7_current, syncMachine7_flux, syncMachine7_speed, mulVec,
      dotProduct, Fin.sum_univ_succ]
  ring

/-- Interconnection matrix `J(x)` of §1.13 (state dependent through `Ψ_d, Ψ_q`). -/
def syncMachine7_J (x : State 7) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![0, 0, 0, 0, 0, x 1, 0;
     0, 0, 0, 0, 0, -x 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     -x 1, x 0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 0, 1, 0]

/-- Dissipation `R = diag(r_s, r_s, r_f, r_kd, r_kq, D, 0)`. -/
def syncMachine7_R (p : SyncMachine7Params) : Matrix (Fin 7) (Fin 7) ℝ :=
  diagonal ![p.rs, p.rs, p.rf, p.rkd, p.rkq, p.D, 0]

/-- Port matrix: inputs `(v_d, v_q, v_f, T_m^ext)`. -/
def syncMachine7_g : Matrix (Fin 7) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 0, 0]

/-- The seven-state dq synchronous machine of T-sync-machine §1.13 as a nonlinear pH model. -/
def syncMachine7 (p : SyncMachine7Params) : NonlinearModel 7 4 where
  J := syncMachine7_J
  R _ := syncMachine7_R p
  g _ := syncMachine7_g
  H := quadraticEnergy (syncMachine7_Q p)
  dH x := WithLp.toLp 2 (syncMachine7_Q p *ᵥ WithLp.ofLp x)
  skew x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [syncMachine7_J]
  dissipation_posSemidef _ := PosSemidef.diagonal (fun i => by
    fin_cases i <;> simp [p.rs_nonneg, p.rf_nonneg, p.rkd_nonneg, p.rkq_nonneg, p.D_nonneg])
  hasGradient := hasGradientAt_quadraticEnergy (syncMachine7_Q_symm p)

/-- The co-energy is `∇H = (i_d, i_q, i_f, i_kd, i_kq, ω_r, 0)`. -/
@[powerlib_foundation] theorem syncMachine7_dH (p : SyncMachine7Params) (x : State 7) :
    WithLp.ofLp ((syncMachine7 p).dH x) =
      ![syncMachine7_current p x 0, syncMachine7_current p x 1, syncMachine7_current p x 2,
        syncMachine7_current p x 3, syncMachine7_current p x 4, syncMachine7_speed p x, 0] :=
  syncMachine7_Q_mulVec p x

/-- The pH field reproduces the rate equations of §1.13:
`Ψ̇_d = −r_s i_d + ω_r Ψ_q + v_d`, `Ψ̇_q = −r_s i_q − ω_r Ψ_d + v_q`, `Ψ̇_f = −r_f i_f + v_f`,
`Ψ̇_kd = −r_kd i_kd`, `Ψ̇_kq = −r_kq i_kq`, `ṗ = (i_q Ψ_d − i_d Ψ_q) + T_m^ext − D ω_r`,
`δ̇ = ω_r`. -/
@[powerlib_foundation] theorem syncMachine7_field (p : SyncMachine7Params) (x : State 7)
    (u : Fin 4 → ℝ) :
    WithLp.ofLp ((syncMachine7 p).field x u) =
      ![-p.rs * syncMachine7_current p x 0 + syncMachine7_speed p x * x 1 + u 0,
        -p.rs * syncMachine7_current p x 1 - syncMachine7_speed p x * x 0 + u 1,
        -p.rf * syncMachine7_current p x 2 + u 2,
        -p.rkd * syncMachine7_current p x 3,
        -p.rkq * syncMachine7_current p x 4,
        (syncMachine7_current p x 1 * x 0 - syncMachine7_current p x 0 * x 1) + u 3 -
          p.D * syncMachine7_speed p x,
        syncMachine7_speed p x] := by
  rw [NonlinearModel.ofLp_field, syncMachine7_dH]
  ext i
  fin_cases i <;>
    simp [syncMachine7, syncMachine7_J, syncMachine7_R, syncMachine7_g, mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.diagonal_apply]
  all_goals ring

/-- Damping power `r_s(i_d² + i_q²) + r_f i_f² + r_kd i_kd² + r_kq i_kq² + D ω_r²`. -/
@[powerlib_foundation] theorem syncMachine7_dampingPower (p : SyncMachine7Params) (x : State 7) :
    (syncMachine7 p).dampingPower x =
      p.rs * (syncMachine7_current p x 0 ^ 2 + syncMachine7_current p x 1 ^ 2) +
        p.rf * syncMachine7_current p x 2 ^ 2 + p.rkd * syncMachine7_current p x 3 ^ 2 +
        p.rkq * syncMachine7_current p x 4 ^ 2 + p.D * syncMachine7_speed p x ^ 2 := by
  rw [NonlinearModel.dampingPower, syncMachine7_dH]
  simp [syncMachine7, syncMachine7_R, mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.diagonal_apply]
  ring

/-- Port power `v_d i_d + v_q i_q + v_f i_f + T_m^ext ω_r` (IN-positive). -/
@[powerlib_foundation] theorem syncMachine7_supply (p : SyncMachine7Params) (x : State 7)
    (u : Fin 4 → ℝ) :
    (syncMachine7 p).supply x u =
      u 0 * syncMachine7_current p x 0 + u 1 * syncMachine7_current p x 1 +
        u 2 * syncMachine7_current p x 2 + u 3 * syncMachine7_speed p x := by
  rw [NonlinearModel.supply, NonlinearModel.output, syncMachine7_dH]
  simp [syncMachine7, syncMachine7_g, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Energy balance of §1.13: `Ḣ = (v_d i_d + v_q i_q + v_f i_f + T_m ω_r) −
(r_s(i_d²+i_q²) + r_f i_f² + r_kd i_kd² + r_kq i_kq² + D ω_r²)`; the speed-voltage and
electromagnetic-torque terms cancel. -/
@[powerlib_foundation] theorem syncMachine7_power_balance (p : SyncMachine7Params) (x : State 7)
    (u : Fin 4 → ℝ) :
    fderiv ℝ (syncMachine7 p).H x ((syncMachine7 p).field x u) =
      (u 0 * syncMachine7_current p x 0 + u 1 * syncMachine7_current p x 1 +
        u 2 * syncMachine7_current p x 2 + u 3 * syncMachine7_speed p x) -
      (p.rs * (syncMachine7_current p x 0 ^ 2 + syncMachine7_current p x 1 ^ 2) +
        p.rf * syncMachine7_current p x 2 ^ 2 + p.rkd * syncMachine7_current p x 3 ^ 2 +
        p.rkq * syncMachine7_current p x 4 ^ 2 + p.D * syncMachine7_speed p x ^ 2) := by
  rw [NonlinearModel.power_balance, syncMachine7_supply, syncMachine7_dampingPower]

/-- `H = ½ Ψᵀ Γ Ψ + p² / (2M)`: magnetic plus kinetic energy, independent of `δ`. -/
@[powerlib_foundation] theorem syncMachine7_H (p : SyncMachine7Params) (x : State 7) :
    (syncMachine7 p).H x =
      (1 / 2 : ℝ) * (syncMachine7_flux x ⬝ᵥ (p.Γ *ᵥ syncMachine7_flux x)) +
        x 5 ^ 2 / (2 * p.M) := by
  have hQ := syncMachine7_Q_mulVec p x
  simp only [syncMachine7, quadraticEnergy]
  rw [hQ]
  simp [syncMachine7_current, syncMachine7_flux, syncMachine7_speed, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- The Hamiltonian is nonnegative (`Γ ≻ 0`, `M > 0`). -/
@[powerlib_foundation] theorem syncMachine7_H_nonneg (p : SyncMachine7Params) (x : State 7) :
    0 ≤ (syncMachine7 p).H x := by
  rw [syncMachine7_H]
  have h := p.Γ_posDef.posSemidef.dotProduct_mulVec_nonneg (syncMachine7_flux x)
  rw [star_trivial] at h
  have hM := p.M_pos
  positivity

/-- Along every solution segment the energy balance of §1.13 holds pointwise in time.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem syncMachine7_trajectory_energy_derivative (p : SyncMachine7Params)
    {u : ℝ → (Fin 4 → ℝ)} {x : ℝ → State 7} {t₀ t₁ t : ℝ}
    (hx : (syncMachine7 p).system.IsTrajectoryOn u x t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    HasDerivWithinAt (fun τ => (syncMachine7 p).H (x τ))
      ((syncMachine7 p).supply (x t) (u t) - (syncMachine7 p).dampingPower (x t))
      (Icc t₀ t₁) t :=
  (syncMachine7 p).trajectory_energy_derivative hx ht

/-! ### The rotor-angle direction at the origin -/

/-- The entries of `J(x)` are `C¹` (constants and the flux coordinates `Ψ_d`, `Ψ_q`). -/
private theorem syncMachine7_contDiff_J (i j : Fin 7) :
    ContDiff ℝ 1 fun x : State 7 => syncMachine7_J x i j := by
  fin_cases i <;> fin_cases j <;> simp [syncMachine7_J] <;> fun_prop

/-- `∇H` is the linear map `x ↦ Q x`. -/
private theorem syncMachine7_dH_eq (p : SyncMachine7Params) :
    (syncMachine7 p).dH = Matrix.toEuclideanCLM (n := Fin 7) (𝕜 := ℝ) (syncMachine7_Q p) :=
  funext fun _ => rfl

/-- The zero-input field `(J(x) − R) ∇H(x)` is `C¹`. -/
private theorem syncMachine7_contDiff_zeroInputField (p : SyncMachine7Params) :
    ContDiff ℝ 1 (syncMachine7 p).zeroInputField :=
  (syncMachine7 p).contDiff_zeroInputField syncMachine7_contDiff_J (fun _ _ => contDiff_const)
    (by rw [syncMachine7_dH_eq]; exact ContinuousLinearMap.contDiff _)

/-- At the origin the Jacobian `(J(0) − R) Q` of the zero-input field kills the rotor-angle
direction `e_δ`: `∇H(0) = 0`, and the column of `Q = ∇²H` at `δ` is zero (`∂H/∂δ = 0`). -/
private theorem syncMachine7_fderiv_angle (p : SyncMachine7Params) :
    fderiv ℝ (syncMachine7 p).zeroInputField 0 (EuclideanSpace.single 6 1) = 0 := by
  have hQ : HasFDerivAt (syncMachine7 p).dH
      (Matrix.toEuclideanCLM (n := Fin 7) (𝕜 := ℝ) (syncMachine7_Q p)) 0 := by
    rw [syncMachine7_dH_eq]
    exact ContinuousLinearMap.hasFDerivAt _
  rw [(syncMachine7 p).fderiv_zeroInputField_of_dH_eq_zero
    (fun i j => ((syncMachine7_contDiff_J i j).differentiable one_ne_zero) 0)
    (fun _ _ => differentiableAt_const _) hQ (by rw [syncMachine7_dH_eq, map_zero])]
  have hcol : (syncMachine7_Q p).col 6 = 0 := by
    ext k
    fin_cases k <;> simp [syncMachine7_Q]
  ext i
  simp [hcol]

/-! ### The seven-state machine family -/

namespace SyncMachine7

/-- Requirements of the seven-state machine family: none is available beyond passivity. -/
inductive Requirement
  | impossible

/-- Satisfaction of a requirement. -/
def Meets (_ : SyncMachine7Params) : Requirement → Prop
  | .impossible => False

/-- Passivity needs no requirement; the flow sentences have no translation. -/
def translate : Sentence → Set Requirement
  | .passive => ∅
  | .flow _ => Set.univ
  | .envelope _ => ∅

/-- The seven-state machine family, read as its pH port system at the origin. -/
def family : Family SyncMachine7Params Requirement 7 4 :=
  ⟨fun p => (syncMachine7 p).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isNonlinearPH : family.IsNonlinearPH syncMachine7 :=
  fun _ => rfl

@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.realize_univ_eq_empty_of_forall fun _ h => h .impossible

/-- Passivity of the seven-state machine with storage `H` (T-sync-machine §1.13): for every
input `(v_d, v_q, v_f, T_m^ext)` and solution segment,
`H(x(t₁)) − H(x(t₀)) ≤ ∫ (v_d i_d + v_q i_q + v_f i_f + T_m ω_r)`. -/
@[tmio TM, powerlib_domain] theorem mem_den_passive (p : SyncMachine7Params) :
    connection% (p ∈ family.den .passive) :=
  family_isNonlinearPH.mem_den_passive_of_lowerBound 0 (syncMachine7_H_nonneg p)

/-- Passivity is translated exactly. -/
@[tmio TM, powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  refine Family.exact_of_translate_eq_empty rfl ?_
  ext p
  simp only [Set.mem_univ, iff_true]
  exact mem_den_passive p

/-- Every translation of the seven-state machine family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s p hp => ?_
  rw [(connection_proof% TMIO.mem_realize)] at hp
  change ∀ q ∈ translate s, Meets p q at hp
  rcases s with P | _ | E
  · exact (hp .impossible trivial).elim
  · exact mem_den_passive p
  · exact (Family.mem_den _).mpr trivial

/-- **No seven-state machine is locally exponentially stable at the origin**, whatever its
parameters. A locally exponentially stable point of the `C¹` zero-input field has an injective
Jacobian (converse linearization, `Dynamics.fderiv_injective_of_locallyExponentiallyStable`),
but at the origin the Jacobian `(J(0) − R) ∇²H` kills the rotor-angle direction `e_δ`: `H` does
not depend on `δ` and `∇H(0) = 0`. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable (p : SyncMachine7Params) :
    connection% (p ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isNonlinearPH.mem_den_flow)]
  intro h
  change LocallyExponentiallyStable (syncMachine7 p).zeroInputField 0 at h
  have hv : (EuclideanSpace.single 6 1 : State 7) ≠ 0 := fun h0 => by
    simpa using congrArg (fun z : State 7 => z 6) h0
  exact hv (Dynamics.fderiv_injective_of_locallyExponentiallyStable
    (syncMachine7_contDiff_zeroInputField p) h (by rw [syncMachine7_fderiv_angle, map_zero]))

/-- The translation of local exponential stability (the whole, inconsistent language) is exact:
no member is locally exponentially stable (`not_mem_den_locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hu := realize_univ
  unfold powerlib.TMIO.Statement at hu
  exact Family.exact_of_translate_eq_univ (F := family) hu rfl
    (Set.eq_empty_of_forall_notMem fun p => by
      have h := not_mem_den_locallyExponentiallyStable p
      unfold powerlib.TMIO.Statement at h
      exact h)

end SyncMachine7

end powerlib.Synchronous
