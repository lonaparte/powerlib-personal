import theorem.PH.Linear
import theorem.PH.Linearization
import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.TMIO.ClaimElab
import theorem.CurrentControl.SISO

/-! # Synchronous machines as nonlinear port-Hamiltonian systems

Two models, both instances of `powerlib.PH.NonlinearModel` (P0b), continuous time.

## Classical machine (`classicalSM`, T-ph §1.7 (1.12))
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
* Correction (T-ph §1.1, structural assumption 3 `H ≥ H_min > −∞`): this `H` contains
  `−P_m δ` and is **not bounded below** whenever `P_m ≠ 0`
  (`classicalSM_hamiltonian_not_bddBelow`), so (1.12) violates assumption 3 and the global
  passivity inequality (1.4) with storage `H − H_min` is unavailable; the dissipation
  inequality (`classicalSM_integral_dissipation`) still holds.
* Local stability uses `H − H(x*)` as a local Lyapunov function on the strip
  `|δ| < π/2` around a stable equilibrium `δ* ∈ (−π/2, π/2)`, `b sin δ* = P_m`, `p* = 0`.
  (`H − H(x*)` is in general **not** positive on all of `|δ − δ*| < π`: it changes sign
  beyond the unstable equilibrium `π − δ*`; positivity is only claimed on `|δ| < π/2`.)
  Further: `D > 0, cos δ* > 0` ⇒ local exponential stability; `cos δ* < 0` ⇒ instability.

## Seven-state dq machine (`syncMachine7`, T-sync-machine §1.13)
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
  Not an instance of `PortHamiltonian.Model` (`J` depends on the state, `H` is not diagonal).
* Results: the pH field reproduces every rate equation of §1.13; the energy balance
  `Ḣ = (v_d i_d + v_q i_q + v_f i_f + T_m ω_r) − (r_s(i_d²+i_q²) + r_f i_f² + r_kd i_kd² +
  r_kq i_kq² + D ω_r²)`; `H ≥ 0`; trajectory-level `PassiveWithStorage` with storage `H`.

## Families and connection conclusions

* `ClassicalSM.family`: a complete system is the classical machine together with a selected
  rotor angle `δ*` (`ClassicalSM.Model`, operating point `x* = (δ*, 0)`); the system map reads
  the pH system in coordinates centred at `x*` (`NonlinearModel.shift`), because the library
  reads flow sentences at the origin, so every flow sentence speaks about `x*` itself. The
  requirements are static: `x*` is an equilibrium (`b sin δ* = P_m`), the stable branch
  `|δ*| < π/2`, strict damping with `cos δ* > 0`, the unstable branch `cos δ* < 0`, and zero
  mechanical power (`P_m = 0`, which bounds `H` below). Lyapunov stability translates into an
  equilibrium on the stable branch, the local attractive sentences into a damped equilibrium with
  `cos δ* > 0`, instability into an equilibrium on the unstable branch, passivity into
  `P_m = 0`; the global sentences, decay rates, sampled contraction and conservation have no
  translation (the whole, inconsistent, language). The chain lies below the semantics
  (`ClassicalSM.chain_le_semantics`). The passivity translation is exact
  (`ClassicalSM.exact_passive`): for `P_m ≠ 0` the machine is not passive
  (`ClassicalSM.not_mem_den_passive`) — a slow spin `ω₀ = P_m / (2 (D + 1))`, held at constant
  speed by the port, draws `2π |P_m|` minus the damping loss per revolution, so the energy drawn
  over many revolutions exceeds every nonnegative storage. The local exponential translation is
  exact (`ClassicalSM.exact_locallyExponentiallyStable`): by the converse linearization theorem
  (`Dynamics.isHurwitz_of_locallyExponentiallyStable`) local exponential stability forces an
  equilibrium whose Jacobian `[[0, 1/M], [−b cos δ*, −D/M]]` is Hurwitz, i.e. `D > 0`,
  `cos δ* > 0`. The instability translation is not exact (`ClassicalSM.not_exact_unstable`):
  instability is the failure of Lyapunov stability, so the unbalanced machine
  `ClassicalSM.offEquilibrium` (`P_m = 2 > b = 1`) is unstable
  (`ClassicalSM.offEquilibrium_mem_den_unstable`). The local asymptotic translation is exact
  (`ClassicalSM.exact_locallyAsymptoticallyStable`), although the linearization does not decide the
  degenerate cases: an undamped machine conserves `H`, and at a fold (`cos δ* = 0`) the Hamiltonian
  `p²/(2M) − P_m (s − sin s)` (`classicalSM_H_fold`) is below its value at `(δ*, 0)` on one side, where
  the dissipated `H` keeps every solution away (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`).
  The Lyapunov translation is not exact (`ClassicalSM.not_exact_lyapunovStable`): the stable-branch
  requirement `|δ*| < π/2` is not invariant under whole turns (`ClassicalSM.wrapped`, `δ* = 2π`,
  `ClassicalSM.wrapped_mem_den_lyapunovStable`); its denotation is
  `ClassicalSM.mem_den_lyapunovStable_iff` (`b sin δ* = P_m`, `cos δ* > 0`, every `D ≥ 0`): a fold is
  unstable for every `D ≥ 0` (`classicalSM_accel_fold`, `Dynamics.unstable_of_lie_nonpos_of_lie_pos`).
* `SyncMachine7.family`: a complete system is the seven-state machine (`SyncMachine7Params`),
  read as its pH port system at the origin (the unforced state, an equilibrium). Passivity is
  translated into no requirement and is exact (`H ≥ 0`); flow sentences have no translation.

Connection conclusions: `ClassicalSM.mem_den_lyapunovStable`,
`ClassicalSM.mem_den_locallyExponentiallyStable`, `ClassicalSM.mem_den_unstable` (formerly the
raw `classicalSM_lyapunovStable`, `classicalSM_locallyExponentiallyStable`, `classicalSM_unstable`),
`ClassicalSM.mem_den_passive_of_Pm_zero`, `SyncMachine7.mem_den_passive` (formerly
`syncMachine7_passiveWithStorage`), plus the chain soundness and `realize_univ` of both
families. The rate equations, energies, damping powers, supplies, power balances, equilibrium
characterization, unboundedness of `H` and the linearization are static evidence; the
trajectory-level dissipation inequality of the classical machine and the energy derivative of the
seven-state machine are private implementation evidence.

Source: work-sync `theory/T-ph.md` §1.7 (1.12); `theory/T-sync-machine.md` §1.13.
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter
open scoped Topology
open powerlib.Dynamics (State)

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

@[powerlib_foundation] theorem classicalSM_hasGradientAt (p : ClassicalSMParams) (x : State 2) :
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
  skew _ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
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

/-- Formerly the public `classicalSM_integral_dissipation`: dissipation inequality without any
lower bound on `H`, `H(x(t₁)) − H(x(t₀)) ≤ ∫ u ω`, on every solution segment.
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
  have hmem : classicalSM_equilibrium δs ∈ {x : State 2 | x 0 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)} := by
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

/-- Formerly the public `classicalSM_lyapunovStable`; see `ClassicalSM.mem_den_lyapunovStable`. -/
private theorem classicalSM_lyapunovStable (p : ClassicalSMParams) {δs : ℝ}
    (hδs : δs ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (heq : p.b * Real.sin δs = p.Pm) :
    LyapunovStable (classicalSM p).zeroInputField (classicalSM_equilibrium δs) :=
  (classicalSM_isStrictLocalMin p hδs heq).lyapunovStable

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
    ((classicalSM p).J (classicalSM_equilibrium δs) - (classicalSM p).R (classicalSM_equilibrium δs)) *
        !![p.b * Real.cos δs, 0; 0, 1 / p.M] =
      !![0, 1 / p.M; -(p.b * Real.cos δs), -(p.D / p.M)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [classicalSM, Matrix.diagonal_vec2]
  all_goals ring

/-- Formerly the public `classicalSM_locallyExponentiallyStable`; see
`ClassicalSM.mem_den_locallyExponentiallyStable`. -/
private theorem classicalSM_locallyExponentiallyStable (p : ClassicalSMParams)
    {δs : ℝ} (hD : 0 < p.D) (heq : p.b * Real.sin δs = p.Pm) (hcos : 0 < Real.cos δs) :
    LocallyExponentiallyStable (classicalSM p).zeroInputField (classicalSM_equilibrium δs) := by
  have hM := p.M_pos
  have hb := p.b_pos
  have h0 : (classicalSM p).dH (classicalSM_equilibrium δs) = 0 := by
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> simp [classicalSM, classicalSM_dH, classicalSM_equilibrium, heq]
  have hQ := (classicalSM_hasFDerivAt_dH p (classicalSM_equilibrium δs)).fderiv
  simp only [classicalSM_equilibrium, PiLp.toLp_apply, Matrix.cons_val_zero] at hQ
  refine (classicalSM p).locallyExponentiallyStable_of_isHurwitz (fun _ _ => contDiff_const)
    (fun _ _ => contDiff_const) (classicalSM_contDiff_dH p) hQ h0 ?_
  rw [classicalSM_linearization, Criteria.isHurwitz_fin_two_of_iff]
  constructor
  · have : 0 < p.D / p.M := div_pos hD hM
    linarith
  · have : 0 < 1 / p.M * (p.b * Real.cos δs) := by positivity
    nlinarith

/-- Formerly the public `classicalSM_unstable`; see `ClassicalSM.mem_den_unstable`. -/
private theorem classicalSM_unstable (p : ClassicalSMParams) {δs : ℝ}
    (heq : p.b * Real.sin δs = p.Pm) (hcos : Real.cos δs < 0) :
    Unstable (classicalSM p).zeroInputField (classicalSM_equilibrium δs) := by
  have hM := p.M_pos
  have hb := p.b_pos
  have h0 : (classicalSM p).dH (classicalSM_equilibrium δs) = 0 := by
    apply WithLp.ofLp_injective 2
    ext i
    fin_cases i <;> simp [classicalSM, classicalSM_dH, classicalSM_equilibrium, heq]
  have hQ := (classicalSM_hasFDerivAt_dH p (classicalSM_equilibrium δs)).fderiv
  simp only [classicalSM_equilibrium, PiLp.toLp_apply, Matrix.cons_val_zero] at hQ
  refine (classicalSM p).unstable_of_eigenvalue_re_pos (fun _ _ => contDiff_const)
    (fun _ _ => contDiff_const) (classicalSM_contDiff_dH p) hQ h0 ?_
  rw [classicalSM_linearization]
  apply Criteria.exists_eigenvalue_re_pos_of_det_neg
  rw [Matrix.det_fin_two_of]
  have : 0 < 1 / p.M * (p.b * -Real.cos δs) := by
    have : 0 < -Real.cos δs := by linarith
    positivity
  nlinarith

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

/-- Requirements on the classical machine, all static. -/
inductive Requirement
  /-- `(δ*, 0)` is an equilibrium: `b sin δ* = P_m`. -/
  | locked
  /-- The stable branch `|δ*| < π/2`. -/
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
  | .stableBranch => m.δs ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)
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
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : Meets m .damped := h .damped
  have h2 : Meets m .unstableBranch := h .unstableBranch
  exact lt_asymm h1.2 h2

/-- Lyapunov stability of the stable equilibrium `(δ*, 0)`, `|δ*| < π/2`, `b sin δ* = P_m`, of
the unforced classical machine, for every `D ≥ 0` (`H − H(x*)` as local Lyapunov function). -/
@[powerlib_domain] theorem mem_den_lyapunovStable (m : Model)
    (hδs : m.δs ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (heq : m.p.b * Real.sin m.δs = m.p.Pm) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) :=
  family_isNonlinearPH.mem_den_lyapunovStable_shift (classicalSM_isStrictLocalMin m.p hδs heq)

/-- `D > 0`, `b sin δ* = P_m`, `cos δ* > 0`: the equilibrium `(δ*, 0)` of the full nonlinear
unforced classical machine is locally exponentially stable. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model) (hD : 0 < m.p.D)
    (heq : m.p.b * Real.sin m.δs = m.p.Pm) (hcos : 0 < Real.cos m.δs) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_flow_iff.mpr (classicalSM_locallyExponentiallyStable m.p hD heq hcos)

/-- `b sin δ* = P_m`, `cos δ* < 0` (the unstable branch): the equilibrium `(δ*, 0)` of the full
nonlinear unforced classical machine is unstable, for every `D ≥ 0`. -/
@[powerlib_domain] theorem mem_den_unstable (m : Model) (heq : m.p.b * Real.sin m.δs = m.p.Pm)
    (hcos : Real.cos m.δs < 0) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  mem_den_flow_iff.mpr (classicalSM_unstable m.p heq hcos)

/-- With no mechanical power the Hamiltonian `p²/(2M) − b cos δ ≥ −b` is bounded below, so the
machine is passive. -/
@[powerlib_domain] theorem mem_den_passive_of_Pm_zero (m : Model) (hPm : m.p.Pm = 0) :
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

/-- Every translation of the classical-machine family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · cases P
    case lyapunovStable =>
      exact mem_den_lyapunovStable m (hm .stableBranch (by simp [translate]))
        (hm .locked (by simp [translate]))
    case locallyAsymptoticallyStable =>
      have hd : Meets m .damped := hm .damped (by simp [translate])
      have h := mem_den_locallyExponentiallyStable m hd.1 (hm .locked (by simp [translate])) hd.2
      unfold powerlib.TMIO.Statement at h
      rw [mem_den_flow_iff] at h ⊢
      exact Flow.locallyExponentiallyStable_localAsymptoticStable h
    case locallyExponentiallyStable =>
      have hd : Meets m .damped := hm .damped (by simp [translate])
      exact mem_den_locallyExponentiallyStable m hd.1 (hm .locked (by simp [translate])) hd.2
    case unstable =>
      exact mem_den_unstable m (hm .locked (by simp [translate]))
        (hm .unstableBranch (by simp [translate]))
    all_goals exact (hnone fun q => hm q trivial).elim
  · exact mem_den_passive_of_Pm_zero m (hm .noPower rfl)

/-! #### Exactness of the local exponential translation -/

private theorem zeroInputField_contDiff (p : ClassicalSMParams) :
    ContDiff ℝ 1 (classicalSM p).zeroInputField :=
  (classicalSM p).contDiff_zeroInputField (fun _ _ => contDiff_const) (fun _ _ => contDiff_const)
    (classicalSM_contDiff_dH p)

/-- The local exponential translation is exact: the classical machine is locally exponentially
stable at `(δ*, 0)` exactly when `b sin δ* = P_m`, `D > 0` and `cos δ* > 0`. Converse
linearization: local exponential stability of the `C¹` zero-input field forces an equilibrium
whose Jacobian `(J − R) ∇²H = [[0, 1/M], [−b cos δ*, −D/M]]` is Hurwitz. -/
@[powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [TMIO.mem_realize]
  simp only [family, translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro ⟨hl, hd⟩
    exact mem_den_locallyExponentiallyStable m hd.1 hl hd.2
  · intro h
    have hles : LocallyExponentiallyStable (classicalSM m.p).zeroInputField m.point :=
      mem_den_flow_iff.mp h
    have hcd := zeroInputField_contDiff m.p
    have heq := Dynamics.isEquilibrium_of_locallyExponentiallyStable hcd hles
    rw [classicalSM_isEquilibrium_iff] at heq
    have hl : m.p.b * Real.sin m.δs = m.p.Pm := by
      simpa [Model.point, classicalSM_equilibrium] using heq.1
    have h0 : (classicalSM m.p).dH m.point = 0 := by
      apply WithLp.ofLp_injective 2
      ext i
      fin_cases i <;> simp [classicalSM, classicalSM_dH, Model.point, classicalSM_equilibrium, hl]
    have hQ := classicalSM_hasFDerivAt_dH m.p m.point
    simp only [Model.point, classicalSM_equilibrium, PiLp.toLp_apply, Matrix.cons_val_zero] at hQ
    have hJac := (classicalSM m.p).fderiv_zeroInputField_of_dH_eq_zero
      (fun _ _ => differentiableAt_const _) (fun _ _ => differentiableAt_const _) hQ h0
    have hA := Dynamics.isHurwitz_of_locallyExponentiallyStable _ hcd hJac hles
    have hlin : ((classicalSM m.p).J (WithLp.toLp 2 ![m.δs, 0]) -
        (classicalSM m.p).R (WithLp.toLp 2 ![m.δs, 0])) *
          !![m.p.b * Real.cos m.δs, 0; 0, 1 / m.p.M] =
        !![0, 1 / m.p.M; -(m.p.b * Real.cos m.δs), -(m.p.D / m.p.M)] :=
      classicalSM_linearization m.p m.δs
    rw [hlin, Criteria.isHurwitz_fin_two_of_iff] at hA
    obtain ⟨htr, hdet⟩ := hA
    have hM := m.p.M_pos
    have hb := m.p.b_pos
    refine ⟨hl, show 0 < m.p.D ∧ 0 < Real.cos m.δs from ⟨?_, ?_⟩⟩
    · have : 0 < m.p.D / m.p.M := by linarith
      exact (div_pos_iff_of_pos_right hM).mp this
    · have : 0 < 1 / m.p.M * (m.p.b * Real.cos m.δs) := by linarith
      have h2 : 0 < m.p.b * Real.cos m.δs := pos_of_mul_pos_right this (by positivity)
      exact pos_of_mul_pos_right h2 hb.le

/-! #### The local asymptotic and Lyapunov translations -/

private theorem norm_state2_le (x : State 2) : ‖x‖ ≤ |x 0| + |x 1| := by
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  have hsq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_succ, sq_abs]
  have h : ‖x‖ ^ 2 ≤ (|x 0| + |x 1|) ^ 2 := by
    rw [hsq]
    nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg h0 h1]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

private theorem norm_seed_sub (δs s w : ℝ) :
    ‖(WithLp.toLp 2 ![δs + s, w] : State 2) - classicalSM_equilibrium δs‖ ≤ |s| + |w| := by
  refine (norm_state2_le _).trans (le_of_eq ?_)
  simp [classicalSM_equilibrium]

private theorem H_contDiff (p : ClassicalSMParams) : ContDiff ℝ 1 (classicalSM_H p) := by
  unfold classicalSM_H
  fun_prop

/-- Under zero input the Hamiltonian decreases at the damping rate `D ω²`. -/
private theorem H_lie (p : ClassicalSMParams) (x : State 2) :
    fderiv ℝ (classicalSM_H p) x ((classicalSM p).zeroInputField x) =
      -(p.D * (x 1 / p.M) ^ 2) := by
  have h := (classicalSM p).zeroInput_power_balance x
  rw [classicalSM_dampingPower] at h
  exact h

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

private theorem Pm_ne_zero_of_fold (p : ClassicalSMParams) {δs : ℝ}
    (heq : p.b * Real.sin δs = p.Pm) (hcos : Real.cos δs = 0) : p.Pm ≠ 0 := by
  intro h0
  rw [h0] at heq
  have hs : Real.sin δs = 0 := (mul_eq_zero.mp heq).resolve_left p.b_pos.ne'
  have := Real.sin_sq_add_cos_sq δs
  rw [hs, hcos] at this
  norm_num at this

/-- At a fold the Hamiltonian takes values below `H(δ*, 0)` arbitrarily close to it. -/
private theorem fold_seeds (p : ClassicalSMParams) {δs : ℝ} (heq : p.b * Real.sin δs = p.Pm)
    (hcos : Real.cos δs = 0) : ∀ ε > 0, ∃ x, ‖x - classicalSM_equilibrium δs‖ < ε ∧
      classicalSM_H p x < classicalSM_H p (classicalSM_equilibrium δs) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hP := Pm_ne_zero_of_fold p heq hcos
  have hsin := Real.sin_lt hε2
  rcases lt_or_gt_of_ne hP with hneg | hpos
  · refine ⟨WithLp.toLp 2 ![δs + -(ε / 2), 0], ?_, ?_⟩
    · refine (norm_seed_sub _ _ _).trans_lt ?_
      rw [abs_neg, abs_of_pos hε2, abs_zero, add_zero]
      linarith
    · have h := classicalSM_H_fold p heq hcos (-(ε / 2)) 0
      rw [Real.sin_neg] at h
      nlinarith
  · refine ⟨WithLp.toLp 2 ![δs + ε / 2, 0], ?_, ?_⟩
    · refine (norm_seed_sub _ _ _).trans_lt ?_
      rw [abs_of_pos hε2, abs_zero, add_zero]
      linarith
    · have h := classicalSM_H_fold p heq hcos (ε / 2) 0
      nlinarith

/-- Local asymptotic stability of `(δ*, 0)` forces `b sin δ* = P_m`, `D > 0` and `cos δ* > 0`:
an undamped machine conserves `H`, the unstable branch is unstable, and at a fold `H` is below
its value at `(δ*, 0)` on one side, where the dissipated `H` keeps every solution away. -/
private theorem las_requirements {m : Model}
    (hlas : LocalAsymptoticStable (classicalSM m.p).zeroInputField m.point) :
    m.p.b * Real.sin m.δs = m.p.Pm ∧ 0 < m.p.D ∧ 0 < Real.cos m.δs := by
  have hcd := zeroInputField_contDiff m.p
  have heq := Dynamics.isEquilibrium_of_lyapunovStable hcd hlas.1
  rw [classicalSM_isEquilibrium_iff] at heq
  have hl : m.p.b * Real.sin m.δs = m.p.Pm := by
    simpa [Model.point, classicalSM_equilibrium] using heq.1
  have hM := m.p.M_pos
  have hHd : Differentiable ℝ (classicalSM_H m.p) := (H_contDiff m.p).differentiable one_ne_zero
  have hD : 0 < m.p.D := by
    rcases eq_or_lt_of_le m.p.D_nonneg with hD | hD
    · exfalso
      refine Dynamics.not_localAsymptoticStable_of_lie_nonpos
        (V := fun x => -classicalSM_H m.p x) (ρ := 1) hcd hHd.neg one_pos (fun x _ => ?_)
        (fun ε hε => ⟨WithLp.toLp 2 ![m.δs + 0, ε / 2], ?_, ?_⟩) hlas
      · rw [fderiv_fun_neg, _root_.neg_apply, H_lie, ← hD]
        simp
      · refine (norm_seed_sub _ _ _).trans_lt ?_
        rw [abs_zero, zero_add, abs_of_pos (by linarith)]
        linarith
      · simp only [Model.point, classicalSM_H, classicalSM_equilibrium, PiLp.toLp_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero]
        have : 0 < 1 / (2 * m.p.M) * (ε / 2) ^ 2 := by positivity
        linarith
    · exact hD
  refine ⟨hl, hD, ?_⟩
  rcases lt_trichotomy (Real.cos m.δs) 0 with hc | hc | hc
  · exact absurd hlas.1 (classicalSM_unstable m.p hl hc)
  · exfalso
    refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := classicalSM_H m.p) (ρ := 1)
      hcd hHd one_pos (fun x _ => ?_) (fold_seeds m.p hl hc) hlas
    rw [H_lie]
    have := m.p.D_nonneg
    nlinarith [sq_nonneg (x 1 / m.p.M)]
  · exact hc

/-- The local asymptotic translation is exact: the classical machine is locally asymptotically
stable at `(δ*, 0)` exactly when `b sin δ* = P_m`, `D > 0` and `cos δ* > 0`. The linearization
does not decide the degenerate cases, the model's structure does: an undamped machine conserves
`H`, and at a fold (`cos δ* = 0`) the Hamiltonian `p²/(2M) − P_m (s − sin s)`
(`classicalSM_H_fold`) is below its value at `(δ*, 0)` on one side, where the dissipated `H`
keeps every solution away (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`). -/
@[powerlib_domain] theorem exact_locallyAsymptoticallyStable :
    connection% (family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [TMIO.mem_realize]
  simp only [family, translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro ⟨hl, hd⟩
    have h := mem_den_locallyExponentiallyStable m hd.1 hl hd.2
    unfold powerlib.TMIO.Statement at h
    exact mem_den_flow_iff.mpr
      (Flow.locallyExponentiallyStable_localAsymptoticStable (mem_den_flow_iff.mp h))
  · intro h
    obtain ⟨hl, hD, hc⟩ := las_requirements (mem_den_flow_iff.mp h)
    exact ⟨hl, hD, hc⟩

/-- The zero-input field is `2π`-periodic in the rotor angle. -/
private theorem zeroInputField_add_period (p : ClassicalSMParams) (k : ℤ) (x : State 2) :
    (classicalSM p).zeroInputField (x + WithLp.toLp 2 ![k * (2 * Real.pi), 0]) =
      (classicalSM p).zeroInputField x := by
  apply WithLp.ofLp_injective 2
  simp only [NonlinearModel.zeroInputField]
  rw [classicalSM_field, classicalSM_field]
  ext i
  fin_cases i <;> simp [Real.sin_add_int_mul_two_pi]

private theorem lyapunovStable_add_period (p : ClassicalSMParams) (δs : ℝ) (k : ℤ) :
    LyapunovStable (classicalSM p).zeroInputField
        (classicalSM_equilibrium (δs + k * (2 * Real.pi))) ↔
      LyapunovStable (classicalSM p).zeroInputField (classicalSM_equilibrium δs) := by
  have hfun : (fun z => (classicalSM p).zeroInputField
        (z + classicalSM_equilibrium (δs + k * (2 * Real.pi)))) =
      fun z => (classicalSM p).zeroInputField (z + classicalSM_equilibrium δs) := by
    funext z
    have hz : z + classicalSM_equilibrium (δs + k * (2 * Real.pi)) =
        (z + classicalSM_equilibrium δs) + WithLp.toLp 2 ![k * (2 * Real.pi), 0] := by
      ext i
      fin_cases i
      · simp [classicalSM_equilibrium]
        ring
      · simp [classicalSM_equilibrium]
    rw [hz, zeroInputField_add_period]
  have h1 := Flow.Property.holds_shift_iff (f := (classicalSM p).zeroInputField)
    (e := classicalSM_equilibrium (δs + k * (2 * Real.pi))) Flow.Property.lyapunovStable
  have h2 := Flow.Property.holds_shift_iff (f := (classicalSM p).zeroInputField)
    (e := classicalSM_equilibrium δs) Flow.Property.lyapunovStable
  rw [hfun] at h1
  exact h1.symm.trans h2

/-- Lyapunov stability holds exactly at the equilibria with `cos δ* > 0` (every damping
`D ≥ 0`): the stable branch up to whole turns. The unstable branch is unstable, and a fold
(`cos δ* = 0`) is unstable for every `D ≥ 0`: below the level of `(δ*, 0)` the dissipated
Hamiltonian keeps the solution, and there `P_m (p + D δ)` grows at the rate
`P_m² (1 − cos(δ − δ*))` (`Dynamics.unstable_of_lie_nonpos_of_lie_pos`). -/
@[powerlib_domain] theorem mem_den_lyapunovStable_iff (m : Model) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.p.b * Real.sin m.δs = m.p.Pm ∧ 0 < Real.cos m.δs}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq, mem_den_flow_iff]
  have hcd := zeroInputField_contDiff m.p
  have hM := m.p.M_pos
  constructor
  · intro hls
    have heq := Dynamics.isEquilibrium_of_lyapunovStable hcd hls
    rw [classicalSM_isEquilibrium_iff] at heq
    have hl : m.p.b * Real.sin m.δs = m.p.Pm := by
      simpa [Model.point, classicalSM_equilibrium] using heq.1
    refine ⟨hl, ?_⟩
    rcases lt_trichotomy (Real.cos m.δs) 0 with hc | hc | hc
    · exact absurd hls (classicalSM_unstable m.p hl hc)
    · exfalso
      set a := m.p.Pm with ha
      have h0 := fun x : State 2 => (smCoord (n := 2) 0).hasFDerivAt (x := x)
      have h1 := fun x : State 2 => (smCoord (n := 2) 1).hasFDerivAt (x := x)
      have hW : ContDiff ℝ 1 fun x : State 2 => a * (x 1 + m.p.D * x 0) :=
        contDiff_const.mul ((smCoord (n := 2) 1).contDiff.add
          (contDiff_const.mul (smCoord (n := 2) 0).contDiff))
      refine Dynamics.unstable_of_lie_nonpos_of_lie_pos (E := classicalSM_H m.p)
        (W := fun x : State 2 => a * (x 1 + m.p.D * x 0)) (r := 1) hcd (H_contDiff m.p) hW
        one_pos (fun x _ => ?_) (fold_seeds m.p hl hc) (fun x hx hEx => ?_) hls
      · rw [H_lie]
        have := m.p.D_nonneg
        nlinarith [sq_nonneg (x 1 / m.p.M)]
      · have hd : HasFDerivAt (fun y : State 2 => a * (y 1 + m.p.D * y 0))
            (a • (smCoord (n := 2) 1 + m.p.D • smCoord (n := 2) 0)) x :=
          ((h1 x).add ((h0 x).const_mul m.p.D)).const_mul a
        rw [hd.fderiv]
        have hf := classicalSM_field m.p x 0
        have hf0 : ((classicalSM m.p).zeroInputField x) 0 = x 1 / m.p.M := by
          have := congrFun hf 0
          simpa [NonlinearModel.zeroInputField] using this
        have hf1 : ((classicalSM m.p).zeroInputField x) 1 =
            m.p.Pm - m.p.b * Real.sin (x 0) - m.p.D * (x 1 / m.p.M) := by
          have := congrFun hf 1
          simpa [NonlinearModel.zeroInputField] using this
        simp only [_root_.smul_apply, _root_.add_apply, smCoord, PiLp.proj_apply, smul_eq_mul,
          hf0, hf1]
        set s₀ := x 0 - m.δs with hs₀
        have hx0 : x 0 = m.δs + s₀ := by rw [hs₀]; ring
        have hrate : m.p.Pm - m.p.b * Real.sin (x 0) - m.p.D * (x 1 / m.p.M) +
            m.p.D * (x 1 / m.p.M) = a * (1 - Real.cos s₀) := by
          rw [hx0, ← classicalSM_accel_fold m.p hl hc]
          ring
        rw [hrate]
        have hs1 : |s₀| ≤ 1 := by
          have h' := PiLp.norm_apply_le (x - classicalSM_equilibrium m.δs) 0
          have he : (x - classicalSM_equilibrium m.δs) 0 = s₀ := by
            simp [classicalSM_equilibrium, hs₀]
          rw [he, Real.norm_eq_abs] at h'
          exact h'.trans hx
        have hs0 : s₀ ≠ 0 := by
          intro h
          have hx' : x = WithLp.toLp 2 ![m.δs + 0, x 1] := by
            ext i
            fin_cases i
            · simp [hx0, h]
            · simp
          have hfold := classicalSM_H_fold m.p hl hc 0 (x 1)
          rw [← hx'] at hfold
          change classicalSM_H m.p x < classicalSM_H m.p (classicalSM_equilibrium m.δs) at hEx
          have : 0 ≤ 1 / (2 * m.p.M) * x 1 ^ 2 := by positivity
          simp only [sub_zero, Real.sin_zero, mul_zero] at hfold
          linarith
        have hcos1 : Real.cos s₀ < 1 := by
          refine lt_of_le_of_ne (Real.cos_le_one _) fun h => hs0 ?_
          refine (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp h
          · linarith [neg_abs_le s₀, Real.two_le_pi]
          · linarith [le_abs_self s₀, Real.two_le_pi]
        have ha0 : a ≠ 0 := Pm_ne_zero_of_fold m.p hl hc
        have : 0 < a * a := mul_self_pos.mpr ha0
        nlinarith
    · exact hc
  · rintro ⟨hl, hc⟩
    -- reduce to the stable branch `|δ'| < π/2`, `δ* = δ' + k · 2π`
    set k : ℤ := round (m.δs / (2 * Real.pi)) with hk
    set δ' := m.δs - k * (2 * Real.pi) with hδ'
    have hpi := Real.pi_pos
    have habs : |δ'| ≤ Real.pi := by
      have h := abs_sub_round (m.δs / (2 * Real.pi))
      have : δ' = 2 * Real.pi * (m.δs / (2 * Real.pi) - round (m.δs / (2 * Real.pi))) := by
        rw [hδ', hk]; field_simp
      rw [this, abs_mul, abs_of_pos (by positivity)]
      nlinarith
    have hcos' : Real.cos δ' = Real.cos m.δs := by
      rw [hδ', Real.cos_sub_int_mul_two_pi]
    have hsin' : Real.sin δ' = Real.sin m.δs := by
      rw [hδ', Real.sin_sub_int_mul_two_pi]
    have hmem : δ' ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · by_contra h
        push Not at h
        have : Real.cos δ' ≤ 0 := by
          rw [← Real.cos_neg]
          exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith)
            (by linarith [neg_abs_le δ'])
        linarith
      · by_contra h
        push Not at h
        have : Real.cos δ' ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [le_abs_self δ'])
        linarith
    have hls := classicalSM_lyapunovStable m.p hmem (by rw [hsin']; exact hl)
    have hδs : m.δs = δ' + k * (2 * Real.pi) := by rw [hδ']; ring
    change LyapunovStable _ (classicalSM_equilibrium m.δs)
    rw [hδs, lyapunovStable_add_period]
    exact hls

/-- A machine balanced one whole turn away from the reference: `M = b = 1`, `D = P_m = 0`,
`δ* = 2π`. It is the stable equilibrium `(0, 0)` up to a turn. -/
def wrapped : Model := ⟨⟨1, 0, 1, 0, one_pos, le_rfl, one_pos⟩, 2 * Real.pi⟩

/-- The wrapped machine is Lyapunov stable (`cos 2π = 1 > 0`). -/
@[powerlib_domain] theorem wrapped_mem_den_lyapunovStable :
    connection% (wrapped ∈ family.den (.flow .lyapunovStable)) := by
  have h := mem_den_lyapunovStable_iff wrapped
  unfold powerlib.TMIO.Statement at h ⊢
  exact h.mpr ⟨by simp [wrapped], by simp [wrapped]⟩

/-- The Lyapunov translation is sound but not exact: the stable-branch requirement
`|δ*| < π/2` is not invariant under whole turns, so the wrapped machine is Lyapunov stable
without meeting it. Its denotation is `mem_den_lyapunovStable_iff` (`cos δ* > 0`). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := wrapped_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : Meets wrapped .stableBranch := hmem .stableBranch (by simp [family, translate])
  have h2 := hs.2
  simp only [wrapped] at h2
  linarith [Real.pi_pos]

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
@[powerlib_domain] theorem not_mem_den_passive (m : Model) (hPm : m.p.Pm ≠ 0) :
    connection% (m ∉ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den]
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
  have htraj : (family.system m).IsTrajectoryOn (spinInput m ω₀) (spin m ω₀) 0 T := by
    intro t _
    show HasDerivWithinAt (spin m ω₀) (m.toPH.system.field (spin m ω₀ t) (spinInput m ω₀ t))
      (Set.Icc 0 T) t
    rw [spin_field]
    exact (spin_hasDerivAt m ω₀ t).hasDerivWithinAt
  have hsupply : (fun t => (family.system m).supply (spin m ω₀ t) (spinInput m ω₀ t)) =
      fun t => ω₀ * (-m.p.Pm + m.p.b * Real.sin (ω₀ * t + m.δs) + m.p.D * ω₀) :=
    funext (spin_supply m ω₀)
  have hcont : Continuous fun t : ℝ =>
      ω₀ * (-m.p.Pm + m.p.b * Real.sin (ω₀ * t + m.δs) + m.p.D * ω₀) := by fun_prop
  have hint : IntervalIntegrable
      (fun t => (family.system m).supply (spin m ω₀ t) (spinInput m ω₀ t)) MeasureTheory.volume
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
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [TMIO.mem_realize]
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

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Dynamics.unstable_of_ne_zero
    (zeroInputField_contDiff offEquilibrium.p) fun h => ?_)
  have h' := (classicalSM_isEquilibrium_iff offEquilibrium.p _).mp h
  simp [offEquilibrium, Model.point, classicalSM_equilibrium] at h'

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for an equilibrium. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hl : Meets offEquilibrium .locked := hmem .locked (by simp [family, translate])
  simp [Meets, offEquilibrium] at hl

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
@[powerlib_foundation] theorem syncMachine7_inductance_symm (Ld Lq Lad Laq Lff Lfkd Lkdkd Lkqkq : ℝ) :
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
      (1 / 2 : ℝ) * (syncMachine7_flux x ⬝ᵥ (p.Γ *ᵥ syncMachine7_flux x)) + x 5 ^ 2 / (2 * p.M) := by
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

/-- Formerly the public `syncMachine7_trajectory_energy_derivative`: along every solution segment
the energy balance of §1.13 holds pointwise in time.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem syncMachine7_trajectory_energy_derivative (p : SyncMachine7Params)
    {u : ℝ → (Fin 4 → ℝ)} {x : ℝ → State 7} {t₀ t₁ t : ℝ}
    (hx : (syncMachine7 p).system.IsTrajectoryOn u x t₀ t₁) (ht : t ∈ Icc t₀ t₁) :
    HasDerivWithinAt (fun τ => (syncMachine7 p).H (x τ))
      ((syncMachine7 p).supply (x t) (u t) - (syncMachine7 p).dampingPower (x t))
      (Icc t₀ t₁) t :=
  (syncMachine7 p).trajectory_energy_derivative hx ht

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

/-- The seven-state machine family, read as its pH port system at the origin. -/
def family : Family SyncMachine7Params Requirement 7 4 :=
  ⟨fun p => (syncMachine7 p).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isNonlinearPH : family.IsNonlinearPH syncMachine7 :=
  fun _ => rfl

@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext p
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  exact fun h => h .impossible

/-- Passivity of the seven-state machine with storage `H` (T-sync-machine §1.13): for every
input `(v_d, v_q, v_f, T_m^ext)` and solution segment,
`H(x(t₁)) − H(x(t₀)) ≤ ∫ (v_d i_d + v_q i_q + v_f i_f + T_m ω_r)`. -/
@[powerlib_domain] theorem mem_den_passive (p : SyncMachine7Params) :
    connection% (p ∈ family.den .passive) :=
  family_isNonlinearPH.mem_den_passive_of_lowerBound 0 (syncMachine7_H_nonneg p)

/-- Passivity is translated exactly. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  refine Family.exact_of_translate_eq_empty rfl ?_
  ext p
  simp only [Set.mem_univ, iff_true]
  exact mem_den_passive p

/-- Every translation of the seven-state machine family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s p hp => ?_
  rw [TMIO.mem_realize] at hp
  change ∀ q ∈ translate s, Meets p q at hp
  rcases s with P | _
  · exact (hp .impossible trivial).elim
  · exact mem_den_passive p

end SyncMachine7

end powerlib.PH
