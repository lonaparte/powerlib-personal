import theorem.PH.Linear
import theorem.PH.Linearization
import theorem.Criteria.Hurwitz2
import theorem.TMIO.ClaimElab

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
  (`ClassicalSM.chain_le_semantics`). Exactness of the passivity translation (non-passivity for
  `P_m ≠ 0`) and of the local translations is not claimed (UNPROVED).
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
