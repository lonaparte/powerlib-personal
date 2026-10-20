import theorem.Network.Swing.Basic
import theorem.Dynamics.Mechanical
import theorem.Spectral.Equilibrium

/-! # Networked swing equations: energy, degenerate linearizations, local asymptotic stability

The energy function of the swing network, its Taylor expansion at a power-balance point, and the
complete characterization of local asymptotic stability, which decides the exactness of the local
asymptotic translation for two and three machines.

Model boundary.
* Exactly the model of `theorem/Network/Swing/Basic.lean` (`Swing.family`): `n + 1` machines,
  reduced state `(δ, ω)` of order `Fin (n + (n + 1))` (relative angles `δᵢ = θ_{i+1} − θ₀`, then
  all frequency deviations), positive inertia and damping, constant power, symmetric nonnegative
  couplings, lossless Kron-reduced network, constant voltages; no governor, AVR, PLL, converter
  control, delay or PWM; continuous time. Statements concern the selected angle profile `θ*` of
  a model.

Source: work-sync `theory/T-synchronization-manifold.md` §1.7 and §2.2 (swing network
`Mᵢ θ̈ᵢ = P_{m,i} − Dᵢ θ̇ᵢ − ∑ⱼ Bᵢⱼ sin(θᵢ − θⱼ)` and its energy function).

Results.
* Energy (static foundation): `potential` `U(θ) = −∑ Pₖθₖ − ½∑ₖ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)` with
  gradient `Pₖ(θ) − Pₖ` (`hasFDerivAt_potential`), `energy` (kinetic plus potential of the
  absolute angles) and the energy balance `lie_energy` (`Ė = −∑ Dₖωₖ² + ω₀ ∑ Pₖ`, so `Ė ≤ 0` at a
  power-balance point, `lie_energy_nonpos`).
* Mechanical structure (static): `reducedField_eq_mechanical` — with zero total power the reduced
  field is the damped mechanical field `Dynamics.Mechanical.field relRate M D (U ∘ ground)` of
  `theorem/Dynamics/Mechanical.lean` (positions the relative angles, velocities the frequency
  deviations, `relRate ω = (ωᵢ₊₁ − ω₀)ᵢ`); `equilibrium_eq_point`,
  `potential_ground_relAngles_add` (the potential in relative angles about `relAngles θ` is
  `U(θ + ground v)`), `critical_iff_balance` (its critical points along the reachable directions
  are the power-balance points), `fderiv_potential_comp_ground_relRate`.
* Edge form and Taylor expansion: `potential_add_sub`
  (`U(θ + u) − U(θ) = ½∑ Bₖⱼ g(θₖ − θⱼ, uₖ − uⱼ)`, `g = edgeIncrement`; `B g` is the line
  potential `CycleMinimum.edgeG` of `theorem/Network/Swing/CycleMinimum.lean`),
  `edgeIncrement_taylor`, `exists_potential_lt` (a direction with `A₂ < 0`, or `A₂ = 0` and
  `A₃ ≠ 0`, lowers the potential at arbitrarily small steps).
* Hurwitz test with signed weights: `jacobian_isHurwitz_of_hessForm` (the reduced Jacobian is
  Hurwitz when `A₂` is positive on grounded directions), `exists_hessForm_nonpos`.
* Three-machine arithmetic (static): `triangle_cubic_ne_zero`, `sin_mul_cos_same_sign`,
  `node_open_or_antiphase`, `balance_line_of_edges`: on at most three machines every singular
  positive semidefinite Hessian is a fold (nonzero cubic term along the null direction) or comes
  with a continuum of equilibria.
* Four machines (`n = 3`): `theorem/Network/Swing/Four.lean` proves exactness for every network
  with at most four lines (`mem_den_locallyAsymptoticallyStable_iff_four`; two uncoupled machine
  pairs: a subgraph of a four-cycle, the cubic term by superadditivity of `tan`, or of a triangle
  with a pendant line) and the cut and flat-direction tests for every `n`;
  `theorem/Network/Swing/FourDense.lean` decides the diamond and the complete graph and proves
  `exact_locallyAsymptoticallyStable_four` (exact for every four-machine network) and
  `mem_den_locallyAsymptoticallyStable_iff_four_machines`. For five or more machines the
  translation is not exact (`theorem/Network/Swing/DegenerateRing.lean`).

Family and connection conclusions.
* The family is `Swing.family`; the public behavioural conclusions are `connection%` statements on
  its generated denotations, with static premises.
* `not_localAsymptoticStable_of_forms` — at a power-balance point a relative-angle direction with
  `A₂ < 0`, or `A₂ = 0` and `A₃ ≠ 0` (a saddle or a fold), puts the model outside the local
  asymptotic denotation.
* `mem_den_locallyAsymptoticallyStable_iff_of_guard` — a model at which every power-balance
  point with a non-Hurwitz reduced Jacobian fails local asymptotic stability is locally
  asymptotically stable exactly when its profile is a power-balance point with a Hurwitz reduced
  Jacobian; `exact_locallyAsymptoticallyStable_of_guard`, the same for every model of
  `family (n := n)`: the local asymptotic translation is exact. The four-machine results of
  `Four.lean` and `FourDense.lean` are instances.
* `not_localAsymptoticStable_two`, `not_localAsymptoticStable_three` — two or three machines at a
  power-balance point with a non-Hurwitz reduced Jacobian are not locally asymptotically stable;
  hence `exact_locallyAsymptoticallyStable_two` (`n = 1`) and
  `exact_locallyAsymptoticallyStable_three` (`n = 2`): the local asymptotic translation
  `{powerFlow, jacobianStable}` is exact.
* `mem_den_locallyAsymptoticallyStable_iff` — complete membership characterization, every `n`:
  local asymptotic stability ⇔ power balance ∧ a strict local minimum of the potential in relative
  angles ∧ an isolated power-balance point. Sufficiency by LaSalle
  (`Dynamics.Mechanical.localAsymptoticStable_of_strictMin`), necessity by the energy
  (`Dynamics.Mechanical.strictMin_of_localAsymptoticStable`), through `reducedField_eq_mechanical`.
* The generic obstructions — a non-minimum of the potential, a continuum of equilibria — are the
  foundation results `Dynamics.Mechanical.not_localAsymptoticStable_of_potential_lt` and
  `Dynamics.Mechanical.not_localAsymptoticStable_of_critical_line`, applied through
  `reducedField_eq_mechanical`. Their field-level instances and the field-level forms of the
  statements above are private implementation evidence.
-/

noncomputable section
namespace powerlib.Network.Swing
open Matrix Finset Filter Topology Metric
open powerlib.Dynamics (State)

variable {n : ℕ}

/-- Network potential `U(θ) = −∑ₖ Pₖ θₖ − ½ ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)`. -/
def potential (p : Params n) (θ : Fin (n + 1) → ℝ) : ℝ :=
  -(∑ k, p.P k * θ k) - (∑ k, ∑ j, p.B k j * Real.cos (θ k - θ j)) / 2

/-- Swing energy on the reduced state: kinetic energy plus the potential of the absolute angles
`angleMap z` (with `θ₀ = 0`). -/
def energy (p : Params n) (z : State (n + (n + 1))) : ℝ :=
  (∑ k, p.M k * z (wIdx k) ^ 2) / 2 + potential p (angleMap z)

@[powerlib_foundation] theorem sum_powerInjection (p : Params n) (θ : Fin (n + 1) → ℝ) :
    ∑ k, powerInjection p.B θ k = 0 := by
  have h : ∑ k, powerInjection p.B θ k = -∑ k, powerInjection p.B θ k := by
    unfold powerInjection
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [p.B_symm, show θ j - θ k = -(θ k - θ j) by ring, Real.sin_neg]
    ring
  linarith

/-- `∑ₖ ∑ⱼ Bₖⱼ sin(θₖ − θⱼ)(vₖ − vⱼ) = 2 ∑ₖ Pₖ(θ) vₖ`. -/
@[powerlib_foundation] theorem sum_sin_mul_sub (p : Params n) (θ v : Fin (n + 1) → ℝ) :
    ∑ k, ∑ j, p.B k j * Real.sin (θ k - θ j) * (v k - v j) =
      2 * ∑ k, powerInjection p.B θ k * v k := by
  have h1 : ∑ k, ∑ j, p.B k j * Real.sin (θ k - θ j) * v j =
      -∑ k, ∑ j, p.B k j * Real.sin (θ k - θ j) * v k := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [p.B_symm, show θ j - θ k = -(θ k - θ j) by ring, Real.sin_neg]
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, h1, powerInjection, Finset.sum_mul]
  ring

/-- The gradient of the potential: `∂U/∂θₖ = Pₖ(θ) − Pₖ`. -/
def potentialGrad (p : Params n) (θ : Fin (n + 1) → ℝ) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  ∑ k, (powerInjection p.B θ k - p.P k) • ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin (n + 1) => ℝ) k

@[powerlib_foundation] theorem potentialGrad_apply (p : Params n) (θ v : Fin (n + 1) → ℝ) :
    potentialGrad p θ v = ∑ k, (powerInjection p.B θ k - p.P k) * v k := by
  simp [potentialGrad]

@[powerlib_foundation] theorem hasFDerivAt_potential (p : Params n) (θ : Fin (n + 1) → ℝ) :
    HasFDerivAt (potential p) (potentialGrad p θ) θ := by
  have hlin : HasFDerivAt (fun φ : Fin (n + 1) → ℝ => ∑ k, p.P k * φ k)
      (∑ k, p.P k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k) θ := by
    refine HasFDerivAt.fun_sum fun k _ => ?_
    exact (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (n + 1) => ℝ) k θ).const_mul (p.P k)
  have hcos : HasFDerivAt (fun φ : Fin (n + 1) → ℝ => ∑ k, ∑ j, p.B k j * Real.cos (φ k - φ j))
      (∑ k, ∑ j, (-(p.B k j * Real.sin (θ k - θ j))) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j)) θ := by
    refine HasFDerivAt.fun_sum fun k _ => HasFDerivAt.fun_sum fun j _ => ?_
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (n + 1) => ℝ) k θ).sub
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (n + 1) => ℝ) j θ)).cos.const_mul (p.B k j)
    convert hd using 1
    ext v
    simp [smul_eq_mul]
    ring
  have h := hlin.neg.sub (hcos.const_mul (1 / 2 : ℝ))
  convert h using 1
  · funext φ
    simp only [potential, Pi.sub_apply, Pi.neg_apply]
    ring
  ext v
  simp only [potentialGrad_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, ContinuousLinearMap.coe_sub',
    Pi.sub_apply]
  have := sum_sin_mul_sub p θ v
  simp only [neg_mul, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib] at this ⊢
  simp only [sub_mul, Finset.sum_sub_distrib]
  linarith

@[powerlib_foundation] theorem potential_contDiff (p : Params n) {N : WithTop ℕ∞} :
    ContDiff ℝ N (potential p) := by
  unfold potential
  apply ContDiff.sub
  · exact (ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply ℝ ℝ k)).neg
  · apply ContDiff.div_const
    exact ContDiff.sum fun k _ => ContDiff.sum fun j _ => contDiff_const.mul
      (Real.contDiff_cos.comp ((contDiff_apply ℝ ℝ k).sub (contDiff_apply ℝ ℝ j)))

@[powerlib_foundation] theorem energy_contDiff (p : Params n) : ContDiff ℝ 1 (energy p) := by
  unfold energy
  apply ContDiff.add
  · apply ContDiff.div_const
    exact ContDiff.sum fun k _ => contDiff_const.mul ((contDiff_piLp_apply 2).pow 2)
  · exact (potential_contDiff p).comp angleMap.contDiff

/-- The absolute angles move with the frequency differences: `(angleMap ż)ₖ = ωₖ − ω₀`. -/
@[powerlib_foundation] theorem angleMap_reducedField (p : Params n) (z : State (n + (n + 1)))
    (k : Fin (n + 1)) : angleMap (reducedField p z) k = z (wIdx k) - z (wIdx 0) := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [reducedField_dIdx]

/-- The derivative of the energy. -/
def energyGrad (p : Params n) (z : State (n + (n + 1))) : State (n + (n + 1)) →L[ℝ] ℝ :=
  (∑ k, (p.M k * z (wIdx k)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + (n + 1)) => ℝ) (wIdx k)) +
    (potentialGrad p (angleMap z)).comp angleMap

@[powerlib_foundation] theorem energyGrad_apply (p : Params n) (z v : State (n + (n + 1))) :
    energyGrad p z v = ∑ k, p.M k * z (wIdx k) * v (wIdx k) +
      ∑ k, (powerInjection p.B (angleMap z) k - p.P k) * angleMap v k := by
  simp [energyGrad, potentialGrad_apply]

@[powerlib_foundation] theorem hasFDerivAt_energy (p : Params n) (z : State (n + (n + 1))) :
    HasFDerivAt (energy p) (energyGrad p z) z := by
  have hkin : HasFDerivAt (fun y : State (n + (n + 1)) => (∑ k, p.M k * y (wIdx k) ^ 2) / 2)
      (∑ k, (p.M k * z (wIdx k)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + (n + 1)) => ℝ)
        (wIdx k)) z := by
    have hs : HasFDerivAt (fun y : State (n + (n + 1)) => ∑ k, p.M k * y (wIdx k) ^ 2)
        (∑ k, (2 * (p.M k * z (wIdx k))) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + (n + 1)) => ℝ)
          (wIdx k)) z := by
      refine HasFDerivAt.fun_sum fun k _ => ?_
      have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z (wIdx k)
      have h2 := (h1.mul h1).const_mul (p.M k)
      convert h2 using 1
      · funext y; simp only [Pi.mul_apply]; ring
      · ext v
        simp [smul_eq_mul]
        ring
    convert hs.const_mul (1 / 2 : ℝ) using 1
    · funext y; ring
    · ext v
      simp [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
  exact hkin.add ((hasFDerivAt_potential p (angleMap z)).comp z angleMap.hasFDerivAt)

/-- **Energy balance.** Along the reduced swing field the energy changes at the rate
`−∑ₖ Dₖ ωₖ² + ω₀ ∑ₖ Pₖ`; at a power-balance point `∑ₖ Pₖ = 0`, so the energy dissipates. -/
@[powerlib_foundation] theorem lie_energy (p : Params n) (z : State (n + (n + 1))) :
    fderiv ℝ (energy p) z (reducedField p z) =
      -(∑ k, p.D k * z (wIdx k) ^ 2) + z (wIdx 0) * ∑ k, p.P k := by
  rw [(hasFDerivAt_energy p z).fderiv, energyGrad_apply]
  simp only [reducedField_wIdx, angleMap_reducedField]
  have hPI := sum_powerInjection p (angleMap z)
  have key : ∀ k, p.M k * z (wIdx k) * ((p.P k - p.D k * z (wIdx k) -
      powerInjection p.B (angleMap z) k) / p.M k) +
      (powerInjection p.B (angleMap z) k - p.P k) * (z (wIdx k) - z (wIdx 0)) =
      -(p.D k * z (wIdx k) ^ 2) - (powerInjection p.B (angleMap z) k - p.P k) * z (wIdx 0) := by
    intro k
    field_simp [(p.M_pos k).ne']
    ring
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun k _ => key k, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hPI]
  ring

/-! ## Angle-only displacements and the potential difference -/

/-- The reduced state with relative angles `v` and zero frequencies. -/
def angleState (v : Fin n → ℝ) : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ) v (fun _ => 0) r

@[simp, powerlib_foundation] theorem angleState_dIdx (v : Fin n → ℝ) (i : Fin n) :
    angleState v (dIdx i) = v i := by
  simp [angleState]

@[simp, powerlib_foundation] theorem angleState_wIdx (v : Fin n → ℝ) (k : Fin (n + 1)) :
    angleState v (wIdx k) = 0 := by
  simp [angleState]

/-- Absolute angle displacement of relative angles `v` (reference angle `0`). -/
def ground (v : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons 0 v

@[simp, powerlib_foundation] theorem ground_zero (v : Fin n → ℝ) : ground v 0 = 0 := rfl

@[simp, powerlib_foundation] theorem ground_succ (v : Fin n → ℝ) (i : Fin n) :
    ground v i.succ = v i := rfl

@[powerlib_foundation] theorem ground_smul (c : ℝ) (v : Fin n → ℝ) :
    ground (c • v) = c • ground v := by
  funext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp

@[powerlib_foundation] theorem ground_zero_vec : ground (0 : Fin n → ℝ) = 0 := by
  funext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp

@[powerlib_foundation] theorem angleMap_angleState (v : Fin n → ℝ) :
    angleMap (angleState v) = ground v := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

@[powerlib_foundation] theorem angleState_smul (c : ℝ) (v : Fin n → ℝ) :
    angleState (c • v) = c • angleState v := by
  apply state_ext <;> intro _ <;> simp

@[powerlib_foundation] theorem angleState_eq_zero_iff (v : Fin n → ℝ) :
    angleState v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrArg (fun y : State (n + (n + 1)) => y (dIdx i)) h
    simpa using this
  · rintro rfl
    apply state_ext <;> intro _ <;> simp

@[powerlib_foundation] theorem angleMap_equilibrium (θ : Fin (n + 1) → ℝ) :
    angleMap (equilibrium θ) = fun k => θ k + -θ 0 := by
  rw [equilibrium, angleMap_reduce]

@[powerlib_foundation] theorem equilibrium_wIdx (θ : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    equilibrium θ (wIdx k) = 0 := by
  simp [equilibrium]

@[powerlib_foundation] theorem potential_add_const (p : Params n) (θ : Fin (n + 1) → ℝ) (c : ℝ) :
    potential p (fun k => θ k + c) = potential p θ - c * ∑ k, p.P k := by
  simp only [potential, add_sub_add_right_eq_sub]
  rw [show ∑ k, p.P k * (θ k + c) = ∑ k, p.P k * θ k + c * ∑ k, p.P k by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring]
  ring

/-- Total power vanishes at a power-balance point. -/
@[powerlib_foundation] theorem sum_P_of_balance {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) : ∑ k, p.P k = 0 := by
  rw [Finset.sum_congr rfl fun k _ => hbal k, sum_powerInjection]

/-- The energy at an angle-only displacement of the selected point is the potential there. -/
@[powerlib_foundation] theorem energy_equilibrium_add_angleState {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k) (v : Fin n → ℝ) :
    energy p (equilibrium θ + angleState v) = potential p (θ + ground v) := by
  have hz : ∀ k, (equilibrium θ + angleState v) (wIdx k) = 0 := fun k => by
    simp [equilibrium_wIdx]
  have ha : angleMap (equilibrium θ + angleState v) = fun k => (θ + ground v) k + -θ 0 := by
    rw [map_add, angleMap_equilibrium, angleMap_angleState]
    funext k
    simp only [Pi.add_apply]
    ring
  rw [energy, ha, potential_add_const, sum_P_of_balance hbal]
  simp [hz]

@[powerlib_foundation] theorem energy_equilibrium {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k) :
    energy p (equilibrium θ) = potential p θ := by
  have := energy_equilibrium_add_angleState hbal (0 : Fin n → ℝ)
  have h0 : angleState (0 : Fin n → ℝ) = 0 := (angleState_eq_zero_iff 0).mpr rfl
  rwa [h0, add_zero, ground_zero_vec, add_zero] at this

/-- The energy does not increase along the reduced field at a power-balance point. -/
@[powerlib_foundation] theorem lie_energy_nonpos {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) (z : State (n + (n + 1))) :
    fderiv ℝ (energy p) z (reducedField p z) ≤ 0 := by
  rw [lie_energy, sum_P_of_balance hbal, mul_zero, add_zero, neg_nonpos]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (p.D_pos k).le (sq_nonneg _)

/-! ## The reduced field as a damped mechanical system -/

@[powerlib_foundation] theorem angleMap_eq_ground (w : State (n + (n + 1))) :
    angleMap w = ground fun i => w (dIdx i) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

@[powerlib_foundation] theorem norm_le_of_dIdx (w : State (n + (n + 1))) :
    ‖(fun i => w (dIdx i) : Fin n → ℝ)‖ ≤ ‖w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun i => PiLp.norm_apply_le w (dIdx i)

/-- `ground` as a continuous linear map. -/
def groundCLM : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := ground
      map_add' := fun v w => by
        funext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp
      map_smul' := fun c v => by
        funext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp }

@[simp, powerlib_foundation] theorem groundCLM_apply (v : Fin n → ℝ) : groundCLM v = ground v :=
  rfl

/-- The relative angle rates `ωᵢ₊₁ − ω₀` of the frequency deviations. -/
def relRate : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.succ -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0

@[simp, powerlib_foundation] theorem relRate_apply (w : Fin (n + 1) → ℝ) (i : Fin n) :
    relRate w i = w i.succ - w 0 := by
  simp [relRate]

/-- The relative angles `θᵢ₊₁ − θ₀` of an angle profile. -/
def relAngles (θ : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => θ i.succ - θ 0

@[powerlib_foundation] theorem ground_relAngles_add (θ : Fin (n + 1) → ℝ) (v : Fin n → ℝ) :
    ground (relAngles θ + v) = fun k => (θ + ground v) k + -θ 0 := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp only [ground_succ, Pi.add_apply, relAngles]
    ring

/-- The selected point is the rest point at the relative angles of the profile. -/
@[powerlib_foundation] theorem equilibrium_eq_point (θ : Fin (n + 1) → ℝ) :
    equilibrium θ = Dynamics.Mechanical.point (relAngles θ) := by
  apply state_ext
  · intro i
    rw [Dynamics.Mechanical.point_qIdx]
    simp [equilibrium, relAngles]
  · intro k
    rw [Dynamics.Mechanical.point_vIdx]
    simp [equilibrium]

/-- At a power-balance point the potential in relative angles, about the relative angles of
`θ`, is the network potential of the displaced profile. -/
@[powerlib_foundation] theorem potential_ground_relAngles_add {p : Params n}
    (hP : ∑ k, p.P k = 0) (θ : Fin (n + 1) → ℝ) (v : Fin n → ℝ) :
    potential p (ground (relAngles θ + v)) = potential p (θ + ground v) := by
  rw [ground_relAngles_add, potential_add_const, hP, mul_zero, sub_zero]

@[powerlib_foundation] theorem potential_ground_relAngles {p : Params n}
    (hP : ∑ k, p.P k = 0) (θ : Fin (n + 1) → ℝ) :
    potential p (ground (relAngles θ)) = potential p θ := by
  simpa [ground_zero_vec] using potential_ground_relAngles_add hP θ 0

@[powerlib_foundation] theorem hasFDerivAt_potential_comp_ground (p : Params n)
    (q : Fin n → ℝ) :
    HasFDerivAt (fun q => potential p (ground q))
      ((potentialGrad p (ground q)).comp groundCLM) q :=
  (hasFDerivAt_potential p (groundCLM q)).comp q groundCLM.hasFDerivAt

@[powerlib_foundation] theorem potential_comp_ground_contDiff (p : Params n) :
    ContDiff ℝ 2 (fun q : Fin n → ℝ => potential p (ground q)) :=
  (potential_contDiff p).comp groundCLM.contDiff

/-- The generalized force of the potential in relative angles: at a network with zero total
power, `dU(q)(relRate w) = ∑ₖ (Pₖ(θ) − Pₖ) wₖ` with `θ = ground q`. -/
@[powerlib_foundation] theorem fderiv_potential_comp_ground_relRate {p : Params n}
    (hP : ∑ k, p.P k = 0) (q : Fin n → ℝ) (w : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun q => potential p (ground q)) q (relRate w) =
      ∑ k, (powerInjection p.B (ground q) k - p.P k) * w k := by
  rw [(hasFDerivAt_potential_comp_ground p q).fderiv, ContinuousLinearMap.comp_apply,
    groundCLM_apply, potentialGrad_apply]
  have hg : ground (relRate w) = fun k => w k - w 0 := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hs : ∑ k, (powerInjection p.B (ground q) k - p.P k) = 0 := by
    rw [Finset.sum_sub_distrib, sum_powerInjection, hP, sub_zero]
  rw [hg]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, zero_mul, sub_zero]

/-- **The reduced swing field of a network with zero total power is a damped mechanical system**
(`Dynamics.Mechanical.field`): positions the relative angles, velocities the frequency deviations,
`relRate` the velocity-to-position map, inertias as masses, dampings, and the network potential
in relative angles `q ↦ U(ground q)`. Static identity: the dynamics results of
`theorem/Dynamics/Mechanical.lean` apply to the swing network at every power-balance point. -/
@[powerlib_foundation] theorem reducedField_eq_mechanical {p : Params n}
    (hP : ∑ k, p.P k = 0) :
    reducedField p =
      Dynamics.Mechanical.field relRate p.M p.D (fun q => potential p (ground q)) := by
  funext z
  have hpos : Dynamics.Mechanical.pos z = fun i => z (dIdx i) := by
    ext i
    simp
  apply state_ext
  · intro i
    rw [reducedField_dIdx, Dynamics.Mechanical.field_qIdx]
    simp
  · intro k
    rw [reducedField_wIdx, Dynamics.Mechanical.field_vIdx, fderiv_potential_comp_ground_relRate hP,
      angleMap_eq_ground, hpos]
    have hsum : ∑ l, (powerInjection p.B (ground fun i => z (dIdx i)) l - p.P l) *
        (Pi.single k (1 : ℝ) : Fin (n + 1) → ℝ) l =
          powerInjection p.B (ground fun i => z (dIdx i)) k - p.P k := by
      simp [Pi.single_apply]
    rw [hsum]
    ring

/-- At a network with zero total power, the critical points of the potential in relative angles
along the reachable directions are the power-balance points. -/
@[powerlib_foundation] theorem critical_iff_balance {p : Params n} (hP : ∑ k, p.P k = 0)
    (θ : Fin (n + 1) → ℝ) (v : Fin n → ℝ) :
    (fderiv ℝ (fun q => potential p (ground q)) (relAngles θ + v)).comp relRate = 0 ↔
      ∀ k, p.P k = powerInjection p.B (θ + ground v) k := by
  have hinj : ∀ k, powerInjection p.B (ground (relAngles θ + v)) k =
      powerInjection p.B (θ + ground v) k := by
    intro k
    rw [ground_relAngles_add, powerInjection_add_const]
  constructor
  · intro h k
    have := congrArg (fun T : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => T (Pi.single k 1)) h
    simp only [ContinuousLinearMap.comp_apply, fderiv_potential_comp_ground_relRate hP, hinj,
      _root_.zero_apply] at this
    simp [Pi.single_apply] at this
    linarith
  · intro h
    ext w
    simp only [ContinuousLinearMap.comp_apply, fderiv_potential_comp_ground_relRate hP, hinj,
      _root_.zero_apply]
    simp [← h]

@[powerlib_foundation] theorem critical_iff_balance_zero {p : Params n} (hP : ∑ k, p.P k = 0)
    (θ : Fin (n + 1) → ℝ) :
    (fderiv ℝ (fun q => potential p (ground q)) (relAngles θ)).comp relRate = 0 ↔
      ∀ k, p.P k = powerInjection p.B θ k := by
  simpa [ground_zero_vec] using critical_iff_balance hP θ 0

/-! ## Necessary conditions for local asymptotic stability -/

private theorem mem_den_flow_iff' {m : Model n} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (reducedField m.params) (equilibrium m.θ) :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model n => reducedField m.params)
    (pt := fun m => equilibrium m.θ) family_isAutonomous

/-- A Lyapunov stable selected point of the `C¹` reduced field is an equilibrium, hence a
power-balance point. -/
private theorem powerFlow_of_lyapunovStable {p : Params n} {θ : Fin (n + 1) → ℝ}
    (h : LyapunovStable (reducedField p) (equilibrium θ)) :
    ∀ k, p.P k = powerInjection p.B θ k :=
  powerFlow_of_equilibrium (Dynamics.isEquilibrium_of_lyapunovStable (reducedField_contDiff p) h)

/-- Implementation evidence: `Dynamics.Mechanical.not_localAsymptoticStable_of_potential_lt` on the
reduced field (`reducedField_eq_mechanical`). At a power-balance point, relative-angle
displacements arbitrarily close to it with a lower potential rule out local asymptotic
stability. -/
private theorem reducedSwing_not_localAsymptoticStable_of_potential_lt {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hseed : ∀ ε > 0, ∃ v : Fin n → ℝ, ‖angleState v‖ < ε ∧
      potential p (θ + ground v) < potential p θ) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  have hP := sum_P_of_balance hbal
  rw [reducedField_eq_mechanical hP, equilibrium_eq_point]
  refine Dynamics.Mechanical.not_localAsymptoticStable_of_potential_lt
    (potential_comp_ground_contDiff p) (fun j => (p.M_pos j).ne') (fun j => (p.D_pos j).le)
    fun ε hε => ?_
  obtain ⟨v, hv, hlt⟩ := hseed ε hε
  refine ⟨v, lt_of_le_of_lt ?_ hv, ?_⟩
  · simpa using norm_le_of_dIdx (angleState v)
  · rwa [potential_ground_relAngles_add hP, potential_ground_relAngles hP]

/-- Implementation evidence: `Dynamics.Mechanical.not_localAsymptoticStable_of_critical_line` on the
reduced field. If the network stays power balanced along the relative-angle displacements `t • v`
(`v ≠ 0`), every point of that line is an equilibrium. -/
private theorem reducedSwing_not_localAsymptoticStable_of_balance_line {p : Params n}
    {θ : Fin (n + 1) → ℝ} {v : Fin n → ℝ} (hv : v ≠ 0)
    (hline : ∀ t : ℝ, ∀ k, p.P k = powerInjection p.B (θ + ground (t • v)) k) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  have hP : ∑ k, p.P k = 0 := sum_P_of_balance (hline 0)
  rw [reducedField_eq_mechanical hP, equilibrium_eq_point]
  exact Dynamics.Mechanical.not_localAsymptoticStable_of_critical_line hv fun t =>
    (critical_iff_balance hP θ (t • v)).mpr (hline t)

/-! ## Taylor expansion of the potential at a power-balance point -/

/-- Edge increment of the potential, `g(φ, x) = cos φ − cos(φ + x) − x sin φ`. Multiplied by the
line coupling `B` it is the line potential `CycleMinimum.edgeG (B cos φ) (B sin φ) x` of
`theorem/Network/Swing/CycleMinimum.lean`. -/
def edgeIncrement (φ x : ℝ) : ℝ := Real.cos φ - Real.cos (φ + x) - x * Real.sin φ

/-- **Edge form of the potential.** At a power-balance point
`U(θ + u) − U(θ) = ½ ∑ₖ ∑ⱼ Bₖⱼ g(θₖ − θⱼ, uₖ − uⱼ)`. -/
@[powerlib_foundation] theorem potential_add_sub {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) (u : Fin (n + 1) → ℝ) :
    potential p (θ + u) - potential p θ =
      (∑ k, ∑ j, p.B k j * edgeIncrement (θ k - θ j) (u k - u j)) / 2 := by
  have hPu : ∑ k, p.P k * u k = (∑ k, ∑ j, p.B k j * Real.sin (θ k - θ j) * (u k - u j)) / 2 := by
    rw [sum_sin_mul_sub]
    simp only [hbal]
    ring
  have hlin : ∑ k, p.P k * (θ + u) k = ∑ k, p.P k * θ k + ∑ k, p.P k * u k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [Pi.add_apply]; ring
  have hcos : ∑ k, ∑ j, p.B k j * Real.cos ((θ + u) k - (θ + u) j) =
      ∑ k, ∑ j, p.B k j * Real.cos (θ k - θ j + (u k - u j)) :=
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by
      simp only [Pi.add_apply]; ring_nf
  have hsplit : ∑ k, ∑ j, p.B k j * edgeIncrement (θ k - θ j) (u k - u j) =
      ∑ k, ∑ j, p.B k j * Real.cos (θ k - θ j) -
        ∑ k, ∑ j, p.B k j * Real.cos (θ k - θ j + (u k - u j)) -
        ∑ k, ∑ j, p.B k j * Real.sin (θ k - θ j) * (u k - u j) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by
      simp only [edgeIncrement]; ring
  simp only [potential]
  rw [hlin, hcos, hsplit, hPu]
  ring

/-- Second-order coefficient `A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)²` (twice the Hessian form). -/
def hessForm (p : Params n) (θ u : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, ∑ j, p.B k j * Real.cos (θ k - θ j) * (u k - u j) ^ 2

/-- Third-order coefficient `A₃(u) = ∑ₖ ∑ⱼ Bₖⱼ sin(θₖ − θⱼ)(uₖ − uⱼ)³`. -/
def cubicForm (p : Params n) (θ u : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, ∑ j, p.B k j * Real.sin (θ k - θ j) * (u k - u j) ^ 3

@[powerlib_foundation] theorem edgeIncrement_taylor (φ x : ℝ) (hx : |x| ≤ 1) :
    |edgeIncrement φ x - (Real.cos φ * x ^ 2 / 2 - Real.sin φ * x ^ 3 / 6)| ≤ x ^ 4 / 8 := by
  have hc := Real.cos_bound hx
  have hs := Real.sin_bound hx
  have he : edgeIncrement φ x - (Real.cos φ * x ^ 2 / 2 - Real.sin φ * x ^ 3 / 6) =
      -Real.cos φ * (Real.cos x - (1 - x ^ 2 / 2)) +
        Real.sin φ * (Real.sin x - (x - x ^ 3 / 6)) := by
    simp only [edgeIncrement, Real.cos_add]; ring
  rw [he]
  have h4 : |x| ^ 4 = x ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  have h5 : |x| ^ 5 ≤ x ^ 4 := by
    rw [← h4, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hx
  calc |-Real.cos φ * (Real.cos x - (1 - x ^ 2 / 2)) +
        Real.sin φ * (Real.sin x - (x - x ^ 3 / 6))|
      ≤ |Real.cos φ| * |Real.cos x - (1 - x ^ 2 / 2)| +
          |Real.sin φ| * |Real.sin x - (x - x ^ 3 / 6)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_neg]
    _ ≤ 1 * (|x| ^ 4 * (5 / 96)) + 1 * (|x| ^ 5 / 100) := by
        gcongr
        · exact Real.abs_cos_le_one φ
        · exact Real.abs_sin_le_one φ
    _ ≤ x ^ 4 / 8 := by rw [h4]; nlinarith [sq_nonneg (x ^ 2)]

/-- A real cubic-quartic sign lemma: a negative quadratic coefficient, or a vanishing quadratic and
nonzero cubic coefficient, makes `t² a/2 − t³ b/6 + t⁴ C` negative at arbitrarily small `t ≠ 0`. -/
@[powerlib_foundation] theorem exists_small_quartic_neg {a b C : ℝ} (hC : 0 ≤ C)
    (h : a < 0 ∨ (a = 0 ∧ b ≠ 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, t ≠ 0 ∧ |t| < ε ∧ t ^ 2 * a / 2 - t ^ 3 * b / 6 + t ^ 4 * C < 0 := by
  rcases h with ha | ⟨rfl, hb⟩
  · set t := min (ε / 2) (min 1 (-a / (4 * (|b| + C + 1)))) with htdef
    have hden : 0 < 4 * (|b| + C + 1) := by positivity
    have ht0 : 0 < t := lt_min (by linarith) (lt_min one_pos (div_pos (by linarith) hden))
    have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have ht2 : t * (4 * (|b| + C + 1)) ≤ -a := by
      have h' : t ≤ -a / (4 * (|b| + C + 1)) := by
        rw [htdef]; exact (min_le_right _ _).trans (min_le_right _ _)
      rwa [le_div_iff₀ hden] at h'
    refine ⟨t, ht0.ne', ?_, ?_⟩
    · rw [abs_of_pos ht0]; exact (min_le_left _ _).trans_lt (by linarith)
    · have hb : -(t ^ 3 * b / 6) ≤ t ^ 3 * |b| := by
        have h3 : 0 ≤ t ^ 3 := by positivity
        have h1 : -b ≤ |b| := neg_le_abs b
        have h2 : t ^ 3 * (-b) ≤ t ^ 3 * |b| := mul_le_mul_of_nonneg_left h1 h3
        have h4 : 0 ≤ t ^ 3 * |b| := mul_nonneg h3 (abs_nonneg b)
        linarith
      have hC4 : t ^ 4 * C ≤ t ^ 3 * C := by
        have : t ^ 4 ≤ t ^ 3 := by
          rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) ht1
        exact mul_le_mul_of_nonneg_right this hC
      have hkey : t ^ 3 * (|b| + C) ≤ t ^ 2 * (-a) / 4 := by
        have h2 : 0 ≤ t ^ 2 := by positivity
        have : t * (|b| + C) ≤ -a / 4 := by nlinarith [abs_nonneg b]
        calc t ^ 3 * (|b| + C) = t ^ 2 * (t * (|b| + C)) := by ring
          _ ≤ t ^ 2 * (-a / 4) := mul_le_mul_of_nonneg_left this h2
          _ = t ^ 2 * (-a) / 4 := by ring
      have hneg : t ^ 2 * a < 0 := mul_neg_of_pos_of_neg (by positivity) ha
      nlinarith
  · set τ := min (ε / 2) (|b| / (12 * (C + 1))) with hτdef
    have hbpos : 0 < |b| := abs_pos.mpr hb
    have hτ0 : 0 < τ := lt_min (by linarith) (by positivity)
    have hτC : τ * C < |b| / 12 := by
      have h1 : τ ≤ |b| / (12 * (C + 1)) := min_le_right _ _
      have h2 : τ * (12 * (C + 1)) ≤ |b| := by rwa [le_div_iff₀ (by positivity)] at h1
      nlinarith
    set σ : ℝ := if 0 < b then 1 else -1 with hσ
    have hσb : σ * b = |b| := by
      rw [hσ]; split_ifs with h
      · rw [abs_of_pos h]; ring
      · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hb)]; ring
    have hσ2 : σ ^ 2 = 1 := by rw [hσ]; split_ifs <;> norm_num
    refine ⟨σ * τ, ?_, ?_, ?_⟩
    · have : σ ≠ 0 := by rw [hσ]; split_ifs <;> norm_num
      exact mul_ne_zero this hτ0.ne'
    · rw [abs_mul, abs_of_pos hτ0]
      have : |σ| = 1 := by rw [hσ]; split_ifs <;> norm_num
      rw [this, one_mul]; exact (min_le_left _ _).trans_lt (by linarith)
    · have e : (σ * τ) ^ 2 * 0 / 2 - (σ * τ) ^ 3 * b / 6 + (σ * τ) ^ 4 * C =
          τ ^ 3 * (τ * C - |b| / 6) := by
        rw [← hσb]
        have : (σ * τ) ^ 4 = τ ^ 4 := by rw [mul_pow, show σ ^ 4 = (σ ^ 2) ^ 2 by ring, hσ2]; ring
        rw [this]
        have : (σ * τ) ^ 3 * b = τ ^ 3 * (σ * b) * σ ^ 2 := by ring
        rw [this, hσ2]
        ring
      rw [e]
      apply mul_neg_of_pos_of_neg (by positivity)
      linarith

/-- **Taylor seeds below the potential.** At a power-balance point, a direction `u` with
`A₂(u) < 0`, or with `A₂(u) = 0` and `A₃(u) ≠ 0`, gives points `θ + t u` with arbitrarily small
`t ≠ 0` and a lower potential. -/
@[powerlib_foundation] theorem exists_potential_lt {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) (u : Fin (n + 1) → ℝ)
    (h : hessForm p θ u < 0 ∨ (hessForm p θ u = 0 ∧ cubicForm p θ u ≠ 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, t ≠ 0 ∧ |t| < ε ∧ potential p (θ + t • u) < potential p θ := by
  set M : ℝ := ∑ k, ∑ j, |u k - u j| + 1 with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ k, ∑ j, |u k - u j| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hxM : ∀ k j, |u k - u j| ≤ M := fun k j => by
    have h1 : |u k - u j| ≤ ∑ j', |u k - u j'| :=
      Finset.single_le_sum (f := fun j' => |u k - u j'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j', |u k - u j'| ≤ ∑ k', ∑ j', |u k' - u j'| :=
      Finset.single_le_sum (f := fun k' => ∑ j', |u k' - u j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    linarith
  set C : ℝ := ∑ k, ∑ j, p.B k j * (u k - u j) ^ 4 / 8 with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (mul_nonneg (p.B_nonneg k j) (by positivity)) (by norm_num)
  obtain ⟨t, ht0, htε, hneg⟩ := exists_small_quartic_neg hC h
    (lt_min hε (one_div_pos.mpr (by linarith : (0 : ℝ) < M)))
  refine ⟨t, ht0, htε.trans_le (min_le_left _ _), ?_⟩
  have htM : |t| * M ≤ 1 := by
    have := htε.le.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by linarith)] at this
  rw [← sub_neg, potential_add_sub hbal]
  have hterm : ∀ k j, p.B k j * edgeIncrement (θ k - θ j) ((t • u) k - (t • u) j) ≤
      p.B k j * (Real.cos (θ k - θ j) * (t * (u k - u j)) ^ 2 / 2 -
        Real.sin (θ k - θ j) * (t * (u k - u j)) ^ 3 / 6) +
      p.B k j * (t * (u k - u j)) ^ 4 / 8 := by
    intro k j
    have hx : |t * (u k - u j)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hxM k j) (abs_nonneg t)).trans htM
    have hT := edgeIncrement_taylor (θ k - θ j) _ hx
    have he : (t • u) k - (t • u) j = t * (u k - u j) := by simp [mul_sub]
    rw [he]
    have := (abs_le.mp hT).2
    have hB := p.B_nonneg k j
    nlinarith
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm k j
  have hval : ∑ k, ∑ j, (p.B k j * (Real.cos (θ k - θ j) * (t * (u k - u j)) ^ 2 / 2 -
        Real.sin (θ k - θ j) * (t * (u k - u j)) ^ 3 / 6) +
      p.B k j * (t * (u k - u j)) ^ 4 / 8) =
      t ^ 2 * hessForm p θ u / 2 - t ^ 3 * cubicForm p θ u / 6 + t ^ 4 * C := by
    simp only [hessForm, cubicForm, hCdef, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hval] at hsum
  linarith


/-! ## A Hurwitz test with signed linearization weights -/

@[powerlib_foundation] theorem hessForm_add_const (p : Params n) (θ u : Fin (n + 1) → ℝ) (c : ℝ) :
    hessForm p θ (fun k => u k + c) = hessForm p θ u := by
  simp [hessForm]

@[powerlib_foundation] theorem hessForm_nonneg_of_pos {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hpos : ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm p θ u)
    (v : Fin (n + 1) → ℝ) : 0 ≤ hessForm p θ v := by
  rw [← hessForm_add_const p θ v (-v 0)]
  by_cases h : (fun k => v k + -v 0) = 0
  · rw [h]; simp [hessForm]
  · exact (hpos _ (by simp) h).le

@[powerlib_foundation] theorem eq_zero_of_hessForm_eq_zero {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hpos : ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm p θ u)
    {v : Fin (n + 1) → ℝ} (h0 : v 0 = 0) (h : hessForm p θ v = 0) : v = 0 := by
  by_contra hne
  exact (hpos v h0 hne).ne' h

@[powerlib_foundation] theorem sum_normSq_eq_hessForm (p : Params n) (θ : Fin (n + 1) → ℝ)
    (u : Fin (n + 1) → ℂ) :
    ∑ i, ∑ j, flowWeights p.B θ i j * Complex.normSq (u i - u j) =
      hessForm p θ (fun k => (u k).re) + hessForm p θ (fun k => (u k).im) := by
  simp only [hessForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [flowWeights, of_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- **Hurwitz test by the Hessian form.** The reduced swing Jacobian is Hurwitz whenever the form
`A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)²` is positive on every nonzero `u` with `u₀ = 0`
(positive inertia and damping; signed linearization weights are allowed). -/
@[powerlib_foundation] theorem jacobian_isHurwitz_of_hessForm (p : Params n) (θ : Fin (n + 1) → ℝ)
    (hpos : ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm p θ u) :
    LinearSystems.IsHurwitz (jacobian p θ) := by
  intro μ v hv heig
  simp only [neg_zero]
  have hWs := flowWeights_symm p θ
  let η : Fin n → ℂ := fun i => v (dIdx i)
  let w : Fin (n + 1) → ℂ := fun k => v (wIdx k)
  let ζ : Fin (n + 1) → ℂ := Fin.cons 0 η
  have hrow : ∀ r, ∑ c, ((jacobian p θ r c : ℝ) : ℂ) * v c = μ * v r := by
    intro r
    have := congrFun heig r
    simpa [mulVec, dotProduct] using this
  have h1 : ∀ i, w i.succ - w 0 = μ * η i := by
    intro i
    have := hrow (dIdx i)
    rw [sum_state] at this
    simp only [jacobian_dd, jacobian_dw, Complex.ofReal_sub, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, zero_add, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one,
      sub_mul, ite_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    exact this
  have hζ0 : ζ 0 = 0 := rfl
  have hζs : ∀ i, ζ i.succ = η i := fun i => rfl
  have h2 : ∀ k, μ * p.M k * w k + p.D k * w k +
      ∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l) = 0 := by
    intro k
    have := hrow (wIdx k)
    rw [sum_state] at this
    simp only [jacobian_wd, jacobian_ww] at this
    have e1 : ∑ l, ((laplacian (flowWeights p.B θ) k l : ℝ) : ℂ) * ζ l =
        ∑ i : Fin n, ((laplacian (flowWeights p.B θ) k i.succ : ℝ) : ℂ) * η i := by
      rw [Fin.sum_univ_succ, hζ0, mul_zero, zero_add]
      rfl
    have hL : ∑ i : Fin n, ((-(laplacian (flowWeights p.B θ) k i.succ) / p.M k : ℝ) : ℂ) *
        v (dIdx i) = -(∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l)) / p.M k := by
      rw [← complex_laplacian_sum, e1, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [hL] at this
    have hD : ∑ k' : Fin (n + 1), (((if k = k' then -(p.D k / p.M k) else 0 : ℝ)) : ℂ) *
        v (wIdx k') = -(p.D k / p.M k) * w k := by
      rw [Finset.sum_eq_single k]
      · simp [w]
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    rw [hD] at this
    have hM : (p.M k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (p.M_pos k).ne'
    have h' : -(∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l)) / p.M k +
        -((p.D k : ℂ) / p.M k) * w k = μ * w k := by
      push_cast at this; exact this
    field_simp at h'
    linear_combination (-1 : ℂ) * h'
  have hv0 : ∀ (hη : η = 0) (hw : w = 0), False := by
    intro hη hw
    apply hv
    funext r
    refine Fin.addCases (fun i => ?_) (fun k => ?_) r
    · exact congrFun hη i
    · exact congrFun hw k
  by_cases hμ : μ = 0
  · exfalso
    subst hμ
    have hwconst : ∀ k, w k = w 0 := by
      intro k
      refine Fin.cases rfl (fun i => ?_) k
      have := h1 i
      rw [zero_mul, sub_eq_zero] at this
      exact this
    have e : ∀ k, ((p.D k : ℝ) : ℂ) * w 0 = -(∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l)) := by
      intro k
      have := h2 k
      rw [hwconst k] at this
      linear_combination this
    have hsum : ((∑ k, p.D k : ℝ) : ℂ) * w 0 = 0 := by
      push_cast
      rw [Finset.sum_mul, Finset.sum_congr rfl (fun k _ => e k), Finset.sum_neg_distrib,
        complex_laplacian_total hWs, neg_zero]
    have hDpos : (0 : ℝ) < ∑ k, p.D k := Finset.sum_pos (fun k _ => p.D_pos k) Finset.univ_nonempty
    have hw0 : w 0 = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hDpos.ne'
      · exact h
    have hlap : ∀ k, ∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l) = 0 := by
      intro k
      have := e k
      rw [hw0, mul_zero] at this
      linear_combination this
    have hζ : ζ = 0 := by
      have hz := star_dotProduct_laplacian_mulVec hWs ζ
      rw [Finset.sum_eq_zero fun k _ => by rw [hlap k, mul_zero]] at hz
      have hz' : ∑ i, ∑ j, flowWeights p.B θ i j * Complex.normSq (ζ i - ζ j) = 0 := by
        have := congrArg Complex.re hz
        simp only [Complex.zero_re, Complex.ofReal_re] at this
        linarith
      rw [sum_normSq_eq_hessForm] at hz'
      have h1 := hessForm_nonneg_of_pos hpos (fun k => (ζ k).re)
      have h2 := hessForm_nonneg_of_pos hpos (fun k => (ζ k).im)
      have hre := eq_zero_of_hessForm_eq_zero (v := fun k => (ζ k).re) hpos
        (by show (ζ 0).re = 0; rw [hζ0]; rfl) (by linarith)
      have him := eq_zero_of_hessForm_eq_zero (v := fun k => (ζ k).im) hpos
        (by show (ζ 0).im = 0; rw [hζ0]; rfl) (by linarith)
      funext k
      exact Complex.ext (congrFun hre k) (congrFun him k)
    exact hv0 (funext fun i => by rw [← hζs i, hζ]; rfl)
      (funext fun k => by rw [hwconst k, hw0]; rfl)
  · let u : Fin (n + 1) → ℂ := fun k => w k / μ
    have hwk : ∀ k, w k = μ * u k := fun k => by simp only [u]; field_simp
    have hu : ∀ l, ζ l = u l - u 0 := by
      intro l
      refine Fin.cases (by simp [hζ0]) (fun i => ?_) l
      rw [hζs]
      have := h1 i
      rw [hwk, hwk] at this
      apply mul_left_cancel₀ hμ
      linear_combination -this
    have h3 : ∀ k, μ ^ 2 * p.M k * u k + μ * p.D k * u k +
        ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l) = 0 := by
      intro k
      have := h2 k
      simp only [hu, hwk k, sub_sub_sub_cancel_right] at this
      linear_combination this
    have hsum : ∑ k, star (u k) * (μ ^ 2 * p.M k * u k + μ * p.D k * u k +
        ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l)) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [h3 k, mul_zero]
    have hns : ∀ k, star (u k) * u k = (Complex.normSq (u k) : ℂ) := fun k => by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    have hexp : ∑ k, star (u k) * (μ ^ 2 * p.M k * u k + μ * p.D k * u k +
        ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l)) =
        ((∑ k, p.M k * Complex.normSq (u k) : ℝ) : ℂ) * μ ^ 2 +
          ((∑ k, p.D k * Complex.normSq (u k) : ℝ) : ℂ) * μ +
          ∑ k, star (u k) * ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l) := by
      push_cast
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by rw [← hns]; ring
      · exact Finset.sum_congr rfl fun k _ => by rw [← hns]; ring
    rw [hexp, star_dotProduct_laplacian_mulVec hWs] at hsum
    have hune : ∃ k, u k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hv0
      · funext i
        have := h1 i
        rw [hwk, hwk, hall, hall] at this
        simp only [mul_zero, sub_zero] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hμ
      · funext k; rw [hwk, hall]; simp
    obtain ⟨k₀, hk₀⟩ := hune
    have hm : 0 < ∑ k, p.M k * Complex.normSq (u k) :=
      Finset.sum_pos' (fun k _ => mul_nonneg (p.M_pos k).le (Complex.normSq_nonneg _))
        ⟨k₀, Finset.mem_univ _, mul_pos (p.M_pos k₀) (Complex.normSq_pos.mpr hk₀)⟩
    have hd : 0 < ∑ k, p.D k * Complex.normSq (u k) :=
      Finset.sum_pos' (fun k _ => mul_nonneg (p.D_pos k).le (Complex.normSq_nonneg _))
        ⟨k₀, Finset.mem_univ _, mul_pos (p.D_pos k₀) (Complex.normSq_pos.mpr hk₀)⟩
    have hl : 0 ≤ (∑ i, ∑ j, flowWeights p.B θ i j * Complex.normSq (u i - u j)) / 2 := by
      rw [sum_normSq_eq_hessForm]
      exact div_nonneg (add_nonneg (hessForm_nonneg_of_pos hpos _)
        (hessForm_nonneg_of_pos hpos _)) zero_le_two
    exact re_neg_of_quadratic hm hd hl hsum hμ

/-! ## Necessary conditions from the Hessian and cubic forms -/

/-- Implementation evidence for `not_localAsymptoticStable_of_forms`, at the selected point of the
untranslated field. -/
private theorem reducedSwing_not_localAsymptoticStable_of_forms {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k) (v : Fin n → ℝ)
    (h : hessForm p θ (ground v) < 0 ∨
      (hessForm p θ (ground v) = 0 ∧ cubicForm p θ (ground v) ≠ 0)) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  refine reducedSwing_not_localAsymptoticStable_of_potential_lt hbal fun ε hε => ?_
  have hN : 0 < ‖angleState v‖ + 1 := by positivity
  obtain ⟨t, -, ht, hlt⟩ := exists_potential_lt hbal (ground v) h (div_pos hε hN)
  refine ⟨t • v, ?_, by rwa [ground_smul]⟩
  rw [angleState_smul, norm_smul, Real.norm_eq_abs]
  calc |t| * ‖angleState v‖ ≤ |t| * (‖angleState v‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
    _ < ε / (‖angleState v‖ + 1) * (‖angleState v‖ + 1) :=
        mul_lt_mul_of_pos_right ht hN
    _ = ε := by field_simp

/-- **Second- and third-order test.** At a power-balance point, a relative-angle direction `v`
with `A₂ < 0`, or with `A₂ = 0` and `A₃ ≠ 0` (a fold), rules out local asymptotic stability:
the model is not in the denotation of the local asymptotic sentence. -/
@[powerlib_domain] theorem not_localAsymptoticStable_of_forms (m : Model n)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) (v : Fin n → ℝ)
    (h : hessForm m.params m.θ (ground v) < 0 ∨
      (hessForm m.params m.θ (ground v) = 0 ∧ cubicForm m.params m.θ (ground v) ≠ 0)) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff']
  exact reducedSwing_not_localAsymptoticStable_of_forms hbal v h

/-- A non-Hurwitz reduced Jacobian leaves a nonzero grounded direction with a nonpositive
Hessian form. -/
@[powerlib_foundation] theorem exists_hessForm_nonpos {p : Params n} {θ : Fin (n + 1) → ℝ}
    (h : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ∃ u : Fin (n + 1) → ℝ, u 0 = 0 ∧ u ≠ 0 ∧ hessForm p θ u ≤ 0 := by
  by_contra hne
  push Not at hne
  exact h (jacobian_isHurwitz_of_hessForm p θ fun u h0 hu => hne u h0 hu)

/-! ## The family: exactness of the local asymptotic translation for small networks -/

/-- **Local asymptotic stability decided by the Hurwitz test, model by model.** If at a
power-balance point a non-Hurwitz reduced Jacobian rules out local asymptotic stability of `m`, then
`m` is locally asymptotically stable exactly when its profile is a power-balance point with a
Hurwitz reduced Jacobian: a Lyapunov stable point of the `C¹` reduced field is an equilibrium,
hence a power-balance point (`powerFlow_of_equilibrium`), and the translation
`{powerFlow, jacobianStable}` is sound (`chain_le_semantics`). -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_guard (m : Model n)
    (h : (∀ k, m.params.P k = powerInjection m.params.B m.θ k) →
      ¬ LinearSystems.IsHurwitz (jacobian m.params m.θ) →
      m ∉ family.den (.flow .locallyAsymptoticallyStable)) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      (∀ k, m.params.P k = powerInjection m.params.B m.θ k) ∧
      LinearSystems.IsHurwitz (jacobian m.params m.θ)) := by
  unfold powerlib.TMIO.Statement
  constructor
  · intro hm
    have hLAS : LocalAsymptoticStable (reducedField m.params) (equilibrium m.θ) :=
      mem_den_flow_iff'.mp hm
    have hp := powerFlow_of_lyapunovStable hLAS.1
    exact ⟨hp, by_contra fun hH => h hp hH hm⟩
  · rintro ⟨hp, hH⟩
    have hsound := chain_le_semantics (n := n)
    unfold powerlib.TMIO.Statement at hsound
    refine Family.chain_le_semantics_iff.mp hsound _ ?_
    rw [TMIO.mem_realize]
    rintro q (rfl | rfl)
    exacts [hp, hH]

/-- **Exactness of the local asymptotic translation from the Hurwitz test.** If for every model a
power-balance point with a non-Hurwitz reduced Jacobian is not locally asymptotically stable, the
local asymptotic translation `{powerFlow, jacobianStable}` of `family (n := n)` is exact
(`mem_den_locallyAsymptoticallyStable_iff_of_guard` at every model). -/
@[powerlib_domain] theorem exact_locallyAsymptoticallyStable_of_guard
    (h : ∀ m : Model n, (∀ k, m.params.P k = powerInjection m.params.B m.θ k) →
      ¬ LinearSystems.IsHurwitz (jacobian m.params m.θ) →
      m ∉ family.den (.flow .locallyAsymptoticallyStable)) :
    connection% ((family (n := n)).Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext m
  have hm := mem_den_locallyAsymptoticallyStable_iff_of_guard m (h m)
  unfold powerlib.TMIO.Statement at hm
  rw [hm, TMIO.mem_realize]
  simp only [family, translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  rfl

/-- Two machines: the forms in the direction of the second machine. -/
private theorem hessForm_two (p : Params 1) (θ w : Fin (1 + 1) → ℝ) (hw : w 0 = 0) :
    hessForm p θ w = 2 * (p.B 0 1 * Real.cos (θ 0 - θ 1)) * w 1 ^ 2 := by
  simp only [hessForm, Fin.sum_univ_succ, Fin.sum_univ_zero, hw]
  simp only [Fin.succ_zero_eq_one, sub_self, zero_sub, add_zero, ne_eq, zero_pow two_ne_zero,
    mul_zero, Fin.isValue]
  rw [p.B_symm 1 0, show θ 1 - θ 0 = -(θ 0 - θ 1) by ring, Real.cos_neg]
  ring

private theorem cubicForm_two (p : Params 1) (θ w : Fin (1 + 1) → ℝ) (hw : w 0 = 0) :
    cubicForm p θ w = -2 * (p.B 0 1 * Real.sin (θ 0 - θ 1)) * w 1 ^ 3 := by
  simp only [cubicForm, Fin.sum_univ_succ, Fin.sum_univ_zero, hw]
  simp only [Fin.succ_zero_eq_one, sub_self, zero_sub, add_zero, ne_eq,
    zero_pow (three_ne_zero), mul_zero, Fin.isValue]
  rw [p.B_symm 1 0, show θ 1 - θ 0 = -(θ 0 - θ 1) by ring, Real.sin_neg]
  ring

private theorem powerInjection_two_of_B (p : Params 1) (hB : p.B 0 1 = 0)
    (θ : Fin (1 + 1) → ℝ) (k : Fin (1 + 1)) : powerInjection p.B θ k = 0 := by
  have hB' : p.B 1 0 = 0 := by rw [p.B_symm]; exact hB
  simp only [powerInjection, Fin.sum_univ_succ, Fin.sum_univ_zero]
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [hB]
  · rw [Subsingleton.elim i 0]; simp [hB']

/-- Implementation evidence for `not_localAsymptoticStable_two`, at the selected point of the
untranslated field. -/
private theorem reducedSwing_not_localAsymptoticStable_two (p : Params 1) (θ : Fin (1 + 1) → ℝ)
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  obtain ⟨u, hu0, hu, hle⟩ := exists_hessForm_nonpos hH
  have hu1 : u 1 ≠ 0 := by
    intro h1
    apply hu
    funext k
    refine Fin.cases hu0 (fun i => ?_) k
    rw [Subsingleton.elim i 0]; exact h1
  set v : Fin 1 → ℝ := fun _ => 1 with hv
  have hg0 : ground v 0 = 0 := rfl
  have hg1 : ground v 1 = 1 := rfl
  rw [hessForm_two p θ u hu0] at hle
  have hW : p.B 0 1 * Real.cos (θ 0 - θ 1) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < 2 * (p.B 0 1 * Real.cos (θ 0 - θ 1)) * u 1 ^ 2 := by positivity
    linarith
  rcases hW.lt_or_eq with hW | hW
  · refine reducedSwing_not_localAsymptoticStable_of_forms hbal v (Or.inl ?_)
    rw [hessForm_two p θ _ hg0, hg1]
    linarith
  · by_cases hB : p.B 0 1 = 0
    · refine reducedSwing_not_localAsymptoticStable_of_balance_line (v := v) (fun h => ?_)
        fun t k => ?_
      · have := congrFun h 0
        simp [hv] at this
      · rw [powerInjection_two_of_B p hB, hbal, powerInjection_two_of_B p hB]
    · have hc : Real.cos (θ 0 - θ 1) = 0 := by
        rcases mul_eq_zero.mp hW with h | h
        · exact absurd h hB
        · exact h
      have hs : Real.sin (θ 0 - θ 1) ≠ 0 := by
        intro hs
        have := Real.sin_sq_add_cos_sq (θ 0 - θ 1)
        rw [hs, hc] at this
        norm_num at this
      refine reducedSwing_not_localAsymptoticStable_of_forms hbal v (Or.inr ⟨?_, ?_⟩)
      · rw [hessForm_two p θ _ hg0, hW]; ring
      · rw [cubicForm_two p θ _ hg0, hg1]
        simp only [one_pow, mul_one]
        exact mul_ne_zero (by norm_num) (mul_ne_zero hB hs)

/-- **Two machines (`n = 1`).** At a power-balance point with a non-Hurwitz reduced Jacobian the
model is not locally asymptotically stable: the line weight `B₀₁ cos(θ₀ − θ₁)` is negative (a
saddle of the potential), or zero with a coupled line (a fold, nonzero cubic term), or the
machines are uncoupled (a continuum of equilibria). -/
@[powerlib_domain] theorem not_localAsymptoticStable_two (m : Model 1)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian m.params m.θ)) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff']
  exact reducedSwing_not_localAsymptoticStable_two m.params m.θ hbal hH

/-- **For two machines the local asymptotic translation is exact.** -/
@[powerlib_domain] theorem exact_locallyAsymptoticallyStable_two :
    connection% ((family (n := 1)).Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact exact_locallyAsymptoticallyStable_of_guard fun m hp hH =>
    not_localAsymptoticStable_two m hp hH

/-! ## Three machines -/

/-- A linear-quadratic function that is nonnegative everywhere has no linear term. -/
@[powerlib_foundation] theorem eq_zero_of_forall_linear_quadratic_nonneg {L Q : ℝ}
    (h : ∀ x : ℝ, 0 ≤ x * L + x ^ 2 * Q) : L = 0 := by
  by_contra hL
  have hpos : 0 < L ^ 2 := by positivity
  set x := -L / (2 * (|Q| + 1)) with hx
  have hd : 0 < 2 * (|Q| + 1) := by positivity
  have h1 := h x
  have e : x * L + x ^ 2 * Q = L ^ 2 * (-(2 * (|Q| + 1)) + Q) / (2 * (|Q| + 1)) ^ 2 := by
    rw [hx]; field_simp
  rw [e] at h1
  have : -(2 * (|Q| + 1)) + Q < 0 := by linarith [le_abs_self Q, abs_nonneg Q]
  have : L ^ 2 * (-(2 * (|Q| + 1)) + Q) / (2 * (|Q| + 1)) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpos this) (by positivity)
  linarith

/-- Three angles summing to zero, exactly one with a negative cosine: `sin · cos` has one strict
sign on all three. -/
@[powerlib_foundation] theorem sin_mul_cos_same_sign {α β γ : ℝ} (hsum : α + β + γ = 0)
    (hα : Real.cos α < 0) (hβ : 0 < Real.cos β) (hγ : 0 < Real.cos γ) :
    (0 < Real.sin α * Real.cos α ∧ 0 < Real.sin β * Real.cos β ∧ 0 < Real.sin γ * Real.cos γ) ∨
      (Real.sin α * Real.cos α < 0 ∧ Real.sin β * Real.cos β < 0 ∧
        Real.sin γ * Real.cos γ < 0) := by
  have hαe : α = -(β + γ) := by linarith
  have hc : Real.cos α = Real.cos β * Real.cos γ - Real.sin β * Real.sin γ := by
    rw [hαe, Real.cos_neg, Real.cos_add]
  have hs : Real.sin α = -(Real.sin β * Real.cos γ + Real.cos β * Real.sin γ) := by
    rw [hαe, Real.sin_neg, Real.sin_add]
  have hprod : 0 < Real.sin β * Real.sin γ := by nlinarith [mul_pos hβ hγ]
  rcases lt_trichotomy (Real.sin β) 0 with hsβ | hsβ | hsβ
  · have hsγ : Real.sin γ < 0 := by
      by_contra h; push Not at h; nlinarith
    right
    refine ⟨?_, mul_neg_of_neg_of_pos hsβ hβ, mul_neg_of_neg_of_pos hsγ hγ⟩
    have h1 : Real.sin β * Real.cos γ < 0 := mul_neg_of_neg_of_pos hsβ hγ
    have h2 : Real.cos β * Real.sin γ < 0 := mul_neg_of_pos_of_neg hβ hsγ
    have h3 : 0 < Real.sin α := by rw [hs]; linarith
    exact mul_neg_of_pos_of_neg h3 hα
  · rw [hsβ, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
  · have hsγ : 0 < Real.sin γ := by
      by_contra h; push Not at h; nlinarith
    left
    refine ⟨?_, mul_pos hsβ hβ, mul_pos hsγ hγ⟩
    have h1 : 0 < Real.sin β * Real.cos γ := mul_pos hsβ hγ
    have h2 : 0 < Real.cos β * Real.sin γ := mul_pos hβ hsγ
    have h3 : Real.sin α < 0 := by rw [hs]; linarith
    exact mul_pos_of_neg_of_neg h3 hα

/-- Two zero-weight lines at a node whose cubic terms cancel: either both are open, or the third
side of the triangle is in antiphase (`cos = −1`). -/
@[powerlib_foundation] theorem node_open_or_antiphase {B₁ B₂ φ₁ φ₂ : ℝ} (hB₁ : 0 ≤ B₁)
    (hB₂ : 0 ≤ B₂) (hc₁ : B₁ * Real.cos φ₁ = 0) (hc₂ : B₂ * Real.cos φ₂ = 0)
    (hs : B₁ * Real.sin φ₁ + B₂ * Real.sin φ₂ = 0) :
    (B₁ = 0 ∧ B₂ = 0) ∨ Real.cos (φ₂ - φ₁) = -1 := by
  have p1 := Real.sin_sq_add_cos_sq φ₁
  have p2 := Real.sin_sq_add_cos_sq φ₂
  rcases hB₁.lt_or_eq with h1 | h1
  · rcases hB₂.lt_or_eq with h2 | h2
    · right
      have hc1 : Real.cos φ₁ = 0 := (mul_eq_zero.mp hc₁).resolve_left h1.ne'
      have hc2 : Real.cos φ₂ = 0 := (mul_eq_zero.mp hc₂).resolve_left h2.ne'
      rw [hc1] at p1; rw [hc2] at p2
      rw [Real.cos_sub, hc1, hc2]
      have e : B₁ * (Real.sin φ₂ * Real.sin φ₁) = -B₂ := by
        have := congrArg (· * Real.sin φ₂) hs
        simp only [zero_mul] at this
        nlinarith
      have hpr : (Real.sin φ₂ * Real.sin φ₁) ^ 2 = 1 := by nlinarith
      have hneg : Real.sin φ₂ * Real.sin φ₁ < 0 := by
        by_contra hge; push Not at hge; nlinarith
      nlinarith
    · subst h2
      have hc1 : Real.cos φ₁ = 0 := (mul_eq_zero.mp hc₁).resolve_left h1.ne'
      exfalso
      have : Real.sin φ₁ = 0 := by
        have := hs; simp only [zero_mul, add_zero] at this
        exact (mul_eq_zero.mp this).resolve_left h1.ne'
      rw [this, hc1] at p1; norm_num at p1
  · subst h1
    left
    refine ⟨rfl, ?_⟩
    simp only [zero_mul, zero_add] at hs
    nlinarith [sq_nonneg B₂]

/-- Power balance is kept along a relative-angle line whenever every coupled pair moves
together. -/
@[powerlib_foundation] theorem balance_line_of_edges {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) (v : Fin n → ℝ)
    (h : ∀ k j, p.B k j = 0 ∨ ground v k = ground v j) :
    ∀ t : ℝ, ∀ k, p.P k = powerInjection p.B (θ + ground (t • v)) k := by
  intro t k
  rw [hbal k]
  unfold powerInjection
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases h k j with h0 | h0
  · rw [h0, zero_mul, zero_mul]
  · rw [ground_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0]
    ring_nf

/-- **Cubic term on a triangle.** A circulation `κ ≠ 0` through three lines with weights
`Bᵢ cos φᵢ` (`B > 0`, angles summing to zero), exactly one of them negative, has a cubic term of
one strict sign: `∑ Bᵢ sin φᵢ xᵢ³ ≠ 0` for `Bᵢ cos φᵢ xᵢ = κ`. -/
@[powerlib_foundation] theorem triangle_cubic_ne_zero {B₁ B₂ B₃ α β γ x₁ x₂ x₃ κ : ℝ}
    (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB₃ : 0 < B₃) (hsum : α + β + γ = 0)
    (h₁ : B₁ * Real.cos α * x₁ = κ) (h₂ : B₂ * Real.cos β * x₂ = κ)
    (h₃ : B₃ * Real.cos γ * x₃ = κ) (hκ : κ ≠ 0)
    (p₁₂ : 0 ≤ B₁ * Real.cos α + B₂ * Real.cos β) (p₂₃ : 0 ≤ B₂ * Real.cos β + B₃ * Real.cos γ)
    (p₁₃ : 0 ≤ B₁ * Real.cos α + B₃ * Real.cos γ)
    (hnot : ¬ (0 < Real.cos α ∧ 0 < Real.cos β ∧ 0 < Real.cos γ)) :
    B₁ * Real.sin α * x₁ ^ 3 + B₂ * Real.sin β * x₂ ^ 3 + B₃ * Real.sin γ * x₃ ^ 3 ≠ 0 := by
  have hc₁ : Real.cos α ≠ 0 := fun h => hκ (by rw [← h₁, h, mul_zero, zero_mul])
  have hc₂ : Real.cos β ≠ 0 := fun h => hκ (by rw [← h₂, h, mul_zero, zero_mul])
  have hc₃ : Real.cos γ ≠ 0 := fun h => hκ (by rw [← h₃, h, mul_zero, zero_mul])
  -- each term is `κ³` times a positive multiple of `sin φ cos φ`
  have term : ∀ {B φ x : ℝ}, 0 < B → Real.cos φ ≠ 0 → B * Real.cos φ * x = κ →
      B * Real.sin φ * x ^ 3 = κ ^ 3 * (1 / (B ^ 2 * Real.cos φ ^ 4) *
        (Real.sin φ * Real.cos φ)) := by
    intro B φ x hB hc hx
    rw [← hx]
    field_simp
  rw [term hB₁ hc₁ h₁, term hB₂ hc₂ h₂, term hB₃ hc₃ h₃, ← mul_add, ← mul_add]
  refine mul_ne_zero (pow_ne_zero 3 hκ) ?_
  have w₁ : 0 < 1 / (B₁ ^ 2 * Real.cos α ^ 4) := by positivity
  have w₂ : 0 < 1 / (B₂ ^ 2 * Real.cos β ^ 4) := by positivity
  have w₃ : 0 < 1 / (B₃ ^ 2 * Real.cos γ ^ 4) := by positivity
  have hsame : (0 < Real.sin α * Real.cos α ∧ 0 < Real.sin β * Real.cos β ∧
      0 < Real.sin γ * Real.cos γ) ∨ (Real.sin α * Real.cos α < 0 ∧
      Real.sin β * Real.cos β < 0 ∧ Real.sin γ * Real.cos γ < 0) := by
    have m₁ : B₁ * Real.cos α < 0 ↔ Real.cos α < 0 := by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    have m₂ : B₂ * Real.cos β < 0 ↔ Real.cos β < 0 := by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    have m₃ : B₃ * Real.cos γ < 0 ↔ Real.cos γ < 0 := by
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    rcases lt_or_gt_of_ne hc₁ with ha | ha
    · have hb : 0 < Real.cos β := by
        rcases lt_or_gt_of_ne hc₂ with hb | hb
        · exfalso; have := m₁.mpr ha; have := m₂.mpr hb; linarith
        · exact hb
      have hg : 0 < Real.cos γ := by
        rcases lt_or_gt_of_ne hc₃ with hg | hg
        · exfalso; have := m₁.mpr ha; have := m₃.mpr hg; linarith
        · exact hg
      exact sin_mul_cos_same_sign hsum ha hb hg
    · rcases lt_or_gt_of_ne hc₂ with hb | hb
      · have hg : 0 < Real.cos γ := by
          rcases lt_or_gt_of_ne hc₃ with hg | hg
          · exfalso; have := m₂.mpr hb; have := m₃.mpr hg; linarith
          · exact hg
        rcases sin_mul_cos_same_sign (α := β) (β := γ) (γ := α) (by linarith) hb hg ha with
          ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact Or.inl ⟨h3, h1, h2⟩
        · exact Or.inr ⟨h3, h1, h2⟩
      · rcases lt_or_gt_of_ne hc₃ with hg | hg
        · rcases sin_mul_cos_same_sign (α := γ) (β := α) (γ := β) (by linarith) hg ha hb with
            ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨h2, h3, h1⟩
          · exact Or.inr ⟨h2, h3, h1⟩
        · exact absurd ⟨ha, hb, hg⟩ hnot
  rcases hsame with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have := mul_pos w₁ h1; have := mul_pos w₂ h2; have := mul_pos w₃ h3
    linarith
  · have := mul_neg_of_pos_of_neg w₁ h1; have := mul_neg_of_pos_of_neg w₂ h2
    have := mul_neg_of_pos_of_neg w₃ h3
    linarith

private theorem hessForm_three (p : Params 2) (θ : Fin (2 + 1) → ℝ) (s t : ℝ) :
    hessForm p θ (ground ![s, t]) = 2 * (p.B 0 1 * Real.cos (θ 0 - θ 1) * s ^ 2 +
      p.B 0 2 * Real.cos (θ 0 - θ 2) * t ^ 2 + p.B 1 2 * Real.cos (θ 1 - θ 2) * (s - t) ^ 2) := by
  simp only [hessForm, Fin.sum_univ_succ, Fin.sum_univ_zero, ground]
  simp
  rw [p.B_symm 1 0, p.B_symm 2 0, p.B_symm 2 1, show θ 1 - θ 0 = -(θ 0 - θ 1) by ring,
    show θ 2 - θ 0 = -(θ 0 - θ 2) by ring, show θ 2 - θ 1 = -(θ 1 - θ 2) by ring]
  simp only [Real.cos_neg]
  ring

private theorem cubicForm_three (p : Params 2) (θ : Fin (2 + 1) → ℝ) (s t : ℝ) :
    cubicForm p θ (ground ![s, t]) = 2 * (-(p.B 0 1 * Real.sin (θ 0 - θ 1)) * s ^ 3 -
      p.B 0 2 * Real.sin (θ 0 - θ 2) * t ^ 3 + p.B 1 2 * Real.sin (θ 1 - θ 2) * (s - t) ^ 3) := by
  simp only [cubicForm, Fin.sum_univ_succ, Fin.sum_univ_zero, ground]
  simp
  rw [p.B_symm 1 0, p.B_symm 2 0, p.B_symm 2 1, show θ 1 - θ 0 = -(θ 0 - θ 1) by ring,
    show θ 2 - θ 0 = -(θ 0 - θ 2) by ring, show θ 2 - θ 1 = -(θ 1 - θ 2) by ring]
  simp only [Real.sin_neg]
  ring

private theorem B_eq_zero_of {B φ : ℝ} (hB : 0 ≤ B) (hc : B * Real.cos φ = 0)
    (hs : B * Real.sin φ = 0) : B = 0 := by
  have := Real.sin_sq_add_cos_sq φ
  nlinarith [sq_nonneg B]

private theorem pos_of_mul_cos_ne {B φ : ℝ} (hB : 0 ≤ B) (h : B * Real.cos φ ≠ 0) : 0 < B :=
  lt_of_le_of_ne hB fun h0 => h (by rw [← h0, zero_mul])

/-- The grounded vector `(0, u₁, u₂)`. -/
private theorem eq_ground_three (u : Fin (2 + 1) → ℝ) (hu0 : u 0 = 0) :
    u = ground ![u 1, u 2] := by
  funext k
  fin_cases k
  · exact hu0
  · rfl
  · rfl

/-- Implementation evidence for `not_localAsymptoticStable_three`, at the selected point of the
untranslated field. -/
private theorem reducedSwing_not_localAsymptoticStable_three (p : Params 2)
    (θ : Fin (2 + 1) → ℝ) (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  intro hLAS
  have hF : ∀ s t, 0 ≤ p.B 0 1 * Real.cos (θ 0 - θ 1) * s ^ 2 +
      p.B 0 2 * Real.cos (θ 0 - θ 2) * t ^ 2 + p.B 1 2 * Real.cos (θ 1 - θ 2) * (s - t) ^ 2 := by
    intro s t
    by_contra hneg
    push Not at hneg
    exact reducedSwing_not_localAsymptoticStable_of_forms hbal ![s, t]
      (Or.inl (by rw [hessForm_three]; linarith)) hLAS
  have hK : ∀ s t, p.B 0 1 * Real.cos (θ 0 - θ 1) * s ^ 2 +
      p.B 0 2 * Real.cos (θ 0 - θ 2) * t ^ 2 + p.B 1 2 * Real.cos (θ 1 - θ 2) * (s - t) ^ 2 = 0 →
      -(p.B 0 1 * Real.sin (θ 0 - θ 1)) * s ^ 3 - p.B 0 2 * Real.sin (θ 0 - θ 2) * t ^ 3 +
        p.B 1 2 * Real.sin (θ 1 - θ 2) * (s - t) ^ 3 = 0 := by
    intro s t h0
    by_contra hne
    refine reducedSwing_not_localAsymptoticStable_of_forms hbal ![s, t] (Or.inr ⟨?_, ?_⟩) hLAS
    · rw [hessForm_three, h0, mul_zero]
    · rw [cubicForm_three]
      exact mul_ne_zero two_ne_zero hne
  have hline : ∀ v : Fin 2 → ℝ, v ≠ 0 → ¬ ∀ k j, p.B k j = 0 ∨ ground v k = ground v j :=
    fun v hv h => reducedSwing_not_localAsymptoticStable_of_balance_line hv
      (balance_line_of_edges hbal v h) hLAS
  obtain ⟨u, hu0, hu, hle⟩ := exists_hessForm_nonpos hH
  have hug := eq_ground_three u hu0
  have hst : ¬ (u 1 = 0 ∧ u 2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hu
    rw [hug, h1, h2]
    funext k; fin_cases k <;> rfl
  rw [hug, hessForm_three] at hle
  -- abbreviations
  have hB01 := p.B_nonneg 0 1
  have hB02 := p.B_nonneg 0 2
  have hB12 := p.B_nonneg 1 2
  have hcos10 : Real.cos (θ 1 - θ 0) = Real.cos (θ 0 - θ 1) := by
    rw [show θ 1 - θ 0 = -(θ 0 - θ 1) by ring, Real.cos_neg]
  have hcos20 : Real.cos (θ 2 - θ 0) = Real.cos (θ 0 - θ 2) := by
    rw [show θ 2 - θ 0 = -(θ 0 - θ 2) by ring, Real.cos_neg]
  have hcos21 : Real.cos (θ 2 - θ 1) = Real.cos (θ 1 - θ 2) := by
    rw [show θ 2 - θ 1 = -(θ 1 - θ 2) by ring, Real.cos_neg]
  have hsin10 : Real.sin (θ 1 - θ 0) = -Real.sin (θ 0 - θ 1) := by
    rw [show θ 1 - θ 0 = -(θ 0 - θ 1) by ring, Real.sin_neg]
  have hsin20 : Real.sin (θ 2 - θ 0) = -Real.sin (θ 0 - θ 2) := by
    rw [show θ 2 - θ 0 = -(θ 0 - θ 2) by ring, Real.sin_neg]
  have hsin21 : Real.sin (θ 2 - θ 1) = -Real.sin (θ 1 - θ 2) := by
    rw [show θ 2 - θ 1 = -(θ 1 - θ 2) by ring, Real.sin_neg]
  generalize ha : p.B 0 1 * Real.cos (θ 0 - θ 1) = a at hF hK hle
  generalize hc : p.B 0 2 * Real.cos (θ 0 - θ 2) = c at hF hK hle
  generalize hb : p.B 1 2 * Real.cos (θ 1 - θ 2) = b at hF hK hle
  generalize hS₁ : p.B 0 1 * Real.sin (θ 0 - θ 1) = S₁ at hK
  generalize hS₂ : p.B 0 2 * Real.sin (θ 0 - θ 2) = S₂ at hK
  generalize hS₃ : p.B 1 2 * Real.sin (θ 1 - θ 2) = S₃ at hK
  generalize hs₀ : u 1 = s₀ at hst hle
  generalize ht₀ : u 2 = t₀ at hst hle
  have hF0 : a * s₀ ^ 2 + c * t₀ ^ 2 + b * (s₀ - t₀) ^ 2 = 0 := le_antisymm (by linarith) (hF _ _)
  have hL1 : a * s₀ + b * (s₀ - t₀) = 0 := by
    have := eq_zero_of_forall_linear_quadratic_nonneg (L := 2 * (a * s₀ + b * (s₀ - t₀)))
      (Q := a + b) fun x => by
        have h := hF (s₀ + x) t₀
        have e : a * (s₀ + x) ^ 2 + c * t₀ ^ 2 + b * (s₀ + x - t₀) ^ 2 =
            (a * s₀ ^ 2 + c * t₀ ^ 2 + b * (s₀ - t₀) ^ 2) +
              (x * (2 * (a * s₀ + b * (s₀ - t₀))) + x ^ 2 * (a + b)) := by ring
        rw [e, hF0, zero_add] at h
        exact h
    linarith
  have hL2 : c * t₀ - b * (s₀ - t₀) = 0 := by
    have := eq_zero_of_forall_linear_quadratic_nonneg (L := 2 * (c * t₀ - b * (s₀ - t₀)))
      (Q := c + b) fun x => by
        have h := hF s₀ (t₀ + x)
        have e : a * s₀ ^ 2 + c * (t₀ + x) ^ 2 + b * (s₀ - (t₀ + x)) ^ 2 =
            (a * s₀ ^ 2 + c * t₀ ^ 2 + b * (s₀ - t₀) ^ 2) +
              (x * (2 * (c * t₀ - b * (s₀ - t₀))) + x ^ 2 * (c + b)) := by ring
        rw [e, hF0, zero_add] at h
        exact h
    linarith
  have hab : 0 ≤ a + b := by have := hF 1 0; norm_num at this; linarith
  have hcb : 0 ≤ c + b := by have := hF 0 1; norm_num at this; linarith
  have hac : 0 ≤ a + c := by have := hF 1 1; norm_num at this; linarith
  by_cases hκ0 : b * (s₀ - t₀) = 0
  · have ha0 : a * s₀ = 0 := by linarith
    have hc0 : c * t₀ = 0 := by linarith
    have hallzero : a = 0 → b = 0 → c = 0 → False := by
      intro ha' hb' hc'
      have hz : ∀ s t, a * s ^ 2 + c * t ^ 2 + b * (s - t) ^ 2 = 0 := fun s t => by
        rw [ha', hb', hc']; ring
      have k1 := hK 1 0 (hz 1 0)
      have k2 := hK 0 1 (hz 0 1)
      have k3 := hK 1 (-1) (hz 1 (-1))
      norm_num at k1 k2 k3
      have hS1 : S₁ = 0 := by linarith
      have hS2 : S₂ = 0 := by linarith
      have hS3 : S₃ = 0 := by linarith
      have e1 : p.B 0 1 = 0 := B_eq_zero_of hB01 (ha.trans ha') (hS₁.trans hS1)
      have e2 : p.B 0 2 = 0 := B_eq_zero_of hB02 (hc.trans hc') (hS₂.trans hS2)
      have e3 : p.B 1 2 = 0 := B_eq_zero_of hB12 (hb.trans hb') (hS₃.trans hS3)
      refine hline ![1, 0] (fun h => by simpa using congrFun h 0) fun k j => ?_
      fin_cases k <;> fin_cases j <;>
        simp [e1, e2, e3, p.B_symm 1 0, p.B_symm 2 0, p.B_symm 2 1, ground]
    by_cases ha' : a = 0
    · by_cases hc' : c = 0
      · -- node 0 against machines 1 and 2
        have hb' : b ≠ 0 := fun hb' => hallzero ha' hb' hc'
        have hbpos : 0 < b := lt_of_le_of_ne (by linarith) (Ne.symm hb')
        have hk := hK 1 1 (by rw [ha', hc']; ring)
        norm_num at hk
        rcases node_open_or_antiphase hB01 hB02 (ha.trans ha') (hc.trans hc')
            (by rw [hS₁, hS₂]; linarith) with ⟨e1, e2⟩ | hcos
        · refine hline ![1, 1] (fun h => by simpa using congrFun h 0) fun k j => ?_
          fin_cases k <;> fin_cases j <;> simp [e1, e2, p.B_symm 1 0, p.B_symm 2 0, ground]
        · rw [show θ 0 - θ 2 - (θ 0 - θ 1) = θ 1 - θ 2 by ring] at hcos
          rw [hcos] at hb
          linarith
      · -- node 1 against machines 0 and 2
        have ht : t₀ = 0 := (mul_eq_zero.mp hc0).resolve_left hc'
        have hs : s₀ ≠ 0 := fun h => hst ⟨h, ht⟩
        have hb' : b = 0 := by
          rw [ht, sub_zero] at hκ0
          exact (mul_eq_zero.mp hκ0).resolve_right hs
        have hcpos : 0 < c := lt_of_le_of_ne (by linarith) (Ne.symm hc')
        have hk := hK 1 0 (by rw [ha', hb']; ring)
        norm_num at hk
        have hc1 : p.B 1 0 * Real.cos (θ 1 - θ 0) = 0 := by rw [p.B_symm, hcos10, ha, ha']
        have hs1 : p.B 1 0 * Real.sin (θ 1 - θ 0) + p.B 1 2 * Real.sin (θ 1 - θ 2) = 0 := by
          rw [p.B_symm, hsin10, hS₃]
          have : p.B 0 1 * -Real.sin (θ 0 - θ 1) = -S₁ := by rw [← hS₁]; ring
          rw [this]; linarith
        rcases node_open_or_antiphase (p.B_nonneg 1 0) hB12 hc1 (hb.trans hb') hs1 with
          ⟨e1, e2⟩ | hcos
        · refine hline ![1, 0] (fun h => by simpa using congrFun h 0) fun k j => ?_
          have e1' : p.B 0 1 = 0 := by rw [p.B_symm]; exact e1
          fin_cases k <;> fin_cases j <;> simp [e1, e1', e2, p.B_symm 2 1, ground]
        · rw [show θ 1 - θ 2 - (θ 1 - θ 0) = θ 0 - θ 2 by ring] at hcos
          rw [hcos] at hc
          linarith
    · -- node 2 against machines 0 and 1
      have hs : s₀ = 0 := (mul_eq_zero.mp ha0).resolve_left ha'
      have ht : t₀ ≠ 0 := fun h => hst ⟨hs, h⟩
      have hc' : c = 0 := (mul_eq_zero.mp hc0).resolve_right ht
      have hb' : b = 0 := by
        rw [hs, zero_sub] at hκ0
        exact (mul_eq_zero.mp hκ0).resolve_right (neg_ne_zero.mpr ht)
      have hapos : 0 < a := lt_of_le_of_ne (by linarith) (Ne.symm ha')
      have hk := hK 0 1 (by rw [hc', hb']; ring)
      norm_num at hk
      have hc1 : p.B 2 0 * Real.cos (θ 2 - θ 0) = 0 := by rw [p.B_symm, hcos20, hc, hc']
      have hc2 : p.B 2 1 * Real.cos (θ 2 - θ 1) = 0 := by rw [p.B_symm, hcos21, hb, hb']
      have hs1 : p.B 2 0 * Real.sin (θ 2 - θ 0) + p.B 2 1 * Real.sin (θ 2 - θ 1) = 0 := by
        rw [p.B_symm 2 0, p.B_symm 2 1, hsin20, hsin21]
        have e1 : p.B 0 2 * -Real.sin (θ 0 - θ 2) = -S₂ := by rw [← hS₂]; ring
        have e2 : p.B 1 2 * -Real.sin (θ 1 - θ 2) = -S₃ := by rw [← hS₃]; ring
        rw [e1, e2]; linarith
      rcases node_open_or_antiphase (p.B_nonneg 2 0) (p.B_nonneg 2 1) hc1 hc2 hs1 with
        ⟨e1, e2⟩ | hcos
      · refine hline ![0, 1] (fun h => by simpa using congrFun h 1) fun k j => ?_
        have e1' : p.B 0 2 = 0 := by rw [p.B_symm]; exact e1
        have e2' : p.B 1 2 = 0 := by rw [p.B_symm]; exact e2
        fin_cases k <;> fin_cases j <;> simp [e1, e1', e2, e2', ground]
      · rw [show θ 2 - θ 1 - (θ 2 - θ 0) = θ 0 - θ 1 by ring] at hcos
        rw [hcos] at ha
        linarith
  · -- a circulating null direction: a fold on the triangle `0 → 1 → 2 → 0`
    have ha' : a ≠ 0 := fun h => hκ0 (by rw [h, zero_mul] at hL1; linarith)
    have hc' : c ≠ 0 := fun h => hκ0 (by rw [h, zero_mul] at hL2; linarith)
    have hb' : b ≠ 0 := fun h => hκ0 (by rw [h, zero_mul])
    have p01 := pos_of_mul_cos_ne hB01 (ha ▸ ha')
    have p02 := pos_of_mul_cos_ne hB02 (hc ▸ hc')
    have p12 := pos_of_mul_cos_ne hB12 (hb ▸ hb')
    have hnot : ¬ (0 < Real.cos (θ 0 - θ 1) ∧ 0 < Real.cos (θ 1 - θ 2) ∧
        0 < Real.cos (θ 2 - θ 0)) := by
      rintro ⟨h1, h2, h3⟩
      have hs : s₀ ≠ 0 := fun h => hκ0 (by rw [h] at hL1 ⊢; linarith)
      have ht : t₀ ≠ 0 := fun h => hκ0 (by rw [h] at hL2 ⊢; linarith)
      have hapos : 0 < a := by rw [← ha]; positivity
      have hbpos : 0 < b := by rw [← hb]; positivity
      have hcpos : 0 < c := by rw [← hc, ← hcos20]; positivity
      have : 0 < a * s₀ ^ 2 := by positivity
      have : 0 ≤ c * t₀ ^ 2 := by positivity
      have : 0 ≤ b * (s₀ - t₀) ^ 2 := by positivity
      linarith
    have hne := triangle_cubic_ne_zero (x₁ := -s₀) (x₂ := s₀ - t₀) (x₃ := t₀)
      (κ := b * (s₀ - t₀)) p01 p12 p02
      (show (θ 0 - θ 1) + (θ 1 - θ 2) + (θ 2 - θ 0) = 0 by ring)
      (by rw [ha]; linarith) (by rw [hb]) (by rw [hcos20, hc]; linarith) hκ0
      (by rw [ha, hb]; linarith) (by rw [hb, hcos20, hc]; linarith)
      (by rw [ha, hcos20, hc]; linarith) hnot
    apply hne
    have hk := hK s₀ t₀ hF0
    rw [hsin20]
    have e1 : p.B 0 1 * Real.sin (θ 0 - θ 1) * (-s₀) ^ 3 = -S₁ * s₀ ^ 3 := by rw [← hS₁]; ring
    have e2 : p.B 1 2 * Real.sin (θ 1 - θ 2) * (s₀ - t₀) ^ 3 = S₃ * (s₀ - t₀) ^ 3 := by
      rw [← hS₃]
    have e3 : p.B 0 2 * -Real.sin (θ 0 - θ 2) * t₀ ^ 3 = -S₂ * t₀ ^ 3 := by rw [← hS₂]; ring
    rw [e1, e2, e3]
    linarith


/-- **Three machines (`n = 2`).** At a power-balance point with a non-Hurwitz reduced Jacobian the
model is not locally asymptotically stable. With `a, b, c` the linearization weights of the
lines `01, 12, 02`, the Hessian form is `a s² + c t² + b (s − t)²` on grounded directions
`(0, s, t)`. A negative value is a saddle. Otherwise a null direction exists; if its circulation
`κ = b(s − t)` is nonzero, exactly one weight is negative and, since the three line angles sum to
zero, the cubic term has one strict sign (`triangle_cubic_ne_zero`): a fold. If `κ = 0` the null
direction turns one machine against the other two through two zero-weight lines, whose cubic terms
cancel only if both lines are open (a continuum of equilibria) or the third line is in antiphase,
which contradicts the positive Hessian along it. -/
@[powerlib_domain] theorem not_localAsymptoticStable_three (m : Model 2)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian m.params m.θ)) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff']
  exact reducedSwing_not_localAsymptoticStable_three m.params m.θ hbal hH

/-- **For three machines the local asymptotic translation is exact.** -/
@[powerlib_domain] theorem exact_locallyAsymptoticallyStable_three :
    connection% ((family (n := 2)).Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact exact_locallyAsymptoticallyStable_of_guard fun m hp hH =>
    not_localAsymptoticStable_three m hp hH

/-! ## Local asymptotic stability at a strict, isolated minimum of the potential -/

/-- The energy relative to the selected point, at a displacement `w`: kinetic energy of `w` plus
the potential increment of its relative angles. -/
@[powerlib_foundation] theorem energy_equilibrium_add {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) (w : State (n + (n + 1))) :
    energy p (equilibrium θ + w) - energy p (equilibrium θ) =
      (∑ k, p.M k * w (wIdx k) ^ 2) / 2 +
        (potential p (θ + ground fun i => w (dIdx i)) - potential p θ) := by
  have ha : angleMap (equilibrium θ + w) =
      fun k => (θ + ground fun i => w (dIdx i)) k + -θ 0 := by
    rw [map_add, angleMap_equilibrium, angleMap_eq_ground]
    funext k
    simp only [Pi.add_apply]
    ring
  rw [energy, ha, potential_add_const, sum_P_of_balance hbal, energy_equilibrium hbal]
  simp only [PiLp.add_apply, equilibrium_wIdx, zero_add, mul_zero, sub_zero]
  ring

/-- A relative-angle displacement that keeps power balance is an equilibrium of the reduced
field. -/
@[powerlib_foundation] theorem reducedField_equilibrium_add_angleState {p : Params n}
    {θ : Fin (n + 1) → ℝ} {v : Fin n → ℝ}
    (hv : ∀ k, p.P k = powerInjection p.B (θ + ground v) k) :
    reducedField p (equilibrium θ + angleState v) = 0 := by
  apply state_ext
  · intro i; simp [reducedField_dIdx, equilibrium_wIdx]
  · intro k
    rw [reducedField_wIdx]
    have ha : angleMap (equilibrium θ + angleState v) = fun j => (θ + ground v) j + -θ 0 := by
      rw [map_add, angleMap_equilibrium, angleMap_angleState]
      funext j
      simp only [Pi.add_apply]
      ring
    rw [ha, powerInjection_add_const, ← hv k]
    simp [equilibrium_wIdx]

/-- Implementation evidence: `Dynamics.Mechanical.localAsymptoticStable_of_strictMin` (LaSalle) on
the reduced field (`reducedField_eq_mechanical`). At a power-balance point whose relative angles
are a strict local minimum of the potential and an isolated power-balance point, the reduced swing
field is locally asymptotically stable, whatever its linearization. -/
private theorem reducedSwing_localAsymptoticStable_of_strictMin {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖ < r → potential p θ < potential p (θ + ground v))
    (hcrit : ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖ < r →
      ¬ ∀ k, p.P k = powerInjection p.B (θ + ground v) k) :
    LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  have hP := sum_P_of_balance hbal
  rw [reducedField_eq_mechanical hP, equilibrium_eq_point]
  refine Dynamics.Mechanical.localAsymptoticStable_of_strictMin (by omega)
    (potential_comp_ground_contDiff p) p.M_pos p.D_pos ((critical_iff_balance_zero hP θ).mpr hbal)
    hr (fun v hv0 hv => ?_)
    (fun v hv0 hv hc => hcrit v hv0 hv ((critical_iff_balance hP θ v).mp hc))
  rw [potential_ground_relAngles_add hP, potential_ground_relAngles hP]
  exact hmin v hv0 hv

/-- `angleState` as a continuous linear map. -/
def angleStateCLM : (Fin n → ℝ) →L[ℝ] State (n + (n + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := angleState
      map_add' := fun v w => by apply state_ext <;> intro _ <;> simp
      map_smul' := fun c v => by apply state_ext <;> intro _ <;> simp }

@[simp, powerlib_foundation] theorem angleStateCLM_apply (v : Fin n → ℝ) :
    angleStateCLM v = angleState v := rfl

@[powerlib_foundation] theorem hasFDerivAt_potential_ground (p : Params n)
    (θ : Fin (n + 1) → ℝ) (v : Fin n → ℝ) :
    HasFDerivAt (fun v => potential p (θ + ground v))
      ((potentialGrad p (θ + ground v)).comp groundCLM) v := by
  have h := (hasFDerivAt_potential p (θ + groundCLM v)).comp v (groundCLM.hasFDerivAt.const_add θ)
  exact h

/-- A local minimum of the potential in relative angles keeps power balance (its gradient
vanishes). -/
@[powerlib_foundation] theorem balance_of_isLocalMin {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) {v : Fin n → ℝ}
    (h : IsLocalMin (fun v => potential p (θ + ground v)) v) :
    ∀ k, p.P k = powerInjection p.B (θ + ground v) k := by
  have h0 := h.hasFDerivAt_eq_zero (hasFDerivAt_potential_ground p θ v)
  have hi : ∀ i : Fin n, powerInjection p.B (θ + ground v) i.succ - p.P i.succ = 0 := by
    intro i
    have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) h0
    simp only [ContinuousLinearMap.comp_apply, groundCLM_apply, potentialGrad_apply,
      ContinuousLinearMap.zero_apply] at this
    rw [Fin.sum_univ_succ] at this
    simpa [Pi.single_apply] using this
  have hsum : ∑ k, (powerInjection p.B (θ + ground v) k - p.P k) = 0 := by
    rw [Finset.sum_sub_distrib, sum_powerInjection, sum_P_of_balance hbal, sub_zero]
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero fun i _ => hi i, add_zero] at hsum
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · linarith
  · linarith [hi i]

/-- Implementation evidence: `Dynamics.Mechanical.strictMin_of_localAsymptoticStable` on the
reduced field. The selected point of a locally asymptotically stable network is a strict, isolated
minimum of the potential. -/
private theorem reducedSwing_strictMin_of_localAsymptoticStable {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hLAS : LocalAsymptoticStable (reducedField p) (equilibrium θ)) :
    ∃ r > 0, ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖ < r →
      potential p θ < potential p (θ + ground v) ∧
        ¬ ∀ k, p.P k = powerInjection p.B (θ + ground v) k := by
  have hP := sum_P_of_balance (powerFlow_of_lyapunovStable hLAS.1)
  rw [reducedField_eq_mechanical hP, equilibrium_eq_point] at hLAS
  obtain ⟨r, hr, h⟩ := Dynamics.Mechanical.strictMin_of_localAsymptoticStable
    (potential_comp_ground_contDiff p) (fun j => (p.M_pos j).ne') (fun j => (p.D_pos j).le) hLAS
  refine ⟨r, hr, fun v hv0 hv => ?_⟩
  obtain ⟨h1, h2⟩ := h v hv0 hv
  rw [potential_ground_relAngles_add hP, potential_ground_relAngles hP] at h1
  exact ⟨h1, fun hc => h2 ((critical_iff_balance hP θ v).mpr hc)⟩

/-- **Membership in local asymptotic stability, for every number of machines.** A swing network is
locally asymptotically stable at its selected angle profile exactly when the profile is a
power-balance point, a strict local minimum of the network potential in relative angles, and an
isolated power-balance point. The conditions are static: they do not mention solutions, and the
linearization is not involved (LaSalle, `Dynamics.Mechanical.localAsymptoticStable_of_strictMin`,
and the energy, `Dynamics.Mechanical.strictMin_of_localAsymptoticStable`, through
`reducedField_eq_mechanical`). -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (m : Model n) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      (∀ k, m.params.P k = powerInjection m.params.B m.θ k) ∧
      ∃ r > 0, ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖ < r →
        potential m.params m.θ < potential m.params (m.θ + ground v) ∧
        ¬ ∀ k, m.params.P k = powerInjection m.params.B (m.θ + ground v) k) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff']
  change LocalAsymptoticStable _ _ ↔ _
  constructor
  · intro h
    exact ⟨powerFlow_of_lyapunovStable h.1, reducedSwing_strictMin_of_localAsymptoticStable h⟩
  · rintro ⟨hp, r, hr, hv⟩
    exact reducedSwing_localAsymptoticStable_of_strictMin hp hr (fun v h0 h1 => (hv v h0 h1).1)
      (fun v h0 h1 => (hv v h0 h1).2)

end powerlib.Network.Swing
