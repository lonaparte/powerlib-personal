import theorem.LCL

/-! Forward trajectories of the ideal continuous-time three-state plant.
State order is converter current, capacitor voltage, grid current, in stationary
scalar coordinates. Both terminal voltages are constant independent inputs.
There is no controller, PLL, PWM, delay, sampling, or additional grid state.
The norm on `State` is the usual finite-dimensional supremum norm. -/
noncomputable section
namespace powerlib.LCL
open Set Filter
open scoped Topology

abbrev State := Fin 3 → ℝ

def StateSpace.vectorField (m : StateSpace) (u vg : ℝ) (x : State) : State :=
  let f := m.field (x 0) (x 1) (x 2) u vg
  ![f.1, f.2.1, f.2.2]

def StateSpace.operator (m : StateSpace) : State →L[ℝ] State :=
  (Matrix.toLin' m.matrix).toContinuousLinearMap

@[powerlib_foundation] theorem StateSpace.operator_field (m : StateSpace) (x : State) :
    m.operator x = m.vectorField 0 0 x := by
  change m.matrix.mulVec x = _
  have hx : x = ![x 0, x 1, x 2] := by
    ext j
    fin_cases j <;> rfl
  rw [hx, m.matrix_mulVec]
  rfl

def IsTrajectory (m : Circuit) (u vg : ℝ) (x : ℝ → State) : Prop :=
  ∀ t ∈ Ici (0 : ℝ),
    HasDerivWithinAt x ((toStateSpace m).vectorField u vg (x t)) (Ici 0) t

def IsEquilibrium (m : Circuit) (u vg : ℝ) (e : State) : Prop :=
  (toStateSpace m).vectorField u vg e = 0

@[powerlib_foundation] theorem trajectory_iff_circuit (m : Circuit) (u vg : ℝ) (x : ℝ → State) :
    IsTrajectory m u vg x ↔ ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ![(u - m.first.resistance * x t 0 - x t 1) / m.first.inductance.val,
        (x t 0 - x t 2) / m.capacitance.val,
        (x t 1 - m.second.resistance * x t 2 - vg) / m.second.inductance.val]
      (Ici 0) t := by
  simp only [IsTrajectory, StateSpace.vectorField, same_dynamics]

@[simp, powerlib_foundation] theorem zero_equilibrium (m : Circuit) :
    IsEquilibrium m 0 0 0 := by
  simp [IsEquilibrium, StateSpace.vectorField, StateSpace.field]

@[powerlib_foundation] theorem field_shift {m : Circuit} {u vg : ℝ} {e : State}
    (he : IsEquilibrium m u vg e) (x : State) :
    (toStateSpace m).vectorField u vg x = (toStateSpace m).operator (x - e) := by
  rw [StateSpace.operator_field]
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  dsimp [StateSpace.vectorField, StateSpace.field] at h0 h1 h2
  ext j
  fin_cases j
  · dsimp [StateSpace.vectorField, StateSpace.field]
    linear_combination h0
  · dsimp [StateSpace.vectorField, StateSpace.field]
    linear_combination h1
  · dsimp [StateSpace.vectorField, StateSpace.field]
    linear_combination h2

@[powerlib_foundation] theorem trajectory_shift {m : Circuit} {u vg : ℝ} {e : State}
    {x : ℝ → State} (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x) :
    IsTrajectory m 0 0 (fun t => x t - e) := by
  intro t ht
  simpa only [field_shift he, StateSpace.operator_field] using (hx t ht).sub_const e

def equilibrium (m : Circuit) (u vg : ℝ) : State :=
  let j := (u - vg) / m.a0
  ![j, u - m.first.resistance * j, j]

@[powerlib_domain] theorem equilibrium_exists {m : Circuit} (h0 : m.a0 ≠ 0) (u vg : ℝ) :
    IsEquilibrium m u vg (equilibrium m u vg) := by
  dsimp [IsEquilibrium, StateSpace.vectorField]
  rw [same_dynamics]
  ext j
  fin_cases j
  · simp [equilibrium]
  · simp [equilibrium]
  · change (u - m.first.resistance * ((u - vg) / m.a0) -
        m.second.resistance * ((u - vg) / m.a0) - vg) / m.second.inductance.val = 0
    have h : (m.first.resistance + m.second.resistance) *
        ((u - vg) / m.a0) = u - vg := by
      simpa only [Circuit.a0] using mul_div_cancel₀ (u - vg) h0
    have hz : u - m.first.resistance * ((u - vg) / m.a0) -
        m.second.resistance * ((u - vg) / m.a0) - vg = 0 := by
      dsimp [Circuit.a0] at h ⊢
      linear_combination -h
    rw [hz, zero_div]

@[powerlib_domain] theorem equilibrium_unique {m : Circuit} {u vg : ℝ} {e : State}
    (h0 : m.a0 ≠ 0) (he : IsEquilibrium m u vg e) : e = equilibrium m u vg := by
  simp only [IsEquilibrium, StateSpace.vectorField, same_dynamics] at he
  have hf := he
  have hfirst : u - m.first.resistance * e 0 - e 1 = 0 := by
    have h := congrFun hf 0
    simpa [div_eq_zero_iff, ne_of_gt m.first.inductance.property] using h
  have hmiddle : e 0 - e 2 = 0 := by
    have h := congrFun hf 1
    simpa [div_eq_zero_iff, ne_of_gt m.capacitance.property] using h
  have hlast : e 1 - m.second.resistance * e 2 - vg = 0 := by
    have h := congrFun hf 2
    simpa [div_eq_zero_iff, ne_of_gt m.second.inductance.property] using h
  have h02 : e 0 = e 2 := sub_eq_zero.mp hmiddle
  rw [← h02] at hlast
  have hi : e 0 = (u - vg) / m.a0 := by
    apply (eq_div_iff h0).mpr
    dsimp [Circuit.a0]
    linear_combination -hfirst -hlast
  ext j
  fin_cases j
  · exact hi
  · change e 1 = u - m.first.resistance * ((u - vg) / m.a0)
    rw [← hi]
    linarith
  · exact h02.symm.trans hi

def response (m : Circuit) (initial : State) (t : ℝ) : State :=
  (NormedSpace.exp (t • (toStateSpace m).operator)) initial

@[simp, powerlib_foundation] theorem response_initial (m : Circuit) (initial : State) :
    response m initial 0 = initial := by
  simp [response, NormedSpace.exp_zero]

@[powerlib_domain, aesop safe apply] theorem response_solves (m : Circuit) (initial : State) (t : ℝ) :
    HasDerivAt (response m initial) ((toStateSpace m).operator (response m initial t)) t := by
  have h := (hasDerivAt_exp_smul_const' (toStateSpace m).operator t).clm_apply
    (hasDerivAt_const t initial)
  simpa [response, mul_apply_eq_comp] using! h

@[powerlib_domain, aesop safe apply] theorem response_trajectory (m : Circuit) (initial : State) :
    IsTrajectory m 0 0 (response m initial) := by
  intro t _
  simpa only [StateSpace.operator_field] using (response_solves m initial t).hasDerivWithinAt

def equilibriumResponse (m : Circuit) (e initial : State) (t : ℝ) : State :=
  e + response m (initial - e) t

@[simp, powerlib_foundation] theorem equilibriumResponse_initial (m : Circuit) (e initial : State) :
    equilibriumResponse m e initial 0 = initial := by
  simp [equilibriumResponse]

@[powerlib_domain, aesop safe apply] theorem equilibriumResponse_trajectory {m : Circuit} {u vg : ℝ} {e : State}
    (he : IsEquilibrium m u vg e) (initial : State) :
    IsTrajectory m u vg (equilibriumResponse m e initial) := by
  intro t _
  have h := (response_solves m (initial - e) t).const_add e
  convert! h.hasDerivWithinAt using 1
  rw [field_shift he]
  simp [equilibriumResponse]

@[powerlib_domain] theorem trajectory_exists {m : Circuit} {u vg : ℝ} {e : State}
    (he : IsEquilibrium m u vg e) (initial : State) :
    ∃ x, IsTrajectory m u vg x ∧ x 0 = initial :=
  ⟨equilibriumResponse m e initial, equilibriumResponse_trajectory he initial,
    equilibriumResponse_initial m e initial⟩

@[powerlib_domain] theorem trajectory_unique {m : Circuit} {u vg : ℝ} {e : State}
    {x y : ℝ → State} (he : IsEquilibrium m u vg e)
    (hx : IsTrajectory m u vg x) (hy : IsTrajectory m u vg y) (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := by
  intro t ht
  let A := (toStateSpace m).operator
  have hd : ∀ s ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun r => x r - y r) (A (x s - y s)) (Ici 0) s := by
    intro s hs
    convert! (hx s hs).sub (hy s hs) using 1
    simp only [field_shift he, ← map_sub]
    congr 1
    abel
  have hc : ContinuousOn (fun s => x s - y s) (Icc 0 t) := by
    intro s hs
    exact ((hd s hs.1).continuousWithinAt).mono (fun r hr => hr.1)
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := 0) (K := ‖A‖) (ε := 0) hc
    (fun s hs => (hd s hs.1).mono (fun r hr => hs.1.trans hr))
    (by simp [h0]) (fun s _ => by simpa using A.le_opNorm (x s - y s))
    t ⟨ht, le_rfl⟩
  have hz : ‖x t - y t‖ = 0 := le_antisymm (by simpa [gronwallBound] using hb) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

@[powerlib_domain] theorem trajectory_eq_equilibriumResponse {m : Circuit} {u vg : ℝ} {e : State}
    {x : ℝ → State} (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x)
    {t : ℝ} (ht : 0 ≤ t) : x t = equilibriumResponse m e (x 0) t :=
  trajectory_unique he hx (equilibriumResponse_trajectory he (x 0))
    (equilibriumResponse_initial m e (x 0)).symm ht

end powerlib.LCL
