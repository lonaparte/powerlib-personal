import dependencies.Mathlib
import theorem.StateSpacePassivity

noncomputable section
namespace powerlib.StateSpacePassivity
open Set Filter Matrix
open scoped Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def operator (m : Model ι κ) : State ι →L[ℝ] State ι :=
  (Matrix.toLin' m.A).toContinuousLinearMap

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem operator_apply (m : Model ι κ) (x : State ι) :
    operator m x = m.A.mulVec x := rfl

@[powerlib_foundation] theorem operator_field (m : Model ι κ) (x : State ι) :
    operator m x = field m x 0 := by
  simp [field]

@[powerlib_foundation] theorem field_lipschitz (m : Model ι κ) (u : κ → ℝ) :
    LipschitzWith ‖operator m‖₊ (fun x => field m x u) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  simpa only [field, operator_apply, add_sub_add_right_eq_sub] using
    (lipschitzWith_iff_norm_sub_le.mp (operator m).lipschitzWith x y)

def response (m : Model ι κ) (initial : State ι) (t : ℝ) : State ι :=
  (NormedSpace.exp (t • operator m)) initial

omit [Fintype κ] in
@[simp, powerlib_domain] theorem response_initial (m : Model ι κ) (initial : State ι) :
    response m initial 0 = initial := by
  simp [response, NormedSpace.exp_zero]

omit [Fintype κ] in
@[powerlib_domain, aesop safe apply (transparency! := default)] theorem response_solves (m : Model ι κ) (initial : State ι) (t : ℝ) :
    HasDerivAt (response m initial) (operator m (response m initial t)) t := by
  have h := (hasDerivAt_exp_smul_const' (operator m) t).clm_apply
    (hasDerivAt_const t initial)
  simpa [response, mul_apply_eq_comp] using! h

@[powerlib_domain, aesop safe apply] theorem response_trajectory (m : Model ι κ) (initial : State ι) :
    Passivity.IsTrajectory (system m) (fun _ => 0) (response m initial) := by
  intro t _
  simpa only [operator_field, system] using (response_solves m initial t).hasDerivWithinAt

@[powerlib_domain, aesop norm forward (immediate := [m, initial])] theorem trajectory_exists
    (m : Model ι κ) (initial : State ι) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => 0) x ∧ x 0 = initial :=
  ⟨response m initial, response_trajectory m initial, response_initial m initial⟩

@[powerlib_domain, aesop norm forward (immediate := [m, hx, hy, h0])]
theorem trajectory_unique (m : Model ι κ)
    {u : ℝ → (κ → ℝ)} {x y : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) u x)
    (hy : Passivity.IsTrajectory (system m) u y) (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := by
  intro t ht
  have hc (z : ℝ → State ι) (hz : Passivity.IsTrajectory (system m) u z) :
      ContinuousOn z (Icc 0 t) := by
    intro r hr
    exact (hz r hr.1).continuousWithinAt.mono (fun _ hh => hh.1)
  have hd (z : ℝ → State ι) (hz : Passivity.IsTrajectory (system m) u z) :
      ∀ r ∈ Ico 0 t, HasDerivWithinAt z (field m (z r) (u r)) (Ici r) r := by
    intro r hr
    exact (hz r hr.1).mono (fun _ hh => hr.1.trans hh)
  exact ODE_solution_unique (v := fun t x => field m x (u t))
    (fun t => field_lipschitz m (u t))
    (hc x hx) (hd x hx) (hc y hy) (hd y hy) h0 ⟨ht, le_rfl⟩

@[powerlib_domain] theorem trajectory_eq_response (m : Model ι κ)
    {x : ℝ → State ι} (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x)
    {t : ℝ} (ht : 0 ≤ t) : x t = response m (x 0) t :=
  trajectory_unique m hx (response_trajectory m (x 0)) (response_initial m (x 0)).symm ht

@[powerlib_domain, aesop norm -1 apply] theorem trajectory_exists_unique (m : Model ι κ) (initial : State ι) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => 0) x ∧ x 0 = initial ∧
      ∀ y, Passivity.IsTrajectory (system m) (fun _ => 0) y → y 0 = initial →
        EqOn y x (Ici 0) := by
  refine ⟨response m initial, response_trajectory m initial, response_initial m initial, ?_⟩
  intro y hy h0
  exact trajectory_unique m hy (response_trajectory m initial)
    (h0.trans (response_initial m initial).symm)

def IsEquilibrium (m : Model ι κ) (u : κ → ℝ) (e : State ι) : Prop :=
  field m e u = 0

def LyapunovStableAt (m : Model ι κ) (u : κ → ℝ) (e : State ι) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    Passivity.IsTrajectory (system m) (fun _ => u) x → ‖x 0 - e‖ < δ →
      ∀ t ≥ 0, ‖x t - e‖ < ε

@[powerlib_foundation] theorem field_shift {m : Model ι κ} {u : κ → ℝ} {e : State ι}
    (he : IsEquilibrium m u e) (x : State ι) :
    field m x u = operator m (x - e) := by
  change m.A.mulVec x + m.B.mulVec u = m.A.mulVec (x - e)
  rw [mulVec_sub]
  have he' : m.A.mulVec e + m.B.mulVec u = 0 := he
  calc
    _ = m.A.mulVec x + m.B.mulVec u - (m.A.mulVec e + m.B.mulVec u) := by
      rw [he']; simp
    _ = _ := by abel

@[powerlib_foundation] theorem trajectory_shift {m : Model ι κ}
    {u : κ → ℝ} {e : State ι} {x : ℝ → State ι}
    (he : IsEquilibrium m u e)
    (hx : Passivity.IsTrajectory (system m) (fun _ => u) x) :
    Passivity.IsTrajectory (system m) (fun _ => 0) (fun t => x t - e) := by
  intro t ht
  simpa only [system, field_shift he, ← operator_field] using (hx t ht).sub_const e

@[powerlib_foundation] theorem trajectory_add_equilibrium {m : Model ι κ}
    {u : κ → ℝ} {e : State ι} {x : ℝ → State ι}
    (he : IsEquilibrium m u e)
    (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x) :
    Passivity.IsTrajectory (system m) (fun _ => u) (fun t => x t + e) := by
  intro t ht
  simpa only [system, field_shift he, add_sub_cancel_right, ← operator_field] using
    (hx t ht).add_const e

@[powerlib_foundation] theorem trajectory_shift_iff {m : Model ι κ}
    {u : κ → ℝ} {e : State ι} {x : ℝ → State ι} (he : IsEquilibrium m u e) :
    Passivity.IsTrajectory (system m) (fun _ => u) x ↔
      Passivity.IsTrajectory (system m) (fun _ => 0) (fun t => x t - e) := by
  constructor
  · exact trajectory_shift he
  · intro hx
    simpa only [sub_add_cancel] using trajectory_add_equilibrium he hx

def equilibriumResponse (m : Model ι κ) (e initial : State ι) (t : ℝ) : State ι :=
  response m (initial - e) t + e

omit [Fintype κ] in
@[simp, powerlib_domain] theorem equilibriumResponse_initial
    (m : Model ι κ) (e initial : State ι) : equilibriumResponse m e initial 0 = initial := by
  simp [equilibriumResponse]

@[powerlib_domain, aesop safe apply] theorem equilibriumResponse_trajectory {m : Model ι κ}
    {u : κ → ℝ} {e : State ι} (he : IsEquilibrium m u e) (initial : State ι) :
    Passivity.IsTrajectory (system m) (fun _ => u) (equilibriumResponse m e initial) :=
  trajectory_add_equilibrium he (response_trajectory m (initial - e))

@[powerlib_domain, aesop norm forward (immediate := [m, he, initial])] theorem equilibrium_trajectory_exists {m : Model ι κ}
    {u : κ → ℝ} {e : State ι} (he : IsEquilibrium m u e) (initial : State ι) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => u) x ∧ x 0 = initial :=
  ⟨equilibriumResponse m e initial, equilibriumResponse_trajectory he initial,
    equilibriumResponse_initial m e initial⟩

@[powerlib_domain] theorem trajectory_eq_equilibriumResponse {m : Model ι κ}
    {u : κ → ℝ} {e : State ι} (he : IsEquilibrium m u e) {x : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) (fun _ => u) x) {t : ℝ} (ht : 0 ≤ t) :
    x t = equilibriumResponse m e (x 0) t :=
  trajectory_unique m hx (equilibriumResponse_trajectory he (x 0))
    (equilibriumResponse_initial m e (x 0)).symm ht

@[powerlib_domain, aesop safe apply] theorem lyapunovStableAt_of_zeroInput
    {m : Model ι κ} {u : κ → ℝ} {e : State ι}
    (he : IsEquilibrium m u e) (hs : Passivity.LyapunovStable (system m)) :
    LyapunovStableAt m u e := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx h0 t ht
  exact hbound (fun r => x r - e) (trajectory_shift he hx) h0 t ht

@[powerlib_domain, aesop norm forward (immediate := [c, he])]
theorem Certificate.lyapunovStableAt [Nonempty ι]
    {m : Model ι κ} (c : Certificate m) {u : κ → ℝ} {e : State ι}
    (he : IsEquilibrium m u e) : LyapunovStableAt m u e :=
  lyapunovStableAt_of_zeroInput he c.lyapunovStable

@[powerlib_domain] theorem lyapunovStableAt_iff_zeroInput
    {m : Model ι κ} {u : κ → ℝ} {e : State ι} (he : IsEquilibrium m u e) :
    LyapunovStableAt m u e ↔ Passivity.LyapunovStable (system m) := by
  constructor
  · intro hs ε hε
    obtain ⟨δ, hδ, hbound⟩ := hs ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx h0 t ht
    simpa only [add_sub_cancel_right] using
      hbound (fun r => x r + e) (trajectory_add_equilibrium he hx)
        (by simpa only [add_sub_cancel_right] using h0) t ht
  · exact lyapunovStableAt_of_zeroInput he

end powerlib.StateSpacePassivity
