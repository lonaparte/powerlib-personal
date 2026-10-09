import dependencies.Mathlib
import theorem.StateSpacePassivity

noncomputable section
namespace powerlib.StateSpacePassivity
open Set Filter Matrix
open scoped Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

@[powerlib_domain, aesop safe apply] theorem response_trajectory (m : LTI.Model ι κ) (initial : ι → ℝ) :
    Passivity.IsTrajectory (system m) (fun _ => 0) (m.response initial) := by
  intro t _
  simpa only [LTI.Model.operator_field, system] using (m.response_solves initial t).hasDerivWithinAt

@[powerlib_domain, aesop norm forward (immediate := [m, initial])] theorem trajectory_exists
    (m : LTI.Model ι κ) (initial : ι → ℝ) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => 0) x ∧ x 0 = initial :=
  ⟨m.response initial, response_trajectory m initial, m.response_initial initial⟩

@[powerlib_domain, aesop norm forward (immediate := [m, hx, hy, h0])]
theorem trajectory_unique (m : LTI.Model ι κ)
    {u : ℝ → (κ → ℝ)} {x y : ℝ → (ι → ℝ)}
    (hx : Passivity.IsTrajectory (system m) u x)
    (hy : Passivity.IsTrajectory (system m) u y) (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := by
  intro t ht
  have hc (z : ℝ → (ι → ℝ)) (hz : Passivity.IsTrajectory (system m) u z) :
      ContinuousOn z (Icc 0 t) := by
    intro r hr
    exact (hz r hr.1).continuousWithinAt.mono (fun _ hh => hh.1)
  have hd (z : ℝ → (ι → ℝ)) (hz : Passivity.IsTrajectory (system m) u z) :
      ∀ r ∈ Ico 0 t, HasDerivWithinAt z (m.field (z r) (u r)) (Ici r) r := by
    intro r hr
    exact (hz r hr.1).mono (fun _ hh => hr.1.trans hh)
  exact ODE_solution_unique (v := fun t x => m.field x (u t))
    (fun t => m.field_lipschitz (u t))
    (hc x hx) (hd x hx) (hc y hy) (hd y hy) h0 ⟨ht, le_rfl⟩

@[powerlib_domain] theorem trajectory_eq_response (m : LTI.Model ι κ)
    {x : ℝ → (ι → ℝ)} (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x)
    {t : ℝ} (ht : 0 ≤ t) : x t = m.response (x 0) t :=
  trajectory_unique m hx (response_trajectory m (x 0)) (m.response_initial (x 0)).symm ht

@[powerlib_domain, aesop norm -1 apply] theorem trajectory_exists_unique (m : LTI.Model ι κ) (initial : ι → ℝ) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => 0) x ∧ x 0 = initial ∧
      ∀ y, Passivity.IsTrajectory (system m) (fun _ => 0) y → y 0 = initial →
        EqOn y x (Ici 0) := by
  refine ⟨m.response initial, response_trajectory m initial, m.response_initial initial, ?_⟩
  intro y hy h0
  exact trajectory_unique m hy (response_trajectory m initial)
    (h0.trans (m.response_initial initial).symm)

@[powerlib_foundation, aesop safe forward] theorem trajectory_of_autonomous {n : ℕ} {m : LTI.Model (Fin n) κ}
    {x : ℝ → (Fin n → ℝ)} (hx : LTI.IsTrajectory m.autonomous x) :
    Passivity.IsTrajectory (system m) (fun _ => 0) x := by
  intro t _
  simpa only [system, LTI.Model.autonomous_field] using (hx t).hasDerivWithinAt

def LyapunovStableAt (m : LTI.Model ι κ) (u : κ → ℝ) (e : ι → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    Passivity.IsTrajectory (system m) (fun _ => u) x → ‖x 0 - e‖ < δ →
      ∀ t ≥ 0, ‖x t - e‖ < ε

@[powerlib_foundation] theorem trajectory_shift {m : LTI.Model ι κ}
    {u : κ → ℝ} {e : ι → ℝ} {x : ℝ → (ι → ℝ)}
    (he : m.IsEquilibrium u e)
    (hx : Passivity.IsTrajectory (system m) (fun _ => u) x) :
    Passivity.IsTrajectory (system m) (fun _ => 0) (fun t => x t - e) := by
  intro t ht
  simpa only [system, LTI.Model.field_shift he, ← LTI.Model.operator_field] using (hx t ht).sub_const e

@[powerlib_foundation] theorem trajectory_add_equilibrium {m : LTI.Model ι κ}
    {u : κ → ℝ} {e : ι → ℝ} {x : ℝ → (ι → ℝ)}
    (he : m.IsEquilibrium u e)
    (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x) :
    Passivity.IsTrajectory (system m) (fun _ => u) (fun t => x t + e) := by
  intro t ht
  simpa only [system, LTI.Model.field_shift he, add_sub_cancel_right, ← LTI.Model.operator_field] using
    (hx t ht).add_const e

@[powerlib_foundation] theorem trajectory_shift_iff {m : LTI.Model ι κ}
    {u : κ → ℝ} {e : ι → ℝ} {x : ℝ → (ι → ℝ)} (he : m.IsEquilibrium u e) :
    Passivity.IsTrajectory (system m) (fun _ => u) x ↔
      Passivity.IsTrajectory (system m) (fun _ => 0) (fun t => x t - e) := by
  constructor
  · exact trajectory_shift he
  · intro hx
    simpa only [sub_add_cancel] using trajectory_add_equilibrium he hx

@[powerlib_domain, aesop safe apply] theorem equilibriumResponse_trajectory {m : LTI.Model ι κ}
    {u : κ → ℝ} {e : ι → ℝ} (he : m.IsEquilibrium u e) (initial : ι → ℝ) :
    Passivity.IsTrajectory (system m) (fun _ => u) (m.equilibriumResponse e initial) :=
  trajectory_add_equilibrium he (response_trajectory m (initial - e))

@[powerlib_domain, aesop norm forward (immediate := [m, he, initial])] theorem equilibrium_trajectory_exists {m : LTI.Model ι κ}
    {u : κ → ℝ} {e : ι → ℝ} (he : m.IsEquilibrium u e) (initial : ι → ℝ) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => u) x ∧ x 0 = initial :=
  ⟨m.equilibriumResponse e initial, equilibriumResponse_trajectory he initial,
    m.equilibriumResponse_initial e initial⟩

@[powerlib_domain] theorem trajectory_eq_equilibriumResponse {m : LTI.Model ι κ}
    {u : κ → ℝ} {e : ι → ℝ} (he : m.IsEquilibrium u e) {x : ℝ → (ι → ℝ)}
    (hx : Passivity.IsTrajectory (system m) (fun _ => u) x) {t : ℝ} (ht : 0 ≤ t) :
    x t = m.equilibriumResponse e (x 0) t :=
  trajectory_unique m hx (equilibriumResponse_trajectory he (x 0))
    (m.equilibriumResponse_initial e (x 0)).symm ht

@[powerlib_domain, aesop safe apply] theorem lyapunovStableAt_of_zeroInput
    {m : LTI.Model ι κ} {u : κ → ℝ} {e : ι → ℝ}
    (he : m.IsEquilibrium u e) (hs : Passivity.LyapunovStable (system m)) :
    LyapunovStableAt m u e := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx h0 t ht
  exact hbound (fun r => x r - e) (trajectory_shift he hx) h0 t ht

@[powerlib_domain, aesop norm forward (immediate := [c, he])]
theorem Certificate.lyapunovStableAt [Nonempty ι]
    {m : LTI.Model ι κ} (c : Certificate m) {u : κ → ℝ} {e : ι → ℝ}
    (he : m.IsEquilibrium u e) : LyapunovStableAt m u e :=
  lyapunovStableAt_of_zeroInput he c.lyapunovStable

@[powerlib_domain] theorem lyapunovStableAt_iff_zeroInput
    {m : LTI.Model ι κ} {u : κ → ℝ} {e : ι → ℝ} (he : m.IsEquilibrium u e) :
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
