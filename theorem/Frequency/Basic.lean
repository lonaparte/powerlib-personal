import theorem.Hurwitz
import theorem.StateSpaceTrajectories

/-! # Frequency-response family: shared LTI trajectory interface

Foundation glue used by every `powerlib.Frequency` module.

* `Frequency.IsTrajectory m u x` is a forward trajectory (`t ≥ 0`, one-sided derivatives at
  `t = 0`) of the input-state model `ẋ = A x + B u` of an `LTI.Model` under the **constant**
  input `u` (a load step applied at `t = 0`). It is `Passivity.IsTrajectory` of
  `StateSpacePassivity.system m` with the constant input signal.
* `Frequency.ExponentiallyConvergesTo m u e` says that every such trajectory converges to the
  state `e` with one uniform exponential envelope (Euclidean norm of `Fin n → ℝ`).
* `exponentiallyConvergesTo_of_isHurwitz`: an equilibrium `e` for the input `u` together with a
  Hurwitz state matrix gives `ExponentiallyConvergesTo m u e`. The proof shifts the trajectory
  to the zero-input model (`StateSpacePassivity.trajectory_shift`), identifies it with the
  operator-exponential response (`StateSpacePassivity.trajectory_eq_response`) and applies
  `LTI.exponentiallyStable_of_isHurwitz`.

These are statements about an arbitrary submitted `LTI.Model`; the frequency-response models
themselves (state order, signs, parameter ranges) are fixed in the modules that use them.
-/

noncomputable section
namespace powerlib.Frequency
open Set Filter Matrix
open scoped Topology

variable {n : ℕ} {κ : Type*} [Fintype κ]

/-- Forward trajectory of `ẋ = A x + B u` under the constant input `u`. -/
abbrev IsTrajectory (m : LTI.Model (Fin n) κ) (u : κ → ℝ) (x : ℝ → Fin n → ℝ) : Prop :=
  Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => u) x

/-- Every constant-input trajectory converges to `e` with a uniform exponential envelope. -/
def ExponentiallyConvergesTo (m : LTI.Model (Fin n) κ) (u : κ → ℝ) (e : Fin n → ℝ) : Prop :=
  ∃ C > 0, ∃ r > 0, ∀ x, IsTrajectory m u x → ∀ t, 0 ≤ t →
    ‖LTI.euclidean (x t - e)‖ ≤ C * Real.exp (-(r * t)) * ‖LTI.euclidean (x 0 - e)‖

@[powerlib_foundation] theorem isTrajectory_field {m : LTI.Model (Fin n) κ} {u : κ → ℝ}
    {x : ℝ → Fin n → ℝ} (hx : IsTrajectory m u x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt x (m.A *ᵥ x t + m.B *ᵥ u) (Ici 0) t :=
  hx t ht

/-- Hurwitz state matrix and an equilibrium for `u`: exponential convergence to it. -/
@[powerlib_domain] theorem exponentiallyConvergesTo_of_isHurwitz {m : LTI.Model (Fin n) κ}
    {u : κ → ℝ} {e : Fin n → ℝ} (he : m.IsEquilibrium u e)
    (hA : LinearSystems.IsHurwitz m.A) : ExponentiallyConvergesTo m u e := by
  obtain ⟨C, hC, r, hr, hb⟩ := LTI.exponentiallyStable_of_isHurwitz (m := m.autonomous) hA
  refine ⟨C, hC, r, hr, fun x hx t ht => ?_⟩
  have hy := StateSpacePassivity.trajectory_shift he hx
  have h1 : x t - e = m.response (x 0 - e) t :=
    StateSpacePassivity.trajectory_eq_response m hy ht
  have h2 := hb (LTI.response m.autonomous (x 0 - e)) (LTI.response_solves _ _) t ht
  rw [LTI.response_initial, LTI.Model.response_autonomous] at h2
  rw [h1]
  exact h2

/-- Exponential convergence implies convergence of the state. -/
@[powerlib_foundation] theorem tendsto_of_exponentiallyConvergesTo {m : LTI.Model (Fin n) κ}
    {u : κ → ℝ} {e : Fin n → ℝ} (h : ExponentiallyConvergesTo m u e)
    {x : ℝ → Fin n → ℝ} (hx : IsTrajectory m u x) : Tendsto x atTop (𝓝 e) := by
  obtain ⟨C, -, r, hr, hb⟩ := h
  have hexp : Tendsto (fun t : ℝ => C * Real.exp (-(r * t)) * ‖LTI.euclidean (x 0 - e)‖)
      atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-(r * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
    simpa using (he.const_mul C).mul_const ‖LTI.euclidean (x 0 - e)‖
  have hE : Tendsto (fun t => LTI.euclidean (x t - e)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact hb x hx t ht
  have hc : Continuous (fun y : PiLp 2 (fun _ : Fin n => ℝ) => (WithLp.equiv 2 _) y) :=
    PiLp.continuous_ofLp 2 _
  have h0 : Tendsto (fun t => x t - e) atTop (𝓝 0) := by
    have := (hc.tendsto 0).comp hE
    simpa [Function.comp_def, LTI.euclidean] using this
  simpa using h0.add_const e

/-- Componentwise convergence (for instance of the frequency deviation `x t 0`). -/
@[powerlib_foundation] theorem tendsto_apply_of_exponentiallyConvergesTo
    {m : LTI.Model (Fin n) κ} {u : κ → ℝ} {e : Fin n → ℝ} (h : ExponentiallyConvergesTo m u e)
    {x : ℝ → Fin n → ℝ} (hx : IsTrajectory m u x) (i : Fin n) :
    Tendsto (fun t => x t i) atTop (𝓝 (e i)) :=
  ((continuous_apply i).tendsto e).comp (tendsto_of_exponentiallyConvergesTo h hx)

end powerlib.Frequency
