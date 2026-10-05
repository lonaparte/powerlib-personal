import theorem.Dynamics.Autonomous
import theorem.Dynamics.Existence
import theorem.Dynamics.ExponentialStability

/-! Complete large-signal stability for autonomous nonlinear state-space systems.
Unlike convergence predicates over pre-existing trajectories, the public GAS
predicate includes global solution existence through every initial condition.
The strict Lyapunov criterion needs only C¹ regularity of the original field;
global Lipschitz continuity is not an assumption.
-/

noncomputable section
namespace powerlib.Dynamics

variable {n : ℕ}

/-- Equilibrium, forward completeness, Lyapunov stability, and attraction from
every initial state. There is no restriction on the perturbation amplitude. -/
def GloballyAsymptoticallyStable (f : State n → State n) (equilibrium : State n) : Prop :=
  f equilibrium = 0 ∧ ForwardComplete f ∧
    TrajectoryGloballyAsymptoticallyStable f equilibrium

/-- A strict proper energy proves the complete nonlinear system globally stable. -/
@[powerlib_domain, aesop norm forward (immediate := [hn, hf, hV])] theorem globallyAsymptoticallyStable_of_strictLyapunov
    {f : State n → State n} {V : State n → ℝ} {equilibrium : State n}
    (hn : 0 < n) (hf : ContDiff ℝ 1 f)
    (hV : IsStrictLyapunovFunction f V equilibrium) :
    GloballyAsymptoticallyStable f equilibrium := by
  have hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0 := by
    intro x
    by_cases hx : x = equilibrium
    · subst x
      simp [hV.hequil]
    · exact (hV.hLie_neg x hx).le
  exact ⟨hV.hequil,
    forwardComplete_of_compact_sublevel hf
      (hV.hV_c1.differentiable (by norm_num)) hdec hV.hbounded_sublevel,
    lyapunov_asymptotic_stable hn hV hf.continuous⟩

/-- The usual radial-unboundedness form of the complete large-signal criterion. -/
@[powerlib_domain, aesop norm forward (immediate := [hn, hf, hV])] theorem globallyAsymptoticallyStable_of_radialLyapunov
    {f : State n → State n} {V : State n → ℝ} {equilibrium : State n}
    (hn : 0 < n) (hf : ContDiff ℝ 1 f)
    (hV : IsAsymptoticLyapunovFunction f V equilibrium) :
    GloballyAsymptoticallyStable f equilibrium :=
  globallyAsymptoticallyStable_of_strictLyapunov hn hf (asymptotic_implies_strict hV)

/-- An exponential decay certificate is also a strict proper Lyapunov certificate. -/
@[powerlib_foundation, aesop norm forward (immediate := [c])] theorem QuadraticDecayCertificate.strictLyapunov
    {f : State n → State n} {V : State n → ℝ} {equilibrium : State n}
    (c : QuadraticDecayCertificate f V equilibrium) :
    IsStrictLyapunovFunction f V equilibrium where
  hcont := c.smooth.continuous
  hV_c1 := c.smooth
  hzero := c.equilibrium_value
  hpos := by
    intro x hx
    have hnorm : 0 < ‖x - equilibrium‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    exact (mul_pos c.lower_pos (sq_pos_of_pos hnorm)).trans_le (c.lower_bound x)
  hequil := c.equilibrium_field
  hLie_neg := by
    intro x hx
    have hnorm : 0 < ‖x - equilibrium‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have hpos : 0 < V x :=
      (mul_pos c.lower_pos (sq_pos_of_pos hnorm)).trans_le (c.lower_bound x)
    exact (c.dissipation x).trans_lt (mul_neg_of_neg_of_pos (neg_neg_of_pos c.rate_pos) hpos)
  hbounded_sublevel := c.compact_sublevel

@[powerlib_domain, aesop norm forward (immediate := [c, hn, hf])] theorem QuadraticDecayCertificate.globallyAsymptoticallyStable
    {f : State n → State n} {V : State n → ℝ} {equilibrium : State n}
    (c : QuadraticDecayCertificate f V equilibrium) (hn : 0 < n)
    (hf : ContDiff ℝ 1 f) : GloballyAsymptoticallyStable f equilibrium :=
  globallyAsymptoticallyStable_of_strictLyapunov hn hf c.strictLyapunov

end powerlib.Dynamics
