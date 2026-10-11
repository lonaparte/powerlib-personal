import theorem.Criteria.Hurwitz2

/-! # Single-input single-output LTI helpers (foundation)

Shared helpers for the converter current-loop, DC-link and feedforward modules
(`theorem/CurrentControl/`, `theorem/DCLink/`). Nothing here describes a physical system.

* `transfer_fin_one`, `transfer_fin_two`: closed forms of `LTI.transfer` for one- and two-state
  single-input single-output realizations `⟨A, B, C, D⟩` (input and output index `Fin 1`), off
  the characteristic roots. These are plain resolvent computations (adjugate of a 1×1 / 2×2
  matrix).
* `negOutput`, `transfer_negOutput`: reversing the output sign of a realization negates its
  transfer matrix. With the output read as a port current, this is the `Y^IN = −Y^OUT`
  translation between the IN-positive and OUT-positive current conventions
  (work-sync `theory/T-gfl-impedance.md` §1.4 / §2.2, `conventions.md` §D8).
* `isTrajectory_sub_equilibrium`: a solution of `ẋ = A x + B u` with constant input `u` minus an
  equilibrium `e` is a zero-input trajectory.
* `tendsto_of_exponentiallyStable`: on an exponentially stable autonomous model every
  trajectory tends to `0` componentwise.

Source: standard state-space algebra, used by work-sync `theory/T-gfl-control.md` §1.4,
`theory/T-gfl-impedance.md` §1.4–§1.5, `theory/T-voltage-feedforward.md` §2.2,
`theory/T-vsc-dc-voltage-control.md` §1.4.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter
open scoped Topology

/-- Transfer function of a one-state SISO realization `⟨[a], [b], [c], [d]⟩`:
`c b / (s − a) + d` for `s ≠ a`. -/
@[powerlib_foundation] theorem transfer_fin_one (a b c d : ℝ) {s : ℂ} (hs : s - a ≠ 0) :
    LTI.transfer (⟨!![a], !![b], !![c], !![d]⟩ : LTI.Model (Fin 1) (Fin 1)) s 0 0 =
      (c : ℂ) * b / (s - a) + d := by
  simp [LTI.transfer, LTI.characteristicMatrix, Matrix.mul_apply]
  field_simp

/-- Characteristic determinant of a 2×2 state matrix in the literal form `!![a, b; c, d]`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_of (a b c d : ℝ) (s : ℂ) :
    (LTI.characteristicMatrix !![a, b; c, d] s).det = (s - a) * (s - d) - (b : ℂ) * c := by
  simp [LTI.characteristicMatrix, Matrix.det_fin_two]

/-- Transfer function of a two-state SISO realization, off the characteristic roots. -/
@[powerlib_foundation] theorem transfer_fin_two (a b c d b1 b2 c1 c2 d0 : ℝ) {s : ℂ}
    (hs : (s - a) * (s - d) - (b : ℂ) * c ≠ 0) :
    LTI.transfer (⟨!![a, b; c, d], !![b1; b2], !![c1, c2], !![d0]⟩ :
      LTI.Model (Fin 2) (Fin 1)) s 0 0 =
      ((c1 : ℂ) * ((s - d) * b1 + b * b2) + c2 * (c * b1 + (s - a) * b2)) /
        ((s - a) * (s - d) - b * c) + d0 := by
  simp only [LTI.transfer, Matrix.inv_def, Ring.inverse_eq_inv', det_characteristicMatrix_of]
  simp [LTI.characteristicMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

section Sign

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- The same realization with the output (and feedthrough) sign reversed. -/
def negOutput (m : LTI.Model ι κ) : LTI.Model ι κ := ⟨m.A, m.B, -m.C, -m.D⟩

/-- Reversing the output sign negates the transfer matrix. Read with the output as a port
current: `Y^IN(s) = −Y^OUT(s)`. -/
@[powerlib_foundation] theorem transfer_negOutput (m : LTI.Model ι κ) (s : ℂ) :
    LTI.transfer (negOutput m) s = -LTI.transfer m s := by
  simp only [LTI.transfer, negOutput, LTI.complexify_neg, Matrix.neg_mul, neg_add]

omit [Fintype ι] [DecidableEq ι] in
@[powerlib_foundation] theorem negOutput_negOutput (m : LTI.Model ι κ) :
    negOutput (negOutput m) = m := by
  simp [negOutput]

end Sign

section Trajectory

variable {n : ℕ} {κ : Type*} [Fintype κ]

/-- A solution with constant input, shifted by an equilibrium, is a zero-input trajectory. -/
@[powerlib_foundation] theorem isTrajectory_sub_equilibrium (m : LTI.Model (Fin n) κ)
    {u : κ → ℝ} {e : Fin n → ℝ} (he : m.IsEquilibrium u e) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (m.field (x t) u) t) :
    LTI.IsTrajectory m.autonomous (fun t => x t - e) := by
  intro t
  have h := (hx t).sub_const e
  rw [LTI.Model.field_shift he] at h
  simpa [LTI.Model.autonomous_field, LTI.Model.field, LTI.Model.operator_apply] using h

/-- Every trajectory of an exponentially stable autonomous LTI model tends to zero. -/
@[powerlib_foundation] theorem tendsto_of_exponentiallyStable {m : LTI.AutonomousModel n}
    (hm : LTI.ExponentiallyStable m) {y : ℝ → Fin n → ℝ} (hy : LTI.IsTrajectory m y)
    (j : Fin n) : Tendsto (fun t => y t j) atTop (𝓝 0) := by
  obtain ⟨K, -, r, hr, hb⟩ := hm
  have he : Tendsto (fun t : ℝ => K * Real.exp (-(r * t)) * ‖LTI.euclidean (y 0)‖)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => Real.exp (-(r * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
    simpa using (h0.const_mul K).mul_const ‖LTI.euclidean (y 0)‖
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  calc ‖y t j‖ = ‖(LTI.euclidean (y t)) j‖ := by simp [LTI.euclidean]
    _ ≤ ‖LTI.euclidean (y t)‖ := PiLp.norm_apply_le _ j
    _ ≤ _ := hb y hy t ht

/-- Constant-input solutions of an exponentially stable model converge to the equilibrium. -/
@[powerlib_foundation] theorem tendsto_equilibrium (m : LTI.Model (Fin n) κ)
    (hm : LTI.ExponentiallyStable m.autonomous)
    {u : κ → ℝ} {e : Fin n → ℝ} (he : m.IsEquilibrium u e) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (m.field (x t) u) t) (j : Fin n) :
    Tendsto (fun t => x t j) atTop (𝓝 (e j)) := by
  have h := tendsto_of_exponentiallyStable hm (isTrajectory_sub_equilibrium m he hx) j
  simpa using h.add_const (e j)

end Trajectory

end powerlib.CurrentControl
