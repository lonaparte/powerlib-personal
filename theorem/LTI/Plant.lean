import theorem.Linear.Transfer
import theorem.Linear.Stability

/-! # Single-input single-output plant helpers (foundation)

Library-owned LTI plant lemmas (the codex `Linear/` layer is not modified), shared by the converter
current-loop, DC-link and feedforward modules. Nothing here describes a physical system.

* `transfer_fin_one`, `transfer_fin_two`: closed forms of `Linear.transfer` for one- and
  two-state single-input single-output plants `⟨A, B, C, D⟩` (one port), off the
  characteristic roots. These are plain resolvent computations (adjugate of a 1×1 / 2×2
  matrix).
* `negOutput`, `transfer_negOutput`: reversing the output sign of a plant negates its transfer
  matrix. With the output read as a port current, this is the `Y^IN = −Y^OUT` translation
  between the IN-positive and OUT-positive current conventions (work-sync
  `theory/T-gfl-impedance.md` §1.4 / §2.2, `conventions.md` §D8).
* `tendsto_equilibrium`: under a constant input with an equilibrium `e`, every forward-complete
  solution of a plant with a Hurwitz state matrix converges to `e` (the hub's global asymptotic
  stability, `Linear.globallyAsymptoticallyStable_of_isHurwitz`, about the shifted
  equilibrium). It replaces the former `isTrajectory_sub_equilibrium`,
  `tendsto_of_exponentiallyStable` and `tendsto_equilibrium` on the deleted `LTI` models.

The spectral `Family` templates built on these plants are in `theorem/Spectral/Family.lean`.

Source: standard state-space algebra, used by work-sync `theory/T-gfl-control.md` §1.4,
`theory/T-gfl-impedance.md` §1.4–§1.5, `theory/T-voltage-feedforward.md` §2.2.
-/

noncomputable section
namespace powerlib.LTI
open Matrix Filter Linear LinearSystems
open scoped Topology

/-- Transfer function of a one-state SISO plant `⟨[a], [b], [c], [d]⟩`:
`c b / (s − a) + d` for `s ≠ a`. -/
@[powerlib_foundation] theorem transfer_fin_one (a b c d : ℝ) {s : ℂ} (hs : s - a ≠ 0) :
    transfer (⟨!![a], !![b], !![c], !![d]⟩ : Plant 1 1) s 0 0 =
      (c : ℂ) * b / (s - a) + d := by
  simp [transfer, characteristicMatrix, Matrix.mul_apply]
  field_simp

/-- Characteristic determinant of a 2×2 state matrix in the literal form `!![a, b; c, d]`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_of (a b c d : ℝ) (s : ℂ) :
    (characteristicMatrix !![a, b; c, d] s).det = (s - a) * (s - d) - (b : ℂ) * c := by
  simp [characteristicMatrix, Matrix.det_fin_two]

/-- Transfer function of a two-state SISO plant, off the characteristic roots. -/
@[powerlib_foundation] theorem transfer_fin_two (a b c d b1 b2 c1 c2 d0 : ℝ) {s : ℂ}
    (hs : (s - a) * (s - d) - (b : ℂ) * c ≠ 0) :
    transfer (⟨!![a, b; c, d], !![b1; b2], !![c1, c2], !![d0]⟩ : Plant 2 1) s 0 0 =
      ((c1 : ℂ) * ((s - d) * b1 + b * b2) + c2 * (c * b1 + (s - a) * b2)) /
        ((s - a) * (s - d) - b * c) + d0 := by
  simp only [transfer, Matrix.inv_def, Ring.inverse_eq_inv', det_characteristicMatrix_of]
  simp [characteristicMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

section Sign

variable {n p : ℕ}

/-- The same plant with the output (and feedthrough) sign reversed. -/
def negOutput (m : Plant n p) : Plant n p := ⟨m.A, m.B, -m.C, -m.D⟩

/-- Reversing the output sign negates the transfer matrix. Read with the output as a port
current: `Y^IN(s) = −Y^OUT(s)`. -/
@[powerlib_foundation] theorem transfer_negOutput (m : Plant n p) (s : ℂ) :
    transfer (negOutput m) s = -transfer m s := by
  simp only [transfer, negOutput, complexify_neg, Matrix.neg_mul, neg_add]

@[powerlib_foundation] theorem negOutput_negOutput (m : Plant n p) :
    negOutput (negOutput m) = m := by
  simp [negOutput]

end Sign

section Trajectory

variable {n p : ℕ}

/-- Constant-input solutions of a plant with a Hurwitz state matrix converge to the
equilibrium: generic foundation, the hub's global asymptotic stability about `e`. -/
@[powerlib_foundation] theorem tendsto_equilibrium (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ : ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Set.Ici t₀)) :
    Tendsto x atTop (𝓝 e) := by
  rw [M.inputField_eq he] at hx
  exact (globallyAsymptoticallyStable_of_isHurwitz e hA).2.2.2 t₀ x hx

/-- Componentwise form, for a solution given by its derivative at every time. -/
@[powerlib_foundation] theorem tendsto_equilibrium_apply (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} (hx : ∀ t, HasDerivAt x (M.inputField u (x t)) t)
    (j : Fin n) : Tendsto (fun t => x t j) atTop (𝓝 (e j)) := by
  have h := tendsto_equilibrium M hA he (t₀ := 0) fun t _ => (hx t).hasDerivWithinAt
  exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.tendsto
    e).comp h

end Trajectory

end powerlib.LTI
