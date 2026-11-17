import theorem.GridTiedConverter.GFL.DCLink.FourState
import theorem.GridTiedConverter.GFL.DCLink.PLLDC.Boundary

/-! # Four-state GFL: the closed quartic Routh region is necessary

Model boundary.
The four-state GFL models of `theorem/GridTiedConverter/GFL/DCLink/FourState.lean`, read as the
PLL–DC model (`FourState.Model.toPLLDC`, `PLLDC.family`; scaffold
`theorem/GridTiedConverter/GFL/DCLink/FourStatePLLDC.agda`): a single grid-following VSC on an
infinite ac source of amplitude `V₀` behind a lossless reactance `X_g`, balanced averaged dq model
in the PLL frame, algebraic network, ideal current loop, constant grid angle, continuous time;
states in order `θ` (PLL error angle), `x` (PLL integrator), `V` (dc-bus voltage, p.u.), `η`
(dc-voltage PI integrator); port current IN-positive, absorbed power `P_abs = (3/2) v_d i_d`,
`i_q = 0`; the full nonlinear field with its `1 / V` term, read at the selected operating point
`(θ₀, 0, 1, 0)`. The trajectory argument is made on the note's field, which is the PLL–DC model's
in the coordinates of the integrator flip (`FourState.field_eq_transport`), and is read as a
statement about the PLL–DC image. No PWM, delay, limiter, line resistance or current-loop
dynamics.

Source: work-sync `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2, §2.3 (the
four-state model); every inequality is checked here by the Lean kernel.

Results.
* `closedRouth_of_mem_den_lyapunovStable` (hence also for local asymptotic stability, through
  `Spectral.den_las_subset_lyapunovStable`): every four-state model whose PLL–DC image is
  Lyapunov stable has `C ≠ 0` (otherwise the image is unstable,
  `PLLDC.mem_den_unstable_of_Cdc_eq_zero`), an equilibrium at the selected point (`IsEq`), and
  quartic coefficients in the closed Routh region `a₃, a₂, a₁, a₀ ≥ 0`, `a₁² + a₃² a₀ ≤ a₃ a₂ a₁`
  (a strict violation is a strict violation of the PLL–DC model's 4×4 Routh conditions and gives
  instability, `PLLDC.mem_den_unstable_of_violation`). With
  `FourState.mem_den_locallyExponentiallyStable_of_routh`, the Lyapunov and local asymptotic
  denotations of the four-state models therefore lie between the strict and the closed Routh sets
  (with equilibrium and `C ≠ 0`).
* On the Routh boundary itself the PLL–DC model's requirement language decides nothing: its
  Lyapunov, local asymptotic and instability sentences are inexpressible in it
  (`PLLDC.realize_ne_den_lyapunovStable`, `PLLDC.realize_ne_den_locallyAsymptoticallyStable`,
  `PLLDC.realize_ne_den_unstable`, witnesses of the PLL–DC model's own Routh boundary in
  `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Boundary.lean`). The weak-focus mechanism of the
  four-state models (a coupling-induced negative first Lyapunov coefficient with `X_g ≠ 0`) is no
  longer certified in the library.

Family and connection conclusions.
No family: the result is a connection statement on `PLLDC.family` at the images of four-state
models (an inclusion of the preimage of its Lyapunov denotation).

Remaining exact set (not characterized here). Let `S` be the four-state models with
`{IsEq, C ≠ 0, strict Routh conditions}` and `B` those with `{IsEq, C ≠ 0, closed Routh
conditions}` not in `S`, the Routh boundary. For `P` Lyapunov or local asymptotic stability, the
preimage of `den P` is `S ∪ (den P ∩ B)`, and the instability denotation is the complement of the
Lyapunov one. On `B` membership is decided by the nonlinear terms (first Lyapunov coefficients at
Hopf points, centre-manifold reductions at zero eigenvalues, higher codimension).
-/

noncomputable section
namespace powerlib.GFL.DCLink.FourStateBoundary
open FourState Set

/-! ## Reading the note's field as the PLL–DC model (implementation evidence) -/

/-- A flow sentence of the PLL–DC image is the sentence of the note's field at the operating
point (`FourState.field_eq_transport`, `Dynamics.holds_transport_iff`). -/
@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff' {m : Model} {P : Flow.Property} :
    m.toPLLDC ∈ PLLDC.family.den (.flow P) ↔
      P.holds (FourState.field m.params) (opPoint m.θ) := by
  have h : m.toPLLDC ∈ PLLDC.family.den (.flow P) ↔
      P.holds m.params.toPLLDC.field (opPoint m.θ) :=
    Spectral.mem_den_flow_iff_shift (f := fun m : PLLDC.Model => m.p.field)
      (pt := PLLDC.Model.x) PLLDC.family_isAutonomous
  have hpt : Dynamics.affineCoord integratorFlip 0 (opPoint m.θ) = opPoint m.θ := by
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [Dynamics.affineCoord, opPoint]
  rw [h, field_eq_transport]
  conv_rhs => rw [← hpt]
  exact (Dynamics.holds_transport_iff integratorFlip 0 P).symm

/-! ## Necessary conditions: the closed Routh region -/

/-- **Necessary condition (closed Routh region).** A four-state model whose PLL–DC image is
Lyapunov stable has `C ≠ 0` (without capacitance the image is unstable,
`PLLDC.mem_den_unstable_of_Cdc_eq_zero`), its operating point is an equilibrium (`IsEq`; the
note's field is `C¹` near it, `field_contDiffOn`), and the quartic coefficients of
`det(λI − A₀)` lie in the closure of the Routh region: `a₃, a₂, a₁, a₀ ≥ 0` and
`a₁² + a₃² a₀ ≤ a₃ a₂ a₁` (a strict violation is one of the PLL–DC model's 4×4 Routh conditions,
`Criteria.routhViolationFin4_iff_of_det_characteristicMatrix_quartic`, and gives instability,
`PLLDC.mem_den_unstable_of_violation`). Hence the same holds for local asymptotic and local
exponential stability. -/
@[tmio TM, powerlib_domain] theorem closedRouth_of_mem_den_lyapunovStable :
    connection% (Model.toPLLDC ⁻¹' PLLDC.family.den (.flow .lyapunovStable) ⊆
      {m : Model | IsEq m.params m.θ ∧ m.params.C ≠ 0 ∧ 0 ≤ a3 m.params m.θ ∧
        0 ≤ a2 m.params m.θ ∧ 0 ≤ a1 m.params m.θ ∧ 0 ≤ a0 m.params m.θ ∧
        a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ ≤
          a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ}) := by
  unfold powerlib.TMIO.Statement
  intro m h
  have h' : m.toPLLDC ∈ PLLDC.family.den (.flow .lyapunovStable) := h
  have hns : m.toPLLDC ∉ PLLDC.family.den (.flow .unstable) := fun hu => by
    have hn := Spectral.not_mem_den_lyapunovStable_of_unstable hu
    unfold powerlib.TMIO.Statement at hn
    exact hn h'
  have hC : m.params.C ≠ 0 := fun hC => by
    have hu := PLLDC.mem_den_unstable_of_Cdc_eq_zero m.toPLLDC hC
    unfold powerlib.TMIO.Statement at hu
    exact hns hu
  have h0 : FourState.field m.params (opPoint m.θ) = 0 :=
    Dynamics.isEquilibrium_of_lyapunovStable_local PLLDC.Params.isOpen_nonzeroVdc
      (by simp [PLLDC.Params.nonzeroVdc, opPoint]) (field_contDiffOn m.params)
      (mem_den_flow_iff'.mp h')
  have heq : IsEq m.params m.θ := (isEq_iff m.params hC m.θ).mp h0
  have hnot : ¬ (a3 m.params m.θ < 0 ∨ a2 m.params m.θ < 0 ∨ a1 m.params m.θ < 0 ∨
      a0 m.params m.θ < 0 ∨ a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ <
        a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ) := fun hv => by
    have hviol := (Criteria.routhViolationFin4_iff_of_det_characteristicMatrix_quartic _
      (det_characteristicMatrix_jacobian m.params heq.1)).mpr hv
    have hu := PLLDC.mem_den_unstable_of_violation m.toPLLDC
      (by norm_num [Model.toPLLDC, Params.toPLLDC]) ((meets_equilibrium_iff m hC).mpr heq) hviol
    unfold powerlib.TMIO.Statement at hu
    exact hns hu
  push Not at hnot
  exact ⟨heq, hC, hnot⟩

end powerlib.GFL.DCLink.FourStateBoundary
