import theorem.GridTiedConverter.GFM.Matching.StiffGrid
import theorem.Criteria.Hurwitz
import theorem.Criteria.Routh4
import theorem.Dynamics.ConverseLinearization

/-! # Direct angle control on a stiff grid

The direct-angle-control variant of matching control: the synchronizing term is moved from the
DC current control into the angle dynamics, `θ' = η u_dc − κ ∇S` (24a), and the DC current
control keeps only the P-control and the steady-state feedforward (24b). This module formalizes
the closed loop with the L filter and the stiff grid, its equilibria and its local stability.

Model boundary.
* The converter, filter, grid and frame of `theorem.GridTiedConverter.GFM.Matching.StiffGrid`
  (averaged converter, DC capacitor `C_dc` and conductance `G_dc`, L filter `L_s`, `R_s`, stiff
  grid `v₀`, `ω₀ = η u*_dc`, grid `dq` frame, `i_s` from the grid into the converter; no PWM,
  delay, current or modulation limits), whose parameters are the field `base`; a second
  parameter, the angle-feedback gain `κ` of (24a) (implemented in software, independent of
  `K_p`). With `∇S(θ_dq) = k sin θ_dq` (`k = L_s μ u* v₀/N`) the angle feedback is `κa sin θ_dq`,
  `κa = κ k`. State `(θ_dq, u_dc, i_d, i_q) ∈ ℝ⁴`, continuous time, autonomous:
  `θ_dq' = η u_dc − ω₀ − κa sin θ_dq`,
  `C_dc u_dc' = −G_dc u_dc + i_dc + μ (−sin θ_dq, cos θ_dq)ᵀ i_dq`,
  `L_s i_dq' = −Z_s i_dq + v₀ e₂ − μ (−sin θ_dq, cos θ_dq) u_dc`,
  `i_dc = −K_p ũ_dc + G_dc u*_dc + î_x(θ_dq)` (`Model.field`).
* Operating point `(0, u*_dc, î_dq(0))` (`MatchingStiffGrid.Model.point`). Parameter ranges as
  stated in each result.
* Excluded: the reduced (inductor-transient-free) model (21) with (24), which the source uses for
  its remark that the angle dynamics are first order with the equilibria of (21); PI/PID DC
  control in place of (24b).

Source: C. Arghir, F. Dörfler, "The electronic realization of synchronous machines: model
matching, angle tracking, and energy shaping techniques", IEEE Trans. Power Electron. 35(4)
(2020) 4398–4410, author version (ETH Research Collection, `bare_jrnl.pdf`, text layer read):
§III-D "Direct angle control", eq. (24a) `dθ/dt = η u_dc − κ ∇S`, (24b)
`i_dc = −K_p ũ_dc + G_dc u*_dc + î_x`, with the model (4), (11) and the internal model (14)–(16)
of §III. The source states no stability result for (24); work-sync
`theory/papers/@arghir2020matching.md` ("direct angle control 变体").

Results.
* Static: `field_eq_zero_of_kappaA_mul_sin_eq_zero` (every `θ_dq` with `κa sin θ_dq = 0` gives an
  equilibrium `(θ_dq, u*, î(θ_dq))`), `eq_of_field_eq_zero` (**these are all equilibria** when
  `G_dc + K_p + μ² R_s/N ≠ 0`), `field_point`, `field_add_two_pi`.
* Linearization: `hasFDerivAt_field_point`, `jac`, `det_jac`
  (`det J = κa ((G_dc+K_p) N + R_s μ²)/(C_dc L_s²)`), the Lyapunov matrix `lyap`
  (`β δθ² + C_dc δu² + L_s ‖δi − î'(0) δθ‖²`, `β = 2 κa (G_dc+K_p)/η²`; `lyap_form`) and its
  dissipation as a sum of squares (`lyap_jac`), `jac_isHurwitz` (**`κa > 0` and the stiff-grid
  condition `margin > 0` give a Hurwitz linearization, with no condition on the sign of
  `μ u* v₀`**), `jac_isHurwitz_iff` (under `margin > 0`, Hurwitz iff `κa > 0`, by Stodola:
  `Criteria.charpoly_coeff_pos_of_isHurwitz`).

Family and connection conclusions.
* `family : Family Model Requirement 4 0`: the translated loops (`family_isAutonomous`).
  Requirements `physical` (`C_dc, L_s, R_s > 0`), `angleFeedback` (`κa > 0`), `antiFeedback`
  (`κa < 0`), `damped` (`margin > 0`), `matching` (`η ≠ 0`); translation `Spectral.localTable`:
  Lyapunov, local asymptotic and local exponential stability into
  `{physical, angleFeedback, damped, matching}`, instability into
  `{physical, antiFeedback, damped}`, passivity into nothing, the rest into the whole, inconsistent,
  language (`realize_univ`). Connection results: `chain_le_semantics` (through
  `Spectral.chain_le_semantics_of_jacobian`; instability from `det J < 0`),
  `mem_den_locallyExponentiallyStable_iff` (**decided**: with `C_dc, L_s, R_s > 0`, `η ≠ 0`,
  `margin > 0`, locally exponentially stable iff `κa > 0`; converse linearization
  `Dynamics.isHurwitz_of_locallyExponentiallyStable`),
  `not_mem_den_globallyAsymptoticallyStable`, `not_mem_den_globallyExponentiallyStable`,
  `exact_globallyAsymptoticallyStable`, `exact_globallyExponentiallyStable`.
* Not proved: global or LaSalle-type results (the source proves none; the stiff-grid energy is
  not dissipated by (24), whose DC row carries no synchronizing term), and the exact
  stability region below `margin = 0`.
-/

noncomputable section
namespace powerlib.GFM.Matching.DirectAngle
open powerlib.Dynamics (State)
open Matrix

/-- Direct angle control on a stiff grid. -/
structure Model where
  /-- The stiff-grid converter, filter, grid and DC control gains. -/
  base : MatchingStiffGrid.Model
  /-- The gain `κ` of the angle feedback `θ' = η u_dc − κ ∇S` (24a). -/
  κ : ℝ

namespace Model
variable (m : Model)

/-- The angle-feedback gain: `κ ∇S(θ) = κa sin θ` (`∇S = k sin θ`). -/
def κa : ℝ := m.κ * m.base.k

/-- The DC current control (24b): no synchronizing term. -/
def idc (x : State 4) : ℝ :=
  -m.base.Kp * (x 1 - m.base.ustar) + m.base.Gdc * m.base.ustar + m.base.ixHat (x 0)

/-- The closed loop (4), (11), (24) in the grid `dq` frame, state `(θ_dq, u_dc, i_d, i_q)`. -/
def field (x : State 4) : State 4 :=
  WithLp.toLp 2 ![
    m.base.η * x 1 - m.base.ω0 - m.κa * Real.sin (x 0),
    (-m.base.Gdc * x 1 + m.idc x +
      m.base.μ * (-Real.sin (x 0) * x 2 + Real.cos (x 0) * x 3)) / m.base.Cdc,
    (-(m.base.Rs * x 2 - m.base.ω0 * m.base.Ls * x 3) - m.base.μ * (-Real.sin (x 0)) * x 1) /
      m.base.Ls,
    (-(m.base.ω0 * m.base.Ls * x 2 + m.base.Rs * x 3) + m.base.v0 -
      m.base.μ * Real.cos (x 0) * x 1) / m.base.Ls]

end Model

/-- Every `θ_dq` with `κa sin θ_dq = 0` gives an equilibrium `(θ_dq, u*, î(θ_dq))`: the
equilibria of (21). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_of_kappaA_mul_sin_eq_zero (m : Model)
    (hN : m.base.N ≠ 0) {θ : ℝ} (h : m.κa * Real.sin θ = 0) :
    m.field (WithLp.toLp 2 ![θ, m.base.ustar, m.base.iHatD θ, m.base.iHatQ θ]) = 0 := by
  ext i
  fin_cases i
  · simp only [Model.field, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, MatchingStiffGrid.Model.ω0, Fin.zero_eta, Fin.isValue]
    linear_combination -h
  · simp only [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue,
      Fin.mk_one]
    ring
  · simp only [Model.field, MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue,
      Fin.reduceFinMk]
    field_simp
    simp only [MatchingStiffGrid.Model.N]
    ring
  · simp only [Model.field, MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue,
      Fin.reduceFinMk]
    field_simp
    simp only [MatchingStiffGrid.Model.N]
    ring

/-- The stiff-grid operating point is an equilibrium. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_point (m : Model) (hN : m.base.N ≠ 0) :
    m.field m.base.point = 0 := by
  simpa [MatchingStiffGrid.Model.point] using
    field_eq_zero_of_kappaA_mul_sin_eq_zero m hN (θ := 0) (by simp)

/-- **These are all equilibria**: with `G_dc + K_p + μ² R_s/N ≠ 0` every equilibrium has
`u_dc = u*`, `i_dq = î(θ_dq)` and `κa sin θ_dq = 0`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem eq_of_field_eq_zero (m : Model) (hN : m.base.N ≠ 0)
    (hL : m.base.Ls ≠ 0) (hC : m.base.Cdc ≠ 0)
    (hg : m.base.Gdc + m.base.Kp + m.base.μ ^ 2 * m.base.Rs / m.base.N ≠ 0) {x : State 4}
    (hx : m.field x = 0) :
    x 1 = m.base.ustar ∧ x 2 = m.base.iHatD (x 0) ∧ x 3 = m.base.iHatQ (x 0) ∧
      m.κa * Real.sin (x 0) = 0 := by
  have r0 := congrArg (fun z : State 4 => z 0) hx
  have r1 := congrArg (fun z : State 4 => z 1) hx
  have r2 := congrArg (fun z : State 4 => z 2) hx
  have r3 := congrArg (fun z : State 4 => z 3) hx
  simp only [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
    MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply] at r0 r1 r2 r3
  rw [div_eq_zero_iff, or_iff_left hC] at r1
  rw [div_eq_zero_iff, or_iff_left hL] at r2 r3
  set s := Real.sin (x 0)
  set c := Real.cos (x 0)
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq (x 0)
  set B := m.base
  -- the current errors
  have e2 : x 2 - B.cD c s = B.μ * (x 1 - B.ustar) * (B.Rs * s - B.ω0 * B.Ls * c) / B.N := by
    simp only [MatchingStiffGrid.Model.cD]
    field_simp
    simp only [MatchingStiffGrid.Model.N] at *
    linear_combination (-B.Rs) * r2 + (-(B.ω0 * B.Ls)) * r3
  have e3 : x 3 - B.cQ c s = -(B.μ * (x 1 - B.ustar) * (B.ω0 * B.Ls * s + B.Rs * c)) / B.N := by
    simp only [MatchingStiffGrid.Model.cQ]
    field_simp
    simp only [MatchingStiffGrid.Model.N] at *
    linear_combination (B.ω0 * B.Ls) * r2 + (-B.Rs) * r3
  have hx2 : x 2 = B.cD c s + B.μ * (x 1 - B.ustar) * (B.Rs * s - B.ω0 * B.Ls * c) / B.N := by
    linarith
  have hx3 : x 3 = B.cQ c s - B.μ * (x 1 - B.ustar) * (B.ω0 * B.Ls * s + B.Rs * c) / B.N := by
    rw [sub_eq_add_neg, ← neg_div]
    linarith
  have key : (x 1 - B.ustar) * (B.Gdc + B.Kp + B.μ ^ 2 * B.Rs / B.N) = 0 := by
    rw [hx2, hx3] at r1
    simp only [MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ] at r1
    field_simp at r1 ⊢
    linear_combination (-1) * r1 + (-(B.μ ^ 2 * B.Rs * (x 1 - B.ustar))) * hsc
  have hu : x 1 = B.ustar := by
    have := (mul_eq_zero.mp key).resolve_right hg
    linarith
  refine ⟨hu, ?_, ?_, ?_⟩
  · rw [hx2, hu, sub_self, mul_zero, zero_mul, zero_div, add_zero]
  · rw [hx3, hu, sub_self, mul_zero, zero_mul, zero_div, sub_zero]
  · rw [hu] at r0
    simp only [MatchingStiffGrid.Model.ω0] at r0
    linear_combination -r0


/-- The loop is `2π`-periodic in `θ_dq`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem field_add_two_pi (m : Model) (θ u id iq : ℝ) :
    m.field (WithLp.toLp 2 ![θ + 2 * Real.pi, u, id, iq]) =
      m.field (WithLp.toLp 2 ![θ, u, id, iq]) := by
  simp [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
    MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ]

/-! ## Linearization at the operating point -/

namespace Model
variable (m : Model)

/-- The Jacobian at the operating point `(0, u*, î(0))` (`hasFDerivAt_field_point`). -/
def jac : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-m.κa, m.base.η, 0, 0;
     m.base.μ ^ 2 * m.base.ustar * m.base.ω0 * m.base.Ls / (m.base.N * m.base.Cdc),
       -(m.base.Gdc + m.base.Kp) / m.base.Cdc, 0, m.base.μ / m.base.Cdc;
     m.base.μ * m.base.ustar / m.base.Ls, 0, -m.base.Rs / m.base.Ls, m.base.ω0;
     0, -m.base.μ / m.base.Ls, -m.base.ω0, -m.base.Rs / m.base.Ls]

/-- The angle weight `β = 2 κa (G_dc + K_p)/η²` of the quadratic Lyapunov function. -/
def β : ℝ := 2 * m.κa * (m.base.Gdc + m.base.Kp) / m.base.η ^ 2

/-- The quadratic Lyapunov function `β δθ² + C_dc δu² + L_s ‖δi − î'(0) δθ‖²` as a matrix. -/
def lyap : Matrix (Fin 4) (Fin 4) ℝ :=
  !![m.β + m.base.Ls * (m.base.p ^ 2 + m.base.q ^ 2), 0, -(m.base.Ls * m.base.p),
       -(m.base.Ls * m.base.q);
     0, m.base.Cdc, 0, 0;
     -(m.base.Ls * m.base.p), 0, m.base.Ls, 0;
     -(m.base.Ls * m.base.q), 0, 0, m.base.Ls]

end Model

@[tmio M, powerlib_domain] private theorem lyap_symm (m : Model) : m.lyapᵀ = m.lyap := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Model.lyap]

/-- The Lyapunov form. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem lyap_form (m : Model) (w : Fin 4 → ℝ) :
    w ⬝ᵥ (m.lyap *ᵥ w) = m.β * w 0 ^ 2 + m.base.Cdc * w 1 ^ 2 +
      m.base.Ls * ((w 2 - m.base.p * w 0) ^ 2 + (w 3 - m.base.q * w 0) ^ 2) := by
  simp [Model.lyap, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- **Dissipation of the linearization**, as a sum of squares:
`wᵀ P J w = −(R_s ‖ĩ + X î'(0)‖² + margin (δu − κa δθ/η)² + κa² (G_dc+K_p) δθ²/η²)`,
`ĩ = δi − î'(0) δθ`, `X = L_s (η δu − κa δθ)/(2R_s)`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem lyap_jac (m : Model) (hR : m.base.Rs ≠ 0)
    (hL : m.base.Ls ≠ 0) (hC : m.base.Cdc ≠ 0) (hη : m.base.η ≠ 0) (hN : m.base.N ≠ 0)
    (w : Fin 4 → ℝ) :
    w ⬝ᵥ (m.lyap *ᵥ (m.jac *ᵥ w)) =
      -(m.base.Rs * ((w 2 - m.base.p * w 0 +
            m.base.Ls * (m.base.η * w 1 - m.κa * w 0) / (2 * m.base.Rs) * m.base.p) ^ 2 +
          (w 3 - m.base.q * w 0 +
            m.base.Ls * (m.base.η * w 1 - m.κa * w 0) / (2 * m.base.Rs) * m.base.q) ^ 2) +
        m.base.margin * (w 1 - m.κa * w 0 / m.base.η) ^ 2 +
        m.κa ^ 2 * (m.base.Gdc + m.base.Kp) * w 0 ^ 2 / m.base.η ^ 2) := by
  simp [Model.lyap, Model.jac, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  simp only [Model.β, MatchingStiffGrid.Model.margin, MatchingStiffGrid.Model.p,
    MatchingStiffGrid.Model.q]
  field_simp
  simp only [MatchingStiffGrid.Model.N, MatchingStiffGrid.Model.ω0]
  ring


/-- **The linearization is Hurwitz** with angle feedback `κa > 0` under the stiff-grid damping
condition `margin > 0`, `C_dc, L_s, R_s > 0` and `η ≠ 0` — without any condition on the sign of
`μ u* v₀`. Proof: `lyap` is positive definite (`β > 0`) and the dissipation `lyap_jac` is
negative definite (`Criteria.re_neg_of_lyapunov`). Static evidence on the model, not a
connection conclusion. -/
@[tmio TM, powerlib_domain] theorem jac_isHurwitz (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hη : m.base.η ≠ 0) (hδ : 0 < m.base.margin)
    (hκ : 0 < m.κa) : LinearSystems.IsHurwitz m.jac := by
  have hN : 0 < m.base.N := MatchingStiffGrid.N_pos m.base hR.ne'
  have hX : 0 ≤ m.base.μ ^ 2 * m.base.ω0 ^ 2 * m.base.Ls ^ 2 / (4 * m.base.Rs * m.base.N) := by
    positivity
  have hg : 0 < m.base.Gdc + m.base.Kp := by
    have : m.base.margin = m.base.Gdc + m.base.Kp -
        m.base.μ ^ 2 * m.base.ω0 ^ 2 * m.base.Ls ^ 2 / (4 * m.base.Rs * m.base.N) := rfl
    linarith
  have hβ : 0 < m.β := by unfold Model.β; positivity
  intro lam v hv hev
  rw [neg_zero]
  refine Criteria.re_neg_of_lyapunov (lyap_symm m) (fun w hw => ?_) (fun w hw => ?_) hv hev
  · rw [lyap_form]
    by_contra hle
    push Not at hle
    have a0 : 0 ≤ m.β * w 0 ^ 2 := by positivity
    have a1 : 0 ≤ m.base.Cdc * w 1 ^ 2 := by positivity
    have a2 : 0 ≤ m.base.Ls * ((w 2 - m.base.p * w 0) ^ 2 + (w 3 - m.base.q * w 0) ^ 2) := by
      positivity
    have h0 : w 0 = 0 := by
      have : m.β * w 0 ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left hβ.ne')
    have h1 : w 1 = 0 := by
      have : m.base.Cdc * w 1 ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left hC.ne')
    have h23 : (w 2 - m.base.p * w 0) ^ 2 + (w 3 - m.base.q * w 0) ^ 2 = 0 := by
      have : m.base.Ls * ((w 2 - m.base.p * w 0) ^ 2 + (w 3 - m.base.q * w 0) ^ 2) = 0 := by
        linarith
      exact (mul_eq_zero.mp this).resolve_left hL.ne'
    simp only [h0, mul_zero, sub_zero] at h23
    have h2 : w 2 = 0 := by nlinarith [sq_nonneg (w 2), sq_nonneg (w 3)]
    have h3 : w 3 = 0 := by nlinarith [sq_nonneg (w 2), sq_nonneg (w 3)]
    apply hw
    funext j
    fin_cases j <;> simp [h0, h1, h2, h3]
  · rw [lyap_jac m hR.ne' hL.ne' hC.ne' hη hN.ne']
    rw [neg_lt_zero]
    by_cases h0 : w 0 = 0
    · by_cases h1 : w 1 = 0
      · have h23 : w 2 ≠ 0 ∨ w 3 ≠ 0 := by
          by_contra h
          push Not at h
          apply hw
          funext j
          fin_cases j <;> simp [h0, h1, h.1, h.2]
        rw [h0, h1]
        simp only [mul_zero, sub_zero, sub_self, zero_div, add_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        rcases h23 with h | h
        · nlinarith [sq_nonneg (w 3), sq_pos_of_ne_zero h]
        · nlinarith [sq_nonneg (w 2), sq_pos_of_ne_zero h]
      · have hb : 0 < m.base.margin * (w 1 - m.κa * w 0 / m.base.η) ^ 2 := by
          rw [h0, mul_zero, zero_div, sub_zero]
          exact mul_pos hδ (sq_pos_of_ne_zero h1)
        have : 0 ≤ m.base.Rs * ((w 2 - m.base.p * w 0 +
            m.base.Ls * (m.base.η * w 1 - m.κa * w 0) / (2 * m.base.Rs) * m.base.p) ^ 2 +
          (w 3 - m.base.q * w 0 +
            m.base.Ls * (m.base.η * w 1 - m.κa * w 0) / (2 * m.base.Rs) * m.base.q) ^ 2) := by
          positivity
        have : 0 ≤ m.κa ^ 2 * (m.base.Gdc + m.base.Kp) * w 0 ^ 2 / m.base.η ^ 2 := by
          positivity
        linarith
    · have ha : 0 < m.κa ^ 2 * (m.base.Gdc + m.base.Kp) * w 0 ^ 2 / m.base.η ^ 2 := by
        have := sq_pos_of_ne_zero h0
        have := sq_pos_of_ne_zero hκ.ne'
        positivity
      have : 0 ≤ m.base.Rs * ((w 2 - m.base.p * w 0 +
          m.base.Ls * (m.base.η * w 1 - m.κa * w 0) / (2 * m.base.Rs) * m.base.p) ^ 2 +
        (w 3 - m.base.q * w 0 +
          m.base.Ls * (m.base.η * w 1 - m.κa * w 0) / (2 * m.base.Rs) * m.base.q) ^ 2) := by
        positivity
      have : 0 ≤ m.base.margin * (w 1 - m.κa * w 0 / m.base.η) ^ 2 := by positivity
      linarith

/-- `det J = κa (G_dc + K_p + μ² R_s/N) N/(C_dc L_s²)`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem det_jac (m : Model) (hN : m.base.N ≠ 0) (hL : m.base.Ls ≠ 0)
    (hC : m.base.Cdc ≠ 0) :
    m.jac.det = m.κa * ((m.base.Gdc + m.base.Kp) * m.base.N + m.base.Rs * m.base.μ ^ 2) /
      (m.base.Cdc * m.base.Ls ^ 2) := by
  rw [Criteria.det_fin_four]
  simp [Model.jac]
  field_simp
  simp only [MatchingStiffGrid.Model.N, MatchingStiffGrid.Model.ω0]
  ring

/-- **The angle feedback sign is necessary**: under the same damping hypotheses the
linearization is Hurwitz iff `κa > 0`. Static evidence on the model, not a connection
conclusion. -/
@[tmio TM, powerlib_domain] theorem jac_isHurwitz_iff (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hη : m.base.η ≠ 0) (hδ : 0 < m.base.margin) :
    LinearSystems.IsHurwitz m.jac ↔ 0 < m.κa := by
  refine ⟨fun h => ?_, jac_isHurwitz m hC hL hR hη hδ⟩
  have hN : 0 < m.base.N := MatchingStiffGrid.N_pos m.base hR.ne'
  have hX : 0 ≤ m.base.μ ^ 2 * m.base.ω0 ^ 2 * m.base.Ls ^ 2 / (4 * m.base.Rs * m.base.N) := by
    positivity
  have hg : 0 < m.base.Gdc + m.base.Kp := by
    have : m.base.margin = m.base.Gdc + m.base.Kp -
        m.base.μ ^ 2 * m.base.ω0 ^ 2 * m.base.Ls ^ 2 / (4 * m.base.Rs * m.base.N) := rfl
    linarith
  have hc := Criteria.charpoly_coeff_pos_of_isHurwitz h (Nat.zero_le 4)
  have hdet : m.jac.det = m.jac.charpoly.coeff 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff]
    simp only [Fintype.card_fin]
    norm_num
  have hpos : 0 < m.jac.det := hdet ▸ hc
  rw [det_jac m hN.ne' hL.ne' hC.ne'] at hpos
  have hden : 0 < (m.base.Gdc + m.base.Kp) * m.base.N + m.base.Rs * m.base.μ ^ 2 := by
    positivity
  have hnum := (div_pos_iff_of_pos_right (by positivity : 0 < m.base.Cdc * m.base.Ls ^ 2)).mp
    hpos
  by_contra hk
  push Not at hk
  nlinarith


/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_contDiff (m : Model) : ContDiff ℝ 1 m.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;>
    simp [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
      MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ] <;> fun_prop

/-- Entries of the Jacobian applied to a vector. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem jac_apply (m : Model) (v : State 4) :
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 0 = -m.κa * v 0 + m.base.η * v 1 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 1 =
      m.base.μ ^ 2 * m.base.ustar * m.base.ω0 * m.base.Ls / (m.base.N * m.base.Cdc) * v 0 -
        (m.base.Gdc + m.base.Kp) / m.base.Cdc * v 1 + m.base.μ / m.base.Cdc * v 3 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 2 =
      m.base.μ * m.base.ustar / m.base.Ls * v 0 - m.base.Rs / m.base.Ls * v 2 +
        m.base.ω0 * v 3 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 3 =
      -m.base.μ / m.base.Ls * v 1 - m.base.ω0 * v 2 - m.base.Rs / m.base.Ls * v 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four] <;>
    simp only [Model.jac, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The derivative of the loop at the operating point is `jac`. Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field_point (m : Model) (hL : m.base.Ls ≠ 0) :
    HasFDerivAt m.field (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac) m.base.point := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have hp : ∀ k : Fin 4, HasFDerivAt (fun x : State 4 => x k)
      (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : State 4 →L[ℝ] ℝ) m.base.point :=
    fun k => (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : State 4 →L[ℝ] ℝ).hasFDerivAt
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have hs := h0.sin
  have hc := h0.cos
  have hD := (MatchingStiffGrid.hasDerivAt_iHatD m.base (m.base.point 0)).comp_hasFDerivAt
    m.base.point h0
  have hQ := (MatchingStiffGrid.hasDerivAt_iHatQ m.base (m.base.point 0)).comp_hasFDerivAt
    m.base.point h0
  have p0 : m.base.point 0 = 0 := by simp [MatchingStiffGrid.Model.point]
  have p1 : m.base.point 1 = m.base.ustar := by simp [MatchingStiffGrid.Model.point]
  have p2 : m.base.point 2 = m.base.iHatD 0 := by simp [MatchingStiffGrid.Model.point]
  have p3 : m.base.point 3 = m.base.iHatQ 0 := by simp [MatchingStiffGrid.Model.point]
  have j := jac_apply m
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · have h := ((h1.const_mul m.base.η).sub_const m.base.ω0).sub (hs.const_mul m.κa)
    convert h using 1
    · funext y; simp [Model.field]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).1]
      simp [p0]
      ring
  · have hix := ((hs.neg.mul hD).add (hc.mul hQ)).const_mul m.base.μ |>.neg
    have hidc :=
      (((h1.sub_const m.base.ustar).const_mul (-m.base.Kp)).add_const
        (m.base.Gdc * m.base.ustar)).add hix
    have h := (((h1.const_mul (-m.base.Gdc)).add hidc).add
      (((hs.neg.mul h2).add (hc.mul h3)).const_mul m.base.μ)).mul_const m.base.Cdc⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
        PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
        Pi.neg_apply, Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.1]
      simp [p0, p2, p3, MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ]
      field_simp
      ring
  · have h := ((((h2.const_mul m.base.Rs).sub ((h3.const_mul m.base.ω0).const_mul
      m.base.Ls)).neg).sub ((hs.neg.const_mul m.base.μ).mul h1)).mul_const m.base.Ls⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, div_eq_mul_inv]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.1]
      simp [p0, p1]
      field_simp
      ring
  · have h :=
      (((((h2.const_mul m.base.ω0).const_mul m.base.Ls).add
        (h3.const_mul m.base.Rs)).neg.add_const m.base.v0).sub
        ((hc.const_mul m.base.μ).mul h1)).mul_const m.base.Ls⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, PiLp.toLp_apply, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply,
        div_eq_mul_inv]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.2]
      simp [p0, p1]
      field_simp
      ring


/-! ## Family -/

/-- Static requirements on direct-angle-control models. -/
inductive Requirement
  | physical
  | angleFeedback
  | antiFeedback
  | damped
  | matching

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .physical => 0 < m.base.Cdc ∧ 0 < m.base.Ls ∧ 0 < m.base.Rs
  | .angleFeedback => 0 < m.κa
  | .antiFeedback => m.κa < 0
  | .damped => 0 < m.base.margin
  | .matching => m.base.η ≠ 0

/-- The translation (`Spectral.localTable`): Lyapunov, local asymptotic and local exponential
stability into `{physical, angleFeedback, damped, matching}`, instability into
`{physical, antiFeedback, damped}`, passivity into nothing, every other sentence into the whole,
inconsistent, language. -/
abbrev translate : Sentence → Set Requirement :=
  Spectral.localTable {.physical, .angleFeedback, .damped, .matching}
    {.physical, .angleFeedback, .damped, .matching} {.physical, .antiFeedback, .damped} ∅

/-- The loop translated to the operating point. -/
def Model.translated (m : Model) (z : State 4) : State 4 := m.field (z + m.base.point)

/-- The direct-angle-control family. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.translated, Meets, translate⟩

/-- The direct-angle-control family is the family of the translated autonomous fields. -/
@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.translated :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem mem_den_flow {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.field m.base.point :=
  Spectral.mem_den_flow_iff_shift (f := Model.field) (pt := fun m => m.base.point)
    family_isAutonomous

/-- **Local exponential stability, decided** under the stiff-grid damping condition: with
`C_dc, L_s, R_s > 0`, `η ≠ 0` and `margin > 0`, the operating point of direct angle control is
locally exponentially stable iff the angle feedback has the synchronizing sign, `κ k > 0`
(`k = L_s μ u* v₀/N`); no condition on `μ u* v₀` itself. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hC : 0 < m.base.Cdc) (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hη : m.base.η ≠ 0)
    (hδ : 0 < m.base.margin) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔ 0 < m.κa) := by
  unfold TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  change LocallyExponentiallyStable m.field m.base.point ↔ _
  have hN : 0 < m.base.N := MatchingStiffGrid.N_pos m.base hR.ne'
  rw [← jac_isHurwitz_iff m hC hL hR hη hδ]
  exact ⟨fun h => Dynamics.isHurwitz_of_locallyExponentiallyStable m.jac (field_contDiff m)
      (hasFDerivAt_field_point m hL.ne').fderiv h,
    fun h => hurwitz_linearization_locally_exponentially_stable m.jac (field_contDiff m)
      (field_point m hN.ne') (hasFDerivAt_field_point m hL.ne').fderiv h⟩

/-- The whole requirement language is inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .angleFeedback .antiFeedback fun m h1 h2 => ?_
  have h1 : 0 < m.κa := h1
  have h2 : m.κa < 0 := h2
  linarith

/-- Every translation of the direct-angle-control family is sound: stability from the Hurwitz
linearization (`jac_isHurwitz`), instability from `det J < 0` (`det_jac`,
`Criteria.exists_root_re_pos_of_det`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_jacobian (f := Model.field) (pt := fun m => m.base.point)
    (fun _ _ => (connection_proof% mem_den_flow)) family_isAutonomous.den_passive (fun _ => rfl)
    Model.jac (fun m hm => ?_) (fun m hm => ?_) (fun m hm => ?_)
  · have hphys : Meets m .physical := by
      rcases hm with hm | hm <;> rw [(connection_proof% TMIO.mem_realize)] at hm <;>
        exact hm .physical (by simp)
    obtain ⟨hC, hL, hR⟩ := hphys
    have hN : 0 < m.base.N := MatchingStiffGrid.N_pos m.base hR.ne'
    exact ⟨field_contDiff m, field_point m hN.ne', (hasFDerivAt_field_point m hL.ne').fderiv⟩
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    obtain ⟨hC, hL, hR⟩ : Meets m .physical := hm .physical (by simp)
    exact jac_isHurwitz m hC hL hR (hm .matching (by simp)) (hm .damped (by simp))
      (hm .angleFeedback (by simp))
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    obtain ⟨hC, hL, hR⟩ : Meets m .physical := hm .physical (by simp)
    have hκ : m.κa < 0 := hm .antiFeedback (by simp)
    have hδ : 0 < m.base.margin := hm .damped (by simp)
    have hN : 0 < m.base.N := MatchingStiffGrid.N_pos m.base hR.ne'
    have hX : 0 ≤ m.base.μ ^ 2 * m.base.ω0 ^ 2 * m.base.Ls ^ 2 /
        (4 * m.base.Rs * m.base.N) := by positivity
    have hg : 0 < m.base.Gdc + m.base.Kp := by
      have : m.base.margin = m.base.Gdc + m.base.Kp -
          m.base.μ ^ 2 * m.base.ω0 ^ 2 * m.base.Ls ^ 2 / (4 * m.base.Rs * m.base.N) := rfl
      linarith
    apply Criteria.exists_root_re_pos_of_det
    rw [det_jac m hN.ne' hL.ne' hC.ne']
    have hden : 0 < (m.base.Gdc + m.base.Kp) * m.base.N + m.base.Rs * m.base.μ ^ 2 := by
      positivity
    have : m.κa * ((m.base.Gdc + m.base.Kp) * m.base.N + m.base.Rs * m.base.μ ^ 2) /
        (m.base.Cdc * m.base.Ls ^ 2) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hκ hden) (by positivity)
    norm_num
    exact this

/-- **Boundary**: no direct-angle-control loop is globally asymptotically stable on `ℝ⁴`
(`2π`-periodicity gives a second equilibrium whenever the operating point is one). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyAsymptoticallyStable (m : Model) :
    connection% (m ∉ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  intro h
  change Flow.GloballyAsymptoticallyStable _ _ at h
  refine Dynamics.not_globallyAsymptoticallyStable_of_equilibrium_ne
    (y := WithLp.toLp 2 ![0 + 2 * Real.pi, m.base.ustar, m.base.iHatD 0, m.base.iHatQ 0]) ?_ ?_ h
  · rw [field_add_two_pi]
    exact h.1
  · intro he
    have h0 := congrArg (fun z : State 4 => z 0) he
    simp [MatchingStiffGrid.Model.point, Real.pi_ne_zero] at h0

/-- The same boundary for global exponential stability. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyExponentiallyStable (m : Model) :
    connection% (m ∉ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact fun h => not_mem_den_globallyAsymptoticallyStable m
    (Spectral.den_globallyExponentiallyStable_subset_gas h)

/-- The global asymptotic translation is exact: both its denotation and its space are empty. -/
@[tmio TM, powerlib_domain] theorem exact_globallyAsymptoticallyStable :
    connection% (family.Exact (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_univ (F := family) realize_univ rfl
    (Set.eq_empty_iff_forall_notMem.mpr not_mem_den_globallyAsymptoticallyStable)

/-- The global exponential translation is exact: both its denotation and its space are empty. -/
@[tmio TM, powerlib_domain] theorem exact_globallyExponentiallyStable :
    connection% (family.Exact (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_univ (F := family) realize_univ rfl
    (Set.eq_empty_iff_forall_notMem.mpr not_mem_den_globallyExponentiallyStable)

end powerlib.GFM.Matching.DirectAngle
