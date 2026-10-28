import theorem.CurrentControl.PILoop

/-! # Cross-decoupling algebra and the stability premise of zero steady-state error

Algebra of the dq cross-decoupling term (foundation), and the closed-loop stability premise that
the "integral action removes the steady-state error" argument needs (one connection statement).

Model boundary.
* Decoupling algebra: IN-positive dq plant `L i_d' = v_d − u_d − R i_d + ω L i_q` with the
  decoupling command `u_d^dec = +ω̂ L̂ i_q`, `u_q^dec = −ω̂ L̂ i_d`; parameters and currents are
  arbitrary reals.
* Stability premise: the single-axis PI loop of `PILoop.lean` (state `(i, ξ)`, input the
  reference `i*`, `L > 0`), read through its family `PIParams.family` (the closed-loop plant as
  a port system).

Source: work-sync `theory/T-decoupling-control.md` §1.3–§1.5, §2.2;
`theory/T-gfl-control.md` §1.4.3; `theory/T-dae-elimination.md` §2.2 (uses the cancellation).

Results.
* `residual_general`, `residual_caseA`, `residual_caseB` (+ q-axis forms): the coupling left in
  the `L`-equation is `(ω L − ω̂ L̂) i_q` on d and `−(ω L − ω̂ L̂) i_d` on q; it is `ω ΔL i` when
  `ω̂ = ω` (case A, `ΔL = L − L̂`) and `(ω − ω̂) L i` when `L̂ = L` (case B). `residual_rate` is
  the `di/dt` form (divided by `L`).
* `decoupling_power_cancel`: the decoupling terms contribute nothing to the bridge power
  `u_d i_d + u_q i_q`, for either sign convention (`decoupling_power_cancel_out`).

Family and connection conclusions.
* `PIParams.mem_den_unstable_of_Ki_neg` (connection): if `Ki < 0` the loop is unstable — a
  negative monic coefficient `Ki/L` places a real characteristic root in the open right half
  plane. Under the exact premise `R + Kp > 0 ∧ Ki > 0` the loop is stable
  (`PIParams.mem_den_iff`); every *equilibrium* has `i = i*` unconditionally
  (`PIParams.equilibrium_current`, static).
* The trajectory form — with `Ki < 0` some solution with a constant reference has `i(t) ↛ i*`,
  diverging exponentially along a real unstable mode (`PIParams.not_tracks_of_Ki_neg`) — is
  outside the sentence language and is kept as private implementation evidence.

Correction (T-decoupling-control §2.2, T-gfl-control §2.2 "积分项消静差"): "the PI loop drives
the steady state to `i = i*`" requires closed-loop stability; the notes omit this premise
(`PIParams.mem_den_unstable_of_Ki_neg` is the counterexample for `Ki < 0`).
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter LinearSystems
open scoped Topology

/-! ## Decoupling residuals (IN-positive) -/

/-- d-axis coupling left in the `L`-equation: geometric `+ω L i_q` minus `u_d^dec = ω̂ L̂ i_q`. -/
@[tmio T, powerlib_foundation] theorem residual_general (ω ωhat L Lhat iq : ℝ) :
    ω * L * iq - ωhat * Lhat * iq = (ω * L - ωhat * Lhat) * iq := by ring

/-- q-axis coupling: geometric `−ω L i_d` minus `u_q^dec = −ω̂ L̂ i_d`. -/
@[powerlib_foundation] theorem residual_general_q (ω ωhat L Lhat id : ℝ) :
    -(ω * L * id) - -(ωhat * Lhat * id) = -((ω * L - ωhat * Lhat) * id) := by ring

/-- Case A (`ω̂ = ω`): residual `ω ΔL i_q`, `ΔL = L − L̂`. -/
@[powerlib_foundation] theorem residual_caseA (ω L Lhat iq : ℝ) :
    ω * L * iq - ω * Lhat * iq = ω * (L - Lhat) * iq := by ring

/-- Case B (`L̂ = L`): residual `(ω − ω̂) L i_q`. -/
@[powerlib_foundation] theorem residual_caseB (ω ωhat L iq : ℝ) :
    ω * L * iq - ωhat * L * iq = (ω - ωhat) * L * iq := by ring

/-- Case A in rate form: the `di_d/dt` contribution is `ω ΔL i_q / L`. -/
@[powerlib_foundation] theorem residual_rate (ω L Lhat iq : ℝ) :
    (ω * L * iq - ω * Lhat * iq) / L = ω * (L - Lhat) * iq / L := by ring

/-- The decoupling terms do no work: `u_d^dec i_d + u_q^dec i_q = 0`. -/
@[powerlib_foundation] theorem decoupling_power_cancel (ωhat Lhat id iq : ℝ) :
    (ωhat * Lhat * iq) * id + (-(ωhat * Lhat * id)) * iq = 0 := by ring

/-- Same cancellation in the OUT-positive sign convention. -/
@[powerlib_foundation] theorem decoupling_power_cancel_out (ωhat Lhat id iq : ℝ) :
    (-(ωhat * Lhat * iq)) * id + (ωhat * Lhat * id) * iq = 0 := by ring

/-- Bridge power splits into the non-decoupling part only. -/
@[powerlib_foundation] theorem bridgePower_decoupling (ud uq ωhat Lhat id iq : ℝ) :
    (ud + ωhat * Lhat * iq) * id + (uq - ωhat * Lhat * id) * iq = ud * id + uq * iq := by ring

/-! ## Zero steady-state error needs closed-loop stability -/

namespace PIParams

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable (p : PIParams)

/-- With `L > 0` and `Ki < 0` the PI current loop is unstable: `Ki/L < 0` makes the
determinant of its state matrix negative (a real saddle mode). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_Ki_neg (hL : 0 < p.L) (hKi : p.Ki < 0) :
    connection% (p ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨s, hs, hre⟩ := p.exists_root_of_unstable (Or.inr (div_neg_of_neg_of_pos hKi hL))
  exact family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 hs hre)

/-- In the state matrix of the PI loop, a real eigenvector of a positive eigenvalue has a
nonzero current component. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem first_ne_zero {r : ℝ} (hr : 0 < r) {v : Fin 2 → ℝ}
    (hv : v ≠ 0) (h : p.model.A *ᵥ v = r • v) : v 0 ≠ 0 := by
  intro h0
  have h1 := congrFun h 1
  simp [model, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0] at h1
  apply hv
  ext k
  fin_cases k
  · simpa using h0
  · rcases h1 with h1 | h1
    · exact absurd h1 hr.ne'
    · simpa using h1

/-- With `Ki < 0` the PI current loop does not track: some solution with a constant reference
has `i(t) ↛ i*`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem not_tracks_of_Ki_neg (hL : 0 < p.L) (hKi : p.Ki < 0) (iref : ℝ) :
    ∃ x : ℝ → ℝ², (∀ t, HasDerivAt x (p.field iref (x t)) t) ∧
      ¬ Tendsto (fun t => x t 0) atTop (𝓝 iref) := by
  have hdet : p.model.A.det < 0 := by
    change (!![-(p.R + p.Kp) / p.L, p.Ki / p.L; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).det < 0
    rw [Matrix.det_fin_two_of]
    have : p.Ki / p.L < 0 := div_neg_of_neg_of_pos hKi hL
    linarith
  obtain ⟨r, hr, v, hv, hAv⟩ := Criteria.exists_pos_real_eigenvector_of_det_neg _ hdet
  obtain ⟨x, hx, hn⟩ := LTI.exists_not_tendsto_of_eigenvector p.model (p.isEquilibrium hKi.ne iref)
    hr hAv (p.first_ne_zero hr hv hAv) iref
  exact ⟨x, fun t => by rw [← model_field]; exact hx t, hn⟩

end PIParams

end powerlib.CurrentControl
