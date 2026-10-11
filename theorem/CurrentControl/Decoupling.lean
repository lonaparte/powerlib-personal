import theorem.CurrentControl.PILoop

/-! # Cross-decoupling algebra and the stability premise of zero steady-state error

Foundation part (algebra of the decoupling term, T-decoupling-control §1.3–§1.5).
* `residual_general`, `residual_caseA`, `residual_caseB` (+ q-axis forms): with the
  IN-positive plant `L i_d' = v_d − u_d − R i_d + ω L i_q` and the decoupling command
  `u_d^dec = +ω̂ L̂ i_q`, `u_q^dec = −ω̂ L̂ i_d`, the coupling left in the `L`-equation is
  `(ω L − ω̂ L̂) i_q` on d and `−(ω L − ω̂ L̂) i_d` on q; it is `ω ΔL i` when `ω̂ = ω` (case A,
  `ΔL = L − L̂`) and `(ω − ω̂) L i` when `L̂ = L` (case B). `residual_rate` is the
  `di/dt` form (divided by `L`).
* `decoupling_power_cancel`: the decoupling terms contribute nothing to the bridge power
  `u_d i_d + u_q i_q`, for either sign convention (`decoupling_power_cancel_out`).

Domain part (Correction).
* `PIParams.not_tracks_of_Ki_neg`: model = the single-axis PI loop of `PILoop.lean`
  (state `(i, ξ)`, constant reference `i*`, `L > 0`). If `Ki < 0`, some solution has a current
  that does not converge to `i*` (it diverges exponentially along a real unstable mode).
  Correction (T-decoupling-control §2.2, T-gfl-control §2.2 "积分项消静差"): "the PI loop drives
  the steady state to `i = i*`" requires closed-loop stability; the notes omit this premise.
  Under the exact premise `R + Kp > 0 ∧ Ki > 0` tracking holds (`PIParams.tracks_reference`,
  `MismatchParams.tracks_reference`); every *equilibrium* has `i = i*` unconditionally
  (`PIParams.equilibrium_current`).

Source: work-sync `theory/T-decoupling-control.md` §1.3–§1.5, §2.2;
`theory/T-gfl-control.md` §1.4.3; `theory/T-dae-elimination.md` §2.2 (uses the cancellation).
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter
open scoped Topology

/-! ## Decoupling residuals (IN-positive) -/

/-- d-axis coupling left in the `L`-equation: geometric `+ω L i_q` minus `u_d^dec = ω̂ L̂ i_q`. -/
@[powerlib_foundation] theorem residual_general (ω ωhat L Lhat iq : ℝ) :
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

variable (p : PIParams)

@[powerlib_foundation] private lemma first_ne_zero {r : ℝ} (hr : 0 < r) {v : Fin 2 → ℝ}
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
has `i(t) ↛ i*`. -/
@[powerlib_domain] theorem not_tracks_of_Ki_neg (hL : 0 < p.L) (hKi : p.Ki < 0) (iref : ℝ) :
    ∃ x : ℝ → Fin 2 → ℝ, (∀ t, HasDerivAt x (p.field iref (x t)) t) ∧
      ¬ Tendsto (fun t => x t 0) atTop (𝓝 iref) := by
  have hdet : p.model.A.det < 0 := by
    change (!![-(p.R + p.Kp) / p.L, p.Ki / p.L; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ).det < 0
    rw [Matrix.det_fin_two_of]
    have : p.Ki / p.L < 0 := div_neg_of_neg_of_pos hKi hL
    linarith
  obtain ⟨r, hr, v, hv, hAv⟩ := Criteria.exists_pos_real_eigenvector_of_det_neg _ hdet
  have he := p.isEquilibrium hKi.ne iref
  set e := p.equilibrium iref
  let x : ℝ → Fin 2 → ℝ := fun t => e + Real.exp (r * t) • v
  refine ⟨x, ?_, ?_⟩
  · intro t
    rw [← model_field]
    have hexp : HasDerivAt (fun s => Real.exp (r * s)) (Real.exp (r * t) * r) t := by
      simpa using ((hasDerivAt_id t).const_mul r).exp
    have h := (hexp.smul_const v).const_add e
    convert h using 1
    rw [LTI.Model.field_shift he, LTI.Model.operator_apply]
    simp only [x, add_sub_cancel_left, Matrix.mulVec_smul, hAv, smul_smul]
  · intro hlim
    have hv0 := p.first_ne_zero hr hv hAv
    have hpos : 0 < |v 0| := abs_pos.mpr hv0
    have hlim' : Tendsto (fun t => x t 0 - iref) atTop (𝓝 0) := by
      simpa using hlim.sub_const iref
    have hev := hlim'.eventually (Metric.ball_mem_nhds (0 : ℝ) hpos)
    obtain ⟨T, hT⟩ := (hev.and (eventually_ge_atTop (0 : ℝ))).exists
    have hx : x T 0 - iref = Real.exp (r * T) * v 0 := by
      simp only [x, e, equilibrium, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero]
      ring
    have hge : |v 0| ≤ |x T 0 - iref| := by
      rw [hx, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact le_mul_of_one_le_left (abs_nonneg _)
        (Real.one_le_exp_iff.mpr (mul_nonneg hr.le hT.2))
    have hlt : |x T 0 - iref| < |v 0| := by
      simpa [Real.dist_eq] using hT.1
    linarith

end PIParams

end powerlib.CurrentControl
