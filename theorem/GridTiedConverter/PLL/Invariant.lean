import theorem.GridTiedConverter.PLL.Model
import theorem.GridTiedConverter.PLL.PIPLLLienard

/-! # Invariant coordinates: pendulum form of the SRF-PLL, amplitude–phase and normal modes

Coordinate and trajectory identities; the stability claims are those of the PI-PLL family,
read at the member below.

Model boundary.
* System: the SRF-PLL error model of `theorem/GridTiedConverter/PLL/Model.lean` in the `(θ, ξ)`
  coordinates (`xiField a b Δω`, `a = V K_p`, `b = V K_i`, constant frequency offset `Δω`): ideal
  balanced grid, PI loop filter, VCO; no pre-filter, delay, PWM, current loop or saturation;
  continuous time.
* The amplitude–phase and normal-mode items are pointers to the modules that hold them.

Source: work-sync `theory/T-invariant-coordinates.md` §1.2, §1.3, §1.4;
`theory/T-gfl-multiscale-modeling.md` §1.8; the Liénard (velocity) coordinates of the PI-PLL
(`theorem/GridTiedConverter/PLL/PIPLLLienard.lean`).

Results.
* Pendulum form (T-invariant-coordinates §1.2, T-gfl-multiscale §1.8). For the `(θ, ξ)` field
  `xiField a b Δω` (`θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`, constant `Δω`, `a = V K_p`,
  `b = V K_i`): every solution has `θ ∈ C²` with
  `θ̈ + a cos θ · θ̇ + b sin θ = 0`; conversely (`b ≠ 0`) every `C²` solution of the pendulum
  equation gives a solution of the first-order system with `ξ = (θ̇ − Δω + a sin θ)/b`
  (`xiField_pendulum`, `pendulum_xiField`: the Liénard form `θ̇ = w`, `ẇ = K_i h + K_p h' w` of the
  unit-amplitude SRF member, `h = srfPD 1`, read through its velocity coordinates `w = θ̇`).
  (The note's right-hand side `dΔω/dt` vanishes for the constant offset modelled here.)
* Amplitude–phase coordinates of a dq current (T-invariant-coordinates §1.3): the identities
  for the dq R–L filter (`Passive.SeriesRLC.dq_power_balance` for the amplitude,
  `hasDerivAt_arg_current`, `hasDerivAt_phase`) are in `theorem/Passive/Dq.lean` and
  `theorem/Passive/DqRL.lean`; the complex power
  `S̄ = V̄ Ī*` in dq components is `Transform.complexPower_expand`
  (`theorem/Transform/ComplexPower.lean`).
* Complex normal modes of an LC pair (T-invariant-coordinates §1.4), with the correction of
  the note's scale factor: `Passive.normalMode_sum`, `Passive.normalMode_diff`,
  `Passive.normalMode_diff_ne_note` in `theorem/Passive/PH/RLC.lean`.

Family and connection conclusions.
No new family: the `(θ_err, ξ)` model with gains `(a, b)`
and offset `Δω`, read about `θ*`, is the member `PLL.PIPLL.srf 1 a b (−Δω) θ*` of the PI-PLL
family (`xi_piPLLField`; its selected point is `(θ*, −Δω / b)`). Its local stability is that
family's at `V = 1`, `K_p = a`, `K_i = b`, `δω = −Δω`: for `a, b > 0` the equilibria
`(2kπ, −Δω/b)` are locally exponentially stable
(`PIPLL.srf_mem_den_locallyExponentiallyStable_inPhase`) and for `b > 0` the equilibria
`((2k+1)π, −Δω/b)` are saddles (`PIPLL.srf_mem_den_unstable_antiPhase`), in
`theorem/GridTiedConverter/PLL/PIPLLFamily.lean`. The pendulum form is domain evidence for the
stated PLL fields and their signals.
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.PLL.PIPLL (srf)

/-! ## Pendulum form -/

/-- First-order `(θ, ξ)` system ⇒ second-order pendulum: along any solution of `xiField`,
`θ̇ = Δω − a sin θ + b ξ` and `θ̈ = −a cos θ · θ̇ − b sin θ`. The velocity coordinates of the
unit-amplitude SRF member (`isIntegralCurveOn_piPLLVelocityCoord` at `h = srfPD 1`) map the
solution to one of the Liénard field. -/
@[tmio M, powerlib_domain] theorem xiField_pendulum {a b Δω : ℝ} {φ : ℝ → State 2}
    (hφ : ∀ t, HasDerivAt φ (xiField a b Δω (φ t)) t) (t : ℝ) :
    HasDerivAt (fun τ => φ τ 0) (Δω - a * Real.sin (φ t 0) + b * φ t 1) t ∧
      HasDerivAt (fun τ => Δω - a * Real.sin (φ τ 0) + b * φ τ 1)
        (-(a * Real.cos (φ t 0) * (Δω - a * Real.sin (φ t 0) + b * φ t 1)) -
          b * Real.sin (φ t 0)) t := by
  rw [xiField_eq_srfField] at hφ
  obtain ⟨h0, h1⟩ := PhasePlane.hasDerivWithinAt_iff_components.mp
    (isIntegralCurveOn_piPLLVelocityCoord (Kp := a) (Ki := b) (δω := -Δω) (hasDerivAt_srfPD 1)
      (s := Set.univ) (fun τ _ => (hφ τ).hasDerivWithinAt) t (Set.mem_univ t))
  simp only [hasDerivWithinAt_univ, piPLLVelocityCoord, piPLLLienardField, srfPD,
    PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one] at h0 h1
  refine ⟨h0.congr_deriv (by ring), ?_⟩
  convert h1 using 1
  · funext τ; ring
  · ring

/-- Second-order pendulum ⇒ first-order system (`b ≠ 0`): a solution `θ` of
`θ̈ + a cos θ · θ̇ + b sin θ = 0` with `ξ := (θ̇ − Δω + a sin θ)/b` solves `xiField a b Δω` (the
inverse velocity coordinates, `isIntegralCurveOn_piPLLVelocityCoordInv` at `h = srfPD 1`). -/
@[tmio M, powerlib_domain] theorem pendulum_xiField {a b Δω : ℝ} (hb : b ≠ 0) {θ θ' : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (θ' t) t)
    (hθ' : ∀ t, HasDerivAt θ' (-(a * Real.cos (θ t) * θ' t) - b * Real.sin (θ t)) t) (t : ℝ) :
    HasDerivAt (fun τ => PhasePlane.mk (θ τ) ((θ' τ - Δω + a * Real.sin (θ τ)) / b))
      (xiField a b Δω (PhasePlane.mk (θ t) ((θ' t - Δω + a * Real.sin (θ t)) / b))) t := by
  have hψ : IsIntegralCurveOn (fun τ => PhasePlane.mk (θ τ) (θ' τ))
      (fun _ y => piPLLLienardField (srfPD 1) (fun x => -(1 * Real.cos x)) a b y) Set.univ :=
    fun τ _ => PhasePlane.hasDerivWithinAt_iff_components.mpr ⟨(hθ τ).hasDerivWithinAt,
      (hθ' τ).hasDerivWithinAt.congr_deriv (by
        simp only [piPLLLienardField, srfPD, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one]
        ring)⟩
  have e (τ : ℝ) : piPLLVelocityCoordInv (srfPD 1) a b (-Δω) (PhasePlane.mk (θ τ) (θ' τ)) =
      PhasePlane.mk (θ τ) ((θ' τ - Δω + a * Real.sin (θ τ)) / b) := by
    simp only [piPLLVelocityCoordInv, srfPD, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one]
    congr 1; field_simp; ring
  have h := isIntegralCurveOn_piPLLVelocityCoordInv (δω := -Δω) hb (hasDerivAt_srfPD 1) hψ t
    (Set.mem_univ t)
  rw [hasDerivWithinAt_univ, ← srfField, ← xiField_eq_srfField] at h
  simpa only [e] using h

/-! ## The `(θ_err, ξ)` field as a PI-PLL family member -/

/-- The `(θ_err, ξ)` field is the untranslated field of the unit-amplitude SRF family member with
gains `(a, b)` and offset `−Δω`. -/
@[tmio M, powerlib_domain] theorem xi_piPLLField (a b Δω θ : ℝ) :
    piPLLField (srf 1 a b (-Δω) θ).h a b (-Δω) = xiField a b Δω := by
  rw [srf_piPLLField, xiField_eq_srfField]

end powerlib.PLL
