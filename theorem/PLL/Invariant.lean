import theorem.PLL.Model

/-! # Invariant coordinates: pendulum form of the SRF-PLL, amplitude–phase and normal modes

Coordinate and trajectory identities; the only stability claims are the two connection
statements on the PI-PLL family at the end.

Model boundary.
* System: the SRF-PLL error model of `theorem/PLL/Model.lean` in the `(θ, ξ)` coordinates
  (`xiField a b Δω`, `a = V K_p`, `b = V K_i`, constant frequency offset `Δω`): ideal balanced
  grid, PI loop filter, VCO; no pre-filter, delay, PWM, current loop or saturation; continuous
  time.
* The amplitude–phase and normal-mode items are pointers to the modules that hold them.

Source: work-sync `theory/T-invariant-coordinates.md` §1.2, §1.3, §1.4;
`theory/T-gfl-multiscale-modeling.md` §1.8.

Results.
* Pendulum form (T-invariant-coordinates §1.2, T-gfl-multiscale §1.8). For the `(θ, ξ)` field
  `xiField a b Δω` (`θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`, constant `Δω`, `a = V K_p`,
  `b = V K_i`): every solution has `θ ∈ C²` with
  `θ̈ + a cos θ · θ̇ + b sin θ = 0`; conversely (`b ≠ 0`) every `C²` solution of the pendulum
  equation gives a solution of the first-order system with `ξ = (θ̇ − Δω + a sin θ)/b`.
  (The note's right-hand side `dΔω/dt` vanishes for the constant offset modelled here.)
* Amplitude–phase coordinates of a dq current (T-invariant-coordinates §1.3): the identities
  for the dq R–L filter (`hasDerivAt_half_sq_amplitude`, `hasDerivAt_arg_current`,
  `hasDerivAt_phase`) are in `theorem/CurrentControl/DqRL.lean`; the complex power
  `S̄ = V̄ Ī*` in dq components is `Transform.complexPower_expand`
  (`theorem/Transform/ComplexPower.lean`).
* Complex normal modes of an LC pair (T-invariant-coordinates §1.4), with the correction of
  the note's scale factor: `PH.Models.normalMode_sum`, `PH.Models.normalMode_diff`,
  `PH.Models.normalMode_diff_ne_note` in `theorem/PH/Models/RLC.lean`.

Family and connection conclusions.
No new family: the `(θ_err, ξ)` model with gains `(a, b)`
and offset `Δω`, read about `θ*`, is the member `PLL.PIPLL.srf 1 a b (−Δω) θ*` of the PI-PLL
family (`xi_piPLLField`; its selected point is `(θ*, −Δω / b)`). The two local-stability results
are connection statements on that family (`xi_mem_den_locallyExponentiallyStable`,
`xi_mem_den_unstable_antiPhase`). Everything else is foundation: the pendulum form holds for
the stated (generic) signals and fields.
-/

noncomputable section
namespace powerlib.PLL
open Matrix
open powerlib.Dynamics (State)
open powerlib.PLL.PIPLL (srf)

@[powerlib_foundation] private lemma hasDerivAt_state {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun τ => PhasePlane.mk (f τ) (g τ)) (PhasePlane.mk f' g') t := by
  have h : HasDerivAt (fun τ => ![f τ, g τ]) ![f', g'] t := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hg
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h

/-! ## Pendulum form -/

/-- First-order `(θ, ξ)` system ⇒ second-order pendulum: along any solution of `xiField`,
`θ̇ = Δω − a sin θ + b ξ` and `θ̈ = −a cos θ · θ̇ − b sin θ`. -/
@[tmio M, powerlib_foundation] theorem xiField_pendulum {a b Δω : ℝ} {φ : ℝ → State 2}
    (hφ : ∀ t, HasDerivAt φ (xiField a b Δω (φ t)) t) (t : ℝ) :
    HasDerivAt (fun τ => φ τ 0) (Δω - a * Real.sin (φ t 0) + b * φ t 1) t ∧
      HasDerivAt (fun τ => Δω - a * Real.sin (φ τ 0) + b * φ τ 1)
        (-(a * Real.cos (φ t 0) * (Δω - a * Real.sin (φ t 0) + b * φ t 1)) -
          b * Real.sin (φ t 0)) t := by
  have h0 := Dynamics.hasDerivAt_iff_coords.mp (hφ t) 0
  have h1 := Dynamics.hasDerivAt_iff_coords.mp (hφ t) 1
  simp only [xiField] at h0 h1
  refine ⟨by simpa using h0, ?_⟩
  have hs := (h0.sin.const_mul a)
  have h := ((hasDerivAt_const t Δω).sub hs).add (h1.const_mul b)
  convert h using 1
  simp; ring

/-- Second-order pendulum ⇒ first-order system (`b ≠ 0`): a solution `θ` of
`θ̈ + a cos θ · θ̇ + b sin θ = 0` with `ξ := (θ̇ − Δω + a sin θ)/b` solves `xiField a b Δω`. -/
@[powerlib_foundation] theorem pendulum_xiField {a b Δω : ℝ} (hb : b ≠ 0) {θ θ' : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (θ' t) t)
    (hθ' : ∀ t, HasDerivAt θ' (-(a * Real.cos (θ t) * θ' t) - b * Real.sin (θ t)) t) (t : ℝ) :
    HasDerivAt (fun τ => PhasePlane.mk (θ τ) ((θ' τ - Δω + a * Real.sin (θ τ)) / b))
      (xiField a b Δω (PhasePlane.mk (θ t) ((θ' t - Δω + a * Real.sin (θ t)) / b))) t := by
  have hξ := ((((hθ' t).sub_const Δω).add ((hθ t).sin.const_mul a))).div_const b
  convert hasDerivAt_state (hθ t) hξ using 1
  rw [PhasePlane.ext_iff']
  simp [xiField]
  constructor
  · field_simp; ring
  · field_simp; ring

/-! ## Local stability in `(θ_err, ξ)` coordinates -/

/-- The `(θ_err, ξ)` field is the untranslated field of the unit-amplitude SRF family member with
gains `(a, b)` and offset `−Δω`. -/
@[powerlib_foundation] theorem xi_piPLLField (a b Δω θ : ℝ) :
    piPLLField (srf 1 a b (-Δω) θ).h a b (-Δω) = xiField a b Δω := by
  rw [srf_piPLLField, xiField_eq_srfField]

/-- `(θ_err, ξ)` model (T-invariant-coordinates §1.2, T-gfl-multiscale §1.3): for
`a = V K_p > 0`, `b = V K_i > 0` the equilibria `(2kπ, −Δω/b)` are locally exponentially
stable. -/
@[tmio TM, powerlib_domain] theorem xi_mem_den_locallyExponentiallyStable {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (Δω : ℝ) (k : ℤ) :
    connection% (srf 1 a b (-Δω) (2 * k * Real.pi) ∈
      PIPLL.family.den (.flow .locallyExponentiallyStable)) :=
  srf_mem_den_locallyExponentiallyStable_inPhase (by simpa using ha) (by simpa using hb) (-Δω) k

/-- `(θ_err, ξ)` model: for `b > 0` the equilibria `((2k+1)π, −Δω/b)` are saddles, unstable. -/
@[tmio TM, powerlib_domain] theorem xi_mem_den_unstable_antiPhase {a b : ℝ} (hb : 0 < b) (Δω : ℝ)
    (k : ℤ) :
    connection% (srf 1 a b (-Δω) ((2 * k + 1) * Real.pi) ∈
      PIPLL.family.den (.flow .unstable)) :=
  srf_mem_den_unstable_antiPhase (Kp := a) (by simpa using hb) (-Δω) k

end powerlib.PLL
