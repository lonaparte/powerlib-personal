import theorem.GridTiedConverter.GFM.HopfCoefficient
import theorem.GridTiedConverter.GFM.Bifurcation
import theorem.Dynamics.HopfCycleAmplitude

/-! # VSM with a power filter: Hopf cycles below the Hopf damping

Domain module.

Model boundary.
* The three-state model of `theorem/GridTiedConverter/GFM/VSMLPF.lean`, unchanged (state
  `(δ, ω, P_f)`, `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)`, lossless line,
  constant internal EMF; excluded as there), read about a balanced selected point on the Hopf
  boundary `K = D ω_c + D²/M` with `M, D, ω_c > 0`, and unfolded in the damping: the parameter
  `μ` replaces `D` by `D + μ` (`VSMLPF.dampShift`); the operating point `(δ*, 0, P₀)` does not
  depend on the damping, so the translated family `VSMLPF.Model.dampFamily` keeps the origin as
  an equilibrium.
* Level: the cycles of the generic Hopf theorem `Dynamics.HopfCycle.exists_hopfCycle` for this
  family, and the amplitude law of every small cycle `Dynamics.HopfCycle.periodic_amplitude`.
  Periodic orbits are not sentences of `VSMLPF.family`, so the conclusions on the model are
  private evidence; no new family, no connection conclusion. Uniqueness of the cycle and its
  orbital stability are not proved.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3,
the transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`); the critical pair and `ℓ₁` of
`theorem/GridTiedConverter/GFM/HopfCoefficient.lean`; the characteristic polynomial of
`theorem/GridTiedConverter/GFM/Bifurcation.lean`. The transversality coefficient was derived
with SymPy (untrusted) and is checked by the kernel (`field_simp`, `ring`).

Results.
* `VSMLPF.dampShift`, `VSMLPF.Model.dampFamily`, `VSMLPF.dampJac` (`∂J/∂D = −(1/M) e₁e₁ᵀ`);
  `Model.dampFamily_zero_param` (at `μ = 0` the family is the model field),
  `Model.dampFamily_origin`, `dampShift_jacobian`, `Model.fderiv_dampFamily`,
  `Model.hasDerivAt_fderiv_dampFamily` (the Jacobian is affine in `μ` with slope `∂J/∂D`).
* `Model.charpoly_hopf`: on the boundary `det(sI − J) = (s² + ω₀²)(s + D/M + ω_c)`,
  `ω₀ = √(Dω_c/M)`.
* `paramTrace_dampJac`: the transversality coefficient along the damping,
  `τ = −M ω₀² (2D² + M²ω₀²)/(D⁴ + 3D²M²ω₀² + M⁴ω₀⁴) < 0`.
* Private evidence `Model.exists_hopfCycle_damping`: since `ℓ₁ < 0` (supercritical) and
  `τ < 0`, for every small `μ < 0` (damping just below the Hopf value, where the operating
  point is unstable) the model has a nonconstant periodic orbit around the operating point with
  `κ|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8κ|μ|`, `κ = τ/(ω₀ ℓ₁) > 0`; with it the private evidence
  `Model.contDiff_augField_dampFamily` (the augmented field is smooth, hence analytic) and the
  private helper `Model.hopfData_damping` (critical pair, factorized characteristic polynomial,
  `τ < 0`, `ℓ₁ < 0`).
* Private evidence `Model.periodic_amplitude_damping`: for every `η > 0`, every small
  nonconstant periodic orbit around the operating point has `μ < 0` (none at or above the Hopf
  damping) and `(1 − η) κ|μ| ≤ ‖critπ p z(t)‖² ≤ (1 + η) κ|μ|`.
-/

noncomputable section
namespace powerlib.GFM
namespace VSMLPF
open Polynomial Complex
open powerlib.Dynamics (State mk3 state3_ext)
open powerlib.Dynamics.HopfCycle (augField xpart mpart xin emu xpart_apply)
open powerlib.NormalForm.LyapunovCoefficient

/-- The parameters with the damping shifted by `μ`: `D ↦ D + μ`. -/
def dampShift (g : VSMLPF) (μ : ℝ) : VSMLPF := ⟨g.M, g.D + μ, g.ωc, g.P0, g.K0⟩

/-- The translated field of the model with the damping `D + μ`, as a family in `μ`
(`z = x − (δ*, 0, P₀)`; the operating point does not depend on the damping). -/
def Model.dampFamily (m : Model) (z : State 3) (μ : ℝ) : State 3 :=
  (m.g.dampShift μ).field (z + m.point)

/-- The parameter derivative of the Jacobian: `∂J/∂D = −(1/M) e₁ e₁ᵀ`. -/
def dampJac (M : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, -(1 / M), 0; 0, 0, 0]

@[tmio M, simp, powerlib_domain] theorem dampShift_zero (g : VSMLPF) : g.dampShift 0 = g := by
  cases g; simp [dampShift]

@[tmio M, powerlib_domain] theorem Model.dampFamily_zero_param (m : Model) :
    (fun z => m.dampFamily z 0) = m.field := by
  funext z; simp [Model.dampFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.dampFamily_origin (m : Model) (hb : Meets m .balanced)
    (μ : ℝ) : m.dampFamily 0 μ = 0 := by
  have hb' : m.g.K0 * Real.sin m.δ = m.g.P0 := hb
  apply state3_ext <;> simp [Model.dampFamily, Model.point, dampShift, hb']

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_dampFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.dampFamily) := by
  have h : ContDiff ℝ k (fun w : State (3 + 1) => (m.g.dampShift (mpart w)).field
      (xpart w + m.point)) := by
    rw [contDiff_euclidean]
    intro i
    have hx : ∀ j : Fin 3, ContDiff ℝ k fun w : State (3 + 1) => (xpart w + m.point) j :=
      fun j => ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp
        (xpart.contDiff.add contDiff_const))
    have hm : ContDiff ℝ k fun w : State (3 + 1) => mpart w := mpart.contDiff
    fin_cases i
    · simpa [field] using hx 1
    · simp only [Fin.mk_one, Fin.isValue, field_apply_one, dampShift]
      exact (((contDiff_const.sub (hx 2)).sub ((contDiff_const.add hm).mul (hx 1))).div_const _)
    · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two, dampShift]
      exact contDiff_const.mul ((contDiff_const.mul (Real.contDiff_sin.comp (hx 0))).sub (hx 2))
  exact xin.contDiff.comp h

@[tmio M, powerlib_domain] theorem dampShift_jacobian (g : VSMLPF) (μ δ : ℝ) :
    (g.dampShift μ).jacobian δ = g.jacobian δ + μ • dampJac g.M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, dampShift, dampJac]
  ring

@[tmio M, powerlib_domain] theorem Model.fderiv_dampFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.dampFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (m.g.jacobian m.δ) +
        μ • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (dampJac m.g.M) := by
  rw [show (fun z => m.dampFamily z μ) = fun z => (m.g.dampShift μ).field (z + m.point) from rfl,
    fderiv_comp_add_right, zero_add, fderiv_field, dampShift_jacobian]
  simp [Model.point, map_add, map_smul]

/-- **Transversality data**: `μ ↦ D_z F(0, μ)` is affine with slope `toEuclideanCLM (∂J/∂D)`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_dampFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.dampFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (dampJac m.g.M)) 0 := by
  simp only [Model.fderiv_dampFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (dampJac m.g.M))).const_add
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (m.g.jacobian m.δ))

/-- On the Hopf boundary the characteristic polynomial is `(s² + ω₀²)(s + D/M + ω_c)`,
`ω₀ = √(D ω_c/M)`. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_hopf (m : Model) (hp : Meets m .physical)
    (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    (jacobianC m.field 0).charpoly =
      (X ^ 2 + C ((√(m.g.D * m.g.ωc / m.g.M) : ℂ) ^ 2)) *
        (X + C ((m.g.D / m.g.M + m.g.ωc : ℝ) : ℂ)) := by
  obtain ⟨hM, hD, hω⟩ := hp
  have hJ : jacobianC m.field 0 = (m.g.jacobian m.δ).map (fun x => (x : ℂ)) := by
    rw [jacobianC, show m.field = fun z => m.g.field (z + m.point) from rfl,
      fderiv_comp_add_right, zero_add, fderiv_field]
    simpa [Model.point] using cmat_toEuclideanCLM (m.g.jacobian m.δ)
  have hK : m.g.K0 * Real.cos m.δ = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M := hH
  have hs : (√(m.g.D * m.g.ωc / m.g.M)) ^ 2 = m.g.D * m.g.ωc / m.g.M :=
    Real.sq_sqrt (by positivity)
  have e : m.g.ωc * (m.g.K0 * Real.cos m.δ) / m.g.M =
      m.g.D * m.g.ωc / m.g.M * (m.g.D / m.g.M + m.g.ωc) := by
    rw [hK]; field_simp; ring
  rw [hJ, show (fun x : ℝ => (x : ℂ)) = ⇑(algebraMap ℝ ℂ) from rfl, Matrix.charpoly_map,
    charpoly_jacobian, e]
  rw [← Complex.ofReal_pow, hs]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div,
    Complex.coe_algebraMap, C_mul, C_add]
  ring

open powerlib.Dynamics.CenterManifold (critπ critι critι_apply critπ_apply0 critπ_apply1 reV_apply
  imV_apply)
open powerlib.Dynamics.Degenerate.PlanarFocus (e0 e1 e0_apply0 e0_apply1 e1_apply0 e1_apply1)

/-- **The transversality coefficient along the damping**:
`τ = tr (critπ p ∘ ∂J/∂D ∘ critι q) = −M ω₀² (2D² + M²ω₀²)/(D⁴ + 3D²M²ω₀² + M⁴ω₀⁴) < 0`
(`= 2 Re ⟨p, (∂J/∂D) q⟩`): more damping moves the critical eigenvalues to the left. -/
@[tmio M, powerlib_domain] theorem paramTrace_dampJac {M D ω : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hω : 0 < ω) :
    Dynamics.PlanarHopf.paramTrace ((critπ (HopfCoefficient.hopfP M D ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (dampJac M)).comp
          (critι (HopfCoefficient.hopfQ M D ω)))) =
      -(M * ω ^ 2 * (2 * D ^ 2 + M ^ 2 * ω ^ 2)) /
        (D ^ 4 + 3 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4) := by
  have hN : D ^ 4 + 3 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4 ≠ 0 := by positivity
  have hM0 := hM.ne'
  have hω0 := hω.ne'
  have hq1 : (HopfCoefficient.hopfQ M D ω 1).re = 0 ∧ (HopfCoefficient.hopfQ M D ω 1).im = ω := by
    simp [HopfCoefficient.hopfQ]
  have hp1 : (HopfCoefficient.hopfP M D ω 1).re =
        D ^ 3 * M / (2 * (D ^ 4 + 3 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4)) ∧
      (HopfCoefficient.hopfP M D ω 1).im = M ^ 2 * ω * (2 * D ^ 2 + M ^ 2 * ω ^ 2) /
        (2 * (D ^ 4 + 3 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4)) := by
    simp only [HopfCoefficient.hopfP, Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  have hB : ∀ v : State 3, Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (dampJac M) v =
      mk3 0 (-(v 1 / M)) 0 := by
    intro v
    apply state3_ext <;> simp [Dynamics.toEuclideanCLM_apply3, dampJac]
    ring
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Dynamics.mk3_zero, Dynamics.mk3_one,
    Dynamics.mk3_two, PiLp.add_apply, PiLp.sub_apply, reV_apply, imV_apply, hq1.1, hq1.2,
    hp1.1, hp1.2, RCLike.inner_apply, conj_trivial]
  field_simp
  ring

/-- The Hopf data of the damping family on the boundary: the critical pair, the factorized
characteristic polynomial with the third root `−(D/M + ω_c) < 0`, `τ < 0` and `ℓ₁ < 0`. -/
@[tmio TM, powerlib_domain] private theorem Model.hopfData_damping (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    IsCriticalPair (fun z => m.dampFamily z 0) 0 √(m.g.D * m.g.ωc / m.g.M)
        (HopfCoefficient.hopfQ m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M))
        (HopfCoefficient.hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) ∧
      (jacobianC (fun z => m.dampFamily z 0) 0).charpoly =
        (X ^ 2 + C ((√(m.g.D * m.g.ωc / m.g.M) : ℂ) ^ 2)) *
          (X + C ((m.g.D / m.g.M + m.g.ωc : ℝ) : ℂ)) ∧
      (∀ s : ℂ, (X + C ((m.g.D / m.g.M + m.g.ωc : ℝ) : ℂ)).eval s = 0 → s.re < 0) ∧
      Dynamics.PlanarHopf.paramTrace ((critπ (HopfCoefficient.hopfP m.g.M m.g.D
        √(m.g.D * m.g.ωc / m.g.M))).comp ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
          (dampJac m.g.M)).comp (critι (HopfCoefficient.hopfQ m.g.M m.g.D
            √(m.g.D * m.g.ωc / m.g.M))))) < 0 ∧
      firstLyapunov (fun z => m.dampFamily z 0) 0 √(m.g.D * m.g.ωc / m.g.M)
        (HopfCoefficient.hopfQ m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M))
        (HopfCoefficient.hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) < 0 := by
  obtain ⟨hM, hD, hωc⟩ := hp
  set ω₀ := √(m.g.D * m.g.ωc / m.g.M) with hω₀
  have hω0 : 0 < ω₀ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨?_, ?_, fun s hs => ?_, ?_, ?_⟩
  · rw [m.dampFamily_zero_param]; exact isCriticalPair m ⟨hM, hD, hωc⟩ hb hH
  · rw [m.dampFamily_zero_param]; exact m.charpoly_hopf ⟨hM, hD, hωc⟩ hH
  · simp only [eval_add, eval_X, eval_C] at hs
    have : s = -((m.g.D / m.g.M + m.g.ωc : ℝ) : ℂ) := by linear_combination hs
    rw [this, Complex.neg_re, Complex.ofReal_re]
    have : 0 < m.g.D / m.g.M + m.g.ωc := by positivity
    linarith
  · rw [paramTrace_dampJac hM hD hω0]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)
  · rw [m.dampFamily_zero_param]; exact firstLyapunov_neg m ⟨hM, hD, hωc⟩ hb hH

/-- **Hopf cycles below the Hopf damping.** On the Hopf boundary `K = D ω_c + D²/M` (balanced,
physical) the critical eigenvalues cross at speed `τ/2 < 0` in the damping
(`paramTrace_dampJac`) and `ℓ₁ < 0` (`VSMLPF.firstLyapunov_neg`), so `τ l₁ > 0`: for every small
`μ < 0` the translated model field with the damping `D + μ` has a nonconstant periodic orbit
around the operating point whose critical coordinates satisfy
`κ|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8κ|μ|`, `κ = τ/(ω₀ l₁) > 0` (`HopfCycle.exists_hopfCycle`). Private
evidence: periodic orbits are not sentences of the family. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_damping (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    ∃ δ > 0, ∃ κ > 0, ∀ μ, -δ < μ → μ < 0 →
      ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, κ * |μ| / 8 ≤
            ‖critπ (HopfCoefficient.hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) (z t)‖ ^ 2 ∧
          ‖critπ (HopfCoefficient.hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) (z t)‖ ^ 2 ≤
            8 * (κ * |μ|) := by
  obtain ⟨hcp, hchar, hr, hτn, hl⟩ := m.hopfData_damping hp hb hH
  obtain ⟨hM, hD, hωc⟩ := hp
  set ω₀ := √(m.g.D * m.g.ωc / m.g.M) with hω₀
  have hω0 : 0 < ω₀ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle m.contDiff_augField_dampFamily
    (m.contDiff_augField_dampFamily (k := ⊤)).contDiffAt.analyticAt (m.dampFamily_origin hb)
    hcp hchar hr m.hasDerivAt_fderiv_dampFamily hτn.ne hl.ne
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (HopfCoefficient.hopfP m.g.M m.g.D ω₀)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (dampJac m.g.M)).comp
        (critι (HopfCoefficient.hopfQ m.g.M m.g.D ω₀)))) with hτdef
  set ℓ := firstLyapunov (fun z => m.dampFamily z 0) 0 ω₀
      (HopfCoefficient.hopfQ m.g.M m.g.D ω₀) (HopfCoefficient.hopfP m.g.M m.g.D ω₀) with hℓdef
  have hκ : 0 < τ / (ω₀ * ℓ) := div_pos_of_neg_of_neg hτn (mul_neg_of_pos_of_neg hω0 hl)
  refine ⟨δ, hδ, τ / (ω₀ * ℓ), hκ, fun μ h1 h2 => ?_⟩
  have hμ : |μ| < δ := by rw [abs_of_neg h2]; linarith
  have hs : μ * τ * ℓ < 0 := by
    have : 0 < τ * ℓ := mul_pos_of_neg_of_neg hτn hl
    nlinarith
  obtain ⟨z, T, hT0, -, hz, hzT, hznc, hamp⟩ := hcyc μ hμ hs
  have hν : -(μ * τ) / (ω₀ * ℓ) = τ / (ω₀ * ℓ) * |μ| := by
    rw [abs_of_neg h2]; ring
  refine ⟨z, T, hT0, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hν] at this
  constructor
  · linarith [this.1]
  · linarith [this.2]

/-- **Every small cycle around the operating point is a Hopf cycle below the Hopf damping.** On
the Hopf boundary (balanced, physical), for every `η > 0` there are `δ > 0` and `κ > 0` such that
every nonconstant periodic orbit of the translated model field with the damping `D + μ`,
`|μ| < δ`, staying in the ball of radius `δ`, has `μ < 0` (no small cycle at or above the Hopf
damping) and `(1 − η) κ|μ| ≤ ‖critπ p z(t)‖² ≤ (1 + η) κ|μ|`, `κ = τ/(ω₀ l₁)`
(`HopfCycle.periodic_amplitude`). Private evidence: periodic orbits are not sentences of the
family. -/
@[tmio TM, powerlib_domain] private theorem Model.periodic_amplitude_damping (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ κ > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 3) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) → (∀ t, z (t + T) = z t) →
      (∃ t, z t ≠ z 0) → (∀ t, ‖z t‖ < δ) →
      μ < 0 ∧ ∀ t, (1 - η) * (κ * |μ|) ≤
          ‖critπ (HopfCoefficient.hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) (z t)‖ ^ 2 ∧
        ‖critπ (HopfCoefficient.hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) (z t)‖ ^ 2 ≤
          (1 + η) * (κ * |μ|) := by
  obtain ⟨hcp, hchar, hr, hτn, hl⟩ := m.hopfData_damping hp hb hH
  obtain ⟨hM, hD, hωc⟩ := hp
  set ω₀ := √(m.g.D * m.g.ωc / m.g.M) with hω₀
  have hω0 : 0 < ω₀ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨δ, hδ, hamp⟩ := Dynamics.HopfCycle.periodic_amplitude m.contDiff_augField_dampFamily
    (m.contDiff_augField_dampFamily (k := ⊤)).contDiffAt.analyticAt (m.dampFamily_origin hb)
    hcp hchar hr m.hasDerivAt_fderiv_dampFamily hτn.ne hl.ne hη
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (HopfCoefficient.hopfP m.g.M m.g.D ω₀)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (dampJac m.g.M)).comp
        (critι (HopfCoefficient.hopfQ m.g.M m.g.D ω₀)))) with hτdef
  set ℓ := firstLyapunov (fun z => m.dampFamily z 0) 0 ω₀
      (HopfCoefficient.hopfQ m.g.M m.g.D ω₀) (HopfCoefficient.hopfP m.g.M m.g.D ω₀) with hℓdef
  have hκ : 0 < τ / (ω₀ * ℓ) := div_pos_of_neg_of_neg hτn (mul_neg_of_pos_of_neg hω0 hl)
  refine ⟨δ, hδ, τ / (ω₀ * ℓ), hκ, fun μ hμ z T hT hz hzT hnc hzδ => ?_⟩
  obtain ⟨hs, hbd⟩ := hamp μ hμ z T hT hz hzT hnc hzδ
  have hτℓ : 0 < τ * ℓ := mul_pos_of_neg_of_neg hτn hl
  have hμn : μ < 0 := by
    by_contra hc
    have : 0 ≤ μ * τ * ℓ := by rw [mul_assoc]; exact mul_nonneg (not_lt.mp hc) hτℓ.le
    linarith
  have hν : -(μ * τ) / (ω₀ * ℓ) = τ / (ω₀ * ℓ) * |μ| := by
    rw [abs_of_neg hμn]; ring
  refine ⟨hμn, fun t => ?_⟩
  have := hbd t
  rw [hν] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

end VSMLPF
end powerlib.GFM
