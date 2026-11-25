import theorem.GridTiedConverter.GFM.HopfLinePSC
import theorem.Dynamics.HopfCycle

/-! # Power synchronization on a dynamic R–L line: Hopf cycles along the gain

Domain module.

Model boundary.
* The three-state power-synchronization law `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged (state `(δ, i_d, i_q)`, grid dq frame
  at `ω₀`, export-positive power, `δ̇ = K_p (P_ref − P_e)`, `L i̇ = E e^{jδ} − V − (R + jX) i`,
  constant `E`; excluded as there), read about a balanced selected angle `δ*` on the Hopf
  boundary `a₂ a₁ = a₀`, `a₁, a₀ > 0` of `theorem/GridTiedConverter/GFM/HopfLinePSC.lean`
  (every physical parameter set, every angle), and unfolded in the gain: the parameter `μ`
  replaces `K_p` by `K_p + μ` (`Line.PSC.gainShift`). The gain multiplies `P_ref − P_e`, which
  vanishes at the operating point `(δ*, i_s(δ*))`, so the translated family
  `Line.PSC.Model.gainFamily` keeps the origin as an equilibrium for every `μ`.
* Notation of `HopfLinePSC`: `σ = R/L`, `κ = K_p Q`, `a₂ = 2σ − κ`, `ω² = a₁`; the critical pair
  `(Line.PSC.Model.critQ ω, Line.PSC.Model.critP ω)`.
* Level: the static transversality data in closed form (public) and the cycles of the generic
  Hopf theorem `Dynamics.HopfCycle.exists_hopfCycle` for this family (private evidence: periodic
  orbits are not sentences of `Line.PSC.family`); no new family, no connection conclusion.
  Uniqueness and orbital stability of the cycles, the cycles at the degenerate points
  `𝔅_P = 0` and at the non-transversal points `K_p Q = −|Z|/L` are not proved.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3,
the transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`); the template
`theorem/GridTiedConverter/GFM/VSMLPFHopfCycle.lean`; the critical pair and `ℓ₁`
(`Line.PSC.Model.isCriticalPair_crit`, `Line.PSC.Model.firstLyapunov_crit`) of
`theorem/GridTiedConverter/GFM/HopfLinePSC.lean`. The closed form of `τ` was derived with SymPy
in exact arithmetic (untrusted; also from `λ' = −∂_μχ/∂_sχ` of the cubic) and is checked by the
kernel (`field_simp`, `linear_combination` with the boundary relation `ω² = σ² + ω₀² − 2σκ`).

Results.
* `Line.PSC.gainShift`, `Line.PSC.Model.gainFamily`, `Line.PSC.Model.gainJac`
  (`∂J/∂K_p = e₀ (Q, −E cos δ*, −E sin δ*)`); `Line.PSC.gainShift_zero`,
  `Line.PSC.Model.gainFamily_zero_param` (at `μ = 0` the family is the model field),
  `Line.PSC.Model.gainFamily_origin`, `Line.PSC.gainShift_jacobian`,
  `Line.PSC.Model.fderiv_gainFamily`, `Line.PSC.Model.hasDerivAt_fderiv_gainFamily` (the
  Jacobian is affine in `μ` with slope `∂J/∂K_p`).
* `Line.PSC.Model.paramTrace_gainJac_eq`: for every critical pair `(q, p)`,
  `τ = tr (critπ p ∘ ∂J/∂K_p ∘ critι q) = 2ω (Im p₀ Re q₀ − Re p₀ Im q₀)/K_p`.
* **`Line.PSC.Model.paramTrace_gainJac_crit`**: at every Hopf boundary point,
  `τ = 2σ (σ² + ω₀² − κ²)/(K_p (a₂² + ω²))`; its sign
  `Line.PSC.Model.sign_paramTrace_gainJac_crit` (`sign τ = sign (σ² + ω₀² − κ²)`) and where it
  vanishes, `Line.PSC.Model.paramTrace_gainJac_crit_eq_zero_iff` (`τ = 0` iff
  `K_p Q = −√(σ² + ω₀²) = −|Z|/L`; `τ > 0` for larger `K_p Q`, since `κ < √(σ² + ω₀²)` on the
  boundary): raising the gain destabilizes the operating point unless the reactive power is very
  negative.
* Private evidence `Line.PSC.Model.exists_hopfCycle_gain`: at every Hopf boundary point with
  `𝔅_P ≠ 0` and `K_p Q ≠ −|Z|/L`, for every small `μ` with `μ (σ² + ω₀² − κ²) 𝔅_P > 0` the model
  with the gain `K_p + μ` has a nonconstant periodic orbit around the operating point with
  `c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c = |τ|/(ω|ℓ₁|) > 0` (supercritical `𝔅_P > 0`: cycles on the
  unstable side; subcritical `𝔅_P < 0`: on the stable side); with it the private evidence
  `Line.PSC.Model.contDiff_augField_gainFamily` (the augmented field is smooth, hence analytic).
-/

noncomputable section
namespace powerlib.GFM.Line
namespace PSC
open Polynomial Complex
open powerlib.Dynamics (State mk3 state3_ext)
open powerlib.Dynamics.HopfCycle (augField xpart mpart xin)
open powerlib.NormalForm.LyapunovCoefficient

/-- The parameters with the gain shifted by `μ`: `K_p ↦ K_p + μ` (network and set-point
unchanged). -/
def gainShift (g : PSC) (μ : ℝ) : PSC := ⟨g.toNetwork, g.Kp + μ, g.Pref⟩

/-- The translated field of the model with the gain `K_p + μ`, as a family in `μ`
(`z = x − (δ*, i_s(δ*))`; the operating point does not depend on the gain). -/
def Model.gainFamily (m : Model) (z : State 3) (μ : ℝ) : State 3 :=
  (m.g.gainShift μ).field (z + m.point)

/-- The parameter derivative of the Jacobian at the operating point:
`∂J/∂K_p = e₀ (Q, −E cos δ*, −E sin δ*)` (the gain multiplies the angle row only). -/
def Model.gainJac (m : Model) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![m.Q, -(m.g.E * Real.cos m.δ), -(m.g.E * Real.sin m.δ); 0, 0, 0; 0, 0, 0]

@[tmio M, simp, powerlib_domain] theorem gainShift_zero (g : PSC) : g.gainShift 0 = g := by
  cases g; simp [gainShift]

@[tmio M, powerlib_domain] theorem Model.gainFamily_zero_param (m : Model) :
    (fun z => m.gainFamily z 0) = m.field := by
  funext z; simp [Model.gainFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.gainFamily_origin (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (μ : ℝ) : m.gainFamily 0 μ = 0 := by
  have h : m.g.field m.point = 0 :=
    (m.field_point_eq_zero_iff hp.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
  have hb' : m.g.qssPower m.δ = m.g.Pref := hb
  rw [Model.gainFamily, zero_add]
  ext i
  fin_cases i
  · simp [gainShift, Model.point, qss]
    right
    rw [← hb']
    exact sub_self _
  · simpa [field, gainShift] using congrArg (fun v : State 3 => v 1) h
  · simpa [field, gainShift] using congrArg (fun v : State 3 => v 2) h

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_gainFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.gainFamily) := by
  have h : ContDiff ℝ k (fun w : State (3 + 1) => (m.g.gainShift (mpart w)).field
      (xpart w + m.point)) := by
    rw [contDiff_euclidean]
    intro i
    have hx : ∀ j : Fin 3, ContDiff ℝ k fun w : State (3 + 1) => (xpart w + m.point) j :=
      fun j => ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).contDiff.comp
        (xpart.contDiff.add contDiff_const))
    have hm : ContDiff ℝ k fun w : State (3 + 1) => mpart w := mpart.contDiff
    have hc := fun j => (Real.contDiff_cos.comp (hx j))
    have hs := fun j => (Real.contDiff_sin.comp (hx j))
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, field_apply_zero, gainShift, Network.power_eq]
      exact (contDiff_const.add hm).mul (contDiff_const.sub (contDiff_const.mul
        (((hc 0).mul (hx 1)).add ((hs 0).mul (hx 2)))))
    · simp only [Fin.mk_one, Fin.isValue, field_apply_one, gainShift, Network.rateD]
      exact ((((contDiff_const.mul (hc 0)).sub contDiff_const).sub (contDiff_const.mul (hx 1))).add
        (contDiff_const.mul (hx 2))).div_const _
    · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two, gainShift, Network.rateQ]
      exact (((contDiff_const.mul (hs 0)).sub (contDiff_const.mul (hx 2))).sub
        (contDiff_const.mul (hx 1))).div_const _
  exact xin.contDiff.comp h

@[tmio M, powerlib_domain] theorem gainShift_jacobian (g : PSC) (μ δ id iq : ℝ) :
    (g.gainShift μ).jacobian δ id iq = g.jacobian δ id iq +
      μ • !![g.reactive δ id iq, -(g.E * Real.cos δ), -(g.E * Real.sin δ); 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, gainShift] <;> ring

@[tmio M, powerlib_domain] theorem Model.fderiv_gainFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.gainFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jac +
        μ • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac := by
  rw [show (fun z => m.gainFamily z μ) = fun z => (m.g.gainShift μ).field (z + m.point) from rfl,
    fderiv_comp_add_right, zero_add, fderiv_field, gainShift_jacobian, map_add, map_smul]
  rfl

/-- **Transversality data**: `μ ↦ D_z F(0, μ)` is affine with slope `toEuclideanCLM (∂J/∂K_p)`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_gainFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.gainFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac) 0 := by
  simp only [Model.fderiv_gainFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac)).const_add
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jac)

open powerlib.Dynamics.CenterManifold (critπ critι critι_apply critπ_apply0 critπ_apply1 reV_apply
  imV_apply)
open powerlib.Dynamics.Degenerate.PlanarFocus (e0 e1 e0_apply0 e0_apply1 e1_apply0 e1_apply1)

/-- **The transversality coefficient along the gain, for every critical pair**: for
`L, K_p ≠ 0` and a critical pair `(q, p)` of the model field at the operating point,
`τ = tr (critπ p ∘ ∂J/∂K_p ∘ critι q) = 2ω (Im p₀ Re q₀ − Re p₀ Im q₀)/K_p` (the gain row of the
eigen-equation `J q = iω q` replaces `∂J/∂K_p q` by `iω q₀/K_p e₀`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_gainJac_eq {m : Model} (hL : m.g.L ≠ 0)
    (hK : m.g.Kp ≠ 0) {ω : ℝ} {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    Dynamics.PlanarHopf.paramTrace ((critπ p).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp (critι q))) =
      2 * ω * ((p 0).im * (q 0).re - (p 0).re * (q 0).im) / m.g.Kp := by
  have h0 := congrFun hcp.right 0
  rw [m.jacobianC_field, m.jac_eq hL] at h0
  simp [Linear.complexify, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re] at hre him
  have hB : ∀ v : State 3, Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac v =
      mk3 (m.Q * v 0 - m.g.E * Real.cos m.δ * v 1 - m.g.E * Real.sin m.δ * v 2) 0 0 := by
    intro v
    apply state3_ext <;> simp [Dynamics.toEuclideanCLM_apply3, Model.gainJac]
    ring
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Dynamics.mk3_zero, Dynamics.mk3_one,
    Dynamics.mk3_two, PiLp.add_apply, PiLp.sub_apply, reV_apply, imV_apply,
    RCLike.inner_apply, conj_trivial]
  field_simp
  linear_combination (2 * (p 0).re) * hre + (2 * (p 0).im) * him

@[tmio M, powerlib_domain] private theorem crit_p0 {m : Model} {ω : ℝ} (hp : Meets m .physical)
    (hω : 0 < ω) :
    (m.critP ω 0).re = -1 / (2 * (ω ^ 2 + (2 * (m.g.R / m.g.L) - m.g.Kp * m.Q) ^ 2)) ∧
      (m.critP ω 0).im = (2 * (m.g.R / m.g.L) - m.g.Kp * m.Q) /
        (2 * ω * (ω ^ 2 + (2 * (m.g.R / m.g.L) - m.g.Kp * m.Q) ^ 2)) := by
  have hb : m.g.E / m.g.L ≠ 0 := div_ne_zero hp.1.E.ne' hp.1.L.ne'
  have hw := hp.1.ω0.ne'
  have hω0 := hω.ne'
  set a := 2 * (m.g.R / m.g.L) - m.g.Kp * m.Q with ha
  have hN : ω ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hc : critPairing (m.g.E / m.g.L) (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0 := by
    simp only [critPairing]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
    · exact_mod_cast hb
    · exact_mod_cast hw
    · exact_mod_cast hω0
    · intro h
      apply hω0
      have h' := congrArg Complex.re h
      simpa using h'
  have e : m.critP ω 0 = (((-1 / (2 * (ω ^ 2 + a ^ 2)) : ℝ) : ℂ) +
      ((a / (2 * ω * (ω ^ 2 + a ^ 2)) : ℝ) : ℂ) * I) := by
    simp only [Model.critP, rotC, critVecL, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_eq_iff_eq_mul₀ ((_root_.map_ne_zero _).mpr hc)]
    apply Complex.ext <;>
      simp [critPairing, Complex.mul_re, Complex.mul_im, -Complex.ofReal_div] <;>
      field_simp <;> ring
  rw [e]
  simp [-Complex.ofReal_div]

/-- **The transversality coefficient along the gain at every Hopf boundary point**: for every
balanced physical model on the Hopf boundary `a₂ a₁ = a₀` and its frequency `ω` (`ω² = a₁`), at
the critical pair (`Line.PSC.Model.critQ`, `Line.PSC.Model.critP`),
`τ = 2σ (σ² + ω₀² − κ²)/(K_p (a₂² + ω²))` (`σ = R/L`, `κ = K_p Q`, `a₂ = 2σ − κ`): the crossing
speed of the critical eigenvalues in the gain is `τ/2`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_gainJac_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp (critι (m.critQ ω)))) =
      2 * (m.g.R / m.g.L) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) /
        (m.g.Kp * (m.g.coeff2 m.Q ^ 2 + ω ^ 2)) := by
  have hL := hp.1.L.ne'
  have hK := hp.2.ne'
  obtain ⟨p0r, p0i⟩ := crit_p0 hp hω
  have hq0 : (m.critQ ω 0).re = (m.g.R / m.g.L) ^ 2 - ω ^ 2 + m.g.ω0 ^ 2 ∧
      (m.critQ ω 0).im = 2 * (m.g.R / m.g.L) * ω := by
    simp [Model.critQ, rotC, critVecQ, pow_two, -Complex.ofReal_div]
    ring
  rw [m.paramTrace_gainJac_eq hL hK (Model.isCriticalPair_crit hp hb hH hω hω2), p0r, p0i,
    hq0.1, hq0.2, (m.coeff_atoms hL).1]
  obtain ⟨e1, -⟩ := Model.freq_relations_of_boundary hp hH hω2
  set a := 2 * (m.g.R / m.g.L) - m.g.Kp * m.Q with ha
  have hN : ω ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hN' : a ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have hω0 := hω.ne'
  have e1' : ω ^ 2 * m.g.L ^ 2 =
      m.g.R ^ 2 + m.g.ω0 ^ 2 * m.g.L ^ 2 - 2 * m.g.R * m.g.L * (m.g.Kp * m.Q) := by
    rw [e1]; field_simp
  have ha' : a * m.g.L = 2 * m.g.R - m.g.Kp * m.Q * m.g.L := by
    rw [ha]; field_simp
  field_simp
  linear_combination (a ^ 2 + ω ^ 2) * ((m.g.R ^ 2 - ω ^ 2 * m.g.L ^ 2 + m.g.L ^ 2 * m.g.ω0 ^ 2) *
    ha' + m.g.L * (m.g.Kp * m.Q) * e1')

@[tmio M, powerlib_domain] private theorem crit_factor_pos {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (hω : 0 < ω) : 0 < 2 * (m.g.R / m.g.L) / (m.g.Kp * (m.g.coeff2 m.Q ^ 2 + ω ^ 2)) := by
  have hR := Model.R_pos_of_boundary hp hH
  have hL := hp.1.L
  have hK := hp.2
  positivity

/-- **The sign of the transversality coefficient**: at every Hopf boundary point (balanced,
physical, `a₂ a₁ = a₀`, `ω² = a₁`), `sign τ = sign (σ² + ω₀² − κ²)` (`σ = R/L`, `κ = K_p Q`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_gainJac_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp (critι (m.critQ ω))))) =
      SignType.sign ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) := by
  rw [Model.paramTrace_gainJac_crit hp hb hH hω hω2, mul_div_right_comm, sign_mul,
    sign_pos (crit_factor_pos hp hH hω), one_mul]

/-- **Where the transversality coefficient vanishes**: at every Hopf boundary point with
`a₁, a₀ > 0` (balanced, physical, `ω² = a₁`), `τ = 0` iff `K_p Q = −√(σ² + ω₀²) = −|Z|/L`;
`τ > 0` above, `τ < 0` below (`Line.PSC.Model.sign_paramTrace_gainJac_crit`: on the boundary
`κ < √(σ² + ω₀²)` always). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_gainJac_crit_eq_zero_iff {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q) (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp (critι (m.critQ ω)))) = 0 ↔
      m.g.Kp * m.Q = -Real.sqrt ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) := by
  rw [Model.paramTrace_gainJac_crit hp hb hH hω hω2, mul_div_right_comm,
    mul_eq_zero, or_iff_right (crit_factor_pos hp hH hω).ne']
  obtain ⟨c2, c1, -⟩ := m.coeff_atoms hp.1.L.ne'
  have h2 : 0 < m.g.coeff2 m.Q := by
    by_contra h2
    push Not at h2
    nlinarith
  rw [c2] at h2
  rw [c1] at h1
  set κ := m.g.Kp * m.Q
  set σ := m.g.R / m.g.L
  have hρ : 0 ≤ σ ^ 2 + m.g.ω0 ^ 2 := by positivity
  have hs := Real.sq_sqrt hρ
  have hs0 := Real.sqrt_nonneg (σ ^ 2 + m.g.ω0 ^ 2)
  constructor
  · intro h
    have hne : κ ≠ Real.sqrt (σ ^ 2 + m.g.ω0 ^ 2) := by
      intro he
      have hσ : 0 ≤ σ := div_nonneg hp.1.R hp.1.L.le
      nlinarith
    have hf : (κ - Real.sqrt (σ ^ 2 + m.g.ω0 ^ 2)) * (κ + Real.sqrt (σ ^ 2 + m.g.ω0 ^ 2)) = 0 := by
      linear_combination -h - hs
    rcases mul_eq_zero.mp hf with hf | hf
    · exact absurd (sub_eq_zero.mp hf) hne
    · linarith
  · intro h
    rw [h, neg_sq, hs, sub_self]

/-- **Hopf cycles along the gain.** At every Hopf boundary point (balanced, physical,
`a₂ a₁ = a₀`, `a₁, a₀ > 0`) off the degenerate points `𝔅_P = 0` and off `K_p Q = −√(σ² + ω₀²)`
(`τ = 0`), for every small `μ` with `μ (σ² + ω₀² − κ²) 𝔅_P > 0` the model with the gain
`K_p + μ` (translated field `Line.PSC.Model.gainFamily`) has a nonconstant periodic orbit
around the operating point whose critical coordinates satisfy
`c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c = |τ|/(ω |ℓ₁|) > 0` (`Dynamics.HopfCycle.exists_hopfCycle`
with `τ` of `Line.PSC.Model.paramTrace_gainJac_crit` and `ℓ₁` of
`Line.PSC.Model.firstLyapunov_crit`). Private evidence: periodic orbits are not sentences of
the family. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_gain (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0)
    (hκ : m.g.Kp * m.Q ≠ -Real.sqrt ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      0 < μ * (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) *
        bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift) →
      ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (m.gainFamily (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * |μ| / 8 ≤ ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t)‖ ^ 2 ≤ 8 * (c * |μ|) := by
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h1
  have hω2 : ω ^ 2 = m.g.coeff1 m.Q := Real.sq_sqrt h1.le
  have h2 : 0 < m.g.coeff2 m.Q := by
    by_contra h2
    push Not at h2
    nlinarith
  have hcp : IsCriticalPair (fun z => m.gainFamily z 0) 0 ω (m.critQ ω) (m.critP ω) := by
    rw [m.gainFamily_zero_param]; exact Model.isCriticalPair_crit hp hb hH hω hω2
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h2 hH hω2
  rw [← m.gainFamily_zero_param] at hchar
  have hτ := Model.paramTrace_gainJac_crit hp hb hH hω hω2
  have hτ0 := (Model.paramTrace_gainJac_crit_eq_zero_iff hp hb hH h1 h0 hω hω2).not.mpr hκ
  have hl := Model.firstLyapunov_crit hp hb hH h1 h0 hω hω2
  rw [← m.gainFamily_zero_param] at hl
  have hcl : 0 < 4 * (m.g.R / m.g.L) ^ 3 * ((m.g.Kp * m.Q) ^ 2 + ω ^ 2) /
      (ω ^ 3 * m.g.ω0 ^ 2 * m.g.coeff2 m.Q * (m.g.coeff2 m.Q ^ 2 + ω ^ 2) *
        (m.g.coeff2 m.Q ^ 2 + 4 * ω ^ 2)) := by
    have := Model.R_pos_of_boundary hp hH
    have := hp.1.L
    have := hp.1.ω0
    positivity
  have hl0 : firstLyapunov (fun z => m.gainFamily z 0) 0 ω (m.critQ ω) (m.critP ω) ≠ 0 := by
    rw [hl]
    exact mul_ne_zero (neg_ne_zero.mpr hcl.ne') hB
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle m.contDiff_augField_gainFamily
    (m.contDiff_augField_gainFamily (k := ⊤)).contDiffAt.analyticAt (m.gainFamily_origin hp hb)
    hcp hchar hr m.hasDerivAt_fderiv_gainFamily hτ0 hl0
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp (critι (m.critQ ω))))
    with hτdef
  set ℓ := firstLyapunov (fun z => m.gainFamily z 0) 0 ω (m.critQ ω) (m.critP ω) with hℓdef
  have hct := crit_factor_pos hp hH hω
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), by positivity, fun μ hμ hsgn => ?_⟩
  have hs : μ * τ * ℓ < 0 := by
    rw [hτ, hl]
    have e : μ * (2 * (m.g.R / m.g.L) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) /
        (m.g.Kp * (m.g.coeff2 m.Q ^ 2 + ω ^ 2))) * (-(4 * (m.g.R / m.g.L) ^ 3 *
          ((m.g.Kp * m.Q) ^ 2 + ω ^ 2) / (ω ^ 3 * m.g.ω0 ^ 2 * m.g.coeff2 m.Q *
            (m.g.coeff2 m.Q ^ 2 + ω ^ 2) * (m.g.coeff2 m.Q ^ 2 + 4 * ω ^ 2))) *
          bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift) =
        -((2 * (m.g.R / m.g.L) / (m.g.Kp * (m.g.coeff2 m.Q ^ 2 + ω ^ 2))) *
          (4 * (m.g.R / m.g.L) ^ 3 * ((m.g.Kp * m.Q) ^ 2 + ω ^ 2) /
            (ω ^ 3 * m.g.ω0 ^ 2 * m.g.coeff2 m.Q * (m.g.coeff2 m.Q ^ 2 + ω ^ 2) *
              (m.g.coeff2 m.Q ^ 2 + 4 * ω ^ 2))) *
          (μ * (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) *
            bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by ring
    rw [e]
    exact neg_neg_of_pos (mul_pos (mul_pos hct hcl) hsgn)
  obtain ⟨z, T, hT0, -, hz, hzT, hznc, hamp⟩ := hcyc μ hμ hs
  have hℓ0 : ℓ ≠ 0 := hl0
  have hν : -(μ * τ) / (ω * ℓ) = |τ| / (ω * |ℓ|) * |μ| := by
    have hpos : 0 < -(μ * τ) / (ω * ℓ) := by
      have e : -(μ * τ) / (ω * ℓ) = -(μ * τ * ℓ) / (ω * ℓ ^ 2) := by
        field_simp
      rw [e]
      exact div_pos (neg_pos.mpr hs)
        (mul_pos hω (lt_of_le_of_ne (sq_nonneg ℓ) (Ne.symm (pow_ne_zero 2 hℓ0))))
    rw [← abs_of_pos hpos, abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos hω]
    ring
  refine ⟨z, T, hT0, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hν] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

end PSC
end powerlib.GFM.Line
