import theorem.GridTiedConverter.GFM.HopfLinePSC
import theorem.Dynamics.HopfCycleBranch
import theorem.Dynamics.HopfCycleAmplitude

/-! # Power synchronization on a dynamic R–L line: Hopf cycles along the gain and the voltage

Domain module.

Model boundary.
* The three-state power-synchronization law `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged (state `(δ, i_d, i_q)`, grid dq frame
  at `ω₀`, export-positive power, `δ̇ = K_p (P_ref − P_e)`, `L i̇ = E e^{jδ} − V − (R + jX) i`,
  constant `E`; excluded as there), read about a balanced selected angle `δ*` on the Hopf
  boundary `a₂ a₁ = a₀`, `a₁, a₀ > 0` of `theorem/GridTiedConverter/GFM/HopfLinePSC.lean`
  (every physical parameter set, every angle), and unfolded in two ways.
* Along the gain: `μ` replaces `K_p` by `K_p + μ` (`Line.PSC.gainShift`); the gain multiplies
  `P_ref − P_e`, which vanishes at the operating point `(δ*, i_s(δ*))`, so the translated family
  `Line.PSC.Model.gainFamily` keeps the origin as an equilibrium for every `μ`.
* Along a direction `(a, b)` of the `(K_p, V)` plane (`Line.PSC.Model.dirParams`): gain
  `K_p + aμ`, grid voltage `V + bμ`, set-point `P_ref + bμ ∂P/∂V` (the angle `δ*` stays balanced;
  `E, R, L, ω₀` unchanged). The operating point `(δ*, i_s(δ*))` of the moved model
  (`Line.PSC.Model.dirModel`) moves with `V`: the cycles come from the moving-equilibrium law
  `Dynamics.HopfCycle.exists_hopfCycle_of_branch` (`theorem/Dynamics/HopfCycleBranch.lean`).
* Notation of `HopfLinePSC`: `σ = R/L`, `κ = K_p Q`, `a₂ = 2σ − κ`, `ω² = a₁`, `K = P'(δ*)`; the
  critical pair `(Line.PSC.Model.critQ ω, Line.PSC.Model.critP ω)`.
* Level: the static transversality data in closed form (public) and the cycles of the generic
  Hopf theorems for these families (private evidence: periodic orbits are not sentences of
  `Line.PSC.family`); no new family, no connection conclusion. Every small cycle
  (`Dynamics.HopfCycle.periodic_amplitude`, `periodic_amplitude_of_branch`): no small cycle on
  the other side; amplitude `(1 ± η) ν`. Uniqueness and orbital stability of the cycles, and the
  cycles at the degenerate points `𝔅_P = 0`, are not proved.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3,
the transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`; the shift of the equilibrium branch
to the origin); the template `theorem/GridTiedConverter/GFM/VSMLPFHopfCycle.lean`; the critical
pair and `ℓ₁` (`Line.PSC.Model.isCriticalPair_crit`, `Line.PSC.Model.firstLyapunov_crit`) of
`theorem/GridTiedConverter/GFM/HopfLinePSC.lean`. The closed forms of `τ` were derived with SymPy
in exact arithmetic (untrusted; also from `λ' = −∂_μχ/∂_sχ` of the cubic: `τ = −∂_μ(a₂a₁ − a₀)
/(a₂² + ω²)`) and are checked by the kernel (`field_simp`, `ring`, `linear_combination` with the
boundary relation `ω² = σ² + ω₀² − 2σκ`).

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
* The direction family: `Line.PSC.Model.powerV` (`∂P/∂V`), `Line.PSC.Model.reactiveV`
  (`∂Q/∂V = −K/V`), `Line.PSC.Model.dirParams`, `Line.PSC.Model.dirModel`,
  `Line.PSC.Model.voltJac` (`∂J/∂V = K_p ∂Q/∂V e₀ e₀ᵀ`), `Line.PSC.Model.transvForm`
  (`T(a, b) = a V (σ² + ω₀² − κ²) + 2b K_p² K (κ − σ)`); `Line.PSC.Model.dirParams_zero`,
  `Line.PSC.Model.dirModel_zero`, `Line.PSC.Model.dirModel_balanced`,
  `Line.PSC.Model.dirModel_field_point` (the moved point is an equilibrium for every `μ`),
  `Line.PSC.Model.jac_dirModel` (`J(μ) = J + μ (a ∂J/∂K_p + b ∂J/∂V) + μ² ab ∂Q/∂V e₀ e₀ᵀ`),
  `Line.PSC.Model.hasDerivAt_jac_dirModel` (the transversality data along the moving point).
* **`Line.PSC.Model.paramTrace_voltJac_crit`**: along the voltage, at every Hopf boundary point,
  `τ_V = 4σ K_p K (κ − σ)/(V (a₂² + ω²))` (`Line.PSC.Model.paramTrace_voltJac_eq` for every
  pair); `Line.PSC.Model.sign_paramTrace_voltJac_crit` (`sign τ_V = sign (κ − σ)`, `a₀ > 0`),
  `Line.PSC.Model.paramTrace_voltJac_crit_eq_zero_iff` (`τ_V = 0` iff `K_p Q = R/L`) and
  **`Line.PSC.Model.paramTrace_voltJac_crit_neg_of_gain`**: on the set `K_p Q = −|Z|/L` where the
  gain is not transversal, `τ_V < 0`.
* `Line.PSC.Model.paramTrace_dirJac_crit` (`τ = 2σ T(a, b)/(K_p V (a₂² + ω²))` for every
  direction), `Line.PSC.Model.sign_paramTrace_dirJac_crit` and
  **`Line.PSC.Model.transvForm_normal_pos`**: the direction `(T(1, 0), T(0, 1))` has
  `T = V²(σ² + ω₀² − κ²)² + 4K_p⁴K²(κ − σ)² > 0`; no Hopf point with `a₀ > 0` is non-transversal
  in the `(K_p, V)` plane.
* Private evidence `Line.PSC.Model.hopfData_gain`, `Line.PSC.Model.hopfData_dir` (the shared Hopf
  data), `Model.periodic_amplitude_gain`, `Model.periodic_amplitude_dir` (every small cycle is on
  the cycle side, with amplitude `(1 ± η) c|μ|`).
* Private evidence `Line.PSC.Model.exists_hopfCycle_gain`: at every Hopf boundary point with
  `𝔅_P ≠ 0` and `K_p Q ≠ −|Z|/L`, for every small `μ` with `μ (σ² + ω₀² − κ²) 𝔅_P > 0` the model
  with the gain `K_p + μ` has a nonconstant periodic orbit around the operating point with
  `c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c = |τ|/(ω|ℓ₁|) > 0` (supercritical `𝔅_P > 0`: cycles on the
  unstable side; subcritical `𝔅_P < 0`: on the stable side); with it the private evidence
  `Line.PSC.Model.contDiff_augField_gainFamily` (the augmented field is smooth, hence analytic).
* Private evidence along the `(K_p, V)` plane: `Line.PSC.Model.exists_hopfCycle_dir` (every
  direction with `T(a, b) ≠ 0`, `μ T(a, b) 𝔅_P > 0`, cycles around the moved operating point),
  `Line.PSC.Model.exists_hopfCycle_volt` (at `K_p Q = −|Z|/L`, along the voltage, `μ 𝔅_P < 0`) and
  `Line.PSC.Model.exists_hopfCycle_of_bautinForm_ne`: **at every Hopf boundary point with
  `𝔅_P ≠ 0`** (every angle, every physical parameter set), along the direction
  `𝔅_P (T(1, 0), T(0, 1))`, a nonconstant periodic orbit for every small `μ > 0`; with them
  `Line.PSC.Model.contDiff_augField_dirParams`, `Line.PSC.Model.contDiff_dirPoint`.
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

@[tmio M, powerlib_domain] private theorem crit_q0 (m : Model) (ω : ℝ) :
    (m.critQ ω 0).re = (m.g.R / m.g.L) ^ 2 - ω ^ 2 + m.g.ω0 ^ 2 ∧
      (m.critQ ω 0).im = 2 * (m.g.R / m.g.L) * ω := by
  simp [Model.critQ, rotC, critVecQ, pow_two, -Complex.ofReal_div]
  ring

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
  have hq0 := crit_q0 m ω
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

/-- The Hopf data of the gain family on the boundary (shared by the cycle and amplitude laws):
the critical pair, the factorized characteristic polynomial, `τ ≠ 0`, `ℓ₁ ≠ 0`, and
`μ τ ℓ₁ = −k μ (σ² + ω₀² − κ²) 𝔅_P` with `k > 0`. -/
@[tmio TM, powerlib_domain] private theorem Model.hopfData_gain (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0)
    (hκ : m.g.Kp * m.Q ≠ -Real.sqrt ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)) :
    ∃ r : ℂ[X], IsCriticalPair (fun z => m.gainFamily z 0) 0 (Real.sqrt (m.g.coeff1 m.Q))
        (m.critQ (Real.sqrt (m.g.coeff1 m.Q))) (m.critP (Real.sqrt (m.g.coeff1 m.Q))) ∧
      (jacobianC (fun z => m.gainFamily z 0) 0).charpoly =
        (X ^ 2 + C (((Real.sqrt (m.g.coeff1 m.Q)) : ℂ) ^ 2)) * r ∧
      (∀ s : ℂ, r.eval s = 0 → s.re < 0) ∧
      Dynamics.PlanarHopf.paramTrace ((critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q)))).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp
          (critι (m.critQ (Real.sqrt (m.g.coeff1 m.Q)))))) ≠ 0 ∧
      firstLyapunov (fun z => m.gainFamily z 0) 0 (Real.sqrt (m.g.coeff1 m.Q))
        (m.critQ (Real.sqrt (m.g.coeff1 m.Q))) (m.critP (Real.sqrt (m.g.coeff1 m.Q))) ≠ 0 ∧
      ∃ k > 0, ∀ μ : ℝ, μ * Dynamics.PlanarHopf.paramTrace
        ((critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q)))).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp
          (critι (m.critQ (Real.sqrt (m.g.coeff1 m.Q)))))) *
        (firstLyapunov (fun z => m.gainFamily z 0) 0 (Real.sqrt (m.g.coeff1 m.Q))
        (m.critQ (Real.sqrt (m.g.coeff1 m.Q))) (m.critP (Real.sqrt (m.g.coeff1 m.Q)))) =
        -(k * (μ * (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) *
        bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by
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
  have hct := crit_factor_pos hp hH hω
  refine ⟨r, hcp, hchar, hr, hτ0, hl0, _, mul_pos hct hcl, fun μ => ?_⟩
  rw [hτ, hl]
  ring

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
  obtain ⟨r, hcp, hchar, hr, hτ0, hl0, k, hk, hkey⟩ := m.hopfData_gain hp hb hH h1 h0 hB hκ
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h1
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle m.contDiff_augField_gainFamily
    (m.contDiff_augField_gainFamily (k := ⊤)).contDiffAt.analyticAt (m.gainFamily_origin hp hb)
    hcp hchar hr m.hasDerivAt_fderiv_gainFamily hτ0 hl0
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp (critι (m.critQ ω))))
    with hτdef
  set ℓ := firstLyapunov (fun z => m.gainFamily z 0) 0 ω (m.critQ ω) (m.critP ω) with hℓdef
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), div_pos (abs_pos.mpr hτ0) (mul_pos hω (abs_pos.mpr hl0)),
    fun μ hμ hsgn => ?_⟩
  have hs : μ * τ * ℓ < 0 := by rw [hkey]; exact neg_neg_of_pos (mul_pos hk hsgn)
  obtain ⟨z, T, hT0, -, hz, hzT, hznc, hamp⟩ := hcyc μ hμ hs
  have hν := Dynamics.HopfCycle.hopfAmplitude_eq_abs hω hs
  refine ⟨z, T, hT0, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hν] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **Every small cycle along the gain.** With the hypotheses of `Model.exists_hopfCycle_gain`:
for every `η > 0` there are `δ, c > 0` such that every nonconstant periodic orbit of the gain
family, `|μ| < δ`, in the ball of radius `δ`, has `μ (σ² + ω₀² − κ²) 𝔅_P > 0` (none on the other
side) and `(1 − η) c|μ| ≤ ‖critπ p z(t)‖² ≤ (1 + η) c|μ|` (`HopfCycle.periodic_amplitude`).
Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.periodic_amplitude_gain (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0)
    (hκ : m.g.Kp * m.Q ≠ -Real.sqrt ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 3) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z (m.gainFamily (z t) μ) t) → (∀ t, z (t + T) = z t) →
      (∃ t, z t ≠ z 0) → (∀ t, ‖z t‖ < δ) →
      0 < μ * (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) *
        bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift) ∧
        ∀ t, (1 - η) * (c * |μ|) ≤ ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t)‖ ^ 2 ≤ (1 + η) * (c * |μ|) := by
  obtain ⟨r, hcp, hchar, hr, hτ0, hl0, k, hk, hkey⟩ := m.hopfData_gain hp hb hH h1 h0 hB hκ
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h1
  obtain ⟨δ, hδ, hamp⟩ := Dynamics.HopfCycle.periodic_amplitude m.contDiff_augField_gainFamily
    (m.contDiff_augField_gainFamily (k := ⊤)).contDiffAt.analyticAt (m.gainFamily_origin hp hb)
    hcp hchar hr m.hasDerivAt_fderiv_gainFamily hτ0 hl0 hη
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.gainJac).comp (critι (m.critQ ω))))
    with hτdef
  set ℓ := firstLyapunov (fun z => m.gainFamily z 0) 0 ω (m.critQ ω) (m.critP ω) with hℓdef
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), div_pos (abs_pos.mpr hτ0) (mul_pos hω (abs_pos.mpr hl0)),
    fun μ hμ z T hT hz hzT hnc hzδ => ?_⟩
  obtain ⟨hs, hbd⟩ := hamp μ hμ z T hT hz hzT hnc hzδ
  have hpos := hs
  rw [hkey] at hpos
  refine ⟨pos_of_mul_pos_right (neg_neg_iff_pos.mp hpos) hk.le, fun t => ?_⟩
  rw [Dynamics.HopfCycle.hopfAmplitude_eq_abs hω hs] at hbd
  exact hbd t

/-! ## A direction of the `(K_p, V)` plane: a family with a moving operating point -/

/-- The voltage sensitivity of the quasi-steady power at the selected angle,
`∂P/∂V = E (X sin δ* − R cos δ*)/|Z|²`. -/
def Model.powerV (m : Model) : ℝ :=
  m.g.E * (m.g.X * Real.sin m.δ - m.g.R * Real.cos m.δ) / m.g.absSq

/-- The voltage sensitivity of the quasi-steady reactive power at the selected angle,
`∂Q/∂V = −E (X cos δ* + R sin δ*)/|Z|²` (`= −K/V`). -/
def Model.reactiveV (m : Model) : ℝ :=
  -(m.g.E * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) / m.g.absSq)

/-- The parameters moved along the direction `(a, b)` of the `(K_p, V)` plane: gain `K_p + aμ`,
grid voltage `V + bμ`, and the set-point `P_ref + bμ ∂P/∂V` that keeps the angle `δ*` balanced
(network otherwise unchanged). -/
def Model.dirParams (m : Model) (a b μ : ℝ) : PSC :=
  ⟨⟨m.g.E, m.g.V + b * μ, m.g.R, m.g.L, m.g.ω0⟩, m.g.Kp + a * μ, m.g.Pref + b * μ * m.powerV⟩

/-- The moved model at the same angle; its operating point `(δ*, i_s(δ*))` moves with `V`. -/
def Model.dirModel (m : Model) (a b μ : ℝ) : Model := ⟨m.dirParams a b μ, m.δ⟩

/-- The voltage derivative of the Jacobian at the operating point, `∂J/∂V = K_p (∂Q/∂V) e₀ e₀ᵀ`
(the current `i_s(δ*)` enters the Jacobian only through `Q_e`). -/
def Model.voltJac (m : Model) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![m.g.Kp * m.reactiveV, 0, 0; 0, 0, 0; 0, 0, 0]

/-- The transversality form of the direction `(a, b)`:
`a V (σ² + ω₀² − κ²) + 2b K_p² K (κ − σ)` (`σ = R/L`, `κ = K_p Q`, `K = P'(δ*)`). -/
def Model.transvForm (m : Model) (a b : ℝ) : ℝ :=
  a * m.g.V * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2) +
    2 * b * m.g.Kp ^ 2 * m.K * (m.g.Kp * m.Q - m.g.R / m.g.L)

@[tmio M, simp, powerlib_domain] theorem Model.dirParams_zero (m : Model) (a b : ℝ) :
    m.dirParams a b 0 = m.g := by
  rcases m with ⟨⟨⟨E, V, R, L, ω0⟩, Kp, Pref⟩, δ⟩
  simp [Model.dirParams]

@[tmio M, simp, powerlib_domain] theorem Model.dirModel_zero (m : Model) (a b : ℝ) :
    m.dirModel a b 0 = m := by
  simp [Model.dirModel]

/-- **The moved model stays balanced**: `P(δ*) = P_ref + bμ ∂P/∂V` for the voltage `V + bμ`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.dirModel_balanced {m : Model} (hZ : m.g.absSq ≠ 0)
    (hb : Meets m .balanced) (a b μ : ℝ) : Meets (m.dirModel a b μ) .balanced := by
  have hb' : m.g.qssPower m.δ = m.g.Pref := hb
  show (m.dirParams a b μ).qssPower m.δ = (m.dirParams a b μ).Pref
  rw [Network.qssPower_eq _ hZ] at hb'
  rw [Network.qssPower_eq (m.dirParams a b μ).toNetwork hZ]
  simp only [Model.dirParams, Model.powerV, Network.absSq, Network.X] at hb' hZ ⊢
  rw [← hb']
  field_simp
  ring

/-- **The moved operating point is an equilibrium** of the moved model, for every `μ` (balanced
physical `m`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.dirModel_field_point {m : Model}
    (hp : Meets m .physical) (hb : Meets m .balanced) (a b μ : ℝ) :
    (m.dirModel a b μ).g.field (m.dirModel a b μ).point = 0 := by
  have hZ := hp.1.absSq_pos.ne'
  have hL := hp.1.L.ne'
  set M := m.dirModel a b μ
  have hb' : M.g.qssPower M.δ = M.g.Pref := m.dirModel_balanced hZ hb a b μ
  have hr := (M.g.rate_eq_zero_iff hL hZ M.δ (M.g.is M.δ).re (M.g.is M.δ).im).mpr ⟨rfl, rfl⟩
  apply state3_ext
  · show M.g.Kp * (M.g.Pref - M.g.qssPower M.δ) = (0 : State 3) 0
    rw [hb', sub_self, mul_zero]
    rfl
  · show M.g.rateD M.δ (M.g.is M.δ).re (M.g.is M.δ).im = (0 : State 3) 1
    rw [hr.1]
    rfl
  · show M.g.rateQ M.δ (M.g.is M.δ).re (M.g.is M.δ).im = (0 : State 3) 2
    rw [hr.2]
    rfl

/-- **The Jacobian along the moved operating point**:
`J(μ) = J + μ (a ∂J/∂K_p + b ∂J/∂V) + μ² ab (∂Q/∂V) e₀ e₀ᵀ` (the gain multiplies the angle row;
`Q_e` at `i_s(δ*)` is affine in `V`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.jac_dirModel (m : Model) (a b μ : ℝ) :
    (m.dirModel a b μ).jac = m.jac + μ • (a • m.gainJac + b • m.voltJac) +
      μ ^ 2 • !![a * b * m.reactiveV, 0, 0; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.jac, jacobian, Model.dirModel, Model.dirParams, Model.gainJac, Model.voltJac,
      Model.reactiveV, Model.Q, Network.qssReactive, Network.reactive_eq, Network.is_re,
      Network.is_im, Network.X, Network.absSq] <;>
    ring

/-- **The transversality data of the direction family**: the Jacobian at the moved operating
point has the derivative `a ∂J/∂K_p + b ∂J/∂V` at `μ = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_jac_dirModel (m : Model) (a b : ℝ) :
    HasDerivAt (fun μ => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (m.dirModel a b μ).jac)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac)) 0 := by
  simp only [m.jac_dirModel, map_add, map_smul]
  have h := (((hasDerivAt_id (0 : ℝ)).smul_const
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac))).add
    ((hasDerivAt_pow 2 (0 : ℝ)).smul_const (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
      !![a * b * m.reactiveV, 0, 0; 0, 0, 0; 0, 0, 0]))).const_add
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jac)
  convert h using 1
  · funext μ; simp [map_add, map_smul, add_assoc]
  · simp

/-- **The transversality coefficient of the voltage, for every pair** `(q, p)`:
`τ_V = tr (critπ p ∘ ∂J/∂V ∘ critι q) = 2 K_p ∂Q/∂V (Re p₀ Re q₀ + Im p₀ Im q₀)`. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_voltJac_eq (m : Model) (q p : Fin 3 → ℂ) :
    Dynamics.PlanarHopf.paramTrace ((critπ p).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.voltJac).comp (critι q))) =
      2 * (m.g.Kp * m.reactiveV) * ((p 0).re * (q 0).re + (p 0).im * (q 0).im) := by
  have hB : ∀ v : State 3, Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.voltJac v =
      mk3 (m.g.Kp * m.reactiveV * v 0) 0 0 := by
    intro v
    apply state3_ext <;> simp [Dynamics.toEuclideanCLM_apply3, Model.voltJac]
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Dynamics.mk3_zero, Dynamics.mk3_one,
    Dynamics.mk3_two, PiLp.add_apply, PiLp.sub_apply, reV_apply, imV_apply,
    RCLike.inner_apply, conj_trivial]
  ring

@[tmio M, powerlib_domain] private theorem K_mul_absSq {m : Model} (hZ : 0 < m.g.absSq) :
    m.K * m.g.absSq = m.g.E * m.g.V * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) := by
  have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
  have h2 := m.g.qssReactive_eq hZ.ne' m.δ
  rw [Model.K, show m.g.syncCoeff m.δ = m.g.κ - m.g.qssReactive m.δ by linarith, h2,
    Network.κ]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem K_pos_of_boundary {m : Model}
    (hp : Meets m .physical) (h0 : 0 < m.g.coeff0 m.Q) : 0 < m.K := by
  have hZ := hp.1.absSq_pos
  rw [m.coeff0_eq hp.1.L.ne' hZ] at h0
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hp.1.L.ne']
    rw [this]; exact div_pos hZ (pow_pos hp.1.L 2)
  have hK := hp.2
  by_contra h
  push Not at h
  nlinarith [mul_nonneg hK.le (mul_nonneg hρ.le (neg_nonneg.mpr h))]

/-- **The transversality coefficient of the voltage at every Hopf boundary point**:
`τ_V = 4σ K_p K (κ − σ)/(V (a₂² + ω²))` (`σ = R/L`, `κ = K_p Q`, `K = P'(δ*)`, `a₂ = 2σ − κ`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_voltJac_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.voltJac).comp (critι (m.critQ ω)))) =
      4 * (m.g.R / m.g.L) * (m.g.Kp * m.K) * (m.g.Kp * m.Q - m.g.R / m.g.L) /
        (m.g.V * (m.g.coeff2 m.Q ^ 2 + ω ^ 2)) := by
  have hZ := hp.1.absSq_pos
  have hV := hp.1.V.ne'
  have hL := hp.1.L.ne'
  obtain ⟨p0r, p0i⟩ := crit_p0 hp hω
  obtain ⟨q0r, q0i⟩ := crit_q0 m ω
  have hK' : m.K = m.g.E * m.g.V * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) / m.g.absSq := by
    rw [eq_div_iff hZ.ne']; exact K_mul_absSq hZ
  have hrV : m.g.Kp * m.reactiveV = -(m.g.Kp * m.K) / m.g.V := by
    rw [Model.reactiveV, hK']
    field_simp
  rw [m.paramTrace_voltJac_eq, p0r, p0i, q0r, q0i, (m.coeff_atoms hL).1, hrV]
  obtain ⟨e1, -⟩ := Model.freq_relations_of_boundary hp hH hω2
  set σ := m.g.R / m.g.L
  set κ := m.g.Kp * m.Q
  set k := m.g.Kp * m.K
  have hN : ω ^ 2 + (2 * σ - κ) ^ 2 ≠ 0 := by positivity
  have hN' : (2 * σ - κ) ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have hω0 := hω.ne'
  have hd : 2 * (-k / m.g.V) *
      (-1 / (2 * (ω ^ 2 + (2 * σ - κ) ^ 2)) * (σ ^ 2 - ω ^ 2 + m.g.ω0 ^ 2) +
        (2 * σ - κ) / (2 * ω * (ω ^ 2 + (2 * σ - κ) ^ 2)) * (2 * σ * ω)) -
      4 * σ * k * (κ - σ) / (m.g.V * ((2 * σ - κ) ^ 2 + ω ^ 2)) =
      -k * (ω ^ 2 - (σ ^ 2 + m.g.ω0 ^ 2 - 2 * σ * κ)) / (m.g.V * (ω ^ 2 + (2 * σ - κ) ^ 2)) := by
    field_simp
    ring
  rw [← e1, sub_self, mul_zero, zero_div, sub_eq_zero] at hd
  exact hd

@[tmio M, powerlib_domain] private theorem volt_factor_pos {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q) (hω : 0 < ω) :
    0 < 4 * (m.g.R / m.g.L) * (m.g.Kp * m.K) / (m.g.V * (m.g.coeff2 m.Q ^ 2 + ω ^ 2)) := by
  have hR := Model.R_pos_of_boundary hp hH
  have hK := K_pos_of_boundary hp h0
  have hL := hp.1.L
  have hV := hp.1.V
  have hKp := hp.2
  positivity

/-- **The sign of the voltage transversality coefficient**: at every Hopf boundary point
(physical, `a₂ a₁ = a₀`, `a₀ > 0`, `ω² = a₁`), `sign τ_V = sign (κ − σ)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_voltJac_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q) (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.voltJac).comp (critι (m.critQ ω))))) =
      SignType.sign (m.g.Kp * m.Q - m.g.R / m.g.L) := by
  rw [Model.paramTrace_voltJac_crit hp hH hω hω2, mul_div_right_comm, sign_mul,
    sign_pos (volt_factor_pos hp hH h0 hω), one_mul]

/-- **Where the voltage transversality coefficient vanishes**: at every Hopf boundary point,
`τ_V = 0` iff `K_p Q = R/L`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_voltJac_crit_eq_zero_iff {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q) (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.voltJac).comp (critι (m.critQ ω)))) = 0 ↔
      m.g.Kp * m.Q = m.g.R / m.g.L := by
  rw [Model.paramTrace_voltJac_crit hp hH hω hω2, mul_div_right_comm, mul_eq_zero,
    or_iff_right (volt_factor_pos hp hH h0 hω).ne', sub_eq_zero]

/-- **The voltage is transversal where the gain is not**: at every Hopf boundary point with
`K_p Q = −√(σ² + ω₀²) = −|Z|/L` (where `Line.PSC.Model.paramTrace_gainJac_crit` vanishes),
`τ_V = −4σ K_p K (√(σ² + ω₀²) + σ)/(V (a₂² + ω²)) < 0`: raising the grid voltage stabilizes.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_voltJac_crit_neg_of_gain {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q) (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q)
    (hκ : m.g.Kp * m.Q = -Real.sqrt ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.voltJac).comp
          (critι (m.critQ ω)))) < 0 := by
  have hs := Model.sign_paramTrace_voltJac_crit hp hH h0 hω hω2
  have hσ : 0 < m.g.R / m.g.L := div_pos (Model.R_pos_of_boundary hp hH) hp.1.L
  have hneg : m.g.Kp * m.Q - m.g.R / m.g.L < 0 := by
    rw [hκ]
    linarith [Real.sqrt_nonneg ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)]
  rw [sign_neg hneg] at hs
  exact sign_eq_neg_one_iff.mp hs

/-- **The transversality coefficient of every direction `(a, b)` of the `(K_p, V)` plane**: at
every Hopf boundary point (balanced, physical, `a₂ a₁ = a₀`, `ω² = a₁`),
`τ = a τ_{K_p} + b τ_V = 2σ T(a, b)/(K_p V (a₂² + ω²))`, `T = Line.PSC.Model.transvForm`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_dirJac_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) (a b : ℝ) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac)).comp
          (critι (m.critQ ω)))) =
      2 * (m.g.R / m.g.L) * m.transvForm a b /
        (m.g.Kp * m.g.V * (m.g.coeff2 m.Q ^ 2 + ω ^ 2)) := by
  have hL := hp.1.L.ne'
  have hV := hp.1.V.ne'
  have hK := hp.2.ne'
  have hN : m.g.coeff2 m.Q ^ 2 + ω ^ 2 ≠ 0 := by have := hω; positivity
  rw [map_add, map_smul, map_smul, Dynamics.HopfCycle.paramTrace_comp_add_smul,
    Model.paramTrace_gainJac_crit hp hb hH hω hω2, Model.paramTrace_voltJac_crit hp hH hω hω2,
    Model.transvForm]
  field_simp
  ring

/-- **The sign of the transversality coefficient of a direction**: `sign τ = sign T(a, b)` at
every Hopf boundary point. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_dirJac_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) (a b : ℝ) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac)).comp
          (critι (m.critQ ω))))) = SignType.sign (m.transvForm a b) := by
  have hR := Model.R_pos_of_boundary hp hH
  have hL := hp.1.L
  have hV := hp.1.V
  have hK := hp.2
  have hpos : 0 < 2 * (m.g.R / m.g.L) / (m.g.Kp * m.g.V * (m.g.coeff2 m.Q ^ 2 + ω ^ 2)) := by
    have := hω; positivity
  rw [Model.paramTrace_dirJac_crit hp hb hH hω hω2, mul_div_right_comm, sign_mul,
    sign_pos hpos, one_mul]

/-- **No Hopf point is non-transversal in the `(K_p, V)` plane**: at every Hopf boundary point
with `a₀ > 0` the direction `(T(1, 0), T(0, 1))` has
`T = V² (σ² + ω₀² − κ²)² + 4 K_p⁴ K² (κ − σ)² > 0` (the two coefficients `τ_{K_p}`, `τ_V` never
vanish together). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.transvForm_normal_pos {m : Model}
    (hp : Meets m .physical) (h0 : 0 < m.g.coeff0 m.Q) :
    0 < m.transvForm (m.transvForm 1 0) (m.transvForm 0 1) := by
  have hK := K_pos_of_boundary hp h0
  have hKp := hp.2
  have hV := hp.1.V
  have hw := hp.1.ω0
  have e : m.transvForm (m.transvForm 1 0) (m.transvForm 0 1) =
      (m.g.V * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.Kp * m.Q) ^ 2)) ^ 2 +
        4 * (m.g.Kp ^ 2 * m.K * (m.g.Kp * m.Q - m.g.R / m.g.L)) ^ 2 := by
    simp only [Model.transvForm]; ring
  rw [e]
  rcases eq_or_ne (m.g.Kp * m.Q) (m.g.R / m.g.L) with h | h
  · rw [h, sub_self, mul_zero, sq (0 : ℝ), mul_zero, mul_zero, add_zero,
      show (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - (m.g.R / m.g.L) ^ 2 = m.g.ω0 ^ 2 by ring]
    positivity
  · have : 0 < (m.g.Kp ^ 2 * m.K * (m.g.Kp * m.Q - m.g.R / m.g.L)) ^ 2 := by
      have := sub_ne_zero.mpr h
      positivity
    positivity

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_dirParams (m : Model)
    (a b : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (augField fun x μ => (m.dirParams a b μ).field x) := by
  have h : ContDiff ℝ k (fun w : State (3 + 1) => (m.dirParams a b (mpart w)).field (xpart w)) := by
    rw [contDiff_euclidean]
    intro i
    have h0 : ContDiff ℝ k fun w : State (3 + 1) => xpart w 0 :=
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).contDiff.comp xpart.contDiff
    have h1 : ContDiff ℝ k fun w : State (3 + 1) => xpart w 1 :=
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1).contDiff.comp xpart.contDiff
    have h2 : ContDiff ℝ k fun w : State (3 + 1) => xpart w 2 :=
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2).contDiff.comp xpart.contDiff
    have hm : ContDiff ℝ k fun w : State (3 + 1) => mpart w := mpart.contDiff
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, field_apply_zero, Model.dirParams, Network.power_eq]
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, field_apply_one, Model.dirParams, Network.rateD,
        Network.X]
      fun_prop
    · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two, Model.dirParams, Network.rateQ,
        Network.X]
      fun_prop
  exact xin.contDiff.comp h

@[tmio M, powerlib_domain] private theorem Model.contDiff_dirPoint (m : Model) (a b : ℝ)
    {k : WithTop ℕ∞} : ContDiff ℝ k (fun μ => (m.dirModel a b μ).point) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;>
    simp [Model.point, qss, Model.dirModel, Model.dirParams, Network.is_re, Network.is_im,
      Network.X, Network.absSq] <;>
    fun_prop

/-- The Hopf data of a direction family about its moving operating point (shared by the cycle
and amplitude laws): the critical pair, the factorized characteristic polynomial, the parameter
derivative of the Jacobian along the branch, `τ ≠ 0`, `ℓ₁ ≠ 0`, and
`μ τ ℓ₁ = −k μ 𝔗(a, b) 𝔅_P` with `k > 0`. -/
@[tmio TM, powerlib_domain] private theorem Model.hopfData_dir (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0) {a b : ℝ}
    (hT : m.transvForm a b ≠ 0) :
    ∃ r : ℂ[X], IsCriticalPair (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point
        (Real.sqrt (m.g.coeff1 m.Q)) (m.critQ (Real.sqrt (m.g.coeff1 m.Q)))
        (m.critP (Real.sqrt (m.g.coeff1 m.Q))) ∧
      (jacobianC (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point).charpoly =
        (X ^ 2 + C (((Real.sqrt (m.g.coeff1 m.Q)) : ℂ) ^ 2)) * r ∧
      (∀ s : ℂ, r.eval s = 0 → s.re < 0) ∧
      HasDerivAt (fun μ => fderiv ℝ (fun x => (m.dirParams a b μ).field x)
        (m.dirModel a b μ).point) (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
          (a • m.gainJac + b • m.voltJac)) 0 ∧
      Dynamics.PlanarHopf.paramTrace ((critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q)))).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
          (a • m.gainJac + b • m.voltJac)).comp
            (critι (m.critQ (Real.sqrt (m.g.coeff1 m.Q)))))) ≠ 0 ∧
      firstLyapunov (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point
        (Real.sqrt (m.g.coeff1 m.Q)) (m.critQ (Real.sqrt (m.g.coeff1 m.Q)))
          (m.critP (Real.sqrt (m.g.coeff1 m.Q))) ≠ 0 ∧
      ∃ k > 0, ∀ μ : ℝ, μ * Dynamics.PlanarHopf.paramTrace
        ((critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q)))).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
          (a • m.gainJac + b • m.voltJac)).comp (critι (m.critQ (Real.sqrt (m.g.coeff1 m.Q)))))) *
        firstLyapunov (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point
          (Real.sqrt (m.g.coeff1 m.Q)) (m.critQ (Real.sqrt (m.g.coeff1 m.Q)))
            (m.critP (Real.sqrt (m.g.coeff1 m.Q))) =
        -(k * (μ * (m.transvForm a b *
          bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h1
  have hω2 : ω ^ 2 = m.g.coeff1 m.Q := Real.sq_sqrt h1.le
  have h2 : 0 < m.g.coeff2 m.Q := by
    by_contra h2
    push Not at h2
    nlinarith
  have e0 : (fun x => (m.dirParams a b 0).field x) = m.g.field := by rw [m.dirParams_zero]
  have e1 : (m.dirModel a b 0).point = m.point := by rw [m.dirModel_zero]
  have hcp : IsCriticalPair (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point ω
      (m.critQ ω) (m.critP ω) := by
    rw [e0, e1]
    exact (isCriticalPair_comp_add (f := m.g.field) (x₀ := m.point)).mp
      (Model.isCriticalPair_crit hp hb hH hω hω2)
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h2 hH hω2
  have hchar' : (jacobianC (fun x => (m.dirParams a b 0).field x)
      (m.dirModel a b 0).point).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r := by
    rw [e0, e1, ← jacobianC_comp_add m.g.field m.point]
    exact hchar
  have hl' : firstLyapunov (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point ω
      (m.critQ ω) (m.critP ω) = firstLyapunov m.field 0 ω (m.critQ ω) (m.critP ω) := by
    rw [e0, e1, ← firstLyapunov_comp_add m.g.field m.point]
    rfl
  have hBd : HasDerivAt (fun μ => fderiv ℝ (fun x => (m.dirParams a b μ).field x)
      (m.dirModel a b μ).point)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac)) 0 := by
    have e : (fun μ => fderiv ℝ (fun x => (m.dirParams a b μ).field x) (m.dirModel a b μ).point) =
        fun μ => Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (m.dirModel a b μ).jac :=
      funext fun μ => (m.dirModel a b μ).fderiv_point
    rw [e]
    exact m.hasDerivAt_jac_dirModel a b
  have hτ := Model.paramTrace_dirJac_crit hp hb hH hω hω2 a b
  have hR := Model.R_pos_of_boundary hp hH
  have hfac : 0 < 2 * (m.g.R / m.g.L) / (m.g.Kp * m.g.V * (m.g.coeff2 m.Q ^ 2 + ω ^ 2)) := by
    have := hp.1.L
    have := hp.1.V
    have := hp.2
    positivity
  have hτ0 : Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac)).comp
        (critι (m.critQ ω)))) ≠ 0 := by
    rw [hτ, mul_div_right_comm]
    exact mul_ne_zero hfac.ne' hT
  have hl := Model.firstLyapunov_crit hp hb hH h1 h0 hω hω2
  have hcl : 0 < 4 * (m.g.R / m.g.L) ^ 3 * ((m.g.Kp * m.Q) ^ 2 + ω ^ 2) /
      (ω ^ 3 * m.g.ω0 ^ 2 * m.g.coeff2 m.Q * (m.g.coeff2 m.Q ^ 2 + ω ^ 2) *
        (m.g.coeff2 m.Q ^ 2 + 4 * ω ^ 2)) := by
    have := hp.1.L
    have := hp.1.ω0
    positivity
  have hl0 : firstLyapunov (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point ω
      (m.critQ ω) (m.critP ω) ≠ 0 := by
    rw [hl', hl]
    exact mul_ne_zero (neg_ne_zero.mpr hcl.ne') hB
  refine ⟨r, hcp, hchar', hr, hBd, hτ0, hl0, _, mul_pos hfac hcl, fun μ => ?_⟩
  rw [hτ, hl', hl]
  ring

/-- **Hopf cycles along a direction of the `(K_p, V)` plane.** At every Hopf boundary point
(balanced, physical, `a₂ a₁ = a₀`, `a₁, a₀ > 0`) off the degenerate points `𝔅_P = 0`, for every
direction `(a, b)` with `T(a, b) ≠ 0` (`Line.PSC.Model.transvForm`) and every small `μ` with
`μ T(a, b) 𝔅_P > 0`, the model with the gain `K_p + aμ`, the grid voltage `V + bμ` and the
set-point `P_ref + bμ ∂P/∂V` (`Line.PSC.Model.dirParams`) has a nonconstant periodic orbit around
its operating point `(δ*, i_s(δ*))`, which moves with `V`, with
`c|μ|/8 ≤ ‖critπ p (z(t) − x*(μ))‖² ≤ 8c|μ|`, `c = |τ|/(ω |ℓ₁|) > 0`
(`Dynamics.HopfCycle.exists_hopfCycle_of_branch`, `τ` of `Line.PSC.Model.paramTrace_dirJac_crit`,
`ℓ₁` of `Line.PSC.Model.firstLyapunov_crit`). Private evidence: periodic orbits are not sentences
of the family. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_dir (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0) {a b : ℝ}
    (hT : m.transvForm a b ≠ 0) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      0 < μ * (m.transvForm a b * bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift) →
      ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z ((m.dirParams a b μ).field (z t)) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * |μ| / 8 ≤
            ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel a b μ).point)‖ ^ 2 ∧
          ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel a b μ).point)‖ ^ 2 ≤
            8 * (c * |μ|) := by
  obtain ⟨r, hcp, hchar', hr, hBd, hτ0, hl0, k, hk, hkey⟩ := m.hopfData_dir hp hb hH h1 h0 hB hT
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h1
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle_of_branch
    (F := fun x μ => (m.dirParams a b μ).field x) (xs := fun μ => (m.dirModel a b μ).point)
    (m.contDiff_augField_dirParams a b)
    ((m.contDiff_augField_dirParams a b (k := ⊤)).contDiffAt.analyticAt)
    (m.contDiff_dirPoint a b) ((m.contDiff_dirPoint a b (k := ⊤)).contDiffAt.analyticAt)
    (fun μ => m.dirModel_field_point hp hb a b μ) hcp hchar' hr hBd hτ0 hl0
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac)).comp
        (critι (m.critQ ω)))) with hτdef
  set ℓ := firstLyapunov (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point ω
      (m.critQ ω) (m.critP ω) with hℓdef
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), div_pos (abs_pos.mpr hτ0) (mul_pos hω (abs_pos.mpr hl0)),
    fun μ hμ hsgn => ?_⟩
  have hs : μ * τ * ℓ < 0 := by rw [hkey]; exact neg_neg_of_pos (mul_pos hk hsgn)
  obtain ⟨z, T, hT0, -, hz, hzT, hznc, hamp⟩ := hcyc μ hμ hs
  have hν := Dynamics.HopfCycle.hopfAmplitude_eq_abs hω hs
  refine ⟨z, T, hT0, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hν] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **Every small cycle along a direction of the `(K_p, V)` plane.** With the hypotheses of
`Model.exists_hopfCycle_dir`: for every `η > 0` there are `δ, c > 0` such that every nonconstant
periodic orbit of the direction family, `|μ| < δ`, within `δ` of the moved operating point, has
`μ 𝔗(a, b) 𝔅_P > 0` (none on the other side) and
`(1 − η) c|μ| ≤ ‖critπ p (z(t) − x*(μ))‖² ≤ (1 + η) c|μ|`
(`HopfCycle.periodic_amplitude_of_branch`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.periodic_amplitude_dir (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0) {a b : ℝ}
    (hT : m.transvForm a b ≠ 0) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 3) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z ((m.dirParams a b μ).field (z t)) t) → (∀ t, z (t + T) = z t) →
      (∃ t, z t ≠ z 0) → (∀ t, ‖z t - (m.dirModel a b μ).point‖ < δ) →
      0 < μ * (m.transvForm a b * bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift) ∧
        ∀ t, (1 - η) * (c * |μ|) ≤
            ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel a b μ).point)‖ ^ 2 ∧
          ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel a b μ).point)‖ ^ 2 ≤
            (1 + η) * (c * |μ|) := by
  obtain ⟨r, hcp, hchar', hr, hBd, hτ0, hl0, k, hk, hkey⟩ := m.hopfData_dir hp hb hH h1 h0 hB hT
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h1
  obtain ⟨δ, hδ, hamp⟩ := Dynamics.HopfCycle.periodic_amplitude_of_branch
    (F := fun x μ => (m.dirParams a b μ).field x) (xs := fun μ => (m.dirModel a b μ).point)
    (m.contDiff_augField_dirParams a b)
    ((m.contDiff_augField_dirParams a b (k := ⊤)).contDiffAt.analyticAt)
    (m.contDiff_dirPoint a b) ((m.contDiff_dirPoint a b (k := ⊤)).contDiffAt.analyticAt)
    (fun μ => m.dirModel_field_point hp hb a b μ) hcp hchar' hr hBd hτ0 hl0 hη
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (a • m.gainJac + b • m.voltJac)).comp
        (critι (m.critQ ω)))) with hτdef
  set ℓ := firstLyapunov (fun x => (m.dirParams a b 0).field x) (m.dirModel a b 0).point ω
      (m.critQ ω) (m.critP ω) with hℓdef
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), div_pos (abs_pos.mpr hτ0) (mul_pos hω (abs_pos.mpr hl0)),
    fun μ hμ z T hT0 hz hzT hnc hzδ => ?_⟩
  obtain ⟨hs, hbd⟩ := hamp μ hμ z T hT0 hz hzT hnc hzδ
  have hpos := hs
  rw [hkey] at hpos
  refine ⟨pos_of_mul_pos_right (neg_neg_iff_pos.mp hpos) hk.le, fun t => ?_⟩
  rw [Dynamics.HopfCycle.hopfAmplitude_eq_abs hω hs] at hbd
  exact hbd t

/-- **Hopf cycles along the voltage where the gain is not transversal.** At every Hopf boundary
point (balanced, physical, `a₂ a₁ = a₀`, `a₁, a₀ > 0`) with `𝔅_P ≠ 0` and
`K_p Q = −√(σ² + ω₀²) = −|Z|/L` (`τ_{K_p} = 0`), for every small `μ` with `μ 𝔅_P < 0` the model
with the grid voltage `V + μ` and the set-point `P_ref + μ ∂P/∂V` (`Line.PSC.Model.dirParams 0 1`)
has a nonconstant periodic orbit around its moved operating point `(δ*, i_s(δ*))`, with
`c|μ|/8 ≤ ‖critπ p (z(t) − x*(μ))‖² ≤ 8c|μ|`, `c > 0` (`τ_V < 0`,
`Line.PSC.Model.paramTrace_voltJac_crit_neg_of_gain`; supercritical `𝔅_P > 0`: cycles for a
lowered voltage, on the unstable side). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_volt (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0)
    (hκ : m.g.Kp * m.Q = -Real.sqrt ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      μ * bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift < 0 →
      ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z ((m.dirParams 0 1 μ).field (z t)) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * |μ| / 8 ≤
            ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel 0 1 μ).point)‖ ^ 2 ∧
          ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel 0 1 μ).point)‖ ^ 2 ≤
            8 * (c * |μ|) := by
  have hK := K_pos_of_boundary hp h0
  have hσ : 0 < m.g.R / m.g.L := div_pos (Model.R_pos_of_boundary hp hH) hp.1.L
  have hT : m.transvForm 0 1 < 0 := by
    have hneg : m.g.Kp * m.Q - m.g.R / m.g.L < 0 := by
      rw [hκ]
      linarith [Real.sqrt_nonneg ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)]
    have hKp := hp.2
    have : 0 < 2 * m.g.Kp ^ 2 * m.K := by positivity
    simp only [Model.transvForm, zero_mul, zero_add, mul_one]
    nlinarith
  obtain ⟨δ, hδ, c, hc, hcyc⟩ := m.exists_hopfCycle_dir hp hb hH h1 h0 hB hT.ne
  refine ⟨δ, hδ, c, hc, fun μ hμ hs => hcyc μ hμ ?_⟩
  nlinarith

/-- **Hopf cycles at every non-degenerate Hopf point of `Line.PSC`.** At every Hopf boundary
point (balanced, physical, `a₂ a₁ = a₀`, `a₁, a₀ > 0`) with `𝔅_P ≠ 0`, along the direction
`𝔅_P (T(1, 0), T(0, 1))` of the `(K_p, V)` plane (gain `K_p + aμ`, voltage `V + bμ`, set-point
`P_ref + bμ ∂P/∂V`), for every small `μ > 0` the moved model has a nonconstant periodic orbit
around its operating point with `cμ/8 ≤ ‖critπ p (z(t) − x*(μ))‖² ≤ 8cμ`, `c > 0`: the direction
is transversal at every such point (`Line.PSC.Model.transvForm_normal_pos`) and `μ > 0` is the
side of the cycles (`T 𝔅_P > 0`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_of_bautinForm_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift ≠ 0) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, 0 < μ → μ < δ →
      ∃ z : ℝ → State 3, ∃ T, 0 < T ∧
        (∀ t, HasDerivAt z ((m.dirParams
          (bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift * m.transvForm 1 0)
          (bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift * m.transvForm 0 1)
          μ).field (z t)) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * μ / 8 ≤ ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel
            (bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift * m.transvForm 1 0)
            (bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift * m.transvForm 0 1)
            μ).point)‖ ^ 2 ∧
          ‖critπ (m.critP (Real.sqrt (m.g.coeff1 m.Q))) (z t - (m.dirModel
            (bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift * m.transvForm 1 0)
            (bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift * m.transvForm 0 1)
            μ).point)‖ ^ 2 ≤ 8 * (c * μ) := by
  set 𝔅 := bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift with h𝔅
  have hN := Model.transvForm_normal_pos hp h0
  have hT : m.transvForm (𝔅 * m.transvForm 1 0) (𝔅 * m.transvForm 0 1) =
      𝔅 * m.transvForm (m.transvForm 1 0) (m.transvForm 0 1) := by
    simp only [Model.transvForm]; ring
  have hT0 : m.transvForm (𝔅 * m.transvForm 1 0) (𝔅 * m.transvForm 0 1) ≠ 0 := by
    rw [hT]; exact mul_ne_zero hB hN.ne'
  obtain ⟨δ, hδ, c, hc, hcyc⟩ := m.exists_hopfCycle_dir hp hb hH h1 h0 hB hT0
  refine ⟨δ, hδ, c, hc, fun μ hμ hμδ => ?_⟩
  have hμa : |μ| = μ := abs_of_pos hμ
  have hs : 0 < μ * (m.transvForm (𝔅 * m.transvForm 1 0) (𝔅 * m.transvForm 0 1) * 𝔅) := by
    rw [hT]
    have : 0 < 𝔅 * 𝔅 := mul_self_pos.mpr hB
    have : 0 < μ * ((𝔅 * 𝔅) * m.transvForm (m.transvForm 1 0) (m.transvForm 0 1)) := by
      positivity
    linarith [show μ * (𝔅 * m.transvForm (m.transvForm 1 0) (m.transvForm 0 1) * 𝔅) =
      μ * ((𝔅 * 𝔅) * m.transvForm (m.transvForm 1 0) (m.transvForm 0 1)) by ring]
  obtain ⟨z, T, hT0', hz, hzT, hznc, hamp⟩ := hcyc μ (by rw [hμa]; exact hμδ) hs
  refine ⟨z, T, hT0', hz, hzT, hznc, fun t => ?_⟩
  have h := hamp t
  rw [hμa] at h
  exact h


end PSC
end powerlib.GFM.Line
