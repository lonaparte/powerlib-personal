import theorem.GridTiedConverter.GFM.Line.VSM
import theorem.NormalForm.LyapunovCoefficient

/-! # A subcritical and a supercritical Hopf point of the VSM on a dynamic R–L line (four states)

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* The witness `Line.VSM.hopfWitness`: `E = V = 1`, `R = 1/5`, `L = 1/10`, `ω₀ = 5` (`X = 1/2`),
  `M = 7/4`, `D = 1/4`, `P_ref = 0`, `δ* = 0` (zero current at the operating point), a balanced
  physical model; the second witness `Line.VSM.hopfWitnessSup`: `E = V = 1`, `R = L = 1/5`,
  `ω₀ = 1` (`X = 1/5`), `M = 1`, `D = 2`, `P_ref = 0`, `δ* = 0`, also balanced and physical.
* Level: the second and third derivatives at the state `0`, and the Jacobian, its characteristic
  polynomial and Kuznetsov's first Lyapunov coefficient
  (`NormalForm.LyapunovCoefficient.firstLyapunov`) at the two exhibited parameter points, in exact
  rational arithmetic. No behavioural sentence is concluded here: the instability of every
  boundary point with `ℓ₁ > 0` and the local asymptotic stability of every boundary point with
  `ℓ₁ < 0` (centre-manifold reduction), and their instances at the witnesses, are in
  `theorem/GridTiedConverter/GFM/HopfLineInstability.lean`. The `ε = 1/ω_b` expansion of the
  source note is not formalized.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, "Subcritical EXISTS: VSM without
filter on dynamic RL line") and its scripts `s5b_dynline.py`, `s5f_slow_manifold.py` (discovery
evidence only; the witness was found with exact rational search outside the library; the
supercritical witness was found by a SymPy search of the zero-current boundary, untrusted);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5.

Results.
* `Line.VSM.field_eq_pieces`: for every parameter set the field is an affine field plus the four
  nonlinear terms `(E/L) cos δ e₂`, `(E/L) sin δ e₃`, `−(E/M) cos δ i_d e₁`, `−(E/M) sin δ i_q e₁`
  (`NormalForm.LyapunovCoefficient.ridge`, `prodRidge`), so the second and third derivatives are
  computed by the generic laws: `Line.VSM.bilinC_field_zero`, `Line.VSM.trilinC_field_zero`
  (`B(u, w) = (0, −(E/M)(u₀w₃ + u₃w₀), −(E/L) u₀w₀, 0)`,
  `C(u, w, z) = (0, (E/M)(u₀w₀z₂ + u₀w₂z₀ + u₂w₀z₀), 0, −(E/L) u₀w₀z₀)` at the state `0`);
  `Line.VSM.Model.jacobianC_field` (the complexified Jacobian of the model field is that of
  `Line.VSM.Model.jac`).
* `Line.VSM.hopfWitness_charpoly`: at the witness
  `det(sI − J) = (s² + 1)(s² + 29s/7 + 200/7)`: eigenvalues `±i` and a stable pair, a Hopf point
  at `ω₀ = 1`.
* `Line.VSM.hopfWitness_isCriticalPair`: `q = (1, i, 7/4 − i/4, 3/4 + i/4)` and the explicit
  `p` (`hopfWitnessP`) form a critical pair.
* `Line.VSM.hopfWitness_firstLyapunov`: `ℓ₁ = 1478182/156873665 > 0`
  (`Line.VSM.hopfWitness_firstLyapunov_pos`): a subcritical Hopf point of a physical model,
  whereas every boundary point of the quasi-static (phasor) models is supercritical
  (`VSMLPF.firstLyapunov_neg`, `VSMLPFLossy.firstLyapunov_neg`).
* The supercritical witness: `Line.VSM.hopfWitnessSup_coeffs` (`a₃ = 4`, `a₂ = 6`, `a₁ = 4`,
  `a₀ = 5`, on the Hopf boundary), `Line.VSM.hopfWitnessSup_charpoly`
  (`(s² + 1)(s² + 4s + 5)`), `Line.VSM.hopfWitnessSup_isCriticalPair` (`q = (1, i, 1 − 2i, 3 − i)`),
  `Line.VSM.hopfWitnessSup_firstLyapunov` (`ℓ₁ = −73/416 < 0`,
  `Line.VSM.hopfWitnessSup_firstLyapunov_neg`): both signs occur on the boundary of the full
  model.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Complex Matrix
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

variable (g : VSM)

/-- The affine part of the field. -/
def affinePart : State 4 →L[ℝ] State 4 :=
  Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    !![0, 1, 0, 0; 0, -g.D / g.M, 0, 0; 0, 0, -g.R / g.L, g.X / g.L;
      0, 0, -g.X / g.L, -g.R / g.L]

/-- The constant part of the field. -/
def constPart : State 4 := WithLp.toLp 2 ![0, g.Pref / g.M, -g.V / g.L, 0]

/-- The field as an affine field plus four one-nonlinearity terms. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem field_eq_pieces :
    g.field =
      ridge g.affinePart g.constPart (coord 0) (fun t => g.E / g.L * Real.cos t)
          (EuclideanSpace.single 2 1) +
        ridge 0 0 (coord 0) (fun t => g.E / g.L * Real.sin t) (EuclideanSpace.single 3 1) +
        prodRidge (coord 0) (coord 2) Real.cos ((-g.E / g.M) • EuclideanSpace.single 1 1) +
        prodRidge (coord 0) (coord 3) Real.sin ((-g.E / g.M) • EuclideanSpace.single 1 1) := by
  funext x
  ext i
  fin_cases i <;>
    simp [field, ridge, prodRidge, affinePart, constPart, Dynamics.toEuclideanCLM_apply,
      Fin.sum_univ_four, Network.power_eq, Network.rateD, Network.rateQ] <;>
    ring

/-! ## Derivatives at the zero state -/

@[tmio M, powerlib_domain] private theorem cos_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.cos t)) (c * Real.sin t) t) :=
  ⟨fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).neg.congr_deriv (by ring)⟩

@[tmio M, powerlib_domain] private theorem sin_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.sin t) (c * Real.cos t) t) ∧
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) :=
  ⟨fun t => (Real.hasDerivAt_sin t).const_mul c,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg⟩

@[tmio M, powerlib_domain] private theorem contDiff_pieces (g : VSM) :
    ContDiff ℝ 3 (ridge g.affinePart g.constPart (coord (n := 4) 0)
        (fun t => g.E / g.L * Real.cos t) (EuclideanSpace.single 2 1)) ∧
    ContDiff ℝ 3 (ridge 0 0 (coord (n := 4) 0) (fun t => g.E / g.L * Real.sin t)
        (EuclideanSpace.single 3 1)) ∧
    ContDiff ℝ 3 (prodRidge (coord (n := 4) 0) (coord (n := 4) 2) Real.cos
        ((-g.E / g.M) • EuclideanSpace.single 1 1)) ∧
    ContDiff ℝ 3 (prodRidge (coord (n := 4) 0) (coord (n := 4) 3) Real.sin
        ((-g.E / g.M) • EuclideanSpace.single 1 1)) :=
  ⟨contDiff_ridge _ _ _ _ (by fun_prop), contDiff_ridge _ _ _ _ (by fun_prop),
    contDiff_prodRidge _ _ _ Real.contDiff_cos, contDiff_prodRidge _ _ _ Real.contDiff_sin⟩

/-- The second derivative of the field at the state `0` (angle `0`, zero current):
`B(u, w) = (0, −(E/M)(u₀w₃ + u₃w₀), −(E/L) u₀w₀, 0)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bilinC_field_zero (u w : Fin 4 → ℂ) :
    bilinC g.field 0 u w =
      ![0, -((g.E / g.M : ℝ) : ℂ) * (u 0 * w 3 + u 3 * w 0),
        -((g.E / g.L : ℝ) : ℂ) * (u 0 * w 0), 0] := by
  obtain ⟨c1, c2, c3, c4⟩ := contDiff_pieces g
  have k2 : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  rw [field_eq_pieces, bilinC_add, bilinC_add, bilinC_add,
    bilinC_ridge _ _ _ _ (by fun_prop), bilinC_ridge _ _ _ _ (by fun_prop),
    bilinC_prodRidge _ _ _ Real.contDiff_cos Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    bilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos,
    (iteratedDeriv_of_hasDerivAt (cos_chain _).1 (cos_chain _).2.1 (cos_chain _).2.2 _).2.1,
    (iteratedDeriv_of_hasDerivAt (sin_chain _).1 (sin_chain _).2.1 (sin_chain _).2.2 _).2.1]
  · ext i
    fin_cases i <;> simp [toC] <;> ring
  all_goals first | exact c1.of_le k2 | exact c2.of_le k2 | exact c3.of_le k2 |
    exact c4.of_le k2 | exact (c1.add c2).of_le k2 | exact ((c1.add c2).add c3).of_le k2

/-- The third derivative of the field at the state `0`:
`C(u, w, z) = (0, (E/M)(u₀w₀z₂ + u₀w₂z₀ + u₂w₀z₀), 0, −(E/L) u₀w₀z₀)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem trilinC_field_zero (u w z : Fin 4 → ℂ) :
    trilinC g.field 0 u w z =
      ![0, ((g.E / g.M : ℝ) : ℂ) * (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0), 0,
        -((g.E / g.L : ℝ) : ℂ) * (u 0 * w 0 * z 0)] := by
  obtain ⟨c1, c2, c3, c4⟩ := contDiff_pieces g
  rw [field_eq_pieces, trilinC_add, trilinC_add, trilinC_add,
    trilinC_ridge _ _ _ _ (by fun_prop), trilinC_ridge _ _ _ _ (by fun_prop),
    trilinC_prodRidge _ _ _ Real.contDiff_cos (Real.hasDerivAt_cos)
      (fun t => (Real.hasDerivAt_sin t).neg)
      (fun t => (Real.hasDerivAt_cos t).neg.congr_deriv (neg_neg _)),
    trilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    (iteratedDeriv_of_hasDerivAt (cos_chain _).1 (cos_chain _).2.1 (cos_chain _).2.2 _).2.2,
    (iteratedDeriv_of_hasDerivAt (sin_chain _).1 (sin_chain _).2.1 (sin_chain _).2.2 _).2.2]
  · ext i
    fin_cases i <;> simp [toC] <;> ring
  all_goals first | exact c1 | exact c2 | exact c3 | exact c4 | exact c1.add c2 |
    exact (c1.add c2).add c3

@[tmio M, powerlib_domain] private theorem Model.field_eq_of_point {m : Model}
    (h : m.point = 0) : m.field = m.g.field := by
  funext z
  simp [Model.field, h]

/-- The complexified Jacobian of the model field at the operating point is that of `Model.jac`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.jacobianC_field (m : Model) :
    jacobianC m.field 0 = Linear.complexify m.jac := by
  have h : fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac := by
    rw [show m.field = fun z => m.g.field (z + m.point) from rfl, fderiv_comp_add_right,
      zero_add, m.fderiv_point]
  rw [jacobianC, h, cmat_toEuclideanCLM]
  rfl

/-! ## The subcritical witness -/

/-- The witness `E = V = 1`, `R = 1/5`, `L = 1/10`, `ω₀ = 5`, `M = 7/4`, `D = 1/4`, `P_ref = 0`,
`δ* = 0`. -/
def hopfWitness : Model := ⟨⟨⟨1, 1, 1 / 5, 1 / 10, 5⟩, 7 / 4, 1 / 4, 0⟩, 0⟩

/-- The critical right eigenvector `q = (1, i, 7/4 − i/4, 3/4 + i/4)`. -/
def hopfWitnessQ : Fin 4 → ℂ :=
  ![1, I, ((7 / 4 : ℝ) : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I, ((3 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * I]

/-- The critical left eigenvector, `⟨p, q⟩ = 1`. -/
def hopfWitnessP : Fin 4 → ℂ :=
  ![((1930 / 3809 : ℝ) : ℂ) + ((290 / 3809 : ℝ) : ℂ) * I,
    ((-14 / 3809 : ℝ) : ℂ) + ((1932 / 3809 : ℝ) : ℂ) * I,
    ((-27 / 3809 : ℝ) : ℂ) + ((-83 / 3809 : ℝ) : ℂ) * I,
    ((29 / 3809 : ℝ) : ℂ) + ((-193 / 3809 : ℝ) : ℂ) * I]

@[tmio M, powerlib_domain] theorem hopfWitness_point : hopfWitness.point = 0 := by
  ext i
  fin_cases i <;> simp [Model.point, qss, hopfWitness, Network.is]

/-- The witness is balanced and physical. Satisfaction of the requirements. -/
@[tmio M, powerlib_domain] theorem hopfWitness_meets :
    Meets hopfWitness .balanced ∧ Meets hopfWitness .physical := by
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩ <;>
    norm_num [Meets, hopfWitness, Network.qssPower, Network.is, Network.power_eq]

@[tmio M, powerlib_domain] private theorem hopfWitness_field :
    hopfWitness.field = hopfWitness.g.field :=
  Model.field_eq_of_point hopfWitness_point

/-- The Jacobian at the witness, `[[0, 1, 0, 0], [0, −1/7, −4/7, 0], [0, 0, −2, 5],
[10, 0, −5, −2]]`. -/
@[tmio M, powerlib_domain] theorem hopfWitness_jac :
    hopfWitness.jac = !![0, 1, 0, 0; 0, -1 / 7, -4 / 7, 0; 0, 0, -2, 5; 10, 0, -5, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Model.jac, jacobian, hopfWitness, Network.is, Network.reactive_eq, Network.X]

/-- **A Hopf point**: `det(sI − J) = (s² + 1)(s² + 29 s/7 + 200/7)` at the witness. -/
@[tmio M, powerlib_domain] theorem hopfWitness_charpoly (s : ℂ) :
    (Linear.characteristicMatrix hopfWitness.jac s).det =
      (s ^ 2 + 1) * (s ^ 2 + 29 / 7 * s + 200 / 7) := by
  rw [Model.det_characteristicMatrix]
  have h3 : hopfWitness.g.coeff3 = 29 / 7 := by
    norm_num [coeff3, hopfWitness, Network.σ]
  have hQ : hopfWitness.Q = 0 := by
    norm_num [Model.Q, Network.qssReactive, hopfWitness, Network.is, Network.reactive_eq]
  have h2 : hopfWitness.g.coeff2 hopfWitness.Q = 207 / 7 := by
    rw [hQ]; norm_num [coeff2, hopfWitness, Network.ρ, Network.σ, Network.X]
  have h1 : hopfWitness.g.coeff1 hopfWitness.Q = 29 / 7 := by
    rw [hQ]; norm_num [coeff1, hopfWitness, Network.ρ, Network.σ, Network.X]
  have h0 : hopfWitness.g.coeff0 hopfWitness.Q = 200 / 7 := by
    rw [hQ]; norm_num [coeff0, hopfWitness, Network.ρ, Network.σ, Network.X]
  rw [h3, h2, h1, h0]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem hopfWitness_jacobianC :
    jacobianC hopfWitness.field 0 =
      (!![0, 1, 0, 0; 0, -1 / 7, -4 / 7, 0; 0, 0, -2, 5; 10, 0, -5, -2] :
        Matrix (Fin 4) (Fin 4) ℝ).map (fun x => (x : ℂ)) := by
  rw [Model.jacobianC_field, hopfWitness_jac]
  rfl

/-- The second derivative at the witness: `B(u, w) = (0, −(4/7)(u₀w₃ + u₃w₀), −10 u₀w₀, 0)`. -/
@[tmio M, powerlib_domain] private theorem hopfWitness_bilinC (u w : Fin 4 → ℂ) :
    bilinC hopfWitness.field 0 u w =
      ![0, -(4 / 7) * (u 0 * w 3 + u 3 * w 0), -10 * (u 0 * w 0), 0] := by
  rw [hopfWitness_field, bilinC_field_zero]
  ext i
  fin_cases i <;> norm_num [hopfWitness]

/-- The third derivative at the witness:
`C(u, w, z) = (0, (4/7)(u₀w₀z₂ + u₀w₂z₀ + u₂w₀z₀), 0, −10 u₀w₀z₀)`. -/
@[tmio M, powerlib_domain] private theorem hopfWitness_trilinC (u w z : Fin 4 → ℂ) :
    trilinC hopfWitness.field 0 u w z =
      ![0, 4 / 7 * (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0), 0,
        -10 * (u 0 * w 0 * z 0)] := by
  rw [hopfWitness_field, trilinC_field_zero]
  ext i
  fin_cases i <;> norm_num [hopfWitness]

/-- **The critical pair** of the witness at `ω₀ = 1`. -/
@[tmio M, powerlib_domain] theorem hopfWitness_isCriticalPair :
    IsCriticalPair hopfWitness.field 0 1 hopfWitnessQ hopfWitnessP := by
  refine ⟨?_, one_pos, ?_, ?_, ?_⟩
  · rw [hopfWitness_field]
    ext i
    fin_cases i <;> norm_num [field, hopfWitness, Network.power_eq, Network.rateD,
      Network.rateQ, Network.X]
  · rw [hopfWitness_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · rw [hopfWitness_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessP, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · simp [dotProduct, Fin.sum_univ_four, hopfWitnessP, hopfWitnessQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num

/-- **The first Lyapunov coefficient of the witness**: `ℓ₁ = 1478182/156873665`. -/
@[tmio M, powerlib_domain] theorem hopfWitness_firstLyapunov :
    firstLyapunov hopfWitness.field 0 1 hopfWitnessQ hopfWitnessP = 1478182 / 156873665 := by
  set r : Fin 4 → ℂ := ![((47 / 100 : ℝ) : ℂ), 0, ((3 / 2 : ℝ) : ℂ), ((-7 / 5 : ℝ) : ℂ)]
  set s : Fin 4 → ℂ := ![((861 / 8237 : ℝ) : ℂ) + ((-3 / 8237 : ℝ) : ℂ) * I,
    ((6 / 8237 : ℝ) : ℂ) + ((1722 / 8237 : ℝ) : ℂ) * I,
    ((-6330 / 8237 : ℝ) : ℂ) + ((-4570 / 8237 : ℝ) : ℂ) * I,
    ((15770 / 8237 : ℝ) : ℂ) + ((-4360 / 8237 : ℝ) : ℂ) * I]
  have hA : IsUnit (jacobianC hopfWitness.field 0).det := by
    have h := hopfWitness_charpoly 0
    rw [Linear.characteristicMatrix, zero_smul, zero_sub, Matrix.det_neg,
      ← Model.jacobianC_field hopfWitness] at h
    norm_num at h
    rw [h]
    norm_num
  have h2 : IsUnit (shift2 (jacobianC hopfWitness.field 0) 1).det := by
    have h := hopfWitness_charpoly (2 * I)
    rw [Linear.characteristicMatrix, ← Model.jacobianC_field hopfWitness] at h
    rw [shift2, show ((2 * (1 : ℝ) : ℂ) * I) = 2 * I by push_cast; ring, h]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h1 := congrArg Complex.re h0
    simp [pow_two] at h1
    norm_num at h1
  have hr : jacobianC hopfWitness.field 0 *ᵥ r =
      bilinC hopfWitness.field 0 hopfWitnessQ (star hopfWitnessQ) := by
    rw [hopfWitness_jacobianC, hopfWitness_bilinC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessQ, r,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  have hs : shift2 (jacobianC hopfWitness.field 0) 1 *ᵥ s =
      bilinC hopfWitness.field 0 hopfWitnessQ hopfWitnessQ := by
    rw [hopfWitness_jacobianC, hopfWitness_bilinC, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessQ, s,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  rw [firstLyapunov_eq_of_solve hA h2 hr hs, hopfWitness_trilinC, hopfWitness_bilinC,
    hopfWitness_bilinC]
  simp [pairing_apply, Fin.sum_univ_four, hopfWitnessP, hopfWitnessQ, r, s, Complex.mul_re,
    Complex.mul_im, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
    -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-- **Subcritical**: the witness has `ℓ₁ > 0`. -/
@[tmio M, powerlib_domain] theorem hopfWitness_firstLyapunov_pos :
    0 < firstLyapunov hopfWitness.field 0 1 hopfWitnessQ hopfWitnessP := by
  rw [hopfWitness_firstLyapunov]; norm_num

/-! ## A supercritical witness -/

/-- A second boundary point: `E = V = 1`, `R = L = 1/5`, `ω₀ = 1` (`X = 1/5`), `M = 1`, `D = 2`,
`P_ref = 0`, `δ* = 0`. -/
def hopfWitnessSup : Model := ⟨⟨⟨1, 1, 1 / 5, 1 / 5, 1⟩, 1, 2, 0⟩, 0⟩

/-- The critical right eigenvector `q = (1, i, 1 − 2i, 3 − i)`. -/
def hopfWitnessSupQ : Fin 4 → ℂ :=
  ![1, I, 1 + ((-2 : ℝ) : ℂ) * I, 3 + ((-1 : ℝ) : ℂ) * I]

/-- The critical left eigenvector, `⟨p, q⟩ = 1`. -/
def hopfWitnessSupP : Fin 4 → ℂ :=
  ![((5 / 16 : ℝ) : ℂ) + ((5 / 16 : ℝ) : ℂ) * I, ((1 / 16 : ℝ) : ℂ) + ((3 / 16 : ℝ) : ℂ) * I,
    ((-1 / 8 : ℝ) : ℂ) * I, ((1 / 16 : ℝ) : ℂ) + ((-1 / 16 : ℝ) : ℂ) * I]

@[tmio M, powerlib_domain] theorem hopfWitnessSup_point : hopfWitnessSup.point = 0 := by
  ext i
  fin_cases i <;> simp [Model.point, qss, hopfWitnessSup, Network.is]

/-- The supercritical witness is balanced and physical. Satisfaction of the requirements. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_meets :
    Meets hopfWitnessSup .balanced ∧ Meets hopfWitnessSup .physical := by
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩ <;>
    norm_num [Meets, hopfWitnessSup, Network.qssPower, Network.is, Network.power_eq]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_field :
    hopfWitnessSup.field = hopfWitnessSup.g.field :=
  Model.field_eq_of_point hopfWitnessSup_point

/-- The Jacobian at the supercritical witness, `[[0, 1, 0, 0], [0, −2, −1, 0], [0, 0, −1, 1],
[5, 0, −1, −1]]`. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_jac :
    hopfWitnessSup.jac = !![0, 1, 0, 0; 0, -2, -1, 0; 0, 0, -1, 1; 5, 0, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Model.jac, jacobian, hopfWitnessSup, Network.is, Network.reactive_eq, Network.X]

/-- The coefficients of the quartic at the supercritical witness: `a₃ = 4`, `a₂ = 6`, `a₁ = 4`,
`a₀ = 5`, on the Hopf boundary `a₃ a₂ a₁ = a₁² + a₃² a₀ = 96`. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_coeffs :
    hopfWitnessSup.g.coeff3 = 4 ∧ hopfWitnessSup.g.coeff2 hopfWitnessSup.Q = 6 ∧
      hopfWitnessSup.g.coeff1 hopfWitnessSup.Q = 4 ∧
      hopfWitnessSup.g.coeff0 hopfWitnessSup.Q = 5 := by
  have hQ : hopfWitnessSup.Q = 0 := by
    norm_num [Model.Q, Network.qssReactive, hopfWitnessSup, Network.is, Network.reactive_eq]
  rw [hQ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [coeff3, coeff2, coeff1, coeff0, hopfWitnessSup, Network.ρ, Network.σ, Network.X]

/-- **A Hopf point**: `det(sI − J) = (s² + 1)(s² + 4s + 5)` at the supercritical witness. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_charpoly (s : ℂ) :
    (Linear.characteristicMatrix hopfWitnessSup.jac s).det = (s ^ 2 + 1) * (s ^ 2 + 4 * s + 5) := by
  obtain ⟨h3, h2, h1, h0⟩ := hopfWitnessSup_coeffs
  rw [Model.det_characteristicMatrix, h3, h2, h1, h0]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_jacobianC :
    jacobianC hopfWitnessSup.field 0 =
      (!![0, 1, 0, 0; 0, -2, -1, 0; 0, 0, -1, 1; 5, 0, -1, -1] :
        Matrix (Fin 4) (Fin 4) ℝ).map (fun x => (x : ℂ)) := by
  rw [Model.jacobianC_field, hopfWitnessSup_jac]
  rfl

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_bilinC (u w : Fin 4 → ℂ) :
    bilinC hopfWitnessSup.field 0 u w =
      ![0, -(u 0 * w 3 + u 3 * w 0), -5 * (u 0 * w 0), 0] := by
  rw [hopfWitnessSup_field, bilinC_field_zero]
  ext i
  fin_cases i <;> norm_num [hopfWitnessSup]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_trilinC (u w z : Fin 4 → ℂ) :
    trilinC hopfWitnessSup.field 0 u w z =
      ![0, u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0, 0, -5 * (u 0 * w 0 * z 0)] := by
  rw [hopfWitnessSup_field, trilinC_field_zero]
  ext i
  fin_cases i <;> norm_num [hopfWitnessSup]

/-- **The critical pair** of the supercritical witness at `ω₀ = 1`. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_isCriticalPair :
    IsCriticalPair hopfWitnessSup.field 0 1 hopfWitnessSupQ hopfWitnessSupP := by
  refine ⟨?_, one_pos, ?_, ?_, ?_⟩
  · rw [hopfWitnessSup_field]
    ext i
    fin_cases i <;> norm_num [field, hopfWitnessSup, Network.power_eq, Network.rateD,
      Network.rateQ, Network.X]
  · rw [hopfWitnessSup_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessSupQ,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · rw [hopfWitnessSup_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessSupP,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · simp [dotProduct, Fin.sum_univ_four, hopfWitnessSupP, hopfWitnessSupQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num

/-- **The first Lyapunov coefficient of the supercritical witness**: `ℓ₁ = −73/416`. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_firstLyapunov :
    firstLyapunov hopfWitnessSup.field 0 1 hopfWitnessSupQ hopfWitnessSupP = -73 / 416 := by
  set r : Fin 4 → ℂ := ![((7 / 5 : ℝ) : ℂ), 0, 6, 1]
  set s : Fin 4 → ℂ := ![((9 / 13 : ℝ) : ℂ) + ((6 / 13 : ℝ) : ℂ) * I,
    ((-12 / 13 : ℝ) : ℂ) + ((18 / 13 : ℝ) : ℂ) * I,
    ((-18 / 13 : ℝ) : ℂ) + ((14 / 13 : ℝ) : ℂ) * I,
    ((19 / 13 : ℝ) : ℂ) + ((-22 / 13 : ℝ) : ℂ) * I]
  have hA : IsUnit (jacobianC hopfWitnessSup.field 0).det := by
    have h := hopfWitnessSup_charpoly 0
    rw [Linear.characteristicMatrix, zero_smul, zero_sub, Matrix.det_neg,
      ← Model.jacobianC_field hopfWitnessSup] at h
    norm_num at h
    rw [h]
    norm_num
  have h2 : IsUnit (shift2 (jacobianC hopfWitnessSup.field 0) 1).det := by
    have h := hopfWitnessSup_charpoly (2 * I)
    rw [Linear.characteristicMatrix, ← Model.jacobianC_field hopfWitnessSup] at h
    rw [shift2, show ((2 * (1 : ℝ) : ℂ) * I) = 2 * I by push_cast; ring, h]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h1 := congrArg Complex.re h0
    simp [pow_two] at h1
    norm_num at h1
  have hr : jacobianC hopfWitnessSup.field 0 *ᵥ r =
      bilinC hopfWitnessSup.field 0 hopfWitnessSupQ (star hopfWitnessSupQ) := by
    rw [hopfWitnessSup_jacobianC, hopfWitnessSup_bilinC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessSupQ, r,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  have hs : shift2 (jacobianC hopfWitnessSup.field 0) 1 *ᵥ s =
      bilinC hopfWitnessSup.field 0 hopfWitnessSupQ hopfWitnessSupQ := by
    rw [hopfWitnessSup_jacobianC, hopfWitnessSup_bilinC, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfWitnessSupQ, s,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  rw [firstLyapunov_eq_of_solve hA h2 hr hs, hopfWitnessSup_trilinC, hopfWitnessSup_bilinC,
    hopfWitnessSup_bilinC]
  simp [pairing_apply, Fin.sum_univ_four, hopfWitnessSupP, hopfWitnessSupQ, r, s, Complex.mul_re,
    Complex.mul_im, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
    -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-- **Supercritical**: the second witness has `ℓ₁ < 0`. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_firstLyapunov_neg :
    firstLyapunov hopfWitnessSup.field 0 1 hopfWitnessSupQ hopfWitnessSupP < 0 := by
  rw [hopfWitnessSup_firstLyapunov]; norm_num

end VSM
end powerlib.GFM.Line
