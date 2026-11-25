import theorem.GridTiedConverter.GFM.HopfLineInstability

/-! # The boundary between sub- and supercritical Hopf points of the VSM on a line, every angle

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* Every operating angle: every balanced physical model (`P(δ*) = P_ref`, `E, V, L, ω₀, M, D > 0`,
  `R ≥ 0`, any `δ* ∈ ℝ`) on the Hopf boundary `a₃a₂a₁ = a₁² + a₃²a₀` with `a₁, a₀ > 0`; `a₀ > 0`
  is the stable range of the angle, `K = P'(δ*) > 0` (`Line.VSM.Model.coeff0_eq`). The slice
  `δ* = 0` (`Line.VSM.angleZero E V R L ω₀ M D`, `P_ref = P(0) = E(E − V)R/|Z|²`, line current
  `(E − V)/Z`) and its zero-current instance `V = E`
  (`theorem/GridTiedConverter/GFM/HopfLyapunovSymbolic.lean`) are instances.
* Notation: `a = E/M`, `b = E/L`, `d = D/M`, `σ = R/L`, `κ = Q/M` (`Q = Q(δ*)`), `ν = P_ref/M`,
  `ρ = σ² + ω₀²`, the angle term `t = ω₀ν − σκ = E V sin δ*/(L M)`
  (`Line.VSM.Model.angleShift`). The monic quartic has `a₃ = 2σ + d`, `a₂ = ρ + 2σd − κ`,
  `a₁ = dρ − 2σκ`, `a₀ = abω₀ − κρ` (`Line.VSM.Model.coeff_atoms`). The angle enters only
  through `κ` and `t`, that is through `P(δ*)` and `K = P'(δ*)` (`Q = E²X/|Z|² − K`,
  `Line.Network.syncCoeff_add_qssReactive`; `P'' = c₀ − P`, `P''' = −K`).
* The rotated frame: rotating the current by `−δ*` (`i' = e^{−jδ*} i`, `rotC`) carries the
  Jacobian and the second and third derivatives at the operating point to those of the angle `0`
  with `κ = Q/M` and the second-derivative coefficient `ν = P_ref/M` free (`νω₀ = σκ`, `t = 0`
  exactly at `δ* = 0`); the coordinate invariance
  `NormalForm.LyapunovCoefficient.firstLyapunov_conj` carries `ℓ₁` back.
* Level: exact identities and signs for all parameters and every angle, and Lyapunov
  instability / local asymptotic stability of the operating point (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`). Not stated: the bifurcating cycles (their existence is the generic
  `Dynamics.HopfCycle.exists_hopfCycle`, given `ℓ₁ ≠ 0` and the transversality `τ ≠ 0`,
  instantiated only for `VSMLPF` in `VSMLPFHopfCycle`; for this model the transversality
  computation and the instance are missing, and uniqueness and orbital stability are not
  proved), the degenerate points `𝔅_δ = 0` themselves.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, the VSM without filter on a dynamic
R–L line); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4
(`NormalForm.LyapunovCoefficient.firstLyapunov`); Carr, *Applications of Centre Manifold Theory*
(1981), §2.4. The closed form was derived with SymPy in exact rational arithmetic in the rotated
frame (Gröbner reduction modulo the boundary relations, exact division, factorisation over `ℚ`;
untrusted discovery); every identity is proved here by `linear_combination` with its polynomial
certificate. The family laws are `theorem/GridTiedConverter/GFM/HopfLineInstability.lean`.

Results.
* The slice: `Line.VSM.angleZero`, `angleZero_point`, `angleZero_balanced`, `angleZero_Q`.
* The derivatives at any state (`δ = x₀ 0`): `bilinC_field_eq`
  (`B(u, w) = (0, (E/M)(sin δ (u₀w₂ + u₂w₀) − cos δ (u₀w₃ + u₃w₀)) + (P_e/M) u₀w₀,
  −(E/L) cos δ u₀w₀, −(E/L) sin δ u₀w₀)`) and `trilinC_field_eq`
  (`C(u, w, z) = (0, (E/M)(cos δ Σ₂ + sin δ Σ₃) − (Q_e/M) u₀w₀z₀, (E/L) sin δ u₀w₀z₀,
  −(E/L) cos δ u₀w₀z₀)`, `Σₖ = u₀w₀zₖ + u₀wₖz₀ + uₖw₀z₀`), by the generic laws `bilinC_ridge`,
  `bilinC_prodRidge`, `trilinC_ridge`, `trilinC_prodRidge`; at the operating point
  `Line.VSM.Model.bilinC_field`, `Line.VSM.Model.trilinC_field`, `Line.VSM.Model.jac_eq`.
* `Line.VSM.Model.coeff_atoms`; `Line.VSM.Model.R_pos_of_boundary` (the boundary forces `R > 0`);
  `Line.VSM.Model.freq_relations_of_boundary` (at `ω² = a₁/a₃`: `d(ρ − ω²) = 2σ(κ + ω²)`,
  `abω₀ = κρ + ω²(ρ − ω² + 2σd − κ)`).
* The critical pair at every angle: `rotC`, `rotC_zero`; `Line.VSM.Model.critQ`,
  `Line.VSM.Model.critP` (the vectors `angleZeroQ`, `angleZeroP` of the rotated frame read in the
  grid frame), `Line.VSM.Model.isCriticalPair_crit`; `Line.VSM.Model.angleShift_eq`.
* **`ℓ₁` in closed form at every angle**: `Line.VSM.Model.firstLyapunov_crit`,
  `ℓ₁ = −a² d σ (4ω²a₀𝔅_Q + t(2(d + σ)ω² − t)𝔊) / ((2σ + d)⁴ ω a₀ |r(iω)|² |r(2iω)|²)`,
  `𝔅_Q = bautinFormQ`, `𝔊 = bautinCorr` (degree 11, 75 terms), polynomials in
  `(d, σ, ω₀, κ)`, `r(z) = z² + (2σ + d) z + ρ − ω² + 2σd − κ` the stable factor
  (`angleZeroR1`, `angleZeroR2`).
* **The symbolic boundary between sub- and supercritical at every angle**:
  `Line.VSM.Model.sign_firstLyapunov_crit` (every critical pair:
  `sign ℓ₁ = −sign 𝔅_δ(D/M, R/L, ω₀, Q/M, t)`, `𝔅_δ = bautinFormAngle =
  4a₁²(a₃a₂ − a₁)𝔅_Q + t(2a₃²(d + σ)a₁ − a₃³t)𝔊`, a polynomial in the parameters).
* **The angle term decides the criticality** (section docstring): the witness `angleWitness`
  (`E = 1`, `V = 25/7`, `R = L = ω₀ = M = 1`, `D = 1/4`, `δ* = arctan(4/3)`; `angleWitness_meets`:
  physical, balanced, `Q = −2`, `t = 20/7`) and the slice point `angleZero 1 5 1 1 1 1 (1/4)`
  have the same monic quartic `(s² + 2)(s² + 9s/4 + 5/2)` on the boundary
  (`angleWitness_coeffs`) and opposite criticality (connection conclusions below).
* The slice `δ* = 0` (`t = 0`, `𝔅_δ = 4a₁²(a₃a₂ − a₁)𝔅_Q`) as an instance:
  `angleZero_isCriticalPair`, `angleZero_firstLyapunov`
  (`ℓ₁ = −4 a² d σ ω 𝔅_Q / ((2σ + d)⁴ |r(iω)|² |r(2iω)|²)`), `angleZero_sign_firstLyapunov`
  (`sign ℓ₁ = −sign 𝔅_Q(D/M, R/L, ω₀, Q/M)`).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* `Line.VSM.mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos` (`𝔅_δ > 0`:
  supercritical) and `Line.VSM.mem_den_unstable_of_bautinFormAngle_neg` (`𝔅_δ < 0`:
  subcritical), for every balanced physical model on the Hopf boundary with `a₁, a₀ > 0`, at
  every operating angle.
* Their instances on the slice `δ* = 0`: `Line.VSM.angleZero_mem_den_locallyAsymptoticallyStable`
  (`𝔅_Q > 0`) and `Line.VSM.angleZero_mem_den_unstable` (`𝔅_Q < 0`).
* The same linearization, opposite criticality:
  `Line.VSM.angleWitness_mem_den_locallyAsymptoticallyStable` and
  `Line.VSM.angleWitnessTwin_mem_den_unstable`; the criticality of a Hopf point is not a function
  of the quartic, the angle term `t` decides it.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Complex Matrix
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

/-! ## The slice `δ* = 0` -/

/-- **The models read at `δ* = 0`**: grid voltage `V`, `P_ref = P(0) = E(E − V)R/|Z|²`, line
`R, L`, nominal frequency `ω₀ = w`, inertia `M`, damping `D`. -/
def angleZero (E V R L w M D : ℝ) : Model :=
  ⟨⟨⟨E, V, R, L, w⟩, M, D, E * (E - V) * R / (R ^ 2 + (w * L) ^ 2)⟩, 0⟩

/-- The operating point: `δ* = 0`, `ω = 0`, current `(E − V)/Z`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleZero_point (E V R L w M D : ℝ) :
    (angleZero E V R L w M D).point = WithLp.toLp 2 ![0, 0,
      (E - V) * R / (R ^ 2 + (w * L) ^ 2), -((E - V) * (w * L)) / (R ^ 2 + (w * L) ^ 2)] := by
  ext i
  fin_cases i <;>
    simp [Model.point, qss, angleZero, Network.is_re, Network.is_im, Network.absSq, Network.X] <;>
    ring

/-- `δ* = 0` is balanced. Satisfaction of the requirements. -/
@[tmio M, powerlib_domain] theorem angleZero_balanced {E V R L w M D : ℝ}
    (hZ : R ^ 2 + (w * L) ^ 2 ≠ 0) : Meets (angleZero E V R L w M D) .balanced := by
  show Network.qssPower _ 0 = _
  rw [Network.qssPower_eq _ (by simpa [angleZero, Network.absSq, Network.X] using hZ)]
  simp [angleZero, Network.absSq, Network.X]
  ring

/-- The reactive power at the operating point, `Q = E(E − V)X/|Z|²`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem angleZero_Q {E V R L w M D : ℝ}
    (hZ : R ^ 2 + (w * L) ^ 2 ≠ 0) :
    (angleZero E V R L w M D).Q = E * (E - V) * (w * L) / (R ^ 2 + (w * L) ^ 2) := by
  rw [Model.Q, Network.qssReactive_eq _ (by simpa [angleZero, Network.absSq, Network.X] using hZ)]
  simp [angleZero, Network.absSq, Network.X]
  ring

/-! ## The derivatives at any state -/

@[tmio M, powerlib_domain] private theorem az_cos_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.cos t)) (c * Real.sin t) t) :=
  ⟨fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).neg.congr_deriv (by ring)⟩

@[tmio M, powerlib_domain] private theorem az_sin_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.sin t) (c * Real.cos t) t) ∧
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) :=
  ⟨fun t => (Real.hasDerivAt_sin t).const_mul c,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg⟩

@[tmio M, powerlib_domain] private theorem az_contDiff_pieces (g : VSM) :
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

/-- **The second derivative at any state** `x₀` (angle `δ = x₀ 0`):
`B(u, w) = (0, (E/M)(sin δ (u₀w₂ + u₂w₀) − cos δ (u₀w₃ + u₃w₀)) + (P_e(x₀)/M) u₀w₀,
−(E/L) cos δ u₀w₀, −(E/L) sin δ u₀w₀)`, `P_e` the exported power at `x₀` (generic laws
`bilinC_ridge`, `bilinC_prodRidge`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bilinC_field_eq (g : VSM) (x₀ : State 4) (u w : Fin 4 → ℂ) :
    bilinC g.field x₀ u w =
      ![0, ((g.E / g.M * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 2 + u 2 * w 0) -
          ((g.E / g.M * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 3 + u 3 * w 0) +
          ((g.power (x₀ 0) (x₀ 2) (x₀ 3) / g.M : ℝ) : ℂ) * (u 0 * w 0),
        -((g.E / g.L * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0),
        -((g.E / g.L * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0)] := by
  obtain ⟨c1, c2, c3, c4⟩ := az_contDiff_pieces g
  have k2 : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  rw [field_eq_pieces, bilinC_add, bilinC_add, bilinC_add,
    bilinC_ridge _ _ _ _ (by fun_prop), bilinC_ridge _ _ _ _ (by fun_prop),
    bilinC_prodRidge _ _ _ Real.contDiff_cos Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    bilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos,
    (iteratedDeriv_of_hasDerivAt (az_cos_chain _).1 (az_cos_chain _).2.1
      (az_cos_chain _).2.2 _).2.1,
    (iteratedDeriv_of_hasDerivAt (az_sin_chain _).1 (az_sin_chain _).2.1
      (az_sin_chain _).2.2 _).2.1]
  · ext i
    fin_cases i <;> simp [toC, Network.power_eq] <;> ring
  all_goals first | exact c1.of_le k2 | exact c2.of_le k2 | exact c3.of_le k2 |
    exact c4.of_le k2 | exact (c1.add c2).of_le k2 | exact ((c1.add c2).add c3).of_le k2

/-- **The third derivative at any state** `x₀` (angle `δ = x₀ 0`):
`C(u, w, z) = (0, (E/M)(cos δ Σ₂ + sin δ Σ₃) − (Q_e(x₀)/M) u₀w₀z₀, (E/L) sin δ u₀w₀z₀,
−(E/L) cos δ u₀w₀z₀)`, `Σₖ = u₀w₀zₖ + u₀wₖz₀ + uₖw₀z₀`, `Q_e` the reactive power at `x₀`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem trilinC_field_eq (g : VSM) (x₀ : State 4)
    (u w z : Fin 4 → ℂ) :
    trilinC g.field x₀ u w z =
      ![0, ((g.E / g.M * Real.cos (x₀ 0) : ℝ) : ℂ) *
            (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0) +
          ((g.E / g.M * Real.sin (x₀ 0) : ℝ) : ℂ) *
            (u 0 * w 0 * z 3 + u 0 * w 3 * z 0 + u 3 * w 0 * z 0) -
          ((g.reactive (x₀ 0) (x₀ 2) (x₀ 3) / g.M : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        ((g.E / g.L * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        -((g.E / g.L * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0 * z 0)] := by
  obtain ⟨c1, c2, c3, c4⟩ := az_contDiff_pieces g
  rw [field_eq_pieces, trilinC_add, trilinC_add, trilinC_add,
    trilinC_ridge _ _ _ _ (by fun_prop), trilinC_ridge _ _ _ _ (by fun_prop),
    trilinC_prodRidge _ _ _ Real.contDiff_cos (Real.hasDerivAt_cos)
      (fun t => (Real.hasDerivAt_sin t).neg)
      (fun t => (Real.hasDerivAt_cos t).neg.congr_deriv (neg_neg _)),
    trilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    (iteratedDeriv_of_hasDerivAt (az_cos_chain _).1 (az_cos_chain _).2.1
      (az_cos_chain _).2.2 _).2.2,
    (iteratedDeriv_of_hasDerivAt (az_sin_chain _).1 (az_sin_chain _).2.1
      (az_sin_chain _).2.2 _).2.2]
  · ext i
    fin_cases i <;> simp [toC, Network.reactive_eq] <;> ring
  all_goals first | exact c1 | exact c2 | exact c3 | exact c4 | exact c1.add c2 |
    exact (c1.add c2).add c3

/-! ## The model at its operating point -/

@[tmio M, powerlib_domain] private theorem model_hess (m : Model) :
    hess m.field 0 = hess m.g.field m.point := by
  funext k i j
  show iteratedFDeriv ℝ 2 (fun z => m.g.field (z + m.point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, hess]

@[tmio M, powerlib_domain] private theorem model_third (m : Model) :
    third m.field 0 = third m.g.field m.point := by
  funext k i j l
  show iteratedFDeriv ℝ 3 (fun z => m.g.field (z + m.point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, third]

@[tmio M, powerlib_domain] private theorem model_bilinC (m : Model) :
    bilinC m.field 0 = bilinC m.g.field m.point := by
  unfold bilinC
  rw [model_hess]

@[tmio M, powerlib_domain] private theorem model_trilinC (m : Model) :
    trilinC m.field 0 = trilinC m.g.field m.point := by
  unfold trilinC
  rw [model_third]

@[tmio M, powerlib_domain] private theorem model_point (m : Model) :
    m.point 0 = m.δ ∧ m.point 2 = (m.g.is m.δ).re ∧ m.point 3 = (m.g.is m.δ).im := by
  simp [Model.point, qss]

/-- **The second derivative of the model field at the operating point**, at every angle `δ*`:
`B(u, w) = (0, (E/M)(sin δ* (u₀w₂ + u₂w₀) − cos δ* (u₀w₃ + u₃w₀)) + (P(δ*)/M) u₀w₀,
−(E/L) cos δ* u₀w₀, −(E/L) sin δ* u₀w₀)` (`bilinC_field_eq`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.bilinC_field (m : Model) (u w : Fin 4 → ℂ) :
    bilinC m.field 0 u w =
      ![0, ((m.g.E / m.g.M * Real.sin m.δ : ℝ) : ℂ) * (u 0 * w 2 + u 2 * w 0) -
          ((m.g.E / m.g.M * Real.cos m.δ : ℝ) : ℂ) * (u 0 * w 3 + u 3 * w 0) +
          ((m.g.qssPower m.δ / m.g.M : ℝ) : ℂ) * (u 0 * w 0),
        -((m.g.E / m.g.L * Real.cos m.δ : ℝ) : ℂ) * (u 0 * w 0),
        -((m.g.E / m.g.L * Real.sin m.δ : ℝ) : ℂ) * (u 0 * w 0)] := by
  obtain ⟨p0, p2, p3⟩ := model_point m
  rw [model_bilinC, bilinC_field_eq, p0, p2, p3]
  rfl

/-- **The third derivative of the model field at the operating point**, at every angle `δ*`:
`C(u, w, z) = (0, (E/M)(cos δ* Σ₂ + sin δ* Σ₃) − (Q/M) u₀w₀z₀, (E/L) sin δ* u₀w₀z₀,
−(E/L) cos δ* u₀w₀z₀)` (`trilinC_field_eq`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.trilinC_field (m : Model) (u w z : Fin 4 → ℂ) :
    trilinC m.field 0 u w z =
      ![0, ((m.g.E / m.g.M * Real.cos m.δ : ℝ) : ℂ) *
            (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0) +
          ((m.g.E / m.g.M * Real.sin m.δ : ℝ) : ℂ) *
            (u 0 * w 0 * z 3 + u 0 * w 3 * z 0 + u 3 * w 0 * z 0) -
          ((m.Q / m.g.M : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        ((m.g.E / m.g.L * Real.sin m.δ : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        -((m.g.E / m.g.L * Real.cos m.δ : ℝ) : ℂ) * (u 0 * w 0 * z 0)] := by
  obtain ⟨p0, p2, p3⟩ := model_point m
  rw [model_trilinC, trilinC_field_eq, p0, p2, p3]
  rfl

/-- **The monic coefficients in the atoms** `a = E/M`, `b = E/L`, `d = D/M`, `σ = R/L`,
`κ = Q/M`: `a₃ = 2σ + d`, `a₂ = σ² + ω₀² + 2σd − κ`, `a₁ = d(σ² + ω₀²) − 2σκ`,
`a₀ = abω₀ − κ(σ² + ω₀²)`, at every operating angle. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.coeff_atoms (m : Model) (hL : m.g.L ≠ 0) :
    m.g.coeff3 = 2 * (m.g.R / m.g.L) + m.g.D / m.g.M ∧
      m.g.coeff2 m.Q = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 + 2 * (m.g.R / m.g.L) * (m.g.D / m.g.M) -
        m.Q / m.g.M ∧
      m.g.coeff1 m.Q = m.g.D / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) -
        2 * (m.g.R / m.g.L) * (m.Q / m.g.M) ∧
      m.g.coeff0 m.Q = m.g.E / m.g.M * (m.g.E / m.g.L) * m.g.ω0 -
        m.Q / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [coeff3, coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X]
  all_goals field_simp
  all_goals ring

/-- **The boundary forces a resistive line**: a physical model on the Hopf boundary has `R > 0`,
at every operating angle (the lossless line has a negative third Hurwitz determinant,
`Line.VSM.hurwitzDet_of_lossless`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.R_pos_of_boundary {m : Model} (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) : 0 < m.g.R := by
  obtain ⟨hN, hM, hD⟩ := hp
  rcases hN.R.lt_or_eq with hR | hR
  · exact hR
  · exfalso
    have h := m.g.hurwitzDet_of_lossless hR.symm hM.ne' hN.L.ne' m.Q
    rw [hH, sub_self] at h
    have hX := hN.X_pos
    have hE := hN.E
    have hL := hN.L
    have : 0 < m.g.D ^ 2 * m.g.E ^ 2 * m.g.X / (m.g.L ^ 2 * m.g.M ^ 3) := by positivity
    linarith

/-- **The frequency relations**: at a frequency with `ω² = a₁/a₃` a physical model on the Hopf
boundary satisfies `d(ρ − ω²) = 2σ(κ + ω²)` and `abω₀ = κρ + ω²(ρ − ω² + 2σd − κ)`
(`ρ = σ² + ω₀²`, `κ = Q/M`), at every operating angle. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.freq_relations_of_boundary {m : Model} {ω : ℝ}
    (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    m.g.D / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) =
        2 * (m.g.R / m.g.L) * (m.Q / m.g.M + ω ^ 2) ∧
      m.g.E / m.g.M * (m.g.E / m.g.L) * m.g.ω0 = m.Q / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) +
        ω ^ 2 * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2 + 2 * (m.g.R / m.g.L) * (m.g.D / m.g.M) -
          m.Q / m.g.M) := by
  have hR := Model.R_pos_of_boundary hp hH
  obtain ⟨hN, hM, hD⟩ := hp
  have hL : 0 < m.g.L := hN.L
  obtain ⟨h3, h2, h1, h0⟩ := m.coeff_atoms hL.ne'
  set κ := m.Q / m.g.M with hκ
  have h3p : 0 < 2 * (m.g.R / m.g.L) + m.g.D / m.g.M := by positivity
  rw [h3, h2, h1, h0] at hH
  rw [h3, h1, eq_div_iff h3p.ne'] at hω2
  refine ⟨by linear_combination -hω2, ?_⟩
  have h3n : (2 * (m.g.R / m.g.L) + m.g.D / m.g.M) ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ h3n
  linear_combination -hH + (m.g.D / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) -
    2 * (m.g.R / m.g.L) * κ + (2 * (m.g.R / m.g.L) + m.g.D / m.g.M) * ω ^ 2 -
    (2 * (m.g.R / m.g.L) + m.g.D / m.g.M) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 +
      2 * (m.g.R / m.g.L) * (m.g.D / m.g.M) - κ)) * hω2

/-- **The Jacobian at the operating point** at every angle `δ*` (`X/L = ω₀`, `κ`-entry `Q/M`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.jac_eq (m : Model) (hL : m.g.L ≠ 0) :
    m.jac = !![0, 1, 0, 0;
      m.Q / m.g.M, -m.g.D / m.g.M, -(m.g.E * Real.cos m.δ) / m.g.M,
        -(m.g.E * Real.sin m.δ) / m.g.M;
      -(m.g.E * Real.sin m.δ) / m.g.L, 0, -m.g.R / m.g.L, m.g.ω0;
      m.g.E * Real.cos m.δ / m.g.L, 0, -m.g.ω0, -m.g.R / m.g.L] := by
  have hX : m.g.X / m.g.L = m.g.ω0 := by simp only [Network.X]; field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.jac, jacobian, Model.Q, Network.qssReactive, hX, neg_div]

/-! ## The polynomials of the closed form -/

/-- **The Bautin form of the slice `δ* = 0`** in the model parameters `d = D/M`, `σ = R/L`,
`w = ω₀`, `κ = Q/M` (degree 4 in `κ`; on the slice `ℓ₁` has the sign of `−bautinFormQ`; at every
angle it is the `t`-free part of `bautinFormAngle`). -/
def bautinFormQ (d σ w κ : ℝ) : ℝ :=
  d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) + d ^ (7:ℕ) * w ^ (4:ℕ) + 5 * d ^ (6:ℕ) * σ ^ (5:ℕ) + 12 *
    d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) - d ^ (6:ℕ) * σ ^ (3:ℕ) * κ + 9 * d ^ (6:ℕ) * σ * w ^ (4:ℕ) -
    2 * d ^ (6:ℕ) * σ * w ^ (2:ℕ) * κ + 24 * d ^ (5:ℕ) * σ ^ (6:ℕ) + 40 * d ^ (5:ℕ) * σ ^ (4:ℕ) *
    w ^ (2:ℕ) - (61 / 2) * d ^ (5:ℕ) * σ ^ (4:ℕ) * κ + 36 * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) - 22 *
    d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * κ + (7 / 4) * d ^ (5:ℕ) * σ ^ (2:ℕ) * κ ^ (2:ℕ) + 4 *
    d ^ (5:ℕ) * w ^ (6:ℕ) + (5 / 2) * d ^ (5:ℕ) * w ^ (4:ℕ) * κ + (3 / 4) * d ^ (5:ℕ) * w ^ (2:ℕ) *
    κ ^ (2:ℕ) + 16 * d ^ (4:ℕ) * σ ^ (7:ℕ) + 24 * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) - (275 / 2) *
    d ^ (4:ℕ) * σ ^ (5:ℕ) * κ + 76 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) - 61 * d ^ (4:ℕ) * σ ^ (3:ℕ)
    * w ^ (2:ℕ) * κ + (95 / 2) * d ^ (4:ℕ) * σ ^ (3:ℕ) * κ ^ (2:ℕ) + 20 * d ^ (4:ℕ) * σ * w ^ (6:ℕ)
    + (17 / 2) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * κ + 9 * d ^ (4:ℕ) * σ * w ^ (2:ℕ) * κ ^ (2:ℕ) + (1 / 4)
    * d ^ (4:ℕ) * σ * κ ^ (3:ℕ) - 36 * d ^ (3:ℕ) * σ ^ (8:ℕ) + 37 * d ^ (3:ℕ) * σ ^ (6:ℕ) *
    w ^ (2:ℕ) - (213 / 2) * d ^ (3:ℕ) * σ ^ (6:ℕ) * κ + 215 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) +
    (233 / 2) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * κ + (909 / 4) * d ^ (3:ℕ) * σ ^ (4:ℕ) *
    κ ^ (2:ℕ) + 87 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) + (141 / 2) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
    w ^ (4:ℕ) * κ + (77 / 2) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) - (77 / 4) * d ^ (3:ℕ)
    * σ ^ (2:ℕ) * κ ^ (3:ℕ) + 9 * d ^ (3:ℕ) * w ^ (8:ℕ) + (31 / 2) * d ^ (3:ℕ) * w ^ (6:ℕ) * κ + (21
    / 4) * d ^ (3:ℕ) * w ^ (4:ℕ) * κ ^ (2:ℕ) - (9 / 4) * d ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (3:ℕ) -
    d ^ (3:ℕ) * κ ^ (4:ℕ) - 51 * d ^ (2:ℕ) * σ ^ (9:ℕ) + 98 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) +
    (177 / 2) * d ^ (2:ℕ) * σ ^ (7:ℕ) * κ + 242 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) + (117 / 2) *
    d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * κ + (271 / 2) * d ^ (2:ℕ) * σ ^ (5:ℕ) * κ ^ (2:ℕ) + 66 *
    d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) - (313 / 2) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ - 227 *
    d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) - 144 * d ^ (2:ℕ) * σ ^ (3:ℕ) * κ ^ (3:ℕ) + 5 *
    d ^ (2:ℕ) * σ * w ^ (8:ℕ) - (61 / 2) * d ^ (2:ℕ) * σ * w ^ (6:ℕ) * κ - (129 / 2) * d ^ (2:ℕ) * σ
    * w ^ (4:ℕ) * κ ^ (2:ℕ) - 31 * d ^ (2:ℕ) * σ * w ^ (2:ℕ) * κ ^ (3:ℕ) - 2 * d ^ (2:ℕ) * σ *
    κ ^ (4:ℕ) - 20 * d * σ ^ (10:ℕ) + 64 * d * σ ^ (8:ℕ) * w ^ (2:ℕ) + 111 * d * σ ^ (8:ℕ) * κ + 96
    * d * σ ^ (6:ℕ) * w ^ (4:ℕ) - 171 * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * κ - 112 * d * σ ^ (6:ℕ) *
    κ ^ (2:ℕ) + 16 * d * σ ^ (4:ℕ) * w ^ (6:ℕ) - 155 * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * κ - 80 * d *
    σ ^ (4:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) - 44 * d * σ ^ (4:ℕ) * κ ^ (3:ℕ) + 4 * d * σ ^ (2:ℕ) *
    w ^ (8:ℕ) - d * σ ^ (2:ℕ) * w ^ (6:ℕ) * κ + 48 * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * κ ^ (2:ℕ) + 88 * d
    * σ ^ (2:ℕ) * w ^ (2:ℕ) * κ ^ (3:ℕ) + 35 * d * σ ^ (2:ℕ) * κ ^ (4:ℕ) - 2 * σ ^ (11:ℕ) + 8 *
    σ ^ (9:ℕ) * w ^ (2:ℕ) + 24 * σ ^ (9:ℕ) * κ + 12 * σ ^ (7:ℕ) * w ^ (4:ℕ) - 84 * σ ^ (7:ℕ) *
    w ^ (2:ℕ) * κ - 72 * σ ^ (7:ℕ) * κ ^ (2:ℕ) - 8 * σ ^ (5:ℕ) * w ^ (6:ℕ) - 16 * σ ^ (5:ℕ) *
    w ^ (4:ℕ) * κ + 96 * σ ^ (5:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) + 50 * σ ^ (5:ℕ) * κ ^ (3:ℕ) - 10 *
    σ ^ (3:ℕ) * w ^ (8:ℕ) - 36 * σ ^ (3:ℕ) * w ^ (6:ℕ) * κ - 24 * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ ^ (2:ℕ)
    + 2 * σ ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (3:ℕ)

/-- **The correction form of the operating angle** in `d = D/M`, `σ = R/L`, `w = ω₀`,
`κ = Q/M` (degree 11, 75 terms, degree 4 in `κ`). -/
def bautinCorr (d σ w κ : ℝ) : ℝ :=
  10 * d ^ (6:ℕ) * σ ^ (5:ℕ) + 16 * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) + 6 * d ^ (6:ℕ) * σ *
    w ^ (4:ℕ) + 28 * d ^ (5:ℕ) * σ ^ (6:ℕ) + 32 * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) - 31 * d ^ (5:ℕ)
    * σ ^ (4:ℕ) * κ - 4 * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) - 38 * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ)
    * κ - 8 * d ^ (5:ℕ) * w ^ (6:ℕ) - 7 * d ^ (5:ℕ) * w ^ (4:ℕ) * κ + 80 * d ^ (4:ℕ) * σ ^ (7:ℕ) +
    168 * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) + 6 * d ^ (4:ℕ) * σ ^ (5:ℕ) * κ + 96 * d ^ (4:ℕ) *
    σ ^ (3:ℕ) * w ^ (4:ℕ) + 4 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * κ + 35 * d ^ (4:ℕ) * σ ^ (3:ℕ) *
    κ ^ (2:ℕ) + 8 * d ^ (4:ℕ) * σ * w ^ (6:ℕ) + 30 * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * κ + 27 * d ^ (4:ℕ)
    * σ * w ^ (2:ℕ) * κ ^ (2:ℕ) + 212 * d ^ (3:ℕ) * σ ^ (8:ℕ) + 428 * d ^ (3:ℕ) * σ ^ (6:ℕ) *
    w ^ (2:ℕ) - 21 * d ^ (3:ℕ) * σ ^ (6:ℕ) * κ + 124 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) - 415 *
    d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * κ - 141 * d ^ (3:ℕ) * σ ^ (4:ℕ) * κ ^ (2:ℕ) - 124 *
    d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) - 255 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * κ - 86 * d ^ (3:ℕ)
    * σ ^ (2:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) - 20 * d ^ (3:ℕ) * σ ^ (2:ℕ) * κ ^ (3:ℕ) - 32 * d ^ (3:ℕ) *
    w ^ (8:ℕ) - 53 * d ^ (3:ℕ) * w ^ (6:ℕ) * κ - 25 * d ^ (3:ℕ) * w ^ (4:ℕ) * κ ^ (2:ℕ) - 4 *
    d ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (3:ℕ) + 230 * d ^ (2:ℕ) * σ ^ (9:ℕ) + 284 * d ^ (2:ℕ) * σ ^ (7:ℕ) *
    w ^ (2:ℕ) - 434 * d ^ (2:ℕ) * σ ^ (7:ℕ) * κ - 208 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) - 1094 *
    d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * κ - 162 * d ^ (2:ℕ) * σ ^ (5:ℕ) * κ ^ (2:ℕ) - 284 *
    d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) - 182 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ + 424 *
    d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) + 132 * d ^ (2:ℕ) * σ ^ (3:ℕ) * κ ^ (3:ℕ) - 22 *
    d ^ (2:ℕ) * σ * w ^ (8:ℕ) + 94 * d ^ (2:ℕ) * σ * w ^ (6:ℕ) * κ + 170 * d ^ (2:ℕ) * σ * w ^ (4:ℕ)
    * κ ^ (2:ℕ) + 60 * d ^ (2:ℕ) * σ * w ^ (2:ℕ) * κ ^ (3:ℕ) + 6 * d ^ (2:ℕ) * σ * κ ^ (4:ℕ) + 88 *
    d * σ ^ (10:ℕ) + 48 * d * σ ^ (8:ℕ) * w ^ (2:ℕ) - 448 * d * σ ^ (8:ℕ) * κ - 128 * d * σ ^ (6:ℕ)
    * w ^ (4:ℕ) - 320 * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * κ + 424 * d * σ ^ (6:ℕ) * κ ^ (2:ℕ) - 48 * d *
    σ ^ (4:ℕ) * w ^ (6:ℕ) + 576 * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * κ + 928 * d * σ ^ (4:ℕ) * w ^ (2:ℕ) *
    κ ^ (2:ℕ) + 84 * d * σ ^ (4:ℕ) * κ ^ (3:ℕ) + 40 * d * σ ^ (2:ℕ) * w ^ (8:ℕ) + 192 * d *
    σ ^ (2:ℕ) * w ^ (6:ℕ) * κ + 56 * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * κ ^ (2:ℕ) - 124 * d * σ ^ (2:ℕ) *
    w ^ (2:ℕ) * κ ^ (3:ℕ) - 28 * d * σ ^ (2:ℕ) * κ ^ (4:ℕ) + 8 * σ ^ (11:ℕ) + 16 * σ ^ (9:ℕ) *
    w ^ (2:ℕ) - 96 * σ ^ (9:ℕ) * κ + 96 * σ ^ (7:ℕ) * w ^ (2:ℕ) * κ + 288 * σ ^ (7:ℕ) * κ ^ (2:ℕ) -
    16 * σ ^ (5:ℕ) * w ^ (6:ℕ) + 96 * σ ^ (5:ℕ) * w ^ (4:ℕ) * κ - 200 * σ ^ (5:ℕ) * κ ^ (3:ℕ) - 8 *
    σ ^ (3:ℕ) * w ^ (8:ℕ) - 96 * σ ^ (3:ℕ) * w ^ (6:ℕ) * κ - 288 * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ ^ (2:ℕ)
    - 200 * σ ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (3:ℕ)

/-- **The Bautin form at every operating angle** (`d = D/M`, `σ = R/L`, `w = ω₀`, `κ = Q/M`,
`t = (ω₀ P_ref − σ Q)/M = E V sin δ*/(L M)`):
`𝔅_δ = 4 a₁² (a₃a₂ − a₁) 𝔅_Q + t (2 a₃² (d + σ) a₁ − a₃³ t) 𝔊` in the monic coefficients
`a₃ = 2σ + d`, `a₂ = σ² + w² + 2σd − κ`, `a₁ = d(σ² + w²) − 2σκ` of the angle (`ℓ₁` has the sign
of `−𝔅_δ`). -/
def bautinFormAngle (d σ w κ t : ℝ) : ℝ :=
  4 * (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ) ^ 2 *
      (2 * σ * (σ ^ 2 + w ^ 2) + 4 * d * σ ^ 2 + 2 * d ^ 2 * σ - d * κ) * bautinFormQ d σ w κ +
    t * (2 * (d + 2 * σ) ^ 2 * (d + σ) * (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ) - (d + 2 * σ) ^ 3 * t) *
      bautinCorr d σ w κ

/-- On the boundary `𝔅_δ = a₃³ (4ω²a₀𝔅_Q + t(2(d + σ)ω² − t)𝔊)`. -/
@[tmio M, powerlib_domain] private theorem bautinFormAngle_eq {d σ w κ t ω a₀ : ℝ}
    (h1 : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * (κ + ω ^ 2))
    (h2 : a₀ = ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d - κ)) :
    bautinFormAngle d σ w κ t = (2 * σ + d) ^ 3 * (4 * ω ^ 2 * a₀ * bautinFormQ d σ w κ +
      t * (2 * (d + σ) * ω ^ 2 - t) * bautinCorr d σ w κ) := by
  unfold bautinFormAngle
  rw [h2]
  linear_combination (2 * (4 * d ^ (3:ℕ) * σ ^ (3:ℕ) + 4 * d ^ (3:ℕ) * σ * w ^ (2:ℕ) + 4 * d ^ (3:ℕ)
      * σ * ω ^ (2:ℕ) + 8 * d ^ (2:ℕ) * σ ^ (4:ℕ) + 8 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) + 16 *
      d ^ (2:ℕ) * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 10 * d ^ (2:ℕ) * σ ^ (2:ℕ) * κ - 2 * d ^ (2:ℕ) * w ^ (2:ℕ)
      * κ - 2 * d ^ (2:ℕ) * ω ^ (4:ℕ) - 2 * d ^ (2:ℕ) * ω ^ (2:ℕ) * κ + 4 * d * σ ^ (5:ℕ) + 8 * d *
      σ ^ (3:ℕ) * w ^ (2:ℕ) + 20 * d * σ ^ (3:ℕ) * ω ^ (2:ℕ) - 16 * d * σ ^ (3:ℕ) * κ + 4 * d * σ *
      w ^ (4:ℕ) + 4 * d * σ * w ^ (2:ℕ) * ω ^ (2:ℕ) - 8 * d * σ * ω ^ (4:ℕ) - 4 * d * σ * ω ^ (2:ℕ)
      * κ + 4 * d * σ * κ ^ (2:ℕ) + 8 * σ ^ (4:ℕ) * ω ^ (2:ℕ) - 8 * σ ^ (4:ℕ) * κ + 8 * σ ^ (2:ℕ) *
      w ^ (2:ℕ) * ω ^ (2:ℕ) - 8 * σ ^ (2:ℕ) * w ^ (2:ℕ) * κ - 8 * σ ^ (2:ℕ) * ω ^ (4:ℕ)) *
      bautinFormQ d σ w κ + 2 * (d + σ) * (d + 2 * σ) ^ 2 * t * bautinCorr d σ w κ) * h1

/-- `|r(iω)|²` for the stable factor `r(z) = z² + (2σ + d) z + σ² + ω₀² − ω² + 2σd − κ`. -/
def angleZeroR1 (d σ w κ ω : ℝ) : ℝ :=
  (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ) ^ 2 + ω ^ 2 * (2 * σ + d) ^ 2

/-- `|r(2iω)|²` for the stable factor `r(z) = z² + (2σ + d) z + σ² + ω₀² − ω² + 2σd − κ`. -/
def angleZeroR2 (d σ w κ ω : ℝ) : ℝ :=
  (σ ^ 2 + w ^ 2 - 5 * ω ^ 2 + 2 * σ * d - κ) ^ 2 + 4 * ω ^ 2 * (2 * σ + d) ^ 2

/-! ## Exact algebra of the critical data

The Jacobian pattern of the rotated frame, the critical eigenvectors and the resolvent solutions
as polynomial vectors in complex atoms `A = a`, `B = b`, `D = d`, `S = σ`, `W = ω₀`, `O = ω`,
`K = κ`, `N = ν` (free) and a square root `j` of `−1`, under the relations
`h1 : D(S² + W² − O²) = 2S(K + O²)`, `h2 : ABW = K(S² + W²) + O²(S² + W² − O² + 2SD − K)`;
every identity is checked by `linear_combination` with its polynomial certificate (exponents
typed `ℕ` for elaboration). -/

/-- The Jacobian pattern of the rotated frame (`K = Q/M`). -/
private def zkJ (A B D K S W : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; K, -D, -A, 0; 0, 0, -S, W; B, 0, -W, -S]

/-- The second-derivative pattern (`N = E i'_d/M = P_ref/M`). -/
private def zkBil (A B N : ℂ) (u v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![0, -A * (u 0 * v 3 + u 3 * v 0) + N * (u 0 * v 0), -B * (u 0 * v 0), 0]

/-- The third-derivative pattern (`E i'_q/M = −K`). -/
private def zkTri (A B K : ℂ) (u v z : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![0, A * (u 0 * v 0 * z 2 + u 0 * v 2 * z 0 + u 2 * v 0 * z 0) - K * (u 0 * v 0 * z 0), 0,
    -B * (u 0 * v 0 * z 0)]

/-- The right eigenvector. -/
private def zkQC (A D K S W O j : ℂ) : Fin 4 → ℂ :=
  ![A * W, j * O * A * W, W * (K + O ^ 2 - j * O * D), (S + j * O) * (K + O ^ 2 - j * O * D)]

/-- The unnormalised left eigenvector. -/
private def zkLC (A D S W O j : ℂ) : Fin 4 → ℂ :=
  ![(D - j * O) * -((S - j * O) ^ 2 + W ^ 2), -((S - j * O) ^ 2 + W ^ 2), A * (S - j * O), A * W]

/-- The pairing `⟨p̃, q⟩`. -/
private def zkCC (A D K S W O j : ℂ) : ℂ :=
  2 * A * O * W * (O * (2 * S + D) - j * (S ^ 2 + W ^ 2 - 2 * O ^ 2 + 2 * S * D - K))

/-- `det(2iω − J)`. -/
private def zkDC (D K S W O j : ℂ) : ℂ :=
  -3 * O ^ 2 * (S ^ 2 + W ^ 2 - 5 * O ^ 2 + 2 * S * D - K + 2 * O * (2 * S + D) * j)

/-- `det J` times the solution of `J r = B(q, q̄)`. -/
private def zkRC (A D K N S W O : ℂ) : Fin 4 → ℂ :=
  ![2 * A ^ (2:ℕ) * D * W ^ (3:ℕ) * O ^ (2:ℕ) + A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) + A ^ (2:ℕ) *
    S ^ (3:ℕ) * W * K - A ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * N + A ^ (2:ℕ) * S * W ^ (3:ℕ) *
    O ^ (2:ℕ) + A ^ (2:ℕ) * S * W ^ (3:ℕ) * K + A ^ (2:ℕ) * S * W * O ^ (4:ℕ) + A ^ (2:ℕ) * S * W *
    O ^ (2:ℕ) * K - A ^ (2:ℕ) * W ^ (4:ℕ) * N, 0, 4 * A * D ^ (2:ℕ) * S * W * O ^ (4:ℕ) - 2 * A * D
    * S * W ^ (2:ℕ) * O ^ (2:ℕ) * N - 4 * A * D * W ^ (3:ℕ) * O ^ (4:ℕ) - 2 * A * D * W ^ (3:ℕ) *
    O ^ (2:ℕ) * K + 4 * A * D * W * O ^ (6:ℕ) + 2 * A * D * W * O ^ (4:ℕ) * K + 2 * A * S ^ (3:ℕ) *
    W * O ^ (4:ℕ) + 3 * A * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K + A * S ^ (3:ℕ) * W * K ^ (2:ℕ) - A *
    S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N - A * S ^ (2:ℕ) * W ^ (2:ℕ) * K * N + 2 * A * S *
    W ^ (3:ℕ) * O ^ (4:ℕ) + 3 * A * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K + A * S * W ^ (3:ℕ) * K ^ (2:ℕ) +
    10 * A * S * W * O ^ (6:ℕ) + 17 * A * S * W * O ^ (4:ℕ) * K + 7 * A * S * W * O ^ (2:ℕ) *
    K ^ (2:ℕ) - A * W ^ (4:ℕ) * O ^ (2:ℕ) * N - A * W ^ (4:ℕ) * K * N + A * W ^ (2:ℕ) * O ^ (4:ℕ) *
    N + A * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N, -4 * A * D * S * W ^ (2:ℕ) * O ^ (4:ℕ) - 2 * A * D * S *
    W ^ (2:ℕ) * O ^ (2:ℕ) * K + 4 * A * D * S * O ^ (6:ℕ) + 4 * A * D * S * O ^ (4:ℕ) * K + 2 * A *
    D * W ^ (3:ℕ) * O ^ (2:ℕ) * N - 2 * A * D * W * O ^ (4:ℕ) * N + A * S ^ (4:ℕ) * O ^ (4:ℕ) + 2 *
    A * S ^ (4:ℕ) * O ^ (2:ℕ) * K + A * S ^ (4:ℕ) * K ^ (2:ℕ) - A * S ^ (3:ℕ) * W * O ^ (2:ℕ) * N -
    A * S ^ (3:ℕ) * W * K * N + A * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K + A * S ^ (2:ℕ) *
    W ^ (2:ℕ) * K ^ (2:ℕ) + 4 * A * S ^ (2:ℕ) * O ^ (6:ℕ) + 8 * A * S ^ (2:ℕ) * O ^ (4:ℕ) * K + 4 *
    A * S ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - A * S * W ^ (3:ℕ) * O ^ (2:ℕ) * N - A * S * W ^ (3:ℕ) *
    K * N - 3 * A * S * W * O ^ (4:ℕ) * N - 3 * A * S * W * O ^ (2:ℕ) * K * N - A * W ^ (4:ℕ) *
    O ^ (4:ℕ) - A * W ^ (4:ℕ) * O ^ (2:ℕ) * K + 2 * A * W ^ (2:ℕ) * O ^ (6:ℕ) + 3 * A * W ^ (2:ℕ) *
    O ^ (4:ℕ) * K + A * W ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - A * O ^ (8:ℕ) - 2 * A * O ^ (6:ℕ) * K -
    A * O ^ (4:ℕ) * K ^ (2:ℕ)]

/-- `zkDC` times the solution of `(2iω − J) s = B(q, q)`. -/
private def zkSC (A D K N S W O j : ℂ) : Fin 4 → ℂ :=
  ![-10 * A ^ (2:ℕ) * D * S * W * O ^ (3:ℕ) * j + 6 * A ^ (2:ℕ) * D * W ^ (3:ℕ) * O ^ (2:ℕ) -
    A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) - A ^ (2:ℕ) * S ^ (3:ℕ) * W * K + A ^ (2:ℕ) * S ^ (2:ℕ) *
    W ^ (2:ℕ) * N - 4 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j - 4 * A ^ (2:ℕ) * S ^ (2:ℕ) * W *
    O * K * j - A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (2:ℕ) * S * W ^ (3:ℕ) * K + 4 *
    A ^ (2:ℕ) * S * W ^ (2:ℕ) * O * N * j - A ^ (2:ℕ) * S * W * O ^ (4:ℕ) - A ^ (2:ℕ) * S * W *
    O ^ (2:ℕ) * K + A ^ (2:ℕ) * W ^ (4:ℕ) * N - 4 * A ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N + 6 *
    A ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 6 * A ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j, 20 * A ^ (2:ℕ) * D * S *
    W * O ^ (4:ℕ) + 12 * A ^ (2:ℕ) * D * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 2 * A ^ (2:ℕ) * S ^ (3:ℕ) * W *
    O ^ (3:ℕ) * j - 2 * A ^ (2:ℕ) * S ^ (3:ℕ) * W * O * K * j + 2 * A ^ (2:ℕ) * S ^ (2:ℕ) *
    W ^ (2:ℕ) * O * N * j + 8 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) + 8 * A ^ (2:ℕ) * S ^ (2:ℕ) *
    W * O ^ (2:ℕ) * K - 2 * A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 2 * A ^ (2:ℕ) * S *
    W ^ (3:ℕ) * O * K * j - 8 * A ^ (2:ℕ) * S * W ^ (2:ℕ) * O ^ (2:ℕ) * N - 2 * A ^ (2:ℕ) * S * W *
    O ^ (5:ℕ) * j - 2 * A ^ (2:ℕ) * S * W * O ^ (3:ℕ) * K * j + 2 * A ^ (2:ℕ) * W ^ (4:ℕ) * O * N *
    j - 8 * A ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * N * j - 12 * A ^ (2:ℕ) * W * O ^ (6:ℕ) - 12 *
    A ^ (2:ℕ) * W * O ^ (4:ℕ) * K, 4 * A * D ^ (2:ℕ) * S * W * O ^ (4:ℕ) + 2 * A * D * S * W ^ (2:ℕ)
    * O ^ (2:ℕ) * N + 12 * A * D * S * W * O ^ (5:ℕ) * j - 4 * A * D * W ^ (3:ℕ) * O ^ (4:ℕ) + 2 * A
    * D * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 4 * A * D * W * O ^ (6:ℕ) - 2 * A * D * W * O ^ (4:ℕ) * K + 2
    * A * S ^ (3:ℕ) * W * O ^ (4:ℕ) + A * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K - A * S ^ (3:ℕ) * W *
    K ^ (2:ℕ) + A * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N + A * S ^ (2:ℕ) * W ^ (2:ℕ) * K * N + 6 *
    A * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 6 * A * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j + 2 * A * S *
    W ^ (3:ℕ) * O ^ (4:ℕ) + A * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K - A * S * W ^ (3:ℕ) * K ^ (2:ℕ) + 10 *
    A * S * W * O ^ (6:ℕ) + 11 * A * S * W * O ^ (4:ℕ) * K + A * S * W * O ^ (2:ℕ) * K ^ (2:ℕ) + A *
    W ^ (4:ℕ) * O ^ (2:ℕ) * N + A * W ^ (4:ℕ) * K * N + 6 * A * W ^ (3:ℕ) * O ^ (5:ℕ) * j + 6 * A *
    W ^ (3:ℕ) * O ^ (3:ℕ) * K * j - A * W ^ (2:ℕ) * O ^ (4:ℕ) * N - A * W ^ (2:ℕ) * O ^ (2:ℕ) * K *
    N - 6 * A * W * O ^ (7:ℕ) * j - 6 * A * W * O ^ (5:ℕ) * K * j, -4 * A * D ^ (2:ℕ) * S *
    O ^ (5:ℕ) * j + 8 * A * D ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) - 8 * A * D ^ (2:ℕ) * O ^ (6:ℕ) - 4 *
    A * D * S * W ^ (2:ℕ) * O ^ (4:ℕ) + 2 * A * D * S * W ^ (2:ℕ) * O ^ (2:ℕ) * K + 4 * A * D * S *
    W * O ^ (3:ℕ) * N * j - 12 * A * D * S * O ^ (6:ℕ) - 12 * A * D * S * O ^ (4:ℕ) * K - 2 * A * D
    * W ^ (3:ℕ) * O ^ (2:ℕ) * N + 4 * A * D * W ^ (2:ℕ) * O ^ (5:ℕ) * j + 4 * A * D * W ^ (2:ℕ) *
    O ^ (3:ℕ) * K * j + 2 * A * D * W * O ^ (4:ℕ) * N - 4 * A * D * O ^ (7:ℕ) * j - 4 * A * D *
    O ^ (5:ℕ) * K * j - A * S ^ (4:ℕ) * O ^ (4:ℕ) - 2 * A * S ^ (4:ℕ) * O ^ (2:ℕ) * K - A *
    S ^ (4:ℕ) * K ^ (2:ℕ) + A * S ^ (3:ℕ) * W * O ^ (2:ℕ) * N + A * S ^ (3:ℕ) * W * K * N - 2 * A *
    S ^ (3:ℕ) * O ^ (5:ℕ) * j - 4 * A * S ^ (3:ℕ) * O ^ (3:ℕ) * K * j - 2 * A * S ^ (3:ℕ) * O *
    K ^ (2:ℕ) * j - 4 * A * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) - 5 * A * S ^ (2:ℕ) * W ^ (2:ℕ) *
    O ^ (2:ℕ) * K - A * S ^ (2:ℕ) * W ^ (2:ℕ) * K ^ (2:ℕ) + 2 * A * S ^ (2:ℕ) * W * O ^ (3:ℕ) * N *
    j + 2 * A * S ^ (2:ℕ) * W * O * K * N * j - 8 * A * S ^ (2:ℕ) * O ^ (6:ℕ) - 16 * A * S ^ (2:ℕ) *
    O ^ (4:ℕ) * K - 8 * A * S ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + A * S * W ^ (3:ℕ) * O ^ (2:ℕ) * N +
    A * S * W ^ (3:ℕ) * K * N - 2 * A * S * W ^ (2:ℕ) * O ^ (5:ℕ) * j - 4 * A * S * W ^ (2:ℕ) *
    O ^ (3:ℕ) * K * j - 2 * A * S * W ^ (2:ℕ) * O * K ^ (2:ℕ) * j + 3 * A * S * W * O ^ (4:ℕ) * N +
    3 * A * S * W * O ^ (2:ℕ) * K * N - 10 * A * S * O ^ (7:ℕ) * j - 20 * A * S * O ^ (5:ℕ) * K * j
    - 10 * A * S * O ^ (3:ℕ) * K ^ (2:ℕ) * j - 3 * A * W ^ (4:ℕ) * O ^ (4:ℕ) - 3 * A * W ^ (4:ℕ) *
    O ^ (2:ℕ) * K + 2 * A * W ^ (3:ℕ) * O ^ (3:ℕ) * N * j + 2 * A * W ^ (3:ℕ) * O * K * N * j + 6 *
    A * W ^ (2:ℕ) * O ^ (6:ℕ) + 9 * A * W ^ (2:ℕ) * O ^ (4:ℕ) * K + 3 * A * W ^ (2:ℕ) * O ^ (2:ℕ) *
    K ^ (2:ℕ) - 2 * A * W * O ^ (5:ℕ) * N * j - 2 * A * W * O ^ (3:ℕ) * K * N * j - 3 * A *
    O ^ (8:ℕ) - 6 * A * O ^ (6:ℕ) * K - 3 * A * O ^ (4:ℕ) * K ^ (2:ℕ)]

@[tmio M, powerlib_domain] private theorem zk_r {A B D S W O K N j : ℂ}
    (hj : j ^ 2 = -1) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    zkJ A B D K S W *ᵥ zkRC A D K N S W O =
      (A * B * W - K * (S ^ 2 + W ^ 2)) •
        zkBil A B N (zkQC A D K S W O j) (zkQC A D K S W (-O) j) := by
  ext k
  fin_cases k <;> simp only [zkJ, zkRC, zkBil, zkQC, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply,
      smul_eq_mul]
  · ring
  · linear_combination (-2 * A ^ (2:ℕ) * D * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 2 * A ^ (2:ℕ) * S * W *
      O ^ (2:ℕ) + 2 * A ^ (2:ℕ) * S * W * K - A ^ (2:ℕ) * W ^ (2:ℕ) * N) * h2 + (-2 * A ^ (2:ℕ) * W
      * O ^ (4:ℕ) * j ^ (2:ℕ) + 4 * A ^ (2:ℕ) * W * O ^ (4:ℕ) + 4 * A ^ (2:ℕ) * W * O ^ (2:ℕ) * K) *
      h1 + (-4 * A ^ (2:ℕ) * D ^ (2:ℕ) * S * W * O ^ (4:ℕ) + 2 * A ^ (2:ℕ) * D * W * O ^ (4:ℕ) * K -
      4 * A ^ (2:ℕ) * S * W * O ^ (6:ℕ) - 4 * A ^ (2:ℕ) * S * W * O ^ (4:ℕ) * K) * hj
  · linear_combination (A ^ (2:ℕ) * B * W ^ (2:ℕ) + 2 * A * D * S * W * O ^ (2:ℕ) + A * S ^ (2:ℕ) *
      W * O ^ (2:ℕ) + A * W ^ (3:ℕ) * O ^ (2:ℕ) - A * W * O ^ (4:ℕ) - A * W * O ^ (2:ℕ) * K) * h2 +
      (4 * A * S * W * O ^ (4:ℕ) + 2 * A * S * W * O ^ (2:ℕ) * K + 2 * A * W ^ (2:ℕ) * O ^ (2:ℕ) *
      N) * h1
  · linear_combination (2 * A * D * W ^ (2:ℕ) * O ^ (2:ℕ) + A * S ^ (3:ℕ) * O ^ (2:ℕ) + A *
      S ^ (3:ℕ) * K - A * S ^ (2:ℕ) * W * N + A * S * W ^ (2:ℕ) * O ^ (2:ℕ) + A * S * W ^ (2:ℕ) * K
      + A * S * O ^ (4:ℕ) + A * S * O ^ (2:ℕ) * K - A * W ^ (3:ℕ) * N) * h2 + (2 * A * S ^ (2:ℕ) *
      O ^ (4:ℕ) + 2 * A * S ^ (2:ℕ) * O ^ (2:ℕ) * K - 2 * A * S * W * O ^ (2:ℕ) * N + 6 * A *
      W ^ (2:ℕ) * O ^ (4:ℕ) + 4 * A * W ^ (2:ℕ) * O ^ (2:ℕ) * K) * h1

@[tmio M, powerlib_domain] private theorem zk_S {A B D S W O K N j : ℂ}
    (hj : j ^ 2 = -1) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    ((2 * O * j) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - zkJ A B D K S W) *ᵥ zkSC A D K N S W O j =
      zkDC D K S W O j • zkBil A B N (zkQC A D K S W O j) (zkQC A D K S W O j) := by
  ext k
  fin_cases k <;> simp only [zkJ, zkSC, zkBil, zkQC, zkDC, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.reduceEq, ↓reduceIte]
  · linear_combination (-20 * A ^ (2:ℕ) * D * S * W * O ^ (4:ℕ) - 8 * A ^ (2:ℕ) * S ^ (2:ℕ) * W *
      O ^ (4:ℕ) - 8 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * K + 8 * A ^ (2:ℕ) * S * W ^ (2:ℕ) *
      O ^ (2:ℕ) * N + 12 * A ^ (2:ℕ) * W * O ^ (6:ℕ) + 12 * A ^ (2:ℕ) * W * O ^ (4:ℕ) * K) * hj
  · linear_combination (12 * A ^ (2:ℕ) * D * W * O ^ (3:ℕ) * j + 4 * A ^ (2:ℕ) * S * W * O ^ (3:ℕ) *
      j - 2 * A ^ (2:ℕ) * S * W * O * K * j + 2 * A ^ (2:ℕ) * W ^ (2:ℕ) * O * N * j + 30 * A ^ (2:ℕ)
      * W * O ^ (4:ℕ) * j ^ (2:ℕ) - 4 * A ^ (2:ℕ) * W * O ^ (4:ℕ) - 4 * A ^ (2:ℕ) * W * O ^ (2:ℕ) *
      K) * h1 + (24 * A ^ (2:ℕ) * D ^ (2:ℕ) * S * W * O ^ (4:ℕ) + 12 * A ^ (2:ℕ) * D ^ (2:ℕ) * W *
      O ^ (5:ℕ) * j + 24 * A ^ (2:ℕ) * D * S * W * O ^ (5:ℕ) * j - 12 * A ^ (2:ℕ) * D * W *
      O ^ (6:ℕ) - 18 * A ^ (2:ℕ) * D * W * O ^ (4:ℕ) * K - 4 * A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ)
      - 4 * A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K + 4 * A ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) *
      O ^ (2:ℕ) * N - 4 * A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) - 4 * A ^ (2:ℕ) * S * W ^ (3:ℕ) *
      O ^ (2:ℕ) * K + 32 * A ^ (2:ℕ) * S * W * O ^ (6:ℕ) + 32 * A ^ (2:ℕ) * S * W * O ^ (4:ℕ) * K +
      4 * A ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * N - 16 * A ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N) * hj
  · linear_combination (-6 * A * D * S * W * O ^ (2:ℕ) - 6 * A * D * W * O ^ (3:ℕ) * j - 3 * A *
      S ^ (2:ℕ) * W * O ^ (2:ℕ) - 12 * A * S * W * O ^ (3:ℕ) * j - 3 * A * W ^ (3:ℕ) * O ^ (2:ℕ) +
      15 * A * W * O ^ (4:ℕ) + 3 * A * W * O ^ (2:ℕ) * K) * h2 + (-8 * A * D * W * O ^ (4:ℕ) - 12 *
      A * S * W * O ^ (4:ℕ) - 6 * A * S * W * O ^ (2:ℕ) * K + 2 * A * W ^ (2:ℕ) * O ^ (2:ℕ) * N - 18
      * A * W * O ^ (5:ℕ) * j - 6 * A * W * O ^ (3:ℕ) * K * j) * h1 + (24 * A * D * S * W *
      O ^ (6:ℕ) + 12 * A * S ^ (2:ℕ) * W * O ^ (6:ℕ) + 12 * A * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K + 12 *
      A * W ^ (3:ℕ) * O ^ (6:ℕ) + 12 * A * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 12 * A * W * O ^ (8:ℕ) - 12 *
      A * W * O ^ (6:ℕ) * K) * hj
  · linear_combination (10 * A * D * S * O ^ (3:ℕ) * j - 6 * A * D * W ^ (2:ℕ) * O ^ (2:ℕ) + A *
      S ^ (3:ℕ) * O ^ (2:ℕ) + A * S ^ (3:ℕ) * K - A * S ^ (2:ℕ) * W * N + 4 * A * S ^ (2:ℕ) *
      O ^ (3:ℕ) * j + 4 * A * S ^ (2:ℕ) * O * K * j + A * S * W ^ (2:ℕ) * O ^ (2:ℕ) + A * S *
      W ^ (2:ℕ) * K - 4 * A * S * W * O * N * j + A * S * O ^ (4:ℕ) + A * S * O ^ (2:ℕ) * K - A *
      W ^ (3:ℕ) * N + 4 * A * W * O ^ (2:ℕ) * N - 6 * A * O ^ (5:ℕ) * j - 6 * A * O ^ (3:ℕ) * K * j)
      * h2 + (16 * A * D * O ^ (5:ℕ) * j + 2 * A * S ^ (2:ℕ) * O ^ (4:ℕ) + 2 * A * S ^ (2:ℕ) *
      O ^ (2:ℕ) * K - 2 * A * S * W * O ^ (2:ℕ) * N + 18 * A * S * O ^ (5:ℕ) * j + 18 * A * S *
      O ^ (3:ℕ) * K * j - 10 * A * W ^ (2:ℕ) * O ^ (4:ℕ) - 4 * A * W ^ (2:ℕ) * O ^ (2:ℕ) * K - 4 * A
      * W * O ^ (3:ℕ) * N * j - 8 * A * O ^ (6:ℕ) - 8 * A * O ^ (4:ℕ) * K) * h1 + (-8 * A *
      D ^ (2:ℕ) * S * O ^ (6:ℕ) + 8 * A * D * S * W * O ^ (4:ℕ) * N + 8 * A * D * W ^ (2:ℕ) *
      O ^ (6:ℕ) + 8 * A * D * W ^ (2:ℕ) * O ^ (4:ℕ) * K - 8 * A * D * O ^ (8:ℕ) - 8 * A * D *
      O ^ (6:ℕ) * K - 4 * A * S ^ (3:ℕ) * O ^ (6:ℕ) - 8 * A * S ^ (3:ℕ) * O ^ (4:ℕ) * K - 4 * A *
      S ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + 4 * A * S ^ (2:ℕ) * W * O ^ (4:ℕ) * N + 4 * A * S ^ (2:ℕ)
      * W * O ^ (2:ℕ) * K * N - 4 * A * S * W ^ (2:ℕ) * O ^ (6:ℕ) - 8 * A * S * W ^ (2:ℕ) *
      O ^ (4:ℕ) * K - 4 * A * S * W ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - 20 * A * S * O ^ (8:ℕ) - 40 *
      A * S * O ^ (6:ℕ) * K - 20 * A * S * O ^ (4:ℕ) * K ^ (2:ℕ) + 4 * A * W ^ (3:ℕ) * O ^ (4:ℕ) * N
      + 4 * A * W ^ (3:ℕ) * O ^ (2:ℕ) * K * N - 4 * A * W * O ^ (6:ℕ) * N - 4 * A * W * O ^ (4:ℕ) *
      K * N) * hj

@[tmio M, powerlib_domain] private theorem zkRC_apply_zero {A D K N S W O : ℂ} :
    zkRC A D K N S W O 0 = 2 * A ^ (2:ℕ) * D * W ^ (3:ℕ) * O ^ (2:ℕ) + A ^ (2:ℕ) * S ^ (3:ℕ) * W *
        O ^ (2:ℕ) + A ^ (2:ℕ) * S ^ (3:ℕ) * W * K - A ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * N +
        A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) + A ^ (2:ℕ) * S * W ^ (3:ℕ) * K + A ^ (2:ℕ) * S * W *
        O ^ (4:ℕ) + A ^ (2:ℕ) * S * W * O ^ (2:ℕ) * K - A ^ (2:ℕ) * W ^ (4:ℕ) * N := by
  rw [zkRC]
  simp only [Matrix.cons_val_zero]

@[tmio M, powerlib_domain] private theorem zkRC_apply_three {A D K N S W O : ℂ} :
    zkRC A D K N S W O 3 = -4 * A * D * S * W ^ (2:ℕ) * O ^ (4:ℕ) - 2 * A * D * S * W ^ (2:ℕ) *
        O ^ (2:ℕ) * K + 4 * A * D * S * O ^ (6:ℕ) + 4 * A * D * S * O ^ (4:ℕ) * K + 2 * A * D *
        W ^ (3:ℕ) * O ^ (2:ℕ) * N - 2 * A * D * W * O ^ (4:ℕ) * N + A * S ^ (4:ℕ) * O ^ (4:ℕ) + 2 *
        A * S ^ (4:ℕ) * O ^ (2:ℕ) * K + A * S ^ (4:ℕ) * K ^ (2:ℕ) - A * S ^ (3:ℕ) * W * O ^ (2:ℕ) *
        N - A * S ^ (3:ℕ) * W * K * N + A * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K + A * S ^ (2:ℕ) *
        W ^ (2:ℕ) * K ^ (2:ℕ) + 4 * A * S ^ (2:ℕ) * O ^ (6:ℕ) + 8 * A * S ^ (2:ℕ) * O ^ (4:ℕ) * K +
        4 * A * S ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - A * S * W ^ (3:ℕ) * O ^ (2:ℕ) * N - A * S *
        W ^ (3:ℕ) * K * N - 3 * A * S * W * O ^ (4:ℕ) * N - 3 * A * S * W * O ^ (2:ℕ) * K * N - A *
        W ^ (4:ℕ) * O ^ (4:ℕ) - A * W ^ (4:ℕ) * O ^ (2:ℕ) * K + 2 * A * W ^ (2:ℕ) * O ^ (6:ℕ) + 3 *
        A * W ^ (2:ℕ) * O ^ (4:ℕ) * K + A * W ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - A * O ^ (8:ℕ) - 2 *
        A * O ^ (6:ℕ) * K - A * O ^ (4:ℕ) * K ^ (2:ℕ) := by
  rw [zkRC]
  simp only [Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

@[tmio M, powerlib_domain] private theorem zkSC_apply_zero {A D K N S W O j : ℂ} :
    zkSC A D K N S W O j 0 = -10 * A ^ (2:ℕ) * D * S * W * O ^ (3:ℕ) * j + 6 * A ^ (2:ℕ) * D *
        W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) - A ^ (2:ℕ) * S ^ (3:ℕ) * W *
        K + A ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * N - 4 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j -
        4 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O * K * j - A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) -
        A ^ (2:ℕ) * S * W ^ (3:ℕ) * K + 4 * A ^ (2:ℕ) * S * W ^ (2:ℕ) * O * N * j - A ^ (2:ℕ) * S *
        W * O ^ (4:ℕ) - A ^ (2:ℕ) * S * W * O ^ (2:ℕ) * K + A ^ (2:ℕ) * W ^ (4:ℕ) * N - 4 *
        A ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N + 6 * A ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 6 * A ^ (2:ℕ) *
        W * O ^ (3:ℕ) * K * j := by
  rw [zkSC]
  simp only [Matrix.cons_val_zero]

@[tmio M, powerlib_domain] private theorem zkSC_apply_three {A D K N S W O j : ℂ} :
    zkSC A D K N S W O j 3 = -4 * A * D ^ (2:ℕ) * S * O ^ (5:ℕ) * j + 8 * A * D ^ (2:ℕ) * W ^ (2:ℕ)
        * O ^ (4:ℕ) - 8 * A * D ^ (2:ℕ) * O ^ (6:ℕ) - 4 * A * D * S * W ^ (2:ℕ) * O ^ (4:ℕ) + 2 * A
        * D * S * W ^ (2:ℕ) * O ^ (2:ℕ) * K + 4 * A * D * S * W * O ^ (3:ℕ) * N * j - 12 * A * D * S
        * O ^ (6:ℕ) - 12 * A * D * S * O ^ (4:ℕ) * K - 2 * A * D * W ^ (3:ℕ) * O ^ (2:ℕ) * N + 4 * A
        * D * W ^ (2:ℕ) * O ^ (5:ℕ) * j + 4 * A * D * W ^ (2:ℕ) * O ^ (3:ℕ) * K * j + 2 * A * D * W
        * O ^ (4:ℕ) * N - 4 * A * D * O ^ (7:ℕ) * j - 4 * A * D * O ^ (5:ℕ) * K * j - A * S ^ (4:ℕ)
        * O ^ (4:ℕ) - 2 * A * S ^ (4:ℕ) * O ^ (2:ℕ) * K - A * S ^ (4:ℕ) * K ^ (2:ℕ) + A * S ^ (3:ℕ)
        * W * O ^ (2:ℕ) * N + A * S ^ (3:ℕ) * W * K * N - 2 * A * S ^ (3:ℕ) * O ^ (5:ℕ) * j - 4 * A
        * S ^ (3:ℕ) * O ^ (3:ℕ) * K * j - 2 * A * S ^ (3:ℕ) * O * K ^ (2:ℕ) * j - 4 * A * S ^ (2:ℕ)
        * W ^ (2:ℕ) * O ^ (4:ℕ) - 5 * A * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K - A * S ^ (2:ℕ) *
        W ^ (2:ℕ) * K ^ (2:ℕ) + 2 * A * S ^ (2:ℕ) * W * O ^ (3:ℕ) * N * j + 2 * A * S ^ (2:ℕ) * W *
        O * K * N * j - 8 * A * S ^ (2:ℕ) * O ^ (6:ℕ) - 16 * A * S ^ (2:ℕ) * O ^ (4:ℕ) * K - 8 * A *
        S ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + A * S * W ^ (3:ℕ) * O ^ (2:ℕ) * N + A * S * W ^ (3:ℕ) *
        K * N - 2 * A * S * W ^ (2:ℕ) * O ^ (5:ℕ) * j - 4 * A * S * W ^ (2:ℕ) * O ^ (3:ℕ) * K * j -
        2 * A * S * W ^ (2:ℕ) * O * K ^ (2:ℕ) * j + 3 * A * S * W * O ^ (4:ℕ) * N + 3 * A * S * W *
        O ^ (2:ℕ) * K * N - 10 * A * S * O ^ (7:ℕ) * j - 20 * A * S * O ^ (5:ℕ) * K * j - 10 * A * S
        * O ^ (3:ℕ) * K ^ (2:ℕ) * j - 3 * A * W ^ (4:ℕ) * O ^ (4:ℕ) - 3 * A * W ^ (4:ℕ) * O ^ (2:ℕ)
        * K + 2 * A * W ^ (3:ℕ) * O ^ (3:ℕ) * N * j + 2 * A * W ^ (3:ℕ) * O * K * N * j + 6 * A *
        W ^ (2:ℕ) * O ^ (6:ℕ) + 9 * A * W ^ (2:ℕ) * O ^ (4:ℕ) * K + 3 * A * W ^ (2:ℕ) * O ^ (2:ℕ) *
        K ^ (2:ℕ) - 2 * A * W * O ^ (5:ℕ) * N * j - 2 * A * W * O ^ (3:ℕ) * K * N * j - 3 * A *
        O ^ (8:ℕ) - 6 * A * O ^ (6:ℕ) * K - 3 * A * O ^ (4:ℕ) * K ^ (2:ℕ) := by
  rw [zkSC]
  simp only [Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

@[tmio M, powerlib_domain] private theorem zk_Y2p1 {A B D S W O K N j : ℂ}
    (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O)
    (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2 = -1)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2)) :
    starRingEnd ℂ ((zkLC A D S W O j) 1) *
        (zkBil A B N (zkQC A D K S W O j) (zkRC A D K N S W O)) 1 =
      (-4 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) + 4 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) + 4 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) + 4 * A ^ (3:ℕ) * D * S *
        W ^ (3:ℕ) * O ^ (4:ℕ) * K + 4 * A ^ (3:ℕ) * D * S * W * O ^ (8:ℕ) + 4 * A ^ (3:ℕ) * D * S *
        W * O ^ (6:ℕ) * K + 2 * A ^ (3:ℕ) * D * W ^ (4:ℕ) * O ^ (4:ℕ) * N - 2 * A ^ (3:ℕ) * D *
        W ^ (2:ℕ) * O ^ (6:ℕ) * N + 2 * A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (4:ℕ) + 4 * A ^ (3:ℕ) *
        S ^ (6:ℕ) * W * O ^ (2:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (6:ℕ) * W * K ^ (2:ℕ) - 3 * A ^ (3:ℕ) *
        S ^ (5:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N - 3 * A ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (2:ℕ) * K * N + 3 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) + 7 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) *
        O ^ (2:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (4:ℕ) *
        W ^ (3:ℕ) * N ^ (2:ℕ) + 7 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) + 14 * A ^ (3:ℕ) *
        S ^ (4:ℕ) * W * O ^ (4:ℕ) * K + 7 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * K ^ (2:ℕ) - 6 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * N - 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) *
        K * N - 5 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N - 5 * A ^ (3:ℕ) * S ^ (3:ℕ) *
        W ^ (2:ℕ) * O ^ (2:ℕ) * K * N + 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K + 2 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) *
        N ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + 6 * A ^ (3:ℕ) * S ^ (2:ℕ) *
        W ^ (3:ℕ) * O ^ (4:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) -
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) + 10 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
        O ^ (8:ℕ) + 20 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 10 * A ^ (3:ℕ) * S ^ (2:ℕ) * W
        * O ^ (4:ℕ) * K ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S * W ^ (6:ℕ) * O ^ (2:ℕ) * N - 3 * A ^ (3:ℕ) * S
        * W ^ (6:ℕ) * K * N - A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (4:ℕ) * N - A ^ (3:ℕ) * S * W ^ (4:ℕ)
        * O ^ (2:ℕ) * K * N - 4 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (6:ℕ) * N - 4 * A ^ (3:ℕ) * S *
        W ^ (2:ℕ) * O ^ (4:ℕ) * K * N - A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (4:ℕ) - A ^ (3:ℕ) * W ^ (7:ℕ) *
        O ^ (2:ℕ) * K + A ^ (3:ℕ) * W ^ (7:ℕ) * N ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) +
        4 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) -
        A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) - 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) - 5 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K - 2 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) +
        A ^ (3:ℕ) * W * O ^ (10:ℕ) + 2 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K + A ^ (3:ℕ) * W * O ^ (6:ℕ) *
        K ^ (2:ℕ)) + (4 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) - 6 * A ^ (3:ℕ) * D * S
        * W ^ (2:ℕ) * O ^ (5:ℕ) * N + 8 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (5:ℕ) + 4 * A ^ (3:ℕ) * D
        * W ^ (5:ℕ) * O ^ (3:ℕ) * K - 20 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) - 16 * A ^ (3:ℕ) *
        D * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 12 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) + 12 * A ^ (3:ℕ) * D * W
        * O ^ (7:ℕ) * K + 3 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (5:ℕ) + 6 * A ^ (3:ℕ) * S ^ (5:ℕ) * W
        * O ^ (3:ℕ) * K + 3 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O * K ^ (2:ℕ) - 5 * A ^ (3:ℕ) * S ^ (4:ℕ)
        * W ^ (2:ℕ) * O ^ (3:ℕ) * N - 5 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) * O * K * N + 2 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) + 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) *
        O ^ (3:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * K ^ (2:ℕ) + 2 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W ^ (3:ℕ) * O * N ^ (2:ℕ) + 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (7:ℕ) + 24 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K + 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) *
        K ^ (2:ℕ) - 6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * N - 6 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (4:ℕ) * O * K * N - 11 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (5:ℕ) * N -
        11 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * K * N - A ^ (3:ℕ) * S * W ^ (5:ℕ) *
        O ^ (5:ℕ) + A ^ (3:ℕ) * S * W ^ (5:ℕ) * O * K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O *
        N ^ (2:ℕ) - 8 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) - 10 * A ^ (3:ℕ) * S * W ^ (3:ℕ) *
        O ^ (5:ℕ) * K - 2 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * K ^ (2:ℕ) + 21 * A ^ (3:ℕ) * S *
        W * O ^ (9:ℕ) + 42 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K + 21 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ)
        * K ^ (2:ℕ) - A ^ (3:ℕ) * W ^ (6:ℕ) * O ^ (3:ℕ) * N - A ^ (3:ℕ) * W ^ (6:ℕ) * O * K * N +
        A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (5:ℕ) * N + A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * K * N) * j := by
  simp only [zkLC, zkBil, zkQC, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_add, map_sub, map_neg, map_pow, hS, hW, hO, hjc]
  rw [zkRC_apply_zero, zkRC_apply_three]
  linear_combination (-2 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 6 * A ^ (3:ℕ) * D *
      W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j - A ^ (3:ℕ) *
      S ^ (4:ℕ) * W * O * K * j + A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O * N * j - 3 * A ^ (3:ℕ) *
      S ^ (3:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K *
      j ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j - A ^ (3:ℕ) * S ^ (2:ℕ) *
      W ^ (3:ℕ) * O * K * j + 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N * j ^ (2:ℕ) - 3
      * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j ^ (3:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (5:ℕ) * j - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j ^ (3:ℕ) - 2 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j + A ^ (3:ℕ) * S * W ^ (4:ℕ) * O * N * j - A ^ (3:ℕ) * S *
      W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) - 2 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) - A ^ (3:ℕ) * S
      * W ^ (3:ℕ) * O ^ (2:ℕ) * K * j ^ (2:ℕ) + 3 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (3:ℕ) * N *
      j ^ (3:ℕ) + A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (3:ℕ) * N * j - A ^ (3:ℕ) * S * W * O ^ (6:ℕ) *
      j ^ (4:ℕ) - 6 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) * j ^ (2:ℕ) + 4 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ)
      - A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K * j ^ (4:ℕ) - 6 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K *
      j ^ (2:ℕ) + 4 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K + A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * N *
      j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) * j - 2 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ)
      * K * j + A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N * j ^ (4:ℕ) + 3 * A ^ (3:ℕ) * W ^ (2:ℕ) *
      O ^ (4:ℕ) * N * j ^ (2:ℕ) - 2 * A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N - 6 * A ^ (3:ℕ) * W *
      O ^ (7:ℕ) * j ^ (3:ℕ) + 6 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j - 6 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K
      * j ^ (3:ℕ) + 6 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j) * h1 + (-6 * A ^ (3:ℕ) * D ^ (2:ℕ) * S *
      W ^ (3:ℕ) * O ^ (5:ℕ) * j + 4 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 2 * A ^ (3:ℕ)
      * D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) - 4 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
      O ^ (6:ℕ) - 6 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) - 4 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ)
      * O ^ (4:ℕ) * K + 3 * A ^ (3:ℕ) * D * S * W ^ (2:ℕ) * O ^ (5:ℕ) * N * j - 2 * A ^ (3:ℕ) * D *
      S * W * O ^ (8:ℕ) * j ^ (2:ℕ) - 2 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K * j ^ (2:ℕ) - 2 *
      A ^ (3:ℕ) * D * W ^ (4:ℕ) * O ^ (4:ℕ) * N + 8 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) * j + 8
      * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K * j + A ^ (3:ℕ) * D * W ^ (2:ℕ) * O ^ (6:ℕ) * N *
      j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) * j - 6 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K * j
      - 2 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) - 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K -
      2 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) *
      O ^ (4:ℕ) * N + A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N - 5 * A ^ (3:ℕ) *
      S ^ (3:ℕ) * W * O ^ (7:ℕ) * j - 10 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j - 5 *
      A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * K ^ (2:ℕ) * j + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
      O ^ (6:ℕ) + 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (2:ℕ)
      * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) *
      N ^ (2:ℕ) + 5 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (5:ℕ) * N * j + 5 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * K * N * j - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) *
      j ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) - 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (6:ℕ) * K * j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K - 2 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) * j ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ)
      * K ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (4:ℕ) * N - 3 * A ^ (3:ℕ) * S * W ^ (4:ℕ) *
      O ^ (2:ℕ) * K * N + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) * j + 2 * A ^ (3:ℕ) * S * W ^ (3:ℕ)
      * O ^ (5:ℕ) * K * j + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * K ^ (2:ℕ) * j + 2 * A ^ (3:ℕ) *
      S * W ^ (2:ℕ) * O ^ (6:ℕ) * N * j ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ) * K * N
      * j ^ (2:ℕ) - 11 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) * j - 22 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K
      * j - 11 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ) * j - A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) -
      A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) -
      A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (5:ℕ) * N * j - A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * K * N * j + 2
      * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) + 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K + A ^ (3:ℕ) *
      W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) - A ^ (3:ℕ) * W * O ^ (10:ℕ) - 2 * A ^ (3:ℕ) * W * O ^ (8:ℕ)
      * K - A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem zk_Y2p2 {A B D S W O K N j : ℂ}
    (hA : starRingEnd ℂ A = A) (hS : starRingEnd ℂ S = S) (hO : starRingEnd ℂ O = O)
    (hjc : starRingEnd ℂ j = -j) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    starRingEnd ℂ ((zkLC A D S W O j) 2) *
        (zkBil A B N (zkQC A D K S W O j) (zkRC A D K N S W O)) 2 =
      (4 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 4 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) - 4 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) - 4 * A ^ (3:ℕ) * D * S *
        W ^ (3:ℕ) * O ^ (4:ℕ) * K - 4 * A ^ (3:ℕ) * D * S * W * O ^ (8:ℕ) - 4 * A ^ (3:ℕ) * D * S *
        W * O ^ (6:ℕ) * K - 2 * A ^ (3:ℕ) * D * W ^ (4:ℕ) * O ^ (4:ℕ) * N + 2 * A ^ (3:ℕ) * D *
        W ^ (2:ℕ) * O ^ (6:ℕ) * N - A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) *
        S ^ (6:ℕ) * W * O ^ (2:ℕ) * K - A ^ (3:ℕ) * S ^ (6:ℕ) * W * K ^ (2:ℕ) + A ^ (3:ℕ) *
        S ^ (5:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N + A ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (2:ℕ) * K * N - 2 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) - 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) *
        O ^ (2:ℕ) * K - 2 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * K ^ (2:ℕ) - 4 * A ^ (3:ℕ) *
        S ^ (4:ℕ) * W * O ^ (6:ℕ) - 8 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K - 4 * A ^ (3:ℕ) *
        S ^ (4:ℕ) * W * O ^ (2:ℕ) * K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) *
        N + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * K * N + 3 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) *
        O ^ (4:ℕ) * N + 3 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N - A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K -
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * K ^ (2:ℕ) - 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) - 8 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 4 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - 7 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) -
        14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K - 7 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) *
        K ^ (2:ℕ) + A ^ (3:ℕ) * S * W ^ (6:ℕ) * O ^ (2:ℕ) * N + A ^ (3:ℕ) * S * W ^ (6:ℕ) * K * N -
        A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (4:ℕ) * N - A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (2:ℕ) * K * N +
        4 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (6:ℕ) * N + 4 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ) *
        K * N) + (-4 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) + 2 * A ^ (3:ℕ) * D * S *
        W ^ (2:ℕ) * O ^ (5:ℕ) * N + 4 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) + 4 * A ^ (3:ℕ) * D *
        W ^ (3:ℕ) * O ^ (5:ℕ) * K - 4 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) - 4 * A ^ (3:ℕ) * D * W *
        O ^ (7:ℕ) * K - A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (5:ℕ) - 2 * A ^ (3:ℕ) * S ^ (5:ℕ) * W *
        O ^ (3:ℕ) * K - A ^ (3:ℕ) * S ^ (5:ℕ) * W * O * K ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (4:ℕ) *
        W ^ (2:ℕ) * O ^ (3:ℕ) * N + A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) * O * K * N - 2 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) - 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K -
        2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * K ^ (2:ℕ) - 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W *
        O ^ (7:ℕ) - 8 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K - 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W *
        O ^ (3:ℕ) * K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * N + 2 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O * K * N + 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) *
        O ^ (5:ℕ) * N + 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * K * N - A ^ (3:ℕ) * S *
        W ^ (5:ℕ) * O ^ (5:ℕ) - 2 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K - A ^ (3:ℕ) * S *
        W ^ (5:ℕ) * O * K ^ (2:ℕ) - 4 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) - 8 * A ^ (3:ℕ) * S *
        W ^ (3:ℕ) * O ^ (5:ℕ) * K - 4 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * K ^ (2:ℕ) - 7 *
        A ^ (3:ℕ) * S * W * O ^ (9:ℕ) - 14 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K - 7 * A ^ (3:ℕ) * S *
        W * O ^ (5:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * W ^ (6:ℕ) * O ^ (3:ℕ) * N + A ^ (3:ℕ) * W ^ (6:ℕ) *
        O * K * N - A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (5:ℕ) * N - A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * K *
        N) * j := by
  simp only [zkLC, zkBil, zkQC, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_sub, hA, hS, hO, hjc]
  rw [zkRC_apply_zero]
  linear_combination (-2 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (2:ℕ) - 2 * A ^ (3:ℕ) * D * W ^ (3:ℕ)
      * O ^ (3:ℕ) * j - A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (4:ℕ) * W * K +
      A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * N - A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j - A ^ (3:ℕ)
      * S ^ (3:ℕ) * W * O * K * j - A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (3:ℕ) *
      S ^ (2:ℕ) * W ^ (3:ℕ) * K + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O * N * j - A ^ (3:ℕ) *
      S ^ (2:ℕ) * W * O ^ (4:ℕ) - A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * K + A ^ (3:ℕ) * S *
      W ^ (4:ℕ) * N - A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - A ^ (3:ℕ) * S * W ^ (3:ℕ) * O * K
      * j - A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * j - A ^ (3:ℕ) * S * W * O ^ (3:ℕ) * K * j + A ^ (3:ℕ) *
      W ^ (4:ℕ) * O * N * j) * h2 + (-4 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) *
      S ^ (3:ℕ) * W * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K + 2 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j - 2 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j - 2 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) - 2
      * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 2 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (3:ℕ) * N *
      j - 4 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) - 4 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K - 2 * A ^ (3:ℕ)
      * W ^ (3:ℕ) * O ^ (5:ℕ) * j - 2 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K * j + 2 * A ^ (3:ℕ) *
      W ^ (2:ℕ) * O ^ (4:ℕ) * N - 4 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j - 4 * A ^ (3:ℕ) * W * O ^ (5:ℕ)
      * K * j) * h1

@[tmio M, powerlib_domain] private theorem zk_Y2 {A B D S W O K N j : ℂ}
    (hA : starRingEnd ℂ A = A) (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W)
    (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2 = -1)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    pairing (zkLC A D S W O j) (zkBil A B N (zkQC A D K S W O j) (zkRC A D K N S W O)) =
      (A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (4:ℕ) + 2 * A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (2:ℕ) * K +
        A ^ (3:ℕ) * S ^ (6:ℕ) * W * K ^ (2:ℕ) - 2 * A ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) *
        N - 2 * A ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (2:ℕ) * K * N + A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) *
        O ^ (4:ℕ) + 3 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 2 * A ^ (3:ℕ) *
        S ^ (4:ℕ) * W ^ (3:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * N ^ (2:ℕ) + 3 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) + 6 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K + 3 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * K ^ (2:ℕ) - 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) *
        O ^ (2:ℕ) * N - 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * K * N - 2 * A ^ (3:ℕ) * S ^ (3:ℕ) *
        W ^ (2:ℕ) * O ^ (4:ℕ) * N - 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N -
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) *
        K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * N ^ (2:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) *
        W ^ (3:ℕ) * O ^ (6:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K - A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) + 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) +
        6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) *
        K ^ (2:ℕ) - 2 * A ^ (3:ℕ) * S * W ^ (6:ℕ) * O ^ (2:ℕ) * N - 2 * A ^ (3:ℕ) * S * W ^ (6:ℕ) *
        K * N - 2 * A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (4:ℕ) * N - 2 * A ^ (3:ℕ) * S * W ^ (4:ℕ) *
        O ^ (2:ℕ) * K * N - A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (4:ℕ) - A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (2:ℕ) *
        K + A ^ (3:ℕ) * W ^ (7:ℕ) * N ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) + 4 *
        A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) -
        A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) - 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) - 5 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K - 2 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) +
        A ^ (3:ℕ) * W * O ^ (10:ℕ) + 2 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K + A ^ (3:ℕ) * W * O ^ (6:ℕ) *
        K ^ (2:ℕ)) + (-4 * A ^ (3:ℕ) * D * S * W ^ (2:ℕ) * O ^ (5:ℕ) * N + 8 * A ^ (3:ℕ) * D *
        W ^ (5:ℕ) * O ^ (5:ℕ) + 4 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (3:ℕ) * K - 16 * A ^ (3:ℕ) * D *
        W ^ (3:ℕ) * O ^ (7:ℕ) - 12 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 8 * A ^ (3:ℕ) * D *
        W * O ^ (9:ℕ) + 8 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (5:ℕ) * W *
        O ^ (5:ℕ) + 4 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (3:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (5:ℕ) * W *
        O * K ^ (2:ℕ) - 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * N - 4 * A ^ (3:ℕ) *
        S ^ (4:ℕ) * W ^ (2:ℕ) * O * K * N + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K +
        2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) *
        W ^ (3:ℕ) * O * N ^ (2:ℕ) + 8 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (7:ℕ) + 16 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W * O ^ (5:ℕ) * K + 8 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * K ^ (2:ℕ) - 4 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * N - 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) *
        O * K * N - 8 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (5:ℕ) * N - 8 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * K * N - 2 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (5:ℕ) - 2 *
        A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K + 2 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O * N ^ (2:ℕ) -
        12 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) - 18 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K
        - 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * K ^ (2:ℕ) + 14 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ)
        + 28 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K + 14 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ)) *
        j := by
  rw [pairing_apply, Fin.sum_univ_four, zk_Y2p1 hS hW hO hjc hj h1, zk_Y2p2 hA hS hO hjc h1 h2]
  have e0 : (zkBil A B N (zkQC A D K S W O j) (zkRC A D K N S W O)) 0 = 0 := rfl
  have e3 : (zkBil A B N (zkQC A D K S W O j) (zkRC A D K N S W O)) 3 = 0 := rfl
  rw [e0, e3]
  ring

@[tmio M, powerlib_domain] private theorem zk_Y3p1 {A B D S W O K N j : ℂ}
    (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O)
    (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2 = -1)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2)) :
    starRingEnd ℂ ((zkLC A D S W O j) 1) *
        (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K N S W O j)) 1 =
      (12 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 40 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) + 28 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 44 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ)
        * O ^ (6:ℕ) - 44 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 88 * A ^ (3:ℕ) * D * S *
        W * O ^ (8:ℕ) + 88 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K + 30 * A ^ (3:ℕ) * D * W ^ (4:ℕ)
        * O ^ (4:ℕ) * N - 30 * A ^ (3:ℕ) * D * W ^ (2:ℕ) * O ^ (6:ℕ) * N - 2 * A ^ (3:ℕ) * S ^ (6:ℕ)
        * W * O ^ (4:ℕ) - 4 * A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (2:ℕ) * K - 2 * A ^ (3:ℕ) * S ^ (6:ℕ)
        * W * K ^ (2:ℕ) + 3 * A ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N + 3 * A ^ (3:ℕ) *
        S ^ (5:ℕ) * W ^ (2:ℕ) * K * N - 7 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) - 11 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K - 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) *
        K ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * N ^ (2:ℕ) + 9 * A ^ (3:ℕ) * S ^ (4:ℕ) * W *
        O ^ (6:ℕ) + 18 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K + 9 * A ^ (3:ℕ) * S ^ (4:ℕ) * W *
        O ^ (2:ℕ) * K ^ (2:ℕ) + 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * N + 6 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * K * N - 27 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) *
        O ^ (4:ℕ) * N - 27 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N - 8 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 10 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K -
        2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * K ^ (2:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) *
        N ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + 10 * A ^ (3:ℕ) * S ^ (2:ℕ) *
        W ^ (3:ℕ) * O ^ (4:ℕ) * K + 8 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) +
        13 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) + 68 * A ^ (3:ℕ) * S ^ (2:ℕ)
        * W * O ^ (8:ℕ) + 136 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 68 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) + 3 * A ^ (3:ℕ) * S * W ^ (6:ℕ) * O ^ (2:ℕ) * N + 3 *
        A ^ (3:ℕ) * S * W ^ (6:ℕ) * K * N - 15 * A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (4:ℕ) * N - 15 *
        A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (2:ℕ) * K * N - 60 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (6:ℕ) *
        N - 60 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ) * K * N - 3 * A ^ (3:ℕ) * W ^ (7:ℕ) *
        O ^ (4:ℕ) - 3 * A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (2:ℕ) * K - A ^ (3:ℕ) * W ^ (7:ℕ) * N ^ (2:ℕ) +
        9 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) + 12 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + 3 *
        A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + 5 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) *
        N ^ (2:ℕ) - 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) - 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) *
        K - 4 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * N ^ (2:ℕ) - 3 * A ^ (3:ℕ) * W * O ^ (10:ℕ) - 6 *
        A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - 3 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) + (8 * A ^ (3:ℕ)
        * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) + 4 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W * O ^ (7:ℕ) - 8
        * A ^ (3:ℕ) * D * S * W ^ (4:ℕ) * O ^ (3:ℕ) * N - 10 * A ^ (3:ℕ) * D * S * W ^ (2:ℕ) *
        O ^ (5:ℕ) * N - 8 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (5:ℕ) - 20 * A ^ (3:ℕ) * D * W ^ (5:ℕ) *
        O ^ (3:ℕ) * K + 48 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) + 60 * A ^ (3:ℕ) * D * W ^ (3:ℕ)
        * O ^ (5:ℕ) * K - 40 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) - 40 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) *
        K - 11 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (5:ℕ) - 22 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (3:ℕ)
        * K - 11 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O * K ^ (2:ℕ) + 17 * A ^ (3:ℕ) * S ^ (4:ℕ) *
        W ^ (2:ℕ) * O ^ (3:ℕ) * N + 17 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) * O * K * N - 18 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) - 30 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) *
        O ^ (3:ℕ) * K - 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * K ^ (2:ℕ) - 6 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W ^ (3:ℕ) * O * N ^ (2:ℕ) - 42 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (7:ℕ) - 84 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K - 42 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) *
        K ^ (2:ℕ) + 18 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * N + 18 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (4:ℕ) * O * K * N + 11 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (5:ℕ) * N +
        11 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * K * N - 7 * A ^ (3:ℕ) * S * W ^ (5:ℕ) *
        O ^ (5:ℕ) - 8 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K - A ^ (3:ℕ) * S * W ^ (5:ℕ) * O *
        K ^ (2:ℕ) - 6 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O * N ^ (2:ℕ) + 22 * A ^ (3:ℕ) * S * W ^ (3:ℕ) *
        O ^ (7:ℕ) + 62 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 40 * A ^ (3:ℕ) * S * W ^ (3:ℕ)
        * O ^ (3:ℕ) * K ^ (2:ℕ) + 12 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * N ^ (2:ℕ) - 67 *
        A ^ (3:ℕ) * S * W * O ^ (9:ℕ) - 134 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K - 67 * A ^ (3:ℕ) * S
        * W * O ^ (5:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * W ^ (6:ℕ) * O ^ (3:ℕ) * N + A ^ (3:ℕ) * W ^ (6:ℕ)
        * O * K * N - 5 * A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (5:ℕ) * N - 5 * A ^ (3:ℕ) * W ^ (4:ℕ) *
        O ^ (3:ℕ) * K * N + 4 * A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (7:ℕ) * N + 4 * A ^ (3:ℕ) * W ^ (2:ℕ) *
        O ^ (5:ℕ) * K * N) * j := by
  simp only [zkLC, zkBil, zkQC, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_add, map_sub, map_neg, map_pow, hS, hW, hO, hjc]
  rw [zkSC_apply_zero, zkSC_apply_three]
  linear_combination (-10 * A ^ (3:ℕ) * D * S ^ (2:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) + 6 * A ^ (3:ℕ) *
      D * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 10 * A ^ (3:ℕ) * D * S * W * O ^ (5:ℕ) * j ^ (3:ℕ) - 4 *
      A ^ (3:ℕ) * D * S * W * O ^ (5:ℕ) * j + 6 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ)
      + 8 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) + 10 * A ^ (3:ℕ) * D * W * O ^ (6:ℕ) * j ^ (4:ℕ) -
      18 * A ^ (3:ℕ) * D * W * O ^ (6:ℕ) * j ^ (2:ℕ) - 8 * A ^ (3:ℕ) * D * W * O ^ (6:ℕ) - A ^ (3:ℕ)
      * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j - A ^ (3:ℕ) * S ^ (4:ℕ) * W * O * K * j + A ^ (3:ℕ) *
      S ^ (3:ℕ) * W ^ (2:ℕ) * O * N * j - 5 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) - 5
      * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K * j ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
      O ^ (3:ℕ) * j - A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * K * j + 5 * A ^ (3:ℕ) * S ^ (2:ℕ) *
      W ^ (2:ℕ) * O ^ (2:ℕ) * N * j ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j ^ (3:ℕ)
      - 12 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) *
      K * j ^ (3:ℕ) - 12 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j + A ^ (3:ℕ) * S * W ^ (4:ℕ)
      * O * N * j + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S *
      W ^ (3:ℕ) * O ^ (4:ℕ) + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K * j ^ (2:ℕ) + 8 * A ^ (3:ℕ)
      * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 3 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (3:ℕ) * N * j ^ (3:ℕ) +
      11 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (3:ℕ) * N * j + 5 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) *
      j ^ (4:ℕ) - 30 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) * j ^ (2:ℕ) - 12 * A ^ (3:ℕ) * S * W *
      O ^ (6:ℕ) + 5 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K * j ^ (4:ℕ) - 30 * A ^ (3:ℕ) * S * W *
      O ^ (4:ℕ) * K * j ^ (2:ℕ) - 12 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K - A ^ (3:ℕ) * W ^ (4:ℕ) *
      O ^ (2:ℕ) * N * j ^ (2:ℕ) - 8 * A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * N + 8 * A ^ (3:ℕ) *
      W ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) + 14 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) * j + 8 * A ^ (3:ℕ)
      * W ^ (3:ℕ) * O ^ (3:ℕ) * K * j ^ (3:ℕ) + 26 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K * j - 5 *
      A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N * j ^ (4:ℕ) + 29 * A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N
      * j ^ (2:ℕ) + 2 * A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N + 4 * A ^ (3:ℕ) * W * O ^ (7:ℕ) *
      j ^ (5:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j ^ (3:ℕ) - 48 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j + 4
      * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j ^ (5:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j ^ (3:ℕ) -
      48 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j) * h1 + (14 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) *
      O ^ (5:ℕ) * j + 10 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W * O ^ (7:ℕ) * j ^ (3:ℕ) - 24 * A ^ (3:ℕ) *
      D ^ (2:ℕ) * S * W * O ^ (7:ℕ) * j - 12 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 16 *
      A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) + 48 * A ^ (3:ℕ) * D ^ (2:ℕ) *
      W ^ (3:ℕ) * O ^ (6:ℕ) + 10 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) * j ^ (2:ℕ) - 36 *
      A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 8 * A ^ (3:ℕ) * D * S * W ^ (4:ℕ) * O ^ (3:ℕ) * N * j
      - 4 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) + 62 * A ^ (3:ℕ) * D * S *
      W ^ (3:ℕ) * O ^ (6:ℕ) - 4 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K * j ^ (2:ℕ) + 68 *
      A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 4 * A ^ (3:ℕ) * D * S * W ^ (2:ℕ) * O ^ (5:ℕ)
      * N * j ^ (3:ℕ) + 25 * A ^ (3:ℕ) * D * S * W ^ (2:ℕ) * O ^ (5:ℕ) * N * j + 30 * A ^ (3:ℕ) * D
      * S * W * O ^ (8:ℕ) * j ^ (2:ℕ) - 116 * A ^ (3:ℕ) * D * S * W * O ^ (8:ℕ) + 30 * A ^ (3:ℕ) * D
      * S * W * O ^ (6:ℕ) * K * j ^ (2:ℕ) - 116 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K - 8 *
      A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (5:ℕ) * j - 8 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (3:ℕ) * K * j
      + 4 * A ^ (3:ℕ) * D * W ^ (4:ℕ) * O ^ (4:ℕ) * N * j ^ (2:ℕ) - 38 * A ^ (3:ℕ) * D * W ^ (4:ℕ) *
      O ^ (4:ℕ) * N - 4 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) + 10 * A ^ (3:ℕ) * D *
      W ^ (3:ℕ) * O ^ (7:ℕ) * j - 4 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K * j ^ (3:ℕ) + 10 *
      A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K * j - A ^ (3:ℕ) * D * W ^ (2:ℕ) * O ^ (6:ℕ) * N *
      j ^ (2:ℕ) + 32 * A ^ (3:ℕ) * D * W ^ (2:ℕ) * O ^ (6:ℕ) * N - 2 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ)
      * j ^ (3:ℕ) - 8 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) * j - 2 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K *
      j ^ (3:ℕ) - 8 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K * j - 18 * A ^ (3:ℕ) * S ^ (4:ℕ) * W *
      O ^ (6:ℕ) - 36 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K - 18 * A ^ (3:ℕ) * S ^ (4:ℕ) * W *
      O ^ (2:ℕ) * K ^ (2:ℕ) + 27 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N + 27 *
      A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N - 3 * A ^ (3:ℕ) * S ^ (3:ℕ) * W *
      O ^ (7:ℕ) * j - 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j - 3 * A ^ (3:ℕ) * S ^ (3:ℕ)
      * W * O ^ (3:ℕ) * K ^ (2:ℕ) * j - A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + A ^ (3:ℕ) *
      S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) *
      K ^ (2:ℕ) - 9 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) + 7 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (5:ℕ) * N * j + 7 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ)
      * K * N * j + 14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) * j ^ (2:ℕ) - 95 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W * O ^ (8:ℕ) + 28 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K * j ^ (2:ℕ) - 190 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) *
      K ^ (2:ℕ) * j ^ (2:ℕ) - 95 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) - A ^ (3:ℕ) * S
      * W ^ (4:ℕ) * O ^ (4:ℕ) * N - A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (2:ℕ) * K * N + 15 * A ^ (3:ℕ) *
      S * W ^ (3:ℕ) * O ^ (7:ℕ) * j + 30 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K * j + 15 *
      A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * K ^ (2:ℕ) * j - 4 * A ^ (3:ℕ) * S * W ^ (3:ℕ) *
      O ^ (3:ℕ) * N ^ (2:ℕ) * j - 14 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (6:ℕ) * N * j ^ (2:ℕ) + 64 *
      A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (6:ℕ) * N - 14 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ) * K * N
      * j ^ (2:ℕ) + 64 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ) * K * N + 8 * A ^ (3:ℕ) * S * W *
      O ^ (9:ℕ) * j ^ (3:ℕ) - 35 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) * j + 16 * A ^ (3:ℕ) * S * W *
      O ^ (7:ℕ) * K * j ^ (3:ℕ) - 70 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K * j + 8 * A ^ (3:ℕ) * S * W
      * O ^ (5:ℕ) * K ^ (2:ℕ) * j ^ (3:ℕ) - 35 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ) * j - 3 *
      A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) - 3 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K - A ^ (3:ℕ) *
      W ^ (5:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) + A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (5:ℕ) * N * j + A ^ (3:ℕ) *
      W ^ (4:ℕ) * O ^ (3:ℕ) * K * N * j - 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K - 3 * A ^ (3:ℕ)
      * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) + 4 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * N ^ (2:ℕ) - 4 *
      A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (7:ℕ) * N * j - 4 * A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (5:ℕ) * K * N * j
      - 6 * A ^ (3:ℕ) * W * O ^ (10:ℕ) * j ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W * O ^ (10:ℕ) - 12 * A ^ (3:ℕ)
      * W * O ^ (8:ℕ) * K * j ^ (2:ℕ) + 6 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - 6 * A ^ (3:ℕ) * W *
      O ^ (6:ℕ) * K ^ (2:ℕ) * j ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem zk_Y3p2 {A B D S W O K N j : ℂ}
    (hA : starRingEnd ℂ A = A) (hS : starRingEnd ℂ S = S) (hO : starRingEnd ℂ O = O)
    (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2 = -1)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    starRingEnd ℂ ((zkLC A D S W O j) 2) *
        (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K N S W O j)) 2 =
      (12 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) + 8 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) - 20 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 20 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ)
        * O ^ (6:ℕ) - 20 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 32 * A ^ (3:ℕ) * D * S *
        W * O ^ (8:ℕ) - 32 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K - 14 * A ^ (3:ℕ) * D * W ^ (4:ℕ)
        * O ^ (4:ℕ) * N + 14 * A ^ (3:ℕ) * D * W ^ (2:ℕ) * O ^ (6:ℕ) * N + A ^ (3:ℕ) * S ^ (6:ℕ) * W
        * O ^ (4:ℕ) + 2 * A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (2:ℕ) * K + A ^ (3:ℕ) * S ^ (6:ℕ) * W *
        K ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N - A ^ (3:ℕ) * S ^ (5:ℕ) *
        W ^ (2:ℕ) * K * N + 2 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) + 4 * A ^ (3:ℕ) *
        S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * K ^ (2:ℕ) -
        2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * N - 2 * A ^ (3:ℕ) * S ^ (3:ℕ) *
        W ^ (4:ℕ) * K * N + 5 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N + 5 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) +
        2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) *
        K ^ (2:ℕ) - 16 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) - 32 * A ^ (3:ℕ) * S ^ (2:ℕ)
        * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 16 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ)
        - 19 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) - 38 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) *
        K - 19 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) - A ^ (3:ℕ) * S * W ^ (6:ℕ) *
        O ^ (2:ℕ) * N - A ^ (3:ℕ) * S * W ^ (6:ℕ) * K * N + 9 * A ^ (3:ℕ) * S * W ^ (4:ℕ) *
        O ^ (4:ℕ) * N + 9 * A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (2:ℕ) * K * N + 20 * A ^ (3:ℕ) * S *
        W ^ (2:ℕ) * O ^ (6:ℕ) * N + 20 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ) * K * N + 6 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) + 12 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K + 6 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (10:ℕ) - 12 *
        A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - 6 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) + (-32 *
        A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) + 20 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W *
        O ^ (7:ℕ) + 8 * A ^ (3:ℕ) * D * S * W ^ (4:ℕ) * O ^ (3:ℕ) * N - 2 * A ^ (3:ℕ) * D * S *
        W ^ (2:ℕ) * O ^ (5:ℕ) * N + 8 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (5:ℕ) + 8 * A ^ (3:ℕ) * D *
        W ^ (5:ℕ) * O ^ (3:ℕ) * K - 48 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) - 48 * A ^ (3:ℕ) * D
        * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 40 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) + 40 * A ^ (3:ℕ) * D * W *
        O ^ (7:ℕ) * K + 5 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (5:ℕ) + 10 * A ^ (3:ℕ) * S ^ (5:ℕ) * W *
        O ^ (3:ℕ) * K + 5 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O * K ^ (2:ℕ) - 5 * A ^ (3:ℕ) * S ^ (4:ℕ) *
        W ^ (2:ℕ) * O ^ (3:ℕ) * N - 5 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) * O * K * N + 6 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) + 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) *
        O ^ (3:ℕ) * K + 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * K ^ (2:ℕ) + 30 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W * O ^ (7:ℕ) + 60 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K + 30 * A ^ (3:ℕ)
        * S ^ (3:ℕ) * W * O ^ (3:ℕ) * K ^ (2:ℕ) - 6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ)
        * N - 6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O * K * N - 11 * A ^ (3:ℕ) * S ^ (2:ℕ) *
        W ^ (2:ℕ) * O ^ (5:ℕ) * N - 11 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * K * N +
        A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (5:ℕ) + 2 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K +
        A ^ (3:ℕ) * S * W ^ (5:ℕ) * O * K ^ (2:ℕ) - 34 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) - 68
        * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K - 34 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) *
        K ^ (2:ℕ) + 85 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) + 170 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K +
        85 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ) - A ^ (3:ℕ) * W ^ (6:ℕ) * O ^ (3:ℕ) * N -
        A ^ (3:ℕ) * W ^ (6:ℕ) * O * K * N + 5 * A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (5:ℕ) * N + 5 *
        A ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * K * N - 4 * A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (7:ℕ) * N - 4 *
        A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (5:ℕ) * K * N) * j := by
  simp only [zkLC, zkBil, zkQC, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_sub, hA, hS, hO, hjc]
  rw [zkSC_apply_zero]
  linear_combination (10 * A ^ (3:ℕ) * D * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j - 6 * A ^ (3:ℕ) * D * S *
      W ^ (3:ℕ) * O ^ (2:ℕ) + 10 * A ^ (3:ℕ) * D * S * W * O ^ (4:ℕ) * j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * D
      * W ^ (3:ℕ) * O ^ (3:ℕ) * j + A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (4:ℕ) *
      W * K - A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * N + 5 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j
      + 5 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O * K * j + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) +
      A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * K - 5 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O * N * j + 4
      * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) +
      4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * K * j ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (2:ℕ) * K - A ^ (3:ℕ) * S * W ^ (4:ℕ) * N + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j +
      A ^ (3:ℕ) * S * W ^ (3:ℕ) * O * K * j - 4 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (2:ℕ) * N *
      j ^ (2:ℕ) + 4 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (2:ℕ) * N - 5 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ)
      * j - 5 * A ^ (3:ℕ) * S * W * O ^ (3:ℕ) * K * j - A ^ (3:ℕ) * W ^ (4:ℕ) * O * N * j + 4 *
      A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * N * j - 6 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * j ^ (2:ℕ) - 6 *
      A ^ (3:ℕ) * W * O ^ (4:ℕ) * K * j ^ (2:ℕ)) * h2 + (20 * A ^ (3:ℕ) * D * S * W * O ^ (5:ℕ) * j
      - 12 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) + 20 * A ^ (3:ℕ) * D * W * O ^ (6:ℕ) * j ^ (2:ℕ)
      + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ) + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K -
      2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N + 20 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (5:ℕ) * j + 20 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j - 6 * A ^ (3:ℕ) * S *
      W ^ (3:ℕ) * O ^ (4:ℕ) - 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K - 10 * A ^ (3:ℕ) * S *
      W ^ (2:ℕ) * O ^ (3:ℕ) * N * j + 18 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) * j ^ (2:ℕ) + 4 * A ^ (3:ℕ)
      * S * W * O ^ (6:ℕ) + 18 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K * j ^ (2:ℕ) + 4 * A ^ (3:ℕ) * S *
      W * O ^ (4:ℕ) * K - 14 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) * j - 14 * A ^ (3:ℕ) * W ^ (3:ℕ) *
      O ^ (3:ℕ) * K * j - 8 * A ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N * j ^ (2:ℕ) + 6 * A ^ (3:ℕ) *
      W ^ (2:ℕ) * O ^ (4:ℕ) * N + 40 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j + 40 * A ^ (3:ℕ) * W *
      O ^ (5:ℕ) * K * j) * h1 + (-20 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + 20 *
      A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 8 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) - 8 *
      A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 36 * A ^ (3:ℕ) * D * S * W * O ^ (8:ℕ) + 36 *
      A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K + 8 * A ^ (3:ℕ) * D * W ^ (4:ℕ) * O ^ (4:ℕ) * N - 8 *
      A ^ (3:ℕ) * D * W ^ (2:ℕ) * O ^ (6:ℕ) * N + 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) + 8 *
      A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) *
      K ^ (2:ℕ) - 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) * N - 4 * A ^ (3:ℕ) * S ^ (3:ℕ)
      * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N + 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + 8 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
      O ^ (2:ℕ) * K ^ (2:ℕ) + 26 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) + 52 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 26 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) - 4 *
      A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (4:ℕ) * N - 4 * A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (2:ℕ) * K * N
      - 12 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (6:ℕ) * N - 12 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ)
      * K * N - 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) - 12 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K -
      6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) + 6 * A ^ (3:ℕ) * W * O ^ (10:ℕ) + 12 *
      A ^ (3:ℕ) * W * O ^ (8:ℕ) * K + 6 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem zk_Y3 {A B D S W O K N j : ℂ}
    (hA : starRingEnd ℂ A = A) (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W)
    (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2 = -1)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    pairing (zkLC A D S W O j) (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K N S W O j)) =
      (24 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 32 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) + 8 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 64 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) *
        O ^ (6:ℕ) - 64 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 56 * A ^ (3:ℕ) * D * S * W
        * O ^ (8:ℕ) + 56 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K + 16 * A ^ (3:ℕ) * D * W ^ (4:ℕ) *
        O ^ (4:ℕ) * N - 16 * A ^ (3:ℕ) * D * W ^ (2:ℕ) * O ^ (6:ℕ) * N - A ^ (3:ℕ) * S ^ (6:ℕ) * W *
        O ^ (4:ℕ) - 2 * A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (2:ℕ) * K - A ^ (3:ℕ) * S ^ (6:ℕ) * W *
        K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * N + 2 * A ^ (3:ℕ) *
        S ^ (5:ℕ) * W ^ (2:ℕ) * K * N - 5 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) - 7 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K - 2 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) *
        K ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * N ^ (2:ℕ) + 9 * A ^ (3:ℕ) * S ^ (4:ℕ) * W *
        O ^ (6:ℕ) + 18 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K + 9 * A ^ (3:ℕ) * S ^ (4:ℕ) * W *
        O ^ (2:ℕ) * K ^ (2:ℕ) + 4 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * N + 4 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (4:ℕ) * K * N - 22 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) *
        O ^ (4:ℕ) * N - 22 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K * N - 7 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 8 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K -
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * K ^ (2:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) *
        N ^ (2:ℕ) - 14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) - 22 * A ^ (3:ℕ) * S ^ (2:ℕ)
        * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 8 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ)
        + 13 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * N ^ (2:ℕ) + 49 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W * O ^ (8:ℕ) + 98 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 49 * A ^ (3:ℕ)
        * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S * W ^ (6:ℕ) * O ^ (2:ℕ) * N + 2
        * A ^ (3:ℕ) * S * W ^ (6:ℕ) * K * N - 6 * A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (4:ℕ) * N - 6 *
        A ^ (3:ℕ) * S * W ^ (4:ℕ) * O ^ (2:ℕ) * K * N - 40 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (6:ℕ) *
        N - 40 * A ^ (3:ℕ) * S * W ^ (2:ℕ) * O ^ (4:ℕ) * K * N - 3 * A ^ (3:ℕ) * W ^ (7:ℕ) *
        O ^ (4:ℕ) - 3 * A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (2:ℕ) * K - A ^ (3:ℕ) * W ^ (7:ℕ) * N ^ (2:ℕ) +
        9 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) + 12 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + 3 *
        A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + 5 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) *
        N ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) + 9 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) *
        K + 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) - 4 * A ^ (3:ℕ) * W ^ (3:ℕ) *
        O ^ (4:ℕ) * N ^ (2:ℕ) - 9 * A ^ (3:ℕ) * W * O ^ (10:ℕ) - 18 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K
        - 9 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) + (-24 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ)
        * O ^ (5:ℕ) + 24 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W * O ^ (7:ℕ) - 12 * A ^ (3:ℕ) * D * S *
        W ^ (2:ℕ) * O ^ (5:ℕ) * N - 12 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (3:ℕ) * K + 12 * A ^ (3:ℕ)
        * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K - 6 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (5:ℕ) - 12 * A ^ (3:ℕ)
        * S ^ (5:ℕ) * W * O ^ (3:ℕ) * K - 6 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O * K ^ (2:ℕ) + 12 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * N + 12 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) *
        O * K * N - 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) - 18 * A ^ (3:ℕ) * S ^ (3:ℕ)
        * W ^ (3:ℕ) * O ^ (3:ℕ) * K - 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * K ^ (2:ℕ) - 6 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * N ^ (2:ℕ) - 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W *
        O ^ (7:ℕ) - 24 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K - 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W
        * O ^ (3:ℕ) * K ^ (2:ℕ) + 12 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (3:ℕ) * N + 12 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (4:ℕ) * O * K * N - 6 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (5:ℕ) -
        6 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K - 6 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O *
        N ^ (2:ℕ) - 12 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) - 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) *
        O ^ (5:ℕ) * K + 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * K ^ (2:ℕ) + 12 * A ^ (3:ℕ) * S *
        W ^ (3:ℕ) * O ^ (3:ℕ) * N ^ (2:ℕ) + 18 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) + 36 * A ^ (3:ℕ) * S
        * W * O ^ (7:ℕ) * K + 18 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ)) * j := by
  rw [pairing_apply, Fin.sum_univ_four, zk_Y3p1 hS hW hO hjc hj h1, zk_Y3p2 hA hS hO hjc hj h1 h2]
  have e0 : (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K N S W O j)) 0 = 0 := rfl
  have e3 : (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K N S W O j)) 3 = 0 := rfl
  rw [e0, e3]
  ring

@[tmio M, powerlib_domain] private theorem zk_right {A B D S W O K j : ℂ}
    (hj : j ^ 2 = -1) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    zkJ A B D K S W *ᵥ zkQC A D K S W O j = (O * j) • zkQC A D K S W O j := by
  ext k
  fin_cases k <;> simp only [zkJ, zkQC, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply,
      smul_eq_mul]
  · ring
  · linear_combination (-A * W * O ^ (2:ℕ)) * hj
  · ring
  · linear_combination (1) * h2 + (O * j) * h1 + (2 * D * S * O ^ (2:ℕ) + D * O ^ (3:ℕ) * j -
      O ^ (4:ℕ) - O ^ (2:ℕ) * K) * hj

@[tmio M, powerlib_domain] private theorem zk_left {A B D S W O K j : ℂ}
    (hj : j ^ 2 = -1) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    (zkJ A B D K S W)ᵀ *ᵥ zkLC A D S W O j = (-(O * j)) • zkLC A D S W O j := by
  ext k
  fin_cases k <;> simp only [zkJ, zkLC, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply,
      smul_eq_mul, Matrix.transpose_apply]
  · linear_combination (1) * h2 + (-O * j) * h1 + (2 * D * S * O ^ (2:ℕ) - D * O ^ (3:ℕ) * j +
      S ^ (2:ℕ) * O ^ (2:ℕ) - 2 * S * O ^ (3:ℕ) * j + W ^ (2:ℕ) * O ^ (2:ℕ) + O ^ (4:ℕ) * j ^ (2:ℕ)
      - O ^ (4:ℕ) - O ^ (2:ℕ) * K) * hj
  · ring
  · ring
  · ring

@[tmio M, powerlib_domain] private theorem zk_norm {A D S W O K j : ℂ}
    (hA : starRingEnd ℂ A = A) (hD : starRingEnd ℂ D = D) (hS : starRingEnd ℂ S = S)
    (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2
        = -1)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2)) :
    star (zkLC A D S W O j) ⬝ᵥ zkQC A D K S W O j = zkCC A D K S W O j := by
  simp only [Pi.star_apply, RCLike.star_def, zkLC, zkQC, zkCC, dotProduct, Fin.sum_univ_four,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_add, map_sub, map_neg, map_pow, hA, hD, hS, hW, hO, hjc]
  linear_combination (-A * W) * h1 + (-3 * A * D * W * O ^ (2:ℕ) - 4 * A * S * W * O ^ (2:ℕ) - 2 * A
      * W * O ^ (3:ℕ) * j) * hj

@[tmio M, powerlib_domain] private theorem zk_det2 {A B D S W O K j : ℂ}
    (hj : j ^ 2 = -1) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    ((2 * O * j) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - zkJ A B D K S W).det = zkDC D K S W O j := by
  simp only [Criteria.det_fin_four, zkJ, zkDC, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.reduceEq, ↓reduceIte]
  linear_combination (1) * h2 + (2 * O * j) * h1 + (8 * D * S * O ^ (2:ℕ) + 8 * D * O ^ (3:ℕ) * j +
      4 * S ^ (2:ℕ) * O ^ (2:ℕ) + 16 * S * O ^ (3:ℕ) * j + 4 * W ^ (2:ℕ) * O ^ (2:ℕ) + 16 *
      O ^ (4:ℕ) * j ^ (2:ℕ) - 16 * O ^ (4:ℕ) - 4 * O ^ (2:ℕ) * K) * hj

@[tmio M, powerlib_domain] private theorem zk_Y1 {A B D S W O K j : ℂ}
    (hA : starRingEnd ℂ A = A) (hD : starRingEnd ℂ D = D) (hS : starRingEnd ℂ S = S)
    (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2
        = -1)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    pairing (zkLC A D S W O j) (zkTri A B K (zkQC A D K S W O j) (zkQC A D K S W O j) (zkQC A D K S
        W (-O) j)) =
      (-4 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (2:ℕ) - 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * K - 4 * A ^ (3:ℕ) * W ^ (5:ℕ) *
        O ^ (2:ℕ) - 3 * A ^ (3:ℕ) * W ^ (5:ℕ) * K + 4 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) + 3 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K) + (-4 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) - 2 *
        A ^ (3:ℕ) * S * W ^ (3:ℕ) * O * K) * j := by
  simp only [pairing_apply, zkLC, zkTri, zkQC, Fin.sum_univ_four, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul, map_add, map_sub,
      map_neg, map_pow, hA, hD, hS, hW, hO, hjc]
  linear_combination (-A ^ (3:ℕ) * W ^ (3:ℕ)) * h2 + (A ^ (3:ℕ) * W ^ (3:ℕ) * O * j) * h1 + (2 *
      A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (2:ℕ) + A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 3 *
      A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K) * hj

@[tmio M, powerlib_domain] private theorem zk_star {A D K S W O j : ℂ}
    (hA : starRingEnd ℂ A = A) (hD : starRingEnd ℂ D = D) (hK : starRingEnd ℂ K = K)
    (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O)
    (hjc : starRingEnd ℂ j = -j) :
    star (zkQC A D K S W O j) = zkQC A D K S W (-O) j := by
  ext k
  fin_cases k <;> simp only [Pi.star_apply, RCLike.star_def, zkQC, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_add, map_sub, map_pow, hA, hD, hK, hS, hW, hO, hjc] <;> ring

@[tmio M, powerlib_domain] private theorem zk_det {A B D K S W : ℂ} :
    (zkJ A B D K S W).det = A * B * W - K * (S ^ 2 + W ^ 2) := by
  simp only [Criteria.det_fin_four, zkJ, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The combination `Z` of the projection formula. -/
private def zkZ (cr ci dr di y1r y1i y2r y2i y3r y3i b : ℝ) : ℝ :=
  (b * (dr * y1r - di * y1i) - 2 * (dr * y2r - di * y2i) + b * y3r) * (cr * dr - ci * di) +
    (b * (dr * y1i + di * y1r) - 2 * (dr * y2i + di * y2r) + b * y3i) * (cr * di + ci * dr)

/-- The real part of the combination of the projection formula. -/
@[tmio M, powerlib_domain] private theorem zk_re (cr ci dr di y1r y1i y2r y2i y3r y3i b : ℝ)
    (hb : b ≠ 0) (hc : cr ^ 2 + ci ^ 2 ≠ 0) (hd : dr ^ 2 + di ^ 2 ≠ 0) :
    (((cr : ℂ) + ci * I)⁻¹ * ((y1r : ℂ) + y1i * I) -
        2 * ((b : ℂ)⁻¹ * (((cr : ℂ) + ci * I)⁻¹ * ((y2r : ℂ) + y2i * I))) +
        ((dr : ℂ) + di * I)⁻¹ * (((cr : ℂ) + ci * I)⁻¹ * ((y3r : ℂ) + y3i * I))).re =
      zkZ cr ci dr di y1r y1i y2r y2i y3r y3i b /
        (b * ((cr ^ 2 + ci ^ 2) * (dr ^ 2 + di ^ 2))) := by
  unfold zkZ
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.inv_re, Complex.inv_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul,
      sub_zero, zero_add, add_zero, mul_one, neg_zero, zero_div]
  have hc' : cr * cr + ci * ci ≠ 0 := by rw [← sq, ← sq]; exact hc
  have hd' : dr * dr + di * di ≠ 0 := by rw [← sq, ← sq]; exact hd
  have hb' : b * b + 0 * 0 ≠ 0 := by simpa using mul_ne_zero hb hb
  field_simp
  ring

/-- `Z` is linear in the pairings: the split by the degree in `ν`. -/
@[tmio M, powerlib_domain] private theorem zkZ_split
    (cr ci dr di y1r y1i u0 u1 u2 v0 v1 v2 x0 x1 x2 z0 z1 z2 ν b : ℝ) :
    zkZ cr ci dr di y1r y1i (u0 + ν * u1 + ν ^ 2 * u2) (v0 + ν * v1 + ν ^ 2 * v2)
        (x0 + ν * x1 + ν ^ 2 * x2) (z0 + ν * z1 + ν ^ 2 * z2) b =
      zkZ cr ci dr di y1r y1i u0 v0 x0 z0 b + ν * zkZ cr ci dr di 0 0 u1 v1 x1 z1 b +
        ν ^ 2 * zkZ cr ci dr di 0 0 u2 v2 x2 z2 b := by
  unfold zkZ
  ring

/-- The key identity of the closed form, the part of degree 0 in `ν`. -/
@[tmio M, powerlib_domain] private theorem zk_key0 {a b d κ σ w ω : ℝ}
    (h1 : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * (κ + ω ^ 2))
    (h2 : a * b * w = κ * (σ ^ 2 + w ^ 2) + ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d - κ)) :
    zkZ (2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ)) (-4 * a * d * σ * w * ω - 2 * a *
      σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w * ω ^ (3:ℕ) + 2 * a * w * ω * κ) (-6 * d
      * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 * ω ^ (4:ℕ) + 3 *
      ω ^ (2:ℕ) * κ) (-6 * d * ω ^ (3:ℕ) - 12 * σ * ω ^ (3:ℕ)) (-4 * a ^ (3:ℕ) * d * σ * w ^ (3:ℕ) *
      ω ^ (2:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) - 3 * a ^ (3:ℕ) * σ ^ (2:ℕ) *
      w ^ (3:ℕ) * κ - 4 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (5:ℕ) * κ + 4 *
      a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) + 3 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ) (-4 * a ^ (3:ℕ)
      * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω * κ) (a ^ (3:ℕ) * σ ^ (6:ℕ) *
      w * ω ^ (4:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω ^ (2:ℕ) * κ + a ^ (3:ℕ) * σ ^ (6:ℕ) * w *
      κ ^ (2:ℕ) + a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) + 3 * a ^ (3:ℕ) * σ ^ (4:ℕ) *
      w ^ (3:ℕ) * ω ^ (2:ℕ) * κ + 2 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * κ ^ (2:ℕ) + 3 * a ^ (3:ℕ)
      * σ ^ (4:ℕ) * w * ω ^ (6:ℕ) + 6 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (4:ℕ) * κ + 3 * a ^ (3:ℕ) *
      σ ^ (4:ℕ) * w * ω ^ (2:ℕ) * κ ^ (2:ℕ) - a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) +
      a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * κ ^ (2:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
      ω ^ (6:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 3 * a ^ (3:ℕ) * σ ^ (2:ℕ)
      * w * ω ^ (8:ℕ) + 6 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (6:ℕ) * κ + 3 * a ^ (3:ℕ) * σ ^ (2:ℕ) *
      w * ω ^ (4:ℕ) * κ ^ (2:ℕ) - a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) - a ^ (3:ℕ) * w ^ (7:ℕ) *
      ω ^ (2:ℕ) * κ + 3 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 4 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ)
      * κ + a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) -
      5 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 2 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ)
      + a ^ (3:ℕ) * w * ω ^ (10:ℕ) + 2 * a ^ (3:ℕ) * w * ω ^ (8:ℕ) * κ + a ^ (3:ℕ) * w * ω ^ (6:ℕ) *
      κ ^ (2:ℕ)) (8 * a ^ (3:ℕ) * d * w ^ (5:ℕ) * ω ^ (5:ℕ) + 4 * a ^ (3:ℕ) * d * w ^ (5:ℕ) *
      ω ^ (3:ℕ) * κ - 16 * a ^ (3:ℕ) * d * w ^ (3:ℕ) * ω ^ (7:ℕ) - 12 * a ^ (3:ℕ) * d * w ^ (3:ℕ) *
      ω ^ (5:ℕ) * κ + 8 * a ^ (3:ℕ) * d * w * ω ^ (9:ℕ) + 8 * a ^ (3:ℕ) * d * w * ω ^ (7:ℕ) * κ + 2
      * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (5:ℕ) + 4 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (3:ℕ) * κ + 2 *
      a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω * κ ^ (2:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (3:ℕ)
      * κ + 2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω * κ ^ (2:ℕ) + 8 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w *
      ω ^ (7:ℕ) + 16 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (5:ℕ) * κ + 8 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w *
      ω ^ (3:ℕ) * κ ^ (2:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (5:ℕ) - 2 * a ^ (3:ℕ) * σ *
      w ^ (5:ℕ) * ω ^ (3:ℕ) * κ - 12 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (7:ℕ) - 18 * a ^ (3:ℕ) * σ *
      w ^ (3:ℕ) * ω ^ (5:ℕ) * κ - 6 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ ^ (2:ℕ) + 14 *
      a ^ (3:ℕ) * σ * w * ω ^ (9:ℕ) + 28 * a ^ (3:ℕ) * σ * w * ω ^ (7:ℕ) * κ + 14 * a ^ (3:ℕ) * σ *
      w * ω ^ (5:ℕ) * κ ^ (2:ℕ)) (24 * a ^ (3:ℕ) * d ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) - 32 *
      a ^ (3:ℕ) * d ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) + 8 * a ^ (3:ℕ) * d ^ (2:ℕ) * w * ω ^ (8:ℕ) - 64
      * a ^ (3:ℕ) * d * σ * w ^ (3:ℕ) * ω ^ (6:ℕ) - 64 * a ^ (3:ℕ) * d * σ * w ^ (3:ℕ) * ω ^ (4:ℕ) *
      κ + 56 * a ^ (3:ℕ) * d * σ * w * ω ^ (8:ℕ) + 56 * a ^ (3:ℕ) * d * σ * w * ω ^ (6:ℕ) * κ -
      a ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω ^ (4:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω ^ (2:ℕ) * κ -
      a ^ (3:ℕ) * σ ^ (6:ℕ) * w * κ ^ (2:ℕ) - 5 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) - 7
      * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ - 2 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) *
      κ ^ (2:ℕ) + 9 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (6:ℕ) + 18 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w *
      ω ^ (4:ℕ) * κ + 9 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (2:ℕ) * κ ^ (2:ℕ) - 7 * a ^ (3:ℕ) *
      σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) - 8 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ -
      a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * κ ^ (2:ℕ) - 14 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
      ω ^ (6:ℕ) - 22 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ - 8 * a ^ (3:ℕ) * σ ^ (2:ℕ)
      * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) + 49 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (8:ℕ) + 98 *
      a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (6:ℕ) * κ + 49 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) - 3 * a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (2:ℕ) * κ
      + 9 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 12 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ + 3 *
      a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) + 3 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 9 *
      a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ + 6 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 9
      * a ^ (3:ℕ) * w * ω ^ (10:ℕ) - 18 * a ^ (3:ℕ) * w * ω ^ (8:ℕ) * κ - 9 * a ^ (3:ℕ) * w *
      ω ^ (6:ℕ) * κ ^ (2:ℕ)) (-24 * a ^ (3:ℕ) * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ) + 24 *
      a ^ (3:ℕ) * d ^ (2:ℕ) * σ * w * ω ^ (7:ℕ) - 12 * a ^ (3:ℕ) * d * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ +
      12 * a ^ (3:ℕ) * d * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ - 6 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (5:ℕ) -
      12 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (3:ℕ) * κ - 6 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω * κ ^ (2:ℕ)
      - 12 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (5:ℕ) - 18 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ)
      * ω ^ (3:ℕ) * κ - 6 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω * κ ^ (2:ℕ) - 12 * a ^ (3:ℕ) *
      σ ^ (3:ℕ) * w * ω ^ (7:ℕ) - 24 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (5:ℕ) * κ - 12 * a ^ (3:ℕ) *
      σ ^ (3:ℕ) * w * ω ^ (3:ℕ) * κ ^ (2:ℕ) - 6 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (5:ℕ) - 6 *
      a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ - 12 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (7:ℕ) - 6 *
      a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ + 6 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) *
      κ ^ (2:ℕ) + 18 * a ^ (3:ℕ) * σ * w * ω ^ (9:ℕ) + 36 * a ^ (3:ℕ) * σ * w * ω ^ (7:ℕ) * κ + 18 *
      a ^ (3:ℕ) * σ * w * ω ^ (5:ℕ) * κ ^ (2:ℕ)) (a * b * w - κ * (σ ^ 2 + w ^ 2)) * (2 * σ + d) ^ 4
      = 72 * a ^ 4 * d * σ * w ^ 2 * ω ^ 6 * (-4 * ω ^ 2 * (a * b * w - κ * (σ ^ 2 + w ^ 2)) *
      bautinFormQ d σ w κ + κ * σ * (κ * σ + 2 * (d + σ) * ω ^ 2) * bautinCorr d σ w κ) := by
  unfold zkZ bautinFormQ bautinCorr
  linear_combination (-576 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 576 *
      a ^ (4:ℕ) * d ^ (8:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 576 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ *
      w ^ (6:ℕ) * ω ^ (8:ℕ) + 1152 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) - 576 *
      a ^ (4:ℕ) * d ^ (8:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) + 1440 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (6:ℕ)
      * w ^ (2:ℕ) * ω ^ (8:ℕ) - 4608 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) +
      72 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 5184 * a ^ (4:ℕ) *
      d ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 288 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 7632 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) -
      504 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 18432 * a ^ (4:ℕ) *
      d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 3168 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ - 10512 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ)
      - 2592 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 432 * a ^ (4:ℕ) *
      d ^ (7:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) + 1584 * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) +
      360 * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ - 1584 * a ^ (4:ℕ) * d ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (12:ℕ) - 504 * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 432 *
      a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 144 * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (2:ℕ) *
      ω ^ (12:ℕ) * κ + 6804 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 216 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ - 108 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 19332 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) + 180 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ -
      72 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 18036 * a ^ (4:ℕ)
      * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 9864 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 540 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 38916 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 4608 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 36 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 110952 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) + 30960 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ
      + 288 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 69732 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 28440 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 684 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
      ω ^ (8:ℕ) * κ ^ (2:ℕ) - 3564 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (8:ℕ) * ω ^ (8:ℕ) - 396 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 19476 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ *
      w ^ (6:ℕ) * ω ^ (10:ℕ) + 7992 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 396 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 25380 * a ^ (4:ℕ) * d ^ (6:ℕ)
      * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) - 15300 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ
      - 2088 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 8892 * a ^ (4:ℕ) *
      d ^ (6:ℕ) * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) + 6696 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (2:ℕ) *
      ω ^ (12:ℕ) * κ + 1260 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 3690
      * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 1836 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ - 918 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) *
      ω ^ (4:ℕ) * κ ^ (2:ℕ) - 55908 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) -
      1764 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 666 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 28728 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 48834 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) *
      ω ^ (8:ℕ) * κ - 4428 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) +
      126 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 102168 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 17100 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 270 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) *
      ω ^ (4:ℕ) * κ ^ (2:ℕ) + 338724 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) +
      137286 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 3816 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 108 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 233460 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (12:ℕ) - 129222 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
      κ + 3168 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 450 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 14940 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 3420 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) *
      w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 18 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) + 95040 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 49626 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 3492 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 18 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) *
      w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 149868 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) *
      ω ^ (12:ℕ) - 116568 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 20466 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 126 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 60984 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 58482 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
      ω ^ (12:ℕ) * κ + 14076 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
      κ ^ (2:ℕ) + 522 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 18 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) - 72 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (10:ℕ) *
      ω ^ (6:ℕ) * κ + 468 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 882 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 144 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 2088 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 3330 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 1098 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) - 72 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 2124 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 3654 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) *
      ω ^ (12:ℕ) * κ + 1764 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 234 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 486 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (16:ℕ) - 1134 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ - 810 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 162 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 13392 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) *
      ω ^ (8:ℕ) - 6048 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ - 3024 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 64224 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 9792 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 2448 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) + 15300 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 61236 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 13716 * a ^ (4:ℕ) * d ^ (4:ℕ)
      * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 1044 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) *
      w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 111168 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) *
      ω ^ (8:ℕ) - 33120 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 720 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 576036 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 380484 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 19656 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ)
      * κ ^ (2:ℕ) + 936 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) -
      437724 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 310608 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 29304 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ)
      * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 3744 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) *
      ω ^ (6:ℕ) * κ ^ (3:ℕ) - 36 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) *
      κ ^ (4:ℕ) - 21024 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 11520 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 144 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 235260 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) *
      w ^ (6:ℕ) * ω ^ (10:ℕ) + 165492 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) *
      κ + 12636 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 108 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 441288 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 409968 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 86436 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) - 1584 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) -
      36 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (4:ℕ) + 204588 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 230652 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 67500 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ)
      * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 1044 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) *
      κ ^ (3:ℕ) - 72 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 2448
      * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (10:ℕ) * ω ^ (8:ℕ) - 576 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ *
      w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 3996 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (8:ℕ) * ω ^ (10:ℕ) + 11772
      * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 1152 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ *
      w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 17388 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (12:ℕ)
      - 27504 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 7452 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 576 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ *
      w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 16164 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (14:ℕ)
      + 27468 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 12996 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 1044 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 3780 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (2:ℕ) * ω ^ (16:ℕ)
      - 8424 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ - 5400 * a ^ (4:ℕ) * d ^ (4:ℕ)
      * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 648 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (2:ℕ) *
      ω ^ (10:ℕ) * κ ^ (3:ℕ) - 180 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) -
      19440 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 9504 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ - 4752 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (10:ℕ)
      * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 26784 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) - 19296 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 4464 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 11808 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 22464 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 19008 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ)
      * κ ^ (2:ℕ) + 3312 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) -
      61056 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 36000 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 720 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) *
      w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 554112 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) *
      ω ^ (10:ℕ) + 468864 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 50688 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 3168 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 465984 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 414864 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) *
      ω ^ (10:ℕ) * κ - 19728 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ)
      + 11952 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 288 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (4:ℕ) - 34272 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 18720 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) *
      w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 432 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) + 309600 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 191232 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 24768 * a ^ (4:ℕ) * d ^ (3:ℕ)
      * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 144 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) *
      w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 709344 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) *
      ω ^ (12:ℕ) - 782784 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 291888
      * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 7632 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 288 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (4:ℕ) + 378144 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (14:ℕ) + 496656 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) *
      κ + 178560 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 23472 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 576 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 1008 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) - 1728 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) *
      ω ^ (6:ℕ) * κ + 13248 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 14400 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 3456 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 55584 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
      w ^ (6:ℕ) * ω ^ (12:ℕ) - 86832 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) *
      κ - 46368 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 1728 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 44352 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 73584 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
      w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 33408 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) *
      ω ^ (10:ℕ) * κ ^ (2:ℕ) - 4752 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) *
      κ ^ (3:ℕ) - 10800 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) - 22032 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ - 10800 * a ^ (4:ℕ) * d ^ (3:ℕ)
      * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) + 1296 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
      w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 288 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
      ω ^ (8:ℕ) * κ ^ (4:ℕ) - 9216 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) -
      6912 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ - 3456 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 6336 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 16704 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) *
      ω ^ (6:ℕ) * κ - 4032 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) -
      16992 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 1728 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 9504 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) *
      w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 4896 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) *
      ω ^ (4:ℕ) * κ ^ (3:ℕ) - 21312 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) -
      21888 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 291168 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 289728 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 68544 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ)
      * κ ^ (2:ℕ) + 5184 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) -
      263520 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 288576 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 73152 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ)
      * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 17856 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) *
      ω ^ (6:ℕ) * κ ^ (3:ℕ) - 864 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) *
      κ ^ (4:ℕ) - 23616 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 14400 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 576 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 204768 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) *
      w ^ (6:ℕ) * ω ^ (10:ℕ) + 159552 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) *
      κ + 29664 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 288 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 627840 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 849600 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 333216 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) * κ ^ (2:ℕ) - 17856 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) - 864 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (4:ℕ) +
      393696 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 612576 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 275040 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 23328 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 1728 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) *
      ω ^ (6:ℕ) * κ ^ (4:ℕ) + 576 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) -
      2304 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 21024 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 33984 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
      w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 4608 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 83232 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 127296 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 25632 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 2304 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
      w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 48096 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) *
      ω ^ (14:ℕ) + 74592 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 29664 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 28512 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 12960 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) - 20736 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
      ω ^ (14:ℕ) * κ + 10368 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
      κ ^ (3:ℕ) + 12672 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) -
      1440 * a ^ (4:ℕ) * d * σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 1728 * a ^ (4:ℕ) * d * σ ^ (12:ℕ)
      * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ - 864 * a ^ (4:ℕ) * d * σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) - 2880 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 5184 * a ^ (4:ℕ) * d *
      σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 1440 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) *
      ω ^ (4:ℕ) * κ ^ (2:ℕ) - 4608 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) + 864 *
      a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ + 1728 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) *
      w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 3168 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ)
      * κ ^ (3:ℕ) - 4608 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 6336 * a ^ (4:ℕ) * d
      * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ - 288 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) *
      ω ^ (4:ℕ) * κ ^ (2:ℕ) + 75456 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 104544 *
      a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 44928 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 4032 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) *
      κ ^ (3:ℕ) - 61632 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 76896 * a ^ (4:ℕ) * d
      * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 23040 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) *
      ω ^ (8:ℕ) * κ ^ (2:ℕ) + 11808 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ)
      - 1152 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (4:ℕ) - 6336 * a ^ (4:ℕ) * d
      * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 4032 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ)
      * κ + 288 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 58752 * a ^ (4:ℕ)
      * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 83232 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) *
      ω ^ (8:ℕ) * κ + 22464 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 864 *
      a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 294336 * a ^ (4:ℕ) * d *
      σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 510336 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) *
      ω ^ (10:ℕ) * κ - 213408 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) -
      20448 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 1152 * a ^ (4:ℕ) * d *
      σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (4:ℕ) + 218880 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ)
      * ω ^ (14:ℕ) + 413856 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 233280 *
      a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 50400 * a ^ (4:ℕ) * d *
      σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 2304 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) *
      ω ^ (6:ℕ) * κ ^ (4:ℕ) - 3168 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) - 1152 *
      a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 15552 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) *
      w ^ (8:ℕ) * ω ^ (10:ℕ) + 11808 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 2304
      * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 55296 * a ^ (4:ℕ) * d *
      σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 80928 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) *
      ω ^ (10:ℕ) * κ - 30240 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 1152
      * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 7488 * a ^ (4:ℕ) * d *
      σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 2016 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ)
      * κ - 7488 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 1440 * a ^ (4:ℕ)
      * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 4320 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (16:ℕ) + 2592 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 21600
      * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) + 18144 * a ^ (4:ℕ) * d *
      σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 3456 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ)
      * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) + 1728 *
      a ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ + 1728 * a ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ)
      * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) +
      5184 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 14400 * a ^ (4:ℕ) * σ ^ (9:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 10368 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ)
      + 1152 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) + 576 * a ^ (4:ℕ) *
      σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) + 4608 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ
      + 6912 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 2304 * a ^ (4:ℕ) *
      σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) *
      ω ^ (4:ℕ) * κ ^ (4:ℕ) + 8640 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 16704 *
      a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 8640 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) -
      65664 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 140544 * a ^ (4:ℕ) * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 83520 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ)
      - 9216 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 576 * a ^ (4:ℕ) *
      σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (4:ℕ) + 52416 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) *
      ω ^ (14:ℕ) + 121536 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 84672 * a ^ (4:ℕ) *
      σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 14400 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) *
      ω ^ (8:ℕ) * κ ^ (3:ℕ) - 1152 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) +
      4032 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 4032 * a ^ (4:ℕ) * σ ^ (5:ℕ) *
      w ^ (8:ℕ) * ω ^ (8:ℕ) * κ - 10944 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 13824 *
      a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 2880 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ)
      * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 13248 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 28224 *
      a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ - 17856 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ)
      * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 2880 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) +
      1728 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 10368 * a ^ (4:ℕ) * σ ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 17280 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) *
      κ ^ (2:ℕ) + 10368 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 1728 *
      a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ)) * h2 + (-1152 * a ^ (4:ℕ) *
      d ^ (8:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 1152 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ ^ (2:ℕ) *
      w ^ (2:ℕ) * ω ^ (12:ℕ) + 2880 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) -
      1440 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 12672 * a ^ (4:ℕ) *
      d ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 720 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (3:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 13824 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ)
      - 2016 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 1440 * a ^ (4:ℕ) *
      d ^ (7:ℕ) * σ * w ^ (6:ℕ) * ω ^ (10:ℕ) + 5760 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (4:ℕ) *
      ω ^ (12:ℕ) + 2448 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 3744 * a ^ (4:ℕ)
      * d ^ (7:ℕ) * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) - 3168 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (2:ℕ) *
      ω ^ (12:ℕ) * κ + 15480 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 5040 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 504 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 57456 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) - 1296 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ
      - 504 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 63360 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 19008 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 2304 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ)
      * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 11160 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) +
      1728 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 56880 * a ^ (4:ℕ) *
      d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 22680 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 288 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) *
      κ ^ (2:ℕ) - 36792 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) - 26928 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 2664 * a ^ (4:ℕ) * d ^ (6:ℕ)
      * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 432 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (8:ℕ) *
      ω ^ (10:ℕ) + 2880 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) + 1512 * a ^ (4:ℕ) *
      d ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 5328 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ)
      - 5544 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ - 1080 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 2880 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) +
      4320 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 1440 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) + 18072 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) *
      ω ^ (10:ℕ) - 11664 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 72 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 143280 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 18540 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ - 720 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) + 137304 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 66456 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 1512 * a ^ (4:ℕ) * d ^ (5:ℕ)
      * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 864 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 38664 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) *
      ω ^ (10:ℕ) + 3960 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 504 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 233280 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 78768 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 6048 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) -
      161928 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) - 103320 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 21600 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ)
      * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 1440 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
      ω ^ (8:ℕ) * κ ^ (3:ℕ) - 1728 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (8:ℕ) * ω ^ (10:ℕ) + 468 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 18504 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ *
      w ^ (6:ℕ) * ω ^ (12:ℕ) + 7560 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 936 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 29376 * a ^ (4:ℕ) * d ^ (5:ℕ)
      * σ * w ^ (4:ℕ) * ω ^ (14:ℕ) - 31068 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ
      - 4680 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 468 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 11160 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ *
      w ^ (2:ℕ) * ω ^ (16:ℕ) + 17712 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 5400
      * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 1152 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 9162 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (8:ℕ)
      * w ^ (2:ℕ) * ω ^ (10:ℕ) - 28116 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) *
      κ + 1206 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 172476 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 68904 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ - 6822 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 147960 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) -
      64044 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 3600 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 3708 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 52200 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) *
      w ^ (6:ℕ) * ω ^ (10:ℕ) + 20376 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ
      - 1134 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 536724 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 194256 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 7812 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ)
      * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 792 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) - 405108 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) - 230472 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 74466 * a ^ (4:ℕ) * d ^ (4:ℕ)
      * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 2412 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 594 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
      ω ^ (6:ℕ) * κ ^ (4:ℕ) + 5436 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) +
      8280 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ - 18 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 43488 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) + 19044 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) *
      ω ^ (10:ℕ) * κ + 432 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) +
      36 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 29268 * a ^ (4:ℕ)
      * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 24552 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) *
      w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 16542 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) *
      ω ^ (10:ℕ) * κ ^ (2:ℕ) + 7272 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) *
      κ ^ (3:ℕ) - 18 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) - 10296
      * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) - 2772 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ - 2520 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ)
      * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 10188 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ)
      * κ ^ (3:ℕ) + 432 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) +
      306 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (10:ℕ) + 108 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      w ^ (10:ℕ) * ω ^ (8:ℕ) * κ - 3708 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ) - 2520 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 324 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (8:ℕ) *
      ω ^ (8:ℕ) * κ ^ (2:ℕ) + 15984 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ) + 16488 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) * κ + 4284 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ)
      * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 324 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) -
      27396 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) - 38952 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      w ^ (4:ℕ) * ω ^ (14:ℕ) * κ - 15984 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) *
      κ ^ (2:ℕ) - 2232 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 108 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 14814 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (18:ℕ) + 27900 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) * κ + 16128 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ ^ (2:ℕ) + 3204 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) + 162 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
      κ ^ (4:ℕ) - 27216 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 38592 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 2736 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 100224 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) - 85824 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ
      - 13680 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 67464 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 5400 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 31464 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ)
      * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 6768 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) - 34272 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 50976 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 5040 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 723384 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) *
      w ^ (4:ℕ) * ω ^ (12:ℕ) + 273096 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) *
      κ + 56160 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 12240 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 604728 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) - 372960 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 37296 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) *
      ω ^ (10:ℕ) * κ ^ (2:ℕ) + 72 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) *
      κ ^ (3:ℕ) + 4392 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) +
      29952 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 18432 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 2160 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) *
      w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 33336 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) *
      ω ^ (12:ℕ) - 6696 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 14760 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 4032 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 70416 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 86832 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) *
      ω ^ (12:ℕ) * κ + 55728 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) *
      κ ^ (2:ℕ) + 9864 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) +
      1800 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) - 84888 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) - 86112 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ - 43056 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ)
      * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 43056 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ)
      * κ ^ (3:ℕ) - 432 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) +
      216 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (5:ℕ) + 5040 * a ^ (4:ℕ)
      * d ^ (3:ℕ) * σ * w ^ (10:ℕ) * ω ^ (10:ℕ) + 864 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (10:ℕ) *
      ω ^ (8:ℕ) * κ - 29304 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (8:ℕ) * ω ^ (12:ℕ) - 17928 * a ^ (4:ℕ)
      * d ^ (3:ℕ) * σ * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 2592 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (8:ℕ) *
      ω ^ (8:ℕ) * κ ^ (2:ℕ) + 126504 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (14:ℕ) + 127152 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (12:ℕ) * κ + 30528 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ *
      w ^ (6:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 2592 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ)
      * κ ^ (3:ℕ) - 218232 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (16:ℕ) - 311472 * a ^ (4:ℕ)
      * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (14:ℕ) * κ - 130320 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ)
      * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 19800 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) *
      κ ^ (3:ℕ) - 864 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 115992 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (18:ℕ) + 215928 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ *
      w ^ (2:ℕ) * ω ^ (16:ℕ) * κ + 122616 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) *
      κ ^ (2:ℕ) + 24840 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) + 2160 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (4:ℕ) - 14544 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 22464 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ)
      * ω ^ (8:ℕ) * κ - 4896 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 33120 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 41760 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 1728 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 2304 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) *
      w ^ (2:ℕ) * ω ^ (12:ℕ) - 720 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ
      + 37296 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 7920 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 6912 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 30240 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) *
      w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 16992 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ)
      * κ ^ (2:ℕ) + 559584 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 294192 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 56160 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 22176 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 507024 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) *
      ω ^ (14:ℕ) - 389664 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ - 42336 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 16704 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 3456 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 38880 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) *
      w ^ (8:ℕ) * ω ^ (10:ℕ) + 10656 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ
      + 1152 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 29376 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 34992 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 44208 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ)
      * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 1872 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) + 95616 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 155520 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 109296 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 4896 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 4032 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) - 55584 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
      ω ^ (16:ℕ) - 16560 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 9216 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 11232 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 1584 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) - 1008 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) *
      w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (5:ℕ) + 8784 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) *
      ω ^ (10:ℕ) + 2592 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) * κ - 80928 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ) - 62640 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 7776 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ)
      * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 378576 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ)
      + 387360 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) * κ + 91152 * a ^ (4:ℕ)
      * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 7776 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 646848 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) *
      w ^ (4:ℕ) * ω ^ (16:ℕ) - 916272 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) *
      κ - 371232 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 49680 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 2592 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 340416 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (18:ℕ) + 631008 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
      ω ^ (16:ℕ) * κ + 363168 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) *
      κ ^ (2:ℕ) + 84960 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) +
      12384 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (4:ℕ) - 1728 *
      a ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 3456 * a ^ (4:ℕ) * d * σ ^ (11:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 1152 * a ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 9216 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 8640 * a ^ (4:ℕ) * d *
      σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 8064 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) - 4608 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 4320 *
      a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 11232 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 7776 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) - 2304 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 8064 * a ^ (4:ℕ) * d *
      σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 5760 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 218880 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 192672 *
      a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 24192 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 3456 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) - 177408 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) - 148320 * a ^ (4:ℕ) *
      d * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ - 4032 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) *
      ω ^ (10:ℕ) * κ ^ (2:ℕ) - 6624 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ)
      - 6624 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 16128 * a ^ (4:ℕ) * d
      * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 576 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ)
      * κ - 3456 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 61056 * a ^ (4:ℕ)
      * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 11808 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) *
      ω ^ (10:ℕ) * κ - 29664 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 11232
      * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 92160 * a ^ (4:ℕ) * d *
      σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 51264 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) *
      ω ^ (12:ℕ) * κ + 28224 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 4320
      * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 6624 * a ^ (4:ℕ) * d *
      σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 127008 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ)
      * ω ^ (16:ℕ) + 270720 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 171360 *
      a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) + 39168 * a ^ (4:ℕ) * d *
      σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 3456 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ)
      * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 10944 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (10:ℕ) + 3456 *
      a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) * κ - 107136 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) *
      w ^ (8:ℕ) * ω ^ (12:ℕ) - 70560 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ -
      10368 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 497664 * a ^ (4:ℕ) * d
      * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ) + 489312 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) *
      ω ^ (12:ℕ) * κ + 127872 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) +
      10368 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 845280 * a ^ (4:ℕ) * d
      * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) - 1194048 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) *
      ω ^ (14:ℕ) * κ - 507168 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) -
      78048 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 3456 * a ^ (4:ℕ) * d
      * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 443808 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) *
      w ^ (2:ℕ) * ω ^ (18:ℕ) + 825696 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) * κ +
      487296 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ ^ (2:ℕ) + 115200 * a ^ (4:ℕ) *
      d * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) + 9792 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) *
      w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (4:ℕ) + 288 * a ^ (4:ℕ) * σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) +
      576 * a ^ (4:ℕ) * σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ + 288 * a ^ (4:ℕ) * σ ^ (12:ℕ) *
      w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 1728 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) -
      2304 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 864 * a ^ (4:ℕ) * σ ^ (10:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 5760 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) +
      9216 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 2880 * a ^ (4:ℕ) * σ ^ (10:ℕ) *
      w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) - 2304 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 4608 * a ^ (4:ℕ) *
      σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 864 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) + 21312 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 30528 * a ^ (4:ℕ) *
      σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 5184 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) - 1152 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 10944 *
      a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 38016 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) *
      ω ^ (12:ℕ) * κ + 30816 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 4032 *
      a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 288 * a ^ (4:ℕ) * σ ^ (8:ℕ) *
      w ^ (2:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 1728 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) +
      288 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 43776 * a ^ (4:ℕ) *
      σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) + 24192 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) *
      κ - 2880 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 576 * a ^ (4:ℕ) *
      σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 134208 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) *
      ω ^ (14:ℕ) - 155520 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ - 38304 * a ^ (4:ℕ) *
      σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 1152 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) * κ ^ (3:ℕ) + 288 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) +
      134784 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 253440 * a ^ (4:ℕ) * σ ^ (6:ℕ) *
      w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 142848 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) *
      κ ^ (2:ℕ) + 25920 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 1728 *
      a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 2016 * a ^ (4:ℕ) * σ ^ (4:ℕ) *
      w ^ (10:ℕ) * ω ^ (10:ℕ) + 1728 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) * κ - 45504 *
      a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ) - 33984 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) *
      ω ^ (10:ℕ) * κ - 5184 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 237312 *
      a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ) + 243072 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) *
      ω ^ (12:ℕ) * κ + 66816 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 5184 *
      a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 410688 * a ^ (4:ℕ) * σ ^ (4:ℕ) *
      w ^ (4:ℕ) * ω ^ (16:ℕ) - 591552 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) * κ - 255744
      * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 39744 * a ^ (4:ℕ) * σ ^ (4:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 1728 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) *
      κ ^ (4:ℕ) + 216864 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (18:ℕ) + 408384 * a ^ (4:ℕ) *
      σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) * κ + 244800 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
      ω ^ (14:ℕ) * κ ^ (2:ℕ) + 58176 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) +
      4896 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (4:ℕ)) * h1

/-- The key identity of the closed form, the part of degree 1 in `ν`. -/
@[tmio M, powerlib_domain] private theorem zk_key1 {a b d κ σ w ω : ℝ}
    (h1 : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * (κ + ω ^ 2))
    (h2 : a * b * w = κ * (σ ^ 2 + w ^ 2) + ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d - κ)) :
    zkZ (2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ)) (-4 * a * d * σ * w * ω - 2 * a *
      σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w * ω ^ (3:ℕ) + 2 * a * w * ω * κ) (-6 * d
      * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 * ω ^ (4:ℕ) + 3 *
      ω ^ (2:ℕ) * κ) (-6 * d * ω ^ (3:ℕ) - 12 * σ * ω ^ (3:ℕ)) 0 0 (-2 * a ^ (3:ℕ) * σ ^ (5:ℕ) *
      w ^ (2:ℕ) * ω ^ (2:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * κ - 4 * a ^ (3:ℕ) * σ ^ (3:ℕ)
      * w ^ (4:ℕ) * ω ^ (2:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ - 2 * a ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) * κ - 2
      * a ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (2:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (6:ℕ) * κ - 2 * a ^ (3:ℕ) *
      σ * w ^ (4:ℕ) * ω ^ (4:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (2:ℕ) * κ) (-4 * a ^ (3:ℕ) * d
      * σ * w ^ (2:ℕ) * ω ^ (5:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (3:ℕ) - 4 *
      a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω * κ - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (3:ℕ)
      - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω * κ - 8 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
      ω ^ (5:ℕ) - 8 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (3:ℕ) * κ) (16 * a ^ (3:ℕ) * d *
      w ^ (4:ℕ) * ω ^ (4:ℕ) - 16 * a ^ (3:ℕ) * d * w ^ (2:ℕ) * ω ^ (6:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (5:ℕ)
      * w ^ (2:ℕ) * ω ^ (2:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * κ + 4 * a ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ) + 4 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ - 22 * a ^ (3:ℕ)
      * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) - 22 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) * κ +
      2 * a ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (2:ℕ) + 2 * a ^ (3:ℕ) * σ * w ^ (6:ℕ) * κ - 6 * a ^ (3:ℕ)
      * σ * w ^ (4:ℕ) * ω ^ (4:ℕ) - 6 * a ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (2:ℕ) * κ - 40 * a ^ (3:ℕ) *
      σ * w ^ (2:ℕ) * ω ^ (6:ℕ) - 40 * a ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ) (-12 * a ^ (3:ℕ) *
      d * σ * w ^ (2:ℕ) * ω ^ (5:ℕ) + 12 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (3:ℕ) + 12 *
      a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω * κ + 12 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (3:ℕ)
      + 12 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω * κ) (a * b * w - κ * (σ ^ 2 + w ^ 2)) * (2 * σ +
      d) ^ 4 = 72 * a ^ 4 * d * σ * w ^ 2 * ω ^ 6 * (-(w * (2 * κ * σ + 2 * (d + σ) * ω ^ 2)) *
      bautinCorr d σ w κ) := by
  unfold zkZ bautinCorr
  linear_combination (-288 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) - 576 *
      a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (5:ℕ) * ω ^ (8:ℕ) + 720 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ *
      w ^ (3:ℕ) * ω ^ (10:ℕ) + 216 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) + 216
      * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 144 * a ^ (4:ℕ) * d ^ (6:ℕ)
      * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 144 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) *
      ω ^ (4:ℕ) * κ - 1944 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 648 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 72 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) - 72 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) *
      ω ^ (4:ℕ) * κ - 6264 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) + 72 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ + 10224 * a ^ (4:ℕ) * d ^ (6:ℕ)
      * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) + 1728 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
      ω ^ (8:ℕ) * κ - 288 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) + 1152 * a ^ (4:ℕ) *
      d ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) + 288 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ -
      864 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) - 288 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (3:ℕ)
      * ω ^ (10:ℕ) * κ + 1836 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) + 1836 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 1332 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 1332 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) *
      ω ^ (4:ℕ) * κ - 3600 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 5436 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 252 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 540 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) *
      w ^ (7:ℕ) * ω ^ (6:ℕ) - 540 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ -
      28224 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 72 * a ^ (4:ℕ) * d ^ (5:ℕ)
      * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ - 216 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ)
      * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 57060 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) +
      15984 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 396 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 36 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ *
      w ^ (9:ℕ) * ω ^ (6:ℕ) - 36 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (9:ℕ) * ω ^ (4:ℕ) * κ - 2736 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (7:ℕ) * ω ^ (8:ℕ) + 252 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ *
      w ^ (7:ℕ) * ω ^ (6:ℕ) * κ + 36 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ)
      + 12420 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (5:ℕ) * ω ^ (10:ℕ) + 3312 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ - 108 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (5:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 11520 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (3:ℕ) * ω ^ (12:ℕ) - 6264 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ - 792 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (3:ℕ) *
      ω ^ (8:ℕ) * κ ^ (2:ℕ) + 6048 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) +
      6048 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 4896 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 4896 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) *
      w ^ (5:ℕ) * ω ^ (4:ℕ) * κ + 2808 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) +
      17424 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 2088 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 1440 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) - 1440 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) *
      ω ^ (4:ℕ) * κ - 67536 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 3744 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ - 1872 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 162504 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) *
      w ^ (3:ℕ) * ω ^ (10:ℕ) + 58248 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ
      - 3384 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 72 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 288 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * ω ^ (6:ℕ) - 288 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) *
      w ^ (9:ℕ) * ω ^ (4:ℕ) * κ - 10440 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ)
      + 1872 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) * κ + 216 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 54792 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) + 16776 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) *
      ω ^ (8:ℕ) * κ - 504 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) +
      72 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 61920 * a ^ (4:ℕ)
      * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) - 44352 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) *
      w ^ (3:ℕ) * ω ^ (10:ℕ) * κ - 7776 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) + 9504 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) + 9504 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 8928 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 8928 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) *
      ω ^ (4:ℕ) * κ + 16704 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 25632 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 6624 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 1440 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) *
      w ^ (7:ℕ) * ω ^ (6:ℕ) - 1440 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ -
      91008 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 15552 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ - 6336 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) *
      w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 250272 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) *
      ω ^ (10:ℕ) + 103104 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 11232 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 864 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (9:ℕ) * ω ^ (6:ℕ) - 864 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) *
      ω ^ (4:ℕ) * κ - 20160 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) + 4896 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) * κ + 288 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 125856 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) *
      w ^ (5:ℕ) * ω ^ (10:ℕ) + 47808 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ
      + 288 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 576 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 172800 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) - 150336 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) *
      w ^ (3:ℕ) * ω ^ (10:ℕ) * κ - 30528 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) + 6912 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) + 6912 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 8064 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (8:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 8064 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) *
      ω ^ (4:ℕ) * κ + 17856 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 14976 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 9792 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 66816 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) *
      w ^ (5:ℕ) * ω ^ (8:ℕ) - 26496 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ
      - 10368 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 196416 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) + 84672 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 17856 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ)
      * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 1728 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) *
      κ ^ (3:ℕ) - 1152 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * ω ^ (6:ℕ) - 1152 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * ω ^ (4:ℕ) * κ - 20160 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) + 4608 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) *
      ω ^ (6:ℕ) * κ - 576 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) +
      157248 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) + 80064 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ + 5184 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) *
      w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 1728 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) *
      ω ^ (4:ℕ) * κ ^ (3:ℕ) - 264960 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) -
      269568 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ - 59904 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 1728 * a ^ (4:ℕ) * d * σ ^ (11:ℕ)
      * w ^ (3:ℕ) * ω ^ (6:ℕ) + 1728 * a ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 2880
      * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 2880 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) *
      w ^ (5:ℕ) * ω ^ (4:ℕ) * κ + 4608 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) - 576 *
      a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 6336 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) *
      w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) +
      576 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ - 23040 * a ^ (4:ℕ) * d *
      σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 19584 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ)
      * κ - 8064 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 58176 * a ^ (4:ℕ)
      * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) + 18432 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (3:ℕ) *
      ω ^ (8:ℕ) * κ - 13248 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 2304 *
      a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 576 * a ^ (4:ℕ) * d *
      σ ^ (5:ℕ) * w ^ (9:ℕ) * ω ^ (6:ℕ) - 576 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (9:ℕ) * ω ^ (4:ℕ) *
      κ - 9216 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) - 576 * a ^ (4:ℕ) * d * σ ^ (5:ℕ)
      * w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 1728 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) + 99648 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) + 73728 * a ^ (4:ℕ) * d
      * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ + 9792 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (5:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 2304 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) -
      211968 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) - 247680 * a ^ (4:ℕ) * d *
      σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ - 58752 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (3:ℕ) *
      ω ^ (8:ℕ) * κ ^ (2:ℕ) - 1152 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) - 2304 *
      a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 1152 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ)
      * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 2304 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 4608 *
      a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ - 2304 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) *
      ω ^ (4:ℕ) * κ ^ (2:ℕ) - 3456 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) - 8064 *
      a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 3456 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 1152 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) -
      1152 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) - 2304 * a ^ (4:ℕ) * σ ^ (6:ℕ) *
      w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 1152 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) +
      24192 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) + 28800 * a ^ (4:ℕ) * σ ^ (6:ℕ) *
      w ^ (5:ℕ) * ω ^ (8:ℕ) * κ + 5760 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) +
      1152 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ ^ (3:ℕ) - 69120 * a ^ (4:ℕ) *
      σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) - 92160 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) *
      κ - 23040 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ)) * h2 + (1440 *
      a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 864 * a ^ (4:ℕ) * d ^ (7:ℕ) *
      σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 288 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
      ω ^ (10:ℕ) + 5040 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 1008 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ + 1584 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) + 1008 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) *
      ω ^ (6:ℕ) * κ - 10080 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) - 2160 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 1152 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ * w ^ (7:ℕ) * ω ^ (8:ℕ) - 2016 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (5:ℕ) * ω ^ (10:ℕ) - 720 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ + 1296 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ *
      w ^ (3:ℕ) * ω ^ (12:ℕ) + 720 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ + 11664
      * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 144 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ + 14112 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ)
      * ω ^ (8:ℕ) + 1440 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ - 53568 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) - 2448 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 1728 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 144 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) - 1008
      * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 12384 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) + 2736 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) *
      w ^ (5:ℕ) * ω ^ (8:ℕ) * κ - 1152 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) + 27504 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) + 16128 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ + 1296 * a ^ (4:ℕ) * d ^ (5:ℕ)
      * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 288 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (7:ℕ) *
      ω ^ (10:ℕ) + 1152 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (12:ℕ) + 576 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) * κ - 864 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (14:ℕ)
      - 1152 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) * κ - 288 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      w ^ (3:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 28116 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) *
      ω ^ (8:ℕ) - 2412 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ + 44748 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) + 13644 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ - 108720 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ)
      * ω ^ (10:ℕ) - 6768 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ + 7416 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 10980 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) + 2268 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) *
      w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 52272 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ)
      - 11376 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ + 1584 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 157932 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) + 80460 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) *
      ω ^ (10:ℕ) * κ - 540 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) +
      1188 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 4572 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (9:ℕ) * ω ^ (8:ℕ) + 36 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (9:ℕ)
      * ω ^ (6:ℕ) * κ - 8064 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (7:ℕ) * ω ^ (10:ℕ) - 8064 * a ^ (4:ℕ)
      * d ^ (4:ℕ) * σ * w ^ (7:ℕ) * ω ^ (8:ℕ) * κ - 72 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (7:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 9324 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (5:ℕ) * ω ^ (12:ℕ) - 756 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (5:ℕ) * ω ^ (10:ℕ) * κ - 3420 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ *
      w ^ (5:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 36 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (5:ℕ) * ω ^ (6:ℕ) *
      κ ^ (3:ℕ) - 16992 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (3:ℕ) * ω ^ (14:ℕ) - 20232 * a ^ (4:ℕ) *
      d ^ (4:ℕ) * σ * w ^ (3:ℕ) * ω ^ (12:ℕ) * κ - 5904 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (3:ℕ) *
      ω ^ (10:ℕ) * κ ^ (2:ℕ) - 360 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) +
      38592 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 5472 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ + 35136 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ)
      * w ^ (5:ℕ) * ω ^ (8:ℕ) + 27360 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) *
      κ - 86256 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) - 24912 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ + 13536 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ)
      * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 47808 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) *
      ω ^ (8:ℕ) - 10080 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 151488 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) - 42912 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ - 24480 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ)
      * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 389664 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ)
      + 170928 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ + 4896 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 8784 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 7488 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
      w ^ (9:ℕ) * ω ^ (8:ℕ) - 4320 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * ω ^ (6:ℕ) * κ -
      32976 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (10:ℕ) - 11088 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) * κ - 8064 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
      w ^ (7:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 37728 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) *
      ω ^ (12:ℕ) - 3600 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) * κ - 2592 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 3600 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 99936 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (14:ℕ) - 111024 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
      ω ^ (12:ℕ) * κ - 30096 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) *
      κ ^ (2:ℕ) - 144 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 432
      * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 22464 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 9792 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) *
      w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 9216 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) -
      3456 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ - 8928 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) - 13824 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) *
      w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 15840 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ)
      * κ ^ (2:ℕ) - 46656 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) - 33984 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 223488 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) - 27072 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) *
      ω ^ (8:ℕ) * κ - 44352 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ)
      + 434016 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) + 161568 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ + 10944 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ)
      * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 6912 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) *
      ω ^ (6:ℕ) * κ ^ (3:ℕ) + 3456 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * ω ^ (8:ℕ) -
      2304 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * ω ^ (6:ℕ) * κ - 48672 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (10:ℕ) + 5184 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
      w ^ (7:ℕ) * ω ^ (8:ℕ) * κ + 3744 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) + 91872 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (12:ℕ) + 11808 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) * κ - 5184 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 8064 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
      w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 260928 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) *
      ω ^ (14:ℕ) - 275616 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) * κ - 71424 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 3456 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 2016 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (4:ℕ) + 3456 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (3:ℕ)
      * ω ^ (8:ℕ) + 2304 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 14976 *
      a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 16128 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) *
      w ^ (5:ℕ) * ω ^ (6:ℕ) * κ + 5184 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) + 2304 *
      a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ - 15552 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) *
      w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 12672 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ)
      - 11520 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 133632 * a ^ (4:ℕ) * d *
      σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) - 4608 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ)
      * κ + 6912 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 162432 *
      a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) + 29376 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) *
      w ^ (3:ℕ) * ω ^ (10:ℕ) * κ - 10368 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) *
      κ ^ (2:ℕ) + 13248 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 5760 *
      a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (9:ℕ) * ω ^ (8:ℕ) + 6912 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) *
      w ^ (9:ℕ) * ω ^ (6:ℕ) * κ - 28224 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (10:ℕ) + 11520
      * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) * κ + 22464 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) *
      w ^ (7:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 120960 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (5:ℕ) *
      ω ^ (12:ℕ) + 31680 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) * κ - 12672 *
      a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 13248 * a ^ (4:ℕ) * d *
      σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 319104 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (3:ℕ)
      * ω ^ (14:ℕ) - 325440 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) * κ - 84672 *
      a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 4608 * a ^ (4:ℕ) * d *
      σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (3:ℕ) *
      ω ^ (8:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 1728 * a ^ (4:ℕ) *
      σ ^ (9:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) - 1728 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ -
      10368 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) - 5760 * a ^ (4:ℕ) * σ ^ (9:ℕ) *
      w ^ (3:ℕ) * ω ^ (8:ℕ) * κ + 1152 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) -
      1728 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) - 1728 * a ^ (4:ℕ) * σ ^ (7:ℕ) *
      w ^ (7:ℕ) * ω ^ (6:ℕ) * κ - 16128 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) + 2304 *
      a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ) * κ + 2304 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) - 23616 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (12:ℕ) - 37440 *
      a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ - 9792 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ)
      * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) -
      576 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (9:ℕ) * ω ^ (8:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (9:ℕ)
      * ω ^ (6:ℕ) * κ - 5760 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (10:ℕ) + 8064 * a ^ (4:ℕ) *
      σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (8:ℕ) * κ + 1152 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) + 63936 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (12:ℕ) + 17856 * a ^ (4:ℕ) *
      σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (10:ℕ) * κ - 5184 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 149760 *
      a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (14:ℕ) - 149760 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) *
      ω ^ (12:ℕ) * κ - 39168 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 2304 *
      a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ)) * h1

/-- The key identity of the closed form, the part of degree 2 in `ν`. -/
@[tmio M, powerlib_domain] private theorem zk_key2 {a b d κ σ w ω : ℝ}
    (h1 : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * (κ + ω ^ 2))
    (h2 : a * b * w = κ * (σ ^ 2 + w ^ 2) + ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d - κ)) :
    zkZ (2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ)) (-4 * a * d * σ * w * ω - 2 * a *
      σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w * ω ^ (3:ℕ) + 2 * a * w * ω * κ) (-6 * d
      * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 * ω ^ (4:ℕ) + 3 *
      ω ^ (2:ℕ) * κ) (-6 * d * ω ^ (3:ℕ) - 12 * σ * ω ^ (3:ℕ)) 0 0 (a ^ (3:ℕ) * σ ^ (4:ℕ) *
      w ^ (3:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) - a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
      ω ^ (2:ℕ) + a ^ (3:ℕ) * w ^ (7:ℕ) - a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ)) (2 * a ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (3:ℕ) * ω + 2 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω) (-a ^ (3:ℕ) * σ ^ (4:ℕ) *
      w ^ (3:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) + 13 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
      ω ^ (2:ℕ) - a ^ (3:ℕ) * w ^ (7:ℕ) + 5 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) - 4 * a ^ (3:ℕ) *
      w ^ (3:ℕ) * ω ^ (4:ℕ)) (-6 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω - 6 * a ^ (3:ℕ) * σ *
      w ^ (5:ℕ) * ω + 12 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (3:ℕ)) (a * b * w - κ * (σ ^ 2 + w ^ 2))
      * (2 * σ + d) ^ 4 = 72 * a ^ 4 * d * σ * w ^ 2 * ω ^ 6 * (w ^ 2 * bautinCorr d σ w κ) := by
  unfold zkZ bautinCorr
  linear_combination (-108 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) - 72 *
      a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) - 108 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) + 36 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (8:ℕ) * ω ^ (4:ℕ) -
      108 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (6:ℕ) * ω ^ (6:ℕ) - 918 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) - 666 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) *
      ω ^ (4:ℕ) - 1008 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) + 126 * a ^ (4:ℕ)
      * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ + 270 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ)
      * w ^ (8:ℕ) * ω ^ (4:ℕ) - 576 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) +
      108 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ - 522 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 54 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 18 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) - 144 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 18 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (8:ℕ) *
      ω ^ (4:ℕ) * κ + 342 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) + 90 * a ^ (4:ℕ) *
      d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ - 216 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) -
      72 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ - 3024 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) - 2448 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) *
      ω ^ (4:ℕ) - 3708 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) + 1044 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ + 720 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) - 216 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) + 936 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ - 4068 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 360 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 36 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) *
      ω ^ (4:ℕ) * κ ^ (2:ℕ) + 144 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (10:ℕ) * ω ^ (4:ℕ) - 1116 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (8:ℕ) * ω ^ (6:ℕ) - 108 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ *
      w ^ (8:ℕ) * ω ^ (4:ℕ) * κ + 2556 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) + 504 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ - 36 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ *
      w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 1440 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ)
      - 216 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 72 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ
      * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 4752 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) *
      ω ^ (4:ℕ) - 4464 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) - 6624 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) + 3312 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ + 720 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) *
      ω ^ (4:ℕ) + 4032 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) + 3168 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ - 11664 * a ^ (4:ℕ) * d ^ (3:ℕ)
      * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 720 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) *
      ω ^ (6:ℕ) * κ - 288 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) +
      432 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) - 3168 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 144 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
      w ^ (8:ℕ) * ω ^ (4:ℕ) * κ + 6768 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) +
      432 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ - 288 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 2880 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 1152 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) * κ + 576 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) -
      3456 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) - 4032 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) - 5472 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) + 4896 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ +
      9216 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) + 5184 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ - 14112 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ)
      * w ^ (4:ℕ) * ω ^ (8:ℕ) - 864 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) - 3744 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) + 288 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) * κ + 6624 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) *
      ω ^ (8:ℕ) - 2304 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ - 864 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 6336 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 1728 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 864 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      1440 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) - 1152 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) + 3168 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ - 288 *
      a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) + 6912 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) *
      w ^ (6:ℕ) * ω ^ (6:ℕ) + 4032 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ - 4896 *
      a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 1440 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 1152 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) + 288 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) - 1152 * a ^ (4:ℕ) * d *
      σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) + 864 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) *
      κ - 288 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 5472 * a ^ (4:ℕ) * d * σ ^ (4:ℕ)
      * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ - 1152 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) *
      κ ^ (2:ℕ) + 5760 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 10368 * a ^ (4:ℕ) * d
      * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 2304 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) + 576 * a ^ (4:ℕ)
      * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ + 1152 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ)
      + 1152 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ + 1728 * a ^ (4:ℕ) * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) + 1152 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 576 *
      a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (5:ℕ) *
      w ^ (8:ℕ) * ω ^ (6:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) * κ - 2880 *
      a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 3456 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) * κ - 576 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) + 4608 *
      a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 5760 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) * κ + 1152 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ)) * h2 + (-504
      * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) - 504 * a ^ (4:ℕ) * d ^ (6:ℕ) *
      σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) - 144 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) - 144 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 72 * a ^ (4:ℕ) * d ^ (5:ℕ) *
      σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) - 720 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) + 936 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 864 * a ^ (4:ℕ)
      * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 504 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ *
      w ^ (8:ℕ) * ω ^ (6:ℕ) - 792 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) + 576 *
      a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 432 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ *
      w ^ (4:ℕ) * ω ^ (10:ℕ) + 144 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 1206 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) - 6822 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) + 3168 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) - 3708 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 1134 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 5832 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 792 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) * κ + 594 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 1872 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ - 594 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 18 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (10:ℕ) *
      ω ^ (6:ℕ) + 216 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) + 36 * a ^ (4:ℕ) * d ^ (4:ℕ) *
      w ^ (8:ℕ) * ω ^ (6:ℕ) * κ - 558 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 144 *
      a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ - 18 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) - 216 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 288 * a ^ (4:ℕ)
      * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 72 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ)
      * κ ^ (2:ℕ) - 2736 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) - 13680 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) - 6552 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 6768 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) *
      ω ^ (6:ℕ) * κ + 5040 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 16416 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) + 12240 * a ^ (4:ℕ) * d ^ (3:ℕ) *
      σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ - 4464 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) *
      ω ^ (10:ℕ) - 4968 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 4392 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 2160 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ * w ^ (10:ℕ) * ω ^ (6:ℕ) + 3960 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (8:ℕ) *
      ω ^ (8:ℕ) + 4032 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ - 1296 * a ^ (4:ℕ) *
      d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (10:ℕ) + 3672 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) *
      ω ^ (8:ℕ) * κ + 1800 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 1008 *
      a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) - 648 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ *
      w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 576 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) *
      κ ^ (2:ℕ) + 216 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 4896 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) + 1728 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) - 23472 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) + 7920 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 16992 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 12672 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) + 22176 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) * κ - 7920 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 5760 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 3456 * a ^ (4:ℕ) * d ^ (2:ℕ) *
      σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 1152 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) *
      w ^ (10:ℕ) * ω ^ (6:ℕ) + 10800 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) -
      1872 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 4176 * a ^ (4:ℕ) *
      d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 14400 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) *
      w ^ (6:ℕ) * ω ^ (8:ℕ) * κ - 4032 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 864 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 1584 *
      a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 1872 * a ^ (4:ℕ) * d ^ (2:ℕ)
      * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 1008 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) *
      w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) - 1152 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      8064 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) - 13536 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) + 7776 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 5760 *
      a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) + 1152 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) *
      w ^ (6:ℕ) * ω ^ (8:ℕ) - 3456 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 6336 *
      a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 16992 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ - 6624 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) *
      κ ^ (2:ℕ) - 3456 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) + 5472 * a ^ (4:ℕ) * d *
      σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 11232 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ)
      * κ + 14400 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 14688 * a ^ (4:ℕ) * d *
      σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ - 6624 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) *
      ω ^ (6:ℕ) * κ ^ (2:ℕ) + 1728 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 4896 *
      a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 1152 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) *
      w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 288 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) + 864
      * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) + 2880 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) *
      ω ^ (8:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 864 * a ^ (4:ℕ) *
      σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 1152 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) -
      1152 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 12960 * a ^ (4:ℕ) * σ ^ (6:ℕ) *
      w ^ (4:ℕ) * ω ^ (10:ℕ) + 5760 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 288 *
      a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 288 * a ^ (4:ℕ) * σ ^ (4:ℕ) *
      w ^ (10:ℕ) * ω ^ (6:ℕ) - 4032 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 576 *
      a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 10656 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ)
      * ω ^ (10:ℕ) + 3456 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 288 * a ^ (4:ℕ) *
      σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) + 2304 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) *
      ω ^ (12:ℕ) + 2880 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 576 * a ^ (4:ℕ) *
      σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ)) * h1

/-- The last step of the closed form. -/
@[tmio M, powerlib_domain] private theorem zk_final {Z a d σ ω w K1 K2 bb B : ℝ} (ha : a ≠ 0)
    (hb : bb ≠ 0) (hα : 2 * σ + d ≠ 0) (hω : ω ≠ 0) (hw : w ≠ 0) (hK1 : K1 ≠ 0) (hK2 : K2 ≠ 0)
    (key : Z * (2 * σ + d) ^ 4 = -(72 * a ^ 4 * d * σ * w ^ 2 * ω ^ 6) * B) :
    1 / (2 * ω) * (Z / (bb * ((4 * a ^ 2 * ω ^ 2 * w ^ 2 * K1) * (9 * ω ^ 4 * K2)))) =
      -(a ^ 2 * d * σ / ((2 * σ + d) ^ 4 * ω * bb * K1 * K2)) * B := by
  have hZ : Z = -(72 * a ^ 4 * d * σ * w ^ 2 * ω ^ 6) * B / (2 * σ + d) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 hα)]
    exact key
  rw [hZ]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem zk_isCriticalPair {f : State 4 → State 4}
    {a b d κ σ w ω : ℝ} (ha : 0 < a) (hw : 0 < w) (hω : 0 < ω) (hσ : 0 < σ) (hd : 0 < d)
    (h1 : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * (κ + ω ^ 2))
    (h2 : a * b * w = κ * (σ ^ 2 + w ^ 2) + ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d - κ))
    (hf : f 0 = 0) (hJ : jacobianC f 0 = zkJ a b d κ σ w) :
    IsCriticalPair f 0 ω (zkQC a d κ σ w ω I)
      ((starRingEnd ℂ (zkCC a d κ σ w ω I))⁻¹ • zkLC a d σ w ω I) := by
  have hj : (I : ℂ) ^ 2 = -1 := I_sq
  have hjc : starRingEnd ℂ I = -I := conj_I
  have h1c : (d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) = 2 * σ * (κ + ω ^ 2) := by
    exact_mod_cast h1
  have h2c : (a : ℂ) * b * w = κ * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2) + (ω : ℂ) ^ 2 *
      ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d - κ) := by
    exact_mod_cast h2
  have hR := conj_ofReal
  have hc : zkCC a d κ σ w ω I = ((2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ) : ℝ) : ℂ)
      + ((-4 * a * d * σ * w * ω - 2 * a * σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w *
      ω ^ (3:ℕ) + 2 * a * w * ω * κ : ℝ) : ℂ) * I := by
    simp only [zkCC]
    push_cast
    ring
  have hc0 : zkCC a d κ σ w ω I ≠ 0 := by
    rw [hc]
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
        zero_re] at h'
    nlinarith [mul_pos (mul_pos (mul_pos ha hw) (pow_pos hω 2)) (by positivity : 0 < 2 * σ + d)]
  refine ⟨hf, hω, ?_, ?_, ?_⟩
  · rw [hJ]
    exact zk_right hj h1c h2c
  · rw [hJ, Matrix.mulVec_smul, zk_left hj h1c h2c, smul_comm]
  · have hstar : star ((starRingEnd ℂ (zkCC a d κ σ w ω I))⁻¹ • zkLC a d σ w ω I) =
        (zkCC a d κ σ w ω I)⁻¹ • star (zkLC a d σ w ω I) := by
      ext k
      simp [Pi.star_apply]
    rw [hstar, smul_dotProduct, zk_norm (hR a) (hR d) (hR σ) (hR w) (hR ω) hjc hj h1c, smul_eq_mul,
        inv_mul_cancel₀ hc0]

@[tmio M, powerlib_domain] private theorem zk_firstLyapunov {f : State 4 → State 4}
    {a b d κ ν σ w ω : ℝ} (ha : 0 < a) (hd : 0 < d) (hσ : 0 < σ) (hw : 0 < w) (hω : 0 < ω)
    (hdet : 0 < a * b * w - κ * (σ ^ 2 + w ^ 2))
    (h1 : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * (κ + ω ^ 2))
    (h2 : a * b * w = κ * (σ ^ 2 + w ^ 2) + ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d - κ))
    (hJ : jacobianC f 0 = zkJ a b d κ σ w) (hB : ∀ u v, bilinC f 0 u v = zkBil a b ν u v)
    (hC : ∀ u v z, trilinC f 0 u v z = zkTri a b κ u v z) :
    firstLyapunov f 0 ω (zkQC a d κ σ w ω I)
        ((starRingEnd ℂ (zkCC a d κ σ w ω I))⁻¹ • zkLC a d σ w ω I) =
      -(a ^ 2 * d * σ / ((2 * σ + d) ^ 4 * ω * (a * b * w - κ * (σ ^ 2 + w ^ 2)) *
          angleZeroR1 d σ w κ ω * angleZeroR2 d σ w κ ω)) *
        (4 * ω ^ 2 * (a * b * w - κ * (σ ^ 2 + w ^ 2)) * bautinFormQ d σ w κ +
          (ν * w - κ * σ) * (2 * (d + σ) * ω ^ 2 - (ν * w - κ * σ)) * bautinCorr d σ w κ) := by
  have hj : (I : ℂ) ^ 2 = -1 := I_sq
  have hjc : starRingEnd ℂ I = -I := conj_I
  have h1c : (d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) = 2 * σ * (κ + ω ^ 2) := by
    exact_mod_cast h1
  have h2c : (a : ℂ) * b * w = κ * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2) + (ω : ℂ) ^ 2 *
      ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d - κ) := by
    exact_mod_cast h2
  have hR := conj_ofReal
  have hq : star (zkQC a d κ σ w ω I) = zkQC a d κ σ w (-ω) I :=
    zk_star (hR a) (hR d) (hR κ) (hR σ) (hR w) (hR ω) hjc
  have hdet' : ((a * b * w - κ * (σ ^ 2 + w ^ 2) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr hdet.ne'
  have hdetC : (a : ℂ) * b * w - κ * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2) =
      ((a * b * w - κ * (σ ^ 2 + w ^ 2) : ℝ) : ℂ) := by push_cast; ring
  have hc : zkCC a d κ σ w ω I = ((2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ) : ℝ) : ℂ) +
        ((-4 * a * d * σ * w * ω - 2 * a * σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w *
        ω ^ (3:ℕ) + 2 * a * w * ω * κ : ℝ) : ℂ) * I := by
    simp only [zkCC]
    push_cast
    ring
  have hΔ : zkDC d κ σ w ω I = ((-6 * d * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ)
        * ω ^ (2:ℕ) + 15 * ω ^ (4:ℕ) + 3 * ω ^ (2:ℕ) * κ : ℝ) : ℂ) + ((-6 * d * ω ^ (3:ℕ) - 12 * σ *
        ω ^ (3:ℕ) : ℝ) : ℂ) * I := by
    simp only [zkDC]
    push_cast
    ring
  have hα : 0 < 2 * σ + d := by positivity
  have hΔ0 : zkDC d κ σ w ω I ≠ 0 := by
    rw [hΔ]
    intro h
    have h' := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
        zero_im] at h'
    nlinarith [mul_pos (pow_pos hω 3) hα]
  have hA : IsUnit (jacobianC f 0).det := by
    rw [hJ, zk_det, hdetC]
    exact isUnit_iff_ne_zero.mpr hdet'
  have h2' : IsUnit (shift2 (jacobianC f 0) ω).det := by
    rw [hJ, shift2, zk_det2 hj h1c h2c]
    exact isUnit_iff_ne_zero.mpr hΔ0
  have hr : jacobianC f 0 *ᵥ (((a * b * w - κ * (σ ^ 2 + w ^ 2) : ℝ) : ℂ)⁻¹ •
      zkRC a d κ ν σ w ω) = bilinC f 0 (zkQC a d κ σ w ω I) (star (zkQC a d κ σ w ω I)) := by
    rw [Matrix.mulVec_smul, hJ, zk_r hj h1c h2c, hB, hq, hdetC, smul_smul,
      inv_mul_cancel₀ hdet', one_smul]
  have hs : shift2 (jacobianC f 0) ω *ᵥ ((zkDC d κ σ w ω I)⁻¹ • zkSC a d κ ν σ w ω I) =
      bilinC f 0 (zkQC a d κ σ w ω I) (zkQC a d κ σ w ω I) := by
    rw [Matrix.mulVec_smul, hJ, shift2, zk_S hj h1c h2c, hB, smul_smul, inv_mul_cancel₀ hΔ0,
      one_smul]
  have hpair : ∀ (z : ℂ) (v : Fin 4 → ℂ),
      pairing ((starRingEnd ℂ z)⁻¹ • zkLC a d σ w ω I) v = z⁻¹ * pairing (zkLC a d σ w ω I) v := by
    intro z v
    simp [pairing_apply, Finset.mul_sum, mul_assoc]
  rw [firstLyapunov_eq_of_solve hA h2' hr hs, (bilinC f 0 _).map_smul, (bilinC f 0 _).map_smul,
    hC, hB, hB, hq, (pairing _).map_smul, (pairing _).map_smul, hpair, hpair, hpair, smul_eq_mul,
    smul_eq_mul]
  rw [(zk_Y1 (hR a) (hR d) (hR σ) (hR w) (hR ω) hjc hj h1c h2c).trans
      (show _ = ((-4 * a ^ (3:ℕ) * d * σ * w ^ (3:ℕ) * ω ^ (2:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) *
          w ^ (3:ℕ) * ω ^ (2:ℕ) - 3 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * κ - 4 * a ^ (3:ℕ) *
          w ^ (5:ℕ) * ω ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (5:ℕ) * κ + 4 * a ^ (3:ℕ) * w ^ (3:ℕ) *
          ω ^ (4:ℕ) + 3 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ : ℝ) : ℂ) + ((-4 * a ^ (3:ℕ) * σ *
          w ^ (3:ℕ) * ω ^ (3:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω * κ : ℝ) : ℂ) * I
          by push_cast; ring),
    (zk_Y2 (hR a) (hR σ) (hR w) (hR ω) hjc hj h1c h2c).trans
      (show _ = (((a ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω ^ (4:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω ^ (2:ℕ)
          * κ + a ^ (3:ℕ) * σ ^ (6:ℕ) * w * κ ^ (2:ℕ) + a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) *
          ω ^ (4:ℕ) + 3 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ + 2 * a ^ (3:ℕ) *
          σ ^ (4:ℕ) * w ^ (3:ℕ) * κ ^ (2:ℕ) + 3 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (6:ℕ) + 6 *
          a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (4:ℕ) * κ + 3 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (2:ℕ) *
          κ ^ (2:ℕ) - a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) + a ^ (3:ℕ) * σ ^ (2:ℕ) *
          w ^ (5:ℕ) * κ ^ (2:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) - 2 * a ^ (3:ℕ)
          * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 3 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (8:ℕ) + 6 *
          a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (6:ℕ) * κ + 3 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (4:ℕ) *
          κ ^ (2:ℕ) - a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) - a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (2:ℕ) * κ + 3
          * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 4 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ +
          a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) - 5
          * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 2 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) *
          κ ^ (2:ℕ) + a ^ (3:ℕ) * w * ω ^ (10:ℕ) + 2 * a ^ (3:ℕ) * w * ω ^ (8:ℕ) * κ + a ^ (3:ℕ) * w
          * ω ^ (6:ℕ) * κ ^ (2:ℕ)) + ν * (-2 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) - 2 *
          a ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * κ - 4 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ)
          - 4 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ - 2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
          ω ^ (4:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) * κ - 2 * a ^ (3:ℕ) * σ *
          w ^ (6:ℕ) * ω ^ (2:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (6:ℕ) * κ - 2 * a ^ (3:ℕ) * σ * w ^ (4:ℕ)
          * ω ^ (4:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (2:ℕ) * κ) + ν ^ 2 * (a ^ (3:ℕ) *
          σ ^ (4:ℕ) * w ^ (3:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) - a ^ (3:ℕ) * σ ^ (2:ℕ) *
          w ^ (3:ℕ) * ω ^ (2:ℕ) + a ^ (3:ℕ) * w ^ (7:ℕ) - a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ)) : ℝ) :
          ℂ) + (((8 * a ^ (3:ℕ) * d * w ^ (5:ℕ) * ω ^ (5:ℕ) + 4 * a ^ (3:ℕ) * d * w ^ (5:ℕ) *
          ω ^ (3:ℕ) * κ - 16 * a ^ (3:ℕ) * d * w ^ (3:ℕ) * ω ^ (7:ℕ) - 12 * a ^ (3:ℕ) * d *
          w ^ (3:ℕ) * ω ^ (5:ℕ) * κ + 8 * a ^ (3:ℕ) * d * w * ω ^ (9:ℕ) + 8 * a ^ (3:ℕ) * d * w *
          ω ^ (7:ℕ) * κ + 2 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (5:ℕ) + 4 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w
          * ω ^ (3:ℕ) * κ + 2 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω * κ ^ (2:ℕ) + 2 * a ^ (3:ℕ) *
          σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ + 2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω *
          κ ^ (2:ℕ) + 8 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (7:ℕ) + 16 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w *
          ω ^ (5:ℕ) * κ + 8 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (3:ℕ) * κ ^ (2:ℕ) - 2 * a ^ (3:ℕ) * σ
          * w ^ (5:ℕ) * ω ^ (5:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ - 12 * a ^ (3:ℕ) *
          σ * w ^ (3:ℕ) * ω ^ (7:ℕ) - 18 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ - 6 * a ^ (3:ℕ)
          * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ ^ (2:ℕ) + 14 * a ^ (3:ℕ) * σ * w * ω ^ (9:ℕ) + 28 *
          a ^ (3:ℕ) * σ * w * ω ^ (7:ℕ) * κ + 14 * a ^ (3:ℕ) * σ * w * ω ^ (5:ℕ) * κ ^ (2:ℕ)) + ν *
          (-4 * a ^ (3:ℕ) * d * σ * w ^ (2:ℕ) * ω ^ (5:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (3:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω * κ - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) *
          w ^ (4:ℕ) * ω ^ (3:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω * κ - 8 * a ^ (3:ℕ) *
          σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (5:ℕ) - 8 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (3:ℕ) * κ)
          + ν ^ 2 * (2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω + 2 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω)
          : ℝ) : ℂ) * I by push_cast; ring),
    (zk_Y3 (hR a) (hR σ) (hR w) (hR ω) hjc hj h1c h2c).trans
      (show _ = (((24 * a ^ (3:ℕ) * d ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) - 32 * a ^ (3:ℕ) * d ^ (2:ℕ) *
          w ^ (3:ℕ) * ω ^ (6:ℕ) + 8 * a ^ (3:ℕ) * d ^ (2:ℕ) * w * ω ^ (8:ℕ) - 64 * a ^ (3:ℕ) * d * σ
          * w ^ (3:ℕ) * ω ^ (6:ℕ) - 64 * a ^ (3:ℕ) * d * σ * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 56 *
          a ^ (3:ℕ) * d * σ * w * ω ^ (8:ℕ) + 56 * a ^ (3:ℕ) * d * σ * w * ω ^ (6:ℕ) * κ - a ^ (3:ℕ)
          * σ ^ (6:ℕ) * w * ω ^ (4:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω ^ (2:ℕ) * κ - a ^ (3:ℕ) *
          σ ^ (6:ℕ) * w * κ ^ (2:ℕ) - 5 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) - 7 *
          a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ - 2 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ)
          * κ ^ (2:ℕ) + 9 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (6:ℕ) + 18 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w *
          ω ^ (4:ℕ) * κ + 9 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (2:ℕ) * κ ^ (2:ℕ) - 7 * a ^ (3:ℕ) *
          σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) - 8 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ
          - a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * κ ^ (2:ℕ) - 14 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) *
          ω ^ (6:ℕ) - 22 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ - 8 * a ^ (3:ℕ) *
          σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) + 49 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (8:ℕ)
          + 98 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (6:ℕ) * κ + 49 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w *
          ω ^ (4:ℕ) * κ ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) - 3 * a ^ (3:ℕ) * w ^ (7:ℕ)
          * ω ^ (2:ℕ) * κ + 9 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 12 * a ^ (3:ℕ) * w ^ (5:ℕ) *
          ω ^ (4:ℕ) * κ + 3 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) + 3 * a ^ (3:ℕ) *
          w ^ (3:ℕ) * ω ^ (8:ℕ) + 9 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ + 6 * a ^ (3:ℕ) *
          w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ) - 9 * a ^ (3:ℕ) * w * ω ^ (10:ℕ) - 18 * a ^ (3:ℕ) * w *
          ω ^ (8:ℕ) * κ - 9 * a ^ (3:ℕ) * w * ω ^ (6:ℕ) * κ ^ (2:ℕ)) + ν * (16 * a ^ (3:ℕ) * d *
          w ^ (4:ℕ) * ω ^ (4:ℕ) - 16 * a ^ (3:ℕ) * d * w ^ (2:ℕ) * ω ^ (6:ℕ) + 2 * a ^ (3:ℕ) *
          σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) + 2 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * κ + 4 *
          a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ) + 4 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * κ
          - 22 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) - 22 * a ^ (3:ℕ) * σ ^ (3:ℕ) *
          w ^ (2:ℕ) * ω ^ (2:ℕ) * κ + 2 * a ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (2:ℕ) + 2 * a ^ (3:ℕ) * σ
          * w ^ (6:ℕ) * κ - 6 * a ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (4:ℕ) - 6 * a ^ (3:ℕ) * σ *
          w ^ (4:ℕ) * ω ^ (2:ℕ) * κ - 40 * a ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (6:ℕ) - 40 * a ^ (3:ℕ) *
          σ * w ^ (2:ℕ) * ω ^ (4:ℕ) * κ) + ν ^ 2 * (-a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) - 2 *
          a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) + 13 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) -
          a ^ (3:ℕ) * w ^ (7:ℕ) + 5 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) - 4 * a ^ (3:ℕ) * w ^ (3:ℕ)
          * ω ^ (4:ℕ)) : ℝ) : ℂ) + (((-24 * a ^ (3:ℕ) * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ) + 24 *
          a ^ (3:ℕ) * d ^ (2:ℕ) * σ * w * ω ^ (7:ℕ) - 12 * a ^ (3:ℕ) * d * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ
          + 12 * a ^ (3:ℕ) * d * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ - 6 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w *
          ω ^ (5:ℕ) - 12 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (3:ℕ) * κ - 6 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w
          * ω * κ ^ (2:ℕ) - 12 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (5:ℕ) - 18 * a ^ (3:ℕ) *
          σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ - 6 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω *
          κ ^ (2:ℕ) - 12 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (7:ℕ) - 24 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w *
          ω ^ (5:ℕ) * κ - 12 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (3:ℕ) * κ ^ (2:ℕ) - 6 * a ^ (3:ℕ) * σ
          * w ^ (5:ℕ) * ω ^ (5:ℕ) - 6 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ - 12 * a ^ (3:ℕ) *
          σ * w ^ (3:ℕ) * ω ^ (7:ℕ) - 6 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ + 6 * a ^ (3:ℕ)
          * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ ^ (2:ℕ) + 18 * a ^ (3:ℕ) * σ * w * ω ^ (9:ℕ) + 36 *
          a ^ (3:ℕ) * σ * w * ω ^ (7:ℕ) * κ + 18 * a ^ (3:ℕ) * σ * w * ω ^ (5:ℕ) * κ ^ (2:ℕ)) + ν *
          (-12 * a ^ (3:ℕ) * d * σ * w ^ (2:ℕ) * ω ^ (5:ℕ) + 12 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ)
          * ω ^ (3:ℕ) + 12 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω * κ + 12 * a ^ (3:ℕ) * σ ^ (2:ℕ)
          * w ^ (4:ℕ) * ω ^ (3:ℕ) + 12 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω * κ) + ν ^ 2 * (-6 *
          a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω - 6 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω + 12 * a ^ (3:ℕ)
          * σ * w ^ (3:ℕ) * ω ^ (3:ℕ)) : ℝ) : ℂ) * I by push_cast; ring), hc, hΔ, zk_re]
  · rw [zkZ_split, show (2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ)) ^ 2 + (-4 * a * d *
          σ * w * ω - 2 * a * σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w * ω ^ (3:ℕ) + 2
          * a * w * ω * κ) ^ 2 = 4 * a ^ 2 * ω ^ 2 * w ^ 2 * angleZeroR1 d σ w κ ω by
        unfold angleZeroR1; ring,
      show (-6 * d * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 *
          ω ^ (4:ℕ) + 3 * ω ^ (2:ℕ) * κ) ^ 2 + (-6 * d * ω ^ (3:ℕ) - 12 * σ * ω ^ (3:ℕ)) ^ 2 = 9 *
          ω ^ 4 * angleZeroR2 d σ w κ ω by
        unfold angleZeroR2; ring]
    exact zk_final ha.ne' hdet.ne' hα.ne' hω.ne' hw.ne'
      (by unfold angleZeroR1; positivity) (by unfold angleZeroR2; positivity)
      (by linear_combination zk_key0 h1 h2 + ν * zk_key1 h1 h2 + ν ^ 2 * zk_key2 h1 h2)
  · exact hdet.ne'
  · positivity
  · rw [show (-6 * d * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 *
        ω ^ (4:ℕ) + 3 * ω ^ (2:ℕ) * κ) ^ 2 + (-6 * d * ω ^ (3:ℕ) - 12 * σ * ω ^ (3:ℕ)) ^ 2 = (-6 * d
        * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 * ω ^ (4:ℕ) + 3
        * ω ^ (2:ℕ) * κ) ^ 2 + (6 * d * ω ^ 3 + 12 * σ * ω ^ 3) ^ 2 by ring]
    positivity

/-! ## The rotated frame -/

/-- The rotation of the current components by `θ`. -/
private def rotMat (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, Real.cos θ, -Real.sin θ; 0, 0, Real.sin θ, Real.cos θ]

@[tmio M, powerlib_domain] private theorem rotMat_inv (θ : ℝ) (x : State 4) :
    Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (rotMat θ)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (rotMat (-θ)) x) = x := by
  ext i
  fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four, rotMat, Real.cos_neg,
    Real.sin_neg]
  · linear_combination (x 2) * Real.cos_sq_add_sin_sq θ
  · linear_combination (x 3) * Real.cos_sq_add_sin_sq θ

/-- The rotation as a linear isomorphism (grid frame to the frame rotated by `θ`). -/
private def rotE (θ : ℝ) : State 4 ≃L[ℝ] State 4 :=
  ContinuousLinearEquiv.equivOfInverse (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (rotMat (-θ)))
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (rotMat θ)) (rotMat_inv θ)
    (fun x => by simpa using rotMat_inv (-θ) x)

/-- **The current components rotated by `θ`**: `(v₀, v₁, cos θ v₂ − sin θ v₃,
sin θ v₂ + cos θ v₃)`, the grid-frame reading of a vector of the frame rotated by `θ`. -/
def rotC (θ : ℝ) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![v 0, v 1, (Real.cos θ : ℂ) * v 2 - (Real.sin θ : ℂ) * v 3,
    (Real.sin θ : ℂ) * v 2 + (Real.cos θ : ℂ) * v 3]

@[tmio M, powerlib_domain] theorem rotC_zero (v : Fin 4 → ℂ) : rotC 0 v = v := by
  ext i
  fin_cases i <;> simp [rotC]

@[tmio M, powerlib_domain] private theorem rotE_symm_mulVec (θ : ℝ) (v : Fin 4 → ℂ) :
    cmat ((rotE θ).symm : State 4 →L[ℝ] State 4) *ᵥ v = rotC θ v := by
  rw [show ((rotE θ).symm : State 4 →L[ℝ] State 4) =
    Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (rotMat θ) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

@[tmio M, powerlib_domain] private theorem rotE_transpose_mulVec (θ : ℝ) (v : Fin 4 → ℂ) :
    (cmat (rotE θ : State 4 →L[ℝ] State 4))ᵀ *ᵥ v = rotC θ v := by
  rw [show (rotE θ : State 4 →L[ℝ] State 4) =
    Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (rotMat (-θ)) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Real.cos_neg,
    Real.sin_neg]
  ring

@[tmio M, powerlib_domain] private theorem rotE_mul_symm (θ : ℝ) :
    cmat (rotE θ : State 4 →L[ℝ] State 4) * cmat ((rotE θ).symm : State 4 →L[ℝ] State 4) = 1 := by
  rw [← cmat_comp, (rotE θ).coe_comp_coe_symm, cmat_id]

/-- **The derivatives in the rotated frame**: in the frame rotated with the operating angle
(`rotE`), the Jacobian, the second and the third derivative of a physical balanced model are the
patterns of the angle `0` with `κ = Q/M` and `ν = P_ref/M`. -/
@[tmio M, powerlib_domain] private theorem rot_data {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) :
    jacobianC (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 =
        zkJ ((m.g.E / m.g.M : ℝ) : ℂ) ((m.g.E / m.g.L : ℝ) : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
          ((m.Q / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) ∧
      (∀ u v, bilinC (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 u v =
        zkBil ((m.g.E / m.g.M : ℝ) : ℂ) ((m.g.E / m.g.L : ℝ) : ℂ) ((m.g.Pref / m.g.M : ℝ) : ℂ)
          u v) ∧
      (∀ u v z, trilinC (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 u v z =
        zkTri ((m.g.E / m.g.M : ℝ) : ℂ) ((m.g.E / m.g.L : ℝ) : ℂ) ((m.Q / m.g.M : ℝ) : ℂ)
          u v z) := by
  have hL : m.g.L ≠ 0 := hp.1.L.ne'
  have hcsC := Complex.cos_sq_add_sin_sq (m.δ : ℂ)
  have hT : cmat (rotE m.δ : State 4 →L[ℝ] State 4) =
      (rotMat (-m.δ)).map (fun x => (x : ℂ)) := cmat_toEuclideanCLM _
  have hS : cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4) =
      (rotMat m.δ).map (fun x => (x : ℂ)) := cmat_toEuclideanCLM _
  have hinv : ∀ u : Fin 4 → ℂ, cmat (rotE m.δ : State 4 →L[ℝ] State 4) *ᵥ
      (cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, rotE_mul_symm, Matrix.one_mulVec]
  obtain ⟨p0, p2, p3⟩ := model_point m
  have hP : m.g.E * (Real.cos m.δ * (m.g.is m.δ).re + Real.sin m.δ * (m.g.is m.δ).im) =
      m.g.Pref := by
    rw [← hb]; simp only [Network.qssPower, Network.power_eq]
  have hQ : m.g.E * (Real.sin m.δ * (m.g.is m.δ).re - Real.cos m.δ * (m.g.is m.δ).im) = m.Q := by
    simp only [Model.Q, Network.qssReactive, Network.reactive_eq]
  refine ⟨?_, fun u v => ?_, fun u v z => ?_⟩
  · have h := jacobianC_conj (rotE m.δ) m.field 0
    rw [map_zero] at h
    rw [h, Model.jacobianC_field, hT, hS, m.jac_eq hL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zkJ, rotMat, Matrix.mul_apply, Fin.sum_univ_four, Real.cos_neg, Real.sin_neg]
    all_goals first | ring1 | linear_combination (-((m.g.E : ℂ) / m.g.M)) * hcsC |
      linear_combination (-((m.g.R : ℂ) / m.g.L)) * hcsC | linear_combination (m.g.ω0 : ℂ) * hcsC |
      linear_combination ((m.g.E : ℂ) / m.g.L) * hcsC | linear_combination (-(m.g.ω0 : ℂ)) * hcsC
  · have h := bilinC_conj (rotE m.δ) m.field 0
      (cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4) *ᵥ u)
      (cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4) *ᵥ v)
    rw [hinv, hinv, map_zero] at h
    rw [h, rotE_symm_mulVec, rotE_symm_mulVec, model_bilinC, bilinC_field_eq, hT, p0, p2, p3,
      Network.power_eq, hP]
    ext k
    fin_cases k <;> simp [zkBil, rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Real.cos_neg, Real.sin_neg]
    all_goals first | ring1 |
      linear_combination (-((m.g.E : ℂ) / m.g.M) * (u 0 * v 3 + u 3 * v 0)) * hcsC |
      linear_combination (-((m.g.E : ℂ) / m.g.L) * (u 0 * v 0)) * hcsC
  · have h := trilinC_conj (rotE m.δ) m.field 0
      (cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4) *ᵥ u)
      (cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4) *ᵥ v)
      (cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4) *ᵥ z)
    rw [hinv, hinv, hinv, map_zero] at h
    rw [h, rotE_symm_mulVec, rotE_symm_mulVec, rotE_symm_mulVec, model_trilinC, trilinC_field_eq,
      hT, p0, p2, p3, Network.reactive_eq, hQ]
    ext k
    fin_cases k <;> simp [zkTri, rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Real.cos_neg, Real.sin_neg]
    all_goals first | ring1 |
      linear_combination ((m.g.E : ℂ) / m.g.M * (u 0 * v 0 * z 2 + u 0 * v 2 * z 0 +
        u 2 * v 0 * z 0)) * hcsC |
      linear_combination (-((m.g.E : ℂ) / m.g.L) * (u 0 * v 0 * z 0)) * hcsC

/-! ## The critical pair and the first Lyapunov coefficient at every angle -/

/-- **The critical right eigenvector** at the frequency `ω` (`a = E/M`, `d = D/M`, `κ = Q/M`,
`σ = R/L`, `w = ω₀`): `q = (aw, iωaw, w(κ + ω² − iωd), (σ + iω)(κ + ω² − iωd))`, on the slice
`δ* = 0` and, at every angle, in the frame rotated with `δ*` (`Line.VSM.Model.critQ`). -/
def angleZeroQ (a d κ σ w ω : ℝ) : Fin 4 → ℂ :=
  ![a * w, I * ω * a * w, w * (κ + ω ^ 2 - I * ω * d), (σ + I * ω) * (κ + ω ^ 2 - I * ω * d)]

/-- The unnormalised left eigenvector `p̃ = ((d − iω)P, P, a(σ − iω), aw)`,
`P = −((σ − iω)² + w²)`. -/
def angleZeroLeft (a d σ w ω : ℝ) : Fin 4 → ℂ :=
  ![(d - I * ω) * -((σ - I * ω) ^ 2 + w ^ 2), -((σ - I * ω) ^ 2 + w ^ 2), a * (σ - I * ω), a * w]

/-- The pairing `⟨p̃, q⟩ = 2aωw(ω(2σ + d) − i(σ² + w² − 2ω² + 2σd − κ))`. -/
def angleZeroPairing (a d κ σ w ω : ℝ) : ℂ :=
  2 * a * ω * w * (ω * (2 * σ + d) - I * (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ))

/-- **The critical left eigenvector**, `p = p̃ / conj⟨p̃, q⟩`, so that `⟨p, q⟩ = 1`. -/
def angleZeroP (a d κ σ w ω : ℝ) : Fin 4 → ℂ :=
  (starRingEnd ℂ (angleZeroPairing a d κ σ w ω))⁻¹ • angleZeroLeft a d σ w ω

/-- **The critical right eigenvector at every operating angle**: the vector `angleZeroQ` of the
frame rotated with the angle `δ*`, read in the grid frame (`rotC`); `κ = Q/M`. -/
def Model.critQ (m : Model) (ω : ℝ) : Fin 4 → ℂ :=
  rotC m.δ (angleZeroQ (m.g.E / m.g.M) (m.g.D / m.g.M) (m.Q / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω)

/-- **The critical left eigenvector at every operating angle** (`⟨p, q⟩ = 1`). -/
def Model.critP (m : Model) (ω : ℝ) : Fin 4 → ℂ :=
  rotC m.δ (angleZeroP (m.g.E / m.g.M) (m.g.D / m.g.M) (m.Q / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω)

/-- **The angle term** `t = (ω₀ P_ref − σ Q)/M` (`σ = R/L`; `t = E V sin δ*/(L M)` at a balanced
point, `Line.VSM.Model.angleShift_eq`). -/
def Model.angleShift (m : Model) : ℝ := (m.g.Pref * m.g.ω0 - m.Q * (m.g.R / m.g.L)) / m.g.M

/-- **The angle term is `E V sin δ*/(L M)`** at a balanced physical model. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.angleShift_eq {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) :
    m.angleShift = m.g.E * m.g.V * Real.sin m.δ / (m.g.L * m.g.M) := by
  have hZ := hp.1.absSq_pos.ne'
  have hL := hp.1.L.ne'
  have hM := hp.2.1.ne'
  have hZ' : m.g.ω0 ^ 2 * m.g.L ^ 2 + m.g.R ^ 2 ≠ 0 := by
    have h : m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 ≠ 0 := hZ
    rwa [show m.g.ω0 ^ 2 * m.g.L ^ 2 + m.g.R ^ 2 = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 by ring]
  rw [Model.angleShift, ← hb, Model.Q, Network.qssPower_eq _ hZ, Network.qssReactive_eq _ hZ]
  simp only [Network.absSq, Network.X]
  field_simp
  linear_combination (m.g.E * m.g.V * Real.sin m.δ) * mul_inv_cancel₀ hZ'

@[tmio M, powerlib_domain] private theorem model_equilibrium {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) : m.field 0 = 0 := by
  have h := (m.field_point_eq_zero_iff hp.2.1.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
  simpa [Model.field] using h

@[tmio M, powerlib_domain] private theorem model_coeff3_pos {m : Model} (hp : Meets m .physical) :
    0 < m.g.coeff3 := by
  have hR : 0 ≤ m.g.R := hp.1.R
  have hL : 0 < m.g.L := hp.1.L
  have hM : 0 < m.g.M := hp.2.1
  have hD : 0 < m.g.D := hp.2.2
  rw [(m.coeff_atoms hL.ne').1]
  positivity

/-- **The critical pair at every operating angle**: at a frequency `ω > 0` with `ω² = a₁/a₃`,
(`Model.critQ`, `Model.critP`) is a critical pair of every balanced physical model on the Hopf
boundary (the rotated frame, `NormalForm.LyapunovCoefficient.isCriticalPair_conj`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isCriticalPair_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    IsCriticalPair m.field 0 ω (m.critQ ω) (m.critP ω) := by
  have hR := Model.R_pos_of_boundary hp hH
  obtain ⟨h1, h2⟩ := Model.freq_relations_of_boundary hp hH hω2
  obtain ⟨hJ, -, -⟩ := rot_data hp hb
  have hE := hp.1.E
  have hL := hp.1.L
  have hM := hp.2.1
  have hD := hp.2.2
  have hf : (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 = 0 := by
    simp [model_equilibrium hp hb]
  have hc := zk_isCriticalPair (by positivity) hp.1.ω0 hω (by positivity) (by positivity) h1 h2 hf
    hJ
  have h := isCriticalPair_conj (rotE m.δ).symm hc
  have e : (fun z => (rotE m.δ).symm ((fun z => rotE m.δ (m.field ((rotE m.δ).symm z)))
      ((rotE m.δ).symm.symm z))) = m.field := by
    funext z
    simp
  rw [e, map_zero, rotE_symm_mulVec, ContinuousLinearEquiv.symm_symm, rotE_transpose_mulVec] at h
  exact h

/-- **The first Lyapunov coefficient at every operating angle in closed form**: for every balanced
physical model on the Hopf boundary with `a₀ > 0` and its frequency `ω` (`ω² = a₁/a₃`),
`ℓ₁ = −a² d σ (4ω²a₀𝔅_Q + t(2(d + σ)ω² − t)𝔊)/((2σ + d)⁴ ω a₀ |r(iω)|² |r(2iω)|²)` at
(`Model.critQ`, `Model.critP`), `𝔅_Q = bautinFormQ`, `𝔊 = bautinCorr` at
`(d, σ, ω₀, κ) = (D/M, R/L, ω₀, Q/M)`, `t = Model.angleShift`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.firstLyapunov_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q) (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    firstLyapunov m.field 0 ω (m.critQ ω) (m.critP ω) =
      -((m.g.E / m.g.M) ^ 2 * (m.g.D / m.g.M) * (m.g.R / m.g.L) /
          ((2 * (m.g.R / m.g.L) + m.g.D / m.g.M) ^ 4 * ω * m.g.coeff0 m.Q *
            angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω *
            angleZeroR2 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω)) *
        (4 * ω ^ 2 * m.g.coeff0 m.Q *
            bautinFormQ (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) +
          m.angleShift * (2 * (m.g.D / m.g.M + m.g.R / m.g.L) * ω ^ 2 - m.angleShift) *
            bautinCorr (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)) := by
  have hR := Model.R_pos_of_boundary hp hH
  obtain ⟨h1, h2⟩ := Model.freq_relations_of_boundary hp hH hω2
  obtain ⟨hJ, hB, hC⟩ := rot_data hp hb
  have hE := hp.1.E
  have hL := hp.1.L
  have hM := hp.2.1
  have hD := hp.2.2
  have ha0 := (m.coeff_atoms hL.ne').2.2.2
  have ht : m.angleShift = m.g.Pref / m.g.M * m.g.ω0 - m.Q / m.g.M * (m.g.R / m.g.L) := by
    unfold Model.angleShift; ring
  rw [← firstLyapunov_conj (rotE m.δ) m.field 0 ω (m.critQ ω) (m.critP ω), map_zero]
  have hq : cmat (rotE m.δ : State 4 →L[ℝ] State 4) *ᵥ m.critQ ω =
      zkQC ((m.g.E / m.g.M : ℝ) : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ) ((m.Q / m.g.M : ℝ) : ℂ)
        ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [Model.critQ, ← rotE_symm_mulVec, Matrix.mulVec_mulVec, rotE_mul_symm, Matrix.one_mulVec]
    rfl
  have hp' : (cmat ((rotE m.δ).symm : State 4 →L[ℝ] State 4))ᵀ *ᵥ m.critP ω =
      (starRingEnd ℂ (zkCC ((m.g.E / m.g.M : ℝ) : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.Q / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I))⁻¹ •
        zkLC ((m.g.E / m.g.M : ℝ) : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ)
          (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [Model.critP, ← rotE_transpose_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      rotE_mul_symm, Matrix.transpose_one, Matrix.one_mulVec]
    rfl
  rw [hq, hp', zk_firstLyapunov (by positivity) (by positivity) (by positivity) hp.1.ω0 hω
    (by rwa [ha0] at h0) h1 h2 hJ hB hC, ha0, ht]

/-- **The symbolic boundary between sub- and supercritical Hopf points at every operating
angle**: for every critical pair of a balanced physical model on the Hopf boundary with
`a₁, a₀ > 0`, `sign ℓ₁ = −sign 𝔅_δ(D/M, R/L, ω₀, Q/M, t)` (`bautinFormAngle`,
`t = Model.angleShift = E V sin δ*/(L M)`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    {q p : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    SignType.sign (firstLyapunov m.field 0 ω q p) =
      -SignType.sign (bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
        m.angleShift) := by
  have h3 := model_coeff3_pos hp
  have hω := hcp.freq_pos
  have hω2 := m.sq_freq_of_isCriticalPair h3.ne' hcp
  have hR := Model.R_pos_of_boundary hp hH
  obtain ⟨e1, e2⟩ := Model.freq_relations_of_boundary hp hH hω2
  have hE := hp.1.E
  have hL := hp.1.L
  have hM := hp.2.1
  have hD := hp.2.2
  have ha0 := (m.coeff_atoms hL.ne').2.2.2
  rw [m.sign_firstLyapunov_eq_of_boundary h3 h1 h0 hH (Model.isCriticalPair_crit hp hb hH hω hω2)
    hcp, Model.firstLyapunov_crit hp hb hH h0 hω hω2,
    bautinFormAngle_eq e1 (show m.g.coeff0 m.Q = _ by rw [ha0]; linear_combination e2)]
  have hpos : 0 < (m.g.E / m.g.M) ^ 2 * (m.g.D / m.g.M) * (m.g.R / m.g.L) /
      ((2 * (m.g.R / m.g.L) + m.g.D / m.g.M) ^ 4 * ω * m.g.coeff0 m.Q *
        angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω *
        angleZeroR2 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω) := by
    unfold angleZeroR1 angleZeroR2
    positivity
  have h3' : 0 < (2 * (m.g.R / m.g.L) + m.g.D / m.g.M) ^ 3 := by positivity
  rw [sign_mul, sign_neg (neg_lt_zero.mpr hpos), neg_one_mul, sign_mul, sign_pos h3', one_mul]

/-! ## Connection conclusions at every operating angle -/

/-- **Supercritical points at every operating angle**: every balanced physical model on the Hopf
boundary with `a₁, a₀ > 0` and `𝔅_δ(D/M, R/L, ω₀, Q/M, t) > 0` is locally asymptotically stable
(`mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : 0 < bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨q, p, hcp⟩ := m.exists_isCriticalPair_of_boundary hp hb h1 h0 hH
  have hs := Model.sign_firstLyapunov_crit hp hb hH h1 h0 hcp
  rw [sign_pos hB] at hs
  exact mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg _ (model_coeff3_pos hp) h1 h0 hH
    hcp (sign_eq_neg_one_iff.mp hs)

/-- **Subcritical points at every operating angle**: every balanced physical model on the Hopf
boundary with `a₁, a₀ > 0` and `𝔅_δ(D/M, R/L, ω₀, Q/M, t) < 0` is unstable
(`mem_den_unstable_of_firstLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bautinFormAngle_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨q, p, hcp⟩ := m.exists_isCriticalPair_of_boundary hp hb h1 h0 hH
  have hs := Model.sign_firstLyapunov_crit hp hb hH h1 h0 hcp
  rw [sign_neg hB, neg_neg] at hs
  exact mem_den_unstable_of_firstLyapunov_pos _ (model_coeff3_pos hp) h1 h0 hH hcp
    (sign_eq_one_iff.mp hs)

/-! ## The slice `δ* = 0` as an instance -/

@[tmio M, powerlib_domain] private theorem angleZero_absSq {E V R L w M D : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical) : R ^ 2 + (w * L) ^ 2 ≠ 0 := by
  have := hp.1.L
  have := hp.1.ω0
  positivity

@[tmio M, powerlib_domain] private theorem angleZero_angleShift {E V R L w M D : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical) :
    (angleZero E V R L w M D).angleShift = 0 := by
  rw [Model.angleShift_eq hp (angleZero_balanced (angleZero_absSq hp))]
  simp [angleZero]

/-- **The critical pair of a boundary point of the slice**: at a frequency `ω > 0` with
`ω² = a₁/a₃`, the pair (`angleZeroQ`, `angleZeroP`) is a critical pair of a physical boundary
model of the slice (the instance `δ* = 0` of `Line.VSM.Model.isCriticalPair_crit`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleZero_isCriticalPair {E V R L w M D ω : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q /
      (angleZero E V R L w M D).g.coeff3) :
    IsCriticalPair (angleZero E V R L w M D).field 0 ω
      (angleZeroQ (E / M) (D / M) ((angleZero E V R L w M D).Q / M) (R / L) w ω)
      (angleZeroP (E / M) (D / M) ((angleZero E V R L w M D).Q / M) (R / L) w ω) := by
  have h := Model.isCriticalPair_crit hp (angleZero_balanced (angleZero_absSq hp)) hH hω hω2
  rwa [Model.critQ, Model.critP, show (angleZero E V R L w M D).δ = 0 from rfl, rotC_zero,
    rotC_zero] at h

/-- **The first Lyapunov coefficient of the slice in closed form**: for every physical boundary
model with `a₀ > 0` and its frequency `ω` (`ω² = a₁/a₃`),
`ℓ₁ = −4 a² d σ ω 𝔅_Q(d, σ, ω₀, κ) / ((2σ + d)⁴ |r(iω)|² |r(2iω)|²)` at the critical pair
(`angleZeroQ`, `angleZeroP`) (the instance `δ* = 0`, `t = 0` of
`Line.VSM.Model.firstLyapunov_crit`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleZero_firstLyapunov {E V R L w M D ω : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q)
    (h0 : 0 < (angleZero E V R L w M D).g.coeff0 (angleZero E V R L w M D).Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q /
      (angleZero E V R L w M D).g.coeff3) :
    firstLyapunov (angleZero E V R L w M D).field 0 ω
        (angleZeroQ (E / M) (D / M) ((angleZero E V R L w M D).Q / M) (R / L) w ω)
        (angleZeroP (E / M) (D / M) ((angleZero E V R L w M D).Q / M) (R / L) w ω) =
      -(4 * (E / M) ^ 2 * (D / M) * (R / L) * ω /
          ((2 * (R / L) + D / M) ^ 4 *
            angleZeroR1 (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) ω *
            angleZeroR2 (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) ω)) *
        bautinFormQ (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) := by
  have h := Model.firstLyapunov_crit hp (angleZero_balanced (angleZero_absSq hp)) hH h0 hω hω2
  rw [Model.critQ, Model.critP, show (angleZero E V R L w M D).δ = 0 from rfl, rotC_zero,
    rotC_zero, angleZero_angleShift hp, show (angleZero E V R L w M D).g.E = E from rfl,
    show (angleZero E V R L w M D).g.M = M from rfl,
    show (angleZero E V R L w M D).g.D = D from rfl,
    show (angleZero E V R L w M D).g.R = R from rfl,
    show (angleZero E V R L w M D).g.L = L from rfl,
    show (angleZero E V R L w M D).g.ω0 = w from rfl] at h
  rw [h]
  have hR1 : 0 < angleZeroR1 (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) ω := by
    unfold angleZeroR1
    have := hp.2.1
    have := hp.2.2
    have := hp.1.L
    have := Model.R_pos_of_boundary hp hH
    positivity
  have hR2 : 0 < angleZeroR2 (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) ω := by
    unfold angleZeroR2
    have := hp.2.1
    have := hp.2.2
    have := hp.1.L
    have := Model.R_pos_of_boundary hp hH
    positivity
  have hα : 0 < 2 * (R / L) + D / M := by
    have := hp.2.1
    have := hp.2.2
    have := hp.1.L
    have := Model.R_pos_of_boundary hp hH
    positivity
  have ha0 := h0.ne'
  have hω' := hω.ne'
  have := hp.2.1
  have := hp.1.L
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem sign_bautinFormAngle_zero {m : Model}
    (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q) :
    SignType.sign (bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) 0) =
      SignType.sign (bautinFormQ (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)) := by
  obtain ⟨c3, c2, c1, -⟩ := m.coeff_atoms hp.1.L.ne'
  have h3 := model_coeff3_pos hp
  have hβ : 0 < m.g.coeff3 * m.g.coeff2 m.Q - m.g.coeff1 m.Q := by
    refine pos_of_mul_pos_right ?_ h1.le
    rw [show m.g.coeff1 m.Q * (m.g.coeff3 * m.g.coeff2 m.Q - m.g.coeff1 m.Q) =
      m.g.coeff3 ^ 2 * m.g.coeff0 m.Q by linear_combination hH]
    positivity
  have e : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) 0 =
      (4 * m.g.coeff1 m.Q ^ 2 * (m.g.coeff3 * m.g.coeff2 m.Q - m.g.coeff1 m.Q)) *
        bautinFormQ (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) := by
    rw [c3, c2, c1]
    unfold bautinFormAngle
    ring
  rw [e, sign_mul, sign_pos (by positivity), one_mul]

/-- **The symbolic boundary between sub- and supercritical Hopf points of the slice**: for every
critical pair of a physical boundary model with `a₁, a₀ > 0`,
`sign ℓ₁ = −sign 𝔅_Q(D/M, R/L, ω₀, Q/M)` (the instance `δ* = 0` of
`Line.VSM.Model.sign_firstLyapunov_crit`: `t = 0`, `𝔅_δ = 4a₁²(a₃a₂ − a₁)𝔅_Q`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem angleZero_sign_firstLyapunov {E V R L w M D ω : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q)
    (h1 : 0 < (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q)
    (h0 : 0 < (angleZero E V R L w M D).g.coeff0 (angleZero E V R L w M D).Q)
    {q p : Fin 4 → ℂ} (hcp : IsCriticalPair (angleZero E V R L w M D).field 0 ω q p) :
    SignType.sign (firstLyapunov (angleZero E V R L w M D).field 0 ω q p) =
      -SignType.sign (bautinFormQ (D / M) (R / L) w ((angleZero E V R L w M D).Q / M)) := by
  have h := Model.sign_firstLyapunov_crit hp (angleZero_balanced (angleZero_absSq hp)) hH h1 h0
    hcp
  rw [angleZero_angleShift hp, sign_bautinFormAngle_zero hp hH h1 h0] at h
  exact h

/-- **Supercritical points of the slice**: every physical boundary model of the slice with
`a₁, a₀ > 0` and `𝔅_Q(D/M, R/L, ω₀, Q/M) > 0` is locally asymptotically stable (the instance
`δ* = 0` of `mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos`). -/
@[tmio TM, powerlib_domain] theorem angleZero_mem_den_locallyAsymptoticallyStable
    {E V R L w M D : ℝ} (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q)
    (h1 : 0 < (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q)
    (h0 : 0 < (angleZero E V R L w M D).g.coeff0 (angleZero E V R L w M D).Q)
    (hB : 0 < bautinFormQ (D / M) (R / L) w ((angleZero E V R L w M D).Q / M)) :
    connection% (angleZero E V R L w M D ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  refine mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos _ hp
    (angleZero_balanced (angleZero_absSq hp)) hH h1 h0 ?_
  rw [angleZero_angleShift hp, ← sign_eq_one_iff, sign_bautinFormAngle_zero hp hH h1 h0]
  exact sign_pos hB

/-- **Subcritical points of the slice**: every physical boundary model of the slice with
`a₁, a₀ > 0` and `𝔅_Q(D/M, R/L, ω₀, Q/M) < 0` is unstable (the instance `δ* = 0` of
`mem_den_unstable_of_bautinFormAngle_neg`). -/
@[tmio TM, powerlib_domain] theorem angleZero_mem_den_unstable {E V R L w M D : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q)
    (h1 : 0 < (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q)
    (h0 : 0 < (angleZero E V R L w M D).g.coeff0 (angleZero E V R L w M D).Q)
    (hB : bautinFormQ (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) < 0) :
    connection% (angleZero E V R L w M D ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable_of_bautinFormAngle_neg _ hp (angleZero_balanced (angleZero_absSq hp))
    hH h1 h0 ?_
  rw [angleZero_angleShift hp, ← sign_eq_neg_one_iff, sign_bautinFormAngle_zero hp hH h1 h0]
  exact sign_neg hB

/-! ## The angle term decides the criticality

Two physical balanced models on the Hopf boundary with the same monic quartic
`s⁴ + (9/4)s³ + (9/2)s² + (9/2)s + 5 = (s² + 2)(s² + (9/4)s + 5/2)` (the same atoms
`a = b = 1`, `d = 1/4`, `σ = ω₀ = 1`, `κ = −2`, and the same `K = P'(δ*) = 5/2`): the slice point
`angleZero 1 5 1 1 1 1 (1/4)` (`t = 0`, `𝔅_Q < 0`) is unstable, the point `angleWitness` at
`δ* = arctan(4/3)` (`t = 20/7`, `𝔅_δ > 0`) is locally asymptotically stable. -/

/-- **A boundary point at a non-zero angle**: `E = 1`, `V = 25/7`, `R = L = ω₀ = M = 1`,
`D = 1/4`, `P_ref = P(δ*) = 6/7`, `δ* = arctan(4/3)` (`cos δ* = 3/5`, `sin δ* = 4/5`); `Q = −2`,
`t = 20/7`. -/
def angleWitness : Model := ⟨⟨⟨1, 25 / 7, 1, 1, 1⟩, 1, 1 / 4, 6 / 7⟩, Real.arctan (4 / 3)⟩

@[tmio M, powerlib_domain] private theorem angleWitness_trig :
    Real.cos angleWitness.δ = 3 / 5 ∧ Real.sin angleWitness.δ = 4 / 5 := by
  have h : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show (1 + (4 / 3 : ℝ) ^ 2) = (5 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [show angleWitness.δ = Real.arctan (4 / 3) from rfl, Real.cos_arctan, h]
    norm_num
  · rw [show angleWitness.δ = Real.arctan (4 / 3) from rfl, Real.sin_arctan, h]
    norm_num

/-- The witness is physical and balanced, with `Q = −2` and the angle term `t = 20/7`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleWitness_meets :
    Meets angleWitness .physical ∧ Meets angleWitness .balanced ∧ angleWitness.Q = -2 ∧
      angleWitness.angleShift = 20 / 7 := by
  obtain ⟨hc, hs⟩ := angleWitness_trig
  have hZ : angleWitness.g.absSq ≠ 0 := by norm_num [angleWitness, Network.absSq, Network.X]
  have hp : Meets angleWitness .physical :=
    ⟨⟨by norm_num [angleWitness], by norm_num [angleWitness], by norm_num [angleWitness],
      by norm_num [angleWitness], by norm_num [angleWitness]⟩,
      by norm_num [angleWitness], by norm_num [angleWitness]⟩
  have hb : Meets angleWitness .balanced := by
    show angleWitness.g.qssPower angleWitness.δ = angleWitness.g.Pref
    rw [Network.qssPower_eq _ hZ, hc, hs]
    norm_num [angleWitness, Network.absSq, Network.X]
  have hQ : angleWitness.Q = -2 := by
    rw [Model.Q, Network.qssReactive_eq _ hZ, hc, hs]
    norm_num [angleWitness, Network.absSq, Network.X]
  refine ⟨hp, hb, hQ, ?_⟩
  rw [Model.angleShift_eq hp hb, hs]
  norm_num [angleWitness]

/-- **The two models have the same monic quartic**: `a₃ = 9/4`, `a₂ = a₁ = 9/2`, `a₀ = 5` for the
witness and for the slice point `angleZero 1 5 1 1 1 1 (1/4)`, both on the Hopf boundary
(`(9/4)(9/2)(9/2) = (9/2)² + (9/4)² 5`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleWitness_coeffs :
    (angleWitness.g.coeff3 = 9 / 4 ∧ angleWitness.g.coeff2 angleWitness.Q = 9 / 2 ∧
      angleWitness.g.coeff1 angleWitness.Q = 9 / 2 ∧ angleWitness.g.coeff0 angleWitness.Q = 5) ∧
    ((angleZero 1 5 1 1 1 1 (1 / 4)).g.coeff3 = 9 / 4 ∧
      (angleZero 1 5 1 1 1 1 (1 / 4)).g.coeff2 (angleZero 1 5 1 1 1 1 (1 / 4)).Q = 9 / 2 ∧
      (angleZero 1 5 1 1 1 1 (1 / 4)).g.coeff1 (angleZero 1 5 1 1 1 1 (1 / 4)).Q = 9 / 2 ∧
      (angleZero 1 5 1 1 1 1 (1 / 4)).g.coeff0 (angleZero 1 5 1 1 1 1 (1 / 4)).Q = 5) := by
  obtain ⟨-, -, hQ, -⟩ := angleWitness_meets
  have hQ0 : (angleZero 1 5 1 1 1 1 (1 / 4)).Q = -2 := by
    rw [angleZero_Q (by norm_num)]
    norm_num
  obtain ⟨a3, a2, a1, a0⟩ := angleWitness.coeff_atoms (by norm_num [angleWitness])
  obtain ⟨b3, b2, b1, b0⟩ := (angleZero 1 5 1 1 1 1 (1 / 4)).coeff_atoms (by norm_num [angleZero])
  rw [a3, a2, a1, a0, b3, b2, b1, b0, hQ, hQ0]
  norm_num [angleWitness, angleZero]

/-- **The non-zero angle stabilises**: the witness at `δ* = arctan(4/3)` is locally
asymptotically stable (`𝔅_δ(1/4, 1, 1, −2, 20/7) > 0`,
`mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos`), whereas the slice point with the
same quartic is unstable (`angleWitnessTwin_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem angleWitness_mem_den_locallyAsymptoticallyStable :
    connection% (angleWitness ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨hp, hb, hQ, ht⟩ := angleWitness_meets
  obtain ⟨⟨c3, c2, c1, c0⟩, -⟩ := angleWitness_coeffs
  refine mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos _ hp hb
    (by rw [c3, c2, c1, c0]; norm_num) (by rw [c1]; norm_num) (by rw [c0]; norm_num) ?_
  rw [hQ, ht]
  norm_num [angleWitness, bautinFormAngle, bautinFormQ, bautinCorr]

/-- **The slice point with the same quartic is unstable** (`𝔅_Q(1/4, 1, 1, −2) < 0`,
`angleZero_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem angleWitnessTwin_mem_den_unstable :
    connection% (angleZero 1 5 1 1 1 1 (1 / 4) ∈ family.den (.flow .unstable)) := by
  obtain ⟨-, ⟨c3, c2, c1, c0⟩⟩ := angleWitness_coeffs
  have hQ0 : (angleZero 1 5 1 1 1 1 (1 / 4)).Q = -2 := by
    rw [angleZero_Q (by norm_num)]
    norm_num
  refine angleZero_mem_den_unstable
    ⟨⟨by norm_num [angleZero], by norm_num [angleZero], by norm_num [angleZero],
      by norm_num [angleZero], by norm_num [angleZero]⟩, by norm_num [angleZero],
      by norm_num [angleZero]⟩
    (by rw [c3, c2, c1, c0]; norm_num) (by rw [c1]; norm_num) (by rw [c0]; norm_num) ?_
  rw [hQ0]
  norm_num [bautinFormQ]

end VSM
end powerlib.GFM.Line
