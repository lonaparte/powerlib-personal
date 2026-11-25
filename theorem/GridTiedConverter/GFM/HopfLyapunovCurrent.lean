import theorem.GridTiedConverter.GFM.HopfLineInstability

/-! # The boundary between sub- and supercritical Hopf points of the VSM on a line at `δ* = 0`

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* The slice: the models read at the angle `δ* = 0`, `Line.VSM.angleZero E V R L ω₀ M D` (grid
  voltage `V`, `P_ref = P(0) = E(E − V)R/|Z|²`, so that `δ* = 0` is balanced for every parameter
  set); the line current at the operating point is `(E − V)/Z`, the reactive power
  `Q = E(E − V)X/|Z|²` (`angleZero_point`, `angleZero_Q`). Physical range `E, V, L, ω₀, M, D > 0`,
  `R ≥ 0`. `V = E` is the zero-current slice
  (`theorem/GridTiedConverter/GFM/HopfLyapunovSymbolic.lean`).
  Not covered: `δ* ≠ 0`.
* Notation: `a = E/M`, `b = E/L`, `d = D/M`, `σ = R/L`, `κ = Q/M`, `ν = E i_d/M`, `ρ = σ² + ω₀²`.
  The Jacobian is `[[0, 1, 0, 0], [κ, −d, −a, 0], [0, 0, −σ, ω₀], [b, 0, −ω₀, −σ]]`, the monic
  quartic has `a₃ = 2σ + d`, `a₂ = ρ + 2σd − κ`, `a₁ = dρ − 2σκ`, `a₀ = abω₀ − κρ`.
* Level: exact identities and signs for all parameters of the slice, and Lyapunov instability /
  local asymptotic stability of the operating point (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`). Not stated: the bifurcating cycles, the degenerate points
  `𝔅_Q = 0` themselves.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, the VSM without filter on a dynamic
R–L line); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4
(`NormalForm.LyapunovCoefficient.firstLyapunov`); Carr, *Applications of Centre Manifold Theory*
(1981), §2.4. The closed form was derived with SymPy in exact rational arithmetic (Gröbner
reduction modulo the boundary relations, exact division, factorisation over `ℚ`; untrusted
discovery); every identity is proved here by `linear_combination` with its polynomial
certificate. The family laws are `theorem/GridTiedConverter/GFM/HopfLineInstability.lean`.

Results.
* The slice: `Line.VSM.angleZero`, `angleZero_point`, `angleZero_balanced`, `angleZero_Q`,
  `angleZero_coeffs`, `angleZero_jacobianC`; the derivatives at a current-carrying operating
  point (`δ* = 0`) of any parameter set, `bilinC_field_angle_zero`
  (`B(u, v) = (0, −a(u₀v₃ + u₃v₀) + (E i_d/M) u₀v₀, −b u₀v₀, 0)`) and
  `trilinC_field_angle_zero` (`C(u, v, z) = (0, a(u₀v₀z₂ + u₀v₂z₀ + u₂v₀z₀) + (E i_q/M) u₀v₀z₀,
  0, −b u₀v₀z₀)`), and their reading on the slice `angleZero_bilinC`, `angleZero_trilinC`.
* `angleZero_R_pos` (the boundary forces `R > 0`), `angleZero_freq_relations`: at a frequency
  `ω² = a₁/a₃` of a boundary point, `d(ρ − ω²) = 2σ(κ + ω²)`, `abω₀ = κρ + ω²(ρ − ω² + 2σd − κ)`
  (and `νω₀ = κσ` for `ν = E i_d/M`).
* The critical pair `angleZeroQ` (`q = (aω₀, iωaω₀, ω₀(κ + ω² − iωd), (σ + iω)(κ + ω² − iωd))`),
  `angleZeroLeft`, `angleZeroPairing`, `angleZeroP`; `angleZero_isCriticalPair`.
* **`ℓ₁` in closed form**: `angleZero_firstLyapunov`,
  `ℓ₁ = −4 a² d σ ω 𝔅_Q(d, σ, ω₀, κ) / ((2σ + d)⁴ |r(iω)|² |r(2iω)|²)`, `r(z) = z² + (2σ + d) z +
  ρ − ω² + 2σd − κ` the stable factor (`angleZeroR1`, `angleZeroR2`), `𝔅_Q = bautinFormQ` a
  polynomial in the model parameters (degree 4 in `κ`).
* **The symbolic boundary between sub- and supercritical**: `angleZero_sign_firstLyapunov` (every
critical
  pair of every physical boundary model with `a₁, a₀ > 0`: `sign ℓ₁ = −sign 𝔅_Q(D/M, R/L, ω₀,
  Q/M)`).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* `Line.VSM.angleZero_mem_den_locallyAsymptoticallyStable` (`𝔅_Q > 0`: supercritical) and
  `Line.VSM.angleZero_mem_den_unstable` (`𝔅_Q < 0`: subcritical), for every physical model of the
  slice on the Hopf boundary with `a₁, a₀ > 0`.
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

/-- The coefficients of the monic quartic: `a₃ = 2σ + d`, `a₂ = ρ + 2σd − κ`, `a₁ = dρ − 2σκ`,
`a₀ = abω₀ − κρ` (`κ = Q/M`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleZero_coeffs {E V R L w M D : ℝ} (hL : L ≠ 0) :
    (angleZero E V R L w M D).g.coeff3 = 2 * (R / L) + D / M ∧
      (angleZero E V R L w M D).g.coeff2 (angleZero E V R L w M D).Q =
        (R / L) ^ 2 + w ^ 2 + 2 * (R / L) * (D / M) - (angleZero E V R L w M D).Q / M ∧
      (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q =
        D / M * ((R / L) ^ 2 + w ^ 2) - 2 * (R / L) * ((angleZero E V R L w M D).Q / M) ∧
      (angleZero E V R L w M D).g.coeff0 (angleZero E V R L w M D).Q =
        E / M * (E / L) * w - (angleZero E V R L w M D).Q / M * ((R / L) ^ 2 + w ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [coeff3, coeff2, coeff1, coeff0, angleZero, Network.ρ, Network.σ, Network.X]
  all_goals field_simp
  all_goals ring

/-- The complexified Jacobian at the operating point,
`[[0, 1, 0, 0], [κ, −d, −a, 0], [0, 0, −σ, ω₀], [b, 0, −ω₀, −σ]]`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem angleZero_jacobianC {E V R L w M D : ℝ} (hL : L ≠ 0) :
    jacobianC (angleZero E V R L w M D).field 0 =
      !![0, 1, 0, 0; (((angleZero E V R L w M D).Q / M : ℝ) : ℂ), -((D / M : ℝ) : ℂ),
        -((E / M : ℝ) : ℂ), 0; 0, 0, -((R / L : ℝ) : ℂ), (w : ℂ);
        ((E / L : ℝ) : ℂ), 0, -(w : ℂ), -((R / L : ℝ) : ℂ)] := by
  have hL' : (L : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL
  rw [Model.jacobianC_field]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Linear.complexify, Model.jac, jacobian, angleZero, Model.Q, Network.qssReactive,
      Network.X] <;>
    field_simp

/-! ## Derivatives at a current-carrying operating point -/

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

/-- **The second derivative at a state with angle `0`** (any current `(x₀ 2, x₀ 3)`):
`B(u, w) = (0, −(E/M)(u₀w₃ + u₃w₀) + (E x₀₂/M) u₀w₀, −(E/L) u₀w₀, 0)` (generic laws
`bilinC_ridge`, `bilinC_prodRidge`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bilinC_field_angle_zero (g : VSM) {x₀ : State 4}
    (h0 : x₀ 0 = 0) (u w : Fin 4 → ℂ) :
    bilinC g.field x₀ u w =
      ![0, -((g.E / g.M : ℝ) : ℂ) * (u 0 * w 3 + u 3 * w 0) +
          ((g.E * x₀ 2 / g.M : ℝ) : ℂ) * (u 0 * w 0), -((g.E / g.L : ℝ) : ℂ) * (u 0 * w 0), 0] := by
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
    fin_cases i <;> simp [toC, h0] <;> ring
  all_goals first | exact c1.of_le k2 | exact c2.of_le k2 | exact c3.of_le k2 |
    exact c4.of_le k2 | exact (c1.add c2).of_le k2 | exact ((c1.add c2).add c3).of_le k2

/-- **The third derivative at a state with angle `0`**:
`C(u, w, z) = (0, (E/M)(u₀w₀z₂ + u₀w₂z₀ + u₂w₀z₀) + (E x₀₃/M) u₀w₀z₀, 0, −(E/L) u₀w₀z₀)`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem trilinC_field_angle_zero (g : VSM) {x₀ : State 4}
    (h0 : x₀ 0 = 0) (u w z : Fin 4 → ℂ) :
    trilinC g.field x₀ u w z =
      ![0, ((g.E / g.M : ℝ) : ℂ) * (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0) +
          ((g.E * x₀ 3 / g.M : ℝ) : ℂ) * (u 0 * w 0 * z 0), 0,
        -((g.E / g.L : ℝ) : ℂ) * (u 0 * w 0 * z 0)] := by
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
    fin_cases i <;> simp [toC, h0] <;> ring
  all_goals first | exact c1 | exact c2 | exact c3 | exact c4 | exact c1.add c2 |
    exact (c1.add c2).add c3

@[tmio M, powerlib_domain] private theorem angleZero_hess (E V R L w M D : ℝ) :
    hess (angleZero E V R L w M D).field 0 =
      hess (angleZero E V R L w M D).g.field (angleZero E V R L w M D).point := by
  funext k i j
  show iteratedFDeriv ℝ 2 (fun z => (angleZero E V R L w M D).g.field
    (z + (angleZero E V R L w M D).point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, hess]

@[tmio M, powerlib_domain] private theorem angleZero_third (E V R L w M D : ℝ) :
    third (angleZero E V R L w M D).field 0 =
      third (angleZero E V R L w M D).g.field (angleZero E V R L w M D).point := by
  funext k i j l
  show iteratedFDeriv ℝ 3 (fun z => (angleZero E V R L w M D).g.field
    (z + (angleZero E V R L w M D).point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, third]

/-- The second derivative of the model field at the operating point. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem angleZero_bilinC (E V R L w M D : ℝ) (u v : Fin 4 → ℂ) :
    bilinC (angleZero E V R L w M D).field 0 u v =
      ![0, -((E / M : ℝ) : ℂ) * (u 0 * v 3 + u 3 * v 0) +
          ((E * ((E - V) * R / (R ^ 2 + (w * L) ^ 2)) / M : ℝ) : ℂ) * (u 0 * v 0),
        -((E / L : ℝ) : ℂ) * (u 0 * v 0), 0] := by
  have hb : bilinC (angleZero E V R L w M D).field 0 =
      bilinC (angleZero E V R L w M D).g.field (angleZero E V R L w M D).point := by
    unfold bilinC
    rw [angleZero_hess]
  rw [hb, bilinC_field_angle_zero _ (by simp [angleZero_point])]
  simp only [angleZero_point]
  rfl

/-- The third derivative of the model field at the operating point. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem angleZero_trilinC (E V R L w M D : ℝ) (u v z : Fin 4 → ℂ) :
    trilinC (angleZero E V R L w M D).field 0 u v z =
      ![0, ((E / M : ℝ) : ℂ) * (u 0 * v 0 * z 2 + u 0 * v 2 * z 0 + u 2 * v 0 * z 0) +
          ((E * (-((E - V) * (w * L)) / (R ^ 2 + (w * L) ^ 2)) / M : ℝ) : ℂ) * (u 0 * v 0 * z 0),
        0, -((E / L : ℝ) : ℂ) * (u 0 * v 0 * z 0)] := by
  have ht : trilinC (angleZero E V R L w M D).field 0 =
      trilinC (angleZero E V R L w M D).g.field (angleZero E V R L w M D).point := by
    unfold trilinC
    rw [angleZero_third]
  rw [ht, trilinC_field_angle_zero _ (by simp [angleZero_point])]
  simp only [angleZero_point]
  rfl


/-! ## The Hopf boundary of the slice -/

/-- **The boundary forces a resistive line**: a physical model of the slice on the Hopf boundary
has `R > 0` (the lossless line has a negative third Hurwitz determinant,
`Line.VSM.hurwitzDet_of_lossless`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleZero_R_pos {E V R L w M D : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q) : 0 < R := by
  obtain ⟨hN, hM, hD⟩ := hp
  have hR0 : 0 ≤ R := hN.R
  rcases hR0.lt_or_eq with hR | hR
  · exact hR
  · exfalso
    have h := (angleZero E V R L w M D).g.hurwitzDet_of_lossless hR.symm hM.ne' hN.L.ne'
      (angleZero E V R L w M D).Q
    rw [hH, sub_self] at h
    have hX := hN.X_pos
    have hE := hN.E
    have hL := hN.L
    have : 0 < (angleZero E V R L w M D).g.D ^ 2 * (angleZero E V R L w M D).g.E ^ 2 *
        (angleZero E V R L w M D).g.X / ((angleZero E V R L w M D).g.L ^ 2 *
          (angleZero E V R L w M D).g.M ^ 3) := by positivity
    linarith

/-- **The frequency relations**: at a frequency with `ω² = a₁/a₃` a physical model of the slice on
the Hopf boundary satisfies `d(ρ − ω²) = 2σ(κ + ω²)` and `abω₀ = κρ + ω²(ρ − ω² + 2σd − κ)`
(`κ = Q/M`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem angleZero_freq_relations {E V R L w M D ω : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q)
    (hω2 : ω ^ 2 = (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q /
      (angleZero E V R L w M D).g.coeff3) :
    D / M * ((R / L) ^ 2 + w ^ 2 - ω ^ 2) =
        2 * (R / L) * ((angleZero E V R L w M D).Q / M + ω ^ 2) ∧
      E / M * (E / L) * w = (angleZero E V R L w M D).Q / M * ((R / L) ^ 2 + w ^ 2) +
        ω ^ 2 * ((R / L) ^ 2 + w ^ 2 - ω ^ 2 + 2 * (R / L) * (D / M) -
          (angleZero E V R L w M D).Q / M) := by
  have hR := angleZero_R_pos hp hH
  obtain ⟨hN, hM', hD'⟩ := hp
  have hL : 0 < L := hN.L
  have hM : 0 < M := hM'
  have hD : 0 < D := hD'
  obtain ⟨h3, h2, h1, h0⟩ := angleZero_coeffs (E := E) (V := V) (R := R) (w := w) (M := M)
    (D := D) hL.ne'
  set κ := (angleZero E V R L w M D).Q / M with hκ
  have h3p : 0 < 2 * (R / L) + D / M := by positivity
  rw [h3, h2, h1, h0] at hH
  rw [h3, h1, eq_div_iff h3p.ne'] at hω2
  refine ⟨by linear_combination -hω2, ?_⟩
  have h3n : (2 * (R / L) + D / M) ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ h3n
  linear_combination -hH + (D / M * ((R / L) ^ 2 + w ^ 2) - 2 * (R / L) * κ +
    (2 * (R / L) + D / M) * ω ^ 2 - (2 * (R / L) + D / M) * ((R / L) ^ 2 + w ^ 2 +
      2 * (R / L) * (D / M) - κ)) * hω2

/-! ## The polynomials of the closed form -/

/-- **The Bautin form of the slice** in the model parameters `d = D/M`, `σ = R/L`, `w = ω₀`,
`κ = Q/M` (degree 4 in `κ`; `ℓ₁` has the sign of `−bautinFormQ`). -/
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

/-- `|r(iω)|²` for the stable factor `r(z) = z² + (2σ + d) z + σ² + ω₀² − ω² + 2σd − κ`. -/
def angleZeroR1 (d σ w κ ω : ℝ) : ℝ :=
  (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ) ^ 2 + ω ^ 2 * (2 * σ + d) ^ 2

/-- `|r(2iω)|²` for the stable factor `r(z) = z² + (2σ + d) z + σ² + ω₀² − ω² + 2σd − κ`. -/
def angleZeroR2 (d σ w κ ω : ℝ) : ℝ :=
  (σ ^ 2 + w ^ 2 - 5 * ω ^ 2 + 2 * σ * d - κ) ^ 2 + 4 * ω ^ 2 * (2 * σ + d) ^ 2

/-! ## Exact algebra of the critical data

The Jacobian pattern, the critical eigenvectors and the resolvent solutions as polynomial vectors
in complex atoms `A = a`, `B = b`, `D = d`, `S = σ`, `W = ω₀`, `O = ω`, `K = κ`, `N = ν` and a
square root `j` of `−1`, under the relations `h0 : NW = KS`, `h1 : D(S² + W² − O²) = 2S(K + O²)`,
`h2 : ABW = K(S² + W²) + O²(S² + W² − O² + 2SD − K)`; every identity is checked by
`linear_combination` with its polynomial certificate (exponents typed `ℕ` for elaboration). -/

/-- The Jacobian pattern at `δ* = 0` with a line current (`K = Q/M`). -/
private def zkJ (A B D K S W : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; K, -D, -A, 0; 0, 0, -S, W; B, 0, -W, -S]

/-- The second-derivative pattern (`N = E i_d/M`). -/
private def zkBil (A B N : ℂ) (u v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![0, -A * (u 0 * v 3 + u 3 * v 0) + N * (u 0 * v 0), -B * (u 0 * v 0), 0]

/-- The third-derivative pattern (`E i_q/M = −K`). -/
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

private def zkRC (A D K S W O : ℂ) : Fin 4 → ℂ :=
  ![2 * A ^ (2:ℕ) * D * W ^ (3:ℕ) * O ^ (2:ℕ) + A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) + A ^ (2:ℕ) *
    S * W ^ (3:ℕ) * O ^ (2:ℕ) + A ^ (2:ℕ) * S * W * O ^ (4:ℕ) + A ^ (2:ℕ) * S * W * O ^ (2:ℕ) * K,
    0, 4 * A * D ^ (2:ℕ) * S * W * O ^ (4:ℕ) - 4 * A * D * W ^ (3:ℕ) * O ^ (4:ℕ) + 4 * A * D * W *
    O ^ (6:ℕ) + 2 * A * S ^ (3:ℕ) * W * O ^ (4:ℕ) + 2 * A * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K + 2 * A *
    S * W ^ (3:ℕ) * O ^ (4:ℕ) + 2 * A * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 10 * A * S * W * O ^ (6:ℕ) +
    14 * A * S * W * O ^ (4:ℕ) * K + 4 * A * S * W * O ^ (2:ℕ) * K ^ (2:ℕ), -4 * A * D * S *
    W ^ (2:ℕ) * O ^ (4:ℕ) + 4 * A * D * S * O ^ (6:ℕ) + 2 * A * D * S * O ^ (4:ℕ) * K + A *
    S ^ (4:ℕ) * O ^ (4:ℕ) + A * S ^ (4:ℕ) * O ^ (2:ℕ) * K + 4 * A * S ^ (2:ℕ) * O ^ (6:ℕ) + 5 * A *
    S ^ (2:ℕ) * O ^ (4:ℕ) * K + A * S ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - A * W ^ (4:ℕ) * O ^ (4:ℕ) -
    A * W ^ (4:ℕ) * O ^ (2:ℕ) * K + 2 * A * W ^ (2:ℕ) * O ^ (6:ℕ) + 3 * A * W ^ (2:ℕ) * O ^ (4:ℕ) *
    K + A * W ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - A * O ^ (8:ℕ) - 2 * A * O ^ (6:ℕ) * K - A *
    O ^ (4:ℕ) * K ^ (2:ℕ)]

/-- `zkDC` times the solution of `(2iω − J) s = B(q, q)`. -/
private def zkSC (A D K S W O j : ℂ) : Fin 4 → ℂ :=
  ![-10 * A ^ (2:ℕ) * D * S * W * O ^ (3:ℕ) * j + 6 * A ^ (2:ℕ) * D * W ^ (3:ℕ) * O ^ (2:ℕ) -
    A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) - 4 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j -
    A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (2:ℕ) * S * W * O ^ (4:ℕ) - 5 * A ^ (2:ℕ) * S * W *
    O ^ (2:ℕ) * K + 6 * A ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 6 * A ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j, 20 *
    A ^ (2:ℕ) * D * S * W * O ^ (4:ℕ) + 12 * A ^ (2:ℕ) * D * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 2 *
    A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j + 8 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) - 2 *
    A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 2 * A ^ (2:ℕ) * S * W * O ^ (5:ℕ) * j - 10 *
    A ^ (2:ℕ) * S * W * O ^ (3:ℕ) * K * j - 12 * A ^ (2:ℕ) * W * O ^ (6:ℕ) - 12 * A ^ (2:ℕ) * W *
    O ^ (4:ℕ) * K, 4 * A * D ^ (2:ℕ) * S * W * O ^ (4:ℕ) + 12 * A * D * S * W * O ^ (5:ℕ) * j - 4 *
    A * D * W ^ (3:ℕ) * O ^ (4:ℕ) + 4 * A * D * W * O ^ (6:ℕ) + 2 * A * S ^ (3:ℕ) * W * O ^ (4:ℕ) +
    2 * A * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K + 6 * A * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 6 * A *
    S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j + 2 * A * S * W ^ (3:ℕ) * O ^ (4:ℕ) + 2 * A * S * W ^ (3:ℕ) *
    O ^ (2:ℕ) * K + 10 * A * S * W * O ^ (6:ℕ) + 14 * A * S * W * O ^ (4:ℕ) * K + 4 * A * S * W *
    O ^ (2:ℕ) * K ^ (2:ℕ) + 6 * A * W ^ (3:ℕ) * O ^ (5:ℕ) * j + 6 * A * W ^ (3:ℕ) * O ^ (3:ℕ) * K *
    j - 6 * A * W * O ^ (7:ℕ) * j - 6 * A * W * O ^ (5:ℕ) * K * j, -4 * A * D ^ (2:ℕ) * S *
    O ^ (5:ℕ) * j + 8 * A * D ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) - 8 * A * D ^ (2:ℕ) * O ^ (6:ℕ) - 4 *
    A * D * S * W ^ (2:ℕ) * O ^ (4:ℕ) - 12 * A * D * S * O ^ (6:ℕ) - 10 * A * D * S * O ^ (4:ℕ) * K
    + 4 * A * D * W ^ (2:ℕ) * O ^ (5:ℕ) * j - 4 * A * D * O ^ (7:ℕ) * j - A * S ^ (4:ℕ) * O ^ (4:ℕ)
    - A * S ^ (4:ℕ) * O ^ (2:ℕ) * K - 2 * A * S ^ (3:ℕ) * O ^ (5:ℕ) * j - 2 * A * S ^ (3:ℕ) *
    O ^ (3:ℕ) * K * j - 4 * A * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (4:ℕ) - 4 * A * S ^ (2:ℕ) * W ^ (2:ℕ) *
    O ^ (2:ℕ) * K - 8 * A * S ^ (2:ℕ) * O ^ (6:ℕ) - 13 * A * S ^ (2:ℕ) * O ^ (4:ℕ) * K - 5 * A *
    S ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - 2 * A * S * W ^ (2:ℕ) * O ^ (5:ℕ) * j - 2 * A * S *
    W ^ (2:ℕ) * O ^ (3:ℕ) * K * j - 10 * A * S * O ^ (7:ℕ) * j - 14 * A * S * O ^ (5:ℕ) * K * j - 4
    * A * S * O ^ (3:ℕ) * K ^ (2:ℕ) * j - 3 * A * W ^ (4:ℕ) * O ^ (4:ℕ) - 3 * A * W ^ (4:ℕ) *
    O ^ (2:ℕ) * K + 6 * A * W ^ (2:ℕ) * O ^ (6:ℕ) + 9 * A * W ^ (2:ℕ) * O ^ (4:ℕ) * K + 3 * A *
    W ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - 3 * A * O ^ (8:ℕ) - 6 * A * O ^ (6:ℕ) * K - 3 * A *
    O ^ (4:ℕ) * K ^ (2:ℕ)]

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

@[tmio M, powerlib_domain] private theorem zk_r {A B D S W O K N j : ℂ}
    (hj : j ^ 2 = -1) (h0 : N * W = K * S) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    zkJ A B D K S W *ᵥ zkRC A D K S W O =
      (A * B * W - K * (S ^ 2 + W ^ 2)) • zkBil A B N (zkQC A D K S W O j) (zkQC A D K S W (-O) j)
          := by
  ext k
  fin_cases k <;> simp only [zkJ, zkRC, zkBil, zkQC, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply,
      smul_eq_mul]
  · ring
  · linear_combination (-A ^ (3:ℕ) * B * W ^ (2:ℕ) + A ^ (2:ℕ) * S ^ (2:ℕ) * W * K + A ^ (2:ℕ) *
      W ^ (3:ℕ) * K) * h0 + (-2 * A ^ (2:ℕ) * D * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 2 * A ^ (2:ℕ) * S * W
      * O ^ (2:ℕ) + A ^ (2:ℕ) * S * W * K) * h2 + (-2 * A ^ (2:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) + 4 *
      A ^ (2:ℕ) * W * O ^ (4:ℕ) + 2 * A ^ (2:ℕ) * W * O ^ (2:ℕ) * K) * h1 + (-4 * A ^ (2:ℕ) *
      D ^ (2:ℕ) * S * W * O ^ (4:ℕ) + 2 * A ^ (2:ℕ) * D * W * O ^ (4:ℕ) * K - 4 * A ^ (2:ℕ) * S * W
      * O ^ (6:ℕ) - 4 * A ^ (2:ℕ) * S * W * O ^ (4:ℕ) * K) * hj
  · linear_combination (A ^ (2:ℕ) * B * W ^ (2:ℕ) + 2 * A * D * S * W * O ^ (2:ℕ) + A * S ^ (2:ℕ) *
      W * O ^ (2:ℕ) + A * W ^ (3:ℕ) * O ^ (2:ℕ) - A * W * O ^ (4:ℕ) - A * W * O ^ (2:ℕ) * K) * h2 +
      (4 * A * S * W * O ^ (4:ℕ) + 2 * A * S * W * O ^ (2:ℕ) * K) * h1
  · linear_combination (2 * A * D * W ^ (2:ℕ) * O ^ (2:ℕ) + A * S ^ (3:ℕ) * O ^ (2:ℕ) + A * S *
      W ^ (2:ℕ) * O ^ (2:ℕ) + A * S * O ^ (4:ℕ) + A * S * O ^ (2:ℕ) * K) * h2 + (2 * A * S ^ (2:ℕ) *
      O ^ (4:ℕ) + 6 * A * W ^ (2:ℕ) * O ^ (4:ℕ) + 2 * A * W ^ (2:ℕ) * O ^ (2:ℕ) * K) * h1

@[tmio M, powerlib_domain] private theorem zk_S {A B D S W O K N j : ℂ}
    (hj : j ^ 2 = -1) (h0 : N * W = K * S) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    ((2 * O * j) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - zkJ A B D K S W) *ᵥ zkSC A D K S W O j =
      zkDC D K S W O j • zkBil A B N (zkQC A D K S W O j) (zkQC A D K S W O j) := by
  ext k
  fin_cases k <;> simp only [zkJ, zkSC, zkBil, zkQC, zkDC, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.reduceEq, ↓reduceIte]
  · linear_combination (-20 * A ^ (2:ℕ) * D * S * W * O ^ (4:ℕ) - 8 * A ^ (2:ℕ) * S ^ (2:ℕ) * W *
      O ^ (4:ℕ) + 12 * A ^ (2:ℕ) * W * O ^ (6:ℕ) + 12 * A ^ (2:ℕ) * W * O ^ (4:ℕ) * K) * hj
  · linear_combination (6 * A ^ (2:ℕ) * D * S * W * O ^ (2:ℕ) + 6 * A ^ (2:ℕ) * D * W * O ^ (3:ℕ) *
      j + 3 * A ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) + 12 * A ^ (2:ℕ) * S * W * O ^ (3:ℕ) * j + 3 *
      A ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) - 15 * A ^ (2:ℕ) * W * O ^ (4:ℕ) - 3 * A ^ (2:ℕ) * W *
      O ^ (2:ℕ) * K) * h0 + (12 * A ^ (2:ℕ) * D * W * O ^ (3:ℕ) * j + 4 * A ^ (2:ℕ) * S * W *
      O ^ (3:ℕ) * j + 30 * A ^ (2:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) - 4 * A ^ (2:ℕ) * W * O ^ (4:ℕ) - 6
      * A ^ (2:ℕ) * W * O ^ (2:ℕ) * K) * h1 + (24 * A ^ (2:ℕ) * D ^ (2:ℕ) * S * W * O ^ (4:ℕ) + 12 *
      A ^ (2:ℕ) * D ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 24 * A ^ (2:ℕ) * D * S * W * O ^ (5:ℕ) * j - 12 *
      A ^ (2:ℕ) * D * W * O ^ (6:ℕ) - 18 * A ^ (2:ℕ) * D * W * O ^ (4:ℕ) * K - 4 * A ^ (2:ℕ) *
      S ^ (3:ℕ) * W * O ^ (4:ℕ) - 4 * A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) + 32 * A ^ (2:ℕ) * S * W
      * O ^ (6:ℕ) + 16 * A ^ (2:ℕ) * S * W * O ^ (4:ℕ) * K) * hj
  · linear_combination (-6 * A * D * S * W * O ^ (2:ℕ) - 6 * A * D * W * O ^ (3:ℕ) * j - 3 * A *
      S ^ (2:ℕ) * W * O ^ (2:ℕ) - 12 * A * S * W * O ^ (3:ℕ) * j - 3 * A * W ^ (3:ℕ) * O ^ (2:ℕ) +
      15 * A * W * O ^ (4:ℕ) + 3 * A * W * O ^ (2:ℕ) * K) * h2 + (-8 * A * D * W * O ^ (4:ℕ) - 12 *
      A * S * W * O ^ (4:ℕ) - 6 * A * S * W * O ^ (2:ℕ) * K - 18 * A * W * O ^ (5:ℕ) * j - 6 * A * W
      * O ^ (3:ℕ) * K * j) * h1 + (24 * A * D * S * W * O ^ (6:ℕ) + 12 * A * S ^ (2:ℕ) * W *
      O ^ (6:ℕ) + 12 * A * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K + 12 * A * W ^ (3:ℕ) * O ^ (6:ℕ) + 12 * A *
      W ^ (3:ℕ) * O ^ (4:ℕ) * K - 12 * A * W * O ^ (8:ℕ) - 12 * A * W * O ^ (6:ℕ) * K) * hj
  · linear_combination (10 * A * D * S * O ^ (3:ℕ) * j - 6 * A * D * W ^ (2:ℕ) * O ^ (2:ℕ) + A *
      S ^ (3:ℕ) * O ^ (2:ℕ) + 4 * A * S ^ (2:ℕ) * O ^ (3:ℕ) * j + A * S * W ^ (2:ℕ) * O ^ (2:ℕ) + A
      * S * O ^ (4:ℕ) + 5 * A * S * O ^ (2:ℕ) * K - 6 * A * O ^ (5:ℕ) * j - 6 * A * O ^ (3:ℕ) * K *
      j) * h2 + (16 * A * D * O ^ (5:ℕ) * j + 2 * A * S ^ (2:ℕ) * O ^ (4:ℕ) + 18 * A * S * O ^ (5:ℕ)
      * j + 10 * A * S * O ^ (3:ℕ) * K * j - 10 * A * W ^ (2:ℕ) * O ^ (4:ℕ) - 6 * A * W ^ (2:ℕ) *
      O ^ (2:ℕ) * K - 8 * A * O ^ (6:ℕ)) * h1 + (-8 * A * D ^ (2:ℕ) * S * O ^ (6:ℕ) + 8 * A * D *
      W ^ (2:ℕ) * O ^ (6:ℕ) - 8 * A * D * O ^ (8:ℕ) - 4 * A * S ^ (3:ℕ) * O ^ (6:ℕ) - 4 * A *
      S ^ (3:ℕ) * O ^ (4:ℕ) * K - 4 * A * S * W ^ (2:ℕ) * O ^ (6:ℕ) - 4 * A * S * W ^ (2:ℕ) *
      O ^ (4:ℕ) * K - 20 * A * S * O ^ (8:ℕ) - 28 * A * S * O ^ (6:ℕ) * K - 8 * A * S * O ^ (4:ℕ) *
      K ^ (2:ℕ)) * hj

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

@[tmio M, powerlib_domain] private theorem zkSC_apply_zero {A D K S W O j : ℂ} :
    zkSC A D K S W O j 0 = -10 * A ^ (2:ℕ) * D * S * W * O ^ (3:ℕ) * j + 6 * A ^ (2:ℕ) * D *
        W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) - 4 * A ^ (2:ℕ) * S ^ (2:ℕ) *
        W * O ^ (3:ℕ) * j - A ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (2:ℕ) * S * W * O ^ (4:ℕ) -
        5 * A ^ (2:ℕ) * S * W * O ^ (2:ℕ) * K + 6 * A ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 6 * A ^ (2:ℕ) *
        W * O ^ (3:ℕ) * K * j := rfl

@[tmio M, powerlib_domain] private theorem zkSC_apply_three {A D K S W O j : ℂ} :
    zkSC A D K S W O j 3 = -4 * A * D ^ (2:ℕ) * S * O ^ (5:ℕ) * j + 8 * A * D ^ (2:ℕ) * W ^ (2:ℕ) *
        O ^ (4:ℕ) - 8 * A * D ^ (2:ℕ) * O ^ (6:ℕ) - 4 * A * D * S * W ^ (2:ℕ) * O ^ (4:ℕ) - 12 * A *
        D * S * O ^ (6:ℕ) - 10 * A * D * S * O ^ (4:ℕ) * K + 4 * A * D * W ^ (2:ℕ) * O ^ (5:ℕ) * j -
        4 * A * D * O ^ (7:ℕ) * j - A * S ^ (4:ℕ) * O ^ (4:ℕ) - A * S ^ (4:ℕ) * O ^ (2:ℕ) * K - 2 *
        A * S ^ (3:ℕ) * O ^ (5:ℕ) * j - 2 * A * S ^ (3:ℕ) * O ^ (3:ℕ) * K * j - 4 * A * S ^ (2:ℕ) *
        W ^ (2:ℕ) * O ^ (4:ℕ) - 4 * A * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * K - 8 * A * S ^ (2:ℕ) *
        O ^ (6:ℕ) - 13 * A * S ^ (2:ℕ) * O ^ (4:ℕ) * K - 5 * A * S ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) -
        2 * A * S * W ^ (2:ℕ) * O ^ (5:ℕ) * j - 2 * A * S * W ^ (2:ℕ) * O ^ (3:ℕ) * K * j - 10 * A *
        S * O ^ (7:ℕ) * j - 14 * A * S * O ^ (5:ℕ) * K * j - 4 * A * S * O ^ (3:ℕ) * K ^ (2:ℕ) * j -
        3 * A * W ^ (4:ℕ) * O ^ (4:ℕ) - 3 * A * W ^ (4:ℕ) * O ^ (2:ℕ) * K + 6 * A * W ^ (2:ℕ) *
        O ^ (6:ℕ) + 9 * A * W ^ (2:ℕ) * O ^ (4:ℕ) * K + 3 * A * W ^ (2:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) -
        3 * A * O ^ (8:ℕ) - 6 * A * O ^ (6:ℕ) * K - 3 * A * O ^ (4:ℕ) * K ^ (2:ℕ) := rfl

@[tmio M, powerlib_domain] private theorem zk_Y3p1 {A B D S W O K N j : ℂ}
    (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc :
        starRingEnd ℂ j = -j)
    (hj : j ^ 2 = -1) (h0 : N * W = K * S) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
        :
    starRingEnd ℂ ((zkLC A D S W O j) 1) * (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K S W O
        j)) 1 =
      (12 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 40 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) + 28 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 44 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ)
        * O ^ (6:ℕ) - 14 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 88 * A ^ (3:ℕ) * D * S *
        W * O ^ (8:ℕ) + 58 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K - 2 * A ^ (3:ℕ) * S ^ (6:ℕ) * W *
        O ^ (4:ℕ) - A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (2:ℕ) * K - 7 * A ^ (3:ℕ) * S ^ (4:ℕ) *
        W ^ (3:ℕ) * O ^ (4:ℕ) - 5 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 9 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) - 9 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K - 5 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * K ^ (2:ℕ) - 8 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) *
        O ^ (4:ℕ) - 7 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K + 2 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) - 5 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K -
        2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + 68 * A ^ (3:ℕ) * S ^ (2:ℕ) *
        W * O ^ (8:ℕ) + 76 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (2:ℕ) *
        W * O ^ (4:ℕ) * K ^ (2:ℕ) - 3 * A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (4:ℕ) - 3 * A ^ (3:ℕ) *
        W ^ (7:ℕ) * O ^ (2:ℕ) * K + 9 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) + 12 * A ^ (3:ℕ) *
        W ^ (5:ℕ) * O ^ (4:ℕ) * K + 3 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - 3 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) - 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K - 3 *
        A ^ (3:ℕ) * W * O ^ (10:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - 3 * A ^ (3:ℕ) * W *
        O ^ (6:ℕ) * K ^ (2:ℕ)) + (8 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) + 4 *
        A ^ (3:ℕ) * D ^ (2:ℕ) * S * W * O ^ (7:ℕ) - 8 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (5:ℕ) - 12 *
        A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (3:ℕ) * K + 48 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) + 62
        * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K - 40 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) - 50 *
        A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K - 11 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (5:ℕ) - 5 *
        A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (3:ℕ) * K - 18 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) *
        O ^ (5:ℕ) - 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K - 42 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W * O ^ (7:ℕ) - 73 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K - 19 * A ^ (3:ℕ)
        * S ^ (3:ℕ) * W * O ^ (3:ℕ) * K ^ (2:ℕ) - 7 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (5:ℕ) - 7 *
        A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K + 22 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) + 41
        * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 19 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) *
        K ^ (2:ℕ) - 67 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) - 150 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K -
        83 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ)) * j := by
  simp only [zkLC, zkBil, zkQC, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_add, map_sub, map_neg, map_pow, hS, hW, hO, hjc]
  rw [zkSC_apply_zero, zkSC_apply_three]
  linear_combination (10 * A ^ (3:ℕ) * D * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j - 6 * A ^ (3:ℕ) * D *
      S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) + 20 * A ^ (3:ℕ) * D * S ^ (2:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ)
      - 2 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j + 10 * A ^ (3:ℕ) * D * S * W * O ^ (5:ℕ) *
      j ^ (3:ℕ) - 6 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (2:ℕ) - 6 * A ^ (3:ℕ) * D * W ^ (3:ℕ) *
      O ^ (4:ℕ) * j ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (2:ℕ) + 6 * A ^ (3:ℕ) * S ^ (4:ℕ) * W
      * O ^ (3:ℕ) * j + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) + 9 * A ^ (3:ℕ) *
      S ^ (3:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ) + 5 * A ^ (3:ℕ)
      * S ^ (3:ℕ) * W * O ^ (2:ℕ) * K + 6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j + 4 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j ^ (3:ℕ) - 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ)
      * j + 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j + A ^ (3:ℕ) * S * W ^ (5:ℕ) *
      O ^ (2:ℕ) + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) + A ^ (3:ℕ) * S * W ^ (3:ℕ) *
      O ^ (4:ℕ) + 5 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K - 11 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ)
      * j ^ (2:ℕ) - 7 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K * j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * W ^ (3:ℕ) *
      O ^ (5:ℕ) * j - 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K * j - 6 * A ^ (3:ℕ) * W * O ^ (7:ℕ)
      * j ^ (3:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j ^ (3:ℕ)) * h0 + (-10 * A ^ (3:ℕ) * D *
      S ^ (2:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) + 6 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 10
      * A ^ (3:ℕ) * D * S * W * O ^ (5:ℕ) * j ^ (3:ℕ) - 4 * A ^ (3:ℕ) * D * S * W * O ^ (5:ℕ) * j +
      6 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) + 8 * A ^ (3:ℕ) * D * W ^ (3:ℕ) *
      O ^ (4:ℕ) + 10 * A ^ (3:ℕ) * D * W * O ^ (6:ℕ) * j ^ (4:ℕ) - 18 * A ^ (3:ℕ) * D * W *
      O ^ (6:ℕ) * j ^ (2:ℕ) - 8 * A ^ (3:ℕ) * D * W * O ^ (6:ℕ) - A ^ (3:ℕ) * S ^ (4:ℕ) * W *
      O ^ (3:ℕ) * j - 5 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (2:ℕ)
      * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j ^ (3:ℕ) - 12 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j - 5 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j
      + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S * W ^ (3:ℕ) *
      O ^ (4:ℕ) + 5 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) * j ^ (4:ℕ) - 30 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ)
      * j ^ (2:ℕ) - 12 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) - 9 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K *
      j ^ (2:ℕ) - 10 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K + 8 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) *
      j ^ (3:ℕ) + 14 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) * j + 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ)
      * K * j + 4 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j ^ (5:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (7:ℕ) *
      j ^ (3:ℕ) - 48 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j + 11 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K *
      j ^ (3:ℕ) - 33 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j) * h1 + (14 * A ^ (3:ℕ) * D ^ (2:ℕ) * S *
      W ^ (3:ℕ) * O ^ (5:ℕ) * j + 10 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W * O ^ (7:ℕ) * j ^ (3:ℕ) - 24 *
      A ^ (3:ℕ) * D ^ (2:ℕ) * S * W * O ^ (7:ℕ) * j - 12 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) *
      O ^ (4:ℕ) - 16 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) + 48 * A ^ (3:ℕ) *
      D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + 10 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) * j ^ (2:ℕ) -
      36 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 4 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) *
      j ^ (2:ℕ) + 62 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) + 30 * A ^ (3:ℕ) * D * S *
      W ^ (3:ℕ) * O ^ (4:ℕ) * K + 30 * A ^ (3:ℕ) * D * S * W * O ^ (8:ℕ) * j ^ (2:ℕ) - 116 *
      A ^ (3:ℕ) * D * S * W * O ^ (8:ℕ) + 29 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K * j ^ (2:ℕ) -
      84 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K - 8 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (5:ℕ) * j - 4
      * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) + 10 * A ^ (3:ℕ) * D * W ^ (3:ℕ) *
      O ^ (7:ℕ) * j - 23 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K * j - 2 * A ^ (3:ℕ) * D * W *
      O ^ (9:ℕ) * j ^ (3:ℕ) - 8 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) * j - 6 * A ^ (3:ℕ) * D * W *
      O ^ (7:ℕ) * K * j ^ (3:ℕ) + 17 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K * j - 18 * A ^ (3:ℕ) *
      S ^ (4:ℕ) * W * O ^ (6:ℕ) - 9 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K - 3 * A ^ (3:ℕ) *
      S ^ (3:ℕ) * W * O ^ (7:ℕ) * j + A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j - A ^ (3:ℕ) *
      S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + 14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) * j ^ (2:ℕ) -
      95 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) + 14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K *
      j ^ (2:ℕ) - 126 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K - 27 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (4:ℕ) * K ^ (2:ℕ) + 15 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) * j + 15 * A ^ (3:ℕ) * S *
      W ^ (3:ℕ) * O ^ (5:ℕ) * K * j + 8 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) * j ^ (3:ℕ) - 35 * A ^ (3:ℕ)
      * S * W * O ^ (9:ℕ) * j + 8 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K * j ^ (3:ℕ) - 24 * A ^ (3:ℕ) *
      S * W * O ^ (7:ℕ) * K * j + 11 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ) * j - 3 * A ^ (3:ℕ)
      * W ^ (5:ℕ) * O ^ (6:ℕ) - 3 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K - 3 * A ^ (3:ℕ) *
      W ^ (3:ℕ) * O ^ (6:ℕ) * K - 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) - 6 * A ^ (3:ℕ)
      * W * O ^ (10:ℕ) * j ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W * O ^ (10:ℕ) - 12 * A ^ (3:ℕ) * W * O ^ (8:ℕ)
      * K * j ^ (2:ℕ) + 6 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - 6 * A ^ (3:ℕ) * W * O ^ (6:ℕ) *
      K ^ (2:ℕ) * j ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem zk_Y3p2 {A B D S W O K N j : ℂ}
    (hA : starRingEnd ℂ A = A) (hS : starRingEnd ℂ S = S) (hO : starRingEnd ℂ O = O) (hjc :
        starRingEnd ℂ j = -j)
    (hj : j ^ 2 = -1) (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    starRingEnd ℂ ((zkLC A D S W O j) 2) * (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K S W O
        j)) 2 =
      (12 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) + 8 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) - 20 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 20 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ)
        * O ^ (6:ℕ) - 34 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 32 * A ^ (3:ℕ) * D * S *
        W * O ^ (8:ℕ) - 18 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K + A ^ (3:ℕ) * S ^ (6:ℕ) * W *
        O ^ (4:ℕ) + A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (2:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (4:ℕ) *
        W ^ (3:ℕ) * O ^ (4:ℕ) + 2 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 5 *
        A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K + 5 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) *
        K ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) + A ^ (3:ℕ) * S ^ (2:ℕ) *
        W ^ (5:ℕ) * O ^ (2:ℕ) * K - 16 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) - 23 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 7 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (2:ℕ) * K ^ (2:ℕ) - 19 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) - 18 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) + 6 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) + 12 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K + 6 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (10:ℕ) - 12 *
        A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - 6 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) + (-32 *
        A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) + 20 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W *
        O ^ (7:ℕ) + 8 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (5:ℕ) - 48 * A ^ (3:ℕ) * D * W ^ (3:ℕ) *
        O ^ (7:ℕ) - 38 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 40 * A ^ (3:ℕ) * D * W *
        O ^ (9:ℕ) + 38 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K + 5 * A ^ (3:ℕ) * S ^ (5:ℕ) * W *
        O ^ (5:ℕ) + 5 * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (3:ℕ) * K + 6 * A ^ (3:ℕ) * S ^ (3:ℕ) *
        W ^ (3:ℕ) * O ^ (5:ℕ) + 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K + 30 *
        A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (7:ℕ) + 49 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K + 19
        * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (5:ℕ)
        + A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K - 34 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) -
        47 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K - 13 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ)
        * K ^ (2:ℕ) + 85 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) + 162 * A ^ (3:ℕ) * S * W * O ^ (7:ℕ) * K +
        77 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ)) * j := by
  simp only [zkLC, zkBil, zkQC, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul,
      map_sub, hA, hS, hO, hjc]
  rw [zkSC_apply_zero]
  linear_combination (10 * A ^ (3:ℕ) * D * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j - 6 * A ^ (3:ℕ) * D * S *
      W ^ (3:ℕ) * O ^ (2:ℕ) + 10 * A ^ (3:ℕ) * D * S * W * O ^ (4:ℕ) * j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * D
      * W ^ (3:ℕ) * O ^ (3:ℕ) * j + A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) + 5 * A ^ (3:ℕ) *
      S ^ (3:ℕ) * W * O ^ (3:ℕ) * j + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) + 4 * A ^ (3:ℕ)
      * S ^ (2:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) + A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) + 5 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * K + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 5 *
      A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * j - A ^ (3:ℕ) * S * W * O ^ (3:ℕ) * K * j - 6 * A ^ (3:ℕ) * W
      * O ^ (6:ℕ) * j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * W * O ^ (4:ℕ) * K * j ^ (2:ℕ)) * h2 + (20 *
      A ^ (3:ℕ) * D * S * W * O ^ (5:ℕ) * j - 12 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) + 20 *
      A ^ (3:ℕ) * D * W * O ^ (6:ℕ) * j ^ (2:ℕ) + 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ) + 20 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j + 10 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j
      - 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) - 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K +
      18 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) * j ^ (2:ℕ) + 4 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) + 10 *
      A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K * j ^ (2:ℕ) + 10 * A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K - 14 *
      A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) * j - 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K * j + 40 *
      A ^ (3:ℕ) * W * O ^ (7:ℕ) * j + 38 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j) * h1 + (-20 *
      A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) + 20 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 8
      * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (6:ℕ) + 36 * A ^ (3:ℕ) * D * S * W * O ^ (8:ℕ) + 28 *
      A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) + 4 *
      A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K + 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ)
      + 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 26 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (8:ℕ) + 40 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (4:ℕ) * K ^ (2:ℕ) - 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) - 12 * A ^ (3:ℕ) * W ^ (3:ℕ) *
      O ^ (6:ℕ) * K - 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) + 6 * A ^ (3:ℕ) * W *
      O ^ (10:ℕ) + 12 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K + 6 * A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) *
      hj

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

@[tmio M, powerlib_domain] private theorem zk_Y2 {A B D S W O K N j : ℂ}
    (hA : starRingEnd ℂ A = A) (hD : starRingEnd ℂ D = D) (hS : starRingEnd ℂ S = S)
    (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2
        = -1) (h0 : N * W = K * S)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    pairing (zkLC A D S W O j) (zkBil A B N (zkQC A D K S W O j) (zkRC A D K S W O)) =
      (A ^ (3:ℕ) * S ^ (6:ℕ) * W * O ^ (4:ℕ) + A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) -
        A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K + 3 * A ^ (3:ℕ) * S ^ (4:ℕ) * W *
        O ^ (6:ℕ) + 4 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K - A ^ (3:ℕ) * S ^ (2:ℕ) *
        W ^ (5:ℕ) * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K - 2 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) - 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (4:ℕ) * K - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + 3 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) + 6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 3 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) - A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (4:ℕ) -
        A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (2:ℕ) * K + 3 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) + 4 *
        A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) - 3 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) - 5 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K - 2 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * W * O ^ (10:ℕ) + 2 * A ^ (3:ℕ) *
        W * O ^ (8:ℕ) * K + A ^ (3:ℕ) * W * O ^ (6:ℕ) * K ^ (2:ℕ)) + (8 * A ^ (3:ℕ) * D * W ^ (5:ℕ)
        * O ^ (5:ℕ) + 4 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (3:ℕ) * K - 16 * A ^ (3:ℕ) * D * W ^ (3:ℕ)
        * O ^ (7:ℕ) - 8 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 8 * A ^ (3:ℕ) * D * W *
        O ^ (9:ℕ) + 4 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K + 2 * A ^ (3:ℕ) * S ^ (5:ℕ) * W *
        O ^ (5:ℕ) - 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K + 8 * A ^ (3:ℕ) *
        S ^ (3:ℕ) * W * O ^ (7:ℕ) + 8 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K - 2 * A ^ (3:ℕ) *
        S * W ^ (5:ℕ) * O ^ (5:ℕ) - 2 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K - 12 * A ^ (3:ℕ) *
        S * W ^ (3:ℕ) * O ^ (7:ℕ) - 18 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K - 6 * A ^ (3:ℕ) *
        S * W ^ (3:ℕ) * O ^ (3:ℕ) * K ^ (2:ℕ) + 14 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) + 20 * A ^ (3:ℕ)
        * S * W * O ^ (7:ℕ) * K + 6 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ)) * j := by
  simp only [pairing_apply, zkLC, zkBil, zkQC, zkRC, Fin.sum_univ_four, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul, map_add, map_sub,
      map_neg, map_pow, hA, hD, hS, hW, hO, hjc]
  linear_combination (-2 * A ^ (3:ℕ) * D * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) - 4 * A ^ (3:ℕ) * D * S
      * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 2 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (2:ℕ) - 2 * A ^ (3:ℕ) * D *
      W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (2:ℕ) - 2 * A ^ (3:ℕ) *
      S ^ (4:ℕ) * W * O ^ (3:ℕ) * j - 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (3:ℕ)
      * S ^ (3:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ) - A ^ (3:ℕ) *
      S ^ (3:ℕ) * W * O ^ (2:ℕ) * K - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 2 *
      A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * K * j
      - A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (2:ℕ) - A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
      A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) - A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K - A ^ (3:ℕ)
      * S * W * O ^ (6:ℕ) * j ^ (2:ℕ) - A ^ (3:ℕ) * S * W * O ^ (4:ℕ) * K * j ^ (2:ℕ)) * h0 + (-2 *
      A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (2:ℕ) - 2 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (3:ℕ) * j -
      A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j - A ^ (3:ℕ)
      * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) - A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) - A ^ (3:ℕ) *
      S ^ (2:ℕ) * W * O ^ (2:ℕ) * K - A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (3:ℕ) * j - A ^ (3:ℕ) * S * W
      * O ^ (5:ℕ) * j - A ^ (3:ℕ) * S * W * O ^ (3:ℕ) * K * j) * h2 + (-2 * A ^ (3:ℕ) * D * S *
      W ^ (3:ℕ) * O ^ (3:ℕ) * j - 6 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) - 4 *
      A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (4:ℕ) - A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j - 3 *
      A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ) * j ^ (2:ℕ) - 2 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (4:ℕ)
      - A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (5:ℕ) * j ^ (3:ℕ) - 4 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (5:ℕ) * j - A ^ (3:ℕ) * S ^ (2:ℕ)
      * W * O ^ (3:ℕ) * K * j - A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) - 4 * A ^ (3:ℕ) *
      S * W ^ (3:ℕ) * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (2:ℕ) * K - A ^ (3:ℕ) * S * W
      * O ^ (6:ℕ) * j ^ (4:ℕ) - 6 * A ^ (3:ℕ) * S * W * O ^ (6:ℕ) * j ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S *
      W * O ^ (4:ℕ) * K * j ^ (2:ℕ) - 8 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ) * j - 4 * A ^ (3:ℕ) *
      W ^ (3:ℕ) * O ^ (3:ℕ) * K * j - 6 * A ^ (3:ℕ) * W * O ^ (7:ℕ) * j ^ (3:ℕ) + 2 * A ^ (3:ℕ) * W
      * O ^ (7:ℕ) * j - 3 * A ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j ^ (3:ℕ) + A ^ (3:ℕ) * W * O ^ (5:ℕ) *
      K * j) * h1 + (-6 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * j + 4 * A ^ (3:ℕ) *
      D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 2 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) *
      j ^ (2:ℕ) - 4 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) - 6 * A ^ (3:ℕ) * D * S *
      W ^ (3:ℕ) * O ^ (6:ℕ) - 6 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 2 * A ^ (3:ℕ) * D
      * S * W * O ^ (8:ℕ) * j ^ (2:ℕ) - A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K * j ^ (2:ℕ) + 8 *
      A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (7:ℕ) * j + 5 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K * j
      - 6 * A ^ (3:ℕ) * D * W * O ^ (9:ℕ) * j - 3 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K * j - 2 *
      A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) - 3 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (4:ℕ) * K - 5 *
      A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (7:ℕ) * j - 5 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K * j
      + A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) *
      j ^ (2:ℕ) - 3 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) - 2 * A ^ (3:ℕ) * S ^ (2:ℕ) * W *
      O ^ (6:ℕ) * K * j ^ (2:ℕ) - 6 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K - 3 * A ^ (3:ℕ) *
      S ^ (2:ℕ) * W * O ^ (4:ℕ) * K ^ (2:ℕ) + A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (7:ℕ) * j + A ^ (3:ℕ)
      * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K * j - 11 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) * j - 16 * A ^ (3:ℕ)
      * S * W * O ^ (7:ℕ) * K * j - 5 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ) * j - A ^ (3:ℕ) *
      W ^ (5:ℕ) * O ^ (6:ℕ) - A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + 2 * A ^ (3:ℕ) * W ^ (3:ℕ) *
      O ^ (8:ℕ) + 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K + A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) *
      K ^ (2:ℕ) - A ^ (3:ℕ) * W * O ^ (10:ℕ) - 2 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - A ^ (3:ℕ) * W *
      O ^ (6:ℕ) * K ^ (2:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem zk_Y3 {A B D S W O K N j : ℂ}
    (hA : starRingEnd ℂ A = A) (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W)
    (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j) (hj : j ^ 2 = -1) (h0 : N * W = K * S)
    (h1 : D * (S ^ 2 + W ^ 2 - O ^ 2) = 2 * S * (K + O ^ 2))
    (h2 : A * B * W = K * (S ^ 2 + W ^ 2) + O ^ 2 * (S ^ 2 + W ^ 2 - O ^ 2 + 2 * S * D - K)) :
    pairing (zkLC A D S W O j) (zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K S W O j)) =
      (24 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 32 * A ^ (3:ℕ) * D ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) + 8 * A ^ (3:ℕ) * D ^ (2:ℕ) * W * O ^ (8:ℕ) - 64 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) *
        O ^ (6:ℕ) - 48 * A ^ (3:ℕ) * D * S * W ^ (3:ℕ) * O ^ (4:ℕ) * K + 56 * A ^ (3:ℕ) * D * S * W
        * O ^ (8:ℕ) + 40 * A ^ (3:ℕ) * D * S * W * O ^ (6:ℕ) * K - A ^ (3:ℕ) * S ^ (6:ℕ) * W *
        O ^ (4:ℕ) - 5 * A ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) - 3 * A ^ (3:ℕ) * S ^ (4:ℕ) *
        W ^ (3:ℕ) * O ^ (2:ℕ) * K + 9 * A ^ (3:ℕ) * S ^ (4:ℕ) * W * O ^ (6:ℕ) - 4 * A ^ (3:ℕ) *
        S ^ (4:ℕ) * W * O ^ (4:ℕ) * K - 7 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) - 6 *
        A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K - 14 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) *
        O ^ (6:ℕ) - 28 * A ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K - 9 * A ^ (3:ℕ) *
        S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + 49 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (8:ℕ) +
        58 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (6:ℕ) * K + 5 * A ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (4:ℕ) *
        K ^ (2:ℕ) - 3 * A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (4:ℕ) - 3 * A ^ (3:ℕ) * W ^ (7:ℕ) * O ^ (2:ℕ) *
        K + 9 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (6:ℕ) + 12 * A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (4:ℕ) * K + 3 *
        A ^ (3:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * K ^ (2:ℕ) + 3 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (8:ℕ) + 9 *
        A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (6:ℕ) * K + 6 * A ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (4:ℕ) * K ^ (2:ℕ) -
        9 * A ^ (3:ℕ) * W * O ^ (10:ℕ) - 18 * A ^ (3:ℕ) * W * O ^ (8:ℕ) * K - 9 * A ^ (3:ℕ) * W *
        O ^ (6:ℕ) * K ^ (2:ℕ)) + (-24 * A ^ (3:ℕ) * D ^ (2:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) + 24 *
        A ^ (3:ℕ) * D ^ (2:ℕ) * S * W * O ^ (7:ℕ) - 12 * A ^ (3:ℕ) * D * W ^ (5:ℕ) * O ^ (3:ℕ) * K +
        24 * A ^ (3:ℕ) * D * W ^ (3:ℕ) * O ^ (5:ℕ) * K - 12 * A ^ (3:ℕ) * D * W * O ^ (7:ℕ) * K - 6
        * A ^ (3:ℕ) * S ^ (5:ℕ) * W * O ^ (5:ℕ) - 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (5:ℕ)
        - 6 * A ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * K - 12 * A ^ (3:ℕ) * S ^ (3:ℕ) * W *
        O ^ (7:ℕ) - 24 * A ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (5:ℕ) * K - 6 * A ^ (3:ℕ) * S * W ^ (5:ℕ) *
        O ^ (5:ℕ) - 6 * A ^ (3:ℕ) * S * W ^ (5:ℕ) * O ^ (3:ℕ) * K - 12 * A ^ (3:ℕ) * S * W ^ (3:ℕ) *
        O ^ (7:ℕ) - 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) * O ^ (5:ℕ) * K + 6 * A ^ (3:ℕ) * S * W ^ (3:ℕ) *
        O ^ (3:ℕ) * K ^ (2:ℕ) + 18 * A ^ (3:ℕ) * S * W * O ^ (9:ℕ) + 12 * A ^ (3:ℕ) * S * W *
        O ^ (7:ℕ) * K - 6 * A ^ (3:ℕ) * S * W * O ^ (5:ℕ) * K ^ (2:ℕ)) * j := by
  rw [pairing_apply, Fin.sum_univ_four, zk_Y3p1 hS hW hO hjc hj h0 h1, zk_Y3p2 hA hS hO hjc hj h1
        h2]
  have e0 : zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K S W O j) 0 = 0 := rfl
  have e3 : zkBil A B N (zkQC A D K S W (-O) j) (zkSC A D K S W O j) 3 = 0 := rfl
  rw [e0, e3]
  ring


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

/-- The real part of the combination of the projection formula. -/
@[tmio M, powerlib_domain] private theorem zk_re (cr ci dr di y1r y1i y2r y2i y3r y3i b : ℝ)
    (hb : b ≠ 0) (hc : cr ^ 2 + ci ^ 2 ≠ 0) (hd : dr ^ 2 + di ^ 2 ≠ 0) :
    (((cr : ℂ) + ci * I)⁻¹ * ((y1r : ℂ) + y1i * I) -
        2 * ((b : ℂ)⁻¹ * (((cr : ℂ) + ci * I)⁻¹ * ((y2r : ℂ) + y2i * I))) +
        ((dr : ℂ) + di * I)⁻¹ * (((cr : ℂ) + ci * I)⁻¹ * ((y3r : ℂ) + y3i * I))).re =
      ((b * (dr * y1r - di * y1i) - 2 * (dr * y2r - di * y2i) + b * y3r) * (cr * dr - ci * di) +
        (b * (dr * y1i + di * y1r) - 2 * (dr * y2i + di * y2r) + b * y3i) * (cr * di + ci * dr)) /
        (b * ((cr ^ 2 + ci ^ 2) * (dr ^ 2 + di ^ 2))) := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.inv_re, Complex.inv_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul,
      sub_zero, zero_add, add_zero, mul_one, neg_zero, zero_div]
  have hc' : cr * cr + ci * ci ≠ 0 := by rw [← sq, ← sq]; exact hc
  have hd' : dr * dr + di * di ≠ 0 := by rw [← sq, ← sq]; exact hd
  have hb' : b * b + 0 * 0 ≠ 0 := by simpa using mul_ne_zero hb hb
  field_simp
  ring

/-- The last step of the closed form. -/
@[tmio M, powerlib_domain] private theorem zk_final {Z a d σ ω w N K1 K2 bb : ℝ} (ha : a ≠ 0)
    (hb : bb ≠ 0) (hα : 2 * σ + d ≠ 0) (hω : ω ≠ 0) (hw : w ≠ 0) (hK1 : K1 ≠ 0) (hK2 : K2 ≠ 0)
    (key : Z * (2 * σ + d) ^ 4 = -288 * a ^ 4 * d * σ * ω ^ 8 * w ^ 2 * bb * N) :
    1 / (2 * ω) * (Z / (bb * ((4 * a ^ 2 * ω ^ 2 * w ^ 2 * K1) * (9 * ω ^ 4 * K2)))) =
      -(4 * a ^ 2 * d * σ * ω / ((2 * σ + d) ^ 4 * K1 * K2)) * N := by
  rw [div_mul_div_comm, one_mul, neg_mul, div_mul_eq_mul_div, eq_neg_iff_add_eq_zero,
    div_add_div _ _ (by positivity) (by positivity), div_eq_zero_iff]
  left
  linear_combination (K1 * K2) * key

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
    (hdet : 0 < a * b * w - κ * (σ ^ 2 + w ^ 2)) (h0 : ν * w = κ * σ)
    (h1 : d * (σ ^ 2 + w ^ 2 - ω ^ 2) = 2 * σ * (κ + ω ^ 2))
    (h2 : a * b * w = κ * (σ ^ 2 + w ^ 2) + ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d - κ))
    (hJ : jacobianC f 0 = zkJ a b d κ σ w) (hB : ∀ u v, bilinC f 0 u v = zkBil a b ν u v)
    (hC : ∀ u v z, trilinC f 0 u v z = zkTri a b κ u v z) :
    firstLyapunov f 0 ω (zkQC a d κ σ w ω I)
        ((starRingEnd ℂ (zkCC a d κ σ w ω I))⁻¹ • zkLC a d σ w ω I) =
      -(4 * a ^ 2 * d * σ * ω / ((2 * σ + d) ^ 4 * angleZeroR1 d σ w κ ω *
        angleZeroR2 d σ w κ ω)) * bautinFormQ d σ w κ := by
  have hj : (I : ℂ) ^ 2 = -1 := I_sq
  have hjc : starRingEnd ℂ I = -I := conj_I
  have h0c : (ν : ℂ) * w = κ * σ := by exact_mod_cast h0
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
  have hc : zkCC a d κ σ w ω I = ((2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ) : ℝ) : ℂ)
      + ((-4 * a * d * σ * w * ω - 2 * a * σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w *
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
      zkRC a d κ σ w ω) = bilinC f 0 (zkQC a d κ σ w ω I) (star (zkQC a d κ σ w ω I)) := by
    rw [Matrix.mulVec_smul, hJ, zk_r hj h0c h1c h2c, hB, hq, hdetC, smul_smul,
      inv_mul_cancel₀ hdet', one_smul]
  have hs : shift2 (jacobianC f 0) ω *ᵥ ((zkDC d κ σ w ω I)⁻¹ • zkSC a d κ σ w ω I) =
      bilinC f 0 (zkQC a d κ σ w ω I) (zkQC a d κ σ w ω I) := by
    rw [Matrix.mulVec_smul, hJ, shift2, zk_S hj h0c h1c h2c, hB, smul_smul, inv_mul_cancel₀ hΔ0,
      one_smul]
  have hpair : ∀ (z : ℂ) (v : Fin 4 → ℂ),
      pairing ((starRingEnd ℂ z)⁻¹ • zkLC a d σ w ω I) v = z⁻¹ * pairing (zkLC a d σ w ω I) v := by
    intro z v
    simp [pairing_apply, Finset.mul_sum, mul_assoc]
  rw [firstLyapunov_eq_of_solve hA h2' hr hs, (bilinC f 0 _).map_smul, (bilinC f 0 _).map_smul,
    hC, hB, hB, hq, (pairing _).map_smul, (pairing _).map_smul, hpair, hpair, hpair, smul_eq_mul,
    smul_eq_mul]
  rw [(zk_Y1 (hR a) (hR d) (hR σ) (hR w) (hR ω) hjc hj h1c h2c).trans (show _ = ((-4 * a ^ (3:ℕ) *
      d * σ * w ^ (3:ℕ) * ω ^ (2:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) - 3 *
      a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * κ - 4 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) - 3 * a ^ (3:ℕ)
      * w ^ (5:ℕ) * κ + 4 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) + 3 * a ^ (3:ℕ) * w ^ (3:ℕ) *
      ω ^ (2:ℕ) * κ : ℝ) : ℂ) + ((-4 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) - 2 * a ^ (3:ℕ) * σ *
      w ^ (3:ℕ) * ω * κ : ℝ) : ℂ) * I by push_cast; ring),
    (zk_Y2 (hR a) (hR d) (hR σ) (hR w) (hR ω) hjc hj h0c h1c h2c).trans (show _ = ((a ^ (3:ℕ) *
        σ ^ (6:ℕ) * w * ω ^ (4:ℕ) + a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) - a ^ (3:ℕ) *
        σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ + 3 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (6:ℕ) + 4 *
        a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (4:ℕ) * κ - a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) -
        2 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ - 2 * a ^ (3:ℕ) * σ ^ (2:ℕ) *
        w ^ (3:ℕ) * ω ^ (6:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ - 3 *
        a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) + 3 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w *
        ω ^ (8:ℕ) + 6 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (6:ℕ) * κ + 3 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w *
        ω ^ (4:ℕ) * κ ^ (2:ℕ) - a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) - a ^ (3:ℕ) * w ^ (7:ℕ) *
        ω ^ (2:ℕ) * κ + 3 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 4 * a ^ (3:ℕ) * w ^ (5:ℕ) *
        ω ^ (4:ℕ) * κ + a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (3:ℕ) *
        ω ^ (8:ℕ) - 5 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ - 2 * a ^ (3:ℕ) * w ^ (3:ℕ) *
        ω ^ (4:ℕ) * κ ^ (2:ℕ) + a ^ (3:ℕ) * w * ω ^ (10:ℕ) + 2 * a ^ (3:ℕ) * w * ω ^ (8:ℕ) * κ +
        a ^ (3:ℕ) * w * ω ^ (6:ℕ) * κ ^ (2:ℕ) : ℝ) : ℂ) + ((8 * a ^ (3:ℕ) * d * w ^ (5:ℕ) *
        ω ^ (5:ℕ) + 4 * a ^ (3:ℕ) * d * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ - 16 * a ^ (3:ℕ) * d * w ^ (3:ℕ)
        * ω ^ (7:ℕ) - 8 * a ^ (3:ℕ) * d * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ + 8 * a ^ (3:ℕ) * d * w *
        ω ^ (9:ℕ) + 4 * a ^ (3:ℕ) * d * w * ω ^ (7:ℕ) * κ + 2 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w *
        ω ^ (5:ℕ) - 2 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ + 8 * a ^ (3:ℕ) *
        σ ^ (3:ℕ) * w * ω ^ (7:ℕ) + 8 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (5:ℕ) * κ - 2 * a ^ (3:ℕ) *
        σ * w ^ (5:ℕ) * ω ^ (5:ℕ) - 2 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ - 12 * a ^ (3:ℕ)
        * σ * w ^ (3:ℕ) * ω ^ (7:ℕ) - 18 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ - 6 *
        a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ ^ (2:ℕ) + 14 * a ^ (3:ℕ) * σ * w * ω ^ (9:ℕ) + 20
        * a ^ (3:ℕ) * σ * w * ω ^ (7:ℕ) * κ + 6 * a ^ (3:ℕ) * σ * w * ω ^ (5:ℕ) * κ ^ (2:ℕ) : ℝ) :
        ℂ) * I by push_cast; ring),
    (zk_Y3 (hR a) (hR σ) (hR w) (hR ω) hjc hj h0c h1c h2c).trans (show _ = ((24 * a ^ (3:ℕ) *
        d ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) - 32 * a ^ (3:ℕ) * d ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) + 8
        * a ^ (3:ℕ) * d ^ (2:ℕ) * w * ω ^ (8:ℕ) - 64 * a ^ (3:ℕ) * d * σ * w ^ (3:ℕ) * ω ^ (6:ℕ) -
        48 * a ^ (3:ℕ) * d * σ * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ + 56 * a ^ (3:ℕ) * d * σ * w * ω ^ (8:ℕ)
        + 40 * a ^ (3:ℕ) * d * σ * w * ω ^ (6:ℕ) * κ - a ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω ^ (4:ℕ) - 5 *
        a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) - 3 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) *
        ω ^ (2:ℕ) * κ + 9 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w * ω ^ (6:ℕ) - 4 * a ^ (3:ℕ) * σ ^ (4:ℕ) * w *
        ω ^ (4:ℕ) * κ - 7 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) - 6 * a ^ (3:ℕ) *
        σ ^ (2:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ - 14 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ)
        - 28 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ - 9 * a ^ (3:ℕ) * σ ^ (2:ℕ) *
        w ^ (3:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) + 49 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (8:ℕ) + 58 *
        a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (6:ℕ) * κ + 5 * a ^ (3:ℕ) * σ ^ (2:ℕ) * w * ω ^ (4:ℕ) *
        κ ^ (2:ℕ) - 3 * a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) - 3 * a ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (2:ℕ) *
        κ + 9 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) + 12 * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) * κ + 3
        * a ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (2:ℕ) * κ ^ (2:ℕ) + 3 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (8:ℕ) + 9
        * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) * κ + 6 * a ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) * κ ^ (2:ℕ)
        - 9 * a ^ (3:ℕ) * w * ω ^ (10:ℕ) - 18 * a ^ (3:ℕ) * w * ω ^ (8:ℕ) * κ - 9 * a ^ (3:ℕ) * w *
        ω ^ (6:ℕ) * κ ^ (2:ℕ) : ℝ) : ℂ) + ((-24 * a ^ (3:ℕ) * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ)
        + 24 * a ^ (3:ℕ) * d ^ (2:ℕ) * σ * w * ω ^ (7:ℕ) - 12 * a ^ (3:ℕ) * d * w ^ (5:ℕ) *
        ω ^ (3:ℕ) * κ + 24 * a ^ (3:ℕ) * d * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ - 12 * a ^ (3:ℕ) * d * w *
        ω ^ (7:ℕ) * κ - 6 * a ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (5:ℕ) - 12 * a ^ (3:ℕ) * σ ^ (3:ℕ) *
        w ^ (3:ℕ) * ω ^ (5:ℕ) - 6 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ - 12 *
        a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (7:ℕ) - 24 * a ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω ^ (5:ℕ) * κ - 6
        * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (5:ℕ) - 6 * a ^ (3:ℕ) * σ * w ^ (5:ℕ) * ω ^ (3:ℕ) * κ -
        12 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (7:ℕ) - 6 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (5:ℕ) * κ
        + 6 * a ^ (3:ℕ) * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) * κ ^ (2:ℕ) + 18 * a ^ (3:ℕ) * σ * w *
        ω ^ (9:ℕ) + 12 * a ^ (3:ℕ) * σ * w * ω ^ (7:ℕ) * κ - 6 * a ^ (3:ℕ) * σ * w * ω ^ (5:ℕ) *
        κ ^ (2:ℕ) : ℝ) : ℂ) * I by push_cast; ring), hc, hΔ, zk_re]
  · rw [show (2 * a * d * w * ω ^ (2:ℕ) + 4 * a * σ * w * ω ^ (2:ℕ)) ^ 2 + (-4 * a * d * σ * w * ω
      - 2 * a * σ ^ (2:ℕ) * w * ω - 2 * a * w ^ (3:ℕ) * ω + 4 * a * w * ω ^ (3:ℕ) + 2 * a * w * ω *
      κ) ^ 2 = 4 * a ^ 2 * ω ^ 2 * w ^ 2 * angleZeroR1 d σ w κ ω by
        unfold angleZeroR1; ring,
      show (-6 * d * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 *
          ω ^ (4:ℕ) + 3 * ω ^ (2:ℕ) * κ) ^ 2 + (-6 * d * ω ^ (3:ℕ) - 12 * σ * ω ^ (3:ℕ)) ^ 2 = 9 *
          ω ^ 4 * angleZeroR2 d σ w κ ω by
        unfold angleZeroR2; ring]
    exact zk_final ha.ne' hdet.ne' hα.ne' hω.ne' hw.ne'
      (by unfold angleZeroR1; positivity) (by unfold angleZeroR2; positivity)
      (by unfold bautinFormQ; linear_combination (-576 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ ^ (3:ℕ) *
          w ^ (4:ℕ) * ω ^ (8:ℕ) + 576 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ)
          - 576 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) + 1152 * a ^ (4:ℕ) * d ^ (8:ℕ)
          * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) - 576 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) +
          1440 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 4608 * a ^ (4:ℕ) *
          d ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 72 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (4:ℕ) *
          w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 5184 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) - 288 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 7632 *
          a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 504 * a ^ (4:ℕ) * d ^ (7:ℕ) *
          σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 18432 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) + 2880 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ)
          * κ - 10512 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 2304 *
          a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 432 * a ^ (4:ℕ) *
          d ^ (7:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) + 1584 * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ)
          + 360 * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ - 1584 * a ^ (4:ℕ) * d ^ (7:ℕ)
          * w ^ (4:ℕ) * ω ^ (12:ℕ) - 648 * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 432
          * a ^ (4:ℕ) * d ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 288 * a ^ (4:ℕ) * d ^ (7:ℕ) *
          w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 6804 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) *
          ω ^ (8:ℕ) - 19332 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 324 *
          a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 18036 * a ^ (4:ℕ) *
          d ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 9216 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (5:ℕ)
          * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 38916 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) *
          ω ^ (8:ℕ) - 4680 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 110952
          * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 27576 * a ^ (4:ℕ) *
          d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 252 * a ^ (4:ℕ) * d ^ (6:ℕ) *
          σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 69732 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ)
          * w ^ (2:ℕ) * ω ^ (12:ℕ) - 24120 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ + 180 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) *
          κ ^ (2:ℕ) - 3564 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (8:ℕ) * ω ^ (8:ℕ) - 396 * a ^ (4:ℕ) *
          d ^ (6:ℕ) * σ * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 19476 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (6:ℕ)
          * ω ^ (10:ℕ) + 7992 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 396 *
          a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 25380 * a ^ (4:ℕ) *
          d ^ (6:ℕ) * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) - 17172 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (4:ℕ) *
          ω ^ (10:ℕ) * κ - 2088 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) +
          8892 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) + 8856 * a ^ (4:ℕ) * d ^ (6:ℕ)
          * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 1548 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ ^ (2:ℕ) + 3690 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ)
          - 55908 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) - 432 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 28728 * a ^ (4:ℕ) * d ^ (5:ℕ) *
          σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 43146 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (6:ℕ) *
          w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 102168 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) *
          ω ^ (8:ℕ) - 17640 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ +
          338724 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 120798 * a ^ (4:ℕ)
          * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 3168 * a ^ (4:ℕ) * d ^ (5:ℕ) *
          σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 233460 * a ^ (4:ℕ) * d ^ (5:ℕ) *
          σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 103842 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) *
          w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 10998 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (8:ℕ) * κ ^ (2:ℕ) - 14940 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ)
          - 3456 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 95040 *
          a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 49410 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 3600 * a ^ (4:ℕ) * d ^ (5:ℕ) *
          σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 149868 * a ^ (4:ℕ) * d ^ (5:ℕ) *
          σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 124884 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 19980 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) * κ ^ (2:ℕ) - 144 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) *
          κ ^ (3:ℕ) + 60984 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 70362 *
          a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 16596 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 306 * a ^ (4:ℕ) * d ^ (5:ℕ)
          * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 18 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (10:ℕ)
          * ω ^ (8:ℕ) - 72 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 468 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 954 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ)
          * κ + 144 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 2088 * a ^ (4:ℕ)
          * d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 3906 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (6:ℕ) *
          ω ^ (10:ℕ) * κ - 1242 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 72 *
          a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 2124 * a ^ (4:ℕ) * d ^ (5:ℕ)
          * w ^ (4:ℕ) * ω ^ (14:ℕ) + 4878 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ +
          2412 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 306 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 486 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (2:ℕ) *
          ω ^ (16:ℕ) - 1854 * a ^ (4:ℕ) * d ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ - 1314 * a ^ (4:ℕ)
          * d ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 234 * a ^ (4:ℕ) * d ^ (5:ℕ) *
          w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 13392 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (9:ℕ) *
          w ^ (2:ℕ) * ω ^ (8:ℕ) - 64224 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ)
          - 4896 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ + 15300 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 41724 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 111168 * a ^ (4:ℕ) * d ^ (4:ℕ) *
          σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 34560 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ)
          * ω ^ (6:ℕ) * κ + 576036 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) +
          337716 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 15696 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 437724 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 234648 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 56844 * a ^ (4:ℕ) * d ^ (4:ℕ) *
          σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 21024 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ)
          * w ^ (8:ℕ) * ω ^ (8:ℕ) - 11808 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) *
          ω ^ (6:ℕ) * κ + 235260 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) +
          163692 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 13392 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 441288 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 423432 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 81216 * a ^ (4:ℕ) * d ^ (4:ℕ) *
          σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 1584 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ)
          * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 204588 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) + 260172 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) * κ + 73116 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
          κ ^ (2:ℕ) - 3564 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ)
          + 2448 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (10:ℕ) * ω ^ (8:ℕ) - 576 * a ^ (4:ℕ) * d ^ (4:ℕ)
          * σ * w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 3996 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (8:ℕ) *
          ω ^ (10:ℕ) + 12348 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 1152 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 17388 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (12:ℕ) - 32256 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (6:ℕ) *
          ω ^ (10:ℕ) * κ - 8748 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) -
          576 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 16164 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (14:ℕ) + 38268 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) *
          ω ^ (12:ℕ) * κ + 19476 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) +
          1908 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 3780 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ * w ^ (2:ℕ) * ω ^ (16:ℕ) - 15624 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (2:ℕ) *
          ω ^ (14:ℕ) * κ - 11880 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) -
          2376 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 324 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) - 19440 * a ^ (4:ℕ) * d ^ (3:ℕ) *
          σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 26784 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) *
          w ^ (4:ℕ) * ω ^ (8:ℕ) - 10368 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ)
          * κ - 11808 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) + 9792 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 61056 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 37440 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ)
          * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 554112 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) *
          ω ^ (10:ℕ) + 406080 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ +
          39168 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 465984 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 292464 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ + 25632 * a ^ (4:ℕ) * d ^ (3:ℕ) *
          σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 34272 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ)
          * w ^ (8:ℕ) * ω ^ (8:ℕ) - 19584 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) *
          ω ^ (6:ℕ) * κ + 309600 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) +
          185472 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 26496 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 709344 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 776736 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 269568 * a ^ (4:ℕ) * d ^ (3:ℕ) *
          σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 6912 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ)
          * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 378144 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) + 522576 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) * κ + 168768 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
          κ ^ (2:ℕ) - 34992 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ)
          + 1008 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) - 1728 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 13248 * a ^ (4:ℕ) * d ^ (3:ℕ) *
          σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 16128 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
          w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 3456 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) *
          ω ^ (6:ℕ) * κ ^ (2:ℕ) - 55584 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) *
          ω ^ (12:ℕ) - 101808 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ -
          50976 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 1728 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 44352 * a ^ (4:ℕ)
          * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 111024 * a ^ (4:ℕ) * d ^ (3:ℕ) *
          σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 59328 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 720 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ)
          * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 10800 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
          ω ^ (16:ℕ) - 50832 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ -
          42480 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 9648 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 864 * a ^ (4:ℕ)
          * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) - 9216 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 6336 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ)
          * w ^ (4:ℕ) * ω ^ (8:ℕ) - 8640 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) *
          ω ^ (6:ℕ) * κ - 16992 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) +
          23040 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 21312 * a ^ (4:ℕ)
          * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 21888 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 291168 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) + 239040 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) * κ + 51264 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) *
          κ ^ (2:ℕ) - 263520 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 190080
          * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 42912 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 23616 * a ^ (4:ℕ) * d ^ (2:ℕ)
          * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 15552 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) *
          w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 204768 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) *
          ω ^ (10:ℕ) + 150912 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ +
          30528 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 627840 *
          a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 802944 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 285696 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 14976 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ)
          * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 393696 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) + 588384 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) * κ + 213984 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
          κ ^ (2:ℕ) - 2592 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ)
          + 576 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) - 2304 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 21024 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 36288 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
          w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 4608 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) *
          ω ^ (6:ℕ) * κ ^ (2:ℕ) - 83232 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) *
          ω ^ (12:ℕ) - 149184 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ -
          33696 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 2304 *
          a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 48096 * a ^ (4:ℕ)
          * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 137952 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 81504 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 37728 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) *
          w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 12960 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ)
          * ω ^ (16:ℕ) - 78336 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ -
          74880 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 19584 *
          a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 9216 * a ^ (4:ℕ)
          * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) - 1440 * a ^ (4:ℕ) * d *
          σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 2880 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) - 2304 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ - 4608 *
          a ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) + 6624 * a ^ (4:ℕ) * d * σ ^ (10:ℕ) *
          w ^ (2:ℕ) * ω ^ (8:ℕ) * κ - 4608 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) -
          5760 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ + 75456 * a ^ (4:ℕ) * d *
          σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 84960 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) * κ + 32256 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) -
          61632 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 50976 * a ^ (4:ℕ) * d *
          σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 25632 * a ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) *
          ω ^ (8:ℕ) * κ ^ (2:ℕ) - 6336 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) - 4608 *
          a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ + 58752 * a ^ (4:ℕ) * d * σ ^ (6:ℕ)
          * w ^ (6:ℕ) * ω ^ (10:ℕ) + 77472 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ
          + 20736 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 294336 *
          a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 456768 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 163008 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) *
          κ ^ (2:ℕ) - 16128 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) +
          218880 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 350496 * a ^ (4:ℕ) * d *
          σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 139968 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ ^ (2:ℕ) + 21600 * a ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) *
          κ ^ (3:ℕ) - 3168 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) - 1152 * a ^ (4:ℕ)
          * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) * κ + 15552 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) *
          w ^ (8:ℕ) * ω ^ (10:ℕ) + 12960 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ +
          2304 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 55296 * a ^ (4:ℕ)
          * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 94752 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ)
          * ω ^ (10:ℕ) * κ - 37152 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ)
          - 1152 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 7488 * a ^ (4:ℕ)
          * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) + 53856 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ)
          * ω ^ (12:ℕ) * κ + 44352 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ)
          + 8928 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 4320 * a ^ (4:ℕ)
          * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) - 55008 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ)
          * ω ^ (14:ℕ) * κ - 64800 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ)
          - 19872 * a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 1152 *
          a ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 576 * a ^ (4:ℕ) *
          σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) *
          ω ^ (8:ℕ) * κ + 5184 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 12096 * a ^ (4:ℕ)
          * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 6912 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) *
          ω ^ (6:ℕ) * κ ^ (2:ℕ) + 576 * a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 1152 *
          a ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 1728 * a ^ (4:ℕ) * σ ^ (9:ℕ) *
          w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 8640 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ)
          + 15552 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 6912 * a ^ (4:ℕ) *
          σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) * κ ^ (2:ℕ) - 65664 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ)
          * ω ^ (12:ℕ) - 120960 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 62208 *
          a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 6912 * a ^ (4:ℕ) * σ ^ (7:ℕ)
          * w ^ (4:ℕ) * ω ^ (6:ℕ) * κ ^ (3:ℕ) + 52416 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) *
          ω ^ (14:ℕ) + 86976 * a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 36288 *
          a ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 1728 * a ^ (4:ℕ) * σ ^ (7:ℕ)
          * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 4032 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) *
          ω ^ (10:ℕ) + 4032 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ - 10944 * a ^ (4:ℕ)
          * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 16128 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) *
          ω ^ (10:ℕ) * κ - 5184 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 13248
          * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 12096 * a ^ (4:ℕ) * σ ^ (5:ℕ) *
          w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 2880 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) *
          κ ^ (2:ℕ) + 1728 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 1728 *
          a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) - 12672 * a ^ (4:ℕ) * σ ^ (5:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) * κ - 21888 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) *
          κ ^ (2:ℕ) - 8064 * a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 576 *
          a ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ)) * h2 + (-1152 * a ^ (4:ℕ) *
          d ^ (8:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 1152 * a ^ (4:ℕ) * d ^ (8:ℕ) * σ ^ (2:ℕ)
          * w ^ (2:ℕ) * ω ^ (12:ℕ) + 2880 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) - 12672 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 144 *
          a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 13824 * a ^ (4:ℕ) *
          d ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) - 576 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ ^ (3:ℕ)
          * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 1440 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (6:ℕ) * ω ^ (10:ℕ)
          + 5760 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) + 2448 * a ^ (4:ℕ) *
          d ^ (7:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 3744 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (2:ℕ)
          * ω ^ (14:ℕ) - 2304 * a ^ (4:ℕ) * d ^ (7:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 15480 *
          a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 57456 * a ^ (4:ℕ) *
          d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 288 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ)
          * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 63360 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) - 12672 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ -
          11160 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 576 * a ^ (4:ℕ) *
          d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 56880 * a ^ (4:ℕ) * d ^ (6:ℕ) *
          σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 23256 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 576 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) * κ ^ (2:ℕ) - 36792 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
          ω ^ (14:ℕ) - 24048 * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 792
          * a ^ (4:ℕ) * d ^ (6:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 432 *
          a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 2880 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (6:ℕ)
          * ω ^ (12:ℕ) + 1512 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 5328 *
          a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 5112 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (4:ℕ)
          * ω ^ (12:ℕ) * κ - 1080 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) +
          2880 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 3312 * a ^ (4:ℕ) * d ^ (6:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 1008 * a ^ (4:ℕ) * d ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) *
          κ ^ (2:ℕ) + 18072 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 143280 *
          a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 4428 * a ^ (4:ℕ) * d ^ (5:ℕ)
          * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 137304 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) *
          w ^ (2:ℕ) * ω ^ (12:ℕ) - 56520 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ - 38664 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) +
          4104 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 233280 * a ^ (4:ℕ)
          * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 89712 * a ^ (4:ℕ) * d ^ (5:ℕ) *
          σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 4104 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) *
          w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 161928 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) - 101736 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) * κ + 14832 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) *
          κ ^ (2:ℕ) - 1728 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (8:ℕ) * ω ^ (10:ℕ) + 468 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * σ * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 18504 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (6:ℕ)
          * ω ^ (12:ℕ) + 8568 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 936 *
          a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 29376 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * σ * w ^ (4:ℕ) * ω ^ (14:ℕ) - 33948 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (4:ℕ) *
          ω ^ (12:ℕ) * κ - 6696 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) +
          468 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 11160 * a ^ (4:ℕ) *
          d ^ (5:ℕ) * σ * w ^ (2:ℕ) * ω ^ (16:ℕ) + 20160 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (2:ℕ) *
          ω ^ (14:ℕ) * κ + 8280 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) -
          144 * a ^ (4:ℕ) * d ^ (5:ℕ) * σ * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 9162 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 172476 * a ^ (4:ℕ) * d ^ (4:ℕ) *
          σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 24156 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) *
          w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 147960 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) - 44676 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ -
          52200 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 9396 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 536724 * a ^ (4:ℕ) * d ^ (4:ℕ) *
          σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 225576 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 9396 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) * κ ^ (2:ℕ) - 405108 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (14:ℕ) - 205596 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ +
          71928 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 5436 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 3708 * a ^ (4:ℕ) * d ^ (4:ℕ)
          * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 43488 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) *
          w ^ (6:ℕ) * ω ^ (12:ℕ) + 21996 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) *
          ω ^ (10:ℕ) * κ - 7416 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) *
          κ ^ (2:ℕ) - 29268 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 67644 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ - 6804 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 3708 * a ^ (4:ℕ) * d ^ (4:ℕ)
          * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 10296 * a ^ (4:ℕ) * d ^ (4:ℕ) *
          σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 50724 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 29448 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) * κ ^ (2:ℕ) - 5364 * a ^ (4:ℕ) * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ ^ (3:ℕ) + 306 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (10:ℕ) + 108 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) * κ - 3708 * a ^ (4:ℕ) * d ^ (4:ℕ) *
          w ^ (8:ℕ) * ω ^ (12:ℕ) - 2304 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 324
          * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 15984 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ) + 14184 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) *
          ω ^ (12:ℕ) * κ + 3636 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 324
          * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 27396 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) - 31248 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) *
          ω ^ (14:ℕ) * κ - 11376 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) -
          1584 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 108 * a ^ (4:ℕ) *
          d ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 14814 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (2:ℕ)
          * ω ^ (18:ℕ) + 19980 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) * κ + 8424 *
          a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ ^ (2:ℕ) + 900 * a ^ (4:ℕ) * d ^ (4:ℕ)
          * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) - 54 * a ^ (4:ℕ) * d ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ ^ (4:ℕ) - 27216 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) - 100224 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 50688
          * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 67464 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) + 51768 * a ^ (4:ℕ) * d ^ (3:ℕ) *
          σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 34272 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) *
          w ^ (6:ℕ) * ω ^ (10:ℕ) + 3168 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ)
          * κ + 723384 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) + 271944 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ - 3168 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 604728 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) - 241344 * a ^ (4:ℕ) * d ^ (3:ℕ) *
          σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ + 53424 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (5:ℕ) *
          w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 29952 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) *
          w ^ (8:ℕ) * ω ^ (10:ℕ) + 10944 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) *
          ω ^ (8:ℕ) * κ + 33336 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) - 3384
          * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 21888 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 70416 * a ^ (4:ℕ) * d ^ (3:ℕ)
          * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 64368 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) *
          w ^ (4:ℕ) * ω ^ (12:ℕ) * κ - 21744 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) *
          ω ^ (10:ℕ) * κ ^ (2:ℕ) + 10944 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) * κ ^ (3:ℕ) - 84888 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) *
          ω ^ (16:ℕ) + 84096 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ +
          33840 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 37512 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 5040 * a ^ (4:ℕ)
          * d ^ (3:ℕ) * σ * w ^ (10:ℕ) * ω ^ (10:ℕ) + 864 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (10:ℕ)
          * ω ^ (8:ℕ) * κ - 29304 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (8:ℕ) * ω ^ (12:ℕ) - 16200 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 2592 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ
          * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 126504 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) *
          ω ^ (14:ℕ) + 108720 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (12:ℕ) * κ + 25344 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 2592 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 218232 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ *
          w ^ (4:ℕ) * ω ^ (16:ℕ) - 249840 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (14:ℕ) * κ
          - 93456 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 14616 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 864 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 115992 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ *
          w ^ (2:ℕ) * ω ^ (18:ℕ) + 152568 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (16:ℕ) * κ
          + 60984 * a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ ^ (2:ℕ) + 6408 *
          a ^ (4:ℕ) * d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) + 432 * a ^ (4:ℕ) *
          d ^ (3:ℕ) * σ * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (4:ℕ) - 14544 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 33120 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) - 50976 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) *
          ω ^ (8:ℕ) * κ - 2304 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) + 78480
          * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 6912 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 16416 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 559584 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) *
          w ^ (4:ℕ) * ω ^ (12:ℕ) + 210672 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) *
          ω ^ (10:ℕ) * κ + 16416 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) *
          κ ^ (2:ℕ) - 507024 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) - 183744
          * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ - 28656 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 38880 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 14112 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 29376 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) *
          w ^ (6:ℕ) * ω ^ (12:ℕ) - 26640 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) *
          ω ^ (10:ℕ) * κ - 28224 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) *
          κ ^ (2:ℕ) + 95616 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 54432 *
          a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ + 11232 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 14112 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 55584 * a ^ (4:ℕ) * d ^ (2:ℕ)
          * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 158544 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 34560 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) * κ ^ (2:ℕ) - 24048 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ ^ (3:ℕ) + 8784 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) *
          ω ^ (10:ℕ) + 2592 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) * κ -
          80928 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ) - 57456 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 7776 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 378576 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ) + 332064 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) *
          w ^ (6:ℕ) * ω ^ (12:ℕ) * κ + 75600 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) *
          ω ^ (10:ℕ) * κ ^ (2:ℕ) + 7776 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ)
          * κ ^ (3:ℕ) - 646848 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) -
          731376 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) * κ - 260640 *
          a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) - 34128 *
          a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 2592 * a ^ (4:ℕ)
          * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 340416 * a ^ (4:ℕ) *
          d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (18:ℕ) + 440928 * a ^ (4:ℕ) * d ^ (2:ℕ) *
          σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) * κ + 178272 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) * κ ^ (2:ℕ) + 29664 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) *
          w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) + 7200 * a ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ)
          * ω ^ (10:ℕ) * κ ^ (4:ℕ) - 1728 * a ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) -
          9216 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 23616 * a ^ (4:ℕ) * d *
          σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ - 4608 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) *
          ω ^ (12:ℕ) + 28512 * a ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ - 2304 *
          a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 20736 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) *
          w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 218880 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) +
          121248 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 20736 * a ^ (4:ℕ) * d *
          σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 177408 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) *
          w ^ (2:ℕ) * ω ^ (14:ℕ) - 68832 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ -
          30528 * a ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 16128 *
          a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) + 6336 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) *
          w ^ (8:ℕ) * ω ^ (8:ℕ) * κ + 61056 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) +
          1440 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ - 12672 * a ^ (4:ℕ) * d *
          σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) - 92160 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) *
          w ^ (4:ℕ) * ω ^ (14:ℕ) - 142272 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ
          - 8640 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 6336 *
          a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) + 127008 * a ^ (4:ℕ) * d *
          σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 251136 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) *
          ω ^ (14:ℕ) * κ + 59616 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) +
          864 * a ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) + 10944 * a ^ (4:ℕ)
          * d * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (10:ℕ) + 3456 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ)
          * ω ^ (8:ℕ) * κ - 107136 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ) - 63648 *
          a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 10368 * a ^ (4:ℕ) * d *
          σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 497664 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) *
          w ^ (6:ℕ) * ω ^ (14:ℕ) + 415584 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) * κ
          + 107136 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 10368 *
          a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ) - 845280 * a ^ (4:ℕ) * d *
          σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) - 947520 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) *
          ω ^ (14:ℕ) * κ - 359712 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ)
          - 57312 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (3:ℕ) - 3456 *
          a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 443808 * a ^ (4:ℕ) * d *
          σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (18:ℕ) + 572256 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) *
          ω ^ (16:ℕ) * κ + 240768 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ ^ (2:ℕ)
          + 41472 * a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) + 2880 *
          a ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (4:ℕ) + 288 * a ^ (4:ℕ) *
          σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 1728 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) *
          ω ^ (10:ℕ) - 4032 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ + 5760 * a ^ (4:ℕ)
          * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) + 2304 * a ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) *
          ω ^ (10:ℕ) * κ - 2304 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 6336 * a ^ (4:ℕ)
          * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ + 21312 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) *
          ω ^ (12:ℕ) + 24768 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) * κ + 6336 *
          a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (2:ℕ) + 10944 * a ^ (4:ℕ) * σ ^ (8:ℕ)
          * w ^ (2:ℕ) * ω ^ (14:ℕ) + 5184 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ -
          4032 * a ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) + 1728 * a ^ (4:ℕ) *
          σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ)
          * κ + 43776 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) + 28800 * a ^ (4:ℕ) *
          σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) * κ + 1152 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) *
          ω ^ (8:ℕ) * κ ^ (2:ℕ) - 134208 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 137664
          * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) * κ - 30528 * a ^ (4:ℕ) * σ ^ (6:ℕ) *
          w ^ (4:ℕ) * ω ^ (10:ℕ) * κ ^ (2:ℕ) - 576 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ)
          * κ ^ (3:ℕ) + 134784 * a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 162432 *
          a ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) * κ + 41472 * a ^ (4:ℕ) * σ ^ (6:ℕ) *
          w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (2:ℕ) + 2016 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (10:ℕ) *
          ω ^ (10:ℕ) + 1728 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) * κ - 45504 *
          a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ) - 30528 * a ^ (4:ℕ) * σ ^ (4:ℕ) *
          w ^ (8:ℕ) * ω ^ (10:ℕ) * κ - 5184 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) *
          κ ^ (2:ℕ) + 237312 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ) + 206208 * a ^ (4:ℕ)
          * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) * κ + 56448 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) *
          ω ^ (10:ℕ) * κ ^ (2:ℕ) + 5184 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) * κ ^ (3:ℕ)
          - 410688 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) - 468288 * a ^ (4:ℕ) *
          σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) * κ - 182016 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) *
          ω ^ (12:ℕ) * κ ^ (2:ℕ) - 29376 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) *
          κ ^ (3:ℕ) - 1728 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) * κ ^ (4:ℕ) + 216864 *
          a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (18:ℕ) + 281664 * a ^ (4:ℕ) * σ ^ (4:ℕ) *
          w ^ (2:ℕ) * ω ^ (16:ℕ) * κ + 121536 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) *
          κ ^ (2:ℕ) + 21312 * a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) * κ ^ (3:ℕ) + 1440 *
          a ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) * κ ^ (4:ℕ)) * h1)
  · exact hdet.ne'
  · positivity
  · rw [show (-6 * d * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 *
      ω ^ (4:ℕ) + 3 * ω ^ (2:ℕ) * κ) ^ 2 + (-6 * d * ω ^ (3:ℕ) - 12 * σ * ω ^ (3:ℕ)) ^ 2 = (-6 * d
      * σ * ω ^ (2:ℕ) - 3 * σ ^ (2:ℕ) * ω ^ (2:ℕ) - 3 * w ^ (2:ℕ) * ω ^ (2:ℕ) + 15 * ω ^ (4:ℕ) + 3
      * ω ^ (2:ℕ) * κ) ^ 2 + (6 * d * ω ^ 3 + 12 * σ * ω ^ 3) ^ 2 by ring]
    positivity

/-! ## The critical pair and the first Lyapunov coefficient -/

/-- **The critical right eigenvector** at the frequency `ω` (`a = E/M`, `d = D/M`, `κ = Q/M`,
`σ = R/L`, `w = ω₀`): `q = (aw, iωaw, w(κ + ω² − iωd), (σ + iω)(κ + ω² − iωd))`. -/
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

@[tmio M, powerlib_domain] private theorem angleZeroQ_eq (a d κ σ w ω : ℝ) :
    angleZeroQ a d κ σ w ω = zkQC a d κ σ w ω I := rfl

@[tmio M, powerlib_domain] private theorem angleZeroP_eq (a d κ σ w ω : ℝ) :
    angleZeroP a d κ σ w ω = (starRingEnd ℂ (zkCC a d κ σ w ω I))⁻¹ • zkLC a d σ w ω I := rfl

/-- The data of a physical boundary model of the slice in the atoms of the closed form. -/
@[tmio M, powerlib_domain] private theorem angleZero_data {E V R L w M D : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical)
    (hH : (angleZero E V R L w M D).g.coeff3 * (angleZero E V R L w M D).g.coeff2
          (angleZero E V R L w M D).Q * (angleZero E V R L w M D).g.coeff1
          (angleZero E V R L w M D).Q =
        (angleZero E V R L w M D).g.coeff1 (angleZero E V R L w M D).Q ^ 2 +
          (angleZero E V R L w M D).g.coeff3 ^ 2 * (angleZero E V R L w M D).g.coeff0
            (angleZero E V R L w M D).Q) :
    0 < E / M ∧ 0 < E / L ∧ 0 < D / M ∧ 0 < R / L ∧ 0 < w ∧
      (angleZero E V R L w M D).field 0 = 0 ∧
      E * ((E - V) * R / (R ^ 2 + (w * L) ^ 2)) / M * w =
        (angleZero E V R L w M D).Q / M * (R / L) ∧
      E * (-((E - V) * (w * L)) / (R ^ 2 + (w * L) ^ 2)) / M =
        -((angleZero E V R L w M D).Q / M) := by
  have hR := angleZero_R_pos hp hH
  obtain ⟨hN, hM', hD'⟩ := hp
  have hE : 0 < E := hN.E
  have hL : 0 < L := hN.L
  have hw : 0 < w := hN.ω0
  have hM : 0 < M := hM'
  have hD : 0 < D := hD'
  have hZ : R ^ 2 + (w * L) ^ 2 ≠ 0 := by positivity
  refine ⟨by positivity, by positivity, by positivity, by positivity, hw, ?_, ?_, ?_⟩
  · have h := ((angleZero E V R L w M D).field_point_eq_zero_iff hM.ne' hL.ne'
      hN.absSq_pos.ne').mpr (angleZero_balanced hZ)
    simpa [Model.field] using h
  · rw [angleZero_Q hZ]
    field_simp
  · rw [angleZero_Q hZ]
    field_simp

/-- **The critical pair of a boundary point**: at a frequency `ω > 0` with `ω² = a₁/a₃`, the pair
(`angleZeroQ`, `angleZeroP`) is a critical pair of a physical boundary model of the slice.
Static evidence on the model. -/
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
  obtain ⟨ha, -, hd, hσ, hw, hf, -, -⟩ := angleZero_data hp hH
  obtain ⟨h1, h2⟩ := angleZero_freq_relations hp hH hω2
  rw [angleZeroQ_eq, angleZeroP_eq]
  exact zk_isCriticalPair ha hw hω hσ hd h1 h2 hf (angleZero_jacobianC hp.1.L.ne')

/-- **The first Lyapunov coefficient of the slice in closed form**: for every physical boundary
model with `a₀ > 0` and its frequency `ω` (`ω² = a₁/a₃`),
`ℓ₁ = −4 a² d σ ω 𝔅_Q(d, σ, ω₀, κ) / ((2σ + d)⁴ |r(iω)|² |r(2iω)|²)` at the critical pair
(`angleZeroQ`, `angleZeroP`). Static evidence on the model. -/
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
  obtain ⟨ha, -, hd, hσ, hw, -, hν, hT⟩ := angleZero_data hp hH
  obtain ⟨h1, h2⟩ := angleZero_freq_relations hp hH hω2
  have hdet : 0 < E / M * (E / L) * w -
      (angleZero E V R L w M D).Q / M * ((R / L) ^ 2 + w ^ 2) := by
    have := h0
    rwa [(angleZero_coeffs (E := E) (V := V) (R := R) (L := L) (w := w) (M := M) (D := D)
      hp.1.L.ne').2.2.2] at this
  rw [angleZeroQ_eq, angleZeroP_eq]
  refine zk_firstLyapunov ha hd hσ hw hω hdet hν h1 h2 (angleZero_jacobianC hp.1.L.ne')
    (angleZero_bilinC E V R L w M D) (fun u v z => ?_)
  rw [angleZero_trilinC, show ((E * (-((E - V) * (w * L)) / (R ^ 2 + (w * L) ^ 2)) / M : ℝ) : ℂ) =
    -(((angleZero E V R L w M D).Q / M : ℝ) : ℂ) by rw [hT, ofReal_neg]]
  ext i
  fin_cases i
  all_goals simp [zkTri]
  all_goals ring

/-- The positivity of `a₃` and `a₁` for a physical boundary model of the slice at its frequency. -/
@[tmio M, powerlib_domain] private theorem angleZero_coeff3_pos {E V R L w M D : ℝ}
    (hp : Meets (angleZero E V R L w M D) .physical) :
    0 < (angleZero E V R L w M D).g.coeff3 := by
  obtain ⟨hN, hM', hD'⟩ := hp
  have hL : 0 < L := hN.L
  have hM : 0 < M := hM'
  have hD : 0 < D := hD'
  have hR : 0 ≤ R := hN.R
  rw [(angleZero_coeffs (E := E) (V := V) (R := R) (L := L) (w := w) (M := M) (D := D)
    hL.ne').1]
  positivity

/-- **The symbolic boundary between sub- and supercritical Hopf points of the slice**: for every
critical pair of a physical boundary model with `a₁, a₀ > 0`,
`sign ℓ₁ = −sign 𝔅_Q(D/M, R/L, ω₀, Q/M)` (`angleZero_firstLyapunov` and the normalisation
independence `Line.VSM.Model.sign_firstLyapunov_eq_of_boundary`). Static evidence on the model. -/
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
  have h3 := angleZero_coeff3_pos hp
  have hω := hcp.freq_pos
  have hω2 := (angleZero E V R L w M D).sq_freq_of_isCriticalPair h3.ne' hcp
  obtain ⟨ha, -, hd, hσ, -, -, -, -⟩ := angleZero_data hp hH
  rw [(angleZero E V R L w M D).sign_firstLyapunov_eq_of_boundary h3 h1 h0 hH
    (angleZero_isCriticalPair hp hH hω hω2) hcp, angleZero_firstLyapunov hp hH h0 hω hω2]
  have hpos : 0 < 4 * (E / M) ^ 2 * (D / M) * (R / L) * ω /
      ((2 * (R / L) + D / M) ^ 4 *
        angleZeroR1 (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) ω *
        angleZeroR2 (D / M) (R / L) w ((angleZero E V R L w M D).Q / M) ω) := by
    unfold angleZeroR1 angleZeroR2
    positivity
  rw [sign_mul, sign_neg (neg_lt_zero.mpr hpos), neg_one_mul]

/-! ## Connection conclusions -/

/-- **Supercritical points of the slice**: every physical boundary model of the slice with
`a₁, a₀ > 0` and `𝔅_Q(D/M, R/L, ω₀, Q/M) > 0` is locally asymptotically stable
(`mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`). -/
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
  have hZ : R ^ 2 + (w * L) ^ 2 ≠ 0 := by
    have := hp.1.L
    have := hp.1.ω0
    positivity
  obtain ⟨q, p, hcp⟩ := (angleZero E V R L w M D).exists_isCriticalPair_of_boundary hp
    (angleZero_balanced hZ) h1 h0 hH
  have hs := angleZero_sign_firstLyapunov hp hH h1 h0 hcp
  rw [sign_pos hB] at hs
  exact mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg _ (angleZero_coeff3_pos hp) h1
    h0 hH hcp (sign_eq_neg_one_iff.mp hs)

/-- **Subcritical points of the slice**: every physical boundary model of the slice with
`a₁, a₀ > 0` and `𝔅_Q(D/M, R/L, ω₀, Q/M) < 0` is unstable
(`mem_den_unstable_of_firstLyapunov_pos`). -/
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
  have hZ : R ^ 2 + (w * L) ^ 2 ≠ 0 := by
    have := hp.1.L
    have := hp.1.ω0
    positivity
  obtain ⟨q, p, hcp⟩ := (angleZero E V R L w M D).exists_isCriticalPair_of_boundary hp
    (angleZero_balanced hZ) h1 h0 hH
  have hs := angleZero_sign_firstLyapunov hp hH h1 h0 hcp
  rw [sign_neg hB, neg_neg] at hs
  exact mem_den_unstable_of_firstLyapunov_pos _ (angleZero_coeff3_pos hp) h1 h0 hH hcp
    (sign_eq_one_iff.mp hs)

end VSM
end powerlib.GFM.Line
