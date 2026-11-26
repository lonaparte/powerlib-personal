import theorem.GridTiedConverter.GFM.Line.PSC
import theorem.Dynamics.HopfDichotomy
import theorem.Dynamics.SaddleNodeReduction
import theorem.Dynamics.BTInstability

/-! # Hopf and fold points of power synchronization on a dynamic R–L line

Model boundary.
* The three-state power-synchronization (pure droop) law `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, i_d, i_q) : State 3`,
  grid dq frame at `ω₀`, export-positive power, constant `E`, `δ̇ = K_p (P_ref − P_e)`,
  `L i̇ = E e^{jδ} − V − (R + jX) i`; no active-resistance damping loop, voltage loop, inner
  loops, PLL, delay or PWM. Read about a selected angle (`Line.PSC.Model`), translated so that
  the operating point `(δ*, i_s(δ*))` is the origin.
* Parameter range: every balanced physical model (`P(δ*) = P_ref`, `E, V, L, ω₀, K_p > 0`,
  `R ≥ 0`, any `δ* ∈ ℝ`) on the Hopf boundary of the monic characteristic cubic
  `s³ + a₂ s² + a₁ s + a₀` (`Line.PSC.coeff2` … `coeff0`): `a₂ a₁ = a₀` with `a₁, a₀ > 0`, where
  it factors as `(s² + a₁)(s + a₂)`, `a₂ > 0`: eigenvalues `±iω`, `ω² = a₁`, and the stable root
  `−a₂`. The boundary forces `R > 0`. The fold laws: every balanced physical model with `K = 0`;
  the membership theorems: every physical model, balanced or not.
* Notation: `σ = R/L`, `b = E/L`, `κ = K_p Q` (`Q = Q(δ*)`), `ν = K_p P_ref`, `ρ = σ² + ω₀²`; the
  angle term `t = ω₀ν − σκ = K_p E V sin δ*/L` (`Line.PSC.Model.angleShift`). On the boundary
  `a₂ = 2σ − κ`, `a₁ = ω² = ρ − 2σκ` and `K_p E b ω₀ = 2σ(ω² + κ²)`.
* The rotated frame: rotating the current by `−δ*` (`rotC`) carries the Jacobian and the second
  and third derivatives at the operating point to those of the angle `0` with `κ` and `ν` free;
  the coordinate invariance `NormalForm.LyapunovCoefficient.firstLyapunov_conj` carries `ℓ₁` back.
* Level: exact identities and signs for all parameters and every angle, and Lyapunov instability /
  local asymptotic stability of the operating point (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`, `LyapunovStable`). The bifurcating cycles are private evidence of
  `theorem/GridTiedConverter/GFM/LinePSCHopfCycle.lean` at every Hopf point with `𝔅_P ≠ 0`
  (along the gain `K_p` where its transversality coefficient does not vanish, and along a
  direction of the `(K_p, V)` plane in general, `Dynamics.HopfCycle.exists_hopfCycle_of_branch`);
  their uniqueness and orbital stability are not proved. Not decided: the
  degenerate points `Line.PSC.Model.Degenerate` (located): the zeros of `𝔅_P` on the Hopf
  boundary and the fold points `K = 0` at a zero–Hopf point (`a₂ = 0`, eigenvalues `0, ±i√a₁`,
  or a triple zero). The Bogdanov–Takens gain `K_p D_line = 1` (`a₁ = 0`, a double zero) is
  decided where `a₂ ≠ 0`; the zero–Hopf points with `a₁ > 0` are decided in
  `theorem/GridTiedConverter/GFM/LinePSCZeroHopf.lean`, and the membership with only the triple
  zero and the Bautin-type points left is `theorem/GridTiedConverter/GFM/LinePSCMembership.lean`.
* The fold `a₀ = K_p ρ K = 0` (`K = 0`, a zero eigenvalue): there `Q = E² X/|Z|²`,
  `det(sI − J) = s (s² + a₂ s + a₁)` and `a₁ = ρ (1 − K_p D_line)`,
  `D_line = 2E²RXL/|Z|⁴` (`Line.Network.Dline`); the null vectors are the tangent
  `(1, i_s'(δ*))` of the quasi-steady set and its left partner normalised by `1 − K_p D_line`;
  at `K_p D_line = 1` the Jordan chain `q₁ = (0, −j L E e^{jδ*}/(R + jX)²)` and the left vector
  normalised by `a₂/ρ`, `a₂ = (3R² − X²)/(2RL)` there.

Source: the four-state template `theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean` (same
method); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4
(`NormalForm.LyapunovCoefficient.firstLyapunov`); Carr, *Applications of Centre Manifold Theory*
(1981), §2.4. The closed form was derived with SymPy in exact rational arithmetic in the rotated
frame (Gröbner reduction modulo the boundary relations, factorisation over `ℚ`; untrusted
discovery); every identity is proved here by `linear_combination` with its polynomial
certificate. The family laws are `theorem/Dynamics/HopfDichotomy.lean`. The fold: the
saddle-node law `Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`
(`theorem/Dynamics/SaddleNodeReduction.lean`; Kuznetsov, §3.2 and §5.4, the fold coefficient
`a = ½⟨p, B(q, q)⟩`), as for `Line.VSM` in `theorem/GridTiedConverter/GFM/HopfLineMembership.lean`;
the Bogdanov–Takens law `NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`
(`theorem/Dynamics/BTInstability.lean`; Kuznetsov, §8.4, §8.7); the null pair, the chain and the
coefficients were derived with SymPy (untrusted) and are proved here by `field_simp` and
`linear_combination`.

Results.
* The field in pieces (`Line.PSC.field_eq_pieces`, `Line.PSC.affinePart`, `Line.PSC.constPart`);
  the derivatives at any state `Line.PSC.bilinC_field_eq`, `Line.PSC.trilinC_field_eq` (generic
  laws `bilinC_ridge`, `bilinC_prodRidge`, `trilinC_ridge`, `trilinC_prodRidge`) and at the
  operating point `Line.PSC.Model.bilinC_field`, `Line.PSC.Model.trilinC_field`,
  `Line.PSC.Model.jacobianC_field`, `Line.PSC.Model.jac_eq`, `Line.PSC.Model.analyticAt_field`.
* `Line.PSC.Model.coeff_atoms`, `Line.PSC.Model.R_pos_of_boundary`,
  `Line.PSC.Model.freq_relations_of_boundary`; `Line.PSC.Model.charpoly_eq_of_boundary` (the
  factorization `(s² + a₁)(s + a₂)`), `Line.PSC.Model.sq_freq_of_isCriticalPair`,
  `Line.PSC.Model.exists_charpoly_factor_of_boundary`,
  `Line.PSC.Model.exists_isCriticalPair_of_boundary` (`ℓ₁` is defined at every boundary point),
  `Line.PSC.Model.sign_firstLyapunov_eq_of_boundary` (its sign does not depend on the pair).
* The critical pair at every angle: `Line.PSC.rotC`, `Line.PSC.critVecQ`, `Line.PSC.critVecL`,
  `Line.PSC.critPairing`, `Line.PSC.Model.critQ`, `Line.PSC.Model.critP`,
  `Line.PSC.Model.isCriticalPair_crit`; the angle term `Line.PSC.Model.angleShift`,
  `Line.PSC.Model.angleShift_eq`.
* **`ℓ₁` in closed form at every angle**: `Line.PSC.Model.firstLyapunov_crit`,
  `ℓ₁ = −4σ³(κ² + ω²) 𝔅_P(κ, σ, ω₀, t)/(ω³ ω₀² a₂ (a₂² + ω²)(a₂² + 4ω²))` with the Bautin form
  `𝔅_P = 𝔊_P t (t − 2a₁) + a₂ a₁² ℌ_P` (`Line.PSC.bautinForm`, `Line.PSC.bautinG` of degree 5,
  `Line.PSC.bautinH` of degree 4, polynomials in `(κ, σ, ω₀)`).
* **The symbolic boundary between sub- and supercritical at every angle**:
  `Line.PSC.Model.sign_firstLyapunov_crit` (every critical pair:
  `sign ℓ₁ = −sign 𝔅_P(K_p Q, R/L, ω₀, t)`). The degenerate (Bautin-type) points of the boundary
  are therefore exactly the zeros of `𝔅_P`: located, not decided in general (the second
  Lyapunov coefficient decides a point, `theorem/GridTiedConverter/GFM/HopfBautinPSC.lean`).
* Witnesses on the unit line `E = 1`, `R = L = ω₀ = 1` at `δ* = 0` (`Line.PSC.unitLine V K_p`,
  `t = 0`, `𝔅_P = a₂ a₁² ℌ_P(K_p Q, 1, 1)`): the zero-load model at the critical gain `K_p = 4`
  (`𝔅_P = 64`), the model `V = 20/17`, `K_p = 34` (`κ = −3`, `𝔅_P = −69440`) and an exact
  degenerate point `V = 6/5`, `K_p = 20` (`κ = −2`, `ℌ_P(−2, 1, 1) = 0`;
  `Line.PSC.unitLine_bautin_firstLyapunov`: a critical pair exists and every critical pair has
  `ℓ₁ = 0`; decided unstable by the second Lyapunov coefficient `ℓ₂ = 51200√6/77 > 0` in
  `theorem/GridTiedConverter/GFM/HopfBautinPSC.lean`, `Line.PSC.unitLine_bautin_mem_den_unstable`).
* The fold data at every angle: the tangent `Line.PSC.Model.foldQ` and the left null vector
  `Line.PSC.Model.foldP`, `Line.PSC.Model.coeff_fold` (at `K = 0`: `Q = E² X/|Z|²`,
  `a₁ = ρ (1 − K_p D_line)`), `Line.PSC.Model.isNullPair_fold` (a normalised null pair at `K = 0`,
  `K_p D_line ≠ 1`), `Line.PSC.Model.charpoly_fold` (`s (s² + a₂ s + a₁)`) and
  `Line.PSC.Model.foldCoeff_fold`: the fold coefficient in closed form,
  `a = K_p (P(δ*) − c₀)/(2 (1 − K_p D_line))`, `c₀ = E² R/|Z|²`; at a fold `P(δ*) − c₀ = ± A ≠ 0`,
  so the fold coefficient vanishes nowhere on the fold off `K_p D_line = 1`
  (`Line.PSC.Model.foldCoeff_fold_ne_zero`); through the unnormalised left vector
  `Line.PSC.Model.foldPu` (`Line.PSC.Model.jac_mulVec_foldQ`, `Line.PSC.Model.vecMul_foldPu_jac`,
  `Line.PSC.Model.inner_foldPu_bilin`: `⟨p_u, B(q, q)⟩ = K_p (P(δ*) − c₀)` at every angle).
* The Bogdanov–Takens gain `K_p D_line = 1`: `Line.PSC.Model.btChain`,
  `Line.PSC.Model.jac_mulVec_btChain` (`J q₁ = q₀`), `Line.PSC.Model.foldPu_dot_btChain_eq`
  (`⟨p_u, q₁⟩ = K_p E² L² X (3R² − X²)/|Z|⁶`), `Line.PSC.Model.foldPu_dot_btChain`
  (`ρ ⟨p_u, q₁⟩ = a₂`), `Line.PSC.Model.eq_smul_foldQ_of_mulVec_eq_zero` (one-dimensional
  kernel), `Line.PSC.Model.btLeft`, `Line.PSC.Model.exists_isBTChain_of_bt` (the normalised chain
  for `a₂ ≠ 0`) and `Line.PSC.Model.coeffA_bt`: `a = K_p ρ (P(δ*) − c₀)/(2 a₂)`, which never
  vanishes at a fold (no codimension-three point `a = 0`).
* `Line.PSC.Model.Degenerate`: the degenerate balanced points still undecided: the fold points with
  `a₁ ≥ 0` and `a₂ = 0` (zero–Hopf, or the triple zero at `K_p D_line = 1`, `X² = 3R²`), and the
  zeros of `𝔅_P` on the Hopf boundary.

Family and connection conclusions.
No new family: connection conclusions on `Line.PSC.family`.
* `Line.PSC.mem_den_unstable_of_firstLyapunov_pos` and
  `Line.PSC.mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`: the family laws at a Hopf
  point of the cubic (centre-manifold reduction, analytic field).
* `Line.PSC.mem_den_locallyAsymptoticallyStable_of_bautinForm_pos` (`𝔅_P > 0`: supercritical)
  and `Line.PSC.mem_den_unstable_of_bautinForm_neg` (`𝔅_P < 0`: subcritical), for every balanced
  physical model on the Hopf boundary with `a₁, a₀ > 0`, at every operating angle.
* `Line.PSC.unitLine_critGain_mem_den_locallyAsymptoticallyStable` (supercritical at the critical
  gain) and `Line.PSC.unitLine_subcritical_mem_den_unstable`; hence neither the local asymptotic
  nor the instability translation of `Line.PSC.family` is exact within physical models
  (`Line.PSC.not_exactUnder_locallyAsymptoticallyStable`, `Line.PSC.not_exactUnder_unstable`).
* **`Line.PSC.mem_den_unstable_of_fold`** (the fold is a saddle-node): a balanced physical model
  at `K = 0` with `a₁, a₂ > 0` is unstable; **`Line.PSC.mem_den_unstable_of_fold_of_ne`** (the
  fold decided): at `K = 0` with `a₁ ≠ 0` and `a₂ ≠ 0` it is unstable (a strict Routh violation,
  or the saddle-node law).
* **`Line.PSC.mem_den_unstable_of_bt`** (the Bogdanov–Takens point is a cusp): a balanced
  physical model at `K = 0` with `K_p D_line = 1` and `a₂ > 0` is unstable;
  **`Line.PSC.mem_den_unstable_of_fold_of_coeff2_ne`** (the fold decided off the zero–Hopf
  points): at `K = 0` with `a₂ ≠ 0` it is unstable.
* **`Line.PSC.mem_den_locallyAsymptoticallyStable_iff`** and
  **`Line.PSC.mem_den_lyapunovStable_iff`** (complete membership off the degenerate set, the
  counterpart of `GFL.RatePLL.mem_den_locallyAsymptoticallyStable_iff`): a physical model is
  locally asymptotically stable, equivalently Lyapunov stable, iff it is balanced and either
  meets the strict cubic Routh conditions or lies on the Hopf boundary with `𝔅_P > 0`; every
  other non-degenerate physical model is unstable or not an equilibrium.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace PSC
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

/-! ## The field in pieces and its derivatives at any state -/

section Pieces

variable (g : PSC)

/-- The affine part of the field. -/
def affinePart : State 3 →L[ℝ] State 3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
    !![0, 0, 0; 0, -g.R / g.L, g.X / g.L; 0, -g.X / g.L, -g.R / g.L]

/-- The constant part of the field. -/
def constPart : State 3 := WithLp.toLp 2 ![g.Kp * g.Pref, -g.V / g.L, 0]

/-- The field as an affine field plus four one-nonlinearity terms. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem field_eq_pieces :
    g.field =
      ridge g.affinePart g.constPart (coord 0) (fun t => g.E / g.L * Real.cos t)
          (EuclideanSpace.single 1 1) +
        ridge 0 0 (coord 0) (fun t => g.E / g.L * Real.sin t) (EuclideanSpace.single 2 1) +
        prodRidge (coord 0) (coord 1) Real.cos ((-(g.Kp * g.E)) • EuclideanSpace.single 0 1) +
        prodRidge (coord 0) (coord 2) Real.sin ((-(g.Kp * g.E)) • EuclideanSpace.single 0 1) := by
  funext x
  ext i
  fin_cases i <;>
    simp [field, ridge, prodRidge, affinePart, constPart, Dynamics.toEuclideanCLM_apply,
      Fin.sum_univ_three, Network.power_eq, Network.rateD, Network.rateQ] <;>
    ring

@[tmio M, powerlib_domain] private theorem pc_cos_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.cos t)) (c * Real.sin t) t) :=
  ⟨fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).neg.congr_deriv (by ring)⟩

@[tmio M, powerlib_domain] private theorem pc_sin_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.sin t) (c * Real.cos t) t) ∧
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) :=
  ⟨fun t => (Real.hasDerivAt_sin t).const_mul c,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg⟩

@[tmio M, powerlib_domain] private theorem pc_contDiff_pieces :
    ContDiff ℝ 3 (ridge g.affinePart g.constPart (coord (n := 3) 0)
        (fun t => g.E / g.L * Real.cos t) (EuclideanSpace.single 1 1)) ∧
    ContDiff ℝ 3 (ridge 0 0 (coord (n := 3) 0) (fun t => g.E / g.L * Real.sin t)
        (EuclideanSpace.single 2 1)) ∧
    ContDiff ℝ 3 (prodRidge (coord (n := 3) 0) (coord (n := 3) 1) Real.cos
        ((-(g.Kp * g.E)) • EuclideanSpace.single 0 1)) ∧
    ContDiff ℝ 3 (prodRidge (coord (n := 3) 0) (coord (n := 3) 2) Real.sin
        ((-(g.Kp * g.E)) • EuclideanSpace.single 0 1)) :=
  ⟨contDiff_ridge _ _ _ _ (by fun_prop), contDiff_ridge _ _ _ _ (by fun_prop),
    contDiff_prodRidge _ _ _ Real.contDiff_cos, contDiff_prodRidge _ _ _ Real.contDiff_sin⟩

/-- **The second derivative at any state** `x₀` (angle `δ = x₀ 0`):
`B(u, w) = (K_p P_e u₀w₀ + K_p E (sin δ (u₀w₁ + u₁w₀) − cos δ (u₀w₂ + u₂w₀)),
−(E/L) cos δ u₀w₀, −(E/L) sin δ u₀w₀)`, `P_e` the exported power at `x₀` (generic laws
`bilinC_ridge`, `bilinC_prodRidge`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bilinC_field_eq (x₀ : State 3) (u w : Fin 3 → ℂ) :
    bilinC g.field x₀ u w =
      ![((g.Kp * g.power (x₀ 0) (x₀ 1) (x₀ 2) : ℝ) : ℂ) * (u 0 * w 0) +
          ((g.Kp * g.E * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 1 + u 1 * w 0) -
          ((g.Kp * g.E * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 2 + u 2 * w 0),
        -((g.E / g.L * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0),
        -((g.E / g.L * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0)] := by
  obtain ⟨c1, c2, c3, c4⟩ := pc_contDiff_pieces g
  have k2 : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  rw [field_eq_pieces, bilinC_add, bilinC_add, bilinC_add,
    bilinC_ridge _ _ _ _ (by fun_prop), bilinC_ridge _ _ _ _ (by fun_prop),
    bilinC_prodRidge _ _ _ Real.contDiff_cos Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    bilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos,
    (iteratedDeriv_of_hasDerivAt (pc_cos_chain _).1 (pc_cos_chain _).2.1
      (pc_cos_chain _).2.2 _).2.1,
    (iteratedDeriv_of_hasDerivAt (pc_sin_chain _).1 (pc_sin_chain _).2.1
      (pc_sin_chain _).2.2 _).2.1]
  · ext i
    fin_cases i <;> simp [toC, Network.power_eq] <;> ring
  all_goals first | exact c1.of_le k2 | exact c2.of_le k2 | exact c3.of_le k2 |
    exact c4.of_le k2 | exact (c1.add c2).of_le k2 | exact ((c1.add c2).add c3).of_le k2

/-- **The third derivative at any state** `x₀` (angle `δ = x₀ 0`):
`C(u, w, z) = (K_p E (cos δ Σ₁ + sin δ Σ₂) − K_p Q_e u₀w₀z₀, (E/L) sin δ u₀w₀z₀,
−(E/L) cos δ u₀w₀z₀)`, `Σₖ = u₀w₀zₖ + u₀wₖz₀ + uₖw₀z₀`, `Q_e` the reactive power at `x₀`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem trilinC_field_eq (x₀ : State 3) (u w z : Fin 3 → ℂ) :
    trilinC g.field x₀ u w z =
      ![((g.Kp * g.E * Real.cos (x₀ 0) : ℝ) : ℂ) *
            (u 0 * w 0 * z 1 + u 0 * w 1 * z 0 + u 1 * w 0 * z 0) +
          ((g.Kp * g.E * Real.sin (x₀ 0) : ℝ) : ℂ) *
            (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0) -
          ((g.Kp * g.reactive (x₀ 0) (x₀ 1) (x₀ 2) : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        ((g.E / g.L * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        -((g.E / g.L * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0 * z 0)] := by
  obtain ⟨c1, c2, c3, c4⟩ := pc_contDiff_pieces g
  rw [field_eq_pieces, trilinC_add, trilinC_add, trilinC_add,
    trilinC_ridge _ _ _ _ (by fun_prop), trilinC_ridge _ _ _ _ (by fun_prop),
    trilinC_prodRidge _ _ _ Real.contDiff_cos (Real.hasDerivAt_cos)
      (fun t => (Real.hasDerivAt_sin t).neg)
      (fun t => (Real.hasDerivAt_cos t).neg.congr_deriv (neg_neg _)),
    trilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    (iteratedDeriv_of_hasDerivAt (pc_cos_chain _).1 (pc_cos_chain _).2.1
      (pc_cos_chain _).2.2 _).2.2,
    (iteratedDeriv_of_hasDerivAt (pc_sin_chain _).1 (pc_sin_chain _).2.1
      (pc_sin_chain _).2.2 _).2.2]
  · ext i
    fin_cases i <;> simp [toC, Network.reactive_eq] <;> ring
  all_goals first | exact c1 | exact c2 | exact c3 | exact c4 | exact c1.add c2 |
    exact (c1.add c2).add c3

end Pieces

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

@[tmio M, powerlib_domain] private theorem model_point (m : Model) :
    m.point 0 = m.δ ∧ m.point 1 = (m.g.is m.δ).re ∧ m.point 2 = (m.g.is m.δ).im := by
  simp [Model.point, qss]

/-- **The second derivative of the model field at the operating point**, at every angle `δ*`
(`bilinC_field_eq` at `(δ*, i_s(δ*))`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.bilinC_field (m : Model) (u w : Fin 3 → ℂ) :
    bilinC m.field 0 u w =
      ![((m.g.Kp * m.g.qssPower m.δ : ℝ) : ℂ) * (u 0 * w 0) +
          ((m.g.Kp * m.g.E * Real.sin m.δ : ℝ) : ℂ) * (u 0 * w 1 + u 1 * w 0) -
          ((m.g.Kp * m.g.E * Real.cos m.δ : ℝ) : ℂ) * (u 0 * w 2 + u 2 * w 0),
        -((m.g.E / m.g.L * Real.cos m.δ : ℝ) : ℂ) * (u 0 * w 0),
        -((m.g.E / m.g.L * Real.sin m.δ : ℝ) : ℂ) * (u 0 * w 0)] := by
  obtain ⟨p0, p1, p2⟩ := model_point m
  have h : bilinC m.field 0 = bilinC m.g.field m.point := by
    unfold bilinC
    rw [model_hess]
  rw [h, bilinC_field_eq, p0, p1, p2]
  rfl

/-- **The third derivative of the model field at the operating point**, at every angle `δ*`
(`trilinC_field_eq`; `Q = Q(δ*)`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.trilinC_field (m : Model) (u w z : Fin 3 → ℂ) :
    trilinC m.field 0 u w z =
      ![((m.g.Kp * m.g.E * Real.cos m.δ : ℝ) : ℂ) *
            (u 0 * w 0 * z 1 + u 0 * w 1 * z 0 + u 1 * w 0 * z 0) +
          ((m.g.Kp * m.g.E * Real.sin m.δ : ℝ) : ℂ) *
            (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0) -
          ((m.g.Kp * m.Q : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        ((m.g.E / m.g.L * Real.sin m.δ : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        -((m.g.E / m.g.L * Real.cos m.δ : ℝ) : ℂ) * (u 0 * w 0 * z 0)] := by
  obtain ⟨p0, p1, p2⟩ := model_point m
  have h : trilinC m.field 0 = trilinC m.g.field m.point := by
    unfold trilinC
    rw [model_third]
  rw [h, trilinC_field_eq, p0, p1, p2]
  rfl

/-- The complexified Jacobian of the model field at the operating point is that of `Model.jac`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.jacobianC_field (m : Model) :
    jacobianC m.field 0 = Linear.complexify m.jac := by
  have h : fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jac := by
    rw [show m.field = fun z => m.g.field (z + m.point) from rfl, fderiv_comp_add_right,
      zero_add, m.fderiv_point]
  rw [jacobianC, h, cmat_toEuclideanCLM]
  rfl

/-- The model field is analytic at the operating point (`sin`, `cos` and polynomials). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.analyticAt_field (m : Model) :
    AnalyticAt ℝ m.field 0 := by
  have h : ContDiff ℝ (⊤ : WithTop ℕ∞) m.field :=
    (m.g.contDiff_field (k := ⊤)).comp (contDiff_id.add contDiff_const)
  exact h.contDiffAt.analyticAt

/-- **The Jacobian at the operating point** at every angle `δ*` (`X/L = ω₀`). Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem Model.jac_eq (m : Model) (hL : m.g.L ≠ 0) :
    m.jac = !![m.g.Kp * m.Q, -(m.g.Kp * (m.g.E * Real.cos m.δ)),
        -(m.g.Kp * (m.g.E * Real.sin m.δ));
      -(m.g.E * Real.sin m.δ) / m.g.L, -m.g.R / m.g.L, m.g.ω0;
      m.g.E * Real.cos m.δ / m.g.L, -m.g.ω0, -m.g.R / m.g.L] := by
  have hX : m.g.X / m.g.L = m.g.ω0 := by simp only [Network.X]; field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.jac, jacobian, Model.Q, Network.qssReactive, hX, neg_div]

/-- **The monic coefficients in the atoms** `b = E/L`, `σ = R/L`, `κ = K_p Q`: `a₂ = 2σ − κ`,
`a₁ = σ² + ω₀² − 2σκ`, `a₀ = K_p E b ω₀ − κ(σ² + ω₀²)`, at every operating angle. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.coeff_atoms (m : Model) (hL : m.g.L ≠ 0) :
    m.g.coeff2 m.Q = 2 * (m.g.R / m.g.L) - m.g.Kp * m.Q ∧
      m.g.coeff1 m.Q = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - 2 * (m.g.R / m.g.L) * (m.g.Kp * m.Q) ∧
      m.g.coeff0 m.Q = m.g.Kp * m.g.E * (m.g.E / m.g.L) * m.g.ω0 -
        m.g.Kp * m.Q * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X]
  all_goals field_simp

/-- **The boundary forces a resistive line**: a physical model on the Hopf boundary
`a₂ a₁ = a₀` has `R > 0` (the lossless Routh gap is `−K_p E² X/L² < 0`,
`Line.PSC.routhGap_of_lossless`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.R_pos_of_boundary {m : Model} (hp : Meets m .physical)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) : 0 < m.g.R := by
  obtain ⟨hN, hK⟩ := hp
  rcases hN.R.lt_or_eq with hR | hR
  · exact hR
  · exfalso
    have h := m.g.routhGap_of_lossless hR.symm m.Q
    rw [hH, sub_self] at h
    have hX := hN.X_pos
    have hE := hN.E
    have hL := hN.L
    have : 0 < m.g.Kp * (m.g.E ^ 2 * m.g.X / m.g.L ^ 2) := by positivity
    linarith

/-- **The frequency relations**: at `ω² = a₁` a physical model on the Hopf boundary satisfies
`ω² = σ² + ω₀² − 2σκ` and `K_p E b ω₀ = 2σ(ω² + κ²)` (`b = E/L`, `σ = R/L`, `κ = K_p Q`), at
every operating angle. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.freq_relations_of_boundary {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    ω ^ 2 = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - 2 * (m.g.R / m.g.L) * (m.g.Kp * m.Q) ∧
      m.g.Kp * m.g.E * (m.g.E / m.g.L) * m.g.ω0 =
        2 * (m.g.R / m.g.L) * (ω ^ 2 + (m.g.Kp * m.Q) ^ 2) := by
  obtain ⟨h2, h1, h0⟩ := m.coeff_atoms hp.1.L.ne'
  rw [h1] at hω2
  refine ⟨hω2, ?_⟩
  rw [h2, h1, h0] at hH
  linear_combination -hH - 2 * (m.g.R / m.g.L) * hω2

/-! ## The characteristic polynomial on the Hopf boundary -/

/-- **The cubic factors on its Hopf boundary**: if `a₂ a₁ = a₀`,
`det(sI − J) = (s² + a₁)(s + a₂)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_eq_of_boundary (m : Model)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) :
    (jacobianC m.field 0).charpoly =
      (X ^ 2 + C ((m.g.coeff1 m.Q : ℝ) : ℂ)) * (X + C ((m.g.coeff2 m.Q : ℝ) : ℂ)) := by
  refine Polynomial.funext fun s => ?_
  rw [m.jacobianC_field, ← Linear.det_characteristicMatrix_eq_eval, m.det_characteristicMatrix]
  have hk : ((m.g.coeff0 m.Q : ℝ) : ℂ) = ((m.g.coeff2 m.Q * m.g.coeff1 m.Q : ℝ) : ℂ) := by
    rw [hH]
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
  rw [hk]
  push_cast
  ring

/-- **The frequency of a critical pair**: `iω` is a root of the cubic, so its imaginary part
`ω (a₁ − ω²)` vanishes and `ω² = a₁`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sq_freq_of_isCriticalPair (m : Model) {ω : ℝ}
    {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) : ω ^ 2 = m.g.coeff1 m.Q := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h := hcp.normalized
    simp at h
  have hdet := (Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair m.jac
    ((ω : ℂ) * I)).mpr ⟨q, hq0, by rw [← m.jacobianC_field]; exact hcp.right⟩
  rw [m.det_characteristicMatrix] at hdet
  have him := congrArg Complex.im hdet
  simp [pow_succ, Complex.mul_im, Complex.mul_re] at him
  have hω := hcp.freq_pos
  have h : ω * (m.g.coeff1 m.Q - ω ^ 2) = 0 := by linear_combination him
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hω.ne'
  · linarith

/-- On the Hopf boundary with `a₁ > 0`, `a₂ > 0`, at a frequency with `ω² = a₁`, the
characteristic polynomial is `(s² + ω²)(s + a₂)` with the stable root `−a₂`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_charpoly_factor_of_boundary (m : Model)
    (h2 : 0 < m.g.coeff2 m.Q) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    {ω : ℝ} (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    ∃ r : ℂ[X], (jacobianC m.field 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r ∧
      ∀ s : ℂ, r.eval s = 0 → s.re < 0 := by
  have hchar := m.charpoly_eq_of_boundary hH
  rw [← hω2, Complex.ofReal_pow] at hchar
  refine ⟨_, hchar, fun s hs => ?_⟩
  simp only [eval_add, eval_X, eval_C] at hs
  have hs' : s = -((m.g.coeff2 m.Q : ℝ) : ℂ) := by linear_combination hs
  rw [hs']
  simp [h2]

@[tmio M, powerlib_domain] private theorem coeff2_pos_of_boundary {m : Model}
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) : 0 < m.g.coeff2 m.Q := by
  by_contra h
  push Not at h
  nlinarith

/-- **`ℓ₁` is defined at every boundary point**: a balanced physical model on the Hopf boundary
(`a₁, a₀ > 0`, `a₂ a₁ = a₀`) has a critical pair at the frequency `ω = √a₁`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_isCriticalPair_of_boundary (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q) (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) :
    ∃ q p : Fin 3 → ℂ, IsCriticalPair m.field 0 (Real.sqrt (m.g.coeff1 m.Q)) q p := by
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hω
  have hω0 : 0 < ω := Real.sqrt_pos.mpr h1
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary
    (coeff2_pos_of_boundary h1 h0 hH) hH (Real.sq_sqrt h1.le)
  obtain ⟨q, p, hc⟩ := Dynamics.CenterManifold.exists_isCritical_of_charpoly hω0 hchar hr
  have heq : m.field 0 = 0 := by
    have h := (m.field_point_eq_zero_iff hp.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
    simpa [Model.field] using h
  exact ⟨q, p, heq, hω0, hc.right, hc.left, hc.normalized⟩

/-- **The sign of `ℓ₁` is a property of the model**: on the Hopf boundary (`a₁, a₀ > 0`) all
critical pairs of the model field at the operating point give first Lyapunov coefficients of the
same sign. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_eq_of_boundary (m : Model)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    {ω : ℝ} {q p q' p' : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hcp' : IsCriticalPair m.field 0 ω q' p') :
    SignType.sign (firstLyapunov m.field 0 ω q' p') =
      SignType.sign (firstLyapunov m.field 0 ω q p) := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary
    (coeff2_pos_of_boundary h1 h0 hH) hH (m.sq_freq_of_isCriticalPair hcp)
  exact Dynamics.CenterManifold.sign_firstLyapunov_eq_of_charpoly hchar hr hcp hcp'

/-! ## The family laws at a Hopf point -/

/-- **Subcritical Hopf points are unstable**: a model on the Hopf boundary of the cubic
(`a₁, a₀ > 0`, `a₂ a₁ = a₀`) with a critical pair `(q, p)` of its field at the operating point
and `ℓ₁ = firstLyapunov > 0` is unstable (centre-manifold reduction,
`Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly`; the stable root `−a₂`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_firstLyapunov_pos (m : Model)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hl : 0 < firstLyapunov m.field 0 ω q p) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary
    (coeff2_pos_of_boundary h1 h0 hH) hH (m.sq_freq_of_isCriticalPair hcp)
  exact Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly m.contDiff_field
    m.analyticAt_field hcp hchar hr hl

/-- **Supercritical Hopf points are locally asymptotically stable**: a model on the Hopf boundary
of the cubic with a critical pair whose `ℓ₁` is negative is locally asymptotically stable
(`Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg
    (m : Model) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hl : firstLyapunov m.field 0 ω q p < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary
    (coeff2_pos_of_boundary h1 h0 hH) hH (m.sq_freq_of_isCriticalPair hcp)
  exact Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly
    m.contDiff_field m.analyticAt_field hcp hchar hr hl
/-! ## The Bautin form -/

/-- The coefficient `𝔊_P(κ, σ, w)` of the angle term in the PSC Bautin form. -/
def bautinG (κ σ w : ℝ) : ℝ :=
  -6 * κ ^ 4 * σ + 20 * κ ^ 3 * σ ^ 2 + 4 * κ ^ 3 * w ^ 2 - 35 * κ ^ 2 * σ ^ 3 -
    27 * κ ^ 2 * σ * w ^ 2 + 31 * κ * σ ^ 4 + 38 * κ * σ ^ 2 * w ^ 2 + 7 * κ * w ^ 4 -
    10 * σ ^ 5 - 16 * σ ^ 3 * w ^ 2 - 6 * σ * w ^ 4

/-- The angle-free part `ℌ_P(κ, σ, w)` of the PSC Bautin form. -/
def bautinH (κ σ w : ℝ) : ℝ :=
  -4 * κ ^ 4 + κ ^ 3 * σ + 7 * κ ^ 2 * σ ^ 2 + 3 * κ ^ 2 * w ^ 2 - 4 * κ * σ ^ 3 -
    8 * κ * σ * w ^ 2 + 4 * σ ^ 2 * w ^ 2 + 4 * w ^ 4

/-- **The Bautin form of power synchronization on the line**:
`𝔅_P(κ, σ, w, t) = 𝔊_P t (t − 2a₁) + a₂ a₁² ℌ_P` with `a₁ = σ² + w² − 2σκ`, `a₂ = 2σ − κ`
(`κ = K_p Q`, `σ = R/L`, `w = ω₀`, `t` the angle term `K_p (ω₀ P_ref − σ Q)`). -/
def bautinForm (κ σ w t : ℝ) : ℝ :=
  bautinG κ σ w * t * (t - 2 * (σ ^ 2 + w ^ 2 - 2 * σ * κ)) +
    (2 * σ - κ) * (σ ^ 2 + w ^ 2 - 2 * σ * κ) ^ 2 * bautinH κ σ w

/-! ## Exact algebra of the critical data

The Jacobian pattern of the rotated frame, the critical eigenvectors and the resolvent solutions
as polynomial vectors in complex atoms `G = K_p E`, `B = E/L`, `K = K_p Q`, `N = K_p P_ref`,
`S = σ`, `W = ω₀`, `O = ω` and a square root `j` of `−1`, under the boundary relations
`h1 : O² = S² + W² − 2SK`, `h2 : GBW = 2S(O² + K²)`; every identity is checked by
`linear_combination` with its polynomial certificate. -/

/-- The Jacobian pattern of the rotated frame. -/
private def pcJ (G B K S W : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![K, -G, 0; 0, -S, W; B, -W, -S]

/-- The second-derivative pattern. -/
private def pcBil (G B N : ℂ) (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![N * (u 0 * v 0) - G * (u 0 * v 2 + u 2 * v 0), -B * (u 0 * v 0), 0]

/-- The third-derivative pattern. -/
private def pcTri (G B K : ℂ) (u v z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![G * (u 0 * v 0 * z 1 + u 0 * v 1 * z 0 + u 1 * v 0 * z 0) - K * (u 0 * v 0 * z 0), 0,
    -B * (u 0 * v 0 * z 0)]

/-- The right eigenvector. -/
private def pcQC (B S W O j : ℂ) : Fin 3 → ℂ :=
  ![(S + j * O) ^ 2 + W ^ 2, B * W, B * (S + j * O)]

/-- The unnormalised left eigenvector. -/
private def pcLC (B K S W O j : ℂ) : Fin 3 → ℂ :=
  ![B * W, (S - j * O) * (-(j * O) - K), W * (-(j * O) - K)]

/-- The pairing `⟨p̃, q⟩ = 2BWO(j(2S − K) − O)`. -/
private def pcCC (B K S W O j : ℂ) : ℂ := 2 * B * W * O * (j * (2 * S - K) - O)

/-- `det(2iω − J) = −3O²(2S − K + 2Oj)`. -/
private def pcDC (K S O j : ℂ) : ℂ := -3 * O ^ 2 * (2 * S - K + 2 * O * j)

/-- `det J` times the solution of `J r = B(q, q̄)` (the adjugate applied to `B(q, q̄)`,
reduced modulo the boundary relations). -/
private def pcRC (G B K N S W : ℂ) : Fin 3 → ℂ :=
  ![4 * G * B * K ^ (2:ℕ) * S ^ (3:ℕ) - 4 * G * B * K * S ^ (4:ℕ) + 8 * K ^ (3:ℕ) * S ^ (3:ℕ) * W +
    4 * K ^ (2:ℕ) * N * S ^ (4:ℕ) + 4 * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) -
    24 * K ^ (2:ℕ) * S ^ (4:ℕ) * W - 8 * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) - 8 * K * N * S ^ (5:ℕ) -
    8 * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) + 24 * K * S ^ (5:ℕ) * W + 24 * K * S ^ (3:ℕ) * W ^ (3:ℕ) +
    4 * N * S ^ (6:ℕ) + 8 * N * S ^ (4:ℕ) * W ^ (2:ℕ) + 4 * N * S ^ (2:ℕ) * W ^ (4:ℕ) -
    8 * S ^ (6:ℕ) * W - 16 * S ^ (4:ℕ) * W ^ (3:ℕ) - 8 * S ^ (2:ℕ) * W ^ (5:ℕ),
    12 * B * K ^ (3:ℕ) * S ^ (3:ℕ) + 4 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W -
    32 * B * K ^ (2:ℕ) * S ^ (4:ℕ) - 8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) -
    8 * B * K * N * S ^ (3:ℕ) * W + 28 * B * K * S ^ (5:ℕ) + 28 * B * K * S ^ (3:ℕ) * W ^ (2:ℕ) +
    4 * B * N * S ^ (4:ℕ) * W + 4 * B * N * S ^ (2:ℕ) * W ^ (3:ℕ) - 8 * B * S ^ (6:ℕ) -
    16 * B * S ^ (4:ℕ) * W ^ (2:ℕ) - 8 * B * S ^ (2:ℕ) * W ^ (4:ℕ),
    4 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (2:ℕ) - 4 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) -
    4 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W + 4 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) +
    8 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W - 8 * B * K * N * S ^ (4:ℕ) - 4 * B * K * S ^ (4:ℕ) * W -
    4 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) + 4 * B * N * S ^ (5:ℕ) + 4 * B * N * S ^ (3:ℕ) * W ^ (2:ℕ)]

/-- `pcDC` times the solution of `(2iω − J) s = B(q, q)`. -/
private def pcSC (G B K N S W O j : ℂ) : Fin 3 → ℂ :=
  ![-92 * G * B * K ^ (2:ℕ) * S ^ (3:ℕ) - 24 * G * B * K ^ (2:ℕ) * S ^ (2:ℕ) * O * j +
    44 * G * B * K * S ^ (4:ℕ) - 44 * G * B * K * S ^ (3:ℕ) * O * j + 20 * G * B * S ^ (4:ℕ) * O * j
    + 32 * K ^ (3:ℕ) * N * S ^ (3:ℕ) + 136 * K ^ (3:ℕ) * S ^ (3:ℕ) * W +
    24 * K ^ (3:ℕ) * S ^ (2:ℕ) * W * O * j + 116 * K ^ (2:ℕ) * N * S ^ (4:ℕ) +
    80 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * O * j - 12 * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) -
    296 * K ^ (2:ℕ) * S ^ (4:ℕ) * W - 8 * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O * j -
    24 * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) - 88 * K * N * S ^ (5:ℕ) + 8 * K * N * S ^ (4:ℕ) * O * j
    - 88 * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) - 24 * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j +
    184 * K * S ^ (5:ℕ) * W - 56 * K * S ^ (4:ℕ) * W * O * j + 184 * K * S ^ (3:ℕ) * W ^ (3:ℕ) +
    24 * K * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j + 12 * N * S ^ (6:ℕ) - 16 * N * S ^ (5:ℕ) * O * j +
    24 * N * S ^ (4:ℕ) * W ^ (2:ℕ) - 16 * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j +
    12 * N * S ^ (2:ℕ) * W ^ (4:ℕ) - 24 * S ^ (6:ℕ) * W + 40 * S ^ (5:ℕ) * W * O * j -
    48 * S ^ (4:ℕ) * W ^ (3:ℕ) + 40 * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j - 24 * S ^ (2:ℕ) * W ^ (5:ℕ),
    -20 * B * K ^ (3:ℕ) * S ^ (3:ℕ) + 4 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W -
    32 * B * K ^ (2:ℕ) * S ^ (4:ℕ) - 40 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * O * j +
    8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) + 8 * B * K * N * S ^ (3:ℕ) * W +
    8 * B * K * N * S ^ (2:ℕ) * W * O * j + 36 * B * K * S ^ (5:ℕ) + 16 * B * K * S ^ (4:ℕ) * O * j
    + 36 * B * K * S ^ (3:ℕ) * W ^ (2:ℕ) + 16 * B * K * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j -
    4 * B * N * S ^ (4:ℕ) * W - 4 * B * N * S ^ (2:ℕ) * W ^ (3:ℕ) - 8 * B * S ^ (6:ℕ) -
    16 * B * S ^ (4:ℕ) * W ^ (2:ℕ) - 8 * B * S ^ (2:ℕ) * W ^ (4:ℕ),
    -12 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (2:ℕ) - 12 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) -
    20 * G * B ^ (2:ℕ) * K * S ^ (2:ℕ) * O * j + 8 * G * B ^ (2:ℕ) * S ^ (4:ℕ) +
    4 * G * B ^ (2:ℕ) * S ^ (3:ℕ) * O * j + 12 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W +
    36 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) + 8 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * O * j +
    8 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W + 16 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W * O * j -
    8 * B * K * N * S ^ (4:ℕ) + 24 * B * K * N * S ^ (3:ℕ) * O * j -
    16 * B * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) - 28 * B * K * S ^ (4:ℕ) * W -
    16 * B * K * S ^ (3:ℕ) * W * O * j + 4 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) - 4 * B * N * S ^ (5:ℕ) -
    8 * B * N * S ^ (4:ℕ) * O * j - 4 * B * N * S ^ (3:ℕ) * W ^ (2:ℕ) -
    8 * B * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j + 16 * B * S ^ (5:ℕ) * W +
    8 * B * S ^ (4:ℕ) * W * O * j + 16 * B * S ^ (3:ℕ) * W ^ (3:ℕ) +
    8 * B * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j]

@[tmio M, powerlib_domain] private theorem pc_right {G B K S W O j : ℂ}
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    pcJ G B K S W *ᵥ pcQC B S W O j = (O * j) • pcQC B S W O j := by
  ext k
  fin_cases k <;> simp only [pcJ, pcQC, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
  · linear_combination (-1) * h2 + (K * j ^ (2:ℕ) - 2 * S * j ^ (2:ℕ) - 2 * S - O * j ^ (3:ℕ)) * h1
      + (-2 * K ^ (2:ℕ) * S + 5 * K * S ^ (2:ℕ) + 2 * K * S * O * j + K * W ^ (2:ℕ) - 2 * S ^ (3:ℕ)
      - S ^ (2:ℕ) * O * j - 2 * S * W ^ (2:ℕ) - W ^ (2:ℕ) * O * j) * hj
  · ring
  · ring

@[tmio M, powerlib_domain] private theorem pc_left {G B K S W O j : ℂ}
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    (pcJ G B K S W)ᵀ *ᵥ pcLC B K S W O j = (-(O * j)) • pcLC B K S W O j := by
  ext k
  fin_cases k <;> simp only [pcJ, pcLC, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk]
  · ring
  · linear_combination (-1) * h2 + (K * j ^ (2:ℕ) - 2 * S * j ^ (2:ℕ) - 2 * S + O * j ^ (3:ℕ)) * h1
      + (-2 * K ^ (2:ℕ) * S + 5 * K * S ^ (2:ℕ) - 2 * K * S * O * j + K * W ^ (2:ℕ) - 2 * S ^ (3:ℕ)
      + S ^ (2:ℕ) * O * j - 2 * S * W ^ (2:ℕ) + W ^ (2:ℕ) * O * j) * hj
  · ring

@[tmio M, powerlib_domain] private theorem pc_r {G B K N S W O j : ℂ}
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    pcJ G B K S W *ᵥ pcRC G B K N S W =
      (K * (S ^ 2 + W ^ 2) - G * B * W) • pcBil G B N (pcQC B S W O j) (pcQC B S W (-O) j) := by
  ext k
  fin_cases k <;> simp only [pcJ, pcRC, pcBil, pcQC, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.vecHead, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
  · linear_combination (-2 * G * B * S ^ (3:ℕ) - 2 * G * B * S * W ^ (2:ℕ) +
      2 * G * B * S * O ^ (2:ℕ) * j ^ (2:ℕ) - 4 * K ^ (2:ℕ) * N * S ^ (2:ℕ) +
      4 * K ^ (2:ℕ) * S ^ (2:ℕ) * W * j ^ (2:ℕ) + 4 * K ^ (2:ℕ) * S ^ (2:ℕ) * W +
      8 * K * N * S ^ (3:ℕ) - 10 * K * S ^ (3:ℕ) * W * j ^ (2:ℕ) - 24 * K * S ^ (3:ℕ) * W +
      2 * K * S * W ^ (3:ℕ) - 2 * K * S * W * O ^ (2:ℕ) * j ^ (2:ℕ) - 3 * N * S ^ (4:ℕ) -
      2 * N * S ^ (2:ℕ) * W ^ (2:ℕ) - 2 * N * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + N * W ^ (4:ℕ) +
      2 * N * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + N * O ^ (4:ℕ) * j ^ (4:ℕ) +
      4 * S ^ (4:ℕ) * W * j ^ (2:ℕ) + 12 * S ^ (4:ℕ) * W + 8 * S ^ (2:ℕ) * W ^ (3:ℕ) +
      4 * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) - 4 * S ^ (2:ℕ) * W * O ^ (2:ℕ)) * h2 +
      (4 * G * B * K ^ (2:ℕ) * S ^ (2:ℕ) * j ^ (2:ℕ) - 10 * G * B * K * S ^ (3:ℕ) * j ^ (2:ℕ) +
      4 * G * B * S ^ (4:ℕ) * j ^ (2:ℕ) - 4 * G * B * S ^ (4:ℕ) +
      4 * G * B * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 4 * K ^ (3:ℕ) * N * S ^ (2:ℕ) * j ^ (4:ℕ) -
      4 * K ^ (3:ℕ) * S ^ (2:ℕ) * W * j ^ (2:ℕ) + 12 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * j ^ (4:ℕ) -
      4 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * j ^ (2:ℕ) - 8 * K ^ (2:ℕ) * N * S ^ (3:ℕ) +
      4 * K ^ (2:ℕ) * N * S * W ^ (2:ℕ) * j ^ (4:ℕ) + 4 * K ^ (2:ℕ) * N * S * W ^ (2:ℕ) * j ^ (2:ℕ)
      + 2 * K ^ (2:ℕ) * N * S * O ^ (2:ℕ) * j ^ (4:ℕ) + 24 * K ^ (2:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) -
      9 * K * N * S ^ (4:ℕ) * j ^ (4:ℕ) + 10 * K * N * S ^ (4:ℕ) * j ^ (2:ℕ) +
      16 * K * N * S ^ (4:ℕ) - 10 * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) -
      8 * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) - 5 * K * N * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ)
      - K * N * W ^ (4:ℕ) * j ^ (4:ℕ) - 2 * K * N * W ^ (4:ℕ) * j ^ (2:ℕ) -
      K * N * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) - 40 * K * S ^ (4:ℕ) * W * j ^ (2:ℕ) -
      32 * K * S ^ (4:ℕ) * W - 4 * K * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      4 * K * S ^ (2:ℕ) * W ^ (3:ℕ) - 4 * K * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) +
      2 * N * S ^ (5:ℕ) * j ^ (4:ℕ) - 4 * N * S ^ (5:ℕ) * j ^ (2:ℕ) - 6 * N * S ^ (5:ℕ) +
      4 * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) - 4 * N * S ^ (3:ℕ) * W ^ (2:ℕ) +
      2 * N * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) - 4 * N * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      2 * N * S * W ^ (4:ℕ) * j ^ (4:ℕ) + 4 * N * S * W ^ (4:ℕ) * j ^ (2:ℕ) + 2 * N * S * W ^ (4:ℕ)
      + 2 * N * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      4 * N * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + 2 * N * S * O ^ (4:ℕ) * j ^ (4:ℕ) +
      16 * S ^ (5:ℕ) * W * j ^ (2:ℕ) + 16 * S ^ (5:ℕ) * W + 8 * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      8 * S ^ (3:ℕ) * W ^ (3:ℕ) + 8 * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) -
      8 * S ^ (3:ℕ) * W * O ^ (2:ℕ)) * h1 + (-8 * G * B * K ^ (3:ℕ) * S ^ (3:ℕ) +
      24 * G * B * K ^ (2:ℕ) * S ^ (4:ℕ) - 18 * G * B * K * S ^ (5:ℕ) + 4 * G * B * S ^ (6:ℕ) +
      8 * K ^ (4:ℕ) * N * S ^ (3:ℕ) * j ^ (2:ℕ) - 8 * K ^ (4:ℕ) * N * S ^ (3:ℕ) +
      16 * K ^ (4:ℕ) * S ^ (3:ℕ) * W - 28 * K ^ (3:ℕ) * N * S ^ (4:ℕ) * j ^ (2:ℕ) +
      36 * K ^ (3:ℕ) * N * S ^ (4:ℕ) - 12 * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      4 * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) - 72 * K ^ (3:ℕ) * S ^ (4:ℕ) * W -
      4 * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) + 30 * K ^ (2:ℕ) * N * S ^ (5:ℕ) * j ^ (2:ℕ) -
      54 * K ^ (2:ℕ) * N * S ^ (5:ℕ) + 36 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      20 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) + 6 * K ^ (2:ℕ) * N * S * W ^ (4:ℕ) * j ^ (2:ℕ) +
      2 * K ^ (2:ℕ) * N * S * W ^ (4:ℕ) + 112 * K ^ (2:ℕ) * S ^ (5:ℕ) * W +
      32 * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) - 13 * K * N * S ^ (6:ℕ) * j ^ (2:ℕ) +
      31 * K * N * S ^ (6:ℕ) - 27 * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      29 * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) - 15 * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      3 * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) - K * N * W ^ (6:ℕ) * j ^ (2:ℕ) - K * N * W ^ (6:ℕ) -
      72 * K * S ^ (6:ℕ) * W - 60 * K * S ^ (4:ℕ) * W ^ (3:ℕ) - 4 * K * S ^ (2:ℕ) * W ^ (5:ℕ) +
      2 * N * S ^ (7:ℕ) * j ^ (2:ℕ) - 6 * N * S ^ (7:ℕ) + 6 * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ)
      - 10 * N * S ^ (5:ℕ) * W ^ (2:ℕ) + 6 * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      2 * N * S ^ (3:ℕ) * W ^ (4:ℕ) + 2 * N * S * W ^ (6:ℕ) * j ^ (2:ℕ) + 2 * N * S * W ^ (6:ℕ) +
      16 * S ^ (7:ℕ) * W + 24 * S ^ (5:ℕ) * W ^ (3:ℕ) + 8 * S ^ (3:ℕ) * W ^ (5:ℕ)) * hj
  · linear_combination (4 * B * K ^ (2:ℕ) * S ^ (2:ℕ) - 4 * B * K * S ^ (3:ℕ) - B * S ^ (4:ℕ) -
      2 * B * S ^ (2:ℕ) * W ^ (2:ℕ) + 2 * B * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - B * W ^ (4:ℕ) -
      2 * B * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - B * O ^ (4:ℕ) * j ^ (4:ℕ)) * h2 +
      (4 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * j ^ (4:ℕ) - 12 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * j ^ (4:ℕ) +
      4 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) + 8 * B * K ^ (2:ℕ) * S ^ (3:ℕ) -
      4 * B * K ^ (2:ℕ) * S * W ^ (2:ℕ) * j ^ (4:ℕ) - 4 * B * K ^ (2:ℕ) * S * W ^ (2:ℕ) * j ^ (2:ℕ)
      - 2 * B * K ^ (2:ℕ) * S * O ^ (2:ℕ) * j ^ (4:ℕ) + 9 * B * K * S ^ (4:ℕ) * j ^ (4:ℕ) -
      10 * B * K * S ^ (4:ℕ) * j ^ (2:ℕ) - 8 * B * K * S ^ (4:ℕ) +
      10 * B * K * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) + 8 * B * K * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ)
      + 5 * B * K * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) + B * K * W ^ (4:ℕ) * j ^ (4:ℕ) +
      2 * B * K * W ^ (4:ℕ) * j ^ (2:ℕ) + B * K * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      2 * B * S ^ (5:ℕ) * j ^ (4:ℕ) + 4 * B * S ^ (5:ℕ) * j ^ (2:ℕ) - 2 * B * S ^ (5:ℕ) -
      4 * B * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) - 4 * B * S ^ (3:ℕ) * W ^ (2:ℕ) -
      2 * B * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) + 4 * B * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      2 * B * S * W ^ (4:ℕ) * j ^ (4:ℕ) - 4 * B * S * W ^ (4:ℕ) * j ^ (2:ℕ) - 2 * B * S * W ^ (4:ℕ)
      - 2 * B * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      4 * B * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 2 * B * S * O ^ (4:ℕ) * j ^ (4:ℕ)) * h1 +
      (-8 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) + 8 * B * K ^ (4:ℕ) * S ^ (3:ℕ) +
      28 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * j ^ (2:ℕ) - 36 * B * K ^ (3:ℕ) * S ^ (4:ℕ) +
      12 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      4 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) - 30 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * j ^ (2:ℕ) +
      54 * B * K ^ (2:ℕ) * S ^ (5:ℕ) - 36 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      20 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) - 6 * B * K ^ (2:ℕ) * S * W ^ (4:ℕ) * j ^ (2:ℕ) -
      2 * B * K ^ (2:ℕ) * S * W ^ (4:ℕ) + 13 * B * K * S ^ (6:ℕ) * j ^ (2:ℕ) -
      31 * B * K * S ^ (6:ℕ) + 27 * B * K * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      29 * B * K * S ^ (4:ℕ) * W ^ (2:ℕ) + 15 * B * K * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) +
      3 * B * K * S ^ (2:ℕ) * W ^ (4:ℕ) + B * K * W ^ (6:ℕ) * j ^ (2:ℕ) + B * K * W ^ (6:ℕ) -
      2 * B * S ^ (7:ℕ) * j ^ (2:ℕ) + 6 * B * S ^ (7:ℕ) - 6 * B * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ)
      + 10 * B * S ^ (5:ℕ) * W ^ (2:ℕ) - 6 * B * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) +
      2 * B * S ^ (3:ℕ) * W ^ (4:ℕ) - 2 * B * S * W ^ (6:ℕ) * j ^ (2:ℕ) -
      2 * B * S * W ^ (6:ℕ)) * hj
  · ring

@[tmio M, powerlib_domain] private theorem pc_S {G B K N S W O j : ℂ}
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    ((2 * O * j) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - pcJ G B K S W) *ᵥ pcSC G B K N S W O j =
      pcDC K S O j • pcBil G B N (pcQC B S W O j) (pcQC B S W O j) := by
  ext k
  fin_cases k <;> simp only [pcJ, pcSC, pcBil, pcQC, pcDC, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.vecHead,
      Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.reduceEq, ↓reduceIte, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
  · linear_combination (4 * K ^ (2:ℕ) * N * S ^ (2:ℕ) - 48 * K ^ (2:ℕ) * S ^ (2:ℕ) * W * j ^ (4:ℕ) -
      84 * K ^ (2:ℕ) * S ^ (2:ℕ) * W * j ^ (2:ℕ) + 8 * K ^ (2:ℕ) * S ^ (2:ℕ) * W -
      12 * K ^ (2:ℕ) * S * W * O * j ^ (3:ℕ) + 8 * K * N * S ^ (3:ℕ) + 8 * K * N * S ^ (2:ℕ) * O * j
      + 48 * K * S ^ (3:ℕ) * W * j ^ (4:ℕ) + 74 * K * S ^ (3:ℕ) * W * j ^ (2:ℕ) +
      42 * K * S ^ (3:ℕ) * W + 102 * K * S ^ (2:ℕ) * W * O * j ^ (3:ℕ) +
      34 * K * S ^ (2:ℕ) * W * O * j + 24 * K * S * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      18 * K * S * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 6 * K * S * W * O ^ (2:ℕ) +
      6 * K * W * O ^ (3:ℕ) * j ^ (3:ℕ) + 6 * K * W * O ^ (3:ℕ) * j - 4 * N * S ^ (4:ℕ) -
      4 * N * S ^ (2:ℕ) * W ^ (2:ℕ) - 12 * S ^ (4:ℕ) * W * j ^ (4:ℕ) -
      32 * S ^ (4:ℕ) * W * j ^ (2:ℕ) - 28 * S ^ (4:ℕ) * W - 48 * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) -
      48 * S ^ (3:ℕ) * W * O * j - 8 * S ^ (2:ℕ) * W ^ (3:ℕ) -
      12 * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) - 72 * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) -
      12 * S ^ (2:ℕ) * W * O ^ (2:ℕ) - 48 * S * W * O ^ (3:ℕ) * j ^ (3:ℕ) -
      24 * S * W * O ^ (3:ℕ) * j - 12 * W * O ^ (4:ℕ) * j ^ (4:ℕ) -
      12 * W * O ^ (4:ℕ) * j ^ (2:ℕ)) * h2 + (-48 * G * B * K ^ (2:ℕ) * S ^ (2:ℕ) * j ^ (4:ℕ) -
      84 * G * B * K ^ (2:ℕ) * S ^ (2:ℕ) * j ^ (2:ℕ) - 12 * G * B * K ^ (2:ℕ) * S * O * j ^ (3:ℕ) +
      48 * G * B * K * S ^ (3:ℕ) * j ^ (4:ℕ) + 74 * G * B * K * S ^ (3:ℕ) * j ^ (2:ℕ) +
      6 * G * B * K * S ^ (3:ℕ) + 102 * G * B * K * S ^ (2:ℕ) * O * j ^ (3:ℕ) +
      18 * G * B * K * S ^ (2:ℕ) * O * j + 24 * G * B * K * S * O ^ (2:ℕ) * j ^ (4:ℕ) +
      18 * G * B * K * S * O ^ (2:ℕ) * j ^ (2:ℕ) + 6 * G * B * K * O ^ (3:ℕ) * j ^ (3:ℕ) -
      12 * G * B * S ^ (4:ℕ) * j ^ (4:ℕ) - 32 * G * B * S ^ (4:ℕ) * j ^ (2:ℕ) -
      12 * G * B * S ^ (4:ℕ) - 48 * G * B * S ^ (3:ℕ) * O * j ^ (3:ℕ) -
      48 * G * B * S ^ (3:ℕ) * O * j - 12 * G * B * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      72 * G * B * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 48 * G * B * S * O ^ (3:ℕ) * j ^ (3:ℕ) -
      12 * G * B * O ^ (4:ℕ) * j ^ (4:ℕ) - 12 * K ^ (3:ℕ) * N * S ^ (2:ℕ) * j ^ (4:ℕ) +
      96 * K ^ (3:ℕ) * S ^ (2:ℕ) * W * j ^ (4:ℕ) + 132 * K ^ (3:ℕ) * S ^ (2:ℕ) * W * j ^ (2:ℕ) +
      12 * K ^ (3:ℕ) * S ^ (2:ℕ) * W + 12 * K ^ (3:ℕ) * S * W * O * j ^ (3:ℕ) +
      12 * K ^ (3:ℕ) * S * W * O * j + 132 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * j ^ (4:ℕ) +
      196 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * j ^ (2:ℕ) + 8 * K ^ (2:ℕ) * N * S ^ (3:ℕ) +
      24 * K ^ (2:ℕ) * N * S ^ (2:ℕ) * O * j ^ (5:ℕ) +
      24 * K ^ (2:ℕ) * N * S ^ (2:ℕ) * O * j ^ (3:ℕ) +
      12 * K ^ (2:ℕ) * N * S * W ^ (2:ℕ) * j ^ (4:ℕ) +
      12 * K ^ (2:ℕ) * N * S * W ^ (2:ℕ) * j ^ (2:ℕ) + 6 * K ^ (2:ℕ) * N * S * O ^ (2:ℕ) * j ^ (4:ℕ)
      - 336 * K ^ (2:ℕ) * S ^ (3:ℕ) * W * j ^ (4:ℕ) - 520 * K ^ (2:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) -
      32 * K ^ (2:ℕ) * S ^ (3:ℕ) * W - 144 * K ^ (2:ℕ) * S ^ (2:ℕ) * W * O * j ^ (3:ℕ) -
      72 * K ^ (2:ℕ) * S ^ (2:ℕ) * W * O * j - 24 * K ^ (2:ℕ) * S * W ^ (3:ℕ) * j ^ (4:ℕ) -
      24 * K ^ (2:ℕ) * S * W ^ (3:ℕ) * j ^ (2:ℕ) - 24 * K ^ (2:ℕ) * S * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      24 * K ^ (2:ℕ) * S * W * O ^ (2:ℕ) * j ^ (2:ℕ) - 123 * K * N * S ^ (4:ℕ) * j ^ (4:ℕ) -
      122 * K * N * S ^ (4:ℕ) * j ^ (2:ℕ) + 13 * K * N * S ^ (4:ℕ) -
      24 * K * N * S ^ (3:ℕ) * O * j ^ (5:ℕ) - 132 * K * N * S ^ (3:ℕ) * O * j ^ (3:ℕ) +
      4 * K * N * S ^ (3:ℕ) * O * j - 126 * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) -
      144 * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) - 6 * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) -
      63 * K * N * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      18 * K * N * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 24 * K * N * S * W ^ (2:ℕ) * O * j ^ (5:ℕ) -
      36 * K * N * S * W ^ (2:ℕ) * O * j ^ (3:ℕ) - 12 * K * N * S * W ^ (2:ℕ) * O * j -
      12 * K * N * S * O ^ (3:ℕ) * j ^ (5:ℕ) - 12 * K * N * S * O ^ (3:ℕ) * j ^ (3:ℕ) -
      3 * K * N * W ^ (4:ℕ) * j ^ (4:ℕ) - 6 * K * N * W ^ (4:ℕ) * j ^ (2:ℕ) - 3 * K * N * W ^ (4:ℕ)
      - 3 * K * N * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      6 * K * N * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 3 * K * N * O ^ (4:ℕ) * j ^ (4:ℕ) +
      288 * K * S ^ (4:ℕ) * W * j ^ (4:ℕ) + 456 * K * S ^ (4:ℕ) * W * j ^ (2:ℕ) +
      144 * K * S ^ (4:ℕ) * W + 408 * K * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) +
      176 * K * S ^ (3:ℕ) * W * O * j + 144 * K * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) +
      180 * K * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) + 12 * K * S ^ (2:ℕ) * W ^ (3:ℕ) +
      96 * K * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      84 * K * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 12 * K * S ^ (2:ℕ) * W * O ^ (2:ℕ) +
      12 * K * S * W ^ (3:ℕ) * O * j ^ (3:ℕ) + 12 * K * S * W ^ (3:ℕ) * O * j +
      12 * K * S * W * O ^ (3:ℕ) * j ^ (3:ℕ) + 12 * K * S * W * O ^ (3:ℕ) * j +
      30 * N * S ^ (5:ℕ) * j ^ (4:ℕ) + 28 * N * S ^ (5:ℕ) * j ^ (2:ℕ) - 2 * N * S ^ (5:ℕ) +
      6 * N * S ^ (4:ℕ) * O * j ^ (5:ℕ) + 60 * N * S ^ (4:ℕ) * O * j ^ (3:ℕ) +
      30 * N * S ^ (4:ℕ) * O * j + 60 * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) +
      64 * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 4 * N * S ^ (3:ℕ) * W ^ (2:ℕ) +
      30 * N * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) + 60 * N * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      12 * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (5:ℕ) +
      72 * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) + 36 * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j +
      6 * N * S ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) + 60 * N * S ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
      30 * N * S * W ^ (4:ℕ) * j ^ (4:ℕ) + 36 * N * S * W ^ (4:ℕ) * j ^ (2:ℕ) +
      6 * N * S * W ^ (4:ℕ) + 30 * N * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      36 * N * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + 30 * N * S * O ^ (4:ℕ) * j ^ (4:ℕ) +
      6 * N * W ^ (4:ℕ) * O * j ^ (5:ℕ) + 12 * N * W ^ (4:ℕ) * O * j ^ (3:ℕ) +
      6 * N * W ^ (4:ℕ) * O * j + 6 * N * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) +
      12 * N * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) + 6 * N * O ^ (5:ℕ) * j ^ (5:ℕ) -
      72 * S ^ (5:ℕ) * W * j ^ (4:ℕ) - 152 * S ^ (5:ℕ) * W * j ^ (2:ℕ) - 80 * S ^ (5:ℕ) * W -
      192 * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) - 144 * S ^ (4:ℕ) * W * O * j -
      72 * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) - 112 * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      40 * S ^ (3:ℕ) * W ^ (3:ℕ) - 48 * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      168 * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) - 24 * S ^ (3:ℕ) * W * O ^ (2:ℕ) -
      96 * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) - 48 * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j -
      96 * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) - 48 * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j -
      24 * S * W ^ (5:ℕ) * j ^ (4:ℕ) - 24 * S * W ^ (5:ℕ) * j ^ (2:ℕ) -
      24 * S * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) - 24 * S * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      24 * S * W * O ^ (4:ℕ) * j ^ (4:ℕ) - 24 * S * W * O ^ (4:ℕ) * j ^ (2:ℕ)) * h1 +
      (96 * G * B * K ^ (3:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) + 72 * G * B * K ^ (3:ℕ) * S ^ (3:ℕ) +
      24 * G * B * K ^ (3:ℕ) * S ^ (2:ℕ) * O * j - 144 * G * B * K ^ (2:ℕ) * S ^ (4:ℕ) * j ^ (2:ℕ) -
      88 * G * B * K ^ (2:ℕ) * S ^ (4:ℕ) - 216 * G * B * K ^ (2:ℕ) * S ^ (3:ℕ) * O * j +
      72 * G * B * K * S ^ (5:ℕ) * j ^ (2:ℕ) + 66 * G * B * K * S ^ (5:ℕ) +
      198 * G * B * K * S ^ (4:ℕ) * O * j - 12 * G * B * S ^ (6:ℕ) * j ^ (2:ℕ) -
      20 * G * B * S ^ (6:ℕ) - 48 * G * B * S ^ (5:ℕ) * O * j +
      24 * K ^ (4:ℕ) * N * S ^ (3:ℕ) * j ^ (2:ℕ) - 24 * K ^ (4:ℕ) * N * S ^ (3:ℕ) -
      288 * K ^ (4:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) - 144 * K ^ (4:ℕ) * S ^ (3:ℕ) * W -
      48 * K ^ (4:ℕ) * S ^ (2:ℕ) * W * O * j - 276 * K ^ (3:ℕ) * N * S ^ (4:ℕ) * j ^ (2:ℕ) -
      116 * K ^ (3:ℕ) * N * S ^ (4:ℕ) - 48 * K ^ (3:ℕ) * N * S ^ (3:ℕ) * O * j ^ (3:ℕ) -
      36 * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      12 * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) + 864 * K ^ (3:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) +
      456 * K ^ (3:ℕ) * S ^ (4:ℕ) * W + 504 * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j +
      144 * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) + 36 * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) +
      12 * K ^ (3:ℕ) * S * W ^ (3:ℕ) * O * j + 378 * K ^ (2:ℕ) * N * S ^ (5:ℕ) * j ^ (2:ℕ) +
      62 * K ^ (2:ℕ) * N * S ^ (5:ℕ) + 72 * K ^ (2:ℕ) * N * S ^ (4:ℕ) * O * j ^ (3:ℕ) +
      216 * K ^ (2:ℕ) * N * S ^ (4:ℕ) * O * j +
      396 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      100 * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) +
      72 * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) +
      24 * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j +
      18 * K ^ (2:ℕ) * N * S * W ^ (4:ℕ) * j ^ (2:ℕ) + 6 * K ^ (2:ℕ) * N * S * W ^ (4:ℕ) -
      936 * K ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) - 560 * K ^ (2:ℕ) * S ^ (5:ℕ) * W -
      1056 * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j - 648 * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ)
      - 256 * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) - 168 * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j -
      24 * K ^ (2:ℕ) * S * W ^ (5:ℕ) * j ^ (2:ℕ) - 183 * K * N * S ^ (6:ℕ) * j ^ (2:ℕ) +
      5 * K * N * S ^ (6:ℕ) - 36 * K * N * S ^ (5:ℕ) * O * j ^ (3:ℕ) -
      216 * K * N * S ^ (5:ℕ) * O * j - 369 * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      25 * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) - 72 * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      240 * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j - 189 * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ)
      - 33 * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) - 36 * K * N * S * W ^ (4:ℕ) * O * j ^ (3:ℕ) -
      24 * K * N * S * W ^ (4:ℕ) * O * j - 3 * K * N * W ^ (6:ℕ) * j ^ (2:ℕ) - 3 * K * N * W ^ (6:ℕ)
      + 432 * K * S ^ (6:ℕ) * W * j ^ (2:ℕ) + 328 * K * S ^ (6:ℕ) * W +
      792 * K * S ^ (5:ℕ) * W * O * j + 576 * K * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      284 * K * S ^ (4:ℕ) * W ^ (3:ℕ) + 612 * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j +
      192 * K * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) + 36 * K * S ^ (2:ℕ) * W ^ (5:ℕ) +
      12 * K * S * W ^ (5:ℕ) * O * j + 30 * N * S ^ (7:ℕ) * j ^ (2:ℕ) - 2 * N * S ^ (7:ℕ) +
      6 * N * S ^ (6:ℕ) * O * j ^ (3:ℕ) + 54 * N * S ^ (6:ℕ) * O * j +
      90 * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 2 * N * S ^ (5:ℕ) * W ^ (2:ℕ) +
      18 * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) + 114 * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j +
      90 * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) + 10 * N * S ^ (3:ℕ) * W ^ (4:ℕ) +
      18 * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) + 66 * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j +
      30 * N * S * W ^ (6:ℕ) * j ^ (2:ℕ) + 6 * N * S * W ^ (6:ℕ) + 6 * N * W ^ (6:ℕ) * O * j ^ (3:ℕ)
      + 6 * N * W ^ (6:ℕ) * O * j - 72 * S ^ (7:ℕ) * W * j ^ (2:ℕ) - 80 * S ^ (7:ℕ) * W -
      192 * S ^ (6:ℕ) * W * O * j - 144 * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      120 * S ^ (5:ℕ) * W ^ (3:ℕ) - 288 * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j -
      96 * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) - 40 * S ^ (3:ℕ) * W ^ (5:ℕ) -
      96 * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j - 24 * S * W ^ (7:ℕ) * j ^ (2:ℕ)) * hj
  · linear_combination (12 * B * K ^ (2:ℕ) * S ^ (2:ℕ) + 12 * B * K * S ^ (3:ℕ) +
      20 * B * K * S ^ (2:ℕ) * O * j - 8 * B * S ^ (4:ℕ) - 4 * B * S ^ (3:ℕ) * O * j) * h2 +
      (12 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * j ^ (4:ℕ) - 132 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * j ^ (4:ℕ) -
      116 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) + 24 * B * K ^ (2:ℕ) * S ^ (3:ℕ) -
      24 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * O * j ^ (5:ℕ) -
      24 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * O * j ^ (3:ℕ) -
      12 * B * K ^ (2:ℕ) * S * W ^ (2:ℕ) * j ^ (4:ℕ) -
      12 * B * K ^ (2:ℕ) * S * W ^ (2:ℕ) * j ^ (2:ℕ) - 6 * B * K ^ (2:ℕ) * S * O ^ (2:ℕ) * j ^ (4:ℕ)
      + 16 * B * K * N * S ^ (2:ℕ) * W * j ^ (2:ℕ) + 123 * B * K * S ^ (4:ℕ) * j ^ (4:ℕ) +
      170 * B * K * S ^ (4:ℕ) * j ^ (2:ℕ) + 27 * B * K * S ^ (4:ℕ) +
      24 * B * K * S ^ (3:ℕ) * O * j ^ (5:ℕ) + 132 * B * K * S ^ (3:ℕ) * O * j ^ (3:ℕ) +
      52 * B * K * S ^ (3:ℕ) * O * j + 126 * B * K * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) +
      128 * B * K * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 6 * B * K * S ^ (2:ℕ) * W ^ (2:ℕ) +
      63 * B * K * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      18 * B * K * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + 24 * B * K * S * W ^ (2:ℕ) * O * j ^ (5:ℕ) +
      36 * B * K * S * W ^ (2:ℕ) * O * j ^ (3:ℕ) + 12 * B * K * S * W ^ (2:ℕ) * O * j +
      12 * B * K * S * O ^ (3:ℕ) * j ^ (5:ℕ) + 12 * B * K * S * O ^ (3:ℕ) * j ^ (3:ℕ) +
      3 * B * K * W ^ (4:ℕ) * j ^ (4:ℕ) + 6 * B * K * W ^ (4:ℕ) * j ^ (2:ℕ) + 3 * B * K * W ^ (4:ℕ)
      + 3 * B * K * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      6 * B * K * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + 3 * B * K * O ^ (4:ℕ) * j ^ (4:ℕ) -
      30 * B * S ^ (5:ℕ) * j ^ (4:ℕ) - 60 * B * S ^ (5:ℕ) * j ^ (2:ℕ) - 22 * B * S ^ (5:ℕ) -
      6 * B * S ^ (4:ℕ) * O * j ^ (5:ℕ) - 60 * B * S ^ (4:ℕ) * O * j ^ (3:ℕ) -
      38 * B * S ^ (4:ℕ) * O * j - 60 * B * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) -
      96 * B * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) - 12 * B * S ^ (3:ℕ) * W ^ (2:ℕ) -
      30 * B * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) - 60 * B * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      12 * B * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (5:ℕ) -
      72 * B * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) - 36 * B * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j -
      6 * B * S ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) - 60 * B * S ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
      30 * B * S * W ^ (4:ℕ) * j ^ (4:ℕ) - 36 * B * S * W ^ (4:ℕ) * j ^ (2:ℕ) -
      6 * B * S * W ^ (4:ℕ) - 30 * B * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      36 * B * S * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 30 * B * S * O ^ (4:ℕ) * j ^ (4:ℕ) -
      6 * B * W ^ (4:ℕ) * O * j ^ (5:ℕ) - 12 * B * W ^ (4:ℕ) * O * j ^ (3:ℕ) -
      6 * B * W ^ (4:ℕ) * O * j - 6 * B * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      12 * B * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) - 6 * B * O ^ (5:ℕ) * j ^ (5:ℕ)) * h1 +
      (-24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) + 24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) +
      276 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * j ^ (2:ℕ) - 44 * B * K ^ (3:ℕ) * S ^ (4:ℕ) +
      48 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * O * j ^ (3:ℕ) +
      36 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      12 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) - 32 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W -
      378 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * j ^ (2:ℕ) - 78 * B * K ^ (2:ℕ) * S ^ (5:ℕ) -
      72 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * O * j ^ (3:ℕ) - 216 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * O * j -
      396 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      12 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) -
      72 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      24 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j -
      18 * B * K ^ (2:ℕ) * S * W ^ (4:ℕ) * j ^ (2:ℕ) - 6 * B * K ^ (2:ℕ) * S * W ^ (4:ℕ) +
      16 * B * K * N * S ^ (4:ℕ) * W + 16 * B * K * N * S ^ (2:ℕ) * W ^ (3:ℕ) +
      183 * B * K * S ^ (6:ℕ) * j ^ (2:ℕ) + 107 * B * K * S ^ (6:ℕ) +
      36 * B * K * S ^ (5:ℕ) * O * j ^ (3:ℕ) + 216 * B * K * S ^ (5:ℕ) * O * j +
      369 * B * K * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 121 * B * K * S ^ (4:ℕ) * W ^ (2:ℕ) +
      72 * B * K * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) +
      240 * B * K * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j + 189 * B * K * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ)
      + 17 * B * K * S ^ (2:ℕ) * W ^ (4:ℕ) + 36 * B * K * S * W ^ (4:ℕ) * O * j ^ (3:ℕ) +
      24 * B * K * S * W ^ (4:ℕ) * O * j + 3 * B * K * W ^ (6:ℕ) * j ^ (2:ℕ) + 3 * B * K * W ^ (6:ℕ)
      - 30 * B * S ^ (7:ℕ) * j ^ (2:ℕ) - 30 * B * S ^ (7:ℕ) - 6 * B * S ^ (6:ℕ) * O * j ^ (3:ℕ) -
      54 * B * S ^ (6:ℕ) * O * j - 90 * B * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      66 * B * S ^ (5:ℕ) * W ^ (2:ℕ) - 18 * B * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      114 * B * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j - 90 * B * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      42 * B * S ^ (3:ℕ) * W ^ (4:ℕ) - 18 * B * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) -
      66 * B * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j - 30 * B * S * W ^ (6:ℕ) * j ^ (2:ℕ) -
      6 * B * S * W ^ (6:ℕ) - 6 * B * W ^ (6:ℕ) * O * j ^ (3:ℕ) - 6 * B * W ^ (6:ℕ) * O * j) * hj
  · linear_combination (-40 * B * K * S ^ (2:ℕ) * W * j ^ (2:ℕ) +
      8 * B * S ^ (3:ℕ) * W * j ^ (2:ℕ)) * h2 + (-40 * G * B ^ (2:ℕ) * K * S ^ (2:ℕ) * j ^ (2:ℕ) +
      8 * G * B ^ (2:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) + 16 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * j ^ (2:ℕ) +
      32 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W * j ^ (2:ℕ) + 48 * B * K * N * S ^ (3:ℕ) * j ^ (2:ℕ) -
      112 * B * K * S ^ (3:ℕ) * W * j ^ (2:ℕ) - 16 * B * N * S ^ (4:ℕ) * j ^ (2:ℕ) -
      16 * B * N * S ^ (2:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 32 * B * S ^ (4:ℕ) * W * j ^ (2:ℕ) +
      16 * B * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ)) * h1 + (80 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (3:ℕ)
      - 56 * G * B ^ (2:ℕ) * K * S ^ (4:ℕ) + 8 * G * B ^ (2:ℕ) * S ^ (5:ℕ) -
      32 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) - 144 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W -
      80 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) + 16 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) +
      272 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W + 32 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) +
      80 * B * K * N * S ^ (5:ℕ) + 80 * B * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) -
      176 * B * K * S ^ (5:ℕ) * W - 144 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) - 16 * B * N * S ^ (6:ℕ) -
      32 * B * N * S ^ (4:ℕ) * W ^ (2:ℕ) - 16 * B * N * S ^ (2:ℕ) * W ^ (4:ℕ) +
      32 * B * S ^ (6:ℕ) * W + 48 * B * S ^ (4:ℕ) * W ^ (3:ℕ) + 16 * B * S ^ (2:ℕ) * W ^ (5:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem pc_det2 {G B K S W O j : ℂ}
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    ((2 * O * j) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - pcJ G B K S W).det = pcDC K S O j := by
  simp only [Matrix.det_fin_three, pcJ, pcDC, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.reduceEq, ↓reduceIte]
  linear_combination (1) * h2 + (-4 * K * j ^ (2:ℕ) - 3 * K + 8 * S * j ^ (2:ℕ) + 8 * S +
      8 * O * j ^ (3:ℕ) + 6 * O * j) * h1 + (8 * K ^ (2:ℕ) * S - 20 * K * S ^ (2:ℕ) -
      16 * K * S * O * j - 4 * K * W ^ (2:ℕ) + 8 * S ^ (3:ℕ) + 8 * S ^ (2:ℕ) * O * j +
      8 * S * W ^ (2:ℕ) + 8 * W ^ (2:ℕ) * O * j) * hj

@[tmio M, powerlib_domain] private theorem pc_norm {B K S W O j : ℂ}
    (hB : starRingEnd ℂ B = B) (hK : starRingEnd ℂ K = K) (hS : starRingEnd ℂ S = S)
    (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j)
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K) :
    star (pcLC B K S W O j) ⬝ᵥ pcQC B S W O j = pcCC B K S W O j := by
  simp only [Pi.star_apply, RCLike.star_def, pcLC, pcQC, pcCC, dotProduct, Fin.sum_univ_three,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul, map_sub, map_neg, hB, hK,
      hS, hW, hO, hjc]
  linear_combination (3 * B * W * j ^ (2:ℕ) + 2 * B * W) * h1 + (-6 * B * K * S * W +
      3 * B * S ^ (2:ℕ) * W + 3 * B * W ^ (3:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem pc_Y1 {G B K S W O j : ℂ}
    (hB : starRingEnd ℂ B = B) (hK : starRingEnd ℂ K = K) (hS : starRingEnd ℂ S = S)
    (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j)
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    pairing (pcLC B K S W O j) (pcTri G B K (pcQC B S W O j) (pcQC B S W O j) (pcQC B S W (-O) j)) =
      (24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W - 80 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W +
        104 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W + 40 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) -
        64 * B * K * S ^ (6:ℕ) * W - 64 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) + 16 * B * S ^ (7:ℕ) * W +
        32 * B * S ^ (5:ℕ) * W ^ (3:ℕ) + 16 * B * S ^ (3:ℕ) * W ^ (5:ℕ)) +
        (8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O - 16 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O +
        8 * B * K * S ^ (5:ℕ) * W * O + 8 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O) * j := by
  simp only [pairing_apply, pcLC, pcTri, pcQC, Fin.sum_univ_three, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.vecHead, Matrix.cons_val_fin_one, map_mul, map_sub, map_neg, hB, hK, hS, hW, hO, hjc]
  linear_combination (3 * B * S ^ (4:ℕ) * W + 4 * B * S ^ (3:ℕ) * W * O * j +
      6 * B * S ^ (2:ℕ) * W ^ (3:ℕ) + 2 * B * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) +
      4 * B * S * W ^ (3:ℕ) * O * j + 4 * B * S * W * O ^ (3:ℕ) * j ^ (3:ℕ) + 3 * B * W ^ (5:ℕ) +
      6 * B * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + 3 * B * W * O ^ (4:ℕ) * j ^ (4:ℕ)) * h2 +
      (-12 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W * j ^ (4:ℕ) -
      8 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * j ^ (6:ℕ) + 30 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * j ^ (4:ℕ)
      + 4 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) -
      4 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W * O * j ^ (7:ℕ) +
      8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W * O * j ^ (3:ℕ) +
      6 * B * K ^ (2:ℕ) * S * W ^ (3:ℕ) * j ^ (4:ℕ) + 12 * B * K ^ (2:ℕ) * S * W ^ (3:ℕ) * j ^ (2:ℕ)
      + 6 * B * K ^ (2:ℕ) * S * W * O ^ (2:ℕ) * j ^ (4:ℕ) + 8 * B * K * S ^ (4:ℕ) * W * j ^ (6:ℕ) -
      32 * B * K * S ^ (4:ℕ) * W * j ^ (4:ℕ) - 8 * B * K * S ^ (4:ℕ) * W * j ^ (2:ℕ) +
      4 * B * K * S ^ (3:ℕ) * W * O * j ^ (7:ℕ) - 2 * B * K * S ^ (3:ℕ) * W * O * j ^ (5:ℕ) -
      16 * B * K * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) + 8 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (6:ℕ) -
      16 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) -
      24 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      4 * B * K * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (6:ℕ) -
      12 * B * K * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) + 4 * B * K * S * W ^ (3:ℕ) * O * j ^ (7:ℕ)
      + 6 * B * K * S * W ^ (3:ℕ) * O * j ^ (5:ℕ) + 2 * B * K * S * W * O ^ (3:ℕ) * j ^ (7:ℕ) -
      2 * B * S ^ (5:ℕ) * W * j ^ (6:ℕ) + 10 * B * S ^ (5:ℕ) * W * j ^ (4:ℕ) +
      2 * B * S ^ (5:ℕ) * W * j ^ (2:ℕ) + 6 * B * S ^ (5:ℕ) * W - B * S ^ (4:ℕ) * W * O * j ^ (7:ℕ)
      + B * S ^ (4:ℕ) * W * O * j ^ (5:ℕ) + 9 * B * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) +
      8 * B * S ^ (4:ℕ) * W * O * j - 4 * B * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (6:ℕ) +
      12 * B * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) + 12 * B * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      12 * B * S ^ (3:ℕ) * W ^ (3:ℕ) - 2 * B * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (6:ℕ) +
      10 * B * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) + 4 * B * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ)
      - 2 * B * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (7:ℕ) -
      2 * B * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) + 6 * B * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ)
      + 8 * B * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j - B * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j ^ (7:ℕ) +
      B * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) + 8 * B * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) -
      2 * B * S * W ^ (5:ℕ) * j ^ (6:ℕ) + 2 * B * S * W ^ (5:ℕ) * j ^ (4:ℕ) +
      10 * B * S * W ^ (5:ℕ) * j ^ (2:ℕ) + 6 * B * S * W ^ (5:ℕ) -
      2 * B * S * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (6:ℕ) + 2 * B * S * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ)
      + 12 * B * S * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 2 * B * S * W * O ^ (4:ℕ) * j ^ (6:ℕ) +
      6 * B * S * W * O ^ (4:ℕ) * j ^ (4:ℕ) - B * W ^ (5:ℕ) * O * j ^ (7:ℕ) -
      3 * B * W ^ (5:ℕ) * O * j ^ (5:ℕ) - 3 * B * W ^ (5:ℕ) * O * j ^ (3:ℕ) -
      B * W ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (7:ℕ) - 3 * B * W ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      B * W * O ^ (5:ℕ) * j ^ (7:ℕ)) * h1 + (24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) -
      24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W + 16 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * j ^ (4:ℕ) -
      88 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) + 80 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W +
      8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j ^ (5:ℕ) -
      8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) - 8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j
      - 24 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (4:ℕ) +
      118 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) - 98 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W -
      12 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j ^ (5:ℕ) +
      16 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) +
      24 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j -
      24 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) +
      92 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      28 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) -
      12 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) +
      8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j +
      6 * B * K ^ (2:ℕ) * S * W ^ (5:ℕ) * j ^ (2:ℕ) + 6 * B * K ^ (2:ℕ) * S * W ^ (5:ℕ) +
      12 * B * K * S ^ (6:ℕ) * W * j ^ (4:ℕ) - 64 * B * K * S ^ (6:ℕ) * W * j ^ (2:ℕ) +
      52 * B * K * S ^ (6:ℕ) * W + 6 * B * K * S ^ (5:ℕ) * W * O * j ^ (5:ℕ) -
      10 * B * K * S ^ (5:ℕ) * W * O * j ^ (3:ℕ) - 24 * B * K * S ^ (5:ℕ) * W * O * j +
      24 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) -
      96 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) + 40 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) +
      12 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) -
      4 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) - 24 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j
      + 12 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) -
      32 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) - 12 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) +
      6 * B * K * S * W ^ (5:ℕ) * O * j ^ (5:ℕ) + 6 * B * K * S * W ^ (5:ℕ) * O * j ^ (3:ℕ) -
      2 * B * S ^ (7:ℕ) * W * j ^ (4:ℕ) + 12 * B * S ^ (7:ℕ) * W * j ^ (2:ℕ) -
      10 * B * S ^ (7:ℕ) * W - B * S ^ (6:ℕ) * W * O * j ^ (5:ℕ) +
      2 * B * S ^ (6:ℕ) * W * O * j ^ (3:ℕ) + 7 * B * S ^ (6:ℕ) * W * O * j -
      6 * B * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) + 28 * B * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      14 * B * S ^ (5:ℕ) * W ^ (3:ℕ) - 3 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) +
      2 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) + 13 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j -
      6 * B * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) + 20 * B * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      2 * B * S ^ (3:ℕ) * W ^ (5:ℕ) - 3 * B * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j ^ (5:ℕ) -
      2 * B * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) + 5 * B * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j -
      2 * B * S * W ^ (7:ℕ) * j ^ (4:ℕ) + 4 * B * S * W ^ (7:ℕ) * j ^ (2:ℕ) + 6 * B * S * W ^ (7:ℕ)
      - B * W ^ (7:ℕ) * O * j ^ (5:ℕ) - 2 * B * W ^ (7:ℕ) * O * j ^ (3:ℕ) -
      B * W ^ (7:ℕ) * O * j) * hj

@[tmio M, powerlib_domain] private theorem pc_Y2 {G B K N S W O j : ℂ}
    (hB : starRingEnd ℂ B = B) (hK : starRingEnd ℂ K = K) (hS : starRingEnd ℂ S = S)
    (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j)
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    pairing (pcLC B K S W O j) (pcBil G B N (pcQC B S W O j) (pcRC G B K N S W)) =
      (-16 * G * B ^ (2:ℕ) * K ^ (5:ℕ) * S ^ (4:ℕ) + 48 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (5:ℕ) -
        48 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (6:ℕ) + 16 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (7:ℕ) +
        16 * B * K ^ (6:ℕ) * S ^ (4:ℕ) * W - 96 * B * K ^ (5:ℕ) * S ^ (5:ℕ) * W +
        16 * B * K ^ (4:ℕ) * N * S ^ (6:ℕ) + 16 * B * K ^ (4:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) +
        192 * B * K ^ (4:ℕ) * S ^ (6:ℕ) * W + 32 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
        8 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (5:ℕ) * W +
        8 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) - 48 * B * K ^ (3:ℕ) * N * S ^ (7:ℕ) -
        64 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) -
        16 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) - 160 * B * K ^ (3:ℕ) * S ^ (7:ℕ) * W -
        96 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) - 16 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (6:ℕ) * W
        - 16 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
        48 * B * K ^ (2:ℕ) * N * S ^ (8:ℕ) + 96 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * W ^ (2:ℕ) +
        48 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (4:ℕ) + 48 * B * K ^ (2:ℕ) * S ^ (8:ℕ) * W +
        64 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) + 16 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) +
        8 * B * K * N ^ (2:ℕ) * S ^ (7:ℕ) * W + 16 * B * K * N ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) +
        8 * B * K * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) - 16 * B * K * N * S ^ (9:ℕ) -
        48 * B * K * N * S ^ (7:ℕ) * W ^ (2:ℕ) - 48 * B * K * N * S ^ (5:ℕ) * W ^ (4:ℕ) -
        16 * B * K * N * S ^ (3:ℕ) * W ^ (6:ℕ)) + (-16 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (4:ℕ) * O +
        48 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (5:ℕ) * O -
        48 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (6:ℕ) * O + 16 * G * B ^ (2:ℕ) * K * S ^ (7:ℕ) * O +
        16 * B * K ^ (5:ℕ) * S ^ (4:ℕ) * W * O - 96 * B * K ^ (4:ℕ) * S ^ (5:ℕ) * W * O +
        16 * B * K ^ (3:ℕ) * N * S ^ (6:ℕ) * O + 16 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O
        + 192 * B * K ^ (3:ℕ) * S ^ (6:ℕ) * W * O + 32 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O +
        8 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (5:ℕ) * W * O +
        8 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O -
        48 * B * K ^ (2:ℕ) * N * S ^ (7:ℕ) * O - 64 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O
        - 16 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O -
        160 * B * K ^ (2:ℕ) * S ^ (7:ℕ) * W * O - 96 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O -
        16 * B * K * N ^ (2:ℕ) * S ^ (6:ℕ) * W * O -
        16 * B * K * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O + 48 * B * K * N * S ^ (8:ℕ) * O +
        96 * B * K * N * S ^ (6:ℕ) * W ^ (2:ℕ) * O + 48 * B * K * N * S ^ (4:ℕ) * W ^ (4:ℕ) * O +
        48 * B * K * S ^ (8:ℕ) * W * O + 64 * B * K * S ^ (6:ℕ) * W ^ (3:ℕ) * O +
        16 * B * K * S ^ (4:ℕ) * W ^ (5:ℕ) * O + 8 * B * N ^ (2:ℕ) * S ^ (7:ℕ) * W * O +
        16 * B * N ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O +
        8 * B * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * O - 16 * B * N * S ^ (9:ℕ) * O -
        48 * B * N * S ^ (7:ℕ) * W ^ (2:ℕ) * O - 48 * B * N * S ^ (5:ℕ) * W ^ (4:ℕ) * O -
        16 * B * N * S ^ (3:ℕ) * W ^ (6:ℕ) * O) * j := by
  simp only [pairing_apply, pcLC, pcBil, pcQC, pcRC, Fin.sum_univ_three, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.vecHead, Matrix.cons_val_fin_one, map_mul, map_sub, map_neg, hB, hK, hS, hW, hO, hjc]
  linear_combination (-8 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (4:ℕ) -
      12 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (3:ℕ) * O * j -
      4 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) -
      4 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      8 * G * B ^ (2:ℕ) * K * S ^ (5:ℕ) + 12 * G * B ^ (2:ℕ) * K * S ^ (4:ℕ) * O * j +
      4 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) * W ^ (2:ℕ) +
      4 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      8 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) - 8 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W +
      8 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * j ^ (4:ℕ) + 36 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ)
      + 8 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W + 4 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) +
      4 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j + 4 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) +
      4 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) - 4 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ)
      - 4 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * O * j - 4 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) -
      4 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j -
      12 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (4:ℕ) -
      48 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) - 4 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W -
      16 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) -
      24 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j -
      4 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      20 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) -
      8 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) +
      8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j + 12 * B * K * N * S ^ (6:ℕ) +
      16 * B * K * N * S ^ (5:ℕ) * O * j + 12 * B * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) +
      4 * B * K * N * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      8 * B * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j + 4 * B * K * S ^ (6:ℕ) * W * j ^ (4:ℕ) +
      20 * B * K * S ^ (6:ℕ) * W * j ^ (2:ℕ) - 4 * B * K * S ^ (6:ℕ) * W +
      12 * B * K * S ^ (5:ℕ) * W * O * j ^ (3:ℕ) + 12 * B * K * S ^ (5:ℕ) * W * O * j -
      16 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) + 4 * B * K * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      16 * B * K * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 8 * B * K * S ^ (4:ℕ) * W * O ^ (2:ℕ) -
      16 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j + 4 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) +
      4 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 8 * B * N * S ^ (7:ℕ) -
      12 * B * N * S ^ (6:ℕ) * O * j - 16 * B * N * S ^ (5:ℕ) * W ^ (2:ℕ) -
      4 * B * N * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 16 * B * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j -
      8 * B * N * S ^ (3:ℕ) * W ^ (4:ℕ) - 4 * B * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)
      - 4 * B * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j + 8 * B * S ^ (7:ℕ) * W +
      8 * B * S ^ (6:ℕ) * W * O * j + 16 * B * S ^ (5:ℕ) * W ^ (3:ℕ) +
      16 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j + 8 * B * S ^ (3:ℕ) * W ^ (5:ℕ) +
      8 * B * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j) * h2 +
      (-8 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) +
      8 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (4:ℕ) * j ^ (4:ℕ) +
      36 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (4:ℕ) * j ^ (2:ℕ) +
      4 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (3:ℕ) * O * j ^ (3:ℕ) -
      12 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (5:ℕ) * j ^ (4:ℕ) -
      48 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (5:ℕ) * j ^ (2:ℕ) -
      16 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (5:ℕ) -
      16 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (4:ℕ) * O * j ^ (3:ℕ) -
      24 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (4:ℕ) * O * j -
      4 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      8 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      4 * G * B ^ (2:ℕ) * K * S ^ (6:ℕ) * j ^ (4:ℕ) + 20 * G * B ^ (2:ℕ) * K * S ^ (6:ℕ) * j ^ (2:ℕ)
      + 16 * G * B ^ (2:ℕ) * K * S ^ (6:ℕ) + 12 * G * B ^ (2:ℕ) * K * S ^ (5:ℕ) * O * j ^ (3:ℕ) +
      24 * G * B ^ (2:ℕ) * K * S ^ (5:ℕ) * O * j +
      4 * G * B ^ (2:ℕ) * K * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      8 * G * B ^ (2:ℕ) * K * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      8 * B * K ^ (5:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) + 8 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W * j ^ (4:ℕ)
      - 48 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) - 32 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W +
      8 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) +
      8 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * j ^ (4:ℕ) + 20 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * j ^ (2:ℕ)
      + 4 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * O * j ^ (3:ℕ) +
      8 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) +
      20 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      4 * B * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      16 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W * j ^ (4:ℕ) +
      96 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) + 64 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W -
      40 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) + 8 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * O * j
      - 24 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) -
      16 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) -
      8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) -
      8 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      4 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) +
      4 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      20 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * j ^ (4:ℕ) -
      60 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * j ^ (2:ℕ) - 8 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) -
      20 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * O * j ^ (3:ℕ) - 8 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * O * j
      - 24 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) -
      72 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      8 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) -
      4 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      20 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      8 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j -
      4 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (4:ℕ) -
      12 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      4 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      24 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W * j ^ (4:ℕ) -
      56 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W * j ^ (2:ℕ) - 56 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W +
      64 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * O * j ^ (3:ℕ) -
      48 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * O * j +
      72 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) +
      64 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      16 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
      16 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      40 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) -
      16 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) +
      48 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      16 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j +
      8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) +
      8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      8 * B * K * N ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) -
      8 * B * K * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      16 * B * K * N * S ^ (7:ℕ) * j ^ (4:ℕ) + 60 * B * K * N * S ^ (7:ℕ) * j ^ (2:ℕ) +
      24 * B * K * N * S ^ (7:ℕ) + 28 * B * K * N * S ^ (6:ℕ) * O * j ^ (3:ℕ) +
      32 * B * K * N * S ^ (6:ℕ) * O * j + 32 * B * K * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) +
      104 * B * K * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 24 * B * K * N * S ^ (5:ℕ) * W ^ (2:ℕ) +
      8 * B * K * N * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      8 * B * K * N * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      32 * B * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) +
      16 * B * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j +
      16 * B * K * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (4:ℕ) +
      44 * B * K * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) +
      8 * B * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      4 * B * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) - 24 * B * K * S ^ (7:ℕ) * W * j ^ (4:ℕ)
      - 24 * B * K * S ^ (7:ℕ) * W * j ^ (2:ℕ) + 8 * B * K * S ^ (7:ℕ) * W -
      56 * B * K * S ^ (6:ℕ) * W * O * j ^ (3:ℕ) + 24 * B * K * S ^ (6:ℕ) * W * O * j -
      72 * B * K * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) -
      104 * B * K * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) - 16 * B * K * S ^ (5:ℕ) * W ^ (3:ℕ) -
      16 * B * K * S ^ (5:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      32 * B * K * S ^ (5:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 16 * B * K * S ^ (5:ℕ) * W * O ^ (2:ℕ) -
      88 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) -
      32 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j - 40 * B * K * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) -
      40 * B * K * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) + 8 * B * K * S ^ (3:ℕ) * W ^ (5:ℕ) -
      24 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      8 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      8 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) +
      4 * B * N ^ (2:ℕ) * S ^ (6:ℕ) * W * j ^ (2:ℕ) +
      8 * B * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      4 * B * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) - 4 * B * N * S ^ (8:ℕ) * j ^ (4:ℕ) -
      20 * B * N * S ^ (8:ℕ) * j ^ (2:ℕ) - 16 * B * N * S ^ (8:ℕ) -
      12 * B * N * S ^ (7:ℕ) * O * j ^ (3:ℕ) - 24 * B * N * S ^ (7:ℕ) * O * j -
      12 * B * N * S ^ (6:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) -
      52 * B * N * S ^ (6:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) - 32 * B * N * S ^ (6:ℕ) * W ^ (2:ℕ) -
      4 * B * N * S ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) - 8 * B * N * S ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)
      - 24 * B * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      32 * B * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j - 12 * B * N * S ^ (4:ℕ) * W ^ (4:ℕ) * j ^ (4:ℕ) -
      44 * B * N * S ^ (4:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) - 16 * B * N * S ^ (4:ℕ) * W ^ (4:ℕ) -
      8 * B * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      8 * B * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      12 * B * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) - 8 * B * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j
      - 4 * B * N * S ^ (2:ℕ) * W ^ (6:ℕ) * j ^ (4:ℕ) -
      12 * B * N * S ^ (2:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) -
      4 * B * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) + 8 * B * S ^ (8:ℕ) * W * j ^ (4:ℕ)
      + 24 * B * S ^ (8:ℕ) * W * j ^ (2:ℕ) + 16 * B * S ^ (8:ℕ) * W +
      24 * B * S ^ (7:ℕ) * W * O * j ^ (3:ℕ) + 16 * B * S ^ (7:ℕ) * W * O * j +
      24 * B * S ^ (6:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) + 56 * B * S ^ (6:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      32 * B * S ^ (6:ℕ) * W ^ (3:ℕ) + 8 * B * S ^ (6:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      48 * B * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) + 32 * B * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j +
      24 * B * S ^ (4:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) + 40 * B * S ^ (4:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      16 * B * S ^ (4:ℕ) * W ^ (5:ℕ) + 16 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      24 * B * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) + 16 * B * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j +
      8 * B * S ^ (2:ℕ) * W ^ (7:ℕ) * j ^ (4:ℕ) + 8 * B * S ^ (2:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ) +
      8 * B * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ)) * h1 +
      (16 * G * B ^ (2:ℕ) * K ^ (5:ℕ) * S ^ (4:ℕ) -
      16 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (5:ℕ) * j ^ (2:ℕ) -
      64 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (5:ℕ) - 8 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (4:ℕ) * O * j
      + 32 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (6:ℕ) * j ^ (2:ℕ) +
      100 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (6:ℕ) +
      36 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (5:ℕ) * O * j -
      20 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (7:ℕ) * j ^ (2:ℕ) -
      68 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (7:ℕ) -
      40 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (6:ℕ) * O * j +
      4 * G * B ^ (2:ℕ) * K * S ^ (8:ℕ) * j ^ (2:ℕ) + 16 * G * B ^ (2:ℕ) * K * S ^ (8:ℕ) +
      12 * G * B ^ (2:ℕ) * K * S ^ (7:ℕ) * O * j - 32 * B * K ^ (6:ℕ) * S ^ (4:ℕ) * W +
      176 * B * K ^ (5:ℕ) * S ^ (5:ℕ) * W - 8 * B * K ^ (5:ℕ) * S ^ (4:ℕ) * W * O * j +
      8 * B * K ^ (5:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) - 16 * B * K ^ (4:ℕ) * N * S ^ (6:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (4:ℕ) * N * S ^ (6:ℕ) - 8 * B * K ^ (4:ℕ) * N * S ^ (5:ℕ) * O * j -
      16 * B * K ^ (4:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (4:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) -
      8 * B * K ^ (4:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j +
      16 * B * K ^ (4:ℕ) * S ^ (6:ℕ) * W * j ^ (2:ℕ) - 352 * B * K ^ (4:ℕ) * S ^ (6:ℕ) * W +
      56 * B * K ^ (4:ℕ) * S ^ (5:ℕ) * W * O * j +
      56 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      72 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
      24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j -
      8 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (5:ℕ) * W -
      8 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) +
      48 * B * K ^ (3:ℕ) * N * S ^ (7:ℕ) * j ^ (2:ℕ) + 92 * B * K ^ (3:ℕ) * N * S ^ (7:ℕ) +
      44 * B * K ^ (3:ℕ) * N * S ^ (6:ℕ) * O * j +
      64 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      120 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) +
      48 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j +
      16 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) +
      28 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) +
      4 * B * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j -
      56 * B * K ^ (3:ℕ) * S ^ (7:ℕ) * W * j ^ (2:ℕ) + 304 * B * K ^ (3:ℕ) * S ^ (7:ℕ) * W -
      144 * B * K ^ (3:ℕ) * S ^ (6:ℕ) * W * O * j -
      184 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      136 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) -
      144 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j -
      40 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      8 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) - 8 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j
      + 20 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (6:ℕ) * W +
      24 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
      4 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) -
      52 * B * K ^ (2:ℕ) * N * S ^ (8:ℕ) * j ^ (2:ℕ) - 128 * B * K ^ (2:ℕ) * N * S ^ (8:ℕ) -
      76 * B * K ^ (2:ℕ) * N * S ^ (7:ℕ) * O * j -
      108 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      232 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * W ^ (2:ℕ) -
      104 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j -
      60 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      112 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (4:ℕ) -
      28 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j -
      4 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) -
      8 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (6:ℕ) + 72 * B * K ^ (2:ℕ) * S ^ (8:ℕ) * W * j ^ (2:ℕ)
      - 80 * B * K ^ (2:ℕ) * S ^ (8:ℕ) * W + 176 * B * K ^ (2:ℕ) * S ^ (7:ℕ) * W * O * j +
      240 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) +
      288 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j +
      160 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) -
      8 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) + 64 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j
      + 8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ) -
      16 * B * K * N ^ (2:ℕ) * S ^ (7:ℕ) * W - 32 * B * K * N ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) -
      16 * B * K * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) + 24 * B * K * N * S ^ (9:ℕ) * j ^ (2:ℕ) +
      76 * B * K * N * S ^ (9:ℕ) + 52 * B * K * N * S ^ (8:ℕ) * O * j +
      72 * B * K * N * S ^ (7:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 196 * B * K * N * S ^ (7:ℕ) * W ^ (2:ℕ) +
      108 * B * K * N * S ^ (6:ℕ) * W ^ (2:ℕ) * O * j +
      72 * B * K * N * S ^ (5:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) + 164 * B * K * N * S ^ (5:ℕ) * W ^ (4:ℕ) +
      60 * B * K * N * S ^ (4:ℕ) * W ^ (4:ℕ) * O * j +
      24 * B * K * N * S ^ (3:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) + 44 * B * K * N * S ^ (3:ℕ) * W ^ (6:ℕ) +
      4 * B * K * N * S ^ (2:ℕ) * W ^ (6:ℕ) * O * j - 40 * B * K * S ^ (9:ℕ) * W * j ^ (2:ℕ) -
      32 * B * K * S ^ (9:ℕ) * W - 104 * B * K * S ^ (8:ℕ) * W * O * j -
      144 * B * K * S ^ (7:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) - 96 * B * K * S ^ (7:ℕ) * W ^ (3:ℕ) -
      240 * B * K * S ^ (6:ℕ) * W ^ (3:ℕ) * O * j - 160 * B * K * S ^ (5:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ)
      - 64 * B * K * S ^ (5:ℕ) * W ^ (5:ℕ) - 144 * B * K * S ^ (4:ℕ) * W ^ (5:ℕ) * O * j -
      56 * B * K * S ^ (3:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ) - 8 * B * K * S ^ (2:ℕ) * W ^ (7:ℕ) * O * j +
      4 * B * N ^ (2:ℕ) * S ^ (8:ℕ) * W + 12 * B * N ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) +
      12 * B * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) + 4 * B * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (7:ℕ) -
      4 * B * N * S ^ (10:ℕ) * j ^ (2:ℕ) - 16 * B * N * S ^ (10:ℕ) - 12 * B * N * S ^ (9:ℕ) * O * j
      - 16 * B * N * S ^ (8:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) - 56 * B * N * S ^ (8:ℕ) * W ^ (2:ℕ) -
      36 * B * N * S ^ (7:ℕ) * W ^ (2:ℕ) * O * j - 24 * B * N * S ^ (6:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      72 * B * N * S ^ (6:ℕ) * W ^ (4:ℕ) - 36 * B * N * S ^ (5:ℕ) * W ^ (4:ℕ) * O * j -
      16 * B * N * S ^ (4:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) - 40 * B * N * S ^ (4:ℕ) * W ^ (6:ℕ) -
      12 * B * N * S ^ (3:ℕ) * W ^ (6:ℕ) * O * j - 4 * B * N * S ^ (2:ℕ) * W ^ (8:ℕ) * j ^ (2:ℕ) -
      8 * B * N * S ^ (2:ℕ) * W ^ (8:ℕ) + 8 * B * S ^ (10:ℕ) * W * j ^ (2:ℕ) +
      16 * B * S ^ (10:ℕ) * W + 24 * B * S ^ (9:ℕ) * W * O * j +
      32 * B * S ^ (8:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) + 48 * B * S ^ (8:ℕ) * W ^ (3:ℕ) +
      72 * B * S ^ (7:ℕ) * W ^ (3:ℕ) * O * j + 48 * B * S ^ (6:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      48 * B * S ^ (6:ℕ) * W ^ (5:ℕ) + 72 * B * S ^ (5:ℕ) * W ^ (5:ℕ) * O * j +
      32 * B * S ^ (4:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ) + 16 * B * S ^ (4:ℕ) * W ^ (7:ℕ) +
      24 * B * S ^ (3:ℕ) * W ^ (7:ℕ) * O * j + 8 * B * S ^ (2:ℕ) * W ^ (9:ℕ) * j ^ (2:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem pc_Y3 {G B K N S W O j : ℂ}
    (hB : starRingEnd ℂ B = B) (hK : starRingEnd ℂ K = K) (hS : starRingEnd ℂ S = S)
    (hW : starRingEnd ℂ W = W) (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j)
    (hj : j ^ 2 = -1) (h1 : O ^ 2 = S ^ 2 + W ^ 2 - 2 * S * K)
    (h2 : G * B * W = 2 * S * (O ^ 2 + K ^ 2)) :
    pairing (pcLC B K S W O j) (pcBil G B N (pcQC B S W (-O) j) (pcSC G B K N S W O j)) =
      (-144 * G * B ^ (2:ℕ) * K ^ (5:ℕ) * S ^ (4:ℕ) + 464 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (5:ℕ) -
        512 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (6:ℕ) + 192 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (7:ℕ) +
        16 * G * B ^ (2:ℕ) * K * S ^ (8:ℕ) - 16 * G * B ^ (2:ℕ) * S ^ (9:ℕ) +
        336 * B * K ^ (6:ℕ) * S ^ (4:ℕ) * W + 128 * B * K ^ (5:ℕ) * N * S ^ (5:ℕ) -
        1952 * B * K ^ (5:ℕ) * S ^ (5:ℕ) * W - 96 * B * K ^ (5:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) +
        64 * B * K ^ (4:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W - 304 * B * K ^ (4:ℕ) * N * S ^ (6:ℕ) -
        176 * B * K ^ (4:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) + 4256 * B * K ^ (4:ℕ) * S ^ (6:ℕ) * W +
        1120 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) -
        88 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (5:ℕ) * W -
        24 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) + 80 * B * K ^ (3:ℕ) * N * S ^ (7:ℕ)
        + 384 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) +
        48 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) - 4416 * B * K ^ (3:ℕ) * S ^ (7:ℕ) * W -
        3104 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) - 192 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) -
        48 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (6:ℕ) * W +
        80 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) + 304 * B * K ^ (2:ℕ) * N * S ^ (8:ℕ)
        + 96 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * W ^ (2:ℕ) -
        208 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (4:ℕ) + 2192 * B * K ^ (2:ℕ) * S ^ (8:ℕ) * W +
        3136 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) + 848 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) +
        104 * B * K * N ^ (2:ℕ) * S ^ (7:ℕ) * W + 80 * B * K * N ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) -
        24 * B * K * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) - 272 * B * K * N * S ^ (9:ℕ) -
        496 * B * K * N * S ^ (7:ℕ) * W ^ (2:ℕ) - 176 * B * K * N * S ^ (5:ℕ) * W ^ (4:ℕ) +
        48 * B * K * N * S ^ (3:ℕ) * W ^ (6:ℕ) - 416 * B * K * S ^ (9:ℕ) * W -
        1152 * B * K * S ^ (7:ℕ) * W ^ (3:ℕ) - 768 * B * K * S ^ (5:ℕ) * W ^ (5:ℕ) -
        96 * B * K * S ^ (3:ℕ) * W ^ (7:ℕ) - 32 * B * N ^ (2:ℕ) * S ^ (8:ℕ) * W -
        64 * B * N ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) - 32 * B * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) +
        64 * B * N * S ^ (10:ℕ) + 192 * B * N * S ^ (8:ℕ) * W ^ (2:ℕ) +
        192 * B * N * S ^ (6:ℕ) * W ^ (4:ℕ) + 64 * B * N * S ^ (4:ℕ) * W ^ (6:ℕ) +
        96 * B * S ^ (8:ℕ) * W ^ (3:ℕ) + 160 * B * S ^ (6:ℕ) * W ^ (5:ℕ) +
        64 * B * S ^ (4:ℕ) * W ^ (7:ℕ)) + (-144 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (4:ℕ) * O +
        480 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (5:ℕ) * O -
        576 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (6:ℕ) * O + 288 * G * B ^ (2:ℕ) * K * S ^ (7:ℕ) * O -
        48 * G * B ^ (2:ℕ) * S ^ (8:ℕ) * O + 144 * B * K ^ (5:ℕ) * S ^ (4:ℕ) * W * O +
        192 * B * K ^ (4:ℕ) * N * S ^ (5:ℕ) * O - 960 * B * K ^ (4:ℕ) * S ^ (5:ℕ) * W * O +
        96 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W * O - 624 * B * K ^ (3:ℕ) * N * S ^ (6:ℕ) * O
        - 240 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O +
        2208 * B * K ^ (3:ℕ) * S ^ (6:ℕ) * W * O + 288 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O -
        216 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (5:ℕ) * W * O -
        24 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O +
        720 * B * K ^ (2:ℕ) * N * S ^ (7:ℕ) * O +
        768 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O +
        48 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O -
        2304 * B * K ^ (2:ℕ) * S ^ (7:ℕ) * W * O - 1056 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O
        + 144 * B * K * N ^ (2:ℕ) * S ^ (6:ℕ) * W * O +
        144 * B * K * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O - 336 * B * K * N * S ^ (8:ℕ) * O -
        672 * B * K * N * S ^ (6:ℕ) * W ^ (2:ℕ) * O - 336 * B * K * N * S ^ (4:ℕ) * W ^ (4:ℕ) * O +
        1104 * B * K * S ^ (8:ℕ) * W * O + 1056 * B * K * S ^ (6:ℕ) * W ^ (3:ℕ) * O +
        144 * B * K * S ^ (4:ℕ) * W ^ (5:ℕ) * O - 24 * B * N ^ (2:ℕ) * S ^ (7:ℕ) * W * O -
        48 * B * N ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O -
        24 * B * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * O + 48 * B * N * S ^ (9:ℕ) * O +
        144 * B * N * S ^ (7:ℕ) * W ^ (2:ℕ) * O + 144 * B * N * S ^ (5:ℕ) * W ^ (4:ℕ) * O +
        48 * B * N * S ^ (3:ℕ) * W ^ (6:ℕ) * O - 192 * B * S ^ (9:ℕ) * W * O -
        288 * B * S ^ (7:ℕ) * W ^ (3:ℕ) * O - 96 * B * S ^ (5:ℕ) * W ^ (5:ℕ) * O) * j := by
  simp only [pairing_apply, pcLC, pcBil, pcQC, pcSC, Fin.sum_univ_three, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.vecHead, Matrix.cons_val_fin_one, map_mul, map_sub, map_neg, hB, hK, hS, hW, hO, hjc]
  linear_combination (104 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (4:ℕ) -
      92 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (3:ℕ) * O * j +
      12 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (2:ℕ) -
      12 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      32 * G * B ^ (2:ℕ) * K * S ^ (5:ℕ) + 84 * G * B ^ (2:ℕ) * K * S ^ (4:ℕ) * O * j +
      12 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) * W ^ (2:ℕ) -
      72 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      20 * G * B ^ (2:ℕ) * K * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j +
      20 * G * B ^ (2:ℕ) * K * S ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) - 8 * G * B ^ (2:ℕ) * S ^ (6:ℕ) -
      8 * G * B ^ (2:ℕ) * S ^ (5:ℕ) * O * j - 8 * G * B ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (2:ℕ) +
      20 * G * B ^ (2:ℕ) * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      4 * G * B ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j -
      4 * G * B ^ (2:ℕ) * S ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
      48 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W * j ^ (4:ℕ) -
      24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) + 24 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W -
      32 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) + 32 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * O * j -
      72 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * j ^ (4:ℕ) +
      20 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) - 216 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W -
      48 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j ^ (5:ℕ) -
      28 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) +
      60 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O * j - 12 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) -
      24 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      12 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) -
      244 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) + 260 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * O * j -
      116 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) +
      16 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      44 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j -
      32 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
      160 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (4:ℕ) +
      236 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) + 524 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W -
      64 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j ^ (5:ℕ) -
      116 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) -
      388 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j + 16 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) +
      24 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      64 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) +
      24 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) -
      40 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j +
      24 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) +
      8 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) + 140 * B * K * N * S ^ (6:ℕ) -
      268 * B * K * N * S ^ (5:ℕ) * O * j + 156 * B * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) +
      196 * B * K * N * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      164 * B * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j -
      68 * B * K * N * S ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) + 16 * B * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) -
      8 * B * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      108 * B * K * S ^ (6:ℕ) * W * j ^ (4:ℕ) - 156 * B * K * S ^ (6:ℕ) * W * j ^ (2:ℕ) -
      220 * B * K * S ^ (6:ℕ) * W + 84 * B * K * S ^ (5:ℕ) * W * O * j ^ (5:ℕ) +
      36 * B * K * S ^ (5:ℕ) * W * O * j ^ (3:ℕ) + 344 * B * K * S ^ (5:ℕ) * W * O * j -
      160 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) - 68 * B * K * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      184 * B * K * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 24 * B * K * S ^ (4:ℕ) * W * O ^ (2:ℕ) +
      184 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j +
      44 * B * K * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) +
      100 * B * K * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) +
      40 * B * K * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j - 4 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) +
      20 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) - 8 * B * N * S ^ (7:ℕ) +
      48 * B * N * S ^ (6:ℕ) * O * j - 16 * B * N * S ^ (5:ℕ) * W ^ (2:ℕ) -
      68 * B * N * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + 68 * B * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j +
      28 * B * N * S ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) - 8 * B * N * S ^ (3:ℕ) * W ^ (4:ℕ) -
      28 * B * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      20 * B * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j +
      8 * B * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) + 20 * B * S ^ (7:ℕ) * W * j ^ (4:ℕ)
      + 20 * B * S ^ (7:ℕ) * W * j ^ (2:ℕ) - 8 * B * S ^ (7:ℕ) * W -
      20 * B * S ^ (6:ℕ) * W * O * j ^ (5:ℕ) + 12 * B * S ^ (6:ℕ) * W * O * j ^ (3:ℕ) -
      56 * B * S ^ (6:ℕ) * W * O * j + 16 * B * S ^ (5:ℕ) * W ^ (3:ℕ) +
      20 * B * S ^ (5:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      60 * B * S ^ (5:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) - 16 * B * S ^ (5:ℕ) * W * O ^ (2:ℕ) -
      72 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j - 20 * B * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) -
      36 * B * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) - 8 * B * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j +
      8 * B * S ^ (3:ℕ) * W ^ (5:ℕ) + 40 * B * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      32 * B * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j -
      8 * B * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ)) * h2 +
      (48 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (3:ℕ) * j ^ (4:ℕ) -
      24 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (3:ℕ) * j ^ (2:ℕ) -
      72 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (4:ℕ) * j ^ (4:ℕ) +
      20 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (4:ℕ) * j ^ (2:ℕ) -
      48 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (3:ℕ) * O * j ^ (5:ℕ) -
      28 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (3:ℕ) * O * j ^ (3:ℕ) -
      24 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      160 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (5:ℕ) * j ^ (4:ℕ) +
      236 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (5:ℕ) * j ^ (2:ℕ) +
      208 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (5:ℕ) -
      64 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (4:ℕ) * O * j ^ (5:ℕ) -
      116 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (4:ℕ) * O * j ^ (3:ℕ) -
      184 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (4:ℕ) * O * j +
      24 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      24 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      24 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      108 * G * B ^ (2:ℕ) * K * S ^ (6:ℕ) * j ^ (4:ℕ) -
      156 * G * B ^ (2:ℕ) * K * S ^ (6:ℕ) * j ^ (2:ℕ) - 64 * G * B ^ (2:ℕ) * K * S ^ (6:ℕ) +
      84 * G * B ^ (2:ℕ) * K * S ^ (5:ℕ) * O * j ^ (5:ℕ) +
      36 * G * B ^ (2:ℕ) * K * S ^ (5:ℕ) * O * j ^ (3:ℕ) +
      168 * G * B ^ (2:ℕ) * K * S ^ (5:ℕ) * O * j -
      68 * G * B ^ (2:ℕ) * K * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      144 * G * B ^ (2:ℕ) * K * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      44 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) +
      40 * G * B ^ (2:ℕ) * K * S ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
      20 * G * B ^ (2:ℕ) * S ^ (7:ℕ) * j ^ (4:ℕ) + 20 * G * B ^ (2:ℕ) * S ^ (7:ℕ) * j ^ (2:ℕ) -
      16 * G * B ^ (2:ℕ) * S ^ (7:ℕ) - 20 * G * B ^ (2:ℕ) * S ^ (6:ℕ) * O * j ^ (5:ℕ) +
      12 * G * B ^ (2:ℕ) * S ^ (6:ℕ) * O * j ^ (3:ℕ) - 16 * G * B ^ (2:ℕ) * S ^ (6:ℕ) * O * j +
      20 * G * B ^ (2:ℕ) * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      40 * G * B ^ (2:ℕ) * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      20 * G * B ^ (2:ℕ) * S ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      8 * G * B ^ (2:ℕ) * S ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
      96 * B * K ^ (5:ℕ) * S ^ (3:ℕ) * W * j ^ (4:ℕ) -
      24 * B * K ^ (5:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) -
      96 * B * K ^ (4:ℕ) * N * S ^ (4:ℕ) * j ^ (4:ℕ) -
      32 * B * K ^ (4:ℕ) * N * S ^ (3:ℕ) * O * j ^ (3:ℕ) +
      504 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W * j ^ (4:ℕ) -
      32 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) + 96 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W +
      96 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W * O * j ^ (5:ℕ) +
      128 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) +
      24 * B * K ^ (4:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) +
      24 * B * K ^ (4:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      24 * B * K ^ (4:ℕ) * S ^ (2:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      32 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W * j ^ (2:ℕ) +
      104 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * j ^ (4:ℕ) +
      164 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * j ^ (2:ℕ) - 64 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) +
      160 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * O * j ^ (5:ℕ) +
      60 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * O * j ^ (3:ℕ) +
      64 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * O * j +
      72 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) +
      132 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      48 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      12 * B * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      1008 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W * j ^ (4:ℕ) -
      192 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) - 480 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W -
      144 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * O * j ^ (5:ℕ) -
      16 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) +
      200 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W * O * j -
      264 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) -
      128 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) -
      168 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      24 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) -
      48 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) -
      24 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) -
      44 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) +
      80 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W * O * j ^ (3:ℕ) -
      12 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      188 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * j ^ (4:ℕ) -
      772 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * j ^ (2:ℕ) - 488 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) -
      64 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * O * j ^ (5:ℕ) +
      364 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * O * j ^ (3:ℕ) +
      520 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * O * j -
      136 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) -
      360 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      232 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) -
      28 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      32 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      128 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j ^ (5:ℕ) -
      212 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      88 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j -
      80 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      64 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
      12 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (4:ℕ) -
      36 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      12 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      1312 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W * j ^ (4:ℕ) +
      1040 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W * j ^ (2:ℕ) + 968 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W -
      400 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * O * j ^ (5:ℕ) -
      752 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * O * j ^ (3:ℕ) -
      952 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W * O * j +
      568 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) +
      144 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      80 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
      280 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      128 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) +
      48 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W * O ^ (2:ℕ) +
      104 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) +
      144 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) -
      80 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j +
      56 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) +
      16 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) +
      48 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) +
      48 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      48 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      104 * B * K * N ^ (2:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ) +
      8 * B * K * N ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) -
      40 * B * K * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      24 * B * K * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      136 * B * K * N * S ^ (7:ℕ) * j ^ (4:ℕ) + 572 * B * K * N * S ^ (7:ℕ) * j ^ (2:ℕ) +
      280 * B * K * N * S ^ (7:ℕ) - 40 * B * K * N * S ^ (6:ℕ) * O * j ^ (5:ℕ) -
      300 * B * K * N * S ^ (6:ℕ) * O * j ^ (3:ℕ) - 536 * B * K * N * S ^ (6:ℕ) * O * j +
      208 * B * K * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) +
      776 * B * K * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 312 * B * K * N * S ^ (5:ℕ) * W ^ (2:ℕ)
      + 80 * B * K * N * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      392 * B * K * N * S ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      16 * B * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j ^ (5:ℕ) -
      304 * B * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      328 * B * K * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j -
      8 * B * K * N * S ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      136 * B * K * N * S ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
      72 * B * K * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (4:ℕ) +
      204 * B * K * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) + 32 * B * K * N * S ^ (3:ℕ) * W ^ (4:ℕ) +
      48 * B * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      16 * B * K * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      24 * B * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j ^ (5:ℕ) +
      60 * B * K * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) +
      24 * B * K * N * S ^ (2:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      760 * B * K * S ^ (7:ℕ) * W * j ^ (4:ℕ) - 696 * B * K * S ^ (7:ℕ) * W * j ^ (2:ℕ) -
      328 * B * K * S ^ (7:ℕ) * W + 472 * B * K * S ^ (6:ℕ) * W * O * j ^ (5:ℕ) +
      480 * B * K * S ^ (6:ℕ) * W * O * j ^ (3:ℕ) + 800 * B * K * S ^ (6:ℕ) * W * O * j -
      632 * B * K * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) -
      408 * B * K * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) - 272 * B * K * S ^ (5:ℕ) * W ^ (3:ℕ) -
      336 * B * K * S ^ (5:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) -
      368 * B * K * S ^ (5:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) + 48 * B * K * S ^ (5:ℕ) * W * O ^ (2:ℕ) +
      200 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) +
      408 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      448 * B * K * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j +
      144 * B * K * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) +
      200 * B * K * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) +
      80 * B * K * S ^ (4:ℕ) * W * O ^ (3:ℕ) * j - 168 * B * K * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) -
      104 * B * K * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) - 8 * B * K * S ^ (3:ℕ) * W ^ (5:ℕ) -
      120 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      40 * B * K * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      24 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j ^ (5:ℕ) -
      48 * B * K * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) -
      24 * B * K * S ^ (2:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) +
      44 * B * N ^ (2:ℕ) * S ^ (6:ℕ) * W * j ^ (2:ℕ) -
      16 * B * N ^ (2:ℕ) * S ^ (5:ℕ) * W * O * j ^ (3:ℕ) +
      56 * B * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      16 * B * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      12 * B * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) - 28 * B * N * S ^ (8:ℕ) * j ^ (4:ℕ) -
      108 * B * N * S ^ (8:ℕ) * j ^ (2:ℕ) - 16 * B * N * S ^ (8:ℕ) +
      16 * B * N * S ^ (7:ℕ) * O * j ^ (5:ℕ) + 52 * B * N * S ^ (7:ℕ) * O * j ^ (3:ℕ) +
      96 * B * N * S ^ (7:ℕ) * O * j - 68 * B * N * S ^ (6:ℕ) * W ^ (2:ℕ) * j ^ (4:ℕ) -
      252 * B * N * S ^ (6:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) - 32 * B * N * S ^ (6:ℕ) * W ^ (2:ℕ) -
      28 * B * N * S ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      136 * B * N * S ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      32 * B * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j ^ (5:ℕ) +
      136 * B * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) +
      136 * B * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j + 16 * B * N * S ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) +
      56 * B * N * S ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
      52 * B * N * S ^ (4:ℕ) * W ^ (4:ℕ) * j ^ (4:ℕ) -
      180 * B * N * S ^ (4:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) - 16 * B * N * S ^ (4:ℕ) * W ^ (4:ℕ) -
      40 * B * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) -
      56 * B * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
      16 * B * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j ^ (5:ℕ) +
      84 * B * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) +
      40 * B * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j +
      16 * B * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) +
      16 * B * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
      12 * B * N * S ^ (2:ℕ) * W ^ (6:ℕ) * j ^ (4:ℕ) -
      36 * B * N * S ^ (2:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) -
      12 * B * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      144 * B * S ^ (8:ℕ) * W * j ^ (4:ℕ) + 96 * B * S ^ (8:ℕ) * W * j ^ (2:ℕ) -
      48 * B * S ^ (8:ℕ) * W - 120 * B * S ^ (7:ℕ) * W * O * j ^ (5:ℕ) -
      32 * B * S ^ (7:ℕ) * W * O * j ^ (3:ℕ) - 128 * B * S ^ (7:ℕ) * W * O * j +
      192 * B * S ^ (6:ℕ) * W ^ (3:ℕ) * j ^ (4:ℕ) + 96 * B * S ^ (6:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      104 * B * S ^ (6:ℕ) * W * O ^ (2:ℕ) * j ^ (4:ℕ) +
      120 * B * S ^ (6:ℕ) * W * O ^ (2:ℕ) * j ^ (2:ℕ) - 32 * B * S ^ (6:ℕ) * W * O ^ (2:ℕ) -
      120 * B * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j ^ (5:ℕ) -
      136 * B * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) - 160 * B * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j -
      80 * B * S ^ (5:ℕ) * W * O ^ (3:ℕ) * j ^ (5:ℕ) -
      72 * B * S ^ (5:ℕ) * W * O ^ (3:ℕ) * j ^ (3:ℕ) - 16 * B * S ^ (5:ℕ) * W * O ^ (3:ℕ) * j +
      112 * B * S ^ (4:ℕ) * W ^ (5:ℕ) * j ^ (4:ℕ) + 64 * B * S ^ (4:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      16 * B * S ^ (4:ℕ) * W ^ (5:ℕ) + 88 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ) +
      80 * B * S ^ (4:ℕ) * W ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
      40 * B * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j ^ (5:ℕ) -
      80 * B * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) - 64 * B * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j -
      40 * B * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (5:ℕ) -
      16 * B * S ^ (3:ℕ) * W ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
      24 * B * S ^ (2:ℕ) * W ^ (7:ℕ) * j ^ (4:ℕ) + 24 * B * S ^ (2:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ) +
      24 * B * S ^ (2:ℕ) * W ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (4:ℕ)) * h1 +
      (-96 * G * B ^ (2:ℕ) * K ^ (5:ℕ) * S ^ (4:ℕ) * j ^ (2:ℕ) +
      144 * G * B ^ (2:ℕ) * K ^ (5:ℕ) * S ^ (4:ℕ) +
      192 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (5:ℕ) * j ^ (2:ℕ) -
      256 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (5:ℕ) +
      96 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (4:ℕ) * O * j ^ (3:ℕ) -
      40 * G * B ^ (2:ℕ) * K ^ (4:ℕ) * S ^ (4:ℕ) * O * j -
      392 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (6:ℕ) * j ^ (2:ℕ) -
      60 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (6:ℕ) +
      80 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (5:ℕ) * O * j ^ (3:ℕ) +
      124 * G * B ^ (2:ℕ) * K ^ (3:ℕ) * S ^ (5:ℕ) * O * j +
      376 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (7:ℕ) * j ^ (2:ℕ) +
      172 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (7:ℕ) -
      232 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (6:ℕ) * O * j ^ (3:ℕ) +
      44 * G * B ^ (2:ℕ) * K ^ (2:ℕ) * S ^ (6:ℕ) * O * j -
      148 * G * B ^ (2:ℕ) * K * S ^ (8:ℕ) * j ^ (2:ℕ) - 48 * G * B ^ (2:ℕ) * K * S ^ (8:ℕ) +
      124 * G * B ^ (2:ℕ) * K * S ^ (7:ℕ) * O * j ^ (3:ℕ) -
      112 * G * B ^ (2:ℕ) * K * S ^ (7:ℕ) * O * j + 20 * G * B ^ (2:ℕ) * S ^ (9:ℕ) * j ^ (2:ℕ) -
      20 * G * B ^ (2:ℕ) * S ^ (8:ℕ) * O * j ^ (3:ℕ) + 32 * G * B ^ (2:ℕ) * S ^ (8:ℕ) * O * j +
      288 * B * K ^ (6:ℕ) * S ^ (4:ℕ) * W * j ^ (2:ℕ) - 288 * B * K ^ (6:ℕ) * S ^ (4:ℕ) * W +
      192 * B * K ^ (5:ℕ) * N * S ^ (5:ℕ) * j ^ (2:ℕ) - 192 * B * K ^ (5:ℕ) * N * S ^ (5:ℕ) +
      64 * B * K ^ (5:ℕ) * N * S ^ (4:ℕ) * O * j - 1248 * B * K ^ (5:ℕ) * S ^ (5:ℕ) * W * j ^ (2:ℕ)
      + 1328 * B * K ^ (5:ℕ) * S ^ (5:ℕ) * W - 288 * B * K ^ (5:ℕ) * S ^ (4:ℕ) * W * O * j ^ (3:ℕ) -
      24 * B * K ^ (5:ℕ) * S ^ (4:ℕ) * W * O * j -
      144 * B * K ^ (5:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      72 * B * K ^ (5:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) - 64 * B * K ^ (4:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W -
      304 * B * K ^ (4:ℕ) * N * S ^ (6:ℕ) * j ^ (2:ℕ) - 24 * B * K ^ (4:ℕ) * N * S ^ (6:ℕ) -
      320 * B * K ^ (4:ℕ) * N * S ^ (5:ℕ) * O * j ^ (3:ℕ) +
      168 * B * K ^ (4:ℕ) * N * S ^ (5:ℕ) * O * j -
      240 * B * K ^ (4:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (4:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) -
      56 * B * K ^ (4:ℕ) * N * S ^ (3:ℕ) * W ^ (2:ℕ) * O * j +
      2840 * B * K ^ (4:ℕ) * S ^ (6:ℕ) * W * j ^ (2:ℕ) - 2016 * B * K ^ (4:ℕ) * S ^ (6:ℕ) * W +
      256 * B * K ^ (4:ℕ) * S ^ (5:ℕ) * W * O * j ^ (3:ℕ) -
      328 * B * K ^ (4:ℕ) * S ^ (5:ℕ) * W * O * j +
      1056 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      808 * B * K ^ (4:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
      144 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      80 * B * K ^ (4:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j +
      24 * B * K ^ (4:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      120 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (5:ℕ) * W -
      160 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W * O * j +
      56 * B * K ^ (3:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) +
      480 * B * K ^ (3:ℕ) * N * S ^ (7:ℕ) * j ^ (2:ℕ) + 1228 * B * K ^ (3:ℕ) * N * S ^ (7:ℕ) +
      288 * B * K ^ (3:ℕ) * N * S ^ (6:ℕ) * O * j ^ (3:ℕ) -
      956 * B * K ^ (3:ℕ) * N * S ^ (6:ℕ) * O * j +
      448 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) +
      568 * B * K ^ (3:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) +
      416 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) +
      80 * B * K ^ (3:ℕ) * N * S ^ (4:ℕ) * W ^ (2:ℕ) * O * j +
      96 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) +
      108 * B * K ^ (3:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) +
      12 * B * K ^ (3:ℕ) * N * S ^ (2:ℕ) * W ^ (4:ℕ) * O * j -
      3848 * B * K ^ (3:ℕ) * S ^ (7:ℕ) * W * j ^ (2:ℕ) + 1264 * B * K ^ (3:ℕ) * S ^ (7:ℕ) * W +
      824 * B * K ^ (3:ℕ) * S ^ (6:ℕ) * W * O * j ^ (3:ℕ) +
      736 * B * K ^ (3:ℕ) * S ^ (6:ℕ) * W * O * j -
      2408 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      1800 * B * K ^ (3:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) -
      376 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      24 * B * K ^ (3:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j -
      360 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) +
      136 * B * K ^ (3:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) -
      24 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) -
      24 * B * K ^ (3:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j +
      164 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (6:ℕ) * W +
      64 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (5:ℕ) * W * O * j +
      24 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) +
      128 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (3:ℕ) * O * j -
      12 * B * K ^ (2:ℕ) * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) -
      460 * B * K ^ (2:ℕ) * N * S ^ (8:ℕ) * j ^ (2:ℕ) - 1456 * B * K ^ (2:ℕ) * N * S ^ (8:ℕ) +
      16 * B * K ^ (2:ℕ) * N * S ^ (7:ℕ) * O * j ^ (3:ℕ) +
      948 * B * K ^ (2:ℕ) * N * S ^ (7:ℕ) * O * j -
      740 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      1944 * B * K ^ (2:ℕ) * N * S ^ (6:ℕ) * W ^ (2:ℕ) -
      160 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) +
      920 * B * K ^ (2:ℕ) * N * S ^ (5:ℕ) * W ^ (2:ℕ) * O * j -
      292 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) -
      512 * B * K ^ (2:ℕ) * N * S ^ (4:ℕ) * W ^ (4:ℕ) -
      176 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) -
      156 * B * K ^ (2:ℕ) * N * S ^ (3:ℕ) * W ^ (4:ℕ) * O * j -
      12 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) -
      24 * B * K ^ (2:ℕ) * N * S ^ (2:ℕ) * W ^ (6:ℕ) +
      2872 * B * K ^ (2:ℕ) * S ^ (8:ℕ) * W * j ^ (2:ℕ) - 400 * B * K ^ (2:ℕ) * S ^ (8:ℕ) * W -
      1384 * B * K ^ (2:ℕ) * S ^ (7:ℕ) * W * O * j ^ (3:ℕ) -
      304 * B * K ^ (2:ℕ) * S ^ (7:ℕ) * W * O * j +
      3144 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      1144 * B * K ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) -
      696 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) -
      728 * B * K ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j +
      952 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) -
      552 * B * K ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) +
      152 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) +
      88 * B * K ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j +
      48 * B * K ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ) -
      192 * B * K * N ^ (2:ℕ) * S ^ (7:ℕ) * W + 40 * B * K * N ^ (2:ℕ) * S ^ (6:ℕ) * W * O * j -
      256 * B * K * N ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) +
      16 * B * K * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (3:ℕ) * O * j -
      64 * B * K * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) -
      24 * B * K * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (5:ℕ) * O * j +
      192 * B * K * N * S ^ (9:ℕ) * j ^ (2:ℕ) + 596 * B * K * N * S ^ (9:ℕ) -
      72 * B * K * N * S ^ (8:ℕ) * O * j ^ (3:ℕ) - 332 * B * K * N * S ^ (8:ℕ) * O * j +
      480 * B * K * N * S ^ (7:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) + 1372 * B * K * N * S ^ (7:ℕ) * W ^ (2:ℕ)
      - 120 * B * K * N * S ^ (6:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) -
      756 * B * K * N * S ^ (6:ℕ) * W ^ (2:ℕ) * O * j +
      384 * B * K * N * S ^ (5:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ) + 956 * B * K * N * S ^ (5:ℕ) * W ^ (4:ℕ)
      - 24 * B * K * N * S ^ (4:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) -
      388 * B * K * N * S ^ (4:ℕ) * W ^ (4:ℕ) * O * j +
      96 * B * K * N * S ^ (3:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) + 180 * B * K * N * S ^ (3:ℕ) * W ^ (6:ℕ) +
      24 * B * K * N * S ^ (2:ℕ) * W ^ (6:ℕ) * O * j ^ (3:ℕ) +
      36 * B * K * N * S ^ (2:ℕ) * W ^ (6:ℕ) * O * j - 1048 * B * K * S ^ (9:ℕ) * W * j ^ (2:ℕ) +
      160 * B * K * S ^ (9:ℕ) * W + 712 * B * K * S ^ (8:ℕ) * W * O * j ^ (3:ℕ) -
      168 * B * K * S ^ (8:ℕ) * W * O * j - 1776 * B * K * S ^ (7:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) +
      480 * B * K * S ^ (7:ℕ) * W ^ (3:ℕ) + 912 * B * K * S ^ (6:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      248 * B * K * S ^ (6:ℕ) * W ^ (3:ℕ) * O * j - 1024 * B * K * S ^ (5:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ)
      + 384 * B * K * S ^ (5:ℕ) * W ^ (5:ℕ) + 256 * B * K * S ^ (4:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) +
      264 * B * K * S ^ (4:ℕ) * W ^ (5:ℕ) * O * j - 216 * B * K * S ^ (3:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ)
      + 64 * B * K * S ^ (3:ℕ) * W ^ (7:ℕ) - 24 * B * K * S ^ (2:ℕ) * W ^ (7:ℕ) * O * j ^ (3:ℕ) -
      24 * B * K * S ^ (2:ℕ) * W ^ (7:ℕ) * O * j + 44 * B * N ^ (2:ℕ) * S ^ (8:ℕ) * W -
      16 * B * N ^ (2:ℕ) * S ^ (7:ℕ) * W * O * j + 100 * B * N ^ (2:ℕ) * S ^ (6:ℕ) * W ^ (3:ℕ) -
      32 * B * N ^ (2:ℕ) * S ^ (5:ℕ) * W ^ (3:ℕ) * O * j +
      68 * B * N ^ (2:ℕ) * S ^ (4:ℕ) * W ^ (5:ℕ) -
      16 * B * N ^ (2:ℕ) * S ^ (3:ℕ) * W ^ (5:ℕ) * O * j +
      12 * B * N ^ (2:ℕ) * S ^ (2:ℕ) * W ^ (7:ℕ) - 28 * B * N * S ^ (10:ℕ) * j ^ (2:ℕ) -
      80 * B * N * S ^ (10:ℕ) + 16 * B * N * S ^ (9:ℕ) * O * j ^ (3:ℕ) +
      36 * B * N * S ^ (9:ℕ) * O * j - 96 * B * N * S ^ (8:ℕ) * W ^ (2:ℕ) * j ^ (2:ℕ) -
      264 * B * N * S ^ (8:ℕ) * W ^ (2:ℕ) + 48 * B * N * S ^ (7:ℕ) * W ^ (2:ℕ) * O * j ^ (3:ℕ) +
      140 * B * N * S ^ (7:ℕ) * W ^ (2:ℕ) * O * j - 120 * B * N * S ^ (6:ℕ) * W ^ (4:ℕ) * j ^ (2:ℕ)
      - 312 * B * N * S ^ (6:ℕ) * W ^ (4:ℕ) + 48 * B * N * S ^ (5:ℕ) * W ^ (4:ℕ) * O * j ^ (3:ℕ) +
      172 * B * N * S ^ (5:ℕ) * W ^ (4:ℕ) * O * j - 64 * B * N * S ^ (4:ℕ) * W ^ (6:ℕ) * j ^ (2:ℕ) -
      152 * B * N * S ^ (4:ℕ) * W ^ (6:ℕ) + 16 * B * N * S ^ (3:ℕ) * W ^ (6:ℕ) * O * j ^ (3:ℕ) +
      68 * B * N * S ^ (3:ℕ) * W ^ (6:ℕ) * O * j - 12 * B * N * S ^ (2:ℕ) * W ^ (8:ℕ) * j ^ (2:ℕ) -
      24 * B * N * S ^ (2:ℕ) * W ^ (8:ℕ) + 144 * B * S ^ (10:ℕ) * W * j ^ (2:ℕ) -
      48 * B * S ^ (10:ℕ) * W - 120 * B * S ^ (9:ℕ) * W * O * j ^ (3:ℕ) +
      88 * B * S ^ (9:ℕ) * W * O * j + 336 * B * S ^ (8:ℕ) * W ^ (3:ℕ) * j ^ (2:ℕ) -
      144 * B * S ^ (8:ℕ) * W ^ (3:ℕ) - 240 * B * S ^ (7:ℕ) * W ^ (3:ℕ) * O * j ^ (3:ℕ) +
      72 * B * S ^ (7:ℕ) * W ^ (3:ℕ) * O * j + 304 * B * S ^ (6:ℕ) * W ^ (5:ℕ) * j ^ (2:ℕ) -
      144 * B * S ^ (6:ℕ) * W ^ (5:ℕ) - 160 * B * S ^ (5:ℕ) * W ^ (5:ℕ) * O * j ^ (3:ℕ) -
      56 * B * S ^ (5:ℕ) * W ^ (5:ℕ) * O * j + 136 * B * S ^ (4:ℕ) * W ^ (7:ℕ) * j ^ (2:ℕ) -
      48 * B * S ^ (4:ℕ) * W ^ (7:ℕ) - 40 * B * S ^ (3:ℕ) * W ^ (7:ℕ) * O * j ^ (3:ℕ) -
      40 * B * S ^ (3:ℕ) * W ^ (7:ℕ) * O * j + 24 * B * S ^ (2:ℕ) * W ^ (9:ℕ) * j ^ (2:ℕ)) * hj

/-- The combination `Z` of the projection formula. -/
private def pcZ (cr ci dr di y1r y1i y2r y2i y3r y3i e : ℝ) : ℝ :=
  (e * (dr * y1r - di * y1i) - 2 * (dr * y2r - di * y2i) + e * y3r) * (cr * dr - ci * di) +
    (e * (dr * y1i + di * y1r) - 2 * (dr * y2i + di * y2r) + e * y3i) * (cr * di + ci * dr)

/-- The key identity of the closed form (polynomial certificate modulo the boundary
relations). -/
@[tmio M, powerlib_domain] private theorem pc_key {g b κ ν σ w ω : ℝ}
    (h1 : ω ^ 2 = σ ^ 2 + w ^ 2 - 2 * σ * κ) (h2 : g * b * w = 2 * σ * (ω ^ 2 + κ ^ 2)) :
    pcZ (-2 * b * w * ω ^ (2:ℕ)) (-2 * b * κ * w * ω + 4 * b * σ * w * ω) (3 * κ * ω ^ (2:ℕ) -
      6 * σ * ω ^ (2:ℕ)) (-6 * ω ^ (3:ℕ)) (24 * b * κ ^ (4:ℕ) * σ ^ (3:ℕ) * w -
      80 * b * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w + 104 * b * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w +
      40 * b * κ ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) - 64 * b * κ * σ ^ (6:ℕ) * w -
      64 * b * κ * σ ^ (4:ℕ) * w ^ (3:ℕ) + 16 * b * σ ^ (7:ℕ) * w + 32 * b * σ ^ (5:ℕ) * w ^ (3:ℕ) +
      16 * b * σ ^ (3:ℕ) * w ^ (5:ℕ)) (8 * b * κ ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω -
      16 * b * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w * ω + 8 * b * κ * σ ^ (5:ℕ) * w * ω +
      8 * b * κ * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω) (-16 * g * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (4:ℕ) +
      48 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (5:ℕ) - 48 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (6:ℕ) +
      16 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (7:ℕ) + 16 * b * κ ^ (6:ℕ) * σ ^ (4:ℕ) * w -
      96 * b * κ ^ (5:ℕ) * σ ^ (5:ℕ) * w + 16 * b * κ ^ (4:ℕ) * ν * σ ^ (6:ℕ) +
      16 * b * κ ^ (4:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) + 192 * b * κ ^ (4:ℕ) * σ ^ (6:ℕ) * w +
      32 * b * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) + 8 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w +
      8 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) - 48 * b * κ ^ (3:ℕ) * ν * σ ^ (7:ℕ) -
      64 * b * κ ^ (3:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) -
      16 * b * κ ^ (3:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) - 160 * b * κ ^ (3:ℕ) * σ ^ (7:ℕ) * w -
      96 * b * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) - 16 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w -
      16 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) + 48 * b * κ ^ (2:ℕ) * ν * σ ^ (8:ℕ) +
      96 * b * κ ^ (2:ℕ) * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) +
      48 * b * κ ^ (2:ℕ) * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) + 48 * b * κ ^ (2:ℕ) * σ ^ (8:ℕ) * w +
      64 * b * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) + 16 * b * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) +
      8 * b * κ * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w + 16 * b * κ * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) +
      8 * b * κ * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) - 16 * b * κ * ν * σ ^ (9:ℕ) -
      48 * b * κ * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) - 48 * b * κ * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) -
      16 * b * κ * ν * σ ^ (3:ℕ) * w ^ (6:ℕ)) (-16 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * ω +
      48 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * ω -
      48 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * ω + 16 * g * b ^ (2:ℕ) * κ * σ ^ (7:ℕ) * ω +
      16 * b * κ ^ (5:ℕ) * σ ^ (4:ℕ) * w * ω - 96 * b * κ ^ (4:ℕ) * σ ^ (5:ℕ) * w * ω +
      16 * b * κ ^ (3:ℕ) * ν * σ ^ (6:ℕ) * ω + 16 * b * κ ^ (3:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω +
      192 * b * κ ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω + 32 * b * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω +
      8 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w * ω +
      8 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω -
      48 * b * κ ^ (2:ℕ) * ν * σ ^ (7:ℕ) * ω - 64 * b * κ ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω -
      16 * b * κ ^ (2:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω - 160 * b * κ ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω -
      96 * b * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω - 16 * b * κ * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w * ω -
      16 * b * κ * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω + 48 * b * κ * ν * σ ^ (8:ℕ) * ω +
      96 * b * κ * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω + 48 * b * κ * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω +
      48 * b * κ * σ ^ (8:ℕ) * w * ω + 64 * b * κ * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω +
      16 * b * κ * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω + 8 * b * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω +
      16 * b * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω + 8 * b * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω
      - 16 * b * ν * σ ^ (9:ℕ) * ω - 48 * b * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω -
      48 * b * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω - 16 * b * ν * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω)
      (-144 * g * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (4:ℕ) + 464 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (5:ℕ) -
      512 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (6:ℕ) + 192 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (7:ℕ) +
      16 * g * b ^ (2:ℕ) * κ * σ ^ (8:ℕ) - 16 * g * b ^ (2:ℕ) * σ ^ (9:ℕ) +
      336 * b * κ ^ (6:ℕ) * σ ^ (4:ℕ) * w + 128 * b * κ ^ (5:ℕ) * ν * σ ^ (5:ℕ) -
      1952 * b * κ ^ (5:ℕ) * σ ^ (5:ℕ) * w - 96 * b * κ ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) +
      64 * b * κ ^ (4:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w - 304 * b * κ ^ (4:ℕ) * ν * σ ^ (6:ℕ) -
      176 * b * κ ^ (4:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) + 4256 * b * κ ^ (4:ℕ) * σ ^ (6:ℕ) * w +
      1120 * b * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) - 88 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w
      - 24 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) + 80 * b * κ ^ (3:ℕ) * ν * σ ^ (7:ℕ)
      + 384 * b * κ ^ (3:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) +
      48 * b * κ ^ (3:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) - 4416 * b * κ ^ (3:ℕ) * σ ^ (7:ℕ) * w -
      3104 * b * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) - 192 * b * κ ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) -
      48 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w +
      80 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) + 304 * b * κ ^ (2:ℕ) * ν * σ ^ (8:ℕ) +
      96 * b * κ ^ (2:ℕ) * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) -
      208 * b * κ ^ (2:ℕ) * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) + 2192 * b * κ ^ (2:ℕ) * σ ^ (8:ℕ) * w +
      3136 * b * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) + 848 * b * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) +
      104 * b * κ * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w + 80 * b * κ * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) -
      24 * b * κ * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) - 272 * b * κ * ν * σ ^ (9:ℕ) -
      496 * b * κ * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) - 176 * b * κ * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) +
      48 * b * κ * ν * σ ^ (3:ℕ) * w ^ (6:ℕ) - 416 * b * κ * σ ^ (9:ℕ) * w -
      1152 * b * κ * σ ^ (7:ℕ) * w ^ (3:ℕ) - 768 * b * κ * σ ^ (5:ℕ) * w ^ (5:ℕ) -
      96 * b * κ * σ ^ (3:ℕ) * w ^ (7:ℕ) - 32 * b * ν ^ (2:ℕ) * σ ^ (8:ℕ) * w -
      64 * b * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) - 32 * b * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) +
      64 * b * ν * σ ^ (10:ℕ) + 192 * b * ν * σ ^ (8:ℕ) * w ^ (2:ℕ) +
      192 * b * ν * σ ^ (6:ℕ) * w ^ (4:ℕ) + 64 * b * ν * σ ^ (4:ℕ) * w ^ (6:ℕ) +
      96 * b * σ ^ (8:ℕ) * w ^ (3:ℕ) + 160 * b * σ ^ (6:ℕ) * w ^ (5:ℕ) +
      64 * b * σ ^ (4:ℕ) * w ^ (7:ℕ)) (-144 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * ω +
      480 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * ω -
      576 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * ω + 288 * g * b ^ (2:ℕ) * κ * σ ^ (7:ℕ) * ω -
      48 * g * b ^ (2:ℕ) * σ ^ (8:ℕ) * ω + 144 * b * κ ^ (5:ℕ) * σ ^ (4:ℕ) * w * ω +
      192 * b * κ ^ (4:ℕ) * ν * σ ^ (5:ℕ) * ω - 960 * b * κ ^ (4:ℕ) * σ ^ (5:ℕ) * w * ω +
      96 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w * ω - 624 * b * κ ^ (3:ℕ) * ν * σ ^ (6:ℕ) * ω -
      240 * b * κ ^ (3:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω + 2208 * b * κ ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω
      + 288 * b * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω -
      216 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w * ω -
      24 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω +
      720 * b * κ ^ (2:ℕ) * ν * σ ^ (7:ℕ) * ω + 768 * b * κ ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω
      + 48 * b * κ ^ (2:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω -
      2304 * b * κ ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω - 1056 * b * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω +
      144 * b * κ * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w * ω +
      144 * b * κ * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω - 336 * b * κ * ν * σ ^ (8:ℕ) * ω -
      672 * b * κ * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω - 336 * b * κ * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω +
      1104 * b * κ * σ ^ (8:ℕ) * w * ω + 1056 * b * κ * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω +
      144 * b * κ * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω - 24 * b * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω -
      48 * b * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω -
      24 * b * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω + 48 * b * ν * σ ^ (9:ℕ) * ω +
      144 * b * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω + 144 * b * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω +
      48 * b * ν * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω - 192 * b * σ ^ (9:ℕ) * w * ω -
      288 * b * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω - 96 * b * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω) (κ * (σ ^ 2 + w ^ 2)
      - g * b * w) =
      288 * σ ^ 3 * b ^ 2 * ω ^ 6 * (κ ^ 2 + ω ^ 2) * bautinForm κ σ w (w * ν - σ * κ) := by
  unfold pcZ bautinForm bautinG bautinH
  linear_combination (-3456 * g * b ^ (3:ℕ) * κ ^ (6:ℕ) * σ ^ (4:ℕ) * w * ω ^ (4:ℕ) +
      19872 * g * b ^ (3:ℕ) * κ ^ (5:ℕ) * σ ^ (5:ℕ) * w * ω ^ (4:ℕ) -
      44352 * g * b ^ (3:ℕ) * κ ^ (4:ℕ) * σ ^ (6:ℕ) * w * ω ^ (4:ℕ) +
      1728 * g * b ^ (3:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w * ω ^ (6:ℕ) +
      48960 * g * b ^ (3:ℕ) * κ ^ (3:ℕ) * σ ^ (7:ℕ) * w * ω ^ (4:ℕ) -
      5760 * g * b ^ (3:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w * ω ^ (6:ℕ) -
      27648 * g * b ^ (3:ℕ) * κ ^ (2:ℕ) * σ ^ (8:ℕ) * w * ω ^ (4:ℕ) +
      6912 * g * b ^ (3:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w * ω ^ (6:ℕ) +
      7200 * g * b ^ (3:ℕ) * κ * σ ^ (9:ℕ) * w * ω ^ (4:ℕ) -
      3456 * g * b ^ (3:ℕ) * κ * σ ^ (7:ℕ) * w * ω ^ (6:ℕ) -
      576 * g * b ^ (3:ℕ) * σ ^ (10:ℕ) * w * ω ^ (4:ℕ) +
      576 * g * b ^ (3:ℕ) * σ ^ (8:ℕ) * w * ω ^ (6:ℕ) -
      6912 * b ^ (2:ℕ) * κ ^ (8:ℕ) * σ ^ (5:ℕ) * ω ^ (4:ℕ) +
      43200 * b ^ (2:ℕ) * κ ^ (7:ℕ) * σ ^ (6:ℕ) * ω ^ (4:ℕ) +
      10368 * b ^ (2:ℕ) * κ ^ (7:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      1152 * b ^ (2:ℕ) * κ ^ (7:ℕ) * σ ^ (4:ℕ) * ω ^ (6:ℕ) +
      3456 * b ^ (2:ℕ) * κ ^ (6:ℕ) * ν * σ ^ (5:ℕ) * w * ω ^ (4:ℕ) -
      108576 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (7:ℕ) * ω ^ (4:ℕ) -
      76320 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      5760 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (5:ℕ) * ω ^ (6:ℕ) -
      1728 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      576 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      1728 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      18432 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν * σ ^ (6:ℕ) * w * ω ^ (4:ℕ) -
      4608 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) +
      142272 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (8:ℕ) * ω ^ (4:ℕ) +
      230976 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      3456 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (6:ℕ) * ω ^ (6:ℕ) +
      25344 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      7776 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      4608 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (4:ℕ) * ω ^ (8:ℕ) -
      7488 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      576 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      36288 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (7:ℕ) * w * ω ^ (4:ℕ) +
      23616 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) -
      2304 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (5:ℕ) * w * ω ^ (6:ℕ) +
      1152 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) -
      104256 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (9:ℕ) * ω ^ (4:ℕ) -
      371520 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      18432 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (7:ℕ) * ω ^ (6:ℕ) -
      109440 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      30240 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      21888 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (5:ℕ) * ω ^ (8:ℕ) -
      3456 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      864 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      2304 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) +
      10656 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      3744 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      1152 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      31680 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (8:ℕ) * w * ω ^ (4:ℕ) -
      40320 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) +
      7488 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (6:ℕ) * w * ω ^ (6:ℕ) -
      8640 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) +
      2880 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) +
      42048 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (10:ℕ) * ω ^ (4:ℕ) +
      340992 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      36864 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (8:ℕ) * ω ^ (6:ℕ) +
      206784 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      53280 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      39168 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (6:ℕ) * ω ^ (8:ℕ) +
      23040 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
      8352 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) -
      8064 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) -
      5184 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      5760 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      2592 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      576 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      288 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      9792 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (9:ℕ) * w * ω ^ (4:ℕ) +
      23040 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) -
      8640 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (7:ℕ) * w * ω ^ (6:ℕ) +
      14400 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) -
      9216 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) +
      1152 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) -
      576 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) -
      8352 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (11:ℕ) * ω ^ (4:ℕ) -
      176544 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      27648 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (9:ℕ) * ω ^ (6:ℕ) -
      186048 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      47520 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      32256 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (7:ℕ) * ω ^ (8:ℕ) -
      48384 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      22464 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      10368 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) -
      1728 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) +
      288 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) +
      3456 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) -
      288 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      576 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      1728 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      864 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
      1728 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      1728 * b ^ (2:ℕ) * κ * ν * σ ^ (10:ℕ) * w * ω ^ (4:ℕ) +
      1728 * b ^ (2:ℕ) * κ * ν * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) +
      4032 * b ^ (2:ℕ) * κ * ν * σ ^ (8:ℕ) * w * ω ^ (6:ℕ) -
      1728 * b ^ (2:ℕ) * κ * ν * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) +
      8064 * b ^ (2:ℕ) * κ * ν * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) -
      1728 * b ^ (2:ℕ) * κ * ν * σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) +
      4032 * b ^ (2:ℕ) * κ * ν * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) +
      576 * b ^ (2:ℕ) * κ * σ ^ (12:ℕ) * ω ^ (4:ℕ) +
      46656 * b ^ (2:ℕ) * κ * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      9216 * b ^ (2:ℕ) * κ * σ ^ (10:ℕ) * ω ^ (6:ℕ) +
      75456 * b ^ (2:ℕ) * κ * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      20736 * b ^ (2:ℕ) * κ * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      11520 * b ^ (2:ℕ) * κ * σ ^ (8:ℕ) * ω ^ (8:ℕ) +
      36288 * b ^ (2:ℕ) * κ * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
      20736 * b ^ (2:ℕ) * κ * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) -
      5760 * b ^ (2:ℕ) * κ * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) +
      4608 * b ^ (2:ℕ) * κ * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) -
      2880 * b ^ (2:ℕ) * κ * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
      5760 * b ^ (2:ℕ) * κ * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) +
      576 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      1152 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      288 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      576 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      576 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      288 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
      1152 * b ^ (2:ℕ) * ν * σ ^ (11:ℕ) * w * ω ^ (4:ℕ) -
      3456 * b ^ (2:ℕ) * ν * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) -
      576 * b ^ (2:ℕ) * ν * σ ^ (9:ℕ) * w * ω ^ (6:ℕ) -
      3456 * b ^ (2:ℕ) * ν * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) -
      1728 * b ^ (2:ℕ) * ν * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) -
      1152 * b ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) -
      1728 * b ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) -
      576 * b ^ (2:ℕ) * ν * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) -
      4608 * b ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      1152 * b ^ (2:ℕ) * σ ^ (11:ℕ) * ω ^ (6:ℕ) -
      10368 * b ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      3456 * b ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      1152 * b ^ (2:ℕ) * σ ^ (9:ℕ) * ω ^ (8:ℕ) -
      8064 * b ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      5760 * b ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      1152 * b ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) -
      2304 * b ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) +
      2304 * b ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) +
      2304 * b ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) +
      1152 * b ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ)) * h2 +
      (-6912 * b ^ (2:ℕ) * κ ^ (9:ℕ) * σ ^ (5:ℕ) * ω ^ (4:ℕ) +
      39744 * b ^ (2:ℕ) * κ ^ (8:ℕ) * σ ^ (6:ℕ) * ω ^ (4:ℕ) +
      6912 * b ^ (2:ℕ) * κ ^ (8:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      3456 * b ^ (2:ℕ) * κ ^ (7:ℕ) * ν * σ ^ (5:ℕ) * w * ω ^ (4:ℕ) -
      88704 * b ^ (2:ℕ) * κ ^ (7:ℕ) * σ ^ (7:ℕ) * ω ^ (4:ℕ) -
      56448 * b ^ (2:ℕ) * κ ^ (7:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      16128 * b ^ (2:ℕ) * κ ^ (7:ℕ) * σ ^ (5:ℕ) * ω ^ (6:ℕ) -
      1728 * b ^ (2:ℕ) * κ ^ (7:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      1728 * b ^ (2:ℕ) * κ ^ (6:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      18432 * b ^ (2:ℕ) * κ ^ (6:ℕ) * ν * σ ^ (6:ℕ) * w * ω ^ (4:ℕ) -
      4608 * b ^ (2:ℕ) * κ ^ (6:ℕ) * ν * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) +
      97920 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (8:ℕ) * ω ^ (4:ℕ) +
      186624 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      83520 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (6:ℕ) * ω ^ (6:ℕ) +
      25344 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      14976 * b ^ (2:ℕ) * κ ^ (6:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      7488 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      576 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      36288 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν * σ ^ (7:ℕ) * w * ω ^ (4:ℕ) +
      23616 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) +
      3456 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν * σ ^ (5:ℕ) * w * ω ^ (6:ℕ) +
      1152 * b ^ (2:ℕ) * κ ^ (5:ℕ) * ν * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) -
      55296 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (9:ℕ) * ω ^ (4:ℕ) -
      322560 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      167040 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (7:ℕ) * ω ^ (6:ℕ) -
      109440 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      86976 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      9216 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (5:ℕ) * ω ^ (8:ℕ) -
      3456 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
      3456 * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      10656 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      3744 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      1728 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      31680 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (8:ℕ) * w * ω ^ (4:ℕ) -
      40320 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) -
      14976 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (6:ℕ) * w * ω ^ (6:ℕ) -
      8640 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) -
      1152 * b ^ (2:ℕ) * κ ^ (4:ℕ) * ν * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) +
      14400 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (10:ℕ) * ω ^ (4:ℕ) +
      313344 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      162432 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (8:ℕ) * ω ^ (6:ℕ) +
      206784 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      195552 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      43776 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (6:ℕ) * ω ^ (8:ℕ) +
      23040 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      27360 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      4608 * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) -
      5184 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      5760 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      5760 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      576 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      1152 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      9792 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (9:ℕ) * w * ω ^ (4:ℕ) +
      23040 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) +
      28224 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (7:ℕ) * w * ω ^ (6:ℕ) +
      14400 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) +
      12096 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) +
      1152 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) -
      2304 * b ^ (2:ℕ) * κ ^ (3:ℕ) * ν * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) -
      1152 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (11:ℕ) * ω ^ (4:ℕ) -
      169344 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      78336 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (9:ℕ) * ω ^ (6:ℕ) -
      186048 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      233568 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      78336 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (7:ℕ) * ω ^ (8:ℕ) -
      48384 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
      63360 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) -
      16128 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) -
      1728 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) -
      2592 * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
      288 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      576 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      8352 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      864 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      1440 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      1728 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (10:ℕ) * w * ω ^ (4:ℕ) +
      1728 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) -
      27648 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (8:ℕ) * w * ω ^ (6:ℕ) -
      1728 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) -
      29952 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) -
      1728 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (4:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) -
      2304 * b ^ (2:ℕ) * κ ^ (2:ℕ) * ν * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) +
      46080 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      16704 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (10:ℕ) * ω ^ (6:ℕ) +
      75456 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
      161856 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      64512 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (8:ℕ) * ω ^ (8:ℕ) +
      36288 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
      76608 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      20736 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) +
      4608 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) +
      7488 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) +
      6912 * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) +
      576 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
      1152 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      5472 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      576 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
      5184 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      288 * b ^ (2:ℕ) * κ * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
      1152 * b ^ (2:ℕ) * κ * ν * σ ^ (11:ℕ) * w * ω ^ (4:ℕ) -
      3456 * b ^ (2:ℕ) * κ * ν * σ ^ (9:ℕ) * w ^ (3:ℕ) * ω ^ (4:ℕ) +
      13248 * b ^ (2:ℕ) * κ * ν * σ ^ (9:ℕ) * w * ω ^ (6:ℕ) -
      3456 * b ^ (2:ℕ) * κ * ν * σ ^ (7:ℕ) * w ^ (5:ℕ) * ω ^ (4:ℕ) +
      23616 * b ^ (2:ℕ) * κ * ν * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) -
      1152 * b ^ (2:ℕ) * κ * ν * σ ^ (5:ℕ) * w ^ (7:ℕ) * ω ^ (4:ℕ) +
      9792 * b ^ (2:ℕ) * κ * ν * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) -
      576 * b ^ (2:ℕ) * κ * ν * σ ^ (3:ℕ) * w ^ (7:ℕ) * ω ^ (6:ℕ) -
      4608 * b ^ (2:ℕ) * κ * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
      1152 * b ^ (2:ℕ) * κ * σ ^ (11:ℕ) * ω ^ (6:ℕ) -
      10368 * b ^ (2:ℕ) * κ * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
      61056 * b ^ (2:ℕ) * κ * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
      23040 * b ^ (2:ℕ) * κ * σ ^ (9:ℕ) * ω ^ (8:ℕ) -
      8064 * b ^ (2:ℕ) * κ * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
      49536 * b ^ (2:ℕ) * κ * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) -
      11520 * b ^ (2:ℕ) * κ * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) -
      2304 * b ^ (2:ℕ) * κ * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) -
      9216 * b ^ (2:ℕ) * κ * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
      11520 * b ^ (2:ℕ) * κ * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) +
      1152 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      1152 * b ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) -
      2304 * b ^ (2:ℕ) * ν * σ ^ (10:ℕ) * w * ω ^ (6:ℕ) -
      4608 * b ^ (2:ℕ) * ν * σ ^ (8:ℕ) * w ^ (3:ℕ) * ω ^ (6:ℕ) -
      2304 * b ^ (2:ℕ) * ν * σ ^ (6:ℕ) * w ^ (5:ℕ) * ω ^ (6:ℕ) +
      9216 * b ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) +
      2304 * b ^ (2:ℕ) * σ ^ (10:ℕ) * ω ^ (8:ℕ) +
      11520 * b ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
      2304 * b ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) +
      4608 * b ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) +
      4608 * b ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) +
      2304 * b ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ)) * h1

@[tmio M, powerlib_domain] private theorem pc_star {B S W O j : ℂ}
    (hB : starRingEnd ℂ B = B) (hS : starRingEnd ℂ S = S) (hW : starRingEnd ℂ W = W)
    (hO : starRingEnd ℂ O = O) (hjc : starRingEnd ℂ j = -j) :
    star (pcQC B S W O j) = pcQC B S W (-O) j := by
  ext k
  fin_cases k <;> simp only [Pi.star_apply, RCLike.star_def, pcQC, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.vecHead, Matrix.cons_val_fin_one, map_mul, map_add, map_pow, hB, hS,
      hW, hO, hjc] <;> ring

@[tmio M, powerlib_domain] private theorem pc_det {G B K S W : ℂ} :
    (pcJ G B K S W).det = K * (S ^ 2 + W ^ 2) - G * B * W := by
  simp only [Matrix.det_fin_three, pcJ, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.vecHead, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The real part of the combination of the projection formula. -/
@[tmio M, powerlib_domain] private theorem pc_re (cr ci dr di y1r y1i y2r y2i y3r y3i e : ℝ)
    (he : e ≠ 0) (hc : cr ^ 2 + ci ^ 2 ≠ 0) (hd : dr ^ 2 + di ^ 2 ≠ 0) :
    (((cr : ℂ) + ci * I)⁻¹ * ((y1r : ℂ) + y1i * I) -
        2 * ((e : ℂ)⁻¹ * (((cr : ℂ) + ci * I)⁻¹ * ((y2r : ℂ) + y2i * I))) +
        ((dr : ℂ) + di * I)⁻¹ * (((cr : ℂ) + ci * I)⁻¹ * ((y3r : ℂ) + y3i * I))).re =
      pcZ cr ci dr di y1r y1i y2r y2i y3r y3i e / (e * ((cr ^ 2 + ci ^ 2) * (dr ^ 2 + di ^ 2))) :=
            by
  unfold pcZ
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.inv_re, Complex.inv_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul,
      sub_zero, zero_add, add_zero, mul_one, neg_zero, zero_div]
  have hc' : cr * cr + ci * ci ≠ 0 := by rw [← sq, ← sq]; exact hc
  have hd' : dr * dr + di * di ≠ 0 := by rw [← sq, ← sq]; exact hd
  have he' : e * e + 0 * 0 ≠ 0 := by simpa using mul_ne_zero he he
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem pc_final {Z e b σ ω w κ a B : ℝ} (hb : b ≠ 0)
    (hω : ω ≠ 0) (hw : w ≠ 0) (ha : a ≠ 0) (hK1 : a ^ 2 + ω ^ 2 ≠ 0) (he : e = -(a * ω ^ 2))
    (key : Z = 288 * σ ^ 3 * b ^ 2 * ω ^ 6 * (κ ^ 2 + ω ^ 2) * B) :
    1 / (2 * ω) * (Z / (e * ((4 * b ^ 2 * w ^ 2 * ω ^ 2 * (a ^ 2 + ω ^ 2)) *
        (9 * ω ^ 4 * (a ^ 2 + 4 * ω ^ 2))))) =
      -(4 * σ ^ 3 * (κ ^ 2 + ω ^ 2) / (ω ^ 3 * w ^ 2 * a * (a ^ 2 + ω ^ 2) * (a ^ 2 + 4 * ω ^ 2))) *
        B := by
  rw [key, he]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem pc_isCriticalPair {f : State 3 → State 3}
    {g b κ σ w ω : ℝ} (hb : 0 < b) (hw : 0 < w) (hω : 0 < ω)
    (h1 : ω ^ 2 = σ ^ 2 + w ^ 2 - 2 * σ * κ) (h2 : g * b * w = 2 * σ * (ω ^ 2 + κ ^ 2))
    (hf : f 0 = 0) (hJ : jacobianC f 0 = pcJ g b κ σ w) :
    IsCriticalPair f 0 ω (pcQC b σ w ω I)
      ((starRingEnd ℂ (pcCC b κ σ w ω I))⁻¹ • pcLC b κ σ w ω I) := by
  have hj : (I : ℂ) ^ 2 = -1 := I_sq
  have hjc : starRingEnd ℂ I = -I := conj_I
  have h1c : (ω : ℂ) ^ 2 = (σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - 2 * σ * κ := by exact_mod_cast h1
  have h2c : (g : ℂ) * b * w = 2 * σ * ((ω : ℂ) ^ 2 + (κ : ℂ) ^ 2) := by exact_mod_cast h2
  have hR := conj_ofReal
  have hc0 : pcCC b κ σ w ω I ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [pcCC] at h'
    norm_num at h'
    rcases h' with (h | h) | h <;> linarith
  refine ⟨hf, hω, ?_, ?_, ?_⟩
  · rw [hJ]
    exact pc_right hj h1c h2c
  · rw [hJ, Matrix.mulVec_smul, pc_left hj h1c h2c, smul_comm]
  · have hstar : star ((starRingEnd ℂ (pcCC b κ σ w ω I))⁻¹ • pcLC b κ σ w ω I) =
        (pcCC b κ σ w ω I)⁻¹ • star (pcLC b κ σ w ω I) := by
      ext k
      simp [Pi.star_apply]
    rw [hstar, smul_dotProduct, pc_norm (hR b) (hR κ) (hR σ) (hR w) (hR ω) hjc hj h1c,
      smul_eq_mul, inv_mul_cancel₀ hc0]

@[tmio M, powerlib_domain] private theorem pc_firstLyapunov {f : State 3 → State 3}
    {g b κ ν σ w ω : ℝ} (hb : 0 < b) (hw : 0 < w) (hω : 0 < ω)
    (ha : 0 < 2 * σ - κ) (h1 : ω ^ 2 = σ ^ 2 + w ^ 2 - 2 * σ * κ)
    (h2 : g * b * w = 2 * σ * (ω ^ 2 + κ ^ 2))
    (hJ : jacobianC f 0 = pcJ g b κ σ w) (hB : ∀ u v, bilinC f 0 u v = pcBil g b ν u v)
    (hC : ∀ u v z, trilinC f 0 u v z = pcTri g b κ u v z) :
    firstLyapunov f 0 ω (pcQC b σ w ω I)
        ((starRingEnd ℂ (pcCC b κ σ w ω I))⁻¹ • pcLC b κ σ w ω I) =
      -(4 * σ ^ 3 * (κ ^ 2 + ω ^ 2) / (ω ^ 3 * w ^ 2 * (2 * σ - κ) *
          ((2 * σ - κ) ^ 2 + ω ^ 2) * ((2 * σ - κ) ^ 2 + 4 * ω ^ 2))) *
        bautinForm κ σ w (w * ν - σ * κ) := by
  have hj : (I : ℂ) ^ 2 = -1 := I_sq
  have hjc : starRingEnd ℂ I = -I := conj_I
  have h1c : (ω : ℂ) ^ 2 = (σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - 2 * σ * κ := by exact_mod_cast h1
  have h2c : (g : ℂ) * b * w = 2 * σ * ((ω : ℂ) ^ 2 + (κ : ℂ) ^ 2) := by exact_mod_cast h2
  have hR := conj_ofReal
  have hq : star (pcQC b σ w ω I) = pcQC b σ w (-ω) I :=
    pc_star (hR b) (hR σ) (hR w) (hR ω) hjc
  have hdet : κ * (σ ^ 2 + w ^ 2) - g * b * w = -((2 * σ - κ) * ω ^ 2) := by
    linear_combination -h2 - κ * h1
  have hdet0 : κ * (σ ^ 2 + w ^ 2) - g * b * w ≠ 0 := by
    rw [hdet]
    have : 0 < (2 * σ - κ) * ω ^ 2 := by positivity
    linarith
  have hdet' : ((κ * (σ ^ 2 + w ^ 2) - g * b * w : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hdet0
  have hdetC : (κ : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2) - g * b * w =
      ((κ * (σ ^ 2 + w ^ 2) - g * b * w : ℝ) : ℂ) := by push_cast; ring
  have hc : pcCC b κ σ w ω I = ((-2 * b * w * ω ^ (2:ℕ) : ℝ) : ℂ) + ((-2 * b * κ * w * ω +
        4 * b * σ * w * ω : ℝ) : ℂ) * I := by
    simp only [pcCC]
    push_cast
    ring
  have hΔ : pcDC κ σ ω I = ((3 * κ * ω ^ (2:ℕ) - 6 * σ * ω ^ (2:ℕ) : ℝ) : ℂ) + ((-6 * ω ^ (3:ℕ) : ℝ)
        : ℂ) * I := by
    simp only [pcDC]
    push_cast
    ring
  have hΔ0 : pcDC κ σ ω I ≠ 0 := by
    rw [hΔ]
    intro h
    have h' := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
        zero_im] at h'
    have : 0 < ω ^ 3 := by positivity
    linarith
  have hA : IsUnit (jacobianC f 0).det := by
    rw [hJ, pc_det, hdetC]
    exact isUnit_iff_ne_zero.mpr hdet'
  have h2' : IsUnit (shift2 (jacobianC f 0) ω).det := by
    rw [hJ, shift2, pc_det2 hj h1c h2c]
    exact isUnit_iff_ne_zero.mpr hΔ0
  have hr : jacobianC f 0 *ᵥ (((κ * (σ ^ 2 + w ^ 2) - g * b * w : ℝ) : ℂ)⁻¹ •
      pcRC g b κ ν σ w) = bilinC f 0 (pcQC b σ w ω I) (star (pcQC b σ w ω I)) := by
    rw [Matrix.mulVec_smul, hJ, pc_r hj h1c h2c, hB, hq, hdetC, smul_smul,
      inv_mul_cancel₀ hdet', one_smul]
  have hs : shift2 (jacobianC f 0) ω *ᵥ ((pcDC κ σ ω I)⁻¹ • pcSC g b κ ν σ w ω I) =
      bilinC f 0 (pcQC b σ w ω I) (pcQC b σ w ω I) := by
    rw [Matrix.mulVec_smul, hJ, shift2, pc_S hj h1c h2c, hB, smul_smul, inv_mul_cancel₀ hΔ0,
      one_smul]
  have hpair : ∀ (z : ℂ) (v : Fin 3 → ℂ),
      pairing ((starRingEnd ℂ z)⁻¹ • pcLC b κ σ w ω I) v = z⁻¹ * pairing (pcLC b κ σ w ω I) v := by
    intro z v
    simp [pairing_apply, Finset.mul_sum, mul_assoc]
  rw [firstLyapunov_eq_of_solve hA h2' hr hs, (bilinC f 0 _).map_smul, (bilinC f 0 _).map_smul,
    hC, hB, hB, hq, (pairing _).map_smul, (pairing _).map_smul, hpair, hpair, hpair, smul_eq_mul,
    smul_eq_mul]

  rw [(pc_Y1 (hR b) (hR κ) (hR σ) (hR w) (hR ω) hjc hj h1c h2c).trans
      (show _ = ((24 * b * κ ^ (4:ℕ) * σ ^ (3:ℕ) * w - 80 * b * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w +
            104 * b * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w + 40 * b * κ ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) -
            64 * b * κ * σ ^ (6:ℕ) * w - 64 * b * κ * σ ^ (4:ℕ) * w ^ (3:ℕ) + 16 * b * σ ^ (7:ℕ) * w
            + 32 * b * σ ^ (5:ℕ) * w ^ (3:ℕ) + 16 * b * σ ^ (3:ℕ) * w ^ (5:ℕ) : ℝ) : ℂ) +
            ((8 * b * κ ^ (3:ℕ) * σ ^ (3:ℕ) * w * ω - 16 * b * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w * ω +
            8 * b * κ * σ ^ (5:ℕ) * w * ω + 8 * b * κ * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω : ℝ) : ℂ) * I
          by push_cast; ring),
    (pc_Y2 (hR b) (hR κ) (hR σ) (hR w) (hR ω) hjc hj h1c h2c).trans
      (show _ = ((-16 * g * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (4:ℕ) +
            48 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (5:ℕ) - 48 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (6:ℕ)
            + 16 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (7:ℕ) + 16 * b * κ ^ (6:ℕ) * σ ^ (4:ℕ) * w -
            96 * b * κ ^ (5:ℕ) * σ ^ (5:ℕ) * w + 16 * b * κ ^ (4:ℕ) * ν * σ ^ (6:ℕ) +
            16 * b * κ ^ (4:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) + 192 * b * κ ^ (4:ℕ) * σ ^ (6:ℕ) * w +
            32 * b * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) +
            8 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w +
            8 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) -
            48 * b * κ ^ (3:ℕ) * ν * σ ^ (7:ℕ) - 64 * b * κ ^ (3:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) -
            16 * b * κ ^ (3:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) - 160 * b * κ ^ (3:ℕ) * σ ^ (7:ℕ) * w -
            96 * b * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) -
            16 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w -
            16 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) +
            48 * b * κ ^ (2:ℕ) * ν * σ ^ (8:ℕ) + 96 * b * κ ^ (2:ℕ) * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) +
            48 * b * κ ^ (2:ℕ) * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) + 48 * b * κ ^ (2:ℕ) * σ ^ (8:ℕ) * w +
            64 * b * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) + 16 * b * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ)
            + 8 * b * κ * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w + 16 * b * κ * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ)
            + 8 * b * κ * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) - 16 * b * κ * ν * σ ^ (9:ℕ) -
            48 * b * κ * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) - 48 * b * κ * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) -
            16 * b * κ * ν * σ ^ (3:ℕ) * w ^ (6:ℕ) : ℝ) : ℂ) +
            ((-16 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * ω +
            48 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * ω -
            48 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * ω + 16 * g * b ^ (2:ℕ) * κ * σ ^ (7:ℕ) * ω
            + 16 * b * κ ^ (5:ℕ) * σ ^ (4:ℕ) * w * ω - 96 * b * κ ^ (4:ℕ) * σ ^ (5:ℕ) * w * ω +
            16 * b * κ ^ (3:ℕ) * ν * σ ^ (6:ℕ) * ω +
            16 * b * κ ^ (3:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω +
            192 * b * κ ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω + 32 * b * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω
            + 8 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w * ω +
            8 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω -
            48 * b * κ ^ (2:ℕ) * ν * σ ^ (7:ℕ) * ω -
            64 * b * κ ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω -
            16 * b * κ ^ (2:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω -
            160 * b * κ ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω - 96 * b * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω
            - 16 * b * κ * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w * ω -
            16 * b * κ * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω + 48 * b * κ * ν * σ ^ (8:ℕ) * ω +
            96 * b * κ * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω + 48 * b * κ * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω
            + 48 * b * κ * σ ^ (8:ℕ) * w * ω + 64 * b * κ * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω +
            16 * b * κ * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω + 8 * b * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω +
            16 * b * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω +
            8 * b * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω - 16 * b * ν * σ ^ (9:ℕ) * ω -
            48 * b * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω - 48 * b * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω -
            16 * b * ν * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω : ℝ) : ℂ) * I
          by push_cast; ring),
    (pc_Y3 (hR b) (hR κ) (hR σ) (hR w) (hR ω) hjc hj h1c h2c).trans
      (show _ = ((-144 * g * b ^ (2:ℕ) * κ ^ (5:ℕ) * σ ^ (4:ℕ) +
            464 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (5:ℕ) -
            512 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (6:ℕ) +
            192 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (7:ℕ) + 16 * g * b ^ (2:ℕ) * κ * σ ^ (8:ℕ) -
            16 * g * b ^ (2:ℕ) * σ ^ (9:ℕ) + 336 * b * κ ^ (6:ℕ) * σ ^ (4:ℕ) * w +
            128 * b * κ ^ (5:ℕ) * ν * σ ^ (5:ℕ) - 1952 * b * κ ^ (5:ℕ) * σ ^ (5:ℕ) * w -
            96 * b * κ ^ (5:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) +
            64 * b * κ ^ (4:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w - 304 * b * κ ^ (4:ℕ) * ν * σ ^ (6:ℕ) -
            176 * b * κ ^ (4:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) + 4256 * b * κ ^ (4:ℕ) * σ ^ (6:ℕ) * w +
            1120 * b * κ ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) -
            88 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w -
            24 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) +
            80 * b * κ ^ (3:ℕ) * ν * σ ^ (7:ℕ) + 384 * b * κ ^ (3:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) +
            48 * b * κ ^ (3:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) - 4416 * b * κ ^ (3:ℕ) * σ ^ (7:ℕ) * w -
            3104 * b * κ ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) -
            192 * b * κ ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) -
            48 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w +
            80 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) +
            304 * b * κ ^ (2:ℕ) * ν * σ ^ (8:ℕ) + 96 * b * κ ^ (2:ℕ) * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) -
            208 * b * κ ^ (2:ℕ) * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) + 2192 * b * κ ^ (2:ℕ) * σ ^ (8:ℕ) * w +
            3136 * b * κ ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) +
            848 * b * κ ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) + 104 * b * κ * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w +
            80 * b * κ * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) -
            24 * b * κ * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) - 272 * b * κ * ν * σ ^ (9:ℕ) -
            496 * b * κ * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) - 176 * b * κ * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) +
            48 * b * κ * ν * σ ^ (3:ℕ) * w ^ (6:ℕ) - 416 * b * κ * σ ^ (9:ℕ) * w -
            1152 * b * κ * σ ^ (7:ℕ) * w ^ (3:ℕ) - 768 * b * κ * σ ^ (5:ℕ) * w ^ (5:ℕ) -
            96 * b * κ * σ ^ (3:ℕ) * w ^ (7:ℕ) - 32 * b * ν ^ (2:ℕ) * σ ^ (8:ℕ) * w -
            64 * b * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) - 32 * b * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ)
            + 64 * b * ν * σ ^ (10:ℕ) + 192 * b * ν * σ ^ (8:ℕ) * w ^ (2:ℕ) +
            192 * b * ν * σ ^ (6:ℕ) * w ^ (4:ℕ) + 64 * b * ν * σ ^ (4:ℕ) * w ^ (6:ℕ) +
            96 * b * σ ^ (8:ℕ) * w ^ (3:ℕ) + 160 * b * σ ^ (6:ℕ) * w ^ (5:ℕ) +
            64 * b * σ ^ (4:ℕ) * w ^ (7:ℕ) : ℝ) : ℂ) +
            ((-144 * g * b ^ (2:ℕ) * κ ^ (4:ℕ) * σ ^ (4:ℕ) * ω +
            480 * g * b ^ (2:ℕ) * κ ^ (3:ℕ) * σ ^ (5:ℕ) * ω -
            576 * g * b ^ (2:ℕ) * κ ^ (2:ℕ) * σ ^ (6:ℕ) * ω +
            288 * g * b ^ (2:ℕ) * κ * σ ^ (7:ℕ) * ω - 48 * g * b ^ (2:ℕ) * σ ^ (8:ℕ) * ω +
            144 * b * κ ^ (5:ℕ) * σ ^ (4:ℕ) * w * ω + 192 * b * κ ^ (4:ℕ) * ν * σ ^ (5:ℕ) * ω -
            960 * b * κ ^ (4:ℕ) * σ ^ (5:ℕ) * w * ω +
            96 * b * κ ^ (3:ℕ) * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w * ω -
            624 * b * κ ^ (3:ℕ) * ν * σ ^ (6:ℕ) * ω -
            240 * b * κ ^ (3:ℕ) * ν * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω +
            2208 * b * κ ^ (3:ℕ) * σ ^ (6:ℕ) * w * ω +
            288 * b * κ ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω -
            216 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w * ω -
            24 * b * κ ^ (2:ℕ) * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * ω +
            720 * b * κ ^ (2:ℕ) * ν * σ ^ (7:ℕ) * ω +
            768 * b * κ ^ (2:ℕ) * ν * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω +
            48 * b * κ ^ (2:ℕ) * ν * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω -
            2304 * b * κ ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω -
            1056 * b * κ ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω +
            144 * b * κ * ν ^ (2:ℕ) * σ ^ (6:ℕ) * w * ω +
            144 * b * κ * ν ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * ω - 336 * b * κ * ν * σ ^ (8:ℕ) * ω -
            672 * b * κ * ν * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω -
            336 * b * κ * ν * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω + 1104 * b * κ * σ ^ (8:ℕ) * w * ω +
            1056 * b * κ * σ ^ (6:ℕ) * w ^ (3:ℕ) * ω + 144 * b * κ * σ ^ (4:ℕ) * w ^ (5:ℕ) * ω -
            24 * b * ν ^ (2:ℕ) * σ ^ (7:ℕ) * w * ω - 48 * b * ν ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * ω
            - 24 * b * ν ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * ω + 48 * b * ν * σ ^ (9:ℕ) * ω +
            144 * b * ν * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω + 144 * b * ν * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω +
            48 * b * ν * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω - 192 * b * σ ^ (9:ℕ) * w * ω -
            288 * b * σ ^ (7:ℕ) * w ^ (3:ℕ) * ω - 96 * b * σ ^ (5:ℕ) * w ^ (5:ℕ) * ω : ℝ) : ℂ) * I
          by push_cast; ring), hc, hΔ, pc_re]
  · rw [pc_key h1 h2, show (-2 * b * w * ω ^ (2:ℕ)) ^ 2 + (-2 * b * κ * w * ω +
        4 * b * σ * w * ω) ^ 2 =
        4 * b ^ 2 * w ^ 2 * ω ^ 2 * ((2 * σ - κ) ^ 2 + ω ^ 2) by ring,
      show (3 * κ * ω ^ (2:ℕ) - 6 * σ * ω ^ (2:ℕ)) ^ 2 + (-6 * ω ^ (3:ℕ)) ^ 2 = 9 * ω ^ 4 * ((2 * σ
            - κ) ^ 2 + 4 * ω ^ 2) by ring]
    exact pc_final hb.ne' hω.ne' hw.ne' ha.ne' (by positivity) (by linear_combination hdet) rfl
  · exact hdet0
  · have : 0 < b * w * ω := by positivity
    positivity
  · have : 0 < ω ^ 3 := by positivity
    positivity

/-! ## The rotated frame -/

/-- The rotation of the current components by `θ`. -/
private def rotMat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos θ, -Real.sin θ; 0, Real.sin θ, Real.cos θ]

@[tmio M, powerlib_domain] private theorem rotMat_inv (θ : ℝ) (x : State 3) :
    Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (rotMat θ)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (rotMat (-θ)) x) = x := by
  ext i
  fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_three, rotMat, Real.cos_neg,
    Real.sin_neg]
  · linear_combination (x 1) * Real.cos_sq_add_sin_sq θ
  · linear_combination (x 2) * Real.cos_sq_add_sin_sq θ

/-- The rotation as a linear isomorphism (grid frame to the frame rotated by `θ`). -/
private def rotE (θ : ℝ) : State 3 ≃L[ℝ] State 3 :=
  ContinuousLinearEquiv.equivOfInverse (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (rotMat (-θ)))
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (rotMat θ)) (rotMat_inv θ)
    (fun x => by simpa using rotMat_inv (-θ) x)

/-- **The current components rotated by `θ`**: `(v₀, cos θ v₁ − sin θ v₂, sin θ v₁ + cos θ v₂)`,
the grid-frame reading of a vector of the frame rotated by `θ`. -/
def rotC (θ : ℝ) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![v 0, (Real.cos θ : ℂ) * v 1 - (Real.sin θ : ℂ) * v 2,
    (Real.sin θ : ℂ) * v 1 + (Real.cos θ : ℂ) * v 2]

@[tmio M, powerlib_domain] private theorem rotE_symm_mulVec (θ : ℝ) (v : Fin 3 → ℂ) :
    cmat ((rotE θ).symm : State 3 →L[ℝ] State 3) *ᵥ v = rotC θ v := by
  rw [show ((rotE θ).symm : State 3 →L[ℝ] State 3) =
    Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (rotMat θ) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

@[tmio M, powerlib_domain] private theorem rotE_transpose_mulVec (θ : ℝ) (v : Fin 3 → ℂ) :
    (cmat (rotE θ : State 3 →L[ℝ] State 3))ᵀ *ᵥ v = rotC θ v := by
  rw [show (rotE θ : State 3 →L[ℝ] State 3) =
    Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (rotMat (-θ)) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Real.cos_neg, Real.sin_neg]
  ring

@[tmio M, powerlib_domain] private theorem rotE_mul_symm (θ : ℝ) :
    cmat (rotE θ : State 3 →L[ℝ] State 3) * cmat ((rotE θ).symm : State 3 →L[ℝ] State 3) = 1 := by
  rw [← cmat_comp, (rotE θ).coe_comp_coe_symm, cmat_id]

/-- **The derivatives in the rotated frame**: in the frame rotated with the operating angle
(`rotE`), the Jacobian, the second and the third derivative of a physical balanced model are the
patterns of the angle `0` with `G = K_p E`, `B = E/L`, `K = K_p Q`, `N = K_p P_ref`. -/
@[tmio M, powerlib_domain] private theorem rot_data {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) :
    jacobianC (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 =
        pcJ ((m.g.Kp * m.g.E : ℝ) : ℂ) ((m.g.E / m.g.L : ℝ) : ℂ) ((m.g.Kp * m.Q : ℝ) : ℂ)
          ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) ∧
      (∀ u v, bilinC (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 u v =
        pcBil ((m.g.Kp * m.g.E : ℝ) : ℂ) ((m.g.E / m.g.L : ℝ) : ℂ)
          ((m.g.Kp * m.g.Pref : ℝ) : ℂ) u v) ∧
      (∀ u v z, trilinC (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 u v z =
        pcTri ((m.g.Kp * m.g.E : ℝ) : ℂ) ((m.g.E / m.g.L : ℝ) : ℂ) ((m.g.Kp * m.Q : ℝ) : ℂ)
          u v z) := by
  have hL : m.g.L ≠ 0 := hp.1.L.ne'
  have hcsC := Complex.cos_sq_add_sin_sq (m.δ : ℂ)
  have hT : cmat (rotE m.δ : State 3 →L[ℝ] State 3) =
      (rotMat (-m.δ)).map (fun x => (x : ℂ)) := cmat_toEuclideanCLM _
  have hS : cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3) =
      (rotMat m.δ).map (fun x => (x : ℂ)) := cmat_toEuclideanCLM _
  have hinv : ∀ u : Fin 3 → ℂ, cmat (rotE m.δ : State 3 →L[ℝ] State 3) *ᵥ
      (cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, rotE_mul_symm, Matrix.one_mulVec]
  have hP : m.g.qssPower m.δ = m.g.Pref := hb
  refine ⟨?_, fun u v => ?_, fun u v z => ?_⟩
  · have h := jacobianC_conj (rotE m.δ) m.field 0
    rw [map_zero] at h
    rw [h, Model.jacobianC_field, hT, hS, m.jac_eq hL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pcJ, rotMat, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_neg, Real.sin_neg]
    all_goals first | ring1 |
      linear_combination (-((m.g.Kp : ℂ) * m.g.E)) * hcsC |
      linear_combination (-((m.g.R : ℂ) / m.g.L)) * hcsC | linear_combination (m.g.ω0 : ℂ) * hcsC |
      linear_combination ((m.g.E : ℂ) / m.g.L) * hcsC | linear_combination (-(m.g.ω0 : ℂ)) * hcsC
  · have h := bilinC_conj (rotE m.δ) m.field 0
      (cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3) *ᵥ u)
      (cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3) *ᵥ v)
    rw [hinv, hinv, map_zero] at h
    rw [h, rotE_symm_mulVec, rotE_symm_mulVec, Model.bilinC_field, hT, hP]
    ext k
    fin_cases k <;> simp [pcBil, rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.cos_neg, Real.sin_neg]
    all_goals first | ring1 |
      linear_combination (-((m.g.Kp : ℂ) * m.g.E) * (u 0 * v 2 + u 2 * v 0)) * hcsC |
      linear_combination (-((m.g.E : ℂ) / m.g.L) * (u 0 * v 0)) * hcsC
  · have h := trilinC_conj (rotE m.δ) m.field 0
      (cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3) *ᵥ u)
      (cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3) *ᵥ v)
      (cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3) *ᵥ z)
    rw [hinv, hinv, hinv, map_zero] at h
    rw [h, rotE_symm_mulVec, rotE_symm_mulVec, rotE_symm_mulVec, Model.trilinC_field, hT]
    ext k
    fin_cases k <;> simp [pcTri, rotC, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.cos_neg, Real.sin_neg]
    all_goals first | ring1 |
      linear_combination ((m.g.Kp : ℂ) * m.g.E * (u 0 * v 0 * z 1 + u 0 * v 1 * z 0 +
        u 1 * v 0 * z 0)) * hcsC |
      linear_combination (-((m.g.E : ℂ) / m.g.L) * (u 0 * v 0 * z 0)) * hcsC

/-! ## The critical pair and the first Lyapunov coefficient at every angle -/

/-- **The critical right eigenvector of the rotated frame** at the frequency `ω` (`b = E/L`,
`σ = R/L`, `w = ω₀`): `q = ((σ + iω)² + w², bw, b(σ + iω))`. -/
def critVecQ (b σ w ω : ℝ) : Fin 3 → ℂ :=
  ![(σ + I * ω) ^ 2 + w ^ 2, b * w, b * (σ + I * ω)]

/-- The unnormalised left eigenvector `p̃ = (bw, (σ − iω)(−iω − κ), w(−iω − κ))`. -/
def critVecL (b κ σ w ω : ℝ) : Fin 3 → ℂ :=
  ![b * w, (σ - I * ω) * (-(I * ω) - κ), w * (-(I * ω) - κ)]

/-- The pairing `⟨p̃, q⟩ = 2bwω(i(2σ − κ) − ω)`. -/
def critPairing (b κ σ w ω : ℝ) : ℂ := 2 * b * w * ω * (I * (2 * σ - κ) - ω)

/-- **The critical right eigenvector at every operating angle**: `critVecQ` of the frame rotated
with the angle `δ*`, read in the grid frame (`rotC`). -/
def Model.critQ (m : Model) (ω : ℝ) : Fin 3 → ℂ :=
  rotC m.δ (critVecQ (m.g.E / m.g.L) (m.g.R / m.g.L) m.g.ω0 ω)

/-- **The critical left eigenvector at every operating angle** (`⟨p, q⟩ = 1`; `κ = K_p Q`). -/
def Model.critP (m : Model) (ω : ℝ) : Fin 3 → ℂ :=
  rotC m.δ ((starRingEnd ℂ (critPairing (m.g.E / m.g.L) (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0
    ω))⁻¹ • critVecL (m.g.E / m.g.L) (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 ω)

/-- **The angle term** `t = K_p (ω₀ P_ref − σ Q)` (`σ = R/L`; `t = K_p E V sin δ*/L` at a balanced
point, `Line.PSC.Model.angleShift_eq`). -/
def Model.angleShift (m : Model) : ℝ :=
  m.g.ω0 * (m.g.Kp * m.g.Pref) - m.g.R / m.g.L * (m.g.Kp * m.Q)

/-- **The angle term is `K_p E V sin δ*/L`** at a balanced physical model. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.angleShift_eq {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) :
    m.angleShift = m.g.Kp * m.g.E * m.g.V * Real.sin m.δ / m.g.L := by
  have hZ := hp.1.absSq_pos.ne'
  have hL := hp.1.L.ne'
  have hZ' : m.g.ω0 ^ 2 * m.g.L ^ 2 + m.g.R ^ 2 ≠ 0 := by
    have h : m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 ≠ 0 := hZ
    rwa [show m.g.ω0 ^ 2 * m.g.L ^ 2 + m.g.R ^ 2 = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 by ring]
  rw [Model.angleShift, ← hb, Model.Q, Network.qssPower_eq _ hZ, Network.qssReactive_eq _ hZ]
  simp only [Network.absSq, Network.X]
  field_simp
  linear_combination (m.g.Kp * m.g.E * m.g.V * Real.sin m.δ) * mul_inv_cancel₀ hZ'

@[tmio M, powerlib_domain] private theorem model_equilibrium {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) : m.field 0 = 0 := by
  have h := (m.field_point_eq_zero_iff hp.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
  simpa [Model.field] using h

/-- **The critical pair at every operating angle**: at a frequency `ω > 0` with `ω² = a₁`,
(`Model.critQ`, `Model.critP`) is a critical pair of every balanced physical model on the Hopf
boundary (the rotated frame, `NormalForm.LyapunovCoefficient.isCriticalPair_conj`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isCriticalPair_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    IsCriticalPair m.field 0 ω (m.critQ ω) (m.critP ω) := by
  obtain ⟨h1, h2⟩ := Model.freq_relations_of_boundary hp hH hω2
  obtain ⟨hJ, -, -⟩ := rot_data hp hb
  have hE := hp.1.E
  have hL := hp.1.L
  have hf : (fun z => rotE m.δ (m.field ((rotE m.δ).symm z))) 0 = 0 := by
    simp [model_equilibrium hp hb]
  have hc := pc_isCriticalPair (by positivity) hp.1.ω0 hω h1 h2 hf hJ
  have h := isCriticalPair_conj (rotE m.δ).symm hc
  have e : (fun z => (rotE m.δ).symm ((fun z => rotE m.δ (m.field ((rotE m.δ).symm z)))
      ((rotE m.δ).symm.symm z))) = m.field := by
    funext z
    simp
  rw [e, map_zero, rotE_symm_mulVec, ContinuousLinearEquiv.symm_symm, rotE_transpose_mulVec] at h
  exact h

/-- **The first Lyapunov coefficient at every operating angle in closed form**: for every
balanced physical model on the Hopf boundary with `a₁, a₀ > 0` and its frequency `ω`
(`ω² = a₁`), at (`Model.critQ`, `Model.critP`),
`ℓ₁ = −4σ³(κ² + ω²) 𝔅_P(κ, σ, ω₀, t)/(ω³ ω₀² a₂ (a₂² + ω²)(a₂² + 4ω²))`, `σ = R/L`,
`κ = K_p Q`, `a₂ = 2σ − κ`, `t = Model.angleShift`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.firstLyapunov_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    firstLyapunov m.field 0 ω (m.critQ ω) (m.critP ω) =
      -(4 * (m.g.R / m.g.L) ^ 3 * ((m.g.Kp * m.Q) ^ 2 + ω ^ 2) /
          (ω ^ 3 * m.g.ω0 ^ 2 * m.g.coeff2 m.Q * (m.g.coeff2 m.Q ^ 2 + ω ^ 2) *
            (m.g.coeff2 m.Q ^ 2 + 4 * ω ^ 2))) *
        bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift := by
  have hR := Model.R_pos_of_boundary hp hH
  obtain ⟨e1, e2⟩ := Model.freq_relations_of_boundary hp hH hω2
  obtain ⟨hJ, hB, hC⟩ := rot_data hp hb
  have hE := hp.1.E
  have hL := hp.1.L
  have ha2 := coeff2_pos_of_boundary h1 h0 hH
  have hc2 := (m.coeff_atoms hL.ne').1
  rw [hc2] at ha2 ⊢
  rw [← firstLyapunov_conj (rotE m.δ) m.field 0 ω (m.critQ ω) (m.critP ω), map_zero]
  have hq : cmat (rotE m.δ : State 3 →L[ℝ] State 3) *ᵥ m.critQ ω =
      pcQC ((m.g.E / m.g.L : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [Model.critQ, ← rotE_symm_mulVec, Matrix.mulVec_mulVec, rotE_mul_symm, Matrix.one_mulVec]
    rfl
  have hp' : (cmat ((rotE m.δ).symm : State 3 →L[ℝ] State 3))ᵀ *ᵥ m.critP ω =
      (starRingEnd ℂ (pcCC ((m.g.E / m.g.L : ℝ) : ℂ) ((m.g.Kp * m.Q : ℝ) : ℂ)
        ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I))⁻¹ •
        pcLC ((m.g.E / m.g.L : ℝ) : ℂ) ((m.g.Kp * m.Q : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ)
          (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [Model.critP, ← rotE_transpose_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      rotE_mul_symm, Matrix.transpose_one, Matrix.one_mulVec]
    rfl
  rw [hq, hp']
  unfold Model.angleShift
  exact pc_firstLyapunov (by positivity) hp.1.ω0 hω ha2 e1 e2 hJ hB hC

/-- **The symbolic boundary between sub- and supercritical Hopf points at every operating
angle**: for every critical pair of a balanced physical model on the Hopf boundary with
`a₁, a₀ > 0`, `sign ℓ₁ = −sign 𝔅_P(K_p Q, R/L, ω₀, t)` (`bautinForm`,
`t = Model.angleShift = K_p E V sin δ*/L`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    {q p : Fin 3 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    SignType.sign (firstLyapunov m.field 0 ω q p) =
      -SignType.sign (bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift) := by
  have hω := hcp.freq_pos
  have hω2 := m.sq_freq_of_isCriticalPair hcp
  have hR := Model.R_pos_of_boundary hp hH
  have hL := hp.1.L
  have ha2 := coeff2_pos_of_boundary h1 h0 hH
  rw [m.sign_firstLyapunov_eq_of_boundary h1 h0 hH (Model.isCriticalPair_crit hp hb hH hω hω2)
    hcp, Model.firstLyapunov_crit hp hb hH h1 h0 hω hω2]
  have hpos : 0 < 4 * (m.g.R / m.g.L) ^ 3 * ((m.g.Kp * m.Q) ^ 2 + ω ^ 2) /
      (ω ^ 3 * m.g.ω0 ^ 2 * m.g.coeff2 m.Q * (m.g.coeff2 m.Q ^ 2 + ω ^ 2) *
        (m.g.coeff2 m.Q ^ 2 + 4 * ω ^ 2)) := by
    have := hp.1.ω0
    positivity
  rw [sign_mul, sign_neg (neg_lt_zero.mpr hpos), neg_one_mul]

/-! ## Connection conclusions at every operating angle -/

/-- **Supercritical points at every operating angle**: every balanced physical model on the Hopf
boundary with `a₁, a₀ > 0` and `𝔅_P(K_p Q, R/L, ω₀, t) > 0` is locally asymptotically stable
(`mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_bautinForm_pos
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : 0 < bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨q, p, hcp⟩ := m.exists_isCriticalPair_of_boundary hp hb h1 h0 hH
  have hs := Model.sign_firstLyapunov_crit hp hb hH h1 h0 hcp
  rw [sign_pos hB] at hs
  exact mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg _ h1 h0 hH hcp
    (sign_eq_neg_one_iff.mp hs)

/-- **Subcritical points at every operating angle**: every balanced physical model on the Hopf
boundary with `a₁, a₀ > 0` and `𝔅_P(K_p Q, R/L, ω₀, t) < 0` is unstable
(`mem_den_unstable_of_firstLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bautinForm_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  obtain ⟨q, p, hcp⟩ := m.exists_isCriticalPair_of_boundary hp hb h1 h0 hH
  have hs := Model.sign_firstLyapunov_crit hp hb hH h1 h0 hcp
  rw [sign_neg hB, neg_neg] at hs
  exact mem_den_unstable_of_firstLyapunov_pos _ h1 h0 hH hcp (sign_eq_one_iff.mp hs)

/-! ## Witnesses on the unit line at `δ* = 0`

The line `E = 1`, `R = L = ω₀ = 1` (`X = 1`, `|Z|² = 2`) with grid voltage `V`, gain `K_p` and the
set-point `P_ref = P(0) = (1 − V)/2`, read at `δ* = 0`: `Q = (1 − V)/2`, `t = 0`, and
`a₂ = 2 − K_p Q`, `a₁ = 2 − 2K_p Q`, `a₀ = K_p V`. -/

/-- The unit line with grid voltage `V` and gain `K_p`, read at `δ* = 0`. -/
def unitLine (V Kp : ℝ) : Model := ⟨⟨⟨1, V, 1, 1, 1⟩, Kp, (1 - V) / 2⟩, 0⟩

@[tmio M, powerlib_domain] private theorem unitLine_physical {V Kp : ℝ} (hV : 0 < V)
    (hK : 0 < Kp) : Meets (unitLine V Kp) .physical :=
  ⟨⟨by norm_num [unitLine], hV, by norm_num [unitLine], by norm_num [unitLine],
    by norm_num [unitLine]⟩, hK⟩

@[tmio M, powerlib_domain] private theorem unitLine_balanced (V Kp : ℝ) :
    Meets (unitLine V Kp) .balanced := by
  change (unitLine V Kp).g.qssPower 0 = (1 - V) / 2
  rw [Network.qssPower_eq _ (by norm_num [unitLine, Network.absSq, Network.X])]
  norm_num [unitLine, Network.absSq, Network.X]

@[tmio M, powerlib_domain] private theorem unitLine_Q (V Kp : ℝ) :
    (unitLine V Kp).Q = (1 - V) / 2 := by
  change (unitLine V Kp).g.qssReactive 0 = (1 - V) / 2
  rw [Network.qssReactive_eq _ (by norm_num [unitLine, Network.absSq, Network.X])]
  norm_num [unitLine, Network.absSq, Network.X]

@[tmio M, powerlib_domain] private theorem unitLine_angleShift (V Kp : ℝ) :
    (unitLine V Kp).angleShift = 0 := by
  rw [Model.angleShift, unitLine_Q]
  norm_num [unitLine]

@[tmio M, powerlib_domain] private theorem unitLine_coeffs (V Kp : ℝ) :
    (unitLine V Kp).g.coeff2 (unitLine V Kp).Q = 2 - Kp * ((1 - V) / 2) ∧
      (unitLine V Kp).g.coeff1 (unitLine V Kp).Q = 2 - 2 * (Kp * ((1 - V) / 2)) ∧
      (unitLine V Kp).g.coeff0 (unitLine V Kp).Q = Kp * V := by
  rw [unitLine_Q]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [coeff2, coeff1, coeff0, Network.ρ, Network.σ, Network.X,
    unitLine]

/-- **A supercritical Hopf point at the critical gain**: on the unit line at zero load (`V = 1`,
`Q = 0`) the critical gain `K_p = K_p,crit = 4` puts the model on the Hopf boundary
(`(s² + 2)(s + 2)`) with `𝔅_P = 64 > 0`: it is locally asymptotically stable
(`mem_den_locallyAsymptoticallyStable_of_bautinForm_pos`), although its linearization has the
eigenvalues `±i√2`. -/
@[tmio TM, powerlib_domain] theorem unitLine_critGain_mem_den_locallyAsymptoticallyStable :
    connection% (unitLine 1 4 ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨h2, h1, h0⟩ := unitLine_coeffs 1 4
  refine mem_den_locallyAsymptoticallyStable_of_bautinForm_pos _
    (unitLine_physical (by norm_num) (by norm_num)) (unitLine_balanced 1 4)
    (by rw [h2, h1, h0]; norm_num) (by rw [h1]; norm_num) (by rw [h0]; norm_num) ?_
  rw [unitLine_angleShift, unitLine_Q]
  norm_num [bautinForm, bautinG, bautinH, unitLine]

/-- **A subcritical Hopf point**: on the unit line with `V = 20/17` and `K_p = 34` (`Q = −3/34`,
`κ = −3`; the cubic `(s² + 8)(s + 5)`) `𝔅_P = −69440 < 0`: the model is unstable
(`mem_den_unstable_of_bautinForm_neg`). -/
@[tmio TM, powerlib_domain] theorem unitLine_subcritical_mem_den_unstable :
    connection% (unitLine (20 / 17) 34 ∈ family.den (.flow .unstable)) := by
  obtain ⟨h2, h1, h0⟩ := unitLine_coeffs (20 / 17) 34
  refine mem_den_unstable_of_bautinForm_neg _
    (unitLine_physical (by norm_num) (by norm_num)) (unitLine_balanced _ _)
    (by rw [h2, h1, h0]; norm_num) (by rw [h1]; norm_num) (by rw [h0]; norm_num) ?_
  rw [unitLine_angleShift, unitLine_Q]
  norm_num [bautinForm, bautinG, bautinH, unitLine]

/-- **A degenerate (Bautin-type) point, located**: on the unit line with `V = 6/5` and `K_p = 20`
(`Q = −1/10`, `κ = −2`; the cubic `(s² + 6)(s + 4)`) the model is balanced, physical and on the
Hopf boundary, it has a critical pair, and every critical pair has `ℓ₁ = 0`
(`Line.PSC.Model.sign_firstLyapunov_crit`, `ℌ_P(−2, 1, 1) = 0`). Its stability is decided by the
second Lyapunov coefficient in `theorem/GridTiedConverter/GFM/HopfBautinPSC.lean` (unstable,
`Line.PSC.unitLine_bautin_mem_den_unstable`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem unitLine_bautin_firstLyapunov :
    (∃ q p : Fin 3 → ℂ, IsCriticalPair (unitLine (6 / 5) 20).field 0 (Real.sqrt 6) q p) ∧
      ∀ ω (q p : Fin 3 → ℂ), IsCriticalPair (unitLine (6 / 5) 20).field 0 ω q p →
        firstLyapunov (unitLine (6 / 5) 20).field 0 ω q p = 0 := by
  obtain ⟨h2, h1, h0⟩ := unitLine_coeffs (6 / 5) 20
  have hp := unitLine_physical (V := 6 / 5) (Kp := 20) (by norm_num) (by norm_num)
  have hb := unitLine_balanced (6 / 5) 20
  have hH : (unitLine (6 / 5) 20).g.coeff2 (unitLine (6 / 5) 20).Q *
      (unitLine (6 / 5) 20).g.coeff1 (unitLine (6 / 5) 20).Q =
      (unitLine (6 / 5) 20).g.coeff0 (unitLine (6 / 5) 20).Q := by rw [h2, h1, h0]; norm_num
  have h1p : 0 < (unitLine (6 / 5) 20).g.coeff1 (unitLine (6 / 5) 20).Q := by rw [h1]; norm_num
  have h0p : 0 < (unitLine (6 / 5) 20).g.coeff0 (unitLine (6 / 5) 20).Q := by rw [h0]; norm_num
  refine ⟨?_, fun ω q p hcp => ?_⟩
  · have h := (unitLine (6 / 5) 20).exists_isCriticalPair_of_boundary hp hb h1p h0p hH
    rwa [h1, show (2 : ℝ) - 2 * (20 * ((1 - 6 / 5) / 2)) = 6 by norm_num] at h
  · have hs := Model.sign_firstLyapunov_crit hp hb hH h1p h0p hcp
    have hB : bautinForm ((unitLine (6 / 5) 20).g.Kp * (unitLine (6 / 5) 20).Q)
        ((unitLine (6 / 5) 20).g.R / (unitLine (6 / 5) 20).g.L) (unitLine (6 / 5) 20).g.ω0
        (unitLine (6 / 5) 20).angleShift = 0 := by
      rw [unitLine_angleShift, unitLine_Q]
      norm_num [bautinForm, bautinG, bautinH, unitLine]
    rw [hB, sign_zero, neg_zero] at hs
    exact sign_eq_zero_iff.mp hs

@[tmio M, powerlib_domain] private theorem unitLine_not_routhViolation :
    ¬ (unitLine (20 / 17) 34).RouthViolation := by
  obtain ⟨h2, h1, h0⟩ := unitLine_coeffs (20 / 17) 34
  rw [Model.RouthViolation, h2, h1, h0]
  norm_num

@[tmio M, powerlib_domain] private theorem unitLine_not_routh : ¬ (unitLine 1 4).Routh := by
  obtain ⟨h2, h1, h0⟩ := unitLine_coeffs 1 4
  rw [Model.Routh, h2, h1, h0]
  norm_num

/-- **The instability translation is not exact within physical models**: it asks for a strict
violation of the cubic Routh conditions, but the subcritical witness lies on the Routh boundary
(`a₂ a₁ = a₀`) and is unstable (`unitLine_subcritical_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_unstable :
    connection% (¬ family.ExactUnder {.physical} (.flow .unstable)) := by
  have hmem := unitLine_subcritical_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine Spectral.not_exactUnder_of_witness ?_ hmem (q := .destabilizing) ?_ ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact unitLine_physical (by norm_num) (by norm_num)
  · simp [family, translate, Spectral.localTable, Spectral.table]
  · exact unitLine_not_routhViolation

/-- **The local asymptotic translation is not exact within physical models**: it asks for the
strict cubic Routh conditions, but the supercritical witness at the critical gain lies on the
Routh boundary and is locally asymptotically stable
(`unitLine_critGain_mem_den_locallyAsymptoticallyStable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.physical} (.flow .locallyAsymptoticallyStable)) := by
  have hmem := unitLine_critGain_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine Spectral.not_exactUnder_of_witness ?_ hmem (q := .routh) ?_ ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact unitLine_physical (by norm_num) (by norm_num)
  · simp [family, translate, Spectral.localTable, Spectral.table]
  · exact unitLine_not_routh

/-! ## The fold: a saddle-node point -/

section Fold

open scoped RealInnerProductSpace
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff isNullPair_toEuclideanCLM_iff
  IsBTChain coeffA)

/-- The tangent `(1, i_s'(δ*))` of the quasi-steady set at the operating point,
`i_s'(δ) = j E e^{jδ}/(R + jX)`: the right null vector at a fold. -/
def Model.foldQ (m : Model) : Fin 3 → ℝ :=
  ![1, m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq,
    m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq]

/-- The left null vector at a fold, normalised against `Line.PSC.Model.foldQ` by
`1 − K_p D_line` (`D_line = 2E²RXL/|Z|⁴`, `Line.Network.Dline`):
`p = (1, K_p E L (X sin δ* − R cos δ*)/|Z|², −K_p E L (X cos δ* + R sin δ*)/|Z|²)` divided by
`1 − K_p D_line`. -/
def Model.foldP (m : Model) : Fin 3 → ℝ :=
  (1 - m.g.Kp * m.g.Dline)⁻¹ • ![1,
    m.g.Kp * m.g.E * m.g.L * (m.g.X * Real.sin m.δ - m.g.R * Real.cos m.δ) / m.g.absSq,
    -(m.g.Kp * m.g.E * m.g.L * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) / m.g.absSq)]

/-- The left null vector at a fold before normalisation:
`p_u = (1, K_p E L (X sin δ* − R cos δ*)/|Z|², −K_p E L (X cos δ* + R sin δ*)/|Z|²)`;
`Line.PSC.Model.foldP = p_u/(1 − K_p D_line)`. -/
def Model.foldPu (m : Model) : Fin 3 → ℝ :=
  ![1, m.g.Kp * m.g.E * m.g.L * (m.g.X * Real.sin m.δ - m.g.R * Real.cos m.δ) / m.g.absSq,
    -(m.g.Kp * m.g.E * m.g.L * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) / m.g.absSq)]

@[tmio M, powerlib_domain] private theorem fold_fderiv (m : Model) :
    fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jac := by
  rw [show m.field = fun z => m.g.field (z + m.point) from rfl, fderiv_comp_add_right,
    zero_add, m.fderiv_point]

@[tmio M, powerlib_domain] private theorem fold_Q {m : Model} (hZ : 0 < m.g.absSq)
    (hK : m.K = 0) : m.Q = m.g.E ^ 2 * m.g.X / m.g.absSq := by
  have h := m.g.syncCoeff_add_qssReactive hZ m.δ
  rw [show m.g.syncCoeff m.δ = m.K from rfl, hK, zero_add] at h
  rw [Model.Q, h, Network.κ]

/-- **The reactive power and the coefficient `a₁` at a fold**: for `L ≠ 0`, `|Z|² > 0` and
`K = 0`, `Q = E² X/|Z|²` (`Line.Network.κ`) and `a₁ = ρ (1 − K_p D_line)` (`ρ = σ² + ω₀²`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.coeff_fold (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) :
    m.Q = m.g.κ ∧ m.g.coeff1 m.Q = m.g.ρ * (1 - m.g.Kp * m.g.Dline) := by
  have hQ := fold_Q hZ hK
  refine ⟨by rw [hQ, Network.κ], ?_⟩
  have hρ : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
    simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
  have hZ' := hZ.ne'
  rw [coeff1, hQ, hρ, Network.Dline, Network.σ]
  field_simp

/-- **The tangent is a right null vector at a fold**: for `L ≠ 0`, `|Z|² > 0` and `K = 0`,
`J q = 0` for `q = Line.PSC.Model.foldQ` (at every angle). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.jac_mulVec_foldQ {m : Model} (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) : m.jac *ᵥ m.foldQ = 0 := by
  have hZ' := hZ.ne'
  have hQ := fold_Q hZ hK
  have hX : m.g.X = m.g.ω0 * m.g.L := rfl
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hA : m.g.absSq = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 := by rw [Network.absSq, hX]
  rw [m.jac_eq hL]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Model.foldQ, hQ, hX] <;>
    field_simp
  · linear_combination (-(m.g.Kp * m.g.E ^ 2 * m.g.ω0 * m.g.L)) * hcs
  · linear_combination (-(m.g.E * Real.sin m.δ)) * hA
  · linear_combination (m.g.E * Real.cos m.δ) * hA

/-- **The unnormalised left null vector at a fold**: for `L ≠ 0`, `|Z|² > 0` and `K = 0`,
`p_uᵀ J = 0` for `p_u = Line.PSC.Model.foldPu` (at every angle). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.vecMul_foldPu_jac {m : Model} (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) : m.foldPu ᵥ* m.jac = 0 := by
  have hZ' := hZ.ne'
  have hQ := fold_Q hZ hK
  have hX : m.g.X = m.g.ω0 * m.g.L := rfl
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hA : m.g.absSq = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 := by rw [Network.absSq, hX]
  rw [m.jac_eq hL]
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Model.foldPu, hQ, hX] <;>
    field_simp
  · linear_combination (-(m.g.Kp * m.g.E ^ 2 * m.g.ω0 * m.g.L)) * hcs
  · linear_combination (-(m.g.Kp * m.g.E * Real.cos m.δ)) * hA
  · linear_combination (-(m.g.Kp * m.g.E * Real.sin m.δ)) * hA

/-- **The null pair of a fold**: at a physical model with `K = 0` and `K_p D_line ≠ 1`, the
tangent `q = (1, i_s'(δ*))` (`Line.PSC.Model.foldQ`) and `p = Line.PSC.Model.foldP` are a
normalised null pair of the Jacobian at the operating point (`J q = 0`, `pᵀ J = 0`,
`⟨p, q⟩ = 1`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isNullPair_fold {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) (hD : m.g.Kp * m.g.Dline ≠ 1) :
    IsNullPair (fderiv ℝ m.field 0) (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldP) := by
  obtain ⟨hN, -⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hX : m.g.X = m.g.ω0 * m.g.L := rfl
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hDD : 1 - m.g.Kp * m.g.Dline ≠ 0 := sub_ne_zero.mpr (Ne.symm hD)
  have hA : m.g.absSq = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 := by rw [Network.absSq, hX]
  have hZ' := hZ.ne'
  rw [fold_fderiv, isNullPair_toEuclideanCLM_iff]
  refine ⟨m.jac_mulVec_foldQ hL hZ hK, ?_, ?_⟩
  · rw [show m.foldP = (1 - m.g.Kp * m.g.Dline)⁻¹ • m.foldPu from rfl, Matrix.smul_vecMul,
      m.vecMul_foldPu_jac hL hZ hK, smul_zero]
  · simp only [dotProduct, Fin.sum_univ_three, Model.foldP, Model.foldQ, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, hX]
    have hDl : m.g.Dline * m.g.absSq ^ 2 = 2 * m.g.E ^ 2 * m.g.R * (m.g.ω0 * m.g.L) * m.g.L := by
      rw [Network.Dline, hX]; field_simp
    field_simp
    linear_combination m.g.Kp * hDl -
      (2 * m.g.Kp * m.g.E ^ 2 * m.g.L ^ 2 * m.g.ω0 * m.g.R) * hcs

@[tmio M, powerlib_domain] private theorem fold_fderiv2 (m : Model) (u : State 3) (r : Fin 3) :
    (fderiv ℝ (fderiv ℝ m.field) 0 u u r : ℂ) = bilinC m.field 0 (toC u) (toC u) r := by
  rw [bilinC_toC, iteratedFDeriv_two_apply]
  simp

/-- **The quadratic form of the fold**: for `L ≠ 0` and `|Z|² > 0`,
`⟨p_u, B(q, q)⟩ = K_p (P(δ*) − c₀)` for the tangent `q = Line.PSC.Model.foldQ` and
`p_u = Line.PSC.Model.foldPu`, `c₀ = E² R/|Z|²` (at every angle). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.inner_foldPu_bilin (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    ⟪WithLp.toLp 2 m.foldPu, fderiv ℝ (fderiv ℝ m.field) 0 (WithLp.toLp 2 m.foldQ)
      (WithLp.toLp 2 m.foldQ)⟫ = m.g.Kp * (m.g.qssPower m.δ - m.g.c0) := by
  have hZ' := hZ.ne'
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have v0 := fold_fderiv2 m (WithLp.toLp 2 m.foldQ) 0
  have v1 := fold_fderiv2 m (WithLp.toLp 2 m.foldQ) 1
  have v2 := fold_fderiv2 m (WithLp.toLp 2 m.foldQ) 2
  rw [m.bilinC_field] at v0 v1 v2
  generalize fderiv ℝ (fderiv ℝ m.field) 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldQ) = v
    at v0 v1 v2 ⊢
  simp only [toC, Model.foldQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at v0 v1 v2
  have e0 : v 0 = m.g.Kp * m.g.qssPower m.δ +
      m.g.Kp * m.g.E * Real.sin m.δ * (2 * (m.g.E * (m.g.X * Real.cos m.δ -
        m.g.R * Real.sin m.δ) / m.g.absSq)) -
      m.g.Kp * m.g.E * Real.cos m.δ * (2 * (m.g.E * (m.g.X * Real.sin m.δ +
        m.g.R * Real.cos m.δ) / m.g.absSq)) := by
    apply Complex.ofReal_injective; rw [v0]; push_cast; ring
  have e1 : v 1 = -(m.g.E / m.g.L * Real.cos m.δ) := by
    apply Complex.ofReal_injective; rw [v1]; push_cast; ring
  have e2 : v 2 = -(m.g.E / m.g.L * Real.sin m.δ) := by
    apply Complex.ofReal_injective; rw [v2]; push_cast; ring
  simp only [Model.foldPu, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, e0, e1, e2]
  rw [Network.c0]
  field_simp
  linear_combination (-(m.g.Kp * m.g.E ^ 2 * m.g.R)) * hcs

/-- **The fold coefficient**: for `L ≠ 0`, `|Z|² > 0` and `K_p D_line ≠ 1`, Kuznetsov's quadratic
coefficient `a = ½ ⟨p, B(q, q)⟩` of the tangent `q = Line.PSC.Model.foldQ` and
`p = Line.PSC.Model.foldP` is `a = K_p (P(δ*) − c₀)/(2 (1 − K_p D_line))`, `c₀ = E² R/|Z|²` (at
every angle; at a fold `K = 0` it is the coefficient of the saddle-node). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_fold (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hD : m.g.Kp * m.g.Dline ≠ 1) :
    foldCoeff m.field 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldP) =
      m.g.Kp * (m.g.qssPower m.δ - m.g.c0) / (2 * (1 - m.g.Kp * m.g.Dline)) := by
  have hDD : 1 - m.g.Kp * m.g.Dline ≠ 0 := sub_ne_zero.mpr (Ne.symm hD)
  rw [foldCoeff, show m.foldP = (1 - m.g.Kp * m.g.Dline)⁻¹ • m.foldPu from rfl,
    WithLp.toLp_smul, real_inner_smul_left, m.inner_foldPu_bilin hL hZ]
  field_simp

/-- **The characteristic polynomial at a fold**: for `L ≠ 0`, `|Z|² > 0` and `K = 0` (`a₀ = 0`),
`det(sI − J) = s (s² + a₂ s + a₁)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_fold (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) :
    (jacobianC m.field 0).charpoly =
      X * (X ^ 2 + C ((m.g.coeff2 m.Q : ℝ) : ℂ) * X + C ((m.g.coeff1 m.Q : ℝ) : ℂ)) := by
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  refine Polynomial.funext fun s => ?_
  rw [m.jacobianC_field, ← Linear.det_characteristicMatrix_eq_eval, m.det_characteristicMatrix,
    h0]
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem fold_P_sub_c0_ne {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) : m.g.qssPower m.δ - m.g.c0 ≠ 0 := by
  have hZ := hp.1.absSq_pos
  have hA : m.g.A ≠ 0 :=
    div_ne_zero (mul_pos hp.1.E hp.1.V).ne' (Real.sqrt_pos.mpr hZ).ne'
  have hcos : Real.cos (m.δ - m.g.α) = 0 :=
    (mul_eq_zero.mp (show m.g.A * Real.cos (m.δ - m.g.α) = 0 from hK)).resolve_left hA
  have h : 0 < (m.g.qssPower m.δ - m.g.c0) ^ 2 := by
    rw [m.g.qssPower_eq_polar hZ, add_sub_cancel_left, mul_pow,
      show Real.sin (m.δ - m.g.α) ^ 2 = 1 by
        nlinarith [Real.sin_sq_add_cos_sq (m.δ - m.g.α)], mul_one]
    positivity
  intro h0
  rw [h0] at h
  simp at h

/-- **The fold coefficient vanishes nowhere on the fold** off the Bogdanov–Takens gain: at a
physical model with `K = 0` and `K_p D_line ≠ 1`,
`a = K_p (P(δ*) − c₀)/(2 (1 − K_p D_line)) ≠ 0` (`P(δ*) − c₀ = ± A`, `A = E V/|Z|`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_fold_ne_zero {m : Model}
    (hp : Meets m .physical) (hK : m.K = 0) (hD : m.g.Kp * m.g.Dline ≠ 1) :
    foldCoeff m.field 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldP) ≠ 0 := by
  rw [m.foldCoeff_fold hp.1.L.ne' hp.1.absSq_pos hD]
  exact div_ne_zero (mul_ne_zero hp.2.ne' (fold_P_sub_c0_ne hp hK))
    (mul_ne_zero two_ne_zero (sub_ne_zero.mpr (Ne.symm hD)))

@[tmio M, powerlib_domain] private theorem fold_ρ_pos {m : Model} (hp : Meets m .physical) :
    0 < m.g.ρ := by
  have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
    simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hp.1.L.ne']
  rw [this]; exact div_pos hp.1.absSq_pos (pow_pos hp.1.L 2)

/-- **The fold is a saddle-node**
(`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`): a balanced physical
model at a fold `K = 0` whose other two eigenvalues are stable (`a₁, a₂ > 0`) is unstable. Its
fold coefficient `a = K_p (P_ref − c₀)/(2 (1 − K_p D_line))` (`Line.PSC.Model.foldCoeff_fold`)
never vanishes there: `P_ref − c₀ = ± A ≠ 0` at a fold, and `a₁ = ρ (1 − K_p D_line) > 0`
(`Line.PSC.Model.coeff_fold`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hK : m.K = 0) (h1 : 0 < m.g.coeff1 m.Q)
    (h2 : 0 < m.g.coeff2 m.Q) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  have hD : m.g.Kp * m.g.Dline ≠ 1 := by
    intro hD
    rw [(m.coeff_fold hL hZ hK).2, hD, sub_self, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hF : ContDiff ℝ 2 m.field := (m.g.contDiff_field (k := 2)).comp
    (contDiff_id.add contDiff_const)
  have hF0 : m.field 0 = 0 := by
    show m.g.field (0 + m.point) = 0
    rw [zero_add]
    exact (m.field_point_eq_zero_iff hp.2.ne' hL hZ.ne').mpr hb
  refine Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly hF hF0
    (m.isNullPair_fold hp hK hD) (m.charpoly_fold hL hZ hK) ?_ ?_
  · intro s hs
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hs
    exact (Criteria.quadratic_roots_re_neg_iff _ _).mpr ⟨h2, h1⟩ s hs
  · exact m.foldCoeff_fold_ne_zero hp hK hD

/-- **The fold decided off its degenerate set**: a balanced physical model at a fold `K = 0`
with `a₁ ≠ 0` (off the Bogdanov–Takens gain `K_p D_line = 1`) and `a₂ ≠ 0` (off the zero–Hopf
points `K_p κ = 2σ`) is unstable: a strict Routh violation (`Line.PSC.mem_den_unstable`), or the
saddle-node law (`Line.PSC.mem_den_unstable_of_fold`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h1 : m.g.coeff1 m.Q ≠ 0) (h2 : m.g.coeff2 m.Q ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  rcases h1.lt_or_gt with h1 | h1
  · exact mem_den_unstable m hp hb (Or.inr (Or.inl h1))
  rcases h2.lt_or_gt with h2 | h2
  · exact mem_den_unstable m hp hb (Or.inl h2)
  exact mem_den_unstable_of_fold m hp hb hK h1 h2

/-! ### The Bogdanov–Takens gain `K_p D_line = 1` -/

/-- The second Jordan vector at the Bogdanov–Takens gain, `q₁ = (0, w)`,
`w = −j L E e^{jδ*}/(R + jX)²`:
`w = L E ((R² − X²) sin δ* − 2RX cos δ*, −((R² − X²) cos δ* + 2RX sin δ*))/|Z|⁴`. -/
def Model.btChain (m : Model) : Fin 3 → ℝ :=
  ![0, m.g.L * m.g.E * ((m.g.R ^ 2 - m.g.X ^ 2) * Real.sin m.δ -
      2 * m.g.R * m.g.X * Real.cos m.δ) / m.g.absSq ^ 2,
    -(m.g.L * m.g.E * ((m.g.R ^ 2 - m.g.X ^ 2) * Real.cos m.δ +
      2 * m.g.R * m.g.X * Real.sin m.δ) / m.g.absSq ^ 2)]

/-- The left null vector at the Bogdanov–Takens gain, normalised against
`Line.PSC.Model.btChain`: `p₁ = (ρ/a₂) p_u` (`p_u = Line.PSC.Model.foldPu`). -/
def Model.btLeft (m : Model) : Fin 3 → ℝ := (m.g.ρ / m.g.coeff2 m.Q) • m.foldPu

/-- **The Jordan chain at the Bogdanov–Takens gain**: for `L ≠ 0`, `|Z|² > 0` and
`K_p D_line = 1`, `J q₁ = q₀` for `q₁ = Line.PSC.Model.btChain`, `q₀ = Line.PSC.Model.foldQ` (at
every angle; the first row is `K_p D_line = 1`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.jac_mulVec_btChain {m : Model} (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hD : m.g.Kp * m.g.Dline = 1) : m.jac *ᵥ m.btChain = m.foldQ := by
  have hZ' := hZ.ne'
  have hX : m.g.X = m.g.ω0 * m.g.L := rfl
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hA : m.g.absSq = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 := by rw [Network.absSq, hX]
  have hDl : m.g.Dline * m.g.absSq ^ 2 = 2 * m.g.E ^ 2 * m.g.R * (m.g.ω0 * m.g.L) * m.g.L := by
    rw [Network.Dline, hX]; field_simp
  rw [m.jac_eq hL]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Model.btChain,
    Model.foldQ, hX] <;> field_simp
  · linear_combination (2 * m.g.Kp * m.g.E ^ 2 * m.g.L ^ 2 * m.g.R * m.g.ω0) * hcs -
      m.g.Kp * hDl + m.g.absSq ^ 2 * hD
  · linear_combination (m.g.E * m.g.R * Real.sin m.δ - m.g.E * m.g.L * m.g.ω0 * Real.cos m.δ) *
      hA
  · linear_combination (-(m.g.E * m.g.ω0 * m.g.L * Real.sin m.δ) -
      m.g.E * m.g.R * Real.cos m.δ) * hA

/-- `⟨p_u, q₁⟩ = K_p E² L² X (3R² − X²)/|Z|⁶` at every angle. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldPu_dot_btChain_eq (m : Model)
    (hZ : 0 < m.g.absSq) :
    m.foldPu ⬝ᵥ m.btChain = m.g.Kp * m.g.E ^ 2 * m.g.L ^ 2 * m.g.X *
      (3 * m.g.R ^ 2 - m.g.X ^ 2) / m.g.absSq ^ 3 := by
  have hZ' := hZ.ne'
  have hcs := Real.cos_sq_add_sin_sq m.δ
  simp only [dotProduct, Fin.sum_univ_three, Model.foldPu, Model.btChain, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  linear_combination (3 * m.g.Kp * m.g.E ^ 2 * m.g.L ^ 2 * m.g.X * m.g.R ^ 2 -
    m.g.Kp * m.g.E ^ 2 * m.g.L ^ 2 * m.g.X ^ 3) * hcs

/-- **The normalisation at the Bogdanov–Takens point**: at a fold `K = 0` with
`K_p D_line = 1` (`L ≠ 0`, `|Z|² > 0`), `ρ ⟨p_u, q₁⟩ = a₂ = (3R² − X²)/(2RL)`: the chain normalises
exactly when the third eigenvalue `−a₂` is not zero. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldPu_dot_btChain {m : Model} (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) (hD : m.g.Kp * m.g.Dline = 1) :
    m.g.ρ * (m.foldPu ⬝ᵥ m.btChain) = m.g.coeff2 m.Q := by
  have hZ' := hZ.ne'
  have hQ := fold_Q hZ hK
  have hA : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  have hDl : m.g.Dline * m.g.absSq ^ 2 = 2 * m.g.E ^ 2 * m.g.R * m.g.X * m.g.L := by
    rw [Network.Dline]; field_simp
  have hρ : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
    simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
  rw [m.foldPu_dot_btChain_eq hZ, coeff2, hQ, hρ, Network.σ]
  field_simp
  linear_combination (m.g.L * m.g.Kp * m.g.E ^ 2 * m.g.X) * hA - 2 * m.g.R * m.g.Kp * hDl +
    2 * m.g.R * m.g.absSq ^ 2 * hD

/-- **The kernel is one-dimensional**: for `L ≠ 0` and `|Z|² > 0` every null vector of the
Jacobian is a multiple of the tangent `Line.PSC.Model.foldQ` (the line rows alone; at every
angle). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.eq_smul_foldQ_of_mulVec_eq_zero (m : Model)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) {v : Fin 3 → ℝ} (hv : m.jac *ᵥ v = 0) :
    v = v 0 • m.foldQ := by
  have hZ' := hZ.ne'
  have hX : m.g.X = m.g.ω0 * m.g.L := rfl
  have hA : m.g.absSq = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 := by rw [Network.absSq, hX]
  have h1 : (m.jac *ᵥ v) 1 = 0 := by rw [hv]; rfl
  have h2 : (m.jac *ᵥ v) 2 = 0 := by rw [hv]; rfl
  rw [m.jac_eq hL] at h1 h2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  field_simp at h1 h2
  funext i
  fin_cases i
  · show v 0 = v 0 * 1
    ring
  · show v 1 = v 0 * (m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq)
    field_simp
    rw [hX, hA]
    linear_combination (-m.g.R) * h1 + (-(m.g.L * m.g.ω0)) * h2
  · show v 2 = v 0 * (m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq)
    field_simp
    rw [hX, hA]
    linear_combination (m.g.L * m.g.ω0) * h1 + (-m.g.R) * h2

/-- **The Bogdanov–Takens chain**: at a physical fold `K = 0` with the gain `K_p D_line = 1` and
`a₂ ≠ 0`, `q₀ = Line.PSC.Model.foldQ`, `q₁ = Line.PSC.Model.btChain` and
`p₁ = Line.PSC.Model.btLeft` complete to a normalised chain (`IsBTChain.exists_of_left`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_isBTChain_of_bt {m : Model}
    (hp : Meets m .physical) (hK : m.K = 0) (hD : m.g.Kp * m.g.Dline = 1)
    (h2 : m.g.coeff2 m.Q ≠ 0) :
    ∃ p₀ : State 3, IsBTChain (fderiv ℝ m.field 0) (WithLp.toLp 2 m.foldQ)
      (WithLp.toLp 2 m.btChain) p₀ (WithLp.toLp 2 m.btLeft) := by
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  have hin : ∀ a b : Fin 3 → ℝ, ⟪(WithLp.toLp 2 a : State 3), WithLp.toLp 2 b⟫ = a ⬝ᵥ b :=
    fun a b => by rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  rw [fold_fderiv]
  refine NormalForm.BogdanovTakens.IsBTChain.exists_of_left ?_ ?_ (fun v hv => ?_)
    (fun v => ?_) ?_
  · rw [Matrix.toEuclideanCLM_toLp, m.jac_mulVec_foldQ hL hZ hK]; rfl
  · rw [Matrix.toEuclideanCLM_toLp, m.jac_mulVec_btChain hL hZ hD]
  · have hv' : m.jac *ᵥ (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa [Matrix.ofLp_toEuclideanCLM] using this
    have he := m.eq_smul_foldQ_of_mulVec_eq_zero hL hZ hv'
    refine ⟨v 0, ?_⟩
    ext i
    have := congrFun he i
    simpa using this
  · rw [Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec, Model.btLeft, Matrix.smul_vecMul,
      m.vecMul_foldPu_jac hL hZ hK, smul_zero, zero_dotProduct]
  · rw [hin, Model.btLeft, smul_dotProduct, smul_eq_mul, div_mul_eq_mul_div,
      m.foldPu_dot_btChain hL hZ hK hD, div_self h2]

/-- **The Bogdanov–Takens coefficient `a`**: for `L ≠ 0` and `|Z|² > 0`,
`a = ½ ⟨p₁, B(q₀, q₀)⟩ = K_p ρ (P(δ*) − c₀)/(2 a₂)` for `q₀ = Line.PSC.Model.foldQ`,
`p₁ = Line.PSC.Model.btLeft`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.coeffA_bt (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    coeffA m.field 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.btLeft) =
      m.g.Kp * m.g.ρ * (m.g.qssPower m.δ - m.g.c0) / (2 * m.g.coeff2 m.Q) := by
  rw [coeffA, Model.btLeft, WithLp.toLp_smul, real_inner_smul_left, m.inner_foldPu_bilin hL hZ]
  ring

/-- **The Bogdanov–Takens point is unstable** (the cusp,
`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`): a balanced physical model at a
fold `K = 0` with the gain `K_p D_line = 1` and `a₂ > 0` (`det(sI − J) = s² (s + a₂)`) is
unstable. Its coefficient `a = K_p ρ (P(δ*) − c₀)/(2 a₂)` (`Line.PSC.Model.coeffA_bt`) never
vanishes there (`P(δ*) − c₀ = ± A`): no codimension-three point `a = 0`; the chain degenerates
only at `a₂ = 0` (`X² = 3R²`, a triple zero). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bt (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hK : m.K = 0) (hD : m.g.Kp * m.g.Dline = 1)
    (h2 : 0 < m.g.coeff2 m.Q) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  obtain ⟨p₀, hch⟩ := m.exists_isBTChain_of_bt hp hK hD h2.ne'
  have hF : ContDiff ℝ 2 m.field := (m.g.contDiff_field (k := 2)).comp
    (contDiff_id.add contDiff_const)
  have hF0 : m.field 0 = 0 := by
    show m.g.field (0 + m.point) = 0
    rw [zero_add]
    exact (m.field_point_eq_zero_iff hp.2.ne' hL hZ.ne').mpr hb
  have hker : ∀ v, fderiv ℝ m.field 0 v = 0 → ∃ s : ℝ, v = s • WithLp.toLp 2 m.foldQ := by
    intro v hv
    rw [fold_fderiv] at hv
    have hv' : m.jac *ᵥ (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa [Matrix.ofLp_toEuclideanCLM] using this
    have he := m.eq_smul_foldQ_of_mulVec_eq_zero hL hZ hv'
    refine ⟨v 0, ?_⟩
    ext i
    have := congrFun he i
    simpa using this
  have h1 : m.g.coeff1 m.Q = 0 := by rw [(m.coeff_fold hL hZ hK).2, hD, sub_self, mul_zero]
  have hchar : (cmat (fderiv ℝ m.field 0)).charpoly =
      X ^ 2 * (X + C ((m.g.coeff2 m.Q : ℝ) : ℂ)) := by
    have h := m.charpoly_fold hL hZ hK
    rw [h1] at h
    rw [show cmat (fderiv ℝ m.field 0) = jacobianC m.field 0 from rfl, h]
    simp
    ring
  have hr : ∀ s : ℂ, (X + C ((m.g.coeff2 m.Q : ℝ) : ℂ)).eval s = 0 → s.re < 0 := by
    intro s hs
    simp only [eval_add, eval_X, eval_C] at hs
    have : s = -((m.g.coeff2 m.Q : ℝ) : ℂ) := by linear_combination hs
    rw [this]; simp [h2]
  refine hch.unstable_of_coeffA_ne_zero hF hF0 hker hchar hr ?_
  rw [m.coeffA_bt hL hZ]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp.2.ne' (fold_ρ_pos hp).ne')
    (fold_P_sub_c0_ne hp hK)) (mul_ne_zero two_ne_zero h2.ne')

/-- **The fold decided off the zero–Hopf points**: a balanced physical model at a fold `K = 0`
with `a₂ ≠ 0` is unstable: off the Bogdanov–Takens gain (`a₁ ≠ 0`)
`Line.PSC.mem_den_unstable_of_fold_of_ne`; at it (`a₁ = 0`, `K_p D_line = 1`) a strict Routh
violation (`a₂ < 0`, `Line.PSC.mem_den_unstable`) or the cusp (`a₂ > 0`,
`Line.PSC.mem_den_unstable_of_bt`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_coeff2_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h2 : m.g.coeff2 m.Q ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases h1 : m.g.coeff1 m.Q = 0
  swap
  · exact mem_den_unstable_of_fold_of_ne m hp hb hK h1 h2
  rcases h2.lt_or_gt with h2 | h2
  · exact mem_den_unstable m hp hb (Or.inl h2)
  have hD : m.g.Kp * m.g.Dline = 1 := by
    rw [(m.coeff_fold hp.1.L.ne' hp.1.absSq_pos hK).2] at h1
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (fold_ρ_pos hp).ne')).symm
  exact mem_den_unstable_of_bt m hp hb hK hD h2

end Fold

/-! ## Complete Lyapunov and local asymptotic membership off the degenerate set -/

/-- The degenerate balanced points of power synchronization on the line still undecided: the
fold points `K = 0` (`a₀ = 0`, a zero eigenvalue) with `a₁ ≥ 0` and a pair of imaginary
eigenvalues or a triple zero (`a₂ = 0`, i.e. `K_p Q = 2σ`: zero–Hopf), and the Bautin-type points
of the Hopf boundary (`a₂ a₁ = a₀`, `a₁, a₀ > 0`, `𝔅_P = 0`). The other fold points, the
Bogdanov–Takens gain `K_p D_line = 1` included, are decided
(`Line.PSC.mem_den_unstable_of_fold_of_coeff2_ne`). -/
def Model.Degenerate (m : Model) : Prop :=
  Meets m .balanced ∧ ((m.K = 0 ∧ 0 ≤ m.g.coeff1 m.Q ∧ m.g.coeff2 m.Q = 0) ∨
    (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
      0 < m.g.coeff0 m.Q ∧ bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift = 0))

/-- Off the degenerate set, a balanced physical model that is neither Routh-stable nor a
supercritical Hopf point is unstable (strict Routh violation, the fold law, the subcritical law). -/
@[tmio TM, powerlib_domain] private theorem mem_den_unstable_of_nondegenerate (m : Model)
    (hp : Meets m .physical) (hd : ¬ m.Degenerate) (hb : Meets m .balanced)
    (hn : ¬ (m.Routh ∨ (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧
        0 < m.g.coeff1 m.Q ∧ 0 < m.g.coeff0 m.Q ∧
        0 < bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases hv : m.RouthViolation
  · exact mem_den_unstable m hp hb hv
  obtain ⟨hr, hh⟩ := not_or.mp hn
  unfold Model.RouthViolation at hv
  unfold Model.Routh at hr
  push Not at hv hr hh
  obtain ⟨v2, v1, v0, v3⟩ := hv
  rcases v0.lt_or_eq with h0 | h0
  · have h2 : 0 < m.g.coeff2 m.Q := by
      rcases v2.lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at v3
        linarith
    have hH : m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q := le_antisymm (hr h2 h0) v3
    have h1 : 0 < m.g.coeff1 m.Q := by
      by_contra h1
      push Not at h1
      nlinarith
    rcases (hh hH h1 h0).lt_or_eq with hB | hB
    · exact mem_den_unstable_of_bautinForm_neg m hp hb hH h1 h0 hB
    · exact absurd ⟨hb, Or.inr ⟨hH, h1, h0, hB⟩⟩ hd
  · have hK : m.K = 0 := by
      rw [m.coeff0_eq hp.1.L.ne' hp.1.absSq_pos] at h0
      rcases mul_eq_zero.mp h0.symm with h' | h'
      · exact absurd h' hp.2.ne'
      · exact (mul_eq_zero.mp h').resolve_left (fold_ρ_pos hp).ne'
    exact mem_den_unstable_of_fold_of_coeff2_ne m hp hb hK fun h => hd ⟨hb, Or.inl ⟨hK, v1, h⟩⟩

/-- **Complete local asymptotic membership** (the counterpart of the rate-coupled GFL PLL's
`GFL.RatePLL.mem_den_locallyAsymptoticallyStable_iff`): a physical model off the degenerate set
(`Line.PSC.Model.Degenerate`) is locally asymptotically stable iff it is balanced and either meets
the strict cubic Routh conditions or lies on the Hopf boundary (`a₂ a₁ = a₀`, `a₁, a₀ > 0`) with
`𝔅_P > 0`. Every other physical non-degenerate model is unstable or not an equilibrium: a strict
Routh violation (linear instability), the fold off its degenerate set
(`Line.PSC.mem_den_unstable_of_fold_of_ne`), the Hopf boundary with `𝔅_P < 0` (subcritical). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (m : Model)
    (hp : Meets m .physical) (hd : ¬ m.Degenerate) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧
        0 < m.g.coeff1 m.Q ∧ 0 < m.g.coeff0 m.Q ∧
        0 < bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by
  unfold TMIO.Statement
  have hs := chain_le_semantics
  unfold powerlib.TMIO.Statement at hs
  constructor
  · intro hl
    have hb : Meets m .balanced := by
      by_contra hb
      have hne : m.field 0 ≠ 0 := by
        intro h0
        apply hb
        have h' : m.g.field m.point = 0 := by simpa [Model.field] using h0
        exact (m.field_point_eq_zero_iff hp.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mp h'
      rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hl
      change LocalAsymptoticStable m.field 0 at hl
      exact Dynamics.unstable_of_ne_zero m.contDiff_field hne hl.1
    refine ⟨hb, by_contra fun hn => ?_⟩
    have hu := mem_den_unstable_of_nondegenerate m hp hd hb hn
    unfold powerlib.TMIO.Statement at hu
    exact Spectral.not_mem_den_lyapunovStable_of_unstable hu
      (Spectral.den_las_subset_lyapunovStable hl)
  · rintro ⟨hb, hr | ⟨hH, h1, h0, hB⟩⟩
    · refine (Family.chain_le_semantics_iff.mp hs _) ((TMIO.mem_realize _ _ _).mpr ?_)
      intro q hq
      simp only [family, translate, Spectral.localTable, Spectral.table, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact hb
      · exact hp
      · exact hr
    · exact mem_den_locallyAsymptoticallyStable_of_bautinForm_pos m hp hb hH h1 h0 hB

/-- **Complete Lyapunov membership**: off the degenerate set (`Line.PSC.Model.Degenerate`) a
physical model is Lyapunov stable iff it is locally asymptotically stable, i.e. iff it is balanced
and either meets the strict cubic Routh conditions or lies on the Hopf boundary with `𝔅_P > 0`
(`Line.PSC.mem_den_locallyAsymptoticallyStable_iff`); every other non-degenerate physical model is
unstable or not an equilibrium. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff (m : Model)
    (hp : Meets m .physical) (hd : ¬ m.Degenerate) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧
        0 < m.g.coeff1 m.Q ∧ 0 < m.g.coeff0 m.Q ∧
        0 < bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by
  have hlas := mem_den_locallyAsymptoticallyStable_iff m hp hd
  unfold powerlib.TMIO.Statement at hlas ⊢
  constructor
  · intro hl
    have heq : m.g.field m.point = 0 :=
      Dynamics.isEquilibrium_of_lyapunovStable m.g.contDiff_field
        ((Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.g.field)
          (pt := Model.point) family_isAutonomous).mp hl)
    have hb : Meets m .balanced :=
      (m.field_point_eq_zero_iff hp.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mp heq
    refine ⟨hb, by_contra fun hn => ?_⟩
    have hu := mem_den_unstable_of_nondegenerate m hp hd hb hn
    unfold powerlib.TMIO.Statement at hu
    exact Spectral.not_mem_den_lyapunovStable_of_unstable hu hl
  · intro h
    exact Spectral.den_las_subset_lyapunovStable (hlas.mpr h)

end PSC
end powerlib.GFM.Line
