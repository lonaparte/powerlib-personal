import theorem.GridTiedConverter.GFM.HopfLinePSC
import theorem.Dynamics.ZeroHopfReduction

/-! # The power-synchronization converter on a dynamic line: the zero–Hopf points of the fold

Model boundary.
* The three-state power-synchronization control `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, i_d, i_q) : State 3`,
  grid dq frame at `ω₀`, export-positive power, constant `E`, `δ̇ = K_p (P_ref − P_e)`,
  `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, inertia, inner loops, PLL, delay or PWM.
  Read about a selected angle (`Line.PSC.Model`), translated so that the operating point is the
  origin.
* The zero–Hopf points of the fold: balanced physical models (`P(δ*) = P_ref`, `E, V, L, ω₀ > 0`,
  `R ≥ 0`, `K_p > 0`) with `K = P'(δ*) = 0` (`a₀ = 0`), `K_p Q = 2σ` (`a₂ = 0`, `σ = R/L`) and
  `a₁ = ρ − 4σ² > 0` (`ρ = σ² + ω₀²`): `det(sI − J) = s (s² + a₁)`, the eigenvalues `0, ±iω`,
  `ω² = a₁`, and no stable part (the centre manifold is the whole state space).
* Level: Lyapunov instability (LeanForControl's `Unstable`) of the operating point, through
  `Line.PSC.family`; exact closed forms of the normal-form coefficients.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.5 and §8.7 (the
zero–Hopf normal form and its projection formulas); the generic law
`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`
(`theorem/Dynamics/ZeroHopfReduction.lean`, `theorem/Dynamics/ZeroHopfNormalForm.lean`); the null
pair, the fold coefficient, the characteristic polynomial at a fold, the critical pair and the
second derivative of `theorem/GridTiedConverter/GFM/HopfLinePSC.lean`
(`Line.PSC.Model.isNullPair_fold`, `Model.foldCoeff_fold`, `Model.charpoly_fold`,
`Model.isCriticalPair_crit`, `Model.bilinC_field`). The coefficient `c` was derived with exact
computer algebra (SymPy, rational parametrisation of `ω₀² = ω² + 3σ²`, untrusted discovery) and
is proved here by `linear_combination`.

Results.
* `Line.PSC.Model.pairing_bilinC_foldQ`: along the tangent `q₀ = Line.PSC.Model.foldQ`, the
  pairing of the second derivative with vectors of the frame rotated by `δ*` is
  `⟨rotC p', B(q₀, rotC q')⟩ = p̄'₀ (K_p (P − c₀) q'₀ − K_p E q'₂) − (E/L) p̄'₁ q'₀` at every angle.
* **The coefficients at a zero–Hopf point** (`D' = K_p (P(δ*) − c₀) ≠ 0`, `c₀ = E² R/|Z|²`):
  `a = ρ D'/(2ω²)` (`Line.PSC.Model.foldCoeff_zeroHopf`, from `Model.foldCoeff_fold` and
  `a₁ = ρ(1 − K_p D_line)`), `c = −2σ² D'/ω²` (`Line.PSC.Model.zhC_zeroHopf`), so
  `c/a = −4σ²/ρ < 0` and `a(a − c) = ρ(ρ + 4σ²) D'²/(4ω⁴) > 0`
  (`Line.PSC.Model.zeroHopfDecided_zeroHopf`): every zero–Hopf point of the fold is in the
  decided regime `a(a − c) > 0` of `Dynamics.CenterManifold.ZeroHopfDecided`; `b` is not needed
  and not stated.

Family and connection conclusions.
No new family: connection conclusions on `Line.PSC.family`.
* **`Line.PSC.mem_den_unstable_of_zeroHopf`**: a balanced physical model with `K = 0`,
  `K_p Q = 2σ` and `a₁ > 0` is unstable (the escaping half axis of the centre manifold attracts
  its neighbours). With `Line.PSC.mem_den_unstable_of_fold_of_ne` this decides every fold point
  with `a₁ ≠ 0`; the fold points left are the Bogdanov–Takens gain `a₁ = 0`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace PSC
open Complex Matrix Polynomial
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff)
open powerlib.Dynamics.CenterManifold (zhC ZeroHopfDecided)

/-- **The pairing along the tangent in the rotated frame**: for `L ≠ 0`, `|Z|² > 0`, at every
angle, `⟨rotC p', B(q₀, rotC q')⟩ = p̄'₀ (K_p (P − c₀) q'₀ − K_p E q'₂) − (E/L) p̄'₁ q'₀`
(`q₀ = Line.PSC.Model.foldQ`, `B` the second derivative at the operating point). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem Model.pairing_bilinC_foldQ (m : Model) (p' q' : Fin 3 → ℂ) :
    pairing (rotC m.δ p') (bilinC m.field 0 (toC (WithLp.toLp 2 m.foldQ)) (rotC m.δ q')) =
      starRingEnd ℂ (p' 0) * (((m.g.Kp * (m.g.qssPower m.δ - m.g.c0) : ℝ) : ℂ) * q' 0 -
        ((m.g.Kp * m.g.E : ℝ) : ℂ) * q' 2) -
        ((m.g.E / m.g.L : ℝ) : ℂ) * starRingEnd ℂ (p' 1) * q' 0 := by
  have hcs : (Real.cos m.δ : ℂ) ^ 2 + (Real.sin m.δ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq m.δ
  rw [m.bilinC_field, pairing_apply, Fin.sum_univ_three]
  simp only [rotC, toC, Model.foldQ, Network.c0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_mul,
    Complex.conj_ofReal]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_one]
  linear_combination (-((m.g.E : ℂ) ^ 2 * (m.g.Kp : ℂ) * (m.g.R : ℂ) * starRingEnd ℂ (p' 0) *
    q' 0 / (m.g.absSq : ℂ)) - (m.g.E : ℂ) * (m.g.Kp : ℂ) * starRingEnd ℂ (p' 0) * q' 2 -
    (m.g.E : ℂ) * starRingEnd ℂ (p' 1) * q' 0 / (m.g.L : ℂ)) * hcs

/-- **The coefficient `c` at a zero–Hopf point**: for a physical model with `K = 0`, `K_p Q = 2σ`
(`a₂ = 0`) and `ω > 0`, `ω² = a₁`, Kuznetsov's `c = Re⟨p, B(q₀, q)⟩` of the tangent
`q₀ = Line.PSC.Model.foldQ` and the critical pair `Line.PSC.Model.critQ`, `Model.critP` is
`c = −2σ² K_p (P(δ*) − c₀)/ω²` (`σ = R/L`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.zhC_zeroHopf {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hK : m.K = 0) (h2 : m.g.coeff2 m.Q = 0) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    zhC m.field (WithLp.toLp 2 m.foldQ) (m.critQ ω) (m.critP ω) =
      -(2 * (m.g.R / m.g.L) ^ 2 * (m.g.Kp * (m.g.qssPower m.δ - m.g.c0)) / ω ^ 2) := by
  have hL := hp.1.L.ne'
  obtain ⟨e2, e1, e0⟩ := m.coeff_atoms hL
  have hκ : m.g.Kp * m.Q = 2 * (m.g.R / m.g.L) := by linarith
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hp.1.absSq_pos, hK]; simp
  obtain ⟨f1, f2⟩ := Model.freq_relations_of_boundary hp (by rw [h2, h0, zero_mul]) hω2
  rw [hκ] at f1 f2
  rw [Dynamics.CenterManifold.zhC_eq_pairing]
  unfold Model.critQ Model.critP
  rw [hκ, m.pairing_bilinC_foldQ]
  simp only [critVecQ, critVecL, critPairing, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  set σ := m.g.R / m.g.L
  set b := m.g.E / m.g.L
  set w := m.g.ω0
  set D := m.g.Kp * (m.g.qssPower m.δ - m.g.c0)
  set k := m.g.Kp * m.g.E
  have hpair : (2 * (b : ℂ) * (w : ℂ) * (ω : ℂ) * (I * (2 * (σ : ℂ) - ((2 * σ : ℝ) : ℂ)) - (ω : ℂ)))
      = ((-(2 * b * w * ω ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [hpair]
  simp only [Complex.conj_ofReal, map_mul, map_sub, map_neg, Complex.conj_I]
  simp [Complex.mul_re, Complex.mul_im, sq]
  have hb0 : b ≠ 0 := div_ne_zero hp.1.E.ne' hL
  have hw0 : w ≠ 0 := hp.1.ω0.ne'
  have hω0 : ω ≠ 0 := hω.ne'
  have e : σ * σ - ω * ω + w * w = 4 * σ ^ 2 := by nlinarith [f1]
  have e3 : k * (b * σ) = 2 * σ ^ 2 * (ω ^ 2 + 4 * σ ^ 2) / w := by
    field_simp
    linear_combination σ * f2
  rw [e, e3]
  field_simp
  ring

/-- **The fold coefficient at a zero–Hopf point**: `a = ρ K_p (P(δ*) − c₀)/(2ω²)` (with
`Model.foldCoeff_fold` and `a₁ = ρ (1 − K_p D_line) = ω²`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_zeroHopf {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hK : m.K = 0) (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q) :
    foldCoeff m.field 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldP) =
      m.g.ρ * (m.g.Kp * (m.g.qssPower m.δ - m.g.c0)) / (2 * ω ^ 2) := by
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  have h1 := (m.coeff_fold hL hZ hK).2
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  have hD1 : 1 - m.g.Kp * m.g.Dline = ω ^ 2 / m.g.ρ := by
    rw [hω2, h1]; field_simp
  have hD : m.g.Kp * m.g.Dline ≠ 1 := by
    intro h
    rw [h, sub_self] at hD1
    exact (div_ne_zero (pow_ne_zero 2 hω.ne') hρ) hD1.symm
  rw [m.foldCoeff_fold hL hZ hD, hD1]
  field_simp

/-- **Every zero–Hopf point of the fold is decided**: for a physical model with `K = 0`,
`K_p Q = 2σ`, `ω > 0`, `ω² = a₁`, the coefficients satisfy `c = −(4σ²/ρ) a`, `a ≠ 0`, so
`a(a − c) = (1 + 4σ²/ρ) a² > 0`: `ZeroHopfDecided a b c` for every `b`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.zeroHopfDecided_zeroHopf {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hK : m.K = 0) (h2 : m.g.coeff2 m.Q = 0) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q) (b : ℝ) :
    ZeroHopfDecided (foldCoeff m.field 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldP)) b
      (zhC m.field (WithLp.toLp 2 m.foldQ) (m.critQ ω) (m.critP ω)) := by
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (pow_pos hp.1.L 2)
  have h1 := (m.coeff_fold hL hZ hK).2
  have hD : m.g.Kp * m.g.Dline ≠ 1 := by
    intro h
    rw [h, sub_self, mul_zero] at h1
    rw [h1] at hω2
    exact (pow_ne_zero 2 hω.ne') hω2
  have ha := m.foldCoeff_fold_ne_zero hp hK hD
  have hc : zhC m.field (WithLp.toLp 2 m.foldQ) (m.critQ ω) (m.critP ω) =
      -(4 * (m.g.R / m.g.L) ^ 2 / m.g.ρ) *
        foldCoeff m.field 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldP) := by
    rw [m.zhC_zeroHopf hp hK h2 hω hω2, m.foldCoeff_zeroHopf hp hK hω hω2]
    field_simp
    ring
  refine Or.inr (Or.inl ?_)
  rw [hc]
  set a := foldCoeff m.field 0 (WithLp.toLp 2 m.foldQ) (WithLp.toLp 2 m.foldP)
  have : a * (a - -(4 * (m.g.R / m.g.L) ^ 2 / m.g.ρ) * a) =
      a ^ 2 * (1 + 4 * (m.g.R / m.g.L) ^ 2 / m.g.ρ) := by ring
  rw [this]
  have : 0 < a ^ 2 := by positivity
  positivity

/-- **The zero–Hopf points of the fold are unstable**
(`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`): a balanced physical model with
`K = 0` (`a₀ = 0`), `K_p Q = 2σ` (`a₂ = 0`) and `a₁ > 0` (`det(sI − J) = s (s² + a₁)`) is
unstable: at its zero–Hopf point the coefficients satisfy `a(a − c) > 0`
(`Line.PSC.Model.zeroHopfDecided_zeroHopf`), the half axis of the centre manifold on which
`u̇ = a u²` escapes attracts its neighbours. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_zeroHopf (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h2 : m.g.coeff2 m.Q = 0) (h1 : 0 < m.g.coeff1 m.Q) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  set ω := Real.sqrt (m.g.coeff1 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h1
  have hω2 : ω ^ 2 = m.g.coeff1 m.Q := Real.sq_sqrt h1.le
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
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  have hcp := Model.isCriticalPair_crit hp hb (by rw [h2, h0, zero_mul]) hω hω2
  have hchar : (jacobianC m.field 0).charpoly = X * (X ^ 2 + C ((ω : ℂ) ^ 2)) * 1 := by
    rw [m.charpoly_fold hL hZ hK, h2, ← hω2, mul_one]
    simp
  refine Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly hF hF0
    (m.isNullPair_fold hp hK hD) (Dynamics.CenterManifold.IsCriticalPair.isCritical hcp rfl) hchar
    (fun s hs => ?_)
    (m.zeroHopfDecided_zeroHopf hp hK h2 hω hω2 _)
  simp at hs

end PSC
end powerlib.GFM.Line
