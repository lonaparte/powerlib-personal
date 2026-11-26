import theorem.GridTiedConverter.GFM.HopfLineMembership
import theorem.Dynamics.ZeroHopfReduction

/-! # The VSM on a dynamic R–L line: the zero–Hopf points of the fold

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* The zero–Hopf points of the fold: balanced physical models (`P(δ*) = P_ref`,
  `E, V, L, ω₀, M, D > 0`, `R ≥ 0`) with `K = P'(δ*) = 0` (`a₀ = 0`) and `a₃ a₂ = a₁` with
  `a₂ > 0`: `det(sI − J) = s (s + a₃)(s² + a₂)`, the eigenvalues `0, ±iω` (`ω² = a₂`) and
  `−a₃ < 0`. They force `R > 0` (`Line.VSM.Model.R_pos_of_boundary`) and
  `d(ρ − ω² − 4σ²) = 2σρ` (`d = D/M`, `σ = R/L`, `ρ = σ² + ω₀²`).
* Level: Lyapunov instability (LeanForControl's `Unstable`) of the operating point, through
  `Line.VSM.family`; exact closed forms of the normal-form coefficients `a`, `c`.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.5 and §8.7 (the
zero–Hopf normal form and its projection formulas); the generic law
`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`
(`theorem/Dynamics/ZeroHopfReduction.lean`); the null pair, the fold coefficient and the
characteristic polynomial at a fold of `theorem/GridTiedConverter/GFM/HopfLineMembership.lean`
(`Line.VSM.Model.isNullPair_fold`, `Model.foldCoeff_fold`, `Model.charpoly_fold`), the critical
pair and the second derivative of `theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean`
(`Line.VSM.Model.isCriticalPair_crit`, `Model.bilinC_field`). The coefficient `c` was derived
with exact computer algebra (SymPy, untrusted discovery) and is proved here by `field_simp` and
`linear_combination`.

Results.
* `Line.VSM.Model.pairing_bilinC_tangent`: along the tangent `q₀ = Line.VSM.Model.tangent`, the
  pairing of the second derivative with vectors of the rotated frame is
  `⟨rotC p', B(q₀, rotC q')⟩ = p̄'₁ (((P − c₀)/M) q'₀ − (E/M) q'₃) − (E/L) p̄'₂ q'₀` at every
  angle.
* **The coefficients at a zero–Hopf point**: `a = (P(δ*) − c₀)/(2(D − D_line))`
  (`Line.VSM.Model.foldCoeff_fold`), and
  `c = −d (ω₀² − σ² − ω²)(P(δ*) − c₀)/(M ω² (ω² + a₃²))` (`Line.VSM.Model.zhC_zeroHopf`), so
  `c/a = −2 d a₃ (ω₀² − σ² − ω²)/(ρ (ω² + a₃²)) < 0` (`ω₀² − σ² − ω² > 2σ²`) and
  `a(a − c) > 0` (`Line.VSM.Model.zeroHopfDecided_zeroHopf`): every zero–Hopf point of the fold
  is in the decided regime `a(a − c) > 0`; `b` is not needed and not stated.

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* **`Line.VSM.mem_den_unstable_of_zeroHopf`**: a balanced physical model with `K = 0`,
  `a₃ a₂ = a₁` and `a₂ > 0` is unstable. With `Line.VSM.mem_den_unstable_of_fold_of_ne` this
  decides every fold point with `a₁ ≠ 0`; the fold points left are the Bogdanov–Takens damping
  `D = D_line`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Complex Matrix Polynomial
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff)
open powerlib.Dynamics.CenterManifold (zhC ZeroHopfDecided)

/-- **The pairing along the tangent in the rotated frame**: at every angle,
`⟨rotC p', B(q₀, rotC q')⟩ = p̄'₁ (((P − c₀)/M) q'₀ − (E/M) q'₃) − (E/L) p̄'₂ q'₀`
(`q₀ = Line.VSM.Model.tangent`, `B` the second derivative at the operating point). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.pairing_bilinC_tangent (m : Model) (p' q' : Fin 4 → ℂ) :
    pairing (rotC m.δ p') (bilinC m.field 0 (toC (WithLp.toLp 2 m.tangent)) (rotC m.δ q')) =
      starRingEnd ℂ (p' 1) * ((((m.g.qssPower m.δ - m.g.c0) / m.g.M : ℝ) : ℂ) * q' 0 -
        ((m.g.E / m.g.M : ℝ) : ℂ) * q' 3) -
        ((m.g.E / m.g.L : ℝ) : ℂ) * starRingEnd ℂ (p' 2) * q' 0 := by
  have hcs : (Real.cos m.δ : ℂ) ^ 2 + (Real.sin m.δ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq m.δ
  rw [m.bilinC_field, pairing_apply, Fin.sum_univ_four]
  simp only [rotC, toC, Model.tangent, Network.c0, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add,
    map_sub, map_mul, Complex.conj_ofReal]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_one]
  linear_combination (-((m.g.E : ℂ) ^ 2 * (m.g.R : ℂ) * starRingEnd ℂ (p' 1) * q' 0 /
    ((m.g.M : ℂ) * (m.g.absSq : ℂ))) - (m.g.E : ℂ) * starRingEnd ℂ (p' 1) * q' 3 / (m.g.M : ℂ) -
    (m.g.E : ℂ) * starRingEnd ℂ (p' 2) * q' 0 / (m.g.L : ℂ)) * hcs

/-- **The coefficient `c` at a zero–Hopf point**: for a physical model with `K = 0`,
`a₃ a₂ = a₁` and `ω > 0`, `ω² = a₂`, Kuznetsov's `c = Re⟨p, B(q₀, q)⟩` of the tangent
`q₀ = Line.VSM.Model.tangent` and the critical pair `Line.VSM.Model.critQ`, `Model.critP` is
`c = −d (ω₀² − σ² − ω²) ((P(δ*) − c₀)/M)/(ω² (ω² + a₃²))` (`d = D/M`, `σ = R/L`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.zhC_zeroHopf {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hK : m.K = 0)
    (h32 : m.g.coeff3 * m.g.coeff2 m.Q = m.g.coeff1 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff2 m.Q) :
    zhC m.field (WithLp.toLp 2 m.tangent) (m.critQ ω) (m.critP ω) =
      -(m.g.D / m.g.M * (m.g.ω0 ^ 2 - (m.g.R / m.g.L) ^ 2 - ω ^ 2) *
        ((m.g.qssPower m.δ - m.g.c0) / m.g.M) / (ω ^ 2 * (ω ^ 2 + m.g.coeff3 ^ 2))) := by
  rw [Dynamics.CenterManifold.zhC_eq_pairing]
  have hL := hp.1.L.ne'
  have hM := hp.2.1.ne'
  obtain ⟨e3, e2, e1, e0⟩ := m.coeff_atoms hL
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hp.1.absSq_pos, hK]; simp
  unfold Model.critQ Model.critP angleZeroP
  rw [m.pairing_bilinC_tangent]
  set σ := m.g.R / m.g.L with hσ
  set w := m.g.ω0 with hw
  set a := m.g.E / m.g.M with ha
  set bb := m.g.E / m.g.L with hbb
  set d := m.g.D / m.g.M with hd
  set κ := m.Q / m.g.M with hκ
  set ν := (m.g.qssPower m.δ - m.g.c0) / m.g.M with hν
  have hR := Model.R_pos_of_boundary hp (by rw [h0, ← h32]; ring)
  have hσ0 : 0 < σ := div_pos hR hp.1.L
  have hw0 : 0 < w := hp.1.ω0
  have ha0 : 0 < a := div_pos hp.1.E hp.2.1
  have hd0 : 0 < d := div_pos hp.2.2 hp.2.1
  have hκe : κ = σ ^ 2 + w ^ 2 + 2 * σ * d - ω ^ 2 := by linarith
  have hbbe : bb = κ * (σ ^ 2 + w ^ 2) / (a * w) := by
    field_simp; linarith
  have hdd : d * (σ ^ 2 + w ^ 2 - 4 * σ ^ 2 - ω ^ 2) = 2 * σ * (σ ^ 2 + w ^ 2) := by
    rw [e3, e2, e1, hκe] at h32; rw [e2, hκe] at hω2; nlinarith
  have hΓ : σ ^ 2 + w ^ 2 - 4 * σ ^ 2 - ω ^ 2 ≠ 0 := by
    intro h; rw [h, mul_zero] at hdd
    have : 0 < 2 * σ * (σ ^ 2 + w ^ 2) := by positivity
    linarith
  have hde : d = 2 * σ * (σ ^ 2 + w ^ 2) / (σ ^ 2 + w ^ 2 - 4 * σ ^ 2 - ω ^ 2) := by
    rw [eq_div_iff hΓ]; exact hdd
  rw [e3]
  set Z := angleZeroPairing a d κ σ w ω with hZ
  set T := starRingEnd ℂ (angleZeroLeft a d σ w ω 1) * ((ν : ℂ) * angleZeroQ a d κ σ w ω 0 -
      (a : ℂ) * angleZeroQ a d κ σ w ω 3) - (bb : ℂ) * starRingEnd ℂ (angleZeroLeft a d σ w ω 2) *
      angleZeroQ a d κ σ w ω 0 with hT
  have hXT : starRingEnd ℂ ((((starRingEnd ℂ) Z)⁻¹ • angleZeroLeft a d σ w ω) 1) *
      ((ν : ℂ) * angleZeroQ a d κ σ w ω 0 - (a : ℂ) * angleZeroQ a d κ σ w ω 3) -
      (bb : ℂ) * starRingEnd ℂ ((((starRingEnd ℂ) Z)⁻¹ • angleZeroLeft a d σ w ω) 2) *
      angleZeroQ a d κ σ w ω 0 = Z⁻¹ * T := by
    simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, Complex.conj_conj]
    ring
  have hab : a * bb * w = κ * (σ ^ 2 + w ^ 2) := by linarith
  clear_value σ w a bb d κ ν
  subst hκe
  have hω0 : ω ≠ 0 := hω.ne'
  have ha3 : 0 < 2 * σ + d := by positivity
  have hZ' : Z = ((2 * a * ω ^ 2 * w : ℝ) : ℂ) * (((2 * σ + d : ℝ) : ℂ) + (ω : ℂ) * I) := by
    rw [hZ, angleZeroPairing]; push_cast; ring
  set r : ℝ := (2 * a * ω ^ 2 * w)⁻¹ * ((2 * σ + d) ^ 2 + ω ^ 2)⁻¹ with hr
  have hrp : r * (2 * a * ω ^ 2 * w) * ((2 * σ + d) ^ 2 + ω ^ 2) = 1 := by
    rw [hr]; field_simp
  clear_value r
  have hZinv : Z⁻¹ = (r : ℂ) * (((2 * σ + d : ℝ) : ℂ) - (ω : ℂ) * I) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hZ']
    have p1 : ((ω : ℂ) ^ 2).re = ω ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have p2 : ((ω : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, p1, p2]
      linear_combination hrp
    · simp [Complex.mul_re, Complex.mul_im, p1, p2]
      ring
  rw [hXT, hZinv, mul_assoc, Complex.re_ofReal_mul]
  have hRe : ((((2 * σ + d : ℝ) : ℂ) - (ω : ℂ) * I) * T).re =
      -(2 * a * w * d * (w ^ 2 - σ ^ 2 - ω ^ 2) * ν) := by
    simp only [hT, angleZeroQ, angleZeroLeft, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul,
      map_sub, map_add, map_neg, Complex.conj_ofReal, Complex.conj_I]
    simp [Complex.mul_re, Complex.mul_im, sq]
    linear_combination (-(a * (d * σ + ω ^ 2 + 2 * σ ^ 2))) * hab +
      (a * (d * ω ^ 2 + ν * w + ω ^ 2 * σ)) * hdd
  rw [hRe]
  have hr' : r = 1 / ((2 * a * ω ^ 2 * w) * ((2 * σ + d) ^ 2 + ω ^ 2)) := by
    rw [eq_div_iff (by positivity)]; linear_combination hrp
  rw [hr']
  field_simp
  ring

/-- **Every zero–Hopf point of the fold is decided**: for a physical model with `K = 0`,
`a₃ a₂ = a₁`, `ω > 0`, `ω² = a₂`, the coefficients satisfy `c = −λ a` with
`λ = 2 d a₃ (ω₀² − σ² − ω²)/(ρ (ω² + a₃²)) > 0` (the relation `d (ρ − ω² − 4σ²) = 2σρ` gives
`ω₀² − σ² − ω² > 2σ²`) and `a ≠ 0`, so `a(a − c) = (1 + λ) a² > 0`: `ZeroHopfDecided a b c` for
every `b`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.zeroHopfDecided_zeroHopf {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hK : m.K = 0)
    (h32 : m.g.coeff3 * m.g.coeff2 m.Q = m.g.coeff1 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff2 m.Q) (b : ℝ) :
    ZeroHopfDecided (foldCoeff m.field 0 (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.foldP)) b
      (zhC m.field (WithLp.toLp 2 m.tangent) (m.critQ ω) (m.critP ω)) := by
  have hL := hp.1.L.ne'
  have hM := hp.2.1
  have hZ := hp.1.absSq_pos
  obtain ⟨e3, e2, e1, e0⟩ := m.coeff_atoms hL
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  have hR := Model.R_pos_of_boundary hp (by rw [h0, ← h32]; ring)
  have hσ0 : 0 < m.g.R / m.g.L := div_pos hR hp.1.L
  have hd0 : 0 < m.g.D / m.g.M := div_pos hp.2.2 hM
  have ha3 : 0 < m.g.coeff3 := by rw [e3]; positivity
  have hρ : m.g.ρ = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 := by
    simp only [Network.ρ, Network.σ, Network.X]; field_simp
  have hρ0 : 0 < m.g.ρ := by rw [hρ]; positivity
  -- `D − D_line = M a₃ ω²/ρ`
  have h1 := m.coeff1_eq hL hZ
  rw [hK, mul_zero, add_zero] at h1
  have hDD : m.g.D - m.g.Dline = m.g.M * m.g.coeff3 * ω ^ 2 / m.g.ρ := by
    rw [eq_div_iff hρ0.ne', hω2, mul_assoc, h32, h1]; field_simp
  have hD : m.g.D ≠ m.g.Dline := by
    intro h; rw [h, sub_self] at hDD
    have : 0 < m.g.M * m.g.coeff3 * ω ^ 2 / m.g.ρ := by positivity
    linarith
  -- `ω₀² − σ² − ω² > 0`
  have hκe : m.Q / m.g.M = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 +
      2 * (m.g.R / m.g.L) * (m.g.D / m.g.M) - ω ^ 2 := by linarith
  have hdd : m.g.D / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - 4 * (m.g.R / m.g.L) ^ 2 -
      ω ^ 2) = 2 * (m.g.R / m.g.L) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) := by
    rw [e3, e2, e1, hκe] at h32; rw [e2, hκe] at hω2; nlinarith
  have hgap : 0 < m.g.ω0 ^ 2 - (m.g.R / m.g.L) ^ 2 - ω ^ 2 := by
    have hpos : 0 < 2 * (m.g.R / m.g.L) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) := by positivity
    have : 0 < (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - 4 * (m.g.R / m.g.L) ^ 2 - ω ^ 2 := by
      by_contra hn
      push Not at hn
      have := mul_nonpos_of_nonneg_of_nonpos hd0.le hn
      linarith
    nlinarith [sq_nonneg (m.g.R / m.g.L)]
  have hν := Model.qssPower_sub_c0_ne_zero_of_fold hp hK
  set a := foldCoeff m.field 0 (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.foldP) with ha
  have hae : a = (m.g.qssPower m.δ - m.g.c0) / (2 * (m.g.D - m.g.Dline)) :=
    m.foldCoeff_fold hM.ne' hL hZ hD
  set lam := 2 * (m.g.D / m.g.M) * m.g.coeff3 * (m.g.ω0 ^ 2 - (m.g.R / m.g.L) ^ 2 - ω ^ 2) /
    (m.g.ρ * (ω ^ 2 + m.g.coeff3 ^ 2)) with hlam
  have hlam0 : 0 < lam := by positivity
  have hc : zhC m.field (WithLp.toLp 2 m.tangent) (m.critQ ω) (m.critP ω) = -lam * a := by
    rw [m.zhC_zeroHopf hp hK h32 hω hω2, hae, hDD, hlam]
    field_simp
  have ha0 : a ≠ 0 := by
    rw [hae]; exact div_ne_zero hν (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hD))
  refine Or.inr (Or.inl ?_)
  rw [hc]
  have : a * (a - -lam * a) = a ^ 2 * (1 + lam) := by ring
  rw [this]
  have : 0 < a ^ 2 := by positivity
  positivity

/-- **The zero–Hopf points of the fold are unstable**
(`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`): a balanced physical model with
`K = 0` (`a₀ = 0`), `a₃ a₂ = a₁` and `a₂ > 0` (`det(sI − J) = s (s² + a₂)(s + a₃)`) is unstable:
at its zero–Hopf point the coefficients satisfy `a(a − c) > 0`
(`Line.VSM.Model.zeroHopfDecided_zeroHopf`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_zeroHopf (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h32 : m.g.coeff3 * m.g.coeff2 m.Q = m.g.coeff1 m.Q) (h2 : 0 < m.g.coeff2 m.Q) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  have hL := hp.1.L.ne'
  have hZ := hp.1.absSq_pos
  obtain ⟨e3, -, -, -⟩ := m.coeff_atoms hL
  have ha3 : 0 < m.g.coeff3 := by
    rw [e3]
    exact add_pos_of_nonneg_of_pos (by have := div_nonneg hp.1.R hp.1.L.le; linarith)
      (div_pos hp.2.2 hp.2.1)
  set ω := Real.sqrt (m.g.coeff2 m.Q) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr h2
  have hω2 : ω ^ 2 = m.g.coeff2 m.Q := Real.sq_sqrt h2.le
  have hF : ContDiff ℝ 2 m.field := (m.g.contDiff_field (k := 2)).comp
    (contDiff_id.add contDiff_const)
  have hF0 : m.field 0 = 0 := by
    show m.g.field (0 + m.point) = 0
    rw [zero_add]
    exact (m.field_point_eq_zero_iff hp.2.1.ne' hL hZ.ne').mpr hb
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  have hcp := Model.isCriticalPair_crit hp hb (by rw [h0, ← h32]; ring) hω
    (by rw [hω2, ← h32]; field_simp)
  -- `D ≠ D_line`
  have h1 := m.coeff1_eq hL hZ
  rw [hK, mul_zero, add_zero] at h1
  have hD : m.g.D ≠ m.g.Dline := by
    intro h
    rw [h, sub_self, mul_zero, zero_div] at h1
    have : 0 < m.g.coeff3 * m.g.coeff2 m.Q := mul_pos ha3 h2
    linarith
  have hchar : (jacobianC m.field 0).charpoly =
      X * (X ^ 2 + C ((ω : ℂ) ^ 2)) * (X + C ((m.g.coeff3 : ℝ) : ℂ)) := by
    rw [m.charpoly_fold hL hZ hK, ← h32, ← hω2]
    push_cast
    simp only [map_mul, map_pow]
    ring
  refine Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly hF hF0
    (m.isNullPair_fold hp hK hD) (Dynamics.CenterManifold.IsCriticalPair.isCritical hcp rfl)
    hchar (fun s hs => ?_) (m.zeroHopfDecided_zeroHopf hp hK h32 hω hω2 _)
  rw [eval_add, eval_X, eval_C] at hs
  have : s = -((m.g.coeff3 : ℝ) : ℂ) := by linear_combination hs
  rw [this]
  simpa using ha3

end VSM
end powerlib.GFM.Line
