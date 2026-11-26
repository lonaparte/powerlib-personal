import theorem.GridTiedConverter.GFM.Line.VSM
import theorem.SpecialFunctions.PolynomialSigns

/-! # The VSM on a dynamic R–L line: the Bogdanov–Takens point at the line damping and its unfolding

Static linear algebra of the four-state VSM on a dynamic line at its operating point.

Model boundary.
The four-state model `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
state `(δ, ω, i_d, i_q)`, grid dq frame at `ω₀`, `δ̇ = ω`, `M ω̇ = P_ref − P_e − D ω`,
`L i̇ = E e^{jδ} − V − (R + jX) i`, export-positive active power, constant `E`; no voltage loop,
inner loops, LC filter, limiting, PLL, delay or PWM. A model `Line.VSM.Model` is read at its
operating point `(δ*, 0, i_s(δ*))`; `K = A cos(δ* − α) = P'(δ*)`, `Q = Q(δ*)`, `κ = K + Q =
E² X/|Z|²`, `D_line = 2 E² R X L/|Z|⁴` (`Line.Network.Dline`). Statements are about the Jacobian
`Line.VSM.Model.jac` (from `fderiv`, `Line.VSM.Model.fderiv_point`), not about the nonlinear flow:
the unfolding is the linear one, in the parameter plane of the synchronizing coefficient (or
the angle `δ*`) and the damping, with the network and the inertia fixed — the fold line, the
Hopf curve and the regularity of the two lowest coefficients. Elsewhere: the normal form on the
centre manifold at the Bogdanov–Takens point,
`theorem/GridTiedConverter/GFM/BTCoefficientLine.lean`
(`Line.VSM.Model.exists_centerManifold_btNormalForm_of_bt`); Kuznetsov's nondegeneracy condition
(BT.3) for the unfolding in `(P_ref, D)`, the regularity of the map
`(x, P_ref, D) ↦ (f, a₀, a₁)` with determinant `−ρ³(P(δ*) − c₀)/M³`,
`theorem/GridTiedConverter/GFM/BTTransversality.lean` (`Line.VSM.Model.bijective_fderiv_btMap`);
the homoclinic orbit of the rescaled normal form and the homoclinic curve to leading order
(`β₁ = −(6/25) β₂²/a`), `theorem/Dynamics/BTUnfolding.lean`. Not proved: the persistence of the
homoclinic orbit for this model (it needs invariant manifolds of the saddle with parameters, the
Melnikov splitting expansion and the parameter-dependent centre-manifold reduction), the phase
portraits.

Source: GFM counterpart study, note t3-bifurcation (b) (the BT point of the dynamic line at
`D_BT = 2 E² R X²/(ω_b |Z|⁴)`, `ω_b = X/L = ω₀`, i.e. `D_BT = D_line`; scripts s2b, s2c, derived
and checked numerically there; scratch notes outside the repository); the characteristic
polynomial and the line damping of `theorem/GridTiedConverter/GFM/Line/VSM.lean`
(`Line.VSM.Model.coeff0_eq`, `Line.VSM.Model.coeff1_eq`); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed., 2004), §8.4 (a Bogdanov–Takens point is a double zero eigenvalue
with a single Jordan block; its fold and Hopf curves); Arnold, *Geometrical Methods in the Theory
of Ordinary Differential Equations* (1983), §30 (versal deformations of a Jordan block). The Hopf
curve was solved with SymPy (exact, untrusted) and is proved here by `linear_combination`.

Results.
* `Line.VSM.charpoly_jacobian`: the characteristic polynomial of the Jacobian at every state is
  the quartic `s⁴ + a₃ s³ + a₂(Q_e) s² + a₁(Q_e) s + a₀(Q_e)` of
  `Line.VSM.det_characteristicMatrix`; at the operating point `Line.VSM.Model.charpoly_jac`.
* `Line.VSM.Model.two_le_rootMultiplicity_zero_iff`: the eigenvalue `0` is (at least) double
  exactly at a fold `K = 0` with the damping `D = D_line` (`a₀ = ρK/M`, `a₁ = (ρ(D − D_line) +
  2σK)/M`; the two-lowest-coefficients law `SpecialFunctions.two_le_rootMultiplicity_zero_iff`).
  On a lossless line `D_line = 0`, so a damped model (`D > 0`) never has a double zero
  eigenvalue; on a lossy line (`R > 0`, `E, X, L > 0`) `D_line > 0`
  (`Line.Network.Dline_pos`): the Bogdanov–Takens point lies at a physical damping, unlike the
  quasi-static model (`VSMLPF.rootMultiplicity_zero_le_one`,
  `swing_rootMultiplicity_zero_le_one` in `theorem/GridTiedConverter/GFM/Bifurcation.lean`).
* Jordan structure. With the tangent of the quasi-steady set `q₀ = (1, 0, i_s'(δ*))`
  (`Line.VSM.Model.tangent`) and `q₁ = (0, 1, w)`, `w` the line currents solving the line rows
  for `q₀` (`Line.VSM.Model.chain`), at every angle
  `J q₀ = −(K/M) e_ω` (`Line.VSM.Model.jac_mulVec_tangent`) and
  `J q₁ = q₀ + ((D_line − D)/M) e_ω` (`Line.VSM.Model.jac_mulVec_chain`); every null vector is a
  multiple of `q₀` (`Line.VSM.Model.eq_smul_tangent_of_mulVec_eq_zero`). At `K = 0`,
  `D = D_line` the eigenvalue `0` therefore has the Jordan chain `J q₁ = q₀ ≠ 0`, `J q₀ = 0` and a
  one-dimensional kernel: a single Jordan block (`Line.VSM.Model.jordan_chain_of_bt`).
* **The unfolding** (network and inertia fixed, `M, L, R ≠ 0`, `|Z|² > 0`):
  the fold line — `0` is an eigenvalue iff `K = 0`
  (`Line.VSM.Model.det_characteristicMatrix_zero_eq_zero_iff`); the Hopf curve — `iω`, `ω > 0`,
  is an eigenvalue iff `(K, D) = (K_H(ω), D_H(ω))` (`Line.VSM.hopfK`, `Line.VSM.hopfD`, rational
  in `ω²`: Cramer's rule for `a₁ = a₃ω²`, `a₀ = ω²(a₂ − ω²)`, which are linear in `(K, D)`;
  `Line.VSM.Model.det_characteristicMatrix_I_eq_zero_iff`); the Hopf curve ends at the
  Bogdanov–Takens point, `(K_H(ω), D_H(ω)) → (0, D_line)` as `ω → 0`
  (`Line.VSM.tendsto_hopf_bt`), with the tangent `K_H(ω)/ω² → n = M + E² L² X (3R² − X²)/|Z|⁶`
  (`Line.VSM.tendsto_hopfK_div_sq`; `n` is the effective inertia `Line.VSM.btInertia` of
  `theorem/GridTiedConverter/GFM/BTCoefficientLine.lean`): near the Bogdanov–Takens point the Hopf
  frequency is `ω² ≈ K/n`, so for `n > 0` the Hopf curve leaves it into the synchronizing side
  `K > 0`.
* Linear versality: the map `(δ*, D) ↦ (a₀, a₁)` (`Line.VSM.unfoldingMap`,
  `Line.VSM.unfoldingMap_eq`) has the derivative `(u, v) ↦ (ρK'u/M, (2σK'u + ρv)/M)`,
  `K' = −A sin(δ* − α) = P''(δ*)` (`Line.VSM.hasFDerivAt_unfoldingMap`), injective at a fold
  with `A ≠ 0` (`Line.VSM.unfolding_derivative_injective`): the two lowest coefficients are
  regular coordinates of the parameter plane at the Bogdanov–Takens point.
-/

noncomputable section
namespace powerlib.GFM.Line
open Polynomial Matrix
open Filter Topology

namespace Network

variable (N : Network)

/-- On a lossy line the line damping is positive: `R, E, X, L > 0` ⇒ `D_line > 0`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Dline_pos (hR : 0 < N.R) (hE : N.E ≠ 0) (hX : 0 < N.X)
    (hL : 0 < N.L) : 0 < N.Dline := by
  have hZ : 0 < N.absSq := by unfold absSq; positivity
  unfold Dline
  positivity

end Network

namespace VSM

/-- The tangent `(1, 0, i_s'(δ*))` of the quasi-steady set at the operating point,
`i_s'(δ) = j E e^{jδ}/(R + jX)`. -/
def Model.tangent (m : Model) : Fin 4 → ℝ :=
  ![1, 0, m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq,
    m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq]

/-- The second vector of the Jordan chain, `(0, 1, w_d, w_q)` with the line rows solved for the
tangent: `|Z|² w_d = −L (R t_d + X t_q)`, `|Z|² w_q = L (X t_d − R t_q)`. -/
def Model.chain (m : Model) : Fin 4 → ℝ :=
  ![0, 1, -(m.g.L * (m.g.R * m.tangent 2 + m.g.X * m.tangent 3)) / m.g.absSq,
    m.g.L * (m.g.X * m.tangent 2 - m.g.R * m.tangent 3) / m.g.absSq]

/-- The characteristic polynomial of the Jacobian at every state,
`s⁴ + a₃ s³ + a₂(Q_e) s² + a₁(Q_e) s + a₀(Q_e)` (`VSM.det_characteristicMatrix`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem charpoly_jacobian (g : VSM) (δ id iq : ℝ) :
    (g.jacobian δ id iq).charpoly = X ^ 4 + C g.coeff3 * X ^ 3 +
      C (g.coeff2 (g.reactive δ id iq)) * X ^ 2 + C (g.coeff1 (g.reactive δ id iq)) * X +
        C (g.coeff0 (g.reactive δ id iq)) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  apply Polynomial.funext
  intro s
  rw [← Matrix.charpoly_map, ← Linear.det_characteristicMatrix_eq_eval,
    g.det_characteristicMatrix]
  simp

/-- The characteristic polynomial of the Jacobian at the operating point.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_jac (m : Model) :
    m.jac.charpoly = X ^ 4 + C m.g.coeff3 * X ^ 3 + C (m.g.coeff2 m.Q) * X ^ 2 +
      C (m.g.coeff1 m.Q) * X + C (m.g.coeff0 m.Q) :=
  m.g.charpoly_jacobian _ _ _

/-- **The double zero eigenvalue of the dynamic line.** For `M, L ≠ 0` and `|Z|² > 0` the
eigenvalue `0` of the Jacobian at the operating point has algebraic multiplicity at least two
exactly at a fold `K = 0` with the damping `D = D_line = 2 E² R X L/|Z|⁴`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.two_le_rootMultiplicity_zero_iff (m : Model)
    (hM : m.g.M ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    2 ≤ m.jac.charpoly.rootMultiplicity 0 ↔ m.K = 0 ∧ m.g.D = m.g.Dline := by
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  rw [SpecialFunctions.two_le_rootMultiplicity_zero_iff (charpoly_monic _).ne_zero,
    m.charpoly_jac]
  simp [coeff_X, coeff_C]
  rw [m.coeff1_eq hL hZ, m.coeff0_eq hL hZ]
  constructor
  · rintro ⟨h1, h0⟩
    have hK : m.K = 0 := by
      rw [div_eq_zero_iff, or_iff_left hM, mul_eq_zero, or_iff_right hρ] at h0
      exact h0
    refine ⟨hK, ?_⟩
    rw [hK, mul_zero, add_zero, div_eq_zero_iff, or_iff_left hM, mul_eq_zero,
      or_iff_right hρ, sub_eq_zero] at h1
    exact h1
  · rintro ⟨hK, hD⟩
    rw [hK, hD]
    simp

/-- The tangent is mapped to `−(K/M) e_ω`: it is a null vector exactly at a fold.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.jac_mulVec_tangent (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    m.jac *ᵥ m.tangent = ![0, -(m.K / m.g.M), 0, 0] := by
  have hQ : m.Q = m.g.κ - m.K := by
    have := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [Model.Q, Model.K]; linarith
  have hZ' : m.g.absSq ≠ 0 := hZ.ne'
  have hc := Real.sin_sq_add_cos_sq m.δ
  have hreac : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.Q := rfl
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  funext i
  fin_cases i
  · simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Model.tangent]
  · simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Model.tangent,
      hreac, hQ, Network.κ]
    field_simp
    linear_combination (-(m.g.E ^ 2 * m.g.X)) * hc
  · simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Model.tangent]
    field_simp
    rw [habs]
    ring
  · simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Model.tangent]
    field_simp
    rw [habs]
    ring

/-- The line rows of `J v` (`L` times the line rates of the linearization). -/
@[tmio M, powerlib_domain] private theorem jac_mulVec_two (m : Model) (v : Fin 4 → ℝ) :
    (m.jac *ᵥ v) 2 = (-(m.g.E * Real.sin m.δ) * v 0 - m.g.R * v 2 + m.g.X * v 3) / m.g.L := by
  simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

@[tmio M, powerlib_domain] private theorem jac_mulVec_three (m : Model) (v : Fin 4 → ℝ) :
    (m.jac *ᵥ v) 3 = (m.g.E * Real.cos m.δ * v 0 - m.g.X * v 2 - m.g.R * v 3) / m.g.L := by
  simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

@[tmio M, powerlib_domain] private theorem jac_mulVec_one (m : Model) (v : Fin 4 → ℝ) :
    (m.jac *ᵥ v) 1 = (m.Q * v 0 - m.g.D * v 1 - m.g.E * Real.cos m.δ * v 2 -
      m.g.E * Real.sin m.δ * v 3) / m.g.M := by
  have hreac : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.Q := rfl
  simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hreac]
  ring

/-- The second Jordan vector: `J q₁ = q₀ + ((D_line − D)/M) e_ω` at every angle.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.jac_mulVec_chain (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    m.jac *ᵥ m.chain = m.tangent + ![0, (m.g.Dline - m.g.D) / m.g.M, 0, 0] := by
  have hZ' : m.g.absSq ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  have hc := Real.sin_sq_add_cos_sq m.δ
  have t2 : m.tangent 2 =
      m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq := rfl
  have t3 : m.tangent 3 =
      m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq := rfl
  have w0 : m.chain 0 = 0 := rfl
  have w1 : m.chain 1 = 1 := rfl
  have w2 : m.chain 2 =
      -(m.g.L * (m.g.R * m.tangent 2 + m.g.X * m.tangent 3)) / m.g.absSq := rfl
  have w3 : m.chain 3 = m.g.L * (m.g.X * m.tangent 2 - m.g.R * m.tangent 3) / m.g.absSq := rfl
  funext i
  fin_cases i
  · simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Model.chain,
      Model.tangent]
  · have e := jac_mulVec_one m m.chain
    have hrow : m.g.E * Real.cos m.δ * m.chain 2 + m.g.E * Real.sin m.δ * m.chain 3 =
        -m.g.Dline := by
      have e1 : m.g.E * Real.cos m.δ * m.chain 2 + m.g.E * Real.sin m.δ * m.chain 3 =
          -(2 * m.g.E ^ 2 * m.g.R * m.g.X * m.g.L *
            (Real.sin m.δ ^ 2 + Real.cos m.δ ^ 2) / m.g.absSq ^ 2) := by
        rw [w2, w3, t2, t3]
        field_simp
        ring
      rw [e1, hc, Network.Dline]
      ring
    show (m.jac *ᵥ m.chain) 1 = m.tangent 1 + (m.g.Dline - m.g.D) / m.g.M
    rw [e, w0, w1]
    have t1 : m.tangent 1 = 0 := rfl
    rw [t1]
    field_simp
    linear_combination (-1 : ℝ) * hrow
  · show (m.jac *ᵥ m.chain) 2 = m.tangent 2 + 0
    rw [jac_mulVec_two, w0, w2, w3, add_zero]
    field_simp
    rw [habs]
    ring
  · show (m.jac *ᵥ m.chain) 3 = m.tangent 3 + 0
    rw [jac_mulVec_three, w0, w2, w3, add_zero]
    field_simp
    rw [habs]
    ring

/-- **The kernel is at most one-dimensional**: every null vector of the Jacobian is a multiple of
the tangent `q₀` (the line rows determine the currents, the angle row the speed).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.eq_smul_tangent_of_mulVec_eq_zero (m : Model)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) {v : Fin 4 → ℝ} (hv : m.jac *ᵥ v = 0) :
    v = v 0 • m.tangent := by
  have hZ' : m.g.absSq ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  have h0 : (m.jac *ᵥ v) 0 = 0 := by rw [hv]; rfl
  have h2 : (m.jac *ᵥ v) 2 = 0 := by rw [hv]; rfl
  have h3 : (m.jac *ᵥ v) 3 = 0 := by rw [hv]; rfl
  have e0 : (m.jac *ᵥ v) 0 = v 1 := by
    simp [Model.jac, VSM.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [e0] at h0
  rw [jac_mulVec_two, div_eq_zero_iff, or_iff_left hL] at h2
  rw [jac_mulVec_three, div_eq_zero_iff, or_iff_left hL] at h3
  funext i
  fin_cases i
  · simp [Model.tangent]
  · simp [Model.tangent, h0]
  · show v 2 = v 0 * (m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq)
    field_simp
    rw [habs]
    linear_combination (-m.g.R) * h2 + (-m.g.X) * h3
  · show v 3 = v 0 * (m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq)
    field_simp
    rw [habs]
    linear_combination m.g.X * h2 + (-m.g.R) * h3

/-- **The Bogdanov–Takens Jordan block.** At a fold (`K = 0`) with the damping `D = D_line`
the eigenvalue `0` of the Jacobian has the Jordan chain `J q₁ = q₀ ≠ 0`, `J q₀ = 0`, and every
null vector is a multiple of `q₀`: a double zero eigenvalue
(`Model.two_le_rootMultiplicity_zero_iff`) with a single Jordan block.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.jordan_chain_of_bt (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hK : m.K = 0) (hD : m.g.D = m.g.Dline) :
    m.jac *ᵥ m.tangent = 0 ∧ m.jac *ᵥ m.chain = m.tangent ∧ m.tangent ≠ 0 ∧
      ∀ v, m.jac *ᵥ v = 0 → v = v 0 • m.tangent := by
  refine ⟨?_, ?_, ?_, fun v hv => m.eq_smul_tangent_of_mulVec_eq_zero hL hZ hv⟩
  · rw [m.jac_mulVec_tangent hM hL hZ, hK, zero_div, neg_zero]
    funext i
    fin_cases i <;> rfl
  · rw [m.jac_mulVec_chain hM hL hZ, hD, sub_self, zero_div]
    funext i
    fin_cases i <;> simp
  · intro h
    have := congrFun h 0
    simp [Model.tangent] at this

/-! ## The unfolding of the Bogdanov–Takens point -/

/-- **The synchronizing coefficient of the Hopf curve** at frequency `ω` (`w = ω²`):
`K_H = (2σw(2σκ + 2σMw) + (ρ − w)w(M(ρ − w) − κ))/(4σ²w + (ρ − w)²)`. -/
def hopfK (g : VSM) (ω : ℝ) : ℝ :=
  (2 * g.σ * ω ^ 2 * (2 * g.σ * g.κ + 2 * g.σ * g.M * ω ^ 2) +
      (g.ρ - ω ^ 2) * ω ^ 2 * (g.M * (g.ρ - ω ^ 2) - g.κ)) /
    (4 * g.σ ^ 2 * ω ^ 2 + (g.ρ - ω ^ 2) ^ 2)

/-- **The damping of the Hopf curve** at frequency `ω` (`w = ω²`):
`D_H = ((ρ − w)(2σκ + 2σMw) − 2σw(M(ρ − w) − κ))/(4σ²w + (ρ − w)²)`. -/
def hopfD (g : VSM) (ω : ℝ) : ℝ :=
  ((g.ρ - ω ^ 2) * (2 * g.σ * g.κ + 2 * g.σ * g.M * ω ^ 2) -
      2 * g.σ * ω ^ 2 * (g.M * (g.ρ - ω ^ 2) - g.κ)) /
    (4 * g.σ ^ 2 * ω ^ 2 + (g.ρ - ω ^ 2) ^ 2)

/-- The characteristic determinant at `iω` through its real and imaginary parts. -/
@[tmio M, powerlib_domain] private theorem charDet_I (m : Model) (ω : ℝ) :
    (Linear.characteristicMatrix m.jac ((ω : ℂ) * Complex.I)).det =
      ((ω ^ 4 - m.g.coeff2 m.Q * ω ^ 2 + m.g.coeff0 m.Q : ℝ) : ℂ) +
        ((ω * (m.g.coeff1 m.Q - m.g.coeff3 * ω ^ 2) : ℝ) : ℂ) * Complex.I := by
  rw [m.det_characteristicMatrix]
  push_cast
  ring_nf
  rw [Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring,
    show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; ring]
  ring

/-- Cramer's rule for the two linear equations of the Hopf curve. -/
@[tmio T, powerlib_foundation] private theorem hopf_cramer {s ρ κ M w K D : ℝ}
    (hΔ : 4 * s ^ 2 * w + (ρ - w) ^ 2 ≠ 0) :
    (2 * s * K + (ρ - w) * D - (2 * s * M * w + 2 * s * κ) = 0 ∧
        (ρ - w) * K - 2 * s * w * D - w * (M * (ρ - w) - κ) = 0) ↔
      (K = (2 * s * w * (2 * s * κ + 2 * s * M * w) + (ρ - w) * w * (M * (ρ - w) - κ)) /
          (4 * s ^ 2 * w + (ρ - w) ^ 2) ∧
        D = ((ρ - w) * (2 * s * κ + 2 * s * M * w) - 2 * s * w * (M * (ρ - w) - κ)) /
          (4 * s ^ 2 * w + (ρ - w) ^ 2)) := by
  constructor
  · rintro ⟨e1, e2⟩
    constructor
    · rw [eq_div_iff hΔ]; linear_combination 2 * s * w * e1 + (ρ - w) * e2
    · rw [eq_div_iff hΔ]; linear_combination (ρ - w) * e1 - 2 * s * e2
  · rintro ⟨eK, eD⟩
    have hK : K * (4 * s ^ 2 * w + (ρ - w) ^ 2) =
        2 * s * w * (2 * s * κ + 2 * s * M * w) + (ρ - w) * w * (M * (ρ - w) - κ) := by
      rw [eK, div_mul_cancel₀ _ hΔ]
    have hD : D * (4 * s ^ 2 * w + (ρ - w) ^ 2) =
        (ρ - w) * (2 * s * κ + 2 * s * M * w) - 2 * s * w * (M * (ρ - w) - κ) := by
      rw [eD, div_mul_cancel₀ _ hΔ]
    constructor
    · apply mul_right_cancel₀ hΔ
      linear_combination 2 * s * hK + (ρ - w) * hD
    · apply mul_right_cancel₀ hΔ
      linear_combination (ρ - w) * hK - 2 * s * w * hD

/-- **The fold line.** The eigenvalue `0` occurs exactly at a fold `K = 0` (`M ≠ 0`, `L ≠ 0`,
`|Z|² > 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix_zero_eq_zero_iff (m : Model)
    (hM : m.g.M ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    (Linear.characteristicMatrix m.jac 0).det = 0 ↔ m.K = 0 := by
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  rw [m.det_characteristicMatrix, m.coeff0_eq hL hZ]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    zero_add, Complex.ofReal_eq_zero, div_eq_zero_iff, mul_eq_zero, hρ, hM, false_or, or_false]

/-- **The Hopf curve.** For `M, L, R ≠ 0` and `|Z|² > 0` (so `σ ≠ 0`), the Jacobian at the
operating point has the eigenvalue `iω`, `ω > 0`, exactly when `(K, D) = (K_H(ω), D_H(ω))`
(`hopfK`, `hopfD`): the curve of Hopf points in the plane of the synchronizing coefficient and
the damping is the rational curve `ω ↦ (K_H(ω), D_H(ω))`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.det_characteristicMatrix_I_eq_zero_iff (m : Model)
    (hM : m.g.M ≠ 0) (hL : m.g.L ≠ 0) (hR : m.g.R ≠ 0) (hZ : 0 < m.g.absSq) {ω : ℝ}
    (hω : 0 < ω) :
    (Linear.characteristicMatrix m.jac ((ω : ℂ) * Complex.I)).det = 0 ↔
      m.K = hopfK m.g ω ∧ m.g.D = hopfD m.g ω := by
  have hσ : m.g.σ ≠ 0 := div_ne_zero hR hL
  have hQ : m.Q = m.g.κ - m.K := by
    have h := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [Model.Q, Model.K] at *; linarith
  have h0 := m.coeff0_eq hL hZ
  have hΔ : 0 < 4 * m.g.σ ^ 2 * ω ^ 2 + (m.g.ρ - ω ^ 2) ^ 2 := by
    have : 0 < 4 * m.g.σ ^ 2 * ω ^ 2 := by positivity
    positivity
  rw [charDet_I, Complex.ext_iff]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im]
  simp only [mul_zero, mul_one, sub_zero, zero_add, add_zero]
  rw [h0, coeff3, coeff2, coeff1, hQ]
  set K := m.K
  set D := m.g.D
  set s := m.g.σ
  set ρ := m.g.ρ
  set κ := m.g.κ
  set M := m.g.M
  -- the two linear equations in `(K, D)`
  have key : (ω ^ 4 - (ρ + (2 * s * D - (κ - K)) / M) * ω ^ 2 + ρ * K / M = 0 ∧
        ω * ((D * ρ - 2 * s * (κ - K)) / M - (2 * s + D / M) * ω ^ 2) = 0) ↔
      (2 * s * K + (ρ - ω ^ 2) * D - (2 * s * M * ω ^ 2 + 2 * s * κ) = 0 ∧
        (ρ - ω ^ 2) * K - 2 * s * ω ^ 2 * D - ω ^ 2 * (M * (ρ - ω ^ 2) - κ) = 0) := by
    constructor
    · rintro ⟨e2, e1⟩
      have e1' : (D * ρ - 2 * s * (κ - K)) / M - (2 * s + D / M) * ω ^ 2 = 0 :=
        (mul_eq_zero.mp e1).resolve_left hω.ne'
      constructor
      · field_simp at e1'; linear_combination e1'
      · field_simp at e2; linear_combination e2
    · rintro ⟨e1, e2⟩
      constructor
      · field_simp; linear_combination e2
      · field_simp; linear_combination ω * e1
  rw [key, hopfK, hopfD]
  exact hopf_cramer (w := ω ^ 2) hΔ.ne'

/-- **The Hopf curve ends at the Bogdanov–Takens point**: as `ω → 0`,
`(K_H(ω), D_H(ω)) → (0, D_line)` (`L ≠ 0`, `|Z|² > 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem tendsto_hopf_bt (g : VSM) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) :
    Tendsto (fun ω => (hopfK g ω, hopfD g ω)) (𝓝 0) (𝓝 (0, g.Dline)) := by
  have hρ : g.ρ ≠ 0 := by
    have : g.ρ = g.absSq / g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  have hden : (4 * g.σ ^ 2 * (0:ℝ) ^ 2 + (g.ρ - (0:ℝ) ^ 2) ^ 2) ≠ 0 := by simpa using hρ
  have hcK : ContinuousAt (hopfK g) 0 := by
    unfold hopfK; exact (by fun_prop : Continuous _).continuousAt.div
      (by fun_prop : Continuous _).continuousAt hden
  have hcD : ContinuousAt (hopfD g) 0 := by
    unfold hopfD; exact (by fun_prop : Continuous _).continuousAt.div
      (by fun_prop : Continuous _).continuousAt hden
  have hK0 : hopfK g 0 = 0 := by simp [hopfK]
  have hD0 : hopfD g 0 = g.Dline := by
    rw [g.Dline_eq hL hZ.ne', hopfD]; field_simp; ring
  have := hcK.tendsto.prodMk_nhds hcD.tendsto
  rwa [hK0, hD0] at this

/-- **The tangent of the Hopf curve at the Bogdanov–Takens point**: `K_H(ω)/ω² → n` as `ω → 0`
(`ω ≠ 0`), `n = M + E² L² X (3R² − X²)/|Z|⁶` the effective inertia of
`theorem/GridTiedConverter/GFM/BTCoefficientLine.lean` (`Line.VSM.btInertia`): near the
Bogdanov–Takens point the Hopf frequency is `ω² ≈ K/n`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem tendsto_hopfK_div_sq (g : VSM) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) :
    Tendsto (fun ω => hopfK g ω / ω ^ 2) (𝓝[≠] 0)
      (𝓝 (g.M + g.E ^ 2 * g.L ^ 2 * g.X * (3 * g.R ^ 2 - g.X ^ 2) / g.absSq ^ 3)) := by
  have hρ : g.ρ ≠ 0 := by
    have : g.ρ = g.absSq / g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  set F : ℝ → ℝ := fun ω => (2 * g.σ * (2 * g.σ * g.κ + 2 * g.σ * g.M * ω ^ 2) +
      (g.ρ - ω ^ 2) * (g.M * (g.ρ - ω ^ 2) - g.κ)) /
    (4 * g.σ ^ 2 * ω ^ 2 + (g.ρ - ω ^ 2) ^ 2) with hF
  have hden : (4 * g.σ ^ 2 * (0:ℝ) ^ 2 + (g.ρ - (0:ℝ) ^ 2) ^ 2) ≠ 0 := by simpa using hρ
  have hc : ContinuousAt F 0 := by
    rw [hF]; exact (by fun_prop : Continuous _).continuousAt.div
      (by fun_prop : Continuous _).continuousAt hden
  have hF0 : F 0 = g.M + g.E ^ 2 * g.L ^ 2 * g.X * (3 * g.R ^ 2 - g.X ^ 2) / g.absSq ^ 3 := by
    rw [hF]
    simp only [Network.σ, Network.ρ, Network.κ, Network.absSq] at hZ ⊢
    have hX : g.X = g.ω0 * g.L := rfl
    field_simp
    rw [hX]
    ring
  rw [← hF0]
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω
  have e : hopfK g ω = ω ^ 2 * F ω := by rw [hF, hopfK]; ring
  rw [e, mul_div_cancel_left₀ _ hω2]

/-- The unfolding map `(δ*, D) ↦ (a₀, a₁) = (ρK(δ*)/M, (ρ(D − D_line) + 2σK(δ*))/M)` of the two
lowest coefficients of the characteristic polynomial at the operating point (network and inertia
fixed; `Model.coeff0_eq`, `Model.coeff1_eq`). -/
def unfoldingMap (g : VSM) (p : ℝ × ℝ) : ℝ × ℝ :=
  (g.ρ * g.syncCoeff p.1 / g.M, (g.ρ * (p.2 - g.Dline) + 2 * g.σ * g.syncCoeff p.1) / g.M)

/-- The unfolding map reads the two lowest coefficients of every model with the network and the
inertia of `g`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem unfoldingMap_eq (g : VSM) (hL : g.L ≠ 0) (hZ : 0 < g.absSq)
    (δ D : ℝ) :
    unfoldingMap g (δ, D) =
      (({ g with D := D } : VSM).coeff0 (Model.Q ⟨{ g with D := D }, δ⟩),
        ({ g with D := D } : VSM).coeff1 (Model.Q ⟨{ g with D := D }, δ⟩)) := by
  rw [Model.coeff0_eq ⟨{ g with D := D }, δ⟩ hL hZ, Model.coeff1_eq ⟨{ g with D := D }, δ⟩ hL hZ]
  rfl

/-- **Linear versality of the Bogdanov–Takens point.** The unfolding map has at `(δ*, D)` the
derivative `(u, v) ↦ (ρK'u/M, (2σK'u + ρv)/M)`, `K'(δ*) = −A sin(δ* − α) = P''(δ*)`; at a fold
`K(δ*) = 0` with `A ≠ 0` (and `ρ, M ≠ 0`) it is injective (determinant `ρ²K'/M² ≠ 0`): the two
lowest coefficients are regular coordinates of the parameter plane `(δ*, D)` at the
Bogdanov–Takens point. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_unfoldingMap (g : VSM) (p : ℝ × ℝ) :
    HasFDerivAt (unfoldingMap g)
      (((g.ρ * -(g.A * Real.sin (p.1 - g.α)) / g.M) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((2 * g.σ * -(g.A * Real.sin (p.1 - g.α)) / g.M) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (g.ρ / g.M) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  have hK : HasDerivAt g.syncCoeff (-(g.A * Real.sin (p.1 - g.α))) p.1 := by
    have h := ((Real.hasDerivAt_cos (p.1 - g.α)).comp p.1
      ((hasDerivAt_id p.1).sub_const g.α)).const_mul g.A
    convert h using 1
    · funext x; simp [Network.syncCoeff]
    · simp
  have hK' := hK.hasFDerivAt.comp p (hasFDerivAt_fst (p := p))
  refine HasFDerivAt.prodMk ?_ ?_
  · have := (hK'.const_mul g.ρ).mul_const g.M⁻¹
    convert this using 1
    · funext q; simp [div_eq_mul_inv]
    · refine ContinuousLinearMap.ext fun q => ?_
      simp; ring
  · have h2 := (((hasFDerivAt_snd (p := p)).sub_const g.Dline).const_mul g.ρ).add
      (hK'.const_mul (2 * g.σ))
    have := h2.mul_const g.M⁻¹
    convert this using 1
    · funext q; simp [div_eq_mul_inv]
    · refine ContinuousLinearMap.ext fun q => ?_
      simp; ring

/-- At a fold with `A, ρ, M ≠ 0` the derivative of the unfolding map is injective. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem unfolding_derivative_injective (g : VSM) {δ : ℝ}
    (hA : g.A ≠ 0) (hρ : g.ρ ≠ 0) (hM : g.M ≠ 0) (hK : g.syncCoeff δ = 0) :
    Function.Injective (((g.ρ * -(g.A * Real.sin (δ - g.α)) / g.M) •
        ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((2 * g.σ * -(g.A * Real.sin (δ - g.α)) / g.M) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (g.ρ / g.M) • ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  have hc : Real.cos (δ - g.α) = 0 :=
    (mul_eq_zero.mp (show g.A * Real.cos (δ - g.α) = 0 from hK)).resolve_left hA
  have hs : Real.sin (δ - g.α) ≠ 0 := by
    intro h0
    have := Real.sin_sq_add_cos_sq (δ - g.α)
    rw [h0, hc] at this; norm_num at this
  have hc0 : g.ρ * -(g.A * Real.sin (δ - g.α)) / g.M ≠ 0 :=
    div_ne_zero (mul_ne_zero hρ (neg_ne_zero.mpr (mul_ne_zero hA hs))) hM
  have hd : g.ρ / g.M ≠ 0 := div_ne_zero hρ hM
  rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  simp only [ContinuousLinearMap.prod_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at h1 h2
  have hu : u₁ = u₂ := mul_left_cancel₀ hc0 h1
  subst hu
  have hv : v₁ = v₂ := mul_left_cancel₀ hd (by linarith)
  rw [hv]

end VSM
end powerlib.GFM.Line
