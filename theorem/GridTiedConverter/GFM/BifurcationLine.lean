import theorem.GridTiedConverter.GFM.Line.VSM
import theorem.SpecialFunctions.PolynomialSigns

/-! # The VSM on a dynamic R–L line: the Bogdanov–Takens point at the line damping

Static linear algebra of the four-state VSM on a dynamic line at its operating point.

Model boundary.
The four-state model `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
state `(δ, ω, i_d, i_q)`, grid dq frame at `ω₀`, `δ̇ = ω`, `M ω̇ = P_ref − P_e − D ω`,
`L i̇ = E e^{jδ} − V − (R + jX) i`, export-positive active power, constant `E`; no voltage loop,
inner loops, LC filter, limiting, PLL, delay or PWM. A model `Line.VSM.Model` is read at its
operating point `(δ*, 0, i_s(δ*))`; `K = A cos(δ* − α) = P'(δ*)`, `Q = Q(δ*)`, `κ = K + Q =
E² X/|Z|²`, `D_line = 2 E² R X L/|Z|⁴` (`Line.Network.Dline`). Statements are about the Jacobian
`Line.VSM.Model.jac` (from `fderiv`, `Line.VSM.Model.fderiv_point`), not about the nonlinear flow:
no normal form, unfolding or bifurcation diagram is asserted.

Source: GFM counterpart study, note t3-bifurcation (b) (the BT point of the dynamic line at
`D_BT = 2 E² R X²/(ω_b |Z|⁴)`, `ω_b = X/L = ω₀`, i.e. `D_BT = D_line`; scripts s2b, s2c, derived
and checked numerically there; scratch notes outside the repository); the characteristic
polynomial and the line damping of `theorem/GridTiedConverter/GFM/Line/VSM.lean`
(`Line.VSM.Model.coeff0_eq`, `Line.VSM.Model.coeff1_eq`); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed., 2004), §8.4 (a Bogdanov–Takens point is a double zero eigenvalue
with a single Jordan block).

Results.
* `Line.VSM.Model.charpoly_jac`: the characteristic polynomial of the Jacobian at the operating
  point is the quartic `s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` of
  `Line.VSM.Model.det_characteristicMatrix`.
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
-/

noncomputable section
namespace powerlib.GFM.Line
open Polynomial Matrix

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

/-- The characteristic polynomial of the Jacobian at the operating point.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_jac (m : Model) :
    m.jac.charpoly = X ^ 4 + C m.g.coeff3 * X ^ 3 + C (m.g.coeff2 m.Q) * X ^ 2 +
      C (m.g.coeff1 m.Q) * X + C (m.g.coeff0 m.Q) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  apply Polynomial.funext
  intro s
  rw [← Matrix.charpoly_map, ← Linear.det_characteristicMatrix_eq_eval,
    m.det_characteristicMatrix]
  simp

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

end VSM
end powerlib.GFM.Line
