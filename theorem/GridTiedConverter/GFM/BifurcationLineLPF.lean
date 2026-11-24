import theorem.GridTiedConverter.GFM.Line.VSMLPF
import theorem.GridTiedConverter.GFM.BifurcationLine

/-! # The VSM with a power filter on a dynamic R–L line: the Bogdanov–Takens point

Static linear algebra of the five-state VSM + power filter on a dynamic line at its operating
point, the counterpart of `theorem/GridTiedConverter/GFM/BifurcationLine.lean` (four states).

Model boundary.
The five-state model `Line.VSMLPF` of `theorem/GridTiedConverter/GFM/Line/Model.lean`,
unchanged: state `(δ, ω, P_f, i_d, i_q)`, grid dq frame at `ω₀`, `δ̇ = ω`,
`M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`,
export-positive active power, constant `E`; no voltage loop, inner loops, LC filter, limiting,
PLL, delay or PWM. A model `Line.VSMLPF.Model` is read at `(δ*, 0, P_ref, i_s(δ*))`, its Jacobian
`Line.VSMLPF.Model.jac` (from `fderiv`); `K = A cos(δ* − α)` (`Line.Network.syncCoeff`),
`Q = Q(δ*)`, `D_line = 2 E² R X L/|Z|⁴`. Statements are about the Jacobian only: no normal form,
unfolding or bifurcation diagram is asserted.

Source: GFM counterpart study, note t3-bifurcation (b) (the BT point of the dynamic line, five
states, at the same damping as without filter; scripts s2b, s2c; scratch notes outside the
repository); the characteristic polynomial `Line.VSMLPF.det_characteristicMatrix`
(`theorem/GridTiedConverter/GFM/Line/VSMLPF.lean`); Kuznetsov, *Elements of Applied Bifurcation
Theory* (3rd ed., 2004), §8.4.

Results.
* `Line.VSMLPF.Model.charpoly_jac`: the characteristic polynomial of the Jacobian at the
  operating point, `(s³ + (D/M + ω_c) s² + (D ω_c/M) s − ω_c Q/M)(s² + 2σ s + ρ) + ω_c E² X/(L² M)`;
  its two lowest coefficients are `ω_c` times those of the four-state model
  (`Line.VSM.Model.coeff0_eq`, `Line.VSM.Model.coeff1_eq`).
* `Line.VSMLPF.Model.two_le_rootMultiplicity_zero_iff`: for `ω_c ≠ 0` the eigenvalue `0` is (at
  least) double exactly at a fold `K = 0` with `D = D_line`, the same damping as without the
  filter: the filter does not move the Bogdanov–Takens point (the two-lowest-coefficients law
  `SpecialFunctions.two_le_rootMultiplicity_zero_iff`).
* Jordan structure (`Line.VSMLPF.Model.btTangent` `q₀ = (1, 0, 0, i_s'(δ*))`,
  `Line.VSMLPF.Model.btChain` `q₁ = (0, 1, −D, w)` with the line part `w` of
  `Line.VSM.Model.chain`): `J q₀ = ω_c K e_P` (`Line.VSMLPF.Model.jac_mulVec_btTangent`),
  `J q₁ = q₀ + ω_c (D − D_line) e_P` (`Line.VSMLPF.Model.jac_mulVec_btChain`), every null vector is
  a multiple of `q₀` (`Line.VSMLPF.Model.eq_smul_btTangent_of_mulVec_eq_zero`); at `K = 0`,
  `D = D_line` a single Jordan block (`Line.VSMLPF.Model.jordan_chain_of_bt`).
-/

noncomputable section
namespace powerlib.GFM.Line
open Polynomial Matrix

namespace VSMLPF

/-- The four-state model with the same network, inertia, damping and set-point, about the same
angle. -/
private def lineVSM (m : Model) : VSM.Model := ⟨m.g.toVSM, m.δ⟩

/-- The tangent `(1, 0, 0, i_s'(δ*))` of the quasi-steady set at the operating point. -/
def Model.btTangent (m : Model) : Fin 5 → ℝ :=
  ![1, 0, 0, (lineVSM m).tangent 2, (lineVSM m).tangent 3]

/-- The second Jordan vector `(0, 1, −D, w)`, `w` the line part of `Line.VSM.Model.chain`. -/
def Model.btChain (m : Model) : Fin 5 → ℝ :=
  ![0, 1, -m.g.D, (lineVSM m).chain 2, (lineVSM m).chain 3]

/-- The characteristic polynomial of the Jacobian at the operating point.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_jac (m : Model) :
    m.jac.charpoly =
      (X ^ 3 + C (m.g.D / m.g.M + m.g.ωc) * X ^ 2 + C (m.g.D * m.g.ωc / m.g.M) * X -
          C (m.g.ωc * m.g.qssReactive m.δ / m.g.M)) *
        (X ^ 2 + C (2 * m.g.σ) * X + C m.g.ρ) +
          C (m.g.ωc * m.g.E ^ 2 * m.g.X / (m.g.L ^ 2 * m.g.M)) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  apply Polynomial.funext
  intro s
  rw [← Matrix.charpoly_map, ← Linear.det_characteristicMatrix_eq_eval, Model.jac,
    m.g.det_characteristicMatrix]
  simp [Network.qssReactive]

/-- **The double zero eigenvalue with a power filter.** For `M, ω_c, L ≠ 0` and `|Z|² > 0` the
eigenvalue `0` of the Jacobian at the operating point has algebraic multiplicity at least two
exactly at a fold `K = 0` with `D = D_line`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem Model.two_le_rootMultiplicity_zero_iff (m : Model)
    (hM : m.g.M ≠ 0) (hω : m.g.ωc ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    2 ≤ m.jac.charpoly.rootMultiplicity 0 ↔
      m.g.syncCoeff m.δ = 0 ∧ m.g.D = m.g.Dline := by
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  have c1 : m.jac.charpoly.coeff 1 = m.g.ωc * ((m.g.ρ * (m.g.D - m.g.Dline) +
      2 * m.g.σ * m.g.syncCoeff m.δ) / m.g.M) := by
    have h := (lineVSM m).coeff1_eq hL hZ
    simp only [VSM.coeff1, VSM.Model.Q, VSM.Model.K, lineVSM] at h
    rw [← h, m.charpoly_jac]
    simp [mul_coeff_one, coeff_X, coeff_C]
    ring
  have c0 : m.jac.charpoly.coeff 0 = m.g.ωc * (m.g.ρ * m.g.syncCoeff m.δ / m.g.M) := by
    have h := (lineVSM m).coeff0_eq hL hZ
    simp only [VSM.coeff0, VSM.Model.Q, VSM.Model.K, lineVSM] at h
    rw [← h, m.charpoly_jac]
    simp [coeff_X, coeff_C]
    field_simp
    ring
  rw [SpecialFunctions.two_le_rootMultiplicity_zero_iff (charpoly_monic _).ne_zero, c1, c0,
    mul_eq_zero, mul_eq_zero, or_iff_right hω, or_iff_right hω]
  constructor
  · rintro ⟨h1, h0⟩
    have hK : m.g.syncCoeff m.δ = 0 := by
      rw [div_eq_zero_iff, or_iff_left hM, mul_eq_zero, or_iff_right hρ] at h0
      exact h0
    refine ⟨hK, ?_⟩
    rw [hK, mul_zero, add_zero, div_eq_zero_iff, or_iff_left hM, mul_eq_zero,
      or_iff_right hρ, sub_eq_zero] at h1
    exact h1
  · rintro ⟨hK, hD⟩
    rw [hK, hD]
    simp


/-! ## Jordan structure -/

@[tmio M, powerlib_domain] private theorem jac_row (m : Model) (v : Fin 5 → ℝ) :
    (m.jac *ᵥ v) 0 = v 1 ∧
    (m.jac *ᵥ v) 1 = (-(m.g.D * v 1) - v 2) / m.g.M ∧
    (m.jac *ᵥ v) 2 = m.g.ωc * (-(m.g.qssReactive m.δ * v 0) - v 2 +
      m.g.E * Real.cos m.δ * v 3 + m.g.E * Real.sin m.δ * v 4) ∧
    (m.jac *ᵥ v) 3 = (-(m.g.E * Real.sin m.δ) * v 0 - m.g.R * v 3 + m.g.X * v 4) / m.g.L ∧
    (m.jac *ᵥ v) 4 = (m.g.E * Real.cos m.δ * v 0 - m.g.X * v 3 - m.g.R * v 4) / m.g.L := by
  have hreac : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.qssReactive m.δ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Model.jac, VSMLPF.jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_five, hreac] <;>
    ring

/-- The line identities of the tangent and the chain: `E (cos δ* t_d + sin δ* t_q) = κ` and
`E (cos δ* w_d + sin δ* w_q) = −D_line`, and the line rows of `q₀` and `q₁`. -/
@[tmio M, powerlib_domain] private theorem line_identities (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    m.g.E * Real.cos m.δ * (lineVSM m).tangent 2 + m.g.E * Real.sin m.δ * (lineVSM m).tangent 3 =
        m.g.κ ∧
      m.g.E * Real.cos m.δ * (lineVSM m).chain 2 + m.g.E * Real.sin m.δ * (lineVSM m).chain 3 =
        -m.g.Dline ∧
      -(m.g.E * Real.sin m.δ) - m.g.R * (lineVSM m).tangent 2 +
        m.g.X * (lineVSM m).tangent 3 = 0 ∧
      m.g.E * Real.cos m.δ - m.g.X * (lineVSM m).tangent 2 - m.g.R * (lineVSM m).tangent 3 = 0 ∧
      (-(m.g.R * (lineVSM m).chain 2) + m.g.X * (lineVSM m).chain 3) / m.g.L =
        (lineVSM m).tangent 2 ∧
      (-(m.g.X * (lineVSM m).chain 2) - m.g.R * (lineVSM m).chain 3) / m.g.L =
        (lineVSM m).tangent 3 := by
  have hZ' : m.g.absSq ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  have hc := Real.sin_sq_add_cos_sq m.δ
  have t2 : (lineVSM m).tangent 2 =
      m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq := rfl
  have t3 : (lineVSM m).tangent 3 =
      m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq := rfl
  have w2 : (lineVSM m).chain 2 = -(m.g.L * (m.g.R * (lineVSM m).tangent 2 +
      m.g.X * (lineVSM m).tangent 3)) / m.g.absSq := rfl
  have w3 : (lineVSM m).chain 3 = m.g.L * (m.g.X * (lineVSM m).tangent 2 -
      m.g.R * (lineVSM m).tangent 3) / m.g.absSq := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : m.g.E * Real.cos m.δ * (lineVSM m).tangent 2 +
        m.g.E * Real.sin m.δ * (lineVSM m).tangent 3 =
        m.g.E ^ 2 * m.g.X * (Real.sin m.δ ^ 2 + Real.cos m.δ ^ 2) / m.g.absSq := by
      rw [t2, t3]; field_simp; ring
    rw [e, hc, Network.κ]; ring
  · have e : m.g.E * Real.cos m.δ * (lineVSM m).chain 2 +
        m.g.E * Real.sin m.δ * (lineVSM m).chain 3 =
        -(2 * m.g.E ^ 2 * m.g.R * m.g.X * m.g.L *
          (Real.sin m.δ ^ 2 + Real.cos m.δ ^ 2) / m.g.absSq ^ 2) := by
      rw [w2, w3, t2, t3]; field_simp; ring
    rw [e, hc, Network.Dline]; ring
  · rw [t2, t3]; field_simp; rw [habs]; ring
  · rw [t2, t3]; field_simp; rw [habs]; ring
  · rw [w2, w3]; field_simp; rw [habs]; ring
  · rw [w2, w3]; field_simp; rw [habs]; ring

/-- The tangent is mapped to `ω_c K e_P`: a null vector exactly at a fold.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.jac_mulVec_btTangent (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) :
    m.jac *ᵥ m.btTangent = ![0, 0, m.g.ωc * m.g.syncCoeff m.δ, 0, 0] := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := jac_row m m.btTangent
  obtain ⟨i1, -, i3, i4, -, -⟩ := line_identities m hL hZ
  have hQ := m.g.syncCoeff_add_qssReactive hZ m.δ
  have b0 : m.btTangent 0 = 1 := rfl
  have b1 : m.btTangent 1 = 0 := rfl
  have b2 : m.btTangent 2 = 0 := rfl
  have b3 : m.btTangent 3 = (lineVSM m).tangent 2 := rfl
  have b4 : m.btTangent 4 = (lineVSM m).tangent 3 := rfl
  funext i
  fin_cases i
  · show (m.jac *ᵥ m.btTangent) 0 = 0
    rw [r0, b1]
  · show (m.jac *ᵥ m.btTangent) 1 = 0
    rw [r1, b1, b2]; ring
  · show (m.jac *ᵥ m.btTangent) 2 = m.g.ωc * m.g.syncCoeff m.δ
    rw [r2, b0, b2, b3, b4]
    linear_combination m.g.ωc * i1 - m.g.ωc * hQ
  · show (m.jac *ᵥ m.btTangent) 3 = 0
    rw [r3, b0, b3, b4, div_eq_zero_iff]
    left; linear_combination i3
  · show (m.jac *ᵥ m.btTangent) 4 = 0
    rw [r4, b0, b3, b4, div_eq_zero_iff]
    left; linear_combination i4

/-- The second Jordan vector: `J q₁ = q₀ + ω_c (D − D_line) e_P` at every angle.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.jac_mulVec_btChain (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) :
    m.jac *ᵥ m.btChain =
      m.btTangent + ![0, 0, m.g.ωc * (m.g.D - m.g.Dline), 0, 0] := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := jac_row m m.btChain
  obtain ⟨-, i2, -, -, i5, i6⟩ := line_identities m hL hZ
  have c0 : m.btChain 0 = 0 := rfl
  have c1 : m.btChain 1 = 1 := rfl
  have c2 : m.btChain 2 = -m.g.D := rfl
  have c3 : m.btChain 3 = (lineVSM m).chain 2 := rfl
  have c4 : m.btChain 4 = (lineVSM m).chain 3 := rfl
  funext i
  fin_cases i
  · show (m.jac *ᵥ m.btChain) 0 = 1 + 0
    rw [r0, c1]; ring
  · show (m.jac *ᵥ m.btChain) 1 = 0 + 0
    rw [r1, c1, c2]; field_simp; ring
  · show (m.jac *ᵥ m.btChain) 2 = 0 + m.g.ωc * (m.g.D - m.g.Dline)
    rw [r2, c0, c2, c3, c4]
    linear_combination m.g.ωc * i2
  · show (m.jac *ᵥ m.btChain) 3 = (lineVSM m).tangent 2 + 0
    rw [r3, c0, c3, c4, ← i5]; ring
  · show (m.jac *ᵥ m.btChain) 4 = (lineVSM m).tangent 3 + 0
    rw [r4, c0, c3, c4, ← i6]; ring

/-- **The kernel is at most one-dimensional**: every null vector is a multiple of `q₀`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.eq_smul_btTangent_of_mulVec_eq_zero (m : Model)
    (hM : m.g.M ≠ 0) (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) {v : Fin 5 → ℝ}
    (hv : m.jac *ᵥ v = 0) : v = v 0 • m.btTangent := by
  have hZ' : m.g.absSq ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  obtain ⟨r0, r1, -, r3, r4⟩ := jac_row m v
  have h0 : (m.jac *ᵥ v) 0 = 0 := by rw [hv]; rfl
  have h1 : (m.jac *ᵥ v) 1 = 0 := by rw [hv]; rfl
  have h3 : (m.jac *ᵥ v) 3 = 0 := by rw [hv]; rfl
  have h4 : (m.jac *ᵥ v) 4 = 0 := by rw [hv]; rfl
  rw [r0] at h0
  rw [r1, div_eq_zero_iff, or_iff_left hM, h0] at h1
  rw [r3, div_eq_zero_iff, or_iff_left hL] at h3
  rw [r4, div_eq_zero_iff, or_iff_left hL] at h4
  funext i
  fin_cases i
  · show v 0 = v 0 * 1
    ring
  · show v 1 = v 0 * 0
    rw [h0]; ring
  · show v 2 = v 0 * 0
    linarith
  · show v 3 = v 0 * (m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq)
    field_simp
    rw [habs]
    linear_combination (-m.g.R) * h3 + (-m.g.X) * h4
  · show v 4 = v 0 * (m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq)
    field_simp
    rw [habs]
    linear_combination m.g.X * h3 + (-m.g.R) * h4

/-- **The Bogdanov–Takens Jordan block with a power filter.** At a fold (`K = 0`) with
`D = D_line` the eigenvalue `0` of the Jacobian has the Jordan chain `J q₁ = q₀ ≠ 0`, `J q₀ = 0`,
and every null vector is a multiple of `q₀`: a double zero eigenvalue
(`Model.two_le_rootMultiplicity_zero_iff`) with a single Jordan block.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.jordan_chain_of_bt (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hK : m.g.syncCoeff m.δ = 0)
    (hD : m.g.D = m.g.Dline) :
    m.jac *ᵥ m.btTangent = 0 ∧ m.jac *ᵥ m.btChain = m.btTangent ∧ m.btTangent ≠ 0 ∧
      ∀ v, m.jac *ᵥ v = 0 → v = v 0 • m.btTangent := by
  refine ⟨?_, ?_, ?_, fun v hv => m.eq_smul_btTangent_of_mulVec_eq_zero hM hL hZ hv⟩
  · rw [m.jac_mulVec_btTangent hL hZ, hK, mul_zero]
    funext i
    fin_cases i <;> rfl
  · rw [m.jac_mulVec_btChain hM hL hZ, hD, sub_self, mul_zero]
    funext i
    fin_cases i <;> simp
  · intro h
    have := congrFun h 0
    simp [Model.btTangent] at this

end VSMLPF
end powerlib.GFM.Line
