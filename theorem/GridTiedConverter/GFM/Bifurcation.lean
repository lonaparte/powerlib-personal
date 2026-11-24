import theorem.GridTiedConverter.GFM.VSMLPFLossy

/-! # The quasi-static GFM: third-order Liénard form and no Bogdanov–Takens point

Static identities of the reduced (quasi-static line) grid-forming models.

Model boundary.
* Three states: the lossy VSM + power filter `VSMLPFLossy` of
  `theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`, unchanged: state `(δ, ω, P_f)`, continuous
  time, `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P(δ) − P_f)`,
  `P(δ) = c₀ + A sin(δ − α)` (export-positive), and its lossless case `VSMLPF`
  (`theorem/GridTiedConverter/GFM/VSMLPF.lean`).
* Two states (no power filter): the swing model `Synchronous.SwingParams`
  (`theorem/PowerSystem/Synchronous/Swing.lean`) `δ̇ = ω`,
  `M ω̇ = P_m − (k₁ + k₂ sin(δ − k₃)) − D ω`, which is the reduced GFM
  `⟨M, D, P_ref, c₀, A, α⟩` on a lossy line.
* Excluded: line dynamics, voltage loop, inner loops, limiting, PLL, delay, PWM. Statements are
  static: a coordinate change of the field and the characteristic polynomial of the Jacobian
  (computed from `fderiv`, `VSMLPF.hasFDerivAt_field`, `VSMLPFLossy.hasFDerivAt_field`,
  `Synchronous.SwingParams.hasFDerivAt_field`); no family is defined.

Source: GFM counterpart study, note t3-bifurcation (a) (`L2`, third-order Liénard form) and (b)
(`B1`, `B2`, no double zero eigenvalue for `D ≠ 0`), derived and checked symbolically (scratch
notes outside the repository); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.,
2004), §8.4 (a Bogdanov–Takens point is an equilibrium with a double zero eigenvalue).

Results.
* Third-order Liénard form (`VSMLPFLossy.lienardField_eq_transport`): in the coordinates
  `(δ, δ̇, δ̈) = (δ, ω, (P_ref − P_f − D ω)/M)` (`VSMLPFLossy.lienardCoord`, the matrix
  `VSMLPFLossy.lienardMatrix` with determinant `−1/M`, `VSMLPFLossy.det_lienardMatrix`, plus the
  offset `(0, 0, P_ref/M)`), the lossy field is the jerk field `ẋ = y`, `ẏ = z`,
  `ż = −λ z − H y − (ω_c/M)(P(x) − P_ref)`, `λ = ω_c + D/M`, `H = D ω_c/M`
  (`VSMLPFLossy.lienardField`), i.e. `M δ⃛ + (D + M ω_c) δ̈ + D ω_c δ̇ + ω_c (P(δ) − P_ref) = 0`.
  The friction coefficients `D + M ω_c` and `D ω_c` are constants: unlike the PI-PLL Liénard form
  (`theorem/GridTiedConverter/PLL/PIPLLLienard.lean`), where the friction is proportional to the
  slope of the characteristic, the GFM friction does not depend on the operating point.
* Jacobian of the lossy field (`VSMLPFLossy.hasFDerivAt_field`): the lossless Jacobian
  `VSMLPF.jacobian` of `⟨M, D, ω_c, P_ref − c₀, A⟩` at `δ − α`.
* Characteristic polynomial (`VSMLPF.charpoly_jacobian`):
  `χ(s) = s³ + (D/M + ω_c) s² + (D ω_c/M) s + ω_c K₀ cos δ / M`.
* No Bogdanov–Takens point with damping (three states): the eigenvalue `0` has algebraic
  multiplicity at least two iff `D = 0` and `K₀ cos δ = 0` (`M, ω_c ≠ 0`,
  `VSMLPF.two_le_rootMultiplicity_zero_iff`); with `D ≠ 0` it is at most simple
  (`VSMLPF.rootMultiplicity_zero_le_one`): the fold `K = 0` of a damped model is a simple zero
  eigenvalue (a saddle-node), never a double zero. The same holds on a lossy line through
  `VSMLPFLossy.hasFDerivAt_field` (its Jacobian is `VSMLPF.jacobian` at `δ − α`).
* Two states: `0` is a double eigenvalue of the swing Jacobian iff `D = 0` and `K = 0`
  (`swing_two_le_rootMultiplicity_zero_iff`); with `D ≠ 0` it is at most simple
  (`swing_rootMultiplicity_zero_le_one`).
-/

noncomputable section
namespace powerlib.GFM
open Polynomial Matrix
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)

/-! ## Polynomial and matrix helpers (implementation evidence) -/

/-- The characteristic polynomial of a `3 × 3` matrix:
`χ = X³ − tr A · X² + Σ₂(A) X − det A` (`Criteria.principalMinorSum`). -/
@[tmio T, powerlib_foundation] private theorem charpoly_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.charpoly = X ^ 3 - C A.trace * X ^ 2 + C (Criteria.principalMinorSum A) * X - C A.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.det_fin_three]
  simp only [charmatrix_apply, Matrix.diagonal_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true,
    Matrix.diagonal_apply_ne, Criteria.principalMinorSum, map_add, map_sub, map_mul]
  ring

/-- The eigenvalue `0` of a monic cubic is (at least) double iff its two lowest coefficients
vanish. -/
@[tmio T, powerlib_foundation] private theorem two_le_rootMultiplicity_zero_cubic (a2 a1 a0 : ℝ) :
    2 ≤ (X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : ℝ[X]).rootMultiplicity 0 ↔
      a1 = 0 ∧ a0 = 0 := by
  have hq : (X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0 : ℝ[X]) ≠ 0 := fun h => by
    have := congrArg (fun q : ℝ[X] => q.coeff 3) h
    simp at this
  rw [le_rootMultiplicity_iff hq, map_zero, sub_zero, X_pow_dvd_iff]
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    have h0 := h 0 (by norm_num)
    simp [coeff_X, coeff_C] at h1 h0
    exact ⟨h1, h0⟩
  · rintro ⟨h1, h0⟩ d hd
    interval_cases d <;> simp [coeff_C, h1, h0]

/-- The eigenvalue `0` of a monic quadratic is double iff both lower coefficients vanish. -/
@[tmio T, powerlib_foundation] private theorem two_le_rootMultiplicity_zero_quadratic (a1 a0 : ℝ) :
    2 ≤ (X ^ 2 + C a1 * X + C a0 : ℝ[X]).rootMultiplicity 0 ↔ a1 = 0 ∧ a0 = 0 := by
  have hq : (X ^ 2 + C a1 * X + C a0 : ℝ[X]) ≠ 0 := fun h => by
    have := congrArg (fun q : ℝ[X] => q.coeff 2) h
    simp at this
  rw [le_rootMultiplicity_iff hq, map_zero, sub_zero, X_pow_dvd_iff]
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    have h0 := h 0 (by norm_num)
    simp [coeff_X, coeff_C] at h1 h0
    exact ⟨h1, h0⟩
  · rintro ⟨h1, h0⟩ d hd
    interval_cases d <;> simp [h1, h0]

/-! ## Three states: the third-order Liénard form -/

namespace VSMLPFLossy

variable (p : VSMLPFLossy)

/-- The matrix of the Liénard coordinates `(δ, ω, P_f) ↦ (δ, ω, −(D ω + P_f)/M)`. -/
def lienardMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, -p.D / p.M, -1 / p.M]

/-- The offset `(0, 0, P_ref/M)` of the Liénard coordinates. -/
def lienardOffset : State 3 := mk3 0 0 (p.Pref / p.M)

@[tmio M, powerlib_domain] theorem det_lienardMatrix : p.lienardMatrix.det = -1 / p.M := by
  simp [lienardMatrix, Matrix.det_fin_three]

@[tmio M, powerlib_domain] theorem isUnit_lienardMatrix (hM : p.M ≠ 0) :
    IsUnit p.lienardMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, det_lienardMatrix, isUnit_iff_ne_zero]
  exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hM

/-- The Liénard coordinates `(δ, δ̇, δ̈) = (δ, ω, (P_ref − P_f − D ω)/M)` (`M ≠ 0`), the affine map
`x ↦ lienardMatrix x + lienardOffset`. -/
def lienardCoord (hM : p.M ≠ 0) : State 3 ≃L[ℝ] State 3 :=
  Dynamics.matrixCoord p.lienardMatrix (p.isUnit_lienardMatrix hM)

/-- The third-order Liénard (jerk) field `ẋ = y`, `ẏ = z`,
`ż = −(ω_c + D/M) z − (D ω_c/M) y − (ω_c/M)(P(x) − P_ref)`. -/
def lienardField (y : State 3) : State 3 :=
  mk3 (y 1) (y 2) (-(p.ωc + p.D / p.M) * y 2 - p.D * p.ωc / p.M * y 1 -
    p.ωc / p.M * (p.Pe (y 0) - p.Pref))

/-- **Third-order Liénard form.** In the coordinates `(δ, ω, (P_ref − P_f − D ω)/M)` the lossy
VSM + power-filter field is the jerk field with constant friction:
`M δ⃛ + (D + M ω_c) δ̈ + D ω_c δ̇ + ω_c (P(δ) − P_ref) = 0`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem lienardField_eq_transport (hM : p.M ≠ 0) :
    p.lienardField = Dynamics.transportField (p.lienardCoord hM) p.lienardOffset p.field := by
  funext y
  rw [← Dynamics.affineCoord_affineCoord_symm (p.lienardCoord hM) p.lienardOffset y,
    Dynamics.transportField_affineCoord]
  set x := Dynamics.affineCoord (p.lienardCoord hM).symm
    (-((p.lienardCoord hM).symm p.lienardOffset)) y
  apply state3_ext <;>
    simp only [lienardField, field, Dynamics.affineCoord, lienardCoord, Dynamics.matrixCoord_apply,
      PiLp.add_apply, toEuclideanCLM_apply3, lienardMatrix, lienardOffset, mk3_zero, mk3_one,
      mk3_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const] <;>
    field_simp <;> ring

/-- The Jacobian of the lossy field is the lossless Jacobian `VSMLPF.jacobian` of
`⟨M, D, ω_c, P_ref − c₀, A⟩` at `δ − α`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field (x : State 3) :
    HasFDerivAt p.field
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (p.toVSMLPF.jacobian (x 0 - p.α))) x := by
  have h := (p.toVSMLPF.hasFDerivAt_field (x - p.offset)).comp x
    ((hasFDerivAt_id x).sub_const p.offset)
  rw [ContinuousLinearMap.comp_id] at h
  have key : (x - p.offset) 0 = x 0 - p.α := by simp [offset]
  rw [key] at h
  have hf : p.field = p.toVSMLPF.field ∘ fun y => id y - p.offset :=
    funext fun y => p.field_eq y
  rw [hf]
  exact h

end VSMLPFLossy

/-! ## Three states: no double zero eigenvalue with damping -/

namespace VSMLPF

variable (g : VSMLPF)

/-- `χ(s) = s³ + (D/M + ω_c) s² + (D ω_c/M) s + ω_c K₀ cos δ / M`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem charpoly_jacobian (δ : ℝ) :
    (g.jacobian δ).charpoly = X ^ 3 + C (g.D / g.M + g.ωc) * X ^ 2 + C (g.D * g.ωc / g.M) * X +
      C (g.ωc * (g.K0 * Real.cos δ) / g.M) := by
  rw [charpoly_fin_three, trace_jacobian, principalMinorSum_jacobian, det_jacobian]
  have e2 : -g.D / g.M - g.ωc = -(g.D / g.M + g.ωc) := by ring
  have e0 : -(g.ωc * (g.K0 * Real.cos δ)) / g.M = -(g.ωc * (g.K0 * Real.cos δ) / g.M) := by ring
  rw [e2, e0, map_neg, map_neg]
  ring

/-- **The zero eigenvalue is double only without damping.** For `M, ω_c ≠ 0` the eigenvalue `0`
of the Jacobian at `δ` has algebraic multiplicity at least two iff `D = 0` and `K₀ cos δ = 0`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem two_le_rootMultiplicity_zero_iff (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (δ : ℝ) :
    2 ≤ (g.jacobian δ).charpoly.rootMultiplicity 0 ↔ g.D = 0 ∧ g.K0 * Real.cos δ = 0 := by
  rw [charpoly_jacobian, two_le_rootMultiplicity_zero_cubic, div_eq_zero_iff, div_eq_zero_iff,
    or_iff_left hM, or_iff_left hM, mul_eq_zero, or_iff_left hω, mul_eq_zero, or_iff_right hω]

/-- **No Bogdanov–Takens point with damping.** For `M, D, ω_c ≠ 0` the eigenvalue `0` of the
Jacobian is at most simple at every angle; at the fold `K₀ cos δ = 0` it is simple, the other two
eigenvalues being `−D/M` and `−ω_c`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem rootMultiplicity_zero_le_one (hM : g.M ≠ 0) (hD : g.D ≠ 0)
    (hω : g.ωc ≠ 0) (δ : ℝ) : (g.jacobian δ).charpoly.rootMultiplicity 0 ≤ 1 := by
  by_contra h
  exact hD ((g.two_le_rootMultiplicity_zero_iff hM hω δ).mp (by omega)).1

end VSMLPF

/-! ## Two states: the swing model -/

/-- For `M ≠ 0` the eigenvalue `0` of the swing Jacobian at `δ` is double iff `D = 0` and
`K = k₂ cos(δ − k₃) = 0`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem swing_two_le_rootMultiplicity_zero_iff
    (p : Synchronous.SwingParams) (hM : p.M ≠ 0) (δ : ℝ) :
    2 ≤ (p.jacobian δ).charpoly.rootMultiplicity 0 ↔ p.D = 0 ∧ p.syncCoeff δ = 0 := by
  have e : (p.jacobian δ).charpoly =
      X ^ 2 + C (p.D / p.M) * X + C (p.syncCoeff δ / p.M) := by
    rw [Matrix.charpoly_fin_two, p.trace_jacobian, p.det_jacobian, neg_div, map_neg]
    ring
  rw [e, two_le_rootMultiplicity_zero_quadratic, div_eq_zero_iff, div_eq_zero_iff, or_iff_left hM,
    or_iff_left hM]

/-- **No Bogdanov–Takens point in the damped two-state model**: with `M, D ≠ 0` the eigenvalue `0`
of the swing Jacobian is at most simple. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem swing_rootMultiplicity_zero_le_one (p : Synchronous.SwingParams)
    (hM : p.M ≠ 0) (hD : p.D ≠ 0) (δ : ℝ) : (p.jacobian δ).charpoly.rootMultiplicity 0 ≤ 1 := by
  by_contra h
  exact hD ((swing_two_le_rootMultiplicity_zero_iff p hM δ).mp (by omega)).1

end powerlib.GFM
