import theorem.GridTiedConverter.GFM.QVDroopVirtualFold
import theorem.Dynamics.CuspReduction

/-! # Grid-forming converter with Q–V droop and a virtual impedance: the cusp points of the fold

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P_t(δ, E) − D Δω`, `Q̇_f = ω_q (Q_t(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, the powers measured at the converter terminal behind the virtual
  impedance `Z_v = R_v + jX_v`, the grid branch `Z_g = R_g + jX_g` to a stiff grid `V ∠ 0`,
  export-positive, continuous time, autonomous. Read about a selected point
  (`QVDroopVirtual.Model`) on `QVDroopVirtual.family`. Excluded as there.
* Level: the cubic (cusp) coefficient at the cusp points `C = 0`, `𝔉 = 0` of the fold (static),
  Lyapunov instability and local asymptotic stability there, and the Lyapunov and local
  asymptotic stability decision off the Hopf surface with the cusp points included. Parameters
  are free reals; every theorem lists its range.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.2 and §8.7 (the cusp
coefficient `c = (1/6)⟨p, C(q, q, q) + 3 B(q, h₂)⟩`, `A h₂ = −B(q, q)`); the cusp laws
`Dynamics.CenterManifold.unstable_of_cuspCoeff_pos_of_charpoly`,
`Dynamics.CenterManifold.localAsymptoticStable_of_cuspCoeff_neg_of_charpoly`
(`theorem/Dynamics/CuspReduction.lean`); the derivative forms (with the angle curvatures
`ρ = ∂²P_t/∂δ²`, `τ = ∂²Q_t/∂δ²`), the null pair `QVDroop.foldQ`, `QVDroop.foldP` and the
characteristic polynomial at a fold of `theorem/GridTiedConverter/GFM/QVDroopVirtualFold.lean`. The
cubic coefficient was derived with exact computer algebra (sympy: the homological equation solved
on the fold, the numerator reduced modulo `𝔉`, which is linear in `ρ`, a polynomial certificate in
the ideal of `C` and `𝔉`) and is proved here by `linear_combination`.

Results.
* `cuspW` (the homological vector `w = (−W/c, 0, 0)`), `Model.homological_cusp` (`J w = −B(q, q)`
  at `C = 0`, `𝔉 = 0`), **`Model.cuspCoeff_cusp`**: with `a = P_tδ`, `c = Q_tδ`, `k = K_t`,
  `m = n_q/E*`, `ρ = ∂²P_t/∂δ²`, the cubic coefficient of the fold null pair is
  `c₃ = −ω_q k m c ρ/(2 (a + D ω_q k))`; `Model.sign_cuspCoeff_cusp`
  (`sign c₃ = sign (−k m c ρ)` for `ω_q > 0`, `a + D ω_q k > 0`). For `Z_v = 0` (`ρ = −c`) it is
  the coefficient `ω_q c² k m/(2 (a + D ω_q k))` of
  `theorem/GridTiedConverter/GFM/QVDroopCusp.lean`.
* The remaining degenerate set: on the cusp set with `c, k ≠ 0`, `m = 0` forces `ρ = 0`, so
  `c₃ = 0` exactly when `ρ = 0`; these cusp points (and the fold points with `K_t = 0` or
  `Q_tδ = 0`, and the double-zero set `C = 0`, `G = 0`) are located, not decided.
* Witnesses (exact rationals with `Z_v ≠ 0`, outside the physical range: `n_q < 0`):
  `cuspSaddle` (`δ* = 0`, `K_t m c ρ = −1/8`) and `cuspStable` (`δ* = π/2`,
  `K_t m c ρ = 16/375`): both signs of `c₃` occur. Whether the cusp set meets the physical range
  (`n_q, X_g, V, E* > 0`) is not decided here.

Family and connection conclusions.
No new family: connection conclusions on `QVDroopVirtual.family`.
* **`mem_den_unstable_of_cusp`**: for `M, ω_q > 0`, an equilibrium at a cusp point (`C = 0`,
  `𝔉 = 0`) with `A > 0`, `a + D ω_q K_t > 0`, `E* ≠ 0`, `Q_tδ ≠ 0` and
  `K_t (n_q/E*) Q_tδ ρ < 0` is unstable; **`mem_den_locallyAsymptoticallyStable_of_cusp`**: with
  `K_t (n_q/E*) Q_tδ ρ > 0` it is locally asymptotically stable.
* **`mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp`**,
  **`mem_den_lyapunovStable_iff_of_hopf_ne_cusp`**: for `M, ω_q > 0` off the Hopf surface
  (`G ≠ 0`) and, at a fold, `K_t, E*, Q_tδ ≠ 0` and `ρ ≠ 0` at a cusp point, the model is locally
  asymptotically (Lyapunov) stable iff the point is an equilibrium with `A, C, G > 0`, or a cusp
  point with `A > 0`, `a + D ω_q K_t > 0` and `K_t (n_q/E*) Q_tδ ρ > 0` (no hypothesis `𝔉 ≠ 0`,
  unlike `mem_den_lyapunovStable_iff_of_hopf_ne`).
* `cuspSaddle_mem_den_unstable`, `cuspStable_mem_den_locallyAsymptoticallyStable`.
-/

noncomputable section
namespace powerlib.GFM.QVDroopVirtual
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Criteria (droopJacobian)

/-! ## The homological vector and the cubic coefficient at a cusp point -/

/-- The homological vector `w = (−W/c, 0, 0)` of a cusp point,
`W = k² τ − m c² k − m c² + m² c² τ` (`ω_q W` is the third component of `B(q, q)` at the fold null
vector `q = (k, 0, c)`, `τ = ∂²Q_t/∂δ²`). -/
def cuspW (c k m τ : ℝ) : State 3 :=
  WithLp.toLp 2 ![-(k ^ 2 * τ - m * c ^ 2 * k - m * c ^ 2 + m ^ 2 * c ^ 2 * τ) / c, 0, 0]

/-- **The homological equation at a cusp point.** At a fold (`C = 0`) with `M ≠ 0`, `E* ≠ 0`,
`c = Q_tδ ≠ 0` and a vanishing cusp quantity `𝔉 = 0`: `J w = −B(q, q)` for `w = cuspW` and the
fold null vector `q = QVDroop.foldQ k c`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.homological_cusp (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0) :
    fderiv ℝ m.field 0 (cuspW (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))
        (m.q.nq / m.q.emf m.Qf) (m.q.Qtδδ m.δ (m.q.emf m.Qf))) =
      -fderiv ℝ (fderiv ℝ m.field) 0
        (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
        (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  set q3 := QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)) with hq3
  have v0 := m.fderiv_fderiv_apply_eq_bForm hE q3 q3 0
  have v1 := m.fderiv_fderiv_apply_eq_bForm hE q3 q3 1
  have v2 := m.fderiv_fderiv_apply_eq_bForm hE q3 q3 2
  rw [m.fderiv_field, Model.jacobian, jacobian_eq_droopJacobian]
  generalize fderiv ℝ (fderiv ℝ m.field) 0 q3 q3 = v at v0 v1 v2 ⊢
  rw [hq3] at *
  generalize m.q.Ptδ m.δ (m.q.emf m.Qf) = a at h0 v0 v1 v2 hF ⊢
  generalize m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) = b at h0 v0 v1 v2 ⊢
  generalize m.q.Qtδ m.δ (m.q.emf m.Qf) = c at h0 v0 v1 v2 hF hc ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 v0 v1 v2 hF ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at v0 v1 v2 hF ⊢
  generalize m.q.Ptδδ m.δ (m.q.emf m.Qf) = ρ at v0 v1 v2 hF ⊢
  generalize m.q.Qtδδ m.δ (m.q.emf m.Qf) = τ at v0 v1 v2 hF ⊢
  simp only [bForm, toC, QVDroop.foldQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at v0 v1 v2
  have e1 : v 1 = -(ρ / m.q.M) * (k * k) + μ * a / m.q.M * (k * c + c * k) -
      μ * (b + μ * ρ) / m.q.M * (c * c) := by
    apply Complex.ofReal_injective; rw [v1]; push_cast; ring
  have e2 : v 2 = m.q.ωq * (k ^ 2 * τ - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * c ^ 2 * τ) := by
    apply Complex.ofReal_injective; rw [v2]; push_cast; ring
  have hv0 : v 0 = 0 := by apply Complex.ofReal_injective; rw [v0]; simp
  have hM1 : m.q.M * v 1 = -(ρ * k ^ 2) + 2 * μ * a * k * c - μ * (b + μ * ρ) * c ^ 2 := by
    rw [e1]; field_simp; ring
  have key1 : a * (k ^ 2 * τ - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * c ^ 2 * τ) +
      c * (m.q.M * v 1) = 0 := by
    rw [hM1]
    unfold foldQuad at hF
    linear_combination (μ * c ^ 2) * h0 + hF
  have hv1 : v 1 = -(a * (k ^ 2 * τ - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * c ^ 2 * τ)) /
      (c * m.q.M) := by
    rw [eq_div_iff (mul_ne_zero hc hM)]
    linear_combination key1
  apply Dynamics.state3_ext
  · rw [Dynamics.toEuclideanCLM_apply3]
    simp [droopJacobian, cuspW, hv0]
  · rw [Dynamics.toEuclideanCLM_apply3, PiLp.neg_apply, hv1]
    simp [droopJacobian, cuspW]
    field_simp
    ring
  · rw [Dynamics.toEuclideanCLM_apply3, PiLp.neg_apply, e2]
    simp [droopJacobian, cuspW]
    field_simp
    ring

/-- **The cubic coefficient at a cusp point.** At a fold (`C = 0`) with `M ≠ 0`, `E* ≠ 0`,
`c = Q_tδ ≠ 0`, `k = K_t ≠ 0`, `a + D ω_q k ≠ 0` and `𝔉 = 0`, Kuznetsov's cubic coefficient of the
null pair `(QVDroop.foldQ, QVDroop.foldP)` read with `w = cuspW` is
`2 (a + D ω_q k) c₃ = −ω_q k m c ρ` (`a = P_tδ`, `m = n_q/E*`, `ρ = ∂²P_t/∂δ²`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem Model.cuspCoeff_cusp (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0) (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0)
    (ha1 : m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0) :
    2 * (m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) *
      NormalForm.BogdanovTakens.cuspCoeff m.field 0
        (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
        (QVDroop.foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
          (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)))
        (cuspW (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))
          (m.q.nq / m.q.emf m.Qf) (m.q.Qtδδ m.δ (m.q.emf m.Qf))) =
      -(m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
        m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  set q3 := QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)) with hq3
  set w3 := cuspW (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))
    (m.q.nq / m.q.emf m.Qf) (m.q.Qtδδ m.δ (m.q.emf m.Qf)) with hw3
  have t0 := m.iteratedFDeriv_three_apply_eq_cForm hE q3 q3 q3 0
  have t1 := m.iteratedFDeriv_three_apply_eq_cForm hE q3 q3 q3 1
  have t2 := m.iteratedFDeriv_three_apply_eq_cForm hE q3 q3 q3 2
  have u0 := m.fderiv_fderiv_apply_eq_bForm hE q3 w3 0
  have u1 := m.fderiv_fderiv_apply_eq_bForm hE q3 w3 1
  have u2 := m.fderiv_fderiv_apply_eq_bForm hE q3 w3 2
  rw [NormalForm.BogdanovTakens.cuspCoeff]
  generalize iteratedFDeriv ℝ 3 m.field 0 ![q3, q3, q3] = T at t0 t1 t2 ⊢
  generalize fderiv ℝ (fderiv ℝ m.field) 0 q3 w3 = U at u0 u1 u2 ⊢
  rw [hq3, hw3] at *
  generalize m.q.Ptδ m.δ (m.q.emf m.Qf) = a at h0 t0 t1 t2 u0 u1 u2 hF ha1 ⊢
  generalize m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) = b at h0 t0 t1 t2 u0 u1 u2 ⊢
  generalize m.q.Qtδ m.δ (m.q.emf m.Qf) = c at h0 t0 t1 t2 u0 u1 u2 hF hc ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 t0 t1 t2 u0 u1 u2 hF hk ha1 ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at t0 t1 t2 u0 u1 u2 hF ⊢
  generalize m.q.Ptδδ m.δ (m.q.emf m.Qf) = ρ at t0 t1 t2 u0 u1 u2 hF ⊢
  generalize m.q.Qtδδ m.δ (m.q.emf m.Qf) = τ at t0 t1 t2 u0 u1 u2 hF ⊢
  simp only [cForm, bForm, toC, QVDroop.foldQ, cuspW, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at t0 t1 t2 u0 u1 u2
  have hT0 : T 0 = 0 := by apply Complex.ofReal_injective; rw [t0]; simp
  have hU0 : U 0 = 0 := by apply Complex.ofReal_injective; rw [u0]; simp
  have hT1 : m.q.M * T 1 = a * k ^ 3 + 3 * μ * ρ * k ^ 2 * c := by
    have e : T 1 = a / m.q.M * (k * k * k) +
        μ * ρ / m.q.M * (k * k * c + k * c * k + c * k * k) := by
      apply Complex.ofReal_injective; rw [t1]; push_cast; ring
    rw [e]; field_simp; ring
  have hT2 : T 2 = -(m.q.ωq * c * k ^ 3) - 3 * m.q.ωq * μ * τ * k ^ 2 * c := by
    apply Complex.ofReal_injective; rw [t2]; push_cast; ring
  have hU1 : c * (m.q.M * U 1) = -(k ^ 2 * τ - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * c ^ 2 * τ) *
      (μ * a * c - ρ * k) := by
    have e : U 1 = -(ρ / m.q.M) * (k * (-(k ^ 2 * τ - μ * c ^ 2 * k - μ * c ^ 2 +
        μ ^ 2 * c ^ 2 * τ) / c)) + μ * a / m.q.M * (k * 0 + c * (-(k ^ 2 * τ - μ * c ^ 2 * k -
        μ * c ^ 2 + μ ^ 2 * c ^ 2 * τ) / c)) - μ * (b + μ * ρ) / m.q.M * (c * 0) := by
      apply Complex.ofReal_injective; rw [u1]; push_cast; ring
    rw [e]; field_simp; ring
  have hU2 : c * U 2 = -(m.q.ωq * (k ^ 2 * τ - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * c ^ 2 * τ)) *
      (τ * k - μ * c ^ 2) := by
    have e : U 2 = m.q.ωq * τ * (k * (-(k ^ 2 * τ - μ * c ^ 2 * k - μ * c ^ 2 +
        μ ^ 2 * c ^ 2 * τ) / c)) - m.q.ωq * μ * c * (k * 0 + c * (-(k ^ 2 * τ - μ * c ^ 2 * k -
        μ * c ^ 2 + μ ^ 2 * c ^ 2 * τ) / c)) + m.q.ωq * μ * (k - 1 + μ * τ) * (c * 0) := by
      apply Complex.ofReal_injective; rw [u2]; push_cast; ring
    rw [e]; field_simp; ring
  simp only [QVDroop.foldP, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hT0, hU0]
  have hN2 : m.q.D * m.q.ωq * k ^ 2 + b * c ≠ 0 := by
    have e : m.q.D * m.q.ωq * k ^ 2 + b * c = k * (a + m.q.D * m.q.ωq * k) := by
      linear_combination (-1 : ℝ) * h0
    rw [e]; exact mul_ne_zero hk ha1
  field_simp
  refine mul_left_cancel₀ (pow_ne_zero 2 hc) ?_
  unfold foldQuad at hF
  linear_combination (c ^ 2 * (2 * (a + m.q.D * m.q.ωq * k)) * m.q.ωq * k) * hT1 +
    (c * (2 * (a + m.q.D * m.q.ωq * k)) * 3 * m.q.ωq * k) * hU1 +
    (c ^ 2 * (2 * (a + m.q.D * m.q.ωq * k)) * b) * hT2 +
    (c * (2 * (a + m.q.D * m.q.ωq * k)) * 3 * b) * hU2 +
    (2 * m.q.ωq * (3 * m.q.D * c ^ 4 * k ^ 2 * μ ^ 2 * m.q.ωq -
      3 * m.q.D * c ^ 4 * k * μ ^ 3 * m.q.ωq * τ + 3 * m.q.D * c ^ 4 * k * μ ^ 2 * m.q.ωq +
      m.q.D * c ^ 2 * k ^ 4 * m.q.ωq - 3 * m.q.D * c ^ 2 * k ^ 3 * μ * m.q.ωq * τ +
      3 * m.q.D * c ^ 2 * k ^ 2 * μ ^ 2 * m.q.ωq * τ ^ 2 -
      3 * m.q.D * c ^ 2 * k ^ 2 * μ * m.q.ωq * τ + 3 * m.q.D * k ^ 4 * m.q.ωq * τ ^ 2 +
      3 * a * c ^ 4 * k * μ ^ 2 - 3 * a * c ^ 4 * μ ^ 3 * τ + 3 * a * c ^ 4 * μ ^ 2 +
      a * c ^ 2 * k ^ 3 - 3 * a * c ^ 2 * k ^ 2 * μ * τ + 3 * a * c ^ 2 * k * μ ^ 2 * τ ^ 2 -
      3 * a * c ^ 2 * k * μ * τ + 3 * a * k ^ 3 * τ ^ 2 - 3 * c ^ 3 * k * μ * ρ)) * h0 +
    (-6 * k ^ 2 * m.q.ωq * τ * (m.q.D * k * m.q.ωq + a)) * hF

/-- **The sign of the cubic coefficient at a cusp point**: under the hypotheses of
`Model.cuspCoeff_cusp` with `ω_q > 0` and `a + D ω_q k > 0`, `c₃` has the sign of `−k m c ρ`
(`k = K_t`, `m = n_q/E*`, `c = Q_tδ`, `ρ = ∂²P_t/∂δ²`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_cuspCoeff_cusp (m : Model) (hM : m.q.M ≠ 0)
    (hω : 0 < m.q.ωq) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0) (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0)
    (ha1 : 0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hF : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0) :
    SignType.sign (NormalForm.BogdanovTakens.cuspCoeff m.field 0
        (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
        (QVDroop.foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
          (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)))
        (cuspW (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))
          (m.q.nq / m.q.emf m.Qf) (m.q.Qtδδ m.δ (m.q.emf m.Qf)))) =
      SignType.sign (-(m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
        m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf))) := by
  have h := m.cuspCoeff_cusp hM hC hE hc hk ha1.ne' hF
  generalize NormalForm.BogdanovTakens.cuspCoeff m.field 0 _ _ _ = X at h ⊢
  have hX : X = m.q.ωq / (2 * (m.q.Ptδ m.δ (m.q.emf m.Qf) +
      m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))) *
      (-(m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) *
        m.q.Ptδδ m.δ (m.q.emf m.Qf))) := by
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    linear_combination h
  rw [hX, sign_mul, sign_pos (by positivity), one_mul]

/-! ## Connection conclusions at the cusp points -/

/-- **A cusp point with `K_t m c ρ < 0` is unstable.** For `M, ω_q > 0`, an equilibrium at a cusp
point of the fold (`C = 0`, `𝔉 = 0`) with `A > 0`, `a + D ω_q K_t > 0` (the other two eigenvalues
in the open left half plane), `E* ≠ 0`, `Q_tδ ≠ 0` and `K_t (n_q/E*) Q_tδ ∂²P_t/∂δ² < 0` is
unstable: the cubic coefficient is positive
(`Dynamics.CenterManifold.unstable_of_cuspCoeff_pos_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_cusp (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0) (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0)
    (hkm : m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
      m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf) < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hkm.ne))
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    have e : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
        m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) =
        m.q.gain m.δ (m.q.emf m.Qf) *
          (m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
      linear_combination (-1 : ℝ) * h0
    rw [e]
    exact mul_ne_zero hk ha1.ne'
  have heq0 : m.field 0 = 0 := by simpa [Model.field] using heq
  refine Dynamics.CenterManifold.unstable_of_cuspCoeff_pos_of_charpoly
    (m.contDiff_field (k := 1)) m.analyticAt_field heq0 (m.isNullPair_fold hM.ne' hC hN)
    (m.charpoly_fold hM.ne' hC) (fun s hs => (Criteria.quadratic_roots_re_neg_iff _ _).mpr
      ⟨div_pos hA hM, div_pos ha1 hM⟩ s (by simpa using hs))
    (m.homological_cusp hM.ne' hC hE hc hF) ?_
  have hs := m.sign_cuspCoeff_cusp hM.ne' hω hC hE hc hk ha1 hF
  rw [sign_pos (neg_pos.mpr hkm)] at hs
  exact sign_eq_one_iff.mp hs

/-- **A cusp point with `K_t m c ρ > 0` is locally asymptotically stable** (and not locally
exponentially stable: `C = 0`), under the hypotheses of `mem_den_unstable_of_cusp` with the
opposite sign (`Dynamics.CenterManifold.localAsymptoticStable_of_cuspCoeff_neg_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_cusp (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0) (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0)
    (hkm : 0 < m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
      m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hkm.ne'))
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    have e : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
        m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) =
        m.q.gain m.δ (m.q.emf m.Qf) *
          (m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
      linear_combination (-1 : ℝ) * h0
    rw [e]
    exact mul_ne_zero hk ha1.ne'
  have heq0 : m.field 0 = 0 := by simpa [Model.field] using heq
  refine Dynamics.CenterManifold.localAsymptoticStable_of_cuspCoeff_neg_of_charpoly
    (m.contDiff_field (k := 1)) m.analyticAt_field heq0 (m.isNullPair_fold hM.ne' hC hN)
    (m.charpoly_fold hM.ne' hC) (fun s hs => (Criteria.quadratic_roots_re_neg_iff _ _).mpr
      ⟨div_pos hA hM, div_pos ha1 hM⟩ s (by simpa using hs))
    (m.homological_cusp hM.ne' hC hE hc hF) ?_
  have hs := m.sign_cuspCoeff_cusp hM.ne' hω hC hE hc hk ha1 hF
  rw [sign_neg (neg_neg_of_pos hkm)] at hs
  exact sign_eq_neg_one_iff.mp hs

/-! ## Stability off the Hopf surface, cusp points included -/

/-- The fold alternative: an equilibrium that is Lyapunov stable, off the Hopf surface and, at a
fold, with `K_t, E*, Q_tδ ≠ 0` and (at a cusp point) `∂²P_t/∂δ² ≠ 0`, has `A, C, G > 0` or is a
cusp point with `A > 0`, `a + D ω_q K_t > 0` and `K_t m c ρ > 0`. -/
@[tmio TM, powerlib_domain] private theorem cusp_alternative_of_lyapunovStable (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 ∧
      (foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
        (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0 → m.q.Ptδδ m.δ (m.q.emf m.Qf) ≠ 0))
    (hl : m ∈ family.den (.flow .lyapunovStable)) :
    m.q.field m.point = 0 ∧ ((0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
      0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
      (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧
        foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
          (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0 ∧
        0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ∧
        0 < m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
          m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf))) := by
  have heq : m.q.field m.point = 0 :=
    Dynamics.isEquilibrium_of_lyapunovStable m.q.contDiff_field
      ((Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field) (pt := Model.point)
        family_isAutonomous).mp hl)
  refine ⟨heq, ?_⟩
  by_cases hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0
  · obtain ⟨hk, hE, hc, hρ⟩ := hfold hC
    by_cases hF : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
        (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0
    · have hρ0 := hρ hF
      have hGe := m.q.routhHopf_eq m.δ (m.q.emf m.Qf)
      rw [hC, mul_zero, sub_zero] at hGe
      rcases (left_ne_zero_of_mul (hGe ▸ hG)).lt_or_gt with hA | hA
      · exact absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
          (mem_den_unstable_of_violation m hM hω heq (Or.inl hA)))
      rcases (right_ne_zero_of_mul (hGe ▸ hG)).lt_or_gt with ha1 | ha1
      · refine absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
          (mem_den_unstable_of_violation m hM hω heq (Or.inr (Or.inr ?_))))
        rw [hGe]
        exact mul_neg_of_pos_of_neg hA ha1
      refine Or.inr ⟨hC, hF, hA, ha1, ?_⟩
      have hμ : m.q.nq / m.q.emf m.Qf ≠ 0 := by
        intro hμ
        have hnq : m.q.nq = 0 := by
          rcases div_eq_zero_iff.mp hμ with h | h
          · exact h
          · exact absurd h hE
        have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
            m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
        rw [hnq, zero_mul, zero_mul, sub_zero] at h0
        have ha0 := (mul_eq_zero.mp h0).resolve_left hk
        rw [hμ, ha0] at hF
        simp only [foldQuad] at hF
        have : m.q.gain m.δ (m.q.emf m.Qf) ^ 2 * (m.q.Qtδ m.δ (m.q.emf m.Qf) *
            m.q.Ptδδ m.δ (m.q.emf m.Qf)) = 0 := by linear_combination -hF
        rcases mul_eq_zero.mp this with h | h
        · exact hk (pow_eq_zero_iff two_ne_zero |>.mp h)
        · exact (mul_ne_zero hc hρ0) h
      rcases lt_trichotomy (m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
          m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)) 0 with h | h | h
      · exact absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
          (mem_den_unstable_of_cusp m hM hω heq hC hA ha1 hE hc hF h))
      · exact absurd h (mul_ne_zero (mul_ne_zero (mul_ne_zero hk hμ) hc) hρ0)
      · exact h
    · exact absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
        (mem_den_unstable_of_fold_of_hopf_ne m hM hω heq hC hG hk hE hF))
  · exact Or.inl ((mem_den_lyapunovStable_iff_of_ne m hM hω hC hG).mp hl).2

/-- **Local asymptotic stability off the Hopf surface, cusp points included.** For `M, ω_q > 0`,
`G ≠ 0` at the selected point and, at a fold (`C = 0`), `K_t ≠ 0`, `E* ≠ 0`, `Q_tδ ≠ 0` and, at a
cusp point, `∂²P_t/∂δ² ≠ 0`: the model is locally asymptotically stable iff the point is an
equilibrium with `A, C, G > 0`, or an equilibrium at a cusp point (`C = 0`, `𝔉 = 0`) with `A > 0`,
`P_tδ + D ω_q K_t > 0` and `K_t (n_q/E*) Q_tδ ∂²P_t/∂δ² > 0` (a negative cubic coefficient). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp
    (m : Model) (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 ∧
      (foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
        (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0 → m.q.Ptδδ m.δ (m.q.emf m.Qf) ≠ 0)) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ ((0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧
          foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
            (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
            (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0 ∧
          0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
          0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ∧
          0 < m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
            m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)))}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  unfold powerlib.TMIO.Statement at hles ⊢
  constructor
  · intro hl
    exact cusp_alternative_of_lyapunovStable m hM hω hG hfold
      (Spectral.den_las_subset_lyapunovStable hl)
  · rintro ⟨heq, h | ⟨hC, hF, hA, ha1, hkm⟩⟩
    · exact Spectral.den_locallyExponentiallyStable_subset_las (hles.mpr ⟨heq, h⟩)
    · obtain ⟨-, hE, hc, -⟩ := hfold hC
      exact mem_den_locallyAsymptoticallyStable_of_cusp m hM hω heq hC hA ha1 hE hc hF hkm

/-- **Lyapunov stability off the Hopf surface, cusp points included**, under the hypotheses of
`mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp`: the same two alternatives. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_hopf_ne_cusp (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 ∧
      (foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
        (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0 → m.q.Ptδδ m.δ (m.q.emf m.Qf) ≠ 0)) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ ((0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧
          foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
            (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
            (m.q.Qtδδ m.δ (m.q.emf m.Qf)) = 0 ∧
          0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
          0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ∧
          0 < m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) *
            m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)))}) := by
  have hlas := mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp m hM hω hG hfold
  unfold powerlib.TMIO.Statement at hlas ⊢
  exact ⟨cusp_alternative_of_lyapunovStable m hM hω hG hfold,
    fun h => Spectral.den_las_subset_lyapunovStable (hlas.mpr h)⟩

/-! ## Witnesses: cusp points of both signs -/

/-- An unstable cusp point with a virtual impedance: `M = D = ω_q = 1`, `n_q = −1`, `E₀ = 1`,
`Q_ref = P_ref = 0`, `V = 1`, `Z_g = j/2`, `Z_v = 1 + j/2`, at `δ* = 0`, `Q_f* = 0` (`E* = 1`:
`K_t = 1/2`, `P_tδ = 1/2`, `Q_tδ = −1/2`, `ρ = −1/2`, `C = 𝔉 = 0`, `K_t m c ρ = −1/8`). -/
def cuspSaddle : Model := ⟨⟨1, 1, 1, -1, 1, 0, 0, 1, 0, 1 / 2, 1, 1 / 2⟩, 0, 0⟩

/-- A locally asymptotically stable cusp point with a virtual impedance: `M = ω_q = 1`, `D = 3`,
`n_q = −1/3`, `E₀ = 2`, `Q_ref = 0`, `P_ref = 1`, `V = 1`, `Z_g = 2j`, `Z_v = 1`, at `δ* = π/2`,
`Q_f* = 3` (`E* = 3`: `K_t = 4/15`, `P_tδ = −3/5`, `Q_tδ = 6/5`, `ρ = −6/5`, `C = 𝔉 = 0`,
`K_t m c ρ = 16/375`). -/
def cuspStable : Model := ⟨⟨1, 3, 1, -1 / 3, 2, 0, 1, 1, 0, 2, 1, 0⟩, Real.pi / 2, 3⟩

/-- **An unstable cusp point with a virtual impedance** (`cuspSaddle`, a positive cubic
coefficient; outside the physical range: `n_q < 0`). -/
@[tmio TM, powerlib_domain] theorem cuspSaddle_mem_den_unstable :
    connection% (cuspSaddle ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable_of_cusp cuspSaddle (by norm_num [cuspSaddle]) (by norm_num [cuspSaddle])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply Dynamics.state3_ext <;> simp [cuspSaddle, Model.point, field, Pt_eq, Qt_eq, emf, ztsq]
  all_goals norm_num [cuspSaddle, routhFold, routhTrace, gain, coupling, Ptδ, PtE, Qtδ, QtE,
    Ptδδ, Qtδδ, emf, ztsq, foldQuad]

/-- **A locally asymptotically stable cusp point with a virtual impedance** (`cuspStable`, a
negative cubic coefficient; outside the physical range: `n_q < 0`). -/
@[tmio TM, powerlib_domain] theorem cuspStable_mem_den_locallyAsymptoticallyStable :
    connection% (cuspStable ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  refine mem_den_locallyAsymptoticallyStable_of_cusp cuspStable (by norm_num [cuspStable])
    (by norm_num [cuspStable]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply Dynamics.state3_ext <;>
      simp [cuspStable, Model.point, field, Pt_eq, Qt_eq, emf, ztsq] <;> norm_num
  all_goals norm_num [cuspStable, routhFold, routhTrace, gain, coupling, Ptδ, PtE, Qtδ, QtE,
    Ptδδ, Qtδδ, emf, ztsq, foldQuad]

end QVDroopVirtual

end powerlib.GFM
