import theorem.GridTiedConverter.GFM.QVDroopFold
import theorem.Dynamics.CuspReduction

/-! # Grid-forming converter with Q–V droop: the cusp points of the fold

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroop.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P(δ, E) − D Δω`, `Q̇_f = ω_q (Q(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, line `Z = R + jX` to a stiff grid `V ∠ 0`, export-positive powers,
  continuous time, autonomous. Read about a selected point (`QVDroop.Model`) on
  `QVDroop.family`. Excluded as there.
* Level: the cubic (cusp) coefficient at the cusp points `C = 0`, `𝔉 = 0` of the fold (static),
  Lyapunov instability and local asymptotic stability there, and the Lyapunov and local
  asymptotic stability decision off the Hopf surface with the cusp points included. Parameters
  are free reals; every theorem lists its range (the physical range is that of
  `theorem/GridTiedConverter/GFM/QVDroop.lean`).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.2 and §8.7 (the cusp
coefficient `c = (1/6)⟨p, C(q, q, q) + 3 B(q, h₂)⟩`, `A h₂ = −B(q, q)`); the cusp laws
`Dynamics.CenterManifold.unstable_of_cuspCoeff_pos_of_charpoly`,
`Dynamics.CenterManifold.localAsymptoticStable_of_cuspCoeff_neg_of_charpoly`
(`theorem/Dynamics/CuspReduction.lean`); the derivative forms, the null pair and the
characteristic polynomial at a fold of `theorem/GridTiedConverter/GFM/QVDroopFold.lean`. The cubic
coefficient was derived with exact computer algebra (sympy: the homological equation solved on
the fold, the numerator reduced modulo `𝔉` by pseudo-division, a polynomial certificate in the
ideal of `C` and `𝔉`) and is proved here by `linear_combination`; the witnesses are exact
rationals.

Results.
* `cuspW` (the homological vector `w = (−W/c, 0, 0)`), `Model.homological_cusp` (`J w = −B(q, q)`
  at `C = 0`, `𝔉 = 0`), **`Model.cuspCoeff_cusp`**: with `a = P_δ`, `c = Q_δ`, `k = K`,
  `m = n_q/E*`, the cubic coefficient of the fold null pair is
  `c₃ = ω_q c² k m/(2 (a + D ω_q k))`; `Model.sign_cuspCoeff_cusp` (`sign c₃ = sign (k m)` for
  `ω_q > 0`, `a + D ω_q k > 0`). On the cusp set with `c ≠ 0`, `k ≠ 0` also `m ≠ 0`, so `c₃ ≠ 0`:
  the remaining degenerate fold points are those with `K = 0` or `Q_δ = 0` (then `P_δ = 0`, so
  `E* V = 0`, `Qδ_ne_zero_of_fold`) and the double-zero set `C = 0`, `G = 0`.
* No cusp point in the physical range: `Pδ_add_mul_QE` (`P_δ + E Q_E = 2 X E²/|Z|²`),
  `Pδ_sq_add_Qδ_sq` (`P_δ² + Q_δ² = (E V)²/|Z|²`), `foldQuad_pos_of_lt` (`𝔉 > 0` for `k, m > 0`,
  `c ≠ 0`, `m a + k > 1`), **`foldQuad_pos_of_physical`** (`X, n_q, E > 0`, `K > 0`, `Q_δ ≠ 0` ⇒
  `𝔉 > 0`), `Qδ_ne_zero_of_fold`, `Model.gain_pos_of_physical` (`K > 0` at every physical
  equilibrium).
* Witnesses (exact rationals at `δ* = 0`, `E* = −1`): `cuspStable` (`K m = −1/10`) and
  `cuspSaddle` (`K m = 1/10`, `X = −2`, `n_q = −1/2`): the cusp set is not empty and both signs
  of `c₃` occur, outside the physical range.

Family and connection conclusions.
No new family: connection conclusions on `QVDroop.family`.
* **`mem_den_unstable_of_cusp`**: for `M, ω_q > 0`, an equilibrium at a cusp point (`C = 0`,
  `𝔉 = 0`) with `A > 0`, `a + D ω_q K > 0`, `E* ≠ 0`, `Q_δ ≠ 0` and `K n_q/E* > 0` is unstable;
  **`mem_den_locallyAsymptoticallyStable_of_cusp`**: with `K n_q/E* < 0` it is locally
  asymptotically stable.
* **`mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp`**,
  **`mem_den_lyapunovStable_iff_of_hopf_ne_cusp`**: for `M, ω_q > 0` off the Hopf surface
  (`G ≠ 0`) and, at a fold, `K, E*, Q_δ ≠ 0`, the model is locally asymptotically (Lyapunov)
  stable iff the point is an equilibrium with `A, C, G > 0`, or a cusp point with `A > 0`,
  `a + D ω_q K > 0` and `K n_q/E* < 0` (no hypothesis `𝔉 ≠ 0`, unlike
  `mem_den_lyapunovStable_iff_of_hopf_ne`).
* In the physical range: **`mem_den_unstable_of_fold_of_physical`** (every physical fold point
  with `A > 0`, `a + D ω_q K > 0` is unstable), **`mem_den_lyapunovStable_iff_of_physical`**,
  **`mem_den_locallyAsymptoticallyStable_iff_of_physical`** (`E* > 0`, `G ≠ 0`: stable iff an
  equilibrium with `A, C, G > 0`, with no fold hypothesis).
* `cuspStable_mem_den_locallyAsymptoticallyStable`,
  `cuspStable_not_mem_den_locallyExponentiallyStable` (local asymptotic stability is strictly
  weaker than local exponential stability in this family), `cuspSaddle_mem_den_unstable`.
-/

noncomputable section
namespace powerlib.GFM.QVDroop
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Criteria (droopJacobian)

variable (q : QVDroop)

/-! ## The homological vector and the cubic coefficient at a cusp point -/

/-- The homological vector `w = (−W/c, 0, 0)` of a cusp point,
`W = a k² − m c² k − m c² + m² a c²` (`ω_q W` is the third component of `B(q, q)` at the fold null
vector `q = (k, 0, c)`). -/
def cuspW (a c k m : ℝ) : State 3 :=
  WithLp.toLp 2 ![-(a * k ^ 2 - m * c ^ 2 * k - m * c ^ 2 + m ^ 2 * a * c ^ 2) / c, 0, 0]

/-- **The homological equation at a cusp point.** At a fold (`C = 0`) with `M ≠ 0`, `E* ≠ 0`,
`c = Q_δ ≠ 0` and a vanishing cusp quadric `𝔉 = 0`: `J w = −B(q, q)` for `w = cuspW` and the fold
null vector `q = foldQ k c`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.homological_cusp (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hc : m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0) :
    fderiv ℝ m.field 0 (cuspW (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf)) =
      -fderiv ℝ (fderiv ℝ m.field) 0
        (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
        (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have v0 := m.fderiv_fderiv_apply_eq_bForm hE (foldQ (m.q.gain m.δ (m.q.emf m.Qf))
    (m.q.Qδ m.δ (m.q.emf m.Qf))) (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) 0
  have v1 := m.fderiv_fderiv_apply_eq_bForm hE (foldQ (m.q.gain m.δ (m.q.emf m.Qf))
    (m.q.Qδ m.δ (m.q.emf m.Qf))) (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) 1
  have v2 := m.fderiv_fderiv_apply_eq_bForm hE (foldQ (m.q.gain m.δ (m.q.emf m.Qf))
    (m.q.Qδ m.δ (m.q.emf m.Qf))) (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) 2
  rw [m.fderiv_field, Model.jacobian, jacobian_eq_droopJacobian]
  generalize fderiv ℝ (fderiv ℝ m.field) 0
    (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
    (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) = v at v0 v1 v2 ⊢
  generalize m.q.Pδ m.δ (m.q.emf m.Qf) = a at h0 v0 v1 v2 hF ⊢
  generalize m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) = b at h0 v0 v1 v2 ⊢
  generalize m.q.Qδ m.δ (m.q.emf m.Qf) = c at h0 v0 v1 v2 hF hc ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 v0 v1 v2 hF ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at v0 v1 v2 hF ⊢
  simp only [bForm, toC, foldQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at v0 v1 v2
  have e1 : v 1 = c / m.q.M * (k * k) + μ * a / m.q.M * (k * c + c * k) -
      μ * (b - μ * c) / m.q.M * (c * c) := by
    apply Complex.ofReal_injective; rw [v1]; push_cast; ring
  have e2 : v 2 = m.q.ωq * (a * k ^ 2 - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * a * c ^ 2) := by
    apply Complex.ofReal_injective; rw [v2]; push_cast; ring
  have hv0 : v 0 = 0 := by apply Complex.ofReal_injective; rw [v0]; simp
  have hM1 : m.q.M * v 1 = c * k ^ 2 + 2 * μ * a * k * c - μ * (b - μ * c) * c ^ 2 := by
    rw [e1]; field_simp; ring
  have key1 : a * (a * k ^ 2 - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * a * c ^ 2) +
      c * (m.q.M * v 1) = 0 := by
    rw [hM1]
    unfold foldQuad at hF
    linear_combination (μ * c ^ 2) * h0 + hF
  have hv1 : v 1 = -(a * (a * k ^ 2 - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * a * c ^ 2)) /
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
`c = Q_δ ≠ 0`, `k = K ≠ 0`, `a + D ω_q k ≠ 0` and `𝔉 = 0`, Kuznetsov's cubic coefficient of the
null pair `(foldQ, foldP)` read with `w = cuspW` is
`2 (a + D ω_q k) c₃ = ω_q c² k m` (`a = P_δ`, `m = n_q/E*`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.cuspCoeff_cusp (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hc : m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0) (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0)
    (ha1 : m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0) :
    2 * (m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) *
      NormalForm.BogdanovTakens.cuspCoeff m.field 0
        (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
        (foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)))
        (cuspW (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf)) =
      m.q.ωq * m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2 * m.q.gain m.δ (m.q.emf m.Qf) *
        (m.q.nq / m.q.emf m.Qf) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  set q3 := foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)) with hq3
  set w3 := cuspW (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
    (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) with hw3
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
  generalize m.q.Pδ m.δ (m.q.emf m.Qf) = a at h0 t0 t1 t2 u0 u1 u2 hF ha1 ⊢
  generalize m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) = b at h0 t0 t1 t2 u0 u1 u2 ⊢
  generalize m.q.Qδ m.δ (m.q.emf m.Qf) = c at h0 t0 t1 t2 u0 u1 u2 hF hc ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 t0 t1 t2 u0 u1 u2 hF hk ha1 ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at t0 t1 t2 u0 u1 u2 hF ⊢
  simp only [cForm, bForm, toC, foldQ, cuspW, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at t0 t1 t2 u0 u1 u2
  have hT0 : T 0 = 0 := by apply Complex.ofReal_injective; rw [t0]; simp
  have hU0 : U 0 = 0 := by apply Complex.ofReal_injective; rw [u0]; simp
  have hT1 : m.q.M * T 1 = a * k ^ 3 - 3 * μ * c ^ 2 * k ^ 2 := by
    have e : T 1 = a / m.q.M * (k * k * k) -
        μ * c / m.q.M * (k * k * c + k * c * k + c * k * k) := by
      apply Complex.ofReal_injective; rw [t1]; push_cast; ring
    rw [e]; field_simp; ring
  have hT2 : T 2 = -(m.q.ωq * c * k ^ 3) - 3 * m.q.ωq * μ * a * k ^ 2 * c := by
    apply Complex.ofReal_injective; rw [t2]; push_cast; ring
  have hU1 : m.q.M * U 1 = -(a * k ^ 2 - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * a * c ^ 2) *
      (k + μ * a) := by
    have e : U 1 = c / m.q.M * (k * (-(a * k ^ 2 - μ * c ^ 2 * k - μ * c ^ 2 +
        μ ^ 2 * a * c ^ 2) / c)) + μ * a / m.q.M * (k * 0 + c * (-(a * k ^ 2 - μ * c ^ 2 * k -
        μ * c ^ 2 + μ ^ 2 * a * c ^ 2) / c)) - μ * (b - μ * c) / m.q.M * (c * 0) := by
      apply Complex.ofReal_injective; rw [u1]; push_cast; ring
    rw [e]; field_simp; ring
  have hU2 : c * U 2 = -(m.q.ωq * (a * k ^ 2 - μ * c ^ 2 * k - μ * c ^ 2 + μ ^ 2 * a * c ^ 2)) *
      (a * k - μ * c ^ 2) := by
    have e : U 2 = m.q.ωq * a * (k * (-(a * k ^ 2 - μ * c ^ 2 * k - μ * c ^ 2 +
        μ ^ 2 * a * c ^ 2) / c)) - m.q.ωq * μ * c * (k * 0 + c * (-(a * k ^ 2 - μ * c ^ 2 * k -
        μ * c ^ 2 + μ ^ 2 * a * c ^ 2) / c)) + m.q.ωq * μ * (k - 1 + μ * a) * (c * 0) := by
      apply Complex.ofReal_injective; rw [u2]; push_cast; ring
    rw [e]; field_simp; ring
  simp only [foldP, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hT0, hU0]
  have hN2 : m.q.D * m.q.ωq * k ^ 2 + b * c ≠ 0 := by
    have e : m.q.D * m.q.ωq * k ^ 2 + b * c = k * (a + m.q.D * m.q.ωq * k) := by
      linear_combination (-1 : ℝ) * h0
    rw [e]; exact mul_ne_zero hk ha1
  field_simp
  refine mul_left_cancel₀ (pow_ne_zero 2 hc) ?_
  unfold foldQuad at hF
  linear_combination (2 * (a + m.q.D * m.q.ωq * k) * c ^ 2 * m.q.ωq * k) * hT1 +
    (2 * (a + m.q.D * m.q.ωq * k) * c ^ 2 * 3 * m.q.ωq * k) * hU1 +
    (2 * (a + m.q.D * m.q.ωq * k) * c ^ 2 * b) * hT2 +
    (2 * (a + m.q.D * m.q.ωq * k) * 3 * b * c) * hU2 +
    (2 * (a + m.q.D * m.q.ωq * k) * (m.q.ωq * (3 * a ^ 2 * c ^ 2 * k * μ ^ 2 + 3 * a ^ 2 * k ^ 3 -
      3 * a * c ^ 4 * μ ^ 3 - 3 * a * c ^ 2 * k ^ 2 * μ - 3 * a * c ^ 2 * k * μ +
      3 * c ^ 4 * k * μ ^ 2 + 3 * c ^ 4 * μ ^ 2 + c ^ 2 * k ^ 3)) +
      6 * m.q.ωq * k * c ^ 4 * μ) * h0 +
    (2 * (a + m.q.D * m.q.ωq * k) * (-3 * a * k ^ 2 * m.q.ωq)) * hF

/-- **The sign of the cubic coefficient at a cusp point**: under the hypotheses of
`Model.cuspCoeff_cusp` with `ω_q > 0` and `a + D ω_q k > 0`, `c₃` has the sign of `k m`
(`k = K`, `m = n_q/E*`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_cuspCoeff_cusp (m : Model) (hM : m.q.M ≠ 0)
    (hω : 0 < m.q.ωq) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hc : m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0) (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0)
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hF : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0) :
    SignType.sign (NormalForm.BogdanovTakens.cuspCoeff m.field 0
        (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
        (foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)))
        (cuspW (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf))) =
      SignType.sign (m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf)) := by
  have h := m.cuspCoeff_cusp hM hC hE hc hk ha1.ne' hF
  generalize NormalForm.BogdanovTakens.cuspCoeff m.field 0 _ _ _ = X at h ⊢
  have hc2 : 0 < m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2 := lt_of_le_of_ne (sq_nonneg _)
    (Ne.symm (pow_ne_zero 2 hc))
  have hX : X = m.q.ωq * m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2 /
      (2 * (m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))) *
      (m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf)) := by
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    linear_combination h
  rw [hX, sign_mul, sign_pos (by positivity), one_mul]

/-! ## Connection conclusions at the cusp points -/

/-- **A cusp point with `K n_q/E* > 0` is unstable.** For `M, ω_q > 0`, an equilibrium at a cusp
point of the fold (`C = 0`, `𝔉 = 0`) with `A > 0`, `a + D ω_q K > 0` (the other two eigenvalues in
the open left half plane), `E* ≠ 0`, `Q_δ ≠ 0` and `K n_q/E* > 0` is unstable: the cubic
coefficient is `ω_q Q_δ² K n_q/(2 E* (a + D ω_q K)) > 0`
(`Dynamics.CenterManifold.unstable_of_cuspCoeff_pos_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_cusp (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0) (hc : m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0)
    (hkm : 0 < m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 := left_ne_zero_of_mul hkm.ne'
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    have e : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
        m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) =
        m.q.gain m.δ (m.q.emf m.Qf) *
          (m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
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
  rw [sign_pos hkm] at hs
  exact sign_eq_one_iff.mp hs

/-- **A cusp point with `K n_q/E* < 0` is locally asymptotically stable** (and not locally
exponentially stable: `C = 0`). Under the hypotheses of `mem_den_unstable_of_cusp` with
`K n_q/E* < 0`, the cubic coefficient is negative
(`Dynamics.CenterManifold.localAsymptoticStable_of_cuspCoeff_neg_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_cusp (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0) (hc : m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0)
    (hF : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0)
    (hkm : m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 := left_ne_zero_of_mul hkm.ne
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    have e : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
        m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) =
        m.q.gain m.δ (m.q.emf m.Qf) *
          (m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
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
  rw [sign_neg hkm] at hs
  exact sign_eq_neg_one_iff.mp hs

/-! ## The physical range has no cusp point -/

/-- `P_δ + E Q_E = 2 X E²/|Z|²` at every `(δ, E)`: the angle terms cancel. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Pδ_add_mul_QE (δ E : ℝ) :
    q.Pδ δ E + E * q.QE δ E = 2 * q.X * E ^ 2 / q.zsq := by
  simp only [Pδ, QE]
  ring

/-- `P_δ² + Q_δ² = (E V)²/|Z|²` (`|Z|² ≠ 0`): the slopes are a rotation of `E V e^{jδ}`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Pδ_sq_add_Qδ_sq (hz : q.zsq ≠ 0) (δ E : ℝ) :
    q.Pδ δ E ^ 2 + q.Qδ δ E ^ 2 = (E * q.V) ^ 2 / q.zsq := by
  simp only [Pδ, Qδ]
  field_simp
  have h := Real.sin_sq_add_cos_sq δ
  unfold zsq
  linear_combination (E * q.V) ^ 2 * (q.R ^ 2 + q.X ^ 2) * h

/-- **The cusp quadric is positive off a strip**: for `k > 0`, `m > 0`, `c ≠ 0` and
`m a + k > 1`, `𝔉 = (a² + c²)(c² m² + k²) − a c² m > 0` (`m² 𝔉 = (s² + t²)(t² + k²) − s t²`,
`s = m a`, `t = m c`, a sum of squares plus `t² s (s + k − 1) ≥ 0` for `s ≥ 0`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem foldQuad_pos_of_lt {a c k m : ℝ} (hk : 0 < k) (hm : 0 < m)
    (hc : c ≠ 0) (hs : 1 < m * a + k) : 0 < foldQuad a c k m := by
  have ht : 0 < (m * c) ^ 2 := lt_of_le_of_ne (sq_nonneg _)
    (Ne.symm (pow_ne_zero 2 (mul_ne_zero hm.ne' hc)))
  have key : m ^ 2 * foldQuad a c k m = ((m * a) ^ 2 + (m * c) ^ 2) * ((m * c) ^ 2 + k ^ 2) -
      m * a * (m * c) ^ 2 := by
    unfold foldQuad; ring
  have hpos : 0 < ((m * a) ^ 2 + (m * c) ^ 2) * ((m * c) ^ 2 + k ^ 2) - m * a * (m * c) ^ 2 := by
    rcases le_or_gt 0 (m * a) with h0 | h0
    · have e : ((m * a) ^ 2 + (m * c) ^ 2) * ((m * c) ^ 2 + k ^ 2) - m * a * (m * c) ^ 2 =
          ((m * c) ^ 2 - m * a * k / 2) ^ 2 + 3 / 4 * (m * a) ^ 2 * k ^ 2 + k ^ 2 * (m * c) ^ 2 +
            (m * c) ^ 2 * (m * a) * (m * a + k - 1) := by ring
      rw [e]
      have h1 : 0 ≤ (m * c) ^ 2 * (m * a) * (m * a + k - 1) :=
        mul_nonneg (mul_nonneg ht.le h0) (by linarith)
      have h2 : 0 < k ^ 2 * (m * c) ^ 2 := mul_pos (pow_pos hk 2) ht
      positivity
    · have h1 : 0 < ((m * c) ^ 2) ^ 2 := pow_pos ht 2
      nlinarith [sq_nonneg (m * a), sq_nonneg k, mul_pos (neg_pos.mpr h0) ht]
  have hm2 : 0 < m ^ 2 := pow_pos hm 2
  rw [← key] at hpos
  exact pos_of_mul_pos_right hpos hm2.le

/-- **No cusp point in the physical range**: for `X > 0`, `n_q > 0`, `E > 0`, `K = 1 + n_q Q_E > 0`
and `Q_δ ≠ 0`, the cusp quadric is positive, `𝔉(P_δ, Q_δ, K, n_q/E) > 0`
(`m P_δ + K − 1 = 2 n_q X E/|Z|² > 0` by `Pδ_add_mul_QE`, then `foldQuad_pos_of_lt`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem foldQuad_pos_of_physical (hX : 0 < q.X) (hnq : 0 < q.nq)
    {δ E : ℝ} (hE : 0 < E) (hk : 0 < q.gain δ E) (hc : q.Qδ δ E ≠ 0) :
    0 < foldQuad (q.Pδ δ E) (q.Qδ δ E) (q.gain δ E) (q.nq / E) := by
  refine foldQuad_pos_of_lt hk (div_pos hnq hE) hc ?_
  have h := q.Pδ_add_mul_QE δ E
  have hz := q.zsq_pos hX.ne'
  have e : q.nq / E * q.Pδ δ E + q.gain δ E = 1 + 2 * q.nq * q.X * E / q.zsq := by
    have e2 : q.nq / E * q.Pδ δ E + q.gain δ E = 1 + q.nq / E * (q.Pδ δ E + E * q.QE δ E) := by
      rw [gain]; field_simp; ring
    rw [e2, h]; field_simp
  rw [e]
  have : 0 < 2 * q.nq * q.X * E / q.zsq := by positivity
  linarith

/-- At a fold with `K ≠ 0`, `E V ≠ 0` and `|Z|² ≠ 0` the angle slope of `Q` does not vanish:
`Q_δ = 0` would give `P_δ = 0` (`C = K P_δ − n_q P_E Q_δ`), against
`P_δ² + Q_δ² = (E V)²/|Z|² > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Qδ_ne_zero_of_fold (hz : q.zsq ≠ 0) {δ E : ℝ}
    (hEV : E * q.V ≠ 0) (hk : q.gain δ E ≠ 0) (hC : q.routhFold δ E = 0) : q.Qδ δ E ≠ 0 := by
  intro hc
  have hP : q.Pδ δ E = 0 := by
    have h0 : q.gain δ E * q.Pδ δ E - q.nq * q.PE δ E * q.Qδ δ E = 0 := hC
    rw [hc, mul_zero, sub_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hk
  have h := q.Pδ_sq_add_Qδ_sq hz δ E
  rw [hP, hc] at h
  have : (E * q.V) ^ 2 / q.zsq ≠ 0 := div_ne_zero (pow_ne_zero 2 hEV) hz
  apply this
  rw [← h]
  ring

/-- In the physical range (`M, ω_q, n_q, X > 0`, `E₀ + n_q Q_ref > 0`) the gain `K` is positive at
every physical equilibrium (`E* > 0`): `K = √disc` on the physical branch
(`QVDroop.emf_eq_Eplus`, `QVDroop.one_add_nq_QE_Eplus`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.gain_pos_of_physical (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref)
    (heq : m.q.field m.point = 0) (hE : 0 < m.q.emf m.Qf) :
    0 < m.q.gain m.δ (m.q.emf m.Qf) := by
  have h2 := m.q.a2_pos hnq hX
  have h0 := m.q.a0_neg hlev
  have hEq : m.q.emf m.Qf = m.q.Eplus m.δ := by
    simpa [Model.point] using m.q.emf_eq_Eplus hM.ne' hω.ne' h2 h0 heq (by simpa [Model.point])
  rw [gain, hEq]
  exact (m.q.one_add_nq_QE_Eplus h2 h0 m.δ).2

/-- **Every physical fold point is a nondegenerate saddle-node.** In the physical range
(`M, ω_q, n_q, X, V > 0`, `E₀ + n_q Q_ref > 0`) an equilibrium with `E* > 0` at a fold (`C = 0`)
with `A > 0` and `P_δ + D ω_q K > 0` is unstable: `K > 0`, `Q_δ ≠ 0` and `𝔉 > 0` there
(`foldQuad_pos_of_physical`), so `mem_den_unstable_of_fold` applies with no further hypothesis. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_physical (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X) (hV : 0 < m.q.V)
    (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hk := m.gain_pos_of_physical hM hω hnq hX hlev heq hE
  have hc := m.q.Qδ_ne_zero_of_fold (m.q.zsq_pos hX.ne').ne' (mul_ne_zero hE.ne' hV.ne') hk.ne' hC
  exact mem_den_unstable_of_fold m hM hω heq hC hA ha1 hk.ne' hE.ne'
    (m.q.foldQuad_pos_of_physical hX hnq hE hk hc).ne'

/-- **Lyapunov stability in the physical range off the Hopf surface.** For `M, ω_q, n_q, X, V > 0`,
`E₀ + n_q Q_ref > 0`, `E* > 0` and `G ≠ 0` at the selected point, the model is Lyapunov stable iff
the point is an equilibrium with `A, C, G > 0`: no fold hypothesis is left
(`mem_den_lyapunovStable_iff_of_hopf_ne` with `foldQuad_pos_of_physical`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_physical (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X) (hV : 0 < m.q.V)
    (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (hE : 0 < m.q.emf m.Qf)
    (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  by_cases heq : m.q.field m.point = 0
  · have hk := m.gain_pos_of_physical hM hω hnq hX hlev heq hE
    refine mem_den_lyapunovStable_iff_of_hopf_ne m hM hω hG fun hC => ⟨hk.ne', hE.ne', ?_⟩
    exact (m.q.foldQuad_pos_of_physical hX hnq hE hk (m.q.Qδ_ne_zero_of_fold
      (m.q.zsq_pos hX.ne').ne' (mul_ne_zero hE.ne' hV.ne') hk.ne' hC)).ne'
  · unfold powerlib.TMIO.Statement
    refine ⟨fun hl => absurd (Dynamics.isEquilibrium_of_lyapunovStable m.q.contDiff_field
      ((Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field) (pt := Model.point)
        family_isAutonomous).mp hl)) heq, fun h => absurd h.1 heq⟩

/-- **Local asymptotic stability in the physical range off the Hopf surface**, under the hypotheses
of `mem_den_lyapunovStable_iff_of_physical`: iff an equilibrium with `A, C, G > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_physical
    (m : Model) (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hV : 0 < m.q.V) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (hE : 0 < m.q.emf m.Qf)
    (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  have hly := mem_den_lyapunovStable_iff_of_physical m hM hω hnq hX hV hlev hE hG
  unfold powerlib.TMIO.Statement at hles hly ⊢
  exact ⟨fun h => hly.mp (Spectral.den_las_subset_lyapunovStable h),
    fun h => Spectral.den_locallyExponentiallyStable_subset_las (hles.mpr h)⟩

/-! ## Stability off the Hopf surface, cusp points included -/

/-- The fold alternative: an equilibrium that is Lyapunov stable, off the Hopf surface and, at a
fold, with `K, E*, Q_δ ≠ 0`, has `A, C, G > 0` or is a cusp point with `A > 0`, `a + D ω_q K > 0`
and `K n_q/E* < 0`. -/
@[tmio TM, powerlib_domain] private theorem cusp_alternative_of_lyapunovStable (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0)
    (hl : m ∈ family.den (.flow .lyapunovStable)) :
    m.q.field m.point = 0 ∧ ((0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
      0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
      (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧
        foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0 ∧
        0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ∧
        m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) < 0)) := by
  have heq : m.q.field m.point = 0 :=
    Dynamics.isEquilibrium_of_lyapunovStable m.q.contDiff_field
      ((Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field) (pt := Model.point)
        family_isAutonomous).mp hl)
  refine ⟨heq, ?_⟩
  by_cases hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0
  · obtain ⟨hk, hE, hc⟩ := hfold hC
    by_cases hF : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0
    · have hGe := m.q.routhHopf_eq m.δ (m.q.emf m.Qf)
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
      rcases lt_trichotomy (m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf)) 0 with
        h | h | h
      · exact h
      · exfalso
        have hμ : m.q.nq / m.q.emf m.Qf = 0 := (mul_eq_zero.mp h).resolve_left hk
        rw [hμ] at hF
        simp only [foldQuad] at hF
        have hc2 : 0 < m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2 := lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (pow_ne_zero 2 hc))
        have hk2 : 0 < m.q.gain m.δ (m.q.emf m.Qf) ^ 2 := lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (pow_ne_zero 2 hk))
        nlinarith [sq_nonneg (m.q.Pδ m.δ (m.q.emf m.Qf)), mul_pos hc2 hk2]
      · exact absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
          (mem_den_unstable_of_cusp m hM hω heq hC hA ha1 hE hc hF h))
    · exact absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
        (mem_den_unstable_of_fold_of_hopf_ne m hM hω heq hC hG hk hE hF))
  · exact Or.inl ((mem_den_lyapunovStable_iff_of_ne m hM hω hC hG).mp hl).2

/-- **Local asymptotic stability off the Hopf surface, cusp points included.** For `M, ω_q > 0`,
`G ≠ 0` at the selected point and, at a fold (`C = 0`), `K ≠ 0`, `E* ≠ 0`, `Q_δ ≠ 0`: the model is
locally asymptotically stable iff the point is an equilibrium with `A, C, G > 0`, or an equilibrium
at a cusp point (`C = 0`, `𝔉 = 0`) with `A > 0`, `P_δ + D ω_q K > 0` and `K n_q/E* < 0` (a
negative cubic coefficient). The cusp alternative is locally asymptotically but not locally
exponentially stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp
    (m : Model) (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ ((0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧
          foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
            (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0 ∧
          0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
          0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ∧
          m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) < 0))}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  unfold powerlib.TMIO.Statement at hles ⊢
  constructor
  · intro hl
    exact cusp_alternative_of_lyapunovStable m hM hω hG hfold
      (Spectral.den_las_subset_lyapunovStable hl)
  · rintro ⟨heq, h | ⟨hC, hF, hA, ha1, hkm⟩⟩
    · exact Spectral.den_locallyExponentiallyStable_subset_las (hles.mpr ⟨heq, h⟩)
    · obtain ⟨-, hE, hc⟩ := hfold hC
      exact mem_den_locallyAsymptoticallyStable_of_cusp m hM hω heq hC hA ha1 hE hc hF hkm

/-- **Lyapunov stability off the Hopf surface, cusp points included**, under the hypotheses of
`mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp`: the same two alternatives. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_hopf_ne_cusp (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ ((0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧
          foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
            (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0 ∧
          0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
          0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ∧
          m.q.gain m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf) < 0))}) := by
  have hlas := mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne_cusp m hM hω hG hfold
  unfold powerlib.TMIO.Statement at hlas ⊢
  exact ⟨cusp_alternative_of_lyapunovStable m hM hω hG hfold,
    fun h => Spectral.den_las_subset_lyapunovStable (hlas.mpr h)⟩

/-! ## Witnesses: cusp points of both signs -/

/-- A cusp point with a negative cubic coefficient: `M = ω_q = 1`, `D = 5`, `n_q = 1/2`,
`E₀ = −2/5`, `Q_ref = 0`, `P_ref = 3/5`, `V = 2`, `R = 1`, `X = 2`, at `δ* = 0`, `Q_f* = 6/5`
(`E* = −1`, a negative EMF: `K = 1/5`, `n_q/E* = −1/2`, `C = 𝔉 = 0`). -/
def cuspStable : Model := ⟨⟨1, 5, 1, 1 / 2, -2 / 5, 0, 3 / 5, 2, 1, 2⟩, 0, 6 / 5⟩

/-- A cusp point with a positive cubic coefficient: `M = ω_q = D = 1`, `n_q = −1/2`,
`E₀ = −2/5`, `Q_ref = 0`, `P_ref = 3/5`, `V = 2`, `R = 1`, `X = −2`, at `δ* = 0`, `Q_f* = −6/5`
(`E* = −1`: `K = 1/5`, `n_q/E* = 1/2`, `C = 𝔉 = 0`). -/
def cuspSaddle : Model := ⟨⟨1, 1, 1, -1 / 2, -2 / 5, 0, 3 / 5, 2, 1, -2⟩, 0, -6 / 5⟩

/-- **A locally asymptotically stable cusp point** (`cuspStable`, `K n_q/E* = −1/10 < 0`). -/
@[tmio TM, powerlib_domain] theorem cuspStable_mem_den_locallyAsymptoticallyStable :
    connection% (cuspStable ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  refine mem_den_locallyAsymptoticallyStable_of_cusp cuspStable (by norm_num [cuspStable])
    (by norm_num [cuspStable]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply Dynamics.state3_ext <;> simp [cuspStable, Model.point, field, P_eq, Q_eq, emf, zsq] <;>
      norm_num
  all_goals norm_num [cuspStable, routhFold, routhTrace, gain, coupling, Pδ, PE, Qδ, QE, emf, zsq,
    foldQuad]

/-- The cusp point `cuspStable` is not locally exponentially stable (`C = 0`): local asymptotic
stability in the Q–V droop family is strictly weaker than local exponential stability. -/
@[tmio TM, powerlib_domain] theorem cuspStable_not_mem_den_locallyExponentiallyStable :
    connection% (cuspStable ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have hles := mem_den_locallyExponentiallyStable_iff cuspStable (by norm_num [cuspStable])
    (by norm_num [cuspStable])
  unfold powerlib.TMIO.Statement at hles ⊢
  intro h
  have hC := (hles.mp h).2.2.1
  norm_num [cuspStable, routhFold, gain, coupling, Pδ, PE, Qδ, QE, emf, zsq] at hC

/-- **An unstable cusp point** (`cuspSaddle`, `K n_q/E* = 1/10 > 0`). -/
@[tmio TM, powerlib_domain] theorem cuspSaddle_mem_den_unstable :
    connection% (cuspSaddle ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable_of_cusp cuspSaddle (by norm_num [cuspSaddle]) (by norm_num [cuspSaddle])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply Dynamics.state3_ext <;> simp [cuspSaddle, Model.point, field, P_eq, Q_eq, emf, zsq] <;>
      norm_num
  all_goals norm_num [cuspSaddle, routhFold, routhTrace, gain, coupling, Pδ, PE, Qδ, QE, emf, zsq,
    foldQuad]

end QVDroop

end powerlib.GFM
