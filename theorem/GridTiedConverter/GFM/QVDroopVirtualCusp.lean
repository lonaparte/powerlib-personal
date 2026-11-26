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
  asymptotic stability decision off the Hopf surface with the cusp points included; the
  location of the cusp set relative to the physical range (`n_q, X_g, E* > 0`, `X_v ≥ 0`, any
  `R_g`, `R_v`) and the fold coefficient at the folds with `Q_tδ = 0`. Parameters are free reals;
  every theorem lists its range.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.2 and §8.7 (the cusp
coefficient `c = (1/6)⟨p, C(q, q, q) + 3 B(q, h₂)⟩`, `A h₂ = −B(q, q)`); the cusp laws
`Dynamics.CenterManifold.unstable_of_cuspCoeff_pos_of_charpoly`,
`Dynamics.CenterManifold.localAsymptoticStable_of_cuspCoeff_neg_of_charpoly`
(`theorem/Dynamics/CuspReduction.lean`); the derivative forms (with the angle curvatures
`ρ = ∂²P_t/∂δ²`, `τ = ∂²Q_t/∂δ²`), the null pair `QVDroop.foldQ`, `QVDroop.foldP` and the
characteristic polynomial at a fold of `theorem/GridTiedConverter/GFM/QVDroopVirtualFold.lean`. The
cubic coefficient was derived with exact computer algebra (sympy: the homological equation solved
on the fold, the numerator reduced modulo `𝔉`, which is linear in `ρ`, a polynomial certificate in
the ideal of `C` and `𝔉`) and is proved here by `linear_combination`. The exclusion of physical cusp
points was derived with exact computer algebra as well (sympy: `𝔉` linear in `ρ`, the fold linear
in `r = 2 R_g E*²/|Z_t|²`, both eliminated; the virtual-reactance condition `X_v ≥ 0` read as the
sign of the reactance minor; the remainder `−(a² N + N₀)` with `N₀ > 0` and case certificates
for `N ≥ 0`, for the sign with the offset `a = (1 + k²/(m c)² + e) m (a τ − c ρ)`, `e ≥ 0`) and
is proved by `linear_combination` and `nlinarith`.

Results.
* `cuspW` (the homological vector `w = (−W/c, 0, 0)`), `Model.homological_cusp` (`J w = −B(q, q)`
  at `C = 0`, `𝔉 = 0`), **`Model.cuspCoeff_cusp`**: with `a = P_tδ`, `c = Q_tδ`, `k = K_t`,
  `m = n_q/E*`, `ρ = ∂²P_t/∂δ²`, the cubic coefficient of the fold null pair is
  `c₃ = −ω_q k m c ρ/(2 (a + D ω_q k))`; `Model.sign_cuspCoeff_cusp`
  (`sign c₃ = sign (−k m c ρ)` for `ω_q > 0`, `a + D ω_q k > 0`). For `Z_v = 0` (`ρ = −c`) it is
  the coefficient `ω_q c² k m/(2 (a + D ω_q k))` of
  `theorem/GridTiedConverter/GFM/QVDroopCusp.lean`.
* The remaining degenerate set: on the cusp set with `c, k ≠ 0`, `m = 0` forces `ρ = 0`, so
  `c₃ = 0` exactly when `ρ = 0`; these cusp points, the fold points with `K_t = 0`, the folds with
  `Q_tδ = 0` and `b τ = k ρ` (below) are located, not decided; the double-zero set `C = 0`,
  `G = 0` is decided in `theorem/GridTiedConverter/GFM/QVDroopVirtualBT.lean`.
* No cusp point on an inductive fold: `mul_QtE_add_Qtδδ` (`E ∂Q_t/∂E + τ = 2 X_g E²/|Z_t|²`),
  `mul_PtE_add_Ptδδ` (`E ∂P_t/∂E + ρ = 2 R_g E²/|Z_t|²`), so `k = 1 + m (x − τ)`,
  `b = m (r − ρ)` with `x, r = 2 X_g E²/|Z_t|², 2 R_g E²/|Z_t|²`; `reactanceMinor_eq`
  (`(a² + ρ² − c² − τ²) x − 2 (a c + ρ τ) r = 8 E⁴ V² X_v |Z_g|²/|Z_t|⁶`, the sign of `X_v`);
  `foldQuad_ne_zero_of_fold` (pure algebra: `m, x > 0`, `c ≠ 0`, the fold and a nonnegative minor
  give `𝔉 ≠ 0`) and **`foldQuad_ne_zero_of_physical`** (`X_g, n_q, E > 0`, `X_v ≥ 0`, `C = 0`,
  `Q_tδ ≠ 0` ⇒ `𝔉 ≠ 0`, for all `R_g`, `R_v`, with no balance or level hypothesis): the cusp set
  with `Q_tδ ≠ 0` does not meet the physical range. `Ptδ_mul_Qtδδ_sub`
  (`a τ − c ρ = dz (E V)²/|Z_t|⁴`); the sign: `mul_foldQuad_pos_of_fold` (`(a τ − c ρ) 𝔉 > 0`)
  and **`dz_mul_foldQuad_pos_of_physical`** (`dz 𝔉 > 0` for `dz ≠ 0`: on a physical fold the
  cusp quantity, hence the fold coefficient up to the factor `k ω_q/(2 c (D ω_q k² + b c))`, has
  the sign of `|Z_g|² − |Z_v|²`). `Qtδ_ne_zero_of_fold` (`Q_tδ ≠ 0` at a fold with `K_t ≠ 0`,
  `E V ≠ 0`, `dz ≠ 0`); `Model.gain_pos_of_physical` (`K_t > 0` at every physical equilibrium).
* The folds with `Q_tδ = 0` (then `P_tδ = 0`; in the physical range only for `dz = 0`, where
  `𝔉 = 0` trivially): `Model.foldCoeff_fold_of_Qtδ_eq_zero` (the fold coefficient is
  `(b τ − k ρ)/(2 D)`). The witness `dzFold` (`dzFold_fold`: a physical equilibrium with
  `Z_g = Z_v = j` at a fold with `Q_tδ = 0`, `𝔉 = 0`) shows that the cusp set meets the physical
  range there, and only there.
* Witnesses (exact rationals with `Z_v ≠ 0`, outside the physical range: `n_q < 0`):
  `cuspSaddle` (`δ* = 0`, `K_t m c ρ = −1/8`) and `cuspStable` (`δ* = π/2`,
  `K_t m c ρ = 16/375`): both signs of `c₃` occur.

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
* `mem_den_unstable_of_fold_of_Qtδ_eq_zero`: an equilibrium at a fold with `Q_tδ = 0`, `A > 0`,
  `P_tδ + D ω_q K_t > 0`, `K_t, E* ≠ 0` and `b τ ≠ k ρ` is unstable (a saddle-node).
* **`mem_den_unstable_of_fold_of_physical`**: in the physical range (`M, ω_q, n_q, X_g > 0`,
  `X_v ≥ 0`, `E₀ + n_q Q_ref > 0`, `E* > 0`) every fold equilibrium with `Q_tδ ≠ 0`, `A > 0`,
  `P_tδ + D ω_q K_t > 0` is unstable, with no hypothesis on `𝔉`. The complete physical-range
  membership is in `theorem/GridTiedConverter/GFM/QVDroopVirtualMembership.lean`.
* `cuspSaddle_mem_den_unstable`, `cuspStable_mem_den_locallyAsymptoticallyStable`,
  `dzFold_mem_den_unstable` (`b τ − k ρ = 3/4`).
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

/-! ## No cusp point on an inductive fold -/

/-- The polynomial `N₂(C, x, y) = x C³ + e₂ C² + (x − y + 1)² f₁ C + y² (x + 2)(x − y + 1)⁴` of the
cusp exclusion is nonnegative for `C, x ≥ 0`: `(3x + 2) e₂` is a square plus `x² (2x² + 6x + 3)`;
for `f₁ ≥ 0` every term is nonnegative; for `f₁ < 0` (then `y > 1/2`, `x < 1/8`) the quadratic
part in `(C, (x − y + 1)²)` has discriminant `−(x − y + 1)² Dr ≥ 0`, `Dr < 0`. -/
@[tmio T, powerlib_foundation] private theorem cuspN2_nonneg {C x y : ℝ} (hC : 0 ≤ C)
    (hx : 0 ≤ x) :
    0 ≤ x * C ^ 3 + (2 * x ^ 3 - 4 * x ^ 2 * y + 6 * x ^ 2 + 3 * x * y ^ 2 - 8 * x * y + 5 * x +
      2 * y ^ 2 - 4 * y + 2) * C ^ 2 + (x - y + 1) ^ 2 * (x ^ 3 - 2 * x ^ 2 * y + 4 * x ^ 2 +
      3 * x * y ^ 2 - 6 * x * y + 5 * x + 4 * y ^ 2 - 6 * y + 2) * C +
      y ^ 2 * (x + 2) * (x - y + 1) ^ 4 := by
  generalize he : 2 * x ^ 3 - 4 * x ^ 2 * y + 6 * x ^ 2 + 3 * x * y ^ 2 - 8 * x * y + 5 * x +
    2 * y ^ 2 - 4 * y + 2 = e2
  generalize hf : x ^ 3 - 2 * x ^ 2 * y + 4 * x ^ 2 + 3 * x * y ^ 2 - 6 * x * y + 5 * x +
    4 * y ^ 2 - 6 * y + 2 = f1
  generalize hK : x - y + 1 = K
  have h3 : 0 < 3 * x + 2 := by linarith
  have hE2 : (3 * x + 2) * e2 = ((3 * x + 2) * y - 2 * (x + 1) ^ 2) ^ 2 +
      x ^ 2 * (2 * x ^ 2 + 6 * x + 3) := by rw [← he]; ring
  have he2 : 0 ≤ e2 := by
    have : 0 ≤ (3 * x + 2) * e2 := by rw [hE2]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) h3
  have hxC : 0 ≤ x * C ^ 3 := by positivity
  rcases le_or_gt 0 f1 with hf1 | hf1
  · have : 0 ≤ K ^ 2 * f1 * C := by positivity
    have : 0 ≤ e2 * C ^ 2 := by positivity
    have : 0 ≤ y ^ 2 * (x + 2) * K ^ 4 := by positivity
    linarith
  · -- f₁ < 0 forces `y > 1/2` and `x < 1/8`, where the discriminant `−K² Dr` is nonnegative
    have hy : 1 / 2 < y := by
      have e : f1 - x * (4 * x ^ 2 + 12 * x + 11) / 4 =
          (y - 1 / 2) * ((3 * x + 4) * (y + 1 / 2) - (2 * x ^ 2 + 6 * x + 6)) := by
        rw [← hf]; ring
      by_contra hle
      push Not at hle
      have h1 : (3 * x + 4) * (y + 1 / 2) - (2 * x ^ 2 + 6 * x + 6) < 0 := by nlinarith
      have h2 : 0 ≤ (y - 1 / 2) * ((3 * x + 4) * (y + 1 / 2) - (2 * x ^ 2 + 6 * x + 6)) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) h1.le
      have h4 : 0 ≤ x * (4 * x ^ 2 + 12 * x + 11) / 4 := by positivity
      linarith
    have hx8 : x < 1 / 8 := by
      have e : 4 * (3 * x + 4) * f1 = (2 * (3 * x + 4) * y - (2 * x ^ 2 + 6 * x + 6)) ^ 2 +
          8 * x ^ 4 + 40 * x ^ 3 + 64 * x ^ 2 + 32 * x - 4 := by rw [← hf]; ring
      have h1 : 4 * (3 * x + 4) * f1 < 0 := by
        have : 0 < 4 * (3 * x + 4) := by linarith
        exact mul_neg_of_pos_of_neg this hf1
      nlinarith [sq_nonneg (2 * (3 * x + 4) * y - (2 * x ^ 2 + 6 * x + 6)), pow_nonneg hx 4,
        pow_nonneg hx 3, pow_nonneg hx 2]
    have hDr : x ^ 4 - 2 * x ^ 3 * y + 6 * x ^ 3 - 3 * x ^ 2 * y ^ 2 - 10 * x ^ 2 * y +
        13 * x ^ 2 - 8 * x * y ^ 2 - 20 * x * y + 12 * x - 16 * y + 4 < 0 := by
      have hy0 : 0 < y := by linarith
      have : 0 ≤ x ^ 3 * y := by positivity
      have : 0 ≤ x ^ 2 * y ^ 2 := by positivity
      have : 0 ≤ x ^ 2 * y := by positivity
      have : 0 ≤ x * y ^ 2 := by positivity
      have : 0 ≤ x * y := by positivity
      have : x ^ 2 ≤ x / 8 := by nlinarith
      have : x ^ 3 ≤ x ^ 2 / 8 := by nlinarith
      have : x ^ 4 ≤ x ^ 3 / 8 := by nlinarith
      nlinarith
    have hq : 4 * e2 * (e2 * C ^ 2 + f1 * K ^ 2 * C + y ^ 2 * (x + 2) * K ^ 4) =
        (2 * e2 * C + f1 * K ^ 2) ^ 2 - (x ^ 4 - 2 * x ^ 3 * y + 6 * x ^ 3 - 3 * x ^ 2 * y ^ 2 -
          10 * x ^ 2 * y + 13 * x ^ 2 - 8 * x * y ^ 2 - 20 * x * y + 12 * x - 16 * y + 4) *
          K ^ 6 := by
      rw [← he, ← hf, ← hK]; ring
    have he2p : 0 < e2 := by
      rcases he2.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, mul_zero] at hE2
        have hs : 0 ≤ ((3 * x + 2) * y - 2 * (x + 1) ^ 2) ^ 2 := sq_nonneg _
        have hp : 0 ≤ x ^ 2 * (2 * x ^ 2 + 6 * x + 3) := by positivity
        have h0 : x ^ 2 * (2 * x ^ 2 + 6 * x + 3) = 0 := by linarith
        have hx0 : x = 0 := by
          rcases mul_eq_zero.mp h0 with h' | h'
          · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
          · nlinarith
        rw [hx0] at he hf
        have hy1 : (y - 1) ^ 2 = 0 := by linear_combination (1 / 2) * he - (1 / 2) * h
        have hy : y = 1 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy1
          linarith
        rw [hy] at hf
        norm_num at hf
        linarith
    have hrest : 0 ≤ e2 * C ^ 2 + f1 * K ^ 2 * C + y ^ 2 * (x + 2) * K ^ 4 := by
      generalize hD : x ^ 4 - 2 * x ^ 3 * y + 6 * x ^ 3 - 3 * x ^ 2 * y ^ 2 - 10 * x ^ 2 * y +
        13 * x ^ 2 - 8 * x * y ^ 2 - 20 * x * y + 12 * x - 16 * y + 4 = Dr at hDr hq
      have : 0 ≤ 4 * e2 * (e2 * C ^ 2 + f1 * K ^ 2 * C + y ^ 2 * (x + 2) * K ^ 4) := by
        rw [hq]
        have h6 : 0 ≤ (-Dr) * K ^ 6 := mul_nonneg (by linarith) (by positivity)
        linarith [sq_nonneg (2 * e2 * C + f1 * K ^ 2)]
      exact nonneg_of_mul_nonneg_right this (by linarith)
    linarith


/-- The polynomial `B(C, x, y) = (x + 1) C² + g C + y² (x + 2)(x − y + 1)²` of the signed cusp
exclusion is nonnegative for `C, x ≥ 0`: for `g ≥ 0` termwise; for `g < 0` (then `x < 1/16`,
`2/3 < y < 1`) its discriminant `4 (x + 1)(x + 2) y² (x − y + 1)² − g² ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem cuspB_nonneg {C x y : ℝ} (hC : 0 ≤ C)
    (hx : 0 ≤ x) :
    0 ≤ (x + 1) * C ^ 2 + (x ^ 3 - 2 * x ^ 2 * y + 4 * x ^ 2 + 2 * x * y ^ 2 - 6 * x * y +
      5 * x + 3 * y ^ 2 - 5 * y + 2) * C + y ^ 2 * (x + 2) * (x - y + 1) ^ 2 := by
  generalize hg : x ^ 3 - 2 * x ^ 2 * y + 4 * x ^ 2 + 2 * x * y ^ 2 - 6 * x * y + 5 * x +
    3 * y ^ 2 - 5 * y + 2 = g
  rcases le_or_gt 0 g with hg0 | hg0
  · have : 0 ≤ g * C := mul_nonneg hg0 hC
    have : 0 ≤ (x + 1) * C ^ 2 := by positivity
    have : 0 ≤ y ^ 2 * (x + 2) * (x - y + 1) ^ 2 := by positivity
    linarith
  · -- `g < 0` forces `x < 1/16` and `2/3 < y < 1`, where the discriminant is nonnegative
    have hx16 : x < 1 / 16 := by
      have e : 4 * (2 * x + 3) * g = (2 * (2 * x + 3) * y - (2 * x ^ 2 + 6 * x + 5)) ^ 2 +
          4 * x ^ 4 + 20 * x ^ 3 + 32 * x ^ 2 + 16 * x - 1 := by rw [← hg]; ring
      have h1 : 4 * (2 * x + 3) * g < 0 := mul_neg_of_pos_of_neg (by linarith) hg0
      nlinarith [sq_nonneg (2 * (2 * x + 3) * y - (2 * x ^ 2 + 6 * x + 5)), pow_nonneg hx 4,
        pow_nonneg hx 3, pow_nonneg hx 2]
    have hy0 : 2 / 3 < y := by
      have e : g - x * (9 * x ^ 2 + 24 * x + 17) / 9 =
          (y - 2 / 3) * ((2 * x + 3) * (y + 2 / 3) - (2 * x ^ 2 + 6 * x + 5)) := by
        rw [← hg]; ring
      by_contra hle
      push Not at hle
      have h1 : (2 * x + 3) * (y + 2 / 3) - (2 * x ^ 2 + 6 * x + 5) < 0 := by nlinarith
      have h2 : 0 ≤ (y - 2 / 3) * ((2 * x + 3) * (y + 2 / 3) - (2 * x ^ 2 + 6 * x + 5)) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) h1.le
      have h4 : 0 ≤ x * (9 * x ^ 2 + 24 * x + 17) / 9 := by positivity
      linarith
    have hy1 : y < 1 := by
      have e : g - x * (x + 1) ^ 2 =
          (y - 1) * ((2 * x + 3) * (y + 1) - (2 * x ^ 2 + 6 * x + 5)) := by rw [← hg]; ring
      by_contra hle
      push Not at hle
      have h1 : 0 < (2 * x + 3) * (y + 1) - (2 * x ^ 2 + 6 * x + 5) := by nlinarith
      have h2 : 0 ≤ (y - 1) * ((2 * x + 3) * (y + 1) - (2 * x ^ 2 + 6 * x + 5)) :=
        mul_nonneg (by linarith) h1.le
      have h4 : 0 ≤ x * (x + 1) ^ 2 := by positivity
      linarith
    have hD : 0 ≤ 4 * (x + 1) * (x + 2) * y ^ 2 * (x - y + 1) ^ 2 - g ^ 2 := by
      obtain ⟨s, rfl⟩ : ∃ s, y = 1 - s := ⟨1 - y, by ring⟩
      have hs0 : 0 < s := by linarith
      have hs1 : s < 1 / 3 := by linarith
      have e : 4 * (x + 1) * (x + 2) * (1 - s) ^ 2 * (x - (1 - s) + 1) ^ 2 - g ^ 2 =
          s ^ 2 * (7 - 10 * s - s ^ 2) + 2 * s * x * (9 - 11 * s - 8 * s ^ 2) +
            x ^ 2 * (7 + 8 * s - 52 * s ^ 2 - 4 * s ^ 3) + 2 * x ^ 3 * (4 - 13 * s - 13 * s ^ 2) -
            2 * x ^ 4 * (2 * s ^ 2 + 10 * s + 1) - 4 * x ^ 5 * (s + 1) - x ^ 6 := by
        rw [← hg]; ring
      rw [e]
      have t0 : 0 ≤ s ^ 2 * (7 - 10 * s - s ^ 2) := mul_nonneg (by positivity) (by nlinarith)
      have t1 : 0 ≤ 2 * s * x * (9 - 11 * s - 8 * s ^ 2) :=
        mul_nonneg (by positivity) (by nlinarith)
      have t2 : x ^ 2 ≤ x ^ 2 * (7 + 8 * s - 52 * s ^ 2 - 4 * s ^ 3) := by
        have : 0 ≤ 7 + 8 * s - 52 * s ^ 2 - 4 * s ^ 3 - 1 := by nlinarith
        have := mul_nonneg (sq_nonneg x) this
        linarith
      have hx3 : x ^ 3 ≤ x ^ 2 / 16 := by
        have := mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 16 - x)
        linarith
      have hx4 : x ^ 4 ≤ x ^ 3 / 16 := by
        have := mul_nonneg (pow_nonneg hx 3) (by linarith : (0 : ℝ) ≤ 1 / 16 - x)
        linarith
      have hx5 : x ^ 5 ≤ x ^ 4 / 16 := by
        have := mul_nonneg (pow_nonneg hx 4) (by linarith : (0 : ℝ) ≤ 1 / 16 - x)
        linarith
      have hx6 : x ^ 6 ≤ x ^ 5 / 16 := by
        have := mul_nonneg (pow_nonneg hx 5) (by linarith : (0 : ℝ) ≤ 1 / 16 - x)
        linarith
      have t3 : -(12 * x ^ 3) ≤ 2 * x ^ 3 * (4 - 13 * s - 13 * s ^ 2) := by
        have : 0 ≤ 4 - 13 * s - 13 * s ^ 2 + 6 := by nlinarith
        have := mul_nonneg (pow_nonneg hx 3) this
        linarith
      have t4 : 2 * x ^ 4 * (2 * s ^ 2 + 10 * s + 1) ≤ 10 * x ^ 4 := by
        have : 0 ≤ 5 - (2 * s ^ 2 + 10 * s + 1) := by nlinarith
        have := mul_nonneg (pow_nonneg hx 4) this
        linarith
      have t5 : 4 * x ^ 5 * (s + 1) ≤ 8 * x ^ 5 := by
        have := mul_nonneg (pow_nonneg hx 5) (by linarith : (0 : ℝ) ≤ 1 - s)
        linarith
      have := pow_nonneg hx 2
      linarith
    have hq : 4 * (x + 1) * ((x + 1) * C ^ 2 + g * C + y ^ 2 * (x + 2) * (x - y + 1) ^ 2) =
        (2 * (x + 1) * C + g) ^ 2 +
          (4 * (x + 1) * (x + 2) * y ^ 2 * (x - y + 1) ^ 2 - g ^ 2) := by ring
    have : 0 ≤ 4 * (x + 1) * ((x + 1) * C ^ 2 + g * C + y ^ 2 * (x + 2) * (x - y + 1) ^ 2) := by
      rw [hq]; linarith [sq_nonneg (2 * (x + 1) * C + g)]
    exact nonneg_of_mul_nonneg_right this (by linarith)

/-- The scaled cusp exclusion (pure algebra): with `k = X + 1 − T`, `X > 0`, `C ≠ 0`, `e ≥ 0`, the
fold `k A − (R_r − R) C = 0` and `(A² + R² − C² − T²) X − 2 (A C + R T) R_r ≥ 0`, the quantity
`(C² + k² + e C²)(A T − C R) − A C²` does not vanish (for `e = 0` the scaled cusp quantity).
Certificate: on its zero set `C² (C² + k² + e C²)² H = −(A² N + C² X (C² + k² + e C²)² (C² + T²))`
with `N = N₂ + 2 e C² B + e² (X + 2) C⁴ (C² + T²) ≥ 0` (`cuspN2_nonneg`, `cuspB_nonneg`). -/
@[tmio T, powerlib_foundation] private theorem cusp_core {A Cc R T Rr X e : ℝ} (hX : 0 < X)
    (hc : Cc ≠ 0) (he : 0 ≤ e) (hfold : (X + 1 - T) * A - (Rr - R) * Cc = 0)
    (hH : 0 ≤ (A ^ 2 + R ^ 2 - Cc ^ 2 - T ^ 2) * X - 2 * (A * Cc + R * T) * Rr) :
    (Cc ^ 2 + (X + 1 - T) ^ 2 + e * Cc ^ 2) * (A * T - Cc * R) - A * Cc ^ 2 ≠ 0 := by
  intro hF
  have h1 := cuspN2_nonneg (C := Cc ^ 2) (x := X) (y := T) (sq_nonneg _) hX.le
  have hB := cuspB_nonneg (C := Cc ^ 2) (x := X) (y := T) (sq_nonneg _) hX.le
  have key : Cc ^ 2 * (Cc ^ 2 + (X + 1 - T) ^ 2 + e * Cc ^ 2) ^ 2 *
      ((A ^ 2 + R ^ 2 - Cc ^ 2 - T ^ 2) * X - 2 * (A * Cc + R * T) * Rr) =
      -(A ^ 2 * ((X * (Cc ^ 2) ^ 3 + (2 * X ^ 3 - 4 * X ^ 2 * T + 6 * X ^ 2 + 3 * X * T ^ 2 -
        8 * X * T + 5 * X + 2 * T ^ 2 - 4 * T + 2) * (Cc ^ 2) ^ 2 + (X - T + 1) ^ 2 *
        (X ^ 3 - 2 * X ^ 2 * T + 4 * X ^ 2 + 3 * X * T ^ 2 - 6 * X * T + 5 * X + 4 * T ^ 2 -
          6 * T + 2) * Cc ^ 2 + T ^ 2 * (X + 2) * (X - T + 1) ^ 4) +
        2 * e * Cc ^ 2 * ((X + 1) * (Cc ^ 2) ^ 2 + (X ^ 3 - 2 * X ^ 2 * T + 4 * X ^ 2 +
          2 * X * T ^ 2 - 6 * X * T + 5 * X + 3 * T ^ 2 - 5 * T + 2) * Cc ^ 2 +
          T ^ 2 * (X + 2) * (X - T + 1) ^ 2) +
        e ^ 2 * (X + 2) * (Cc ^ 2) ^ 2 * (Cc ^ 2 + T ^ 2)) +
        Cc ^ 2 * X * (Cc ^ 2 + (X + 1 - T) ^ 2 + e * Cc ^ 2) ^ 2 * (Cc ^ 2 + T ^ 2)) := by
    linear_combination (A * (2 * Cc ^ 4 * e + 2 * Cc ^ 4 + 2 * Cc ^ 2 * T ^ 2 +
      Cc ^ 2 * T * X * e - 3 * Cc ^ 2 * T * X + 2 * Cc ^ 2 * T * e - 4 * Cc ^ 2 * T +
      2 * Cc ^ 2 * X ^ 2 + 5 * Cc ^ 2 * X + 2 * Cc ^ 2 + T ^ 3 * X + 2 * T ^ 3 -
      2 * T ^ 2 * X ^ 2 - 6 * T ^ 2 * X - 4 * T ^ 2 + T * X ^ 3 + 4 * T * X ^ 2 + 5 * T * X +
      2 * T) + 2 * Cc ^ 3 * R * T - Cc ^ 3 * R * X + 2 * Cc * R * T ^ 3 -
      5 * Cc * R * T ^ 2 * X - 4 * Cc * R * T ^ 2 + 4 * Cc * R * T * X ^ 2 + 6 * Cc * R * T * X +
      2 * Cc * R * T - Cc * R * X ^ 3 - 2 * Cc * R * X ^ 2 - Cc * R * X +
      e * (2 * Cc ^ 3 * R * T - Cc ^ 3 * R * X)) * hF +
      (2 * Cc * (A * Cc + R * T) * (Cc ^ 2 + (X + 1 - T) ^ 2 + e * Cc ^ 2) ^ 2) * hfold
  have hC2 : 0 < Cc ^ 2 := by positivity
  have h2 : 0 < Cc ^ 2 * X * (Cc ^ 2 + (X + 1 - T) ^ 2 + e * Cc ^ 2) ^ 2 * (Cc ^ 2 + T ^ 2) := by
    positivity
  have h3 : 0 ≤ Cc ^ 2 * (Cc ^ 2 + (X + 1 - T) ^ 2 + e * Cc ^ 2) ^ 2 *
      ((A ^ 2 + R ^ 2 - Cc ^ 2 - T ^ 2) * X - 2 * (A * Cc + R * T) * Rr) := by positivity
  have h5 : 0 ≤ 2 * e * Cc ^ 2 * ((X + 1) * (Cc ^ 2) ^ 2 + (X ^ 3 - 2 * X ^ 2 * T + 4 * X ^ 2 +
      2 * X * T ^ 2 - 6 * X * T + 5 * X + 3 * T ^ 2 - 5 * T + 2) * Cc ^ 2 +
      T ^ 2 * (X + 2) * (X - T + 1) ^ 2) := mul_nonneg (by positivity) hB
  have h6 : 0 ≤ e ^ 2 * (X + 2) * (Cc ^ 2) ^ 2 * (Cc ^ 2 + T ^ 2) := by positivity
  have h4 := mul_nonneg (sq_nonneg A) (add_nonneg (add_nonneg h1 h5) h6)
  linarith

/-- The fold data of an inductive fold in the scaled frame (`x, r` as below). -/
@[tmio M, powerlib_domain] private theorem foldQuad_scaled {a c k m ρ τ r x : ℝ} (hm : 0 < m)
    (hx : 0 < x) (hc : c ≠ 0) (hk : k = 1 + m * (x - τ)) (hC : k * a - m * (r - ρ) * c = 0)
    (hH : 0 ≤ (a ^ 2 + ρ ^ 2 - c ^ 2 - τ ^ 2) * x - 2 * (a * c + ρ * τ) * r) {e : ℝ}
    (he : 0 ≤ e) :
    ((m * c) ^ 2 + k ^ 2 + e * (m * c) ^ 2) * (m * a * (m * τ) - m * c * (m * ρ)) -
      m * a * (m * c) ^ 2 ≠ 0 := by
  have hk' : k = m * x + 1 - m * τ := by rw [hk]; ring
  rw [hk']
  refine cusp_core (A := m * a) (R := m * ρ) (T := m * τ) (Rr := m * r) (mul_pos hm hx)
    (mul_ne_zero hm.ne' hc) he (by rw [← hk']; linear_combination m * hC) ?_
  have e : ((m * a) ^ 2 + (m * ρ) ^ 2 - (m * c) ^ 2 - (m * τ) ^ 2) * (m * x) -
      2 * (m * a * (m * c) + m * ρ * (m * τ)) * (m * r) =
      m ^ 3 * ((a ^ 2 + ρ ^ 2 - c ^ 2 - τ ^ 2) * x - 2 * (a * c + ρ * τ) * r) := by ring
  rw [e]; positivity

/-- **The cusp quantity does not vanish on an inductive fold** (pure algebra). For `m, x > 0`,
`c ≠ 0`, `k = 1 + m (x − τ)`, the fold `k a − m (r − ρ) c = 0` and the reactance condition
`(a² + ρ² − c² − τ²) x − 2 (a c + ρ τ) r ≥ 0`: `𝔉(a, c, k, m, ρ, τ) ≠ 0`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem foldQuad_ne_zero_of_fold {a c k m ρ τ r x : ℝ} (hm : 0 < m)
    (hx : 0 < x) (hc : c ≠ 0) (hk : k = 1 + m * (x - τ)) (hC : k * a - m * (r - ρ) * c = 0)
    (hH : 0 ≤ (a ^ 2 + ρ ^ 2 - c ^ 2 - τ ^ 2) * x - 2 * (a * c + ρ * τ) * r) :
    foldQuad a c k m ρ τ ≠ 0 := by
  intro hF
  apply foldQuad_scaled hm hx hc hk hC hH le_rfl
  have e : ((m * c) ^ 2 + k ^ 2 + 0 * (m * c) ^ 2) * (m * a * (m * τ) - m * c * (m * ρ)) -
      m * a * (m * c) ^ 2 = m ^ 2 * foldQuad a c k m ρ τ := by unfold foldQuad; ring
  rw [e, hF, mul_zero]

/-- **The sign of the cusp quantity on an inductive fold** (pure algebra). Under the hypotheses
of `foldQuad_ne_zero_of_fold` and `a τ − c ρ ≠ 0`: `(a τ − c ρ) 𝔉 > 0`. If `(a τ − c ρ) 𝔉 ≤ 0`,
then `m² 𝔉 = (C² + k² + e C²) D − A C²` vanishes, in the scaled data `A = m a`, `C = m c`,
`D = m² (a τ − c ρ)`, with `e = (A C² D − (k² + C²) D²)/(C² D²) ≥ 0`, against
the scaled exclusion. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem mul_foldQuad_pos_of_fold {a c k m ρ τ r x : ℝ} (hm : 0 < m)
    (hx : 0 < x) (hc : c ≠ 0) (hk : k = 1 + m * (x - τ)) (hC : k * a - m * (r - ρ) * c = 0)
    (hH : 0 ≤ (a ^ 2 + ρ ^ 2 - c ^ 2 - τ ^ 2) * x - 2 * (a * c + ρ * τ) * r)
    (hD : a * τ - c * ρ ≠ 0) :
    0 < (a * τ - c * ρ) * foldQuad a c k m ρ τ := by
  by_contra hneg
  push Not at hneg
  set D := m * a * (m * τ) - m * c * (m * ρ) with hDdef
  have hD' : D ≠ 0 := by
    rw [show D = m ^ 2 * (a * τ - c * ρ) by rw [hDdef]; ring]
    exact mul_ne_zero (pow_ne_zero 2 hm.ne') hD
  have hcm : (m * c) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hm.ne' hc)
  have hF : (k ^ 2 + (m * c) ^ 2) * D - m * a * (m * c) ^ 2 = m ^ 2 * foldQuad a c k m ρ τ := by
    rw [hDdef]; unfold foldQuad; ring
  have hDF : D * ((k ^ 2 + (m * c) ^ 2) * D - m * a * (m * c) ^ 2) ≤ 0 := by
    rw [hF, show D = m ^ 2 * (a * τ - c * ρ) by rw [hDdef]; ring]
    have : 0 ≤ m ^ 2 * m ^ 2 := by positivity
    nlinarith
  refine foldQuad_scaled hm hx hc hk hC hH
    (e := (m * a * (m * c) ^ 2 * D - (k ^ 2 + (m * c) ^ 2) * D ^ 2) / ((m * c) ^ 2 * D ^ 2))
    ?_ ?_
  · apply div_nonneg _ (by positivity)
    nlinarith
  · rw [← hDdef]
    field_simp
    ring

section Physical

variable (q : QVDroopVirtual)

/-- `E ∂Q_t/∂E + ∂²Q_t/∂δ² = 2 X_g E²/|Z_t|²`: the EMF slope of the terminal reactive power is the
grid-branch term minus the angle curvature (for `Z_v = 0`, `QVDroop.Pδ_add_mul_QE`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem mul_QtE_add_Qtδδ (δ E : ℝ) :
    E * q.QtE δ E + q.Qtδδ δ E = 2 * q.Xg * E ^ 2 / q.ztsq := by
  simp only [QtE, Qtδδ]
  ring

/-- `E ∂P_t/∂E + ∂²P_t/∂δ² = 2 R_g E²/|Z_t|²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem mul_PtE_add_Ptδδ (δ E : ℝ) :
    E * q.PtE δ E + q.Ptδδ δ E = 2 * q.Rg * E ^ 2 / q.ztsq := by
  simp only [PtE, Ptδδ]
  ring

/-- **The reactance minor.** With `x = 2 X_g E²/|Z_t|²`, `r = 2 R_g E²/|Z_t|²` and the slopes and
curvatures `a, c, ρ, τ` of the terminal powers,
`(a² + ρ² − c² − τ²) x − 2 (a c + ρ τ) r = 8 E⁴ V² X_v |Z_g|²/|Z_t|⁶`: its sign is that of the
virtual reactance. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem reactanceMinor_eq (hZ : q.ztsq ≠ 0) (δ E : ℝ) :
    (q.Ptδ δ E ^ 2 + q.Ptδδ δ E ^ 2 - q.Qtδ δ E ^ 2 - q.Qtδδ δ E ^ 2) *
        (2 * q.Xg * E ^ 2 / q.ztsq) -
      2 * (q.Ptδ δ E * q.Qtδ δ E + q.Ptδδ δ E * q.Qtδδ δ E) * (2 * q.Rg * E ^ 2 / q.ztsq) =
      8 * E ^ 4 * q.V ^ 2 * q.Xv * (q.Rg ^ 2 + q.Xg ^ 2) / q.ztsq ^ 3 := by
  have hs : E ^ 4 * q.V ^ 2 =
      E ^ 2 * ((E * q.V * Real.cos δ) ^ 2 + (E * q.V * Real.sin δ) ^ 2) := by
    have := Real.sin_sq_add_cos_sq δ
    linear_combination (-(E ^ 4 * q.V ^ 2)) * this
  rw [show 8 * E ^ 4 * q.V ^ 2 * q.Xv * (q.Rg ^ 2 + q.Xg ^ 2) =
    8 * (E ^ 4 * q.V ^ 2) * q.Xv * (q.Rg ^ 2 + q.Xg ^ 2) by ring, hs]
  simp only [Ptδ, Qtδ, Ptδδ, Qtδδ]
  generalize E * q.V * Real.cos δ = u
  generalize E * q.V * Real.sin δ = w
  field_simp
  ring

/-- The scaled fold data of a physical fold: `k = 1 + m (x − τ)`, the fold
`k a − m (r − ρ) c = 0` and a nonnegative reactance minor, with `m = n_q/E`,
`x = 2 X_g E²/|Z_t|²`, `r = 2 R_g E²/|Z_t|²`. -/
@[tmio M, powerlib_domain] private theorem physical_fold_data (hXg : 0 < q.Xg) (hXv : 0 ≤ q.Xv)
    {δ E : ℝ} (hE : E ≠ 0) (hC : q.routhFold δ E = 0) :
    q.gain δ E = 1 + q.nq / E * (2 * q.Xg * E ^ 2 / q.ztsq - q.Qtδδ δ E) ∧
      q.gain δ E * q.Ptδ δ E -
        q.nq / E * (2 * q.Rg * E ^ 2 / q.ztsq - q.Ptδδ δ E) * q.Qtδ δ E = 0 ∧
      0 ≤ (q.Ptδ δ E ^ 2 + q.Ptδδ δ E ^ 2 - q.Qtδ δ E ^ 2 - q.Qtδδ δ E ^ 2) *
          (2 * q.Xg * E ^ 2 / q.ztsq) -
        2 * (q.Ptδ δ E * q.Qtδ δ E + q.Ptδδ δ E * q.Qtδδ δ E) * (2 * q.Rg * E ^ 2 / q.ztsq) := by
  have hZ := q.ztsq_pos hXg hXv
  have hQ := q.mul_QtE_add_Qtδδ δ E
  have hP := q.mul_PtE_add_Ptδδ δ E
  refine ⟨?_, ?_, ?_⟩
  · rw [gain, ← hQ]
    field_simp
    ring
  · have h0 : q.gain δ E * q.Ptδ δ E - q.nq * q.PtE δ E * q.Qtδ δ E = 0 := hC
    have e : q.nq / E * (2 * q.Rg * E ^ 2 / q.ztsq - q.Ptδδ δ E) = q.nq * q.PtE δ E := by
      rw [← hP]; field_simp; ring
    rw [e]
    linear_combination h0
  · rw [q.reactanceMinor_eq hZ.ne']
    positivity

/-- **No cusp point on an inductive fold.** For `X_g > 0`, `X_v ≥ 0`, `n_q > 0` and `E > 0`, at a
fold `C = 0` with `Q_tδ ≠ 0` the cusp quantity does not vanish:
`𝔉(P_tδ, Q_tδ, K_t, n_q/E, P_tδδ, Q_tδδ) ≠ 0` (`foldQuad_ne_zero_of_fold` with
`mul_QtE_add_Qtδδ`, `mul_PtE_add_Ptδδ`, `reactanceMinor_eq`). No sign of `R_g`, `R_v`, no
balance and no level hypothesis is needed. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem foldQuad_ne_zero_of_physical (hXg : 0 < q.Xg)
    (hXv : 0 ≤ q.Xv) (hnq : 0 < q.nq) {δ E : ℝ} (hE : 0 < E) (hC : q.routhFold δ E = 0)
    (hc : q.Qtδ δ E ≠ 0) :
    foldQuad (q.Ptδ δ E) (q.Qtδ δ E) (q.gain δ E) (q.nq / E) (q.Ptδδ δ E) (q.Qtδδ δ E) ≠ 0 := by
  have hZ := q.ztsq_pos hXg hXv
  obtain ⟨h1, h2, h3⟩ := q.physical_fold_data hXg hXv hE.ne' hC
  exact foldQuad_ne_zero_of_fold (div_pos hnq hE) (by positivity) hc h1 h2 h3

/-- `P_tδ ∂²Q_t/∂δ² − Q_tδ ∂²P_t/∂δ² = dz (E V)²/|Z_t|⁴`, `dz = |Z_g|² − |Z_v|²`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem Ptδ_mul_Qtδδ_sub (hZ : q.ztsq ≠ 0) (δ E : ℝ) :
    q.Ptδ δ E * q.Qtδδ δ E - q.Qtδ δ E * q.Ptδδ δ E = q.dz * (E * q.V) ^ 2 / q.ztsq ^ 2 := by
  have hs : (E * q.V) ^ 2 = (E * q.V * Real.cos δ) ^ 2 + (E * q.V * Real.sin δ) ^ 2 := by
    have := Real.sin_sq_add_cos_sq δ
    linear_combination (-(E * q.V) ^ 2) * this
  rw [hs]
  simp only [Ptδ, Qtδ, Ptδδ, Qtδδ, dz]
  generalize E * q.V * Real.cos δ = u
  generalize E * q.V * Real.sin δ = w
  field_simp
  ring

/-- **The sign of the cusp quantity on an inductive fold.** Under the hypotheses of
`foldQuad_ne_zero_of_physical` and `|Z_v| ≠ |Z_g|` (`dz ≠ 0`): `dz 𝔉 > 0`, the cusp quantity has
the sign of `|Z_g|² − |Z_v|²` (`mul_foldQuad_pos_of_fold`, `Ptδ_mul_Qtδδ_sub`). For `dz = 0`,
`𝔉 = −m a c² ≠ 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dz_mul_foldQuad_pos_of_physical (hXg : 0 < q.Xg)
    (hXv : 0 ≤ q.Xv) (hnq : 0 < q.nq) {δ E : ℝ} (hE : 0 < E) (hC : q.routhFold δ E = 0)
    (hc : q.Qtδ δ E ≠ 0) (hdz : q.dz ≠ 0) :
    0 < q.dz *
      foldQuad (q.Ptδ δ E) (q.Qtδ δ E) (q.gain δ E) (q.nq / E) (q.Ptδδ δ E) (q.Qtδδ δ E) := by
  have hZ := q.ztsq_pos hXg hXv
  have hV : q.V ≠ 0 := by
    intro hV; apply hc; simp [Qtδ, hV]
  obtain ⟨h1, h2, h3⟩ := q.physical_fold_data hXg hXv hE.ne' hC
  have hD := q.Ptδ_mul_Qtδδ_sub hZ.ne' δ E
  have hw : 0 < (E * q.V) ^ 2 / q.ztsq ^ 2 := by
    have : 0 < (E * q.V) ^ 2 := by positivity
    positivity
  have hD0 : q.Ptδ δ E * q.Qtδδ δ E - q.Qtδ δ E * q.Ptδδ δ E ≠ 0 := by
    rw [hD]
    exact div_ne_zero (mul_ne_zero hdz (pow_ne_zero 2 (mul_ne_zero hE.ne' hV)))
      (pow_ne_zero 2 hZ.ne')
  have hpos := mul_foldQuad_pos_of_fold (div_pos hnq hE) (by positivity) hc h1 h2 h3 hD0
  rw [hD, show q.dz * (E * q.V) ^ 2 / q.ztsq ^ 2 = (E * q.V) ^ 2 / q.ztsq ^ 2 * q.dz by ring,
    mul_assoc] at hpos
  exact pos_of_mul_pos_right hpos hw.le

/-- At a fold with `K_t ≠ 0`, `E V ≠ 0`, `|Z_t| ≠ 0` and `|Z_v| ≠ |Z_g|` (`dz ≠ 0`) the angle slope
of `Q_t` does not vanish: `Q_tδ = 0` would give `P_tδ = 0` (`C = K_t P_tδ − n_q P_tE Q_tδ`), against
`P_tδ Q_tδδ − Q_tδ P_tδδ = dz (E V)²/|Z_t|⁴ ≠ 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Qtδ_ne_zero_of_fold (hZ : q.ztsq ≠ 0) (hdz : q.dz ≠ 0)
    {δ E : ℝ} (hEV : E * q.V ≠ 0) (hk : q.gain δ E ≠ 0) (hC : q.routhFold δ E = 0) :
    q.Qtδ δ E ≠ 0 := by
  intro hc
  have hP : q.Ptδ δ E = 0 := by
    have h0 : q.gain δ E * q.Ptδ δ E - q.nq * q.PtE δ E * q.Qtδ δ E = 0 := hC
    rw [hc, mul_zero, sub_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hk
  have h := q.Ptδ_mul_Qtδδ_sub hZ δ E
  rw [hP, hc, zero_mul, zero_mul, sub_zero] at h
  exact div_ne_zero (mul_ne_zero hdz (pow_ne_zero 2 hEV)) (pow_ne_zero 2 hZ) h.symm

end Physical

/-- In the physical range (`M, ω_q ≠ 0`, `n_q, X_g > 0`, `X_v ≥ 0`, `E₀ + n_q Q_ref > 0`) the gain
`K_t` is positive at every equilibrium with `E* > 0`:
`E |Z_t|² K_t = n_q X_g E² + n_q X_v V² + (E₀ + n_q Q_ref) |Z_t|²` (`gain_of_balance`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.gain_pos_of_physical (m : Model) (hM : m.q.M ≠ 0)
    (hω : m.q.ωq ≠ 0) (hnq : 0 < m.q.nq) (hXg : 0 < m.q.Xg) (hXv : 0 ≤ m.q.Xv)
    (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) : 0 < m.q.gain m.δ (m.q.emf m.Qf) := by
  have hZ := m.q.ztsq_pos hXg hXv
  have hQ : m.q.Qt m.δ (m.q.emf m.Qf) = m.q.qOf (m.q.emf m.Qf) := by
    simpa [Model.point] using (m.q.balance_of_field_eq_zero hM hω hnq.ne' heq).2
  rw [m.q.gain_of_balance hZ.ne' hnq.ne' hE.ne' hQ]
  have h1 : 0 < m.q.nq * m.q.Xg * m.q.emf m.Qf ^ 2 := by positivity
  have h2 : 0 ≤ m.q.nq * m.q.Xv * m.q.V ^ 2 := by positivity
  have h3 : 0 < (m.q.E0 + m.q.nq * m.q.Qref) * m.q.ztsq := mul_pos hlev hZ
  exact div_pos (by linarith) (mul_pos hE hZ)

/-! ## Folds with `Q_tδ = 0` -/

/-- **The fold coefficient at a fold with `Q_tδ = 0`.** At `C = 0` with `M, E* ≠ 0`, `Q_tδ = 0`
and `D ω_q K_t² ≠ 0`, the fold coefficient of the null pair `(QVDroop.foldQ, QVDroop.foldP)` is
`(b τ − k ρ)/(2 D)`: `2 D ω_q k² foldCoeff = ω_q k² (b τ − k ρ)` (`b = n_q ∂P_t/∂E`, `k = K_t`,
`ρ, τ` the angle curvatures; the identity of `Model.foldCoeff_fold` degenerates there). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_fold_of_Qtδ_eq_zero (m : Model)
    (hM : m.q.M ≠ 0) (hE : m.q.emf m.Qf ≠ 0) (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) = 0)
    (hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 ≠ 0) :
    2 * (m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2) *
      NormalForm.BogdanovTakens.foldCoeff m.field 0
        (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
        (QVDroop.foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
          (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))) =
      m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 *
        (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδδ m.δ (m.q.emf m.Qf) -
          m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)) := by
  have v1 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 1
  have v2 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 2
  have v0 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 0
  rw [NormalForm.BogdanovTakens.foldCoeff]
  generalize fderiv ℝ (fderiv ℝ m.field) 0
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) = v at v0 v1 v2 ⊢
  generalize m.q.Ptδ m.δ (m.q.emf m.Qf) = a at v1 v2 v0 ⊢
  generalize m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) = b at v1 v2 v0 ⊢
  generalize m.q.Qtδ m.δ (m.q.emf m.Qf) = c at hc v1 v2 v0 ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at hN v1 v2 v0 ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at v1 v2 v0 ⊢
  generalize m.q.Ptδδ m.δ (m.q.emf m.Qf) = ρ at v1 v2 v0 ⊢
  generalize m.q.Qtδδ m.δ (m.q.emf m.Qf) = τ at v1 v2 v0 ⊢
  subst hc
  simp only [bForm, toC, QVDroop.foldQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at v0 v1 v2
  have e1 : m.q.M * v 1 = -(ρ * k ^ 2) := by
    have : v 1 = -(ρ / m.q.M) * (k * k) := by
      apply Complex.ofReal_injective; rw [v1]; push_cast; ring
    rw [this]; field_simp
  have e2 : v 2 = m.q.ωq * τ * k ^ 2 := by
    apply Complex.ofReal_injective; rw [v2]; push_cast; ring
  have hv0 : v 0 = 0 := by apply Complex.ofReal_injective; rw [v0]; simp
  simp only [QVDroop.foldP, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hv0, e2, mul_zero, add_zero]
  have hD : m.q.D ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hN)
  have hω : m.q.ωq ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hN)
  have hk : k ≠ 0 := pow_ne_zero_iff (n := 2) (by norm_num) |>.mp (right_ne_zero_of_mul hN)
  have e1' : v 1 = -(ρ * k ^ 2) / m.q.M := by rw [← e1]; field_simp
  rw [e1']
  field_simp
  ring

/-- **A fold with `Q_tδ = 0` is a saddle-node off `b τ = k ρ`.** For `M, ω_q > 0`, an equilibrium
at a fold (`C = 0`) with `Q_tδ = 0` (then `P_tδ = 0`), `A > 0`, `P_tδ + D ω_q K_t > 0`,
`K_t ≠ 0`, `E* ≠ 0` and `n_q (∂P_t/∂E) ∂²Q_t/∂δ² ≠ K_t ∂²P_t/∂δ²` is unstable: the fold coefficient
is `(b τ − k ρ)/(2 D) ≠ 0` (`Model.foldCoeff_fold_of_Qtδ_eq_zero`,
`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_Qtδ_eq_zero (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) = 0)
    (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hE : m.q.emf m.Qf ≠ 0)
    (hΦ : m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδδ m.δ (m.q.emf m.Qf) ≠
      m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  have ha0 : m.q.Ptδ m.δ (m.q.emf m.Qf) = 0 := by
    rw [hc, mul_zero, sub_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hk
  have hN0 : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 ≠ 0 := by
    have e : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 = m.q.gain m.δ (m.q.emf m.Qf) *
        (m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
      rw [ha0]; ring
    rw [e]
    exact mul_ne_zero hk ha1.ne'
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    rwa [hc, mul_zero, add_zero]
  have heq0 : m.field 0 = 0 := by simpa [Model.field] using heq
  refine Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly
    (m.contDiff_field (k := 2)) heq0 (m.isNullPair_fold hM.ne' hC hN)
    (m.charpoly_fold hM.ne' hC) (fun s hs => (Criteria.quadratic_roots_re_neg_iff _ _).mpr
      ⟨div_pos hA hM, div_pos ha1 hM⟩ s (by simpa using hs)) ?_
  intro h
  have key := m.foldCoeff_fold_of_Qtδ_eq_zero hM.ne' hE hc hN0
  rw [h, mul_zero] at key
  exact mul_ne_zero (mul_ne_zero hω.ne' (pow_ne_zero 2 hk)) (sub_ne_zero.mpr hΦ) key.symm

/-! ## The physical range -/

/-- **Every physical fold point with `Q_tδ ≠ 0` is a saddle-node.** For `M, ω_q, n_q, X_g > 0`,
`X_v ≥ 0` and `E₀ + n_q Q_ref > 0`, an equilibrium with `E* > 0` at a fold (`C = 0`) with
`Q_tδ ≠ 0`, `A > 0` and `P_tδ + D ω_q K_t > 0` is unstable, with no hypothesis on `𝔉`
(`mem_den_unstable_of_fold`; `K_t > 0` by `Model.gain_pos_of_physical`, `𝔉 ≠ 0` by
`foldQuad_ne_zero_of_physical`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_physical (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hXg : 0 < m.q.Xg) (hXv : 0 ≤ m.q.Xv)
    (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0) (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hk := m.gain_pos_of_physical hM.ne' hω.ne' hnq hXg hXv hlev heq hE
  exact mem_den_unstable_of_fold m hM hω heq hC hA ha1 hk.ne' hE.ne'
    (m.q.foldQuad_ne_zero_of_physical hXg hXv hnq hE hC hc)

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

/-- A physical fold point with `Q_tδ = 0`: `M = D = ω_q = n_q = E₀ = V = 1`, `Q_ref = 0`,
`P_ref = 1/2`, `Z_g = Z_v = j` (`dz = 0`), at `δ* = π/2`, `Q_f* = 0` (`E* = 1`: `P_tδ = Q_tδ = 0`,
`K_t = 3/2`, `b = 1/2`, `ρ = −1/2`, `τ = 0`). -/
def dzFold : Model := ⟨⟨1, 1, 1, 1, 1, 0, 1 / 2, 1, 0, 1, 0, 1⟩, Real.pi / 2, 0⟩

/-- **The cusp set meets the physical range only through `Q_tδ = 0`.** `dzFold` is a physical
equilibrium (`M, D, ω_q, n_q, X_g, X_v, V > 0`, `E₀ + n_q Q_ref = 1`, `E* = 1`) with `dz = 0` at a
fold with `Q_tδ = 0` and `𝔉 = 0`: the hypothesis `Q_tδ ≠ 0` of `foldQuad_ne_zero_of_physical`
cannot be dropped. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dzFold_fold :
    dzFold.q.field dzFold.point = 0 ∧ dzFold.q.dz = 0 ∧
      dzFold.q.routhFold dzFold.δ (dzFold.q.emf dzFold.Qf) = 0 ∧
      dzFold.q.Qtδ dzFold.δ (dzFold.q.emf dzFold.Qf) = 0 ∧
      foldQuad (dzFold.q.Ptδ dzFold.δ (dzFold.q.emf dzFold.Qf))
        (dzFold.q.Qtδ dzFold.δ (dzFold.q.emf dzFold.Qf))
        (dzFold.q.gain dzFold.δ (dzFold.q.emf dzFold.Qf)) (dzFold.q.nq / dzFold.q.emf dzFold.Qf)
        (dzFold.q.Ptδδ dzFold.δ (dzFold.q.emf dzFold.Qf))
        (dzFold.q.Qtδδ dzFold.δ (dzFold.q.emf dzFold.Qf)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Dynamics.state3_ext <;> simp [dzFold, Model.point, field, Pt_eq, Qt_eq, emf, ztsq]
    norm_num
  all_goals norm_num [dzFold, dz, routhFold, gain, coupling, Ptδ, PtE, Qtδ, QtE, Ptδδ, Qtδδ, emf,
    ztsq, foldQuad]

/-- **The physical fold point `dzFold` is unstable** (a saddle-node with `Q_tδ = 0`,
`b τ − k ρ = 3/4`; `mem_den_unstable_of_fold_of_Qtδ_eq_zero`). -/
@[tmio TM, powerlib_domain] theorem dzFold_mem_den_unstable :
    connection% (dzFold ∈ family.den (.flow .unstable)) := by
  obtain ⟨heq, -, hC, hc, -⟩ := dzFold_fold
  refine mem_den_unstable_of_fold_of_Qtδ_eq_zero dzFold (by norm_num [dzFold])
    (by norm_num [dzFold]) heq hC hc ?_ ?_ ?_ ?_ ?_
  all_goals norm_num [dzFold, routhTrace, gain, Ptδ, PtE, Qtδ, QtE, Ptδδ, Qtδδ, emf, ztsq]

end QVDroopVirtual

end powerlib.GFM
