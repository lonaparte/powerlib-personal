import theorem.GridTiedConverter.GFM.QVDroopVirtualCusp
import theorem.GridTiedConverter.GFM.QVDroopBT
import theorem.Dynamics.BTInstability

/-! # Q–V droop with a virtual impedance: the Bogdanov–Takens points of the fold

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P_t(δ, E) − D Δω`, `Q̇_f = ω_q (Q_t(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, the powers measured at the converter terminal behind the virtual
  impedance `Z_v = R_v + jX_v`, the grid branch `Z_g = R_g + jX_g` to a stiff grid `V ∠ 0`,
  export-positive, continuous time, autonomous. Read about a selected point
  (`QVDroopVirtual.Model`) on `QVDroopVirtual.family`. Excluded as there.
* The double-zero points of the fold: `C = k a − b c = 0` and `a + D ω_q k = 0` (`a = P_tδ`,
  `b = n_q P_tE`, `c = Q_tδ`, `k = K_t` at `(δ*, E*)`), where `det(sI − J) = s² (s + A/M)`,
  `A = D + M ω_q K_t`. Parameters are free reals; every theorem lists its range. Not decided
  here: `A = 0` (a triple zero), `K_t = 0`, `E* = 0`, and the Bogdanov–Takens–cusp points
  `𝔉 = 0` (none in the physical range with `D ≠ 0`).
* Level: the Bogdanov–Takens chain and Kuznetsov's coefficient `a` (static), and Lyapunov
  instability (LeanForControl's `Unstable`).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.4 and §8.7 (the chain
and the projection formula `a = ½⟨p₁, B(q₀, q₀)⟩`); the cusp law
`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`
(`theorem/Dynamics/BTInstability.lean`); the chain vectors `QVDroop.foldQ`, `QVDroop.btQ1`,
`QVDroop.btP1` of `theorem/GridTiedConverter/GFM/QVDroopBT.lean` (the Jacobian pattern is the
same `Criteria.droopJacobian`, only the second derivative differs) and the chain and kernel laws
`Criteria.droopJacobian_bt`, `Criteria.droopJacobian_eq_smul_of_mulVec_eq_zero`
(`theorem/Criteria/DroopJacobian.lean`); the derivative form
`QVDroopVirtual.bForm` and the characteristic polynomial `QVDroopVirtual.Model.charpoly_fold` of
`theorem/GridTiedConverter/GFM/QVDroopVirtualFold.lean`; the physical-range facts of
`theorem/GridTiedConverter/GFM/QVDroopVirtualCusp.lean`. The coefficient identity is the one of
`QVDroopVirtual.Model.foldCoeff_fold` (the same vector `(D ω_q k, M ω_q k, b)` pairs with
`B(q₀, q₀)`), proved here by `field_simp` and `linear_combination`.

Results.
* **`QVDroopVirtual.Model.exists_isBTChain_of_bt`**: at a double zero with `M, ω_q, K_t, A ≠ 0`,
  `(QVDroop.foldQ, QVDroop.btQ1)` and `QVDroop.btP1` complete to a normalised Bogdanov–Takens
  chain of the Jacobian (every null vector is a multiple of `q₀`).
* **`QVDroopVirtual.Model.coeffA_bt`**: `2 c A a = ω_q 𝔉`, `𝔉 = QVDroopVirtual.foldQuad` the cusp
  quantity of the fold: the Bogdanov–Takens coefficient vanishes exactly on the
  Bogdanov–Takens–cusp points `𝔉 = 0`.

Family and connection conclusions.
No new family: connection conclusions on `QVDroopVirtual.family`.
* **`QVDroopVirtual.mem_den_unstable_of_bt`**: for `M, ω_q > 0`, an equilibrium at a double zero
  (`C = 0`, `P_tδ + D ω_q K_t = 0`) with `A > 0`, `K_t ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable.
* **`QVDroopVirtual.mem_den_unstable_of_fold_of_trace_ne`**: every fold equilibrium (`C = 0`)
  with `A ≠ 0`, `K_t, E* ≠ 0` and `𝔉 ≠ 0` is unstable (a Routh violation, the saddle-node law
  `QVDroopVirtual.mem_den_unstable_of_fold`, or the cusp).
* **`QVDroopVirtual.mem_den_unstable_of_bt_of_physical`**: in the physical range
  (`M, ω_q, n_q, X_g > 0`, `X_v ≥ 0`, `E₀ + n_q Q_ref > 0`, `E* > 0`) with `D ≠ 0` every
  equilibrium at a double zero with `A > 0` is unstable, with no further hypothesis (`K_t > 0`;
  `Q_tδ = 0` would force `D ω_q K_t = 0`; `𝔉 ≠ 0` by
  `QVDroopVirtual.foldQuad_ne_zero_of_physical`).
-/

noncomputable section
namespace powerlib.GFM.QVDroopVirtual
open Complex Matrix Polynomial
open scoped RealInnerProductSpace
open powerlib.Dynamics (State coord mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.NormalForm.BogdanovTakens (IsBTChain coeffA)
open powerlib.Criteria (droopJacobian)

@[tmio M, powerlib_domain] private theorem model_fderiv_eq (m : Model) :
    fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
      (droopJacobian m.q.M m.q.D m.q.ωq (m.q.Ptδ m.δ (m.q.emf m.Qf))
        (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf))) := by
  rw [m.fderiv_field, Model.jacobian, jacobian_eq_droopJacobian]

/-- **The Bogdanov–Takens chain at a double zero.** At `C = k a − b c = 0`, `a + D ω_q k = 0`
with `M, ω_q, K_t ≠ 0` and `A = D + M ω_q K_t ≠ 0`, the right null vector `q₀ = (k, 0, c)`
(`QVDroop.foldQ`), `q₁ = QVDroop.btQ1` and the left null vector `p₁ = QVDroop.btP1` complete to a
normalised Bogdanov–Takens chain of the Jacobian (`IsBTChain.exists_of_left`; every null vector
is a multiple of `q₀`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_isBTChain_of_bt (m : Model) (hM : m.q.M ≠ 0)
    (hω : m.q.ωq ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hBT : m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0)
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) ≠ 0) :
    ∃ p₀ : State 3, IsBTChain (fderiv ℝ m.field 0)
      (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
      (QVDroop.btQ1 m.q.ωq (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))) p₀
      (QVDroop.btP1 m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf))) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hA' : m.q.D + m.q.M * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 := hA
  rw [model_fderiv_eq, QVDroop.foldQ, QVDroop.btQ1, QVDroop.btP1]
  generalize m.q.Ptδ m.δ (m.q.emf m.Qf) = a at h0 hBT ⊢
  generalize m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) = b at h0 ⊢
  generalize m.q.Qtδ m.δ (m.q.emf m.Qf) = c at h0 ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 hBT hk hA' ⊢
  obtain ⟨hq1, hl, hn⟩ := Criteria.droopJacobian_bt hM hω hk hA' h0 hBT
  have hin : ∀ x y : Fin 3 → ℝ, ⟪(WithLp.toLp 2 x : State 3), WithLp.toLp 2 y⟫ = x ⬝ᵥ y :=
    fun x y => by rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  refine NormalForm.BogdanovTakens.IsBTChain.exists_of_left ?_ ?_ (fun v hv => ?_)
    (fun v => ?_) ?_
  · rw [Matrix.toEuclideanCLM_toLp, (Criteria.droopJacobian_null h0).1]; rfl
  · rw [Matrix.toEuclideanCLM_toLp, hq1]
  · have hv' : droopJacobian m.q.M m.q.D m.q.ωq a b c k *ᵥ (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa [Matrix.ofLp_toEuclideanCLM] using this
    have he := Criteria.droopJacobian_eq_smul_of_mulVec_eq_zero hω hk hv'
    refine ⟨v 0 / k, ?_⟩
    ext i
    have := congrFun he i
    simpa using this
  · rw [Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec, hl, zero_dotProduct]
  · rw [hin, hn]

/-- **The Bogdanov–Takens coefficient `a`.** At a fold `C = 0` with `M, E*, K_t, A ≠ 0`,
Kuznetsov's `a = ½⟨p₁, B(q₀, q₀)⟩` of `q₀ = QVDroop.foldQ`, `p₁ = QVDroop.btP1` satisfies
`2 c A a = ω_q 𝔉(a, c, k, n_q/E*, ρ, τ)` (`𝔉 = QVDroopVirtual.foldQuad`, the cusp quantity of the
fold). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.coeffA_bt (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) ≠ 0) :
    2 * m.q.Qtδ m.δ (m.q.emf m.Qf) * m.q.routhTrace m.δ (m.q.emf m.Qf) *
      coeffA m.field 0 (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
        (QVDroop.btP1 m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf))) =
      m.q.ωq * foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
        (m.q.Qtδδ m.δ (m.q.emf m.Qf)) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  have v1 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 1
  have v2 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 2
  have v0 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 0
  have hA' : m.q.D + m.q.M * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 := hA
  rw [coeffA, routhTrace]
  generalize fderiv ℝ (fderiv ℝ m.field) 0
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) = v at v0 v1 v2 ⊢
  generalize m.q.Ptδ m.δ (m.q.emf m.Qf) = a at h0 v1 v2 v0 ⊢
  generalize m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) = b at h0 v1 v2 v0 ⊢
  generalize m.q.Qtδ m.δ (m.q.emf m.Qf) = c at h0 v1 v2 v0 ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 hk hA' v1 v2 v0 ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at v1 v2 v0 ⊢
  generalize m.q.Ptδδ m.δ (m.q.emf m.Qf) = ρ at v1 v2 v0 ⊢
  generalize m.q.Qtδδ m.δ (m.q.emf m.Qf) = τ at v1 v2 v0 ⊢
  simp only [bForm, toC, QVDroop.foldQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at v0 v1 v2
  have e1 : v 1 = -(ρ / m.q.M) * (k * k) + μ * a / m.q.M * (k * c + c * k) -
      μ * (b + μ * ρ) / m.q.M * (c * c) := by
    apply Complex.ofReal_injective; rw [v1]; push_cast; ring
  have e2 : v 2 = m.q.ωq * τ * (k * k) - m.q.ωq * μ * c * (k * c + c * k) +
      m.q.ωq * μ * (k - 1 + μ * τ) * (c * c) := by
    apply Complex.ofReal_injective; rw [v2]; push_cast; ring
  have hv0 : v 0 = 0 := by apply Complex.ofReal_injective; rw [v0]; simp
  have hM1 : m.q.M * v 1 = -(ρ * k ^ 2) + 2 * μ * a * k * c - μ * (b + μ * ρ) * c ^ 2 := by
    rw [e1]; field_simp; ring
  have key : c * (m.q.ωq * k * (m.q.M * v 1) + b * v 2) = k * m.q.ωq * foldQuad a c k μ ρ τ := by
    rw [hM1, e2]
    unfold foldQuad
    linear_combination (-(m.q.ωq * (c ^ 2 * μ ^ 2 * τ + k ^ 2 * τ - 2 * c ^ 2 * k * μ -
      c ^ 2 * μ))) * h0
  simp only [QVDroop.btP1, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hv0]
  trans k⁻¹ * (c * (m.q.ωq * k * (m.q.M * v 1) + b * v 2))
  · field_simp
    ring
  · rw [key]
    field_simp

/-- **The Bogdanov–Takens points are unstable** (the cusp,
`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`). For `M, ω_q > 0`, an
equilibrium at a double zero of the fold (`C = 0`, `P_tδ + D ω_q K_t = 0`) with `A > 0` (the
third eigenvalue `−A/M` stable), `K_t ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable:
`a = ω_q 𝔉/(2 c A) ≠ 0` (`QVDroopVirtual.Model.coeffA_bt`; `𝔉 ≠ 0` forces `c = Q_tδ ≠ 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bt (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq)
    (heq : m.q.field m.point = 0) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hBT : m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0)
    (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hE : m.q.emf m.Qf ≠ 0)
    (hQ : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨p₀, hch⟩ := m.exists_isBTChain_of_bt hM.ne' hω.ne' hC hBT hk hA.ne'
  have heq0 : m.field 0 = 0 := by simpa [Model.field] using heq
  have hker : ∀ v, fderiv ℝ m.field 0 v = 0 → ∃ s : ℝ,
      v = s • QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)) := by
    intro v hv
    rw [model_fderiv_eq] at hv
    have hv' : droopJacobian m.q.M m.q.D m.q.ωq (m.q.Ptδ m.δ (m.q.emf m.Qf))
        (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) *ᵥ (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa [Matrix.ofLp_toEuclideanCLM] using this
    have he := Criteria.droopJacobian_eq_smul_of_mulVec_eq_zero hω.ne' hk hv'
    refine ⟨v 0 / m.q.gain m.δ (m.q.emf m.Qf), ?_⟩
    ext i
    have := congrFun he i
    simpa [QVDroop.foldQ] using this
  have hchar : (cmat (fderiv ℝ m.field 0)).charpoly =
      Polynomial.X ^ 2 * (Polynomial.X +
        Polynomial.C (((m.q.routhTrace m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ)) := by
    have h := m.charpoly_fold hM.ne' hC
    rw [hBT, zero_div] at h
    rw [show cmat (fderiv ℝ m.field 0) = jacobianC m.field 0 from rfl, h]
    simp
    ring
  have hr : ∀ s : ℂ, (Polynomial.X +
      Polynomial.C (((m.q.routhTrace m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ)).eval s = 0 →
      s.re < 0 := by
    intro s hs
    simp only [eval_add, eval_X, eval_C] at hs
    have : s = -(((m.q.routhTrace m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ) := by
      linear_combination hs
    rw [this]
    simp only [neg_re, ofReal_re, Left.neg_neg_iff]
    exact div_pos hA hM
  refine hch.unstable_of_coeffA_ne_zero (m.contDiff_field (k := 2)) heq0 hker hchar hr ?_
  intro h
  have key := m.coeffA_bt hM.ne' hC hE hk hA.ne'
  rw [h, mul_zero] at key
  exact mul_ne_zero hω.ne' hQ key.symm

/-- **Every nondegenerate fold with `A ≠ 0` is unstable.** For `M, ω_q > 0`, an equilibrium with
`C = 0`, `A ≠ 0`, `K_t ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable: with `G = A (P_tδ + D ω_q K_t)` at a
fold (`QVDroopVirtual.routhHopf_eq`), a strict Routh violation (`A < 0`, or `G < 0`), the
saddle-node law (`QVDroopVirtual.mem_den_unstable_of_fold`, `P_tδ + D ω_q K_t > 0`) or the cusp
(`QVDroopVirtual.mem_den_unstable_of_bt`, `P_tδ + D ω_q K_t = 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_trace_ne (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq)
    (heq : m.q.field m.point = 0) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) ≠ 0)
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hE : m.q.emf m.Qf ≠ 0)
    (hQ : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  rcases hA.lt_or_gt with hA | hA
  · exact mem_den_unstable_of_violation m hM hω heq (Or.inl hA)
  have hGe := m.q.routhHopf_eq m.δ (m.q.emf m.Qf)
  rw [hC, mul_zero, sub_zero] at hGe
  rcases lt_trichotomy (m.q.Ptδ m.δ (m.q.emf m.Qf) +
    m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) 0 with h1 | h1 | h1
  · exact mem_den_unstable_of_violation m hM hω heq
      (Or.inr (Or.inr (by rw [hGe]; exact mul_neg_of_pos_of_neg hA h1)))
  · exact mem_den_unstable_of_bt m hM hω heq hC h1 hA hk hE hQ
  · exact mem_den_unstable_of_fold m hM hω heq hC hA h1 hk hE hQ

/-! ## The physical range -/

/-- **Every physical Bogdanov–Takens point is unstable.** In the physical range
(`M, ω_q, n_q, X_g > 0`, `X_v ≥ 0`, `E₀ + n_q Q_ref > 0`) with `D ≠ 0`, an equilibrium with
`E* > 0` at a double zero (`C = 0`, `P_tδ + D ω_q K_t = 0`) with `A > 0` is unstable: `K_t > 0`
(`QVDroopVirtual.Model.gain_pos_of_physical`), `Q_tδ ≠ 0` (else `P_tδ = 0` and
`D ω_q K_t = 0`) and `𝔉 ≠ 0` (`QVDroopVirtual.foldQuad_ne_zero_of_physical`), so
`QVDroopVirtual.mem_den_unstable_of_bt` applies. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bt_of_physical (m : Model)
    (hM : 0 < m.q.M) (hD : m.q.D ≠ 0) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hXg : 0 < m.q.Xg)
    (hXv : 0 ≤ m.q.Xv) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hBT : m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0)
    (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hk := m.gain_pos_of_physical hM.ne' hω.ne' hnq hXg hXv hlev heq hE
  have hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    intro hc0
    have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
        m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
    rw [hc0, mul_zero, sub_zero] at h0
    have ha0 := (mul_eq_zero.mp h0).resolve_left hk.ne'
    rw [ha0, zero_add] at hBT
    exact mul_ne_zero (mul_ne_zero hD hω.ne') hk.ne' hBT
  exact mem_den_unstable_of_bt m hM hω heq hC hBT hA hk.ne' hE.ne'
    (m.q.foldQuad_ne_zero_of_physical hXg hXv hnq hE hC hc)

end QVDroopVirtual

end powerlib.GFM
