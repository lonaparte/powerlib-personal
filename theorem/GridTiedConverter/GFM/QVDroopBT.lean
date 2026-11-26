import theorem.GridTiedConverter.GFM.QVDroopCusp
import theorem.Dynamics.BTInstability

/-! # Grid-forming converter with Q–V droop: the Bogdanov–Takens points of the fold

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroop.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P(δ, E) − D Δω`, `Q̇_f = ω_q (Q(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, line `Z = R + jX` to a stiff grid `V ∠ 0`, export-positive powers,
  continuous time, autonomous. Read about a selected point (`QVDroop.Model`) on
  `QVDroop.family`. Excluded as there.
* The double-zero points of the fold: `C = k a − b c = 0` and `a + D ω_q k = 0` (`a = P_δ`,
  `b = n_q P_E`, `c = Q_δ`, `k = K = 1 + n_q Q_E` at `(δ*, E*)`), where
  `det(sI − J) = s² (s + A/M)`, `A = D + M ω_q K`. Parameters are free reals; every theorem lists
  its range. Not decided here: `A = 0` (a triple zero), `K = 0`, `E* = 0`, and the
  Bogdanov–Takens–cusp points `𝔉 = 0` (codimension three; none in the physical range).
* Level: the Bogdanov–Takens chain and Kuznetsov's coefficient `a` (static), and Lyapunov
  instability (LeanForControl's `Unstable`).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §8.4 and §8.7 (the chain
and the projection formula `a = ½⟨p₁, B(q₀, q₀)⟩`); the cusp law
`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`
(`theorem/Dynamics/BTInstability.lean`); the derivative form `QVDroop.bForm`, the right null
vector `QVDroop.foldQ`, the characteristic polynomial `QVDroop.Model.charpoly_fold` and the fold
law of `theorem/GridTiedConverter/GFM/QVDroopFold.lean`, the physical-range facts of
`theorem/GridTiedConverter/GFM/QVDroopCusp.lean`. The chain and the coefficient were derived by
hand from the null vectors of `Criteria.droopJacobian` and the identity
`c (ω_q k M B₁ + b B₂) = k ω_q 𝔉` modulo `C` (the certificate of `QVDroop.Model.foldCoeff_fold`),
and are proved here by `field_simp` and `linear_combination`.

Results.
* `QVDroop.btQ1` (`q₁ = (0, k, −c/(ω_q k))`) and `QVDroop.btP1`
  (`p₁ = (D ω_q k, M ω_q k, b)/(k A)`); **`QVDroop.Model.exists_isBTChain_of_bt`**: at a double
  zero with `M, ω_q, K, A ≠ 0`, `(foldQ, btQ1)` and `btP1` complete to a normalised
  Bogdanov–Takens chain (every null vector is a multiple of `q₀`).
* **`QVDroop.Model.coeffA_bt`**: `2 c A a = ω_q 𝔉`, `𝔉 = QVDroop.foldQuad` the cusp quadric of the
  fold: the Bogdanov–Takens coefficient vanishes exactly on the Bogdanov–Takens–cusp points
  `𝔉 = 0` (located; `𝔉 > 0` in the physical range, `QVDroop.foldQuad_pos_of_physical`).

Family and connection conclusions.
No new family: connection conclusions on `QVDroop.family`.
* **`QVDroop.mem_den_unstable_of_bt`**: for `M, ω_q > 0`, an equilibrium at a double zero
  (`C = 0`, `a + D ω_q K = 0`) with `A > 0`, `K ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable (the
  cusp).
* **`QVDroop.mem_den_unstable_of_fold_of_trace_ne`**: every fold equilibrium (`C = 0`) with
  `A ≠ 0`, `K, E* ≠ 0` and `𝔉 ≠ 0` is unstable (a Routh violation, the saddle-node law
  `QVDroop.mem_den_unstable_of_fold`, or the cusp): the double-zero set `C = G = 0` is decided off
  `A = 0`.
* **`QVDroop.mem_den_unstable_of_bt_of_physical`**,
  **`QVDroop.mem_den_unstable_of_fold_of_physical_of_trace_ne`**: in the physical range
  (`M, ω_q, n_q, X, V > 0`, `E₀ + n_q Q_ref > 0`, `E* > 0`) every equilibrium at a double zero
  with `A > 0`, and every fold equilibrium with `A ≠ 0`, is unstable, with no further
  hypothesis.
-/

noncomputable section
namespace powerlib.GFM.QVDroop
open Complex Matrix Polynomial
open scoped RealInnerProductSpace
open powerlib.Dynamics (State coord mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.NormalForm.BogdanovTakens (IsBTChain coeffA)
open powerlib.Criteria (droopJacobian)

/-- The second Jordan vector `q₁ = (0, k, −c/(ω_q k))` at a double zero of the fold. -/
def btQ1 (ω c k : ℝ) : State 3 := WithLp.toLp 2 ![0, k, -(c / (ω * k))]

/-- The left null vector `(D ω_q k, M ω_q k, b)/(k A)`, `A = D + M ω_q k`, normalised
against `btQ1`. -/
def btP1 (M D ω b k : ℝ) : State 3 :=
  WithLp.toLp 2 ((k * (D + M * ω * k))⁻¹ • ![D * ω * k, M * ω * k, b])

/-- The Jordan chain and the adjoint chain of `droopJacobian` at a double zero
`k a − b c = 0`, `a + D ω k = 0` (`M, ω, k ≠ 0`, `A = D + M ω k ≠ 0`): `J q₁ = q₀`, `p₁ᵀ J = 0`,
`⟨p₁, q₁⟩ = 1`. -/
@[tmio T, powerlib_foundation] private theorem droopJacobian_bt {M D ω a b c k : ℝ}
    (hM : M ≠ 0) (hω : ω ≠ 0) (hk : k ≠ 0)
    (hA : D + M * ω * k ≠ 0) (h0 : k * a - b * c = 0) (h1 : a + D * ω * k = 0) :
    droopJacobian M D ω a b c k *ᵥ ![0, k, -(c / (ω * k))] = ![k, 0, c] ∧
      ((k * (D + M * ω * k))⁻¹ • ![D * ω * k, M * ω * k, b]) ᵥ*
        droopJacobian M D ω a b c k = 0 ∧
      ((k * (D + M * ω * k))⁻¹ • ![D * ω * k, M * ω * k, b]) ⬝ᵥ ![0, k, -(c / (ω * k))] = 1 := by
  obtain ⟨-, hl⟩ := Criteria.droopJacobian_null (M := M) (D := D) (ω := ω) h0
  have hbc : b * c = -(D * ω * k ^ 2) := by linear_combination -h0 + k * h1
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [droopJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      field_simp
    linear_combination (-1 : ℝ) * hbc
  · have e : ![D * ω * k, M * ω * k, b] = M • ![D * ω * k / M, ω * k, b / M] := by
      ext i; fin_cases i <;> simp <;> field_simp
    rw [e, Matrix.smul_vecMul, Matrix.smul_vecMul, hl, smul_zero, smul_zero]
  · simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have e : M * ω * k * k + b * -(c / (ω * k)) = k * (D + M * ω * k) := by
      field_simp
      linear_combination (-1 : ℝ) * hbc
    rw [show (k * (D + M * ω * k))⁻¹ * (D * ω * k) * 0 + (k * (D + M * ω * k))⁻¹ * (M * ω * k) * k +
        (k * (D + M * ω * k))⁻¹ * b * -(c / (ω * k)) =
        (k * (D + M * ω * k))⁻¹ * (M * ω * k * k + b * -(c / (ω * k))) by ring, e,
      inv_mul_cancel₀ (mul_ne_zero hk hA)]

/-- Every null vector of `droopJacobian` is a multiple of `(k, 0, c)` (`ω, k ≠ 0`). -/
@[tmio T, powerlib_foundation] private theorem droopJacobian_eq_smul_of_mulVec_eq_zero
    {M D ω a b c k : ℝ} (hω : ω ≠ 0) (hk : k ≠ 0)
    {v : Fin 3 → ℝ} (hv : droopJacobian M D ω a b c k *ᵥ v = 0) :
    v = (v 0 / k) • ![k, 0, c] := by
  have h0 : (droopJacobian M D ω a b c k *ᵥ v) 0 = 0 := by rw [hv]; rfl
  have h2 : (droopJacobian M D ω a b c k *ᵥ v) 2 = 0 := by rw [hv]; rfl
  simp [droopJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h2
  funext i
  fin_cases i
  · simp; field_simp
  · simp [h0]
  · simp
    field_simp
    have : ω * (c * v 0 - k * v 2) = 0 := by linear_combination h2
    have h' := (mul_eq_zero.mp this).resolve_left hω
    linear_combination -h'

@[tmio M, powerlib_domain] private theorem model_fderiv_eq (m : Model) :
    fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
      (droopJacobian m.q.M m.q.D m.q.ωq (m.q.Pδ m.δ (m.q.emf m.Qf))
        (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf))) := by
  rw [m.fderiv_field, Model.jacobian, jacobian_eq_droopJacobian]

/-- **The Bogdanov–Takens chain at a double zero.** At `C = k a − b c = 0`, `a + D ω_q k = 0`
with `M, ω_q, K ≠ 0` and `A = D + M ω_q K ≠ 0`, the right null vector `q₀ = (k, 0, c)`
(`QVDroop.foldQ`), `q₁ = QVDroop.btQ1` and the left null vector `p₁ = QVDroop.btP1` complete to a
normalised Bogdanov–Takens chain of the Jacobian (`IsBTChain.exists_of_left`; every null vector
is a multiple of `q₀`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_isBTChain_of_bt (m : Model) (hM : m.q.M ≠ 0)
    (hω : m.q.ωq ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hBT : m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0)
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) ≠ 0) :
    ∃ p₀ : State 3, IsBTChain (fderiv ℝ m.field 0)
      (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
      (btQ1 m.q.ωq (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))) p₀
      (btP1 m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf))) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hA' : m.q.D + m.q.M * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 := hA
  rw [model_fderiv_eq, foldQ, btQ1, btP1]
  generalize m.q.Pδ m.δ (m.q.emf m.Qf) = a at h0 hBT ⊢
  generalize m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) = b at h0 ⊢
  generalize m.q.Qδ m.δ (m.q.emf m.Qf) = c at h0 ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 hBT hk hA' ⊢
  obtain ⟨hq1, hl, hn⟩ := droopJacobian_bt hM hω hk hA' h0 hBT
  have hin : ∀ x y : Fin 3 → ℝ, ⟪(WithLp.toLp 2 x : State 3), WithLp.toLp 2 y⟫ = x ⬝ᵥ y :=
    fun x y => by rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  refine NormalForm.BogdanovTakens.IsBTChain.exists_of_left ?_ ?_ (fun v hv => ?_)
    (fun v => ?_) ?_
  · rw [Matrix.toEuclideanCLM_toLp, (Criteria.droopJacobian_null h0).1]; rfl
  · rw [Matrix.toEuclideanCLM_toLp, hq1]
  · have hv' : droopJacobian m.q.M m.q.D m.q.ωq a b c k *ᵥ (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa [Matrix.ofLp_toEuclideanCLM] using this
    have he := droopJacobian_eq_smul_of_mulVec_eq_zero hω hk hv'
    refine ⟨v 0 / k, ?_⟩
    ext i
    have := congrFun he i
    simpa using this
  · rw [Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec, hl, zero_dotProduct]
  · rw [hin, hn]

/-- **The Bogdanov–Takens coefficient `a`.** At a fold `C = 0` with `M, E*, K, A ≠ 0`, Kuznetsov's
`a = ½⟨p₁, B(q₀, q₀)⟩` of `q₀ = QVDroop.foldQ`, `p₁ = QVDroop.btP1` satisfies
`2 c A a = ω_q 𝔉(a, c, k, n_q/E*)` (`𝔉 = QVDroop.foldQuad`, the cusp quadric of the fold). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.coeffA_bt (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) ≠ 0) :
    2 * m.q.Qδ m.δ (m.q.emf m.Qf) * m.q.routhTrace m.δ (m.q.emf m.Qf) *
      coeffA m.field 0 (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
        (btP1 m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf))) =
      m.q.ωq * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hB : ∀ r : Fin 3, (fderiv ℝ (fderiv ℝ m.field) 0
      (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
      (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) r : ℂ) =
      bForm m.q.M m.q.ωq (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
        (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf)
        (toC (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))))
        (toC (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))) r := by
    intro r
    have h := congrFun (bilinC_toC m.field 0
      (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
      (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))) r
    rw [m.bilinC_field hE, iteratedFDeriv_two_apply] at h
    rw [h]
    simp
  have v0 := hB 0
  have v1 := hB 1
  have v2 := hB 2
  have hA' : m.q.D + m.q.M * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 := hA
  rw [coeffA, routhTrace]
  generalize fderiv ℝ (fderiv ℝ m.field) 0
    (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
    (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) = v at v0 v1 v2 ⊢
  generalize m.q.Pδ m.δ (m.q.emf m.Qf) = a at h0 v1 v2 v0 ⊢
  generalize m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) = b at h0 v1 v2 v0 ⊢
  generalize m.q.Qδ m.δ (m.q.emf m.Qf) = c at h0 v1 v2 v0 ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 hk hA' v1 v2 v0 ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at v1 v2 v0 ⊢
  simp only [bForm, toC, foldQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at v0 v1 v2
  have e1 : v 1 = c / m.q.M * (k * k) + μ * a / m.q.M * (k * c + c * k) -
      μ * (b - μ * c) / m.q.M * (c * c) := by
    apply Complex.ofReal_injective; rw [v1]; push_cast; ring
  have e2 : v 2 = m.q.ωq * a * (k * k) - m.q.ωq * μ * c * (k * c + c * k) +
      m.q.ωq * μ * (k - 1 + μ * a) * (c * c) := by
    apply Complex.ofReal_injective; rw [v2]; push_cast; ring
  have hv0 : v 0 = 0 := by apply Complex.ofReal_injective; rw [v0]; simp
  have hM1 : m.q.M * v 1 = c * k ^ 2 + 2 * μ * a * k * c - μ * (b - μ * c) * c ^ 2 := by
    rw [e1]; field_simp; ring
  have key : c * (m.q.ωq * k * (m.q.M * v 1) + b * v 2) = k * m.q.ωq * foldQuad a c k μ := by
    rw [hM1, e2]
    unfold foldQuad
    linear_combination (-(m.q.ωq * (a * c ^ 2 * μ ^ 2 + a * k ^ 2 - 2 * c ^ 2 * k * μ -
      c ^ 2 * μ))) * h0
  simp only [btP1, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hv0]
  trans k⁻¹ * (c * (m.q.ωq * k * (m.q.M * v 1) + b * v 2))
  · field_simp
    ring
  · rw [key]
    field_simp

/-- **The Bogdanov–Takens points are unstable** (the cusp,
`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`). For `M, ω_q > 0`, an
equilibrium at a double zero of the fold (`C = 0`, `P_δ + D ω_q K = 0`) with `A > 0` (the third
eigenvalue `−A/M` stable), `K ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable: `a = ω_q 𝔉/(2 c A) ≠ 0`
(`QVDroop.Model.coeffA_bt`; `𝔉 ≠ 0` forces `c = Q_δ ≠ 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bt (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq)
    (heq : m.q.field m.point = 0) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hBT : m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0)
    (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hE : m.q.emf m.Qf ≠ 0)
    (hQ : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨p₀, hch⟩ := m.exists_isBTChain_of_bt hM.ne' hω.ne' hC hBT hk hA.ne'
  have heq0 : m.field 0 = 0 := by simpa [Model.field] using heq
  have hker : ∀ v, fderiv ℝ m.field 0 v = 0 → ∃ s : ℝ,
      v = s • foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)) := by
    intro v hv
    rw [model_fderiv_eq] at hv
    have hv' : droopJacobian m.q.M m.q.D m.q.ωq (m.q.Pδ m.δ (m.q.emf m.Qf))
        (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) *ᵥ (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa [Matrix.ofLp_toEuclideanCLM] using this
    have he := droopJacobian_eq_smul_of_mulVec_eq_zero hω.ne' hk hv'
    refine ⟨v 0 / m.q.gain m.δ (m.q.emf m.Qf), ?_⟩
    ext i
    have := congrFun he i
    simpa [foldQ] using this
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
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hc : m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    intro hc0
    apply hQ
    have ha0 : m.q.Pδ m.δ (m.q.emf m.Qf) = 0 := by
      rw [hc0, mul_zero, sub_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hk
    simp [foldQuad, hc0, ha0]
  refine hch.unstable_of_coeffA_ne_zero (m.contDiff_field (k := 2)) heq0 hker hchar hr ?_
  intro h
  have key := m.coeffA_bt hM.ne' hC hE hk hA.ne'
  rw [h, mul_zero] at key
  exact mul_ne_zero hω.ne' hQ key.symm

/-- **Every nondegenerate fold with `A ≠ 0` is unstable.** For `M, ω_q > 0`, an equilibrium with
`C = 0`, `A ≠ 0`, `K ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable: with `G = A (P_δ + D ω_q K)` at a
fold (`QVDroop.routhHopf_eq`), a strict Routh violation (`A < 0`, or `G < 0`), the saddle-node law
(`QVDroop.mem_den_unstable_of_fold`, `P_δ + D ω_q K > 0`) or the cusp
(`QVDroop.mem_den_unstable_of_bt`, `P_δ + D ω_q K = 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_trace_ne (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq)
    (heq : m.q.field m.point = 0) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) ≠ 0)
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hE : m.q.emf m.Qf ≠ 0)
    (hQ : foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  rcases hA.lt_or_gt with hA | hA
  · exact mem_den_unstable_of_violation m hM hω heq (Or.inl hA)
  have hGe := m.q.routhHopf_eq m.δ (m.q.emf m.Qf)
  rw [hC, mul_zero, sub_zero] at hGe
  rcases lt_trichotomy (m.q.Pδ m.δ (m.q.emf m.Qf) +
    m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) 0 with h1 | h1 | h1
  · exact mem_den_unstable_of_violation m hM hω heq
      (Or.inr (Or.inr (by rw [hGe]; exact mul_neg_of_pos_of_neg hA h1)))
  · exact mem_den_unstable_of_bt m hM hω heq hC h1 hA hk hE hQ
  · exact mem_den_unstable_of_fold m hM hω heq hC hA h1 hk hE hQ

/-! ## The physical range -/

/-- **Every physical Bogdanov–Takens point is unstable.** In the physical range
(`M, ω_q, n_q, X, V > 0`, `E₀ + n_q Q_ref > 0`) an equilibrium with `E* > 0` at a double zero
(`C = 0`, `P_δ + D ω_q K = 0`) with `A > 0` is unstable: `K > 0`, `Q_δ ≠ 0` and `𝔉 > 0` there
(`QVDroop.Model.gain_pos_of_physical`, `QVDroop.Qδ_ne_zero_of_fold`,
`QVDroop.foldQuad_pos_of_physical`), so `QVDroop.mem_den_unstable_of_bt` applies. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bt_of_physical (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X) (hV : 0 < m.q.V)
    (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hBT : m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0)
    (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hk := m.gain_pos_of_physical hM hω hnq hX hlev heq hE
  have hc := m.q.Qδ_ne_zero_of_fold (m.q.zsq_pos hX.ne').ne' (mul_ne_zero hE.ne' hV.ne') hk.ne' hC
  exact mem_den_unstable_of_bt m hM hω heq hC hBT hA hk.ne' hE.ne'
    (m.q.foldQuad_pos_of_physical hX hnq hE hk hc).ne'

/-- **Every physical fold point with `A ≠ 0` is unstable.** In the physical range an equilibrium
with `E* > 0` at a fold (`C = 0`) with `A ≠ 0` is unstable
(`QVDroop.mem_den_unstable_of_fold_of_trace_ne`; `K > 0`, `Q_δ ≠ 0`, `𝔉 > 0` there): the
double-zero points `C = G = 0` of the physical range are decided off `A = 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_physical_of_trace_ne (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X) (hV : 0 < m.q.V)
    (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hk := m.gain_pos_of_physical hM hω hnq hX hlev heq hE
  have hc := m.q.Qδ_ne_zero_of_fold (m.q.zsq_pos hX.ne').ne' (mul_ne_zero hE.ne' hV.ne') hk.ne' hC
  exact mem_den_unstable_of_fold_of_trace_ne m hM hω heq hC hA hk.ne' hE.ne'
    (m.q.foldQuad_pos_of_physical hX hnq hE hk hc).ne'
