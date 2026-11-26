import theorem.GridTiedConverter.GFM.QVDroopHopf
import theorem.Dynamics.ZeroHopfReduction

/-! # Grid-forming converter with Q–V droop: the zero–Hopf points of the fold

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroop.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P(δ, E) − D Δω`, `Q̇_f = ω_q (Q(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, line `Z = R + jX` to a stiff grid `V ∠ 0`, export-positive powers,
  continuous time, autonomous. Read about a selected point (`QVDroop.Model`) on
  `QVDroop.family`.
* The zero–Hopf points: equilibria at a fold `C = K P_δ − n_q P_E Q_δ = 0` with `A = D + M ω_q K
  = 0` and `a₁ = (P_δ + D ω_q K)/M > 0`, `M, D, ω_q > 0`, `E* ≠ 0`:
  `det(sI − J) = s (s² + w²)`, `w² = a₁`; the centre manifold is the whole state space. Data
  `a = P_δ`, `c = Q_δ`, `k = K`, `μ = n_q/E*`, `𝔉 = (a² + c²)(c²μ² + k²) − a c² μ` (`foldQuad`).
* Level: Lyapunov instability (LeanForControl's `Unstable`) through `QVDroop.family`; exact
  closed forms of the three normal-form coefficients.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.5 and §8.7 (the
zero–Hopf normal form and its projection formulas); the generic law
`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`
(`theorem/Dynamics/ZeroHopfReduction.lean`); the fold data of
`theorem/GridTiedConverter/GFM/QVDroopFold.lean` (`QVDroop.Model.isNullPair_fold`,
`Model.foldCoeff_fold`, `Model.charpoly_fold`, `Model.bilinC_field`) and the Hopf-surface vectors
of `theorem/GridTiedConverter/GFM/QVDroopHopf.lean` (`hopfQ`, `hopfP`, `hopf_right`,
`hopf_leftY`, `hopf_dotYQ`), here at `L = 0`. The coefficients were derived with exact computer
algebra (SymPy, untrusted discovery) and are proved here by `field_simp` and `ring`.

Results.
* `QVDroop.hopfN0_zeroHopf`, `hopfN0_ne_of_zeroHopf`, `zeroHopf_isCriticalPair` (the critical
  pair at `L = 0`), `zeroHopf_c`, `zeroHopf_b` (the coefficients in the data).
* **The coefficients at a zero–Hopf point** (`QVDroop.Model.zeroHopf_coeffs`):
  `a = ω_q 𝔉/(2 M c w²)`, `b = ω_q (ω_q² 𝔉 + w² (a_δ² + c²))/(2 M c w²)` (`a_δ = P_δ`),
  `c_ZH = −ω_q (𝔉 + M w² c² μ (1 − a_δ μ))/(2 M c w²)`; hence `ab > 0 ⇔ 𝔉 (ω_q² 𝔉 +
  w²(a_δ² + c²)) > 0`, `a(a − c_ZH) > 0 ⇔ 𝔉 (2𝔉 + M w² c² μ (1 − a_δ μ)) > 0`, and at `𝔉 = 0`:
  `b c_ZH > 0 ⇔ μ (1 − a_δ μ) < 0`.
* **Decided** (`QVDroop.Model.zeroHopfDecided_zeroHopf`): every zero–Hopf point with `𝔉 > 0`;
  with `𝔉 < 0` those with `ω_q² 𝔉 + w² (a_δ² + c²) < 0` or `2𝔉 + M w² c² μ (1 − a_δ μ) < 0`; at
  `𝔉 = 0` those with `μ (1 − a_δ μ) < 0`. **Located, not decided**: `𝔉 < 0` with both
  `ω_q² 𝔉 + w² (a_δ² + c²) ≥ 0` and `2𝔉 + M w² c² μ (1 − a_δ μ) ≥ 0` (the regimes `ab ≤ 0`,
  `a(a − c) ≤ 0` of `Dynamics.CenterManifold.ZeroHopfDecided`), and `𝔉 = 0`,
  `μ (1 − a_δ μ) ≥ 0`.

Family and connection conclusions.
No new family: connection conclusions on `QVDroop.family`.
* **`QVDroop.mem_den_unstable_of_zeroHopf`**: an equilibrium at a fold with `A = 0`, `a₁ > 0`
  and decided coefficients is unstable; **`QVDroop.mem_den_unstable_of_zeroHopf_of_foldQuad_pos`**:
  in particular every one with `𝔉 > 0`.
-/

noncomputable section
namespace powerlib.GFM.QVDroop
open Complex Matrix Polynomial
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Criteria (droopJacobian)
open powerlib.NormalForm.BogdanovTakens (foldCoeff)
open powerlib.Dynamics.CenterManifold (zhB zhC ZeroHopfDecided)

section ZeroHopfCore

variable {M D ω w k c μ : ℝ}

/-- At `L = D + M ω_q k = 0` the normalisation is `hopfN0 = −2Mw²(ω_q k + iw)`. -/
@[tmio M, powerlib_domain] theorem hopfN0_zeroHopf (hL : hopfL M D ω k = 0) :
    hopfN0 M D ω w k = ((-(2 * M * w ^ 2) : ℝ) : ℂ) * (((ω * k : ℝ) : ℂ) + (w : ℂ) * I) := by
  have hD : D = -(M * k * ω) := by simp only [hopfL] at hL; linarith
  apply Complex.ext <;>
    simp [hopfN0, hD, -Complex.ofReal_mul, -Complex.ofReal_pow, -Complex.ofReal_add,
      -Complex.ofReal_neg, -Complex.ofReal_sub] <;> ring

/-- At `L = 0` the normalisation `hopfN0` is nonzero (`M ≠ 0`, `w > 0`). -/
@[tmio M, powerlib_domain] theorem hopfN0_ne_of_zeroHopf (hM : M ≠ 0) (hw : 0 < w)
    (hL : hopfL M D ω k = 0) :
    hopfN0 M D ω w k ≠ 0 := by
  rw [hopfN0_zeroHopf hL]
  have h2 : (2 * M * w ^ 2) ≠ 0 := by positivity
  refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr h2)) ?_
  intro h; have := congrArg Complex.im h; simp at this; exact hw.ne' this

/-- **The critical pair at a zero–Hopf point**: a field vanishing at `x₀` whose Jacobian there
is the droop-loop Jacobian `hopfJ` with `L = D + M ω_q k = 0` (`M, ω_q, w > 0`, `c ≠ 0`) has the
critical pair `(hopfQ, hopfP)` at the frequency `w` (the eigen-relations `hopf_right`,
`hopf_leftY`, `hopf_dotYQ` hold on the whole parametrisation; only the normalisation needs
`hopfN0_ne_of_zeroHopf`). -/
@[tmio M, powerlib_domain] theorem zeroHopf_isCriticalPair {F : State 3 → State 3}
    {x₀ : State 3} (hM : 0 < M) (hω : 0 < ω) (hw : 0 < w) (hc : c ≠ 0)
    (hL : hopfL M D ω k = 0) (h0 : F x₀ = 0)
    (hJ : jacobianC F x₀ = Linear.complexify (hopfJ M D ω w k c)) :
    IsCriticalPair F x₀ w (hopfQ ω w k c) (hopfP M D ω w k c) := by
  have hN := hopfN0_ne_of_zeroHopf (w := w) hM.ne' hw hL
  have hpstar : star (hopfP M D ω w k c) = fun j => hopfY M D ω w k c j / hopfN0 M D ω w k := by
    funext j; simp [hopfP]
  refine ⟨h0, hw, ?_, ?_, ?_⟩
  · rw [hJ]; exact hopf_right hM.ne' hω.ne' hc
  · rw [hJ]
    have h := transpose_mulVec_conj_div (z := starRingEnd ℂ (hopfN0 M D ω w k))
      (hopf_leftY (D := D) (w := w) (k := k) hM.ne' hω.ne' hc)
    have e : starRingEnd ℂ ((w : ℂ) * I) = -((w : ℂ) * I) := by simp
    rw [e] at h
    exact h
  · rw [hpstar]
    simp only [dotProduct, Fin.sum_univ_three]
    have h := hopf_dotYQ (M := M) (D := D) (w := w) (k := k) hω.ne' hc
    simp only [dotProduct, Fin.sum_univ_three] at h
    rw [show hopfY M D ω w k c 0 / hopfN0 M D ω w k * hopfQ ω w k c 0 +
        hopfY M D ω w k c 1 / hopfN0 M D ω w k * hopfQ ω w k c 1 +
        hopfY M D ω w k c 2 / hopfN0 M D ω w k * hopfQ ω w k c 2 =
        (hopfY M D ω w k c 0 * hopfQ ω w k c 0 + hopfY M D ω w k c 1 * hopfQ ω w k c 1 +
          hopfY M D ω w k c 2 * hopfQ ω w k c 2) / hopfN0 M D ω w k by ring, h,
      div_self hN]

/-- **The coefficient `c`** at `L = 0`: `Re⟨hopfP, B(foldQ, hopfQ)⟩ =
−ω_q (𝔉 + M w² c² μ (1 − aμ))/(2 M c w²)`, `a = hopfA`, `𝔉 = foldQuad a c k μ`. -/
@[tmio M, powerlib_domain] theorem zeroHopf_c (hM : 0 < M) (hω : 0 < ω) (hw : 0 < w) (hc : c ≠ 0)
    (hL : hopfL M D ω k = 0) :
    (pairing (hopfP M D ω w k c) (bForm M ω (hopfA M D ω w k) (hopfB D ω w k c) c k μ
      (toC (foldQ k c)) (hopfQ ω w k c))).re =
      -(ω * (foldQuad (hopfA M D ω w k) c k μ +
        M * w ^ 2 * c ^ 2 * μ * (1 - hopfA M D ω w k * μ)) / (2 * M * c * w ^ 2)) := by
  have hD : D = -(M * k * ω) := by simp only [hopfL] at hL; linarith
  have hpc : ∀ j, starRingEnd ℂ (hopfP M D ω w k c j) =
      hopfY M D ω w k c j / hopfN0 M D ω w k := fun j => by simp [hopfP]
  have hAe : hopfA M D ω w k = M * (w ^ 2 + ω ^ 2 * k ^ 2) := by rw [hopfA, hD]; ring
  have hBe : hopfB D ω w k c = M * k * (w ^ 2 + ω ^ 2 * k ^ 2) / c := by
    rw [hopfB, hD]; field_simp
  rw [pairing_apply, Fin.sum_univ_three, hpc, hpc, hpc, hopfN0_zeroHopf hL]
  have p1 : ((w : ℂ) ^ 2).re = w ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have p2 : ((w : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  set r : ℝ := -(2 * M * w ^ 2 * (ω ^ 2 * k ^ 2 + w ^ 2))⁻¹ with hr
  have hrp : r * (-(2 * M * w ^ 2)) * (ω ^ 2 * k ^ 2 + w ^ 2) = 1 := by
    rw [hr]; field_simp
  have hr' : r = -1 / (2 * M * w ^ 2 * (ω ^ 2 * k ^ 2 + w ^ 2)) := by
    rw [hr]; field_simp
  clear_value r
  have hinv : (((-(2 * M * w ^ 2) : ℝ) : ℂ) * (((ω * k : ℝ) : ℂ) + (w : ℂ) * I))⁻¹ =
      (r : ℂ) * (((ω * k : ℝ) : ℂ) - (w : ℂ) * I) := by
    refine inv_eq_of_mul_eq_one_right ?_
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, p1, p2]
      linear_combination hrp
    · simp [Complex.mul_re, Complex.mul_im, p1, p2]
      ring
  simp only [div_eq_mul_inv, hinv]
  simp only [bForm, hopfY, hopfQ, foldQ, toC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.toLp_apply]
  generalize hopfA M D ω w k = A at hAe ⊢
  generalize hopfB D ω w k c = B at hBe ⊢
  simp [Complex.mul_re, Complex.mul_im, foldQuad, -Complex.ofReal_mul, -Complex.ofReal_pow,
    -Complex.ofReal_add, -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_div]
  subst hAe hBe hr' hD
  field_simp
  ring

/-- **The coefficient `b`** at `L = 0`: `½ Re⟨foldP, B(hopfQ, hopfQ̄)⟩ =
ω_q (ω_q² 𝔉 + w² (a² + c²))/(2 M c w²)`. -/
@[tmio M, powerlib_domain] theorem zeroHopf_b (hM : 0 < M) (hω : 0 < ω) (hw : 0 < w)
    (hc : c ≠ 0) (hk : k ≠ 0) (hL : hopfL M D ω k = 0) :
    (pairing (toC (foldP M D ω (hopfB D ω w k c) c k)) (bForm M ω (hopfA M D ω w k)
      (hopfB D ω w k c) c k μ (hopfQ ω w k c) (star (hopfQ ω w k c)))).re / 2 =
      ω * (ω ^ 2 * foldQuad (hopfA M D ω w k) c k μ + w ^ 2 * (hopfA M D ω w k ^ 2 + c ^ 2)) /
        (2 * M * c * w ^ 2) := by
  have hD : D = -(M * k * ω) := by simp only [hopfL] at hL; linarith
  have hAe : hopfA M D ω w k = M * (w ^ 2 + ω ^ 2 * k ^ 2) := by rw [hopfA, hD]; ring
  have hBe : hopfB D ω w k c = M * k * (w ^ 2 + ω ^ 2 * k ^ 2) / c := by
    rw [hopfB, hD]; field_simp
  rw [pairing_apply, Fin.sum_univ_three]
  simp only [bForm, hopfQ, foldP, toC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.toLp_apply, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul]
  generalize hopfA M D ω w k = A at hAe ⊢
  generalize hopfB D ω w k c = B at hBe ⊢
  simp [Complex.mul_re, Complex.mul_im, foldQuad, -Complex.ofReal_mul,
    -Complex.ofReal_pow, -Complex.ofReal_add, -Complex.ofReal_neg, -Complex.ofReal_sub,
    -Complex.ofReal_div]
  subst hAe hBe hD
  field_simp
  ring

end ZeroHopfCore

/-! ## The model at a zero–Hopf point -/

/-- **The data at a zero–Hopf point**: for `M, D, ω_q > 0`, at a fold `C = 0` with `A = 0` and
`a₁ = (P_δ + D ω_q K)/M > 0`, the frequency `w = Model.hopfFreq` is positive, `K ≠ 0`, `Q_δ ≠ 0`,
`L = 0` and the Jacobian data are the Hopf-surface data at `w`: `P_δ = hopfA`,
`n_q P_E = hopfB`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.zeroHopf_relations (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) = 0)
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) :
    0 < m.hopfFreq ∧ m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧ m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0 ∧
      hopfL m.q.M m.q.D m.q.ωq (m.q.gain m.δ (m.q.emf m.Qf)) = 0 ∧
      m.q.Pδ m.δ (m.q.emf m.Qf) =
        hopfA m.q.M m.q.D m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) ∧
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) = hopfB m.q.D m.q.ωq m.hopfFreq
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)) := by
  have hw : 0 < m.hopfFreq := Real.sqrt_pos.mpr (div_pos ha1 hM)
  have hw2 : m.hopfFreq ^ 2 = (m.q.Pδ m.δ (m.q.emf m.Qf) +
      m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) / m.q.M :=
    Real.sq_sqrt (div_pos ha1 hM).le
  have hC' : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hA' : m.q.D + m.q.M * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0 := hA
  generalize m.hopfFreq = w at hw hw2 ⊢
  generalize m.q.Pδ m.δ (m.q.emf m.Qf) = a at ha1 hC' hw2 ⊢
  generalize m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) = b at hC' ⊢
  generalize m.q.Qδ m.δ (m.q.emf m.Qf) = c at hC' ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at ha1 hC' hA' hw2 ⊢
  have hDk : m.q.D = -(m.q.M * m.q.ωq * k) := by linarith
  have hk : k ≠ 0 := by
    intro h; rw [h, mul_zero, neg_zero] at hDk; linarith
  have ha : a = m.q.M * w ^ 2 - m.q.D * m.q.ωq * k := by
    rw [hw2]; field_simp; ring
  have hc : c ≠ 0 := by
    intro h
    rw [h, mul_zero, sub_zero] at hC'
    have ha0 : a = 0 := (mul_eq_zero.mp hC').resolve_left hk
    rw [ha0, hDk] at ha1
    nlinarith [sq_nonneg k, mul_pos hM (mul_pos hω hω)]
  refine ⟨hw, hk, hc, ?_, ?_, ?_⟩
  · simp only [hopfL]; linarith
  · rw [hopfA, ha]
  · rw [hopfB, eq_div_iff (mul_ne_zero hω.ne' hc)]
    have hbc : b * c = k * a := by linarith
    rw [ha, hDk] at hbc
    rw [hDk]
    linear_combination m.q.ωq * hbc

/-- **The coefficients at a zero–Hopf point** (`E* ≠ 0`, `w = Model.hopfFreq`,
`μ = n_q/E*`, `𝔉 = foldQuad a_δ c k μ`): `a = ω_q 𝔉/(2 M c w²)`,
`b = ω_q (ω_q² 𝔉 + w² (a_δ² + c²))/(2 M c w²)`, `c_ZH = −ω_q (𝔉 + M w² c² μ (1 − a_δ μ))/(2 M c w²)`
for the null pair `(foldQ, foldP)` and the critical pair `(hopfQ, hopfP)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.zeroHopf_coeffs (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) = 0)
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0) :
    foldCoeff m.field 0 (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
        (foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))) =
        m.q.ωq * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) /
          (2 * m.q.M * m.q.Qδ m.δ (m.q.emf m.Qf) * m.hopfFreq ^ 2) ∧
      zhB m.field (foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)))
          (hopfQ m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) =
        m.q.ωq * (m.q.ωq ^ 2 * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) + m.hopfFreq ^ 2 *
          (m.q.Pδ m.δ (m.q.emf m.Qf) ^ 2 + m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2)) /
          (2 * m.q.M * m.q.Qδ m.δ (m.q.emf m.Qf) * m.hopfFreq ^ 2) ∧
      zhC m.field (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
          (hopfQ m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
          (hopfP m.q.M m.q.D m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf))
            (m.q.Qδ m.δ (m.q.emf m.Qf))) =
        -(m.q.ωq * (foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) + m.q.M * m.hopfFreq ^ 2 *
          m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2 * (m.q.nq / m.q.emf m.Qf) *
          (1 - m.q.Pδ m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf))) /
          (2 * m.q.M * m.q.Qδ m.δ (m.q.emf m.Qf) * m.hopfFreq ^ 2)) := by
  obtain ⟨hw, hk, hc, hL, ha, hb⟩ := m.zeroHopf_relations hM hD hω hC hA ha1
  have hC' : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) =
      m.q.gain m.δ (m.q.emf m.Qf) *
        (m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
    linear_combination (-1 : ℝ) * hC'
  have hw2 : m.hopfFreq ^ 2 = (m.q.Pδ m.δ (m.q.emf m.Qf) +
      m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) / m.q.M :=
    Real.sq_sqrt (div_pos ha1 hM).le
  have hfold := m.foldCoeff_fold hM.ne' hC hE (by rw [hN]; exact mul_ne_zero hk ha1.ne')
  rw [hN] at hfold
  have h2 : 2 * m.q.Qδ m.δ (m.q.emf m.Qf) * (m.q.Pδ m.δ (m.q.emf m.Qf) +
      m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) *
      foldCoeff m.field 0 (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
        (foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))) =
      m.q.ωq * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) :=
    mul_left_cancel₀ hk (by linear_combination hfold)
  have hden : 2 * m.q.M * m.q.Qδ m.δ (m.q.emf m.Qf) * m.hopfFreq ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hM.ne') hc) (pow_ne_zero 2 hw.ne')
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff hden, hw2]
    field_simp
    linear_combination h2
  · rw [Dynamics.CenterManifold.zhB_eq_pairing, m.bilinC_field hE]
    have key := zeroHopf_b (μ := m.q.nq / m.q.emf m.Qf) hM hω hw hc hk hL
    rw [← ha, ← hb] at key
    exact key
  · rw [Dynamics.CenterManifold.zhC_eq_pairing, m.bilinC_field hE]
    have key := zeroHopf_c (μ := m.q.nq / m.q.emf m.Qf) hM hω hw hc hL
    rw [← ha, ← hb] at key
    exact key

/-- **The decided zero–Hopf points**: with the closed forms of `Model.zeroHopf_coeffs`
(`X = ω_q/(2 M c w²) ≠ 0`: `a = X 𝔉`, `b = X (ω_q² 𝔉 + w²(a_δ² + c²))`,
`c_ZH = −X (𝔉 + Y)`, `Y = M w² c² μ (1 − a_δ μ)`), `ab = X² 𝔉 (ω_q² 𝔉 + w²(a_δ² + c²))`,
`a(a − c_ZH) = X² 𝔉 (2𝔉 + Y)` and, at `𝔉 = 0`, `b c_ZH = −X² w² (a_δ² + c²) Y`: each of the three
conditions gives `ZeroHopfDecided a b c_ZH`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.zeroHopfDecided_zeroHopf (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) = 0)
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0)
    (hdec : 0 < foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) *
        (m.q.ωq ^ 2 * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) + m.hopfFreq ^ 2 *
          (m.q.Pδ m.δ (m.q.emf m.Qf) ^ 2 + m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2)) ∨
      0 < foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) *
        (2 * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) + m.q.M * m.hopfFreq ^ 2 *
          m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2 * (m.q.nq / m.q.emf m.Qf) *
          (1 - m.q.Pδ m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf))) ∨
      (foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0 ∧
        m.q.nq / m.q.emf m.Qf * (1 - m.q.Pδ m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf)) < 0)) :
    ZeroHopfDecided
      (foldCoeff m.field 0 (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
        (foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))))
      (zhB m.field (foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
          (m.q.Qδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)))
          (hopfQ m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))))
      (zhC m.field (foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
          (hopfQ m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf)))
          (hopfP m.q.M m.q.D m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf))
            (m.q.Qδ m.δ (m.q.emf m.Qf)))) := by
  obtain ⟨hw, -, hc, -, -, -⟩ := m.zeroHopf_relations hM hD hω hC hA ha1
  obtain ⟨ea, eb, ec⟩ := m.zeroHopf_coeffs hM hD hω hC hA ha1 hE
  rw [ea, eb, ec]
  generalize foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
    (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = F at hdec ⊢
  generalize m.q.Pδ m.δ (m.q.emf m.Qf) = a at hdec ⊢
  generalize m.q.Qδ m.δ (m.q.emf m.Qf) = c at hc hdec ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at hdec ⊢
  generalize m.hopfFreq = w at hw hdec ⊢
  have hX : m.q.ωq / (2 * m.q.M * c * w ^ 2) ≠ 0 :=
    div_ne_zero hω.ne' (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hM.ne') hc)
      (pow_ne_zero 2 hw.ne'))
  have hX2 : 0 < (m.q.ωq / (2 * m.q.M * c * w ^ 2)) ^ 2 := by positivity
  set X := m.q.ωq / (2 * m.q.M * c * w ^ 2) with hXdef
  have e1 : m.q.ωq * F / (2 * m.q.M * c * w ^ 2) = X * F := by rw [hXdef]; ring
  have e2 : m.q.ωq * (m.q.ωq ^ 2 * F + w ^ 2 * (a ^ 2 + c ^ 2)) / (2 * m.q.M * c * w ^ 2) =
      X * (m.q.ωq ^ 2 * F + w ^ 2 * (a ^ 2 + c ^ 2)) := by rw [hXdef]; ring
  have e3 : -(m.q.ωq * (F + m.q.M * w ^ 2 * c ^ 2 * μ * (1 - a * μ)) / (2 * m.q.M * c * w ^ 2))
      = -(X * (F + m.q.M * w ^ 2 * c ^ 2 * μ * (1 - a * μ))) := by rw [hXdef]; ring
  rw [e1, e2, e3]
  rcases hdec with h | h | ⟨h0, h⟩
  · refine Or.inl ?_
    have : X * F * (X * (m.q.ωq ^ 2 * F + w ^ 2 * (a ^ 2 + c ^ 2))) =
        X ^ 2 * (F * (m.q.ωq ^ 2 * F + w ^ 2 * (a ^ 2 + c ^ 2))) := by ring
    rw [this]; positivity
  · refine Or.inr (Or.inl ?_)
    have : X * F * (X * F - -(X * (F + m.q.M * w ^ 2 * c ^ 2 * μ * (1 - a * μ)))) =
        X ^ 2 * (F * (2 * F + m.q.M * w ^ 2 * c ^ 2 * μ * (1 - a * μ))) := by ring
    rw [this]; positivity
  · refine Or.inr (Or.inr ⟨by rw [h0, mul_zero], ?_⟩)
    rw [h0]
    have : X * (m.q.ωq ^ 2 * 0 + w ^ 2 * (a ^ 2 + c ^ 2)) *
        -(X * (0 + m.q.M * w ^ 2 * c ^ 2 * μ * (1 - a * μ))) =
        X ^ 2 * (m.q.M * w ^ 4 * c ^ 2 * (a ^ 2 + c ^ 2)) * (-(μ * (1 - a * μ))) := by ring
    rw [this]
    have hc2 : 0 < c ^ 2 := by positivity
    have : 0 < -(μ * (1 - a * μ)) := by linarith
    positivity

/-- **Decided zero–Hopf points are unstable**
(`Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly`): for `M, D, ω_q > 0`, an
equilibrium at a fold (`C = 0`) with `A = 0` (`det(sI − J) = s (s² + w²)`, `w² = a₁ > 0`),
`E* ≠ 0` and decided coefficients (`QVDroop.Model.zeroHopfDecided_zeroHopf`) is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_zeroHopf (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) = 0)
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0)
    (hdec : 0 < foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) *
        (m.q.ωq ^ 2 * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) + m.hopfFreq ^ 2 *
          (m.q.Pδ m.δ (m.q.emf m.Qf) ^ 2 + m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2)) ∨
      0 < foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) *
        (2 * foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) + m.q.M * m.hopfFreq ^ 2 *
          m.q.Qδ m.δ (m.q.emf m.Qf) ^ 2 * (m.q.nq / m.q.emf m.Qf) *
          (1 - m.q.Pδ m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf))) ∨
      (foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) = 0 ∧
        m.q.nq / m.q.emf m.Qf * (1 - m.q.Pδ m.δ (m.q.emf m.Qf) * (m.q.nq / m.q.emf m.Qf)) < 0)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  obtain ⟨hw, hk, hc, hL, ha, hb⟩ := m.zeroHopf_relations hM hD hω hC hA ha1
  have hC' : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Pδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) = 0 := hC
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    have e : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
        m.q.nq * m.q.PE m.δ (m.q.emf m.Qf) * m.q.Qδ m.δ (m.q.emf m.Qf) =
        m.q.gain m.δ (m.q.emf m.Qf) *
          (m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
      linear_combination (-1 : ℝ) * hC'
    rw [e]
    exact mul_ne_zero hk ha1.ne'
  have heq0 : m.field 0 = 0 := by simpa [Model.field] using heq
  have hJ : jacobianC m.field 0 = Linear.complexify (hopfJ m.q.M m.q.D m.q.ωq m.hopfFreq
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))) := by
    rw [m.jacobianC_field, Model.jacobian, jacobian_eq_droopJacobian, ha, hb]
  have hcp := zeroHopf_isCriticalPair hM hω hw hc hL heq0 hJ
  have hw2 : m.hopfFreq ^ 2 = (m.q.Pδ m.δ (m.q.emf m.Qf) +
      m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) / m.q.M :=
    Real.sq_sqrt (div_pos ha1 hM).le
  have hchar : (jacobianC m.field 0).charpoly =
      Polynomial.X * (Polynomial.X ^ 2 + Polynomial.C ((m.hopfFreq : ℂ) ^ 2)) * 1 := by
    rw [m.charpoly_fold hM.ne' hC, hA, zero_div, ← hw2]
    simp
  exact Dynamics.CenterManifold.unstable_of_zeroHopf_of_charpoly (m.contDiff_field (k := 2))
    heq0 (m.isNullPair_fold hM.ne' hC hN)
    (Dynamics.CenterManifold.IsCriticalPair.isCritical hcp rfl) hchar (fun s hs => by simp at hs)
    (m.zeroHopfDecided_zeroHopf hM hD hω hC hA ha1 hE hdec)

/-- **Every zero–Hopf point with `𝔉 > 0` is unstable** (the first decided regime, `ab > 0`:
`𝔉 > 0` makes `ω_q² 𝔉 + w² (a_δ² + c²) > 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_zeroHopf_of_foldQuad_pos (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hA : m.q.routhTrace m.δ (m.q.emf m.Qf) = 0)
    (ha1 : 0 < m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hE : m.q.emf m.Qf ≠ 0)
    (hF : 0 < foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_zeroHopf m hM hD hω heq hC hA ha1 hE (Or.inl (by positivity))

end QVDroop
end powerlib.GFM
