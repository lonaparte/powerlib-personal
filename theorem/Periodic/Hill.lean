import theorem.Linear.Transfer
import Mathlib.Analysis.Fourier.AddCircle

/-! # LTI checks of the harmonic-linearization framework

Three exact statements about **linear time-invariant** systems that the harmonic-linearization
note uses as sanity checks, and the gauge symmetry of general (time-periodic) Hill matrices.

Scope.
* Static linear algebra and complex-signal calculus; no model family.
* The LTI system of the mirror-coupling check is given by its state-space matrices `A B C D`
  (state index `ι`, `p` inputs and outputs), with the characteristic matrix and transfer function
  of `powerlib.Linear` (`Linear.characteristicMatrix`, `Linear.transferOf`).
* The passage from the converter model to the periodic Jacobian `J(t)` is not formalized.

Source: work-sync theory/T-harmonic-linearization.md §1.2 (sequence injection
`δv₊^{αβ} = V_p e^{jω_p t}`, `δv₋^{αβ} = V_n e^{−jω_p t}`), §1.3 ("纯 LTI 系统 `Y₁₂ = Y₂₁ = 0`";
the premise `ω_p ≠ ω_s` is added: at `ω_p = ω_s` the mirror pair collapses to one frequency),
§1.5–1.6 (Hill matrix, LTI check `eig(𝓗) = {λ_i(A₀) − jkω_s}`);
projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md §11
("半周期对称性（恒等式）…Hill 层对应规范 `φ_m → (−1)^m φ_m`（一阶块变号、二阶块不变、三阶块变号）").

Results.
* Truncated Hill matrix of an LTI system. For a constant state matrix `A₀` the lifted Hill
  matrix `𝓗_K = 𝓐_K − 𝓝_K` (harmonics `h = −K, …, K`, `𝓝 = diag(jhω_s I)`) is block diagonal
  with blocks `A₀ − jhω_s I` (`hillLTI`). Its characteristic determinant factorizes
  (`det_hillLTI`), so `s` is an eigenvalue of `𝓗_K` iff `s + jhω_s` is an eigenvalue of `A₀` for
  some `|h| ≤ K`, i.e. `eig(𝓗_K) = {λ − jhω_s}` (`hillLTI_root_iff`).
* Sequence injection in the αβ frame (amplitude-invariant Clarke, `Transform.clarke`): a
  negative-sequence three-phase signal `V cos(θ + φ − 2πk/3·(−1))` maps to the αβ vector
  `V(cos(θ + φ), −sin(θ + φ))`, i.e. `V e^{−j(θ+φ)}` (`Transform.clarke_mulVec_negSeq`, with
  `Transform.negSeq` and `Transform.toComplex_clarke_negSeq`, in `theorem/Transform/Park.lean`).
  The positive-sequence counterpart `V e^{j(θ+φ)}` is `Transform.clarke_mulVec_balanced`.
* No mirror coupling for LTI. For a (real-coefficient) LTI model driven by complex tones, a
  tone at `jω` produces exactly `G(jω) U e^{jωt}` (`tone_solves`), tones superpose, and the
  coefficients of distinct exponentials are unique (`exp_coeff_unique`). Hence for the mirror
  pair `ω_p`, `ω_c = 2ω_s − ω_p` with `ω_p ≠ ω_s` (so `ω_c ≠ ω_p`), the steady-state output
  coefficient at `ω_p` is `G(jω_p) V(ω_p)` and at `ω_c` is `G(jω_c) V(ω_c)`
  (`mirror_coupling_zero`): the off-diagonal entries `Y₁₂`, `Y₂₁` vanish.
* Hill gauge symmetry `φ_m ↦ (−1)^m φ_m`. For a general truncated Hill matrix
  `𝓗[J]` (`hillMatrix`: block `(m, m')` is `J_{m − m'} − δ_{mm'} j(m + ν)ω I`, `ν = 1/2` for the
  half-integer ansatz `w = ∑ φ_m e^{j(m + 1/2)ω_p t}`), conjugation by the involutive gauge
  `G = diag((−1)^m I)` (`hillGauge`, `hillGauge_mul_self`) multiplies the band `Δm = h` by `(−1)^h`
  and leaves the diagonal blocks unchanged (`hillGauge_conj`). Hence coefficient families with
  `J'_h = (−1)^h J_h` give similar Hill matrices (`hillMatrix_gauge_similar`) with the same
  characteristic polynomial, determinant `det(sI − 𝓗)`, spectrum and gauge-mapped eigenvectors
  (`hillMatrix_charpoly_eq`, `hillMatrix_det_eq`, `hillMatrix_spectrum_eq`,
  `hillMatrix_gauge_eigenvector`); `hillLTI` is the case `J_0 = A₀`, `ν = 0`
  (`hillLTI_eq_hillMatrix`). For the third-order truncated Hill matrix of the source
  (`hillCoeff3`: `J₀ = A₀ + δ̂₁²Q₀`, `J₁ = (δ̂₁/2)P + δ̂₁³P₃`, `J₂ = δ̂₁²Q₂`, `J₃ = δ̂₁³P₃₃`,
  `J_{−h} = conj J_h`) `δ̂₁ ↦ −δ̂₁` flips the first- and third-order bands and keeps the
  second-order band (`hillBand3_neg`, `hillCoeff3_neg`), so the Hill matrices at `±δ̂₁` are
  gauge-similar and their spectra coincide (`hill3_neg_similar`). For the exact Hill matrix built
  from Fourier coefficients on `ℝ/Tℤ`, a half-period shift multiplies the `h`-th coefficient by
  `(−1)^h` (`fourierCoeff_add_half`, `fourierCoeffMatrix_half_shift`), so `J'(t) = J(t + T/2)`
  (what the half-period symmetry `u(t + T/2) = −u(t)` turns `δ̂₁ ↦ −δ̂₁` into) gives
  gauge-similar exact Hill matrices (`exactHill_half_shift`).
-/

noncomputable section
namespace powerlib.Periodic

open Matrix Complex

/-! ## 1. Truncated Hill matrix of an LTI system -/

section Hill

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Harmonic index `h = k − K ∈ {−K, …, K}` of block `k : Fin (2K + 1)`. -/
def harmonicIndex (K : ℕ) (k : Fin (2 * K + 1)) : ℤ := (k : ℤ) - K

/-- Truncated Hill matrix of the LTI system `A(t) = A₀`: block `h` is `A₀ − jhω_s I`. -/
def hillLTI (A : Matrix X X ℝ) (ωs : ℝ) (K : ℕ) :
    Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ :=
  Matrix.blockDiagonal fun k =>
    A.map (algebraMap ℝ ℂ) - (((harmonicIndex K k : ℂ) * ωs * I)) • (1 : Matrix X X ℂ)

/-- `det(sI − 𝓗_K) = ∏_h det((s + jhω_s) I − A₀)`. -/
@[powerlib_foundation] theorem det_hillLTI (A : Matrix X X ℝ) (ωs : ℝ) (K : ℕ) (s : ℂ) :
    (s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) - hillLTI A ωs K).det =
      ∏ k, (Linear.characteristicMatrix A (s + (harmonicIndex K k : ℂ) * ωs * I)).det := by
  have h : s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) - hillLTI A ωs K =
      Matrix.blockDiagonal fun k =>
        Linear.characteristicMatrix A (s + (harmonicIndex K k : ℂ) * ωs * I) := by
    rw [hillLTI, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_smul,
      ← Matrix.blockDiagonal_sub]
    congr 1
    funext k
    simp only [Linear.characteristicMatrix, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, add_smul]
    abel
  rw [h, Matrix.det_blockDiagonal]

/-- `s` is a characteristic root of `𝓗_K` iff `s + jhω_s` is an eigenvalue of `A₀` for some
`|h| ≤ K`: `eig(𝓗_K) = {λ_i(A₀) − jhω_s}`. -/
@[powerlib_foundation] theorem hillLTI_root_iff (A : Matrix X X ℝ) (ωs : ℝ) (K : ℕ) (s : ℂ) :
    (s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) - hillLTI A ωs K).det = 0 ↔
      ∃ k : Fin (2 * K + 1),
        (Linear.characteristicMatrix A (s + (harmonicIndex K k : ℂ) * ωs * I)).det = 0 := by
  rw [det_hillLTI, Finset.prod_eq_zero_iff]
  simp

end Hill

/-! ## 3. No mirror coupling for LTI systems -/

section Mirror

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
variable (A : Matrix ι ι ℝ) (B : Matrix ι (Fin p) ℝ) (C : Matrix (Fin p) ι ℝ)
  (D : Matrix (Fin p) (Fin p) ℝ)

/-- Coefficients of two distinct exponentials are unique. -/
@[powerlib_foundation] theorem exp_coeff_unique {ω₁ ω₂ : ℝ} (hne : ω₁ ≠ ω₂) {a b : ℂ}
    (h : ∀ t : ℝ, a * Complex.exp (ω₁ * t * I) + b * Complex.exp (ω₂ * t * I) = 0) :
    a = 0 ∧ b = 0 := by
  have hd : ∀ ω : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (ω * t * I)) (ω * I) 0 := by
    intro ω
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 0 := hasDerivAt_id (0 : ℝ) |>.ofReal_comp
    have h2 := ((h1.const_mul (ω : ℂ)).mul_const I).cexp
    simpa using h2
  have hD : HasDerivAt (fun t : ℝ => a * Complex.exp (ω₁ * t * I) + b * Complex.exp (ω₂ * t * I))
      (a * (ω₁ * I) + b * (ω₂ * I)) 0 := ((hd ω₁).const_mul a).add ((hd ω₂).const_mul b)
  have hfun : (fun t : ℝ => a * Complex.exp (ω₁ * t * I) + b * Complex.exp (ω₂ * t * I)) =
      fun _ => 0 := funext h
  rw [hfun] at hD
  have hz := hD.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  have h0 := h 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h0
  have hb : b = -a := by linear_combination h0
  subst hb
  have hω : ((ω₁ : ℂ) - ω₂) * a * I = 0 := by linear_combination hz
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hω' : ((ω₁ : ℂ) - ω₂) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hne
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hω with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hω'
      · exact h
    · exact absurd h hI
  exact ⟨ha, by rw [ha, neg_zero]⟩

/-- The output `y = C x + D u` of a complex-signal trajectory. -/
def toneOutput (u : ℝ → Fin p → ℂ) (x : ℝ → ι → ℂ) (t : ℝ) : Fin p → ℂ :=
  Linear.complexify C *ᵥ x t + Linear.complexify D *ᵥ u t

/-- Steady state of a single tone `U e^{jωt}`: `x = (jωI − A)⁻¹ B U e^{jωt}`. -/
def toneState (ω : ℝ) (U : Fin p → ℂ) (t : ℝ) : ι → ℂ :=
  Complex.exp (ω * t * I) • ((Linear.characteristicMatrix A (ω * I))⁻¹ *ᵥ
    (Linear.complexify B *ᵥ U))

/-- The tone steady state is a complex-signal trajectory of the LTI model under the complex
input `u(t) = U e^{jωt}`: `ẋ = A x + B u` at every instant. -/
@[powerlib_foundation] theorem tone_solves {ω : ℝ}
    (h : (Linear.characteristicMatrix A (ω * I)).det ≠ 0) (U : Fin p → ℂ) :
    ∀ t, HasDerivAt (toneState A B ω U)
      (Linear.complexify A *ᵥ toneState A B ω U t +
        Linear.complexify B *ᵥ (Complex.exp (ω * t * I) • U)) t := by
  intro t
  set R := Linear.characteristicMatrix A (ω * I)
  set w := R⁻¹ *ᵥ (Linear.complexify B *ᵥ U)
  have hRw : R *ᵥ w = Linear.complexify B *ᵥ U := by
    simp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h),
      Matrix.one_mulVec]
  have hAw : ((ω : ℂ) * I) • w = Linear.complexify A *ᵥ w + Linear.complexify B *ᵥ U := by
    rw [← hRw]
    simp only [R, Linear.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Linear.complexify]
    abel
  have he : HasDerivAt (fun t : ℝ => Complex.exp (ω * t * I)) (ω * I * Complex.exp (ω * t * I))
      t := by
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 t := hasDerivAt_id t |>.ofReal_comp
    have h2 := ((h1.const_mul (ω : ℂ)).mul_const I).cexp
    convert h2 using 1; ring
  have hx := he.smul_const w
  show HasDerivAt (fun y : ℝ => Complex.exp (ω * y * I) • w)
    (Linear.complexify A *ᵥ (Complex.exp (ω * t * I) • w) +
      Linear.complexify B *ᵥ (Complex.exp (ω * t * I) • U)) t
  convert hx using 1
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, ← hAw, smul_smul]
  congr 1; ring

/-- The output of a single tone is `G(jω) U e^{jωt}`. -/
@[powerlib_foundation] theorem toneOutput_eq (ω : ℝ) (U : Fin p → ℂ) (t : ℝ) :
    toneOutput C D (fun t => Complex.exp (ω * t * I) • U) (toneState A B ω U) t =
      Complex.exp (ω * t * I) • (Linear.transferOf A B C D (ω * I) *ᵥ U) := by
  simp only [toneOutput, toneState, Linear.transferOf, Matrix.mulVec_smul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, smul_add]

/-- LTI systems do not couple the mirror frequency: if the two-tone steady-state output
(`ω_p`, `ω_c = 2ω_s − ω_p`, `ω_p ≠ ω_s`) is written as `Y₁ e^{jω_p t} + Y₂ e^{jω_c t}`, then
`Y₁ = G(jω_p) V₁` and `Y₂ = G(jω_c) V₂`: the off-diagonal entries `Y₁₂ = Y₂₁ = 0`. -/
@[powerlib_foundation] theorem mirror_coupling_zero {ωp ωs : ℝ}
    (hne : ωp ≠ ωs) (V₁ V₂ Y₁ Y₂ : Fin p → ℂ)
    (hy : ∀ t, toneOutput C D (fun t => Complex.exp (ωp * t * I) • V₁) (toneState A B ωp V₁) t +
        toneOutput C D (fun t => Complex.exp ((2 * ωs - ωp : ℝ) * t * I) • V₂)
          (toneState A B (2 * ωs - ωp) V₂) t =
      Complex.exp (ωp * t * I) • Y₁ + Complex.exp ((2 * ωs - ωp : ℝ) * t * I) • Y₂) :
    Y₁ = Linear.transferOf A B C D (ωp * I) *ᵥ V₁ ∧
      Y₂ = Linear.transferOf A B C D (((2 * ωs - ωp : ℝ) : ℂ) * I) *ᵥ V₂ := by
  have hω : ωp ≠ 2 * ωs - ωp := by
    intro h; apply hne; linarith
  have hk : ∀ k, (Y₁ k - (Linear.transferOf A B C D (ωp * I) *ᵥ V₁) k = 0) ∧
      (Y₂ k - (Linear.transferOf A B C D (((2 * ωs - ωp : ℝ) : ℂ) * I) *ᵥ V₂) k = 0) := by
    intro k
    apply exp_coeff_unique hω
    intro t
    have := congrFun (hy t) k
    rw [toneOutput_eq, toneOutput_eq] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination -this
  exact ⟨funext fun k => sub_eq_zero.mp (hk k).1, funext fun k => sub_eq_zero.mp (hk k).2⟩

end Mirror

/-! ## 4. The Hill gauge symmetry `φ_m ↦ (−1)^m φ_m` -/

section Gauge

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Truncated Hill matrix of a Fourier-coefficient family `J : ℤ → Matrix X X ℂ`
(`J(t) = ∑_h J_h e^{jhωt}`), harmonics `m = −K, …, K`, frequency offset `ν` (`ν = 1/2` for the
half-integer ansatz `w = ∑_m φ_m e^{j(m + 1/2)ωt}`): block `(m, m')` is
`J_{m − m'} − δ_{mm'} j(m + ν)ω I`. -/
def hillMatrix (J : ℤ → Matrix X X ℂ) (ν ω : ℝ) (K : ℕ) :
    Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ :=
  Matrix.of (fun p q => J (harmonicIndex K p.2 - harmonicIndex K q.2) p.1 q.1) -
    Matrix.blockDiagonal fun k => (((harmonicIndex K k : ℂ) + ν) * ω * I) • (1 : Matrix X X ℂ)

/-- The gauge `φ_m ↦ (−1)^m φ_m`, as the diagonal matrix `diag((−1)^m I)`. -/
def hillGauge (K : ℕ) : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ :=
  Matrix.diagonal fun p => ((harmonicIndex K p.2).negOnePow : ℂ)

@[powerlib_foundation] private theorem negOnePow_mul_self (a : ℤ) :
    (a.negOnePow : ℂ) * (a.negOnePow : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

@[powerlib_foundation] private theorem negOnePow_mul_negOnePow (a b : ℤ) :
    (a.negOnePow : ℂ) * (b.negOnePow : ℂ) = ((a - b).negOnePow : ℂ) := by
  rw [Int.negOnePow_sub, Units.val_mul, Int.cast_mul]

/-- The gauge is an involution. -/
@[powerlib_foundation] theorem hillGauge_mul_self (K : ℕ) :
    hillGauge (X := X) K * hillGauge K = 1 := by
  rw [hillGauge, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext p
  exact negOnePow_mul_self _

/-- The gauge as a unit of the matrix ring (its own inverse). -/
def hillGaugeUnit (K : ℕ) : (Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ)ˣ :=
  ⟨hillGauge K, hillGauge K, hillGauge_mul_self K, hillGauge_mul_self K⟩

/-- **Gauge covariance.** Conjugating the Hill matrix by `diag((−1)^m I)` multiplies the band
`Δm = h` by `(−1)^h`: `G 𝓗[J] G = 𝓗[(−1)^h J_h]`; the diagonal (`h = 0`) blocks, including
the frequency shift `−j(m + ν)ω I`, are unchanged. -/
@[powerlib_foundation] theorem hillGauge_conj (J : ℤ → Matrix X X ℂ) (ν ω : ℝ) (K : ℕ) :
    hillGauge K * hillMatrix J ν ω K * hillGauge K =
      hillMatrix (fun h => (h.negOnePow : ℂ) • J h) ν ω K := by
  ext ⟨i, k⟩ ⟨i', k'⟩
  simp only [hillGauge, hillMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply,
    Matrix.of_apply, Matrix.blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hk : k = k'
  · subst hk
    simp only [ite_true, sub_self, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul]
    have h1 := negOnePow_mul_self (harmonicIndex K k)
    linear_combination (J 0 i i' - (((harmonicIndex K k : ℂ) + ν) * ω * I) *
      (1 : Matrix X X ℂ) i i') * h1
  · simp only [hk, ite_false, sub_zero]
    rw [← negOnePow_mul_negOnePow]
    ring

/-- If the coefficient family has the parity `J'_h = (−1)^h J_h` (as produced by
`δ̂₁ ↦ −δ̂₁` under the half-period symmetry), the two Hill matrices are similar through the
gauge: `𝓗[J'] = G 𝓗[J] G⁻¹` with `G = G⁻¹`. -/
@[powerlib_foundation] theorem hillMatrix_gauge_similar {J J' : ℤ → Matrix X X ℂ}
    (hJ : ∀ h, J' h = (h.negOnePow : ℂ) • J h) (ν ω : ℝ) (K : ℕ) :
    hillMatrix J' ν ω K = hillGauge K * hillMatrix J ν ω K * hillGauge K := by
  have : J' = fun h => (h.negOnePow : ℂ) • J h := funext hJ
  subst this
  exact (hillGauge_conj J ν ω K).symm

@[powerlib_foundation] private theorem hillMatrix_units_conj {J J' : ℤ → Matrix X X ℂ}
    (hJ : ∀ h, J' h = (h.negOnePow : ℂ) • J h) (ν ω : ℝ) (K : ℕ) :
    hillMatrix J' ν ω K =
      (hillGaugeUnit (X := X) K).val * hillMatrix J ν ω K * (hillGaugeUnit (X := X) K)⁻¹.val :=
  hillMatrix_gauge_similar hJ ν ω K

/-- Spectral consequence: the gauge-related Hill matrices have the same characteristic
polynomial. -/
@[powerlib_foundation] theorem hillMatrix_charpoly_eq {J J' : ℤ → Matrix X X ℂ}
    (hJ : ∀ h, J' h = (h.negOnePow : ℂ) • J h) (ν ω : ℝ) (K : ℕ) :
    (hillMatrix J' ν ω K).charpoly = (hillMatrix J ν ω K).charpoly := by
  have hinv : (hillGauge (X := X) K)⁻¹ = hillGauge K :=
    Matrix.inv_eq_left_inv (hillGauge_mul_self K)
  calc (hillMatrix J' ν ω K).charpoly
      = ((hillGaugeUnit (X := X) K).val * hillMatrix J ν ω K *
          (hillGaugeUnit (X := X) K).val⁻¹).charpoly := by
        rw [hillMatrix_gauge_similar hJ, show (hillGaugeUnit (X := X) K).val = hillGauge K from rfl,
          hinv]
    _ = (hillMatrix J ν ω K).charpoly := Matrix.charpoly_units_conj _ _

/-- Spectral consequence: the same spectrum (truncated Floquet exponents). -/
@[powerlib_foundation] theorem hillMatrix_spectrum_eq {J J' : ℤ → Matrix X X ℂ}
    (hJ : ∀ h, J' h = (h.negOnePow : ℂ) • J h) (ν ω : ℝ) (K : ℕ) :
    spectrum ℂ (hillMatrix J' ν ω K) = spectrum ℂ (hillMatrix J ν ω K) := by
  rw [hillMatrix_units_conj hJ, spectrum.units_conjugate]

/-- Spectral consequence, determinant form: `det(sI − 𝓗[J']) = det(sI − 𝓗[J])` for every `s`;
an eigenvector `φ` of `𝓗[J]` is mapped to the eigenvector `Gφ = ((−1)^m φ_m)` of `𝓗[J']`. -/
@[powerlib_foundation] theorem hillMatrix_det_eq {J J' : ℤ → Matrix X X ℂ}
    (hJ : ∀ h, J' h = (h.negOnePow : ℂ) • J h) (ν ω : ℝ) (K : ℕ) (s : ℂ) :
    (s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) - hillMatrix J' ν ω K).det =
      (s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) -
        hillMatrix J ν ω K).det := by
  have hG := hillGauge_mul_self (X := X) K
  have e : s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) - hillMatrix J' ν ω K =
      hillGauge K * (s • 1 - hillMatrix J ν ω K) * hillGauge K := by
    rw [hillMatrix_gauge_similar hJ, mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc,
      hG]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hG,
    Matrix.det_one, one_mul]

/-- An eigenvector `φ` of `𝓗[J]` for the exponent `s` gives the eigenvector `Gφ` of `𝓗[J']`. -/
@[powerlib_foundation] theorem hillMatrix_gauge_eigenvector {J J' : ℤ → Matrix X X ℂ}
    (hJ : ∀ h, J' h = (h.negOnePow : ℂ) • J h) (ν ω : ℝ) (K : ℕ) {s : ℂ}
    {φ : X × Fin (2 * K + 1) → ℂ} (hφ : hillMatrix J ν ω K *ᵥ φ = s • φ) :
    hillMatrix J' ν ω K *ᵥ (hillGauge K *ᵥ φ) = s • (hillGauge K *ᵥ φ) := by
  rw [hillMatrix_gauge_similar hJ, Matrix.mulVec_mulVec, Matrix.mul_assoc, hillGauge_mul_self,
    Matrix.mul_one, ← Matrix.mulVec_mulVec, hφ, Matrix.mulVec_smul]

omit [Fintype X] in
/-- The LTI Hill matrix is the case `J_0 = A₀`, `J_h = 0` (`h ≠ 0`), `ν = 0`. -/
@[powerlib_foundation] theorem hillLTI_eq_hillMatrix (A : Matrix X X ℝ) (ωs : ℝ) (K : ℕ) :
    hillLTI A ωs K =
      hillMatrix (fun h => if h = 0 then A.map (algebraMap ℝ ℂ) else 0) 0 ωs K := by
  ext ⟨i, k⟩ ⟨i', k'⟩
  simp only [hillLTI, hillMatrix, Matrix.blockDiagonal_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_zero, add_zero]
  by_cases hk : k = k'
  · subst hk; simp
  · have : harmonicIndex K k - harmonicIndex K k' ≠ 0 := by
      simp only [harmonicIndex, ne_eq, sub_eq_zero, sub_left_inj, Nat.cast_inj]
      exact fun h => hk (Fin.ext h)
    simp [hk, this]

/-! ### The truncated third-order Hill matrix of the source (§11) -/

/-- Non-negative Fourier bands of the third-order truncated Jacobian in `δ = δ̂₁`:
`J₀ = A₀ + δ²Q₀`, `J₁ = (δ/2)P + δ³P₃`, `J₂ = δ²Q₂`, `J₃ = δ³P₃₃`, `J_h = 0` for `h ≥ 4`. -/
def hillBand3 (A₀ Q₀ P P₃ Q₂ P₃₃ : Matrix X X ℂ) (δ : ℝ) : ℕ → Matrix X X ℂ
  | 0 => A₀ + ((δ : ℂ) ^ 2) • Q₀
  | 1 => ((δ : ℂ) / 2) • P + ((δ : ℂ) ^ 3) • P₃
  | 2 => ((δ : ℂ) ^ 2) • Q₂
  | 3 => ((δ : ℂ) ^ 3) • P₃₃
  | _ => 0

/-- Full coefficient family: `J_h` for `h ≥ 0`, `J_{−h} = conj J_h` (real `J(t)`). -/
def hillCoeff3 (A₀ Q₀ P P₃ Q₂ P₃₃ : Matrix X X ℂ) (δ : ℝ) (h : ℤ) : Matrix X X ℂ :=
  if 0 ≤ h then hillBand3 A₀ Q₀ P P₃ Q₂ P₃₃ δ h.toNat
  else (hillBand3 A₀ Q₀ P P₃ Q₂ P₃₃ δ (-h).toNat).map (starRingEnd ℂ)

omit [Fintype X] [DecidableEq X] in
/-- Band parity: under `δ ↦ −δ` the first-order band changes sign, the second-order band is
invariant, the third-order band changes sign: `J_h(−δ) = (−1)^h J_h(δ)`. -/
@[powerlib_foundation] theorem hillBand3_neg (A₀ Q₀ P P₃ Q₂ P₃₃ : Matrix X X ℂ) (δ : ℝ)
    (n : ℕ) :
    hillBand3 A₀ Q₀ P P₃ Q₂ P₃₃ (-δ) n = ((-1 : ℂ) ^ n) • hillBand3 A₀ Q₀ P P₃ Q₂ P₃₃ δ n := by
  match n with
  | 0 => simp [hillBand3]
  | 1 => ext i j; simp [hillBand3]; ring
  | 2 => simp [hillBand3]
  | 3 => ext i j; simp [hillBand3]; ring
  | n + 4 => simp [hillBand3]

omit [Fintype X] [DecidableEq X] in
@[powerlib_foundation] theorem hillCoeff3_neg (A₀ Q₀ P P₃ Q₂ P₃₃ : Matrix X X ℂ) (δ : ℝ)
    (h : ℤ) :
    hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ (-δ) h =
      (h.negOnePow : ℂ) • hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ δ h := by
  unfold hillCoeff3
  split_ifs with hh
  · rw [hillBand3_neg, Int.coe_negOnePow]
    congr 2
    omega
  · rw [hillBand3_neg, Int.coe_negOnePow]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_neg,
      map_one]
    congr 2
    omega

/-- **Half-period symmetry at the Hill level.** The third-order truncated Hill matrix at `−δ̂₁` is
similar to the one at `δ̂₁` through the gauge `φ_m ↦ (−1)^m φ_m`; hence its characteristic
polynomial and spectrum (the truncated Floquet exponents) are even in `δ̂₁`. -/
@[powerlib_foundation] theorem hill3_neg_similar (A₀ Q₀ P P₃ Q₂ P₃₃ : Matrix X X ℂ) (δ ν ω : ℝ)
    (K : ℕ) :
    hillMatrix (hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ (-δ)) ν ω K =
        hillGauge K * hillMatrix (hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ δ) ν ω K * hillGauge K ∧
      (hillMatrix (hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ (-δ)) ν ω K).charpoly =
        (hillMatrix (hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ δ) ν ω K).charpoly ∧
      spectrum ℂ (hillMatrix (hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ (-δ)) ν ω K) =
        spectrum ℂ (hillMatrix (hillCoeff3 A₀ Q₀ P P₃ Q₂ P₃₃ δ) ν ω K) := by
  have hJ := hillCoeff3_neg A₀ Q₀ P P₃ Q₂ P₃₃ δ
  exact ⟨hillMatrix_gauge_similar hJ ν ω K, hillMatrix_charpoly_eq hJ ν ω K,
    hillMatrix_spectrum_eq hJ ν ω K⟩

/-! ### Exact Hill: the half-period shift of the Fourier coefficients -/

open MeasureTheory AddCircle in
/-- A half-period shift on the circle `ℝ/Tℤ` multiplies the `n`-th Fourier coefficient by
`(−1)^n`: `(f(· + T/2))^_n = (−1)^n f^_n`. -/
@[powerlib_foundation] theorem fourierCoeff_add_half {T : ℝ} [hT : Fact (0 < T)]
    (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun t => f (t + ((T / 2 : ℝ) : AddCircle T))) n =
      (n.negOnePow : ℂ) * fourierCoeff f n := by
  set c : AddCircle T := ((T / 2 : ℝ) : AddCircle T)
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.out.ne'
  have hc : fourier n c = (n.negOnePow : ℂ) := by
    rw [fourier_coe_apply, Int.cast_negOnePow, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    field_simp
  have hadd : ∀ t : AddCircle T, fourier (-n) (t + c) = fourier (-n) t * fourier (-n) c := by
    intro t
    simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
  have hinv : fourier n c * fourier (-n) c = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  have key : ∀ t : AddCircle T, fourier (-n) t • f (t + c) =
      fourier n c * (fourier (-n) (t + c) • f (t + c)) := by
    intro t
    rw [hadd, smul_eq_mul, smul_eq_mul]
    linear_combination (-(fourier (-n) t * f (t + c))) * hinv
  unfold fourierCoeff
  simp_rw [key]
  rw [integral_const_mul, integral_add_right_eq_self (fun t => fourier (-n) t • f t) c, hc]

/-- Fourier-coefficient matrices of a matrix function on the circle. -/
def fourierCoeffMatrix {T : ℝ} [Fact (0 < T)] (J : AddCircle T → Matrix X X ℂ) (h : ℤ) :
    Matrix X X ℂ :=
  Matrix.of fun i j => fourierCoeff (fun t => J t i j) h

omit [Fintype X] [DecidableEq X] in
/-- If `J'(t) = J(t + T/2)` (the half-period symmetry `u(t + T/2) = −u(t)` turns `δ̂₁ ↦ −δ̂₁`
into this shift), then `J'_h = (−1)^h J_h`. -/
@[powerlib_foundation] theorem fourierCoeffMatrix_half_shift {T : ℝ} [Fact (0 < T)]
    {J J' : AddCircle T → Matrix X X ℂ} (hshift : ∀ t, J' t = J (t + ((T / 2 : ℝ) : AddCircle T)))
    (h : ℤ) : fourierCoeffMatrix J' h = (h.negOnePow : ℂ) • fourierCoeffMatrix J h := by
  ext i j
  simp only [fourierCoeffMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hshift]
  exact fourierCoeff_add_half (fun t => J t i j) h

/-- **Exact Hill matrices under the half-period shift.** If `J'(t) = J(t + T/2)`, the exact
(Fourier-coefficient) Hill matrices are gauge-similar, so their characteristic polynomials and
spectra coincide. -/
@[powerlib_foundation] theorem exactHill_half_shift {T : ℝ} [Fact (0 < T)]
    {J J' : AddCircle T → Matrix X X ℂ} (hshift : ∀ t, J' t = J (t + ((T / 2 : ℝ) : AddCircle T)))
    (ν ω : ℝ) (K : ℕ) :
    hillMatrix (fourierCoeffMatrix J') ν ω K =
        hillGauge K * hillMatrix (fourierCoeffMatrix J) ν ω K * hillGauge K ∧
      (hillMatrix (fourierCoeffMatrix J') ν ω K).charpoly =
        (hillMatrix (fourierCoeffMatrix J) ν ω K).charpoly ∧
      spectrum ℂ (hillMatrix (fourierCoeffMatrix J') ν ω K) =
        spectrum ℂ (hillMatrix (fourierCoeffMatrix J) ν ω K) := by
  have hJ := fourierCoeffMatrix_half_shift hshift
  exact ⟨hillMatrix_gauge_similar hJ ν ω K, hillMatrix_charpoly_eq hJ ν ω K,
    hillMatrix_spectrum_eq hJ ν ω K⟩

end Gauge

end powerlib.Periodic
