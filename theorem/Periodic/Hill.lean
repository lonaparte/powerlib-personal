import theorem.LTI
import theorem.Transform.Park

/-! # LTI checks of the harmonic-linearization framework

Foundation layer: three exact statements about **linear time-invariant** systems that the
harmonic-linearization note uses as sanity checks.

1. Truncated Hill matrix of an LTI system. For a constant state matrix `A₀` the lifted Hill
   matrix `𝓗_K = 𝓐_K − 𝓝_K` (harmonics `h = −K, …, K`, `𝓝 = diag(jhω_s I)`) is block diagonal
   with blocks `A₀ − jhω_s I` (`hillLTI`). Its characteristic determinant factorizes
   (`det_hillLTI`), so `s` is an eigenvalue of `𝓗_K` iff `s + jhω_s` is an eigenvalue of `A₀` for
   some `|h| ≤ K`, i.e. `eig(𝓗_K) = {λ − jhω_s}` (`hillLTI_root_iff`).
2. Sequence injection in the αβ frame (amplitude-invariant Clarke, `Transform.clarke`): a
   negative-sequence three-phase signal `V cos(θ + φ − 2πk/3·(−1))` maps to the αβ vector
   `V(cos(θ + φ), −sin(θ + φ))`, i.e. `V e^{−j(θ+φ)}` (`clarke_mulVec_negSeq`). The
   positive-sequence counterpart `V e^{j(θ+φ)}` is `Transform.clarke_mulVec_balanced`
   (already in powerlib).
3. No mirror coupling for LTI. For a (real-coefficient) LTI model driven by complex tones, a
   tone at `jω` produces exactly `G(jω) U e^{jωt}` (`tone_solves`), tones superpose, and the
   coefficients of distinct exponentials are unique (`exp_coeff_unique`). Hence for the mirror
   pair `ω_p`, `ω_c = 2ω_s − ω_p` with `ω_p ≠ ω_s` (so `ω_c ≠ ω_p`), the steady-state output
   coefficient at `ω_p` is `G(jω_p) V(ω_p)` and at `ω_c` is `G(jω_c) V(ω_c)`
   (`mirror_coupling_zero`): the off-diagonal entries `Y₁₂`, `Y₂₁` vanish.

Source: work-sync theory/T-harmonic-linearization.md §1.2 (sequence injection
`δv₊^{αβ} = V_p e^{jω_p t}`, `δv₋^{αβ} = V_n e^{−jω_p t}`), §1.3 ("纯 LTI 系统 `Y₁₂ = Y₂₁ = 0`";
the premise `ω_p ≠ ω_s` is added: at `ω_p = ω_s` the mirror pair collapses to one frequency),
§1.5–1.6 (Hill matrix, LTI check `eig(𝓗) = {λ_i(A₀) − jkω_s}`).
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
      ∏ k, (LTI.characteristicMatrix A (s + (harmonicIndex K k : ℂ) * ωs * I)).det := by
  have h : s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) - hillLTI A ωs K =
      Matrix.blockDiagonal fun k =>
        LTI.characteristicMatrix A (s + (harmonicIndex K k : ℂ) * ωs * I) := by
    rw [hillLTI, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_smul,
      ← Matrix.blockDiagonal_sub]
    congr 1
    funext k
    simp only [LTI.characteristicMatrix, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, add_smul]
    abel
  rw [h, Matrix.det_blockDiagonal]

/-- `s` is a characteristic root of `𝓗_K` iff `s + jhω_s` is an eigenvalue of `A₀` for some
`|h| ≤ K`: `eig(𝓗_K) = {λ_i(A₀) − jhω_s}`. -/
@[powerlib_foundation] theorem hillLTI_root_iff (A : Matrix X X ℝ) (ωs : ℝ) (K : ℕ) (s : ℂ) :
    (s • (1 : Matrix (X × Fin (2 * K + 1)) (X × Fin (2 * K + 1)) ℂ) - hillLTI A ωs K).det = 0 ↔
      ∃ k : Fin (2 * K + 1),
        (LTI.characteristicMatrix A (s + (harmonicIndex K k : ℂ) * ωs * I)).det = 0 := by
  rw [det_hillLTI, Finset.prod_eq_zero_iff]
  simp

end Hill

/-! ## 2. Negative-sequence injection in the αβ frame -/

/-- Negative-sequence three-phase signal `V cos(θ + φ)`, `V cos(θ + 2π/3 + φ)`,
`V cos(θ − 2π/3 + φ)` (phases `b`, `c` swapped with respect to `Transform.balanced`). -/
def negSeq (V φ θ : ℝ) : Fin 3 → ℝ :=
  ![V * Real.cos (θ + φ), V * Real.cos (θ + 2 * Real.pi / 3 + φ),
    V * Real.cos (θ - 2 * Real.pi / 3 + φ)]

@[powerlib_foundation] private lemma cos_two_pi_div_three' :
    Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

@[powerlib_foundation] private lemma sin_two_pi_div_three' :
    Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- A negative-sequence signal is `V e^{−j(θ+φ)}` in αβ: `(V cos(θ + φ), −V sin(θ + φ))`. -/
@[powerlib_foundation] theorem clarke_mulVec_negSeq (V φ θ : ℝ) :
    Transform.clarke *ᵥ negSeq V φ θ = ![V * Real.cos (θ + φ), -(V * Real.sin (θ + φ))] := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h1 : θ + 2 * Real.pi / 3 + φ = (θ + φ) + 2 * Real.pi / 3 := by ring
  have h2 : θ - 2 * Real.pi / 3 + φ = (θ + φ) - 2 * Real.pi / 3 := by ring
  simp only [negSeq, h1, h2]
  generalize θ + φ = ψ
  rw [Real.cos_sub ψ, Real.cos_add ψ, cos_two_pi_div_three', sin_two_pi_div_three']
  ext i; fin_cases i <;>
    simp [Transform.clarke, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ring
  · linear_combination (-(1 / 3)) * V * Real.sin ψ * h3

/-- In complex form, `toComplex (clarke · negSeq) = V e^{−j(θ+φ)}`. -/
@[powerlib_foundation] theorem toComplex_clarke_negSeq (V φ θ : ℝ) :
    Transform.toComplex (Transform.clarke *ᵥ negSeq V φ θ) =
      V * Complex.exp (-((θ + φ : ℝ) : ℂ) * I) := by
  rw [clarke_mulVec_negSeq]
  have he : Complex.exp (-((θ + φ : ℝ) : ℂ) * I) =
      ((Real.cos (θ + φ) : ℝ) : ℂ) - ((Real.sin (θ + φ) : ℝ) : ℂ) * I := by
    rw [show -((θ + φ : ℝ) : ℂ) * I = ((-(θ + φ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  rw [he]
  generalize Real.cos (θ + φ) = c
  generalize Real.sin (θ + φ) = sn
  apply Complex.ext <;> simp [Transform.toComplex]

/-! ## 3. No mirror coupling for LTI systems -/

section Mirror

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

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

/-- Complex-signal trajectories of an LTI model with complex input `u`. -/
def IsToneTrajectory (m : LTI.Model ι κ) (u : ℝ → κ → ℂ) (x : ℝ → ι → ℂ) : Prop :=
  ∀ t, HasDerivAt x (LTI.complexify m.A *ᵥ x t + LTI.complexify m.B *ᵥ u t) t

/-- The output `y = C x + D u` of a complex-signal trajectory. -/
def toneOutput (m : LTI.Model ι κ) (u : ℝ → κ → ℂ) (x : ℝ → ι → ℂ) (t : ℝ) : κ → ℂ :=
  LTI.complexify m.C *ᵥ x t + LTI.complexify m.D *ᵥ u t

/-- Steady state of a single tone `U e^{jωt}`: `x = (jωI − A)⁻¹ B U e^{jωt}`. -/
def toneState (m : LTI.Model ι κ) (ω : ℝ) (U : κ → ℂ) (t : ℝ) : ι → ℂ :=
  Complex.exp (ω * t * I) • ((LTI.characteristicMatrix m.A (ω * I))⁻¹ *ᵥ
    (LTI.complexify m.B *ᵥ U))

@[powerlib_foundation] theorem tone_solves (m : LTI.Model ι κ) {ω : ℝ}
    (h : (LTI.characteristicMatrix m.A (ω * I)).det ≠ 0) (U : κ → ℂ) :
    IsToneTrajectory m (fun t => Complex.exp (ω * t * I) • U) (toneState m ω U) := by
  intro t
  set R := LTI.characteristicMatrix m.A (ω * I)
  set w := R⁻¹ *ᵥ (LTI.complexify m.B *ᵥ U)
  have hRw : R *ᵥ w = LTI.complexify m.B *ᵥ U := by
    simp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h),
      Matrix.one_mulVec]
  have hAw : ((ω : ℂ) * I) • w = LTI.complexify m.A *ᵥ w + LTI.complexify m.B *ᵥ U := by
    rw [← hRw]
    simp only [R, LTI.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, LTI.complexify]
    abel
  have he : HasDerivAt (fun t : ℝ => Complex.exp (ω * t * I)) (ω * I * Complex.exp (ω * t * I))
      t := by
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 t := hasDerivAt_id t |>.ofReal_comp
    have h2 := ((h1.const_mul (ω : ℂ)).mul_const I).cexp
    convert h2 using 1; ring
  have hx := he.smul_const w
  show HasDerivAt (fun y : ℝ => Complex.exp (ω * y * I) • w)
    (LTI.complexify m.A *ᵥ (Complex.exp (ω * t * I) • w) +
      LTI.complexify m.B *ᵥ (Complex.exp (ω * t * I) • U)) t
  convert hx using 1
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, ← hAw, smul_smul]
  congr 1; ring

/-- The output of a single tone is `G(jω) U e^{jωt}`. -/
@[powerlib_foundation] theorem toneOutput_eq (m : LTI.Model ι κ) (ω : ℝ) (U : κ → ℂ) (t : ℝ) :
    toneOutput m (fun t => Complex.exp (ω * t * I) • U) (toneState m ω U) t =
      Complex.exp (ω * t * I) • (LTI.transfer m (ω * I) *ᵥ U) := by
  simp only [toneOutput, toneState, LTI.transfer, Matrix.mulVec_smul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, smul_add]

/-- LTI systems do not couple the mirror frequency: if the two-tone steady-state output
(`ω_p`, `ω_c = 2ω_s − ω_p`, `ω_p ≠ ω_s`) is written as `Y₁ e^{jω_p t} + Y₂ e^{jω_c t}`, then
`Y₁ = G(jω_p) V₁` and `Y₂ = G(jω_c) V₂`: the off-diagonal entries `Y₁₂ = Y₂₁ = 0`. -/
@[powerlib_foundation] theorem mirror_coupling_zero (m : LTI.Model ι κ) {ωp ωs : ℝ}
    (hne : ωp ≠ ωs) (V₁ V₂ Y₁ Y₂ : κ → ℂ)
    (hy : ∀ t, toneOutput m (fun t => Complex.exp (ωp * t * I) • V₁) (toneState m ωp V₁) t +
        toneOutput m (fun t => Complex.exp ((2 * ωs - ωp : ℝ) * t * I) • V₂)
          (toneState m (2 * ωs - ωp) V₂) t =
      Complex.exp (ωp * t * I) • Y₁ + Complex.exp ((2 * ωs - ωp : ℝ) * t * I) • Y₂) :
    Y₁ = LTI.transfer m (ωp * I) *ᵥ V₁ ∧
      Y₂ = LTI.transfer m (((2 * ωs - ωp : ℝ) : ℂ) * I) *ᵥ V₂ := by
  have hω : ωp ≠ 2 * ωs - ωp := by
    intro h; apply hne; linarith
  have hk : ∀ k, (Y₁ k - (LTI.transfer m (ωp * I) *ᵥ V₁) k = 0) ∧
      (Y₂ k - (LTI.transfer m (((2 * ωs - ωp : ℝ) : ℂ) * I) *ᵥ V₂) k = 0) := by
    intro k
    apply exp_coeff_unique hω
    intro t
    have := congrFun (hy t) k
    rw [toneOutput_eq, toneOutput_eq] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination -this
  exact ⟨funext fun k => sub_eq_zero.mp (hk k).1, funext fun k => sub_eq_zero.mp (hk k).2⟩

end Mirror

end powerlib.Periodic
