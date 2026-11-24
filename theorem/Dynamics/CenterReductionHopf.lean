import theorem.Dynamics.Degenerate.PlanarFocus
import theorem.Dynamics.CenterManifoldDefs

/-! # Kuznetsov's projection formula as the planar formula of the reduced field (foundation)

For a field `F` on `ℝⁿ` with a critical pair `(q, p)` of `A = DF(0)` (`A q = iωq`,
`Aᵀ p = −iωp`, `⟨p, q⟩ = 1`, `ω > 0`), the centre plane is coordinatized by the critical chart
`ι y = y₀ (a + b) + y₁ (a − b)` (`q = a + ib`), `π x = (Re⟨p, x⟩ − Im⟨p, x⟩, Re⟨p, x⟩ + Im⟨p, x⟩)`,
with spectral projection `P = ι π`. In these coordinates the reduced linear part is the rotation
`(y₀, y₁) ↦ (−ωy₁, ωy₀)`, and the planar first Lyapunov coefficient of the reduced quadratic and
cubic parts — with the quadratic part `H` of the centre manifold solving the homological
equation — equals Kuznetsov's projection formula `firstLyapunov F 0 ω q p` exactly.

Scope.
* Generic: `State n = ℝⁿ`, a real linear map `A`, a critical pair (`IsCritical`), the second and
  third derivatives of `F` at `0` given by a bilinear `Q` (`D²F(0)(u, w) = Q(u, w) + Q(w, u)`)
  and a trilinear `C` (`D³F(0)` the sum of `C` over the six orders of its arguments), `A` and
  `2iω − A` invertible, and `H` with values in `ker P` solving the homological equation
  `H(u, PAu) + H(PAu, u) = (1 − P)A H(u, u) + (1 − P)Q(u, u)` on `range P`. Nothing here
  describes a physical system (foundation).
* The identity is algebraic (complex linear algebra on `ℂⁿ` and `ℂ²`); the dynamical reading
  (instability for `ℓ₁ > 0`) is in `theorem/Dynamics/CenterReduction.lean`.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 (eq. (3.20), the
planar formula), §5.4 (the projection method: `h₂₀ = (2iω − A)⁻¹(1 − P)B(q, q)`,
`h₁₁ = −A⁻¹(1 − P)B(q, q̄)`, eq. (5.39)); Carr, *Applications of Centre Manifold Theory* (1981),
§2.5.

Results.
* The critical chart: `reV`, `imV` (real and imaginary parts), `IsCritical` (critical pair of a
  real linear map), `IsCritical.apply_re`, `apply_im` (`Aa = −ωb`, `Ab = ωa`),
  `IsCritical.pairing_mulVec`, `pairing_star` (`⟨p, q̄⟩ = 0`), `inner_values`, `inner_apply`;
  `critι`, `critπ`, `critP`, `rotL` and `IsCritical.critπ_critι` (`π ι = 1`),
  `apply_critι` (`A ι = ι L`), `critπ_apply` (`π A = L π`), `isChart`,
  `isCommutingProjection`, `critπ_comp` (the reduced linear part is the rotation `rotL ω`),
  `rotL_rotL` (`L² = −ω²`).
* Complexification: `cmapR`, `cmapR_toC`, `clin_ext`, `cmapR_comp`, `cmapR_critι_critVec`
  (`ι_ℂ critVec = q`), `pairing_critVec_cmapR_critπ` (the planar pairing with `critVec` reads
  `⟨p, ·⟩`), `cmat_rotL`, `IsCritical.cmat_cmapR_critι`, `cmapR_critπ_cmat`, `inv_cmapR`,
  `inv_shift2_cmapR` (the resolvents restricted to the centre plane).
* The reduced data: `triQH`, `redQ`, `redC` (real), `cbiOf`, `ctriOf`, `sym6`, `redB`, `redT`
  (complexified), `redB_jet`, `redT_jet` (their jet in the rotation coordinates of `rotL ω`),
  `redB_eq` (`B₂ = π B(ι·, ι·)`).
* Homological equation and resolvents: `homological_polarized`, `homological_vectors`,
  `IsCritical.rs_eq` (`A⁻¹(1 − P)B(q, q̄) = −(H(v₀, v₀) + H(v₁, v₁))`), `IsCritical.ss_eq`
  (`(2iω − A)⁻¹(1 − P)B(q, q) = H(v₀, v₁) + H(v₁, v₀) + i(H(v₀, v₀) − H(v₁, v₁))`).
* `lyap1_transport` (Kuznetsov's formula transported along a reduction), `cubic_identity` (the
  cubic part of the reduced field carries the complement resolvent terms).
* **`IsCritical.l1_reduced_eq_firstLyapunov`**:
  `PlanarFocus.l1 (rotL ω) (redQ q p Q) (redC q p Q H C) ω = firstLyapunov F 0 ω q p`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Complex Matrix NormalForm.LyapunovCoefficient
open powerlib.Dynamics (State)

section Chart

variable {n : ℕ}

/-- The real part of a complex vector, as a state. -/
def reV (z : Fin n → ℂ) : State n := ∑ k, (z k).re • basisVec k

/-- The imaginary part of a complex vector, as a state. -/
def imV (z : Fin n → ℂ) : State n := ∑ k, (z k).im • basisVec k

@[tmio T, simp, powerlib_foundation]
theorem reV_apply (z : Fin n → ℂ) (k : Fin n) : reV z k = (z k).re := by
  simp [reV, basisVec, Finset.sum_apply, Pi.single_apply]

@[tmio T, simp, powerlib_foundation]
theorem imV_apply (z : Fin n → ℂ) (k : Fin n) : imV z k = (z k).im := by
  simp [imV, basisVec, Finset.sum_apply, Pi.single_apply]

@[tmio T, powerlib_foundation]
theorem toC_reV_add_imV (z : Fin n → ℂ) : toC (reV z) + I • toC (imV z) = z := by
  ext k; simp [Complex.ext_iff]

@[tmio T, powerlib_foundation]
theorem toC_reV_sub_imV (z : Fin n → ℂ) : toC (reV z) - I • toC (imV z) = star z := by
  ext k; simp [Complex.ext_iff]

@[tmio T, powerlib_foundation]
theorem inner_state (a x : State n) : inner ℝ a x = ∑ k, a k * x k := by
  simp [PiLp.inner_apply, mul_comm]

@[tmio T, powerlib_foundation] theorem pairing_toC (p : Fin n → ℂ) (x : State n) :
    pairing p (toC x) = (inner ℝ (reV p) x : ℂ) - I * (inner ℝ (imV p) x : ℂ) := by
  rw [pairing_apply, inner_state, inner_state]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [toC_apply, reV_apply, imV_apply]
  apply Complex.ext <;> simp

end Chart

section CriticalChart

variable {n : ℕ}

/-- A critical pair of a real linear map: `A q = iω q`, `Aᵀ p = −iω p`, `⟨p, q⟩ = 1`, `ω > 0`. -/
structure IsCritical (A : State n →L[ℝ] State n) (ω : ℝ) (q p : Fin n → ℂ) : Prop where
  /-- The frequency is positive. -/
  freq_pos : 0 < ω
  /-- `q` is a right eigenvector of `iω`. -/
  right : cmat A *ᵥ q = ((ω : ℂ) * I) • q
  /-- `p` is an eigenvector of `Aᵀ` for `−iω`. -/
  left : (cmat A)ᵀ *ᵥ p = (-((ω : ℂ) * I)) • p
  /-- `⟨p, q⟩ = 1`. -/
  normalized : star p ⬝ᵥ q = 1

/-- A critical pair of a field at `0` (`NormalForm.LyapunovCoefficient.IsCriticalPair`) is a
critical pair of its Jacobian. -/
@[tmio T, powerlib_foundation] theorem IsCriticalPair.isCritical {F : State n → State n}
    {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ} (h : IsCriticalPair F 0 ω q p)
    (hdA : fderiv ℝ F 0 = A) : IsCritical A ω q p := by
  have hJ : jacobianC F 0 = cmat A := by rw [jacobianC, hdA]
  exact ⟨h.freq_pos, hJ ▸ h.right, hJ ▸ h.left, h.normalized⟩

@[tmio T, powerlib_foundation]
theorem cmat_mulVec_star (L : State n →L[ℝ] State n) (v : Fin n → ℂ) :
    star (cmat L *ᵥ v) = cmat L *ᵥ star v := by
  ext k; simp [Matrix.mulVec, dotProduct]

@[tmio T, powerlib_foundation]
theorem star_cmatT_mulVec (L : State n →L[ℝ] State n) (v : Fin n → ℂ) :
    star ((cmat L)ᵀ *ᵥ v) = (cmat L)ᵀ *ᵥ star v := by
  ext k; simp [Matrix.mulVec, dotProduct]

variable {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation] theorem cmat_mulVec_toC_add_smul (a b : State n) :
    cmat A *ᵥ (toC a + I • toC b) = toC (A a) + I • toC (A b) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, cmat_mulVec_toC, cmat_mulVec_toC]

@[tmio T, powerlib_foundation]
theorem IsCritical.apply_re (hc : IsCritical A ω q p) : A (reV q) = (-ω) • imV q := by
  have h := hc.right
  rw [← toC_reV_add_imV q, cmat_mulVec_toC_add_smul] at h
  ext k
  have hk := congrFun h k
  simp only [Pi.add_apply, Pi.smul_apply, toC_apply, smul_eq_mul, Complex.ext_iff,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hk
  simp only [PiLp.smul_apply, smul_eq_mul]
  linarith [hk.1]

@[tmio T, powerlib_foundation]
theorem IsCritical.apply_im (hc : IsCritical A ω q p) : A (imV q) = ω • reV q := by
  have h := hc.right
  rw [← toC_reV_add_imV q, cmat_mulVec_toC_add_smul] at h
  ext k
  have hk := congrFun h k
  simp only [Pi.add_apply, Pi.smul_apply, toC_apply, smul_eq_mul, Complex.ext_iff,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hk
  simp only [PiLp.smul_apply, smul_eq_mul]
  linarith [hk.2]

/-- `p` is a left eigenvector: `⟨p, A x⟩ = iω ⟨p, x⟩`. -/
@[tmio T, powerlib_foundation]
theorem IsCritical.pairing_mulVec (hc : IsCritical A ω q p) (x : Fin n → ℂ) :
    pairing p (cmat A *ᵥ x) = ((ω : ℂ) * I) * pairing p x := by
  rw [pairing_eq_dotProduct, pairing_eq_dotProduct, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  have h : (cmat A)ᵀ *ᵥ star p = ((ω : ℂ) * I) • star p := by
    rw [← star_cmatT_mulVec, hc.left, star_smul]
    congr 1
    simp
  rw [h, smul_dotProduct, smul_eq_mul]

@[tmio T, powerlib_foundation]
theorem IsCritical.pairing_star (hc : IsCritical A ω q p) : pairing p (star q) = 0 := by
  have h1 : cmat A *ᵥ star q = (-((ω : ℂ) * I)) • star q := by
    rw [← cmat_mulVec_star, hc.right, star_smul]
    congr 1
    simp
  have h2 := hc.pairing_mulVec (star q)
  rw [h1, map_smul, smul_eq_mul] at h2
  have hω : ((ω : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hc.freq_pos.ne') I_ne_zero
  have : (2 * ((ω : ℂ) * I)) * pairing p (star q) = 0 := by linear_combination -h2
  exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hω)

@[tmio T, powerlib_foundation]
theorem IsCritical.pairing_re (hc : IsCritical A ω q p) : pairing p (toC (reV q)) = 1 / 2 := by
  have h1 : pairing p q = 1 := by rw [pairing_eq_dotProduct]; exact hc.normalized
  have h2 := hc.pairing_star
  rw [← toC_reV_add_imV q, map_add, map_smul, smul_eq_mul] at h1
  rw [← toC_reV_sub_imV q, map_sub, map_smul, smul_eq_mul] at h2
  linear_combination (h1 + h2) / 2

@[tmio T, powerlib_foundation]
theorem IsCritical.pairing_im (hc : IsCritical A ω q p) : pairing p (toC (imV q)) = -I / 2 := by
  have h1 : pairing p q = 1 := by rw [pairing_eq_dotProduct]; exact hc.normalized
  have h2 := hc.pairing_star
  rw [← toC_reV_add_imV q, map_add, map_smul, smul_eq_mul] at h1
  rw [← toC_reV_sub_imV q, map_sub, map_smul, smul_eq_mul] at h2
  have : I * pairing p (toC (imV q)) = 1 / 2 := by linear_combination (h1 - h2) / 2
  have hI : I * (-I / 2) = 1 / 2 := by ring_nf; simp [Complex.I_sq]; ring
  exact mul_left_cancel₀ I_ne_zero (this.trans hI.symm)

/-- The four real pairings of the chart. -/
@[tmio T, powerlib_foundation] theorem IsCritical.inner_values (hc : IsCritical A ω q p) :
    inner ℝ (reV p) (reV q) = 1 / 2 ∧ inner ℝ (imV p) (reV q) = 0 ∧
      inner ℝ (reV p) (imV q) = 0 ∧ inner ℝ (imV p) (imV q) = 1 / 2 := by
  have h1 := hc.pairing_re
  have h2 := hc.pairing_im
  rw [pairing_toC] at h1 h2
  simp only [Complex.ext_iff, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_re,
    Complex.div_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im] at h1 h2
  norm_num at h1 h2
  refine ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2]⟩

/-- `⟨p, A x⟩ = iω ⟨p, x⟩` on real vectors. -/
@[tmio T, powerlib_foundation]
theorem IsCritical.inner_apply (hc : IsCritical A ω q p) (x : State n) :
    inner ℝ (reV p) (A x) = ω * inner ℝ (imV p) x ∧
      inner ℝ (imV p) (A x) = -(ω * inner ℝ (reV p) x) := by
  have h := hc.pairing_mulVec (toC x)
  rw [cmat_mulVec_toC, pairing_toC, pairing_toC] at h
  simp only [Complex.ext_iff, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at h
  norm_num at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end CriticalChart

section ChartMaps

variable {n : ℕ}

/-- The chart `ι y = y₀ (a + b) + y₁ (a − b)`, `a + ib = q`: `ι_ℂ` maps `critVec` to `q`. -/
def critι (q : Fin n → ℂ) : State 2 →L[ℝ] State n :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (reV q + imV q) +
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (reV q - imV q)

/-- The coordinates `π x = (Re⟨p, x⟩ − Im⟨p, x⟩, Re⟨p, x⟩ + Im⟨p, x⟩)`. -/
def critπ (p : Fin n → ℂ) : State n →L[ℝ] State 2 :=
  (innerSL ℝ (reV p + imV p)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (innerSL ℝ (reV p - imV p)).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- The planar rotation `(y₀, y₁) ↦ (−ω y₁, ω y₀)`. -/
def rotL (ω : ℝ) : State 2 →L[ℝ] State 2 :=
  (-ω) • (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    ω • (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

@[tmio T, powerlib_foundation] theorem critι_apply (q : Fin n → ℂ) (y : State 2) :
    critι q y = y 0 • (reV q + imV q) + y 1 • (reV q - imV q) := by
  simp [critι]

@[tmio T, powerlib_foundation] theorem critπ_apply0 (p : Fin n → ℂ) (x : State n) :
    critπ p x 0 = inner ℝ (reV p) x + inner ℝ (imV p) x := by
  simp [critπ]

@[tmio T, powerlib_foundation] theorem critπ_apply1 (p : Fin n → ℂ) (x : State n) :
    critπ p x 1 = inner ℝ (reV p) x - inner ℝ (imV p) x := by
  simp [critπ]

@[tmio T, powerlib_foundation]
theorem rotL_apply0 (ω : ℝ) (y : State 2) : rotL ω y 0 = -(ω * y 1) := by
  simp [rotL]

@[tmio T, powerlib_foundation]
theorem rotL_apply1 (ω : ℝ) (y : State 2) : rotL ω y 1 = ω * y 0 := by
  simp [rotL]

@[tmio T, powerlib_foundation]
theorem rotL_rotL (ω : ℝ) (y : State 2) : rotL ω (rotL ω y) = -(ω ^ 2) • y := by
  ext i; fin_cases i <;> simp [rotL_apply0, rotL_apply1] <;> ring

variable {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation]
theorem IsCritical.critπ_critι (hc : IsCritical A ω q p) (y : State 2) :
    critπ p (critι q y) = y := by
  obtain ⟨h1, h2, h3, h4⟩ := hc.inner_values
  ext i; fin_cases i
  · simp only [Fin.zero_eta, critπ_apply0, critι_apply, inner_add_right, inner_smul_right,
      inner_sub_right, h1, h2, h3, h4]
    ring
  · simp only [Fin.mk_one, critπ_apply1, critι_apply, inner_add_right, inner_smul_right,
      inner_sub_right, h1, h2, h3, h4]
    ring

@[tmio T, powerlib_foundation]
theorem IsCritical.apply_critι (hc : IsCritical A ω q p) (y : State 2) :
    A (critι q y) = critι q (rotL ω y) := by
  rw [critι_apply, critι_apply, map_add, map_smul, map_smul, map_add, map_sub, hc.apply_re,
    hc.apply_im, rotL_apply0, rotL_apply1]
  ext k
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, reV_apply,
    imV_apply]
  ring

@[tmio T, powerlib_foundation]
theorem IsCritical.critπ_apply (hc : IsCritical A ω q p) (x : State n) :
    critπ p (A x) = rotL ω (critπ p x) := by
  obtain ⟨h1, h2⟩ := hc.inner_apply x
  ext i; fin_cases i
  · simp only [Fin.zero_eta, critπ_apply0, rotL_apply0, critπ_apply1, h1, h2]; ring
  · simp only [Fin.mk_one, critπ_apply1, rotL_apply1, critπ_apply0, h1, h2]; ring

/-- The spectral projection onto the critical plane, `P = ι π`. -/
def critP (q p : Fin n → ℂ) : State n →L[ℝ] State n := (critι q).comp (critπ p)

@[tmio T, powerlib_foundation]
theorem IsCritical.isChart (hc : IsCritical A ω q p) : IsChart (critP q p) (critι q) (critπ p) :=
  ⟨hc.critπ_critι, fun _ => rfl⟩

@[tmio T, powerlib_foundation] theorem IsCritical.isCommutingProjection (hc : IsCritical A ω q p) :
    IsCommutingProjection A (critP q p) :=
  ⟨fun x => by simp [critP, hc.critπ_critι],
    fun x => by simp only [critP, ContinuousLinearMap.comp_apply, hc.apply_critι, hc.critπ_apply]⟩

/-- The reduced linear part is the rotation. -/
@[tmio T, powerlib_foundation]
theorem IsCritical.critπ_comp (hc : IsCritical A ω q p) (y : State 2) :
    critπ p (A (critι q y)) = rotL ω y := by
  rw [hc.apply_critι, hc.critπ_critι]

end ChartMaps

section Transport

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- **Transport of Kuznetsov's formula along a reduction.** If the reduced data are the full
data read through `ι`, `π` (`B₂ = π B(ι·, ι·)`, the reduced pairing is the full one on `π`),
the full resolvents differ from the reduced ones read through `ι` by `r_s`, `s_s`, and the
reduced cubic term carries the corresponding corrections, the two formulas agree. -/
@[tmio T, powerlib_foundation]
theorem lyap1_transport (B : V →ₗ[ℂ] V →ₗ[ℂ] V) (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (Ainv R2 : V →ₗ[ℂ] V) (Pv : V →ₗ[ℂ] ℂ) (B₂ : W →ₗ[ℂ] W →ₗ[ℂ] W)
    (C₂ : W →ₗ[ℂ] W →ₗ[ℂ] W →ₗ[ℂ] W) (Ainv₂ R2₂ : W →ₗ[ℂ] W) (Pw : W →ₗ[ℂ] ℂ)
    (ι : W →ₗ[ℂ] V) (π : V →ₗ[ℂ] W) (ω : ℝ) (q₂ qc₂ : W) (rs ss : V)
    (hP : ∀ x, Pw (π x) = Pv x) (hB : ∀ u w, B₂ u w = π (B (ι u) (ι w)))
    (hr : Ainv (B (ι q₂) (ι qc₂)) = ι (Ainv₂ (B₂ q₂ qc₂)) + rs)
    (hs : R2 (B (ι q₂) (ι q₂)) = ι (R2₂ (B₂ q₂ q₂)) + ss)
    (hC : Pw (C₂ q₂ q₂ qc₂) = Pv (C (ι q₂) (ι q₂) (ι qc₂)) - 2 * Pv (B (ι q₂) rs) +
      Pv (B (ι qc₂) ss)) :
    NormalForm.Hopf.lyap1 B₂ C₂ Ainv₂ R2₂ Pw ω q₂ qc₂ =
      NormalForm.Hopf.lyap1 B C Ainv R2 Pv ω (ι q₂) (ι qc₂) := by
  have e2 : Pw (B₂ q₂ (Ainv₂ (B₂ q₂ qc₂))) =
      Pv (B (ι q₂) (Ainv (B (ι q₂) (ι qc₂)))) - Pv (B (ι q₂) rs) := by
    rw [hB, hP, hr, map_add, map_add, add_sub_cancel_right]
  have e3 : Pw (B₂ qc₂ (R2₂ (B₂ q₂ q₂))) =
      Pv (B (ι qc₂) (R2 (B (ι q₂) (ι q₂)))) - Pv (B (ι qc₂) ss) := by
    rw [hB, hP, hs, map_add, map_add, add_sub_cancel_right]
  simp only [NormalForm.Hopf.lyap1, e2, e3, hC]
  congr 2
  ring

end Transport

section Complexification

variable {m n : ℕ}

/-- The complexification of a real linear map `ℝᵐ → ℝⁿ`. -/
def cmapR (L : State m →L[ℝ] State n) : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.mulVecLin (Matrix.of fun k j => (L (basisVec j) k : ℂ))

@[tmio T, powerlib_foundation]
theorem cmapR_apply (L : State m →L[ℝ] State n) (u : Fin m → ℂ) (k : Fin n) :
    cmapR L u k = ∑ j, (L (basisVec j) k : ℂ) * u j := by
  simp [cmapR, Matrix.mulVec, dotProduct]

@[tmio T, powerlib_foundation]
theorem cmapR_toC (L : State m →L[ℝ] State n) (a : State m) : cmapR L (toC a) = toC (L a) := by
  ext k
  conv_rhs => rw [← sum_basisVec a]
  simp [cmapR_apply, map_sum, map_smul, mul_comm]

@[tmio T, powerlib_foundation] theorem cmapR_eq_cmat (L : State n →L[ℝ] State n) (u : Fin n → ℂ) :
    cmapR L u = cmat L *ᵥ u := rfl

/-- Complex-linear maps out of `ℂᵐ` agreeing on the real basis are equal. -/
@[tmio T, powerlib_foundation]
theorem clin_ext {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : (Fin m → ℂ) →ₗ[ℂ] V}
    (h : ∀ i, f (toC (basisVec i)) = g (toC (basisVec i))) : f = g := by
  refine LinearMap.pi_ext fun i x => ?_
  have hx : (Pi.single i x : Fin m → ℂ) = x • toC (basisVec i) := by
    rw [toC_basisVec]; ext j; by_cases hj : j = i <;> simp [hj]
  rw [hx, map_smul, map_smul, h]

@[tmio T, powerlib_foundation]
theorem cmapR_comp {l : ℕ} (L : State m →L[ℝ] State n) (L' : State l →L[ℝ] State m) :
    cmapR (L.comp L') = (cmapR L).comp (cmapR L') :=
  clin_ext fun i => by simp [cmapR_toC]

@[tmio T, powerlib_foundation]
theorem toC_add (a b : State n) : toC (a + b) = toC a + toC b := by ext k; simp
@[tmio T, powerlib_foundation]
theorem toC_sub (a b : State n) : toC (a - b) = toC a - toC b := by ext k; simp
@[tmio T, powerlib_foundation]
theorem toC_smul (r : ℝ) (a : State n) : toC (r • a) = (r : ℂ) • toC a := by ext k; simp
@[tmio T, powerlib_foundation] theorem toC_neg (a : State n) : toC (-a) = -toC a := by ext k; simp

end Complexification

section ChartComplex

open Degenerate.PlanarFocus

variable {n : ℕ} {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation]
theorem inner_basisVec (a : State n) (k : Fin n) : inner ℝ a (basisVec k) = a k := by
  simp [basisVec, EuclideanSpace.inner_single_right]

@[tmio T, powerlib_foundation] theorem cmapR_critι (q : Fin n → ℂ) (u : Fin 2 → ℂ) :
    cmapR (critι q) u = u 0 • toC (reV q + imV q) + u 1 • toC (reV q - imV q) := by
  ext k
  simp [cmapR_apply, critι_apply, Fin.sum_univ_two, basisVec, mul_comm]

@[tmio T, powerlib_foundation]
theorem cmapR_critι_critVec (q : Fin n → ℂ) : cmapR (critι q) critVec = q := by
  rw [cmapR_critι]
  ext k
  simp [critVec, Complex.ext_iff]
  constructor <;> ring

@[tmio T, powerlib_foundation]
theorem cmapR_critι_star (q : Fin n → ℂ) : cmapR (critι q) (star critVec) = star q := by
  rw [cmapR_critι, star_critVec]
  ext k
  simp [Complex.ext_iff]
  constructor <;> ring

@[tmio T, powerlib_foundation] theorem pairing_critVec_cmapR_critπ (p x : Fin n → ℂ) :
    pairing critVec (cmapR (critπ p) x) = pairing p x := by
  rw [pairing_apply, pairing_apply, Fin.sum_univ_two, cmapR_apply, cmapR_apply,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [critπ_apply0, critπ_apply1, inner_basisVec, inner_basisVec]
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := by
    apply Complex.ext <;> simp
  have h0 : starRingEnd ℂ (critVec 0) = (1 - I) / 2 := by
    simp [critVec, map_div₀, Complex.conj_I, h2]; ring
  have h1 : starRingEnd ℂ (critVec 1) = (1 + I) / 2 := by
    simp [critVec, map_div₀, Complex.conj_I, h2]
  have hp : starRingEnd ℂ (p k) = ((p k).re : ℂ) - ((p k).im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [h0, h1, hp]
  simp only [reV_apply, imV_apply]
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem cmat_rotL (ω : ℝ) : cmat (rotL ω) = rotC ω := by
  ext k j
  fin_cases k <;> fin_cases j <;> simp [cmat_apply, rotL_apply0, rotL_apply1, rotC, basisVec]

@[tmio T, powerlib_foundation]
theorem cmapR_rotL (ω : ℝ) (y : Fin 2 → ℂ) : cmapR (rotL ω) y = rotC ω *ᵥ y := by
  rw [cmapR_eq_cmat, cmat_rotL]

@[tmio T, powerlib_foundation]
theorem IsCritical.cmat_cmapR_critι (hc : IsCritical A ω q p) (y : Fin 2 → ℂ) :
    cmat A *ᵥ cmapR (critι q) y = cmapR (critι q) (rotC ω *ᵥ y) := by
  have h : (cmapR A).comp (cmapR (critι q)) = (cmapR (critι q)).comp (cmapR (rotL ω)) := by
    rw [← cmapR_comp, ← cmapR_comp]
    congr 1
    ext1 z
    exact hc.apply_critι z
  have := congrArg (fun T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin n → ℂ) => T y) h
  simpa [cmapR_eq_cmat, cmat_rotL] using this

@[tmio T, powerlib_foundation]
theorem IsCritical.cmapR_critπ_cmat (hc : IsCritical A ω q p) (x : Fin n → ℂ) :
    cmapR (critπ p) (cmat A *ᵥ x) = rotC ω *ᵥ cmapR (critπ p) x := by
  have h : (cmapR (critπ p)).comp (cmapR A) = (cmapR (rotL ω)).comp (cmapR (critπ p)) := by
    rw [← cmapR_comp, ← cmapR_comp]
    congr 1
    ext1 z
    exact hc.critπ_apply z
  have := congrArg (fun T : (Fin n → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) => T x) h
  simpa [cmapR_eq_cmat, cmat_rotL] using this

end ChartComplex

section ReducedData

open Degenerate.PlanarFocus

variable {n : ℕ}

/-- The trilinear map `(u, w, z) ↦ Q(u, H(w, z)) + Q(H(u, w), z)`. -/
def triQH (Q H : State n →L[ℝ] State n →L[ℝ] State n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n) where
  toFun m := Q (m 0) (H (m 1) (m 2)) + Q (H (m 0) (m 1)) (m 2)
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin 3 := Subsingleton.elim _ _
    fin_cases i <;> simp <;> abel
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin 3 := Subsingleton.elim _ _
    fin_cases i <;> simp [smul_add]
  cont := by fun_prop

@[tmio T, powerlib_foundation]
theorem triQH_apply (Q H : State n →L[ℝ] State n →L[ℝ] State n) (u w z : State n) :
    triQH Q H ![u, w, z] = Q u (H w z) + Q (H u w) z := rfl

/-- The reduced quadratic part `Q₂(y, y') = π Q(ι y, ι y')`. -/
def redQ (q p : Fin n → ℂ) (Q : State n →L[ℝ] State n →L[ℝ] State n) :
    State 2 →L[ℝ] State 2 →L[ℝ] State 2 :=
  (ContinuousLinearMap.compL ℝ (State 2) (State n) (State 2) (critπ p)).comp
    (Q.bilinearComp (critι q) (critι q))

@[tmio T, powerlib_foundation]
theorem redQ_apply (q p : Fin n → ℂ) (Q : State n →L[ℝ] State n →L[ℝ] State n)
    (y y' : State 2) : redQ q p Q y y' = critπ p (Q (critι q y) (critι q y')) := by
  simp [redQ]

/-- The reduced cubic part `C₂(y, y', y'') = π [Q(ιy, H(ιy', ιy'')) + Q(H(ιy, ιy'), ιy'') +
C(ιy, ιy', ιy'')]`. -/
def redC (q p : Fin n → ℂ) (Q H : State n →L[ℝ] State n →L[ℝ] State n)
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2) :=
  (critπ p).compContinuousMultilinearMap
    ((triQH Q H + C).compContinuousLinearMap fun _ => critι q)

@[tmio T, powerlib_foundation]
theorem redC_apply (q p : Fin n → ℂ) (Q H : State n →L[ℝ] State n →L[ℝ] State n)
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)) (u w z : State 2) :
    redC q p Q H C ![u, w, z] = critπ p (Q (critι q u) (H (critι q w) (critι q z)) +
      Q (H (critι q u) (critι q w)) (critι q z) + C ![critι q u, critι q w, critι q z]) := by
  have e : (fun i => critι q (![u, w, z] i)) = ![critι q u, critι q w, critι q z] := by
    funext i; fin_cases i <;> rfl
  simp only [redC, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, e,
    _root_.add_apply, triQH_apply]

@[tmio T, powerlib_foundation]
theorem frameVec0_rotL {ω : ℝ} (hω : ω ≠ 0) : frameVec0 (rotL ω) = e0 := by
  ext i; fin_cases i <;> simp [frameVec0, rotL_apply0, rotL_apply1, e0, e1, hω]

@[tmio T, powerlib_foundation]
theorem frameVec1_rotL {ω : ℝ} (hω : ω ≠ 0) : frameVec1 (rotL ω) ω = e1 := by
  ext i; fin_cases i <;> simp [frameVec1, rotL_apply0, e1, hω]

@[tmio T, powerlib_foundation]
theorem frameY_rotL {ω : ℝ} (hω : ω ≠ 0) (u : State 2) : frameY (rotL ω) ω u = u 1 := by
  rw [frameY_apply, rotL_apply0]; field_simp

end ReducedData

section Coefficients

open Degenerate.PlanarFocus

variable {m n : ℕ}

/-- The complex bilinear map with real coefficients `c i j k` (`B(u, w)_k = Σ c i j k uᵢ wⱼ`). -/
def cbiOf (c : Fin m → Fin m → Fin n → ℝ) :
    (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ∑ i, (LinearMap.proj i).smulRight (Matrix.mulVecLin (Matrix.of fun k j => (c i j k : ℂ)))

@[tmio T, powerlib_foundation]
theorem cbiOf_apply (c : Fin m → Fin m → Fin n → ℝ) (u w : Fin m → ℂ) (k : Fin n) :
    cbiOf c u w k = ∑ i, ∑ j, (c i j k : ℂ) * u i * w j := by
  simp only [cbiOf, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The complex trilinear map with real coefficients `c i j l k`. -/
def ctriOf (c : Fin m → Fin m → Fin m → Fin n → ℝ) :
    (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  ∑ i, (LinearMap.proj i).smulRight
    (∑ j, (LinearMap.proj j).smulRight
      (Matrix.mulVecLin (Matrix.of fun k l => (c i j l k : ℂ))))

@[tmio T, powerlib_foundation]
theorem ctriOf_apply (c : Fin m → Fin m → Fin m → Fin n → ℝ) (u w z : Fin m → ℂ) (k : Fin n) :
    ctriOf c u w z k = ∑ i, ∑ j, ∑ l, (c i j l k : ℂ) * u i * w j * z l := by
  simp only [ctriOf, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The sum of a trilinear map over the six orders of its arguments. -/
def sym6 (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State m) (State n))
    (x y z : State m) : State n :=
  T ![x, y, z] + T ![x, z, y] + T ![y, x, z] + T ![y, z, x] + T ![z, x, y] + T ![z, y, x]

/-- The reduced bilinear form (complexified second derivative of the reduced field). -/
def redB (q p : Fin n → ℂ) (Q : State n →L[ℝ] State n →L[ℝ] State n) :
    (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  cbiOf fun i j k => (redQ q p Q (basisVec i) (basisVec j) + redQ q p Q (basisVec j) (basisVec i)) k

/-- The reduced trilinear form (complexified third derivative of the reduced field). -/
def redT (q p : Fin n → ℂ) (Q H : State n →L[ℝ] State n →L[ℝ] State n)
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)) :
    (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  ctriOf fun i j l k => sym6 (redC q p Q H C) (basisVec i) (basisVec j) (basisVec l) k

@[tmio T, powerlib_foundation] theorem basisVec_two_zero : (basisVec 0 : State 2) = e0 := rfl
@[tmio T, powerlib_foundation] theorem basisVec_two_one : (basisVec 1 : State 2) = e1 := rfl

@[tmio T, powerlib_foundation]
theorem redB_jet {ω : ℝ} (hω : ω ≠ 0) (q p : Fin n → ℂ) (Q H : State n →L[ℝ] State n →L[ℝ] State n)
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)) (u w : Fin 2 → ℂ) :
    redB q p Q u w = ![2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).a20 * u 0 * w 0 +
        (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).a11 * (u 0 * w 1 + u 1 * w 0) +
        2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).a02 * u 1 * w 1,
      2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).b20 * u 0 * w 0 +
        (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).b11 * (u 0 * w 1 + u 1 * w 0) +
        2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).b02 * u 1 * w 1] := by
  ext k
  rw [redB, cbiOf_apply]
  fin_cases k <;>
    simp [Fin.sum_univ_two, jet, frameVec0_rotL hω, frameVec1_rotL hω, frameY_rotL hω,
      basisVec_two_zero, basisVec_two_one] <;> ring

@[tmio T, powerlib_foundation]
theorem redT_jet {ω : ℝ} (hω : ω ≠ 0) (q p : Fin n → ℂ) (Q H : State n →L[ℝ] State n →L[ℝ] State n)
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)) (u w z : Fin 2 → ℂ) :
    redT q p Q H C u w z =
      ![6 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).a30 * u 0 * w 0 * z 0 +
        2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).a21 *
          (u 0 * w 0 * z 1 + u 0 * w 1 * z 0 + u 1 * w 0 * z 0) +
        2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).a12 *
          (u 0 * w 1 * z 1 + u 1 * w 0 * z 1 + u 1 * w 1 * z 0) +
        6 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).a03 * u 1 * w 1 * z 1,
      6 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).b30 * u 0 * w 0 * z 0 +
        2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).b21 *
          (u 0 * w 0 * z 1 + u 0 * w 1 * z 0 + u 1 * w 0 * z 0) +
        2 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).b12 *
          (u 0 * w 1 * z 1 + u 1 * w 0 * z 1 + u 1 * w 1 * z 0) +
        6 * (jet (rotL ω) (redQ q p Q) (redC q p Q H C) ω).b03 * u 1 * w 1 * z 1] := by
  ext k
  rw [redT, ctriOf_apply]
  fin_cases k <;>
    simp [Fin.sum_univ_two, jet, sym6, frameVec0_rotL hω, frameVec1_rotL hω, frameY_rotL hω,
      basisVec_two_zero, basisVec_two_one] <;> ring

end Coefficients

section HomologicalReal

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- The polarized homological equation: for `u, w ∈ range P`,
`A (H(u, w) + H(w, u)) = H(u, Aw) + H(Aw, u) + H(w, Au) + H(Au, w) − (1 − P)(Q(u, w) + Q(w, u))`. -/
@[tmio T, powerlib_foundation] theorem homological_polarized (hP : IsCommutingProjection A P)
    {Q H : State n →L[ℝ] State n →L[ℝ] State n}
    (hhom : ∀ u, P u = u → H u (P (A u)) + H (P (A u)) u = (1 - P) (A (H u u)) + (1 - P) (Q u u))
    (hPH : ∀ u v, P (H u v) = 0) {u w : State n} (hu : P u = u) (hw : P w = w) :
    A (H u w + H w u) = H u (A w) + H (A w) u + (H w (A u) + H (A u) w) -
      (1 - P) (Q u w + Q w u) := by
  have hPA : ∀ x, P x = x → P (A x) = A x := fun x hx => by rw [← hP.comm, hx]
  have hcA : ∀ x y, (1 - P) (A (H x y)) = A (H x y) := fun x y => by
    rw [compl_apply, ← hP.comm, hPH, map_zero, sub_zero]
  have huw : P (u + w) = u + w := by rw [map_add, hu, hw]
  have d1 := hhom (u + w) huw
  have d2 := hhom u hu
  have d3 := hhom w hw
  rw [hPA _ huw] at d1
  rw [hPA _ hu] at d2
  rw [hPA _ hw] at d3
  simp only [map_add, _root_.add_apply, hcA] at d1 d2 d3
  rw [map_add, map_add]
  linear_combination (norm := abel) d2 + d3 - d1

end HomologicalReal

section ChartVectors

variable {n : ℕ} {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation]
theorem critι_e0 (q : Fin n → ℂ) : critι q (basisVec 0) = reV q + imV q := by
  simp [critι_apply, basisVec]

@[tmio T, powerlib_foundation]
theorem critι_e1 (q : Fin n → ℂ) : critι q (basisVec 1) = reV q - imV q := by
  simp [critι_apply, basisVec]

@[tmio T, powerlib_foundation] theorem IsCritical.apply_v0 (hc : IsCritical A ω q p) :
    A (reV q + imV q) = ω • (reV q - imV q) := by
  rw [map_add, hc.apply_re, hc.apply_im, smul_sub]; abel_nf; module

@[tmio T, powerlib_foundation] theorem IsCritical.apply_v1 (hc : IsCritical A ω q p) :
    A (reV q - imV q) = (-ω) • (reV q + imV q) := by
  rw [map_sub, hc.apply_re, hc.apply_im]; module

@[tmio T, powerlib_foundation]
theorem IsCritical.critP_v0 (hc : IsCritical A ω q p) :
    critP q p (reV q + imV q) = reV q + imV q := by
  rw [← critι_e0, critP, ContinuousLinearMap.comp_apply, hc.critπ_critι]

@[tmio T, powerlib_foundation]
theorem IsCritical.critP_v1 (hc : IsCritical A ω q p) :
    critP q p (reV q - imV q) = reV q - imV q := by
  rw [← critι_e1, critP, ContinuousLinearMap.comp_apply, hc.critπ_critι]

/-- `q = c₀ v₀ + c₁ v₁` with `c = critVec`. -/
@[tmio T, powerlib_foundation] theorem q_eq_comb (q : Fin n → ℂ) :
    q = ((1 + I) / 2) • toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q) := by
  ext k; simp [Complex.ext_iff]; constructor <;> ring

@[tmio T, powerlib_foundation] theorem star_q_eq_comb (q : Fin n → ℂ) :
    star q = ((1 - I) / 2) • toC (reV q + imV q) + ((1 + I) / 2) • toC (reV q - imV q) := by
  ext k; simp [Complex.ext_iff]; constructor <;> ring

@[tmio T, powerlib_foundation] theorem cmapR_critP_toC (q p : Fin n → ℂ) (y : State n) :
    cmapR (critι q) (cmapR (critπ p) (toC y)) = toC (critP q p y) := by
  rw [cmapR_toC, cmapR_toC]; rfl

@[tmio T, powerlib_foundation] theorem cmapR_critP_comb (q p : Fin n → ℂ) (a b : State n) :
    cmapR (critι q) (cmapR (critπ p) (toC a + I • toC b)) =
      toC (critP q p a) + I • toC (critP q p b) := by
  rw [map_add, map_add, map_smul, map_smul, cmapR_critP_toC, cmapR_critP_toC]

end ChartVectors

section FullForms

variable {n : ℕ} {F : State n → State n} {Q : State n →L[ℝ] State n →L[ℝ] State n}

@[tmio T, powerlib_foundation]
theorem bilin_comb (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (a b c d : ℂ) (x y : State n) :
    bilinC F 0 (a • toC x + b • toC y) (c • toC x + d • toC y) =
      (a * c) • toC (Q x x + Q x x) + (a * d) • toC (Q x y + Q y x) +
        (b * c) • toC (Q y x + Q x y) + (b * d) • toC (Q y y + Q y y) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, bilinC_toC, hd2]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

@[tmio T, powerlib_foundation]
theorem bilin_q_starq (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (q : Fin n → ℂ) :
    bilinC F 0 q (star q) = toC (Q (reV q + imV q) (reV q + imV q) +
      Q (reV q - imV q) (reV q - imV q)) := by
  have hq := q_eq_comb q
  have hs := star_q_eq_comb q
  rw [show bilinC F 0 q (star q) = bilinC F 0
      (((1 + I) / 2) • toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q))
      (((1 - I) / 2) • toC (reV q + imV q) + ((1 + I) / 2) • toC (reV q - imV q)) by
    rw [← hq, ← hs], bilin_comb hd2]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toC_apply, PiLp.add_apply]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

@[tmio T, powerlib_foundation]
theorem bilin_q_q (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (q : Fin n → ℂ) :
    bilinC F 0 q q = toC (Q (reV q + imV q) (reV q - imV q) + Q (reV q - imV q) (reV q + imV q)) +
      I • toC (Q (reV q + imV q) (reV q + imV q) - Q (reV q - imV q) (reV q - imV q)) := by
  have hq := q_eq_comb q
  rw [show bilinC F 0 q q = bilinC F 0
      (((1 + I) / 2) • toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q))
      (((1 + I) / 2) • toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q)) by
    rw [← hq], bilin_comb hd2]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toC_apply, PiLp.add_apply,
    PiLp.sub_apply]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

end FullForms

section Resolvents

variable {n : ℕ} {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ}
  {F : State n → State n} {Q H : State n →L[ℝ] State n →L[ℝ] State n}

/-- The homological equation on a rotation-invariant pair `A v₀ = ω v₁`, `A v₁ = −ω v₀` in
`range P`. -/
@[tmio T, powerlib_foundation]
theorem homological_vectors {P : State n →L[ℝ] State n} (hP : IsCommutingProjection A P)
    (hhom : ∀ u, P u = u → H u (P (A u)) + H (P (A u)) u = (1 - P) (A (H u u)) + (1 - P) (Q u u))
    (hPH : ∀ u v, P (H u v) = 0) {v0 v1 : State n} (h0 : P v0 = v0) (h1 : P v1 = v1)
    (hA0 : A v0 = ω • v1) (hA1 : A v1 = (-ω) • v0) :
    -(A (H v0 v0 + H v1 v1)) = (Q v0 v0 + Q v1 v1) - P (Q v0 v0 + Q v1 v1) ∧
      -((2 * ω) • (H v0 v0 - H v1 v1)) - A (H v0 v1 + H v1 v0) =
        (Q v0 v1 + Q v1 v0) - P (Q v0 v1 + Q v1 v0) ∧
      (2 * ω) • (H v0 v1 + H v1 v0) - A (H v0 v0 - H v1 v1) =
        (Q v0 v0 - Q v1 v1) - P (Q v0 v0 - Q v1 v1) := by
  have E00 := homological_polarized hP hhom hPH h0 h0
  have E11 := homological_polarized hP hhom hPH h1 h1
  have E01 := homological_polarized hP hhom hPH h0 h1
  rw [hA0] at E00 E01
  rw [hA1] at E11 E01
  simp only [map_smul, _root_.smul_apply, compl_apply, map_add] at E00 E11 E01
  simp only [map_add, map_sub]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := module) (-(1 / 2 : ℝ)) • (E00 + E11)
  · linear_combination (norm := module) -E01
  · linear_combination (norm := module) (-(1 / 2 : ℝ)) • (E00 - E11)

@[tmio T, powerlib_foundation]
theorem shift2_mulVec_split (A : State n →L[ℝ] State n) (ω : ℝ) (Y1 Y2 : State n) :
    shift2 (cmat A) ω *ᵥ (toC Y1 + I • toC Y2) =
      toC (-((2 * ω) • Y2) - A Y1) + I • toC ((2 * ω) • Y1 - A Y2) := by
  rw [shift2, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    cmat_mulVec_toC_add_smul]
  ext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toC_apply, PiLp.sub_apply,
    PiLp.neg_apply, PiLp.smul_apply]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- The first resolvent on the complement: `r_s = A⁻¹(1 − P)B(q, q̄) = −(H(v₀, v₀) + H(v₁, v₁))`. -/
@[tmio T, powerlib_foundation] theorem IsCritical.rs_eq (hc : IsCritical A ω q p)
    (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (hhom : ∀ u, critP q p u = u → H u (critP q p (A u)) + H (critP q p (A u)) u =
      (1 - critP q p) (A (H u u)) + (1 - critP q p) (Q u u))
    (hPH : ∀ u v, critP q p (H u v) = 0) (hA : IsUnit (cmat A).det) :
    (cmat A)⁻¹ *ᵥ (bilinC F 0 q (star q) -
        cmapR (critι q) (cmapR (critπ p) (bilinC F 0 q (star q)))) =
      -toC (H (reV q + imV q) (reV q + imV q) + H (reV q - imV q) (reV q - imV q)) := by
  have hv := homological_vectors hc.isCommutingProjection hhom hPH hc.critP_v0 hc.critP_v1
    hc.apply_v0 hc.apply_v1
  rw [bilin_q_starq hd2, cmapR_critP_toC, ← toC_sub]
  have key : cmat A *ᵥ -toC (H (reV q + imV q) (reV q + imV q) +
      H (reV q - imV q) (reV q - imV q)) = toC ((Q (reV q + imV q) (reV q + imV q) +
        Q (reV q - imV q) (reV q - imV q)) - critP q p (Q (reV q + imV q) (reV q + imV q) +
        Q (reV q - imV q) (reV q - imV q))) := by
    rw [Matrix.mulVec_neg, cmat_mulVec_toC, ← toC_neg, hv.1]
  rw [← key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]

/-- The second resolvent on the complement:
`s_s = (2iω − A)⁻¹(1 − P)B(q, q) = H(v₀, v₁) + H(v₁, v₀) + i(H(v₀, v₀) − H(v₁, v₁))`. -/
@[tmio T, powerlib_foundation] theorem IsCritical.ss_eq (hc : IsCritical A ω q p)
    (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (hhom : ∀ u, critP q p u = u → H u (critP q p (A u)) + H (critP q p (A u)) u =
      (1 - critP q p) (A (H u u)) + (1 - critP q p) (Q u u))
    (hPH : ∀ u v, critP q p (H u v) = 0) (h2 : IsUnit (shift2 (cmat A) ω).det) :
    (shift2 (cmat A) ω)⁻¹ *ᵥ (bilinC F 0 q q -
        cmapR (critι q) (cmapR (critπ p) (bilinC F 0 q q))) =
      toC (H (reV q + imV q) (reV q - imV q) + H (reV q - imV q) (reV q + imV q)) +
        I • toC (H (reV q + imV q) (reV q + imV q) - H (reV q - imV q) (reV q - imV q)) := by
  have hv := homological_vectors hc.isCommutingProjection hhom hPH hc.critP_v0 hc.critP_v1
    hc.apply_v0 hc.apply_v1
  rw [bilin_q_q hd2, cmapR_critP_comb]
  have key := shift2_mulVec_split A ω
    (H (reV q + imV q) (reV q - imV q) + H (reV q - imV q) (reV q + imV q))
    (H (reV q + imV q) (reV q + imV q) - H (reV q - imV q) (reV q - imV q))
  rw [hv.2.1, hv.2.2] at key
  have e : toC (Q (reV q + imV q) (reV q - imV q) + Q (reV q - imV q) (reV q + imV q)) +
      I • toC (Q (reV q + imV q) (reV q + imV q) - Q (reV q - imV q) (reV q - imV q)) -
      (toC (critP q p (Q (reV q + imV q) (reV q - imV q) + Q (reV q - imV q) (reV q + imV q))) +
        I • toC (critP q p (Q (reV q + imV q) (reV q + imV q) -
          Q (reV q - imV q) (reV q - imV q)))) =
      toC ((Q (reV q + imV q) (reV q - imV q) + Q (reV q - imV q) (reV q + imV q)) -
        critP q p (Q (reV q + imV q) (reV q - imV q) + Q (reV q - imV q) (reV q + imV q))) +
      I • toC ((Q (reV q + imV q) (reV q + imV q) - Q (reV q - imV q) (reV q - imV q)) -
        critP q p (Q (reV q + imV q) (reV q + imV q) - Q (reV q - imV q) (reV q - imV q))) := by
    simp only [toC_sub, smul_sub]; abel
  rw [e, ← key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h2, Matrix.one_mulVec]

end Resolvents

section CubicAlgebra

variable {n : ℕ}

/-- The cubic identity behind the projection formula: the symmetrized cubic part of the reduced
field, `Q(u, H(w, z)) + Q(H(u, w), z)` over the six orders, read at `(q, q, q̄)` with
`q = c₀ v₀ + c₁ v₁`, equals the two complement corrections of Kuznetsov's formula. -/
@[tmio T, powerlib_foundation]
theorem cubic_identity (Λ : State n →ₗ[ℝ] ℂ) (Q H : State n →L[ℝ] State n →L[ℝ] State n)
    (v0 v1 : State n) :
    (1 + I) / 2 * ((1 + I) / 2) * ((1 - I) / 2) * Λ (sym6 (triQH Q H) v0 v0 v0) +
      (1 + I) / 2 * ((1 + I) / 2) * ((1 + I) / 2) * Λ (sym6 (triQH Q H) v0 v0 v1) +
      (1 + I) / 2 * ((1 - I) / 2) * ((1 - I) / 2) * Λ (sym6 (triQH Q H) v0 v1 v0) +
      (1 + I) / 2 * ((1 - I) / 2) * ((1 + I) / 2) * Λ (sym6 (triQH Q H) v0 v1 v1) +
      ((1 - I) / 2 * ((1 + I) / 2) * ((1 - I) / 2) * Λ (sym6 (triQH Q H) v1 v0 v0) +
      (1 - I) / 2 * ((1 + I) / 2) * ((1 + I) / 2) * Λ (sym6 (triQH Q H) v1 v0 v1) +
      ((1 - I) / 2 * ((1 - I) / 2) * ((1 - I) / 2) * Λ (sym6 (triQH Q H) v1 v1 v0) +
      (1 - I) / 2 * ((1 - I) / 2) * ((1 + I) / 2) * Λ (sym6 (triQH Q H) v1 v1 v1))) =
    -(2 * -((1 + I) / 2 * Λ (Q v0 (H v0 v0 + H v1 v1) + Q (H v0 v0 + H v1 v1) v0) +
        (1 - I) / 2 * Λ (Q v1 (H v0 v0 + H v1 v1) + Q (H v0 v0 + H v1 v1) v1))) +
      ((1 - I) / 2 * Λ (Q v0 (H v0 v1 + H v1 v0) + Q (H v0 v1 + H v1 v0) v0) +
        (1 + I) / 2 * Λ (Q v1 (H v0 v1 + H v1 v0) + Q (H v0 v1 + H v1 v0) v1) +
        I * ((1 - I) / 2 * Λ (Q v0 (H v0 v0 - H v1 v1) + Q (H v0 v0 - H v1 v1) v0) +
          (1 + I) / 2 * Λ (Q v1 (H v0 v0 - H v1 v1) + Q (H v0 v0 - H v1 v1) v1))) := by
  simp only [sym6, triQH_apply, map_add, map_sub, _root_.add_apply, _root_.sub_apply]
  ring_nf
  simp only [I_sq, I_pow_three]
  ring

end CubicAlgebra

section TransportData

variable {n : ℕ} {F : State n → State n} {Q H : State n →L[ℝ] State n →L[ℝ] State n}

@[tmio T, powerlib_foundation]
theorem cbiOf_toC_basis {m k : ℕ} (c : Fin m → Fin m → Fin k → ℝ) (i j : Fin m) :
    cbiOf c (toC (basisVec i)) (toC (basisVec j)) = fun l => (c i j l : ℂ) := by
  ext l
  rw [cbiOf_apply, toC_basisVec, toC_basisVec]
  simp [Pi.single_apply]

/-- The reduced bilinear form is the full one read through the chart. -/
@[tmio T, powerlib_foundation]
theorem redB_eq (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (q p : Fin n → ℂ) (u w : Fin 2 → ℂ) :
    redB q p Q u w = cmapR (critπ p) (bilinC F 0 (cmapR (critι q) u) (cmapR (critι q) w)) := by
  have h : redB q p Q =
      ((bilinC F 0).compl₁₂ (cmapR (critι q)) (cmapR (critι q))).compr₂ (cmapR (critπ p)) := by
    refine clin_ext fun i => clin_ext fun j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, cmapR_toC, bilinC_toC, hd2]
    rw [redB, cbiOf_toC_basis]
    ext l
    simp [redQ_apply, toC_apply]
  rw [h]
  simp

/-- The real-linear functional `x ↦ ⟨p, x⟩` on real vectors. -/
def realPairing (p : Fin n → ℂ) : State n →ₗ[ℝ] ℂ where
  toFun x := pairing p (toC x)
  map_add' x y := by rw [toC_add, map_add]
  map_smul' r x := by
    rw [toC_smul, map_smul, smul_eq_mul, RingHom.id_apply, Complex.real_smul]

@[tmio T, powerlib_foundation] theorem realPairing_apply (p : Fin n → ℂ) (x : State n) :
    realPairing p x = pairing p (toC x) := rfl

end TransportData

section CubicGlue

open Degenerate.PlanarFocus

variable {n : ℕ} {F : State n → State n} {Q H : State n →L[ℝ] State n →L[ℝ] State n}
  {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)}

@[tmio T, powerlib_foundation] theorem pairing_critVec_toC_critπ (p : Fin n → ℂ) (X : State n) :
    pairing critVec (toC (critπ p X)) = realPairing p X := by
  rw [← cmapR_toC, pairing_critVec_cmapR_critπ, realPairing_apply]

@[tmio T, powerlib_foundation] theorem sym6_redC (q p : Fin n → ℂ) (x y z : State 2) :
    sym6 (redC q p Q H C) x y z =
      critπ p (sym6 (triQH Q H + C) (critι q x) (critι q y) (critι q z)) := by
  have e : ∀ a b c : State 2, (fun i => critι q (![a, b, c] i)) =
      ![critι q a, critι q b, critι q c] := by
    intro a b c; funext i; fin_cases i <;> rfl
  simp only [sym6, redC, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_add, e]

@[tmio T, powerlib_foundation] theorem pairing_redT (q p : Fin n → ℂ) (u w z : Fin 2 → ℂ) :
    pairing critVec (redT q p Q H C u w z) =
      ∑ i, ∑ j, ∑ l, u i * w j * z l * realPairing p
        (sym6 (triQH Q H + C) (critι q (basisVec i)) (critι q (basisVec j))
          (critι q (basisVec l))) := by
  simp only [← pairing_critVec_toC_critπ, ← sym6_redC]
  rw [redT]
  simp only [pairing_apply, ctriOf_apply, Fin.sum_univ_two, toC_apply]
  ring

@[tmio T, powerlib_foundation]
theorem sym6_add (T T' : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n))
    (x y z : State n) : sym6 (T + T') x y z = sym6 T x y z + sym6 T' x y z := by
  simp only [sym6, _root_.add_apply]; abel

@[tmio T, powerlib_foundation] theorem pairing_tri_comb
    (hd3 : ∀ u w z, iteratedFDeriv ℝ 3 F 0 ![u, w, z] = C ![u, w, z] + C ![u, z, w] +
      C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u])
    (p : Fin n → ℂ) (a b c d e g : ℂ) (x y : State n) :
    pairing p (trilinC F 0 (a • toC x + b • toC y) (c • toC x + d • toC y)
        (e • toC x + g • toC y)) =
      a * c * e * realPairing p (sym6 C x x x) + a * c * g * realPairing p (sym6 C x x y) +
      a * d * e * realPairing p (sym6 C x y x) + a * d * g * realPairing p (sym6 C x y y) +
      b * c * e * realPairing p (sym6 C y x x) + b * c * g * realPairing p (sym6 C y x y) +
      b * d * e * realPairing p (sym6 C y y x) + b * d * g * realPairing p (sym6 C y y y) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, trilinC_toC, hd3,
    smul_eq_mul, realPairing_apply, sym6, toC_add]
  ring

@[tmio T, powerlib_foundation]
theorem pairing_bilin_toC (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (p : Fin n → ℂ) (a b : ℂ) (x y Y : State n) :
    pairing p (bilinC F 0 (a • toC x + b • toC y) (toC Y)) =
      a * realPairing p (Q x Y + Q Y x) + b * realPairing p (Q y Y + Q Y y) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, bilinC_toC, hd2,
    smul_eq_mul, realPairing_apply, toC_add]

end CubicGlue

section Bridge

open Degenerate.PlanarFocus

variable {n : ℕ} {A : State n →L[ℝ] State n} {ω : ℝ} {q p : Fin n → ℂ}
  {F : State n → State n} {Q H : State n →L[ℝ] State n →L[ℝ] State n}
  {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)}

@[tmio T, powerlib_foundation] theorem rotC_det_isUnit (hω : ω ≠ 0) : IsUnit (rotC ω).det := by
  have : (rotC ω).det = (ω : ℂ) ^ 2 := by simp [rotC, Matrix.det_fin_two]; ring
  rw [this]; exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (by exact_mod_cast hω))

@[tmio T, powerlib_foundation]
theorem shift2_rotC_det_isUnit (hω : ω ≠ 0) : IsUnit (shift2 (rotC ω) ω).det := by
  have : (shift2 (rotC ω) ω).det = -3 * (ω : ℂ) ^ 2 := by
    simp [shift2, rotC, Matrix.det_fin_two]; ring_nf; simp [Complex.I_sq]; ring
  rw [this]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast hω)))

@[tmio T, powerlib_foundation]
theorem IsCritical.inv_cmapR (hc : IsCritical A ω q p) (hA : IsUnit (cmat A).det)
    (z : Fin 2 → ℂ) : (cmat A)⁻¹ *ᵥ cmapR (critι q) z = cmapR (critι q) ((rotC ω)⁻¹ *ᵥ z) := by
  have h : cmat A *ᵥ cmapR (critι q) ((rotC ω)⁻¹ *ᵥ z) = cmapR (critι q) z := by
    rw [hc.cmat_cmapR_critι, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (rotC_det_isUnit hc.freq_pos.ne'), Matrix.one_mulVec]
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]

@[tmio T, powerlib_foundation]
theorem IsCritical.shift2_cmapR (hc : IsCritical A ω q p) (y : Fin 2 → ℂ) :
    shift2 (cmat A) ω *ᵥ cmapR (critι q) y = cmapR (critι q) (shift2 (rotC ω) ω *ᵥ y) := by
  rw [shift2, shift2, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, hc.cmat_cmapR_critι, map_sub,
    map_smul]

@[tmio T, powerlib_foundation] theorem IsCritical.inv_shift2_cmapR (hc : IsCritical A ω q p)
    (h2 : IsUnit (shift2 (cmat A) ω).det) (z : Fin 2 → ℂ) :
    (shift2 (cmat A) ω)⁻¹ *ᵥ cmapR (critι q) z =
      cmapR (critι q) ((shift2 (rotC ω) ω)⁻¹ *ᵥ z) := by
  have h : shift2 (cmat A) ω *ᵥ cmapR (critι q) ((shift2 (rotC ω) ω)⁻¹ *ᵥ z) =
      cmapR (critι q) z := by
    rw [hc.shift2_cmapR, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (shift2_rotC_det_isUnit hc.freq_pos.ne'), Matrix.one_mulVec]
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h2, Matrix.one_mulVec]

/-- **Kuznetsov's projection formula is the planar formula of the reduced field.** For a
critical pair `(q, p)` of `A = DF(0)` (`A q = iωq`, `Aᵀp = −iωp`, `⟨p, q⟩ = 1`), with
`D²F(0)(u, w) = Q(u, w) + Q(w, u)`, `D³F(0)` the six orders of `C`, `A` and `2iω − A`
invertible, and `H` (values in `ker P`) solving the homological equation for the spectral
projection `P = ι π` of the critical chart, the planar first Lyapunov coefficient of the reduced
linear, quadratic and cubic parts (`rotL ω`, `redQ`, `redC`) equals
`firstLyapunov F 0 ω q p`. -/
@[tmio T, powerlib_foundation]
theorem IsCritical.l1_reduced_eq_firstLyapunov (hc : IsCritical A ω q p)
    (hdA : fderiv ℝ F 0 = A)
    (hd2 : ∀ u w, iteratedFDeriv ℝ 2 F 0 ![u, w] = Q u w + Q w u)
    (hd3 : ∀ u w z, iteratedFDeriv ℝ 3 F 0 ![u, w, z] = C ![u, w, z] + C ![u, z, w] +
      C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u])
    (hA : IsUnit (cmat A).det) (h2 : IsUnit (shift2 (cmat A) ω).det)
    (hhom : ∀ u, critP q p u = u → H u (critP q p (A u)) + H (critP q p (A u)) u =
      (1 - critP q p) (A (H u u)) + (1 - critP q p) (Q u u))
    (hPH : ∀ u v, critP q p (H u v) = 0) :
    l1 (rotL ω) (redQ q p Q) (redC q p Q H C) ω = firstLyapunov F 0 ω q p := by
  have hω := hc.freq_pos.ne'
  rw [l1, ← lyap1_rot _ hc.freq_pos (redB q p Q) (redT q p Q H C) (redB_jet hω q p Q H C)
    (redT_jet hω q p Q H C)]
  have hq : cmapR (critι q) critVec = q := cmapR_critι_critVec q
  have hqs : cmapR (critι q) (star critVec) = star q := cmapR_critι_star q
  have hB := redB_eq (Q := Q) hd2 q p
  have hr : ((cmat A)⁻¹).mulVecLin (bilinC F 0 (cmapR (critι q) critVec)
        (cmapR (critι q) (star critVec))) =
      cmapR (critι q) (((rotC ω)⁻¹).mulVecLin (redB q p Q critVec (star critVec))) +
        (cmat A)⁻¹ *ᵥ (bilinC F 0 q (star q) -
          cmapR (critι q) (cmapR (critπ p) (bilinC F 0 q (star q)))) := by
    rw [hB, hq, hqs, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, ← hc.inv_cmapR hA,
      Matrix.mulVec_sub]
    abel
  have hs : ((shift2 (cmat A) ω)⁻¹).mulVecLin (bilinC F 0 (cmapR (critι q) critVec)
        (cmapR (critι q) critVec)) =
      cmapR (critι q) (((shift2 (rotC ω) ω)⁻¹).mulVecLin (redB q p Q critVec critVec)) +
        (shift2 (cmat A) ω)⁻¹ *ᵥ (bilinC F 0 q q -
          cmapR (critι q) (cmapR (critπ p) (bilinC F 0 q q))) := by
    rw [hB, hq, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, ← hc.inv_shift2_cmapR h2,
      Matrix.mulVec_sub]
    abel
  have hrs := hc.rs_eq hd2 hhom hPH hA
  have hss := hc.ss_eq hd2 hhom hPH h2
  have hC : pairing critVec (redT q p Q H C critVec critVec (star critVec)) =
      pairing p (trilinC F 0 (cmapR (critι q) critVec) (cmapR (critι q) critVec)
        (cmapR (critι q) (star critVec))) -
        2 * pairing p (bilinC F 0 (cmapR (critι q) critVec) ((cmat A)⁻¹ *ᵥ
          (bilinC F 0 q (star q) - cmapR (critι q) (cmapR (critπ p) (bilinC F 0 q (star q)))))) +
        pairing p (bilinC F 0 (cmapR (critι q) (star critVec)) ((shift2 (cmat A) ω)⁻¹ *ᵥ
          (bilinC F 0 q q - cmapR (critι q) (cmapR (critπ p) (bilinC F 0 q q))))) := by
    rw [hq, hqs, hrs, hss, pairing_redT]
    have e3 : trilinC F 0 q q (star q) = trilinC F 0
        (((1 + I) / 2) • toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q))
        (((1 + I) / 2) • toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q))
        (((1 - I) / 2) • toC (reV q + imV q) + ((1 + I) / 2) • toC (reV q - imV q)) := by
      rw [← q_eq_comb, ← star_q_eq_comb]
    have e2 : bilinC F 0 q = bilinC F 0
        (((1 + I) / 2) • toC (reV q + imV q) + ((1 - I) / 2) • toC (reV q - imV q)) := by
      rw [← q_eq_comb]
    have e2s : bilinC F 0 (star q) = bilinC F 0
        (((1 - I) / 2) • toC (reV q + imV q) + ((1 + I) / 2) • toC (reV q - imV q)) := by
      rw [← star_q_eq_comb]
    rw [e3, e2, e2s]
    simp only [star_critVec]
    simp only [Fin.sum_univ_two, critι_e0, critι_e1, critVec, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    generalize reV q + imV q = v0
    generalize reV q - imV q = v1
    rw [pairing_tri_comb hd3,
      (bilinC F 0 (((1 + I) / 2) • toC v0 + ((1 - I) / 2) • toC v1)).map_neg,
      (pairing p).map_neg, pairing_bilin_toC hd2,
      (bilinC F 0 (((1 - I) / 2) • toC v0 + ((1 + I) / 2) • toC v1)).map_add,
      (bilinC F 0 (((1 - I) / 2) • toC v0 + ((1 + I) / 2) • toC v1)).map_smul,
      (pairing p).map_add, (pairing p).map_smul, pairing_bilin_toC hd2,
      pairing_bilin_toC hd2, smul_eq_mul]
    have cub := cubic_identity (realPairing p) Q H v0 v1
    simp only [sym6_add, map_add, map_sub, _root_.add_apply, _root_.sub_apply] at cub ⊢
    linear_combination cub
  have ht := lyap1_transport (bilinC F 0) (trilinC F 0) ((cmat A)⁻¹.mulVecLin)
    ((shift2 (cmat A) ω)⁻¹.mulVecLin) (pairing p) (redB q p Q) (redT q p Q H C)
    ((rotC ω)⁻¹.mulVecLin) ((shift2 (rotC ω) ω)⁻¹.mulVecLin) (pairing critVec)
    (cmapR (critι q)) (cmapR (critπ p)) ω critVec (star critVec) _ _
    (pairing_critVec_cmapR_critπ p) hB hr hs hC
  rw [hq, hqs] at ht
  rw [ht, firstLyapunov, jacobianC, hdA]

end Bridge

end powerlib.Dynamics.CenterManifold
