import theorem.ParametricResonance.SlowFlow
import theorem.Modal.Sensitivity
import theorem.Modal.Splitting

/-! # Element-wise decomposition of the first-order 2:1 pump coefficient

Exact matrix identities behind the element-wise reading `g_m = Σ Γ_ik` of the first-order 2:1
pump coefficient, the three structural lemmas (constant element, proportional modulation, pure
rotation), and the canonical threshold law `ε_crit = 4 (σ_m/Ω_m)/ĝ_m` inside the first-order slow
flow. No converter model is fixed here.

Scope.
* A complex square state matrix `A₀ : Matrix (Fin n) (Fin n) ℂ` (for a real Jacobian,
  `Linear.complexify A`), a right eigenvector `r` (`A₀ r = λ r`) and a left eigenvector written as
  a row `u` (`u A₀ = λ u`, `u ⬝ᵥ r = 1`). The source writes the left eigenvector as `l_mᴴ`; here
  `u = l_mᴴ`, so the source's `l*_{m,i}` is `u i`.
* A complex modulation matrix `A₁`; the pump coefficient is `g = u A₁ r̄` (`pump`), the element
  weight `w_ik = u_i (A₀)_ik r_k` (`weight`), the element contribution
  `Γ_ik = u_i (A₁)_ik r̄_k` (`contribution`) and the relative modulation
  `ρ_ik = (A₁)_ik/(A₀)_ik` (`ratio`).
* The passage from a converter model to `A₀`, `A₁` (forced orbit, `A₁ = Σ_l ∂A/∂x_l z_l + G û`)
  is represented only generically (`modulation`: the entrywise derivative of a real
  matrix-valued map along a complex direction). The passage from the periodic variational
  equation to the first-order slow flow is formalized for two states in
  `theorem/ParametricResonance/TwoToOneAveraging.lean` (`averaging_stable`,
  `averaging_unstable`: for small `ε` the Floquet stability is that of the slow flow with pump
  `g/2`, `g = pump A₁ u r`); for more states (projection on the mode and elimination of the other
  modes) it is **not** formalized, and the threshold statements here hold inside the slow flow of
  `theorem/ParametricResonance/SlowFlow.lean`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.2 (2:1 criterion), §2.3 (element decomposition (5)), §2.4
(Lemmas 1–3, (6)), §2.5 (canonical threshold law (7) and the damped Mathieu check).

Results.
* Decomposition (5): `sum_weight`, `sum_weight_eq` (`Σ_ik w_ik = λ` for `u ⬝ᵥ r = 1`),
  `sum_contribution` (`Σ_ik Γ_ik = g`), `contribution_eq` (`Γ_ik = ρ_ik (r̄_k/r_k) w_ik` when
  `(A₀)_ik ≠ 0`, `r_k ≠ 0`), `norm_contribution` (`|Γ_ik| = |ρ_ik| |w_ik|`).
* `weight_eq_logDeriv` — `w_ik = ∂λ/∂ln (A₀)_ik`: along a differentiable eigen-branch of the
  family that scales the entry `(i, k)` by `e^s` (`scaleEntry`), `λ'(0) (u ⬝ᵥ r) = w_ik`
  (`Modal.eigenvalue_deriv_left_of_eventually`).
* Coordinate independence: `pump_similar` — under a real invertible change of coordinates
  `x ↦ P x` (`A₁ ↦ P A₁ P⁻¹`, `r ↦ P r`, `u ↦ u P⁻¹`) the pump coefficient is unchanged, while
  single contributions `Γ_ik` are not invariant in general (source §2.3). `pump_rescale`,
  `norm_pump_rescale` — rescaling the eigenvectors `r ↦ c r`, `u ↦ c⁻¹ u` (the normalization
  `u ⬝ᵥ r = 1` is kept) multiplies `g` by the unimodular `c̄/c`: the phase of `g` is a convention
  (eigenvector phase, pump time origin), its modulus `|g|` is not.
* Lemma 1: `modulation_eq_zero_of_const`, `contribution_modulation_eq_zero_of_const` — an entry
  of the Jacobian that does not depend on state and input has `(A₁)_ik = 0`, hence `Γ_ik = 0`.
* Lemma 2: `dotProduct_star_eq_zero` — for a real `A₀` and a non-real eigenvalue
  (`Im λ ≠ 0`), `u ⬝ᵥ r̄ = 0`; hence `pump_smul_eq_zero`: `A₁ = c A₀` gives `g = 0`.
  `exists_pump_smul_ne_zero` shows the premise `Im λ ≠ 0` cannot be dropped (a real eigenvalue
  with `A₁ = A₀` has `g = λ ≠ 0`); the source's proof uses it implicitly.
* Lemma 3: `pump_commutator` — `A₁ = z [J, A₀]` (any complex `J`, real `A₀`) gives
  `g = z (λ̄ − λ) (u ⬝ᵥ J r̄)`; `pump_commutator_eq` — for `λ = −σ + jΩ`,
  `g = −2jΩ z (u ⬝ᵥ J r̄)` (6). No symmetry of `J` is needed.
* Canonical threshold law (7), inside the first-order slow flow at exact 2:1 tuning (`Δ = 0`):
  with `ĝ = 2|g|/Ω` (`normalizedPump`), the slow flow with pump `ε g/2` is exponentially stable iff
  `ε ĝ < 4 σ/Ω` (`canonical_threshold_iff`), i.e. iff `ε < 4 (σ/Ω)/ĝ` for `g ≠ 0`
  (`canonical_threshold_iff'`); both are `slowFlow_threshold_iff` at `Δ = 0`.
* Damped Mathieu check: for `ẍ + 2σẋ + Ω²[1 + εh cos ω_p t] x = 0` (`mathieuA₀`, `mathieuA₁`)
  with `0 < Ω_m`, `Ω_m² = Ω² − σ²`, the eigenpairs (`mathieu_right`, `mathieu_left`,
  `mathieu_normalized`) give `g = jΩ²h/(2Ω_m)` (`mathieu_pump`) and
  `ĝ = |h| Ω²/(Ω² − σ²)` (`mathieu_normalizedPump`).

Corrections.
* §2.5 states `ĝ_m = |h|` for the damped Mathieu equation. With the mode frequency
  `Ω_m = √(Ω² − σ²)` of the source's own definition `ĝ_m = 2|g_m|/Ω_m`, the exact value is
  `ĝ_m = |h| Ω²/(Ω² − σ²)`; it equals `|h|` iff `σ = 0` or `h = 0`
  (`mathieu_normalizedPump_eq_abs_iff`). The relative difference `σ²/(Ω² − σ²)` is second order in
  `σ/Ω`, so `εh_crit = 4σ/Ω` holds to first order only.
* §2.4 Lemma 2 needs `Ω_m ≠ 0` (`exists_pump_smul_ne_zero`).
-/

noncomputable section
namespace powerlib.ParametricResonance.Element

open Matrix Complex Filter Topology ComplexConjugate

variable {n : ℕ}

/-! ## The element decomposition -/

/-- Element weight `w_ik = u_i (A₀)_ik r_k` (`u` the left eigenvector as a row). -/
def weight (A : Matrix (Fin n) (Fin n) ℂ) (u r : Fin n → ℂ) (i k : Fin n) : ℂ :=
  u i * A i k * r k

/-- First-order 2:1 pump coefficient `g = u A₁ r̄`. -/
def pump (A₁ : Matrix (Fin n) (Fin n) ℂ) (u r : Fin n → ℂ) : ℂ :=
  u ⬝ᵥ (A₁ *ᵥ star r)

/-- Element contribution `Γ_ik = u_i (A₁)_ik r̄_k`. -/
def contribution (A₁ : Matrix (Fin n) (Fin n) ℂ) (u r : Fin n → ℂ) (i k : Fin n) : ℂ :=
  u i * A₁ i k * star (r k)

/-- Relative modulation `ρ_ik = (A₁)_ik / (A₀)_ik`. -/
def ratio (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) : ℂ :=
  A₁ i k / A₀ i k

@[tmio T, powerlib_foundation] theorem sum_weight (A : Matrix (Fin n) (Fin n) ℂ)
    (u r : Fin n → ℂ) :
    ∑ i, ∑ k, weight A u r i k = u ⬝ᵥ (A *ᵥ r) := by
  simp only [weight, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- The weights of a normalized eigentriple sum to the eigenvalue. -/
@[tmio T, powerlib_foundation] theorem sum_weight_eq {A : Matrix (Fin n) (Fin n) ℂ}
    {u r : Fin n → ℂ} {lam : ℂ} (hr : A *ᵥ r = lam • r) (hn : u ⬝ᵥ r = 1) :
    ∑ i, ∑ k, weight A u r i k = lam := by
  rw [sum_weight, hr, dotProduct_smul, hn, smul_eq_mul, mul_one]

@[tmio T, powerlib_foundation] theorem sum_contribution (A₁ : Matrix (Fin n) (Fin n) ℂ)
    (u r : Fin n → ℂ) :
    ∑ i, ∑ k, contribution A₁ u r i k = pump A₁ u r := by
  simp only [contribution, pump, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- `Γ_ik = ρ_ik (r̄_k / r_k) w_ik` (source (5)). -/
@[tmio T, powerlib_foundation] theorem contribution_eq (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (u r : Fin n → ℂ) {i k : Fin n} (hA : A₀ i k ≠ 0) (hr : r k ≠ 0) :
    contribution A₁ u r i k = ratio A₀ A₁ i k * (star (r k) / r k) * weight A₀ u r i k := by
  simp only [contribution, ratio, weight]
  field_simp

/-- `|Γ_ik| = |ρ_ik| |w_ik|`. -/
@[tmio T, powerlib_foundation] theorem norm_contribution (A₀ A₁ : Matrix (Fin n) (Fin n) ℂ)
    (u r : Fin n → ℂ) {i k : Fin n} (hA : A₀ i k ≠ 0) :
    ‖contribution A₁ u r i k‖ = ‖ratio A₀ A₁ i k‖ * ‖weight A₀ u r i k‖ := by
  have hA' : ‖A₀ i k‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  simp only [contribution, ratio, weight, norm_mul, norm_div, norm_star]
  field_simp

/-! ## The weight as a logarithmic eigenvalue sensitivity -/

/-- The matrix `A` with its entry `(i, k)` scaled by `e^s`. -/
def scaleEntry (A : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a = i ∧ b = k then (Real.exp s : ℂ) * A a b else A a b

@[tmio T, powerlib_foundation] theorem scaleEntry_zero (A : Matrix (Fin n) (Fin n) ℂ)
    (i k : Fin n) : scaleEntry A i k 0 = A := by
  funext a b
  simp [scaleEntry]

@[tmio T, powerlib_foundation] theorem hasDerivAt_scaleEntry (A : Matrix (Fin n) (Fin n) ℂ)
    (i k a b : Fin n) :
    HasDerivAt (fun s => scaleEntry A i k s a b) (if a = i ∧ b = k then A a b else 0) 0 := by
  by_cases h : a = i ∧ b = k
  · obtain ⟨rfl, rfl⟩ := h
    simp only [scaleEntry, and_self, ite_true]
    have := ((Real.hasDerivAt_exp 0).ofReal_comp).mul_const (A a b)
    simpa using this
  · simp only [scaleEntry, h, ite_false]
    exact hasDerivAt_const _ _

/-- `w_ik = ∂λ/∂ln (A₀)_ik`: along a differentiable eigen-branch `(λ(s), v(s))` of the family that
scales the entry `(i, k)` by `e^s`, `λ'(0) (u ⬝ᵥ v(0)) = w_ik`. -/
@[tmio T, powerlib_foundation] theorem weight_eq_logDeriv {A : Matrix (Fin n) (Fin n) ℂ}
    {i k : Fin n} {v : ℝ → Fin n → ℂ} {v' : Fin n → ℂ} {lam : ℝ → ℂ} {lam' : ℂ}
    (hv : ∀ j, HasDerivAt (fun s => v s j) (v' j) 0) (hlam : HasDerivAt lam lam' 0)
    (heig : ∀ᶠ s in 𝓝 0, scaleEntry A i k s *ᵥ v s = lam s • v s) {u : Fin n → ℂ}
    (hu : vecMul u A = lam 0 • u) :
    lam' * (u ⬝ᵥ v 0) = weight A u (v 0) i k := by
  have h := Modal.eigenvalue_deriv_left_of_eventually
    (A' := fun a b => if a = i ∧ b = k then A a b else 0)
    (fun a b => hasDerivAt_scaleEntry A i k a b) hv hlam heig
    (u := u) (by rw [scaleEntry_zero]; exact hu)
  rw [h]
  simp only [dotProduct, mulVec]
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp),
    Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp [weight, mul_assoc]

/-! ## Coordinate independence of the pump coefficient -/

/-- The pump coefficient does not depend on real linear coordinates: `g` of `(P A₁ P⁻¹, u P⁻¹, P r)`
equals `g` of `(A₁, u, r)`. -/
@[tmio T, powerlib_foundation] theorem pump_similar {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P)
    (A₁ : Matrix (Fin n) (Fin n) ℂ) (u r : Fin n → ℂ) :
    pump (Linear.complexify P * A₁ * Linear.complexify P⁻¹) (vecMul u (Linear.complexify P⁻¹))
        (Linear.complexify P *ᵥ r) = pump A₁ u r := by
  have hinv : Linear.complexify P⁻¹ * Linear.complexify P = 1 := by
    rw [Linear.complexify, Linear.complexify, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).mp hP)]
    simp
  rw [pump, pump, ← Modal.complexify_mulVec_star, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hinv, Matrix.mul_one,
    ← Matrix.mul_assoc, hinv, Matrix.one_mul]

/-- Rescaling the eigenvectors (`r ↦ c r`, `u ↦ c⁻¹ u`) multiplies `g` by `c̄/c`. -/
@[tmio T, powerlib_foundation] theorem pump_rescale (A₁ : Matrix (Fin n) (Fin n) ℂ)
    (u r : Fin n → ℂ) (c : ℂ) :
    pump A₁ (c⁻¹ • u) (c • r) = (starRingEnd ℂ) c / c * pump A₁ u r := by
  rw [pump, pump, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul]
  rw [show star c = (starRingEnd ℂ) c from rfl]
  ring

/-- The modulus of `g` does not depend on the eigenvector phase (`c ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem norm_pump_rescale (A₁ : Matrix (Fin n) (Fin n) ℂ)
    (u r : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    ‖pump A₁ (c⁻¹ • u) (c • r)‖ = ‖pump A₁ u r‖ := by
  rw [pump_rescale, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hc),
    one_mul]

/-! ## Lemma 1: constant elements are not modulated -/

/-- Entrywise first-order modulation `A₁ = DA(p)[Re d] + j DA(p)[Im d]` of a real matrix-valued
map along the complex direction `d = d_r + j d_i` (source (3): `A₁ = Σ_l ∂A/∂x_l z_l + G û`, with
`p = (x₀, u₀)` and `d = (z⁽¹⁾, û)`). -/
def modulation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Matrix (Fin n) (Fin n) ℝ) (p dr di : E) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => (fderiv ℝ (fun q => A q a b) p dr : ℂ) + I * (fderiv ℝ (fun q => A q a b) p di : ℂ)

/-- Lemma 1: an entry that does not depend on state and input is not modulated. -/
@[tmio T, powerlib_foundation] theorem modulation_eq_zero_of_const {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → Matrix (Fin n) (Fin n) ℝ} {i k : Fin n}
    {c : ℝ} (hc : ∀ q, A q i k = c) (p dr di : E) :
    modulation A p dr di i k = 0 := by
  have : (fun q => A q i k) = fun _ => c := funext hc
  simp [modulation, this]

/-- Lemma 1: a constant element contributes nothing to the pump coefficient. -/
@[tmio T, powerlib_foundation] theorem contribution_modulation_eq_zero_of_const {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → Matrix (Fin n) (Fin n) ℝ} {i k : Fin n}
    {c : ℝ} (hc : ∀ q, A q i k = c) (p dr di : E) (u r : Fin n → ℂ) :
    contribution (modulation A p dr di) u r i k = 0 := by
  simp [contribution, modulation_eq_zero_of_const hc]

/-! ## Lemma 2: proportional modulation -/

/-- For a real state matrix and a non-real eigenvalue, the left eigenvector of `λ` annihilates the
right eigenvector of `λ̄`: `u ⬝ᵥ r̄ = 0`. -/
@[tmio T, powerlib_foundation] theorem dotProduct_star_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    {lam : ℂ} {u r : Fin n → ℂ} (hr : Linear.complexify A *ᵥ r = lam • r)
    (hu : vecMul u (Linear.complexify A) = lam • u) (hlam : lam.im ≠ 0) :
    u ⬝ᵥ star r = 0 := by
  have h1 : u ⬝ᵥ (Linear.complexify A *ᵥ star r) = conj lam * (u ⬝ᵥ star r) := by
    rw [Modal.complexify_mulVec_star, hr, star_smul, dotProduct_smul, smul_eq_mul]
    rfl
  have h2 : u ⬝ᵥ (Linear.complexify A *ᵥ star r) = lam * (u ⬝ᵥ star r) := by
    rw [dotProduct_mulVec, hu, smul_dotProduct, smul_eq_mul]
  have h3 : (lam - conj lam) * (u ⬝ᵥ star r) = 0 := by linear_combination h1 - h2
  have h4 : lam - conj lam ≠ 0 := by
    rw [Complex.sub_conj]
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero two_ne_zero hlam) I_ne_zero
  exact (mul_eq_zero.mp h3).resolve_left h4

/-- Lemma 2: `A₁ = c A₀` (real `A₀`, non-real eigenvalue) gives `g = 0`. -/
@[tmio T, powerlib_foundation] theorem pump_smul_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    {lam : ℂ} {u r : Fin n → ℂ} (hr : Linear.complexify A *ᵥ r = lam • r)
    (hu : vecMul u (Linear.complexify A) = lam • u) (hlam : lam.im ≠ 0) (c : ℂ) :
    pump (c • Linear.complexify A) u r = 0 := by
  rw [pump, smul_mulVec, dotProduct_smul, dotProduct_mulVec, hu, smul_dotProduct,
    dotProduct_star_eq_zero hr hu hlam]
  simp

/-- Lemma 2 needs a non-real eigenvalue: for `A₀ = [1]`, `λ = 1`, `A₁ = A₀`, `g = 1 ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem exists_pump_smul_ne_zero :
    ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (u r : Fin 1 → ℂ) (lam c : ℂ),
      Linear.complexify A *ᵥ r = lam • r ∧ vecMul u (Linear.complexify A) = lam • u ∧
        u ⬝ᵥ r = 1 ∧ lam.im = 0 ∧ pump (c • Linear.complexify A) u r ≠ 0 := by
  refine ⟨1, fun _ => 1, fun _ => 1, 1, 1, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [pump, dotProduct, mulVec, Linear.complexify]

/-! ## Lemma 3: pure rotation -/

/-- Lemma 3: `A₁ = z [J, A₀]` gives `g = z (λ̄ − λ) (u ⬝ᵥ J r̄)`. -/
@[tmio T, powerlib_foundation] theorem pump_commutator {A : Matrix (Fin n) (Fin n) ℝ}
    {lam : ℂ} {u r : Fin n → ℂ} (hr : Linear.complexify A *ᵥ r = lam • r)
    (hu : vecMul u (Linear.complexify A) = lam • u) (J : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    pump (z • (J * Linear.complexify A - Linear.complexify A * J)) u r =
      z * (conj lam - lam) * (u ⬝ᵥ (J *ᵥ star r)) := by
  have h1 : u ⬝ᵥ ((J * Linear.complexify A) *ᵥ star r) = conj lam * (u ⬝ᵥ (J *ᵥ star r)) := by
    rw [← mulVec_mulVec, Modal.complexify_mulVec_star, hr, star_smul, mulVec_smul,
      dotProduct_smul, smul_eq_mul]
    rfl
  have h2 : u ⬝ᵥ ((Linear.complexify A * J) *ᵥ star r) = lam * (u ⬝ᵥ (J *ᵥ star r)) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hu, smul_dotProduct, smul_eq_mul]
  rw [pump, smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, h1, h2, smul_eq_mul]
  ring

/-- Lemma 3 for `λ = −σ + jΩ`: `g = −2jΩ z (u ⬝ᵥ J r̄)` (source (6)). -/
@[tmio T, powerlib_foundation] theorem pump_commutator_eq {A : Matrix (Fin n) (Fin n) ℝ}
    {lam : ℂ} {u r : Fin n → ℂ} (hr : Linear.complexify A *ᵥ r = lam • r)
    (hu : vecMul u (Linear.complexify A) = lam • u) (J : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    pump (z • (J * Linear.complexify A - Linear.complexify A * J)) u r =
      -2 * I * (lam.im : ℂ) * z * (u ⬝ᵥ (J *ᵥ star r)) := by
  rw [pump_commutator hr hu, ← neg_sub, Complex.sub_conj]
  push_cast
  ring

/-! ## The canonical threshold law -/

/-- Normalized pump strength `ĝ = 2|g|/Ω`. -/
def normalizedPump (g : ℂ) (Ω : ℝ) : ℝ := 2 * ‖g‖ / Ω

/-- Canonical threshold law (7) inside the first-order slow flow at exact 2:1 tuning: the slow flow
`Ȧ = −σ A + (ε g/2) A*` is exponentially stable iff `ε ĝ < 4 σ/Ω`. -/
@[tmio TM, powerlib_foundation] theorem canonical_threshold_iff {σ Ω ε : ℝ} (hσ : 0 < σ)
    (hΩ : 0 < Ω) (hε : 0 ≤ ε) (g : ℂ) :
    Flow.GloballyExponentiallyStable (slowFlowSystem σ 0 ((ε : ℂ) * g / 2)) 0 ↔
      ε * normalizedPump g Ω < 4 * (σ / Ω) := by
  rw [slowFlow_threshold_iff hσ hε g]
  have hs : √(σ ^ 2 + (0 : ℝ) ^ 2) = σ := by
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hσ.le]
  rw [hs, normalizedPump]
  have e1 : ε * (2 * ‖g‖ / Ω) = (ε * ‖g‖) * (2 / Ω) := by ring
  have e2 : 4 * (σ / Ω) = (2 * σ) * (2 / Ω) := by ring
  rw [e1, e2, mul_lt_mul_iff_left₀ (by positivity)]

/-- Canonical threshold law (7) as a critical amplitude: for `g ≠ 0`, exponential stability of the
slow flow holds iff `ε < ε_crit = 4 (σ/Ω)/ĝ`. -/
@[tmio TM, powerlib_foundation] theorem canonical_threshold_iff' {σ Ω ε : ℝ} (hσ : 0 < σ)
    (hΩ : 0 < Ω) (hε : 0 ≤ ε) {g : ℂ} (hg : g ≠ 0) :
    Flow.GloballyExponentiallyStable (slowFlowSystem σ 0 ((ε : ℂ) * g / 2)) 0 ↔
      ε < 4 * (σ / Ω) / normalizedPump g Ω := by
  have hpos : 0 < normalizedPump g Ω := by
    unfold normalizedPump; have := norm_pos_iff.mpr hg; positivity
  rw [canonical_threshold_iff hσ hΩ hε g, lt_div_iff₀ hpos]

/-! ## The damped Mathieu check -/

/-- State matrix of `ẍ + 2σẋ + Ω² x = 0` in the state `(x, ẋ)`. -/
def mathieuA₀ (σ Ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -Ω ^ 2, -(2 * σ)]

/-- Modulation matrix of the stiffness pump `Ω² h cos(ω_p t) x`: `J(t) = A₀ + ε Re{A₁ e^{jω_p t}}`. -/
def mathieuA₁ (Ω h : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; -((Ω ^ 2 * h : ℝ) : ℂ), 0]

/-- The mode `λ = −σ + jΩ_m`. -/
def mathieuEig (σ Ωm : ℝ) : ℂ := -(σ : ℂ) + (Ωm : ℂ) * I

/-- Right eigenvector `(1, λ)`. -/
def mathieuRight (σ Ωm : ℝ) : Fin 2 → ℂ := ![1, mathieuEig σ Ωm]

/-- Left eigenvector (row) `(λ + 2σ, 1)/(2jΩ_m) = −j(λ + 2σ, 1)/(2Ω_m)`, normalized against
`mathieuRight`. -/
def mathieuLeft (σ Ωm : ℝ) : Fin 2 → ℂ :=
  ![-I * (mathieuEig σ Ωm + 2 * (σ : ℂ)) / (2 * (Ωm : ℂ)), -I / (2 * (Ωm : ℂ))]

@[tmio T, powerlib_foundation] private theorem mathieu_char {σ Ω Ωm : ℝ} (hm : Ωm ^ 2 = Ω ^ 2 - σ ^ 2) :
    mathieuEig σ Ωm ^ 2 = -((Ω : ℂ) ^ 2) - 2 * (σ : ℂ) * mathieuEig σ Ωm := by
  have hm' : (Ωm : ℂ) ^ 2 = (Ω : ℂ) ^ 2 - (σ : ℂ) ^ 2 := by exact_mod_cast hm
  unfold mathieuEig
  linear_combination (-1 : ℂ) * hm' + ((Ωm : ℂ) ^ 2) * I_sq

@[tmio T, powerlib_foundation] theorem mathieu_right {σ Ω Ωm : ℝ}
    (hm : Ωm ^ 2 = Ω ^ 2 - σ ^ 2) :
    Linear.complexify (mathieuA₀ σ Ω) *ᵥ mathieuRight σ Ωm =
      mathieuEig σ Ωm • mathieuRight σ Ωm := by
  have hc := mathieu_char hm
  funext a
  fin_cases a
  · simp [mathieuA₀, mathieuRight, Linear.complexify, mulVec, dotProduct, Fin.sum_univ_two]
  · simp [mathieuA₀, mathieuRight, Linear.complexify, mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -hc

@[tmio T, powerlib_foundation] theorem mathieu_left {σ Ω Ωm : ℝ} (hΩm : Ωm ≠ 0)
    (hm : Ωm ^ 2 = Ω ^ 2 - σ ^ 2) :
    vecMul (mathieuLeft σ Ωm) (Linear.complexify (mathieuA₀ σ Ω)) =
      mathieuEig σ Ωm • mathieuLeft σ Ωm := by
  have hc := mathieu_char hm
  have hΩc : (Ωm : ℂ) ≠ 0 := by exact_mod_cast hΩm
  funext a
  fin_cases a
  · simp [mathieuA₀, mathieuLeft, Linear.complexify, vecMul, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination hc
  · simp [mathieuA₀, mathieuLeft, Linear.complexify, vecMul, dotProduct, Fin.sum_univ_two]
    ring

@[tmio T, powerlib_foundation] theorem mathieu_normalized {σ Ωm : ℝ} (hΩm : Ωm ≠ 0) :
    mathieuLeft σ Ωm ⬝ᵥ mathieuRight σ Ωm = 1 := by
  have hΩc : (Ωm : ℂ) ≠ 0 := by exact_mod_cast hΩm
  simp only [mathieuLeft, mathieuRight, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mathieuEig]
  field_simp
  linear_combination (-2 * (Ωm : ℂ)) * I_sq

/-- First-order pump coefficient of the damped Mathieu equation: `g = jΩ²h/(2Ω_m)`. -/
@[tmio T, powerlib_foundation] theorem mathieu_pump (σ Ω Ωm h : ℝ) (hΩm : Ωm ≠ 0) :
    pump (mathieuA₁ Ω h) (mathieuLeft σ Ωm) (mathieuRight σ Ωm) =
      I * (((Ω ^ 2 * h : ℝ) : ℂ) / (2 * (Ωm : ℂ))) := by
  have : (Ωm : ℂ) ≠ 0 := by exact_mod_cast hΩm
  simp [pump, mathieuA₁, mathieuLeft, mathieuRight, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp

/-- `ĝ = 2|g|/Ω_m = |h| Ω²/(Ω² − σ²)` for the damped Mathieu equation. -/
@[tmio T, powerlib_foundation] theorem mathieu_normalizedPump {σ Ω Ωm h : ℝ} (hΩm : 0 < Ωm)
    (hm : Ωm ^ 2 = Ω ^ 2 - σ ^ 2) :
    normalizedPump (pump (mathieuA₁ Ω h) (mathieuLeft σ Ωm) (mathieuRight σ Ωm)) Ωm =
      |h| * Ω ^ 2 / (Ω ^ 2 - σ ^ 2) := by
  have hn : ‖I * (((Ω ^ 2 * h : ℝ) : ℂ) / (2 * (Ωm : ℂ)))‖ = Ω ^ 2 * |h| / (2 * Ωm) := by
    rw [norm_mul, norm_I, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg Ω), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hΩm]
    norm_num
  rw [mathieu_pump σ Ω Ωm h hΩm.ne', normalizedPump, hn, ← hm]
  field_simp

/-- The source's `ĝ_m = |h|` holds exactly only without damping (or without pump). -/
@[tmio T, powerlib_foundation] theorem mathieu_normalizedPump_eq_abs_iff {σ Ω Ωm h : ℝ}
    (hΩm : 0 < Ωm) (hm : Ωm ^ 2 = Ω ^ 2 - σ ^ 2) :
    normalizedPump (pump (mathieuA₁ Ω h) (mathieuLeft σ Ωm) (mathieuRight σ Ωm)) Ωm = |h| ↔
      σ = 0 ∨ h = 0 := by
  rw [mathieu_normalizedPump hΩm hm]
  have hpos : 0 < Ω ^ 2 - σ ^ 2 := by rw [← hm]; positivity
  rw [div_eq_iff hpos.ne']
  constructor
  · intro H
    have : |h| * σ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inr (abs_eq_zero.mp h1)
    · exact Or.inl (pow_eq_zero_iff two_ne_zero |>.mp h1)
  · rintro (h1 | h1) <;> simp [h1]

end powerlib.ParametricResonance.Element
