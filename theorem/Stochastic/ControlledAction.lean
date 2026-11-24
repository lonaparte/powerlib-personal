import dependencies.Mathlib
import theorem.Attributes

/-! # Controlled action and quasi-potential for degenerate noise: the verification theorem

The Freidlin–Wentzell action of `theorem/Stochastic/LargeDeviations.lean` (`fwAction`,
`quasiPotential`) needs a positive definite diffusion matrix. Here the noise may act on some
state rows only (degenerate diffusion, e.g. a swing equation driven through the frequency row):
the skeleton is the controlled field `ẋ = b(x) + Σⱼ uⱼ σⱼ(x)` (the noise columns `σⱼ` with the
white noise replaced by a control `u`), its action is `S_T(u) = ½ ∫₀ᵀ |u(t)|² dt` and the
quasi-potential `V(x_A, x)` is the infimum of `S_T(u)` over `T ≥ 0` and admissible pairs `(φ, u)`
from `x_A` to `x`. When `a = σσᵀ` is positive definite, the least `|u|²` with
`σ u = φ̇ − b(φ)` is `(φ̇ − b)ᵀ a⁻¹ (φ̇ − b)`, so the infimum over controls of a given path is the
action `fwAction` (not formalized here).

Scope.
* Calculus of variations / optimal control on a real normed space; no engineering import.
* Deterministic variational objects only: that `V` is the large-deviation rate of the exit
  problem of the diffusion `dx = b dt + √ε σ dw` (Freidlin–Wentzell's theorem, for degenerate
  noise under a controllability hypothesis) is not formalized and not claimed.
* Admissible pairs: `T ≥ 0`, `φ(0) = x_A`, `φ(T) = x`, `φ` continuous on `[0, T]` with right
  derivative `b(φ) + Σⱼ uⱼ σⱼ(φ)` at every point of `[0, T)`, and `|u|²` integrable on `[0, T]`
  (piecewise paths are admissible, so pairs concatenate).

Source: work-sync theory/T-freidlin-wentzell.md (the diffusion `dX = b dt + √ε σ dW` and the
action with `a = σσᵀ` invertible; the controlled form for a degenerate `a` is not in the note),
theory/T-quasi-potential.md (`V_qp(x) = inf_{T, φ(0) = x_A, φ(T) = x} S`); M. I. Freidlin,
A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984), Ch. 4–5 (skeleton with a
control, quasi-potential, Hamilton–Jacobi characterization);
W. H. Fleming, R. W. Rishel, *Deterministic and Stochastic Optimal Control* (1975), Ch. IV
(verification theorem for the Hamilton–Jacobi inequality).

Results.
* `controlField`, `controlAction`, `controlQuasiPotential`, `hjHamiltonian`
  (`H(x, L) = L(b(x)) + ½ Σⱼ L(σⱼ(x))²` for a linear form `L`, the Hamilton–Jacobi Hamiltonian
  at the gradient `L = dW(x)`).
* `apply_controlField` (completing the square):
  `L(b + Σⱼ uⱼ σⱼ) = H(x, L) + ½ |u|² − ½ Σⱼ (uⱼ − L(σⱼ))²`.
* `sub_le_controlAction` (verification inequality): along an admissible pair on which the
  differentiable `W` satisfies `H(φ, dW(φ)) ≤ 0`, `W(φ(T)) − W(φ(0)) ≤ S_T(u)`;
  `controlAction_eq_of_feedback`: equality when moreover `H = 0` along the path and the control
  is the feedback `uⱼ = dW(φ)(σⱼ(φ))`.
* `le_controlQuasiPotential` (lower bound): a Hamilton–Jacobi subsolution `W`
  (`H(x, dW(x)) ≤ 0` everywhere) gives `V(x_A, x) ≥ W(x) − W(x_A)`;
  `controlQuasiPotential_le` (upper bound): `V(x_A, x) ≤ S_T(u)` for every admissible pair;
  `controlQuasiPotential_eq_of_feedback`: both together, `V(x_A, x) = W(x) − W(x_A)` when an
  admissible pair follows the feedback of an exact solution.
* `controlQuasiPotential_triangle`: `V(x, z) ≤ V(x, y) + V(y, z)` (concatenation).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **Controlled (skeleton) field** `b(x) + Σⱼ uⱼ σⱼ(x)`: the noise column `σ x j` driven by the
control value `u j` in place of white noise. -/
def controlField (b : E → E) (σ : E → Fin m → E) (x : E) (u : Fin m → ℝ) : E :=
  b x + ∑ j, u j • σ x j

/-- **Controlled action** `S_T(u) = ½ ∫₀ᵀ |u(t)|² dt`. -/
def controlAction (u : ℝ → Fin m → ℝ) (T : ℝ) : ℝ :=
  1 / 2 * ∫ t in (0 : ℝ)..T, ∑ j, u t j ^ 2

/-- **Quasi-potential for degenerate noise**: `V(x_A, x) = inf S_T(u)` over `T ≥ 0` and
admissible pairs `(φ, u)` from `x_A` to `x` (`ℝ≥0∞`-valued, `∞` if `x` is not reachable). -/
def controlQuasiPotential (b : E → E) (σ : E → Fin m → E) (xA x : E) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → E) (u : ℝ → Fin m → ℝ)
    (_ : 0 ≤ T ∧ φ 0 = xA ∧ φ T = x ∧ ContinuousOn φ (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t) ∧
      IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T),
    ENNReal.ofReal (controlAction u T)

/-- **Hamilton–Jacobi Hamiltonian** at the state `x` and the linear form `L` (the derivative of
a candidate quasi-potential): `H(x, L) = L(b(x)) + ½ Σⱼ L(σⱼ(x))²`. -/
def hjHamiltonian (b : E → E) (σ : E → Fin m → E) (x : E) (L : E →L[ℝ] ℝ) : ℝ :=
  L (b x) + 1 / 2 * ∑ j, L (σ x j) ^ 2

/-- **Completing the square**: `L(b + Σⱼ uⱼ σⱼ) = H(x, L) + ½|u|² − ½ Σⱼ (uⱼ − L(σⱼ))²`. -/
@[tmio T, powerlib_foundation] theorem apply_controlField (b : E → E) (σ : E → Fin m → E)
    (x : E) (u : Fin m → ℝ) (L : E →L[ℝ] ℝ) :
    L (controlField b σ x u) = hjHamiltonian b σ x L + 1 / 2 * ∑ j, u j ^ 2 -
      1 / 2 * ∑ j, (u j - L (σ x j)) ^ 2 := by
  simp only [controlField, hjHamiltonian, map_add, map_sum, map_smul, smul_eq_mul]
  have key : ∑ j, u j * L (σ x j) = 1 / 2 * ∑ j, L (σ x j) ^ 2 + 1 / 2 * ∑ j, u j ^ 2 -
      1 / 2 * ∑ j, (u j - L (σ x j)) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith

/-- The action is nonnegative on `T ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem controlAction_nonneg (u : ℝ → Fin m → ℝ) {T : ℝ}
    (hT : 0 ≤ T) : 0 ≤ controlAction u T :=
  mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hT fun t _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- The right derivative of `W ∘ φ` along an admissible pair, in the open interval. -/
@[tmio T, powerlib_foundation] private theorem comp_hasDerivWithinAt {b : E → E}
    {σ : E → Fin m → E} {W : E → ℝ} {dW : E → E →L[ℝ] ℝ} {T : ℝ} {φ : ℝ → E}
    {u : ℝ → Fin m → ℝ} (hW : ∀ t ∈ Icc 0 T, HasFDerivAt W (dW (φ t)) (φ t))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivWithinAt (fun s => W (φ s)) (dW (φ t) (controlField b σ (φ t) (u t))) (Ioi t) t :=
  ((hW t (Ioo_subset_Icc_self ht)).comp_hasDerivWithinAt t
    (hφ t ⟨ht.1.le, ht.2⟩)).mono Ioi_subset_Ici_self

@[tmio T, powerlib_foundation] private theorem comp_continuousOn {W : E → ℝ}
    {dW : E → E →L[ℝ] ℝ} {T : ℝ} {φ : ℝ → E}
    (hW : ∀ t ∈ Icc 0 T, HasFDerivAt W (dW (φ t)) (φ t)) (hc : ContinuousOn φ (Icc 0 T)) :
    ContinuousOn (fun s => W (φ s)) (Icc 0 T) := fun t ht =>
  (hW t ht).continuousAt.comp_continuousWithinAt (hc t ht)

@[tmio T, powerlib_foundation] private theorem integrableOn_half {u : ℝ → Fin m → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) :
    IntegrableOn (fun t => 1 / 2 * ∑ j, u t j ^ 2) (Icc 0 T) := by
  have h := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hu
  exact h.const_mul _

/-- **Verification inequality**: along an admissible pair on which the differentiable `W`
satisfies the Hamilton–Jacobi inequality `H(φ, dW(φ)) ≤ 0`, `W(φ(T)) − W(φ(0)) ≤ S_T(u)`. -/
@[tmio T, powerlib_foundation] theorem sub_le_controlAction {b : E → E} {σ : E → Fin m → E}
    {W : E → ℝ} {dW : E → E →L[ℝ] ℝ} {T : ℝ} (hT : 0 ≤ T) {φ : ℝ → E} {u : ℝ → Fin m → ℝ}
    (hW : ∀ t ∈ Icc 0 T, HasFDerivAt W (dW (φ t)) (φ t))
    (hHJ : ∀ t ∈ Icc 0 T, hjHamiltonian b σ (φ t) (dW (φ t)) ≤ 0)
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t)
    (hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) :
    W (φ T) - W (φ 0) ≤ controlAction u T := by
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hT
    (comp_continuousOn hW hc) (comp_hasDerivWithinAt hW hφ) (integrableOn_half hT hu)
    (fun t ht => by
      have ht' := Ioo_subset_Icc_self ht
      rw [apply_controlField]
      have h1 := hHJ t ht'
      have h2 : 0 ≤ ∑ j, (u t j - dW (φ t) (σ (φ t) j)) ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith)
  rwa [intervalIntegral.integral_const_mul] at h

/-- **Equality case**: if moreover `H(φ, dW(φ)) = 0` along the path and the control is the
feedback `uⱼ = dW(φ)(σⱼ(φ))`, then `S_T(u) = W(φ(T)) − W(φ(0))`. -/
@[tmio T, powerlib_foundation] theorem controlAction_eq_of_feedback {b : E → E}
    {σ : E → Fin m → E} {W : E → ℝ} {dW : E → E →L[ℝ] ℝ} {T : ℝ} (hT : 0 ≤ T) {φ : ℝ → E}
    {u : ℝ → Fin m → ℝ} (hW : ∀ t ∈ Icc 0 T, HasFDerivAt W (dW (φ t)) (φ t))
    (hHJ : ∀ t ∈ Icc 0 T, hjHamiltonian b σ (φ t) (dW (φ t)) = 0)
    (hfb : ∀ t ∈ Icc 0 T, ∀ j, u t j = dW (φ t) (σ (φ t) j))
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t)
    (hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) :
    controlAction u T = W (φ T) - W (φ 0) := by
  refine le_antisymm ?_ (sub_le_controlAction hT hW (fun t ht => (hHJ t ht).le) hc hφ hu)
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT
    (comp_continuousOn hW hc) (comp_hasDerivWithinAt hW hφ) (integrableOn_half hT hu)
    (fun t ht => by
      have ht' := Ioo_subset_Icc_self ht
      rw [apply_controlField, hHJ t ht']
      simp [hfb t ht'])
  rwa [intervalIntegral.integral_const_mul] at h

/-- **Lower bound (verification theorem)**: a Hamilton–Jacobi subsolution `W`
(`H(x, dW(x)) ≤ 0` at every state) bounds the quasi-potential from below:
`V(x_A, x) ≥ W(x) − W(x_A)`. -/
@[tmio T, powerlib_foundation] theorem le_controlQuasiPotential {b : E → E}
    {σ : E → Fin m → E} {W : E → ℝ} {dW : E → E →L[ℝ] ℝ} (hW : ∀ x, HasFDerivAt W (dW x) x)
    (hHJ : ∀ x, hjHamiltonian b σ x (dW x) ≤ 0) (xA x : E) :
    ENNReal.ofReal (W x - W xA) ≤ controlQuasiPotential b σ xA x := by
  unfold controlQuasiPotential
  refine le_iInf fun T => le_iInf fun φ => le_iInf fun u => le_iInf fun h => ?_
  obtain ⟨hT, h0, hTx, hc, hφ, hu⟩ := h
  apply ENNReal.ofReal_le_ofReal
  have := sub_le_controlAction hT (fun t _ => hW (φ t)) (fun t _ => hHJ (φ t)) hc hφ hu
  rwa [h0, hTx] at this

/-- **Upper bound by an explicit admissible pair**: `V(x_A, x) ≤ S_T(u)`. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le {b : E → E}
    {σ : E → Fin m → E} {xA x : E} {T : ℝ} {φ : ℝ → E} {u : ℝ → Fin m → ℝ} (hT : 0 ≤ T)
    (h0 : φ 0 = xA) (hTx : φ T = x) (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t)
    (hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) :
    controlQuasiPotential b σ xA x ≤ ENNReal.ofReal (controlAction u T) :=
  iInf_le_of_le T <| iInf_le_of_le φ <| iInf_le_of_le u <|
    iInf_le_of_le ⟨hT, h0, hTx, hc, hφ, hu⟩ le_rfl

/-- **Value of the quasi-potential**: if `W` is a Hamilton–Jacobi subsolution everywhere and an
admissible pair from `x_A` to `x` follows its feedback `uⱼ = dW(φ)(σⱼ(φ))` with `H = 0` along
the path, then `V(x_A, x) = W(x) − W(x_A)`. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_eq_of_feedback {b : E → E}
    {σ : E → Fin m → E} {W : E → ℝ} {dW : E → E →L[ℝ] ℝ} (hW : ∀ x, HasFDerivAt W (dW x) x)
    (hHJ : ∀ x, hjHamiltonian b σ x (dW x) ≤ 0) {xA x : E} {T : ℝ} {φ : ℝ → E}
    {u : ℝ → Fin m → ℝ} (hT : 0 ≤ T) (h0 : φ 0 = xA) (hTx : φ T = x)
    (hHJ0 : ∀ t ∈ Icc 0 T, hjHamiltonian b σ (φ t) (dW (φ t)) = 0)
    (hfb : ∀ t ∈ Icc 0 T, ∀ j, u t j = dW (φ t) (σ (φ t) j))
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t)
    (hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) :
    controlQuasiPotential b σ xA x = ENNReal.ofReal (W x - W xA) := by
  refine le_antisymm ?_ (le_controlQuasiPotential hW hHJ xA x)
  have h := controlAction_eq_of_feedback hT (fun t _ => hW (φ t)) hHJ0 hfb hc hφ hu
  rw [h0, hTx] at h
  exact h ▸ controlQuasiPotential_le hT h0 hTx hc hφ hu

/-! ## Concatenation -/

/-- The concatenation of two admissible pairs is admissible, with the sum of the actions. -/
@[tmio T, powerlib_foundation] private theorem concat_admissible {b : E → E}
    {σ : E → Fin m → E} {x y z : E} {T₁ T₂ : ℝ} {φ₁ φ₂ : ℝ → E} {u₁ u₂ : ℝ → Fin m → ℝ}
    (hT₁ : 0 ≤ T₁) (h₁0 : φ₁ 0 = x) (h₁T : φ₁ T₁ = y) (hc₁ : ContinuousOn φ₁ (Icc 0 T₁))
    (hφ₁ : ∀ t ∈ Ico 0 T₁, HasDerivWithinAt φ₁ (controlField b σ (φ₁ t) (u₁ t)) (Ici t) t)
    (hu₁ : IntervalIntegrable (fun t => ∑ j, u₁ t j ^ 2) volume 0 T₁)
    (hT₂ : 0 ≤ T₂) (h₂0 : φ₂ 0 = y) (h₂T : φ₂ T₂ = z) (hc₂ : ContinuousOn φ₂ (Icc 0 T₂))
    (hφ₂ : ∀ t ∈ Ico 0 T₂, HasDerivWithinAt φ₂ (controlField b σ (φ₂ t) (u₂ t)) (Ici t) t)
    (hu₂ : IntervalIntegrable (fun t => ∑ j, u₂ t j ^ 2) volume 0 T₂) :
    controlQuasiPotential b σ x z ≤
      ENNReal.ofReal (controlAction u₁ T₁ + controlAction u₂ T₂) := by
  set φ : ℝ → E := fun t => if t ≤ T₁ then φ₁ t else φ₂ (t - T₁) with hφdef
  set u : ℝ → Fin m → ℝ := fun t => if t < T₁ then u₁ t else u₂ (t - T₁) with hudef
  have hlo : ∀ t, t ≤ T₁ → φ t = φ₁ t := fun t ht => by simp [φ, ht]
  have hhi : ∀ t, T₁ ≤ t → φ t = φ₂ (t - T₁) := by
    intro t ht
    by_cases h : t ≤ T₁
    · have e : t = T₁ := le_antisymm h ht
      rw [hlo t h, e, h₁T, sub_self, h₂0]
    · simp [φ, h]
  have hT : 0 ≤ T₁ + T₂ := add_nonneg hT₁ hT₂
  have hmaps : MapsTo (fun t => t - T₁) (Icc T₁ (T₁ + T₂)) (Icc 0 T₂) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- continuity
  have hc : ContinuousOn φ (Icc 0 (T₁ + T₂)) := by
    rw [← Icc_union_Icc_eq_Icc hT₁ (le_add_of_nonneg_right hT₂)]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hc₁.congr fun t ht => hlo t ht.2
    · exact (hc₂.comp (continuousOn_id.sub continuousOn_const) hmaps).congr
        fun t ht => hhi t ht.1
  -- right derivatives
  have hφ : ∀ t ∈ Ico 0 (T₁ + T₂),
      HasDerivWithinAt φ (controlField b σ (φ t) (u t)) (Ici t) t := by
    intro t ht
    by_cases h : t < T₁
    · have hu : u t = u₁ t := by simp [u, h]
      rw [hu, hlo t h.le]
      refine (hφ₁ t ⟨ht.1, h⟩).congr_of_eventuallyEq ?_ (hlo t h.le)
      filter_upwards [Icc_mem_nhdsGE h] with s hs using hlo s hs.2
    · push Not at h
      have hu : u t = u₂ (t - T₁) := by simp [u, not_lt.mpr h]
      rw [hu, hhi t h]
      have h2 := hφ₂ (t - T₁) ⟨by linarith, by linarith [ht.2]⟩
      have hs := (hasDerivWithinAt_id t (Ici t)).sub_const T₁
      have hcomp := h2.scomp t hs (fun s hs' => by
        simp only [mem_Ici] at hs' ⊢; simp only [id]; linarith)
      simp only [one_smul] at hcomp
      refine hcomp.congr_of_eventuallyEq ?_ (hhi t h)
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hhi s (le_trans h hs)
  -- the two integrals
  have heq1 : EqOn (fun t => ∑ j, u t j ^ 2) (fun t => ∑ j, u₁ t j ^ 2) (uIoo 0 T₁) := by
    intro t ht
    rw [uIoo_of_le hT₁] at ht
    simp [u, ht.2]
  have heq2 : EqOn (fun t => ∑ j, u t j ^ 2) (fun t => ∑ j, u₂ (t - T₁) j ^ 2)
      (uIcc T₁ (T₁ + T₂)) := by
    intro t ht
    rw [uIcc_of_le (le_add_of_nonneg_right hT₂)] at ht
    simp [u, not_lt.mpr ht.1]
  have hi1 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T₁ :=
    hu₁.congr_uIoo heq1.symm
  have hi2' : IntervalIntegrable (fun t => ∑ j, u₂ (t - T₁) j ^ 2) volume T₁ (T₁ + T₂) := by
    have := hu₂.comp_sub_right T₁
    simpa [add_comm] using this
  have hi2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume T₁ (T₁ + T₂) :=
    hi2'.congr_uIoo fun t ht => (heq2 (Ioo_subset_Icc_self ht)).symm
  have hu : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 (T₁ + T₂) := hi1.trans hi2
  have hS : controlAction u (T₁ + T₂) = controlAction u₁ T₁ + controlAction u₂ T₂ := by
    unfold controlAction
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
      intervalIntegral.integral_congr_uIoo heq1, intervalIntegral.integral_congr heq2,
      intervalIntegral.integral_comp_sub_right (fun t => ∑ j, u₂ t j ^ 2) T₁]
    simp only [sub_self, add_sub_cancel_left]
    ring
  have hTz : φ (T₁ + T₂) = z := by
    rw [hhi _ (le_add_of_nonneg_right hT₂), add_sub_cancel_left, h₂T]
  rw [← hS]
  exact controlQuasiPotential_le hT (by rw [hlo 0 hT₁, h₁0]) hTz hc hφ hu

/-- **Triangle inequality**: `V(x, z) ≤ V(x, y) + V(y, z)` (concatenation of admissible
pairs). -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_triangle (b : E → E)
    (σ : E → Fin m → E) (x y z : E) :
    controlQuasiPotential b σ x z ≤
      controlQuasiPotential b σ x y + controlQuasiPotential b σ y z := by
  conv_rhs => simp only [controlQuasiPotential, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun T₁ => le_iInf fun φ₁ => le_iInf fun u₁ => le_iInf fun h₁ => ?_
  refine le_iInf fun T₂ => le_iInf fun φ₂ => le_iInf fun u₂ => le_iInf fun h₂ => ?_
  -- the first pair runs from `y` to `z`, the second from `x` to `y`
  obtain ⟨hT₁, h₁0, h₁T, hc₁, hφ₁, hu₁⟩ := h₁
  obtain ⟨hT₂, h₂0, h₂T, hc₂, hφ₂, hu₂⟩ := h₂
  rw [← ENNReal.ofReal_add (controlAction_nonneg _ hT₂) (controlAction_nonneg _ hT₁)]
  exact concat_admissible hT₂ h₂0 h₂T hc₂ hφ₂ hu₂ hT₁ h₁0 h₁T hc₁ hφ₁ hu₁

end powerlib.Stochastic.LDP
