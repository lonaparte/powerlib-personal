import theorem.Modal.ForcedPhasor

/-! # Mode shape at resonance along a family whose modal vectors move

TR-110 §2.2.3: at resonance the steady-state response has the shape of the right eigenvector of
the resonating mode. `Modal.tendsto_mode_shape` proves this along a family of matrices whose
modal vectors are fixed. A physical family (an operating point that drifts, a damping control
whose gain is turned down) changes its eigenvectors with its eigenvalues; this module allows the
right and left modal matrices to converge, `V_ε → V₀`, `W_ε → W₀`, while the resonating
eigenvalue `−σ_ε + jω_d` approaches the forcing frequency `jω_d` and the other eigenvalues stay a
uniform distance `δ` from it. The scaled steady state then tends to `(ψ_{0,r}ᵀ b) v_{0,r}`, the
limit modal vectors.

Scope.
* An arbitrary filter `L` on an index type `ι` and a family of complex matrices `A ε` with modal
  bases `mb ε : ModalBasis (A ε)` (`theorem/Modal/Participation.lean`: diagonalizable, columns of
  `V` right and of `W` left eigenvectors, `Wᵀ V = 1`), modal matrices converging entrywise in
  `L`. Steady state `(jω_d I − A ε)⁻¹ b` for a fixed input `b`, as in
  `theorem/Modal/ForcedPhasor.lean`. No model family; generic linear algebra and limits.
* The resonating eigenvalue is exactly `−σ_ε + jω_d` with `σ_ε → 0`, `σ_ε ≠ 0`; the separation
  `δ > 0` of the other eigenvalues from `jω_d` is uniform in `ε`.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.2.3 (the mode shape at
resonance is the right eigenvector of the resonating mode) and §2.2.1, eq. (2-18) (modal
expansion of the steady state).

Results.
* `tendsto_mode_shape_family` — `σ_ε (jω_d I − A ε)⁻¹ b → (ψ_{0,r}ᵀ b) v_{0,r}` with
  `ψ_{0,r}`, `v_{0,r}` the `r`-th columns of `W₀`, `V₀` (the remainder is bounded by
  `|σ_ε| Σ_{i≠r} ‖ψ_{ε,i}ᵀb‖‖v_{ε,i}‖/δ`, `ModalBasis.norm_resolvent_mulVec_sub_le`, which stays
  bounded because the modal vectors converge).
* `tendsto_mode_shape_family_ratio` — if `ψ_{0,r}ᵀ b ≠ 0` and `v_{0,r,k'} ≠ 0`, the complex
  ratio of the steady-state phasors of states `k`, `k'` tends to `V₀ k r / V₀ k' r`, whatever
  the input.
-/

noncomputable section
namespace powerlib.Modal
open Matrix Complex Filter Topology

section ModeShapeFamily

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The leading term `(ψ_rᵀ b) v_r` as a continuous function of the modal matrices `(V, W)`. -/
@[tmio T, powerlib_foundation] private theorem continuous_leading (r : n) (b : n → ℂ) :
    Continuous fun p : Matrix n n ℂ × Matrix n n ℂ =>
      ((fun l => p.2 l r) ⬝ᵥ b) • fun k => p.1 k r :=
  ((continuous_pi fun l => continuous_snd.matrix_elem l r).dotProduct continuous_const).smul
    (continuous_pi fun k => continuous_fst.matrix_elem k r)

/-- The remainder weight `Σ_{i≠r} ‖ψ_iᵀ b‖/δ ‖v_i‖` as a continuous function of `(V, W)`. -/
@[tmio T, powerlib_foundation] private theorem continuous_weight (r : n) (b : n → ℂ) (δ : ℝ) :
    Continuous fun p : Matrix n n ℂ × Matrix n n ℂ =>
      ∑ i ∈ Finset.univ.erase r, ‖(fun l => p.2 l i) ⬝ᵥ b‖ / δ * ‖fun k => p.1 k i‖ := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((((continuous_pi fun l => continuous_snd.matrix_elem l i).dotProduct
    continuous_const).norm.div_const δ).mul (continuous_pi fun k =>
      continuous_fst.matrix_elem k i).norm)

/-- §2.2.3 along a family with moving modal vectors: if `V_ε → V₀`, `W_ε → W₀`, the resonating
eigenvalue is `−σ_ε + jω_d` with `σ_ε → 0`, and the other eigenvalues stay at distance `≥ δ > 0`
from `jω_d`, then `σ_ε (jω_d I − A ε)⁻¹ b → (ψ_{0,r}ᵀ b) v_{0,r}` for every input `b`. -/
@[tmio T, powerlib_foundation] theorem tendsto_mode_shape_family {ι : Type*} {L : Filter ι}
    {A : ι → Matrix n n ℂ} (mb : ∀ ε, ModalBasis (A ε)) {V₀ W₀ : Matrix n n ℂ}
    (hV : Tendsto (fun ε => (mb ε).V) L (𝓝 V₀)) (hW : Tendsto (fun ε => (mb ε).W) L (𝓝 W₀))
    (r : n) (ωd : ℝ) {σ : ι → ℝ} (hσ : Tendsto σ L (𝓝 0)) (hσ0 : ∀ ε, σ ε ≠ 0)
    (heig : ∀ ε, (mb ε).eig r = -(σ ε : ℂ) + (ωd : ℂ) * I) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ε, ∀ i, i ≠ r → δ ≤ ‖(ωd : ℂ) * I - (mb ε).eig i‖) (b : n → ℂ) :
    Tendsto (fun ε => (σ ε : ℂ) • ((((ωd : ℂ) * I) • (1 : Matrix n n ℂ) - A ε)⁻¹ *ᵥ b)) L
      (𝓝 (((fun l => W₀ l r) ⬝ᵥ b) • fun k => V₀ k r)) := by
  have hs : ∀ ε i, (ωd : ℂ) * I ≠ (mb ε).eig i := by
    intro ε i h
    by_cases hi : i = r
    · subst hi
      rw [heig] at h
      have := congrArg Complex.re h
      simp at this
      exact hσ0 ε (by linarith)
    · have := hsep ε i hi
      rw [h, sub_self, norm_zero] at this
      linarith
  have hsr : ∀ ε, (ωd : ℂ) * I - (mb ε).eig r = (σ ε : ℂ) := by
    intro ε; rw [heig]; ring
  have hp : Tendsto (fun ε => ((mb ε).V, (mb ε).W)) L (𝓝 (V₀, W₀)) := hV.prodMk_nhds hW
  -- the leading term converges
  have hlead := ((continuous_leading r b).tendsto (V₀, W₀)).comp hp
  -- the remainder tends to zero
  have hC := ((continuous_weight r b δ).tendsto (V₀, W₀)).comp hp
  have hg := hσ.abs.mul hC
  rw [abs_zero, zero_mul] at hg
  have hrem : Tendsto (fun ε => (σ ε : ℂ) • ((((ωd : ℂ) * I) • (1 : Matrix n n ℂ) - A ε)⁻¹ *ᵥ b) -
      ((fun l => (mb ε).W l r) ⬝ᵥ b) • fun k => (mb ε).V k r) L (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun ε => ?_) hg
    have h := (mb ε).norm_resolvent_mulVec_sub_le (hs ε) b r
    rw [hsr, Complex.norm_real, Real.norm_eq_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_)
      (abs_nonneg _))
    have hi' : i ≠ r := Finset.ne_of_mem_erase hi
    show ‖(mb ε).ψ i ⬝ᵥ b‖ / ‖(ωd : ℂ) * I - (mb ε).eig i‖ * ‖(mb ε).v i‖ ≤
      ‖(mb ε).ψ i ⬝ᵥ b‖ / δ * ‖(mb ε).v i‖
    gcongr
    exact hsep ε i hi'
  have h := hlead.add hrem
  simp only [Function.comp_apply, add_zero, add_sub_cancel] at h
  exact h

/-- §2.2.3, relative amplitude and phase along a family with moving modal vectors: if the limit
mode is excited (`ψ_{0,r}ᵀ b ≠ 0`) and visible in state `k'` (`V₀ k' r ≠ 0`), the ratio of the
steady-state phasors of states `k`, `k'` tends to `V₀ k r / V₀ k' r`, whatever the input. -/
@[tmio T, powerlib_foundation] theorem tendsto_mode_shape_family_ratio {ι : Type*}
    {L : Filter ι} {A : ι → Matrix n n ℂ} (mb : ∀ ε, ModalBasis (A ε)) {V₀ W₀ : Matrix n n ℂ}
    (hV : Tendsto (fun ε => (mb ε).V) L (𝓝 V₀)) (hW : Tendsto (fun ε => (mb ε).W) L (𝓝 W₀))
    (r : n) (ωd : ℝ) {σ : ι → ℝ} (hσ : Tendsto σ L (𝓝 0)) (hσ0 : ∀ ε, σ ε ≠ 0)
    (heig : ∀ ε, (mb ε).eig r = -(σ ε : ℂ) + (ωd : ℂ) * I) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ε, ∀ i, i ≠ r → δ ≤ ‖(ωd : ℂ) * I - (mb ε).eig i‖) (b : n → ℂ)
    (hb : (fun l => W₀ l r) ⬝ᵥ b ≠ 0) (k k' : n) (hk' : V₀ k' r ≠ 0) :
    Tendsto (fun ε => ((((ωd : ℂ) * I) • (1 : Matrix n n ℂ) - A ε)⁻¹ *ᵥ b) k /
        ((((ωd : ℂ) * I) • (1 : Matrix n n ℂ) - A ε)⁻¹ *ᵥ b) k') L (𝓝 (V₀ k r / V₀ k' r)) := by
  have h := tendsto_mode_shape_family mb hV hW r ωd hσ hσ0 heig hδ hsep b
  have hk := (continuous_apply k).continuousAt.tendsto.comp h
  have hk'' := (continuous_apply k').continuousAt.tendsto.comp h
  have hdiv := hk.div hk'' (by simp [hb, hk'])
  have hlim : ((((fun l => W₀ l r) ⬝ᵥ b) • fun k => V₀ k r) k) /
      ((((fun l => W₀ l r) ⬝ᵥ b) • fun k => V₀ k r) k') = V₀ k r / V₀ k' r := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hb]
  rw [hlim] at hdiv
  refine hdiv.congr fun ε => ?_
  have hσc : (σ ε : ℂ) ≠ 0 := by exact_mod_cast hσ0 ε
  simp [mul_div_mul_left _ _ hσc]

end ModeShapeFamily

end powerlib.Modal
