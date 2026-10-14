import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes

/-! # Periodic linear time-varying systems: transition and monodromy matrices

The forward transition matrix of a bounded linear time-varying system, its monodromy matrix for a
periodic state matrix, and the independence of the Floquet multipliers from the initial time.

Scope.
* The linear time-varying system `ẋ = A(t) x` with a continuous real state matrix
  `A : ℝ → Matrix X X ℝ` that is uniformly bounded, `‖A t‖ ≤ M` (operator `L∞` norm,
  `Matrix.Norms.Operator`; vectors carry the sup norm). Every `T`-periodic continuous `A` is
  uniformly bounded (`exists_bound_of_periodic`).
* No model family; every statement is generic in the state matrix `A`.
* Construction. `transition A t s` is the forward solution `Y` of the matrix equation
  `Ẏ = A(t) Y`, `Y(s) = I` on `[s, ∞)`; it is chosen from the global existence theorem for
  globally Lipschitz time-dependent fields (LeanForControl `exists_isIntegralCurveOn_Ici`,
  applied directly), and pinned down by uniqueness (LeanForControl
  `eqOn_of_isIntegralCurveOn_Icc`). Only forward times `t ≥ s` are used.
* LeanForControl's Peano–Baker state-transition matrix `LinearSystems.stateTransitionMatrix`
  (`LinearSystems/Solutions/CtsLTV.lean`) is imported through `dependencies/LeanForControl.lean`;
  `theorem/Dynamics/VariationOfConstants.lean` wraps its variation-of-constants formula for
  continuous `A`. `transition` here is a separate forward-time construction for uniformly
  bounded `A`; the library does not identify the two transition matrices.

Source: work-sync theory/T-harmonic-linearization.md §1.6 (monodromy `Φ(T, 0)`, multipliers);
projects/basin-guard/notes/concepts/guard-object.md §1, §5; projects/vsc-parametric-oscillation/
references/gfm-driven-gfl-parametric-resonance/notes/concepts/coupled-parametric-resonance.md §2
(`Φ' = J Φ`, `Φ(0) = I`).

Results.
* `transition_spec`, `transition_unique`, `trajectory_eq` — existence; every forward matrix or
  vector solution is `Φ(t, s) C`, resp. `Φ(t, s) x(s)`.
* `transition_trans` — `Φ(t, s) Φ(s, τ) = Φ(t, τ)` for `τ ≤ s ≤ t`.
* `norm_transition_le` — `‖Φ(t, s)‖ ≤ ‖I‖ e^{M (t - s)}` (Grönwall).
* `transition_add_period` — `Φ(t + T, s + T) = Φ(t, s)` for a `T`-periodic `A` (any real
  period).
* `monodromy`, `transition_add_nat_mul_period`, `monodromy_add_int_mul` —
  `monodromy A T s = Φ(s + T, s)`; `Φ(s + nT, s) = M_s^n`; `M_{s + kT} = M_s`.
* `charpoly_monodromy`, `spectrum_monodromy` — the characteristic polynomial and the complex
  spectrum (Floquet multipliers) of `M_s` do not depend on the initial time `s`
  (`M_0 = Q P`, `M_s = P Q` with `P = Φ(s, 0)`, `Q = Φ(T, s)`).
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The linear matrix field `Y ↦ A(t) Y`. -/
def matField (A : ℝ → Matrix X X ℝ) (t : ℝ) (Y : Matrix X X ℝ) : Matrix X X ℝ := A t * Y

/-- The linear vector field `x ↦ A(t) x`. -/
def vecField (A : ℝ → Matrix X X ℝ) (t : ℝ) (x : X → ℝ) : X → ℝ := A t *ᵥ x

open Classical in
/-- Forward state-transition matrix `Φ(t, s)` of `ẋ = A(t) x` (meaningful for `t ≥ s`). -/
def transition (A : ℝ → Matrix X X ℝ) (t s : ℝ) : Matrix X X ℝ :=
  if h : ∃ Y : ℝ → Matrix X X ℝ, Y s = 1 ∧ IsIntegralCurveOn Y (matField A) (Ici s) then
    h.choose t
  else 0

/-- One-period (monodromy) matrix from the initial time `s`. -/
def monodromy (A : ℝ → Matrix X X ℝ) (T s : ℝ) : Matrix X X ℝ := transition A (s + T) s

variable {A : ℝ → Matrix X X ℝ} {M : ℝ}

/-! ## Lipschitz bounds of the linear fields -/

@[powerlib_foundation] theorem matField_lipschitz (hM : ∀ t, ‖A t‖ ≤ M) (t : ℝ) :
    LipschitzWith (Real.toNNReal M) (matField A t) := by
  refine LipschitzWith.of_dist_le_mul fun Y Z => ?_
  rw [dist_eq_norm, dist_eq_norm, matField, matField, ← mul_sub, Real.coe_toNNReal']
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right ((hM t).trans (le_max_left _ _)) (norm_nonneg _))

@[powerlib_foundation] theorem vecField_lipschitz (hM : ∀ t, ‖A t‖ ≤ M) (t : ℝ) :
    LipschitzWith (Real.toNNReal M) (vecField A t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, vecField, vecField, ← Matrix.mulVec_sub, Real.coe_toNNReal']
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right ((hM t).trans (le_max_left _ _)) (norm_nonneg _))

/-- A continuous periodic state matrix (period `T > 0`) is uniformly bounded. -/
@[powerlib_foundation] theorem exists_bound_of_periodic {T : ℝ} (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) : ∃ M, ∀ t, ‖A t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  refine ⟨M, fun t => ?_⟩
  obtain ⟨y, hy, hty⟩ := hP.exists_mem_Ico₀ hT t
  rw [hty]
  exact hM y (Ico_subset_Icc_self hy)

/-! ## Existence and uniqueness -/

@[powerlib_foundation] theorem transition_spec (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    (s : ℝ) :
    transition A s s = 1 ∧ IsIntegralCurveOn (fun t => transition A t s) (matField A) (Ici s) := by
  have hex : ∃ Y : ℝ → Matrix X X ℝ, Y s = 1 ∧ IsIntegralCurveOn Y (matField A) (Ici s) := by
    obtain ⟨Y, h0, hY, -⟩ := _root_.exists_isIntegralCurveOn_Ici
      (f := matField A) ((hA.comp continuous_fst).mul continuous_snd) (matField_lipschitz hM) s
      (1 : Matrix X X ℝ)
    exact ⟨Y, h0, hY⟩
  have hdef : (fun t => transition A t s) = hex.choose := by
    funext t
    unfold transition
    simp only [hex, ↓reduceDIte]
  refine ⟨?_, ?_⟩
  · rw [show transition A s s = hex.choose s from congrFun hdef s]
    exact hex.choose_spec.1
  · rw [hdef]
    exact hex.choose_spec.2

@[powerlib_foundation] theorem transition_self (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    (s : ℝ) : transition A s s = 1 :=
  (transition_spec hA hM s).1

/-- Every forward matrix solution of `Ẏ = A(t) Y` with `Y(s) = C` is `Φ(t, s) C`. -/
@[powerlib_foundation] theorem transition_unique (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {s : ℝ} {Y : ℝ → Matrix X X ℝ} (hY : IsIntegralCurveOn Y (matField A) (Ici s)) :
    ∀ t, s ≤ t → Y t = transition A t s * Y s := by
  intro t hst
  obtain ⟨h1, hΦ⟩ := transition_spec hA hM s
  have hZ : IsIntegralCurveOn (fun r => transition A r s * Y s) (matField A) (Ici s) := by
    intro r hr
    have h := (hΦ r hr).mul_const (Y s)
    simpa only [matField, mul_assoc] using h
  have heq := _root_.eqOn_of_isIntegralCurveOn_Icc (matField_lipschitz hM)
    (hY.mono Icc_subset_Ici_self) (hZ.mono Icc_subset_Ici_self)
    (by simp [h1]) (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
  exact heq

/-- Every forward vector solution of `ẋ = A(t) x` is `x(t) = Φ(t, s) x(s)`. -/
@[powerlib_foundation] theorem trajectory_eq (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {s : ℝ} {x : ℝ → X → ℝ} (hx : IsIntegralCurveOn x (vecField A) (Ici s)) :
    ∀ t, s ≤ t → x t = transition A t s *ᵥ x s := by
  intro t hst
  obtain ⟨h1, hΦ⟩ := transition_spec hA hM s
  let L : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun N => N *ᵥ x s
        map_add' := fun N N' => Matrix.add_mulVec N N' (x s)
        map_smul' := fun c N => Matrix.smul_mulVec c N (x s) }
  have hZ : IsIntegralCurveOn (fun r => transition A r s *ᵥ x s) (vecField A) (Ici s) := by
    intro r hr
    have h := L.hasFDerivAt.comp_hasDerivWithinAt r (hΦ r hr)
    change HasDerivWithinAt (fun r => transition A r s *ᵥ x s)
      ((A r * transition A r s) *ᵥ x s) (Ici s) r at h
    rw [vecField, Matrix.mulVec_mulVec]
    exact h
  exact _root_.eqOn_of_isIntegralCurveOn_Icc (vecField_lipschitz hM)
    (hx.mono Icc_subset_Ici_self) (hZ.mono Icc_subset_Ici_self)
    (by simp [h1]) (show t ∈ Icc s t from ⟨hst, le_rfl⟩)

/-- Forward composition: `Φ(t, s) Φ(s, τ) = Φ(t, τ)` for `τ ≤ s ≤ t`. -/
@[powerlib_foundation] theorem transition_trans (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {τ s t : ℝ} (hτs : τ ≤ s) (hst : s ≤ t) :
    transition A t s * transition A s τ = transition A t τ := by
  have hY := (transition_spec hA hM τ).2.mono (Ici_subset_Ici.mpr hτs)
  exact (transition_unique hA hM hY t hst).symm

/-- Grönwall bound `‖Φ(t, s)‖ ≤ ‖I‖ e^{M (t - s)}`. -/
@[powerlib_foundation] theorem norm_transition_le (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {s t : ℝ} (hst : s ≤ t) :
    ‖transition A t s‖ ≤ ‖(1 : Matrix X X ℝ)‖ * Real.exp (Real.toNNReal M * (t - s)) := by
  obtain ⟨h1, hΦ⟩ := transition_spec hA hM s
  have h0 : IsIntegralCurveOn (fun _ => (0 : Matrix X X ℝ)) (matField A) (Icc s t) := by
    intro r _
    simpa [matField] using (hasDerivWithinAt_const r (Icc s t) (0 : Matrix X X ℝ))
  have h := _root_.dist_le_of_isIntegralCurveOn_Icc (matField_lipschitz hM)
    (hΦ.mono Icc_subset_Ici_self) h0 t ⟨hst, le_rfl⟩
  simpa [dist_zero_right, h1] using h

/-! ## Periodicity -/

/-- `Φ(t + T, s + T) = Φ(t, s)` for a `T`-periodic state matrix (any real period `T`). -/
@[powerlib_foundation] theorem transition_add_period (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hP : Periodic A T) {s t : ℝ} (hst : s ≤ t) :
    transition A (t + T) (s + T) = transition A t s := by
  obtain ⟨h1, hΦ⟩ := transition_spec hA hM (s + T)
  have hY : IsIntegralCurveOn (fun r => transition A (r + T) (s + T)) (matField A) (Ici s) := by
    intro r hr
    have hmaps : MapsTo (fun r : ℝ => r + T) (Ici s) (Ici (s + T)) :=
      fun x hx => by simpa using add_le_add_right (show s ≤ x from hx) T
    have h := HasDerivWithinAt.scomp r (hΦ (r + T) (hmaps hr))
      ((hasDerivAt_id' r).hasDerivWithinAt.add_const T) hmaps
    simpa only [matField, hP r, Function.comp_def, one_smul] using h
  have := transition_unique hA hM hY t hst
  simpa [h1] using this

@[powerlib_foundation] theorem monodromy_add_period (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T c : ℝ} (hT : 0 ≤ T) (hP : Periodic A c) (s : ℝ) :
    monodromy A T (s + c) = monodromy A T s := by
  rw [monodromy, monodromy, show s + c + T = s + T + c by ring]
  exact transition_add_period hA hM hP (by linarith)

@[powerlib_foundation] theorem monodromy_add_int_mul (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) (k : ℤ) :
    monodromy A T (s + k * T) = monodromy A T s :=
  monodromy_add_period hA hM hT (hP.int_mul k) s

/-- `Φ(s + n T, s) = (monodromy A T s)^n`. -/
@[powerlib_foundation] theorem transition_add_nat_mul_period (hA : Continuous A)
    (hM : ∀ t, ‖A t‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) (n : ℕ) :
    transition A (s + n * T) s = monodromy A T s ^ n := by
  induction n with
  | zero => simp [transition_self hA hM]
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n * T := mul_nonneg (Nat.cast_nonneg n) hT
    have hshift : transition A (s + T + n * T) (s + n * T) = transition A (s + T) s :=
      transition_add_period hA hM (hP.nat_mul n) (by linarith)
    rw [pow_succ', ← ih, monodromy, ← hshift,
      show s + ((n + 1 : ℕ) : ℝ) * T = s + T + n * T by push_cast; ring]
    exact (transition_trans hA hM (by linarith) (by linarith)).symm

/-- On `[0, T]`: `M_0 = Q P` and `M_s = P Q` with `P = Φ(s, 0)`, `Q = Φ(T, s)`. -/
@[powerlib_foundation] theorem monodromy_eq_mul_swap (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hP : Periodic A T) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    monodromy A T 0 = transition A T s * transition A s 0 ∧
      monodromy A T s = transition A s 0 * transition A T s := by
  constructor
  · rw [monodromy, zero_add]
    exact (transition_trans hA hM hs0 hsT).symm
  · have hshift : transition A (s + T) (0 + T) = transition A s 0 :=
      transition_add_period hA hM hP hs0
    rw [zero_add] at hshift
    rw [monodromy, ← hshift]
    exact (transition_trans hA hM hsT (by linarith)).symm

/-- The characteristic polynomial of the monodromy matrix does not depend on the initial
time. -/
@[powerlib_foundation] theorem charpoly_monodromy (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) :
    (monodromy A T s).charpoly = (monodromy A T 0).charpoly := by
  rcases hT.eq_or_lt with hT0 | hTpos
  · subst hT0
    simp [monodromy, transition_self hA hM]
  · set k : ℤ := ⌊s / T⌋
    set s' : ℝ := s - k * T
    have hs'0 : 0 ≤ s' := by
      have := Int.floor_le (s / T)
      have h2 : (k : ℝ) * T ≤ s := by
        calc (k : ℝ) * T ≤ s / T * T := mul_le_mul_of_nonneg_right this hTpos.le
          _ = s := by field_simp
      simp only [s']; linarith
    have hs'T : s' ≤ T := by
      have := Int.lt_floor_add_one (s / T)
      have h2 : s < ((k : ℝ) + 1) * T := by
        calc s = s / T * T := by field_simp
          _ < ((k : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hTpos
      simp only [s']; nlinarith
    have hred : monodromy A T s = monodromy A T s' := by
      have := monodromy_add_int_mul hA hM hT hP s' k
      rwa [show s' + k * T = s by simp [s']] at this
    obtain ⟨h0, hs⟩ := monodromy_eq_mul_swap hA hM hP hs'0 hs'T
    rw [hred, hs, h0, Matrix.charpoly_mul_comm]

/-- The Floquet multipliers (complex spectrum of the complexified monodromy matrix) do not
depend on the initial time. -/
@[powerlib_foundation] theorem spectrum_monodromy (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) :
    spectrum ℂ ((monodromy A T s).map (algebraMap ℝ ℂ)) =
      spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.charpoly_map, Matrix.charpoly_map, charpoly_monodromy hA hM hT hP s]

end powerlib.Periodic
