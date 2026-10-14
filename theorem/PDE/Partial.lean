import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Partial derivatives on `ℝ × ℝ` (foundation)

Calculus tools for functions `F : ℝ × ℝ → ℝ` of `(x, t)`, shared by the one-dimensional PDE
modules.

Scope.
* Generic calculus; nothing here describes a physical system and no model family is defined.

Source: work-sync `theory/T-pde-systems.md` §1.4.4–§1.4.5, `theory/T-telegrapher-bergeron.md`
§1.1 (the partial-derivative notation of the telegrapher equations).

Results.
* `HasPartialsWithin U Ux Ut S q`: `U` has partial derivatives `Ux`, `Ut` (in `x` and `t`) within
  `S` at `q` (a Fréchet derivative within `S`, so C¹ up to the boundary of a strip);
  `strip a b = [a, b] × ℝ`.
* `const_along_segment`: a function with partial derivatives is constant along a segment on
  which its directional derivative vanishes (characteristics).
* `dx F`, `dt F` are the partial derivatives `fderiv ℝ F p (1,0)`, `fderiv ℝ F p (0,1)`;
  `hasFDerivAt_fderiv_apply`, `differentiable_dx`, `differentiable_dt` (for `C²` functions),
  `dx_dt_comm` (mixed partials commute, Mathlib `ContDiffAt.isSymmSndFDerivAt`), `fderiv_combo`
  (the partial derivative of `a·F − b·G`).
-/

noncomputable section
namespace powerlib.PDE
open Set

/-- `U` has partial derivatives `Ux`, `Ut` (in `x` and `t`) within `S` at `q`. -/
abbrev HasPartialsWithin (U Ux Ut : ℝ × ℝ → ℝ) (S : Set (ℝ × ℝ)) (q : ℝ × ℝ) : Prop :=
  HasFDerivWithinAt U
    (Ux q • ContinuousLinearMap.fst ℝ ℝ ℝ + Ut q • ContinuousLinearMap.snd ℝ ℝ ℝ) S q

/-- The space-time strip `[a, b] × ℝ`. -/
def strip (a b : ℝ) : Set (ℝ × ℝ) := Icc a b ×ˢ univ

/-- A function with partial derivatives is constant along a segment on which its
directional derivative vanishes. -/
@[powerlib_foundation] theorem const_along_segment {U Ux Ut : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    {p₀ d : ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmaps : ∀ s ∈ Icc a b, p₀ + s • d ∈ S)
    (hU : ∀ s ∈ Icc a b, HasPartialsWithin U Ux Ut S (p₀ + s • d))
    (hdir : ∀ s ∈ Icc a b, Ux (p₀ + s • d) * d.1 + Ut (p₀ + s • d) * d.2 = 0) :
    U (p₀ + b • d) = U (p₀ + a • d) := by
  have hderiv : ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun s => U (p₀ + s • d)) 0 (Icc a b) s := by
    intro s hs
    have hγ : HasDerivWithinAt (fun s : ℝ => p₀ + s • d) d (Icc a b) s := by
      have := ((hasDerivAt_id s).smul_const d).const_add p₀
      simpa using this.hasDerivWithinAt
    have hU' : HasFDerivWithinAt U
        (Ux (p₀ + s • d) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Ut (p₀ + s • d) • ContinuousLinearMap.snd ℝ ℝ ℝ) S (p₀ + s • d) := hU s hs
    have h := hU'.comp_hasDerivWithinAt s hγ (fun s hs => hmaps s hs)
    have h0 : (Ux (p₀ + s • d) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Ut (p₀ + s • d) • ContinuousLinearMap.snd ℝ ℝ ℝ) d = 0 := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
      linarith [hdir s hs]
    rw [h0] at h
    exact h
  have hconst := constant_of_has_deriv_right_zero (f := fun s => U (p₀ + s • d))
    (fun s hs => (hderiv s hs).continuousWithinAt)
    (fun s hs => (hderiv s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
    b ⟨hab, le_rfl⟩
  exact hconst

/-- Partial derivative in `x`. -/
def dx (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ F p (1, 0)

/-- Partial derivative in `t`. -/
def dt (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ F p (0, 1)

@[powerlib_foundation] theorem hasFDerivAt_fderiv_apply {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (w p : ℝ × ℝ) :
    HasFDerivAt (fun q => fderiv ℝ F q w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ F) p)) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) p
  exact (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp p hd.hasFDerivAt

@[powerlib_foundation] theorem differentiable_dx {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (dx F) := fun p => (hasFDerivAt_fderiv_apply hF (1, 0) p).differentiableAt

@[powerlib_foundation] theorem differentiable_dt {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (dt F) := fun p => (hasFDerivAt_fderiv_apply hF (0, 1) p).differentiableAt

/-- Mixed partials commute for `C²` functions. -/
@[powerlib_foundation] theorem dx_dt_comm {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 2 F) (p : ℝ × ℝ) :
    dx (dt F) p = dt (dx F) p := by
  unfold dx dt
  rw [(hasFDerivAt_fderiv_apply hF (0, 1) p).fderiv, (hasFDerivAt_fderiv_apply hF (1, 0) p).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)) (1, 0) (0, 1)

/-- Partial derivative of `a·F − b·G`. -/
@[powerlib_foundation] theorem fderiv_combo {F G : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (a b : ℝ) (w p : ℝ × ℝ) :
    fderiv ℝ (fun q => a * F q - b * G q) p w = a * fderiv ℝ F p w - b * fderiv ℝ G p w := by
  rw [fderiv_fun_sub ((hF p).const_mul a) ((hG p).const_mul b), fderiv_const_mul (hF p),
    fderiv_const_mul (hG p)]
  simp

end powerlib.PDE
