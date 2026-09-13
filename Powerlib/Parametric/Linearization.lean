import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.NormNum

/-!
# Local differential identities for periodic linearization

These lemmas derive the state Jacobian, its trajectory/input modulation, and a
quadratic Taylor estimate from genuine derivatives. They do not assert existence
or smooth parameter dependence of a forced periodic orbit: that is a separate
ODE theorem. A supplied parameter path need not be an ODE solution.
-/

noncomputable section

open Set
open scoped Topology

namespace Powerlib.Parametric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The state derivative of a vector field whose joint arguments are `(state, input)`. -/
def stateJacobian (f : E × ℝ → E) (p : E × ℝ) : E →L[ℝ] E :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)

@[simp]
theorem stateJacobian_apply (f : E × ℝ → E) (p : E × ℝ) (v : E) :
    stateJacobian f p v = fderiv ℝ f p (v, 0) := rfl

/-- This definition agrees with differentiation in the state while fixing the input. -/
theorem stateJacobian_hasFDerivAt {f : E × ℝ → E} {p : E × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    HasFDerivAt (fun x ↦ f (x, p.2)) (stateJacobian f p) p.1 := by
  exact hf.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)

/-- Perturbing a state under one fixed prescribed input creates no input-variation term. -/
theorem sameInput_hasDerivAt {f : E × ℝ → E} {x : ℝ → E}
    {s u : ℝ} {v : E} (hf : DifferentiableAt ℝ f (x s, u))
    (hx : HasDerivAt x v s) :
    HasDerivAt (fun r ↦ f (x r, u)) (stateJacobian f (x s, u) v) s := by
  exact (stateJacobian_hasFDerivAt hf).comp_hasDerivAt s hx

/-- Differentiating a directional derivative of a `C²` map gives its Hessian. -/
theorem fderiv_directionalDerivative {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {X : F → E} {p : F}
    (hX : ContDiffAt ℝ 2 X p) (v w : F) :
    fderiv ℝ (fun q ↦ fderiv ℝ X q w) p v =
      fderiv ℝ (fderiv ℝ X) p v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ X) p :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd differentiableAt_const]
  simp

/-- The parameter derivative of a `C²` family of trajectories obeys the homogeneous
variational equation when its prescribed input is independent of that parameter.
The first coordinate of `X` is time and the second is the trajectory parameter.
This theorem derives the variational equation; it does not postulate it. -/
theorem sameInput_variational_identity {f : E × ℝ → E} {X : ℝ × ℝ → E}
    {u : ℝ → ℝ} {p : ℝ × ℝ}
    (hX : ContDiffAt ℝ 2 X p) (hf : DifferentiableAt ℝ f (X p, u p.1))
    (hu : DifferentiableAt ℝ u p.1)
    (hode : ∀ᶠ q in 𝓝 p, fderiv ℝ X q (1, 0) = f (X q, u q.1)) :
    fderiv ℝ (fun q ↦ fderiv ℝ X q (0, 1)) p (1, 0) =
      stateJacobian f (X p, u p.1) (fderiv ℝ X p (0, 1)) := by
  have hpath := (hX.differentiableAt (by norm_num)).hasFDerivAt.prodMk
    (hu.hasFDerivAt.comp p hasFDerivAt_fst)
  have hrhs := hf.hasFDerivAt.comp p hpath
  have heq : (fun q ↦ fderiv ℝ X q (1, 0)) =ᶠ[𝓝 p]
      (fun q ↦ f (X q, u q.1)) := hode
  calc
    fderiv ℝ (fun q ↦ fderiv ℝ X q (0, 1)) p (1, 0) =
        fderiv ℝ (fderiv ℝ X) p (1, 0) (0, 1) :=
      fderiv_directionalDerivative hX _ _
    _ = fderiv ℝ (fderiv ℝ X) p (0, 1) (1, 0) :=
      (hX.isSymmSndFDerivAt (by norm_num)) _ _
    _ = fderiv ℝ (fun q ↦ fderiv ℝ X q (1, 0)) p (0, 1) :=
      (fderiv_directionalDerivative hX _ _).symm
    _ = fderiv ℝ (fun q ↦ f (X q, u q.1)) p (0, 1) := by
      rw [heq.fderiv_eq (𝕜 := ℝ)]
    _ = stateJacobian f (X p, u p.1) (fderiv ℝ X p (0, 1)) := by
      rw [hrhs.fderiv]
      simp

/-- Time-derivative form of `sameInput_variational_identity`. -/
theorem sameInput_variation_hasDerivAt {f : E × ℝ → E} {X : ℝ × ℝ → E}
    {u : ℝ → ℝ} {p : ℝ × ℝ}
    (hX : ContDiffAt ℝ 2 X p) (hf : DifferentiableAt ℝ f (X p, u p.1))
    (hu : DifferentiableAt ℝ u p.1)
    (hode : ∀ᶠ q in 𝓝 p, fderiv ℝ X q (1, 0) = f (X q, u q.1)) :
    HasDerivAt (fun t ↦ fderiv ℝ X (t, p.2) (0, 1))
      (stateJacobian f (X p, u p.1) (fderiv ℝ X p (0, 1))) p.1 := by
  have hd : DifferentiableAt ℝ (fun q ↦ fderiv ℝ X q (0, 1)) p :=
    ((hX.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).clm_apply differentiableAt_const
  have h := hd.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  simpa only [Function.comp_apply, sameInput_variational_identity hX hf hu hode] using h

/-- Three derivatives of the vector field give two derivatives of its state Jacobian. -/
theorem stateJacobian_contDiffAt {f : E × ℝ → E} {p : E × ℝ}
    (hf : ContDiffAt ℝ 3 f p) : ContDiffAt ℝ 2 (stateJacobian f) p := by
  exact (hf.fderiv_right (m := 2) (by norm_num)).clm_comp contDiffAt_const

/-- The corresponding statement on an open neighborhood. -/
theorem stateJacobian_contDiffOn {f : E × ℝ → E} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) :
    ContDiffOn ℝ 2 (stateJacobian f) U := by
  exact (hf.fderiv_of_isOpen hU (m := 2) (by norm_num)).clm_comp contDiffOn_const

/-- The real bilinear state-state derivative. -/
def stateSecond (f : E × ℝ → E) (p : E × ℝ) (v w : E) : E :=
  fderiv ℝ (fderiv ℝ f) p (v, 0) (w, 0)

/-- The real mixed derivative, ordered as state followed by input. -/
def mixedSecond (f : E × ℝ → E) (p : E × ℝ) (w : E) (a : ℝ) : E :=
  fderiv ℝ (fderiv ℝ f) p (w, 0) (0, a)

/-- The Jacobian variation splits into the state-induced and direct-input terms.
Symmetry of the Hessian justifies the mixed-derivative argument order. -/
theorem hessian_state_input_split {f : E × ℝ → E} {p : E × ℝ}
    (hf : ContDiffAt ℝ 3 f p) (v w : E) (a : ℝ) :
    fderiv ℝ (fderiv ℝ f) p (v, a) (w, 0) =
      stateSecond f p v w + mixedSecond f p w a := by
  have hpair : (v, a) = (v, (0 : ℝ)) + ((0 : E), a) := by simp
  rw [hpair, map_add, add_apply]
  congr 1
  exact (hf.isSymmSndFDerivAt (by norm_num)) (0, a) (w, 0)

/-- The operator-valued derivative used in the Taylor estimate has exactly the
state-induced plus direct-input form when applied to a state direction. -/
theorem fderiv_stateJacobian_apply {f : E × ℝ → E} {p : E × ℝ}
    (hf : ContDiffAt ℝ 3 f p) (v w : E) (a : ℝ) :
    fderiv ℝ (stateJacobian f) p (v, a) w =
      stateSecond f p v w + mixedSecond f p w a := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  unfold stateJacobian
  rw [fderiv_clm_comp hdf differentiableAt_const]
  simpa using hessian_state_input_split hf v w a

/-- Differentiate the applied Jacobian along arbitrary differentiable state/input paths.
This proves the two-term modulation formula before complexification. -/
theorem stateJacobian_path_hasDerivAt_apply {f : E × ℝ → E}
    {x : ℝ → E} {u : ℝ → ℝ} {s : ℝ} {v : E} {a : ℝ}
    (hf : ContDiffAt ℝ 3 f (x s, u s))
    (hx : HasDerivAt x v s) (hu : HasDerivAt u a s) (w : E) :
    HasDerivAt (fun r ↦ stateJacobian f (x r, u r) w)
      (stateSecond f (x s, u s) v w + mixedSecond f (x s, u s) w a) s := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (x s, u s) :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have h := (hdf.hasFDerivAt.clm_apply
    (hasFDerivAt_const (w, (0 : ℝ)) (x s, u s))).comp_hasDerivAt s (hx.prodMk hu)
  simpa [Function.comp_def, hessian_state_input_split hf] using h

/-- A local `C³` vector field and a `C²` parameter path yield a uniform, operator-norm
quadratic remainder on a compact amplitude interval. The initial path derivative is
explicit. Existence of a suitable periodic-orbit path is not assumed proved here. -/
theorem stateJacobian_path_taylor {f : E × ℝ → E} {U : Set (E × ℝ)}
    {p : ℝ → E × ℝ} {p₁ : E × ℝ} {a : ℝ}
    (ha : 0 < a) (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    (hp : ContDiffOn ℝ 2 p (Icc 0 a)) (hpU : MapsTo p (Icc 0 a) U)
    (hp₁ : HasDerivAt p p₁ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc 0 a,
      ‖stateJacobian f (p ε) - stateJacobian f (p 0) -
        ε • fderiv ℝ (stateJacobian f) (p 0) p₁‖ ≤ C * ε ^ 2 := by
  let J : ℝ → E →L[ℝ] E := fun ε ↦ stateJacobian f (p ε)
  have hJ : ContDiffOn ℝ 2 J (Icc 0 a) :=
    (stateJacobian_contDiffOn hU hf).comp hp hpU
  have hp0 : p 0 ∈ U := hpU ⟨le_rfl, ha.le⟩
  have hd : HasDerivAt J (fderiv ℝ (stateJacobian f) (p 0) p₁) 0 :=
    ((stateJacobian_contDiffAt (hf.contDiffAt (hU.mem_nhds hp0))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hp₁
  have hdw := hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc ha 0 ⟨le_rfl, ha.le⟩)
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := 1) ha.le hJ
  refine ⟨max C 0, le_max_right _ _, fun ε hε ↦ ?_⟩
  have hbound := hC ε hε
  simp [taylorWithinEval_succ, hdw] at hbound
  change ‖J ε - J 0 - ε • fderiv ℝ (stateJacobian f) (p 0) p₁‖ ≤ _
  rw [sub_sub]
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg ε))

end Powerlib.Parametric
