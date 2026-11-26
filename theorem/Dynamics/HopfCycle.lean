import theorem.Dynamics.HopfDichotomy
import theorem.Dynamics.PlanarHopf
import theorem.Dynamics.CenterManifoldBounded
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Hopf cycles of a one-parameter family in any dimension

The cycle half of the Hopf bifurcation theorem: at a Hopf point with `l₁ ≠ 0` and a transversal
crossing, a family `ẋ = F(x, μ)` on `ℝⁿ` has, for small `μ` on one side, a nonconstant periodic
orbit of amplitude of order `|μ|^{1/2}`.

Scope.
* A family of autonomous ODEs `ẋ = F(x, μ)` on `State n`, `μ ∈ ℝ` constant, with `F(0, μ) = 0`
  for every `μ` (the equilibrium does not move), the augmented field
  `augField F : (x, μ) ↦ (F(x, μ), 0)` on `State (n + 1)` of class `C¹` and analytic at `0`.
  At `μ = 0`: a critical pair `(q, p)` of `F(·, 0)` at the frequency `ω > 0`
  (`NormalForm.LyapunovCoefficient.IsCriticalPair`), the other eigenvalues in the open left
  half-plane (factorized characteristic polynomial), Kuznetsov's first Lyapunov coefficient
  `l₁ = firstLyapunov (F(·, 0)) 0 ω q p ≠ 0`, and transversality: `μ ↦ D_x F(0, μ)` has the
  derivative `B` at `0` with `τ = tr (critπ p ∘ B ∘ critι q) ≠ 0` (`PlanarHopf.paramTrace`;
  `τ = 2 Re ⟨p, B q⟩`, twice the speed at which the real part of the critical eigenvalues
  crosses).
* Periodic orbits are written out in the statements, as in `theorem/NormalForm/Hopf.lean`.
  Existence and the amplitude bound in the critical coordinates `critπ p` are proved here; the
  reduced slices are also controlled on a full neighbourhood of `0`, which gives in
  `theorem/Dynamics/HopfCycleAmplitude.lean` the absence of small cycles for `μ τ l₁ ≥ 0` and
  the amplitude `(1 + o(1)) ν` of every small cycle. Uniqueness up to a time shift and orbital
  stability are not proved (they need `Dh(y) = 2H(y, ·) + o(‖y‖)` for the centre manifold and
  the derivative of the planar return map).
* Generic foundation, independent of any model; no model family is defined.

Source: Hassard–Kazarinoff–Wan, *Theory and Applications of Hopf Bifurcation* (1981), Ch. 1
(the centre manifold of the suspended system `μ̇ = 0`); Carr, *Applications of Centre Manifold
Theory* (1981), §1.5 (dependence on parameters) and §2.4 (small bounded solutions lie on the
centre manifold); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed.), §3.4 (Theorem 3.3) and §5.4; Guckenheimer–Holmes,
*Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector Fields* (1983), §3.4.

Results.
* The augmented state: `xpart`, `mpart`, `xin`, `emu` (`z = (x, 0) + μ (0, 1)`,
  `xin_add_smul`, `ext_iff_parts`), `augField`, `augL`, `augP`, `augι`, `augπ`.
* `expFlow_augL` (the flow of `(x, μ) ↦ (Ax, 0)` is `(x, μ) ↦ (e^{tA}x, μ)`),
  `exists_dichotomy_aug`, `isCommutingProjection_aug`, `isChart_aug`: the parameter axis joins
  the centre, the dichotomy of `A` carries over.
* `fderiv_augField_zero` (`D(augField F)(0) = augL (D_x F(0, 0))` when `F(0, μ) ≡ 0`),
  `fderiv_augField_apply`, `fderiv_fderiv_augField_emu`, `fderiv_fderiv_augField_xin_emu`
  (the mixed second derivative is `B`), `taylor_restrict` (on `(x, 0)` the quadratic and cubic
  Taylor terms are those of `F(·, 0)`), `eq_zero_of_isBigO_quad_cubic` (uniqueness of
  homogeneous parts), `jet_congr`, `l1_congr` (`l₁` depends only on the cubic polynomial).
* `sliceField`, `sliceM`, `sliceQ`, `sliceC`, `unfoldRem_slice_eq`, `isLittleO_unfoldRem_slice`,
  `exists_lipschitzOnWith_slice`: a field on `(u, μ) ∈ ℝ³` with a cubic expansion gives the
  planar family of `theorem/Dynamics/PlanarHopf.lean`, uniformly in `μ`.
* `xpart_emu_emu_eq_zero`, `isLittleO_unfoldRem_slice_full`: if moreover the slices are linearly
  approximated near `0` (`‖g(μ, u) − R u − μ M u‖ ≤ ε|μ|‖u‖ + C_q‖u‖²`), the slice remainder is
  `o(|μ| ‖u‖ + ‖u‖³)` on a full neighbourhood of `0` (no restriction `|μ| ≤ K‖u‖²`).
* `chartField_aug_eq` (`G(y) = π Φ(ι y + h(ι y))`), `norm_taylor_le_of_lipschitzOn`
  (second-order Taylor bound from a Lipschitz derivative), `slice_sub_eq`, `slice_linear_bound`:
  for a graph map with strict derivative `0` at `0` containing the equilibria `(0, μ)`, the
  slices of the reduced field satisfy that linear approximation (`Φ` analytic at `0`).
* `chartQ`, `chartC`, `sliceM_chartQ` (the `μu` term of the reduced field is
  `critπ p ∘ B ∘ critι q`), `l1_slice_eq` (its `l₁` is Kuznetsov's `l₁` of `F(·, 0)`).
* `reducedSlice_bounded`, `exists_reducedSlice`: the parameter-dependent centre manifold (the
  `C¹` centre manifold of the augmented field containing its small bounded solutions,
  `CenterManifold.exists_centerManifold_bounded`): the reduced field on `(u, μ)` keeps `μ`
  constant, its slices have the unfolded expansion with `M = critπ p ∘ B ∘ critι q` and `l₁` of
  `F(·, 0)` (along `|μ| ≤ K‖u‖²`, and with remainder `o(|μ| ‖u‖ + ‖u‖³)` on a full
  neighbourhood), are Lipschitz on a fixed disc; small reduced solutions lift to solutions of the
  augmented field with the same parameter and critical coordinates, and every whole-line solution
  of the augmented field in a small ball is such a lift (`Λ(π z(t)) = z(t)`).
* `exists_hopfCycle`: for every small `μ` with `μ τ l₁ < 0`, a nonconstant periodic orbit of
  `F(·, μ)`, period at most `4π/ω`, with `ν/8 ≤ ‖critπ p x(t)‖² ≤ 8ν`, `ν = −μτ/(ω l₁)`.
-/

noncomputable section
namespace powerlib.Dynamics.HopfCycle
open Set Filter Topology Asymptotics
open powerlib.Dynamics.LyapunovPerron (expFlow expFlow_zero hasDerivAt_expFlow expFlow_mul_comm
  expFlow_mul_neg)
open powerlib.Dynamics.CenterManifold (IsCommutingProjection IsChart taylor3_isBigO)

/-! ## The augmented state `(x, μ)` -/

section Coordinates

variable {n : ℕ}

/-- The state part `x` of `z = (x, μ) ∈ ℝⁿ⁺¹`. -/
def xpart : State (n + 1) →L[ℝ] State n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => z (Fin.castSucc i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The parameter part `μ` of `z = (x, μ)`. -/
def mpart : State (n + 1) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last n)

/-- The embedding `x ↦ (x, 0)`. -/
def xin : State n →L[ℝ] State (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => Fin.lastCases (0 : ℝ) (fun i => x i) j)
      map_add' := fun x y => by
        ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      map_smul' := fun c x => by
        ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }

/-- The parameter direction `(0, 1)`. -/
def emu : State (n + 1) := EuclideanSpace.single (Fin.last n) 1

@[tmio T, simp, powerlib_foundation] theorem xpart_apply (z : State (n + 1)) (i : Fin n) :
    xpart z i = z (Fin.castSucc i) := rfl

@[tmio T, powerlib_foundation] theorem mpart_apply (z : State (n + 1)) :
    mpart z = z (Fin.last n) := rfl

@[tmio T, simp, powerlib_foundation] theorem xin_apply_castSucc (x : State n) (i : Fin n) :
    xin x (Fin.castSucc i) = x i := by
  simp [xin]

@[tmio T, simp, powerlib_foundation] theorem xin_apply_last (x : State n) :
    xin x (Fin.last n) = 0 := by
  simp [xin]

@[tmio T, simp, powerlib_foundation] theorem emu_apply_castSucc (i : Fin n) :
    (emu : State (n + 1)) (Fin.castSucc i) = 0 := by
  simp [emu, Fin.castSucc_ne_last]

@[tmio T, simp, powerlib_foundation] theorem emu_apply_last :
    (emu : State (n + 1)) (Fin.last n) = 1 := by
  simp [emu]

@[tmio T, simp, powerlib_foundation] theorem xpart_xin (x : State n) : xpart (xin x) = x := by
  ext i; simp

@[tmio T, simp, powerlib_foundation] theorem mpart_xin (x : State n) : mpart (xin x) = 0 := by
  simp [mpart_apply]

@[tmio T, simp, powerlib_foundation] theorem xpart_emu : xpart (emu : State (n + 1)) = 0 := by
  ext i; simp

@[tmio T, simp, powerlib_foundation] theorem mpart_emu : mpart (emu : State (n + 1)) = 1 := by
  simp [mpart_apply]

/-- `z = (x, 0) + μ (0, 1)`. -/
@[tmio T, powerlib_foundation] theorem xin_add_smul (z : State (n + 1)) :
    xin (xpart z) + mpart z • emu = z := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [mpart_apply]

@[tmio T, powerlib_foundation] theorem ext_iff_parts {z w : State (n + 1)} :
    z = w ↔ xpart z = xpart w ∧ mpart z = mpart w := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← xin_add_smul z, ← xin_add_smul w, h1, h2]

/-- The parameter projection `z ↦ μ (0, 1)`. -/
def projM : State (n + 1) →L[ℝ] State (n + 1) := mpart.smulRight emu

@[tmio T, simp, powerlib_foundation] theorem projM_apply (z : State (n + 1)) :
    projM z = mpart z • emu := rfl

/-- The augmented field `(x, μ) ↦ (F(x, μ), 0)`. -/
def augField (F : State n → ℝ → State n) (z : State (n + 1)) : State (n + 1) :=
  xin (F (xpart z) (mpart z))

/-- The augmented linear map `(x, μ) ↦ (A x, 0)`. -/
def augL (A : State n →L[ℝ] State n) : State (n + 1) →L[ℝ] State (n + 1) :=
  xin.comp (A.comp xpart)

/-- The augmented projection `(x, μ) ↦ (P x, μ)`. -/
def augP (P : State n →L[ℝ] State n) : State (n + 1) →L[ℝ] State (n + 1) :=
  xin.comp (P.comp xpart) + projM

@[tmio T, simp, powerlib_foundation] theorem augL_apply (A : State n →L[ℝ] State n)
    (z : State (n + 1)) : augL A z = xin (A (xpart z)) := rfl

@[tmio T, simp, powerlib_foundation] theorem augP_apply (P : State n →L[ℝ] State n)
    (z : State (n + 1)) : augP P z = xin (P (xpart z)) + mpart z • emu := rfl

end Coordinates

/-! ## The flow and the dichotomy of the augmented linear part -/

section Flow

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- The candidate flow `(x, μ) ↦ (e^{tA} x, μ)`. -/
def augFlow (A : State n →L[ℝ] State n) (t : ℝ) : State (n + 1) →L[ℝ] State (n + 1) :=
  xin.comp ((expFlow A t).comp xpart) + projM

@[tmio T, powerlib_foundation] theorem expFlow_augL (t : ℝ) :
    expFlow (augL A) t = augFlow A t := by
  set E : ℝ → State (n + 1) →L[ℝ] State (n + 1) := augFlow A with hE
  have hEd : ∀ s, HasDerivAt E (xin.comp ((expFlow A s * A).comp xpart)) s := by
    intro s
    have h1 := (hasDerivAt_expFlow (A := A) s)
    have h2 : HasDerivAt (fun s => xin.comp ((expFlow A s).comp xpart))
        (xin.comp ((expFlow A s * A).comp xpart)) s := by
      have := (hasDerivAt_const s xin).clm_comp (h1.clm_comp (hasDerivAt_const s xpart))
      convert this using 1
      rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, add_zero, zero_add]
    exact h2.add_const projM
  have hAE : ∀ s, augL A * E s = xin.comp ((expFlow A s * A).comp xpart) := by
    intro s
    ext1 z
    have hc : (expFlow A s * A) (xpart z) = (A * expFlow A s) (xpart z) := by
      rw [expFlow_mul_comm]
    show xin (A (xpart (xin (expFlow A s (xpart z)) + mpart z • emu))) =
      xin ((expFlow A s * A) (xpart z))
    rw [map_add, map_smul, xpart_xin, xpart_emu, smul_zero, add_zero, hc]
    rfl
  have hG : ∀ s, HasDerivAt (fun s => expFlow (augL A) (-s) * E s) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => expFlow (augL A) (-s)) (-(expFlow (augL A) (-s) * augL A))
        s := by
      have := (hasDerivAt_expFlow (A := augL A) (-s)).scomp s (hasDerivAt_neg s)
      rw [neg_one_smul] at this
      exact this
    refine (h1.mul (hEd s)).congr_deriv ?_
    rw [← hAE s, neg_mul, mul_assoc]
    abel
  have hconst : ∀ s, expFlow (augL A) (-s) * E s = expFlow (augL A) (-0) * E 0 := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt) (fun s => (hG s).deriv) s 0
  have h0 : E 0 = 1 := by
    ext1 z
    show xin (expFlow A 0 (xpart z)) + mpart z • emu = z
    rw [expFlow_zero]
    exact xin_add_smul z
  have h00 : expFlow (augL A) (-0) * E 0 = 1 := by simp [h0, expFlow_zero]
  calc expFlow (augL A) t = expFlow (augL A) t * (expFlow (augL A) (-t) * E t) := by
        rw [hconst, h00, mul_one]
    _ = E t := by rw [← mul_assoc, expFlow_mul_neg, one_mul]

end Flow

section Norms

variable {n : ℕ}

@[tmio T, powerlib_foundation] theorem norm_xin (x : State n) : ‖xin x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]
  simp

@[tmio T, powerlib_foundation] theorem norm_xpart_le (z : State (n + 1)) : ‖xpart z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]
  apply Real.sqrt_le_sqrt
  simp only [xpart_apply]
  linarith [sq_nonneg ‖z (Fin.last n)‖]

@[tmio T, powerlib_foundation] theorem norm_emu : ‖(emu : State (n + 1))‖ = 1 := by
  simp [emu]

@[tmio T, powerlib_foundation] theorem norm_xin_add_smul_le (x : State n) (μ : ℝ) :
    ‖xin x + μ • (emu : State (n + 1))‖ ≤ ‖x‖ + |μ| := by
  calc ‖xin x + μ • (emu : State (n + 1))‖ ≤ ‖xin x‖ + ‖μ • (emu : State (n + 1))‖ :=
        norm_add_le _ _
    _ = ‖x‖ + |μ| := by rw [norm_xin, norm_smul, norm_emu, mul_one, Real.norm_eq_abs]

end Norms

section Dichotomy

variable {n : ℕ} {A P : State n →L[ℝ] State n}

@[tmio T, powerlib_foundation] theorem isCommutingProjection_aug (hP : IsCommutingProjection A P) :
    IsCommutingProjection (augL A) (augP P) :=
  ⟨fun z => by simp [hP.idem], fun z => by simp [hP.comm]⟩

@[tmio T, powerlib_foundation] theorem expFlow_augL_mul_augP (t : ℝ) :
    expFlow (augL A) t * augP P = xin.comp ((expFlow A t * P).comp xpart) + projM := by
  rw [expFlow_augL]
  ext1 z
  show xin (expFlow A t (xpart (xin (P (xpart z)) + mpart z • emu))) +
      mpart (xin (P (xpart z)) + mpart z • emu) • emu = xin (expFlow A t (P (xpart z))) +
      mpart z • emu
  simp

@[tmio T, powerlib_foundation] theorem expFlow_augL_mul_one_sub_augP (t : ℝ) :
    expFlow (augL A) t * (1 - augP P) = xin.comp ((expFlow A t * (1 - P)).comp xpart) := by
  rw [expFlow_augL]
  ext1 z
  show xin (expFlow A t (xpart (z - (xin (P (xpart z)) + mpart z • emu)))) +
      mpart (z - (xin (P (xpart z)) + mpart z • emu)) • emu =
      xin (expFlow A t (xpart z - P (xpart z)))
  simp

@[tmio T, powerlib_foundation] theorem norm_xin_comp_le (T : State n →L[ℝ] State n) :
    ‖xin.comp (T.comp (xpart : State (n + 1) →L[ℝ] State n))‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, norm_xin]
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_xpart_le z) (norm_nonneg _))

@[tmio T, powerlib_foundation] theorem norm_projM_le : ‖(projM : State (n + 1) →L[ℝ] _)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [projM_apply, norm_smul, norm_emu, mul_one, one_mul, mpart_apply, Real.norm_eq_abs]
  exact (PiLp.norm_apply_le z (Fin.last n)).trans_eq' (by rw [Real.norm_eq_abs])

/-- **The dichotomy of the augmented linear part.** The flow is `(x, μ) ↦ (e^{tA}x, μ)`, so a
centre–stable dichotomy of `A` with respect to `P` gives one of `augL A` with respect to
`augP P` (the parameter direction joins the centre). -/
@[tmio T, powerlib_foundation] theorem exists_dichotomy_aug {K ε β : ℝ} (hε : 0 ≤ ε)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) :
    ∃ K' : ℝ, (∀ t, ‖expFlow (augL A) t * augP P‖ ≤ K' * Real.exp (ε * |t|)) ∧
      ∀ t, 0 ≤ t → ‖expFlow (augL A) t * (1 - augP P)‖ ≤ K' * Real.exp (-(β * t)) := by
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hst 0 le_rfl)
    simpa using this
  refine ⟨K + 1, fun t => ?_, fun t ht => ?_⟩
  · rw [expFlow_augL_mul_augP]
    have he : 1 ≤ Real.exp (ε * |t|) := Real.one_le_exp (by positivity)
    calc ‖xin.comp ((expFlow A t * P).comp xpart) + projM‖
        ≤ ‖xin.comp ((expFlow A t * P).comp (xpart : State (n + 1) →L[ℝ] State n))‖ +
          ‖(projM : State (n + 1) →L[ℝ] _)‖ := norm_add_le _ _
      _ ≤ K * Real.exp (ε * |t|) + 1 * Real.exp (ε * |t|) := by
          gcongr
          · exact (norm_xin_comp_le _).trans (hcen t)
          · exact norm_projM_le.trans (by linarith)
      _ = (K + 1) * Real.exp (ε * |t|) := by ring
  · rw [expFlow_augL_mul_one_sub_augP]
    calc _ ≤ K * Real.exp (-(β * t)) := (norm_xin_comp_le _).trans (hst t ht)
      _ ≤ (K + 1) * Real.exp (-(β * t)) := by gcongr; linarith

end Dichotomy

section Chart

variable {n m : ℕ}

/-- The augmented chart `(y, μ) ↦ (ι y, μ)`. -/
def augι (ι : State m →L[ℝ] State n) : State (m + 1) →L[ℝ] State (n + 1) :=
  xin.comp (ι.comp xpart) + (mpart : State (m + 1) →L[ℝ] ℝ).smulRight emu

/-- The augmented coordinates `(x, μ) ↦ (π x, μ)`. -/
def augπ (π : State n →L[ℝ] State m) : State (n + 1) →L[ℝ] State (m + 1) :=
  xin.comp (π.comp xpart) + (mpart : State (n + 1) →L[ℝ] ℝ).smulRight emu

@[tmio T, simp, powerlib_foundation] theorem augι_apply (ι : State m →L[ℝ] State n)
    (y : State (m + 1)) : augι ι y = xin (ι (xpart y)) + mpart y • emu := rfl

@[tmio T, simp, powerlib_foundation] theorem augπ_apply (π : State n →L[ℝ] State m)
    (z : State (n + 1)) : augπ π z = xin (π (xpart z)) + mpart z • emu := rfl

@[tmio T, powerlib_foundation] theorem isChart_aug {P : State n →L[ℝ] State n}
    {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m} (hc : IsChart P ι π) :
    IsChart (augP P) (augι ι) (augπ π) :=
  ⟨fun y => by
    rw [ext_iff_parts]
    simp [hc.left_inv],
   fun z => by
    rw [ext_iff_parts]
    simp [hc.ι_π]⟩

end Chart

section Family

variable {n : ℕ} {F : State n → ℝ → State n}

@[tmio T, simp, powerlib_foundation] theorem xpart_augField (z : State (n + 1)) :
    xpart (augField F z) = F (xpart z) (mpart z) := by simp [augField]

@[tmio T, simp, powerlib_foundation] theorem mpart_augField (z : State (n + 1)) :
    mpart (augField F z) = 0 := by simp [augField]

/-- **The linear part of the augmented field.** If `F(0, μ) = 0` for every `μ`, the derivative of
`(x, μ) ↦ (F(x, μ), 0)` at `0` is `(x, μ) ↦ (A x, 0)`, `A = D_x F(0, 0)`. -/
@[tmio T, powerlib_foundation] theorem fderiv_augField_zero
    (hF : DifferentiableAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0) :
    fderiv ℝ (augField F) 0 = augL (fderiv ℝ (fun x => F x 0) 0) := by
  set D := fderiv ℝ (augField F) 0 with hDdef
  have hD : HasFDerivAt (augField F) D 0 := hF.hasFDerivAt
  have hF₀ : (fun x => F x 0) = fun x => xpart (augField F (xin x)) := by
    funext x; simp
  have hd0 : HasFDerivAt (fun x => F x 0) (xpart.comp (D.comp xin)) 0 := by
    rw [hF₀]
    have h1 : HasFDerivAt (augField F) D (xin (0 : State n)) := by rw [map_zero]; exact hD
    exact xpart.hasFDerivAt.comp _ (h1.comp _ xin.hasFDerivAt)
  have hemu : D emu = 0 := by
    have h1 : HasDerivAt (fun s : ℝ => augField F (s • emu)) (D emu) 0 := by
      have h2 : HasDerivAt (fun s : ℝ => s • (emu : State (n + 1))) emu 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (emu : State (n + 1))
      have h3 : HasFDerivAt (augField F) D ((0 : ℝ) • (emu : State (n + 1))) := by
        rw [zero_smul]; exact hD
      exact h3.comp_hasDerivAt 0 h2
    have h4 : (fun s : ℝ => augField F (s • emu)) = fun _ => 0 := by
      funext s
      rw [ext_iff_parts]
      simp [hF0]
    rw [h4] at h1
    exact h1.unique (hasDerivAt_const _ _)
  have hm : (mpart : State (n + 1) →L[ℝ] ℝ).comp D = 0 := by
    have h1 : HasFDerivAt (fun z => mpart (augField F z)) (mpart.comp D) 0 :=
      mpart.hasFDerivAt.comp _ hD
    have h2 : (fun z => mpart (augField F z)) = fun _ => (0 : ℝ) := funext fun z => by simp
    rw [h2] at h1
    exact h1.unique (hasFDerivAt_const _ _)
  ext1 z
  rw [hd0.fderiv]
  conv_lhs => rw [← xin_add_smul z]
  rw [map_add, map_smul, hemu, smul_zero, add_zero, augL_apply]
  rw [ext_iff_parts]
  refine ⟨by simp, ?_⟩
  have := congrArg (fun T : State (n + 1) →L[ℝ] ℝ => T (xin (xpart z))) hm
  simpa using this

end Family

/-! ## Uniqueness of the quadratic and cubic parts -/

section Uniqueness

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- **Homogeneous parts are unique.** If `Q(x, x) + C(x, x, x) = O(‖x‖⁴)` at `0`, then
`Q(x, x) = 0` and `C(x, x, x) = 0` for every `x`. -/
@[tmio T, powerlib_foundation] theorem eq_zero_of_isBigO_quad_cubic {Q : E →L[ℝ] E →L[ℝ] V}
    {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) V}
    (h : (fun x => Q x x + C ![x, x, x]) =O[𝓝 0] fun x => ‖x‖ ^ 4) (x : E) :
    Q x x = 0 ∧ C ![x, x, x] = 0 := by
  obtain ⟨c, hc⟩ := h.bound
  have hseg : Tendsto (fun t : ℝ => t • x) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 ((0 : ℝ) • x)) := tendsto_id.smul_const x
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hC3 : ∀ t : ℝ, C ![t • x, t • x, t • x] = t ^ 3 • C ![x, x, x] := by
    intro t
    have e : (![t • x, t • x, t • x] : Fin 3 → E) = fun i => t • (![x, x, x] : Fin 3 → E) i := by
      funext i; fin_cases i <;> rfl
    rw [e, C.map_smul_univ]
    simp
  have e1 : ∀ t : ℝ, Q (t • x) (t • x) + C ![t • x, t • x, t • x] =
      (t ^ 2) • (Q x x + t • C ![x, x, x]) := by
    intro t
    simp only [map_smul, _root_.smul_apply, hC3]
    module
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖Q x x + t • C ![x, x, x]‖ ≤ c * ‖x‖ ^ 4 * t ^ 2 := by
    filter_upwards [hseg.eventually hc, self_mem_nhdsWithin] with t ht htpos
    have htp : (0 : ℝ) < t := htpos
    simp only [e1 t, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos htp] at ht
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ t * ‖x‖)] at ht
    have ht2 : 0 < t ^ 2 := by positivity
    have : t ^ 2 * ‖Q x x + t • C ![x, x, x]‖ ≤ t ^ 2 * (c * ‖x‖ ^ 4 * t ^ 2) :=
      ht.trans_eq (by ring)
    exact le_of_mul_le_mul_left this ht2
  have hlim1 : Tendsto (fun t : ℝ => ‖Q x x + t • C ![x, x, x]‖) (𝓝[>] 0) (𝓝 ‖Q x x‖) := by
    have : Tendsto (fun t : ℝ => Q x x + t • C ![x, x, x]) (𝓝 0)
        (𝓝 (Q x x + (0 : ℝ) • C ![x, x, x])) :=
      tendsto_const_nhds.add (tendsto_id.smul_const _)
    rw [zero_smul, add_zero] at this
    exact (this.norm).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun t : ℝ => c * ‖x‖ ^ 4 * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => c * ‖x‖ ^ 4 * t ^ 2) (𝓝 0) (𝓝 (c * ‖x‖ ^ 4 * 0 ^ 2)) :=
      tendsto_const_nhds.mul ((continuous_pow 2).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hQ : Q x x = 0 := norm_le_zero_iff.mp (le_of_tendsto_of_tendsto hlim1 hlim2 hev)
  refine ⟨hQ, ?_⟩
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖C ![x, x, x]‖ ≤ c * ‖x‖ ^ 4 * t := by
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
    have htp : (0 : ℝ) < t := htpos
    rw [hQ, zero_add, norm_smul, Real.norm_of_nonneg htp.le] at ht
    have : t * ‖C ![x, x, x]‖ ≤ t * (c * ‖x‖ ^ 4 * t) := by nlinarith
    exact le_of_mul_le_mul_left this htp
  have hlim3 : Tendsto (fun t : ℝ => c * ‖x‖ ^ 4 * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => c * ‖x‖ ^ 4 * t) (𝓝 0) (𝓝 (c * ‖x‖ ^ 4 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa using this.mono_left nhdsWithin_le_nhds
  exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hlim3 hev2)

end Uniqueness

section JetCongr

open powerlib.Dynamics.Degenerate.PlanarFocus

variable {L : State 2 →L[ℝ] State 2} {ω : ℝ}

/-- The planar jet, hence `l₁`, depends only on the cubic polynomial `Q(u, u) + C(u, u, u)`. -/
@[tmio T, powerlib_foundation] theorem jet_congr {Q Q' : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
    {C C' : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)}
    (h : ∀ u, Q u u + C ![u, u, u] = Q' u u + C' ![u, u, u]) :
    jet L Q C ω = jet L Q' C' ω := by
  have key : ∀ ℓ : State 2 →L[ℝ] ℝ,
      ℓ (Q (frameVec0 L) (frameVec0 L)) = ℓ (Q' (frameVec0 L) (frameVec0 L)) ∧
      ℓ (Q (frameVec0 L) (frameVec1 L ω) + Q (frameVec1 L ω) (frameVec0 L)) =
        ℓ (Q' (frameVec0 L) (frameVec1 L ω) + Q' (frameVec1 L ω) (frameVec0 L)) ∧
      ℓ (Q (frameVec1 L ω) (frameVec1 L ω)) = ℓ (Q' (frameVec1 L ω) (frameVec1 L ω)) ∧
      ℓ (C ![frameVec0 L, frameVec0 L, frameVec0 L]) =
        ℓ (C' ![frameVec0 L, frameVec0 L, frameVec0 L]) ∧
      ℓ (C ![frameVec0 L, frameVec0 L, frameVec1 L ω] +
          C ![frameVec0 L, frameVec1 L ω, frameVec0 L] +
          C ![frameVec1 L ω, frameVec0 L, frameVec0 L]) =
        ℓ (C' ![frameVec0 L, frameVec0 L, frameVec1 L ω] +
          C' ![frameVec0 L, frameVec1 L ω, frameVec0 L] +
          C' ![frameVec1 L ω, frameVec0 L, frameVec0 L]) ∧
      ℓ (C ![frameVec0 L, frameVec1 L ω, frameVec1 L ω] +
          C ![frameVec1 L ω, frameVec0 L, frameVec1 L ω] +
          C ![frameVec1 L ω, frameVec1 L ω, frameVec0 L]) =
        ℓ (C' ![frameVec0 L, frameVec1 L ω, frameVec1 L ω] +
          C' ![frameVec1 L ω, frameVec0 L, frameVec1 L ω] +
          C' ![frameVec1 L ω, frameVec1 L ω, frameVec0 L]) ∧
      ℓ (C ![frameVec1 L ω, frameVec1 L ω, frameVec1 L ω]) =
        ℓ (C' ![frameVec1 L ω, frameVec1 L ω, frameVec1 L ω]) := by
    intro ℓ
    have hp : ∀ a b : ℝ, _ := fun a b =>
      (functional_cubic (Q := Q) (C := C) ℓ (frameVec0 L) (frameVec1 L ω) a b).symm.trans
        ((congrArg ℓ (h (a • frameVec0 L + b • frameVec1 L ω))).trans
          (functional_cubic (Q := Q') (C := C') ℓ (frameVec0 L) (frameVec1 L ω) a b))
    have h1 := hp 1 0
    have h2 := hp (-1) 0
    have h3 := hp 0 1
    have h4 := hp 0 (-1)
    have h5 := hp 1 1
    have h6 := hp 1 (-1)
    have h7 := hp (-1) 1
    norm_num at h1 h2 h3 h4 h5 h6 h7
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [map_add]) <;> linarith
  obtain ⟨x1, x2, x3, x4, x5, x6, x7⟩ := key frameX
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := key (frameY L ω)
  simp only [jet, x1, x2, x3, x4, x5, x6, x7, y1, y2, y3, y4, y5, y6, y7]

@[tmio T, powerlib_foundation] theorem l1_congr {Q Q' : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
    {C C' : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)}
    (h : ∀ u, Q u u + C ![u, u, u] = Q' u u + C' ![u, u, u]) :
    l1 L Q C ω = l1 L Q' C' ω := by
  rw [l1, l1, jet_congr h]

end JetCongr

/-! ## From a field on `(u, μ)` to the unfolded planar family -/

section Slice

open powerlib.Dynamics.CenterManifold (rotL isBigO_trilin trilin_add_zero trilin_add_one
  trilin_add_two)
open powerlib.Dynamics.PlanarHopf (nhdsW unfoldRem tendsto_nhdsW isBigO_nhdsW_fst)

/-- The planar family `g(μ, u) = x-part of G(u, μ)` of a field `G` on `(u, μ) ∈ ℝ³`. -/
def sliceField (G : State (2 + 1) → State (2 + 1)) (μ : ℝ) (u : State 2) : State 2 :=
  xpart (G (xin u + μ • emu))

variable (Q₃ : State (2 + 1) →L[ℝ] State (2 + 1) →L[ℝ] State (2 + 1))
  (C₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State (2 + 1)) (State (2 + 1)))

/-- The mixed term `M u = x-part of Q₃((u, 0), (0, 1)) + Q₃((0, 1), (u, 0))`. -/
def sliceM : State 2 →L[ℝ] State 2 :=
  xpart.comp ((Q₃.flip emu).comp xin + (Q₃ emu).comp xin)

/-- The quadratic part at `μ = 0`. -/
def sliceQ : State 2 →L[ℝ] State 2 →L[ℝ] State 2 :=
  (ContinuousLinearMap.compL ℝ (State 2) (State (2 + 1)) (State 2) xpart).comp
    (Q₃.bilinearComp xin xin)

/-- The cubic part at `μ = 0`. -/
def sliceC : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2) :=
  xpart.compContinuousMultilinearMap (C₃.compContinuousLinearMap fun _ => xin)

@[tmio T, powerlib_foundation] theorem sliceM_apply (u : State 2) :
    sliceM Q₃ u = xpart (Q₃ (xin u) emu + Q₃ emu (xin u)) := by
  simp [sliceM]

@[tmio T, powerlib_foundation] theorem sliceQ_apply (u v : State 2) :
    sliceQ Q₃ u v = xpart (Q₃ (xin u) (xin v)) := by
  simp [sliceQ]

@[tmio T, powerlib_foundation] theorem sliceC_apply (u : State 2) :
    sliceC C₃ ![u, u, u] = xpart (C₃ ![xin u, xin u, xin u]) := by
  have e : (fun i => xin ((![u, u, u] : Fin 3 → State 2) i)) = ![xin u, xin u, xin u] := by
    funext i; fin_cases i <;> rfl
  simp only [sliceC, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, e]

variable {Q₃ C₃} {ω : ℝ} {G : State (2 + 1) → State (2 + 1)}
  {L₃ : State (2 + 1) →L[ℝ] State (2 + 1)}

/-- The decomposition of the slice remainder: the remainder of the expansion of `G`, the `μ²`
term and the cubic terms with a factor `μ`. -/
@[tmio T, powerlib_foundation] theorem unfoldRem_slice_eq
    (hL : ∀ (u : State 2) (μ : ℝ), xpart (L₃ (xin u + μ • emu)) = rotL ω u) (μ : ℝ)
    (u : State 2) :
    unfoldRem (sliceM Q₃) (sliceQ Q₃) (sliceC C₃) ω (sliceField G) μ u =
      xpart (G (xin u + μ • emu) - (L₃ (xin u + μ • emu) +
        Q₃ (xin u + μ • emu) (xin u + μ • emu) +
          C₃ ![xin u + μ • emu, xin u + μ • emu, xin u + μ • emu])) +
        (μ ^ 2) • xpart (Q₃ emu emu) +
      xpart (C₃ ![μ • emu, xin u + μ • emu, xin u + μ • emu] +
        C₃ ![xin u, μ • emu, xin u + μ • emu] + C₃ ![xin u, xin u, μ • emu]) := by
  set Y := xin u + μ • emu with hY
  have hC : C₃ ![Y, Y, Y] = C₃ ![xin u, xin u, xin u] +
      (C₃ ![μ • emu, Y, Y] + C₃ ![xin u, μ • emu, Y] + C₃ ![xin u, xin u, μ • emu]) := by
    simp only [hY]
    rw [trilin_add_zero, trilin_add_one, trilin_add_two]
    abel
  have hQ : Q₃ Y Y = Q₃ (xin u) (xin u) + μ • (Q₃ (xin u) emu + Q₃ emu (xin u)) +
      (μ ^ 2) • Q₃ emu emu := by
    simp only [hY, map_add, map_smul, _root_.add_apply, _root_.smul_apply]
    module
  have hLp : xpart (L₃ Y) = rotL ω u := hL u μ
  simp only [unfoldRem, sliceField, sliceM_apply, sliceQ_apply, sliceC_apply]
  rw [← hY, hC, hQ]
  simp only [map_add, map_sub, map_smul, hLp]
  abel

/-- **The unfolded expansion of a slice.** If `G(y) = L₃ y + Q₃(y, y) + C₃(y, y, y) + o(‖y‖³)` on
`(u, μ) ∈ ℝ³` and the `x`-part of `L₃(u, μ)` is `R u`, then the planar family
`g(μ, u) = x-part of G(u, μ)` has the unfolded expansion of
`theorem/Dynamics/PlanarHopf.lean` with `M = sliceM`, `Q = sliceQ`, `C = sliceC`, along every
`nhdsW K` (`μ²`, `μ‖u‖²`, `μ²‖u‖`, `μ³` and `o(‖(u, μ)‖³)` are `o(‖u‖³)` there). -/
@[tmio T, powerlib_foundation] theorem isLittleO_unfoldRem_slice
    (hexp : (fun y => G y - (L₃ y + Q₃ y y + C₃ ![y, y, y])) =o[𝓝 0] fun y => ‖y‖ ^ 3)
    (hL : ∀ (u : State 2) (μ : ℝ), xpart (L₃ (xin u + μ • emu)) = rotL ω u) (K : ℝ) :
    (fun p : ℝ × State 2 => unfoldRem (sliceM Q₃) (sliceQ Q₃) (sliceC C₃) ω (sliceField G) p.1
      p.2) =o[nhdsW K] fun p => ‖p.2‖ ^ 3 := by
  set Y : ℝ × State 2 → State (2 + 1) := fun p => xin p.2 + p.1 • emu with hY
  set E : State (2 + 1) → State (2 + 1) := fun y => G y - (L₃ y + Q₃ y y + C₃ ![y, y, y])
    with hE
  have key : ∀ p : ℝ × State 2,
      unfoldRem (sliceM Q₃) (sliceQ Q₃) (sliceC C₃) ω (sliceField G) p.1 p.2 =
        xpart (E (Y p)) + (p.1 ^ 2) • xpart (Q₃ emu emu) +
        xpart (C₃ ![p.1 • emu, Y p, Y p] + C₃ ![xin p.2, p.1 • emu, Y p] +
          C₃ ![xin p.2, xin p.2, p.1 • emu]) := fun p => unfoldRem_slice_eq hL p.1 p.2
  have hYt : Tendsto Y (nhdsW K) (𝓝 0) := by
    have hc : Continuous Y := by
      simp only [hY]; fun_prop
    have h0 : Y 0 = 0 := by simp [hY]
    have := hc.tendsto 0
    rw [h0] at this
    exact this.mono_left inf_le_left
  have hμ : (fun p : ℝ × State 2 => ‖p.1 • (emu : State (2 + 1))‖) =O[nhdsW K]
      fun p => ‖p.2‖ ^ 2 := by
    refine ((isBigO_nhdsW_fst K).norm_left).congr_left fun p => ?_
    rw [norm_smul, norm_emu, mul_one]
  have hμ1 : (fun p : ℝ × State 2 => ‖p.1 • (emu : State (2 + 1))‖) =O[nhdsW K]
      fun p => ‖p.2‖ :=
    (hμ.trans (Dynamics.isBigO_pow_of_tendsto (tendsto_nhdsW K) (by norm_num : 1 ≤ 2))).congr_right
      fun p => pow_one _
  have hx0 : (fun p : ℝ × State 2 => ‖xin p.2‖) =O[nhdsW K] fun p => ‖p.2‖ :=
    (isBigO_refl _ _).congr_left fun p => (norm_xin p.2).symm
  have hYO : (fun p : ℝ × State 2 => ‖Y p‖) =O[nhdsW K] fun p => ‖p.2‖ := by
    refine IsBigO.trans ?_ (hx0.add hμ1)
    exact IsBigO.of_bound 1 (Eventually.of_forall fun p => by
      rw [one_mul, norm_norm, Real.norm_of_nonneg (by positivity)]
      exact norm_add_le _ _)
  -- (a) the remainder of the expansion
  have h3 : (fun p : ℝ × State 2 => ‖Y p‖ ^ 3) =O[nhdsW K] fun p => ‖p.2‖ ^ 3 := hYO.pow 3
  have ha : (fun p : ℝ × State 2 => xpart (E (Y p))) =o[nhdsW K] fun p => ‖p.2‖ ^ 3 :=
    (xpart.isBigO_comp _ _).trans_isLittleO ((hexp.comp_tendsto hYt).trans_isBigO h3)
  -- (b) the `μ²` term
  have hb : (fun p : ℝ × State 2 => (p.1 ^ 2) • xpart (Q₃ emu emu)) =o[nhdsW K]
      fun p => ‖p.2‖ ^ 3 := by
    have h1 : (fun p : ℝ × State 2 => (p.1 ^ 2) • xpart (Q₃ emu emu)) =O[nhdsW K]
        fun p => p.1 ^ 2 :=
      IsBigO.of_bound ‖xpart (Q₃ emu emu)‖ (Eventually.of_forall fun p => by
        rw [norm_smul, mul_comm])
    refine (h1.trans ((isBigO_nhdsW_fst K).pow 2)).trans_isLittleO ?_
    refine (Dynamics.isLittleO_pow_of_tendsto (tendsto_nhdsW K) (by norm_num : 3 < 4)).congr_left
      fun p => ?_
    ring
  -- (c) the cubic terms with a factor `μ`
  have h4 : ∀ {a b c : ℝ × State 2 → ℝ}, a =O[nhdsW K] (fun p => ‖p.2‖ ^ 2) →
      b =O[nhdsW K] (fun p => ‖p.2‖) → c =O[nhdsW K] (fun p => ‖p.2‖) →
      (fun p => a p * b p * c p) =o[nhdsW K] fun p => ‖p.2‖ ^ 3 := by
    intro a b c ha hb hc
    have h1 : (fun p : ℝ × State 2 => ‖p.2‖ ^ 2 * ‖p.2‖ * ‖p.2‖) =o[nhdsW K]
        fun p => ‖p.2‖ ^ 3 :=
      (Dynamics.isLittleO_pow_of_tendsto (tendsto_nhdsW K) (by norm_num : 3 < 4)).congr_left
        fun p => by ring
    exact ((ha.mul hb).mul hc).trans_isLittleO h1
  have hc : (fun p : ℝ × State 2 => xpart (C₃ ![p.1 • emu, Y p, Y p] +
      C₃ ![xin p.2, p.1 • emu, Y p] + C₃ ![xin p.2, xin p.2, p.1 • emu])) =o[nhdsW K]
      fun p => ‖p.2‖ ^ 3 := by
    refine (xpart.isBigO_comp _ _).trans_isLittleO ?_
    refine (((isBigO_trilin C₃ _ _ _).trans_isLittleO (h4 hμ hYO hYO)).add
      ((isBigO_trilin C₃ _ _ _).trans_isLittleO ?_)).add
      ((isBigO_trilin C₃ _ _ _).trans_isLittleO ?_)
    · exact (h4 hμ hx0 hYO).congr_left fun p => by ring
    · exact (h4 hμ hx0 hx0).congr_left fun p => by ring
  exact ((ha.add hb).add hc).congr_left fun p => (key p).symm

/-- A vector `q` with `μ² q = o(μ²)` at `0` vanishes. -/
@[tmio T, powerlib_foundation] private theorem eq_zero_of_isLittleO_sq {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {q : V}
    (h : (fun μ : ℝ => (μ ^ 2) • q) =o[𝓝 0] fun μ => μ ^ 2) : q = 0 := by
  by_contra hq
  have hpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (h.def (half_pos hpos))
  have hμ : dist (r / 2) (0 : ℝ) < r := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]; linarith
  have h1 := hb hμ
  simp only [norm_smul, norm_pow, Real.norm_eq_abs] at h1
  have h2 : 0 < |r / 2| ^ 2 := by positivity
  nlinarith

/-- The `μ²` coefficient of the slices vanishes when `g(μ, 0) = 0` for small `μ`. -/
@[tmio T, powerlib_foundation] theorem xpart_emu_emu_eq_zero
    (hexp : (fun y => G y - (L₃ y + Q₃ y y + C₃ ![y, y, y])) =o[𝓝 0] fun y => ‖y‖ ^ 3)
    (hL : ∀ (u : State 2) (μ : ℝ), xpart (L₃ (xin u + μ • emu)) = rotL ω u) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hg0 : ∀ μ : ℝ, |μ| < r₀ → sliceField G μ 0 = 0) :
    xpart (Q₃ emu emu) = 0 := by
  have htri : ∀ a b d : State (2 + 1), ‖C₃ ![a, b, d]‖ ≤ ‖C₃‖ * (‖a‖ * (‖b‖ * ‖d‖)) :=
    fun a b d => by simpa [Fin.prod_univ_three, mul_assoc] using C₃.le_opNorm ![a, b, d]
  have hne : ∀ μ : ℝ, ‖μ • (emu : State (2 + 1))‖ = |μ| := fun μ => by
    rw [norm_smul, norm_emu, mul_one, Real.norm_eq_abs]
  apply eq_zero_of_isLittleO_sq
  have ht : Tendsto (fun μ : ℝ => μ • (emu : State (2 + 1))) (𝓝 0) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const (emu : State (2 + 1))
    simpa using this
  have h3 : (fun μ : ℝ => |μ| ^ 3) =o[𝓝 0] fun μ => μ ^ 2 := by
    have := Dynamics.isLittleO_pow_of_tendsto (l := 𝓝 (0 : ℝ)) (s := fun μ : ℝ => |μ|)
      (by simpa using (continuous_abs.tendsto (0 : ℝ))) (by norm_num : 2 < 3)
    exact this.congr_right fun μ => sq_abs μ
  have hE0 : (fun μ : ℝ => G (μ • emu) - (L₃ (μ • emu) + Q₃ (μ • emu) (μ • emu) +
      C₃ ![μ • emu, μ • emu, μ • emu])) =o[𝓝 0] fun μ => |μ| ^ 3 :=
    (hexp.comp_tendsto ht).congr_right fun μ => by simp only [Function.comp_apply, hne]
  have hE1 : (fun μ : ℝ => xpart (G (μ • emu) - (L₃ (μ • emu) + Q₃ (μ • emu) (μ • emu) +
      C₃ ![μ • emu, μ • emu, μ • emu]))) =o[𝓝 0] fun μ => μ ^ 2 :=
    (xpart.isBigO_comp _ _).trans_isLittleO (hE0.trans h3)
  have hC1 : (fun μ : ℝ => xpart (C₃ ![μ • emu, μ • emu, μ • emu])) =o[𝓝 0]
      fun μ => μ ^ 2 := by
    refine (xpart.isBigO_comp _ _).trans_isLittleO ((IsBigO.of_bound ‖C₃‖
      (Eventually.of_forall fun μ => ?_)).trans_isLittleO h3)
    refine (htri _ _ _).trans (le_of_eq ?_)
    rw [hne, Real.norm_of_nonneg (by positivity)]
    ring
  refine ((hE1.add hC1).neg_left).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr₀] with μ hμ
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hμ
  have hz0 : (![0, 0, 0] : Fin 3 → State 2) = 0 := by funext i; fin_cases i <;> rfl
  have hL0 : unfoldRem (sliceM Q₃) (sliceQ Q₃) (sliceC C₃) ω (sliceField G) μ 0 = 0 := by
    simp only [unfoldRem, hg0 μ hμ, map_zero, smul_zero, add_zero, hz0,
      ContinuousMultilinearMap.map_zero, sub_zero]
  have hx0 : ∀ a b : State (2 + 1), C₃ ![0, a, b] = 0 := fun a b =>
    C₃.map_coord_zero 0 rfl
  have hk := unfoldRem_slice_eq (Q₃ := Q₃) (C₃ := C₃) (G := G) hL μ 0
  rw [hL0] at hk
  simp only [map_zero, zero_add, hx0, add_zero] at hk
  show -(xpart (G (μ • emu) - (L₃ (μ • emu) + Q₃ (μ • emu) (μ • emu) +
    C₃ ![μ • emu, μ • emu, μ • emu])) + xpart (C₃ ![μ • emu, μ • emu, μ • emu])) =
    μ ^ 2 • xpart (Q₃ emu emu)
  linear_combination (norm := module) hk

/-- The slice remainder in the linear regime `‖u‖ ≤ c |μ|`. -/
@[tmio T, powerlib_foundation] private theorem unfoldRem_le_linear {g : ℝ → State 2 → State 2}
    {M : State 2 →L[ℝ] State 2} {Q : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
    {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)} {ε Cq c μ : ℝ}
    {u : State 2} (h1 : ‖g μ u - rotL ω u - μ • M u‖ ≤ ε / 2 * |μ| * ‖u‖ + Cq * ‖u‖ ^ 2)
    (hu : ‖u‖ ≤ 1) (hA : ‖u‖ ≤ c * |μ|) (hc : (|Cq| + (‖Q‖ + ‖C‖)) * c ≤ ε / 2)
    (hε : 0 ≤ ε) : ‖unfoldRem M Q C ω g μ u‖ ≤ ε * (|μ| * ‖u‖ + ‖u‖ ^ 3) := by
  have hun : 0 ≤ ‖u‖ := norm_nonneg u
  have hQ : ‖Q u u‖ ≤ ‖Q‖ * ‖u‖ ^ 2 := by
    have := Q.le_opNorm₂ u u
    rw [sq, ← mul_assoc]; exact this
  have hC : ‖C ![u, u, u]‖ ≤ ‖C‖ * ‖u‖ ^ 2 := by
    have h := C.le_opNorm ![u, u, u]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    have hu3 : ‖u‖ * ‖u‖ * ‖u‖ ≤ ‖u‖ ^ 2 := by
      rw [sq]; exact mul_le_of_le_one_right (mul_nonneg hun hun) hu
    exact h.trans (mul_le_mul_of_nonneg_left hu3 (norm_nonneg _))
  have e : unfoldRem M Q C ω g μ u = (g μ u - rotL ω u - μ • M u) - Q u u - C ![u, u, u] := by
    simp only [unfoldRem]; abel
  rw [e]
  have hsq : ‖u‖ ^ 2 ≤ c * |μ| * ‖u‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hA hun
  have hCq : Cq * ‖u‖ ^ 2 ≤ |Cq| * ‖u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self Cq) (sq_nonneg _)
  have hK : (|Cq| + (‖Q‖ + ‖C‖)) * ‖u‖ ^ 2 ≤ ε / 2 * (|μ| * ‖u‖) := by
    calc (|Cq| + (‖Q‖ + ‖C‖)) * ‖u‖ ^ 2 ≤ (|Cq| + (‖Q‖ + ‖C‖)) * (c * |μ| * ‖u‖) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (|Cq| + (‖Q‖ + ‖C‖)) * c * (|μ| * ‖u‖) := by ring
      _ ≤ ε / 2 * (|μ| * ‖u‖) := mul_le_mul_of_nonneg_right hc (by positivity)
  have h3 : 0 ≤ ε * ‖u‖ ^ 3 := by positivity
  have := norm_sub_le (g μ u - rotL ω u - μ • M u - Q u u) (C ![u, u, u])
  have := norm_sub_le (g μ u - rotL ω u - μ • M u) (Q u u)
  linarith only [this, ‹‖g μ u - rotL ω u - μ • M u - Q u u - C ![u, u, u]‖ ≤ _›, h1, hQ, hC,
    hCq, hK, h3]

/-- The slice remainder in the expansion regime `‖(u, μ)‖ ≤ B ‖u‖`. -/
@[tmio T, powerlib_foundation] private theorem unfoldRem_le_expansion
    (hL : ∀ (u : State 2) (μ : ℝ), xpart (L₃ (xin u + μ • emu)) = rotL ω u)
    (hq : xpart (Q₃ emu emu) = 0) {ε B μ : ℝ} {u : State 2}
    (hE : ‖G (xin u + μ • emu) - (L₃ (xin u + μ • emu) + Q₃ (xin u + μ • emu) (xin u + μ • emu)
      + C₃ ![xin u + μ • emu, xin u + μ • emu, xin u + μ • emu])‖ ≤
        ε / (2 * B ^ 3) * ‖xin u + μ • emu‖ ^ 3)
    (hY : ‖xin u + μ • emu‖ ≤ B * ‖u‖) (hB0 : 0 < B) (hε : 0 < ε)
    (hCu : ‖C₃‖ * (B ^ 2 + B + 1) * ‖u‖ ≤ ε / 2) :
    ‖unfoldRem (sliceM Q₃) (sliceQ Q₃) (sliceC C₃) ω (sliceField G) μ u‖ ≤
      ε * (|μ| * ‖u‖ + ‖u‖ ^ 3) := by
  have htri : ∀ a b d : State (2 + 1), ‖C₃ ![a, b, d]‖ ≤ ‖C₃‖ * (‖a‖ * (‖b‖ * ‖d‖)) :=
    fun a b d => by simpa [Fin.prod_univ_three, mul_assoc] using C₃.le_opNorm ![a, b, d]
  have hne : ‖μ • (emu : State (2 + 1))‖ = |μ| := by
    rw [norm_smul, norm_emu, mul_one, Real.norm_eq_abs]
  have hun : 0 ≤ ‖u‖ := norm_nonneg u
  have hμa : 0 ≤ |μ| := abs_nonneg μ
  have hC0 : 0 ≤ ‖C₃‖ := norm_nonneg _
  have hY0 : 0 ≤ ‖xin u + μ • emu‖ := norm_nonneg _
  rw [unfoldRem_slice_eq hL μ u, hq, smul_zero, add_zero]
  have ha : ‖xpart (G (xin u + μ • emu) - (L₃ (xin u + μ • emu) +
      Q₃ (xin u + μ • emu) (xin u + μ • emu) + C₃ ![xin u + μ • emu, xin u + μ • emu,
        xin u + μ • emu]))‖ ≤ ε / 2 * ‖u‖ ^ 3 := by
    refine (norm_xpart_le _).trans (hE.trans ?_)
    calc ε / (2 * B ^ 3) * ‖xin u + μ • emu‖ ^ 3 ≤ ε / (2 * B ^ 3) * (B * ‖u‖) ^ 3 := by
          gcongr
      _ = ε / 2 * ‖u‖ ^ 3 := by field_simp
  have t1 := htri (μ • emu) (xin u + μ • emu) (xin u + μ • emu)
  have t2 := htri (xin u) (μ • emu) (xin u + μ • emu)
  have t3 := htri (xin u) (xin u) (μ • emu)
  rw [hne] at t1
  rw [hne, norm_xin] at t2 t3
  have k1 : ‖C₃‖ * (|μ| * (‖xin u + μ • emu‖ * ‖xin u + μ • emu‖)) ≤
      ‖C₃‖ * (|μ| * (B * ‖u‖ * (B * ‖u‖))) := by gcongr
  have k2 : ‖C₃‖ * (‖u‖ * (|μ| * ‖xin u + μ • emu‖)) ≤
      ‖C₃‖ * (‖u‖ * (|μ| * (B * ‖u‖))) := by gcongr
  have hsum : ‖C₃‖ * (|μ| * (B * ‖u‖ * (B * ‖u‖))) + ‖C₃‖ * (‖u‖ * (|μ| * (B * ‖u‖))) +
      ‖C₃‖ * (‖u‖ * (‖u‖ * |μ|)) = ‖C₃‖ * (B ^ 2 + B + 1) * ‖u‖ * (|μ| * ‖u‖) := by ring
  have hlast : ‖C₃‖ * (B ^ 2 + B + 1) * ‖u‖ * (|μ| * ‖u‖) ≤ ε / 2 * (|μ| * ‖u‖) :=
    mul_le_mul_of_nonneg_right hCu (by positivity)
  have hb : ‖xpart (C₃ ![μ • emu, xin u + μ • emu, xin u + μ • emu] +
      C₃ ![xin u, μ • emu, xin u + μ • emu] + C₃ ![xin u, xin u, μ • emu])‖ ≤
      ε / 2 * (|μ| * ‖u‖) := by
    refine (norm_xpart_le _).trans ((norm_add₃_le).trans ?_)
    linarith only [t1, t2, t3, k1, k2, hsum, hlast]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 * ‖u‖ ^ 3 + ε / 2 * (|μ| * ‖u‖) := add_le_add ha hb
    _ ≤ ε * (|μ| * ‖u‖ + ‖u‖ ^ 3) := by
        have h0 : 0 ≤ ε * (|μ| * ‖u‖ + ‖u‖ ^ 3) := by positivity
        linarith only [h0, show ε / 2 * ‖u‖ ^ 3 + ε / 2 * (|μ| * ‖u‖) =
          ε * (|μ| * ‖u‖ + ‖u‖ ^ 3) / 2 by ring]

/-- **The slice remainder on a full neighbourhood.** If, besides the expansion of `G`, the slices
are linearly approximated near `0` (for every `ε > 0`, `‖g(μ, u) − R u − μ M u‖ ≤ ε |μ| ‖u‖ +
C_q ‖u‖²`: the regime `‖u‖ ≪ |μ|`), then
`g(μ, u) − (R u + μ M u + Q(u, u) + C(u, u, u)) = o(|μ| ‖u‖ + ‖u‖³)` as `(μ, u) → 0`, with no
restriction on `μ` (the linear regime for `‖u‖ ≤ c|μ|`, the expansion of `G` for
`‖u‖ ≥ c|μ|`; the `μ²` coefficient vanishes because `g(μ, 0) = 0`). -/
@[tmio T, powerlib_foundation] theorem isLittleO_unfoldRem_slice_full
    (hexp : (fun y => G y - (L₃ y + Q₃ y y + C₃ ![y, y, y])) =o[𝓝 0] fun y => ‖y‖ ^ 3)
    (hL : ∀ (u : State 2) (μ : ℝ), xpart (L₃ (xin u + μ • emu)) = rotL ω u) {Cq : ℝ}
    (hlin : ∀ ε > 0, ∃ r > 0, ∀ (μ : ℝ) (u : State 2), |μ| < r → ‖u‖ < r →
      ‖sliceField G μ u - rotL ω u - μ • sliceM Q₃ u‖ ≤ ε * |μ| * ‖u‖ + Cq * ‖u‖ ^ 2) :
    (fun p : ℝ × State 2 => unfoldRem (sliceM Q₃) (sliceQ Q₃) (sliceC C₃) ω (sliceField G) p.1
      p.2) =o[𝓝 0] fun p => |p.1| * ‖p.2‖ + ‖p.2‖ ^ 3 := by
  obtain ⟨r₀, hr₀, h₀⟩ := hlin 1 one_pos
  have hq : xpart (Q₃ emu emu) = 0 := xpart_emu_emu_eq_zero hexp hL hr₀ fun μ hμ => by
    have := h₀ μ 0 hμ (by simpa using hr₀)
    simpa using this
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨S, hS⟩ : ∃ S, S = ‖sliceQ Q₃‖ + ‖sliceC C₃‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS ▸ by positivity
  obtain ⟨c, hc⟩ : ∃ c, c = ε / (2 * (|Cq| + S + 1)) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ by positivity
  have hcS : (|Cq| + S) * c ≤ ε / 2 := by
    rw [hc, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg Cq]
  obtain ⟨B, hB⟩ : ∃ B, B = 1 + 1 / c := ⟨_, rfl⟩
  have hB0 : 0 < B := hB ▸ by positivity
  obtain ⟨r₁, hr₁, h₁⟩ := hlin (ε / 2) (half_pos hε)
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff.mp
    (hexp.def (show 0 < ε / (2 * B ^ 3) by positivity))
  obtain ⟨r₃, hr₃⟩ : ∃ r, r = ε / (2 * (‖C₃‖ * (B ^ 2 + B + 1)) + 1) := ⟨_, rfl⟩
  have hr₃0 : 0 < r₃ := hr₃ ▸ by positivity
  have hr₃C : ‖C₃‖ * (B ^ 2 + B + 1) * r₃ ≤ ε / 2 := by
    rw [hr₃, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg C₃, show 0 ≤ ‖C₃‖ * (B ^ 2 + B + 1) by positivity]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × State 2)
    (lt_min (lt_min hr₁ one_pos) (lt_min (half_pos hr₂) hr₃0))] with pr hpr
  obtain ⟨μ, u⟩ := pr
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs] at hpr
  obtain ⟨hμ, hu⟩ := hpr
  simp only [lt_min_iff] at hμ hu
  obtain ⟨⟨hμ1, -⟩, hμ2, -⟩ := hμ
  obtain ⟨⟨hu1, hu1'⟩, hu2, hu3⟩ := hu
  have hnorm : ‖|μ| * ‖u‖ + ‖u‖ ^ 3‖ = |μ| * ‖u‖ + ‖u‖ ^ 3 :=
    Real.norm_of_nonneg (by positivity)
  rw [hnorm]
  rcases le_or_gt ‖u‖ (c * |μ|) with hA | hBr
  · exact unfoldRem_le_linear (h₁ μ u hμ1 hu1) hu1'.le hA (by rw [← hS]; exact hcS) hε.le
  · have hμu : |μ| ≤ ‖u‖ / c := by rw [le_div_iff₀ hc0]; linarith
    have hY : ‖xin u + μ • emu‖ ≤ B * ‖u‖ := by
      refine (norm_xin_add_smul_le u μ).trans ?_
      rw [hB, add_mul, one_mul]
      have : ‖u‖ / c = 1 / c * ‖u‖ := by ring
      linarith
    have hYr : dist (xin u + μ • emu) 0 < r₂ := by
      rw [dist_zero_right]
      exact lt_of_le_of_lt (norm_xin_add_smul_le u μ) (by linarith)
    have hE2 := h₂ hYr
    rw [norm_pow, norm_norm] at hE2
    refine unfoldRem_le_expansion hL hq hE2 hY hB0 hε (le_trans ?_ hr₃C)
    exact mul_le_mul_of_nonneg_left hu3.le (by positivity)

/-- A slice of a field Lipschitz on a ball is Lipschitz on a ball, uniformly in small `μ`. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitzOnWith_slice {r : ℝ} {L : NNReal}
    (hr : 0 < r) (hG : LipschitzOnWith L G (Metric.closedBall 0 r)) :
    ∃ ρ > 0, ∀ μ, |μ| < ρ → ∃ L' : NNReal,
      LipschitzOnWith L' (sliceField G μ) (Metric.closedBall 0 ρ) := by
  refine ⟨r / 2, by positivity, fun μ hμ => ⟨L, LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hu hv
  have hY : ∀ w : State 2, ‖w‖ ≤ r / 2 →
      xin w + μ • emu ∈ Metric.closedBall (0 : State (2 + 1)) r :=
    fun w hw => by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [norm_xin_add_smul_le w μ]
  have h := hG.dist_le_mul _ (hY u hu) _ (hY v hv)
  rw [dist_eq_norm, dist_eq_norm] at h ⊢
  have e : xin u + μ • emu - (xin v + μ • emu) = xin (u - v) := by
    rw [map_sub]; abel
  rw [e, norm_xin] at h
  calc ‖sliceField G μ u - sliceField G μ v‖
      = ‖xpart (G (xin u + μ • emu) - G (xin v + μ • emu))‖ := by
        rw [map_sub]; rfl
    _ ≤ ‖G (xin u + μ • emu) - G (xin v + μ • emu)‖ := norm_xpart_le _
    _ ≤ L * ‖u - v‖ := h

end Slice

/-! ## The Taylor data of the augmented field -/

section Taylor

variable {n : ℕ} {F : State n → ℝ → State n}

@[tmio T, powerlib_foundation] theorem augField_xin_add (x : State n) (s : ℝ) :
    augField F (xin x + s • emu) = xin (F x s) := by
  simp [augField]

/-- The derivative of the augmented field along the state directions at `(0, s)`. -/
@[tmio T, powerlib_foundation] theorem fderiv_augField_apply (hF : ContDiff ℝ 1 (augField F))
    (s : ℝ) (a : State n) :
    fderiv ℝ (augField F) (s • emu) (xin a) = xin (fderiv ℝ (fun x => F x s) 0 a) := by
  have hd : HasFDerivAt (fun x => augField F (xin x + s • emu))
      ((fderiv ℝ (augField F) (s • emu)).comp xin) 0 := by
    have h1 : HasFDerivAt (fun x : State n => xin x + s • (emu : State (n + 1))) xin 0 :=
      xin.hasFDerivAt.add_const _
    have h2 : HasFDerivAt (augField F) (fderiv ℝ (augField F) (s • emu))
        (xin (0 : State n) + s • emu) := by
      rw [map_zero, zero_add]
      exact ((hF.differentiable one_ne_zero) _).hasFDerivAt
    exact h2.comp 0 h1
  have he : (fun x => augField F (xin x + s • emu)) = fun x => xin (F x s) :=
    funext fun x => augField_xin_add x s
  have hFs : DifferentiableAt ℝ (fun x => F x s) 0 := by
    have : (fun x => F x s) = fun x => xpart (augField F (xin x + s • emu)) := by
      funext x; simp [augField_xin_add]
    rw [this]
    exact (xpart.differentiableAt).comp _ hd.differentiableAt
  have hd' : HasFDerivAt (fun x => xin (F x s)) (xin.comp (fderiv ℝ (fun x => F x s) 0)) 0 :=
    xin.hasFDerivAt.comp 0 hFs.hasFDerivAt
  rw [he] at hd
  have := hd.unique hd'
  exact congrArg (fun T : State n →L[ℝ] State (n + 1) => T a) this

/-- **The mixed derivative.** If `μ ↦ D_x F(0, μ)` has derivative `B` at `0`, then
`D²Φ(0)((0, 1), (a, 0)) = (B a, 0)` for the augmented field `Φ`. -/
@[tmio T, powerlib_foundation] theorem fderiv_fderiv_augField_emu
    (hF : ContDiff ℝ 1 (augField F)) (ha : AnalyticAt ℝ (augField F) 0)
    {B : State n →L[ℝ] State n} (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    (a : State n) : fderiv ℝ (fderiv ℝ (augField F)) 0 emu (xin a) = xin (B a) := by
  have hD : HasFDerivAt (fderiv ℝ (augField F)) (fderiv ℝ (fderiv ℝ (augField F)) 0) 0 :=
    ha.fderiv.differentiableAt.hasFDerivAt
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (augField F) (s • emu))
      (fderiv ℝ (fderiv ℝ (augField F)) 0 emu) 0 := by
    have h2 : HasDerivAt (fun s : ℝ => s • (emu : State (n + 1))) emu 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (emu : State (n + 1))
    have h3 : HasFDerivAt (fderiv ℝ (augField F)) (fderiv ℝ (fderiv ℝ (augField F)) 0)
        ((0 : ℝ) • (emu : State (n + 1))) := by rw [zero_smul]; exact hD
    exact h3.comp_hasDerivAt 0 h2
  have h4 : HasDerivAt (fun s : ℝ => fderiv ℝ (augField F) (s • emu) (xin a))
      (fderiv ℝ (fderiv ℝ (augField F)) 0 emu (xin a)) 0 := by
    have := h1.clm_apply (hasDerivAt_const (0 : ℝ) (xin a))
    simpa using this
  have h7 : HasDerivAt (fun s : ℝ => fderiv ℝ (fun x => F x s) 0 a) (B a) 0 := by
    simpa using hB.clm_apply (hasDerivAt_const (0 : ℝ) a)
  have h5 : HasDerivAt (fun s : ℝ => xin (fderiv ℝ (fun x => F x s) 0 a)) (xin (B a)) 0 :=
    xin.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h7
  have he : (fun s : ℝ => fderiv ℝ (augField F) (s • emu) (xin a)) =
      fun s => xin (fderiv ℝ (fun x => F x s) 0 a) :=
    funext fun s => fderiv_augField_apply hF s a
  rw [he] at h4
  exact h4.unique h5

/-- The restriction of the second derivative to the state directions, and its mixed part. -/
@[tmio T, powerlib_foundation] theorem fderiv_fderiv_augField_xin_emu
    (hF : ContDiff ℝ 1 (augField F)) (ha : AnalyticAt ℝ (augField F) 0)
    {B : State n →L[ℝ] State n} (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    (a : State n) : fderiv ℝ (fderiv ℝ (augField F)) 0 (xin a) emu = xin (B a) := by
  have hc2 : ContDiffAt ℝ 2 (augField F) 0 := ha.contDiffAt
  have hs := hc2.isSymmSndFDerivAt (by simp)
  rw [hs]
  exact fderiv_fderiv_augField_emu hF ha hB a

/-- **The state part of the Taylor data.** With `F₀ = F(·, 0)`, the restrictions to `(x, 0)` of
the quadratic and cubic Taylor terms of the augmented field are those of `F₀`, on the diagonal. -/
@[tmio T, powerlib_foundation] theorem taylor_restrict (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0) (x : State n) :
    xpart (((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (augField F)) 0) (xin x) (xin x)) =
        ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (fun y => F y 0)) 0) x x ∧
      xpart (((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 (augField F) 0) ![xin x, xin x, xin x]) =
        ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 (fun y => F y 0) 0) ![x, x, x] := by
  set Φ := augField F
  set F₀ : State n → State n := fun y => F y 0 with hF₀
  have hF₀e : F₀ = fun y => xpart (Φ (xin y)) := by
    funext y
    show F y 0 = xpart (augField F (xin y))
    simp [augField]
  have ha0 : AnalyticAt ℝ F₀ 0 := by
    rw [hF₀e]
    have h1 : AnalyticAt ℝ Φ (xin (0 : State n)) := by rw [map_zero]; exact ha
    exact xpart.analyticAt _ |>.comp (h1.comp (xin.analyticAt 0))
  set Qa := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Φ) 0 with hQa
  set Ca := (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 Φ 0 with hCa
  set Q₀ := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F₀) 0 with hQ₀
  set C₀ := (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 F₀ 0 with hC₀
  set Qt : State n →L[ℝ] State n →L[ℝ] State n :=
    (ContinuousLinearMap.compL ℝ (State n) (State (n + 1)) (State n) xpart).comp
      (Qa.bilinearComp xin xin)
  set Ct : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n) :=
    xpart.compContinuousMultilinearMap (Ca.compContinuousLinearMap fun _ => xin)
  have hQt : ∀ u v, Qt u v = xpart (Qa (xin u) (xin v)) := fun u v => by simp [Qt]
  have hCt : ∀ u, Ct ![u, u, u] = xpart (Ca ![xin u, xin u, xin u]) := by
    intro u
    have e : (fun i => xin ((![u, u, u] : Fin 3 → State n) i)) = ![xin u, xin u, xin u] := by
      funext i; fin_cases i <;> rfl
    simp only [Ct, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, e]
  have hΦ0 : Φ 0 = 0 := by
    have := augField_xin_add (F := F) 0 0
    simpa [hF0] using this
  have hd : fderiv ℝ Φ 0 = augL (fderiv ℝ F₀ 0) :=
    fderiv_augField_zero (hF.differentiable one_ne_zero 0) hF0
  have hT1 := taylor3_isBigO ha0
  have hT2 : (fun y : State n => xpart (Φ (xin y) - (Φ 0 + fderiv ℝ Φ 0 (xin y) +
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Φ) 0 (xin y) (xin y) +
      (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 Φ 0 ![xin y, xin y, xin y]))) =O[𝓝 0]
      fun y => ‖y‖ ^ 4 := by
    have hx : Tendsto (fun y : State n => xin y) (𝓝 0) (𝓝 0) := by
      simpa using xin.continuous.tendsto (0 : State n)
    refine ((xpart.isBigO_comp _ _).trans ((taylor3_isBigO ha).comp_tendsto hx)).congr_right ?_
    intro y; simp [norm_xin]
  have hF00 : F₀ 0 = 0 := hF0 0
  have hdiff : (fun y => (Qt - Q₀) y y + (Ct - C₀) ![y, y, y]) =O[𝓝 0] fun y => ‖y‖ ^ 4 := by
    refine (hT1.sub hT2).congr_left fun y => ?_
    have hFy : F₀ y = xpart (Φ (xin y)) := by rw [hF₀e]
    simp only [_root_.sub_apply, hQt, hCt, hQa, hCa, hQ₀, hC₀, _root_.smul_apply, hΦ0, hF00, hd,
      augL_apply, xpart_xin, hFy, map_sub, map_add, map_smul, zero_add]
    abel
  obtain ⟨h1, h2⟩ := eq_zero_of_isBigO_quad_cubic hdiff x
  simp only [_root_.sub_apply, sub_eq_zero, hQt, hCt] at h1 h2
  exact ⟨h1, h2⟩

end Taylor

/-! ## The reduced data of the augmented field -/

section ChartData

open powerlib.Dynamics.CenterManifold (triQH triQH_apply)

variable {N m : ℕ}

/-- The quadratic part in chart coordinates: `(y, y') ↦ π Q(ι y, ι y')`. -/
def chartQ (π : State N →L[ℝ] State m) (Q : State N →L[ℝ] State N →L[ℝ] State N)
    (ι : State m →L[ℝ] State N) : State m →L[ℝ] State m →L[ℝ] State m :=
  (ContinuousLinearMap.compL ℝ (State m) (State N) (State m) π).comp (Q.bilinearComp ι ι)

/-- The cubic part in chart coordinates:
`π [Q(ι y, H(ι y', ι y'')) + Q(H(ι y, ι y'), ι y'') + C(ι y, ι y', ι y'')]`. -/
def chartC (π : State N →L[ℝ] State m) (Q H : State N →L[ℝ] State N →L[ℝ] State N)
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State N) (State N))
    (ι : State m →L[ℝ] State N) : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State m) (State m) :=
  π.compContinuousMultilinearMap ((triQH Q H + C).compContinuousLinearMap fun _ => ι)

@[tmio T, powerlib_foundation] theorem chartQ_apply (π : State N →L[ℝ] State m)
    (Q : State N →L[ℝ] State N →L[ℝ] State N) (ι : State m →L[ℝ] State N) (y y' : State m) :
    chartQ π Q ι y y' = π (Q (ι y) (ι y')) := by
  simp [chartQ]

@[tmio T, powerlib_foundation] theorem chartC_apply (π : State N →L[ℝ] State m)
    (Q H : State N →L[ℝ] State N →L[ℝ] State N)
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State N) (State N))
    (ι : State m →L[ℝ] State N) (y : State m) :
    chartC π Q H C ι ![y, y, y] =
      π (Q (ι y) (H (ι y) (ι y)) + Q (H (ι y) (ι y)) (ι y) + C ![ι y, ι y, ι y]) := by
  have e : (fun i => ι ((![y, y, y] : Fin 3 → State m) i)) = ![ι y, ι y, ι y] := by
    funext i; fin_cases i <;> rfl
  simp only [chartC, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, e, _root_.add_apply, triQH_apply]

end ChartData

section Identification

open Polynomial
open powerlib.Dynamics.CenterManifold
open powerlib.NormalForm.LyapunovCoefficient (IsCriticalPair firstLyapunov jacobianC)
open powerlib.Dynamics.Degenerate.PlanarFocus (l1)

variable {n : ℕ} {F : State n → ℝ → State n} {ω : ℝ} {q p : Fin n → ℂ}

@[tmio T, powerlib_foundation] theorem augι_xin (a : State 2) :
    augι (critι q) (xin a) = xin (critι q a) := by simp

@[tmio T, powerlib_foundation] theorem augι_emu :
    augι (critι q) (emu : State (2 + 1)) = (emu : State (n + 1)) := by simp

@[tmio T, powerlib_foundation] theorem xpart_augπ (v : State (n + 1)) :
    xpart (augπ (critπ p) v) = critπ p (xpart v) := by simp

/-- **The mixed term is the transversality map.** The `μ u` coefficient of the reduced field on
`(u, μ)` is `critπ p ∘ B ∘ critι q`. -/
@[tmio T, powerlib_foundation] theorem sliceM_chartQ (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0) :
    sliceM (chartQ (augπ (critπ p)) ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (augField F)) 0)
      (augι (critι q))) = (critπ p).comp (B.comp (critι q)) := by
  ext1 u
  rw [sliceM_apply, chartQ_apply, chartQ_apply, augι_xin, augι_emu, ← map_add, xpart_augπ]
  simp only [_root_.smul_apply, fderiv_fderiv_augField_xin_emu hF ha hB,
    fderiv_fderiv_augField_emu hF ha hB, ContinuousLinearMap.comp_apply]
  rw [← add_smul]
  norm_num

@[tmio T, powerlib_foundation] theorem analyticAt_slice_zero (ha : AnalyticAt ℝ (augField F) 0) :
    AnalyticAt ℝ (fun x => F x 0) 0 := by
  have e : (fun x => F x 0) = fun x => xpart (augField F (xin x)) := by
    funext x; simp [augField]
  rw [e]
  have h1 : AnalyticAt ℝ (augField F) (xin (0 : State n)) := by rw [map_zero]; exact ha
  exact xpart.analyticAt _ |>.comp (h1.comp (xin.analyticAt 0))

/-- **The reduced `l₁` of the augmented field is Kuznetsov's `l₁` of `F(·, 0)`.** At `μ = 0` the
quadratic and cubic parts of the reduced field on `(u, μ)` are, on the diagonal, the reduced
forms of `F(·, 0)` with the state part of the augmented homological solution
(`taylor_restrict`); `l₁` depends only on the diagonal (`l1_congr`), and the planar `l₁` of the
reduced forms is the projection formula (`IsCritical.l1_reduced_eq_firstLyapunov`). -/
@[tmio T, powerlib_foundation] theorem l1_slice_eq (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0)
    (hc : IsCritical (fderiv ℝ (fun x => F x 0) 0) ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0)
    {H₀ : State (n + 1) →L[ℝ] State (n + 1) →L[ℝ] State (n + 1)}
    (hhom : IsHomological (augL (fderiv ℝ (fun x => F x 0) 0)) (augP (critP q p))
      ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (augField F)) 0) H₀)
    (hPH : ∀ u v, augP (critP q p) (H₀ u v) = 0) :
    l1 (rotL ω) (sliceQ (chartQ (augπ (critπ p))
        ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (augField F)) 0) (augι (critι q))))
      (sliceC (chartC (augπ (critπ p)) ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (augField F)) 0) H₀
        ((1 / 6 : ℝ) • iteratedFDeriv ℝ 3 (augField F) 0) (augι (critι q)))) ω =
      firstLyapunov (fun x => F x 0) 0 ω q p := by
  obtain ⟨Qa, hQa⟩ : ∃ Qa, Qa = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (augField F)) 0 := ⟨_, rfl⟩
  obtain ⟨Ca, hCa⟩ : ∃ Ca, Ca = (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 (augField F) 0 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = fderiv ℝ (fun x => F x 0) 0 := ⟨_, rfl⟩
  rw [← hQa, ← hCa]
  rw [← hQa, ← hA] at hhom
  rw [← hA] at hc
  set Q₀ := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (fun x => F x 0)) 0 with hQ₀
  set C₀ := (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 (fun x => F x 0) 0 with hC₀
  set Ht : State n →L[ℝ] State n →L[ℝ] State n :=
    (ContinuousLinearMap.compL ℝ (State n) (State (n + 1)) (State n) xpart).comp
      (H₀.bilinearComp xin xin) with hHt
  have hHta : ∀ a b, Ht a b = xpart (H₀ (xin a) (xin b)) := fun a b => by simp [hHt]
  have hTR : ∀ x, xpart (Qa (xin x) (xin x)) = Q₀ x x ∧
      xpart (Ca ![xin x, xin x, xin x]) = C₀ ![x, x, x] := by
    intro x; rw [hQa, hCa]; exact taylor_restrict hF ha hF0 x
  have hpol : ∀ a b, xpart (Qa (xin a) (xin b)) + xpart (Qa (xin b) (xin a)) =
      Q₀ a b + Q₀ b a := by
    intro a b
    have h1 := (hTR (a + b)).1
    have h2 := (hTR a).1
    have h3 := (hTR b).1
    simp only [map_add, _root_.add_apply] at h1
    rw [h2, h3] at h1
    have e : ∀ x y z w : State n, x + (y + z + w) = x + (y + z) + w := fun x y z w => by abel
    rw [← sub_eq_zero] at h1 ⊢
    rw [← h1]
    abel
  have hPm : ∀ v, mpart (augP (critP q p) v) = mpart v := fun v => by simp
  have hHx : ∀ a b, H₀ (xin a) (xin b) = xin (Ht a b) := by
    intro a b
    rw [ext_iff_parts, hHta, xpart_xin, mpart_xin, ← hPm, hPH]
    exact ⟨rfl, by simp⟩
  -- the diagonal agrees with the reduced forms of `F(·, 0)`
  have step1 : l1 (rotL ω) (sliceQ (chartQ (augπ (critπ p)) Qa (augι (critι q))))
      (sliceC (chartC (augπ (critπ p)) Qa H₀ Ca (augι (critι q)))) ω =
      l1 (rotL ω) (redQ q p Q₀) (redC q p Q₀ Ht C₀) ω := by
    refine l1_congr fun y => ?_
    rw [sliceQ_apply, sliceC_apply, chartQ_apply, chartC_apply, augι_xin, hHx, xpart_augπ,
      xpart_augπ, redQ_apply, redC_apply, ← map_add, ← map_add]
    simp only [map_add]
    have h1 := hTR (critι q y)
    have h2 := hpol (critι q y) (Ht (critι q y) (critι q y))
    rw [h1.1, h1.2, ← map_add (critπ p) (xpart _) (xpart _), h2, map_add]
  rw [step1]
  -- the projection formula
  have haF₀ := analyticAt_slice_zero ha
  obtain ⟨hAu, h2u⟩ := isUnit_det_of_charpoly hc.freq_pos.ne' hchar hr
  have hJ : jacobianC (fun x => F x 0) 0 = NormalForm.LyapunovCoefficient.cmat A := by
    rw [hA]; rfl
  rw [hJ] at hAu h2u
  have hd2 : ∀ u w, iteratedFDeriv ℝ 2 (fun x => F x 0) 0 ![u, w] = Q₀ u w + Q₀ w u := by
    intro u w
    rw [iteratedFDeriv_two_eq_of_analytic haF₀]
    rfl
  have hd3 : ∀ u w z, iteratedFDeriv ℝ 3 (fun x => F x 0) 0 ![u, w, z] = C₀ ![u, w, z] +
      C₀ ![u, z, w] + C₀ ![w, u, z] + C₀ ![w, z, u] + C₀ ![z, u, w] + C₀ ![z, w, u] :=
    fun u w z => iteratedFDeriv_three_eq_of_analytic haF₀ u w z
  have hPx : ∀ v, xpart (augP (critP q p) v) = critP q p (xpart v) := fun v => by simp
  have hhom' : ∀ u, critP q p u = u → Ht u (critP q p (A u)) + Ht (critP q p (A u)) u =
      (1 - critP q p) (A (Ht u u)) + (1 - critP q p) (Q₀ u u) := by
    intro u hu
    have hz : augP (critP q p) (xin u) = xin u := by simp [hu]
    have hAz : augP (critP q p) (augL A (xin u)) = xin (critP q p (A u)) := by simp
    have h := congrArg xpart (hhom (xin u) hz)
    rw [hAz] at h
    simp only [map_add, _root_.sub_apply, one_apply_eq_self,
      map_sub, hPx, augL_apply, xpart_xin, ← hHta] at h
    rw [(hTR u).1] at h
    simpa only [_root_.sub_apply, one_apply_eq_self] using h
  have hPH' : ∀ u v, critP q p (Ht u v) = 0 := by
    intro u v
    rw [hHta, ← hPx, hPH, map_zero]
  exact hc.l1_reduced_eq_firstLyapunov hA.symm hd2 hd3 hAu h2u hhom' hPH'

end Identification

/-! ## The reduced planar family of the augmented field -/

section Reduction

open Polynomial
open powerlib.Dynamics.CenterManifold
open powerlib.NormalForm.LyapunovCoefficient (IsCriticalPair firstLyapunov jacobianC)
open powerlib.Dynamics.Degenerate.PlanarFocus (l1)
open powerlib.Dynamics.PlanarHopf (nhdsW unfoldRem)

variable {n : ℕ} {F : State n → ℝ → State n} {ω : ℝ} {q p : Fin n → ℂ}

/-- The reduced field of the augmented family in the augmented critical coordinates is the
critical coordinate of the augmented field on the graph: `G(y) = π Φ(ι y + h(ι y))` (the term
`π A h` vanishes, `h` taking values in the stable part). -/
@[tmio T, powerlib_foundation] theorem chartField_aug_eq {A : State n →L[ℝ] State n}
    (hc : IsCritical A ω q p) {h : State (n + 1) → State (n + 1)}
    (hh : IsGraphMap (augP (critP q p)) h) (y : State (2 + 1)) :
    chartField (augL A) (fun z => augField F z - augL A z) h (augι (critι q)) (augπ (critπ p))
        y = augπ (critπ p) (augField F (augι (critι q) y + h (augι (critι q) y))) := by
  have hz : critπ p (xpart (h (augι (critι q) y))) = 0 := by
    have h1 := congrArg xpart (hh.proj_apply (augι (critι q) y))
    simp only [augP_apply, map_add, map_smul, xpart_xin, xpart_emu, smul_zero, add_zero,
      map_zero] at h1
    have h2 := congrArg (critπ p) h1
    rwa [critP, ContinuousLinearMap.comp_apply, hc.critπ_critι, map_zero] at h2
  have hA : augπ (critπ p) (augL A (h (augι (critι q) y))) = 0 := by
    refine ext_iff_parts.mpr ⟨?_, ?_⟩
    · rw [xpart_augπ, augL_apply, xpart_xin, hc.critπ_apply, hz, map_zero, map_zero]
    · simp only [augπ_apply, augL_apply, map_add, map_smul, mpart_xin, mpart_emu, smul_eq_mul,
        mul_one, zero_add, map_zero]
  simp only [chartField, map_add, map_sub, hA]
  abel

/-- **Second-order Taylor bound.** If `Φ` is differentiable and `DΦ` is `C`-Lipschitz on the
ball of radius `r`, then `‖Φ(a + w) − Φ(a) − DΦ(a) w‖ ≤ C ‖w‖²` for `a, a + w` in the ball. -/
@[tmio T, powerlib_foundation] theorem norm_taylor_le_of_lipschitzOn {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : E → V} (hΦ : Differentiable ℝ Φ) {C : NNReal} {r : ℝ}
    (hL : LipschitzOnWith C (fderiv ℝ Φ) (Metric.ball 0 r)) {a w : E} (ha : ‖a‖ < r)
    (haw : ‖a + w‖ < r) : ‖Φ (a + w) - Φ a - fderiv ℝ Φ a w‖ ≤ C * ‖w‖ ^ 2 := by
  have hseg : segment ℝ a (a + w) ⊆ Metric.ball 0 r :=
    (convex_ball 0 r).segment_subset (mem_ball_zero_iff.mpr ha) (mem_ball_zero_iff.mpr haw)
  have hb : ∀ z ∈ segment ℝ a (a + w), ‖fderiv ℝ Φ z - fderiv ℝ Φ a‖ ≤ C * ‖w‖ := by
    intro z hz
    have h1 := hL.norm_sub_le (hseg hz) (hseg (left_mem_segment ℝ _ _))
    refine h1.trans ?_
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have e : a + θ • (a + w - a) - a = θ • w := by simp only [add_sub_cancel_left]
    rw [e, norm_smul, Real.norm_of_nonneg hθ.1]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hθ.2) C.2
  have := (convex_segment a (a + w)).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hΦ z) hb (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  rw [add_sub_cancel_left] at this
  calc _ ≤ C * ‖w‖ * ‖w‖ := this
    _ = C * ‖w‖ ^ 2 := by ring

/-- **The slice in the linear regime, exactly.** For a graph map `h` over the augmented centre,
`z = (ι u, μ)`, `w = (ι u, 0) + h z`, the slice of the reduced field minus
`R u + μ M u` is `π((D_μ − A − μB) ι u) + π((D_μ − A) h z) + π R`, `D_μ = D_x F(0, μ)`, `R` the
second-order Taylor remainder of the augmented field at `(0, μ)` in the direction `w`. -/
@[tmio T, powerlib_foundation] theorem slice_sub_eq (hF : ContDiff ℝ 1 (augField F))
    (hF0 : ∀ μ, F 0 μ = 0) {A : State n →L[ℝ] State n} (hc : IsCritical A ω q p)
    (B : State n →L[ℝ] State n) {h : State (n + 1) → State (n + 1)}
    (hh : IsGraphMap (augP (critP q p)) h) (μ : ℝ) (u : State 2) :
    sliceField (chartField (augL A) (fun z => augField F z - augL A z) h (augι (critι q))
        (augπ (critπ p))) μ u - rotL ω u - μ • ((critπ p).comp (B.comp (critι q))) u =
      critπ p ((fderiv ℝ (fun x => F x μ) 0 - A - μ • B) (critι q u)) +
      critπ p ((fderiv ℝ (fun x => F x μ) 0 - A) (xpart (h (xin (critι q u) + μ • emu)))) +
      critπ p (xpart (augField F (μ • emu + (xin (critι q u) + h (xin (critι q u) + μ • emu))) -
        augField F (μ • emu) - fderiv ℝ (augField F) (μ • emu)
          (xin (critι q u) + h (xin (critι q u) + μ • emu)))) := by
  obtain ⟨z, hz⟩ : ∃ z : State (n + 1), z = xin (critι q u) + μ • emu := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : State (n + 1), w = xin (critι q u) + h z := ⟨_, rfl⟩
  rw [← hz, ← hw]
  have hιy : augι (critι q) (xin u + μ • emu) = z := by
    rw [hz, map_add, map_smul, augι_xin, augι_emu]
  have hΛ : z + h z = μ • emu + w := by rw [hw, hz]; abel
  have hhz : critP q p (xpart (h z)) = 0 := by
    have h1 := congrArg xpart (hh.proj_apply z)
    simpa only [augP_apply, map_add, map_smul, xpart_xin, xpart_emu, smul_zero, add_zero,
      map_zero] using h1
  have hπh : critπ p (xpart (h z)) = 0 := by
    have h2 := congrArg (critπ p) hhz
    rwa [critP, ContinuousLinearMap.comp_apply, hc.critπ_critι, map_zero] at h2
  have hmw : mpart w = 0 := by
    have h1 := congrArg mpart (hh.proj_apply z)
    simp only [augP_apply, map_add, map_smul, mpart_xin, mpart_emu, smul_eq_mul, mul_one,
      zero_add, map_zero] at h1
    rw [hw, map_add, mpart_xin, h1, add_zero]
  have hwx : w = xin (xpart w) := by
    rw [← xin_add_smul w, hmw, zero_smul, add_zero, xpart_xin]
  have hΦa : augField F (μ • emu) = 0 := by
    have := augField_xin_add (F := F) 0 μ
    rwa [map_zero, zero_add, hF0, map_zero] at this
  have hDw : fderiv ℝ (augField F) (μ • emu) w =
      xin (fderiv ℝ (fun x => F x μ) 0 (xpart w)) := by
    conv_lhs => rw [hwx]
    exact fderiv_augField_apply hF μ (xpart w)
  have hxw : xpart w = critι q u + xpart (h z) := by rw [hw, map_add, xpart_xin]
  obtain ⟨R, hR⟩ : ∃ R, R = augField F (μ • emu + w) - augField F (μ • emu) -
      fderiv ℝ (augField F) (μ • emu) w := ⟨_, rfl⟩
  rw [← hR]
  have e : augField F (μ • emu + w) = fderiv ℝ (augField F) (μ • emu) w + R := by
    rw [hR, hΦa]; abel
  rw [sliceField, chartField_aug_eq hc hh, hιy, hΛ, xpart_augπ, e, map_add, hDw, xpart_xin, hxw]
  simp only [map_add, _root_.sub_apply, _root_.smul_apply, map_sub,
    map_smul, ContinuousLinearMap.comp_apply, hc.critπ_comp, hc.critπ_apply, hπh, map_zero]
  abel

/-- **The linear regime of the reduced slices.** Let `h` be a graph map over the augmented
centre with strict derivative `0` at `0` whose graph contains the equilibria `(0, μ)` for small
`μ`, and `G` the reduced field of the augmented family. Then, near `0`,
`‖g(μ, u) − R u − μ M u‖ ≤ ε |μ| ‖u‖ + C_q ‖u‖²` for every `ε > 0`, `M = critπ p ∘ B ∘ critι q`,
`C_q` from a Lipschitz bound of `DΦ` near `0` (`Φ` analytic at `0`). -/
@[tmio T, powerlib_foundation] theorem slice_linear_bound (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0) {A : State n →L[ℝ] State n}
    (hA : A = fderiv ℝ (fun x => F x 0) 0) (hc : IsCritical A ω q p)
    {B : State n →L[ℝ] State n} (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    {h : State (n + 1) → State (n + 1)} (hh : IsGraphMap (augP (critP q p)) h)
    (hhs : HasStrictFDerivAt h (0 : State (n + 1) →L[ℝ] State (n + 1)) 0) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hhμ : ∀ μ : ℝ, |μ| < r₀ → h (μ • emu) = 0) :
    ∃ Cq : ℝ, ∀ ε > 0, ∃ r > 0, ∀ (μ : ℝ) (u : State 2), |μ| < r → ‖u‖ < r →
      ‖sliceField (chartField (augL A) (fun z => augField F z - augL A z) h (augι (critι q))
        (augπ (critπ p))) μ u - rotL ω u - μ • ((critπ p).comp (B.comp (critι q))) u‖ ≤
        ε * |μ| * ‖u‖ + Cq * ‖u‖ ^ 2 := by
  have hc2 : ContDiffAt ℝ 2 (augField F) 0 := ha.contDiffAt
  obtain ⟨C₂, s₂, hs₂, hL₂⟩ :=
    (hc2.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.mp hs₂
  have hL₂' := hL₂.mono hball₂
  obtain ⟨Kπ, hKπ⟩ : ∃ K, K = ‖critπ p‖ := ⟨_, rfl⟩
  obtain ⟨Kι, hKι⟩ : ∃ K, K = ‖critι q‖ := ⟨_, rfl⟩
  have hKπ0 : 0 ≤ Kπ := hKπ ▸ norm_nonneg _
  have hKι0 : 0 ≤ Kι := hKι ▸ norm_nonneg _
  refine ⟨Kπ * C₂ * (2 * Kι) ^ 2, fun ε hε => ?_⟩
  -- the parameter derivative of the linear part
  obtain ⟨ε₁, hε₁⟩ : ∃ e, e = min 1 (ε / (2 * (Kπ * Kι + 1))) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := hε₁ ▸ lt_min one_pos (by positivity)
  have hε₁1 : ε₁ ≤ 1 := hε₁ ▸ min_le_left _ _
  have hε₁2 : ε₁ * (Kπ * Kι) ≤ ε / 2 := by
    have h1 : ε₁ ≤ ε / (2 * (Kπ * Kι + 1)) := hε₁ ▸ min_le_right _ _
    calc ε₁ * (Kπ * Kι) ≤ ε / (2 * (Kπ * Kι + 1)) * (Kπ * Kι + 1) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = ε / 2 := by field_simp
  obtain ⟨rB, hrB, hBb⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hB).def hε₁0)
  obtain ⟨θ, hθ⟩ : ∃ e, e = min 1 (ε / (2 * (Kπ * (‖B‖ + 1) * Kι + 1))) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := hθ ▸ lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := hθ ▸ min_le_left _ _
  have hθ2 : θ * (Kπ * (‖B‖ + 1) * Kι) ≤ ε / 2 := by
    have h1 : θ ≤ ε / (2 * (Kπ * (‖B‖ + 1) * Kι + 1)) := hθ ▸ min_le_right _ _
    calc θ * (Kπ * (‖B‖ + 1) * Kι) ≤ ε / (2 * (Kπ * (‖B‖ + 1) * Kι + 1)) *
          (Kπ * (‖B‖ + 1) * Kι + 1) := mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = ε / 2 := by field_simp
  obtain ⟨sh, hsh, hLh⟩ := hhs.exists_lipschitzOnWith_of_nnnorm_lt (Real.toNNReal θ)
    (by simpa using hθ0)
  obtain ⟨rh, hrh, hballh⟩ := Metric.mem_nhds_iff.mp hsh
  obtain ⟨r₁, hr₁⟩ : ∃ r, r = min (rh / (2 * (Kι + 1))) (r₂ / (3 * (Kι + 1))) := ⟨_, rfl⟩
  have hr₁0 : 0 < r₁ := hr₁ ▸ lt_min (by positivity) (by positivity)
  have hm1 : (Kι + 1) * r₁ ≤ rh / 2 := by
    calc (Kι + 1) * r₁ ≤ (Kι + 1) * (rh / (2 * (Kι + 1))) :=
          mul_le_mul_of_nonneg_left (hr₁ ▸ min_le_left _ _) (by positivity)
      _ = rh / 2 := by field_simp
  have hm2 : (Kι + 1) * r₁ ≤ r₂ / 3 := by
    calc (Kι + 1) * r₁ ≤ (Kι + 1) * (r₂ / (3 * (Kι + 1))) :=
          mul_le_mul_of_nonneg_left (hr₁ ▸ min_le_right _ _) (by positivity)
      _ = r₂ / 3 := by field_simp
  refine ⟨min r₀ (min rB r₁), lt_min hr₀ (lt_min hrB hr₁0), fun μ u hμ hu => ?_⟩
  simp only [lt_min_iff] at hμ hu
  obtain ⟨hμ0, hμB, hμ1⟩ := hμ
  obtain ⟨-, -, hu1⟩ := hu
  have hμa : 0 ≤ |μ| := abs_nonneg μ
  have hun : 0 ≤ ‖u‖ := norm_nonneg u
  have hιu : ‖critι q u‖ ≤ Kι * ‖u‖ := hKι ▸ (critι q).le_opNorm u
  have hsum : Kι * ‖u‖ + |μ| ≤ (Kι + 1) * r₁ := by
    have := mul_le_mul_of_nonneg_left hu1.le hKι0
    linarith only [this, hμ1]
  -- the points
  have hne : ‖μ • (emu : State (n + 1))‖ = |μ| := by
    rw [norm_smul, norm_emu, mul_one, Real.norm_eq_abs]
  obtain ⟨z, hz⟩ : ∃ z : State (n + 1), z = xin (critι q u) + μ • emu := ⟨_, rfl⟩
  have hnz : ‖z‖ ≤ Kι * ‖u‖ + |μ| := by
    rw [hz]
    refine (norm_add_le _ _).trans ?_
    rw [norm_xin, hne]
    exact add_le_add hιu le_rfl
  have hzb : z ∈ sh := hballh (mem_ball_zero_iff.mpr (by linarith only [hnz, hsum, hm1, hrh]))
  have hab : μ • emu ∈ sh := hballh (mem_ball_zero_iff.mpr (by
    rw [hne]; linarith only [hsum, hm1, hrh, mul_nonneg hKι0 hun]))
  have hhd : ‖h z‖ ≤ θ * (Kι * ‖u‖) := by
    have h1 := hLh.norm_sub_le hzb hab
    rw [hhμ μ hμ0, sub_zero, Real.coe_toNNReal _ hθ0.le] at h1
    refine h1.trans ?_
    have e : z - μ • emu = xin (critι q u) := by rw [hz]; abel
    rw [e, norm_xin]
    exact mul_le_mul_of_nonneg_left hιu hθ0.le
  obtain ⟨w, hw⟩ : ∃ w : State (n + 1), w = xin (critι q u) + h z := ⟨_, rfl⟩
  have hnw : ‖w‖ ≤ 2 * Kι * ‖u‖ := by
    rw [hw]
    refine (norm_add_le _ _).trans ?_
    rw [norm_xin]
    have : θ * (Kι * ‖u‖) ≤ 1 * (Kι * ‖u‖) :=
      mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hKι0 hun)
    linarith only [hιu, hhd, this]
  have hRb : ‖augField F (μ • emu + w) - augField F (μ • emu) -
      fderiv ℝ (augField F) (μ • emu) w‖ ≤ C₂ * (2 * Kι * ‖u‖) ^ 2 := by
    refine (norm_taylor_le_of_lipschitzOn (hF.differentiable one_ne_zero) hL₂'
      (by rw [hne]; linarith only [hsum, hm2, hr₂, mul_nonneg hKι0 hun]) ?_).trans ?_
    · calc ‖μ • emu + w‖ ≤ ‖μ • (emu : State (n + 1))‖ + ‖w‖ := norm_add_le _ _
        _ < r₂ := by rw [hne]; linarith only [hnw, hsum, hm2, hr₂, hμa]
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnw 2) C₂.2
  -- the derivative of the linear part in the parameter
  have hDB : ‖fderiv ℝ (fun x => F x μ) 0 - A - μ • B‖ ≤ ε₁ * |μ| := by
    have h1 := hBb (show dist μ 0 < rB by rw [dist_zero_right, Real.norm_eq_abs]; exact hμB)
    rwa [← hA, sub_zero, Real.norm_eq_abs] at h1
  have hDA : ‖fderiv ℝ (fun x => F x μ) 0 - A‖ ≤ (‖B‖ + 1) * |μ| := by
    have e : fderiv ℝ (fun x => F x μ) 0 - A = (fderiv ℝ (fun x => F x μ) 0 - A - μ • B) +
        μ • B := by abel
    rw [e]
    have h2 : ‖μ • B‖ ≤ |μ| * ‖B‖ := by
      simpa only [Real.norm_eq_abs] using norm_smul_le μ B
    have h3 : ε₁ * |μ| ≤ 1 * |μ| := mul_le_mul_of_nonneg_right hε₁1 hμa
    linarith only [norm_add_le (fderiv ℝ (fun x => F x μ) 0 - A - μ • B) (μ • B), hDB, h2, h3]
  -- assembly
  rw [slice_sub_eq hF hF0 hc B hh μ u, ← hz, ← hw]
  have t1 : ‖critπ p ((fderiv ℝ (fun x => F x μ) 0 - A - μ • B) (critι q u))‖ ≤
      ε / 2 * |μ| * ‖u‖ := by
    calc _ ≤ Kπ * (‖fderiv ℝ (fun x => F x μ) 0 - A - μ • B‖ * ‖critι q u‖) := by
          rw [hKπ]
          exact ((critπ p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ Kπ * (ε₁ * |μ| * (Kι * ‖u‖)) := by gcongr
      _ = ε₁ * (Kπ * Kι) * (|μ| * ‖u‖) := by ring
      _ ≤ ε / 2 * (|μ| * ‖u‖) := mul_le_mul_of_nonneg_right hε₁2 (by positivity)
      _ = _ := by ring
  have t2 : ‖critπ p ((fderiv ℝ (fun x => F x μ) 0 - A) (xpart (h z)))‖ ≤
      ε / 2 * |μ| * ‖u‖ := by
    calc _ ≤ Kπ * (‖fderiv ℝ (fun x => F x μ) 0 - A‖ * ‖xpart (h z)‖) := by
          rw [hKπ]
          exact ((critπ p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ Kπ * ((‖B‖ + 1) * |μ| * (θ * (Kι * ‖u‖))) := by
          gcongr; exact (norm_xpart_le _).trans hhd
      _ = θ * (Kπ * (‖B‖ + 1) * Kι) * (|μ| * ‖u‖) := by ring
      _ ≤ ε / 2 * (|μ| * ‖u‖) := mul_le_mul_of_nonneg_right hθ2 (by positivity)
      _ = _ := by ring
  have t3 : ‖critπ p (xpart (augField F (μ • emu + w) - augField F (μ • emu) -
      fderiv ℝ (augField F) (μ • emu) w))‖ ≤ Kπ * C₂ * (2 * Kι) ^ 2 * ‖u‖ ^ 2 := by
    calc _ ≤ Kπ * ‖xpart (augField F (μ • emu + w) - augField F (μ • emu) -
          fderiv ℝ (augField F) (μ • emu) w)‖ := hKπ ▸ (critπ p).le_opNorm _
      _ ≤ Kπ * (C₂ * (2 * Kι * ‖u‖) ^ 2) := by
          gcongr; exact (norm_xpart_le _).trans hRb
      _ = _ := by ring
  refine (norm_add₃_le).trans ?_
  linarith only [t1, t2, t3]

/-- The equilibria `(0, μ)` lie on a centre manifold containing the small bounded solutions, and
the reduced field there, with the graph map's strict derivative, gives the uniform remainder of
the slices, the chart identity and the lift of small bounded solutions. -/
@[tmio T, powerlib_foundation] theorem reducedSlice_bounded (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0) {A : State n →L[ℝ] State n}
    (hA : A = fderiv ℝ (fun x => F x 0) 0) (hc : IsCritical A ω q p)
    {B : State n →L[ℝ] State n} (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    {h : State (n + 1) → State (n + 1)} (hh : IsGraphMap (augP (critP q p)) h)
    (hhs : HasStrictFDerivAt h (0 : State (n + 1) →L[ℝ] State (n + 1)) 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hbdd : ∀ φ : ℝ → State (n + 1), (∀ t, HasDerivAt φ (augField F (φ t)) t) →
      (∀ t, ‖φ t‖ < ρ) → ∀ t, φ t ∈ graph (augP (critP q p)) h)
    {L₃ : State (2 + 1) →L[ℝ] State (2 + 1)}
    {Q₃ : State (2 + 1) →L[ℝ] State (2 + 1) →L[ℝ] State (2 + 1)}
    {C₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State (2 + 1)) (State (2 + 1))}
    (hexp : (fun y => chartField (augL A) (fun z => augField F z - augL A z) h (augι (critι q))
      (augπ (critπ p)) y - (L₃ y + Q₃ y y + C₃ ![y, y, y])) =o[𝓝 0] fun y => ‖y‖ ^ 3)
    (hL : ∀ (u : State 2) (μ : ℝ), xpart (L₃ (xin u + μ • emu)) = rotL ω u)
    (hM : sliceM Q₃ = (critπ p).comp (B.comp (critι q))) :
    (fun z : ℝ × State 2 => unfoldRem ((critπ p).comp (B.comp (critι q))) (sliceQ Q₃)
      (sliceC C₃) ω (sliceField (chartField (augL A) (fun z => augField F z - augL A z) h
        (augι (critι q)) (augπ (critπ p)))) z.1 z.2) =o[𝓝 0]
        (fun z => |z.1| * ‖z.2‖ + ‖z.2‖ ^ 3) ∧
    (∀ y, chartField (augL A) (fun z => augField F z - augL A z) h (augι (critι q))
      (augπ (critπ p)) y =
        augπ (critπ p) (augField F (augι (critι q) y + h (augι (critι q) y)))) ∧
    ∀ z : ℝ → State (n + 1), (∀ t, HasDerivAt z (augField F (z t)) t) → (∀ t, ‖z t‖ < ρ) →
      ∀ t, augι (critι q) (augπ (critπ p) (z t)) +
        h (augι (critι q) (augπ (critπ p) (z t))) = z t := by
  have hc3 : IsChart (augP (critP q p)) (augι (critι q)) (augπ (critπ p)) :=
    isChart_aug hc.isChart
  have hhμ : ∀ μ : ℝ, |μ| < ρ → h (μ • emu) = 0 := by
    intro μ hμ
    have hP : augP (critP q p) (μ • emu) = μ • emu := by simp [mpart_apply]
    have h0 : augField F (μ • emu) = 0 := by
      have := augField_xin_add (F := F) 0 μ
      rwa [map_zero, zero_add, hF0, map_zero] at this
    have hg := hbdd (fun _ => μ • emu) (fun t => by
      simpa only [h0] using hasDerivAt_const t (μ • (emu : State (n + 1)))) (fun _ => by
        rwa [norm_smul, norm_emu, mul_one, Real.norm_eq_abs]) 0
    change μ • emu = augP (critP q p) (μ • emu) + h (μ • emu) at hg
    rw [hP] at hg
    simpa using hg.symm
  obtain ⟨Cq, hlin⟩ := slice_linear_bound hF ha hF0 hA hc hB hh hhs hρ hhμ
  rw [← hM] at hlin
  have hfull := isLittleO_unfoldRem_slice_full hexp hL hlin
  rw [hM] at hfull
  refine ⟨hfull, fun y => chartField_aug_eq hc hh y, fun z hz hzρ t => ?_⟩
  have hg := hbdd z hz hzρ t
  change z t = augP (critP q p) (z t) + h (z t) at hg
  rw [hc3.ι_π, hh.comp_proj]
  exact hg.symm

/-- **The parameter-dependent centre manifold.** The augmented field `(x, μ) ↦ (F(x, μ), 0)` has
the three-dimensional centre `range critP ⊕ (parameter axis)`; its locally invariant centre
manifold carries the reduced field `G` on `(u, μ) ∈ ℝ³`, whose parameter component vanishes, so
`μ` is constant along reduced solutions. The slices `g(μ, ·)` form a planar family with the
unfolded cubic expansion (`M = critπ p ∘ B ∘ critι q`, `l₁` of `F(·, 0)`), Lipschitz on a fixed
disc, and reduced solutions near `0` lift, through `Λ(y) = ι y + h(ι y)`, to solutions of the
augmented field with the same parameter and critical coordinates. -/
@[tmio T, powerlib_foundation] theorem exists_reducedSlice (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0)
    (hcp : IsCriticalPair (fun x => F x 0) 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0) :
    ∃ (G : State (2 + 1) → State (2 + 1)) (Λ : State (2 + 1) → State (n + 1))
      (Q₂ : State 2 →L[ℝ] State 2 →L[ℝ] State 2)
      (C₂ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)),
      (∀ K, (fun z : ℝ × State 2 => unfoldRem ((critπ p).comp (B.comp (critι q))) Q₂ C₂ ω
        (sliceField G) z.1 z.2) =o[nhdsW K] fun z => ‖z.2‖ ^ 3) ∧
      (∃ ρ > 0, ∀ μ, |μ| < ρ → ∃ L : NNReal,
        LipschitzOnWith L (sliceField G μ) (Metric.closedBall 0 ρ)) ∧
      l1 (rotL ω) Q₂ C₂ ω = firstLyapunov (fun x => F x 0) 0 ω q p ∧
      (∀ y, mpart (G y) = 0) ∧ (∀ y, mpart (Λ y) = mpart y) ∧
      (∀ y, critπ p (xpart (Λ y)) = xpart y) ∧
      (fun z : ℝ × State 2 => unfoldRem ((critπ p).comp (B.comp (critι q))) Q₂ C₂ ω
        (sliceField G) z.1 z.2) =o[𝓝 0] (fun z => |z.1| * ‖z.2‖ + ‖z.2‖ ^ 3) ∧
      (∀ y, G y = augπ (critπ p) (augField F (Λ y))) ∧
      (∃ rb > 0, ∀ z : ℝ → State (n + 1), (∀ t, HasDerivAt z (augField F (z t)) t) →
        (∀ t, ‖z t‖ < rb) → ∀ t, Λ (augπ (critπ p) (z t)) = z t) ∧
      ∃ rl > 0, ∀ (t₀ t₁ : ℝ) (ψ : ℝ → State (2 + 1)), IsTrajectoryOn ψ G t₀ t₁ →
        (∀ t ∈ Icc t₀ t₁, ‖ψ t‖ < rl) → IsTrajectoryOn (fun t => Λ (ψ t)) (augField F) t₀ t₁ := by
  obtain ⟨A, hA⟩ : ∃ A, A = fderiv ℝ (fun x => F x 0) 0 := ⟨_, rfl⟩
  have hc : IsCritical A ω q p := hA ▸ IsCriticalPair.isCritical hcp rfl
  have hΦd : fderiv ℝ (augField F) 0 = augL A :=
    hA ▸ fderiv_augField_zero (hF.differentiable one_ne_zero 0) hF0
  have hΦ0 : augField F 0 = 0 := by
    have := augField_xin_add (F := F) 0 0
    simpa [hF0] using this
  obtain ⟨f, hfdef⟩ : ∃ f : State (n + 1) → State (n + 1),
      f = fun z => augField F z - augL A z := ⟨_, rfl⟩
  have hff : fullField (augL A) f = augField F := funext fun z => by simp [fullField, hfdef]
  have hf : ContDiff ℝ 1 f := hfdef ▸ hF.sub (augL A).contDiff
  have hf0 : f 0 = 0 := by simp [hfdef, hΦ0]
  have hDf : fderiv ℝ f 0 = 0 := by
    have h := (hF.differentiable one_ne_zero 0).hasFDerivAt.sub (augL A).hasFDerivAt
    rw [hΦd, sub_self] at h
    rw [hfdef]
    exact h.fderiv
  obtain ⟨Qa, hQa⟩ : ∃ Qa, Qa = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (augField F)) 0 := ⟨_, rfl⟩
  obtain ⟨Ca, hCa⟩ : ∃ Ca, Ca = (1 / 6 : ℝ) • iteratedFDeriv ℝ 3 (augField F) 0 := ⟨_, rfl⟩
  have hfQC : (fun z => f z - (Qa z z + Ca ![z, z, z])) =o[𝓝 0] fun z => ‖z‖ ^ 3 := by
    have h43 : (fun z : State (n + 1) => ‖z‖ ^ 4) =o[𝓝 0] fun z => ‖z‖ ^ 3 :=
      Dynamics.isLittleO_pow_of_tendsto tendsto_norm_zero (by norm_num)
    refine ((taylor3_isBigO ha).trans_isLittleO h43).congr_left fun z => ?_
    simp only [hfdef, hΦ0, hΦd, zero_add, hQa, hCa, _root_.smul_apply]
    abel
  have hf2 : (fun z => f z - Qa z z) =O[𝓝 0] fun z => ‖z‖ ^ 3 := by
    have hCb : (fun z : State (n + 1) => Ca ![z, z, z]) =O[𝓝 0] fun z => ‖z‖ ^ 3 :=
      (isBigO_trilin Ca (fun z => z) (fun z => z) fun z => z).congr_right fun z => by ring
    exact (hfQC.isBigO.add hCb).congr_left fun z => by abel
  obtain ⟨K, β, hβ, hcen, hst⟩ := hc.exists_dichotomy (hA ▸ hchar) hr
  have hPa := isCommutingProjection_aug hc.isCommutingProjection
  obtain ⟨Ka, hcena, hsta⟩ := exists_dichotomy_aug le_rfl hcen hst
  obtain ⟨H₀, hhom, hPH⟩ := exists_isHomological_of_dichotomy hPa (by linarith) hcena hsta Qa
  obtain ⟨ρ, hρ, h, Lh, hh, hLh, hH, hh1, hDh0, hinv, hbdd⟩ := exists_centerManifold_bounded hPa
    le_rfl (by linarith) hcena hsta hf hf0 hDf hf2 hhom hPH
  have hc3 : IsChart (augP (critP q p)) (augι (critι q)) (augπ (critπ p)) :=
    isChart_aug hc.isChart
  obtain ⟨G, hGdef⟩ : ∃ G, G = chartField (augL A) f h (augι (critι q)) (augπ (critπ p)) :=
    ⟨_, rfl⟩
  -- the reduced field and its expansion
  have hπm : ∀ v, mpart (augπ (critπ p) v) = mpart v := fun v => by simp
  have hPm : ∀ v, mpart (augP (critP q p) v) = mpart v := fun v => by simp
  have hGm : ∀ y, mpart (G y) = 0 := fun y => by
    simp only [hGdef, chartField, hπm, map_add, augL_apply, mpart_xin, hfdef, map_sub,
      mpart_augField, sub_zero, zero_add]
  have hexp3 : (fun y => G y - (augπ (critπ p) (augL A (augι (critι q) y)) +
      chartQ (augπ (critπ p)) Qa (augι (critι q)) y y +
      chartC (augπ (critπ p)) Qa H₀ Ca (augι (critι q)) ![y, y, y])) =o[𝓝 0]
      fun y => ‖y‖ ^ 3 := by
    refine (chartField_expansion (A := augL A) hc3 hfQC hH).congr_left fun y => ?_
    rw [chartQ_apply, chartC_apply, hGdef]
    simp only [map_add]
    abel
  have hL3 : ∀ (u : State 2) (μ : ℝ),
      xpart ((augπ (critπ p)).comp ((augL A).comp (augι (critι q))) (xin u + μ • emu)) =
        rotL ω u := by
    intro u μ
    simp only [ContinuousLinearMap.comp_apply, map_add, map_smul, augι_xin, augι_emu,
      augL_apply, xpart_xin, xpart_emu, smul_zero, add_zero, map_zero, xpart_augπ]
    exact hc.critπ_comp u
  have hrem := isLittleO_unfoldRem_slice (ω := ω) (G := G)
    (L₃ := (augπ (critπ p)).comp ((augL A).comp (augι (critι q))))
    (Q₃ := chartQ (augπ (critπ p)) Qa (augι (critι q)))
    (C₃ := chartC (augπ (critπ p)) Qa H₀ Ca (augι (critι q))) hexp3 hL3
  have hM := sliceM_chartQ (q := q) (p := p) hF ha hB
  rw [← hQa] at hM
  rw [hM] at hrem
  -- Lipschitz slices
  obtain ⟨Rf, hRf, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf
  obtain ⟨rL, hrL0, hrLR⟩ : ∃ rL : ℝ, 0 < rL ∧ (1 + Lh) * ‖augι (critι q)‖ * rL ≤ Rf := by
    refine ⟨Rf / ((1 + Lh) * ‖augι (critι q)‖ + 1), by positivity, ?_⟩
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (augι (critι q)), Lh.2]
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := augL A) (π := augπ (critπ p))
    hh.map_zero hLh hLf hrLR
  rw [← hGdef] at hLg
  -- the uniform remainder, the chart identity and the bounded solutions
  have hhs : HasStrictFDerivAt h (0 : State (n + 1) →L[ℝ] State (n + 1)) 0 := by
    have := (hh1.contDiffAt (x := 0)).hasStrictFDerivAt (by norm_num)
    rwa [hDh0] at this
  obtain ⟨hfull, hchart, hbd⟩ := reducedSlice_bounded (L₃ := (augπ (critπ p)).comp
    ((augL A).comp (augι (critι q)))) hF ha hF0 hA hc hB hh hhs hρ
    (fun φ hφ hφρ => hbdd φ (fun t => by rw [hff]; exact hφ t) hφρ)
    (by rw [← hfdef, ← hGdef]; exact hexp3) hL3 hM
  -- the lift
  obtain ⟨rl, hrl, hlift⟩ := chart_lift_isTrajectoryOn hPa hh hLh hc3 hf hρ hinv
  refine ⟨G, fun y => augι (critι q) y + h (augι (critι q) y),
    sliceQ (chartQ (augπ (critπ p)) Qa (augι (critι q))),
    sliceC (chartC (augπ (critπ p)) Qa H₀ Ca (augι (critι q))), hrem,
    exists_lipschitzOnWith_slice hrL0 hLg, ?_, hGm, ?_, ?_, by rw [hGdef, hfdef]; exact hfull,
    fun y => by rw [hGdef, hfdef]; exact hchart y, ⟨ρ, hρ, hbd⟩, rl, hrl, ?_⟩
  · rw [hQa, hCa]
    rw [hQa, hA] at hhom
    exact l1_slice_eq hF ha hF0 (hA ▸ hc) hchar hr hhom hPH
  · intro y
    rw [map_add, ← hPm (h _), hh.proj_apply]
    simp
  · intro y
    have h1 : augπ (critπ p) (augι (critι q) y + h (augι (critι q) y)) = y := by
      rw [map_add, hc3.left_inv, ← hc3.π_proj, hh.proj_apply, map_zero, add_zero]
    have h2 := congrArg xpart h1
    rwa [xpart_augπ] at h2
  · intro t₀ t₁ ψ hψ hψr
    have := hlift t₀ t₁ ψ (hGdef ▸ hψ) hψr
    rwa [hff] at this

/-- **The Hopf cycles of a one-parameter family, in any dimension.** Let `ẋ = F(x, μ)` on `ℝⁿ`
with `F(0, μ) = 0` for every `μ`, the augmented field `(x, μ) ↦ (F(x, μ), 0)` of class `C¹` and
analytic at `0`, a critical pair `(q, p)` of `F(·, 0)` at the frequency `ω` with the remaining
eigenvalues in the open left half-plane, first Lyapunov coefficient `l₁ ≠ 0`, and
transversality: `μ ↦ D_x F(0, μ)` has derivative `B` at `0` with
`τ = tr (critπ p ∘ B ∘ critι q) ≠ 0` (twice the speed of the real part of the critical
eigenvalues). Then for every small `μ` with `μ τ l₁ < 0` the field `F(·, μ)` has a nonconstant
periodic orbit, defined for all time, of period at most `4π/ω`, whose critical coordinates
satisfy `ν/8 ≤ ‖critπ p x(t)‖² ≤ 8ν`, `ν = −μτ/(ω l₁) > 0`: the amplitude is of order
`|μ|^{1/2}`. -/
@[tmio T, powerlib_foundation] theorem exists_hopfCycle (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0)
    (hcp : IsCriticalPair (fun x => F x 0) 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    (hτ : PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) ≠ 0)
    (hl : firstLyapunov (fun x => F x 0) 0 ω q p ≠ 0) :
    ∃ δ > 0, ∀ μ, |μ| < δ →
      μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) *
        firstLyapunov (fun x => F x 0) 0 ω q p < 0 →
      ∃ x : ℝ → State n, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
        (∀ t, HasDerivAt x (F (x t) μ) t) ∧ (∀ t, x (t + T) = x t) ∧ (∃ t, x t ≠ x 0) ∧
        ∀ t, -(μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q)))) /
            (ω * firstLyapunov (fun x => F x 0) 0 ω q p) / 8 ≤ ‖critπ p (x t)‖ ^ 2 ∧
          ‖critπ p (x t)‖ ^ 2 ≤ 8 * (-(μ * PlanarHopf.paramTrace
            ((critπ p).comp (B.comp (critι q)))) /
              (ω * firstLyapunov (fun x => F x 0) 0 ω q p)) := by
  obtain ⟨G, Λ, Q₂, C₂, hrem, hlip, hl1, hGm, hΛm, hΛc, -, -, -, rl, hrl, hlift⟩ :=
    exists_reducedSlice hF ha hF0 hcp hchar hr hB
  have hω := hcp.freq_pos
  set τ := PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) with hτdef
  set ℓ := firstLyapunov (fun x => F x 0) 0 ω q p with hℓdef
  obtain ⟨δ, hδ, hcyc⟩ := PlanarHopf.exists_periodicOrbit hω hrem hlip hτ (hl1 ▸ hl)
  rw [hl1] at hcyc
  have hτa : 0 < |τ| := abs_pos.mpr hτ
  have hℓa : 0 < |ℓ| := abs_pos.mpr hl
  refine ⟨min δ (min (rl / 2) (rl ^ 2 * ω * |ℓ| / (32 * |τ|))), by positivity,
    fun μ hμ hsgn => ?_⟩
  obtain ⟨γ, T, hT0, hT, hγd, hγT, hγnc, hγb⟩ :=
    hcyc μ (lt_of_lt_of_le hμ (min_le_left _ _)) hsgn
  have hμ1 : |μ| < rl / 2 := lt_of_lt_of_le hμ ((min_le_right _ _).trans (min_le_left _ _))
  have hμ2 : |μ| < rl ^ 2 * ω * |ℓ| / (32 * |τ|) :=
    lt_of_lt_of_le hμ ((min_le_right _ _).trans (min_le_right _ _))
  -- the planar cycle stays in the lifting ball
  have hν : -(μ * τ) / (ω * ℓ) ≤ |μ| * |τ| / (ω * |ℓ|) := by
    calc -(μ * τ) / (ω * ℓ) ≤ |-(μ * τ) / (ω * ℓ)| := le_abs_self _
      _ = |μ| * |τ| / (ω * |ℓ|) := by
          rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos hω]
  have hsmall : ∀ t, ‖γ t‖ < rl / 2 := by
    intro t
    have h1 := (hγb t).2
    have h2 : |μ| * |τ| / (ω * |ℓ|) < rl ^ 2 / 32 := by
      rw [div_lt_iff₀ (by positivity)]
      have := mul_lt_mul_of_pos_right hμ2 hτa
      calc |μ| * |τ| < rl ^ 2 * ω * |ℓ| / (32 * |τ|) * |τ| := this
        _ = rl ^ 2 / 32 * (ω * |ℓ|) := by field_simp
    have h3 : ‖γ t‖ ^ 2 < (rl / 2) ^ 2 := by nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  set ψ : ℝ → State (2 + 1) := fun t => xin (γ t) + μ • emu with hψ
  have hGψ : ∀ t, G (ψ t) = xin (sliceField G μ (γ t)) := by
    intro t
    rw [ext_iff_parts, hGm, xpart_xin, mpart_xin]
    exact ⟨rfl, rfl⟩
  have hψd : ∀ t, HasDerivAt ψ (G (ψ t)) t := by
    intro t
    rw [hGψ]
    exact (xin.hasFDerivAt.comp_hasDerivAt t (hγd t)).add_const _
  have hψr : ∀ t, ‖ψ t‖ < rl := fun t =>
    lt_of_le_of_lt (norm_xin_add_smul_le _ _) (by linarith [hsmall t])
  have hZd : ∀ t, HasDerivAt (fun s => Λ (ψ s)) (augField F (Λ (ψ t))) t := by
    intro t
    have h := hlift (t - 1) (t + 1) ψ (fun s _ => (hψd s).hasDerivWithinAt) (fun s _ => hψr s)
    exact (h t ⟨by linarith, by linarith⟩).hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))
  have hZm : ∀ t, mpart (Λ (ψ t)) = μ := fun t => by simp [hΛm, hψ]
  have hZc : ∀ t, critπ p (xpart (Λ (ψ t))) = γ t := fun t => by simp [hΛc, hψ]
  refine ⟨fun t => xpart (Λ (ψ t)), T, hT0, hT, fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · have h := xpart.hasFDerivAt.comp_hasDerivAt t (hZd t)
    rw [xpart_augField, hZm] at h
    exact h
  · simp only [hψ, hγT]
  · obtain ⟨t, ht⟩ := hγnc
    refine ⟨t, fun hx => ht ?_⟩
    have := congrArg (critπ p) hx
    rwa [hZc, hZc] at this
  · rw [hZc]
    exact hγb t

end Reduction

end powerlib.Dynamics.HopfCycle
