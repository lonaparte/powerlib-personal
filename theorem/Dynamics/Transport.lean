import dependencies.Mathlib
import Mathlib.Analysis.CStarAlgebra.Matrix
import theorem.Dynamics.LyapunovDefs
import theorem.Dynamics.Stability

/-! Transport of stability properties under changes of coordinates and of time scale.

Setting: autonomous continuous-time fields `f : State n → State n` on
`State n = EuclideanSpace ℝ (Fin n)`, with the `powerlib.Dynamics` trajectory semantics
(finite forward solution segments). No linearization is involved.

* Affine coordinate change `y = φ(x) = T x + c`, `T : State n ≃L[ℝ] State n` invertible
  (every invertible linear map of `ℝⁿ` is continuous), `c` arbitrary. The field in the new
  coordinates is `g(y) = T f(φ⁻¹ y) = T f(T⁻¹ (y − c))`. Equilibria, Lyapunov stability,
  instability, local exponential stability, and local asymptotic stability of `x*` for `f`
  are equivalent to the same property of `φ(x*)` for `g`. Smoothness and the Jacobian
  (`T ∘ Df(x*) ∘ T⁻¹`) are transported as well.
* Matrix form: `T = P` for an invertible matrix `P` (`IsUnit P`), acting through
  `Matrix.toEuclideanCLM`; the Jacobian matrix becomes `P A P⁻¹`.
* Equilibrium shift: `φ(x) = x − x*`, `g(y) = f(y + x*)`, moving `x*` to `0`.
* Global (large-signal) properties: forward completeness, `GloballyExponentiallyStable`
  and `GloballyAsymptoticallyStable` are also invariant under affine coordinate changes and
  equilibrium shifts.
* Time scaling `τ = t / c`, `c > 0` (e.g. a per-unit time base): `f` and `c • f` have the
  same Lyapunov stability, instability, local exponential stability (the rate scales by
  `c`), and local asymptotic stability.
* Excluded: time-varying coordinate changes (e.g. the rotating abc → dq Park transform
  `T(θ(t))`), nonlinear diffeomorphisms, state-dependent time scaling, and transport of
  non-autonomous or forced systems.

These are transport laws (foundation results); they do not by themselves assert a
property of any particular power system.

Source: work-sync `theory/T-PU.md` §1.2 / §1.5 (per-unit scaling of states = constant
diagonal change of coordinates), §1.6 (time base `t̂ = ω_B t`, `d/dt = ω_B d/dt̂`, i.e. the
per-unit-time field is `ω_B⁻¹ • f`); equilibrium shift to error coordinates as used in
`theory/T-pll-dynamics.md` / `theory/T-invariant-coordinates.md`.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology

variable {n : ℕ}

@[powerlib_foundation] private lemma mul_div_add_one_lt {K r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) :
    K * (r / (K + 1)) < r := by
  rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
  nlinarith

/-! ### Affine coordinate changes -/

/-- The affine coordinate change `y = T x + c`. -/
def affineCoord (T : State n ≃L[ℝ] State n) (c : State n) (x : State n) : State n :=
  T x + c

/-- The vector field in the coordinates `y = T x + c`: `g(y) = T f(T⁻¹ (y − c))`. -/
def transportField (T : State n ≃L[ℝ] State n) (c : State n) (f : State n → State n)
    (y : State n) : State n :=
  T (f (T.symm (y - c)))

section Affine

variable (T : State n ≃L[ℝ] State n) (c : State n)

@[simp, powerlib_foundation] theorem transportField_affineCoord (f : State n → State n)
    (x : State n) : transportField T c f (affineCoord T c x) = T (f x) := by
  simp [transportField, affineCoord]

@[simp, powerlib_foundation] theorem affineCoord_symm_affineCoord (x : State n) :
    affineCoord T.symm (-(T.symm c)) (affineCoord T c x) = x := by
  simp [affineCoord]

@[simp, powerlib_foundation] theorem affineCoord_affineCoord_symm (y : State n) :
    affineCoord T c (affineCoord T.symm (-(T.symm c)) y) = y := by
  simp [affineCoord]

/-- Transporting back by the inverse coordinate change recovers the original field. -/
@[simp, powerlib_foundation] theorem transportField_symm_transportField
    (f : State n → State n) :
    transportField T.symm (-(T.symm c)) (transportField T c f) = f := by
  funext y
  simp [transportField]

@[powerlib_foundation] theorem continuous_affineCoord : Continuous (affineCoord T c) :=
  T.continuous.add continuous_const

/-- Solutions are mapped to solutions by the affine coordinate change, on any time set. -/
@[powerlib_foundation] theorem isIntegralCurveOn_transport {f : State n → State n}
    {φ : ℝ → State n} {s : Set ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) s) :
    IsIntegralCurveOn (fun t => affineCoord T c (φ t))
      (fun _ y => transportField T c f y) s := by
  intro t ht
  show HasDerivWithinAt _ (transportField T c f (affineCoord T c (φ t))) s t
  rw [transportField_affineCoord]
  exact (T.hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)).add_const c

@[powerlib_foundation] theorem isTrajectoryOn_transport {f : State n → State n}
    {φ : ℝ → State n} {a b : ℝ} (hφ : IsTrajectoryOn φ f a b) :
    IsTrajectoryOn (fun t => affineCoord T c (φ t)) (transportField T c f) a b :=
  isIntegralCurveOn_transport T c hφ

@[powerlib_foundation] private lemma sub_affineCoord (x y : State n) :
    y - affineCoord T c x = T (affineCoord T.symm (-(T.symm c)) y - x) := by
  simp only [affineCoord, map_sub, map_add, map_neg, ContinuousLinearEquiv.apply_symm_apply]
  abel

@[powerlib_foundation] private lemma affineCoord_symm_sub (x y : State n) :
    affineCoord T.symm (-(T.symm c)) y - x = T.symm (y - affineCoord T c x) := by
  simp only [affineCoord, map_sub, map_add, ContinuousLinearEquiv.symm_apply_apply]
  abel

@[powerlib_foundation] private lemma norm_sub_affineCoord_le (x y : State n) :
    ‖y - affineCoord T c x‖ ≤
      ‖(T : State n →L[ℝ] State n)‖ * ‖affineCoord T.symm (-(T.symm c)) y - x‖ := by
  rw [sub_affineCoord T c x y]
  exact (T : State n →L[ℝ] State n).le_opNorm _

@[powerlib_foundation] private lemma norm_affineCoord_symm_sub_le (x y : State n) :
    ‖affineCoord T.symm (-(T.symm c)) y - x‖ ≤
      ‖(T.symm : State n →L[ℝ] State n)‖ * ‖y - affineCoord T c x‖ := by
  rw [affineCoord_symm_sub T c x y]
  exact (T.symm : State n →L[ℝ] State n).le_opNorm _

@[powerlib_foundation] private lemma isTrajectoryOn_back {f : State n → State n}
    {χ : ℝ → State n} {a b : ℝ} (hχ : IsTrajectoryOn χ (transportField T c f) a b) :
    IsTrajectoryOn (fun t => affineCoord T.symm (-(T.symm c)) (χ t)) f a b := by
  have h := isTrajectoryOn_transport T.symm (-(T.symm c)) hχ
  rwa [transportField_symm_transportField] at h

/-- Equilibria correspond under the affine coordinate change. -/
@[powerlib_foundation] theorem transportField_affineCoord_eq_zero_iff
    (f : State n → State n) (x : State n) :
    transportField T c f (affineCoord T c x) = 0 ↔ f x = 0 := by
  rw [transportField_affineCoord, map_eq_zero_iff T T.injective]

@[powerlib_foundation] theorem isEquilibrium_transport_iff (f : State n → State n)
    (x : State n) :
    IsEquilibrium (transportField T c f) (affineCoord T c x) ↔ IsEquilibrium f x :=
  transportField_affineCoord_eq_zero_iff T c f x

@[powerlib_foundation] theorem contDiff_transportField {f : State n → State n} {k : WithTop ℕ∞}
    (hf : ContDiff ℝ k f) : ContDiff ℝ k (transportField T c f) :=
  T.contDiff.comp (hf.comp (T.symm.contDiff.comp (contDiff_id.sub contDiff_const)))

/-- The Jacobian in the new coordinates is `T ∘ Df(x) ∘ T⁻¹`. -/
@[powerlib_foundation] theorem hasFDerivAt_transportField {f : State n → State n}
    {f' : State n →L[ℝ] State n} {x : State n} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (transportField T c f)
      ((T : State n →L[ℝ] State n).comp (f'.comp (T.symm : State n →L[ℝ] State n)))
      (affineCoord T c x) := by
  have hin : HasFDerivAt (fun y => T.symm (y - c)) (T.symm : State n →L[ℝ] State n)
      (affineCoord T c x) := by
    have h := T.symm.hasFDerivAt.comp (affineCoord T c x)
      ((hasFDerivAt_id (affineCoord T c x)).sub_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hx : T.symm (affineCoord T c x - c) = x := by simp [affineCoord]
  have hf' : HasFDerivAt f f' (T.symm (affineCoord T c x - c)) := by rwa [hx]
  exact T.hasFDerivAt.comp (affineCoord T c x) (hf'.comp (affineCoord T c x) hin)

@[powerlib_foundation] theorem fderiv_transportField {f : State n → State n} {x : State n}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (transportField T c f) (affineCoord T c x) =
      (T : State n →L[ℝ] State n).comp
        ((fderiv ℝ f x).comp (T.symm : State n →L[ℝ] State n)) :=
  (hasFDerivAt_transportField T c hf.hasFDerivAt).fderiv

/-! #### Stability transport -/

variable {T c}

@[powerlib_foundation] theorem LyapunovStable.transport {f : State n → State n}
    {x : State n} (h : LyapunovStable f x) :
    LyapunovStable (transportField T c f) (affineCoord T c x) := by
  set K := ‖(T : State n →L[ℝ] State n)‖
  set K' := ‖(T.symm : State n →L[ℝ] State n)‖
  have hK : 0 ≤ K := norm_nonneg _
  have hK' : 0 ≤ K' := norm_nonneg _
  intro ε hε
  obtain ⟨δ, hδ, hstab⟩ := h (ε / (K + 1)) (div_pos hε (by linarith))
  refine ⟨δ / (K' + 1), div_pos hδ (by linarith), ?_⟩
  intro t₀ t₁ χ hχ h0 t ht
  have hφ := isTrajectoryOn_back T c hχ
  have h0' : ‖affineCoord T.symm (-(T.symm c)) (χ t₀) - x‖ < δ :=
    calc _ ≤ K' * ‖χ t₀ - affineCoord T c x‖ := norm_affineCoord_symm_sub_le T c x (χ t₀)
      _ ≤ K' * (δ / (K' + 1)) := mul_le_mul_of_nonneg_left h0.le hK'
      _ < δ := mul_div_add_one_lt hK' hδ
  have hφt := hstab t₀ t₁ _ hφ h0' t ht
  calc ‖χ t - affineCoord T c x‖
      ≤ K * ‖affineCoord T.symm (-(T.symm c)) (χ t) - x‖ := norm_sub_affineCoord_le T c x (χ t)
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hφt.le hK
    _ < ε := mul_div_add_one_lt hK hε

@[powerlib_foundation] theorem LocallyExponentiallyStable.transport {f : State n → State n}
    {x : State n} (h : LocallyExponentiallyStable f x) :
    LocallyExponentiallyStable (transportField T c f) (affineCoord T c x) := by
  obtain ⟨r, C, a, hr, hC, ha, hdecay⟩ := h
  set K := ‖(T : State n →L[ℝ] State n)‖
  set K' := ‖(T.symm : State n →L[ℝ] State n)‖
  have hK : 0 ≤ K := norm_nonneg _
  have hK' : 0 ≤ K' := norm_nonneg _
  refine ⟨r / (K' + 1), max 1 (K * K') * C, a, div_pos hr (by linarith),
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hC, ha, ?_⟩
  intro t₀ t₁ χ hχ h0 t ht
  have hφ := isTrajectoryOn_back T c hχ
  set e₀ := ‖χ t₀ - affineCoord T c x‖
  have hφ0 : ‖affineCoord T.symm (-(T.symm c)) (χ t₀) - x‖ ≤ K' * e₀ :=
    norm_affineCoord_symm_sub_le T c x (χ t₀)
  have h0' : ‖affineCoord T.symm (-(T.symm c)) (χ t₀) - x‖ < r :=
    calc _ ≤ K' * e₀ := hφ0
      _ ≤ K' * (r / (K' + 1)) := mul_le_mul_of_nonneg_left h0.le hK'
      _ < r := mul_div_add_one_lt hK' hr
  have hφt := hdecay t₀ t₁ _ hφ h0' t ht
  have hE : 0 ≤ C * Real.exp (-a * (t - t₀)) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  calc ‖χ t - affineCoord T c x‖
      ≤ K * ‖affineCoord T.symm (-(T.symm c)) (χ t) - x‖ := norm_sub_affineCoord_le T c x (χ t)
    _ ≤ K * (C * Real.exp (-a * (t - t₀)) * (K' * e₀)) :=
        mul_le_mul_of_nonneg_left (hφt.trans (mul_le_mul_of_nonneg_left hφ0 hE)) hK
    _ = (K * K') * C * Real.exp (-a * (t - t₀)) * e₀ := by ring
    _ ≤ max 1 (K * K') * C * Real.exp (-a * (t - t₀)) * e₀ := by
        gcongr
        exact le_max_right _ _

@[powerlib_foundation] theorem LocalAsymptoticStable.transport {f : State n → State n}
    {x : State n} (h : LocalAsymptoticStable f x) :
    LocalAsymptoticStable (transportField T c f) (affineCoord T c x) := by
  obtain ⟨hs, ρ, hρ, hattr⟩ := h
  set K' := ‖(T.symm : State n →L[ℝ] State n)‖
  have hK' : 0 ≤ K' := norm_nonneg _
  refine ⟨LyapunovStable.transport hs, ρ / (K' + 1), div_pos hρ (by linarith), ?_⟩
  intro t₀ χ hχ h0
  have hφ : IsIntegralCurveOn (fun t => affineCoord T.symm (-(T.symm c)) (χ t))
      (fun _ y => f y) (Ici t₀) := by
    have h := isIntegralCurveOn_transport T.symm (-(T.symm c)) hχ
    rwa [transportField_symm_transportField] at h
  have h0' : ‖affineCoord T.symm (-(T.symm c)) (χ t₀) - x‖ < ρ :=
    calc _ ≤ K' * ‖χ t₀ - affineCoord T c x‖ := norm_affineCoord_symm_sub_le T c x (χ t₀)
      _ ≤ K' * (ρ / (K' + 1)) := mul_le_mul_of_nonneg_left h0.le hK'
      _ < ρ := mul_div_add_one_lt hK' hρ
  have hlim := hattr t₀ _ hφ h0'
  have hχ_eq : χ = fun t => affineCoord T c (affineCoord T.symm (-(T.symm c)) (χ t)) := by
    funext t
    simp
  rw [hχ_eq]
  exact ((continuous_affineCoord T c).tendsto x).comp hlim

variable (T c)

/-- Lyapunov stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem lyapunovStable_transport_iff {f : State n → State n}
    {x : State n} :
    LyapunovStable (transportField T c f) (affineCoord T c x) ↔ LyapunovStable f x := by
  refine ⟨fun h => ?_, fun h => h.transport⟩
  have h' := (show LyapunovStable (transportField T c f) (affineCoord T c x) from h).transport
    (T := T.symm) (c := -(T.symm c))
  rwa [transportField_symm_transportField, affineCoord_symm_affineCoord] at h'

/-- Instability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem unstable_transport_iff {f : State n → State n} {x : State n} :
    Unstable (transportField T c f) (affineCoord T c x) ↔ Unstable f x :=
  (lyapunovStable_transport_iff T c).not

/-- Local exponential stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_transport_iff
    {f : State n → State n} {x : State n} :
    LocallyExponentiallyStable (transportField T c f) (affineCoord T c x) ↔
      LocallyExponentiallyStable f x := by
  refine ⟨fun h => ?_, fun h => h.transport⟩
  have h' := (show LocallyExponentiallyStable (transportField T c f) (affineCoord T c x)
    from h).transport (T := T.symm) (c := -(T.symm c))
  rwa [transportField_symm_transportField, affineCoord_symm_affineCoord] at h'

/-- Local asymptotic stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem localAsymptoticStable_transport_iff
    {f : State n → State n} {x : State n} :
    LocalAsymptoticStable (transportField T c f) (affineCoord T c x) ↔
      LocalAsymptoticStable f x := by
  refine ⟨fun h => ?_, fun h => h.transport⟩
  have h' := (show LocalAsymptoticStable (transportField T c f) (affineCoord T c x)
    from h).transport (T := T.symm) (c := -(T.symm c))
  rwa [transportField_symm_transportField, affineCoord_symm_affineCoord] at h'

end Affine

/-! ### Invertible matrices as coordinate changes -/

/-- The coordinate change `x ↦ P x` for an invertible matrix `P`. -/
def matrixCoord (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P) : State n ≃L[ℝ] State n :=
  ContinuousLinearEquiv.unitsEquiv ℝ (State n)
    (hP.map (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))).unit

section MatrixCoord

variable (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P)

@[simp, powerlib_foundation] theorem matrixCoord_apply (x : State n) :
    matrixCoord P hP x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P x := rfl

@[simp, powerlib_foundation] theorem ofLp_matrixCoord (x : State n) :
    WithLp.ofLp (matrixCoord P hP x) = P.mulVec (WithLp.ofLp x) := rfl

@[powerlib_foundation] theorem coe_matrixCoord :
    (matrixCoord P hP : State n →L[ℝ] State n) = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P :=
  rfl

@[powerlib_foundation] theorem coe_matrixCoord_symm :
    ((matrixCoord P hP).symm : State n →L[ℝ] State n) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P⁻¹ := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  ext1 y
  apply (matrixCoord P hP).injective
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  apply WithLp.ofLp_injective
  rw [ofLp_matrixCoord, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv P hdet, Matrix.one_mulVec]

@[simp, powerlib_foundation] theorem matrixCoord_symm_apply (y : State n) :
    (matrixCoord P hP).symm y = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P⁻¹ y := by
  rw [← coe_matrixCoord_symm P hP, ContinuousLinearEquiv.coe_coe]

/-- Matrix form of the Jacobian transport: `Df(x*) = A` becomes `Dg(P x* + c) = P A P⁻¹`. -/
@[powerlib_foundation] theorem fderiv_transportField_matrix (c : State n)
    {f : State n → State n} {x : State n} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : DifferentiableAt ℝ f x)
    (hJac : fderiv ℝ f x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) :
    fderiv ℝ (transportField (matrixCoord P hP) c f) (affineCoord (matrixCoord P hP) c x) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (P * A * P⁻¹) := by
  rw [fderiv_transportField _ c hf, hJac, coe_matrixCoord, coe_matrixCoord_symm, map_mul,
    map_mul]
  rfl

end MatrixCoord

/-! ### Equilibrium shift -/

section Shift

@[powerlib_foundation] private lemma transportField_refl_neg (f : State n → State n)
    (x : State n) :
    transportField (ContinuousLinearEquiv.refl ℝ (State n)) (-x) f = fun y => f (y + x) := by
  funext y
  simp [transportField]

@[powerlib_foundation] private lemma affineCoord_refl_neg (x : State n) :
    affineCoord (ContinuousLinearEquiv.refl ℝ (State n)) (-x) x = 0 := by
  simp [affineCoord]

/-- Shifting the equilibrium to the origin preserves Lyapunov stability. -/
@[powerlib_foundation] theorem lyapunovStable_shift_iff {f : State n → State n}
    {x : State n} : LyapunovStable (fun y => f (y + x)) 0 ↔ LyapunovStable f x := by
  have h := lyapunovStable_transport_iff (ContinuousLinearEquiv.refl ℝ (State n)) (-x)
    (f := f) (x := x)
  rwa [transportField_refl_neg, affineCoord_refl_neg] at h

/-- Shifting the equilibrium to the origin preserves instability. -/
@[powerlib_foundation] theorem unstable_shift_iff {f : State n → State n} {x : State n} :
    Unstable (fun y => f (y + x)) 0 ↔ Unstable f x :=
  lyapunovStable_shift_iff.not

/-- Shifting the equilibrium to the origin preserves local exponential stability. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_shift_iff {f : State n → State n}
    {x : State n} :
    LocallyExponentiallyStable (fun y => f (y + x)) 0 ↔ LocallyExponentiallyStable f x := by
  have h := locallyExponentiallyStable_transport_iff (ContinuousLinearEquiv.refl ℝ (State n))
    (-x) (f := f) (x := x)
  rwa [transportField_refl_neg, affineCoord_refl_neg] at h

/-- Shifting the equilibrium to the origin preserves local asymptotic stability. -/
@[powerlib_foundation] theorem localAsymptoticStable_shift_iff {f : State n → State n}
    {x : State n} :
    LocalAsymptoticStable (fun y => f (y + x)) 0 ↔ LocalAsymptoticStable f x := by
  have h := localAsymptoticStable_transport_iff (ContinuousLinearEquiv.refl ℝ (State n))
    (-x) (f := f) (x := x)
  rwa [transportField_refl_neg, affineCoord_refl_neg] at h

end Shift

/-! ### Time scaling -/

section TimeScale

/-- A solution of `ẋ = c f(x)` on `[s₀, s₁]` read at time `t / c` solves `ẋ = f(x)` on
`[c s₀, c s₁]`. -/
@[powerlib_foundation] theorem isTrajectoryOn_timeScale {f : State n → State n} {c : ℝ}
    (hc : 0 < c) {χ : ℝ → State n} {s₀ s₁ : ℝ} (hχ : IsTrajectoryOn χ (c • f) s₀ s₁) :
    IsTrajectoryOn (fun t => χ (t * c⁻¹)) f (c * s₀) (c * s₁) := by
  have hmaps : MapsTo (fun t => t * c⁻¹) (Icc (c * s₀) (c * s₁)) (Icc s₀ s₁) := by
    intro τ hτ
    simp only [mem_Icc, ← div_eq_mul_inv, le_div_iff₀ hc, div_le_iff₀ hc]
    constructor <;> linarith [hτ.1, hτ.2]
  intro t ht
  have h := (hχ (t * c⁻¹) (hmaps ht)).scomp t
    (hasDerivAt_mul_const c⁻¹).hasDerivWithinAt hmaps
  convert h using 1
  · rfl
  · simp [smul_smul, inv_mul_cancel₀ hc.ne']

@[powerlib_foundation] private lemma mul_inv_cancel_time {c : ℝ} (hc : 0 < c) (s : ℝ) :
    c * s * c⁻¹ = s := by
  field_simp

@[powerlib_foundation] theorem LyapunovStable.timeScale {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) (h : LyapunovStable f x) :
    LyapunovStable (c • f) x := by
  intro ε hε
  obtain ⟨δ, hδ, hstab⟩ := h ε hε
  refine ⟨δ, hδ, fun s₀ s₁ χ hχ h0 s hs => ?_⟩
  have hψ := isTrajectoryOn_timeScale hc hχ
  have hs' : c * s ∈ Icc (c * s₀) (c * s₁) :=
    ⟨mul_le_mul_of_nonneg_left hs.1 hc.le, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
  have := hstab (c * s₀) (c * s₁) _ hψ (by simpa [mul_inv_cancel_time hc] using h0) (c * s) hs'
  simpa [mul_inv_cancel_time hc] using this

@[powerlib_foundation] theorem LocallyExponentiallyStable.timeScale {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) (h : LocallyExponentiallyStable f x) :
    LocallyExponentiallyStable (c • f) x := by
  obtain ⟨r, C, a, hr, hC, ha, hdecay⟩ := h
  refine ⟨r, C, a * c, hr, hC, mul_pos ha hc, fun s₀ s₁ χ hχ h0 s hs => ?_⟩
  have hψ := isTrajectoryOn_timeScale hc hχ
  have hs' : c * s ∈ Icc (c * s₀) (c * s₁) :=
    ⟨mul_le_mul_of_nonneg_left hs.1 hc.le, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
  have := hdecay (c * s₀) (c * s₁) _ hψ (by simpa [mul_inv_cancel_time hc] using h0) (c * s) hs'
  simp only [mul_inv_cancel_time hc] at this
  have hexp : -a * (c * s - c * s₀) = -(a * c) * (s - s₀) := by ring
  rwa [hexp] at this

@[powerlib_foundation] private lemma inv_smul_smul_field {f : State n → State n} {c : ℝ}
    (hc : 0 < c) : c⁻¹ • (c • f) = f := by
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- Time scaling by `c > 0` preserves Lyapunov stability. -/
@[powerlib_foundation] theorem lyapunovStable_smul_iff {f : State n → State n} {x : State n}
    {c : ℝ} (hc : 0 < c) : LyapunovStable (c • f) x ↔ LyapunovStable f x := by
  refine ⟨fun h => ?_, fun h => h.timeScale hc⟩
  have h' := (show LyapunovStable (c • f) x from h).timeScale (inv_pos.mpr hc)
  rwa [inv_smul_smul_field hc] at h'

/-- Time scaling by `c > 0` preserves instability. -/
@[powerlib_foundation] theorem unstable_smul_iff {f : State n → State n} {x : State n}
    {c : ℝ} (hc : 0 < c) : Unstable (c • f) x ↔ Unstable f x :=
  (lyapunovStable_smul_iff hc).not

/-- Time scaling by `c > 0` preserves local exponential stability (the rate scales by `c`). -/
@[powerlib_foundation] theorem locallyExponentiallyStable_smul_iff {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) :
    LocallyExponentiallyStable (c • f) x ↔ LocallyExponentiallyStable f x := by
  refine ⟨fun h => ?_, fun h => h.timeScale hc⟩
  have h' := (show LocallyExponentiallyStable (c • f) x from h).timeScale (inv_pos.mpr hc)
  rwa [inv_smul_smul_field hc] at h'

end TimeScale

/-! ### Global properties under affine coordinate changes -/

section Global

variable {T : State n ≃L[ℝ] State n} {c : State n}

@[powerlib_foundation] theorem ForwardComplete.transport {f : State n → State n}
    (h : ForwardComplete f) : ForwardComplete (transportField T c f) := by
  intro a y₀
  obtain ⟨φ, hφa, hφ⟩ := h a (affineCoord T.symm (-(T.symm c)) y₀)
  exact ⟨fun t => affineCoord T c (φ t), by simp [hφa], isIntegralCurveOn_transport T c hφ⟩

@[powerlib_foundation] theorem GloballyExponentiallyStable.transport {f : State n → State n}
    {x : State n} (h : GloballyExponentiallyStable f x) :
    GloballyExponentiallyStable (transportField T c f) (affineCoord T c x) := by
  obtain ⟨heq, hfc, C, a, hC, ha, hdecay⟩ := h
  set K := ‖(T : State n →L[ℝ] State n)‖
  set K' := ‖(T.symm : State n →L[ℝ] State n)‖
  have hK : 0 ≤ K := norm_nonneg _
  refine ⟨(transportField_affineCoord_eq_zero_iff T c f x).mpr heq, hfc.transport,
    max 1 (K * K') * C, a, one_le_mul_of_one_le_of_one_le (le_max_left _ _) hC, ha, ?_⟩
  intro t₀ t₁ χ hχ t ht
  have hφ := isTrajectoryOn_back T c hχ
  set e₀ := ‖χ t₀ - affineCoord T c x‖
  have hφ0 : ‖affineCoord T.symm (-(T.symm c)) (χ t₀) - x‖ ≤ K' * e₀ :=
    norm_affineCoord_symm_sub_le T c x (χ t₀)
  have hφt := hdecay t₀ t₁ _ hφ t ht
  have hE : 0 ≤ C * Real.exp (-(a * (t - t₀))) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  calc ‖χ t - affineCoord T c x‖
      ≤ K * ‖affineCoord T.symm (-(T.symm c)) (χ t) - x‖ := norm_sub_affineCoord_le T c x (χ t)
    _ ≤ K * (C * Real.exp (-(a * (t - t₀))) * (K' * e₀)) :=
        mul_le_mul_of_nonneg_left (hφt.trans (mul_le_mul_of_nonneg_left hφ0 hE)) hK
    _ = (K * K') * C * Real.exp (-(a * (t - t₀))) * e₀ := by ring
    _ ≤ max 1 (K * K') * C * Real.exp (-(a * (t - t₀))) * e₀ := by
        gcongr
        exact le_max_right _ _

@[powerlib_foundation] theorem TrajectoryGloballyAsymptoticallyStable.transport
    {f : State n → State n} {x : State n} (h : TrajectoryGloballyAsymptoticallyStable f x) :
    TrajectoryGloballyAsymptoticallyStable (transportField T c f) (affineCoord T c x) := by
  obtain ⟨hs, hattr⟩ := h
  refine ⟨LyapunovStable.transport hs, fun t₀ χ hχ => ?_⟩
  have hφ : IsIntegralCurveOn (fun t => affineCoord T.symm (-(T.symm c)) (χ t))
      (fun _ y => f y) (Ici t₀) := by
    have h' := isIntegralCurveOn_transport T.symm (-(T.symm c)) hχ
    rwa [transportField_symm_transportField] at h'
  have hχ_eq : χ = fun t => affineCoord T c (affineCoord T.symm (-(T.symm c)) (χ t)) := by
    funext t
    simp
  rw [hχ_eq]
  exact ((continuous_affineCoord T c).tendsto x).comp (hattr t₀ _ hφ)

@[powerlib_foundation] theorem GloballyAsymptoticallyStable.transport {f : State n → State n}
    {x : State n} (h : GloballyAsymptoticallyStable f x) :
    GloballyAsymptoticallyStable (transportField T c f) (affineCoord T c x) :=
  ⟨(transportField_affineCoord_eq_zero_iff T c f x).mpr h.1, h.2.1.transport,
    TrajectoryGloballyAsymptoticallyStable.transport h.2.2⟩

variable (T c)

@[powerlib_foundation] theorem forwardComplete_transport_iff {f : State n → State n} :
    ForwardComplete (transportField T c f) ↔ ForwardComplete f := by
  refine ⟨fun h => ?_, fun h => h.transport⟩
  have h' := ForwardComplete.transport (T := T.symm) (c := -(T.symm c)) h
  rwa [transportField_symm_transportField] at h'

/-- Global exponential stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem globallyExponentiallyStable_transport_iff
    {f : State n → State n} {x : State n} :
    GloballyExponentiallyStable (transportField T c f) (affineCoord T c x) ↔
      GloballyExponentiallyStable f x := by
  refine ⟨fun h => ?_, fun h => h.transport⟩
  have h' := GloballyExponentiallyStable.transport (T := T.symm) (c := -(T.symm c)) h
  rwa [transportField_symm_transportField, affineCoord_symm_affineCoord] at h'

/-- Global asymptotic stability (with global existence) is invariant under invertible affine
coordinate changes. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_transport_iff
    {f : State n → State n} {x : State n} :
    GloballyAsymptoticallyStable (transportField T c f) (affineCoord T c x) ↔
      GloballyAsymptoticallyStable f x := by
  refine ⟨fun h => ?_, fun h => h.transport⟩
  have h' := GloballyAsymptoticallyStable.transport (T := T.symm) (c := -(T.symm c)) h
  rwa [transportField_symm_transportField, affineCoord_symm_affineCoord] at h'

/-- Shifting the equilibrium to the origin preserves global exponential stability. -/
@[powerlib_foundation] theorem globallyExponentiallyStable_shift_iff {f : State n → State n}
    {x : State n} :
    GloballyExponentiallyStable (fun y => f (y + x)) 0 ↔ GloballyExponentiallyStable f x := by
  have h := globallyExponentiallyStable_transport_iff (ContinuousLinearEquiv.refl ℝ (State n))
    (-x) (f := f) (x := x)
  rwa [transportField_refl_neg, affineCoord_refl_neg] at h

/-- Shifting the equilibrium to the origin preserves global asymptotic stability. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_shift_iff {f : State n → State n}
    {x : State n} :
    GloballyAsymptoticallyStable (fun y => f (y + x)) 0 ↔ GloballyAsymptoticallyStable f x := by
  have h := globallyAsymptoticallyStable_transport_iff
    (ContinuousLinearEquiv.refl ℝ (State n)) (-x) (f := f) (x := x)
  rwa [transportField_refl_neg, affineCoord_refl_neg] at h

end Global

/-! ### Local asymptotic stability under time scaling -/

section TimeScaleAsymptotic

/-- A forward-complete solution of `ẋ = c f(x)` from `s₀`, read at time `t / c`, is a
forward-complete solution of `ẋ = f(x)` from `c s₀`. -/
@[powerlib_foundation] theorem isIntegralCurveOn_Ici_timeScale {f : State n → State n}
    {c : ℝ} (hc : 0 < c) {χ : ℝ → State n} {s₀ : ℝ}
    (hχ : IsIntegralCurveOn χ (fun _ y => (c • f) y) (Ici s₀)) :
    IsIntegralCurveOn (fun t => χ (t * c⁻¹)) (fun _ y => f y) (Ici (c * s₀)) := by
  have hmaps : MapsTo (fun t => t * c⁻¹) (Ici (c * s₀)) (Ici s₀) := by
    intro τ hτ
    simp only [mem_Ici, ← div_eq_mul_inv, le_div_iff₀ hc] at hτ ⊢
    linarith
  intro t ht
  have h := (hχ (t * c⁻¹) (hmaps ht)).scomp t
    (hasDerivAt_mul_const c⁻¹).hasDerivWithinAt hmaps
  convert h using 1
  · rfl
  · simp [smul_smul, inv_mul_cancel₀ hc.ne']

@[powerlib_foundation] theorem LocalAsymptoticStable.timeScale {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) (h : LocalAsymptoticStable f x) :
    LocalAsymptoticStable (c • f) x := by
  obtain ⟨hs, ρ, hρ, hattr⟩ := h
  refine ⟨LyapunovStable.timeScale hc hs, ρ, hρ, fun s₀ χ hχ h0 => ?_⟩
  have hψ := isIntegralCurveOn_Ici_timeScale hc hχ
  have hlim := hattr (c * s₀) _ hψ (by simpa [mul_inv_cancel_time hc] using h0)
  have hχ_eq : χ = (fun t => χ (t * c⁻¹)) ∘ fun s => c * s := by
    funext s
    simp [mul_inv_cancel_time hc]
  rw [hχ_eq]
  exact hlim.comp (tendsto_id.const_mul_atTop hc)

/-- Time scaling by `c > 0` preserves local asymptotic stability. -/
@[powerlib_foundation] theorem localAsymptoticStable_smul_iff {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) :
    LocalAsymptoticStable (c • f) x ↔ LocalAsymptoticStable f x := by
  refine ⟨fun h => ?_, fun h => h.timeScale hc⟩
  have h' := LocalAsymptoticStable.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

end TimeScaleAsymptotic

end powerlib.Dynamics
