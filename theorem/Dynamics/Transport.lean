import theorem.Dynamics.State
import theorem.Dynamics.Shift
import theorem.Linear.Transfer

/-! # Transport of the Flow sentences under changes of coordinates and of time scale

Every behavioural sentence of the library is invariant under invertible affine changes of
coordinates. Under a constant positive time scaling every sentence keeps its form with its time
parameters rescaled: decay rates scale with the time base, sampling horizons inversely.

Scope.
* Generic foundation, independent of any model. Autonomous continuous-time fields
  `f : State n → State n` on `State n = EuclideanSpace ℝ (Fin n)`, read through the Flow semantics
  (`theorem/Flow/Defs.lean`: LeanForControl's finite forward solution segments, and the global
  notions `Flow.ForwardComplete`, `Flow.GloballyAsymptoticallyStable`,
  `Flow.GloballyExponentiallyStable`). No linearization is involved.
* Excluded: time-varying coordinate changes (e.g. the rotating abc → dq Park transform `T(θ(t))`),
  nonlinear diffeomorphisms, state-dependent time scaling, and transport of non-autonomous or
  forced systems (port passivity under linear coordinates is `Port.System.passive_conjugate`).
* These are transport laws (foundation results); they do not by themselves assert a property of
  any particular power system. A model family whose field is the transport of another family's
  field uses `holds_transport_iff` to identify the denotations of the two families sentence by
  sentence.

Source: work-sync `theory/T-PU.md` §1.2 / §1.5 (per-unit scaling of states = constant diagonal
change of coordinates), §1.6 (time base `t̂ = ω_B t`, `d/dt = ω_B d/dt̂`, i.e. the per-unit-time
field is `ω_B⁻¹ • f`); equilibrium shift to error coordinates as used in
`theory/T-pll-dynamics.md` / `theory/T-invariant-coordinates.md`.

Results.
* Affine coordinate change `y = φ(x) = T x + c` (`affineCoord`), `T : State n ≃L[ℝ] State n`
  invertible (every invertible linear map of `ℝⁿ` is continuous), `c` arbitrary. The field in the
  new coordinates is `g(y) = T f(φ⁻¹ y) = T f(T⁻¹ (y − c))` (`transportField`). Solutions,
  equilibria, smoothness and the Jacobian (`T ∘ Df(x*) ∘ T⁻¹`) are transported, and **every**
  behavioural sentence of the library holds for `f` at `x*` exactly when it holds for `g` at
  `φ(x*)` (`holds_transport_iff`); forward completeness is invariant as well. The per-sentence
  forms (`lyapunovStable_transport_iff`, …) are corollaries. Scaffold:
  `theorem/FlowSemantics.agda` (satisfaction of the sentences by a field at a point, invariant
  under affine changes of coordinates: `transportSystem`, `invariant`).
* Matrix form: `T = P` for an invertible matrix `P` (`IsUnit P`), acting through
  `Matrix.toEuclideanCLM` (`matrixCoord`); the Jacobian matrix becomes `P A P⁻¹`. Example: the
  planar scaling `(θ, v) ↦ (θ, η v)`, `η ≠ 0` (`scaleMatrix`, `scaleCoord`, `scaleCoord_apply`,
  `scaleCoord_symm_apply`).
* Time scaling `τ = t / c`, `c > 0` (e.g. a per-unit time base): the solutions of `c • f` are the
  solutions of `f` read at `t = c τ` (`isTrajectoryOn_timeScale`,
  `isIntegralCurveOn_Ici_timeScale`).
  Equilibria, forward completeness, Lyapunov stability, instability, local and global asymptotic
  stability, local and global exponential stability (the rate of the estimate scales by `c`) and
  conservation are invariant (`*_smul_iff`); decay at the rate `a` becomes decay at the rate `c a`
  (`decay_smul_iff`); a contraction over the horizon `T` of `c • f` is a contraction over the
  horizon `c T` of `f` (`contraction_smul_iff`), so sampled contraction of `c • f` is contraction of
  `f` over a horizon `c k`, `k` a positive integer (`sampledContraction_smul_iff`); `c k` need not
  be an integer, so this is not the sentence `contractive` of `f` in general. Collected:
  `Flow.Property.timeScale c` (the sentence with its decay rate scaled by `c`) and
  `holds_timeScale_iff` (`P` of `f` is `P.timeScale c` of `c • f`, every `P` but sampled
  contraction). For linear fields every sentence, sampled contraction included (it is the Hurwitz
  property): `holds_timeScale_linear_iff`.

Reuse. The proof of `holds_transport_iff` moves the equilibrium to the origin with
`Flow.Property.holds_shift_iff` (`theorem/Dynamics/Shift.lean`) and conjugates by `T` at the origin.
Lyapunov stability, decay rates and conservation are conjugated by
`Linear.lyapunovStable_conj`, `Linear.decay_conj` and `Linear.conservative_conj`
(`theorem/Linear/Transfer.lean`), unchanged; the remaining sentences (local and global
exponential and asymptotic stability, forward completeness, sampled contraction) are conjugated
here, for arbitrary nonlinear fields (`*_conjEquiv`, collected in `holds_conjEquiv_iff`; forward
completeness is the case `c = 0` of `ForwardComplete.transport`). The
equilibrium-shift lemmas (`Dynamics.*_shift_iff`, `Flow.Property.holds_shift_iff`) are those of
`theorem/Dynamics/Shift.lean` and are not restated.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology

variable {n : ℕ}

private lemma mul_div_add_one_lt {K r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) :
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

@[tmio T, simp, powerlib_foundation] theorem transportField_affineCoord (f : State n → State n)
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

/-- Forward completeness is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem forwardComplete_transport_iff {f : State n → State n} :
    Flow.ForwardComplete (transportField T c f) ↔ Flow.ForwardComplete f := by
  have key : ∀ (S : State n ≃L[ℝ] State n) (d : State n) (g : State n → State n),
      Flow.ForwardComplete g → Flow.ForwardComplete (transportField S d g) := by
    intro S d g h a y₀
    obtain ⟨φ, hφa, hφ⟩ := h a (affineCoord S.symm (-(S.symm d)) y₀)
    exact ⟨fun t => affineCoord S d (φ t), by simp [hφa], isIntegralCurveOn_transport S d hφ⟩
  refine ⟨fun h => ?_, key T c f⟩
  have h' := key T.symm (-(T.symm c)) _ h
  rwa [transportField_symm_transportField] at h'

variable {T c} in
@[powerlib_foundation] theorem ForwardComplete.transport {f : State n → State n}
    (h : Flow.ForwardComplete f) : Flow.ForwardComplete (transportField T c f) :=
  (forwardComplete_transport_iff T c).mpr h

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

end Affine

/-! ### Linear conjugation at the origin

`transportField T 0 g` is the conjugate field `y ↦ T g(T⁻¹ y)`. Each sentence of `g` at the origin
passes to it; the reverse direction is the same statement for `T⁻¹`. -/

section Conj

variable {T : State n ≃L[ℝ] State n}

@[simp, powerlib_foundation] theorem transportField_zero_apply (g : State n → State n)
    (y : State n) : transportField T 0 g y = T (g (T.symm y)) := by
  simp [transportField]

@[simp, powerlib_foundation] theorem affineCoord_zero_apply (x : State n) :
    affineCoord T 0 x = T x := by
  simp [affineCoord]

@[simp, powerlib_foundation] theorem transportField_symm_zero (g : State n → State n) :
    transportField T.symm 0 (transportField T 0 g) = g := by
  funext y
  simp

private lemma transportField_zero_eq_conj (g : State n → State n) :
    transportField T 0 g =
      fun y => (T : State n →L[ℝ] State n) (g ((T.symm : State n →L[ℝ] State n) y)) := by
  funext y
  simp

private lemma symm_apply_coe (x : State n) :
    (T.symm : State n →L[ℝ] State n) ((T : State n →L[ℝ] State n) x) = x := by
  simp

private lemma apply_symm_coe (x : State n) :
    (T : State n →L[ℝ] State n) ((T.symm : State n →L[ℝ] State n) x) = x := by
  simp

/-- A solution of the conjugate field, read back through `T⁻¹`, is a solution of the field. -/
private lemma isIntegralCurveOn_back {g : State n → State n} {χ : ℝ → State n} {s : Set ℝ}
    (hχ : IsIntegralCurveOn χ (fun _ y => transportField T 0 g y) s) :
    IsIntegralCurveOn (fun t => T.symm (χ t)) (fun _ x => g x) s := by
  have h := isIntegralCurveOn_transport T.symm 0 hχ
  rw [transportField_symm_zero] at h
  simpa only [affineCoord_zero_apply] using h

private lemma norm_apply_le (x : State n) :
    ‖T x‖ ≤ ‖(T : State n →L[ℝ] State n)‖ * ‖x‖ := by
  simpa using (T : State n →L[ℝ] State n).le_opNorm x

private lemma tendsto_of_back {χ : ℝ → State n}
    (h : Tendsto (fun t => T.symm (χ t)) atTop (𝓝 0)) : Tendsto χ atTop (𝓝 0) := by
  have h' := ((T.continuous.tendsto 0).comp h)
  simpa [Function.comp_def] using h'

@[powerlib_foundation] theorem isEquilibrium_conjEquiv {g : State n → State n}
    (h : IsEquilibrium g 0) : IsEquilibrium (transportField T 0 g) 0 := by
  unfold IsEquilibrium at h ⊢
  simp [h]

@[powerlib_foundation] theorem lyapunovStable_conjEquiv {g : State n → State n}
    (h : LyapunovStable g 0) : LyapunovStable (transportField T 0 g) 0 := by
  rw [transportField_zero_eq_conj]
  exact Linear.lyapunovStable_conj _ _ symm_apply_coe apply_symm_coe h

@[powerlib_foundation] theorem decay_conjEquiv {g : State n → State n} {a : ℝ}
    (h : Flow.Decay g 0 a) : Flow.Decay (transportField T 0 g) 0 a := by
  rw [transportField_zero_eq_conj]
  exact Linear.decay_conj _ _ symm_apply_coe apply_symm_coe h

@[powerlib_foundation] theorem conservative_conjEquiv {g : State n → State n}
    (h : Flow.Conservative g 0) : Flow.Conservative (transportField T 0 g) 0 := by
  rw [transportField_zero_eq_conj]
  exact Linear.conservative_conj _ _ symm_apply_coe apply_symm_coe h

@[powerlib_foundation] theorem forwardComplete_conjEquiv {g : State n → State n}
    (h : Flow.ForwardComplete g) : Flow.ForwardComplete (transportField T 0 g) :=
  ForwardComplete.transport h

@[powerlib_foundation] theorem locallyExponentiallyStable_conjEquiv {g : State n → State n}
    (h : LocallyExponentiallyStable g 0) :
    LocallyExponentiallyStable (transportField T 0 g) 0 := by
  obtain ⟨r, C, a, hr, hC, ha, hdecay⟩ := h
  set K := ‖(T : State n →L[ℝ] State n)‖
  set K' := ‖(T.symm : State n →L[ℝ] State n)‖
  have hK : 0 ≤ K := norm_nonneg _
  have hK' : 0 ≤ K' := norm_nonneg _
  refine ⟨r / (K' + 1), max 1 (K * K') * C, a, div_pos hr (by linarith),
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hC, ha, ?_⟩
  intro t₀ t₁ χ hχ h0 t ht
  simp only [sub_zero] at h0 ⊢
  have hψ : IsTrajectoryOn (fun t => T.symm (χ t)) g t₀ t₁ := isIntegralCurveOn_back hχ
  have hψ0 : ‖T.symm (χ t₀)‖ ≤ K' * ‖χ t₀‖ := norm_apply_le (T := T.symm) _
  have h0' : ‖T.symm (χ t₀) - 0‖ < r := by
    rw [sub_zero]
    calc _ ≤ K' * ‖χ t₀‖ := hψ0
      _ ≤ K' * (r / (K' + 1)) := mul_le_mul_of_nonneg_left h0.le hK'
      _ < r := mul_div_add_one_lt hK' hr
  have hψt := hdecay t₀ t₁ _ hψ h0' t ht
  simp only [sub_zero] at hψt
  have hE : 0 ≤ C * Real.exp (-a * (t - t₀)) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  calc ‖χ t‖ = ‖T (T.symm (χ t))‖ := by simp
    _ ≤ K * ‖T.symm (χ t)‖ := norm_apply_le _
    _ ≤ K * (C * Real.exp (-a * (t - t₀)) * (K' * ‖χ t₀‖)) :=
        mul_le_mul_of_nonneg_left (hψt.trans (mul_le_mul_of_nonneg_left hψ0 hE)) hK
    _ = (K * K') * C * Real.exp (-a * (t - t₀)) * ‖χ t₀‖ := by ring
    _ ≤ max 1 (K * K') * C * Real.exp (-a * (t - t₀)) * ‖χ t₀‖ := by
        gcongr
        exact le_max_right _ _

@[powerlib_foundation] theorem localAsymptoticStable_conjEquiv {g : State n → State n}
    (h : LocalAsymptoticStable g 0) : LocalAsymptoticStable (transportField T 0 g) 0 := by
  obtain ⟨hs, ρ, hρ, hattr⟩ := h
  set K' := ‖(T.symm : State n →L[ℝ] State n)‖
  have hK' : 0 ≤ K' := norm_nonneg _
  refine ⟨lyapunovStable_conjEquiv hs, ρ / (K' + 1), div_pos hρ (by linarith), ?_⟩
  intro t₀ χ hχ h0
  rw [sub_zero] at h0
  have h0' : ‖T.symm (χ t₀) - 0‖ < ρ := by
    rw [sub_zero]
    calc _ ≤ K' * ‖χ t₀‖ := norm_apply_le (T := T.symm) _
      _ ≤ K' * (ρ / (K' + 1)) := mul_le_mul_of_nonneg_left h0.le hK'
      _ < ρ := mul_div_add_one_lt hK' hρ
  exact tendsto_of_back (hattr t₀ _ (isIntegralCurveOn_back hχ) h0')

@[powerlib_foundation] theorem globalAsymptoticStable_conjEquiv {g : State n → State n}
    (h : GlobalAsymptoticStable g 0) : GlobalAsymptoticStable (transportField T 0 g) 0 :=
  ⟨lyapunovStable_conjEquiv h.1, fun t₀ _ hχ =>
    tendsto_of_back (h.2 t₀ _ (isIntegralCurveOn_back hχ))⟩

@[powerlib_foundation] theorem globallyAsymptoticallyStable_conjEquiv {g : State n → State n}
    (h : Flow.GloballyAsymptoticallyStable g 0) :
    Flow.GloballyAsymptoticallyStable (transportField T 0 g) 0 :=
  ⟨isEquilibrium_conjEquiv h.1, forwardComplete_conjEquiv h.2.1,
    globalAsymptoticStable_conjEquiv h.2.2⟩

@[powerlib_foundation] theorem globallyExponentiallyStable_conjEquiv {g : State n → State n}
    (h : Flow.GloballyExponentiallyStable g 0) :
    Flow.GloballyExponentiallyStable (transportField T 0 g) 0 := by
  obtain ⟨heq, hfc, C, a, hC, ha, hdecay⟩ := h
  set K := ‖(T : State n →L[ℝ] State n)‖
  set K' := ‖(T.symm : State n →L[ℝ] State n)‖
  have hK : 0 ≤ K := norm_nonneg _
  refine ⟨isEquilibrium_conjEquiv heq, forwardComplete_conjEquiv hfc, max 1 (K * K') * C, a,
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hC, ha, ?_⟩
  intro t₀ t₁ χ hχ t ht
  rw [sub_zero, sub_zero]
  have hψ : IsTrajectoryOn (fun t => T.symm (χ t)) g t₀ t₁ := isIntegralCurveOn_back hχ
  have hψ0 : ‖T.symm (χ t₀)‖ ≤ K' * ‖χ t₀‖ := norm_apply_le (T := T.symm) _
  have hψt := hdecay t₀ t₁ _ hψ t ht
  simp only [sub_zero] at hψt
  have hE : 0 ≤ C * Real.exp (-a * (t - t₀)) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  calc ‖χ t‖ = ‖T (T.symm (χ t))‖ := by simp
    _ ≤ K * ‖T.symm (χ t)‖ := norm_apply_le _
    _ ≤ K * (C * Real.exp (-a * (t - t₀)) * (K' * ‖χ t₀‖)) :=
        mul_le_mul_of_nonneg_left (hψt.trans (mul_le_mul_of_nonneg_left hψ0 hE)) hK
    _ = (K * K') * C * Real.exp (-a * (t - t₀)) * ‖χ t₀‖ := by ring
    _ ≤ max 1 (K * K') * C * Real.exp (-a * (t - t₀)) * ‖χ t₀‖ := by
        gcongr
        exact le_max_right _ _

/-- A contraction over the horizon `k` iterates to the horizon `j k`, with the factor `cʲ`
(`c` replaced by `max c 0`). -/
@[powerlib_foundation] theorem sampledContraction_iterate {g : State n → State n} {x : State n}
    {k : ℕ} {c : ℝ}
    (h : ∀ (t₀ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ g t₀ (t₀ + k) →
      ‖φ (t₀ + k) - x‖ ≤ c * ‖φ t₀ - x‖) (j : ℕ) :
    ∀ (t₀ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ g t₀ (t₀ + j * k) →
      ‖φ (t₀ + j * k) - x‖ ≤ max c 0 ^ j * ‖φ t₀ - x‖ := by
  induction j with
  | zero => intro t₀ φ _; simp
  | succ j ih =>
    intro t₀ φ hφ
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hj : (0 : ℝ) ≤ j * k := mul_nonneg (Nat.cast_nonneg j) hk
    have hsplit : t₀ + ((j + 1 : ℕ) : ℝ) * k = t₀ + j * k + k := by push_cast; ring
    rw [hsplit] at hφ ⊢
    have h1 := ih t₀ φ (hφ.mono (Icc_subset_Icc le_rfl (by linarith)))
    have h2 := h (t₀ + j * k) φ (hφ.mono (Icc_subset_Icc (by linarith) le_rfl))
    calc ‖φ (t₀ + j * k + k) - x‖ ≤ c * ‖φ (t₀ + j * k) - x‖ := h2
      _ ≤ max c 0 * ‖φ (t₀ + j * k) - x‖ := by gcongr; exact le_max_left _ _
      _ ≤ max c 0 * (max c 0 ^ j * ‖φ t₀ - x‖) := by gcongr
      _ = max c 0 ^ (j + 1) * ‖φ t₀ - x‖ := by ring

@[powerlib_foundation] theorem sampledContraction_conjEquiv {g : State n → State n}
    (h : Flow.SampledContraction g 0) :
    Flow.SampledContraction (transportField T 0 g) 0 := by
  obtain ⟨k, hk, c, hc, hcon⟩ := h
  set K := ‖(T : State n →L[ℝ] State n)‖ * ‖(T.symm : State n →L[ℝ] State n)‖
  have hK : 0 ≤ K := by positivity
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hc1 : max c 0 < 1 := max_lt hc one_pos
  have hlim : Tendsto (fun j : ℕ => K * max c 0 ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul K
  obtain ⟨m, hm0, hm⟩ :=
    ((eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds one_pos))).exists
  refine ⟨m * k, Nat.mul_pos hm0 hk, K * max c 0 ^ m, hm, fun t₀ χ hχ => ?_⟩
  have hcast : ((m * k : ℕ) : ℝ) = (m : ℝ) * k := by push_cast; ring
  rw [hcast] at hχ ⊢
  rw [sub_zero, sub_zero]
  have hψ : IsTrajectoryOn (fun t => T.symm (χ t)) g t₀ (t₀ + m * k) := isIntegralCurveOn_back hχ
  have hit := sampledContraction_iterate hcon m t₀ _ hψ
  simp only [sub_zero] at hit
  calc ‖χ (t₀ + m * k)‖ = ‖T (T.symm (χ (t₀ + m * k)))‖ := by simp
    _ ≤ ‖(T : State n →L[ℝ] State n)‖ * ‖T.symm (χ (t₀ + m * k))‖ := norm_apply_le _
    _ ≤ ‖(T : State n →L[ℝ] State n)‖ * (max c 0 ^ m * ‖T.symm (χ t₀)‖) := by gcongr
    _ ≤ ‖(T : State n →L[ℝ] State n)‖ *
          (max c 0 ^ m * (‖(T.symm : State n →L[ℝ] State n)‖ * ‖χ t₀‖)) := by
        gcongr
        exact norm_apply_le (T := T.symm) _
    _ = K * max c 0 ^ m * ‖χ t₀‖ := by ring

@[powerlib_foundation] theorem lyapunovStable_conjEquiv_iff {g : State n → State n} :
    LyapunovStable (transportField T 0 g) 0 ↔ LyapunovStable g 0 := by
  refine ⟨fun h => ?_, lyapunovStable_conjEquiv⟩
  have h' := lyapunovStable_conjEquiv (T := T.symm) h
  rwa [transportField_symm_zero] at h'

/-- Each behavioural sentence of `g` at the origin passes to the conjugate field. -/
@[powerlib_foundation] theorem holds_conjEquiv (P : Flow.Property) {g : State n → State n}
    (h : P.holds g 0) : P.holds (transportField T 0 g) 0 := by
  cases P
  case lyapunovStable => exact lyapunovStable_conjEquiv h
  case locallyAsymptoticallyStable => exact localAsymptoticStable_conjEquiv h
  case locallyExponentiallyStable => exact locallyExponentiallyStable_conjEquiv h
  case globallyAsymptoticallyStable => exact globallyAsymptoticallyStable_conjEquiv h
  case globallyExponentiallyStable => exact globallyExponentiallyStable_conjEquiv h
  case unstable => exact fun hs => h (lyapunovStable_conjEquiv_iff.mp hs)
  case decay a => exact decay_conjEquiv h
  case contractive => exact sampledContraction_conjEquiv h
  case conservative => exact conservative_conjEquiv h

/-- Every behavioural sentence is invariant under conjugation by an invertible linear map. -/
@[powerlib_foundation] theorem holds_conjEquiv_iff (P : Flow.Property) {g : State n → State n} :
    P.holds (transportField T 0 g) 0 ↔ P.holds g 0 := by
  refine ⟨fun h => ?_, holds_conjEquiv P⟩
  have h' := holds_conjEquiv (T := T.symm) P h
  rwa [transportField_symm_zero] at h'

end Conj

/-! ### Every sentence under affine coordinate changes -/

section Transport

variable (T : State n ≃L[ℝ] State n) (c : State n)

private lemma transportField_shift (f : State n → State n) (x : State n) :
    (fun z => transportField T c f (z + affineCoord T c x)) =
      transportField T 0 (fun z => f (z + x)) := by
  funext z
  have hz : z + affineCoord T c x - c = z + T x := by simp only [affineCoord]; abel
  simp only [transportField, hz, sub_zero, map_add, ContinuousLinearEquiv.symm_apply_apply]

/-- **Transport law.** Every behavioural sentence of the library holds for `f` at `x` exactly
when it holds for the field in the coordinates `y = T x + c` at the image of `x`. -/
@[powerlib_foundation] theorem holds_transport_iff (P : Flow.Property) {f : State n → State n}
    {x : State n} :
    P.holds (transportField T c f) (affineCoord T c x) ↔ P.holds f x := by
  rw [← Flow.Property.holds_shift_iff P (f := transportField T c f),
    ← Flow.Property.holds_shift_iff P (f := f), transportField_shift]
  exact holds_conjEquiv_iff P

/-- Lyapunov stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem lyapunovStable_transport_iff {f : State n → State n}
    {x : State n} :
    LyapunovStable (transportField T c f) (affineCoord T c x) ↔ LyapunovStable f x :=
  holds_transport_iff T c .lyapunovStable

/-- Instability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem unstable_transport_iff {f : State n → State n} {x : State n} :
    Unstable (transportField T c f) (affineCoord T c x) ↔ Unstable f x :=
  holds_transport_iff T c .unstable

/-- Local exponential stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_transport_iff
    {f : State n → State n} {x : State n} :
    LocallyExponentiallyStable (transportField T c f) (affineCoord T c x) ↔
      LocallyExponentiallyStable f x :=
  holds_transport_iff T c .locallyExponentiallyStable

/-- Local asymptotic stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem localAsymptoticStable_transport_iff
    {f : State n → State n} {x : State n} :
    LocalAsymptoticStable (transportField T c f) (affineCoord T c x) ↔
      LocalAsymptoticStable f x :=
  holds_transport_iff T c .locallyAsymptoticallyStable

/-- Global exponential stability is invariant under invertible affine coordinate changes. -/
@[powerlib_foundation] theorem globallyExponentiallyStable_transport_iff
    {f : State n → State n} {x : State n} :
    Flow.GloballyExponentiallyStable (transportField T c f) (affineCoord T c x) ↔
      Flow.GloballyExponentiallyStable f x :=
  holds_transport_iff T c .globallyExponentiallyStable

/-- Global asymptotic stability (with global existence) is invariant under invertible affine
coordinate changes. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_transport_iff
    {f : State n → State n} {x : State n} :
    Flow.GloballyAsymptoticallyStable (transportField T c f) (affineCoord T c x) ↔
      Flow.GloballyAsymptoticallyStable f x :=
  holds_transport_iff T c .globallyAsymptoticallyStable

/-- LeanForControl's global asymptotic stability (without global existence) is invariant under
invertible affine coordinate changes. -/
@[powerlib_foundation] theorem globalAsymptoticStable_transport_iff
    {f : State n → State n} {x : State n} :
    GlobalAsymptoticStable (transportField T c f) (affineCoord T c x) ↔
      GlobalAsymptoticStable f x := by
  rw [← Dynamics.globalAsymptoticStable_shift_iff (f := transportField T c f),
    ← Dynamics.globalAsymptoticStable_shift_iff (f := f), transportField_shift]
  refine ⟨fun h => ?_, globalAsymptoticStable_conjEquiv⟩
  have h' := globalAsymptoticStable_conjEquiv (T := T.symm) h
  rwa [transportField_symm_zero] at h'

variable {T c}

@[powerlib_foundation] theorem LyapunovStable.transport {f : State n → State n} {x : State n}
    (h : LyapunovStable f x) : LyapunovStable (transportField T c f) (affineCoord T c x) :=
  (lyapunovStable_transport_iff T c).mpr h

@[powerlib_foundation] theorem LocallyExponentiallyStable.transport {f : State n → State n}
    {x : State n} (h : LocallyExponentiallyStable f x) :
    LocallyExponentiallyStable (transportField T c f) (affineCoord T c x) :=
  (locallyExponentiallyStable_transport_iff T c).mpr h

@[powerlib_foundation] theorem LocalAsymptoticStable.transport {f : State n → State n}
    {x : State n} (h : LocalAsymptoticStable f x) :
    LocalAsymptoticStable (transportField T c f) (affineCoord T c x) :=
  (localAsymptoticStable_transport_iff T c).mpr h

@[powerlib_foundation] theorem GloballyExponentiallyStable.transport {f : State n → State n}
    {x : State n} (h : Flow.GloballyExponentiallyStable f x) :
    Flow.GloballyExponentiallyStable (transportField T c f) (affineCoord T c x) :=
  (globallyExponentiallyStable_transport_iff T c).mpr h

@[powerlib_foundation] theorem GlobalAsymptoticStable.transport {f : State n → State n}
    {x : State n} (h : GlobalAsymptoticStable f x) :
    GlobalAsymptoticStable (transportField T c f) (affineCoord T c x) :=
  (globalAsymptoticStable_transport_iff T c).mpr h

@[powerlib_foundation] theorem GloballyAsymptoticallyStable.transport {f : State n → State n}
    {x : State n} (h : Flow.GloballyAsymptoticallyStable f x) :
    Flow.GloballyAsymptoticallyStable (transportField T c f) (affineCoord T c x) :=
  (globallyAsymptoticallyStable_transport_iff T c).mpr h

end Transport

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

/-! ### Scaling one coordinate: `(θ, v) ↦ (θ, η v)` -/

section Scale

open Matrix

/-- Scaling matrix `(θ, v) ↦ (θ, η v)`. -/
def scaleMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, η]

@[powerlib_foundation] theorem scaleMatrix_isUnit {η : ℝ} (hη : η ≠ 0) :
    IsUnit (scaleMatrix η) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simpa [scaleMatrix, Matrix.det_fin_two] using hη

private lemma scaleMatrix_inv {η : ℝ} (hη : η ≠ 0) :
    (scaleMatrix η)⁻¹ = !![1, 0; 0, η⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scaleMatrix, hη]

/-- The coordinate change `(θ, v) ↦ (θ, η v)`. -/
def scaleCoord {η : ℝ} (hη : η ≠ 0) : State 2 ≃L[ℝ] State 2 :=
  matrixCoord (scaleMatrix η) (scaleMatrix_isUnit hη)

@[simp, powerlib_foundation] theorem scaleCoord_apply {η : ℝ} (hη : η ≠ 0) (x : State 2) :
    scaleCoord hη x = WithLp.toLp 2 ![x 0, η * x 1] := by
  ext i
  fin_cases i <;>
    simp [scaleCoord, scaleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp, powerlib_foundation] theorem scaleCoord_symm_apply {η : ℝ} (hη : η ≠ 0) (y : State 2) :
    (scaleCoord hη).symm y = WithLp.toLp 2 ![y 0, y 1 / η] := by
  ext i
  fin_cases i <;>
    simp [scaleCoord, scaleMatrix_inv hη, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      div_eq_inv_mul]

end Scale

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

private lemma mul_inv_cancel_time {c : ℝ} (hc : 0 < c) (s : ℝ) :
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

private lemma inv_smul_smul_field {f : State n → State n} {c : ℝ}
    (hc : 0 < c) : c⁻¹ • (c • f) = f := by
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- Time scaling by `c > 0` preserves Lyapunov stability. -/
@[powerlib_foundation] theorem lyapunovStable_smul_iff {f : State n → State n} {x : State n}
    {c : ℝ} (hc : 0 < c) : LyapunovStable (c • f) x ↔ LyapunovStable f x := by
  refine ⟨fun h => ?_, fun h => LyapunovStable.timeScale hc h⟩
  have h' := LyapunovStable.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

/-- Time scaling by `c > 0` preserves instability. -/
@[powerlib_foundation] theorem unstable_smul_iff {f : State n → State n} {x : State n}
    {c : ℝ} (hc : 0 < c) : Unstable (c • f) x ↔ Unstable f x :=
  (lyapunovStable_smul_iff hc).not

/-- Time scaling by `c > 0` preserves local exponential stability (the rate scales by `c`). -/
@[powerlib_foundation] theorem locallyExponentiallyStable_smul_iff {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) :
    LocallyExponentiallyStable (c • f) x ↔ LocallyExponentiallyStable f x := by
  refine ⟨fun h => ?_, fun h => LocallyExponentiallyStable.timeScale hc h⟩
  have h' := LocallyExponentiallyStable.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

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
  refine ⟨fun h => ?_, fun h => LocalAsymptoticStable.timeScale hc h⟩
  have h' := LocalAsymptoticStable.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

/-- Time scaling by `c ≠ 0` keeps the equilibria. -/
@[powerlib_foundation] theorem isEquilibrium_smul_iff {f : State n → State n} {x : State n}
    {c : ℝ} (hc : c ≠ 0) : IsEquilibrium (c • f) x ↔ IsEquilibrium f x := by
  simp [IsEquilibrium, hc]

/-- A forward-complete solution of `f` from `c t₀`, read at time `c τ`, is a forward-complete
solution of `c • f` from `t₀`. -/
@[powerlib_foundation] theorem ForwardComplete.timeScale {f : State n → State n} {c : ℝ}
    (hc : 0 < c) (h : Flow.ForwardComplete f) : Flow.ForwardComplete (c • f) := by
  intro t₀ x₀
  obtain ⟨φ, hφ0, hφ⟩ := h (c * t₀) x₀
  have hφ' : IsIntegralCurveOn φ (fun _ y => (c⁻¹ • (c • f)) y) (Ici (c * t₀)) := by
    rwa [inv_smul_smul_field hc]
  have hψ := isIntegralCurveOn_Ici_timeScale (inv_pos.mpr hc) hφ'
  rw [inv_inv, inv_mul_cancel_left₀ hc.ne'] at hψ
  exact ⟨fun t => φ (t * c), by show φ (t₀ * c) = x₀; rw [mul_comm]; exact hφ0, hψ⟩

/-- Time scaling by `c > 0` preserves forward completeness. -/
@[powerlib_foundation] theorem forwardComplete_smul_iff {f : State n → State n} {c : ℝ}
    (hc : 0 < c) : Flow.ForwardComplete (c • f) ↔ Flow.ForwardComplete f := by
  refine ⟨fun h => ?_, ForwardComplete.timeScale hc⟩
  have h' := ForwardComplete.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

@[powerlib_foundation] theorem GlobalAsymptoticStable.timeScale {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) (h : GlobalAsymptoticStable f x) :
    GlobalAsymptoticStable (c • f) x := by
  refine ⟨LyapunovStable.timeScale hc h.1, fun s₀ χ hχ => ?_⟩
  have hlim := h.2 (c * s₀) _ (isIntegralCurveOn_Ici_timeScale hc hχ)
  have hχ_eq : χ = (fun t => χ (t * c⁻¹)) ∘ fun s => c * s := by
    funext s
    simp [mul_inv_cancel_time hc]
  rw [hχ_eq]
  exact hlim.comp (tendsto_id.const_mul_atTop hc)

/-- Time scaling by `c > 0` preserves LeanForControl's global asymptotic stability. -/
@[powerlib_foundation] theorem globalAsymptoticStable_smul_iff {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) :
    GlobalAsymptoticStable (c • f) x ↔ GlobalAsymptoticStable f x := by
  refine ⟨fun h => ?_, GlobalAsymptoticStable.timeScale hc⟩
  have h' := GlobalAsymptoticStable.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

/-- Time scaling by `c > 0` preserves global asymptotic stability with global existence. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_smul_iff {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) :
    Flow.GloballyAsymptoticallyStable (c • f) x ↔ Flow.GloballyAsymptoticallyStable f x := by
  simp only [Flow.GloballyAsymptoticallyStable]
  rw [isEquilibrium_smul_iff hc.ne', forwardComplete_smul_iff hc,
    globalAsymptoticStable_smul_iff hc]

/-- An exponential estimate `C e^{-a (t - t₀)}` on every solution segment of `f` is the estimate
`C e^{-c a (s - s₀)}` on every solution segment of `c • f`. -/
private lemma bound_timeScale {f : State n → State n} {x : State n} {c C a : ℝ} (hc : 0 < c)
    (h : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ f t₀ t₁ →
      ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x‖) :
    ∀ (s₀ s₁ : ℝ) (χ : ℝ → State n), IsTrajectoryOn χ (c • f) s₀ s₁ →
      ∀ s ∈ Icc s₀ s₁, ‖χ s - x‖ ≤ C * Real.exp (-(c * a) * (s - s₀)) * ‖χ s₀ - x‖ := by
  intro s₀ s₁ χ hχ s hs
  have hs' : c * s ∈ Icc (c * s₀) (c * s₁) :=
    ⟨mul_le_mul_of_nonneg_left hs.1 hc.le, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
  have := h (c * s₀) (c * s₁) _ (isTrajectoryOn_timeScale hc hχ) (c * s) hs'
  simp only [mul_inv_cancel_time hc] at this
  have hexp : -a * (c * s - c * s₀) = -(c * a) * (s - s₀) := by ring
  rwa [hexp] at this

@[powerlib_foundation] theorem Decay.timeScale {f : State n → State n} {x : State n}
    {c a : ℝ} (hc : 0 < c) (h : Flow.Decay f x a) : Flow.Decay (c • f) x (c * a) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, bound_timeScale hc hC⟩

/-- **Decay rates scale with time.** For `c > 0`, `f` decays at the rate `a` exactly when `c • f`
decays at the rate `c a`. -/
@[powerlib_foundation] theorem decay_smul_iff {f : State n → State n} {x : State n} {c a : ℝ}
    (hc : 0 < c) : Flow.Decay (c • f) x (c * a) ↔ Flow.Decay f x a := by
  refine ⟨fun h => ?_, Decay.timeScale hc⟩
  have h' := Decay.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc, inv_mul_cancel_left₀ hc.ne'] at h'

@[powerlib_foundation] theorem GloballyExponentiallyStable.timeScale {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) (h : Flow.GloballyExponentiallyStable f x) :
    Flow.GloballyExponentiallyStable (c • f) x := by
  obtain ⟨heq, hfc, C, a, hC, ha, hdecay⟩ := h
  exact ⟨(isEquilibrium_smul_iff hc.ne').mpr heq, ForwardComplete.timeScale hc hfc, C, c * a, hC,
    mul_pos hc ha, bound_timeScale hc hdecay⟩

/-- Time scaling by `c > 0` preserves global exponential stability (the rate scales by `c`). -/
@[powerlib_foundation] theorem globallyExponentiallyStable_smul_iff {f : State n → State n}
    {x : State n} {c : ℝ} (hc : 0 < c) :
    Flow.GloballyExponentiallyStable (c • f) x ↔ Flow.GloballyExponentiallyStable f x := by
  refine ⟨fun h => ?_, GloballyExponentiallyStable.timeScale hc⟩
  have h' := GloballyExponentiallyStable.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

@[powerlib_foundation] theorem Conservative.timeScale {f : State n → State n} {x : State n}
    {c : ℝ} (hc : 0 < c) (h : Flow.Conservative f x) : Flow.Conservative (c • f) x := by
  obtain ⟨V, hV, hmin, hcons⟩ := h
  refine ⟨V, hV, hmin, fun s₀ s₁ χ hχ s hs => ?_⟩
  have hs' : c * s ∈ Icc (c * s₀) (c * s₁) :=
    ⟨mul_le_mul_of_nonneg_left hs.1 hc.le, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
  have := hcons (c * s₀) (c * s₁) _ (isTrajectoryOn_timeScale hc hχ) (c * s) hs'
  simpa [mul_inv_cancel_time hc] using this

/-- Time scaling by `c > 0` preserves conservation, with the same energy. -/
@[powerlib_foundation] theorem conservative_smul_iff {f : State n → State n} {x : State n}
    {c : ℝ} (hc : 0 < c) : Flow.Conservative (c • f) x ↔ Flow.Conservative f x := by
  refine ⟨fun h => ?_, Conservative.timeScale hc⟩
  have h' := Conservative.timeScale (inv_pos.mpr hc) h
  rwa [inv_smul_smul_field hc] at h'

private lemma contraction_timeScale {f : State n → State n} {x : State n} {c T ρ : ℝ}
    (hc : 0 < c)
    (h : ∀ (t₀ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ f t₀ (t₀ + c * T) →
      ‖φ (t₀ + c * T) - x‖ ≤ ρ * ‖φ t₀ - x‖) :
    ∀ (s₀ : ℝ) (χ : ℝ → State n), IsTrajectoryOn χ (c • f) s₀ (s₀ + T) →
      ‖χ (s₀ + T) - x‖ ≤ ρ * ‖χ s₀ - x‖ := by
  intro s₀ χ hχ
  have hψ := isTrajectoryOn_timeScale hc hχ
  rw [mul_add] at hψ
  have := h (c * s₀) _ hψ
  have e : (c * s₀ + c * T) * c⁻¹ = s₀ + T := by rw [← mul_add]; exact mul_inv_cancel_time hc _
  simpa only [e, mul_inv_cancel_time hc] using this

/-- **Sampling horizons scale inversely with time.** For `c > 0` the solutions of `c • f` contract
by the factor `ρ` over the horizon `T` exactly when the solutions of `f` contract by `ρ` over the
horizon `c T`: a contraction horizon `T` of `f` is the horizon `T / c` of `c • f`. -/
@[powerlib_foundation] theorem contraction_smul_iff {f : State n → State n} {x : State n} {c : ℝ}
    (hc : 0 < c) (T ρ : ℝ) :
    (∀ (s₀ : ℝ) (χ : ℝ → State n), IsTrajectoryOn χ (c • f) s₀ (s₀ + T) →
        ‖χ (s₀ + T) - x‖ ≤ ρ * ‖χ s₀ - x‖) ↔
      ∀ (t₀ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ f t₀ (t₀ + c * T) →
        ‖φ (t₀ + c * T) - x‖ ≤ ρ * ‖φ t₀ - x‖ := by
  refine ⟨fun h => ?_, contraction_timeScale hc⟩
  have h' := contraction_timeScale (f := c • f) (T := c * T) (inv_pos.mpr hc)
    (by rwa [inv_mul_cancel_left₀ hc.ne'])
  rwa [inv_smul_smul_field hc] at h'

/-- **Sampled contraction under time scaling.** For `c > 0`, sampled contraction of `c • f` is
contraction of the solutions of `f` over a horizon `c k`, `k` a positive integer. -/
@[powerlib_foundation] theorem sampledContraction_smul_iff {f : State n → State n} {x : State n}
    {c : ℝ} (hc : 0 < c) :
    Flow.SampledContraction (c • f) x ↔ ∃ k : ℕ, 0 < k ∧ ∃ ρ < 1, ∀ (t₀ : ℝ) (φ : ℝ → State n),
      IsTrajectoryOn φ f t₀ (t₀ + c * k) → ‖φ (t₀ + c * k) - x‖ ≤ ρ * ‖φ t₀ - x‖ :=
  exists_congr fun k => and_congr_right fun _ => exists_congr fun ρ =>
    and_congr_right fun _ => contraction_smul_iff hc k ρ

end TimeScale

end powerlib.Dynamics

/-! ### The time-scaled sentence -/

namespace powerlib.Flow

/-- The sentence `P` read in the time `τ = t / c`: a decay rate `a` becomes `c a`; every other
sentence keeps its form. -/
def Property.timeScale (c : ℝ) : Property → Property
  | .decay a => .decay (c * a)
  | P => P

@[simp, powerlib_foundation] theorem Property.timeScale_decay (c a : ℝ) :
    (Property.decay a).timeScale c = .decay (c * a) := rfl

@[simp, powerlib_foundation] theorem Property.timeScale_one (P : Property) : P.timeScale 1 = P := by
  cases P <;> simp [Property.timeScale]

@[simp, powerlib_foundation] theorem Property.timeScale_timeScale (P : Property) (c d : ℝ) :
    (P.timeScale c).timeScale d = P.timeScale (d * c) := by
  cases P <;> simp [Property.timeScale, mul_assoc]

/-- Time scaling keeps the attractive sentences. -/
@[simp, powerlib_foundation] theorem Property.attractive_timeScale (P : Property) (c : ℝ) :
    (P.timeScale c).Attractive ↔ P.Attractive := by
  cases P <;> rfl

end powerlib.Flow

namespace powerlib.Dynamics

variable {n : ℕ}

/-- **Time scaling law.** For `c > 0`, every behavioural sentence `P` other than sampled
contraction holds for `f` at `x` exactly when its time-scaled form `P.timeScale c` holds for
`c • f` (the field in the time `τ = t / c`): Lyapunov stability, instability, local and global
asymptotic and exponential stability and conservation are invariant, and decay at the rate `a`
is decay at the rate `c a`. Sampled contraction: `sampledContraction_smul_iff`. -/
@[powerlib_foundation] theorem holds_timeScale_iff {f : State n → State n} {x : State n} {c : ℝ}
    (hc : 0 < c) {P : Flow.Property} (hP : P ≠ .contractive) :
    (P.timeScale c).holds (c • f) x ↔ P.holds f x := by
  cases P with
  | lyapunovStable => exact lyapunovStable_smul_iff hc
  | locallyAsymptoticallyStable => exact localAsymptoticStable_smul_iff hc
  | locallyExponentiallyStable => exact locallyExponentiallyStable_smul_iff hc
  | globallyAsymptoticallyStable => exact globallyAsymptoticallyStable_smul_iff hc
  | globallyExponentiallyStable => exact globallyExponentiallyStable_smul_iff hc
  | unstable => exact unstable_smul_iff hc
  | decay a => exact decay_smul_iff hc
  | contractive => exact absurd rfl hP
  | conservative => exact conservative_smul_iff hc

/-- **Time scaling of linear fields.** For `c > 0` every flow sentence `P` holds for the linear
field of `A` at its centre exactly when `P.timeScale c` holds for the linear field of `c A`;
sampled contraction is invariant here, since for linear fields it is the Hurwitz property. -/
@[powerlib_foundation] theorem holds_timeScale_linear_iff {c : ℝ} (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℝ) (e : State n) (P : Flow.Property) :
    (P.timeScale c).holds (LinearSystems.affineLinearVectorField (c • A) e) e ↔
      P.holds (LinearSystems.affineLinearVectorField A e) e := by
  have hfield : LinearSystems.affineLinearVectorField (c • A) e =
      c • LinearSystems.affineLinearVectorField A e := by
    funext y
    simp [LinearSystems.affineLinearVectorField]
  by_cases hP : P = .contractive
  · subst hP
    change Flow.SampledContraction _ e ↔ Flow.SampledContraction _ e
    rw [Linear.sampledContraction_iff_isHurwitz, Linear.sampledContraction_iff_isHurwitz,
      ← Linear.holds_iff_isHurwitz e Flow.Property.attractive_locallyExponentiallyStable,
      ← Linear.holds_iff_isHurwitz e Flow.Property.attractive_locallyExponentiallyStable, hfield]
    exact locallyExponentiallyStable_smul_iff hc
  · rw [hfield]
    exact holds_timeScale_iff hc hP

end powerlib.Dynamics
