import theorem.SingularPerturbation.QuasiSteadyGraph
import theorem.Dynamics.LaSalle.Basin

/-! # Singular perturbation on a quasi-steady graph: region of attraction and decay uniform in `ε`

Tikhonov-type uniformity: one ball around the equilibrium lies in the region of attraction of the
`ε`-system for every small `ε`, and the solutions from it decay at one rate with one overshoot
constant, all independent of `ε`.

Scope.
* Generic statements about an arbitrary globally `C¹` field `f` on `Dynamics.State N` whose
  coordinates are split by an equivalence `e : Fin N ≃ F ⊕ S` into fast (`F`) and slow (`S`)
  ones, and a globally `C¹` graph `Φ` over the slow coordinates on which the fast rows of `f`
  vanish identically (the data of `theorem/SingularPerturbation/QuasiSteadyGraph.lean`); the
  `ε`-system `splitScaledField e ε f` multiplies the fast rows by `ε⁻¹`.
* Continuous time, autonomous, no input. Solutions: Mathlib integral curves on the forward ray
  `[0, ∞)` for the region of attraction (`Flow.regionOfAttraction`: existence of a forward
  solution and convergence of every forward solution; a set of initial states, outside the
  sentence language) and LeanForControl's finite solution segments (`IsTrajectoryOn`) for the
  decay estimate. Local statements: the ball is small, but its radius, the overshoot constant and
  the decay rate do not depend on `ε`. Finite-horizon `O(ε)` approximation of the nonlinear
  system is not claimed (the linear case is `theorem/SingularPerturbation/FiniteHorizon.lean`).

Source: Kokotović–Khalil–O'Reilly, *Singular Perturbation Methods in Control* (1986), Ch. 7
(composite Lyapunov functions, region of attraction independent of `ε`); Khalil, *Nonlinear
Systems* (3rd ed., 2002), Thm. 11.4 and §11.5 (the composite Lyapunov function in the
boundary-layer coordinate `y = z − h(x)`, exponential stability with an estimate of the region of
attraction valid for all `ε < ε*`); work-sync theory/T-singular-perturbation.md §1.3–§1.5,
theory/T-tikhonov.md §1.2 (the boundary-layer coordinate).

Results.
* The split coordinates as continuous linear maps: `slowPart`, `fastPart` (the slow and fast
  coordinates), `fastEmbed` (a fast vector as a state with zero slow part), with
  `slowPart_fastEmbed`, `fastPart_fastEmbed`, `norm_sq_eq_fast_add_slow`, `norm_fastEmbed`,
  `norm_slowPart_le`, `norm_fastPart_le`, `eq_add_fastEmbed` (two states with the same slow part
  differ by a fast vector) and the two parts of the `ε`-system (`slowPart_splitScaledField`,
  `fastPart_splitScaledField`).
* Quadratic forms of symmetric matrices on `EuclideanSpace` over any finite index:
  `inner_toEuclideanCLM_symm`, `inner_lyapunov` (`2 ⟪x, P M x⟫ = −|x|²` from
  `P M + Mᵀ P = −1`), `exists_lower_bound_of_posDef` (`λ |x|² ≤ ⟪x, P x⟫`).
* `compositeLyapunov e Φ s₀ P₀ P₂`: `V(w) = ξᵀ P₀ ξ + ηᵀ P₂ η`, `ξ = s − s₀` (`s` the slow part of
  `w`), `η = z − (Φ s)_fast` (the boundary-layer coordinate); `contDiff_compositeLyapunov`,
  `fderiv_compositeLyapunov` (`V'(w) h = 2⟪ξ, P₀ h_s⟫ + 2⟪η, P₂ (h_f − (Φ'(s) h_s)_fast)⟫`).
* `basinEpsStar f Φ s₀ P₀ R P₂`: an explicit `ε* = 1/(2(c₁² + c₂ + 1))` with
  `c₁ = 2p₀L + 2p₂K(‖R‖ + 1)`, `c₂ = 2p₂KL`, `p₀ = ‖P₀‖`, `p₂ = ‖P₂‖`, `κ = 1/(4(p₀ + p₂ + 1))`,
  `L = ‖f'(Φ s₀)‖ + κ`, `K = ‖Φ'(s₀)‖ + 1` (operator norms); `basinEpsStar_pos`.
* **`uniform_basin_of_lt_basinEpsStar`** — under the hypotheses of
  `locallyExponentiallyStable_of_lt_graphEpsStar` (fast block `A`, reduced Jacobian `R` at the
  equilibrium `Φ s₀`, positive definite Lyapunov matrices `P₀ R + Rᵀ P₀ = −1`,
  `P₂ A + Aᵀ P₂ = −1`), with `f` and `Φ` globally `C¹`: there are `r > 0`, `C ≥ 1`, `a > 0` such
  that for every `ε ∈ (0, basinEpsStar f Φ s₀ P₀ R P₂)` the ball of radius `r` about `Φ s₀` lies
  in the region of attraction of the `ε`-system and every solution segment from the ball
  satisfies `|φ(t) − Φ s₀| ≤ C e^{−a(t − t₀)} |φ(t₀) − Φ s₀|`. Proof: on a ball `W` chosen
  independently of `ε` the mean value inequality gives `|a_s − R ξ| ≤ κ|ξ| + L|η|` for the slow
  rows and `|f_fast − A η| ≤ κ|η|` for the fast rows (they vanish on the graph), so
  `V̇ ≤ −|ξ|²/2 − |η|²/(2ε) + c₁|ξ||η| + c₂|η|² ≤ −|ξ|²/4 − |η|²` for `ε < ε*` (`lie_le`,
  `composite_le`); the sublevel set `{w ∈ W | V w ≤ c}` is compact, positively invariant
  (`Dynamics.LaSalle.isPositivelyInvariant_sublevel_of_isOpen`), and LaSalle's principle
  (`Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel`) puts it in the region of
  attraction; `V̇ ≤ −V/(4(p₀ + p₂ + 1))` and Grönwall (`Dynamics.le_exp_mul_of_hasDerivWithinAt`)
  give the decay with `a = 1/(8(p₀ + p₂ + 1))`. Only `r` comes from continuity (of `f'`, `Φ'`,
  `Φ` and the reduced field's derivative at the equilibrium); `ε*` is explicit.
* `exists_epsStar_uniform_basin_of_graph`: the same with spectrally stable `A` and `R` and some
  `ε* > 0` (`exists_posDef_lyapunov_of_spectrallyStable`).
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Set Metric Filter Topology Matrix
open scoped RealInnerProductSpace

variable {N : ℕ} {F S : Type*} [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S]

/-! ## The split coordinates -/

/-- The slow coordinates of a split state. -/
def slowPart (e : Fin N ≃ F ⊕ S) : Dynamics.State N →L[ℝ] EuclideanSpace ℝ S :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 fun k => w (e.symm (.inr k))
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }

/-- The fast coordinates of a split state. -/
def fastPart (e : Fin N ≃ F ⊕ S) : Dynamics.State N →L[ℝ] EuclideanSpace ℝ F :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 fun i => w (e.symm (.inl i))
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }

/-- A fast vector read as a state with zero slow part. -/
def fastEmbed (e : Fin N ≃ F ⊕ S) : EuclideanSpace ℝ F →L[ℝ] Dynamics.State N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun j => Sum.elim (fun i => v i) (fun _ => 0) (e j)
      map_add' := fun _ _ => by ext j; rcases h : e j with i | k <;> simp [h]
      map_smul' := fun _ _ => by ext j; rcases h : e j with i | k <;> simp [h] }

omit [Fintype F] [DecidableEq F] [DecidableEq S] in
@[tmio T, simp, powerlib_foundation] theorem slowPart_apply (e : Fin N ≃ F ⊕ S)
    (w : Dynamics.State N) (k : S) : slowPart e w k = w (e.symm (.inr k)) := rfl

omit [DecidableEq F] [Fintype S] [DecidableEq S] in
@[tmio T, simp, powerlib_foundation] theorem fastPart_apply (e : Fin N ≃ F ⊕ S)
    (w : Dynamics.State N) (i : F) : fastPart e w i = w (e.symm (.inl i)) := rfl

omit [DecidableEq F] [Fintype S] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem fastEmbed_apply (e : Fin N ≃ F ⊕ S)
    (v : EuclideanSpace ℝ F) (j : Fin N) :
    fastEmbed e v j = Sum.elim (fun i => v i) (fun _ => 0) (e j) := rfl

omit [DecidableEq F] [DecidableEq S] in
@[tmio T, simp, powerlib_foundation] theorem slowPart_fastEmbed (e : Fin N ≃ F ⊕ S)
    (v : EuclideanSpace ℝ F) : slowPart e (fastEmbed e v) = 0 := by
  ext k
  simp [fastEmbed_apply]

omit [DecidableEq F] [Fintype S] [DecidableEq S] in
@[tmio T, simp, powerlib_foundation] theorem fastPart_fastEmbed (e : Fin N ≃ F ⊕ S)
    (v : EuclideanSpace ℝ F) : fastPart e (fastEmbed e v) = v := by
  ext i
  simp [fastEmbed_apply]

omit [DecidableEq F] [DecidableEq S] in
/-- `|w|² = |w_fast|² + |w_slow|²`. -/
@[tmio T, powerlib_foundation] theorem norm_sq_eq_fast_add_slow (e : Fin N ≃ F ⊕ S)
    (w : Dynamics.State N) : ‖w‖ ^ 2 = ‖fastPart e w‖ ^ 2 + ‖slowPart e w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, ← e.symm.sum_comp, Fintype.sum_sum_type]
  rfl

omit [DecidableEq F] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem norm_slowPart_le (e : Fin N ≃ F ⊕ S)
    (w : Dynamics.State N) : ‖slowPart e w‖ ≤ ‖w‖ := by
  have h := norm_sq_eq_fast_add_slow e w
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖fastPart e w‖])

omit [DecidableEq F] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem norm_fastPart_le (e : Fin N ≃ F ⊕ S)
    (w : Dynamics.State N) : ‖fastPart e w‖ ≤ ‖w‖ := by
  have h := norm_sq_eq_fast_add_slow e w
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖slowPart e w‖])

omit [DecidableEq F] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem norm_fastEmbed (e : Fin N ≃ F ⊕ S)
    (v : EuclideanSpace ℝ F) : ‖fastEmbed e v‖ = ‖v‖ := by
  have h := norm_sq_eq_fast_add_slow e (fastEmbed e v)
  rw [fastPart_fastEmbed, slowPart_fastEmbed, norm_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa using h)

omit [DecidableEq F] [DecidableEq S] in
/-- Two states with the same slow part differ by a fast vector. -/
@[tmio T, powerlib_foundation] theorem eq_add_fastEmbed (e : Fin N ≃ F ⊕ S)
    {w w' : Dynamics.State N} (h : slowPart e w = slowPart e w') :
    w = w' + fastEmbed e (fastPart e w - fastPart e w') := by
  ext j
  rw [PiLp.add_apply, fastEmbed_apply]
  rcases hj : e j with i | k
  · have hj' : e.symm (.inl i) = j := by rw [← hj, Equiv.symm_apply_apply]
    simp [hj']
  · have hj' : e.symm (.inr k) = j := by rw [← hj, Equiv.symm_apply_apply]
    have := congrArg (· k) h
    simp only [slowPart_apply, hj'] at this
    simp [this]

omit [Fintype F] [DecidableEq F] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem slowPart_splitScaledField (e : Fin N ≃ F ⊕ S) (ε : ℝ)
    (f : Dynamics.State N → Dynamics.State N) (w : Dynamics.State N) :
    slowPart e (splitScaledField e ε f w) = slowPart e (f w) := by
  ext k
  simp [splitScaledField_slow]

omit [DecidableEq F] [Fintype S] [DecidableEq S] in
@[tmio T, powerlib_foundation] theorem fastPart_splitScaledField (e : Fin N ≃ F ⊕ S) (ε : ℝ)
    (f : Dynamics.State N → Dynamics.State N) (w : Dynamics.State N) :
    fastPart e (splitScaledField e ε f w) = ε⁻¹ • fastPart e (f w) := by
  ext i
  simp [splitScaledField_fast]

/-! ## Quadratic forms of symmetric matrices -/

section Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric matrix gives a symmetric operator: `⟪P x, y⟫ = ⟪x, P y⟫`. -/
@[tmio T, powerlib_foundation] theorem inner_toEuclideanCLM_symm {P : Matrix ι ι ℝ}
    (hP : Pᵀ = P) (x y : EuclideanSpace ℝ ι) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) P x, y⟫ = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) P y⟫ := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM,
    Criteria.dotProduct_mulVec_comm_of_symm hP]

/-- **The Lyapunov identity on `EuclideanSpace`.** A symmetric `P` with `P M + Mᵀ P = −1` gives
`2 ⟪x, P M x⟫ = −|x|²`. -/
@[tmio T, powerlib_foundation] theorem inner_lyapunov {P M : Matrix ι ι ℝ} (hP : Pᵀ = P)
    (hL : P * M + Mᵀ * P = -1) (x : EuclideanSpace ℝ ι) :
    2 * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) P (Matrix.toEuclideanCLM (𝕜 := ℝ) M x)⟫ =
      -‖x‖ ^ 2 := by
  have hn : ‖x‖ ^ 2 = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  have h := congrArg (fun Q => WithLp.ofLp x ⬝ᵥ (Q *ᵥ WithLp.ofLp x)) hL
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add, Matrix.neg_mulVec,
    Matrix.one_mulVec, dotProduct_neg] at h
  rw [Matrix.dotProduct_mulVec (WithLp.ofLp x) Mᵀ, Matrix.vecMul_transpose,
    Criteria.dotProduct_mulVec_comm_of_symm hP _ (M *ᵥ _)] at h
  have h3 := Criteria.dotProduct_mulVec_comm_of_symm hP (WithLp.ofLp x) (M *ᵥ WithLp.ofLp x)
  rw [Matrix.inner_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM, hn]
  linarith

/-- A positive definite matrix bounds its quadratic form from below: `λ |x|² ≤ ⟪x, P x⟫` with
some `λ > 0` (`Flow.quadratic_lower_bound`). -/
@[tmio T, powerlib_foundation] theorem exists_lower_bound_of_posDef {P : Matrix ι ι ℝ}
    (hP : P.PosDef) :
    ∃ l > 0, ∀ x : EuclideanSpace ℝ ι, l * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) P x⟫ := by
  refine Flow.quadratic_lower_bound _
    (continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) P).continuous)
    (fun a x => ?_) (fun x hx => ?_)
  · rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  · rw [Matrix.inner_toEuclideanCLM]
    have hx' : WithLp.ofLp x ≠ 0 := fun h => hx (by ext i; simpa using congrFun h i)
    simpa using hP.dotProduct_mulVec_pos hx'

end Quadratic

/-! ## The composite Lyapunov function -/

/-- The composite Lyapunov function of the two-time-scale system on a quasi-steady graph:
`V(w) = ξᵀ P₀ ξ + ηᵀ P₂ η` with the slow deviation `ξ = s − s₀` (`s` the slow part of `w`) and the
boundary-layer coordinate `η = z − (Φ s)_fast` (`z` the fast part of `w`). -/
def compositeLyapunov (e : Fin N ≃ F ⊕ S) (Φ : EuclideanSpace ℝ S → Dynamics.State N)
    (s₀ : EuclideanSpace ℝ S) (P0 : Matrix S S ℝ) (P2 : Matrix F F ℝ) (w : Dynamics.State N) :
    ℝ :=
  ⟪slowPart e w - s₀, Matrix.toEuclideanCLM (𝕜 := ℝ) P0 (slowPart e w - s₀)⟫ +
    ⟪fastPart e w - fastPart e (Φ (slowPart e w)),
      Matrix.toEuclideanCLM (𝕜 := ℝ) P2 (fastPart e w - fastPart e (Φ (slowPart e w)))⟫

@[tmio T, powerlib_foundation] theorem contDiff_compositeLyapunov (e : Fin N ≃ F ⊕ S)
    {Φ : EuclideanSpace ℝ S → Dynamics.State N} (hΦ : ContDiff ℝ 1 Φ) (s₀ : EuclideanSpace ℝ S)
    (P0 : Matrix S S ℝ) (P2 : Matrix F F ℝ) : ContDiff ℝ 1 (compositeLyapunov e Φ s₀ P0 P2) := by
  have hξ : ContDiff ℝ 1 fun w => slowPart e w - s₀ := (slowPart e).contDiff.sub contDiff_const
  have hη : ContDiff ℝ 1 fun w => fastPart e w - fastPart e (Φ (slowPart e w)) :=
    (fastPart e).contDiff.sub ((fastPart e).contDiff.comp (hΦ.comp (slowPart e).contDiff))
  exact (hξ.inner ℝ ((Matrix.toEuclideanCLM (𝕜 := ℝ) P0).contDiff.comp hξ)).add
    (hη.inner ℝ ((Matrix.toEuclideanCLM (𝕜 := ℝ) P2).contDiff.comp hη))

/-- The derivative of the composite Lyapunov function (symmetric `P₀`, `P₂`):
`V'(w) h = 2 ⟪ξ, P₀ h_s⟫ + 2 ⟪η, P₂ (h_f − (Φ'(s) h_s)_fast)⟫`. -/
@[tmio T, powerlib_foundation] theorem fderiv_compositeLyapunov (e : Fin N ≃ F ⊕ S)
    {Φ : EuclideanSpace ℝ S → Dynamics.State N} (hΦ : Differentiable ℝ Φ)
    (s₀ : EuclideanSpace ℝ S) {P0 : Matrix S S ℝ} {P2 : Matrix F F ℝ} (hP0 : P0ᵀ = P0)
    (hP2 : P2ᵀ = P2) (w h : Dynamics.State N) :
    fderiv ℝ (compositeLyapunov e Φ s₀ P0 P2) w h =
      2 * ⟪slowPart e w - s₀, Matrix.toEuclideanCLM (𝕜 := ℝ) P0 (slowPart e h)⟫ +
        2 * ⟪fastPart e w - fastPart e (Φ (slowPart e w)), Matrix.toEuclideanCLM (𝕜 := ℝ) P2
          (fastPart e h - fastPart e (fderiv ℝ Φ (slowPart e w) (slowPart e h)))⟫ := by
  set Q0 := Matrix.toEuclideanCLM (𝕜 := ℝ) P0
  set Q2 := Matrix.toEuclideanCLM (𝕜 := ℝ) P2
  have hξ : HasFDerivAt (fun w => slowPart e w - s₀) (slowPart e) w :=
    (slowPart e).hasFDerivAt.sub_const s₀
  have hη : HasFDerivAt (fun w => fastPart e w - fastPart e (Φ (slowPart e w)))
      (fastPart e - (fastPart e).comp ((fderiv ℝ Φ (slowPart e w)).comp (slowPart e))) w :=
    (fastPart e).hasFDerivAt.sub ((fastPart e).hasFDerivAt.comp w
      ((hΦ (slowPart e w)).hasFDerivAt.comp w (slowPart e).hasFDerivAt))
  have hV : HasFDerivAt (compositeLyapunov e Φ s₀ P0 P2) _ w :=
    (hξ.inner ℝ (Q0.hasFDerivAt.comp w hξ)).add (hη.inner ℝ (Q2.hasFDerivAt.comp w hη))
  rw [hV.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, _root_.sub_apply, Function.comp_apply]
  have h1 : ⟪slowPart e h, Q0 (slowPart e w - s₀)⟫ = ⟪slowPart e w - s₀, Q0 (slowPart e h)⟫ := by
    rw [← inner_toEuclideanCLM_symm hP0, real_inner_comm]
  have h2 : ⟪fastPart e h - fastPart e (fderiv ℝ Φ (slowPart e w) (slowPart e h)),
      Q2 (fastPart e w - fastPart e (Φ (slowPart e w)))⟫ =
      ⟪fastPart e w - fastPart e (Φ (slowPart e w)),
        Q2 (fastPart e h - fastPart e (fderiv ℝ Φ (slowPart e w) (slowPart e h)))⟫ := by
    rw [← inner_toEuclideanCLM_symm hP2, real_inner_comm]
  rw [h1, h2]
  ring

/-! ## The composite Lyapunov estimate -/

/-- The scalar core of the composite Lyapunov estimate: with `X = |ξ|`, `Y = |η|`, the three
terms of `V̇` (slow, fast scaled by `ε⁻¹`, graph correction) sum to at most `−X²/4 − Y²` once
`ε⁻¹ > 2(c₁² + c₂ + 1)`, `c₁ = 2p₀L + 2p₂K(r + 1)`, `c₂ = 2p₂KL`. -/
@[tmio T, powerlib_foundation] private theorem composite_le {X Y p0 p2 κ L K r εi T1 T2 T3 : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hp2 : 0 ≤ p2) (hK : 0 ≤ K) (hL : 0 ≤ L) (hκ1 : κ ≤ 1)
    (h0 : 2 * p0 * κ ≤ 1 / 2) (h2 : 2 * p2 * κ ≤ 1 / 2)
    (hεi : 2 * ((2 * p0 * L + 2 * p2 * K * (r + 1)) ^ 2 + 2 * p2 * K * L + 1) < εi)
    (hT1 : T1 ≤ -X ^ 2 + 2 * p0 * X * (κ * X + L * Y))
    (hT2 : T2 ≤ εi * (-Y ^ 2 + 2 * p2 * κ * Y ^ 2))
    (hT3 : T3 ≤ 2 * p2 * Y * (K * ((r + κ) * X + L * Y))) :
    T1 + T2 + T3 ≤ -X ^ 2 / 4 - Y ^ 2 := by
  set c1 := 2 * p0 * L + 2 * p2 * K * (r + 1)
  set c2 := 2 * p2 * K * L
  have hεi0 : 0 < εi := lt_of_le_of_lt (by positivity) hεi
  have e1 : 2 * p0 * X * (κ * X + L * Y) ≤ X ^ 2 / 2 + 2 * p0 * L * (X * Y) := by
    have : 2 * p0 * κ * X ^ 2 ≤ X ^ 2 / 2 := by nlinarith [sq_nonneg X]
    nlinarith
  have e2 : εi * (-Y ^ 2 + 2 * p2 * κ * Y ^ 2) ≤ -(εi / 2) * Y ^ 2 := by
    have : 2 * p2 * κ * Y ^ 2 ≤ Y ^ 2 / 2 := by nlinarith [sq_nonneg Y]
    nlinarith
  have e3 : 2 * p2 * Y * (K * ((r + κ) * X + L * Y)) ≤
      2 * p2 * K * (r + 1) * (X * Y) + c2 * Y ^ 2 := by
    have hXY : 0 ≤ X * Y := mul_nonneg hX hY
    have : 2 * p2 * K * κ * (X * Y) ≤ 2 * p2 * K * (X * Y) := by
      have h1 : 0 ≤ 2 * p2 * K * (X * Y) := by positivity
      nlinarith
    nlinarith
  have e4 : c1 * (X * Y) ≤ X ^ 2 / 4 + c1 ^ 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (X / 2 - c1 * Y)]
  have e5 : (c1 ^ 2 + c2 + 1) * Y ^ 2 ≤ (εi / 2) * Y ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg Y)
  nlinarith

/-- `⟪u, Q v⟫ ≤ ‖Q‖ |u| |v|`. -/
@[tmio T, powerlib_foundation] private theorem inner_le_opNorm {Z : Type*} [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] (Q : Z →L[ℝ] Z) (u v : Z) : ⟪u, Q v⟫ ≤ ‖Q‖ * ‖u‖ * ‖v‖ :=
  (real_inner_le_norm _ _).trans (by
    rw [mul_assoc, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (Q.le_opNorm v) (norm_nonneg u))

/-- The composite Lyapunov estimate in operator form: with Lyapunov operators
`2 ⟪x, Q₀ R x⟫ = −|x|²`, `2 ⟪y, Q₂ A y⟫ = −|y|²`, a slow row `a` with `|a − R ξ| ≤ κ|ξ| + L|η|`, a
fast row `b` with `|b − A η| ≤ κ|η|`, a graph correction `|k| ≤ K|a|` and
`κ = 1/(4(‖Q₀‖ + ‖Q₂‖ + 1))`: `2⟪ξ, Q₀ a⟫ + 2⟪η, Q₂ (ε⁻¹ b − k)⟫ ≤ −|ξ|²/4 − |η|²` once
`ε⁻¹ > 2(c₁² + c₂ + 1)`. -/
@[tmio T, powerlib_foundation] private theorem lie_le {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {Q0 R' : X →L[ℝ] X} {Q2 A' : Y →L[ℝ] Y} (hL0 : ∀ x, 2 * ⟪x, Q0 (R' x)⟫ = -‖x‖ ^ 2)
    (hL2 : ∀ y, 2 * ⟪y, Q2 (A' y)⟫ = -‖y‖ ^ 2) {ξ a : X} {η b k : Y} {L K εi : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (ha : ‖a - R' ξ‖ ≤ 1 / (4 * (‖Q0‖ + ‖Q2‖ + 1)) * ‖ξ‖ + L * ‖η‖)
    (hb : ‖b - A' η‖ ≤ 1 / (4 * (‖Q0‖ + ‖Q2‖ + 1)) * ‖η‖) (hk : ‖k‖ ≤ K * ‖a‖)
    (hεi : 2 * ((2 * ‖Q0‖ * L + 2 * ‖Q2‖ * K * (‖R'‖ + 1)) ^ 2 + 2 * ‖Q2‖ * K * L + 1) < εi) :
    2 * ⟪ξ, Q0 a⟫ + 2 * ⟪η, Q2 (εi • b - k)⟫ ≤ -‖ξ‖ ^ 2 / 4 - ‖η‖ ^ 2 := by
  set κ := 1 / (4 * (‖Q0‖ + ‖Q2‖ + 1)) with hκdef
  have hp0 : 0 ≤ ‖Q0‖ := norm_nonneg _
  have hp2 : 0 ≤ ‖Q2‖ := norm_nonneg _
  have hκ1 : κ ≤ 1 := by rw [hκdef, div_le_one (by positivity)]; linarith
  have hκ0 : 2 * ‖Q0‖ * κ ≤ 1 / 2 := by
    rw [hκdef, mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have hκ2 : 2 * ‖Q2‖ * κ ≤ 1 / 2 := by
    rw [hκdef, mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have hεi0 : 0 < εi := lt_of_le_of_lt (by positivity) hεi
  have hT1 : 2 * ⟪ξ, Q0 a⟫ ≤ -‖ξ‖ ^ 2 + 2 * ‖Q0‖ * ‖ξ‖ * (κ * ‖ξ‖ + L * ‖η‖) := by
    have h1 : ⟪ξ, Q0 a⟫ = ⟪ξ, Q0 (R' ξ)⟫ + ⟪ξ, Q0 (a - R' ξ)⟫ := by
      rw [← inner_add_right, ← map_add, add_sub_cancel]
    have h2 := inner_le_opNorm Q0 ξ (a - R' ξ)
    have h3 := hL0 ξ
    have h4 : ‖Q0‖ * ‖ξ‖ * ‖a - R' ξ‖ ≤ ‖Q0‖ * ‖ξ‖ * (κ * ‖ξ‖ + L * ‖η‖) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    rw [h1]; linarith
  have hT2 : 2 * ⟪η, Q2 (εi • b)⟫ ≤ εi * (-‖η‖ ^ 2 + 2 * ‖Q2‖ * κ * ‖η‖ ^ 2) := by
    have h1 : ⟪η, Q2 (εi • b)⟫ = εi * (⟪η, Q2 (A' η)⟫ + ⟪η, Q2 (b - A' η)⟫) := by
      rw [map_smul, inner_smul_right, ← inner_add_right, ← map_add, add_sub_cancel]
    have h2 := inner_le_opNorm Q2 η (b - A' η)
    have h3 := hL2 η
    have h4 : ‖Q2‖ * ‖η‖ * ‖b - A' η‖ ≤ ‖Q2‖ * ‖η‖ * (κ * ‖η‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    rw [h1]
    have h5 : 2 * (⟪η, Q2 (A' η)⟫ + ⟪η, Q2 (b - A' η)⟫) ≤
        -‖η‖ ^ 2 + 2 * ‖Q2‖ * κ * ‖η‖ ^ 2 := by nlinarith
    nlinarith
  have hT3 : -(2 * ⟪η, Q2 k⟫) ≤ 2 * ‖Q2‖ * ‖η‖ * (K * ((‖R'‖ + κ) * ‖ξ‖ + L * ‖η‖)) := by
    have h1 : -⟪η, Q2 k⟫ ≤ ‖Q2‖ * ‖η‖ * ‖k‖ := by
      have := inner_le_opNorm Q2 η (-k)
      rwa [map_neg, inner_neg_right, norm_neg] at this
    have ha' : ‖a‖ ≤ (‖R'‖ + κ) * ‖ξ‖ + L * ‖η‖ := by
      calc ‖a‖ = ‖R' ξ + (a - R' ξ)‖ := by rw [add_sub_cancel]
        _ ≤ ‖R'‖ * ‖ξ‖ + (κ * ‖ξ‖ + L * ‖η‖) :=
          (norm_add_le _ _).trans (add_le_add (R'.le_opNorm ξ) ha)
        _ = _ := by ring
    have h2 : ‖k‖ ≤ K * ((‖R'‖ + κ) * ‖ξ‖ + L * ‖η‖) :=
      hk.trans (mul_le_mul_of_nonneg_left ha' hK)
    have h3 : ‖Q2‖ * ‖η‖ * ‖k‖ ≤ ‖Q2‖ * ‖η‖ * (K * ((‖R'‖ + κ) * ‖ξ‖ + L * ‖η‖)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hsplit : 2 * ⟪ξ, Q0 a⟫ + 2 * ⟪η, Q2 (εi • b - k)⟫ =
      2 * ⟪ξ, Q0 a⟫ + 2 * ⟪η, Q2 (εi • b)⟫ + -(2 * ⟪η, Q2 k⟫) := by
    rw [map_sub, inner_sub_right]; ring
  rw [hsplit]
  exact composite_le (norm_nonneg ξ) (norm_nonneg η) hp2 hK hL hκ1 hκ0 hκ2 hεi hT1 hT2
    (by linarith [hT3])

/-- The mean value step for the fast rows: if `fs ∘ f` vanishes at `p` and the derivative of `f`
stays within `κ` of `f'(w₀)` on a ball containing `p` and `p + ι η`, then
`|fs f(p + ι η) − fs f'(w₀) ι η| ≤ κ |η|` (`‖fs‖, ‖ι‖ ≤ 1`). -/
@[tmio T, powerlib_foundation] private theorem norm_fast_sub_le {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : E → E} (hfd : Differentiable ℝ f) (fs : E →L[ℝ] Y) (ιf : Y →L[ℝ] E) (hfs : ‖fs‖ ≤ 1)
    (hιf : ‖ιf‖ ≤ 1) {w₀ p : E} {ρ κ : ℝ}
    (hD : ∀ u ∈ ball w₀ ρ, ‖fderiv ℝ f u - fderiv ℝ f w₀‖ ≤ κ) (hp : p ∈ ball w₀ ρ) {η : Y}
    (hw : p + ιf η ∈ ball w₀ ρ) (hp0 : fs (f p) = 0) :
    ‖fs (f (p + ιf η)) - fs.comp ((fderiv ℝ f w₀).comp ιf) η‖ ≤ κ * ‖η‖ := by
  have hseg : ∀ v ∈ segment ℝ 0 η, p + ιf v ∈ ball w₀ ρ := by
    intro v hv
    rw [segment_eq_image'] at hv
    obtain ⟨θ, hθ, rfl⟩ := hv
    have hmem : p + θ • ((p + ιf η) - p) ∈ segment ℝ p (p + ιf η) := by
      rw [segment_eq_image']; exact ⟨θ, hθ, rfl⟩
    have := (convex_ball w₀ ρ).segment_subset hp hw hmem
    simpa [map_smul] using this
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hD p hp)
  have hGd : ∀ v ∈ segment ℝ 0 η, HasFDerivWithinAt (fun v => fs (f (p + ιf v)))
      (fs.comp ((fderiv ℝ f (p + ιf v)).comp ιf)) (segment ℝ 0 η) v := fun v _ =>
    (fs.hasFDerivAt.comp v ((hfd _).hasFDerivAt.comp v
      (ιf.hasFDerivAt.const_add p))).hasFDerivWithinAt
  have hGb : ∀ v ∈ segment ℝ 0 η,
      ‖fs.comp ((fderiv ℝ f (p + ιf v)).comp ιf) - fs.comp ((fderiv ℝ f w₀).comp ιf)‖ ≤ κ := by
    intro v hv
    rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
    calc _ ≤ ‖fs‖ * (‖fderiv ℝ f (p + ιf v) - fderiv ℝ f w₀‖ * ‖ιf‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (κ * 1) := by
          gcongr
          exact hD _ (hseg v hv)
      _ = κ := by ring
  have hmv := (convex_segment (0 : Y) η).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    hGd hGb (left_mem_segment ℝ 0 η) (right_mem_segment ℝ 0 η)
  simpa [hp0] using hmv

/-- Two nonnegative numbers whose weighted squares lie below `min l₀ l₂ · m²` are at most `m`. -/
@[tmio T, powerlib_foundation] private theorem le_of_weighted_sq_le {l0 l2 X Y m : ℝ}
    (hl0 : 0 < l0) (hl2 : 0 < l2) (hm : 0 ≤ m) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : l0 * X ^ 2 + l2 * Y ^ 2 ≤ min l0 l2 * m ^ 2) : X ≤ m ∧ Y ≤ m := by
  have hmin : 0 < min l0 l2 := lt_min hl0 hl2
  have h0 : min l0 l2 * X ^ 2 ≤ l0 * X ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg X)
  have h2 : min l0 l2 * Y ^ 2 ≤ l2 * Y ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg Y)
  have hX2 : 0 ≤ l0 * X ^ 2 := by positivity
  have hY2 : 0 ≤ l2 * Y ^ 2 := by positivity
  refine ⟨(pow_le_pow_iff_left₀ hX hm two_ne_zero).mp (le_of_mul_le_mul_left ?_ hmin),
    (pow_le_pow_iff_left₀ hY hm two_ne_zero).mp (le_of_mul_le_mul_left ?_ hmin)⟩ <;> linarith

@[tmio T, powerlib_foundation] private theorem neg_quarter_sub_nonpos (X Y : ℝ) :
    -X ^ 2 / 4 - Y ^ 2 ≤ 0 := by
  nlinarith [sq_nonneg X, sq_nonneg Y]

@[tmio T, powerlib_foundation] private theorem eq_zero_of_neg_quarter {X Y : ℝ}
    (h : 0 ≤ -X ^ 2 / 4 - Y ^ 2) : X = 0 ∧ Y = 0 := by
  have hX : X ^ 2 = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
  have hY : Y ^ 2 = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
  exact ⟨pow_eq_zero_iff two_ne_zero |>.mp hX, pow_eq_zero_iff two_ne_zero |>.mp hY⟩

/-- The state from the split estimate: `n ≤ Y + K X` and `l₀X² + l₂Y² ≤ v` give
`n² ≤ 2(1 + K)² v / min l₀ l₂`. -/
@[tmio T, powerlib_foundation] private theorem sq_le_of_split {X Y n K l0 l2 v : ℝ} (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hK : 0 ≤ K) (hl0 : 0 < l0) (hl2 : 0 < l2) (hn0 : 0 ≤ n)
    (hn : n ≤ Y + K * X) (hv : l0 * X ^ 2 + l2 * Y ^ 2 ≤ v) :
    n ^ 2 ≤ 2 * (1 + K) ^ 2 * (v / min l0 l2) := by
  have hm := lt_min hl0 hl2
  have h1 : n ≤ (1 + K) * (X + Y) := by nlinarith
  have h2 : n ^ 2 ≤ (1 + K) ^ 2 * (X + Y) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hn0 h1 2
  have h3 : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by nlinarith [sq_nonneg (X - Y)]
  have e0 := mul_le_mul_of_nonneg_right (min_le_left l0 l2) (sq_nonneg X)
  have e2 := mul_le_mul_of_nonneg_right (min_le_right l0 l2) (sq_nonneg Y)
  have h5 : X ^ 2 + Y ^ 2 ≤ v / min l0 l2 := by rw [le_div_iff₀ hm]; linarith
  calc n ^ 2 ≤ (1 + K) ^ 2 * (X + Y) ^ 2 := h2
    _ ≤ (1 + K) ^ 2 * (2 * (X ^ 2 + Y ^ 2)) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ ≤ (1 + K) ^ 2 * (2 * (v / min l0 l2)) := by gcongr
    _ = _ := by ring

/-- The energy from the split estimate: `X ≤ n`, `Y ≤ (1 + K) n` and `v ≤ hi (X² + Y²)` give
`v ≤ hi (1 + (1 + K)²) n²`. -/
@[tmio T, powerlib_foundation] private theorem le_mul_sq_of_split {X Y n K hi v : ℝ}
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hhi : 0 ≤ hi) (hX : X ≤ n) (hY : Y ≤ (1 + K) * n)
    (hv : v ≤ hi * (X ^ 2 + Y ^ 2)) : v ≤ hi * (1 + (1 + K) ^ 2) * n ^ 2 := by
  have h1 : X ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hX0 hX 2
  have h2 : Y ^ 2 ≤ (1 + K) ^ 2 * n ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hY0 hY 2
  calc v ≤ hi * (X ^ 2 + Y ^ 2) := hv
    _ ≤ hi * (n ^ 2 + (1 + K) ^ 2 * n ^ 2) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hhi
    _ = _ := by ring

/-- Chaining the two estimates through an energy bound `v_t ≤ E v₀`. -/
@[tmio T, powerlib_foundation] private theorem sq_le_of_energy {nt n0 vt v0 m E H K : ℝ}
    (hm : 0 < m) (hE : 0 ≤ E) (h1 : nt ^ 2 ≤ 2 * (1 + K) ^ 2 * (vt / m)) (h2 : vt ≤ E * v0)
    (h3 : v0 ≤ H * n0 ^ 2) : nt ^ 2 ≤ 2 * (1 + K) ^ 2 * H / m * E * n0 ^ 2 := by
  calc nt ^ 2 ≤ 2 * (1 + K) ^ 2 * (vt / m) := h1
    _ ≤ 2 * (1 + K) ^ 2 * (E * (H * n0 ^ 2) / m) := by
        gcongr; exact h2.trans (mul_le_mul_of_nonneg_left h3 hE)
    _ = _ := by ring

/-! ## The region of attraction uniform in `ε` -/

/-- **The explicit `ε*` of the uniform region of attraction.** With Lyapunov matrices `P₀` of the
reduced Jacobian `R` and `P₂` of the fast block, `p₀ = ‖P₀‖`, `p₂ = ‖P₂‖` (operator norms),
`κ = 1/(4(p₀ + p₂ + 1))`, `L = ‖f'(Φ s₀)‖ + κ`, `K = ‖Φ'(s₀)‖ + 1`:
`ε* = 1/(2(c₁² + c₂ + 1))`, `c₁ = 2p₀L + 2p₂K(‖R‖ + 1)`, `c₂ = 2p₂KL`. -/
def basinEpsStar (f : Dynamics.State N → Dynamics.State N)
    (Φ : EuclideanSpace ℝ S → Dynamics.State N) (s₀ : EuclideanSpace ℝ S) (P0 R : Matrix S S ℝ)
    (P2 : Matrix F F ℝ) : ℝ :=
  (2 * ((2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P0‖ * (‖fderiv ℝ f (Φ s₀)‖ +
      1 / (4 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) P0‖ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P2‖ + 1))) +
    2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P2‖ * (‖fderiv ℝ Φ s₀‖ + 1) *
      (‖Matrix.toEuclideanCLM (𝕜 := ℝ) R‖ + 1)) ^ 2 +
    2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P2‖ * (‖fderiv ℝ Φ s₀‖ + 1) * (‖fderiv ℝ f (Φ s₀)‖ +
      1 / (4 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) P0‖ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P2‖ + 1)))
    + 1))⁻¹

@[tmio T, powerlib_foundation] theorem basinEpsStar_pos
    (f : Dynamics.State N → Dynamics.State N) (Φ : EuclideanSpace ℝ S → Dynamics.State N)
    (s₀ : EuclideanSpace ℝ S) (P0 R : Matrix S S ℝ) (P2 : Matrix F F ℝ) :
    0 < basinEpsStar f Φ s₀ P0 R P2 := by
  unfold basinEpsStar
  positivity

/-- **Region of attraction and exponential decay uniform in `ε`, explicit `ε*` (Tikhonov).** Let
the fast rows of the globally `C¹` field `f` vanish on the globally `C¹` graph `Φ` over the slow
coordinates (split by `e`), with an equilibrium `Φ s₀`, fast block `A` and reduced Jacobian `R`
(the data of `locallyExponentiallyStable_of_lt_graphEpsStar`), and positive definite Lyapunov
matrices `P₀ R + Rᵀ P₀ = −1`, `P₂ A + Aᵀ P₂ = −1`. There are `r > 0`, `C ≥ 1` and `a > 0` such that
for every `ε ∈ (0, basinEpsStar f Φ s₀ P₀ R P₂)` the `ε`-system — the fast rows multiplied by
`ε⁻¹` — has the ball of radius `r` about `Φ s₀` in its region of attraction, and every solution
segment starting in that ball satisfies `|φ(t) − Φ s₀| ≤ C e^{−a(t − t₀)} |φ(t₀) − Φ s₀|`. The
radius, the overshoot `C` and the rate `a` do not depend on `ε`. -/
@[tmio T, powerlib_foundation] theorem uniform_basin_of_lt_basinEpsStar
    (e : Fin N ≃ F ⊕ S) {f : Dynamics.State N → Dynamics.State N} (hf : ContDiff ℝ 1 f)
    {Φ : EuclideanSpace ℝ S → Dynamics.State N} (hΦ : ContDiff ℝ 1 Φ)
    {s₀ : EuclideanSpace ℝ S} (heq : f (Φ s₀) = 0)
    (hslow : ∀ s k, Φ s (e.symm (.inr k)) = s k) (hfast : ∀ s i, f (Φ s) (e.symm (.inl i)) = 0)
    {A : Matrix F F ℝ} {R : Matrix S S ℝ}
    (hA : ∀ i j, HasDerivAt
      (fun t : ℝ => f (Φ s₀ + t • EuclideanSpace.single (e.symm (.inl j)) 1) (e.symm (.inl i)))
      (A i j) 0)
    (hR : HasFDerivAt (fun s => (WithLp.toLp 2 fun k => f (Φ s) (e.symm (.inr k)) :
      EuclideanSpace ℝ S)) (Matrix.toEuclideanCLM (𝕜 := ℝ) R) s₀)
    {P0 : Matrix S S ℝ} {P2 : Matrix F F ℝ} (hP0 : P0.PosDef) (hP2 : P2.PosDef)
    (hL0 : P0 * R + Rᵀ * P0 = -1) (hL2 : P2 * A + Aᵀ * P2 = -1) :
    ∃ r > 0, ∃ C ≥ 1, ∃ a > 0, ∀ ε, 0 < ε → ε < basinEpsStar f Φ s₀ P0 R P2 →
      ball (Φ s₀) r ⊆ Flow.regionOfAttraction (splitScaledField e ε f) (Φ s₀) ∧
      ∀ (t₀ t₁ : ℝ) (φ : ℝ → Dynamics.State N), IsTrajectoryOn φ (splitScaledField e ε f) t₀ t₁ →
        ‖φ t₀ - Φ s₀‖ < r → ∀ t ∈ Icc t₀ t₁,
          ‖φ t - Φ s₀‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - Φ s₀‖ := by
  classical
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hslΦ : ∀ s, slowPart e (Φ s) = s := fun s => by ext k; simp [hslow]
  have hfsfΦ : ∀ s, fastPart e (f (Φ s)) = 0 := fun s => by ext i; simp [hfast]
  have hfs1 : ‖fastPart e‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    simpa using norm_fastPart_le e w
  have hιf1 : ‖fastEmbed e‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simp [norm_fastEmbed]
  have hP0s : P0ᵀ = P0 := hP0.isHermitian.isSymm
  have hP2s : P2ᵀ = P2 := hP2.isHermitian.isSymm
  obtain ⟨l0, hl0, hlb0⟩ := exists_lower_bound_of_posDef hP0
  obtain ⟨l2, hl2, hlb2⟩ := exists_lower_bound_of_posDef hP2
  set Q0 := Matrix.toEuclideanCLM (𝕜 := ℝ) P0 with hQ0
  set Q2 := Matrix.toEuclideanCLM (𝕜 := ℝ) P2 with hQ2
  set R' := Matrix.toEuclideanCLM (𝕜 := ℝ) R with hR'
  set A' := Matrix.toEuclideanCLM (𝕜 := ℝ) A with hA'
  -- the fast block as an operator
  have hA'eq : (fastPart e).comp ((fderiv ℝ f (Φ s₀)).comp (fastEmbed e)) = A' := by
    set J := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).symm (fderiv ℝ f (Φ s₀)) with hJdef
    have hJ' : fderiv ℝ f (Φ s₀) = Matrix.toEuclideanCLM (𝕜 := ℝ) J := by simp [J]
    have hJ : HasFDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (Φ s₀) := by
      rw [← hJ']; exact (hfd _).hasFDerivAt
    obtain ⟨hA11, -⟩ := LinearAlgebra.exists_blocks_of_graph e hJ (hΦd s₀) hslow hfast hA hR
    have hAij : ∀ i j, J (e.symm (.inl i)) (e.symm (.inl j)) = A i j := fun i j => by
      rw [← hA11]; rfl
    refine ContinuousLinearMap.ext fun v => ?_
    ext i
    simp only [ContinuousLinearMap.comp_apply, fastPart_apply, hJ', hA',
      Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, fastEmbed_apply]
    rw [← e.symm.sum_comp, Fintype.sum_sum_type]
    simp [hAij]
  -- the composite Lyapunov function and its neighbourhood, independent of `ε`
  set V := compositeLyapunov e Φ s₀ P0 P2 with hV
  have hVc : ContDiff ℝ 1 V := contDiff_compositeLyapunov e hΦ s₀ P0 P2
  have hV0 : V (Φ s₀) = 0 := by simp [hV, compositeLyapunov, hslΦ]
  have hVlb : ∀ w, l0 * ‖slowPart e w - s₀‖ ^ 2 +
      l2 * ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ ^ 2 ≤ V w := fun w =>
    add_le_add (hlb0 _) (hlb2 _)
  set hi := ‖Q0‖ + ‖Q2‖ + 1 with hhi
  have hhi0 : 0 < hi := by positivity
  have hVub : ∀ w, V w ≤ hi * (‖slowPart e w - s₀‖ ^ 2 +
      ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ ^ 2) := fun w => by
    have h0 := inner_le_opNorm Q0 (slowPart e w - s₀) (slowPart e w - s₀)
    have h2 := inner_le_opNorm Q2 (fastPart e w - fastPart e (Φ (slowPart e w)))
      (fastPart e w - fastPart e (Φ (slowPart e w)))
    have hn0 : ‖Q0‖ ≤ hi := by linarith [norm_nonneg Q2]
    have hn2 : ‖Q2‖ ≤ hi := by linarith [norm_nonneg Q0]
    have e0 := mul_le_mul_of_nonneg_right hn0 (sq_nonneg ‖slowPart e w - s₀‖)
    have e2 := mul_le_mul_of_nonneg_right hn2
      (sq_nonneg ‖fastPart e w - fastPart e (Φ (slowPart e w))‖)
    show ⟪_, Q0 _⟫ + ⟪_, Q2 _⟫ ≤ _
    nlinarith
  set κ := 1 / (4 * (‖Q0‖ + ‖Q2‖ + 1)) with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ :=
    Metric.continuous_iff.mp (hf.continuous_fderiv one_ne_zero) (Φ s₀) κ hκ
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ :=
    Metric.continuous_iff.mp (hΦ.continuous_fderiv one_ne_zero) s₀ 1 one_pos
  obtain ⟨ρ₃, hρ₃, hρ₃'⟩ := Metric.continuous_iff.mp hΦ.continuous s₀ ρ₁ hρ₁
  obtain ⟨ρ₄, hρ₄, hρ₄'⟩ := Metric.eventually_nhds_iff.mp (hR.isLittleO.def hκ)
  set ρ := min ρ₁ (min ρ₂ (min ρ₃ ρ₄)) with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ (lt_min hρ₂ (lt_min hρ₃ hρ₄))
  have hρ1 : ρ ≤ ρ₁ := min_le_left _ _
  have hρ2 : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ ρ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ4 : ρ ≤ ρ₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set Lf := ‖fderiv ℝ f (Φ s₀)‖ + κ with hLf
  set KΦ := ‖fderiv ℝ Φ s₀‖ + 1 with hKΦ
  have hLf0 : 0 ≤ Lf := by positivity
  have hKΦ0 : 0 ≤ KΦ := by positivity
  have hD : ∀ u ∈ ball (Φ s₀) ρ₁, ‖fderiv ℝ f u - fderiv ℝ f (Φ s₀)‖ ≤ κ := fun u hu => by
    have h := (hρ₁' u (mem_ball.mp hu)).le
    rwa [dist_eq_norm] at h
  have hDf : ∀ u ∈ ball (Φ s₀) ρ₁, ‖fderiv ℝ f u‖ ≤ Lf := fun u hu =>
    calc ‖fderiv ℝ f u‖ = ‖fderiv ℝ f (Φ s₀) + (fderiv ℝ f u - fderiv ℝ f (Φ s₀))‖ := by
          rw [add_sub_cancel]
      _ ≤ Lf := (norm_add_le _ _).trans (by linarith [hD u hu])
  have hDΦ : ∀ s ∈ ball s₀ ρ₂, ‖fderiv ℝ Φ s‖ ≤ KΦ := fun s hs => by
    have h := (hρ₂' s (mem_ball.mp hs)).le
    rw [dist_eq_norm] at h
    calc ‖fderiv ℝ Φ s‖ = ‖fderiv ℝ Φ s₀ + (fderiv ℝ Φ s - fderiv ℝ Φ s₀)‖ := by
          rw [add_sub_cancel]
      _ ≤ KΦ := (norm_add_le _ _).trans (by linarith)
  have hMVf : ∀ x ∈ ball (Φ s₀) ρ₁, ∀ y ∈ ball (Φ s₀) ρ₁, ‖f y - f x‖ ≤ Lf * ‖y - x‖ :=
    fun x hx y hy => (convex_ball (Φ s₀) ρ₁).norm_image_sub_le_of_norm_fderiv_le
      (fun u _ => hfd u) hDf hx hy
  have hMVΦ : ∀ x ∈ ball s₀ ρ₂, ∀ y ∈ ball s₀ ρ₂, ‖Φ y - Φ x‖ ≤ KΦ * ‖y - x‖ :=
    fun x hx y hy => (convex_ball s₀ ρ₂).norm_image_sub_le_of_norm_fderiv_le
      (fun u _ => hΦd u) hDΦ hx hy
  -- geometry of the ball `W = ball (Φ s₀) ρ`
  have hξle : ∀ w, ‖slowPart e w - s₀‖ ≤ ‖w - Φ s₀‖ := fun w => by
    have h : slowPart e w - s₀ = slowPart e (w - Φ s₀) := by rw [map_sub, hslΦ]
    rw [h]; exact norm_slowPart_le e _
  have hsball : ∀ w ∈ ball (Φ s₀) ρ, slowPart e w ∈ ball s₀ ρ := fun w hw => by
    rw [mem_ball, dist_eq_norm]
    exact (hξle w).trans_lt (by rw [← dist_eq_norm]; exact mem_ball.mp hw)
  have hdec : ∀ w, w = Φ (slowPart e w) +
      fastEmbed e (fastPart e w - fastPart e (Φ (slowPart e w))) := fun w =>
    eq_add_fastEmbed e (by rw [hslΦ])
  have hnormη : ∀ w, ‖w - Φ (slowPart e w)‖ =
      ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ := fun w => by
    rw [sub_eq_iff_eq_add'.mpr (hdec w), norm_fastEmbed]
  have hΦball : ∀ w ∈ ball (Φ s₀) ρ, Φ (slowPart e w) ∈ ball (Φ s₀) ρ₁ := fun w hw =>
    mem_ball.mpr (hρ₃' _ ((mem_ball.mp (hsball w hw)).trans_le hρ3))
  have hwball : ∀ w ∈ ball (Φ s₀) ρ, w ∈ ball (Φ s₀) ρ₁ := fun w hw => ball_subset_ball hρ1 hw
  have hΦs : ∀ w ∈ ball (Φ s₀) ρ, ‖Φ (slowPart e w) - Φ s₀‖ ≤ KΦ * ‖slowPart e w - s₀‖ :=
    fun w hw => hMVΦ _ (mem_ball_self hρ₂) _ (ball_subset_ball hρ2 (hsball w hw))
  -- the norm comparisons on `W`
  have hup : ∀ w ∈ ball (Φ s₀) ρ, ‖w - Φ s₀‖ ≤
      ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ + KΦ * ‖slowPart e w - s₀‖ :=
    fun w hw => by
      have h : w - Φ s₀ = (w - Φ (slowPart e w)) + (Φ (slowPart e w) - Φ s₀) := by abel
      rw [h]
      exact (norm_add_le _ _).trans (add_le_add (hnormη w).le (hΦs w hw))
  have hηle : ∀ w ∈ ball (Φ s₀) ρ,
      ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ ≤ (1 + KΦ) * ‖w - Φ s₀‖ := fun w hw => by
    have h1 : fastPart e w - fastPart e (Φ (slowPart e w)) =
        fastPart e (w - Φ s₀) + fastPart e (Φ s₀ - Φ (slowPart e w)) := by
      rw [map_sub, map_sub]; abel
    rw [h1]
    calc _ ≤ ‖w - Φ s₀‖ + ‖Φ (slowPart e w) - Φ s₀‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_fastPart_le e _)
            ((norm_fastPart_le e _).trans (by rw [norm_sub_rev])))
      _ ≤ ‖w - Φ s₀‖ + KΦ * ‖w - Φ s₀‖ :=
          add_le_add le_rfl ((hΦs w hw).trans (mul_le_mul_of_nonneg_left (hξle w) hKΦ0))
      _ = (1 + KΦ) * ‖w - Φ s₀‖ := by ring
  -- the explicit `ε*`
  set c₀ := 2 * ((2 * ‖Q0‖ * Lf + 2 * ‖Q2‖ * KΦ * (‖R'‖ + 1)) ^ 2 + 2 * ‖Q2‖ * KΦ * Lf + 1)
    with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hεstar : basinEpsStar f Φ s₀ P0 R P2 = c₀⁻¹ := rfl
  -- the Lie derivative along the `ε`-system on `W`
  have hlie : ∀ ε, 0 < ε → ε < c₀⁻¹ → ∀ w ∈ ball (Φ s₀) ρ,
      fderiv ℝ V w (splitScaledField e ε f w) ≤
        -‖slowPart e w - s₀‖ ^ 2 / 4 - ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ ^ 2 := by
    intro ε hε hεs w hw
    have hεi : c₀ < ε⁻¹ := (lt_inv_comm₀ hc₀pos hε).mpr hεs
    rw [hV, fderiv_compositeLyapunov e hΦd s₀ hP0s hP2s, slowPart_splitScaledField,
      fastPart_splitScaledField]
    refine lie_le (inner_lyapunov hP0s hL0) (inner_lyapunov hP2s hL2) hKΦ0 hLf0 ?_ ?_ ?_ hεi
    · -- slow rows
      have hred := hρ₄' ((mem_ball.mp (hsball w hw)).trans_le hρ4)
      have hg0 : (WithLp.toLp 2 fun k => f (Φ s₀) (e.symm (.inr k)) :
          EuclideanSpace ℝ S) = 0 := by
        ext k; simp [heq]
      have hgs : (WithLp.toLp 2 fun k => f (Φ (slowPart e w)) (e.symm (.inr k)) :
          EuclideanSpace ℝ S) = slowPart e (f (Φ (slowPart e w))) := rfl
      rw [hg0, sub_zero, hgs] at hred
      have hmv := hMVf _ (hΦball w hw) _ (hwball w hw)
      rw [hnormη] at hmv
      calc ‖slowPart e (f w) - R' (slowPart e w - s₀)‖
          = ‖(slowPart e (f (Φ (slowPart e w))) - R' (slowPart e w - s₀)) +
              slowPart e (f w - f (Φ (slowPart e w)))‖ := by
            rw [ContinuousLinearMap.map_sub (slowPart e)]; congr 1; abel
        _ ≤ κ * ‖slowPart e w - s₀‖ + ‖f w - f (Φ (slowPart e w))‖ :=
            (norm_add_le _ _).trans (add_le_add hred (norm_slowPart_le e _))
        _ ≤ κ * ‖slowPart e w - s₀‖ + Lf * ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ := by
            linarith
    · -- fast rows
      have h := norm_fast_sub_le hfd (fastPart e) (fastEmbed e) hfs1 hιf1 hD (hΦball w hw)
        (by rw [← hdec w]; exact hwball w hw) (hfsfΦ _)
      rwa [← hdec w, hA'eq] at h
    · -- graph correction
      calc ‖fastPart e (fderiv ℝ Φ (slowPart e w) (slowPart e (f w)))‖
          ≤ ‖fderiv ℝ Φ (slowPart e w) (slowPart e (f w))‖ := norm_fastPart_le e _
        _ ≤ ‖fderiv ℝ Φ (slowPart e w)‖ * ‖slowPart e (f w)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ KΦ * ‖slowPart e (f w)‖ := mul_le_mul_of_nonneg_right
            (hDΦ _ (ball_subset_ball hρ2 (hsball w hw))) (norm_nonneg _)
  -- the sublevel set: compact, inside `W`
  set m := ρ / (2 * (1 + KΦ)) with hm
  have hm0 : 0 < m := by positivity
  set c := min l0 l2 * m ^ 2 with hcdef
  have hc : 0 < c := by positivity
  have hclose : ∀ w ∈ ball (Φ s₀) ρ, V w ≤ c → ‖w - Φ s₀‖ ≤ ρ / 2 := by
    intro w hw hVw
    obtain ⟨hX, hY⟩ := le_of_weighted_sq_le hl0 hl2 hm0.le (norm_nonneg _) (norm_nonneg _)
      ((hVlb w).trans hVw)
    calc ‖w - Φ s₀‖ ≤ ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ +
          KΦ * ‖slowPart e w - s₀‖ := hup w hw
      _ ≤ m + KΦ * m := add_le_add hY (mul_le_mul_of_nonneg_left hX hKΦ0)
      _ = ρ / 2 := by rw [hm]; field_simp
  have hΩeq : {w ∈ ball (Φ s₀) ρ | V w ≤ c} = closedBall (Φ s₀) (ρ / 2) ∩ {w | V w ≤ c} := by
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_eq_norm]
    constructor
    · rintro ⟨hw, hVw⟩; exact ⟨hclose w hw hVw, hVw⟩
    · rintro ⟨hw, hVw⟩
      exact ⟨mem_ball.mpr (by rw [dist_eq_norm]; linarith), hVw⟩
  have hΩc : IsCompact {w ∈ ball (Φ s₀) ρ | V w ≤ c} := by
    rw [hΩeq]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le hVc.continuous continuous_const)
  -- a ball inside the sublevel set; the constants of the decay
  obtain ⟨r₀, hr₀, hr₀'⟩ := Metric.continuous_iff.mp hVc.continuous (Φ s₀) c hc
  set D := 2 * (1 + KΦ) ^ 2 * (hi * (1 + (1 + KΦ) ^ 2)) / min l0 l2 with hDdef
  have hD0 : 0 ≤ D := by have := lt_min hl0 hl2; positivity
  set C := max 1 (Real.sqrt D) with hCdef
  set a := 1 / (8 * hi) with hadef
  refine ⟨min r₀ ρ, lt_min hr₀ hρ, C, le_max_left _ _, a, by positivity,
    fun ε hε hεs => ?_⟩
  rw [hεstar] at hεs
  have hball : ball (Φ s₀) (min r₀ ρ) ⊆ {w ∈ ball (Φ s₀) ρ | V w ≤ c} := fun w hw => by
    refine ⟨ball_subset_ball (min_le_right _ _) hw, ?_⟩
    have h := hr₀' w (lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _))
    rw [hV0, Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans h.le
  have hLie : ∀ x ∈ ball (Φ s₀) ρ, fderiv ℝ V x (splitScaledField e ε f x) ≤ 0 :=
    fun x hx => (hlie ε hε hεs x hx).trans (neg_quarter_sub_nonpos _ _)
  have hFc : ContDiff ℝ 1 (splitScaledField e ε f) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (splitScale e ε)).contDiff.comp hf
  refine ⟨fun w hw => ?_, fun t₀ t₁ φ hφ hφ0 t ht => ?_⟩
  · -- the region of attraction
    refine Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel isOpen_ball hFc hVc hLie hΩc
      ?_ (hball hw)
    intro Nset hN _ x hx
    obtain ⟨⟨hxW, -⟩, hx0⟩ := hN hx
    have h := hlie ε hε hεs x hxW
    change fderiv ℝ V x (splitScaledField e ε f x) = 0 at hx0
    rw [hx0] at h
    obtain ⟨hX, hY⟩ := eq_zero_of_neg_quarter h
    have hsx : slowPart e x = s₀ := sub_eq_zero.mp (norm_eq_zero.mp hX)
    have hx' := hdec x
    rw [norm_eq_zero.mp hY, map_zero, add_zero, hsx] at hx'
    exact hx'
  · -- the uniform exponential decay
    have hinv := Dynamics.LaSalle.isPositivelyInvariant_sublevel_of_isOpen isOpen_ball
      (hVc.differentiable (by norm_num)) hLie hΩc.isClosed
    have hstay : ∀ s ∈ Icc t₀ t₁, φ s ∈ {w ∈ ball (Φ s₀) ρ | V w ≤ c} :=
      hinv t₀ t₁ φ hφ (hball (mem_ball.mpr (by rw [dist_eq_norm]; exact hφ0)))
    have hdiss : ∀ w ∈ ball (Φ s₀) ρ,
        fderiv ℝ V w (splitScaledField e ε f w) ≤ -(1 / (4 * hi)) * V w := fun w hw => by
      have h1 := hlie ε hε hεs w hw
      have h2 := hVub w
      have hB := sq_nonneg ‖fastPart e w - fastPart e (Φ (slowPart e w))‖
      generalize ‖slowPart e w - s₀‖ ^ 2 = A at h1 h2
      generalize ‖fastPart e w - fastPart e (Φ (slowPart e w))‖ ^ 2 = B at h1 h2 hB
      generalize fderiv ℝ V w (splitScaledField e ε f w) = d at h1 ⊢
      generalize V w = v at h2 ⊢
      have h3 : 1 / (4 * hi) * v ≤ (A + B) / 4 :=
        calc 1 / (4 * hi) * v ≤ 1 / (4 * hi) * (hi * (A + B)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (A + B) / 4 := by field_simp
      linarith
    have henergy := Dynamics.le_exp_mul_of_hasDerivWithinAt (g := fun s => V (φ s))
      (g' := fun s => fderiv ℝ V (φ s) (splitScaledField e ε f (φ s))) (ρ := 1 / (4 * hi))
      (fun s hs => ((hVc.differentiable (by norm_num)) (φ s)).hasFDerivAt.comp_hasDerivWithinAt s
        (hφ s hs)) (fun s hs => hdiss _ (hstay s hs).1) t ht
    -- state estimates at `t` and at `t₀`
    have hwt := (hstay t ht).1
    have hw0 := (hstay t₀ ⟨le_rfl, ht.1.trans ht.2⟩).1
    have hlow := sq_le_of_split (norm_nonneg _) (norm_nonneg _) hKΦ0 hl0 hl2 (norm_nonneg _)
      (hup _ hwt) (hVlb (φ t))
    have hhigh := le_mul_sq_of_split (norm_nonneg _) (norm_nonneg _) hhi0.le (hξle (φ t₀))
      (hηle _ hw0) (hVub (φ t₀))
    have hsq : ‖φ t - Φ s₀‖ ^ 2 ≤ D * Real.exp (-(1 / (4 * hi)) * (t - t₀)) *
        ‖φ t₀ - Φ s₀‖ ^ 2 :=
      sq_le_of_energy (lt_min hl0 hl2) (Real.exp_pos _).le hlow henergy hhigh
    have hC2 : D ≤ C ^ 2 := by
      calc D = Real.sqrt D ^ 2 := (Real.sq_sqrt hD0).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
    have hexp2 : Real.exp (-a * (t - t₀)) ^ 2 = Real.exp (-(1 / (4 * hi)) * (t - t₀)) := by
      rw [← Real.exp_nat_mul]; congr 1; rw [hadef]; field_simp; ring
    have hC0 : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    calc ‖φ t - Φ s₀‖ ^ 2 ≤ D * Real.exp (-(1 / (4 * hi)) * (t - t₀)) * ‖φ t₀ - Φ s₀‖ ^ 2 := hsq
      _ ≤ C ^ 2 * Real.exp (-(1 / (4 * hi)) * (t - t₀)) * ‖φ t₀ - Φ s₀‖ ^ 2 := by
          gcongr
      _ = (C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - Φ s₀‖) ^ 2 := by rw [mul_pow, mul_pow, hexp2]

/-- **Region of attraction and exponential decay uniform in `ε` (Tikhonov).** With the data of
`uniform_basin_of_lt_basinEpsStar` and a spectrally stable fast block `A` and reduced Jacobian `R`
(Lyapunov matrices by `exists_posDef_lyapunov_of_spectrallyStable`): there are `ε* > 0`, `r > 0`,
`C ≥ 1` and `a > 0` such that for every `ε ∈ (0, ε*)` the ball of radius `r` about `Φ s₀` lies
in the region of attraction of the `ε`-system and every solution segment from it decays as
`C e^{−a(t − t₀)}`; `r`, `C`, `a` do not depend on `ε`. -/
@[tmio T, powerlib_foundation] theorem exists_epsStar_uniform_basin_of_graph
    (e : Fin N ≃ F ⊕ S) {f : Dynamics.State N → Dynamics.State N} (hf : ContDiff ℝ 1 f)
    {Φ : EuclideanSpace ℝ S → Dynamics.State N} (hΦ : ContDiff ℝ 1 Φ)
    {s₀ : EuclideanSpace ℝ S} (heq : f (Φ s₀) = 0)
    (hslow : ∀ s k, Φ s (e.symm (.inr k)) = s k) (hfast : ∀ s i, f (Φ s) (e.symm (.inl i)) = 0)
    {A : Matrix F F ℝ} {R : Matrix S S ℝ}
    (hA : ∀ i j, HasDerivAt
      (fun t : ℝ => f (Φ s₀ + t • EuclideanSpace.single (e.symm (.inl j)) 1) (e.symm (.inl i)))
      (A i j) 0)
    (hR : HasFDerivAt (fun s => (WithLp.toLp 2 fun k => f (Φ s) (e.symm (.inr k)) :
      EuclideanSpace ℝ S)) (Matrix.toEuclideanCLM (𝕜 := ℝ) R) s₀)
    (hAs : Linear.SpectrallyStable A) (hRs : Linear.SpectrallyStable R) :
    ∃ εs > 0, ∃ r > 0, ∃ C ≥ 1, ∃ a > 0, ∀ ε, 0 < ε → ε < εs →
      ball (Φ s₀) r ⊆ Flow.regionOfAttraction (splitScaledField e ε f) (Φ s₀) ∧
      ∀ (t₀ t₁ : ℝ) (φ : ℝ → Dynamics.State N), IsTrajectoryOn φ (splitScaledField e ε f) t₀ t₁ →
        ‖φ t₀ - Φ s₀‖ < r → ∀ t ∈ Icc t₀ t₁,
          ‖φ t - Φ s₀‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - Φ s₀‖ := by
  obtain ⟨P0, hP0, hL0⟩ := exists_posDef_lyapunov_of_spectrallyStable hRs
  obtain ⟨P2, hP2, hL2⟩ := exists_posDef_lyapunov_of_spectrallyStable hAs
  exact ⟨basinEpsStar f Φ s₀ P0 R P2, basinEpsStar_pos f Φ s₀ P0 R P2,
    uniform_basin_of_lt_basinEpsStar e hf hΦ heq hslow hfast hA hR hP0 hP2 hL0 hL2⟩

end powerlib.SingularPerturbation
