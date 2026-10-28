import theorem.Map.Linearization
import theorem.Family.Basic

/-! # Linear maps: the attractive sentences are Schur stability (foundation)

The discrete counterpart of the linear hub of the flow semantics (`Linear.holds_iff_isHurwitz`,
`Family.IsLinear.den_hurwitz`): for the linear map of a real square matrix `Φ`, every attractive
sentence and sampled contraction holds at the origin exactly when `Φ` is Schur stable, whatever
the step length. A Schur matrix gives a global geometric estimate, which gives every one of these
sentences (`Map.GloballyExponentiallyStable.holdsMap`, `theorem/Map/Basic.lean`); conversely each
of them gives local asymptotic stability, which for a linear map makes every orbit converge (scale
the initial state into the basin), and convergence of every orbit is Schur stability
(`LTI.asymptoticallyStable_iff_schurStable`). Lyapunov stability of a linear map bounds its
orbits (scale the initial state into the stability ball), so one eigenvalue outside the closed
unit disk gives instability: the discrete counterpart of `Linear.unstable_of_eigenvalue`.
Scaffold: the `discrete-reading` hypothesis of `theorem/ExactSampling.agda` and
`theorem/SwitchedAveraging.agda`.

Scope. Maps `F : ℝⁿ → ℝⁿ` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, read by the map semantics
`theorem/Map/Defs.lean`; the linear map of a matrix is `Map.op Φ`
(`theorem/Map/Linearization.lean`); Schur stability is `LTI.SchurStable`
(`theorem/LTI/Discrete.lean`); families of autonomous maps (`Family.IsAutonomousMap`). No model.

Source: the map semantics (`theorem/Map/Defs.lean`, `theorem/Map/Basic.lean`), the linearization
of maps (`theorem/Map/Linearization.lean`: `globallyExponentiallyStable_of_schurStable`,
`locallyExponentiallyStable_of_pow_norm_lt_one`), the discrete converse
`LTI.asymptoticallyStable_iff_schurStable` (`theorem/LTI/Discrete.lean`) and the real and
imaginary parts of a complex eigenpair (LeanForControl `matrixMulVec_re_smul_eigenpair`); work-sync
`theory/T-numerical-integration.md` §2.7 (the recursion `x_{k+1} = R(hA) x_k` as the discrete
semantics).

Results.
* Linear maps: `Map.tendsto_iterate_of_localAsymptoticStable` (local asymptotic stability of a
  continuous linear map at the origin makes every orbit converge);
  `Map.decay_zero_of_lyapunovStable` (Lyapunov stability of a continuous linear map at the origin
  bounds every orbit by a multiple of its initial norm: `Map.Decay` at the rate zero);
  `Map.unstable_op_of_eigenvalue`: a complex eigenvalue `μ` of `Φ` with `1 < ‖μ‖` gives
  `Map.Unstable (op Φ) 0`; `Map.schurStable_of_localAsymptoticStable`,
  `Map.schurStable_of_sampledContraction`; `Map.holdsMap_op_iff_schurStable` (main):
  `P.holdsMap T (op Φ) 0 ↔ LTI.SchurStable Φ` for every attractive sentence and sampled
  contraction and every step length `T`.
* Families: `Family.IsAutonomousMap.den_schurStable`: in a family of linear maps the attractive
  sentences and sampled contraction denote the members with a Schur matrix (the discrete
  counterpart of `Family.IsLinear.den_hurwitz`).

Family and connection conclusions.
* None: generic laws of families of linear maps; the families of
  `theorem/LTI/ExactSampling.lean` and `theorem/Averaging/SwitchedFamily.lean` use them in their
  connection statements.
-/

noncomputable section

namespace powerlib

open Filter Topology Matrix

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Map

/-! ## Linear maps -/

/-- The iterates of a continuous linear map commute with scalar multiplication. -/
private theorem iterate_smul (L : ℝⁿ →L[ℝ] ℝⁿ) (c : ℝ) (y : ℝⁿ) (k : ℕ) :
    (⇑L)^[k] (c • y) = c • (⇑L)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_smul]

/-- Local asymptotic stability of a continuous linear map at the origin makes every orbit converge
to the origin: a scaled copy of the initial state lies in the basin. -/
@[tmio T, powerlib_foundation] theorem tendsto_iterate_of_localAsymptoticStable {L : ℝⁿ →L[ℝ] ℝⁿ}
    (h : LocalAsymptoticStable L 0) (y : ℝⁿ) :
    Tendsto (fun k : ℕ => (⇑L)^[k] y) atTop (𝓝 0) := by
  obtain ⟨-, c, hc, hconv⟩ := h
  set s : ℝ := c / (‖y‖ + 1) with hs
  have hy1 : 0 < ‖y‖ + 1 := by positivity
  have hs0 : 0 < s := div_pos hc hy1
  have hsy : ‖s • y - 0‖ < c := by
    rw [sub_zero, norm_smul, Real.norm_of_nonneg hs0.le, hs, div_mul_eq_mul_div,
      div_lt_iff₀ hy1]
    nlinarith [norm_nonneg y]
  have ht := (hconv (s • y) hsy).const_smul s⁻¹
  rw [smul_zero] at ht
  refine ht.congr fun k => ?_
  rw [iterate_smul, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]

/-- Lyapunov stability of a continuous linear map at the origin bounds every orbit by a fixed
multiple of its initial norm (decay at the rate zero): a scaled copy of the initial state lies in
the ball that stays within distance one. -/
@[powerlib_foundation] theorem decay_zero_of_lyapunovStable {L : ℝⁿ →L[ℝ] ℝⁿ}
    (h : LyapunovStable L 0) : Decay L 0 0 := by
  obtain ⟨δ, hδ, hb⟩ := h 1 one_pos
  refine ⟨2 / δ, fun y k => ?_⟩
  rw [neg_zero, zero_mul, Real.exp_zero, mul_one, sub_zero, sub_zero]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [Function.iterate_fixed (map_zero L), norm_zero, mul_zero]
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set c : ℝ := δ / (2 * ‖y‖) with hc
  have hc0 : 0 < c := by positivity
  have hcy : ‖c • y - 0‖ < δ := by
    rw [sub_zero, norm_smul, Real.norm_of_nonneg hc0.le, hc]
    field_simp
    linarith
  have h1 := hb (c • y) hcy k
  rw [iterate_smul, sub_zero, norm_smul, Real.norm_of_nonneg hc0.le, hc, div_mul_eq_mul_div,
    div_lt_one (by positivity)] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  linarith

/-- **Instability from one eigenvalue.** The linear map of a real square matrix with a complex
eigenvalue outside the closed unit disk is unstable at the origin: the real and imaginary parts of
the eigenvector start orbits whose squared norms add up to `‖μ‖^{2k}` times their initial value,
which the bound of a Lyapunov stable linear map (`decay_zero_of_lyapunovStable`) forbids. -/
@[powerlib_foundation] theorem unstable_op_of_eigenvalue {Φ : Matrix (Fin n) (Fin n) ℝ} {μ : ℂ}
    {v : Fin n → ℂ} (hv : v ≠ 0) (heig : Φ.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ : 1 < ‖μ‖) : Unstable (op Φ) 0 := by
  intro hstab
  obtain ⟨C, hC⟩ := decay_zero_of_lyapunovStable hstab
  let re : ℕ → ℝⁿ := fun k => WithLp.toLp 2 fun j => (μ ^ k * v j).re
  let im : ℕ → ℝⁿ := fun k => WithLp.toLp 2 fun j => (μ ^ k * v j).im
  have hre : ∀ k, (⇑(op Φ))^[k] (re 0) = re k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      have h := MatrixAlgebra.matrixMulVec_re_smul_eigenpair Φ μ (μ ^ k) v heig
      simp only [re, toEuclideanCLM_toLp, ← h, pow_succ]
  have him : ∀ k, (⇑(op Φ))^[k] (im 0) = im k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      have h := MatrixAlgebra.matrixMulVec_im_smul_eigenpair Φ μ (μ ^ k) v heig
      simp only [im, toEuclideanCLM_toLp, ← h, pow_succ]
  set N : ℝ := ∑ j, Complex.normSq (v j) with hN
  have hsq : ∀ k, ‖re k‖ ^ 2 + ‖im k‖ ^ 2 = (‖μ‖ ^ 2) ^ k * N := by
    intro k
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib,
      hN, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [re, im]
    rw [← Complex.normSq_eq_norm_sq, ← map_pow, ← Complex.normSq_mul, Complex.normSq_apply]
    ring
  have hN0 : 0 < N := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
  have hbound : ∀ k, (‖μ‖ ^ 2) ^ k * N ≤ C ^ 2 * N := by
    intro k
    have h1 := hC (re 0) k
    have h2 := hC (im 0) k
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, sub_zero, hre, him] at h1 h2
    have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h0 := hsq 0
    rw [pow_zero, one_mul] at h0
    rw [← hsq k]
    nlinarith
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by nlinarith : 1 < ‖μ‖ ^ 2))
    |>.eventually_gt_atTop (C ^ 2)).exists
  linarith [hbound k, mul_lt_mul_of_pos_right hk hN0]

/-- Convergence of every orbit of the linear map of `Φ` is Schur stability of `Φ`. -/
private theorem schurStable_of_tendsto {Φ : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ y : ℝⁿ, Tendsto (fun k : ℕ => (⇑(op Φ))^[k] y) atTop (𝓝 0)) :
    LTI.SchurStable Φ := by
  refine (LTI.asymptoticallyStable_iff_schurStable ⟨Φ⟩).mp fun x hx => ?_
  have hxk : ∀ k, x k = WithLp.ofLp ((⇑(op Φ))^[k] (WithLp.toLp 2 (x 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hx k, Function.iterate_succ_apply', ofLp_toEuclideanCLM, ← ih]
      rfl
  have ht := ((PiLp.continuous_ofLp 2 _).tendsto 0).comp (h (WithLp.toLp 2 (x 0)))
  refine ht.congr' (Eventually.of_forall fun k => ?_) |>.trans_eq ?_
  · exact (hxk k).symm
  · rfl

/-- Local asymptotic stability of the linear map of `Φ` at the origin is Schur stability. -/
@[powerlib_foundation] theorem schurStable_of_localAsymptoticStable
    {Φ : Matrix (Fin n) (Fin n) ℝ} (h : LocalAsymptoticStable (op Φ) 0) : LTI.SchurStable Φ :=
  schurStable_of_tendsto (tendsto_iterate_of_localAsymptoticStable h)

/-- Sampled contraction of the linear map of `Φ` at the origin is Schur stability: the contracting
block is a power of operator norm below one. -/
@[powerlib_foundation] theorem schurStable_of_sampledContraction {Φ : Matrix (Fin n) (Fin n) ℝ}
    (h : SampledContraction (op Φ) 0) : LTI.SchurStable Φ := by
  obtain ⟨k, hk, c, hc, hb⟩ := h
  have hnorm : ‖op Φ ^ k‖ ≤ max c 0 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right c 0) fun y => ?_
    have := hb y
    rw [sub_zero, sub_zero, ← FunLike.coe_pow_eq_iterate] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg y))
  have hles := locallyExponentiallyStable_of_pow_norm_lt_one (op Φ).hasFDerivAt (map_zero _) hk
    (hnorm.trans_lt (max_lt hc one_pos))
  exact schurStable_of_localAsymptoticStable hles.localAsymptoticStable

/-- **The linear reading of the map semantics.** For the linear map of a real square matrix `Φ`,
every attractive sentence and sampled contraction holds at the origin, with any step length,
exactly when `Φ` is Schur stable. -/
@[powerlib_foundation] theorem holdsMap_op_iff_schurStable {Φ : Matrix (Fin n) (Fin n) ℝ}
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) (T : ℝ) :
    P.holdsMap T (op Φ) 0 ↔ LTI.SchurStable Φ := by
  refine ⟨fun h => ?_, fun h => (globallyExponentiallyStable_of_schurStable h).holdsMap hP T⟩
  rcases hP with hP | rfl
  · exact schurStable_of_localAsymptoticStable
      (Flow.Property.localAsymptoticStable_of_holdsMap hP h)
  · exact schurStable_of_sampledContraction h

end Map

/-! ## Families of linear maps -/

namespace Family

variable {X Q : Type*}

/-- In a family of linear maps, the attractive sentences and sampled contraction denote the
members with a Schur matrix, whatever their step lengths (the discrete counterpart of
`Family.IsLinear.den_hurwitz`). -/
@[tmio TM, powerlib_foundation] theorem IsAutonomousMap.den_schurStable {F : Family X Q n 0}
    {period : X → ℝ} {Φ : X → Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsAutonomousMap period fun x => Map.op (Φ x)) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (F.den (.flow P) = {x | LTI.SchurStable (Φ x)}) := by
  unfold powerlib.TMIO.Statement
  ext x
  rw [hF.mem_den_flow, Set.mem_ofPred_eq]
  exact Map.holdsMap_op_iff_schurStable hP _

end Family

end powerlib
