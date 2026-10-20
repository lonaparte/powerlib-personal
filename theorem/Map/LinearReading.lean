import theorem.Map.Linearization
import theorem.Family.Basic

/-! # Linear maps: the attractive sentences are Schur stability (foundation)

The discrete counterpart of the linear hub of the flow semantics (`Linear.holds_iff_isHurwitz`,
`Family.IsLinear.den_hurwitz`): for the linear map of a real square matrix `Φ`, every attractive
sentence and sampled contraction holds at the origin exactly when `Φ` is Schur stable, whatever
the step length. A Schur matrix gives a global geometric estimate, which gives every one of these
sentences; conversely each of them gives local asymptotic stability, which for a linear map makes
every orbit converge (scale the initial state into the basin), and convergence of every orbit is
Schur stability (`LTI.asymptoticallyStable_iff_schurStable`). Scaffold: the `discrete-reading`
hypothesis of `theorem/ExactSampling.agda` and `theorem/SwitchedAveraging.agda`.

Scope. Maps `F : ℝⁿ → ℝⁿ` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, read by the map semantics
`theorem/Map/Defs.lean`; the linear map of a matrix is `Map.op Φ`
(`theorem/Map/Linearization.lean`); Schur stability is `LTI.SchurStable`
(`theorem/LTI/Discrete.lean`); families of autonomous maps (`Family.IsAutonomousMap`). No model.

Source: the map semantics (`theorem/Map/Defs.lean`, `theorem/Map/Basic.lean`), the linearization
of maps (`theorem/Map/Linearization.lean`: `globallyExponentiallyStable_of_schurStable`,
`locallyExponentiallyStable_of_pow_norm_lt_one`) and the discrete converse
`LTI.asymptoticallyStable_iff_schurStable` (`theorem/LTI/Discrete.lean`); work-sync
`theory/T-numerical-integration.md` §2.7 (the recursion `x_{k+1} = R(hA) x_k` as the discrete
semantics).

Results.
* General maps: `Map.GloballyAsymptoticallyStable.localAsymptoticStable`;
  `Map.GloballyExponentiallyStable.holdsMap` (a global geometric estimate gives every attractive
  sentence and sampled contraction); `Flow.Property.localAsymptoticStable_of_holdsMap` (every
  attractive sentence of a map gives local asymptotic stability).
* Linear maps: `Map.tendsto_iterate_of_localAsymptoticStable` (local asymptotic stability of a
  continuous linear map at the origin makes every orbit converge);
  `Map.schurStable_of_localAsymptoticStable`, `Map.schurStable_of_sampledContraction`;
  `Map.holdsMap_op_iff_schurStable` (main): `P.holdsMap T (op Φ) 0 ↔ LTI.SchurStable Φ` for every
  attractive sentence and sampled contraction and every step length `T`.
* Families: `Family.IsAutonomousMap.den_schurStable`: in a family of linear maps the attractive
  sentences and sampled contraction denote the members with a Schur matrix (the discrete
  counterpart of `Family.IsLinear.den_hurwitz`).

Family and connection conclusions.
* None: generic laws of the map semantics and of families of linear maps; the families of
  `theorem/LTI/ExactSampling.lean` and `theorem/Averaging/SwitchedFamily.lean` use them in their
  connection statements.
-/

noncomputable section

namespace powerlib

open Filter Topology Matrix

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Map

/-! ## General maps -/

/-- Global asymptotic stability gives local asymptotic stability. -/
@[powerlib_foundation] theorem GloballyAsymptoticallyStable.localAsymptoticStable {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} (h : GloballyAsymptoticallyStable F x) : LocalAsymptoticStable F x :=
  ⟨h.2.1, 1, one_pos, fun y _ => h.2.2 y⟩

/-- A global geometric estimate gives every attractive sentence and sampled contraction, for every
step length. -/
@[powerlib_foundation] theorem GloballyExponentiallyStable.holdsMap {F : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : GloballyExponentiallyStable F x) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) (T : ℝ) : P.holdsMap T F x := by
  rcases hP with hP | rfl
  · cases P
    case locallyAsymptoticallyStable =>
      exact h.locallyExponentiallyStable.localAsymptoticStable
    case locallyExponentiallyStable => exact h.locallyExponentiallyStable
    case globallyAsymptoticallyStable => exact h.globallyAsymptoticallyStable
    case globallyExponentiallyStable => exact h
    all_goals exact hP.elim
  · exact h.sampledContraction

end Map

/-- Every attractive sentence of a map gives local asymptotic stability. -/
@[powerlib_foundation] theorem Flow.Property.localAsymptoticStable_of_holdsMap {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} {P : Flow.Property} (hP : P.Attractive) {T : ℝ} (h : P.holdsMap T F x) :
    Map.LocalAsymptoticStable F x := by
  cases P
  case locallyAsymptoticallyStable => exact h
  case locallyExponentiallyStable => exact Map.LocallyExponentiallyStable.localAsymptoticStable h
  case globallyAsymptoticallyStable =>
    exact Map.GloballyAsymptoticallyStable.localAsymptoticStable h
  case globallyExponentiallyStable =>
    exact Map.LocallyExponentiallyStable.localAsymptoticStable
      (Map.GloballyExponentiallyStable.locallyExponentiallyStable h)
  all_goals exact hP.elim

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
@[powerlib_foundation] theorem tendsto_iterate_of_localAsymptoticStable {L : ℝⁿ →L[ℝ] ℝⁿ}
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
@[powerlib_foundation] theorem IsAutonomousMap.den_schurStable {F : Family X Q n 0}
    {period : X → ℝ} {Φ : X → Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsAutonomousMap period fun x => Map.op (Φ x)) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) : F.den (.flow P) = {x | LTI.SchurStable (Φ x)} := by
  ext x
  rw [hF.mem_den_flow, Set.mem_ofPred_eq]
  exact Map.holdsMap_op_iff_schurStable hP _

end Family

end powerlib
