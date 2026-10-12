import theorem.Flow.Linearization
import theorem.Flow.Shift
import theorem.Dynamics.State
import theorem.Family.Basic
import theorem.TMIO.ClaimElab
import theorem.Network.WeightedLaplacian
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Networked swing equations: local exponential stability in relative angles

Source: work-sync `theory/T-synchronization-manifold.md` §1.7 (swing network
`Mᵢ θ̈ᵢ = P_{m,i} - ∑ⱼ Bᵢⱼ ViVj sin(θᵢ - θⱼ)`, with damping as in §2.2 and
`theory/T-small-signal-stability.md`).

Model boundary.
* `n + 1` machines, indices `Fin (n+1)`, machine `0` is the angle reference.
* Classical second-order swing model in the frame rotating at the synchronous
  frequency: `θ̇ₖ = ωₖ`, `Mₖ ω̇ₖ = Pₖ - Dₖ ωₖ - ∑ⱼ Bₖⱼ sin(θₖ - θⱼ)` with inertia
  `Mₖ > 0`, damping `Dₖ > 0`, constant net mechanical power `Pₖ`, and coupling
  `Bₖⱼ = Bⱼₖ ≥ 0` (`= VₖVⱼ/Xₖⱼ`, constant voltage magnitudes, lossless lines, Kron-reduced
  network). No governor, AVR, PLL, converter control, delay, or PWM. Continuous time.
* Reduced state, order `Fin (n + (n+1))`: first the relative angles
  `δᵢ = θ_{i+1} - θ₀` (`i : Fin n`), then the frequency deviations `ωₖ` (`k : Fin (n+1)`).
  The full model has a continuum of equilibria `θ* + c𝟙` (zero Jacobian eigenvalue);
  the relative-angle coordinates remove exactly this direction.
* Equilibrium: `θ*` with `Pₖ = ∑ⱼ Bₖⱼ sin(θ*ₖ - θ*ⱼ)` and `ω = 0`, all edge angle
  differences `|θ*ᵢ - θ*ⱼ| < π/2`, and the graph of `B` connected.

Result (equilibrium / linearization level, with a nonlinear conclusion): the reduced
nonlinear swing field is locally exponentially stable at the synchronous
equilibrium (`reducedSwing_locallyExponentiallyStable`). The proof derives the Jacobian
by `fderiv`, shows it is Hurwitz from the eigenvector identity
`μ²uᴴMu + μuᴴDu + uᴴLu = 0` with `L` the Laplacian of `Bᵢⱼ cos(θ*ᵢ - θ*ⱼ)`, and applies
`Flow.locallyExponentiallyStable_of_isHurwitz_jacobian`.

Family and connection conclusions.
* System map: a model (`Model n`: the swing data `Params n` and a selected angle profile `θ*`)
  is read as the autonomous reduced field translated so that the selected point
  `equilibrium θ* = (θ*_{i+1} − θ*_0, 0)` is the origin, `z ↦ f(z + x*)`; every flow sentence is
  invariant under this translation (`Flow.Property.holds_shift_iff`), so the sentences speak
  about `x*` itself. No ports.
* Requirements (static): `powerFlow` (`Pₖ = ∑ⱼ Bₖⱼ sin(θ*ₖ − θ*ⱼ)`), `angle` (every coupled
  edge has `|θ*ᵢ − θ*ⱼ| < π/2`), `connected` (the graph of `B` is connected),
  `jacobianUnstable` (the reduced Jacobian at `x*` has a characteristic root in the open right
  half plane). The local sentences translate into `{powerFlow, angle, connected}`, instability
  into `{powerFlow, jacobianUnstable}`, passivity into nothing; the global sentences, decay
  rates, sampled contraction and conservation, which a linearization cannot decide, into the
  whole (inconsistent) language.
* Connection theorems: `chain_le_semantics`, `exact_passive`,
  `mem_den_locallyExponentiallyStable` (the former `reducedSwing_locallyExponentiallyStable`) and
  `mem_den_unstable`.
* Static evidence (formerly `@[powerlib_domain]`): `fullField_equilibrium_shift`,
  `reducedField_reduce`, `reducedField_equilibrium`, and the new `jacobian_isHurwitz_of_angle`.
  Private implementation evidence (trajectory level, Rules §3a): `reduce_trajectory`.
-/

noncomputable section
namespace powerlib.Network.Swing
open Matrix Finset
open powerlib.Dynamics (State)

/-- Swing-network data for `n + 1` machines. -/
structure Params (n : ℕ) where
  M : Fin (n + 1) → ℝ
  D : Fin (n + 1) → ℝ
  P : Fin (n + 1) → ℝ
  B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
  M_pos : ∀ k, 0 < M k
  D_pos : ∀ k, 0 < D k
  B_symm : ∀ i j, B i j = B j i
  B_nonneg : ∀ i j, 0 ≤ B i j

variable {n : ℕ}

/-! ## Full model and its rotational symmetry -/

/-- Full swing field on `(θ, ω)`. -/
def fullField (p : Params n) (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) :=
  (x.2, fun k => (p.P k - p.D k * x.2 k - powerInjection p.B x.1 k) / p.M k)

@[powerlib_foundation] theorem powerInjection_add_const (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (θ : Fin (n + 1) → ℝ) (c : ℝ) :
    powerInjection B (fun k => θ k + c) = powerInjection B θ := by
  funext k
  simp [powerInjection]

/-- The full model has the equilibrium continuum `(θ* + c𝟙, 0)`: its linearization has a
zero eigenvalue along `𝟙`, so it cannot be exponentially stable in full coordinates. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem fullField_equilibrium_shift (p : Params n) (θ : Fin (n + 1) → ℝ)
    (heq : ∀ k, p.P k = powerInjection p.B θ k) (c : ℝ) :
    fullField p ((fun k => θ k + c), 0) = 0 := by
  simp only [fullField, powerInjection_add_const, ← heq]
  ext k <;> simp

/-! ## Reduced coordinates -/

/-- Position of the relative angle `δᵢ` in the reduced state. -/
abbrev dIdx (i : Fin n) : Fin (n + (n + 1)) := Fin.castAdd (n + 1) i

/-- Position of the frequency deviation `ωₖ` in the reduced state. -/
abbrev wIdx (k : Fin (n + 1)) : Fin (n + (n + 1)) := Fin.natAdd n k

/-- Absolute angles reconstructed from relative angles, with `θ₀ = 0`. -/
def angleMap : State (n + (n + 1)) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    Fin.cases (0 : State (n + (n + 1)) →L[ℝ] ℝ)
      (fun i => PiLp.proj 2 (fun _ => ℝ) (dIdx i)) k

@[simp, powerlib_foundation] theorem angleMap_zero (z : State (n + (n + 1))) :
    angleMap z 0 = 0 := by
  simp [angleMap]

@[simp, powerlib_foundation] theorem angleMap_succ (z : State (n + (n + 1))) (i : Fin n) :
    angleMap z i.succ = z (dIdx i) := by
  simp [angleMap]

/-- The reduced swing field on `(δ, ω)`. -/
def reducedField (p : Params n) (z : State (n + (n + 1))) : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun i => z (wIdx i.succ) - z (wIdx 0))
    (fun k => (p.P k - p.D k * z (wIdx k) - powerInjection p.B (angleMap z) k) / p.M k) r

@[simp, powerlib_foundation] theorem reducedField_dIdx (p : Params n) (z : State (n + (n + 1)))
    (i : Fin n) : reducedField p z (dIdx i) = z (wIdx i.succ) - z (wIdx 0) := by
  simp [reducedField]

@[simp, powerlib_foundation] theorem reducedField_wIdx (p : Params n) (z : State (n + (n + 1)))
    (k : Fin (n + 1)) : reducedField p z (wIdx k) =
      (p.P k - p.D k * z (wIdx k) - powerInjection p.B (angleMap z) k) / p.M k := by
  simp [reducedField]

/-- Reduction map `(θ, ω) ↦ (θ_{i+1} - θ₀, ω)`. -/
def reduce (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun i => x.1 i.succ - x.1 0) (fun k => x.2 k) r

@[simp, powerlib_foundation] theorem reduce_dIdx (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ))
    (i : Fin n) : reduce x (dIdx i) = x.1 i.succ - x.1 0 := by
  simp [reduce]

@[simp, powerlib_foundation] theorem reduce_wIdx (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ))
    (k : Fin (n + 1)) : reduce x (wIdx k) = x.2 k := by
  simp [reduce]

@[powerlib_foundation] theorem angleMap_reduce (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    angleMap (reduce x) = fun k => x.1 k + -x.1 0 := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [sub_eq_add_neg]

@[powerlib_foundation] theorem state_ext {z z' : State (n + (n + 1))}
    (hd : ∀ i, z (dIdx i) = z' (dIdx i)) (hw : ∀ k, z (wIdx k) = z' (wIdx k)) : z = z' := by
  ext r
  refine Fin.addCases (fun i => ?_) (fun k => ?_) r
  · exact hd i
  · exact hw k

/-- The reduction intertwines the full and the reduced field. Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem reducedField_reduce (p : Params n)
    (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    reducedField p (reduce x) = reduce (fullField p x) := by
  apply state_ext
  · intro i; simp [fullField]
  · intro k
    simp only [reducedField_wIdx, reduce_wIdx, fullField, angleMap_reduce,
      powerInjection_add_const]

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Every trajectory of the full swing model projects to a trajectory of the reduced field. -/
private theorem reduce_trajectory (p : Params n)
    {x : ℝ → (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)} {t : ℝ}
    (hx : HasDerivAt x (fullField p (x t)) t) :
    HasDerivAt (fun s => reduce (x s)) (reducedField p (reduce (x t))) t := by
  rw [reducedField_reduce]
  have hlin : ∃ R : ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) →L[ℝ] State (n + (n + 1)),
      ∀ y, R y = reduce y := by
    refine ⟨(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + (n + 1)) => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun r => Fin.addCases (motive := fun _ => _ →L[ℝ] ℝ)
        (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.succ).comp
            (ContinuousLinearMap.fst ℝ (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)) -
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0).comp
            (ContinuousLinearMap.fst ℝ (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)))
        (fun k => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k).comp
          (ContinuousLinearMap.snd ℝ (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ))) r), ?_⟩
    intro y
    apply state_ext
    · intro i; simp [reduce]
    · intro k; simp [reduce]
  obtain ⟨R, hR⟩ := hlin
  have h := R.hasFDerivAt.comp_hasDerivAt t hx
  simp only [Function.comp_def, hR] at h
  exact h

/-! ## Equilibrium and Jacobian -/

/-- The synchronous equilibrium in reduced coordinates. -/
def equilibrium (θ : Fin (n + 1) → ℝ) : State (n + (n + 1)) := reduce (θ, 0)

/-- The synchronous point is an equilibrium of the reduced field. Static evidence on the model,
not a connection conclusion. -/
@[powerlib_foundation] theorem reducedField_equilibrium (p : Params n) (θ : Fin (n + 1) → ℝ)
    (heq : ∀ k, p.P k = powerInjection p.B θ k) :
    reducedField p (equilibrium θ) = 0 := by
  rw [equilibrium, reducedField_reduce]
  have : fullField p (θ, 0) = 0 := by
    have := fullField_equilibrium_shift p θ heq 0
    simpa using this
  rw [this]
  apply state_ext <;> intro _ <;> simp

/-- Block form of the reduced Jacobian. -/
def jacobianBlocks (p : Params n) (θ : Fin (n + 1) → ℝ) :
    Matrix (Fin n ⊕ Fin (n + 1)) (Fin n ⊕ Fin (n + 1)) ℝ :=
  fromBlocks 0
    (Matrix.of fun i k => (if k = i.succ then 1 else 0) - (if k = 0 then 1 else 0))
    (Matrix.of fun k i => -(laplacian (flowWeights p.B θ) k i.succ) / p.M k)
    (Matrix.of fun k k' => if k = k' then -(p.D k / p.M k) else 0)

/-- The reduced Jacobian matrix in the state order `(δ, ω)`. -/
def jacobian (p : Params n) (θ : Fin (n + 1) → ℝ) : Matrix (Fin (n + (n + 1))) (Fin (n + (n + 1))) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (jacobianBlocks p θ)

@[simp, powerlib_foundation] theorem jacobian_dd (p : Params n) (θ : Fin (n + 1) → ℝ)
    (i i' : Fin n) : jacobian p θ (dIdx i) (dIdx i') = 0 := by
  simp [jacobian, jacobianBlocks]

@[simp, powerlib_foundation] theorem jacobian_dw (p : Params n) (θ : Fin (n + 1) → ℝ)
    (i : Fin n) (k : Fin (n + 1)) : jacobian p θ (dIdx i) (wIdx k) =
      (if k = i.succ then 1 else 0) - (if k = 0 then 1 else 0) := by
  simp [jacobian, jacobianBlocks]

@[simp, powerlib_foundation] theorem jacobian_wd (p : Params n) (θ : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) (i : Fin n) : jacobian p θ (wIdx k) (dIdx i) = -(laplacian (flowWeights p.B θ) k i.succ) / p.M k := by
  simp [jacobian, jacobianBlocks]

@[simp, powerlib_foundation] theorem jacobian_ww (p : Params n) (θ : Fin (n + 1) → ℝ)
    (k k' : Fin (n + 1)) : jacobian p θ (wIdx k) (wIdx k') =
      if k = k' then -(p.D k / p.M k) else 0 := by
  simp [jacobian, jacobianBlocks]

@[powerlib_foundation] theorem flowWeights_angleMap_equilibrium (p : Params n) (θ : Fin (n + 1) → ℝ) :
    flowWeights p.B (angleMap (equilibrium θ)) = flowWeights p.B θ := by
  ext i j
  simp [flowWeights, equilibrium, angleMap_reduce]

/-- Sum over the reduced state, split into the angle and frequency blocks. -/
@[powerlib_foundation] theorem sum_state {β : Type*} [AddCommMonoid β] (f : Fin (n + (n + 1)) → β) :
    ∑ r, f r = ∑ i : Fin n, f (dIdx i) + ∑ k : Fin (n + 1), f (wIdx k) :=
  Fin.sum_univ_add f

@[powerlib_foundation] theorem laplacian_angleMap (p : Params n) (θ : Fin (n + 1) → ℝ)
    (v : State (n + (n + 1))) (k : Fin (n + 1)) :
    (laplacian (flowWeights p.B θ) *ᵥ angleMap v) k =
      ∑ i : Fin n, laplacian (flowWeights p.B θ) k i.succ * v (dIdx i) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, angleMap_zero, mul_zero, zero_add,
    angleMap_succ]

/-- The Jacobian of the reduced field at the synchronous equilibrium. -/
@[powerlib_foundation] theorem hasFDerivAt_reducedField (p : Params n) (θ : Fin (n + 1) → ℝ) :
    HasFDerivAt (reducedField p)
      (Matrix.toEuclideanCLM (n := Fin (n + (n + 1))) (𝕜 := ℝ) (jacobian p θ)) (equilibrium θ) := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro r
  rw [hasFDerivWithinAt_univ]
  refine Fin.addCases (fun i => ?_) (fun k => ?_) r
  · have hd := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (equilibrium θ) (wIdx i.succ)).sub
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (equilibrium θ) (wIdx 0))
    have hfun : (fun z => reducedField p z (dIdx i)) = fun z => z (wIdx i.succ) - z (wIdx 0) := by
      funext z; exact reducedField_dIdx p z i
    rw [hfun]
    convert hd using 1
    ext v
    simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply, Matrix.ofLp_toEuclideanCLM,
      ContinuousLinearMap.sub_apply]
    rw [mulVec, dotProduct, sum_state]
    simp only [jacobian_dd, zero_mul, Finset.sum_const_zero, zero_add, jacobian_dw, sub_mul,
      ite_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hP := (hasFDerivAt_powerInjection p.B (angleMap (equilibrium θ))).comp (equilibrium θ)
      angleMap.hasFDerivAt
    have hPk := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (n + 1) => ℝ) k _).comp
      (equilibrium θ) hP
    have hd := (((hasFDerivAt_const (p.P k) (equilibrium θ)).sub
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (equilibrium θ) (wIdx k)).const_mul (p.D k))).sub
      hPk).const_mul (1 / p.M k)
    have hfun : (fun z => reducedField p z (wIdx k)) = fun z =>
        1 / p.M k * (p.P k - p.D k * z (wIdx k) - powerInjection p.B (angleMap z) k) := by
      funext z; rw [reducedField_wIdx]; ring
    rw [hfun]
    convert hd using 1
    · rfl
    ext v
    simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply, Matrix.ofLp_toEuclideanCLM]
    rw [mulVec, dotProduct, sum_state]
    simp only [jacobian_wd, jacobian_ww, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
      flowWeights_angleMap_equilibrium, laplacian_angleMap, PiLp.proj_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_sub', Pi.sub_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, zero_sub, ContinuousLinearMap.neg_apply]
    simp only [mul_sub, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro x _; ring

/-! ## The Jacobian is Hurwitz -/

@[powerlib_foundation] theorem re_neg_of_quadratic {μ : ℂ} {m d l : ℝ} (hm : 0 < m) (hd : 0 < d)
    (hl : 0 ≤ l) (h : (m : ℂ) * μ ^ 2 + d * μ + l = 0) (hμ : μ ≠ 0) : μ.re < 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im, zero_mul, sub_zero,
    add_zero, mul_zero] at hre him
  by_contra hnn
  push Not at hnn
  have him0 : μ.im = 0 := by
    have : μ.im * (2 * m * μ.re + d) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · nlinarith
  rw [him0] at hre
  have hre0 : μ.re = 0 := by nlinarith [mul_nonneg hm.le (mul_nonneg hnn hnn)]
  exact hμ (Complex.ext hre0 him0)

@[powerlib_foundation] theorem flowWeights_symm (p : Params n) (θ : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    flowWeights p.B θ i j = flowWeights p.B θ j i := by
  simp only [flowWeights, of_apply, p.B_symm i j]
  rw [← Real.cos_neg, neg_sub]

@[powerlib_foundation] theorem complex_laplacian_sum (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ζ : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    ∑ l, ((laplacian W k l : ℝ) : ℂ) * ζ l = ∑ l, (W k l : ℂ) * (ζ k - ζ l) := by
  simp only [laplacian_apply, Complex.ofReal_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

@[powerlib_foundation] theorem complex_laplacian_total {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hW : ∀ i j, W i j = W j i) (ζ : Fin (n + 1) → ℂ) :
    ∑ k, ∑ l, (W k l : ℂ) * (ζ k - ζ l) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hW]

/-- The reduced swing Jacobian is Hurwitz when the linearization weights are
nonnegative and their positive edges connect all machines. -/
@[powerlib_foundation] theorem jacobian_isHurwitz (p : Params n) (θ : Fin (n + 1) → ℝ)
    (hWnn : ∀ i j, 0 ≤ flowWeights p.B θ i j) (hconn : ∀ i j, Reach (flowWeights p.B θ) i j) :
    LinearSystems.IsHurwitz (jacobian p θ) := by
  intro μ v hv heig
  simp only [neg_zero]
  have hWs := flowWeights_symm p θ
  let η : Fin n → ℂ := fun i => v (dIdx i)
  let w : Fin (n + 1) → ℂ := fun k => v (wIdx k)
  let ζ : Fin (n + 1) → ℂ := Fin.cons 0 η
  have hrow : ∀ r, ∑ c, ((jacobian p θ r c : ℝ) : ℂ) * v c = μ * v r := by
    intro r
    have := congrFun heig r
    simpa [mulVec, dotProduct] using this
  have h1 : ∀ i, w i.succ - w 0 = μ * η i := by
    intro i
    have := hrow (dIdx i)
    rw [sum_state] at this
    simp only [jacobian_dd, jacobian_dw, Complex.ofReal_sub, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, zero_add, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one,
      sub_mul, ite_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    exact this
  have hζ0 : ζ 0 = 0 := rfl
  have hζs : ∀ i, ζ i.succ = η i := fun i => rfl
  have h2 : ∀ k, μ * p.M k * w k + p.D k * w k +
      ∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l) = 0 := by
    intro k
    have := hrow (wIdx k)
    rw [sum_state] at this
    simp only [jacobian_wd, jacobian_ww] at this
    have e1 : ∑ l, ((laplacian (flowWeights p.B θ) k l : ℝ) : ℂ) * ζ l =
        ∑ i : Fin n, ((laplacian (flowWeights p.B θ) k i.succ : ℝ) : ℂ) * η i := by
      rw [Fin.sum_univ_succ, hζ0, mul_zero, zero_add]
      rfl
    have hL : ∑ i : Fin n, ((-(laplacian (flowWeights p.B θ) k i.succ) / p.M k : ℝ) : ℂ) *
        v (dIdx i) = -(∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l)) / p.M k := by
      rw [← complex_laplacian_sum, e1, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [hL] at this
    have hD : ∑ k' : Fin (n + 1), (((if k = k' then -(p.D k / p.M k) else 0 : ℝ)) : ℂ) *
        v (wIdx k') = -(p.D k / p.M k) * w k := by
      rw [Finset.sum_eq_single k]
      · simp [w]
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    rw [hD] at this
    have hM : (p.M k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (p.M_pos k).ne'
    have h' : -(∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l)) / p.M k +
        -((p.D k : ℂ) / p.M k) * w k = μ * w k := by
      push_cast at this; exact this
    field_simp at h'
    linear_combination (-1 : ℂ) * h'
  have hv0 : ∀ (hη : η = 0) (hw : w = 0), False := by
    intro hη hw
    apply hv
    funext r
    refine Fin.addCases (fun i => ?_) (fun k => ?_) r
    · exact congrFun hη i
    · exact congrFun hw k
  by_cases hμ : μ = 0
  · exfalso
    subst hμ
    have hwconst : ∀ k, w k = w 0 := by
      intro k
      refine Fin.cases rfl (fun i => ?_) k
      have := h1 i
      rw [zero_mul, sub_eq_zero] at this
      exact this
    have e : ∀ k, ((p.D k : ℝ) : ℂ) * w 0 = -(∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l)) := by
      intro k
      have := h2 k
      rw [hwconst k] at this
      linear_combination this
    have hsum : ((∑ k, p.D k : ℝ) : ℂ) * w 0 = 0 := by
      push_cast
      rw [Finset.sum_mul, Finset.sum_congr rfl (fun k _ => e k), Finset.sum_neg_distrib,
        complex_laplacian_total hWs, neg_zero]
    have hDpos : (0 : ℝ) < ∑ k, p.D k := Finset.sum_pos (fun k _ => p.D_pos k) Finset.univ_nonempty
    have hw0 : w 0 = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hDpos.ne'
      · exact h
    have hlap : ∀ k, ∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l) = 0 := by
      intro k
      have := e k
      rw [hw0, mul_zero] at this
      linear_combination this
    have hζ := complex_eq_of_laplacian_eq_zero hWs hWnn hconn hlap
    exact hv0 (funext fun i => by rw [← hζs i, hζ i.succ 0, hζ0]; rfl)
      (funext fun k => by rw [hwconst k, hw0]; rfl)
  · let u : Fin (n + 1) → ℂ := fun k => w k / μ
    have hwk : ∀ k, w k = μ * u k := fun k => by simp only [u]; field_simp
    have hu : ∀ l, ζ l = u l - u 0 := by
      intro l
      refine Fin.cases (by simp [hζ0]) (fun i => ?_) l
      rw [hζs]
      have := h1 i
      rw [hwk, hwk] at this
      apply mul_left_cancel₀ hμ
      linear_combination -this
    have h3 : ∀ k, μ ^ 2 * p.M k * u k + μ * p.D k * u k +
        ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l) = 0 := by
      intro k
      have := h2 k
      simp only [hu, hwk k, sub_sub_sub_cancel_right] at this
      linear_combination this
    have hsum : ∑ k, star (u k) * (μ ^ 2 * p.M k * u k + μ * p.D k * u k +
        ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l)) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [h3 k, mul_zero]
    have hns : ∀ k, star (u k) * u k = (Complex.normSq (u k) : ℂ) := fun k => by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    have hexp : ∑ k, star (u k) * (μ ^ 2 * p.M k * u k + μ * p.D k * u k +
        ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l)) =
        ((∑ k, p.M k * Complex.normSq (u k) : ℝ) : ℂ) * μ ^ 2 +
          ((∑ k, p.D k * Complex.normSq (u k) : ℝ) : ℂ) * μ +
          ∑ k, star (u k) * ∑ l, (flowWeights p.B θ k l : ℂ) * (u k - u l) := by
      push_cast
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by rw [← hns]; ring
      · exact Finset.sum_congr rfl fun k _ => by rw [← hns]; ring
    rw [hexp, star_dotProduct_laplacian_mulVec hWs] at hsum
    have hune : ∃ k, u k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hv0
      · funext i
        have := h1 i
        rw [hwk, hwk, hall, hall] at this
        simp only [mul_zero, sub_zero] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hμ
      · funext k; rw [hwk, hall]; simp
    obtain ⟨k₀, hk₀⟩ := hune
    have hm : 0 < ∑ k, p.M k * Complex.normSq (u k) :=
      Finset.sum_pos' (fun k _ => mul_nonneg (p.M_pos k).le (Complex.normSq_nonneg _))
        ⟨k₀, Finset.mem_univ _, mul_pos (p.M_pos k₀) (Complex.normSq_pos.mpr hk₀)⟩
    have hd : 0 < ∑ k, p.D k * Complex.normSq (u k) :=
      Finset.sum_pos' (fun k _ => mul_nonneg (p.D_pos k).le (Complex.normSq_nonneg _))
        ⟨k₀, Finset.mem_univ _, mul_pos (p.D_pos k₀) (Complex.normSq_pos.mpr hk₀)⟩
    have hl : 0 ≤ (∑ i, ∑ j, flowWeights p.B θ i j * Complex.normSq (u i - u j)) / 2 :=
      div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hWnn i j) (Complex.normSq_nonneg _)) zero_le_two
    exact re_neg_of_quadratic hm hd hl hsum hμ

/-! ## Local exponential stability -/

@[powerlib_foundation] theorem reducedField_contDiff (p : Params n) : ContDiff ℝ 1 (reducedField p) := by
  rw [contDiff_euclidean]
  intro r
  refine Fin.addCases (fun i => ?_) (fun k => ?_) r
  · have : (fun z => reducedField p z (dIdx i)) = fun z => z (wIdx i.succ) - z (wIdx 0) := by
      funext z; exact reducedField_dIdx p z i
    rw [this]
    exact (contDiff_piLp_apply 2).sub (contDiff_piLp_apply 2)
  · have : (fun z => reducedField p z (wIdx k)) = fun z =>
        (p.P k - p.D k * z (wIdx k) - powerInjection p.B (angleMap z) k) / p.M k := by
      funext z; exact reducedField_wIdx p z k
    rw [this]
    apply ContDiff.div_const
    apply ContDiff.sub
    · exact contDiff_const.sub (contDiff_const.mul (contDiff_piLp_apply 2))
    · unfold powerInjection
      apply ContDiff.sum
      intro j _
      apply contDiff_const.mul
      apply Real.contDiff_sin.comp
      exact ((contDiff_apply ℝ ℝ k).comp angleMap.contDiff).sub
        ((contDiff_apply ℝ ℝ j).comp angleMap.contDiff)

/-- The angle condition on a connected coupling graph makes the reduced Jacobian Hurwitz. -/
@[powerlib_foundation] theorem jacobian_isHurwitz_of_angle (p : Params n) (θ : Fin (n + 1) → ℝ)
    (hangle : ∀ i j, 0 < p.B i j → |θ i - θ j| < Real.pi / 2)
    (hconn : ∀ i j, Reach p.B i j) : LinearSystems.IsHurwitz (jacobian p θ) := by
  have hpos : ∀ i j, 0 < p.B i j → 0 < flowWeights p.B θ i j := by
    intro i j hij
    have hc : 0 < Real.cos (θ i - θ j) := by
      have := abs_lt.mp (hangle i j hij)
      exact Real.cos_pos_of_mem_Ioo ⟨this.1, this.2⟩
    exact mul_pos hij hc
  have hWnn : ∀ i j, 0 ≤ flowWeights p.B θ i j := by
    intro i j
    rcases (p.B_nonneg i j).lt_or_eq with h | h
    · exact (hpos i j h).le
    · simp [flowWeights, ← h]
  have hconnW : ∀ i j, Reach (flowWeights p.B θ) i j := fun i j =>
    Relation.ReflTransGen.mono (fun a b h => hpos a b h) i j (hconn i j)
  exact jacobian_isHurwitz p θ hWnn hconnW

/-! ## The family -/

/-- A swing-network model read about a selected angle profile `θ*`. -/
structure Model (n : ℕ) where
  /-- The swing data. -/
  params : Params n
  /-- The selected angle profile `θ*`. -/
  θ : Fin (n + 1) → ℝ

/-- The reduced swing field translated so that the selected point is the origin. -/
def Model.field (m : Model n) (z : State (n + (n + 1))) : State (n + (n + 1)) :=
  reducedField m.params (z + equilibrium m.θ)

/-- Requirements on the swing-network models, all static. -/
inductive Requirement
  /-- Power balance at `θ*`: `Pₖ = ∑ⱼ Bₖⱼ sin(θ*ₖ − θ*ⱼ)`. -/
  | powerFlow
  /-- Every coupled edge has `|θ*ᵢ − θ*ⱼ| < π/2`. -/
  | angle
  /-- The graph of `B` is connected. -/
  | connected
  /-- The reduced Jacobian at `θ*` has a characteristic root in the open right half plane. -/
  | jacobianUnstable

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model n) : Requirement → Prop
  | .powerFlow => ∀ k, m.params.P k = powerInjection m.params.B m.θ k
  | .angle => ∀ i j, 0 < m.params.B i j → |m.θ i - m.θ j| < Real.pi / 2
  | .connected => ∀ i j, Reach m.params.B i j
  | .jacobianUnstable =>
    ∃ s : ℂ, (Linear.characteristicMatrix (jacobian m.params m.θ) s).det = 0 ∧ 0 < s.re

/-- The translation of the sentences: the local ones into power balance with the angle
condition on a connected graph, instability into power balance with an unstable Jacobian,
passivity into nothing. The global sentences, decay rates, sampled contraction and conservation
are translated into the whole language, which no model meets (unavailable translation coverage,
not a usable translation). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.powerFlow, .angle, .connected}
  | .flow .unstable => {.powerFlow, .jacobianUnstable}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The swing-network family: every model read as its autonomous field translated to the
selected point. -/
def family : Family (Model n) Requirement (n + (n + 1)) 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous :
    (family (n := n)).IsAutonomous Model.field := fun _ => rfl

/-- A flow sentence of a model is the sentence of the untranslated reduced field at the
selected point. -/
private theorem mem_den_flow_iff {m : Model n} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (reducedField m.params) (equilibrium m.θ) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- Implementation evidence: the former public `reducedSwing_locallyExponentiallyStable`, at the
selected point of the untranslated field. -/
private theorem reducedSwing_locallyExponentiallyStable (p : Params n)
    (θ : Fin (n + 1) → ℝ) (heq : ∀ k, p.P k = powerInjection p.B θ k)
    (hangle : ∀ i j, 0 < p.B i j → |θ i - θ j| < Real.pi / 2)
    (hconn : ∀ i j, Reach p.B i j) :
    LocallyExponentiallyStable (reducedField p) (equilibrium θ) :=
  Flow.locallyExponentiallyStable_of_isHurwitz_jacobian (jacobian p θ)
    (reducedField_contDiff p) (reducedField_equilibrium p θ heq)
    (hasFDerivAt_reducedField p θ).fderiv (jacobian_isHurwitz_of_angle p θ hangle hconn)

private theorem les_of_meets {m : Model n} (hp : Meets m .powerFlow) (ha : Meets m .angle)
    (hc : Meets m .connected) : m ∈ family.den (.flow .locallyExponentiallyStable) :=
  mem_den_flow_iff.mpr (reducedSwing_locallyExponentiallyStable m.params m.θ hp ha hc)

private theorem unstable_of_meets {m : Model n} (hp : Meets m .powerFlow)
    (hu : Meets m .jacobianUnstable) : m ∈ family.den (.flow .unstable) := by
  obtain ⟨s, hs, hre⟩ := hu
  exact mem_den_flow_iff.mpr (Flow.unstable_of_characteristic_root_re_pos (jacobian m.params m.θ)
    (reducedField_contDiff m.params) (reducedField_equilibrium m.params m.θ hp)
    (hasFDerivAt_reducedField m.params m.θ).fderiv hs hre)

/-- No model has both a Hurwitz reduced Jacobian (angle condition on a connected graph) and an
unstable one: the whole requirement language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize (Meets (n := n)) Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have hH := jacobian_isHurwitz_of_angle m.params m.θ (h .angle) (h .connected)
  obtain ⟨s, hs, hre⟩ : Meets m .jacobianUnstable := h .jacobianUnstable
  have := (Linear.spectrallyStable_iff_isHurwitz _).2 hH s hs
  linarith

/-- Every translation of the swing-network family is sound: power balance with the angle
condition on a connected graph proves the local sentences (a Hurwitz reduced Jacobian,
LeanForControl's linearization theorem), an unstable Jacobian proves instability, and passivity
holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, (family (n := n)).chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ :=
      (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · have hles : Meets m .powerFlow → Meets m .angle → Meets m .connected →
        LocallyExponentiallyStable m.field 0 := fun hp ha hc =>
      family_isAutonomous.mem_den_flow.mp (les_of_meets hp ha hc)
    rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable =>
      exact (hles (hm .powerFlow (by simp [translate])) (hm .angle (by simp [translate]))
        (hm .connected (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (hles (hm .powerFlow (by simp [translate])) (hm .angle (by simp [translate]))
          (hm .connected (by simp [translate])))
    case locallyExponentiallyStable =>
      exact hles (hm .powerFlow (by simp [translate])) (hm .angle (by simp [translate]))
        (hm .connected (by simp [translate]))
    case unstable =>
      exact family_isAutonomous.mem_den_flow.mp (unstable_of_meets
        (hm .powerFlow (by simp [translate])) (hm .jacobianUnstable (by simp [translate])))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% ((family (n := n)).Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- **Swing network, relative-angle coordinates.** At a synchronous equilibrium with
`Pₖ = ∑ⱼ Bₖⱼ sin(θ*ₖ - θ*ⱼ)`, every line angle difference `|θ*ᵢ - θ*ⱼ| < π/2` and a
connected coupling graph, the reduced nonlinear swing dynamics (relative angles and
frequencies, positive inertia and damping) is locally exponentially stable. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model n)
    (heq : ∀ k, m.params.P k = powerInjection m.params.B m.θ k)
    (hangle : ∀ i j, 0 < m.params.B i j → |m.θ i - m.θ j| < Real.pi / 2)
    (hconn : ∀ i j, Reach m.params.B i j) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact les_of_meets heq hangle hconn

/-- At a power-balance point, a reduced Jacobian with a characteristic root in the open right
half plane places the model in instability. -/
@[powerlib_domain] theorem mem_den_unstable (m : Model n)
    (heq : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) {s : ℂ}
    (hs : (Linear.characteristicMatrix (jacobian m.params m.θ) s).det = 0) (hre : 0 < s.re) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact unstable_of_meets heq ⟨s, hs, hre⟩

end powerlib.Network.Swing
