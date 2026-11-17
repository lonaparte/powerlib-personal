import theorem.Dynamics.Linearization
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Shift
import theorem.Dynamics.State
import theorem.Dynamics.Coordinates
import theorem.Family.Basic
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Lyapunov
import theorem.Grid.PowerFlow
import theorem.Spectral.Equilibrium
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Networked swing equations: local exponential stability in relative angles

The classical multi-machine swing network in relative-angle coordinates, read through a family
about a selected angle profile: local exponential stability of the synchronous equilibrium and
the exactness of each local translation.

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

Source: work-sync `theory/T-synchronization-manifold.md` §1.7 (swing network
`Mᵢ θ̈ᵢ = P_{m,i} - ∑ⱼ Bᵢⱼ ViVj sin(θᵢ - θⱼ)`, with damping as in §2.2 and
`theory/T-small-signal-stability.md`).

Results.
* Equilibrium / linearization level, with a nonlinear conclusion: the reduced nonlinear swing
  field is locally exponentially stable at the synchronous equilibrium
  (`mem_den_locallyExponentiallyStable`; private implementation
  `reducedSwing_locallyExponentiallyStable`). The proof derives the Jacobian by `fderiv`
  (`hasFDerivAt_reducedField`), shows it is Hurwitz from the eigenvector identity
  `μ²uᴴMu + μuᴴDu + uᴴLu = 0` with `L` the Laplacian of `Bᵢⱼ cos(θ*ᵢ - θ*ⱼ)`, and applies
  `hurwitz_linearization_locally_exponentially_stable`. One Hurwitz test serves every case
  (`jacobian_isHurwitz_of_hessForm`, signed weights allowed): the reduced Jacobian is Hurwitz
  when the form `A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)²` (`hessForm`, `2 uᵀLu`) is positive on
  every nonzero grounded direction `u₀ = 0` (`hessForm_add_const`, `hessForm_nonneg_of_pos`,
  `eq_zero_of_hessForm_eq_zero`, `sum_normSq_eq_hessForm`); nonnegative weights connecting all
  machines give it (`jacobian_isHurwitz`, through `dotProduct_laplacian_mulVec`,
  `edge_eq_of_form_zero`, `eq_of_reach`), and so does the angle condition
  (`jacobian_isHurwitz_of_angle`).
* Static evidence: `fullField_equilibrium_shift`, `reducedField_reduce`,
  `reducedField_equilibrium` and its converse `powerFlow_of_equilibrium` (the equilibria of the
  reduced field at the selected points are the power-balance points; a reduced state is fixed by
  its `dIdx`/`wIdx` blocks, `Dynamics.state_ext_blocks`), `jacobian_isHurwitz_of_angle`.
  Private implementation evidence (trajectory level, Rules §3a): `reduce_trajectory`.

Family and connection conclusions.
* System map: a model (`Model n`: the swing data `Params n` and a selected angle profile `θ*`)
  is read as the autonomous reduced field translated so that the selected point
  `equilibrium θ* = (θ*_{i+1} − θ*_0, 0)` is the origin, `z ↦ f(z + x*)`; every flow sentence is
  invariant under this translation (`Flow.Property.holds_shift_iff`), so the sentences speak
  about `x*` itself. No ports.
* Requirements (static): `powerFlow` (`Pₖ = ∑ⱼ Bₖⱼ sin(θ*ₖ − θ*ⱼ)`), `angle` (every coupled
  edge has `|θ*ᵢ − θ*ⱼ| < π/2`), `connected` (the graph of `B` is connected),
  `jacobianStable` (the reduced Jacobian at `x*` is Hurwitz), `jacobianUnstable` (the reduced
  Jacobian at `x*` has a characteristic root in the open right half plane). The local sentences
  translate into `{powerFlow, jacobianStable}`, instability into `{powerFlow, jacobianUnstable}`,
  passivity into nothing; the global sentences, decay rates, sampled contraction and
  conservation, which a linearization cannot decide, into the whole (inconsistent) language.
  The angle condition on a connected graph is a static sufficient condition for
  `jacobianStable` (`jacobian_isHurwitz_of_angle`), not a necessary one in meshed networks.
  With the Hurwitz test the local exponential translation is exact
  (`exact_locallyExponentiallyStable`, by the converse linearization theorem
  `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`).
* Connection theorems: `chain_le_semantics` (from the linearization,
  `Spectral.chain_le_semantics_of_jacobian`), `family_isAutonomous.exact_passive`,
  `exact_locallyExponentiallyStable`, `mem_den_locallyExponentiallyStable` and
  `mem_den_unstable`. Boundary witness: the instability translation is not exact
  (`not_exact_unstable`): instability is the failure of Lyapunov stability, so an unbalanced
  network (`offEquilibrium`) is unstable (`offEquilibrium_mem_den_unstable`,
  `Dynamics.unstable_of_ne_zero`) while the translation asks for power balance.
* Lyapunov translation: not exact for every network of at least two machines
  (`not_exact_lyapunovStable`, `n + 2` machines): `n + 2` uncoupled machines (`uncoupledN`,
  `B = 0`) are Lyapunov stable (`uncoupledN_mem_den_lyapunovStable`: in the block coordinates
  `(δᵢ + ω_{i+1} − ω₀, ω)`, built with `Fin.addCases`, the first block is conserved and the
  frequencies decay) while their reduced Jacobian has a zero column (`uncoupledN_not_isHurwitz`);
  two machines are `uncoupledN 0`. For a single machine (`family (n := 0)`) it is exact
  (`exact_lyapunovStable_zero`; `jacobian_isHurwitz_zero`).
* Local asymptotic translation `{powerFlow, jacobianStable}`, decided per number of machines:
  exact for one machine (`exact_locallyAsymptoticallyStable_zero`, here), two machines
  (`exact_locallyAsymptoticallyStable_two`) and three machines
  (`exact_locallyAsymptoticallyStable_three`) in
  `theorem/PowerSystem/Network/Swing/Degenerate.lean`; not exact for five or more machines
  (`not_exact_locallyAsymptoticallyStable`, `n + 5` machines, a five-machine ring with a degenerate
  strict minimum of the network potential plus unit leaves) in
  `theorem/PowerSystem/Network/Swing/DegenerateRing.lean`. The complete membership characterization
  for every `n` is `mem_den_locallyAsymptoticallyStable_iff` (power balance, a strict local minimum
  of the network potential in relative angles, and an isolated power-balance point). Four machines
  (`n = 3`): exact (`exact_locallyAsymptoticallyStable_four`,
  `theorem/PowerSystem/Network/Swing/FourDense.lean`; at most four lines already decided by
  `not_localAsymptoticStable_four`, `theorem/PowerSystem/Network/Swing/Four.lean`).
  Hence the local asymptotic translation is exact for at most four machines and not exact from five.
-/

noncomputable section
namespace powerlib.Network.Swing
open powerlib.Grid (powerInjection flowWeights hasFDerivAt_powerInjection)
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

@[tmio M, powerlib_domain] theorem powerInjection_add_const (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (θ : Fin (n + 1) → ℝ) (c : ℝ) :
    powerInjection B (fun k => θ k + c) = powerInjection B θ := by
  funext k
  simp [powerInjection]

/-- The full model has the equilibrium continuum `(θ* + c𝟙, 0)`: its linearization has a
zero eigenvalue along `𝟙`, so it cannot be exponentially stable in full coordinates. Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fullField_equilibrium_shift (p : Params n) (θ : Fin (n + 1) → ℝ)
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

@[tmio M, simp, powerlib_domain] theorem angleMap_zero (z : State (n + (n + 1))) :
    angleMap z 0 = 0 := by
  simp [angleMap]

@[tmio M, simp, powerlib_domain] theorem angleMap_succ (z : State (n + (n + 1))) (i : Fin n) :
    angleMap z i.succ = z (dIdx i) := by
  simp [angleMap]

/-- The reduced swing field on `(δ, ω)`. -/
def reducedField (p : Params n) (z : State (n + (n + 1))) : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun i => z (wIdx i.succ) - z (wIdx 0))
    (fun k => (p.P k - p.D k * z (wIdx k) - powerInjection p.B (angleMap z) k) / p.M k) r

@[tmio M, simp, powerlib_domain] theorem reducedField_dIdx (p : Params n) (z : State (n + (n + 1)))
    (i : Fin n) : reducedField p z (dIdx i) = z (wIdx i.succ) - z (wIdx 0) := by
  simp [reducedField]

@[tmio M, simp, powerlib_domain] theorem reducedField_wIdx (p : Params n) (z : State (n + (n + 1)))
    (k : Fin (n + 1)) : reducedField p z (wIdx k) =
      (p.P k - p.D k * z (wIdx k) - powerInjection p.B (angleMap z) k) / p.M k := by
  simp [reducedField]

/-- Reduction map `(θ, ω) ↦ (θ_{i+1} - θ₀, ω)`. -/
def reduce (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun i => x.1 i.succ - x.1 0) (fun k => x.2 k) r

@[tmio M, simp, powerlib_domain] theorem reduce_dIdx (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ))
    (i : Fin n) : reduce x (dIdx i) = x.1 i.succ - x.1 0 := by
  simp [reduce]

@[tmio M, simp, powerlib_domain] theorem reduce_wIdx (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ))
    (k : Fin (n + 1)) : reduce x (wIdx k) = x.2 k := by
  simp [reduce]

@[tmio M, powerlib_domain] theorem angleMap_reduce (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    angleMap (reduce x) = fun k => x.1 k + -x.1 0 := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [sub_eq_add_neg]

/-- The reduction intertwines the full and the reduced field. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem reducedField_reduce (p : Params n)
    (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    reducedField p (reduce x) = reduce (fullField p x) := by
  apply Dynamics.state_ext_blocks
  · intro i; simp [fullField]
  · intro k
    simp only [reducedField_wIdx, reduce_wIdx, fullField, angleMap_reduce,
      powerInjection_add_const]

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Every trajectory of the full swing model projects to a trajectory of the reduced field. -/
@[tmio M, powerlib_domain] private theorem reduce_trajectory (p : Params n)
    {x : ℝ → (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)} {t : ℝ}
    (hx : HasDerivAt x (fullField p (x t)) t) :
    HasDerivAt (fun s => reduce (x s)) (reducedField p (reduce (x t))) t := by
  rw [reducedField_reduce]
  have hlin : ∃ R : ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) →L[ℝ] State (n + (n + 1)),
      ∀ y, R y = reduce y := by
    refine ⟨(PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin (n + (n + 1)) => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun r => Fin.addCases (motive := fun _ => _ →L[ℝ] ℝ)
        (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.succ).comp
            (ContinuousLinearMap.fst ℝ (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)) -
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0).comp
            (ContinuousLinearMap.fst ℝ (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ)))
        (fun k => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k).comp
          (ContinuousLinearMap.snd ℝ (Fin (n + 1) → ℝ) (Fin (n + 1) → ℝ))) r), ?_⟩
    intro y
    apply Dynamics.state_ext_blocks
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
@[tmio M, powerlib_domain] theorem reducedField_equilibrium (p : Params n) (θ : Fin (n + 1) → ℝ)
    (heq : ∀ k, p.P k = powerInjection p.B θ k) :
    reducedField p (equilibrium θ) = 0 := by
  rw [equilibrium, reducedField_reduce]
  have : fullField p (θ, 0) = 0 := by
    have := fullField_equilibrium_shift p θ heq 0
    simpa using this
  rw [this]
  apply Dynamics.state_ext_blocks <;> intro _ <;> simp

/-- Block form of the reduced Jacobian. -/
def jacobianBlocks (p : Params n) (θ : Fin (n + 1) → ℝ) :
    Matrix (Fin n ⊕ Fin (n + 1)) (Fin n ⊕ Fin (n + 1)) ℝ :=
  fromBlocks 0
    (Matrix.of fun i k => (if k = i.succ then 1 else 0) - (if k = 0 then 1 else 0))
    (Matrix.of fun k i => -(laplacian (flowWeights p.B θ) k i.succ) / p.M k)
    (Matrix.of fun k k' => if k = k' then -(p.D k / p.M k) else 0)

/-- The reduced Jacobian matrix in the state order `(δ, ω)`. -/
def jacobian (p : Params n) (θ : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + (n + 1))) (Fin (n + (n + 1))) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (jacobianBlocks p θ)

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
  /-- The reduced Jacobian at `θ*` is Hurwitz. -/
  | jacobianStable
  /-- The reduced Jacobian at `θ*` has a characteristic root in the open right half plane. -/
  | jacobianUnstable

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model n) : Requirement → Prop
  | .powerFlow => ∀ k, m.params.P k = powerInjection m.params.B m.θ k
  | .angle => ∀ i j, 0 < m.params.B i j → |m.θ i - m.θ j| < Real.pi / 2
  | .connected => ∀ i j, Reach m.params.B i j
  | .jacobianStable => LinearSystems.IsHurwitz (jacobian m.params m.θ)
  | .jacobianUnstable =>
    ∃ s : ℂ, (Linear.characteristicMatrix (jacobian m.params m.θ) s).det = 0 ∧ 0 < s.re

/-- The translation of the sentences: the local ones into power balance with a Hurwitz reduced
Jacobian, instability into power balance with an unstable Jacobian, passivity into nothing. The
global sentences, decay rates, sampled contraction and conservation are translated into the
whole language, which no model meets (unavailable translation coverage, not a usable
translation). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.powerFlow, .jacobianStable}
  | .flow .unstable => {.powerFlow, .jacobianUnstable}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The swing-network family: every model read as its autonomous field translated to the
selected point. -/
def family : Family (Model n) Requirement (n + (n + 1)) 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous :
    (family (n := n)).IsAutonomous Model.field := fun _ => rfl

/-- A flow sentence of a model is the sentence of the untranslated reduced field at the
selected point. -/
@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model n} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (reducedField m.params) (equilibrium m.θ) :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model n => reducedField m.params)
    (pt := fun m => equilibrium m.θ) family_isAutonomous

@[tmio M, simp, powerlib_domain] theorem jacobian_dd (p : Params n) (θ : Fin (n + 1) → ℝ)
    (i i' : Fin n) : jacobian p θ (dIdx i) (dIdx i') = 0 := by
  simp [jacobian, jacobianBlocks]

@[tmio M, simp, powerlib_domain] theorem jacobian_dw (p : Params n) (θ : Fin (n + 1) → ℝ)
    (i : Fin n) (k : Fin (n + 1)) : jacobian p θ (dIdx i) (wIdx k) =
      (if k = i.succ then 1 else 0) - (if k = 0 then 1 else 0) := by
  simp [jacobian, jacobianBlocks]

@[tmio M, simp, powerlib_domain] theorem jacobian_wd (p : Params n) (θ : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) (i : Fin n) : jacobian p θ (wIdx k) (dIdx i) =
      -(laplacian (flowWeights p.B θ) k i.succ) / p.M k := by
  simp [jacobian, jacobianBlocks]

@[tmio M, simp, powerlib_domain] theorem jacobian_ww (p : Params n) (θ : Fin (n + 1) → ℝ)
    (k k' : Fin (n + 1)) : jacobian p θ (wIdx k) (wIdx k') =
      if k = k' then -(p.D k / p.M k) else 0 := by
  simp [jacobian, jacobianBlocks]

@[tmio M, powerlib_domain] theorem flowWeights_angleMap_equilibrium (p : Params n)
    (θ : Fin (n + 1) → ℝ) :
    flowWeights p.B (angleMap (equilibrium θ)) = flowWeights p.B θ := by
  ext i j
  simp [flowWeights, equilibrium, angleMap_reduce]

@[tmio M, powerlib_domain] theorem laplacian_angleMap (p : Params n) (θ : Fin (n + 1) → ℝ)
    (v : State (n + (n + 1))) (k : Fin (n + 1)) :
    (laplacian (flowWeights p.B θ) *ᵥ angleMap v) k =
      ∑ i : Fin n, laplacian (flowWeights p.B θ) k i.succ * v (dIdx i) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, angleMap_zero, mul_zero, zero_add,
    angleMap_succ]

/-- The Jacobian of the reduced field at the synchronous equilibrium. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_reducedField (p : Params n) (θ : Fin (n + 1) → ℝ) :
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
      _root_.sub_apply]
    rw [mulVec, dotProduct, Fin.sum_univ_add]
    simp only [jacobian_dd, zero_mul, Finset.sum_const_zero, zero_add, jacobian_dw, sub_mul,
      ite_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
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
    rw [mulVec, dotProduct, Fin.sum_univ_add]
    simp only [jacobian_wd, jacobian_ww, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
      flowWeights_angleMap_equilibrium, laplacian_angleMap, PiLp.proj_apply, zero_sub,
      _root_.neg_apply]
    simp only [mul_sub, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro x _; ring

/-! ## The Jacobian is Hurwitz -/

@[tmio T, powerlib_foundation] theorem re_neg_of_quadratic {μ : ℂ} {m d l : ℝ} (hm : 0 < m) (hd : 0 < d)
    (hl : 0 ≤ l) (h : (m : ℂ) * μ ^ 2 + d * μ + l = 0) (hμ : μ ≠ 0) : μ.re < 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.add_im, Complex.mul_im, Complex.zero_im, zero_mul, sub_zero,
    add_zero] at hre him
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

@[tmio M, powerlib_domain] theorem flowWeights_symm (p : Params n) (θ : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    flowWeights p.B θ i j = flowWeights p.B θ j i := by
  simp only [flowWeights, of_apply, p.B_symm i j]
  rw [← Real.cos_neg, neg_sub]

/-! ## A Hurwitz test with signed linearization weights -/

/-- Second-order coefficient `A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)²` (twice the Hessian form). -/
def hessForm (p : Params n) (θ u : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, ∑ j, p.B k j * Real.cos (θ k - θ j) * (u k - u j) ^ 2

@[tmio M, powerlib_domain] theorem hessForm_add_const (p : Params n) (θ u : Fin (n + 1) → ℝ)
    (c : ℝ) : hessForm p θ (fun k => u k + c) = hessForm p θ u := by
  simp [hessForm]

@[tmio M, powerlib_domain] theorem hessForm_nonneg_of_pos {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hpos : ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm p θ u)
    (v : Fin (n + 1) → ℝ) : 0 ≤ hessForm p θ v := by
  rw [← hessForm_add_const p θ v (-v 0)]
  by_cases h : (fun k => v k + -v 0) = 0
  · rw [h]; simp [hessForm]
  · exact (hpos _ (by simp) h).le

@[tmio M, powerlib_domain] theorem eq_zero_of_hessForm_eq_zero {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hpos : ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm p θ u)
    {v : Fin (n + 1) → ℝ} (h0 : v 0 = 0) (h : hessForm p θ v = 0) : v = 0 := by
  by_contra hne
  exact (hpos v h0 hne).ne' h

@[tmio M, powerlib_domain] theorem sum_normSq_eq_hessForm (p : Params n) (θ : Fin (n + 1) → ℝ)
    (u : Fin (n + 1) → ℂ) :
    ∑ i, ∑ j, flowWeights p.B θ i j * Complex.normSq (u i - u j) =
      hessForm p θ (fun k => (u k).re) + hessForm p θ (fun k => (u k).im) := by
  simp only [hessForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [flowWeights, of_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- **Hurwitz test by the Hessian form.** The reduced swing Jacobian is Hurwitz whenever the form
`A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)²` is positive on every nonzero `u` with `u₀ = 0`
(positive inertia and damping; signed linearization weights are allowed). -/
@[tmio M, powerlib_domain] theorem jacobian_isHurwitz_of_hessForm (p : Params n)
    (θ : Fin (n + 1) → ℝ)
    (hpos : ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm p θ u) :
    connection% ((⟨p, θ⟩ : Model n) ∈ TMIO.realize Meets {.jacobianStable}) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq,
    powerlib.Network.Swing.Meets]
  change LinearSystems.IsHurwitz (jacobian p θ)
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
    rw [Fin.sum_univ_add] at this
    simp only [jacobian_dd, jacobian_dw, Complex.ofReal_sub, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, zero_add, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one,
      sub_mul, ite_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at this
    exact this
  have hζ0 : ζ 0 = 0 := rfl
  have hζs : ∀ i, ζ i.succ = η i := fun i => rfl
  have h2 : ∀ k, μ * p.M k * w k + p.D k * w k +
      ∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l) = 0 := by
    intro k
    have := hrow (wIdx k)
    rw [Fin.sum_univ_add] at this
    simp only [jacobian_wd, jacobian_ww] at this
    have e1 : ∑ l, ((laplacian (flowWeights p.B θ) k l : ℝ) : ℂ) * ζ l =
        ∑ i : Fin n, ((laplacian (flowWeights p.B θ) k i.succ : ℝ) : ℂ) * η i := by
      rw [Fin.sum_univ_succ, hζ0, mul_zero, zero_add]
      rfl
    have hL : ∑ i : Fin n, ((-(laplacian (flowWeights p.B θ) k i.succ) / p.M k : ℝ) : ℂ) *
        v (dIdx i) = -(∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l)) / p.M k := by
      have hrow : ∑ l, ((laplacian (flowWeights p.B θ) k l : ℝ) : ℂ) * ζ l =
          ∑ l, (flowWeights p.B θ k l : ℂ) * (ζ k - ζ l) := by
        have h := laplacian_mulVec_apply ((flowWeights p.B θ).map Complex.ofRealHom) ζ k
        rw [← laplacian_map] at h
        exact h
      rw [← hrow, e1, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
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
      exact this
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
      have htot := sum_laplacian_mulVec (W := (flowWeights p.B θ).map Complex.ofRealHom)
        (fun i j => by simp [hWs i j]) ζ
      simp only [laplacian_mulVec_apply, map_apply, Complex.ofRealHom_eq_coe] at htot
      rw [Finset.sum_mul, Finset.sum_congr rfl (fun k _ => e k), Finset.sum_neg_distrib, htot,
        neg_zero]
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
    have hζ : ζ = 0 := by
      have hz := star_dotProduct_laplacian_mulVec hWs ζ
      rw [Finset.sum_eq_zero fun k _ => by rw [hlap k, mul_zero]] at hz
      have hz' : ∑ i, ∑ j, flowWeights p.B θ i j * Complex.normSq (ζ i - ζ j) = 0 := by
        have := congrArg Complex.re hz
        simp only [Complex.zero_re, Complex.ofReal_re] at this
        linarith
      rw [sum_normSq_eq_hessForm] at hz'
      have h1 := hessForm_nonneg_of_pos hpos (fun k => (ζ k).re)
      have h2 := hessForm_nonneg_of_pos hpos (fun k => (ζ k).im)
      have hre := eq_zero_of_hessForm_eq_zero (v := fun k => (ζ k).re) hpos
        (by show (ζ 0).re = 0; rw [hζ0]; rfl) (by linarith)
      have him := eq_zero_of_hessForm_eq_zero (v := fun k => (ζ k).im) hpos
        (by show (ζ 0).im = 0; rw [hζ0]; rfl) (by linarith)
      funext k
      exact Complex.ext (congrFun hre k) (congrFun him k)
    exact hv0 (funext fun i => by rw [← hζs i, hζ]; rfl)
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
    have hl : 0 ≤ (∑ i, ∑ j, flowWeights p.B θ i j * Complex.normSq (u i - u j)) / 2 := by
      rw [sum_normSq_eq_hessForm]
      exact div_nonneg (add_nonneg (hessForm_nonneg_of_pos hpos _)
        (hessForm_nonneg_of_pos hpos _)) zero_le_two
    exact re_neg_of_quadratic hm hd hl hsum hμ

/-- The reduced swing Jacobian is Hurwitz when the linearization weights are
nonnegative and their positive edges connect all machines: then `A₂` is twice the Laplacian form
of the weights, positive on every nonzero grounded direction (`jacobian_isHurwitz_of_hessForm`). -/
@[tmio M, powerlib_domain] theorem jacobian_isHurwitz (p : Params n) (θ : Fin (n + 1) → ℝ)
    (hWnn : ∀ i j, 0 ≤ flowWeights p.B θ i j) (hconn : ∀ i j, Reach (flowWeights p.B θ) i j) :
    connection% ((⟨p, θ⟩ : Model n) ∈ TMIO.realize Meets {.jacobianStable}) := by
  refine jacobian_isHurwitz_of_hessForm p θ fun u h0 hu => ?_
  have hWs := flowWeights_symm p θ
  have hH : hessForm p θ u = 2 * dotProduct u (laplacian (flowWeights p.B θ) *ᵥ u) := by
    rw [dotProduct_laplacian_mulVec hWs]
    simp only [hessForm, flowWeights, of_apply]
    ring
  rw [hH]
  refine mul_pos two_pos ((laplacian_posSemidef_form hWs hWnn u).lt_of_ne fun h => hu ?_)
  funext k
  rw [eq_of_reach (edge_eq_of_form_zero hWs hWnn h.symm) (hconn k 0), h0]
  rfl

@[tmio M, powerlib_domain] theorem reducedField_contDiff (p : Params n) :
    ContDiff ℝ 1 (reducedField p) := by
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
@[tmio M, powerlib_domain] theorem jacobian_isHurwitz_of_angle (p : Params n) (θ : Fin (n + 1) → ℝ)
    (hangle : ∀ i j, 0 < p.B i j → |θ i - θ j| < Real.pi / 2)
    (hconn : ∀ i j, Reach p.B i j) :
    connection% ((⟨p, θ⟩ : Model n) ∈ TMIO.realize Meets {.jacobianStable}) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets]
  change LinearSystems.IsHurwitz (jacobian p θ)
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
  exact (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets] using (jacobian_isHurwitz p θ hWnn hconnW))

/-- Implementation evidence for `mem_den_locallyExponentiallyStable`, at the selected point of
the untranslated field. -/
@[tmio TM, powerlib_domain] private theorem reducedSwing_locallyExponentiallyStable (p : Params n)
    (θ : Fin (n + 1) → ℝ) (heq : ∀ k, p.P k = powerInjection p.B θ k)
    (hangle : ∀ i j, 0 < p.B i j → |θ i - θ j| < Real.pi / 2)
    (hconn : ∀ i j, Reach p.B i j) :
    connection% ((⟨p, θ⟩ : Model n) ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% mem_den_flow_iff)]
  change LocallyExponentiallyStable (reducedField p) (equilibrium θ)
  exact hurwitz_linearization_locally_exponentially_stable (jacobian p θ)
    (reducedField_contDiff p) (reducedField_equilibrium p θ heq)
    (hasFDerivAt_reducedField p θ).fderiv ((by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets] using (jacobian_isHurwitz_of_angle p θ hangle hconn)))

/-- No model has both a Hurwitz reduced Jacobian (angle condition on a connected graph) and an
unstable one: the whole requirement language is inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize (Meets (n := n)) Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  have hH := (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets] using (jacobian_isHurwitz_of_angle m.params m.θ (h .angle) (h .connected)))
  obtain ⟨s, hs, hre⟩ : Meets m .jacobianUnstable := h .jacobianUnstable
  have := (Linear.spectrallyStable_iff_isHurwitz _).2 hH s hs
  linarith

/-- Every translation of the swing-network family is sound: power balance with the angle
condition on a connected graph proves the local sentences (a Hurwitz reduced Jacobian,
LeanForControl's linearization theorem), an unstable Jacobian proves instability, and passivity
holds without requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, (family (n := n)).chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_jacobian (fun m P => mem_den_flow_iff)
    family_isAutonomous.den_passive (Rs := {.powerFlow, .jacobianStable})
    (Ru := {.powerFlow, .jacobianUnstable})
    (fun s => by rcases s with P | _ | _ <;> (try cases P) <;> rfl)
    (fun m => jacobian m.params m.θ) (fun m hm => ?_)
    (fun m hm => (TMIO.mem_realize _ _ _).mp hm .jacobianStable (by simp))
    fun m hm => (TMIO.mem_realize _ _ _).mp hm .jacobianUnstable (by simp)
  have hp : Meets m .powerFlow := by
    rcases hm with hm | hm <;> exact (TMIO.mem_realize _ _ _).mp hm .powerFlow (by simp)
  exact ⟨reducedField_contDiff m.params, reducedField_equilibrium m.params m.θ hp,
    (hasFDerivAt_reducedField m.params m.θ).fderiv⟩

/-- An equilibrium of the reduced field at the selected point is a power-balance point (the
converse of `reducedField_equilibrium`). Read through the existing family endpoint.
 -/
@[tmio M, powerlib_domain] theorem powerFlow_of_equilibrium {p : Params n} {θ : Fin (n + 1) → ℝ}
    (h : reducedField p (equilibrium θ) = 0) :
    connection% ((⟨p, θ⟩ : Model n) ∈ TMIO.realize Meets {.powerFlow}) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets]
  change ∀ k, p.P k = powerInjection p.B θ k
  intro k
  have hk := congrArg (fun z : State (n + (n + 1)) => z (wIdx k)) h
  simp only [reducedField_wIdx, equilibrium, reduce_wIdx, angleMap_reduce,
    powerInjection_add_const, PiLp.zero_apply] at hk
  rw [div_eq_zero_iff, or_iff_left (p.M_pos k).ne'] at hk
  simp only [Pi.zero_apply, mul_zero, sub_zero] at hk
  linarith

/-- The local exponential translation is exact: a swing-network model is locally exponentially
stable at its selected point exactly when the angle profile is a power-balance point with a
Hurwitz reduced Jacobian. Converse linearization: local exponential stability of the `C¹`
reduced field forces an equilibrium with a Hurwitz Jacobian. -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% ((family (n := n)).Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exact_of_exactUnder_empty (Spectral.exactUnder_les_of_jacobian
    (fun m P => mem_den_flow_iff) ∅ (fun m => jacobian m.params m.θ)
    (fun m _ hm => Family.chain_le_semantics_iff.mp chain_le_semantics _ hm)
    (fun m _ => reducedField_contDiff m.params)
    (fun m _ => (hasFDerivAt_reducedField m.params m.θ).fderiv) fun m _ heq hH => ?_)
  rw [(connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl)
  · exact (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets] using (powerFlow_of_equilibrium heq))
  · exact hH

/-- **Swing network, relative-angle coordinates.** At a synchronous equilibrium with
`Pₖ = ∑ⱼ Bₖⱼ sin(θ*ₖ - θ*ⱼ)`, every line angle difference `|θ*ᵢ - θ*ⱼ| < π/2` and a
connected coupling graph, the reduced nonlinear swing dynamics (relative angles and
frequencies, positive inertia and damping) is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model n)
    (heq : ∀ k, m.params.P k = powerInjection m.params.B m.θ k)
    (hangle : ∀ i j, 0 < m.params.B i j → |m.θ i - m.θ j| < Real.pi / 2)
    (hconn : ∀ i j, Reach m.params.B i j) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact reducedSwing_locallyExponentiallyStable m.params m.θ heq hangle hconn

/-- At a power-balance point, a reduced Jacobian with a characteristic root in the open right
half plane places the model in instability. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model n)
    (heq : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) {s : ℂ}
    (hs : (Linear.characteristicMatrix (jacobian m.params m.θ) s).det = 0) (hre : 0 < s.re) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mp chain_le_semantics _
    ((TMIO.mem_realize _ _ _).mpr fun q hq => ?_)
  rcases hq with rfl | rfl
  exacts [heq, ⟨s, hs, hre⟩]

/-! ### Instability away from equilibrium -/

/-- An unbalanced network: unit inertia, damping and power at every machine, no coupling,
`θ* = 0`. -/
def offEquilibrium : Model n :=
  ⟨⟨fun _ => 1, fun _ => 1, fun _ => 1, 0, fun _ => one_pos, fun _ => one_pos,
    fun _ _ => rfl, fun _ _ => le_rfl⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[tmio TM, powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% ((offEquilibrium (n := n)) ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff)
    (reducedField_contDiff _) fun h => ?_
  have := ((TMIO.mem_realize _ _ _).mp (powerFlow_of_equilibrium h) .powerFlow (by simp)) 0
  simp [offEquilibrium, powerInjection] at this

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for power balance. -/
@[tmio TM, powerlib_domain] theorem not_exact_unstable :
    connection% (¬ (family (n := n)).Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.not_exact_of_witness (offEquilibrium_mem_den_unstable (n := n))
    (q := .powerFlow) (by simp [family, translate]) fun hp => ?_
  have := (hp : Meets (offEquilibrium (n := n)) .powerFlow) 0
  simp [offEquilibrium, powerInjection] at this

/-! ### The Lyapunov translation for every number of machines -/

/-- `n + 2` uncoupled machines: unit inertia and damping, no power, no coupling, `θ* = 0`. In the
reduced state the field is `δ̇ᵢ = ω_{i+1} − ω₀`, `ω̇ₖ = −ωₖ`. -/
def uncoupledN (n : ℕ) : Model (n + 1) :=
  ⟨⟨fun _ => 1, fun _ => 1, fun _ => 0, 0, fun _ => one_pos, fun _ => one_pos,
    fun _ _ => rfl, fun _ _ => le_rfl⟩, 0⟩

@[tmio M, powerlib_domain] private theorem uncoupledN_point : equilibrium (uncoupledN n).θ = 0 := by
  apply Dynamics.state_ext_blocks
  · intro i; simp [equilibrium, uncoupledN]
  · intro k; simp [equilibrium, uncoupledN]

@[tmio M, powerlib_domain] private theorem uncoupledN_field_d (z : State (n + 1 + (n + 1 + 1))) (i : Fin (n + 1)) :
    (uncoupledN n).field z (dIdx i) = z (wIdx i.succ) - z (wIdx 0) := by
  simp [Model.field, uncoupledN_point]

@[tmio M, powerlib_domain] private theorem uncoupledN_field_w (z : State (n + 1 + (n + 1 + 1))) (k : Fin (n + 1 + 1)) :
    (uncoupledN n).field z (wIdx k) = - z (wIdx k) := by
  show reducedField _ (z + equilibrium (uncoupledN n).θ) (wIdx k) = _
  rw [uncoupledN_point, add_zero, reducedField_wIdx]
  simp [uncoupledN, powerInjection]

/-- The block coordinates `(δᵢ + ω_{i+1} − ω₀, ω)` (built with `Fin.addCases`): the first block is
conserved by the uncoupled field. -/
private def conservedLin (m : ℕ) : State (m + (m + 1)) →ₗ[ℝ] State (m + (m + 1)) where
  toFun z := WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun i => z (dIdx i) + z (wIdx i.succ) - z (wIdx 0)) (fun k => z (wIdx k)) r
  map_add' z w := by
    apply Dynamics.state_ext_blocks
    · intro i; simp; ring
    · intro k; simp
  map_smul' c z := by
    apply Dynamics.state_ext_blocks
    · intro i; simp; ring
    · intro k; simp

@[tmio M, powerlib_domain] private theorem conservedLin_d {m : ℕ} (z : State (m + (m + 1)))
    (i : Fin m) :
    conservedLin m z (dIdx i) = z (dIdx i) + z (wIdx i.succ) - z (wIdx 0) := by
  simp [conservedLin]

@[tmio M, powerlib_domain] private theorem conservedLin_w {m : ℕ} (z : State (m + (m + 1)))
    (k : Fin (m + 1)) :
    conservedLin m z (wIdx k) = z (wIdx k) := by
  simp [conservedLin]

@[tmio M, powerlib_domain] private theorem conservedLin_injective (m : ℕ) : Function.Injective
    (conservedLin m) := by
  intro z w h
  have hw : ∀ k, z (wIdx k) = w (wIdx k) := fun k => by
    have := congrArg (fun y : State (m + (m + 1)) => y (wIdx k)) h
    simpa [conservedLin_w] using this
  apply Dynamics.state_ext_blocks _ hw
  intro i
  have := congrArg (fun y : State (m + (m + 1)) => y (dIdx i)) h
  simp only [conservedLin_d, hw] at this
  linarith

/-- `n + 2` uncoupled machines are Lyapunov stable: in the block coordinates
`(δᵢ + ω_{i+1} − ω₀, ω)` the first block is conserved and the frequencies decay, so the quadratic
energy `∑ᵢ (δᵢ + ω_{i+1} − ω₀)² + ∑ₖ ωₖ²` does not increase. -/
@[tmio TM, powerlib_domain] theorem uncoupledN_mem_den_lyapunovStable :
    connection% (uncoupledN n ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  refine Dynamics.lyapunovStable_of_inner_nonpos (by omega)
    (LinearMap.toContinuousLinearMap (conservedLin (n + 1))) (conservedLin_injective _)
    fun z => ?_
  simp only [LinearMap.coe_toContinuousLinearMap', PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin (n + 1), conservedLin (n + 1) ((uncoupledN n).field z) (dIdx i) = 0 := by
    intro i
    rw [conservedLin_d, uncoupledN_field_d, uncoupledN_field_w, uncoupledN_field_w]
    ring
  simp only [h1, zero_mul, Finset.sum_const_zero, zero_add, conservedLin_w, uncoupledN_field_w]
  exact Finset.sum_nonpos fun k _ => by nlinarith [sq_nonneg (z (wIdx k))]

/-- The reduced Jacobian of `n + 2` uncoupled machines is not Hurwitz (the column of `δ₀` is zero).
Read through the existing family endpoint. -/
@[tmio M, powerlib_domain] theorem uncoupledN_not_isHurwitz :
    connection% (uncoupledN n ∉ TMIO.realize Meets {.jacobianStable}) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets]
  change ¬ LinearSystems.IsHurwitz (jacobian (uncoupledN n).params (uncoupledN n).θ)
  intro hH
  apply Dynamics.mulVec_ne_zero_of_isHurwitz hH (v := Pi.single (dIdx 0) 1)
  · intro h
    have := congrFun h (dIdx 0)
    simp at this
  · rw [Matrix.mulVec_single]
    funext r
    refine Fin.addCases (fun i => ?_) (fun k => ?_) r
    · have h := jacobian_dd (uncoupledN n).params (uncoupledN n).θ i 0
      simp only [Pi.smul_apply, Matrix.col_apply, op_smul_eq_mul, mul_one, Pi.zero_apply]
      exact h
    · have h := jacobian_wd (uncoupledN n).params (uncoupledN n).θ k 0
      simp only [Pi.smul_apply, Matrix.col_apply, op_smul_eq_mul, mul_one, Pi.zero_apply]
      rw [h]
      simp [uncoupledN, laplacian, flowWeights]

/-- **The Lyapunov translation is not exact for any network of at least two machines**
(`n + 2` machines, every `n`): `n + 2` uncoupled machines are Lyapunov stable at a power-balance
point whose reduced Jacobian is not Hurwitz. -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ (family (n := n + 1)).Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness (uncoupledN_mem_den_lyapunovStable (n := n))
    (q := .jacobianStable) (by simp [family, translate]) (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets] using (uncoupledN_not_isHurwitz))

/-! ### A single machine -/

/-- The reduced Jacobian of a single machine (`n = 0`, the frequency alone) is Hurwitz. Read through the existing family endpoint.
 -/
@[tmio M, powerlib_domain] theorem jacobian_isHurwitz_zero (p : Params 0) (θ : Fin 1 → ℝ) :
    connection% ((⟨p, θ⟩ : Model 0) ∈ TMIO.realize Meets {.jacobianStable}) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets]
  change LinearSystems.IsHurwitz (jacobian p θ)
  have hij : ∀ i j : Fin (0 + 1), i = j := fun i j => Fin.ext (by omega)
  refine (TMIO.mem_realize _ _ _).mp (jacobian_isHurwitz p θ (fun i j => ?_) (fun i j => ?_)) .jacobianStable (by simp)
  · rw [hij i j]
    simp [flowWeights, p.B_nonneg]
  · rw [hij i j]
    exact Relation.ReflTransGen.refl

/-- For a single machine the Lyapunov and local asymptotic translations are exact: a Lyapunov
stable point of the `C¹` field is an equilibrium, hence a power-balance point, and the reduced
Jacobian is always Hurwitz (`jacobian_isHurwitz_zero`), so every equilibrium meets the translation
(`Spectral.exact_of_equilibrium`, with no degenerate equilibria). -/
@[tmio TM, powerlib_domain] private theorem exact_zero {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable) :
    connection% ((family (n := 0)).Exact (.flow P)) := by
  change (family (n := 0)).Exact (.flow P)
  have hsound := chain_le_semantics (n := 0)
  unfold powerlib.TMIO.Statement at hsound
  have ht : (family (n := 0)).translate (.flow P) = {.powerFlow, .jacobianStable} := by
    rcases hP with rfl | rfl <;> rfl
  refine Spectral.exact_of_equilibrium (fun m P => mem_den_flow_iff)
    (by rcases hP with rfl | rfl <;> simp) (fun _ => True)
    (Family.chain_le_semantics_iff.mp hsound _) (fun m => reducedField_contDiff m.params)
    (fun _ _ h => absurd trivial h) fun m heq _ => ?_
  rw [ht, (connection_proof% TMIO.mem_realize)]
  rintro q (rfl | rfl)
  · exact (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets] using (powerFlow_of_equilibrium heq))
  · exact (by simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, powerlib.Network.Swing.family, powerlib.Network.Swing.Meets] using (jacobian_isHurwitz_zero _ _))

/-- For a single machine (`n = 0`) the Lyapunov translation is exact. -/
@[tmio TM, powerlib_domain] theorem exact_lyapunovStable_zero :
    connection% ((family (n := 0)).Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact exact_zero (Or.inl rfl)

/-- For a single machine (`n = 0`) the local asymptotic translation is exact. -/
@[tmio TM, powerlib_domain] theorem exact_locallyAsymptoticallyStable_zero :
    connection% ((family (n := 0)).Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact exact_zero (Or.inr rfl)

end powerlib.Network.Swing
