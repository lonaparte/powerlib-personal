import theorem.PH.Composition
import theorem.Network.WeightedLaplacian

/-! # Lumped RL networks (with optional node capacitors) as port-Hamiltonian systems

RL networks on an arbitrary (possibly weighted) incidence matrix, with or without node
capacitors, as diagonal port-Hamiltonian data; passivity, stability and invariance under branch
rescaling (ideal-transformer referral).

Model boundary.
* Topology: a finite directed multigraph with node type `ν` and branch type `β` (`Fintype`,
  `DecidableEq`). The signed incidence matrix `signedIncidence tail head : Matrix ν β ℝ`
  (`Network.signedIncidence`, `theorem/Network/WeightedLaplacian.lean`) has entry `+1` at the
  tail of a branch (branch current leaves the node), `−1` at the head, `0` otherwise (a
  self-loop gives a zero column). Mathlib's `incMatrix` is unsigned and is not used. Every model
  below is stated for an **arbitrary** real matrix `𝓑 : Matrix ν β ℝ`, so weighted
  (ideal-transformer) incidence columns are included.
* Branches: series `L_k > 0`, `r_k ≥ 0`; state is the branch flux `φ_k = L_k i_k`;
  `H = Σ φ_k² / (2 L_k)`. Lumped, linear, continuous time, single phase or one axis of a
  stationary frame (no dq rotation terms), no switching, no controller.
* `rlNetwork` (note §1.6.bis): input = node potentials `v_node : ν → ℝ`, output =
  node current injections `i_node = 𝓑 i_br`; `J = 0`, `R = diag r`, `B = 𝓑ᵀ`.
  KVL: `φ̇_k = v(tail k) − v(head k) − r_k i_k`; port power `v_nodeᵀ i_node`.
* `rlcNetwork` (note §1.6.ter, node capacitors): state `(φ, q)` on `β ⊕ ν` with
  `q_i = C_i v_i`, `C_i > 0`, plus a shunt conductance `G_i ≥ 0` from node `i` to ground
  (constant-impedance load, which enters `R`, cf. T-power-system-ph §1.7); input = current
  injected into each node by an external source, output = node voltage.
  `J = [[0, 𝓑ᵀ], [−𝓑, 0]]`, `R = diag(r, G)`, `B = [0; I]`.
* Nothing is claimed about a particular grid.

Source: work-sync `theory/T-ph.md` §1.6.bis (RL network pH form and energy check),
§1.6.ter (node capacitors, transformers, constant-impedance loads).

Results (static evidence on the models).
* `signedIncidence_mulVec` (KCL), `rlNetwork_field_signedIncidence` (KVL around each branch),
  `rlNetwork_power_balance` — `Ḣ = i_nodeᵀ v_node − Σ r_k i_k²`; `rlcNetwork_field_branch`,
  `rlcNetwork_field_node`, `rlcNetwork_power_balance` —
  `Ḣ = Σ u_j v_j − Σ r_k i_k² − Σ G_j v_j²`.
* Branch rescaling (transformer form): rescaling branch states by nonzero factors `c_k`
  maps the network `(L, r, 𝓑)` to `(c² L, c² r, 𝓑 · diag c)`, with the same node port
  behaviour and the same energy (`rlNetwork_scale_field`, `rlNetwork_scale_output`,
  `rlNetwork_scale_energy`, `rlNetwork_scale_similar_data`).

Family and connection conclusions.
* The networks are diagonal port-Hamiltonian data (`DiagonalPH`, `theorem/PH/Composition.lean`);
  with `m` branches `Fin m` and `k` nodes `Fin k` they are numbered into linear port-Hamiltonian
  plants (`rlNetworkPH : Port.PortHamiltonian m k`,
  `rlcNetworkPH : Port.PortHamiltonian (m + k) k`, states `(φ, q)` numbered by
  `finSumFinEquiv`) and read through the existing family `Port.PortHamiltonian.family` (system
  map: the plant's port system; sentences at the origin, which is the unforced operating point
  of both networks).
* Connection conclusions: passivity and Lyapunov stability of both networks
  (`rlNetworkPH_mem_den_passive`, `rlNetworkPH_mem_den_lyapunovStable`,
  `rlcNetworkPH_mem_den_passive`, `rlcNetworkPH_mem_den_lyapunovStable`); global exponential
  stability of the unforced RL network when every branch is resistive
  (`rlNetworkPH_mem_den_globallyExponentiallyStable`); and invariance of every sentence under
  branch rescaling (`rlNetworkPH_scale_mem_den_iff`), the sentence-level form of the
  transformer referral, a diagonal change of coordinates (scaffold `theorem/Similarity.agda`).
* The pointwise KVL/KCL fields, outputs, energies and power balances are static evidence on the
  model; the trajectory transport `rlNetwork_scale_trajectory` is private implementation
  evidence.

Correction (note §1.6.ter "变压器").
* The note states that an ideal `n_T : 1` transformer is equivalent to `L_k → L_k / n_T²`
  together with scaling the incidence column by `1/n_T`, and that the pH structure is
  unchanged. The structure is indeed unchanged (the model is stated for any `𝓑`), but the
  equivalence of the scaled model also requires the branch resistance to scale the same way,
  `r_k → r_k / n_T²`; this is the `c_k = 1 / n_T` case of `rlNetwork_scale_*`.
-/

noncomputable section
namespace powerlib.PH.Models
open Matrix Set
open powerlib.Network (signedIncidence signedIncidence_transpose_mulVec)

variable {β ν : Type*} [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]

/-! ## Signed incidence matrix -/

omit [Fintype ν] [DecidableEq β] in
/-- KCL: `(𝓑 i)_j` is the total current leaving node `j` through the branches. -/
@[powerlib_foundation] theorem signedIncidence_mulVec (tail head : β → ν) (c : β → ℝ) (j : ν) :
    (signedIncidence tail head *ᵥ c) j =
      (∑ k with tail k = j, c k) - ∑ k with head k = j, c k := by
  simp [signedIncidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul,
    Finset.sum_filter, eq_comm]

/-! ## Pure RL network (node potentials as inputs) -/

/-- Branch parameters of an RL network. -/
structure RLBranchParams (β : Type*) where
  L : β → ℝ
  r : β → ℝ
  L_pos : ∀ k, 0 < L k
  r_nonneg : ∀ k, 0 ≤ r k

/-- The RL network as diagonal port-Hamiltonian data: `J = 0`, `R = diag r`, `w = 1/L`,
`B = 𝓑ᵀ`. Inputs: node potentials; outputs: node current injections. -/
def rlNetwork (p : RLBranchParams β) (𝓑 : Matrix ν β ℝ) : DiagonalPH β ν where
  J := 0
  d := p.r
  w := fun k => 1 / p.L k
  B := 𝓑ᵀ
  skew := by simp
  damping_nonneg := p.r_nonneg
  weights_pos := fun k => one_div_pos.mpr (p.L_pos k)

omit [DecidableEq ν] in
/-- Branch equations: `φ̇_k = (𝓑ᵀ v)_k − r_k φ_k / L_k`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlNetwork_field (p : RLBranchParams β) (𝓑 : Matrix ν β ℝ)
    (φ : β → ℝ) (v : ν → ℝ) (k : β) :
    (rlNetwork p 𝓑).field φ v k = (𝓑ᵀ *ᵥ v) k - p.r k * (φ k / p.L k) := by
  simp [DiagonalPH.field, rlNetwork, DiagonalPH.gradient, mulVec_diagonal]
  ring

/-- With the signed incidence matrix the branch equation is KVL around the branch:
`φ̇_k = v(tail k) − v(head k) − r_k i_k`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlNetwork_field_signedIncidence (p : RLBranchParams β)
    (tail head : β → ν) (φ : β → ℝ) (v : ν → ℝ) (k : β) :
    (rlNetwork p (signedIncidence tail head)).field φ v k =
      v (tail k) - v (head k) - p.r k * (φ k / p.L k) := by
  rw [rlNetwork_field, signedIncidence_transpose_mulVec]

omit [DecidableEq β] [Fintype ν] [DecidableEq ν] in
/-- The collocated output is the node current injection `i_node = 𝓑 i_br`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlNetwork_output (p : RLBranchParams β) (𝓑 : Matrix ν β ℝ)
    (φ : β → ℝ) :
    (rlNetwork p 𝓑).output φ = 𝓑 *ᵥ fun k => φ k / p.L k := by
  simp only [DiagonalPH.output, rlNetwork, transpose_transpose]
  congr 1
  ext k
  simp [DiagonalPH.gradient]
  ring

omit [DecidableEq ν] in
/-- Energy check of note §1.6.bis: `Ḣ = i_nodeᵀ v_node − Σ r_k i_k²`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlNetwork_power_balance (p : RLBranchParams β)
    (𝓑 : Matrix ν β ℝ) (φ : β → ℝ) (v : ν → ℝ) :
    (rlNetwork p 𝓑).gradient φ ⬝ᵥ (rlNetwork p 𝓑).field φ v =
      v ⬝ᵥ (𝓑 *ᵥ fun k => φ k / p.L k) - ∑ k, p.r k * (φ k / p.L k) ^ 2 := by
  rw [DiagonalPH.power_balance, DiagonalPH.supply, rlNetwork_output]
  simp only [DiagonalPH.dampingPower, DiagonalPH.gradient, rlNetwork]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ### The numbered RL network and its connection conclusions -/

variable {m k : ℕ}

/-- The RL network with branches `Fin m` and nodes `Fin k`, as a linear port-Hamiltonian plant. -/
def rlNetworkPH (p : RLBranchParams (Fin m)) (𝓑 : Matrix (Fin k) (Fin m) ℝ) :
    Port.PortHamiltonian m k :=
  (rlNetwork p 𝓑).toPH (Equiv.refl _) (Equiv.refl _)

/-- Passivity of every RL network; the storage is `H = Σ φ_k² / (2 L_k)` (`toPH_storage`). -/
@[powerlib_domain] theorem rlNetworkPH_mem_den_passive (p : RLBranchParams (Fin m))
    (𝓑 : Matrix (Fin k) (Fin m) ℝ) :
    connection% (rlNetworkPH p 𝓑 ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- Lyapunov stability of the unforced RL network (all node potentials zero) at the origin. -/
@[powerlib_domain] theorem rlNetworkPH_mem_den_lyapunovStable (p : RLBranchParams (Fin m))
    (𝓑 : Matrix (Fin k) (Fin m) ℝ) :
    connection% (rlNetworkPH p 𝓑 ∈ Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

/-- With a positive resistance in every branch the unforced RL network is globally
exponentially stable. -/
@[powerlib_domain] theorem rlNetworkPH_mem_den_globallyExponentiallyStable
    (p : RLBranchParams (Fin m)) (𝓑 : Matrix (Fin k) (Fin m) ℝ) (hr : ∀ j, 0 < p.r j) :
    connection% (rlNetworkPH p 𝓑 ∈
      Port.PortHamiltonian.family.den (.flow .globallyExponentiallyStable)) :=
  mem_den_globallyExponentiallyStable_of_dissipation_pos _
    (DiagonalPH.toPH_dissipation_pos _ _ _ hr)

/-! ## Branch rescaling (ideal-transformer referral) -/

/-- Branch rescaling by nonzero factors `c`: `L ↦ c² L`, `r ↦ c² r`. -/
def RLBranchParams.scale (p : RLBranchParams β) (c : β → ℝ) (hc : ∀ k, c k ≠ 0) :
    RLBranchParams β where
  L := fun k => c k ^ 2 * p.L k
  r := fun k => c k ^ 2 * p.r k
  L_pos := fun k => mul_pos (by have := hc k; positivity) (p.L_pos k)
  r_nonneg := fun k => mul_nonneg (sq_nonneg _) (p.r_nonneg k)

omit [DecidableEq ν] in
/-- Rescaled branch states obey the rescaled network's equations:
the field of `(c² L, c² r, 𝓑 diag c)` at `c φ` is `c` times the original field. -/
@[powerlib_foundation] theorem rlNetwork_scale_field (p : RLBranchParams β)
    (𝓑 : Matrix ν β ℝ) (c : β → ℝ) (hc : ∀ k, c k ≠ 0) (φ : β → ℝ) (v : ν → ℝ) (k : β) :
    (rlNetwork (p.scale c hc) (𝓑 * diagonal c)).field (fun j => c j * φ j) v k =
      c k * (rlNetwork p 𝓑).field φ v k := by
  rw [rlNetwork_field, rlNetwork_field, transpose_mul, diagonal_transpose, ← mulVec_mulVec,
    mulVec_diagonal]
  have hk := hc k
  have hL := (p.L_pos k).ne'
  simp only [RLBranchParams.scale]
  field_simp

omit [Fintype ν] [DecidableEq ν] in
/-- The rescaled network has the same node port behaviour. -/
@[powerlib_foundation] theorem rlNetwork_scale_output (p : RLBranchParams β)
    (𝓑 : Matrix ν β ℝ) (c : β → ℝ) (hc : ∀ k, c k ≠ 0) (φ : β → ℝ) :
    (rlNetwork (p.scale c hc) (𝓑 * diagonal c)).output (fun j => c j * φ j) =
      (rlNetwork p 𝓑).output φ := by
  rw [rlNetwork_output, rlNetwork_output, ← mulVec_mulVec]
  congr 1
  ext k
  rw [mulVec_diagonal]
  have hk := hc k
  have hL := (p.L_pos k).ne'
  simp only [RLBranchParams.scale]
  field_simp

omit [Fintype ν] [DecidableEq ν] in
/-- The rescaled network stores the same energy. -/
@[powerlib_foundation] theorem rlNetwork_scale_energy (p : RLBranchParams β)
    (𝓑 : Matrix ν β ℝ) (c : β → ℝ) (hc : ∀ k, c k ≠ 0) (φ : β → ℝ) :
    (rlNetwork (p.scale c hc) (𝓑 * diagonal c)).energy (fun j => c j * φ j) =
      (rlNetwork p 𝓑).energy φ := by
  simp only [DiagonalPH.energy, rlNetwork, RLBranchParams.scale]
  apply Finset.sum_congr rfl
  intro k _
  have hk := hc k
  have hL := (p.L_pos k).ne'
  field_simp

omit [Fintype ν] [DecidableEq ν] in
/-- The rescaling is a change of state coordinates `T = diag c`, `S = diag c⁻¹` of the data. -/
@[powerlib_foundation] theorem rlNetwork_scale_similar_data (p : RLBranchParams β)
    (𝓑 : Matrix ν β ℝ) (c : β → ℝ) (hc : ∀ k, c k ≠ 0) :
    (rlNetwork (p.scale c hc) (𝓑 * diagonal c)).stateMatrix =
        diagonal c * (rlNetwork p 𝓑).stateMatrix * diagonal c⁻¹ ∧
      (rlNetwork (p.scale c hc) (𝓑 * diagonal c)).B = diagonal c * (rlNetwork p 𝓑).B ∧
      (rlNetwork (p.scale c hc) (𝓑 * diagonal c)).Bᵀ *
          diagonal (rlNetwork (p.scale c hc) (𝓑 * diagonal c)).w =
        (rlNetwork p 𝓑).Bᵀ * diagonal (rlNetwork p 𝓑).w * diagonal c⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [DiagonalPH.stateMatrix, rlNetwork, RLBranchParams.scale, zero_sub,
      Matrix.neg_mul, Matrix.mul_neg, diagonal_mul_diagonal]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij
      have hk := hc i
      have hL := (p.L_pos i).ne'
      simp only [diagonal_apply_eq, Pi.inv_apply]
      field_simp
    · simp [diagonal_apply_ne _ hij]
  · simp only [rlNetwork, transpose_mul, diagonal_transpose]
  · simp only [rlNetwork, transpose_transpose, RLBranchParams.scale, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij
      have hk := hc i
      have hL := (p.L_pos i).ne'
      simp only [diagonal_apply_eq, Pi.inv_apply]
      field_simp
    · simp [diagonal_apply_ne _ hij]

/-- The branch-rescaling map as a continuous linear map. -/
def rlNetwork_scaleCLM (c : β → ℝ) : (β → ℝ) →L[ℝ] (β → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (diagonal c))

omit [Fintype ν] [DecidableEq ν] in
@[simp, powerlib_foundation] theorem rlNetwork_scaleCLM_apply (c : β → ℝ) (φ : β → ℝ) :
    rlNetwork_scaleCLM c φ = fun j => c j * φ j := by
  ext j
  simp [rlNetwork_scaleCLM, mulVec_diagonal]

/-- Branch rescaling by nonzero factors preserves every sentence: the referred network and the
original network are the same linear port-Hamiltonian plant up to a change of state
coordinates. -/
@[powerlib_domain] theorem rlNetworkPH_scale_mem_den_iff (p : RLBranchParams (Fin m))
    (𝓑 : Matrix (Fin k) (Fin m) ℝ) (c : Fin m → ℝ) (hc : ∀ j, c j ≠ 0) :
    connection% (∀ s : Sentence,
      rlNetworkPH (p.scale c hc) (𝓑 * diagonal c) ∈ Port.PortHamiltonian.family.den s ↔
        rlNetworkPH p 𝓑 ∈ Port.PortHamiltonian.family.den s) := by
  obtain ⟨hA, hB, hC⟩ := rlNetwork_scale_similar_data p 𝓑 c hc
  have hTS : diagonal c * diagonal c⁻¹ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext j
    exact mul_inv_cancel₀ (hc j)
  have hST : diagonal c⁻¹ * diagonal c = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext j
    exact inv_mul_cancel₀ (hc j)
  exact mem_den_iff_of_similar
    (DiagonalPH.toPH_similar _ _ _ _ hTS hST hA hB hC)

/-- The branch-rescaling map of numbered states. -/
private def scaleCLM (c : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (diagonal c)

private theorem ofLp_scaleCLM (c : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    WithLp.ofLp (scaleCLM c x) = fun j => c j * WithLp.ofLp x j := by
  simp only [scaleCLM, Matrix.ofLp_toEuclideanCLM]
  funext j
  exact mulVec_diagonal c _ j

/-- Rescaling any solution segment of the original network gives a solution segment of the
rescaled network driven by the same node potentials, with identical node currents.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem rlNetwork_scale_trajectory (p : RLBranchParams (Fin m))
    (𝓑 : Matrix (Fin k) (Fin m) ℝ) (c : Fin m → ℝ) (hc : ∀ j, c j ≠ 0)
    {u : ℝ → Fin k → ℝ} {x : ℝ → EuclideanSpace ℝ (Fin m)} {t₀ t₁ : ℝ}
    (hx : (rlNetworkPH p 𝓑).plant.system.IsTrajectoryOn u x t₀ t₁) :
    (rlNetworkPH (p.scale c hc) (𝓑 * diagonal c)).plant.system.IsTrajectoryOn u
        (fun t => scaleCLM c (x t)) t₀ t₁ ∧
      ∀ t, (rlNetworkPH (p.scale c hc) (𝓑 * diagonal c)).plant.system.output
          (scaleCLM c (x t)) (u t) = (rlNetworkPH p 𝓑).plant.system.output (x t) (u t) := by
  refine ⟨isTrajectoryOn_map _ _ (scaleCLM c) (fun _ w => w) (fun y w => ?_) hx, fun t => ?_⟩
  · apply WithLp.ofLp_injective
    funext j
    rw [rlNetworkPH, rlNetworkPH, ofLp_scaleCLM, DiagonalPH.toPH_field, DiagonalPH.toPH_field,
      ofLp_scaleCLM]
    simpa using (rlNetwork_scale_field p 𝓑 c hc (WithLp.ofLp y) w j).symm
  · rw [rlNetworkPH, rlNetworkPH, DiagonalPH.toPH_output, DiagonalPH.toPH_output, ofLp_scaleCLM]
    simpa using congrArg (· ∘ (Equiv.refl (Fin k)).symm)
      (rlNetwork_scale_output p 𝓑 c hc (WithLp.ofLp (x t)))

/-! ## RL network with node capacitors and shunt conductances -/

/-- Node parameters: capacitance to ground `C_i > 0` and shunt conductance `G_i ≥ 0`. -/
structure NodeParams (ν : Type*) where
  C : ν → ℝ
  G : ν → ℝ
  C_pos : ∀ i, 0 < C i
  G_nonneg : ∀ i, 0 ≤ G i

/-- RL network with node capacitors (note §1.6.ter) on the state `β ⊕ ν = (φ, q)`.
`J = [[0, 𝓑ᵀ], [−𝓑, 0]]`, `R = diag(r, G)`, `w = (1/L, 1/C)`, inputs are node current
injections, `B = [0; I]`. -/
def rlcNetwork (p : RLBranchParams β) (q : NodeParams ν) (𝓑 : Matrix ν β ℝ) :
    DiagonalPH (β ⊕ ν) ν where
  J := fromBlocks 0 𝓑ᵀ (-𝓑) 0
  d := Sum.elim p.r q.G
  w := Sum.elim (fun k => 1 / p.L k) (fun i => 1 / q.C i)
  B := fromRows 0 1
  skew := by
    rw [fromBlocks_transpose, fromBlocks_neg]
    simp
  damping_nonneg := by
    rintro (k | i)
    · exact p.r_nonneg k
    · exact q.G_nonneg i
  weights_pos := by
    rintro (k | i)
    · exact one_div_pos.mpr (p.L_pos k)
    · exact one_div_pos.mpr (q.C_pos i)

/-- Branch equations with node capacitors: `φ̇_k = (𝓑ᵀ v)_k − r_k i_k`, `v = q / C`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlcNetwork_field_branch (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) (u : ν → ℝ) (k : β) :
    (rlcNetwork p q 𝓑).field x u (Sum.inl k) =
      (𝓑ᵀ *ᵥ fun i => x (Sum.inr i) / q.C i) k - p.r k * (x (Sum.inl k) / p.L k) := by
  simp [DiagonalPH.field, rlcNetwork, DiagonalPH.gradient, sub_mulVec,
    mulVec_diagonal, fromBlocks_mulVec, Function.comp_def, ← fromBlocks_diagonal]
  simp only [mulVec, dotProduct, transpose_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

/-- Node equations (KCL with capacitor and shunt): `q̇_j = u_j − (𝓑 i_br)_j − G_j v_j`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlcNetwork_field_node (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) (u : ν → ℝ) (j : ν) :
    (rlcNetwork p q 𝓑).field x u (Sum.inr j) =
      u j - (𝓑 *ᵥ fun k => x (Sum.inl k) / p.L k) j - q.G j * (x (Sum.inr j) / q.C j) := by
  simp [DiagonalPH.field, rlcNetwork, DiagonalPH.gradient, sub_mulVec,
    mulVec_diagonal, fromBlocks_mulVec, Function.comp_def, ← fromBlocks_diagonal]
  simp only [mulVec, dotProduct, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have h : ∑ k, 𝓑 j k * ((p.L k)⁻¹ * x (Sum.inl k)) = ∑ k, 𝓑 j k * (x (Sum.inl k) / p.L k) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  ring

omit [DecidableEq β] in
/-- The collocated output is the node voltage `v_j = q_j / C_j`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlcNetwork_output (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) :
    (rlcNetwork p q 𝓑).output x = fun j => x (Sum.inr j) / q.C j := by
  ext j
  simp [DiagonalPH.output, rlcNetwork, DiagonalPH.gradient, mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]
  ring

/-- Power balance with node capacitors: `Ḣ = Σ u_j v_j − Σ r_k i_k² − Σ G_j v_j²`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rlcNetwork_power_balance (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) (u : ν → ℝ) :
    (rlcNetwork p q 𝓑).gradient x ⬝ᵥ (rlcNetwork p q 𝓑).field x u =
      ∑ j, u j * (x (Sum.inr j) / q.C j) - ∑ k, p.r k * (x (Sum.inl k) / p.L k) ^ 2 -
        ∑ j, q.G j * (x (Sum.inr j) / q.C j) ^ 2 := by
  rw [DiagonalPH.power_balance, DiagonalPH.supply, rlcNetwork_output]
  simp only [DiagonalPH.dampingPower, DiagonalPH.gradient, rlcNetwork,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have h1 : ∀ k, p.r k * (1 / p.L k * x (Sum.inl k)) ^ 2 = p.r k * (x (Sum.inl k) / p.L k) ^ 2 :=
    fun k => by ring
  have h2 : ∀ j, q.G j * (1 / q.C j * x (Sum.inr j)) ^ 2 = q.G j * (x (Sum.inr j) / q.C j) ^ 2 :=
    fun j => by ring
  simp only [h1, h2, dotProduct]
  ring

/-- The RL network with node capacitors, with branches `Fin m` and nodes `Fin k`, as a linear
port-Hamiltonian plant on the state `(φ, q)` numbered by `finSumFinEquiv`. -/
def rlcNetworkPH (p : RLBranchParams (Fin m)) (q : NodeParams (Fin k))
    (𝓑 : Matrix (Fin k) (Fin m) ℝ) : Port.PortHamiltonian (m + k) k :=
  (rlcNetwork p q 𝓑).toPH finSumFinEquiv (Equiv.refl _)

/-- Passivity of the RL network with node capacitors and shunt loads; the storage is the
magnetic plus electric energy (`toPH_storage`). -/
@[powerlib_domain] theorem rlcNetworkPH_mem_den_passive (p : RLBranchParams (Fin m))
    (q : NodeParams (Fin k)) (𝓑 : Matrix (Fin k) (Fin m) ℝ) :
    connection% (rlcNetworkPH p q 𝓑 ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- Lyapunov stability of the unforced network (zero injections) at the origin. -/
@[powerlib_domain] theorem rlcNetworkPH_mem_den_lyapunovStable (p : RLBranchParams (Fin m))
    (q : NodeParams (Fin k)) (𝓑 : Matrix (Fin k) (Fin m) ℝ) :
    connection% (rlcNetworkPH p q 𝓑 ∈
      Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

end powerlib.PH.Models
