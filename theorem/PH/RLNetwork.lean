import theorem.PortHamiltonian

/-! # Lumped RL networks (with optional node capacitors) as port-Hamiltonian systems

Model boundary.
* Topology: a finite directed multigraph with node type `ν` and branch type `β`
  (`Fintype`, `DecidableEq`). The signed incidence matrix `signedIncidence tail head :
  Matrix ν β ℝ` has entry `+1` at the tail of a branch (branch current leaves the node),
  `−1` at the head, `0` otherwise (a self-loop gives a zero column). Mathlib's `incMatrix`
  is unsigned and is not used. Every model below is stated for an **arbitrary** real matrix
  `𝓑 : Matrix ν β ℝ`, so weighted (ideal-transformer) incidence columns are included.
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
* Branch rescaling (transformer form): rescaling branch states by nonzero factors `c_k`
  maps the network `(L, r, 𝓑)` to `(c² L, c² r, 𝓑 · diag c)`, with the same node port
  behaviour and the same energy.
  Correction (note §1.6.ter "变压器"): the note states that an ideal `n_T : 1` transformer
  is equivalent to `L_k → L_k / n_T²` together with scaling the incidence column by `1/n_T`,
  and that the pH structure is unchanged. The structure is indeed unchanged (the model is
  stated for any `𝓑`), but the equivalence of the scaled model also requires the branch
  resistance to scale the same way, `r_k → r_k / n_T²`; this is the `c_k = 1 / n_T` case
  of `rlNetwork_scale_*`.
* Results are pointwise power balances, trajectory-level passivity (`PassiveWithStorage`) and
  Lyapunov stability of the unforced origin. Nothing is claimed about a particular grid.

Source: work-sync `theory/T-ph.md` §1.6.bis (RL network pH form and energy check),
§1.6.ter (node capacitors, transformers, constant-impedance loads).
-/

noncomputable section
namespace powerlib.PH
open Matrix Set

variable {β ν : Type*} [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]

/-! ## Signed incidence matrix -/

/-- Signed node–branch incidence matrix: `+1` if branch `k` leaves node `i` (tail),
`−1` if it enters node `i` (head). -/
def signedIncidence (tail head : β → ν) : Matrix ν β ℝ :=
  Matrix.of fun i k => (if i = tail k then 1 else 0) - (if i = head k then 1 else 0)

omit [Fintype β] [DecidableEq β] in
/-- KVL: the branch voltage `(𝓑ᵀ v)_k` is the potential difference `v(tail k) − v(head k)`. -/
@[powerlib_foundation] theorem signedIncidence_transpose_mulVec (tail head : β → ν)
    (v : ν → ℝ) (k : β) :
    ((signedIncidence tail head)ᵀ *ᵥ v) k = v (tail k) - v (head k) := by
  simp [signedIncidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

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

/-- The RL network as a port-Hamiltonian model: `J = 0`, `R = diag r`, `w = 1/L`,
`B = 𝓑ᵀ`. Inputs: node potentials; outputs: node current injections. -/
def rlNetwork (p : RLBranchParams β) (𝓑 : Matrix ν β ℝ) : PortHamiltonian.Model β ν where
  J := 0
  d := p.r
  w := fun k => 1 / p.L k
  B := 𝓑ᵀ
  skew := by simp
  damping_nonneg := p.r_nonneg
  weights_pos := fun k => one_div_pos.mpr (p.L_pos k)

omit [DecidableEq ν] in
/-- Branch equations: `φ̇_k = (𝓑ᵀ v)_k − r_k φ_k / L_k`. -/
@[powerlib_domain] theorem rlNetwork_field (p : RLBranchParams β) (𝓑 : Matrix ν β ℝ)
    (φ : β → ℝ) (v : ν → ℝ) (k : β) :
    PortHamiltonian.field (rlNetwork p 𝓑) φ v k = (𝓑ᵀ *ᵥ v) k - p.r k * (φ k / p.L k) := by
  simp [PortHamiltonian.field, rlNetwork, PortHamiltonian.gradient, mulVec_diagonal]
  ring

/-- With the signed incidence matrix the branch equation is KVL around the branch:
`φ̇_k = v(tail k) − v(head k) − r_k i_k`. -/
@[powerlib_domain] theorem rlNetwork_field_signedIncidence (p : RLBranchParams β)
    (tail head : β → ν) (φ : β → ℝ) (v : ν → ℝ) (k : β) :
    PortHamiltonian.field (rlNetwork p (signedIncidence tail head)) φ v k =
      v (tail k) - v (head k) - p.r k * (φ k / p.L k) := by
  rw [rlNetwork_field, signedIncidence_transpose_mulVec]

omit [DecidableEq β] [Fintype ν] [DecidableEq ν] in
/-- The collocated output is the node current injection `i_node = 𝓑 i_br`. -/
@[powerlib_domain] theorem rlNetwork_output (p : RLBranchParams β) (𝓑 : Matrix ν β ℝ)
    (φ : β → ℝ) :
    PortHamiltonian.output (rlNetwork p 𝓑) φ = 𝓑 *ᵥ fun k => φ k / p.L k := by
  simp only [PortHamiltonian.output, rlNetwork, transpose_transpose]
  congr 1
  ext k
  simp [PortHamiltonian.gradient]
  ring

omit [DecidableEq ν] in
/-- Energy check of note §1.6.bis: `Ḣ = i_nodeᵀ v_node − Σ r_k i_k²`. -/
@[powerlib_domain] theorem rlNetwork_power_balance (p : RLBranchParams β) (𝓑 : Matrix ν β ℝ)
    (φ : β → ℝ) (v : ν → ℝ) :
    dotProduct (PortHamiltonian.gradient (rlNetwork p 𝓑) φ)
        (PortHamiltonian.field (rlNetwork p 𝓑) φ v) =
      v ⬝ᵥ (𝓑 *ᵥ fun k => φ k / p.L k) - ∑ k, p.r k * (φ k / p.L k) ^ 2 := by
  rw [PortHamiltonian.power_balance]
  simp only [Passivity.supply, PortHamiltonian.system]
  rw [rlNetwork_output]
  simp only [PortHamiltonian.dampingPower, PortHamiltonian.gradient, rlNetwork, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ν] in
/-- Passivity of every RL network with storage `H = Σ φ_k² / (2 L_k)`. -/
@[powerlib_domain] theorem rlNetwork_passiveWithStorage (p : RLBranchParams β)
    (𝓑 : Matrix ν β ℝ) :
    Passivity.PassiveWithStorage (PortHamiltonian.system (rlNetwork p 𝓑))
      (PortHamiltonian.energy (rlNetwork p 𝓑)) :=
  PortHamiltonian.passiveWithStorage (rlNetwork p 𝓑)

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
    PortHamiltonian.field (rlNetwork (p.scale c hc) (𝓑 * diagonal c)) (fun j => c j * φ j) v k =
      c k * PortHamiltonian.field (rlNetwork p 𝓑) φ v k := by
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
    PortHamiltonian.output (rlNetwork (p.scale c hc) (𝓑 * diagonal c)) (fun j => c j * φ j) =
      PortHamiltonian.output (rlNetwork p 𝓑) φ := by
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
    PortHamiltonian.energy (rlNetwork (p.scale c hc) (𝓑 * diagonal c)) (fun j => c j * φ j) =
      PortHamiltonian.energy (rlNetwork p 𝓑) φ := by
  simp only [PortHamiltonian.energy, rlNetwork, RLBranchParams.scale]
  apply Finset.sum_congr rfl
  intro k _
  have hk := hc k
  have hL := (p.L_pos k).ne'
  field_simp

/-- The branch-rescaling map as a continuous linear map. -/
def rlNetwork_scaleCLM (c : β → ℝ) : (β → ℝ) →L[ℝ] (β → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (diagonal c))

@[simp, powerlib_foundation] theorem rlNetwork_scaleCLM_apply (c : β → ℝ) (φ : β → ℝ) :
    rlNetwork_scaleCLM c φ = fun j => c j * φ j := by
  ext j
  simp [rlNetwork_scaleCLM, mulVec_diagonal]

omit [DecidableEq ν] in
/-- Trajectory transport: rescaling any trajectory of the original network gives a trajectory
of the rescaled network driven by the same node potentials, with identical node currents. -/
@[powerlib_domain] theorem rlNetwork_scale_trajectory (p : RLBranchParams β)
    (𝓑 : Matrix ν β ℝ) (c : β → ℝ) (hc : ∀ k, c k ≠ 0)
    {u : ℝ → (ν → ℝ)} {x : ℝ → (β → ℝ)}
    (hx : Passivity.IsTrajectory (PortHamiltonian.system (rlNetwork p 𝓑)) u x) :
    Passivity.IsTrajectory (PortHamiltonian.system (rlNetwork (p.scale c hc) (𝓑 * diagonal c)))
        u (fun t j => c j * x t j) ∧
      ∀ t, PortHamiltonian.output (rlNetwork (p.scale c hc) (𝓑 * diagonal c))
          (fun j => c j * x t j) = PortHamiltonian.output (rlNetwork p 𝓑) (x t) := by
  refine ⟨fun t ht => ?_, fun t => rlNetwork_scale_output p 𝓑 c hc (x t)⟩
  have h := (rlNetwork_scaleCLM c).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
  simp only [Function.comp_def, rlNetwork_scaleCLM_apply] at h
  convert h using 1
  ext k
  exact rlNetwork_scale_field p 𝓑 c hc (x t) (u t) k

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
    PortHamiltonian.Model (β ⊕ ν) ν where
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

/-- Branch equations with node capacitors: `φ̇_k = (𝓑ᵀ v)_k − r_k i_k`, `v = q / C`. -/
@[powerlib_domain] theorem rlcNetwork_field_branch (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) (u : ν → ℝ) (k : β) :
    PortHamiltonian.field (rlcNetwork p q 𝓑) x u (Sum.inl k) =
      (𝓑ᵀ *ᵥ fun i => x (Sum.inr i) / q.C i) k - p.r k * (x (Sum.inl k) / p.L k) := by
  simp [PortHamiltonian.field, rlcNetwork, PortHamiltonian.gradient, sub_mulVec,
    mulVec_diagonal, fromBlocks_mulVec, Function.comp_def, ← fromBlocks_diagonal]
  simp only [mulVec, dotProduct, transpose_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

/-- Node equations (KCL with capacitor and shunt): `q̇_j = u_j − (𝓑 i_br)_j − G_j v_j`. -/
@[powerlib_domain] theorem rlcNetwork_field_node (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) (u : ν → ℝ) (j : ν) :
    PortHamiltonian.field (rlcNetwork p q 𝓑) x u (Sum.inr j) =
      u j - (𝓑 *ᵥ fun k => x (Sum.inl k) / p.L k) j - q.G j * (x (Sum.inr j) / q.C j) := by
  simp [PortHamiltonian.field, rlcNetwork, PortHamiltonian.gradient, sub_mulVec,
    mulVec_diagonal, fromBlocks_mulVec, Function.comp_def, ← fromBlocks_diagonal]
  simp only [mulVec, dotProduct, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have h : ∑ k, 𝓑 j k * ((p.L k)⁻¹ * x (Sum.inl k)) = ∑ k, 𝓑 j k * (x (Sum.inl k) / p.L k) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  ring

omit [DecidableEq β] in
/-- The collocated output is the node voltage `v_j = q_j / C_j`. -/
@[powerlib_domain] theorem rlcNetwork_output (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) :
    PortHamiltonian.output (rlcNetwork p q 𝓑) x = fun j => x (Sum.inr j) / q.C j := by
  ext j
  simp [PortHamiltonian.output, rlcNetwork, PortHamiltonian.gradient, mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]
  ring

/-- Power balance with node capacitors: `Ḣ = Σ u_j v_j − Σ r_k i_k² − Σ G_j v_j²`. -/
@[powerlib_domain] theorem rlcNetwork_power_balance (p : RLBranchParams β) (q : NodeParams ν)
    (𝓑 : Matrix ν β ℝ) (x : β ⊕ ν → ℝ) (u : ν → ℝ) :
    dotProduct (PortHamiltonian.gradient (rlcNetwork p q 𝓑) x)
        (PortHamiltonian.field (rlcNetwork p q 𝓑) x u) =
      ∑ j, u j * (x (Sum.inr j) / q.C j) - ∑ k, p.r k * (x (Sum.inl k) / p.L k) ^ 2 -
        ∑ j, q.G j * (x (Sum.inr j) / q.C j) ^ 2 := by
  rw [PortHamiltonian.power_balance]
  simp only [Passivity.supply, PortHamiltonian.system]
  rw [rlcNetwork_output]
  simp only [PortHamiltonian.dampingPower, PortHamiltonian.gradient, rlcNetwork,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have h1 : ∀ k, p.r k * (1 / p.L k * x (Sum.inl k)) ^ 2 = p.r k * (x (Sum.inl k) / p.L k) ^ 2 :=
    fun k => by ring
  have h2 : ∀ j, q.G j * (1 / q.C j * x (Sum.inr j)) ^ 2 = q.G j * (x (Sum.inr j) / q.C j) ^ 2 :=
    fun j => by ring
  simp only [h1, h2]
  ring

/-- Passivity of the RL network with node capacitors and shunt loads. -/
@[powerlib_domain] theorem rlcNetwork_passiveWithStorage (p : RLBranchParams β)
    (q : NodeParams ν) (𝓑 : Matrix ν β ℝ) :
    Passivity.PassiveWithStorage (PortHamiltonian.system (rlcNetwork p q 𝓑))
      (PortHamiltonian.energy (rlcNetwork p q 𝓑)) :=
  PortHamiltonian.passiveWithStorage (rlcNetwork p q 𝓑)

/-- Lyapunov stability of the unforced network (zero injections) at the origin. -/
@[powerlib_domain] theorem rlcNetwork_lyapunovStable [Nonempty β] (p : RLBranchParams β)
    (q : NodeParams ν) (𝓑 : Matrix ν β ℝ) :
    Passivity.LyapunovStable (PortHamiltonian.system (rlcNetwork p q 𝓑)) :=
  PortHamiltonian.lyapunovStable (rlcNetwork p q 𝓑)

end powerlib.PH
