import theorem.Network.WeightedLaplacian
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.ODE.ExistUnique
import LeanForControl.LinearSystems.Stability.Continuous.DefsHurwitz

/-! # Synchronization manifolds of diffusively coupled identical nodes

Foundation layer (categories B and C).

Source: work-sync `theory/T-synchronization-manifold.md` §1.1 (network
`ẋᵢ = f(xᵢ) − σ Σⱼ Lᵢⱼ H(xⱼ)`, `L𝟙 = 0`), §1.2 (invariance of `M_sync`), §1.3 (variational
equation decoupled by the Laplacian spectrum), §1.5 (linear-node threshold `σ μ₂ > a`), §1.6
(cluster synchronization under an equitable partition).

Model boundary: `N` identical nodes indexed by a finite type `ι`, node state in a real normed
space `E`, node dynamics `f : E → E`, coupling output `H : E → E`, coupling matrix `L` with zero
row sums (`Σⱼ Lᵢⱼ = 0`, e.g. a weighted Laplacian), coupling strength `σ`; continuous time,
autonomous, deterministic. No delay, sampling or heterogeneity.

Results.
* C (Mathlib wrappers for the unweighted Laplacian `SimpleGraph.lapMatrix`): `L𝟙 = 0`, positive
  semidefinite, kernel = vectors constant on connected components, `dim ker L = #components`;
  bridge `G.lapMatrix ℝ = Network.laplacian (G.adjMatrix ℝ)`.
* `netField_diag`: on the diagonal the network field is `f` in every node (tangency);
  `sync_lift`: a node solution `s` gives the network solution `(s, …, s)`;
  `sync_invariant`: if the network field is globally Lipschitz, every network solution that
  starts on `M_sync` stays on it (it equals `(s, …, s)`; Mathlib `ODE_solution_unique_univ`).
* `variational_decouple`: for `δẊᵢ = A(t) δXᵢ − σ Σⱼ Lᵢⱼ Γ(t) δXⱼ` and any matrix `W` of left
  eigenvectors (`W L = diag(μ) W`; for symmetric `L`, `W = Vᵀ` with `L = VΛVᵀ`), the modal
  coordinates `ξ_k = Σᵢ W_{ki} δXᵢ` obey `ξ̇_k = (A(t) − σ μ_k Γ(t)) ξ_k`.
* `isHurwitz_sub_smul_one`, `transverse_isHurwitz_of_threshold`: with `H = Γ = I`, every
  transverse block `A − σμ_k I` (`k ≥ 2`) is Hurwitz as soon as `σ μ_k > a` where `a` bounds the
  real parts of the spectrum of `A` — in particular for all `k` once `σ μ₂ > a`, `σ ≥ 0`.
* Cluster synchronization (`EquitablePartition`, `cluster_field`, `cluster_lift`,
  `cluster_invariant`): if every node of cluster `c` receives the same total coupling `Q c c'`
  from cluster `c'`, the cluster manifold `{X = Y ∘ π}` is invariant and carries the quotient
  dynamics `Ẏ_c = f(Y_c) − σ Σ_{c'} Q_{cc'} H(Y_{c'})`.

Not formalized here: Master Stability Function / Lyapunov exponents, Kuramoto `K_c`, Fenichel
persistence (near-identical nodes) — these are outside the algebraic/ODE core.
-/

noncomputable section
namespace powerlib.Network.Sync
open Matrix Finset

/-! ## Unweighted graph Laplacian (Mathlib wrappers) -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `L𝟙 = 0` (wraps `SimpleGraph.lapMatrix_mulVec_one_eq_zero`). -/
@[powerlib_foundation] theorem lapMatrix_mulVec_one : G.lapMatrix ℝ *ᵥ 1 = 0 :=
  G.lapMatrix_mulVec_one_eq_zero ℝ

/-- `L ⪰ 0` (wraps `SimpleGraph.posSemidef_lapMatrix`). -/
@[powerlib_foundation] theorem lapMatrix_posSemidef : (G.lapMatrix ℝ).PosSemidef :=
  SimpleGraph.posSemidef_lapMatrix ℝ G

/-- `L x = 0` iff `x` is constant on connected components
(wraps `SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable`). -/
@[powerlib_foundation] theorem lapMatrix_mulVec_eq_zero_iff (x : V → ℝ) :
    G.lapMatrix ℝ *ᵥ x = 0 ↔ ∀ i j, G.Reachable i j → x i = x j :=
  G.lapMatrix_mulVec_eq_zero_iff_forall_reachable

/-- For a connected graph the kernel of `L` is spanned by `𝟙`. -/
@[powerlib_foundation] theorem lapMatrix_mulVec_eq_zero_iff_const (hG : G.Connected) (x : V → ℝ) :
    G.lapMatrix ℝ *ᵥ x = 0 ↔ ∀ i j, x i = x j := by
  rw [lapMatrix_mulVec_eq_zero_iff]
  exact ⟨fun h i j => h i j (hG.preconnected i j), fun h i j _ => h i j⟩

/-- `dim ker L` equals the number of connected components
(wraps `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`). -/
@[powerlib_foundation] theorem card_components_eq_finrank_ker :
    Fintype.card G.ConnectedComponent = Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker :=
  G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix

/-- The unweighted Laplacian is the weighted Laplacian of the 0/1 adjacency weights. -/
@[powerlib_foundation] theorem lapMatrix_eq_laplacian :
    G.lapMatrix ℝ = Network.laplacian (G.adjMatrix ℝ) := by
  have hdeg : ∀ i, ∑ j, G.adjMatrix ℝ i j = G.degree i := by
    intro i
    have := G.adjMatrix_mulVec_const_apply (α := ℝ) (a := 1) (v := i)
    simpa [mulVec, dotProduct] using this
  ext i j
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Network.laplacian, Matrix.sub_apply,
    diagonal_apply, hdeg]

end Graph

/-! ## Network of identical nodes and the synchronization manifold -/

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Network field `Fᵢ(X) = f(Xᵢ) − σ Σⱼ Lᵢⱼ H(Xⱼ)`. -/
def netField (f H : E → E) (L : Matrix ι ι ℝ) (σ : ℝ) (X : ι → E) : ι → E :=
  fun i => f (X i) - σ • ∑ j, L i j • H (X j)

/-- Zero row sums (`L𝟙 = 0`). -/
def RowSumZero (L : Matrix ι ι ℝ) : Prop := ∀ i, ∑ j, L i j = 0

/-- **Tangency**: on the diagonal every node evolves by `f`. -/
@[powerlib_foundation] theorem netField_diag {f H : E → E} {L : Matrix ι ι ℝ} (hL : RowSumZero L)
    (σ : ℝ) (x : E) : netField f H L σ (fun _ => x) = fun _ => f x := by
  funext i
  simp only [netField]
  rw [← Finset.sum_smul, hL i, zero_smul, smul_zero, sub_zero]

/-- A solution of the isolated node lifts to the synchronized network solution. -/
@[powerlib_foundation] theorem sync_lift {f H : E → E} {L : Matrix ι ι ℝ} (hL : RowSumZero L)
    (σ : ℝ) {s : ℝ → E} (hs : ∀ t, HasDerivAt s (f (s t)) t) (t : ℝ) :
    HasDerivAt (fun τ => fun _ : ι => s τ) (netField f H L σ (fun _ => s t)) t := by
  rw [netField_diag hL]
  exact hasDerivAt_pi.mpr fun _ => hs t

/-- **Invariance of `M_sync`** (globally Lipschitz network field): a network solution starting
at `(s(0), …, s(0))` equals `(s(t), …, s(t))` for all `t`. -/
@[powerlib_foundation] theorem sync_invariant {f H : E → E} {L : Matrix ι ι ℝ} (hL : RowSumZero L)
    {σ : ℝ} {K : NNReal} (hF : LipschitzWith K (netField f H L σ)) {s : ℝ → E}
    (hs : ∀ t, HasDerivAt s (f (s t)) t) {X : ℝ → ι → E}
    (hX : ∀ t, HasDerivAt X (netField f H L σ (X t)) t) (h0 : X 0 = fun _ => s 0) :
    ∀ t i, X t i = s t := by
  have heq : X = fun τ => fun _ : ι => s τ :=
    ODE_solution_unique_univ (v := fun _ => netField f H L σ) (s := fun _ => Set.univ) (t₀ := 0)
      (fun _ => hF.lipschitzOnWith) (fun t => ⟨hX t, trivial⟩)
      (fun t => ⟨sync_lift hL σ hs t, trivial⟩) h0
  intro t i
  rw [heq]

/-! ## Variational equation: decoupling by the Laplacian spectrum -/

/-- **Modal decoupling**: if `W L = diag(μ) W`, then `ξ_k = Σᵢ W_{ki} δXᵢ` satisfies
`ξ̇_k = (A(t) − σ μ_k Γ(t)) ξ_k` along every solution of the variational equation. -/
@[powerlib_foundation] theorem variational_decouple {d : ℕ} {L W : Matrix ι ι ℝ} {μ : ι → ℝ}
    [DecidableEq ι] (hW : W * L = diagonal μ * W) (σ : ℝ) (A Γ : ℝ → Matrix (Fin d) (Fin d) ℝ)
    {δX : ℝ → ι → Fin d → ℝ}
    (hX : ∀ t, HasDerivAt δX (fun i => A t *ᵥ δX t i - σ • ∑ j, L i j • (Γ t *ᵥ δX t j)) t)
    (t : ℝ) :
    HasDerivAt (fun τ => fun k => ∑ i, W k i • δX τ i)
      (fun k => (A t - (σ * μ k) • Γ t) *ᵥ ∑ i, W k i • δX t i) t := by
  apply hasDerivAt_pi.mpr
  intro k
  have hi : ∀ i, HasDerivAt (fun τ => δX τ i)
      (A t *ᵥ δX t i - σ • ∑ j, L i j • (Γ t *ᵥ δX t j)) t :=
    fun i => (hasDerivAt_pi.mp (hX t)) i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hi i).const_smul (W k i)
  convert hsum using 1
  -- algebra: Σᵢ W_{ki}(A δXᵢ − σ Σⱼ L_{ij} Γ δXⱼ) = (A − σ μ_k Γ) Σᵢ W_{ki} δXᵢ
  have hWL : ∀ j, ∑ i, W k i * L i j = μ k * W k j := by
    intro j
    have := congrFun (congrFun hW k) j
    rw [Matrix.diagonal_mul, Matrix.mul_apply] at this
    exact this
  rw [sub_mulVec, mulVec_sum, smul_mulVec, mulVec_sum]
  simp only [mulVec_smul, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [show σ * μ k * W k j = σ * (μ k * W k j) by ring, ← hWL j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Linear nodes: the transverse blocks and the threshold `σ μ₂ > a` -/

/-- Shifting by `c I` shifts the spectrum: if every eigenvalue of `A` has real part `< c`,
then `A − c I` is Hurwitz. -/
@[powerlib_foundation] theorem isHurwitz_sub_smul_one {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    {c : ℝ} (h : ∀ (lam : ℂ) (v : Fin d → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = lam • v →
      lam.re < c) : LinearSystems.IsHurwitz (A - c • 1) := by
  intro lam v hv heig
  have hmap : (A - c • (1 : Matrix (Fin d) (Fin d) ℝ)).map (algebraMap ℝ ℂ) =
      A.map (algebraMap ℝ ℂ) - (c : ℂ) • 1 := by
    ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
  rw [hmap, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_iff_eq_add, ← add_smul] at heig
  have := h _ v hv heig
  simp only [Complex.add_re, Complex.ofReal_re] at this
  simp only [neg_zero]
  linarith

/-- **Threshold `σ μ_k > a`**: with `H = Γ = I`, if every eigenvalue of `A` has real part
`≤ a` and `σ μ_k > a`, the transverse block `A − σ μ_k I` is Hurwitz. If `0 ≤ σ`, the eigenvalues
are ordered `μ₂ ≤ μ_k`, and `σ μ₂ > a`, this holds for every transverse mode. -/
@[powerlib_foundation] theorem transverse_isHurwitz_of_threshold {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} {a σ μ2 μk : ℝ}
    (ha : ∀ (lam : ℂ) (v : Fin d → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = lam • v →
      lam.re ≤ a) (hσ : 0 ≤ σ) (hμ : μ2 ≤ μk) (hthr : a < σ * μ2) :
    LinearSystems.IsHurwitz (A - (σ * μk) • 1) := by
  apply isHurwitz_sub_smul_one
  intro lam v hv heig
  have := ha lam v hv heig
  have : σ * μ2 ≤ σ * μk := mul_le_mul_of_nonneg_left hμ hσ
  linarith

/-! ## Cluster synchronization under an equitable partition -/

section Cluster

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `π : ι → κ` is equitable for `L` with quotient matrix `Q`: every node of cluster `c`
receives total coupling `Q c c'` from cluster `c'`. -/
def EquitablePartition (L : Matrix ι ι ℝ) (π : ι → κ) (Q : Matrix κ κ ℝ) : Prop :=
  ∀ i c, ∑ j ∈ Finset.univ.filter (fun j => π j = c), L i j = Q (π i) c

/-- Quotient (cluster) field `Ẏ_c = f(Y_c) − σ Σ_{c'} Q_{cc'} H(Y_{c'})`. -/
def quotField (f H : E → E) (Q : Matrix κ κ ℝ) (σ : ℝ) (Y : κ → E) : κ → E :=
  fun c => f (Y c) - σ • ∑ c', Q c c' • H (Y c')

/-- On the cluster manifold the network field is the lifted quotient field. -/
@[powerlib_foundation] theorem cluster_field {f H : E → E} {L : Matrix ι ι ℝ} {π : ι → κ}
    {Q : Matrix κ κ ℝ} (hπ : EquitablePartition L π Q) (σ : ℝ) (Y : κ → E) :
    netField f H L σ (Y ∘ π) = quotField f H Q σ Y ∘ π := by
  funext i
  simp only [netField, quotField, Function.comp_apply]
  congr 2
  rw [← Finset.sum_fiberwise Finset.univ π (fun j => L i j • H (Y (π j)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hπ i c, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.mp hj).2]

/-- A quotient solution lifts to a cluster-synchronized network solution. -/
@[powerlib_foundation] theorem cluster_lift {f H : E → E} {L : Matrix ι ι ℝ} {π : ι → κ}
    {Q : Matrix κ κ ℝ} (hπ : EquitablePartition L π Q) (σ : ℝ) {Y : ℝ → κ → E}
    (hY : ∀ t, HasDerivAt Y (quotField f H Q σ (Y t)) t) (t : ℝ) :
    HasDerivAt (fun τ => Y τ ∘ π) (netField f H L σ (Y t ∘ π)) t := by
  rw [cluster_field hπ]
  exact hasDerivAt_pi.mpr fun i => (hasDerivAt_pi.mp (hY t)) (π i)

/-- **Invariance of the cluster manifold** (globally Lipschitz network field). -/
@[powerlib_foundation] theorem cluster_invariant {f H : E → E} {L : Matrix ι ι ℝ} {π : ι → κ}
    {Q : Matrix κ κ ℝ} (hπ : EquitablePartition L π Q) {σ : ℝ} {K : NNReal}
    (hF : LipschitzWith K (netField f H L σ)) {Y : ℝ → κ → E}
    (hY : ∀ t, HasDerivAt Y (quotField f H Q σ (Y t)) t) {X : ℝ → ι → E}
    (hX : ∀ t, HasDerivAt X (netField f H L σ (X t)) t) (h0 : X 0 = Y 0 ∘ π) :
    ∀ t, X t = Y t ∘ π := by
  have heq : X = fun τ => Y τ ∘ π :=
    ODE_solution_unique_univ (v := fun _ => netField f H L σ) (s := fun _ => Set.univ) (t₀ := 0)
      (fun _ => hF.lipschitzOnWith) (fun t => ⟨hX t, trivial⟩)
      (fun t => ⟨cluster_lift hπ σ hY t, trivial⟩) h0
  intro t
  rw [heq]

/-- Complete synchronization is the one-cluster case: zero row sums make the trivial partition
equitable with `Q = 0`. -/
@[powerlib_foundation] theorem equitable_trivial {L : Matrix ι ι ℝ} (hL : RowSumZero L) :
    EquitablePartition L (fun _ => ()) (0 : Matrix Unit Unit ℝ) := by
  intro i c
  simp [hL i]

end Cluster

end powerlib.Network.Sync
