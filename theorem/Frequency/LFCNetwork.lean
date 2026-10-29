import theorem.Frequency.LFC
import theorem.Network.WeightedLaplacian
import theorem.LTI.Decay

/-! # Multi-area load-frequency control on a tie-line graph

The `N`-area LFC/AGC model on an arbitrary tie-line graph as a linear family: the
non-interactive steady state, the zero mode of meshed graphs, and a gain condition that makes
every radial graph exponentially stable (including the two-area model of `Frequency.LFC`).

Model boundary.
* Same per-area model as `Frequency.LFC.plant` (continuous-time, linear, Kundur per-unit,
  governors instantaneous `T_g → 0`, one coherent machine per area, AGC integral on the
  tie-line-bias ACE, no dead-band / limits / HVDC / voltage dynamics), for a finite set `α` of
  areas and a finite set `β` of tie lines, coupled by an arbitrary real matrix
  `𝓑 : Matrix α β ℝ`; the intended case is the signed incidence matrix
  `Network.signedIncidence tail head` of the directed tie-line graph (`+1` at the sending area).
* State index `α ⊕ (β ⊕ α)`: `inl a` = `Δω_a`, `inr (inl ℓ)` = line flow `ΔP_tie,ℓ`
  (from `tail ℓ` to `head ℓ`), `inr (inr a)` = `ΔP_C,a`. Input `ΔP_L : α → ℝ`.
* Equations: `M_a Δω̇_a = ΔP_C,a − K_R,a Δω_a − ΔP_L,a − D_a Δω_a − (𝓑 ΔP_tie)_a`;
  `ΔṖ_tie,ℓ = ω_s T_ℓ (𝓑ᵀ Δω)_ℓ`; `ΔṖ_C,a = −K_I,a ((𝓑 ΔP_tie)_a + B_a Δω_a)`.

Source: work-sync `theory/T-load-frequency-control.md` §1.1–§1.6 and the last paragraph of §1.7
("进一步推广到 `N_a` 区 … `(3 N_a + N_t)` 维").

Results.
* `netModel_card` (foundation): the state dimension is `2 N_a + N_t`.
* `netField x u = netA x + netB u` is the field under the constant loads `u`.
* `netModel_isEquilibrium_iff` (foundation, static, §1.6 for `N_a` areas): if the tie-line graph
  is connected (`ker 𝓑ᵀ` = constants), every column of `𝓑` sums to zero, `Σ_a B_a ≠ 0`,
  `K_I,a ≠ 0`, `ω_s T_ℓ ≠ 0`, `M_a ≠ 0`, then the equilibria are exactly
  `Δω = 0`, net tie exports `𝓑 ΔP_tie = 0`, `ΔP_C,a = ΔP_L,a` (non-interactive control).
  `signedIncidence_isEquilibrium_iff` instantiates this for the signed incidence matrix of a
  connected graph (`TieConnected`); `isEquilibrium_iff_of_ker` gives the unique equilibrium
  `(0, 0, ΔP_L)` when `𝓑` has trivial kernel (radial tie-line graph).
* `netModel_not_spectrallyStable` (foundation), `triangle_not_spectrallyStable`: if `𝓑`
  has a nonzero kernel vector (a loop in the tie-line graph, e.g. three areas in a ring) the
  line-flow state matrix is singular (a circulating flow is a zero mode), so the model is
  **never** asymptotically stable, for any gains.
* `LTI.tendsto_of_spectrallyStable` (foundation, any matrices on a finite index type, by
  transport to `Fin N`; `theorem/LTI/Decay.lean`) and `netModel_tendsto` (private): on a radial
  tie-line graph, a spectrally stable state matrix (explicit premise) makes every trajectory
  under constant loads converge to `(0, 0, ΔP_L)`.
* Gain condition (foundation, static; a sufficient condition in place of the missing parametric
  Routh–Hurwitz condition, holding for every tie-line strength and every radial topology):
  `netA_spectrallyStable_of_gain` — if `𝓑` has trivial kernel (radial graph), every area has
  `M_a, K_I,a, B_a > 0` and **`K_I,a M_a ≤ D_a + K_R,a`**, and every line has `ω_s T_ℓ > 0`, the
  state matrix is spectrally stable. Proof: in the coordinates `ξ_a = ΔP_C,a − K_I,a M_a Δω_a`
  the tie-line flows drop out of the AGC rows (`netXi_mulVec`: `ξ̇ = K_I (g − B) Δω − K_I ξ`,
  `g = D + K_R − K_I M ≥ 0`); the storage
  `E = Σ M Δω² + Σ ΔP_tie²/(ω_s T) + Σ ξ²/(K_I (g + B))` (`netEnergy`) has
  `E(z, A z) = −Σ ((ξ − g Δω)² + g B Δω²)/(g + B)` for every state `z` (`netEnergy_mulVec`, the
  tie-line terms cancel by `𝓑`/`𝓑ᵀ` duality); a real eigen-pair with nonnegative real part
  (`LTI.spectrallyStable_of_real_pairs`) must then have `ξ = 0`, `Δω = 0` (AGC rows), zero net
  exports (frequency rows) and zero line flows (trivial kernel). `plant_A_eq_reindex`,
  `plant_isHurwitz_of_gain`: the five-state two-area matrix of `Frequency.LFC` is this matrix
  for two areas and one line (`𝓑 = (1, −1)ᵀ`), relabelled, so the same condition makes it
  Hurwitz. Only sufficiency is claimed (the exact two-area condition would be the fifth-order
  Hurwitz-determinant list, not formalized); the condition involves neither the tie-line
  coefficients nor the size of the frequency bias.

Family and connection conclusions.
* System map: an `N`-area model (`NetModel α β`: areas, `ω_s`, line coefficients, coupling
  matrix) is read as the port system of its plant, the line-flow realization transported to
  `Fin (card (α ⊕ (β ⊕ α)))` states and `Fin (card α)` load ports along `Fintype.equivFin`
  (`NetModel.plant`, `Family.IsLinear`); port output the area frequencies. Since the steady
  state of a constant load is an equilibrium, the flow sentences about the origin are the
  sentences about that steady state in deviation coordinates.
* Requirements: the matrix language of `Frequency.LFC` (`hurwitz`, `rhpRoot`, `rate a`) on the
  transported state matrix, with the same translation; soundness and exactness are the generic
  `LFC.sound_of_meetsMatrix`, `LFC.exact_of_meetsMatrix`.
* Connection theorems, for `Fin N_a` areas and `Fin N_t` lines (the claim grammar quantifies
  over data, not over index types): `net_chain_le_semantics`, `net_exact_hurwitz`,
  `net_mem_den_globallyExponentiallyStable` (spectral stability of `netA`, explicit static
  premise), `net_not_mem_den_attractive` (a loop in the tie-line graph excludes every attractive
  sentence, for any gains) and `triangle_not_mem_den_attractive`. Parametric connection
  conclusions: `net_mem_den_of_gain` (`N` areas, radial graph, gain condition ⇒ every
  attractive sentence and sampled contraction) and `mem_den_of_gain` (the two-area family
  `Frequency.LFC.family` under the same condition, replacing the Hurwitz premise of
  `LFC.mem_den_globallyExponentiallyStable`).
* The equilibrium characterizations and spectral statements are static evidence
  (`@[powerlib_foundation]`); `LTI.tendsto_of_spectrallyStable` is a generic implication about
  arbitrary matrices (foundation). Private implementation evidence (trajectory level, Rules
  §3a): `netModel_tendsto`.

Corrections.
* §1.7 dimension: with `T_g → 0` (the simplification used for §1.7) the state dimension is
  `2 N_a + N_t` (`netModel_card`); the note's `3 N_a + N_t` counts one governor state per area
  that the §1.7 model has eliminated.
* Meshed graphs: line flows are not independent states on a meshed graph
  (`netModel_not_spectrallyStable`); a stable realization must use area angles or a spanning
  tree.
-/

noncomputable section
namespace powerlib.Frequency.LFC
open Set Filter Matrix LinearSystems TMIO
open scoped Topology

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]

/-- State matrix of the `N`-area model. -/
def netA (area : α → Area) (ωs : ℝ) (T : β → ℝ) (𝓑 : Matrix α β ℝ) :
    Matrix (α ⊕ (β ⊕ α)) (α ⊕ (β ⊕ α)) ℝ :=
  fun i j => match i, j with
  | .inl a, .inl c => if a = c then -((area a).D + (area a).K) / (area a).M else 0
  | .inl a, .inr (.inl ℓ) => -𝓑 a ℓ / (area a).M
  | .inl a, .inr (.inr c) => if a = c then 1 / (area a).M else 0
  | .inr (.inl ℓ), .inl c => ωs * T ℓ * 𝓑 c ℓ
  | .inr (.inl _), .inr _ => 0
  | .inr (.inr a), .inl c => if a = c then -((area a).KI * (area a).B) else 0
  | .inr (.inr a), .inr (.inl ℓ) => -((area a).KI * 𝓑 a ℓ)
  | .inr (.inr _), .inr (.inr _) => 0

/-- Input matrix: the load step `ΔP_L,a` enters the swing row of area `a` as `−1/M_a`. -/
def netB (area : α → Area) : Matrix (α ⊕ (β ⊕ α)) α ℝ :=
  fun i c => match i with
  | .inl a => if a = c then -1 / (area a).M else 0
  | .inr _ => 0

/-- Output matrix: the area frequencies. -/
def netC : Matrix α (α ⊕ (β ⊕ α)) ℝ :=
  fun c i => match i with
  | .inl a => if c = a then 1 else 0
  | .inr _ => 0

/-- The field `netA x + netB u` of the `N`-area model under the constant loads `u`. -/
def netField (area : α → Area) (ωs : ℝ) (T : β → ℝ) (𝓑 : Matrix α β ℝ)
    (x : α ⊕ (β ⊕ α) → ℝ) (u : α → ℝ) : α ⊕ (β ⊕ α) → ℝ :=
  netA area ωs T 𝓑 *ᵥ x + netB area *ᵥ u

omit [DecidableEq α] in
/-- Correction (dimension): `2 N_a + N_t` states once `T_g → 0`. -/
@[tmio T, powerlib_foundation] theorem netModel_card :
    Fintype.card (α ⊕ (β ⊕ α)) = 2 * Fintype.card α + Fintype.card β := by
  simp only [Fintype.card_sum]
  ring

variable (α β) in
/-- An `N`-area LFC model on the tie-line graph with coupling matrix `𝓑`. -/
structure NetModel where
  area : α → Area
  ωs : ℝ
  T : β → ℝ
  𝓑 : Matrix α β ℝ

/-- The plant of an `N`-area model: the line-flow realization transported to `Fin` indices. -/
def NetModel.plant (m : NetModel α β) :
    Linear.Plant (Fintype.card (α ⊕ (β ⊕ α))) (Fintype.card α) where
  A := (netA m.area m.ωs m.T m.𝓑).reindex (Fintype.equivFin _) (Fintype.equivFin _)
  B := (netB m.area).reindex (Fintype.equivFin _) (Fintype.equivFin α)
  C := (netC : Matrix α (α ⊕ (β ⊕ α)) ℝ).reindex (Fintype.equivFin α) (Fintype.equivFin _)
  D := 0

variable (α β) in
/-- The `N`-area LFC family: every model read as the port system of its transported plant, with
the matrix requirement language of `Frequency.LFC`. -/
def netFamily :
    Family (NetModel α β) Requirement (Fintype.card (α ⊕ (β ⊕ α))) (Fintype.card α) :=
  ⟨fun m => m.plant.system, fun m => MeetsMatrix m.plant.A, translate⟩

@[powerlib_foundation] theorem netFamily_isLinear :
    (netFamily α β).IsLinear NetModel.plant := fun _ => rfl

/-- The transported state matrix is Hurwitz exactly when `netA` is spectrally stable. -/
@[powerlib_foundation] theorem netModel_isHurwitz_iff [DecidableEq β] (m : NetModel α β) :
    IsHurwitz m.plant.A ↔ Linear.SpectrallyStable (netA m.area m.ωs m.T m.𝓑) :=
  (Linear.spectrallyStable_iff_isHurwitz _).symm.trans (Linear.spectrallyStable_reindex _ _)


variable {area : α → Area} {ωs : ℝ} {T : β → ℝ} {𝓑 : Matrix α β ℝ}

/-- Swing row of area `a`. -/
@[powerlib_foundation] theorem netField_freq (x : α ⊕ (β ⊕ α) → ℝ) (u : α → ℝ) (a : α) :
    netField area ωs T 𝓑 x u (.inl a) =
      (-((area a).D + (area a).K) * x (.inl a) - ∑ ℓ, 𝓑 a ℓ * x (.inr (.inl ℓ)) +
        x (.inr (.inr a)) - u a) / (area a).M := by
  simp only [netField, Pi.add_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, netA, netB, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sub_div, add_div, sub_div, Finset.sum_div]
  have : ∀ ℓ, -𝓑 a ℓ / (area a).M * x (.inr (.inl ℓ)) =
      -(𝓑 a ℓ * x (.inr (.inl ℓ)) / (area a).M) :=
    fun ℓ => by ring
  simp only [this, Finset.sum_neg_distrib]
  ring

/-- Tie-line rows: `ΔṖ_tie,ℓ = ω_s T_ℓ (𝓑ᵀ Δω)_ℓ`. -/
@[powerlib_foundation] theorem netField_tie (x : α ⊕ (β ⊕ α) → ℝ) (u : α → ℝ) (ℓ : β) :
    netField area ωs T 𝓑 x u (.inr (.inl ℓ)) =
      ωs * T ℓ * ∑ c, 𝓑 c ℓ * x (.inl c) := by
  simp only [netField, Pi.add_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, netA, netB, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- AGC rows: `ΔṖ_C,a = −K_I,a ((𝓑 ΔP_tie)_a + B_a Δω_a)`. -/
@[powerlib_foundation] theorem netField_agc (x : α ⊕ (β ⊕ α) → ℝ) (u : α → ℝ) (a : α) :
    netField area ωs T 𝓑 x u (.inr (.inr a)) =
      -(area a).KI * (∑ ℓ, 𝓑 a ℓ * x (.inr (.inl ℓ)) + (area a).B * x (.inl a)) := by
  simp only [netField, Pi.add_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, netA, netB, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, mul_add, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun ℓ _ => by ring
  · ring

/-- §1.6 for `N` areas (non-interactive control) under connectivity of the tie-line graph.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem netModel_isEquilibrium_iff (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (hcol : ∀ ℓ, ∑ a, 𝓑 a ℓ = 0)
    (hconn : ∀ w : α → ℝ, (∀ ℓ, ∑ c, 𝓑 c ℓ * w c = 0) → ∀ a c, w a = w c)
    (u : α → ℝ) (e : α ⊕ (β ⊕ α) → ℝ) :
    netField area ωs T 𝓑 e u = 0 ↔
      (∀ a, e (.inl a) = 0) ∧ (∀ a, ∑ ℓ, 𝓑 a ℓ * e (.inr (.inl ℓ)) = 0) ∧
        ∀ a, e (.inr (.inr a)) = u a := by
  constructor
  · intro h
    have hf := fun a => congrFun h (.inl a)
    have ht := fun ℓ => congrFun h (.inr (.inl ℓ))
    have hc := fun a => congrFun h (.inr (.inr a))
    simp only [netField_freq, netField_tie, netField_agc, Pi.zero_apply] at hf ht hc
    -- tie rows: `𝓑ᵀ Δω = 0`, so `Δω` is constant
    have hω : ∀ ℓ, ∑ c, 𝓑 c ℓ * e (.inl c) = 0 := fun ℓ =>
      (mul_eq_zero.1 (ht ℓ)).resolve_left (hT ℓ)
    have hconst := hconn (fun c => e (.inl c)) hω
    -- AGC rows: `(𝓑 p)_a = −B_a Δω_a`
    have hace : ∀ a, ∑ ℓ, 𝓑 a ℓ * e (.inr (.inl ℓ)) + (area a).B * e (.inl a) = 0 :=
      fun a => (mul_eq_zero.1 (hc a)).resolve_left (neg_ne_zero.2 (hKI a))
    -- summing: the net exports cancel
    have hsum : ∑ a, ∑ ℓ, 𝓑 a ℓ * e (.inr (.inl ℓ)) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun ℓ _ => ?_
      rw [← Finset.sum_mul, hcol ℓ, zero_mul]
    have hω0 : ∀ a, e (.inl a) = 0 := by
      intro a
      have h1 : ∑ c, (area c).B * e (.inl c) = 0 := by
        have := Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hace c
        rw [Finset.sum_add_distrib, hsum, zero_add, Finset.sum_const_zero] at this
        exact this
      have h2 : ∑ c, (area c).B * e (.inl c) = (∑ c, (area c).B) * e (.inl a) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by rw [hconst c a]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1).resolve_left hB
    have hp : ∀ a, ∑ ℓ, 𝓑 a ℓ * e (.inr (.inl ℓ)) = 0 := fun a => by
      have := hace a; rw [hω0 a, mul_zero, add_zero] at this; exact this
    refine ⟨hω0, hp, fun a => ?_⟩
    have := hf a
    rw [hω0 a, hp a, div_eq_zero_iff] at this
    rcases this with h' | h'
    · linarith
    · exact absurd h' (hM a)
  · rintro ⟨hω0, hp, hc⟩
    funext i
    rcases i with a | ℓ | a
    · rw [netField_freq, hω0, hp, hc]; simp
    · rw [netField_tie]; simp [hω0]
    · rw [netField_agc, hp, hω0]; simp

/-- The non-interactive steady state `(0, 0, ΔP_L)`. -/
def netSteadyState (u : α → ℝ) : α ⊕ (β ⊕ α) → ℝ :=
  Sum.elim (fun _ => (0 : ℝ)) (Sum.elim (fun _ => (0 : ℝ)) u)

/-- The steady state `(0, 0, ΔP_L)` is an equilibrium of every constant load, for every
parameter value. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem netSteadyState_isEquilibrium (u : α → ℝ) :
    netField area ωs T 𝓑 (netSteadyState u) u = 0 := by
  funext i
  rcases i with a | ℓ | a
  · rw [netField_freq]; simp [netSteadyState]
  · rw [netField_tie]; simp [netSteadyState]
  · rw [netField_agc]; simp [netSteadyState]

/-- Radial tie-line graph (`ker 𝓑 = 0`): the unique equilibrium is `(0, 0, ΔP_L)`. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem isEquilibrium_iff_of_ker (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (hcol : ∀ ℓ, ∑ a, 𝓑 a ℓ = 0)
    (hconn : ∀ w : α → ℝ, (∀ ℓ, ∑ c, 𝓑 c ℓ * w c = 0) → ∀ a c, w a = w c)
    (hker : ∀ p : β → ℝ, 𝓑 *ᵥ p = 0 → p = 0) (u : α → ℝ) (e : α ⊕ (β ⊕ α) → ℝ) :
    netField area ωs T 𝓑 e u = 0 ↔ e = netSteadyState u := by
  rw [netModel_isEquilibrium_iff hM hKI hT hB hcol hconn]
  constructor
  · rintro ⟨hω, hp, hc⟩
    have hp0 := hker (fun ℓ => e (.inr (.inl ℓ))) (funext fun a => by
      simpa [mulVec, dotProduct] using hp a)
    funext i
    rcases i with a | ℓ | a
    · simp [netSteadyState, hω]
    · simpa [netSteadyState] using congrFun hp0 ℓ
    · simp [netSteadyState, hc]
  · rintro rfl
    simp [netSteadyState]

/-! ## Signed incidence matrix of a connected tie-line graph -/

/-- The tie-line graph is connected: any two areas are joined by a chain of lines (either
direction). -/
def TieConnected (tail head : β → α) : Prop :=
  ∀ a c, Relation.ReflTransGen
    (fun x y => ∃ ℓ, (tail ℓ = x ∧ head ℓ = y) ∨ (tail ℓ = y ∧ head ℓ = x)) a c

omit [Fintype β] in
@[powerlib_foundation] theorem signedIncidence_const_of_connected {tail head : β → α}
    (hconn : TieConnected tail head) (w : α → ℝ)
    (hw : ∀ ℓ, ∑ c, Network.signedIncidence tail head c ℓ * w c = 0) (a c : α) : w a = w c := by
  have hedge : ∀ ℓ, w (tail ℓ) = w (head ℓ) := by
    intro ℓ
    have h := Network.signedIncidence_transpose_mulVec tail head w ℓ
    have h' : ((Network.signedIncidence tail head)ᵀ *ᵥ w) ℓ = 0 := by
      simpa [mulVec, dotProduct] using hw ℓ
    linarith
  induction hconn a c with
  | refl => rfl
  | tail _ hxy ih =>
    obtain ⟨ℓ, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hxy
    · rw [ih, ← h1, ← h2, hedge ℓ]
    · rw [ih, ← h1, ← h2, hedge ℓ]

/-- §1.6 for `N` areas on a connected tie-line graph with signed incidence matrix. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem signedIncidence_isEquilibrium_iff {tail head : β → α}
    (hconn : TieConnected tail head) (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (u : α → ℝ) (e : α ⊕ (β ⊕ α) → ℝ) :
    netField area ωs T (Network.signedIncidence tail head) e u = 0 ↔
      (∀ a, e (.inl a) = 0) ∧
        (∀ a, ∑ ℓ, Network.signedIncidence tail head a ℓ * e (.inr (.inl ℓ)) = 0) ∧
        ∀ a, e (.inr (.inr a)) = u a :=
  netModel_isEquilibrium_iff hM hKI hT hB (Network.signedIncidence_col_sum tail head)
    (signedIncidence_const_of_connected hconn) u e

/-! ## Meshed tie-line graphs: circulating flows -/

/-- A kernel vector `p` of `𝓑` (a circulating flow) is a zero mode of the state matrix. -/
@[powerlib_foundation] theorem netA_mulVec_circulation {p : β → ℝ} (hp : 𝓑 *ᵥ p = 0) :
    netA area ωs T 𝓑 *ᵥ Sum.elim 0 (Sum.elim p 0) = 0 := by
  have hp' : ∀ a, ∑ ℓ, 𝓑 a ℓ * p ℓ = 0 := fun a => by
    simpa [mulVec, dotProduct] using congrFun hp a
  funext i
  rcases i with a | ℓ | a
  · simp only [mulVec, dotProduct, Fintype.sum_sum_type, netA, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    have : ∑ ℓ, -𝓑 a ℓ / (area a).M * p ℓ = -(∑ ℓ, 𝓑 a ℓ * p ℓ) / (area a).M := by
      rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    rw [this, hp' a]; simp
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, netA]
  · simp only [mulVec, dotProduct, Fintype.sum_sum_type, netA, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
    have : ∑ ℓ, -((area a).KI * 𝓑 a ℓ) * p ℓ = -(area a).KI * ∑ ℓ, 𝓑 a ℓ * p ℓ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    rw [this, hp' a]; simp

/-- Correction: if the tie-line graph has a loop (a nonzero `p` with `𝓑 p = 0`), the
line-flow realization never belongs to the family denotation of global exponential
stability, whatever the gains. -/
@[tmio TM, powerlib_foundation] theorem netModel_not_spectrallyStable [DecidableEq β] {p : β → ℝ}
    (hp0 : p ≠ 0) (hp : 𝓑 *ᵥ p = 0) :
    connection% ((⟨area, ωs, T, 𝓑⟩ : NetModel α β) ∉ (netFamily α β).den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% netFamily_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) (x := (⟨area, ωs, T, 𝓑⟩ : NetModel α β))).trans (netModel_isHurwitz_iff (⟨area, ωs, T, 𝓑⟩ : NetModel α β))]
  change ¬ Linear.SpectrallyStable (netA area ωs T 𝓑)
  intro hs
  have hv : (Sum.elim 0 (Sum.elim p 0) : α ⊕ (β ⊕ α) → ℝ) ≠ 0 := by
    intro h
    apply hp0
    funext ℓ
    simpa using congrFun h (.inr (.inl ℓ))
  have hdet : (netA area ωs T 𝓑).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hv, netA_mulVec_circulation hp⟩
  have h0 : (Linear.characteristicMatrix (netA area ωs T 𝓑) 0).det = 0 := by
    have : Linear.characteristicMatrix (netA area ωs T 𝓑) 0 =
        -(netA area ωs T 𝓑).map (algebraMap ℝ ℂ) := by
      simp [Linear.characteristicMatrix]
      rfl
    rw [this, Matrix.det_neg, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
    simp
  have := hs 0 h0
  simp at this

/-- Three areas in a ring: the circulating flow `(1, 1, 1)` is in the kernel of the signed
incidence matrix. -/
@[powerlib_foundation] theorem triangle_circulation :
    Network.signedIncidence (![0, 1, 2] : Fin 3 → Fin 3) ![1, 2, 0] *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  funext a
  fin_cases a <;>
    simp only [Network.signedIncidence, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Pi.zero_apply] <;> norm_num

/-- Three areas in a ring (`1 → 2 → 3 → 1`): the line-flow LFC model is not spectrally stable
for any parameters. A negative membership in the family denotation. -/
@[tmio TM, powerlib_foundation] theorem triangle_not_spectrallyStable (area : Fin 3 → Area) (ωs : ℝ)
    (T : Fin 3 → ℝ) :
    connection% ((⟨area, ωs, T, Network.signedIncidence (![0, 1, 2] : Fin 3 → Fin 3) ![1, 2, 0]⟩ : NetModel (Fin 3) (Fin 3)) ∉ (netFamily (Fin 3) (Fin 3)).den (.flow .globallyExponentiallyStable)) :=
  netModel_not_spectrallyStable (p := fun _ => 1) (fun h => by simpa using congrFun h 0)
    triangle_circulation

/-! ## Gain condition: a parametric stability certificate on radial graphs -/

/-- Margin `g_a = D_a + K_R,a − K_I,a M_a` of the gain condition. -/
def netGap (area : α → Area) (a : α) : ℝ := (area a).D + (area a).K - (area a).KI * (area a).M

/-- AGC deviation `ξ_a = ΔP_C,a − K_I,a M_a Δω_a` of a state vector. -/
def netXi (area : α → Area) (z : α ⊕ (β ⊕ α) → ℝ) (a : α) : ℝ :=
  z (.inr (.inr a)) - (area a).KI * (area a).M * z (.inl a)

/-- Bilinear storage `Σ M ω ω' + Σ P P'/(ω_s T) + Σ ξ ξ'/(K_I (g + B))`. -/
def netEnergy (area : α → Area) (ωs : ℝ) (T : β → ℝ) (z₁ z₂ : α ⊕ (β ⊕ α) → ℝ) : ℝ :=
  (∑ a, (area a).M * z₁ (.inl a) * z₂ (.inl a)) +
    (∑ ℓ, z₁ (.inr (.inl ℓ)) * z₂ (.inr (.inl ℓ)) / (ωs * T ℓ)) +
    ∑ a, netXi area z₁ a * netXi area z₂ a / ((area a).KI * (netGap area a + (area a).B))

/-- Dissipation `Σ ((ξ − g ω)² + g B ω²)/(g + B)`. -/
def netDiss (area : α → Area) (z : α ⊕ (β ⊕ α) → ℝ) : ℝ :=
  ∑ a, ((netXi area z a - netGap area a * z (.inl a)) ^ 2 +
    netGap area a * (area a).B * z (.inl a) ^ 2) / (netGap area a + (area a).B)

@[powerlib_foundation] theorem netA_mulVec_freq (z : α ⊕ (β ⊕ α) → ℝ) (a : α) :
    (netA area ωs T 𝓑 *ᵥ z) (.inl a) =
      (-((area a).D + (area a).K) * z (.inl a) - ∑ ℓ, 𝓑 a ℓ * z (.inr (.inl ℓ)) +
        z (.inr (.inr a))) / (area a).M := by
  have h := netField_freq (area := area) (ωs := ωs) (T := T) (𝓑 := 𝓑) z 0 a
  simpa [netField] using h

@[powerlib_foundation] theorem netA_mulVec_tie (z : α ⊕ (β ⊕ α) → ℝ) (ℓ : β) :
    (netA area ωs T 𝓑 *ᵥ z) (.inr (.inl ℓ)) = ωs * T ℓ * ∑ c, 𝓑 c ℓ * z (.inl c) := by
  have h := netField_tie (area := area) (ωs := ωs) (T := T) (𝓑 := 𝓑) z 0 ℓ
  simpa [netField] using h

@[powerlib_foundation] theorem netA_mulVec_agc (z : α ⊕ (β ⊕ α) → ℝ) (a : α) :
    (netA area ωs T 𝓑 *ᵥ z) (.inr (.inr a)) =
      -(area a).KI * (∑ ℓ, 𝓑 a ℓ * z (.inr (.inl ℓ)) + (area a).B * z (.inl a)) := by
  have h := netField_agc (area := area) (ωs := ωs) (T := T) (𝓑 := 𝓑) z 0 a
  simpa [netField] using h

/-- AGC deviation of `A z`: `ξ(A z) = K_I (g − B) ω − K_I ξ`. -/
@[powerlib_foundation] theorem netXi_mulVec (hM : ∀ a, (area a).M ≠ 0) (z : α ⊕ (β ⊕ α) → ℝ)
    (a : α) :
    netXi area (netA area ωs T 𝓑 *ᵥ z) a =
      (area a).KI * (netGap area a - (area a).B) * z (.inl a) - (area a).KI * netXi area z a := by
  rw [netXi, netA_mulVec_freq, netA_mulVec_agc, netXi, netGap]
  field_simp [hM a]
  ring

/-- **Energy identity**: `E(z, A z) = −Diss(z)` for every state vector `z`. -/
@[powerlib_foundation] theorem netEnergy_mulVec (hM : ∀ a, (area a).M ≠ 0)
    (hK : ∀ a, (area a).KI ≠ 0) (hgB : ∀ a, netGap area a + (area a).B ≠ 0)
    (hw : ∀ ℓ, ωs * T ℓ ≠ 0) (z : α ⊕ (β ⊕ α) → ℝ) :
    netEnergy area ωs T z (netA area ωs T 𝓑 *ᵥ z) = -netDiss area z := by
  have htie : ∑ ℓ, z (.inr (.inl ℓ)) * (netA area ωs T 𝓑 *ᵥ z) (.inr (.inl ℓ)) / (ωs * T ℓ) =
      ∑ a, z (.inl a) * ∑ ℓ, 𝓑 a ℓ * z (.inr (.inl ℓ)) := by
    simp_rw [netA_mulVec_tie, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ℓ _ => ?_
    rw [div_eq_iff (hw ℓ)]
    ring
  unfold netEnergy netDiss
  rw [htie, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [netA_mulVec_freq, netXi_mulVec hM]
  have hgB' := hgB a
  have hK' := hK a
  have hM' := hM a
  have hd : (area a).D + (area a).K = netGap area a + (area a).KI * (area a).M := by
    unfold netGap; ring
  rw [hd]
  unfold netXi
  generalize netGap area a = g at hgB' ⊢
  field_simp
  ring

omit [Fintype α] [DecidableEq α] [Fintype β] in
@[powerlib_foundation] theorem netXi_combo (c d : ℝ) (z₁ z₂ : α ⊕ (β ⊕ α) → ℝ) (a : α) :
    netXi area (c • z₁ + d • z₂) a = c * netXi area z₁ a + d * netXi area z₂ a := by
  simp only [netXi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype α] [DecidableEq α] [Fintype β] in
@[powerlib_foundation] theorem netXi_sub (c d : ℝ) (z₁ z₂ : α ⊕ (β ⊕ α) → ℝ) (a : α) :
    netXi area (c • z₁ - d • z₂) a = c * netXi area z₁ a - d * netXi area z₂ a := by
  simp only [netXi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq α] in
/-- The storage is linear in its second argument. -/
@[powerlib_foundation] theorem netEnergy_combo (c d : ℝ) (z z₁ z₂ : α ⊕ (β ⊕ α) → ℝ) :
    netEnergy area ωs T z (c • z₁ + d • z₂) =
      c * netEnergy area ωs T z z₁ + d * netEnergy area ωs T z z₂ := by
  unfold netEnergy
  simp only [netXi_combo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ a, (area a).M * z (.inl a) * (c * z₁ (.inl a) + d * z₂ (.inl a))) =
      c * (∑ a, (area a).M * z (.inl a) * z₁ (.inl a)) +
        d * ∑ a, (area a).M * z (.inl a) * z₂ (.inl a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : (∑ ℓ, z (.inr (.inl ℓ)) * (c * z₁ (.inr (.inl ℓ)) + d * z₂ (.inr (.inl ℓ))) /
      (ωs * T ℓ)) = c * (∑ ℓ, z (.inr (.inl ℓ)) * z₁ (.inr (.inl ℓ)) / (ωs * T ℓ)) +
        d * ∑ ℓ, z (.inr (.inl ℓ)) * z₂ (.inr (.inl ℓ)) / (ωs * T ℓ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h3 : (∑ a, netXi area z a * (c * netXi area z₁ a + d * netXi area z₂ a) /
      ((area a).KI * (netGap area a + (area a).B))) =
      c * (∑ a, netXi area z a * netXi area z₁ a / ((area a).KI * (netGap area a + (area a).B))) +
        d * ∑ a, netXi area z a * netXi area z₂ a /
          ((area a).KI * (netGap area a + (area a).B)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h1, h2, h3]
  ring

omit [DecidableEq α] in
@[powerlib_foundation] theorem netEnergy_sub (c d : ℝ) (z z₁ z₂ : α ⊕ (β ⊕ α) → ℝ) :
    netEnergy area ωs T z (c • z₁ - d • z₂) =
      c * netEnergy area ωs T z z₁ - d * netEnergy area ωs T z z₂ := by
  rw [sub_eq_add_neg, ← neg_smul, netEnergy_combo]
  ring

omit [DecidableEq α] in
/-- The storage is symmetric. -/
@[powerlib_foundation] theorem netEnergy_comm (z₁ z₂ : α ⊕ (β ⊕ α) → ℝ) :
    netEnergy area ωs T z₁ z₂ = netEnergy area ωs T z₂ z₁ := by
  simp only [netEnergy]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun a _ => by ring
    · exact Finset.sum_congr rfl fun ℓ _ => by ring
  · exact Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq α] in
/-- The storage is nonnegative under positive inertia, AGC gain, `g + B` and line coefficients. -/
@[powerlib_foundation] theorem netEnergy_nonneg (hM : ∀ a, 0 ≤ (area a).M)
    (hK : ∀ a, 0 < (area a).KI) (hgB : ∀ a, 0 < netGap area a + (area a).B)
    (hw : ∀ ℓ, 0 < ωs * T ℓ) (z : α ⊕ (β ⊕ α) → ℝ) : 0 ≤ netEnergy area ωs T z z := by
  unfold netEnergy
  refine add_nonneg (add_nonneg (Finset.sum_nonneg fun a _ => ?_) (Finset.sum_nonneg fun ℓ _ => ?_))
    (Finset.sum_nonneg fun a _ => ?_)
  · have := hM a; rw [mul_assoc]; exact mul_nonneg this (mul_self_nonneg _)
  · exact div_nonneg (mul_self_nonneg _) (hw ℓ).le
  · exact div_nonneg (mul_self_nonneg _) (mul_pos (hK a) (hgB a)).le

omit [Fintype α] [DecidableEq α] [Fintype β] in
/-- The dissipation is nonnegative under `g ≥ 0`, `B > 0`. -/
@[powerlib_foundation] theorem netDiss_term_nonneg (hg : ∀ a, 0 ≤ netGap area a)
    (hB : ∀ a, 0 < (area a).B) (z : α ⊕ (β ⊕ α) → ℝ) (a : α) :
    0 ≤ ((netXi area z a - netGap area a * z (.inl a)) ^ 2 +
      netGap area a * (area a).B * z (.inl a) ^ 2) / (netGap area a + (area a).B) := by
  have := hg a; have := hB a
  positivity

omit [DecidableEq α] [Fintype β] in
/-- A vanishing dissipation forces `ξ = 0` and `g ω = 0` in every area. -/
@[powerlib_foundation] theorem netDiss_eq_zero (hg : ∀ a, 0 ≤ netGap area a)
    (hB : ∀ a, 0 < (area a).B) {z : α ⊕ (β ⊕ α) → ℝ} (h : netDiss area z = 0) (a : α) :
    netXi area z a = 0 ∧ netGap area a * z (.inl a) = 0 := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => netDiss_term_nonneg hg hB z a).mp h a
    (Finset.mem_univ a)
  have hpos : 0 < netGap area a + (area a).B := add_pos_of_nonneg_of_pos (hg a) (hB a)
  rw [div_eq_zero_iff, or_iff_left hpos.ne'] at hterm
  have hB' := hB a
  have hg' := hg a
  have h1 : (netXi area z a - netGap area a * z (.inl a)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (netXi area z a - netGap area a * z (.inl a)),
      mul_nonneg (mul_nonneg hg' hB'.le) (sq_nonneg (z (.inl a)))]
  have h2 : netGap area a * (area a).B * z (.inl a) ^ 2 = 0 := by
    nlinarith [sq_nonneg (netXi area z a - netGap area a * z (.inl a)),
      mul_nonneg (mul_nonneg hg' hB'.le) (sq_nonneg (z (.inl a)))]
  have h3 : netGap area a * z (.inl a) = 0 := by
    have : (netGap area a * z (.inl a)) * z (.inl a) * (area a).B = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · rw [h, mul_zero]
    · exact absurd h hB'.ne'
  have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  exact ⟨by linear_combination h4 + h3, h3⟩

/-- **Gain condition, `N` areas on a radial tie-line graph.** If every area has `M_a, K_I,a,
B_a > 0` and `K_I,a M_a ≤ D_a + K_R,a`, every line has `ω_s T_ℓ > 0`, and `𝓑` has trivial
kernel (radial graph), the line-flow state matrix is spectrally stable — for every tie-line
strength and every radial topology. -/
@[tmio TM, powerlib_foundation] theorem netA_spectrallyStable_of_gain [DecidableEq β]
    (hM : ∀ a, 0 < (area a).M) (hK : ∀ a, 0 < (area a).KI) (hB : ∀ a, 0 < (area a).B)
    (hgain : ∀ a, (area a).KI * (area a).M ≤ (area a).D + (area a).K)
    (hw : ∀ ℓ, 0 < ωs * T ℓ) (hker : ∀ p : β → ℝ, 𝓑 *ᵥ p = 0 → p = 0) :
    connection% ((⟨area, ωs, T, 𝓑⟩ : NetModel α β) ∈ (netFamily α β).den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% netFamily_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) (x := (⟨area, ωs, T, 𝓑⟩ : NetModel α β))).trans (netModel_isHurwitz_iff (⟨area, ωs, T, 𝓑⟩ : NetModel α β))]
  change Linear.SpectrallyStable (netA area ωs T 𝓑)
  classical
  have hg : ∀ a, 0 ≤ netGap area a := fun a => by unfold netGap; linarith [hgain a]
  have hgB : ∀ a, 0 < netGap area a + (area a).B := fun a => add_pos_of_nonneg_of_pos (hg a) (hB a)
  have hM0 : ∀ a, (area a).M ≠ 0 := fun a => (hM a).ne'
  refine LTI.spectrallyStable_of_real_pairs _ fun x y u v hu hv hx => ?_
  have hEu := netEnergy_mulVec (𝓑 := 𝓑) hM0 (fun a => (hK a).ne') (fun a => (hgB a).ne')
    (fun ℓ => (hw ℓ).ne') u
  have hEv := netEnergy_mulVec (𝓑 := 𝓑) hM0 (fun a => (hK a).ne') (fun a => (hgB a).ne')
    (fun ℓ => (hw ℓ).ne') v
  rw [hu, netEnergy_sub] at hEu
  rw [hv, netEnergy_combo] at hEv
  have hcomm := netEnergy_comm (area := area) (ωs := ωs) (T := T) u v
  have hNu := netEnergy_nonneg (fun a => (hM a).le) hK hgB hw u
  have hNv := netEnergy_nonneg (fun a => (hM a).le) hK hgB hw v
  have hDu : 0 ≤ netDiss area u := Finset.sum_nonneg fun a _ => netDiss_term_nonneg hg hB u a
  have hDv : 0 ≤ netDiss area v := Finset.sum_nonneg fun a _ => netDiss_term_nonneg hg hB v a
  have hsum : x * (netEnergy area ωs T u u + netEnergy area ωs T v v) =
      -(netDiss area u + netDiss area v) := by linear_combination hEu + hEv + y * hcomm
  have hxE : 0 ≤ x * (netEnergy area ωs T u u + netEnergy area ωs T v v) :=
    mul_nonneg hx (add_nonneg hNu hNv)
  have hDu0 : netDiss area u = 0 := by linarith
  have hDv0 : netDiss area v = 0 := by linarith
  -- every area: `ω = 0` and `ξ = 0`
  have hω : ∀ a, u (.inl a) = 0 ∧ v (.inl a) = 0 := by
    intro a
    obtain ⟨xu, gu⟩ := netDiss_eq_zero hg hB hDu0 a
    obtain ⟨xv, gv⟩ := netDiss_eq_zero hg hB hDv0 a
    have ru := netXi_mulVec (ωs := ωs) (T := T) (𝓑 := 𝓑) hM0 u a
    have rv := netXi_mulVec (ωs := ωs) (T := T) (𝓑 := 𝓑) hM0 v a
    rw [hu, netXi_sub, xu, xv] at ru
    rw [hv, netXi_combo, xu, xv] at rv
    have hKB : (area a).KI * (area a).B ≠ 0 := (mul_pos (hK a) (hB a)).ne'
    constructor
    · have : (area a).KI * (area a).B * u (.inl a) = 0 := by
        linear_combination ru + (area a).KI * gu
      exact (mul_eq_zero.mp this).resolve_left hKB
    · have : (area a).KI * (area a).B * v (.inl a) = 0 := by
        linear_combination rv + (area a).KI * gv
      exact (mul_eq_zero.mp this).resolve_left hKB
  have hC : ∀ a, u (.inr (.inr a)) = 0 ∧ v (.inr (.inr a)) = 0 := by
    intro a
    obtain ⟨xu, -⟩ := netDiss_eq_zero hg hB hDu0 a
    obtain ⟨xv, -⟩ := netDiss_eq_zero hg hB hDv0 a
    unfold netXi at xu xv
    rw [(hω a).1] at xu
    rw [(hω a).2] at xv
    constructor <;> linarith
  -- the frequency rows force zero net export, hence zero line flows (radial graph)
  have hP : ∀ z : α ⊕ (β ⊕ α) → ℝ, ∀ c d : ℝ, netA area ωs T 𝓑 *ᵥ z = c • u + d • v →
      (∀ a, z (.inl a) = 0) → (∀ a, z (.inr (.inr a)) = 0) → ∀ ℓ, z (.inr (.inl ℓ)) = 0 := by
    intro z c d hz hz0 hzC
    have hexp : 𝓑 *ᵥ (fun ℓ => z (.inr (.inl ℓ))) = 0 := by
      funext a
      have h := congrFun hz (.inl a)
      rw [netA_mulVec_freq, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, (hω a).1, (hω a).2,
        hz0 a, hzC a] at h
      simp only [smul_eq_mul, mul_zero, add_zero, zero_sub] at h
      have hMa := hM0 a
      field_simp at h
      simp only [mulVec, dotProduct, Pi.zero_apply]
      linarith
    exact fun ℓ => congrFun (hker _ hexp) ℓ
  have hPu := hP u x (-y) (by rw [hu]; simp [sub_eq_add_neg]) (fun a => (hω a).1)
    (fun a => (hC a).1)
  have hPv := hP v y x hv (fun a => (hω a).2) (fun a => (hC a).2)
  constructor
  · funext i
    rcases i with a | ℓ | a
    · exact (hω a).1
    · exact hPu ℓ
    · exact (hC a).1
  · funext i
    rcases i with a | ℓ | a
    · exact (hω a).2
    · exact hPv ℓ
    · exact (hC a).2

/-- Relabelling of the two-area state `(Δω_a, Δω_b, ΔP_tie, ΔP_C,a, ΔP_C,b)` as areas, the one
line `a → b`, and the AGC states. -/
def twoAreaEquiv : Fin 2 ⊕ (Fin 1 ⊕ Fin 2) ≃ Fin 5 where
  toFun
    | .inl a => if a = 0 then 0 else 1
    | .inr (.inl _) => 2
    | .inr (.inr a) => if a = 0 then 3 else 4
  invFun i := if i = 0 then .inl 0 else if i = 1 then .inl 1 else if i = 2 then .inr (.inl 0)
    else if i = 3 then .inr (.inr 0) else .inr (.inr 1)
  left_inv := by
    intro x
    rcases x with a | ℓ | a
    · fin_cases a <;> rfl
    · fin_cases ℓ; rfl
    · fin_cases a <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- The two-area state matrix of `Frequency.LFC.plant` is the line-flow `N`-area matrix of the two
areas and the single line `a → b` (`𝓑 = (1, −1)ᵀ`), relabelled. Static evidence on the model, not
a connection conclusion. -/
@[powerlib_foundation] theorem plant_A_eq_reindex (a b : Area) (ωs T : ℝ) :
    (plant a b ωs T).A =
      (netA ![a, b] ωs (fun _ : Fin 1 => T) !![1; -1]).reindex twoAreaEquiv twoAreaEquiv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plant, netA, twoAreaEquiv, Matrix.reindex_apply, Matrix.submatrix_apply] 

/-- **Gain condition, two areas.** With `M, K_I, B > 0` in both areas, `ω_s T > 0` and
`K_I M ≤ D + K_R` in both areas, the five-state LFC matrix is Hurwitz. -/
@[tmio TM, powerlib_foundation] theorem plant_isHurwitz_of_gain {a b : Area} {ωs T : ℝ}
    (hMa : 0 < a.M) (hMb : 0 < b.M) (hKa : 0 < a.KI) (hKb : 0 < b.KI) (hBa : 0 < a.B)
    (hBb : 0 < b.B) (hga : a.KI * a.M ≤ a.D + a.K) (hgb : b.KI * b.M ≤ b.D + b.K)
    (hw : 0 < ωs * T) :
    connection% ((⟨a, b, ωs, T⟩ : Model) ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial))]
  change IsHurwitz (plant a b ωs T).A
  rw [← Linear.spectrallyStable_iff_isHurwitz, plant_A_eq_reindex,
    Linear.spectrallyStable_reindex]
  refine ((connection_proof% netFamily_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) (x := (⟨![a, b], ωs, (fun _ : Fin 1 => T), !![1; -1]⟩ : NetModel (Fin 2) (Fin 1)))).trans (netModel_isHurwitz_iff (⟨![a, b], ωs, (fun _ : Fin 1 => T), !![1; -1]⟩ : NetModel (Fin 2) (Fin 1)))).mp
    (netA_spectrallyStable_of_gain (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i => ?_)
      (fun _ => hw) ?_)
  · fin_cases i <;> simpa
  · fin_cases i <;> simpa
  · fin_cases i <;> simpa
  · fin_cases i <;> simpa
  · intro p hp
    have h := congrFun hp 0
    simp [mulVec, dotProduct] at h
    funext ℓ
    fin_cases ℓ
    simpa using h


/-! ## The `N`-area family -/

/-! The connection statements quantify over the numbers of areas and lines (`Fin N_a` areas,
`Fin N_t` lines): the closed claim grammar quantifies over data, not over types. -/

/-- Every translation of the `N`-area family is sound. -/
@[tmio TM, powerlib_domain] theorem net_chain_le_semantics (Na Nt : ℕ) :
    connection% (∀ P, (netFamily (Fin Na) (Fin Nt)).chain P ≤
      (netFamily (Fin Na) (Fin Nt)).semantics P) := by
  unfold powerlib.TMIO.Statement
  exact sound_of_meetsMatrix netFamily_isLinear (fun _ _ => Iff.rfl) rfl

/-- The attractive sentences and sampled contraction of the `N`-area family are translated
exactly by the Hurwitz property of the transported state matrix. -/
@[tmio TM, powerlib_domain] theorem net_exact_hurwitz (Na Nt : ℕ) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((netFamily (Fin Na) (Fin Nt)).Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_meetsMatrix netFamily_isLinear (fun _ _ => Iff.rfl) rfl hP

/-- A spectrally stable state matrix (explicit premise) makes the `N`-area model globally
exponentially stable; in deviation coordinates this is the convergence of every trajectory under
constant loads to its steady state (on a radial graph, `(0, 0, ΔP_L)`). -/
@[tmio TM, powerlib_domain] theorem net_mem_den_globallyExponentiallyStable {Na Nt : ℕ}
    (m : NetModel (Fin Na) (Fin Nt))
    (hA : Linear.SpectrallyStable (netA m.area m.ωs m.T m.𝓑)) :
    connection% (m ∈ (netFamily (Fin Na) (Fin Nt)).den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [netFamily_isLinear.den_hurwitz (Or.inl (by simp))]
  exact (netModel_isHurwitz_iff m).2 hA

/-- Correction as a refutation: a loop in the tie-line graph (a nonzero circulating flow `p`,
`𝓑 p = 0`) excludes every attractive sentence, whatever the gains. -/
@[tmio TM, powerlib_domain] theorem net_not_mem_den_attractive {Na Nt : ℕ}
    (m : NetModel (Fin Na) (Fin Nt)) {p : Fin Nt → ℝ} (hp0 : p ≠ 0) (hp : m.𝓑 *ᵥ p = 0)
    {P : Flow.Property} (hP : P.Attractive) :
    connection% (m ∉ (netFamily (Fin Na) (Fin Nt)).den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [netFamily_isLinear.den_hurwitz (Or.inl hP)]
  intro h
  exact netModel_not_spectrallyStable hp0 hp
    (netFamily_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) |>.mpr h)

/-- Three areas in a ring: the line-flow LFC model satisfies no attractive sentence for any
parameters. -/
@[tmio TM, powerlib_domain] theorem triangle_not_mem_den_attractive (area : Fin 3 → Area) (ωs : ℝ)
    (T : Fin 3 → ℝ) {P : Flow.Property} (hP : P.Attractive) :
    connection% ((⟨area, ωs, T, Network.signedIncidence (![0, 1, 2] : Fin 3 → Fin 3) ![1, 2, 0]⟩ :
      NetModel (Fin 3) (Fin 3)) ∉ (netFamily (Fin 3) (Fin 3)).den (.flow P)) :=
  net_not_mem_den_attractive _ (p := fun _ => 1) (fun h => by simpa using congrFun h 0)
    triangle_circulation hP

/-- **Gain condition (connection), `N` areas.** On a radial tie-line graph (`𝓑` with trivial
kernel), if every area has `M_a, K_I,a, B_a > 0` and `K_I,a M_a ≤ D_a + K_R,a`, and every line
has `ω_s T_ℓ > 0`, the model satisfies every attractive sentence and sampled contraction —
whatever the tie-line strengths and the radial topology. -/
@[tmio TM, powerlib_domain] theorem net_mem_den_of_gain {Na Nt : ℕ} (m : NetModel (Fin Na) (Fin Nt))
    (hM : ∀ a, 0 < (m.area a).M) (hK : ∀ a, 0 < (m.area a).KI) (hB : ∀ a, 0 < (m.area a).B)
    (hgain : ∀ a, (m.area a).KI * (m.area a).M ≤ (m.area a).D + (m.area a).K)
    (hw : ∀ ℓ, 0 < m.ωs * m.T ℓ) (hker : ∀ p : Fin Nt → ℝ, m.𝓑 *ᵥ p = 0 → p = 0)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ (netFamily (Fin Na) (Fin Nt)).den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [netFamily_isLinear.den_hurwitz hP]
  exact (netFamily_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) (x := m)).mp
    (netA_spectrallyStable_of_gain (area := m.area) (ωs := m.ωs) (T := m.T) (𝓑 := m.𝓑) hM hK hB hgain hw hker)

/-- **Gain condition (connection), two areas** (`Frequency.LFC.family`, five states): with
`M, K_I, B > 0`, `K_I M ≤ D + K_R` in both areas and `ω_s T > 0`, the two-area model satisfies
every attractive sentence and sampled contraction; this replaces the explicit Hurwitz premise of
`LFC.mem_den_globallyExponentiallyStable` by a parametric one. -/
@[tmio TM, powerlib_domain] theorem mem_den_of_gain (m : Model) (hMa : 0 < m.a.M) (hMb : 0 < m.b.M)
    (hKa : 0 < m.a.KI) (hKb : 0 < m.b.KI) (hBa : 0 < m.a.B) (hBb : 0 < m.b.B)
    (hga : m.a.KI * m.a.M ≤ m.a.D + m.a.K) (hgb : m.b.KI * m.b.M ≤ m.b.D + m.b.K)
    (hw : 0 < m.ωs * m.T) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz hP]
  exact (family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial) (x := m)).mp
    (plant_isHurwitz_of_gain hMa hMb hKa hKb hBa hBb hga hgb hw)

/-! ## Implementation evidence (private, trajectory level) -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
`N`-area model on a radial tie-line graph: if the state matrix is spectrally stable, every
forward solution under constant loads converges to the non-interactive steady state
`(Δω, ΔP_tie, ΔP_C) = (0, 0, ΔP_L)`. -/
private theorem netModel_tendsto [DecidableEq β] (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (hcol : ∀ ℓ, ∑ a, 𝓑 a ℓ = 0)
    (hconn : ∀ w : α → ℝ, (∀ ℓ, ∑ c, 𝓑 c ℓ * w c = 0) → ∀ a c, w a = w c)
    (hker : ∀ p : β → ℝ, 𝓑 *ᵥ p = 0 → p = 0)
    (hA : Linear.SpectrallyStable (netA area ωs T 𝓑)) (u : α → ℝ)
    {x : ℝ → α ⊕ (β ⊕ α) → ℝ}
    (hx : ∀ t ≥ 0, HasDerivWithinAt x (netField area ωs T 𝓑 (x t) u) (Ici 0) t) :
    Tendsto x atTop (𝓝 (netSteadyState u)) :=
  LTI.tendsto_of_spectrallyStable hA
    ((isEquilibrium_iff_of_ker hM hKI hT hB hcol hconn hker u _).2 rfl) hx

end powerlib.Frequency.LFC
