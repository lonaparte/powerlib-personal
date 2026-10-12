import theorem.Frequency.LFC
import theorem.PH.RLNetwork

/-! # Multi-area load-frequency control on a tie-line graph

Source: work-sync `theory/T-load-frequency-control.md` §1.1–§1.6 and the last paragraph of §1.7
("进一步推广到 `N_a` 区 … `(3 N_a + N_t)` 维").

Model boundary. Same per-area model as `Frequency.LFC.plant` (continuous-time, linear, Kundur
per-unit, governors instantaneous `T_g → 0`, one coherent machine per area, AGC integral on the
tie-line-bias ACE, no dead-band / limits / HVDC / voltage dynamics), now for a finite set `α`
of areas and a finite set `β` of tie lines, coupled by an arbitrary real matrix
`𝓑 : Matrix α β ℝ`; the intended case is the signed incidence matrix
`PH.signedIncidence tail head` of the directed tie-line graph (`+1` at the sending area).
* State index `α ⊕ (β ⊕ α)`: `inl a` = `Δω_a`, `inr (inl ℓ)` = line flow `ΔP_tie,ℓ`
  (from `tail ℓ` to `head ℓ`), `inr (inr a)` = `ΔP_C,a`. Input `ΔP_L : α → ℝ`.
* Equations: `M_a Δω̇_a = ΔP_C,a − K_R,a Δω_a − ΔP_L,a − D_a Δω_a − (𝓑 ΔP_tie)_a`;
  `ΔṖ_tie,ℓ = ω_s T_ℓ (𝓑ᵀ Δω)_ℓ`; `ΔṖ_C,a = −K_I,a ((𝓑 ΔP_tie)_a + B_a Δω_a)`.

Results.
* `netModel_card` (foundation). Correction: with `T_g → 0` (the simplification used for §1.7)
  the state dimension is `2 N_a + N_t`; the note's `3 N_a + N_t` counts one governor state per
  area that the §1.7 model has eliminated.
* `netField x u = netA x + netB u` is the field under the constant loads `u`.
* `netModel_isEquilibrium_iff` (foundation, static, §1.6 for `N_a` areas): if the tie-line graph is
  connected (`ker 𝓑ᵀ` = constants), every column of `𝓑` sums to zero, `Σ_a B_a ≠ 0`,
  `K_I,a ≠ 0`, `ω_s T_ℓ ≠ 0`, `M_a ≠ 0`, then the equilibria are exactly
  `Δω = 0`, net tie exports `𝓑 ΔP_tie = 0`, `ΔP_C,a = ΔP_L,a` (non-interactive control).
  `signedIncidence_isEquilibrium_iff` instantiates this for the signed incidence matrix of a
  connected graph (`TieConnected`); `isEquilibrium_iff_of_ker` gives the unique equilibrium
  `(0, 0, ΔP_L)` when `𝓑` has trivial kernel (radial tie-line graph).
* `netModel_not_spectrallyStable` (foundation, static), `triangle_not_spectrallyStable`: if `𝓑` has a
  nonzero kernel vector (a loop in the tie-line graph, e.g. three areas in a ring) the
  line-flow state matrix is singular (a circulating flow is a zero mode), so the model is
  **never** asymptotically stable, for any gains. Correction: line flows are not independent
  states on a meshed graph; a stable realization must use area angles or a spanning tree.
* `tendsto_of_spectrallyStable` (foundation, any matrices on a finite index type, by transport to
  `Fin N`) and `netModel_tendsto` (private): on a radial tie-line graph, a spectrally stable
  state matrix (explicit premise; no parametric Routh–Hurwitz condition is available) makes every
  trajectory under constant loads converge to `(0, 0, ΔP_L)`.

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
  premise; formerly `netModel_tendsto`), `net_not_mem_den_attractive` (a loop in the tie-line
  graph excludes every attractive sentence, for any gains) and `triangle_not_mem_den_attractive`.
* The equilibrium characterizations and spectral statements (formerly `@[powerlib_domain]`) are
  static evidence (`@[powerlib_foundation]`); `tendsto_of_spectrallyStable` is a generic
  implication about arbitrary matrices (foundation). Private implementation evidence
  (trajectory level, Rules §3a): `netModel_tendsto`.
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
@[powerlib_foundation] theorem netModel_card :
    Fintype.card (α ⊕ (β ⊕ α)) = 2 * Fintype.card α + Fintype.card β := by
  simp only [Fintype.card_sum]
  ring

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
@[powerlib_foundation] theorem signedIncidence_col_sum (tail head : β → α) (ℓ : β) :
    ∑ a, PH.signedIncidence tail head a ℓ = 0 := by
  have h := PH.signedIncidence_transpose_mulVec tail head (fun _ => (1 : ℝ)) ℓ
  simpa [mulVec, dotProduct] using h

omit [Fintype β] in
@[powerlib_foundation] theorem signedIncidence_const_of_connected {tail head : β → α}
    (hconn : TieConnected tail head) (w : α → ℝ)
    (hw : ∀ ℓ, ∑ c, PH.signedIncidence tail head c ℓ * w c = 0) (a c : α) : w a = w c := by
  have hedge : ∀ ℓ, w (tail ℓ) = w (head ℓ) := by
    intro ℓ
    have h := PH.signedIncidence_transpose_mulVec tail head w ℓ
    have h' : ((PH.signedIncidence tail head)ᵀ *ᵥ w) ℓ = 0 := by
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
    netField area ωs T (PH.signedIncidence tail head) e u = 0 ↔
      (∀ a, e (.inl a) = 0) ∧
        (∀ a, ∑ ℓ, PH.signedIncidence tail head a ℓ * e (.inr (.inl ℓ)) = 0) ∧
        ∀ a, e (.inr (.inr a)) = u a :=
  netModel_isEquilibrium_iff hM hKI hT hB (signedIncidence_col_sum tail head)
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
line-flow realization is never spectrally stable, whatever the gains. Static evidence on the
model, not a connection conclusion. -/
@[powerlib_foundation] theorem netModel_not_spectrallyStable [DecidableEq β] {p : β → ℝ}
    (hp0 : p ≠ 0) (hp : 𝓑 *ᵥ p = 0) : ¬ Linear.SpectrallyStable (netA area ωs T 𝓑) := by
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
    PH.signedIncidence (![0, 1, 2] : Fin 3 → Fin 3) ![1, 2, 0] *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  funext a
  fin_cases a <;>
    simp only [PH.signedIncidence, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Pi.zero_apply] <;> norm_num

/-- Three areas in a ring (`1 → 2 → 3 → 1`): the line-flow LFC model is not spectrally stable
for any parameters. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem triangle_not_spectrallyStable (area : Fin 3 → Area) (ωs : ℝ)
    (T : Fin 3 → ℝ) :
    ¬ Linear.SpectrallyStable
      (netA area ωs T (PH.signedIncidence (![0, 1, 2] : Fin 3 → Fin 3) ![1, 2, 0])) :=
  netModel_not_spectrallyStable (p := fun _ => 1) (fun h => by simpa using congrFun h 0)
    triangle_circulation

/-! ## Convergence on a general index type -/

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Spectral stability of the state matrix gives convergence of every constant-input forward
solution to an equilibrium, on any finite index type (transport to `Fin N`, then the linear hub
`Linear.globallyAsymptoticallyStable_of_isHurwitz`). Generic in the matrices. -/
@[powerlib_foundation] theorem tendsto_of_spectrallyStable {A : Matrix ι ι ℝ}
    {B : Matrix ι κ ℝ} (hA : Linear.SpectrallyStable A) {u : κ → ℝ} {e : ι → ℝ}
    (he : A *ᵥ e + B *ᵥ u = 0) {x : ℝ → ι → ℝ}
    (hx : ∀ t ≥ 0, HasDerivWithinAt x (A *ᵥ x t + B *ᵥ u) (Ici 0) t) :
    Tendsto x atTop (𝓝 e) := by
  set eq := Fintype.equivFin ι
  set A' := A.reindex eq eq
  have hA' : IsHurwitz A' :=
    (Linear.spectrallyStable_iff_isHurwitz _).1 ((Linear.spectrallyStable_reindex eq A).2 hA)
  set e' : EuclideanSpace ℝ (Fin (Fintype.card ι)) := WithLp.toLp 2 (e ∘ eq.symm)
  set y : ℝ → EuclideanSpace ℝ (Fin (Fintype.card ι)) := fun t => WithLp.toLp 2 (x t ∘ eq.symm)
  have hBu : B *ᵥ u = -(A *ᵥ e) := eq_neg_of_add_eq_zero_right he
  have hy : IsIntegralCurveOn y (fun _ z => affineLinearVectorField A' e' z) (Ici 0) := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t => x t ∘ eq.symm) ((A *ᵥ x t + B *ᵥ u) ∘ eq.symm)
        (Ici 0) t :=
      hasDerivWithinAt_pi.2 fun i => hasDerivWithinAt_pi.1 (hx t ht) (eq.symm i)
    have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Fintype.card ι) => ℝ)).symm
      |>.hasFDerivAt.comp_hasDerivWithinAt t h1
    refine h2.congr_deriv ?_
    show _ = affineLinearVectorField A' e' (y t)
    rw [Linear.affine_apply]
    change WithLp.toLp 2 ((A *ᵥ x t + B *ᵥ u) ∘ eq.symm) =
      WithLp.toLp 2 (A' *ᵥ ((x t - e) ∘ eq.symm))
    congr 1
    rw [hBu, show A' = A.submatrix eq.symm eq.symm from rfl, Matrix.submatrix_mulVec_equiv]
    funext i
    simp only [Function.comp_def, Equiv.symm_symm, Pi.add_apply,
      Pi.neg_apply, Pi.sub_apply]
    rw [show (fun j => x t (eq.symm (eq j)) - e (eq.symm (eq j))) = x t - e by
      funext j; simp, Matrix.mulVec_sub]
    simp [sub_eq_add_neg]
  have hlim := (Linear.globallyAsymptoticallyStable_of_isHurwitz e' hA').2.2.2 0 y hy
  have hc : Continuous (fun w : EuclideanSpace ℝ (Fin (Fintype.card ι)) => WithLp.ofLp w ∘ eq) :=
    by fun_prop
  have := (hc.tendsto _).comp hlim
  simpa [Function.comp_def, y, e'] using this

end Reindex

/-! ## The `N`-area family -/

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

/-! The connection statements quantify over the numbers of areas and lines (`Fin N_a` areas,
`Fin N_t` lines): the closed claim grammar quantifies over data, not over types. -/

/-- Every translation of the `N`-area family is sound. -/
@[powerlib_domain] theorem net_chain_le_semantics (Na Nt : ℕ) :
    connection% (∀ P, (netFamily (Fin Na) (Fin Nt)).chain P ≤
      (netFamily (Fin Na) (Fin Nt)).semantics P) := by
  unfold powerlib.TMIO.Statement
  exact sound_of_meetsMatrix netFamily_isLinear (fun _ _ => Iff.rfl) rfl

/-- The attractive sentences and sampled contraction of the `N`-area family are translated
exactly by the Hurwitz property of the transported state matrix. -/
@[powerlib_domain] theorem net_exact_hurwitz (Na Nt : ℕ) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((netFamily (Fin Na) (Fin Nt)).Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_meetsMatrix netFamily_isLinear (fun _ _ => Iff.rfl) rfl hP

/-- A spectrally stable state matrix (explicit premise) makes the `N`-area model globally
exponentially stable; in deviation coordinates this is the convergence of every trajectory under
constant loads to its steady state (on a radial graph, `(0, 0, ΔP_L)`). -/
@[powerlib_domain] theorem net_mem_den_globallyExponentiallyStable {Na Nt : ℕ}
    (m : NetModel (Fin Na) (Fin Nt))
    (hA : Linear.SpectrallyStable (netA m.area m.ωs m.T m.𝓑)) :
    connection% (m ∈ (netFamily (Fin Na) (Fin Nt)).den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [netFamily_isLinear.den_hurwitz (Or.inl (by simp))]
  exact (netModel_isHurwitz_iff m).2 hA

/-- Correction as a refutation: a loop in the tie-line graph (a nonzero circulating flow `p`,
`𝓑 p = 0`) excludes every attractive sentence, whatever the gains. -/
@[powerlib_domain] theorem net_not_mem_den_attractive {Na Nt : ℕ}
    (m : NetModel (Fin Na) (Fin Nt)) {p : Fin Nt → ℝ} (hp0 : p ≠ 0) (hp : m.𝓑 *ᵥ p = 0)
    {P : Flow.Property} (hP : P.Attractive) :
    connection% (m ∉ (netFamily (Fin Na) (Fin Nt)).den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [netFamily_isLinear.den_hurwitz (Or.inl hP)]
  intro h
  exact netModel_not_spectrallyStable hp0 hp ((netModel_isHurwitz_iff m).1 h)

/-- Three areas in a ring: the line-flow LFC model satisfies no attractive sentence for any
parameters. -/
@[powerlib_domain] theorem triangle_not_mem_den_attractive (area : Fin 3 → Area) (ωs : ℝ)
    (T : Fin 3 → ℝ) {P : Flow.Property} (hP : P.Attractive) :
    connection% ((⟨area, ωs, T, PH.signedIncidence (![0, 1, 2] : Fin 3 → Fin 3) ![1, 2, 0]⟩ :
      NetModel (Fin 3) (Fin 3)) ∉ (netFamily (Fin 3) (Fin 3)).den (.flow P)) :=
  net_not_mem_den_attractive _ (p := fun _ => 1) (fun h => by simpa using congrFun h 0)
    triangle_circulation hP

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
  tendsto_of_spectrallyStable hA
    ((isEquilibrium_iff_of_ker hM hKI hT hB hcol hconn hker u _).2 rfl) hx

end powerlib.Frequency.LFC
