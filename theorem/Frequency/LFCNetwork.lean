import theorem.Frequency.LFC
import theorem.PH.RLNetwork

/-! # Multi-area load-frequency control on a tie-line graph

Source: work-sync `theory/T-load-frequency-control.md` §1.1–§1.6 and the last paragraph of §1.7
("进一步推广到 `N_a` 区 … `(3 N_a + N_t)` 维").

Model boundary. Same per-area model as `Frequency.LFC.model` (continuous-time, linear, Kundur
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
* `netModel_isEquilibrium_iff` (domain, §1.6 for `N_a` areas): if the tie-line graph is
  connected (`ker 𝓑ᵀ` = constants), every column of `𝓑` sums to zero, `Σ_a B_a ≠ 0`,
  `K_I,a ≠ 0`, `ω_s T_ℓ ≠ 0`, `M_a ≠ 0`, then the equilibria are exactly
  `Δω = 0`, net tie exports `𝓑 ΔP_tie = 0`, `ΔP_C,a = ΔP_L,a` (non-interactive control).
  `signedIncidence_isEquilibrium_iff` instantiates this for the signed incidence matrix of a
  connected graph (`TieConnected`); `isEquilibrium_iff_of_ker` gives the unique equilibrium
  `(0, 0, ΔP_L)` when `𝓑` has trivial kernel (radial tie-line graph).
* `netModel_not_spectrallyStable` (domain), `triangle_not_spectrallyStable`: if `𝓑` has a
  nonzero kernel vector (a loop in the tie-line graph, e.g. three areas in a ring) the
  line-flow state matrix is singular (a circulating flow is a zero mode), so the model is
  **never** asymptotically stable, for any gains. Correction: line flows are not independent
  states on a meshed graph; a stable realization must use area angles or a spanning tree.
* `tendsto_of_spectrallyStable` (domain, any finite index type, by transport to `Fin N`) and
  `netModel_tendsto` (domain): on a radial tie-line graph, a spectrally stable state matrix
  (explicit premise; no parametric Routh–Hurwitz condition is available) makes every trajectory
  under constant loads converge to `(0, 0, ΔP_L)`.
-/

noncomputable section
namespace powerlib.Frequency.LFC
open Set Filter Matrix
open scoped Topology

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

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

/-- `N`-area LFC model with outputs `Δω`. -/
def netModel (area : α → Area) (ωs : ℝ) (T : β → ℝ) (𝓑 : Matrix α β ℝ) :
    LTI.Model (α ⊕ (β ⊕ α)) α where
  A := netA area ωs T 𝓑
  B := netB area
  C := fun c i => match i with
    | .inl a => if c = a then 1 else 0
    | .inr _ => 0
  D := 0

omit [DecidableEq α] in
/-- Correction (dimension): `2 N_a + N_t` states once `T_g → 0`. -/
@[powerlib_foundation] theorem netModel_card :
    Fintype.card (α ⊕ (β ⊕ α)) = 2 * Fintype.card α + Fintype.card β := by
  simp only [Fintype.card_sum]
  ring

variable {area : α → Area} {ωs : ℝ} {T : β → ℝ} {𝓑 : Matrix α β ℝ}

/-- Swing row of area `a`. -/
@[powerlib_foundation] theorem netField_freq (x : α ⊕ (β ⊕ α) → ℝ) (u : α → ℝ) (a : α) :
    (netModel area ωs T 𝓑).field x u (.inl a) =
      (-((area a).D + (area a).K) * x (.inl a) - ∑ ℓ, 𝓑 a ℓ * x (.inr (.inl ℓ)) +
        x (.inr (.inr a)) - u a) / (area a).M := by
  simp only [LTI.Model.field, netModel, Pi.add_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, netA, netB, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sub_div, add_div, sub_div, Finset.sum_div]
  have : ∀ ℓ, -𝓑 a ℓ / (area a).M * x (.inr (.inl ℓ)) = -(𝓑 a ℓ * x (.inr (.inl ℓ)) / (area a).M) :=
    fun ℓ => by ring
  simp only [this, Finset.sum_neg_distrib]
  ring

/-- Tie-line rows: `ΔṖ_tie,ℓ = ω_s T_ℓ (𝓑ᵀ Δω)_ℓ`. -/
@[powerlib_foundation] theorem netField_tie (x : α ⊕ (β ⊕ α) → ℝ) (u : α → ℝ) (ℓ : β) :
    (netModel area ωs T 𝓑).field x u (.inr (.inl ℓ)) =
      ωs * T ℓ * ∑ c, 𝓑 c ℓ * x (.inl c) := by
  simp only [LTI.Model.field, netModel, Pi.add_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, netA, netB, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- AGC rows: `ΔṖ_C,a = −K_I,a ((𝓑 ΔP_tie)_a + B_a Δω_a)`. -/
@[powerlib_foundation] theorem netField_agc (x : α ⊕ (β ⊕ α) → ℝ) (u : α → ℝ) (a : α) :
    (netModel area ωs T 𝓑).field x u (.inr (.inr a)) =
      -(area a).KI * (∑ ℓ, 𝓑 a ℓ * x (.inr (.inl ℓ)) + (area a).B * x (.inl a)) := by
  simp only [LTI.Model.field, netModel, Pi.add_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, netA, netB, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, mul_add, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun ℓ _ => by ring
  · ring

/-- §1.6 for `N` areas (non-interactive control) under connectivity of the tie-line graph. -/
@[powerlib_domain] theorem netModel_isEquilibrium_iff (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (hcol : ∀ ℓ, ∑ a, 𝓑 a ℓ = 0)
    (hconn : ∀ w : α → ℝ, (∀ ℓ, ∑ c, 𝓑 c ℓ * w c = 0) → ∀ a c, w a = w c)
    (u : α → ℝ) (e : α ⊕ (β ⊕ α) → ℝ) :
    (netModel area ωs T 𝓑).IsEquilibrium u e ↔
      (∀ a, e (.inl a) = 0) ∧ (∀ a, ∑ ℓ, 𝓑 a ℓ * e (.inr (.inl ℓ)) = 0) ∧
        ∀ a, e (.inr (.inr a)) = u a := by
  unfold LTI.Model.IsEquilibrium
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

/-- Radial tie-line graph (`ker 𝓑 = 0`): the unique equilibrium is `(0, 0, ΔP_L)`. -/
@[powerlib_domain] theorem isEquilibrium_iff_of_ker (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (hcol : ∀ ℓ, ∑ a, 𝓑 a ℓ = 0)
    (hconn : ∀ w : α → ℝ, (∀ ℓ, ∑ c, 𝓑 c ℓ * w c = 0) → ∀ a c, w a = w c)
    (hker : ∀ p : β → ℝ, 𝓑 *ᵥ p = 0 → p = 0) (u : α → ℝ) (e : α ⊕ (β ⊕ α) → ℝ) :
    (netModel area ωs T 𝓑).IsEquilibrium u e ↔ e = Sum.elim (fun _ => (0 : ℝ)) (Sum.elim (fun _ => (0 : ℝ)) u) := by
  rw [netModel_isEquilibrium_iff hM hKI hT hB hcol hconn]
  constructor
  · rintro ⟨hω, hp, hc⟩
    have hp0 := hker (fun ℓ => e (.inr (.inl ℓ))) (funext fun a => by
      simpa [mulVec, dotProduct] using hp a)
    funext i
    rcases i with a | ℓ | a
    · simp [hω]
    · simpa using congrFun hp0 ℓ
    · simp [hc]
  · rintro rfl
    simp

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

/-- §1.6 for `N` areas on a connected tie-line graph with signed incidence matrix. -/
@[powerlib_domain] theorem signedIncidence_isEquilibrium_iff {tail head : β → α}
    (hconn : TieConnected tail head) (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (u : α → ℝ) (e : α ⊕ (β ⊕ α) → ℝ) :
    (netModel area ωs T (PH.signedIncidence tail head)).IsEquilibrium u e ↔
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
line-flow realization is never spectrally stable, whatever the gains. -/
@[powerlib_domain] theorem netModel_not_spectrallyStable [DecidableEq β] {p : β → ℝ} (hp0 : p ≠ 0)
    (hp : 𝓑 *ᵥ p = 0) : ¬ LTI.SpectrallyStable (netModel area ωs T 𝓑).A := by
  intro hs
  have hv : (Sum.elim 0 (Sum.elim p 0) : α ⊕ (β ⊕ α) → ℝ) ≠ 0 := by
    intro h
    apply hp0
    funext ℓ
    simpa using congrFun h (.inr (.inl ℓ))
  have hdet : (netA area ωs T 𝓑).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hv, netA_mulVec_circulation hp⟩
  have h0 : (LTI.characteristicMatrix (netModel area ωs T 𝓑).A 0).det = 0 := by
    have : LTI.characteristicMatrix (netModel area ωs T 𝓑).A 0 =
        -(netA area ωs T 𝓑).map (algebraMap ℝ ℂ) := by
      simp [LTI.characteristicMatrix, netModel]
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
for any parameters. -/
@[powerlib_domain] theorem triangle_not_spectrallyStable (area : Fin 3 → Area) (ωs : ℝ)
    (T : Fin 3 → ℝ) :
    ¬ LTI.SpectrallyStable
      (netModel area ωs T (PH.signedIncidence (![0, 1, 2] : Fin 3 → Fin 3) ![1, 2, 0])).A :=
  netModel_not_spectrallyStable (p := fun _ => 1) (fun h => by simpa using congrFun h 0)
    triangle_circulation

/-! ## Convergence on a general index type -/

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- An LTI model on a finite index type, transported to `Fin N` along `eq : ι ≃ Fin N`. -/
def reindexModel {N : ℕ} (eq : ι ≃ Fin N) (m : LTI.Model ι κ) : LTI.Model (Fin N) κ where
  A := m.A.submatrix eq.symm eq.symm
  B := m.B.submatrix eq.symm (Equiv.refl κ)
  C := m.C.submatrix (Equiv.refl κ) eq.symm
  D := m.D

omit [DecidableEq ι] in
@[powerlib_foundation] theorem reindexModel_field {N : ℕ} (eq : ι ≃ Fin N) (m : LTI.Model ι κ)
    (v : ι → ℝ) (u : κ → ℝ) :
    (reindexModel eq m).field (v ∘ eq.symm) u = m.field v u ∘ eq.symm := by
  simp only [LTI.Model.field, reindexModel, submatrix_mulVec_equiv]
  funext i
  simp [Function.comp_def]

/-- Spectral stability of the state matrix gives convergence of every constant-input trajectory
to an equilibrium, on any finite index type (transport to `Fin N`, then
`Frequency.exponentiallyConvergesTo_of_isHurwitz`). -/
@[powerlib_domain] theorem tendsto_of_spectrallyStable {m : LTI.Model ι κ}
    (hA : LTI.SpectrallyStable m.A) {u : κ → ℝ} {e : ι → ℝ} (he : m.IsEquilibrium u e)
    {x : ℝ → ι → ℝ} (hx : Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => u) x) :
    Filter.Tendsto x Filter.atTop (𝓝 e) := by
  set eq := Fintype.equivFin ι
  set m' := reindexModel eq m
  have hA' : LinearSystems.IsHurwitz m'.A := by
    have h := (LTI.spectrallyStable_reindex eq m.A).2 hA
    rw [Matrix.reindex_apply] at h
    exact (LTI.spectrallyStable_iff_isHurwitz _).1 h
  have he' : m'.IsEquilibrium u (e ∘ eq.symm) := by
    unfold LTI.Model.IsEquilibrium
    rw [reindexModel_field, show m.field e u = 0 from he]
    rfl
  have hx' : IsTrajectory m' u (fun t => x t ∘ eq.symm) := by
    intro t ht
    have h := hx t ht
    change HasDerivWithinAt (fun t => x t ∘ eq.symm) (m'.field (x t ∘ eq.symm) u) (Ici 0) t
    rw [reindexModel_field]
    exact hasDerivWithinAt_pi.2 fun i => hasDerivWithinAt_pi.1 h (eq.symm i)
  have hlim := tendsto_of_exponentiallyConvergesTo
    (Frequency.exponentiallyConvergesTo_of_isHurwitz he' hA') hx'
  have hc : Continuous (fun w : Fin (Fintype.card ι) → ℝ => w ∘ eq) := by fun_prop
  have := (hc.tendsto _).comp hlim
  simpa [Function.comp_def] using this

end Reindex

/-- `N`-area model on a radial tie-line graph: if the state matrix is spectrally stable, every
trajectory under constant loads converges to the non-interactive steady state
`(Δω, ΔP_tie, ΔP_C) = (0, 0, ΔP_L)`. -/
@[powerlib_domain] theorem netModel_tendsto [DecidableEq β] (hM : ∀ a, (area a).M ≠ 0)
    (hKI : ∀ a, (area a).KI ≠ 0) (hT : ∀ ℓ, ωs * T ℓ ≠ 0) (hB : ∑ a, (area a).B ≠ 0)
    (hcol : ∀ ℓ, ∑ a, 𝓑 a ℓ = 0)
    (hconn : ∀ w : α → ℝ, (∀ ℓ, ∑ c, 𝓑 c ℓ * w c = 0) → ∀ a c, w a = w c)
    (hker : ∀ p : β → ℝ, 𝓑 *ᵥ p = 0 → p = 0)
    (hA : LTI.SpectrallyStable (netModel area ωs T 𝓑).A) (u : α → ℝ)
    {x : ℝ → α ⊕ (β ⊕ α) → ℝ}
    (hx : Passivity.IsTrajectory (StateSpacePassivity.system (netModel area ωs T 𝓑))
      (fun _ => u) x) :
    Filter.Tendsto x Filter.atTop
      (𝓝 (Sum.elim (fun _ => (0 : ℝ)) (Sum.elim (fun _ => (0 : ℝ)) u))) :=
  tendsto_of_spectrallyStable hA
    ((isEquilibrium_iff_of_ker hM hKI hT hB hcol hconn hker u _).2 rfl) hx

end powerlib.Frequency.LFC
