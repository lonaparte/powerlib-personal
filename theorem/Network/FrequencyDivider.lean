import theorem.Network.WeightedLaplacian

/-! # Frequency divider: bus frequencies as convex combinations of machine frequencies

Static foundation for the Milano–Ortega frequency divider `Δω_b = −B_bb⁻¹ B_bg Δω_g`: when the
grounded block is nonsingular, and why the bus frequencies are convex combinations of the machine
frequencies.

Model boundary.
* Buses `β ⊕ γ`: `inl b` are the non-machine buses, `inr g` the machine buses.
* Lossless network with no shunt branches, constant voltage magnitudes, small-signal
  linearization of `Pᵢ = ∑ⱼ bᵢⱼ ViVj sin(θᵢ - θⱼ)` around an operating point: the
  linearized injections are `ΔP = L Δθ` with `L` the weighted Laplacian of
  `Wᵢⱼ = bᵢⱼ ViVj cos(θᵢ⁰ - θⱼ⁰)` (`Network.hasFDerivAt_powerInjection`). The theorems below
  take `W` symmetric and entrywise nonnegative (each line has positive susceptance
  and angle difference below `π/2`).
* Non-machine buses carry no net injection perturbation: `ΔP_b = 0`.
* `B_bb`, `B_bg` denote the blocks of `L` (the note's `B` is this Laplacian).
* Algebraic / small-signal level: no machine dynamics, PLL, measurement filter or
  voltage-magnitude dynamics (§1.7 complex frequency is excluded).

Source: work-sync `theory/T-local-frequency.md` §1.2–§1.5, §2.6, §2.7
(Milano–Ortega frequency divider `Δω_b = -B_bb⁻¹ B_bg Δω_g`).

Results.
* `B_bb = L_bb + diag(∑_g W_bg)` is a grounded Laplacian (`Bbb_eq_grounded`); it is nonsingular
  iff every non-machine bus is connected to some machine bus (`Bbb_det_ne_zero_iff`,
  `MachineConnected`).
* `Δθ_b = D_fd Δθ_g` (`nonMachine_angles`) and, along differentiable angle trajectories, the
  frequency divider `Δω_b = D_fd Δω_g` with `D_fd = -B_bb⁻¹ B_bg` (`frequencyDivider`).
* `D_fd ≥ 0` entrywise and each row sums to 1 (§1.4; `Dfd_nonneg`, `Dfd_row_sum`).
* Each bus frequency deviation lies between the smallest and the largest machine
  frequency deviation (`le_busFrequency`, `busFrequency_le`); in common mode all bus
  frequencies equal the COI frequency (`busFrequency_commonMode`,
  `busFrequency_sub_coi_commonMode`); a machine mode shape `v` appears at the buses as `D_fd v`
  (`busFrequency_modal`).

Corrections.
* §2.7 ("环网可能病态"): meshed (loopy) networks are never singular under the connectivity
  condition; singularity occurs exactly when a non-machine component is isolated from all
  machines (`Bbb_det_ne_zero_iff`).
* §1.4: the note says the weights are "正" (positive); they are only nonnegative in general (a
  machine not connected to the component of bus `b` has weight 0).
-/

noncomputable section
namespace powerlib.Network
open Matrix Finset

variable {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-! ## Singularity of grounded Laplacians -/

section Singular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- If node `i` has no positive-weight path to a grounded node, the indicator of its
component lies in the kernel of the grounded Laplacian. -/
@[powerlib_foundation] theorem grounded_mulVec_component_eq_zero {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) {i : ι}
    (hnot : ∀ k, Reach W i k → g k ≤ 0) :
    grounded W g *ᵥ (fun a => if Reach W i a then (1 : ℝ) else 0) = 0 := by
  classical
  funext a
  rw [grounded_mulVec_apply, Pi.zero_apply]
  have hgx : g a * (if Reach W i a then (1 : ℝ) else 0) = 0 := by
    by_cases ha : Reach W i a
    · simp [ha, le_antisymm (hnot a ha) (hg a)]
    · simp [ha]
  rw [hgx, zero_add]
  apply Finset.sum_eq_zero
  intro b _
  rcases (hpos a b).lt_or_eq with hab | hab
  · by_cases ha : Reach W i a
    · have hb : Reach W i b := ha.tail hab
      simp [ha, hb]
    · have hb : ¬ Reach W i b := fun hb => ha (hb.tail (by rw [hW]; exact hab))
      simp [ha, hb]
  · rw [← hab, zero_mul]

open scoped Classical in
/-- For symmetric nonnegative weights and nonnegative grounding, the grounded Laplacian
is nonsingular exactly when every node reaches a grounded node. -/
@[powerlib_foundation] theorem grounded_det_ne_zero_iff {W : Matrix ι ι ℝ} {g : ι → ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) (hg : ∀ i, 0 ≤ g i) :
    (grounded W g).det ≠ 0 ↔ GroundReachable W g := by
  constructor
  · intro hdet i
    by_contra hnot
    push Not at hnot
    apply hdet
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun a => if Reach W i a then 1 else 0, ?_,
      grounded_mulVec_component_eq_zero hW hpos hg hnot⟩
    intro h
    have := congrFun h i
    simp only [Pi.zero_apply] at this
    rw [ite_eq_left (show Reach W i i from Relation.ReflTransGen.refl)] at this
    exact one_ne_zero this
  · exact grounded_det_ne_zero hpos hg

end Singular

/-! ## Network blocks -/

/-- Weights among non-machine buses. -/
def Wbb (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) : Matrix β β ℝ := W.submatrix Sum.inl Sum.inl

/-- Weights from non-machine to machine buses. -/
def Wbg (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) : Matrix β γ ℝ := W.submatrix Sum.inl Sum.inr

/-- Total coupling of each non-machine bus to the machine buses. -/
def machineCoupling (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) (b : β) : ℝ := ∑ g, W (.inl b) (.inr g)

/-- Block `B_bb` of the network Laplacian. -/
def Bbb (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) : Matrix β β ℝ := (laplacian W).submatrix Sum.inl Sum.inl

/-- Block `B_bg` of the network Laplacian. -/
def Bbg (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) : Matrix β γ ℝ := (laplacian W).submatrix Sum.inl Sum.inr

/-- Frequency-divider matrix `D_fd = -B_bb⁻¹ B_bg`. -/
def Dfd (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) : Matrix β γ ℝ := -((Bbb W)⁻¹ * Bbg W)

/-- Machine-bus connectivity: every non-machine bus reaches a machine bus. -/
def MachineConnected (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) : Prop := ∀ b, ∃ g, Reach W (.inl b) (.inr g)

@[powerlib_foundation] theorem Bbb_eq_grounded (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) :
    Bbb W = grounded (Wbb W) (machineCoupling W) := by
  ext i j
  simp only [Bbb, submatrix_apply, grounded, laplacian, Wbb, machineCoupling,
    Matrix.add_apply, Matrix.sub_apply, diagonal_apply, Fintype.sum_sum_type, Sum.inl.injEq]
  by_cases h : i = j
  · subst h; simp; ring
  · simp [h]

@[powerlib_foundation] theorem Bbg_eq (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ) : Bbg W = -Wbg W := by
  ext i g
  simp [Bbg, Wbg, laplacian_apply]

omit [Fintype β] [DecidableEq β] [DecidableEq γ] in
@[powerlib_foundation] theorem machineConnected_iff_groundReachable
    {W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ} (hpos : ∀ i j, 0 ≤ W i j) :
    GroundReachable (Wbb W) (machineCoupling W) ↔ MachineConnected W := by
  constructor
  · intro h b
    obtain ⟨k, hk, hgk⟩ := h b
    obtain ⟨g, hg⟩ : ∃ g, 0 < W (.inl k) (.inr g) := by
      by_contra hall
      push Not at hall
      have : machineCoupling W k ≤ 0 := Finset.sum_nonpos fun g _ => hall g
      linarith
    refine ⟨g, ?_⟩
    have hlift : ∀ a c, Reach (Wbb W) a c → Reach W (.inl a) (.inl c) := by
      intro a c hac
      induction hac with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hst ih => exact ih.tail hst
    exact (hlift b k hk).tail hg
  · intro h b
    obtain ⟨g, hg⟩ := h b
    -- first-hit argument along the path from `inl b` to `inr g`
    have key : ∀ a, Reach W a (.inr g) → ∀ i, a = .inl i →
        ∃ k, Reach (Wbb W) i k ∧ 0 < machineCoupling W k := by
      intro a ha
      induction ha using Relation.ReflTransGen.head_induction_on with
      | refl => intro i hi; cases hi
      | @head a c hac _ ih =>
        intro i hi
        subst hi
        rcases c with i' | g'
        · obtain ⟨k, hk, hgk⟩ := ih i' rfl
          exact ⟨k, Relation.ReflTransGen.head hac hk, hgk⟩
        · refine ⟨i, Relation.ReflTransGen.refl, ?_⟩
          exact hac.trans_le (Finset.single_le_sum (f := fun g => W (.inl i) (.inr g))
            (fun g _ => hpos _ _) (Finset.mem_univ g'))
    exact key _ hg b rfl

/-- `B_bb` is nonsingular iff every non-machine bus is connected to a machine bus. -/
@[powerlib_foundation] theorem Bbb_det_ne_zero_iff {W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ}
    (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j) :
    (Bbb W).det ≠ 0 ↔ MachineConnected W := by
  rw [Bbb_eq_grounded, grounded_det_ne_zero_iff (W := Wbb W) (g := machineCoupling W)
    (fun i j => by simp only [Wbb, submatrix_apply]; exact hW _ _) (fun i j => hpos _ _)
    (fun b => Finset.sum_nonneg fun g _ => hpos _ _), machineConnected_iff_groundReachable hpos]

/-! ## The frequency divider -/

variable {W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ}

@[powerlib_foundation] theorem laplacian_mulVec_inl (W : Matrix (β ⊕ γ) (β ⊕ γ) ℝ)
    (θ : β ⊕ γ → ℝ) (b : β) :
    (laplacian W *ᵥ θ) (.inl b) =
      (Bbb W *ᵥ (θ ∘ Sum.inl)) b + (Bbg W *ᵥ (θ ∘ Sum.inr)) b := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Bbb, Bbg]

/-- Static divider: zero injection perturbations at non-machine buses force
`Δθ_b = D_fd Δθ_g`. -/
@[powerlib_foundation] theorem nonMachine_angles (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : MachineConnected W) {θ : β ⊕ γ → ℝ}
    (hP : ∀ b, (laplacian W *ᵥ θ) (.inl b) = 0) :
    θ ∘ Sum.inl = Dfd W *ᵥ (θ ∘ Sum.inr) := by
  have hunit : IsUnit (Bbb W).det := by
    rw [Bbb_eq_grounded]
    exact (isUnit_iff_isUnit_det _).mp (grounded_isUnit (fun _ _ => hpos _ _)
      (fun b => Finset.sum_nonneg fun g _ => hpos _ _)
      ((machineConnected_iff_groundReachable hpos).mpr hconn))
  have hB : Bbb W *ᵥ (θ ∘ Sum.inl) = -(Bbg W *ᵥ (θ ∘ Sum.inr)) := by
    funext b
    have := hP b
    rw [laplacian_mulVec_inl] at this
    simp only [Pi.neg_apply]
    linarith
  calc θ ∘ Sum.inl = (Bbb W)⁻¹ *ᵥ (Bbb W *ᵥ (θ ∘ Sum.inl)) := by
        rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
    _ = Dfd W *ᵥ (θ ∘ Sum.inr) := by
        rw [hB, Dfd, mulVec_neg, neg_mulVec, mulVec_mulVec]

/-- **Frequency divider.** Along any differentiable angle-deviation trajectory with zero
injection perturbation at every non-machine bus, `Δω_b(t) = D_fd Δω_g(t)`. -/
@[powerlib_foundation] theorem frequencyDivider (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : MachineConnected W) {θ ω : ℝ → β ⊕ γ → ℝ} {t : ℝ}
    (hθ : ∀ s, HasDerivAt θ (ω s) s)
    (hP : ∀ s b, (laplacian W *ᵥ θ s) (.inl b) = 0) :
    ω t ∘ Sum.inl = Dfd W *ᵥ (ω t ∘ Sum.inr) := by
  have heq : (fun s => θ s ∘ Sum.inl) = fun s => Dfd W *ᵥ (θ s ∘ Sum.inr) :=
    funext fun s => nonMachine_angles hpos hconn (hP s)
  have hb : HasDerivAt (fun s => θ s ∘ Sum.inl) (ω t ∘ Sum.inl) t := by
    rw [hasDerivAt_pi]
    intro b
    exact (hasDerivAt_pi.mp (hθ t)) (.inl b)
  have hg : HasDerivAt (fun s => θ s ∘ Sum.inr) (ω t ∘ Sum.inr) t := by
    rw [hasDerivAt_pi]
    intro g
    exact (hasDerivAt_pi.mp (hθ t)) (.inr g)
  have hD : HasDerivAt (fun s => Dfd W *ᵥ (θ s ∘ Sum.inr)) (Dfd W *ᵥ (ω t ∘ Sum.inr)) t := by
    have := (Matrix.toLin' (Dfd W)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hg
    exact this
  rw [heq] at hb
  exact hb.unique hD

/-- The divider weights are nonnegative. -/
@[powerlib_foundation] theorem Dfd_nonneg (hpos : ∀ i j, 0 ≤ W i j) (hconn : MachineConnected W)
    (b : β) (g : γ) : 0 ≤ Dfd W b g := by
  simp only [Dfd, Bbg_eq, Matrix.mul_neg, neg_neg, Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg
  · rw [Bbb_eq_grounded]
    exact grounded_inv_nonneg (fun _ _ => hpos _ _) (fun b => Finset.sum_nonneg fun g _ => hpos _ _)
      ((machineConnected_iff_groundReachable hpos).mpr hconn) b k
  · exact hpos _ _

/-- Each row of the divider sums to one. -/
@[powerlib_foundation] theorem Dfd_row_sum (hpos : ∀ i j, 0 ≤ W i j) (hconn : MachineConnected W)
    (b : β) : ∑ g, Dfd W b g = 1 := by
  have hreach := (machineConnected_iff_groundReachable hpos).mpr hconn
  have hunit : IsUnit (Bbb W).det := by
    rw [Bbb_eq_grounded]
    exact (isUnit_iff_isUnit_det _).mp (grounded_isUnit (fun _ _ => hpos _ _)
      (fun b => Finset.sum_nonneg fun g _ => hpos _ _) hreach)
  have h1 : Bbb W *ᵥ (fun _ => (1 : ℝ)) = -(Bbg W *ᵥ (fun _ => (1 : ℝ))) := by
    have h := laplacian_mulVec_const W 1
    funext b
    have hb := congrFun h (.inl b)
    rw [laplacian_mulVec_inl] at hb
    simp only [Pi.neg_apply, Pi.zero_apply] at hb ⊢
    have e1 : ((fun _ : β ⊕ γ => (1 : ℝ)) ∘ Sum.inl) = fun _ => 1 := rfl
    have e2 : ((fun _ : β ⊕ γ => (1 : ℝ)) ∘ Sum.inr) = fun _ => 1 := rfl
    rw [e1, e2] at hb
    linarith
  have h2 : Dfd W *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    rw [Dfd, neg_mulVec, ← mulVec_mulVec, ← mulVec_neg, ← h1, mulVec_mulVec,
      nonsing_inv_mul _ hunit, one_mulVec]
  have := congrFun h2 b
  simpa [mulVec, dotProduct] using this

/-- Every non-machine bus frequency deviation is bounded above by the largest machine
frequency deviation. -/
@[powerlib_foundation] theorem busFrequency_le (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : MachineConnected W) {ωg : γ → ℝ} {c : ℝ} (hc : ∀ g, ωg g ≤ c) (b : β) :
    (Dfd W *ᵥ ωg) b ≤ c := by
  calc (Dfd W *ᵥ ωg) b = ∑ g, Dfd W b g * ωg g := rfl
    _ ≤ ∑ g, Dfd W b g * c :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hc g) (Dfd_nonneg hpos hconn b g)
    _ = c := by rw [← Finset.sum_mul, Dfd_row_sum hpos hconn, one_mul]

/-- Every non-machine bus frequency deviation is bounded below by the smallest machine
frequency deviation. -/
@[powerlib_foundation] theorem le_busFrequency (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : MachineConnected W) {ωg : γ → ℝ} {c : ℝ} (hc : ∀ g, c ≤ ωg g) (b : β) :
    c ≤ (Dfd W *ᵥ ωg) b := by
  calc c = ∑ g, Dfd W b g * c := by rw [← Finset.sum_mul, Dfd_row_sum hpos hconn, one_mul]
    _ ≤ ∑ g, Dfd W b g * ωg g :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hc g) (Dfd_nonneg hpos hconn b g)
    _ = (Dfd W *ᵥ ωg) b := rfl

/-- Common mode: if all machines share one frequency deviation, every bus has it. -/
@[powerlib_foundation] theorem busFrequency_commonMode (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : MachineConnected W) (c : ℝ) (b : β) :
    (Dfd W *ᵥ (fun _ => c)) b = c :=
  le_antisymm (busFrequency_le hpos hconn (fun _ => le_rfl) b)
    (le_busFrequency hpos hconn (fun _ => le_rfl) b)

/-- In common mode the deviation of each bus frequency from the COI frequency
`∑ w_g ω_g` (weights summing to one) vanishes. -/
@[powerlib_foundation] theorem busFrequency_sub_coi_commonMode (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : MachineConnected W) {wH : γ → ℝ} (hw : ∑ g, wH g = 1) (c : ℝ) (b : β) :
    (Dfd W *ᵥ (fun _ => c)) b - ∑ g, wH g * c = 0 := by
  rw [busFrequency_commonMode hpos hconn, ← Finset.sum_mul, hw, one_mul, sub_self]

/-- Modal map: a machine-frequency mode shape `v` appears at the buses as `D_fd v`,
linearly in the modal amplitudes. -/
@[powerlib_foundation] theorem busFrequency_modal {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (v : ι → γ → ℝ) :
    Dfd W *ᵥ (∑ i, a i • v i) = ∑ i, a i • (Dfd W *ᵥ v i) := by
  rw [Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_smul _ _ _

end powerlib.Network
