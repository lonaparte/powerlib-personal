import theorem.PhasePlane.Conservative

/-! # The undamped pendulum `θ̈ + ω₀² sin θ = 0`

Foundation layer (a canonical textbook system, not a power-system model).

Model boundary. State `(θ, ω) = (y 0, y 1) ∈ State 2` with the angle `θ ∈ ℝ` unwrapped (not on
the circle), constant `ω₀ ≠ 0`, no damping, input or noise; continuous time. The field is
`Conservative.field 1 0 (ω₀² sin)`, i.e. `θ̇ = ω`, `ω̇ = −ω₀² sin θ`, with potential
`V(θ) = ω₀² (1 − cos θ)` (engineering convention `V_min = 0`) and energy `E = ω²/2 + V(θ)`.

Results.
* Energy is conserved along every solution.
* `(0, 0)` is Lyapunov stable (strict minimum of `V` on `(−π, π)`).
* `(π, 0)` is unstable: the Jacobian there is `!![0, 1; ω₀², 0]` with `det = −ω₀² < 0` (saddle).
* Separatrix energy `E(π, 0) = 2ω₀²`.
* Libration/rotation dichotomy on every solution segment: if `E < 2ω₀²` and `|θ(a)| < π` then
  `|θ(t)| < π` throughout; if `E > 2ω₀²` then `ω` never vanishes, keeps its sign, and
  `|θ(t) − θ(a)| ≥ √(2(E − 2ω₀²)) (t − a)` (the angle runs away linearly).

Source: work-sync theory/T-nonlinear-phase-plane.md §1.2–1.3, theory/T-dynamical-systems.md
(codes example: pendulum equilibria, energy).
-/

noncomputable section
namespace powerlib.PhasePlane.Pendulum
open Set Filter Topology
open powerlib.Dynamics (State)
open powerlib.PhasePlane

/-- Potential `V(θ) = ω₀² (1 − cos θ)`. -/
def potential (ω₀ θ : ℝ) : ℝ := ω₀ ^ 2 * (1 - Real.cos θ)

/-- Restoring torque `V'(θ) = ω₀² sin θ`. -/
def torque (ω₀ θ : ℝ) : ℝ := ω₀ ^ 2 * Real.sin θ

/-- The pendulum field `θ̇ = ω`, `ω̇ = −ω₀² sin θ`. -/
def field (ω₀ : ℝ) : State 2 → State 2 := Conservative.field 1 0 (torque ω₀)

/-- Energy `ω²/2 + ω₀²(1 − cos θ)`. -/
def energy (ω₀ : ℝ) : State 2 → ℝ := Conservative.energy 1 (potential ω₀)

@[powerlib_foundation] theorem hasDerivAt_potential (ω₀ θ : ℝ) :
    HasDerivAt (potential ω₀) (torque ω₀ θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_sub 1).const_mul (ω₀ ^ 2)
  unfold potential torque
  convert h using 1
  ring

@[powerlib_foundation] theorem torque_contDiff (ω₀ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (torque ω₀) := by
  unfold torque; fun_prop

@[powerlib_foundation] theorem field_contDiff (ω₀ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (field ω₀) :=
  Conservative.field_contDiff (torque_contDiff ω₀)

@[powerlib_foundation] theorem energy_conserved (ω₀ : ℝ) {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field ω₀) a b) :
    ∀ t ∈ Icc a b, energy ω₀ (φ t) = energy ω₀ (φ a) :=
  Conservative.energy_conserved one_ne_zero (hasDerivAt_potential ω₀) hφ

@[powerlib_foundation] theorem potential_le (ω₀ θ : ℝ) : potential ω₀ θ ≤ 2 * ω₀ ^ 2 := by
  unfold potential
  nlinarith [Real.neg_one_le_cos θ, sq_nonneg ω₀]

@[powerlib_foundation] theorem potential_pos {ω₀ θ : ℝ} (hω : ω₀ ≠ 0) (h1 : |θ| < 2 * Real.pi)
    (h0 : θ ≠ 0) : 0 < potential ω₀ θ := by
  unfold potential
  have hc : Real.cos θ < 1 := by
    rcases lt_or_eq_of_le (Real.cos_le_one θ) with h | h
    · exact h
    · exact absurd ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [neg_abs_le θ])
        (by linarith [le_abs_self θ])).mp h) h0
  have : 0 < ω₀ ^ 2 := by positivity
  nlinarith

/-- The lower equilibrium `(0, 0)` is Lyapunov stable. -/
@[powerlib_foundation] theorem origin_lyapunovStable {ω₀ : ℝ} (hω : ω₀ ≠ 0) :
    LyapunovStable (field ω₀) (mk 0 0) :=
  Conservative.center_lyapunovStable one_pos le_rfl (hasDerivAt_potential ω₀) Real.pi_pos
    (fun θ hθ hne => by
      have : potential ω₀ 0 = 0 := by simp [potential]
      rw [this]
      exact potential_pos hω (by rw [sub_zero] at hθ; linarith [Real.pi_pos]) hne)

/-- Jacobian of the pendulum field. -/
@[powerlib_foundation] theorem hasFDerivAt_field (ω₀ : ℝ) (y : State 2) :
    HasFDerivAt (field ω₀)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![0, 1; -(ω₀ ^ 2 * Real.cos (y 0)), 0]) y := by
  refine hasFDerivAt_of_components _ ![coord 1, (-(ω₀ ^ 2 * Real.cos (y 0))) • coord 0] ?_ ?_
  · intro i; fin_cases i
    · show HasFDerivAt (fun z => field ω₀ z 0) (coord 1) y
      exact hasFDerivAt_coord 1 y
    · show HasFDerivAt (fun z => field ω₀ z 1) ((-(ω₀ ^ 2 * Real.cos (y 0))) • coord 0) y
      have h0 := hasFDerivAt_coord 0 y
      have h : HasFDerivAt (fun z : State 2 => -(ω₀ ^ 2 * Real.sin (z 0))) _ y :=
        ((Real.hasDerivAt_sin (y 0)).comp_hasFDerivAt y h0).const_mul (ω₀ ^ 2) |>.neg
      have hf : (fun z => field ω₀ z 1) = fun z : State 2 => -(ω₀ ^ 2 * Real.sin (z 0)) := by
        funext z; simp [field, torque]
      rw [hf]
      convert h using 1
      ext v; simp; ring
  · intro i v; fin_cases i <;> simp

/-- The upper equilibrium `(π, 0)` is a saddle, hence unstable. -/
@[powerlib_foundation] theorem top_unstable {ω₀ : ℝ} (hω : ω₀ ≠ 0) :
    Unstable (field ω₀) (mk Real.pi 0) := by
  refine Criteria.unstable_of_jacobian_det_neg_fin_two _ (field_contDiff ω₀) ?_
    (hasFDerivAt_field ω₀ (mk Real.pi 0)).fderiv ?_
  · rw [field, Conservative.field_eq_zero_iff one_ne_zero]; simp [torque]
  · simp [Matrix.det_fin_two]; positivity

/-- Separatrix energy `E(π, 0) = 2ω₀²`. -/
@[powerlib_foundation] theorem separatrix_energy (ω₀ : ℝ) : energy ω₀ (mk Real.pi 0) = 2 * ω₀ ^ 2 := by
  simp [energy, Conservative.energy, potential]; ring

/-- Libration: below the separatrix energy a solution started in `(−π, π)` never reaches `±π`. -/
@[powerlib_foundation] theorem libration (ω₀ : ℝ) {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field ω₀) a b) (hE : energy ω₀ (φ a) < 2 * ω₀ ^ 2)
    (hθ : |φ a 0| < Real.pi) :
    ∀ t ∈ Icc a b, |φ t 0| < Real.pi := by
  intro t ht
  by_contra hle
  push Not at hle
  have hcont : ContinuousOn (fun s => |φ s 0|) (Icc a t) :=
    (((coord 0).continuous.comp_continuousOn hφ.continuousOn).abs).mono
      (Icc_subset_Icc_right ht.2)
  obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc ht.1 hcont ⟨hθ.le, hle⟩
  have hsmem : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
  have hcons := energy_conserved ω₀ hφ s hsmem
  have hcos : Real.cos (φ s 0) = -1 := by
    rcases abs_eq Real.pi_pos.le |>.mp hseq with h | h <;> rw [h] <;> simp
  have : 2 * ω₀ ^ 2 ≤ energy ω₀ (φ s) := by
    simp only [energy, Conservative.energy, potential, hcos]
    nlinarith [sq_nonneg (φ s 1)]
  linarith

/-- Rotation: above the separatrix energy the angular velocity never vanishes and the angle
advances at least linearly. -/
@[powerlib_foundation] theorem rotation (ω₀ : ℝ) {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field ω₀) a b) (hE : 2 * ω₀ ^ 2 < energy ω₀ (φ a)) :
    (∀ t ∈ Icc a b, φ t 1 ≠ 0) ∧
      ∀ t ∈ Icc a b, √(2 * (energy ω₀ (φ a) - 2 * ω₀ ^ 2)) * (t - a) ≤ |φ t 0 - φ a 0| := by
  set c := √(2 * (energy ω₀ (φ a) - 2 * ω₀ ^ 2))
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hvsq : ∀ t ∈ Icc a b, c ^ 2 ≤ φ t 1 ^ 2 := by
    intro t ht
    have hcons := energy_conserved ω₀ hφ t ht
    have hV := potential_le ω₀ (φ t 0)
    rw [Real.sq_sqrt (by linarith)]
    simp only [energy, Conservative.energy] at hcons ⊢
    linarith
  have hne : ∀ t ∈ Icc a b, φ t 1 ≠ 0 := by
    intro t ht h0
    have := hvsq t ht
    rw [h0] at this
    nlinarith
  refine ⟨hne, ?_⟩
  have hv1 : ContinuousOn (fun s => φ s 1) (Icc a b) :=
    (coord 1).continuous.comp_continuousOn hφ.continuousOn
  -- the sign of `ω` is constant
  have hsign : (∀ t ∈ Icc a b, c ≤ φ t 1) ∨ ∀ t ∈ Icc a b, φ t 1 ≤ -c := by
    rcases lt_or_ge b a with hba | hab
    · left; intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hba)
    rcases lt_or_gt_of_ne (hne a ⟨le_rfl, hab⟩) with h | h
    · right
      intro t ht
      have hneg : φ t 1 < 0 := by
        by_contra hpos
        push Not at hpos
        obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.1 (hv1.mono (Icc_subset_Icc_right ht.2))
          ⟨h.le, hpos⟩
        exact hne s ⟨hs.1, hs.2.trans ht.2⟩ hs0
      nlinarith [hvsq t ht]
    · left
      intro t ht
      have hpos : 0 < φ t 1 := by
        by_contra hneg
        push Not at hneg
        obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 (hv1.mono (Icc_subset_Icc_right ht.2))
          ⟨hneg, h.le⟩
        exact hne s ⟨hs.1, hs.2.trans ht.2⟩ hs0
      nlinarith [hvsq t ht]
  have hθd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => φ s 0) (φ t 1) (Icc a b) t := fun t ht =>
    (hasDerivWithinAt_iff_components.mp (hφ t ht)).1
  intro t ht
  rcases hsign with hs | hs
  · have hmono : MonotoneOn (fun s => φ s 0 - c * s) (Icc a b) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := fun s => φ s 1 - c)
      · exact fun s hs' => ((hθd s hs').sub ((hasDerivAt_id s).const_mul c).hasDerivWithinAt
          |>.continuousWithinAt).congr (fun _ _ => by simp) (by simp)
      · intro s hs'
        rw [interior_Icc] at hs'
        have h := (hθd s (Ioo_subset_Icc_self hs')).sub
          ((hasDerivAt_id s).const_mul c).hasDerivWithinAt
        simp only [id, mul_one] at h
        exact (h.mono Ioo_subset_Icc_self).mono_of_mem_nhdsWithin
          (by rw [interior_Icc]; exact self_mem_nhdsWithin)
      · intro s hs'
        rw [interior_Icc] at hs'
        linarith [hs s (Ioo_subset_Icc_self hs')]
    have := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
    simp only at this
    rw [abs_of_nonneg (by nlinarith [ht.1])]
    linarith
  · have hanti : AntitoneOn (fun s => φ s 0 + c * s) (Icc a b) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (f' := fun s => φ s 1 + c)
      · exact fun s hs' => ((hθd s hs').add ((hasDerivAt_id s).const_mul c).hasDerivWithinAt
          |>.continuousWithinAt).congr (fun _ _ => by simp) (by simp)
      · intro s hs'
        rw [interior_Icc] at hs'
        have h := (hθd s (Ioo_subset_Icc_self hs')).add
          ((hasDerivAt_id s).const_mul c).hasDerivWithinAt
        simp only [id, mul_one] at h
        exact (h.mono Ioo_subset_Icc_self).mono_of_mem_nhdsWithin
          (by rw [interior_Icc]; exact self_mem_nhdsWithin)
      · intro s hs'
        rw [interior_Icc] at hs'
        linarith [hs s (Ioo_subset_Icc_self hs')]
    have := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
    simp only at this
    rw [abs_of_nonpos (by nlinarith [ht.1]), neg_sub]
    linarith

end powerlib.PhasePlane.Pendulum
