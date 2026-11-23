import theorem.Dynamics.State

/-! # One transport law for the Flow sentences: the space-time map

The space-time map `(t, x) ↦ (t / c, T x + b)` (`c > 0`, `T : State n ≃L[ℝ] State n` invertible,
`b` arbitrary) carries the solutions of `ẋ = f(x)` to those of the field
`c • transportField T b f`, `y ↦ c T f(T⁻¹ (y − b))`, in the time `τ = t / c` and the coordinates
`y = T x + b`. Every behavioural sentence of the Flow semantics is transported here once, with its
decay rate scaled by `c` (`holds_spaceTime_iff`). Moving an equilibrium to the origin
(`Flow.Property.holds_shift_iff`: `c = 1`, `T = 1`), affine changes of coordinates
(`holds_transport_iff`: `c = 1`) and a constant time scale (`holds_timeScale_iff`: `T = 1`,
`b = 0`) are its instances.

Scope.
* Generic foundation, independent of any model: autonomous fields `f : State n → State n` on
  `State n = EuclideanSpace ℝ (Fin n)`, read through the Flow semantics
  (`theorem/Flow/Defs.lean`). No linearization is involved.
* Excluded: time-varying or nonlinear changes of coordinates, state-dependent time scaling,
  non-autonomous or forced systems.

Source: work-sync `theory/T-PU.md` §1.2 / §1.5 (per-unit scaling of states = constant diagonal
change of coordinates), §1.6 (time base `t̂ = ω_B t`: the per-unit-time field is `ω_B⁻¹ • f`);
`theory/T-dynamical-systems.md` §1.3 (deviation coordinates `ξ = x − x*` about an equilibrium).

Results.
* `affineCoord T b x = T x + b` and `transportField T b f y = T f(T⁻¹ (y − b))`; the space-time
  field is `c • transportField T b f`, inverted by the space-time map of `(c⁻¹, T⁻¹, −T⁻¹ b)`
  (`smul_transportField_symm`, `affineCoord_symm_affineCoord`).
* Solutions: if `φ` solves `f` on `s`, then `τ ↦ T φ(c τ) + b` solves the space-time field on
  `(c ·)⁻¹' s` (`isIntegralCurveOn_spaceTime`).
* Each sentence once, read back from the space-time field at `T x + b` to `f` at `x`: equilibria
  (`isEquilibrium_spaceTime_iff`), forward completeness, Lyapunov stability, local asymptotic
  stability, LeanForControl's global asymptotic stability, conservation (with the energy read
  through the map), local and global exponential stability (overshoot multiplied by
  `max 1 (‖T‖ ‖T⁻¹‖)`, rate divided by `c`) and decay (rate `c a` read as `a`): the lemmas
  `*_of_spaceTime`. Sampled contraction of the space-time field is contraction of `f` over a
  horizon `c k`, `k` a positive integer (`sampledContraction_spaceTime_iff`).
* `Flow.Property.timeScale c`: the sentence read in the time `t / c` (a decay rate `a` becomes
  `c a`). **Space-time law** `holds_spaceTime_iff`: `P.timeScale c` holds for the space-time field
  at `T x + b` exactly when `P` holds for `f` at `x`; for `c ≠ 1` sampled contraction is excluded
  (its integer horizon need not stay an integer).
-/

noncomputable section

namespace powerlib.Flow

/-- The sentence `P` read in the time `τ = t / c`: a decay rate `a` becomes `c a`; every other
sentence keeps its form. -/
def Property.timeScale (c : ℝ) : Property → Property
  | .decay a => .decay (c * a)
  | P => P

@[tmio T, simp, powerlib_foundation] theorem Property.timeScale_decay (c a : ℝ) :
    (Property.decay a).timeScale c = .decay (c * a) := rfl

@[tmio T, simp, powerlib_foundation] theorem Property.timeScale_one (P : Property) :
    P.timeScale 1 = P := by
  cases P <;> simp [Property.timeScale]

@[tmio T, simp, powerlib_foundation] theorem Property.timeScale_timeScale (P : Property)
    (c d : ℝ) : (P.timeScale c).timeScale d = P.timeScale (d * c) := by
  cases P <;> simp [Property.timeScale, mul_assoc]

/-- Time scaling keeps the attractive sentences. -/
@[tmio T, simp, powerlib_foundation] theorem Property.attractive_timeScale (P : Property) (c : ℝ) :
    (P.timeScale c).Attractive ↔ P.Attractive := by
  cases P <;> rfl

end powerlib.Flow

namespace powerlib.Dynamics
open Set Filter Topology

variable {n : ℕ}

/-- The affine coordinate change `y = T x + c`. -/
def affineCoord (T : State n ≃L[ℝ] State n) (c : State n) (x : State n) : State n :=
  T x + c

/-- The vector field in the coordinates `y = T x + c`: `g(y) = T f(T⁻¹ (y − c))`. -/
def transportField (T : State n ≃L[ℝ] State n) (c : State n) (f : State n → State n)
    (y : State n) : State n :=
  T (f (T.symm (y - c)))

@[tmio T, simp, powerlib_foundation] theorem affineCoord_symm_affineCoord
    (T : State n ≃L[ℝ] State n) (c : State n) (x : State n) :
    affineCoord T.symm (-(T.symm c)) (affineCoord T c x) = x := by
  simp [affineCoord]

/-- The space-time map of `(c⁻¹, T⁻¹, −T⁻¹ b)` inverts that of `(c, T, b)`. -/
@[tmio T, simp, powerlib_foundation] theorem smul_transportField_symm {c : ℝ} (hc : c ≠ 0)
    (T : State n ≃L[ℝ] State n) (b : State n) (f : State n → State n) :
    c⁻¹ • transportField T.symm (-(T.symm b)) (c • transportField T b f) = f := by
  funext y
  simp [transportField, smul_smul, inv_mul_cancel₀ hc]

/-- **Solutions under the space-time map.** A solution `φ` of `f` on `s`, read at `t = c τ` in the
coordinates `y = T x + b`, solves the space-time field on `(c ·)⁻¹' s`. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_spaceTime (c : ℝ)
    (T : State n ≃L[ℝ] State n) (b : State n) {f : State n → State n} {φ : ℝ → State n}
    {s : Set ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) s) :
    IsIntegralCurveOn (fun τ => affineCoord T b (φ (c * τ)))
      (fun _ y => (c • transportField T b f) y) ((c * ·) ⁻¹' s) := by
  intro τ hτ
  have h := (hφ (c * τ) hτ).scomp τ (hasDerivAt_const_mul c).hasDerivWithinAt (mapsTo_preimage _ _)
  have h' := (T.hasFDerivAt.comp_hasDerivWithinAt τ h).add_const b
  convert h' using 1
  · rfl
  · simp [transportField, affineCoord]

section Estimates

variable (T : State n ≃L[ℝ] State n) (b : State n)

@[tmio T, powerlib_foundation] private lemma mul_div_add_one_lt {K r : ℝ} (hK : 0 ≤ K)
    (hr : 0 < r) : K * (r / (K + 1)) < r := by
  rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
  nlinarith

@[tmio T, powerlib_foundation] private lemma norm_affineCoord_sub_le (u x : State n) :
    ‖affineCoord T b u - affineCoord T b x‖ ≤ ‖(T : State n →L[ℝ] State n)‖ * ‖u - x‖ := by
  simpa [affineCoord, ← map_sub] using (T : State n →L[ℝ] State n).le_opNorm (u - x)

@[tmio T, powerlib_foundation] private lemma norm_sub_le_affineCoord (u x : State n) :
    ‖u - x‖ ≤ ‖(T.symm : State n →L[ℝ] State n)‖ * ‖affineCoord T b u - affineCoord T b x‖ := by
  simpa [affineCoord, ← map_sub] using (T.symm : State n →L[ℝ] State n).le_opNorm (T (u - x))

@[tmio T, powerlib_foundation] private lemma norm_affineCoord_sub_lt {u x : State n} {r : ℝ}
    (hr : 0 < r) (h : ‖u - x‖ < r / (‖(T : State n →L[ℝ] State n)‖ + 1)) :
    ‖affineCoord T b u - affineCoord T b x‖ < r :=
  (norm_affineCoord_sub_le T b u x).trans_lt <|
    (mul_le_mul_of_nonneg_left h.le (norm_nonneg _)).trans_lt
      (mul_div_add_one_lt (norm_nonneg _) hr)

@[tmio T, powerlib_foundation] private lemma norm_sub_lt_of_affineCoord {u x : State n} {r : ℝ}
    (hr : 0 < r)
    (h : ‖affineCoord T b u - affineCoord T b x‖ < r / (‖(T.symm : State n →L[ℝ] State n)‖ + 1)) :
    ‖u - x‖ < r :=
  (norm_sub_le_affineCoord T b u x).trans_lt <|
    (mul_le_mul_of_nonneg_left h.le (norm_nonneg _)).trans_lt
      (mul_div_add_one_lt (norm_nonneg _) hr)

/-- A bound read on the image gives one on the solution, the factor multiplied by
`max 1 (‖T‖ ‖T⁻¹‖)`. -/
@[tmio T, powerlib_foundation] private lemma norm_sub_le_of_affineCoord {u u₀ x : State n} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ‖affineCoord T b u - affineCoord T b x‖ ≤ C * ‖affineCoord T b u₀ - affineCoord T b x‖) :
    ‖u - x‖ ≤ max 1 (‖(T : State n →L[ℝ] State n)‖ * ‖(T.symm : State n →L[ℝ] State n)‖) * C *
      ‖u₀ - x‖ := by
  have hK : 0 ≤ ‖(T.symm : State n →L[ℝ] State n)‖ := norm_nonneg _
  calc ‖u - x‖ ≤ ‖(T.symm : State n →L[ℝ] State n)‖ * (C * (‖(T : State n →L[ℝ] State n)‖ *
        ‖u₀ - x‖)) :=
      (norm_sub_le_affineCoord T b u x).trans <| mul_le_mul_of_nonneg_left
        (h.trans (mul_le_mul_of_nonneg_left (norm_affineCoord_sub_le T b u₀ x) hC)) hK
    _ = ‖(T : State n →L[ℝ] State n)‖ * ‖(T.symm : State n →L[ℝ] State n)‖ * (C * ‖u₀ - x‖) := by
      ring
    _ ≤ _ := by
      rw [mul_assoc _ C]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Estimates

/-- A contraction over the horizon `h ≥ 0` iterates to the horizon `j h`, with the factor `ρʲ`
(`ρ` replaced by `max ρ 0`). -/
@[tmio T, powerlib_foundation] private lemma contraction_iterate {g : State n → State n}
    {x : State n} {h ρ : ℝ} (hh : 0 ≤ h)
    (hcon : ∀ (t₀ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ g t₀ (t₀ + h) →
      ‖φ (t₀ + h) - x‖ ≤ ρ * ‖φ t₀ - x‖) (j : ℕ) :
    ∀ (t₀ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ g t₀ (t₀ + j * h) →
      ‖φ (t₀ + j * h) - x‖ ≤ max ρ 0 ^ j * ‖φ t₀ - x‖ := by
  induction j with
  | zero => intro t₀ φ _; simp
  | succ j ih =>
    intro t₀ φ hφ
    have hj : (0 : ℝ) ≤ j * h := mul_nonneg (Nat.cast_nonneg j) hh
    have hsplit : t₀ + ((j + 1 : ℕ) : ℝ) * h = t₀ + j * h + h := by push_cast; ring
    rw [hsplit] at hφ ⊢
    have h1 := ih t₀ φ (hφ.mono (Icc_subset_Icc le_rfl (by linarith)))
    have h2 := hcon (t₀ + j * h) φ (hφ.mono (Icc_subset_Icc (by linarith) le_rfl))
    calc ‖φ (t₀ + j * h + h) - x‖ ≤ ρ * ‖φ (t₀ + j * h) - x‖ := h2
      _ ≤ max ρ 0 * ‖φ (t₀ + j * h) - x‖ := by gcongr; exact le_max_left _ _
      _ ≤ max ρ 0 * (max ρ 0 ^ j * ‖φ t₀ - x‖) := by gcongr
      _ = max ρ 0 ^ (j + 1) * ‖φ t₀ - x‖ := by ring

section Sentences

variable {c : ℝ} (hc : 0 < c) (T : State n ≃L[ℝ] State n) (b : State n)
  {f : State n → State n} {x : State n}
include hc

@[tmio T, powerlib_foundation] private lemma mem_Icc_div {t t₀ t₁ : ℝ} (ht : t ∈ Icc t₀ t₁) :
    t / c ∈ Icc (t₀ / c) (t₁ / c) :=
  ⟨div_le_div_of_nonneg_right ht.1 hc.le, div_le_div_of_nonneg_right ht.2 hc.le⟩

@[tmio T, powerlib_foundation] private lemma isTrajectoryOn_spaceTime {φ : ℝ → State n}
    {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁) :
    IsTrajectoryOn (fun τ => affineCoord T b (φ (c * τ))) (c • transportField T b f)
      (t₀ / c) (t₁ / c) := by
  have h := isIntegralCurveOn_spaceTime c T b hφ
  rwa [preimage_const_mul_Icc₀ _ _ hc] at h

@[tmio T, powerlib_foundation] private lemma tendsto_of_spaceTime {φ : ℝ → State n}
    (h : Tendsto (fun τ => affineCoord T b (φ (c * τ))) atTop (𝓝 (affineCoord T b x))) :
    Tendsto φ atTop (𝓝 x) := by
  have hT : Continuous fun y : State n => T.symm (y - b) :=
    T.symm.continuous.comp (continuous_sub_right b)
  have h2 := (hT.tendsto _).comp (h.comp (tendsto_id.atTop_div_const hc))
  simpa [Function.comp_def, affineCoord, mul_div_cancel₀ _ hc.ne'] using h2

/-- One exponential estimate read back through the space-time map: the rate is divided by `c`. -/
@[tmio T, powerlib_foundation] private lemma bound_of_spaceTime {φ : ℝ → State n} {t₀ t₁ C a : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ s ∈ Icc (t₀ / c) (t₁ / c), ‖affineCoord T b (φ (c * s)) - affineCoord T b x‖ ≤
      C * Real.exp (-a * (s - t₀ / c)) *
        ‖affineCoord T b (φ (c * (t₀ / c))) - affineCoord T b x‖) :
    ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ ≤
      max 1 (‖(T : State n →L[ℝ] State n)‖ * ‖(T.symm : State n →L[ℝ] State n)‖) * C *
        Real.exp (-(a / c) * (t - t₀)) * ‖φ t₀ - x‖ := by
  intro t ht
  have ht' := h (t / c) (mem_Icc_div hc ht)
  have hexp : -a * (t / c - t₀ / c) = -(a / c) * (t - t₀) := by ring
  rw [mul_div_cancel₀ _ hc.ne', mul_div_cancel₀ _ hc.ne', hexp] at ht'
  simpa only [mul_assoc] using
    norm_sub_le_of_affineCoord T b (mul_nonneg hC (Real.exp_pos _).le) ht'

@[tmio T, powerlib_foundation] theorem isEquilibrium_spaceTime_iff :
    IsEquilibrium (c • transportField T b f) (affineCoord T b x) ↔ IsEquilibrium f x := by
  simp [IsEquilibrium, transportField, affineCoord, hc.ne']

@[tmio T, powerlib_foundation] theorem forwardComplete_of_spaceTime
    (h : Flow.ForwardComplete (c • transportField T b f)) : Flow.ForwardComplete f := by
  intro t₀ x₀
  obtain ⟨χ, hχ0, hχ⟩ := h (t₀ / c) (affineCoord T b x₀)
  have hφ := isIntegralCurveOn_spaceTime c⁻¹ T.symm (-(T.symm b)) hχ
  have e : t₀ / c / c⁻¹ = t₀ := by field_simp
  rw [smul_transportField_symm hc.ne', preimage_const_mul_Ici₀ _ (inv_pos.mpr hc), e] at hφ
  refine ⟨_, ?_, hφ⟩
  show affineCoord T.symm (-(T.symm b)) (χ (c⁻¹ * t₀)) = x₀
  rw [inv_mul_eq_div, hχ0, affineCoord_symm_affineCoord]

@[tmio T, powerlib_foundation] theorem lyapunovStable_of_spaceTime
    (h : LyapunovStable (c • transportField T b f) (affineCoord T b x)) : LyapunovStable f x := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ε / (‖(T.symm : State n →L[ℝ] State n)‖ + 1)) (by positivity)
  refine ⟨δ / (‖(T : State n →L[ℝ] State n)‖ + 1), by positivity, fun t₀ t₁ φ hφ h0 t ht => ?_⟩
  have hχ := hb _ _ _ (isTrajectoryOn_spaceTime hc T b hφ)
    (by simpa only [mul_div_cancel₀ _ hc.ne'] using norm_affineCoord_sub_lt T b hδ h0)
    (t / c) (mem_Icc_div hc ht)
  simp only [mul_div_cancel₀ _ hc.ne'] at hχ
  exact norm_sub_lt_of_affineCoord T b hε hχ

@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_of_spaceTime
    (h : LocallyExponentiallyStable (c • transportField T b f) (affineCoord T b x)) :
    LocallyExponentiallyStable f x := by
  obtain ⟨r, C, a, hr, hC, ha, hdecay⟩ := h
  refine ⟨r / (‖(T : State n →L[ℝ] State n)‖ + 1),
    max 1 (‖(T : State n →L[ℝ] State n)‖ * ‖(T.symm : State n →L[ℝ] State n)‖) * C, a / c,
    by positivity,
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hC, div_pos ha hc,
    fun t₀ t₁ φ hφ h0 => bound_of_spaceTime hc T b (by linarith) ?_⟩
  exact hdecay _ _ _ (isTrajectoryOn_spaceTime hc T b hφ)
    (by simpa only [mul_div_cancel₀ _ hc.ne'] using norm_affineCoord_sub_lt T b hr h0)

@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_spaceTime
    (h : LocalAsymptoticStable (c • transportField T b f) (affineCoord T b x)) :
    LocalAsymptoticStable f x := by
  obtain ⟨hs, ρ, hρ, hattr⟩ := h
  refine ⟨lyapunovStable_of_spaceTime hc T b hs, ρ / (‖(T : State n →L[ℝ] State n)‖ + 1),
    by positivity, fun t₀ φ hφ h0 => tendsto_of_spaceTime hc T b (hattr (t₀ / c) _ ?_ ?_)⟩
  · simpa only [preimage_const_mul_Ici₀ _ hc] using isIntegralCurveOn_spaceTime c T b hφ
  · simpa only [mul_div_cancel₀ _ hc.ne'] using norm_affineCoord_sub_lt T b hρ h0

@[tmio T, powerlib_foundation] theorem globalAsymptoticStable_of_spaceTime
    (h : GlobalAsymptoticStable (c • transportField T b f) (affineCoord T b x)) :
    GlobalAsymptoticStable f x :=
  ⟨lyapunovStable_of_spaceTime hc T b h.1, fun t₀ φ hφ => tendsto_of_spaceTime hc T b
    (h.2 (t₀ / c) _ (by
      simpa only [preimage_const_mul_Ici₀ _ hc] using isIntegralCurveOn_spaceTime c T b hφ))⟩

@[tmio T, powerlib_foundation] theorem decay_of_spaceTime {a : ℝ}
    (h : Flow.Decay (c • transportField T b f) (affineCoord T b x) (c * a)) : Flow.Decay f x a := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max 1 (‖(T : State n →L[ℝ] State n)‖ * ‖(T.symm : State n →L[ℝ] State n)‖) * max C 0,
    fun t₀ t₁ φ hφ => ?_⟩
  have hb := bound_of_spaceTime hc T b (le_max_right C 0) (fun s hs =>
    (hC _ _ _ (isTrajectoryOn_spaceTime hc T b hφ) s hs).trans (by gcongr; exact le_max_left _ _))
  rwa [mul_div_cancel_left₀ _ hc.ne'] at hb

@[tmio T, powerlib_foundation] theorem globallyExponentiallyStable_of_spaceTime
    (h : Flow.GloballyExponentiallyStable (c • transportField T b f) (affineCoord T b x)) :
    Flow.GloballyExponentiallyStable f x := by
  obtain ⟨heq, hfc, a, ha, hd⟩ := h
  exact ⟨(isEquilibrium_spaceTime_iff hc T b).mp heq, forwardComplete_of_spaceTime hc T b hfc,
    a / c, div_pos ha hc, decay_of_spaceTime hc T b (by rwa [mul_div_cancel₀ a hc.ne'])⟩

/-- Conservation, with the energy read through the coordinate change. -/
@[tmio T, powerlib_foundation] theorem conservative_of_spaceTime
    (h : Flow.Conservative (c • transportField T b f) (affineCoord T b x)) :
    Flow.Conservative f x := by
  obtain ⟨V, hV, hmin, hcons⟩ := h
  refine ⟨V ∘ affineCoord T b, hV.comp (T.continuous.add continuous_const),
    fun u hu => hmin _ fun he => hu ?_, fun t₀ t₁ φ hφ t ht => ?_⟩
  · simpa [affineCoord] using he
  · simpa only [Function.comp, mul_div_cancel₀ _ hc.ne'] using
      hcons _ _ _ (isTrajectoryOn_spaceTime hc T b hφ) (t / c) (mem_Icc_div hc ht)

/-- A contraction by `ρ < 1` over the horizon `h ≥ 0` of the space-time field is, after `m`
steps, a contraction by a factor below one of `f` over the horizon `c (m h)`. -/
@[tmio T, powerlib_foundation] private lemma contraction_of_spaceTime {h ρ : ℝ} (hh : 0 ≤ h)
    (hρ : ρ < 1)
    (hcon : ∀ (s₀ : ℝ) (χ : ℝ → State n), IsTrajectoryOn χ (c • transportField T b f) s₀ (s₀ + h) →
      ‖χ (s₀ + h) - affineCoord T b x‖ ≤ ρ * ‖χ s₀ - affineCoord T b x‖) :
    ∃ m : ℕ, 0 < m ∧ ∃ ρ' < 1, ∀ (t₀ : ℝ) (φ : ℝ → State n),
      IsTrajectoryOn φ f t₀ (t₀ + c * (m * h)) →
        ‖φ (t₀ + c * (m * h)) - x‖ ≤ ρ' * ‖φ t₀ - x‖ := by
  set M := max 1 (‖(T : State n →L[ℝ] State n)‖ * ‖(T.symm : State n →L[ℝ] State n)‖)
  have hc0 : 0 ≤ max ρ 0 := le_max_right _ _
  have hlim : Tendsto (fun j : ℕ => M * max ρ 0 ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 (max_lt hρ one_pos)).const_mul M
  obtain ⟨m, hm0, hm⟩ :=
    ((eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds one_pos))).exists
  refine ⟨m, hm0, M * max ρ 0 ^ m, hm, fun t₀ φ hφ => ?_⟩
  have hχ := isTrajectoryOn_spaceTime hc T b hφ
  have e : (t₀ + c * (m * h)) / c = t₀ / c + m * h := by field_simp
  rw [e] at hχ
  have hit := contraction_iterate hh hcon m (t₀ / c) _ hχ
  have e' : c * (t₀ / c + m * h) = t₀ + c * (m * h) := by field_simp
  simp only [e', mul_div_cancel₀ _ hc.ne'] at hit
  exact norm_sub_le_of_affineCoord T b (by positivity) hit

/-- **Sampled contraction under the space-time map.** Sampled contraction of the space-time field
at `T x + b` is contraction of the solutions of `f` about `x` over a horizon `c k`, `k` a positive
integer. -/
@[tmio T, powerlib_foundation] theorem sampledContraction_spaceTime_iff :
    Flow.SampledContraction (c • transportField T b f) (affineCoord T b x) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ ρ < 1, ∀ (t₀ : ℝ) (φ : ℝ → State n),
        IsTrajectoryOn φ f t₀ (t₀ + c * k) → ‖φ (t₀ + c * k) - x‖ ≤ ρ * ‖φ t₀ - x‖ := by
  constructor
  · rintro ⟨k, hk, ρ, hρ, hcon⟩
    obtain ⟨m, hm, ρ', hρ', h'⟩ := contraction_of_spaceTime hc T b (Nat.cast_nonneg k) hρ hcon
    exact ⟨m * k, Nat.mul_pos hm hk, ρ', hρ', by push_cast; exact h'⟩
  · rintro ⟨k, hk, ρ, hρ, hcon⟩
    obtain ⟨m, hm, ρ', hρ', h'⟩ := contraction_of_spaceTime (f := c • transportField T b f)
      (x := affineCoord T b x) (inv_pos.mpr hc) T.symm (-(T.symm b)) (h := c * k) (by positivity)
      hρ (by rwa [smul_transportField_symm hc.ne', affineCoord_symm_affineCoord])
    have e : c⁻¹ * (m * (c * k)) = ((m * k : ℕ) : ℝ) := by push_cast; field_simp
    rw [e] at h'
    exact ⟨m * k, Nat.mul_pos hm hk, ρ', hρ', h'⟩

/-- Each sentence read back from the space-time field. -/
@[tmio T, powerlib_foundation] private theorem holds_of_spaceTime {P : Flow.Property}
    (hP : P ≠ .contractive ∨ c = 1)
    (h : (P.timeScale c).holds (c • transportField T b f) (affineCoord T b x)) : P.holds f x := by
  cases P with
  | lyapunovStable => exact lyapunovStable_of_spaceTime hc T b h
  | locallyAsymptoticallyStable => exact localAsymptoticStable_of_spaceTime hc T b h
  | locallyExponentiallyStable => exact locallyExponentiallyStable_of_spaceTime hc T b h
  | globallyAsymptoticallyStable =>
    exact ⟨(isEquilibrium_spaceTime_iff hc T b).mp h.1, forwardComplete_of_spaceTime hc T b h.2.1,
      globalAsymptoticStable_of_spaceTime hc T b h.2.2⟩
  | globallyExponentiallyStable => exact globallyExponentiallyStable_of_spaceTime hc T b h
  | unstable =>
    exact fun hs => h (lyapunovStable_of_spaceTime (inv_pos.mpr hc) T.symm (-(T.symm b))
      (by rwa [smul_transportField_symm hc.ne', affineCoord_symm_affineCoord]))
  | decay a => exact decay_of_spaceTime hc T b h
  | contractive =>
    obtain rfl : c = 1 := hP.resolve_left fun h => h rfl
    have h' := (sampledContraction_spaceTime_iff hc T b).mp h
    simp only [one_mul] at h'
    exact h'
  | conservative => exact conservative_of_spaceTime hc T b h

/-- **Space-time transport law.** For `c > 0`, `T` invertible and any `b`, a behavioural sentence
`P` holds for `f` at `x` exactly when its time-scaled form `P.timeScale c` holds for the
space-time field `c • transportField T b f` at `T x + b`; for `c ≠ 1` sampled contraction is
excluded (`sampledContraction_spaceTime_iff`). -/
@[tmio T, powerlib_foundation] theorem holds_spaceTime_iff {P : Flow.Property}
    (hP : P ≠ .contractive ∨ c = 1) :
    (P.timeScale c).holds (c • transportField T b f) (affineCoord T b x) ↔ P.holds f x := by
  refine ⟨holds_of_spaceTime hc T b hP, fun h => ?_⟩
  have hP' : P.timeScale c ≠ .contractive ∨ c⁻¹ = 1 := hP.imp
    (fun h' => by cases P <;> first | exact absurd rfl h' | exact h' | simp)
    (fun h' => by simp [h'])
  have h' := holds_of_spaceTime (f := c • transportField T b f) (x := affineCoord T b x)
    (inv_pos.mpr hc) T.symm (-(T.symm b)) hP'
  rw [Flow.Property.timeScale_timeScale, inv_mul_cancel₀ hc.ne', Flow.Property.timeScale_one,
    smul_transportField_symm hc.ne', affineCoord_symm_affineCoord] at h'
  exact h' h

end Sentences

end powerlib.Dynamics
