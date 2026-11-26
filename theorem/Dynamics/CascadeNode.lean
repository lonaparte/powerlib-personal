import theorem.Dynamics.Degenerate.RelaxedExtension
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.CenterReduction

/-! # A drive and a contracting node: stability of cascades

A field `f` on `ℝⁿ` whose components along a subspace, read by a linear map `π : ℝⁿ → ℝᵐ` with a
right inverse isometry `ι`, are a field `h` of their own (`π (f y) = h (π y)`: the drive does not
read the complement), and whose complement `Q y = y − ι π y` (the node) is contracted near a point
`x` up to a term linear in the drive's distance:
`⟪Q(y − x), Q f(y)⟫ ≤ −c ‖Q(y − x)‖² + L ‖Q(y − x)‖ ‖π y − π x‖` (`c > 0`), e.g. a scalar node
`ż = a(y) z + g(y)` with `a < 0` and `g` Lipschitz near the drive's equilibrium.

Scope.
* Generic foundation, independent of any model: it imports no engineering module and defines no
  family. Autonomous fields `h : ℝᵐ → ℝᵐ`, `f : ℝⁿ → ℝⁿ`, continuous linear maps `ι`, `π` with
  `π ∘ ι = id`, `‖ι u‖ = ‖u‖`, `‖π y‖ ≤ ‖y‖`, `‖y − ι π y‖ ≤ ‖y‖` (an orthogonal splitting of
  coordinates, as in `theorem/Dynamics/Degenerate/RelaxedExtension.lean`), read through
  LeanForControl's notions (solution segments for Lyapunov stability, forward-complete solutions
  for attraction). The node estimate is only required on a ball around `x`; the cascade laws
  need no regularity (the first-integral law a differentiable integral), the converse laws need
  `f` to be `C¹` near `x` and `h` to be `C¹` near `π x` (uniqueness of the drive's solutions).
* The splitting of `ℝ⁵` into its first four coordinates and the fifth (`incl45`, `proj54`), and
  the inclusion of `ℝ³` as the first three coordinates of `ℝ⁴` (`incl34`).

Source: the cascade (drive–node) argument for asymptotic stability, Khalil, *Nonlinear Systems*
(3rd ed.), §4.9 (Lemma 4.7 and the local input-to-state stability of an exponentially stable
node); Definitions 4.1 and 4.5; the comparison principle for scalar differential inequalities
(Mathlib's `image_le_of_deriv_right_lt_deriv_boundary'`) and the norm bound by a derivative
bound (Mathlib's `image_norm_le_of_norm_deriv_right_le_deriv_boundary`).

Results.
* Scalar comparison: `le_max_of_hasDerivWithinAt_le` (`w' ≤ −a w + b` keeps `w` below
  `max (w t₀) (b/a)`), `tendsto_zero_of_hasDerivWithinAt_le` (`w' ≤ −a w + β(t)`, `β → 0`,
  `w ≥ 0` gives `w → 0`).
* **Cascade laws.** `lyapunovStable_cascade`: a Lyapunov stable drive at `π x` with a contracting
  node makes `x` Lyapunov stable for `f`; `localAsymptoticStable_cascade`: a locally
  asymptotically stable drive makes `x` locally asymptotically stable (the node's square obeys
  `w' ≤ −c w + (L²/c) ‖π φ − π x‖²`). `lyapunovStable_cascade_of_exponential`: a locally
  exponentially stable drive with a node that need not contract but whose rate is bounded by the
  drive's distance, `‖Q f(y)‖ ≤ L ‖π y − π x‖` (it vanishes at the drive's equilibrium), makes `x`
  Lyapunov stable (the node moves by at most `(L C/a) ‖π φ(t₀) − π x‖`).
  `lyapunovStable_cascade_of_firstIntegral`: a Lyapunov stable drive with a node pinned near `x`
  by a differentiable first integral `I` of `f`, `‖Q(y − x)‖ ≤ K (|I(y) − I(x)| + ‖π y − π x‖)`,
  makes `x` Lyapunov stable (neither contraction of the node nor a decay rate of the drive; the
  bootstrap `Dynamics.forall_norm_sub_lt_of_bootstrap` and `Dynamics.eq_of_lie_eq_zero_along`).
* **Converse laws.** `lyapunovStable_drive_of_cascade`, `localAsymptoticStable_drive_of_cascade`:
  if `f` is `C¹` near `x`, `h` is `C¹` near `π x`, and `x` is Lyapunov stable (locally
  asymptotically stable) for `f`, so is `π x` for `h`: a solution of the drive is the projection
  of the solution of `f` started at its lift (forward solutions exist near a Lyapunov stable
  point, `Dynamics.exists_forward_of_lyapunovStable`; the drive's solutions are unique where `h`
  is Lipschitz, `Dynamics.CenterManifold.eqOn_of_lipschitzOnWith`). No node estimate is needed.
* **Invariant slice.** `lyapunovStable_of_invariantSlice`: if `g (ι u + c) = ι (h u)` (`ι` an
  isometry), Lyapunov stability of `ι u₀ + c` for `g` passes to `u₀` for `h` (solutions of `h`
  carried into the slice solve `g`).
* `incl34` (`incl34_apply`, `norm_incl34`); `incl45`, `proj54` with `proj54_incl45`,
  `norm_incl45`, `norm_proj54_le`, `norm_sub_incl45_proj54_le`, and the node of `ℝ⁵` read as its
  fifth coordinate: `sub_incl45_proj54`, `norm_sub_incl45_proj54`, `inner_sub_incl45_proj54`.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology Metric
open scoped Pointwise

/-! ## Scalar comparison -/

/-- **Comparison.** A function with right derivatives `w' ≤ −a w + b` on `[t₀, t₁]` (`a > 0`)
stays below `max (w t₀) (b/a)`. -/
@[tmio T, powerlib_foundation] theorem le_max_of_hasDerivWithinAt_le {w w' : ℝ → ℝ}
    {a b t₀ t₁ : ℝ} (ha : 0 < a) (hw : ContinuousOn w (Icc t₀ t₁))
    (hd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt w (w' t) (Ici t) t)
    (hle : ∀ t ∈ Ico t₀ t₁, w' t ≤ -a * w t + b) :
    ∀ t ∈ Icc t₀ t₁, w t ≤ max (w t₀) (b / a) := by
  intro t ht
  refine le_of_forall_pos_le_add fun η hη => ?_
  refine image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => max (w t₀) (b / a) + η)
    (B' := fun _ => 0) hw hd (by linarith [le_max_left (w t₀) (b / a)]) continuousOn_const
    (fun _ _ => hasDerivWithinAt_const _ _ _) (fun s hs hws => ?_) ht
  have h1 := hle s hs
  have h2 : b / a < max (w t₀) (b / a) + η := by linarith [le_max_right (w t₀) (b / a)]
  rw [div_lt_iff₀ ha] at h2
  have hws' : w s = max (w t₀) (b / a) + η := hws
  rw [hws'] at h1
  nlinarith

/-- **Decay.** A nonnegative function on `[t₀, ∞)` with right derivatives `w' ≤ −a w + β(t)`
(`a > 0`) and `β(t) → 0` tends to `0`: past the time where `β ≤ a η/2` it stays below
`w(T) e^{−a(t − T)} + η`. -/
@[tmio T, powerlib_foundation] theorem tendsto_zero_of_hasDerivWithinAt_le {w w' β : ℝ → ℝ}
    {a t₀ : ℝ} (ha : 0 < a) (hw0 : ∀ t, t₀ ≤ t → 0 ≤ w t) (hw : ContinuousOn w (Ici t₀))
    (hd : ∀ t, t₀ ≤ t → HasDerivWithinAt w (w' t) (Ici t) t)
    (hle : ∀ t, t₀ ≤ t → w' t ≤ -a * w t + β t) (hβ : Tendsto β atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / 3 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp hβ (a * η / 2) (by positivity)
  set T := max t₀ T₁ with hT
  have hbound : ∀ t, T ≤ t → w t ≤ w T * Real.exp (-a * (t - T)) + η := by
    intro t ht
    have hB : ∀ s, HasDerivAt (fun s => w T * Real.exp (-a * (s - T)) + η)
        (w T * (Real.exp (-a * (s - T)) * (-a))) s := fun s => by
      have h := ((((hasDerivAt_id s).sub_const T).const_mul (-a)).exp).const_mul (w T)
      simpa using h.add_const η
    refine image_le_of_deriv_right_lt_deriv_boundary' (a := T) (b := t)
      (hw.mono fun s hs => (le_max_left t₀ T₁).trans hs.1)
      (fun s hs => hd s ((le_max_left _ _).trans hs.1)) (by simp [hη0.le])
      (fun s _ => (hB s).continuousAt.continuousWithinAt)
      (fun s _ => (hB s).hasDerivWithinAt) (fun s hs hws => ?_) ⟨ht, le_rfl⟩
    have hsT : T ≤ s := hs.1
    have h1 := hle s ((le_max_left _ _).trans hsT)
    have h2 : |β s - 0| < a * η / 2 := by
      have := hT₁ s ((le_max_right _ _).trans hsT)
      rwa [Real.dist_eq] at this
    rw [sub_zero] at h2
    have h3 := (abs_lt.mp h2).2
    have hws' : w s = w T * Real.exp (-a * (s - T)) + η := hws
    rw [hws'] at h1
    nlinarith
  have hlin : Tendsto (fun t : ℝ => t - T) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-T) tendsto_id).congr fun t => by simp [sub_eq_add_neg]
  have hexp := (Real.tendsto_exp_atBot.comp (hlin.const_mul_atTop_of_neg
    (neg_neg_of_pos ha))).const_mul (w T)
  rw [mul_zero] at hexp
  obtain ⟨T₂, hT₂⟩ := Metric.tendsto_atTop.mp hexp η hη0
  refine ⟨max T T₂, fun t ht => ?_⟩
  have hb := hbound t ((le_max_left _ _).trans ht)
  have he := hT₂ t ((le_max_right _ _).trans ht)
  rw [Real.dist_eq, sub_zero, Function.comp_apply] at he
  have hwt := hw0 t ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hwt]
  have : w T * Real.exp (-a * (t - T)) < η := by
    have := (abs_lt.mp he).2
    linarith
  linarith

/-! ## Cascades -/

section Cascade

variable {m n : ℕ} {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m}
  {h : State m → State m} {f : State n → State n} {x : State n}

/-- The projection of a solution of the cascade is a solution of the drive. -/
@[tmio T, powerlib_foundation] private theorem isIntegralCurveOn_proj_cascade
    (hf : ∀ y, π (f y) = h (π y)) {s : Set ℝ} {φ : ℝ → State n}
    (hφ : IsIntegralCurveOn φ (fun _ y => f y) s) :
    IsIntegralCurveOn (fun t => π (φ t)) (fun _ u => h u) s := fun t ht => by
  have hd := π.hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)
  show HasDerivWithinAt (fun t => π (φ t)) (h (π (φ t))) s t
  rw [← hf]
  exact hd

/-- The distance to `x` is within the drive's distance plus the node's. -/
@[tmio T, powerlib_foundation] private theorem norm_sub_le_cascade (hι : ∀ u, ‖ι u‖ = ‖u‖)
    (y : State n) :
    ‖y - x‖ ≤ ‖π y - π x‖ + ‖(y - x) - ι (π (y - x))‖ := by
  calc ‖y - x‖ = ‖ι (π (y - x)) + ((y - x) - ι (π (y - x)))‖ := by rw [add_sub_cancel]
    _ ≤ ‖ι (π (y - x))‖ + ‖(y - x) - ι (π (y - x))‖ := norm_add_le _ _
    _ = ‖π y - π x‖ + ‖(y - x) - ι (π (y - x))‖ := by rw [hι, map_sub]

/-- Along a solution of the cascade the node's square `w = ‖Q(φ − x)‖²` has the derivative
`2 ⟪Q(φ − x), Q f(φ)⟫`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivWithinAt_node (π' : State n →L[ℝ] State n)
    {s : Set ℝ} {φ : ℝ → State n} (hφ : IsIntegralCurveOn φ (fun _ y => f y) s) {t : ℝ}
    (ht : t ∈ s) :
    HasDerivWithinAt (fun t => ‖(φ t - x) - π' (φ t - x)‖ ^ 2)
      (2 * inner ℝ ((φ t - x) - π' (φ t - x)) (f (φ t) - π' (f (φ t)))) s t := by
  set P : State n →L[ℝ] State n := ContinuousLinearMap.id ℝ (State n) - π' with hP
  have hd := P.hasFDerivAt.comp_hasDerivWithinAt t ((hφ t ht).sub_const x)
  have e : ∀ v, P v = v - π' v := fun v => by simp [hP]
  simp only [Function.comp_def, e] at hd
  exact hd.norm_sq

/-- The node estimate in the linear form used by the comparison: with `q = ‖Q(y − x)‖` and the
drive's distance `d`, `2 (−c q² + L q d) ≤ −c q² + (L²/c) d²`. -/
@[tmio T, powerlib_foundation] private theorem node_ineq {c L q d : ℝ} (hc : 0 < c) :
    2 * (-c * q ^ 2 + L * q * d) ≤ -c * q ^ 2 + L ^ 2 / c * d ^ 2 := by
  have h : 0 ≤ (c * q - L * d) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  have e : (c * q - L * d) ^ 2 / c = c * q ^ 2 - 2 * L * q * d + L ^ 2 / c * d ^ 2 := by
    field_simp
    ring
  linarith

/-- The node bound on a segment: while a solution of the cascade stays within `ρ` of `x` and its
drive within `ε₁` of `π x`, the node stays below `max ‖Q(φ(t₀) − x)‖ (L ε₁ / c)`. -/
@[tmio T, powerlib_foundation] private theorem node_le_of_segment {c L ρ ε₁ : ℝ} (hc : 0 < c)
    (hL : 0 ≤ L) (hε₁ : 0 ≤ ε₁)
    (hnode : ∀ y, ‖y - x‖ < ρ → inner ℝ ((y - x) - ι (π (y - x))) (f y - ι (π (f y))) ≤
      -c * ‖(y - x) - ι (π (y - x))‖ ^ 2 + L * ‖(y - x) - ι (π (y - x))‖ * ‖π y - π x‖)
    {φ : ℝ → State n} {t₀ s : ℝ} (hts : t₀ ≤ s) (hφ : IsTrajectoryOn φ f t₀ s)
    (hin : ∀ t ∈ Icc t₀ s, ‖φ t - x‖ < ρ) (hdr : ∀ t ∈ Icc t₀ s, ‖π (φ t) - π x‖ < ε₁) :
    ‖(φ s - x) - ι (π (φ s - x))‖ ≤
      max ‖(φ t₀ - x) - ι (π (φ t₀ - x))‖ (L * ε₁ / c) := by
  have hw := le_max_of_hasDerivWithinAt_le (a := c) (b := L ^ 2 / c * ε₁ ^ 2)
    (w := fun t => ‖(φ t - x) - ι.comp π (φ t - x)‖ ^ 2) hc
    (fun t ht => (hasDerivWithinAt_node (ι.comp π) hφ ht).continuousWithinAt)
    (fun t ht => (hasDerivWithinAt_node (ι.comp π) hφ
      (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => ?_) s ⟨hts, le_rfl⟩
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hw
    set a := ‖(φ t₀ - x) - ι (π (φ t₀ - x))‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ L * ε₁ / c := by positivity
    have hmax : max (a ^ 2) (L ^ 2 / c * ε₁ ^ 2 / c) = (max a (L * ε₁ / c)) ^ 2 := by
      rw [show L ^ 2 / c * ε₁ ^ 2 / c = (L * ε₁ / c) ^ 2 by field_simp]
      rcases le_total a (L * ε₁ / c) with hab | hab
      · rw [max_eq_right hab, max_eq_right (pow_le_pow_left₀ ha hab 2)]
      · rw [max_eq_left hab, max_eq_left (pow_le_pow_left₀ hb hab 2)]
    rw [hmax] at hw
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (ha.trans (le_max_left _ _)) two_ne_zero).mp hw
  · have ht' := Ico_subset_Icc_self ht
    have hn := hnode (φ t) (hin t ht')
    have hd := hdr t ht'
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hn ⊢
    have hq := node_ineq (L := L) (q := ‖(φ t - x) - ι (π (φ t - x))‖)
      (d := ‖π (φ t) - π x‖) hc
    have hd2 : ‖π (φ t) - π x‖ ^ 2 ≤ ε₁ ^ 2 := by
      have := norm_nonneg (π (φ t) - π x)
      nlinarith
    have hLc : 0 ≤ L ^ 2 / c := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hd2 hLc]

/-- **Cascade, Lyapunov stability.** If the drive `h` is Lyapunov stable at `π x` and the node is
contracted near `x` (`⟪Q(y − x), Q f(y)⟫ ≤ −c ‖Q(y − x)‖² + L ‖Q(y − x)‖ ‖π y − π x‖` on a ball,
`c > 0`, `Q y = y − ι π y`), then `x` is Lyapunov stable for `f`: the drive stays within `ε₁`,
and while the solution stays in the ball the node stays below `max ‖Q(φ(t₀) − x)‖ (L ε₁/c)`. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_cascade (hι : ∀ u, ‖ι u‖ = ‖u‖)
    (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hQ : ∀ y, ‖y - ι (π y)‖ ≤ ‖y‖) (hf : ∀ y, π (f y) = h (π y))
    {ρ c L : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hL : 0 ≤ L)
    (hnode : ∀ y, ‖y - x‖ < ρ → inner ℝ ((y - x) - ι (π (y - x))) (f y - ι (π (f y))) ≤
      -c * ‖(y - x) - ι (π (y - x))‖ ^ 2 + L * ‖(y - x) - ι (π (y - x))‖ * ‖π y - π x‖)
    (hh : LyapunovStable h (π x)) : LyapunovStable f x := by
  intro ε hε
  set R := min ε ρ with hR
  have hR0 : 0 < R := lt_min hε hρ
  have hLc : 0 ≤ L / c := div_nonneg hL hc.le
  set ε₁ := R / (4 * (1 + L / c)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁R : ε₁ * (2 + L / c) ≤ R / 2 := by
    rw [hε₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨δ₁, hδ₁, hb⟩ := hh ε₁ hε₁0
  refine ⟨min δ₁ ε₁, lt_min hδ₁ hε₁0, fun t₀ t₁ φ hφ h0 => ?_⟩
  have h0δ : ‖φ t₀ - x‖ < δ₁ := h0.trans_le (min_le_left _ _)
  have h0ε : ‖φ t₀ - x‖ < ε₁ := h0.trans_le (min_le_right _ _)
  have hdrive : ∀ t ∈ Icc t₀ t₁, ‖π (φ t) - π x‖ < ε₁ := by
    refine hb t₀ t₁ _ (isIntegralCurveOn_proj_cascade hf hφ) ?_
    rw [← map_sub]
    exact (hπ _).trans_lt h0δ
  have key : ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ < R := by
    refine forall_norm_sub_lt_of_bootstrap hφ.continuousOn (h0ε.trans (by nlinarith))
      fun s hs hin => ?_
    have hnodeS := node_le_of_segment (ε₁ := ε₁) hc hL hε₁0.le hnode hs.1
      (hφ.mono (Icc_subset_Icc le_rfl hs.2))
      (fun t ht => (hin t ht).trans_le (min_le_right _ _))
      (fun t ht => hdrive t ⟨ht.1, ht.2.trans hs.2⟩)
    have hq0 : ‖(φ t₀ - x) - ι (π (φ t₀ - x))‖ < ε₁ := (hQ _).trans_lt h0ε
    have hsplit := norm_sub_le_cascade (x := x) (π := π) hι (φ s)
    have hd := hdrive s hs
    have hmax : max ‖(φ t₀ - x) - ι (π (φ t₀ - x))‖ (L * ε₁ / c) ≤ ε₁ + L / c * ε₁ :=
      max_le (by nlinarith) (by rw [mul_div_right_comm, mul_comm]; nlinarith)
    nlinarith
  exact fun t ht => (key t ht).trans_le (min_le_left _ _)

/-- **Cascade, local asymptotic stability.** If the drive `h` is locally asymptotically stable at
`π x` and the node is contracted near `x` (as in `lyapunovStable_cascade`), then `x` is locally
asymptotically stable for `f`: along a forward solution that stays in the ball the drive
converges, and the node's square obeys `w' ≤ −c w + (L²/c) ‖π φ − π x‖²`
(`tendsto_zero_of_hasDerivWithinAt_le`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_cascade (hι : ∀ u, ‖ι u‖ = ‖u‖)
    (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hQ : ∀ y, ‖y - ι (π y)‖ ≤ ‖y‖) (hf : ∀ y, π (f y) = h (π y))
    {ρ c L : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hL : 0 ≤ L)
    (hnode : ∀ y, ‖y - x‖ < ρ → inner ℝ ((y - x) - ι (π (y - x))) (f y - ι (π (f y))) ≤
      -c * ‖(y - x) - ι (π (y - x))‖ ^ 2 + L * ‖(y - x) - ι (π (y - x))‖ * ‖π y - π x‖)
    (hh : LocalAsymptoticStable h (π x)) : LocalAsymptoticStable f x := by
  have hls := lyapunovStable_cascade hι hπ hQ hf hρ hc hL hnode hh.1
  obtain ⟨ch, hch, hconv⟩ := hh.2
  obtain ⟨δ, hδ, hb⟩ := hls ρ hρ
  refine ⟨hls, min δ ch, lt_min hδ hch, fun t₀ φ hφ h0 => ?_⟩
  have hin : ∀ t, t₀ ≤ t → ‖φ t - x‖ < ρ := fun t ht =>
    hb t₀ t φ (hφ.mono Icc_subset_Ici_self) (h0.trans_le (min_le_left _ _)) t ⟨ht, le_rfl⟩
  have hd : Tendsto (fun t => π (φ t)) atTop (𝓝 (π x)) := by
    refine hconv t₀ _ (isIntegralCurveOn_proj_cascade hf hφ) ?_
    rw [← map_sub]
    exact (hπ _).trans_lt (h0.trans_le (min_le_right _ _))
  have hdn : Tendsto (fun t => ‖π (φ t) - π x‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hd
  have hβ : Tendsto (fun t => L ^ 2 / c * ‖π (φ t) - π x‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hdn.pow 2).const_mul (L ^ 2 / c)
  have hw := tendsto_zero_of_hasDerivWithinAt_le (a := c) (t₀ := t₀)
    (w := fun t => ‖(φ t - x) - ι.comp π (φ t - x)‖ ^ 2) hc (fun t _ => by positivity)
    (fun t ht => (hasDerivWithinAt_node (ι.comp π) hφ ht).continuousWithinAt)
    (fun t ht => (hasDerivWithinAt_node (ι.comp π) hφ (mem_Ici.mpr ht)).mono
      (Ici_subset_Ici.mpr ht)) (fun t ht => ?_) hβ
  · have hq : Tendsto (fun t => ‖(φ t - x) - ι (π (φ t - x))‖) atTop (𝓝 0) := by
      have h1 := (Real.continuous_sqrt.tendsto 0).comp hw
      simp only [Real.sqrt_zero, ContinuousLinearMap.coe_comp, Function.comp_apply] at h1
      refine h1.congr fun t => ?_
      simp only [Function.comp_apply]
      rw [Real.sqrt_sq (norm_nonneg _)]
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun t => norm_nonneg _)
      (fun t => norm_sub_le_cascade (π := π) hι (φ t)) ?_)
    simpa using hdn.add hq
  · have hn := hnode (φ t) (hin t ht)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    have hq := node_ineq (L := L) (q := ‖(φ t - x) - ι (π (φ t - x))‖)
      (d := ‖π (φ t) - π x‖) hc
    nlinarith

/-- **Cascade with an exponentially stable drive and a slaved node.** If the drive `h` is locally
exponentially stable at `π x` and, near `x`, the node rate is bounded by the drive's distance,
`‖Q f(y)‖ ≤ L ‖π y − π x‖` (`Q y = y − ι π y`: the node moves only while the drive is off its
equilibrium, e.g. a voltage integrating a power mismatch), then `x` is Lyapunov stable for `f`:
the node moves by at most `(L C/a) ‖π φ(t₀) − π x‖`, `C e^{−a t}` the drive's decay. The node
need not contract. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_cascade_of_exponential (hι : ∀ u, ‖ι u‖ = ‖u‖)
    (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hQ : ∀ y, ‖y - ι (π y)‖ ≤ ‖y‖) (hf : ∀ y, π (f y) = h (π y))
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hnode : ∀ y, ‖y - x‖ < ρ → ‖f y - ι (π (f y))‖ ≤ L * ‖π y - π x‖)
    (hh : LocallyExponentiallyStable h (π x)) : LyapunovStable f x := by
  obtain ⟨r, C, a, hr, hC, ha, hexp⟩ := hh
  intro ε hε
  set R := min ε ρ with hR
  have hR0 : 0 < R := lt_min hε hρ
  set K := 1 + C + L * C / a with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min r (R / (2 * K)), by positivity, fun t₀ t₁ φ hφ h0 => ?_⟩
  set e₀ := ‖φ t₀ - x‖ with he₀
  set d₀ := ‖π (φ t₀) - π x‖ with hd₀
  have hd₀e : d₀ ≤ e₀ := by rw [hd₀, ← map_sub]; exact hπ _
  have hdr : d₀ < r := hd₀e.trans_lt (h0.trans_le (min_le_left _ _))
  have hdrive : ∀ t ∈ Icc t₀ t₁, ‖π (φ t) - π x‖ ≤ C * Real.exp (-a * (t - t₀)) * d₀ :=
    hexp t₀ t₁ _ (isIntegralCurveOn_proj_cascade hf hφ) hdr
  set P : State n →L[ℝ] State n := ContinuousLinearMap.id ℝ (State n) - ι.comp π with hP
  have hPe : ∀ v, P v = v - ι (π v) := fun v => by simp [hP]
  have hgd : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (fun t => (φ t - x) - ι (π (φ t - x)))
      (f (φ t) - ι (π (f (φ t)))) (Icc t₀ t₁) t := fun t ht => by
    have hd := P.hasFDerivAt.comp_hasDerivWithinAt t ((hφ t ht).sub_const x)
    simp only [Function.comp_def, hPe] at hd
    exact hd
  have key : ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ < R := by
    have hK1 : 1 ≤ 2 * K := by
      have : 0 ≤ L * C / a := by positivity
      linarith
    refine forall_norm_sub_lt_of_bootstrap hφ.continuousOn
      (h0.trans_le ((min_le_right _ _).trans (div_le_self hR0.le hK1))) fun s hs hin => ?_
    have hg := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := t₀) (b := s)
      (f := fun t => (φ t - x) - ι (π (φ t - x))) (f' := fun t => f (φ t) - ι (π (f (φ t))))
      (B := fun t => ‖(φ t₀ - x) - ι (π (φ t₀ - x))‖ +
        L * C * d₀ / a * (1 - Real.exp (-a * (t - t₀))))
      (B' := fun t => L * C * d₀ * Real.exp (-a * (t - t₀)))
      (fun t ht => (hgd t ⟨ht.1, ht.2.trans hs.2⟩).continuousWithinAt.mono
        (Icc_subset_Icc le_rfl hs.2))
      (fun t ht => (hgd t ⟨ht.1, ht.2.le.trans hs.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le hs.2⟩))
      (by simp) (fun t => by
        have he := (((hasDerivAt_id t).sub_const t₀).const_mul (-a)).exp
        simp only [id_eq, mul_one] at he
        have h2 := ((he.const_sub 1).const_mul (L * C * d₀ / a)).const_add
          ‖(φ t₀ - x) - ι (π (φ t₀ - x))‖
        refine h2.congr_deriv ?_
        calc L * C * d₀ / a * -(Real.exp (-a * (t - t₀)) * -a)
            = L * C * d₀ * Real.exp (-a * (t - t₀)) * (a / a) := by ring
          _ = L * C * d₀ * Real.exp (-a * (t - t₀)) := by rw [div_self ha.ne', mul_one])
      (fun t ht => by
        have ht' : t ∈ Icc t₀ s := Ico_subset_Icc_self ht
        have hn := hnode (φ t) ((hin t ht').trans_le (min_le_right _ _))
        have hd := hdrive t ⟨ht'.1, ht'.2.trans hs.2⟩
        calc ‖f (φ t) - ι (π (f (φ t)))‖ ≤ L * ‖π (φ t) - π x‖ := hn
          _ ≤ L * (C * Real.exp (-a * (t - t₀)) * d₀) := mul_le_mul_of_nonneg_left hd hL
          _ = L * C * d₀ * Real.exp (-a * (t - t₀)) := by ring) ⟨hs.1, le_rfl⟩
    have hq0 : ‖(φ t₀ - x) - ι (π (φ t₀ - x))‖ ≤ e₀ := hQ _
    have hex : 0 < Real.exp (-a * (s - t₀)) := Real.exp_pos _
    have hLCd : 0 ≤ L * C * d₀ / a := by positivity
    have hgs : ‖(φ s - x) - ι (π (φ s - x))‖ ≤ e₀ + L * C * d₀ / a := by
      have : L * C * d₀ / a * (1 - Real.exp (-a * (s - t₀))) ≤ L * C * d₀ / a := by
        nlinarith
      linarith [hg]
    have hds := hdrive s hs
    have hex1 : Real.exp (-a * (s - t₀)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hs.1])
    have hCd : C * Real.exp (-a * (s - t₀)) * d₀ ≤ C * e₀ := by
      have := norm_nonneg (π (φ t₀) - π x)
      have hC0 : 0 ≤ C := by linarith
      calc C * Real.exp (-a * (s - t₀)) * d₀ ≤ C * 1 * d₀ := by gcongr
        _ ≤ C * e₀ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hd₀e hC0
    have hsplit : ‖φ s - x‖ ≤ ‖π (φ s) - π x‖ + ‖(φ s - x) - ι (π (φ s - x))‖ := by
      calc ‖φ s - x‖ = ‖ι (π (φ s - x)) + ((φ s - x) - ι (π (φ s - x)))‖ := by
            rw [add_sub_cancel]
        _ ≤ ‖ι (π (φ s - x))‖ + ‖(φ s - x) - ι (π (φ s - x))‖ := norm_add_le _ _
        _ = ‖π (φ s) - π x‖ + ‖(φ s - x) - ι (π (φ s - x))‖ := by rw [hι, map_sub]
    have hLd : L * C * d₀ / a ≤ L * C / a * e₀ := by
      rw [mul_div_right_comm, mul_comm (L * C / a)]
      exact mul_le_mul_of_nonneg_left hd₀e (by positivity) |>.trans_eq' (by ring)
    have he : e₀ < R / (2 * K) := h0.trans_le (min_le_right _ _)
    have hKe : K * e₀ ≤ R / 2 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp he
      nlinarith
    nlinarith
  exact fun t ht => (key t ht).trans_le (min_le_left _ _)

/-- **A drive and a node tied by a first integral.** If the drive `h` is Lyapunov stable at
`π x` and, near `x`, a differentiable `I` is conserved by `f` (`DI(y) f(y) = 0`) and pins the node
up to the drive's distance, `‖Q(y − x)‖ ≤ K (|I(y) − I(x)| + ‖π y − π x‖)` (`Q y = y − ι π y`),
then `x` is Lyapunov stable for `f`: along a solution `I` keeps its initial value, close to
`I(x)`, and the drive stays close to `π x`. The node need not contract and the drive need not be
exponentially, nor asymptotically, stable (e.g. a voltage whose square integrates a power
mismatch that is itself the time derivative of a function of the drive). -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_cascade_of_firstIntegral
    (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hf : ∀ y, π (f y) = h (π y))
    {I : State n → ℝ} (hI : Differentiable ℝ I) {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hlie : ∀ y, ‖y - x‖ < ρ → fderiv ℝ I y (f y) = 0)
    (hnode : ∀ y, ‖y - x‖ < ρ →
      ‖(y - x) - ι (π (y - x))‖ ≤ K * (|I y - I x| + ‖π y - π x‖))
    (hh : LyapunovStable h (π x)) : LyapunovStable f x := by
  intro ε hε
  set R := min ε ρ with hR
  have hR0 : 0 < R := lt_min hε hρ
  have hK1 : 0 < 1 + 2 * K := by linarith
  set η := R / (2 * (1 + 2 * K)) with hη
  have hη0 : 0 < η := div_pos hR0 (by linarith)
  obtain ⟨δ₁, hδ₁, hdrive⟩ := hh η hη0
  obtain ⟨δ₂, hδ₂, hIc⟩ := Metric.continuous_iff.mp hI.continuous x η hη0
  refine ⟨min (min δ₁ δ₂) (R / 2), lt_min (lt_min hδ₁ hδ₂) (half_pos hR0),
    fun t₀ t₁ φ hφ h0 => ?_⟩
  have h0₁ : ‖φ t₀ - x‖ < δ₁ := h0.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h0₂ : ‖φ t₀ - x‖ < δ₂ := h0.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hd : ∀ t ∈ Icc t₀ t₁, ‖π (φ t) - π x‖ < η :=
    hdrive t₀ t₁ _ (isIntegralCurveOn_proj_cascade hf hφ)
      (by rw [← map_sub]; exact (hπ _).trans_lt h0₁)
  have hI0 : |I (φ t₀) - I x| < η := by
    have := hIc (φ t₀) (by rw [dist_eq_norm]; exact h0₂)
    rwa [Real.dist_eq] at this
  have key : ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ < R := by
    refine forall_norm_sub_lt_of_bootstrap hφ.continuousOn
      (h0.trans_le ((min_le_right _ _).trans (half_le_self hR0.le))) fun s hs hin => ?_
    have hcons : I (φ s) = I (φ t₀) :=
      eq_of_lie_eq_zero_along hI (convex_Icc t₀ s) (hφ.mono (Icc_subset_Icc le_rfl hs.2))
        (fun u hu => hlie _ ((hin u hu).trans_le (min_le_right _ _))) ⟨le_rfl, hs.1⟩
        ⟨hs.1, le_rfl⟩ hs.1
    have hn := hnode (φ s) ((hin s ⟨hs.1, le_rfl⟩).trans_le (min_le_right _ _))
    rw [hcons] at hn
    have hds := hd s hs
    have hsplit := norm_sub_le_cascade (π := π) (x := x) hι (φ s)
    have hKb : K * (|I (φ t₀) - I x| + ‖π (φ s) - π x‖) ≤ K * (2 * η) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    have hRη : (1 + 2 * K) * η = R / 2 := by
      rw [hη]; field_simp
    nlinarith
  exact fun t ht => (key t ht).trans_le (min_le_left _ _)

/-- A solution of a field `C¹` near a Lyapunov stable point, started near it, that is extended
for all forward time and stays where the field is the cascade field. -/
@[tmio T, powerlib_foundation] private theorem isIntegralCurveOn_shift_zero {g : State n → State n}
    {φ : ℝ → State n} (hφ : IsIntegralCurveOn φ (fun _ y => g y) (Ici 0)) (t₀ : ℝ) :
    IsIntegralCurveOn (fun t => φ (t - t₀)) (fun _ y => g y) (Ici t₀) := by
  have h := hφ.comp_add_autonomous (-t₀)
  have hset : -(-t₀) +ᵥ Ici (0 : ℝ) = Ici t₀ := by
    ext s
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, mem_Ici]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  simpa [sub_eq_add_neg] using h

/-- **Lifting the drive.** With `f` `C¹` near a Lyapunov stable point `x`, `h` `C¹` near `π x` and
`π f = h π`: for every radius `R₁ > 0` there is `δ > 0` such that a state `y₀` of the drive within
`δ` of `π x` has a forward solution of `f` from `x + ι (y₀ − π x)` that stays within `R₁` of `x`,
and every solution segment of the drive from `y₀` is its projection. -/
@[tmio T, powerlib_foundation] private theorem exists_lift (hπι : ∀ u, π (ι u) = u)
    (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hf : ∀ y, π (f y) = h (π y))
    {U : Set (State n)} (hU : IsOpen U) (hxU : x ∈ U) (hfU : ContDiffOn ℝ 1 f U)
    (hh : ContDiffAt ℝ 1 h (π x)) (hs : LyapunovStable f x) {R₁ : ℝ} (hR₁ : 0 < R₁) :
    ∃ δ > 0, ∀ (t₀ : ℝ) (y₀ : State m), ‖y₀ - π x‖ < δ → ∃ φ : ℝ → State n,
      IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀) ∧ φ t₀ = x + ι (y₀ - π x) ∧
      (∀ t, t₀ ≤ t → ‖φ t - x‖ < R₁) ∧
      ∀ (t₁ : ℝ) (ψ : ℝ → State m), IsTrajectoryOn ψ h t₀ t₁ → ψ t₀ = y₀ →
        ∀ t ∈ Icc t₀ t₁, ψ t = π (φ t) := by
  obtain ⟨g, hg, hgf, σ, hσ, hball⟩ := exists_contDiff_ball hU hxU hfU
  have hsg : LyapunovStable g x := lyapunovStable_congr_nhds hgf hs
  obtain ⟨K, V, hV, hK⟩ := hh.exists_lipschitzOnWith
  obtain ⟨R₀, hR₀, hRV₀⟩ := Metric.mem_nhds_iff.mp hV
  set R := R₀ / 2 with hR
  have hR : 0 < R := by positivity
  have hRV : closedBall (π x) R ⊆ V := (closedBall_subset_ball (by linarith)).trans hRV₀
  obtain ⟨δf, hδf, hfwd⟩ := exists_forward_of_lyapunovStable hg hsg
  set r := min (min R₁ R) σ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrR₁ : r < R₁ := by
    have := min_le_left (min R₁ R) σ
    have := min_le_left R₁ R
    linarith
  have hrR : r < R := by
    have := min_le_left (min R₁ R) σ
    have := min_le_right R₁ R
    linarith
  have hrσ : r < σ := by
    have := min_le_right (min R₁ R) σ
    linarith
  obtain ⟨δg, hδg, hbg⟩ := hsg r hr0
  refine ⟨min (min δg δf) r, by positivity, fun t₀ y₀ hy₀ => ?_⟩
  set z₀ := x + ι (y₀ - π x) with hz₀
  have hz₀x : ‖z₀ - x‖ = ‖y₀ - π x‖ := by rw [hz₀, add_sub_cancel_left, hι]
  obtain ⟨φ, hφ0, hφ, -⟩ := hfwd z₀ (by
    rw [hz₀x]; exact hy₀.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hφs := isIntegralCurveOn_shift_zero hφ t₀
  have hstay : ∀ t, t₀ ≤ t → ‖φ (t - t₀) - x‖ < r := fun t ht =>
    hbg t₀ t _ (hφs.mono Icc_subset_Ici_self) (by
      rw [sub_self, hφ0, hz₀x]
      exact hy₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))) t ⟨ht, le_rfl⟩
  have hgf' : ∀ t, t₀ ≤ t → g (φ (t - t₀)) = f (φ (t - t₀)) := fun t ht =>
    (hball _ ((hstay t ht).trans hrσ)).1
  have hφf : IsIntegralCurveOn (fun t => φ (t - t₀)) (fun _ y => f y) (Ici t₀) := fun t ht => by
    have := hφs t ht
    simp only at this ⊢
    rwa [← hgf' t ht]
  refine ⟨fun t => φ (t - t₀), hφf, by simp [hφ0, hz₀], fun t ht => (hstay t ht).trans hrR₁,
    fun t₁ ψ hψ hψ0 => ?_⟩
  have hχ : IsTrajectoryOn (fun t => π (φ (t - t₀))) h t₀ t₁ :=
    (isIntegralCurveOn_proj_cascade hf hφf).mono Icc_subset_Ici_self
  have hχ0 : π (φ (t₀ - t₀)) = y₀ := by
    rw [sub_self, hφ0, hz₀, map_add, hπι, add_sub_cancel]
  have hχin : ∀ t, t₀ ≤ t → ‖π (φ (t - t₀)) - π x‖ < r := fun t ht => by
    rw [← map_sub]
    exact (hπ _).trans_lt (hstay t ht)
  have hR2 : r ≤ R / 2 := by
    have := min_le_left (min R₁ R) σ
    have := min_le_right R₁ R
    linarith
  have hboot := forall_norm_sub_lt_of_bootstrap (φ := ψ) (x := π x) (R := R) hψ.continuousOn
    (by rw [hψ0]; exact hy₀.trans_le ((min_le_right _ _).trans hrR.le)) fun s hs hin => by
      have heq := CenterManifold.eqOn_of_lipschitzOnWith (S := closedBall (π x) R) (hK.mono hRV)
        (hψ.mono (Icc_subset_Icc le_rfl hs.2)) (hχ.mono (Icc_subset_Icc le_rfl hs.2))
        (fun t ht => by
          rw [mem_closedBall, dist_eq_norm]; exact (hin t ht).le)
        (fun t ht => by
          rw [mem_closedBall, dist_eq_norm]; exact (hχin t ht.1).le.trans hrR.le)
        (by rw [hψ0, hχ0]) ⟨hs.1, le_rfl⟩
      rw [heq]
      exact (hχin s hs.1).le.trans hR2
  intro t ht
  have heq := CenterManifold.eqOn_of_lipschitzOnWith (S := closedBall (π x) R) (hK.mono hRV) hψ
    hχ (fun t ht => by rw [mem_closedBall, dist_eq_norm]; exact (hboot t ht).le)
    (fun t ht => by
      rw [mem_closedBall, dist_eq_norm]; exact (hχin t ht.1).le.trans hrR.le)
    (by rw [hψ0, hχ0]) ht
  exact heq

/-- **The drive of a Lyapunov stable cascade is Lyapunov stable.** With `f` `C¹` near `x`, `h`
`C¹` near `π x` and `π f = h π`, Lyapunov stability of `x` for `f` gives that of `π x` for `h`:
a drive segment is the projection of the solution of `f` from its lift (`exists_lift`). -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_drive_of_cascade (hπι : ∀ u, π (ι u) = u)
    (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖) (hf : ∀ y, π (f y) = h (π y))
    {U : Set (State n)} (hU : IsOpen U) (hxU : x ∈ U) (hfU : ContDiffOn ℝ 1 f U)
    (hh : ContDiffAt ℝ 1 h (π x)) (hs : LyapunovStable f x) : LyapunovStable h (π x) := by
  intro ε hε
  obtain ⟨δ, hδ, hlift⟩ := exists_lift hπι hι hπ hf hU hxU hfU hh hs hε
  refine ⟨δ, hδ, fun t₀ t₁ ψ hψ h0 t ht => ?_⟩
  obtain ⟨φ, -, -, hstay, hproj⟩ := hlift t₀ (ψ t₀) h0
  rw [hproj t₁ ψ hψ rfl t ht, ← map_sub]
  exact (hπ _).trans_lt (hstay t ht.1)

/-- **The drive of a locally asymptotically stable cascade is locally asymptotically stable**
(with the hypotheses of `lyapunovStable_drive_of_cascade`): a forward solution of the drive from
near `π x` is the projection of the solution of `f` from its lift, which converges. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_drive_of_cascade
    (hπι : ∀ u, π (ι u) = u) (hι : ∀ u, ‖ι u‖ = ‖u‖) (hπ : ∀ y, ‖π y‖ ≤ ‖y‖)
    (hf : ∀ y, π (f y) = h (π y)) {U : Set (State n)} (hU : IsOpen U) (hxU : x ∈ U)
    (hfU : ContDiffOn ℝ 1 f U) (hh : ContDiffAt ℝ 1 h (π x)) (hs : LocalAsymptoticStable f x) :
    LocalAsymptoticStable h (π x) := by
  refine ⟨lyapunovStable_drive_of_cascade hπι hι hπ hf hU hxU hfU hh hs.1, ?_⟩
  obtain ⟨cf, hcf, hconv⟩ := hs.2
  obtain ⟨δ, hδ, hlift⟩ := exists_lift hπι hι hπ hf hU hxU hfU hh hs.1 one_pos
  refine ⟨min δ cf, lt_min hδ hcf, fun t₀ ψ hψ h0 => ?_⟩
  obtain ⟨φ, hφ, hφ0, -, hproj⟩ := hlift t₀ (ψ t₀) (h0.trans_le (min_le_left _ _))
  have hlim := hconv t₀ φ hφ (by
    rw [hφ0, add_sub_cancel_left, hι]; exact h0.trans_le (min_le_right _ _))
  have h1 := (π.continuous.tendsto x).comp hlim
  refine h1.congr' (eventually_atTop.mpr ⟨t₀, fun t ht => ?_⟩)
  exact (hproj t ψ (hψ.mono Icc_subset_Ici_self) rfl t ⟨ht, le_rfl⟩).symm

end Cascade

/-! ## Restriction to an invariant slice -/

/-- **Restriction to an invariant affine slice.** If a field `g` on `ℝⁿ` is tangent to the slice
`ι(ℝᵐ) + c` (`ι` a linear isometry) and reads there as the field `h`, `g (ι u + c) = ι (h u)`,
the solutions of `h` carried into the slice are solutions of `g`: Lyapunov stability of
`ι u₀ + c` for `g` passes to `u₀` for `h`. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_invariantSlice {m n : ℕ}
    {g : State n → State n} {h : State m → State m} (ι : State m →L[ℝ] State n)
    (hι : ∀ u, ‖ι u‖ = ‖u‖) (c : State n) (hgh : ∀ u, g (ι u + c) = ι (h u)) {u₀ : State m}
    (hs : LyapunovStable g (ι u₀ + c)) : LyapunovStable h u₀ := by
  have hn : ∀ u, ι u + c - (ι u₀ + c) = ι (u - u₀) := fun u => by rw [map_sub]; abel
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hs ε hε
  refine ⟨δ, hδ, fun t₀ t₁ ψ hψ h0 t ht => ?_⟩
  have hφ : IsTrajectoryOn (fun s => ι (ψ s) + c) g t₀ t₁ := fun s hs => by
    have hd := (ι.hasFDerivAt.comp_hasDerivWithinAt s (hψ s hs)).add_const c
    show HasDerivWithinAt _ (g (ι (ψ s) + c)) _ s
    rw [hgh]
    exact hd
  have h1 := hb t₀ t₁ _ hφ (by rw [hn, hι]; exact h0) t ht
  rwa [hn, hι] at h1

/-! ## The first three coordinates of `ℝ⁴` -/

/-- The inclusion `(a, b, c) ↦ (a, b, c, 0)`. -/
def incl34 : State 3 →L[ℝ] State 4 :=
  (coord 0).smulRight (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) +
    (coord 1).smulRight (EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) +
    (coord 2).smulRight (EuclideanSpace.single (2 : Fin 4) (1 : ℝ))

@[tmio T, simp, powerlib_foundation] theorem incl34_apply (u : State 3) (i : Fin 4) :
    incl34 u i = if h : i.val < 3 then u ⟨i.val, h⟩ else 0 := by
  fin_cases i <;> simp [incl34]

@[tmio T, powerlib_foundation] theorem norm_incl34 (u : State 3) : ‖incl34 u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_four, Fin.sum_univ_three]
  simp

/-! ## The first four coordinates of `ℝ⁵` -/

/-- The inclusion `(a, b, c, d) ↦ (a, b, c, d, 0)`. -/
def incl45 : State 4 →L[ℝ] State 5 :=
  (coord 0).smulRight (EuclideanSpace.single (0 : Fin 5) (1 : ℝ)) +
    (coord 1).smulRight (EuclideanSpace.single (1 : Fin 5) (1 : ℝ)) +
    (coord 2).smulRight (EuclideanSpace.single (2 : Fin 5) (1 : ℝ)) +
    (coord 3).smulRight (EuclideanSpace.single (3 : Fin 5) (1 : ℝ))

/-- The projection `(a, b, c, d, e) ↦ (a, b, c, d)`. -/
def proj54 : State 5 →L[ℝ] State 4 :=
  (coord 0).smulRight (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) +
    (coord 1).smulRight (EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) +
    (coord 2).smulRight (EuclideanSpace.single (2 : Fin 4) (1 : ℝ)) +
    (coord 3).smulRight (EuclideanSpace.single (3 : Fin 4) (1 : ℝ))

@[tmio T, simp, powerlib_foundation] theorem incl45_apply (u : State 4) (i : Fin 5) :
    incl45 u i = if h : i.val < 4 then u ⟨i.val, h⟩ else 0 := by
  fin_cases i <;> simp [incl45]

@[tmio T, simp, powerlib_foundation] theorem proj54_apply (y : State 5) (i : Fin 4) :
    proj54 y i = y (Fin.castSucc i) := by
  fin_cases i <;> simp [proj54]

@[tmio T, powerlib_foundation] theorem proj54_incl45 (u : State 4) : proj54 (incl45 u) = u := by
  ext i
  fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem norm_incl45 (u : State 4) : ‖incl45 u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_five, Fin.sum_univ_four]
  simp

@[tmio T, powerlib_foundation] theorem norm_proj54_le (y : State 5) : ‖proj54 y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_five, Fin.sum_univ_four]
  apply Real.sqrt_le_sqrt
  simp only [show proj54 y 0 = y 0 by simp [proj54], show proj54 y 1 = y 1 by simp [proj54],
    show proj54 y 2 = y 2 by simp [proj54], show proj54 y 3 = y 3 by simp [proj54]]
  nlinarith [sq_nonneg ‖y 4‖]

/-- The complement of the first four coordinates is the fifth axis. -/
@[tmio T, powerlib_foundation] theorem sub_incl45_proj54 (y : State 5) :
    y - incl45 (proj54 y) = y 4 • EuclideanSpace.single (4 : Fin 5) (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem norm_sub_incl45_proj54 (y : State 5) :
    ‖y - incl45 (proj54 y)‖ = |y 4| := by
  rw [sub_incl45_proj54, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

@[tmio T, powerlib_foundation] theorem inner_sub_incl45_proj54 (y z : State 5) :
    inner ℝ (y - incl45 (proj54 y)) (z - incl45 (proj54 z)) = y 4 * z 4 := by
  rw [sub_incl45_proj54, sub_incl45_proj54, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left]
  simp

@[tmio T, powerlib_foundation] theorem norm_sub_incl45_proj54_le (y : State 5) :
    ‖y - incl45 (proj54 y)‖ ≤ ‖y‖ := by
  rw [norm_sub_incl45_proj54]
  exact abs_apply_le_norm y 4

end powerlib.Dynamics
