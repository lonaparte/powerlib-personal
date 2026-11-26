import theorem.Dynamics.HopfCycleLocal
import theorem.Dynamics.HopfCycleBranch

/-! # Every small periodic orbit at a Hopf point has the Hopf amplitude (foundation)

At a Hopf point with `l₁ ≠ 0` and a transversal crossing (the hypotheses of
`Dynamics.HopfCycle.exists_hopfCycle`), every nonconstant periodic orbit of `ẋ = F(x, μ)` near the
point lies on the centre manifold, exists only on the side `μ τ l₁ < 0`, and has critical
amplitude `‖critπ p x(t)‖² = ν (1 + o(1))`, `ν = −μτ/(ω l₁)`, uniformly in time: all small cycles
are asymptotically indistinguishable from the constructed one in amplitude. Uniqueness up to a time
shift and orbital stability are not proved (they need a second-order approximation of the
derivative of the centre manifold and the derivative of the planar return map).

Scope.
* The hypotheses of `theorem/Dynamics/HopfCycle.lean` (`F(0, μ) = 0`, augmented field `C¹`
  globally or only on an open set `U ∋ 0`, analytic at `0`, a critical pair at the frequency
  `ω`, the rest of the spectrum in the open left half plane, `τ ≠ 0`, `l₁ ≠ 0`). Periodic orbits
  are written out in the statements (a curve with `ẋ = F(x, μ)`, a period `T > 0`, not constant)
  and stay in a small ball; nothing is assumed about their period or shape.
* Generic foundation, independent of any model; no model family is defined.

Source: Hassard–Kazarinoff–Wan, *Theory and Applications of Hopf Bifurcation* (1981), Ch. 1
(Theorem: all small periodic solutions near a Hopf point lie on the bifurcating branch, and none
for the other sign of the parameter); Carr, *Applications of Centre Manifold Theory* (1981),
§2.4 (bounded solutions lie on the centre manifold); Kuznetsov, *Elements of Applied Bifurcation
Theory* (3rd ed.), §3.4 (Theorem 3.3); Marsden–McCracken, *The Hopf Bifurcation and Its
Applications* (1976), §3.

Results.
* `HopfCycle.periodic_amplitude`: for every `η > 0` there is `δ > 0` such that, for `|μ| < δ`,
  every nonconstant periodic solution of `F(·, μ)` in the ball of radius `δ` has `μ τ l₁ < 0` and
  `(1 − η) ν ≤ ‖critπ p x(t)‖² ≤ (1 + η) ν` for all `t`. In particular there is no small
  nonconstant periodic orbit for `μ τ l₁ ≥ 0`, nor at `μ = 0`. Proof: the orbit lies on the
  centre manifold (`exists_reducedSlice`, `CenterManifold.exists_centerManifold_bounded`), its
  critical coordinates are a periodic orbit of the reduced slice avoiding `0`
  (`ne_zero_of_periodic`), and the planar law `PlanarHopf.periodic_amplitude` applies with the
  uniform remainder of the slices.
* `HopfCycle.periodic_amplitude_local`: the same for an augmented field `C¹` only on an open set
  `U ∋ 0` (a small cycle of `F` is a cycle of the cut-off family of `exists_hopfCycle_local`).
-/

noncomputable section
namespace powerlib.Dynamics.HopfCycle
open Set Filter Topology Metric Polynomial
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold (critπ critι)

variable {n : ℕ} {F : State n → ℝ → State n} {ω : ℝ} {q p : Fin n → ℂ}

/-- **Every small cycle at a Hopf point has the Hopf amplitude.** With the hypotheses of
`exists_hopfCycle`: for every `η > 0` there is `δ > 0` such that, for `|μ| < δ`, every
nonconstant periodic solution `x` of `ẋ = F(x, μ)` staying in the ball of radius `δ` satisfies
`μ τ l₁ < 0` and `(1 − η) ν ≤ ‖critπ p x(t)‖² ≤ (1 + η) ν` for all `t`, `ν = −μτ/(ω l₁)`: there
is no small cycle for `μ τ l₁ ≥ 0` (in particular at `μ = 0`), and all small cycles have the
amplitude of the bifurcating cycle up to a factor `1 + o(1)`. -/
@[tmio T, powerlib_foundation] theorem periodic_amplitude (hF : ContDiff ℝ 1 (augField F))
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0)
    (hcp : IsCriticalPair (fun x => F x 0) 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    (hτ : PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) ≠ 0)
    (hl : firstLyapunov (fun x => F x 0) 0 ω q p ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ μ, |μ| < δ → ∀ (x : ℝ → State n) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt x (F (x t) μ) t) → (∀ t, x (t + T) = x t) → (∃ t, x t ≠ x 0) →
      (∀ t, ‖x t‖ < δ) →
      μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) *
          firstLyapunov (fun x => F x 0) 0 ω q p < 0 ∧
        ∀ t, (1 - η) * (-(μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q)))) /
            (ω * firstLyapunov (fun x => F x 0) 0 ω q p)) ≤ ‖critπ p (x t)‖ ^ 2 ∧
          ‖critπ p (x t)‖ ^ 2 ≤ (1 + η) * (-(μ * PlanarHopf.paramTrace
            ((critπ p).comp (B.comp (critι q)))) /
              (ω * firstLyapunov (fun x => F x 0) 0 ω q p)) := by
  obtain ⟨G, Λ, Q₂, C₂, -, -, hl1, -, -, -, hfull, hchart, ⟨rb, hrb, hbd⟩, -⟩ :=
    exists_reducedSlice hF ha hF0 hcp hchar hr hB
  have hω := hcp.freq_pos
  obtain ⟨δ₀, hδ₀, hamp⟩ := PlanarHopf.periodic_amplitude hω hfull hτ (hl1 ▸ hl) hη
  rw [hl1] at hamp
  obtain ⟨Kp, hKp⟩ : ∃ K, K = ‖critπ p‖ := ⟨_, rfl⟩
  have hKp0 : 0 ≤ Kp := hKp ▸ norm_nonneg _
  refine ⟨min (δ₀ / (Kp + 1)) (min δ₀ (rb / 2)), lt_min (by positivity)
    (lt_min hδ₀ (by positivity)), fun μ hμ x T hT hx hxT hnc hxδ => ?_⟩
  simp only [lt_min_iff] at hμ
  obtain ⟨-, hμ0, hμr⟩ := hμ
  have hxδ' : ∀ t, ‖x t‖ < δ₀ / (Kp + 1) ∧ ‖x t‖ < rb / 2 := fun t => by
    have := hxδ t
    simp only [lt_min_iff] at this
    exact ⟨this.1, this.2.2⟩
  have hxp : ∀ t, ‖critπ p (x t)‖ < δ₀ := fun t => by
    calc ‖critπ p (x t)‖ ≤ Kp * ‖x t‖ := hKp ▸ (critπ p).le_opNorm _
      _ ≤ (Kp + 1) * ‖x t‖ := by nlinarith [norm_nonneg (x t)]
      _ < (Kp + 1) * (δ₀ / (Kp + 1)) := by
          exact mul_lt_mul_of_pos_left (hxδ' t).1 (by positivity)
      _ = δ₀ := by field_simp
  -- the augmented solution lies on the centre manifold
  have hz : ∀ t, HasDerivAt (fun s => xin (x s) + μ • emu) (augField F (xin (x t) + μ • emu))
      t := fun t => by
    rw [augField_xin_add]
    exact (xin.hasFDerivAt.comp_hasDerivAt t (hx t)).add_const _
  have hzr : ∀ t, ‖xin (x t) + μ • emu‖ < rb := fun t =>
    (norm_xin_add_smul_le _ _).trans_lt (by linarith [(hxδ' t).2])
  have hzΛ : ∀ t, Λ (augπ (critπ p) (xin (x t) + μ • emu)) = xin (x t) + μ • emu :=
    fun t => hbd _ hz hzr t
  have hπz : ∀ t, augπ (critπ p) (xin (x t) + μ • emu) = xin (critπ p (x t)) + μ • emu :=
    fun t => by rw [augπ_apply]; simp
  -- the reduced cycle
  have hγ : ∀ t, HasDerivAt (fun s => critπ p (x s))
      (sliceField G μ (critπ p (x t))) t := by
    intro t
    have h1 := (critπ p).hasFDerivAt.comp_hasDerivAt t (hx t)
    have e : sliceField G μ (critπ p (x t)) = critπ p (F (x t) μ) := by
      show xpart (G (xin (critπ p (x t)) + μ • emu)) = _
      rw [← hπz, hchart, hzΛ, xpart_augπ, augField_xin_add, xpart_xin]
    rw [e]
    exact h1
  have hΦ0 : augField F (μ • emu) = 0 := by
    have := augField_xin_add (F := F) 0 μ
    rwa [map_zero, zero_add, hF0, map_zero] at this
  have hΛ0 : Λ (μ • emu) = μ • emu := by
    have h1 : Λ (augπ (critπ p) (μ • emu)) = μ • emu := hbd (fun _ => μ • emu) (fun s => by
      simpa only [hΦ0] using hasDerivAt_const s (μ • (emu : State (n + 1)))) (fun _ => by
        rw [norm_smul, norm_emu, mul_one, Real.norm_eq_abs]; linarith) 0
    have hπe : augπ (critπ p) (μ • emu) = μ • emu := by rw [augπ_apply]; simp
    rwa [hπe] at h1
  have hg : ContDiff ℝ 1 fun x => F x μ := by
    have h := (xpart (n := n)).contDiff.comp (hF.comp
      ((xin (n := n)).contDiff.add (contDiff_const (c := μ • (emu : State (n + 1))))))
    have e : (fun x => F x μ) = ⇑xpart ∘ augField F ∘ fun x => xin x + μ • emu :=
      funext fun x => by simp [augField_xin_add]
    rw [e]
    exact h
  have hγ0 : ∀ t, critπ p (x t) ≠ 0 := by
    intro t h0
    have h1 := hzΛ t
    rw [hπz, h0, map_zero, zero_add, hΛ0] at h1
    have hxt : x t = 0 := by
      have h2 := congrArg xpart h1
      rw [map_add, xpart_xin, map_smul, xpart_emu, smul_zero, add_zero] at h2
      exact h2.symm
    exact ne_zero_of_periodic hg hT hx hxT hnc t (by rw [hxt, hF0])
  exact hamp μ hμ0 (fun s => critπ p (x s)) T hT hγ (fun t => by simp only [hxT]) hγ0 hxp

/-- On the side `μ τ l₁ < 0` the Hopf amplitude `ν = −μτ/(ω l₁)` is `|τ|/(ω |l₁|) · |μ|`. -/
@[tmio T, powerlib_foundation] theorem hopfAmplitude_eq_abs {μ τ ℓ ω : ℝ} (hω : 0 < ω)
    (h : μ * τ * ℓ < 0) : -(μ * τ) / (ω * ℓ) = |τ| / (ω * |ℓ|) * |μ| := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at h
  have habs : |μ| * |τ| * |ℓ| = -(μ * τ * ℓ) := by
    rw [← abs_mul, ← abs_mul]; exact abs_of_neg h
  have hl2 : ℓ ^ 2 = |ℓ| ^ 2 := (sq_abs ℓ).symm
  have hla : |ℓ| ≠ 0 := abs_ne_zero.mpr hℓ0
  rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hω.ne' hℓ0) (mul_ne_zero hω.ne' hla)]
  apply mul_right_cancel₀ hℓ0
  linear_combination (-(ω * |ℓ|)) * habs - (ω * |μ| * |τ|) * hl2

/-- **Small cycles about a moving equilibrium.** With the hypotheses of
`exists_hopfCycle_of_branch` (a branch `x*(μ)` of equilibria, `C¹` and analytic at `0`): for
every `η > 0` there is `δ > 0` such that, for `|μ| < δ`, every nonconstant periodic solution with
`‖x(t) − x*(μ)‖ < δ` has `μ τ l₁ < 0` and `(1 − η) ν ≤ ‖critπ p (x(t) − x*(μ))‖² ≤ (1 + η) ν`
(`periodic_amplitude` for the re-centred family `F(z + x*(μ), μ)`). -/
@[tmio T, powerlib_foundation] theorem periodic_amplitude_of_branch {xs : ℝ → State n}
    (hF : ContDiff ℝ 1 (augField F)) (ha : AnalyticAt ℝ (augField F) (xin (xs 0)))
    (hxs : ContDiff ℝ 1 xs) (hxa : AnalyticAt ℝ xs 0) (hF0 : ∀ μ, F (xs μ) μ = 0)
    (hcp : IsCriticalPair (fun x => F x 0) (xs 0) ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) (xs 0)).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) (xs μ)) B 0)
    (hτ : PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) ≠ 0)
    (hl : firstLyapunov (fun x => F x 0) (xs 0) ω q p ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ μ, |μ| < δ → ∀ (x : ℝ → State n) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt x (F (x t) μ) t) → (∀ t, x (t + T) = x t) → (∃ t, x t ≠ x 0) →
      (∀ t, ‖x t - xs μ‖ < δ) →
      μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) *
          firstLyapunov (fun x => F x 0) (xs 0) ω q p < 0 ∧
        ∀ t, (1 - η) * (-(μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q)))) /
            (ω * firstLyapunov (fun x => F x 0) (xs 0) ω q p)) ≤ ‖critπ p (x t - xs μ)‖ ^ 2 ∧
          ‖critπ p (x t - xs μ)‖ ^ 2 ≤ (1 + η) * (-(μ * PlanarHopf.paramTrace
            ((critπ p).comp (B.comp (critι q)))) /
              (ω * firstLyapunov (fun x => F x 0) (xs 0) ω q p)) := by
  have hl' : firstLyapunov (fun z => F (z + xs 0) 0) 0 ω q p =
      firstLyapunov (fun x => F x 0) (xs 0) ω q p :=
    firstLyapunov_comp_add (fun x => F x 0) (xs 0) ω q p
  have hB' : HasDerivAt (fun μ => fderiv ℝ (fun z => F (z + xs μ) μ) 0) B 0 := by
    have e : (fun μ => fderiv ℝ (fun z => F (z + xs μ) μ) 0) =
        fun μ => fderiv ℝ (fun x => F x μ) (xs μ) := by
      funext μ
      rw [fderiv_comp_add_right (f := fun x => F x μ), zero_add]
    rw [e]
    exact hB
  have hchar' : (jacobianC (fun z => F (z + xs 0) 0) 0).charpoly =
      (X ^ 2 + C ((ω : ℂ) ^ 2)) * r := by
    rw [jacobianC_comp_add (fun x => F x 0) (xs 0)]
    exact hchar
  obtain ⟨δ, hδ, hamp⟩ := periodic_amplitude (F := fun z μ => F (z + xs μ) μ)
    (contDiff_augField_recentre hF hxs) (analyticAt_augField_recentre ha hxa)
    (fun μ => by simpa using hF0 μ) (isCriticalPair_comp_add.mpr hcp) hchar' hr hB' hτ
    (hl'.symm ▸ hl) hη
  rw [hl'] at hamp
  refine ⟨δ, hδ, fun μ hμ x T hT hx hxT hnc hxδ => ?_⟩
  refine hamp μ hμ (fun t => x t - xs μ) T hT (fun t => ?_) (fun t => by simp only [hxT])
    ?_ hxδ
  · have := (hx t).sub_const (xs μ)
    simpa only [sub_add_cancel] using this
  · obtain ⟨t, ht⟩ := hnc
    exact ⟨t, fun h => ht (sub_left_injective h)⟩

/-- **Small cycles of a family that is `C¹` only near the point.** With the hypotheses of
`exists_hopfCycle_local` (the augmented field `C¹` on an open set `U ∋ 0`, analytic at `0`), the
conclusion of `periodic_amplitude`: no small cycle for `μ τ l₁ ≥ 0`, and the Hopf amplitude
`(1 ± η) ν` otherwise. Proof: in a small ball the family agrees with its cut-off `b · F`, which
satisfies the hypotheses of `periodic_amplitude`. -/
@[tmio T, powerlib_foundation] theorem periodic_amplitude_local {U : Set (State (n + 1))}
    (hU : IsOpen U) (h0 : (0 : State (n + 1)) ∈ U) (hF : ContDiffOn ℝ 1 (augField F) U)
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0)
    (hcp : IsCriticalPair (fun x => F x 0) 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    (hτ : PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) ≠ 0)
    (hl : firstLyapunov (fun x => F x 0) 0 ω q p ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ μ, |μ| < δ → ∀ (x : ℝ → State n) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt x (F (x t) μ) t) → (∀ t, x (t + T) = x t) → (∃ t, x t ≠ x 0) →
      (∀ t, ‖x t‖ < δ) →
      μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) *
          firstLyapunov (fun x => F x 0) 0 ω q p < 0 ∧
        ∀ t, (1 - η) * (-(μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q)))) /
            (ω * firstLyapunov (fun x => F x 0) 0 ω q p)) ≤ ‖critπ p (x t)‖ ^ 2 ∧
          ‖critπ p (x t)‖ ^ 2 ≤ (1 + η) * (-(μ * PlanarHopf.paramTrace
            ((critπ p).comp (B.comp (critι q)))) /
              (ω * firstLyapunov (fun x => F x 0) 0 ω q p)) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 h0
  let b : ContDiffBump (0 : State (n + 1)) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  set G : State n → ℝ → State n := fun x μ => b (xin x + μ • emu) • F x μ with hGdef
  have haug : augField G = fun z => b z • augField F z := funext fun z => by
    simp only [augField, hGdef, xin_add_smul, map_smul]
  have hGc : ContDiff ℝ 1 (augField G) := by
    rw [haug, contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hy))
    · have hnot : y ∉ tsupport b := by
        rw [b.tsupport_eq]
        intro hyb
        apply hy
        apply hεU
        rw [mem_ball]
        exact (mem_closedBall.mp hyb).trans_lt (by simp [b]; linarith)
      have hzero : (fun y => b y • augField F y) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hb1 : ∀ x : State n, ∀ μ : ℝ, ‖x‖ + |μ| < ε / 4 → G x μ = F x μ := fun x μ h => by
    show b (xin x + μ • emu) • F x μ = F x μ
    rw [b.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr
      ((norm_xin_add_smul_le x μ).trans h.le)), one_smul]
  have hGF : augField G =ᶠ[𝓝 0] augField F := by
    filter_upwards [Metric.ball_mem_nhds (0 : State (n + 1)) (show (0 : ℝ) < ε / 4 by positivity)]
      with z hz
    rw [haug]
    show b z • augField F z = augField F z
    rw [b.one_of_mem_closedBall (ball_subset_closedBall hz), one_smul]
  have hG0F : ∀ μ, |μ| < ε / 8 → (fun x => G x μ) =ᶠ[𝓝 0] fun x => F x μ := fun μ hμ => by
    filter_upwards [Metric.ball_mem_nhds (0 : State n) (show (0 : ℝ) < ε / 8 by positivity)]
      with x hx
    exact hb1 x μ (by rw [mem_ball_zero_iff] at hx; linarith)
  have h00 := hG0F 0 (by rw [abs_zero]; positivity)
  have hG0 : ∀ μ, G 0 μ = 0 := fun μ => by simp [hGdef, hF0]
  have hB' : HasDerivAt (fun μ => fderiv ℝ (fun x => G x μ) 0) B 0 := by
    refine hB.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < ε / 8 by positivity)]
      with μ hμ
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at hμ
    exact (hG0F μ hμ).fderiv_eq
  have hl' := firstLyapunov_congr h00 ω q p
  obtain ⟨δ, hδ, hamp⟩ := periodic_amplitude hGc (ha.congr hGF.symm) hG0
    ((isCriticalPair_congr h00).mpr hcp) (by rw [jacobianC_congr h00]; exact hchar) hr hB' hτ
    (by rw [hl']; exact hl) hη
  rw [hl'] at hamp
  refine ⟨min δ (ε / 8), lt_min hδ (by positivity), fun μ hμ x T hT hx hxT hnc hxδ => ?_⟩
  simp only [lt_min_iff] at hμ
  have hxδ' : ∀ t, ‖x t‖ < δ ∧ ‖x t‖ < ε / 8 := fun t => lt_min_iff.mp (hxδ t)
  refine hamp μ hμ.1 x T hT (fun t => ?_) hxT hnc fun t => (hxδ' t).1
  rw [hb1 (x t) μ (by linarith [(hxδ' t).2, hμ.2])]
  exact hx t

end powerlib.Dynamics.HopfCycle
