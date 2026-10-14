import theorem.Dynamics.LaSalle.Basin

/-! # Passivity and detectability: asymptotic stability by LaSalle (foundation)

Model boundary: an arbitrary continuous-time input-affine or general system `ẋ = F(x, u)`,
`y = H(x)` on `EuclideanSpace ℝ (Fin n)` with `m` ports, no delay, switching or time variation;
passivity is the static dissipation inequality `V̇(x, u) = DV(x)·F(x, u) ≤ ⟪u, y⟫` for a `C¹`
storage `V` that is positive definite (`V(0) = 0`, `V > 0` elsewhere); `F(0, 0) = 0`; zero-state
detectability: every unforced forward solution (`u ≡ 0`) with `y ≡ 0` converges to `0`. The loop
is closed by an output feedback `u = −ψ(y)` with `ψ(0) = 0` and `⟪ψ(y), y⟫ > 0` for `y ≠ 0`
(damping injection `ψ(y) = k y`, `k > 0`), and the closed-loop field is assumed `C¹`.

* `tendsto_zero_of_lasalle_detectable`: LaSalle's principle (via
  `lasalle_invariance_principle_of_contDiff`) with detectability on `{V̇ = 0}` — every forward
  solution from a compact positively invariant set converges to `0` (a positively invariant subset
  of `{V̇ = 0}` carries a forward solution along which `V` is constant and which converges to `0`,
  so `V = 0` on it).
* `output_eq_zero_of_passive` (`H(0) = 0`), `lieDeriv_feedback_le` (`V̇ ≤ −⟪ψ(y), y⟫ ≤ 0`, and
  `V̇ = 0` only on `{y = 0}`, where the closed loop is the unforced system).
* `globallyAsymptoticallyStable_of_passive_detectable`: with `V` radially unbounded, `0` is a
  globally asymptotically stable equilibrium of the closed loop (Flow semantics: equilibrium,
  forward completeness, LeanForControl's `GlobalAsymptoticStable`).
* `localAsymptoticStable_of_passive_detectable`: with one compact sublevel set `{V ≤ c₀}`,
  `c₀ > 0`, local asymptotic stability.
* `detectable_of_observable`, `globallyAsymptoticallyStable_of_passive_observable`: the
  zero-state-observable special case.

These are generic implications about arbitrary fields, hence foundation results (no model
family). The linear port-Hamiltonian counterexample (passive and observable but not asymptotically
stable without output feedback) and the spectral proof for linear pH plants are in
`theorem/PH/Observability.lean`.

Source: Khalil, *Nonlinear Systems*, 3rd ed., Lemma 6.7 with zero-state detectability; work-sync
`theory/T-ph.md` Part 2, "Passivity 不等于稳定".
-/

noncomputable section
namespace powerlib.Dynamics.LaSalle
open Set Filter Topology
open scoped Pointwise

variable {n m : ℕ}

/-- **LaSalle with detectability.** `f` C¹, `V` C¹ positive definite with `V̇ ≤ 0` everywhere,
and every forward solution of `f` along which `V̇` vanishes identically converges to `0`. Then
every forward solution starting in a compact positively invariant set converges to `0`. -/
@[powerlib_foundation] theorem tendsto_zero_of_lasalle_detectable
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0)
    (hdet : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), fderiv ℝ V (φ t) (f (φ t)) = 0) → Tendsto φ atTop (𝓝 0))
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩc : IsCompact Ω) (hΩi : IsPositivelyInvariant Ω f)
    {φ : ℝ → EuclideanSpace ℝ (Fin n)} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0))
    (hφ0 : φ 0 ∈ Ω) : Tendsto φ atTop (𝓝 0) := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hM : ∀ N ⊆ Dynamics.LaSalle.LieDerivZeroSet f V Ω, IsPositivelyInvariant N f →
      N ⊆ ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
    intro N hN hNinv p hp
    obtain ⟨g, -, ⟨K, hglip⟩, -, -, -, -, hgf⟩ := Dynamics.LaSalle.exists_globalization hf hΩc hΩi
    obtain ⟨χ, hχ0, hχ⟩ := Flow.forwardComplete_of_lipschitzWith hglip 0 p
    have hχf : IsIntegralCurveOn χ (fun _ x => f x) (Ici 0) :=
      hgf hχ (hχ0 ▸ (hN hp).1)
    have hstay : ∀ t ∈ Ici (0 : ℝ), χ t ∈ N := fun t ht =>
      hNinv 0 t χ (hχf.mono Icc_subset_Ici_self) (hχ0 ▸ hp) t ⟨ht, le_rfl⟩
    have hzero : ∀ t ∈ Ici (0 : ℝ), fderiv ℝ V (χ t) (f (χ t)) = 0 := fun t ht =>
      (hN (hstay t ht)).2
    have hlim := hdet χ hχf hzero
    -- `V ∘ χ` is constant on `[0, ∞)`
    have hanti : AntitoneOn (V ∘ χ) (Ici 0) :=
      antitoneOn_V_comp_traj hVd hVd.continuous (convex_Ici 0) hχf
        (fun t ht => (hzero t (interior_subset ht)).le)
    have hmono : AntitoneOn ((fun x => -V x) ∘ χ) (Ici 0) := by
      refine antitoneOn_V_comp_traj hVd.neg hVd.continuous.neg (convex_Ici 0) hχf
        (fun t ht => ?_)
      rw [fderiv_neg]
      simp [hzero t (interior_subset ht)]
    have hconst : ∀ t ∈ Ici (0 : ℝ), V (χ t) = V p := by
      intro t ht
      have h1 := hanti (mem_Ici.mpr le_rfl) ht ht
      have h2 := hmono (mem_Ici.mpr le_rfl) ht ht
      simp only [Function.comp_apply, hχ0] at h1 h2
      linarith
    have hVlim : Tendsto (fun t => V (χ t)) atTop (𝓝 (V 0)) :=
      (hVd.continuous.tendsto 0).comp hlim
    have hVlim' : Tendsto (fun t => V (χ t)) atTop (𝓝 (V p)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 0] with t ht
        exact (hconst t ht).symm)
    have hVp : V p = 0 := by rw [← hV0]; exact tendsto_nhds_unique hVlim' hVlim
    by_contra hne
    exact (hVpos p hne).ne' hVp
  have h := Dynamics.LaSalle.lasalle_invariance_principle_of_contDiff hΩc hΩi hf hV
    (fun x _ => hdec x) hφ hφ0 hM
  rwa [nhdsSet_singleton] at h

/-- Passivity with a storage minimized at `0` forces the output to vanish at `0`. -/
@[powerlib_foundation] theorem output_eq_zero_of_passive
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x)) : H 0 = 0 := by
  have hmin : IsLocalMin V 0 := Filter.Eventually.of_forall fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · exact le_rfl
    · rw [hV0]; exact (hVpos x hx).le
  have hd : fderiv ℝ V 0 = 0 := hmin.fderiv_eq_zero
  have h := hpass 0 (-H 0)
  rw [hd, inner_neg_left, real_inner_self_eq_norm_sq] at h
  rw [_root_.zero_apply] at h
  have : ‖H 0‖ ^ 2 ≤ 0 := by linarith
  exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (le_antisymm this (sq_nonneg _)))

/-- Output feedback `u = −ψ(y)` with `⟪ψ(y), y⟫ > 0` (`y ≠ 0`), `ψ(0) = 0` on a passive system:
`V̇ ≤ −⟪ψ(y), y⟫ ≤ 0`, and `V̇ = 0` only where `y = 0`. -/
@[powerlib_foundation] theorem lieDeriv_feedback_le
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ V x (F x (-ψ (H x))) ≤ 0 ∧
      (fderiv ℝ V x (F x (-ψ (H x))) = 0 → H x = 0) := by
  have h := hpass x (-ψ (H x))
  rw [inner_neg_left] at h
  constructor
  · rcases eq_or_ne (H x) 0 with h0 | h0
    · simp only [h0, hψ0, inner_zero_left, neg_zero] at h ⊢; exact h
    · linarith [hψ (H x) h0]
  · intro hz
    by_contra h0
    linarith [hψ (H x) h0]

/-- Zero-state detectability transported to the closed loop: a closed-loop solution along which
`V̇` vanishes stays in `{y = 0}`, where the closed loop is the unforced system. -/
private theorem closedLoop_detectable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y)
    (hzsd : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0)) :
    ∀ φ : ℝ → EuclideanSpace ℝ (Fin n),
      IsIntegralCurveOn φ (fun _ x => F x (-ψ (H x))) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), fderiv ℝ V (φ t) (F (φ t) (-ψ (H (φ t)))) = 0) →
        Tendsto φ atTop (𝓝 0) := by
  intro φ hφ hz
  have hH : ∀ t ∈ Ici (0 : ℝ), H (φ t) = 0 := fun t ht =>
    (lieDeriv_feedback_le hpass hψ0 hψ (φ t)).2 (hz t ht)
  refine hzsd φ (Dynamics.isIntegralCurveOn_of_eq_on_curve hφ fun t ht => ?_) hH
  rw [hH t ht, hψ0, neg_zero]

/-- **Passivity + zero-state detectability ⇒ global asymptotic stability** (Khalil, *Nonlinear
Systems*, Lemma 6.7, global part, with detectability in place of observability). For
`ẋ = F(x, u)`, `y = H(x)` passive with a `C¹` storage `V` that is positive definite and radially
unbounded (`V̇ ≤ ⟪u, y⟫`), with `F(0, 0) = 0`, and zero-state detectable (every unforced forward
solution with `y ≡ 0` converges to `0`), the output feedback `u = −ψ(y)` with `ψ(0) = 0`,
`⟪ψ(y), y⟫ > 0` (`y ≠ 0`; e.g. `ψ(y) = k y`, `k > 0`) makes `0` globally asymptotically stable,
provided the closed-loop field is `C¹`. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_of_passive_detectable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hn : 0 < n)
    (hf : ContDiff ℝ 1 fun x => F x (-ψ (H x)))
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hradial : Tendsto V (comap norm atTop) atTop)
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y) (hF0 : F 0 0 = 0)
    (hzsd : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0)) :
    Flow.GloballyAsymptoticallyStable (fun x => F x (-ψ (H x))) 0 := by
  set f := fun x => F x (-ψ (H x)) with hfdef
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hH0 := output_eq_zero_of_passive hV0 hVpos hpass
  have hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0 := fun x => (lieDeriv_feedback_le hpass hψ0 hψ x).1
  have hdet := closedLoop_detectable hpass hψ0 hψ hzsd
  have hsub : ∀ c : ℝ, IsCompact {x : EuclideanSpace ℝ (Fin n) | V x ≤ c} :=
    isCompact_sublevel_set V hV.continuous hradial
  refine ⟨?_, Flow.forwardComplete_of_compact_sublevel hf hVd hdec hsub, ?_, ?_⟩
  · show F 0 (-ψ (H 0)) = 0
    rw [hH0, hψ0, neg_zero, hF0]
  · exact lyapunov_stable hn ⟨isOpen_univ, mem_univ _, hVd.continuous, hVd, hV0,
      fun x _ hx => hVpos x hx, fun x _ => hdec x⟩
  · intro t₀ φ hφ
    have hψs : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Ici 0) := by
      have hset : -t₀ +ᵥ Ici t₀ = Ici (0 : ℝ) := by
        ext x
        simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, mem_Ici]
        constructor <;> intro h <;> linarith
      have h' := _root_.IsIntegralCurveOn.comp_add_autonomous hφ t₀
      rwa [hset] at h'
    have hinv : IsPositivelyInvariant {x | V x ≤ V (φ t₀)} f := by
      have h := Dynamics.LaSalle.isPositivelyInvariant_sublevel_of_isOpen (f := f) (c := V (φ t₀))
        isOpen_univ hVd (fun x _ => hdec x) (by
          simpa using (isClosed_le hVd.continuous continuous_const))
      simpa using h
    have hconv := tendsto_zero_of_lasalle_detectable hf hV hV0 hVpos hdec hdet (hsub _) hinv hψs
      (by simp)
    exact Tendsto.congr (fun x => by simp)
      (hconv.comp (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id))

/-- **Passivity + zero-state detectability ⇒ local asymptotic stability** (Khalil, Lemma 6.7,
local part). As `globallyAsymptoticallyStable_of_passive_detectable`, with radial unboundedness
replaced by one compact sublevel set `{V ≤ c₀}`, `c₀ > 0`. -/
@[powerlib_foundation] theorem localAsymptoticStable_of_passive_detectable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hn : 0 < n)
    (hf : ContDiff ℝ 1 fun x => F x (-ψ (H x)))
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hcompact : ∃ c > 0, IsCompact {x : EuclideanSpace ℝ (Fin n) | V x ≤ c})
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y)
    (hzsd : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0)) :
    LocalAsymptoticStable (fun x => F x (-ψ (H x))) 0 := by
  set f := fun x => F x (-ψ (H x)) with hfdef
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0 := fun x => (lieDeriv_feedback_le hpass hψ0 hψ x).1
  have hdet := closedLoop_detectable hpass hψ0 hψ hzsd
  obtain ⟨c₀, hc₀, hK⟩ := hcompact
  refine ⟨lyapunov_stable hn ⟨isOpen_univ, mem_univ _, hVd.continuous, hVd, hV0,
      fun x _ hx => hVpos x hx, fun x _ => hdec x⟩, ?_⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuousAt_iff.mp (hVd.continuous.continuousAt (x := 0)) c₀ hc₀
  refine ⟨δ, hδ, fun t₀ φ hφ hφ0 => ?_⟩
  have hlt : V (φ t₀) < c₀ := by
    have h := hδV (x := φ t₀) (by rwa [dist_eq_norm])
    rw [Real.dist_eq, hV0, sub_zero] at h
    exact (abs_lt.mp h).2
  have hψs : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Ici 0) := by
    have hset : -t₀ +ᵥ Ici t₀ = Ici (0 : ℝ) := by
      ext x
      simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, mem_Ici]
      constructor <;> intro h <;> linarith
    have h' := _root_.IsIntegralCurveOn.comp_add_autonomous hφ t₀
    rwa [hset] at h'
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin n) | V x ≤ V (φ t₀)} :=
    isClosed_le hVd.continuous continuous_const
  have hinv : IsPositivelyInvariant {x | V x ≤ V (φ t₀)} f := by
    have h := Dynamics.LaSalle.isPositivelyInvariant_sublevel_of_isOpen (f := f) (c := V (φ t₀))
      isOpen_univ hVd (fun x _ => hdec x) (by simpa using hclosed)
    simpa using h
  have hΩ : IsCompact {x : EuclideanSpace ℝ (Fin n) | V x ≤ V (φ t₀)} :=
    hK.of_isClosed_subset hclosed fun x (hx : V x ≤ V (φ t₀)) => show V x ≤ c₀ by linarith
  have hconv := tendsto_zero_of_lasalle_detectable hf hV hV0 hVpos hdec hdet hΩ hinv hψs
    (by simp)
  exact Tendsto.congr (fun x => by simp)
    (hconv.comp (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id))

/-- Zero-state observability (the only unforced forward solution with `y ≡ 0` is `x ≡ 0`)
implies zero-state detectability. -/
@[powerlib_foundation] theorem detectable_of_observable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hzso : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → ∀ t ∈ Ici (0 : ℝ), φ t = 0) :
    ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0) := by
  intro φ hφ hH
  exact tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hzso φ hφ hH t ht).symm)

/-- **Passivity + zero-state observability ⇒ global asymptotic stability under output feedback**
(Khalil, Lemma 6.7): the zero-state-observable special case of
`globallyAsymptoticallyStable_of_passive_detectable`. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_of_passive_observable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hn : 0 < n)
    (hf : ContDiff ℝ 1 fun x => F x (-ψ (H x)))
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hradial : Tendsto V (comap norm atTop) atTop)
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y) (hF0 : F 0 0 = 0)
    (hzso : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → ∀ t ∈ Ici (0 : ℝ), φ t = 0) :
    Flow.GloballyAsymptoticallyStable (fun x => F x (-ψ (H x))) 0 :=
  globallyAsymptoticallyStable_of_passive_detectable hn hf hV hV0 hVpos hradial hpass hψ0 hψ hF0
    (detectable_of_observable hzso)

end powerlib.Dynamics.LaSalle
