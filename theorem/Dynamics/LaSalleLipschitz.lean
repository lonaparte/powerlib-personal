import theorem.Dynamics.LaSalle.Passivity

/-! # LaSalle's invariance principle for globally Lipschitz fields

LaSalle's principle and the global asymptotic stability theorem it gives, for a globally Lipschitz
field that need not be differentiable (piecewise-affine closed loops, saturations).

Scope.
* An arbitrary autonomous continuous-time ODE `ẋ = f x` on `Dynamics.State n =
  EuclideanSpace ℝ (Fin n)` with a globally Lipschitz field `f` (no differentiability); no input,
  delay, switching or time variation. Solutions are `IsIntegralCurveOn` curves on `[0, ∞)`;
  `V̇ x = fderiv ℝ V x (f x)` for a `C¹` function `V`.
* The upstream principle (`_root_.lasalle_invariance_principle`, LeanForControl) and the
  library's `lasalle_invariance_principle_of_contDiff` assume a `C¹` field, used only for a
  solution through each point of the ω-limit set; a globally Lipschitz field has one
  (`Flow.forwardComplete_of_lipschitzWith`), which is all the proof here uses.
* Every theorem is a generic implication about arbitrary fields and functions (foundation, no
  model family). The orbit-wise form (one bounded orbit, no invariant set, no derivative of `V`)
  is `Dynamics.tendsto_nhdsSet_of_antitone` in `theorem/Dynamics/OrbitLaSalle.lean`; this module
  keeps the set-wise form of the upstream principle, with the Lie derivative `V̇`.

Source: Khalil, *Nonlinear Systems*, 3rd ed., Lemma 4.1, Theorem 4.4 and Corollary 4.2 (LaSalle,
Barbashin–Krasovskii); LeanForControl `Stability/LaSalle.lean` (the ω-limit set
`omegaLimitTraj` and its positive invariance `isPositivelyInvariant_omegaLimitTraj` for Lipschitz
fields); work-sync `theory/T-lyapunov-function-method.md` §1.4.

Results.
* `lieDeriv_eq_zero_of_isPositivelyInvariant`: on a positively invariant set of a Lipschitz field
  where a `C¹` function `h` vanishes, its derivative along the field vanishes too (the step that
  discharges a LaSalle condition one function at a time).
* `lieDeriv_eq_zero_on_omegaLimitTraj_of_lipschitz`: `V̇ = 0` on the ω-limit set of a forward
  solution starting in a compact positively invariant set where `V̇ ≤ 0`.
* `lasalle_invariance_principle_of_lipschitz`: LaSalle's principle for a Lipschitz field.
* `globallyAsymptoticallyStable_of_lasalle_lipschitz`: a positive definite radially unbounded
  `C¹` function with `V̇ ≤ 0` whose set `{V̇ = 0}` has no positively invariant subset other than
  the equilibrium (or the empty set) makes the equilibrium of a Lipschitz field globally
  asymptotically stable (`Flow.GloballyAsymptoticallyStable`).
-/

noncomputable section
namespace powerlib.Dynamics.LaSalle
open Set Filter Topology
variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- **Derivative along an invariant zero set.** On a positively invariant set `N` of a globally
Lipschitz field where a `C¹` function `h` vanishes, the derivative of `h` along the field vanishes
(the forward solution through a point of `N` stays in `N`, where `h ∘ φ ≡ 0`). -/
@[tmio T, powerlib_foundation] theorem lieDeriv_eq_zero_of_isPositivelyInvariant
    {f : ℝⁿ → ℝⁿ} {K : NNReal} (hf : LipschitzWith K f) {N : Set ℝⁿ}
    (hN : IsPositivelyInvariant N f) {h : ℝⁿ → ℝ} (hh : Differentiable ℝ h)
    (hzero : ∀ x ∈ N, h x = 0) {x : ℝⁿ} (hx : x ∈ N) : fderiv ℝ h x (f x) = 0 := by
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hf 0 x
  have hψ1 : IsIntegralCurveOn ψ (fun _ x => f x) (Icc 0 1) := hψ.mono Icc_subset_Ici_self
  have hstay : ∀ t ∈ Icc (0 : ℝ) 1, ψ t ∈ N := hN 0 1 ψ hψ1 (hψ0 ▸ hx)
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hchain : HasDerivWithinAt (h ∘ ψ) (fderiv ℝ h (ψ 0) (f (ψ 0))) (Icc 0 1) 0 :=
    (hh (ψ 0)).hasFDerivAt.comp_hasDerivWithinAt 0 (hψ1 0 hmem0)
  have hconst : HasDerivWithinAt (h ∘ ψ) 0 (Icc 0 1) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) _ (0 : ℝ)).congr (fun s hs => hzero _ (hstay s hs))
      (hzero _ (hstay 0 hmem0))
  rw [← hψ0]
  exact (uniqueDiffOn_Icc zero_lt_one 0 hmem0).eq_deriv _ hchain hconst

/-- A forward solution in a compact positively invariant set along which `V̇ ≤ 0`: `V ∘ φ`
converges, and `V` is constant on the ω-limit set. -/
@[tmio T, powerlib_foundation] private theorem exists_const_on_omegaLimitTraj {f : ℝⁿ → ℝⁿ}
    {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} (hV : ContDiff ℝ 1 V) (hΩc : IsCompact Ω)
    (hΩi : IsPositivelyInvariant Ω f) (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∃ c : ℝ, ∀ y ∈ omegaLimitTraj φ, V y = c := by
  have hphi : ∀ t ≥ (0 : ℝ), φ t ∈ Ω := fun t ht =>
    hΩi 0 t φ (hφ.mono fun r hr => hr.1) hφ0 t ⟨ht, le_rfl⟩
  have hanti : AntitoneOn (V ∘ φ) (Ici 0) :=
    antitoneOn_V_comp_traj (hV.differentiable (by norm_num)) hV.continuous (convex_Ici 0) hφ
      fun t ht => by
        rw [interior_Ici] at ht
        exact hLie (φ t) (hphi t (le_of_lt ht))
  obtain ⟨xm, -, hxm⟩ := hΩc.exists_isMinOn ⟨φ 0, hφ0⟩ hV.continuous.continuousOn
  set g : ℝ → ℝ := fun t => (V ∘ φ) (max t 0) with hg
  have hga : Antitone g := fun s t hst =>
    hanti (mem_Ici.mpr (le_max_right s 0)) (mem_Ici.mpr (le_max_right t 0))
      (max_le_max_right 0 hst)
  have hgb : BddBelow (range g) :=
    ⟨V xm, fun _ ⟨t, ht⟩ => ht ▸ hxm (hphi (max t 0) (le_max_right t 0))⟩
  have hgt : Tendsto g atTop (𝓝 (⨅ t, g t)) := tendsto_atTop_ciInf hga hgb
  have hVt : Tendsto (V ∘ φ) atTop (𝓝 (⨅ t, g t)) :=
    hgt.congr' ((eventually_ge_atTop 0).mono fun t ht => by simp [hg, max_eq_left ht])
  refine ⟨⨅ t, g t, fun y hy => ?_⟩
  rw [omegaLimitTraj, mem_omegaLimit_iff_frequently] at hy
  have hcl : MapClusterPt (V y) atTop (V ∘ φ) := by
    rw [mapClusterPt_iff_frequently]
    intro U hU
    refine (hy (V ⁻¹' U) (hV.continuous.continuousAt hU)).mono fun t ht => ?_
    simp only [univ_inter, Set.Nonempty] at ht
    obtain ⟨_, hm⟩ := ht
    simpa using hm
  exact eq_of_nhds_neBot (NeBot.mono hcl.clusterPt (inf_le_inf_left _ hVt))

/-- **`V̇ = 0` on the ω-limit set, for a Lipschitz field.** `V ∘ φ` converges, so `V` is constant
on `ω(φ)`; the forward solution through an ω-limit point stays in `ω(φ)`
(`isPositivelyInvariant_omegaLimitTraj`), so the derivative of `V` along it vanishes. -/
@[tmio T, powerlib_foundation] theorem lieDeriv_eq_zero_on_omegaLimitTraj_of_lipschitz
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} {K : NNReal} (hf : LipschitzWith K f)
    (hV : ContDiff ℝ 1 V) (hΩc : IsCompact Ω) (hΩi : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∀ y ∈ omegaLimitTraj φ, fderiv ℝ V y (f y) = 0 := by
  obtain ⟨c, hc⟩ := exists_const_on_omegaLimitTraj hV hΩc hΩi hLie hφ hφ0
  intro y hy
  have h := lieDeriv_eq_zero_of_isPositivelyInvariant hf
    (isPositivelyInvariant_omegaLimitTraj hf hφ) (h := fun x => V x - c)
    ((hV.differentiable (by norm_num)).sub_const c) (fun x hx => by rw [hc x hx, sub_self]) hy
  rwa [fderiv_sub_const] at h

/-- **LaSalle's invariance principle for a globally Lipschitz field.** `Ω` compact and positively
invariant, `V` `C¹` with `V̇ ≤ 0` on `Ω`, and `M` containing every positively invariant subset of
`{x ∈ Ω | V̇ x = 0}`: every forward solution starting in `Ω` converges to `M`. -/
@[tmio T, powerlib_foundation] theorem lasalle_invariance_principle_of_lipschitz
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω M : Set ℝⁿ} {K : NNReal} (hf : LipschitzWith K f)
    (hV : ContDiff ℝ 1 V) (hΩc : IsCompact Ω) (hΩi : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) (hφ0 : φ 0 ∈ Ω)
    (hM : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ M) :
    Tendsto φ atTop (𝓝ˢ M) := by
  have hphi : ∀ t ≥ (0 : ℝ), φ t ∈ Ω := fun t ht =>
    hΩi 0 t φ (hφ.mono fun r hr => hr.1) hφ0 t ⟨ht, le_rfl⟩
  have hωΩ : omegaLimitTraj φ ⊆ Ω := by
    have hsub : omegaLimitTraj φ ⊆
        closure (image2 (fun (t : ℝ) (_ : Unit) => φ t) (Ici 0) univ) :=
      omegaLimit_subset_closure_image2 atTop (fun (t : ℝ) (_ : Unit) => φ t) univ
        (Ici_mem_atTop 0)
    have himg : image2 (fun (t : ℝ) (_ : Unit) => φ t) (Ici 0) univ ⊆ Ω := by
      rintro x ⟨t, ht, _, _, rfl⟩
      exact hphi t ht
    exact hsub.trans ((closure_mono himg).trans hΩc.isClosed.closure_eq.le)
  have hωM : omegaLimitTraj φ ⊆ M :=
    hM _ (fun y hy => ⟨hωΩ hy,
      lieDeriv_eq_zero_on_omegaLimitTraj_of_lipschitz hf hV hΩc hΩi hLie hφ hφ0 y hy⟩)
      (isPositivelyInvariant_omegaLimitTraj hf hφ)
  have hc₂ : ∀ᶠ t in atTop, MapsTo (fun (_ : Unit) => φ t) univ Ω :=
    (eventually_ge_atTop 0).mono fun t ht () _ => hphi t ht
  rw [tendsto_def]
  intro U hU
  rw [mem_nhdsSet_iff_exists] at hU
  obtain ⟨W, hWo, hMW, hWU⟩ := hU
  have hev : ∀ᶠ t in atTop, MapsTo (fun (_ : Unit) => φ t) univ W :=
    eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atTop
      (fun (t : ℝ) (_ : Unit) => φ t) univ hΩc hc₂ hWo (hωM.trans hMW)
  exact hev.mono fun t ht => hWU (ht (mem_univ ()))

/-- **Global asymptotic stability by LaSalle, for a globally Lipschitz field.** `f` globally
Lipschitz with `f x_eq = 0`; `V` `C¹`, positive definite about `x_eq`, radially unbounded, with
`V̇ ≤ 0`; every positively invariant subset of `{V̇ = 0}` lies in `{x_eq}`. Then `x_eq` is globally
asymptotically stable: sublevel sets are compact and positively invariant, and LaSalle's principle
(`lasalle_invariance_principle_of_lipschitz`) applies on each. -/
@[tmio T, powerlib_foundation] theorem globallyAsymptoticallyStable_of_lasalle_lipschitz
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} {K : NNReal} (hn : 0 < n)
    (hf : LipschitzWith K f) (hf0 : f x_eq = 0) (hV : ContDiff ℝ 1 V) (hV0 : V x_eq = 0)
    (hVpos : ∀ x, x ≠ x_eq → 0 < V x) (hradial : Tendsto V (comap norm atTop) atTop)
    (hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0)
    (hM : ∀ N : Set ℝⁿ, N ⊆ {x | fderiv ℝ V x (f x) = 0} → IsPositivelyInvariant N f →
      N ⊆ {x_eq}) :
    Flow.GloballyAsymptoticallyStable f x_eq := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  refine ⟨hf0, Flow.forwardComplete_of_lipschitzWith hf, ?_, ?_⟩
  · exact lyapunov_stable hn ⟨isOpen_univ, mem_univ _, hVd.continuous, hVd, hV0,
      fun x _ hx => hVpos x hx, fun x _ => hdec x⟩
  · intro t₀ φ hφ
    have hinv : IsPositivelyInvariant {x | V x ≤ V (φ t₀)} f := by
      have h := isPositivelyInvariant_sublevel_of_isOpen (f := f) (c := V (φ t₀))
        isOpen_univ hVd (fun x _ => hdec x) (by
          simpa using (isClosed_le hVd.continuous continuous_const))
      simpa using h
    have hconv := lasalle_invariance_principle_of_lipschitz hf hV
      (isCompact_sublevel_set V hV.continuous hradial (V (φ t₀))) hinv (fun x _ => hdec x)
      (isIntegralCurveOn_shift_Ici hφ) (by simp [SublevelSet])
      (M := {x_eq}) fun N hN hNi => hM N (fun x hx => (hN hx).2) hNi
    rw [nhdsSet_singleton] at hconv
    exact Tendsto.congr (fun x => by simp)
      (hconv.comp (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id))

end powerlib.Dynamics.LaSalle
