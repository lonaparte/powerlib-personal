import theorem.Periodic.FlipReduction
import theorem.Map.AsymptoticPhase
import theorem.Map.DegenerateFlip

/-! # A periodic orbit with a simple multiplier `−1` and a degenerate flip coefficient

When the flip coefficient `a² + b` of `theorem/Periodic/FlipReduction.lean` vanishes, the period
map `P` at its fixed point `p` is decided by the fifth-order coefficient of the map restricted to a
centre manifold. This module computes that restricted map to any order from a candidate curve: if
`t ↦ p + t v + η(t)` (`w ∘ η = 0`, `η` tangent to `0`) is invariant up to a defect `O(t^q)`,
the restricted map `r` of the true (cut-off) centre manifold satisfies
`r(x) = w(P(p + x v + η(x)) − p) + O(x^{q+1})`.
The candidate is read in the adapted coordinates of `FlipReduction` as a graph `x ↦ T η(x)`, its
defect there is `−T D(x)` with the defect `D` in `ℝⁿ`, the approximation theorem
(`Map.CenterManifold.isBigO_sub_of_defect`) puts the centre manifold within `O(x^q)` of it, and
the nonlinearity, flat to second order, turns that into `O(x^{q+1})` on the centre coordinate.
With `q = 5` and the expansion `w(P(p + t v + η(t)) − p) = −t + c₂t² + c₃t³ + c₄t⁴ + c₅t⁵ +
O(t⁶)`, a degenerate flip `c₂² + c₃ = 0` is decided by the sign of `c₅ + 3c₂c₄ − 2c₂⁴`
(`theorem/Map/DegenerateFlip.lean`). With the asymptotic phase
(`theorem/Map/AsymptoticPhase.lean`) the reduction also transfers Lyapunov stability and
instability in both directions.

Scope.
* The setting of `theorem/Periodic/FlipReduction.lean`: the map semantics on `ℝⁿ`, a map `P` with
  a fixed point `p`, strict derivative `M` there, `M v = −v`, `w ∘ M = −w`, `w v = 1`, a power of
  the deflated map `M + v wᵀ` of norm below one. For a periodic orbit `P` is the period map, and
  its regularity is a **hypothesis**: the nonlinearity `N e = P(p + e) − p − M e` is flat to
  second order, `‖N e − N e'‖ ≤ L max(‖e‖, ‖e'‖) ‖e − e'‖` near `0` (a period map of class `C²`);
  no Taylor expansion of `P` is assumed.
* The coefficients are those of the scalar map `t ↦ w(P(p + t v + η(t)) − p)` along a candidate
  curve with defect `O(t⁵)`, for instance the polynomial `η(t) = t² k₂ + t³ k₃ + t⁴ k₄` of the
  projection method. Their expression through the multilinear Taylor coefficients of `P` (the
  homological equations for `k₂, k₃, k₄` and the resulting formulas for `c₄`, `c₅`) is not
  derived here: the theorems take the expansion of the scalar map as a hypothesis.
* `c₅ + 3c₂c₄ − 2c₂⁴ = 0` is not decided (the next odd order is needed, and no finite order
  suffices in general: `Map.flat_jet_undecided`).
* Generic; nothing here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.4 (restricted
normalized maps computed from a polynomial approximation of the centre manifold) and §9.5
(degenerate flip); Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2 (Theorem 3, the
approximation theorem); the open item of `theorem/Periodic/FlipReduction.lean` (Scope: "`a² + b =
0` (a degenerate flip) is not decided here").

Results.
* `lyapunovStable_of_translate` (Lyapunov stability of `e ↦ P(p + e) − p` at `0` gives that of
  `P` at `p`).
* **The restricted map from a candidate**: `exists_reduced_map_of_candidate` — a map
  `r : ℝ¹ → ℝ¹` with `r(x) = w(P(p + x v + η(x)) − p) + O(‖x‖^{q+1})`, whose local asymptotic
  stability gives that of `P`, and whose Lyapunov stability is that of `P` (so `r` is unstable
  exactly when `P` is).
* **The degenerate flip of a periodic orbit**: `localAsymptoticStable_of_degenerateFlip_pos`
  (`c₂² + c₃ = 0`, `c₅ + 3c₂c₄ − 2c₂⁴ > 0`: locally asymptotically, not exponentially, stable),
  `unstable_of_degenerateFlip_neg` (`c₅ + 3c₂c₄ − 2c₂⁴ < 0`: unstable).

Corrections.
None: an extension (the degenerate flip `a² + b = 0`, left undecided by
`theorem/Periodic/FlipReduction.lean`).

Family and connection conclusions.
None: static evidence on maps (the period map of a periodic orbit).
-/

noncomputable section

open Filter Topology Asymptotics

namespace powerlib.Periodic.FlipReduction

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

variable {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {v : EuclideanSpace ℝ (Fin n)} {w : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}

/-- Lyapunov stability of the map read from the fixed point, `e ↦ P(p + e) − p` at `0`, gives
that of `P` at `p`. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_translate {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (h : Map.LyapunovStable (fun e => P (p + e) - p) 0) : Map.LyapunovStable P p := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  refine ⟨δ, hδ, fun y hy k => ?_⟩
  have := hb (y - p) (by rwa [sub_zero]) k
  rwa [iterate_translate, add_sub_cancel, sub_zero] at this

/-- **The restricted map from a candidate curve.** In the setting of `exists_reduced_map` (`P`
fixes `p`, strict derivative `M`, `M v = −v`, `w ∘ M = −w`, `w v = 1`, a power of `M + v wᵀ` of
norm below one), let the nonlinearity `N e = P(p + e) − p − M e` be flat to second order,
`‖N e − N e'‖ ≤ L max(‖e‖, ‖e'‖) ‖e − e'‖` for `‖e‖, ‖e'‖ ≤ ρ₀`, and let `η : ℝ → ℝⁿ`
(`η(0) = 0`, `η'(0) = 0` strictly, `w ∘ η = 0`) describe a candidate curve `t ↦ p + t v + η(t)`
whose invariance defect `Q(P(p + t v + η t) − p) − η(w(P(p + t v + η t) − p))` is `O(t^q)`
(`Q e = e − (w e) v`, `q ≥ 1`). Then there is a map `r : ℝ¹ → ℝ¹` (the map restricted to a
centre manifold, in the coordinate `w`) with `r(x) = w(P(p + x v + η(x)) − p) + O(‖x‖^{q+1})`,
whose local asymptotic stability gives that of `P` at `p`, and which is Lyapunov stable exactly
when `P` is at `p`. -/
@[tmio T, powerlib_foundation] theorem exists_reduced_map_of_candidate {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v) (hw : ∀ e, w (M e) = -w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflate M v w ^ m‖ < 1) {L ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) (hN : ∀ e e' : ℝⁿ, ‖e‖ ≤ ρ₀ → ‖e'‖ ≤ ρ₀ →
      ‖nonlin P p M e - nonlin P p M e'‖ ≤ L * max ‖e‖ ‖e'‖ * ‖e - e'‖)
    {η : ℝ → ℝⁿ} (hη : HasStrictDerivAt η 0 0) (hη0 : η 0 = 0) (hwη : ∀ t, w (η t) = 0)
    {q : ℕ} (hq : 1 ≤ q)
    (hD : (fun t : ℝ => specProj v w (P (p + (t • v + η t)) - p) -
      η (w (P (p + (t • v + η t)) - p))) =O[𝓝 0] fun t => t ^ q) :
    ∃ r : ℝ¹ → ℝ¹,
      (fun x : ℝ¹ => r x 0 - w (P (p + (x 0 • v + η (x 0))) - p)) =O[𝓝 0]
        (fun x => ‖x‖ ^ (q + 1)) ∧
      (Map.LocalAsymptoticStable r 0 → Map.LocalAsymptoticStable P p) ∧
      (Map.LyapunovStable r 0 ↔ Map.LyapunovStable P p) := by
  set Ld := deflate M v w with hLdef
  obtain ⟨θ, hθ0, hθ1, hθm⟩ := exists_rate hm hLm
  -- the size of the nonlinearities
  have hεr : 0 < (1 - θ) / (2 * ((q : ℝ) + 2)) := div_pos (by linarith) (by positivity)
  let ε : NNReal := ⟨(1 - θ) / (2 * ((q : ℝ) + 2)), hεr.le⟩
  have hεe : (ε : ℝ) = (1 - θ) / (2 * ((q : ℝ) + 2)) := rfl
  have hε0 : 0 < ε := by rw [← NNReal.coe_pos, hεe]; exact hεr
  have hqε : ((q : ℝ) + 2) * ε = (1 - θ) / 2 := by rw [hεe]; field_simp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hεpos : (0 : ℝ) < ε := hεr
  have h3ε : 3 * (ε : ℝ) ≤ (1 - θ) / 2 := by nlinarith
  have hgap : θ + 3 * ε < 1 := by linarith
  have hθ2 : θ + 2 * ε < 1 := by linarith
  have hεa : (ε : ℝ) < 1 := by linarith
  have hκ1 : θ + ε < 1 - ε := by linarith
  have hκq : θ + ε < (1 - ε) ^ q := by
    have hb := one_add_mul_le_pow (a := -(ε : ℝ)) (by linarith) q
    rw [← sub_eq_add_neg] at hb
    nlinarith
  -- coordinates and the linear part
  set Φ := coordMap M v w m θ with hΦ
  set Ψ := coordInv (n := n) v hm with hΨ
  set B := orbitShift m hm θ Ld with hBdef
  set A : ℝ¹ →L[ℝ] ℝ¹ := -ContinuousLinearMap.id ℝ ℝ¹ with hAdef
  have hAs : Function.Surjective A := fun x => ⟨-x, by simp [hAdef]⟩
  have hA : ∀ x, 1 * ‖x‖ ≤ ‖A x‖ := fun x => by simp [hAdef]
  have hB : ∀ u, ‖B u‖ ≤ θ * ‖u‖ := norm_orbitShift_le hm hθ0 hθm
  -- the cut-off nonlinearity
  obtain ⟨hN', hN0⟩ := nonlin_spec hP hPp
  set ε' : NNReal := ε / ((‖Φ‖₊ + 1) * (‖Ψ‖₊ + 1)) with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨ρ₁, hρ₁, Nc, hNcl, hNc0, hNcN⟩ :=
    Map.CenterManifold.exists_lipschitz_cutoff hN' hN0 hε'0
  set f := cutF M v w hm θ Nc with hfdef
  set g := cutG M v w hm θ Nc with hgdef
  have hK : ‖Φ‖₊ * ε' * ‖Ψ‖₊ ≤ ε := by
    rw [hε', ← NNReal.coe_le_coe]
    push_cast
    have ha := norm_nonneg Φ
    have hb := norm_nonneg Ψ
    have hε := ε.coe_nonneg
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hε ha, mul_nonneg hε hb, mul_nonneg (mul_nonneg hε ha) hb]
  have hfl : LipschitzWith ε f := (lipschitzWith_cut hm θ hNcl).1.weaken hK
  have hgl : LipschitzWith ε g := (lipschitzWith_cut hm θ hNcl).2.weaken hK
  have hf0 : f 0 = 0 := by simp [hfdef, cutF, hNc0]
  have hg0 : g 0 = 0 := by simp [hgdef, cutG, hNc0]
  -- the centre manifold, its range and its graph
  set h := Map.CenterManifold.centreGraph A B f g with hhdef
  obtain ⟨hh, hh0, hinv⟩ :=
    Map.CenterManifold.centreGraph_spec hAs hA hB hθ0.le hfl hgl hf0 hg0 (by simpa using hgap)
  set T : ℝⁿ →L[ℝ] (Fin m → ℝⁿ) := (orbitEmb m θ Ld).comp (specProj v w) with hTdef
  set Kr : Submodule ℝ (Fin m → ℝⁿ) := LinearMap.range (T : ℝⁿ →ₗ[ℝ] (Fin m → ℝⁿ)) with hKr
  have hKc : IsClosed (Kr : Set (Fin m → ℝⁿ)) := Submodule.closed_of_finiteDimensional _
  have hBK : ∀ y ∈ Kr, B y ∈ Kr := by
    rintro _ ⟨z, rfl⟩
    refine ⟨M z, ?_⟩
    simp only [hTdef, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply, hBdef]
    rw [orbitShift_orbitEmb hm hθ0.ne', (deflate_specProj hv hw hwv z).1]
  have hgK : ∀ x, ∀ y ∈ Kr, g (x, y) ∈ Kr := fun x y _ => ⟨Nc (Ψ (x, y)), rfl⟩
  have hhK : ∀ x, h x ∈ Kr := fun x =>
    Map.CenterManifold.centreGraph_mem hKc hBK hgK hAs hA hB hθ0.le hfl hgl hf0 hg0
      (by simpa using hgap) x
  have hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x) := fun x => by
    obtain ⟨z, hz⟩ := hhK x
    rw [← hz]
    exact coordMap_coordInv hwv hm θ x z
  -- the map read in the coordinates
  have hG : ∀ e, ‖e‖ < ρ₁ →
      Φ ((fun e => P (p + e) - p) e) = Map.CenterManifold.splitMap A B f g (Φ e) :=
    fun e he => coordMap_conj hv hw hwv hm hθ0.ne' (hNcN e he.le)
  -- identities along a curve `e = t v + y`, `w y = 0`
  have hPe : ∀ e, P (p + e) - p = M e + nonlin P p M e := fun e => by simp only [nonlin]; abel
  have hwP : ∀ (t : ℝ) (y : ℝ¹ → ℝⁿ) (x : ℝ¹), w (y x) = 0 →
      w (P (p + (t • v + y x)) - p) = -t + w (nonlin P p M (t • v + y x)) := fun t y x hy => by
    rw [hPe, map_add, hw]
    simp [map_add, map_smul, hwv, hy]
  -- the candidate graph in the coordinates
  set φ : ℝ¹ → (Fin m → ℝⁿ) := fun x => orbitEmb m θ Ld (η (x 0)) with hφdef
  have hφ0 : φ 0 = 0 := by simp [hφdef, hη0]
  have hp0 : HasStrictFDerivAt (fun x : ℝ¹ => x 0)
      (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) 0 := by
    have e : (fun x : ℝ¹ => x 0) = ⇑(EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) := by
      funext x; simp
    rw [e]
    exact ContinuousLinearMap.hasStrictFDerivAt (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ)
  have hφ : HasStrictFDerivAt φ (0 : ℝ¹ →L[ℝ] (Fin m → ℝⁿ)) 0 := by
    have h2 : HasStrictFDerivAt η (0 : ℝ →L[ℝ] ℝⁿ) ((fun x : ℝ¹ => x 0) 0) := by
      have := hη.hasStrictFDerivAt
      simpa using this
    have h3 := (orbitEmb m θ Ld).hasStrictFDerivAt.comp (0 : ℝ¹) (h2.comp (0 : ℝ¹) hp0)
    convert h3 using 1
    ext x
    simp
  have hx0lim : Tendsto (fun x : ℝ¹ => x 0) (𝓝 0) (𝓝 0) := by
    simpa using hp0.continuousAt.tendsto
  have hu1' : (fun x : ℝ¹ => x 0) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    simpa using isBigO_coord_pow 1
  have hηO : (fun x : ℝ¹ => η (x 0)) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    have h1 : η =O[𝓝 0] fun t : ℝ => t := by
      have := hη.hasDerivAt.isLittleO
      simp only [hη0, sub_zero, smul_zero] at this
      exact this.isBigO
    exact (h1.comp_tendsto hx0lim).trans hu1'
  have heη : (fun x : ℝ¹ => x 0 • v + η (x 0)) =O[𝓝 0] fun x => ‖x‖ ^ 1 :=
    (isBigO_smul_const hu1' v).add hηO
  have hnorm0 : Tendsto (fun x : ℝ¹ => ‖x‖ ^ 1) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_norm_zero (E := ℝ¹)).pow 1
  have hρ01 : 0 < min ρ₁ ρ₀ := lt_min hρ₁ hρ₀
  have hevη : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + η (x 0)‖ ≤ min ρ₁ ρ₀ := by
    have := (heη.trans_tendsto hnorm0).eventually (Metric.closedBall_mem_nhds 0 hρ01)
    filter_upwards [this] with x hx
    simpa using hx
  -- its invariance defect is `−T D` with the defect `D` in `ℝⁿ`
  have hDc : (fun x => φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)) =O[𝓝 0]
      fun x => ‖x‖ ^ q := by
    have hD' := ((hD.comp_tendsto hx0lim).trans (isBigO_coord_pow q))
    refine (((orbitEmb m θ Ld).isBigO_comp _ _).trans hD').neg_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [hevη] with x hx
    have hx1 : ‖x 0 • v + η (x 0)‖ ≤ ρ₁ := hx.trans (min_le_left _ _)
    have hΨφ : coordInv v hm (x, φ x) = x 0 • v + η (x 0) := by
      rw [coordInv_apply]
      show x 0 • v + orbitEmb m θ Ld (η (x 0)) ⟨0, hm⟩ = _
      rw [orbitEmb_zero]
    have hNe := hNcN _ hx1
    have hfφ : f (x, φ x) = centreCoord w (nonlin P p M (x 0 • v + η (x 0))) := by
      simp only [hfdef, cutF, hΨφ, hNe]; rfl
    have hgφ : g (x, φ x) =
        orbitEmb m θ Ld (specProj v w (nonlin P p M (x 0 • v + η (x 0)))) := by
      simp only [hgdef, cutG, hΨφ, hNe]; rfl
    have hc : (A x + f (x, φ x)) 0 = -x 0 + w (nonlin P p M (x 0 • v + η (x 0))) := by
      rw [hfφ]; simp [hAdef, centreCoord_apply_zero]
    have hQP : specProj v w (P (p + (x 0 • v + η (x 0))) - p) =
        Ld (η (x 0)) + specProj v w (nonlin P p M (x 0 • v + η (x 0))) := by
      rw [hPe, map_add, specProj_apply (e := M _), hw, hLdef, deflate_apply, hwη, zero_smul,
        add_zero]
      simp only [map_add, map_smul, hv, hwv, hwη, smul_eq_mul, mul_one, add_zero]
      module
    have hwP' := hwP (x 0) (fun x => η (x 0)) x (hwη _)
    show -(orbitEmb m θ Ld (specProj v w (P (p + (x 0 • v + η (x 0))) - p) -
        η (w (P (p + (x 0 • v + η (x 0))) - p)))) =
      orbitEmb m θ Ld (η ((A x + f (x, φ x)) 0)) - B (orbitEmb m θ Ld (η (x 0))) - g (x, φ x)
    rw [hc, hBdef, orbitShift_orbitEmb hm hθ0.ne', hgφ, hQP, hwP']
    simp only [map_sub, map_add]
    abel
  -- the approximation of the centre manifold by the candidate
  have happrox := Map.CenterManifold.isBigO_sub_of_defect hAs hA hB hθ0.le hfl hgl hf0 hg0
    (by simpa using hεa) hh hh0 hinv hφ hφ0 hq hDc (by simpa using hκq) (by simpa using hκ1)
  set π₀ : (Fin m → ℝⁿ) →L[ℝ] ℝⁿ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin n)) ⟨0, hm⟩
    with hπ₀
  have hy : (fun x : ℝ¹ => h x ⟨0, hm⟩ - η (x 0)) =O[𝓝 0] fun x => ‖x‖ ^ q := by
    refine ((π₀.isBigO_comp _ _).trans happrox).congr_left fun x => ?_
    show (h x - orbitEmb m θ Ld (η (x 0))) ⟨0, hm⟩ = _
    rw [Pi.sub_apply, orbitEmb_zero]
  have heh : (fun x : ℝ¹ => x 0 • v + h x ⟨0, hm⟩) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    have := heη.add (hy.trans (isBigO_norm_pow_of_le hq))
    refine this.congr_left fun x => ?_
    abel
  have hevh : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + h x ⟨0, hm⟩‖ ≤ min ρ₁ ρ₀ := by
    have := (heh.trans_tendsto hnorm0).eventually (Metric.closedBall_mem_nhds 0 hρ01)
    filter_upwards [this] with x hx
    simpa using hx
  -- the reduced map against the candidate's map
  have hbound : (fun x : ℝ¹ => ‖w‖ * |L| * ((‖x 0 • v + h x ⟨0, hm⟩‖ + ‖x 0 • v + η (x 0)‖) *
      ‖h x ⟨0, hm⟩ - η (x 0)‖)) =O[𝓝 0] fun x => ‖x‖ ^ (q + 1) := by
    have := ((heh.norm_left.add heη.norm_left).mul hy.norm_left).const_mul_left (‖w‖ * |L|)
    refine this.congr_right fun x => ?_
    ring
  have hred : (fun x : ℝ¹ => Map.CenterManifold.reducedMap A f h x 0 -
      w (P (p + (x 0 • v + η (x 0))) - p)) =O[𝓝 0] fun x => ‖x‖ ^ (q + 1) := by
    refine IsBigO.trans ?_ hbound
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hevh, hevη] with x hxh hxη
    have hΨh : coordInv v hm (x, h x) = x 0 • v + h x ⟨0, hm⟩ := by rw [coordInv_apply]
    have hfh : f (x, h x) = centreCoord w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) := by
      simp only [hfdef, cutF, hΨh, hNcN _ (hxh.trans (min_le_left _ _))]; rfl
    have hc : Map.CenterManifold.reducedMap A f h x 0 =
        -x 0 + w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) := by
      rw [Map.CenterManifold.reducedMap, hfh]; simp [hAdef, centreCoord_apply_zero]
    rw [hc, hwP (x 0) (fun x => η (x 0)) x (hwη _)]
    have e : -x 0 + w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) -
        (-x 0 + w (nonlin P p M (x 0 • v + η (x 0)))) =
        w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩) - nonlin P p M (x 0 • v + η (x 0))) := by
      rw [map_sub]; ring
    rw [e, one_mul]
    have hN1 := hN _ _ (hxh.trans (min_le_right _ _)) (hxη.trans (min_le_right _ _))
    have hsub : (x 0 • v + h x ⟨0, hm⟩) - (x 0 • v + η (x 0)) = h x ⟨0, hm⟩ - η (x 0) := by
      abel
    rw [hsub] at hN1
    have hmax : max ‖x 0 • v + h x ⟨0, hm⟩‖ ‖x 0 • v + η (x 0)‖ ≤
        ‖x 0 • v + h x ⟨0, hm⟩‖ + ‖x 0 • v + η (x 0)‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    have hnn : 0 ≤ ‖w‖ * |L| * ((‖x 0 • v + h x ⟨0, hm⟩‖ + ‖x 0 • v + η (x 0)‖) *
        ‖h x ⟨0, hm⟩ - η (x 0)‖) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    have hLm : L * max ‖x 0 • v + h x ⟨0, hm⟩‖ ‖x 0 • v + η (x 0)‖ ≤
        |L| * (‖x 0 • v + h x ⟨0, hm⟩‖ + ‖x 0 • v + η (x 0)‖) :=
      mul_le_mul (le_abs_self L) hmax (le_max_of_le_left (norm_nonneg _)) (abs_nonneg L)
    calc |w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩) - nonlin P p M (x 0 • v + η (x 0)))|
        ≤ ‖w‖ * ‖nonlin P p M (x 0 • v + h x ⟨0, hm⟩) - nonlin P p M (x 0 • v + η (x 0))‖ := by
          rw [← Real.norm_eq_abs]; exact w.le_opNorm _
      _ ≤ ‖w‖ * (L * max ‖x 0 • v + h x ⟨0, hm⟩‖ ‖x 0 • v + η (x 0)‖ *
            ‖h x ⟨0, hm⟩ - η (x 0)‖) := mul_le_mul_of_nonneg_left hN1 (norm_nonneg _)
      _ ≤ ‖w‖ * (|L| * (‖x 0 • v + h x ⟨0, hm⟩‖ + ‖x 0 • v + η (x 0)‖) *
            ‖h x ⟨0, hm⟩ - η (x 0)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLm (norm_nonneg _))
            (norm_nonneg _)
      _ = _ := by ring
  refine ⟨Map.CenterManifold.reducedMap A f h, hred,
    fun hr => localAsymptoticStable_of_translate
      (Map.CenterManifold.localAsymptoticStable_of_reduced hB hθ0.le hfl hgl hθ2 hh hh0 hinv
        (coordInv_coordMap hm θ) hρ₁ hG hr),
    fun hr => lyapunovStable_of_translate
      (Map.CenterManifold.lyapunovStable_of_reduced hAs hA hB hθ0.le hfl hgl
        (by simpa using hgap) hθ2 hh hh0 hinv (coordInv_coordMap hm θ) hρ₁ hG hr),
    fun hLS => Map.CenterManifold.lyapunovStable_reduced hh hh0 hinv hgraph hρ₁ hG
      (lyapunovStable_translate hLS)⟩

/-- The restricted map of `exists_reduced_map_of_candidate` with `q = 5` inherits a fifth-order
expansion of the candidate's map: `r(y) = −y + c₂y² + … + c₅y⁵ + O(y⁶)`. -/
@[tmio T, powerlib_foundation] private theorem reduced_expansion_five {r : ℝ¹ → ℝ¹}
    {R : ℝ → ℝ} {c₂ c₃ c₄ c₅ K ρ : ℝ} (hρ : 0 < ρ)
    (hrO : (fun x : ℝ¹ => r x 0 - R (x 0)) =O[𝓝 0] fun x => ‖x‖ ^ (5 + 1))
    (hR : ∀ t : ℝ, |t| ≤ ρ →
      |R t - (-t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 + c₅ * t ^ 5)| ≤ K * |t| ^ 6) :
    ∃ ρ' > 0, ∃ K', ∀ y : ℝ¹, ‖y‖ ≤ ρ' → |r y 0 - (-y 0 + c₂ * y 0 ^ 2 + c₃ * y 0 ^ 3 +
      c₄ * y 0 ^ 4 + c₅ * y 0 ^ 5)| ≤ K' * |y 0| ^ 6 := by
  obtain ⟨C, hC⟩ := hrO.bound
  obtain ⟨r₀, hr₀, hCb⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨min ρ (r₀ / 2), lt_min hρ (half_pos hr₀), C + K, fun y hy => ?_⟩
  have h1 := hCb (show dist y 0 < r₀ by
    rw [dist_zero_right]; exact hy.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr₀)))
  rw [Real.norm_eq_abs, norm_pow, norm_norm, NormalForm.norm_state1] at h1
  have h2 := hR (y 0) (by rw [← NormalForm.norm_state1]; exact hy.trans (min_le_left _ _))
  calc _ = |(r y 0 - R (y 0)) + (R (y 0) - (-y 0 + c₂ * y 0 ^ 2 + c₃ * y 0 ^ 3 +
        c₄ * y 0 ^ 4 + c₅ * y 0 ^ 5))| := by rw [sub_add_sub_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ C * |y 0| ^ 6 + K * |y 0| ^ 6 := add_le_add h1 h2
    _ = (C + K) * |y 0| ^ 6 := by ring

/-- **A degenerate flip of a periodic orbit, stable side.** Under the hypotheses of
`exists_reduced_map_of_candidate` with a candidate of defect `O(t⁵)`, let the map along the
candidate expand as `w(P(p + t v + η(t)) − p) = −t + c₂t² + c₃t³ + c₄t⁴ + c₅t⁵ + O(t⁶)`. If the
flip coefficient vanishes, `c₂² + c₃ = 0`, and `c₅ + 3c₂c₄ − 2c₂⁴ > 0`, the fixed point `p` of
`P` is locally asymptotically stable, and not exponentially stable (the multiplier `−1`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_degenerateFlip_pos
    {P : ℝⁿ → ℝⁿ} {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflate M v w ^ m‖ < 1) {L ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hN : ∀ e e' : ℝⁿ, ‖e‖ ≤ ρ₀ → ‖e'‖ ≤ ρ₀ →
      ‖nonlin P p M e - nonlin P p M e'‖ ≤ L * max ‖e‖ ‖e'‖ * ‖e - e'‖)
    {η : ℝ → ℝⁿ} (hη : HasStrictDerivAt η 0 0) (hη0 : η 0 = 0) (hwη : ∀ t, w (η t) = 0)
    (hD : (fun t : ℝ => specProj v w (P (p + (t • v + η t)) - p) -
      η (w (P (p + (t • v + η t)) - p))) =O[𝓝 0] fun t => t ^ 5)
    {c₂ c₃ c₄ c₅ K ρ : ℝ} (hρ : 0 < ρ)
    (hR : ∀ t : ℝ, |t| ≤ ρ → |w (P (p + (t • v + η t)) - p) -
      (-t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 + c₅ * t ^ 5)| ≤ K * |t| ^ 6)
    (hdeg : c₂ ^ 2 + c₃ = 0) (hκ : 0 < c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4) :
    Map.LocalAsymptoticStable P p ∧ ¬ Map.LocallyExponentiallyStable P p := by
  obtain ⟨r, hrO, hLAS, -⟩ := exists_reduced_map_of_candidate hP hPp hv hw hwv hm hLm hρ₀ hN
    hη hη0 hwη (by norm_num) hD
  obtain ⟨ρ', hρ', K', hK'⟩ := reduced_expansion_five hρ hrO hR
  refine ⟨hLAS (Map.degenerateFlip_localAsymptoticStable hρ' hdeg hκ hK').1, ?_⟩
  have hv0 : v ≠ 0 := by rintro rfl; simp at hwv
  exact Map.not_locallyExponentiallyStable_of_eigenvector hP.hasFDerivAt hPp hv0
    (μ := -1) (by rw [hv, neg_one_smul]) (by norm_num)

/-- **A degenerate flip of a periodic orbit, unstable side.** Under the hypotheses of
`localAsymptoticStable_of_degenerateFlip_pos`, if `c₂² + c₃ = 0` and `c₅ + 3c₂c₄ − 2c₂⁴ < 0`,
the fixed point `p` of `P` is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_degenerateFlip_neg {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflate M v w ^ m‖ < 1) {L ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hN : ∀ e e' : ℝⁿ, ‖e‖ ≤ ρ₀ → ‖e'‖ ≤ ρ₀ →
      ‖nonlin P p M e - nonlin P p M e'‖ ≤ L * max ‖e‖ ‖e'‖ * ‖e - e'‖)
    {η : ℝ → ℝⁿ} (hη : HasStrictDerivAt η 0 0) (hη0 : η 0 = 0) (hwη : ∀ t, w (η t) = 0)
    (hD : (fun t : ℝ => specProj v w (P (p + (t • v + η t)) - p) -
      η (w (P (p + (t • v + η t)) - p))) =O[𝓝 0] fun t => t ^ 5)
    {c₂ c₃ c₄ c₅ K ρ : ℝ} (hρ : 0 < ρ)
    (hR : ∀ t : ℝ, |t| ≤ ρ → |w (P (p + (t • v + η t)) - p) -
      (-t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 + c₅ * t ^ 5)| ≤ K * |t| ^ 6)
    (hdeg : c₂ ^ 2 + c₃ = 0) (hκ : c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4 < 0) :
    Map.Unstable P p := by
  obtain ⟨r, hrO, -, hLS⟩ := exists_reduced_map_of_candidate hP hPp hv hw hwv hm hLm hρ₀ hN
    hη hη0 hwη (by norm_num) hD
  obtain ⟨ρ', hρ', K', hK'⟩ := reduced_expansion_five hρ hrO hR
  exact fun hP' => Map.degenerateFlip_unstable hρ' hdeg hκ hK' (hLS.mpr hP')

end powerlib.Periodic.FlipReduction
