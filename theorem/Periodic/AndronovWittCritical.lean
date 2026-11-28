import theorem.Periodic.AndronovWitt
import theorem.Periodic.FoldOrbit

/-! # Periodic orbits with a critical nontrivial multiplier: the Poincaré map decides

The Andronov–Witt theorem (`theorem/Periodic/AndronovWitt.lean`) decides a nonconstant periodic
orbit `x_*` of `ẋ = f(x)` when every nontrivial multiplier lies off the unit circle on one side:
all inside — orbital exponential stability with asymptotic phase; one outside — orbital
instability. In the **critical case** (a nontrivial multiplier on the unit circle, the others
inside) the multipliers decide nothing (`theorem/Periodic/CriticalCycles.lean`: explicit planar
cycles with the multipliers `{1, 1}` that are attracting, repelling or neutral), and an
attracting cycle need not have an asymptotic phase. What remains true is the transfer of the
verdict of the Poincaré map `Π` of a transverse section (`theorem/Periodic/PoincareSection.lean`)
to the orbit, without rate and without phase:

* `Π` Lyapunov stable at `p = x_*(0)` ⇒ the orbit is orbitally stable
  (`orbit_stable_of_poincareMap`); `Π` locally asymptotically stable ⇒ the orbit attracts the
  solutions near it, `dist(x(t), x_*(ℝ)) → 0` (`orbit_attracts_of_poincareMap`); `Π` unstable ⇒
  the orbit is orbitally unstable (`orbit_unstable_of_poincareMap`). The proofs sample a solution
  at its successive crossings of the section, `y(t_k) = Πᵏ(y(0))`, with return times in
  `(T − s, T + s) ⊂ [T/2, 3T/2]` while the iterates stay in the box of the section, and use
  Grönwall's inequality between the crossings (`infDist_le_iterate`); a solution starting near
  `x_*(σ)` reaches the section box within the time `T` (`exists_time_near_section`). On the
  unstable side the escape of `Π` through the section is turned into a positive distance from the
  orbit by the compactness argument of `AndronovWitt.orbit_unstable`.
* At a simple critical eigenvalue of `DΠ(p)` (whose eigenvalue `0` belongs to the direction
  `f(p)` along the orbit, `PoincareSection.sectionMatrix_maps`) with the rest of the spectrum
  inside the unit circle, the centre-manifold reductions of `Π` decide the map, hence the orbit:
  at `−1` the flip coefficient `a² + b` of `theorem/Periodic/FlipReduction.lean`
  (`orbit_stable_of_flipCoeff_pos`, `orbit_unstable_of_flipCoeff_neg`), at `+1` the fold
  coefficient `a` and the cubic coefficient `b` of `theorem/Periodic/FoldReduction.lean`
  (`orbit_unstable_of_foldCoeff_ne_zero`, `orbit_stable_of_cubicCoeff_neg`,
  `orbit_unstable_of_cubicCoeff_pos`). The eigenvalue `+1` of `DΠ(p)` is a nontrivial
  multiplier `1`, i.e. the trivial multiplier `1` of the monodromy is double
  (`PoincareSection.one_mem_spectrum_deflate_iff`).

Scope.
* As in `theorem/Periodic/AndronovWitt.lean`: `ẋ = f(x)` on `ℝ^{Fin n}` with the sup norm, `f`
  globally `K`-Lipschitz (of class `C¹` where the return time is constructed), `x_*` a global
  `T`-periodic solution (`f(x_*(0)) ≠ 0` on the unstable side), solutions on `[0, ∞)`, orbital
  distance `Metric.infDist` to the range of `x_*`; the map semantics through `FlipOrbit.euclidMap`.
* The transfer theorems hold for every return time `τ` with `|τ(ξ) − T| < s ≤ T/2` on a ball
  about `p` (and, for instability, with `Π` on the section and differentiable at `p`), e.g. the
  one of `PoincareSection.exists_poincareMap` (`orbit_of_poincareMap` packages it). Orbital
  stability, attraction and instability are written out in the statements (no predicate on
  solutions is defined). Only the stable/unstable verdicts are transferred: no rate (a critical
  orbit attracts at most algebraically) and no asymptotic phase (it may fail to exist).
* The reductions take the cubic Taylor expansion of `Π` at `p` as a **hypothesis**
  (`‖Π(p + e) − p − Mm e − P₂(e, e) − P₃(e, e, e)‖ ≤ C ‖e‖⁴` near `0`); deriving it from the
  expansion of the flow (`theorem/Periodic/PeriodMapJet.lean`,
  `theorem/Periodic/PeriodMapTaylor.lean`) through the return time is not done here (it needs the
  second and third derivatives of the implicit return time). The degenerate cases `a² + b = 0`,
  `a = b = 0` and a pair of complex critical multipliers are not treated.
* Generic mathematics; no model family.

Source: A. A. Andronov and A. A. Witt, "Zur Stabilität nach Liapounoff", Phys. Z. Sowjetunion 4
(1933); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §1.5 (the Poincaré map of a
cycle; the cycle is stable/unstable with its fixed point), Ch. 4 and §5.4 (flip and fold of
fixed points of maps); Hirsch, Smale and Devaney, *Differential Equations, Dynamical Systems, and
an Introduction to Chaos*, Ch. 10; the open item of `theorem/Periodic/AndronovWitt.lean` (Scope:
"The critical case (a nontrivial multiplier on the unit circle, the others inside) is not decided
here").

Results.
* Coordinates and crossings: `infDist_le_iterate`, `exists_time_near_section`.
* **Transfer**: `orbit_stable_of_poincareMap`, `orbit_attracts_of_poincareMap`,
  `orbit_unstable_of_poincareMap`, and the packaged form `orbit_of_poincareMap`.
* **Decision through the reductions**: `orbit_stable_of_flipCoeff_pos`,
  `orbit_unstable_of_flipCoeff_neg` (a nontrivial multiplier `−1`);
  `orbit_unstable_of_foldCoeff_ne_zero`, `orbit_stable_of_cubicCoeff_neg`,
  `orbit_unstable_of_cubicCoeff_pos` (a nontrivial multiplier `+1`).

Corrections.
None: an extension (the critical case of the Andronov–Witt theorem, which
`theorem/Periodic/AndronovWitt.lean` left open).

Family and connection conclusions.
None: static evidence on autonomous ODEs (orbital stability of a periodic orbit).
-/

noncomputable section
namespace powerlib.Periodic.AndronovWittCritical

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative FlipOrbit PoincareSection

variable {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Map notions read in the coordinates `Fin n → ℝ` -/

/-- Lyapunov stability of `euclidMap F` at `p`, in the sup norm of `Fin n → ℝ`. -/
@[tmio T, powerlib_foundation] private theorem coord_lyapunovStable
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ}
    (h : Map.LyapunovStable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p)) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ, ‖ξ - p‖ < δ → ∀ k : ℕ, ‖F^[k] ξ - p‖ < ε := by
  set E := EuclideanSpace.equiv (Fin n) ℝ with hE
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (E : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (E.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ε / (‖εL‖ + 1)) (by positivity)
  refine ⟨δ / (‖εS‖ + 1), by positivity, fun ξ hξ k => ?_⟩
  have hξE : ‖E.symm ξ - E.symm p‖ < δ := by
    rw [← map_sub]
    calc ‖E.symm (ξ - p)‖ ≤ ‖εS‖ * ‖ξ - p‖ := εS.le_opNorm _
      _ ≤ (‖εS‖ + 1) * ‖ξ - p‖ := by nlinarith [norm_nonneg (ξ - p)]
      _ < δ := by rwa [lt_div_iff₀' (by positivity)] at hξ
  have hk := hb _ hξE k
  rw [iterate_euclidMap, ContinuousLinearEquiv.apply_symm_apply, ← map_sub] at hk
  calc ‖F^[k] ξ - p‖ = ‖E (E.symm (F^[k] ξ - p))‖ := by
        rw [ContinuousLinearEquiv.apply_symm_apply]
    _ ≤ ‖εL‖ * ‖E.symm (F^[k] ξ - p)‖ := εL.le_opNorm _
    _ ≤ ‖εL‖ * (ε / (‖εL‖ + 1)) := mul_le_mul_of_nonneg_left hk.le (norm_nonneg _)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg εL]

/-- Attraction of `euclidMap F` to `p`, in the coordinates `Fin n → ℝ`. -/
@[tmio T, powerlib_foundation] private theorem coord_tendsto
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ}
    (h : Map.LocalAsymptoticStable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p)) :
    ∃ c > 0, ∀ ξ, ‖ξ - p‖ < c → Tendsto (fun k : ℕ => F^[k] ξ) atTop (𝓝 p) := by
  set E := EuclideanSpace.equiv (Fin n) ℝ with hE
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (E.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  obtain ⟨-, c, hc, hatt⟩ := h
  refine ⟨c / (‖εS‖ + 1), by positivity, fun ξ hξ => ?_⟩
  have hξE : ‖E.symm ξ - E.symm p‖ < c := by
    rw [← map_sub]
    calc ‖E.symm (ξ - p)‖ ≤ ‖εS‖ * ‖ξ - p‖ := εS.le_opNorm _
      _ ≤ (‖εS‖ + 1) * ‖ξ - p‖ := by nlinarith [norm_nonneg (ξ - p)]
      _ < c := by rwa [lt_div_iff₀' (by positivity)] at hξ
  have h1 := (E.continuous.tendsto (E.symm p)).comp (hatt _ hξE)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h1
  refine h1.congr fun k => ?_
  simp only [Function.comp_apply, iterate_euclidMap]
  show E (E.symm (F^[k] (E (E.symm ξ)))) = F^[k] ξ
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- Instability of `euclidMap F` at `p`, in the coordinates `Fin n → ℝ`: orbits starting
arbitrarily close to `p` reach the distance `ε`. -/
@[tmio T, powerlib_foundation] private theorem coord_unstable
    {F : (Fin n → ℝ) → Fin n → ℝ} {p : Fin n → ℝ}
    (h : Map.Unstable (euclidMap F) ((EuclideanSpace.equiv (Fin n) ℝ).symm p)) :
    ∃ ε > 0, ∀ δ > 0, ∃ ξ, ‖ξ - p‖ < δ ∧ ∃ k : ℕ, ε ≤ ‖F^[k] ξ - p‖ := by
  set E := EuclideanSpace.equiv (Fin n) ℝ with hE
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (E : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (E.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  unfold Map.Unstable Map.LyapunovStable at h
  push Not at h
  obtain ⟨ε₀, hε₀, hesc⟩ := h
  refine ⟨ε₀ / (‖εS‖ + 1), by positivity, fun δ hδ => ?_⟩
  obtain ⟨y, hy, k, hk⟩ := hesc (δ / (‖εL‖ + 1)) (by positivity)
  refine ⟨E y, ?_, k, ?_⟩
  · have e : E y - p = E (y - E.symm p) := by
      rw [map_sub, ContinuousLinearEquiv.apply_symm_apply]
    rw [e]
    calc ‖E (y - E.symm p)‖ ≤ ‖εL‖ * ‖y - E.symm p‖ := εL.le_opNorm _
      _ ≤ (‖εL‖ + 1) * ‖y - E.symm p‖ := by nlinarith [norm_nonneg (y - E.symm p)]
      _ < δ := by rwa [lt_div_iff₀' (by positivity)] at hy
  · rw [iterate_euclidMap] at hk
    have e : E.symm (F^[k] (E y)) - E.symm p = E.symm (F^[k] (E y) - p) := by rw [map_sub]
    rw [e] at hk
    have h2 : ε₀ ≤ (‖εS‖ + 1) * ‖F^[k] (E y) - p‖ :=
      hk.trans ((εS.le_opNorm _).trans (by nlinarith [norm_nonneg (F^[k] (E y) - p)]))
    rwa [div_le_iff₀' (by positivity)]

/-! ## The solution between the section crossings -/

/-- **The orbit of the Poincaré map controls the distance to the orbit.** Let `τ` be a return
time with `|τ(ξ) − T| < s ≤ T/2` on the ball `‖ξ − x_*(0)‖ < r`, and let the iterates
`Πᵏ(y(0))` of a solution `y` on `[0, ∞)` stay in that ball. Then at every time `t ≥ 0` there is
`k` with `t ≤ (k + 1) 3T/2` and `dist(y(t), x_*(ℝ)) ≤ e^{3KT/2} ‖Πᵏ(y(0)) − x_*(0)‖`
(Grönwall between the crossings `t_k ≤ t < t_{k+1}`). -/
@[tmio T, powerlib_foundation] theorem infDist_le_iterate (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r → |τ ξ - T| < s) {y : ℝ → Fin n → ℝ}
    (hy : IsIntegralCurveOn y (fun _ => f) (Ici 0))
    (hbox : ∀ k : ℕ, ‖(poincareMap hfK τ)^[k] (y 0) - xs 0‖ < r) :
    ∀ t, 0 ≤ t → ∃ k : ℕ, t ≤ (k + 1) * (3 * T / 2) ∧ Metric.infDist (y t) (range xs) ≤
      Real.exp (K * (3 * T / 2)) * ‖(poincareMap hfK τ)^[k] (y 0) - xs 0‖ := by
  intro t ht
  set P := poincareMap hfK τ with hP
  set ξ := y 0 with hξ
  have hτs : ∀ k : ℕ, |τ (P^[k] ξ) - T| < s := fun k => hsec _ (hbox k)
  have hτpos : ∀ k : ℕ, T / 2 ≤ τ (P^[k] ξ) := fun k => by
    have := abs_lt.1 (hτs k); linarith
  have hτup : ∀ k : ℕ, τ (P^[k] ξ) ≤ 3 * T / 2 := fun k => by
    have := abs_lt.1 (hτs k); linarith
  set tt : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, τ (P^[j] ξ) with htt
  have htt_iter : ∀ k : ℕ, P^[k] ξ = y (tt k) := fun k =>
    AndronovWitt.iterate_poincareMap hfK τ hy k fun j _ => le_trans (by linarith) (hτpos j)
  have htt_succ : ∀ k : ℕ, tt (k + 1) = tt k + τ (P^[k] ξ) := fun k =>
    Finset.sum_range_succ _ _
  have htt_ge : ∀ k : ℕ, (k : ℝ) * (T / 2) ≤ tt k := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτpos k]
  have htt_le : ∀ k : ℕ, tt k ≤ k * (3 * T / 2) := fun k => by
    induction k with
    | zero => simp [htt]
    | succ k ih => rw [htt_succ]; push_cast; linarith [hτup k]
  have hex : ∃ k : ℕ, t < tt (k + 1) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (t / (T / 2))
    refine ⟨k, lt_of_lt_of_le ?_ (htt_ge (k + 1))⟩
    rw [div_lt_iff₀ (by positivity)] at hk
    push_cast; nlinarith
  classical
  set k := Nat.find hex with hk
  have hk1 : t < tt (k + 1) := Nat.find_spec hex
  have hk0 : tt k ≤ t := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simpa [htt] using ht
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel hpos] at this
      exact not_lt.1 this
  refine ⟨k, ?_, ?_⟩
  · have := htt_le (k + 1); push_cast at this; linarith
  have htk0 : 0 ≤ tt k := le_trans (by positivity) (htt_ge k)
  have hyI : IsIntegralCurveOn y (fun _ => f) (Icc (tt k) t) :=
    hy.mono fun q hq => mem_Ici.2 (htk0.trans hq.1)
  have hxs' : IsIntegralCurveOn (fun r => xs (r - tt k)) (fun _ => f) (Icc (tt k) t) :=
    fun r _ => ((hxs (r - tt k)).comp_sub_const r (tt k)).hasDerivWithinAt
  have hgr := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK) hyI hxs' t ⟨hk0, le_rfl⟩
  rw [sub_self, ← htt_iter, dist_eq_norm] at hgr
  have hgap : t - tt k ≤ 3 * T / 2 := by have := htt_succ k; linarith [hτup k]
  calc Metric.infDist (y t) (range xs) ≤ dist (y t) (xs (t - tt k)) :=
        Metric.infDist_le_dist_of_mem (mem_range_self _)
    _ ≤ ‖P^[k] ξ - xs 0‖ * Real.exp (K * (t - tt k)) := hgr
    _ ≤ ‖P^[k] ξ - xs 0‖ * Real.exp (K * (3 * T / 2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hgap K.2))
          (norm_nonneg _)
    _ = Real.exp (K * (3 * T / 2)) * ‖P^[k] ξ - xs 0‖ := mul_comm _ _

/-- **From near the orbit to the section.** A solution `x` on `[0, ∞)` starting near a point
`x_*(σ)` of a `T`-periodic orbit reaches, at a time `u ∈ (0, T]`, the distance
`≤ e^{KT} ‖x(0) − x_*(σ)‖` from `x_*(0)`, and stays within that distance of the orbit on `[0, u]`
(`u = T − (σ mod T)`). -/
@[tmio T, powerlib_foundation] theorem exists_time_near_section (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x (fun _ => f) (Ici 0))
    (σ : ℝ) : ∃ u, 0 < u ∧ u ≤ T ∧ ‖x u - xs 0‖ ≤ Real.exp (K * T) * ‖x 0 - xs σ‖ ∧
      ∀ t ∈ Icc 0 u, Metric.infDist (x t) (range xs) ≤ Real.exp (K * T) * ‖x 0 - xs σ‖ := by
  set σ' := toIcoMod hT 0 σ with hσ'
  have hσ'I : σ' ∈ Ico 0 T := by simpa using toIcoMod_mem_Ico hT 0 σ
  have hσσ' : xs σ = xs σ' := by
    have h := toIcoMod_add_toIcoDiv_zsmul hT 0 σ
    rw [← h]
    exact (hper.zsmul _) _
  set u := T - σ' with hu
  have hu0 : 0 < u := by have := hσ'I.2; linarith
  have huT : u ≤ T := by have := hσ'I.1; linarith
  have hxs' : IsIntegralCurveOn (fun r => xs (r + σ')) (fun _ => f) (Icc 0 u) :=
    fun r _ => ((hxs (r + σ')).comp_add_const r σ').hasDerivWithinAt
  have hfollow : ∀ t ∈ Icc 0 u, ‖x t - xs (t + σ')‖ ≤ Real.exp (K * T) * ‖x 0 - xs σ‖ :=
    fun t ht => by
      have h := dist_le_of_isIntegralCurveOn_Icc (fun _ => hfK)
        (hx.mono fun q hq => mem_Ici.2 hq.1) hxs' t ht
      rw [dist_eq_norm, dist_eq_norm, zero_add, ← hσσ'] at h
      rw [mul_comm]
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left (by linarith [ht.2, ht.1]) K.2
  refine ⟨u, hu0, huT, ?_, fun t ht => ?_⟩
  · have h := hfollow u ⟨hu0.le, le_rfl⟩
    rwa [hu, sub_add_cancel, show xs T = xs 0 by simpa using hper 0] at h
  · exact (Metric.infDist_le_dist_of_mem (mem_range_self _)).trans
      ((dist_eq_norm _ _).trans_le (hfollow t ht))


/-! ## Transfer of the verdict of the Poincaré map to the orbit -/

/-- **A Lyapunov stable Poincaré map gives an orbitally stable orbit.** Let `x_*` be a
`T`-periodic solution of `ẋ = f(x)` (`f` globally `K`-Lipschitz) and `τ` a return time with
`|τ(ξ) − T| < s ≤ T/2` on the ball `‖ξ − x_*(0)‖ < r`. If the Poincaré map
`Π(ξ) = x(τ(ξ); ξ)`, read on `ℝⁿ`, is Lyapunov stable at `x_*(0)`, the orbit is orbitally
stable: for every `ε > 0` there is `δ > 0` such that every solution on `[0, ∞)` starting within
`δ` of the orbit stays within `ε` of it. No rate and no asymptotic phase are claimed. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_poincareMap (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r) (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r → |τ ξ - T| < s)
    (hLS : Map.LyapunovStable (euclidMap (poincareMap hfK τ))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      Metric.infDist (x 0) (range xs) < δ → ∀ t, 0 ≤ t →
        Metric.infDist (x t) (range xs) < ε := by
  set P := poincareMap hfK τ with hP
  set E := Real.exp (K * (3 * T / 2)) with hE
  set E₁ := Real.exp (K * T) with hE₁
  have hE0 : 0 < E := Real.exp_pos _
  have hE₁0 : 0 < E₁ := Real.exp_pos _
  intro ε hε
  set ε₁ := min r (ε / (2 * E)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hr (by positivity)
  obtain ⟨δ₁, hδ₁, hb⟩ := coord_lyapunovStable hLS ε₁ hε₁0
  refine ⟨min δ₁ (ε / 2) / E₁, by positivity, fun x hx hx0 t ht => ?_⟩
  obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff (range_nonempty xs)).1 hx0
  rw [dist_eq_norm] at hσ
  have hd : E₁ * ‖x 0 - xs σ‖ < min δ₁ (ε / 2) := by rwa [lt_div_iff₀' hE₁0] at hσ
  obtain ⟨u, hu0, -, hxu, hbefore⟩ := exists_time_near_section hfK hxs hT hper hx σ
  rcases le_or_gt t u with htu | hut
  · exact (hbefore t ⟨ht, htu⟩).trans_lt
      ((hd.trans_le (min_le_right _ _)).trans (half_lt_self hε))
  set y : ℝ → Fin n → ℝ := fun r => x (r + u) with hy
  have hyI : IsIntegralCurveOn y (fun _ => f) (Ici 0) :=
    (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
      (Ici_subset_Ici.2 (by linarith))
  have hy0 : ‖y 0 - xs 0‖ < δ₁ := by
    simp only [hy, zero_add]; exact hxu.trans_lt (hd.trans_le (min_le_left _ _))
  have hbox : ∀ k : ℕ, ‖P^[k] (y 0) - xs 0‖ < r := fun k =>
    (hb _ hy0 k).trans_le (min_le_left _ _)
  obtain ⟨k, -, hk⟩ := infDist_le_iterate hfK hxs hT hsT (fun ξ hξ => hsec ξ hξ) hyI hbox
    (t - u) (by linarith)
  have hyt : y (t - u) = x t := by simp [hy]
  rw [hyt] at hk
  calc Metric.infDist (x t) (range xs) ≤ E * ‖P^[k] (y 0) - xs 0‖ := hk
    _ < E * ε₁ := mul_lt_mul_of_pos_left (hb _ hy0 k) hE0
    _ ≤ E * (ε / (2 * E)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hE0.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- **A locally asymptotically stable Poincaré map gives an orbitally asymptotically stable
orbit.** Under the hypotheses of `orbit_stable_of_poincareMap`, if the Poincaré map is locally
asymptotically stable at `x_*(0)`, the orbit attracts: there is `c > 0` such that every solution
on `[0, ∞)` starting within `c` of the orbit satisfies `dist(x(t), x_*(ℝ)) → 0` (and the orbit is
orbitally stable, `orbit_stable_of_poincareMap`). No rate and no asymptotic phase are claimed. -/
@[tmio T, powerlib_foundation] theorem orbit_attracts_of_poincareMap (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r) (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r → |τ ξ - T| < s)
    (hLAS : Map.LocalAsymptoticStable (euclidMap (poincareMap hfK τ))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    ∃ c > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      Metric.infDist (x 0) (range xs) < c →
        Tendsto (fun t => Metric.infDist (x t) (range xs)) atTop (𝓝 0) := by
  set P := poincareMap hfK τ with hP
  set E := Real.exp (K * (3 * T / 2)) with hE
  set E₁ := Real.exp (K * T) with hE₁
  have hE0 : 0 < E := Real.exp_pos _
  have hE₁0 : 0 < E₁ := Real.exp_pos _
  obtain ⟨c₀, hc₀, hatt⟩ := coord_tendsto hLAS
  obtain ⟨δ₁, hδ₁, hb⟩ := coord_lyapunovStable hLAS.1 r hr
  refine ⟨min δ₁ c₀ / E₁, by positivity, fun x hx hx0 => ?_⟩
  obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff (range_nonempty xs)).1 hx0
  rw [dist_eq_norm] at hσ
  have hd : E₁ * ‖x 0 - xs σ‖ < min δ₁ c₀ := by rwa [lt_div_iff₀' hE₁0] at hσ
  obtain ⟨u, hu0, -, hxu, -⟩ := exists_time_near_section hfK hxs hT hper hx σ
  set y : ℝ → Fin n → ℝ := fun r => x (r + u) with hy
  have hyI : IsIntegralCurveOn y (fun _ => f) (Ici 0) :=
    (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
      (Ici_subset_Ici.2 (by linarith))
  have hy0 : ‖y 0 - xs 0‖ < min δ₁ c₀ := by
    simp only [hy, zero_add]; exact hxu.trans_lt hd
  have hbox : ∀ k : ℕ, ‖P^[k] (y 0) - xs 0‖ < r := fun k =>
    hb _ (hy0.trans_le (min_le_left _ _)) k
  have hconv := hatt _ (hy0.trans_le (min_le_right _ _))
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 hconv (η / E) (by positivity)
  refine ⟨u + (K₀ + 1) * (3 * T / 2), fun t ht => ?_⟩
  have htu : 0 ≤ t - u := by nlinarith
  obtain ⟨k, hkt, hk⟩ := infDist_le_iterate hfK hxs hT hsT (fun ξ hξ => hsec ξ hξ) hyI hbox
    (t - u) htu
  have hyt : y (t - u) = x t := by simp [hy]
  rw [hyt] at hk
  have hkK : K₀ ≤ k := by
    have h1 : ((K₀ : ℝ) + 1) * (3 * T / 2) ≤ ((k : ℝ) + 1) * (3 * T / 2) := by linarith
    have h2 : (K₀ : ℝ) + 1 ≤ k + 1 := le_of_mul_le_mul_right h1 (by positivity)
    exact_mod_cast (by linarith : (K₀ : ℝ) ≤ k)
  have h3 := hK₀ k hkK
  rw [dist_eq_norm] at h3
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  calc Metric.infDist (x t) (range xs) ≤ E * ‖P^[k] (y 0) - xs 0‖ := hk
    _ < E * (η / E) := mul_lt_mul_of_pos_left h3 hE0
    _ = η := by field_simp

/-- **An unstable Poincaré map gives an orbitally unstable orbit.** Let `x_*` be a nonconstant
`T`-periodic solution of `ẋ = f(x)` (`f` globally `K`-Lipschitz) and `τ` a return time with
`|τ(ξ) − T| < s ≤ T/2` and `Π(ξ)` on the section `f(p) ⬝ (ξ − p) = 0` for `‖ξ − p‖ < r`,
`p = x_*(0)`, `Π(p) = p`, `Π` differentiable at `p`. If `Π`, read on `ℝⁿ`, is unstable at `p`,
the orbit is orbitally unstable: there is `ε > 0` such that solutions starting arbitrarily close
to `p` reach the distance `ε` from the whole orbit (the argument of
`AndronovWitt.orbit_unstable`, from any unstable `Π` instead of a multiplier `|μ| > 1`). -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_poincareMap (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r)
    (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r →
      |τ ξ - T| < s ∧ f (xs 0) ⬝ᵥ (poincareMap hfK τ ξ - xs 0) = 0)
    (hPp : poincareMap hfK τ (xs 0) = xs 0) {D : (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    (hPD : HasFDerivAt (poincareMap hfK τ) D (xs 0))
    (hun : Map.Unstable (euclidMap (poincareMap hfK τ))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range xs) := by
  set P := poincareMap hfK τ with hP
  set p := xs 0 with hp
  set v := f (xs 0) with hv
  obtain ⟨ε₀, hε₀, hesc⟩ := coord_unstable hun
  -- the Poincaré map is Lipschitz at `p`
  obtain ⟨L₀, hL₀⟩ := hPD.isBigO_sub.bound
  obtain ⟨r₃, hr₃, hPL₀⟩ := Metric.eventually_nhds_iff.1 hL₀
  set L := max L₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hPL : ∀ ξ, ‖ξ - p‖ < r₃ → ‖P ξ - p‖ ≤ L * ‖ξ - p‖ := fun ξ hξ => by
    have h := hPL₀ (show dist ξ p < r₃ by rwa [dist_eq_norm])
    rw [hPp] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨ρS, hρS, hSig⟩ := AndronovWitt.orbit_section_eq hfK hxs hT hper hne
  -- the radii
  set ε₂ := min (min ε₀ r) (min r₃ (ρS / (L + 2))) with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  have hε₂1 : ε₂ ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂r : ε₂ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
  have hε₂r₃ : ε₂ ≤ r₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₂ρ : ε₂ ≤ ρS / (L + 2) := (min_le_right _ _).trans (min_le_right _ _)
  -- the escape set on the section, at a positive distance from the orbit
  set S := {z : Fin n → ℝ | v ⬝ᵥ (z - p) = 0 ∧ ε₂ ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ (L + 1) * ε₂} with hS
  have hScl : IsClosed S := by
    have hc1 : Continuous fun z : Fin n → ℝ => v ⬝ᵥ (z - p) :=
      (dotCLM v).continuous.comp (continuous_id.sub continuous_const)
    have hc2 : Continuous fun z : Fin n → ℝ => ‖z - p‖ :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    exact (isClosed_eq hc1 continuous_const).inter
      ((isClosed_le continuous_const hc2).inter (isClosed_le hc2 continuous_const))
  have hSb : Bornology.IsBounded S :=
    (Metric.isBounded_closedBall (x := p) (r := (L + 1) * ε₂)).subset fun z hz => by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz.2.2
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  have hOcl : IsClosed (range xs) := by
    have hxc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
    have e : range xs = xs '' Icc 0 T := by
      ext z
      constructor
      · rintro ⟨σ, rfl⟩
        obtain ⟨y, hy, hσy⟩ := hper.exists_mem_Ico₀ hT σ
        exact ⟨y, Ico_subset_Icc_self hy, hσy.symm⟩
      · rintro ⟨σ, -, rfl⟩; exact mem_range_self σ
    rw [e]
    exact (isCompact_Icc.image hxc).isClosed
  have hSpos : ∀ z ∈ S, 0 < Metric.infDist z (range xs) := fun z hz => by
    refine (hOcl.notMem_iff_infDist_pos (range_nonempty xs)).1 ?_
    rintro ⟨σ, hσ⟩
    rw [← hσ] at hz
    have hlt : ‖xs σ - p‖ < ρS := by
      calc ‖xs σ - p‖ ≤ (L + 1) * ε₂ := hz.2.2
        _ < (L + 2) * ε₂ := by nlinarith
        _ ≤ (L + 2) * (ρS / (L + 2)) := mul_le_mul_of_nonneg_left hε₂ρ (by positivity)
        _ = ρS := by field_simp
    have h0 := hSig σ hz.1 hlt
    have := hz.2.1
    rw [h0, sub_self, norm_zero] at this
    linarith
  obtain ⟨εf, hεf, hεfS⟩ : ∃ εf > 0, ∀ z ∈ S, εf ≤ Metric.infDist z (range xs) := by
    by_cases hSne : S.Nonempty
    · obtain ⟨zm, hzm, hmin⟩ := hScpt.exists_isMinOn hSne
        (Metric.continuous_infDist_pt (range xs)).continuousOn
      exact ⟨_, hSpos zm hzm, fun z hz => hmin hz⟩
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hSne⟩
  refine ⟨εf, hεf, fun δ hδ => ?_⟩
  -- an escaping orbit of the Poincaré map
  obtain ⟨ξ, hξp, k, hk⟩ := hesc (min δ ε₂) (lt_min hδ hε₂0)
  have hkξ : ε₂ ≤ ‖P^[k] ξ - p‖ := hε₂1.trans hk
  classical
  have hex : ∃ k, ε₂ ≤ ‖P^[k] ξ - p‖ := ⟨k, hkξ⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀spec : ε₂ ≤ ‖P^[k₀] ξ - p‖ := Nat.find_spec hex
  have hk₀min : ∀ j < k₀, ‖P^[j] ξ - p‖ < ε₂ := fun j hj => not_le.1 (Nat.find_min hex hj)
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | h0
    · exfalso
      have := hk₀spec
      rw [h0, Function.iterate_zero, id] at this
      linarith [hξp.trans_le (min_le_right δ ε₂)]
    · exact h0
  -- the solution from `ξ` and its crossing at the escape
  set x := flow (G := fun _ => f) (hfK.continuous.comp continuous_snd) (fun _ => hfK) 0 ξ with hx
  have hxI : IsIntegralCurveOn x (fun _ => f) (Ici 0) := flow_solution _ _ 0 ξ
  have hx0 : x 0 = ξ := flow_start _ _ 0 ξ
  have hτnn : ∀ j < k₀, 0 ≤ τ (P^[j] (x 0)) := fun j hj => by
    rw [hx0]
    have h := (hsec _ ((hk₀min j hj).trans_le hε₂r)).1
    have := abs_lt.1 h
    linarith
  have hiter := AndronovWitt.iterate_poincareMap hfK τ hxI k₀ hτnn
  refine ⟨x, hxI, by rw [hx0]; exact hξp.trans_le (min_le_left _ _), _,
    Finset.sum_nonneg fun j hj => hτnn j (Finset.mem_range.1 hj), ?_⟩
  rw [← hiter, hx0]
  apply hεfS
  -- the escaping point lies in `S`
  set w := P^[k₀ - 1] ξ with hw
  have hwk : P^[k₀] ξ = P w := by
    rw [hw, ← Function.iterate_succ_apply' P, Nat.succ_eq_add_one, Nat.sub_add_cancel hk₀pos]
  have hwp : ‖w - p‖ < ε₂ := hk₀min (k₀ - 1) (by omega)
  refine ⟨?_, hk₀spec, ?_⟩
  · rw [hwk]; exact (hsec w (hwp.trans_le hε₂r)).2
  · rw [hwk]
    calc ‖P w - p‖ ≤ L * ‖w - p‖ := hPL w (hwp.trans_le hε₂r₃)
      _ ≤ L * ε₂ := mul_le_mul_of_nonneg_left hwp.le hL0
      _ ≤ (L + 1) * ε₂ := by nlinarith


/-- **The Poincaré map decides the orbit.** For a nonconstant `T`-periodic orbit of `ẋ = f(x)`
(`f` of class `C¹`, globally Lipschitz) there is a return time `τ`, `τ(x_*(0)) = T`, whose
Poincaré map fixes `p = x_*(0)` with strict derivative `sectionMatrix M f(p)`, and whose verdict
in the map semantics transfers to the orbit: Lyapunov stable ⇒ orbitally stable, locally
asymptotically stable ⇒ orbitally attracting, unstable ⇒ orbitally unstable (without rate and
without asymptotic phase; `orbit_stable_of_poincareMap`, `orbit_attracts_of_poincareMap`,
`orbit_unstable_of_poincareMap`). This holds whatever the multipliers on the unit circle. -/
@[tmio T, powerlib_foundation] theorem orbit_of_poincareMap (hf : ContDiff ℝ 1 f)
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) :
    ∃ τ : (Fin n → ℝ) → ℝ, τ (xs 0) = T ∧ poincareMap hfK τ (xs 0) = xs 0 ∧
      HasStrictFDerivAt (poincareMap hfK τ)
        (Matrix.toLin' (sectionMatrix (monodromy (variationalMatrix f xs) T 0)
          (f (xs 0)))).toContinuousLinearMap (xs 0) ∧
      (Map.LyapunovStable (euclidMap (poincareMap hfK τ))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) →
        ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
          Metric.infDist (x 0) (range xs) < δ → ∀ t, 0 ≤ t →
            Metric.infDist (x t) (range xs) < ε) ∧
      (Map.LocalAsymptoticStable (euclidMap (poincareMap hfK τ))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) →
        ∃ c > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
          Metric.infDist (x 0) (range xs) < c →
            Tendsto (fun t => Metric.infDist (x t) (range xs)) atTop (𝓝 0)) ∧
      (Map.Unstable (euclidMap (poincareMap hfK τ))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) →
        ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) ∧
          ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range xs)) := by
  obtain ⟨τ, hτp, -, ⟨r, s, hr, hs, hsT, hsec, -⟩, hPp, hPD, -, -, -, -⟩ :=
    exists_poincareMap hf hfK hxs hT hper hne
  exact ⟨τ, hτp, hPp, hPD,
    fun h => orbit_stable_of_poincareMap hfK hxs hT hper hr hsT (fun ξ hξ => (hsec ξ hξ).1) h,
    fun h => orbit_attracts_of_poincareMap hfK hxs hT hper hr hsT (fun ξ hξ => (hsec ξ hξ).1) h,
    fun h => orbit_unstable_of_poincareMap hfK hxs hT hper hne hr hsT hsec hPp hPD.hasFDerivAt h⟩

/-! ## The critical cases decided through the reductions of the Poincaré map -/

/-- **A nontrivial multiplier `−1`: the flip coefficient of the Poincaré map decides, stable
side.** Let `τ` be a return time as in `orbit_unstable_of_poincareMap` (for instance the one of
`PoincareSection.exists_poincareMap`, with `Mm = sectionMatrix M f(p)`), and let the Poincaré
map `Π` have at `p = x_*(0)` the strict derivative `Mm` with a simple eigenvalue `−1` and the rest
of its spectrum strictly inside the unit circle, in projector form (`Mm vm = −vm`,
`wmᵀ Mm = −wmᵀ`, `wm ⬝ vm = 1`, `Mm + vm wmᵀ` Schur stable; the eigenvalue `0` of `Mm` on `f(p)`
is part of the stable rest), and the cubic expansion
`‖Π(p + e) − p − Mm e − P₂(e, e) − P₃(e, e, e)‖ ≤ C ‖e‖⁴` on `‖e‖ ≤ ρ₀` — a **hypothesis** here
(the Taylor expansion of `Π` is not derived from that of the flow). If the flip coefficient
`a² + b`, `a = wm ⬝ P₂(vm, vm)`, `b = wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))`,
`k − Mm k = P₂(vm, vm) − a vm`, is positive, the orbit is orbitally stable and attracting. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_flipCoeff_pos (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r) (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r → |τ ξ - T| < s)
    (hPp : poincareMap hfK τ (xs 0) = xs 0) {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hPD : HasStrictFDerivAt (poincareMap hfK τ) (Matrix.toLin' Mm).toContinuousLinearMap (xs 0))
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖poincareMap hfK τ (xs 0 + e) - xs 0 - Mm *ᵥ e - P₂ e e -
      P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    {k : Fin n → ℝ} (hk : k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hab : 0 < (wm ⬝ᵥ P₂ vm vm) ^ 2 + (wm ⬝ᵥ P₃ (fun _ => vm) + wm ⬝ᵥ (P₂ vm k + P₂ k vm))) :
    (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      Metric.infDist (x 0) (range xs) < δ → ∀ t, 0 ≤ t →
        Metric.infDist (x t) (range xs) < ε) ∧
    ∃ c > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      Metric.infDist (x 0) (range xs) < c →
        Tendsto (fun t => Metric.infDist (x t) (range xs)) atTop (𝓝 0) := by
  have hmap := (localAsymptoticStable_of_flipCoeff_pos_coord hPD hPp hv hw hwv hS hC hρ₀ hTay
    hk hab).1
  exact ⟨orbit_stable_of_poincareMap hfK hxs hT hper hr hsT hsec hmap.1,
    orbit_attracts_of_poincareMap hfK hxs hT hper hr hsT hsec hmap⟩

/-- **A nontrivial multiplier `−1`: the flip coefficient decides, unstable side.** Under the
hypotheses of `orbit_stable_of_flipCoeff_pos` (with the section property of `Π` and `f(p) ≠ 0`
as in `orbit_unstable_of_poincareMap`), a negative flip coefficient `a² + b` makes the orbit
orbitally unstable. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_flipCoeff_neg (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r)
    (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r →
      |τ ξ - T| < s ∧ f (xs 0) ⬝ᵥ (poincareMap hfK τ ξ - xs 0) = 0)
    (hPp : poincareMap hfK τ (xs 0) = xs 0) {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hPD : HasStrictFDerivAt (poincareMap hfK τ) (Matrix.toLin' Mm).toContinuousLinearMap (xs 0))
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖poincareMap hfK τ (xs 0 + e) - xs 0 - Mm *ᵥ e - P₂ e e -
      P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    {k : Fin n → ℝ} (hk : k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (hab : (wm ⬝ᵥ P₂ vm vm) ^ 2 + (wm ⬝ᵥ P₃ (fun _ => vm) + wm ⬝ᵥ (P₂ vm k + P₂ k vm)) < 0) :
    ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range xs) :=
  orbit_unstable_of_poincareMap hfK hxs hT hper hne hr hsT hsec hPp hPD.hasFDerivAt
    (unstable_of_flipCoeff_neg_coord hPD hPp hv hw hwv hS hC hρ₀ hTay hk hab)

/-- **A nontrivial multiplier `+1`: the fold coefficient decides, fold type.** Let the Poincaré
map `Π` (a return time `τ` as in `orbit_unstable_of_poincareMap`) have at `p = x_*(0)` the strict
derivative `Mm` with a simple eigenvalue `+1` (the trivial multiplier `1` is then double for the
monodromy, `PoincareSection.one_mem_spectrum_deflate_iff`) and the rest of its spectrum strictly
inside the unit circle, in projector form (`Mm vm = vm`, `wmᵀ Mm = wmᵀ`, `wm ⬝ vm = 1`,
`Mm − vm wmᵀ` Schur stable), and the cubic expansion of `Π` with remainder `C ‖e‖⁴` (a
**hypothesis**). If the fold coefficient `a = wm ⬝ P₂(vm, vm)` is not zero, the orbit is
orbitally unstable. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_foldCoeff_ne_zero
    (hfK : LipschitzWith K f) {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {τ : (Fin n → ℝ) → ℝ}
    {r s : ℝ} (hr : 0 < r) (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r →
      |τ ξ - T| < s ∧ f (xs 0) ⬝ᵥ (poincareMap hfK τ ξ - xs 0) = 0)
    (hPp : poincareMap hfK τ (xs 0) = xs 0) {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hPD : HasStrictFDerivAt (poincareMap hfK τ) (Matrix.toLin' Mm).toContinuousLinearMap (xs 0))
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = vm) (hw : wm ᵥ* Mm = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm - vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖poincareMap hfK τ (xs 0 + e) - xs 0 - Mm *ᵥ e - P₂ e e -
      P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    (ha : wm ⬝ᵥ P₂ vm vm ≠ 0) :
    ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range xs) := by
  obtain ⟨vE, wE, P₂E, P₃E, ρ', C', hρ', hP', hPp', hv', hw', hwv', hL, hTay', ha', -⟩ :=
    FoldOrbit.coords_at (μ := 1) hPD hPp (by rw [hv, one_smul]) (by rw [hw, one_smul]) hwv hC
      hρ₀ hTay
  rw [one_smul] at hv' hL
  exact orbit_unstable_of_poincareMap hfK hxs hT hper hne hr hsT hsec hPp hPD.hasFDerivAt
    (FoldReduction.unstable_of_foldCoeff_ne_zero_matrix hP' hPp' hv'
      (fun e => by rw [hw', one_mul]) hwv' hL hS hρ' hTay' (by rw [ha']; exact ha))

/-- **A nontrivial multiplier `+1`: the cubic coefficient decides, stable side.** Under the
hypotheses of `orbit_unstable_of_foldCoeff_ne_zero` with `a = 0` and a negative cubic
coefficient `b = wm ⬝ P₃(vm, vm, vm) + wm ⬝ (P₂(vm, k) + P₂(k, vm))`,
`k − Mm k = P₂(vm, vm) − a vm`, the orbit is orbitally stable and attracting. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_cubicCoeff_neg (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r) (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r → |τ ξ - T| < s)
    (hPp : poincareMap hfK τ (xs 0) = xs 0) {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hPD : HasStrictFDerivAt (poincareMap hfK τ) (Matrix.toLin' Mm).toContinuousLinearMap (xs 0))
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = vm) (hw : wm ᵥ* Mm = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm - vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖poincareMap hfK τ (xs 0 + e) - xs 0 - Mm *ᵥ e - P₂ e e -
      P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    {k : Fin n → ℝ} (hk : k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (ha : wm ⬝ᵥ P₂ vm vm = 0) (hb : wm ⬝ᵥ P₃ (fun _ => vm) + wm ⬝ᵥ (P₂ vm k + P₂ k vm) < 0) :
    (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      Metric.infDist (x 0) (range xs) < δ → ∀ t, 0 ≤ t →
        Metric.infDist (x t) (range xs) < ε) ∧
    ∃ c > 0, ∀ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) →
      Metric.infDist (x 0) (range xs) < c →
        Tendsto (fun t => Metric.infDist (x t) (range xs)) atTop (𝓝 0) := by
  obtain ⟨vE, wE, P₂E, P₃E, ρ', C', hρ', hP', hPp', hv', hw', hwv', hL, hTay', ha', hkb⟩ :=
    FoldOrbit.coords_at (μ := 1) hPD hPp (by rw [hv, one_smul]) (by rw [hw, one_smul]) hwv hC
      hρ₀ hTay
  rw [one_smul] at hv' hL
  obtain ⟨hk', hb'⟩ := hkb k
  have hmap := (FoldReduction.localAsymptoticStable_of_cubicCoeff_neg_matrix hP' hPp' hv'
    (fun e => by rw [hw', one_mul]) hwv' hL hS hρ' hTay' (hk' hk) (by rw [ha']; exact ha)
    (by rw [hb']; exact hb)).1
  exact ⟨orbit_stable_of_poincareMap hfK hxs hT hper hr hsT hsec hmap.1,
    orbit_attracts_of_poincareMap hfK hxs hT hper hr hsT hsec hmap⟩

/-- **A nontrivial multiplier `+1`: the cubic coefficient decides, unstable side.** Under the
hypotheses of `orbit_unstable_of_foldCoeff_ne_zero` with `a = 0` and a positive cubic
coefficient `b`, the orbit is orbitally unstable. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_of_cubicCoeff_pos (hfK : LipschitzWith K f)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (f (xs t)) t) {T : ℝ} (hT : 0 < T)
    (hper : Periodic xs T) (hne : f (xs 0) ≠ 0) {τ : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r)
    (hsT : s ≤ T / 2)
    (hsec : ∀ ξ, ‖ξ - xs 0‖ < r →
      |τ ξ - T| < s ∧ f (xs 0) ⬝ᵥ (poincareMap hfK τ ξ - xs 0) = 0)
    (hPp : poincareMap hfK τ (xs 0) = xs 0) {Mm : Matrix (Fin n) (Fin n) ℝ}
    (hPD : HasStrictFDerivAt (poincareMap hfK τ) (Matrix.toLin' Mm).toContinuousLinearMap (xs 0))
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = vm) (hw : wm ᵥ* Mm = wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm - vecMulVec vm wm))
    {P₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)} {C ρ₀ : ℝ}
    (hC : 0 ≤ C) (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖poincareMap hfK τ (xs 0 + e) - xs 0 - Mm *ᵥ e - P₂ e e -
      P₃ (fun _ => e)‖ ≤ C * ‖e‖ ^ 4)
    {k : Fin n → ℝ} (hk : k - Mm *ᵥ k = P₂ vm vm - (wm ⬝ᵥ P₂ vm vm) • vm)
    (ha : wm ⬝ᵥ P₂ vm vm = 0) (hb : 0 < wm ⬝ᵥ P₃ (fun _ => vm) + wm ⬝ᵥ (P₂ vm k + P₂ k vm)) :
    ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x (fun _ => f) (Ici 0) ∧
      ‖x 0 - xs 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range xs) := by
  obtain ⟨vE, wE, P₂E, P₃E, ρ', C', hρ', hP', hPp', hv', hw', hwv', hL, hTay', ha', hkb⟩ :=
    FoldOrbit.coords_at (μ := 1) hPD hPp (by rw [hv, one_smul]) (by rw [hw, one_smul]) hwv hC
      hρ₀ hTay
  rw [one_smul] at hv' hL
  obtain ⟨hk', hb'⟩ := hkb k
  exact orbit_unstable_of_poincareMap hfK hxs hT hper hne hr hsT hsec hPp hPD.hasFDerivAt
    (FoldReduction.unstable_of_cubicCoeff_pos_matrix hP' hPp' hv'
      (fun e => by rw [hw', one_mul]) hwv' hL hS hρ' hTay' (hk' hk) (by rw [ha']; exact ha)
      (by rw [hb']; exact hb))

end powerlib.Periodic.AndronovWittCritical
