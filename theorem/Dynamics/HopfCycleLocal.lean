import theorem.Dynamics.HopfCycle
import theorem.NormalForm.BiRidge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Hopf cycles of a family that is smooth only near the equilibrium

`Dynamics.HopfCycle.exists_hopfCycle` (`theorem/Dynamics/HopfCycle.lean`) reads a family whose
augmented field `(x, μ) ↦ (F(x, μ), 0)` is `C¹` on the whole space. Fields with a singular set
away from the equilibrium (a power balance `P/V` with `V ≠ 0` near the point) are `C¹` only on
an open neighbourhood `U` of `(0, 0)`. The cycle law below reduces them to the global one without
any bound on the cycle beyond its critical coordinates: the cut-off field `b · F` (`b` a smooth
bump, `b = 1` near `0`, `b > 0` exactly on a ball inside `U`) is globally `C¹` and has the same
Hopf data at the point; a nonconstant periodic orbit of `b · F` never meets the zeros of `b`
(they are equilibria, and solutions of a `C¹` field are unique), so it stays in `U`, and, `b` being
positive along it, it is the periodic orbit of `F` run with the clock `ds = b dt`.

Scope.
* Generic foundation, independent of any model; no family is defined. Autonomous fields on a
  normed space (time reparametrization), on `State n` (equilibria), and one-parameter families
  `ẋ = F(x, μ)` on `State n` with the hypotheses of `HopfCycle.exists_hopfCycle`, except that the
  augmented field is only `C¹` on an open set `U ∋ 0` (and analytic at `0`).
* Periodic orbits are written out in the statements, as in `theorem/Dynamics/HopfCycle.lean`;
  existence and the amplitude bound in the critical coordinates are proved; uniqueness, orbital
  stability and the period are not stated.

Source: Hassard–Kazarinoff–Wan, *Theory and Applications of Hopf Bifurcation* (1981), Ch. 1;
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4 (Theorem 3.3) and §2.1
(orbital equivalence: multiplying a field by a positive function only changes the clock);
Hartman, *Ordinary Differential Equations* (2nd ed.), Ch. II (uniqueness for Lipschitz fields).

Results.
* `ne_zero_of_periodic`: a nonconstant periodic solution of a `C¹` field never passes through an
  equilibrium.
* `exists_periodic_of_smul`: a periodic solution of `ẋ = β(x) F(x)` with `β > 0` along it is, with
  the clock `s(t) = ∫₀ᵗ β(x)`, a periodic solution of `ẏ = F(y)` with the same points.
* `HopfCycle.exists_hopfCycle_local`: the Hopf cycles of `HopfCycle.exists_hopfCycle` for a family
  whose augmented field is `C¹` only on `U`; the cycles stay in `U`.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology Metric

/-! ## Equilibria and periodic orbits -/

/-- A solution of a `C¹` field through an equilibrium stays there on every forward segment. -/
@[tmio T, powerlib_foundation] private theorem eqOn_of_equilibrium {n : ℕ} {g : State n → State n}
    (hg : ContDiff ℝ 1 g) {e : State n} (he : g e = 0) {x : ℝ → State n} {t₀ t₁ : ℝ}
    (hx : IsTrajectoryOn x g t₀ t₁) (h0 : x t₀ = e) : ∀ t ∈ Icc t₀ t₁, x t = e := by
  obtain ⟨K, s, hs, hK⟩ := (hg.contDiffAt (x := e)).exists_lipschitzOnWith
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.mp hs
  have hc : IsTrajectoryOn (fun _ => e) g t₀ t₁ := fun t _ => by
    show HasDerivWithinAt (fun _ => e) (g e) _ t
    rw [he]
    exact hasDerivWithinAt_const _ _ _
  have hball : ∀ t ∈ Icc t₀ t₁, ‖x t - e‖ < R := by
    refine forall_norm_sub_lt_of_bootstrap hx.continuousOn
      (by rw [h0, sub_self, norm_zero]; exact hR) fun s' hs' hin => ?_
    have heq := CenterManifold.eqOn_of_lipschitzOnWith (S := ball e R) (hK.mono hRs)
      (hx.mono (Icc_subset_Icc le_rfl hs'.2)) (hc.mono (Icc_subset_Icc le_rfl hs'.2))
      (fun t ht => by rw [mem_ball, dist_eq_norm]; exact hin t ht)
      (fun _ _ => mem_ball_self hR) h0 ⟨hs'.1, le_rfl⟩
    rw [heq, sub_self, norm_zero]
    positivity
  exact fun t ht => CenterManifold.eqOn_of_lipschitzOnWith (S := ball e R) (hK.mono hRs) hx hc
    (fun t ht => by rw [mem_ball, dist_eq_norm]; exact hball t ht)
    (fun _ _ => mem_ball_self hR) h0 ht

/-- **A nonconstant periodic solution of a `C¹` field never meets an equilibrium**: through an
equilibrium the solution is constant (uniqueness), on a whole period and hence everywhere. -/
@[tmio T, powerlib_foundation] theorem ne_zero_of_periodic {n : ℕ} {g : State n → State n}
    (hg : ContDiff ℝ 1 g) {x : ℝ → State n} {T : ℝ} (hT : 0 < T)
    (hx : ∀ t, HasDerivAt x (g (x t)) t) (hxT : ∀ t, x (t + T) = x t) (hnc : ∃ t, x t ≠ x 0)
    (t : ℝ) : g (x t) ≠ 0 := by
  intro he
  have hseg := eqOn_of_equilibrium hg he (x := x) (t₀ := t) (t₁ := t + T)
    (fun s _ => (hx s).hasDerivWithinAt) rfl
  have hper : Function.Periodic x T := hxT
  have hall : ∀ s, x s = x t := fun s => by
    obtain ⟨s', hs', hss'⟩ := hper.exists_mem_Ico hT s t
    rw [hss']
    exact hseg s' (Ico_subset_Icc_self hs')
  obtain ⟨s, hs⟩ := hnc
  exact hs (by rw [hall s, hall 0])

/-! ## Changing the clock -/

/-- **Time reparametrization of a periodic orbit.** If `x` is a `T`-periodic solution of
`ẋ = β(x) F(x)` (`T > 0`) with `β(x(t)) > 0` and continuous in `t`, then with the clock
`s(t) = ∫₀ᵗ β(x(u)) du` the curve `y(s(t)) = x(t)` is an `S`-periodic solution of `ẏ = F(y)`,
`S = s(T) > 0`, through the same points (`y 0 = x 0`). -/
@[tmio T, powerlib_foundation] theorem exists_periodic_of_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → E} {β : E → ℝ} {x : ℝ → E} {T : ℝ}
    (hT : 0 < T) (hβ : Continuous fun t => β (x t)) (hpos : ∀ t, 0 < β (x t))
    (hx : ∀ t, HasDerivAt x (β (x t) • F (x t)) t) (hxT : ∀ t, x (t + T) = x t) :
    ∃ y : ℝ → E, ∃ S, 0 < S ∧ (∀ s, HasDerivAt y (F (y s)) s) ∧ (∀ s, y (s + S) = y s) ∧
      (∀ s, ∃ t, y s = x t) ∧ (∀ t, ∃ s, x t = y s) ∧ y 0 = x 0 := by
  set b : ℝ → ℝ := fun t => β (x t) with hb
  have hbT : Function.Periodic b T := fun t => by simp only [hb, hxT]
  set σ : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, b u with hσ
  have hσd : ∀ t, HasDerivAt σ (b t) t := fun t =>
    (hβ.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hσc : Continuous σ := continuous_iff_continuousAt.mpr fun t => (hσd t).continuousAt
  have hmono : StrictMono σ := strictMono_of_deriv_pos fun t => by
    rw [(hσd t).deriv]; exact hpos t
  have hσ0 : σ 0 = 0 := by simp [hσ]
  set S := σ T with hS
  have hS0 : 0 < S := by rw [hS, ← hσ0]; exact hmono hT
  have hσT : ∀ t, σ (t + T) = σ t + S := fun t => by
    have hi : ∀ a c : ℝ, IntervalIntegrable b MeasureTheory.volume a c :=
      fun a c => hβ.intervalIntegrable a c
    simp only [hσ, hS]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t (t + T)),
      hbT.intervalIntegral_add_eq t 0, zero_add]
  have hnat : ∀ k : ℕ, σ (k * T) = k * S ∧ σ (-(k * T)) = -(k * S) := by
    intro k
    induction k with
    | zero => simp [hσ0]
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_succ, add_mul, one_mul, hσT, ih.1]
        ring
      · have h := hσT (-((k + 1 : ℕ) * T))
        rw [show -((k + 1 : ℕ) * T) + T = -(k * T) by push_cast; ring, ih.2] at h
        push_cast at h ⊢
        linarith
  have htop : Tendsto σ atTop atTop := tendsto_atTop_atTop.mpr fun c => by
    obtain ⟨k, hk⟩ := exists_nat_ge (c / S)
    refine ⟨k * T, fun t ht => ?_⟩
    have h1 := hmono.monotone ht
    rw [(hnat k).1] at h1
    have : c ≤ k * S := by rwa [div_le_iff₀ hS0] at hk
    linarith
  have hbot : Tendsto σ atBot atBot := tendsto_atBot_atBot.mpr fun c => by
    obtain ⟨k, hk⟩ := exists_nat_ge (-c / S)
    refine ⟨-(k * T), fun t ht => ?_⟩
    have h1 := hmono.monotone ht
    rw [(hnat k).2] at h1
    have : -c ≤ k * S := by rwa [div_le_iff₀ hS0] at hk
    linarith
  set e := StrictMono.orderIsoOfSurjective σ hmono (hσc.surjective htop hbot) with he
  have he1 : ∀ s, σ (e.symm s) = s := fun s =>
    StrictMono.orderIsoOfSurjective_self_symm_apply σ hmono _ s
  have he2 : ∀ t, e.symm (σ t) = t := fun t =>
    StrictMono.orderIsoOfSurjective_symm_apply_self σ hmono _ t
  refine ⟨fun s => x (e.symm s), S, hS0, fun s => ?_, fun s => ?_, fun s => ⟨e.symm s, rfl⟩,
    fun t => ⟨σ t, by simp only [he2]⟩, ?_⟩
  · have hinv : HasDerivAt e.symm (β (x (e.symm s)))⁻¹ s :=
      HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hσd (e.symm s))
        (hpos _).ne' (Eventually.of_forall he1)
    have h := (hx (e.symm s)).scomp s hinv
    rw [smul_smul, inv_mul_cancel₀ (hpos _).ne', one_smul] at h
    exact h
  · have h : e.symm (s + S) = e.symm s + T := by
      rw [← he1 s, ← hσT, he2, he2]
    simp only [h, hxT]
  · have h := he2 0
    rw [hσ0] at h
    simp only [h]

end powerlib.Dynamics

namespace powerlib.Dynamics.HopfCycle
open Set Filter Topology Metric Polynomial
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold (critπ critι)

variable {n : ℕ} {F : State n → ℝ → State n} {ω : ℝ} {q p : Fin n → ℂ}

/-- **Hopf cycles of a family that is `C¹` only near the point.** With the hypotheses of
`exists_hopfCycle`, except that the augmented field is `C¹` only on an open set `U ∋ 0` (and
analytic at `0`): for every small `μ` with `μ τ l₁ < 0` the field `F(·, μ)` has a nonconstant
periodic orbit with `(x(t), μ) ∈ U` and `ν/8 ≤ ‖critπ p x(t)‖² ≤ 8ν`, `ν = −μτ/(ω l₁)`. Proof:
the cycles of the cut-off family `b · F` (`exists_hopfCycle`; same Hopf data, `b = 1` near `0`)
avoid the zeros of `b` (`ne_zero_of_periodic`) and are cycles of `F` with another clock
(`exists_periodic_of_smul`). -/
@[tmio T, powerlib_foundation] theorem exists_hopfCycle_local {U : Set (State (n + 1))}
    (hU : IsOpen U) (h0 : (0 : State (n + 1)) ∈ U) (hF : ContDiffOn ℝ 1 (augField F) U)
    (ha : AnalyticAt ℝ (augField F) 0) (hF0 : ∀ μ, F 0 μ = 0)
    (hcp : IsCriticalPair (fun x => F x 0) 0 ω q p) {r : ℂ[X]}
    (hchar : (jacobianC (fun x => F x 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) {B : State n →L[ℝ] State n}
    (hB : HasDerivAt (fun μ => fderiv ℝ (fun x => F x μ) 0) B 0)
    (hτ : PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) ≠ 0)
    (hl : firstLyapunov (fun x => F x 0) 0 ω q p ≠ 0) :
    ∃ δ > 0, ∀ μ, |μ| < δ →
      μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q))) *
        firstLyapunov (fun x => F x 0) 0 ω q p < 0 →
      ∃ x : ℝ → State n, ∃ T, 0 < T ∧
        (∀ t, HasDerivAt x (F (x t) μ) t) ∧ (∀ t, x (t + T) = x t) ∧ (∃ t, x t ≠ x 0) ∧
        (∀ t, xin (x t) + μ • emu ∈ U) ∧
        ∀ t, -(μ * PlanarHopf.paramTrace ((critπ p).comp (B.comp (critι q)))) /
            (ω * firstLyapunov (fun x => F x 0) 0 ω q p) / 8 ≤ ‖critπ p (x t)‖ ^ 2 ∧
          ‖critπ p (x t)‖ ^ 2 ≤ 8 * (-(μ * PlanarHopf.paramTrace
            ((critπ p).comp (B.comp (critι q)))) /
              (ω * firstLyapunov (fun x => F x 0) 0 ω q p)) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 h0
  let b : ContDiffBump (0 : State (n + 1)) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  set G : State n → ℝ → State n := fun x μ => b (xin x + μ • emu) • F x μ with hGdef
  have haug : augField G = fun z => b z • augField F z := funext fun z => by
    simp only [augField, hGdef, xin_add_smul, map_smul]
  -- the cut-off family is globally `C¹` and agrees with `F` near `0`
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
  obtain ⟨δ, hδ, hcyc⟩ := exists_hopfCycle hGc (ha.congr hGF.symm) hG0
    ((isCriticalPair_congr h00).mpr hcp) (by rw [jacobianC_congr h00]; exact hchar) hr hB' hτ
    (by rw [hl']; exact hl)
  refine ⟨δ, hδ, fun μ hμ hs => ?_⟩
  rw [← hl'] at hs
  obtain ⟨x, T, hT0, -, hx, hxT, hxnc, hamp⟩ := hcyc μ hμ hs
  -- the cycle avoids the zeros of the cut-off
  have hgc : ContDiff ℝ 1 fun x => G x μ := by
    have h := (xpart (n := n)).contDiff.comp (hGc.comp
      ((xin (n := n)).contDiff.add (contDiff_const (c := μ • (emu : State (n + 1))))))
    have e : (fun x => G x μ) = ⇑xpart ∘ augField G ∘ fun x => xin x + μ • emu :=
      funext fun x => by simp [augField_xin_add]
    rw [e]
    exact h
  have hpos : ∀ t, 0 < b (xin (x t) + μ • emu) := fun t => by
    refine lt_of_le_of_ne b.nonneg fun h => ne_zero_of_periodic hgc hT0 hx hxT hxnc t ?_
    show b (xin (x t) + μ • emu) • F (x t) μ = 0
    rw [← h, zero_smul]
  have hcont : Continuous fun t => b (xin (x t) + μ • emu) :=
    b.continuous.comp (((xin (n := n)).continuous.comp
      (continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt)).add continuous_const)
  obtain ⟨y, S, hS0, hy, hyS, hyx, hxy, hy0⟩ := exists_periodic_of_smul (F := fun x => F x μ)
    (β := fun x => b (xin x + μ • emu)) hT0 hcont hpos hx hxT
  refine ⟨y, S, hS0, hy, hyS, ?_, fun s => ?_, fun s => ?_⟩
  · obtain ⟨t, ht⟩ := hxnc
    obtain ⟨s, hs⟩ := hxy t
    exact ⟨s, by rw [← hs, hy0]; exact ht⟩
  · obtain ⟨t, ht⟩ := hyx s
    rw [ht]
    have h := (hpos t).ne'
    rw [← Function.mem_support, b.support_eq] at h
    exact hεU (mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp h).trans (by simp [b]; linarith)))
  · obtain ⟨t, ht⟩ := hyx s
    rw [ht, ← hl']
    exact hamp t

end powerlib.Dynamics.HopfCycle
