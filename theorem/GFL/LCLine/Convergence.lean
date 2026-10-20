import theorem.GFL.LCLine.Equilibria
import theorem.PLL.PIPLLLinear
import Mathlib.Topology.MetricSpace.Sequences

/-! # Bounded solutions of the reduced GFL-PLL model converge; node / focus classification

Port current IN-positive (work-sync conventions §D1), as in `theorem/GFL/LCLine/Reduction.lean`;
no statement here involves a current.

Domain module (`vsc-stochastic-stability`, reduced model of `theorem/GFL/LCLine/Reduced2D.lean`).

Model boundary.
* General part: the PI-PLL field `piPLLField h K_p K_i 0` (`theorem/PLL/PIPLL.lean`), state
  `x 0 = θ` (PLL angle error), `x 1 = η` (PLL integrator), `θ̇ = K_p h(θ) + K_i η`, `η̇ = h(θ)`,
  no grid-frequency drift (`δω = 0`), continuous time, autonomous. Hypotheses on the phase
  detector: `h` globally Lipschitz, an antiderivative `V` of `−h` (`V′ = −h`), isolated zeros.
* Instantiation: the reduced 2-state model `Params.reducedField` of `vsc-stochastic-stability`
  (frozen `i_d*, i_q*`, rigid DC, current loop and LC/line at their quasi-steady algebraic values,
  no PWM / delay / limiter), `h(θ) = c₀ − A sin(θ + φ)` derived in
  `theorem/GFL/LCLine/Reduction.lean`, `V_g > 0` (so `A > 0`), `K_p, K_i > 0`.
* Solutions are `IsIntegralCurveOn` curves on `[0, ∞)`. Level: trajectory (ω-limit) level for the
  convergence theorem; linearization level for the node / focus classification.

Source: work-sync `projects/vsc-stochastic-stability/notes/concepts/reduced-2d-equation.md` §4
("所有有界轨迹被某盆地吸引"), `equilibria-and-bifurcation.md` §3 (结点 / 焦点判据) and §6.

Results.
* `piPLL_tendsto_of_bounded`: every solution that stays bounded on `[0, ∞)` converges to a
  single equilibrium `(θ*, 0)` with `h(θ*) = 0`. Proof: the storage
  `H = ½ K_i η² + V(θ)` is nonincreasing (`Ḣ = −K_p h²`) and bounded below on the bounded
  trajectory; since `t ↦ h(θ(t))` is Lipschitz in `t`, `h(θ(t)) → 0` (Barbalat-type argument);
  a cluster point `θ*` of `θ(t)` is a zero of `h`, isolation of the zeros and the intermediate value
  theorem force `θ(t) → θ*`, and `θ(t + 1) − θ(t) − K_i η(t) → 0` gives `η(t) → 0`.
  (The LeanForControl LaSalle principle is not used: it needs a compact positively invariant set,
  and the sublevel sets of `H` are unbounded for `c₀ ≠ 0`.)
* `Params.reduced_tendsto_equilibrium_of_bounded` (instantiation), with
  `Params.lipschitzWith_h`, `Params.h_zero_isolated`.
* `Params.reduced_node_iff`: at a slope `g = h′(θ*) < 0` the Jacobian (from `fderiv`) is
  `[[K_p g, K_i], [g, 0]]`; it has only real eigenvalues (stable node) iff `|g| ≥ 4 K_i / K_p²`,
  otherwise a non-real pair (stable focus) — instantiating `theorem/PLL/PIPLLLinear.lean`.

Family and connection conclusions.
No family and no connection conclusion. The convergence of
bounded solutions is a trajectory-level result (ω-limit level, on the forward ray of one
solution) outside the sentence language: `piPLL_tendsto_of_bounded` and its instantiation
`Params.reduced_tendsto_equilibrium_of_bounded` are kept as private
implementation evidence. The Lipschitz bound, isolation of the zeros of `h` and the node / focus
classification of the Jacobian remain static foundation results.

Correction (`equilibria-and-bifurcation.md` §6, `reduced-2d-equation.md` §4): the notes say every
bounded trajectory "is attracted by some basin" and that there is no "free divergence" on all of
`ℝ`. Formally proved here: a solution whose forward orbit is bounded converges to *some*
equilibrium — possibly a saddle (on its stable manifold) or a fold point, not necessarily a stable
point. Boundedness of the forward orbit is a hypothesis; the claim that no solution diverges
(boundedness for every initial condition) is not proved here.
-/

noncomputable section
namespace powerlib.GFL.LCLine
open Real Filter Topology Set
open powerlib.Dynamics (State)
open powerlib.PLL
open scoped Matrix

/-- Mean-value bound on a segment of `(0, ∞)`. -/
@[powerlib_foundation] private lemma abs_sub_le_of_hasDerivAt {g g' : ℝ → ℝ} {a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hg : ∀ t, 0 < t → HasDerivAt g (g' t) t)
    (hC : ∀ t ∈ Icc a b, |g' t| ≤ C) : |g b - g a| ≤ C * (b - a) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := g') (C := C)
    (fun x hx => (hg x (by linarith [hx.1])).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hC x (Ico_subset_Icc_self hx)) b ⟨hab, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

/-- One-sided mean-value bound on a segment of `(0, ∞)`. -/
@[powerlib_foundation] private lemma sub_le_of_hasDerivAt {g g' : ℝ → ℝ} {a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hg : ∀ t, 0 < t → HasDerivAt g (g' t) t)
    (hC : ∀ t ∈ Icc a b, g' t ≤ C) : g b - g a ≤ C * (b - a) := by
  have hpos : ∀ x ∈ Icc a b, 0 < x := fun x hx => by linarith [hx.1]
  refine (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    (fun x hx => (hg x (hpos x hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hg x (hpos x (interior_subset hx))).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_) a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  rw [(hg x (hpos x (interior_subset hx))).deriv]
  exact hC x (interior_subset hx)

variable {h V : ℝ → ℝ} {Kp Ki : ℝ}

/-- Bounded forward solutions of the PI-PLL converge to an equilibrium.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem piPLL_tendsto_of_bounded
    (hKp : 0 < Kp) (hKi : 0 < Ki) {L : NNReal} (hL : LipschitzWith L h)
    (hV : ∀ θ, HasDerivAt V (-h θ) θ)
    (hiso : ∀ θ, h θ = 0 → ∀ᶠ θ' in 𝓝[≠] θ, h θ' ≠ 0)
    {φ : ℝ → State 2}
    (hφ : IsIntegralCurveOn φ (fun _ x => piPLLField h Kp Ki 0 x) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ θs, h θs = 0 ∧ Tendsto φ atTop (𝓝 (PhasePlane.mk θs 0)) := by
  set θ : ℝ → ℝ := fun t => φ t 0 with hθdef
  set η : ℝ → ℝ := fun t => φ t 1 with hηdef
  have hderφ : ∀ t, 0 < t → HasDerivAt φ (piPLLField h Kp Ki 0 (φ t)) t := fun t ht =>
    (hφ t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht)
  have hθd : ∀ t, 0 < t → HasDerivAt θ (Kp * h (θ t) + Ki * η t) t := by
    intro t ht
    have := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (hderφ t ht)
    have e : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ)
        (piPLLField h Kp Ki 0 (φ t)) = Kp * h (θ t) + Ki * η t := by
      simp [θ, η]
    rw [e] at this
    exact this
  have hηd : ∀ t, 0 < t → HasDerivAt η (h (θ t)) t := by
    intro t ht
    have := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (hderφ t ht)
    have e : (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ)
        (piPLLField h Kp Ki 0 (φ t)) = h (θ t) := by
      simp [θ]
    rw [e] at this
    exact this
  have hφc : ContinuousOn φ (Ici 0) := hφ.continuousOn
  have hθc : ContinuousOn θ (Ici 0) := (PiLp.continuous_apply 2 _ 0).comp_continuousOn hφc
  -- uniform bound on the trajectory
  obtain ⟨R, hR⟩ : ∃ R, ∀ t, 0 ≤ t → |θ t| ≤ R ∧ |η t| ≤ R := by
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    refine ⟨C, fun t ht => ?_⟩
    have hn := hC (φ t) ⟨t, ht, rfl⟩
    have h0 := PiLp.norm_apply_le (φ t) 0
    have h1 := PiLp.norm_apply_le (φ t) 1
    rw [Real.norm_eq_abs] at h0 h1
    exact ⟨h0.trans hn, h1.trans hn⟩
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR 0 le_rfl).1
  have hLip : ∀ a b, |h a - h b| ≤ L * |a - b| := fun a b => by
    have := hL.dist_le_mul a b
    rwa [Real.dist_eq, Real.dist_eq] at this
  have hhc : Continuous h := hL.continuous
  set Mh : ℝ := |h 0| + L * R with hMh
  have hhb : ∀ t, 0 ≤ t → |h (θ t)| ≤ Mh := fun t ht => by
    have h1 := hLip (θ t) 0
    rw [sub_zero] at h1
    have h2 := abs_sub_abs_le_abs_sub (h (θ t)) (h 0)
    have : L * |θ t| ≤ L * R := mul_le_mul_of_nonneg_left (hR t ht).1 L.2
    linarith
  set B : ℝ := Kp * Mh + Ki * R with hB
  have hθs : ∀ t, 0 ≤ t → |Kp * h (θ t) + Ki * η t| ≤ B := fun t ht => by
    calc |Kp * h (θ t) + Ki * η t| ≤ |Kp * h (θ t)| + |Ki * η t| := abs_add_le _ _
      _ = Kp * |h (θ t)| + Ki * |η t| := by
          rw [abs_mul, abs_mul, abs_of_pos hKp, abs_of_pos hKi]
      _ ≤ B := by
          have := hR t ht
          have := hhb t ht
          nlinarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hθs 0 le_rfl)
  -- energy
  set E : ℝ → ℝ := fun t => Ki / 2 * η t ^ 2 + V (θ t) with hE
  have hEd : ∀ t, 0 < t → HasDerivAt E (-(Kp * h (θ t) ^ 2)) t := by
    intro t ht
    have h2 : HasDerivAt E (Ki / 2 * (((2 : ℕ) : ℝ) * η t ^ (2 - 1) * h (θ t)) +
        -h (θ t) * (Kp * h (θ t) + Ki * η t)) t :=
      (((hηd t ht).pow 2).const_mul (Ki / 2)).add ((hV (θ t)).comp t (hθd t ht))
    convert h2 using 1
    push_cast
    ring
  have hEanti : ∀ a b, 0 < a → a ≤ b → E b ≤ E a := fun a b ha hab => by
    have := sub_le_of_hasDerivAt (C := 0) ha hab hEd (fun t _ => by
      have := sq_nonneg (h (θ t)); nlinarith)
    linarith
  obtain ⟨m0, hm0⟩ := (isCompact_Icc (a := -R) (b := R)).bddBelow_image
    (fun x _ => (hV x).continuousAt.continuousWithinAt : ContinuousOn V (Icc (-R) R))
  have hElb : ∀ t, 0 < t → m0 ≤ E t := fun t ht => by
    have hθR := abs_le.mp (hR t ht.le).1
    have := hm0 ⟨θ t, ⟨hθR.1, hθR.2⟩, rfl⟩
    have : 0 ≤ Ki / 2 * η t ^ 2 := by positivity
    simp only [E]; linarith
  set S : Set ℝ := E '' Ioi 0
  have hSne : S.Nonempty := ⟨E 1, 1, by norm_num, rfl⟩
  have hSbdd : BddBelow S := ⟨m0, by rintro _ ⟨t, ht, rfl⟩; exact hElb t ht⟩
  set m : ℝ := sInf S
  have hm_le : ∀ t, 0 < t → m ≤ E t := fun t ht => csInf_le hSbdd ⟨t, ht, rfl⟩
  have hm_lt : ∀ c, 0 < c → ∃ T, 0 < T ∧ E T < m + c := fun c hc => by
    obtain ⟨_, ⟨T, hT, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne (lt_add_of_pos_right m hc)
    exact ⟨T, hT, hlt⟩
  -- Step 3: `h(θ t) → 0`
  have hh0 : Tendsto (fun t => h (θ t)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    set K : ℝ := L * B + 1
    have hK : 0 < K := by positivity
    set δ : ℝ := ε / (2 * K)
    have hδ : 0 < δ := by positivity
    set c : ℝ := Kp * (ε / 2) ^ 2 * δ
    have hc : 0 < c := by positivity
    obtain ⟨T, hT, hET⟩ := hm_lt c hc
    obtain ⟨t, ht, hεt⟩ := hfreq (max T 1)
    rw [Real.dist_eq, sub_zero] at hεt
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht)
    have hTt : T ≤ t := (le_max_left _ _).trans ht
    have hlow : ∀ s ∈ Icc t (t + δ), ε / 2 ≤ |h (θ s)| := by
      intro s hs
      have hθ' : |θ s - θ t| ≤ B * (s - t) :=
        abs_sub_le_of_hasDerivAt ht0 hs.1 hθd (fun u hu => hθs u (by linarith [hu.1]))
      have hLB : L * B * δ < ε / 2 := by
        have : L * B * δ = (ε / 2) * (L * B / K) := by
          simp only [δ]; field_simp
        rw [this]
        have : L * B / K < 1 := by
          rw [div_lt_one hK]; linarith
        nlinarith
      have h1 := hLip (θ s) (θ t)
      have h2 : L * |θ s - θ t| ≤ L * B * δ := by
        calc L * |θ s - θ t| ≤ L * (B * (s - t)) := mul_le_mul_of_nonneg_left hθ' L.2
          _ ≤ L * (B * δ) := by
              apply mul_le_mul_of_nonneg_left _ L.2
              apply mul_le_mul_of_nonneg_left _ hB0
              linarith [hs.2]
          _ = L * B * δ := by ring
      have h3 := abs_sub_abs_le_abs_sub (h (θ t)) (h (θ s))
      rw [abs_sub_comm (h (θ t))] at h3
      linarith
    have hdec := sub_le_of_hasDerivAt (C := -(Kp * (ε / 2) ^ 2)) ht0
      (le_add_of_nonneg_right hδ.le) hEd (fun s hs => by
        have hge := hlow s hs
        have : (ε / 2) ^ 2 ≤ h (θ s) ^ 2 := by
          rw [← sq_abs (h (θ s))]
          exact pow_le_pow_left₀ (by positivity) hge 2
        nlinarith)
    have hEt : E t ≤ E T := hEanti T t hT hTt
    have hm2 := hm_le (t + δ) (by linarith)
    have : -(Kp * (ε / 2) ^ 2) * (t + δ - t) = -c := by simp only [c]; ring
    linarith
  -- Step 4: a cluster point of `θ` is a zero of `h`
  obtain ⟨θs, -, ψ, hψ, hψt⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (-R) R)
    (x := fun n : ℕ => θ n) (fun n => abs_le.mp (hR n (Nat.cast_nonneg n)).1)
  have hψinf : Tendsto (fun k => ((ψ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
  have hzero : h θs = 0 := by
    have h1 : Tendsto (fun k => h (θ (ψ k))) atTop (𝓝 (h θs)) :=
      (hhc.tendsto θs).comp hψt
    have h2 : Tendsto (fun k => h (θ (ψ k))) atTop (𝓝 0) := hh0.comp hψinf
    exact tendsto_nhds_unique h1 h2
  -- Step 5: `θ t → θs`
  have hθlim : Tendsto θ atTop (𝓝 θs) := by
    rw [Metric.tendsto_atTop]
    intro ε0 hε0
    obtain ⟨r, hr, hr'⟩ :=
      Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp (hiso θs hzero))
    set ε : ℝ := min ε0 (r / 2)
    have hε : 0 < ε := lt_min hε0 (by positivity)
    have hεr : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hp : h (θs + ε) ≠ 0 := hr' (by rw [Real.dist_eq]; simp [abs_of_pos hε, hεr])
      (by simp [hε.ne'])
    have hn : h (θs - ε) ≠ 0 := hr' (by rw [Real.dist_eq]; simp [abs_of_pos hε, hεr])
      (by simp [hε.ne'])
    set m' : ℝ := min |h (θs + ε)| |h (θs - ε)|
    have hm' : 0 < m' := lt_min (abs_pos.mpr hp) (abs_pos.mpr hn)
    obtain ⟨T1, hT1⟩ := Metric.tendsto_atTop.mp hh0 m' hm'
    obtain ⟨k, hk1, hk2⟩ := ((hψinf.eventually (eventually_ge_atTop (max T1 1))).and
      (Metric.tendsto_atTop.mp hψt ε hε |> fun ⟨N, hN⟩ => eventually_atTop.mpr ⟨N, hN⟩)).exists
    set t0 : ℝ := ((ψ k : ℕ) : ℝ)
    have ht0 : 0 < t0 := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hk1)
    have hT1t0 : T1 ≤ t0 := (le_max_left _ _).trans hk1
    have hstart : |θ t0 - θs| < ε := by
      have := hk2; rwa [Real.dist_eq] at this
    have hnot : ∀ s, t0 ≤ s → θ s ≠ θs + ε ∧ θ s ≠ θs - ε := by
      intro s hs
      have hsmall := hT1 s (hT1t0.trans hs)
      rw [Real.dist_eq, sub_zero] at hsmall
      constructor
      · intro heq; rw [heq] at hsmall
        exact absurd (lt_of_lt_of_le hsmall (min_le_left _ _)) (lt_irrefl _)
      · intro heq; rw [heq] at hsmall
        exact absurd (lt_of_lt_of_le hsmall (min_le_right _ _)) (lt_irrefl _)
    refine ⟨t0, fun t ht => ?_⟩
    rw [Real.dist_eq]
    have hcont : ContinuousOn θ (Icc t0 t) := hθc.mono (fun s hs => le_trans ht0.le hs.1)
    have hst := abs_lt.mp hstart
    have : |θ t - θs| < ε := by
      rw [abs_lt]
      constructor
      · by_contra hle
        push Not at hle
        obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc' ht hcont
          (show θs - ε ∈ Icc (θ t) (θ t0) from ⟨by linarith, by linarith⟩)
        exact (hnot s hs.1).2 hseq
      · by_contra hle
        push Not at hle
        obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc ht hcont
          (show θs + ε ∈ Icc (θ t0) (θ t) from ⟨by linarith, by linarith⟩)
        exact (hnot s hs.1).1 hseq
    exact lt_of_lt_of_le this (min_le_left _ _)
  -- Step 6: `η t → 0`
  have hηlim : Tendsto η atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ε' : ℝ := ε * Ki / (2 * (Kp + Ki))
    have hε' : 0 < ε' := by positivity
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hθlim (ε * Ki / 4) (by positivity)
    obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hh0 ε' hε'
    refine ⟨max (max N1 N2) 1, fun t ht => ?_⟩
    have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
    have ht0 : 0 < t := by linarith
    have htN1 : N1 ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
    have htN2 : N2 ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
    have hsmall : ∀ s, t ≤ s → |h (θ s)| < ε' := fun s hs => by
      have := hN2 s (htN2.trans hs); rwa [Real.dist_eq, sub_zero] at this
    have hηvar : ∀ s ∈ Icc t (t + 1), |η s - η t| ≤ ε' := by
      intro s hs
      have := abs_sub_le_of_hasDerivAt (C := ε') ht0 hs.1 hηd
        (fun u hu => (hsmall u hu.1).le)
      nlinarith [hs.2]
    have hg := abs_sub_le_of_hasDerivAt (g := fun s => θ s - Ki * η t * s)
      (g' := fun s => Kp * h (θ s) + Ki * η s - Ki * η t) (C := (Kp + Ki) * ε') ht0
      (le_add_of_nonneg_right zero_le_one)
      (fun s hs => by
        have h2 : HasDerivAt (fun s => θ s - Ki * η t * s)
            (Kp * h (θ s) + Ki * η s - Ki * η t * 1) s :=
          (hθd s hs).sub ((hasDerivAt_id s).const_mul (Ki * η t))
        rw [mul_one] at h2
        exact h2)
      (fun s hs => by
        have h1 := hsmall s hs.1
        have h2 := hηvar s hs
        calc |Kp * h (θ s) + Ki * η s - Ki * η t|
            = |Kp * h (θ s) + Ki * (η s - η t)| := by ring_nf
          _ ≤ |Kp * h (θ s)| + |Ki * (η s - η t)| := abs_add_le _ _
          _ = Kp * |h (θ s)| + Ki * |η s - η t| := by
              rw [abs_mul, abs_mul, abs_of_pos hKp, abs_of_pos hKi]
          _ ≤ (Kp + Ki) * ε' := by nlinarith)
    have hθ1 := hN1 (t + 1) (by linarith)
    have hθ0 := hN1 t htN1
    rw [Real.dist_eq] at hθ1 hθ0 ⊢
    rw [sub_zero]
    have hkey : Ki * |η t| ≤ |θ (t + 1) - θ t| + (Kp + Ki) * ε' := by
      have hg' : |θ (t + 1) - θ t - Ki * η t| ≤ (Kp + Ki) * ε' := by
        have e2 : t + 1 - t = 1 := by ring
        rw [e2, mul_one] at hg
        calc |θ (t + 1) - θ t - Ki * η t|
            = |θ (t + 1) - Ki * η t * (t + 1) - (θ t - Ki * η t * t)| := by ring_nf
          _ ≤ (Kp + Ki) * ε' := hg
      calc Ki * |η t| = |(θ (t + 1) - θ t) - (θ (t + 1) - θ t - Ki * η t)| := by
            rw [show (θ (t + 1) - θ t) - (θ (t + 1) - θ t - Ki * η t) = Ki * η t by ring,
              abs_mul, abs_of_pos hKi]
        _ ≤ |θ (t + 1) - θ t| + |θ (t + 1) - θ t - Ki * η t| := abs_sub _ _
        _ ≤ |θ (t + 1) - θ t| + (Kp + Ki) * ε' := by linarith
    have hdiff : |θ (t + 1) - θ t| < ε * Ki / 2 := by
      calc |θ (t + 1) - θ t| = |(θ (t + 1) - θs) - (θ t - θs)| := by ring_nf
        _ ≤ |θ (t + 1) - θs| + |θ t - θs| := abs_sub _ _
        _ < ε * Ki / 4 + ε * Ki / 4 := add_lt_add hθ1 hθ0
        _ = ε * Ki / 2 := by ring
    have hε'eq : (Kp + Ki) * ε' = ε * Ki / 2 := by
      simp only [ε']; field_simp
    have : Ki * |η t| < Ki * ε := by linarith
    exact lt_of_mul_lt_mul_left this hKi.le
  -- Step 7: the state converges
  refine ⟨θs, hzero, ?_⟩
  have hφeq : φ = fun t => WithLp.toLp 2 ![θ t, η t] := by
    funext t
    exact (PhasePlane.mk_coords (φ t)).symm
  rw [hφeq]
  apply ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).tendsto _).comp
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa using hθlim
  · simpa using hηlim

/-! ### Instantiation: the reduced GFL-PLL model of `vsc-stochastic-stability` -/

namespace Params
variable (p : Params)

/-- `h(θ) = c₀ − A sin(θ + φ)` is `A`-Lipschitz. -/
@[powerlib_foundation] theorem lipschitzWith_h (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg) :
    LipschitzWith ⟨p.amp, (p.amp_pos hVg hΔ).le⟩ p.h := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, p.h_eq_polar hwC hΔ, p.h_eq_polar hwC hΔ]
  have hA := (p.amp_pos hVg hΔ).le
  have := abs_sin_sub_sin_le (y + p.phase) (x + p.phase)
  calc |p.c0 - p.amp * sin (x + p.phase) - (p.c0 - p.amp * sin (y + p.phase))|
      = p.amp * |sin (y + p.phase) - sin (x + p.phase)| := by
        rw [show p.c0 - p.amp * sin (x + p.phase) - (p.c0 - p.amp * sin (y + p.phase)) =
          p.amp * (sin (y + p.phase) - sin (x + p.phase)) by ring, abs_mul, abs_of_nonneg hA]
    _ ≤ p.amp * |y + p.phase - (x + p.phase)| := mul_le_mul_of_nonneg_left this hA
    _ = (⟨p.amp, hA⟩ : NNReal) * |x - y| := by
        rw [show y + p.phase - (x + p.phase) = -(x - y) by ring, abs_neg]

/-- The zeros of `h` are isolated (at most two per period, `V_g > 0`). -/
@[powerlib_foundation] theorem h_zero_isolated (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg)
    (θ : ℝ) : ∀ᶠ θ' in 𝓝[≠] θ, p.h θ' ≠ 0 := by
  set Z := SpecialFunctions.sinusoidZeros p.c0 p.amp p.phase (θ - π)
  have hfin : Z.Finite :=
    (Set.toFinite _).subset (SpecialFunctions.sinusoidZeros_subset (p.amp_pos hVg hΔ))
  have h1 : (Z \ {θ})ᶜ ∈ 𝓝 θ :=
    (hfin.subset Set.sdiff_subset).isClosed.compl_mem_nhds (by simp)
  have h2 : Ioo (θ - π) (θ + π) ∈ 𝓝 θ := Ioo_mem_nhds (by linarith [pi_pos]) (by linarith [pi_pos])
  filter_upwards [mem_nhdsWithin_of_mem_nhds h1, mem_nhdsWithin_of_mem_nhds h2,
    self_mem_nhdsWithin] with θ' hZ hI hne hzero
  apply hZ
  refine ⟨⟨⟨hI.1.le, by linarith [hI.2]⟩, ?_⟩, hne⟩
  rw [← p.h_eq_polar hwC hΔ]
  exact hzero

/-- A2: for `K_p, K_i > 0`, `V_g > 0`, every solution of the reduced 2-state PLL model that
stays bounded for `t ≥ 0` converges to a single equilibrium `(θ*, 0)` with `h(θ*) = 0`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem reduced_tendsto_equilibrium_of_bounded (hwC : p.wC ≠ 0)
    (hΔ : p.Δ ≠ 0) (hVg : 0 < p.Vg) (hKp : 0 < p.Kp) (hKi : 0 < p.Ki) {φ : ℝ → State 2}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.reducedField x) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ θs, p.h θs = 0 ∧ Tendsto φ atTop (𝓝 (PhasePlane.mk θs 0)) := by
  rw [reducedField_eq] at hφ
  exact piPLL_tendsto_of_bounded hKp hKi (p.lipschitzWith_h hwC hΔ hVg) (p.hasDerivAt_pot hwC hΔ)
    (fun θ _ => p.h_zero_isolated hwC hΔ hVg θ) hφ hb

/-- A1, node / focus: at a point with slope `g = h′(θ*) = −A cos(θ* + φ) < 0` the Jacobian of the
reduced field (computed with `fderiv`) is `[[K_p g, K_i], [g, 0]]`, and all its eigenvalues are
real (stable node) iff `|g| ≥ 4 K_i / K_p²`; otherwise it has a non-real pair (stable focus). -/
@[powerlib_foundation] theorem reduced_node_iff (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKp : p.Kp ≠ 0)
    {θ η : ℝ} (hslope : -(p.amp * cos (θ + p.phase)) < 0) :
    fderiv ℝ p.reducedField (PhasePlane.mk θ η) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          (piPLLJacobian p.Kp p.Ki (-(p.amp * cos (θ + p.phase)))) ∧
      ((∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
          (piPLLJacobian p.Kp p.Ki (-(p.amp * cos (θ + p.phase)))).map (algebraMap ℝ ℂ) *ᵥ v =
            μ • v → μ.im = 0) ↔
        4 * p.Ki / p.Kp ^ 2 ≤ |-(p.amp * cos (θ + p.phase))|) :=
  ⟨p.fderiv_reducedField hwC hΔ θ η, piPLLJacobian_eigenvalues_real_iff hKp hslope⟩

end Params

end powerlib.GFL.LCLine
