import theorem.Averaging.StateSpaceAveraging
import theorem.LTI.Discrete
import theorem.Criteria.Hurwitz2
import theorem.Periodic.LTI

/-! # Stability transfer from the state-space averaged model to the switched converter

For fast switching, a Hurwitz state-space averaged matrix `Ā = d A₁ + (1 − d) A₂` makes every
trajectory of the ideal two-topology switched linear converter decay exponentially, ripple
included, with constants independent of the switching period `T ≤ T₀`, and the averaging error
`O(T)` holds on the whole half line. Conversely such a `T`-uniform decay forces `Ā` Hurwitz. For
slow switching the transfer fails: two Hurwitz topologies with a Hurwitz average switch into an
unstable system.

Scope.
* The model boundary of `theorem/Averaging/StateSpaceAveraging.lean`: an ideal two-topology
  switched linear converter in continuous conduction mode, state `x ∈ ℝ^X` (sup norm; matrices
  carry the `L∞` operator norm), `ẋ = A₁ x` on `[kT, kT + dT]` and `ẋ = A₂ x` on
  `[kT + dT, (k + 1)T]`, fixed duty ratio `d ∈ [0, 1]`, ideal instantaneous switches, continuous
  time; no PWM carrier or modulator dynamics beyond the fixed duty ratio, no control loop, no delay,
  no discontinuous conduction. Every statement holds for arbitrary matrices `A₁`, `A₂` (no
  particular converter is formalized).
* The dynamics are homogeneous. With a constant input the difference of two switched trajectories
  solves the same homogeneous switched equation, so the decay statements are incremental: every
  switched trajectory approaches every other (in particular the periodic steady state) at the
  rate `α`. Augmenting `u̇ = 0` as a state (as in `StateSpaceAveraging`) adds a zero eigenvalue,
  so a Hurwitz hypothesis must be read on the deviation dynamics, not on the augmented matrix.
* A switched trajectory is written out in each statement exactly as in `StateSpaceAveraging`:
  `∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
  IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))`, with one-sided
  derivatives at the switching instants. Uniform exponential decay
  `∃ C α, 0 < C ∧ 0 < α ∧ … ‖x(t)‖ ≤ C e^{−α t} ‖x(0)‖` quantifies real constants and is written
  out in each statement; no behaviour is defined here (single-semantics rule). Generic
  mathematics only (foundation results).
* Hurwitz is LeanForControl's eigenpair predicate `LinearSystems.IsHurwitz` on `Fin n`; the
  statements for any finite index type and in a Banach algebra assume a contractive averaged
  block `‖e^{HĀ}‖ < 1` instead, which a Hurwitz matrix supplies
  (`exists_norm_exp_lt_one_of_isHurwitz`). Schur stability is `LTI.SchurStable`
  (`theorem/LTI/Discrete.lean`).
* `T₀` is explicit in the proofs but conservative: with `a = ‖A₁‖ + ‖A₂‖`,
  `c = a² (2 e^{2a} + 3 e^a)` (the constant built in the proof of `periodMap_sub_exp_le`) and `H` a
  horizon with `‖e^{HĀ}‖ ≤ 1/4`, the proof of `exists_periodMap_pow_le` takes
  `T₀ = min(1, log 2/(a + 1), 1/(4 e^{a(H+1)} (H + 1) c + 1))`, and the decay rate is
  `α = log(4/3)/(H + 1)`. The statements only assert existence; no sharp switching-frequency bound
  is claimed.
* Not covered: an unstable average (`Re μ > 0`) giving an unstable switched system for every small
  `T` (needs eigenvalue continuity; only the `T`-uniform converse is proved); varying duty ratios
  (closed-loop PWM), discontinuous conduction, nonlinear topologies, sampled-data control.

Source: work-sync theory/T-averaging-method.md §1.5 (state-space averaging, Middlebrook–Ćuk),
§1.8 (long-time behaviour: an asymptotically stable averaged equilibrium attracts the original
system, an unstable one repels it; here the linear case with the `T`-uniform converse), §2.4
(averaging fails without time-scale separation: the slow-switching example). Tools:
`theorem/Averaging/StateSpaceAveraging.lean` (`periodMap_sub_exp_le`, `norm_pow_sub_pow_le`,
`switched_sample`, `switched_ripple`, `stateSpaceAveraging_error_uniform`, `const_solution_eq`),
`theorem/LTI/Discrete.lean` (`exists_pow_norm_lt_one`, `exponentiallyStable_iff_schurStable`),
LeanForControl `LinearSystems.spectralRadius_exp_complexification_lt_one` and
`MatrixAlgebra.complexification_exp`, `theorem/Periodic/LTI.lean`
(`monodromy_const_mulVec_eigen`, `norm_exp_mul_eq`), `theorem/Criteria/Hurwitz2.lean`
(`isHurwitz_fin_two_of_iff`).

Results.
* Banach algebra (`‖1‖ = 1`), `M_T = e^{(1−d)TA₂} e^{dTA₁}` (`periodMap`), `Ā` (`avgMatrix`):
  `exists_norm_exp_smul_le_quarter` (a contractive block `‖e^{HĀ}‖ < 1` gives `‖e^{H'Ā}‖ ≤ 1/4`);
  `exists_periodMap_pow_le` (block contraction: for `T ≤ T₀` there is `N` with
  `H ≤ N T ≤ H + 1` and `‖M_T^N‖ ≤ 3/4`, from `‖M_T^N − e^{NTĀ}‖ ≤ N e^{aNT} c T² = O(T)`);
  `exists_periodMap_pow_decay` (`‖M_T^k‖ ≤ C e^{−α k T}` with `C`, `α` independent of `T`);
  `exists_periodMap_pow_sub_le` (`‖M_T^k − e^{kTĀ}‖ ≤ C T` for **every** `k`, through the
  telescoping identity `pow_sub_pow_eq_sum` and both decays). Auxiliary: `exp_natCast_mul_smul`,
  `avgMatrix_self`, `periodMap_self`, `exp_smul_sqZero_sub_smul_one`
  (`e^{s(N − ε)} = e^{−εs}(1 + sN)` for `N² = 0`).
* Switched trajectories (any finite index type, contractive averaged block):
  `exists_switched_trajectory` (every initial state has a switched trajectory, so the statements
  about every switched trajectory are not vacuous); `switched_decay_of_norm_exp_lt_one`
  (`‖x(t)‖ ≤ C e^{−α t} ‖x(0)‖` for all `t ≥ 0`, `T ≤ T₀`, ripple included through
  `switched_ripple`); `switched_averaging_error_of_norm_exp_lt_one`
  (`‖x(t) − e^{tĀ} x(0)‖ ≤ C T ‖x(0)‖` for all `t ≥ 0`: the finite horizon of
  `stateSpaceAveraging_error_uniform` removed under stability).
* Hurwitz average (`Fin n`): `exists_norm_exp_lt_one_of_isHurwitz`;
  `periodMap_schurStable_of_isHurwitz` (for `T ∈ (0, T₀]` the period map is Schur stable with a
  power of norm `< 1`); `switched_decay_of_isHurwitz` (uniform exponential decay of every switched
  trajectory); `switched_averaging_error_of_isHurwitz` (averaging error `O(T)` on `[0, ∞)`);
  `isHurwitz_of_switched_decay` (converse: decay with `T`-independent constants for all
  `T ∈ (0, T₀]` forces `Ā` Hurwitz, via the averaging error, `exists_switched_trajectory` and the
  Floquet multiplier `e^{μ t}` of an eigenpair); `isHurwitz_iff_switched_decay` (the transfer is
  exact in the fast-switching limit).
* Slow switching (`d = 1/2`, `A₁ = N₁ − εI`, `A₂ = N₂ − εI`, `N₁ = [[0, 1], [0, 0]]`,
  `N₂ = [[0, 0], [−1, 0]]`): `periodMap_shear_pair` (`M_T = e^{−εT} [[1, T/2], [−T/2, 1 − T²/4]]`,
  trace `e^{−εT}(2 − T²/4)`, determinant `e^{−2εT}`); `slowSwitching_counterexample` (`ε = 1/10`:
  `A₁`, `A₂` and `Ā = [[−1/10, 1/2], [−1/2, −1/10]]` are Hurwitz, but `M_5 (1, −2) =
  −4 e^{−1/2} (1, −2)`, `4 e^{−1/2} ≈ 2.43`, so `M_5` is not Schur stable);
  `slowSwitching_unbounded_trajectory` (a switched trajectory from `(1, −2)` with
  `x(5k) = (−4 e^{−1/2})^k (1, −2)`, unbounded). The instability is a flip (period-doubling,
  real multiplier `< −1`, a subharmonic oscillation at half the switching frequency) once the
  undamped trace `2 − T²/4` leaves `[−2, 2]` at `T = 4`; numerically (not formalized) the spectral
  radius of `M_T` is `e^{−T/10} < 1` for `T ≤ 4` and crosses `1` at `T ≈ 4.08` for `ε = 1/10`,
  about a third of the averaged oscillation period `4π`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology Matrix
open scoped Matrix.Norms.Operator

/-! ## Banach-algebra estimates -/

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

omit [NormOneClass 𝔸] in
/-- `e^{(j s) X} = (e^{s X})^j`. -/
@[powerlib_foundation] theorem exp_natCast_mul_smul (X : 𝔸) (s : ℝ) (j : ℕ) :
    NormedSpace.exp (((j : ℝ) * s) • X) = NormedSpace.exp (s • X) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.cast_succ, add_mul, one_mul, exp_add_smul, ih, pow_succ]

/-- A contractive exponential block `‖e^{HX}‖ < 1` gives a block `‖e^{H'X}‖ ≤ 1/4` (a multiple of
the horizon). -/
@[powerlib_foundation] theorem exists_norm_exp_smul_le_quarter {X : 𝔸} {H : ℝ} (hH : 0 < H)
    (hq : ‖NormedSpace.exp (H • X)‖ < 1) :
    ∃ H' : ℝ, 0 < H' ∧ ‖NormedSpace.exp (H' • X)‖ ≤ 1 / 4 := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 4) hq
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · norm_num at hj
    · exact h
  refine ⟨j * H, mul_pos (Nat.cast_pos.mpr hj0) hH, ?_⟩
  rw [exp_natCast_mul_smul]
  exact (norm_pow_le _ _).trans hj.le

/-- **One block of switching periods contracts.** If the averaged model contracts over the
horizon `H` by `1/4`, then for every switching period `T ≤ T₀` a block of `N` periods with
`H ≤ N T ≤ H + 1` contracts by `3/4`. -/
@[powerlib_foundation] theorem exists_periodMap_pow_le {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : 𝔸) {H : ℝ} (hH : 0 < H)
    (hexp : ‖NormedSpace.exp (H • avgMatrix d A₁ A₂)‖ ≤ 1 / 4) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ 1 ∧ ∀ T ∈ Ioc (0 : ℝ) T₀, ∃ N : ℕ, 0 < N ∧
      H ≤ (N : ℝ) * T ∧ (N : ℝ) * T ≤ H + 1 ∧ ‖periodMap d T A₁ A₂ ^ N‖ ≤ 3 / 4 := by
  obtain ⟨c, hc, hper⟩ := periodMap_sub_exp_le hd0 hd1 A₁ A₂
  set a := ‖A₁‖ + ‖A₂‖ with hadef
  have ha0 : 0 ≤ a := by positivity
  set Ab := avgMatrix d A₁ A₂ with hAbdef
  have hAb : ‖Ab‖ ≤ a := norm_avgMatrix_le hd0 hd1 A₁ A₂
  set K := Real.exp (a * (H + 1)) with hKdef
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set Q := K * (H + 1) * c with hQdef
  have hQ : 0 ≤ Q := by positivity
  refine ⟨min (min 1 (Real.log 2 / (a + 1))) (1 / (4 * Q + 1)), by positivity,
    (min_le_left _ _).trans (min_le_left _ _), fun T hT => ?_⟩
  obtain ⟨hT0, hTT₀⟩ := hT
  have hT1 : T ≤ 1 := hTT₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hTlog : T ≤ Real.log 2 / (a + 1) :=
    hTT₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hTc : T ≤ 1 / (4 * Q + 1) := hTT₀.trans (min_le_right _ _)
  set N := ⌈H / T⌉₊ with hNdef
  have hN1 : H ≤ N * T := by
    have := Nat.le_ceil (H / T)
    rwa [div_le_iff₀ hT0] at this
  have hN2 : (N : ℝ) * T < H + T := by
    have h := Nat.ceil_lt_add_one (div_nonneg hH.le hT0.le)
    have h' : (N : ℝ) * T < (H / T + 1) * T := mul_lt_mul_of_pos_right h hT0
    rwa [add_mul, div_mul_cancel₀ _ hT0.ne', one_mul] at h'
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, zero_mul] at hN1
      linarith
    · exact h
  refine ⟨N, hNpos, hN1, by linarith, ?_⟩
  -- `e^{aT} ≤ 2`
  have haT : a * T ≤ Real.log 2 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < a + 1)).mp hTlog
    nlinarith
  have hB2 : Real.exp (a * T) ≤ 2 := by
    calc Real.exp (a * T) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr haT
      _ = 2 := Real.exp_log two_pos
  have hB1 : 1 ≤ Real.exp (a * T) := Real.one_le_exp (by positivity)
  set M := periodMap d T A₁ A₂ with hMdef
  set P := NormedSpace.exp (T • Ab) with hPdef
  have hM : ‖M‖ ≤ Real.exp (a * T) := norm_periodMap_le hd0 hd1 A₁ A₂ hT0.le
  have hP : ‖P‖ ≤ Real.exp (a * T) :=
    (norm_exp_smul_le Ab hT0.le).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAb hT0.le))
  -- the switched block versus the averaged block
  have hBN : Real.exp (a * T) ^ N ≤ K := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (N : ℝ) * T ≤ H + 1 := by linarith
    nlinarith
  have hdiff := hper T ⟨hT0.le, hT1⟩
  have hMP : ‖M ^ N - P ^ N‖ ≤ 1 / 4 := by
    have hNT : (N : ℝ) * T ≤ H + 1 := by linarith
    have hQT : Q * T ≤ 1 / 4 := by
      have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Q + 1)).mp hTc
      nlinarith
    calc ‖M ^ N - P ^ N‖ ≤ N * Real.exp (a * T) ^ N * ‖M - P‖ :=
          norm_pow_sub_pow_le hB1 hM hP N
      _ ≤ N * K * (c * T ^ 2) := by gcongr
      _ = ((N : ℝ) * T) * (K * c * T) := by ring
      _ ≤ (H + 1) * (K * c * T) := by gcongr
      _ = Q * T := by simp only [Q]; ring
      _ ≤ 1 / 4 := hQT
  -- the averaged block contracts by `1/2`
  have hPN : ‖P ^ N‖ ≤ 1 / 2 := by
    have hPN_eq : P ^ N = NormedSpace.exp (((N : ℝ) * T) • Ab) := by
      rw [hPdef, exp_natCast_mul_smul]
    have hsplit := exp_add_smul Ab ((N : ℝ) * T - H) H
    rw [sub_add_cancel] at hsplit
    rw [hPN_eq, hsplit]
    have hr0 : 0 ≤ (N : ℝ) * T - H := by linarith
    have hfirst : ‖NormedSpace.exp (((N : ℝ) * T - H) • Ab)‖ ≤ Real.exp (a * T) :=
      (norm_exp_smul_le Ab hr0).trans (Real.exp_le_exp.mpr (by
        have h1 : ‖Ab‖ * ((N : ℝ) * T - H) ≤ a * ((N : ℝ) * T - H) :=
          mul_le_mul_of_nonneg_right hAb hr0
        have h2 : a * ((N : ℝ) * T - H) ≤ a * T :=
          mul_le_mul_of_nonneg_left (by linarith) ha0
        linarith))
    calc ‖NormedSpace.exp (((N : ℝ) * T - H) • Ab) * NormedSpace.exp (H • Ab)‖
        ≤ ‖NormedSpace.exp (((N : ℝ) * T - H) • Ab)‖ * ‖NormedSpace.exp (H • Ab)‖ :=
          norm_mul_le _ _
      _ ≤ Real.exp (a * T) * (1 / 4) :=
          mul_le_mul hfirst hexp (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ 2 * (1 / 4) := by gcongr
      _ = 1 / 2 := by norm_num
  calc ‖M ^ N‖ = ‖P ^ N + (M ^ N - P ^ N)‖ := by rw [add_sub_cancel]
    _ ≤ ‖P ^ N‖ + ‖M ^ N - P ^ N‖ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 / 4 := add_le_add hPN hMP
    _ = 3 / 4 := by norm_num

/-- **Uniform exponential decay of the switched period map.** If the averaged model contracts
over some horizon (`‖e^{HĀ}‖ < 1`), there are `T₀ ∈ (0, 1]`, `C > 0`, `α > 0` such that for
every switching period `T ∈ (0, T₀]` and every `k`:
`‖(e^{(1−d)TA₂} e^{dTA₁})^k‖ ≤ C e^{−α k T}` (the constants do not depend on `T`). -/
@[powerlib_foundation] theorem exists_periodMap_pow_decay {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : 𝔸) {H : ℝ} (hH : 0 < H)
    (hexp : ‖NormedSpace.exp (H • avgMatrix d A₁ A₂)‖ < 1) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ 1 ∧ ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ T ∈ Ioc (0 : ℝ) T₀, ∀ k : ℕ,
      ‖periodMap d T A₁ A₂ ^ k‖ ≤ C * Real.exp (-(α * (k * T))) := by
  obtain ⟨H', hH', hq⟩ := exists_norm_exp_smul_le_quarter hH hexp
  obtain ⟨T₀, hT₀, hT₀1, hblock⟩ := exists_periodMap_pow_le hd0 hd1 A₁ A₂ hH' hq
  set a := ‖A₁‖ + ‖A₂‖ with hadef
  have ha0 : 0 ≤ a := by positivity
  set γ := Real.log (4 / 3) with hγdef
  have hγ : 0 < γ := Real.log_pos (by norm_num)
  refine ⟨T₀, hT₀, hT₀1, Real.exp (a * (H' + 1)) * Real.exp γ, γ / (H' + 1), by positivity,
    by positivity, fun T hT k => ?_⟩
  obtain ⟨N, hN0, -, hNT, hMN⟩ := hblock T hT
  have hT0 : 0 < T := hT.1
  set M := periodMap d T A₁ A₂ with hMdef
  have hk : k = N * (k / N) + k % N := (Nat.div_add_mod k N).symm
  have hr : k % N < N := Nat.mod_lt k hN0
  have hMk : M ^ k = (M ^ N) ^ (k / N) * M ^ (k % N) := by
    rw [← pow_mul, ← pow_add, ← hk]
  have hMr : ‖M ^ (k % N)‖ ≤ Real.exp (a * (H' + 1)) := by
    calc ‖M ^ (k % N)‖ ≤ ‖M‖ ^ (k % N) := norm_pow_le _ _
      _ ≤ Real.exp (a * T) ^ (k % N) :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_periodMap_le hd0 hd1 A₁ A₂ hT0.le) _
      _ = Real.exp ((k % N : ℕ) * (a * T)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (a * (H' + 1)) := by
          apply Real.exp_le_exp.mpr
          have h1 : ((k % N : ℕ) : ℝ) ≤ N := by exact_mod_cast hr.le
          have h2 : ((k % N : ℕ) : ℝ) * T ≤ H' + 1 :=
            (mul_le_mul_of_nonneg_right h1 hT0.le).trans hNT
          nlinarith
  have hqpow : ‖(M ^ N) ^ (k / N)‖ ≤ Real.exp (-(γ * (k / N : ℕ))) := by
    calc ‖(M ^ N) ^ (k / N)‖ ≤ ‖M ^ N‖ ^ (k / N) := norm_pow_le _ _
      _ ≤ (3 / 4) ^ (k / N) := pow_le_pow_left₀ (norm_nonneg _) hMN _
      _ = Real.exp (-(γ * (k / N : ℕ))) := by
          rw [show -(γ * ((k / N : ℕ) : ℝ)) = ((k / N : ℕ) : ℝ) * (-γ) by ring,
            Real.exp_nat_mul, Real.exp_neg, hγdef, Real.exp_log (by norm_num)]
          norm_num
  have hqk : (k : ℝ) * T / (H' + 1) - 1 ≤ ((k / N : ℕ) : ℝ) := by
    have h1 : k < N * (k / N + 1) := by
      conv_lhs => rw [hk]
      rw [mul_add, mul_one]
      exact Nat.add_lt_add_left hr _
    have h1' : (k : ℝ) < N * (((k / N : ℕ) : ℝ) + 1) := by exact_mod_cast h1
    have h2 : (k : ℝ) * T < (N * T) * (((k / N : ℕ) : ℝ) + 1) := by
      have := mul_lt_mul_of_pos_right h1' hT0
      linarith
    have h3 : (N * T) * (((k / N : ℕ) : ℝ) + 1) ≤ (H' + 1) * (((k / N : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hNT (by positivity)
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    linarith
  calc ‖M ^ k‖ = ‖(M ^ N) ^ (k / N) * M ^ (k % N)‖ := by rw [hMk]
    _ ≤ ‖(M ^ N) ^ (k / N)‖ * ‖M ^ (k % N)‖ := norm_mul_le _ _
    _ ≤ Real.exp (-(γ * (k / N : ℕ))) * Real.exp (a * (H' + 1)) :=
        mul_le_mul hqpow hMr (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (γ + -(γ / (H' + 1) * (k * T))) * Real.exp (a * (H' + 1)) := by
        gcongr
        have h := mul_le_mul_of_nonneg_left hqk hγ.le
        have e : γ * ((k : ℝ) * T / (H' + 1) - 1) = γ / (H' + 1) * (k * T) - γ := by
          field_simp
        linarith
    _ = Real.exp (a * (H' + 1)) * Real.exp γ * Real.exp (-(γ / (H' + 1) * (k * T))) := by
        rw [Real.exp_add]; ring

omit [NormOneClass 𝔸] in
/-- `e^{s(N − ε)} = e^{−εs} (1 + sN)` for a square-zero element `N` (`N² = 0`). -/
@[powerlib_foundation] theorem exp_smul_sqZero_sub_smul_one {N : 𝔸} (hN : N * N = 0)
    (s ε : ℝ) :
    NormedSpace.exp (s • (N - ε • (1 : 𝔸))) = Real.exp (-(ε * s)) • (1 + s • N) := by
  have hsplit : s • (N - ε • (1 : 𝔸)) = s • N + (-(ε * s)) • (1 : 𝔸) := by
    rw [smul_sub, smul_smul, neg_smul, sub_eq_add_neg, mul_comm]
  have hcomm : Commute (s • N) ((-(ε * s)) • (1 : 𝔸)) :=
    ((Commute.one_right N).smul_left s).smul_right _
  have hexp_add : NormedSpace.exp (s • N + (-(ε * s)) • (1 : 𝔸)) =
      NormedSpace.exp (s • N) * NormedSpace.exp ((-(ε * s)) • (1 : 𝔸)) := by
    refine NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm ?_ ?_ <;>
    · rw [NormedSpace.expSeries_radius_eq_top]
      simp
  rw [hsplit, hexp_add]
  have h1 : NormedSpace.exp ((-(ε * s)) • (1 : 𝔸)) = Real.exp (-(ε * s)) • (1 : 𝔸) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
      ← NormedSpace.algebraMap_exp_comm, Real.exp_eq_exp_ℝ]
  have h2 : NormedSpace.exp (s • N) = 1 + s • N := by
    rw [congrFun (NormedSpace.exp_eq_tsum ℝ) (s • N)]
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ]
    · intro k hk
      have hk2 : 2 ≤ k := by simp at hk; omega
      have hsq : (s • N) ^ 2 = 0 := by rw [sq, smul_mul_smul_comm, hN, smul_zero]
      rw [show k = 2 + (k - 2) by omega, pow_add, hsq, zero_mul, smul_zero]
  rw [h1, h2, mul_smul_comm, mul_one]

omit [CompleteSpace 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] in
/-- Telescoping identity `M^k − P^k = Σ_{i<k} M^{k−1−i} (M − P) P^i` (no commutativity). -/
@[powerlib_foundation] theorem pow_sub_pow_eq_sum (M P : 𝔸) (k : ℕ) :
    M ^ k - P ^ k = ∑ i ∈ Finset.range k, M ^ (k - 1 - i) * (M - P) * P ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show k + 1 - 1 - k = 0 by omega, pow_zero, one_mul]
    have h : M ^ (k + 1) - P ^ (k + 1) = M * (M ^ k - P ^ k) + (M - P) * P ^ k := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [h, ih, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega, pow_succ']
    simp only [mul_assoc]

omit [CompleteSpace 𝔸] [NormOneClass 𝔸] in
/-- The averaged matrix of a single topology is itself. -/
@[powerlib_foundation] theorem avgMatrix_self (d : ℝ) (A : 𝔸) : avgMatrix d A A = A := by
  rw [avgMatrix, ← add_smul, add_sub_cancel, one_smul]

omit [NormOneClass 𝔸] in
/-- The period map of a single topology is its exponential over one period. -/
@[powerlib_foundation] theorem periodMap_self (d T : ℝ) (A : 𝔸) :
    periodMap d T A A = NormedSpace.exp (T • A) := by
  rw [periodMap, ← exp_add_smul, show (1 - d) * T + d * T = T by ring]

/-- **Averaging error on the infinite horizon (sampled).** If the averaged model contracts over
some horizon (`‖e^{HĀ}‖ < 1`), there are `T₀ ∈ (0, 1]` and `C` such that for every switching
period `T ∈ (0, T₀]` and **every** `k`: `‖M_T^k − e^{kTĀ}‖ ≤ C T` (the finite-horizon estimate
`stateSpaceAveraging_error` becomes uniform in time). -/
@[powerlib_foundation] theorem exists_periodMap_pow_sub_le {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : 𝔸) {H : ℝ} (hH : 0 < H)
    (hexp : ‖NormedSpace.exp (H • avgMatrix d A₁ A₂)‖ < 1) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Ioc (0 : ℝ) T₀, ∀ k : ℕ,
      ‖periodMap d T A₁ A₂ ^ k - NormedSpace.exp (T • avgMatrix d A₁ A₂) ^ k‖ ≤ C * T := by
  set Ab := avgMatrix d A₁ A₂ with hAbdef
  obtain ⟨T₁, hT₁, hT₁1, C₁, α, hC₁, hα, hdec₁⟩ := exists_periodMap_pow_decay hd0 hd1 A₁ A₂ hH hexp
  obtain ⟨T₂, hT₂, -, C₂, β, hC₂, hβ, hdec₂⟩ :=
    exists_periodMap_pow_decay hd0 hd1 Ab Ab hH (by rwa [avgMatrix_self])
  obtain ⟨c, hc, hper⟩ := periodMap_sub_exp_le hd0 hd1 A₁ A₂
  set γ := min α β with hγdef
  have hγ : 0 < γ := lt_min hα hβ
  refine ⟨min T₁ T₂, lt_min hT₁ hT₂, (min_le_left _ _).trans hT₁1,
    C₁ * C₂ * c * Real.exp γ / γ, by positivity, fun T hT k => ?_⟩
  have hT0 : 0 < T := hT.1
  have hT1 : T ≤ 1 := hT.2.trans ((min_le_left _ _).trans hT₁1)
  have hT₁' : T ∈ Ioc (0 : ℝ) T₁ := ⟨hT0, hT.2.trans (min_le_left _ _)⟩
  have hT₂' : T ∈ Ioc (0 : ℝ) T₂ := ⟨hT0, hT.2.trans (min_le_right _ _)⟩
  set M := periodMap d T A₁ A₂ with hMdef
  set P := NormedSpace.exp (T • Ab) with hPdef
  have hPpow : ∀ i : ℕ, ‖P ^ i‖ ≤ C₂ * Real.exp (-(β * (i * T))) := by
    intro i
    have h := hdec₂ T hT₂' i
    rwa [periodMap_self] at h
  have hMP : ‖M - P‖ ≤ c * T ^ 2 := hper T ⟨hT0.le, hT1⟩
  set B := C₁ * C₂ * (c * T ^ 2) * (Real.exp (γ * T) * Real.exp (-(γ * (k * T)))) with hBdef
  have hterm : ∀ i ∈ Finset.range k, ‖M ^ (k - 1 - i) * (M - P) * P ^ i‖ ≤ B := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hcast : ((k - 1 - i : ℕ) : ℝ) + i + 1 = k := by
      have : k - 1 - i + i + 1 = k := by omega
      exact_mod_cast this
    have hexpo : -(α * (((k - 1 - i : ℕ) : ℝ) * T)) + -(β * (i * T)) ≤
        γ * T + -(γ * (k * T)) := by
      have ha : 0 ≤ ((k - 1 - i : ℕ) : ℝ) * T := by positivity
      have hb : 0 ≤ (i : ℝ) * T := by positivity
      have h1 : γ * (((k - 1 - i : ℕ) : ℝ) * T) ≤ α * (((k - 1 - i : ℕ) : ℝ) * T) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) ha
      have h2 : γ * ((i : ℝ) * T) ≤ β * ((i : ℝ) * T) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hb
      have e : γ * T + -(γ * (k * T)) =
          -(γ * (((k - 1 - i : ℕ) : ℝ) * T)) + -(γ * ((i : ℝ) * T)) := by
        rw [← hcast]; ring
      rw [e]
      linarith
    calc ‖M ^ (k - 1 - i) * (M - P) * P ^ i‖
        ≤ ‖M ^ (k - 1 - i)‖ * ‖M - P‖ * ‖P ^ i‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (C₁ * Real.exp (-(α * (((k - 1 - i : ℕ) : ℝ) * T)))) * (c * T ^ 2) *
            (C₂ * Real.exp (-(β * (i * T)))) := by
          gcongr
          · exact hdec₁ T hT₁' _
          · exact hPpow i
      _ = C₁ * C₂ * (c * T ^ 2) *
            Real.exp (-(α * (((k - 1 - i : ℕ) : ℝ) * T)) + -(β * (i * T))) := by
          rw [Real.exp_add]; ring
      _ ≤ B := by
          rw [hBdef, ← Real.exp_add]
          gcongr
  have hkT : (k : ℝ) * T * Real.exp (-(γ * (k * T))) ≤ 1 / γ := by
    have hy : 0 ≤ (k : ℝ) * T := by positivity
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hγ]
    nlinarith [Real.add_one_le_exp (γ * ((k : ℝ) * T))]
  rw [pow_sub_pow_eq_sum]
  calc ‖∑ i ∈ Finset.range k, M ^ (k - 1 - i) * (M - P) * P ^ i‖
      ≤ ∑ i ∈ Finset.range k, ‖M ^ (k - 1 - i) * (M - P) * P ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range k, B := Finset.sum_le_sum hterm
    _ = k * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = C₁ * C₂ * c * Real.exp (γ * T) * T * ((k : ℝ) * T * Real.exp (-(γ * (k * T)))) := by
        rw [hBdef]; ring
    _ ≤ C₁ * C₂ * c * Real.exp γ * T * (1 / γ) := by
        gcongr
        nlinarith
    _ = C₁ * C₂ * c * Real.exp γ / γ * T := by ring

end Algebra

/-! ## Switched trajectories -/

section Switched

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Stability transfer to switched trajectories** (any finite state index, sup norm). If the
averaged model contracts over some horizon, `‖e^{HĀ}‖ < 1`, there are `T₀ > 0`, `C > 0`,
`α > 0` such that for every switching period `T ∈ (0, T₀]` every switched trajectory decays
exponentially at every instant: `‖x(t)‖ ≤ C e^{−α t} ‖x(0)‖` for `t ≥ 0`. -/
@[powerlib_foundation] theorem switched_decay_of_norm_exp_lt_one [Nonempty X] {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (A₁ A₂ : Matrix X X ℝ) {H : ℝ} (hH : 0 < H)
    (hexp : ‖NormedSpace.exp (H • avgMatrix d A₁ A₂)‖ < 1) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ T ∈ Ioc (0 : ℝ) T₀, ∀ x : ℝ → X → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖ := by
  obtain ⟨T₀, hT₀, hT₀1, C, α, hC, hα, hdec⟩ := exists_periodMap_pow_decay hd0 hd1 A₁ A₂ hH hexp
  obtain ⟨c, hc, hrip⟩ := switched_ripple hd0 hd1 A₁ A₂
  refine ⟨T₀, hT₀, (1 + c) * C * Real.exp α, α, by positivity, hα, fun T hT x hx t ht => ?_⟩
  have hT0 : 0 < T := hT.1
  have hT1 : T ≤ 1 := hT.2.trans hT₀1
  set k := ⌊t / T⌋₊ with hkdef
  have hk1 : (k : ℝ) * T ≤ t := by
    have := Nat.floor_le (div_nonneg ht hT0.le)
    rwa [le_div_iff₀ hT0] at this
  have hk2 : t < ((k : ℝ) + 1) * T := by
    have := Nat.lt_floor_add_one (t / T)
    rwa [div_lt_iff₀ hT0] at this
  have hxk : ‖x (k * T)‖ ≤ C * Real.exp (-(α * (k * T))) * ‖x 0‖ := by
    rw [switched_sample hd0 hd1 hT0.le hx k]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right (hdec T hT k) (norm_nonneg _))
  have hrip' := hrip T ⟨hT0, hT1⟩ x hx k t ⟨hk1, hk2.le⟩
  have hxt : ‖x t‖ ≤ (1 + c) * ‖x (k * T)‖ := by
    calc ‖x t‖ = ‖(x t - x (k * T)) + x (k * T)‖ := by rw [sub_add_cancel]
      _ ≤ ‖x t - x (k * T)‖ + ‖x (k * T)‖ := norm_add_le _ _
      _ ≤ c * T * ‖x (k * T)‖ + ‖x (k * T)‖ := by gcongr
      _ ≤ (1 + c) * ‖x (k * T)‖ := by
          have : c * T ≤ c := by nlinarith
          nlinarith [norm_nonneg (x (k * T))]
  have hexpk : Real.exp (-(α * (k * T))) ≤ Real.exp α * Real.exp (-(α * t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : t ≤ (k : ℝ) * T + 1 := by nlinarith
    nlinarith
  calc ‖x t‖ ≤ (1 + c) * ‖x (k * T)‖ := hxt
    _ ≤ (1 + c) * (C * Real.exp (-(α * (k * T))) * ‖x 0‖) := by gcongr
    _ ≤ (1 + c) * (C * (Real.exp α * Real.exp (-(α * t))) * ‖x 0‖) := by gcongr
    _ = (1 + c) * C * Real.exp α * Real.exp (-(α * t)) * ‖x 0‖ := by ring

/-- **Switched trajectories exist.** For every duty ratio `d ∈ [0, 1]`, switching period `T > 0`
and initial state `x₀` there is a trajectory of the ideal two-topology switched system
(`ẋ = A₁ x` on `[kT, kT + dT]`, `ẋ = A₂ x` on `[kT + dT, (k + 1)T]`) with `x(0) = x₀`; the
statements about every switched trajectory are not vacuous. -/
@[powerlib_foundation] theorem exists_switched_trajectory {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : Matrix X X ℝ) {T : ℝ} (hT : 0 < T) (x₀ : X → ℝ) :
    ∃ x : ℝ → X → ℝ, x 0 = x₀ ∧
      ∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T)) := by
  set M := periodMap d T A₁ A₂ with hMdef
  set Φ : ℝ → Matrix X X ℝ := fun s => if s ≤ d * T then NormedSpace.exp (s • A₁)
    else NormedSpace.exp ((s - d * T) • A₂) * NormedSpace.exp ((d * T) • A₁) with hΦdef
  set x : ℝ → X → ℝ := fun t => Φ (t - ⌊t / T⌋₊ * T) *ᵥ (M ^ ⌊t / T⌋₊ *ᵥ x₀) with hxdef
  have hdT : d * T ≤ T := by nlinarith
  have hΦ0 : Φ 0 = 1 := by
    simp only [hΦdef]
    split_ifs with h
    · simp
    · exact absurd (mul_nonneg hd0 hT.le) h
  have hΦT : Φ T = M := by
    simp only [hΦdef, hMdef, periodMap]
    split_ifs with h
    · have hd : d = 1 := le_antisymm hd1 (by
        by_contra hlt
        nlinarith [not_le.mp hlt])
      subst hd
      simp only [sub_self, zero_mul, zero_smul, NormedSpace.exp_zero, one_mul]
      rfl
    · rw [show T - d * T = (1 - d) * T by ring]
      rfl
  -- on each closed period the trajectory is the period profile applied to the sample
  have hx_eq : ∀ k : ℕ, ∀ t ∈ Icc ((k : ℝ) * T) ((k + 1) * T),
      x t = Φ (t - k * T) *ᵥ (M ^ k *ᵥ x₀) := by
    intro k t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have hfl : ⌊t / T⌋₊ = k := by
        rw [Nat.floor_eq_iff (div_nonneg ((by positivity : (0 : ℝ) ≤ k * T).trans ht.1) hT.le),
          le_div_iff₀ hT, div_lt_iff₀ hT]
        exact ⟨ht.1, hlt⟩
      simp only [hxdef, hfl]
    · have hfl : ⌊t / T⌋₊ = k + 1 := by
        rw [heq, mul_div_assoc, div_self hT.ne', mul_one]
        exact_mod_cast Nat.floor_natCast (k + 1)
      simp only [hxdef, hfl]
      rw [heq, show ((k : ℝ) + 1) * T - (((k + 1 : ℕ) : ℝ) * T) = 0 by push_cast; ring,
        show ((k : ℝ) + 1) * T - k * T = T by ring, hΦ0, hΦT, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, pow_succ']
  refine ⟨x, ?_, fun k => ⟨?_, ?_⟩⟩
  · have h := hx_eq 0 0 ⟨by simp, by simp [hT.le]⟩
    simpa [hΦ0] using h
  · -- ON interval
    have hon : ∀ t ∈ Icc ((k : ℝ) * T) (k * T + d * T),
        x t = NormedSpace.exp ((t - k * T) • A₁) *ᵥ (M ^ k *ᵥ x₀) := by
      intro t ht
      rw [hx_eq k t ⟨ht.1, by nlinarith [ht.2]⟩]
      simp only [hΦdef]
      split_ifs with h
      · rfl
      · exact absurd (show t - k * T ≤ d * T by linarith [ht.2]) h
    intro t ht
    have hy := (hasDerivAt_exp_mulVec A₁ (k * T) (M ^ k *ᵥ x₀) t).hasDerivWithinAt
      (s := Icc ((k : ℝ) * T) (k * T + d * T))
    rw [← hon t ht] at hy
    exact hy.congr (fun s hs => hon s hs) (hon t ht)
  · -- OFF interval
    have hoff : ∀ t ∈ Icc ((k : ℝ) * T + d * T) ((k + 1) * T),
        x t = NormedSpace.exp ((t - (k * T + d * T)) • A₂) *ᵥ
          (NormedSpace.exp ((d * T) • A₁) *ᵥ (M ^ k *ᵥ x₀)) := by
      intro t ht
      rw [hx_eq k t ⟨by nlinarith [ht.1, mul_nonneg hd0 hT.le], ht.2⟩]
      simp only [hΦdef]
      split_ifs with h
      · have h0 : t - (k * T + d * T) = 0 := by linarith [ht.1]
        rw [h0, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec,
          show t - k * T = d * T by linarith [ht.1]]
      · simp only [Matrix.mulVec_mulVec, mul_assoc,
          show t - k * T - d * T = t - (k * T + d * T) by ring]
    intro t ht
    have hy := (hasDerivAt_exp_mulVec A₂ (k * T + d * T)
      (NormedSpace.exp ((d * T) • A₁) *ᵥ (M ^ k *ᵥ x₀)) t).hasDerivWithinAt
      (s := Icc ((k : ℝ) * T + d * T) ((k + 1) * T))
    rw [← hoff t ht] at hy
    exact hy.congr (fun s hs => hoff s hs) (hoff t ht)

/-- **Averaging error on the infinite horizon** (any finite state index, sup norm). If the
averaged model contracts over some horizon (`‖e^{HĀ}‖ < 1`), there are `T₀ > 0` and `C` such that
for every switching period `T ∈ (0, T₀]`, every switched trajectory and **every** instant `t ≥ 0`:
`‖x(t) − e^{tĀ} x(0)‖ ≤ C T ‖x(0)‖` (the horizon of `stateSpaceAveraging_error_uniform` removed). -/
@[powerlib_foundation] theorem switched_averaging_error_of_norm_exp_lt_one [Nonempty X] {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (A₁ A₂ : Matrix X X ℝ) {H : ℝ} (hH : 0 < H)
    (hexp : ‖NormedSpace.exp (H • avgMatrix d A₁ A₂)‖ < 1) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Ioc (0 : ℝ) T₀, ∀ x : ℝ → X → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ t : ℝ, 0 ≤ t →
        ‖x t - NormedSpace.exp (t • avgMatrix d A₁ A₂) *ᵥ x 0‖ ≤ C * T * ‖x 0‖ := by
  set Ab := avgMatrix d A₁ A₂ with hAbdef
  obtain ⟨T₀, hT₀, hT₀1, C₀, hC₀, herr⟩ := exists_periodMap_pow_sub_le hd0 hd1 A₁ A₂ hH hexp
  obtain ⟨T₁, hT₁, hT₁1, C₁, α, hC₁, hα, hdec⟩ := exists_periodMap_pow_decay hd0 hd1 A₁ A₂ hH hexp
  obtain ⟨cr, hcr, hrip⟩ := switched_ripple hd0 hd1 A₁ A₂
  set a := ‖A₁‖ + ‖A₂‖ with hadef
  have ha0 : 0 ≤ a := by positivity
  have hAb : ‖Ab‖ ≤ a := norm_avgMatrix_le hd0 hd1 A₁ A₂
  refine ⟨min T₀ T₁, lt_min hT₀ hT₁, cr * C₁ + C₀ + a * Real.exp a * (C₁ + C₀), by positivity,
    fun T hT x hx t ht => ?_⟩
  have hT0 : 0 < T := hT.1
  have hT1 : T ≤ 1 := hT.2.trans ((min_le_left _ _).trans hT₀1)
  have hT₀' : T ∈ Ioc (0 : ℝ) T₀ := ⟨hT0, hT.2.trans (min_le_left _ _)⟩
  have hT₁' : T ∈ Ioc (0 : ℝ) T₁ := ⟨hT0, hT.2.trans (min_le_right _ _)⟩
  set k := ⌊t / T⌋₊ with hkdef
  have hk1 : (k : ℝ) * T ≤ t := by
    have := Nat.floor_le (div_nonneg ht hT0.le)
    rwa [le_div_iff₀ hT0] at this
  have hk2 : t < ((k : ℝ) + 1) * T := by
    have := Nat.lt_floor_add_one (t / T)
    rwa [div_lt_iff₀ hT0] at this
  set M := periodMap d T A₁ A₂ with hMdef
  set P := NormedSpace.exp (T • Ab) with hPdef
  have hMk : ‖M ^ k‖ ≤ C₁ := by
    refine (hdec T hT₁' k).trans ?_
    have : Real.exp (-(α * (k * T))) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ α * ((k : ℝ) * T) := by positivity
      linarith)
    nlinarith
  have hMPk : ‖M ^ k - P ^ k‖ ≤ C₀ * T := herr T hT₀' k
  have hPk : ‖P ^ k‖ ≤ C₁ + C₀ := by
    calc ‖P ^ k‖ = ‖M ^ k - (M ^ k - P ^ k)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖M ^ k‖ + ‖M ^ k - P ^ k‖ := norm_sub_le _ _
      _ ≤ C₁ + C₀ * T := add_le_add hMk hMPk
      _ ≤ C₁ + C₀ := by nlinarith
  have hPk_eq : NormedSpace.exp (((k : ℝ) * T) • Ab) = P ^ k := exp_natCast_mul_smul Ab T k
  have hsample := switched_sample hd0 hd1 hT0.le hx k
  -- (1) ripple
  have h1 : ‖x t - x (k * T)‖ ≤ cr * C₁ * T * ‖x 0‖ := by
    have hr := hrip T ⟨hT0, hT1⟩ x hx k t ⟨hk1, hk2.le⟩
    have hxk : ‖x (k * T)‖ ≤ C₁ * ‖x 0‖ := by
      rw [hsample]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right hMk (norm_nonneg _))
    calc ‖x t - x (k * T)‖ ≤ cr * T * ‖x (k * T)‖ := hr
      _ ≤ cr * T * (C₁ * ‖x 0‖) := by gcongr
      _ = cr * C₁ * T * ‖x 0‖ := by ring
  -- (2) sampled error
  have h2 : ‖x (k * T) - NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0‖ ≤ C₀ * T * ‖x 0‖ := by
    rw [hsample, hPk_eq, ← Matrix.sub_mulVec]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right hMPk (norm_nonneg _))
  -- (3) averaged model across the partial period
  set s := t - k * T with hsdef
  have hs0 : 0 ≤ s := by simp only [hsdef]; linarith
  have hsT : s ≤ T := by simp only [hsdef]; linarith
  have hsplit : NormedSpace.exp (t • Ab) =
      NormedSpace.exp (s • Ab) * NormedSpace.exp (((k : ℝ) * T) • Ab) := by
    have h := exp_add_smul Ab s ((k : ℝ) * T)
    rw [show s + (k : ℝ) * T = t by simp only [hsdef]; ring] at h
    exact h
  obtain ⟨-, hbs⟩ := exp_smul_bounds hAb hs0 (hsT.trans hT1)
  have h3 : ‖NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0‖ ≤
      a * Real.exp a * (C₁ + C₀) * T * ‖x 0‖ := by
    have e : NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0 =
        -((NormedSpace.exp (s • Ab) - 1) * NormedSpace.exp (((k : ℝ) * T) • Ab)) *ᵥ x 0 := by
      rw [hsplit, Matrix.neg_mulVec, sub_mul, one_mul, Matrix.sub_mulVec]; abel
    rw [e, hPk_eq]
    calc ‖-((NormedSpace.exp (s • Ab) - 1) * P ^ k) *ᵥ x 0‖
        ≤ ‖-((NormedSpace.exp (s • Ab) - 1) * P ^ k)‖ * ‖x 0‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ (a * s * Real.exp a) * (C₁ + C₀) * ‖x 0‖ := by
          rw [norm_neg]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (norm_mul_le _ _).trans (mul_le_mul hbs hPk (norm_nonneg _) (by positivity))
      _ ≤ a * Real.exp a * (C₁ + C₀) * T * ‖x 0‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have : 0 ≤ a * Real.exp a * (C₁ + C₀) := by positivity
          nlinarith
  have hsum : x t - NormedSpace.exp (t • Ab) *ᵥ x 0 =
      (x t - x (k * T)) + (x (k * T) - NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0) +
        (NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0) := by
    abel
  rw [hsum]
  calc ‖(x t - x (k * T)) + (x (k * T) - NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0) +
        (NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0)‖
      ≤ ‖x t - x (k * T)‖ + ‖x (k * T) - NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0‖ +
        ‖NormedSpace.exp (((k : ℝ) * T) • Ab) *ᵥ x 0 - NormedSpace.exp (t • Ab) *ᵥ x 0‖ :=
        norm_add₃_le
    _ ≤ cr * C₁ * T * ‖x 0‖ + C₀ * T * ‖x 0‖ + a * Real.exp a * (C₁ + C₀) * T * ‖x 0‖ := by
        gcongr
    _ = (cr * C₁ + C₀ + a * Real.exp a * (C₁ + C₀)) * T * ‖x 0‖ := by ring

end Switched

/-! ## Hurwitz averaged matrix -/

section Hurwitz

variable {n : ℕ}

/-- A Hurwitz matrix has a contractive exponential block in the `L∞` operator norm. -/
@[powerlib_foundation] theorem exists_norm_exp_lt_one_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) :
    ∃ H : ℝ, 0 < H ∧ ‖NormedSpace.exp (H • A)‖ < 1 := by
  have hρ : spectralRadius ℂ ((NormedSpace.exp A).map (algebraMap ℝ ℂ)) < 1 := by
    rw [MatrixAlgebra.complexification_exp]
    exact LinearSystems.spectralRadius_exp_complexification_lt_one hA
  obtain ⟨m, hm, hlt⟩ := LTI.exists_pow_norm_lt_one (NormedSpace.exp A) hρ
  refine ⟨m, Nat.cast_pos.mpr hm, ?_⟩
  rw [Nat.cast_smul_eq_nsmul ℝ, Matrix.exp_nsmul]
  exact hlt

/-- **Stability transfer, sampled form.** A Hurwitz averaged matrix `Ā = d A₁ + (1 − d) A₂`
makes the switched period map `e^{(1−d)TA₂} e^{dTA₁}` Schur stable for every switching period
`T ∈ (0, T₀]`, with a power of `L∞` operator norm below one. -/
@[powerlib_foundation] theorem periodMap_schurStable_of_isHurwitz {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ)
    (hA : LinearSystems.IsHurwitz (avgMatrix d A₁ A₂)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ∈ Ioc (0 : ℝ) T₀,
      LTI.SchurStable (periodMap d T A₁ A₂) ∧
        ∃ N : ℕ, 0 < N ∧ ‖periodMap d T A₁ A₂ ^ N‖ < 1 := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, one_pos, fun T _ => ⟨fun μ v hv _ => absurd (Subsingleton.elim v 0) hv,
      1, one_pos, ?_⟩⟩
    rw [Subsingleton.elim (periodMap d T A₁ A₂ ^ 1) 0, norm_zero]
    norm_num
  · obtain ⟨H, hH, hexp⟩ := exists_norm_exp_lt_one_of_isHurwitz hA
    obtain ⟨T₀, hT₀, -, C, α, hC, hα, hdec⟩ := exists_periodMap_pow_decay hd0 hd1 A₁ A₂ hH hexp
    refine ⟨T₀, hT₀, fun T hT => ?_⟩
    set M := periodMap d T A₁ A₂ with hMdef
    set ρ := Real.exp (-(α * T)) with hρdef
    have hρ0 : 0 < ρ := Real.exp_pos _
    have hρ1 : ρ < 1 := by
      calc ρ < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith [hT.1])
        _ = 1 := Real.exp_zero
    have hpow : ∀ k : ℕ, ‖M ^ k‖ ≤ C * ρ ^ k := fun k => by
      have h := hdec T hT k
      rwa [show -(α * ((k : ℝ) * T)) = (k : ℝ) * (-(α * T)) by ring, Real.exp_nat_mul] at h
    refine ⟨?_, ?_⟩
    · apply (LTI.exponentiallyStable_iff_schurStable ⟨M⟩).mp
      refine ⟨C, hC, ρ, hρ0.le, hρ1, fun x hx k => ?_⟩
      rw [hx.eq_response k, LTI.response]
      exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (hpow k) (norm_nonneg _))
    · obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC) hρ1
      refine ⟨j + 1, Nat.succ_pos j, ?_⟩
      calc ‖M ^ (j + 1)‖ ≤ C * ρ ^ (j + 1) := hpow _
        _ ≤ C * ρ ^ j :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le (Nat.le_succ j)) hC.le
        _ < C * C⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hC.ne'

/-- **Stability transfer to the switched system** (Hurwitz averaged matrix). If
`Ā = d A₁ + (1 − d) A₂` is Hurwitz, there are `T₀ > 0`, `C > 0`, `α > 0` such that for every
switching period `T ∈ (0, T₀]` every switched trajectory decays exponentially at every instant,
ripple included: `‖x(t)‖ ≤ C e^{−α t} ‖x(0)‖` for all `t ≥ 0`. -/
@[powerlib_foundation] theorem switched_decay_of_isHurwitz {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) (hA : LinearSystems.IsHurwitz (avgMatrix d A₁ A₂)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ T ∈ Ioc (0 : ℝ) T₀,
      ∀ x : ℝ → Fin n → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖ := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, one_pos, 1, 1, one_pos, one_pos, fun T _ x _ t _ => ?_⟩
    rw [Subsingleton.elim (x t) 0, norm_zero]
    positivity
  · obtain ⟨H, hH, hexp⟩ := exists_norm_exp_lt_one_of_isHurwitz hA
    exact switched_decay_of_norm_exp_lt_one hd0 hd1 A₁ A₂ hH hexp

/-- **Averaging error on the infinite horizon** (Hurwitz averaged matrix). If
`Ā = d A₁ + (1 − d) A₂` is Hurwitz, there are `T₀ > 0` and `C` such that for every switching
period `T ∈ (0, T₀]`, every switched trajectory and every `t ≥ 0`:
`‖x(t) − e^{tĀ} x(0)‖ ≤ C T ‖x(0)‖`. -/
@[powerlib_foundation] theorem switched_averaging_error_of_isHurwitz {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ)
    (hA : LinearSystems.IsHurwitz (avgMatrix d A₁ A₂)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Ioc (0 : ℝ) T₀, ∀ x : ℝ → Fin n → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ t : ℝ, 0 ≤ t →
        ‖x t - NormedSpace.exp (t • avgMatrix d A₁ A₂) *ᵥ x 0‖ ≤ C * T * ‖x 0‖ := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, one_pos, 0, le_rfl, fun T _ x _ t _ => ?_⟩
    rw [Subsingleton.elim (x t - NormedSpace.exp (t • avgMatrix d A₁ A₂) *ᵥ x 0) 0, norm_zero]
    simp
  · obtain ⟨H, hH, hexp⟩ := exists_norm_exp_lt_one_of_isHurwitz hA
    exact switched_averaging_error_of_norm_exp_lt_one hd0 hd1 A₁ A₂ hH hexp

/-- **Converse: uniform switched decay forces a Hurwitz average.** If, for some `T₀ > 0`, every
switched trajectory with switching period `T ∈ (0, T₀]` decays as `‖x(t)‖ ≤ C e^{−α t} ‖x(0)‖`
with constants `C`, `α > 0` independent of `T`, then `Ā = d A₁ + (1 − d) A₂` is Hurwitz (the
averaged flow inherits the bound in the limit `T → 0`, through the finite-horizon averaging error
and the existence of switched trajectories). -/
@[powerlib_foundation] theorem isHurwitz_of_switched_decay {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) {T₀ C α : ℝ} (hT₀ : 0 < T₀) (hα : 0 < α)
    (hdec : ∀ T ∈ Ioc (0 : ℝ) T₀, ∀ x : ℝ → Fin n → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖) :
    LinearSystems.IsHurwitz (avgMatrix d A₁ A₂) := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · intro μ v hv _
    exact absurd (Subsingleton.elim v 0) hv
  set Ab := avgMatrix d A₁ A₂ with hAbdef
  -- a horizon `t₁` over which the decay bound is a contraction
  set t₁ := (|C| + 1) / α with ht₁def
  have ht₁ : 0 < t₁ := by positivity
  set q := C * Real.exp (-(α * t₁)) with hqdef
  have hq1 : q < 1 := by
    have hαt : α * t₁ = |C| + 1 := by simp only [ht₁def]; field_simp
    rw [hqdef, hαt, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    have := Real.add_one_le_exp (|C| + 1)
    linarith [le_abs_self C]
  -- the averaged flow over `t₁` inherits the bound
  set E := NormedSpace.exp (t₁ • Ab) with hEdef
  obtain ⟨CL, hCL, herrL⟩ := stateSpaceAveraging_error_uniform hd0 hd1 A₁ A₂ ht₁.le
  have hE : ∀ y : Fin n → ℝ, ‖E *ᵥ y‖ ≤ q * ‖y‖ := by
    intro y
    by_contra hcon
    set δ := ‖E *ᵥ y‖ - q * ‖y‖ with hδdef
    have hδ : 0 < δ := by simp only [hδdef]; linarith [not_le.mp hcon]
    set T := min (min T₀ 1) (δ / (CL * ‖y‖ + 1)) with hTdef
    have hT0 : 0 < T := lt_min (lt_min hT₀ one_pos) (by positivity)
    have hTT₀ : T ≤ T₀ := (min_le_left _ _).trans (min_le_left _ _)
    have hT1 : T ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
    have hTδ : T ≤ δ / (CL * ‖y‖ + 1) := min_le_right _ _
    obtain ⟨x, hx0, hx⟩ := exists_switched_trajectory hd0 hd1 A₁ A₂ hT0 y
    have h1 := hdec T ⟨hT0, hTT₀⟩ x hx t₁ ht₁.le
    have h2 := herrL T ⟨hT0, hT1⟩ x hx t₁ ⟨ht₁.le, le_rfl⟩
    rw [hx0] at h1 h2
    have h3 : CL * T * ‖y‖ < δ := by
      have hy : 0 ≤ CL * ‖y‖ := by positivity
      have h := (le_div_iff₀ (by positivity : (0 : ℝ) < CL * ‖y‖ + 1)).mp hTδ
      nlinarith
    have h4 : ‖E *ᵥ y‖ ≤ ‖x t₁‖ + ‖x t₁ - E *ᵥ y‖ := by
      calc ‖E *ᵥ y‖ = ‖x t₁ - (x t₁ - E *ᵥ y)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x t₁‖ + ‖x t₁ - E *ᵥ y‖ := norm_sub_le _ _
    have h5 : ‖E *ᵥ y‖ < q * ‖y‖ + δ := by
      calc ‖E *ᵥ y‖ ≤ ‖x t₁‖ + ‖x t₁ - E *ᵥ y‖ := h4
        _ ≤ q * ‖y‖ + CL * T * ‖y‖ := add_le_add h1 h2
        _ < q * ‖y‖ + δ := by linarith
    simp only [hδdef] at h5
    linarith
  -- the exponential over `t₁` is Schur stable
  have hS : LTI.SchurStable E := by
    apply (LTI.exponentiallyStable_iff_schurStable ⟨E⟩).mp
    refine ⟨1, one_pos, max q 0, le_max_right _ _, max_lt hq1 one_pos, fun x hx k => ?_⟩
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hx k]
      calc ‖LTI.Model.step ⟨E⟩ (x k)‖ = ‖E *ᵥ x k‖ := rfl
        _ ≤ q * ‖x k‖ := hE (x k)
        _ ≤ max q 0 * ‖x k‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max q 0 * (1 * max q 0 ^ k * ‖x 0‖) :=
            mul_le_mul_of_nonneg_left ih (le_max_right _ _)
        _ = 1 * max q 0 ^ (k + 1) * ‖x 0‖ := by ring
  -- an eigenvalue `μ` of `Ā` gives the eigenvalue `e^{μ t₁}` of `E`
  intro μ v hv hAv
  have heig := Periodic.monodromy_const_mulVec_eigen Ab ht₁.le 0 hAv
  rw [Periodic.monodromy_const Ab ht₁.le] at heig
  have h := hS _ v hv heig
  rw [Periodic.norm_exp_mul_eq] at h
  have hneg : μ.re * t₁ < 0 := by
    by_contra hcon
    have := Real.one_le_exp (not_lt.mp hcon)
    linarith
  have := neg_of_mul_neg_left hneg ht₁.le
  simpa using this

/-- **Exactness of the stability transfer in the fast-switching limit.** The averaged matrix
`Ā = d A₁ + (1 − d) A₂` is Hurwitz iff, for some `T₀ > 0`, every switched trajectory with
switching period `T ∈ (0, T₀]` decays exponentially with constants independent of `T`:
`‖x(t)‖ ≤ C e^{−α t} ‖x(0)‖`, `C, α > 0`. -/
@[powerlib_foundation] theorem isHurwitz_iff_switched_decay {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) :
    LinearSystems.IsHurwitz (avgMatrix d A₁ A₂) ↔
      ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ T ∈ Ioc (0 : ℝ) T₀,
        ∀ x : ℝ → Fin n → ℝ,
        (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
          IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
        ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖ := by
  refine ⟨switched_decay_of_isHurwitz hd0 hd1 A₁ A₂, ?_⟩
  rintro ⟨T₀, hT₀, C, α, -, hα, hdec⟩
  exact isHurwitz_of_switched_decay hd0 hd1 A₁ A₂ hT₀ hα hdec

end Hurwitz

/-! ## Slow switching: a Hurwitz average does not suffice -/

section Counterexample

/-- The slow-switching example: `A₁ = N₁ − εI`, `A₂ = N₂ − εI` with `N₁ = [[0, 1], [0, 0]]`,
`N₂ = [[0, 0], [−1, 0]]`, duty ratio `1/2`: the period map is
`e^{−εT} [[1, T/2], [−T/2, 1 − T²/4]]` (trace `e^{−εT}(2 − T²/4)`, determinant `e^{−2εT}`). -/
@[powerlib_foundation] theorem periodMap_shear_pair (ε T : ℝ) :
    periodMap (1 / 2) T (!![-ε, 1; 0, -ε] : Matrix (Fin 2) (Fin 2) ℝ) !![-ε, 0; -1, -ε] =
      Real.exp (-(ε * T)) • !![1, T / 2; -(T / 2), 1 - T ^ 2 / 4] := by
  have hA₁ : (!![-ε, 1; 0, -ε] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1; 0, 0] - ε • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hA₂ : (!![-ε, 0; -1, -ε] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 0; -1, 0] - ε • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hN₁ : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 0, 0] = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hN₂ : (!![0, 0; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 0; -1, 0] = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold periodMap
  rw [hA₁, hA₂, exp_smul_sqZero_sub_smul_one hN₂, exp_smul_sqZero_sub_smul_one hN₁,
    smul_mul_smul_comm, ← Real.exp_add]
  have e1 : -(ε * ((1 - 1 / 2) * T)) + -(ε * (1 / 2 * T)) = -(ε * T) := by ring
  rw [e1]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

/-- **Slow switching destabilizes a Hurwitz average.** With `ε = 1/10`: both topologies
`A₁ = [[−1/10, 1], [0, −1/10]]`, `A₂ = [[−1/10, 0], [−1, −1/10]]` and their average
`Ā = [[−1/10, 1/2], [−1/2, −1/10]]` (`d = 1/2`) are Hurwitz, but at the switching period `T = 5`
the period map has the real eigenvalue `−4 e^{−1/2}` (modulus `≈ 2.43 > 1`) with eigenvector
`(1, −2)`, so it is not Schur stable. -/
@[powerlib_foundation] theorem slowSwitching_counterexample :
    LinearSystems.IsHurwitz (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    LinearSystems.IsHurwitz (!![-1 / 10, 0; -1, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    LinearSystems.IsHurwitz
      (avgMatrix (1 / 2) (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ)
        !![-1 / 10, 0; -1, -1 / 10]) ∧
    periodMap (1 / 2) 5 (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ)
        !![-1 / 10, 0; -1, -1 / 10] *ᵥ ![1, -2] = (-4 * Real.exp (-1 / 2)) • ![1, -2] ∧
    ¬ LTI.SchurStable (periodMap (1 / 2) 5 (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ)
        !![-1 / 10, 0; -1, -1 / 10]) := by
  have hM := periodMap_shear_pair (1 / 10) 5
  have hneg : (!![-(1 / 10), 1; 0, -(1 / 10)] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-1 / 10, 1; 0, -1 / 10] := by ext i j; fin_cases i <;> fin_cases j <;> norm_num
  have hneg' : (!![-(1 / 10), 0; -1, -(1 / 10)] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-1 / 10, 0; -1, -1 / 10] := by ext i j; fin_cases i <;> fin_cases j <;> norm_num
  rw [hneg, hneg'] at hM
  have heig : periodMap (1 / 2) 5 (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ)
      !![-1 / 10, 0; -1, -1 / 10] *ᵥ ![1, -2] = (-4 * Real.exp (-1 / 2)) • ![1, -2] := by
    rw [hM]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num <;> ring_nf
  refine ⟨?_, ?_, ?_, heig, ?_⟩
  · rw [Criteria.isHurwitz_fin_two_of_iff]; norm_num
  · rw [Criteria.isHurwitz_fin_two_of_iff]; norm_num
  · have hAb : avgMatrix (1 / 2) (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ)
        !![-1 / 10, 0; -1, -1 / 10] = !![-1 / 10, 1 / 2; -1 / 2, -1 / 10] := by
      unfold avgMatrix
      ext i j; fin_cases i <;> fin_cases j <;> norm_num
    rw [hAb, Criteria.isHurwitz_fin_two_of_iff]; norm_num
  · intro hS
    set w : Fin 2 → ℝ := ![1, -2] with hw
    set μr : ℝ := -4 * Real.exp (-1 / 2) with hμr
    have hc : (periodMap (1 / 2) 5 (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ)
        !![-1 / 10, 0; -1, -1 / 10]).map (algebraMap ℝ ℂ) *ᵥ (algebraMap ℝ ℂ ∘ w) =
        (μr : ℂ) • (algebraMap ℝ ℂ ∘ w) := by
      ext i
      rw [← RingHom.map_mulVec, heig]
      simp
    have hv : (algebraMap ℝ ℂ ∘ w) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [hw] at this
    have h1 := hS _ _ hv hc
    have hexp : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
      have := Real.add_one_le_exp (-1 / 2 : ℝ)
      linarith
    have : ‖(μr : ℂ)‖ = 4 * Real.exp (-1 / 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, hμr, abs_mul, abs_of_pos (Real.exp_pos _)]
      norm_num
    rw [this] at h1
    linarith

/-- **Slow switching, trajectory form.** For the example of `slowSwitching_counterexample`
(`A₁ = [[−1/10, 1], [0, −1/10]]`, `A₂ = [[−1/10, 0], [−1, −1/10]]`, `d = 1/2`, `T = 5`; both
topologies and the average Hurwitz) there is a switched trajectory from `(1, −2)` whose samples are
`x(5k) = (−4 e^{−1/2})^k (1, −2)` and grow without bound. -/
@[powerlib_foundation] theorem slowSwitching_unbounded_trajectory :
    ∃ x : ℝ → Fin 2 → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x
          (fun _ y => (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ y)
          (Icc (k * 5) (k * 5 + 1 / 2 * 5)) ∧
        IsIntegralCurveOn x
          (fun _ y => (!![-1 / 10, 0; -1, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ y)
          (Icc (k * 5 + 1 / 2 * 5) ((k + 1) * 5))) ∧
      x 0 = ![1, -2] ∧
      (∀ k : ℕ, x (k * 5) = (-4 * Real.exp (-1 / 2)) ^ k • ![1, -2]) ∧
      ∀ B : ℝ, ∃ k : ℕ, B < ‖x (k * 5)‖ := by
  obtain ⟨-, -, -, heig, -⟩ := slowSwitching_counterexample
  obtain ⟨x, hx0, hx⟩ := exists_switched_trajectory (d := 1 / 2) (by norm_num) (by norm_num)
    (!![-1 / 10, 1; 0, -1 / 10] : Matrix (Fin 2) (Fin 2) ℝ) !![-1 / 10, 0; -1, -1 / 10]
    (T := 5) (by norm_num) ![1, -2]
  set μ : ℝ := -4 * Real.exp (-1 / 2) with hμdef
  have hsamp : ∀ k : ℕ, x (k * 5) = μ ^ k • ![1, -2] := by
    intro k
    rw [switched_sample (by norm_num) (by norm_num) (by norm_num) hx k, hx0]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, heig, smul_smul, pow_succ]
  refine ⟨x, hx, hx0, hsamp, fun B => ?_⟩
  have hμ : 2 ≤ |μ| := by
    have hexp : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
      have := Real.add_one_le_exp (-1 / 2 : ℝ)
      linarith
    rw [hμdef, abs_mul, abs_of_pos (Real.exp_pos _)]
    norm_num
    linarith
  have hv : (1 : ℝ) ≤ ‖(![1, -2] : Fin 2 → ℝ)‖ := by
    have h := norm_le_pi_norm (![1, -2] : Fin 2 → ℝ) 1
    have h1 : ‖(![1, -2] : Fin 2 → ℝ) 1‖ = 2 := by simp
    linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_⟩
  rw [hsamp k, norm_smul, Real.norm_eq_abs, abs_pow]
  calc B < 2 ^ k := hk
    _ ≤ |μ| ^ k := pow_le_pow_left₀ (by norm_num) hμ k
    _ ≤ |μ| ^ k * ‖(![1, -2] : Fin 2 → ℝ)‖ := le_mul_of_one_le_right (by positivity) hv

end Counterexample

end powerlib.Averaging
