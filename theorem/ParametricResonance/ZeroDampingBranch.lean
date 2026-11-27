import theorem.ParametricResonance.SecondOrderClosedForm
import theorem.Periodic.AnalysisLevels
import theorem.Periodic.ForcedRegime

/-! # The undamped two-state 2:1 system: reciprocal multipliers, bounded and subharmonic branches

For the complete two-state system `ẋ = (A₀ + ε Re{A₁ e^{jωt}}) x` with the critical pair
`−εs ± j(ω/2 − εd)` (`TwoToOne.full`) at zero averaged damping `s = 0`, the mean trace vanishes
(`Periodic.Levels.integral_trace_full`), so by Liouville `det M = 1` exactly, for every depth
`ε`: the Floquet multipliers are a reciprocal pair `μ, 1/μ` (`zero_damping_reciprocal`). Either
`|tr M| < 2` and the pair is non-real on the unit circle — every solution bounded, none decaying,
neither Schur stable nor Floquet unstable (`elliptic_monodromy`) — or `|tr M| > 2` and one real
multiplier lies outside the unit circle.

The slow-flow matrix `slowFlowMatrix 0 d (g/2)` has trace `0` and determinant `d² − |g/2|²`: a
centre for `|g| < 2|d|`, a saddle for `|g| > 2|d|`. Since `det Φ_y = 1` for the rotating-frame
monodromy `Φ_y = −M`, `tr Φ_y − 2 = −det(Φ_y − I) = −(ε²T² det M + ε³T mixedDet(M, N₂)) + O(ε⁴)`
(`conservative_trace_bound`, with `Boundary.monodromy_expansion_two`), and the closed form
`mixedDet(M, N₂) = T d |g'|²/(4ω)` at `s = 0` (`SecondOrder.mixedDet_secondTerm_stdForm`,
`g' = SecondOrder.antiPump A`) decides the boundary. For all sufficiently small `ε > 0`
(`zero_damping_trace`):

* `|g| < 2|d|`: `|tr M| < 2` — marginally stable, bounded oscillation (`zero_damping_marginal`);
* `|g| > 2|d|`: `tr M < −2` — a real multiplier `r < −1`, subharmonic (period-doubling)
  instability (`zero_damping_unstable`);
* `|g| = 2|d|`: decided at second order by the sign of `d |g'|²` — positive: marginal, bounded;
  negative: subharmonic instability. Undecided at this order only for `d = 0` (then also `g = 0`
  and the first-order slow flow vanishes) or `g' = 0`.

At `s = 0` the levels L3 (the frozen `A₀` has the eigenvalues `±jΩ`) and L2 (a slow-flow centre)
are marginal and say nothing; L1 adds the decisive information: bounded oscillation, never
asymptotic stability, and instability exactly on the saddle side (and on the boundary side
`d |g'|² < 0`). A consistency remark (not formalized): the undamped Mathieu equation
`ẍ + (Ω² + εaΩ cos ωt) x = 0`, `Ω = ω/2 − εd`, is `TwoToOne.full 0 d ω A ε` with
`A = [[0, 0], [a, 0]]`, `g = ja/2`, `g' = −ja/2`; the verdicts on the boundary `d = ±a/4` agree with
the classical transition curves `δ = 1/4 ± ε'/2 − ε'²/8 + O(ε'³)` (`ω = 1`, `δ = Ω²`, `ε' = εaΩ`).

Scope.
* Generic: real `2 × 2` matrices with `det P = 1` (`elliptic_pow_bounds`, `elliptic_spectrum`,
  `exists_eig_lt_neg_one`); continuous `T`-periodic `A(t)` on `ℝ²` with the transition matrix of
  `theorem/Periodic/Transition.lean` (`elliptic_monodromy`; vectors carry the sup norm);
  families `P(ε) = I + εT M + ε² N + O(ε³)` on `(0, 1]` of determinant one
  (`conservative_trace_bound`, `conservative_jury`).
* Two-state system: `TwoToOne.full 0 d ω A ε` (damping `σ = 0` exactly, detuning
  `ω/2 − Ω = εd`, arbitrary complex modulation `A`, `ω > 0`, `T = 2π/ω`); statements for all
  sufficiently small `ε > 0` except `zero_damping_reciprocal` (every `ε`).
* Generic mathematics; no model family.

Source: the wave-5 question of this library (the full two-state system at zero averaged damping:
the centre side and the boundary are left open by `TwoToOne.averaging_stable` and
`Boundary.full_boundary_decided`, which assume `s > 0`; the saddle side is
`TwoToOne.averaging_unstable`, sharpened here to a real multiplier `r < −1`); Liouville's formula `Periodic.det_monodromy`; the Lyapunov criterion for
Hill-type systems (`|tr M| < 2`: stable, bounded; `|tr M| > 2`: unstable;
Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic Coefficients*; Magnus–Winkler,
*Hill's Equation*); the transition curves of the Mathieu equation (Nayfeh–Mook, *Nonlinear
Oscillations*, Ch. 5); `Periodic.exists_real_eig_of_lt`, `Periodic.mem_spectrum_iff_root`,
`Periodic.sq_norm_eq_det_of_im_ne_zero` of `theorem/Periodic/TwoStateBoundary.lean`.

Results.
* `areaForm_mulVec` — `q(v) = v₀(Pv)₁ − v₁(Pv)₀` satisfies `q(Pv) = det P · q(v)`;
  `elliptic_pow_bounds` — `det P = 1`, `|tr P| < 2`: `m|v|² ≤ |Pⁿv|² ≤ K|v|²`;
  `elliptic_spectrum` — the eigenvalues are non-real with `|μ| = 1`.
* `elliptic_monodromy` — elliptic monodromy: multipliers on the unit circle, not Schur stable, not
  Floquet unstable, `‖Φ(t, 0) v‖ ≤ K‖v‖` for `t ≥ 0`, `‖Φ(nT, 0) v‖ ≥ c‖v‖`.
* `conservative_trace_bound` — `|tr P − 2 + ε²T² det M + ε³T mixedDet(M, N)| ≤ C'ε⁴` for families
  of determinant one; `conservative_jury` — the four verdicts by `det M` and, on `det M = 0`, by
  `mixedDet(M, N)`.
* `exists_eig_lt_neg_one` — `det P = 1`, `tr P < −2`: a real eigenvalue `r < −1`.
* `zero_damping_reciprocal` — `det M = 1` and reciprocal multipliers, every `ε`;
  `zero_damping_trace` — the trace verdicts; `zero_damping_marginal`, `zero_damping_unstable` —
  the two branches and their boundary decision.

Corrections.
None: an extension (the branch `s = 0` excluded by the first-order criterion).

Family and connection conclusions.
None: static evidence on periodic linear systems.
-/

noncomputable section
namespace powerlib.ParametricResonance.ZeroDamping

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator
open Boundary (secondTerm mixedDet)

/-! ## Real `2 × 2` matrices of determinant one -/

section Elliptic

variable {P : Matrix (Fin 2) (Fin 2) ℝ}

/-- The area form `q(v) = v₀ (Pv)₁ − v₁ (Pv)₀` of `v` and `Pv` is multiplied by `det P` when
`v` is replaced by `Pv`. -/
@[tmio T, powerlib_foundation] theorem areaForm_mulVec (P : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Fin 2 → ℝ) :
    (P *ᵥ v) 0 * (P *ᵥ (P *ᵥ v)) 1 - (P *ᵥ v) 1 * (P *ᵥ (P *ᵥ v)) 0 =
      P.det * (v 0 * (P *ᵥ v) 1 - v 1 * (P *ᵥ v) 0) := by
  simp [mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

/-- **Elliptic matrices have bounded, non-decaying powers.** For a real `2 × 2` matrix with
`det P = 1` and `|tr P| < 2` there are `m, K > 0` with
`m |v|² ≤ |Pⁿ v|² ≤ K |v|²` (Euclidean norm) for every `n` and `v`: the area form
`q(v) = v₀ (Pv)₁ − v₁ (Pv)₀` is invariant (`areaForm_mulVec`) and definite, since its
discriminant is `(tr P)² − 4 det P < 0`. -/
@[tmio T, powerlib_foundation] theorem elliptic_pow_bounds (hdet : P.det = 1)
    (htr : |P.trace| < 2) :
    ∃ m K : ℝ, 0 < m ∧ 0 < K ∧ ∀ (n : ℕ) (v : Fin 2 → ℝ),
      m * (v 0 ^ 2 + v 1 ^ 2) ≤ (P ^ n *ᵥ v) 0 ^ 2 + (P ^ n *ᵥ v) 1 ^ 2 ∧
        (P ^ n *ᵥ v) 0 ^ 2 + (P ^ n *ᵥ v) 1 ^ 2 ≤ K * (v 0 ^ 2 + v 1 ^ 2) := by
  have hd : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 1 := by rw [← hdet, det_fin_two]
  have hτ : (P 0 0 + P 1 1) ^ 2 < 4 := by
    rw [← trace_fin_two P]
    have := abs_lt.mp htr
    nlinarith
  set a := P 0 0
  set b := P 0 1
  set c := P 1 0
  set e := P 1 1
  set δ := 4 - (a + e) ^ 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hbc : b * c < 0 := by nlinarith [sq_nonneg (a - e)]
  have hb : b ≠ 0 := by rintro h; rw [h, zero_mul] at hbc; exact lt_irrefl _ hbc
  have hc : c ≠ 0 := by rintro h; rw [h, mul_zero] at hbc; exact lt_irrefl _ hbc
  set q : (Fin 2 → ℝ) → ℝ := fun w => c * w 0 ^ 2 + (e - a) * w 0 * w 1 - b * w 1 ^ 2 with hq
  have hqP : ∀ w, q (P *ᵥ w) = q w := by
    intro w
    simp only [hq, mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (c * w 0 ^ 2 + (e - a) * w 0 * w 1 - b * w 1 ^ 2) * hd
  have hqn : ∀ (n : ℕ) w, q (P ^ n *ᵥ w) = q w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih => intro w; rw [pow_succ', ← Matrix.mulVec_mulVec, hqP, ih]
  -- `δ |w|² ≤ 4(c − b) q(w)`
  have hlow : ∀ w : Fin 2 → ℝ, δ * (w 0 ^ 2 + w 1 ^ 2) ≤ 4 * (c - b) * q w := by
    intro w
    have h1 : 4 * c * q w = (2 * c * w 0 + (e - a) * w 1) ^ 2 + δ * w 1 ^ 2 := by
      simp only [hq, hδ]; linear_combination (4 * w 1 ^ 2) * hd
    have h2 : -(4 * b) * q w = (2 * b * w 1 - (e - a) * w 0) ^ 2 + δ * w 0 ^ 2 := by
      simp only [hq, hδ]; linear_combination (4 * w 0 ^ 2) * hd
    nlinarith [sq_nonneg (2 * c * w 0 + (e - a) * w 1), sq_nonneg (2 * b * w 1 - (e - a) * w 0)]
  -- `|q(w)| ≤ L |w|²`
  set L := |c| + |e - a| + |b| with hL
  have hL0 : 0 < L := by
    have := abs_pos.mpr hc
    positivity
  have hup : ∀ w : Fin 2 → ℝ, |q w| ≤ L * (w 0 ^ 2 + w 1 ^ 2) := by
    intro w
    have h01 : |w 0 * w 1| ≤ w 0 ^ 2 + w 1 ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|w 0| - |w 1|), sq_abs (w 0), sq_abs (w 1), abs_nonneg (w 0),
        abs_nonneg (w 1)]
    calc |q w| ≤ |c * w 0 ^ 2| + |(e - a) * w 0 * w 1| + |b * w 1 ^ 2| := by
          simp only [hq]
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |c| * w 0 ^ 2 + |e - a| * |w 0 * w 1| + |b| * w 1 ^ 2 := by
          rw [abs_mul c, abs_mul b, abs_sq, abs_sq, mul_assoc (e - a), abs_mul (e - a)]
      _ ≤ |c| * (w 0 ^ 2 + w 1 ^ 2) + |e - a| * (w 0 ^ 2 + w 1 ^ 2) +
            |b| * (w 0 ^ 2 + w 1 ^ 2) := by
          gcongr
          · nlinarith [sq_nonneg (w 1)]
          · nlinarith [sq_nonneg (w 0)]
      _ = L * (w 0 ^ 2 + w 1 ^ 2) := by rw [hL]; ring
  set κ := 4 * |c - b| * L with hκ
  have hcb : c - b ≠ 0 := by
    intro h
    have : c = b := by linarith
    rw [this] at hbc
    nlinarith [sq_nonneg b]
  have hκ0 : 0 < κ := by
    have := abs_pos.mpr hcb
    positivity
  have hqb : ∀ w, 4 * (c - b) * q w ≤ κ * (w 0 ^ 2 + w 1 ^ 2) := by
    intro w
    have h := hup w
    calc 4 * (c - b) * q w = 4 * ((c - b) * q w) := by ring
      _ ≤ 4 * |(c - b) * q w| := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ = 4 * |c - b| * |q w| := by rw [abs_mul]; ring
      _ ≤ 4 * |c - b| * (L * (w 0 ^ 2 + w 1 ^ 2)) := by gcongr
      _ = κ * (w 0 ^ 2 + w 1 ^ 2) := by rw [hκ]; ring
  refine ⟨δ / κ, κ / δ, by positivity, by positivity, fun n v => ⟨?_, ?_⟩⟩
  · have h1 := hlow v
    have h2 := hqb (P ^ n *ᵥ v)
    rw [hqn] at h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hκ0]
    nlinarith
  · have h1 := hlow (P ^ n *ᵥ v)
    have h2 := hqb v
    rw [hqn] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
    nlinarith

@[tmio T, powerlib_foundation] private theorem sup_norm_sq_le (v : Fin 2 → ℝ) :
    ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 ∧ v 0 ^ 2 + v 1 ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  have h0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
  constructor
  · have hle : ‖v‖ ≤ √(v 0 ^ 2 + v 1 ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      fin_cases i
      · simp only [Fin.zero_eta]; nlinarith [sq_nonneg (v 1)]
      · simp only [Fin.mk_one]; nlinarith [sq_nonneg (v 0)]
    calc ‖v‖ ^ 2 ≤ √(v 0 ^ 2 + v 1 ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = v 0 ^ 2 + v 1 ^ 2 := Real.sq_sqrt (by positivity)
  · have a0 : v 0 ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
    have a1 : v 1 ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    linarith

/-- An elliptic `2 × 2` matrix (`det P = 1`, `|tr P| < 2`): every eigenvalue is non-real and on
the unit circle. -/
@[tmio T, powerlib_foundation] theorem elliptic_spectrum (hdet : P.det = 1) (htr : |P.trace| < 2)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) : ‖μ‖ = 1 ∧ μ.im ≠ 0 := by
  have hτ : P.trace ^ 2 < 4 := by
    have := abs_lt.mp htr
    nlinarith
  have him : μ.im ≠ 0 := by
    intro h
    have hroot := Periodic.mem_spectrum_iff_root.mp hμ
    have hre := congrArg Complex.re hroot
    simp [pow_two, Complex.mul_re, h] at hre
    nlinarith [sq_nonneg (2 * μ.re - P.trace)]
  refine ⟨?_, him⟩
  have h := Periodic.sq_norm_eq_det_of_im_ne_zero hμ him
  rw [hdet] at h
  have h0 := norm_nonneg μ
  nlinarith [sq_nonneg (‖μ‖ - 1)]

/-- An elliptic `2 × 2` matrix has an eigenvalue: `μ = (tr P + j√(4 − tr² P))/2`. -/
@[tmio T, powerlib_foundation] private theorem elliptic_exists_eig (hdet : P.det = 1)
    (htr : |P.trace| < 2) : ∃ μ : ℂ, μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) := by
  have hτ : P.trace ^ 2 < 4 := by
    have := abs_lt.mp htr
    nlinarith
  set y := √(4 - P.trace ^ 2) with hy
  have hy2 : y ^ 2 = 4 - P.trace ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨⟨P.trace / 2, y / 2⟩, Periodic.mem_spectrum_iff_root.mpr ?_⟩
  rw [hdet]
  apply Complex.ext
  · simp [pow_two]
    nlinarith
  · simp [pow_two]
    ring

/-- **Elliptic monodromy: bounded, non-decaying solutions.** For a continuous `T`-periodic
`A(t)` on `ℝ²` whose monodromy matrix has `det M = 1` and `|tr M| < 2`: every Floquet multiplier
is non-real with `|μ| = 1`; the monodromy is not Schur stable and the system is not Floquet
unstable; every solution is bounded on `t ≥ 0`, uniformly (`‖Φ(t, 0) v‖ ≤ K ‖v‖`), and no nonzero
solution decays (`‖Φ(nT, 0) v‖ ≥ c ‖v‖`). -/
@[tmio T, powerlib_foundation] theorem elliptic_monodromy {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {T : ℝ} (hA : Continuous A) (hP : Function.Periodic A T) (hT : 0 < T)
    (hdet : (Periodic.monodromy A T 0).det = 1) (htr : |(Periodic.monodromy A T 0).trace| < 2) :
    (∀ μ ∈ spectrum ℂ ((Periodic.monodromy A T 0).map (algebraMap ℝ ℂ)), ‖μ‖ = 1 ∧ μ.im ≠ 0) ∧
      ¬ LTI.SchurStable (Periodic.monodromy A T 0) ∧ ¬ Periodic.FloquetUnstable A T ∧
      (∃ K, ∀ t, 0 ≤ t → ∀ v : Fin 2 → ℝ, ‖Periodic.transition A t 0 *ᵥ v‖ ≤ K * ‖v‖) ∧
      ∃ c > 0, ∀ (n : ℕ) (v : Fin 2 → ℝ), c * ‖v‖ ≤ ‖Periodic.transition A (n * T) 0 *ᵥ v‖ := by
  set Mo := Periodic.monodromy A T 0 with hMo
  have hspec := fun μ (hμ : μ ∈ spectrum ℂ (Mo.map (algebraMap ℝ ℂ))) =>
    elliptic_spectrum hdet htr hμ
  obtain ⟨m, K, hm, hK, hbd⟩ := elliptic_pow_bounds hdet htr
  obtain ⟨B, hB⟩ := Periodic.exists_bound_of_periodic hA hP hT
  -- powers of the monodromy in the sup norm
  have hpow_up : ∀ (n : ℕ) (v : Fin 2 → ℝ), ‖Mo ^ n *ᵥ v‖ ≤ √(2 * K) * ‖v‖ := by
    intro n v
    have h1 := (sup_norm_sq_le (Mo ^ n *ᵥ v)).1
    have h2 := (hbd n v).2
    have h3 := (sup_norm_sq_le v).2
    have h4 : ‖Mo ^ n *ᵥ v‖ ^ 2 ≤ (√(2 * K) * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4
  have hpow_low : ∀ (n : ℕ) (v : Fin 2 → ℝ), √(m / 2) * ‖v‖ ≤ ‖Mo ^ n *ᵥ v‖ := by
    intro n v
    have h1 := (sup_norm_sq_le v).1
    have h2 := (hbd n v).1
    have h3 := (sup_norm_sq_le (Mo ^ n *ᵥ v)).2
    have h4 : (√(m / 2) * ‖v‖) ^ 2 ≤ ‖Mo ^ n *ᵥ v‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h4
  -- `Φ(t + nT, 0) = Φ(t, 0) Mⁿ`
  have hshift : ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      Periodic.transition A (t + n * T) 0 = Periodic.transition A t 0 * Mo ^ n := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ n ih =>
      intro t ht
      have h := Periodic.transition_add_period_eq_mul hA hP hT (t := t + n * T)
        (by positivity)
      rw [show t + ((n + 1 : ℕ) : ℝ) * T = t + n * T + T by push_cast; ring, h, ih t ht,
        Matrix.mul_assoc, ← pow_succ]
  refine ⟨hspec, ?_, ?_, ?_, ?_⟩
  · intro hS
    obtain ⟨μ, hμ⟩ := elliptic_exists_eig hdet htr
    obtain ⟨v, hv, hμv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
    have := hS μ v hv hμv
    rw [(hspec μ hμ).1] at this
    exact lt_irrefl _ this
  · rintro ⟨μ, hμ, h1⟩
    rw [(hspec μ hμ).1] at h1
    exact lt_irrefl _ h1
  · set D := ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * Real.exp (Real.toNNReal B * T) with hD
    refine ⟨D * √(2 * K), fun t ht v => ?_⟩
    set n := ⌊t / T⌋₊ with hn
    have hn1 : (n : ℝ) * T ≤ t := by
      have := Nat.floor_le (div_nonneg ht hT.le)
      rw [← hn] at this
      calc (n : ℝ) * T ≤ t / T * T := by gcongr
        _ = t := by field_simp
    have hn2 : t < (n : ℝ) * T + T := by
      have := Nat.lt_floor_add_one (t / T)
      rw [← hn] at this
      calc t = t / T * T := by field_simp
        _ < ((n : ℝ) + 1) * T := by gcongr
        _ = n * T + T := by ring
    set t' := t - n * T with ht'
    have ht'0 : 0 ≤ t' := by rw [ht']; linarith
    have hΦ : Periodic.transition A t 0 = Periodic.transition A t' 0 * Mo ^ n := by
      rw [← hshift n t' ht'0, ht', sub_add_cancel]
    have hbt : ‖Periodic.transition A t' 0‖ ≤ D := by
      refine (Periodic.norm_transition_le hB ht'0).trans ?_
      rw [hD, sub_zero]
      gcongr
      linarith
    rw [hΦ, ← Matrix.mulVec_mulVec]
    calc ‖Periodic.transition A t' 0 *ᵥ (Mo ^ n *ᵥ v)‖
        ≤ ‖Periodic.transition A t' 0‖ * ‖Mo ^ n *ᵥ v‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ D * (√(2 * K) * ‖v‖) := by gcongr; exact hpow_up n v
      _ = D * √(2 * K) * ‖v‖ := by ring
  · refine ⟨√(m / 2), by positivity, fun n v => ?_⟩
    have h := Periodic.transition_add_nat_mul_period hA hB hT.le hP 0 n
    rw [zero_add] at h
    rw [h]
    exact hpow_low n v

end Elliptic

/-! ## Families of determinant one: the trace to third order -/

section Conservative

@[tmio T, powerlib_foundation] private theorem abs_det_le (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.det| ≤ 2 * ‖Z‖ ^ 2 := by
  rw [Matrix.det_fin_two]
  have h : ∀ i j k l, |Z i j * Z k l| ≤ ‖Z‖ ^ 2 := fun i j k l => by
    rw [abs_mul, sq]
    exact mul_le_mul (Averaging.entry_le_norm Z i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  calc |Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0| ≤ |Z 0 0 * Z 1 1| + |Z 0 1 * Z 1 0| := abs_sub _ _
    _ ≤ 2 * ‖Z‖ ^ 2 := by linarith [h 0 0 1 1, h 0 1 1 0]

@[tmio T, powerlib_foundation] private theorem abs_mixedDet_le' (M Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |mixedDet M Z| ≤ 4 * (‖M‖ * ‖Z‖) := by
  have e : mixedDet M Z = M 0 0 * Z 1 1 + M 1 1 * Z 0 0 - M 0 1 * Z 1 0 - M 1 0 * Z 0 1 := by
    simp [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h : ∀ i j k l, |M i j * Z k l| ≤ ‖M‖ * ‖Z‖ := fun i j k l => by
    rw [abs_mul]
    exact mul_le_mul (Averaging.entry_le_norm M i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  rw [e]
  have a1 := abs_le.mp (h 0 0 1 1)
  have a2 := abs_le.mp (h 1 1 0 0)
  have a3 := abs_le.mp (h 0 1 1 0)
  have a4 := abs_le.mp (h 1 0 0 1)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

/-- **The trace of a family of determinant one, to third order.** If
`P(ε) = I + εT M + ε² N + O(ε³)` (`‖·‖ ≤ C ε³` on `(0, 1]`) and `det P(ε) = 1`, then
`tr P(ε) − 2 = −det(P(ε) − I) = −(ε² T² det M + ε³ T mixedDet(M, N)) + O(ε⁴)`, with the explicit
constant `2(‖N‖ + C)² + 4T‖M‖C`. -/
@[tmio T, powerlib_foundation] theorem conservative_trace_bound
    {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M N : Matrix (Fin 2) (Fin 2) ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hC : 0 ≤ C) (hP : ∀ ε, 0 < ε → ε ≤ 1 → ‖P ε - 1 - (ε * T) • M - ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (hdet : ∀ ε, 0 < ε → ε ≤ 1 → (P ε).det = 1) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      |(P ε).trace - 2 + (T ^ 2 * M.det * ε ^ 2 + T * mixedDet M N * ε ^ 3)| ≤
        (2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C) * ε ^ 4 := by
  intro ε h0 h1
  set R := P ε - 1 - (ε * T) • M - ε ^ 2 • N with hR
  have hRb : ‖R‖ ≤ C * ε ^ 3 := hP ε h0 h1
  have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
  set Z := ε ^ 2 • N + R with hZ
  have hY : P ε - 1 = (ε * T) • M + Z := by rw [hZ, hR]; abel
  -- `det(I + Y) = 1 + tr Y + det Y`
  have h1Y : (P ε).det = 1 + (P ε - 1).trace + (P ε - 1).det := by
    have h := Boundary.det_add_fin_two 1 (P ε - 1)
    rw [add_sub_cancel, Matrix.det_one] at h
    rw [h]
    simp [mixedDet, Matrix.trace_fin_two]
    ring
  have htrY : (P ε).trace - 2 = (P ε - 1).trace := by
    rw [Matrix.trace_sub, Matrix.trace_one]; norm_num
  have hdY : (P ε - 1).det = (ε * T) ^ 2 * M.det + Z.det +
      ε * T * (ε ^ 2 * mixedDet M N + mixedDet M R) := by
    rw [hY, Boundary.det_add_fin_two, Matrix.det_smul, Fintype.card_fin, hZ]
    simp [mixedDet, Matrix.trace_add, Matrix.trace_smul, Matrix.mul_add]
    ring
  have hZb : ‖Z‖ ≤ (‖N‖ + C) * ε ^ 2 := by
    calc ‖Z‖ ≤ ‖ε ^ 2 • N‖ + ‖R‖ := norm_add_le _ _
      _ = ε ^ 2 * ‖N‖ + ‖R‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ε ^ 2 * ‖N‖ + C * ε ^ 2 := by
          gcongr; exact hRb.trans (mul_le_mul_of_nonneg_left hε3 hC)
      _ = (‖N‖ + C) * ε ^ 2 := by ring
  have hdZ : |Z.det| ≤ 2 * (‖N‖ + C) ^ 2 * ε ^ 4 := by
    calc |Z.det| ≤ 2 * ‖Z‖ ^ 2 := abs_det_le Z
      _ ≤ 2 * ((‖N‖ + C) * ε ^ 2) ^ 2 := by gcongr
      _ = 2 * (‖N‖ + C) ^ 2 * ε ^ 4 := by ring
  have hmR : |ε * T * mixedDet M R| ≤ 4 * T * ‖M‖ * C * ε ^ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε * T)]
    calc ε * T * |mixedDet M R| ≤ ε * T * (4 * (‖M‖ * (C * ε ^ 3))) := by
          gcongr
          exact (abs_mixedDet_le' M R).trans (by gcongr)
      _ = 4 * T * ‖M‖ * C * ε ^ 4 := by ring
  have e : (P ε).trace - 2 + (T ^ 2 * M.det * ε ^ 2 + T * mixedDet M N * ε ^ 3) =
      -(Z.det + ε * T * mixedDet M R) := by
    rw [htrY]
    have : (P ε - 1).trace = -(P ε - 1).det := by rw [hdet ε h0 h1] at h1Y; linarith
    rw [this, hdY]
    ring
  rw [e, abs_neg]
  calc |Z.det + ε * T * mixedDet M R| ≤ |Z.det| + |ε * T * mixedDet M R| := abs_add_le _ _
    _ ≤ 2 * (‖N‖ + C) ^ 2 * ε ^ 4 + 4 * T * ‖M‖ * C * ε ^ 4 := add_le_add hdZ hmR
    _ = (2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C) * ε ^ 4 := by ring

/-- **Conservative Jury conditions.** For a family `P(ε) = I + εT M + ε² N + O(ε³)` of real
`2 × 2` matrices of determinant one (`T > 0`), for all small `ε > 0`:
* `det M > 0` gives `|tr P(ε)| < 2` (elliptic: multipliers `e^{±jθ}`);
* `det M < 0` gives `tr P(ε) > 2` (hyperbolic: real multipliers `r > 1 > 1/r`);
* on `det M = 0`: `mixedDet(M, N) > 0` gives `|tr P(ε)| < 2`, `mixedDet(M, N) < 0` gives
  `tr P(ε) > 2`. -/
@[tmio T, powerlib_foundation] theorem conservative_jury {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ε ≤ 1 → ‖P ε - 1 - (ε * T) • M - ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (hdet : ∀ ε, 0 < ε → ε ≤ 1 → (P ε).det = 1) :
    (0 < M.det → ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(P ε).trace| < 2) ∧
      (M.det < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 < (P ε).trace) ∧
      (M.det = 0 → 0 < mixedDet M N → ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(P ε).trace| < 2) ∧
      (M.det = 0 → mixedDet M N < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 < (P ε).trace) := by
  set K := 2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C with hK
  have hK0 : 0 ≤ K := by positivity
  have hb := conservative_trace_bound hT.le hC hP hdet
  set a := T ^ 2 * M.det
  set b := T * mixedDet M N
  -- `tr P + 2 > 0` for small `ε`
  have hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (P ε).trace + 2 := by
    refine Averaging.eventually_pos_of_bound (b := 4) (C := |a| + |b| + K) 0 (by norm_num)
      (by positivity) fun ε h0 h1 => ?_
    have h := hb ε h0 h1
    have e1 : ε ^ 4 ≤ ε := by
      calc ε ^ 4 ≤ ε ^ 1 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
        _ = ε := pow_one ε
    have e2 : ε ^ 3 ≤ ε := by
      calc ε ^ 3 ≤ ε ^ 1 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
        _ = ε := pow_one ε
    have e3 : ε ^ 2 ≤ ε := by
      calc ε ^ 2 ≤ ε ^ 1 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
        _ = ε := pow_one ε
    have ha : |a * ε ^ 2| ≤ |a| * ε := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]; gcongr
    have hb' : |b * ε ^ 3| ≤ |b| * ε := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 3)]; gcongr
    have hKε : K * ε ^ 4 ≤ K * ε := by gcongr
    rw [pow_zero, mul_one, zero_add, pow_one]
    have e : (P ε).trace + 2 - 4 = ((P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)) - a * ε ^ 2 -
        b * ε ^ 3 := by ring
    rw [e]
    calc |((P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)) - a * ε ^ 2 - b * ε ^ 3|
        ≤ |(P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)| + |a * ε ^ 2| + |b * ε ^ 3| :=
          (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K * ε + |a| * ε + |b| * ε := by linarith
      _ = (|a| + |b| + K) * ε := by ring
  refine ⟨fun hM => ?_, fun hM => ?_, fun hM0 hm => ?_, fun hM0 hm => ?_⟩
  · have h := Averaging.eventually_pos_of_bound (h := fun ε => 2 - (P ε).trace) (b := a)
      (C := |b| + K) 2 (by positivity) (by positivity) fun ε h0 h1 => by
        have h := hb ε h0 h1
        have e4 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
        have hb' : |b * ε ^ 3| = |b| * ε ^ 3 := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 3)]
        have e : 2 - (P ε).trace - a * ε ^ 2 =
            -((P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)) + b * ε ^ 3 := by ring
        rw [e]
        calc |-((P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)) + b * ε ^ 3|
            ≤ |(P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)| + |b * ε ^ 3| := by
              rw [← abs_neg ((P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3))]; exact abs_add_le _ _
          _ ≤ K * ε ^ 3 + |b| * ε ^ 3 := by
              rw [hb']; gcongr; exact h.trans (by gcongr)
          _ = (|b| + K) * ε ^ (2 + 1) := by ring
    filter_upwards [h, hlow] with ε h1 h2
    rw [abs_lt]; constructor <;> linarith
  · have hpos : 0 < -a := by
      have : 0 < T ^ 2 := by positivity
      simp only [a]; nlinarith
    have h := Averaging.eventually_pos_of_bound (h := fun ε => (P ε).trace - 2) (b := -a)
      (C := |b| + K) 2 hpos (by positivity) fun ε h0 h1 => by
        have h := hb ε h0 h1
        have e4 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
        have hb' : |b * ε ^ 3| = |b| * ε ^ 3 := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 3)]
        have e : (P ε).trace - 2 - -a * ε ^ 2 =
            ((P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)) - b * ε ^ 3 := by ring
        rw [e]
        calc |((P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)) - b * ε ^ 3|
            ≤ |(P ε).trace - 2 + (a * ε ^ 2 + b * ε ^ 3)| + |b * ε ^ 3| := abs_sub _ _
          _ ≤ K * ε ^ 3 + |b| * ε ^ 3 := by
              rw [hb']; gcongr; exact h.trans (by gcongr)
          _ = (|b| + K) * ε ^ (2 + 1) := by ring
    filter_upwards [h] with ε h1
    linarith
  · have ha0 : a = 0 := by simp only [a, hM0, mul_zero]
    have h := Averaging.eventually_pos_of_bound (h := fun ε => 2 - (P ε).trace) (b := b)
      (C := K) 3 (by positivity) hK0 fun ε h0 h1 => by
        have h := hb ε h0 h1
        rw [ha0, zero_mul, zero_add] at h
        have e : 2 - (P ε).trace - b * ε ^ 3 = -((P ε).trace - 2 + b * ε ^ 3) := by ring
        rw [e, abs_neg]
        exact h
    filter_upwards [h, hlow] with ε h1 h2
    rw [abs_lt]; constructor <;> linarith
  · have ha0 : a = 0 := by simp only [a, hM0, mul_zero]
    have h := Averaging.eventually_pos_of_bound (h := fun ε => (P ε).trace - 2) (b := -b)
      (C := K) 3 (by nlinarith) hK0 fun ε h0 h1 => by
        have h := hb ε h0 h1
        rw [ha0, zero_mul, zero_add] at h
        have e : (P ε).trace - 2 - -b * ε ^ 3 = (P ε).trace - 2 + b * ε ^ 3 := by ring
        rw [e]
        exact h
    filter_upwards [h] with ε h1
    linarith

end Conservative

/-! ## The undamped two-state 2:1 system -/

section Full

open TwoToOne (full stdForm left right)
open SecondOrder (antiPump)

/-- A real `2 × 2` matrix with `det P = 1` and `tr P < −2` has a real eigenvalue `r < −1` (and
`1/r ∈ (−1, 0)`). -/
@[tmio T, powerlib_foundation] theorem exists_eig_lt_neg_one {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : P.det = 1) (htr : P.trace < -2) :
    ∃ r : ℝ, r < -1 ∧ (r : ℂ) ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) := by
  obtain ⟨r, hr, hr1⟩ := Periodic.exists_real_eig_of_lt (P := P)
    (by rw [hdet, abs_of_neg (by linarith)]; linarith)
  have hroot := Periodic.mem_spectrum_iff_root.mp hr
  have hre := congrArg Complex.re hroot
  simp [pow_two, hdet] at hre
  have hneg : r < 0 := by nlinarith [sq_nonneg r]
  refine ⟨r, ?_, hr⟩
  rw [abs_of_neg hneg] at hr1
  linarith

/-- **Undamped: the multipliers are a reciprocal pair, at every depth.** For `s = 0` the mean
trace of `TwoToOne.full 0 d ω A ε` vanishes (`Periodic.Levels.integral_trace_full`), so by
Liouville `det M = 1` for every `ε`; every multiplier `μ` is nonzero and `1/μ` is a multiplier too.
-/
@[tmio T, powerlib_foundation] theorem zero_damping_reciprocal (d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).det = 1 ∧
      ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)), μ ≠ 0 ∧
          μ⁻¹ ∈ spectrum ℂ ((Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).map
            (algebraMap ℝ ℂ)) := by
  have hdet : (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).det = 1 := by
    rw [Periodic.det_monodromy (TwoToOne.continuous_full 0 d ω A ε)
      (TwoToOne.periodic_full 0 d hω.ne' A ε) 0, Periodic.Levels.integral_trace_full 0 d hω A ε]
    simp
  refine ⟨hdet, fun μ hμ => ?_⟩
  have hroot := Periodic.mem_spectrum_iff_root.mp hμ
  rw [hdet] at hroot
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hroot
  refine ⟨hμ0, Periodic.mem_spectrum_iff_root.mpr ?_⟩
  rw [hdet]
  have e : μ⁻¹ ^ 2 - ((Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace : ℂ) *
      μ⁻¹ + ((1 : ℝ) : ℂ) = μ⁻¹ ^ 2 * (μ ^ 2 - ((Periodic.monodromy (full 0 d ω A ε)
        (2 * Real.pi / ω) 0).trace : ℂ) * μ + ((1 : ℝ) : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [e, hroot, mul_zero]

/-- **The trace verdicts of the undamped system.** For `TwoToOne.full 0 d ω A ε` (no damping,
detuning `ω/2 − Ω = εd`, pump `g = Element.pump A left right`, anti-resonant pump
`g' = SecondOrder.antiPump A`), monodromy `Φ` over `T = 2π/ω`, for all small `ε > 0`:
* `|g/2|² < d²` (slow flow a centre): `|tr Φ| < 2`;
* `d² < |g/2|²` (slow flow a saddle): `tr Φ < −2`;
* on the boundary `d² = |g/2|²`: `d |g'|² > 0` gives `|tr Φ| < 2`, `d |g'|² < 0` gives `tr Φ < −2`.
Through `Φ = −Φ_y` and `det Φ_y = 1`, `tr Φ_y − 2 = −(ε² T² det M + ε³ T mixedDet(M, N₂)) + O(ε⁴)`
with `det M = d² − |g/2|²` and `mixedDet(M, N₂) = T d |g'|²/(4ω)`
(`SecondOrder.mixedDet_secondTerm_stdForm`). -/
@[tmio T, powerlib_foundation] theorem zero_damping_trace {d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (‖Element.pump A left right / 2‖ ^ 2 < d ^ 2 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        |(Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace| < 2) ∧
      (d ^ 2 < ‖Element.pump A left right / 2‖ ^ 2 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace < -2) ∧
      (d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2 → 0 < d * ‖antiPump A‖ ^ 2 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          |(Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace| < 2) ∧
      (d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2 → d * ‖antiPump A‖ ^ 2 < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace < -2) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set g := Element.pump A left right with hg
  set F := stdForm 0 d ω A with hF
  set Mb := slowFlowMatrix 0 d (g / 2) with hMb
  set N₂ := secondTerm F T with hN₂
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm 0 d hω A
  have havg : ∫ r in (0 : ℝ)..T, F r = T • Mb := TwoToOne.integral_stdForm 0 d hω A
  have hFc : Continuous F := TwoToOne.continuous_stdForm 0 d ω A
  set Py : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun ε => Periodic.monodromy (fun t => ε • F t) T 0
    with hPy
  have hmono : ∀ ε, Periodic.monodromy (full 0 d ω A ε) T 0 = -Py ε := fun ε =>
    TwoToOne.monodromy_full 0 d hω A ε
  have htrace : ∀ ε, (Periodic.monodromy (full 0 d ω A ε) T 0).trace = -(Py ε).trace :=
    fun ε => by rw [hmono, Matrix.trace_neg]
  have hdetPy : ∀ ε, 0 < ε → ε ≤ 1 → (Py ε).det = 1 := fun ε _ _ => by
    have h := (zero_damping_reciprocal d hω A ε).1
    rw [hmono, Matrix.det_neg, Fintype.card_fin] at h
    simpa using h
  set K₂ := MF * T * (MF * T * (MF * T * (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * Real.exp (MF * T))))
    with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hexp : ∀ ε, 0 < ε → ε ≤ 1 → ‖Py ε - 1 - (ε * T) • Mb - ε ^ 2 • N₂‖ ≤ K₂ * ε ^ 3 :=
    fun ε h0 h1 => by
      have h := Boundary.monodromy_expansion_two (F := F) hFc hMF hMF0 hT.le havg h0.le h1
      rw [← hK₂] at h
      calc _ ≤ ε ^ 3 * K₂ := h
        _ = K₂ * ε ^ 3 := mul_comm _ _
  have hdetM : Mb.det = d ^ 2 - ‖g / 2‖ ^ 2 := by
    rw [hMb, det_slowFlowMatrix]; ring
  have hmix : mixedDet Mb N₂ = T / (4 * ω) * (d * ‖antiPump A‖ ^ 2) := by
    rw [hMb, hN₂, hF, SecondOrder.mixedDet_secondTerm_stdForm 0 d hω A]
    ring
  have hc : 0 < T / (4 * ω) := by positivity
  obtain ⟨j1, j2, j3, j4⟩ := conservative_jury (P := Py) hT hK₂0 hexp hdetPy
  refine ⟨fun h => ?_, fun h => ?_, fun hb h => ?_, fun hb h => ?_⟩
  · filter_upwards [j1 (by rw [hdetM]; linarith)] with ε hε
    rwa [htrace, abs_neg]
  · filter_upwards [j2 (by rw [hdetM]; linarith)] with ε hε
    rw [htrace]; linarith
  · filter_upwards [j3 (by rw [hdetM]; linarith) (by rw [hmix]; positivity)] with ε hε
    rwa [htrace, abs_neg]
  · filter_upwards [j4 (by rw [hdetM]; linarith) (by rw [hmix]; exact mul_neg_of_pos_of_neg hc h)]
      with ε hε
    rw [htrace]; linarith

/-- **Undamped, slow-flow centre (or boundary with `d |g'|² > 0`): marginally stable.** For
`TwoToOne.full 0 d ω A ε` with `|g| < 2|d|`, or `|g| = 2|d|` and `d |g'|² > 0`, for all small
`ε > 0`: every Floquet multiplier is non-real on the unit circle, the monodromy is neither Schur
stable nor Floquet unstable, every solution is bounded on `t ≥ 0` and no nonzero solution
decays. Small-signal (frozen `A₀`, eigenvalues `±jΩ`) and averaged verdicts are "marginal";
the Floquet level confirms it: bounded oscillation, not asymptotic stability. -/
@[tmio T, powerlib_foundation] theorem zero_damping_marginal {d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ‖Element.pump A left right / 2‖ ^ 2 < d ^ 2 ∨
      (d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2 ∧ 0 < d * ‖antiPump A‖ ^ 2)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), ‖μ‖ = 1 ∧ μ.im ≠ 0) ∧
        ¬ LTI.SchurStable (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0) ∧
        ¬ Periodic.FloquetUnstable (full 0 d ω A ε) (2 * Real.pi / ω) ∧
        (∃ K, ∀ t, 0 ≤ t → ∀ v : Fin 2 → ℝ,
          ‖Periodic.transition (full 0 d ω A ε) t 0 *ᵥ v‖ ≤ K * ‖v‖) ∧
        ∃ c > 0, ∀ (n : ℕ) (v : Fin 2 → ℝ),
          c * ‖v‖ ≤ ‖Periodic.transition (full 0 d ω A ε) (n * (2 * Real.pi / ω)) 0 *ᵥ v‖ := by
  obtain ⟨t1, -, t3, -⟩ := zero_damping_trace (d := d) hω A
  have htr : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |(Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace| < 2 := by
    rcases h with h | ⟨hb, h⟩
    · exact t1 h
    · exact t3 hb h
  filter_upwards [htr] with ε hε
  exact elliptic_monodromy (TwoToOne.continuous_full 0 d ω A ε)
    (TwoToOne.periodic_full 0 d hω.ne' A ε) (by positivity)
    (zero_damping_reciprocal d hω A ε).1 hε

/-- **Undamped, slow-flow saddle (or boundary with `d |g'|² < 0`): subharmonic instability.** For
`TwoToOne.full 0 d ω A ε` with `|g| > 2|d|`, or `|g| = 2|d|` and `d |g'|² < 0`, for all small
`ε > 0` there is a real multiplier `r < −1` (its reciprocal is the other one): Floquet unstable,
the growing mode antiperiodic up to its envelope (frequency `ω/2`). -/
@[tmio T, powerlib_foundation] theorem zero_damping_unstable {d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : d ^ 2 < ‖Element.pump A left right / 2‖ ^ 2 ∨
      (d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2 ∧ d * ‖antiPump A‖ ^ 2 < 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ r : ℝ, r < -1 ∧ (r : ℂ) ∈ spectrum ℂ
          ((Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ))) ∧
        Periodic.FloquetUnstable (full 0 d ω A ε) (2 * Real.pi / ω) := by
  obtain ⟨-, t2, -, t4⟩ := zero_damping_trace (d := d) hω A
  have htr : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (Periodic.monodromy (full 0 d ω A ε) (2 * Real.pi / ω) 0).trace < -2 := by
    rcases h with h | ⟨hb, h⟩
    · exact t2 h
    · exact t4 hb h
  filter_upwards [htr] with ε hε
  obtain ⟨r, hr, hspec⟩ := exists_eig_lt_neg_one (zero_damping_reciprocal d hω A ε).1 hε
  refine ⟨⟨r, hr, hspec⟩, r, hspec, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  linarith

end Full

end powerlib.ParametricResonance.ZeroDamping
