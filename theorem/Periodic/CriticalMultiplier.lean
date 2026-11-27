import theorem.Map.Linearization
import theorem.Dynamics.CriticalLinearization
import theorem.Dynamics.Instability
import theorem.NormalForm.Scalar
import theorem.ParametricResonance.ResonantNormalForm

/-! # Critical Floquet multipliers: the step from L1 to L0 at `max |μ| = 1`

The multipliers of the linearization along a periodic solution decide its nonlinear stability
when none lies on the unit circle (`Periodic.exp_stable_of_floquet` inside,
`Periodic.unstable_of_floquet` outside). At `max |μ| = 1` they do not: systems with the same
linearization along the same periodic solution can be asymptotically stable or unstable, for each
critical type (`μ = +1`, `μ = −1`, and complex pairs `e^{±iθ}` through a general rotation). At this
codimension-one boundary the verdict is
carried by the Poincaré (period) map beyond its linear part: for a one-dimensional map
`P(x) = μ x + …` with `μ = ±1` it is decided by the first nonlinear coefficient that survives
the normal-form reduction —

* `P(x) = x + a x² + O(x³)`, `a ≠ 0` (fold / transcritical type): unstable;
* `P(x) = x + b x³ + O(x⁴)` (pitchfork type): asymptotically stable for `b < 0`, unstable for
  `b > 0`;
* `P(x) = −x + a x² + b x³ + O(x⁴)` (flip, period doubling): `P∘P(x) = x − 2(a² + b) x³ + O(x⁴)`,
  so the fixed point is asymptotically stable for `a² + b > 0` and unstable for `a² + b < 0`
  (with `a = 0`: stable for `b > 0`, unstable for `b < 0`).

Even when the critical fixed point is stable, it is never exponentially stable: a derivative with
an eigenvalue `|μ| ≥ 1` excludes the geometric estimate. So at the boundary the linear level still
decides *exponential* stability (negatively) but not *asymptotic* stability.

Scope.
* Maps: the map semantics of `theorem/Map/Defs.lean` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`
  (`Map.LyapunovStable`, `Map.LocalAsymptoticStable`, `Map.LocallyExponentiallyStable`,
  `Map.Unstable`). The normal forms are maps `F : ℝ¹ → ℝ¹` with fixed point `0`, written in the
  coordinate `y 0`, with explicit remainder hypotheses
  `|F y 0 − (normal form)| ≤ K |y 0|^k` for `‖y‖ ≤ ρ` (`k = 3` or `4`); no smoothness beyond
  these bounds is assumed. A Poincaré map restricted to a one-dimensional centre direction is such a
  map; the centre-manifold reduction is not formalized here (for a scalar periodic ODE no
  reduction is needed, and only `μ = +1` occurs there, since `μ = e^{∫ ∂ₓG} > 0`); it is
  `theorem/Map/CenterManifold.lean` and `theorem/Map/CenterReduction.lean`.
* Flows: autonomous fields on `ℝⁿ` read as `T`-periodic systems for every `T`, with LeanForControl's
  segment semantics (`LyapunovStable`, `LocalAsymptoticStable`, `Unstable`) and
  `Flow.GloballyAsymptoticallyStable`. The pairs are `ẋ = S x ∓ κ ‖x‖² x` (`rotCubicField`) with
  a skew-symmetric `S`, the cubic field `Dynamics.cubicField` plus a rotation; the periodic
  solution is the equilibrium `0`, its linearization `J(t) ≡ S` for both members of a pair, its
  monodromy `e^{TS}`. The case `S = 0` is the zero-Jacobian pair of
  `Dynamics.linearization_inconclusive` (multiplier `+1` for every `T`); `S = (ω/2) J₂` on `ℝ²` with
  `T = 2π/ω` has the monodromy `−I` (multiplier `−1`, through
  `ParametricResonance.NormalForm.monodromy_nf`).
* A genuinely nonconstant periodic orbit with a simple critical multiplier and a stable
  complement is not treated here; for the multiplier `−1` it is reduced to the scalar flip map by
  the centre manifold of the period map in `theorem/Periodic/FlipReduction.lean`
  (`localAsymptoticStable_of_flipCoeff_pos`, `unstable_of_flipCoeff_neg`; the regularity of the
  period map and `DP = monodromy` are hypotheses there, derived from a `C⁴` field in
  `theorem/Periodic/FlipOrbit.lean`). The multiplier `+1` of a periodic solution of a periodic
  (non-autonomous) system is reduced in `theorem/Periodic/FoldReduction.lean` and
  `theorem/Periodic/FoldOrbit.lean` (fold coefficient `a ≠ 0`: unstable; `a = 0`: the cubic
  coefficient decides); for autonomous orbits `+1` is trivial (`autonomous_trivial_multiplier`).

Source: the wave-4 question of this library (the boundary cases that the assumption levels L0–L3
leave undecided: critical Floquet multipliers at the step L1 → L0); Kuznetsov, *Elements of
Applied Bifurcation Theory* (3rd ed.), Ch. 4 (fold and flip bifurcations of fixed points of maps;
the flip coefficient `(f_xx/2)² + f_xxx/6`, here `a² + b`); work-sync
`theory/T-small-signal-stability.md` §1.6 (`σ_i = 0` is critical: the linearization does not
decide), cited by
`Dynamics.linearization_inconclusive`; `theorem/Periodic/OrbitalInstability.lean` (Scope: "the
boundary case `max |μ| = 1` is not decided by the linearization and is not treated").

Results.
* Map criteria (any `n`): `Map.localAsymptoticStable_of_norm_le_sub_pow` — a slow contraction
  `‖F y − x‖ ≤ ‖y − x‖ − c ‖y − x‖^m` near `x` gives local asymptotic stability;
  `Map.unstable_of_add_pow_le` — a discrete Chetaev function growing additively,
  `V(F y) ≥ V y + c (V y)^m` where `V > 0`, bounded near `x` and positive arbitrarily close to it,
  gives instability; `Map.unstable_of_norm_add_pow_le` — its norm form.
* Iterates: `Map.LyapunovStable.iterate`, `Map.Unstable.of_iterate`,
  `Map.LocalAsymptoticStable.of_iterate` (local asymptotic stability of `F^[m]` and a local linear
  bound on `F` give it for `F`).
* `Map.not_locallyExponentiallyStable_of_eigenvector` — a derivative with a real eigenvalue
  `|μ| ≥ 1` excludes local exponential stability; `Map.critical_not_locallyExponentiallyStable` —
  a map on `ℝ¹` with `F y = μ y + O(y²)`, `|μ| = 1`, is not locally exponentially stable.
* Normal forms on `ℝ¹`: `Map.cubic_localAsymptoticStable` (`y + b y³ + O(y⁴)`, `b < 0`),
  `Map.cubic_unstable` (`b > 0`), `Map.quadratic_unstable` (`y + a y² + O(y³)`, `a ≠ 0`),
  `Map.flip_second_iterate` (`F∘F(y) = y − 2(a² + b) y³ + O(y⁴)`, constant `16 N⁵`,
  `N = 1 + |a| + |b| + |K|`), `Map.flip_localAsymptoticStable` (`−y + a y² + b y³ + O(y⁴)`,
  `a² + b > 0`), `Map.flip_unstable` (`a² + b < 0`).
* Flows: `rotCubicField`, `contDiff_rotCubicField` (`C^k` for every `k`),
  `hasFDerivAt_rotCubicField` (the linearization at `0` is `S` whatever `κ`),
  `inner_op_self_of_skew`, `lie_norm_sq_rotCubicField` (`d‖x‖²/dt = 2κ‖x‖⁴` for skew `S`),
  `rotCubic_globallyAsymptoticallyStable` (`Sᵀ = −S`, `κ < 0`), `rotCubic_unstable` (`κ > 0`),
  `rotCubic_not_locallyExponentiallyStable` (`S` not Hurwitz).
* Multipliers: `eq_of_mem_spectrum_smul_one`, `critical_smul_one` (a monodromy `c I`, `|c| = 1`, is
  neither Schur stable nor has a multiplier outside the unit circle), `monodromy_half_rotation`
  (`J ≡ (ω/2) J₂`, `T = 2π/ω`: monodromy `−I`), `half_rotation_skew`.
* The pairs: `critical_plus_undecided` (`μ = +1`, `J ≡ 0` on `ℝⁿ`) and `critical_minus_undecided`
  (`μ = −1`, `J ≡ (ω/2) J₂` on `ℝ²`): smooth fields with the same linearization along the same
  periodic solution, every multiplier on the unit circle, one member globally asymptotically but
  not exponentially stable and the other unstable.
* `norm_eq_one_of_mem_spectrum_skew` — for every skew `S` and `T ≥ 0` every multiplier of
  `J ≡ S` has modulus one (`e^{TS}` is orthogonal), so the theorems on `rotCubicField` give the
  same undecided pair for every critical type a rotation produces, complex pairs `e^{±iθ}`
  included.

Corrections.
None: an extension (the boundary `max |μ| = 1` of the multiplier criterion and its decision by the
Poincaré-map normal form).

Family and connection conclusions.
None: static evidence on maps and autonomous fields.
-/

noncomputable section

namespace powerlib.Map

open Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Slow contraction and additive escape -/

/-- **Slow contraction gives local asymptotic stability.** If near `x` every step shortens the
distance to `x` by at least `c ‖y − x‖^m` (`c > 0`, `m ≥ 1`), then `x` is locally asymptotically
stable: the distances decrease to a limit `L` with `L ≤ L − c L^m`, so `L = 0`. The contraction
need not be geometric (`m > 1` is the critical case). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_norm_le_sub_pow {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} {r c : ℝ} {m : ℕ} (hr : 0 < r) (hc : 0 < c) (hm : m ≠ 0)
    (h : ∀ y, ‖y - x‖ < r → ‖F y - x‖ ≤ ‖y - x‖ - c * ‖y - x‖ ^ m) :
    LocalAsymptoticStable F x := by
  have hstep : ∀ y, ‖y - x‖ < r → ‖F y - x‖ ≤ ‖y - x‖ := fun y hy => by
    have := mul_nonneg hc.le (pow_nonneg (norm_nonneg (y - x)) m)
    linarith [h y hy]
  have horb : ∀ y, ‖y - x‖ < r → ∀ k : ℕ, ‖F^[k] y - x‖ ≤ ‖y - x‖ := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hstep _ (ih.trans_lt hy)).trans ih
  refine ⟨fun ε hε => ⟨min ε r, lt_min hε hr, fun y hy k =>
    (horb y (hy.trans_le (min_le_right _ _)) k).trans_lt (hy.trans_le (min_le_left _ _))⟩,
    r, hr, fun y hy => ?_⟩
  set d : ℕ → ℝ := fun k => ‖F^[k] y - x‖ with hd
  have hdr : ∀ k, d k < r := fun k => (horb y hy k).trans_lt hy
  have hanti : Antitone d := antitone_nat_of_succ_le fun k => by
    simp only [hd, Function.iterate_succ_apply']
    exact hstep _ (hdr k)
  have hbdd : BddBelow (Set.range d) := ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ k, d k with hLdef
  have hL0 : 0 ≤ L := le_ciInf fun k => norm_nonneg _
  have hlim1 : Tendsto (fun k => d (k + 1)) atTop (𝓝 L) := hlim.comp (tendsto_add_atTop_nat 1)
  have hlim2 : Tendsto (fun k => d k - c * d k ^ m) atTop (𝓝 (L - c * L ^ m)) :=
    hlim.sub ((hlim.pow m).const_mul c)
  have hle : L ≤ L - c * L ^ m := le_of_tendsto_of_tendsto' hlim1 hlim2 fun k => by
    simp only [hd, Function.iterate_succ_apply']
    exact h _ (hdr k)
  have hLm : L ^ m = 0 := by
    have := pow_nonneg hL0 m
    have : c * L ^ m ≤ 0 := by linarith
    nlinarith
  have hL : L = 0 := (pow_eq_zero_iff hm).mp hLm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [hL] at hlim
  exact hlim

/-- **A discrete Chetaev function with additive growth gives instability.** `V` is bounded by `B`
within distance `r` of `x`, takes positive values arbitrarily close to `x`, and wherever it is
positive within distance `r` one step raises it by at least `c (V y)^m` (`c > 0`). Then `x` is
unstable: an orbit kept within distance `r` would have `V ≥ V y + k c (V y)^m → ∞`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_add_pow_le {F : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    {V : ℝⁿ → ℝ} {r c B : ℝ} {m : ℕ} (hr : 0 < r) (hc : 0 < c)
    (hB : ∀ y, ‖y - x‖ < r → V y ≤ B)
    (hgrow : ∀ y, ‖y - x‖ < r → 0 < V y → V y + c * V y ^ m ≤ V (F y))
    (hseed : ∀ δ > 0, ∃ y, ‖y - x‖ < δ ∧ 0 < V y) : Unstable F x := by
  intro hLS
  obtain ⟨δ, hδ, hb⟩ := hLS r hr
  obtain ⟨y, hy, hV⟩ := hseed δ hδ
  have hin : ∀ k, ‖F^[k] y - x‖ < r := hb y hy
  have hpos : 0 < c * V y ^ m := mul_pos hc (pow_pos hV m)
  have hgr : ∀ k : ℕ, V y + k * (c * V y ^ m) ≤ V (F^[k] y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hVk : V y ≤ V (F^[k] y) := by nlinarith
      have hpow : V y ^ m ≤ V (F^[k] y) ^ m := pow_le_pow_left₀ hV.le hVk m
      have := hgrow _ (hin k) (hV.trans_le hVk)
      push_cast
      nlinarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((B - V y) / (c * V y ^ m))
  rw [div_lt_iff₀ hpos] at hk
  have := hgr k
  have := hB _ (hin k)
  linarith

/-- **Additive growth of the distance gives instability** (`n > 0`): if near `x` every step
lengthens the distance to `x` by at least `c ‖y − x‖^m`, then `x` is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_norm_add_pow_le (hn : 0 < n) {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} {r c : ℝ} {m : ℕ} (hr : 0 < r) (hc : 0 < c)
    (h : ∀ y, ‖y - x‖ < r → ‖y - x‖ + c * ‖y - x‖ ^ m ≤ ‖F y - x‖) : Unstable F x := by
  refine unstable_of_add_pow_le (V := fun y => ‖y - x‖) (B := r) hr hc (fun y hy => hy.le)
    (fun y hy _ => h y hy) fun δ hδ => ?_
  let e : ℝⁿ := EuclideanSpace.single ⟨0, hn⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  have hnorm : ‖x + (δ / 2) • e - x‖ = δ / 2 := by
    rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
  refine ⟨x + (δ / 2) • e, ?_, ?_⟩
  · rw [hnorm]; linarith
  · show 0 < ‖x + (δ / 2) • e - x‖
    rw [hnorm]; linarith

/-! ## Iterates -/

/-- Lyapunov stability passes to every iterate. -/
@[tmio T, powerlib_foundation] theorem LyapunovStable.iterate {F : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (h : LyapunovStable F x) (m : ℕ) : LyapunovStable (F^[m]) x := fun ε hε => by
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  exact ⟨δ, hδ, fun y hy k => by rw [← Function.iterate_mul]; exact hb y hy _⟩

/-- Instability of an iterate gives instability of the map. -/
@[tmio T, powerlib_foundation] theorem Unstable.of_iterate {F : ℝⁿ → ℝⁿ} {x : ℝⁿ} {m : ℕ}
    (h : Unstable (F^[m]) x) : Unstable F x := fun hs => h (hs.iterate m)

/-- **Local asymptotic stability of an iterate gives that of the map**, when one step of the map
is bounded linearly near the point (`‖F y − x‖ ≤ C ‖y − x‖`): fewer than `m` steps then move the
orbit by a bounded factor, between two visits at multiples of `m`. -/
@[tmio T, powerlib_foundation] theorem LocalAsymptoticStable.of_iterate {F : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    {m : ℕ} (hm : 0 < m) {r C : ℝ} (hr : 0 < r)
    (hlin : ∀ y, ‖y - x‖ < r → ‖F y - x‖ ≤ C * ‖y - x‖) (h : LocalAsymptoticStable (F^[m]) x) :
    LocalAsymptoticStable F x := by
  set C' := max C 1 with hC'
  have hC1 : 1 ≤ C' := le_max_right _ _
  have hC0 : 0 < C' := lt_of_lt_of_le one_pos hC1
  have hCm : 0 < C' ^ m := pow_pos hC0 m
  have hgrow : ∀ z, ‖z - x‖ < r / C' ^ m → ∀ j, j ≤ m → ‖F^[j] z - x‖ ≤ C' ^ j * ‖z - x‖ := by
    intro z hz j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' := ih (Nat.le_of_succ_le hj)
      have hlt : ‖F^[j] z - x‖ < r := by
        calc ‖F^[j] z - x‖ ≤ C' ^ j * ‖z - x‖ := hj'
          _ ≤ C' ^ m * ‖z - x‖ := mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ hC1 (Nat.le_of_succ_le hj)) (norm_nonneg _)
          _ < C' ^ m * (r / C' ^ m) := by gcongr
          _ = r := by field_simp
      rw [Function.iterate_succ_apply']
      calc ‖F (F^[j] z) - x‖ ≤ C * ‖F^[j] z - x‖ := hlin _ hlt
        _ ≤ C' * ‖F^[j] z - x‖ := by gcongr; exact le_max_left _ _
        _ ≤ C' * (C' ^ j * ‖z - x‖) := by gcongr
        _ = C' ^ (j + 1) * ‖z - x‖ := by ring
  have hsplit : ∀ y (k : ℕ), F^[k] y = F^[k % m] ((F^[m])^[k / m] y) := by
    intro y k
    rw [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.mod_add_div]
  have hsmall : ∀ ε > 0, ∀ z, ‖z - x‖ < min (r / C' ^ m) (ε / C' ^ m) → ∀ j, j < m →
      ‖F^[j] z - x‖ < ε := by
    intro ε hε z hz j hj
    calc ‖F^[j] z - x‖ ≤ C' ^ j * ‖z - x‖ := hgrow z (hz.trans_le (min_le_left _ _)) j hj.le
      _ ≤ C' ^ m * ‖z - x‖ := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hC1 hj.le) (norm_nonneg _)
      _ < C' ^ m * (ε / C' ^ m) := by gcongr; exact hz.trans_le (min_le_right _ _)
      _ = ε := by field_simp
  obtain ⟨hLS, c, hc, hatt⟩ := h
  refine ⟨fun ε hε => ?_, c, hc, fun y hy => ?_⟩
  · have hε' : 0 < min (r / C' ^ m) (ε / C' ^ m) := lt_min (div_pos hr hCm) (div_pos hε hCm)
    obtain ⟨δ, hδ, hb⟩ := hLS _ hε'
    exact ⟨δ, hδ, fun y hy k => by
      rw [hsplit]; exact hsmall ε hε _ (hb y hy _) _ (Nat.mod_lt k hm)⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have hε' : 0 < min (r / C' ^ m) (ε / C' ^ m) := lt_min (div_pos hr hCm) (div_pos hε hCm)
    obtain ⟨Q, hQ⟩ := Metric.tendsto_atTop.mp (hatt y hy) _ hε'
    refine ⟨m * Q, fun k hk => ?_⟩
    rw [dist_eq_norm, hsplit]
    have hq : Q ≤ k / m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hk)
    have := hQ (k / m) hq
    rw [dist_eq_norm] at this
    exact hsmall ε hε _ this _ (Nat.mod_lt k hm)

/-! ## A critical multiplier excludes exponential stability -/

/-- **A derivative with a real eigenvalue `|μ| ≥ 1` excludes local exponential stability.** At a
fixed point where `F` has the derivative `L` with `L v = μ v`, `v ≠ 0`, `|μ| ≥ 1`, the geometric
estimate `‖F^[k] y − x‖ ≤ C ρ^k ‖y − x‖` fails: along `v` the derivative of `F^[k]` keeps the
length `|μ|^k ≥ 1` while `C ρ^k → 0`. -/
@[tmio T, powerlib_foundation] theorem not_locallyExponentiallyStable_of_eigenvector
    {F : ℝⁿ → ℝⁿ} {L : ℝⁿ →L[ℝ] ℝⁿ} {x : ℝⁿ} (hF : HasFDerivAt F L x) (hx : F x = x)
    {v : ℝⁿ} (hv : v ≠ 0) {μ : ℝ} (hLv : L v = μ • v) (hμ : 1 ≤ |μ|) :
    ¬ LocallyExponentiallyStable F x := by
  rintro ⟨r, C, ρ, hr, hC, hρ0, hρ1, hb⟩
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  have hpow : ∀ j : ℕ, (L ^ j) v = μ ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih,
        map_smul, hLv, smul_smul, pow_succ]
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_norm_sub_ge (hF.iterate hx k) (Function.iterate_fixed hx k)
      (by norm_num : (0 : ℝ) < 1 / 2))
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set t : ℝ := min s r / (2 * ‖v‖) with ht
  have hmin : 0 < min s r := lt_min hs hr
  have ht0 : 0 < t := by positivity
  have hyx : ‖(x + t • v) - x‖ = min s r / 2 := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le, ht]
    field_simp
  have hys : dist (x + t • v) x < s := by
    rw [dist_eq_norm, hyx]; linarith [min_le_left s r]
  have hyr : ‖(x + t • v) - x‖ < r := by rw [hyx]; linarith [min_le_right s r]
  have h1 := hball hys
  have h2 := hb _ hyr k
  have hLk : ‖(L ^ k) ((x + t • v) - x)‖ = |μ| ^ k * ‖(x + t • v) - x‖ := by
    rw [add_sub_cancel_left, map_smul, hpow, smul_smul, norm_smul, norm_smul, norm_mul,
      norm_pow]
    simp only [Real.norm_eq_abs]
    ring
  have hμk : 1 ≤ |μ| ^ k := one_le_pow₀ hμ
  have hd0 : 0 < ‖(x + t • v) - x‖ := by rw [hyx]; positivity
  have h3 : C * ρ ^ k * ‖(x + t • v) - x‖ < 1 / 2 * ‖(x + t • v) - x‖ :=
    mul_lt_mul_of_pos_right hk hd0
  rw [hLk] at h1
  nlinarith

/-! ## One-dimensional normal forms at a critical multiplier -/

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- **A critical map is not exponentially stable.** A map on `ℝ¹` with `F y = μ y + O(y²)` at the
fixed point `0` (`|F y 0 − μ y 0| ≤ K |y 0|²` for `‖y‖ ≤ ρ`) and `|μ| = 1` is not locally
exponentially stable: every normal form below is at best asymptotically stable. -/
@[tmio T, powerlib_foundation] theorem critical_not_locallyExponentiallyStable {F : ℝ¹ → ℝ¹}
    {μ K ρ : ℝ} (hρ : 0 < ρ) (hμ : |μ| = 1)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - μ * y 0| ≤ K * |y 0| ^ 2) :
    ¬ LocallyExponentiallyStable F 0 := by
  have hF0 : F 0 = 0 := by
    have h := hF 0 (by simp [hρ.le])
    have h0 : F 0 0 = 0 := by simpa using h
    ext i
    fin_cases i
    simpa using h0
  have hD : HasFDerivAt F (μ • ContinuousLinearMap.id ℝ ℝ¹) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hO : (fun h : ℝ¹ => F (0 + h) - F 0 - (μ • ContinuousLinearMap.id ℝ ℝ¹) h) =O[𝓝 0]
        fun h : ℝ¹ => ‖h‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound K ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ¹) hρ] with h hh
      rw [Metric.mem_closedBall, dist_zero_right] at hh
      have e : (F h - (μ • ContinuousLinearMap.id ℝ ℝ¹) h) 0 = F h 0 - μ * h 0 := by
        simp [PiLp.sub_apply, PiLp.smul_apply]
      rw [zero_add, hF0, sub_zero, NormalForm.norm_state1, e, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg h) 2), NormalForm.norm_state1]
      exact hF h hh
    exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine not_locallyExponentiallyStable_of_eigenvector hD hF0
    (v := EuclideanSpace.single 0 1) (by simp) (μ := μ) (by simp) hμ.ge

/-- **Pitchfork type, stable side.** `F(y) = y + b y³ + O(y⁴)` (`|F y 0 − (y 0 + b y 0³)| ≤
K |y 0|⁴` for `‖y‖ ≤ ρ`) with `b < 0`: the fixed point `0` is locally asymptotically stable, since
`|F y| ≤ |y| − (|b|/2) |y|³` near `0`. -/
@[tmio T, powerlib_foundation] theorem cubic_localAsymptoticStable {F : ℝ¹ → ℝ¹} {b K ρ : ℝ}
    (hρ : 0 < ρ) (hb : b < 0)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (y 0 + b * y 0 ^ 3)| ≤ K * |y 0| ^ 4) :
    LocalAsymptoticStable F 0 := by
  set β := -b with hβdef
  have hβ : 0 < β := by linarith
  set r := min ρ (min (1 / (β + 1)) (β / (2 * (|K| + 1)))) with hrdef
  have hr : 0 < r := lt_min hρ (lt_min (by positivity) (by positivity))
  refine localAsymptoticStable_of_norm_le_sub_pow (c := β / 2) (m := 3) hr (by positivity)
    (by norm_num) fun y hy => ?_
  rw [sub_zero] at hy ⊢
  rw [sub_zero, NormalForm.norm_state1, NormalForm.norm_state1]
  rw [NormalForm.norm_state1] at hy
  set u := y 0 with hu
  set X := |u| with hX
  have hX0 : 0 ≤ X := abs_nonneg u
  have hXb : X ≤ 1 / (β + 1) := hy.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hXK : X ≤ β / (2 * (|K| + 1)) := hy.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hXρ : X ≤ ρ := hy.le.trans (min_le_left _ _)
  have h := hF y (by rw [NormalForm.norm_state1]; exact hXρ)
  rw [← hu] at h
  have hX1 : X ≤ 1 := hXb.trans (by rw [div_le_one (by positivity)]; linarith)
  have hu2 : u ^ 2 = X ^ 2 := (sq_abs u).symm
  have hβX : β * X ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hXb hβ.le
    have h' : β * (1 / (β + 1)) ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have hfac : |u + b * u ^ 3| = X - β * X ^ 3 := by
    have e : u + b * u ^ 3 = u * (1 - β * u ^ 2) := by rw [hβdef]; ring
    have hpos : 0 ≤ 1 - β * u ^ 2 := by
      rw [hu2]; nlinarith [mul_le_mul_of_nonneg_left hX1 hX0]
    rw [e, abs_mul, abs_of_nonneg hpos, hu2]
    ring
  have hK4 : K * X ^ 4 ≤ β / 2 * X ^ 3 := by
    have hKX : |K| * X ≤ β / 2 := by
      have := mul_le_mul_of_nonneg_left hXK (abs_nonneg K)
      have h' : |K| * (β / (2 * (|K| + 1))) ≤ β / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg K]
      linarith
    have h3 : 0 ≤ X ^ 3 := pow_nonneg hX0 3
    calc K * X ^ 4 ≤ |K| * X ^ 4 := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ = (|K| * X) * X ^ 3 := by ring
      _ ≤ β / 2 * X ^ 3 := mul_le_mul_of_nonneg_right hKX h3
  have htri := abs_sub_abs_le_abs_sub (F y 0) (u + b * u ^ 3)
  rw [hfac] at htri
  have : |u| ^ 4 = X ^ 4 := rfl
  rw [this] at h
  linarith

/-- **Pitchfork type, unstable side.** `F(y) = y + b y³ + O(y⁴)` with `b > 0`: the fixed point `0`
is unstable, since `|F y| ≥ |y| + (b/2) |y|³` near `0`. -/
@[tmio T, powerlib_foundation] theorem cubic_unstable {F : ℝ¹ → ℝ¹} {b K ρ : ℝ} (hρ : 0 < ρ)
    (hb : 0 < b) (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (y 0 + b * y 0 ^ 3)| ≤ K * |y 0| ^ 4) :
    Unstable F 0 := by
  set r := min ρ (b / (2 * (|K| + 1))) with hrdef
  have hr : 0 < r := lt_min hρ (by positivity)
  refine unstable_of_norm_add_pow_le one_pos (c := b / 2) (m := 3) hr (by positivity)
    fun y hy => ?_
  rw [sub_zero] at hy ⊢
  rw [sub_zero, NormalForm.norm_state1, NormalForm.norm_state1]
  rw [NormalForm.norm_state1] at hy
  set u := y 0 with hu
  set X := |u| with hX
  have hX0 : 0 ≤ X := abs_nonneg u
  have hXK : X ≤ b / (2 * (|K| + 1)) := hy.le.trans (min_le_right _ _)
  have hXρ : X ≤ ρ := hy.le.trans (min_le_left _ _)
  have h := hF y (by rw [NormalForm.norm_state1]; exact hXρ)
  rw [← hu] at h
  have hu2 : u ^ 2 = X ^ 2 := (sq_abs u).symm
  have hfac : |u + b * u ^ 3| = X + b * X ^ 3 := by
    have e : u + b * u ^ 3 = u * (1 + b * u ^ 2) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + b * u ^ 2), hu2]
    ring
  have hK4 : K * X ^ 4 ≤ b / 2 * X ^ 3 := by
    have hKX : |K| * X ≤ b / 2 := by
      have := mul_le_mul_of_nonneg_left hXK (abs_nonneg K)
      have h' : |K| * (b / (2 * (|K| + 1))) ≤ b / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg K]
      linarith
    have h3 : 0 ≤ X ^ 3 := pow_nonneg hX0 3
    calc K * X ^ 4 ≤ |K| * X ^ 4 := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ = (|K| * X) * X ^ 3 := by ring
      _ ≤ b / 2 * X ^ 3 := mul_le_mul_of_nonneg_right hKX h3
  have htri := abs_sub_abs_le_abs_sub (u + b * u ^ 3) (F y 0)
  rw [hfac, abs_sub_comm] at htri
  have : |u| ^ 4 = X ^ 4 := rfl
  rw [this] at h
  linarith

/-- **Fold / transcritical type.** `F(y) = y + a y² + O(y³)` (`|F y 0 − (y 0 + a y 0²)| ≤
K |y 0|³` for `‖y‖ ≤ ρ`) with `a ≠ 0`: the fixed point `0` is unstable. On the side `a y 0 > 0`
the Chetaev function `V(y) = a y 0` grows by at least `V²/2` per step. -/
@[tmio T, powerlib_foundation] theorem quadratic_unstable {F : ℝ¹ → ℝ¹} {a K ρ : ℝ} (hρ : 0 < ρ)
    (ha : a ≠ 0) (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (y 0 + a * y 0 ^ 2)| ≤ K * |y 0| ^ 3) :
    Unstable F 0 := by
  have ha0 : 0 < |a| := abs_pos.mpr ha
  set r := min ρ (|a| / (2 * (|K| + 1))) with hrdef
  have hr : 0 < r := lt_min hρ (by positivity)
  refine unstable_of_add_pow_le (V := fun y : ℝ¹ => a * y 0) (B := |a| * r) (c := 1 / 2) (m := 2)
    hr (by norm_num) (fun y hy => ?_) (fun y hy hV => ?_) fun δ hδ => ?_
  · rw [sub_zero, NormalForm.norm_state1] at hy
    calc a * y 0 ≤ |a * y 0| := le_abs_self _
      _ = |a| * |y 0| := abs_mul _ _
      _ ≤ |a| * r := by gcongr
  · rw [sub_zero, NormalForm.norm_state1] at hy
    simp only at hV ⊢
    set u := y 0 with hu
    set X := |u| with hX
    have hX0 : 0 ≤ X := abs_nonneg u
    have hXK : X ≤ |a| / (2 * (|K| + 1)) := hy.le.trans (min_le_right _ _)
    have hXρ : X ≤ ρ := hy.le.trans (min_le_left _ _)
    have h := hF y (by rw [NormalForm.norm_state1]; exact hXρ)
    rw [← hu] at h
    have hv : a * u = |a| * X := by
      rw [hX, ← abs_mul]; exact (abs_of_pos hV).symm
    have hlow : a * (u + a * u ^ 2) - |a| * (|K| * X ^ 3) ≤ a * F y 0 := by
      have h1 : |a * F y 0 - a * (u + a * u ^ 2)| ≤ |a| * (|K| * X ^ 3) := by
        rw [← mul_sub, abs_mul]
        refine mul_le_mul_of_nonneg_left (h.trans ?_) (abs_nonneg a)
        exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      linarith [(abs_le.mp h1).1]
    have hsq : a * (u + a * u ^ 2) = a * u + (a * u) ^ 2 := by ring
    have hKX : |K| * X ≤ |a| / 2 := by
      have := mul_le_mul_of_nonneg_left hXK (abs_nonneg K)
      have h' : |K| * (|a| / (2 * (|K| + 1))) ≤ |a| / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg K]
      linarith
    have hterm : |a| * (|K| * X ^ 3) ≤ 1 / 2 * (a * u) ^ 2 := by
      rw [hv]
      have : |a| * (|K| * X ^ 3) = (|K| * X) * (|a| * X ^ 2) := by ring
      rw [this]
      have h2 : 0 ≤ |a| * X ^ 2 := by positivity
      calc (|K| * X) * (|a| * X ^ 2) ≤ |a| / 2 * (|a| * X ^ 2) := mul_le_mul_of_nonneg_right hKX h2
        _ = 1 / 2 * (|a| * X) ^ 2 := by ring
    rw [hsq] at hlow
    linarith
  · refine ⟨EuclideanSpace.single 0 (a * (δ / (2 * |a|))), ?_, ?_⟩
    · rw [sub_zero, NormalForm.norm_state1]
      simp only [PiLp.single_apply, ite_true]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / (2 * |a|))]
      field_simp
      linarith
    · simp only [PiLp.single_apply, ite_true]
      have : a * (a * (δ / (2 * |a|))) = a ^ 2 * (δ / (2 * |a|)) := by ring
      rw [this]
      have : 0 < a ^ 2 := by positivity
      positivity

/-- One step of the flip normal form: `|p| ≤ (1 + |a| + |b| + |K|) |u|` for
`|p − (−u + a u² + b u³)| ≤ K u⁴`, `|u| ≤ 1`. -/
@[tmio T, powerlib_foundation] private theorem flip_one_step_aux {a b K u p : ℝ} (hu : |u| ≤ 1)
    (hp : |p - (-u + a * u ^ 2 + b * u ^ 3)| ≤ K * |u| ^ 4) :
    |p| ≤ (1 + |a| + |b| + |K|) * |u| := by
  have hX0 : 0 ≤ |u| := abs_nonneg u
  have h2 : |u| ^ 2 ≤ |u| := by nlinarith
  have h3 : |u| ^ 3 ≤ |u| := by nlinarith
  have h4 : |u| ^ 4 ≤ |u| := by nlinarith
  have hq : |-u + a * u ^ 2 + b * u ^ 3| ≤ |u| + |a| * |u| ^ 2 + |b| * |u| ^ 3 := by
    calc |-u + a * u ^ 2 + b * u ^ 3| ≤ |-u + a * u ^ 2| + |b * u ^ 3| := abs_add_le _ _
      _ ≤ |-u| + |a * u ^ 2| + |b * u ^ 3| := by gcongr; exact abs_add_le _ _
      _ = |u| + |a| * |u| ^ 2 + |b| * |u| ^ 3 := by rw [abs_neg, abs_mul, abs_mul, abs_pow, abs_pow]
  have hK : K * |u| ^ 4 ≤ |K| * |u| := (mul_le_mul_of_nonneg_right (le_abs_self K)
    (by positivity)).trans (mul_le_mul_of_nonneg_left h4 (abs_nonneg K))
  have ha : |a| * |u| ^ 2 ≤ |a| * |u| := mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
  have hb : |b| * |u| ^ 3 ≤ |b| * |u| := mul_le_mul_of_nonneg_left h3 (abs_nonneg b)
  have htri := abs_sub_abs_le_abs_sub p (-u + a * u ^ 2 + b * u ^ 3)
  nlinarith

/-- Two steps of the flip normal form: with `N = 1 + |a| + |b| + |K|` and `|u| ≤ 1`,
`|p' − (u − 2(a² + b) u³)| ≤ 16 N⁵ u⁴`. The identity behind it, with `v = p + u` and
`e = p − (−u + a u² + b u³)`, is
`−p + a p² + b p³ − u + 2(a² + b) u³ = −e − 2a u e − 2ab u⁴ + a v² + 3b u² v − 3b u v² + b v³`. -/
@[tmio T, powerlib_foundation] private theorem flip_two_step_aux {a b K u p p' : ℝ}
    (hu : |u| ≤ 1) (hp : |p - (-u + a * u ^ 2 + b * u ^ 3)| ≤ K * |u| ^ 4)
    (hp' : |p' - (-p + a * p ^ 2 + b * p ^ 3)| ≤ K * |p| ^ 4) :
    |p' - (u - 2 * (a ^ 2 + b) * u ^ 3)| ≤ 16 * (1 + |a| + |b| + |K|) ^ 5 * |u| ^ 4 := by
  set N := 1 + |a| + |b| + |K| with hNdef
  have hX0 : 0 ≤ |u| := abs_nonneg u
  have hA : |a| ≤ N := by linarith [abs_nonneg b, abs_nonneg K]
  have hB : |b| ≤ N := by linarith [abs_nonneg a, abs_nonneg K]
  have hKN : |K| ≤ N := by linarith [abs_nonneg a, abs_nonneg b]
  have hN1 : 1 ≤ N := by linarith [abs_nonneg a, abs_nonneg b, abs_nonneg K]
  have hN0 : 0 ≤ N := by linarith
  have hpN : |p| ≤ N * |u| := flip_one_step_aux hu hp
  have key : p' - (u - 2 * (a ^ 2 + b) * u ^ 3) =
      (p' - (-p + a * p ^ 2 + b * p ^ 3)) + (-(p - (-u + a * u ^ 2 + b * u ^ 3))
        - 2 * a * u * (p - (-u + a * u ^ 2 + b * u ^ 3)) - 2 * a * b * u ^ 4
        + a * (p + u) ^ 2 + 3 * b * u ^ 2 * (p + u) - 3 * b * u * (p + u) ^ 2
        + b * (p + u) ^ 3) := by ring
  set e := p - (-u + a * u ^ 2 + b * u ^ 3) with he
  set v := p + u with hv
  set e₂ := p' - (-p + a * p ^ 2 + b * p ^ 3) with he₂
  have h4 : |u| ^ 4 ≤ |u| ^ 2 := pow_le_pow_of_le_one hX0 hu (by norm_num)
  have hE : |e| ≤ N * |u| ^ 4 :=
    hp.trans (mul_le_mul_of_nonneg_right ((le_abs_self K).trans hKN) (by positivity))
  have hE' : |e| ≤ |K| * |u| ^ 2 :=
    hp.trans ((mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h4 (abs_nonneg K)))
  have hV : |v| ≤ N * |u| ^ 2 := by
    have hve : v = a * u ^ 2 + b * u ^ 3 + e := by rw [hv, he]; ring
    have h3 : |u| ^ 3 ≤ |u| ^ 2 := pow_le_pow_of_le_one hX0 hu (by norm_num)
    have hb3 : |b| * |u| ^ 3 ≤ |b| * |u| ^ 2 := mul_le_mul_of_nonneg_left h3 (abs_nonneg b)
    calc |v| = |a * u ^ 2 + b * u ^ 3 + e| := by rw [hve]
      _ ≤ |a * u ^ 2| + |b * u ^ 3| + |e| := by
          refine (abs_add_le _ _).trans ?_; gcongr; exact abs_add_le _ _
      _ = |a| * |u| ^ 2 + |b| * |u| ^ 3 + |e| := by rw [abs_mul, abs_mul, abs_pow, abs_pow]
      _ ≤ |a| * |u| ^ 2 + |b| * |u| ^ 2 + |K| * |u| ^ 2 := by linarith
      _ ≤ N * |u| ^ 2 := by
          have : 0 ≤ |u| ^ 2 := by positivity
          nlinarith
  have hE₂ : |e₂| ≤ N ^ 5 * |u| ^ 4 := by
    calc |e₂| ≤ K * |p| ^ 4 := hp'
      _ ≤ |K| * |p| ^ 4 := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ N * (N * |u|) ^ 4 := by gcongr
      _ = N ^ 5 * |u| ^ 4 := by ring
  have t1 : |2 * a * u * e| ≤ 2 * N ^ 2 * |u| ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc 2 * |a| * |u| * |e| ≤ 2 * N * 1 * (N * |u| ^ 4) := by gcongr
      _ = 2 * N ^ 2 * |u| ^ 4 := by ring
  have t2 : |2 * a * b * u ^ 4| ≤ 2 * N ^ 2 * |u| ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_two, abs_pow]
    calc 2 * |a| * |b| * |u| ^ 4 ≤ 2 * N * N * |u| ^ 4 := by gcongr
      _ = 2 * N ^ 2 * |u| ^ 4 := by ring
  have t3 : |a * v ^ 2| ≤ N ^ 3 * |u| ^ 4 := by
    rw [abs_mul, abs_pow]
    calc |a| * |v| ^ 2 ≤ N * (N * |u| ^ 2) ^ 2 := by gcongr
      _ = N ^ 3 * |u| ^ 4 := by ring
  have t4 : |3 * b * u ^ 2 * v| ≤ 3 * N ^ 2 * |u| ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc 3 * |b| * |u| ^ 2 * |v| ≤ 3 * N * |u| ^ 2 * (N * |u| ^ 2) := by gcongr
      _ = 3 * N ^ 2 * |u| ^ 4 := by ring
  have t5 : |3 * b * u * v ^ 2| ≤ 3 * N ^ 3 * |u| ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc 3 * |b| * |u| * |v| ^ 2 ≤ 3 * N * 1 * (N * |u| ^ 2) ^ 2 := by gcongr
      _ = 3 * N ^ 3 * |u| ^ 4 := by ring
  have t6 : |b * v ^ 3| ≤ N ^ 4 * |u| ^ 4 := by
    rw [abs_mul, abs_pow]
    have h6 : |u| ^ 6 ≤ |u| ^ 4 := pow_le_pow_of_le_one hX0 hu (by norm_num)
    calc |b| * |v| ^ 3 ≤ N * (N * |u| ^ 2) ^ 3 := by gcongr
      _ = N ^ 4 * |u| ^ 6 := by ring
      _ ≤ N ^ 4 * |u| ^ 4 := by gcongr
  have hu4 : 0 ≤ |u| ^ 4 := by positivity
  have q1 : N * |u| ^ 4 ≤ N ^ 5 * |u| ^ 4 :=
    mul_le_mul_of_nonneg_right (le_self_pow₀ hN1 (by norm_num)) hu4
  have q2 : N ^ 2 * |u| ^ 4 ≤ N ^ 5 * |u| ^ 4 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by norm_num)) hu4
  have q3 : N ^ 3 * |u| ^ 4 ≤ N ^ 5 * |u| ^ 4 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by norm_num)) hu4
  have q4 : N ^ 4 * |u| ^ 4 ≤ N ^ 5 * |u| ^ 4 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by norm_num)) hu4
  rw [key]
  have a0 := abs_le.mp hE
  have a1 := abs_le.mp t1
  have a2 := abs_le.mp t2
  have a3 := abs_le.mp t3
  have a4 := abs_le.mp t4
  have a5 := abs_le.mp t5
  have a6 := abs_le.mp t6
  have a7 := abs_le.mp hE₂
  rw [abs_le]
  constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1,
    a5.2, a6.1, a6.2, a7.1, a7.2]

/-- **The second iterate of the flip normal form.** If `F(y) = −y + a y² + b y³ + O(y⁴)`
(`|F y 0 − (−y 0 + a y 0² + b y 0³)| ≤ K |y 0|⁴` for `‖y‖ ≤ ρ`), then
`F∘F(y) = y − 2(a² + b) y³ + O(y⁴)` with the explicit bound `16 N⁵ |y 0|⁴` for
`‖y‖ ≤ min 1 (ρ / N)`, `N = 1 + |a| + |b| + |K|`: the quadratic coefficient feeds the cubic one of
the second iterate. -/
@[tmio T, powerlib_foundation] theorem flip_second_iterate {F : ℝ¹ → ℝ¹} {a b K ρ : ℝ}
    (hρ : 0 < ρ)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + a * y 0 ^ 2 + b * y 0 ^ 3)| ≤ K * |y 0| ^ 4) :
    ∀ y : ℝ¹, ‖y‖ ≤ min 1 (ρ / (1 + |a| + |b| + |K|)) →
      |F^[2] y 0 - (y 0 - 2 * (a ^ 2 + b) * y 0 ^ 3)| ≤
        16 * (1 + |a| + |b| + |K|) ^ 5 * |y 0| ^ 4 := by
  intro y hy
  have hN : 1 ≤ 1 + |a| + |b| + |K| := by linarith [abs_nonneg a, abs_nonneg b, abs_nonneg K]
  have hN0 : 0 < 1 + |a| + |b| + |K| := by linarith
  rw [NormalForm.norm_state1] at hy
  have hu1 : |y 0| ≤ 1 := hy.trans (min_le_left _ _)
  have huρ : |y 0| ≤ ρ / (1 + |a| + |b| + |K|) := hy.trans (min_le_right _ _)
  have hyρ : ‖y‖ ≤ ρ := by rw [NormalForm.norm_state1]; exact huρ.trans (div_le_self hρ.le hN)
  have h1 := hF y hyρ
  have hp := flip_one_step_aux hu1 h1
  have hFyρ : ‖F y‖ ≤ ρ := by
    rw [NormalForm.norm_state1]
    calc |F y 0| ≤ (1 + |a| + |b| + |K|) * |y 0| := hp
      _ ≤ (1 + |a| + |b| + |K|) * (ρ / (1 + |a| + |b| + |K|)) := by gcongr
      _ = ρ := by field_simp
  have h2 := hF (F y) hFyρ
  rw [show F^[2] y = F (F y) from rfl]
  exact flip_two_step_aux hu1 h1 h2

/-- **Flip (period doubling), stable side.** `F(y) = −y + a y² + b y³ + O(y⁴)` with
`a² + b > 0`: the fixed point `0` is locally asymptotically stable (the second iterate is of
pitchfork type with cubic coefficient `−2(a² + b) < 0`, and one step is bounded linearly). With
`a = 0`: stable for `b > 0`. -/
@[tmio T, powerlib_foundation] theorem flip_localAsymptoticStable {F : ℝ¹ → ℝ¹} {a b K ρ : ℝ}
    (hρ : 0 < ρ) (hab : 0 < a ^ 2 + b)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + a * y 0 ^ 2 + b * y 0 ^ 3)| ≤ K * |y 0| ^ 4) :
    LocalAsymptoticStable F 0 := by
  have hN : 1 ≤ 1 + |a| + |b| + |K| := by linarith [abs_nonneg a, abs_nonneg b, abs_nonneg K]
  have h2 := flip_second_iterate hρ hF
  have hLAS : LocalAsymptoticStable (F^[2]) 0 := by
    refine cubic_localAsymptoticStable (b := -(2 * (a ^ 2 + b)))
      (K := 16 * (1 + |a| + |b| + |K|) ^ 5) (ρ := min 1 (ρ / (1 + |a| + |b| + |K|)))
      (lt_min one_pos (div_pos hρ (by linarith)))
      (by linarith) fun y hy => ?_
    rw [show y 0 + -(2 * (a ^ 2 + b)) * y 0 ^ 3 = y 0 - 2 * (a ^ 2 + b) * y 0 ^ 3 by ring]
    exact h2 y hy
  refine hLAS.of_iterate two_pos (r := min 1 ρ) (C := 1 + |a| + |b| + |K|)
    (lt_min one_pos hρ) fun y hy => ?_
  rw [sub_zero, NormalForm.norm_state1] at hy
  rw [sub_zero, sub_zero, NormalForm.norm_state1, NormalForm.norm_state1]
  exact flip_one_step_aux (hy.le.trans (min_le_left _ _))
    (hF y (by rw [NormalForm.norm_state1]; exact hy.le.trans (min_le_right _ _)))

/-- **Flip (period doubling), unstable side.** `F(y) = −y + a y² + b y³ + O(y⁴)` with
`a² + b < 0`: the fixed point `0` is unstable (the second iterate is of pitchfork type with cubic
coefficient `−2(a² + b) > 0`). With `a = 0`: unstable for `b < 0`. -/
@[tmio T, powerlib_foundation] theorem flip_unstable {F : ℝ¹ → ℝ¹} {a b K ρ : ℝ} (hρ : 0 < ρ)
    (hab : a ^ 2 + b < 0)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + a * y 0 ^ 2 + b * y 0 ^ 3)| ≤ K * |y 0| ^ 4) :
    Unstable F 0 := by
  have hN : 1 ≤ 1 + |a| + |b| + |K| := by linarith [abs_nonneg a, abs_nonneg b, abs_nonneg K]
  have h2 := flip_second_iterate hρ hF
  refine Unstable.of_iterate (m := 2) ?_
  refine cubic_unstable (b := -(2 * (a ^ 2 + b))) (K := 16 * (1 + |a| + |b| + |K|) ^ 5)
    (ρ := min 1 (ρ / (1 + |a| + |b| + |K|))) (lt_min one_pos (div_pos hρ (by linarith)))
    (by linarith) fun y hy => ?_
  rw [show y 0 + -(2 * (a ^ 2 + b)) * y 0 ^ 3 = y 0 - 2 * (a ^ 2 + b) * y 0 ^ 3 by ring]
  exact h2 y hy

end powerlib.Map

/-! ## Flows: one linearization along one periodic solution, opposite fates -/

namespace powerlib.Periodic

open Filter Topology Matrix
open scoped RealInnerProductSpace ComplexOrder

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- `ẋ = S x + κ ‖x‖² x`: the linear part `S` plus the cubic field `Dynamics.cubicField κ`. With a
skew-symmetric `S` the linear part rotates and the cubic part alone moves `‖x‖`. -/
def rotCubicField (S : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) (x : ℝⁿ) : ℝⁿ :=
  Linear.op S x + Dynamics.cubicField κ x

/-- The field is smooth (indeed `C^k` for every `k`, a polynomial). -/
@[tmio T, powerlib_foundation] theorem contDiff_rotCubicField (S : Matrix (Fin n) (Fin n) ℝ)
    (κ : ℝ) {k : WithTop ℕ∞} : ContDiff ℝ k (rotCubicField S κ) :=
  (Linear.op S).contDiff.add ((contDiff_const.mul (contDiff_norm_sq ℝ)).smul contDiff_id)

/-- The linearization at the equilibrium `0` is `S`, whatever the cubic coefficient `κ`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_rotCubicField (S : Matrix (Fin n) (Fin n) ℝ)
    (κ : ℝ) : HasFDerivAt (rotCubicField S κ) (Linear.op S) 0 := by
  have h1 : HasFDerivAt (Dynamics.cubicField (n := n) κ) (0 : ℝⁿ →L[ℝ] ℝⁿ) 0 := by
    have hd := ((Dynamics.cubicField_contDiff (n := n) κ).differentiable one_ne_zero
      0).hasFDerivAt
    rwa [Dynamics.cubicField_jacobian, map_zero] at hd
  have h := (Linear.op S).hasFDerivAt.add h1
  rw [add_zero] at h
  exact h

/-- A skew-symmetric matrix does no work: `⟪x, S x⟫ = 0` for `Sᵀ = −S`. -/
@[tmio T, powerlib_foundation] theorem inner_op_self_of_skew {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : Sᵀ = -S) (x : ℝⁿ) : ⟪x, Linear.op S x⟫ = 0 := by
  rw [Linear.op, Matrix.inner_toEuclideanCLM]
  have h : x.ofLp ⬝ᵥ S *ᵥ x.ofLp = -(x.ofLp ⬝ᵥ S *ᵥ x.ofLp) := by
    conv_lhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  linarith

/-- Along `ẋ = S x + κ ‖x‖² x` with skew `S`, `d‖x‖²/dt = 2κ ‖x‖⁴`. -/
@[tmio T, powerlib_foundation] theorem lie_norm_sq_rotCubicField {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : Sᵀ = -S) (κ : ℝ) (x : ℝⁿ) :
    fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ 2) x (rotCubicField S κ x) = 2 * κ * ‖x‖ ^ 4 := by
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp [rotCubicField, Dynamics.cubicField, inner_add_right, inner_smul_right,
    inner_op_self_of_skew hS]
  ring

/-- **Stable member: `κ < 0`.** With skew `S` the origin of `ẋ = S x + κ ‖x‖² x` is globally
asymptotically stable (strict Lyapunov function `‖x‖²`, the one of
`Dynamics.cubic_neg_strictLyapunov`). -/
@[tmio T, powerlib_foundation] theorem rotCubic_globallyAsymptoticallyStable
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = -S) {κ : ℝ} (hκ : κ < 0) (hn : 0 < n) :
    Flow.GloballyAsymptoticallyStable (rotCubicField S κ) 0 := by
  have hL := Dynamics.cubic_neg_strictLyapunov (n := n)
  refine Flow.globallyAsymptoticallyStable_of_strictLyapunov hn (contDiff_rotCubicField S κ)
    ⟨hL.hcont, hL.hV_c1, hL.hzero, hL.hpos, ?_, fun x hx => ?_, hL.hbounded_sublevel⟩
  · simp [rotCubicField, Dynamics.cubicField]
  · rw [lie_norm_sq_rotCubicField hS]
    have := pow_pos (norm_pos_iff.mpr hx) 4
    nlinarith

/-- **Unstable member: `κ > 0`.** With skew `S` the origin of `ẋ = S x + κ ‖x‖² x` is unstable
(Chetaev function `‖x‖²`, `Dynamics.unstable_of_eventually_chetaev`). -/
@[tmio T, powerlib_foundation] theorem rotCubic_unstable {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : Sᵀ = -S) {κ : ℝ} (hκ : 0 < κ) (hn : 0 < n) : Unstable (rotCubicField S κ) 0 := by
  refine Dynamics.unstable_of_eventually_chetaev hn (contDiff_rotCubicField S κ)
    (contDiff_norm_sq ℝ) (by simp) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ 0)
    exact pow_pos (norm_pos_iff.mpr hx) 2
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ 0)
    rw [lie_norm_sq_rotCubicField hS]
    have := pow_pos (norm_pos_iff.mpr hx) 4
    positivity

/-- **Never exponentially stable.** If the linear part `S` is not Hurwitz (for skew `S`, always),
the origin of `ẋ = S x + κ ‖x‖² x` is not locally exponentially stable, for every `κ`
(converse linearization, `Dynamics.isHurwitz_of_locallyExponentiallyStable`). -/
@[tmio T, powerlib_foundation] theorem rotCubic_not_locallyExponentiallyStable
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : ¬ LinearSystems.IsHurwitz S) (κ : ℝ) :
    ¬ LocallyExponentiallyStable (rotCubicField S κ) 0 := fun h =>
  hS (Dynamics.isHurwitz_of_locallyExponentiallyStable S (contDiff_rotCubicField S κ)
    (hasFDerivAt_rotCubicField S κ).fderiv h)

/-- The multipliers of a scalar monodromy `c I` are all equal to `c`. -/
@[tmio T, powerlib_foundation] theorem eq_of_mem_spectrum_smul_one {X : Type*} [Fintype X]
    [DecidableEq X] {c : ℝ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((c • (1 : Matrix X X ℝ)).map (algebraMap ℝ ℂ))) : μ = c := by
  obtain ⟨v, hv, h⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
  have hc : (c • (1 : Matrix X X ℝ)).map (algebraMap ℝ ℂ) *ᵥ v = (c : ℂ) • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite (fun r : ℝ => (r : ℂ)), ite_mul]
  rw [hc] at h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
  exact (mul_right_cancel₀ hi this).symm

/-- **A scalar monodromy `c I` with `|c| = 1` sits on the boundary of both Floquet criteria**: it
is not Schur stable (`n > 0`) and has no multiplier outside the unit circle. -/
@[tmio T, powerlib_foundation] theorem critical_smul_one {c : ℝ} (hc : |c| = 1) (hn : 0 < n) :
    ¬ LTI.SchurStable (c • (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
      ∀ μ ∈ spectrum ℂ ((c • (1 : Matrix (Fin n) (Fin n) ℝ)).map (algebraMap ℝ ℂ)), ‖μ‖ = 1 := by
  refine ⟨fun h => ?_, fun μ hμ => ?_⟩
  · have hv : (Pi.single ⟨0, hn⟩ 1 : Fin n → ℂ) ≠ 0 := by
      intro h0; have := congrFun h0 ⟨0, hn⟩; simp at this
    have := h c _ hv (by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite (fun r : ℝ => (r : ℂ)),
        Pi.single_apply])
    rw [Complex.norm_real, Real.norm_eq_abs, hc] at this
    exact lt_irrefl 1 this
  · rw [eq_of_mem_spectrum_smul_one hμ, Complex.norm_real, Real.norm_eq_abs, hc]

/-- **A skew-symmetric linearization has every multiplier on the unit circle.** For `Sᵀ = −S` the
monodromy `e^{TS}` of `J ≡ S` is orthogonal (`(e^{TS})ᵀ e^{TS} = e^{−TS} e^{TS} = I`), so every
Floquet multiplier has modulus one, for every `T ≥ 0`; in particular none lies outside the unit
circle. This covers every critical type a rotation produces: `+1`, `−1` and complex pairs
`e^{±iθ}`. -/
@[tmio T, powerlib_foundation] theorem norm_eq_one_of_mem_spectrum_skew
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = -S) {T : ℝ} (hT : 0 ≤ T) :
    (∀ μ ∈ spectrum ℂ ((monodromy (fun _ => S) T 0).map (algebraMap ℝ ℂ)), ‖μ‖ = 1) ∧
      ¬ FloquetUnstable (fun _ => S) T := by
  have key : ∀ μ ∈ spectrum ℂ ((monodromy (fun _ => S) T 0).map (algebraMap ℝ ℂ)), ‖μ‖ = 1 := by
    intro μ hμ
    rw [monodromy_const S hT] at hμ
    set E := NormedSpace.exp (T • S) with hEdef
    have hE : Eᵀ * E = 1 := by
      rw [hEdef, ← Matrix.exp_transpose, Matrix.transpose_smul, hS, smul_neg,
        ← Matrix.exp_add_of_commute _ _ ((Commute.refl (T • S)).neg_left), neg_add_cancel,
        NormedSpace.exp_zero]
    obtain ⟨v, hv, hEv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
    set B := E.map (algebraMap ℝ ℂ) with hBdef
    have hB : Bᴴ * B = 1 := by
      have : Bᴴ = (Eᵀ).map (algebraMap ℝ ℂ) := by
        ext i j; simp [B, Matrix.conjTranspose_apply]
      rw [this, ← Matrix.map_mul, hE, Matrix.map_one _ (map_zero _) (map_one _)]
    have hdot : star (B *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ v := by
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hB,
        Matrix.vecMul_one]
    rw [hEv, star_smul, smul_dotProduct, dotProduct_smul, smul_smul] at hdot
    have hq : star v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.mp h)
    have h1 : star μ * μ = 1 := by
      have : (star μ * μ - 1) * (star v ⬝ᵥ v) = 0 := by
        rw [sub_mul, one_mul, ← smul_eq_mul, hdot, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hq)
    have h2 : Complex.normSq μ = 1 := by
      have := Complex.normSq_eq_conj_mul_self (z := μ)
      exact_mod_cast this.trans h1
    have h3 : ‖μ‖ ^ 2 = 1 := by rw [Complex.sq_norm, h2]
    rw [← Real.sqrt_sq (norm_nonneg μ), h3, Real.sqrt_one]
  exact ⟨key, fun ⟨μ, hμ, h1⟩ => by rw [key μ hμ] at h1; exact lt_irrefl 1 h1⟩

/-- `J ≡ (ω/2) J₂` over `T = 2π/ω`: the monodromy is `−I` (the multiplier `−1`, double),
through `ParametricResonance.NormalForm.monodromy_nf` with `σ = 0`, `Ω = ω/2`, `c = 0`. -/
@[tmio T, powerlib_foundation] theorem monodromy_half_rotation {ω : ℝ} (hω : 0 < ω) :
    monodromy (fun _ => (ω / 2) • ParametricResonance.NormalForm.quarter) (2 * Real.pi / ω) 0 =
      -1 := by
  have h := ParametricResonance.NormalForm.monodromy_nf 0 (ω / 2) hω 0
  have e1 : ParametricResonance.NormalForm.nfMatrix 0 (ω / 2) ω 0 =
      fun _ => (ω / 2) • ParametricResonance.NormalForm.quarter := by
    funext t
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ParametricResonance.NormalForm.nfMatrix, ParametricResonance.NormalForm.pumpRe,
        ParametricResonance.NormalForm.pumpIm, ParametricResonance.NormalForm.quarter]
  have e2 : ParametricResonance.slowFlowMatrix 0 (ω / 2 - ω / 2) 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ParametricResonance.slowFlowMatrix]
  rw [e1, e2, smul_zero, NormedSpace.exp_zero] at h
  exact h

/-- The half-turn generator `(ω/2) J₂` is skew-symmetric and, for `ω ≠ 0`, not Hurwitz: it has
the eigenvalue `jω/2` with eigenvector `(1, −j)`. -/
@[tmio T, powerlib_foundation] theorem half_rotation_skew (ω : ℝ) :
    ((ω / 2) • ParametricResonance.NormalForm.quarter)ᵀ =
        -((ω / 2) • ParametricResonance.NormalForm.quarter) ∧
      ¬ LinearSystems.IsHurwitz ((ω / 2) • ParametricResonance.NormalForm.quarter) := by
  refine ⟨?_, fun hH => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ParametricResonance.NormalForm.quarter]
  · have hv : (![1, -Complex.I] : Fin 2 → ℂ) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    have h : ((ω / 2) • ParametricResonance.NormalForm.quarter).map (algebraMap ℝ ℂ) *ᵥ
        ![1, -Complex.I] = (((ω / 2 : ℝ) : ℂ) * Complex.I) • ![1, -Complex.I] := by
      funext i
      fin_cases i <;>
        simp [ParametricResonance.NormalForm.quarter, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
      linear_combination (ω : ℂ) / 2 * Complex.I_sq
    have := hH _ _ hv h
    simp at this

/-- **Critical multiplier `+1`: the linearization does not decide.** On `ℝⁿ` (`n > 0`), the fields
`ẋ = −κ ‖x‖² x` and `ẋ = κ ‖x‖² x` (`κ > 0`; for `n = 1`, `ẋ = ∓κ x³`) are smooth, have the
same linearization `J(t) ≡ 0` along the same periodic solution `0` (period `T > 0` arbitrary),
whose monodromy is `I`: every multiplier equals `1`, so neither Floquet criterion applies. The
first is globally asymptotically, not exponentially, stable; the second is unstable. -/
@[tmio T, powerlib_foundation] theorem critical_plus_undecided (hn : 0 < n) {T κ : ℝ}
    (hT : 0 ≤ T) (hκ : 0 < κ) :
    monodromy (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) T 0 = 1 ∧
      ¬ LTI.SchurStable (monodromy (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) T 0) ∧
      ¬ FloquetUnstable (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) T ∧
      ContDiff ℝ ⊤ (rotCubicField (0 : Matrix (Fin n) (Fin n) ℝ) (-κ)) ∧
      ContDiff ℝ ⊤ (rotCubicField (0 : Matrix (Fin n) (Fin n) ℝ) κ) ∧
      HasFDerivAt (rotCubicField (0 : Matrix (Fin n) (Fin n) ℝ) (-κ)) (Linear.op 0) 0 ∧
      HasFDerivAt (rotCubicField (0 : Matrix (Fin n) (Fin n) ℝ) κ) (Linear.op 0) 0 ∧
      Flow.GloballyAsymptoticallyStable (rotCubicField (0 : Matrix (Fin n) (Fin n) ℝ) (-κ)) 0 ∧
      ¬ LocallyExponentiallyStable (rotCubicField (0 : Matrix (Fin n) (Fin n) ℝ) (-κ)) 0 ∧
      Unstable (rotCubicField (0 : Matrix (Fin n) (Fin n) ℝ) κ) 0 := by
  have hM : monodromy (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) T 0 = 1 := by
    rw [monodromy_const _ hT, smul_zero, NormedSpace.exp_zero]
  have hcrit := critical_smul_one (c := 1) (by simp) hn
  rw [one_smul] at hcrit
  have hS : (0 : Matrix (Fin n) (Fin n) ℝ)ᵀ = -0 := by simp
  have hH : ¬ LinearSystems.IsHurwitz (0 : Matrix (Fin n) (Fin n) ℝ) := by
    intro h
    have hv : (Pi.single ⟨0, hn⟩ 1 : Fin n → ℂ) ≠ 0 := by
      intro h0; have := congrFun h0 ⟨0, hn⟩; simp at this
    have := h 0 _ hv (by
      rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, zero_smul])
    simp at this
  refine ⟨hM, hM ▸ hcrit.1, fun ⟨μ, hμ, h1⟩ => ?_, contDiff_rotCubicField _ _,
    contDiff_rotCubicField _ _, hasFDerivAt_rotCubicField _ _, hasFDerivAt_rotCubicField _ _,
    rotCubic_globallyAsymptoticallyStable hS (by linarith) hn,
    rotCubic_not_locallyExponentiallyStable hH _, rotCubic_unstable hS hκ hn⟩
  rw [hM] at hμ
  rw [hcrit.2 μ hμ] at h1
  exact lt_irrefl 1 h1

/-- **Critical multiplier `−1`: the linearization does not decide.** On `ℝ²`, with
`S = (ω/2) J₂` (`ω > 0`) and `κ > 0`, the fields `ẋ = S x − κ ‖x‖² x` and `ẋ = S x + κ ‖x‖² x` are
smooth and have the same linearization `J(t) ≡ S` along the same periodic solution `0`, read with
the period `T = 2π/ω`; its monodromy is `−I`: every multiplier equals `−1`, so neither Floquet
criterion applies (their period maps, not computed here, are `x ↦ −x ∓ κT ‖x‖² x + O(‖x‖⁵)`).
The first is globally
asymptotically, not exponentially, stable; the second is unstable. -/
@[tmio T, powerlib_foundation] theorem critical_minus_undecided {ω κ : ℝ} (hω : 0 < ω)
    (hκ : 0 < κ) :
    monodromy (fun _ => (ω / 2) • ParametricResonance.NormalForm.quarter) (2 * Real.pi / ω) 0 =
        -1 ∧
      ¬ LTI.SchurStable (monodromy (fun _ => (ω / 2) • ParametricResonance.NormalForm.quarter)
        (2 * Real.pi / ω) 0) ∧
      ¬ FloquetUnstable (fun _ => (ω / 2) • ParametricResonance.NormalForm.quarter)
        (2 * Real.pi / ω) ∧
      ContDiff ℝ ⊤ (rotCubicField ((ω / 2) • ParametricResonance.NormalForm.quarter) (-κ)) ∧
      ContDiff ℝ ⊤ (rotCubicField ((ω / 2) • ParametricResonance.NormalForm.quarter) κ) ∧
      HasFDerivAt (rotCubicField ((ω / 2) • ParametricResonance.NormalForm.quarter) (-κ))
        (Linear.op ((ω / 2) • ParametricResonance.NormalForm.quarter)) 0 ∧
      HasFDerivAt (rotCubicField ((ω / 2) • ParametricResonance.NormalForm.quarter) κ)
        (Linear.op ((ω / 2) • ParametricResonance.NormalForm.quarter)) 0 ∧
      Flow.GloballyAsymptoticallyStable
        (rotCubicField ((ω / 2) • ParametricResonance.NormalForm.quarter) (-κ)) 0 ∧
      ¬ LocallyExponentiallyStable
        (rotCubicField ((ω / 2) • ParametricResonance.NormalForm.quarter) (-κ)) 0 ∧
      Unstable (rotCubicField ((ω / 2) • ParametricResonance.NormalForm.quarter) κ) 0 := by
  have hM := monodromy_half_rotation hω
  have hcrit := critical_smul_one (n := 2) (c := -1) (by simp) two_pos
  rw [neg_one_smul] at hcrit
  obtain ⟨hS, hH⟩ := half_rotation_skew ω
  refine ⟨hM, hM ▸ hcrit.1, fun ⟨μ, hμ, h1⟩ => ?_, contDiff_rotCubicField _ _,
    contDiff_rotCubicField _ _, hasFDerivAt_rotCubicField _ _, hasFDerivAt_rotCubicField _ _,
    rotCubic_globallyAsymptoticallyStable hS (by linarith) two_pos,
    rotCubic_not_locallyExponentiallyStable hH _, rotCubic_unstable hS hκ two_pos⟩
  rw [hM] at hμ
  rw [hcrit.2 μ hμ] at h1
  exact lt_irrefl 1 h1

end powerlib.Periodic
