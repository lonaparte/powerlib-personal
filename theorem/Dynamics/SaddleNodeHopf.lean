import theorem.Dynamics.Basin
import theorem.Dynamics.WeakFocus
import theorem.CurrentControl.SISO

/-! # Local Lyapunov criteria at non-hyperbolic equilibria (foundation)

Model boundary. Autonomous continuous-time ODE `ẋ = f x` on
`Dynamics.State n = EuclideanSpace ℝ (Fin n)` with a `C¹` field supplied by the caller; no input,
delay, switching or time variation. `V̇ x = fderiv ℝ V x (f x)`. Nothing here describes a physical
system: every statement is a generic implication about an arbitrary field and function, a
foundation result.

At a Hopf point (a purely imaginary pair) or a saddle-node (a simple zero eigenvalue) the
linearization decides nothing. The decision is made by a polynomial Lyapunov or Chetaev function
computed from the normal form, whose Lie derivative is sign-definite only on a punctured
neighbourhood of the equilibrium, and only up to higher-order terms. The criteria below take the
hypotheses in exactly that form (`∀ᶠ x in 𝓝[≠] x_eq, …`), and the asymptotic lemmas turn a
normal-form identity `V̇ = −q + o(q)` into such an eventual sign. No centre-manifold theorem is
used.

* `localAsymptoticStable_of_eventually_lyapunov`: `f(x*) = 0`, `W(x*) = 0`, `W > 0` and `Ẇ < 0`
  on a punctured neighbourhood ⇒ local asymptotic stability. Unlike LeanForControl's
  `lyapunov_local_asymptotic_stable`, no global compact sublevel set is required; this is the
  eventual (`𝓝[≠]`) form of `WeakFocus.localAsymptoticStable_of_lyapunov_ball` (LeanForControl's
  `lyapunov_stable` on a ball plus LaSalle's principle for `C¹` fields), which it applies.
* `unstable_of_eventually_chetaev`: `W(x*) = 0`, `W > 0` and `Ẇ > 0` on a punctured neighbourhood
  ⇒ instability (`Dynamics.unstable_of_chetaev`).
* `not_localAsymptoticStable_of_eventually_lie_nonpos`: `V̇ ≤ 0` near `x*` and `V < V(x*)` at
  states arbitrarily close to `x*` ⇒ no local asymptotic stability
  (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`).
* `unstable_of_eventually_lie_neg`: `Ė < 0` on a punctured neighbourhood of an equilibrium and
  `E < E(x*)` at states arbitrarily close to it ⇒ instability (Chetaev on the dissipated level set,
  `Dynamics.unstable_of_lie_nonpos_of_lie_pos`); the saddle-node criterion.
* Asymptotic bookkeeping: `eventually_neg_of_isLittleO` / `eventually_pos_of_isLittleO`
  (`g = ∓q + o(q)` with `q > 0` ⇒ `g` has the sign of `∓q`), `eventually_neg_of_le_of_isLittleO`
  (`g ≤ −q + o(q)`), `isBigO_pow_of_tendsto` / `isLittleO_pow_of_tendsto` (powers of a vanishing
  size function), `isBigO_monomial` (a monomial in two `O(s)` functions is `O(s^{i+j})`),
  `frequently_of_forall_smul` (states on a ray accumulate at the origin).
* Taylor remainders at `0`: `one_sub_cos_isBigO` (`1 − cos x = O(x²)`), `sin_sub_self_isBigO`
  (`sin x − x = O(x³)`), `one_sub_cos_sub_isBigO` (`1 − cos x − x²/2 = O(x⁴)`), from Mathlib's
  `Real.sin_bound`, `Real.cos_bound`, `Real.one_sub_sq_div_two_le_cos`.

Connection architecture. No model family is defined or fixed here; the model families of
`theorem/GFLParametric/` apply these criteria inside their own connection proofs.

Source: generic Lyapunov/Chetaev theory (Khalil, *Nonlinear Systems*, 3rd ed., Theorems 4.1,
4.3); the Hopf and saddle-node normal forms (Guckenheimer–Holmes, §3.4, §3.1) only motivate the
eventual form of the hypotheses.
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology Metric Asymptotics

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-! ## Lyapunov and Chetaev criteria on a punctured neighbourhood -/

/-- A radius on which an eventual punctured-neighbourhood property holds. -/
private theorem exists_radius_of_eventually {x_eq : ℝⁿ} {P : ℝⁿ → Prop}
    (h : ∀ᶠ x in 𝓝[≠] x_eq, P x) :
    ∃ r > 0, ∀ x, ‖x - x_eq‖ < r → x ≠ x_eq → P x := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨r, hr, h⟩ := h
  exact ⟨r, hr, fun x hx hne => h (by rwa [dist_eq_norm]) hne⟩

/-- **Local asymptotic stability from a local strict Lyapunov function.** A `C¹` function that
vanishes at an equilibrium of a `C¹` field and is positive with negative derivative along the
field on a punctured neighbourhood makes the equilibrium locally asymptotically stable. No
global compactness of sublevel sets is needed. -/
@[powerlib_foundation] theorem localAsymptoticStable_of_eventually_lyapunov (hn : 0 < n)
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {W : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (hfx : f x_eq = 0)
    (hW : ContDiff ℝ 1 W) (hW0 : W x_eq = 0) (hpos : ∀ᶠ x in 𝓝[≠] x_eq, 0 < W x)
    (hLie : ∀ᶠ x in 𝓝[≠] x_eq, fderiv ℝ W x (f x) < 0) :
    LocalAsymptoticStable f x_eq := by
  obtain ⟨r, hr, hball⟩ := exists_radius_of_eventually (hpos.and hLie)
  exact WeakFocus.localAsymptoticStable_of_lyapunov_ball hn hf hW hr hfx hW0
    (fun x hx hne => (hball x hx hne).1) fun x hx hne => (hball x hx hne).2

/-- States arbitrarily close to a point of a nontrivial Euclidean space with an eventual
punctured-neighbourhood property. -/
private theorem exists_near_of_eventually (hn : 0 < n) {x_eq : ℝⁿ} {P : ℝⁿ → Prop}
    (h : ∀ᶠ x in 𝓝[≠] x_eq, P x) (ε : ℝ) (hε : 0 < ε) :
    ∃ x, ‖x - x_eq‖ < ε ∧ x ≠ x_eq ∧ P x := by
  obtain ⟨r, hr, hP⟩ := exists_radius_of_eventually h
  set e : ℝⁿ := EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1 with he
  have hen : ‖e‖ = 1 := by rw [he, EuclideanSpace.single, PiLp.norm_single, norm_one]
  set t := min ε r / 2 with ht
  have htpos : 0 < t := by positivity
  have hnorm : ‖(x_eq + t • e) - x_eq‖ = t := by
    rw [add_sub_cancel_left, norm_smul, hen, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
  have htε : t < ε := by
    have := min_le_left ε r
    linarith
  have htr : t < r := by
    have := min_le_right ε r
    linarith
  have hne : x_eq + t • e ≠ x_eq := fun h => by
    rw [h, sub_self, norm_zero] at hnorm
    linarith
  exact ⟨x_eq + t • e, by rw [hnorm]; exact htε, hne, hP _ (by rw [hnorm]; exact htr) hne⟩

/-- **Chetaev on a punctured neighbourhood.** A `C¹` function vanishing at the point, positive
with positive derivative along a `C¹` field on a punctured neighbourhood, makes the point
unstable. -/
@[powerlib_foundation] theorem unstable_of_eventually_chetaev (hn : 0 < n) {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {W : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (hW : ContDiff ℝ 1 W) (hW0 : W x_eq = 0)
    (hpos : ∀ᶠ x in 𝓝[≠] x_eq, 0 < W x) (hLie : ∀ᶠ x in 𝓝[≠] x_eq, 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  obtain ⟨r, hr, hball⟩ := exists_radius_of_eventually hLie
  refine unstable_of_chetaev hf hW (half_pos hr) (fun ε hε => ?_) (fun x hx hWx => ?_)
  · obtain ⟨x, hx, -, hWx⟩ := exists_near_of_eventually hn hpos ε hε
    exact ⟨x, hx, hWx⟩
  · have hne : x ≠ x_eq := fun h => by rw [h, hW0] at hWx; exact lt_irrefl 0 hWx
    exact hball x (by linarith) hne

/-- **No attraction from a non-increasing function with lower values nearby** (eventual form). -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_eventually_lie_nonpos
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {V : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (hV : Differentiable ℝ V)
    (hLie : ∀ᶠ x in 𝓝 x_eq, fderiv ℝ V x (f x) ≤ 0) (hseed : ∃ᶠ x in 𝓝 x_eq, V x < V x_eq) :
    ¬ LocalAsymptoticStable f x_eq := by
  rw [Metric.eventually_nhds_iff] at hLie
  obtain ⟨ρ, hρ, hLieρ⟩ := hLie
  refine not_localAsymptoticStable_of_lie_nonpos hf hV hρ
    (fun x hx => hLieρ (by rwa [dist_eq_norm])) fun ε hε => ?_
  obtain ⟨x, hx, hVx⟩ := (hseed.and_eventually (Metric.ball_mem_nhds x_eq hε)).exists
  exact ⟨x, by rw [← dist_eq_norm]; exact hVx, hx⟩

/-- **Instability from a strictly decreasing function with lower values nearby.** If a `C¹`
function decreases strictly along a `C¹` field on a punctured neighbourhood of an equilibrium and
takes values below its value at the equilibrium at states arbitrarily close to it, the equilibrium
is unstable (`Dynamics.unstable_of_lie_nonpos_of_lie_pos` with `W = −E`). -/
@[powerlib_foundation] theorem unstable_of_eventually_lie_neg {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {E : ℝⁿ → ℝ} (hf : ContDiff ℝ 1 f) (hfx : f x_eq = 0) (hE : ContDiff ℝ 1 E)
    (hLie : ∀ᶠ x in 𝓝[≠] x_eq, fderiv ℝ E x (f x) < 0) (hseed : ∃ᶠ x in 𝓝 x_eq, E x < E x_eq) :
    Unstable f x_eq := by
  obtain ⟨r, hr, hball⟩ := exists_radius_of_eventually hLie
  have hLie0 : fderiv ℝ E x_eq (f x_eq) = 0 := by rw [hfx, map_zero]
  refine unstable_of_lie_nonpos_of_lie_pos (W := fun x => -E x) hf hE hE.neg (half_pos hr)
    (fun x hx => ?_) (fun ε hε => ?_) (fun x hx hEx => ?_)
  · by_cases hne : x = x_eq
    · rw [hne, hLie0]
    · exact (hball x (by linarith) hne).le
  · obtain ⟨x, hx, hEx⟩ := (hseed.and_eventually (Metric.ball_mem_nhds x_eq hε)).exists
    exact ⟨x, by rw [← dist_eq_norm]; exact hEx, hx⟩
  · have hne : x ≠ x_eq := fun h => by rw [h] at hEx; exact lt_irrefl _ hEx
    rw [fderiv_fun_neg]
    simp only [neg_apply, neg_pos]
    exact hball x (by linarith) hne

/-! ## Asymptotic bookkeeping -/

/-- `g = −q + o(q)` with `q > 0` eventually forces `g < 0` eventually. -/
@[powerlib_foundation] theorem eventually_neg_of_isLittleO {α : Type*} {l : Filter α}
    {g q : α → ℝ} (hq : ∀ᶠ x in l, 0 < q x) (h : (fun x => g x + q x) =o[l] q) :
    ∀ᶠ x in l, g x < 0 := by
  filter_upwards [hq, h.def (by norm_num : (0 : ℝ) < 1 / 2)] with x hqx hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqx] at hx
  have := le_abs_self (g x + q x)
  linarith

/-- `g = q + o(q)` with `q > 0` eventually forces `g > 0` eventually. -/
@[powerlib_foundation] theorem eventually_pos_of_isLittleO {α : Type*} {l : Filter α}
    {g q : α → ℝ} (hq : ∀ᶠ x in l, 0 < q x) (h : (fun x => g x - q x) =o[l] q) :
    ∀ᶠ x in l, 0 < g x := by
  filter_upwards [hq, h.def (by norm_num : (0 : ℝ) < 1 / 2)] with x hqx hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqx] at hx
  have := neg_abs_le (g x - q x)
  linarith

/-- Higher powers of a vanishing function are small: `s^k = o(s^m)` for `m < k`. -/
@[powerlib_foundation] theorem isLittleO_pow_of_tendsto {α : Type*} {l : Filter α}
    {s : α → ℝ} (hs : Tendsto s l (𝓝 0)) {m k : ℕ} (h : m < k) :
    (fun x => s x ^ k) =o[l] fun x => s x ^ m :=
  (isLittleO_pow_pow h).comp_tendsto hs

/-- Higher powers of a vanishing function are bounded by lower ones: `s^k = O(s^m)` for `m ≤ k`. -/
@[powerlib_foundation] theorem isBigO_pow_of_tendsto {α : Type*} {l : Filter α}
    {s : α → ℝ} (hs : Tendsto s l (𝓝 0)) {m k : ℕ} (h : m ≤ k) :
    (fun x => s x ^ k) =O[l] fun x => s x ^ m := by
  rcases h.lt_or_eq with h | h
  · exact (isLittleO_pow_of_tendsto hs h).isBigO
  · rw [h]

/-- A monomial in two functions that are `O(s)` is `O(s^{i+j})`. -/
@[powerlib_foundation] theorem isBigO_monomial {α : Type*} {l : Filter α} {s u v : α → ℝ}
    (hu : u =O[l] s) (hv : v =O[l] s) (i j : ℕ) :
    (fun x => u x ^ i * v x ^ j) =O[l] fun x => s x ^ (i + j) := by
  have := (hu.pow i).mul (hv.pow j)
  refine this.congr_right fun x => ?_
  rw [pow_add]

/-- A sign estimate `g ≤ −q + R` with `R = o(q)` and `q > 0` forces `g < 0` eventually. -/
@[powerlib_foundation] theorem eventually_neg_of_le_of_isLittleO {α : Type*} {l : Filter α}
    {g q R : α → ℝ} (hq : ∀ᶠ x in l, 0 < q x) (hle : ∀ᶠ x in l, g x ≤ -q x + R x)
    (hR : R =o[l] q) : ∀ᶠ x in l, g x < 0 := by
  filter_upwards [hq, hle, hR.def (by norm_num : (0 : ℝ) < 1 / 2)] with x hqx hgx hRx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqx] at hRx
  have := le_abs_self (R x)
  linarith

/-- States along a ray `t • d`, `t > 0`, accumulate at the origin. -/
@[powerlib_foundation] theorem frequently_of_forall_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) {P : E → Prop} (h : ∀ t : ℝ, 0 < t → P (t • d)) :
    ∃ᶠ z in 𝓝 (0 : E), P z := by
  rw [Filter.frequently_iff]
  intro U hU
  have hc : Tendsto (fun t : ℝ => t • d) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 ((0 : ℝ) • d)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, htU, ht⟩ := ((hc.eventually hU).and self_mem_nhdsWithin).exists
  exact ⟨t • d, htU, h t ht⟩

/-! ## Taylor remainders of `sin` and `cos` at `0` -/

/-- `1 − cos x = O(x²)`. -/
@[powerlib_foundation] theorem one_sub_cos_isBigO :
    (fun x : ℝ => 1 - Real.cos x) =O[𝓝 0] fun x => x ^ 2 := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := Real.cos_le_one x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (sq_nonneg x)]
  nlinarith [sq_nonneg x]

/-- `sin x − x = O(x³)`. -/
@[powerlib_foundation] theorem sin_sub_self_isBigO :
    (fun x : ℝ => Real.sin x - x) =O[𝓝 0] fun x => x ^ 3 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hb := Real.sin_bound hx.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have h5 : |x| ^ 5 ≤ |x| ^ 3 := pow_le_pow_of_le_one (abs_nonneg _) hx.le (by norm_num)
  have h3 : |x ^ 3 / 6| = |x| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  calc |Real.sin x - x| = |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by ring_nf
    _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := abs_sub _ _
    _ ≤ |x| ^ 3 := by
        have h0 : 0 ≤ |x| ^ 3 := by positivity
        rw [h3]; linarith

/-- `1 − cos x − x²/2 = O(x⁴)`. -/
@[powerlib_foundation] theorem one_sub_cos_sub_isBigO :
    (fun x : ℝ => 1 - Real.cos x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 4 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hb := Real.cos_bound hx.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have : |1 - Real.cos x - x ^ 2 / 2| = |Real.cos x - (1 - x ^ 2 / 2)| := by
    rw [← abs_neg]; ring_nf
  rw [this]
  have h4 : 0 ≤ |x| ^ 4 := by positivity
  linarith

end powerlib.Dynamics
