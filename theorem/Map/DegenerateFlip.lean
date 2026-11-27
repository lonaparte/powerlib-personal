import theorem.Periodic.CriticalMultiplier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # The degenerate flip: odd orders, the fifth-order coefficient, and flat jets

At a fixed point with multiplier `−1`, `r(x) = −x + c₂ x² + c₃ x³ + O(x⁴)`, the flip coefficient
`c₂² + c₃` decides stability (`Map.flip_localAsymptoticStable`, `Map.flip_unstable`). When it
vanishes the decision moves to higher order, and this module follows it there.

* **Parity.** If `r(x) = −x + O(x²)` and `r∘r(x) = x + κ xᵐ + O(x^{m+1})` with `κ ≠ 0`, then `m`
  is odd: `r` commutes with `r∘r`, and comparing `r(r∘r(x)) = r(x) − κ xᵐ + O(x^{m+1})` with
  `r∘r(r(x)) = r(x) + κ (−x)ᵐ + O(x^{m+1})` gives `κ (1 + (−1)ᵐ) = 0`. For this the map needs
  `r + id` to be flat to second order in the Lipschitz sense (`C²` maps are); for a map known
  only through a finite expansion `r(x) = −x + Σ_{2 ≤ j ≤ N} c_j xʲ + O(x^{N+1})` the jet of
  `r∘r` up to order `N` is the jet of the polynomial's second iterate, so the parity holds for
  every `m ≤ N` with no derivative hypothesis at all. The first nonvanishing coefficient of
  `r∘r − id` therefore always has odd order `2k + 1`.
* **Odd-order decision.** `r∘r(x) = x − κ x^{2k+1} + O(x^{2k+2})`, `k ≥ 1`: `κ > 0` gives local
  asymptotic stability (slow contraction of `r∘r`, and one step of `r` bounded linearly),
  `κ < 0` instability. The flip theorems are the case `k = 1`, `κ = 2(c₂² + c₃)`.
* **The fifth-order coefficient.** For `r(x) = −x + c₂x² + c₃x³ + c₄x⁴ + c₅x⁵ + O(x⁶)`,
  `r∘r(x) = x − 2(c₂² + c₃) x³ + c₂(c₂² + c₃) x⁴ + (3c₃² − c₂²c₃ − 6c₂c₄ − 2c₅) x⁵ + O(x⁶)`;
  the fourth-order coefficient vanishes with the flip coefficient, as the parity demands. At a
  degenerate flip `c₂² + c₃ = 0` this is `r∘r(x) = x − 2(c₅ + 3c₂c₄ − 2c₂⁴) x⁵ + O(x⁶)`: the
  fixed point is asymptotically (never exponentially) stable for `c₅ + 3c₂c₄ − 2c₂⁴ > 0` and
  unstable for `c₅ + 3c₂c₄ − 2c₂⁴ < 0`.
* **No finite jet decides.** The smooth maps `r_σ(y) = −(1 + σ e^{−1/‖y‖²}) y` (`flatFlip σ`)
  have the jet of `−y` to every order (`|r_σ(y) + y| ≤ |σ| N! |y|^N` for every `N`, `|y| ≤ 1`),
  and `r₀` is Lyapunov but not asymptotically stable, `r₋₁` asymptotically stable, `r₁`
  unstable. So the decision through the first odd coefficient is all a jet can give, and when
  every coefficient of `r∘r − id` vanishes the jet decides nothing.

Scope.
* Maps `F : ℝ¹ → ℝ¹` (`ℝ¹ = EuclideanSpace ℝ (Fin 1)`) with fixed point `0`, written in the
  coordinate `y 0`, with explicit remainder hypotheses `|F y 0 − (polynomial)| ≤ K |y 0|^j` on
  `‖y‖ ≤ ρ`, as in `theorem/Periodic/CriticalMultiplier.lean`; the map semantics of
  `theorem/Map/Defs.lean` (`Map.LyapunovStable`, `Map.LocalAsymptoticStable`,
  `Map.LocallyExponentiallyStable`, `Map.Unstable`). The slow-contraction criterion with a
  continuous modulus is on `ℝⁿ`.
* The parity theorem for maps (`odd_of_iterate_two`) assumes
  `|(F u + u) − (F x + x)| ≤ L (|u| + |x|) |u − x|` near `0` (true for `C²` maps with derivative
  `−1`); the jet form (`odd_of_jet`) assumes only the finite expansion of `F`.
* The reduction of a periodic orbit with a simple multiplier `−1` and a degenerate flip
  coefficient to these scalar maps is `theorem/Periodic/DegenerateFlipReduction.lean`.
* Generic; nothing here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §4.4 (the flip
bifurcation, the normal form `η ↦ −η + c η³` and its nondegeneracy condition) and §9.5
(degenerate flip, codimension two); Whitley, "Discrete dynamical systems in dimensions one and
two", Bull. London Math. Soc. 15 (1983) (stability of a fixed point with multiplier `−1` from the
first nonvanishing coefficient of the second iterate, which has odd order); Cauchy's flat function
`e^{−1/x²}`; the open item of `theorem/Periodic/FlipReduction.lean` (Scope: "`a² + b = 0` (a
degenerate flip) is not decided here").

Results.
* `localAsymptoticStable_of_norm_le_sub`: slow contraction `‖F y − x‖ ≤ ‖y − x‖ − ω(‖y − x‖)`
  with a continuous modulus `ω`, positive on `(0, ∞)`, gives local asymptotic stability (the
  power modulus `c tᵐ` is `Map.localAsymptoticStable_of_norm_le_sub_pow`).
* Odd-power normal forms: `oddPow_localAsymptoticStable` (`F y = y − κ y^{2k+1} + O(y^{2k+2})`,
  `κ > 0`), `oddPow_unstable` (`κ < 0`); for the second iterate:
  `localAsymptoticStable_of_iterate_two`, `unstable_of_iterate_two`.
* Composition: `iterate_two_sub_le` (`F = P + O(yᵐ)` with `P` Lipschitz near `0` gives
  `F∘F = P∘P + O(yᵐ)`), `abs_quintic_sub_le` (the quintic is Lipschitz on `[−1, 1]`),
  `quintic_iterate_two_le` (the polynomial identity for `P∘P` to order five),
  **`flip_second_iterate_five`**.
* **The degenerate flip**: `degenerateFlip_iterate_two` (`r∘r = y − 2(c₅ + 3c₂c₄ − 2c₂⁴) y⁵ +
  O(y⁶)` when `c₂² + c₃ = 0`), `degenerateFlip_localAsymptoticStable` (positive: locally
  asymptotically, not exponentially, stable), `degenerateFlip_unstable` (negative: unstable).
* **Parity**: `odd_of_iterate_two` (for maps with `r + id` flat to second order),
  `abs_sum_pow_sub_le` (the Lipschitz bound of a polynomial with no linear term), `odd_of_jet`
  (for finite expansions).
* **Flat jets**: `flatFlip`, `flatFlip_apply`, `contDiff_flatFlip`, `flatFlip_jet` (the jet of
  `−y` to every order), `flatFlip_zero_lyapunovStable`, `flatFlip_zero_not_localAsymptoticStable`,
  `flatFlip_neg_localAsymptoticStable`, `flatFlip_pos_unstable`, and `flat_jet_undecided`.

Corrections.
None: an extension (the degenerate flip `a² + b = 0`, which `theorem/Periodic/FlipReduction.lean`
left undecided).

Family and connection conclusions.
None: static evidence on maps.
-/

noncomputable section

namespace powerlib.Map

open Filter Topology

/-! ## Slow contraction with a continuous modulus -/

section Modulus

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Slow contraction with a continuous modulus.** If near `x` every step shortens the distance
to `x` by at least `ω(‖y − x‖)`, `ω` continuous, nonnegative on `[0, ∞)` and positive on
`(0, ∞)`, then `x` is locally asymptotically stable: the distances decrease to a limit `L` with
`ω(L) ≤ 0`, so `L = 0`. The modulus may be flat at `0` (`ω(t) = t e^{−1/t²}`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_norm_le_sub {F : ℝⁿ → ℝⁿ}
    {x : ℝⁿ} {r : ℝ} {ω : ℝ → ℝ} (hr : 0 < r) (hω : Continuous ω)
    (hnn : ∀ t, 0 ≤ t → 0 ≤ ω t) (hpos : ∀ t, 0 < t → 0 < ω t)
    (h : ∀ y, ‖y - x‖ < r → ‖F y - x‖ ≤ ‖y - x‖ - ω ‖y - x‖) :
    LocalAsymptoticStable F x := by
  have hstep : ∀ y, ‖y - x‖ < r → ‖F y - x‖ ≤ ‖y - x‖ := fun y hy => by
    have := hnn _ (norm_nonneg (y - x))
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
  have hlim2 : Tendsto (fun k => d k - ω (d k)) atTop (𝓝 (L - ω L)) :=
    hlim.sub ((hω.tendsto L).comp hlim)
  have hle : L ≤ L - ω L := le_of_tendsto_of_tendsto' hlim1 hlim2 fun k => by
    simp only [hd, Function.iterate_succ_apply']
    exact h _ (hdr k)
  have hL : L = 0 := by
    rcases hL0.lt_or_eq with hL | hL
    · have := hpos L hL; linarith
    · exact hL.symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [hL] at hlim
  exact hlim

end Modulus

/-! ## Odd-power normal forms -/

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- **Odd order, stable side.** `F(y) = y − κ y^{2k+1} + O(y^{2k+2})` (`k ≥ 1`,
`|F y 0 − (y 0 − κ y 0^{2k+1})| ≤ K |y 0|^{2k+2}` for `‖y‖ ≤ ρ`) with `κ > 0`: the fixed point
`0` is locally asymptotically stable, since `|F y| ≤ |y| − (κ/2) |y|^{2k+1}` near `0`. -/
@[tmio T, powerlib_foundation] theorem oddPow_localAsymptoticStable {F : ℝ¹ → ℝ¹} {κ K ρ : ℝ}
    {k : ℕ} (hk : 0 < k) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ →
      |F y 0 - (y 0 - κ * y 0 ^ (2 * k + 1))| ≤ K * |y 0| ^ (2 * k + 2)) :
    LocalAsymptoticStable F 0 := by
  set r := min ρ (min (1 / (κ + 1)) (κ / (2 * (|K| + 1)))) with hrdef
  have hr : 0 < r := lt_min hρ (lt_min (by positivity) (by positivity))
  refine localAsymptoticStable_of_norm_le_sub_pow (c := κ / 2) (m := 2 * k + 1) hr
    (by positivity) (by omega) fun y hy => ?_
  rw [sub_zero] at hy ⊢
  rw [sub_zero, NormalForm.norm_state1, NormalForm.norm_state1]
  rw [NormalForm.norm_state1] at hy
  set u := y 0 with hu
  set X := |u| with hX
  have hX0 : 0 ≤ X := abs_nonneg u
  have hXb : X ≤ 1 / (κ + 1) := hy.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hXK : X ≤ κ / (2 * (|K| + 1)) := hy.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hXρ : X ≤ ρ := hy.le.trans (min_le_left _ _)
  have h := hF y (by rw [NormalForm.norm_state1]; exact hXρ)
  rw [← hu] at h
  have hX1 : X ≤ 1 := hXb.trans (by rw [div_le_one (by positivity)]; linarith)
  have hu2 : u ^ (2 * k) = X ^ (2 * k) := (pow_abs_two_mul u).symm
  have h2k : X ^ (2 * k) ≤ X := pow_le_of_le_one hX0 hX1 (by omega)
  have hκX : κ * X ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hXb hκ.le
    have h' : κ * (1 / (κ + 1)) ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have hfac : |u - κ * u ^ (2 * k + 1)| = X - κ * X ^ (2 * k + 1) := by
    have e : u - κ * u ^ (2 * k + 1) = u * (1 - κ * u ^ (2 * k)) := by ring
    have hpos : 0 ≤ 1 - κ * u ^ (2 * k) := by
      rw [hu2]; nlinarith [mul_le_mul_of_nonneg_left h2k hκ.le]
    rw [e, abs_mul, abs_of_nonneg hpos, hu2]
    ring
  have hK4 : K * X ^ (2 * k + 2) ≤ κ / 2 * X ^ (2 * k + 1) := by
    have hKX : |K| * X ≤ κ / 2 := by
      have := mul_le_mul_of_nonneg_left hXK (abs_nonneg K)
      have h' : |K| * (κ / (2 * (|K| + 1))) ≤ κ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg K]
      linarith
    have h3 : 0 ≤ X ^ (2 * k + 1) := pow_nonneg hX0 _
    calc K * X ^ (2 * k + 2) ≤ |K| * X ^ (2 * k + 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ = (|K| * X) * X ^ (2 * k + 1) := by ring
      _ ≤ κ / 2 * X ^ (2 * k + 1) := mul_le_mul_of_nonneg_right hKX h3
  have htri := abs_sub_abs_le_abs_sub (F y 0) (u - κ * u ^ (2 * k + 1))
  rw [hfac] at htri
  have : |u| ^ (2 * k + 2) = X ^ (2 * k + 2) := rfl
  rw [this] at h
  linarith

/-- **Odd order, unstable side.** `F(y) = y − κ y^{2k+1} + O(y^{2k+2})` (`k ≥ 1`) with `κ < 0`:
the fixed point `0` is unstable, since `|F y| ≥ |y| + (|κ|/2) |y|^{2k+1}` near `0`. -/
@[tmio T, powerlib_foundation] theorem oddPow_unstable {F : ℝ¹ → ℝ¹} {κ K ρ : ℝ} {k : ℕ}
    (hρ : 0 < ρ) (hκ : κ < 0)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ →
      |F y 0 - (y 0 - κ * y 0 ^ (2 * k + 1))| ≤ K * |y 0| ^ (2 * k + 2)) :
    Unstable F 0 := by
  set β := -κ with hβdef
  have hβ : 0 < β := by linarith
  set r := min ρ (β / (2 * (|K| + 1))) with hrdef
  have hr : 0 < r := lt_min hρ (by positivity)
  refine unstable_of_norm_add_pow_le one_pos (c := β / 2) (m := 2 * k + 1) hr (by positivity)
    fun y hy => ?_
  rw [sub_zero] at hy ⊢
  rw [sub_zero, NormalForm.norm_state1, NormalForm.norm_state1]
  rw [NormalForm.norm_state1] at hy
  set u := y 0 with hu
  set X := |u| with hX
  have hX0 : 0 ≤ X := abs_nonneg u
  have hXK : X ≤ β / (2 * (|K| + 1)) := hy.le.trans (min_le_right _ _)
  have hXρ : X ≤ ρ := hy.le.trans (min_le_left _ _)
  have h := hF y (by rw [NormalForm.norm_state1]; exact hXρ)
  rw [← hu] at h
  have hu2 : u ^ (2 * k) = X ^ (2 * k) := (pow_abs_two_mul u).symm
  have hfac : |u - κ * u ^ (2 * k + 1)| = X + β * X ^ (2 * k + 1) := by
    have e : u - κ * u ^ (2 * k + 1) = u * (1 + β * u ^ (2 * k)) := by rw [hβdef]; ring
    have hpos : 0 ≤ 1 + β * u ^ (2 * k) := by rw [hu2]; positivity
    rw [e, abs_mul, abs_of_nonneg hpos, hu2]
    ring
  have hK4 : K * X ^ (2 * k + 2) ≤ β / 2 * X ^ (2 * k + 1) := by
    have hKX : |K| * X ≤ β / 2 := by
      have := mul_le_mul_of_nonneg_left hXK (abs_nonneg K)
      have h' : |K| * (β / (2 * (|K| + 1))) ≤ β / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg K]
      linarith
    have h3 : 0 ≤ X ^ (2 * k + 1) := pow_nonneg hX0 _
    calc K * X ^ (2 * k + 2) ≤ |K| * X ^ (2 * k + 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ = (|K| * X) * X ^ (2 * k + 1) := by ring
      _ ≤ β / 2 * X ^ (2 * k + 1) := mul_le_mul_of_nonneg_right hKX h3
  have htri := abs_sub_abs_le_abs_sub (u - κ * u ^ (2 * k + 1)) (F y 0)
  rw [hfac, abs_sub_comm] at htri
  have : |u| ^ (2 * k + 2) = X ^ (2 * k + 2) := rfl
  rw [this] at h
  linarith

/-- **Odd order of the second iterate, stable side.** If `F∘F(y) = y − κ y^{2k+1} +
O(y^{2k+2})` with `k ≥ 1`, `κ > 0`, and one step of `F` is bounded linearly near `0`, the fixed
point `0` of `F` is locally asymptotically stable. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_iterate_two {F : ℝ¹ → ℝ¹}
    {κ K ρ r C : ℝ} {k : ℕ} (hk : 0 < k) (hρ : 0 < ρ) (hκ : 0 < κ) (hr : 0 < r)
    (hlin : ∀ y : ℝ¹, ‖y‖ < r → ‖F y‖ ≤ C * ‖y‖)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ →
      |F^[2] y 0 - (y 0 - κ * y 0 ^ (2 * k + 1))| ≤ K * |y 0| ^ (2 * k + 2)) :
    LocalAsymptoticStable F 0 :=
  (oddPow_localAsymptoticStable hk hρ hκ hF).of_iterate two_pos hr fun y hy => by
    simpa using hlin y (by simpa using hy)

/-- **Odd order of the second iterate, unstable side.** If `F∘F(y) = y − κ y^{2k+1} +
O(y^{2k+2})` with `κ < 0`, the fixed point `0` of `F` is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_iterate_two {F : ℝ¹ → ℝ¹} {κ K ρ : ℝ}
    {k : ℕ} (hρ : 0 < ρ) (hκ : κ < 0)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ →
      |F^[2] y 0 - (y 0 - κ * y 0 ^ (2 * k + 1))| ≤ K * |y 0| ^ (2 * k + 2)) :
    Unstable F 0 :=
  Unstable.of_iterate (oddPow_unstable hρ hκ hF)

/-! ## The second iterate to fifth order -/

/-- **Composing approximations.** If `F(y) = P(y 0) + O(|y 0|^m)` (`m ≥ 1`) on `‖y‖ ≤ ρ`, and `P`
fixes `0` and is `L`-Lipschitz on `[−ρ, ρ]`, then `F∘F(y) = P(P(y 0)) + O(|y 0|^m)` near `0`. -/
@[tmio T, powerlib_foundation] theorem iterate_two_sub_le {F : ℝ¹ → ℝ¹} {P : ℝ → ℝ} {K L ρ : ℝ}
    {m : ℕ} (hm : 0 < m) (hρ : 0 < ρ) (hP0 : P 0 = 0)
    (hP : ∀ a b : ℝ, |a| ≤ ρ → |b| ≤ ρ → |P a - P b| ≤ L * |a - b|)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - P (y 0)| ≤ K * |y 0| ^ m) :
    ∃ ρ' > 0, ∃ K', ∀ y : ℝ¹, ‖y‖ ≤ ρ' → |F^[2] y 0 - P (P (y 0))| ≤ K' * |y 0| ^ m := by
  set N := |L| + |K| + 1 with hN
  have hL0 := abs_nonneg L
  have hK0 := abs_nonneg K
  have hN1 : 1 ≤ N := by linarith
  refine ⟨min 1 (ρ / N), lt_min one_pos (div_pos hρ (by linarith)), |K| * N ^ m + |L| * |K|,
    fun y hy => ?_⟩
  rw [NormalForm.norm_state1] at hy
  set u := y 0 with hu
  have hu0 := abs_nonneg u
  have hu1 : |u| ≤ 1 := hy.trans (min_le_left _ _)
  have huN : |u| ≤ ρ / N := hy.trans (min_le_right _ _)
  have huρ : |u| ≤ ρ := huN.trans (div_le_self hρ.le hN1)
  have hNu : N * |u| ≤ ρ := by rwa [le_div_iff₀ (by linarith), mul_comm] at huN
  have hPu : |P u| ≤ |L| * |u| := by
    have := hP u 0 huρ (by simp [hρ.le])
    rw [hP0, sub_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self L) hu0)
  have hum : |u| ^ m ≤ |u| := pow_le_of_le_one hu0 hu1 (by omega)
  have h1 := hF y (by rw [NormalForm.norm_state1]; exact huρ)
  rw [← hu] at h1
  have hKu : K * |u| ^ m ≤ |K| * |u| :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hum hK0)
  have hFy : |F y 0| ≤ N * |u| := by
    have := abs_sub_abs_le_abs_sub (F y 0) (P u)
    have : |F y 0| ≤ |P u| + K * |u| ^ m := by linarith
    nlinarith
  have hFyρ : ‖F y‖ ≤ ρ := by rw [NormalForm.norm_state1]; linarith
  have h2 := hF (F y) hFyρ
  have h3 := hP (F y 0) (P u) (by linarith) (hPu.trans (by nlinarith))
  rw [show F^[2] y = F (F y) from rfl]
  have e1 : K * |F y 0| ^ m ≤ |K| * N ^ m * |u| ^ m := by
    calc K * |F y 0| ^ m ≤ |K| * |F y 0| ^ m :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ |K| * (N * |u|) ^ m := by gcongr
      _ = |K| * N ^ m * |u| ^ m := by rw [mul_pow, mul_assoc]
  have e2 : L * |F y 0 - P u| ≤ |L| * |K| * |u| ^ m := by
    calc L * |F y 0 - P u| ≤ |L| * |F y 0 - P u| :=
          mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
      _ ≤ |L| * (K * |u| ^ m) := by gcongr
      _ ≤ |L| * (|K| * |u| ^ m) := by
          gcongr; exact le_abs_self K
      _ = |L| * |K| * |u| ^ m := by ring
  calc |F (F y) 0 - P (P u)| = |(F (F y) 0 - P (F y 0)) + (P (F y 0) - P (P u))| := by
        rw [sub_add_sub_cancel]
    _ ≤ |F (F y) 0 - P (F y 0)| + |P (F y 0) - P (P u)| := abs_add_le _ _
    _ ≤ |K| * N ^ m * |u| ^ m + |L| * |K| * |u| ^ m := add_le_add (h2.trans e1) (h3.trans e2)
    _ = (|K| * N ^ m + |L| * |K|) * |u| ^ m := by ring

/-- The quintic `P(t) = −t + c₂t² + c₃t³ + c₄t⁴ + c₅t⁵` is Lipschitz on `[−1, 1]` with constant
`1 + 2|c₂| + 3|c₃| + 4|c₄| + 5|c₅|`. -/
@[tmio T, powerlib_foundation] theorem abs_quintic_sub_le (c₂ c₃ c₄ c₅ : ℝ) {a b : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |(-a + c₂ * a ^ 2 + c₃ * a ^ 3 + c₄ * a ^ 4 + c₅ * a ^ 5) -
        (-b + c₂ * b ^ 2 + c₃ * b ^ 3 + c₄ * b ^ 4 + c₅ * b ^ 5)| ≤
      (1 + 2 * |c₂| + 3 * |c₃| + 4 * |c₄| + 5 * |c₅|) * |a - b| := by
  have hpow : ∀ j : ℕ, |a ^ j - b ^ j| ≤ j * |a - b| := fun j => by
    have h := abs_pow_sub_pow_le (a := a) (b := b) (n := j)
    have hmax : max |a| |b| ^ (j - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg a))
      (max_le ha hb)
    calc |a ^ j - b ^ j| ≤ |a - b| * j * max |a| |b| ^ (j - 1) := h
      _ ≤ |a - b| * j * 1 := by gcongr
      _ = j * |a - b| := by ring
  have e : (-a + c₂ * a ^ 2 + c₃ * a ^ 3 + c₄ * a ^ 4 + c₅ * a ^ 5) -
      (-b + c₂ * b ^ 2 + c₃ * b ^ 3 + c₄ * b ^ 4 + c₅ * b ^ 5) =
      -(a - b) + c₂ * (a ^ 2 - b ^ 2) + c₃ * (a ^ 3 - b ^ 3) + c₄ * (a ^ 4 - b ^ 4) +
        c₅ * (a ^ 5 - b ^ 5) := by ring
  rw [e]
  have t2 : |c₂ * (a ^ 2 - b ^ 2)| ≤ 2 * |c₂| * |a - b| := by
    rw [abs_mul]; have := hpow 2; push_cast at this
    nlinarith [abs_nonneg c₂]
  have t3 : |c₃ * (a ^ 3 - b ^ 3)| ≤ 3 * |c₃| * |a - b| := by
    rw [abs_mul]; have := hpow 3; push_cast at this
    nlinarith [abs_nonneg c₃]
  have t4 : |c₄ * (a ^ 4 - b ^ 4)| ≤ 4 * |c₄| * |a - b| := by
    rw [abs_mul]; have := hpow 4; push_cast at this
    nlinarith [abs_nonneg c₄]
  have t5 : |c₅ * (a ^ 5 - b ^ 5)| ≤ 5 * |c₅| * |a - b| := by
    rw [abs_mul]; have := hpow 5; push_cast at this
    nlinarith [abs_nonneg c₅]
  calc |-(a - b) + c₂ * (a ^ 2 - b ^ 2) + c₃ * (a ^ 3 - b ^ 3) + c₄ * (a ^ 4 - b ^ 4) +
        c₅ * (a ^ 5 - b ^ 5)|
      ≤ |-(a - b)| + |c₂ * (a ^ 2 - b ^ 2)| + |c₃ * (a ^ 3 - b ^ 3)| +
          |c₄ * (a ^ 4 - b ^ 4)| + |c₅ * (a ^ 5 - b ^ 5)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ |a - b| + 2 * |c₂| * |a - b| + 3 * |c₃| * |a - b| + 4 * |c₄| * |a - b| +
          5 * |c₅| * |a - b| := by rw [abs_neg]; linarith
    _ = (1 + 2 * |c₂| + 3 * |c₃| + 4 * |c₄| + 5 * |c₅|) * |a - b| := by ring

/-- **The polynomial identity for the second iterate to fifth order.** For the quintic
`P(t) = −t + c₂t² + c₃t³ + c₄t⁴ + c₅t⁵`, `P(P(u)) − (u − 2(c₂² + c₃)u³ + c₂(c₂² + c₃)u⁴ +
(3c₃² − c₂²c₃ − 6c₂c₄ − 2c₅)u⁵) = u⁶ Q(u)` with a polynomial `Q`, so it is at most `C |u|⁶` on
`[−1, 1]`. -/
@[tmio T, powerlib_foundation] theorem quintic_iterate_two_le {P : ℝ → ℝ} {c₂ c₃ c₄ c₅ : ℝ}
    (hP : ∀ t, P t = -t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 + c₅ * t ^ 5) :
    ∃ C, ∀ u : ℝ, |u| ≤ 1 →
      |P (P u) - (u - 2 * (c₂ ^ 2 + c₃) * u ^ 3 + c₂ * (c₂ ^ 2 + c₃) * u ^ 4 +
        (3 * c₃ ^ 2 - c₂ ^ 2 * c₃ - 6 * c₂ * c₄ - 2 * c₅) * u ^ 5)| ≤ C * |u| ^ 6 := by
  -- `s(u) = c₂ + c₃u + c₄u² + c₅u³`, `P(u) = −u + u² s(u)`
  set s : ℝ → ℝ := fun u => c₂ + c₃ * u + c₄ * u ^ 2 + c₅ * u ^ 3 with hs
  set Q : ℝ → ℝ := fun u =>
    (2 * c₂ ^ 2 * c₄ - 5 * c₂ * c₃ ^ 2 - 2 * c₂ * c₅ - c₃ * c₄) - 3 * c₃ * c₅ ^ 2 * u ^ 5 +
      u ^ 4 * (c₂ * c₅ ^ 2 - 6 * c₃ * c₄ * c₅) +
      u ^ 3 * (2 * c₂ * c₄ * c₅ - 6 * c₃ ^ 2 * c₅ - 3 * c₃ * c₄ ^ 2) +
      u ^ 2 * (-4 * c₂ * c₃ * c₅ + c₂ * c₄ ^ 2 - 6 * c₃ ^ 2 * c₄ - 4 * c₄ * c₅) +
      u * (2 * c₂ ^ 2 * c₅ - 4 * c₂ * c₃ * c₄ - 3 * c₃ ^ 3 + 3 * c₃ * c₅ - 4 * c₄ ^ 2) +
      (c₃ * s u ^ 3 + c₄ * (6 * s u ^ 2 - 4 * u * s u ^ 3 + u ^ 2 * s u ^ 4) +
        c₅ * (5 * s u - 10 * u * s u ^ 2 + 10 * u ^ 2 * s u ^ 3 - 5 * u ^ 3 * s u ^ 4 +
          u ^ 4 * s u ^ 5)) with hQ
  have hid : ∀ u, P (P u) - (u - 2 * (c₂ ^ 2 + c₃) * u ^ 3 + c₂ * (c₂ ^ 2 + c₃) * u ^ 4 +
      (3 * c₃ ^ 2 - c₂ ^ 2 * c₃ - 6 * c₂ * c₄ - 2 * c₅) * u ^ 5) = u ^ 6 * Q u := fun u => by
    simp only [hP, hQ, hs]
    ring
  have hQc : Continuous Q := by rw [hQ, hs]; fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hQc.continuousOn
  refine ⟨C, fun u hu => ?_⟩
  rw [hid, abs_mul, abs_pow, mul_comm]
  have := hC u (Set.mem_Icc.mpr (abs_le.mp hu))
  rw [Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **The second iterate of a flip map to fifth order.** If
`F(y) = −y + c₂y² + c₃y³ + c₄y⁴ + c₅y⁵ + O(y⁶)` (`|F y 0 − (…)| ≤ K |y 0|⁶` for `‖y‖ ≤ ρ`), then
near `0`
`F∘F(y) = y − 2(c₂² + c₃) y³ + c₂(c₂² + c₃) y⁴ + (3c₃² − c₂²c₃ − 6c₂c₄ − 2c₅) y⁵ + O(y⁶)`. -/
@[tmio T, powerlib_foundation] theorem flip_second_iterate_five {F : ℝ¹ → ℝ¹}
    {c₂ c₃ c₄ c₅ K ρ : ℝ} (hρ : 0 < ρ)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + c₂ * y 0 ^ 2 + c₃ * y 0 ^ 3 + c₄ * y 0 ^ 4 +
      c₅ * y 0 ^ 5)| ≤ K * |y 0| ^ 6) :
    ∃ ρ' > 0, ∃ K', ∀ y : ℝ¹, ‖y‖ ≤ ρ' →
      |F^[2] y 0 - (y 0 - 2 * (c₂ ^ 2 + c₃) * y 0 ^ 3 + c₂ * (c₂ ^ 2 + c₃) * y 0 ^ 4 +
        (3 * c₃ ^ 2 - c₂ ^ 2 * c₃ - 6 * c₂ * c₄ - 2 * c₅) * y 0 ^ 5)| ≤ K' * |y 0| ^ 6 := by
  set P : ℝ → ℝ := fun t => -t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 + c₅ * t ^ 5 with hPdef
  have hP : ∀ t, P t = -t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 + c₅ * t ^ 5 := fun t => rfl
  set ρ₁ := min ρ 1 with hρ₁
  have hρ₁0 : 0 < ρ₁ := lt_min hρ one_pos
  obtain ⟨ρ', hρ', K', hK'⟩ := iterate_two_sub_le (F := F) (P := P) (K := K)
    (L := 1 + 2 * |c₂| + 3 * |c₃| + 4 * |c₄| + 5 * |c₅|) (m := 6) (by norm_num) hρ₁0
    (by simp [hPdef])
    (fun a b ha hb => abs_quintic_sub_le c₂ c₃ c₄ c₅ (ha.trans (min_le_right _ _))
      (hb.trans (min_le_right _ _)))
    (fun y hy => hF y (hy.trans (min_le_left _ _)))
  obtain ⟨C, hC⟩ := quintic_iterate_two_le hP
  refine ⟨min ρ' 1, lt_min hρ' one_pos, K' + C, fun y hy => ?_⟩
  have h1 := hK' y (hy.trans (min_le_left _ _))
  have hu1 : |y 0| ≤ 1 := by rw [← NormalForm.norm_state1]; exact hy.trans (min_le_right _ _)
  have h2 := hC (y 0) hu1
  calc _ = |(F^[2] y 0 - P (P (y 0))) + (P (P (y 0)) - (y 0 - 2 * (c₂ ^ 2 + c₃) * y 0 ^ 3 +
          c₂ * (c₂ ^ 2 + c₃) * y 0 ^ 4 +
          (3 * c₃ ^ 2 - c₂ ^ 2 * c₃ - 6 * c₂ * c₄ - 2 * c₅) * y 0 ^ 5))| := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ K' * |y 0| ^ 6 + C * |y 0| ^ 6 := add_le_add h1 h2
    _ = (K' + C) * |y 0| ^ 6 := by ring

/-! ## The degenerate flip -/

/-- **The degenerate flip, the second iterate.** If `F(y) = −y + c₂y² + c₃y³ + c₄y⁴ + c₅y⁵ +
O(y⁶)` with a vanishing flip coefficient `c₂² + c₃ = 0`, then
`F∘F(y) = y − 2(c₅ + 3c₂c₄ − 2c₂⁴) y⁵ + O(y⁶)` near `0`. -/
@[tmio T, powerlib_foundation] theorem degenerateFlip_iterate_two {F : ℝ¹ → ℝ¹}
    {c₂ c₃ c₄ c₅ K ρ : ℝ} (hρ : 0 < ρ) (hdeg : c₂ ^ 2 + c₃ = 0)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + c₂ * y 0 ^ 2 + c₃ * y 0 ^ 3 + c₄ * y 0 ^ 4 +
      c₅ * y 0 ^ 5)| ≤ K * |y 0| ^ 6) :
    ∃ ρ' > 0, ∃ K', ∀ y : ℝ¹, ‖y‖ ≤ ρ' →
      |F^[2] y 0 - (y 0 - 2 * (c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4) * y 0 ^ 5)| ≤
        K' * |y 0| ^ 6 := by
  obtain ⟨ρ', hρ', K', hK'⟩ := flip_second_iterate_five hρ hF
  refine ⟨ρ', hρ', K', fun y hy => ?_⟩
  have e : y 0 - 2 * (c₂ ^ 2 + c₃) * y 0 ^ 3 + c₂ * (c₂ ^ 2 + c₃) * y 0 ^ 4 +
      (3 * c₃ ^ 2 - c₂ ^ 2 * c₃ - 6 * c₂ * c₄ - 2 * c₅) * y 0 ^ 5 =
      y 0 - 2 * (c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4) * y 0 ^ 5 := by
    rw [show c₃ = -c₂ ^ 2 by linarith]; ring
  rw [← e]
  exact hK' y hy

/-- One step of a flip map is bounded linearly and differs from `−y` by `O(y²)`. -/
@[tmio T, powerlib_foundation] private theorem quintic_step {F : ℝ¹ → ℝ¹} {c₂ c₃ c₄ c₅ K ρ : ℝ}
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + c₂ * y 0 ^ 2 + c₃ * y 0 ^ 3 + c₄ * y 0 ^ 4 +
      c₅ * y 0 ^ 5)| ≤ K * |y 0| ^ 6) (y : ℝ¹) (hy : ‖y‖ ≤ min ρ 1) :
    |F y 0 - (-1) * y 0| ≤ (|c₂| + |c₃| + |c₄| + |c₅| + |K|) * |y 0| ^ 2 ∧
      ‖F y‖ ≤ (1 + |c₂| + |c₃| + |c₄| + |c₅| + |K|) * ‖y‖ := by
  rw [NormalForm.norm_state1] at hy ⊢
  rw [NormalForm.norm_state1]
  set u := y 0 with hu
  have hu0 := abs_nonneg u
  have hu1 : |u| ≤ 1 := hy.trans (min_le_right _ _)
  have h := hF y (by rw [NormalForm.norm_state1]; exact hy.trans (min_le_left _ _))
  rw [← hu] at h
  have p3 : |u| ^ 3 ≤ |u| ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have p4 : |u| ^ 4 ≤ |u| ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have p5 : |u| ^ 5 ≤ |u| ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have p6 : |u| ^ 6 ≤ |u| ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have p2 : |u| ^ 2 ≤ |u| := pow_le_of_le_one hu0 hu1 (by norm_num)
  have hK : K * |u| ^ 6 ≤ |K| * |u| ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
      (mul_le_mul_of_nonneg_left p6 (abs_nonneg K))
  have hq : |c₂ * u ^ 2 + c₃ * u ^ 3 + c₄ * u ^ 4 + c₅ * u ^ 5| ≤
      (|c₂| + |c₃| + |c₄| + |c₅|) * |u| ^ 2 := by
    calc |c₂ * u ^ 2 + c₃ * u ^ 3 + c₄ * u ^ 4 + c₅ * u ^ 5|
        ≤ |c₂ * u ^ 2| + |c₃ * u ^ 3| + |c₄ * u ^ 4| + |c₅ * u ^ 5| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ = |c₂| * |u| ^ 2 + |c₃| * |u| ^ 3 + |c₄| * |u| ^ 4 + |c₅| * |u| ^ 5 := by
          simp only [abs_mul, abs_pow]
      _ ≤ |c₂| * |u| ^ 2 + |c₃| * |u| ^ 2 + |c₄| * |u| ^ 2 + |c₅| * |u| ^ 2 := by gcongr
      _ = (|c₂| + |c₃| + |c₄| + |c₅|) * |u| ^ 2 := by ring
  have e : F y 0 - (-1) * u =
      (F y 0 - (-u + c₂ * u ^ 2 + c₃ * u ^ 3 + c₄ * u ^ 4 + c₅ * u ^ 5)) +
        (c₂ * u ^ 2 + c₃ * u ^ 3 + c₄ * u ^ 4 + c₅ * u ^ 5) := by ring
  have h1 : |F y 0 - (-1) * u| ≤ (|c₂| + |c₃| + |c₄| + |c₅| + |K|) * |u| ^ 2 := by
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith
  refine ⟨h1, ?_⟩
  have h2 : |F y 0| ≤ |u| + |F y 0 - (-1) * u| := by
    have := abs_sub_abs_le_abs_sub (F y 0) ((-1) * u)
    rw [abs_mul, abs_neg, abs_one, one_mul] at this
    linarith
  have h3 : (|c₂| + |c₃| + |c₄| + |c₅| + |K|) * |u| ^ 2 ≤
      (|c₂| + |c₃| + |c₄| + |c₅| + |K|) * |u| := by
    gcongr
  nlinarith

/-- **Degenerate flip, stable side.** If `F(y) = −y + c₂y² + c₃y³ + c₄y⁴ + c₅y⁵ + O(y⁶)` with
`c₂² + c₃ = 0` and `c₅ + 3c₂c₄ − 2c₂⁴ > 0`, the fixed point `0` is locally asymptotically stable
(the second iterate is `y − 2(c₅ + 3c₂c₄ − 2c₂⁴) y⁵ + O(y⁶)`), and not exponentially stable (the
multiplier `−1`). -/
@[tmio T, powerlib_foundation] theorem degenerateFlip_localAsymptoticStable {F : ℝ¹ → ℝ¹}
    {c₂ c₃ c₄ c₅ K ρ : ℝ} (hρ : 0 < ρ) (hdeg : c₂ ^ 2 + c₃ = 0)
    (hκ : 0 < c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + c₂ * y 0 ^ 2 + c₃ * y 0 ^ 3 + c₄ * y 0 ^ 4 +
      c₅ * y 0 ^ 5)| ≤ K * |y 0| ^ 6) :
    LocalAsymptoticStable F 0 ∧ ¬ LocallyExponentiallyStable F 0 := by
  obtain ⟨ρ', hρ', K', hK'⟩ := degenerateFlip_iterate_two hρ hdeg hF
  have hρ1 : 0 < min ρ 1 := lt_min hρ one_pos
  refine ⟨localAsymptoticStable_of_iterate_two (k := 2) (κ := 2 * (c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4))
    (K := K') (by norm_num) hρ' (by positivity) hρ1 (C := 1 + |c₂| + |c₃| + |c₄| + |c₅| + |K|)
    (fun y hy => (quintic_step hF y hy.le).2) hK', ?_⟩
  exact critical_not_locallyExponentiallyStable hρ1 (by norm_num : |(-1 : ℝ)| = 1)
    fun y hy => (quintic_step hF y hy).1

/-- **Degenerate flip, unstable side.** If `F(y) = −y + c₂y² + c₃y³ + c₄y⁴ + c₅y⁵ + O(y⁶)` with
`c₂² + c₃ = 0` and `c₅ + 3c₂c₄ − 2c₂⁴ < 0`, the fixed point `0` is unstable. -/
@[tmio T, powerlib_foundation] theorem degenerateFlip_unstable {F : ℝ¹ → ℝ¹}
    {c₂ c₃ c₄ c₅ K ρ : ℝ} (hρ : 0 < ρ) (hdeg : c₂ ^ 2 + c₃ = 0)
    (hκ : c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4 < 0)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F y 0 - (-y 0 + c₂ * y 0 ^ 2 + c₃ * y 0 ^ 3 + c₄ * y 0 ^ 4 +
      c₅ * y 0 ^ 5)| ≤ K * |y 0| ^ 6) :
    Unstable F 0 := by
  obtain ⟨ρ', hρ', K', hK'⟩ := degenerateFlip_iterate_two hρ hdeg hF
  exact unstable_of_iterate_two (k := 2) (κ := 2 * (c₅ + 3 * c₂ * c₄ - 2 * c₂ ^ 4)) hρ'
    (by linarith) hK'

/-! ## Parity: the first nonvanishing coefficient of `r∘r − id` has odd order -/

/-- The size of a point close to `t + κ tᵐ`: `|σ − t| ≤ (|κ| + |K|) |t|ᵐ` and
`|σ| ≤ (1 + |κ| + |K|) |t|` for `|t| ≤ 1`, `m ≥ 1`. -/
@[tmio T, powerlib_foundation] private theorem near_bounds {κ K t σ : ℝ} {m : ℕ} (hm : 0 < m)
    (ht1 : |t| ≤ 1) (h : |σ - (t + κ * t ^ m)| ≤ K * |t| ^ (m + 1)) :
    |σ - t| ≤ (|κ| + |K|) * |t| ^ m ∧ |σ| ≤ (1 + |κ| + |K|) * |t| := by
  have hT0 := abs_nonneg t
  have hTm : |t| ^ m ≤ |t| := pow_le_of_le_one hT0 ht1 (by omega)
  have hTm1 : |t| ^ (m + 1) ≤ |t| ^ m := pow_le_pow_of_le_one hT0 ht1 (by omega)
  have h1 : |σ - t| ≤ (|κ| + |K|) * |t| ^ m := by
    have e : σ - t = (σ - (t + κ * t ^ m)) + κ * t ^ m := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_pow]
    have : K * |t| ^ (m + 1) ≤ |K| * |t| ^ m :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hTm1 (abs_nonneg K))
    linarith
  refine ⟨h1, ?_⟩
  have := abs_sub_abs_le_abs_sub σ t
  have : (|κ| + |K|) * |t| ^ m ≤ (|κ| + |K|) * |t| := mul_le_mul_of_nonneg_left hTm (by positivity)
  linarith

/-- The comparison at the heart of the parity theorem, for real numbers: with
`σ ≈ t + κ tᵐ` (the second iterate of `t`), `ζ ≈ −t` (its first iterate), `A ≈ ζ + t − σ` (one
step from `σ`) and `B ≈ ζ + κ ζᵐ` (two steps from `ζ`), `A = B` forces
`|κ| |1 + (−1)ᵐ| |t|ᵐ ≤ C |t|^{m+1}`. -/
@[tmio T, powerlib_foundation] private theorem parity_core {κ K L t σ ζ A B : ℝ} {m : ℕ}
    (hm : 0 < m) (ht1 : |t| ≤ 1) (hAB : A = B)
    (h1 : |σ - (t + κ * t ^ m)| ≤ K * |t| ^ (m + 1))
    (h2 : |(A + σ) - (ζ + t)| ≤ L * (|σ| + |t|) * |σ - t|)
    (h3 : |ζ + t| ≤ L * (|t| + |(0 : ℝ)|) * |t - 0|)
    (h4 : |B - (ζ + κ * ζ ^ m)| ≤ K * |ζ| ^ (m + 1)) :
    |κ| * |1 + (-1) ^ m| * |t| ^ m ≤
      (|L| * (2 + |κ| + |K|) * (|κ| + |K|) + |K| + |K| * (1 + |L|) ^ (m + 1) +
        |κ| * (m * |L| * (1 + |L|) ^ (m - 1))) * |t| ^ (m + 1) := by
  set T := |t| with hT
  have hT0 : 0 ≤ T := abs_nonneg t
  have hL0 := abs_nonneg L
  have hK0 := abs_nonneg K
  obtain ⟨hσt, hσn⟩ := near_bounds hm ht1 h1
  rw [abs_zero, add_zero, sub_zero] at h3
  have hζt : |ζ + t| ≤ |L| * T ^ 2 := by
    calc |ζ + t| ≤ L * T * T := h3
      _ ≤ |L| * T * T := by gcongr; exact le_abs_self L
      _ = |L| * T ^ 2 := by ring
  have hζn : |ζ| ≤ (1 + |L|) * T := by
    have := abs_sub_abs_le_abs_sub ζ (-t)
    rw [abs_neg, sub_neg_eq_add] at this
    have : |L| * T ^ 2 ≤ |L| * T := by
      gcongr; exact pow_le_of_le_one hT0 ht1 (by norm_num)
    linarith
  have hE1 : |(A + σ) - (ζ + t)| ≤ |L| * (2 + |κ| + |K|) * (|κ| + |K|) * T ^ (m + 1) := by
    calc _ ≤ L * (|σ| + T) * |σ - t| := h2
      _ ≤ |L| * (|σ| + T) * |σ - t| := by gcongr; exact le_abs_self L
      _ ≤ |L| * ((1 + |κ| + |K|) * T + T) * ((|κ| + |K|) * T ^ m) := by gcongr
      _ = |L| * (2 + |κ| + |K|) * (|κ| + |K|) * T ^ (m + 1) := by ring
  have hE2 : |B - (ζ + κ * ζ ^ m)| ≤ |K| * (1 + |L|) ^ (m + 1) * T ^ (m + 1) := by
    calc _ ≤ K * |ζ| ^ (m + 1) := h4
      _ ≤ |K| * |ζ| ^ (m + 1) := by gcongr; exact le_abs_self K
      _ ≤ |K| * ((1 + |L|) * T) ^ (m + 1) := by gcongr
      _ = |K| * (1 + |L|) ^ (m + 1) * T ^ (m + 1) := by rw [mul_pow, mul_assoc]
  have hpow : |ζ ^ m - (-t) ^ m| ≤ m * |L| * (1 + |L|) ^ (m - 1) * T ^ (m + 1) := by
    have h := abs_pow_sub_pow_le ζ (-t) m
    rw [sub_neg_eq_add, abs_neg] at h
    have hmax : max |ζ| T ≤ (1 + |L|) * T := max_le hζn (by nlinarith)
    have e : T ^ 2 * T ^ (m - 1) = T ^ (m + 1) := by rw [← pow_add]; congr 1; omega
    calc _ ≤ |ζ + t| * m * max |ζ| T ^ (m - 1) := h
      _ ≤ (|L| * T ^ 2) * m * ((1 + |L|) * T) ^ (m - 1) := by gcongr
      _ = m * |L| * (1 + |L|) ^ (m - 1) * (T ^ 2 * T ^ (m - 1)) := by rw [mul_pow]; ring
      _ = m * |L| * (1 + |L|) ^ (m - 1) * T ^ (m + 1) := by rw [e]
  have h1' : |σ - (t + κ * t ^ m)| ≤ |K| * T ^ (m + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  have t4 : |κ * (ζ ^ m - (-t) ^ m)| ≤ |κ| * (m * |L| * (1 + |L|) ^ (m - 1)) * T ^ (m + 1) := by
    rw [abs_mul, mul_assoc]; gcongr
  have hsum : κ * t ^ m * (1 + (-1) ^ m) =
      ((A + σ) - (ζ + t)) - (σ - (t + κ * t ^ m)) - (B - (ζ + κ * ζ ^ m)) -
        κ * (ζ ^ m - (-t) ^ m) := by
    rw [← hAB, neg_pow]; ring
  have hfin : |κ * t ^ m * (1 + (-1) ^ m)| ≤
      (|L| * (2 + |κ| + |K|) * (|κ| + |K|) + |K| + |K| * (1 + |L|) ^ (m + 1) +
        |κ| * (m * |L| * (1 + |L|) ^ (m - 1))) * T ^ (m + 1) := by
    rw [hsum]
    have a1 := abs_sub (((A + σ) - (ζ + t)) - (σ - (t + κ * t ^ m)) - (B - (ζ + κ * ζ ^ m)))
      (κ * (ζ ^ m - (-t) ^ m))
    have a2 := abs_sub (((A + σ) - (ζ + t)) - (σ - (t + κ * t ^ m))) (B - (ζ + κ * ζ ^ m))
    have a3 := abs_sub ((A + σ) - (ζ + t)) (σ - (t + κ * t ^ m))
    nlinarith
  rw [abs_mul, abs_mul, abs_pow] at hfin
  calc |κ| * |1 + (-1) ^ m| * T ^ m = |κ| * T ^ m * |1 + (-1) ^ m| := by ring
    _ ≤ _ := hfin

/-- **Parity of the second iterate.** Let `F(0) = 0` with `r + id` flat to second order near `0`,
`|(F u + u) − (F x + x)| ≤ L (|u| + |x|) |u − x|` (as for a `C²` map with derivative `−1`). If
`F∘F(x) = x + κ xᵐ + O(x^{m+1})` with `κ ≠ 0`, then `m` is odd. `F` commutes with `F∘F`:
`F(F∘F(x)) = F(x) − κ xᵐ + O(x^{m+1})` and `F∘F(F(x)) = F(x) + κ (−x)ᵐ + O(x^{m+1})`, so
`κ (1 + (−1)ᵐ) = 0`. -/
@[tmio T, powerlib_foundation] theorem odd_of_iterate_two {F : ℝ¹ → ℝ¹} {L K κ ρ : ℝ} {m : ℕ}
    (hρ : 0 < ρ) (hF0 : F 0 = 0)
    (hφ : ∀ u x : ℝ¹, ‖u‖ ≤ ρ → ‖x‖ ≤ ρ →
      |(F u 0 + u 0) - (F x 0 + x 0)| ≤ L * (|u 0| + |x 0|) * |u 0 - x 0|)
    (hF2 : ∀ x : ℝ¹, ‖x‖ ≤ ρ → |F^[2] x 0 - (x 0 + κ * x 0 ^ m)| ≤ K * |x 0| ^ (m + 1))
    (hκ : κ ≠ 0) : Odd m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exfalso
    have := hF2 0 (by simp [hρ.le])
    rw [Function.iterate_fixed hF0 2] at this
    simp only [PiLp.zero_apply, pow_zero, mul_one, zero_add, zero_sub, abs_neg, abs_zero,
      zero_pow (one_ne_zero), mul_zero] at this
    exact hκ (abs_nonpos_iff.mp this)
  have hL0 := abs_nonneg L
  have hK0 := abs_nonneg K
  have hκ0 := abs_nonneg κ
  set N := 1 + |κ| + |K| with hN
  set δ := min 1 (ρ / (N + |L| + 1)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hρ (by linarith))
  set C := |L| * (2 + |κ| + |K|) * (|κ| + |K|) + |K| + |K| * (1 + |L|) ^ (m + 1) +
    |κ| * (m * |L| * (1 + |L|) ^ (m - 1)) with hC
  have hC0 : 0 ≤ C := by positivity
  -- the main estimate along the curve `t ↦ embed t`
  have key : ∀ t : ℝ, |t| ≤ δ → |κ| * |1 + (-1) ^ m| * |t| ^ m ≤ C * |t| ^ (m + 1) := by
    intro t ht
    have hT0 : 0 ≤ |t| := abs_nonneg t
    have hT1 : |t| ≤ 1 := ht.trans (min_le_left _ _)
    have hNT : (N + |L| + 1) * |t| ≤ ρ := by
      have := ht.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by linarith), mul_comm] at this
    obtain ⟨x, hx0, hxn⟩ : ∃ x : ℝ¹, x 0 = t ∧ ‖x‖ = |t| :=
      ⟨NormalForm.embed t, NormalForm.embed_apply t 0, NormalForm.norm_embed t⟩
    have hxρ : ‖x‖ ≤ ρ := by rw [hxn]; nlinarith
    have h1 := hF2 x hxρ
    rw [hx0] at h1
    obtain ⟨-, hσn⟩ := near_bounds hm hT1 h1
    have hsρ : ‖F^[2] x‖ ≤ ρ := by rw [NormalForm.norm_state1]; nlinarith
    have h3 := hφ x 0 hxρ (by simp [hρ.le])
    rw [hF0, hx0] at h3
    simp only [PiLp.zero_apply, add_zero] at h3
    have hζn : |F x 0| ≤ (1 + |L|) * |t| := by
      have hζt : |F x 0 + t| ≤ |L| * |t| := by
        calc |F x 0 + t| ≤ L * (|t| + |(0 : ℝ)|) * |t - 0| := by simpa using h3
          _ = L * |t| * |t| := by simp
          _ ≤ |L| * |t| * 1 := by gcongr; exact le_abs_self L
          _ = |L| * |t| := by ring
      have := abs_sub_abs_le_abs_sub (F x 0) (-t)
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    have hzρ : ‖F x‖ ≤ ρ := by rw [NormalForm.norm_state1]; nlinarith
    have h2 := hφ (F^[2] x) x hsρ hxρ
    rw [hx0] at h2
    have h4 := hF2 (F x) hzρ
    have hcomm : F (F^[2] x) = F^[2] (F x) := by
      rw [← Function.iterate_succ_apply' F 2 x, Function.iterate_succ_apply]
    exact parity_core hm hT1 (congrArg (· 0) hcomm) h1 h2 (by simpa using h3) h4
  -- `κ (1 + (−1)ᵐ) = 0`
  have hzero : |κ| * |1 + (-1 : ℝ) ^ m| = 0 := by
    by_contra hne
    have hc0 : 0 < |κ| * |1 + (-1 : ℝ) ^ m| := lt_of_le_of_ne (by positivity) (Ne.symm hne)
    set t := min δ (|κ| * |1 + (-1 : ℝ) ^ m| / (2 * (C + 1))) with ht
    have ht0 : 0 < t := lt_min hδ0 (by positivity)
    have h1 := key t (by rw [abs_of_pos ht0]; exact min_le_left _ _)
    rw [abs_of_pos ht0, pow_succ] at h1
    have h2 : |κ| * |1 + (-1 : ℝ) ^ m| ≤ C * t := by
      have htm : 0 < t ^ m := pow_pos ht0 m
      nlinarith
    have h3 : C * t ≤ C * (|κ| * |1 + (-1 : ℝ) ^ m| / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hC0
    have h4 : C * (|κ| * |1 + (-1 : ℝ) ^ m| / (2 * (C + 1))) < |κ| * |1 + (-1 : ℝ) ^ m| := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have h1 : 1 + (-1 : ℝ) ^ m = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (abs_eq_zero.mp h) hκ
    · exact abs_eq_zero.mp h
  exact (neg_one_pow_eq_neg_one_iff_odd (R := ℝ) (by norm_num)).mp (by linarith)

/-- A polynomial without constant and linear terms is flat to second order on `[−1, 1]`:
`|Σ c_j aʲ − Σ c_j bʲ| ≤ (Σ |c_j| j) (|a| + |b|) |a − b|` when every exponent is at least `2`. -/
@[tmio T, powerlib_foundation] theorem abs_sum_pow_sub_le {s : Finset ℕ} (hs : ∀ j ∈ s, 2 ≤ j)
    (c : ℕ → ℝ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |∑ j ∈ s, c j * a ^ j - ∑ j ∈ s, c j * b ^ j| ≤
      (∑ j ∈ s, |c j| * j) * (|a| + |b|) * |a - b| := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hmax0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
  have hmax1 : max |a| |b| ≤ 1 := max_le ha hb
  have hpow : max |a| |b| ^ (j - 1) ≤ |a| + |b| :=
    (pow_le_of_le_one hmax0 hmax1 (by have := hs j hj; omega)).trans
      (max_le (by linarith [abs_nonneg b]) (by linarith [abs_nonneg a]))
  rw [← mul_sub, abs_mul]
  calc |c j| * |a ^ j - b ^ j| ≤ |c j| * (|a - b| * j * max |a| |b| ^ (j - 1)) :=
        mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le a b j) (abs_nonneg _)
    _ ≤ |c j| * (|a - b| * j * (|a| + |b|)) := by gcongr
    _ = |c j| * j * (|a| + |b|) * |a - b| := by ring

/-- **Parity of the jet.** If `F(y) = −y + Σ_{2 ≤ j ≤ N} c_j yʲ + O(y^{N+1})` and
`F∘F(y) = y + κ yᵐ + O(y^{m+1})` with `m ≤ N` and `κ ≠ 0`, then `m` is odd. No derivative of `F`
is assumed: up to order `N` the second iterate is that of the polynomial, to which
`odd_of_iterate_two` applies. -/
@[tmio T, powerlib_foundation] theorem odd_of_jet {F : ℝ¹ → ℝ¹} {c : ℕ → ℝ} {N m : ℕ}
    {K K' κ ρ : ℝ} (hρ : 0 < ρ) (hm : m ≤ N)
    (hF : ∀ y : ℝ¹, ‖y‖ ≤ ρ →
      |F y 0 - (-y 0 + ∑ j ∈ Finset.Icc 2 N, c j * y 0 ^ j)| ≤ K * |y 0| ^ (N + 1))
    (hF2 : ∀ y : ℝ¹, ‖y‖ ≤ ρ → |F^[2] y 0 - (y 0 + κ * y 0 ^ m)| ≤ K' * |y 0| ^ (m + 1))
    (hκ : κ ≠ 0) : Odd m := by
  have hs : ∀ j ∈ Finset.Icc 2 N, 2 ≤ j := fun j hj => (Finset.mem_Icc.mp hj).1
  set P : ℝ → ℝ := fun t => -t + ∑ j ∈ Finset.Icc 2 N, c j * t ^ j with hPdef
  set Lc := ∑ j ∈ Finset.Icc 2 N, |c j| * j with hLc
  have hLc0 : 0 ≤ Lc := Finset.sum_nonneg fun j _ => by positivity
  have hP0 : P 0 = 0 := by
    simp only [hPdef, neg_zero, zero_add]
    exact Finset.sum_eq_zero fun j hj => by
      rw [zero_pow (by have := hs j hj; omega), mul_zero]
  have hPflat : ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 →
      |(P a + a) - (P b + b)| ≤ Lc * (|a| + |b|) * |a - b| := fun a b ha hb => by
    have := abs_sum_pow_sub_le hs c ha hb
    simp only [hPdef]
    convert this using 2
    ring
  have hPlip : ∀ a b : ℝ, |a| ≤ min ρ 1 → |b| ≤ min ρ 1 →
      |P a - P b| ≤ (1 + 2 * Lc) * |a - b| := fun a b ha hb => by
    have ha1 : |a| ≤ 1 := ha.trans (min_le_right _ _)
    have hb1 : |b| ≤ 1 := hb.trans (min_le_right _ _)
    have h1 := hPflat a b ha1 hb1
    have e : P a - P b = ((P a + a) - (P b + b)) - (a - b) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have : Lc * (|a| + |b|) * |a - b| ≤ Lc * 2 * |a - b| := by
      gcongr; linarith
    linarith
  obtain ⟨ρ', hρ', K'', hK''⟩ := iterate_two_sub_le (F := F) (P := P) (K := K)
    (m := N + 1) (by omega) (lt_min hρ one_pos) hP0 hPlip
    (fun y hy => hF y (hy.trans (min_le_left _ _)))
  set G : ℝ¹ → ℝ¹ := NormalForm.lift P with hG
  have hGapp : ∀ y : ℝ¹, G y 0 = P (y 0) := fun y => NormalForm.lift_apply P y 0
  have hG2 : ∀ y : ℝ¹, G^[2] y 0 = P (P (y 0)) := fun y => by
    show G (G y) 0 = _
    rw [hGapp, hGapp]
  have hG0 : G 0 = 0 := by
    rw [hG]; ext i; fin_cases i; simp [hP0]
  set ρ₀ := min ρ' (min ρ 1) with hρ₀
  have hρ₀0 : 0 < ρ₀ := lt_min hρ' (lt_min hρ one_pos)
  refine odd_of_iterate_two (F := G) (L := Lc) (K := |K''| + K') (κ := κ) hρ₀0 hG0
    (fun u x hu hx => ?_) (fun x hx => ?_) hκ
  · rw [hGapp, hGapp]
    have hu1 : |u 0| ≤ 1 := by
      rw [← NormalForm.norm_state1]; exact hu.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hx1 : |x 0| ≤ 1 := by
      rw [← NormalForm.norm_state1]; exact hx.trans ((min_le_right _ _).trans (min_le_right _ _))
    exact hPflat _ _ hu1 hx1
  · rw [hG2]
    have hx1 : |x 0| ≤ 1 := by
      rw [← NormalForm.norm_state1]; exact hx.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h1 := hK'' x (hx.trans (min_le_left _ _))
    have h2 := hF2 x (hx.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hpow : |x 0| ^ (N + 1) ≤ |x 0| ^ (m + 1) :=
      pow_le_pow_of_le_one (abs_nonneg _) hx1 (by omega)
    have h1' : |F^[2] x 0 - P (P (x 0))| ≤ |K''| * |x 0| ^ (m + 1) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self K'') (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg K'')))
    calc |P (P (x 0)) - (x 0 + κ * x 0 ^ m)|
        = |(P (P (x 0)) - F^[2] x 0) + (F^[2] x 0 - (x 0 + κ * x 0 ^ m))| := by
          rw [sub_add_sub_cancel]
      _ ≤ |P (P (x 0)) - F^[2] x 0| + |F^[2] x 0 - (x 0 + κ * x 0 ^ m)| := abs_add_le _ _
      _ ≤ |K''| * |x 0| ^ (m + 1) + K' * |x 0| ^ (m + 1) := by
          rw [abs_sub_comm]; exact add_le_add h1' h2
      _ = (|K''| + K') * |x 0| ^ (m + 1) := by ring

/-! ## Flat jets: no finite expansion decides -/

/-- The flat perturbations of `−y`: `r_σ(y) = −(1 + σ e^{−1/‖y‖²}) y`, with Cauchy's flat function
`expNegInvGlue s = e^{−1/s}` for `s > 0` (and `0` for `s ≤ 0`). -/
def flatFlip (σ : ℝ) (y : ℝ¹) : ℝ¹ := (-(1 + σ * expNegInvGlue (‖y‖ ^ 2))) • y

@[tmio T, powerlib_foundation] theorem flatFlip_apply (σ : ℝ) (y : ℝ¹) :
    flatFlip σ y 0 = -(1 + σ * expNegInvGlue (‖y‖ ^ 2)) * y 0 := by
  simp [flatFlip]

/-- Cauchy's flat function stays below `1`. -/
@[tmio T, powerlib_foundation] private theorem expNegInvGlue_lt_one (s : ℝ) :
    expNegInvGlue s < 1 := by
  unfold expNegInvGlue
  split_ifs with hs
  · norm_num
  · push Not at hs
    exact Real.exp_lt_one_iff.mpr (by have := inv_pos.mpr hs; linarith)

@[tmio T, powerlib_foundation] private theorem norm_flatFlip {σ : ℝ} (hσ : |σ| ≤ 1) (y : ℝ¹) :
    ‖flatFlip σ y‖ = (1 + σ * expNegInvGlue (‖y‖ ^ 2)) * ‖y‖ := by
  have h0 := expNegInvGlue.nonneg (‖y‖ ^ 2)
  have h1 := expNegInvGlue_lt_one (‖y‖ ^ 2)
  have hpos : 0 ≤ 1 + σ * expNegInvGlue (‖y‖ ^ 2) := by
    have : -1 ≤ σ := (abs_le.mp hσ).1
    nlinarith
  rw [flatFlip, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hpos]

/-- The flat perturbations are smooth: `C^n` for every `n ≤ ∞`. -/
@[tmio T, powerlib_foundation] theorem contDiff_flatFlip (σ : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (flatFlip σ) := by
  have h1 : ContDiff ℝ n (fun y : ℝ¹ => expNegInvGlue (‖y‖ ^ 2)) :=
    expNegInvGlue.contDiff.comp (contDiff_norm_sq ℝ)
  exact ((contDiff_const.add (contDiff_const.mul h1)).neg).smul contDiff_id

/-- **The jet of `−y` to every order.** `|r_σ(y) + y| ≤ |σ| N! |y|^N` for every `N` and
`‖y‖ ≤ 1` (`e^{−1/s} ≤ N! s^N`): every finite expansion `r_σ(y) = −y + O(|y|^N)` holds, with all
nonlinear coefficients `0`. -/
@[tmio T, powerlib_foundation] theorem flatFlip_jet (σ : ℝ) (N : ℕ) (y : ℝ¹) (hy : ‖y‖ ≤ 1) :
    |flatFlip σ y 0 - (-y 0)| ≤ |σ| * N.factorial * |y 0| ^ N := by
  rw [flatFlip_apply]
  set u := y 0 with hu
  have hyu : ‖y‖ = |u| := NormalForm.norm_state1 y
  have hu1 : |u| ≤ 1 := by rw [← hyu]; exact hy
  have hu0 := abs_nonneg u
  set ψ := expNegInvGlue (‖y‖ ^ 2) with hψ
  have hψ0 : 0 ≤ ψ := expNegInvGlue.nonneg _
  have hψb : ψ ≤ N.factorial * |u| ^ (2 * N) := by
    rcases hu0.lt_or_eq with hpos | h0
    · have hs : 0 < ‖y‖ ^ 2 := by rw [hyu]; positivity
      have hψe : ψ = Real.exp (-(‖y‖ ^ 2)⁻¹) := by
        simp only [hψ, expNegInvGlue, not_le.mpr hs, ite_false]
      have hexp := Real.pow_div_factorial_le_exp _ (inv_pos.mpr hs).le N
      have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
      rw [hψe, Real.exp_neg]
      have hsN : (0 : ℝ) < ((‖y‖ ^ 2)⁻¹) ^ N := by positivity
      have hinv : (Real.exp (‖y‖ ^ 2)⁻¹)⁻¹ ≤ ((‖y‖ ^ 2)⁻¹ ^ N / N.factorial)⁻¹ :=
        inv_anti₀ (by positivity) hexp
      refine hinv.trans (le_of_eq ?_)
      rw [inv_div, inv_pow, div_inv_eq_mul, hyu, ← pow_mul]
    · have : ‖y‖ = 0 := by rw [hyu, ← h0]
      rw [hψ, this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, expNegInvGlue.zero]
      positivity
  have e : -(1 + σ * ψ) * u - -u = -(σ * ψ * u) := by ring
  rw [e, abs_neg, abs_mul, abs_mul, abs_of_nonneg hψ0]
  have hpow : |u| ^ (2 * N) * |u| ≤ |u| ^ N := by
    rw [← pow_succ]; exact pow_le_pow_of_le_one hu0 hu1 (by omega)
  calc |σ| * ψ * |u| ≤ |σ| * (N.factorial * |u| ^ (2 * N)) * |u| := by gcongr
    _ = |σ| * N.factorial * (|u| ^ (2 * N) * |u|) := by ring
    _ ≤ |σ| * N.factorial * |u| ^ N := by gcongr

/-- `r₀ = −id` is Lyapunov stable at `0`: every orbit keeps its norm. -/
@[tmio T, powerlib_foundation] theorem flatFlip_zero_lyapunovStable :
    LyapunovStable (flatFlip 0) 0 := by
  have hk : ∀ (k : ℕ) (y : ℝ¹), ‖(flatFlip 0)^[k] y‖ = ‖y‖ := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply', norm_flatFlip (by norm_num), ih]
      ring
  exact fun ε hε => ⟨ε, hε, fun y hy k => by rw [sub_zero] at hy ⊢; rw [hk]; exact hy⟩

/-- `r₀ = −id` is not asymptotically stable: no orbit other than `0` converges. -/
@[tmio T, powerlib_foundation] theorem flatFlip_zero_not_localAsymptoticStable :
    ¬ LocalAsymptoticStable (flatFlip 0) 0 := by
  rintro ⟨-, c, hc, hatt⟩
  have hk : ∀ (k : ℕ) (y : ℝ¹), ‖(flatFlip 0)^[k] y‖ = ‖y‖ := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply', norm_flatFlip (by norm_num), ih]
      ring
  set y : ℝ¹ := NormalForm.embed (c / 2) with hy
  have hyn : ‖y‖ = c / 2 := by rw [hy, NormalForm.norm_embed, abs_of_pos (half_pos hc)]
  have hlim := (hatt y (by rw [sub_zero, hyn]; linarith)).norm
  rw [norm_zero] at hlim
  simp only [hk, hyn] at hlim
  exact (half_pos hc).ne' (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- `r₋₁(y) = −(1 − e^{−1/‖y‖²}) y` is locally asymptotically stable at `0`: each step shortens
the norm by the flat modulus `ω(t) = t e^{−1/t²}`. -/
@[tmio T, powerlib_foundation] theorem flatFlip_neg_localAsymptoticStable :
    LocalAsymptoticStable (flatFlip (-1)) 0 := by
  have hc : Continuous expNegInvGlue := (expNegInvGlue.contDiff (n := 0)).continuous
  refine localAsymptoticStable_of_norm_le_sub (n := 1) (r := 1)
    (ω := fun t => t * expNegInvGlue (t ^ 2)) one_pos
    (continuous_id.mul (hc.comp (continuous_pow 2)))
    (fun t ht => mul_nonneg ht (expNegInvGlue.nonneg _))
    (fun t ht => mul_pos ht (expNegInvGlue.pos_of_pos (by positivity))) fun y _ => ?_
  rw [sub_zero, sub_zero, norm_flatFlip (by norm_num)]
  apply le_of_eq
  ring

/-- `r₁(y) = −(1 + e^{−1/‖y‖²}) y` is unstable at `0`: from `y₀ ≠ 0` the norm grows at least by
the factor `1 + e^{−1/‖y₀‖²}` per step. -/
@[tmio T, powerlib_foundation] theorem flatFlip_pos_unstable : Unstable (flatFlip 1) 0 := by
  intro hLS
  obtain ⟨δ, hδ, hb⟩ := hLS 1 one_pos
  set s₀ := min δ 1 / 2 with hs₀
  have hs₀0 : 0 < s₀ := by positivity
  have hs₀δ : s₀ < δ := by
    have := min_le_left δ 1; rw [hs₀]; linarith
  set y₀ : ℝ¹ := NormalForm.embed s₀ with hy₀
  have hy₀n : ‖y₀‖ = s₀ := by rw [hy₀, NormalForm.norm_embed, abs_of_pos hs₀0]
  set ψ₀ := expNegInvGlue (s₀ ^ 2) with hψ₀
  have hψ₀0 : 0 < ψ₀ := expNegInvGlue.pos_of_pos (by positivity)
  have hgrow : ∀ k : ℕ, (1 + ψ₀) ^ k * s₀ ≤ ‖(flatFlip 1)^[k] y₀‖ := by
    intro k
    induction k with
    | zero => simp [hy₀n]
    | succ k ih =>
      rw [Function.iterate_succ_apply', norm_flatFlip (by norm_num)]
      set z := (flatFlip 1)^[k] y₀
      have hz : s₀ ≤ ‖z‖ := le_trans (le_mul_of_one_le_left hs₀0.le
        (one_le_pow₀ (by linarith))) ih
      have hψ : ψ₀ ≤ expNegInvGlue (‖z‖ ^ 2) :=
        expNegInvGlue.monotone (pow_le_pow_left₀ hs₀0.le hz 2)
      calc (1 + ψ₀) ^ (k + 1) * s₀ = (1 + ψ₀) * ((1 + ψ₀) ^ k * s₀) := by ring
        _ ≤ (1 + ψ₀) * ‖z‖ := by gcongr
        _ ≤ (1 + 1 * expNegInvGlue (‖z‖ ^ 2)) * ‖z‖ := by
            gcongr; linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / s₀) (by linarith : (1 : ℝ) < 1 + ψ₀)
  have h1 := hb y₀ (by rw [sub_zero, hy₀n]; exact hs₀δ) k
  rw [sub_zero] at h1
  have h2 := hgrow k
  rw [div_lt_iff₀ hs₀0] at hk
  linarith

/-- **No finite jet decides.** The smooth maps `r_σ(y) = −(1 + σ e^{−1/‖y‖²}) y` have the jet of
`−y` to every order, `|r_σ(y) + y| ≤ |σ| N! |y|^N` (so `r_σ(y) = −y + O(|y|^N)` for every `N`,
every nonlinear coefficient `0`, and `r_σ∘r_σ − id` is flat as well), while `r₀` is Lyapunov
but not asymptotically stable, `r₋₁` is locally asymptotically stable and `r₁` is unstable. -/
@[tmio T, powerlib_foundation] theorem flat_jet_undecided :
    (∀ (σ : ℝ) (n : ℕ∞), ContDiff ℝ n (flatFlip σ)) ∧
    (∀ (σ : ℝ) (N : ℕ) (y : ℝ¹), ‖y‖ ≤ 1 →
      |flatFlip σ y 0 - (-y 0)| ≤ |σ| * N.factorial * |y 0| ^ N) ∧
    (LyapunovStable (flatFlip 0) 0 ∧ ¬ LocalAsymptoticStable (flatFlip 0) 0) ∧
    LocalAsymptoticStable (flatFlip (-1)) 0 ∧ Unstable (flatFlip 1) 0 :=
  ⟨contDiff_flatFlip, flatFlip_jet, ⟨flatFlip_zero_lyapunovStable,
    flatFlip_zero_not_localAsymptoticStable⟩, flatFlip_neg_localAsymptoticStable,
    flatFlip_pos_unstable⟩

end powerlib.Map
