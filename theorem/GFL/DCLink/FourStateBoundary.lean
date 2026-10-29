import theorem.GFL.DCLink.FourState
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability

/-! # Four-state GFL: the boundary of the quartic Routh region

Model boundary.
The four-state GFL family `GFL.DCLink.FourState.family`: a single
grid-following VSC on an infinite ac source of amplitude `V₀` behind a lossless reactance `X_g`,
balanced averaged dq model in the PLL frame, algebraic network, ideal current loop, constant grid
angle, continuous time; states in order `θ` (PLL error angle), `x` (PLL integrator), `V` (dc-bus
voltage, p.u.), `η` (dc-voltage PI integrator); port current IN-positive, absorbed power
`P_abs = (3/2) v_d i_d`, `i_q = 0`; the full nonlinear field with its `1 / V` term, read at the
selected operating point `(θ₀, 0, 1, 0)` moved to the origin. No PWM, delay, limiter, line
resistance or current-loop dynamics. The named members, all at `θ₀ = 0` with `V₀ = 1`,
`i_{d0} = I_dc0 = 0`, `C = 3/2` (so `γ = 1`):
* `weakFocus`: `X_g = k_p = k_iv = 1`, `k_i = 2`, `k_pv = 0`. In translated coordinates
  `(θ, x, u, η)`, `u = V − 1`, its field is `θ̇ = −sin θ + η + 2x`, `ẋ = −sin θ + η`,
  `u̇ = −cos θ · η / (1 + u)`, `η̇ = u`; quartic `(λ² + 1)(λ² + λ + 2)`.
* `FourState.undampedPLL`: `X_g = k_p = 0`, `k_i = k_pv = k_iv = 1`; quartic
  `(λ² + 1)(λ² + λ + 1)`.
* `frozenPLL`: `X_g = k_p = k_i = 0`, `k_pv = k_iv = 1`; quartic `λ² (λ² + λ + 1)`.
All three are equilibria with `C ≠ 0` whose quartic lies on the boundary of the Routh region
(closed conditions hold, a strict one fails).

Source: work-sync `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2, §2.3 (the
four-state model); the first Lyapunov coefficient and the averaging correction were computed by
averaging over the dc oscillation (local SymPy note), and every inequality is checked here by the
Lean kernel.

Results.
* `closedRouth_of_mem_den_lyapunovStable` (and
  `closedRouth_of_mem_den_locallyAsymptoticallyStable`): every Lyapunov stable model has
  `C ≠ 0` (otherwise `W = (V − 1) η` is a Chetaev function), an equilibrium at the selected
  point (`IsEq`), and quartic coefficients in the closed Routh region
  `a₃, a₂, a₁, a₀ ≥ 0`, `a₁² + a₃² a₀ ≤ a₃ a₂ a₁` (a strict violation gives an eigenvalue with
  positive real part, `Criteria.unstable_of_jacobian_quartic_violation`). With
  `FourState.chain_le_semantics`, the Lyapunov and local asymptotic denotations therefore lie
  between the strict and the closed Routh sets (with equilibrium and `C ≠ 0`).
* `weakFocus_mem_den_locallyAsymptoticallyStable`: `weakFocus` is locally asymptotically stable
  (hence Lyapunov stable). The dc loop is undamped (`k_pv + i_{d0} = 0`, imaginary pair `±i`),
  the PLL is Hurwitz, and the coupling `X_g` lets the nonlinear terms decide (a weak focus). The
  certificate is a composite Lyapunov function `W = E + Q + (1/500) ξᵀ P ξ`:
  - `E = u²/2 + u³/3 + η²/2`, the exact dc energy, `Ė = η u (1 − cos θ)` (the `1 / V` term is
    exactly conservative);
  - `ξ = (θ + u/2 − 3η/2, x − u/2 − η/2)`, the deviation of the PLL from its linear response to
    the dc oscillation (`θ = −u/2 + 3η/2`, `x = u/2 + η/2`), and
    `P = [[3/4, −1/4], [−1/4, 7/4]]` with `A_pᵀ P + P A_p = −I` for the PLL matrix
    `A_p = [[−1, 2], [−1, 0]]`;
  - `Q = (u⁴ − 3u³η + 3uη³ − 9η⁴)/32`, the averaging correction: along the linear rotation
    `u̇ = −η`, `η̇ = u` it cancels the oscillating part of `η u θ_lin²/2`, leaving its average
    `−(3/32)(u² + η²)²` (negative first Lyapunov coefficient: the PLL lags the dc oscillation by
    `φ` with `sin 2φ = 3/5`).
  On the ball of radius `1/1000` the derivative of `W` is at most
  `−(3/64)(u² + η²)² − (1/2000)|ξ|²` (Taylor bounds `Real.sin_bound`, `Real.cos_bound`;
  private `lie_bound`), and `W ≥ (u² + η²)/4 + |ξ|²/1000` (private `wf_lower`), so
  `Dynamics.localAsymptoticStable_of_lie_neg` applies (the field is continuous on the ball, where
  it agrees with the smooth `FourState.regField`).
* `not_exact_locallyAsymptoticallyStable`: the local asymptotic translation of the family
  (equilibrium and the strict quartic Routh conditions) is sound (`FourState.chain_le_semantics`)
  but not exact: for `weakFocus`, `a₁² + a₃² a₀ = a₃ a₂ a₁ = 3`.
* `undampedPLL_not_mem_den_locallyAsymptoticallyStable`: `FourState.undampedPLL` (Lyapunov
  stable) is not locally asymptotically stable: its decoupled PLL conserves
  `1 − cos θ + x²/2` (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`).
* `frozenPLL_mem_den_unstable`: `frozenPLL` is unstable: `W = −x sin θ` has `Ẇ = sin² θ`
  (`Dynamics.unstable_of_chetaev`).
* Inexpressibility, `realize_ne_den_lyapunovStable`, `realize_ne_den_locallyAsymptoticallyStable`,
  `realize_ne_den_unstable`: for every set `T` of requirements, `TMIO.realize Meets T` differs from
  the Lyapunov, local asymptotic and instability denotations. `undampedPLL` and `frozenPLL` meet
  exactly the same requirements (equilibrium, neither Routh nor `a₀ < 0`) but only the first is
  Lyapunov stable; `weakFocus` and `undampedPLL` meet the same requirements but only the first is
  locally asymptotically stable. So no translation into the requirement language of the family
  (equilibrium, strict Routh, `a₀ < 0`) is exact for these sentences; in particular
  `FourState.not_exact_lyapunovStable`, `FourState.not_exact_unstable` and
  `not_exact_locallyAsymptoticallyStable` are instances.

Family and connection conclusions.
No new family: all results are connection statements on `FourState.family` (memberships and
inclusions of its generated denotations, comparisons with the generated requirement spaces); the
polynomial estimates are private implementation evidence.

Remaining exact set (not characterized here). Let `S` be the translation set
`{IsEq, C ≠ 0, strict Routh conditions}` and `B = {IsEq, C ≠ 0, closed Routh conditions} \ S`
the Routh boundary. For `P` Lyapunov or local asymptotic stability, `den P = S ∪ (den P ∩ B)`,
and the instability denotation is the complement of the Lyapunov one. On `B` membership is
decided by the nonlinear terms (first Lyapunov coefficients at Hopf points, centre-manifold
reductions at zero eigenvalues, higher codimension); `den P ∩ B` and `B \ den P` are both
nonempty for both sentences, and the requirement language cannot separate them.
-/

noncomputable section
namespace powerlib.GFL.DCLink.FourStateBoundary
open FourState Set

/-! ## Polynomial estimates near the origin (implementation evidence)

Variables: `θ, x, u, η` the translated state, `s = sin θ`, `c = cos θ`, `w = (1 + u)⁻¹`,
`a, b` the PLL deviation `ξ`, `R = u² + η²`, `X = |ξ|²`, `t = −u/2 + 3η/2` the linear slaving of
`θ`. -/

@[tmio T]
private theorem bP1 {η u c θ R X : ℝ} (hηu : |η * u| ≤ R / 2)
    (hc : |1 - c - θ ^ 2 / 2| ≤ θ ^ 4 * (5 / 96)) (hθ4 : θ ^ 4 ≤ X / 10000 + 25 * R ^ 2)
    (hR0 : 0 ≤ R) (hRle : R ≤ 1 / 1000000) (hX0 : 0 ≤ X) :
    η * u * (1 - c - θ ^ 2 / 2) ≤ R ^ 2 / 100000 + X / 100000 := by
  have h1 : η * u * (1 - c - θ ^ 2 / 2) ≤ R / 2 * (θ ^ 4 * (5 / 96)) := by
    calc η * u * (1 - c - θ ^ 2 / 2) ≤ |η * u * (1 - c - θ ^ 2 / 2)| := le_abs_self _
      _ = |η * u| * |1 - c - θ ^ 2 / 2| := abs_mul _ _
      _ ≤ R / 2 * (θ ^ 4 * (5 / 96)) := mul_le_mul hηu hc (abs_nonneg _) (by positivity)
  have h2 : R / 2 * (θ ^ 4 * (5 / 96)) ≤ R / 2 * ((X / 10000 + 25 * R ^ 2) * (5 / 96)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : R * X ≤ X / 1000000 := by nlinarith
  have h4 : R * R ^ 2 ≤ R ^ 2 / 1000000 := by nlinarith [sq_nonneg R]
  nlinarith

private theorem bP2 {η u a t R X : ℝ} (hηu : |η * u| ≤ R / 2) (ht2 : t ^ 2 ≤ 5 / 2 * R)
    (haX : a ^ 2 ≤ X) (hR0 : 0 ≤ R) (hRle : R ≤ 1 / 1000000) :
    η * u * ((a + t) ^ 2 - t ^ 2) / 2 ≤ R ^ 2 / 150 + X / 30000 := by
  have hq : |(a + t) ^ 2 - t ^ 2| ≤ 101 * a ^ 2 + t ^ 2 / 100 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (10 * a + t / 10), sq_nonneg (10 * a - t / 10)]
  have h1 : η * u * ((a + t) ^ 2 - t ^ 2) ≤ R / 2 * (101 * a ^ 2 + t ^ 2 / 100) := by
    calc η * u * ((a + t) ^ 2 - t ^ 2) ≤ |η * u * ((a + t) ^ 2 - t ^ 2)| := le_abs_self _
      _ = |η * u| * |(a + t) ^ 2 - t ^ 2| := abs_mul _ _
      _ ≤ R / 2 * (101 * a ^ 2 + t ^ 2 / 100) :=
        mul_le_mul hηu hq (abs_nonneg _) (by positivity)
  have h2 : R / 2 * (101 * a ^ 2 + t ^ 2 / 100) ≤ R / 2 * (101 * X + 5 / 2 * R / 100) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : R * X ≤ X / 1000000 := by nlinarith
  nlinarith

private theorem quartic_abs {u η : ℝ} :
    |(4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) * η| ≤ 8 * (u ^ 2 + η ^ 2) ^ 2 := by
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg (u + η / 4)),
      mul_nonneg (sq_nonneg u) (sq_nonneg η), sq_nonneg (η ^ 2)]
  · nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg (u - η / 4)),
      mul_nonneg (sq_nonneg u) (sq_nonneg η), sq_nonneg (η ^ 2)]

private theorem bP3 {u η w c R : ℝ} (hR : R = u ^ 2 + η ^ 2) (hw0 : 0 < w) (hw2 : w ≤ 2)
    (hd : |u + 1 - c| ≤ 1 / 500) :
    (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) / 32 * (η * w * (u + 1 - c)) ≤ R ^ 2 / 1000 := by
  have hq := quartic_abs (u := u) (η := η)
  rw [← hR] at hq
  have he : (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) / 32 * (η * w * (u + 1 - c)) =
      (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) * η * (w * (u + 1 - c)) / 32 := by ring
  rw [he]
  have hwd : |w * (u + 1 - c)| ≤ 2 * (1 / 500) := by
    rw [abs_mul, abs_of_pos hw0]
    exact mul_le_mul hw2 hd (abs_nonneg _) (by norm_num)
  have h1 : (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) * η * (w * (u + 1 - c)) ≤
      8 * R ^ 2 * (2 * (1 / 500)) := by
    calc (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) * η * (w * (u + 1 - c))
        ≤ |(4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) * η * (w * (u + 1 - c))| := le_abs_self _
      _ = |(4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) * η| * |w * (u + 1 - c)| := abs_mul _ _
      _ ≤ 8 * R ^ 2 * (2 * (1 / 500)) := mul_le_mul hq hwd (abs_nonneg _) (by positivity)
  linarith

private theorem bP4 {θ s a b R X : ℝ} (hσ : |θ - s| ≤ |θ| ^ 3 / 5) (hθ2 : θ ^ 2 ≤ 1 / 1000000)
    (hθ4 : θ ^ 4 ≤ X / 10000 + 25 * R ^ 2) (hab : (a + 3 * b) ^ 2 ≤ 10 * X) :
    1 / 500 * ((θ - s) * (a + 3 * b)) ≤ X / 40000 + R ^ 2 / 1000000 := by
  have h6 : |θ| ^ 3 * |a + 3 * b| ≤ 50 * θ ^ 6 + (a + 3 * b) ^ 2 / 200 := by
    have e1 : θ ^ 6 = (|θ| ^ 3) ^ 2 := by
      rw [show (|θ| ^ 3) ^ 2 = (|θ| ^ 2) ^ 3 by ring, sq_abs]; ring
    have e2 : (a + 3 * b) ^ 2 = |a + 3 * b| ^ 2 := (sq_abs _).symm
    rw [e1, e2]
    nlinarith [sq_nonneg (10 * |θ| ^ 3 - |a + 3 * b| / 10)]
  have h6' : θ ^ 6 ≤ (X / 10000 + 25 * R ^ 2) / 1000000 := by
    have : θ ^ 6 = θ ^ 2 * θ ^ 4 := by ring
    rw [this]
    have h0 : 0 ≤ θ ^ 4 := by positivity
    nlinarith
  have h1 : (θ - s) * (a + 3 * b) ≤ |θ| ^ 3 / 5 * |a + 3 * b| := by
    calc (θ - s) * (a + 3 * b) ≤ |(θ - s) * (a + 3 * b)| := le_abs_self _
      _ = |θ - s| * |a + 3 * b| := abs_mul _ _
      _ ≤ |θ| ^ 3 / 5 * |a + 3 * b| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
  nlinarith

private theorem bP5 {e a b R X : ℝ} (he2 : e ^ 2 ≤ 2 * R ^ 2 + 8 * R * (X / 10000 + 25 * R ^ 2))
    (hab : (a - 2 * b) ^ 2 ≤ 5 * X) (hRle : R ≤ 1 / 1000000) :
    1 / 500 * (e * (a - 2 * b)) ≤ R ^ 2 / 40 + X / 1900 := by
  have h1 : e * (a - 2 * b) ≤ 5 * e ^ 2 + (a - 2 * b) ^ 2 / 20 := by
    nlinarith [sq_nonneg (e - (a - 2 * b) / 10)]
  have h3 : R * X ≤ X / 1000000 := by nlinarith
  have h4 : R * R ^ 2 ≤ R ^ 2 / 1000000 := by nlinarith [sq_nonneg R]
  nlinarith

private theorem cs_a {θ u η : ℝ} :
    (θ + u / 2 - 3 * η / 2) ^ 2 ≤ 7 / 2 * (θ ^ 2 + u ^ 2 + η ^ 2) := by
  nlinarith [sq_nonneg (u - θ / 2), sq_nonneg (η + 3 * θ / 2), sq_nonneg (η / 2 + 3 * u / 2)]

private theorem cs_b {x u η : ℝ} : (x - u / 2 - η / 2) ^ 2 ≤ 3 / 2 * (x ^ 2 + u ^ 2 + η ^ 2) := by
  nlinarith [sq_nonneg (u + x / 2), sq_nonneg (η + x / 2), sq_nonneg (u / 2 - η / 2)]

private theorem be2 {η u w c θ R X : ℝ} (hR : R = u ^ 2 + η ^ 2) (hw0 : 0 < w) (hw2 : w ≤ 2)
    (h1c : (1 - c) ^ 2 ≤ θ ^ 4) (hθ4 : θ ^ 4 ≤ X / 10000 + 25 * R ^ 2) :
    (η * w * (u + 1 - c)) ^ 2 ≤ 2 * R ^ 2 + 8 * R * (X / 10000 + 25 * R ^ 2) := by
  have hw4 : w ^ 2 ≤ 4 := by nlinarith
  have hsum : (u + 1 - c) ^ 2 ≤ 2 * u ^ 2 + 2 * (1 - c) ^ 2 := by
    nlinarith [sq_nonneg (u - (1 - c))]
  have h1 : (η * w * (u + 1 - c)) ^ 2 ≤ η ^ 2 * 4 * (2 * u ^ 2 + 2 * (1 - c) ^ 2) := by
    have : (η * w * (u + 1 - c)) ^ 2 = η ^ 2 * w ^ 2 * (u + 1 - c) ^ 2 := by ring
    rw [this]
    have hη : 0 ≤ η ^ 2 := sq_nonneg η
    calc η ^ 2 * w ^ 2 * (u + 1 - c) ^ 2 ≤ η ^ 2 * 4 * (u + 1 - c) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hw4 hη
      _ ≤ η ^ 2 * 4 * (2 * u ^ 2 + 2 * (1 - c) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  have h2 : 8 * (η ^ 2 * u ^ 2) ≤ 2 * R ^ 2 := by
    rw [hR]; nlinarith [sq_nonneg (u ^ 2 - η ^ 2)]
  have hηR : η ^ 2 ≤ R := by rw [hR]; nlinarith [sq_nonneg u]
  have h3 : η ^ 2 * (1 - c) ^ 2 ≤ R * (X / 10000 + 25 * R ^ 2) :=
    mul_le_mul hηR (h1c.trans hθ4) (sq_nonneg _) (by rw [hR]; positivity)
  nlinarith

private theorem sz_X {θ x u η : ℝ} (hr : θ ^ 2 + x ^ 2 + u ^ 2 + η ^ 2 ≤ 1 / 1000000) :
    (θ + u / 2 - 3 * η / 2) ^ 2 + (x - u / 2 - η / 2) ^ 2 ≤ 5 / 1000000 := by
  have h1 := cs_a (θ := θ) (u := u) (η := η)
  have h2 := cs_b (x := x) (u := u) (η := η)
  nlinarith [sq_nonneg θ, sq_nonneg x]

private theorem t_sq {u η : ℝ} : (-u / 2 + 3 * η / 2) ^ 2 ≤ 5 / 2 * (u ^ 2 + η ^ 2) := by
  nlinarith [sq_nonneg (3 * u / 2 + η / 2)]

private theorem θ_sq {a t X R : ℝ} (ht2 : t ^ 2 ≤ 5 / 2 * R) (haX : a ^ 2 ≤ X) :
    (a + t) ^ 2 ≤ 2 * X + 5 * R := by
  nlinarith [sq_nonneg (a - t)]

private theorem θ_four {θ X R : ℝ} (hθX : θ ^ 2 ≤ 2 * X + 5 * R) (hX0 : 0 ≤ X)
    (hXle : X ≤ 5 / 1000000) (hRle : R ≤ 1 / 1000000) :
    θ ^ 4 ≤ X / 10000 + 25 * R ^ 2 := by
  have h1 : θ ^ 4 ≤ (2 * X + 5 * R) ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg θ) hθX 2
    rw [← pow_mul] at this
    exact this
  have h2 : X * X ≤ 5 / 1000000 * X := mul_le_mul_of_nonneg_right hXle hX0
  have h3 : R * X ≤ 1 / 1000000 * X := mul_le_mul_of_nonneg_right hRle hX0
  nlinarith

private theorem ηu_abs {η u : ℝ} : |η * u| ≤ (u ^ 2 + η ^ 2) / 2 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (η + u), sq_nonneg (η - u)]

private theorem cos_facts {θ c : ℝ} (hc : |c - (1 - θ ^ 2 / 2)| ≤ |θ| ^ 4 * (5 / 96))
    (hθ2 : θ ^ 2 ≤ 1 / 1000000) :
    |1 - c - θ ^ 2 / 2| ≤ θ ^ 4 * (5 / 96) ∧ 0 ≤ 1 - c ∧ 1 - c ≤ θ ^ 2 := by
  have hθ4' : |θ| ^ 4 = θ ^ 4 := by
    rw [show |θ| ^ 4 = (|θ| ^ 2) ^ 2 by ring, sq_abs]; ring
  have hc' : |1 - c - θ ^ 2 / 2| ≤ θ ^ 4 * (5 / 96) := by
    rw [show 1 - c - θ ^ 2 / 2 = -(c - (1 - θ ^ 2 / 2)) by ring, abs_neg, ← hθ4']
    exact hc
  refine ⟨hc', ?_⟩
  obtain ⟨hl, hu⟩ := abs_le.mp hc'
  have hθ4s : θ ^ 4 ≤ θ ^ 2 / 1000000 := by
    have : θ ^ 4 = θ ^ 2 * θ ^ 2 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hθ2 (sq_nonneg θ)
    linarith
  have h0 : 0 ≤ θ ^ 2 := sq_nonneg θ
  constructor <;> linarith

private theorem sin_fact {θ s : ℝ} (hs : |s - (θ - θ ^ 3 / 6)| ≤ |θ| ^ 5 / 100)
    (hθ2 : θ ^ 2 ≤ 1 / 1000000) : |θ - s| ≤ |θ| ^ 3 / 5 := by
  have e : θ - s = θ ^ 3 / 6 - (s - (θ - θ ^ 3 / 6)) := by ring
  rw [e]
  have h5 : |θ| ^ 5 = |θ| ^ 3 * θ ^ 2 := by
    rw [show |θ| ^ 5 = |θ| ^ 3 * |θ| ^ 2 by ring, sq_abs]
  have h3 : |θ ^ 3 / 6| = |θ| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  have hn : 0 ≤ |θ| ^ 3 := by positivity
  have hm := mul_le_mul_of_nonneg_left hθ2 hn
  calc |θ ^ 3 / 6 - (s - (θ - θ ^ 3 / 6))| ≤ |θ ^ 3 / 6| + |s - (θ - θ ^ 3 / 6)| :=
        abs_sub _ _
    _ ≤ |θ| ^ 3 / 6 + |θ| ^ 3 * θ ^ 2 / 100 := by rw [h3, ← h5]; linarith
    _ ≤ |θ| ^ 3 / 5 := by linarith

private theorem lie_identity {θ x u η s c w : ℝ} (hw : w * (u + 1) = 1) :
    1 / 500 * (3 / 2 * (θ + u / 2 - 3 * η / 2) - (x - u / 2 - η / 2) / 2) * (-s + η + 2 * x) +
      1 / 500 * (-(θ + u / 2 - 3 * η / 2) / 2 + 7 / 2 * (x - u / 2 - η / 2)) * (-s + η) +
      (u + u ^ 2 + (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) / 32 +
        1 / 500 * ((3 / 2 * (θ + u / 2 - 3 * η / 2) - (x - u / 2 - η / 2) / 2) / 2 -
          (-(θ + u / 2 - 3 * η / 2) / 2 + 7 / 2 * (x - u / 2 - η / 2)) / 2)) * (-(c * η * w)) +
      (η + (-3 * u ^ 3 + 9 * u * η ^ 2 - 36 * η ^ 3) / 32 +
        1 / 500 * (-3 * (3 / 2 * (θ + u / 2 - 3 * η / 2) - (x - u / 2 - η / 2) / 2) / 2 -
          (-(θ + u / 2 - 3 * η / 2) / 2 + 7 / 2 * (x - u / 2 - η / 2)) / 2)) * u =
      η * u * (1 - c - θ ^ 2 / 2) +
        η * u * (((θ + u / 2 - 3 * η / 2) + (-u / 2 + 3 * η / 2)) ^ 2 -
          (-u / 2 + 3 * η / 2) ^ 2) / 2 - 3 / 32 * (u ^ 2 + η ^ 2) ^ 2 +
        (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) / 32 * (η * w * (u + 1 - c)) +
        1 / 500 * (-((θ + u / 2 - 3 * η / 2) ^ 2 + (x - u / 2 - η / 2) ^ 2)) +
        1 / 500 * ((θ - s) * ((θ + u / 2 - 3 * η / 2) + 3 * (x - u / 2 - η / 2))) +
        1 / 500 * ((η * w * (u + 1 - c)) *
          ((θ + u / 2 - 3 * η / 2) - 2 * (x - u / 2 - η / 2))) := by
  linear_combination (η * (-4000 * c * u - 375 * η ^ 3 + 1125 * η * u ^ 2 + 4 * η - 8 * θ -
    500 * u ^ 3 - 12 * u + 16 * x) / 4000) * hw

/-- Lie derivative bound on the ball of radius `1/1000`. -/
private theorem lie_bound {θ x u η s c w : ℝ}
    (hr : θ ^ 2 + x ^ 2 + u ^ 2 + η ^ 2 ≤ 1 / 1000000)
    (hs : |s - (θ - θ ^ 3 / 6)| ≤ |θ| ^ 5 / 100)
    (hc : |c - (1 - θ ^ 2 / 2)| ≤ |θ| ^ 4 * (5 / 96))
    (hw : w * (u + 1) = 1) (hw0 : 0 < w) (hw2 : w ≤ 2) :
    1 / 500 * (3 / 2 * (θ + u / 2 - 3 * η / 2) - (x - u / 2 - η / 2) / 2) * (-s + η + 2 * x) +
      1 / 500 * (-(θ + u / 2 - 3 * η / 2) / 2 + 7 / 2 * (x - u / 2 - η / 2)) * (-s + η) +
      (u + u ^ 2 + (4 * u ^ 3 - 9 * u ^ 2 * η + 3 * η ^ 3) / 32 +
        1 / 500 * ((3 / 2 * (θ + u / 2 - 3 * η / 2) - (x - u / 2 - η / 2) / 2) / 2 -
          (-(θ + u / 2 - 3 * η / 2) / 2 + 7 / 2 * (x - u / 2 - η / 2)) / 2)) * (-(c * η * w)) +
      (η + (-3 * u ^ 3 + 9 * u * η ^ 2 - 36 * η ^ 3) / 32 +
        1 / 500 * (-3 * (3 / 2 * (θ + u / 2 - 3 * η / 2) - (x - u / 2 - η / 2) / 2) / 2 -
          (-(θ + u / 2 - 3 * η / 2) / 2 + 7 / 2 * (x - u / 2 - η / 2)) / 2)) * u ≤
    -(3 / 64) * (u ^ 2 + η ^ 2) ^ 2 -
      1 / 2000 * ((θ + u / 2 - 3 * η / 2) ^ 2 + (x - u / 2 - η / 2) ^ 2) := by
  rw [lie_identity hw]
  have hXle := sz_X hr
  have ht2 := t_sq (u := u) (η := η)
  have hηu := ηu_abs (η := η) (u := u)
  have hθ2 : θ ^ 2 ≤ 1 / 1000000 := by linarith [sq_nonneg x, sq_nonneg u, sq_nonneg η]
  have hRle : u ^ 2 + η ^ 2 ≤ 1 / 1000000 := by linarith [sq_nonneg x, sq_nonneg θ]
  have hR0 : 0 ≤ u ^ 2 + η ^ 2 := by positivity
  have huabs : |u| ≤ 1 / 1000 :=
    abs_le_of_sq_le_sq (by linarith [sq_nonneg x, sq_nonneg θ, sq_nonneg η]) (by norm_num)
  obtain ⟨hc', h1c0, h1c1⟩ := cos_facts hc hθ2
  have h1c : (1 - c) ^ 2 ≤ θ ^ 4 := by
    have : θ ^ 4 = (θ ^ 2) ^ 2 := by ring
    rw [this]
    exact sq_le_sq' (by linarith [sq_nonneg θ]) h1c1
  have hd : |u + 1 - c| ≤ 1 / 500 := by
    obtain ⟨hul, huu⟩ := abs_le.mp huabs
    rw [abs_le]; constructor <;> linarith
  have hσ := sin_fact hs hθ2
  generalize ha : θ + u / 2 - 3 * η / 2 = a at hXle ⊢
  generalize hb : x - u / 2 - η / 2 = b at hXle ⊢
  generalize ht : -u / 2 + 3 * η / 2 = t at ht2 ⊢
  have hθat : θ = a + t := by linarith
  generalize hR : u ^ 2 + η ^ 2 = R at ht2 hηu hRle hR0 ⊢
  generalize hX : a ^ 2 + b ^ 2 = X at hXle ⊢
  have hX0 : 0 ≤ X := by rw [← hX]; positivity
  have haX : a ^ 2 ≤ X := by rw [← hX]; linarith [sq_nonneg b]
  have hθX : θ ^ 2 ≤ 2 * X + 5 * R := hθat ▸ θ_sq ht2 haX
  have hθ4 := θ_four hθX hX0 hXle hRle
  have hab3 : (a + 3 * b) ^ 2 ≤ 10 * X := by rw [← hX]; nlinarith [sq_nonneg (3 * a - b)]
  have hab2 : (a - 2 * b) ^ 2 ≤ 5 * X := by rw [← hX]; nlinarith [sq_nonneg (2 * a + b)]
  have hP1 := bP1 (hηu.trans_eq (by ring)) hc' hθ4 hR0 hRle hX0
  have hP2 := bP2 (hηu.trans_eq (by ring)) ht2 haX hR0 hRle
  have hP3 := bP3 (c := c) hR.symm hw0 hw2 hd
  have hP4 := bP4 (s := s) hσ hθ2 hθ4 hab3
  have hP5 := bP5 (be2 hR.symm hw0 hw2 h1c hθ4) hab2 hRle
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  linarith


private theorem quartic_lower {u η : ℝ} :
    -(16 * (u ^ 2 + η ^ 2) ^ 2) ≤ u ^ 4 - 3 * u ^ 3 * η + 3 * u * η ^ 3 - 9 * η ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg (u - η)),
    mul_nonneg (sq_nonneg u) (sq_nonneg (u + η)),
    mul_nonneg (sq_nonneg η) (sq_nonneg (u - η)), mul_nonneg (sq_nonneg η) (sq_nonneg (u + η)),
    sq_nonneg (u ^ 2), sq_nonneg (η ^ 2), mul_nonneg (sq_nonneg u) (sq_nonneg η)]

/-- `W ≥ (u² + η²)/4 + |ξ|²/1000` near the origin. -/
private theorem wf_lower {θ x u η : ℝ} (hr : θ ^ 2 + x ^ 2 + u ^ 2 + η ^ 2 ≤ 1 / 1000000) :
    (u ^ 2 + η ^ 2) / 4 + ((θ + u / 2 - 3 * η / 2) ^ 2 + (x - u / 2 - η / 2) ^ 2) / 1000 ≤
      u ^ 2 / 2 + u ^ 3 / 3 + η ^ 2 / 2 +
        (u ^ 4 - 3 * u ^ 3 * η + 3 * u * η ^ 3 - 9 * η ^ 4) / 32 +
        1 / 500 * (3 / 4 * (θ + u / 2 - 3 * η / 2) ^ 2 -
          1 / 2 * (θ + u / 2 - 3 * η / 2) * (x - u / 2 - η / 2) +
          7 / 4 * (x - u / 2 - η / 2) ^ 2) := by
  have hq := quartic_lower (u := u) (η := η)
  have hRle : u ^ 2 + η ^ 2 ≤ 1 / 1000000 := by linarith [sq_nonneg x, sq_nonneg θ]
  have hR0 : 0 ≤ u ^ 2 + η ^ 2 := by positivity
  have hR2 : (u ^ 2 + η ^ 2) ^ 2 ≤ (u ^ 2 + η ^ 2) / 1000000 := by
    have := mul_le_mul_of_nonneg_left hRle hR0
    nlinarith
  have huabs : |u| ≤ 1 / 1000 :=
    abs_le_of_sq_le_sq (by linarith [sq_nonneg x, sq_nonneg θ, sq_nonneg η]) (by norm_num)
  have hu3 : -(u ^ 2 / 1000) ≤ u ^ 3 := by
    obtain ⟨h1, h2⟩ := abs_le.mp huabs
    have : u ^ 3 = u * u ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_right h1 (sq_nonneg u)]
  have hP : (θ + u / 2 - 3 * η / 2) ^ 2 / 2 + (x - u / 2 - η / 2) ^ 2 / 2 ≤
      3 / 4 * (θ + u / 2 - 3 * η / 2) ^ 2 -
        1 / 2 * (θ + u / 2 - 3 * η / 2) * (x - u / 2 - η / 2) +
        7 / 4 * (x - u / 2 - η / 2) ^ 2 := by
    nlinarith [sq_nonneg ((θ + u / 2 - 3 * η / 2) - (x - u / 2 - η / 2)),
      sq_nonneg (x - u / 2 - η / 2)]
  nlinarith

/-! ## The weak focus -/

/-- The composite Lyapunov function in translated coordinates `(θ, x, u, η)`, `u = V − 1`:
the dc energy `u²/2 + u³/3 + η²/2`, the quartic averaging correction, and `1/500` times the
quadratic form `ξᵀ P ξ` of the PLL coordinates `ξ = (θ + u/2 − 3η/2, x − u/2 − η/2)` measured
from the linear slaving (`P = [[3/4, −1/4], [−1/4, 7/4]]`, `A_pᵀ P + P A_p = −I`). -/
private def wfLyap (z : Dynamics.State 4) : ℝ :=
  z 2 ^ 2 / 2 + z 2 ^ 3 / 3 + z 3 ^ 2 / 2 +
    (z 2 ^ 4 - 3 * z 2 ^ 3 * z 3 + 3 * z 2 * z 3 ^ 3 - 9 * z 3 ^ 4) / 32 +
    1 / 500 * (3 / 4 * (z 0 + z 2 / 2 - 3 * z 3 / 2) ^ 2 -
      1 / 2 * (z 0 + z 2 / 2 - 3 * z 3 / 2) * (z 1 - z 2 / 2 - z 3 / 2) +
      7 / 4 * (z 1 - z 2 / 2 - z 3 / 2) ^ 2)

private theorem wfLyap_hasFDerivAt (z : Dynamics.State 4) :
    HasFDerivAt wfLyap
      ((1 / 500 * (3 / 2 * (z 0 + z 2 / 2 - 3 * z 3 / 2) - (z 1 - z 2 / 2 - z 3 / 2) / 2)) •
          (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : Dynamics.State 4 →L[ℝ] ℝ) +
        (1 / 500 * (-(z 0 + z 2 / 2 - 3 * z 3 / 2) / 2 + 7 / 2 * (z 1 - z 2 / 2 - z 3 / 2))) •
          (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1 : Dynamics.State 4 →L[ℝ] ℝ) +
        (z 2 + z 2 ^ 2 + (4 * z 2 ^ 3 - 9 * z 2 ^ 2 * z 3 + 3 * z 3 ^ 3) / 32 +
          1 / 500 * ((3 / 2 * (z 0 + z 2 / 2 - 3 * z 3 / 2) - (z 1 - z 2 / 2 - z 3 / 2) / 2) / 2 -
            (-(z 0 + z 2 / 2 - 3 * z 3 / 2) / 2 + 7 / 2 * (z 1 - z 2 / 2 - z 3 / 2)) / 2)) •
          (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 2 : Dynamics.State 4 →L[ℝ] ℝ) +
        (z 3 + (-3 * z 2 ^ 3 + 9 * z 2 * z 3 ^ 2 - 36 * z 3 ^ 3) / 32 +
          1 / 500 * (-3 * (3 / 2 * (z 0 + z 2 / 2 - 3 * z 3 / 2) -
            (z 1 - z 2 / 2 - z 3 / 2) / 2) / 2 -
            (-(z 0 + z 2 / 2 - 3 * z 3 / 2) / 2 + 7 / 2 * (z 1 - z 2 / 2 - z 3 / 2)) / 2)) •
          (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 3 : Dynamics.State 4 →L[ℝ] ℝ)) z := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h2 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h3 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have hA := (h0.add (h2.const_mul (1 / 2 : ℝ))).sub (h3.const_mul (3 / 2 : ℝ))
  have hB := (h1.sub (h2.const_mul (1 / 2 : ℝ))).sub (h3.const_mul (1 / 2 : ℝ))
  have hW := (((((h2.pow 2).const_mul (1 / 2 : ℝ)).add ((h2.pow 3).const_mul (1 / 3 : ℝ))).add
    ((h3.pow 2).const_mul (1 / 2 : ℝ))).add
    (((((h2.pow 4).sub (((h2.pow 3).mul h3).const_mul (3 : ℝ))).add
      ((h2.mul (h3.pow 3)).const_mul (3 : ℝ))).sub ((h3.pow 4).const_mul (9 : ℝ))).const_mul
        (1 / 32 : ℝ))).add
    (((((hA.pow 2).const_mul (3 / 4 : ℝ)).sub ((hA.mul hB).const_mul (1 / 2 : ℝ))).add
      ((hB.pow 2).const_mul (7 / 4 : ℝ))).const_mul (1 / 500 : ℝ))
  refine Dynamics.hasFDerivAt_of_eq hW (fun y => by simp [wfLyap]; ring) ?_
  apply ContinuousLinearMap.ext
  intro v
  simp
  ring

/-- The weak focus: `V₀ = X_g = k_p = k_iv = 1`, `k_i = 2`, `i_{d0} = k_pv = I_dc0 = 0`,
`C = 3/2` (so `γ = 1`), at `θ₀ = 0`. -/
def weakFocus : Model := ⟨⟨1, 1, 0, 1, 2, 0, 1, 3 / 2, 0⟩, 0⟩

/-- The translated field of the weak focus: `θ̇ = −sin θ + η + 2x`, `ẋ = −sin θ + η`,
`u̇ = −cos θ · η / (1 + u)`, `η̇ = u`. -/
private theorem weakFocus_field (z : Dynamics.State 4) :
    weakFocus.field z = WithLp.toLp 2 ![-Real.sin (z 0) + z 3 + 2 * z 1, -Real.sin (z 0) + z 3,
      -(Real.cos (z 0) * z 3 * (z 2 + 1)⁻¹), z 2] := by
  ext i
  fin_cases i <;> simp [Model.field, FourState.field, Dynamics.lift, coordField, opPoint, weakFocus,
    vq, idc, Params.γ]
  ring

private theorem wfLyap_contDiff : ContDiff ℝ 1 wfLyap := by
  have c0 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 0) := contDiff_piLp_apply 2
  have c1 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 1) := contDiff_piLp_apply 2
  have c2 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 2) := contDiff_piLp_apply 2
  have c3 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 3) := contDiff_piLp_apply 2
  unfold wfLyap
  fun_prop

private theorem norm_sq_coords (z : Dynamics.State 4) :
    ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]

private theorem coords_small {z : Dynamics.State 4} (hz : ‖z - 0‖ < 1 / 1000) :
    z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 ≤ 1 / 1000000 := by
  rw [sub_zero] at hz
  rw [← norm_sq_coords]
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith

private theorem pos_of_ne {z : Dynamics.State 4} (hne : z ≠ 0) :
    0 < z 2 ^ 2 + z 3 ^ 2 ∨
      0 < (z 0 + z 2 / 2 - 3 * z 3 / 2) ^ 2 + (z 1 - z 2 / 2 - z 3 / 2) ^ 2 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hu : z 2 = 0 := by nlinarith [sq_nonneg (z 2), sq_nonneg (z 3)]
  have hη : z 3 = 0 := by nlinarith [sq_nonneg (z 2), sq_nonneg (z 3)]
  rw [hu, hη] at h2
  have ha : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hb : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  apply hne
  ext i
  fin_cases i
  · exact ha
  · exact hb
  · exact hu
  · exact hη

/-- Four-state GFL on the Hopf boundary of the dc loop: the weak focus `weakFocus`
(`V₀ = X_g = k_p = k_iv = 1`, `k_i = 2`, `i_{d0} = k_pv = I_dc0 = 0`, `C = 3/2`, `θ₀ = 0`) is
locally asymptotically stable. Its linearization has the imaginary pair `±i` of the undamped dc
loop; the PLL response to the dc oscillation (phase lag with `sin 2φ = 3/5`) gives the negative
first Lyapunov coefficient, certified by a composite Lyapunov function whose derivative is at most
`−(3/64)(u² + η²)² − (1/2000)|ξ|²` on the ball of radius `1/1000`. -/
@[tmio TM, powerlib_domain] theorem weakFocus_mem_den_locallyAsymptoticallyStable :
    connection% (weakFocus ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable weakFocus.field 0
  have hg : ContDiff ℝ 1
      (fun z : Dynamics.State 4 => regField weakFocus.params (z + opPoint weakFocus.θ)) :=
    (contDiff_regField _).comp (contDiff_id.add contDiff_const)
  refine Dynamics.localAsymptoticStable_of_lie_neg (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 1000) wfLyap_contDiff
    (hg.continuous.continuousOn.congr fun z hz' => ?_) (by simp [wfLyap]) ?_ ?_
  · have hz : ‖z - 0‖ < 1 / 1000 := mem_ball_iff_norm.mp hz'
    show FourState.field _ (z + opPoint _) = _
    refine field_eq_regField_of_near (θ0 := weakFocus.θ) _ ?_
    rw [add_sub_cancel_right]
    rw [sub_zero] at hz
    linarith
  · intro z hz hne
    have hr := coords_small hz
    have hlow := wf_lower hr
    have hX0 : 0 ≤ (z 0 + z 2 / 2 - 3 * z 3 / 2) ^ 2 + (z 1 - z 2 / 2 - z 3 / 2) ^ 2 := by
      positivity
    have hR0 : 0 ≤ z 2 ^ 2 + z 3 ^ 2 := by positivity
    unfold wfLyap
    rcases pos_of_ne hne with h | h <;> linarith
  · intro z hz hne
    have hr := coords_small hz
    have h0sq : z 0 ^ 2 ≤ 1 ^ 2 := by
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
    have h2sq : z 2 ^ 2 ≤ (1 / 1000) ^ 2 := by
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 0), sq_nonneg (z 3)]
    have hθ1 : |z 0| ≤ 1 := abs_le_of_sq_le_sq h0sq (by norm_num)
    have hu : |z 2| ≤ 1 / 1000 := abs_le_of_sq_le_sq h2sq (by norm_num)
    obtain ⟨hu1, hu2⟩ := abs_le.mp hu
    have hpos : 0 < z 2 + 1 := by linarith
    have hw : (z 2 + 1)⁻¹ * (z 2 + 1) = 1 := inv_mul_cancel₀ hpos.ne'
    have hw0 : 0 < (z 2 + 1)⁻¹ := inv_pos.mpr hpos
    have hw2 : (z 2 + 1)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    have key := lie_bound hr (Real.sin_bound hθ1) (Real.cos_bound hθ1) hw hw0 hw2
    have hstrict : -(3 / 64) * (z 2 ^ 2 + z 3 ^ 2) ^ 2 -
        1 / 2000 * ((z 0 + z 2 / 2 - 3 * z 3 / 2) ^ 2 + (z 1 - z 2 / 2 - z 3 / 2) ^ 2) < 0 := by
      have hX0 : 0 ≤ (z 0 + z 2 / 2 - 3 * z 3 / 2) ^ 2 + (z 1 - z 2 / 2 - z 3 / 2) ^ 2 := by
        positivity
      rcases pos_of_ne hne with h | h
      · have : 0 < (z 2 ^ 2 + z 3 ^ 2) ^ 2 := by positivity
        linarith
      · have : 0 ≤ (z 2 ^ 2 + z 3 ^ 2) ^ 2 := by positivity
        linarith
    rw [(wfLyap_hasFDerivAt z).fderiv, weakFocus_field]
    simp
    linarith

/-- The local asymptotic translation is sound but not exact: the weak focus `weakFocus` is
locally asymptotically stable, but its quartic `(λ² + 1)(λ² + λ + 2)` has the imaginary pair
`±i`, so the Routh inequality `a₁² + a₃² a₀ < a₃ a₂ a₁` fails with equality (`3 = 3`). -/
@[tmio TM, powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := weakFocus_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, (connection_proof% TMIO.mem_realize)] at hmem
  obtain ⟨-, -, -, hg⟩ : Meets weakFocus .routh := hmem .routh (by simp [family, translate])
  norm_num [a1, a2, a3, a0, twoAlphaCl, omegaClSq, Γc, vd0, weakFocus, Params.γ] at hg

/-! ## The Routh boundary: necessary conditions and inexpressibility -/

private theorem mem_den_flow_iff' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (FourState.field m.params) (opPoint m.θ) :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => FourState.field m.params)
    (pt := fun m => opPoint m.θ) family_isAutonomous

private theorem lyapunovStable_regField {p : Params} {θ0 : ℝ}
    (h : LyapunovStable (FourState.field p) (opPoint θ0)) :
    LyapunovStable (regField p) (opPoint θ0) :=
  Dynamics.lyapunovStable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (fun _ hy => (field_eq_regField_of_near p hy).symm) h

private theorem localAsymptoticStable_regField {p : Params} {θ0 : ℝ}
    (h : LocalAsymptoticStable (FourState.field p) (opPoint θ0)) :
    LocalAsymptoticStable (regField p) (opPoint θ0) := by
  obtain ⟨hLS, c, hc, hconv⟩ := h
  have hLSg := lyapunovStable_regField hLS
  refine ⟨hLSg, ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hLSg (1 / 2) (by norm_num)
  refine ⟨min c δ, lt_min hc hδ, fun t₀ φ hφ hφ0 => ?_⟩
  have hstay : ∀ t ∈ Ici t₀, ‖φ t - opPoint θ0‖ < 1 / 2 := fun t ht =>
    hb t₀ t φ (hφ.mono Icc_subset_Ici_self) (hφ0.trans_le (min_le_right _ _)) t ⟨ht, le_rfl⟩
  refine hconv t₀ φ (fun t ht => ?_) (hφ0.trans_le (min_le_left _ _))
  have := hφ t ht
  simp only at this ⊢
  rwa [← field_eq_regField_of_near p (hstay t ht)] at this

private theorem norm_toLp_four (a b c d : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, c, d] : Dynamics.State 4)‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp

/-! ### Necessary conditions: the closed Routh region -/

/-- With no capacitance the dc-bus voltage is frozen while the dc integrator integrates its
deviation: `W = (V − 1) η` has `Ẇ = (V − 1)²` (Chetaev), so the regularized field is unstable at
every operating point. -/
private theorem unstable_regField_of_C_eq_zero {p : Params} (hC : p.C = 0) (θ0 : ℝ) :
    Unstable (regField p) (opPoint θ0) := by
  have c2 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 2) := contDiff_piLp_apply 2
  have c3 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 3) := contDiff_piLp_apply 2
  have hW : ContDiff ℝ 1 (fun y : Dynamics.State 4 => (y 2 - 1) * y 3) := by fun_prop
  refine Dynamics.unstable_of_chetaev (contDiff_regField p) hW one_pos (fun ε hε => ?_) ?_
  · refine ⟨opPoint θ0 + WithLp.toLp 2 ![0, 0, ε / 4, ε / 4], ?_, ?_⟩
    · rw [add_sub_cancel_left]
      have h2 := norm_toLp_four 0 0 (ε / 4) (ε / 4)
      have h0 := norm_nonneg (WithLp.toLp 2 ![0, 0, ε / 4, ε / 4] : Dynamics.State 4)
      nlinarith
    · simp [opPoint]
      positivity
  · intro y _ hWy
    have h2 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) :
      Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := y)
    have h3 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4) :
      Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := y)
    have hd : HasFDerivAt (fun y : Dynamics.State 4 => (y 2 - 1) * y 3) _ y :=
      (h2.sub_const 1).mul h3
    rw [hd.fderiv]
    have hne : y 2 - 1 ≠ 0 := fun h => by
      have : (y 2 - 1) * y 3 = 0 := by rw [h, zero_mul]
      linarith
    simp [regField, Dynamics.lift, regCoordField, Params.γ, hC]
    positivity

/-- **Necessary condition (closed Routh region).** A Lyapunov stable model has `C ≠ 0`, its
selected point is an equilibrium (`IsEq`), and the quartic coefficients of `det(λI − A₀)` lie in
the closure of the Routh region: `a₃, a₂, a₁, a₀ ≥ 0` and `a₁² + a₃² a₀ ≤ a₃ a₂ a₁`. Hence the
same holds for local asymptotic and local exponential stability. -/
@[tmio TM, powerlib_domain] theorem closedRouth_of_mem_den_lyapunovStable :
    connection% (family.den (.flow .lyapunovStable) ⊆
      {m : Model | IsEq m.params m.θ ∧ m.params.C ≠ 0 ∧ 0 ≤ a3 m.params m.θ ∧
        0 ≤ a2 m.params m.θ ∧ 0 ≤ a1 m.params m.θ ∧ 0 ≤ a0 m.params m.θ ∧
        a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ ≤
          a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ}) := by
  unfold powerlib.TMIO.Statement
  intro m h
  rw [mem_den_flow_iff'] at h
  have hg := lyapunovStable_regField (p := m.params) (θ0 := m.θ) h
  have hC : m.params.C ≠ 0 := fun hC => unstable_regField_of_C_eq_zero hC m.θ hg
  have h0 := Dynamics.isEquilibrium_of_lyapunovStable (contDiff_regField m.params) hg
  have heq : IsEq m.params m.θ := by
    rw [← isEq_iff m.params hC,
      field_eq_regField_of_near m.params (by simp : ‖opPoint m.θ - opPoint m.θ‖ < 1 / 2)]
    exact h0
  have hnot : ¬ (a3 m.params m.θ < 0 ∨ a2 m.params m.θ < 0 ∨ a1 m.params m.θ < 0 ∨
      a0 m.params m.θ < 0 ∨ a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ <
        a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ) := fun hv =>
    Criteria.unstable_of_jacobian_quartic_violation (A0 m.params m.θ) (contDiff_regField _)
      (regField_opPoint _ hC heq) (fderiv_regField_opPoint _ _)
      (det_characteristicMatrix_A0_quartic _ heq.1) hv hg
  push Not at hnot
  exact ⟨heq, hC, hnot⟩

/-- The closed Routh region is necessary for local asymptotic stability as well. -/
@[tmio TM, powerlib_domain] theorem closedRouth_of_mem_den_locallyAsymptoticallyStable :
    connection% (family.den (.flow .locallyAsymptoticallyStable) ⊆
      {m : Model | IsEq m.params m.θ ∧ m.params.C ≠ 0 ∧ 0 ≤ a3 m.params m.θ ∧
        0 ≤ a2 m.params m.θ ∧ 0 ≤ a1 m.params m.θ ∧ 0 ≤ a0 m.params m.θ ∧
        a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ ≤
          a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ}) := by
  unfold powerlib.TMIO.Statement
  intro m h
  have hLS := closedRouth_of_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hLS
  refine hLS ?_
  rw [(connection_proof% family_isAutonomous.mem_den_flow)] at h ⊢
  exact h.1

/-! ### The Routh boundary is not decided by the requirement language -/

/-- A frozen PLL (`k_p = k_i = 0`, `X_g = 0`, `V₀ = 1`) with the damped dc loop of
`undampedPLL` (`k_pv = k_iv = 1`, `C = 3/2`), `i_{d0} = I_dc0 = 0`, at `θ₀ = 0`: the PLL angle is
constant and its integrator drifts, `ẋ = −sin θ`. Its quartic is `λ²(λ² + λ + 1)`, on the
boundary of the Routh region. -/
def frozenPLL : Model := ⟨⟨1, 0, 0, 0, 0, 1, 1, 3 / 2, 0⟩, 0⟩

/-- The frozen PLL is unstable: `W = −x sin θ` has `Ẇ = sin² θ` (Chetaev). -/
@[tmio TM, powerlib_domain] theorem frozenPLL_mem_den_unstable :
    connection% (frozenPLL ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff'.mpr (Dynamics.unstable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (fun y hy => field_eq_regField_of_near _ hy) ?_)
  have c0 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 0) := contDiff_piLp_apply 2
  have c1 : ContDiff ℝ 1 (fun z : Dynamics.State 4 => z 1) := contDiff_piLp_apply 2
  have hW : ContDiff ℝ 1 (fun y : Dynamics.State 4 => -(y 1 * Real.sin (y 0))) := by fun_prop
  refine Dynamics.unstable_of_chetaev (contDiff_regField _) hW one_pos (fun ε hε => ?_) ?_
  · set a := min (ε / 4) 1 with ha
    have ha0 : 0 < a := lt_min (by positivity) one_pos
    have ha1 : a ≤ ε / 4 := min_le_left _ _
    have ha2 : a ≤ 1 := min_le_right _ _
    refine ⟨opPoint frozenPLL.θ + WithLp.toLp 2 ![a, -a, 0, 0], ?_, ?_⟩
    · rw [add_sub_cancel_left]
      have h2 := norm_toLp_four a (-a) 0 0
      have h0 := norm_nonneg (WithLp.toLp 2 ![a, -a, 0, 0] : Dynamics.State 4)
      nlinarith
    · have hs : 0 < Real.sin a :=
        Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.two_le_pi])
      simp [opPoint, frozenPLL]
      positivity
  · intro y _ hWy
    have h0 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) :
      Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := y)
    have h1 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4) :
      Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := y)
    have hs := (Real.hasDerivAt_sin (y 0)).comp_hasFDerivAt y h0
    have hd : HasFDerivAt (fun y : Dynamics.State 4 => -(y 1 * Real.sin (y 0))) _ y :=
      (h1.mul hs).neg
    rw [hd.fderiv]
    have hs : Real.sin (y 0) ≠ 0 := fun h => by
      have : -(y 1 * Real.sin (y 0)) = 0 := by rw [h, mul_zero, neg_zero]
      linarith
    simp [regField, Dynamics.lift, regCoordField, frozenPLL, vq, idc]
    positivity

/-- The undamped PLL with a damped dc loop is not locally asymptotically stable: the PLL is
decoupled (`X_g = 0`) and conserves the pendulum energy `1 − cos θ + x²/2`. -/
@[tmio TM, powerlib_domain] theorem undampedPLL_not_mem_den_locallyAsymptoticallyStable :
    connection% (undampedPLL ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  rw [mem_den_flow_iff'] at h
  have hg := localAsymptoticStable_regField (p := undampedPLL.params) (θ0 := undampedPLL.θ) h
  have hd : ∀ y : Dynamics.State 4, HasFDerivAt
      (fun y : Dynamics.State 4 => -(1 - Real.cos (y 0) + 1 / 2 * y 1 ^ 2))
      (-(Real.sin (y 0) • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : Dynamics.State 4 →L[ℝ] ℝ) +
        y 1 • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1 : Dynamics.State 4 →L[ℝ] ℝ))) y := by
    intro y
    have h0 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) :
      Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := y)
    have h1 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4) :
      Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := y)
    have hc := (Real.hasDerivAt_cos (y 0)).comp_hasFDerivAt y h0
    refine ((hc.const_sub 1).add ((h1.pow 2).const_mul (1 / 2 : ℝ))).neg.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp
    ring
  refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (contDiff_regField _)
    (fun y => (hd y).differentiableAt) (by norm_num : (0 : ℝ) < 1) (fun y _ => ?_)
    (fun ε hε => ?_) hg
  · rw [(hd y).fderiv]
    simp [regField, Dynamics.lift, regCoordField, undampedPLL, vq, idc]
    ring_nf
    rfl
  · refine ⟨opPoint undampedPLL.θ + WithLp.toLp 2 ![0, ε / 2, 0, 0], ?_, ?_⟩
    · rw [add_sub_cancel_left]
      have h2 := norm_toLp_four 0 (ε / 2) 0 0
      have h0 := norm_nonneg (WithLp.toLp 2 ![0, ε / 2, 0, 0] : Dynamics.State 4)
      nlinarith
    · simp [opPoint, undampedPLL]
      positivity

/-- `undampedPLL` and `frozenPLL` meet the same requirements: both are equilibria with `C ≠ 0`,
and neither meets the strict Routh conditions nor `a₀ < 0`. -/
private theorem meets_undamped_iff_frozen (q : Requirement) :
    connection% (undampedPLL ∈ TMIO.realize Meets {q} ↔ frozenPLL ∈ TMIO.realize Meets {q}) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq]
  cases q
  · simp [Meets, IsEq, undampedPLL, frozenPLL]
  · constructor
    · rintro ⟨-, -, -, hg⟩
      norm_num [a1, a2, a3, a0, twoAlphaCl, omegaClSq, Γc, vd0, undampedPLL, Params.γ] at hg
    · rintro ⟨-, h1, -, -⟩
      norm_num [a1, twoAlphaCl, omegaClSq, Γc, vd0, frozenPLL, Params.γ] at h1
  · simp only [Meets]
    norm_num [a0, omegaClSq, Γc, vd0, undampedPLL, frozenPLL, Params.γ]

/-- `weakFocus` and `undampedPLL` meet the same requirements. -/
private theorem meets_weakFocus_iff_undamped (q : Requirement) :
    connection% (weakFocus ∈ TMIO.realize Meets {q} ↔ undampedPLL ∈ TMIO.realize Meets {q}) := by
  unfold TMIO.Statement
  simp only [TMIO.mem_realize, Set.mem_singleton_iff, forall_eq]
  cases q
  · simp [Meets, IsEq, undampedPLL, weakFocus]
  · constructor
    · rintro ⟨-, -, -, hg⟩
      norm_num [a1, a2, a3, a0, twoAlphaCl, omegaClSq, Γc, vd0, weakFocus, Params.γ] at hg
    · rintro ⟨-, -, -, hg⟩
      norm_num [a1, a2, a3, a0, twoAlphaCl, omegaClSq, Γc, vd0, undampedPLL, Params.γ] at hg
  · simp only [Meets]
    norm_num [a0, omegaClSq, Γc, vd0, undampedPLL, weakFocus, Params.γ]

/-- **Inexpressibility of Lyapunov stability.** No translation into the requirement language
of the family is exact for Lyapunov stability: `undampedPLL` (Lyapunov stable) and `frozenPLL`
(unstable) meet the same requirements. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_lyapunovStable :
    connection% (∀ T : Set Requirement,
      TMIO.realize Meets T ≠ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro T hT
  have h1 := undampedPLL_mem_den_lyapunovStable
  have h2 := frozenPLL_mem_den_unstable
  unfold powerlib.TMIO.Statement at h1 h2
  rw [← hT, (connection_proof% TMIO.mem_realize)] at h1
  have h3 : frozenPLL ∈ family.den (.flow .lyapunovStable) := by
    rw [← hT, (connection_proof% TMIO.mem_realize)]
    exact fun q hq => by
      have heq : Meets undampedPLL q ↔ Meets frozenPLL q := by
        simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq] using meets_undamped_iff_frozen q
      exact heq.mp (h1 q hq)
  rw [(connection_proof% family_isAutonomous.mem_den_flow)] at h2 h3
  exact h2 h3

/-- **Inexpressibility of instability.** No translation into the requirement language of the
family is exact for instability: `frozenPLL` (unstable) and `undampedPLL` (Lyapunov stable) meet
the same requirements. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_unstable :
    connection% (∀ T : Set Requirement, TMIO.realize Meets T ≠ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro T hT
  have h1 := undampedPLL_mem_den_lyapunovStable
  have h2 := frozenPLL_mem_den_unstable
  unfold powerlib.TMIO.Statement at h1 h2
  rw [← hT, (connection_proof% TMIO.mem_realize)] at h2
  have h3 : undampedPLL ∈ family.den (.flow .unstable) := by
    rw [← hT, (connection_proof% TMIO.mem_realize)]
    exact fun q hq => by
      have heq : Meets undampedPLL q ↔ Meets frozenPLL q := by
        simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq] using meets_undamped_iff_frozen q
      exact heq.mpr (h2 q hq)
  rw [(connection_proof% family_isAutonomous.mem_den_flow)] at h1 h3
  exact h3 h1

/-- **Inexpressibility of local asymptotic stability.** No translation into the requirement
language of the family is exact for local asymptotic stability: `weakFocus` (locally
asymptotically stable) and `undampedPLL` (not) meet the same requirements. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_locallyAsymptoticallyStable :
    connection% (∀ T : Set Requirement,
      TMIO.realize Meets T ≠ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro T hT
  have h1 := weakFocus_mem_den_locallyAsymptoticallyStable
  have h2 := undampedPLL_not_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at h1 h2
  apply h2
  rw [← hT, (connection_proof% TMIO.mem_realize)] at h1 ⊢
  exact fun q hq => by
    have heq : Meets weakFocus q ↔ Meets undampedPLL q := by
      simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq] using meets_weakFocus_iff_undamped q
    exact heq.mp (h1 q hq)

end powerlib.GFL.DCLink.FourStateBoundary
