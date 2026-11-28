import theorem.Map.AsymptoticPhaseRegularity

/-! # Lipschitz continuity of the asymptotic phase under bunching

For a map in centre–stable form `F(x, y) = (A x + f(x, y), B y + g(x, y))` with
`a ‖x‖ ≤ ‖A x‖ ≤ α ‖x‖`, `‖B y‖ ≤ b ‖y‖`, `ε`-Lipschitz `f`, `g`, the gap `b + 3ε < a` and an
invariant `1`-Lipschitz graph `y = h(x)`, the asymptotic phase `φ` of
`theorem/Map/AsymptoticPhase.lean` is Hölder continuous with the exponent of
`theorem/Map/AsymptoticPhaseRegularity.lean`, and no better in general. Here it is shown to be
**Lipschitz** when the second differences of `f`, `g` are bounded,
`‖k(z + d) − k(z) − (k(z' + d) − k(z'))‖ ≤ L₂ ‖d‖ ‖z − z'‖` (for instance `k` differentiable
with `L₂`-Lipschitz derivative, `norm_secondDiff_le`), under the **bunching condition**
`(b + 2ε)(α + ε) < a − ε`, without any smoothness of the graph `h`.

The argument works with differences of differences along orbits. For `p`, `p'` with phases
`x̄ = φ(p)`, `x̄' = φ(p')` and graph points `q = (x̄, h x̄)`, `q' = (x̄', h x̄')`, the sequence
`wₙ = (Fⁿ p − Fⁿ q) − (Fⁿ p' − Fⁿ q')` satisfies `wₙ₊₁ = (A wₙ,₁ + Δfₙ, B wₙ,₂ + Δgₙ)` with
`‖Δₙ‖ ≤ ε ‖wₙ‖ + L₂ ‖Fⁿ p' − Fⁿ q'‖ ‖Fⁿ q − Fⁿ q'‖ ≤ ε ‖wₙ‖ + K δ ((b + 2ε)(α + ε))ⁿ`
(`norm_secondDiff_pairs_le`): the orbit of `p'` approaches its graph orbit at the rate `b + 2ε`
(`‖Fⁿ p' − Fⁿ q'‖ ≤ (1 + ε/(a − b − 3ε)) (b + 2ε)ⁿ Z` for `‖p'₂ − h(p'₁)‖ ≤ Z`), the graph
orbits separate at most at the rate `α + ε`, `δ = ‖x̄ − x̄'‖` and `K = L₂ (1 + ε/(a − b − 3ε)) Z`.
Both orbits shadow their graph orbits, so `wₙ → 0` like `(b + 2ε)ⁿ`; in a weight `ρ` with
`max(b + 2ε, (b + 2ε)(α + ε)) ≤ ρ < a − ε` the centre component of `w` is the backward
(Lyapunov–Perron) sum and the stable one the forward sum (`dichotomy_centre_le`), which gives
`‖w₀,₁‖ ≤ ε ‖w₀,₂‖/(a − ρ) + 2Kδ/(a − ρ − ε)`. With `w₀,₁ = (p₁ − p'₁) − (x̄ − x̄')` and
`‖w₀,₂‖ ≤ ‖p − p'‖ + δ` this closes into `δ ≤ L ‖p − p'‖`,
`L = ((a − ρ)² − ε²)/((a − ρ − ε)² − 2K(a − ρ))` for `2K(a − ρ) < (a − ρ − ε)²`
(`norm_asymptoticPhase_sub_le_mul`). For `K = 0` and `ρ = b + 2ε` this is `1 + 2ε/(a − b − 3ε)`,
the constant that `norm_sub_asymptoticPhase_le` gives for affine `f`, `g`. Far from the graph,
`φ = r⁻ᴺ ∘ φ ∘ Fᴺ` trades `K` for `(b + 2ε)ᴺ K` at the cost `((α + ε)/(a − ε))ᴺ`
(`norm_asymptoticPhase_sub_le_mul_iterate`); for `b + 2ε < 1` the phase is Lipschitz on every
neighbourhood `{‖p₂ − h(p₁)‖ ≤ Z}` of the graph and locally Lipschitz.

The bunching condition is, as `ε → 0`, the centre bunching `b α < a` of Pugh, Shub and Wilkinson
(the stable rate times the largest centre rate below the smallest centre rate): the forcing of the
second differences decays like `((b + 2ε)(α + ε))ⁿ` and has to be summed against the backward
centre contraction `aⁿ`. For a simple multiplier `−1` (`A = −id`, `a = α = 1`, the setting of
`theorem/Periodic/FlipReduction.lean`) it reads `(b + 2ε)(1 + ε) < 1 − ε` and holds for
`ε ≤ (1 − b)/8`; the phase is then `8`-Lipschitz near the graph (`flip_asymptoticPhase_lipschitz`).
Smoothness cannot be dropped: for the `ε`-Lipschitz kink `f(x, y) = ε min(|x|, |y|)` with
`A = a·id` (so `a = α`), `B = b·id`, `g = 0`, `h = 0` the phase is not locally Lipschitz
(`not_locallyLipschitz_kink_asymptoticPhase`), for all `0 < b`, `0 < ε`, `b + 3ε < a`, bunched
or not; the Hölder exponent of `norm_asymptoticPhase_sub_le_rpow` cannot be raised to `1` for
merely Lipschitz nonlinearities.

Scope.
* The setting of `theorem/Map/AsymptoticPhase.lean`: real normed spaces `X` (complete), `Y`,
  `X × Y` with the max norm; `A` onto with `a ‖x‖ ≤ ‖A x‖ ≤ α ‖x‖`, `a ≤ α`; `‖B y‖ ≤ b ‖y‖`,
  `0 ≤ b`; `f`, `g` globally `ε`-Lipschitz; `b + 3ε < a`; `h` any invariant `1`-Lipschitz graph.
  No differentiability of `h`, of the reduced map or of its inverse is used, and no `C¹` theory
  of the centre manifold or of its stable fibres.
* Smoothness enters only through global second-difference bounds, with one constant `L₂` for
  `f` and `g`; `norm_secondDiff_le` derives them from `Differentiable ℝ k` and
  `LipschitzWith L₂ (fderiv ℝ k)`, the form used in `locallyLipschitz_asymptoticPhase` and
  `flip_asymptoticPhase_lipschitz`.
* The weight: `b + 2ε ≤ ρ`, `(b + 2ε)(α + ε) ≤ ρ`, `b < ρ`, `ρ + ε < a`; such a `ρ` exists
  exactly under the bunching condition (`exists_weight` gives one). Only the point `p'` needs a
  bound `Z` on its distance to the graph. The smallness condition `2K(a − ρ) < (a − ρ − ε)²` is
  scale invariant (`K` is dimensionless); it fixes the size of the neighbourhood of the graph in
  which the one-step estimate applies. The constants are explicit, not optimal for `L₂ > 0`.
* The flip instance is stated for globally `ε`-Lipschitz nonlinearities of class `C¹` with
  Lipschitz derivatives. The cut-off of `exists_local_centreManifold` (`f₀ ∘ ballRetract ρ`, the
  radial retraction) is Lipschitz but not differentiable on the sphere `‖p‖ = ρ`, so the phase of
  the cut-off map of a period map is not covered by this instance as such: a cut-off of class
  `C¹` with Lipschitz derivative (a smooth bump, which needs an inner-product or smooth norm) is
  not formalized.
* Generic; nothing here describes a physical system (foundation).

Source: Pugh, Shub and Wilkinson, "Hölder foliations", Duke Math. J. 86 (1997), and "Hölder
foliations, revisited", J. Mod. Dyn. 6 (2012) (centre bunching and `C¹` stable holonomies);
Hirsch, Pugh and Shub, *Invariant Manifolds* (LNM 583, 1977); Fenichel, "Asymptotic stability
with rate conditions", Indiana Univ. Math. J. 23 (1974) (rate conditions for the smoothness of
stable foliations); Hasselblatt and Wilkinson, "Prevalence of non-Lipschitz Anosov foliations",
Ergodic Theory Dynam. Systems 19 (1999); Carr, *Applications of Centre Manifold Theory* (1981),
Ch. 2 (the asymptotic phase); the open item of `theorem/Map/AsymptoticPhaseRegularity.lean`
(Scope: "Lipschitz continuity of the phase is not proved").

Results.
* The dichotomy estimate `dichotomy_centre_le` (`s₀ ≤ ε t₀/(a − ρ) + 2c/(a − ρ − ε)` for a
  centre component expanding by `a` and a stable one contracting by `b`, both `O(ρⁿ)`).
* Second differences: `norm_secondDiff_le` (Lipschitz derivative), `norm_secondDiff_pairs_le`
  (along two pairs of points).
* The constant: `phaseLipConst` (`((a − ρ)² − ε²)/((a − ρ − ε)² − 2K(a − ρ))`),
  `phaseLipConst_nonneg`; the weight `exists_weight`.
* **The theorem** `norm_asymptoticPhase_sub_le_mul`: `‖φ(p) − φ(p')‖ ≤ phaseLipConst a ρ ε K ·
  ‖p − p'‖`, `K = L₂ (1 + ε/(a − b − 3ε)) Z`, `‖p'₂ − h(p'₁)‖ ≤ Z`; far from the graph
  `norm_asymptoticPhase_sub_le_mul_iterate` (the factor `((α + ε)/(a − ε))ᴺ`, `K_N = (b + 2ε)ᴺ K`);
  `lipschitzOnWith_asymptoticPhase` (Lipschitz on `{‖p₂ − h(p₁)‖ ≤ Z}` for every `Z`),
  `locallyLipschitz_asymptoticPhase` (`f`, `g` with Lipschitz derivatives).
* The flip instance `flip_asymptoticPhase_lipschitz` (`A = −id`, `0 < ε ≤ (1 − b)/8`: `8`-Lipschitz
  where `L₂ ‖p'₂ − h(p'₁)‖ ≤ (1 − b)/20`, and locally Lipschitz).
* Sharpness: `kinkMap`, `lipschitzWith_kinkMap`, `kink_asymptoticPhase` (`φ(0, 1) = 0`,
  `φ((b/(a + ε))ᵏ, 1) ≥ (b/a)ᵏ`), `not_locallyLipschitz_kink_asymptoticPhase`.

Corrections.
`theorem/Map/AsymptoticPhaseRegularity.lean` (Scope) expected a Lipschitz phase to need `C¹`
graphs and fibres and a bunching condition of the type `(b + 2ε)(α + ε) < (a − ε)²`. The
argument here needs neither the `C¹` theory nor that condition: it closes under
`(b + 2ε)(α + ε) < a − ε` (the classical centre bunching `b α < a` as `ε → 0`). The two
conditions agree to first order only for `a = 1` (the flip and fold settings); for `a ≠ 1` the
condition `(b + 2ε)(α + ε) < (a − ε)²` is neither proved nor refuted here.

Family and connection conclusions.
None: static evidence on maps.
-/

noncomputable section

open Filter Topology

namespace powerlib.Map.CenterManifold

/-! ## A discrete dichotomy estimate -/

/-- The dichotomy estimate in normalized form (`S`, `T` bounded). -/
@[tmio T, powerlib_foundation] private theorem dichotomy_normalized {S T : ℕ → ℝ}
    {a b ρ ε c M : ℝ} (hS0 : ∀ n, 0 ≤ S n) (hT0 : ∀ n, 0 ≤ T n) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hb : 0 ≤ b) (hbρ : b < ρ) (hρ : b + 2 * ε ≤ ρ) (hρa : ρ + ε < a)
    (hM : ∀ n, max (S n) (T n) ≤ M)
    (hSr : ∀ n, a * S n ≤ ρ * S (n + 1) + ε * max (S n) (T n) + c)
    (hTr : ∀ n, ρ * T (n + 1) ≤ b * T n + ε * max (S n) (T n) + c) :
    S 0 ≤ ε * T 0 / (a - ρ) + 2 * c / (a - ρ - ε) := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt hb hbρ
  have hγ : 0 < a - ρ - ε := by linarith
  have hγ' : 0 < a - ρ := by linarith
  have ha : 0 < a := by linarith
  have hbdd : BddAbove (Set.range fun n => max (S n) (T n)) :=
    ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  set W := ⨆ n, max (S n) (T n) with hW
  have hWn : ∀ n, max (S n) (T n) ≤ W := fun n => le_ciSup hbdd n
  have hW0 : 0 ≤ W := (le_max_of_le_left (hS0 0)).trans (hWn 0)
  set E := ε * W + c with hE
  have hE0 : 0 ≤ E := by positivity
  have hεW : ∀ n, ε * max (S n) (T n) ≤ ε * W := fun n => mul_le_mul_of_nonneg_left (hWn n) hε
  -- the centre component, backward
  have hSk : ∀ k : ℕ, ∀ n, S n ≤ E / (a - ρ) + (ρ / a) ^ k * M := by
    intro k
    induction k with
    | zero =>
      intro n
      have h1 := (le_max_left _ _).trans (hM n)
      have h2 : 0 ≤ E / (a - ρ) := by positivity
      simp only [pow_zero, one_mul]
      linarith
    | succ k ih =>
      intro n
      have h1 := hSr n
      have h2 := ih (n + 1)
      have h3 := hεW n
      have h4 : a * S n ≤ ρ * (E / (a - ρ) + (ρ / a) ^ k * M) + E := by
        have := mul_le_mul_of_nonneg_left h2 hρ0.le
        linarith
      have e : E / (a - ρ) + (ρ / a) ^ (k + 1) * M =
          (ρ * (E / (a - ρ) + (ρ / a) ^ k * M) + E) / a := by
        rw [pow_succ]; field_simp; ring
      rw [e, le_div_iff₀ ha]
      linarith
  have hS : ∀ n, S n ≤ E / (a - ρ) := by
    intro n
    have hr0 : 0 ≤ ρ / a := by positivity
    have hr1 : ρ / a < 1 := by rw [div_lt_one ha]; linarith
    have hlim : Tendsto (fun k : ℕ => E / (a - ρ) + (ρ / a) ^ k * M) atTop
        (𝓝 (E / (a - ρ))) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const M).const_add
        (E / (a - ρ))
      simpa using this
    exact ge_of_tendsto' hlim fun k => hSk k n
  -- the stable component, forward
  have hρb : 0 < ρ - b := by linarith
  set V := max (T 0) (E / (ρ - b)) with hV
  have hEV : E ≤ (ρ - b) * V := by
    calc E = (ρ - b) * (E / (ρ - b)) := by field_simp
      _ ≤ (ρ - b) * V := mul_le_mul_of_nonneg_left (le_max_right _ _) hρb.le
  have hT : ∀ n, T n ≤ V := by
    intro n
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      have h1 := hTr n
      have h3 := hεW n
      have h4 : b * T n ≤ b * V := mul_le_mul_of_nonneg_left ih hb
      have : ρ * T (n + 1) ≤ ρ * V := by nlinarith
      exact le_of_mul_le_mul_left this hρ0
  -- the weighted supremum
  have hWle : W ≤ max V (E / (a - ρ)) :=
    ciSup_le fun n => max_le ((hS n).trans (le_max_right _ _)) ((hT n).trans (le_max_left _ _))
  have hT00 := hT0 0
  have hr : 1 ≤ (a - ρ) / (a - ρ - ε) := by rw [le_div_iff₀ hγ]; linarith
  have key : E ≤ ε * T 0 + 2 * c * (a - ρ) / (a - ρ - ε) := by
    have hc2 : 2 * c ≤ 2 * c * (a - ρ) / (a - ρ - ε) := by
      rw [mul_div_assoc]; nlinarith
    rcases le_max_iff.mp hWle with h | h
    · rcases le_max_iff.mp h with h' | h'
      · have : ε * W ≤ ε * T 0 := mul_le_mul_of_nonneg_left h' hε
        rw [hE]; linarith
      · rw [le_div_iff₀ hρb] at h'
        have h5 : ε * W ≤ (ρ - b - ε) * W := mul_le_mul_of_nonneg_right (by linarith) hW0
        have : ε * W ≤ c := by rw [hE] at h'; nlinarith
        have : 0 ≤ ε * T 0 := mul_nonneg hε hT00
        rw [hE]; linarith
    · rw [le_div_iff₀ hγ'] at h
      have hWc : W ≤ c / (a - ρ - ε) := by rw [le_div_iff₀ hγ]; rw [hE] at h; nlinarith
      have h6 : E ≤ c * (a - ρ) / (a - ρ - ε) := by
        rw [hE]
        calc ε * W + c ≤ ε * (c / (a - ρ - ε)) + c := by gcongr
          _ = c * (a - ρ) / (a - ρ - ε) := by field_simp; ring
      have : 0 ≤ ε * T 0 := mul_nonneg hε hT00
      have : c * (a - ρ) / (a - ρ - ε) ≤ 2 * c * (a - ρ) / (a - ρ - ε) :=
        div_le_div_of_nonneg_right (by nlinarith) hγ.le
      linarith
  calc S 0 ≤ E / (a - ρ) := hS 0
    _ ≤ (ε * T 0 + 2 * c * (a - ρ) / (a - ρ - ε)) / (a - ρ) :=
        div_le_div_of_nonneg_right key hγ'.le
    _ = ε * T 0 / (a - ρ) + 2 * c / (a - ρ - ε) := by field_simp

/-- **A discrete dichotomy estimate.** Let `s`, `t ≥ 0` (a centre and a stable component) grow at
most like `ρⁿ` and satisfy `a sₙ ≤ sₙ₊₁ + ε max(sₙ, tₙ) + c ρⁿ` (the centre expands at least by
`a`) and `tₙ₊₁ ≤ b tₙ + ε max(sₙ, tₙ) + c ρⁿ` (the stable part contracts at least by `b`), with
`0 ≤ b < ρ`, `b + 2ε ≤ ρ`, `ρ + ε < a`, `c ≥ 0`. Then the initial centre component is controlled
by the initial stable one: `s₀ ≤ ε t₀/(a − ρ) + 2c/(a − ρ − ε)`. (Lyapunov–Perron: the centre
component is the backward sum, the stable one the forward sum, in the weight `ρⁿ`.) -/
@[tmio T, powerlib_foundation] theorem dichotomy_centre_le {s t : ℕ → ℝ} {a b ρ ε c M : ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, 0 ≤ t n) (hε : 0 ≤ ε) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hbρ : b < ρ) (hρ : b + 2 * ε ≤ ρ) (hρa : ρ + ε < a) (hM : ∀ n, max (s n) (t n) ≤ M * ρ ^ n)
    (hsr : ∀ n, a * s n ≤ s (n + 1) + ε * max (s n) (t n) + c * ρ ^ n)
    (htr : ∀ n, t (n + 1) ≤ b * t n + ε * max (s n) (t n) + c * ρ ^ n) :
    s 0 ≤ ε * t 0 / (a - ρ) + 2 * c / (a - ρ - ε) := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt hb hbρ
  have hpow : ∀ n, 0 < ρ ^ n := fun n => pow_pos hρ0 n
  have hmax : ∀ n, max (s n / ρ ^ n) (t n / ρ ^ n) = max (s n) (t n) / ρ ^ n := fun n =>
    max_div_div_right (hpow n).le _ _
  have h := dichotomy_normalized (S := fun n => s n / ρ ^ n) (T := fun n => t n / ρ ^ n)
    (M := M) (fun n => div_nonneg (hs n) (hpow n).le) (fun n => div_nonneg (ht n) (hpow n).le)
    hε hc hb hbρ hρ hρa
    (fun n => by
      show max (s n / ρ ^ n) (t n / ρ ^ n) ≤ M
      rw [hmax, div_le_iff₀ (hpow n)]; exact hM n)
    (fun n => by
      show a * (s n / ρ ^ n) ≤ ρ * (s (n + 1) / ρ ^ (n + 1)) +
        ε * max (s n / ρ ^ n) (t n / ρ ^ n) + c
      rw [hmax]
      have e : ρ * (s (n + 1) / ρ ^ (n + 1)) + ε * (max (s n) (t n) / ρ ^ n) + c =
          (s (n + 1) + ε * max (s n) (t n) + c * ρ ^ n) / ρ ^ n := by
        rw [pow_succ]; field_simp
      rw [e, mul_div_assoc', div_le_div_iff_of_pos_right (hpow n)]
      exact hsr n)
    (fun n => by
      show ρ * (t (n + 1) / ρ ^ (n + 1)) ≤ b * (t n / ρ ^ n) +
        ε * max (s n / ρ ^ n) (t n / ρ ^ n) + c
      rw [hmax]
      have e1 : ρ * (t (n + 1) / ρ ^ (n + 1)) = t (n + 1) / ρ ^ n := by
        rw [pow_succ]; field_simp
      have e2 : b * (t n / ρ ^ n) + ε * (max (s n) (t n) / ρ ^ n) + c =
          (b * t n + ε * max (s n) (t n) + c * ρ ^ n) / ρ ^ n := by
        field_simp
      rw [e1, e2, div_le_div_iff_of_pos_right (hpow n)]
      exact htr n)
  simpa using h

/-! ## Second differences -/

section SecondDifference

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Second differences of a map with Lipschitz derivative.** If `φ` is differentiable and
`Dφ` is `L₂`-Lipschitz, then `‖φ(z + d) − φ(z) − (φ(z' + d) − φ(z'))‖ ≤ L₂ ‖d‖ ‖z − z'‖`
(the mean value inequality for `z ↦ φ(z + d) − φ(z)`, whose derivative is bounded by
`L₂ ‖d‖`). -/
@[tmio T, powerlib_foundation] theorem norm_secondDiff_le {φ : E → F} {L₂ : NNReal}
    (hd : Differentiable ℝ φ) (hL : LipschitzWith L₂ (fderiv ℝ φ)) (z z' d : E) :
    ‖φ (z + d) - φ z - (φ (z' + d) - φ z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖ := by
  have hG : ∀ x ∈ (Set.univ : Set E), HasFDerivWithinAt (fun x => φ (x + d) - φ x)
      (fderiv ℝ φ (x + d) - fderiv ℝ φ x) Set.univ x := by
    intro x _
    have h1 : HasFDerivAt (fun x => φ (x + d)) (fderiv ℝ φ (x + d)) x := by
      have := (hd (x + d)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const d)
      simpa [Function.comp_def] using this
    exact (h1.sub (hd x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ x ∈ (Set.univ : Set E), ‖fderiv ℝ φ (x + d) - fderiv ℝ φ x‖ ≤ L₂ * ‖d‖ := by
    intro x _
    have := hL.norm_sub_le (x + d) x
    simpa using this
  have := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le hG hbound (Set.mem_univ z')
    (Set.mem_univ z)
  simpa using this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- **Second differences along two pairs of points.** For an `ε`-Lipschitz `k` whose second
differences are bounded by `L₂ ‖d‖ ‖z − z'‖`,
`‖k P − k Q − (k P' − k Q')‖ ≤ ε ‖(P − Q) − (P' − Q')‖ + L₂ ‖P' − Q'‖ ‖Q − Q'‖`
(compare `P` with `Q + (P' − Q')`, then take the second difference of `k` at `Q`, `Q'` with
the increment `P' − Q'`). -/
@[tmio T, powerlib_foundation] theorem norm_secondDiff_pairs_le {k : E → F} {ε : NNReal} {L₂ : ℝ}
    (hk : LipschitzWith ε k)
    (hk₂ : ∀ z z' d : E, ‖k (z + d) - k z - (k (z' + d) - k z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖)
    (P Q P' Q' : E) :
    ‖k P - k Q - (k P' - k Q')‖ ≤ ε * ‖(P - Q) - (P' - Q')‖ + L₂ * ‖P' - Q'‖ * ‖Q - Q'‖ := by
  have e : k P - k Q - (k P' - k Q') = (k P - k (Q + (P' - Q'))) +
      (k (Q + (P' - Q')) - k Q - (k (Q' + (P' - Q')) - k Q')) := by
    rw [add_sub_cancel]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hk₂ Q Q' (P' - Q')))
  have := hk.norm_sub_le P (Q + (P' - Q'))
  have e2 : P - (Q + (P' - Q')) = (P - Q) - (P' - Q') := by abel
  rwa [e2] at this

end SecondDifference

/-! ## The Lipschitz estimate -/

/-- The Lipschitz constant of the asymptotic phase in the weight `ρ`, for a second-difference
gain `K`: `((a − ρ)² − ε²) / ((a − ρ − ε)² − 2K(a − ρ))`; for `K = 0` and `ρ = b + 2ε` it is
`1 + 2ε/(a − b − 3ε)`. -/
def phaseLipConst (a ρ ε K : ℝ) : ℝ :=
  ((a - ρ) ^ 2 - ε ^ 2) / ((a - ρ - ε) ^ 2 - 2 * K * (a - ρ))

section Lipschitz

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [CompleteSpace X]

variable {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {f : X × Y → X} {g : X × Y → Y} {a b α : ℝ}
  {ε : NNReal} {h : X → Y}

/-- **The asymptotic phase is Lipschitz near the graph under bunching.** In the setting of
`theorem/Map/AsymptoticPhase.lean` with `‖A x‖ ≤ α ‖x‖`, let the second differences of `f` and
`g` be bounded by `L₂ ‖d‖ ‖z − z'‖` (e.g. `C¹` with `L₂`-Lipschitz derivative,
`norm_secondDiff_le`), and let the weight `ρ` satisfy `b + 2ε ≤ ρ`, `(b + 2ε)(α + ε) ≤ ρ`,
`b < ρ`, `ρ + ε < a` (bunching). With `K = L₂ (1 + ε/(a − b − 3ε)) Z` and
`2K(a − ρ) < (a − ρ − ε)²`, every `p'` with `‖p'₂ − h(p'₁)‖ ≤ Z` and every `p` satisfy
`‖φ(p) − φ(p')‖ ≤ ((a − ρ)² − ε²)/((a − ρ − ε)² − 2K(a − ρ)) ‖p − p'‖`. -/
@[tmio T, powerlib_foundation] theorem norm_asymptoticPhase_sub_le_mul
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (haα : a ≤ α) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f)
    (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a) (hh : LipschitzWith 1 h)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {L₂ : NNReal}
    (hf₂ : ∀ z z' d : X × Y, ‖f (z + d) - f z - (f (z' + d) - f z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖)
    (hg₂ : ∀ z z' d : X × Y, ‖g (z + d) - g z - (g (z' + d) - g z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖)
    {ρ Z : ℝ} (hρ : b + 2 * ε ≤ ρ) (hρα : (b + 2 * ε) * (α + ε) ≤ ρ) (hbρ : b < ρ)
    (hρa : ρ + ε < a)
    (hK : 2 * (L₂ * (1 + ε / (a - b - 3 * ε)) * Z) * (a - ρ) < (a - ρ - ε) ^ 2)
    {p p' : X × Y} (hp' : ‖p'.2 - h p'.1‖ ≤ Z) :
    ‖asymptoticPhase A B f g h p - asymptoticPhase A B f g h p'‖ ≤
      phaseLipConst a ρ ε (L₂ * (1 + ε / (a - b - 3 * ε)) * Z) * ‖p - p'‖ := by
  have hε := ε.coe_nonneg
  have hL₂ := L₂.coe_nonneg
  have hgap' : 0 < a - b - 3 * ε := by linarith
  have hbα : b ≤ α := by linarith
  have hαε : 0 ≤ α + ε := by linarith
  have hb2 : 0 ≤ b + 2 * ε := by linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt hb hbρ
  have hZ : 0 ≤ Z := (norm_nonneg _).trans hp'
  set D := 1 + ε / (a - b - 3 * ε) with hD
  have hD0 : 0 ≤ D := by positivity
  set K := L₂ * D * Z with hKdef
  have hK0 : 0 ≤ K := by positivity
  set F := splitMap A B f g with hF
  set x₀ := asymptoticPhase A B f g h p with hx₀
  set x₀' := asymptoticPhase A B f g h p' with hx₀'
  set q : X × Y := (x₀, h x₀) with hq
  set q' : X × Y := (x₀', h x₀') with hq'
  set δ := ‖x₀ - x₀'‖ with hδ
  set d := ‖p - p'‖ with hd
  set c := K * δ with hc
  have hc0 : 0 ≤ c := by positivity
  set w : ℕ → X × Y := fun n => (F^[n] p - F^[n] q) - (F^[n] p' - F^[n] q') with hw
  -- the two orbits approach their graph orbits, which separate at most like `(α + ε)ⁿ`
  have hu : ∀ n, ‖F^[n] p - F^[n] q‖ ≤ D * (b + 2 * ε) ^ n * ‖p.2 - h p.1‖ := fun n =>
    norm_iterate_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv p n
  have hu' : ∀ n, ‖F^[n] p' - F^[n] q'‖ ≤ D * (b + 2 * ε) ^ n * Z := fun n =>
    (norm_iterate_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv p' n).trans
      (mul_le_mul_of_nonneg_left hp' (by positivity))
  have hqq : ∀ n, ‖F^[n] q - F^[n] q'‖ ≤ (α + ε) ^ n * δ := fun n => by
    have := norm_iterate_splitMap_sub_le hAα hB hb hbα hf hg n q q'
    rwa [hq, hq', norm_graph_sub hh] at this
  -- the recursion of the differences of differences
  have hstep1 : ∀ n, (w (n + 1)).1 = A (w n).1 +
      (f (F^[n] p) - f (F^[n] q) - (f (F^[n] p') - f (F^[n] q'))) := by
    intro n
    simp only [hw, Function.iterate_succ_apply', hF, splitMap, Prod.fst_sub, map_sub]
    abel
  have hstep2 : ∀ n, (w (n + 1)).2 = B (w n).2 +
      (g (F^[n] p) - g (F^[n] q) - (g (F^[n] p') - g (F^[n] q'))) := by
    intro n
    simp only [hw, Function.iterate_succ_apply', hF, splitMap, Prod.snd_sub, map_sub]
    abel
  have hσ : ∀ n, (L₂ : ℝ) * ‖F^[n] p' - F^[n] q'‖ * ‖F^[n] q - F^[n] q'‖ ≤ c * ρ ^ n := by
    intro n
    have h1 : (L₂ : ℝ) * ‖F^[n] p' - F^[n] q'‖ * ‖F^[n] q - F^[n] q'‖ ≤
        L₂ * (D * (b + 2 * ε) ^ n * Z) * ((α + ε) ^ n * δ) := by
      gcongr
      exacts [hu' n, hqq n]
    have h2 : ((b + 2 * ε) * (α + ε)) ^ n ≤ ρ ^ n := pow_le_pow_left₀ (by positivity) hρα n
    calc _ ≤ L₂ * (D * (b + 2 * ε) ^ n * Z) * ((α + ε) ^ n * δ) := h1
      _ = c * ((b + 2 * ε) * (α + ε)) ^ n := by rw [hc, hKdef, mul_pow]; ring
      _ ≤ c * ρ ^ n := mul_le_mul_of_nonneg_left h2 hc0
  have hwn : ∀ n, ‖w n‖ = max ‖(w n).1‖ ‖(w n).2‖ := fun n => Prod.norm_def _
  have hΔf : ∀ n, ‖f (F^[n] p) - f (F^[n] q) - (f (F^[n] p') - f (F^[n] q'))‖ ≤
      ε * max ‖(w n).1‖ ‖(w n).2‖ + c * ρ ^ n := fun n => by
    rw [← hwn]
    exact (norm_secondDiff_pairs_le hf hf₂ _ _ _ _).trans (add_le_add le_rfl (hσ n))
  have hΔg : ∀ n, ‖g (F^[n] p) - g (F^[n] q) - (g (F^[n] p') - g (F^[n] q'))‖ ≤
      ε * max ‖(w n).1‖ ‖(w n).2‖ + c * ρ ^ n := fun n => by
    rw [← hwn]
    exact (norm_secondDiff_pairs_le hg hg₂ _ _ _ _).trans (add_le_add le_rfl (hσ n))
  have hsr : ∀ n, a * ‖(w n).1‖ ≤ ‖(w (n + 1)).1‖ + ε * max ‖(w n).1‖ ‖(w n).2‖ + c * ρ ^ n := by
    intro n
    have h2 : A (w n).1 = (w (n + 1)).1 -
        (f (F^[n] p) - f (F^[n] q) - (f (F^[n] p') - f (F^[n] q'))) := by
      rw [hstep1]; abel
    calc a * ‖(w n).1‖ ≤ ‖A (w n).1‖ := hA _
      _ ≤ ‖(w (n + 1)).1‖ + ‖f (F^[n] p) - f (F^[n] q) - (f (F^[n] p') - f (F^[n] q'))‖ := by
          rw [h2]; exact norm_sub_le _ _
      _ ≤ _ := by linarith [hΔf n]
  have htr : ∀ n, ‖(w (n + 1)).2‖ ≤ b * ‖(w n).2‖ + ε * max ‖(w n).1‖ ‖(w n).2‖ + c * ρ ^ n := by
    intro n
    rw [hstep2]
    calc _ ≤ ‖B (w n).2‖ + ‖g (F^[n] p) - g (F^[n] q) - (g (F^[n] p') - g (F^[n] q'))‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith [hB (w n).2, hΔg n]
  have hM : ∀ n, max ‖(w n).1‖ ‖(w n).2‖ ≤ (D * (‖p.2 - h p.1‖ + Z)) * ρ ^ n := by
    intro n
    rw [← hwn]
    have h2 : (b + 2 * ε) ^ n ≤ ρ ^ n := pow_le_pow_left₀ hb2 hρ n
    calc ‖w n‖ ≤ ‖F^[n] p - F^[n] q‖ + ‖F^[n] p' - F^[n] q'‖ := norm_sub_le _ _
      _ ≤ D * (b + 2 * ε) ^ n * ‖p.2 - h p.1‖ + D * (b + 2 * ε) ^ n * Z := add_le_add (hu n) (hu' n)
      _ = (D * (‖p.2 - h p.1‖ + Z)) * (b + 2 * ε) ^ n := by ring
      _ ≤ (D * (‖p.2 - h p.1‖ + Z)) * ρ ^ n := by gcongr
  have hmain := dichotomy_centre_le (s := fun n => ‖(w n).1‖) (t := fun n => ‖(w n).2‖)
    (fun n => norm_nonneg _) (fun n => norm_nonneg _) hε hc0 hb hbρ hρ hρa hM hsr htr
  -- back to the phases
  have hw0 : w 0 = (p - q) - (p' - q') := rfl
  have hs0 : (w 0).1 = (p.1 - p'.1) - (x₀ - x₀') := by
    rw [hw0]; simp only [Prod.fst_sub, hq, hq']; abel
  have ht0 : ‖(w 0).2‖ ≤ d + δ := by
    have e : (w 0).2 = (p.2 - p'.2) - (h x₀ - h x₀') := by
      rw [hw0]; simp only [Prod.snd_sub, hq, hq']; abel
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [← Prod.snd_sub]; exact norm_snd_le _
    · simpa using hh.norm_sub_le x₀ x₀'
  have hδs : δ ≤ d + ‖(w 0).1‖ := by
    have e : x₀ - x₀' = (p.1 - p'.1) - (w 0).1 := by rw [hs0]; abel
    rw [hδ, e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    rw [← Prod.fst_sub]; exact norm_fst_le _
  -- the algebra
  set γ := a - ρ with hγ
  have hγε : 0 < γ - ε := by linarith
  have hγ0 : 0 < γ := by linarith
  have hden : 0 < (γ - ε) ^ 2 - 2 * K * γ := by linarith
  have h2 : ‖(w 0).1‖ * (γ * (γ - ε)) ≤ ε * ‖(w 0).2‖ * (γ - ε) + 2 * c * γ := by
    rw [div_add_div _ _ hγ0.ne' hγε.ne', le_div_iff₀ (mul_pos hγ0 hγε)] at hmain
    linarith
  have h3 : ε * ‖(w 0).2‖ * (γ - ε) ≤ ε * (d + δ) * (γ - ε) := by gcongr
  have h4 : δ * (γ * (γ - ε)) ≤ (d + ‖(w 0).1‖) * (γ * (γ - ε)) :=
    mul_le_mul_of_nonneg_right hδs (by positivity)
  show δ ≤ phaseLipConst a ρ ε K * d
  rw [phaseLipConst, ← hγ, div_mul_eq_mul_div, le_div_iff₀ hden]
  rw [hc] at h2
  nlinarith

/-- The constant `phaseLipConst` is nonnegative where the smallness condition holds. -/
@[tmio T, powerlib_foundation] theorem phaseLipConst_nonneg {a ρ ε K : ℝ} (hε : 0 ≤ ε)
    (hρa : ρ + ε < a) (hK : 2 * K * (a - ρ) < (a - ρ - ε) ^ 2) : 0 ≤ phaseLipConst a ρ ε K := by
  have h1 : 0 ≤ (a - ρ) ^ 2 - ε ^ 2 := by nlinarith
  exact div_nonneg h1 (by linarith)

/-- **The Lipschitz estimate far from the graph.** Under the hypotheses of
`norm_asymptoticPhase_sub_le_mul`, but with the smallness condition only after `N` steps
(`2 K_N (a − ρ) < (a − ρ − ε)²`, `K_N = L₂ (1 + ε/(a − b − 3ε)) (b + 2ε)ᴺ Z`): for every `p` and
every `p'` with `‖p'₂ − h(p'₁)‖ ≤ Z`,
`‖φ(p) − φ(p')‖ ≤ ((α + ε)/(a − ε))ᴺ · phaseLipConst a ρ ε K_N · ‖p − p'‖`
(`φ = r⁻ᴺ ∘ φ ∘ Fᴺ`, `F` is `(α + ε)`-Lipschitz, `r⁻¹` is `1/(a − ε)`-Lipschitz, and `Fᴺ p'` is
within `(b + 2ε)ᴺ Z` of the graph). -/
@[tmio T, powerlib_foundation] theorem norm_asymptoticPhase_sub_le_mul_iterate
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (haα : a ≤ α) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f)
    (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a) (hh : LipschitzWith 1 h)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {L₂ : NNReal}
    (hf₂ : ∀ z z' d : X × Y, ‖f (z + d) - f z - (f (z' + d) - f z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖)
    (hg₂ : ∀ z z' d : X × Y, ‖g (z + d) - g z - (g (z' + d) - g z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖)
    {ρ Z : ℝ} (hρ : b + 2 * ε ≤ ρ) (hρα : (b + 2 * ε) * (α + ε) ≤ ρ) (hbρ : b < ρ)
    (hρa : ρ + ε < a) (N : ℕ)
    (hK : 2 * (L₂ * (1 + ε / (a - b - 3 * ε)) * ((b + 2 * ε) ^ N * Z)) * (a - ρ) <
      (a - ρ - ε) ^ 2)
    {p p' : X × Y} (hp' : ‖p'.2 - h p'.1‖ ≤ Z) :
    ‖asymptoticPhase A B f g h p - asymptoticPhase A B f g h p'‖ ≤
      ((α + ε) / (a - ε)) ^ N *
        phaseLipConst a ρ ε (L₂ * (1 + ε / (a - b - 3 * ε)) * ((b + 2 * ε) ^ N * Z)) *
          ‖p - p'‖ := by
  have hε := ε.coe_nonneg
  have hpos : 0 < a - ε := by linarith
  have hbα : b ≤ α := by linarith
  have hb2 : 0 ≤ b + 2 * ε := by linarith
  set F := splitMap A B f g with hF
  set Λ := phaseLipConst a ρ ε (L₂ * (1 + ε / (a - b - 3 * ε)) * ((b + 2 * ε) ^ N * Z))
  have hΛ : 0 ≤ Λ := phaseLipConst_nonneg hε hρa hK
  have hpN : ‖(F^[N] p').2 - h (F^[N] p').1‖ ≤ (b + 2 * ε) ^ N * Z :=
    (norm_iterate_sub_graph_le hB hb hf hg hh hinv p' N).trans
      (mul_le_mul_of_nonneg_left hp' (pow_nonneg hb2 N))
  have h1 := le_norm_iterate_reducedMap_sub hA hf (by linarith) hh N
    (asymptoticPhase A B f g h p) (asymptoticPhase A B f g h p')
  rw [← asymptoticPhase_iterate hAs hA hB hb hf hg hgap hh hinv,
    ← asymptoticPhase_iterate hAs hA hB hb hf hg hgap hh hinv] at h1
  have h2 := norm_asymptoticPhase_sub_le_mul hAs hA hAα haα hB hb hf hg hgap hh hinv hf₂ hg₂ hρ
    hρα hbρ hρa hK (p := F^[N] p) hpN
  have h3 := norm_iterate_splitMap_sub_le hAα hB hb hbα hf hg N p p'
  have hk : 0 < (a - ε) ^ N := pow_pos hpos N
  have h4 : (a - ε) ^ N * ‖asymptoticPhase A B f g h p - asymptoticPhase A B f g h p'‖ ≤
      Λ * ((α + ε) ^ N * ‖p - p'‖) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hΛ))
  rw [div_pow]
  calc _ = ((a - ε) ^ N * ‖asymptoticPhase A B f g h p - asymptoticPhase A B f g h p'‖) /
        (a - ε) ^ N := by field_simp
    _ ≤ Λ * ((α + ε) ^ N * ‖p - p'‖) / (a - ε) ^ N := div_le_div_of_nonneg_right h4 hk.le
    _ = _ := by ring

/-- A weight for the bunching condition: under `b + 3ε < a` and `(b + 2ε)(α + ε) < a − ε`, the
midpoint `ρ` of `max(b + 2ε, (b + 2ε)(α + ε))` and `a − ε` satisfies the weight conditions of
`norm_asymptoticPhase_sub_le_mul`. -/
@[tmio T, powerlib_foundation] theorem exists_weight {a b α ε : ℝ} (hε : 0 ≤ ε)
    (hgap : b + 3 * ε < a) (hbunch : (b + 2 * ε) * (α + ε) < a - ε) :
    ∃ ρ, b + 2 * ε ≤ ρ ∧ (b + 2 * ε) * (α + ε) ≤ ρ ∧ b < ρ ∧ ρ + ε < a := by
  refine ⟨(max (b + 2 * ε) ((b + 2 * ε) * (α + ε)) + (a - ε)) / 2, ?_, ?_, ?_, ?_⟩
  · have := le_max_left (b + 2 * ε) ((b + 2 * ε) * (α + ε)); linarith
  · have := le_max_right (b + 2 * ε) ((b + 2 * ε) * (α + ε))
    have := max_lt (by linarith : b + 2 * ε < a - ε) hbunch
    linarith
  · have := le_max_left (b + 2 * ε) ((b + 2 * ε) * (α + ε)); linarith
  · have := max_lt (by linarith : b + 2 * ε < a - ε) hbunch
    linarith

/-- **The phase is Lipschitz on every neighbourhood `{‖p₂ − h(p₁)‖ ≤ Z}` of the graph**, under
the gap `b + 3ε < a`, the bunching condition `(b + 2ε)(α + ε) < a − ε`, attraction
`b + 2ε < 1` and second differences of `f`, `g` bounded by `L₂ ‖d‖ ‖z − z'‖` (the constant is
`norm_asymptoticPhase_sub_le_mul_iterate` for `N` large). -/
@[tmio T, powerlib_foundation] theorem lipschitzOnWith_asymptoticPhase
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (haα : a ≤ α) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f)
    (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a) (hbunch : (b + 2 * ε) * (α + ε) < a - ε)
    (hθ : b + 2 * ε < 1) (hh : LipschitzWith 1 h)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {L₂ : NNReal}
    (hf₂ : ∀ z z' d : X × Y, ‖f (z + d) - f z - (f (z' + d) - f z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖)
    (hg₂ : ∀ z z' d : X × Y, ‖g (z + d) - g z - (g (z' + d) - g z')‖ ≤ L₂ * ‖d‖ * ‖z - z'‖)
    (Z : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (asymptoticPhase A B f g h) {p | ‖p.2 - h p.1‖ ≤ Z} := by
  have hε := ε.coe_nonneg
  obtain ⟨ρ, hρ, hρα, hbρ, hρa⟩ := exists_weight hε hgap hbunch
  have hb2 : 0 ≤ b + 2 * ε := by linarith
  have hpos : 0 < (a - ρ - ε) ^ 2 := by have : 0 < a - ρ - ε := by linarith
                                        positivity
  have hlim : Tendsto (fun N : ℕ => 2 * (L₂ * (1 + ε / (a - b - 3 * ε)) * ((b + 2 * ε) ^ N * Z)) *
      (a - ρ)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hb2 hθ).mul_const Z).const_mul
      (2 * (L₂ * (1 + ε / (a - b - 3 * ε))))
    have := this.mul_const (a - ρ)
    simpa [mul_assoc] using this
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  set C := ((α + ε) / (a - ε)) ^ N *
    phaseLipConst a ρ ε (L₂ * (1 + ε / (a - b - 3 * ε)) * ((b + 2 * ε) ^ N * Z))
  refine ⟨C.toNNReal, LipschitzOnWith.of_dist_le_mul fun p _ p' hp' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  refine (norm_asymptoticPhase_sub_le_mul_iterate hAs hA hAα haα hB hb hf hg hgap hh hinv hf₂ hg₂
    hρ hρα hbρ hρa N hN (p := p) hp').trans ?_
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

/-- **The phase is locally Lipschitz** for `f`, `g` differentiable with `L₂`-Lipschitz derivatives
(no smoothness of the graph `h` is assumed), under the gap `b + 3ε < a`, the bunching condition
`(b + 2ε)(α + ε) < a − ε` and attraction `b + 2ε < 1`. -/
@[tmio T, powerlib_foundation] theorem locallyLipschitz_asymptoticPhase
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (haα : a ≤ α) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f)
    (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a) (hbunch : (b + 2 * ε) * (α + ε) < a - ε)
    (hθ : b + 2 * ε < 1) (hh : LipschitzWith 1 h)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {L₂ : NNReal}
    (hfd : Differentiable ℝ f) (hfL : LipschitzWith L₂ (fderiv ℝ f)) (hgd : Differentiable ℝ g)
    (hgL : LipschitzWith L₂ (fderiv ℝ g)) :
    LocallyLipschitz (asymptoticPhase A B f g h) := by
  intro p₀
  obtain ⟨K, hK⟩ := lipschitzOnWith_asymptoticPhase hAs hA hAα haα hB hb hf hg hgap hbunch hθ hh
    hinv (norm_secondDiff_le hfd hfL) (norm_secondDiff_le hgd hgL) (‖p₀.2 - h p₀.1‖ + 1)
  refine ⟨K, _, ?_, hK⟩
  have hc : Continuous fun p : X × Y => ‖p.2 - h p.1‖ :=
    (continuous_snd.sub (hh.continuous.comp continuous_fst)).norm
  exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds
    (by show ‖p₀.2 - h p₀.1‖ < ‖p₀.2 - h p₀.1‖ + 1; linarith)) fun p hp =>
      show ‖p.2 - h p.1‖ ≤ _ from le_of_lt hp

/-- **The flip setting** (`theorem/Periodic/FlipReduction.lean`): `A = −id` (a simple multiplier
`−1`, `a = α = 1`), `‖B y‖ ≤ b ‖y‖` with `0 ≤ b < 1`, and nonlinearities `f`, `g` that are
`ε`-Lipschitz with `0 < ε ≤ (1 − b)/8` (as a cut-off makes them near the fixed point) and
differentiable with `L₂`-Lipschitz derivatives. The bunching condition
`(b + 2ε)(1 + ε) < 1 − ε` then holds, with the weight `ρ = (b + 2ε)(1 + ε)`, so the asymptotic
phase is `8`-Lipschitz in the neighbourhood `L₂ ‖p'₂ − h(p'₁)‖ ≤ (1 − b)/20` of the graph (for
`h(0) = 0` this contains the ball `L₂ ‖p'‖ ≤ (1 − b)/40` around the fixed point), and locally
Lipschitz everywhere. -/
@[tmio T, powerlib_foundation] theorem flip_asymptoticPhase_lipschitz {B : Y →L[ℝ] Y} {b : ℝ}
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hb1 : b < 1) (hε : 0 < ε)
    (hε8 : (ε : ℝ) ≤ (1 - b) / 8) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g)
    {L₂ : NNReal} (hfd : Differentiable ℝ f) (hfL : LipschitzWith L₂ (fderiv ℝ f))
    (hgd : Differentiable ℝ g) (hgL : LipschitzWith L₂ (fderiv ℝ g)) (hh : LipschitzWith 1 h)
    (hinv : ∀ x, h (-x + f (x, h x)) = B (h x) + g (x, h x)) :
    (∀ (Z : ℝ) (p p' : X × Y), L₂ * Z ≤ (1 - b) / 20 → ‖p'.2 - h p'.1‖ ≤ Z →
      ‖asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h p -
        asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h p'‖ ≤ 8 * ‖p - p'‖) ∧
      LocallyLipschitz (asymptoticPhase (-ContinuousLinearMap.id ℝ X) B f g h) := by
  set A := -ContinuousLinearMap.id ℝ X with hAdef
  have hε0 := ε.coe_nonneg
  have hεpos : (0 : ℝ) < ε := hε
  have hL₂ := L₂.coe_nonneg
  have hAs : Function.Surjective A := fun x => ⟨-x, by simp [hAdef]⟩
  have hA : ∀ x, 1 * ‖x‖ ≤ ‖A x‖ := fun x => by simp [hAdef]
  have hAα : ∀ x, ‖A x‖ ≤ 1 * ‖x‖ := fun x => by simp [hAdef]
  have hinv' : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x) := fun x => by
    simpa [hAdef] using hinv x
  have hgap : b + 3 * ε < 1 := by linarith
  have hθ : b + 2 * ε < 1 := by linarith
  set ρ := (b + 2 * ε) * (1 + ε) with hρdef
  have hρ : b + 2 * ε ≤ ρ := by nlinarith
  have hbρ : b < ρ := by nlinarith
  have hρ1 : ρ ≤ b + 3 * ε := by nlinarith [mul_le_mul_of_nonneg_left hθ.le hε0]
  have hρa : ρ + ε < 1 := by linarith
  have hbunch : (b + 2 * ε) * (1 + ε) < 1 - ε := by linarith
  refine ⟨fun Z p p' hZ hp' => ?_, locallyLipschitz_asymptoticPhase hAs hA hAα le_rfl hB hb hf hg
    hgap hbunch hθ hh hinv' hfd hfL hgd hgL⟩
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hp'
  have h3ε : 0 < 1 - b - 3 * ε := by linarith
  have hD : 1 + ε / (1 - b - 3 * ε) ≤ 6 / 5 := by
    have : ε / (1 - b - 3 * ε) ≤ 1 / 5 := by rw [div_le_iff₀ h3ε]; linarith
    linarith
  have hD0 : 0 ≤ 1 + ε / (1 - b - 3 * ε) := by positivity
  set K := L₂ * (1 + ε / (1 - b - 3 * ε)) * Z with hKdef
  have hLZ : 0 ≤ (L₂ : ℝ) * Z := by positivity
  have hK : K ≤ 3 * (1 - b) / 50 := by
    have : K = (1 + ε / (1 - b - 3 * ε)) * (L₂ * Z) := by rw [hKdef]; ring
    rw [this]
    calc _ ≤ 6 / 5 * ((1 - b) / 20) := mul_le_mul hD hZ hLZ (by norm_num)
      _ = 3 * (1 - b) / 50 := by ring
  have hK0 : 0 ≤ K := by positivity
  have hγ1 : 1 - ρ ≤ 1 - b := by linarith
  have hγε : (1 - b) / 2 ≤ 1 - ρ - ε := by linarith
  have hsq : ((1 - b) / 2) ^ 2 ≤ (1 - ρ - ε) ^ 2 := pow_le_pow_left₀ (by linarith) hγε 2
  have h2K : 2 * K * (1 - ρ) ≤ 2 * (3 * (1 - b) / 50) * (1 - b) := by
    have : 0 ≤ 1 - ρ := by linarith
    have := mul_le_mul hK hγ1 this (by linarith)
    nlinarith
  have hb1' : 0 < 1 - b := by linarith
  have hKcond : 2 * K * (1 - ρ) < (1 - ρ - ε) ^ 2 := by nlinarith
  have h := norm_asymptoticPhase_sub_le_mul hAs hA hAα le_rfl hB hb hf hg hgap hh hinv'
    (norm_secondDiff_le hfd hfL) (norm_secondDiff_le hgd hgL) hρ le_rfl hbρ hρa hKcond
    (p := p) hp'
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hden : 0 < (1 - ρ - ε) ^ 2 - 2 * K * (1 - ρ) := by linarith
  rw [phaseLipConst, div_le_iff₀ hden]
  have hsq1 : (1 - ρ) ^ 2 ≤ (1 - b) ^ 2 := pow_le_pow_left₀ (by linarith) hγ1 2
  nlinarith

end Lipschitz

/-! ## A merely Lipschitz nonlinearity with a non-Lipschitz phase -/

section Kink

/-- The kink `ε min(|x|, |y|)` on `ℝ × ℝ`: globally `ε`-Lipschitz, `0` on the axes, not
differentiable along the diagonals. -/
def kinkMap (ε : ℝ) (p : ℝ × ℝ) : ℝ := ε * min |p.1| |p.2|

/-- The kink is `ε`-Lipschitz (max norm on `ℝ × ℝ`). -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_kinkMap (ε : NNReal) :
    LipschitzWith ε (kinkMap ε) := by
  refine LipschitzWith.of_dist_le_mul fun p p' => ?_
  rw [Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, kinkMap, kinkMap, ← mul_sub,
    abs_mul, abs_of_nonneg ε.coe_nonneg]
  refine mul_le_mul_of_nonneg_left ((abs_min_sub_min_le_max _ _ _ _).trans ?_) ε.coe_nonneg
  exact max_le_max (abs_abs_sub_abs_le_abs_sub _ _) (abs_abs_sub_abs_le_abs_sub _ _)

variable {a b : ℝ} {ε : NNReal}

/-- The hypotheses of the asymptotic phase hold for the kink example
`F(x, y) = (a x + ε min(|x|, |y|), b y)`, `h = 0`. -/
@[tmio T, powerlib_foundation] private theorem kink_hyps (ha : 0 < a) (hb : 0 ≤ b) :
    Function.Surjective (a • ContinuousLinearMap.id ℝ ℝ) ∧
      (∀ x : ℝ, a * ‖x‖ ≤ ‖(a • ContinuousLinearMap.id ℝ ℝ) x‖) ∧
      (∀ y : ℝ, ‖(b • ContinuousLinearMap.id ℝ ℝ) y‖ ≤ b * ‖y‖) ∧
      LipschitzWith ε (0 : ℝ × ℝ → ℝ) ∧ LipschitzWith 1 (0 : ℝ → ℝ) ∧
      (∀ x : ℝ, (0 : ℝ → ℝ) ((a • ContinuousLinearMap.id ℝ ℝ) x + kinkMap ε (x, (0 : ℝ → ℝ) x)) =
        (b • ContinuousLinearMap.id ℝ ℝ) ((0 : ℝ → ℝ) x) + (0 : ℝ × ℝ → ℝ) (x, (0 : ℝ → ℝ) x)) := by
  refine ⟨fun z => ⟨z / a, by simp; field_simp⟩, fun x => ?_, fun y => ?_,
    (LipschitzWith.const (0 : ℝ)).weaken (by positivity), (LipschitzWith.const (0 : ℝ)).weaken
      zero_le_one, fun x => by simp⟩
  · simp [Real.norm_eq_abs, abs_of_pos ha]
  · simp [Real.norm_eq_abs, abs_of_nonneg hb]

/-- The finite-horizon phases of the kink example are `(Fᴺ p)₁ / aᴺ`. -/
@[tmio T, powerlib_foundation] private theorem kink_phaseApprox (ha : 0 < a) (N : ℕ)
    (p : ℝ × ℝ) :
    phaseApprox (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ) (kinkMap ε) 0 0
      N p = ((splitMap (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ)
        (kinkMap ε) 0)^[N] p).1 / a ^ N := by
  set r := reducedMap (a • ContinuousLinearMap.id ℝ ℝ) (kinkMap ε) (0 : ℝ → ℝ) with hr
  have hrx : ∀ x, r x = a * x := fun x => by
    simp only [hr, reducedMap, kinkMap, Pi.zero_apply, abs_zero, min_eq_right (abs_nonneg x),
      mul_zero, add_zero]
    simp
  have hinv1 : ∀ z, Function.invFun r z = z / a := fun z => by
    have hex : ∃ x, r x = z := ⟨z / a, by rw [hrx]; field_simp⟩
    have := Function.invFun_eq hex
    rw [hrx] at this
    rw [eq_div_iff ha.ne', mul_comm, this]
  have hit : ∀ N z, (Function.invFun r)^[N] z = z / a ^ N := by
    intro N
    induction N with
    | zero => intro z; simp
    | succ N ih =>
      intro z
      rw [Function.iterate_succ_apply, ih, hinv1, pow_succ, div_div, mul_comm a]
  exact hit N _

/-- Along the orbit of `(δ, 1)`, `δ ≥ 0`, of the kink example: `yₙ = bⁿ`, `xₙ ≥ 0` and
`xₙ₊₁ = a xₙ + ε min(xₙ, bⁿ)`. -/
@[tmio T, powerlib_foundation] private theorem kink_iterate (ha : 0 < a) (hb : 0 ≤ b) {δ : ℝ}
    (hδ : 0 ≤ δ) (n : ℕ) :
    ((splitMap (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ) (kinkMap ε)
        0)^[n] (δ, 1)).2 = b ^ n ∧
      0 ≤ ((splitMap (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ)
        (kinkMap ε) 0)^[n] (δ, 1)).1 ∧
      ((splitMap (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ) (kinkMap ε)
        0)^[n + 1] (δ, 1)).1 =
        a * ((splitMap (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ)
          (kinkMap ε) 0)^[n] (δ, 1)).1 + ε * min ((splitMap (a • ContinuousLinearMap.id ℝ ℝ)
            (b • ContinuousLinearMap.id ℝ ℝ) (kinkMap ε) 0)^[n] (δ, 1)).1 (b ^ n) := by
  set F := splitMap (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ)
    (kinkMap ε) 0 with hF
  have hFp : ∀ q : ℝ × ℝ, F q = (a * q.1 + ε * min |q.1| |q.2|, b * q.2) := fun q => by
    simp [hF, splitMap, kinkMap]
  have h12 : ∀ n, (F^[n] (δ, 1)).2 = b ^ n ∧ 0 ≤ (F^[n] (δ, 1)).1 := by
    intro n
    induction n with
    | zero => exact ⟨by simp, hδ⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply', hFp]
      dsimp only
      refine ⟨by rw [ih.1]; ring, ?_⟩
      have := ε.coe_nonneg
      have : 0 ≤ min |(F^[n] (δ, 1)).1| |(F^[n] (δ, 1)).2| :=
        le_min (abs_nonneg _) (abs_nonneg _)
      have := ih.2
      positivity
  refine ⟨(h12 n).1, (h12 n).2, ?_⟩
  rw [Function.iterate_succ_apply', hFp, (h12 n).1, abs_of_nonneg (h12 n).2,
    abs_of_nonneg (pow_nonneg hb n)]

/-- **A Lipschitz nonlinearity whose phase is not Lipschitz.** For `F(x, y) = (a x + ε min(|x|,
|y|), b y)` on `ℝ × ℝ` (`A = a·id`, so `a = α`; `B = b·id`; `g = 0`; the invariant graph
`h = 0`), with `0 < b`, `0 < ε`, `b + 3ε < a`: the phase of `(0, 1)` is `0`, and the phase of
`((b/(a + ε))ᵏ, 1)` is at least `(b/a)ᵏ`; the difference quotients grow like `(1 + ε/a)ᵏ`. -/
@[tmio T, powerlib_foundation] theorem kink_asymptoticPhase (hb : 0 < b) (hε : 0 < ε)
    (hgap : b + 3 * ε < a) :
    asymptoticPhase (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ)
        (kinkMap ε) 0 0 (0, 1) = 0 ∧
      ∀ k : ℕ, (b / a) ^ k ≤ asymptoticPhase (a • ContinuousLinearMap.id ℝ ℝ)
        (b • ContinuousLinearMap.id ℝ ℝ) (kinkMap ε) 0 0 ((b / (a + ε)) ^ k, 1) := by
  have hε0 := ε.coe_nonneg
  have hεpos : (0 : ℝ) < ε := hε
  have ha : 0 < a := by linarith
  obtain ⟨hAs, hA, hB, hg, hh, hinv⟩ := kink_hyps (ε := ε) ha hb.le
  have hlim := fun p => tendsto_phaseApprox hAs hA hB hb.le (lipschitzWith_kinkMap ε) hg hgap
    hh hinv p
  set F := splitMap (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ)
    (kinkMap ε) 0 with hF
  refine ⟨?_, fun k => ?_⟩
  · have h0 : ∀ n, (F^[n] (0, 1)).1 = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [(kink_iterate (ε := ε) ha hb.le le_rfl n).2.2, ih,
          min_eq_left (pow_nonneg hb.le n)]
        ring
    have hc : ∀ N, phaseApprox (a • ContinuousLinearMap.id ℝ ℝ) (b • ContinuousLinearMap.id ℝ ℝ)
        (kinkMap ε) 0 0 N (0, 1) = 0 := fun N => by
      rw [kink_phaseApprox ha, h0, zero_div]
    have := hlim (0, 1)
    simp only [hc] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  · set δ := (b / (a + ε)) ^ k with hδ
    have haε : 0 < a + ε := by linarith
    have hδ0 : 0 ≤ δ := by positivity
    have hq1 : b / (a + ε) ≤ 1 := by rw [div_le_one haε]; linarith
    -- the orbit grows like `(a + ε)ⁿ δ` up to step `k`
    have hup : ∀ n ≤ k, (F^[n] (δ, 1)).1 = (a + ε) ^ n * δ := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hn' : n ≤ k := Nat.le_of_succ_le hn
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hn'
        have hle : (a + ε) ^ n * δ ≤ b ^ n := by
          rw [hδ, hj, pow_add, ← mul_assoc, ← mul_pow, mul_div_cancel₀ _ haε.ne']
          exact mul_le_of_le_one_right (pow_nonneg hb.le n) (pow_le_one₀ (by positivity) hq1)
        rw [(kink_iterate (ε := ε) ha hb.le hδ0 n).2.2, ih hn', min_eq_left hle]
        ring
    have hk : (F^[k] (δ, 1)).1 = b ^ k := by
      rw [hup k le_rfl, hδ, ← mul_pow, mul_div_cancel₀ _ haε.ne']
    -- after step `k` it grows at least like `aⁿ`
    have hlow : ∀ m, a ^ m * b ^ k ≤ (F^[k + m] (δ, 1)).1 := by
      intro m
      induction m with
      | zero => simp [hk]
      | succ m ih =>
        rw [← add_assoc, (kink_iterate (ε := ε) ha hb.le hδ0 (k + m)).2.2, pow_succ]
        have h1 : 0 ≤ (ε : ℝ) * min ((F^[k + m] (δ, 1)).1) (b ^ (k + m)) :=
          mul_nonneg hε0 (le_min (kink_iterate (ε := ε) ha hb.le hδ0 (k + m)).2.1
            (pow_nonneg hb.le _))
        nlinarith
    refine ge_of_tendsto (hlim (δ, 1)) (eventually_atTop.mpr ⟨k, fun N hN => ?_⟩)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [kink_phaseApprox ha, le_div_iff₀ (pow_pos ha _), div_pow, pow_add]
    have := hlow m
    calc b ^ k / a ^ k * (a ^ k * a ^ m) = a ^ m * b ^ k := by field_simp
      _ ≤ _ := this

/-- **Without smoothness the phase need not be Lipschitz**, even for an isometric centre part and
under bunching: in the kink example (`kink_asymptoticPhase`; `f(x, y) = ε min(|x|, |y|)` is
`ε`-Lipschitz, `0 < b`, `0 < ε`, `b + 3ε < a`) the phase is not Lipschitz on any neighbourhood
of `(0, 1)`. So the Hölder exponent of `norm_asymptoticPhase_sub_le_rpow` cannot be raised to `1`
for merely Lipschitz `f`, and the second-difference hypothesis of
`norm_asymptoticPhase_sub_le_mul` cannot be dropped. -/
@[tmio T, powerlib_foundation] theorem not_locallyLipschitz_kink_asymptoticPhase (hb : 0 < b)
    (hε : 0 < ε) (hgap : b + 3 * ε < a) :
    ¬ LocallyLipschitz (asymptoticPhase (a • ContinuousLinearMap.id ℝ ℝ)
      (b • ContinuousLinearMap.id ℝ ℝ) (kinkMap ε) 0 0) := by
  intro hL
  have hεpos : (0 : ℝ) < ε := hε
  have ha : 0 < a := by linarith
  have haε : 0 < a + ε := by linarith
  obtain ⟨h0, hk⟩ := kink_asymptoticPhase hb hε hgap
  obtain ⟨K, U, hU, hLip⟩ := hL ((0 : ℝ), (1 : ℝ))
  have hq0 : 0 ≤ b / (a + ε) := by positivity
  have hq1 : b / (a + ε) < 1 := by rw [div_lt_one haε]; linarith
  have hpk : Tendsto (fun k : ℕ => ((b / (a + ε)) ^ k, (1 : ℝ))) atTop (𝓝 ((0 : ℝ), (1 : ℝ))) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).prodMk_nhds tendsto_const_nhds
  have hgrow : Tendsto (fun k : ℕ => ((a + ε) / a) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by rw [one_lt_div ha]; linarith)
  obtain ⟨k, hkU, hkK⟩ := ((hpk.eventually (Filter.mem_map.mp hU)).and
    (hgrow.eventually (eventually_gt_atTop (K : ℝ)))).exists
  have h1 := hLip.dist_le_mul _ hkU _ (mem_of_mem_nhds hU)
  rw [h0, Real.dist_eq, sub_zero, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_self,
    abs_zero, abs_of_nonneg (pow_nonneg hq0 k), max_eq_left (pow_nonneg hq0 k)] at h1
  have h2 := (hk k).trans (le_abs_self _)
  have h3 : (b / a) ^ k = ((a + ε) / a) ^ k * (b / (a + ε)) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : 0 < (b / (a + ε)) ^ k := pow_pos (by positivity) k
  have : ((a + ε) / a) ^ k * (b / (a + ε)) ^ k ≤ K * (b / (a + ε)) ^ k := by
    rw [← h3]; exact h2.trans h1
  have := le_of_mul_le_mul_right this h4
  linarith

end Kink

end powerlib.Map.CenterManifold
