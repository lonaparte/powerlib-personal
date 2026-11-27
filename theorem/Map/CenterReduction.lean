import theorem.Map.CenterManifold
import theorem.Map.Defs

/-! # The reduction principle and the approximation theorem for centre manifolds of maps

For a map in centre–stable form with its invariant Lipschitz graph `y = h(x)`
(`theorem/Map/CenterManifold.lean`), the stability of the fixed point `0` is that of the reduced
map `r(x) = A x + f(x, h(x))` on the centre space, and `h` can be computed to any order from a
candidate graph whose invariance defect is small.

* **Reduction principle.** A map `G` on `ℝⁿ` that agrees near `0`, through a linear embedding
  `Φ : ℝⁿ → ℝᶜ × Y` with a left inverse `Ψ`, with the cut-off map `F` of the centre manifold
  theorem is locally asymptotically stable exactly when the reduced map is; if the reduced map is
  unstable so is `G`, and if `G` is Lyapunov stable so is the reduced map. The direction
  "`r` asymptotically stable ⇒ `G` asymptotically stable" uses that `r` is *totally* stable:
  along an orbit of `F` the centre coordinate is a pseudo-orbit of `r` whose defects decay like
  `ε (b + 2ε)ᵏ` (exponential attraction to the graph), and a locally asymptotically stable,
  Lipschitz map on `ℝᶜ` keeps pseudo-orbits with small defects small and drives them to `0` when
  the defects vanish (compactness of closed balls gives uniform attraction).
* **Approximation.** If a candidate `φ` (`φ(0) = 0`) has invariance defect
  `φ(A x + f(x, φ x)) − B φ(x) − g(x, φ x) = O(‖x‖^q)`, then `h(x) − φ(x) = O(‖x‖^q)`, under the
  spectral-gap condition `b + ε(1 + Lip φ) < (a − ε)^q`: one step along the graph gives
  `‖(h − φ)(r x)‖ ≤ κ ‖(h − φ)(x)‖ + C ‖x‖^q`, and `r⁻¹` shrinks norms at most by `a − ε`.
  This computes the reduced map to the order required by the scalar normal forms of
  `theorem/Periodic/CriticalMultiplier.lean` (`Map.flip_localAsymptoticStable`,
  `Map.flip_unstable`, `Map.cubic_localAsymptoticStable`, `Map.cubic_unstable`,
  `Map.quadratic_unstable`).

Scope.
* The map semantics of `theorem/Map/Defs.lean` on `ℝⁿ = EuclideanSpace ℝ (Fin n)` and
  `ℝᶜ = EuclideanSpace ℝ (Fin c)` (`Map.LyapunovStable`, `Map.LocalAsymptoticStable`,
  `Map.Unstable`); the stable space `Y` is any real normed space, so an adapted norm in which the
  stable part contracts in one step is a choice of `Y` and `Φ` (for instance the weighted-orbit
  embedding of `theorem/Periodic/FlipReduction.lean`). `Φ` need not be onto: the graph lies in
  its range in the directions that need it (`Φ (Ψ (x, h x)) = (x, h x)`).
* The agreement `Φ (G e) = F (Φ e)` holds on a ball `‖e‖ < ρ`; `F` is the map with the cut-off
  nonlinearities (`ε`-Lipschitz, vanishing at `0`), so every conclusion concerns the original `G`.
  The reduced map is the one of the cut-off, equal to `x ↦ A x + f₀(x, h x)` near `0`.
* Not proved: "`r` Lyapunov stable (not asymptotically) ⇒ `G` Lyapunov stable", which needs the
  asymptotic phase (a second contraction for the stable fibres); the transfers proved here are
  those that decide the normal forms (asymptotic stability both ways, instability from `r` to `G`).
* Generic; nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2 (Theorem 2, the reduction
principle; Theorem 3, the approximation theorem; their versions for maps); Pliss, "A reduction
principle in the theory of stability of motion" (1964); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed.), §5.1 (the reduction principle for maps); total stability of an
asymptotically stable fixed point: Hahn, *Stability of Motion* (1967).

Results.
* Pseudo-orbits of a locally asymptotically stable map on `ℝᶜ`:
  `Map.LocalAsymptoticStable.exists_uniform` (uniform attraction on a closed ball),
  `Map.norm_pseudoOrbit_sub_iterate_le` (finite-step shadowing: `σ j (1 + L)^j`),
  `Map.LocalAsymptoticStable.pseudoOrbit_stable` (total stability: small defects keep
  pseudo-orbits small), `Map.LocalAsymptoticStable.pseudoOrbit_tendsto` (vanishing defects drive
  them to `0`).
* Orbits: `splitMap_iterate_graph` (on the graph `Fᵏ(x, h x) = (rᵏ x, h(rᵏ x))`),
  `lipschitzWith_reducedMap`, `norm_iterate_succ_sub_reducedMap_le` (the centre coordinate is a
  pseudo-orbit of `r` with defect `ε (b + 2ε)ᵏ ‖y₀ − h x₀‖`), `iterate_conj_of_norm_lt`,
  `iterate_conj_of_norm_lt'` (orbits of `G` that stay in the ball are read through `Φ` as orbits
  of `F`).
* **Reduction principle**: `lyapunovStable_reduced` (`G` Lyapunov stable ⇒ `r` Lyapunov stable),
  `unstable_of_reduced` (`r` unstable ⇒ `G` unstable), `localAsymptoticStable_of_reduced`
  (`r` locally asymptotically stable ⇒ `G` locally asymptotically stable),
  `localAsymptoticStable_reduced` (the converse), `localAsymptoticStable_iff`.
* **Approximation**: `norm_sub_le_of_defect` (global form: `‖h x − φ x‖ ≤ C ‖x‖^q / ((a − ε)^q −
  κ)`), `isBigO_sub_of_defect` (local form, for a candidate with strict derivative `0` at `0`
  and a defect `O(‖x‖^q)` near `0`, `q ≥ 1`), `isBigO_centreGraph` (tangency: `h = O(‖x‖^q)` when
  `g(x, 0) = O(‖x‖^q)`).

Corrections.
None: an extension (the reduction principle and the approximation theorem for maps).

Family and connection conclusions.
None: static evidence on maps (stability in the map semantics).
-/

noncomputable section

open Filter Topology Asymptotics

namespace powerlib.Map

variable {c : ℕ}

local notation "ℝᶜ" => EuclideanSpace ℝ (Fin c)

/-! ## Pseudo-orbits of an asymptotically stable map -/

/-- **Uniform attraction.** A continuous map with `0` locally asymptotically stable attracts a
closed ball uniformly: after some time `N` every orbit from the ball stays within `η`. -/
@[tmio T, powerlib_foundation] theorem LocalAsymptoticStable.exists_uniform {r : ℝᶜ → ℝᶜ}
    (hr : Continuous r) (h : LocalAsymptoticStable r 0) :
    ∃ β > 0, ∀ η > 0, ∃ N : ℕ, ∀ y : ℝᶜ, ‖y‖ ≤ β → ∀ k, N ≤ k → ‖r^[k] y‖ < η := by
  obtain ⟨hLS, c₀, hc₀, hatt⟩ := h
  refine ⟨c₀ / 2, half_pos hc₀, fun η hη => ?_⟩
  obtain ⟨δ, hδ, hδb⟩ := hLS η hη
  have hN : ∀ y : ℝᶜ, ∃ N : ℕ, ‖y‖ ≤ c₀ / 2 → ‖r^[N] y‖ < δ := by
    intro y
    by_cases hy : ‖y‖ ≤ c₀ / 2
    · have hlim := hatt y (by rw [sub_zero]; linarith)
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) δ hδ
      exact ⟨N, fun _ => by have := hN N le_rfl; rwa [dist_zero_right] at this⟩
    · exact ⟨0, fun h' => absurd h' hy⟩
  choose N hN using hN
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℝᶜ) (c₀ / 2)).elim_finite_subcover
    (fun y => {z : ℝᶜ | ‖r^[N y] z‖ < δ})
    (fun y => isOpen_lt (hr.iterate _).norm continuous_const)
    (fun y hy => Set.mem_iUnion.mpr ⟨y, hN y (by simpa using hy)⟩)
  refine ⟨t.sup N, fun y hy k hk => ?_⟩
  obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (ht (by simpa using hy))
  have hle : N i ≤ k := (Finset.le_sup hi).trans hk
  have := hδb (r^[N i] y) (by rw [sub_zero]; exact hiy) (k - N i)
  rwa [sub_zero, ← Function.iterate_add_apply, Nat.sub_add_cancel hle] at this

/-- **Finite-step shadowing.** A pseudo-orbit of an `L`-Lipschitz map with defects at most `σ`
stays within `σ j (1 + L)^j` of the true orbit for `j` steps. -/
@[tmio T, powerlib_foundation] theorem norm_pseudoOrbit_sub_iterate_le {r : ℝᶜ → ℝᶜ} {L : NNReal}
    (hr : LipschitzWith L r) {x : ℕ → ℝᶜ} {m : ℕ} {σ : ℝ} (j : ℕ)
    (hx : ∀ i < j, ‖x (m + i + 1) - r (x (m + i))‖ ≤ σ) :
    ‖x (m + j) - r^[j] (x m)‖ ≤ σ * j * (1 + L) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hσ : 0 ≤ σ := (norm_nonneg _).trans (hx 0 (Nat.succ_pos j))
    have ih' := ih fun i hi => hx i (hi.trans (Nat.lt_succ_self j))
    have hL : (0 : ℝ) ≤ L := L.coe_nonneg
    have hpow : 1 ≤ (1 + (L : ℝ)) ^ (j + 1) := one_le_pow₀ (by linarith)
    rw [Function.iterate_succ_apply', ← add_assoc]
    have e : x (m + j + 1) - r (r^[j] (x m)) =
        (x (m + j + 1) - r (x (m + j))) + (r (x (m + j)) - r (r^[j] (x m))) := by abel
    rw [e]
    have h1 := hx j (Nat.lt_succ_self j)
    have h2 : ‖r (x (m + j)) - r (r^[j] (x m))‖ ≤ L * ‖x (m + j) - r^[j] (x m)‖ :=
      hr.norm_sub_le _ _
    have h3 : (L : ℝ) * (σ * j * (1 + L) ^ j) ≤ σ * j * (1 + L) ^ (j + 1) := by
      rw [pow_succ]
      have : 0 ≤ σ * j * (1 + L) ^ j := by positivity
      nlinarith
    calc ‖(x (m + j + 1) - r (x (m + j))) + (r (x (m + j)) - r (r^[j] (x m)))‖
        ≤ σ + L * ‖x (m + j) - r^[j] (x m)‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ σ + L * (σ * j * (1 + L) ^ j) := by gcongr
      _ ≤ σ * (1 + L) ^ (j + 1) + σ * j * (1 + L) ^ (j + 1) := by nlinarith
      _ = σ * ↑(j + 1) * (1 + L) ^ (j + 1) := by push_cast; ring

/-- **Total stability.** A Lipschitz map with `0` locally asymptotically stable keeps
pseudo-orbits small: for every `ε > 0` there is `δ > 0` such that a sequence starting within `δ`
whose one-step defects `‖x_{k+1} − r(x_k)‖` stay below `δ` stays within `ε`. The proof runs in
blocks of `N` steps: from the ball of radius `β₀` the orbit returns into `β₀/2` after `N` steps
(uniform attraction), and the defects add at most `β₀/2` over a block. -/
@[tmio T, powerlib_foundation] theorem LocalAsymptoticStable.pseudoOrbit_stable {r : ℝᶜ → ℝᶜ}
    {L : NNReal} (hr : LipschitzWith L r) (h : LocalAsymptoticStable r 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℕ → ℝᶜ, ‖x 0‖ < δ → (∀ k, ‖x (k + 1) - r (x k)‖ < δ) →
      ∀ k, ‖x k‖ < ε := by
  intro ε hε
  obtain ⟨β, hβ, hU⟩ := h.exists_uniform hr.continuous
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := h.1 (ε / 2) (half_pos hε)
  set β₀ := min β (δ₁ / 2) with hβ₀def
  have hβ₀ : 0 < β₀ := lt_min hβ (half_pos hδ₁)
  obtain ⟨N₀, hN₀⟩ := hU (β₀ / 2) (half_pos hβ₀)
  set N := N₀ + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos N₀
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  set M : ℝ := (N : ℝ) * (1 + L) ^ N with hM
  have hM0 : 0 ≤ M := by positivity
  set γ := min (ε / 2) (β₀ / 2) with hγ
  have hγ0 : 0 < γ := lt_min (half_pos hε) (half_pos hβ₀)
  set σ := γ / (M + 1) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσM : σ * M < γ := by
    rw [hσ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  -- one block of `N` steps
  have block : ∀ x : ℕ → ℝᶜ, ∀ m, ‖x m‖ < β₀ →
      (∀ i < N, ‖x (m + i + 1) - r (x (m + i))‖ ≤ σ) →
      (∀ j ≤ N, ‖x (m + j)‖ < ε) ∧ ‖x (m + N)‖ < β₀ := by
    intro x m hxm hdef
    have herr : ∀ j ≤ N, ‖x (m + j) - r^[j] (x m)‖ ≤ σ * M := by
      intro j hj
      have := norm_pseudoOrbit_sub_iterate_le hr j fun i hi => hdef i (hi.trans_le hj)
      refine this.trans ?_
      have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
      have hp : (1 + (L : ℝ)) ^ j ≤ (1 + L) ^ N := pow_le_pow_right₀ (by linarith) hj
      have : (j : ℝ) * (1 + L) ^ j ≤ M := by
        rw [hM]; exact mul_le_mul hj' hp (by positivity) (by positivity)
      calc σ * j * (1 + L) ^ j = σ * ((j : ℝ) * (1 + L) ^ j) := by ring
        _ ≤ σ * M := mul_le_mul_of_nonneg_left this hσ0.le
    have hxm' : ‖x m - 0‖ < δ₁ := by
      rw [sub_zero]; exact hxm.trans_le ((min_le_right _ _).trans (half_le_self hδ₁.le))
    refine ⟨fun j hj => ?_, ?_⟩
    · have h1 := hδ₁b (x m) hxm' j
      rw [sub_zero] at h1
      have h2 := herr j hj
      have h3 := norm_le_insert' (x (m + j)) (r^[j] (x m))
      have : γ ≤ ε / 2 := min_le_left _ _
      linarith [norm_sub_norm_le (x (m + j)) (r^[j] (x m))]
    · have h1 := hN₀ (x m) (hxm.le.trans (min_le_left _ _)) N (Nat.le_succ N₀)
      have h2 := herr N le_rfl
      have : γ ≤ β₀ / 2 := min_le_right _ _
      linarith [norm_sub_norm_le (x (m + N)) (r^[N] (x m))]
  refine ⟨min β₀ σ, lt_min hβ₀ hσ0, fun x hx0 hxs k => ?_⟩
  have hdefs : ∀ m, ∀ i < N, ‖x (m + i + 1) - r (x (m + i))‖ ≤ σ := fun m i _ =>
    (hxs (m + i)).le.trans (min_le_right _ _)
  have hq : ∀ q, ‖x (N * q)‖ < β₀ := by
    intro q
    induction q with
    | zero => simpa using hx0.trans_le (min_le_left _ _)
    | succ q ih =>
      have := (block x (N * q) ih (hdefs _)).2
      rwa [show N * q + N = N * (q + 1) by ring] at this
  have := (block x (N * (k / N)) (hq _) (hdefs _)).1 (k % N) (Nat.mod_lt _ hN).le
  rwa [Nat.div_add_mod] at this

/-- **Vanishing defects.** For a Lipschitz map with `0` locally asymptotically stable there is
`c > 0` such that every sequence starting within `c`, with one-step defects below `c` that tend
to `0`, tends to `0`. -/
@[tmio T, powerlib_foundation] theorem LocalAsymptoticStable.pseudoOrbit_tendsto {r : ℝᶜ → ℝᶜ}
    {L : NNReal} (hr : LipschitzWith L r) (h : LocalAsymptoticStable r 0) :
    ∃ c > 0, ∀ x : ℕ → ℝᶜ, ‖x 0‖ < c → (∀ k, ‖x (k + 1) - r (x k)‖ < c) →
      Tendsto (fun k => x (k + 1) - r (x k)) atTop (𝓝 0) → Tendsto x atTop (𝓝 0) := by
  obtain ⟨β, hβ, hU⟩ := h.exists_uniform hr.continuous
  obtain ⟨c₁, hc₁, hc₁b⟩ := h.pseudoOrbit_stable hr β hβ
  refine ⟨c₁, hc₁, fun x hx0 hxs hlim => ?_⟩
  have hin : ∀ k, ‖x k‖ < β := hc₁b x hx0 hxs
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δη, hδη, hδηb⟩ := h.pseudoOrbit_stable hr η hη
  obtain ⟨N, hN⟩ := hU (δη / 2) (half_pos hδη)
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  set M : ℝ := (N : ℝ) * (1 + L) ^ N with hM
  have hM0 : 0 ≤ M := by positivity
  set σ := (δη / 2) / (M + 1) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσM : σ * M < δη / 2 := by
    rw [hσ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.mp hlim) (min σ δη) (lt_min hσ0 hδη)
  have hdef : ∀ k, m₀ ≤ k → ‖x (k + 1) - r (x k)‖ < min σ δη := fun k hk => by
    have := hm₀ k hk; rwa [dist_zero_right] at this
  have hxN : ‖x (m₀ + N)‖ < δη := by
    have h1 := hN (x m₀) (hin m₀).le N le_rfl
    have h2 := norm_pseudoOrbit_sub_iterate_le hr (m := m₀) (σ := σ) N fun i _ =>
      (hdef (m₀ + i) (Nat.le_add_right _ _)).le.trans (min_le_left _ _)
    have h3 : σ * N * (1 + L) ^ N = σ * M := by rw [hM]; ring
    linarith [norm_sub_norm_le (x (m₀ + N)) (r^[N] (x m₀))]
  have htail := hδηb (fun k => x (m₀ + N + k)) (by simpa using hxN) fun k => by
    have := hdef (m₀ + N + k) (by omega)
    exact this.trans_le (min_le_right _ _)
  refine ⟨m₀ + N, fun k hk => ?_⟩
  have := htail (k - (m₀ + N))
  rw [Nat.add_sub_cancel' hk] at this
  rwa [dist_zero_right]

end powerlib.Map

namespace powerlib.Map.CenterManifold

/-! ## Orbits of the split map and of the conjugated map -/

section Orbits

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {f : X × Y → X} {g : X × Y → Y}
  {b : ℝ} {ε : NNReal}

/-- On an invariant graph the orbit of a graph point is the graph of the reduced orbit:
`Fᵏ(x, h x) = (rᵏ x, h(rᵏ x))`. -/
@[tmio T, powerlib_foundation] theorem splitMap_iterate_graph {h : X → Y}
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (x : X) (k : ℕ) :
    (splitMap A B f g)^[k] (x, h x) = ((reducedMap A f h)^[k] x, h ((reducedMap A f h)^[k] x)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, splitMap_graph hinv]

omit [NormedSpace ℝ Y] in
/-- The reduced map along a `1`-Lipschitz graph is `(‖A‖ + ε)`-Lipschitz. -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_reducedMap (hf : LipschitzWith ε f)
    {h : X → Y} (hh : LipschitzWith 1 h) :
    LipschitzWith (‖A‖₊ + ε) (reducedMap A f h) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, coe_nnnorm]
  have h1 := reducedMap_sub_le (A := A) hf hh x x'
  have h2 := A.le_opNorm (x - x')
  calc ‖reducedMap A f h x - reducedMap A f h x'‖
      = ‖(reducedMap A f h x - reducedMap A f h x' - A (x - x')) + A (x - x')‖ := by
        rw [sub_add_cancel]
    _ ≤ ε * ‖x - x'‖ + ‖A‖ * ‖x - x'‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = (‖A‖ + ε) * ‖x - x'‖ := by ring

/-- **The centre coordinate is a pseudo-orbit of the reduced map**, with defect
`‖x_{k+1} − r(x_k)‖ ≤ ε (b + 2ε)ᵏ ‖y₀ − h(x₀)‖`. -/
@[tmio T, powerlib_foundation] theorem norm_iterate_succ_sub_reducedMap_le
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g)
    {h : X → Y} (hh : LipschitzWith 1 h)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (p : X × Y) (k : ℕ) :
    ‖((splitMap A B f g)^[k + 1] p).1 - reducedMap A f h ((splitMap A B f g)^[k] p).1‖ ≤
      ε * ((b + 2 * ε) ^ k * ‖p.2 - h p.1‖) := by
  rw [Function.iterate_succ_apply']
  set q := (splitMap A B f g)^[k] p
  have e : (splitMap A B f g q).1 - reducedMap A f h q.1 = f q - f (q.1, h q.1) := by
    simp only [splitMap, reducedMap]; abel
  rw [e]
  have hpp : ‖q - (q.1, h q.1)‖ = ‖q.2 - h q.1‖ := by
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
    exact max_eq_right (norm_nonneg _)
  calc ‖f q - f (q.1, h q.1)‖ ≤ ε * ‖q - (q.1, h q.1)‖ := hf.norm_sub_le _ _
    _ = ε * ‖q.2 - h q.1‖ := by rw [hpp]
    _ ≤ ε * ((b + 2 * ε) ^ k * ‖p.2 - h p.1‖) :=
        mul_le_mul_of_nonneg_left (norm_iterate_sub_graph_le hB hb hf hg hh hinv p k)
          ε.coe_nonneg

end Orbits

section Conj

variable {E Z : Type*} [Norm E] {G : E → E} {F : Z → Z} {Φ : E → Z} {Ψ : Z → E}

/-- **Reading orbits through the embedding** (condition on the `F`-orbit). If `Φ (G e) = F (Φ e)`
on the ball `‖e‖ < ρ`, `Ψ` is a left inverse of `Φ`, and the `F`-orbit of `Φ e` is read by `Ψ`
inside the ball for `j < k`, then `Φ (Gᵏ e) = Fᵏ (Φ e)`. -/
@[tmio T, powerlib_foundation] theorem iterate_conj_of_norm_lt (hΨΦ : ∀ e, Ψ (Φ e) = e)
    {ρ : ℝ} (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = F (Φ e)) {e : E} {k : ℕ}
    (hsmall : ∀ j < k, ‖Ψ (F^[j] (Φ e))‖ < ρ) : Φ (G^[k] e) = F^[k] (Φ e) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun j hj => hsmall j (hj.trans (Nat.lt_succ_self k))
    have hk : ‖G^[k] e‖ < ρ := by
      rw [← hΨΦ (G^[k] e), ih']; exact hsmall k (Nat.lt_succ_self k)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hG _ hk, ih']

/-- **Reading orbits through the embedding** (condition on the `G`-orbit): if the `G`-orbit of `e`
stays in the ball for `j < k`, then `Φ (Gᵏ e) = Fᵏ (Φ e)`. -/
@[tmio T, powerlib_foundation] theorem iterate_conj_of_norm_lt' {ρ : ℝ}
    (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = F (Φ e)) {e : E} {k : ℕ}
    (hsmall : ∀ j < k, ‖G^[j] e‖ < ρ) : Φ (G^[k] e) = F^[k] (Φ e) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih fun j hj => hsmall j (hj.trans (Nat.lt_succ_self k))
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hG _ (hsmall k
      (Nat.lt_succ_self k)), ih']

end Conj

/-! ## The reduction principle -/

section Reduction

variable {c n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "ℝᶜ" => EuclideanSpace ℝ (Fin c)
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

variable {A : EuclideanSpace ℝ (Fin c) →L[ℝ] EuclideanSpace ℝ (Fin c)} {B : Y →L[ℝ] Y}
  {f : EuclideanSpace ℝ (Fin c) × Y → EuclideanSpace ℝ (Fin c)}
  {g : EuclideanSpace ℝ (Fin c) × Y → Y} {b : ℝ} {ε : NNReal} {h : EuclideanSpace ℝ (Fin c) → Y}
  {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin c) × Y}
  {Ψ : EuclideanSpace ℝ (Fin c) × Y →L[ℝ] EuclideanSpace ℝ (Fin n)} {ρ : ℝ}

/-- **Lyapunov stability passes to the reduced map.** If `G` is Lyapunov stable at `0`, so is
the reduced map on an invariant graph lying in the range of `Φ`: the `G`-orbit of `Ψ(x, h x)` is
read through `Φ` as the graph of the reduced orbit. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_reduced (hh : LipschitzWith 1 h)
    (hh0 : h 0 = 0) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x)) (hρ : 0 < ρ)
    (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e)) (hLS : LyapunovStable G 0) :
    LyapunovStable (reducedMap A f h) 0 := by
  intro ε' hε'
  set η := min ρ (ε' / (‖Φ‖ + 1)) with hη
  have hη0 : 0 < η := lt_min hρ (by positivity)
  obtain ⟨δ, hδ, hδb⟩ := hLS η hη0
  refine ⟨δ / (‖Ψ‖ + 1), by positivity, fun x hx k => ?_⟩
  rw [sub_zero] at hx ⊢
  set e := Ψ (x, h x)
  have he : ‖e - 0‖ < δ := by
    rw [sub_zero]
    calc ‖e‖ ≤ ‖Ψ‖ * ‖(x, h x)‖ := Ψ.le_opNorm _
      _ = ‖Ψ‖ * ‖x‖ := by rw [norm_graph hh hh0]
      _ ≤ (‖Ψ‖ + 1) * ‖x‖ := by gcongr; linarith
      _ < (‖Ψ‖ + 1) * (δ / (‖Ψ‖ + 1)) := by gcongr
      _ = δ := by field_simp
  have horb : ∀ j, ‖G^[j] e‖ < η := fun j => by simpa using hδb e he j
  have hconj := iterate_conj_of_norm_lt' hG (e := e) (k := k) fun j _ =>
    (horb j).trans_le (min_le_left _ _)
  have hΦe : Φ e = (x, h x) := hgraph x
  rw [hΦe, splitMap_iterate_graph hinv] at hconj
  calc ‖(reducedMap A f h)^[k] x‖ ≤ ‖((reducedMap A f h)^[k] x, h ((reducedMap A f h)^[k] x))‖ :=
        by rw [Prod.norm_mk]; exact le_max_left _ _
    _ = ‖Φ (G^[k] e)‖ := by rw [hconj]
    _ ≤ ‖Φ‖ * ‖G^[k] e‖ := Φ.le_opNorm _
    _ ≤ ‖Φ‖ * η := by gcongr; exact (horb k).le
    _ ≤ ‖Φ‖ * (ε' / (‖Φ‖ + 1)) := by gcongr; exact min_le_right _ _
    _ < ε' := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg Φ]

/-- **Reduction principle, instability.** If the reduced map is unstable at `0`, so is `G`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_reduced (hh : LipschitzWith 1 h)
    (hh0 : h 0 = 0) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x)) (hρ : 0 < ρ)
    (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e))
    (hU : Unstable (reducedMap A f h) 0) : Unstable G 0 := fun hLS =>
  hU (lyapunovStable_reduced hh hh0 hinv hgraph hρ hG hLS)

/-- Along an `F`-orbit from a small `p`: the centre coordinate stays below `η` and the orbit
point below `2η` (total stability of `r` and attraction to the graph). -/
@[tmio T, powerlib_foundation] private theorem orbit_small (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hθ : b + 2 * ε < 1)
    (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (hr : LocalAsymptoticStable (reducedMap A f h) 0) :
    ∀ η > 0, ∃ δ > 0, ∀ p : ℝᶜ × Y, ‖p‖ < δ → ∀ k,
      ‖((splitMap A B f g)^[k] p).1‖ < η ∧ ‖(splitMap A B f g)^[k] p‖ < 2 * η := by
  intro η hη
  have hε := ε.coe_nonneg
  obtain ⟨δT, hδT, hδTb⟩ :=
    hr.pseudoOrbit_stable (lipschitzWith_reducedMap (A := A) hf hh) η hη
  set δ := min δT η / (2 * ((ε : ℝ) + 1)) with hδ
  have hmin : 0 < min δT η := lt_min hδT hη
  have hδ0 : 0 < δ := by positivity
  have hδT' : 2 * ((ε : ℝ) + 1) * δ ≤ δT := by
    rw [hδ, mul_div_cancel₀ _ (by positivity)]; exact min_le_left _ _
  have hδη : 2 * ((ε : ℝ) + 1) * δ ≤ η := by
    rw [hδ, mul_div_cancel₀ _ (by positivity)]; exact min_le_right _ _
  refine ⟨δ, hδ0, fun p hp => ?_⟩
  set F := splitMap A B f g with hF
  have hp1 : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hp2 : ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  have hhx : ∀ x, ‖h x‖ ≤ ‖x‖ := fun x => by simpa [hh0] using hh.norm_sub_le x 0
  have hz0 : ‖p.2 - h p.1‖ ≤ 2 * ‖p‖ := by
    calc ‖p.2 - h p.1‖ ≤ ‖p.2‖ + ‖h p.1‖ := norm_sub_le _ _
      _ ≤ ‖p.2‖ + ‖p.1‖ := by gcongr; exact hhx _
      _ ≤ 2 * ‖p‖ := by linarith
  have hθ0 : 0 ≤ b + 2 * ε := by linarith
  have hθk : ∀ k : ℕ, (b + 2 * ε) ^ k ≤ 1 := fun k => pow_le_one₀ hθ0 hθ.le
  have hzθ : ∀ k : ℕ, (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ ≤ 2 * ‖p‖ := fun k => by
    have := mul_le_mul_of_nonneg_right (hθk k) (norm_nonneg (p.2 - h p.1))
    linarith
  have hzk : ∀ k, ‖(F^[k] p).2 - h (F^[k] p).1‖ ≤ 2 * ‖p‖ := fun k =>
    (norm_iterate_sub_graph_le hB hb hf hg hh hinv p k).trans (hzθ k)
  have hx : ∀ k, ‖(F^[k] p).1‖ < η := by
    refine hδTb (fun k => (F^[k] p).1) ?_ fun k => ?_
    · show ‖p.1‖ < δT
      have : δ ≤ 2 * ((ε : ℝ) + 1) * δ := le_mul_of_one_le_left hδ0.le (by linarith)
      linarith
    · have h1 := norm_iterate_succ_sub_reducedMap_le hB hb hf hg hh hinv p k
      have h2 : (ε : ℝ) * ((b + 2 * ε) ^ k * ‖p.2 - h p.1‖) ≤ ε * (2 * ‖p‖) :=
        mul_le_mul_of_nonneg_left (hzθ k) hε
      have h3 : (ε : ℝ) * (2 * ‖p‖) < 2 * ((ε : ℝ) + 1) * δ := by nlinarith
      exact h1.trans_lt (by linarith)
  intro k
  refine ⟨hx k, ?_⟩
  rw [Prod.norm_def]
  refine max_lt ((hx k).trans (by linarith)) ?_
  have e : (F^[k] p).2 = ((F^[k] p).2 - h (F^[k] p).1) + h (F^[k] p).1 := by abel
  rw [e]
  have h1 : 2 * ‖p‖ < η := by
    have : 2 * ‖p‖ < 2 * δ := by linarith
    have : 2 * δ ≤ 2 * ((ε : ℝ) + 1) * δ := by nlinarith
    linarith
  calc ‖((F^[k] p).2 - h (F^[k] p).1) + h (F^[k] p).1‖
      ≤ ‖(F^[k] p).2 - h (F^[k] p).1‖ + ‖h (F^[k] p).1‖ := norm_add_le _ _
    _ ≤ 2 * ‖p‖ + ‖(F^[k] p).1‖ := add_le_add (hzk k) (hhx _)
    _ < η + η := add_lt_add h1 (hx k)
    _ = 2 * η := by ring

/-- **Reduction principle, asymptotic stability.** If the reduced map is locally asymptotically
stable at `0`, so is `G` (`b + 2ε < 1`): along an `F`-orbit the centre coordinate is a pseudo-orbit
of `r` with defects `ε (b + 2ε)ᵏ ‖y₀ − h x₀‖`, kept small and driven to `0` by the total stability
of `r`, and the stable coordinate follows the graph. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_reduced
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g)
    (hθ : b + 2 * ε < 1) (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (hΨΦ : ∀ e, Ψ (Φ e) = e)
    (hρ : 0 < ρ) (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e))
    (hr : LocalAsymptoticStable (reducedMap A f h) 0) : LocalAsymptoticStable G 0 := by
  have hε := ε.coe_nonneg
  set F := splitMap A B f g with hF
  have hctrl : ∀ ε' > 0, ∃ δ > 0, ∀ e : ℝⁿ, ‖e‖ < δ → ∀ k,
      G^[k] e = Ψ (F^[k] (Φ e)) ∧ ‖G^[k] e‖ < ε' := by
    intro ε' hε'
    have hm : 0 < min ε' ρ := lt_min hε' hρ
    set η := min ε' ρ / (2 * (‖Ψ‖ + 1)) with hη
    obtain ⟨δ, hδ, hδb⟩ := orbit_small hB hb hf hg hθ hh hh0 hinv hr η (by positivity)
    refine ⟨δ / (‖Φ‖ + 1), by positivity, fun e he k => ?_⟩
    have hpe : ‖Φ e‖ < δ := by
      calc ‖Φ e‖ ≤ ‖Φ‖ * ‖e‖ := Φ.le_opNorm e
        _ ≤ (‖Φ‖ + 1) * ‖e‖ := by gcongr; linarith
        _ < (‖Φ‖ + 1) * (δ / (‖Φ‖ + 1)) := by gcongr
        _ = δ := by field_simp
    have hsmall : ∀ j, ‖Ψ (F^[j] (Φ e))‖ < min ε' ρ := fun j => by
      have h1 := (hδb (Φ e) hpe j).2
      calc ‖Ψ (F^[j] (Φ e))‖ ≤ ‖Ψ‖ * ‖F^[j] (Φ e)‖ := Ψ.le_opNorm _
        _ ≤ (‖Ψ‖ + 1) * ‖F^[j] (Φ e)‖ := by gcongr; linarith
        _ < (‖Ψ‖ + 1) * (2 * η) := by gcongr
        _ = min ε' ρ := by rw [hη]; field_simp
    have hconj : Φ (G^[k] e) = F^[k] (Φ e) :=
      iterate_conj_of_norm_lt hΨΦ hG fun j _ => (hsmall j).trans_le (min_le_right _ _)
    have hGk : G^[k] e = Ψ (F^[k] (Φ e)) := by rw [← hconj, hΨΦ]
    exact ⟨hGk, by rw [hGk]; exact (hsmall k).trans_le (min_le_left _ _)⟩
  refine ⟨fun ε' hε' => ?_, ?_⟩
  · obtain ⟨δ, hδ, hδb⟩ := hctrl ε' hε'
    exact ⟨δ, hδ, fun e he k => by rw [sub_zero] at he ⊢; exact (hδb e he k).2⟩
  obtain ⟨δρ, hδρ, hδρb⟩ := hctrl ρ hρ
  obtain ⟨cA, hcA, hcAb⟩ := hr.pseudoOrbit_tendsto (lipschitzWith_reducedMap (A := A) hf hh)
  set c' := min δρ (cA / (2 * ((ε : ℝ) + 1) * (‖Φ‖ + 1))) with hc'
  have hc'0 : 0 < c' := lt_min hδρ (by positivity)
  refine ⟨c', hc'0, fun e he => ?_⟩
  rw [sub_zero] at he
  set p := Φ e with hpdef
  have hp : ‖p‖ < cA / (2 * ((ε : ℝ) + 1)) := by
    calc ‖p‖ ≤ ‖Φ‖ * ‖e‖ := Φ.le_opNorm e
      _ ≤ (‖Φ‖ + 1) * ‖e‖ := by gcongr; linarith
      _ < (‖Φ‖ + 1) * (cA / (2 * ((ε : ℝ) + 1) * (‖Φ‖ + 1))) := by
          gcongr; exact he.trans_le (min_le_right _ _)
      _ = cA / (2 * ((ε : ℝ) + 1)) := by field_simp
  have hp' : 2 * ((ε : ℝ) + 1) * ‖p‖ < cA := by
    rwa [lt_div_iff₀ (by positivity), mul_comm] at hp
  have hhx : ∀ x, ‖h x‖ ≤ ‖x‖ := fun x => by simpa [hh0] using hh.norm_sub_le x 0
  have hp1 : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hp2 : ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  have hz0 : ‖p.2 - h p.1‖ ≤ 2 * ‖p‖ := by
    calc ‖p.2 - h p.1‖ ≤ ‖p.2‖ + ‖h p.1‖ := norm_sub_le _ _
      _ ≤ ‖p.2‖ + ‖p.1‖ := by gcongr; exact hhx _
      _ ≤ 2 * ‖p‖ := by linarith
  have hθ0 : 0 ≤ b + 2 * ε := by linarith
  have hθk : ∀ k : ℕ, (b + 2 * ε) ^ k ≤ 1 := fun k => pow_le_one₀ hθ0 hθ.le
  have hzθ : ∀ k : ℕ, (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ ≤ 2 * ‖p‖ := fun k => by
    have := mul_le_mul_of_nonneg_right (hθk k) (norm_nonneg (p.2 - h p.1))
    linarith
  set x : ℕ → ℝᶜ := fun k => (F^[k] p).1 with hxdef
  have hdef := norm_iterate_succ_sub_reducedMap_le hB hb hf hg hh hinv p
  have hθlim : Tendsto (fun k : ℕ => (b + 2 * ε) ^ k * ‖p.2 - h p.1‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).mul_const ‖p.2 - h p.1‖
  have hx0 : ‖x 0‖ < cA := by
    show ‖p.1‖ < cA
    have : ‖p‖ ≤ 2 * ((ε : ℝ) + 1) * ‖p‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith)
    linarith
  have hxs : ∀ k, ‖x (k + 1) - reducedMap A f h (x k)‖ < cA := fun k => by
    have h1 := hdef k
    have h2 : (ε : ℝ) * ((b + 2 * ε) ^ k * ‖p.2 - h p.1‖) ≤ ε * (2 * ‖p‖) :=
      mul_le_mul_of_nonneg_left (hzθ k) hε
    have h3 : (ε : ℝ) * (2 * ‖p‖) ≤ 2 * ((ε : ℝ) + 1) * ‖p‖ := by nlinarith [norm_nonneg p]
    exact h1.trans_lt (by linarith)
  have hlimdef : Tendsto (fun k => x (k + 1) - reducedMap A f h (x k)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => hdef k) ?_
    simpa using hθlim.const_mul (ε : ℝ)
  have hxlim : Tendsto x atTop (𝓝 0) := hcAb x hx0 hxs hlimdef
  have hzlim : Tendsto (fun k => (F^[k] p).2 - h (F^[k] p).1) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun k => norm_nonneg _)
      (fun k => norm_iterate_sub_graph_le hB hb hf hg hh hinv p k) hθlim
  have hhlim : Tendsto (fun k => h (x k)) atTop (𝓝 0) := by
    have := (hh.continuous.tendsto 0).comp hxlim
    rwa [hh0] at this
  have hylim : Tendsto (fun k => (F^[k] p).2) atTop (𝓝 0) := by
    have := hzlim.add hhlim
    rw [zero_add] at this
    refine this.congr fun k => ?_
    show (F^[k] p).2 - h (F^[k] p).1 + h (F^[k] p).1 = (F^[k] p).2
    exact sub_add_cancel _ _
  have hplim : Tendsto (fun k => F^[k] p) atTop (𝓝 0) := by
    have := hxlim.prodMk_nhds hylim
    rwa [Prod.mk_zero_zero] at this
  have hΨlim : Tendsto (fun k => Ψ (F^[k] p)) atTop (𝓝 0) := by
    have := (Ψ.continuous.tendsto 0).comp hplim
    rwa [map_zero] at this
  refine hΨlim.congr fun k => ?_
  exact ((hδρb e (he.trans_le (min_le_left _ _)) k).1).symm

/-- **Reduction principle, the converse.** If `G` is locally asymptotically stable at `0`, so is
the reduced map on an invariant graph lying in the range of `Φ`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_reduced (hh : LipschitzWith 1 h)
    (hh0 : h 0 = 0) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x)) (hρ : 0 < ρ)
    (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e)) (hLAS : LocalAsymptoticStable G 0) :
    LocalAsymptoticStable (reducedMap A f h) 0 := by
  refine ⟨lyapunovStable_reduced hh hh0 hinv hgraph hρ hG hLAS.1, ?_⟩
  obtain ⟨hLS, cG, hcG, hatt⟩ := hLAS
  obtain ⟨δρ, hδρ, hδρb⟩ := hLS ρ hρ
  refine ⟨min cG δρ / (‖Ψ‖ + 1), by have := lt_min hcG hδρ; positivity, fun x hx => ?_⟩
  rw [sub_zero] at hx
  set e := Ψ (x, h x) with he
  have hen : ‖e‖ < min cG δρ := by
    calc ‖e‖ ≤ ‖Ψ‖ * ‖(x, h x)‖ := Ψ.le_opNorm _
      _ = ‖Ψ‖ * ‖x‖ := by rw [norm_graph hh hh0]
      _ ≤ (‖Ψ‖ + 1) * ‖x‖ := by gcongr; linarith
      _ < (‖Ψ‖ + 1) * (min cG δρ / (‖Ψ‖ + 1)) := by gcongr
      _ = min cG δρ := by field_simp
  have horb : ∀ j, ‖G^[j] e‖ < ρ := fun j => by
    simpa using hδρb e (by rw [sub_zero]; exact hen.trans_le (min_le_right _ _)) j
  have hconj : ∀ k, (reducedMap A f h)^[k] x = (Φ (G^[k] e)).1 := fun k => by
    rw [iterate_conj_of_norm_lt' hG fun j _ => horb j, he, hgraph x,
      splitMap_iterate_graph hinv]
  have hlim := hatt e (by rw [sub_zero]; exact hen.trans_le (min_le_left _ _))
  have := ((continuous_fst.comp Φ.continuous).tendsto 0).comp hlim
  simp only [Function.comp_def, map_zero, Prod.fst_zero] at this
  exact this.congr fun k => (hconj k).symm

/-- **Reduction principle.** For an invariant graph lying in the range of `Φ` and `b + 2ε < 1`,
`G` is locally asymptotically stable at `0` exactly when the reduced map is. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_iff
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g)
    (hθ : b + 2 * ε < 1) (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (hΨΦ : ∀ e, Ψ (Φ e) = e)
    (hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x)) (hρ : 0 < ρ)
    (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e)) :
    LocalAsymptoticStable G 0 ↔ LocalAsymptoticStable (reducedMap A f h) 0 :=
  ⟨localAsymptoticStable_reduced hh hh0 hinv hgraph hρ hG,
    localAsymptoticStable_of_reduced hB hb hf hg hθ hh hh0 hinv hΨΦ hρ hG⟩

end Reduction

/-! ## The approximation theorem -/

section Approximation

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {f : X × Y → X}
  {g : X × Y → Y} {a b : ℝ} {ε : NNReal} {h : X → Y}

omit [CompleteSpace X] in
/-- One step along the graph: with `w = h − φ` and the defect `D` of `φ`,
`‖w(r x)‖ ≤ (b + ε(1 + Lip φ)) ‖w(x)‖ + ‖D(x)‖`. -/
@[tmio T, powerlib_foundation] private theorem norm_sub_reducedMap_le
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {φ : X → Y} {Lφ : NNReal}
    (hφ : LipschitzWith Lφ φ) (x : X) :
    ‖h (reducedMap A f h x) - φ (reducedMap A f h x)‖ ≤
      (b + ε * (1 + Lφ)) * ‖h x - φ x‖ +
        ‖φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)‖ := by
  have hε := ε.coe_nonneg
  have hL := Lφ.coe_nonneg
  have hpp : ‖(x, h x) - (x, φ x)‖ = ‖h x - φ x‖ := by
    rw [Prod.mk_sub_mk, sub_self, Prod.norm_mk, norm_zero]
    exact max_eq_right (norm_nonneg _)
  set D := φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x) with hD
  have e : h (reducedMap A f h x) - φ (reducedMap A f h x) =
      B (h x - φ x) + (g (x, h x) - g (x, φ x)) - D -
        (φ (A x + f (x, h x)) - φ (A x + f (x, φ x))) := by
    simp only [reducedMap, hinv, hD, map_sub]; abel
  rw [e]
  have h1 := hB (h x - φ x)
  have h2 : ‖g (x, h x) - g (x, φ x)‖ ≤ ε * ‖h x - φ x‖ := by
    rw [← hpp]; exact hg.norm_sub_le _ _
  have h3 : ‖φ (A x + f (x, h x)) - φ (A x + f (x, φ x))‖ ≤ Lφ * (ε * ‖h x - φ x‖) := by
    refine (hφ.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    rw [add_sub_add_left_eq_sub, ← hpp]; exact hf.norm_sub_le _ _
  have h4 := norm_sub_le (B (h x - φ x) + (g (x, h x) - g (x, φ x)) - D)
    (φ (A x + f (x, h x)) - φ (A x + f (x, φ x)))
  have h5 := norm_sub_le (B (h x - φ x) + (g (x, h x) - g (x, φ x))) D
  have h6 := norm_add_le (B (h x - φ x)) (g (x, h x) - g (x, φ x))
  nlinarith

/-- **The approximation theorem (global form).** Let `h` be the invariant `1`-Lipschitz graph and
`φ` an `Lφ`-Lipschitz candidate through `0` whose invariance defect is bounded by `C ‖x‖^q`
everywhere. If `κ = b + ε(1 + Lφ)` satisfies `κ < (a − ε)^q` and `κ < a − ε`, then
`‖h(x) − φ(x)‖ ≤ C ‖x‖^q / ((a − ε)^q − κ)`. Proof: by induction,
`‖(h − φ)(z)‖ ≤ C' ‖z‖^q + (κ/(a − ε))ᵏ (1 + Lφ) ‖z‖` for every `k`, from the one-step estimate at
the preimage of `z` under the reduced map, which is shorter by the factor `a − ε`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_le_of_defect (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hεa : (ε : ℝ) < a)
    (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {φ : X → Y} {Lφ : NNReal}
    (hφ : LipschitzWith Lφ φ) (hφ0 : φ 0 = 0) {C : ℝ} (hC : 0 ≤ C) {q : ℕ}
    (hD : ∀ x, ‖φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)‖ ≤ C * ‖x‖ ^ q)
    (hκq : b + ε * (1 + Lφ) < (a - ε) ^ q) (hκ1 : b + ε * (1 + Lφ) < a - ε) (x : X) :
    ‖h x - φ x‖ ≤ C / ((a - ε) ^ q - (b + ε * (1 + Lφ))) * ‖x‖ ^ q := by
  have hε := ε.coe_nonneg
  have hL := Lφ.coe_nonneg
  set s := a - (ε : ℝ) with hs
  set κ := b + ε * (1 + (Lφ : ℝ)) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hs0 : 0 < s := hκ0.trans_lt hκ1
  have hsq : 0 < s ^ q - κ := by linarith
  set C' := C / (s ^ q - κ) with hC'
  have hC'0 : 0 ≤ C' := div_nonneg hC hsq.le
  have hC'eq : κ * C' + C = s ^ q * C' := by rw [hC']; field_simp; ring
  have hratio : 0 ≤ κ / s := div_nonneg hκ0 hs0.le
  have hratio1 : κ / s < 1 := (div_lt_one hs0).mpr hκ1
  -- the reduced map shortens by at most `s`
  have hshort : ∀ y, s * ‖y‖ ≤ ‖reducedMap A f h y‖ := fun y => by
    have := le_norm_reducedMap_sub hA hf hh y 0
    rwa [reducedMap_zero hf0 hh0, sub_zero, sub_zero] at this
  have hk : ∀ k : ℕ, ∀ z, ‖h z - φ z‖ ≤ C' * ‖z‖ ^ q + (κ / s) ^ k * (1 + Lφ) * ‖z‖ := by
    intro k
    induction k with
    | zero =>
      intro z
      have h1 : ‖h z‖ ≤ ‖z‖ := by simpa [hh0] using hh.norm_sub_le z 0
      have h2 : ‖φ z‖ ≤ Lφ * ‖z‖ := by simpa [hφ0] using hφ.norm_sub_le z 0
      have h3 : 0 ≤ C' * ‖z‖ ^ q := by positivity
      calc ‖h z - φ z‖ ≤ ‖h z‖ + ‖φ z‖ := norm_sub_le _ _
        _ ≤ C' * ‖z‖ ^ q + (κ / s) ^ 0 * (1 + Lφ) * ‖z‖ := by
          rw [pow_zero, one_mul]; nlinarith
    | succ k ih =>
      intro z
      obtain ⟨y, rfl⟩ := reducedMap_surjective hAs hA hf hεa hh z
      have h1 := norm_sub_reducedMap_le hB hf hg hinv hφ y
      have h2 := ih y
      have h3 := hD y
      have hy := hshort y
      have hyq : s ^ q * ‖y‖ ^ q ≤ ‖reducedMap A f h y‖ ^ q := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hy q
      have hpk : 0 ≤ (κ / s) ^ k := pow_nonneg hratio k
      have e1 : κ * ((κ / s) ^ k * (1 + Lφ) * ‖y‖) =
          (κ / s) ^ (k + 1) * (1 + Lφ) * (s * ‖y‖) := by
        rw [pow_succ]; field_simp
      have h4 : (κ / s) ^ (k + 1) * (1 + Lφ) * (s * ‖y‖) ≤
          (κ / s) ^ (k + 1) * (1 + Lφ) * ‖reducedMap A f h y‖ :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      have h5 : (κ * C' + C) * ‖y‖ ^ q ≤ C' * ‖reducedMap A f h y‖ ^ q := by
        rw [hC'eq, mul_comm (s ^ q) C', mul_assoc]; exact mul_le_mul_of_nonneg_left hyq hC'0
      have h6 : κ * ‖h y - φ y‖ ≤ κ * (C' * ‖y‖ ^ q + (κ / s) ^ k * (1 + Lφ) * ‖y‖) :=
        mul_le_mul_of_nonneg_left h2 hκ0
      nlinarith
  have hlim : Tendsto (fun k : ℕ => C' * ‖x‖ ^ q + (κ / s) ^ k * (1 + Lφ) * ‖x‖) atTop
      (𝓝 (C' * ‖x‖ ^ q)) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1).mul_const
      ((1 + (Lφ : ℝ)) * ‖x‖)).const_add (C' * ‖x‖ ^ q)
    simpa [mul_assoc] using this
  exact ge_of_tendsto' hlim fun k => hk k x

/-- `M + ε t ≤ (M / σ^q + ε / σ^(q−1)) t^q` for `t ≥ σ > 0`, `q ≥ 1`. -/
@[tmio T, powerlib_foundation] private theorem add_mul_le_pow {M e σ t : ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hσ : 0 < σ) (ht : σ ≤ t) (hM : 0 ≤ M) (he : 0 ≤ e) :
    M + e * t ≤ (M / σ ^ q + e / σ ^ (q - 1)) * t ^ q := by
  have ht0 : 0 ≤ t := hσ.le.trans ht
  have hxq : σ ^ q ≤ t ^ q := pow_le_pow_left₀ hσ.le ht q
  have hxq1 : σ ^ (q - 1) * t ≤ t ^ q := by
    have : t ^ q = t ^ (q - 1) * t := by rw [← pow_succ, Nat.sub_add_cancel hq]
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ.le ht _) ht0
  have hq1 : M ≤ M / σ ^ q * t ^ q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hxq hM
  have hq2 : e * t ≤ e / σ ^ (q - 1) * t ^ q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc e * t * σ ^ (q - 1) = e * (σ ^ (q - 1) * t) := by ring
      _ ≤ e * t ^ q := mul_le_mul_of_nonneg_left hxq1 he
  rw [add_mul]
  exact add_le_add hq1 hq2

omit [CompleteSpace X] in
/-- The radial cut-off `φ ∘ π_σ` of a candidate that is `Lφ`-Lipschitz on the closed ball of
radius `σ` is `2Lφ`-Lipschitz, agrees with `φ` on the ball, and its invariance defect is
`O(‖x‖^q)` everywhere when that of `φ` is on the ball. -/
@[tmio T, powerlib_foundation] private theorem cutoff_candidate (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0)
    (hg0 : g 0 = 0) {φ : X → Y} {Lφ : NNReal} {σ C : ℝ} (hσ0 : 0 < σ)
    (hlipσ : LipschitzOnWith Lφ φ (Metric.closedBall 0 σ)) (hφ0 : φ 0 = 0) {q : ℕ} (hq : 1 ≤ q)
    (hC : ∀ x, ‖x‖ ≤ σ → ‖φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)‖ ≤ C * ‖x‖ ^ q) :
    LipschitzWith (Lφ * 2) (φ ∘ ballRetract σ) ∧ (φ ∘ ballRetract σ) 0 = 0 ∧
      (∀ v, ‖v‖ ≤ σ → (φ ∘ ballRetract σ) v = φ v) ∧
      ∃ C₂ ≥ 0, ∀ x, ‖(φ ∘ ballRetract σ) (A x + f (x, (φ ∘ ballRetract σ) x)) -
        B ((φ ∘ ballRetract σ) x) - g (x, (φ ∘ ballRetract σ) x)‖ ≤ C₂ * ‖x‖ ^ q := by
  have hε := ε.coe_nonneg
  have hL0 := Lφ.coe_nonneg
  have hφball : ∀ v, ‖v‖ ≤ σ → ‖φ v‖ ≤ Lφ * ‖v‖ := fun v hv => by
    have := hlipσ.norm_sub_le (by simpa using hv) (Metric.mem_closedBall_self hσ0.le)
    simpa [hφ0] using this
  have hφ'eq : ∀ v, ‖v‖ ≤ σ → (φ ∘ ballRetract σ) v = φ v := fun v hv => by
    simp only [Function.comp, ballRetract_of_norm_le hv]
  have hφ'lip : LipschitzWith (Lφ * 2) (φ ∘ ballRetract σ) := by
    have hmaps : Set.MapsTo (ballRetract σ : X → X) Set.univ (Metric.closedBall 0 σ) :=
      fun v _ => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact norm_ballRetract_le hσ0.le v
    have := hlipσ.comp ((lipschitzWith_ballRetract hσ0.le).lipschitzOnWith (s := Set.univ)) hmaps
    rwa [lipschitzOnWith_univ] at this
  have hφ'0 : (φ ∘ ballRetract σ) 0 = 0 := by rw [hφ'eq 0 (by simpa using hσ0.le), hφ0]
  have hφ'bd : ∀ v, ‖(φ ∘ ballRetract σ) v‖ ≤ Lφ * σ := fun v =>
    (hφball _ (norm_ballRetract_le hσ0.le v)).trans
      (mul_le_mul_of_nonneg_left (norm_ballRetract_le hσ0.le v) hL0)
  refine ⟨hφ'lip, hφ'0, hφ'eq, ?_⟩
  set φ' := φ ∘ ballRetract σ with hφ'
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂, σ₂ = σ / (‖A‖ + ε * (1 + Lφ) + 1) := ⟨_, rfl⟩
  have hden : 0 < ‖A‖ + ε * (1 + Lφ) + 1 := by positivity
  have hσ₂0 : 0 < σ₂ := by rw [hσ₂]; exact div_pos hσ0 hden
  have hσ₂σ : σ₂ ≤ σ := by
    rw [hσ₂]; exact div_le_self hσ0.le (by nlinarith [norm_nonneg A])
  have hσ₂mul : (‖A‖ + ε * (1 + Lφ) + 1) * σ₂ = σ := by rw [hσ₂]; field_simp
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ = (1 + b + ε) * (Lφ * σ) := ⟨_, rfl⟩
  have hM₀0 : 0 ≤ M₀ := by rw [hM₀]; positivity
  refine ⟨max C 0 + (M₀ / σ₂ ^ q + ε / σ₂ ^ (q - 1)), by positivity, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ σ₂
  · have hxσ : ‖x‖ ≤ σ := hx.trans hσ₂σ
    have hφx := hφball x hxσ
    have hfx : ‖f (x, φ x)‖ ≤ ε * ((1 + Lφ) * ‖x‖) := by
      have := hf.norm_sub_le (x, φ x) 0
      rw [hf0, sub_zero, sub_zero, Prod.norm_mk] at this
      refine this.trans (mul_le_mul_of_nonneg_left (max_le ?_ ?_) hε)
      · nlinarith [norm_nonneg x]
      · nlinarith [norm_nonneg x]
    have himg : ‖A x + f (x, φ x)‖ ≤ σ := by
      calc ‖A x + f (x, φ x)‖ ≤ ‖A x‖ + ‖f (x, φ x)‖ := norm_add_le _ _
        _ ≤ ‖A‖ * ‖x‖ + ε * ((1 + Lφ) * ‖x‖) := add_le_add (A.le_opNorm x) hfx
        _ ≤ (‖A‖ + ε * (1 + Lφ) + 1) * ‖x‖ := by nlinarith [norm_nonneg x]
        _ ≤ (‖A‖ + ε * (1 + Lφ) + 1) * σ₂ := mul_le_mul_of_nonneg_left hx hden.le
        _ = σ := hσ₂mul
    rw [hφ'eq x hxσ, hφ'eq _ himg]
    refine (hC x hxσ).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have : C ≤ max C 0 := le_max_left _ _
    have : 0 ≤ M₀ / σ₂ ^ q + ε / σ₂ ^ (q - 1) := by positivity
    linarith
  · push Not at hx
    have h1 := hφ'bd (A x + f (x, φ' x))
    have h2 : ‖B (φ' x)‖ ≤ b * (Lφ * σ) :=
      (hB _).trans (mul_le_mul_of_nonneg_left (hφ'bd x) hb)
    have h3 : ‖g (x, φ' x)‖ ≤ ε * (‖x‖ + Lφ * σ) := by
      have := hg.norm_sub_le (x, φ' x) 0
      rw [hg0, sub_zero, sub_zero, Prod.norm_mk] at this
      refine this.trans (mul_le_mul_of_nonneg_left (max_le ?_ ?_) hε)
      · linarith [mul_nonneg hL0 hσ0.le]
      · linarith [hφ'bd x, norm_nonneg x]
    have h4 := norm_sub_le (φ' (A x + f (x, φ' x)) - B (φ' x)) (g (x, φ' x))
    have h5 := norm_sub_le (φ' (A x + f (x, φ' x))) (B (φ' x))
    have hbound : ‖φ' (A x + f (x, φ' x)) - B (φ' x) - g (x, φ' x)‖ ≤ M₀ + ε * ‖x‖ := by
      rw [hM₀]; linarith
    have := add_mul_le_pow hq hσ₂0 hx.le hM₀0 hε
    have : 0 ≤ max C 0 * ‖x‖ ^ q := by positivity
    rw [add_mul]
    linarith

/-- **The approximation theorem.** Let `h` be the invariant `1`-Lipschitz graph of the cut-off map
and `φ` a candidate graph with `φ(0) = 0` and strict derivative `0` at `0` (`C¹`, tangent to the
centre space), whose invariance defect `φ(A x + f(x, φ x)) − B φ(x) − g(x, φ x)` is `O(‖x‖^q)` at
`0` (`q ≥ 1`). Under the gap condition `b + ε < (a − ε)^q`, `b + ε < a − ε`, the graph agrees
with `φ` to order `q`: `h(x) − φ(x) = O(‖x‖^q)`. The candidate is cut off radially to a globally
Lipschitz one, of small Lipschitz constant, whose defect is `O(‖x‖^q)` everywhere, and the global
form applies. -/
@[tmio T, powerlib_foundation] theorem isBigO_sub_of_defect (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hεa : (ε : ℝ) < a) (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {φ : X → Y}
    (hφ : HasStrictFDerivAt φ (0 : X →L[ℝ] Y) 0) (hφ0 : φ 0 = 0) {q : ℕ} (hq : 1 ≤ q)
    (hD : (fun x => φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)) =O[𝓝 0] fun x => ‖x‖ ^ q)
    (hκq : b + ε < (a - ε) ^ q) (hκ1 : b + ε < a - ε) :
    (fun x => h x - φ x) =O[𝓝 0] fun x => ‖x‖ ^ q := by
  have hε := ε.coe_nonneg
  -- a Lipschitz constant for `φ` small enough for the gap
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = min ((a - ε) ^ q - (b + ε)) (a - ε - (b + ε)) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; exact lt_min (by linarith) (by linarith)
  have hγ1 : γ ≤ (a - ε) ^ q - (b + ε) := by rw [hγ]; exact min_le_left _ _
  have hγ2 : γ ≤ a - ε - (b + ε) := by rw [hγ]; exact min_le_right _ _
  let Lφ : NNReal := ⟨γ / (4 * ((ε : ℝ) + 1)), by positivity⟩
  have hLφr : (Lφ : ℝ) = γ / (4 * ((ε : ℝ) + 1)) := rfl
  have hLφ0 : 0 < Lφ := by rw [← NNReal.coe_pos, hLφr]; positivity
  have hsmall : (ε : ℝ) * (2 * Lφ) < γ := by
    rw [hLφr]
    have e : (ε : ℝ) * (2 * (γ / (4 * ((ε : ℝ) + 1)))) = γ / 2 * (ε / (ε + 1)) := by
      field_simp; ring
    rw [e]
    have : (ε : ℝ) / (ε + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  have hcoe : ((Lφ * 2 : NNReal) : ℝ) = 2 * Lφ := by push_cast; ring
  have hκq' : b + ε * (1 + ((Lφ * 2 : NNReal) : ℝ)) < (a - ε) ^ q := by
    rw [hcoe]; linarith
  have hκ1' : b + ε * (1 + ((Lφ * 2 : NNReal) : ℝ)) < a - ε := by
    rw [hcoe]; linarith
  -- `φ` is `Lφ`-Lipschitz on a closed ball where the defect bound holds
  obtain ⟨sφ, hsφ, hlip⟩ := hφ.exists_lipschitzOnWith_of_nnnorm_lt Lφ (by simpa using hLφ0)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hsφ
  obtain ⟨C, hC⟩ := hD.bound
  obtain ⟨r₁, hr₁, hCb⟩ := Metric.eventually_nhds_iff.mp hC
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = min (r₀ / 2) (r₁ / 2) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; exact lt_min (half_pos hr₀) (half_pos hr₁)
  have hσr₀ : σ < r₀ := by rw [hσ]; exact (min_le_left _ _).trans_lt (half_lt_self hr₀)
  have hσr₁ : σ < r₁ := by rw [hσ]; exact (min_le_right _ _).trans_lt (half_lt_self hr₁)
  have hlipσ : LipschitzOnWith Lφ φ (Metric.closedBall 0 σ) := hlip.mono fun v hv => hball (by
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    exact hv.trans_lt hσr₀)
  have hCσ : ∀ x, ‖x‖ ≤ σ → ‖φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)‖ ≤ C * ‖x‖ ^ q :=
    fun x hx => by
      have := hCb (show dist x 0 < r₁ by rw [dist_zero_right]; exact hx.trans_lt hσr₁)
      rwa [norm_pow, norm_norm] at this
  obtain ⟨hφ'lip, hφ'0, hφ'eq, C₂, hC₂0, hD'⟩ :=
    cutoff_candidate hB hb hf hg hf0 hg0 hσ0 hlipσ hφ0 hq hCσ
  have hglob := norm_sub_le_of_defect hAs hA hB hb hf hg hf0 hεa hh hh0 hinv hφ'lip hφ'0 hC₂0
    hD' hκq' hκ1'
  refine IsBigO.of_bound (C₂ / ((a - ε) ^ q - (b + ε * (1 + ((Lφ * 2 : NNReal) : ℝ))))) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : X) hσ0] with x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [norm_pow, norm_norm, ← hφ'eq x hx]
  exact hglob x

/-- **Tangency of the centre manifold.** If `g(x, 0) = O(‖x‖^q)` (`q ≥ 1`) and
`b + ε < (a − ε)^q`, `b + ε < a − ε`, then `h(x) = O(‖x‖^q)`: the zero graph is a candidate with
defect `−g(x, 0)`. With `q = 2` (`g` of class `C²`, `Dg(0) = 0`), the centre manifold is tangent
to the centre space. -/
@[tmio T, powerlib_foundation] theorem isBigO_centreGraph (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hεa : (ε : ℝ) < a) (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) {q : ℕ} (hq : 1 ≤ q)
    (hg2 : (fun x => g (x, 0)) =O[𝓝 0] fun x => ‖x‖ ^ q)
    (hκq : b + ε < (a - ε) ^ q) (hκ1 : b + ε < a - ε) :
    h =O[𝓝 0] fun x => ‖x‖ ^ q := by
  have := isBigO_sub_of_defect (φ := fun _ => (0 : Y)) hAs hA hB hb hf hg hf0 hg0 hεa hh hh0
    hinv (hasStrictFDerivAt_const 0 0) rfl hq (by simpa using hg2.neg_left) hκq hκ1
  simpa using this

end Approximation

end powerlib.Map.CenterManifold
