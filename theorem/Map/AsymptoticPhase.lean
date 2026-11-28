import theorem.Map.CenterReduction

/-! # The asymptotic phase of the centre manifold of a map; Lyapunov stability in the reduction
principle

Every orbit of a map in centre–stable form `F(x, y) = (A x + f(x, y), B y + g(x, y))` with an
invariant `1`-Lipschitz graph `y = h(x)` (`theorem/Map/CenterManifold.lean`) is shadowed by an
orbit on the graph: there is a point `x̄ = φ(p)` of the centre space, the **asymptotic phase** of
`p`, with
`‖Fᵏ p − Fᵏ(x̄, h x̄)‖ ≤ (1 + ε/(a − b − 3ε)) (b + 2ε)ᵏ ‖p₂ − h(p₁)‖` for every `k`.
The graph orbit is `Fᵏ(x̄, h x̄) = (rᵏ x̄, h(rᵏ x̄))` with the reduced map `r(x) = A x + f(x, h x)`,
so the orbit of `p` approaches the graph not only in distance (`norm_iterate_sub_graph_le`) but
in phase. The construction does not use a second contraction on a function space: the reduced map
is a bijection whose inverse shrinks distances by at most `1/(a − ε)`, the centre coordinates of
an orbit form a pseudo-orbit of `r` with defects `ε (b + 2ε)ᵏ ‖p₂ − h(p₁)‖`, and the
finite-horizon phases `φ_N(p) = r^{−N}((F^N p)₁)` (the graph point whose reduced orbit has, after
`N` steps, the centre coordinate of `F^N p`) form a Cauchy sequence with ratio
`μ = (b + 2ε)/(a − ε) < 1`. The limit commutes with the dynamics, `φ(F p) = r(φ(p))`, which turns
the one-step bound `‖p₁ − φ(p)‖ ≤ ε ‖p₂ − h(p₁)‖/(a − b − 3ε)` into the bound along the orbit.

With the asymptotic phase the reduction principle is complete for Lyapunov stability: in the
setting of `theorem/Map/CenterReduction.lean` (a map `G` on `ℝⁿ` read through a linear embedding
`Φ` as the cut-off map near `0`), `G` is Lyapunov stable exactly when the reduced map is, and
unstable exactly when the reduced map is. The new direction, "`r` Lyapunov stable ⇒ `G`
Lyapunov stable", cannot use total stability (a Lyapunov stable map need not keep pseudo-orbits
small); the phase replaces the pseudo-orbit by a true orbit of `r` started at `φ(Φ e)`, whose
size is controlled by `‖Φ e‖`.

Scope.
* Real normed spaces `X` (complete), `Y`; `X × Y` with the max norm; `A` onto with
  `a ‖x‖ ≤ ‖A x‖`, `‖B y‖ ≤ b ‖y‖`, `0 ≤ b`; `f`, `g` globally `ε`-Lipschitz; `b + 3ε < a`
  (the gap of the centre manifold theorem). The graph `h` is any invariant `1`-Lipschitz graph
  (for instance `centreGraph`); `h(0) = 0` and `f(0) = 0` are used only where stated. The
  rate `b + 2ε` is the rate of attraction of the graph; the phase is unique among graph points
  shadowing at any rate below `a − ε` (`eq_asymptoticPhase`), and the phase map is continuous
  (`continuous_asymptoticPhase`), the identity on the graph, and within
  `ε ‖p₂ − h(p₁)‖/(a − b − 3ε)` of the centre coordinate.
* Lipschitz dependence of the phase on `p` is not proved here: the finite-horizon phases are
  Lipschitz only with constants growing like `((‖A‖ + ε)/(a − ε))^N`, and stable foliations are
  in general only Hölder continuous. Continuity, `φ(0) = 0` and the linear bound at the graph are
  what the stability transfers use. Hölder continuity with an explicit exponent is
  `theorem/Map/AsymptoticPhaseRegularity.lean` (`norm_asymptoticPhase_sub_le_rpow`); Lipschitz
  continuity for nonlinearities with Lipschitz derivatives under the bunching condition
  `(b + 2ε)(α + ε) < a − ε`, and a Lipschitz nonlinearity with a non-Lipschitz phase, are
  `theorem/Map/AsymptoticPhaseLipschitz.lean`.
* The local form (`exists_local_asymptoticPhase`): for nonlinearities with strict derivative `0`
  at `0`, the cut-off of `exists_local_centreManifold`; every orbit of the original map that stays
  in the ball `‖p‖ ≤ ρ` is shadowed by an orbit of the cut-off map on the graph.
* Reduction principle: the map semantics of `theorem/Map/Defs.lean` on `ℝⁿ` and `ℝᶜ`
  (`Map.LyapunovStable`, `Map.Unstable`), with the agreement `Φ (G e) = F (Φ e)` on a ball, a
  left inverse `Ψ`, and `b + 2ε < 1`, as in `theorem/Map/CenterReduction.lean`.
* Generic; nothing here describes a physical system (foundation).

Source: the asymptotic phase (the invariant foliation by stable fibres) of a centre manifold:
Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2 (Theorem 2 and the remark on the
asymptotic phase, used for the full reduction principle); Kelley, "The stable, center-stable,
center, center-unstable and unstable manifolds", J. Differential Equations 3 (1967); Pliss, "A
reduction principle in the theory of stability of motion" (1964); Hirsch, Pugh and Shub,
*Invariant Manifolds* (LNM 583, 1977); Hasselblatt and Wilkinson, "Prevalence of non-Lipschitz
Anosov foliations", Ergodic Theory Dynam. Systems 19 (1999) (stable foliations need not be
Lipschitz); the open item of `theorem/Map/CenterReduction.lean` (Scope: "`r` Lyapunov stable
(not asymptotically) ⇒ `G` Lyapunov stable" needs the asymptotic phase).

Results.
* Maps: `phaseApprox` (`φ_N(p) = r^{−N}((F^N p)₁)`), `asymptoticPhase` (`φ`, their limit).
* The inverse of the reduced map: `reducedMap_invFun`, `invFun_reducedMap`,
  `le_norm_iterate_invFun_sub` (`(a − ε)^N ‖r^{−N} z − r^{−N} z'‖ ≤ ‖z − z'‖`),
  `le_norm_iterate_reducedMap_sub` (`(a − ε)^k ‖x − x'‖ ≤ ‖rᵏ x − rᵏ x'‖`),
  `continuous_invFun_reducedMap`.
* Convergence: `norm_phaseApprox_succ_sub_le` (the increments, `ε (b + 2ε)^N ‖p₂ − h p₁‖ /
  (a − ε)^{N+1}`), `tendsto_phaseApprox`, `norm_phaseApprox_sub_le` (the tail,
  `ε ‖p₂ − h p₁‖ μ^N/(a − b − 3ε)`), `norm_sub_asymptoticPhase_le` (`‖p₁ − φ(p)‖ ≤
  ε ‖p₂ − h p₁‖/(a − b − 3ε)`).
* Properties: `asymptoticPhase_splitMap` (`φ(F p) = r(φ(p))`), `asymptoticPhase_iterate`,
  `asymptoticPhase_graph` (`φ(x, h x) = x`), `asymptoticPhase_zero`, `norm_asymptoticPhase_le`,
  `eq_asymptoticPhase` (uniqueness), `continuous_asymptoticPhase`.
* **The theorem** `norm_iterate_sub_asymptoticPhase_le`:
  `‖Fᵏ p − Fᵏ(φ p, h(φ p))‖ ≤ (1 + ε/(a − b − 3ε)) (b + 2ε)ᵏ ‖p₂ − h(p₁)‖`, with its centre part
  `norm_iterate_fst_sub_asymptoticPhase_le`; the local form `exists_local_asymptoticPhase`.
* **Reduction principle, completed**: `lyapunovStable_of_reduced` (`r` Lyapunov stable ⇒ `G`
  Lyapunov stable), `lyapunovStable_iff` (`G` Lyapunov stable ⇔ `r` Lyapunov stable),
  `unstable_iff` (`G` unstable ⇔ `r` unstable), with `lyapunovStable_reduced` and
  `unstable_of_reduced` of `theorem/Map/CenterReduction.lean` as the other directions.

Corrections.
None: an extension (the asymptotic phase, and the transfer of Lyapunov stability and instability
in both directions, which `theorem/Map/CenterReduction.lean` left open).

Family and connection conclusions.
None: static evidence on maps (stability in the map semantics).
-/

noncomputable section

open Filter Topology

namespace powerlib.Map.CenterManifold

section Phase

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The phase after `N` steps: `r^{−N}((F^N p)₁)`, the graph point whose reduced orbit has, after
`N` steps, the centre coordinate of `F^N p` (`r⁻¹` is `Function.invFun` of the reduced map). -/
def phaseApprox (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) (f : X × Y → X) (g : X × Y → Y) (h : X → Y)
    (N : ℕ) (p : X × Y) : X :=
  (Function.invFun (reducedMap A f h))^[N] ((splitMap A B f g)^[N] p).1

/-- The asymptotic phase of `p`: the limit of the finite-horizon phases `phaseApprox N p`. -/
def asymptoticPhase (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) (f : X × Y → X) (g : X × Y → Y)
    (h : X → Y) (p : X × Y) : X :=
  limUnder atTop fun N => phaseApprox A B f g h N p

variable {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {f : X × Y → X} {g : X × Y → Y} {a b : ℝ}
  {ε : NNReal} {h : X → Y}

omit [NormedSpace ℝ Y] in
/-- Iterates of the reduced map expand distances at least by `(a − ε)ᵏ`. -/
@[tmio T, powerlib_foundation] theorem le_norm_iterate_reducedMap_sub (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖)
    (hf : LipschitzWith ε f) (hεa : (ε : ℝ) ≤ a) (hh : LipschitzWith 1 h) (k : ℕ) (x x' : X) :
    (a - ε) ^ k * ‖x - x'‖ ≤ ‖(reducedMap A f h)^[k] x - (reducedMap A f h)^[k] x'‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    have h1 := le_norm_reducedMap_sub hA hf hh ((reducedMap A f h)^[k] x)
      ((reducedMap A f h)^[k] x')
    have h0 : (0 : ℝ) ≤ a - ε := by linarith
    calc (a - ε) ^ k * (a - ε) * ‖x - x'‖ = (a - ε) * ((a - ε) ^ k * ‖x - x'‖) := by ring
      _ ≤ (a - ε) * ‖(reducedMap A f h)^[k] x - (reducedMap A f h)^[k] x'‖ :=
          mul_le_mul_of_nonneg_left ih h0
      _ ≤ _ := h1

section Inverse

variable [CompleteSpace X]

omit [NormedSpace ℝ Y] in
/-- `r ∘ r⁻¹ = id`: the reduced map along a `1`-Lipschitz graph is onto. -/
@[tmio T, powerlib_foundation] theorem reducedMap_invFun (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hεa : (ε : ℝ) < a)
    (hh : LipschitzWith 1 h) (z : X) :
    reducedMap A f h (Function.invFun (reducedMap A f h) z) = z :=
  Function.rightInverse_invFun (reducedMap_surjective hAs hA hf hεa hh) z

omit [NormedSpace ℝ Y] in
/-- `r⁻¹ ∘ r = id`: the reduced map along a `1`-Lipschitz graph is one-to-one. -/
@[tmio T, powerlib_foundation] theorem invFun_reducedMap (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hεa : (ε : ℝ) < a)
    (hh : LipschitzWith 1 h) (x : X) :
    Function.invFun (reducedMap A f h) (reducedMap A f h x) = x :=
  Function.leftInverse_invFun (reducedMap_bijective hAs hA hf hεa hh).1 x

omit [NormedSpace ℝ Y] in
/-- **The inverse of the reduced map shrinks distances at most by `1/(a − ε)` per step:**
`(a − ε)^N ‖r^{−N} z − r^{−N} z'‖ ≤ ‖z − z'‖`. -/
@[tmio T, powerlib_foundation] theorem le_norm_iterate_invFun_sub (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f) (hεa : (ε : ℝ) < a)
    (hh : LipschitzWith 1 h) (N : ℕ) (z z' : X) :
    (a - ε) ^ N * ‖(Function.invFun (reducedMap A f h))^[N] z -
      (Function.invFun (reducedMap A f h))^[N] z'‖ ≤ ‖z - z'‖ := by
  set R := Function.invFun (reducedMap A f h) with hR
  have h0 : (0 : ℝ) ≤ a - ε := by linarith
  have one : ∀ u u' : X, (a - ε) * ‖R u - R u'‖ ≤ ‖u - u'‖ := fun u u' => by
    have := le_norm_reducedMap_sub hA hf hh (R u) (R u')
    rwa [reducedMap_invFun hAs hA hf hεa hh, reducedMap_invFun hAs hA hf hεa hh] at this
  induction N generalizing z z' with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ]
    calc (a - ε) ^ N * (a - ε) * ‖R^[N] (R z) - R^[N] (R z')‖
        = (a - ε) * ((a - ε) ^ N * ‖R^[N] (R z) - R^[N] (R z')‖) := by ring
      _ ≤ (a - ε) * ‖R z - R z'‖ := mul_le_mul_of_nonneg_left (ih _ _) h0
      _ ≤ ‖z - z'‖ := one z z'

omit [NormedSpace ℝ Y] in
/-- The inverse of the reduced map is continuous (Lipschitz with constant `1/(a − ε)`). -/
@[tmio T, powerlib_foundation] theorem continuous_invFun_reducedMap
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hf : LipschitzWith ε f)
    (hεa : (ε : ℝ) < a) (hh : LipschitzWith 1 h) :
    Continuous (Function.invFun (reducedMap A f h)) := by
  have hpos : 0 < a - ε := by linarith
  refine (LipschitzWith.of_dist_le_mul (K := (a - ε)⁻¹.toNNReal) fun z z' => ?_).continuous
  have := le_norm_iterate_invFun_sub hAs hA hf hεa hh 1 z z'
  simp only [Function.iterate_one, pow_one] at this
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.mpr hpos.le), ← div_eq_inv_mul,
    le_div_iff₀ hpos, mul_comm]
  exact this

/-- **The increments of the finite-horizon phases**:
`(a − ε)^{N+1} ‖φ_{N+1}(p) − φ_N(p)‖ ≤ ε (b + 2ε)^N ‖p₂ − h(p₁)‖`. -/
@[tmio T, powerlib_foundation] theorem norm_phaseApprox_succ_sub_le (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hεa : (ε : ℝ) < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) (N : ℕ) :
    (a - ε) ^ (N + 1) * ‖phaseApprox A B f g h (N + 1) p - phaseApprox A B f g h N p‖ ≤
      ε * ((b + 2 * ε) ^ N * ‖p.2 - h p.1‖) := by
  have e : phaseApprox A B f g h N p = (Function.invFun (reducedMap A f h))^[N + 1]
      (reducedMap A f h ((splitMap A B f g)^[N] p).1) := by
    rw [Function.iterate_succ_apply, invFun_reducedMap hAs hA hf hεa hh]; rfl
  rw [e]
  exact (le_norm_iterate_invFun_sub hAs hA hf hεa hh (N + 1) _ _).trans
    (norm_iterate_succ_sub_reducedMap_le hB hb hf hg hh hinv p N)

/-- The finite-horizon phases converge, with the tail
`‖φ_N(p) − φ(p)‖ ≤ ε ‖p₂ − h(p₁)‖ μ^N/(a − b − 3ε)`, `μ = (b + 2ε)/(a − ε)`. -/
@[tmio T, powerlib_foundation] private theorem phase_spec (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) :
    Tendsto (fun N => phaseApprox A B f g h N p) atTop (𝓝 (asymptoticPhase A B f g h p)) ∧
      ∀ N : ℕ, ‖phaseApprox A B f g h N p - asymptoticPhase A B f g h p‖ ≤
        ε * ‖p.2 - h p.1‖ / (a - b - 3 * ε) * ((b + 2 * ε) / (a - ε)) ^ N := by
  have hε := ε.coe_nonneg
  have hεa : (ε : ℝ) < a := by linarith
  have hpos : 0 < a - ε := by linarith
  have hgap' : 0 < a - b - 3 * ε := by linarith
  set μ := (b + 2 * ε) / (a - ε) with hμ
  have hμ1 : μ < 1 := by rw [hμ, div_lt_one hpos]; linarith
  set C := ε * ‖p.2 - h p.1‖ / (a - ε) with hC
  have hstep : ∀ N : ℕ, dist (phaseApprox A B f g h N p) (phaseApprox A B f g h (N + 1) p) ≤
      C * μ ^ N := fun N => by
    have h1 := norm_phaseApprox_succ_sub_le hAs hA hB hb hf hg hεa hh hinv p N
    rw [dist_eq_norm, norm_sub_rev]
    have key : C * μ ^ N = ε * ((b + 2 * ε) ^ N * ‖p.2 - h p.1‖) / (a - ε) ^ (N + 1) := by
      rw [hC, hμ, div_pow, pow_succ]; field_simp
    rw [key, le_div_iff₀ (pow_pos hpos _), mul_comm]
    exact h1
  have hlim : Tendsto (fun N => phaseApprox A B f g h N p) atTop
      (𝓝 (asymptoticPhase A B f g h p)) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric μ C hμ1 hstep))
  refine ⟨hlim, fun N => ?_⟩
  have := dist_le_of_le_geometric_of_tendsto μ C hμ1 hstep hlim N
  rw [dist_eq_norm] at this
  refine this.trans (le_of_eq ?_)
  have h1 : 1 - μ = (a - b - 3 * ε) / (a - ε) := by rw [hμ]; field_simp; ring
  rw [h1, hC]
  field_simp

/-- The finite-horizon phases converge to the asymptotic phase. -/
@[tmio T, powerlib_foundation] theorem tendsto_phaseApprox (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) :
    Tendsto (fun N => phaseApprox A B f g h N p) atTop (𝓝 (asymptoticPhase A B f g h p)) :=
  (phase_spec hAs hA hB hb hf hg hgap hh hinv p).1

/-- **The tail of the finite-horizon phases**:
`‖φ_N(p) − φ(p)‖ ≤ ε ‖p₂ − h(p₁)‖ ((b + 2ε)/(a − ε))^N / (a − b − 3ε)`. -/
@[tmio T, powerlib_foundation] theorem norm_phaseApprox_sub_le (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) (N : ℕ) :
    ‖phaseApprox A B f g h N p - asymptoticPhase A B f g h p‖ ≤
      ε * ‖p.2 - h p.1‖ / (a - b - 3 * ε) * ((b + 2 * ε) / (a - ε)) ^ N :=
  (phase_spec hAs hA hB hb hf hg hgap hh hinv p).2 N

/-- **The phase is close to the centre coordinate:**
`‖p₁ − φ(p)‖ ≤ ε ‖p₂ − h(p₁)‖/(a − b − 3ε)`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_asymptoticPhase_le (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) :
    ‖p.1 - asymptoticPhase A B f g h p‖ ≤ ε * ‖p.2 - h p.1‖ / (a - b - 3 * ε) := by
  have := norm_phaseApprox_sub_le hAs hA hB hb hf hg hgap hh hinv p 0
  rwa [pow_zero, mul_one] at this

/-- **The phase commutes with the dynamics:** `φ(F p) = r(φ(p))`. The finite-horizon phases
satisfy `r(φ_{N+1}(p)) = φ_N(F p)`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_splitMap (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) :
    asymptoticPhase A B f g h (splitMap A B f g p) =
      reducedMap A f h (asymptoticPhase A B f g h p) := by
  have hεa : (ε : ℝ) < a := by have := ε.coe_nonneg; linarith
  have hstep : ∀ N, reducedMap A f h (phaseApprox A B f g h (N + 1) p) =
      phaseApprox A B f g h N (splitMap A B f g p) := fun N => by
    simp only [phaseApprox]
    rw [Function.iterate_succ_apply' (Function.invFun _), reducedMap_invFun hAs hA hf hεa hh,
      Function.iterate_succ_apply]
  have h1 : Tendsto (fun N => reducedMap A f h (phaseApprox A B f g h (N + 1) p)) atTop
      (𝓝 (reducedMap A f h (asymptoticPhase A B f g h p))) :=
    ((lipschitzWith_reducedMap (A := A) hf hh).continuous.tendsto _).comp
      ((tendsto_phaseApprox hAs hA hB hb hf hg hgap hh hinv p).comp (tendsto_add_atTop_nat 1))
  simp only [hstep] at h1
  exact tendsto_nhds_unique (tendsto_phaseApprox hAs hA hB hb hf hg hgap hh hinv _) h1

/-- Along an orbit the phase follows the reduced map: `φ(Fᵏ p) = rᵏ(φ(p))`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_iterate (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) (k : ℕ) :
    asymptoticPhase A B f g h ((splitMap A B f g)^[k] p) =
      (reducedMap A f h)^[k] (asymptoticPhase A B f g h p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      asymptoticPhase_splitMap hAs hA hB hb hf hg hgap hh hinv, ih]

/-- On the graph the phase is the centre coordinate: `φ(x, h x) = x`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_graph (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (x : X) :
    asymptoticPhase A B f g h (x, h x) = x := by
  have := norm_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv (x, h x)
  simp only [sub_self, norm_zero, mul_zero, zero_div] at this
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp this)).symm

/-- The phase of the fixed point is `0`. -/
@[tmio T, powerlib_foundation] theorem asymptoticPhase_zero (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) :
    asymptoticPhase A B f g h 0 = 0 := by
  have := asymptoticPhase_graph hAs hA hB hb hf hg hgap hh hinv 0
  rwa [hh0, Prod.mk_zero_zero] at this

/-- The phase is bounded linearly: `‖φ(p)‖ ≤ (1 + 2ε/(a − b − 3ε)) ‖p‖` (`h(0) = 0`). -/
@[tmio T, powerlib_foundation] theorem norm_asymptoticPhase_le (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (p : X × Y) :
    ‖asymptoticPhase A B f g h p‖ ≤ (1 + 2 * ε / (a - b - 3 * ε)) * ‖p‖ := by
  have hε := ε.coe_nonneg
  have hgap' : 0 < a - b - 3 * ε := by linarith
  have h1 := norm_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv p
  have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have hhx : ‖h p.1‖ ≤ ‖p.1‖ := by simpa [hh0] using hh.norm_sub_le p.1 0
  have hz : ‖p.2 - h p.1‖ ≤ 2 * ‖p‖ := (norm_sub_le _ _).trans (by linarith)
  have h2 : ε * ‖p.2 - h p.1‖ / (a - b - 3 * ε) ≤ 2 * ε / (a - b - 3 * ε) * ‖p‖ := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hgap']
    nlinarith
  calc ‖asymptoticPhase A B f g h p‖ = ‖p.1 - (p.1 - asymptoticPhase A B f g h p)‖ := by
        rw [sub_sub_cancel]
    _ ≤ ‖p.1‖ + ‖p.1 - asymptoticPhase A B f g h p‖ := norm_sub_le _ _
    _ ≤ ‖p‖ + 2 * ε / (a - b - 3 * ε) * ‖p‖ := add_le_add hp1 (h1.trans h2)
    _ = (1 + 2 * ε / (a - b - 3 * ε)) * ‖p‖ := by ring

/-- **The centre coordinate shadows the reduced orbit of the phase:**
`‖(Fᵏ p)₁ − rᵏ(φ(p))‖ ≤ ε (b + 2ε)ᵏ ‖p₂ − h(p₁)‖/(a − b − 3ε)`. -/
@[tmio T, powerlib_foundation] theorem norm_iterate_fst_sub_asymptoticPhase_le
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) (k : ℕ) :
    ‖((splitMap A B f g)^[k] p).1 - (reducedMap A f h)^[k] (asymptoticPhase A B f g h p)‖ ≤
      ε * ((b + 2 * ε) ^ k * ‖p.2 - h p.1‖) / (a - b - 3 * ε) := by
  have hgap' : 0 < a - b - 3 * ε := by have := ε.coe_nonneg; linarith
  have h1 := norm_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv ((splitMap A B f g)^[k] p)
  rw [asymptoticPhase_iterate hAs hA hB hb hf hg hgap hh hinv] at h1
  refine h1.trans (div_le_div_of_nonneg_right ?_ hgap'.le)
  exact mul_le_mul_of_nonneg_left (norm_iterate_sub_graph_le hB hb hf hg hh hinv p k)
    ε.coe_nonneg

/-- **The asymptotic phase.** Every orbit of `F` is shadowed by the orbit on the invariant graph
started at its phase: `‖Fᵏ p − Fᵏ(φ p, h(φ p))‖ ≤ (1 + ε/(a − b − 3ε)) (b + 2ε)ᵏ ‖p₂ − h(p₁)‖`,
and `Fᵏ(φ p, h(φ p)) = (rᵏ(φ p), h(rᵏ(φ p)))` is an orbit of the reduced map. -/
@[tmio T, powerlib_foundation] theorem norm_iterate_sub_asymptoticPhase_le
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (hb : 0 ≤ b) (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    (p : X × Y) (k : ℕ) :
    ‖(splitMap A B f g)^[k] p -
        (splitMap A B f g)^[k] (asymptoticPhase A B f g h p, h (asymptoticPhase A B f g h p))‖ ≤
      (1 + ε / (a - b - 3 * ε)) * (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ := by
  have hε := ε.coe_nonneg
  have hgap' : 0 < a - b - 3 * ε := by linarith
  rw [splitMap_iterate_graph hinv]
  set q := (splitMap A B f g)^[k] p
  set y := (reducedMap A f h)^[k] (asymptoticPhase A B f g h p)
  set Z := (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ with hZ
  have hc := norm_iterate_fst_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv p k
  have hz : ‖q.2 - h q.1‖ ≤ Z := norm_iterate_sub_graph_le hB hb hf hg hh hinv p k
  have hZ0 : 0 ≤ Z := by
    have : 0 ≤ b + 2 * ε := by linarith
    positivity
  have hc' : ε * Z / (a - b - 3 * ε) = ε / (a - b - 3 * ε) * Z := by ring
  rw [hc'] at hc
  have hcZ : 0 ≤ ε / (a - b - 3 * ε) * Z := by positivity
  have hs : ‖q.2 - h y‖ ≤ Z + ε / (a - b - 3 * ε) * Z := by
    calc ‖q.2 - h y‖ = ‖(q.2 - h q.1) + (h q.1 - h y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖q.2 - h q.1‖ + ‖h q.1 - h y‖ := norm_add_le _ _
      _ ≤ Z + ‖q.1 - y‖ := by
          gcongr
          simpa using hh.norm_sub_le q.1 y
      _ ≤ Z + ε / (a - b - 3 * ε) * Z := by gcongr
  rw [Prod.norm_def]
  simp only [Prod.fst_sub, Prod.snd_sub]
  refine max_le (hc.trans ?_) (hs.trans (le_of_eq ?_))
  · rw [mul_assoc]; nlinarith
  · rw [hZ]; ring

/-- **The phase is unique:** a point whose reduced orbit is shadowed by the centre coordinates of
the orbit of `p` at some rate `s < a − ε` (`‖(Fᵏ p)₁ − rᵏ x‖ ≤ M sᵏ`) is the phase of `p`. -/
@[tmio T, powerlib_foundation] theorem eq_asymptoticPhase (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    {p : X × Y} {x : X} {M s : ℝ} (hs0 : 0 ≤ s) (hs : s < a - ε)
    (hM : ∀ k, ‖((splitMap A B f g)^[k] p).1 - (reducedMap A f h)^[k] x‖ ≤ M * s ^ k) :
    x = asymptoticPhase A B f g h p := by
  have hε := ε.coe_nonneg
  have hpos : 0 < a - ε := by linarith
  have hgap' : 0 < a - b - 3 * ε := by linarith
  set xp := asymptoticPhase A B f g h p
  set c := ε * ‖p.2 - h p.1‖ / (a - b - 3 * ε) with hcdef
  have hθ0 : 0 ≤ (b + 2 * ε) / (a - ε) := by positivity
  have hθ1 : (b + 2 * ε) / (a - ε) < 1 := by rw [div_lt_one hpos]; linarith
  have hs1 : s / (a - ε) < 1 := by rw [div_lt_one hpos]; exact hs
  have hb' : ∀ k : ℕ, ‖x - xp‖ ≤ M * (s / (a - ε)) ^ k + c * ((b + 2 * ε) / (a - ε)) ^ k := by
    intro k
    have h1 := le_norm_iterate_reducedMap_sub hA hf (by linarith) hh k x xp
    have h2 := norm_iterate_fst_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv p k
    have h3 := hM k
    have h4 : ‖(reducedMap A f h)^[k] x - (reducedMap A f h)^[k] xp‖ ≤
        M * s ^ k + c * (b + 2 * ε) ^ k := by
      have e : c * (b + 2 * ε) ^ k = ε * ((b + 2 * ε) ^ k * ‖p.2 - h p.1‖) / (a - b - 3 * ε) := by
        rw [hcdef]; ring
      rw [e]
      calc _ = ‖(((splitMap A B f g)^[k] p).1 - (reducedMap A f h)^[k] xp) -
              (((splitMap A B f g)^[k] p).1 - (reducedMap A f h)^[k] x)‖ := by
            congr 1; abel
        _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hk : 0 < (a - ε) ^ k := pow_pos hpos k
    have e2 : M * (s / (a - ε)) ^ k + c * ((b + 2 * ε) / (a - ε)) ^ k =
        (M * s ^ k + c * (b + 2 * ε) ^ k) / (a - ε) ^ k := by
      rw [div_pow, div_pow]; field_simp
    rw [e2, le_div_iff₀ hk, mul_comm]
    linarith
  have hlim : Tendsto (fun k : ℕ => M * (s / (a - ε)) ^ k + c * ((b + 2 * ε) / (a - ε)) ^ k)
      atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hs1).const_mul M).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul c)
    simpa using this
  have : ‖x - xp‖ ≤ 0 := ge_of_tendsto' hlim hb'
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- **The phase map is continuous:** it is the locally uniform limit of the continuous
finite-horizon phases (the tail bound is uniform where `‖p₂ − h(p₁)‖` is bounded). -/
@[tmio T, powerlib_foundation] theorem continuous_asymptoticPhase (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) :
    Continuous (asymptoticPhase A B f g h) := by
  have hε := ε.coe_nonneg
  have hεa : (ε : ℝ) < a := by linarith
  have hpos : 0 < a - ε := by linarith
  have hgap' : 0 < a - b - 3 * ε := by linarith
  have hθ0 : 0 ≤ (b + 2 * ε) / (a - ε) := by positivity
  have hθ1 : (b + 2 * ε) / (a - ε) < 1 := by rw [div_lt_one hpos]; linarith
  have hF : Continuous (splitMap A B f g) :=
    ((A.continuous.comp continuous_fst).add hf.continuous).prodMk
      ((B.continuous.comp continuous_snd).add hg.continuous)
  have hR := continuous_invFun_reducedMap hAs hA hf hεa hh
  have hN : ∀ N, Continuous (phaseApprox A B f g h N) := fun N =>
    (hR.iterate N).comp (continuous_fst.comp (hF.iterate N))
  have hz : Continuous fun p : X × Y => ‖p.2 - h p.1‖ :=
    (continuous_snd.sub (hh.continuous.comp continuous_fst)).norm
  refine continuous_of_locally_uniform_approx_of_continuousAt fun p₀ u hu => ?_
  obtain ⟨δ, hδ, hδu⟩ := Metric.mem_uniformity_dist.mp hu
  set Z := ‖p₀.2 - h p₀.1‖ + 1 with hZ
  have hZ0 : 0 < Z := by positivity
  have hlim : Tendsto (fun N : ℕ => ε * Z / (a - b - 3 * ε) * ((b + 2 * ε) / (a - ε)) ^ N)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul
      (ε * Z / (a - b - 3 * ε))
  obtain ⟨N, hNδ⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨{p | ‖p.2 - h p.1‖ < Z}, (isOpen_lt hz continuous_const).mem_nhds (by
    show ‖p₀.2 - h p₀.1‖ < Z; linarith), phaseApprox A B f g h N, (hN N).continuousAt,
    fun p hp => hδu ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  refine (norm_phaseApprox_sub_le hAs hA hB hb hf hg hgap hh hinv p N).trans_lt
    (lt_of_le_of_lt ?_ hNδ)
  have hp : ‖p.2 - h p.1‖ ≤ Z := le_of_lt hp
  gcongr

end Inverse

/-- **The local asymptotic phase.** In the setting of `exists_local_centreManifold`
(`F₀(x, y) = (A x + f₀(x, y), B y + g₀(x, y))`, `f₀`, `g₀` with strict derivative `0` at `0`,
`b + 3ε < a`): with the radius `ρ`, the cut-offs `f`, `g` and the invariant graph `h` given
there, every orbit of the original map `F₀` that stays in the ball `‖p‖ ≤ ρ` is shadowed by the
reduced orbit of its phase `x̄ = φ(p)` (the phase of the cut-off map):
`‖F₀ᵏ p − (rᵏ x̄, h(rᵏ x̄))‖ ≤ (1 + ε/(a − b − 3ε)) (b + 2ε)ᵏ ‖p₂ − h(p₁)‖`. -/
@[tmio T, powerlib_foundation] theorem exists_local_asymptoticPhase [CompleteSpace X]
    [CompleteSpace Y] {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {a b : ℝ} {ε : NNReal}
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖)
    (hb : 0 ≤ b) {f₀ : X × Y → X} {g₀ : X × Y → Y}
    (hf : HasStrictFDerivAt f₀ (0 : X × Y →L[ℝ] X) 0)
    (hg : HasStrictFDerivAt g₀ (0 : X × Y →L[ℝ] Y) 0) (hf0 : f₀ 0 = 0) (hg0 : g₀ 0 = 0)
    (hε : 0 < ε) (hgap : b + 3 * ε < a) :
    ∃ ρ > 0, ∃ f : X × Y → X, ∃ g : X × Y → Y,
      LipschitzWith ε f ∧ LipschitzWith ε g ∧ f 0 = 0 ∧ g 0 = 0 ∧
      (∀ p, ‖p‖ ≤ ρ → f p = f₀ p ∧ g p = g₀ p) ∧
      ∃ h : X → Y, LipschitzWith 1 h ∧ h 0 = 0 ∧
        (∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) ∧
        ∀ (p : X × Y) (k : ℕ), (∀ j < k, ‖(splitMap A B f₀ g₀)^[j] p‖ ≤ ρ) →
          ‖(splitMap A B f₀ g₀)^[k] p -
              ((reducedMap A f h)^[k] (asymptoticPhase A B f g h p),
                h ((reducedMap A f h)^[k] (asymptoticPhase A B f g h p)))‖ ≤
            (1 + ε / (a - b - 3 * ε)) * (b + 2 * ε) ^ k * ‖p.2 - h p.1‖ := by
  obtain ⟨ρ, hρ, f, g, hfl, hgl, hf0', hg0', hagree, h, hlip, hh0, hinv, -, -⟩ :=
    exists_local_centreManifold hAs hA hB hb hf hg hf0 hg0 hε hgap
  refine ⟨ρ, hρ, f, g, hfl, hgl, hf0', hg0', hagree, h, hlip, hh0, hinv, fun p k hk => ?_⟩
  have hsplit : ∀ q, ‖q‖ ≤ ρ → splitMap A B f₀ g₀ q = splitMap A B f g q := fun q hq => by
    simp only [splitMap, (hagree q hq).1, (hagree q hq).2]
  have heq : ∀ j ≤ k, (splitMap A B f₀ g₀)^[j] p = (splitMap A B f g)^[j] p := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih (Nat.le_of_succ_le hj)]
      exact hsplit _ (hk j hj)
  rw [heq k le_rfl, ← splitMap_iterate_graph hinv]
  exact norm_iterate_sub_asymptoticPhase_le hAs hA hB hb hfl hgl hgap hlip hinv p k

end Phase

/-! ## The reduction principle for Lyapunov stability and instability -/

section Reduction

variable {c n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "ℝᶜ" => EuclideanSpace ℝ (Fin c)
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

variable {A : EuclideanSpace ℝ (Fin c) →L[ℝ] EuclideanSpace ℝ (Fin c)} {B : Y →L[ℝ] Y}
  {f : EuclideanSpace ℝ (Fin c) × Y → EuclideanSpace ℝ (Fin c)}
  {g : EuclideanSpace ℝ (Fin c) × Y → Y} {a b : ℝ} {ε : NNReal}
  {h : EuclideanSpace ℝ (Fin c) → Y}
  {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin c) × Y}
  {Ψ : EuclideanSpace ℝ (Fin c) × Y →L[ℝ] EuclideanSpace ℝ (Fin n)} {ρ : ℝ}

/-- **Reduction principle, Lyapunov stability.** If the reduced map is Lyapunov stable at `0`,
so is `G` (`b + 3ε < a`, `b + 2ε < 1`): the `F`-orbit of `Φ e` stays within
`(1 + ε/(a − b − 3ε)) · 2‖Φ e‖` of the reduced orbit of its phase, which starts within
`(1 + 2ε/(a − b − 3ε)) ‖Φ e‖` of `0` and is kept small by the stability of `r`. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_reduced (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hθ : b + 2 * ε < 1) (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (hΨΦ : ∀ e, Ψ (Φ e) = e)
    (hρ : 0 < ρ) (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e))
    (hr : LyapunovStable (reducedMap A f h) 0) : LyapunovStable G 0 := by
  intro ε' hε'
  have hε := ε.coe_nonneg
  have hgap' : 0 < a - b - 3 * ε := by linarith
  set F := splitMap A B f g with hF
  set D := 1 + ε / (a - b - 3 * ε) with hD
  set E := 1 + 2 * ε / (a - b - 3 * ε) with hE
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ε / (a - b - 3 * ε) := by positivity
    linarith
  have hE1 : 1 ≤ E := by
    have : 0 ≤ 2 * ε / (a - b - 3 * ε) := by positivity
    linarith
  have hm : 0 < min ε' ρ := lt_min hε' hρ
  set η := min ε' ρ / (2 * (‖Ψ‖ + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δr, hδr, hδrb⟩ := hr η hη0
  set δ' := min (δr / E) (η / (2 * D)) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) (by positivity)
  refine ⟨δ' / (‖Φ‖ + 1), by positivity, fun e he k => ?_⟩
  rw [sub_zero] at he ⊢
  set p := Φ e with hpdef
  have hp : ‖p‖ < δ' := by
    calc ‖p‖ ≤ ‖Φ‖ * ‖e‖ := Φ.le_opNorm e
      _ ≤ (‖Φ‖ + 1) * ‖e‖ := by gcongr; linarith
      _ < (‖Φ‖ + 1) * (δ' / (‖Φ‖ + 1)) := by gcongr
      _ = δ' := by field_simp
  set xp := asymptoticPhase A B f g h p with hxp
  have hxpn : ‖xp - 0‖ < δr := by
    rw [sub_zero]
    calc ‖xp‖ ≤ E * ‖p‖ := norm_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hh0 hinv p
      _ < E * δ' := by gcongr
      _ ≤ E * (δr / E) := by gcongr; exact min_le_left _ _
      _ = δr := by field_simp
  have hz : ‖p.2 - h p.1‖ ≤ 2 * ‖p‖ := by
    have hhx : ‖h p.1‖ ≤ ‖p.1‖ := by simpa [hh0] using hh.norm_sub_le p.1 0
    exact (norm_sub_le _ _).trans (by linarith [norm_fst_le p, norm_snd_le p])
  have hFk : ∀ j, ‖F^[j] p‖ < 2 * η := by
    intro j
    have h1 := norm_iterate_sub_asymptoticPhase_le hAs hA hB hb hf hg hgap hh hinv p j
    rw [splitMap_iterate_graph hinv] at h1
    set y := (reducedMap A f h)^[j] xp
    have h2 : ‖y‖ < η := by simpa using hδrb xp hxpn j
    have hθj : (b + 2 * ε) ^ j ≤ 1 := pow_le_one₀ (by linarith) hθ.le
    have h3 : D * (b + 2 * ε) ^ j * ‖p.2 - h p.1‖ ≤ D * (2 * ‖p‖) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      calc (b + 2 * ε) ^ j * ‖p.2 - h p.1‖ ≤ 1 * ‖p.2 - h p.1‖ := by gcongr
        _ ≤ 2 * ‖p‖ := by rw [one_mul]; exact hz
    have h4 : D * (2 * ‖p‖) < η := by
      calc D * (2 * ‖p‖) < D * (2 * δ') := by gcongr
        _ ≤ D * (2 * (η / (2 * D))) := by gcongr; exact min_le_right _ _
        _ = η := by field_simp
    calc ‖F^[j] p‖ = ‖(F^[j] p - (y, h y)) + (y, h y)‖ := by rw [sub_add_cancel]
      _ ≤ ‖F^[j] p - (y, h y)‖ + ‖(y, h y)‖ := norm_add_le _ _
      _ = ‖F^[j] p - (y, h y)‖ + ‖y‖ := by rw [norm_graph hh hh0]
      _ < η + η := add_lt_add_of_le_of_lt (h1.trans (h3.trans h4.le)) h2
      _ = 2 * η := by ring
  have hsmall : ∀ j, ‖Ψ (F^[j] p)‖ < min ε' ρ := fun j => by
    calc ‖Ψ (F^[j] p)‖ ≤ ‖Ψ‖ * ‖F^[j] p‖ := Ψ.le_opNorm _
      _ ≤ (‖Ψ‖ + 1) * ‖F^[j] p‖ := by gcongr; linarith
      _ < (‖Ψ‖ + 1) * (2 * η) := by gcongr; exact hFk j
      _ = min ε' ρ := by rw [hη]; field_simp
  have hconj : Φ (G^[k] e) = F^[k] (Φ e) :=
    iterate_conj_of_norm_lt hΨΦ hG fun j _ => (hsmall j).trans_le (min_le_right _ _)
  have hGk : G^[k] e = Ψ (F^[k] p) := by rw [← hconj, hΨΦ]
  rw [hGk]
  exact (hsmall k).trans_le (min_le_left _ _)

/-- **Reduction principle, Lyapunov stability, both directions.** For an invariant graph lying in
the range of `Φ`, `b + 3ε < a` and `b + 2ε < 1`, `G` is Lyapunov stable at `0` exactly when the
reduced map is. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_iff (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hθ : b + 2 * ε < 1) (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (hΨΦ : ∀ e, Ψ (Φ e) = e)
    (hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x)) (hρ : 0 < ρ)
    (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e)) :
    LyapunovStable G 0 ↔ LyapunovStable (reducedMap A f h) 0 :=
  ⟨lyapunovStable_reduced hh hh0 hinv hgraph hρ hG,
    lyapunovStable_of_reduced hAs hA hB hb hf hg hgap hθ hh hh0 hinv hΨΦ hρ hG⟩

/-- **Reduction principle, instability, both directions.** Under the hypotheses of
`lyapunovStable_iff`, `G` is unstable at `0` exactly when the reduced map is. -/
@[tmio T, powerlib_foundation] theorem unstable_iff (hAs : Function.Surjective A)
    (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a)
    (hθ : b + 2 * ε < 1) (hh : LipschitzWith 1 h) (hh0 : h 0 = 0)
    (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x)) (hΨΦ : ∀ e, Ψ (Φ e) = e)
    (hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x)) (hρ : 0 < ρ)
    (hG : ∀ e, ‖e‖ < ρ → Φ (G e) = splitMap A B f g (Φ e)) :
    Unstable G 0 ↔ Unstable (reducedMap A f h) 0 :=
  not_congr (lyapunovStable_iff hAs hA hB hb hf hg hgap hθ hh hh0 hinv hΨΦ hgraph hρ hG)

end Reduction

end powerlib.Map.CenterManifold
