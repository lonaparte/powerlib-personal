import theorem.GridTiedConverter.PLL.Linear
import theorem.Linear.Family
import theorem.TMIO.ClaimElab
import theorem.Spectral.Global
import theorem.SpecialFunctions.Sinusoid

/-! # SRF-PLL time-scale algebra: slow manifold, reduced slow equation, eigenvalues

Algebraic and linear-system facts about the reduction of the SRF-PLL in
T-gfl-multiscale-modeling §1.5; no claim about the accuracy of the reduction itself — the
Tikhonov/Fenichel error estimates are not formalized.

Model boundary.
* System: the SRF-PLL of `theorem/GridTiedConverter/PLL/Model.lean` (ideal balanced grid, PI loop
  filter, VCO; no pre-filter, delay, PWM, current loop or saturation; continuous time) in its
  `(θ, ξ)` coordinates (`xiField a b Δω`: `θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`), `a = V K_p`,
  `b = V K_i`, `Δω = ω_s − ω_g`.
* `ReducedSlow.family`: the reduced slow equation as the autonomous linear one-state field
  `ẏ = −(b/a) y`, `y = ξ − ξ*` (origin = reduced equilibrium); parameters `(a, b)` real.

Source: work-sync `theory/T-gfl-multiscale-modeling.md` §1.5, §1.7, §1.8;
`theory/T-invariant-coordinates.md` §1.2 (overdamped limit).

Results.
* Slow manifold (quasi-steady state of the `θ` equation with `ξ` frozen): on the domain
  `|Δω + b ξ| < a` the branch `θ*(ξ) = arcsin((Δω + b ξ)/a)` solves `Δω − a sin θ + b ξ = 0`
  (`slowAngle_spec`), lies in `(−π/2, π/2)` (`abs_slowAngle_lt`), and has normal Jacobian
  `∂_θ(Δω − a sin θ + bξ) = −a cos θ* < 0` (`slowAngle_normal_neg`).
* Reduced slow equation `ξ̇ = −sin θ*(ξ)`: on that domain it equals the linear field
  `−(Δω + b ξ)/a = −(b/a)(ξ − ξ*)`, `ξ* = −Δω/b`; the equilibrium `ξ*` is inside the domain;
  the shifted 1-state linear model `ẏ = −(b/a) y` is globally exponentially stable iff
  `b/a > 0` (`ReducedSlow.mem_den_iff`, every attractive sentence).
* Eigenvalues of the in-phase linearization `λ² + aλ + b = 0` and the overdamping parameter
  `ε_od = b/a² = 1/(4ζ²)` (the reciprocal of `four_mul_zeta_sq`; `ζ = a/(2√b)`, the `zeta` of
  `Linear.lean`). The root
  facts are generic quadratics in `Criteria` (`theorem/Criteria/Hurwitz2.lean`):
  real roots iff `ε_od ≤ 1/4` (`ζ ≥ 1`); then `λ± = −(a/2)(1 ∓ √(1 − 4ε_od))`,
  `λ₊/λ₋ = 4ε_od/(1 + √(1 − 4ε_od))² ∈ [ε_od, 4ε_od]`, `λ₋ ∈ [−a, −a/2]`,
  `λ₊ ∈ [−2b/a, −b/a]` (`Criteria.eigen_real_iff`, `eigen_roots`, `eigen_ratio`,
  `eigen_ratio_ge`, `eigen_ratio_le`, `eigen_fast_bounds`, `eigen_slow_bounds`).

Family and connection conclusions.
`ReducedSlow.family` reads a pair `(a, b)` as the autonomous
one-state field `ẏ = −(b/a) y` (`y = ξ − ξ*`, origin = reduced equilibrium). Its requirements are
static (`b/a > 0` or `b/a < 0`). Connection conclusions: soundness of every translation
(`chain_le_semantics`), exactness for the attractive sentences and sampled contraction
(`exact_hurwitz`), the membership equivalence for these sentences (`mem_den_iff`, global
exponential stability included) and exact passivity (`family_isAutonomous.exact_passive`). The slow
manifold and eigenvalue results are static.

Correction (§1.5): the reduced equation `ξ̇ = −(Δω + V K_i ξ)/(V K_p)` is stated without its
domain; it is valid only where the slow manifold exists, `|Δω + b ξ| < a` (on `|·| = a` the
manifold folds, `cos θ* = 0`, and normal hyperbolicity is lost). Also `ε_od = |λ₊/λ₋|` is not
exactly `b/a²`: the exact ratio is `4ε/(1 + √(1 − 4ε))²`, which lies between `ε` and `4ε`
and is `ε + O(ε²)`.
-/

noncomputable section
namespace powerlib.PLL
open Matrix

/-! ## Slow manifold -/

/-- Slow-manifold branch `θ*(ξ) = arcsin((Δω + b ξ)/a)`. -/
def slowAngle (a b Δω ξ : ℝ) : ℝ := Real.arcsin ((Δω + b * ξ) / a)

/-- On the domain `|Δω + b ξ| < a` the slow-manifold branch solves the quasi-steady equation
`Δω − a sin θ + b ξ = 0`. -/
@[tmio M, powerlib_domain] theorem slowAngle_spec {a b Δω ξ : ℝ} (ha : 0 < a)
    (hdom : |Δω + b * ξ| < a) : Δω - a * Real.sin (slowAngle a b Δω ξ) + b * ξ = 0 := by
  have hsin : a * Real.sin (slowAngle a b Δω ξ) = Δω + b * ξ :=
    SpecialFunctions.mul_sin_arcsin_div hdom.le ha
  linarith

/-- On the domain `|Δω + b ξ| < a` the slow-manifold branch lies in `(−π/2, π/2)`. -/
@[tmio M, powerlib_domain] theorem abs_slowAngle_lt {a b Δω ξ : ℝ} (ha : 0 < a)
    (hdom : |Δω + b * ξ| < a) : |slowAngle a b Δω ξ| < Real.pi / 2 := by
  have hx : |(Δω + b * ξ) / a| < 1 := by rw [abs_div, abs_of_pos ha, div_lt_one ha]; exact hdom
  have hx' := abs_lt.mp hx
  exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arcsin.mpr hx'.1, Real.arcsin_lt_pi_div_two.mpr hx'.2⟩

/-- On the domain `|Δω + b ξ| < a` the normal Jacobian `−a cos θ*` of the slow manifold is
negative. -/
@[tmio M, powerlib_domain] theorem slowAngle_normal_neg {a b Δω ξ : ℝ} (ha : 0 < a)
    (hdom : |Δω + b * ξ| < a) : -(a * Real.cos (slowAngle a b Δω ξ)) < 0 :=
  neg_neg_of_pos (mul_pos ha (SpecialFunctions.cos_arcsin_div_pos hdom ha))

/-- Reduced slow field on the domain: `−sin θ*(ξ) = −(Δω + b ξ)/a = −(b/a)(ξ − ξ*)`,
`ξ* = −Δω/b`. -/
@[tmio M, powerlib_domain] theorem reduced_slow_field {a b Δω ξ : ℝ} (ha : 0 < a) (hb : b ≠ 0)
    (hdom : |Δω + b * ξ| < a) :
    -Real.sin (slowAngle a b Δω ξ) = -(b / a) * (ξ - (-Δω / b)) := by
  have hx : |(Δω + b * ξ) / a| < 1 := by rw [abs_div, abs_of_pos ha, div_lt_one ha]; exact hdom
  have hx' := abs_lt.mp hx
  rw [slowAngle, Real.sin_arcsin hx'.1.le hx'.2.le]
  field_simp
  ring

/-- The reduced equilibrium `ξ* = −Δω/b` lies in the slow-manifold domain, with `θ* = 0`. -/
@[tmio M, powerlib_domain] theorem reduced_equilibrium_mem {a b Δω : ℝ} (ha : 0 < a) (hb : b ≠ 0) :
    |Δω + b * (-Δω / b)| < a ∧ slowAngle a b Δω (-Δω / b) = 0 := by
  have h0 : Δω + b * (-Δω / b) = 0 := by field_simp; ring
  refine ⟨by rw [h0, abs_zero]; exact ha, ?_⟩
  rw [slowAngle, h0, zero_div, Real.arcsin_zero]

/-- The state matrix `[−(b/a)]` of the shifted reduced slow model `ẏ = −(b/a) y`
(`y = ξ − ξ*`). -/
def reducedA (a b : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![-(b / a)]

/-- The reduced slow model is Hurwitz iff `b/a > 0`. -/
@[tmio TM, powerlib_domain] theorem isHurwitz_reducedA_iff (a b : ℝ) :
    LinearSystems.IsHurwitz (reducedA a b) ↔ 0 < b / a := by
  rw [reducedA, Linear.isHurwitz_one_iff, neg_lt_zero]

namespace ReducedSlow

open LinearSystems

/-- The reduced slow model of the SRF-PLL: `a = V K_p`, `b = V K_i`. -/
structure Model where
  /-- Proportional loop gain `V K_p`. -/
  a : ℝ
  /-- Integral loop gain `V K_i`. -/
  b : ℝ

/-- The shifted reduced slow field `ẏ = −(b/a) y`. -/
def Model.field (m : Model) : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
  affineLinearVectorField (reducedA m.a m.b) 0

/-- Requirements on the reduced slow model, all static. -/
inductive Requirement
  /-- `b/a > 0`. -/
  | positiveRatio
  /-- `b/a < 0`. -/
  | negativeRatio

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .positiveRatio => 0 < m.b / m.a
  | .negativeRatio => m.b / m.a < 0

/-- The translation of the sentences: the attractive sentences, sampled contraction and Lyapunov
stability into `b/a > 0`, instability into `b/a < 0`, passivity into nothing. Decay rates and
conservation are translated into the whole (inconsistent) language: unavailable coverage. -/
def translate : Sentence → Set Requirement
  | .flow .unstable => {.negativeRatio}
  | .flow (.decay _) | .flow .conservative => Set.univ
  | .flow _ => {.positiveRatio}
  | .passive => ∅
  | .envelope _ => ∅

/-- The reduced slow family: every model read as its autonomous one-state field. -/
def family : Family Model Requirement 1 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-- The whole requirement language is inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of_forall fun m h => ?_
  have h1 : 0 < m.b / m.a := h .positiveRatio
  have h2 : m.b / m.a < 0 := h .negativeRatio
  linarith

/-- The reduced slow model satisfies an attractive sentence (in particular global exponential
stability) or sampled contraction iff `b/a > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff {m : Model} {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ family.den (.flow P) ↔ 0 < m.b / m.a) := by
  change m ∈ family.den (.flow P) ↔ 0 < m.b / m.a
  rw [(connection_proof% family_isAutonomous.mem_den_flow), ← isHurwitz_reducedA_iff]
  rcases hP with hP | rfl
  · exact Linear.holds_iff_isHurwitz 0 hP
  · exact Linear.sampledContraction_iff_isHurwitz 0

/-- Every translation of the reduced slow family is sound (the global table,
`Spectral.chain_le_semantics_of_globalTable`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hG : TMIO.realize family.meets {.positiveRatio} ⊆
      family.den (.flow .globallyExponentiallyStable) := fun m hm =>
    (mem_den_iff (P := .globallyExponentiallyStable) (Or.inl trivial)).mpr
      ((TMIO.mem_realize _ _ _).mp hm _ rfl)
  refine Spectral.chain_le_semantics_of_globalTable (F := family) (Rs := {.positiveRatio})
    (Rg := {.positiveRatio}) (Ru := {.negativeRatio}) (Rc := Set.univ) (Rp := ∅)
    (Rd := fun _ => Set.univ) (fun s => ?_)
    (fun m hm => Spectral.den_globallyExponentiallyStable_subset_les (hG hm)) hG
    (fun _ => Spectral.realize_univ_subset_of_eq_empty realize_univ _) (fun m hm => ?_)
    (Spectral.realize_univ_subset_of_eq_empty realize_univ _)
    (fun m _ => by rw [family_isAutonomous.den_passive]; trivial) family_isAutonomous.den_envelope
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  have hneg : m.b / m.a < 0 := (TMIO.mem_realize _ _ _).mp hm _ rfl
  refine family_isAutonomous.mem_den_flow.mpr
    (Linear.unstable_of_root (s := ((-(m.b / m.a) : ℝ) : ℂ)) 0 ?_ ?_)
  · simp [Linear.characteristicMatrix, reducedA, Matrix.det_unique]
  · simpa using hneg

/-- On the attractive sentences and sampled contraction the chain agrees with the semantics. -/
@[tmio TM, powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have ht : translate (.flow P) = {.positiveRatio} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact absurd hP id
    · rfl
  unfold Family.Exact
  change TMIO.realize Meets (translate (.flow P)) = _
  rw [ht]
  ext m
  rw [(connection_proof% mem_den_iff hP)]
  simp [Meets]

end ReducedSlow

end powerlib.PLL
