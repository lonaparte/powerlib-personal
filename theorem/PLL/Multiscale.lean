import theorem.PLL.Linear
import theorem.Linear.Family
import theorem.TMIO.ClaimElab

/-! # SRF-PLL time-scale algebra: slow manifold, reduced slow equation, eigenvalues

Algebraic and linear-system facts about the reduction of the SRF-PLL in
T-gfl-multiscale-modeling §1.5; no claim about the accuracy of the reduction itself — the
Tikhonov/Fenichel error estimates are not formalized.

Setting: `(θ, ξ)` coordinates of `theorem/PLL/Model.lean` (`xiField a b Δω`:
`θ̇ = Δω − a sin θ + b ξ`, `ξ̇ = −sin θ`), `a = V K_p`, `b = V K_i`, `Δω = ω_s − ω_g`.

* Slow manifold (quasi-steady state of the `θ` equation with `ξ` frozen): on the domain
  `|Δω + b ξ| < a` the branch `θ*(ξ) = arcsin((Δω + b ξ)/a)` solves `Δω − a sin θ + b ξ = 0`,
  lies in `(−π/2, π/2)`, and has normal Jacobian `∂_θ(Δω − a sin θ + bξ) = −a cos θ* < 0`.
* Reduced slow equation `ξ̇ = −sin θ*(ξ)`: on that domain it equals the linear field
  `−(Δω + b ξ)/a = −(b/a)(ξ − ξ*)`, `ξ* = −Δω/b`; the equilibrium `ξ*` is inside the domain;
  the shifted 1-state linear model `ẏ = −(b/a) y` is globally exponentially stable iff
  `b/a > 0` (`ReducedSlow.mem_den_globallyExponentiallyStable_iff`).
* Eigenvalues of the in-phase linearization `λ² + aλ + b = 0` and the overdamping parameter
  `ε_od = b/a² = 1/(4ζ²)` (`epsOd_eq`; `ζ = a/(2√b)`, the `zeta` of `Linear.lean`). The root
  facts are generic quadratics in `Criteria` (`theorem/Criteria/Hurwitz2.lean`):
  real roots iff `ε_od ≤ 1/4` (`ζ ≥ 1`); then `λ± = −(a/2)(1 ∓ √(1 − 4ε_od))`,
  `λ₊/λ₋ = 4ε_od/(1 + √(1 − 4ε_od))² ∈ [ε_od, 4ε_od]`, `λ₋ ∈ [−a, −a/2]`,
  `λ₊ ∈ [−2b/a, −b/a]` (`Criteria.eigen_real_iff`, `eigen_roots`, `eigen_ratio`,
  `eigen_bounds`).

Source: work-sync `theory/T-gfl-multiscale-modeling.md` §1.5, §1.7, §1.8;
`theory/T-invariant-coordinates.md` §1.2 (overdamped limit).

Correction (§1.5): the reduced equation `ξ̇ = −(Δω + V K_i ξ)/(V K_p)` is stated without its
domain; it is valid only where the slow manifold exists, `|Δω + b ξ| < a` (on `|·| = a` the
manifold folds, `cos θ* = 0`, and normal hyperbolicity is lost). Also `ε_od = |λ₊/λ₋|` is not
exactly `b/a²`: the exact ratio is `4ε/(1 + √(1 − 4ε))²`, which lies between `ε` and `4ε`
and is `ε + O(ε²)`.

Family and connection conclusions. `ReducedSlow.family` reads a pair `(a, b)` as the autonomous
one-state field `ẏ = −(b/a) y` (`y = ξ − ξ*`, origin = reduced equilibrium). Its requirements are
static (`b/a > 0` or `b/a < 0`). Connection conclusions: soundness of every translation
(`chain_le_semantics`), exactness for the attractive sentences and sampled contraction
(`exact_hurwitz`), the membership form of the former `reducedModel_exponentiallyStable_iff`
(`mem_den_globallyExponentiallyStable_iff`) and exact passivity (`exact_passive`). The slow
manifold and eigenvalue results are static.
-/

noncomputable section
namespace powerlib.PLL
open Matrix

/-! ## Slow manifold -/

/-- Slow-manifold branch `θ*(ξ) = arcsin((Δω + b ξ)/a)`. -/
def slowAngle (a b Δω ξ : ℝ) : ℝ := Real.arcsin ((Δω + b * ξ) / a)

@[powerlib_foundation] theorem slowAngle_spec {a b Δω ξ : ℝ} (ha : 0 < a)
    (hdom : |Δω + b * ξ| < a) :
    Δω - a * Real.sin (slowAngle a b Δω ξ) + b * ξ = 0 ∧
      |slowAngle a b Δω ξ| < Real.pi / 2 ∧
      -(a * Real.cos (slowAngle a b Δω ξ)) < 0 := by
  have hx : |(Δω + b * ξ) / a| < 1 := by rw [abs_div, abs_of_pos ha, div_lt_one ha]; exact hdom
  have hx' := abs_lt.mp hx
  have hsin : Real.sin (slowAngle a b Δω ξ) = (Δω + b * ξ) / a :=
    Real.sin_arcsin hx'.1.le hx'.2.le
  have hlt : |slowAngle a b Δω ξ| < Real.pi / 2 :=
    abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arcsin.mpr hx'.1, Real.arcsin_lt_pi_div_two.mpr hx'.2⟩
  have hcos : 0 < Real.cos (slowAngle a b Δω ξ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (slowAngle a b Δω ξ)],
      lt_of_le_of_lt (le_abs_self _) hlt⟩
  refine ⟨?_, hlt, by nlinarith⟩
  rw [hsin]; field_simp; ring

/-- Reduced slow field on the domain: `−sin θ*(ξ) = −(Δω + b ξ)/a = −(b/a)(ξ − ξ*)`,
`ξ* = −Δω/b`. -/
@[powerlib_foundation] theorem reduced_slow_field {a b Δω ξ : ℝ} (ha : 0 < a) (hb : b ≠ 0)
    (hdom : |Δω + b * ξ| < a) :
    -Real.sin (slowAngle a b Δω ξ) = -(b / a) * (ξ - (-Δω / b)) := by
  have hx : |(Δω + b * ξ) / a| < 1 := by rw [abs_div, abs_of_pos ha, div_lt_one ha]; exact hdom
  have hx' := abs_lt.mp hx
  rw [slowAngle, Real.sin_arcsin hx'.1.le hx'.2.le]
  field_simp
  ring

/-- The reduced equilibrium `ξ* = −Δω/b` lies in the slow-manifold domain, with `θ* = 0`. -/
@[powerlib_foundation] theorem reduced_equilibrium_mem {a b Δω : ℝ} (ha : 0 < a) (hb : b ≠ 0) :
    |Δω + b * (-Δω / b)| < a ∧ slowAngle a b Δω (-Δω / b) = 0 := by
  have h0 : Δω + b * (-Δω / b) = 0 := by field_simp; ring
  refine ⟨by rw [h0, abs_zero]; exact ha, ?_⟩
  rw [slowAngle, h0, zero_div, Real.arcsin_zero]

/-- The state matrix `[−(b/a)]` of the shifted reduced slow model `ẏ = −(b/a) y`
(`y = ξ − ξ*`). -/
def reducedA (a b : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := !![-(b / a)]

/-- The reduced slow model is Hurwitz iff `b/a > 0`. -/
@[powerlib_foundation] theorem isHurwitz_reducedA_iff (a b : ℝ) :
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

/-- The reduced slow family: every model read as its autonomous one-state field. -/
def family : Family Model Requirement 1 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-- The whole requirement language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : 0 < m.b / m.a := h .positiveRatio
  have h2 : m.b / m.a < 0 := h .negativeRatio
  linarith

private theorem mem_den_hurwitz {m : Model} {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    m ∈ family.den (.flow P) ↔ 0 < m.b / m.a := by
  rw [family_isAutonomous.mem_den_flow, ← isHurwitz_reducedA_iff]
  rcases hP with hP | rfl
  · exact Linear.holds_iff_isHurwitz 0 hP
  · exact Linear.sampledContraction_iff_isHurwitz 0

/-- Every translation of the reduced slow family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · cases P
    case lyapunovStable =>
      refine family_isAutonomous.mem_den_flow.mpr (Linear.lyapunovStable_of_isHurwitz 0 ?_)
      exact (isHurwitz_reducedA_iff _ _).mpr (hm .positiveRatio rfl)
    case unstable =>
      have hneg : m.b / m.a < 0 := hm .negativeRatio rfl
      refine family_isAutonomous.mem_den_flow.mpr
        (Linear.unstable_of_root (s := ((-(m.b / m.a) : ℝ) : ℂ)) 0 ?_ ?_)
      · simp [Linear.characteristicMatrix, reducedA, Matrix.det_unique]
      · simpa using hneg
    case decay a => exact (hnone fun q => hm q trivial).elim
    case conservative => exact (hnone fun q => hm q trivial).elim
    case contractive => exact (mem_den_hurwitz (Or.inr rfl)).mpr (hm .positiveRatio rfl)
    all_goals
      refine (mem_den_hurwitz (Or.inl ?_)).mpr (hm .positiveRatio rfl)
      trivial
  · rw [family_isAutonomous.den_passive]
    trivial

/-- On the attractive sentences and sampled contraction the chain agrees with the semantics. -/
@[powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
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
  rw [mem_den_hurwitz hP]
  simp [Meets]

/-- The reduced slow model is globally exponentially stable iff `b/a > 0`. -/
@[powerlib_domain] theorem mem_den_globallyExponentiallyStable_iff (m : Model) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable) ↔
      m ∈ {m : Model | 0 < m.b / m.a}) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_hurwitz (Or.inl Flow.Property.attractive_globallyExponentiallyStable)]
  rfl

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

end ReducedSlow

/-! ## Eigenvalues and the overdamping parameter -/

/-- `ε_od = b/a² = 1/(4ζ²)` with `ζ = a/(2√b)` (`a = V K_p`, `b = V K_i > 0`, `a ≠ 0`). -/
@[powerlib_foundation] theorem epsOd_eq {V Kp Ki : ℝ} (ha : V * Kp ≠ 0) (hb : 0 < V * Ki) :
    V * Ki / (V * Kp) ^ 2 = 1 / (4 * zeta V Kp Ki ^ 2) := by
  have hsq : omegaN V Ki ^ 2 = V * Ki := Real.sq_sqrt hb.le
  have h2 : (2 * omegaN V Ki) ^ 2 = 4 * (V * Ki) := by rw [mul_pow, hsq]; norm_num
  have ha2 : (V * Kp) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  rw [zeta, div_pow, h2]
  field_simp

end powerlib.PLL
