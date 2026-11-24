import theorem.Grid.PowerFlow
import theorem.Criteria.Hurwitz
import theorem.Spectral.Family
import theorem.Dynamics.Coordinates
import theorem.Dynamics.Shift
import theorem.SpecialFunctions.PolynomialSigns
import theorem.SpecialFunctions.TrigZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Grid-forming converter with Q–V droop: equilibria, the droop quartic, the descending branch

Domain module.

Model boundary.
* The reduced (quasi-static line) grid-forming converter with reactive-power–voltage droop: an
  internal EMF `E ∠ δ` behind the series branch `Z = R + jX` (`Passive.SeriesRLC ⟨R, X, 0⟩` at
  the per-unit grid frequency `ω = 1`, `|Z|² = R² + X²`, `QVDroop.zsq`) to a stiff grid `V ∠ 0`,
  in a dq frame rotating at the nominal frequency. The line current is quasi-steady,
  `Ī = (Ē − V)/Z`, positive out of the converter; the active and reactive power at the EMF are the
  line powers `P(δ, E) = Grid.lineP`, `Q(δ, E) = Grid.lineQ` (`Grid.linePower`: `P + jQ = Ē Ī*`),
  export-positive (GFM family exception, as in `theorem/GridTiedConverter/GFM/VSMLPF.lean`;
  `Q > 0` is reactive power delivered by the converter).
* State `x = (δ, Δω, Q_f) : Dynamics.State 3`, in this order: EMF angle relative to the grid
  (rad), frequency deviation (rad/s), filtered reactive power (pu). Continuous time, autonomous,
  constant set-points `P_ref`, `Q_ref`, `E₀` (no input):
  `δ̇ = Δω`, `M Δω̇ = P_ref − P(δ, E) − D Δω`, `Q̇_f = ω_q (Q(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)` (`QVDroop.field`, `QVDroop.emf`); the active power is not filtered.
* Parameters are free reals; every theorem lists its range. The physical range is `M > 0`,
  `ω_q > 0`, droop gain `n_q > 0`, `X > 0`, `V > 0` and a positive no-load droop level
  `E₀ + n_q Q_ref > 0`; `R` and `D` are arbitrary unless stated. The formal model admits an EMF of
  either sign; equilibria with `E > 0` are the physical ones.
* Level: the equilibrium set, its count per period window `[a, a + 2π)` of the angle, the
  Jacobian at an equilibrium, the shape of the quasi-static characteristic and the instability of
  an equilibrium. Excluded: the active-power filter (`VSMLPF`), line dynamics, inner voltage and
  current loops, virtual impedance (the terminal-measured variant is
  `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`), current limiting, PLL, delay,
  PWM.

Source: study note GFM equilibrium counting (topic t6 (b): the elimination, the droop quartic and
its sign pattern, the parity, `det J`, the descending branch and the one maximum and one minimum
of `P̃` per period; checked numerically there, derived here); Descartes' rule of signs (Mathlib
`Polynomial.roots_countP_pos_le_signVariations`, read through
`theorem/SpecialFunctions/PolynomialSigns.lean`); injectivity of `θ ↦ e^{jθ}` on a window
(`SpecialFunctions.injOn_cexp_mul_I_Ico`, `theorem/SpecialFunctions/TrigZeros.lean`).

Results.
* Elimination (`balance_iff`): with `u = E V cos δ`, `w = E V sin δ` both `P` and `Q` are affine
  in `(u, w)`; the power balance `P = P_ref` and the droop `Q = Q_ref + (E₀ − E)/n_q` (`qOf`) hold
  iff `E V cos δ = u(E) = E² + β E − γ` and `E V sin δ = w(E) = ρ E + κ` (`u`, `w`), with
  `β = X/n_q`, `ρ = R/n_q`, `q₀ = E₀/n_q + Q_ref`, `γ = R P_ref + X q₀`, `κ = X P_ref − R q₀`.
* The droop quartic `f(E) = u(E)² + w(E)² − V² E²` (`quartic`, `eval_quartic`) has the
  coefficients `(1, 2β, β² − 2γ + ρ² − V², 2(ρκ − βγ), γ² + κ²)` (`quartic_eq`), degree four
  (`natDegree_quartic`) and `f(0) = γ² + κ² = |Z|² (P_ref² + q₀²)` (`eval_zero_quartic`).
* Equilibria and roots: the EMF of every equilibrium is a root of `f`
  (`quartic_isRoot_of_field_eq_zero`); at a nonzero EMF the balance fixes the angle in a window
  (`eq_of_balance`); in every window the equilibria whose EMF lies in a set `T ∌ 0` are as many as
  the roots of `f` in `T` (`ncard_equilibriaWindow`, a bijection through the EMF, `V ≠ 0`).
* At most two physical equilibria per window (`ncard_physical_le_two`): the coefficients of `f`
  have the sign pattern `(+, +, ?, ?, ≥ 0)` (`countP_pos_roots_le_two`, through
  `SpecialFunctions.countP_pos_roots_le_two_of_quartic`). Parity: in the physical range
  `f(0) > 0` (`eval_zero_quartic_pos`) and the positive roots counted with multiplicity are even
  (`even_countP_pos_roots`, `SpecialFunctions.even_countP_pos_roots_iff`), so `0` or `2`
  (`countP_pos_roots_eq_zero_or_two`); a single physical equilibrium in a window has a double
  root of `f` as its EMF, the fold of the physical branch
  (`rootMultiplicity_eq_two_of_ncard_eq_one`).
* Linearization, derived by `fderiv` (`hasFDerivAt_field`): the Jacobian `jacobian δ E` at a point
  with angle `δ` and EMF `E` has the entries `P_δ, P_E, Q_δ, Q_E` (`Pδ`, `PE`, `Qδ`, `QE`), the
  pointwise partial derivatives of `P` and `Q` (`hasDerivAt_Pδ`, `hasDerivAt_PE`, `hasDerivAt_Qδ`,
  `hasDerivAt_QE`), and `det J = −(ω_q/M) ((1 + n_q Q_E) P_δ − n_q P_E Q_δ)` (`det_jacobian`).
* The physical droop branch: for `n_q X > 0` and `E₀ + n_q Q_ref > 0` the droop equation
  `E = E₀ − n_q (Q(δ, E) − Q_ref)` is the quadratic `a₂ E² + a₁(δ) E + a₀ = 0` (`droop_eq`) with
  exactly one positive root `E₊(δ)` (`Eplus`, `droop_Eplus`, `Eplus_pos`, `eq_Eplus`), every
  physical equilibrium has this EMF (`emf_eq_Eplus`), and along the branch
  `1 + n_q Q_E = √disc > 0` (`one_add_nq_QE_Eplus`). The quasi-static characteristic
  `P̃(δ) = P(δ, E₊(δ))` (`Ptilde`) has the slope `P̃' = P_δ − P_E n_q Q_δ / (1 + n_q Q_E)`
  (`hasDerivAt_Ptilde`, implicit differentiation of the droop) and on the branch
  `det J = −(ω_q/M) (1 + n_q Q_E) P̃'` (`det_jacobian_eq_slope`).
* The shape of `P̃` (physical range, `V ≠ 0`): continuous and `2π`-periodic (`continuous_Ptilde`,
  `Ptilde_periodic`), no level is met three times within one period (`Ptilde_not_three`: three
  such angles would be three physical equilibria at `P_ref` equal to that level, `Q_Eplus`), hence
  exactly one local maximum and exactly one local minimum per window
  (`existsUnique_isLocalMax_Ptilde`, `existsUnique_isLocalMin_Ptilde`, through
  `SpecialFunctions.existsUnique_isLocalMax_of_levels`).

Family and connection conclusions.
* `QVDroop.family`: a complete system (`QVDroop.Model`) is a parameter set with a selected point
  `(δ*, 0, Q_f*)`, read as the field translated so that the point is the origin
  (`Flow.Property.holds_shift_iff`). It is the local spectral family `Spectral.localFamily` whose
  stability condition is an equilibrium at the point with a Hurwitz Jacobian (`Model.Stable`) and
  whose instability condition is an equilibrium with `det J > 0` (`Model.Saddle`).
  `QVDroop.chain_le_semantics` proves every translation sound (converse linearization,
  `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`; a positive real eigenvalue,
  `Criteria.unstable_of_jacobian_det`).
* Connection conclusion: `QVDroop.mem_den_unstable_of_slope_neg` — in the physical range a
  physical equilibrium on the descending part of the quasi-static characteristic (`P̃'(δ*) < 0`)
  is unstable, for every damping `D`.
* Static evidence on the model: the elimination, the quartic, the window bijection and the counts,
  the parity and fold statements, the Jacobian and the branch identities, the shape of `P̃`.

Corrections and limits (study note, topic t6 (b)).
* The bound of four zeros per period of a second-order trigonometric polynomial
  (`theorem/SpecialFunctions/TrigZeros.lean`, used by `theorem/GridTiedConverter/PLL/TrigPD.lean`)
  is not the physical count here: the Q–V droop GFM has at most two physical equilibria per period
  (`ncard_physical_le_two`).
* Not formalized (observations of the study only): that the ascending-branch equilibria
  (`P̃' > 0`) were Hurwitz in the sampled cases, and that no sampled `E < 0` equilibrium was.
-/

noncomputable section
namespace powerlib.GFM
open Real Set Polynomial
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)

/-- Parameters of the reduced grid-forming converter with Q–V droop. -/
structure QVDroop where
  /-- Virtual inertia `M`. -/
  M : ℝ
  /-- Damping `D`. -/
  D : ℝ
  /-- Bandwidth `ω_q` of the reactive-power filter. -/
  ωq : ℝ
  /-- Q–V droop gain `n_q`. -/
  nq : ℝ
  /-- No-load EMF set-point `E₀`. -/
  E0 : ℝ
  /-- Reactive-power set-point `Q_ref`. -/
  Qref : ℝ
  /-- Active-power set-point `P_ref`. -/
  Pref : ℝ
  /-- Grid voltage magnitude `V`. -/
  V : ℝ
  /-- Line resistance `R`. -/
  R : ℝ
  /-- Line reactance `X`. -/
  X : ℝ

namespace QVDroop

variable (q : QVDroop)

/-! ## Line powers and the closed-loop field -/

/-- The line as a series R–L branch, evaluated at the per-unit grid frequency `ω = 1`. -/
def line : Passive.SeriesRLC := ⟨q.R, q.X, 0⟩

/-- Active power at the EMF `E ∠ δ` (`Grid.lineP`, export-positive). -/
def P (δ E : ℝ) : ℝ := Grid.lineP q.V q.line 1 δ E

/-- Reactive power at the EMF `E ∠ δ` (`Grid.lineQ`, export-positive). -/
def Q (δ E : ℝ) : ℝ := Grid.lineQ q.V q.line 1 δ E

/-- `|Z|² = R² + X²`. -/
def zsq : ℝ := q.R ^ 2 + q.X ^ 2

@[tmio M, powerlib_domain] theorem P_eq (δ E : ℝ) :
    q.P δ E = (q.R * (E ^ 2 - E * q.V * cos δ) + q.X * (E * q.V * sin δ)) / q.zsq := by
  simp only [P, Grid.lineP, line, Passive.SeriesRLC.reactance, Passive.SeriesRLC.absSq, zsq,
    one_mul, zero_div, sub_zero]
  ring

@[tmio M, powerlib_domain] theorem Q_eq (δ E : ℝ) :
    q.Q δ E = (q.X * (E ^ 2 - E * q.V * cos δ) - q.R * (E * q.V * sin δ)) / q.zsq := by
  simp only [Q, Grid.lineQ, line, Passive.SeriesRLC.reactance, Passive.SeriesRLC.absSq, zsq,
    one_mul, zero_div, sub_zero]
  ring

@[tmio M, powerlib_domain] theorem zsq_pos (hX : q.X ≠ 0) : 0 < q.zsq := by
  have := sq_pos_of_ne_zero hX
  unfold zsq
  positivity

/-- The EMF set by the droop, `E = E₀ − n_q (Q_f − Q_ref)`. -/
def emf (Qf : ℝ) : ℝ := q.E0 - q.nq * (Qf - q.Qref)

/-- The filtered reactive power that the droop maps to the EMF `E`, `Q_ref + (E₀ − E)/n_q`. -/
def qOf (E : ℝ) : ℝ := q.Qref + (q.E0 - E) / q.nq

@[tmio M, powerlib_domain] theorem emf_qOf (hnq : q.nq ≠ 0) (E : ℝ) : q.emf (q.qOf E) = E := by
  have h : q.nq * ((q.E0 - E) / q.nq) = q.E0 - E := by field_simp
  simp only [emf, qOf]
  linear_combination -h

@[tmio M, powerlib_domain] theorem qOf_emf (hnq : q.nq ≠ 0) (Qf : ℝ) : q.qOf (q.emf Qf) = Qf := by
  have h : q.nq * (Qf - q.Qref) / q.nq = Qf - q.Qref := by field_simp
  simp only [emf, qOf, sub_sub_cancel]
  linear_combination h

/-- The closed-loop vector field on `(δ, Δω, Q_f)`. -/
def field (x : State 3) : State 3 :=
  mk3 (x 1) ((q.Pref - q.P (x 0) (q.emf (x 2)) - q.D * x 1) / q.M)
    (q.ωq * (q.Q (x 0) (q.emf (x 2)) - x 2))

@[tmio M, simp, powerlib_domain] theorem field_apply_zero (x : State 3) : q.field x 0 = x 1 := by
  simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_one (x : State 3) :
    q.field x 1 = (q.Pref - q.P (x 0) (q.emf (x 2)) - q.D * x 1) / q.M := by simp [field]

@[tmio M, simp, powerlib_domain] theorem field_apply_two (x : State 3) :
    q.field x 2 = q.ωq * (q.Q (x 0) (q.emf (x 2)) - x 2) := by simp [field]

/-- Equilibria: `Δω = 0`, power balance `P(δ, E) = P_ref` and a settled filter `Q(δ, E) = Q_f`,
`E = E₀ − n_q (Q_f − Q_ref)`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (x : State 3) :
    q.field x = 0 ↔
      x 1 = 0 ∧ q.P (x 0) (q.emf (x 2)) = q.Pref ∧ q.Q (x 0) (q.emf (x 2)) = x 2 := by
  constructor
  · intro h
    have e1 := congrArg (fun y : State 3 => y 0) h
    have e2 := congrArg (fun y : State 3 => y 1) h
    have e3 := congrArg (fun y : State 3 => y 2) h
    simp only [field_apply_zero, field_apply_one, field_apply_two, PiLp.zero_apply] at e1 e2 e3
    rw [e1, mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM, sub_eq_zero] at e2
    rw [mul_eq_zero, or_iff_right hω, sub_eq_zero] at e3
    exact ⟨e1, e2.symm, e3⟩
  · rintro ⟨h1, h2, h3⟩
    apply state3_ext <;> simp [h1, h2, h3]

@[tmio M, powerlib_domain] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k q.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa using Dynamics.contDiff_coord (k := k) 1
  · simp only [Fin.mk_one, Fin.isValue, field_apply_one, P_eq, emf]; fun_prop
  · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two, Q_eq, emf]; fun_prop

/-! ## Elimination and the droop quartic -/

/-- `β = X/n_q`. -/
def β : ℝ := q.X / q.nq

/-- `ρ = R/n_q`. -/
def ρ : ℝ := q.R / q.nq

/-- `q₀ = E₀/n_q + Q_ref`. -/
def q0 : ℝ := q.E0 / q.nq + q.Qref

/-- `γ = R P_ref + X q₀`. -/
def γ : ℝ := q.R * q.Pref + q.X * q.q0

/-- `κ = X P_ref − R q₀`. -/
def κ : ℝ := q.X * q.Pref - q.R * q.q0

/-- `u(E) = E² + β E − γ`, the value of `E V cos δ` at a balanced point. -/
def u (E : ℝ) : ℝ := E ^ 2 + q.β * E - q.γ

/-- `w(E) = ρ E + κ`, the value of `E V sin δ` at a balanced point. -/
def w (E : ℝ) : ℝ := q.ρ * E + q.κ

/-- Elimination: the power balance `P(δ, E) = P_ref` and the droop `Q(δ, E) = Q_ref + (E₀ − E)/n_q`
hold iff `E V cos δ = u(E)` and `E V sin δ = w(E)` (`|Z| ≠ 0`; the map `(E V cos δ, E V sin δ) ↦
(P, Q)` is affine with determinant `1/|Z|²`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem balance_iff (hZ : q.zsq ≠ 0) (δ E : ℝ) :
    q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E ↔
      E * q.V * cos δ = q.u E ∧ E * q.V * sin δ = q.w E := by
  rw [P_eq, Q_eq, div_eq_iff hZ, div_eq_iff hZ]
  generalize E * q.V * cos δ = c
  generalize E * q.V * sin δ = s
  simp only [u, w, β, ρ, γ, κ, q0, qOf]
  constructor
  · rintro ⟨h1, h2⟩
    have k1 : q.zsq * (c - (E ^ 2 + q.X / q.nq * E -
        (q.R * q.Pref + q.X * (q.E0 / q.nq + q.Qref)))) = 0 := by
      simp only [zsq] at h1 h2 ⊢
      linear_combination (-q.R) * h1 - q.X * h2
    have k2 : q.zsq * (s - (q.R / q.nq * E + (q.X * q.Pref - q.R * (q.E0 / q.nq + q.Qref)))) =
        0 := by
      simp only [zsq] at h1 h2 ⊢
      linear_combination q.X * h1 - q.R * h2
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp k1).resolve_left hZ),
      sub_eq_zero.mp ((mul_eq_zero.mp k2).resolve_left hZ)⟩
  · rintro ⟨rfl, rfl⟩
    simp only [zsq]
    constructor <;> ring

/-- The droop quartic `f(E) = u(E)² + w(E)² − V² E²`. -/
def quartic : ℝ[X] :=
  (Polynomial.X ^ 2 + C q.β * Polynomial.X - C q.γ) ^ 2 + (C q.ρ * Polynomial.X + C q.κ) ^ 2 -
    C (q.V ^ 2) * Polynomial.X ^ 2

@[tmio M, powerlib_domain] theorem eval_quartic (E : ℝ) :
    q.quartic.eval E = q.u E ^ 2 + q.w E ^ 2 - q.V ^ 2 * E ^ 2 := by
  simp only [quartic, eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X, u, w]

/-- The coefficients of the droop quartic: `(1, 2β, β² − 2γ + ρ² − V², 2(ρκ − βγ), γ² + κ²)`. -/
@[tmio M, powerlib_domain] theorem quartic_eq :
    q.quartic = C 1 * Polynomial.X ^ 4 + C (2 * q.β) * Polynomial.X ^ 3 +
      C (q.β ^ 2 - 2 * q.γ + q.ρ ^ 2 - q.V ^ 2) * Polynomial.X ^ 2 +
      C (2 * (q.ρ * q.κ - q.β * q.γ)) * Polynomial.X + C (q.γ ^ 2 + q.κ ^ 2) := by
  simp only [quartic, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  ring

@[tmio M, powerlib_domain] theorem natDegree_quartic : q.quartic.natDegree = 4 := by
  rw [quartic_eq]
  compute_degree!

@[tmio M, powerlib_domain] theorem quartic_ne_zero : q.quartic ≠ 0 := by
  intro h
  have := q.natDegree_quartic
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

@[tmio M, powerlib_domain] theorem leadingCoeff_quartic : q.quartic.leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_quartic, quartic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- `f(0) = γ² + κ² = |Z|² (P_ref² + q₀²)`. -/
@[tmio M, powerlib_domain] theorem eval_zero_quartic :
    q.quartic.eval 0 = q.zsq * (q.Pref ^ 2 + q.q0 ^ 2) := by
  rw [eval_quartic]
  simp only [u, w, γ, κ, zsq]
  ring

/-- The EMF of a balanced point is a root of the droop quartic.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem quartic_isRoot_of_balance (hZ : q.zsq ≠ 0) {δ E : ℝ}
    (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) : q.quartic.IsRoot E := by
  obtain ⟨hc, hs⟩ := (q.balance_iff hZ δ E).mp h
  rw [IsRoot.def, eval_quartic, ← hc, ← hs]
  linear_combination (E * q.V) ^ 2 * Real.sin_sq_add_cos_sq δ

/-- The EMF of every equilibrium is a root of the droop quartic.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem quartic_isRoot_of_field_eq_zero (hM : q.M ≠ 0)
    (hω : q.ωq ≠ 0) (hnq : q.nq ≠ 0) (hZ : q.zsq ≠ 0) {x : State 3} (hx : q.field x = 0) :
    q.quartic.IsRoot (q.emf (x 2)) := by
  obtain ⟨-, h1, h2⟩ := (q.field_eq_zero_iff hM hω x).mp hx
  exact q.quartic_isRoot_of_balance hZ ⟨h1, by rw [h2, q.qOf_emf hnq]⟩

/-! ## Counting per period window -/

/-- Every point `(c, s)` of the unit circle is `(cos θ, sin θ)` for an angle `θ` of each window. -/
@[tmio T, powerlib_foundation] private theorem exists_cos_sin_window (a : ℝ) {c s : ℝ}
    (h : c ^ 2 + s ^ 2 = 1) : ∃ θ ∈ Ico a (a + 2 * π), cos θ = c ∧ sin θ = s := by
  have hn : ‖(⟨c, s⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, show c * c + s * s = 1 by linear_combination h,
      Real.sqrt_one]
  have hz0 : (⟨c, s⟩ : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨n, hn'⟩ : ∃ n : ℤ, toIcoMod two_pi_pos a (Complex.arg ⟨c, s⟩) =
      Complex.arg ⟨c, s⟩ - n * (2 * π) := by
    refine ⟨toIcoDiv two_pi_pos a (Complex.arg ⟨c, s⟩), ?_⟩
    have := self_sub_toIcoMod two_pi_pos a (Complex.arg ⟨c, s⟩)
    rw [zsmul_eq_mul] at this
    linarith
  refine ⟨toIcoMod two_pi_pos a (Complex.arg ⟨c, s⟩), toIcoMod_mem_Ico _ _ _, ?_, ?_⟩
  · rw [hn', Real.cos_sub_int_mul_two_pi, Complex.cos_arg hz0, hn, div_one]
  · rw [hn', Real.sin_sub_int_mul_two_pi, Complex.sin_arg, hn, div_one]

/-- At a nonzero EMF the balance fixes the angle in a window: `E V cos δ = u(E)` and
`E V sin δ = w(E)` (`balance_iff`) fix `e^{jδ}`, injective on `[a, a + 2π)` (`V ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem eq_of_balance (hZ : q.zsq ≠ 0) (hV : q.V ≠ 0)
    {a δ₁ δ₂ E : ℝ} (hE : E ≠ 0) (h₁ : δ₁ ∈ Ico a (a + 2 * π)) (h₂ : δ₂ ∈ Ico a (a + 2 * π))
    (hb₁ : q.P δ₁ E = q.Pref ∧ q.Q δ₁ E = q.qOf E)
    (hb₂ : q.P δ₂ E = q.Pref ∧ q.Q δ₂ E = q.qOf E) : δ₁ = δ₂ := by
  obtain ⟨hc₁, hs₁⟩ := (q.balance_iff hZ δ₁ E).mp hb₁
  obtain ⟨hc₂, hs₂⟩ := (q.balance_iff hZ δ₂ E).mp hb₂
  have hEV : E * q.V ≠ 0 := mul_ne_zero hE hV
  have hc : cos δ₁ = cos δ₂ := mul_left_cancel₀ hEV (hc₁.trans hc₂.symm)
  have hs : sin δ₁ = sin δ₂ := mul_left_cancel₀ hEV (hs₁.trans hs₂.symm)
  exact SpecialFunctions.injOn_cexp_mul_I_Ico a h₁ h₂ (Complex.ext (by simp [hc]) (by simp [hs]))

/-- The equilibria with angle in the window `[a, a + 2π)` and EMF in `T`. -/
def equilibriaWindow (T : Set ℝ) (a : ℝ) : Set (State 3) :=
  {x | q.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π) ∧ q.emf (x 2) ∈ T}

/-- Counting law: in every window `[a, a + 2π)` the equilibria with EMF in a set `T ∌ 0` are as
many as the roots of the droop quartic in `T` (the EMF is a bijection; `V ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem ncard_equilibriaWindow (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (hnq : q.nq ≠ 0) (hZ : q.zsq ≠ 0) (hV : q.V ≠ 0) {T : Set ℝ} (hT : (0 : ℝ) ∉ T)
    (a : ℝ) :
    (q.equilibriaWindow T a).ncard = {E | E ∈ T ∧ q.quartic.IsRoot E}.ncard := by
  have hbal : ∀ x, q.field x = 0 → q.P (x 0) (q.emf (x 2)) = q.Pref ∧
      q.Q (x 0) (q.emf (x 2)) = q.qOf (q.emf (x 2)) := by
    intro x hx
    obtain ⟨-, h1, h2⟩ := (q.field_eq_zero_iff hM hω x).mp hx
    exact ⟨h1, by rw [h2, q.qOf_emf hnq]⟩
  refine Set.ncard_congr (fun x _ => q.emf (x 2))
    (fun x hx => ⟨hx.2.2, q.quartic_isRoot_of_balance hZ (hbal x hx.1)⟩) ?_ ?_
  · rintro x y ⟨hx, hxw, hxT⟩ ⟨hy, hyw, -⟩ hxy
    have hE0 : q.emf (x 2) ≠ 0 := fun h => hT (h ▸ hxT)
    have hby := hbal y hy
    rw [← hxy] at hby
    refine state3_ext (q.eq_of_balance hZ hV hE0 hxw hyw (hbal x hx) hby) ?_ ?_
    · rw [((q.field_eq_zero_iff hM hω x).mp hx).1, ((q.field_eq_zero_iff hM hω y).mp hy).1]
    · rw [← q.qOf_emf hnq (x 2), ← q.qOf_emf hnq (y 2), hxy]
  · rintro E ⟨hET, hroot⟩
    have hE0 : E ≠ 0 := fun h => hT (h ▸ hET)
    have hEV : E * q.V ≠ 0 := mul_ne_zero hE0 hV
    have hsum : q.u E ^ 2 + q.w E ^ 2 = (E * q.V) ^ 2 := by
      rw [IsRoot.def, eval_quartic] at hroot
      linear_combination hroot
    obtain ⟨θ, hθ, hc, hs⟩ := exists_cos_sin_window a (c := q.u E / (E * q.V))
      (s := q.w E / (E * q.V))
      (by rw [div_pow, div_pow, ← add_div, hsum, div_self (pow_ne_zero 2 hEV)])
    have hx2 : q.emf ((mk3 θ 0 (q.qOf E)) 2) = E := by rw [mk3_two, q.emf_qOf hnq]
    refine ⟨mk3 θ 0 (q.qOf E), ⟨(q.field_eq_zero_iff hM hω _).mpr ⟨mk3_one _ _ _, ?_⟩,
      by rwa [mk3_zero], by rwa [hx2]⟩, hx2⟩
    rw [hx2, mk3_zero, mk3_two]
    refine (q.balance_iff hZ θ E).mpr ⟨?_, ?_⟩
    · rw [hc]; field_simp
    · rw [hs]; field_simp

/-- The positive roots of the droop quartic, counted with multiplicity, are at most two when
`n_q > 0` and `X > 0`: its coefficient list has the sign pattern `(+, +, ?, ?, ≥ 0)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem countP_pos_roots_le_two (hnq : 0 < q.nq) (hX : 0 < q.X) :
    q.quartic.roots.countP (0 < ·) ≤ 2 := by
  rw [quartic_eq]
  exact SpecialFunctions.countP_pos_roots_le_two_of_quartic one_pos
    (mul_nonneg zero_le_two (div_pos hX hnq).le) (by positivity)

/-- At most two physical equilibria (`E > 0`) in every window `[a, a + 2π)` (`n_q > 0`, `X > 0`,
`V ≠ 0`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem ncard_physical_le_two (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (hnq : 0 < q.nq) (hX : 0 < q.X) (hV : q.V ≠ 0) (a : ℝ) :
    (q.equilibriaWindow (Ioi 0) a).ncard ≤ 2 := by
  rw [q.ncard_equilibriaWindow hM hω hnq.ne' (q.zsq_pos hX.ne').ne' hV (by simp) a]
  exact (SpecialFunctions.ncard_pos_isRoot_le_countP q.quartic_ne_zero).trans
    (q.countP_pos_roots_le_two hnq hX)

/-- In the physical range `f(0) = |Z|² (P_ref² + q₀²) > 0` (`q₀ = (E₀ + n_q Q_ref)/n_q > 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem eval_zero_quartic_pos (hnq : 0 < q.nq) (hX : 0 < q.X)
    (hc : 0 < q.E0 + q.nq * q.Qref) : 0 < q.quartic.eval 0 := by
  rw [eval_zero_quartic]
  have hq : q.q0 * q.nq = q.E0 + q.nq * q.Qref := by
    simp only [q0, add_mul, div_mul_cancel₀ _ hnq.ne']
    ring
  have hq0 : 0 < q.q0 := by nlinarith
  exact mul_pos (q.zsq_pos hX.ne') (by positivity)

/-- Parity: in the physical range the positive roots of the droop quartic, counted with
multiplicity, are even in number (`f(0) > 0`, leading coefficient `1`;
`SpecialFunctions.even_countP_pos_roots_iff`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem even_countP_pos_roots (hnq : 0 < q.nq) (hX : 0 < q.X)
    (hc : 0 < q.E0 + q.nq * q.Qref) : Even (q.quartic.roots.countP (0 < ·)) := by
  have h0 := q.eval_zero_quartic_pos hnq hX hc
  refine (SpecialFunctions.even_countP_pos_roots_iff h0.ne').mpr ?_
  rw [leadingCoeff_quartic, one_mul]
  exact h0

/-- In the physical range the positive roots of the droop quartic, counted with multiplicity, are
`0` or `2`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem countP_pos_roots_eq_zero_or_two (hnq : 0 < q.nq)
    (hX : 0 < q.X) (hc : 0 < q.E0 + q.nq * q.Qref) :
    q.quartic.roots.countP (0 < ·) = 0 ∨ q.quartic.roots.countP (0 < ·) = 2 := by
  have h2 := q.countP_pos_roots_le_two hnq hX
  obtain ⟨k, hk⟩ := q.even_countP_pos_roots hnq hX hc
  omega

/-- The fold of the physical branch: if a window holds exactly one physical equilibrium, the
quartic has exactly one positive root and it is a double root.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem rootMultiplicity_eq_two_of_ncard_eq_one (hM : q.M ≠ 0)
    (hω : q.ωq ≠ 0) (hnq : 0 < q.nq) (hX : 0 < q.X) (hc : 0 < q.E0 + q.nq * q.Qref)
    (hV : q.V ≠ 0) (a : ℝ) (h1 : (q.equilibriaWindow (Ioi 0) a).ncard = 1) :
    ∃ E, {E' : ℝ | 0 < E' ∧ q.quartic.IsRoot E'} = {E} ∧ q.quartic.rootMultiplicity E = 2 := by
  classical
  rw [q.ncard_equilibriaWindow hM hω hnq.ne' (q.zsq_pos hX.ne').ne' hV (by simp) a] at h1
  obtain ⟨E, hE⟩ := Set.ncard_eq_one.mp h1
  have hE' : {E' : ℝ | 0 < E' ∧ q.quartic.IsRoot E'} = {E} := hE
  refine ⟨E, hE', ?_⟩
  have hEmem : 0 < E ∧ q.quartic.IsRoot E := by
    have : E ∈ ({E} : Set ℝ) := Set.mem_singleton E
    rw [← hE'] at this
    exact this
  have hpos := SpecialFunctions.ncard_pos_isRoot_le_countP q.quartic_ne_zero
  rw [hE', Set.ncard_singleton] at hpos
  have h2 : q.quartic.roots.countP (0 < ·) = 2 := by
    rcases q.countP_pos_roots_eq_zero_or_two hnq hX hc with h | h <;> omega
  rw [← count_roots, Multiset.count_eq_card_filter_eq, ← h2, Multiset.countP_eq_card_filter]
  congr 1
  refine Multiset.filter_congr fun x hx => ?_
  constructor
  · rintro rfl
    exact hEmem.1
  · intro hx0
    have : x ∈ {E' : ℝ | 0 < E' ∧ q.quartic.IsRoot E'} :=
      ⟨hx0, (mem_roots q.quartic_ne_zero).mp hx⟩
    rw [hE'] at this
    exact (Set.mem_singleton_iff.mp this).symm

/-! ## Linearization -/

/-- `∂P/∂δ` at `(δ, E)`. -/
def Pδ (δ E : ℝ) : ℝ := (q.R * (E * q.V * sin δ) + q.X * (E * q.V * cos δ)) / q.zsq

/-- `∂P/∂E` at `(δ, E)`. -/
def PE (δ E : ℝ) : ℝ := (q.R * (2 * E - q.V * cos δ) + q.X * (q.V * sin δ)) / q.zsq

/-- `∂Q/∂δ` at `(δ, E)`. -/
def Qδ (δ E : ℝ) : ℝ := (q.X * (E * q.V * sin δ) - q.R * (E * q.V * cos δ)) / q.zsq

/-- `∂Q/∂E` at `(δ, E)`. -/
def QE (δ E : ℝ) : ℝ := (q.X * (2 * E - q.V * cos δ) - q.R * (q.V * sin δ)) / q.zsq

/-- `P_δ` is the partial derivative of `P` in the angle at `(δ, E)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_Pδ (δ E : ℝ) :
    HasDerivAt (fun d => q.P d E) (q.Pδ δ E) δ := by
  have h := (((((Real.hasDerivAt_cos δ).const_mul (E * q.V)).const_sub (E ^ 2)).const_mul
    q.R).add ((Real.hasDerivAt_sin δ).const_mul (q.X * (E * q.V)))).div_const q.zsq
  convert h using 1
  · funext d
    simp only [P_eq, Pi.add_apply]
    ring
  · simp only [Pδ]
    ring

/-- `P_E` is the partial derivative of `P` in the EMF at `(δ, E)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_PE (δ E : ℝ) :
    HasDerivAt (fun e => q.P δ e) (q.PE δ E) E := by
  have h := (((((hasDerivAt_id E).pow 2).sub ((hasDerivAt_id E).mul_const (q.V * cos δ))).const_mul
    q.R).add (((hasDerivAt_id E).mul_const (q.V * sin δ)).const_mul q.X)).div_const q.zsq
  convert h using 1
  · funext e
    simp only [P_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id]
    ring
  · simp only [PE, id]
    ring

/-- `Q_δ` is the partial derivative of `Q` in the angle at `(δ, E)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_Qδ (δ E : ℝ) :
    HasDerivAt (fun d => q.Q d E) (q.Qδ δ E) δ := by
  have h := (((((Real.hasDerivAt_cos δ).const_mul (E * q.V)).const_sub (E ^ 2)).const_mul
    q.X).sub ((Real.hasDerivAt_sin δ).const_mul (q.R * (E * q.V)))).div_const q.zsq
  convert h using 1
  · funext d
    simp only [Q_eq, Pi.sub_apply]
    ring
  · simp only [Qδ]
    ring

/-- `Q_E` is the partial derivative of `Q` in the EMF at `(δ, E)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_QE (δ E : ℝ) :
    HasDerivAt (fun e => q.Q δ e) (q.QE δ E) E := by
  have h := (((((hasDerivAt_id E).pow 2).sub ((hasDerivAt_id E).mul_const (q.V * cos δ))).const_mul
    q.X).sub (((hasDerivAt_id E).mul_const (q.V * sin δ)).const_mul q.R)).div_const q.zsq
  convert h using 1
  · funext e
    simp only [Q_eq, Pi.sub_apply, Pi.pow_apply, id]
    ring
  · simp only [QE, id]
    ring

/-- The Jacobian at a point with angle `δ` and EMF `E`. -/
def jacobian (δ E : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0;
    -q.Pδ δ E / q.M, -q.D / q.M, q.nq * q.PE δ E / q.M;
    q.ωq * q.Qδ δ E, 0, -(q.ωq * (1 + q.nq * q.QE δ E))]

@[tmio M, powerlib_domain] theorem hasFDerivAt_field (x : State 3) :
    HasFDerivAt q.field
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (q.jacobian (x 0) (q.emf (x 2)))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hE := ((h2.sub_const q.Qref).const_mul q.nq).const_sub q.E0
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  have hEc := (hE.mul_const q.V).mul hc
  have hEs := (hE.mul_const q.V).mul hs
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, field_apply_zero]
    convert h1 using 1
    · rfl
    apply ContinuousLinearMap.ext; intro v
    simp [jacobian, toEuclideanCLM_apply3]
  · simp only [Fin.mk_one, Fin.isValue, field_apply_one]
    have hP := ((((hE.mul hE).sub hEc).const_mul q.R).add (hEs.const_mul q.X)).const_mul
      q.zsq⁻¹
    have h := (((hasFDerivAt_const q.Pref x).sub hP).sub (h1.const_mul q.D)).const_mul q.M⁻¹
    convert h using 1
    · funext y
      simp only [P_eq, emf, PiLp.proj_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Function.comp_apply]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3, Pδ, PE, emf]
      ring
  · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two]
    have hQ := ((((hE.mul hE).sub hEc).const_mul q.X).sub (hEs.const_mul q.R)).const_mul
      q.zsq⁻¹
    have h := (hQ.sub h2).const_mul q.ωq
    convert h using 1
    · funext y
      simp only [Q_eq, emf, PiLp.proj_apply, Pi.sub_apply, Pi.mul_apply,
        Function.comp_apply]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3, Qδ, QE, emf]
      ring

@[tmio M, powerlib_domain] theorem fderiv_field (x : State 3) :
    fderiv ℝ q.field x =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (q.jacobian (x 0) (q.emf (x 2))) :=
  (q.hasFDerivAt_field x).fderiv

/-- `det J = −(ω_q/M) ((1 + n_q Q_E) P_δ − n_q P_E Q_δ)`. -/
@[tmio M, powerlib_domain] theorem det_jacobian (δ E : ℝ) :
    (q.jacobian δ E).det =
      -(q.ωq / q.M) * ((1 + q.nq * q.QE δ E) * q.Pδ δ E - q.nq * q.PE δ E * q.Qδ δ E) := by
  simp [jacobian, Matrix.det_fin_three]
  ring

/-! ## The physical droop branch and the quasi-static characteristic -/

/-- Leading coefficient `a₂ = n_q X/|Z|²` of the droop quadratic. -/
def a2 : ℝ := q.nq * q.X / q.zsq

/-- Linear coefficient `a₁(δ) = 1 − n_q V (X cos δ + R sin δ)/|Z|²` of the droop quadratic. -/
def a1 (δ : ℝ) : ℝ := 1 - q.nq * q.V * (q.X * cos δ + q.R * sin δ) / q.zsq

/-- Constant coefficient `a₀ = −(E₀ + n_q Q_ref)` of the droop quadratic. -/
def a0 : ℝ := -(q.E0 + q.nq * q.Qref)

/-- Discriminant `a₁(δ)² − 4 a₂ a₀` of the droop quadratic. -/
def disc (δ : ℝ) : ℝ := q.a1 δ ^ 2 - 4 * q.a2 * q.a0

/-- The positive root `E₊(δ) = (−a₁(δ) + √disc)/(2 a₂)` of the droop quadratic (the physical
branch for `a₂ > 0 > a₀`). -/
def Eplus (δ : ℝ) : ℝ := (-q.a1 δ + √(q.disc δ)) / (2 * q.a2)

/-- The quasi-static characteristic `P̃(δ) = P(δ, E₊(δ))`. -/
def Ptilde (δ : ℝ) : ℝ := q.P δ (q.Eplus δ)

/-- The droop residual `E − (E₀ − n_q (Q(δ, E) − Q_ref))` at the unfiltered reactive power. -/
def droop (δ E : ℝ) : ℝ := E - q.emf (q.Q δ E)

@[tmio M, powerlib_domain] theorem droop_eq (δ E : ℝ) :
    q.droop δ E = q.a2 * E ^ 2 + q.a1 δ * E + q.a0 := by
  simp only [droop, emf, Q_eq, a2, a1, a0]
  ring

@[tmio M, powerlib_domain] theorem a2_pos (hnq : 0 < q.nq) (hX : 0 < q.X) : 0 < q.a2 :=
  div_pos (mul_pos hnq hX) (q.zsq_pos hX.ne')

@[tmio M, powerlib_domain] theorem a0_neg (hc : 0 < q.E0 + q.nq * q.Qref) : q.a0 < 0 :=
  neg_neg_of_pos hc

@[tmio M, powerlib_domain] theorem disc_pos (h2 : 0 < q.a2) (h0 : q.a0 < 0) (δ : ℝ) :
    0 < q.disc δ := by
  unfold disc
  nlinarith [sq_nonneg (q.a1 δ), mul_pos h2 (neg_pos.mpr h0)]

@[tmio M, powerlib_domain] theorem two_a2_Eplus (h2 : 0 < q.a2) (δ : ℝ) :
    2 * q.a2 * q.Eplus δ + q.a1 δ = √(q.disc δ) := by
  have h : 2 * q.a2 * ((-q.a1 δ + √(q.disc δ)) / (2 * q.a2)) = -q.a1 δ + √(q.disc δ) := by
    have := h2.ne'
    field_simp
  rw [Eplus, h]
  ring

/-- `E₊(δ)` solves the droop equation. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem droop_Eplus (h2 : 0 < q.a2) (h0 : q.a0 < 0) (δ : ℝ) :
    q.droop δ (q.Eplus δ) = 0 := by
  rw [droop_eq]
  have hE := q.two_a2_Eplus h2 δ
  have hs := Real.sq_sqrt (q.disc_pos h2 h0 δ).le
  have hd : q.disc δ = q.a1 δ ^ 2 - 4 * q.a2 * q.a0 := rfl
  have h4 : 4 * q.a2 * (q.a2 * q.Eplus δ ^ 2 + q.a1 δ * q.Eplus δ + q.a0) = 0 := by
    linear_combination (2 * q.a2 * q.Eplus δ + q.a1 δ + √(q.disc δ)) * hE + hs + hd
  exact (mul_eq_zero.mp h4).resolve_left (by positivity)

/-- `E₊(δ) > 0` (`a₂ > 0 > a₀`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Eplus_pos (h2 : 0 < q.a2) (h0 : q.a0 < 0) (δ : ℝ) :
    0 < q.Eplus δ := by
  have hlt : |q.a1 δ| < √(q.disc δ) := by
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
    unfold disc
    nlinarith [mul_pos h2 (neg_pos.mpr h0)]
  have := le_abs_self (q.a1 δ)
  exact div_pos (by linarith) (by linarith)

/-- `E₊(δ)` is the only positive root of the droop equation (`a₂ > 0 > a₀`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem eq_Eplus (h2 : 0 < q.a2) (h0 : q.a0 < 0) {δ E : ℝ}
    (hE : 0 < E) (hd : q.droop δ E = 0) : E = q.Eplus δ := by
  rw [droop_eq] at hd
  have hprod : (2 * q.a2 * E + q.a1 δ) * E = q.a2 * E ^ 2 - q.a0 := by linear_combination hd
  have hpos' : 0 < (2 * q.a2 * E + q.a1 δ) * E := by
    rw [hprod]
    nlinarith [sq_nonneg E]
  have hpos : 0 < 2 * q.a2 * E + q.a1 δ := by nlinarith
  have hsq : (2 * q.a2 * E + q.a1 δ) ^ 2 = q.disc δ := by
    unfold disc
    linear_combination 4 * q.a2 * hd
  have hs : √(q.disc δ) = 2 * q.a2 * E + q.a1 δ := by rw [← hsq, Real.sqrt_sq hpos.le]
  rw [Eplus, hs, eq_div_iff (by positivity)]
  ring

/-- `1 + n_q Q_E = 2 a₂ E + a₁(δ)`, the `E`-derivative of the droop residual. -/
@[tmio M, powerlib_domain] theorem one_add_nq_QE (δ E : ℝ) :
    1 + q.nq * q.QE δ E = 2 * q.a2 * E + q.a1 δ := by
  simp only [QE, a2, a1]
  ring

/-- Along the physical branch `1 + n_q Q_E = √disc > 0`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem one_add_nq_QE_Eplus (h2 : 0 < q.a2) (h0 : q.a0 < 0)
    (δ : ℝ) : 1 + q.nq * q.QE δ (q.Eplus δ) = √(q.disc δ) ∧
      0 < 1 + q.nq * q.QE δ (q.Eplus δ) := by
  rw [one_add_nq_QE, q.two_a2_Eplus h2 δ]
  exact ⟨rfl, Real.sqrt_pos.mpr (q.disc_pos h2 h0 δ)⟩

/-- Every physical equilibrium has the EMF of the physical branch, `E* = E₊(δ*)`
(`a₂ > 0 > a₀`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem emf_eq_Eplus (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (h2 : 0 < q.a2) (h0 : q.a0 < 0) {x : State 3} (hx : q.field x = 0)
    (hE : 0 < q.emf (x 2)) : q.emf (x 2) = q.Eplus (x 0) := by
  obtain ⟨-, -, h3⟩ := (q.field_eq_zero_iff hM hω x).mp hx
  refine q.eq_Eplus h2 h0 hE ?_
  rw [droop, h3, sub_self]

/-- The slope of the quasi-static characteristic (implicit differentiation of the droop along
`E₊`): `P̃'(δ) = P_δ − P_E n_q Q_δ / (1 + n_q Q_E)` at `E = E₊(δ)` (`a₂ > 0 > a₀`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_Ptilde (h2 : 0 < q.a2) (h0 : q.a0 < 0) (δ : ℝ) :
    HasDerivAt q.Ptilde (q.Pδ δ (q.Eplus δ) - q.PE δ (q.Eplus δ) * (q.nq * q.Qδ δ (q.Eplus δ)) /
      (1 + q.nq * q.QE δ (q.Eplus δ))) δ := by
  have ha1 : ∀ y, HasDerivAt q.a1 (q.nq * q.V * (q.X * sin y - q.R * cos y) / q.zsq) y := by
    intro y
    have h := (((((Real.hasDerivAt_cos y).const_mul q.X).add
      ((Real.hasDerivAt_sin y).const_mul q.R)).const_mul (q.nq * q.V)).div_const q.zsq).const_sub 1
    exact h.congr_deriv (by ring)
  have hdisc : HasDerivAt q.disc
      (2 * q.a1 δ * (q.nq * q.V * (q.X * sin δ - q.R * cos δ) / q.zsq)) δ := by
    have h := ((ha1 δ).mul (ha1 δ)).sub_const (4 * q.a2 * q.a0)
    convert h using 1
    · funext t
      simp only [disc, Pi.mul_apply]
      ring
    · ring
  obtain ⟨e', hEp⟩ : ∃ e', HasDerivAt q.Eplus e' δ :=
    ⟨_, ((ha1 δ).neg.add (hdisc.sqrt (q.disc_pos h2 h0 δ).ne')).div_const (2 * q.a2)⟩
  have hG := (((hEp.mul hEp).const_mul q.a2).add ((ha1 δ).mul hEp)).add_const q.a0
  have hG' := hG.congr_of_eventuallyEq (f₁ := fun _ => (0 : ℝ))
    (Filter.Eventually.of_forall fun t => by
      have := q.droop_Eplus h2 h0 t
      rw [droop_eq] at this
      simp only [Pi.add_apply, Pi.mul_apply]
      linear_combination -this)
  have hz := hG'.unique (hasDerivAt_const δ (0 : ℝ))
  obtain ⟨hKeq, hKpos⟩ := q.one_add_nq_QE_Eplus h2 h0 δ
  have he : e' = -(q.nq * q.Qδ δ (q.Eplus δ)) / (1 + q.nq * q.QE δ (q.Eplus δ)) := by
    rw [eq_div_iff hKpos.ne', one_add_nq_QE]
    simp only [Qδ]
    linear_combination hz
  have hP := ((((hEp.mul hEp).sub ((hEp.mul_const q.V).mul (Real.hasDerivAt_cos δ))).const_mul
    q.R).add (((hEp.mul_const q.V).mul (Real.hasDerivAt_sin δ)).const_mul q.X)).div_const q.zsq
  have hPt := hP.congr_of_eventuallyEq (f₁ := q.Ptilde) (Filter.Eventually.of_forall fun t => by
    simp only [Ptilde, P_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring)
  refine hPt.congr_deriv ?_
  rw [he]
  simp only [Pδ, PE]
  field_simp
  ring

/-- On the physical branch `det J = −(ω_q/M) (1 + n_q Q_E) P̃'` (`a₂ > 0 > a₀`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem det_jacobian_eq_slope (h2 : 0 < q.a2) (h0 : q.a0 < 0)
    (δ : ℝ) :
    (q.jacobian δ (q.Eplus δ)).det =
      -(q.ωq / q.M) * (1 + q.nq * q.QE δ (q.Eplus δ)) * deriv q.Ptilde δ := by
  have hK := (q.one_add_nq_QE_Eplus h2 h0 δ).2.ne'
  rw [(q.hasDerivAt_Ptilde h2 h0 δ).deriv, det_jacobian]
  have e : (1 + q.nq * q.QE δ (q.Eplus δ)) * (q.Pδ δ (q.Eplus δ) -
      q.PE δ (q.Eplus δ) * (q.nq * q.Qδ δ (q.Eplus δ)) / (1 + q.nq * q.QE δ (q.Eplus δ))) =
      (1 + q.nq * q.QE δ (q.Eplus δ)) * q.Pδ δ (q.Eplus δ) -
        q.nq * q.PE δ (q.Eplus δ) * q.Qδ δ (q.Eplus δ) := by
    rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hK]
    ring
  linear_combination (q.ωq / q.M) * e

/-! ## The shape of the quasi-static characteristic -/

/-- Along the physical branch the droop holds at the unfiltered reactive power,
`Q(δ, E₊(δ)) = Q_ref + (E₀ − E₊(δ))/n_q` (`droop_Eplus`). -/
@[tmio M, powerlib_domain] theorem Q_Eplus (h2 : 0 < q.a2) (h0 : q.a0 < 0) (hnq : q.nq ≠ 0)
    (δ : ℝ) : q.Q δ (q.Eplus δ) = q.qOf (q.Eplus δ) := by
  have h := q.droop_Eplus h2 h0 δ
  rw [droop, sub_eq_zero] at h
  calc q.Q δ (q.Eplus δ) = q.qOf (q.emf (q.Q δ (q.Eplus δ))) := (q.qOf_emf hnq _).symm
    _ = q.qOf (q.Eplus δ) := by rw [← h]

@[tmio M, powerlib_domain] theorem continuous_Ptilde (h2 : 0 < q.a2) (h0 : q.a0 < 0) :
    Continuous q.Ptilde :=
  continuous_iff_continuousAt.mpr fun δ => (q.hasDerivAt_Ptilde h2 h0 δ).continuousAt

@[tmio M, powerlib_domain] theorem Ptilde_periodic : Function.Periodic q.Ptilde (2 * π) := by
  intro δ
  simp only [Ptilde, Eplus, disc, a1, P_eq, cos_add_two_pi, sin_add_two_pi]

/-- No level of `P̃` is met three times within one period (physical range, `V ≠ 0`): angles
`δ₁ < δ₂ < δ₃ < δ₁ + 2π` with one value `c` of `P̃` would be three physical equilibria at
`P_ref = c` with pairwise distinct EMFs (`eq_of_balance`), three positive roots of the droop
quartic (`countP_pos_roots_le_two`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Ptilde_not_three (hnq : 0 < q.nq) (hX : 0 < q.X)
    (hc : 0 < q.E0 + q.nq * q.Qref) (hV : q.V ≠ 0) {δ₁ δ₂ δ₃ : ℝ} (h₁₂ : δ₁ < δ₂)
    (h₂₃ : δ₂ < δ₃) (h₃ : δ₃ < δ₁ + 2 * π) (e₁₂ : q.Ptilde δ₁ = q.Ptilde δ₂)
    (e₂₃ : q.Ptilde δ₂ = q.Ptilde δ₃) : False := by
  classical
  set p : QVDroop := { q with Pref := q.Ptilde δ₁ } with hp
  have h2 := q.a2_pos hnq hX
  have h0 := q.a0_neg hc
  have hZ : p.zsq ≠ 0 := (q.zsq_pos hX.ne').ne'
  have hbal : ∀ δ, q.Ptilde δ = q.Ptilde δ₁ →
      p.P δ (q.Eplus δ) = p.Pref ∧ p.Q δ (q.Eplus δ) = p.qOf (q.Eplus δ) :=
    fun δ hδ => ⟨hδ, q.Q_Eplus h2 h0 hnq.ne' δ⟩
  have b₁ := hbal δ₁ rfl
  have b₂ := hbal δ₂ e₁₂.symm
  have b₃ := hbal δ₃ (e₂₃.symm.trans e₁₂.symm)
  have hmem : ∀ δ, δ₁ ≤ δ → δ < δ₁ + 2 * π → δ ∈ Ico δ₁ (δ₁ + 2 * π) := fun δ h h' => ⟨h, h'⟩
  have hne : ∀ {d d'}, d ∈ Ico δ₁ (δ₁ + 2 * π) → d' ∈ Ico δ₁ (δ₁ + 2 * π) → d ≠ d' →
      p.P d (q.Eplus d) = p.Pref ∧ p.Q d (q.Eplus d) = p.qOf (q.Eplus d) →
      p.P d' (q.Eplus d') = p.Pref ∧ p.Q d' (q.Eplus d') = p.qOf (q.Eplus d') →
      q.Eplus d ≠ q.Eplus d' := by
    intro d d' hd hd' hdd' bd bd' he
    rw [← he] at bd'
    exact hdd' (p.eq_of_balance hZ hV (q.Eplus_pos h2 h0 d).ne' hd hd' bd bd')
  have m₁ := hmem δ₁ le_rfl (by linarith [pi_pos])
  have m₂ := hmem δ₂ h₁₂.le (by linarith)
  have m₃ := hmem δ₃ (h₁₂.trans h₂₃).le h₃
  have hsub : {q.Eplus δ₁, q.Eplus δ₂, q.Eplus δ₃} ⊆ {E : ℝ | 0 < E ∧ p.quartic.IsRoot E} := by
    rintro E (rfl | rfl | rfl)
    · exact ⟨q.Eplus_pos h2 h0 _, p.quartic_isRoot_of_balance hZ b₁⟩
    · exact ⟨q.Eplus_pos h2 h0 _, p.quartic_isRoot_of_balance hZ b₂⟩
    · exact ⟨q.Eplus_pos h2 h0 _, p.quartic_isRoot_of_balance hZ b₃⟩
  have h3 : ({q.Eplus δ₁, q.Eplus δ₂, q.Eplus δ₃} : Set ℝ).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨_, _, _, hne m₁ m₂ h₁₂.ne b₁ b₂, hne m₁ m₃ (h₁₂.trans h₂₃).ne b₁ b₃,
      hne m₂ m₃ h₂₃.ne b₂ b₃, rfl⟩
  have hfin : {E : ℝ | 0 < E ∧ p.quartic.IsRoot E}.Finite :=
    (Polynomial.finite_setOfPred_isRoot p.quartic_ne_zero).subset fun E hE => hE.2
  have hle := (Set.ncard_le_ncard hsub hfin).trans
    ((SpecialFunctions.ncard_pos_isRoot_le_countP p.quartic_ne_zero).trans
      (p.countP_pos_roots_le_two hnq hX))
  omega

/-- **One maximum of `P̃` per period.** In the physical range (`n_q, X > 0`,
`E₀ + n_q Q_ref > 0`, `V ≠ 0`) the quasi-static characteristic has exactly one local maximum in
every window `[a, a + 2π)` (`Ptilde_not_three`,
`SpecialFunctions.existsUnique_isLocalMax_of_levels`). Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem existsUnique_isLocalMax_Ptilde (hnq : 0 < q.nq)
    (hX : 0 < q.X) (hc : 0 < q.E0 + q.nq * q.Qref) (hV : q.V ≠ 0) (a : ℝ) :
    ∃! δ, δ ∈ Ico a (a + 2 * π) ∧ IsLocalMax q.Ptilde δ :=
  SpecialFunctions.existsUnique_isLocalMax_of_levels
    (q.continuous_Ptilde (q.a2_pos hnq hX) (q.a0_neg hc)) q.Ptilde_periodic two_pi_pos
    (fun _ _ _ h₁ h₂ h₃ e₁ e₂ => q.Ptilde_not_three hnq hX hc hV h₁ h₂ h₃ e₁ e₂) a

/-- **One minimum of `P̃` per period.** In the physical range the quasi-static characteristic
has exactly one local minimum in every window `[a, a + 2π)`
(`SpecialFunctions.existsUnique_isLocalMin_of_levels`). Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem existsUnique_isLocalMin_Ptilde (hnq : 0 < q.nq)
    (hX : 0 < q.X) (hc : 0 < q.E0 + q.nq * q.Qref) (hV : q.V ≠ 0) (a : ℝ) :
    ∃! δ, δ ∈ Ico a (a + 2 * π) ∧ IsLocalMin q.Ptilde δ :=
  SpecialFunctions.existsUnique_isLocalMin_of_levels
    (q.continuous_Ptilde (q.a2_pos hnq hX) (q.a0_neg hc)) q.Ptilde_periodic two_pi_pos
    (fun _ _ _ h₁ h₂ h₃ e₁ e₂ => q.Ptilde_not_three hnq hX hc hV h₁ h₂ h₃ e₁ e₂) a

/-! ## The Q–V droop family -/

/-- A Q–V droop model read about a selected point `(δ*, 0, Q_f*)`. -/
structure Model where
  /-- The parameters. -/
  q : QVDroop
  /-- The selected angle `δ*`. -/
  δ : ℝ
  /-- The selected filtered reactive power `Q_f*` (EMF `E* = E₀ − n_q (Q_f* − Q_ref)`). -/
  Qf : ℝ

/-- The selected point `(δ*, 0, Q_f*)`. -/
def Model.point (m : Model) : State 3 := mk3 m.δ 0 m.Qf

/-- The closed-loop field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 3) : State 3 := m.q.field (z + m.point)

/-- The Jacobian at the selected point. -/
def Model.jacobian (m : Model) : Matrix (Fin 3) (Fin 3) ℝ := m.q.jacobian m.δ (m.q.emf m.Qf)

/-- The stability condition: an equilibrium at the selected point with a Hurwitz Jacobian. -/
def Model.Stable (m : Model) : Prop :=
  m.q.field m.point = 0 ∧ LinearSystems.IsHurwitz m.jacobian

/-- The instability condition: an equilibrium at the selected point with `det J > 0`. -/
def Model.Saddle (m : Model) : Prop := m.q.field m.point = 0 ∧ 0 < m.jacobian.det

/-- The Q–V droop family: the local spectral family of the translated field. -/
def family : Family Model Spectral.Requirement 3 0 :=
  Spectral.localFamily Model.field Model.Stable Model.Saddle

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  Spectral.localFamily_isAutonomous _ _ _

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.q.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field) (pt := Model.point)
    family_isAutonomous

@[tmio M, powerlib_domain] private theorem fderiv_point (m : Model) :
    fderiv ℝ m.q.field m.point = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jacobian := by
  rw [m.q.fderiv_field]
  simp [Model.point, Model.jacobian]

@[tmio TM, powerlib_domain] private theorem unstable_of_saddle {m : Model} (h : m.Saddle) :
    Flow.Property.holds .unstable m.q.field m.point := by
  refine Criteria.unstable_of_jacobian_det m.jacobian m.q.contDiff_field h.1 (fderiv_point m) ?_
  rw [show ((-1 : ℝ) ^ 3) = -1 by norm_num, neg_one_mul, neg_lt_zero]
  exact h.2

/-- Every translation of the Q–V droop family is sound: a Hurwitz Jacobian at an equilibrium
gives local exponential stability (converse linearization), `det J > 0` at an equilibrium a
positive real eigenvalue, hence instability. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m hm => ?_) (fun m hm => ?_)
  · refine (Flow.Property.holds_shift_iff _).mpr ?_
    exact (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ m.q.contDiff_field
      (fderiv_point m)).mpr hm
  · exact (Flow.Property.holds_shift_iff _).mpr (unstable_of_saddle hm)

/-- **The descending branch is unstable.** In the physical range (`M, ω_q, n_q, X > 0`,
`E₀ + n_q Q_ref > 0`), an equilibrium with a positive EMF at which the quasi-static
characteristic descends, `P̃'(δ*) < 0`, is unstable for every damping `D`:
`det J = −(ω_q/M) (1 + n_q Q_E) P̃' > 0` with `1 + n_q Q_E > 0` on the physical branch
(`det_jacobian_eq_slope`, `one_add_nq_QE_Eplus`), a positive real eigenvalue. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_slope_neg (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X) (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref)
    (heq : m.q.field m.point = 0) (hE : 0 < m.q.emf m.Qf) (hs : deriv m.q.Ptilde m.δ < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_flow_iff)]
  refine unstable_of_saddle ⟨heq, ?_⟩
  have h2 := m.q.a2_pos hnq hX
  have h0 := m.q.a0_neg hc
  have hEq : m.q.emf m.Qf = m.q.Eplus m.δ := by
    simpa [Model.point] using m.q.emf_eq_Eplus hM.ne' hω.ne' h2 h0 heq (by simpa [Model.point])
  have hK := (m.q.one_add_nq_QE_Eplus h2 h0 m.δ).2
  rw [Model.jacobian, hEq, m.q.det_jacobian_eq_slope h2 h0 m.δ]
  have hωM : 0 < m.q.ωq / m.q.M := div_pos hω hM
  nlinarith [mul_pos hωM hK, mul_pos (mul_pos hωM hK) (neg_pos.mpr hs)]

end QVDroop

end powerlib.GFM
