import theorem.SingularPerturbation.Linear
import theorem.Linear.Certificate
import theorem.Dynamics.Calculus

/-! # Frozen fast subsystems: uniform exponential stability over a compact set

A continuous family of Hurwitz matrices over a compact set of frozen slow states has one
exponential decay estimate for all its linear fast subsystems.

Scope.
* A continuous family of real `m × m` matrices `A(x)` indexed by the frozen slow state `x`
  ranging over a compact space `X` (for a compact subset `K` of the slow state space take `X = K`
  with the subspace topology); the frozen *linearized* fast systems `ẏ = A(x) y` in the fast time
  scale; continuous time.
* `|y|² = y ⬝ᵥ y` (`sqNorm_eq_dotProduct`); trajectories are global coordinate solutions
  `∀ t, HasDerivAt y (M *ᵥ y t) t`. `BoundedCertificate` is a `Linear.Certificate` with explicit
  coordinate bounds.
* The nonlinear boundary-layer system is treated in
  `theorem/SingularPerturbation/BoundaryLayer.lean` (`boundaryLayer_uniform_exponentialStability`,
  `boundaryLayer_uniform_exponentialStability_tx`), which builds on `dissipation_of_close`
  here.

Source: work-sync theory/T-slow-manifold.md §1.5 and theory/T-singular-perturbation.md §1.4
(attractivity of the slow manifold: the frozen fast subsystem `dy/dτ = A_y(x) y`,
`A_y(x) = ∂g/∂y (x, h(x))`, must be exponentially stable "uniformly in `x`").

Results.
* `nonempty_boundedCertificate_of_isHurwitz` — a Hurwitz matrix has a Lyapunov certificate
  (`Linear.Certificate`, from LeanForControl's Lyapunov equation) together with explicit bounds
  `lo|y|² ≤ yᵀPy ≤ hi|y|²` (`Linear.Certificate.exists_energy_bounds`).
* `hasDerivWithinAt_quadratic_of_symm`, `hasDerivAt_quadratic_of_symm` — `(yᵀPy)' = 2 yᵀ P ẏ`
  for symmetric `P` (also used by the finite-horizon and boundary-layer modules).
* `dissipation_of_close` — the certificate of `A₀` is a dissipation certificate for every nearby
  matrix `M` (`yᵀ P M y ≤ −|y|²/4`); reused for the nonlinear boundary layer in
  `theorem/SingularPerturbation/BoundaryLayer.lean`.
* `decay_of_dissipation` — a dissipation certificate `P` (`P = Pᵀ`, `lo|v|² ≤ vᵀPv ≤ hi|v|²`,
  `vᵀ P M v ≤ −|v|²/4`) gives `|y(t)|² ≤ (hi/lo) e^{−t/(2 hi)} |y(0)|²` along `ẏ = M y`.
* `decay_of_close` — if `c` is a Lyapunov certificate for `A₀` (`A₀ᵀP + PA₀ = −I`,
  `lo|y|² ≤ yᵀPy ≤ hi|y|²`) and `Σᵢⱼ |Mᵢⱼ − A₀ᵢⱼ| ≤ 1/(4 Σᵢⱼ|Pᵢⱼ| + 4)`, every trajectory of
  `ẏ = M y` satisfies `|y(t)|² ≤ (hi/lo) e^{−t/(2 hi)} |y(0)|²` — the same `P` works for all
  nearby matrices.
* `exists_uniform_dissipation` — on a compact parameter space one pair of energy bounds `lo, hi`
  and one bound on `Σ|Pᵢⱼ|` serve all parameters: for every `p` a symmetric `P` with
  `lo|v|² ≤ vᵀPv ≤ hi|v|²` and `vᵀ P A(p) v ≤ −|v|²/4` (finite subcover of the certificates, via
  `dissipation_of_close`); reused by `theorem/SingularPerturbation/BoundaryLayer.lean`.
* `uniform_frozen_exponentialStability` — if `A` is continuous on the compact space `X` and every
  `A(x)` is Hurwitz, there are `C > 0`, `α > 0` such that for **every** `x`, every trajectory of
  `ẏ = A(x) y` satisfies `|y(t)|² ≤ C e^{−αt} |y(0)|²` (uniform rate `α`, i.e. the spectral
  abscissa is uniformly negative in the sense of decay estimates).
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix

variable {m : ℕ}

@[tmio T, powerlib_foundation] theorem absSum_mul_le (P Q : Matrix (Fin m) (Fin m) ℝ) :
    absSum (P * Q) ≤ absSum P * absSum Q := by
  have hrow : ∀ l, ∑ j, |Q l j| ≤ absSum Q := fun l =>
    Finset.single_le_sum (f := fun l' => ∑ j, |Q l' j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)
  calc absSum (P * Q) ≤ ∑ i, ∑ j, ∑ l, |P i l| * |Q l j| := by
        unfold absSum
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun l _ => abs_mul _ _
    _ = ∑ i, ∑ l, |P i l| * ∑ j, |Q l j| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ l, |P i l| * absSum Q := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => ?_
        exact mul_le_mul_of_nonneg_left (hrow l) (abs_nonneg _)
    _ = absSum P * absSum Q := by
        unfold absSum
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

@[tmio T, powerlib_foundation] theorem sqNorm_eq_dotProduct (y : Fin m → ℝ) : ∑ i, y i ^ 2 = y ⬝ᵥ y := by
  simp [dotProduct, sq]

/-- A quadratic Lyapunov certificate of `A` with explicit coordinate bounds
`lower |y|² ≤ yᵀ P y ≤ upper |y|²`. -/
structure BoundedCertificate (A : Matrix (Fin m) (Fin m) ℝ) extends Linear.Certificate A where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_bound : ∀ y : Fin m → ℝ, lower * (y ⬝ᵥ y) ≤ y ⬝ᵥ (P *ᵥ y)
  upper_bound : ∀ y : Fin m → ℝ, y ⬝ᵥ (P *ᵥ y) ≤ upper * (y ⬝ᵥ y)

/-- Every Hurwitz matrix has a bounded Lyapunov certificate. -/
@[tmio T, powerlib_foundation] theorem nonempty_boundedCertificate_of_isHurwitz
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : LinearSystems.IsHurwitz A) :
    Nonempty (BoundedCertificate A) := by
  obtain ⟨c⟩ := (Linear.nonempty_certificate_iff A).mpr hA
  obtain ⟨α, hα, β, hβα, hb⟩ := c.exists_energy_bounds
  have hconv (y : Fin m → ℝ) : ‖WithLp.toLp 2 y‖ ^ 2 = y ⬝ᵥ y := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  have hq (y : Fin m → ℝ) : inner ℝ (WithLp.toLp 2 y) (Linear.op c.P (WithLp.toLp 2 y)) =
      y ⬝ᵥ (c.P *ᵥ y) := Linear.inner_op c.P _ _
  exact ⟨{ c with
    lower := α, upper := β, lower_pos := hα, upper_pos := hα.trans_le hβα
    lower_bound := fun y => by rw [← hconv, ← hq]; exact (hb _).1
    upper_bound := fun y => by rw [← hconv, ← hq]; exact (hb _).2 }⟩

/-- Derivative of `yᵀ P y` for symmetric `P` along a path, within any set: `2 yᵀ P ẏ`. -/
@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_quadratic_of_symm
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P) {y : ℝ → Fin m → ℝ} {dy : Fin m → ℝ}
    {s : Set ℝ} {t : ℝ} (hy : HasDerivWithinAt y dy s t) :
    HasDerivWithinAt (fun τ => y τ ⬝ᵥ (P *ᵥ y τ)) (2 * (y t ⬝ᵥ (P *ᵥ dy))) s t := by
  have hPy : HasDerivWithinAt (fun τ => P *ᵥ y τ) (P *ᵥ dy) s t :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' P)).hasFDerivAt.comp_hasDerivWithinAt t hy
  convert Linear.dotProduct_hasDerivWithinAt hy hPy using 1
  rw [Criteria.dotProduct_mulVec_comm_of_symm hP dy (y t)]
  ring

/-- Derivative of `yᵀ P y` for symmetric `P`: `2 yᵀ P ẏ`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_quadratic_of_symm
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P) {y : ℝ → Fin m → ℝ} {dy : Fin m → ℝ} {t : ℝ}
    (hy : HasDerivAt y dy t) :
    HasDerivAt (fun s => y s ⬝ᵥ (P *ᵥ y s)) (2 * (y t ⬝ᵥ (P *ᵥ dy))) t :=
  hasDerivWithinAt_univ.mp (hasDerivWithinAt_quadratic_of_symm hP hy.hasDerivWithinAt)

/-- A Lyapunov certificate of `A₀` is a dissipation certificate for every nearby matrix `M`:
`yᵀ P M y ≤ −|y|²/4` whenever `Σᵢⱼ |Mᵢⱼ − A₀ᵢⱼ| ≤ 1/(4 Σᵢⱼ|Pᵢⱼ| + 4)`. -/
@[tmio T, powerlib_foundation] theorem dissipation_of_close {A0 M : Matrix (Fin m) (Fin m) ℝ}
    (c : BoundedCertificate A0) (hM : absSum (M - A0) ≤ 1 / (4 * absSum c.P + 4))
    (v : Fin m → ℝ) : v ⬝ᵥ (c.P *ᵥ (M *ᵥ v)) ≤ -(v ⬝ᵥ v) / 4 := by
  have hP := c.symmetric
  have hlyap : c.P * A0 + A0ᵀ * c.P = -1 := by rw [add_comm]; exact c.lyapunov
  have hAbs := absSum_nonneg c.P
  have hsplit : v ⬝ᵥ (c.P *ᵥ (M *ᵥ v)) =
      v ⬝ᵥ (c.P *ᵥ (A0 *ᵥ v)) + v ⬝ᵥ ((c.P * (M - A0)) *ᵥ v) := by
    rw [← mulVec_mulVec, ← dotProduct_add, ← mulVec_add, ← add_mulVec, add_sub_cancel]
  have h1 := dotProduct_mulVec_lyapunov hP hlyap v
  have h2 := abs_dotProduct_mulVec_le (c.P * (M - A0)) v v one_pos
  have h3 : absSum (c.P * (M - A0)) ≤ 1 / 4 := by
    calc absSum (c.P * (M - A0)) ≤ absSum c.P * absSum (M - A0) := absSum_mul_le _ _
      _ ≤ absSum c.P * (1 / (4 * absSum c.P + 4)) := by gcongr
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
  have hvv := dotProduct_self_nonneg' v
  have : |v ⬝ᵥ ((c.P * (M - A0)) *ᵥ v)| ≤ (v ⬝ᵥ v) / 4 := by
    calc |v ⬝ᵥ ((c.P * (M - A0)) *ᵥ v)| ≤ absSum (c.P * (M - A0)) * (1 * (v ⬝ᵥ v) +
          (v ⬝ᵥ v) / 1) / 2 := h2
      _ = absSum (c.P * (M - A0)) * (v ⬝ᵥ v) := by ring
      _ ≤ 1 / 4 * (v ⬝ᵥ v) := by gcongr
      _ = (v ⬝ᵥ v) / 4 := by ring
  rw [hsplit, h1]
  linarith [abs_le.mp this]

/-- A dissipation certificate proves exponential decay: if `P = Pᵀ`, `lo|v|² ≤ vᵀPv ≤ hi|v|²`
and `vᵀ P M v ≤ −|v|²/4`, every trajectory of `ẏ = M y` satisfies
`|y(t)|² ≤ (hi/lo) e^{−t/(2 hi)} |y(0)|²`. -/
@[tmio T, powerlib_foundation] theorem decay_of_dissipation {M P : Matrix (Fin m) (Fin m) ℝ}
    (hP : Pᵀ = P) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi)
    (hlower : ∀ v, lo * (v ⬝ᵥ v) ≤ v ⬝ᵥ (P *ᵥ v)) (hupper : ∀ v, v ⬝ᵥ (P *ᵥ v) ≤ hi * (v ⬝ᵥ v))
    (hdiss : ∀ v : Fin m → ℝ, v ⬝ᵥ (P *ᵥ (M *ᵥ v)) ≤ -(v ⬝ᵥ v) / 4)
    {y : ℝ → Fin m → ℝ} (hy : ∀ s, HasDerivAt y (M *ᵥ y s) s) (t : ℝ) (ht : 0 ≤ t) :
    y t ⬝ᵥ y t ≤ (hi / lo) * Real.exp (-(t / (2 * hi))) * (y 0 ⬝ᵥ y 0) := by
  -- energy derivative
  have hderiv : ∀ s, HasDerivAt (fun s => y s ⬝ᵥ (P *ᵥ y s))
      (2 * (y s ⬝ᵥ (P *ᵥ (M *ᵥ y s)))) s := fun s => hasDerivAt_quadratic_of_symm hP (hy s)
  -- Grönwall: `V' ≤ -V/(2 hi)`
  have hV : (y t ⬝ᵥ (P *ᵥ y t)) ≤ Real.exp (-(t / (2 * hi))) * (y 0 ⬝ᵥ (P *ᵥ y 0)) := by
    have h := Dynamics.le_exp_mul_of_hasDerivWithinAt (g := fun s => y s ⬝ᵥ (P *ᵥ y s))
      (ρ := 1 / (2 * hi)) (fun s _ => (hderiv s).hasDerivWithinAt) (fun s _ => by
        have hup := hupper (y s)
        have hd := hdiss (y s)
        have : 1 / (2 * hi) * (y s ⬝ᵥ (P *ᵥ y s)) ≤ (y s ⬝ᵥ y s) / 2 := by
          rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
        linarith) t ⟨ht, le_rfl⟩
    rwa [sub_zero, neg_mul, one_div_mul_eq_div] at h
  have hlow := hlower (y t)
  have hup0 := hupper (y 0)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hlo]
  calc (y t ⬝ᵥ y t) * lo = lo * (y t ⬝ᵥ y t) := mul_comm _ _
    _ ≤ (y t ⬝ᵥ (P *ᵥ y t)) := hlow
    _ ≤ Real.exp (-(t / (2 * hi))) * (y 0 ⬝ᵥ (P *ᵥ y 0)) := hV
    _ ≤ Real.exp (-(t / (2 * hi))) * (hi * (y 0 ⬝ᵥ y 0)) := by gcongr
    _ = hi * Real.exp (-(t / (2 * hi))) * (y 0 ⬝ᵥ y 0) := by ring

/-- A Lyapunov certificate of `A₀` also proves exponential decay for every nearby matrix `M`. -/
@[tmio T, powerlib_foundation] theorem decay_of_close {A0 M : Matrix (Fin m) (Fin m) ℝ}
    (c : BoundedCertificate A0) (hM : absSum (M - A0) ≤ 1 / (4 * absSum c.P + 4))
    {y : ℝ → Fin m → ℝ} (hy : ∀ s, HasDerivAt y (M *ᵥ y s) s) (t : ℝ) (ht : 0 ≤ t) :
    y t ⬝ᵥ y t ≤ (c.upper / c.lower) * Real.exp (-(t / (2 * c.upper))) *
      (y 0 ⬝ᵥ y 0) :=
  decay_of_dissipation c.symmetric c.lower_pos c.upper_pos c.lower_bound c.upper_bound
    (dissipation_of_close c hM) hy t ht

@[tmio T, powerlib_foundation] theorem continuous_absSum_sub (A0 : Matrix (Fin m) (Fin m) ℝ) :
    Continuous fun M : Matrix (Fin m) (Fin m) ℝ => absSum (M - A0) := by
  unfold absSum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_id.matrix_elem i j).sub continuous_const).abs

/-- **Uniform Lyapunov dissipation** for a continuous Hurwitz family on a compact parameter
space: one pair of constants `lo, hi` and one bound `Pb` serve every parameter. -/
@[tmio T, powerlib_foundation] theorem exists_uniform_dissipation {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {A : X → Matrix (Fin m) (Fin m) ℝ} (hA : Continuous A)
    (hH : ∀ p, LinearSystems.IsHurwitz (A p)) :
    ∃ lo > 0, ∃ hi > 0, ∃ Pb ≥ 0, ∀ p, ∃ P : Matrix (Fin m) (Fin m) ℝ, Pᵀ = P ∧
      (∀ v, lo * (v ⬝ᵥ v) ≤ v ⬝ᵥ (P *ᵥ v)) ∧ (∀ v, v ⬝ᵥ (P *ᵥ v) ≤ hi * (v ⬝ᵥ v)) ∧
      absSum P ≤ Pb ∧ ∀ v, v ⬝ᵥ (P *ᵥ (A p *ᵥ v)) ≤ -(v ⬝ᵥ v) / 4 := by
  classical
  let cert : ∀ x, BoundedCertificate (A x) := fun x =>
    (nonempty_boundedCertificate_of_isHurwitz (hH x)).some
  let δ : X → ℝ := fun x => 1 / (4 * absSum (cert x).P + 4)
  have hδ : ∀ x, 0 < δ x := fun x => by have := absSum_nonneg (cert x).P; positivity
  let O : X → Set X := fun x₀ => {x | absSum (A x - A x₀) < δ x₀}
  have hO : ∀ x₀, IsOpen (O x₀) := fun x₀ =>
    isOpen_lt ((continuous_absSum_sub (A x₀)).comp hA) continuous_const
  have hcover : (Set.univ : Set X) ⊆ ⋃ x₀, O x₀ := fun x _ =>
    Set.mem_iUnion.mpr ⟨x, by simp [O, absSum, hδ x]⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  by_cases hX : Nonempty X
  swap
  · exact ⟨1, one_pos, 1, one_pos, 0, le_rfl, fun x => absurd ⟨x⟩ hX⟩
  have hsne : s.Nonempty := by
    obtain ⟨x⟩ := hX
    obtain ⟨x₀, hx₀, -⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨x₀, hx₀⟩
  refine ⟨s.inf' hsne fun x₀ => (cert x₀).lower, ?_, s.sup' hsne fun x₀ => (cert x₀).upper, ?_,
    s.sup' hsne fun x₀ => absSum (cert x₀).P, ?_, fun p => ?_⟩
  · show 0 < _
    rw [Finset.lt_inf'_iff]
    exact fun x₀ _ => (cert x₀).lower_pos
  · obtain ⟨x₀, hx₀⟩ := hsne
    exact lt_of_lt_of_le (cert x₀).upper_pos
      (Finset.le_sup' (fun x₀ => (cert x₀).upper) hx₀)
  · obtain ⟨x₀, hx₀⟩ := hsne
    exact le_trans (absSum_nonneg _) (Finset.le_sup' (fun x₀ => absSum (cert x₀).P) hx₀)
  obtain ⟨x₀, hx₀s, hxO⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
  refine ⟨(cert x₀).P, (cert x₀).symmetric, fun v => ?_, fun v => ?_,
    Finset.le_sup' (fun x₀ => absSum (cert x₀).P) hx₀s,
    dissipation_of_close (cert x₀) (le_of_lt hxO)⟩
  · have h1 := Finset.inf'_le (fun x₀ => (cert x₀).lower) hx₀s
    have h2 := (cert x₀).lower_bound v
    have h3 := dotProduct_self_nonneg' v
    nlinarith
  · have h1 := Finset.le_sup' (fun x₀ => (cert x₀).upper) hx₀s
    have h2 := (cert x₀).upper_bound v
    have h3 := dotProduct_self_nonneg' v
    nlinarith

/-- **Uniform exponential stability of the frozen fast subsystems** on a compact set
(`exists_uniform_dissipation`, then `decay_of_dissipation`: `C = hi/lo`, `α = 1/(2 hi)`). -/
@[tmio T, powerlib_foundation] theorem uniform_frozen_exponentialStability {X : Type*}
    [TopologicalSpace X] [CompactSpace X] {A : X → Matrix (Fin m) (Fin m) ℝ} (hA : Continuous A)
    (hH : ∀ x, LinearSystems.IsHurwitz (A x)) :
    ∃ C > 0, ∃ α > 0, ∀ x (y : ℝ → Fin m → ℝ), (∀ s, HasDerivAt y (A x *ᵥ y s) s) → ∀ t, 0 ≤ t →
      (y t ⬝ᵥ y t) ≤ C * Real.exp (-(α * t)) * (y 0 ⬝ᵥ y 0) := by
  obtain ⟨lo, hlo, hi, hhi, _, _, hcert⟩ := exists_uniform_dissipation hA hH
  refine ⟨hi / lo, by positivity, 1 / (2 * hi), by positivity, fun x y hy t ht => ?_⟩
  obtain ⟨P, hP, hlower, hupper, -, hdiss⟩ := hcert x
  rw [show 1 / (2 * hi) * t = t / (2 * hi) by ring]
  exact decay_of_dissipation hP hlo hhi hlower hupper hdiss hy t ht

end powerlib.SingularPerturbation
