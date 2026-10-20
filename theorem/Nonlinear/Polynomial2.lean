import theorem.TMIO.ClaimElab
import theorem.Family.Basic
import theorem.Flow.Certificate
import theorem.Linear.Synthesis
import theorem.Linear.Transfer
import theorem.Dynamics.Coordinates
import theorem.PhasePlane.Planar

/-! # Two-state polynomial fields with sum-of-squares certificates

A model enters the library through its field map, read as an autonomous system. A certificate is
rational data — a quadratic energy, two bounds, a decay rate and three weighted sums of squares —
accepted by an exact check: the three polynomial identities are compared coefficient by
coefficient and the weights must be nonnegative. The check is a boolean computation whose
soundness is a theorem; an accepted certificate is a quadratic-decay certificate and therefore
proves forward completeness, global exponential stability and decay at half its rate.

The synthesizer proposes the data from the model alone. The energy is taken from a fixed family —
the solution of the Lyapunov equation of the linearization (`Linear.Synthesis`), then diagonal
energies — the bounds and the rate come from eigenvalue bounds, and each sum of squares is the
`L D Lᵀ` factorization of a Gram matrix of canonical shape. It is not trusted: whatever it
proposes is checked. It succeeds when some energy of the family makes the higher-order terms
dissipative and the decay polynomial admits a Gram matrix of that shape; otherwise it proposes
nothing, which proves nothing.

Model boundary.
* Autonomous fields `x' = f(x)` on `ℝ²` whose two components are polynomials with rational
  coefficients, in continuous time, without input, delay or switching. The equilibrium is the
  origin.
* A polynomial example family of generic mathematics, not an engineering model; certificates are
  quadratic energies only.

Source: the quadratic-decay certificates of `theorem/Flow/Certificate.lean`; the rational
Lyapunov synthesizer (`theorem/Linear/Synthesis.lean`) and pole stability
(`theorem/Linear/Transfer.lean`); LeanForControl's linearization theorem and indirect method of
Lyapunov; coordinate and planar helpers (`theorem/Dynamics/Coordinates.lean`,
`theorem/PhasePlane/Planar.lean`).

Results.
* Data: `Term`, `Polynomial`, `Model`, `WeightedSquare`, `Witness`; exact arithmetic (`scale`,
  `mul`, `coeff`, `vanishes`, `Witness.quadPoly`, `circle`, `sosPoly`, `Witness.liePoly`,
  `Witness.lowerGap`, `Witness.upperGap`, `Witness.decayGap`).
* The check: `Witness.check`, `Certificate` (indexed by the model), `Witness.check_spec` (what the
  check establishes), `sosPoly_nonneg`, `Certificate.quadraticDecay` (an accepted certificate is a
  quadratic-decay certificate of the model's field).
* The untrusted synthesizer: `Model.linearPart`, `support`, `basis`, `addAt`, `gram`, `ldlStep`,
  `gramSquares`, `synthWith`, `energies`, `synth`, `accepts`, `certificateOf`.
* Evaluation and smoothness: `eval` (with `eval_nil`, `eval_cons`, `eval_append`, `eval_scale`,
  `eval_map_mul`, `eval_mul`, `coeff_cons`, `coeff_eq_zero_of_not_mem`, `eval_eq_sum`,
  `eval_eq_zero_of_vanishes`, `eval_zero`), `Model.field` (`Model.field_zero_apply`,
  `Model.field_one_apply`, `Model.field_smooth`), `coordinate_smooth`, `eval_smooth`,
  `Witness.energy` (`Witness.energy_apply`, `Witness.energy_smooth`, `Witness.energy_derivative`,
  `Witness.energy_lie`), `norm_sq`, `eval_circle`.
* The linearization: `coord`, `hasFDerivAt_monomial_zero`, `hasFDerivAt_eval_zero`,
  `Model.linearization` (the matrix of linear coefficients), `hasFDerivAt_field_zero` (it is the
  Jacobian of the field at the origin), `Model.field_eq_zero`.
* Static evidence: `family_isAutonomous`; the boundary models `cubicModel`,
  `cascadeModel`, `quarticModel` with `cubicModel_field`, `cubicModel_not_certified`,
  `cubicModel_linearization`, `cascadeModel_field`, `cascadeEnergy`, `cascadeEnergy_lie`,
  `cascade_rejected`, `quarticModel_field`, `quarticEnergy`, `quarticEnergy_smooth`,
  `quarticEnergy_lie`, `quarticEnergy_bounds`, `quarticEnergy_compact`, `nonpos_of_sq_bound`,
  `quartic_leading_nonpos`.

Family and connection conclusions.
* `Nonlinear.Polynomial2.family : Family Model Requirement 2 0`: every model read as its
  autonomous field. The family's requirement language speaks of the origin as an equilibrium, of
  the linearization there — computed from the linear coefficients, and shown to be the Jacobian
  of the field — and of certificates (`equilibrium`, `linearizationHurwitz`,
  `linearizationUnstable`, `certified`, `decayRateAtLeast a`). The local sentences translate into
  an equilibrium with a Hurwitz linearization, instability into one with a right-half-plane root,
  the global sentences and sampled contraction into a certificate, a decay rate into a certificate
  with that rate; conservation into the whole language, which no model meets (`realize_univ`: no
  model has a Hurwitz linearization with a right-half-plane root); passivity into nothing.
* `Certificate.mem_den`: a certificate places its model in global exponential stability.
* Its translation chain lies below its semantics connection (`chain_le_semantics`): the
  linearization decides the local sentences and instability (LeanForControl's indirect method),
  a certificate the global ones and a decay rate.
* Cubic damping `x' = -x³, y' = -y³` marks where the connections part: it is globally
  asymptotically stable with neither a certificate nor a Hurwitz linearization
  (`not_exact_asymptotic`).
* The cascade `cascadeModel` is globally asymptotically stable (`cascade_asymptotic`) but not
  globally exponentially stable (`cascade_not_exponential`), so no certificate of this language
  exists (`cascade_certificate_boundary`), a limitation of the language, not of its search.
* The quartic rotation with linear damping `quarticModel` is globally exponentially stable
  (`quartic_exponential`) without a quadratic certificate (`quartic_certificate_boundary`); the
  global exponential and the contractive translations are therefore not exact
  (`not_exact_exponential`, `not_exact_contractive`).
-/

namespace powerlib.Nonlinear.Polynomial2

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- A monomial `c xᵃ yᵇ`. -/
structure Term where
  coefficient : ℚ
  powers : ℕ × ℕ
  deriving Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- A polynomial in two variables, as a list of monomials; equal monomials may repeat. -/
abbrev Polynomial := List Term

/-- A two-state polynomial model. -/
structure Model where
  field0 : Polynomial
  field1 : Polynomial
  deriving Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- A weighted square `w q²`. -/
structure WeightedSquare where
  weight : ℚ
  poly : Polynomial
  deriving Inhabited, BEq, Lean.ToExpr

/-- The rational data of a certificate. -/
structure Witness where
  p00 : ℚ
  p01 : ℚ
  p11 : ℚ
  lower : ℚ
  upper : ℚ
  rate : ℚ
  lower_sos : List WeightedSquare
  upper_sos : List WeightedSquare
  decay_sos : List WeightedSquare
  deriving Inhabited, BEq, Lean.ToExpr

/-! ## Exact polynomial arithmetic -/

/-- `c p`. -/
def scale (c : ℚ) (p : Polynomial) : Polynomial := p.map fun t => ⟨c * t.coefficient, t.powers⟩

/-- `p q`, term by term. -/
def mul (p q : Polynomial) : Polynomial :=
  p.flatMap fun s => q.map fun t =>
    ⟨s.coefficient * t.coefficient, (s.powers.1 + t.powers.1, s.powers.2 + t.powers.2)⟩

/-- The coefficient of the monomial `m`: the terms with that monomial add up. -/
def coeff : Polynomial → ℕ × ℕ → ℚ
  | [], _ => 0
  | t :: ts, m => (if t.powers = m then t.coefficient else 0) + coeff ts m

/-- Every monomial of `p` has coefficient zero. -/
def vanishes (p : Polynomial) : Bool := p.all fun t => coeff p t.powers == 0

/-- The quadratic energy `p₀₀ x² + 2 p₀₁ x y + p₁₁ y²`. -/
def Witness.quadPoly (w : Witness) : Polynomial :=
  [⟨w.p00, (2, 0)⟩, ⟨2 * w.p01, (1, 1)⟩, ⟨w.p11, (0, 2)⟩]

/-- `x² + y²`. -/
def circle : Polynomial := [⟨1, (2, 0)⟩, ⟨1, (0, 2)⟩]

/-- A weighted sum of squares. -/
def sosPoly (squares : List WeightedSquare) : Polynomial :=
  squares.flatMap fun s => scale s.weight (mul s.poly s.poly)

/-- The Lie derivative of the energy along the model. -/
def Witness.liePoly (model : Model) (w : Witness) : Polynomial :=
  mul [⟨2 * w.p00, (1, 0)⟩, ⟨2 * w.p01, (0, 1)⟩] model.field0 ++
    mul [⟨2 * w.p01, (1, 0)⟩, ⟨2 * w.p11, (0, 1)⟩] model.field1

/-- `V - lower (x² + y²) - σ_lower`. -/
def Witness.lowerGap (w : Witness) : Polynomial :=
  w.quadPoly ++ scale (-w.lower) circle ++ scale (-1) (sosPoly w.lower_sos)

/-- `upper (x² + y²) - V - σ_upper`. -/
def Witness.upperGap (w : Witness) : Polynomial :=
  scale w.upper circle ++ scale (-1) w.quadPoly ++ scale (-1) (sosPoly w.upper_sos)

/-- `-V̇ - rate V - σ_decay`. -/
def Witness.decayGap (model : Model) (w : Witness) : Polynomial :=
  scale (-1) (w.liePoly model) ++ scale (-w.rate) w.quadPoly ++ scale (-1) (sosPoly w.decay_sos)

/-! ## The check -/

/-- The exact check of a proposal: positive bounds and rate, nonnegative weights, a field vanishing
at the origin, and the three identities, coefficient by coefficient. -/
def Witness.check (model : Model) (w : Witness) : Bool :=
  decide (0 < w.lower) && decide (0 < w.upper) && decide (0 < w.rate) &&
    (w.lower_sos ++ w.upper_sos ++ w.decay_sos).all (fun s => decide (0 ≤ s.weight)) &&
    coeff model.field0 (0, 0) == 0 && coeff model.field1 (0, 0) == 0 &&
    vanishes w.lowerGap && vanishes w.upperGap && vanishes (w.decayGap model)

/-- A certificate of a model: rational data passing the check. The type is indexed by the model,
so a certificate of another model does not typecheck. -/
structure Certificate (model : Model) where
  witness : Witness
  checked : witness.check model = true

/-! ## The untrusted synthesizer -/

/-- The linearization at the origin. -/
def Model.linearPart (model : Model) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![coeff model.field0 (1, 0), coeff model.field0 (0, 1);
    coeff model.field1 (1, 0), coeff model.field1 (0, 1)]

/-- The monomials of `p`. -/
def support (p : Polynomial) : List (ℕ × ℕ) := (p.map (·.powers)).eraseDups

/-- The monomials of total degree `1, …, d`. -/
def basis (d : ℕ) : List (ℕ × ℕ) :=
  (List.range d).flatMap fun k => (List.range (k + 2)).map fun i => (k + 1 - i, i)

/-- Add `c` to entry `(i, j)` of a square array. -/
def addAt (Q : List (List ℚ)) (i j : ℕ) (c : ℚ) : List (List ℚ) :=
  Q.modify i fun row => row.modify j (· + c)

/-- A Gram matrix of `h` over the monomial basis `z`, in canonical shape: a positive coefficient
goes to a diagonal entry when its monomial is a square of the basis, every other coefficient is
spread evenly over the off-diagonal pairs producing its monomial. -/
def gram (h : Polynomial) (z : List (ℕ × ℕ)) : Option (List (List ℚ)) :=
  let idx := List.range z.length
  let mono (i j : ℕ) : ℕ × ℕ :=
    ((z.getD i (0, 0)).1 + (z.getD j (0, 0)).1, (z.getD i (0, 0)).2 + (z.getD j (0, 0)).2)
  let zero := List.replicate z.length (List.replicate z.length (0 : ℚ))
  (support h).foldlM (init := zero) fun Q m =>
    let c := coeff h m
    let diag := idx.filter fun i => mono i i == m
    let off := idx.flatMap fun i => (idx.filter fun j => i < j && mono i j == m).map (i, ·)
    if c == 0 then some Q
    else match diag, off with
      | i :: _, _ :: _ => if 0 < c then some (addAt Q i i c)
          else some (off.foldl (fun Q (i, j) =>
            addAt (addAt Q i j (c / (2 * off.length))) j i (c / (2 * off.length))) Q)
      | i :: _, [] => some (addAt Q i i c)
      | [], _ :: _ => some (off.foldl (fun Q (i, j) =>
            addAt (addAt Q i j (c / (2 * off.length))) j i (c / (2 * off.length))) Q)
      | [], [] => none

/-- One column of a semidefinite `L D Lᵀ` factorization; a zero pivot requires a zero column. -/
def ldlStep (Q : List (List ℚ)) (acc : List (List ℚ) × List ℚ) (k : ℕ) :
    Option (List (List ℚ) × List ℚ) :=
  let L := acc.1
  let D := acc.2
  let get (i j : ℕ) : ℚ := (L.getD i []).getD j 0
  let residual (i : ℕ) : ℚ := (Q.getD i []).getD k 0 -
    ((List.range k).map fun j => get i j * get k j * D.getD j 0).sum
  let dk := residual k
  if dk < 0 then none
  else if dk = 0 then
    if (List.range Q.length).all fun i => i ≤ k || residual i == 0 then
      some (L.modify k (·.set k 1), D ++ [0])
    else none
  else
    some (L.mapIdx (fun i row => if i = k then row.set k 1
      else if k < i then row.set k (residual i / dk) else row), D ++ [dk])

/-- A weighted sum of squares equal to `zᵀ Q z`, from a semidefinite factorization of `Q`. -/
def gramSquares (z : List (ℕ × ℕ)) (Q : List (List ℚ)) : Option (List WeightedSquare) :=
  ((List.range Q.length).foldlM (ldlStep Q)
    (List.replicate Q.length (List.replicate Q.length 0), [])).map fun (L, D) =>
    (List.range Q.length).filterMap fun k =>
      if D.getD k 0 = 0 then none else
        some ⟨D.getD k 0, (List.range Q.length).filterMap fun i =>
          let c := (L.getD i []).getD k 0
          if k ≤ i && c != 0 then some ⟨c, z.getD i (0, 0)⟩ else none⟩

/-- The proposal for one quadratic energy `(p₀₀, p₀₁, p₁₁)`: bounds from the eigenvalue bounds
`det / trace ≤ λ_min` and `λ_max ≤ trace`, a rate leaving half of the quadratic decay, and Gram
factorizations of the three identities. -/
def synthWith (model : Model) (P : ℚ × ℚ × ℚ) : Option Witness := do
  let (p00, p01, p11) := P
  let trace := p00 + p11
  let det := p00 * p11 - p01 * p01
  if trace ≤ 0 || det ≤ 0 then none
  -- The quadratic part of `-V̇` is `xᵀ M x` with `M = -(Aᵀ P + P A)`.
  let A := model.linearPart
  let m00 := -2 * (A 0 0 * p00 + A 1 0 * p01)
  let m01 := -(A 0 0 * p01 + A 1 0 * p11 + p00 * A 0 1 + p01 * A 1 1)
  let m11 := -2 * (A 0 1 * p01 + A 1 1 * p11)
  let traceM := m00 + m11
  let detM := m00 * m11 - m01 * m01
  if traceM ≤ 0 || detM ≤ 0 then none
  let lower := det / (2 * trace)
  let upper := trace + 1
  let rate := detM / traceM / (2 * upper)
  let lower_sos ← gramSquares [(1, 0), (0, 1)] [[p00 - lower, p01], [p01, p11 - lower]]
  let upper_sos ← gramSquares [(1, 0), (0, 1)] [[upper - p00, -p01], [-p01, upper - p11]]
  let w : Witness := ⟨p00, p01, p11, lower, upper, rate, lower_sos, upper_sos, []⟩
  let h := scale (-1) (w.liePoly model) ++ scale (-rate) w.quadPoly
  let degree := ((support h).map fun m => m.1 + m.2).foldl max 0
  let z := basis ((degree + 1) / 2)
  let decay_sos ← gramSquares z (← gram h z)
  return { w with decay_sos }

/-- The candidate energies: the Lyapunov energy of the linearization, then diagonal energies. -/
def energies (model : Model) : List (ℚ × ℚ × ℚ) :=
  ((Linear.Synthesis.synth model.linearPart).map fun lw => (lw.P 0 0, lw.P 0 1, lw.P 1 1)).toList ++
    [1, 2, 1 / 2, 4, 1 / 4, 8, 1 / 8].map fun r => (1, 0, r)

/-- The synthesizer: the first candidate energy for which every Gram factorization succeeds. -/
def synth (model : Model) : Option Witness := (energies model).firstM (synthWith model)

/-- Run the synthesizer on a model and check its proposal. -/
def accepts (model : Model) : Bool :=
  match synth model with
  | some w => w.check model
  | none => false

/-- The certificate synthesized for an accepted model. -/
def certificateOf (model : Model) (h : accepts model = true) : Certificate model :=
  match hs : synth model with
  | some w => ⟨w, by
      have h' : accepts model = w.check model := by
        unfold accepts
        rw [hs]
      rwa [h'] at h⟩
  | none => absurd h (by
      unfold accepts
      rw [hs]
      exact Bool.false_ne_true)

/-! ## Soundness of the check -/

noncomputable section

/-- Evaluation of a polynomial. -/
def eval : Polynomial → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | t :: ts, x, y => (t.coefficient : ℝ) * x ^ t.powers.1 * y ^ t.powers.2 + eval ts x y

@[simp, powerlib_foundation] theorem eval_nil (x y : ℝ) : eval [] x y = 0 := rfl

@[simp, powerlib_foundation] theorem eval_cons (t : Term) (ts : Polynomial) (x y : ℝ) :
    eval (t :: ts) x y = (t.coefficient : ℝ) * x ^ t.powers.1 * y ^ t.powers.2 + eval ts x y :=
  rfl

@[simp, powerlib_foundation] theorem eval_append (p q : Polynomial) (x y : ℝ) :
    eval (p ++ q) x y = eval p x y + eval q x y := by
  induction p with
  | nil => simp
  | cons t ts ih => simp [ih, add_assoc]

@[simp, powerlib_foundation] theorem eval_scale (c : ℚ) (p : Polynomial) (x y : ℝ) :
    eval (scale c p) x y = c * eval p x y := by
  induction p with
  | nil => simp [scale]
  | cons t ts ih =>
    simp only [scale, List.map_cons, eval_cons, Rat.cast_mul] at ih ⊢
    rw [ih]
    ring

@[powerlib_foundation] theorem eval_map_mul (s : Term) (q : Polynomial) (x y : ℝ) :
    eval (q.map fun t => (⟨s.coefficient * t.coefficient,
        (s.powers.1 + t.powers.1, s.powers.2 + t.powers.2)⟩ : Term)) x y =
      (s.coefficient : ℝ) * x ^ s.powers.1 * y ^ s.powers.2 * eval q x y := by
  induction q with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, eval_cons, Rat.cast_mul, pow_add] at ih ⊢
    rw [ih]
    ring

@[simp, powerlib_foundation] theorem eval_mul (p q : Polynomial) (x y : ℝ) :
    eval (mul p q) x y = eval p x y * eval q x y := by
  induction p with
  | nil => simp [mul]
  | cons s ss ih =>
    simp only [mul, List.flatMap_cons, eval_append, eval_cons] at ih ⊢
    rw [eval_map_mul, ih]
    ring

@[powerlib_foundation] theorem coeff_cons (t : Term) (ts : Polynomial) (m : ℕ × ℕ) :
    coeff (t :: ts) m = (if t.powers = m then t.coefficient else 0) + coeff ts m := rfl

@[powerlib_foundation] theorem coeff_eq_zero_of_not_mem {p : Polynomial} {m : ℕ × ℕ}
    (h : m ∉ (p.map (·.powers)).toFinset) : coeff p m = 0 := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at h
    rw [coeff_cons, ih h.2]
    simp [Ne.symm h.1]

/-- A polynomial is the sum of its monomials with their collected coefficients. -/
@[powerlib_foundation] theorem eval_eq_sum (p : Polynomial) (x y : ℝ) :
    eval p x y = ∑ m ∈ (p.map (·.powers)).toFinset, (coeff p m : ℝ) * x ^ m.1 * y ^ m.2 := by
  induction p with
  | nil => simp
  | cons t ts ih =>
    have hsplit : ∀ m : ℕ × ℕ, (coeff (t :: ts) m : ℝ) * x ^ m.1 * y ^ m.2 =
        (if t.powers = m then (t.coefficient : ℝ) * x ^ m.1 * y ^ m.2 else 0) +
          (coeff ts m : ℝ) * x ^ m.1 * y ^ m.2 := by
      intro m
      rw [coeff_cons]
      split_ifs <;> push_cast <;> ring
    rw [eval_cons, ih, List.map_cons, List.toFinset_cons, Finset.sum_congr rfl fun m _ => hsplit m,
      Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_insert_self, ↓reduceIte]
    rw [Finset.sum_insert_of_eq_zero_if_notMem fun hm => by rw [coeff_eq_zero_of_not_mem hm]; simp]

/-- A vanishing polynomial is zero everywhere. -/
@[powerlib_foundation] theorem eval_eq_zero_of_vanishes {p : Polynomial}
    (h : vanishes p = true) (x y : ℝ) : eval p x y = 0 := by
  rw [eval_eq_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  have := List.all_eq_true.mp h t ht
  rw [beq_iff_eq] at this
  simp [this]

@[powerlib_foundation] theorem eval_zero (p : Polynomial) : eval p 0 0 = coeff p (0, 0) := by
  induction p with
  | nil => simp [coeff]
  | cons t ts ih =>
    rw [eval_cons, ih, coeff_cons, Rat.cast_add]
    obtain ⟨a, b⟩ := t.powers
    rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos b with rfl | hb <;>
      simp [*, Nat.pos_iff_ne_zero.mp, zero_pow]

/-! ## The model and the energy -/

/-- The field map of the family. -/
def Model.field (model : Model) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)]

@[simp, powerlib_foundation] theorem Model.field_zero_apply (model : Model) (x : ℝ²) :
    model.field x 0 = eval model.field0 (x 0) (x 1) := by
  simp [Model.field]

@[simp, powerlib_foundation] theorem Model.field_one_apply (model : Model) (x : ℝ²) :
    model.field x 1 = eval model.field1 (x 0) (x 1) := by
  simp [Model.field]

@[fun_prop, powerlib_foundation] theorem coordinate_smooth (j : Fin 2) :
    ContDiff ℝ 1 (fun x : ℝ² => x j) :=
  Dynamics.contDiff_coord j

@[powerlib_foundation] theorem eval_smooth (p : Polynomial) :
    ContDiff ℝ 1 (fun x : ℝ² => eval p (x 0) (x 1)) := by
  induction p with
  | nil => exact contDiff_const
  | cons t ts ih =>
      exact ((contDiff_const.mul ((coordinate_smooth 0).pow t.powers.1)).mul
        ((coordinate_smooth 1).pow t.powers.2)).add ih

@[powerlib_foundation] theorem Model.field_smooth (model : Model) : ContDiff ℝ 1 model.field := by
  have hs : ContDiff ℝ 1 (fun x : ℝ² =>
      ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · simpa using eval_smooth model.field0
    · simpa using eval_smooth model.field1
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff.comp hs

/-- The energy of a witness. -/
def Witness.energy (w : Witness) (x : ℝ²) : ℝ := eval w.quadPoly (x 0) (x 1)

@[powerlib_foundation] theorem Witness.energy_apply (w : Witness) (x : ℝ²) :
    w.energy x = (w.p00 : ℝ) * x 0 ^ 2 + 2 * (w.p01 : ℝ) * x 0 * x 1 + (w.p11 : ℝ) * x 1 ^ 2 := by
  simp [Witness.energy, Witness.quadPoly]
  ring

@[powerlib_foundation] theorem Witness.energy_smooth (w : Witness) : ContDiff ℝ 1 w.energy := by
  have h : w.energy = fun x : ℝ² =>
      (w.p00 : ℝ) * x 0 ^ 2 + 2 * (w.p01 : ℝ) * x 0 * x 1 + (w.p11 : ℝ) * x 1 ^ 2 :=
    funext w.energy_apply
  rw [h]
  fun_prop

@[powerlib_foundation] theorem Witness.energy_derivative (w : Witness) (x dx : ℝ²) :
    fderiv ℝ w.energy x dx =
      (2 * (w.p00 : ℝ) * x 0 + 2 * (w.p01 : ℝ) * x 1) * dx 0 +
      (2 * (w.p01 : ℝ) * x 0 + 2 * (w.p11 : ℝ) * x 1) * dx 1 := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : ℝ² →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := (((h0.mul h0).const_mul (w.p00 : ℝ)).add
    ((h0.const_mul (2 * (w.p01 : ℝ))).mul h1)).add ((h1.mul h1).const_mul (w.p11 : ℝ))
  simp only [PiLp.proj_apply] at h
  have hV : w.energy = fun x : ℝ² =>
      (w.p00 : ℝ) * (x 0 * x 0) + 2 * (w.p01 : ℝ) * x 0 * x 1 + (w.p11 : ℝ) * (x 1 * x 1) := by
    funext x
    rw [w.energy_apply]
    ring
  rw [hV]
  erw [h.fderiv]
  simp
  ring

@[powerlib_foundation] theorem Witness.energy_lie (model : Model) (w : Witness) (x : ℝ²) :
    fderiv ℝ w.energy x (model.field x) = eval (w.liePoly model) (x 0) (x 1) := by
  rw [w.energy_derivative]
  simp [Witness.liePoly]

@[powerlib_foundation] theorem norm_sq (x : ℝ²) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 :=
  PhasePlane.norm_sq_eq x

@[powerlib_foundation] theorem eval_circle (x : ℝ²) : eval circle (x 0) (x 1) = ‖x‖ ^ 2 := by
  simp [circle, norm_sq]

@[powerlib_foundation] theorem sosPoly_nonneg {squares : List WeightedSquare}
    (h : ∀ s ∈ squares, 0 ≤ s.weight) (x y : ℝ) : 0 ≤ eval (sosPoly squares) x y := by
  induction squares with
  | nil => simp [sosPoly]
  | cons s ss ih =>
    simp only [sosPoly, List.flatMap_cons, eval_append, eval_scale, eval_mul] at ih ⊢
    exact add_nonneg (mul_nonneg (by exact_mod_cast h s List.mem_cons_self) (mul_self_nonneg _))
      (ih fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- What the check establishes. -/
@[powerlib_foundation] theorem Witness.check_spec {model : Model} {w : Witness}
    (h : w.check model = true) :
    0 < w.lower ∧ 0 < w.upper ∧ 0 < w.rate ∧
      (∀ s ∈ w.lower_sos ++ w.upper_sos ++ w.decay_sos, 0 ≤ s.weight) ∧
      coeff model.field0 (0, 0) = 0 ∧ coeff model.field1 (0, 0) = 0 ∧
      vanishes w.lowerGap = true ∧ vanishes w.upperGap = true ∧
      vanishes (w.decayGap model) = true := by
  simp only [Witness.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3,
    fun s hs => of_decide_eq_true (h4 s hs), h5, h6, h7, h8, h9⟩

/-- An accepted certificate is a quadratic-decay certificate of the model's field. -/
def Certificate.quadraticDecay {model : Model} (c : Certificate model) :
    Flow.QuadraticDecay model.field c.witness.energy 0 :=
  have h := Witness.check_spec c.checked
  { lower := c.witness.lower
    upper := c.witness.upper
    rate := c.witness.rate
    lower_pos := by exact_mod_cast h.1
    upper_pos := by exact_mod_cast h.2.1
    rate_pos := by exact_mod_cast h.2.2.1
    smooth := c.witness.energy_smooth
    equilibrium := by
      ext i
      fin_cases i
      · simp [eval_zero, h.2.2.2.2.1]
      · simp [eval_zero, h.2.2.2.2.2.1]
    lower_bound := fun x => by
      have hz := eval_eq_zero_of_vanishes h.2.2.2.2.2.2.1 (x 0) (x 1)
      have hs := sosPoly_nonneg (squares := c.witness.lower_sos)
        (fun s hs => h.2.2.2.1 s (by simp [hs])) (x 0) (x 1)
      simp only [Witness.lowerGap, eval_append, eval_scale, Rat.cast_neg, Rat.cast_one,
        eval_circle] at hz
      simp only [sub_zero, Witness.energy]
      linarith
    upper_bound := fun x => by
      have hz := eval_eq_zero_of_vanishes h.2.2.2.2.2.2.2.1 (x 0) (x 1)
      have hs := sosPoly_nonneg (squares := c.witness.upper_sos)
        (fun s hs => h.2.2.2.1 s (by simp [hs])) (x 0) (x 1)
      simp only [Witness.upperGap, eval_append, eval_scale, Rat.cast_neg, Rat.cast_one,
        eval_circle] at hz
      simp only [sub_zero, Witness.energy]
      linarith
    dissipation := fun x => by
      have hz := eval_eq_zero_of_vanishes h.2.2.2.2.2.2.2.2 (x 0) (x 1)
      have hs := sosPoly_nonneg (squares := c.witness.decay_sos)
        (fun s hs => h.2.2.2.1 s (by simp [hs])) (x 0) (x 1)
      simp only [Witness.decayGap, eval_append, eval_scale, Rat.cast_neg, Rat.cast_one] at hz
      rw [c.witness.energy_lie]
      simp only [Witness.energy]
      linarith }

/-- An accepted certificate proves global exponential stability of the full polynomial field. -/
@[powerlib_foundation, aesop unsafe 80% apply]
private theorem Certificate.globallyExponentiallyStable {model : Model}
    (c : Certificate model) : Flow.GloballyExponentiallyStable model.field 0 :=
  c.quadraticDecay.globallyExponentiallyStable model.field_smooth

/-! ## The linearization at the origin -/

/-- A coordinate functional. -/
abbrev coord (j : Fin 2) : ℝ² →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) j

@[powerlib_foundation] theorem hasFDerivAt_monomial_zero (c : ℝ) (a b : ℕ) :
    HasFDerivAt (fun x : ℝ² => c * x 0 ^ a * x 1 ^ b)
      ((if (a, b) = (1, 0) then c else 0) • coord 0 +
        (if (a, b) = (0, 1) then c else 0) • coord 1) 0 := by
  have h0 : HasFDerivAt (fun x : ℝ² => x 0) (coord 0) 0 := (coord 0).hasFDerivAt
  have h1 : HasFDerivAt (fun x : ℝ² => x 1) (coord 1) 0 := (coord 1).hasFDerivAt
  have h := ((hasFDerivAt_const c (0 : ℝ²)).mul (h0.pow a)).mul (h1.pow b)
  convert h using 1
  ext v
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [pow_succ]

/-- At the origin a polynomial has the derivative of its linear terms. -/
@[powerlib_foundation] theorem hasFDerivAt_eval_zero (p : Polynomial) :
    HasFDerivAt (fun x : ℝ² => eval p (x 0) (x 1))
      ((coeff p (1, 0) : ℝ) • coord 0 + (coeff p (0, 1) : ℝ) • coord 1) 0 := by
  induction p with
  | nil => simpa [coeff] using hasFDerivAt_const (0 : ℝ) (0 : ℝ²)
  | cons t ts ih =>
    have h := (hasFDerivAt_monomial_zero t.coefficient t.powers.1 t.powers.2).add ih
    convert h using 1
    · rfl
    · ext v
      simp only [coeff_cons, Prod.mk.eta, Rat.cast_add]
      split_ifs <;> simp_all <;> ring

/-- The linearization at the origin: the matrix of linear coefficients. -/
def Model.linearization (model : Model) : Matrix (Fin 2) (Fin 2) ℝ :=
  Linear.Synthesis.real model.linearPart

/-- The linearization is the Jacobian of the field at the origin. -/
@[powerlib_foundation] theorem hasFDerivAt_field_zero (model : Model) :
    HasFDerivAt model.field
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) model.linearization) 0 := by
  have hpi : HasFDerivAt
      (fun x : ℝ² => ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)])
      (ContinuousLinearMap.pi fun i =>
        ![(coeff model.field0 (1, 0) : ℝ) • coord 0 + (coeff model.field0 (0, 1) : ℝ) • coord 1,
          (coeff model.field1 (1, 0) : ℝ) • coord 0 + (coeff model.field1 (0, 1) : ℝ) • coord 1]
          i) 0 := by
    refine hasFDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa using hasFDerivAt_eval_zero model.field0
    · simpa using hasFDerivAt_eval_zero model.field1
  have h :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp (0 : ℝ²) hpi
  have hfun : model.field = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
      fun x : ℝ² => ![eval model.field0 (x 0) (x 1), eval model.field1 (x 0) (x 1)] := rfl
  rw [hfun]
  refine h.congr_fderiv ?_
  ext v i
  fin_cases i <;>
    simp [Model.linearization, Model.linearPart, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Without constant terms the origin is an equilibrium. -/
@[powerlib_foundation] theorem Model.field_eq_zero (model : Model)
    (h : coeff model.field0 (0, 0) = 0 ∧ coeff model.field1 (0, 0) = 0) : model.field 0 = 0 := by
  ext i
  fin_cases i <;> simp [eval_zero, h.1, h.2]

/-! ## The family -/

open LinearSystems

/-- Requirements on the polynomial models. -/
inductive Requirement
  | equilibrium
  | linearizationHurwitz
  | linearizationUnstable
  | certified
  | decayRateAtLeast (a : ℝ)

/-- Satisfaction of a requirement by a model. -/
def Meets (model : Model) : Requirement → Prop
  | .equilibrium => coeff model.field0 (0, 0) = 0 ∧ coeff model.field1 (0, 0) = 0
  | .linearizationHurwitz => IsHurwitz model.linearization
  | .linearizationUnstable =>
    ∃ s : ℂ, (Linear.characteristicMatrix model.linearization s).det = 0 ∧ 0 < s.re
  | .certified => Nonempty (Certificate model)
  | .decayRateAtLeast a => ∃ c : Certificate model, a ≤ (c.witness.rate : ℝ) / 2

/-- The translation of the sentences: the local ones into an equilibrium with a Hurwitz
linearization, instability into one with a right-half-plane root, the global ones into a
certificate, a decay rate into a certificate with that rate. Conservation is translated into the
whole language, which no model meets; passivity needs no requirement. -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.equilibrium, .linearizationHurwitz}
  | .flow .unstable => {.equilibrium, .linearizationUnstable}
  | .flow (.decay a) => {.decayRateAtLeast a}
  | .flow .conservative => Set.univ
  | .flow _ => {.certified}
  | .passive => ∅

/-- The polynomial family: every model read as its autonomous field. -/
def family : Family Model Requirement 2 0 :=
  ⟨fun model => Port.System.autonomous model.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

@[aesop norm -1 apply (index := [unindexed])] theorem Certificate.mem_den {model : Model} (c : Certificate model) :
    connection% (model ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr c.globallyExponentiallyStable

/-- No model has a Hurwitz linearization with a right-half-plane root. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext model
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨s, hs, hre⟩ := h .linearizationUnstable
  have hH : IsHurwitz model.linearization := h .linearizationHurwitz
  exact absurd ((Linear.spectrallyStable_iff_isHurwitz _).mpr hH s hs) (not_lt.mpr hre.le)

/-- An equilibrium with a Hurwitz linearization is locally exponentially stable (LeanForControl's
linearization theorem). -/
@[powerlib_foundation] private theorem locallyExponentiallyStable_of_linearization (model : Model)
    (h : coeff model.field0 (0, 0) = 0 ∧ coeff model.field1 (0, 0) = 0)
    (hH : IsHurwitz model.linearization) : LocallyExponentiallyStable model.field 0 :=
  hurwitz_linearization_locally_exponentially_stable model.linearization model.field_smooth
    (model.field_eq_zero h) (hasFDerivAt_field_zero model).fderiv hH

/-- An equilibrium whose linearization has a right-half-plane root is unstable (LeanForControl's
indirect method). -/
@[powerlib_foundation] private theorem unstable_of_linearization (model : Model)
    (h : coeff model.field0 (0, 0) = 0 ∧ coeff model.field1 (0, 0) = 0) {s : ℂ}
    (hs : (Linear.characteristicMatrix model.linearization s).det = 0) (hre : 0 < s.re) :
    Unstable model.field 0 := by
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root hs
  exact unstable_of_exists_complex_eigenvalue_re_pos model.linearization model.field_smooth
    (model.field_eq_zero h) (hasFDerivAt_field_zero model).fderiv ⟨s, v, hv, heig, hre⟩

/-- Every translation of the polynomial family is sound: its translation chain lies below its
semantics connection. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s model hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets model q at hm
  have hlocal : ∀ (Γ : Set Requirement), Γ = {.equilibrium, .linearizationHurwitz} →
      (∀ q ∈ Γ, Meets model q) → LocallyExponentiallyStable model.field 0 := by
    rintro Γ rfl h
    exact locallyExponentiallyStable_of_linearization model (h .equilibrium (by simp))
      (h .linearizationHurwitz (by simp))
  rcases s with P | _
  · rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable => exact (hlocal _ rfl hm).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable (hlocal _ rfl hm)
    case locallyExponentiallyStable => exact hlocal _ rfl hm
    case unstable =>
      obtain ⟨s, hs, hre⟩ := hm .linearizationUnstable (by simp [translate])
      exact unstable_of_linearization model (hm .equilibrium (by simp [translate])) hs hre
    case decay a =>
      obtain ⟨c, hc⟩ := hm (.decayRateAtLeast a) rfl
      exact c.quadraticDecay.decay.mono hc
    case conservative =>
      have : model ∈ TMIO.realize Meets Set.univ :=
        (TMIO.mem_realize _ _ _).mpr fun q _ => hm q trivial
      rw [realize_univ] at this
      exact this.elim
    case globallyAsymptoticallyStable =>
      obtain ⟨c⟩ := hm .certified rfl
      exact c.globallyExponentiallyStable.globallyAsymptoticallyStable
    case globallyExponentiallyStable =>
      obtain ⟨c⟩ := hm .certified rfl
      exact c.globallyExponentiallyStable
    case contractive =>
      obtain ⟨c⟩ := hm .certified rfl
      exact c.globallyExponentiallyStable.sampledContraction
  · rw [family_isAutonomous.den_passive]
    trivial

/-! ## Where the connections part -/

/-- Cubic damping `x' = -x³`, `y' = -y³`: no linear part. -/
def cubicModel : Model := ⟨[⟨-1, (3, 0)⟩], [⟨-1, (0, 3)⟩]⟩

@[powerlib_foundation] theorem cubicModel_field (x : ℝ²) :
    cubicModel.field x = WithLp.toLp 2 ![-(x 0) ^ 3, -(x 1) ^ 3] := by
  ext i
  fin_cases i <;> simp [Model.field, cubicModel]

/-- Cubic damping is globally asymptotically stable: `‖x‖²` is a strict Lyapunov function with
compact sublevels. -/
@[powerlib_foundation] private theorem cubicModel_globallyAsymptoticallyStable :
    Flow.GloballyAsymptoticallyStable cubicModel.field 0 := by
  refine Flow.globallyAsymptoticallyStable_of_strictLyapunov (V := fun x : ℝ² => ‖x‖ ^ 2)
    two_pos cubicModel.field_smooth ⟨by fun_prop, contDiff_norm_sq ℝ, by simp,
      fun x hx => by positivity, by simp [cubicModel_field], fun x hx => ?_, fun c => ?_⟩
  · rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
    simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
    rw [cubicModel_field]
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
    have hinner : inner ℝ x (WithLp.toLp 2 ![-(x 0) ^ 3, -(x 1) ^ 3]) =
        -(x 0 ^ 4 + x 1 ^ 4) := by
      simp [PiLp.inner_apply, Fin.sum_univ_two]
      ring
    rw [hinner]
    rcases hne with h | h
    · have : 0 < x 0 ^ 4 := by positivity
      nlinarith [pow_two_nonneg (x 1 ^ 2)]
    · have : 0 < x 1 ^ 4 := by positivity
      nlinarith [pow_two_nonneg (x 0 ^ 2)]
  · refine (isCompact_closedBall (0 : ℝ²) (Real.sqrt (max c 0))).of_isClosed_subset
      (isClosed_le (by fun_prop) continuous_const) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Real.le_sqrt_of_sq_le (le_max_of_le_left hx)

/-- Cubic damping has no certificate: near the origin it decays slower than any exponential. -/
@[powerlib_foundation] theorem cubicModel_not_certified : IsEmpty (Certificate cubicModel) := by
  refine ⟨fun c => ?_⟩
  have hrate : (0 : ℝ) < c.witness.rate := c.quadraticDecay.rate_pos
  have hlower : (0 : ℝ) < c.witness.lower := c.quadraticDecay.lower_pos
  set t := Real.sqrt ((c.witness.rate : ℝ) / 4) with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = (c.witness.rate : ℝ) / 4 := Real.sq_sqrt (by positivity)
  set x : ℝ² := WithLp.toLp 2 ![t, 0] with hx_def
  have hdiss := c.quadraticDecay.dissipation x
  have hlow := c.quadraticDecay.lower_bound x
  change fderiv ℝ c.witness.energy x (cubicModel.field x) ≤
    -(c.witness.rate : ℝ) * c.witness.energy x at hdiss
  change (c.witness.lower : ℝ) * ‖x - 0‖ ^ 2 ≤ c.witness.energy x at hlow
  rw [c.witness.energy_derivative, c.witness.energy_apply] at hdiss
  rw [c.witness.energy_apply, sub_zero, EuclideanSpace.norm_sq_eq] at hlow
  simp [hx_def, cubicModel_field, Fin.sum_univ_two] at hdiss hlow
  have hp : (0 : ℝ) < c.witness.p00 := by
    have : (c.witness.lower : ℝ) * t ^ 2 ≤ c.witness.p00 * t ^ 2 := by nlinarith
    nlinarith [pow_pos ht 2]
  nlinarith [pow_pos ht 2, mul_pos hp (pow_pos ht 2)]

@[powerlib_foundation] theorem cubicModel_linearization : cubicModel.linearization = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Model.linearization, Model.linearPart, cubicModel, coeff]

/-- The translations of the asymptotic sentences are sound but not exact: cubic damping is
globally, hence locally, asymptotically stable, yet it has no certificate and its linearization
is not Hurwitz. -/
@[powerlib_domain] theorem not_exact_asymptotic :
    connection% (¬ family.Exact (.flow .globallyAsymptoticallyStable) ∧
      ¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hgas := cubicModel_globallyAsymptoticallyStable
  constructor
  · intro h
    have hmem : cubicModel ∈ family.den (.flow .globallyAsymptoticallyStable) :=
      family_isAutonomous.mem_den_flow.mpr hgas
    rw [← h, TMIO.mem_realize] at hmem
    obtain ⟨c⟩ : Nonempty (Certificate cubicModel) := hmem .certified rfl
    exact cubicModel_not_certified.false c
  · intro h
    have hmem : cubicModel ∈ family.den (.flow .locallyAsymptoticallyStable) :=
      family_isAutonomous.mem_den_flow.mpr hgas.localAsymptoticStable
    rw [← h, TMIO.mem_realize] at hmem
    have hH : IsHurwitz cubicModel.linearization := hmem .linearizationHurwitz
      (show _ ∈ ({.equilibrium, .linearizationHurwitz} : Set Requirement) from Or.inr rfl)
    rw [cubicModel_linearization] at hH
    have := hH 0 ![1, 0] (by simp [funext_iff])
      (by ext i; simp [Matrix.mulVec, dotProduct, Matrix.map_apply])
    simp at this

end

/-! The cascade boundary is stronger than a failed synthesis run: it has global asymptotic
stability but no uniform global exponential estimate, so no certificate of this language exists. -/

def cascadeModel : Model := ⟨[⟨-2, (1, 0)⟩, ⟨1, (0, 2)⟩], [⟨-1, (0, 1)⟩]⟩

@[powerlib_foundation] theorem cascadeModel_field (x : ℝ²) :
    cascadeModel.field x = WithLp.toLp 2 ![-2 * x 0 + (x 1) ^ 2, -x 1] := by
  ext i
  fin_cases i <;> simp [Model.field, cascadeModel]

noncomputable def cascadeEnergy (x : ℝ²) : ℝ := ‖x‖ ^ 2 + (x 1) ^ 4

@[powerlib_foundation] theorem cascadeEnergy_lie (x : ℝ²) :
    fderiv ℝ cascadeEnergy x (cascadeModel.field x) =
      -4 * (x 0) ^ 2 + 2 * x 0 * (x 1) ^ 2 - 2 * (x 1) ^ 2 - 4 * (x 1) ^ 4 := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.add
    (((coord 1).hasFDerivAt (x := x)).pow 4)
  change HasFDerivAt cascadeEnergy _ x at h
  rw [h.fderiv]
  simp [coord, cascadeModel_field, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- A quartic energy proves global asymptotic stability through the family's denotation. -/
@[powerlib_domain] theorem cascade_asymptotic :
    connection% (cascadeModel ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  refine Flow.globallyAsymptoticallyStable_of_strictLyapunov (V := cascadeEnergy)
    two_pos cascadeModel.field_smooth ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_norm.pow 2).add ((coord 1).continuous.pow 4)
  · exact (contDiff_norm_sq ℝ).add ((coord 1).contDiff.pow 4)
  · simp [cascadeEnergy]
  · intro x hx
    have : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    dsimp [cascadeEnergy]
    positivity
  · simp [cascadeModel_field]
  · intro x hx
    rw [cascadeEnergy_lie]
    have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
    rcases hn with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 - (x 1) ^ 2),
        sq_nonneg (x 1), sq_nonneg ((x 1) ^ 2)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 - (x 1) ^ 2),
        sq_nonneg (x 0), sq_nonneg ((x 1) ^ 2)]
  · intro c
    refine (isCompact_closedBall (0 : ℝ²) (Real.sqrt (max c 0))).of_isClosed_subset
      (isClosed_le ((continuous_norm.pow 2).add ((coord 1).continuous.pow 4)) continuous_const)
      fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    have hn : ‖x‖ ^ 2 ≤ c := by
      change ‖x‖ ^ 2 + (x 1) ^ 4 ≤ c at hx
      nlinarith [sq_nonneg ((x 1) ^ 2)]
    exact le_max_of_le_left hn

/-- The quadratic transient from `(0,N)` grows like `N²`; one global linear-in-state
exponential bound cannot cover every initial state. -/
@[powerlib_domain] theorem cascade_not_exponential :
    connection% (cascadeModel ∉ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  rintro ⟨_, _, C, a, hC, ha, hb⟩
  let N := C * Real.exp (-a) * Real.exp 2 + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let φ : ℝ → ℝ² := fun t => WithLp.toLp 2
    ![Real.exp (-2 * t) * (t * N ^ 2), Real.exp (-t) * N]
  have hφ : IsTrajectoryOn φ cascadeModel.field 0 1 := by
    intro t ht
    have h0 := (((hasDerivAt_id t).const_mul (-2)).exp).mul
      ((hasDerivAt_id t).mul_const (N ^ 2))
    have h1 := ((hasDerivAt_id t).neg.exp).mul_const N
    have hd : HasDerivAt φ (WithLp.toLp 2
        ![Real.exp (-2 * t) * (-2) * (t * N ^ 2) + Real.exp (-2 * t) * N ^ 2,
          Real.exp (-t) * (-1) * N]) t := by
      convert (h0.smul_const ((EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) : ℝ²)).add
        (h1.smul_const ((EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) : ℝ²)) using 1
      · funext z
        ext i
        fin_cases i <;> simp [φ, EuclideanSpace.single]
      · ext i
        fin_cases i <;> simp [EuclideanSpace.single]
    have hexp : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    change HasDerivWithinAt φ (cascadeModel.field (φ t)) (Set.Icc 0 1) t
    convert hd.hasDerivWithinAt using 1
    ext i
    fin_cases i <;> simp [φ, cascadeModel_field, mul_pow, hexp]
    ring
  have hinit : φ 0 = EuclideanSpace.single 1 N := by
    ext i
    fin_cases i <;> simp [φ, EuclideanSpace.single]
  have hnorm : ‖φ 0 - 0‖ = N := by
    rw [sub_zero, hinit]
    simp [Real.norm_eq_abs, abs_of_pos hN]
  have hbound := hb 0 1 φ hφ 1 ⟨by norm_num, le_rfl⟩
  rw [hnorm, sub_zero] at hbound
  norm_num only [sub_zero, mul_one] at hbound
  have hfirst : Real.exp (-2) * N ^ 2 ≤ ‖φ 1‖ := by
    have h := PiLp.norm_apply_le (φ 1) (0 : Fin 2)
    simpa [φ, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-2) * N ^ 2)] using h
  have hlinear : Real.exp (-2) * N ≤ C * Real.exp (-a) := by
    apply (mul_le_mul_iff_right₀ hN).mp
    nlinarith [hfirst.trans hbound]
  have hexp : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
  have hvalue : Real.exp (-2) * N = C * Real.exp (-a) + Real.exp (-2) := by
    dsimp [N]
    calc
      _ = C * Real.exp (-a) * (Real.exp (-2) * Real.exp 2) + Real.exp (-2) := by ring
      _ = _ := by rw [hexp]; ring
  rw [hvalue] at hlinear
  linarith [Real.exp_pos (-2)]

/-- This model is outside the certificate requirement space despite being in global asymptotic
semantics. It is a proved limitation of the certificate language, not just of its search. -/
@[powerlib_domain] theorem cascade_certificate_boundary :
    connection% (cascadeModel ∈ family.den (.flow .globallyAsymptoticallyStable) ∧
      cascadeModel ∉ TMIO.realize Meets {.certified}) := by
  unfold powerlib.TMIO.Statement
  refine ⟨cascade_asymptotic, ?_⟩
  intro h
  have hc : Nonempty (Certificate cascadeModel) := (TMIO.mem_realize _ _ _).mp h .certified rfl
  obtain ⟨c⟩ := hc
  exact cascade_not_exponential (family_isAutonomous.mem_den_flow.mpr c.globallyExponentiallyStable)

@[powerlib_foundation] theorem cascade_rejected : accepts cascadeModel = false := by decide +kernel

/-! Global exponential semantics is also strictly larger than the quadratic certificate
language. A quartic Hamiltonian rotation with linear damping is the separating example. -/

def quarticModel : Model :=
  ⟨[⟨-1, (1, 0)⟩, ⟨-1, (0, 3)⟩], [⟨-1, (0, 1)⟩, ⟨1, (3, 0)⟩]⟩

@[powerlib_foundation] theorem quarticModel_field (x : ℝ²) :
    quarticModel.field x = WithLp.toLp 2 ![-x 0 - (x 1) ^ 3, -x 1 + (x 0) ^ 3] := by
  ext i
  fin_cases i <;> simp [Model.field, quarticModel]
  ring

def quarticEnergy (x : ℝ²) : ℝ := (x 0) ^ 4 + (x 1) ^ 4

@[powerlib_foundation] theorem quarticEnergy_smooth : ContDiff ℝ 1 quarticEnergy :=
  ((coord 0).contDiff.pow 4).add ((coord 1).contDiff.pow 4)

@[powerlib_foundation] theorem quarticEnergy_lie (x : ℝ²) :
    fderiv ℝ quarticEnergy x (quarticModel.field x) = -4 * quarticEnergy x := by
  have h := (((coord 0).hasFDerivAt (x := x)).pow 4).add
    (((coord 1).hasFDerivAt (x := x)).pow 4)
  change HasFDerivAt quarticEnergy _ x at h
  rw [h.fderiv]
  simp [quarticEnergy, quarticModel_field, coord]
  ring

@[powerlib_foundation] theorem quarticEnergy_bounds (x : ℝ²) :
    quarticEnergy x ≤ ‖x‖ ^ 4 ∧ ‖x‖ ^ 4 ≤ 2 * quarticEnergy x := by
  have hn : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hn4 : ‖x‖ ^ 4 = ((x 0) ^ 2 + (x 1) ^ 2) ^ 2 := by
    rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring, hn]
  rw [hn4]
  dsimp [quarticEnergy]
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1))]
  · nlinarith [sq_nonneg ((x 0) ^ 2 - (x 1) ^ 2)]

@[powerlib_foundation] theorem quarticEnergy_compact (c : ℝ) :
    IsCompact {x : ℝ² | quarticEnergy x ≤ c} := by
  refine (isCompact_closedBall (0 : ℝ²) (Real.sqrt (2 * max c 0 + 1))).of_isClosed_subset
    (isClosed_le quarticEnergy_smooth.continuous continuous_const) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  apply Real.le_sqrt_of_sq_le
  have h := (quarticEnergy_bounds x).2.trans (mul_le_mul_of_nonneg_left hx (by norm_num))
  have hmax : c ≤ max c 0 := le_max_left _ _
  nlinarith [sq_nonneg ‖x‖, le_max_right c 0]

/-- Linear damping of the quartic rotation has a global exponential state bound. -/
@[powerlib_domain] theorem quartic_exponential :
    connection% (quarticModel ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  have hd : ∀ x, fderiv ℝ quarticEnergy x (quarticModel.field x) ≤ -4 * quarticEnergy x :=
    fun x => (quarticEnergy_lie x).le
  have hfc := Flow.forwardComplete_of_compact_sublevel quarticModel.field_smooth
    (quarticEnergy_smooth.differentiable (by norm_num))
    (fun x => by rw [quarticEnergy_lie]; exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by dsimp [quarticEnergy]; positivity))
    quarticEnergy_compact
  refine ⟨by rw [IsEquilibrium, quarticModel_field]; ext i; fin_cases i <;> simp, hfc, 2, 1, by norm_num, one_pos,
    fun t₀ t₁ φ hφ t ht => ?_⟩
  have he := Flow.energy_bound_of_dissipation quarticEnergy_smooth hd hφ ht
  have hfour : ‖φ t‖ ^ 4 ≤ 2 * Real.exp (-(4 * (t - t₀))) * ‖φ t₀‖ ^ 4 :=
    ((quarticEnergy_bounds (φ t)).2.trans
      (mul_le_mul_of_nonneg_left he (by norm_num))).trans (by
        nlinarith [mul_le_mul_of_nonneg_left (quarticEnergy_bounds (φ t₀)).1
          (Real.exp_nonneg (-(4 * (t - t₀))))])
  have hexp : Real.exp (-(t - t₀)) ^ 4 = Real.exp (-(4 * (t - t₀))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  let B := 2 * Real.exp (-(t - t₀)) * ‖φ t₀‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfourB : ‖φ t‖ ^ 4 ≤ B ^ 4 := by
    dsimp [B]
    rw [mul_pow, mul_pow, hexp]
    nlinarith [Real.exp_nonneg (-(4 * (t - t₀))), pow_nonneg (norm_nonneg (φ t₀)) 4]
  have hsquared : ‖φ t‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (sq_nonneg ‖φ t‖) (sq_nonneg B)).mp (by nlinarith [hfourB])
  have hnorm : ‖φ t‖ ≤ B := (sq_le_sq₀ (norm_nonneg _) hB).mp hsquared
  simpa [B] using hnorm

/-- A uniformly bounded quadratic growth coefficient cannot be positive. -/
@[powerlib_foundation] theorem nonpos_of_sq_bound {a b : ℝ}
    (h : ∀ s : ℝ, 0 < s → a * s ^ 2 ≤ b) : a ≤ 0 := by
  by_contra ha
  have ha : 0 < a := lt_of_not_ge ha
  let s := Real.sqrt ((max b 0 + 1) / a)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = (max b 0 + 1) / a := Real.sq_sqrt (by positivity)
  have hb := h s hs
  rw [hs2] at hb
  have he : a * ((max b 0 + 1) / a) = max b 0 + 1 := by field_simp
  rw [he] at hb
  linarith [le_max_left b 0]

/-- A quadratic certificate forces every homogeneous quartic coefficient nonpositive. -/
@[powerlib_foundation] theorem quartic_leading_nonpos (c : Certificate quarticModel) (u v : ℝ) :
    2 * (c.witness.p01 : ℝ) * (u ^ 4 - v ^ 4) +
      2 * (c.witness.p11 : ℝ) * u ^ 3 * v -
      2 * (c.witness.p00 : ℝ) * u * v ^ 3 ≤ 0 := by
  apply nonpos_of_sq_bound (b := (2 - (c.witness.rate : ℝ)) *
    c.witness.energy (WithLp.toLp 2 ![u, v]))
  intro s hs
  let x : ℝ² := WithLp.toLp 2 ![s * u, s * v]
  have he : c.witness.energy x = s ^ 2 * c.witness.energy (WithLp.toLp 2 ![u, v]) := by
    rw [c.witness.energy_apply, c.witness.energy_apply]
    simp [x]
    ring
  have hl : fderiv ℝ c.witness.energy x (quarticModel.field x) =
      -2 * s ^ 2 * c.witness.energy (WithLp.toLp 2 ![u, v]) + s ^ 4 *
        (2 * (c.witness.p01 : ℝ) * (u ^ 4 - v ^ 4) +
          2 * (c.witness.p11 : ℝ) * u ^ 3 * v -
          2 * (c.witness.p00 : ℝ) * u * v ^ 3) := by
    rw [c.witness.energy_derivative, c.witness.energy_apply]
    simp [quarticModel_field, x]
    ring
  have h := c.quadraticDecay.dissipation x
  change fderiv ℝ c.witness.energy x (quarticModel.field x) ≤
    -(c.witness.rate : ℝ) * c.witness.energy x at h
  rw [he, hl] at h
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp
  nlinarith [h]

/-- The quadratic certificate language cannot describe this global exponential model. -/
@[powerlib_domain] theorem quartic_certificate_boundary :
    connection% (quarticModel ∈ family.den (.flow .globallyExponentiallyStable) ∧
      quarticModel ∉ TMIO.realize Meets {.certified}) := by
  unfold powerlib.TMIO.Statement
  refine ⟨quartic_exponential, ?_⟩
  intro h
  obtain ⟨c⟩ : Nonempty (Certificate quarticModel) := (TMIO.mem_realize _ _ _).mp h .certified rfl
  have hp := c.quadraticDecay.lower_bound (WithLp.toLp 2 ![1, 0])
  change (c.witness.lower : ℝ) * ‖(WithLp.toLp 2 ![1, 0] : ℝ²) - 0‖ ^ 2 ≤
    c.witness.energy (WithLp.toLp 2 ![1, 0]) at hp
  rw [sub_zero, EuclideanSpace.norm_sq_eq, c.witness.energy_apply] at hp
  simp [Fin.sum_univ_two] at hp
  have h0 := quartic_leading_nonpos c 1 0
  have h1 := quartic_leading_nonpos c 0 1
  have h2 := quartic_leading_nonpos c 1 1
  have h3 := quartic_leading_nonpos c 1 (-1)
  have h4 := quartic_leading_nonpos c 1 2
  have h5 := quartic_leading_nonpos c 1 (-2)
  norm_num at h0 h1 h2 h3 h4 h5
  have hp0 : (0 : ℝ) < c.witness.lower := c.quadraticDecay.lower_pos
  have hq0 : (c.witness.p01 : ℝ) = 0 := by linarith
  have hrp : (c.witness.p11 : ℝ) = c.witness.p00 := by exact_mod_cast le_antisymm h2 h3
  rw [hq0, hrp] at h4 h5
  have hpl : (c.witness.lower : ℝ) ≤ c.witness.p00 := by exact_mod_cast hp
  nlinarith only [h5, hpl, hp0]

/-- The global exponential translation is refuted as exact, independently of search failure. -/
@[powerlib_domain] theorem not_exact_exponential :
    connection% (¬ family.Exact (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := quartic_certificate_boundary.1
  rw [← h] at hmem
  exact quartic_certificate_boundary.2 hmem


/-- The same quartic model contracts at an integer horizon, although no certificate represents it. -/
@[powerlib_domain] theorem not_exact_contractive :
    connection% (¬ family.Exact (.flow .contractive)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem : quarticModel ∈ family.den (.flow .contractive) :=
    family_isAutonomous.mem_den_flow.mpr
      ((family_isAutonomous.mem_den_flow.mp quartic_exponential).sampledContraction)
  rw [← h] at hmem
  exact quartic_certificate_boundary.2 hmem


end powerlib.Nonlinear.Polynomial2
