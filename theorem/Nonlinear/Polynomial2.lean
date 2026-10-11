import theorem.Flow.Certificate
import theorem.Linear.Synthesis

/-! # Two-state polynomial fields with sum-of-squares certificates

Model boundary: autonomous fields `x' = f(x)` on `ℝ²` whose two components are polynomials with
rational coefficients, in continuous time, without input, delay or switching. The equilibrium is
the origin.

A model enters the library through its field map; every sentence is the Flow semantics pulled
back along it (`Flow.den Model.field 0`). A certificate is rational data — a quadratic energy, two
bounds, a decay rate and three weighted sums of squares — accepted by an exact check: the three
polynomial identities are compared coefficient by coefficient and the weights must be
nonnegative. The check is a boolean computation whose soundness is a theorem; an accepted
certificate is a quadratic-decay certificate and therefore proves forward completeness and global
exponential stability.

The synthesizer proposes the data from the model alone. The energy is taken from a fixed family —
the solution of the Lyapunov equation of the linearization (`Linear.Synthesis`), then diagonal
energies — the bounds and the rate come from eigenvalue bounds, and each sum of squares is the
`L D Lᵀ` factorization of a Gram matrix of canonical shape. It is not trusted: whatever it
proposes is checked. It succeeds when some energy of the family makes the higher-order terms
dissipative and the decay polynomial admits a Gram matrix of that shape; otherwise it proposes
nothing, which proves nothing. -/

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
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : ℝ² →L[ℝ] ℝ).contDiff

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

@[powerlib_foundation] theorem norm_sq (x : ℝ²) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ, sq_abs]

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
@[powerlib_domain, aesop unsafe 80% apply]
theorem Certificate.globallyExponentiallyStable {model : Model}
    (c : Certificate model) : Flow.GloballyExponentiallyStable model.field 0 :=
  c.quadraticDecay.globallyExponentiallyStable model.field_smooth

/-- An accepted certificate places the model in the denotation of every attractive sentence. -/
@[powerlib_domain] theorem Certificate.mem_den {model : Model} (c : Certificate model)
    {P : Flow.Property} (hP : P.Attractive) : model ∈ Flow.den Model.field 0 P :=
  c.quadraticDecay.mem_den model.field_smooth hP

/-- A model accepted by the synthesizer satisfies every attractive sentence. -/
@[powerlib_domain] theorem mem_den_of_accepts {model : Model} (h : accepts model = true)
    {P : Flow.Property} (hP : P.Attractive) : model ∈ Flow.den Model.field 0 P :=
  (certificateOf model h).mem_den hP

end

end powerlib.Nonlinear.Polynomial2
