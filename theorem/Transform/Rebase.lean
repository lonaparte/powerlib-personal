import theorem.Circuits.Interconnection
import theorem.Dynamics.Calculus
import theorem.Dynamics.Transport
import theorem.Linear.EigenMap
import theorem.LTI.Plant
import theorem.TMIO.ClaimElab

/-! # Changes of bases of linear port models

Scope.
A change of bases of a continuous-time linear plant `x' = A x + B u`, `y = C x + D u`: new state
coordinates `x̂ = T x` with left inverse `S` (`S T = 1`), a time base `w` (`τ = w t`), new input
coordinates `u = S_u û` and new output coordinates `ŷ = T_y y`. The rebased plant is
`(w⁻¹ T A S, w⁻¹ T B S_u, T_y C S, T_y D S_u)` (`plant`). For a source–load interconnection
(`Circuits.Interconnection`) the two plants share the port bases: the source reads the port
current and writes the port voltage, the load the reverse (`Bases`, `interconnection`). State
coordinate changes (`w = 1`, ports unchanged), per-unit bases (diagonal; the instance is
`theorem/Transform/PerUnitLTI.lean`), the current direction convention (port current coordinate
`−1`, `flipCurrent`) and the time base are instances, alone or together.

Scaffold: `theorem/Rebase.agda`. Over six spaces (the two state spaces, their rate spaces, port
voltage and port current) it transports the interconnection along the equivalences of the spaces
and shows that the closed loop commutes with every change of bases, provided the equivalences
preserve the additive operations. Here the maps are matrices, so the operations are preserved by
linearity, and the statement is proved through typed constructions (`Construction`) and one
naturality theorem (`Construction.eval_rebase`): a construction of rebased matrices is the rebased
construction whenever the bases of the spaces it passes through are invertible.

Source: work-sync `theory/T-PU.md` §1.2, §1.6, §1.11 (state and time bases, per-unit impedance);
`conventions.md` §D1, §D8 (IN-positive current, translation of the direction convention);
`theory/T-gfl-impedance.md` §2.2 (`Y^IN = −Y^OUT`).

Results.
* Constructions (generic): `Construction`, `Construction.eval`, `Construction.inner` (the spaces a
  construction passes through), `Construction.rebase`; `Construction.eval_rebase` (naturality).
* Matrices and plants: `rebaseMatrix` (`w⁻¹ T A S`); solutions correspond
  (`solves_rebaseMatrix_iff`, `τ = w t`, `x̂ = T x`); spectral stability, the Hurwitz property and
  the attractive sentences are invariant for `w > 0` (`spectrallyStable_rebaseMatrix_iff`,
  `isHurwitz_rebaseMatrix_iff`, `holds_rebaseMatrix_iff`), every flow sentence for `w = 1`
  (`holds_rebaseMatrix_one_iff`), and for every `w > 0` every flow sentence with its decay rate
  scaled by `w` (`holds_rebaseMatrix_timeScale_iff`, through the time-scaling law
  `Dynamics.holds_timeScale_linear_iff`); `transfer_rebase`: `Ĝ(ŝ) = T_y G(w ŝ) S_u`. Scaling and
  similarity of spectra are the generic eigenvalue maps of `theorem/Linear/EigenMap.lean`
  (`spectrallyStable_smul_iff`, `spectrallyStable_conj_iff`).
* Interconnections: the closed-loop state, input and output blocks of the rebased components are
  the rebased blocks (`closedLoopBlocks_rebase`, `inputBlocks_rebase`, `outputBlocks_rebase`; only
  the port bases need inverses), hence the closed loop is the rebased closed loop
  (`closedLoop_rebase`); the source impedance and load admittance change bases
  (`sourceImpedance_rebase`, `loadAdmittance_rebase`), the return difference is only
  re-parametrized (`returnDifference_rebase`), so the impedance criterion
  (`impedanceStable_rebase_iff`) and closed-loop pole stability
  (`isHurwitz_closedLoop_rebase_iff`) are invariant for `w > 0`.
* Instances: state coordinate changes are rebasings (`changeCoordinates_eq`); the current
  direction convention `flipCurrent` reverses the injected current and leaves the closed-loop
  state matrix unchanged (`closedLoop_flipCurrent`), negates the source impedance and the load
  admittance (`sourceImpedance_flipCurrent`, `loadAdmittance_flipCurrent`) and keeps the return
  difference (`returnDifference_flipCurrent`). Reversing the output sign of one plant,
  `LTI.negOutput` (`Y^IN = −Y^OUT`), is the output basis `−1` (`plant_negOutput`). Port passivity
  is not preserved by a change of port bases (reversing the current reverses the supplied power)
  and is not claimed.
* Port bases over any commutative ring: `det_one_add_mul_rebase`, `det(1 + (T_v Z S_i)(T_i Y S_v))
  = det(1 + Z Y)`; complex bases such as the dq ↔ sequence form
  (`Transform.returnDifference_toSeq`) are instances.

Family and connection conclusions.
* `den_rebase`: on the interconnection family, the denotation of every attractive sentence and of
  sampled contraction is its own pull-back along any change of bases with invertible bases and
  positive time base.
* `den_rebase_unitTime`: with the time base `1`, every flow sentence.
* `den_rebase_timeScale`: with any positive time base `w`, every flow sentence, rescaled: the
  rebased interconnections satisfying `P` are those whose original satisfies `P.timeScale w` (a
  decay rate `a` per unit of `τ = w t` is the rate `w a` per unit of `t`; the other sentences are
  unchanged).
* `den_flipCurrent`: the two current direction conventions denote the same interconnections for
  every flow sentence.
-/

noncomputable section

namespace powerlib.Transform.Rebase

open Matrix Linear LinearSystems powerlib.Circuits

/-! ## Constructions and their naturality -/

section Construction

variable {σ : Type}

/-- Typed constructions from primitive maps `Atom a b` (from the space `b` to the space `a`):
products through a common space, negation and differences. -/
inductive Construction (Atom : σ → σ → Type) : σ → σ → Type
  | atom {a b : σ} : Atom a b → Construction Atom a b
  | mul {a b c : σ} : Construction Atom a b → Construction Atom b c → Construction Atom a c
  | neg {a b : σ} : Construction Atom a b → Construction Atom a b
  | sub {a b : σ} : Construction Atom a b → Construction Atom a b → Construction Atom a b

namespace Construction

variable {Atom : σ → σ → Type} (dim : σ → ℕ)

/-- The matrix of a construction, from matrices of its primitive maps. -/
def eval (M : ∀ a b, Atom a b → Matrix (Fin (dim a)) (Fin (dim b)) ℝ) :
    ∀ {a b}, Construction Atom a b → Matrix (Fin (dim a)) (Fin (dim b)) ℝ
  | _, _, atom x => M _ _ x
  | _, _, mul e f => eval M e * eval M f
  | _, _, neg e => -eval M e
  | _, _, sub e f => eval M e - eval M f

/-- The spaces a construction passes through: the middle spaces of its products. -/
def inner : ∀ {a b}, Construction Atom a b → Set σ
  | _, _, atom _ => ∅
  | _, _, mul (b := c) e f => insert c (inner e ∪ inner f)
  | _, _, neg e => inner e
  | _, _, sub e f => inner e ∪ inner f

/-- Primitive maps in new bases: `T a` on the target space and `S b` on the source space. -/
def rebase (T S : ∀ a, Matrix (Fin (dim a)) (Fin (dim a)) ℝ)
    (M : ∀ a b, Atom a b → Matrix (Fin (dim a)) (Fin (dim b)) ℝ) :
    ∀ a b, Atom a b → Matrix (Fin (dim a)) (Fin (dim b)) ℝ :=
  fun a b x => T a * M a b x * S b

/-- Naturality: a construction of rebased primitive maps is the rebased construction, provided the
bases of the spaces it passes through are invertible. -/
@[powerlib_foundation] theorem eval_rebase (T S : ∀ a, Matrix (Fin (dim a)) (Fin (dim a)) ℝ)
    (M : ∀ a b, Atom a b → Matrix (Fin (dim a)) (Fin (dim b)) ℝ) {a b : σ}
    (e : Construction Atom a b) (h : ∀ c ∈ e.inner, S c * T c = 1) :
    eval dim (rebase dim T S M) e = T a * eval dim M e * S b := by
  induction e with
  | atom x => rfl
  | @mul a b c e f ihe ihf =>
    have hb : S b * T b = 1 := h b (Set.mem_insert _ _)
    have he := ihe fun d hd => h d (Set.mem_insert_of_mem _ (Or.inl hd))
    have hf := ihf fun d hd => h d (Set.mem_insert_of_mem _ (Or.inr hd))
    change eval dim (rebase dim T S M) e * eval dim (rebase dim T S M) f = _
    rw [he, hf]
    change T a * eval dim M e * S b * (T b * eval dim M f * S c) =
      T a * (eval dim M e * eval dim M f) * S c
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (S b) (T b), hb, Matrix.one_mul]
  | neg e ih =>
    change -eval dim (rebase dim T S M) e = T _ * -eval dim M e * S _
    rw [ih h, Matrix.mul_neg, Matrix.neg_mul]
  | sub e f ihe ihf =>
    change eval dim (rebase dim T S M) e - eval dim (rebase dim T S M) f =
      T _ * (eval dim M e - eval dim M f) * S _
    rw [ihe fun d hd => h d (Or.inl hd), ihf fun d hd => h d (Or.inr hd), Matrix.mul_sub,
      Matrix.sub_mul]

end Construction

end Construction

/-! ## Matrices: scaling and similarity -/

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[powerlib_foundation] theorem inv_smul_matrix {c : ℂ} (hc : c ≠ 0) (M : Matrix ι ι ℂ) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · have := Matrix.inv_smul' M (Units.mk0 c hc) h
    rw [Units.smul_def, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    exact this
  · have h' : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul]
      intro hu
      exact h ((IsUnit.mul_iff.mp hu).2)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h', Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

@[powerlib_foundation] theorem characteristicMatrix_smul {c : ℝ} (hc : c ≠ 0)
    (A : Matrix ι ι ℝ) (s : ℂ) :
    characteristicMatrix (c • A) s = (c : ℂ) • characteristicMatrix A (s / c) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  ext i j
  simp only [characteristicMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply, smul_eq_mul, Complex.coe_algebraMap]
  split_ifs <;> push_cast <;> field_simp

/-- Scaling the state matrix by a positive constant does not change spectral stability (the
eigenvalues scale, `Linear.forall_eigen_smul_iff`). -/
@[powerlib_foundation] theorem spectrallyStable_smul_iff {c : ℝ} (hc : 0 < c) (A : Matrix ι ι ℝ) :
    SpectrallyStable (c • A) ↔ SpectrallyStable A := by
  rw [spectrallyStable_iff_forall_eigen, spectrallyStable_iff_forall_eigen]
  refine (forall_eigen_smul_iff hc.ne' A fun μ => μ.re < 0).trans
    (forall₄_congr fun lam v _ _ => ?_)
  show ((c : ℂ) * lam).re < 0 ↔ lam.re < 0
  rw [Complex.re_ofReal_mul]
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.mpr (mul_nonneg hc.le (not_lt.mp h')))
  · exact mul_neg_of_pos_of_neg hc

/-- A similarity on an arbitrary finite index conjugates the characteristic matrix. -/
@[powerlib_foundation] theorem characteristicMatrix_conj' {T S : Matrix ι ι ℝ} (hTS : T * S = 1)
    (A : Matrix ι ι ℝ) (s : ℂ) :
    characteristicMatrix (T * A * S) s =
      complexify T * characteristicMatrix A s * complexify S := by
  simp only [characteristicMatrix, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, complexify_mul_eq_one hTS]

/-- A similarity on an arbitrary finite index preserves spectral stability (it keeps the
characteristic polynomial, `Linear.spectrallyStable_conj`). -/
@[powerlib_foundation] theorem spectrallyStable_conj_iff {T S : Matrix ι ι ℝ} (_hTS : T * S = 1)
    (hST : S * T = 1) (A : Matrix ι ι ℝ) :
    SpectrallyStable (T * A * S) ↔ SpectrallyStable A :=
  spectrallyStable_conj hST A

omit [DecidableEq ι] in
/-- The square instance of `Dynamics.hasDerivAt_mulVec`. -/
@[powerlib_foundation] theorem hasDerivAt_mulVec (M : Matrix ι ι ℝ) {x : ℝ → ι → ℝ} {x' : ι → ℝ}
    {t : ℝ} (hx : HasDerivAt x x' t) : HasDerivAt (fun s => M *ᵥ x s) (M *ᵥ x') t :=
  Dynamics.hasDerivAt_mulVec M hx

/-- **The return difference does not see the port bases.** For voltage coordinates `T_v` with
inverse `S_v` and current coordinates `T_i` with left inverse `S_i`, over any commutative ring
(complex bases included), `det(1 + (T_v Z S_i)(T_i Y S_v)) = det(1 + Z Y)`. -/
@[powerlib_foundation] theorem det_one_add_mul_rebase {R : Type*} [CommRing R]
    {Tv Sv Ti Si : Matrix ι ι R} (hTv : Tv * Sv = 1) (hSv : Sv * Tv = 1) (hi : Si * Ti = 1)
    (Z Y : Matrix ι ι R) : (1 + Tv * Z * Si * (Ti * Y * Sv)).det = (1 + Z * Y).det := by
  have hconj : 1 + Tv * Z * Si * (Ti * Y * Sv) = Tv * (1 + Z * Y) * Sv := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, hTv]
    rw [← Matrix.mul_assoc Si Ti, hi, Matrix.one_mul]
  rw [hconj, Matrix.det_conj_of_mul_eq_one hTv hSv]

/-! ## The rebased state matrix -/

/-- The state matrix `w⁻¹ T A S` in state coordinates `x̂ = T x` (left inverse `S`) and time
`τ = w t`. -/
def rebaseMatrix (T S : Matrix ι ι ℝ) (w : ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  w⁻¹ • (T * A * S)

variable {T S : Matrix ι ι ℝ} {w : ℝ}

/-- An original solution gives a rebased solution `x̂(τ) = T x(τ / w)`. -/
@[powerlib_foundation] theorem solves_rebaseMatrix_of (hST : S * T = 1) {A : Matrix ι ι ℝ}
    {x : ℝ → ι → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) :
    ∀ τ, HasDerivAt (fun τ => T *ᵥ x (τ / w)) (rebaseMatrix T S w A *ᵥ (T *ᵥ x (τ / w))) τ := by
  intro τ
  have hτ : HasDerivAt (fun τ : ℝ => τ / w) w⁻¹ τ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id τ).mul_const w⁻¹
  have h := hasDerivAt_mulVec T ((hx (τ / w)).scomp τ hτ)
  have hM : rebaseMatrix T S w A * T = w⁻¹ • (T * A) := by
    rw [rebaseMatrix, Matrix.smul_mul, Matrix.mul_assoc (T * A), hST, Matrix.mul_one]
  refine h.congr_deriv ?_
  rw [Matrix.mulVec_mulVec, hM]
  simp [Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- A rebased solution gives an original solution `x(t) = S x̂(w t)`. -/
@[powerlib_foundation] theorem solves_of_rebaseMatrix (hST : S * T = 1) (hw : w ≠ 0)
    {A : Matrix ι ι ℝ} {y : ℝ → ι → ℝ}
    (hy : ∀ τ, HasDerivAt y (rebaseMatrix T S w A *ᵥ y τ) τ) :
    ∀ t, HasDerivAt (fun t => S *ᵥ y (w * t)) (A *ᵥ (S *ᵥ y (w * t))) t := by
  intro t
  have ht : HasDerivAt (fun t : ℝ => w * t) w t := by
    simpa using (hasDerivAt_id t).const_mul w
  have h := hasDerivAt_mulVec S ((hy (w * t)).scomp t ht)
  refine h.congr_deriv ?_
  simp only [rebaseMatrix, Matrix.smul_mulVec, smul_smul,
    mul_inv_cancel₀ hw, one_smul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hST, Matrix.one_mul]

/-- Exact correspondence of the original and the rebased solutions. -/
@[powerlib_foundation] theorem solves_rebaseMatrix_iff (hST : S * T = 1) (hw : w ≠ 0)
    (A : Matrix ι ι ℝ) (x : ℝ → ι → ℝ) :
    (∀ t, HasDerivAt x (A *ᵥ x t) t) ↔
      ∀ τ, HasDerivAt (fun τ => T *ᵥ x (τ / w)) (rebaseMatrix T S w A *ᵥ (T *ᵥ x (τ / w))) τ := by
  refine ⟨solves_rebaseMatrix_of hST, fun h => ?_⟩
  have h' := solves_of_rebaseMatrix hST hw h
  simp only [Matrix.mulVec_mulVec, hST, Matrix.one_mulVec, mul_div_cancel_left₀ _ hw] at h'
  exact h'

@[powerlib_foundation] theorem spectrallyStable_rebaseMatrix_iff (hTS : T * S = 1)
    (hST : S * T = 1) (hw : 0 < w) (A : Matrix ι ι ℝ) :
    SpectrallyStable (rebaseMatrix T S w A) ↔ SpectrallyStable A := by
  rw [rebaseMatrix, spectrallyStable_smul_iff (inv_pos.mpr hw)]
  exact spectrallyStable_conj_iff hTS hST A

end Matrices

section Plants

variable {n p : ℕ} {T S : Matrix (Fin n) (Fin n) ℝ} {w : ℝ}

@[powerlib_foundation] theorem isHurwitz_rebaseMatrix_iff (hTS : T * S = 1) (hST : S * T = 1)
    (hw : 0 < w) (A : Matrix (Fin n) (Fin n) ℝ) :
    IsHurwitz (rebaseMatrix T S w A) ↔ IsHurwitz A := by
  rw [← spectrallyStable_iff_isHurwitz, ← spectrallyStable_iff_isHurwitz]
  exact spectrallyStable_rebaseMatrix_iff hTS hST hw A

/-- The attractive sentences of the linear field are invariant under every change of state bases
and every positive time base. -/
@[powerlib_foundation] theorem holds_rebaseMatrix_iff (hTS : T * S = 1) (hST : S * T = 1)
    (hw : 0 < w) (A : Matrix (Fin n) (Fin n) ℝ) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (affineLinearVectorField (rebaseMatrix T S w A) 0) 0 ↔
      P.holds (affineLinearVectorField A 0) 0 := by
  rw [holds_iff_isHurwitz 0 hP, holds_iff_isHurwitz 0 hP, isHurwitz_rebaseMatrix_iff hTS hST hw]

/-- With the time base `1`, every flow sentence of the linear field is invariant. -/
@[powerlib_foundation] theorem holds_rebaseMatrix_one_iff (hTS : T * S = 1) (hST : S * T = 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Flow.Property) :
    P.holds (affineLinearVectorField (rebaseMatrix T S 1 A) 0) 0 ↔
      P.holds (affineLinearVectorField A 0) 0 := by
  rw [rebaseMatrix, inv_one, one_smul]
  exact holds_conj P hTS hST A

/-- For every positive time base, every flow sentence of the linear field is the rebased one with
its decay rate scaled by `w`: `P` holds for the rebased field exactly when `P.timeScale w` holds
for the original. -/
@[powerlib_foundation] theorem holds_rebaseMatrix_timeScale_iff (hTS : T * S = 1)
    (hST : S * T = 1) (hw : 0 < w) (A : Matrix (Fin n) (Fin n) ℝ) (P : Flow.Property) :
    P.holds (affineLinearVectorField (rebaseMatrix T S w A) 0) 0 ↔
      (P.timeScale w).holds (affineLinearVectorField A 0) 0 := by
  have h := Dynamics.holds_timeScale_linear_iff (inv_pos.mpr hw) (T * A * S) 0 (P.timeScale w)
  rw [Flow.Property.timeScale_timeScale, inv_mul_cancel₀ hw.ne', Flow.Property.timeScale_one] at h
  rw [rebaseMatrix, h]
  exact holds_conj _ hTS hST A

@[powerlib_foundation] theorem characteristicMatrix_rebaseMatrix (hTS : T * S = 1) (hw : w ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (s : ℂ) :
    characteristicMatrix (rebaseMatrix T S w A) s =
      (w⁻¹ : ℂ) • (complexify T * characteristicMatrix A (s * w) * complexify S) := by
  rw [rebaseMatrix, characteristicMatrix_smul (inv_ne_zero hw), characteristicMatrix_conj hTS]
  push_cast
  rw [div_inv_eq_mul]

/-- The plant in new bases: state `x̂ = T x` (left inverse `S`), time `τ = w t`, input
`u = S_u û`, output `ŷ = T_y y`. -/
def plant (m : Plant n p) (T S : Matrix (Fin n) (Fin n) ℝ) (w : ℝ)
    (Su Ty : Matrix (Fin p) (Fin p) ℝ) : Plant n p :=
  ⟨rebaseMatrix T S w m.A, w⁻¹ • (T * m.B * Su), Ty * m.C * S, Ty * m.D * Su⟩

private lemma complexify_smul (c : ℝ) {m' n' : Type*} (M : Matrix m' n' ℝ) :
    complexify (c • M) = (c : ℂ) • complexify M := by
  ext i j; simp

/-- Reversing the output sign of a plant (`LTI.negOutput`, read with the output as a port current
the `Y^IN = −Y^OUT` translation) is the change of output basis `−1` with unit time base; its
transfer matrix is `transfer_rebase` at this basis. -/
@[powerlib_foundation] theorem plant_negOutput (m : Plant n p) :
    plant m 1 1 1 1 (-1) = LTI.negOutput m := by
  ext : 1 <;> simp [plant, rebaseMatrix, LTI.negOutput]

/-- The transfer matrix in new bases: `Ĝ(ŝ) = T_y G(w ŝ) S_u`. -/
@[powerlib_foundation] theorem transfer_rebase (hTS : T * S = 1) (hST : S * T = 1) (hw : w ≠ 0)
    (Su Ty : Matrix (Fin p) (Fin p) ℝ) (m : Plant n p) (s : ℂ) :
    transfer (plant m T S w Su Ty) s =
      complexify Ty * transfer m (s * w) * complexify Su := by
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  have hinv : (characteristicMatrix (rebaseMatrix T S w m.A) s)⁻¹ =
      (w : ℂ) • (complexify T * (characteristicMatrix m.A (s * w))⁻¹ * complexify S) := by
    rw [characteristicMatrix_rebaseMatrix hTS hw, inv_smul_matrix (inv_ne_zero hw'), inv_inv,
      inv_conj (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST)]
  have hcancel {α : Type} (X : Matrix (Fin n) α ℂ) : complexify S * (complexify T * X) = X := by
    rw [← Matrix.mul_assoc, complexify_mul_eq_one hST, Matrix.one_mul]
  simp only [transfer, plant, hinv, complexify_mul, complexify_smul, Matrix.mul_assoc,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcancel, Matrix.mul_add, Matrix.add_mul]
  push_cast
  rw [inv_mul_cancel₀ hw', one_smul]

end Plants

/-! ## Interconnections -/

/-- The spaces of a source–load interconnection: the two state spaces, their rate spaces, the port
voltage and the port current. -/
inductive Space
  | x₁ | x₂ | d₁ | d₂ | v | i

/-- The matrices of an interconnection, typed by the spaces they map between. -/
inductive Primitive : Space → Space → Type
  | A₁ : Primitive .d₁ .x₁
  | B₁ : Primitive .d₁ .i
  | C₁ : Primitive .v .x₁
  | D₁ : Primitive .v .i
  | A₂ : Primitive .d₂ .x₂
  | B₂ : Primitive .d₂ .v
  | C₂ : Primitive .i .x₂

/-- Space dimensions. -/
def dims (n₁ n₂ p : ℕ) : Space → ℕ
  | .x₁ | .d₁ => n₁
  | .x₂ | .d₂ => n₂
  | .v | .i => p

section Interconnection

open Construction

variable {n₁ n₂ p : ℕ}

/-- The matrices of an interconnection. -/
def interp (ic : Interconnection n₁ n₂ p) :
    ∀ a b, Primitive a b → Matrix (Fin (dims n₁ n₂ p a)) (Fin (dims n₁ n₂ p b)) ℝ
  | _, _, .A₁ => ic.source.A
  | _, _, .B₁ => ic.source.B
  | _, _, .C₁ => ic.source.C
  | _, _, .D₁ => ic.source.D
  | _, _, .A₂ => ic.load.A
  | _, _, .B₂ => ic.load.B
  | _, _, .C₂ => ic.load.C

/-- The closed-loop blocks as constructions: state `[[A₁, B₁C₂], [−B₂C₁, A₂ − B₂D₁C₂]]`, input
`[−B₁; B₂D₁]`, output `[−C₁, −D₁C₂]`. -/
def a₁₁ : Construction Primitive .d₁ .x₁ := atom .A₁
def a₁₂ : Construction Primitive .d₁ .x₂ := mul (atom .B₁) (atom .C₂)
def a₂₁ : Construction Primitive .d₂ .x₁ := neg (mul (atom .B₂) (atom .C₁))
def a₂₂ : Construction Primitive .d₂ .x₂ :=
  sub (atom .A₂) (mul (mul (atom .B₂) (atom .D₁)) (atom .C₂))
def b₁ : Construction Primitive .d₁ .i := neg (atom .B₁)
def b₂ : Construction Primitive .d₂ .i := mul (atom .B₂) (atom .D₁)
def c₁ : Construction Primitive .v .x₁ := neg (atom .C₁)
def c₂ : Construction Primitive .v .x₂ := neg (mul (atom .D₁) (atom .C₂))

/-- Changes of bases of an interconnection: state coordinates `T₁, T₂` with left inverses
`S₁, S₂`, port voltage coordinates `Tv` and port current coordinates `Ti` with left inverses
`Sv, Si`, and the time base `w`. -/
structure Bases (n₁ n₂ p : ℕ) where
  T₁ : Matrix (Fin n₁) (Fin n₁) ℝ
  S₁ : Matrix (Fin n₁) (Fin n₁) ℝ
  T₂ : Matrix (Fin n₂) (Fin n₂) ℝ
  S₂ : Matrix (Fin n₂) (Fin n₂) ℝ
  Tv : Matrix (Fin p) (Fin p) ℝ
  Sv : Matrix (Fin p) (Fin p) ℝ
  Ti : Matrix (Fin p) (Fin p) ℝ
  Si : Matrix (Fin p) (Fin p) ℝ
  w : ℝ

/-- The bases of the six spaces: a rate space carries the bases of its state space divided by the
time base. -/
def Bases.T (β : Bases n₁ n₂ p) : ∀ a, Matrix (Fin (dims n₁ n₂ p a)) (Fin (dims n₁ n₂ p a)) ℝ
  | .x₁ => β.T₁
  | .x₂ => β.T₂
  | .d₁ => β.w⁻¹ • β.T₁
  | .d₂ => β.w⁻¹ • β.T₂
  | .v => β.Tv
  | .i => β.Ti

def Bases.S (β : Bases n₁ n₂ p) : ∀ a, Matrix (Fin (dims n₁ n₂ p a)) (Fin (dims n₁ n₂ p a)) ℝ
  | .x₁ => β.S₁
  | .x₂ => β.S₂
  | .d₁ => β.w • β.S₁
  | .d₂ => β.w • β.S₂
  | .v => β.Sv
  | .i => β.Si

/-- The interconnection in new bases. -/
def interconnection (ic : Interconnection n₁ n₂ p) (β : Bases n₁ n₂ p) :
    Interconnection n₁ n₂ p :=
  ⟨plant ic.source β.T₁ β.S₁ β.w β.Si β.Tv, plant ic.load β.T₂ β.S₂ β.w β.Sv β.Ti, by
    simp [plant, ic.load_strictly_proper]⟩

variable (ic : Interconnection n₁ n₂ p) (β : Bases n₁ n₂ p)

private theorem smul_conj {α β' γ δ : Type*} [Fintype β'] [Fintype γ] (c : ℝ)
    (T : Matrix α β' ℝ) (A : Matrix β' γ ℝ) (S : Matrix γ δ ℝ) :
    c • (T * A * S) = c • T * A * S := by
  rw [Matrix.smul_mul, Matrix.smul_mul]

theorem interp_interconnection :
    interp (interconnection ic β) = Construction.rebase (dims n₁ n₂ p) β.T β.S (interp ic) := by
  funext a b x
  cases x
  · exact smul_conj β.w⁻¹ β.T₁ ic.source.A β.S₁
  · exact smul_conj β.w⁻¹ β.T₁ ic.source.B β.Si
  · rfl
  · rfl
  · exact smul_conj β.w⁻¹ β.T₂ ic.load.A β.S₂
  · exact smul_conj β.w⁻¹ β.T₂ ic.load.B β.Sv
  · rfl

theorem closedLoopBlocks_eq :
    ic.closedLoopBlocks = fromBlocks (eval (dims n₁ n₂ p) (interp ic) a₁₁)
      (eval (dims n₁ n₂ p) (interp ic) a₁₂) (eval (dims n₁ n₂ p) (interp ic) a₂₁)
      (eval (dims n₁ n₂ p) (interp ic) a₂₂) := rfl

theorem inputBlocks_eq :
    ic.inputBlocks = fromRows (eval (dims n₁ n₂ p) (interp ic) b₁)
      (eval (dims n₁ n₂ p) (interp ic) b₂) := rfl

theorem outputBlocks_eq :
    ic.outputBlocks = fromCols (eval (dims n₁ n₂ p) (interp ic) c₁)
      (eval (dims n₁ n₂ p) (interp ic) c₂) := rfl

/-- Block conjugation of a block matrix, with a scaling of the target bases. -/
@[powerlib_foundation] theorem fromBlocks_conj {α γ : Type*} [Fintype α] [Fintype γ] (c : ℝ)
    (T₁ S₁ : Matrix α α ℝ) (T₂ S₂ : Matrix γ γ ℝ) (a : Matrix α α ℝ) (b : Matrix α γ ℝ)
    (c' : Matrix γ α ℝ) (d : Matrix γ γ ℝ) :
    fromBlocks (c • T₁ * a * S₁) (c • T₁ * b * S₂) (c • T₂ * c' * S₁) (c • T₂ * d * S₂) =
      c • (fromBlocks T₁ 0 0 T₂ * fromBlocks a b c' d * fromBlocks S₁ 0 0 S₂) := by
  simp [fromBlocks_multiply, fromBlocks_smul, Matrix.smul_mul]

@[powerlib_foundation] theorem fromRows_conj {α γ κ : Type*} [Fintype α] [Fintype γ] [Fintype κ]
    (c : ℝ) (T₁ : Matrix α α ℝ) (T₂ : Matrix γ γ ℝ) (S : Matrix κ κ ℝ) (b : Matrix α κ ℝ)
    (b' : Matrix γ κ ℝ) :
    fromRows (c • T₁ * b * S) (c • T₂ * b' * S) =
      c • (fromBlocks T₁ 0 0 T₂ * fromRows b b' * S) := by
  rw [fromBlocks_mul_fromRows, fromRows_mul]
  ext (i | i) j <;> simp [Matrix.smul_mul]

@[powerlib_foundation] theorem fromCols_conj {α γ κ : Type*} [Fintype α] [Fintype γ] [Fintype κ]
    (T : Matrix κ κ ℝ) (S₁ : Matrix α α ℝ) (S₂ : Matrix γ γ ℝ) (b : Matrix κ α ℝ)
    (c : Matrix κ γ ℝ) :
    fromCols (T * b * S₁) (T * c * S₂) = T * fromCols b c * fromBlocks S₁ 0 0 S₂ := by
  simp [fromCols_mul_fromBlocks, mul_fromCols, Matrix.mul_assoc]

variable {ic β}

/-- The closed-loop state blocks of the rebased components are the rebased blocks; only the port
bases need inverses. -/
@[powerlib_foundation] theorem closedLoopBlocks_rebase (hv : β.Sv * β.Tv = 1)
    (hi : β.Si * β.Ti = 1) :
    (interconnection ic β).closedLoopBlocks =
      β.w⁻¹ • (fromBlocks β.T₁ 0 0 β.T₂ * ic.closedLoopBlocks * fromBlocks β.S₁ 0 0 β.S₂) := by
  rw [closedLoopBlocks_eq, closedLoopBlocks_eq, interp_interconnection]
  rw [eval_rebase _ _ _ _ a₁₁ (by intro c hc; simp [a₁₁, Construction.inner] at hc),
    eval_rebase _ _ _ _ a₁₂ (by
      intro c hc; simp [a₁₂, Construction.inner] at hc; subst hc; exact hi),
    eval_rebase _ _ _ _ a₂₁ (by
      intro c hc; simp [a₂₁, Construction.inner] at hc; subst hc; exact hv),
    eval_rebase _ _ _ _ a₂₂ (by
      intro c hc
      simp [a₂₂, Construction.inner] at hc
      rcases hc with rfl | rfl <;> assumption)]
  exact fromBlocks_conj β.w⁻¹ β.T₁ β.S₁ β.T₂ β.S₂ _ _ _ _

/-- The closed-loop input blocks of the rebased components are the rebased blocks. -/
@[powerlib_foundation] theorem inputBlocks_rebase (hv : β.Sv * β.Tv = 1) :
    (interconnection ic β).inputBlocks =
      β.w⁻¹ • (fromBlocks β.T₁ 0 0 β.T₂ * ic.inputBlocks * β.Si) := by
  rw [inputBlocks_eq, inputBlocks_eq, interp_interconnection,
    eval_rebase _ _ _ _ b₁ (by intro c hc; simp [b₁, Construction.inner] at hc),
    eval_rebase _ _ _ _ b₂ (by
      intro c hc; simp [b₂, Construction.inner] at hc; subst hc; exact hv)]
  exact fromRows_conj β.w⁻¹ β.T₁ β.T₂ β.Si _ _

/-- The closed-loop output blocks of the rebased components are the rebased blocks. -/
@[powerlib_foundation] theorem outputBlocks_rebase (hi : β.Si * β.Ti = 1) :
    (interconnection ic β).outputBlocks =
      β.Tv * ic.outputBlocks * fromBlocks β.S₁ 0 0 β.S₂ := by
  rw [outputBlocks_eq, outputBlocks_eq, interp_interconnection,
    eval_rebase _ _ _ _ c₁ (by intro c hc; simp [c₁, Construction.inner] at hc),
    eval_rebase _ _ _ _ c₂ (by
      intro c hc; simp [c₂, Construction.inner] at hc; subst hc; exact hi)]
  exact fromCols_conj β.Tv β.S₁ β.S₂ _ _

/-- The closed loop of the rebased components is the rebased closed loop. -/
@[powerlib_foundation] theorem closedLoop_rebase (hv : β.Sv * β.Tv = 1) (hi : β.Si * β.Ti = 1) :
    (interconnection ic β).closedLoop =
      plant ic.closedLoop (blockCoordinates β.T₁ β.T₂) (blockCoordinates β.S₁ β.S₂) β.w β.Si
        β.Tv := by
  ext : 1
  · change ((interconnection ic β).closedLoopBlocks).reindex _ _ =
      β.w⁻¹ • (blockCoordinates β.T₁ β.T₂ * ic.closedLoopBlocks.reindex _ _ *
        blockCoordinates β.S₁ β.S₂)
    rw [closedLoopBlocks_rebase hv hi, blockCoordinates, blockCoordinates,
      ← reindex_mul finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      ← reindex_mul finSumFinEquiv finSumFinEquiv finSumFinEquiv]
    rfl
  · change ((interconnection ic β).inputBlocks).reindex finSumFinEquiv (Equiv.refl _) =
      β.w⁻¹ • (blockCoordinates β.T₁ β.T₂ * ic.inputBlocks.reindex finSumFinEquiv (Equiv.refl _) *
        β.Si)
    rw [inputBlocks_rebase hv, blockCoordinates,
      ← reindex_mul finSumFinEquiv finSumFinEquiv (Equiv.refl _)]
    conv_rhs => rw [← Matrix.reindex_refl_refl β.Si]
    rw [← reindex_mul finSumFinEquiv (Equiv.refl _) (Equiv.refl _)]
    rfl
  · change ((interconnection ic β).outputBlocks).reindex _ _ =
      β.Tv * ic.outputBlocks.reindex _ _ * blockCoordinates β.S₁ β.S₂
    rw [outputBlocks_rebase hi, blockCoordinates]
    conv_rhs => rw [← Matrix.reindex_refl_refl β.Tv]
    rw [← reindex_mul (Equiv.refl _) (Equiv.refl _) finSumFinEquiv,
      ← reindex_mul (Equiv.refl _) finSumFinEquiv finSumFinEquiv]
  · rfl

/-- The source impedance in new bases: `Ẑ(ŝ) = T_v Z(w ŝ) S_i`. -/
@[powerlib_foundation] theorem sourceImpedance_rebase (h₁ : β.S₁ * β.T₁ = 1) (hw : β.w ≠ 0)
    (s : ℂ) :
    (interconnection ic β).sourceImpedance s =
      complexify β.Tv * ic.sourceImpedance (s * β.w) * complexify β.Si :=
  transfer_rebase (mul_eq_one_comm.mp h₁) h₁ hw _ _ ic.source s

/-- The load admittance in new bases: `Ŷ(ŝ) = T_i Y(w ŝ) S_v`. -/
@[powerlib_foundation] theorem loadAdmittance_rebase (h₂ : β.S₂ * β.T₂ = 1) (hw : β.w ≠ 0)
    (s : ℂ) :
    (interconnection ic β).loadAdmittance s =
      complexify β.Ti * ic.loadAdmittance (s * β.w) * complexify β.Sv :=
  transfer_rebase (mul_eq_one_comm.mp h₂) h₂ hw _ _ ic.load s

/-- The return difference in new bases is the original one at `w ŝ`. -/
@[powerlib_foundation] theorem returnDifference_rebase (h₁ : β.S₁ * β.T₁ = 1)
    (h₂ : β.S₂ * β.T₂ = 1) (hv : β.Sv * β.Tv = 1) (hi : β.Si * β.Ti = 1) (hw : β.w ≠ 0)
    (s : ℂ) :
    (interconnection ic β).returnDifference s = ic.returnDifference (s * β.w) := by
  simp only [Interconnection.returnDifference, sourceImpedance_rebase h₁ hw,
    loadAdmittance_rebase h₂ hw]
  exact det_one_add_mul_rebase (complexify_mul_eq_one (mul_eq_one_comm.mp hv))
    (complexify_mul_eq_one hv) (complexify_mul_eq_one hi) _ _

/-- The impedance criterion is invariant under every change of bases with positive time base. -/
@[powerlib_foundation] theorem impedanceStable_rebase_iff (h₁ : β.S₁ * β.T₁ = 1)
    (h₂ : β.S₂ * β.T₂ = 1) (hv : β.Sv * β.Tv = 1) (hi : β.Si * β.Ti = 1) (hw : 0 < β.w) :
    (interconnection ic β).ImpedanceStable ↔ ic.ImpedanceStable := by
  have hw' : (β.w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  simp only [Interconnection.ImpedanceStable, returnDifference_rebase h₁ h₂ hv hi hw.ne']
  constructor
  · intro h s hs
    have h' := h (s / β.w) (by rw [Complex.div_ofReal_re]; positivity)
    rwa [div_mul_cancel₀ _ hw'] at h'
  · intro h s hs
    exact h _ (by simp; positivity)

private theorem blockCoordinates_inv {T₁ S₁ : Matrix (Fin n₁) (Fin n₁) ℝ}
    {T₂ S₂ : Matrix (Fin n₂) (Fin n₂) ℝ} (h₁ : S₁ * T₁ = 1) (h₂ : S₂ * T₂ = 1) :
    blockCoordinates S₁ S₂ * blockCoordinates T₁ T₂ = 1 := by
  rw [blockCoordinates_mul, h₁, h₂, blockCoordinates_one]

/-- Closed-loop pole stability is invariant under every change of bases with positive time
base. -/
@[powerlib_foundation] theorem isHurwitz_closedLoop_rebase_iff (h₁ : β.S₁ * β.T₁ = 1)
    (h₂ : β.S₂ * β.T₂ = 1) (hv : β.Sv * β.Tv = 1) (hi : β.Si * β.Ti = 1) (hw : 0 < β.w) :
    IsHurwitz (interconnection ic β).closedLoop.A ↔ IsHurwitz ic.closedLoop.A := by
  rw [closedLoop_rebase hv hi]
  exact isHurwitz_rebaseMatrix_iff
    (blockCoordinates_inv (mul_eq_one_comm.mp h₁) (mul_eq_one_comm.mp h₂))
    (blockCoordinates_inv h₁ h₂) hw _

/-! ## Instances: coordinates and the current direction -/

/-- State coordinate changes are changes of bases with unit port bases and time base. -/
@[powerlib_foundation] theorem changeCoordinates_eq (T₁ S₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (T₂ S₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    ic.changeCoordinates T₁ S₁ T₂ S₂ = interconnection ic ⟨T₁, S₁, T₂, S₂, 1, 1, 1, 1, 1⟩ := by
  refine Interconnection.ext ?_ ?_ <;> ext : 1 <;>
    simp [Interconnection.changeCoordinates, Plant.changeCoordinates, interconnection, plant,
      rebaseMatrix, ic.load_strictly_proper]

private theorem complexify_neg_one {κ : Type*} [Fintype κ] [DecidableEq κ] :
    complexify (-1 : Matrix κ κ ℝ) = -1 := by
  rw [complexify_neg]
  unfold complexify
  rw [Matrix.map_one _ (map_zero _) (map_one _)]

/-- The current direction convention: reverse the port current, nothing else. -/
def flipCurrent : Bases n₁ n₂ p := ⟨1, 1, 1, 1, 1, 1, -1, -1, 1⟩

/-- Reversing the current direction reverses the injected current and keeps the closed-loop
state and output matrices. -/
@[powerlib_foundation] theorem closedLoop_flipCurrent :
    (interconnection ic flipCurrent).closedLoop =
      ⟨ic.closedLoop.A, -ic.closedLoop.B, ic.closedLoop.C, -ic.closedLoop.D⟩ := by
  rw [closedLoop_rebase (by simp [flipCurrent]) (by simp [flipCurrent])]
  simp [flipCurrent, plant, rebaseMatrix, blockCoordinates_one]

@[powerlib_foundation] theorem sourceImpedance_flipCurrent (s : ℂ) :
    (interconnection ic flipCurrent).sourceImpedance s = -ic.sourceImpedance s := by
  rw [sourceImpedance_rebase (by simp [flipCurrent]) (by simp [flipCurrent])]
  simp [flipCurrent, complexify_neg_one]

@[powerlib_foundation] theorem loadAdmittance_flipCurrent (s : ℂ) :
    (interconnection ic flipCurrent).loadAdmittance s = -ic.loadAdmittance s := by
  rw [loadAdmittance_rebase (by simp [flipCurrent]) (by simp [flipCurrent])]
  simp [flipCurrent, complexify_neg_one]

@[powerlib_foundation] theorem returnDifference_flipCurrent (s : ℂ) :
    (interconnection ic flipCurrent).returnDifference s = ic.returnDifference s := by
  rw [returnDifference_rebase (by simp [flipCurrent]) (by simp [flipCurrent])
    (by simp [flipCurrent]) (by simp [flipCurrent]) (by simp [flipCurrent])]
  simp [flipCurrent]

end Interconnection

/-! ## The connection on the interconnection family -/

variable {n₁ n₂ p : ℕ}

/-- Stable together in every bases: on the interconnection family, the denotation of every
attractive sentence and of sampled contraction is its own pull-back along any change of bases with
invertible bases and positive time base. -/
@[powerlib_domain] theorem den_rebase {β : Bases n₁ n₂ p} (h₁ : β.S₁ * β.T₁ = 1)
    (h₂ : β.S₂ * β.T₂ = 1) (hv : β.Sv * β.Tv = 1) (hi : β.Si * β.Ti = 1) (hw : 0 < β.w)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% ((Interconnection.family (n₁ := n₁) (n₂ := n₂) (p := p)).den (.flow P) =
      (fun ic => interconnection ic β) ⁻¹' Interconnection.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [Interconnection.family_isLinear.den_hurwitz hP]
  ext ic
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact (isHurwitz_closedLoop_rebase_iff h₁ h₂ hv hi hw).symm

/-- With the time base `1`, every flow sentence is pulled back along any change of bases with
invertible bases. -/
@[powerlib_domain] theorem den_rebase_unitTime {β : Bases n₁ n₂ p} (h₁ : β.S₁ * β.T₁ = 1)
    (h₂ : β.S₂ * β.T₂ = 1) (hv : β.Sv * β.Tv = 1) (hi : β.Si * β.Ti = 1) (hw : β.w = 1)
    (P : Flow.Property) :
    connection% ((Interconnection.family (n₁ := n₁) (n₂ := n₂) (p := p)).den (.flow P) =
      (fun ic => interconnection ic β) ⁻¹' Interconnection.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  ext ic
  rw [Set.mem_preimage, Interconnection.family_isLinear.mem_den_flow,
    Interconnection.family_isLinear.mem_den_flow, closedLoop_rebase hv hi]
  change _ ↔ P.holds (affineLinearVectorField (rebaseMatrix _ _ β.w ic.closedLoop.A) 0) 0
  rw [hw]
  exact (holds_rebaseMatrix_one_iff
    (blockCoordinates_inv (mul_eq_one_comm.mp h₁) (mul_eq_one_comm.mp h₂))
    (blockCoordinates_inv h₁ h₂) _ P).symm

/-- Stable together in every bases, every sentence: on the interconnection family, for any change
of bases with invertible bases and positive time base `w`, the rebased interconnections that
satisfy a flow sentence `P` are those whose original satisfies `P.timeScale w` (decay at the rate
`a` per unit of the rebased time `τ = w t` is decay at the rate `w a` per unit of `t`; every other
sentence is unchanged). -/
@[powerlib_domain] theorem den_rebase_timeScale {β : Bases n₁ n₂ p} (h₁ : β.S₁ * β.T₁ = 1)
    (h₂ : β.S₂ * β.T₂ = 1) (hv : β.Sv * β.Tv = 1) (hi : β.Si * β.Ti = 1) (hw : 0 < β.w)
    (P : Flow.Property) :
    connection% ((Interconnection.family (n₁ := n₁) (n₂ := n₂) (p := p)).den
        (.flow (P.timeScale β.w)) =
      (fun ic => interconnection ic β) ⁻¹' Interconnection.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  ext ic
  rw [Set.mem_preimage, Interconnection.family_isLinear.mem_den_flow,
    Interconnection.family_isLinear.mem_den_flow, closedLoop_rebase hv hi]
  exact (holds_rebaseMatrix_timeScale_iff
    (blockCoordinates_inv (mul_eq_one_comm.mp h₁) (mul_eq_one_comm.mp h₂))
    (blockCoordinates_inv h₁ h₂) hw _ P).symm

/-- The two current direction conventions denote the same interconnections for every flow
sentence. -/
@[powerlib_domain] theorem den_flipCurrent (P : Flow.Property) :
    connection% ((Interconnection.family (n₁ := n₁) (n₂ := n₂) (p := p)).den (.flow P) =
      (fun ic => interconnection ic flipCurrent) ⁻¹' Interconnection.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  ext ic
  rw [Set.mem_preimage, Interconnection.family_isLinear.mem_den_flow,
    Interconnection.family_isLinear.mem_den_flow, closedLoop_flipCurrent]

end powerlib.Transform.Rebase
