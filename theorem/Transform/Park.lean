import dependencies.Mathlib
import theorem.Attributes
import theorem.Transform.ParkABC
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Clarke and Park coordinate transformations

Coordinate identities (foundation) of the Clarke and Park transformations.

Scope.
Conventions fixed by this module:
* A planar (αβ or dq) vector is `Fin 2 → ℝ`, component `0` = α (resp. d), component `1` = β
  (resp. q). Its complex form is `toComplex x = x 0 + x 1 * I`.
* `rot θ` is the counter-clockwise rotation by `θ` (dq → αβ). The Park matrix is
  `park θ = [[cos θ, sin θ], [-sin θ, cos θ]]` (αβ → dq), exactly `conventions.md` §4.
  Hence `park θ = rot (-θ)` and, in complex form, `x^{dq} = x^{αβ} · e^{-jθ}`.
  `rot_neg_mul_rot`: `rot (−a) · rot a = 1` (used by `theorem/Drives/Sensorless.lean`);
  `frameRotation_power_invariant`: `rot δ` preserves the port power `v·i` (machine frame vs
  common DQ frame, `theory/T-power-system-ph.md` §1.2).
* `J = [[0, -1], [1, 0]]` is the rotation generator (`d/dθ rot θ = J · rot θ`); in complex
  form it is multiplication by `j`.
* Scalar components: `parkD θ x_d x_q`, `parkQ θ x_d x_q` are the two rows of `park θ` applied to
  `(x_d, x_q)` (system → controller frame, `conventions.md` §D4) and `iparkD`, `iparkQ` those of
  `rot θ` (controller → system); `parkD_ipark` … `iparkQ_park` (inverse pairs), `park_dot` (dot
  product preserved), `parkD_J`, `parkQ_J` (commutation with `J`).
* `clarke` is the amplitude-invariant Clarke matrix `(2/3)[[1, -1/2, -1/2], [0, √3/2, -√3/2]]`
  (`conventions.md` §4). `clarkePI` is the 3 × 3 power-invariant Clarke matrix with the
  zero-sequence row (`T-impedance-modeling.md` §1.1); it is orthogonal.

Source: work-sync `theory/T-park-transformation.md` §1.2–§1.4 and `conventions.md` §4 / §D4
(Park matrix SSoT), `theory/T-impedance-modeling.md` §1.1 (power-invariant Clarke).

Results.
* `parkABC θ = park θ · clarke` is the amplitude-invariant three-phase Park of `T-PU.md` §1.7;
  `balanced V φ θ` is the balanced positive-sequence signal `V cos(θ − 2πk/3 + φ)`;
  `negSeq V φ θ` is the negative-sequence signal (phases `b`, `c` swapped), which is
  `V e^{−j(θ+φ)}` in αβ (`clarke_mulVec_negSeq`, `toComplex_clarke_negSeq`).
* The chain rule (`hasDerivAt_rot_mulVec`, `hasDerivAt_mul_cexp`) holds for every differentiable
  frame angle `θ(t)`, constant or time-varying. Its first-order form at `θ = 0`
  (`hasDerivAt_park_zero`: `d/dθ (park θ · x)|₀ = −J x`) gives the PLL frame projections of
  `T-gfl-impedance.md` §1.3, and its consequence for a shunt capacitor (`capacitor_dq`:
  `C dv/dt = i − ω C J v` in the dq frame) the cross term of §1.7.
* The αβ / dq KVL of one series R–L branch and its trajectory correspondence under Park
  (`alphaBetaRL_iff_dqRL`) are in `theorem/CurrentControl/DqRL.lean`.

Correction (`T-park-transformation.md` §1.5): the note says a fundamental positive-sequence
vector is "DC in the αβ frame". It is the reverse: `clarke_mulVec_balanced` shows it is the
rotating vector `V (cos(θ+φ), sin(θ+φ))` in αβ, and `parkABC_mulVec_balanced` shows it is the
constant `V (cos φ, sin φ)` in dq.

Correction (`T-PU.md` §1.7): for the amplitude-invariant Park, `v_a = V cos(ωt + φ)` maps to
`v_d = V cos φ`, `v_q = +V sin φ` (the note writes `v_q = −V sin φ`).
-/

noncomputable section
namespace powerlib.Transform
open Matrix

/-- Counter-clockwise rotation by `θ`: maps dq coordinates to αβ coordinates. -/
def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Park transformation `T_{αβ→dq}(θ)` of `conventions.md` §4. -/
def park (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/-- Rotation generator `J = [[0, -1], [1, 0]]`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Complex form `x₀ + j x₁` of a planar vector. -/
def toComplex (x : Fin 2 → ℝ) : ℂ := ⟨x 0, x 1⟩

/-- Planar vector `(Re z, Im z)` of a complex number. -/
def ofComplex (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

/-! ## Elementary identities -/

@[simp, powerlib_foundation] theorem rot_apply_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    rot θ *ᵥ x = ![Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1] := by
  ext i; fin_cases i
  · simp [rot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  · simp [rot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp, powerlib_foundation] theorem park_apply_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    park θ *ᵥ x = ![Real.cos θ * x 0 + Real.sin θ * x 1, -Real.sin θ * x 0 + Real.cos θ * x 1] := by
  ext i; fin_cases i <;> simp [park, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp, powerlib_foundation] theorem J_mulVec (x : Fin 2 → ℝ) : J *ᵥ x = ![-x 1, x 0] := by
  ext i; fin_cases i <;> simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[powerlib_foundation] theorem park_eq_rot_neg (θ : ℝ) : park θ = rot (-θ) := by
  simp [park, rot]

@[powerlib_foundation] theorem park_eq_transpose_rot (θ : ℝ) : park θ = (rot θ)ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [park, rot]

@[simp, powerlib_foundation] theorem rot_zero : rot 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot]

@[simp, powerlib_foundation] theorem park_zero : park 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [park]

@[powerlib_foundation] theorem rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  simp only [rot, mul_fin_two, Real.cos_add, Real.sin_add]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

@[powerlib_foundation] theorem park_add (a b : ℝ) : park (a + b) = park a * park b := by
  rw [park_eq_rot_neg, park_eq_rot_neg, park_eq_rot_neg, neg_add, rot_add]

@[powerlib_foundation] theorem rot_mul_park (θ : ℝ) : rot θ * park θ = 1 := by
  rw [park_eq_rot_neg, ← rot_add, add_neg_cancel, rot_zero]

@[powerlib_foundation] theorem park_mul_rot (θ : ℝ) : park θ * rot θ = 1 := by
  rw [park_eq_rot_neg, ← rot_add, neg_add_cancel, rot_zero]

@[powerlib_foundation] theorem rot_neg_mul_rot (a : ℝ) : rot (-a) * rot a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq a]

/-- T-power-system-ph §1.2: the rotation `R(δ)` is orthogonal, so the port power
`v_d i_d + v_q i_q` is the same in the machine frame and in the common DQ frame. -/
@[powerlib_foundation] theorem frameRotation_power_invariant (δ : ℝ) (v i : Fin 2 → ℝ) :
    (Transform.rot δ *ᵥ v) ⬝ᵥ (Transform.rot δ *ᵥ i) = v ⬝ᵥ i := by
  simp only [Transform.rot_apply_mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h := Real.sin_sq_add_cos_sq δ
  linear_combination (v 0 * i 0 + v 1 * i 1) * h

@[simp, powerlib_foundation] theorem rot_mulVec_park_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    rot θ *ᵥ (park θ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, rot_mul_park, Matrix.one_mulVec]

@[simp, powerlib_foundation] theorem park_mulVec_rot_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    park θ *ᵥ (rot θ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, park_mul_rot, Matrix.one_mulVec]

@[powerlib_foundation] theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  rw [rot, det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ]

@[powerlib_foundation] theorem det_park (θ : ℝ) : (park θ).det = 1 := by
  rw [park_eq_rot_neg, det_rot]

/-- Park is a proper rotation: it lies in `SO(2)`. -/
@[powerlib_foundation] theorem park_mem_specialOrthogonalGroup (θ : ℝ) :
    park θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, det_park θ⟩
  rw [show (park θ)ᵀ = rot θ by rw [park_eq_transpose_rot, transpose_transpose]]
  exact park_mul_rot θ

@[powerlib_foundation] theorem rot_mem_specialOrthogonalGroup (θ : ℝ) :
    rot θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  simpa [park_eq_rot_neg] using park_mem_specialOrthogonalGroup (-θ)

@[powerlib_foundation] theorem J_mul_J : J * J = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

@[powerlib_foundation] theorem J_transpose : Jᵀ = -J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

@[powerlib_foundation] theorem rot_mul_J (θ : ℝ) : rot θ * J = J * rot θ := by
  simp only [rot, J, mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

@[powerlib_foundation] theorem park_mul_J (θ : ℝ) : park θ * J = J * park θ := by
  rw [park_eq_rot_neg, rot_mul_J]

@[powerlib_foundation] theorem rot_mulVec_J_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    rot θ *ᵥ (J *ᵥ x) = J *ᵥ (rot θ *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, rot_mul_J]

@[powerlib_foundation] theorem park_mulVec_J_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    park θ *ᵥ (J *ᵥ x) = J *ᵥ (park θ *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, park_mul_J]

/-! ## Complex form versus matrix form (`T-park-transformation.md` §1.2) -/

@[simp, powerlib_foundation] theorem toComplex_re (x : Fin 2 → ℝ) : (toComplex x).re = x 0 := rfl

@[simp, powerlib_foundation] theorem toComplex_im (x : Fin 2 → ℝ) : (toComplex x).im = x 1 := rfl

@[simp, powerlib_foundation] theorem toComplex_ofComplex (z : ℂ) : toComplex (ofComplex z) = z := by
  apply Complex.ext <;> simp [toComplex, ofComplex]

@[simp, powerlib_foundation] theorem ofComplex_toComplex (x : Fin 2 → ℝ) :
    ofComplex (toComplex x) = x := by
  ext i; fin_cases i <;> simp [toComplex, ofComplex]

@[powerlib_foundation] theorem toComplex_eq (x : Fin 2 → ℝ) :
    toComplex x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [toComplex]

/-- The complex-form coordinate map as a real linear equivalence. -/
def complexEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ where
  toFun := toComplex
  invFun := ofComplex
  map_add' x y := by apply Complex.ext <;> simp [toComplex]
  map_smul' c x := by apply Complex.ext <;> simp [toComplex]
  left_inv := ofComplex_toComplex
  right_inv := toComplex_ofComplex

@[simp, powerlib_foundation] theorem complexEquiv_apply (x : Fin 2 → ℝ) :
    complexEquiv x = toComplex x := rfl

@[simp, powerlib_foundation] theorem toComplex_add (x y : Fin 2 → ℝ) :
    toComplex (x + y) = toComplex x + toComplex y := complexEquiv.map_add x y

@[simp, powerlib_foundation] theorem toComplex_sub (x y : Fin 2 → ℝ) :
    toComplex (x - y) = toComplex x - toComplex y := complexEquiv.map_sub x y

@[simp, powerlib_foundation] theorem toComplex_smul (c : ℝ) (x : Fin 2 → ℝ) :
    toComplex (c • x) = (c : ℂ) * toComplex x := by
  apply Complex.ext <;> simp [toComplex]

/-- Matrix rotation is complex multiplication by `e^{jθ}`. -/
@[powerlib_foundation] theorem toComplex_rot_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    toComplex (rot θ *ᵥ x) = toComplex x * Complex.exp (θ * Complex.I) := by
  apply Complex.ext <;>
    simp [toComplex, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] <;> ring

/-- Park is complex multiplication by `e^{-jθ}`: `x^{dq} = x^{αβ} e^{-jθ}` (§1.2 boxed). -/
@[powerlib_foundation] theorem toComplex_park_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    toComplex (park θ *ᵥ x) = toComplex x * Complex.exp (-(θ * Complex.I)) := by
  rw [park_eq_rot_neg, toComplex_rot_mulVec]
  push_cast
  ring_nf

/-- `J` is complex multiplication by `j`. -/
@[powerlib_foundation] theorem toComplex_J_mulVec (x : Fin 2 → ℝ) :
    toComplex (J *ᵥ x) = Complex.I * toComplex x := by
  apply Complex.ext <;> simp [toComplex]

/-- Rotation preserves the Euclidean squared norm. -/
@[powerlib_foundation] theorem rot_mulVec_sq_sum (θ : ℝ) (x : Fin 2 → ℝ) :
    (rot θ *ᵥ x) 0 ^ 2 + (rot θ *ᵥ x) 1 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp only [rot_apply_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]

@[powerlib_foundation] theorem park_mulVec_sq_sum (θ : ℝ) (x : Fin 2 → ℝ) :
    (park θ *ᵥ x) 0 ^ 2 + (park θ *ᵥ x) 1 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [park_eq_rot_neg, rot_mulVec_sq_sum]

/-- Rotation preserves the Euclidean norm. -/
@[powerlib_foundation] theorem norm_rot_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm (rot θ *ᵥ x)‖ = ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm x‖ := by
  have h := rot_mulVec_sq_sum θ x
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using h

@[powerlib_foundation] theorem norm_park_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm (park θ *ᵥ x)‖ = ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm x‖ := by
  rw [park_eq_rot_neg, norm_rot_mulVec]

/-! ## Chain rule in a rotating frame (`T-park-transformation.md` §1.3) -/

/-- Matrix form of the §1.3 chain rule: if `x^{αβ}(t) = rot θ(t) · x^{dq}(t)` then
`ẋ^{αβ} = rot θ · (ẋ^{dq} + ω J x^{dq})`, with `ω = θ̇` (any differentiable frame angle). -/
@[powerlib_foundation] theorem hasDerivAt_rot_mulVec {θ : ℝ → ℝ} {ω : ℝ} {x : ℝ → Fin 2 → ℝ}
    {x' : Fin 2 → ℝ} {t : ℝ} (hθ : HasDerivAt θ ω t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => rot (θ s) *ᵥ x s) (rot (θ t) *ᵥ (x' + ω • (J *ᵥ x t))) t := by
  have h0 := hasDerivAt_pi.1 hx 0
  have h1 := hasDerivAt_pi.1 hx 1
  have hc := hθ.cos
  have hs := hθ.sin
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simp only [rot_apply_mulVec, Fin.zero_eta, Matrix.cons_val_zero]
    convert (hc.mul h0).sub (hs.mul h1) using 1
    simp; ring
  · simp only [rot_apply_mulVec, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    convert (hs.mul h0).add (hc.mul h1) using 1
    simp; ring

/-- The same chain rule for the Park direction: `d/dt (park θ · x) = park θ · ẋ − ω J (park θ · x)`. -/
@[powerlib_foundation] theorem hasDerivAt_park_mulVec {θ : ℝ → ℝ} {ω : ℝ} {x : ℝ → Fin 2 → ℝ}
    {x' : Fin 2 → ℝ} {t : ℝ} (hθ : HasDerivAt θ ω t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => park (θ s) *ᵥ x s)
      (park (θ t) *ᵥ x' - ω • (J *ᵥ (park (θ t) *ᵥ x t))) t := by
  have h := hasDerivAt_rot_mulVec hθ.neg hx
  simp only [Pi.neg_apply] at h
  rw [show (fun s => park (θ s) *ᵥ x s) = fun s => rot (-θ s) *ᵥ x s from
    funext fun s => by rw [park_eq_rot_neg]]
  convert h using 1
  rw [← park_eq_rot_neg, Matrix.mulVec_add, Matrix.mulVec_smul, park_mulVec_J_mulVec, neg_smul, sub_eq_add_neg]

/-- Complex form of the §1.3 boxed chain rule:
`d/dt (x^{dq} e^{jθ}) = (ẋ^{dq} + jω x^{dq}) e^{jθ}`. -/
@[powerlib_foundation] theorem hasDerivAt_mul_cexp {θ : ℝ → ℝ} {ω : ℝ} {z : ℝ → ℂ} {z' : ℂ}
    {t : ℝ} (hθ : HasDerivAt θ ω t) (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => z s * Complex.exp (θ s * Complex.I))
      ((z' + ω * Complex.I * z t) * Complex.exp (θ t * Complex.I)) t := by
  have he := (hθ.ofReal_comp.mul_const Complex.I).cexp
  convert hz.mul he using 1
  ring

/-! ## First-order frame rotation and a shunt capacitor in the dq frame -/

/-- First-order rotation: `d/dθ (park θ · x)` at `θ = 0` is `−J x`. -/
@[powerlib_foundation] theorem hasDerivAt_park_zero (x : Fin 2 → ℝ) :
    HasDerivAt (fun θ => Transform.park θ *ᵥ x) (-(Transform.J *ᵥ x)) 0 := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simp only [Transform.park_apply_mulVec, Fin.zero_eta, Matrix.cons_val_zero]
    convert ((Real.hasDerivAt_cos 0).mul_const (x 0)).add
      ((Real.hasDerivAt_sin 0).mul_const (x 1)) using 1
    simp
  · simp only [Transform.park_apply_mulVec, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    convert ((Real.hasDerivAt_sin 0).neg.mul_const (x 0)).add
      ((Real.hasDerivAt_cos 0).mul_const (x 1)) using 1
    simp

/-- Park: if `C dv_αβ/dt = i_αβ` with `v_αβ = rot θ · v`, `i_αβ = rot θ · i`, `θ' = ω`, then
`C dv/dt = i − ω C J v`. -/
@[powerlib_foundation] theorem capacitor_dq {C : ℝ} {θ : ℝ → ℝ} {ω : ℝ} {v i : ℝ → Fin 2 → ℝ}
    {v' : Fin 2 → ℝ} {t : ℝ} (hθ : HasDerivAt θ ω t) (hv : HasDerivAt v v' t)
    (hαβ : HasDerivAt (fun s => Transform.rot (θ s) *ᵥ v s)
      (C⁻¹ • (Transform.rot (θ t) *ᵥ i t)) t) (hC : C ≠ 0) :
    C • v' = i t - (ω * C) • (Transform.J *ᵥ v t) := by
  have h := Transform.hasDerivAt_rot_mulVec hθ hv
  have heq := h.unique hαβ
  have h2 : v' + ω • (Transform.J *ᵥ v t) = C⁻¹ • i t := by
    have := congrArg (fun y => Transform.park (θ t) *ᵥ y) heq
    simp only [← Matrix.mulVec_smul, Transform.park_mulVec_rot_mulVec] at this
    rwa [Matrix.mulVec_smul] at this
  have h3 := congrArg (fun y => C • y) h2
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hC, one_smul] at h3
  rw [← h3, mul_comm ω C, ← smul_smul]
  abel

/-! ## Park transformation components (`conventions.md` §D4) -/

section Components

open Real

/-- d-component of `T(θ) x` (system → controller). -/
def parkD (θ xd xq : ℝ) : ℝ := cos θ * xd + sin θ * xq

/-- q-component of `T(θ) x` (system → controller). -/
def parkQ (θ xd xq : ℝ) : ℝ := -sin θ * xd + cos θ * xq

/-- d-component of `T(−θ) x` (controller → system). -/
def iparkD (θ xd xq : ℝ) : ℝ := cos θ * xd - sin θ * xq

/-- q-component of `T(−θ) x` (controller → system). -/
def iparkQ (θ xd xq : ℝ) : ℝ := sin θ * xd + cos θ * xq

@[simp, powerlib_foundation] theorem parkD_ipark (θ x y : ℝ) :
    parkD θ (iparkD θ x y) (iparkQ θ x y) = x := by
  unfold parkD iparkD iparkQ; linear_combination x * sin_sq_add_cos_sq θ

@[simp, powerlib_foundation] theorem parkQ_ipark (θ x y : ℝ) :
    parkQ θ (iparkD θ x y) (iparkQ θ x y) = y := by
  unfold parkQ iparkD iparkQ; linear_combination y * sin_sq_add_cos_sq θ

@[simp, powerlib_foundation] theorem iparkD_park (θ x y : ℝ) :
    iparkD θ (parkD θ x y) (parkQ θ x y) = x := by
  unfold parkD parkQ iparkD; linear_combination x * sin_sq_add_cos_sq θ

@[simp, powerlib_foundation] theorem iparkQ_park (θ x y : ℝ) :
    iparkQ θ (parkD θ x y) (parkQ θ x y) = y := by
  unfold parkD parkQ iparkQ; linear_combination y * sin_sq_add_cos_sq θ

/-- The rotation preserves the dot product. -/
@[powerlib_foundation] theorem park_dot (θ x y u v : ℝ) :
    parkD θ x y * parkD θ u v + parkQ θ x y * parkQ θ u v = x * u + y * v := by
  unfold parkD parkQ; linear_combination (x * u + y * v) * sin_sq_add_cos_sq θ

/-- The rotation commutes with the generator `J (x, y) = (−y, x)`. -/
@[powerlib_foundation] theorem parkD_J (θ x y : ℝ) : parkD θ (-y) x = -parkQ θ x y := by
  unfold parkD parkQ; ring

@[powerlib_foundation] theorem parkQ_J (θ x y : ℝ) : parkQ θ (-y) x = parkD θ x y := by
  unfold parkD parkQ; ring

end Components

/-! ## Clarke transformations -/

/-- Amplitude-invariant Clarke `abc → αβ`, `(2/3)[[1, -1/2, -1/2], [0, √3/2, -√3/2]]`. -/
def clarke : Matrix (Fin 2) (Fin 3) ℝ :=
  (2 / 3 : ℝ) • !![1, -1 / 2, -1 / 2; 0, Real.sqrt 3 / 2, -(Real.sqrt 3 / 2)]

/-- Inverse amplitude-invariant Clarke `αβ → abc` (zero-sequence free). -/
def clarkeInv : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0; -1 / 2, Real.sqrt 3 / 2; -1 / 2, -(Real.sqrt 3 / 2)]

/-- Power-invariant Clarke `abc → αβ0` with zero-sequence row (`T-impedance-modeling.md` §1.1). -/
def clarkePI : Matrix (Fin 3) (Fin 3) ℝ :=
  Real.sqrt (2 / 3) • !![1, -1 / 2, -1 / 2; 0, Real.sqrt 3 / 2, -(Real.sqrt 3 / 2);
    1 / Real.sqrt 2, 1 / Real.sqrt 2, 1 / Real.sqrt 2]

@[powerlib_foundation] private lemma sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

@[powerlib_foundation] private lemma sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

@[powerlib_foundation] theorem clarke_mul_clarkeInv : clarke * clarkeInv = 1 := by
  have h3 := sqrt_three_mul_self
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clarke, clarkeInv, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith [h3]

@[powerlib_foundation] theorem clarke_mul_transpose : clarke * clarkeᵀ = (2 / 3 : ℝ) • 1 := by
  have h3 := sqrt_three_mul_self
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clarke, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith [h3]

/-- On zero-sequence-free vectors (`x_a + x_b + x_c = 0`) the inverse Clarke reconstructs `abc`. -/
@[powerlib_foundation] theorem clarkeInv_mulVec_clarke_mulVec (x : Fin 3 → ℝ)
    (hx : x 0 + x 1 + x 2 = 0) : clarkeInv *ᵥ (clarke *ᵥ x) = x := by
  have h3 := sqrt_three_mul_self
  ext i; fin_cases i <;>
    simp [clarke, clarkeInv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  · linear_combination (-1/3) * hx
  · linear_combination (-1/3) * hx + (1/6) * (x 1 - x 2) * h3
  · linear_combination (-1/3) * hx - (1/6) * (x 1 - x 2) * h3

/-- Amplitude-invariant Clarke power: `v · i = (3/2)(v_α i_α + v_β i_β)` when `i` is
zero-sequence free. -/
@[powerlib_foundation] theorem dotProduct_eq_three_halves_clarke (v i : Fin 3 → ℝ)
    (hi : i 0 + i 1 + i 2 = 0) :
    v ⬝ᵥ i = (3 / 2 : ℝ) * ((clarke *ᵥ v) ⬝ᵥ (clarke *ᵥ i)) := by
  have h3 := sqrt_three_mul_self
  simp [clarke, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  linear_combination (1/3) * (v 0 + v 1 + v 2) * hi - (1/6) * (v 1 - v 2) * (i 1 - i 2) * h3

@[powerlib_foundation] theorem clarkePI_mul_transpose : clarkePI * clarkePIᵀ = 1 := by
  have h3 := sqrt_three_mul_self
  have h2 := sqrt_two_mul_self
  have h3' : (0 : ℝ) < Real.sqrt 3 := by positivity
  have h2' : (0 : ℝ) < Real.sqrt 2 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clarkePI, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | (field_simp; nlinarith [h3, h2])

/-- The power-invariant Clarke matrix is orthogonal. -/
@[powerlib_foundation] theorem clarkePI_mem_orthogonalGroup :
    clarkePI ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  exact clarkePI_mul_transpose

/-- Power invariance: `(T v) · (T i) = v · i` for the power-invariant Clarke `T`. -/
@[powerlib_foundation] theorem clarkePI_dotProduct (v i : Fin 3 → ℝ) :
    (clarkePI *ᵥ v) ⬝ᵥ (clarkePI *ᵥ i) = v ⬝ᵥ i := by
  have hTT : clarkePIᵀ * clarkePI = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (A := clarkePI)).1 clarkePI_mem_orthogonalGroup
    simpa [star_eq_conjTranspose] using this
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hTT,
    Matrix.vecMul_one]

/-! ## Three-phase Park and balanced positive-sequence signals -/

/-- Amplitude-invariant three-phase Park `T^A(θ) = park θ · clarke` (abc → dq, zero-sequence
row dropped), as in `T-PU.md` §1.7. -/
def parkABC (θ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := park θ * clarke

/-- Balanced positive-sequence three-phase signal of amplitude `V` and phase `φ` at electrical
angle `θ`: `x_k = V cos(θ − 2πk/3 + φ)`, `k = a, b, c`. -/
def balanced (V φ θ : ℝ) : Fin 3 → ℝ :=
  ![V * Real.cos (θ + φ), V * Real.cos (θ - 2 * Real.pi / 3 + φ),
    V * Real.cos (θ + 2 * Real.pi / 3 + φ)]

/-- The balanced signal has no zero-sequence component. -/
@[powerlib_foundation] theorem balanced_sum (V φ θ : ℝ) :
    balanced V φ θ 0 + balanced V φ θ 1 + balanced V φ θ 2 = 0 := by
  simp only [balanced, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have h1 : θ - 2 * Real.pi / 3 + φ = (θ + φ) - 2 * Real.pi / 3 := by ring
  have h2 : θ + 2 * Real.pi / 3 + φ = (θ + φ) + 2 * Real.pi / 3 := by ring
  rw [h1, h2]
  generalize θ + φ = ψ
  rw [Real.cos_sub ψ, Real.cos_add ψ, cos_two_pi_div_three, sin_two_pi_div_three]
  ring

/-- In the stationary αβ frame a balanced positive-sequence signal is the rotating vector
`V (cos(θ + φ), sin(θ + φ))`, i.e. `V e^{j(θ+φ)}`; with `θ = ω t` it is not constant. -/
@[powerlib_foundation] theorem clarke_mulVec_balanced (V φ θ : ℝ) :
    clarke *ᵥ balanced V φ θ = ![V * Real.cos (θ + φ), V * Real.sin (θ + φ)] := by
  have h3 := sqrt_three_mul_self
  have h1 : θ - 2 * Real.pi / 3 + φ = (θ + φ) - 2 * Real.pi / 3 := by ring
  have h2 : θ + 2 * Real.pi / 3 + φ = (θ + φ) + 2 * Real.pi / 3 := by ring
  simp only [balanced, h1, h2]
  generalize θ + φ = ψ
  rw [Real.cos_sub ψ, Real.cos_add ψ, cos_two_pi_div_three, sin_two_pi_div_three]
  ext i; fin_cases i <;>
    simp [clarke, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ring
  · linear_combination (1 / 3) * V * Real.sin ψ * h3

/-- In the dq frame at angle `θ` the same signal is the constant `V (cos φ, sin φ)`.
In particular `v_q = +V sin φ` for the amplitude-invariant Park. -/
@[powerlib_foundation] theorem parkABC_mulVec_balanced (V φ θ : ℝ) :
    parkABC θ *ᵥ balanced V φ θ = ![V * Real.cos φ, V * Real.sin φ] := by
  rw [parkABC, ← Matrix.mulVec_mulVec, clarke_mulVec_balanced]
  have hφ : φ = (θ + φ) - θ := by ring
  ext i; fin_cases i
  · simp only [park_apply_mulVec]
    conv_rhs => rw [hφ, Real.cos_sub]
    simp; ring
  · simp only [park_apply_mulVec]
    conv_rhs => rw [hφ, Real.sin_sub]
    simp; ring

/-! ## Negative-sequence signals in the αβ frame -/

section NegativeSequence

open Complex

/-- Negative-sequence three-phase signal `V cos(θ + φ)`, `V cos(θ + 2π/3 + φ)`,
`V cos(θ − 2π/3 + φ)` (phases `b`, `c` swapped with respect to `Transform.balanced`). -/
def negSeq (V φ θ : ℝ) : Fin 3 → ℝ :=
  ![V * Real.cos (θ + φ), V * Real.cos (θ + 2 * Real.pi / 3 + φ),
    V * Real.cos (θ - 2 * Real.pi / 3 + φ)]

/-- A negative-sequence signal is `V e^{−j(θ+φ)}` in αβ: `(V cos(θ + φ), −V sin(θ + φ))`. -/
@[powerlib_foundation] theorem clarke_mulVec_negSeq (V φ θ : ℝ) :
    Transform.clarke *ᵥ negSeq V φ θ = ![V * Real.cos (θ + φ), -(V * Real.sin (θ + φ))] := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h1 : θ + 2 * Real.pi / 3 + φ = (θ + φ) + 2 * Real.pi / 3 := by ring
  have h2 : θ - 2 * Real.pi / 3 + φ = (θ + φ) - 2 * Real.pi / 3 := by ring
  simp only [negSeq, h1, h2]
  generalize θ + φ = ψ
  rw [Real.cos_sub ψ, Real.cos_add ψ, cos_two_pi_div_three, sin_two_pi_div_three]
  ext i; fin_cases i <;>
    simp [Transform.clarke, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ring
  · linear_combination (-(1 / 3)) * V * Real.sin ψ * h3

/-- In complex form, `toComplex (clarke · negSeq) = V e^{−j(θ+φ)}`. -/
@[powerlib_foundation] theorem toComplex_clarke_negSeq (V φ θ : ℝ) :
    Transform.toComplex (Transform.clarke *ᵥ negSeq V φ θ) =
      V * Complex.exp (-((θ + φ : ℝ) : ℂ) * I) := by
  rw [clarke_mulVec_negSeq]
  have he : Complex.exp (-((θ + φ : ℝ) : ℂ) * I) =
      ((Real.cos (θ + φ) : ℝ) : ℂ) - ((Real.sin (θ + φ) : ℝ) : ℂ) * I := by
    rw [show -((θ + φ : ℝ) : ℂ) * I = ((-(θ + φ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  rw [he]
  generalize Real.cos (θ + φ) = c
  generalize Real.sin (θ + φ) = sn
  apply Complex.ext <;> simp [Transform.toComplex]

end NegativeSequence

end powerlib.Transform
