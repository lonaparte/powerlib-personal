import dependencies.Mathlib
import theorem.Attributes
import theorem.Transform.ParkABC
import theorem.Transform.Planar
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Clarke and Park coordinate transformations

Domain identities of the chosen Clarke and Park transformations, with general algebraic helpers.

Scope.
Conventions fixed by this module:
* A planar (αβ or dq) vector is `Fin 2 → ℝ`, component `0` = α (resp. d), component `1` = β
  (resp. q). Its complex form `toComplex x = x 0 + x 1 * I` and the rotation generator `J` are
  the generic planar algebra of `theorem/Transform/Planar.lean`.
* `rot θ` is the counter-clockwise rotation by `θ` (dq → αβ). The Park matrix is
  `park θ = [[cos θ, sin θ], [-sin θ, cos θ]]` (αβ → dq), exactly `conventions.md` §4.
  Hence `park θ = rot (-θ)` (`park_eq_rot_neg`) and, in complex form,
  `x^{dq} = x^{αβ} · e^{-jθ}`. `park_mul_rot`, `rot_mul_park`: the two are mutually inverse;
  `frameRotation_power_invariant`: `rot δ` preserves the port power `v·i` (machine frame vs
  common DQ frame, `theory/T-power-system-ph.md` §1.2).
* `J = [[0, -1], [1, 0]]` generates the rotation (`d/dθ rot θ = J · rot θ`, `rot_mul_J`); in
  complex form it is multiplication by `j` (`toComplex_J_mulVec`).
* Scalar components: `parkD θ x_d x_q`, `parkQ θ x_d x_q` are the two rows of `park θ` applied to
  `(x_d, x_q)` (system → controller frame, `conventions.md` §D4) and `iparkD`, `iparkQ` those of
  `rot θ` (controller → system); `parkD_ipark` … `iparkQ_park` (inverse pairs), `park_dot` (dot
  product preserved), `park_dist_sq` (`‖z − rot θ w‖ = ‖park θ z − w‖`), `parkD_J`, `parkQ_J`
  (commutation with `J`), `hasDerivWithinAt_parkD_parkQ` (their rotating-frame chain rule
  `(park θ z)' = park θ z' − θ' J park θ z`, on any set).
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
  (`hasDerivAt_park_mulVec` at `θ = id`, `x` constant, `t = 0`: `d/dθ (park θ · x)|₀ = −J x`)
  gives the PLL frame projections of `T-gfl-impedance.md` §1.3.
* The element laws read through Park are with the elements: the αβ / dq KVL of one series R–L
  branch and its trajectory correspondence (`alphaBetaRL_iff_dqRL`) in
  `theorem/Passive/DqRL.lean`, the node equation of a shunt G–C element in the dq frame
  (`Passive.ParallelRLC.capacitor_dq`: `C dv/dt = i − G v − ω C J v`, the cross term of
  `T-gfl-impedance.md` §1.7) in `theorem/Passive/Dq.lean`.

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

/-! ## Elementary identities -/

@[tmio M, simp, powerlib_domain] theorem rot_apply_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    rot θ *ᵥ x = ![Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1] := by
  ext i; fin_cases i
  · simp [rot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  · simp [rot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[tmio M, simp, powerlib_domain] theorem park_apply_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    park θ *ᵥ x = ![Real.cos θ * x 0 + Real.sin θ * x 1, -Real.sin θ * x 0 + Real.cos θ * x 1] := by
  ext i; fin_cases i <;> simp [park, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[tmio M, powerlib_domain] theorem park_eq_rot_neg (θ : ℝ) : park θ = rot (-θ) := by
  simp [park, rot]

@[tmio M, powerlib_domain] theorem park_eq_transpose_rot (θ : ℝ) : park θ = (rot θ)ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [park, rot]

@[tmio M, simp, powerlib_domain] theorem rot_zero : rot 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot]

@[tmio M, simp, powerlib_domain] theorem park_zero : park 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [park]

@[tmio M, powerlib_domain] theorem rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  simp only [rot, mul_fin_two, Real.cos_add, Real.sin_add]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

@[tmio M, powerlib_domain] theorem rot_mul_park (θ : ℝ) : rot θ * park θ = 1 := by
  rw [park_eq_rot_neg, ← rot_add, add_neg_cancel, rot_zero]

@[tmio M, powerlib_domain] theorem park_mul_rot (θ : ℝ) : park θ * rot θ = 1 := by
  rw [park_eq_rot_neg, ← rot_add, neg_add_cancel, rot_zero]

/-- T-power-system-ph §1.2: the rotation `R(δ)` is orthogonal, so the port power
`v_d i_d + v_q i_q` is the same in the machine frame and in the common DQ frame. -/
@[tmio M, powerlib_domain] theorem frameRotation_power_invariant (δ : ℝ) (v i : Fin 2 → ℝ) :
    (Transform.rot δ *ᵥ v) ⬝ᵥ (Transform.rot δ *ᵥ i) = v ⬝ᵥ i := by
  simp only [Transform.rot_apply_mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h := Real.sin_sq_add_cos_sq δ
  linear_combination (v 0 * i 0 + v 1 * i 1) * h

@[tmio M, powerlib_domain] theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  rw [rot, det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Park is a proper rotation: it lies in `SO(2)`. -/
@[tmio M, powerlib_domain] theorem park_mem_specialOrthogonalGroup (θ : ℝ) :
    park θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, by rw [park_eq_rot_neg, det_rot]⟩
  rw [show (park θ)ᵀ = rot θ by rw [park_eq_transpose_rot, transpose_transpose]]
  exact park_mul_rot θ

@[tmio M, powerlib_domain] theorem rot_mul_J (θ : ℝ) : rot θ * J = J * rot θ := by
  simp only [rot, J, mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ## Complex form versus matrix form (`T-park-transformation.md` §1.2) -/

/-- Matrix rotation is complex multiplication by `e^{jθ}`. -/
@[tmio M, powerlib_domain] theorem toComplex_rot_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    toComplex (rot θ *ᵥ x) = toComplex x * Complex.exp (θ * Complex.I) := by
  apply Complex.ext <;>
    simp [toComplex, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] <;> ring

/-- Park is complex multiplication by `e^{-jθ}`: `x^{dq} = x^{αβ} e^{-jθ}` (§1.2 boxed). -/
@[tmio M, powerlib_domain] theorem toComplex_park_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    toComplex (park θ *ᵥ x) = toComplex x * Complex.exp (-(θ * Complex.I)) := by
  rw [park_eq_rot_neg, toComplex_rot_mulVec]
  push_cast
  ring_nf

/-- Rotation preserves the Euclidean norm. -/
@[tmio M, powerlib_domain] theorem norm_rot_mulVec (θ : ℝ) (x : Fin 2 → ℝ) :
    ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm (rot θ *ᵥ x)‖ = ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm x‖ := by
  have h := frameRotation_power_invariant θ x x
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, dotProduct, sq] using h

/-! ## Chain rule in a rotating frame (`T-park-transformation.md` §1.3) -/

/-- Matrix form of the §1.3 chain rule: if `x^{αβ}(t) = rot θ(t) · x^{dq}(t)` then
`ẋ^{αβ} = rot θ · (ẋ^{dq} + ω J x^{dq})`, with `ω = θ̇` (any differentiable frame angle). -/
@[tmio M, powerlib_domain] theorem hasDerivAt_rot_mulVec {θ : ℝ → ℝ} {ω : ℝ} {x : ℝ → Fin 2 → ℝ}
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

/-- The same chain rule for the Park direction:
`d/dt (park θ · x) = park θ · ẋ − ω J (park θ · x)`. At `θ = id`, `x` constant and `t = 0` it is
the first-order frame rotation `d/dθ (park θ · x)|₀ = −J x`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_park_mulVec {θ : ℝ → ℝ} {ω : ℝ} {x : ℝ → Fin 2 → ℝ}
    {x' : Fin 2 → ℝ} {t : ℝ} (hθ : HasDerivAt θ ω t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => park (θ s) *ᵥ x s)
      (park (θ t) *ᵥ x' - ω • (J *ᵥ (park (θ t) *ᵥ x t))) t := by
  have h := hasDerivAt_rot_mulVec hθ.neg hx
  simp only [Pi.neg_apply] at h
  rw [show (fun s => park (θ s) *ᵥ x s) = fun s => rot (-θ s) *ᵥ x s from
    funext fun s => by rw [park_eq_rot_neg]]
  convert h using 1
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← park_eq_rot_neg, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, park_eq_rot_neg, rot_mul_J, neg_smul, sub_eq_add_neg]

/-- Complex form of the §1.3 boxed chain rule:
`d/dt (x^{dq} e^{jθ}) = (ẋ^{dq} + jω x^{dq}) e^{jθ}`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_mul_cexp {θ : ℝ → ℝ} {ω : ℝ} {z : ℝ → ℂ} {z' : ℂ}
    {t : ℝ} (hθ : HasDerivAt θ ω t) (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => z s * Complex.exp (θ s * Complex.I))
      ((z' + ω * Complex.I * z t) * Complex.exp (θ t * Complex.I)) t := by
  have he := (hθ.ofReal_comp.mul_const Complex.I).cexp
  convert hz.mul he using 1
  ring

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

@[tmio M, simp, powerlib_domain] theorem parkD_ipark (θ x y : ℝ) :
    parkD θ (iparkD θ x y) (iparkQ θ x y) = x := by
  unfold parkD iparkD iparkQ; linear_combination x * sin_sq_add_cos_sq θ

@[tmio M, simp, powerlib_domain] theorem parkQ_ipark (θ x y : ℝ) :
    parkQ θ (iparkD θ x y) (iparkQ θ x y) = y := by
  unfold parkQ iparkD iparkQ; linear_combination y * sin_sq_add_cos_sq θ

@[tmio M, simp, powerlib_domain] theorem iparkD_park (θ x y : ℝ) :
    iparkD θ (parkD θ x y) (parkQ θ x y) = x := by
  unfold parkD parkQ iparkD; linear_combination x * sin_sq_add_cos_sq θ

@[tmio M, simp, powerlib_domain] theorem iparkQ_park (θ x y : ℝ) :
    iparkQ θ (parkD θ x y) (parkQ θ x y) = y := by
  unfold parkD parkQ iparkQ; linear_combination y * sin_sq_add_cos_sq θ

/-- The rotation preserves the dot product. -/
@[tmio M, powerlib_domain] theorem park_dot (θ x y u v : ℝ) :
    parkD θ x y * parkD θ u v + parkQ θ x y * parkQ θ u v = x * u + y * v := by
  unfold parkD parkQ; linear_combination (x * u + y * v) * sin_sq_add_cos_sq θ

/-- The rotation commutes with the generator `J (x, y) = (−y, x)`. -/
@[tmio M, powerlib_domain] theorem parkD_J (θ x y : ℝ) : parkD θ (-y) x = -parkQ θ x y := by
  unfold parkD parkQ; ring

@[tmio M, powerlib_domain] theorem parkQ_J (θ x y : ℝ) : parkQ θ (-y) x = parkD θ x y := by
  unfold parkD parkQ; ring

/-- The distance of `z` to the rotated vector `rot θ w` is the distance of `park θ z` to `w`. -/
@[tmio M, powerlib_domain] theorem park_dist_sq (θ a b d q : ℝ) :
    (a - iparkD θ d q) ^ 2 + (b - iparkQ θ d q) ^ 2 =
      (parkD θ a b - d) ^ 2 + (parkQ θ a b - q) ^ 2 := by
  unfold parkD parkQ iparkD iparkQ
  linear_combination (d ^ 2 + q ^ 2 - a ^ 2 - b ^ 2) * sin_sq_add_cos_sq θ

/-- The chain rule of the Park rows in a rotating frame, for arbitrary differentiable `θ`, `a`,
`b` on any set: `(park θ (a, b))' = park θ (a', b') − θ' J park θ (a, b)`. -/
@[tmio M, powerlib_domain] theorem hasDerivWithinAt_parkD_parkQ {θ a b : ℝ → ℝ}
    {θ' a' b' t : ℝ} {s : Set ℝ} (hθ : HasDerivWithinAt θ θ' s t)
    (ha : HasDerivWithinAt a a' s t) (hb : HasDerivWithinAt b b' s t) :
    HasDerivWithinAt (fun τ => parkD (θ τ) (a τ) (b τ))
        (parkD (θ t) a' b' + θ' * parkQ (θ t) (a t) (b t)) s t ∧
      HasDerivWithinAt (fun τ => parkQ (θ τ) (a τ) (b τ))
        (parkQ (θ t) a' b' - θ' * parkD (θ t) (a t) (b t)) s t := by
  have hc := hθ.cos
  have hs := hθ.sin
  constructor
  · convert (hc.mul ha).add (hs.mul hb) using 1
    · funext τ
      simp [parkD]
    · simp only [parkD, parkQ]
      ring
  · convert (hs.neg.mul ha).add (hc.mul hb) using 1
    · funext τ
      simp [parkQ]
    · simp only [parkD, parkQ, Pi.neg_apply]
      ring

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

@[tmio T, powerlib_foundation] private lemma sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

@[tmio T, powerlib_foundation] private lemma sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

@[tmio M, powerlib_domain] theorem clarke_mul_clarkeInv : clarke * clarkeInv = 1 := by
  have h3 := sqrt_three_mul_self
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clarke, clarkeInv, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith [h3]

@[tmio M, powerlib_domain] theorem clarke_mul_transpose : clarke * clarkeᵀ = (2 / 3 : ℝ) • 1 := by
  have h3 := sqrt_three_mul_self
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clarke, Matrix.mul_apply, Fin.sum_univ_three] <;> linarith [h3]

/-- On zero-sequence-free vectors (`x_a + x_b + x_c = 0`) the inverse Clarke reconstructs `abc`. -/
@[tmio M, powerlib_domain] theorem clarkeInv_mulVec_clarke_mulVec (x : Fin 3 → ℝ)
    (hx : x 0 + x 1 + x 2 = 0) : clarkeInv *ᵥ (clarke *ᵥ x) = x := by
  have h3 := sqrt_three_mul_self
  ext i; fin_cases i <;>
    simp [clarke, clarkeInv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  · linear_combination (-1/3) * hx
  · linear_combination (-1/3) * hx + (1/6) * (x 1 - x 2) * h3
  · linear_combination (-1/3) * hx - (1/6) * (x 1 - x 2) * h3

/-- Amplitude-invariant Clarke power: `v · i = (3/2)(v_α i_α + v_β i_β)` when `i` is
zero-sequence free. -/
@[tmio M, powerlib_domain] theorem dotProduct_eq_three_halves_clarke (v i : Fin 3 → ℝ)
    (hi : i 0 + i 1 + i 2 = 0) :
    v ⬝ᵥ i = (3 / 2 : ℝ) * ((clarke *ᵥ v) ⬝ᵥ (clarke *ᵥ i)) := by
  have h3 := sqrt_three_mul_self
  simp [clarke, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  linear_combination (1/3) * (v 0 + v 1 + v 2) * hi - (1/6) * (v 1 - v 2) * (i 1 - i 2) * h3

@[tmio M, powerlib_domain] theorem clarkePI_mul_transpose : clarkePI * clarkePIᵀ = 1 := by
  have h3 := sqrt_three_mul_self
  have h2 := sqrt_two_mul_self
  have h3' : (0 : ℝ) < Real.sqrt 3 := by positivity
  have h2' : (0 : ℝ) < Real.sqrt 2 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clarkePI, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | (field_simp; nlinarith [h3, h2])

/-- Power invariance: `(T v) · (T i) = v · i` for the power-invariant Clarke `T`. -/
@[tmio M, powerlib_domain] theorem clarkePI_dotProduct (v i : Fin 3 → ℝ) :
    (clarkePI *ᵥ v) ⬝ᵥ (clarkePI *ᵥ i) = v ⬝ᵥ i := by
  have hTT : clarkePIᵀ * clarkePI = 1 := mul_eq_one_comm.mp clarkePI_mul_transpose
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
@[tmio M, powerlib_domain] theorem balanced_sum (V φ θ : ℝ) :
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
@[tmio M, powerlib_domain] theorem clarke_mulVec_balanced (V φ θ : ℝ) :
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
@[tmio M, powerlib_domain] theorem parkABC_mulVec_balanced (V φ θ : ℝ) :
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
@[tmio M, powerlib_domain] theorem clarke_mulVec_negSeq (V φ θ : ℝ) :
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
@[tmio M, powerlib_domain] theorem toComplex_clarke_negSeq (V φ θ : ℝ) :
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
