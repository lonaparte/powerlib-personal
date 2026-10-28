import theorem.PLL.PIPLL

/-! # Liénard (velocity) coordinates of the PI-PLL and the Bogdanov–Takens coefficients

Foundation module: a coordinate change and exact normal-form coefficients for the PI-PLL.

Model boundary.
The model of `theorem/PLL/PIPLL.lean`, with the same boundary: state `(θ, η)`,
`θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)`, continuous time, constant `δω`.

Source: work-sync `theory/T-bogdanov-takens-bifurcation.md` §1.2, §1.5–§1.6 (the note leaves
`b ≠ 0` "to numerical verification"; here `b₁₁ = K_p h''(θ*)` is proved exactly);
`theory/T-gfl-dynamics.md` §1.13; `projects/vsc-stochastic-stability/notes/concepts/
equilibria-and-bifurcation.md` §9.

Results.
* Velocity coordinates `w = θ̇ = K_p h(θ) + K_i η − δω` (`piPLLVelocityCoord`). For `K_i ≠ 0`
  this is a bijection of `ℝ²` (`piPLLVelocityCoordInv`), and, for differentiable `h` with
  derivative `h'`, it maps solutions of the PI-PLL field to solutions of the Liénard field
  `θ̇ = w`, `ẇ = K_i h(θ) + K_p h'(θ) w` (`piPLLLienardField`) and back
  (`isIntegralCurveOn_piPLLVelocityCoord`, `isIntegralCurveOn_piPLLVelocityCoordInv`).
  The constant offset `δω` disappears from the Liénard form.
* At a zero `θ*` of `h` with `h'(θ*) = 0` (the degenerate case of
  `piPLL_jacobian_nilpotent_of_deriv_zero`) the equilibrium is `(θ*, 0)` in `(θ, w)`, the
  Jacobian of the Liénard field is the Jordan block `[[0, 1], [0, 0]]`, and the second component
  `F(u, w) = K_i h(θ* + u) + K_p h'(θ* + u) w` has, exactly,
  `F_uu(0,0) = b₂₀ = K_i h''(θ*)`, `F_uw(0,0) = b₁₁ = K_p h''(θ*)`, `F_ww = b₀₂ = 0`
  (`bt_b20`, `bt_b11`, `bt_b02`). With the first equation exactly `u̇ = w`, the quadratic
  Bogdanov–Takens nondegeneracy coefficients are `a = b₂₀ / 2` and `b = b₁₁`; both are nonzero iff
  `h''(θ*) ≠ 0` (for `K_p, K_i ≠ 0`).

Family and connection conclusions.
This module defines no family and states no behaviour of the
PI-PLL family (`theorem/PLL/PIPLLFamily.lean`). The conjugacy of the integral curves of the raw
PI-PLL field and the Liénard field is a change of coordinates for arbitrary `h`, `K_p`, `K_i`,
`δω` (generic foundation, Mathlib integral curves); the Jacobian and BT coefficients are static.

Caveat (not a correction of a formula): a Bogdanov–Takens *bifurcation* also needs a transversal
two-parameter unfolding. For this family `K_i · tr J + K_p · det J = 0` holds identically
(`piPLLJacobian_trace_det_relation`), so the pair `(tr, det)` of the linearization stays on one
line through the origin; no claim about a versal unfolding, Hopf or homoclinic curves is made here
(consistent with the narrowed statement of the vsc note §9).
-/

noncomputable section
namespace powerlib.PLL
open Matrix
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## A Jacobian helper on `ℝ²` -/

/-- If `F₀`, `F₁ : ℝ² → ℝ` have derivatives `v ↦ a v₀ + b v₁` and `v ↦ c v₀ + d v₁` at `x`,
then `y ↦ (F₀ y, F₁ y)` has Jacobian matrix `[[a, b], [c, d]]` at `x`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_piPLLState_comp {F₀ F₁ : ℝ² → ℝ} {x : ℝ²}
    {L₀ L₁ : ℝ² →L[ℝ] ℝ} {a b c d : ℝ} (h₀ : HasFDerivAt F₀ L₀ x)
    (h₁ : HasFDerivAt F₁ L₁ x) (hL₀ : ∀ v : ℝ², L₀ v = a * v 0 + b * v 1)
    (hL₁ : ∀ v : ℝ², L₁ v = c * v 0 + d * v 1) :
    HasFDerivAt (fun y => PhasePlane.mk (F₀ y) (F₁ y))
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![a, b; c, d]) x := by
  have hG : HasFDerivAt (fun y : ℝ² => ![F₀ y, F₁ y]) (ContinuousLinearMap.pi ![L₀, L₁]) x := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa using h₀
    · simpa using h₁
  have hE :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp x hG
  have hfun : (fun y => PhasePlane.mk (F₀ y) (F₁ y)) =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
        (fun y : ℝ² => ![F₀ y, F₁ y]) := rfl
  rw [hfun]
  refine hE.congr_fderiv ?_
  ext v i
  rw [Matrix.ofLp_toEuclideanCLM]
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hL₀]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hL₁]

@[powerlib_foundation] theorem hasFDerivAt_coord_zero (x : ℝ²) :
    HasFDerivAt (fun y : ℝ² => y 0)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ) x :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt

@[powerlib_foundation] theorem hasFDerivAt_coord_one (x : ℝ²) :
    HasFDerivAt (fun y : ℝ² => y 1)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ) x :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt

/-! ## Velocity coordinates and the Liénard field -/

/-- `(θ, η) ↦ (θ, w)`, `w = K_p h(θ) + K_i η − δω` (`= θ̇`). -/
def piPLLVelocityCoord (h : ℝ → ℝ) (Kp Ki δω : ℝ) (x : ℝ²) : ℝ² :=
  PhasePlane.mk (x 0) (Kp * h (x 0) + Ki * x 1 - δω)

/-- Inverse of the velocity coordinates: `(θ, w) ↦ (θ, (w − K_p h(θ) + δω) / K_i)`. -/
def piPLLVelocityCoordInv (h : ℝ → ℝ) (Kp Ki δω : ℝ) (y : ℝ²) : ℝ² :=
  PhasePlane.mk (y 0) (Ki⁻¹ * (y 1 - Kp * h (y 0) + δω))

/-- Liénard field `θ̇ = w`, `ẇ = K_i h(θ) + K_p h'(θ) w` (`h'` the derivative of `h`). -/
def piPLLLienardField (h h' : ℝ → ℝ) (Kp Ki : ℝ) (y : ℝ²) : ℝ² :=
  PhasePlane.mk (y 1) (Ki * h (y 0) + Kp * h' (y 0) * y 1)

@[powerlib_foundation] theorem piPLLVelocityCoordInv_comp {h : ℝ → ℝ} {Kp Ki δω : ℝ}
    (hKi : Ki ≠ 0) (x : ℝ²) :
    piPLLVelocityCoordInv h Kp Ki δω (piPLLVelocityCoord h Kp Ki δω x) = x := by
  rw [PhasePlane.ext_iff']
  simp only [piPLLVelocityCoordInv, piPLLVelocityCoord, PhasePlane.mk_apply_zero,
    PhasePlane.mk_apply_one]
  refine ⟨trivial, ?_⟩
  field_simp
  ring

@[powerlib_foundation] theorem piPLLVelocityCoord_comp_inv {h : ℝ → ℝ} {Kp Ki δω : ℝ}
    (hKi : Ki ≠ 0) (y : ℝ²) :
    piPLLVelocityCoord h Kp Ki δω (piPLLVelocityCoordInv h Kp Ki δω y) = y := by
  rw [PhasePlane.ext_iff']
  simp only [piPLLVelocityCoordInv, piPLLVelocityCoord, PhasePlane.mk_apply_zero,
    PhasePlane.mk_apply_one]
  refine ⟨trivial, ?_⟩
  field_simp
  ring

/-- The equilibrium `(θ*, δω / K_i)` is sent to `(θ*, 0)`. -/
@[powerlib_foundation] theorem piPLLVelocityCoord_equilibrium {h : ℝ → ℝ} {Kp Ki δω θ : ℝ}
    (hKi : Ki ≠ 0) (hzero : h θ = 0) :
    piPLLVelocityCoord h Kp Ki δω (PhasePlane.mk θ (δω / Ki)) = PhasePlane.mk θ 0 := by
  rw [PhasePlane.ext_iff']
  simp only [piPLLVelocityCoord, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, hzero]
  refine ⟨trivial, ?_⟩
  field_simp
  ring

/-- Derivative of the velocity coordinates: Jacobian `[[1, 0], [K_p h'(θ), K_i]]`. -/
@[powerlib_foundation] theorem hasFDerivAt_piPLLVelocityCoord {h : ℝ → ℝ} {Kp Ki δω g : ℝ}
    {x : ℝ²} (hh : HasDerivAt h g (x 0)) :
    HasFDerivAt (piPLLVelocityCoord h Kp Ki δω)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 0; Kp * g, Ki]) x := by
  have hc := hh.comp_hasFDerivAt x (hasFDerivAt_coord_zero x)
  have h1 := ((hc.const_mul Kp).add ((hasFDerivAt_coord_one x).const_mul Ki)).sub_const δω
  exact hasFDerivAt_piPLLState_comp (hasFDerivAt_coord_zero x) h1 (fun v => by simp)
    (fun v => by simp; ring)

/-- Derivative of the inverse velocity coordinates: `[[1, 0], [−K_p h'(θ)/K_i, 1/K_i]]`. -/
@[powerlib_foundation] theorem hasFDerivAt_piPLLVelocityCoordInv {h : ℝ → ℝ} {Kp Ki δω g : ℝ}
    {y : ℝ²} (hh : HasDerivAt h g (y 0)) :
    HasFDerivAt (piPLLVelocityCoordInv h Kp Ki δω)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 0; -(Kp * g) / Ki, 1 / Ki]) y := by
  have hc := hh.comp_hasFDerivAt y (hasFDerivAt_coord_zero y)
  have h1 := (((hasFDerivAt_coord_one y).sub (hc.const_mul Kp)).add_const δω).const_mul Ki⁻¹
  exact hasFDerivAt_piPLLState_comp (hasFDerivAt_coord_zero y) h1 (fun v => by simp)
    (fun v => by simp; ring)

/-- Conjugacy identity: `DΦ(x) f(x) = G(Φ(x))`. -/
@[powerlib_foundation] theorem piPLLVelocityCoord_pushforward {h h' : ℝ → ℝ} {Kp Ki δω : ℝ}
    (_hh : ∀ θ, HasDerivAt h (h' θ) θ) (x : ℝ²) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 0; Kp * h' (x 0), Ki]
        (piPLLField h Kp Ki δω x) =
      piPLLLienardField h h' Kp Ki (piPLLVelocityCoord h Kp Ki δω x) := by
  rw [PhasePlane.ext_iff']
  constructor
  · simp [piPLLLienardField, piPLLVelocityCoord, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
  · simp [piPLLLienardField, piPLLVelocityCoord, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring

/-- Inverse conjugacy identity: `DΦ⁻¹(y) G(y) = f(Φ⁻¹(y))` (`K_i ≠ 0`). -/
@[powerlib_foundation] theorem piPLLVelocityCoordInv_pushforward {h h' : ℝ → ℝ} {Kp Ki δω : ℝ}
    (hKi : Ki ≠ 0) (y : ℝ²) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, 0; -(Kp * h' (y 0)) / Ki, 1 / Ki]
        (piPLLLienardField h h' Kp Ki y) =
      piPLLField h Kp Ki δω (piPLLVelocityCoordInv h Kp Ki δω y) := by
  rw [PhasePlane.ext_iff']
  constructor
  · simp [piPLLLienardField, piPLLVelocityCoordInv, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [piPLLLienardField, piPLLVelocityCoordInv, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    field_simp
    ring

/-- Solutions of the PI-PLL field are mapped to solutions of the Liénard field. -/
@[powerlib_foundation] theorem isIntegralCurveOn_piPLLVelocityCoord {h h' : ℝ → ℝ}
    {Kp Ki δω : ℝ} (hh : ∀ θ, HasDerivAt h (h' θ) θ) {φ : ℝ → ℝ²} {s : Set ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => piPLLField h Kp Ki δω x) s) :
    IsIntegralCurveOn (fun t => piPLLVelocityCoord h Kp Ki δω (φ t))
      (fun _ y => piPLLLienardField h h' Kp Ki y) s := by
  intro t ht
  have hd := (hasFDerivAt_piPLLVelocityCoord (Kp := Kp) (Ki := Ki) (δω := δω)
    (hh ((φ t) 0))).comp_hasDerivWithinAt t (hφ t ht)
  rw [piPLLVelocityCoord_pushforward hh] at hd
  exact hd

/-- Solutions of the Liénard field are mapped back to solutions of the PI-PLL field
(`K_i ≠ 0`). Together with `isIntegralCurveOn_piPLLVelocityCoord` and the inverse identities
this is a conjugacy of the two flows. -/
@[powerlib_foundation] theorem isIntegralCurveOn_piPLLVelocityCoordInv {h h' : ℝ → ℝ}
    {Kp Ki δω : ℝ} (hKi : Ki ≠ 0) (hh : ∀ θ, HasDerivAt h (h' θ) θ) {ψ : ℝ → ℝ²}
    {s : Set ℝ} (hψ : IsIntegralCurveOn ψ (fun _ y => piPLLLienardField h h' Kp Ki y) s) :
    IsIntegralCurveOn (fun t => piPLLVelocityCoordInv h Kp Ki δω (ψ t))
      (fun _ x => piPLLField h Kp Ki δω x) s := by
  intro t ht
  have hd := (hasFDerivAt_piPLLVelocityCoordInv (Kp := Kp) (Ki := Ki) (δω := δω)
    (hh ((ψ t) 0))).comp_hasDerivWithinAt t (hψ t ht)
  rw [piPLLVelocityCoordInv_pushforward hKi] at hd
  exact hd

/-! ## Jacobian of the Liénard field and the BT coefficients -/

/-- Jacobian of the Liénard field at `y`: `[[0, 1], [K_i h'(θ) + K_p h''(θ) w, K_p h'(θ)]]`. -/
@[powerlib_foundation] theorem hasFDerivAt_piPLLLienardField {h h' : ℝ → ℝ} {Kp Ki h2 : ℝ}
    {y : ℝ²} (hh : HasDerivAt h (h' (y 0)) (y 0)) (hh' : HasDerivAt h' h2 (y 0)) :
    HasFDerivAt (piPLLLienardField h h' Kp Ki)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        !![0, 1; Ki * h' (y 0) + Kp * h2 * y 1, Kp * h' (y 0)]) y := by
  have hc := hh.comp_hasFDerivAt y (hasFDerivAt_coord_zero y)
  have hc' := hh'.comp_hasFDerivAt y (hasFDerivAt_coord_zero y)
  have h1 := (hc.const_mul Ki).add ((hc'.const_mul Kp).mul (hasFDerivAt_coord_one y))
  exact hasFDerivAt_piPLLState_comp (hasFDerivAt_coord_one y) h1 (fun v => by simp)
    (fun v => by simp; ring)

/-- At a double zero (`h(θ*) = h'(θ*) = 0`) the Liénard Jacobian at `(θ*, 0)` is the Jordan block
`[[0, 1], [0, 0]]`, and `(θ*, 0)` is an equilibrium. -/
@[powerlib_foundation] theorem piPLLLienard_jordan_block {h h' : ℝ → ℝ} {Kp Ki θ h2 : ℝ}
    (hzero : h θ = 0) (hd0 : h' θ = 0) (hh : HasDerivAt h (h' θ) θ) (hh' : HasDerivAt h' h2 θ) :
    piPLLLienardField h h' Kp Ki (PhasePlane.mk θ 0) = 0 ∧
      HasFDerivAt (piPLLLienardField h h' Kp Ki)
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![0, 1; 0, 0]) (PhasePlane.mk θ 0) := by
  refine ⟨?_, ?_⟩
  · rw [PhasePlane.ext_iff']
    simp [piPLLLienardField, hzero]
  · have := hasFDerivAt_piPLLLienardField (Kp := Kp) (Ki := Ki) (y := PhasePlane.mk θ 0)
      (by simpa using hh) (by simpa using hh')
    simpa [hd0] using this

/-- Second component of the Liénard field near `θ*`:
`F(u, w) = K_i h(θ* + u) + K_p h'(θ* + u) w`. -/
def lienardSecond (h h' : ℝ → ℝ) (Kp Ki θ : ℝ) (u w : ℝ) : ℝ :=
  Ki * h (θ + u) + Kp * h' (θ + u) * w

@[powerlib_foundation] theorem lienardSecond_hasDerivAt_u {h h' : ℝ → ℝ} {Kp Ki θ : ℝ}
    (hh : ∀ t, HasDerivAt h (h' t) t) (u : ℝ) :
    HasDerivAt (fun u' => lienardSecond h h' Kp Ki θ u' 0) (Ki * h' (θ + u)) u := by
  have h1 : HasDerivAt (fun u' => θ + u') 1 u := by
    simpa using (hasDerivAt_id u).const_add θ
  have := ((hh (θ + u)).comp u h1).const_mul Ki
  simpa [lienardSecond] using this

@[powerlib_foundation] theorem lienardSecond_hasDerivAt_w (h h' : ℝ → ℝ) (Kp Ki θ u w : ℝ) :
    HasDerivAt (fun w' => lienardSecond h h' Kp Ki θ u w') (Kp * h' (θ + u)) w := by
  have := (hasDerivAt_id w).const_mul (Kp * h' (θ + u))
  have h2 := this.const_add (Ki * h (θ + u))
  simpa [lienardSecond] using h2

@[powerlib_foundation] theorem hasDerivAt_shift_mul {h' : ℝ → ℝ} {θ h2 : ℝ} (c : ℝ)
    (hh' : HasDerivAt h' h2 θ) : HasDerivAt (fun u => c * h' (θ + u)) (c * h2) 0 := by
  have h1 : HasDerivAt (fun u' => θ + u') 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add θ
  have := (hh'.comp_of_eq 0 h1 (by simp)).const_mul c
  simpa using this

/-- `b₂₀ = F_uu(0, 0) = K_i h''(θ*)`. -/
@[powerlib_foundation] theorem bt_b20 {h h' : ℝ → ℝ} {Kp Ki θ h2 : ℝ}
    (hh : ∀ t, HasDerivAt h (h' t) t) (hh' : HasDerivAt h' h2 θ) :
    deriv (fun u => deriv (fun u' => lienardSecond h h' Kp Ki θ u' 0) u) 0 = Ki * h2 := by
  have e : (fun u => deriv (fun u' => lienardSecond h h' Kp Ki θ u' 0) u) =
      fun u => Ki * h' (θ + u) := by
    funext u
    exact (lienardSecond_hasDerivAt_u hh u).deriv
  rw [e]
  exact (hasDerivAt_shift_mul Ki hh').deriv

/-- `b₁₁ = F_uw(0, 0) = K_p h''(θ*)`. -/
@[powerlib_foundation] theorem bt_b11 {h h' : ℝ → ℝ} {Kp Ki θ h2 : ℝ}
    (hh' : HasDerivAt h' h2 θ) :
    deriv (fun u => deriv (fun w => lienardSecond h h' Kp Ki θ u w) 0) 0 = Kp * h2 := by
  have e : (fun u => deriv (fun w => lienardSecond h h' Kp Ki θ u w) 0) =
      fun u => Kp * h' (θ + u) := by
    funext u
    exact (lienardSecond_hasDerivAt_w h h' Kp Ki θ u 0).deriv
  rw [e]
  exact (hasDerivAt_shift_mul Kp hh').deriv

/-- `b₀₂ = F_ww(0, 0) = 0` (`F` is affine in `w`). -/
@[powerlib_foundation] theorem bt_b02 (h h' : ℝ → ℝ) (Kp Ki θ : ℝ) :
    deriv (fun w => deriv (fun w' => lienardSecond h h' Kp Ki θ 0 w') w) 0 = 0 := by
  have e : (fun w => deriv (fun w' => lienardSecond h h' Kp Ki θ 0 w') w) =
      fun _ => Kp * h' (θ + 0) := by
    funext w
    exact (lienardSecond_hasDerivAt_w h h' Kp Ki θ 0 w).deriv
  rw [e]
  exact deriv_const _ _

/-- At a double zero the linear part of `F` vanishes: `F(0,0) = F_u(0,0) = F_w(0,0) = 0`. -/
@[powerlib_foundation] theorem bt_linear_part {h h' : ℝ → ℝ} {Kp Ki θ : ℝ}
    (hh : ∀ t, HasDerivAt h (h' t) t) (hzero : h θ = 0) (hd0 : h' θ = 0) :
    lienardSecond h h' Kp Ki θ 0 0 = 0 ∧
      deriv (fun u => lienardSecond h h' Kp Ki θ u 0) 0 = 0 ∧
      deriv (fun w => lienardSecond h h' Kp Ki θ 0 w) 0 = 0 := by
  refine ⟨by simp [lienardSecond, hzero], ?_, ?_⟩
  · rw [(lienardSecond_hasDerivAt_u hh 0).deriv]
    simp [hd0]
  · rw [(lienardSecond_hasDerivAt_w h h' Kp Ki θ 0 0).deriv]
    simp [hd0]

/-- BT nondegeneracy (`a = b₂₀/2 ≠ 0` and `b = b₁₁ ≠ 0`) holds iff `h''(θ*) ≠ 0`, when
`K_p, K_i ≠ 0`. -/
@[powerlib_foundation] theorem bt_nondegenerate_iff {Kp Ki h2 : ℝ} (hKp : Kp ≠ 0)
    (hKi : Ki ≠ 0) : (Ki * h2 / 2 ≠ 0 ∧ Kp * h2 ≠ 0) ↔ h2 ≠ 0 := by
  constructor
  · rintro ⟨_, h⟩ h0
    exact h (by rw [h0, mul_zero])
  · intro h
    exact ⟨div_ne_zero (mul_ne_zero hKi h) two_ne_zero, mul_ne_zero hKp h⟩

end powerlib.PLL
