import theorem.Linear.Transfer
import theorem.Linear.Stability

/-! # Single-input single-output plant helpers (foundation)

Library-owned LTI plant lemmas (the codex `Linear/` layer is not modified), shared by the converter
current-loop, DC-link and feedforward modules.

Scope.
* Generic plant algebra about arbitrary `Linear.Plant` data, not a model: nothing here describes a
  physical system and no family is defined. It is the common template layer of the converter
  modules; the spectral `Family` templates built on these plants are in
  `theorem/Spectral/Family.lean`.

Source: standard state-space algebra, used by work-sync `theory/T-gfl-control.md` §1.4,
`theory/T-gfl-impedance.md` §1.4–§1.5, `theory/T-voltage-feedforward.md` §2.2.

Results.
* `transfer_fin_one`, `transfer_fin_two`: closed forms of `Linear.transfer` for one- and
  two-state single-input single-output plants `⟨A, B, C, D⟩` (one port), off the
  characteristic roots. These are plain resolvent computations (adjugate of a 1×1 / 2×2
  matrix). `transfer_eq_of_solution`: a solution `X` of `(sI − A) X = B` gives the transfer
  matrix `C X + D`.
* `negOutput`, `transfer_negOutput`: reversing the output sign of a plant negates its transfer
  matrix. With the output read as a port current, this is the `Y^IN = −Y^OUT` translation
  between the IN-positive and OUT-positive current conventions (work-sync
  `theory/T-gfl-impedance.md` §1.4 / §2.2, `conventions.md` §D8).
* `tendsto_equilibrium`: under a constant input with an equilibrium `e`, every forward-complete
  solution of a plant with a Hurwitz state matrix converges to `e` (the hub's global asymptotic
  stability, `Linear.globallyAsymptoticallyStable_of_isHurwitz`, about the shifted
  equilibrium).
* Constant inputs (a forward solution from `t = 0` is a Mathlib integral curve on `[0, ∞)`,
  `IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)`): `inputField_apply`;
  `trajectory_eq_solution_Ici` (every forward solution is the matrix-exponential solution
  `Linear.solution`, through `Linear.trajectory_eq_solution`); `solution_hasDerivAt`,
  `solution_continuous`; `tendsto_apply_of_isHurwitz` (componentwise convergence);
  `hasDerivWithinAt_apply_zero` (the right derivative at `t = 0` of a coordinate of a forward
  solution of any field is that coordinate of the field at the initial state, so initial rates
  such as RoCoF are read off the field); `inputField_shift` (in deviation coordinates about an
  equilibrium the field is the zero-input field); `exists_not_tendsto_of_eigenvector` (a real
  eigenvector of a positive eigenvalue gives a solution through the equilibrium that converges
  to no value along every component where the eigenvector is nonzero).
* Derivative output: `derivModel` (`(A, B, C A, C B)`) — along any input–state solution of a
  strictly proper plant its output is the time derivative of `C x + D u` (`hasDerivAt_output`),
  and its transfer matrix is `s G(s)` (`transfer_derivModel`).
* Common input: `plantOutput` (`C x + D u`); `tendsto_sub_of_isHurwitz`: two forward solutions of
  a plant with Hurwitz state matrix under the same input signal converge to each other,
  componentwise (their difference solves the zero-input field).
-/

noncomputable section
namespace powerlib.LTI
open Matrix Filter Linear LinearSystems
open scoped Topology

/-- Transfer function of a one-state SISO plant `⟨[a], [b], [c], [d]⟩`:
`c b / (s − a) + d` for `s ≠ a`. -/
@[powerlib_foundation] theorem transfer_fin_one (a b c d : ℝ) {s : ℂ} (hs : s - a ≠ 0) :
    transfer (⟨!![a], !![b], !![c], !![d]⟩ : Plant 1 1) s 0 0 =
      (c : ℂ) * b / (s - a) + d := by
  simp [transfer, characteristicMatrix, Matrix.mul_apply]
  field_simp

/-- Characteristic determinant of a 2×2 state matrix in the literal form `!![a, b; c, d]`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_of (a b c d : ℝ) (s : ℂ) :
    (characteristicMatrix !![a, b; c, d] s).det = (s - a) * (s - d) - (b : ℂ) * c := by
  simp [characteristicMatrix, Matrix.det_fin_two]

/-- Transfer function of a two-state SISO plant, off the characteristic roots. -/
@[powerlib_foundation] theorem transfer_fin_two (a b c d b1 b2 c1 c2 d0 : ℝ) {s : ℂ}
    (hs : (s - a) * (s - d) - (b : ℂ) * c ≠ 0) :
    transfer (⟨!![a, b; c, d], !![b1; b2], !![c1, c2], !![d0]⟩ : Plant 2 1) s 0 0 =
      ((c1 : ℂ) * ((s - d) * b1 + b * b2) + c2 * (c * b1 + (s - a) * b2)) /
        ((s - a) * (s - d) - b * c) + d0 := by
  simp only [transfer, Matrix.inv_def, Ring.inverse_eq_inv', det_characteristicMatrix_of]
  simp [characteristicMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

/-- A solution of `(sI − A) X = B` gives the transfer matrix `C X + D`. -/
@[powerlib_foundation] theorem transfer_eq_of_solution
    {n k : ℕ} (m : Plant n k) (s : ℂ) (X : Matrix (Fin n) (Fin k) ℂ)
    (hM : (characteristicMatrix m.A s).det ≠ 0)
    (hX : characteristicMatrix m.A s * X = complexify m.B) :
    transfer m s = complexify m.C * X + complexify m.D := by
  rw [transfer, Matrix.mul_assoc, ← hX,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hM)]

section Sign

variable {n p : ℕ}

/-- The same plant with the output (and feedthrough) sign reversed. -/
def negOutput (m : Plant n p) : Plant n p := ⟨m.A, m.B, -m.C, -m.D⟩

/-- Reversing the output sign negates the transfer matrix. Read with the output as a port
current: `Y^IN(s) = −Y^OUT(s)`. -/
@[powerlib_foundation] theorem transfer_negOutput (m : Plant n p) (s : ℂ) :
    transfer (negOutput m) s = -transfer m s := by
  simp only [transfer, negOutput, complexify_neg, Matrix.neg_mul, neg_add]

@[powerlib_foundation] theorem negOutput_negOutput (m : Plant n p) :
    negOutput (negOutput m) = m := by
  simp [negOutput]

end Sign

/-! ## Derivative output -/

/-- Derivative-output realization `(A, B, C A, C B)` of a plant. -/
def derivModel {n p : ℕ} (m : Linear.Plant n p) : Linear.Plant n p :=
  ⟨m.A, m.B, m.C * m.A, m.C * m.B⟩

/-- Along any input–state solution `ẋ = A x + B u` of a strictly proper plant (`D = 0`), the
output of `derivModel` is the time derivative of the original output `C x + D u`. Generic: any
plant, any differentiable state signal. -/
@[powerlib_foundation] theorem hasDerivAt_output {n p : ℕ} {m : Linear.Plant n p} (hD : m.D = 0)
    {x : ℝ → Fin n → ℝ} {u : ℝ → Fin p → ℝ} {t : ℝ}
    (hx : HasDerivAt x (m.A *ᵥ x t + m.B *ᵥ u t) t) :
    HasDerivAt (fun τ => m.C *ᵥ x τ + m.D *ᵥ u τ)
      ((derivModel m).C *ᵥ x t + (derivModel m).D *ᵥ u t) t := by
  have hC : HasDerivAt (fun τ => m.C *ᵥ x τ) (m.C *ᵥ (m.A *ᵥ x t + m.B *ᵥ u t)) t := by
    refine hasDerivAt_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.1 hx j).const_mul (m.C i j)
  simp only [hD, Matrix.zero_mulVec, add_zero]
  convert hC using 1
  simp [derivModel, Matrix.mulVec_add, Matrix.mulVec_mulVec]

/-- Transfer of the derivative output: `s H(s)` (`D = 0`, `s` not an eigenvalue). -/
@[powerlib_foundation] theorem transfer_derivModel {n p : ℕ} {m : Linear.Plant n p}
    (hD : m.D = 0) {s : ℂ} (hs : (Linear.characteristicMatrix m.A s).det ≠ 0) :
    Linear.transfer (derivModel m) s = s • Linear.transfer m s := by
  set M := Linear.characteristicMatrix m.A s
  have hA : Linear.complexify m.A = s • 1 - M := by
    simp [M, Linear.characteristicMatrix, Linear.complexify]
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hs)
  simp only [Linear.transfer, derivModel, Linear.complexify_mul, hD]
  change Linear.complexify m.C * Linear.complexify m.A * M⁻¹ * Linear.complexify m.B +
    Linear.complexify m.C * Linear.complexify m.B =
    s • (Linear.complexify m.C * M⁻¹ * Linear.complexify m.B + Linear.complexify 0)
  rw [hA, Linear.complexify_zero, add_zero, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.mul_assoc (Linear.complexify m.C) M, hinv, Matrix.mul_one]
  simp [Matrix.mul_smul, Matrix.smul_mul]

section Trajectory

variable {n p : ℕ}

/-- Constant-input solutions of a plant with a Hurwitz state matrix converge to the
equilibrium: generic foundation, the hub's global asymptotic stability about `e`. -/
@[powerlib_foundation] theorem tendsto_equilibrium (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ : ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Set.Ici t₀)) :
    Tendsto x atTop (𝓝 e) := by
  rw [M.inputField_eq he] at hx
  exact (globallyAsymptoticallyStable_of_isHurwitz e hA).2.2.2 t₀ x hx

/-- Componentwise form, for a solution given by its derivative at every time. -/
@[powerlib_foundation] theorem tendsto_equilibrium_apply (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} (hx : ∀ t, HasDerivAt x (M.inputField u (x t)) t)
    (j : Fin n) : Tendsto (fun t => x t j) atTop (𝓝 (e j)) := by
  have h := tendsto_equilibrium M hA he (t₀ := 0) fun t _ => (hx t).hasDerivWithinAt
  exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.tendsto
    e).comp h

end Trajectory

/-! ## Constant inputs: solutions, convergence, initial rates, unstable modes -/

section ConstantInput

open Set

variable {n p m : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The field of a plant under a constant input, applied: `A x + B u`. -/
@[powerlib_foundation] theorem inputField_apply (M : Linear.Plant n p) (u : Fin p → ℝ) (x : ℝⁿ) :
    M.inputField u x = WithLp.toLp 2 (M.A *ᵥ WithLp.ofLp x + M.B *ᵥ u) := rfl

/-- Under a constant input with an equilibrium, every forward solution from `t = 0` is the
matrix-exponential solution. -/
@[powerlib_foundation] theorem trajectory_eq_solution_Ici (M : Linear.Plant n p)
    {u : Fin p → ℝ} {e : ℝⁿ} (he : IsEquilibrium (M.inputField u) e) {x : ℝ → ℝⁿ}
    (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    x t = Linear.solution M.A e 0 (x 0) t := by
  rw [M.inputField_eq he] at hx
  exact Linear.trajectory_eq_solution (hx.mono Icc_subset_Ici_self) t ⟨ht, le_rfl⟩

/-- The matrix-exponential solution is a solution under the constant input. -/
@[powerlib_foundation] theorem solution_hasDerivAt (M : Linear.Plant n p) {u : Fin p → ℝ}
    {e : ℝⁿ} (he : IsEquilibrium (M.inputField u) e) (t₀ : ℝ) (x₀ : ℝⁿ) (t : ℝ) :
    HasDerivAt (Linear.solution M.A e t₀ x₀) (M.inputField u (Linear.solution M.A e t₀ x₀ t)) t := by
  rw [M.inputField_eq he]
  exact Linear.solution_hasDerivAt M.A e t₀ x₀ t

@[powerlib_foundation] theorem solution_continuous (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ)
    (t₀ : ℝ) (x₀ : ℝⁿ) : Continuous (Linear.solution A e t₀ x₀) :=
  continuous_iff_continuousAt.2 fun t => (Linear.solution_hasDerivAt A e t₀ x₀ t).continuousAt

/-- Componentwise convergence (for instance of the frequency deviation `x t 0`). -/
@[powerlib_foundation] theorem tendsto_apply_of_isHurwitz (M : Linear.Plant n p)
    {u : Fin p → ℝ} {e : ℝⁿ} (he : IsEquilibrium (M.inputField u) e) (hA : IsHurwitz M.A)
    {x : ℝ → ℝⁿ} (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) (i : Fin n) :
    Tendsto (fun t => x t i) atTop (𝓝 (e i)) :=
  ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).tendsto e).comp
    (tendsto_equilibrium M hA he hx)

/-- The right derivative at `t = 0` of a coordinate of a forward solution of any field is that
coordinate of the field at the initial state. -/
@[powerlib_foundation] theorem hasDerivWithinAt_apply_zero {f : ℝⁿ → ℝⁿ} {x : ℝ → ℝⁿ}
    (hx : IsIntegralCurveOn x (fun _ y => f y) (Ici 0)) (i : Fin n) :
    HasDerivWithinAt (fun t => x t i) (f (x 0) i) (Ici 0) 0 := by
  have h := (PiLp.proj 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ)
    (hx 0 self_mem_Ici)
  exact h

/-- In deviation coordinates about an equilibrium of a constant input, the field of a plant is
its zero-input field. -/
@[powerlib_foundation] theorem inputField_shift {n p : ℕ} (P : Linear.Plant n p)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (P.inputField u) e) :
    (fun z => P.inputField u (z + e)) = affineLinearVectorField P.A 0 := by
  funext z
  rw [P.inputField_eq he, Linear.affine_apply, Linear.affine_apply, add_sub_cancel_right,
    sub_zero]

/-- Generic: along a real eigenvector `v` of a positive eigenvalue `r` of the state matrix, the
exponential mode `e + e^{r t} v` through an equilibrium `e` of a constant input is a solution,
and every component where `v` is nonzero diverges, so it converges to no value. -/
@[powerlib_foundation] theorem exists_not_tendsto_of_eigenvector (M : Linear.Plant n m)
    {u : Fin m → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {r : ℝ} (hr : 0 < r) {v : Fin n → ℝ} (hAv : M.A *ᵥ v = r • v) {j : Fin n} (hvj : v j ≠ 0)
    (c : ℝ) : ∃ x : ℝ → EuclideanSpace ℝ (Fin n), (∀ t, HasDerivAt x (M.inputField u (x t)) t) ∧
      ¬ Tendsto (fun t => x t j) atTop (𝓝 c) := by
  let x : ℝ → EuclideanSpace ℝ (Fin n) := fun t => e + Real.exp (r * t) • WithLp.toLp 2 v
  refine ⟨x, fun t => ?_, ?_⟩
  · rw [M.inputField_eq he, Linear.affine_apply]
    have hexp : HasDerivAt (fun s => Real.exp (r * s)) (Real.exp (r * t) * r) t := by
      simpa using ((hasDerivAt_id t).const_mul r).exp
    have h := (hexp.smul_const (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))).const_add e
    convert h using 1
    simp only [x, add_sub_cancel_left, map_smul, Linear.op, Matrix.toEuclideanCLM_toLp, hAv,
      smul_smul, WithLp.toLp_smul]
  · intro hlim
    have hpos : 0 < |v j| := abs_pos.mpr hvj
    have hT0 : Tendsto (fun t => x t j - e j) atTop (𝓝 (c - e j)) := hlim.sub_const (e j)
    have hcomp : (fun t => x t j - e j) = fun t => Real.exp (r * t) * v j := by
      funext t
      simp [x]
    rw [hcomp] at hT0
    have hgrow : Tendsto (fun t => Real.exp (r * t) * |v j|) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr)).atTop_mul_const hpos
    have habs : Tendsto (fun t => |Real.exp (r * t) * v j|) atTop atTop := by
      refine hgrow.congr fun t => ?_
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact not_tendsto_atTop_of_tendsto_nhds hT0.abs habs

end ConstantInput

/-! ## Forward solutions under a common input -/

section CommonInput

open Set

/-- The output `C x + D u` of a plant. -/
def plantOutput {n p : ℕ} (M : Linear.Plant n p) (x : Fin n → ℝ) (u : Fin p → ℝ) : Fin p → ℝ :=
  M.C *ᵥ x + M.D *ᵥ u

/-- Two forward trajectories of the same input-driven plant with Hurwitz state matrix converge to
each other, componentwise, for any common input signal: their difference solves the zero-input
field, which is globally exponentially stable (the linear hub). A forward trajectory `x` of the
plant `ẋ = A x + B u` under the input signal `u` is a solution on `[0, ∞)`, in plain coordinates,
with one-sided derivatives at `0`. -/
@[powerlib_foundation] theorem tendsto_sub_of_isHurwitz {n p : ℕ} {M : Linear.Plant n p}
    (hA : LinearSystems.IsHurwitz M.A) {u : ℝ → Fin p → ℝ} {x y : ℝ → Fin n → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (M.A *ᵥ x t + M.B *ᵥ u t) (Ici 0) t)
    (hy : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt y (M.A *ᵥ y t + M.B *ᵥ u t) (Ici 0) t)
    (i : Fin n) :
    Tendsto (fun t => x t i - y t i) atTop (𝓝 0) := by
  let φ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => WithLp.toLp 2 (x t - y t)
  have hder : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt φ (LinearSystems.affineLinearVectorField M.A 0 (φ t)) (Ici 0) t := by
    intro t ht
    have h := (hx t ht).sub (hy t ht)
    have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.hasFDerivAt.comp_hasDerivWithinAt
      t h
    have heq : LinearSystems.affineLinearVectorField M.A 0 (φ t) =
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
          (M.A *ᵥ x t + M.B *ᵥ u t - (M.A *ᵥ y t + M.B *ᵥ u t)) := by
      rw [Linear.affine_apply, sub_zero]
      ext j
      simp [φ, Linear.op]
    rw [heq]
    exact h2
  obtain ⟨-, -, C, a, -, ha, hb⟩ :=
    Linear.globallyExponentiallyStable_of_isHurwitz (0 : EuclideanSpace ℝ (Fin n)) hA
  have hbound : ∀ t, 0 ≤ t → ‖x t i - y t i‖ ≤ C * Real.exp (-a * t) * ‖φ 0‖ := by
    intro t ht
    have htraj : IsTrajectoryOn φ (LinearSystems.affineLinearVectorField M.A 0) 0 t :=
      fun s hs => (hder s hs.1).mono Icc_subset_Ici_self
    have h := hb 0 t φ htraj t ⟨ht, le_rfl⟩
    simp only [sub_zero] at h
    calc ‖x t i - y t i‖ = ‖φ t i‖ := by simp [φ]
      _ ≤ ‖φ t‖ := PiLp.norm_apply_le (φ t) i
      _ ≤ C * Real.exp (-a * t) * ‖φ 0‖ := h
  have hlim : Tendsto (fun t => C * Real.exp (-a * t) * ‖φ 0‖) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using (he.const_mul C).mul_const ‖φ 0‖
  exact squeeze_zero_norm' (eventually_ge_atTop 0 |>.mono hbound) hlim

end CommonInput

end powerlib.LTI
