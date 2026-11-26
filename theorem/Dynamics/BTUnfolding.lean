import theorem.NormalForm.BogdanovTakens
import theorem.Dynamics.Coordinates

/-! # The Bogdanov–Takens unfolding: regular maps and the homoclinic orbit of the rescaled form

Two generic ingredients of Kuznetsov's analysis of the Bogdanov–Takens unfolding: the regularity
of a map from its Jacobian matrix (the form in which the nondegeneracy condition (BT.3) is
checked), and the homoclinic orbit of the rescaled normal form with its Melnikov function, which
locates the homoclinic curve to leading order.

Scope.
* Regularity: any map `f : ℝⁿ → ℝⁿ` (`State n`) with a derivative given by a matrix; regular at
  `x` means `Df(x)` bijective. Engineering instances (the (BT.3) maps of the grid-forming models)
  are in `theorem/GridTiedConverter/GFM/BTTransversality.lean`.
* Rescaled normal form: the planar family `u̇ = v`, `v̇ = u² − 1 + ε c (u − γ) v`
  (`NormalForm.BogdanovTakens.rescaledField`, constants `c, γ, ε`, continuous time, no remainder
  term), obtained from the truncated normal form `ẏ₁ = y₂`, `ẏ₂ = β₁ + β₂ y₁ + a y₁² + b y₁ y₂` of
  `theorem/NormalForm/BogdanovTakens.lean` by Kuznetsov's singular rescaling
  `y = (ε²(u − γ)/a, ε³ v/a)`, `t = τ/ε`, `β₂ = 2γε²`, `β₁ = (β₂²/4 − ε⁴)/a`, `c = b/a`. Not an
  engineering model: no family is defined and the results are public foundation support.
* Excluded: the persistence of the homoclinic orbit for `ε > 0` (stable and unstable manifolds of
  the saddle with their dependence on the parameters, the splitting function and its expansion
  `d(ε, γ) = ε M(γ)/‖f₀‖ + o(ε)`, the implicit-function step), the remainder terms of the normal
  form, the centre-manifold reduction with parameters and the phase portraits. The homoclinic
  curve below is the image of the simple zero of the Melnikov function under the rescaling, an
  exact algebraic statement, not a proof that the full family has a homoclinic orbit there.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., Springer, 2004), §8.4
(Theorem 8.4 with the nondegeneracy conditions (BT.0)–(BT.3); the rescaling of the Bogdanov
normal form, the Hamiltonian `H = v²/2 + u − u³/3`, its homoclinic orbit and the homoclinic curve
`P : β₁ = −(6/25) β₂² + o(β₂²)`, `β₂ < 0`) and §8.7 (Bogdanov–Takens in `n` dimensions);
Guckenheimer and Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector
Fields* (Springer, 1983), §4.5 (the Melnikov function `∫ f₀ ∧ g` of a perturbed planar Hamiltonian
system) and §7.3 (the Bogdanov–Takens homoclinic curve). The closed forms were derived and checked
with SymPy (exact rational arithmetic; untrusted) and are proved here.

Results.
* Regularity: `Dynamics.det_toEuclideanCLM` (the determinant of the linear map of a matrix),
  `Dynamics.bijective_of_det_ne_zero`, `Dynamics.bijective_fderiv_of_hasFDerivAt` (a derivative
  given by a matrix with `det ≠ 0` is bijective).
* Rescaling: `NormalForm.BogdanovTakens.field_rescale` (the normal form at
  `y = (ε²(u − γ)/a, ε³v/a)` is `diag(ε³/a, ε⁴/a)` times the rescaled field, `a ≠ 0`) and
  `NormalForm.BogdanovTakens.hasDerivAt_rescale` (a trajectory `w(τ)` of the rescaled field gives
  the trajectory `y(t) = (ε²(w₀(εt) − γ)/a, ε³ w₁(εt)/a)` of the normal form). The saddle `(1, 0)`
  is an equilibrium of every member (`rescaledField_saddle`).
* The homoclinic orbit at `ε = 0` (`homoclinic`, `u₀ = 3θ² − 2 = 1 − 3 sech²(τ/√2)`,
  `v₀ = 3√2 θ(1 − θ²) = u₀'`, `θ = tanh(τ/√2)`, `homoclinicPhase`): it solves the truncated rescaled
  field (`hasDerivAt_homoclinic`), tends to the saddle `(1, 0)` as `τ → ±∞`
  (`tendsto_homoclinic_atBot`, `tendsto_homoclinic_atTop`) and passes through the turning point
  `(−2, 0)` (`homoclinic_zero`); together `exists_homoclinic`. It lies on the saddle level of the
  energy `H = v²/2 + u − u³/3` (`energy_homoclinic`).
* The energy rate along the rescaled field is `dH/dτ = ε c (u − γ) v²`
  (`fderiv_energy_rescaledField`), and its integral along the unperturbed orbit is `ε M(γ)`
  (`integral_energy_rate`), `M(γ) = ∫ c (u₀ − γ) v₀² dτ` (`melnikov`).
* Melnikov integrals (improper, over `ℝ`): `∫ v₀² = 24√2/5` (`integral_homoclinicV_sq`),
  `∫ u₀ v₀² = −24√2/7` (`integral_homoclinicU_mul_homoclinicV_sq`); hence
  `M(γ) = −(24√2/5) c (γ + 5/7)` (`melnikov_eq`), with the simple zero `γ = −5/7` for `c ≠ 0`
  (`melnikov_eq_zero_iff`, `hasDerivAt_melnikov`: `M' = −(24√2/5) c`).
* The homoclinic curve to leading order (`homoclinicCurve`): at the zero of `M` the rescaling gives
  `β₁ = −(6/25) β₂²/a` with `β₂ < 0` — Kuznetsov's curve `P` for `a = 1`, independent of `b`.
-/

noncomputable section
namespace powerlib.Dynamics
open Matrix

/-- The determinant of the linear map of a matrix on `ℝⁿ` is the determinant of the matrix. -/
@[tmio T, powerlib_foundation] theorem det_toEuclideanCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A : State n →ₗ[ℝ] State n) =
      A.det := by
  rw [show ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) : State n →ₗ[ℝ] State n) =
      Matrix.toEuclideanLin A from rfl, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- A linear map of `ℝⁿ` with nonzero determinant is bijective. -/
@[tmio T, powerlib_foundation] theorem bijective_of_det_ne_zero {n : ℕ}
    (T : State n →L[ℝ] State n) (h : LinearMap.det (T : State n →ₗ[ℝ] State n) ≠ 0) :
    Function.Bijective T :=
  (Module.End.isUnit_iff _).mp ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))

/-- **Regularity from the Jacobian matrix.** A map of `ℝⁿ` whose derivative at `x` is the matrix
`A` with `det A ≠ 0` is regular at `x`: its derivative there is bijective. -/
@[tmio T, powerlib_foundation] theorem bijective_fderiv_of_hasFDerivAt {n : ℕ}
    {f : State n → State n} {x : State n} {A : Matrix (Fin n) (Fin n) ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) x) (hA : A.det ≠ 0) :
    Function.Bijective (fderiv ℝ f x) := by
  rw [hf.fderiv]
  exact bijective_of_det_ne_zero _ (by rwa [det_toEuclideanCLM])

end powerlib.Dynamics

namespace powerlib.NormalForm.BogdanovTakens
open Filter Topology Set MeasureTheory
open powerlib.Dynamics (State)
open powerlib.PhasePlane (mk mk_apply_zero mk_apply_one)

/-- A planar curve from two scalar curves. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_mk {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => mk (f s) (g s)) (mk f' g') t := by
  have h : HasDerivAt (fun s => (![f s, g s] : Fin 2 → ℝ)) ![f', g'] t :=
    hasDerivAt_pi.2 fun i => by fin_cases i <;> simpa
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h

/-- **Kuznetsov's rescaled normal form** `u̇ = v`, `v̇ = u² − 1 + ε c (u − γ) v`. -/
def rescaledField (c γ ε : ℝ) (w : State 2) : State 2 :=
  mk (w 1) (w 0 ^ 2 - 1 + ε * c * (w 0 - γ) * w 1)

/-- The saddle `(1, 0)` is an equilibrium of every member of the rescaled family. -/
@[tmio T, powerlib_foundation] theorem rescaledField_saddle (c γ ε : ℝ) :
    rescaledField c γ ε (mk 1 0) = 0 := by
  ext i; fin_cases i <;> simp [rescaledField]

/-- **Kuznetsov's rescaling.** For `a ≠ 0`, with `β₂ = 2γε²` and `β₁ = (β₂²/4 − ε⁴)/a`, the
truncated normal form at `y = (ε²(u − γ)/a, ε³v/a)` is the rescaled field `rescaledField (b/a) γ ε`
scaled by `diag(ε³/a, ε⁴/a)` (time `τ = εt`). -/
@[tmio T, powerlib_foundation] theorem field_rescale (a b γ ε : ℝ) (ha : a ≠ 0) (w : State 2) :
    field ⟨((2 * γ * ε ^ 2) ^ 2 / 4 - ε ^ 4) / a, 2 * γ * ε ^ 2, a, b⟩
        (mk (ε ^ 2 * (w 0 - γ) / a) (ε ^ 3 * w 1 / a)) =
      mk (ε ^ 3 / a * rescaledField (b / a) γ ε w 0)
        (ε ^ 4 / a * rescaledField (b / a) γ ε w 1) := by
  ext i; fin_cases i
  · simp [field, rescaledField]; ring
  · simp [field, rescaledField]; field_simp; ring

/-- Trajectories of the rescaled field are trajectories of the normal form. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_rescale {a b γ ε : ℝ} (ha : a ≠ 0)
    {w : ℝ → State 2} (hw : ∀ τ, HasDerivAt w (rescaledField (b / a) γ ε (w τ)) τ) (t : ℝ) :
    HasDerivAt (fun s => mk (ε ^ 2 * (w (ε * s) 0 - γ) / a) (ε ^ 3 * w (ε * s) 1 / a))
      (field ⟨((2 * γ * ε ^ 2) ^ 2 / 4 - ε ^ 4) / a, 2 * γ * ε ^ 2, a, b⟩
        (mk (ε ^ 2 * (w (ε * t) 0 - γ) / a) (ε ^ 3 * w (ε * t) 1 / a))) t := by
  rw [field_rescale a b γ ε ha]
  have hs : HasDerivAt (fun s => ε * s) ε t := by simpa using (hasDerivAt_id t).const_mul ε
  have hc : ∀ i : Fin 2, HasDerivAt (fun s => w (ε * s) i)
      (ε * rescaledField (b / a) γ ε (w (ε * t)) i) t := by
    intro i
    have h1 := (hw (ε * t)).scomp t hs
    have h2 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i).hasFDerivAt.comp_hasDerivAt t h1
    simp only [PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul] at h2
    exact h2
  refine hasDerivAt_mk ?_ ?_
  · convert (((hc 0).sub_const γ).const_mul (ε ^ 2)).div_const a using 1; ring
  · convert ((hc 1).const_mul (ε ^ 3)).div_const a using 1; ring

/-! ## The homoclinic orbit of the truncated rescaled normal form -/

/-- The phase `θ(τ) = tanh(τ/√2) = (e^{√2 τ} − 1)/(e^{√2 τ} + 1)` of the homoclinic orbit. -/
def homoclinicPhase (τ : ℝ) : ℝ := (Real.exp (√2 * τ) - 1) / (Real.exp (√2 * τ) + 1)

/-- `u₀ = 3θ² − 2 = 1 − 3 sech²(τ/√2)`. -/
def homoclinicU (τ : ℝ) : ℝ := 3 * homoclinicPhase τ ^ 2 - 2

/-- `v₀ = 3√2 θ (1 − θ²) = u₀'`. -/
def homoclinicV (τ : ℝ) : ℝ := 3 * √2 * homoclinicPhase τ * (1 - homoclinicPhase τ ^ 2)

/-- The homoclinic orbit `τ ↦ (u₀(τ), v₀(τ))`. -/
def homoclinic (τ : ℝ) : State 2 := mk (homoclinicU τ) (homoclinicV τ)

@[tmio T, powerlib_foundation] private theorem sqrt_two_sq : √2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

@[tmio T, powerlib_foundation] private theorem sqrt_two_ne : √2 ≠ 0 := by positivity

/-- `θ' = (1 − θ²)/√2`, the derivative of `tanh(τ/√2)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_homoclinicPhase (τ : ℝ) :
    HasDerivAt homoclinicPhase ((1 - homoclinicPhase τ ^ 2) / √2) τ := by
  have he : HasDerivAt (fun s => Real.exp (√2 * s)) (Real.exp (√2 * τ) * √2) τ := by
    simpa using ((hasDerivAt_id τ).const_mul √2).exp
  have hpos : Real.exp (√2 * τ) + 1 ≠ 0 := by positivity
  have h := (he.sub_const 1).div (he.add_const 1) hpos
  refine (h : HasDerivAt homoclinicPhase _ τ).congr_deriv ?_
  unfold homoclinicPhase
  have h2 := sqrt_two_sq
  have hs := sqrt_two_ne
  field_simp
  rw [h2]
  ring

/-- The phase is odd. -/
@[tmio T, powerlib_foundation] theorem homoclinicPhase_neg (τ : ℝ) :
    homoclinicPhase (-τ) = -homoclinicPhase τ := by
  simp only [homoclinicPhase, mul_neg, Real.exp_neg]
  have hpos : 0 < Real.exp (√2 * τ) := Real.exp_pos _
  field_simp
  ring

/-- `θ → 1` as `τ → +∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_homoclinicPhase_atTop :
    Tendsto homoclinicPhase atTop (𝓝 1) := by
  have h1 : Tendsto (fun s => Real.exp (√2 * s)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have h2 : Tendsto (fun s => 2 / (Real.exp (√2 * s) + 1)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right _ 1 h1).const_div_atTop 2
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  rw [sub_zero] at h3
  refine h3.congr fun s => ?_
  have hpos : Real.exp (√2 * s) + 1 ≠ 0 := by positivity
  unfold homoclinicPhase
  field_simp
  ring

/-- `θ → −1` as `τ → −∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_homoclinicPhase_atBot :
    Tendsto homoclinicPhase atBot (𝓝 (-1)) := by
  have h := tendsto_homoclinicPhase_atTop.comp tendsto_neg_atBot_atTop
  have h' := h.neg
  refine h'.congr fun s => ?_
  show -homoclinicPhase (-s) = homoclinicPhase s
  rw [homoclinicPhase_neg, neg_neg]

/-- The homoclinic orbit solves the truncated rescaled normal form (`ε = 0`). -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_homoclinic (c γ τ : ℝ) :
    HasDerivAt homoclinic (rescaledField c γ 0 (homoclinic τ)) τ := by
  have hθ := hasDerivAt_homoclinicPhase τ
  have h2 := sqrt_two_sq
  have hs := sqrt_two_ne
  have hU : HasDerivAt homoclinicU (homoclinicV τ) τ := by
    have := ((hθ.pow 2).const_mul 3).sub_const 2
    refine (this : HasDerivAt homoclinicU _ τ).congr_deriv ?_
    simp only [homoclinicV]
    field_simp
    rw [h2]
    push_cast
    ring
  have hV : HasDerivAt homoclinicV (homoclinicU τ ^ 2 - 1) τ := by
    have := (hθ.const_mul (3 * √2)).mul ((hasDerivAt_const τ (1 : ℝ)).sub (hθ.pow 2))
    refine (this : HasDerivAt homoclinicV _ τ).congr_deriv ?_
    simp only [homoclinicU, Pi.sub_apply, Pi.pow_apply]
    field_simp
    ring
  have := hasDerivAt_mk hU hV
  refine (this : HasDerivAt homoclinic _ τ).congr_deriv ?_
  simp [rescaledField, homoclinic]

@[tmio T, powerlib_foundation] private theorem tendsto_mk {l : Filter ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun s => mk (f s) (g s)) l (𝓝 (mk a b)) := by
  have h : Tendsto (fun s => (![f s, g s] : Fin 2 → ℝ)) l (𝓝 ![a, b]) :=
    tendsto_pi_nhds.2 fun i => by fin_cases i <;> simpa
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.tendsto _).comp h

@[tmio T, powerlib_foundation] private theorem tendsto_homoclinic_of {l : Filter ℝ} {θ₀ : ℝ}
    (h : Tendsto homoclinicPhase l (𝓝 θ₀)) (hθ : θ₀ ^ 2 = 1) :
    Tendsto homoclinic l (𝓝 (mk 1 0)) := by
  have hU : Tendsto homoclinicU l (𝓝 1) := by
    have := ((h.pow 2).const_mul 3).sub_const 2
    rw [hθ] at this; norm_num at this
    exact this
  have hV : Tendsto homoclinicV l (𝓝 0) := by
    have := (h.const_mul (3 * √2)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub (h.pow 2))
    rw [hθ, sub_self, mul_zero] at this
    exact this
  exact tendsto_mk hU hV

/-- The orbit leaves the saddle `(1, 0)` as `τ → −∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_homoclinic_atBot :
    Tendsto homoclinic atBot (𝓝 (mk 1 0)) :=
  tendsto_homoclinic_of tendsto_homoclinicPhase_atBot (by norm_num)

/-- The orbit returns to the saddle `(1, 0)` as `τ → +∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_homoclinic_atTop :
    Tendsto homoclinic atTop (𝓝 (mk 1 0)) :=
  tendsto_homoclinic_of tendsto_homoclinicPhase_atTop (by norm_num)

/-- The orbit is not the equilibrium: `homoclinic 0 = (−2, 0)`, the turning point. -/
@[tmio T, powerlib_foundation] theorem homoclinic_zero : homoclinic 0 = mk (-2) 0 := by
  simp [homoclinic, homoclinicU, homoclinicV, homoclinicPhase]

/-- **The homoclinic orbit of the truncated rescaled normal form.** At `ε = 0` the rescaled
field has the orbit `(u₀, v₀) = (1 − 3 sech²(τ/√2), u₀')`, which leaves the saddle `(1, 0)` and
returns to it. -/
@[tmio T, powerlib_foundation] theorem exists_homoclinic (c γ : ℝ) :
    ∃ x : ℝ → State 2, (∀ τ, HasDerivAt x (rescaledField c γ 0 (x τ)) τ) ∧
      Tendsto x atBot (𝓝 (mk 1 0)) ∧ Tendsto x atTop (𝓝 (mk 1 0)) ∧ x 0 ≠ mk 1 0 := by
  refine ⟨homoclinic, hasDerivAt_homoclinic c γ, tendsto_homoclinic_atBot,
    tendsto_homoclinic_atTop, ?_⟩
  rw [homoclinic_zero]
  intro h
  have := congrArg (fun w : State 2 => w 0) h
  norm_num at this

/-! ## The energy and the Melnikov function -/

/-- The energy `H(u, v) = v²/2 + u − u³/3`, conserved by the truncated rescaled field. -/
def energy (w : State 2) : ℝ := w 1 ^ 2 / 2 + w 0 - w 0 ^ 3 / 3

/-- The homoclinic orbit lies on the level `H = 2/3` of the saddle. -/
@[tmio T, powerlib_foundation] theorem energy_homoclinic (τ : ℝ) :
    energy (homoclinic τ) = energy (mk 1 0) := by
  have h2 := sqrt_two_sq
  simp only [energy, homoclinic, mk_apply_zero, mk_apply_one, homoclinicU, homoclinicV]
  linear_combination (9 / 2 * homoclinicPhase τ ^ 2 * (1 - homoclinicPhase τ ^ 2) ^ 2) * h2

/-- **The energy rate.** Along the rescaled field the energy changes at the rate
`dH/dτ = ε c (u − γ) v²`: the Melnikov integrand. -/
@[tmio T, powerlib_foundation] theorem fderiv_energy_rescaledField (c γ ε : ℝ) (w : State 2) :
    fderiv ℝ energy w (rescaledField c γ ε w) = ε * (c * (w 0 - γ) * w 1 ^ 2) := by
  have h0 := Dynamics.hasFDerivAt_coord (0 : Fin 2) w
  have h1 := Dynamics.hasFDerivAt_coord (1 : Fin 2) w
  have h : HasFDerivAt (fun y : State 2 => 1 / 2 * y 1 ^ 2 + y 0 - 1 / 3 * y 0 ^ 3) _ w :=
    (((h1.pow 2).const_mul (1 / 2)).add h0).sub ((h0.pow 3).const_mul (1 / 3))
  rw [show energy = fun y : State 2 => 1 / 2 * y 1 ^ 2 + y 0 - 1 / 3 * y 0 ^ 3 by
    funext y; simp only [energy]; ring, h.fderiv]
  simp [rescaledField]
  ring

@[tmio T, powerlib_foundation] private theorem continuous_homoclinicPhase :
    Continuous homoclinicPhase :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_homoclinicPhase τ).continuousAt

@[tmio T, powerlib_foundation] private theorem sq_homoclinicPhase_le (τ : ℝ) :
    homoclinicPhase τ ^ 2 ≤ 1 := by
  have he : 0 < Real.exp (√2 * τ) := Real.exp_pos _
  have h1 : homoclinicPhase τ ≤ 1 := by
    rw [homoclinicPhase, div_le_one (by positivity)]; linarith
  have h2 : -1 ≤ homoclinicPhase τ := by
    rw [homoclinicPhase, le_div_iff₀ (by positivity)]; linarith
  nlinarith

/-- An even, nonnegative derivative of a function with a limit at `+∞` is integrable on `ℝ`. -/
@[tmio T, powerlib_foundation] private theorem integrable_of_even {f F : ℝ → ℝ} {l : ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : ∀ x, 0 ≤ f x) (he : ∀ x, f (-x) = f x)
    (hl : Tendsto F atTop (𝓝 l)) : Integrable f := by
  have h1 : IntegrableOn f (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hF x) (fun x _ => hf x) hl
  have h2 : IntegrableOn f (Ici (-0)) := by
    rw [neg_zero]; exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h1
  have h3 : IntegrableOn (fun x => f (-x)) (Iic 0) := h2.comp_neg_Iic
  simp only [he] at h3
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact h3.union h1

/-- The antiderivative `18√2 (θ³/3 − θ⁵/5)` of `v₀²`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_antideriv_sq (τ : ℝ) :
    HasDerivAt (fun s => 18 * √2 * (homoclinicPhase s ^ 3 / 3 - homoclinicPhase s ^ 5 / 5))
      (homoclinicV τ ^ 2) τ := by
  have hθ := hasDerivAt_homoclinicPhase τ
  have h := (((hθ.pow 3).div_const 3).sub ((hθ.pow 5).div_const 5)).const_mul (18 * √2)
  refine h.congr_deriv ?_
  have h2 := sqrt_two_sq
  have hs := sqrt_two_ne
  simp only [homoclinicV]
  field_simp
  push_cast
  linear_combination (-(135 * homoclinicPhase τ ^ 2 * (1 - homoclinicPhase τ ^ 2) ^ 2)) * h2

/-- The antiderivative `18√2 (−3θ⁷/7 + θ⁵ − 2θ³/3)` of `u₀ v₀²`. -/
@[tmio T, powerlib_foundation] private theorem hasDerivAt_antideriv_mul_sq (τ : ℝ) :
    HasDerivAt (fun s => 18 * √2 * (-(3 * homoclinicPhase s ^ 7 / 7) + homoclinicPhase s ^ 5 -
      2 * homoclinicPhase s ^ 3 / 3)) (homoclinicU τ * homoclinicV τ ^ 2) τ := by
  have hθ := hasDerivAt_homoclinicPhase τ
  have h := (((((hθ.pow 7).const_mul 3).div_const 7).neg.add (hθ.pow 5)).sub
    (((hθ.pow 3).const_mul 2).div_const 3)).const_mul (18 * √2)
  refine h.congr_deriv ?_
  have h2 := sqrt_two_sq
  have hs := sqrt_two_ne
  simp only [homoclinicU, homoclinicV]
  field_simp
  push_cast
  rw [h2]
  ring

@[tmio T, powerlib_foundation] private theorem homoclinicV_neg (τ : ℝ) :
    homoclinicV (-τ) = -homoclinicV τ := by
  simp only [homoclinicV, homoclinicPhase_neg]; ring

@[tmio T, powerlib_foundation] private theorem integrable_homoclinicV_sq :
    Integrable fun τ => homoclinicV τ ^ 2 := by
  refine integrable_of_even (l := 18 * √2 * ((1 : ℝ) ^ 3 / 3 - 1 ^ 5 / 5))
    hasDerivAt_antideriv_sq (fun _ => sq_nonneg _)
    (fun x => by rw [homoclinicV_neg, neg_sq]) ?_
  exact (((tendsto_homoclinicPhase_atTop.pow 3).div_const 3).sub
    ((tendsto_homoclinicPhase_atTop.pow 5).div_const 5)).const_mul _

@[tmio T, powerlib_foundation] private theorem integrable_homoclinicU_mul_sq :
    Integrable fun τ => homoclinicU τ * homoclinicV τ ^ 2 := by
  have hc := continuous_homoclinicPhase
  refine (integrable_homoclinicV_sq.const_mul 2).mono' ?_ (Filter.Eventually.of_forall fun τ => ?_)
  · exact (by unfold homoclinicU homoclinicV; fun_prop :
      Continuous fun τ => homoclinicU τ * homoclinicV τ ^ 2).aestronglyMeasurable
  · have h1 := sq_homoclinicPhase_le τ
    have h0 := sq_nonneg (homoclinicPhase τ)
    have hU : |homoclinicU τ| ≤ 2 := by
      rw [abs_le]; constructor <;> (simp only [homoclinicU]; nlinarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (homoclinicV τ))]
    exact mul_le_mul_of_nonneg_right hU (sq_nonneg _)

/-- `∫ v₀² dτ = 24√2/5`. -/
@[tmio T, powerlib_foundation] theorem integral_homoclinicV_sq :
    ∫ τ, homoclinicV τ ^ 2 = 24 * √2 / 5 := by
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_antideriv_sq integrable_homoclinicV_sq
    ((((tendsto_homoclinicPhase_atBot.pow 3).div_const 3).sub
      ((tendsto_homoclinicPhase_atBot.pow 5).div_const 5)).const_mul _)
    ((((tendsto_homoclinicPhase_atTop.pow 3).div_const 3).sub
      ((tendsto_homoclinicPhase_atTop.pow 5).div_const 5)).const_mul _)]
  ring

/-- `∫ u₀ v₀² dτ = −24√2/7`. -/
@[tmio T, powerlib_foundation] theorem integral_homoclinicU_mul_homoclinicV_sq :
    ∫ τ, homoclinicU τ * homoclinicV τ ^ 2 = -(24 * √2 / 7) := by
  have hl : ∀ {l : Filter ℝ} {θ₀ : ℝ}, Tendsto homoclinicPhase l (𝓝 θ₀) →
      Tendsto (fun s => 18 * √2 * (-(3 * homoclinicPhase s ^ 7 / 7) + homoclinicPhase s ^ 5 -
        2 * homoclinicPhase s ^ 3 / 3)) l
        (𝓝 (18 * √2 * (-(3 * θ₀ ^ 7 / 7) + θ₀ ^ 5 - 2 * θ₀ ^ 3 / 3))) := fun h =>
    (((((h.pow 7).const_mul 3).div_const 7).neg.add (h.pow 5)).sub
      (((h.pow 3).const_mul 2).div_const 3)).const_mul _
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_antideriv_mul_sq integrable_homoclinicU_mul_sq
    (hl tendsto_homoclinicPhase_atBot) (hl tendsto_homoclinicPhase_atTop)]
  ring

/-- **The Melnikov function** of the rescaled family along the homoclinic orbit,
`M(γ) = ∫ c (u₀ − γ) v₀² dτ` (`f₀ ∧ g` integrated, Guckenheimer–Holmes §4.5). -/
def melnikov (c γ : ℝ) : ℝ := ∫ τ, c * (homoclinicU τ - γ) * homoclinicV τ ^ 2

/-- The Melnikov function is the first-order energy change along the unperturbed orbit:
`∫ dH/dτ (rescaled field at ε) dτ = ε M(γ)`. -/
@[tmio T, powerlib_foundation] theorem integral_energy_rate (c γ ε : ℝ) :
    ∫ τ, fderiv ℝ energy (homoclinic τ) (rescaledField c γ ε (homoclinic τ)) =
      ε * melnikov c γ := by
  simp only [fderiv_energy_rescaledField, melnikov, homoclinic, mk_apply_zero, mk_apply_one]
  rw [← integral_const_mul]

/-- **The Melnikov function in closed form**: `M(γ) = −(24√2/5) c (γ + 5/7)`. -/
@[tmio T, powerlib_foundation] theorem melnikov_eq (c γ : ℝ) :
    melnikov c γ = -(24 * √2 / 5) * c * (γ + 5 / 7) := by
  have e : (fun τ => c * (homoclinicU τ - γ) * homoclinicV τ ^ 2) =
      fun τ => c * (homoclinicU τ * homoclinicV τ ^ 2) - c * γ * homoclinicV τ ^ 2 := by
    funext τ; ring
  rw [melnikov, e, integral_sub (integrable_homoclinicU_mul_sq.const_mul c)
    (integrable_homoclinicV_sq.const_mul (c * γ)), integral_const_mul, integral_const_mul,
    integral_homoclinicV_sq, integral_homoclinicU_mul_homoclinicV_sq]
  ring

/-- **The simple zero of the Melnikov function**: for `c ≠ 0`, `M(γ) = 0` iff `γ = −5/7`. -/
@[tmio T, powerlib_foundation] theorem melnikov_eq_zero_iff {c : ℝ} (hc : c ≠ 0) (γ : ℝ) :
    melnikov c γ = 0 ↔ γ = -5 / 7 := by
  have hs : (24 * √2 / 5 : ℝ) ≠ 0 := by positivity
  rw [melnikov_eq, mul_eq_zero, mul_eq_zero, neg_eq_zero, or_iff_right hs, or_iff_right hc]
  constructor <;> intro h <;> linarith

/-- The zero is simple: `M'(γ) = −(24√2/5) c ≠ 0` for `c ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_melnikov (c γ : ℝ) :
    HasDerivAt (melnikov c) (-(24 * √2 / 5) * c) γ := by
  have h := ((hasDerivAt_id γ).add_const (5 / 7 : ℝ)).const_mul (-(24 * √2 / 5) * c)
  rw [show melnikov c = fun γ => -(24 * √2 / 5) * c * (γ + 5 / 7) from funext (melnikov_eq c)]
  simpa using h

/-- **The homoclinic curve to leading order.** The zero `γ = −5/7` of the Melnikov function read
through Kuznetsov's rescaling (`β₂ = 2γε²`, `β₁ = (β₂²/4 − ε⁴)/a`, `field_rescale`): the parabola
`β₁ = −(6/25) β₂²/a`, `β₂ < 0` (Kuznetsov's `β₁ = −(6/25)β₂²` for `a = 1`). -/
@[tmio T, powerlib_foundation] theorem homoclinicCurve {a c γ ε : ℝ} (hc : c ≠ 0)
    (hM : melnikov c γ = 0) (hε : ε ≠ 0) :
    ((2 * γ * ε ^ 2) ^ 2 / 4 - ε ^ 4) / a = -(6 / 25) * (2 * γ * ε ^ 2) ^ 2 / a ∧
      2 * γ * ε ^ 2 < 0 := by
  rw [(melnikov_eq_zero_iff hc γ).mp hM]
  have : 0 < ε ^ 2 := by positivity
  constructor
  · ring
  · linarith

end powerlib.NormalForm.BogdanovTakens
