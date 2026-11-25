import theorem.GridTiedConverter.GFM.DCLink.VSMDCBoundary
import theorem.Dynamics.HopfLocal

/-! # The VSM–DC model with its DC-voltage loop: Hopf points of the Routh boundary

Model boundary.
The VSM–DC family `VSMDC.family` of `theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean` (state
`(δ, ω, V, ζ)`, quasi-static line `P_e(δ) = c₀ + A sin(δ − α)`, affine DC source, DC node
`C V̇ = (P_src(V) − P_e(δ))/V`, DC-voltage PI loop on the power reference; continuous time,
autonomous; export-positive power), on the slice `hopfModel M D C A I_s K_p K_i` of its
parameters and selected points: `c₀ = α = P_ff = 0`, `P_s = −I_s`, `V* = 1`, `δ* = ζ* = 0` (a
balanced point, `Model.hopfModel_balanced`). The field is read translated to the selected point; it
is `C¹` (indeed analytic) on `V ≠ 0`, so on a neighbourhood of the point, not globally. Level: local
asymptotic stability and instability at two exhibited Hopf points of the quartic Routh boundary,
by the centre-manifold reduction for fields smooth near the point
(`Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly_local`,
`theorem/Dynamics/HopfLocal.lean`). Excluded as in `VSMDC.lean`.

Source: GFM counterpart study, note T7 part (a) (`t7-dcside`); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed.), §3.5 (projection formula). The witnesses and their Lyapunov
coefficients were found and computed with exact computer algebra (SymPy, rational arithmetic,
untrusted); Lean checks every number.

Results.
* The translated field on the slice (`Model.hopfModel_field`) agrees near the point with the
  globally smooth surrogate `hopfSurrogate` (two ridges and a product ridge with the smooth
  reciprocal `NormalForm.LyapunovCoefficient.recipSmooth`, `Model.hopfModel_field_eventuallyEq`),
  so its forms at the point are those of the surrogate (`NormalForm.LyapunovCoefficient.biRidge`
  laws): `hopfModel_bilinC` (`B(u, w) = (0, 0, (A/C)(u₀w₂ + u₂w₀) − (2I_s/C) u₂w₂, 0)`),
  `hopfModel_trilinC` (`C(u, w, z) = (0, (A/M) u₀w₀z₀, (A/C) u₀w₀z₀ − (2A/C)(u₀w₂z₂ + u₂w₀z₂ +
  u₂w₂z₀) + (6I_s/C) u₂w₂z₂, 0)`), `hopfModel_fderiv` (the derivative is `hopfJac`, the
  Jacobian of `VSMDC.lean` on the slice), `hopfModel_jacobianC`.
* `hopfSup := hopfModel 1 1 1 1 (−1) 1 1`: characteristic polynomial `(s² + 1)(s + 1)²`
  (`hopfSup_charpoly`; `a₃ = 2`, `a₂ = 2`, `a₁ = 2`, `a₀ = 1`, on the Hopf boundary
  `a₃ a₂ a₁ = a₁² + a₃² a₀ = 8`; the other roots `hopfSup_r_roots`), critical pair
  `q = (1 − i, 1 + i, i, 1)` (`hopfSup_isCriticalPair`), `ℓ₁ = −1/25` (`hopfSup_firstLyapunov`):
  supercritical.
* `hopfSub := hopfModel 2 2 2 2 (−1/2) 2 (1/2)`: `(s² + 1)(s² + 5s/4 + 1/4)` (`hopfSub_charpoly`,
  `hopfSub_r_roots`),
  `q = (1 − i/4, 1/4 + i, i, 1)` (`hopfSub_isCriticalPair`), `ℓ₁ = 8/85`
  (`hopfSub_firstLyapunov`): subcritical.
* Both are balanced with `V* = 1` and meet neither requirement (`hopfSup_not_meets`,
  `hopfSub_not_meets`: Routh fails by `a₁² + a₃² a₀ = a₃ a₂ a₁`, no strict violation).

Family and connection conclusions.
* `hopfSup_mem_den_locallyAsymptoticallyStable`: the supercritical witness is locally
  asymptotically stable; `hopfSub_mem_den_unstable`: the subcritical one is unstable.
* REFUTED exactness of the local asymptotic translation within `V* ≠ 0`:
  `VSMDC.realize_ne_den_inter_locallyAsymptoticallyStable` (witness `hopfSup`: locally
  asymptotically stable, not Routh). Inexpressibility:
  `VSMDC.realize_ne_den_locallyAsymptoticallyStable` (`hopfSup` and `hopfSub` meet the same
  requirements, none, and differ). With `theorem/GridTiedConverter/GFM/DCLink/VSMDCBoundary.lean`
  the Lyapunov, local asymptotic and instability sentences of the VSM–DC family (`V* ≠ 0`) are
  decided off the Routh boundary and inexpressible on it; local exponential stability is exact.
* The bifurcating cycles at the two witnesses (unfolded in the damping, transversality
  `τ = −1/2` at `hopfSup`, `τ = −1/4` at `hopfSub`; supercritical cycles for damping just below
  the boundary, subcritical ones just above, all in `V > 0`) are private evidence of
  `theorem/GridTiedConverter/GFM/DCLink/VSMDCHopfCycle.lean`; their uniqueness and orbital
  stability are not proved.
-/

noncomputable section
namespace powerlib.GFM.DCLink
namespace VSMDC
open Complex Polynomial Filter Matrix
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

/-! ## The Hopf slice and its forms -/

/-- The slice of the Hopf witnesses: `c₀ = α = P_ff = 0`, `P_s = −I_s`, `V* = 1`, `δ* = ζ* = 0`. -/
def hopfModel (M D C A Is Kp Ki : ℝ) : Model :=
  ⟨{ toPlant := ⟨M, D, C, 0, 0, A, 0, -Is, Is⟩, Vref := 1, Kp := Kp, Ki := Ki }, 0, 0⟩

variable (M D C A Is Kp Ki : ℝ)

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.field 0 :=
  (Spectral.localFamily_isAutonomous _ _ _).mem_den_flow

@[tmio M, powerlib_domain] theorem Model.hopfModel_point :
    (hopfModel M D C A Is Kp Ki).point = WithLp.toLp 2 ![0, 0, 1, 0] := by
  ext i
  fin_cases i <;> simp [Model.point, hopfModel]

@[tmio M, powerlib_domain] theorem Model.hopfModel_balanced :
    (hopfModel M D C A Is Kp Ki).Balanced := by
  refine ⟨?_, ?_⟩ <;> simp [hopfModel, Plant.Pe, Plant.Psrc]

/-- The translated field on the slice. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_field (z : State 4) :
    (hopfModel M D C A Is Kp Ki).field z = WithLp.toLp 2 ![z 1,
      (Kp * z 2 + Ki * z 3 - A * Real.sin (z 0) - D * z 1) / M,
      (Is + (-Is - A * Real.sin (z 0)) / (z 2 + 1)) / C, z 2] := by
  ext i
  fin_cases i
  · simp [Model.field, Model.point, hopfModel, Params.field]
  · simp [Model.field, Model.point, hopfModel, Params.field, Plant.swingRate, Params.Pref,
      Plant.Pe]
  · simp [Model.field, Model.point, hopfModel, Params.field, Plant.Pe, Plant.nodeRate,
      GFL.DCLink.nodeRate]
  · simp [Model.field, Model.point, hopfModel, Params.field]

/-- The affine part and the angle ridge `−(A/M) sin z₀ e₁` of the surrogate. -/
def hopfRidge1 : State 4 → State 4 :=
  ridge (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      !![0, 1, 0, 0; 0, -D / M, Kp / M, Ki / M; 0, 0, 0, 0; 0, 0, 1, 0])
    (WithLp.toLp 2 ![0, 0, Is / C, 0]) (coord 0) (fun t => -(A / M) * Real.sin t)
    (EuclideanSpace.single 1 1)

/-- The source ridge `(−I_s/C) recipSmooth(z₂) e₂` of the surrogate. -/
def hopfRidge2 : State 4 → State 4 :=
  ridge 0 0 (coord 2) (fun t => -Is / C * recipSmooth t) (EuclideanSpace.single 2 1)

/-- The power product `(−A/C) sin z₀ recipSmooth(z₂) e₂` of the surrogate. -/
def hopfProd : State 4 → State 4 :=
  biRidge (coord 0) (coord 2) Real.sin recipSmooth ((-A / C) • EuclideanSpace.single 2 1)

/-- The globally smooth surrogate of the translated field near the point. -/
def hopfSurrogate : State 4 → State 4 :=
  hopfRidge1 M D C A Is Kp Ki + hopfRidge2 C Is + hopfProd C A

/-- Near the point the translated field is the surrogate (`recipSmooth z₂ = 1/(1 + z₂)` for
`z₂ > −1/4`). -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_field_eventuallyEq :
    (hopfModel M D C A Is Kp Ki).field =ᶠ[nhds 0] hopfSurrogate M D C A Is Kp Ki := by
  filter_upwards [Metric.ball_mem_nhds (0 : State 4) (show (0 : ℝ) < 1 / 4 by norm_num)]
    with z hz
  have h2 : -1 / 4 < z 2 := by
    have := (Dynamics.abs_coord_sub_le 0 z 2).trans_lt (by simpa [dist_eq_norm] using hz)
    simp at this
    linarith [neg_abs_le (z 2)]
  have hz2 : z 2 + 1 ≠ 0 := by linarith
  have hz2' : 1 + z 2 ≠ 0 := by linarith
  rw [Model.hopfModel_field]
  ext i
  fin_cases i
  · simp [hopfSurrogate, hopfRidge1, hopfRidge2, hopfProd, ridge, biRidge,
      Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
  · simp [hopfSurrogate, hopfRidge1, hopfRidge2, hopfProd, ridge, biRidge,
      Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
    ring
  · simp [hopfSurrogate, hopfRidge1, hopfRidge2, hopfProd, ridge, biRidge,
      Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four, recipSmooth_eq h2]
    rw [show z 2 + 1 = 1 + z 2 by ring]
    field_simp
    ring
  · simp [hopfSurrogate, hopfRidge1, hopfRidge2, hopfProd, ridge, biRidge,
      Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]

@[tmio M, powerlib_domain] private theorem sin_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.sin t) (c * Real.cos t) t) ∧
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) :=
  ⟨fun t => (Real.hasDerivAt_sin t).const_mul c,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg⟩

@[tmio M, powerlib_domain] private theorem contDiff_surrogate_pieces :
    ContDiff ℝ 3 (hopfRidge1 M D C A Is Kp Ki) ∧ ContDiff ℝ 3 (hopfRidge2 C Is) ∧
      ContDiff ℝ 3 (hopfProd C A) :=
  ⟨contDiff_ridge _ _ _ _ (by fun_prop),
    contDiff_ridge _ _ _ _ (contDiff_const.mul (contDiff_recipSmooth.of_le (by simp))),
    contDiff_biRidge _ _ _ Real.contDiff_sin (contDiff_recipSmooth.of_le (by simp))⟩

/-- **The second derivative** of the translated field at the point:
`B(u, w) = (0, 0, (A/C)(u₀w₂ + u₂w₀) − (2I_s/C) u₂w₂, 0)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_bilinC (u w : Fin 4 → ℂ) :
    bilinC (hopfModel M D C A Is Kp Ki).field 0 u w =
      ![0, 0, ((A / C : ℝ) : ℂ) * (u 0 * w 2 + u 2 * w 0) +
        ((-2 * Is / C : ℝ) : ℂ) * (u 2 * w 2), 0] := by
  obtain ⟨c1, c2, c3⟩ := contDiff_surrogate_pieces M D C A Is Kp Ki
  obtain ⟨r0, r1, r2, r3⟩ := recipSmooth_derivs
  obtain ⟨k1, k2, k3⟩ := hasDerivAt_recipSmooth_chain
  have k2' : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  have c12 : ContDiff ℝ 3 (hopfRidge1 M D C A Is Kp Ki + hopfRidge2 C Is) := c1.add c2
  rw [bilinC_congr (Model.hopfModel_field_eventuallyEq M D C A Is Kp Ki), hopfSurrogate,
    bilinC_add (c12.of_le k2') (c3.of_le k2'), bilinC_add (c1.of_le k2') (c2.of_le k2'),
    hopfRidge1, hopfRidge2, hopfProd, bilinC_ridge _ _ _ _ (by fun_prop),
    bilinC_ridge _ _ _ _ (contDiff_const.mul (contDiff_recipSmooth.of_le (by simp))),
    bilinC_biRidge _ _ _ Real.contDiff_sin (contDiff_recipSmooth.of_le (by simp))
      Real.hasDerivAt_sin (fun t => Real.hasDerivAt_cos t) k1 k2,
    (iteratedDeriv_of_hasDerivAt (sin_chain (-(A / M))).1 (sin_chain (-(A / M))).2.1
      (sin_chain (-(A / M))).2.2 _).2.1,
    (iteratedDeriv_of_hasDerivAt (fun t => (k1 t).const_mul (-Is / C))
      (fun t => (k2 t).const_mul (-Is / C)) (fun t => (k3 t).const_mul (-Is / C)) _).2.1]
  ext i
  fin_cases i <;> simp [r0, r1, r2]
  ring

/-- **The third derivative** of the translated field at the point:
`C(u, w, z) = (0, (A/M) u₀w₀z₀, (A/C) u₀w₀z₀ − (2A/C)(u₀w₂z₂ + u₂w₀z₂ + u₂w₂z₀) +
(6I_s/C) u₂w₂z₂, 0)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_trilinC (u w z : Fin 4 → ℂ) :
    trilinC (hopfModel M D C A Is Kp Ki).field 0 u w z =
      ![0, ((A / M : ℝ) : ℂ) * (u 0 * w 0 * z 0), ((A / C : ℝ) : ℂ) * (u 0 * w 0 * z 0) +
        ((-2 * A / C : ℝ) : ℂ) * (u 0 * w 2 * z 2 + u 2 * w 0 * z 2 + u 2 * w 2 * z 0) +
        ((6 * Is / C : ℝ) : ℂ) * (u 2 * w 2 * z 2), 0] := by
  obtain ⟨c1, c2, c3⟩ := contDiff_surrogate_pieces M D C A Is Kp Ki
  obtain ⟨r0, r1, r2, r3⟩ := recipSmooth_derivs
  obtain ⟨k1, k2, k3⟩ := hasDerivAt_recipSmooth_chain
  have c12 : ContDiff ℝ 3 (hopfRidge1 M D C A Is Kp Ki + hopfRidge2 C Is) := c1.add c2
  rw [trilinC_congr (Model.hopfModel_field_eventuallyEq M D C A Is Kp Ki), hopfSurrogate,
    trilinC_add c12 c3, trilinC_add c1 c2,
    hopfRidge1, hopfRidge2, hopfProd, trilinC_ridge _ _ _ _ (by fun_prop),
    trilinC_ridge _ _ _ _ (contDiff_const.mul (contDiff_recipSmooth.of_le (by simp))),
    trilinC_biRidge _ _ _ Real.contDiff_sin (contDiff_recipSmooth.of_le (by simp))
      Real.hasDerivAt_sin (fun t => Real.hasDerivAt_cos t)
      (fun t => (Real.hasDerivAt_sin t).neg) k1 k2 k3,
    (iteratedDeriv_of_hasDerivAt (sin_chain (-(A / M))).1 (sin_chain (-(A / M))).2.1
      (sin_chain (-(A / M))).2.2 _).2.2,
    (iteratedDeriv_of_hasDerivAt (fun t => (k1 t).const_mul (-Is / C))
      (fun t => (k2 t).const_mul (-Is / C)) (fun t => (k3 t).const_mul (-Is / C)) _).2.2]
  ext i
  fin_cases i <;> simp [r0, r1, r2, r3]
  · ring
  · ring

/-- The Jacobian of the slice at the point,
`[[0, 1, 0, 0], [−A/M, −D/M, K_p/M, K_i/M], [−A/C, 0, I_s/C, 0], [0, 0, 1, 0]]`. -/
def hopfJac : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -A / M, -D / M, Kp / M, Ki / M; -A / C, 0, Is / C, 0; 0, 0, 1, 0]

/-- The derivative of the translated field at the point (`Params.jacobian` of `VSMDC.lean` on the
slice). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_fderiv :
    fderiv ℝ (hopfModel M D C A Is Kp Ki).field 0 =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (hopfJac M D C A Is Kp Ki) := by
  set m := hopfModel M D C A Is Kp Ki
  have hV : m.p.Vref ≠ 0 := by simp [m, hopfModel]
  have h1 : HasFDerivAt (fun z : State 4 => z + m.point) (ContinuousLinearMap.id ℝ _) 0 :=
    (hasFDerivAt_id (0 : State 4)).add_const _
  have h2 := m.p.hasFDerivAt_field (x := 0 + m.point) (by simpa [Model.point] using hV)
  have hF : HasFDerivAt m.field
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (m.p.jacobian m.point)) 0 := by
    have h := h2.comp (0 : State 4) h1
    rw [zero_add] at h
    exact h
  rw [hF.fderiv]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m, hopfModel, hopfJac, Params.jacobian, Model.point, Plant.k, Plant.nodeSlope,
      Plant.Pe]

/-- The Jacobian of the translated field at the point (`Params.jacobian` of `VSMDC.lean`). -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_jacobianC :
    jacobianC (hopfModel M D C A Is Kp Ki).field 0 =
      (!![0, 1, 0, 0; -A / M, -D / M, Kp / M, Ki / M; -A / C, 0, Is / C, 0; 0, 0, 1, 0] :
        Matrix (Fin 4) (Fin 4) ℝ).map (fun x => (x : ℂ)) := by
  rw [jacobianC, Model.hopfModel_fderiv, cmat_toEuclideanCLM, hopfJac]

/-- The translated field vanishes at the point (a balanced point with `V* = 1`). -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_field_zero :
    (hopfModel M D C A Is Kp Ki).field 0 = 0 := by
  have h := Model.field_point_of_balanced (m := hopfModel M D C A Is Kp Ki)
    (by simp [hopfModel]) (Model.hopfModel_balanced M D C A Is Kp Ki)
  simpa [Model.field] using h

/-- The translated field is `C¹` off the plane `z₂ = −1`. -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_contDiffOn :
    ContDiffOn ℝ 1 (hopfModel M D C A Is Kp Ki).field {z : State 4 | z 2 + 1 ≠ 0} := by
  set m := hopfModel M D C A Is Kp Ki
  refine m.p.field_contDiffOn.comp (contDiff_id.add contDiff_const).contDiffOn fun z hz => ?_
  simpa [nonzeroDC, Model.point, m, hopfModel] using hz

@[tmio M, powerlib_domain] theorem Model.hopfModel_isOpen :
    IsOpen {z : State 4 | z 2 + 1 ≠ 0} :=
  isOpen_ne_fun ((Dynamics.contDiff_coord (n := 4) (k := 1) 2).continuous.add continuous_const)
    continuous_const

/-- The translated field is analytic at the point (`sin` and `1/(1 + z₂)` near `z₂ = 0`). -/
@[tmio M, powerlib_domain] theorem Model.hopfModel_analyticAt :
    AnalyticAt ℝ (hopfModel M D C A Is Kp Ki).field 0 := by
  have hc : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (hopfModel M D C A Is Kp Ki).field 0 := by
    have e := funext (Model.hopfModel_field M D C A Is Kp Ki)
    rw [e, contDiffAt_euclidean]
    intro i
    fin_cases i
    · simp
      fun_prop
    · simp
      fun_prop
    · simp
      refine ContDiffAt.div_const (contDiffAt_const.add (ContDiffAt.div (by fun_prop)
        (by fun_prop) (by simp))) _
    · simp
      fun_prop
  exact hc.analyticAt

/-! ## The supercritical witness -/

/-- The supercritical witness `M = D = C = A = 1`, `I_s = −1`, `K_p = K_i = 1`. -/
def hopfSup : Model := hopfModel 1 1 1 1 (-1) 1 1

/-- The Jacobian of `hopfSup`: `[[0, 1, 0, 0], [−1, −1, 1, 1], [−1, 0, −1, 0], [0, 0, 1, 0]]`. -/
def hopfSupJ : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; -1, -1, 1, 1; -1, 0, -1, 0; 0, 0, 1, 0]

/-- The critical right eigenvector `q = (1 − i, 1 + i, i, 1)`. -/
def hopfSupQ : Fin 4 → ℂ := ![1 + ((-1 : ℝ) : ℂ) * I, 1 + I, I, 1]

/-- The critical left eigenvector `p = (1/4 − i/4, 1/4, i/4, i/4)`, `⟨p, q⟩ = 1`. -/
def hopfSupP : Fin 4 → ℂ :=
  ![((1 / 4 : ℝ) : ℂ) + ((-1 / 4 : ℝ) : ℂ) * I, ((1 / 4 : ℝ) : ℂ), ((1 / 4 : ℝ) : ℂ) * I,
    ((1 / 4 : ℝ) : ℂ) * I]

@[tmio M, powerlib_domain] private theorem hopfSup_jacobianC :
    jacobianC hopfSup.field 0 = hopfSupJ.map (fun x => (x : ℂ)) := by
  rw [hopfSup, Model.hopfModel_jacobianC]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hopfSupJ]

/-- The quartic of `hopfSup`: `a₃ = a₂ = a₁ = 2`, `a₀ = 1`, on the Hopf boundary. Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem hopfSup_coeffs :
    hopfSup.a3 = 2 ∧ hopfSup.a2 = 2 ∧ hopfSup.a1 = 2 ∧ hopfSup.a0 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [hopfSup, hopfModel, Model.a3, Model.a2, Model.a1, Model.a0, Model.b, Model.k,
      Plant.k]

/-- **A Hopf point**: the characteristic polynomial of `hopfSup` is `(s² + 1)(s + 1)²`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfSup_charpoly :
    (jacobianC hopfSup.field 0).charpoly =
      (X ^ 2 + Polynomial.C (((1 : ℝ) : ℂ) ^ 2)) *
        (X ^ 2 + Polynomial.C 2 * X + Polynomial.C 1) := by
  refine Polynomial.funext fun s => ?_
  rw [hopfSup_jacobianC, show hopfSupJ.map (fun x => (x : ℂ)) = Linear.complexify hopfSupJ from rfl,
    ← Linear.det_characteristicMatrix_eq_eval, Criteria.det_characteristicMatrix_fin_four]
  simp [hopfSupJ, Matrix.trace, Fin.sum_univ_four, Criteria.principalMinorSum2Fin4,
    Criteria.principalMinorSum3Fin4, Criteria.det_fin_four]
  ring

/-- The other roots of `hopfSup`, `s = −1` (double), lie in the open left half-plane. -/
@[tmio M, powerlib_domain] theorem hopfSup_r_roots (s : ℂ)
    (h : (X ^ 2 + Polynomial.C 2 * X + Polynomial.C (1 : ℂ)).eval s = 0) : s.re < 0 := by
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
  have h' : (s + 1) ^ 2 = 0 := by linear_combination h
  have hs : s = -1 := by linear_combination pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  rw [hs]
  norm_num

/-- **The critical pair** of `hopfSup` at `ω = 1`. -/
@[tmio M, powerlib_domain] theorem hopfSup_isCriticalPair :
    IsCriticalPair hopfSup.field 0 1 hopfSupQ hopfSupP := by
  refine ⟨Model.hopfModel_field_zero _ _ _ _ _ _ _, one_pos, ?_, ?_, ?_⟩
  · rw [hopfSup_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfSupQ, hopfSupJ,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  · rw [hopfSup_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfSupP, hopfSupJ,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · simp [dotProduct, Fin.sum_univ_four, hopfSupP, hopfSupQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num

/-- **The first Lyapunov coefficient of `hopfSup`**: `ℓ₁ = −1/25`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfSup_firstLyapunov :
    firstLyapunov hopfSup.field 0 1 hopfSupQ hopfSupP = -1 / 25 := by
  set s : Fin 4 → ℂ := ![((-4 / 15 : ℝ) : ℂ) + ((-2 / 15 : ℝ) : ℂ) * I,
    ((4 / 15 : ℝ) : ℂ) + ((-8 / 15 : ℝ) : ℂ) * I, ((68 / 75 : ℝ) : ℂ) + ((8 / 25 : ℝ) : ℂ) * I,
    ((4 / 25 : ℝ) : ℂ) + ((-34 / 75 : ℝ) : ℂ) * I]
  have hA : IsUnit (jacobianC hopfSup.field 0).det := by
    rw [hopfSup_jacobianC, show hopfSupJ.map (fun x => (x : ℂ)) =
      Complex.ofRealHom.mapMatrix hopfSupJ from rfl, ← RingHom.map_det]
    refine isUnit_iff_ne_zero.mpr ?_
    simp [hopfSupJ, Criteria.det_fin_four]
  have h2 : IsUnit (shift2 (jacobianC hopfSup.field 0) 1).det := by
    have h := congrArg (fun P => P.eval ((2 * (1 : ℝ) : ℂ) * I)) hopfSup_charpoly
    simp only [Matrix.eval_charpoly] at h
    rw [shift2, show ((2 * (1 : ℝ) : ℂ) * I) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      Matrix.scalar (Fin 4) ((2 * (1 : ℝ) : ℂ) * I) by rw [Matrix.smul_one_eq_diagonal]; rfl, h]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h1 := congrArg Complex.re h0
    simp [pow_two] at h1
    norm_num at h1
  have hr : jacobianC hopfSup.field 0 *ᵥ (0 : Fin 4 → ℂ) =
      bilinC hopfSup.field 0 hopfSupQ (star hopfSupQ) := by
    rw [Matrix.mulVec_zero, hopfSup, Model.hopfModel_bilinC]
    ext i; fin_cases i
    all_goals simp [hopfSupQ, Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div,
      -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add,
      -Complex.ofReal_inv]
    all_goals norm_num
  have hs : shift2 (jacobianC hopfSup.field 0) 1 *ᵥ s =
      bilinC hopfSup.field 0 hopfSupQ hopfSupQ := by
    rw [hopfSup_jacobianC, shift2, hopfSup, Model.hopfModel_bilinC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfSupQ, hopfSupJ, s,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  rw [firstLyapunov_eq_of_solve hA h2 hr hs, hopfSup, Model.hopfModel_trilinC,
    Model.hopfModel_bilinC, Model.hopfModel_bilinC]
  simp [pairing_apply, Fin.sum_univ_four, hopfSupP, hopfSupQ, s, Complex.mul_re,
    Complex.mul_im, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
    -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-! ## The subcritical witness -/

/-- The subcritical witness `M = D = C = A = 2`, `I_s = −1/2`, `K_p = 2`, `K_i = 1/2`. -/
def hopfSub : Model := hopfModel 2 2 2 2 (-1 / 2) 2 (1 / 2)

/-- The Jacobian of `hopfSub`:
`[[0, 1, 0, 0], [−1, −1, 1, 1/4], [−1, 0, −1/4, 0], [0, 0, 1, 0]]`. -/
def hopfSubJ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -1, -1, 1, 1 / 4; -1, 0, -1 / 4, 0; 0, 0, 1, 0]

/-- The critical right eigenvector `q = (1 − i/4, 1/4 + i, i, 1)`. -/
def hopfSubQ : Fin 4 → ℂ := ![1 + ((-1 / 4 : ℝ) : ℂ) * I, ((1 / 4 : ℝ) : ℂ) + I, I, 1]

/-- The critical left eigenvector of `hopfSub`, `⟨p, q⟩ = 1`. -/
def hopfSubP : Fin 4 → ℂ :=
  ![((8 / 17 : ℝ) : ℂ) + ((-2 / 17 : ℝ) : ℂ) * I, ((5 / 17 : ℝ) : ℂ) + ((3 / 17 : ℝ) : ℂ) * I,
    ((-3 / 17 : ℝ) : ℂ) + ((5 / 17 : ℝ) : ℂ) * I, ((-3 / 68 : ℝ) : ℂ) + ((5 / 68 : ℝ) : ℂ) * I]

@[tmio M, powerlib_domain] private theorem hopfSub_jacobianC :
    jacobianC hopfSub.field 0 = hopfSubJ.map (fun x => (x : ℂ)) := by
  rw [hopfSub, Model.hopfModel_jacobianC]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hopfSubJ]

/-- The quartic of `hopfSub`: `a₃ = a₂ = a₁ = 5/4`, `a₀ = 1/4`, on the Hopf boundary. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfSub_coeffs :
    hopfSub.a3 = 5 / 4 ∧ hopfSub.a2 = 5 / 4 ∧ hopfSub.a1 = 5 / 4 ∧ hopfSub.a0 = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [hopfSub, hopfModel, Model.a3, Model.a2, Model.a1, Model.a0, Model.b, Model.k,
      Plant.k]

/-- **A Hopf point**: the characteristic polynomial of `hopfSub` is `(s² + 1)(s² + 5s/4 + 1/4)`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfSub_charpoly :
    (jacobianC hopfSub.field 0).charpoly =
      (X ^ 2 + Polynomial.C (((1 : ℝ) : ℂ) ^ 2)) *
        (X ^ 2 + Polynomial.C (5 / 4) * X + Polynomial.C (1 / 4)) := by
  refine Polynomial.funext fun s => ?_
  rw [hopfSub_jacobianC, show hopfSubJ.map (fun x => (x : ℂ)) = Linear.complexify hopfSubJ from rfl,
    ← Linear.det_characteristicMatrix_eq_eval, Criteria.det_characteristicMatrix_fin_four]
  simp [hopfSubJ, Matrix.trace, Fin.sum_univ_four, Criteria.principalMinorSum2Fin4,
    Criteria.principalMinorSum3Fin4, Criteria.det_fin_four]
  ring

/-- The other roots of `hopfSub`, `s = −1, −1/4`, lie in the open left half-plane. -/
@[tmio M, powerlib_domain] theorem hopfSub_r_roots (s : ℂ)
    (h : (X ^ 2 + Polynomial.C (5 / 4) * X + Polynomial.C (1 / 4 : ℂ)).eval s = 0) :
    s.re < 0 := by
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at h
  have h' : (s + 1) * (s + 1 / 4) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with hs | hs
  · rw [show s = -1 by linear_combination hs]
    norm_num
  · rw [show s = -1 / 4 by linear_combination hs]
    norm_num

/-- **The critical pair** of `hopfSub` at `ω = 1`. -/
@[tmio M, powerlib_domain] theorem hopfSub_isCriticalPair :
    IsCriticalPair hopfSub.field 0 1 hopfSubQ hopfSubP := by
  refine ⟨Model.hopfModel_field_zero _ _ _ _ _ _ _, one_pos, ?_, ?_, ?_⟩
  · rw [hopfSub_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfSubQ, hopfSubJ,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · rw [hopfSub_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfSubP, hopfSubJ,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · simp [dotProduct, Fin.sum_univ_four, hopfSubP, hopfSubQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num

/-- **The first Lyapunov coefficient of `hopfSub`**: `ℓ₁ = 8/85`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfSub_firstLyapunov :
    firstLyapunov hopfSub.field 0 1 hopfSubQ hopfSubP = 8 / 85 := by
  set s : Fin 4 → ℂ := ![((-4 / 15 : ℝ) : ℂ) + ((-2 / 15 : ℝ) : ℂ) * I,
    ((4 / 15 : ℝ) : ℂ) + ((-8 / 15 : ℝ) : ℂ) * I, ((16 / 15 : ℝ) : ℂ),
    ((-8 / 15 : ℝ) : ℂ) * I]
  have hA : IsUnit (jacobianC hopfSub.field 0).det := by
    rw [hopfSub_jacobianC, show hopfSubJ.map (fun x => (x : ℂ)) =
      Complex.ofRealHom.mapMatrix hopfSubJ from rfl, ← RingHom.map_det]
    refine isUnit_iff_ne_zero.mpr ?_
    simp [hopfSubJ, Criteria.det_fin_four]
  have h2 : IsUnit (shift2 (jacobianC hopfSub.field 0) 1).det := by
    have h := congrArg (fun P => P.eval ((2 * (1 : ℝ) : ℂ) * I)) hopfSub_charpoly
    simp only [Matrix.eval_charpoly] at h
    rw [shift2, show ((2 * (1 : ℝ) : ℂ) * I) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      Matrix.scalar (Fin 4) ((2 * (1 : ℝ) : ℂ) * I) by rw [Matrix.smul_one_eq_diagonal]; rfl, h]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h1 := congrArg Complex.re h0
    simp [pow_two] at h1
    norm_num at h1
  have hr : jacobianC hopfSub.field 0 *ᵥ (0 : Fin 4 → ℂ) =
      bilinC hopfSub.field 0 hopfSubQ (star hopfSubQ) := by
    rw [Matrix.mulVec_zero, hopfSub, Model.hopfModel_bilinC]
    ext i; fin_cases i
    all_goals simp [hopfSubQ, Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div,
      -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add,
      -Complex.ofReal_inv]
    all_goals norm_num
  have hs : shift2 (jacobianC hopfSub.field 0) 1 *ᵥ s =
      bilinC hopfSub.field 0 hopfSubQ hopfSubQ := by
    rw [hopfSub_jacobianC, shift2, hopfSub, Model.hopfModel_bilinC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hopfSubQ, hopfSubJ, s,
      Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  rw [firstLyapunov_eq_of_solve hA h2 hr hs, hopfSub, Model.hopfModel_trilinC,
    Model.hopfModel_bilinC, Model.hopfModel_bilinC]
  simp [pairing_apply, Fin.sum_univ_four, hopfSubP, hopfSubQ, s, Complex.mul_re,
    Complex.mul_im, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
    -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-! ## Connection conclusions -/

/-- `hopfSup` lies on the Routh boundary: balanced with `V* = 1`, neither Routh nor a strict
violation (`a₁² + a₃² a₀ = a₃ a₂ a₁ = 8`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfSup_not_meets : ¬ hopfSup.Stable ∧ ¬ hopfSup.Unstable := by
  obtain ⟨h3, h2, h1, h0⟩ := hopfSup_coeffs
  refine ⟨fun ⟨_, _, _, _, _, hg⟩ => ?_, fun ⟨_, _, hv⟩ => ?_⟩
  · rw [h3, h2, h1, h0] at hg
    norm_num at hg
  · rw [h3, h2, h1, h0] at hv
    norm_num at hv

/-- `hopfSub` lies on the Routh boundary: balanced with `V* = 1`, neither Routh nor a strict
violation (`a₁² + a₃² a₀ = a₃ a₂ a₁ = 125/64`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfSub_not_meets : ¬ hopfSub.Stable ∧ ¬ hopfSub.Unstable := by
  obtain ⟨h3, h2, h1, h0⟩ := hopfSub_coeffs
  refine ⟨fun ⟨_, _, _, _, _, hg⟩ => ?_, fun ⟨_, _, hv⟩ => ?_⟩
  · rw [h3, h2, h1, h0] at hg
    norm_num at hg
  · rw [h3, h2, h1, h0] at hv
    norm_num at hv

/-- **A supercritical Hopf point of the Routh boundary is locally asymptotically stable**:
`hopfSup` (`ℓ₁ = −1/25`), by the centre-manifold reduction for fields smooth near the point
(`Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly_local`). -/
@[tmio TM, powerlib_domain] theorem hopfSup_mem_den_locallyAsymptoticallyStable :
    connection% (hopfSup ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff']
  exact Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly_local
    (Model.hopfModel_isOpen) (by simp) (Model.hopfModel_contDiffOn _ _ _ _ _ _ _)
    (Model.hopfModel_analyticAt _ _ _ _ _ _ _) hopfSup_isCriticalPair hopfSup_charpoly
    hopfSup_r_roots (by rw [hopfSup_firstLyapunov]; norm_num)

/-- **A subcritical Hopf point of the Routh boundary is unstable**: `hopfSub` (`ℓ₁ = 8/85`,
`Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly_local`). -/
@[tmio TM, powerlib_domain] theorem hopfSub_mem_den_unstable :
    connection% (hopfSub ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff']
  exact Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly_local
    (Model.hopfModel_isOpen) (by simp) (Model.hopfModel_contDiffOn _ _ _ _ _ _ _)
    (Model.hopfModel_analyticAt _ _ _ _ _ _ _) hopfSub_isCriticalPair hopfSub_charpoly
    hopfSub_r_roots (by rw [hopfSub_firstLyapunov]; norm_num)

/-- **The local asymptotic translation is not exact within `V* ≠ 0`**: `hopfSup` is locally
asymptotically stable, has `V* = 1` and does not meet the stability condition. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_inter_locallyAsymptoticallyStable :
    connection% (¬ TMIO.realize family.meets
      (family.translate (.flow .locallyAsymptoticallyStable)) =
        family.den (.flow .locallyAsymptoticallyStable) ∩ {m : Model | m.p.Vref ≠ 0}) :=
  Spectral.local_realize_ne_den_inter_of_witness (Or.inr (Or.inl rfl))
    hopfSup_mem_den_locallyAsymptoticallyStable
    (show hopfSup.p.Vref ≠ 0 by simp [hopfSup, hopfModel]) hopfSup_not_meets.1

@[tmio M, powerlib_domain] private theorem hopf_meets_iff (q : Spectral.Requirement) :
    family.meets hopfSup q ↔ family.meets hopfSub q := by
  cases q
  · exact ⟨fun h => absurd h hopfSup_not_meets.1, fun h => absurd h hopfSub_not_meets.1⟩
  · exact ⟨fun h => absurd h hopfSup_not_meets.2, fun h => absurd h hopfSub_not_meets.2⟩

/-- **Local asymptotic stability is inexpressible in the requirement language**: `hopfSup` and
`hopfSub` meet the same requirements (none); the first is locally asymptotically stable, the
second unstable. -/
@[tmio TM, powerlib_domain] theorem realize_ne_den_locallyAsymptoticallyStable :
    connection% (∀ T, TMIO.realize family.meets T ≠
      family.den (.flow .locallyAsymptoticallyStable)) :=
  Spectral.realize_ne_den_of_indistinguishable hopf_meets_iff
    hopfSup_mem_den_locallyAsymptoticallyStable fun h =>
      Spectral.not_mem_den_lyapunovStable_of_unstable hopfSub_mem_den_unstable
        (Spectral.den_las_subset_lyapunovStable h)

end VSMDC

end powerlib.GFM.DCLink
