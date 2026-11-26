import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.SingularPerturbation.UniformBasin

/-! # The VSM + power filter in the fast-filter limit: an explicit uniform region of attraction

Model boundary.
* The three-state VSM + power filter `GFM.VSMLPF` of
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`: state `(δ, ω, P_f)`, `δ̇ = ω`,
  `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)`, infinite bus, lossless line, constant EMF,
  export-positive power, continuous time, autonomous. A model is read about a selected angle `δ*`
  (`VSMLPF.Model`, point `(δ*, 0, P₀)`).
* Read as a singularly perturbed system with `ε = 1/ω_c`: the filtered power is the fast state
  (`VSMLPF.split`), the swing `(δ, ω)` the slow one, the field with rate `ω_c` is the `ε`-system of
  the unit-rate field (`VSMLPF.unitFilter`, `VSMLPF.field_eq_splitScaledField`), and the fast row
  vanishes on the quasi-steady graph `P_f = K₀ sin δ` (`VSMLPF.graph`).
* Parameter range of the basin: `M, D > 0`, balance `K₀ sin δ* = P₀`, synchronizing
  `K = K₀ cos δ* > 0`; every filter rate above the explicit threshold `Model.basinFilterRate`.
  Excluded as in `VSMLPF.lean`.

Source: Kokotović–Khalil–O'Reilly, *Singular Perturbation Methods in Control* (1986), Ch. 7;
Khalil, *Nonlinear Systems* (3rd ed.), Thm. 11.4; work-sync `theory/T-gfm-control.md` §1.2,
§1.4 (VSM swing law, power filter), `theory/T-singular-perturbation.md` §1.3–§1.5; the generic
law `SingularPerturbation.uniform_basin_of_lipschitz`
(`theorem/SingularPerturbation/UniformBasin.lean`). The Lyapunov matrix of the reduced swing is
solved in closed form (`P R + Rᵀ P = −1`, checked by `ring`).

Results.
* Static support: `split` (fast `P_f`, slow `(δ, ω)`) with `split_symm_inl`,
  `split_symm_inr_zero`, `split_symm_inr_one`; `unitFilter`; `field_eq_splitScaledField`; the
  graph `graph` with its derivative `graphDeriv` (`hasFDerivAt_graph`, `contDiff_graph`), the
  bounds `norm_graphDeriv_le` (`‖Φ'‖ ≤ 1 + |K₀|`), `norm_graphDeriv_sub_le`
  (`‖Φ'(s) − Φ'(s')‖ ≤ |K₀| |s − s'|`) and `norm_fderiv_unitFilter_sub_le`
  (`‖f'(u) − f'(w)‖ ≤ |K₀| |u − w|` for the unit-rate field): the second derivatives are bounded
  by `|K₀|` everywhere.
* `Model.lyapP`: with `a = K/M`, `d = D/M`, `P₀ = [[d/(2a) + (1 + a)/(2d), 1/(2a)],
  [1/(2a), (1 + a)/(2ad)]]`, `Model.lyapP_lyapunov` (`P₀ R + Rᵀ P₀ = −1` for the reduced Jacobian
  `R = [[0, 1], [−a, −d]]`, `Model.reducedJ`), `Model.lyapLower` (determinant over trace, a lower
  bound of the form, `Model.lyapLower_pos`).
* The explicit constants: `Model.basinFilterRate` (the threshold `1/ε*` of
  `SingularPerturbation.basinEpsStarOf` at explicit norm bounds), `Model.basinRadius` (the radius
  `SingularPerturbation.basinRadius` at the Lipschitz constants `|K₀|`), `Model.basinOvershoot`,
  `Model.basinRate`; `Model.basinFilterRate_pos`, `Model.basinRadius_pos`.
* Implementation evidence (private, trajectory level): `Model.uniform_basin` — for `M, D > 0`,
  balance and `K > 0`, for every `ω_c > Model.basinFilterRate` the ball of radius
  `Model.basinRadius` about `(δ*, 0, P₀)` lies in the region of attraction of the VSM + power
  filter with rate `ω_c`, and every solution segment from it decays as `C e^{−a(t − t₀)}` with the
  explicit `C = Model.basinOvershoot`, `a = Model.basinRate`; radius, overshoot and rate do not
  depend on `ω_c`.

Family and connection conclusions.
No family and no connection conclusion: a region of attraction and decay constants uniform over a
family of systems are outside the sentence language (private implementation evidence, as in
`theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean`); the local sentences of the same
equilibria are the connection statements of `VSMLPF.family`.
-/

noncomputable section
namespace powerlib.GFM
open Set Metric Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)

namespace VSMLPF

/-- The splitting of `(δ, ω, P_f)` into the fast filtered power and the slow swing `(δ, ω)`. -/
def split : Fin 3 ≃ Fin 1 ⊕ Fin 2 :=
  (finSumFinEquiv (m := 2) (n := 1)).symm.trans (Equiv.sumComm (Fin 2) (Fin 1))

@[tmio M, simp, powerlib_domain] theorem split_symm_inl (i : Fin 1) :
    split.symm (.inl i) = 2 := by
  fin_cases i; rfl

@[tmio M, simp, powerlib_domain] theorem split_symm_inr_zero : split.symm (.inr 0) = 0 := rfl

@[tmio M, simp, powerlib_domain] theorem split_symm_inr_one : split.symm (.inr 1) = 1 := rfl

variable (g : VSMLPF)

/-- The same model with the unit filter rate `ω_c = 1`. -/
def unitFilter : VSMLPF := { g with ωc := 1 }

/-- **The power filter as a singular perturbation.** The field with filter rate `ω_c` is the
`ε`-system of the unit-rate field with `ε = 1/ω_c` (the filter row multiplied by `ε⁻¹ = ω_c`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem field_eq_splitScaledField (x : State 3) :
    g.field x = SingularPerturbation.splitScaledField split g.ωc⁻¹ g.unitFilter.field x := by
  refine state3_ext ?_ ?_ ?_
  · have h := SingularPerturbation.splitScaledField_slow split g.ωc⁻¹ g.unitFilter.field x 0
    rw [split_symm_inr_zero] at h
    rw [h]; simp [unitFilter]
  · have h := SingularPerturbation.splitScaledField_slow split g.ωc⁻¹ g.unitFilter.field x 1
    rw [split_symm_inr_one] at h
    rw [h]; simp [unitFilter]
  · have h := SingularPerturbation.splitScaledField_fast split g.ωc⁻¹ g.unitFilter.field x 0
    rw [split_symm_inl] at h
    rw [h, inv_inv]; simp [unitFilter]

/-- The quasi-steady graph `P_f = K₀ sin δ` of the power filter over the slow swing `(δ, ω)`. -/
def graph (s : EuclideanSpace ℝ (Fin 2)) : State 3 := mk3 (s 0) (s 1) (g.K0 * Real.sin (s 0))

/-- The derivative of the graph: `h ↦ (h₀, h₁, K₀ cos δ h₀)`. -/
def graphDeriv (s : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) →L[ℝ] State 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => mk3 (h 0) (h 1) (g.K0 * Real.cos (s 0) * h 0)
      map_add' := fun u v => state3_ext (by simp) (by simp) (by simp; ring)
      map_smul' := fun c u => state3_ext (by simp) (by simp) (by simp; ring) }

@[tmio M, simp, powerlib_domain] theorem graphDeriv_apply (s h : EuclideanSpace ℝ (Fin 2)) :
    g.graphDeriv s h = mk3 (h 0) (h 1) (g.K0 * Real.cos (s 0) * h 0) := rfl

@[tmio M, powerlib_domain] theorem graph_slow (s : EuclideanSpace ℝ (Fin 2)) (k : Fin 2) :
    g.graph s (split.symm (.inr k)) = s k := by
  fin_cases k <;> simp [graph]

@[tmio M, powerlib_domain] theorem hasFDerivAt_graph (s : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt g.graph (g.graphDeriv s) s := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt (x := s)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt (x := s)
  fin_cases i
  · convert h0 using 1
    · funext y; simp [graph]
    · apply ContinuousLinearMap.ext; intro v; simp
  · convert h1 using 1
    · funext y; simp [graph]
    · apply ContinuousLinearMap.ext; intro v; simp
  · have h := ((Real.hasDerivAt_sin (s 0)).comp_hasFDerivAt s h0).const_mul g.K0
    convert h using 1
    · funext y; simp [graph]
    · apply ContinuousLinearMap.ext; intro v; simp; ring

@[tmio M, powerlib_domain] theorem fderiv_graph (s : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ g.graph s = g.graphDeriv s :=
  (g.hasFDerivAt_graph s).fderiv

@[tmio M, powerlib_domain] theorem contDiff_graph : ContDiff ℝ 1 g.graph := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [graph] using (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff (n := 1)
  · simpa [graph] using (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff (n := 1)
  · simp only [graph, Fin.reduceFinMk, Fin.isValue, mk3_two]
    exact contDiff_const.mul (Real.contDiff_sin.comp (PiLp.proj 2 (fun _ : Fin 2 => ℝ)
      (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff)

/-- The graph's derivative is bounded: `‖Φ'(s)‖ ≤ 1 + |K₀|`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem norm_graphDeriv_le (s : EuclideanSpace ℝ (Fin 2)) :
    ‖g.graphDeriv s‖ ≤ 1 + |g.K0| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have e1 : ‖g.graphDeriv s h‖ ^ 2 =
      h 0 ^ 2 + h 1 ^ 2 + (g.K0 * Real.cos (s 0) * h 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; simp
  have e2 : ‖h‖ ^ 2 = h 0 ^ 2 + h 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hc : (g.K0 * Real.cos (s 0)) ^ 2 ≤ |g.K0| ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith [Real.cos_sq_le_one (s 0), sq_nonneg g.K0]
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (h 0))
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
  rw [e1, show ((1 + |g.K0|) * ‖h‖) ^ 2 = (1 + |g.K0|) ^ 2 * ‖h‖ ^ 2 from mul_pow _ _ _, e2,
    show (g.K0 * Real.cos (s 0) * h 0) ^ 2 = (g.K0 * Real.cos (s 0)) ^ 2 * h 0 ^ 2 by ring]
  nlinarith [sq_nonneg (h 0), sq_nonneg (h 1), abs_nonneg g.K0]

/-- The graph's derivative is Lipschitz: `‖Φ'(s) − Φ'(s')‖ ≤ |K₀| |s − s'|` (the second derivative
of the graph is bounded by `|K₀|`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem norm_graphDeriv_sub_le (s s' : EuclideanSpace ℝ (Fin 2)) :
    ‖g.graphDeriv s - g.graphDeriv s'‖ ≤ |g.K0| * ‖s - s'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have e1 : ‖(g.graphDeriv s - g.graphDeriv s') h‖ ^ 2 =
      (g.K0 * Real.cos (s 0) * h 0 - g.K0 * Real.cos (s' 0) * h 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; simp
  have hcos := Real.abs_cos_sub_cos_le (s 0) (s' 0)
  have hs : |s 0 - s' 0| ≤ ‖s - s'‖ := by simpa using Dynamics.abs_apply_le_norm (s - s') 0
  have hh := Dynamics.abs_apply_le_norm h 0
  have hb : |g.K0 * Real.cos (s 0) * h 0 - g.K0 * Real.cos (s' 0) * h 0| ≤
      |g.K0| * ‖s - s'‖ * ‖h‖ := by
    rw [show g.K0 * Real.cos (s 0) * h 0 - g.K0 * Real.cos (s' 0) * h 0 =
      g.K0 * (Real.cos (s 0) - Real.cos (s' 0)) * h 0 by ring, abs_mul, abs_mul]
    gcongr
    exact hcos.trans hs
  have hn : ‖(g.graphDeriv s - g.graphDeriv s') h‖ =
      |g.K0 * Real.cos (s 0) * h 0 - g.K0 * Real.cos (s' 0) * h 0| := by
    rw [← Real.sqrt_sq (norm_nonneg _), e1, Real.sqrt_sq_eq_abs]
  rw [hn]; exact hb

/-- The Jacobian of the unit-rate field is Lipschitz: `‖f'(u) − f'(w)‖ ≤ |K₀| |u − w|` (the second
derivative of the field is bounded by `|K₀|`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem norm_fderiv_unitFilter_sub_le (u w : State 3) :
    ‖fderiv ℝ g.unitFilter.field u - fderiv ℝ g.unitFilter.field w‖ ≤ |g.K0| * ‖u - w‖ := by
  rw [g.unitFilter.fderiv_field, g.unitFilter.fderiv_field, ← map_sub]
  refine (SingularPerturbation.norm_toEuclideanCLM_le_absSum _).trans ?_
  have hcos := Real.abs_cos_sub_cos_le (u 0) (w 0)
  have hs : |u 0 - w 0| ≤ ‖u - w‖ := by simpa using Dynamics.abs_apply_le_norm (u - w) 0
  have hA : SingularPerturbation.absSum
      (g.unitFilter.jacobian (u 0) - g.unitFilter.jacobian (w 0)) =
      |g.K0| * |Real.cos (u 0) - Real.cos (w 0)| := by
    simp [SingularPerturbation.absSum, Fin.sum_univ_three, jacobian, unitFilter]
    rw [← mul_sub, abs_mul]
  rw [hA]
  exact mul_le_mul_of_nonneg_left (hcos.trans hs) (abs_nonneg _)

/-! ## The explicit Lyapunov matrix and constants -/

/-- The reduced Jacobian `R = [[0, 1], [−K/M, −D/M]]` of the swing at the selected angle. -/
def Model.reducedJ (m : Model) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -(m.K / m.g.M), -(m.g.D / m.g.M)]

/-- The Lyapunov matrix of the reduced swing in closed form (`a = K/M`, `d = D/M`):
`[[d/(2a) + (1 + a)/(2d), 1/(2a)], [1/(2a), (1 + a)/(2ad)]]`. -/
def Model.lyapP (m : Model) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m.g.D / m.g.M / (2 * (m.K / m.g.M)) + (1 + m.K / m.g.M) / (2 * (m.g.D / m.g.M)),
    1 / (2 * (m.K / m.g.M));
    1 / (2 * (m.K / m.g.M)),
    (1 + m.K / m.g.M) / (2 * (m.K / m.g.M) * (m.g.D / m.g.M))]

/-- `P₀ R + Rᵀ P₀ = −1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.lyapP_lyapunov (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hK : 0 < m.K) :
    m.lyapP * m.reducedJ + m.reducedJᵀ * m.lyapP = -1 := by
  have ha : m.K / m.g.M ≠ 0 := (div_pos hK hM).ne'
  have hd : m.g.D / m.g.M ≠ 0 := (div_pos hD hM).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.lyapP, Model.reducedJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

@[tmio M, powerlib_domain] theorem Model.lyapP_symm (m : Model) : m.lyapPᵀ = m.lyapP := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The lower bound of the Lyapunov form: determinant over trace. -/
def Model.lyapLower (m : Model) : ℝ :=
  (m.lyapP 0 0 * m.lyapP 1 1 - m.lyapP 0 1 ^ 2) / (m.lyapP 0 0 + m.lyapP 1 1)

@[tmio M, powerlib_domain] private theorem Model.lyapP_trace_pos (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hK : 0 < m.K) : 0 < m.lyapP 0 0 + m.lyapP 1 1 := by
  have ha := div_pos hK hM
  have hd := div_pos hD hM
  simp only [Model.lyapP, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  positivity

@[tmio M, powerlib_domain] private theorem Model.lyapP_det_pos (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hK : 0 < m.K) :
    0 < m.lyapP 0 0 * m.lyapP 1 1 - m.lyapP 0 1 ^ 2 := by
  have ha := div_pos hK hM
  have hd := div_pos hD hM
  simp only [Model.lyapP, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  set a := m.K / m.g.M
  set d := m.g.D / m.g.M
  have e : (d / (2 * a) + (1 + a) / (2 * d)) * ((1 + a) / (2 * a * d)) - (1 / (2 * a)) ^ 2 =
      1 / (4 * a) + (1 + a) ^ 2 / (4 * a * d ^ 2) := by
    field_simp; ring
  rw [e]; positivity

@[tmio M, powerlib_domain] theorem Model.lyapLower_pos (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hK : 0 < m.K) : 0 < m.lyapLower :=
  div_pos (m.lyapP_det_pos hM hD hK) (m.lyapP_trace_pos hM hD hK)

/-- The norm bound of the unit-rate Jacobian at the selected angle:
`2 + |D/M| + |1/M| + |K₀ cos δ*|` (the sum of the absolute values of its entries). -/
def Model.jacBound (m : Model) : ℝ := SingularPerturbation.absSum (m.g.unitFilter.jacobian m.δ)

/-- The explicit threshold of the filter rate, `1/ε*`: `SingularPerturbation.basinEpsStarOf` at
the norm bounds `Σ|P₀ᵢⱼ|`, `1/2`, `Model.jacBound`, `1 + |K₀|`, `Σ|Rᵢⱼ|`. -/
def Model.basinFilterRate (m : Model) : ℝ :=
  (SingularPerturbation.basinEpsStarOf (SingularPerturbation.absSum m.lyapP) (1 / 2) m.jacBound
    (1 + |m.g.K0|) (SingularPerturbation.absSum m.reducedJ))⁻¹

/-- **The explicit radius** of the uniform region of attraction:
`SingularPerturbation.basinRadius` at the lower bounds `Model.lyapLower`, `1/2`, the norm bounds
of `Model.basinFilterRate` and the Lipschitz constants `|K₀|` of the field's and the graph's
derivatives on balls of radius `1`. -/
def Model.basinRadius (m : Model) : ℝ :=
  SingularPerturbation.basinRadius m.lyapLower (1 / 2) (SingularPerturbation.absSum m.lyapP)
    (1 / 2) m.jacBound (1 + |m.g.K0|) |m.g.K0| |m.g.K0| 1 1

/-- The explicit overshoot constant of the uniform decay. -/
def Model.basinOvershoot (m : Model) : ℝ :=
  SingularPerturbation.basinOvershoot m.lyapLower (1 / 2) (SingularPerturbation.absSum m.lyapP)
    (1 / 2) (1 + |m.g.K0|)

/-- The explicit rate of the uniform decay. -/
def Model.basinRate (m : Model) : ℝ :=
  SingularPerturbation.basinRate (SingularPerturbation.absSum m.lyapP) (1 / 2)

@[tmio M, powerlib_domain] theorem Model.basinFilterRate_pos (m : Model) : 0 < m.basinFilterRate :=
  inv_pos.mpr (SingularPerturbation.basinEpsStarOf_pos (SingularPerturbation.absSum_nonneg _)
    (by norm_num) (SingularPerturbation.absSum_nonneg _) (by positivity))

@[tmio M, powerlib_domain] theorem Model.basinRadius_pos (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hK : 0 < m.K) : 0 < m.basinRadius :=
  SingularPerturbation.basinRadius_pos (m.lyapLower_pos hM hD hK) (by norm_num)
    (SingularPerturbation.absSum_nonneg _) (by norm_num) (SingularPerturbation.absSum_nonneg _)
    (by positivity) (abs_nonneg _) (abs_nonneg _) one_pos one_pos

/-! ## The uniform region of attraction -/

/-- **An explicit region of attraction uniform in the filter rate.** For `M, D > 0`, balance
`K₀ sin δ* = P₀` and `K = K₀ cos δ* > 0`: for every filter rate `ω_c > Model.basinFilterRate` the
ball of radius `Model.basinRadius` about `(δ*, 0, P₀)` lies in the region of attraction of the
VSM + power filter with rate `ω_c`, and every solution segment from that ball decays as
`C e^{−a(t − t₀)}` with `C = Model.basinOvershoot`, `a = Model.basinRate`; radius, overshoot and
rate are explicit in `M, D, K₀, δ*` and do not depend on `ω_c`
(`SingularPerturbation.uniform_basin_of_lipschitz` with `ε = 1/ω_c`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem Model.uniform_basin (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hbal : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : 0 < m.K) {ωc : ℝ}
    (hω : m.basinFilterRate < ωc) :
    ball m.point m.basinRadius ⊆ Flow.regionOfAttraction ({ m.g with ωc := ωc } : VSMLPF).field
      m.point ∧
    ∀ (t₀ t₁ : ℝ) (φ : ℝ → State 3), IsTrajectoryOn φ ({ m.g with ωc := ωc } : VSMLPF).field t₀ t₁ →
      ‖φ t₀ - m.point‖ < m.basinRadius → ∀ t ∈ Icc t₀ t₁,
        ‖φ t - m.point‖ ≤ m.basinOvershoot * Real.exp (-m.basinRate * (t - t₀)) *
          ‖φ t₀ - m.point‖ := by
  set g := m.g with hgdef
  set f := g.unitFilter.field with hfdef
  set s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![m.δ, 0] with hs₀
  have hs₀0 : s₀ 0 = m.δ := rfl
  have hs₀1 : s₀ 1 = 0 := rfl
  have hpt : g.graph s₀ = m.point := by
    simp [graph, Model.point, hs₀0, hs₀1, ← hgdef, hbal]
  have hω0 : 0 < ωc := m.basinFilterRate_pos.trans hω
  -- the field with rate `ω_c` is the `ε`-system with `ε = 1/ω_c`
  have hfield : ({ m.g with ωc := ωc } : VSMLPF).field =
      SingularPerturbation.splitScaledField split ωc⁻¹ f := by
    funext x
    exact field_eq_splitScaledField { m.g with ωc := ωc } x
  have hfc : ContDiff ℝ 1 f := g.unitFilter.contDiff_field
  have heq : f (g.graph s₀) = 0 := by
    rw [hpt]
    refine state3_ext ?_ ?_ ?_ <;> simp [hfdef, unitFilter, Model.point, ← hgdef]
    rw [← hbal]; ring
  have hslow : ∀ s k, g.graph s (split.symm (.inr k)) = s k := g.graph_slow
  have hfast : ∀ s i, f (g.graph s) (split.symm (.inl i)) = 0 := fun s i => by
    simp [hfdef, graph, unitFilter]
  have hA : ∀ i j : Fin 1, HasDerivAt
      (fun t : ℝ => f (g.graph s₀ + t • EuclideanSpace.single (split.symm (.inl j)) 1)
        (split.symm (.inl i))) ((!![-1] : Matrix (Fin 1) (Fin 1) ℝ) i j) 0 := by
    intro i j
    fin_cases i; fin_cases j
    have hfun : (fun t : ℝ => f (g.graph s₀ + t • EuclideanSpace.single
        (split.symm (.inl (0 : Fin 1))) 1) (split.symm (.inl (0 : Fin 1)))) = fun t => -t := by
      funext t
      simp [hfdef, graph, unitFilter]
    have hA00 : (!![-1] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = -1 := rfl
    simp only [Fin.zero_eta, Fin.isValue]
    rw [hfun, hA00]
    exact (hasDerivAt_id' (0 : ℝ)).neg
  have hR : HasFDerivAt (fun s => (WithLp.toLp 2 fun k => f (g.graph s) (split.symm (.inr k)) :
      EuclideanSpace ℝ (Fin 2))) (Matrix.toEuclideanCLM (𝕜 := ℝ) m.reducedJ) s₀ := by
    rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
    intro k
    rw [hasFDerivWithinAt_univ]
    have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt (x := s₀)
    have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt (x := s₀)
    fin_cases k
    · convert h1 using 1
      · funext y; simp [hfdef, graph, unitFilter]
      · apply ContinuousLinearMap.ext; intro v
        simp [Model.reducedJ, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
    · have hs := (Real.hasDerivAt_sin (s₀ 0)).comp_hasFDerivAt s₀ h0
      have h := (((hasFDerivAt_const g.P0 s₀).sub (hs.const_mul g.K0)).sub
        (h1.const_mul g.D)).const_mul g.M⁻¹
      convert h using 1
      · funext y; simp [hfdef, graph, unitFilter, div_eq_inv_mul]
      · apply ContinuousLinearMap.ext; intro v
        simp [Model.reducedJ, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, Model.K, hs₀0, ← hgdef]
        field_simp
        ring
  -- the bounds
  have hP2s : (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ = !![1 / 2] := by
    ext i j; fin_cases i; fin_cases j; rfl
  have hL2 : (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ) * !![-1] + (!![-1])ᵀ * !![1 / 2] = -1 := by
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; norm_num
  have hlb0 : ∀ x, m.lyapLower * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) m.lyapP x⟫ := by
    intro x
    have h := SingularPerturbation.lower_bound_fin_two (m.lyapP_trace_pos hM hD hK)
      (m.lyapP_det_pos hM hD hK) x
    have hP : m.lyapP = !![m.lyapP 0 0, m.lyapP 0 1; m.lyapP 0 1, m.lyapP 1 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [← hP] at h
    exact h
  have hlb2 : ∀ y : EuclideanSpace ℝ (Fin 1), 1 / 2 * ‖y‖ ^ 2 ≤
      ⟪y, Matrix.toEuclideanCLM (𝕜 := ℝ) (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ) y⟫ := by
    intro y
    rw [Matrix.inner_toEuclideanCLM, EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, Matrix.mulVec]
    nlinarith [sq_nonneg (y 0)]
  have hp2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℝ)‖ ≤ 1 / 2 := by
    refine (SingularPerturbation.norm_toEuclideanCLM_le_absSum _).trans (le_of_eq ?_)
    simp [SingularPerturbation.absSum]
  have hnf : ‖fderiv ℝ f (g.graph s₀)‖ ≤ m.jacBound := by
    rw [hfdef, g.unitFilter.fderiv_field, hpt]
    exact SingularPerturbation.norm_toEuclideanCLM_le_absSum _
  have hnΦ : ‖fderiv ℝ g.graph s₀‖ ≤ 1 + |g.K0| := by
    rw [g.fderiv_graph]; exact g.norm_graphDeriv_le s₀
  have hLf : ∀ u ∈ ball (g.graph s₀) 1, ‖fderiv ℝ f u - fderiv ℝ f (g.graph s₀)‖ ≤
      |g.K0| * ‖u - g.graph s₀‖ := fun u _ => g.norm_fderiv_unitFilter_sub_le u _
  have hLΦ : ∀ s ∈ ball s₀ 1, ‖fderiv ℝ g.graph s - fderiv ℝ g.graph s₀‖ ≤
      |g.K0| * ‖s - s₀‖ := fun s _ => by
    rw [g.fderiv_graph, g.fderiv_graph]; exact g.norm_graphDeriv_sub_le s s₀
  have hcore := SingularPerturbation.uniform_basin_of_lipschitz split hfc g.contDiff_graph heq
    hslow hfast hA hR m.lyapP_symm hP2s (m.lyapP_lyapunov hM hD hK) hL2
    (m.lyapLower_pos hM hD hK) (by norm_num) hlb0 hlb2
    (SingularPerturbation.norm_toEuclideanCLM_le_absSum _) hp2 hnf hnΦ
    (SingularPerturbation.norm_toEuclideanCLM_le_absSum _) (abs_nonneg _) (abs_nonneg _)
    one_pos one_pos hLf hLΦ
  have hε : ωc⁻¹ < SingularPerturbation.basinEpsStarOf (SingularPerturbation.absSum m.lyapP)
      (1 / 2) m.jacBound (1 + |g.K0|) (SingularPerturbation.absSum m.reducedJ) := by
    have hpos := SingularPerturbation.basinEpsStarOf_pos (SingularPerturbation.absSum_nonneg
      m.lyapP) (by norm_num : (0 : ℝ) ≤ 1 / 2) (SingularPerturbation.absSum_nonneg
      (g.unitFilter.jacobian m.δ)) (by positivity : (0 : ℝ) ≤ 1 + |g.K0|)
      (nR := SingularPerturbation.absSum m.reducedJ)
    rw [Model.basinFilterRate] at hω
    exact (inv_lt_comm₀ hω0 hpos).mpr hω
  obtain ⟨hroa, hdec⟩ := hcore ωc⁻¹ (inv_pos.mpr hω0) hε
  rw [hfield, ← hpt]
  exact ⟨hroa, hdec⟩

end VSMLPF

end powerlib.GFM
