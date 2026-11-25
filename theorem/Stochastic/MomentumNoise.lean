import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ControlApprox

/-! # The quasi-potential of the rate for noise in the momentum row

A planar mechanical system `q̇ = c p`, `ṗ = f(q, p) + σ u` (state `(q, p)`, one noise column
`(0, σ)`, `σ ≠ 0`): the Freidlin–Wentzell rate (`fwRate`) admits square-integrable controls, the
controlled quasi-potential (`controlQuasiPotential` of `theorem/Stochastic/ControlledAction.lean`)
only controls along which the path has a right derivative everywhere. They give the same
quasi-potential, for every pair of endpoints: a square-integrable control is replaced by a
right-continuous one (`exists_rc_approx`) whose momentum derivative `ṗ` has the same first two
moments, so both endpoints are kept exactly (`p(T) = p(0) + ∫₀ᵀ ṗ`,
`q(T) = q(0) + c (T p(0) + ∫₀ᵀ ∫₀ᵗ ṗ)`), and the action changes by at most `η`. The noise is
degenerate (one column in two dimensions); the controllability of `q̇ = c p`, `ṗ = σ u` through
the noise row replaces ellipticity.

Scope.
* Generic: `b : ℝ² → ℝ²` globally Lipschitz with `b(x)₀ = c x₁` (any `c`), noise column
  `(0, σ)`, `σ ≠ 0`; deterministic statements on the rate.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §1–3 (quasi-potential of the action functional; degenerate noise in mechanical systems,
Ch. 4 §3 remarks); the flatness of `q̇ = c p`, `ṗ = σ u` (the two endpoint conditions are the two
moments of `ṗ`).

Results.
* `columnsCLM_momentum`, `leftInverse_momentum` (the noise map of `(0, σ)` and its left inverse).
* `controlQuasiPotential_le_controlAction_planar` (**regularisation keeping both endpoints**):
  for `w = ∫ u`, `u` square integrable, `V(x_A, x(T)) ≤ ½ ∫₀ᵀ u²`, `x = solMap w`.
* `controlQuasiPotential_le_fwRate_planar`: `V(x_A, φ(T)) ≤ J_T(φ)` for every path `φ`.
* `fwQP_eq_controlQuasiPotential_planar` (**the quasi-potential of the rate is the controlled
  quasi-potential**): `inf_T inf {J_T(φ) : φ(T) = x} = V(x_A, x)` for all `x_A`, `x`.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {T : ℝ≥0}

/-- The noise map of the column `(0, σ)`. -/
@[tmio T, powerlib_foundation] theorem columnsCLM_momentum (σ : ℝ) (z : Fin 1 → ℝ) :
    columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ]) z = ![0, σ * z 0] := by
  rw [columnsCLM_apply]
  ext i
  fin_cases i <;> simp [mul_comm]

/-- **Regularisation keeping both endpoints** (planar mechanical system, noise in the momentum
row): for `w = ∫ u` with `u` square integrable, the controlled quasi-potential from `x_A` to the
endpoint of `x = solMap w` is at most `½ ∫₀ᵀ u²`. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le_controlAction_planar
    {K : ℝ≥0} {b : (Fin 2 → ℝ) → Fin 2 → ℝ} (hb : LipschitzWith K b) {c : ℝ}
    (hb0 : ∀ y, b y 0 = c * y 1) {σ : ℝ} (hσ : σ ≠ 0) (xA : Fin 2 → ℝ) {u : ℝ → Fin 1 → ℝ}
    (hu : IntervalIntegrable u volume 0 T)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T)
    {w : C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hw : ∀ t : Icc (0 : ℝ) T, w t = ∫ s in (0 : ℝ)..t, u s) :
    controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ]) xA
        (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ]) xA w
          ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩) ≤
      ENNReal.ofReal (controlAction u T) := by
  have hT0 := T.coe_nonneg
  rcases eq_or_lt_of_le hT0 with hT | hT
  · -- `T = 0`: the endpoint is `x_A`
    have hend : solMap b (columnsCLM fun _ : Fin 1 => ![0, σ]) xA w
        ⟨T, right_mem_Icc.mpr hT0⟩ = xA := by
      rw [solMap_spec hb, hw]
      simp [← hT]
    rw [hend]
    have h0 : controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ]) xA xA ≤ 0 := by
      unfold controlQuasiPotential
      refine iInf_le_of_le 0 (iInf_le_of_le (fun _ => xA) (iInf_le_of_le (fun _ _ => 0)
        (iInf_le_of_le ⟨le_rfl, rfl, rfl, continuousOn_const,
          fun t ht => absurd ht.2 (not_lt.mpr ht.1), by simp⟩ ?_)))
      simp [controlAction]
    exact h0.trans zero_le
  -- the solution as an integral equation
  have hint : ∀ t ∈ Icc (0 : ℝ) T,
      pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ]) xA w) t =
        xA + ∫ s in (0 : ℝ)..t, (columnsCLM (fun _ : Fin 1 => ![0, σ]) (u s) +
          b (pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ]) xA w) s)) :=
    fun t ht => pathExt_solMap_of_primitive hb _ xA hu hw ht
  have hΦc := continuous_pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ]) xA w)
  rw [← pathExt_of_mem (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ]) xA w)
    (right_mem_Icc.mpr hT0)]
  generalize pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ]) xA w) = Φ at hint hΦc ⊢
  have hbΦ : Continuous fun s => b (Φ s) := hb.continuous.comp hΦc
  have hb1 : Continuous fun s => b (Φ s) 1 := (continuous_apply 1).comp hbΦ
  have hIcc : uIcc (0 : ℝ) T = Icc (0 : ℝ) T := uIcc_of_le hT0
  -- the control component and the momentum derivative `v = σ u + b(Φ)₁`
  have hu0i : IntervalIntegrable (fun s => u s 0) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mp hu))
  have hsq1 : ∀ z : ℝ → Fin 1 → ℝ, (fun s => ∑ j, z s j ^ 2) = fun s => z s 0 ^ 2 :=
    fun z => by funext s; simp
  have hu02 : IntervalIntegrable (fun s => u s 0 ^ 2) volume 0 T := by rw [← hsq1]; exact hu2
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ, ∀ s, v s = σ * u s 0 + b (Φ s) 1 := ⟨_, fun s => rfl⟩
  have hvfun : v = fun s => σ * u s 0 + b (Φ s) 1 := funext hv
  have hvi : IntervalIntegrable v volume 0 T := by
    rw [hvfun]; exact (hu0i.const_mul σ).add (hb1.intervalIntegrable 0 T)
  have hv2 : IntervalIntegrable (fun s => v s ^ 2) volume 0 T := by
    have e : (fun s => v s ^ 2) = fun s =>
        σ ^ 2 * u s 0 ^ 2 + 2 * σ * (u s 0 * b (Φ s) 1) + b (Φ s) 1 ^ 2 := by
      funext s; rw [hv]; ring
    rw [e]
    exact ((hu02.const_mul _).add ((hu0i.mul_continuousOn hb1.continuousOn).const_mul _)).add
      ((hb1.pow 2).intervalIntegrable 0 T)
  -- the components of the solution
  have hi : ∀ i, ∀ t ∈ Icc (0 : ℝ) T, Φ t i = xA i + ∫ s in (0 : ℝ)..t,
      (columnsCLM (fun _ : Fin 1 => ![0, σ]) (u s) i + b (Φ s) i) := by
    intro i t ht
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1, hIcc]; exact Icc_subset_Icc_right ht.2
    have hNu : IntervalIntegrable (fun r => columnsCLM (fun _ : Fin 1 => ![0, σ]) (u r))
        volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
        ((columnsCLM _).integrable_comp
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp (hu.mono_set hsub)))
    have hF := hNu.add (hbΦ.intervalIntegrable 0 t)
    have hc := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ)
      i).intervalIntegral_comp_comm hF
    simp only [ContinuousLinearMap.proj_apply] at hc
    rw [hint t ht, Pi.add_apply, ← hc]
    rfl
  have h0t : ∀ t ∈ Icc (0 : ℝ) T, Φ t 0 = xA 0 + ∫ s in (0 : ℝ)..t, c * Φ s 1 := by
    intro t ht
    rw [hi 0 t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [columnsCLM_momentum, hb0]
  have h1t : ∀ t ∈ Icc (0 : ℝ) T, Φ t 1 = xA 1 + ∫ s in (0 : ℝ)..t, v s := by
    intro t ht
    rw [hi 1 t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [columnsCLM_momentum, hv]
  -- the tolerance
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set η : ℝ := (ε : ℝ) with hηdef
  have hη : 0 < η := hε
  set A := ∫ s in (0 : ℝ)..T, u s 0 ^ 2 with hA
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hT0 fun s _ => sq_nonneg _
  set C₀ : ℝ := 2 * (K : ℝ) ^ 2 * (c ^ 2 * T ^ 3 + T) with hC₀
  set C₁ : ℝ := 2 * (1 + T * C₀) / σ ^ 2 with hC₁
  set θ : ℝ := η / (A + 1) with hθ
  have hθ0 : 0 < θ := by positivity
  set C₂ : ℝ := (1 + 1 / θ) * C₁ with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set ε₀ : ℝ := η / (C₂ + 1) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  obtain ⟨g, hgm, hgrc, hgi, hg2, hm1, hm2, hgv2, hgv⟩ := exists_rc_approx hT hvi hv2 hε₀0
  -- the regularised path `(q̃, p̃)` and control `ũ`
  obtain ⟨p, hp⟩ : ∃ p : ℝ → ℝ, ∀ t, p t = xA 1 + ∫ s in (0 : ℝ)..t, g s := ⟨_, fun t => rfl⟩
  have hpc : Continuous p := by
    rw [funext hp]; exact continuous_const.add (intervalIntegral.continuous_primitive hgi 0)
  have hcp : Continuous fun s => c * p s := continuous_const.mul hpc
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, ∀ t, q t = xA 0 + ∫ s in (0 : ℝ)..t, c * p s :=
    ⟨_, fun t => rfl⟩
  have hqc : Continuous q := by
    rw [funext hq]; exact continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => hcp.intervalIntegrable a b) 0)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → Fin 2 → ℝ, ∀ t, φ t = ![q t, p t] := ⟨_, fun t => rfl⟩
  have hφc : Continuous φ := by
    rw [funext hφ]
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using hqc
    · simpa using hpc
  have hbφ1 : Continuous fun s => b (φ s) 1 := (continuous_apply 1).comp (hb.continuous.comp hφc)
  obtain ⟨ũ, hũ⟩ : ∃ ũ : ℝ → Fin 1 → ℝ, ∀ t, ũ t = fun _ => (g t - b (φ t) 1) / σ :=
    ⟨_, fun t => rfl⟩
  have hũ0 : ∀ t, ũ t 0 = (g t - b (φ t) 1) / σ := fun t => by rw [hũ]
  -- the controlled field along the regularised path
  have hcf : ∀ t, controlField b (fun _ (_ : Fin 1) => ![0, σ]) (φ t) (ũ t) = ![c * p t, g t] := by
    intro t
    ext i
    fin_cases i
    · simp [controlField, hb0, hφ]
    · simp [controlField, hũ0]
      field_simp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ
      (controlField b (fun _ (_ : Fin 1) => ![0, σ]) (φ t) (ũ t)) (Ici t) t := by
    intro t _
    rw [hcf]
    refine hasDerivWithinAt_pi.mpr fun i => ?_
    have hpd : HasDerivWithinAt p (g t) (Ici t) t := by
      rw [funext hp]
      exact (intervalIntegral.integral_hasDerivWithinAt_right (hgi 0 t)
        hgm.aestronglyMeasurable.stronglyMeasurableAtFilter (hgrc t)).const_add (xA 1)
    have hqd : HasDerivAt q (c * p t) t := by
      rw [funext hq]
      exact ((hcp.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (xA 0)
    fin_cases i
    · simpa [hφ] using hqd.hasDerivWithinAt
    · simpa [hφ] using hpd
  have hũ2 : IntervalIntegrable (fun t => ∑ j, ũ t j ^ 2) volume 0 T := by
    rw [hsq1]
    have e : (fun t => ũ t 0 ^ 2) = fun t =>
        (g t ^ 2 - 2 * (g t * b (φ t) 1) + b (φ t) 1 ^ 2) / σ ^ 2 := by
      funext t; rw [hũ0]; field_simp; ring
    rw [e]
    exact (((hg2 0 T).sub (((hgi 0 T).mul_continuousOn hbφ1.continuousOn).const_mul 2)).add
      ((hbφ1.pow 2).intervalIntegrable 0 T)).div_const _
  -- both endpoints are kept
  have hTmem : (T : ℝ) ∈ Icc (0 : ℝ) T := right_mem_Icc.mpr hT0
  have hP : ∫ s in (0 : ℝ)..T, p s = ∫ s in (0 : ℝ)..T, Φ s 1 := by
    have hVc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (uIcc 0 T) :=
      intervalIntegral.continuousOn_primitive_interval' hvi left_mem_uIcc
    have e1 : ∫ s in (0 : ℝ)..T, Φ s 1 = ∫ s in (0 : ℝ)..T, (xA 1 + ∫ r in (0 : ℝ)..s, v r) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [hIcc] at hs
      exact h1t s hs
    rw [e1, funext hp, intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegral.continuous_primitive hgi 0).intervalIntegrable 0 T),
      intervalIntegral.integral_add intervalIntegrable_const hVc.intervalIntegrable, hm2]
  have hend : φ T = Φ T := by
    ext i
    fin_cases i
    · simp only [hφ, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hq, h0t T hTmem, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hP]
    · simp only [hφ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hp, h1t T hTmem, hm1]
  have hstart : φ 0 = xA := by
    ext i
    fin_cases i
    · simp [hφ, hq]
    · simp [hφ, hp]
  have hQP : controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ]) xA (Φ T) ≤
      ENNReal.ofReal (controlAction ũ T) := by
    unfold controlQuasiPotential
    exact iInf_le_of_le (T : ℝ) (iInf_le_of_le φ (iInf_le_of_le ũ (iInf_le_of_le
      ⟨hT0, hstart, hend, hφc.continuousOn, hderiv, hũ2⟩ le_rfl)))
  -- the action estimate
  have hũ0i : IntervalIntegrable (fun t => ũ t 0 ^ 2) volume 0 T := by rw [← hsq1]; exact hũ2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ∀ s, ψ s = b (φ s) 1 - b (Φ s) 1 := ⟨_, fun s => rfl⟩
  have hψc : Continuous ψ := by rw [funext hψ]; exact hbφ1.sub hb1
  have hdiff : ∀ s, ũ s 0 - u s 0 = ((g s - v s) - ψ s) / σ := by
    intro s; rw [hũ0, hψ, hv]; field_simp; ring
  have hΦ1c : Continuous fun s => Φ s 1 := (continuous_apply 1).comp hΦc
  have hpΦc : Continuous fun s => p s - Φ s 1 := hpc.sub hΦ1c
  have hpb : ∀ s ∈ Icc (0 : ℝ) T, (p s - Φ s 1) ^ 2 ≤ T * ε₀ := by
    intro s hs
    rw [hp, h1t s hs, add_sub_add_left_eq_sub]
    exact (sq_integral_sub_le (hgi 0 T) hvi hgv2 hs).trans (mul_le_mul_of_nonneg_left hgv hT0)
  have hint2 : ∫ s in (0 : ℝ)..T, (p s - Φ s 1) ^ 2 ≤ T * (T * ε₀) := by
    calc _ ≤ ∫ s in (0 : ℝ)..T, (T * ε₀) :=
          intervalIntegral.integral_mono_on hT0 ((hpΦc.pow 2).intervalIntegrable 0 T)
            intervalIntegrable_const hpb
      _ = T * (T * ε₀) := by simp
  have hqb : ∀ s ∈ Icc (0 : ℝ) T, (q s - Φ s 0) ^ 2 ≤ c ^ 2 * T ^ 3 * ε₀ := by
    intro s hs
    rw [hq, h0t s hs, add_sub_add_left_eq_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ← mul_sub, mul_pow]
    have h := sq_integral_sub_le (T := T) (f₁ := p) (f₂ := fun s => Φ s 1)
      (hpc.intervalIntegrable 0 T) (hΦ1c.intervalIntegrable 0 T)
      ((hpΦc.pow 2).intervalIntegrable 0 T) hs
    have e : c ^ 2 * T ^ 3 * ε₀ = c ^ 2 * (T * (T * (T * ε₀))) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hint2 hT0))
      (sq_nonneg c)
  have hψb : ∀ s ∈ Icc (0 : ℝ) T, ψ s ^ 2 ≤ C₀ * ε₀ := by
    intro s hs
    have h1 : |ψ s| ≤ K * ‖φ s - Φ s‖ := by
      rw [hψ]
      have h0 := hb.norm_sub_le (φ s) (Φ s)
      have h2 : ‖(b (φ s) - b (Φ s)) 1‖ ≤ ‖b (φ s) - b (Φ s)‖ := norm_le_pi_norm _ 1
      rw [Pi.sub_apply, Real.norm_eq_abs] at h2
      linarith
    have h3 : ‖φ s - Φ s‖ ≤ |q s - Φ s 0| + |p s - Φ s 1| := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      fin_cases i
      · simp [hφ]
      · simp [hφ]
    have h4 : |ψ s| ≤ K * (|q s - Φ s 0| + |p s - Φ s 1|) :=
      h1.trans (mul_le_mul_of_nonneg_left h3 K.coe_nonneg)
    have h5 : ψ s ^ 2 ≤ (K : ℝ) ^ 2 * (|q s - Φ s 0| + |p s - Φ s 1|) ^ 2 := by
      rw [← sq_abs (ψ s), ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h4 2
    have h6 : (|q s - Φ s 0| + |p s - Φ s 1|) ^ 2 ≤
        2 * ((q s - Φ s 0) ^ 2 + (p s - Φ s 1) ^ 2) := by
      nlinarith [sq_abs (q s - Φ s 0), sq_abs (p s - Φ s 1),
        sq_nonneg (|q s - Φ s 0| - |p s - Φ s 1|)]
    have h7 := hqb s hs
    have h8 := hpb s hs
    calc ψ s ^ 2 ≤ (K : ℝ) ^ 2 * (2 * ((q s - Φ s 0) ^ 2 + (p s - Φ s 1) ^ 2)) :=
          h5.trans (mul_le_mul_of_nonneg_left h6 (sq_nonneg _))
      _ ≤ (K : ℝ) ^ 2 * (2 * (c ^ 2 * T ^ 3 * ε₀ + T * ε₀)) := by gcongr
      _ = C₀ * ε₀ := by rw [hC₀]; ring
  have hgvψ : IntervalIntegrable (fun s => (g s - v s) * ψ s) volume 0 T :=
    ((hgi 0 T).sub hvi).mul_continuousOn hψc.continuousOn
  have hd2 : IntervalIntegrable (fun s => (ũ s 0 - u s 0) ^ 2) volume 0 T := by
    have e : (fun s => (ũ s 0 - u s 0) ^ 2) = fun s =>
        ((g s - v s) ^ 2 - 2 * ((g s - v s) * ψ s) + ψ s ^ 2) / σ ^ 2 := by
      funext s; rw [hdiff]; field_simp; ring
    rw [e]
    exact ((hgv2.sub (hgvψ.const_mul 2)).add ((hψc.pow 2).intervalIntegrable 0 T)).div_const _
  have hd : ∫ s in (0 : ℝ)..T, (ũ s 0 - u s 0) ^ 2 ≤ C₁ * ε₀ := by
    calc ∫ s in (0 : ℝ)..T, (ũ s 0 - u s 0) ^ 2
        ≤ ∫ s in (0 : ℝ)..T, 2 / σ ^ 2 * ((g s - v s) ^ 2 + C₀ * ε₀) := by
          refine intervalIntegral.integral_mono_on hT0 hd2
            ((hgv2.add intervalIntegrable_const).const_mul _) fun s hs => ?_
          have h1 := hψb s hs
          rw [hdiff, div_pow,
            show 2 / σ ^ 2 * ((g s - v s) ^ 2 + C₀ * ε₀) =
              (2 * ((g s - v s) ^ 2 + C₀ * ε₀)) / σ ^ 2 by ring]
          exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (g s - v s + ψ s)])
            (sq_nonneg σ)
      _ = 2 / σ ^ 2 * ((∫ s in (0 : ℝ)..T, (g s - v s) ^ 2) + T * (C₀ * ε₀)) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add hgv2 intervalIntegrable_const,
            intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      _ ≤ 2 / σ ^ 2 * (ε₀ + T * (C₀ * ε₀)) := by gcongr
      _ = C₁ * ε₀ := by rw [hC₁]; ring
  have hY := integral_sq_le_add hT0 hũ0i hu02 hd2 hθ0
  rw [← hA] at hY
  have hfin : ∫ s in (0 : ℝ)..T, ũ s 0 ^ 2 ≤ A + 2 * η := by
    have h1 : θ * A ≤ η := by
      have hA1 : A / (A + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      calc θ * A = η * (A / (A + 1)) := by simp only [hθ]; ring
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left hA1 hη.le
        _ = η := mul_one η
    have h2 : (1 + 1 / θ) * (∫ s in (0 : ℝ)..T, (ũ s 0 - u s 0) ^ 2) ≤ η := by
      have hC1 : C₂ / (C₂ + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      calc _ ≤ (1 + 1 / θ) * (C₁ * ε₀) := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = η * (C₂ / (C₂ + 1)) := by simp only [hC₂, hε₀]; ring
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left hC1 hη.le
        _ = η := mul_one η
    linarith
  have hcaũ : controlAction ũ T = 1 / 2 * ∫ s in (0 : ℝ)..T, ũ s 0 ^ 2 := by
    unfold controlAction; rw [hsq1]
  have hcau : controlAction u T = 1 / 2 * A := by
    unfold controlAction; rw [hsq1]
  calc _ ≤ ENNReal.ofReal (controlAction ũ T) := hQP
    _ ≤ ENNReal.ofReal (controlAction u T + η) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcaũ, hcau]; linarith
    _ = ENNReal.ofReal (controlAction u T) + ε := by
        rw [ENNReal.ofReal_add (by rw [hcau]; positivity) hη.le, hηdef,
          ENNReal.ofReal_coe_nnreal]

/-- The noise row is recovered from the column `(0, σ)`: `L x = x₁/σ`. -/
@[tmio T, powerlib_foundation] theorem leftInverse_momentum {σ : ℝ} (hσ : σ ≠ 0) :
    ∃ L : (Fin 2 → ℝ) →L[ℝ] Fin 1 → ℝ,
      ∀ v, L (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ]) v) = v := by
  refine ⟨ContinuousLinearMap.pi fun _ => σ⁻¹ • ContinuousLinearMap.proj 1, fun v => ?_⟩
  ext j
  fin_cases j
  simp [columnsCLM_momentum]
  field_simp

/-- **The controlled quasi-potential is below the rate** (planar mechanical system, noise in the
momentum row): `V(x_A, φ(T)) ≤ J_T(φ)` for every path `φ` on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le_fwRate_planar {K : ℝ≥0}
    {b : (Fin 2 → ℝ) → Fin 2 → ℝ} (hb : LipschitzWith K b) {c : ℝ}
    (hb0 : ∀ y, b y 0 = c * y 1) {σ : ℝ} (hσ : σ ≠ 0) (xA : Fin 2 → ℝ)
    (φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ)) :
    controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ]) xA
        (φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩) ≤
      fwRate b (fun _ : Fin 1 => ![0, σ]) xA T φ := by
  unfold fwRate pushRate
  refine le_iInf₂ fun w hw => ?_
  subst hw
  unfold schilderRate
  refine le_iInf₂ fun u hu => ?_
  exact controlQuasiPotential_le_controlAction_planar hb hb0 hσ xA hu.1 hu.2.1 hu.2.2

/-- **The quasi-potential of the rate is the controlled quasi-potential** (planar mechanical
system, noise in the momentum row): `inf_T inf {J_T(φ) : φ(T) = x} = V(x_A, x)` for all
endpoints. -/
@[tmio T, powerlib_foundation] theorem fwQP_eq_controlQuasiPotential_planar {K : ℝ≥0}
    {b : (Fin 2 → ℝ) → Fin 2 → ℝ} (hb : LipschitzWith K b) {c : ℝ}
    (hb0 : ∀ y, b y 0 = c * y 1) {σ : ℝ} (hσ : σ ≠ 0) (xA x : Fin 2 → ℝ) :
    ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate b (fun _ : Fin 1 => ![0, σ]) xA T φ =
      controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ]) xA x := by
  refine le_antisymm ?_ (le_iInf fun T => le_iInf fun φ => le_iInf fun hφ => by
    subst hφ; exact controlQuasiPotential_le_fwRate_planar hb hb0 hσ xA φ)
  obtain ⟨L, hL⟩ := leftInverse_momentum hσ
  unfold controlQuasiPotential
  refine le_iInf fun T' => le_iInf fun φ => le_iInf fun u => le_iInf fun hadm => ?_
  obtain ⟨hT, h0, hTx, hc, hφ, hu⟩ := hadm
  let y : C(Icc (0 : ℝ) (⟨T', hT⟩ : ℝ≥0), Fin 2 → ℝ) := ⟨_, hc.domRestrict⟩
  refine iInf_le_of_le ⟨T', hT⟩ (iInf_le_of_le y (iInf_le_of_le hTx ?_))
  exact fwRate_le_controlAction (T := ⟨T', hT⟩) hb _ h0 hc hφ
    (intervalIntegrable_of_admissible hb _ hL hc hφ hu) hu fun t => rfl

end powerlib.Stochastic.LDP
