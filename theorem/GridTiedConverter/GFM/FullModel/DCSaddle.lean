import theorem.GridTiedConverter.GFM.FullModel.DC
import theorem.GridTiedConverter.GFM.FullModel.Saddle
import theorem.SingularPerturbation.QuasiSteadyGraph

/-! # The 16-state grid-forming converter with a DC link: Jacobian determinant and instability

Model boundary.
The 16-state model of `theorem/GridTiedConverter/GFM/FullModel/DC.lean`: the 13 AC coordinates of
`theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (same order, frames, directions: currents out
of the converter positive, export-positive per-unit power), then `x 13 = v_dc`, `x 14 = ξ_dc`,
`x 15 = v_f`; constant-power DC source, lossless averaged bridge not limited by `v_dc`, DC-voltage
PI on the filtered voltage setting the VSM set-point. Continuous time, autonomous, no input. The
field is `C¹` only where `v_dc ≠ 0` (the row `v̇_dc = (P_dc − P_br)/(C_dc v_dc)`). Level: the
Jacobian determinant at an equilibrium and local instability; no stability statement here (the
time-scale statement is in `theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean`).

Source: GFM counterpart study, full-order model note (t5 (d): the 16-state DC variant) and the
G5 follow-up note "det-sign instability, `det J_red6 = ω_f ω_q K_idc (B_δ(1 + n_q Q_E) −
n_q B_E Q_δ)/(M C_dc v_ref)`" (hand derivation, checked here); Schur determinant identity
(Horn–Johnson, *Matrix Analysis*, §0.8.5); the GFL counterpart
`theorem/GridTiedConverter/GFL/LCLine/FullModelDC.lean`.

Results.
* `splitDC`: the fast phasor coordinates `0 … 9` and the slow ones `(δ, Δω, Q_f, v_dc, ξ_dc, v_f)`;
  `DCParams.graph`: the quasi-steady graph over the slow coordinates (`DCParams.graph_slow`,
  `DCParams.core_graph_qss`; its fast rows vanish, `DCParams.fast_graph`, from
  `DCParams.fastAtRest_iff`), `C¹` (`DCParams.contDiff_graph`); `DCParams.hasDerivAt_fast`: the
  fast block of the 16-state field is the AC fast block `Params.fastBlock`.
* `Params.bridgeSlope`, `Params.bridgeSlopeE`: the partials `B_δ`, `B_E` of the quasi-steady
  bridge power (`Params.hasFDerivAt_PbrQ_comp`, from the single harmonic `Params.PbrQ_eq`).
* `DCParams.reducedField_apply`: the reduced field (the slow rows on the graph) is
  `(Δω, (P_ref(x) − P − DΔω)/M, ω_q (Q − Q_f), (P_dc − P_br)/(C_dc v_dc), v_f − v_ref,
  ω_f (v_dc − v_f))` with the quasi-steady powers at the droop EMF;
  `DCParams.hasFDerivAt_reducedField`: at a point with `P_br = P_dc`, `v_dc ≠ 0` its Jacobian is
  `DCParams.reducedJacobian`; `DCParams.det_reducedJacobian`:
  `det J_red = K_idc ω_f ω_q dcSlope/(M C_dc v_dc)`, `dcSlope = B_δ (1 + n_q Q_E) − n_q B_E Q_δ`
  (`DCParams.dcSlope`; without droop `B_δ`, `DCParams.dcSlope_of_nq_eq_zero`).
* `DCParams.contDiffOn_field`: the 16-state field is `C¹` on `v_dc ≠ 0`.
* Instability (`dcFamily_mem_den_unstable` below): at an equilibrium with
  `K_idc ω_f ω_q dcSlope/(M C_dc v_ref) < 0`, `det J = det fastBlock · det J_red < 0` in the even
  dimension 16 gives a positive real eigenvalue, for every choice of the AC controller gains (the
  generic local law `SingularPerturbation.unstable_of_det_fast_mul_det_reduced`).

Family and connection conclusions.
* `dcFamily : Family DCModel Spectral.Requirement 16 0`: a complete system is a parameter set with
  a selected quasi-steady point (angle, filtered reactive power, DC integrator state; `v_dc = v_f
  = v_ref`), read as the field translated so that the point is the origin
  (`Spectral.localFamily`). Requirements: `stable` — none (`False`); `unstable` —
  `DCModel.Saddle` (nondegenerate fast block, `C_dc, v_ref, ω_f, M, ω_q ≠ 0`, a balanced point,
  negative `det J_red`). `dcFamily_chain_le_semantics` proves every translation sound.
* `dcFamily_mem_den_unstable` (connection): the saddle condition places the model in
  instability, for every AC controller gain; `dcFamily_not_mem_den_locallyExponentiallyStable`
  (connection, boundary included): at a quasi-steady point with `P_br = P_dc` and the
  nondegeneracy conditions, `K_idc ω_f ω_q dcSlope/(M C_dc v_ref) ≤ 0` excludes local exponential
  stability (a Hurwitz Jacobian has `det J > 0` in dimension 16, `det fastBlock > 0`), so the
  sign of the reduced determinant decides all but its positive side. An exact local exponential
  decision for the 16-state model is the Hurwitz condition of its `16 × 16` Jacobian, whose
  Hurwitz determinants are not expanded (size obstruction, as in
  `theorem/GridTiedConverter/GFM/FullModel/BoundaryLayerRouth.lean`); the exact cascade decision
  is made for the five-state dynamic line feeding the DC link,
  `theorem/GridTiedConverter/GFM/DCLink/LineCascade.lean`;
  `dcFamily_mem_den_unstable_of_bridgeSlope_neg` (no droop, `K_idc, ω_f, ω_q, M, C_dc,
  v_ref > 0`): a balanced angle on the descending branch of the quasi-steady bridge power,
  `∂P_br/∂δ < 0`, is unstable.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex ComplexConjugate Matrix
open powerlib.Dynamics (State)

/-- The splitting of the 16 coordinates into the fast phasor coordinates (coordinate `2a + c`)
and the slow ones `(δ, Δω, Q_f, v_dc, ξ_dc, v_f)` (coordinates `10 … 15`). -/
def splitDC : Fin 16 ≃ (Fin 5 × Fin 2) ⊕ Fin 6 :=
  (finSumFinEquiv (m := 10) (n := 6)).symm.trans
    (Equiv.sumCongr (finProdFinEquiv (m := 5) (n := 2)).symm (Equiv.refl (Fin 6)))

/-- The fast coordinates of the 16-state vector are those of its AC core. -/
@[tmio M, powerlib_domain] theorem splitDC_symm_inl (a : Fin 5) (c : Fin 2) :
    splitDC.symm (.inl (a, c)) = Fin.castAdd 3 (split.symm (.inl (a, c))) := by
  fin_cases a <;> fin_cases c <;> rfl

@[tmio M, powerlib_domain] theorem splitDC_symm_inr (k : Fin 6) :
    splitDC.symm (.inr k) = ⟨10 + k.val, by omega⟩ := by
  fin_cases k <;> rfl

@[tmio T, powerlib_foundation] private theorem contDiff_ofReal' {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

attribute [local fun_prop] contDiff_ofReal'

namespace Params

variable (p : Params)

/-- The slope `B_δ = ∂P_br/∂δ` of the quasi-steady bridge power, `E |κ| cos(δ + arg(jκ))`. -/
def bridgeSlope (δ E : ℝ) : ℝ :=
  E * ‖p.bridgeCoeff‖ * Real.cos (δ + Complex.arg (I * p.bridgeCoeff))

/-- The slope `B_E = ∂P_br/∂E` of the quasi-steady bridge power,
`2E Re(μα*) + |κ| sin(δ + arg(jκ))`. -/
def bridgeSlopeE (δ E : ℝ) : ℝ :=
  2 * E * (p.bridgeMu * conj p.currentAl).re +
    ‖p.bridgeCoeff‖ * Real.sin (δ + Complex.arg (I * p.bridgeCoeff))

/-- The quasi-steady bridge power along two `C¹` coordinates `δ = u`, `E = w`: partials
`∂P_br/∂δ = bridgeSlope`, `∂P_br/∂E = bridgeSlopeE`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_PbrQ_comp (hZt : p.Zt ≠ 0) {n : ℕ}
    {u w : State n → ℝ} {u' w' : State n →L[ℝ] ℝ} {y : State n} (hu : HasFDerivAt u u' y)
    (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun z => p.PbrQ (u z) (w z))
      (p.bridgeSlope (u y) (w y) • u' + p.bridgeSlopeE (u y) (w y) • w') y := by
  set φ := Complex.arg (I * p.bridgeCoeff)
  set a := (p.bridgeMu * conj p.currentAl).re
  set b := (p.bridgeNu * conj p.currentBe).re
  have hf : (fun z => p.PbrQ (u z) (w z)) = fun z => w z * w z * a + b +
      w z * ‖p.bridgeCoeff‖ * Real.sin (u z + φ) := by
    funext z; rw [p.PbrQ_eq hZt, bridgeOffset]; ring
  rw [hf]
  have hs := (Real.hasDerivAt_sin (u y + φ)).comp_hasFDerivAt y (hu.add_const φ)
  have h := (((hw.fun_mul hw).mul_const a).add_const b).add
    ((hw.mul_const ‖p.bridgeCoeff‖).fun_mul hs)
  refine h.congr_fderiv ?_
  ext v
  simp [bridgeSlope, bridgeSlopeE, a, φ]
  ring

end Params

namespace DCParams

variable (q : DCParams)

/-- The quasi-steady graph
`(δ, Δω, Q_f, v_dc, ξ_dc, v_f) ↦ (qssState δ Δω Q_f, v_dc, ξ_dc, v_f)`. -/
def graph (s : State 6) : State 16 := join (q.qssState (s 0) (s 1) (s 2)) (s 3) (s 4) (s 5)

@[tmio M, powerlib_domain] theorem graph_castAdd (s : State 6) (j : Fin 13) :
    q.graph s (Fin.castAdd 3 j) = q.qssState (s 0) (s 1) (s 2) j :=
  Fin.append_left _ _ _

@[tmio M, powerlib_domain] theorem graph_natAdd (s : State 6) (k : Fin 3) :
    q.graph s (Fin.natAdd 13 k) = ![s 3, s 4, s 5] k :=
  Fin.append_right _ _ _

@[tmio M, powerlib_domain] theorem core_graph (s : State 6) :
    core (q.graph s) = q.qssState (s 0) (s 1) (s 2) := core_join _ _ _ _

@[tmio M, powerlib_domain] theorem graph_10 (s : State 6) : q.graph s 10 = s 0 :=
  q.graph_castAdd s 10
@[tmio M, powerlib_domain] theorem graph_11 (s : State 6) : q.graph s 11 = s 1 :=
  q.graph_castAdd s 11
@[tmio M, powerlib_domain] theorem graph_12 (s : State 6) : q.graph s 12 = s 2 :=
  q.graph_castAdd s 12
@[tmio M, powerlib_domain] theorem graph_13 (s : State 6) : q.graph s 13 = s 3 :=
  q.graph_natAdd s 0
@[tmio M, powerlib_domain] theorem graph_14 (s : State 6) : q.graph s 14 = s 4 :=
  q.graph_natAdd s 1
@[tmio M, powerlib_domain] theorem graph_15 (s : State 6) : q.graph s 15 = s 5 :=
  q.graph_natAdd s 2

/-- The AC core of a graph point is the quasi-steady state at its own slow coordinates. -/
@[tmio M, powerlib_domain] theorem core_graph_qss (s : State 6) :
    core (q.graph s) = q.qssState (q.graph s 10) (q.graph s 11) (q.graph s 12) := by
  rw [core_graph, graph_10, graph_11, graph_12]

/-- The slow coordinates of the graph are its base point. -/
@[tmio M, powerlib_domain] theorem graph_slow (s : State 6) (k : Fin 6) :
    q.graph s (splitDC.symm (.inr k)) = s k := by
  fin_cases k
  · exact q.graph_10 s
  · exact q.graph_11 s
  · exact q.graph_12 s
  · exact q.graph_13 s
  · exact q.graph_14 s
  · exact q.graph_15 s

@[tmio M, powerlib_domain] private theorem contDiff_mk3 :
    ContDiff ℝ 1 fun s : State 6 => Dynamics.mk3 (s 0) (s 1) (s 2) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [Dynamics.mk3] <;> exact Dynamics.contDiff_coord _

/-- The quasi-steady graph is `C¹`. -/
@[tmio M, powerlib_domain] theorem contDiff_graph : ContDiff ℝ 1 q.graph := by
  have hg := q.toParams.contDiff_graph.comp (contDiff_mk3)
  rw [contDiff_euclidean] at hg ⊢
  intro i
  refine Fin.addCases (m := 13) (n := 3) (fun j => ?_) (fun k => ?_) i
  · simp only [graph_castAdd]
    simpa [Params.graph, Function.comp_def] using hg j
  · simp only [graph_natAdd]
    fin_cases k <;> simp <;> exact Dynamics.contDiff_coord _

/-- The fast rows of the 16-state field vanish on the graph. -/
@[tmio M, powerlib_domain] theorem fast_graph (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0) (hLg : q.Lg ≠ 0)
    (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (s : State 6) (i : Fin 5 × Fin 2) :
    q.field (q.graph s) (splitDC.symm (.inl i)) = 0 := by
  obtain ⟨a, c⟩ := i
  refine (q.fastAtRest_iff hLf hCf hLg hKic hKiv hZt _).mpr (q.core_graph_qss s) _ ?_
  rw [splitDC_symm_inl, split_symm_inl]
  simp only [Fin.val_castAdd]
  omega

@[tmio M, powerlib_domain] private theorem core_add_single (x : State 16) (t : ℝ) (k : Fin 13) :
    core (x + t • EuclideanSpace.single (Fin.castAdd 3 k) 1) =
      core x + t • EuclideanSpace.single k 1 := by
  ext i
  by_cases h : i = k
  · subst h; simp [core]
  · simp [core, PiLp.single_apply, h, (Fin.castAdd_injective 13 3).ne h]

/-- The fast–fast partial derivatives of the 16-state field are the AC fast block at its angle. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_fast (x : State 16) (i j : Fin 5 × Fin 2) :
    HasDerivAt (fun t : ℝ => q.field (x + t • EuclideanSpace.single (splitDC.symm (.inl j)) 1)
      (splitDC.symm (.inl i))) (q.fastBlock (x 10) i j) 0 := by
  obtain ⟨a, c⟩ := i
  obtain ⟨b, d⟩ := j
  have hne : split.symm (.inl (a, c)) ≠ 11 := by
    rw [split_symm_inl]; intro h; have := congrArg Fin.val h; simp at this; omega
  have hf : (fun t : ℝ => q.field (x + t • EuclideanSpace.single (splitDC.symm (.inl (b, d))) 1)
      (splitDC.symm (.inl (a, c)))) = fun t => q.toParams.field
        (core x + t • EuclideanSpace.single (split.symm (.inl (b, d))) 1)
          (split.symm (.inl (a, c))) := by
    funext t
    rw [splitDC_symm_inl, splitDC_symm_inl, q.field_fast _ _ hne, core_add_single]
  rw [hf]
  exact q.toParams.hasDerivAt_fast (core x) (a, c) (b, d)

/-- The reduced field: the slow rows of the 16-state field on the graph. -/
def reducedField (s : State 6) : State 6 :=
  WithLp.toLp 2 fun k => q.field (q.graph s) (splitDC.symm (.inr k))

/-- The reduced field is `(Δω, (P_ref + K_pdc (v_f − v_ref) + K_idc ξ_dc − P − DΔω)/M,
ω_q (Q − Q_f), (P_dc − P_br)/(C_dc v_dc), v_f − v_ref, ω_f (v_dc − v_f))`, with the quasi-steady
powers at `(δ, E₀ − n_q (Q_f − Q_ref))`. -/
@[tmio M, powerlib_domain] theorem reducedField_apply (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0)
    (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (s : State 6) :
    q.reducedField s = WithLp.toLp 2 ![s 1,
      (q.Pref + q.Kpdc * (s 5 - q.vref) + q.Kidc * s 4 - q.Pq (s 0) (q.emf (s 2)) - q.D * s 1) /
        q.M, q.ωq * (q.Qq (s 0) (q.emf (s 2)) - s 2),
      (q.Pdc - q.PbrQ (s 0) (q.emf (s 2))) / (q.Cdc * s 3), s 5 - q.vref,
      q.ωf * (s 3 - s 5)] := by
  have hq := q.core_graph_qss s
  ext k
  simp only [reducedField, PiLp.toLp_apply]
  fin_cases k
  · change q.field (q.graph s) (Fin.castAdd 3 10) = s 1
    rw [q.field_fast _ _ (by decide)]
    exact q.graph_11 s
  · change q.field (q.graph s) 11 = _
    rw [q.field_11, core_graph, Params.Pe_qssState, powerRef]
    change (q.Pref + q.Kpdc * (q.graph s 15 - q.vref) + q.Kidc * q.graph s 14 -
      q.Pq (s 0) (q.emf (s 2)) - q.D * q.graph s 11) / q.M = _
    rw [graph_15, graph_14, graph_11]
    rfl
  · change q.field (q.graph s) (Fin.castAdd 3 12) = _
    rw [q.field_fast _ _ (by decide)]
    change q.ωq * (Qe (core (q.graph s)) - core (q.graph s) 12) = _
    rw [core_graph, Params.Qe_qssState]
    rfl
  · change q.field (q.graph s) 13 = _
    rw [q.field_13, q.Pbr_eq_PbrQ hLf hCf hLg hKic hKiv hZt _ hq, graph_10, graph_12, graph_13]
    rfl
  · change q.field (q.graph s) 14 = _
    rw [q.field_14, graph_15]
    rfl
  · change q.field (q.graph s) 15 = _
    rw [q.field_15, graph_13, graph_15]
    rfl

/-- The Jacobian of the reduced field at `(δ, ·, Q_f, v_dc, ·, ·)` on the balance `P_br = P_dc`
(all slopes at `(δ, E)`, `E = E₀ − n_q (Q_f − Q_ref)`), order `(δ, Δω, Q_f, v_dc, ξ_dc, v_f)`. -/
def reducedJacobian (δ Qf vdc : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 0;
    -q.powerSlope δ (q.emf Qf) / q.M, -q.D / q.M, q.nq * q.powerSlopeE δ (q.emf Qf) / q.M, 0,
      q.Kidc / q.M, q.Kpdc / q.M;
    q.ωq * q.reactiveSlope δ (q.emf Qf), 0,
      -(q.ωq * (1 + q.nq * q.reactiveSlopeE δ (q.emf Qf))), 0, 0, 0;
    -q.bridgeSlope δ (q.emf Qf) / (q.Cdc * vdc), 0,
      q.nq * q.bridgeSlopeE δ (q.emf Qf) / (q.Cdc * vdc), 0, 0, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, q.ωf, 0, -q.ωf]

/-- The droop-corrected bridge slope `B_δ (1 + n_q Q_E) − n_q B_E Q_δ` at `(δ, E(Q_f))`. -/
def dcSlope (δ Qf : ℝ) : ℝ :=
  q.bridgeSlope δ (q.emf Qf) * (1 + q.nq * q.reactiveSlopeE δ (q.emf Qf)) -
    q.nq * q.bridgeSlopeE δ (q.emf Qf) * q.reactiveSlope δ (q.emf Qf)

@[tmio M, powerlib_domain] theorem dcSlope_of_nq_eq_zero (hnq : q.nq = 0) (δ Qf : ℝ) :
    q.dcSlope δ Qf = q.bridgeSlope δ q.E0 := by
  simp [dcSlope, Params.emf, hnq]

@[tmio T, powerlib_foundation] private theorem det_six (a10 a11 a12 a14 a15 a20 a22 a30 a32 w : ℝ) :
    (!![0, 1, 0, 0, 0, 0; a10, a11, a12, 0, a14, a15; a20, 0, a22, 0, 0, 0;
      a30, 0, a32, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, w, 0, -w] : Matrix (Fin 6) (Fin 6) ℝ).det =
      -(w * a14 * (a20 * a32 - a22 * a30)) := by
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- `det J_red = K_idc ω_f ω_q dcSlope/(M C_dc v_dc)`. -/
@[tmio M, powerlib_domain] theorem det_reducedJacobian (δ Qf vdc : ℝ) :
    (q.reducedJacobian δ Qf vdc).det =
      q.Kidc * q.ωf * q.ωq * q.dcSlope δ Qf / (q.M * (q.Cdc * vdc)) := by
  rw [reducedJacobian, det_six, dcSlope]
  ring

@[tmio T, powerlib_foundation] private theorem hasFDerivAt_proj6 (k : Fin 6) (y : State 6) :
    HasFDerivAt (fun z : State 6 => z k)
      (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k : State 6 →L[ℝ] ℝ) y :=
  (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k : State 6 →L[ℝ] ℝ).hasFDerivAt

/-- The reduced field has the Jacobian `reducedJacobian` at every point with `v_dc ≠ 0` on the
bridge balance `P_br = P_dc`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_reducedField (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0)
    (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (hCdc : q.Cdc ≠ 0)
    (y : State 6) (hy : y 3 ≠ 0) (hB : q.PbrQ (y 0) (q.emf (y 2)) = q.Pdc) :
    HasFDerivAt q.reducedField
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) (q.reducedJacobian (y 0) (y 2) (y 3))) y := by
  have hf := funext (q.reducedField_apply hLf hCf hLg hKic hKiv hZt)
  rw [hf, ← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have he : HasFDerivAt (fun z : State 6 => q.emf (z 2))
      (-(q.nq • (PiLp.proj 2 (fun _ : Fin 6 => ℝ) (2 : Fin 6) : State 6 →L[ℝ] ℝ))) y :=
    (((hasFDerivAt_proj6 2 y).add_const (-q.Qref)).const_mul q.nq).const_sub q.E0
      |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => by simp [Params.emf, sub_eq_add_neg])
  have hP := q.toParams.hasFDerivAt_Pq_comp hZt (hasFDerivAt_proj6 0 y) he
  have hQ := q.toParams.hasFDerivAt_Qq_comp hZt (hasFDerivAt_proj6 0 y) he
  have hBr := q.toParams.hasFDerivAt_PbrQ_comp hZt (hasFDerivAt_proj6 0 y) he
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    convert hasFDerivAt_proj6 1 y using 1
    apply ContinuousLinearMap.ext; intro v
    simp [reducedJacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_six]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    have h := ((((((hasFDerivAt_const q.Pref y).add (((hasFDerivAt_proj6 5 y).sub_const
      q.vref).const_mul q.Kpdc)).add ((hasFDerivAt_proj6 4 y).const_mul q.Kidc)).sub hP).sub
        ((hasFDerivAt_proj6 1 y).const_mul q.D)).mul_const q.M⁻¹)
    convert h using 1
    · funext z; simp [div_eq_mul_inv]
    · apply ContinuousLinearMap.ext; intro v
      simp [reducedJacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_six]
      ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    have h := (hQ.sub (hasFDerivAt_proj6 2 y)).const_mul q.ωq
    convert h using 1
    · funext z; simp
    · apply ContinuousLinearMap.ext; intro v
      simp [reducedJacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_six]
      ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    have hd : HasFDerivAt (fun z : State 6 => q.Cdc * z 3)
        (q.Cdc • (PiLp.proj 2 (fun _ : Fin 6 => ℝ) (3 : Fin 6) : State 6 →L[ℝ] ℝ)) y :=
      (hasFDerivAt_proj6 3 y).const_mul q.Cdc |>.congr_fderiv (by ext v; simp)
    have hne : q.Cdc * y 3 ≠ 0 := mul_ne_zero hCdc hy
    have hinv := (hasDerivAt_inv hne).comp_hasFDerivAt y hd
    have h := ((hasFDerivAt_const q.Pdc y).sub hBr).fun_mul hinv
    convert h using 1
    · funext z; simp [div_eq_mul_inv]
    · apply ContinuousLinearMap.ext; intro v
      simp [reducedJacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_six]
      field_simp
      rw [hB]
      ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    have h := (hasFDerivAt_proj6 5 y).sub_const q.vref
    convert h using 1
    · funext z; simp
    apply ContinuousLinearMap.ext; intro v
    simp [reducedJacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_six]
  · simp only [Fin.reduceFinMk, Fin.isValue]
    have h := ((hasFDerivAt_proj6 3 y).sub (hasFDerivAt_proj6 5 y)).const_mul q.ωf
    convert h using 1
    · funext z; simp
    · apply ContinuousLinearMap.ext; intro v
      simp [reducedJacobian, Dynamics.toEuclideanCLM_apply, Fin.sum_univ_six]
      ring

@[tmio M, powerlib_domain] private theorem contDiff_core :
    ContDiff ℝ 1 (core : State 16 → State 13) := by
  rw [contDiff_euclidean]
  intro i
  exact Dynamics.contDiff_coord _

@[tmio T, powerlib_foundation] private theorem contDiff_re16 {f : State 16 → ℂ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun x => (f x).re :=
  Complex.reCLM.contDiff.comp hf

@[tmio T, powerlib_foundation] private theorem contDiff_im16 {f : State 16 → ℂ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun x => (f x).im :=
  Complex.imCLM.contDiff.comp hf

@[tmio M, powerlib_domain] private theorem Pbr_eq_re_im (x : State 16) :
    q.Pbr x = (q.uBridge (core x)).re * (convCurrent (core x)).re +
      (q.uBridge (core x)).im * (convCurrent (core x)).im := by
  simp [Pbr, Complex.mul_re]

/-- The 16-state field is `C¹` on the open set `v_dc ≠ 0`. -/
@[tmio M, powerlib_domain] theorem contDiffOn_field (hCdc : q.Cdc ≠ 0) :
    ContDiffOn ℝ 1 q.field {x | x 13 ≠ 0} := by
  have hAC := (contDiff_euclidean.mp (q.toParams.contDiff_field.comp contDiff_core))
  have hu : ContDiff ℝ 1 fun x : State 16 => q.uBridge (core x) := by
    unfold Params.uBridge Params.uCtrl Params.iRef Params.vRef Params.emf ej
    simp only [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor, core,
      PiLp.toLp_apply]
    fun_prop
  have hi : ContDiff ℝ 1 fun x : State 16 => convCurrent (core x) := by
    simp only [convCurrent, phasor, core, PiLp.toLp_apply]
    fun_prop
  have hPbr : ContDiff ℝ 1 q.Pbr := by
    have h := ((contDiff_re16 hu).mul (contDiff_re16 hi)).add
      ((contDiff_im16 hu).mul (contDiff_im16 hi))
    have he : q.Pbr = fun x => (q.uBridge (core x)).re * (convCurrent (core x)).re +
        (q.uBridge (core x)).im * (convCurrent (core x)).im := funext q.Pbr_eq_re_im
    rw [he]
    exact h
  rw [contDiffOn_euclidean]
  intro i
  refine Fin.addCases (m := 13) (n := 3) (fun j => ?_) (fun k => ?_) i
  · by_cases hj : j = 11
    · subst hj
      have h : ContDiff ℝ 1 fun x : State 16 =>
          (q.powerRef x - Pe (core x) - q.D * x 11) / q.M := by
        simp only [powerRef, Pe, Transform.pq, core, PiLp.toLp_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        fun_prop
      refine h.contDiffOn.congr fun x _ => ?_
      exact (q.field_11 x)
    · refine (hAC j).contDiffOn.congr fun x _ => ?_
      exact q.field_fast x j hj
  · fin_cases k
    · have h : ContDiffOn ℝ 1 (fun x : State 16 => (q.Pdc - q.Pbr x) / (q.Cdc * x 13))
          {x | x 13 ≠ 0} :=
        (contDiff_const.sub hPbr).contDiffOn.div
          (contDiff_const.mul (Dynamics.contDiff_coord 13)).contDiffOn
          fun x hx => mul_ne_zero hCdc hx
      exact h.congr fun x _ => q.field_13 x
    · exact ((Dynamics.contDiff_coord 15).sub contDiff_const).contDiffOn.congr fun x _ =>
        q.field_14 x
    · exact (contDiff_const.mul ((Dynamics.contDiff_coord 13).sub
        (Dynamics.contDiff_coord 15))).contDiffOn.congr fun x _ => q.field_15 x

/-- The slow coordinates `(δ, 0, Q_f, v_ref, ξ_dc, v_ref)` of an equilibrium candidate. -/
def slowPoint (δ Qf ξ : ℝ) : State 6 := WithLp.toLp 2 ![δ, 0, Qf, q.vref, ξ, q.vref]

/-- **Determinant-sign instability of the DC variant**, for every choice of the AC controller
gains and with or without droop: at a quasi-steady equilibrium (`P = P_ref + K_idc ξ_dc`,
`Q = Q_f`, `P_br = P_dc`, `v_dc = v_f = v_ref`) with
`K_idc ω_f ω_q dcSlope/(M C_dc v_ref) < 0`, the Jacobian has
`det J = det fastBlock · det J_red < 0` in dimension 16, hence a positive real eigenvalue. -/
@[tmio TM, powerlib_domain] private theorem unstable_of_dcSlope (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0)
    (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (hM : q.M ≠ 0)
    (hωq : q.ωq ≠ 0) (hCdc : q.Cdc ≠ 0) (hvref : q.vref ≠ 0) (hωf : q.ωf ≠ 0) {δ Qf ξ : ℝ}
    (hP : q.Pq δ (q.emf Qf) = q.Pref + q.Kidc * ξ) (hQ : q.Qq δ (q.emf Qf) = Qf)
    (hB : q.PbrQ δ (q.emf Qf) = q.Pdc)
    (hs : q.Kidc * q.ωf * q.ωq * q.dcSlope δ Qf / (q.M * (q.Cdc * q.vref)) < 0) :
    Unstable q.field (q.graph (q.slowPoint δ Qf ξ)) := by
  set s₀ := q.slowPoint δ Qf ξ
  have hs0 : s₀ 0 = δ ∧ s₀ 1 = 0 ∧ s₀ 2 = Qf ∧ s₀ 3 = q.vref ∧ s₀ 4 = ξ ∧ s₀ 5 = q.vref := by
    simp [s₀, slowPoint]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hs0
  have hcore : core (q.graph s₀) = q.qssState δ 0 Qf := by rw [core_graph, h0, h1, h2]
  have hx13 : q.graph s₀ 13 = q.vref := by rw [graph_13, h3]
  have hx14 : q.graph s₀ 14 = ξ := by rw [graph_14, h4]
  have hx15 : q.graph s₀ 15 = q.vref := by rw [graph_15, h5]
  have hx10 : q.graph s₀ 10 = δ := by rw [graph_10, h0]
  have heq : q.field (q.graph s₀) = 0 :=
    (q.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq hCdc hvref hωf _).mpr
      ⟨δ, Qf, hcore, hx13, hx15, by rw [hx14]; exact hP, hQ, hB⟩
  have hU : IsOpen {x : State 16 | x 13 ≠ 0} :=
    isOpen_ne_fun (Dynamics.contDiff_coord (k := 1) 13).continuous continuous_const
  have hR := q.hasFDerivAt_reducedField hLf hCf hLg hKic hKiv hZt hCdc s₀
    (by rw [h3]; exact hvref) (by rw [h0, h2]; exact hB)
  rw [h0, h2, h3] at hR
  refine SingularPerturbation.unstable_of_det_fast_mul_det_reduced (A := q.fastBlock δ) splitDC hU
    (show q.graph s₀ 13 ≠ 0 by rw [hx13]; exact hvref) (q.contDiffOn_field hCdc) heq
    ((q.contDiff_graph).differentiable (by norm_num) _) q.graph_slow
    (q.fast_graph hLf hCf hLg hKic hKiv hZt) (fun i j => ?_) hR ?_
  · have := q.hasDerivAt_fast (q.graph s₀) i j
    rwa [hx10] at this
  · rw [q.det_reducedJacobian]
    have hA := q.toParams.det_fastBlock_pos hLf hCf hLg hKic hKiv hZt δ
    norm_num
    exact mul_neg_of_pos_of_neg hA hs

/-- A Hurwitz real matrix has `(−1)^N det > 0`: the constant coefficient of its characteristic
polynomial, `(−1)^N det`, is positive (`Criteria.charpoly_coeff_pos_of_isHurwitz`). -/
@[tmio T, powerlib_foundation] private theorem neg_one_pow_mul_det_pos {N : ℕ}
    {J : Matrix (Fin N) (Fin N) ℝ} (h : LinearSystems.IsHurwitz J) : 0 < (-1) ^ N * J.det := by
  have hc := Criteria.charpoly_coeff_pos_of_isHurwitz h (Nat.zero_le N)
  rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul]
  simpa using hc

/-- **The reduced determinant sign is necessary, boundary included.** At a quasi-steady point
with `P_br = P_dc` (the data of `unstable_of_dcSlope`), local exponential stability forces a
Hurwitz Jacobian (converse linearization, the field being `C¹` on `v_dc ≠ 0`), hence `det J > 0`
in dimension 16, and `det J = det fastBlock · det J_red` with `det fastBlock > 0`: so
`K_idc ω_f ω_q dcSlope/(M C_dc v_ref) > 0`. A nonpositive reduced determinant excludes local
exponential stability, for every AC controller gain. -/
@[tmio TM, powerlib_domain] private theorem not_les_of_dcSlope_nonpos (hLf : q.Lf ≠ 0)
    (hCf : q.Cf ≠ 0) (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0)
    (hCdc : q.Cdc ≠ 0) (hvref : q.vref ≠ 0) {δ Qf ξ : ℝ} (hB : q.PbrQ δ (q.emf Qf) = q.Pdc)
    (hs : q.Kidc * q.ωf * q.ωq * q.dcSlope δ Qf / (q.M * (q.Cdc * q.vref)) ≤ 0) :
    ¬ LocallyExponentiallyStable q.field (q.graph (q.slowPoint δ Qf ξ)) := by
  intro hles
  set s₀ := q.slowPoint δ Qf ξ
  have hs0 : s₀ 0 = δ ∧ s₀ 1 = 0 ∧ s₀ 2 = Qf ∧ s₀ 3 = q.vref ∧ s₀ 4 = ξ ∧ s₀ 5 = q.vref := by
    simp [s₀, slowPoint]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hs0
  have hx13 : q.graph s₀ 13 = q.vref := by rw [graph_13, h3]
  have hx10 : q.graph s₀ 10 = δ := by rw [graph_10, h0]
  have hU : IsOpen {x : State 16 | x 13 ≠ 0} :=
    isOpen_ne_fun (Dynamics.contDiff_coord (k := 1) 13).continuous continuous_const
  have hxU : q.graph s₀ ∈ {x : State 16 | x 13 ≠ 0} := by
    show q.graph s₀ 13 ≠ 0
    rw [hx13]; exact hvref
  have hdiff : DifferentiableAt ℝ q.field (q.graph s₀) :=
    ((q.contDiffOn_field hCdc).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
  set J := (Matrix.toEuclideanCLM (n := Fin 16) (𝕜 := ℝ)).symm (fderiv ℝ q.field (q.graph s₀))
    with hJdef
  have hJac : fderiv ℝ q.field (q.graph s₀) = Matrix.toEuclideanCLM (n := Fin 16) (𝕜 := ℝ) J :=
    by simp [J]
  have hJ : HasFDerivAt q.field (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (q.graph s₀) := by
    rw [← hJac]; exact hdiff.hasFDerivAt
  have hH := Dynamics.isHurwitz_of_locallyExponentiallyStable_local hU hxU J
    (q.contDiffOn_field hCdc) hJac hles
  have hR := q.hasFDerivAt_reducedField hLf hCf hLg hKic hKiv hZt hCdc s₀
    (by rw [h3]; exact hvref) (by rw [h0, h2]; exact hB)
  rw [h0, h2, h3] at hR
  have hdetJ := LinearAlgebra.det_eq_det_fast_mul_det_reduced (A := q.fastBlock δ) splitDC hJ
    ((q.contDiff_graph).differentiable (by norm_num) _) q.graph_slow
    (q.fast_graph hLf hCf hLg hKic hKiv hZt) (fun i j => by
      have := q.hasDerivAt_fast (q.graph s₀) i j
      rwa [hx10] at this) hR
  have hpos := neg_one_pow_mul_det_pos hH
  rw [hdetJ, q.det_reducedJacobian] at hpos
  have hA := q.toParams.det_fastBlock_pos hLf hCf hLg hKic hKiv hZt δ
  norm_num at hpos
  nlinarith [mul_nonpos_iff.mpr (Or.inl ⟨hA.le, hs⟩)]

end DCParams

/-! ## The family of the DC variant -/

/-- A DC-variant model read about a selected quasi-steady point: angle `δ*`, filtered reactive
power `Q*` and DC integrator state `ξ*`, with `v_dc = v_f = v_ref`. -/
structure DCModel where
  /-- The parameters. -/
  q : DCParams
  /-- The selected angle `δ*`. -/
  δ : ℝ
  /-- The selected filtered reactive power `Q*`. -/
  Qf : ℝ
  /-- The selected DC-voltage integrator state `ξ*`. -/
  ξ : ℝ

/-- The selected point `(qssState δ* 0 Q*, v_ref, ξ*, v_ref)`. -/
def DCModel.point (m : DCModel) : State 16 := m.q.graph (m.q.slowPoint m.δ m.Qf m.ξ)

/-- The 16-state field translated so that the selected point is the origin. -/
def DCModel.field (m : DCModel) (z : State 16) : State 16 := m.q.field (z + m.point)

/-- The saddle condition of the DC variant: nondegenerate fast block, `M, ω_q, C_dc, v_ref, ω_f ≠
0`, a balanced point and a negative reduced determinant `K_idc ω_f ω_q dcSlope/(M C_dc v_ref)`. -/
def DCModel.Saddle (m : DCModel) : Prop :=
  m.q.Lf ≠ 0 ∧ m.q.Cf ≠ 0 ∧ m.q.Lg ≠ 0 ∧ m.q.Kic ≠ 0 ∧ m.q.Kiv ≠ 0 ∧ m.q.Zt ≠ 0 ∧ m.q.M ≠ 0 ∧
    m.q.ωq ≠ 0 ∧ m.q.Cdc ≠ 0 ∧ m.q.vref ≠ 0 ∧ m.q.ωf ≠ 0 ∧
    m.q.Pq m.δ (m.q.emf m.Qf) = m.q.Pref + m.q.Kidc * m.ξ ∧ m.q.Qq m.δ (m.q.emf m.Qf) = m.Qf ∧
    m.q.PbrQ m.δ (m.q.emf m.Qf) = m.q.Pdc ∧
    m.q.Kidc * m.q.ωf * m.q.ωq * m.q.dcSlope m.δ m.Qf / (m.q.M * (m.q.Cdc * m.q.vref)) < 0

/-- The DC-variant family: no stability requirement (`False`), instability through the saddle
condition. -/
def dcFamily : Family DCModel Spectral.Requirement 16 0 :=
  Spectral.localFamily DCModel.field (fun _ => False) DCModel.Saddle

@[tmio TM, powerlib_domain] private theorem dc_mem_den_flow {m : DCModel} {P : Flow.Property} :
    m ∈ dcFamily.den (.flow P) ↔ P.holds m.q.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : DCModel => m.q.field) (pt := DCModel.point)
    (Spectral.localFamily_isAutonomous _ _ _)

@[tmio TM, powerlib_domain] private theorem dc_unstable_of_saddle {m : DCModel}
    (h : m.Saddle) : connection% (m ∈ dcFamily.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨hLf, hCf, hLg, hKic, hKiv, hZt, hM, hωq, hCdc, hvref, hωf, hP, hQ, hB, hs⟩ := h
  exact dc_mem_den_flow.mpr
    (m.q.unstable_of_dcSlope hLf hCf hLg hKic hKiv hZt hM hωq hCdc hvref hωf hP hQ hB hs)

/-- Every translation of the DC-variant family is sound: no model meets the (absent) stability
requirement, and the saddle condition proves instability. -/
@[tmio TM, powerlib_domain] theorem dcFamily_chain_le_semantics :
    connection% (∀ P, dcFamily.chain P ≤ dcFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m h => h.elim) (fun m h => ?_)
  exact (Flow.Property.holds_shift_iff .unstable).mpr (dc_mem_den_flow.mp (dc_unstable_of_saddle h))

/-- The DC variant at a balanced quasi-steady point with a negative reduced determinant
`K_idc ω_f ω_q dcSlope/(M C_dc v_ref) < 0` is unstable, for every choice of the AC controller
gains and of the droop gain: `det J = det fastBlock · det J_red < 0` in dimension 16. -/
@[tmio TM, powerlib_domain] theorem dcFamily_mem_den_unstable (m : DCModel) (h : m.Saddle) :
    connection% (m ∈ dcFamily.den (.flow .unstable)) :=
  dc_unstable_of_saddle h

/-- **Local exponential stability needs a positive reduced determinant** (boundary included):
at a quasi-steady point with `P_br = P_dc` and the nondegeneracy conditions of `DCModel.Saddle`, a
nonpositive `K_idc ω_f ω_q dcSlope/(M C_dc v_ref)` excludes local exponential stability, for every
AC controller gain and droop gain (`det J = det fastBlock · det J_red`, `det fastBlock > 0`, and a
Hurwitz Jacobian has `det J > 0` in dimension 16). With `dcFamily_mem_den_unstable` the sign of the
reduced determinant decides everything except its positive side. -/
@[tmio TM, powerlib_domain] theorem dcFamily_not_mem_den_locallyExponentiallyStable
    (m : DCModel) (hLf : m.q.Lf ≠ 0) (hCf : m.q.Cf ≠ 0) (hLg : m.q.Lg ≠ 0) (hKic : m.q.Kic ≠ 0)
    (hKiv : m.q.Kiv ≠ 0) (hZt : m.q.Zt ≠ 0) (hCdc : m.q.Cdc ≠ 0) (hvref : m.q.vref ≠ 0)
    (hB : m.q.PbrQ m.δ (m.q.emf m.Qf) = m.q.Pdc)
    (hs : m.q.Kidc * m.q.ωf * m.q.ωq * m.q.dcSlope m.δ m.Qf / (m.q.M * (m.q.Cdc * m.q.vref)) ≤ 0) :
    connection% (m ∉ dcFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro hm
  exact m.q.not_les_of_dcSlope_nonpos hLf hCf hLg hKic hKiv hZt hCdc hvref hB hs
    (dc_mem_den_flow.mp hm)

/-- Without droop and with `K_idc, ω_f, ω_q, M, C_dc, v_ref > 0`, a balanced angle on the
descending branch of the quasi-steady bridge power, `∂P_br/∂δ (δ*, E₀) < 0`
(`Params.bridgeSlope`), is an unstable equilibrium of the DC variant, for every AC controller
gain. -/
@[tmio TM, powerlib_domain] theorem dcFamily_mem_den_unstable_of_bridgeSlope_neg (m : DCModel)
    (hLf : m.q.Lf ≠ 0) (hCf : m.q.Cf ≠ 0) (hLg : m.q.Lg ≠ 0) (hKic : m.q.Kic ≠ 0)
    (hKiv : m.q.Kiv ≠ 0) (hZt : m.q.Zt ≠ 0) (hnq : m.q.nq = 0) (hM : 0 < m.q.M)
    (hωq : 0 < m.q.ωq) (hCdc : 0 < m.q.Cdc) (hvref : 0 < m.q.vref) (hωf : 0 < m.q.ωf)
    (hKidc : 0 < m.q.Kidc) (hP : m.q.Pq m.δ m.q.E0 = m.q.Pref + m.q.Kidc * m.ξ)
    (hQ : m.q.Qq m.δ m.q.E0 = m.Qf) (hB : m.q.PbrQ m.δ m.q.E0 = m.q.Pdc)
    (hs : m.q.bridgeSlope m.δ m.q.E0 < 0) :
    connection% (m ∈ dcFamily.den (.flow .unstable)) := by
  have hE : m.q.emf m.Qf = m.q.E0 := by simp [Params.emf, hnq]
  refine dc_unstable_of_saddle ⟨hLf, hCf, hLg, hKic, hKiv, hZt, hM.ne', hωq.ne', hCdc.ne',
    hvref.ne', hωf.ne', by rw [hE]; exact hP, by rw [hE]; exact hQ, by rw [hE]; exact hB, ?_⟩
  rw [m.q.dcSlope_of_nq_eq_zero hnq]
  have h1 : 0 < m.q.Kidc * m.q.ωf * m.q.ωq := by positivity
  have h2 : 0 < m.q.M * (m.q.Cdc * m.q.vref) := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 hs) h2

end powerlib.GFM.FullModel
