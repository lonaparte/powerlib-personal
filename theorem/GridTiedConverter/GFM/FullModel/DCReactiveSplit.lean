import theorem.GridTiedConverter.GFM.FullModel.TimeScale
import theorem.Criteria.Hurwitz

/-! # The 16-state converter with a DC link: the one-way coupling of the reactive-power filter

Model boundary.
The 16-state model of `theorem/GridTiedConverter/GFM/FullModel/DC.lean` (state order, frames and
directions of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean`: currents out of the converter
positive, export-positive per-unit power; `x 12 = Q_f`, `x 13 = v_dc`, `x 14 = ξ_dc`,
`x 15 = v_f`) without Q–V droop, `n_q = 0`, every other parameter value; states with
`v_dc ≠ 0` (where the field is `C¹`). Continuous time, autonomous, no input. Level: the Jacobian
at a state, its characteristic determinant and local exponential stability of the family
`dcFamily` of `theorem/GridTiedConverter/GFM/FullModel/DCSaddle.lean`.

Source: GFM counterpart study, full-order model note (t5 (d): the 16-state DC variant); without
droop the filtered reactive power `Q_f` drives no other state (the EMF is `E₀`), so the field is
exactly affine along `Q_f` and the Jacobian has the column `−ω_q e_{Q_f}` (a one-way coupling:
`Q_f` is driven by the AC states and drives nothing); the determinant of a block triangular
matrix. Sizes of the remaining factor (exact computer algebra, discovery evidence, not
formalized): degree 15; with all parameters and the operating point symbolic (25 symbols, ideal
design) its division-free (Berkowitz) expansion does not complete within 6.5 GB; with the plant and
operating point of the witness of `theorem/GridTiedConverter/GFM/FullModel/DCWitness.lean` fixed
and the controller gains `K_pc, K_ic, K_pv, K_iv, M, D, K_pdc, K_idc, ω_f` (and `E₀`) symbolic,
its coefficients have 1 to 74 terms; its fifteen Hurwitz determinants are not expanded.

Results.
* `Params.uBridge_add_twelve`, `Params.field_add_single_twelve` (13 states) and
  **`DCParams.field_add_single_twelve`** (16 states, `n_q = 0`): `f(x + t e_{Q_f}) = f(x) −
  ω_q t e_{Q_f}` for every state and every `t`.
* `DCParams.jacobian_col_twelve`: at every state with `v_dc ≠ 0` the `Q_f` column of the Jacobian
  `DCParams.jacobian` is `−ω_q e_{Q_f}`; `DCParams.jacobianNoQf`: the Jacobian on the fifteen other
  coordinates; **`DCParams.det_characteristicMatrix_jacobian_of_nq`**: `det(s − J) = (s + ω_q)
  det(s − J₁₅)`; `DCParams.isHurwitz_jacobian_iff_of_nq`: `J` is Hurwitz iff `ω_q > 0` and `J₁₅`
  is spectrally stable.

Family and connection conclusions.
* `dcFamily_mem_den_locallyExponentiallyStable_iff_of_nq` (connection, family `dcFamily`): without
  droop, the DC variant read about its selected point is locally exponentially stable iff the
  point is an equilibrium, `ω_q > 0`, and the Jacobian on the fifteen coordinates other than
  `Q_f` is spectrally stable: the exact local decision of the 16-state model reduces to a
  fifteen-state matrix, the reactive-power filter being decided by the sign of `ω_q`. The
  remaining degree-15 condition is not expanded (sizes above).
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex Matrix
open powerlib.Dynamics (State)

namespace Params

variable (p : Params)

@[tmio M, powerlib_domain] private theorem shift_apply (x : State 13) (t : ℝ) (i : Fin 13) :
    (x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) i = x i + if i = 12 then t else 0 := by
  by_cases h : i = 12
  · subst h; simp
  · simp [h]

@[tmio M, powerlib_domain] private theorem phasors_add_twelve (x : State 13) (t : ℝ) :
    convCurrent (x + t • EuclideanSpace.single 12 1) = convCurrent x ∧
      capVoltage (x + t • EuclideanSpace.single 12 1) = capVoltage x ∧
      lineCurrent (x + t • EuclideanSpace.single 12 1) = lineCurrent x ∧
      currentInt (x + t • EuclideanSpace.single 12 1) = currentInt x ∧
      voltageInt (x + t • EuclideanSpace.single 12 1) = voltageInt x ∧
      (x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) 10 = x 10 ∧
      (x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) 11 = x 11 ∧
      (x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) 12 = x 12 + t := by
  simp only [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor, shift_apply]
  norm_num

/-- Without droop the bridge voltage does not depend on `Q_f`. -/
@[tmio M, powerlib_domain] theorem uBridge_add_twelve (hnq : p.nq = 0) (x : State 13) (t : ℝ) :
    p.uBridge (x + t • EuclideanSpace.single 12 1) = p.uBridge x := by
  obtain ⟨h0, h1, h2, h3, h4, h10, -, h12⟩ := phasors_add_twelve x t
  have hE : p.emf ((x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) 12) = p.emf (x 12) := by
    simp [emf, hnq]
  simp only [uBridge, uCtrl, iRef, vRef, hE, h0, h1, h2, h3, h4, h10]

/-- Without droop the 13-state field is affine along `Q_f`: `f(x + t e_{Q_f}) = f(x) − ω_q t
e_{Q_f}`. -/
@[tmio M, powerlib_domain] theorem field_add_single_twelve (hnq : p.nq = 0) (x : State 13)
    (t : ℝ) :
    p.field (x + t • EuclideanSpace.single 12 1) =
      p.field x - (p.ωq * t) • EuclideanSpace.single 12 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h10, h11, h12⟩ := phasors_add_twelve x t
  have hE : p.emf ((x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) 12) = p.emf (x 12) := by
    simp [emf, hnq]
  have hb := p.uBridge_add_twelve hnq x t
  have hv : p.vRef (x + t • EuclideanSpace.single 12 1) = p.vRef x := by
    simp only [vRef, hE, h10, h2]
  have hi : p.iRef (x + t • EuclideanSpace.single 12 1) = p.iRef x := by
    simp only [iRef, hv, h10, h1, h2, h4]
  have hPe : Pe (x + t • EuclideanSpace.single 12 1) = Pe x := by
    simp only [Pe, shift_apply]; norm_num
  have hQe : Qe (x + t • EuclideanSpace.single 12 1) = Qe x := by
    simp only [Qe, shift_apply]; norm_num
  ext i
  fin_cases i <;>
    simp [Params.field, convRow, capRow, lineRow, currentIntRow, voltageIntRow, hb, hi, hv, h0, h1,
      h2, h10, h11, h12, hPe, hQe]
  ring

end Params

namespace DCParams

variable (q : DCParams)

@[tmio M, powerlib_domain] private theorem core_add_twelve (x : State 16) (t : ℝ) :
    core (x + t • EuclideanSpace.single (12 : Fin 16) (1 : ℝ)) =
      core x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ) := by
  ext i
  simp only [core, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  by_cases h : i = 12
  · subst h; simp
  · have h' : Fin.castAdd 3 i ≠ 12 := fun e => h (Fin.ext (by simpa [Fin.ext_iff] using e))
    simp [h, h']

@[tmio M, powerlib_domain] private theorem coord_add_twelve (x : State 16) (t : ℝ) (k : Fin 16)
    (hk : k ≠ 12) : (x + t • EuclideanSpace.single (12 : Fin 16) (1 : ℝ)) k = x k := by
  simp [hk]

/-- **Without droop the 16-state field is affine along `Q_f`**: `f(x + t e_{Q_f}) = f(x) −
ω_q t e_{Q_f}` for every state and every `t` (the one-way coupling of the reactive-power filter). -/
@[tmio M, powerlib_domain] theorem field_add_single_twelve (hnq : q.nq = 0) (x : State 16)
    (t : ℝ) :
    q.field (x + t • EuclideanSpace.single 12 1) =
      q.field x - (q.ωq * t) • EuclideanSpace.single 12 1 := by
  have hc := core_add_twelve x t
  have hAC := q.toParams.field_add_single_twelve hnq (core x) t
  have hPbr : q.Pbr (x + t • EuclideanSpace.single 12 1) = q.Pbr x := by
    obtain ⟨h0, -⟩ := Params.phasors_add_twelve (core x) t
    simp only [Pbr, hc, q.toParams.uBridge_add_twelve hnq, h0]
  have hPe : Pe (core (x + t • EuclideanSpace.single 12 1)) = Pe (core x) := by
    rw [hc]; simp only [Pe, Params.shift_apply]; norm_num
  have h11 := coord_add_twelve x t 11 (by decide)
  have h13 := coord_add_twelve x t 13 (by decide)
  have h14 := coord_add_twelve x t 14 (by decide)
  have h15 := coord_add_twelve x t 15 (by decide)
  ext i
  refine Fin.addCases (m := 13) (n := 3) (fun j => ?_) (fun k => ?_) i
  · rw [PiLp.sub_apply, PiLp.smul_apply, q.field_castAdd, q.field_castAdd]
    by_cases hj : j = 11
    · subst hj
      simp only [Function.update_self, powerRef, h11, h14, h15, hPe,
        PiLp.single_apply]
      simp [Fin.ext_iff]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, hc, hAC]
      simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
      congr 2
      by_cases h12 : j = 12
      · subst h12; simp
      · have h' : Fin.castAdd 3 j ≠ 12 := fun e => h12 (Fin.ext (by simpa [Fin.ext_iff] using e))
        simp [h12, h']
  · rw [PiLp.sub_apply, PiLp.smul_apply, q.field_natAdd, q.field_natAdd]
    fin_cases k <;> simp [hPbr, h13, h15]

/-- **The `Q_f` column of the Jacobian without droop** (`C_dc ≠ 0`, at every state with
`v_dc ≠ 0`): `J e_{Q_f} = −ω_q e_{Q_f}`. -/
@[tmio M, powerlib_domain] theorem jacobian_col_twelve (hnq : q.nq = 0) (hCdc : q.Cdc ≠ 0)
    {x : State 16} (hx : x 13 ≠ 0) (i : Fin 16) :
    q.jacobian x i 12 = if i = 12 then -q.ωq else 0 := by
  have h := LinearAlgebra.hasDerivAt_line_apply (q.hasFDerivAt_jacobian hCdc hx) i 12
  have h' : HasDerivAt (fun t : ℝ => q.field (x + t • EuclideanSpace.single 12 1) i)
      (if i = 12 then -q.ωq else 0) 0 := by
    simp only [q.field_add_single_twelve hnq, PiLp.sub_apply, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul]
    by_cases hi : i = 12
    · simp only [hi, ite_true, mul_one]
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q.ωq).const_sub (q.field x 12)
    · simp only [hi, ite_false, mul_zero, sub_zero]
      exact hasDerivAt_const _ _
  exact h.unique h'

/-- The Jacobian on the fifteen coordinates other than `Q_f`. -/
def jacobianNoQf (x : State 16) : Matrix {i : Fin 16 // i ≠ 12} {i : Fin 16 // i ≠ 12} ℝ :=
  (q.jacobian x).submatrix Subtype.val Subtype.val

/-- A column `c eₖ` splits the determinant: `det A = A k k · det A'`, `A'` the matrix on the
other indices (block triangular form). -/
@[tmio T, powerlib_foundation] private theorem det_eq_of_col {ι F : Type*} [Fintype ι]
    [DecidableEq ι] [Field F] (A : Matrix ι ι F) (k : ι) (h : ∀ i, i ≠ k → A i k = 0) :
    A.det = A k k * (A.submatrix (Subtype.val : {i // i ≠ k} → ι) Subtype.val).det := by
  let e : {i // i = k} ⊕ {i // i ≠ k} ≃ ι := Equiv.sumCompl (fun i => i = k)
  have : Unique {i // i = k} := ⟨⟨⟨k, rfl⟩⟩, fun ⟨i, hi⟩ => Subtype.ext hi⟩
  have h21 : (reindex e.symm e.symm A).toBlocks₂₁ = 0 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    subst hj
    simpa [e, toBlocks₂₁] using h i hi
  rw [← Matrix.det_reindex_self e.symm A, ← Matrix.fromBlocks_toBlocks (reindex e.symm e.symm A),
    h21, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique]
  congr 1
  rw [show (default : {i // i = k}) = ⟨k, rfl⟩ from Subsingleton.elim _ _]
  rfl

/-- **The characteristic determinant factors without droop** (`C_dc ≠ 0`, `v_dc ≠ 0`):
`det(s − J) = (s + ω_q) det(s − J₁₅)`, `J₁₅` the Jacobian without the `Q_f` row and column. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_jacobian_of_nq (hnq : q.nq = 0)
    (hCdc : q.Cdc ≠ 0) {x : State 16} (hx : x 13 ≠ 0) (s : ℂ) :
    (Linear.characteristicMatrix (q.jacobian x) s).det =
      (s + q.ωq) * (Linear.characteristicMatrix (q.jacobianNoQf x) s).det := by
  have hcol := q.jacobian_col_twelve hnq hCdc hx
  have h1 : Linear.characteristicMatrix (q.jacobian x) s 12 12 = s + q.ωq := by
    simp [Linear.characteristicMatrix, hcol 12]
  have h2 : (Linear.characteristicMatrix (q.jacobian x) s).submatrix
      (Subtype.val : {i : Fin 16 // i ≠ 12} → Fin 16) Subtype.val =
        Linear.characteristicMatrix (q.jacobianNoQf x) s := by
    ext i j
    simp [Linear.characteristicMatrix, jacobianNoQf, Matrix.one_apply, Subtype.ext_iff]
  rw [det_eq_of_col _ 12 (fun i hi => by simp [Linear.characteristicMatrix, hi, hcol i]), h1, h2]

/-- Without droop the Jacobian is Hurwitz iff `ω_q > 0` and the Jacobian on the fifteen other
coordinates is spectrally stable. -/
@[tmio M, powerlib_domain] theorem isHurwitz_jacobian_iff_of_nq (hnq : q.nq = 0)
    (hCdc : q.Cdc ≠ 0) {x : State 16} (hx : x 13 ≠ 0) :
    LinearSystems.IsHurwitz (q.jacobian x) ↔
      0 < q.ωq ∧ Linear.SpectrallyStable (q.jacobianNoQf x) := by
  rw [← Linear.spectrallyStable_iff_isHurwitz]
  simp only [Linear.SpectrallyStable, q.det_characteristicMatrix_jacobian_of_nq hnq hCdc hx]
  constructor
  · intro h
    refine ⟨?_, fun s hs => h s (by rw [hs, mul_zero])⟩
    have := h (-(q.ωq : ℂ)) (by rw [neg_add_cancel, zero_mul])
    simpa using this
  · rintro ⟨hω, h⟩ s hs
    rcases mul_eq_zero.mp hs with hs | hs
    · have : s = -(q.ωq : ℂ) := eq_neg_of_add_eq_zero_left hs
      rw [this]; simpa using hω
    · exact h s hs

end DCParams

/-! ## The family conclusion -/

@[tmio TM, powerlib_domain] private theorem dc_mem_den_flow' {m : DCModel} {P : Flow.Property} :
    m ∈ dcFamily.den (.flow P) ↔ P.holds m.q.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : DCModel => m.q.field) (pt := DCModel.point)
    (Spectral.localFamily_isAutonomous _ _ _)

/-- **The local decision of the DC variant without droop** (`n_q = 0`, `C_dc, v_ref ≠ 0`, every
other parameter value): read about its selected point, the 16-state model is locally
exponentially stable iff the point is an equilibrium, `ω_q > 0` and the `15 × 15` Jacobian
without the reactive-power filter is Hurwitz. -/
@[tmio TM, powerlib_domain] theorem dcFamily_mem_den_locallyExponentiallyStable_iff_of_nq
    (m : DCModel) (hnq : m.q.nq = 0) (hCdc : m.q.Cdc ≠ 0) (hvref : m.q.vref ≠ 0) :
    connection% (m ∈ dcFamily.den (.flow .locallyExponentiallyStable) ↔
      m.q.field m.point = 0 ∧ 0 < m.q.ωq ∧ Linear.SpectrallyStable (m.q.jacobianNoQf m.point)) := by
  unfold powerlib.TMIO.Statement
  have hx : m.point 13 ≠ 0 := by
    simp only [DCModel.point, DCParams.graph_13, DCParams.slowPoint]
    simpa using hvref
  have hU : IsOpen {x : State 16 | x 13 ≠ 0} :=
    isOpen_ne_fun (Dynamics.contDiff_coord (k := 1) 13).continuous continuous_const
  have hJ := m.q.hasFDerivAt_jacobian hCdc hx
  rw [dc_mem_den_flow', ← m.q.isHurwitz_jacobian_iff_of_nq hnq hCdc hx]
  exact Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian_local hU hx _
    (m.q.contDiffOn_field hCdc) hJ.fderiv

end powerlib.GFM.FullModel
