import theorem.GridTiedConverter.GFM.VoltageModulationSmooth

/-! # The droop core with two filters under grid-voltage modulation: forced orbit and Floquet multipliers

End-to-end statement for the three-state droop core (power-measurement filter `ω_m`, droop filter
`ω₁`) with a general `C³` power map `P(δ, V)`. Its Jacobian at the operating point is the
synchronizing core's `A0r` conjugated by the linear part `L` of correspondence (8)
(`(δ, p_m, p_f) ↦ (δ, m_p(P* − p_f), p_m)`, `DroopTwoFilter`); the eigen-data, the first-order
orbit and the modulation are transported by `L`, and the pump is the synchronizing-core pump
`gV`. `SmoothForcedOrbit` then gives the forced orbit and the Floquet criterion
`|g_V/2| ≶ |λ₁|`.

Model boundary.
* States `(δ, p_m, p_f)`: `δ̇ = m_p(P* − p_f)`, `ṗ_m = ω_m(P(δ, V) − p_m)`,
  `ṗ_f = ω₁(p_m − p_f)` (`dfield`), `P` of class `C³`, `P* = P(δ₀, V₀)`, operating point
  `(δ₀, P*, P*)`; quasi-static network (no network dynamics), no Q–V loop dynamics or limits.
* `P_δ`, `P_V`, `P_δδ`, `P_δV` the partial derivatives of `P` at `(δ₀, V₀)`; Hopf point
  `ω₁ω_m = Ω²`, `m_p ω₁ ω_m P_δ = (ω₁ + ω_m)Ω²`, `ω₁ + ω_m > 0`; drive `V₀ + ε V̂ cos 2Ωt`; state
  perturbation `ε A₀'` with any real `A₀'`. Orbital stability is not derived.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2, §3 (droop core, correspondence (8)); the voltage excitation
is new.

Results.
* `conj_right`, `conj_left`, `conj_dot`, `conj_right_real`, `conj_left_real`, `conj_dot_real`,
  `star_map_mulVec`, `conj_pump`, `conj_forced` — eigen-data, pump and forced response under a
  real change of coordinates.
* `dfield`, `core` (correspondence (8): `ω₀ = 1`, `2H = 1/(m_p ω₁)`, `D = 1/m_p`, `ω_c = ω_m`),
  `Lm`, `Li`, `Lm_mul_Li`, `Li_mul_Lm`, `contDiff_dfield`, `djac`, `matX_dfield`, `dxeq`,
  `dfield_eq_zero`, `djac_eq` (`∂ₓF(x₀) = L⁻¹ A0r L`), `fderivW_dfield`, `smDx_dfield`,
  `smM1_dfield`, `smA1_dfield` (`A₁ = L⁻¹ A₁^core L`), `core_a`, `core_d0`, `core_d2`
  (`d₂ = ω₁ + ω_m`).
* `dright`, `dleft`, `droop_data` — the transported data; `orbit_droop_stable`,
  `orbit_droop_unstable` — the end-to-end Floquet statements.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated droop core (forced orbit, Floquet multipliers).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace Droop
open Complex Matrix Filter Topology
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)
open Core (Pd contDiff_Pd hasDerivAt_P_line)

/-! ### Conjugation of eigen-data and pump by a real change of coordinates -/

section Conj

variable {X : Type*} [Fintype X] [DecidableEq X]

@[tmio T, powerlib_foundation] theorem conj_right {A Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    {r : X → ℂ} {l : ℂ} (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = l • r) :
    (Li * A * Lm).map (algebraMap ℝ ℂ) *ᵥ (Li.map (algebraMap ℝ ℂ) *ᵥ r) =
      l • (Li.map (algebraMap ℝ ℂ) *ᵥ r) := by
  have h' : Lm.map (algebraMap ℝ ℂ) * Li.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, h', Matrix.mul_one,
    ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_smul]

@[tmio T, powerlib_foundation] theorem conj_left {A Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    {u : X → ℂ} {l : ℂ} (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = l • u) :
    (u ᵥ* Lm.map (algebraMap ℝ ℂ)) ᵥ* (Li * A * Lm).map (algebraMap ℝ ℂ) =
      l • (u ᵥ* Lm.map (algebraMap ℝ ℂ)) := by
  have h' : Lm.map (algebraMap ℝ ℂ) * Li.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, h', Matrix.one_mul, ← Matrix.vecMul_vecMul, hu, Matrix.smul_vecMul]

@[tmio T, powerlib_foundation] theorem conj_dot {Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    (u r : X → ℂ) :
    (u ᵥ* Lm.map (algebraMap ℝ ℂ)) ⬝ᵥ (Li.map (algebraMap ℝ ℂ) *ᵥ r) = u ⬝ᵥ r := by
  have h' : Lm.map (algebraMap ℝ ℂ) * Li.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h', Matrix.one_mulVec]

@[tmio T, powerlib_foundation] theorem conj_right_real {A Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    {r : X → ℝ} {l : ℝ} (hr : A *ᵥ r = l • r) :
    (Li * A * Lm) *ᵥ (Li *ᵥ r) = l • (Li *ᵥ r) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_smul]

@[tmio T, powerlib_foundation] theorem conj_left_real {A Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    {u : X → ℝ} {l : ℝ} (hu : u ᵥ* A = l • u) :
    (u ᵥ* Lm) ᵥ* (Li * A * Lm) = l • (u ᵥ* Lm) := by
  rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul,
    ← Matrix.vecMul_vecMul, hu, Matrix.smul_vecMul]

@[tmio T, powerlib_foundation] theorem conj_dot_real {Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    (u r : X → ℝ) : (u ᵥ* Lm) ⬝ᵥ (Li *ᵥ r) = u ⬝ᵥ r := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem star_map_mulVec (M : Matrix X X ℝ) (r : X → ℂ) :
    star (M.map (algebraMap ℝ ℂ) *ᵥ r) = M.map (algebraMap ℝ ℂ) *ᵥ star r := by
  funext i
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

@[tmio T, powerlib_foundation] theorem conj_pump {Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    (B : Matrix X X ℂ) (u r : X → ℂ) :
    (u ᵥ* Lm.map (algebraMap ℝ ℂ)) ⬝ᵥ ((Li.map (algebraMap ℝ ℂ) * B * Lm.map (algebraMap ℝ ℂ)) *ᵥ
      star (Li.map (algebraMap ℝ ℂ) *ᵥ r)) = u ⬝ᵥ (B *ᵥ star r) := by
  have h' : Lm.map (algebraMap ℝ ℂ) * Li.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [star_map_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h',
    Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h',
    Matrix.one_mulVec]

@[tmio T, powerlib_foundation] theorem conj_forced {A Li Lm : Matrix X X ℝ} (h : Lm * Li = 1)
    {s : ℂ} {z b : X → ℂ} (hz : s • z - A.map (algebraMap ℝ ℂ) *ᵥ z = b) :
    s • (Li.map (algebraMap ℝ ℂ) *ᵥ z) -
        (Li * A * Lm).map (algebraMap ℝ ℂ) *ᵥ (Li.map (algebraMap ℝ ℂ) *ᵥ z) =
      Li.map (algebraMap ℝ ℂ) *ᵥ b := by
  have h' : Lm.map (algebraMap ℝ ℂ) * Li.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, h', Matrix.mul_one,
    ← Matrix.mulVec_mulVec, ← hz, Matrix.mulVec_sub, Matrix.mulVec_smul]

end Conj

/-! ### The droop core with two filters and a voltage-dependent power map -/

variable (mp ω1 ωm : ℝ)

/-- The droop core with power-measurement filter `ω_m` and droop filter `ω₁` and a general power
map `P(δ, V)`: states `(δ, p_m, p_f)`, `δ̇ = m_p(P* − p_f)`, `ṗ_m = ω_m(P(δ, V) − p_m)`,
`ṗ_f = ω₁(p_m − p_f)`. -/
def dfield (P : ℝ × ℝ → ℝ) (Pset : ℝ) (q : (Fin 3 → ℝ) × ℝ) : Fin 3 → ℝ :=
  ![mp * (Pset - q.1 2), ωm * (P (q.1 0, q.2) - q.1 1), ω1 * (q.1 1 - q.1 2)]

/-- The synchronizing core of correspondence (8): `ω₀ = 1`, `2H = 1/(m_p ω₁)`, `D = 1/m_p`,
`ω_c = ω_m`. -/
def core (Pδ PV Pδδ PδV : ℝ) : Core where
  ω0 := 1
  H := 1 / (2 * mp * ω1)
  D := 1 / mp
  ωc := ωm
  Pδ := Pδ
  PV := PV
  Pδδ := Pδδ
  PδV := PδV

/-- The linear part of `(δ, p_m, p_f) ↦ (δ, Δω, P_f) = (δ, m_p(P* − p_f), p_m)`. -/
def Lm : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, -mp; 0, 1, 0]

/-- Its inverse. -/
def Li : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 1; 0, -1 / mp, 0]

omit ω1 ωm in
@[tmio M, powerlib_domain] theorem Lm_mul_Li (hmp : mp ≠ 0) : Lm mp * Li mp = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lm, Li, Matrix.mul_apply, Fin.sum_univ_three]
  field_simp

omit ω1 ωm in
@[tmio M, powerlib_domain] theorem Li_mul_Lm (hmp : mp ≠ 0) : Li mp * Lm mp = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (Lm_mul_Li mp hmp)

@[tmio M, powerlib_domain] theorem contDiff_dfield {P : ℝ × ℝ → ℝ} {n : WithTop ℕ∞}
    (hP : ContDiff ℝ n P) (Pset : ℝ) : ContDiff ℝ n (dfield mp ω1 ωm P Pset) := by
  have hx : ∀ i : Fin 3, ContDiff ℝ n fun q : (Fin 3 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hPq : ContDiff ℝ n fun q : (Fin 3 → ℝ) × ℝ => P (q.1 0, q.2) :=
    hP.comp ((hx 0).prodMk contDiff_snd)
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (contDiff_const.sub (hx 2))
  · exact contDiff_const.mul (hPq.sub (hx 1))
  · exact contDiff_const.mul ((hx 1).sub (hx 2))

/-- The Jacobian of the droop core at `(x, V)`. -/
def djac (P : ℝ × ℝ → ℝ) (q : (Fin 3 → ℝ) × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, -mp; ωm * Pd P (q.1 0, q.2), -ωm, 0; 0, ω1, -ω1]

@[tmio M, powerlib_domain] theorem matX_dfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (Pset : ℝ) (q : (Fin 3 → ℝ) × ℝ) : matX (dfield mp ω1 ωm P Pset) q = djac mp ω1 ωm P q := by
  refine ParametricResonance.ForcedOrbit.matX_of_line
    ((contDiff_dfield mp ω1 ωm hP Pset).differentiable (by norm_num) _) fun y => ?_
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (q.1 + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (q.1 i)
  have hPl := hasDerivAt_P_line ((hP.differentiable (by norm_num)) (q.1 0, q.2)) (y 0) 0
  have hlin : fderiv ℝ P (q.1 0, q.2) (y 0, 0) = y 0 * Pd P (q.1 0, q.2) := by
    rw [Pd, show ((y 0, (0 : ℝ)) : ℝ × ℝ) = y 0 • ((1, 0) : ℝ × ℝ) by simp, map_smul,
      smul_eq_mul]
  have hPl' : HasDerivAt (fun s : ℝ => P ((q.1 + s • y) 0, q.2))
      (fderiv ℝ P (q.1 0, q.2) (y 0, 0)) 0 := by
    convert hPl using 1; funext s; simp
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine (((hasDerivAt_const (0 : ℝ) Pset).sub (hl 2)).const_mul mp).congr_deriv ?_
    show _ = (djac mp ω1 ωm P q *ᵥ y) 0
    simp [djac, mulVec, dotProduct, Fin.sum_univ_three]
  · refine ((hPl'.sub (hl 1)).const_mul ωm).congr_deriv ?_
    show _ = (djac mp ω1 ωm P q *ᵥ y) 1
    rw [hlin]; simp [djac, mulVec, dotProduct, Fin.sum_univ_three]; ring
  · refine (((hl 1).sub (hl 2)).const_mul ω1).congr_deriv ?_
    show _ = (djac mp ω1 ωm P q *ᵥ y) 2
    simp [djac, mulVec, dotProduct, Fin.sum_univ_three]; ring

/-- The operating point `x₀ = (δ₀, P(δ₀, V₀), P(δ₀, V₀))`. -/
def dxeq (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) : Fin 3 → ℝ := ![δ0, P (δ0, V0), P (δ0, V0)]

omit mp ω1 ωm in
@[tmio M, powerlib_domain] theorem dfield_eq_zero (mp ω1 ωm : ℝ) (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ) :
    dfield mp ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0, V0) = 0 := by
  funext i
  fin_cases i <;> simp [dfield, dxeq]

/-- Correspondence (8) for the Jacobian: `∂ₓF_droop(x₀) = L⁻¹ A0r L`. -/
@[tmio M, powerlib_domain] theorem djac_eq {P : ℝ × ℝ → ℝ} {δ0 V0 Pδ : ℝ} (PV Pδδ PδV : ℝ)
    (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0) (hPδ : Pd P (δ0, V0) = Pδ) :
    djac mp ω1 ωm P (dxeq P δ0 V0, V0) =
      Li mp * (core mp ω1 ωm Pδ PV Pδδ PδV).A0r * Lm mp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [djac, Core.A0r, core, Li, Lm, dxeq, hPδ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp

omit mp ω1 ωm in
@[tmio M, powerlib_domain] theorem fderivW_dfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (mp ω1 ωm : ℝ) {δ0 V0 PV : ℝ} (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) :
    fderiv ℝ (dfield mp ω1 ωm P (P (δ0, V0))) (dxeq P δ0 V0, V0) (0, 1) = ![0, ωm * PV, 0] := by
  have hPl := hasDerivAt_P_line ((hP.differentiable (by norm_num)) (δ0, V0)) 0 1
  refine ParametricResonance.ForcedOrbit.fderivW_of_line
    ((contDiff_dfield mp ω1 ωm hP _).differentiable (by norm_num) _) (hasDerivAt_pi.2 fun i => ?_)
  fin_cases i
  · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [dfield, dxeq])
  · have h := (hPl.sub_const (P (δ0, V0))).const_mul ωm
    rw [hPV] at h
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [dfield, dxeq])
  · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [dfield, dxeq])

@[tmio M, powerlib_domain] theorem smDx_dfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Pδδ : ℝ} (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ) (y : Fin 3 → ℝ) :
    smDx (dfield mp ω1 ωm P (P (δ0, V0))) (dxeq P δ0 V0, V0) y =
      !![0, 0, 0; ωm * (y 0 * Pδδ), 0, 0; 0, 0, 0] := by
  have hPl := hasDerivAt_P_line (((contDiff_Pd hP).differentiable (by norm_num)) (δ0, V0))
    (y 0) 0
  have hlin : fderiv ℝ (Pd P) (δ0, V0) (y 0, 0) = y 0 * Pδδ := by
    rw [show ((y 0, (0 : ℝ)) : ℝ × ℝ) = y 0 • ((1, 0) : ℝ × ℝ) by simp, map_smul, smul_eq_mul,
      hPδδ]
  rw [hlin] at hPl
  refine ParametricResonance.ForcedOrbit.smDx_of_line
    ((contDiff_dfield mp ω1 ωm (n := 2) (hP.of_le (by norm_num)) _).contDiffAt) y
    (Jr := fun t => djac mp ω1 ωm P (dxeq P δ0 V0 + t • y, V0))
    (Filter.Eventually.of_forall fun t => matX_dfield mp ω1 ωm hP _ (dxeq P δ0 V0 + t • y, V0))
    fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-mp)
  · exact (hPl.const_mul ωm).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp [djac, dxeq])
  · exact hasDerivAt_const (0 : ℝ) (-ωm)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) ω1
  · exact hasDerivAt_const (0 : ℝ) (-ω1)

@[tmio M, powerlib_domain] theorem smM1_dfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 PδV : ℝ} (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) :
    smM1 (dfield mp ω1 ωm P (P (δ0, V0))) (dxeq P δ0 V0, V0) =
      !![0, 0, 0; ωm * PδV, 0, 0; 0, 0, 0] := by
  have hPl := hasDerivAt_P_line (((contDiff_Pd hP).differentiable (by norm_num)) (δ0, V0)) 0 1
  rw [hPδV] at hPl
  refine ParametricResonance.ForcedOrbit.smM1_of_line
    ((contDiff_dfield mp ω1 ωm (n := 2) (hP.of_le (by norm_num)) _).contDiffAt)
    (Jr := fun t => djac mp ω1 ωm P (dxeq P δ0 V0, V0 + t))
    (Filter.Eventually.of_forall fun t => matX_dfield mp ω1 ωm hP _ (dxeq P δ0 V0, V0 + t))
    fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-mp)
  · exact (hPl.const_mul ωm).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp [djac, dxeq])
  · exact hasDerivAt_const (0 : ℝ) (-ωm)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) ω1
  · exact hasDerivAt_const (0 : ℝ) (-ω1)

/-- The modulation of the droop core along `(z, V̂)` is the core modulation conjugated by the
coordinate change: `A₁ = L⁻¹ A₁^core(z_δ, V̂) L`. -/
@[tmio M, powerlib_domain] theorem smA1_dfield {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Pδ PV Pδδ PδV : ℝ} (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) (z : Fin 3 → ℂ) :
    smA1 (dfield mp ω1 ωm P (P (δ0, V0))) (dxeq P δ0 V0, V0) Vh z =
      (Li mp).map (algebraMap ℝ ℂ) * (core mp ω1 ωm Pδ PV Pδδ PδV).A1 (z 0) Vh *
        (Lm mp).map (algebraMap ℝ ℂ) := by
  have hdx := smDx_dfield mp ω1 ωm hP hPδδ
  have hm := smM1_dfield mp ω1 ωm hP hPδV
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC, hdx, hm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Core.A1, core, Li, Lm, Matrix.mul_apply, Fin.sum_univ_three,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

omit mp ω1 ωm in
@[tmio M, powerlib_domain] theorem core_a (mp ω1 ωm Pδ PV Pδδ PδV : ℝ) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) : (core mp ω1 ωm Pδ PV Pδδ PδV).a = ω1 := by
  have h1 : (mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have h2 : (ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp [Core.a, core]
  field_simp

omit mp ω1 ωm in
@[tmio M, powerlib_domain] theorem core_d0 (mp ω1 ωm Pδ PV Pδδ PδV : ℝ) :
    (core mp ω1 ωm Pδ PV Pδδ PδV).d0 = mp * ω1 * ωm * Pδ := by
  simp only [Core.d0, core]
  push_cast
  simp only [mul_inv, inv_inv, div_eq_mul_inv]
  ring

omit mp ω1 ωm in
@[tmio M, powerlib_domain] theorem core_d2 (mp ω1 ωm Pδ PV Pδδ PδV : ℝ) (hmp : mp ≠ 0)
    (hω1 : ω1 ≠ 0) : (core mp ω1 ωm Pδ PV Pδδ PδV).d2 = ω1 + ωm := by
  simp [Core.d2, core]
  field_simp

/-- The right eigenvector of the pair `±jΩ` in the droop coordinates: `L⁻¹ r(jΩ)`. -/
def dright (Pδ PV Pδδ PδV Ω : ℝ) : Fin 3 → ℂ :=
  (Li mp).map (algebraMap ℝ ℂ) *ᵥ (core mp ω1 ωm Pδ PV Pδδ PδV).right (Ω * I)

/-- The left eigenvector in the droop coordinates: `u(jΩ) L`. -/
def dleft (Pδ PV Pδδ PδV Ω : ℝ) : Fin 3 → ℂ :=
  (core mp ω1 ωm Pδ PV Pδδ PδV).left (Ω * I) ᵥ* (Lm mp).map (algebraMap ℝ ℂ)

/-- The data of the droop core at its Hopf point, transported from the synchronizing core. -/
@[tmio M, powerlib_domain] theorem droop_data {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) :
    let c := core mp ω1 ωm Pδ PV Pδδ PδV
    let F := dfield mp ω1 ωm P (P (δ0, V0))
    let q0 := (dxeq P δ0 V0, V0)
    let z := (Li mp).map (algebraMap ℝ ℂ) *ᵥ c.forcedV (2 * Ω * I) Vh
    0 < c.d2 ∧
    (matX F q0).map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω =
      ((Ω : ℂ) * I) • dright mp ω1 ωm Pδ PV Pδδ PδV Ω ∧
    dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ᵥ* (matX F q0).map (algebraMap ℝ ℂ) =
      ((Ω : ℂ) * I) • dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ∧
    dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω = 1 ∧
    matX F q0 *ᵥ (Li mp *ᵥ c.r3) = (-c.d2) • (Li mp *ᵥ c.r3) ∧
    (c.u3 ᵥ* Lm mp) ᵥ* matX F q0 = (-c.d2) • (c.u3 ᵥ* Lm mp) ∧
    (c.u3 ᵥ* Lm mp) ⬝ᵥ (Li mp *ᵥ c.r3) = 1 ∧
    (((2 * Ω : ℝ) : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • (fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) ∧
    dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ (smA1 F q0 Vh z *ᵥ
      star (dright mp ω1 ωm Pδ PV Pδδ PδV Ω)) = c.gV V0 Ω Vh := by
  intro c F q0 z
  have hω0 : c.ω0 ≠ 0 := one_ne_zero
  have hH : c.H ≠ 0 := by
    simp only [c, core]; exact one_div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hmp) hω1)
  have hd2c : 0 < c.d2 := by rw [core_d2 mp ω1 ωm Pδ PV Pδδ PδV hmp hω1]; exact hd2
  have hH1c : c.a * c.ωc = (Ω : ℂ) ^ 2 := by
    rw [core_a mp ω1 ωm Pδ PV Pδδ PδV hmp hω1]
    show (ω1 : ℂ) * ωm = (Ω : ℂ) ^ 2
    exact_mod_cast hH1
  have hH2c : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2 := by
    rw [core_d0, core_a mp ω1 ωm Pδ PV Pδδ PδV hmp hω1]
    show (mp : ℂ) * ω1 * ωm * Pδ = ((ω1 : ℂ) + ωm) * (Ω : ℂ) ^ 2
    exact_mod_cast hH2
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1c hH2c
  have hLL := Lm_mul_Li mp hmp
  have hm : matX F q0 = Li mp * c.A0r * Lm mp := by
    simp only [F, q0]
    rw [matX_dfield mp ω1 ωm hP, djac_eq mp ω1 ωm PV Pδδ PδV hmp hω1 hPδ]
  have hzc := c.zorb_sfield hP hΩ.ne' hω0 hH hH1c hH2c hPδ hPV Vh
  have hbc : (fun i => ((fderiv ℝ (c.sfield P (P (δ0, V0))) (Core.sxeq P δ0 V0, V0) (0, 1) i :
      ℝ) : ℂ)) = c.Bv := c.fderivW_sfield hP hPV
  rw [c.matX_sfield hP, c.sjac_eq hPδ, hbc] at hzc
  have hb : (fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) =
      (Li mp).map (algebraMap ℝ ℂ) *ᵥ c.Bv := by
    simp only [F, q0]
    rw [fderivW_dfield hP mp ω1 ωm hPV]
    funext i
    fin_cases i <;> simp [Li, Core.Bv, c, core, mulVec, dotProduct, Fin.sum_univ_three]
  have hz0 : z 0 = c.forcedVδ (2 * Ω * I) Vh := by
    simp [z, Li, mulVec, dotProduct, Fin.sum_univ_three, Core.forcedV]
  have hp := c.pump_voltage_hopf V0 Ω Vh hPδ0 hV0 hH hΩ.ne' hd2c.ne' hH1c hH2c
  rw [ParametricResonance.Element.pump] at hp
  refine ⟨hd2c, by rw [hm]; exact conj_right hLL hr, by rw [hm]; exact conj_left hLL hu,
    by rw [dleft, dright, conj_dot hLL]; exact hur, by rw [hm]; exact conj_right_real hLL hr3,
    by rw [hm]; exact conj_left_real hLL hu3, by rw [conj_dot_real hLL]; exact hur3, ?_, ?_⟩
  · rw [hm, hb]
    conv_rhs => rw [← Matrix.mulVec_smul]
    exact conj_forced hLL hzc
  · simp only [F, q0]
    rw [smA1_dfield mp ω1 ωm hP hPδδ hPδV, dleft, dright, conj_pump hLL, hz0, hp]
    rfl

/-- The droop core with two filters and a general `C³` power map `P(δ, V)`, grid-voltage
modulation, end-to-end, stability. Under correspondence (8) the core is the synchronizing core
`core` (`ω₀ = 1`, `2H = 1/(m_p ω₁)`, `D = 1/m_p`, `ω_c = ω_m`); at its Hopf point
(`ω₁ ω_m = Ω²`, `m_p ω₁ ω_m P_δ = (ω₁ + ω_m)Ω²`) with `V = V₀ + ε V̂ cos 2Ωt` and `ε A₀'`:
`Re λ₁ < 0` and `|g_V/2| < |λ₁|` (`λ₁ = u_d A₀' r_d` in the droop coordinates, `g_V = gV` with
`d₂ = ω₁ + ω_m`) give, for all small `ε > 0`, the forced periodic orbit with all Floquet
multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_droop_stable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)).re < 0)
    (hg : ‖(core mp ω1 ωm Pδ PV Pδδ PδV).gV V0 Ω Vh / 2‖ ^ 2 <
      ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (dfield mp ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (dfield mp ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (dfield mp ω1 ωm P (P (δ0, V0))) (dxeq P δ0 V0, V0)
            Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v =
            μ • v → ‖μ‖ < 1 := by
  obtain ⟨hd2c, hr, hu, hur, hr3, hu3, hur3, hz, hp⟩ := droop_data mp ω1 ωm hP hΩ hmp hω1 hd2
    hPδ0 hV0 hH1 hH2 hPδ hPV hPδδ hPδV Vh
  exact ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_stable
    (contDiff_dfield mp ω1 ωm hP _).contDiffAt (dfield_eq_zero mp ω1 ωm P δ0 V0) hΩ
    (neg_neg_of_pos hd2c) hr hu hur hr3 hu3 hur3 hz A0' hs (by rw [hp]; exact hg)

/-- The droop core with two filters, end-to-end parametric instability: `|λ₁| < |g_V/2|`. -/
@[tmio M, powerlib_domain] theorem orbit_droop_unstable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2 <
      ‖(core mp ω1 ωm Pδ PV Pδδ PδV).gV V0 Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (dfield mp ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (dfield mp ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (dfield mp ω1 ωm P (P (δ0, V0)))
          (dxeq P δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hd2c, hr, hu, hur, hr3, hu3, hur3, hz, hp⟩ := droop_data mp ω1 ωm hP hΩ hmp hω1 hd2
    hPδ0 hV0 hH1 hH2 hPδ hPV hPδδ hPδV Vh
  exact ParametricResonance.ForcedOrbit.smooth_orbit_floquet_three_unstable
    (contDiff_dfield mp ω1 ωm hP _).contDiffAt (dfield_eq_zero mp ω1 ωm P δ0 V0) hΩ
    (neg_neg_of_pos hd2c) hr hu hur hr3 hu3 hur3 hz A0' (by rw [hp]; exact hg)

end Droop
end VoltageModulation
end powerlib.GFM
