import dependencies.Mathlib
import theorem.Attributes

/-! # PMSM steady-state algebra: torque, MTPA, voltage ellipse (foundation)

Model: permanent-magnet synchronous machine in the rotor dq frame (d-axis on the magnet),
motor convention, constant `r_s, L_d, L_q, ψ_f`, `np` pole pairs, amplitude-invariant
transform:
`v_d = r_s i_d + L_d di_d/dt − ω L_q i_q`, `v_q = r_s i_q + L_q di_q/dt + ω L_d i_d + ω ψ_f`,
`T_e = (3/2) np (ψ_f i_q + (L_d − L_q) i_d i_q)`.
These are steady-state / algebraic statements (no dynamics, no controller); saturation,
cross-saturation and temperature effects are excluded.

Contents.
* SPMSM (`L_d = L_q`): torque `(3/2) np ψ_f i_q`; on the current disk `|i| ≤ I` the torque is
  maximised exactly at `(0, I)` (`spmsm_mtpa`), and a given torque is produced with least
  current exactly at `i_d = 0` (`spmsm_minCurrent`). Hence `i_d* = 0`.
* IPMSM (`ΔL = L_q − L_d > 0`, `ψ_f > 0`): the MTPA point is
  `i_d = ψ_f/(4ΔL) − √(ψ_f²/(16ΔL²) + I²/2)`, `i_q = √(I² − i_d²)`; it is the **unique**
  torque maximiser on the disk `i_d² + i_q² ≤ I²` (`ipmsm_mtpa_unique_max`), and in terms of
  `i_q` it is `i_d = ψ_f/(2ΔL) − √(ψ_f²/(4ΔL²) + i_q²)` (`ipmsm_mtpa_id_of_iq`).
* Voltage ellipse: in steady state with `r_s = 0`, `v_d² + v_q² ≤ V²` iff
  `(L_d i_d + ψ_f)² + (L_q i_q)² ≤ (V/ω)²` (`voltageEllipse_iff`).

Source: work-sync theory/T-field-oriented-control.md §1.6 (torque, SPMSM, IPMSM MTPA),
§1.7 (voltage ellipse).

Correction (FOC note §1.6): the note's MTPA formula
`i_d = ψ_f/(2(L_q − L_d)) − √(ψ_f²/(4(L_q − L_d)²) + i_s²/2)` mixes the `|i_s|`-form and the
`i_q`-form. The correct `|i_s|`-form is `ψ_f/(4ΔL) − √(ψ_f²/(16ΔL²) + i_s²/2)` and the correct
`i_q`-form is `ψ_f/(2ΔL) − √(ψ_f²/(4ΔL²) + i_q²)`. `noteMTPA_not_optimal` exhibits
`ψ_f = ΔL = 1`, `|i_s| = 2`, where the note's formula gives `i_d = −1` while the MTPA value is
`(1 − √33)/4 ≈ −1.186`, and the note's point produces strictly less torque.
-/

noncomputable section
namespace powerlib.Drives.PMSM

/-- PMSM electromagnetic torque. -/
def torque (np ψf Ld Lq id iq : ℝ) : ℝ := 3 / 2 * np * (ψf * iq + (Ld - Lq) * id * iq)

/-! ## Surface PMSM -/

@[powerlib_foundation] theorem torque_surface (np ψf L id iq : ℝ) :
    torque np ψf L L id iq = 3 / 2 * np * ψf * iq := by
  unfold torque; ring

/-- SPMSM MTPA: on the disk `i_d² + i_q² ≤ I²` the torque is maximised exactly at
`(i_d, i_q) = (0, I)` (for `np ψ_f > 0`). -/
@[powerlib_foundation] theorem spmsm_mtpa (np ψf L I : ℝ) (hk : 0 < np * ψf) (hI : 0 ≤ I)
    (id iq : ℝ) (hdisk : id ^ 2 + iq ^ 2 ≤ I ^ 2) :
    torque np ψf L L id iq ≤ torque np ψf L L 0 I ∧
      (torque np ψf L L id iq = torque np ψf L L 0 I → id = 0 ∧ iq = I) := by
  rw [torque_surface, torque_surface]
  have hiq : iq ≤ I := by
    have : iq ^ 2 ≤ I ^ 2 := by nlinarith [sq_nonneg id]
    exact abs_le_of_sq_le_sq' this hI |>.2
  constructor
  · nlinarith
  · intro h
    have hq : iq = I := by
      have : np * ψf * (I - iq) = 0 := by linear_combination -(2 / 3) * h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hk.ne'
      · linarith
    refine ⟨?_, hq⟩
    subst hq
    nlinarith [sq_nonneg id]

/-- SPMSM minimum current for a given torque: every current producing the torque `T` has
`|i|² ≥ (T/c)²` with equality iff `i_d = 0`, `c = (3/2) np ψ_f`. -/
@[powerlib_foundation] theorem spmsm_minCurrent (np ψf L T id iq : ℝ) (hk : np * ψf ≠ 0)
    (hT : torque np ψf L L id iq = T) :
    (T / (3 / 2 * np * ψf)) ^ 2 ≤ id ^ 2 + iq ^ 2 ∧
      ((T / (3 / 2 * np * ψf)) ^ 2 = id ^ 2 + iq ^ 2 ↔ id = 0) := by
  rw [torque_surface] at hT
  have hc : 3 / 2 * np * ψf ≠ 0 := by
    have : 3 / 2 * np * ψf = 3 / 2 * (np * ψf) := by ring
    rw [this]; exact mul_ne_zero (by norm_num) hk
  have hiq : iq = T / (3 / 2 * np * ψf) := by
    rw [eq_div_iff hc, ← hT]; ring
  rw [← hiq]
  refine ⟨by nlinarith [sq_nonneg id], ?_⟩
  constructor
  · intro h
    have : id ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h; rw [h]; ring

/-! ## Interior PMSM: MTPA -/

/-- Reduced torque `i_q (ψ_f − ΔL i_d)` (= `T_e / ((3/2) np)` with `ΔL = L_q − L_d`). -/
def reducedTorque (ψf ΔL x y : ℝ) : ℝ := y * (ψf - ΔL * x)

@[powerlib_foundation] theorem torque_eq_reduced (np ψf Ld Lq id iq : ℝ) :
    torque np ψf Ld Lq id iq = 3 / 2 * np * reducedTorque ψf (Lq - Ld) id iq := by
  unfold torque reducedTorque; ring

/-- MTPA d-axis current for current magnitude `I`. -/
def mtpaId (ψf ΔL I : ℝ) : ℝ := ψf / (4 * ΔL) - Real.sqrt (ψf ^ 2 / (16 * ΔL ^ 2) + I ^ 2 / 2)

/-- MTPA q-axis current. -/
def mtpaIq (ψf ΔL I : ℝ) : ℝ := Real.sqrt (I ^ 2 - mtpaId ψf ΔL I ^ 2)

section MTPA

variable {ψf ΔL I : ℝ}

/-- The MTPA `i_d` solves `2ΔL x² − ψ_f x − ΔL I² = 0`. -/
@[powerlib_foundation] theorem mtpaId_root (hΔ : 0 < ΔL) :
    2 * ΔL * mtpaId ψf ΔL I ^ 2 - ψf * mtpaId ψf ΔL I - ΔL * I ^ 2 = 0 := by
  unfold mtpaId
  have hs := Real.sq_sqrt (show 0 ≤ ψf ^ 2 / (16 * ΔL ^ 2) + I ^ 2 / 2 by positivity)
  set s := Real.sqrt (ψf ^ 2 / (16 * ΔL ^ 2) + I ^ 2 / 2)
  have hΔ' : ΔL ≠ 0 := hΔ.ne'
  field_simp
  field_simp at hs
  linear_combination hs

@[powerlib_foundation] theorem mtpaId_neg (hΔ : 0 < ΔL) (hψ : 0 ≤ ψf) (hI : 0 < I) :
    mtpaId ψf ΔL I < 0 := by
  unfold mtpaId
  rw [sub_neg]
  have h0 : 0 ≤ ψf / (4 * ΔL) := by positivity
  apply Real.lt_sqrt_of_sq_lt
  have : (ψf / (4 * ΔL)) ^ 2 = ψf ^ 2 / (16 * ΔL ^ 2) := by field_simp; ring
  rw [this]
  have : 0 < I ^ 2 / 2 := by positivity
  linarith

/-- `i_d² ≤ I²/2`, with strict inequality when `ψ_f > 0` (MTPA angle below 135°). -/
@[powerlib_foundation] theorem mtpaId_sq_lt (hΔ : 0 < ΔL) (hψ : 0 < ψf) (hI : 0 < I) :
    mtpaId ψf ΔL I ^ 2 < I ^ 2 / 2 := by
  have hr := mtpaId_root (ψf := ψf) (I := I) hΔ
  have hn := mtpaId_neg hΔ hψ.le hI
  have : ψf * mtpaId ψf ΔL I < 0 := mul_neg_of_pos_of_neg hψ hn
  nlinarith

@[powerlib_foundation] theorem mtpaIq_sq (hΔ : 0 < ΔL) (hψ : 0 < ψf) (hI : 0 < I) :
    mtpaIq ψf ΔL I ^ 2 = I ^ 2 - mtpaId ψf ΔL I ^ 2 := by
  unfold mtpaIq
  have := mtpaId_sq_lt hΔ hψ hI
  rw [Real.sq_sqrt (by nlinarith)]

@[powerlib_foundation] theorem mtpaIq_pos (hΔ : 0 < ΔL) (hψ : 0 < ψf) (hI : 0 < I) :
    0 < mtpaIq ψf ΔL I := by
  unfold mtpaIq
  have := mtpaId_sq_lt hΔ hψ hI
  apply Real.sqrt_pos.mpr
  nlinarith

/-- The MTPA point lies on the current circle. -/
@[powerlib_foundation] theorem mtpa_on_circle (hΔ : 0 < ΔL) (hψ : 0 < ψf) (hI : 0 < I) :
    mtpaId ψf ΔL I ^ 2 + mtpaIq ψf ΔL I ^ 2 = I ^ 2 := by
  rw [mtpaIq_sq hΔ hψ hI]; ring

/-- MTPA stationarity on the circle: `ΔL x² − ψ_f x − ΔL y² = 0` (the condition
`∂T/∂i_d |_{|i|=const} = 0`). -/
@[powerlib_foundation] theorem mtpa_stationary (hΔ : 0 < ΔL) (hψ : 0 < ψf) (hI : 0 < I) :
    ΔL * mtpaId ψf ΔL I ^ 2 - ψf * mtpaId ψf ΔL I - ΔL * mtpaIq ψf ΔL I ^ 2 = 0 := by
  rw [mtpaIq_sq hΔ hψ hI]
  linear_combination mtpaId_root (ψf := ψf) (I := I) hΔ

/-- Lagrange-multiplier certificate: if `(x₀, y₀)` is on the circle `x₀² + y₀² = I²` and
`∇T = 2λ (x₀, y₀)` there, the torque gap to any current is an explicit quadratic form plus the
multiplier times the slack. -/
@[powerlib_foundation] theorem gap_identity (ψf ΔL I x₀ y₀ μ x y : ℝ)
    (hc : x₀ ^ 2 + y₀ ^ 2 = I ^ 2) (h1 : 2 * μ * x₀ = -(ΔL * y₀))
    (h2 : 2 * μ * y₀ = ψf - ΔL * x₀) :
    reducedTorque ψf ΔL x₀ y₀ - reducedTorque ψf ΔL x y =
      μ * ((x - x₀) ^ 2 + (y - y₀) ^ 2) + ΔL * (x - x₀) * (y - y₀) +
        μ * (I ^ 2 - x ^ 2 - y ^ 2) := by
  unfold reducedTorque
  linear_combination (x - x₀) * h1 + (y - y₀) * h2 + μ * hc

/-- The MTPA multiplier `λ = −ΔL i_q/(2 i_d)` satisfies both Lagrange equations. -/
@[powerlib_foundation] theorem mtpa_lagrange (hΔ : 0 < ΔL) (hψ : 0 < ψf) (hI : 0 < I) :
    2 * (-(ΔL * mtpaIq ψf ΔL I) / (2 * mtpaId ψf ΔL I)) * mtpaId ψf ΔL I =
        -(ΔL * mtpaIq ψf ΔL I) ∧
      2 * (-(ΔL * mtpaIq ψf ΔL I) / (2 * mtpaId ψf ΔL I)) * mtpaIq ψf ΔL I =
        ψf - ΔL * mtpaId ψf ΔL I := by
  have hx0 : mtpaId ψf ΔL I ≠ 0 := (mtpaId_neg hΔ hψ.le hI).ne
  have hst := mtpa_stationary hΔ hψ hI
  constructor
  · field_simp
  · field_simp
    linear_combination hst

end MTPA

/-- **IPMSM MTPA.** For `ΔL = L_q − L_d > 0`, `ψ_f > 0`, `I > 0`, the point
`(mtpaId, mtpaIq)` maximises the torque over the current disk `i_d² + i_q² ≤ I²`, and it is
the unique maximiser. -/
@[powerlib_foundation] theorem ipmsm_mtpa_unique_max (np ψf Ld Lq I : ℝ) (hnp : 0 < np)
    (hΔ : 0 < Lq - Ld) (hψ : 0 < ψf) (hI : 0 < I) (id iq : ℝ) (hdisk : id ^ 2 + iq ^ 2 ≤ I ^ 2)
    (hne : (id, iq) ≠ (mtpaId ψf (Lq - Ld) I, mtpaIq ψf (Lq - Ld) I)) :
    torque np ψf Ld Lq id iq < torque np ψf Ld Lq (mtpaId ψf (Lq - Ld) I) (mtpaIq ψf (Lq - Ld) I) := by
  rw [torque_eq_reduced, torque_eq_reduced]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  set ΔL := Lq - Ld
  obtain ⟨hl1, hl2⟩ := mtpa_lagrange hΔ hψ hI
  have hgap := gap_identity ψf ΔL I _ _ _ id iq (mtpa_on_circle hΔ hψ hI) hl1 hl2
  set x₀ := mtpaId ψf ΔL I
  set y₀ := mtpaIq ψf ΔL I
  have hx0 := mtpaId_neg hΔ hψ.le hI
  have hy0 := mtpaIq_pos hΔ hψ hI
  have hxy : -x₀ < y₀ := by
    have h1 := mtpaId_sq_lt hΔ hψ hI
    have h2 := mtpaIq_sq hΔ hψ hI
    nlinarith
  -- μ > ΔL / 2
  have hmu : ΔL / 2 < -(ΔL * y₀) / (2 * x₀) := by
    rw [lt_div_iff_of_neg (by linarith)]
    nlinarith
  have hd : 0 < (id - x₀) ^ 2 + (iq - y₀) ^ 2 := by
    rcases (ne_or_eq id x₀) with h | h
    · have := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
      positivity
    · have h' : iq ≠ y₀ := fun h' => hne (by rw [h, h'])
      have := sq_pos_of_ne_zero (sub_ne_zero.mpr h')
      positivity
  have hab : -(((id - x₀) ^ 2 + (iq - y₀) ^ 2) / 2) ≤ (id - x₀) * (iq - y₀) := by
    nlinarith [sq_nonneg (id - x₀ + (iq - y₀))]
  have hmupos : 0 < -(ΔL * y₀) / (2 * x₀) := lt_trans (by linarith) hmu
  have hslack : 0 ≤ -(ΔL * y₀) / (2 * x₀) * (I ^ 2 - id ^ 2 - iq ^ 2) :=
    mul_nonneg hmupos.le (by linarith)
  have hmain : 0 < -(ΔL * y₀) / (2 * x₀) * ((id - x₀) ^ 2 + (iq - y₀) ^ 2) +
      ΔL * (id - x₀) * (iq - y₀) := by
    have := mul_lt_mul_of_pos_right hmu hd
    nlinarith
  linarith

/-- The maximum is attained: the MTPA torque bounds every feasible torque. -/
@[powerlib_foundation] theorem ipmsm_mtpa_max (np ψf Ld Lq I : ℝ) (hnp : 0 < np)
    (hΔ : 0 < Lq - Ld) (hψ : 0 < ψf) (hI : 0 < I) (id iq : ℝ) (hdisk : id ^ 2 + iq ^ 2 ≤ I ^ 2) :
    torque np ψf Ld Lq id iq ≤ torque np ψf Ld Lq (mtpaId ψf (Lq - Ld) I) (mtpaIq ψf (Lq - Ld) I) := by
  by_cases h : (id, iq) = (mtpaId ψf (Lq - Ld) I, mtpaIq ψf (Lq - Ld) I)
  · simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]
  · exact (ipmsm_mtpa_unique_max np ψf Ld Lq I hnp hΔ hψ hI id iq hdisk h).le

/-- The MTPA `i_d` in terms of `i_q`: `i_d = ψ_f/(2ΔL) − √(ψ_f²/(4ΔL²) + i_q²)`. -/
@[powerlib_foundation] theorem ipmsm_mtpa_id_of_iq (ψf ΔL I : ℝ) (hΔ : 0 < ΔL) (hψ : 0 < ψf)
    (hI : 0 < I) :
    mtpaId ψf ΔL I = ψf / (2 * ΔL) - Real.sqrt (ψf ^ 2 / (4 * ΔL ^ 2) + mtpaIq ψf ΔL I ^ 2) := by
  have hst := mtpa_stationary hΔ hψ hI
  have hx := mtpaId_neg hΔ hψ.le hI
  set x := mtpaId ψf ΔL I
  set y := mtpaIq ψf ΔL I
  have hsq : (ψf / (2 * ΔL) - x) ^ 2 = ψf ^ 2 / (4 * ΔL ^ 2) + y ^ 2 := by
    field_simp
    linear_combination (16 * ΔL) * hst
  have hpos : 0 ≤ ψf / (2 * ΔL) - x := by
    have : 0 < ψf / (2 * ΔL) := by positivity
    linarith
  have : Real.sqrt (ψf ^ 2 / (4 * ΔL ^ 2) + y ^ 2) = ψf / (2 * ΔL) - x := by
    rw [← hsq, Real.sqrt_sq hpos]
  linarith

/-- The note's MTPA formula. -/
def noteMtpaId (ψf ΔL I : ℝ) : ℝ := ψf / (2 * ΔL) - Real.sqrt (ψf ^ 2 / (4 * ΔL ^ 2) + I ^ 2 / 2)

/-- **Correction witness**: for `ψ_f = ΔL = 1`, `I = 2` the note's formula gives `i_d = −1`,
which differs from the MTPA value, and the corresponding point on the current circle
`(−1, √3)` produces strictly less torque than MTPA (`L_d = 1`, `L_q = 2`, `np = 1`). -/
@[powerlib_foundation] theorem noteMTPA_not_optimal :
    noteMtpaId 1 1 2 = -1 ∧ mtpaId 1 1 2 ≠ -1 ∧
      torque 1 1 1 2 (-1) (Real.sqrt 3) < torque 1 1 1 2 (mtpaId 1 1 2) (mtpaIq 1 1 2) := by
  have hne1 : mtpaId 1 1 2 ≠ -1 := by
    unfold mtpaId
    intro h
    have hs : Real.sqrt ((1 : ℝ) ^ 2 / (16 * 1 ^ 2) + 2 ^ 2 / 2) = 5 / 4 := by linarith
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 ^ 2 / (16 * 1 ^ 2) + 2 ^ 2 / 2 by norm_num)
    rw [hs] at this
    norm_num at this
  refine ⟨?_, hne1, ?_⟩
  · unfold noteMtpaId
    have : (1 : ℝ) ^ 2 / (4 * 1 ^ 2) + 2 ^ 2 / 2 = (3 / 2) ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
    norm_num
  · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    have key := ipmsm_mtpa_unique_max 1 1 1 2 2 one_pos (by norm_num) one_pos (by norm_num)
      (-1) (Real.sqrt 3) (by nlinarith) (by
        rw [h21]
        intro h
        simp only [Prod.mk.injEq] at h
        exact hne1 h.1.symm)
    rwa [h21] at key

/-! ## Voltage ellipse -/

/-- Steady-state PMSM voltages with `r_s = 0` (from the dq voltage equations with
`di/dt = 0`): `v_d = −ω L_q i_q`, `v_q = ω (ψ_f + L_d i_d)`. The voltage limit
`v_d² + v_q² ≤ V²` is the ellipse `(L_d i_d + ψ_f)² + (L_q i_q)² ≤ (V/ω)²`. -/
@[powerlib_foundation] theorem voltageEllipse_iff (ω ψf Ld Lq id iq V : ℝ) (hω : ω ≠ 0) :
    (-ω * Lq * iq) ^ 2 + (ω * (ψf + Ld * id)) ^ 2 ≤ V ^ 2 ↔
      (Ld * id + ψf) ^ 2 + (Lq * iq) ^ 2 ≤ (V / ω) ^ 2 := by
  have hω2 : 0 < ω ^ 2 := by positivity
  rw [div_pow, le_div_iff₀ hω2]
  constructor <;> intro h <;> nlinarith

end powerlib.Drives.PMSM
