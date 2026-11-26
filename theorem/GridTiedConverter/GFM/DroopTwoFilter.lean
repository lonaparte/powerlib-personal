import theorem.GridTiedConverter.GFM.VSMLPF

/-! # Droop with two first-order filters is exactly the VSM with a power filter (three states)

The three-state droop core of the source (power measurement low-pass `ω_m`, droop filter `ω_1`)
on an infinite bus is the three-state VSM + power-filter model `VSMLPF` in affine coordinates,
for every state (large signal), and its Routh condition is the Hopf margin `κ_H > 0`.

Model boundary.
* State `x = (δ, p_m, p_f) : Dynamics.State 3`, in this order: angle of the internal EMF relative
  to the infinite bus (rad), measured power after the measurement low-pass, filtered power after
  the droop low-pass (pu). Continuous time, autonomous (grid angle fixed):
  `δ̇ = m_p (P* − p_f)`, `ṗ_m = ω_m (K₀ sin δ − p_m)`, `ṗ_f = ω_1 (p_m − p_f)` (`field`),
  `K₀ = E V/X` (constant EMF amplitude, lossless quasi-static network: no network dynamics, no
  resistance), export-positive active power, constant set-point `P*`.
* Excluded: Q–V droop and voltage loop, inner current and voltage loops, current limiting, PLL,
  delay, PWM, network electromagnetic dynamics. The grid-angle input and the dynamic network of
  the source are not part of this model.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (droop and VSG cores, the correspondence (8)
`ω₁ ↔ D/2H`, `ω_m ↔ ω_c`, `m_p ↔ ω₀/D`), Table 2 (`D_droop`), Table 3 (droop row of `κ_H`).

Results.
* `field_coord` — with `T(δ, p_m, p_f) = (δ, m_p (P* − p_f), p_m)` (`coord`, the angle, the droop
  frequency and the measured power), `VSMLPF.field (T x) = L (field x)` for every state `x`, where
  `L(y) = (y₀, −m_p y₂, y₁)` is the linear part of `T` (`coordLin`), and the VSM parameters are
  `M = 1/(m_p ω₁)`, `D = 1/m_p`, `ω_c = ω_m`, `P₀ = P*`, `K₀` (`toVSM`). Hence `T` maps
  solutions of the droop core to solutions of `VSMLPF` and back (`T` is invertible for
  `m_p ≠ 0`, `coord_injective`).
* `toVSM_vsg` — in the source's VSG parameters (`2H Δω̇ = P* − P_f − D Δω`, `θ̇ = ω₀ Δω`, so
  `M = 2H/ω₀`, `D_VSM = D/ω₀`), `m_p = ω₀/D`, `ω₁ = D/(2H)` give exactly `toVSM`: the
  correspondence (8) is an exact change of coordinates.
* `charPoly_toVSM` — `m_p ω₁ [(s + ω_c)(M s² + D s) + ω_c K] = s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m K`,
  the droop characteristic polynomial `D_droop` of Table 2 (`K = K_s`).
* `routh_iff_hopfMargin_pos` — the fast-filter Routh condition of `VSMLPF`,
  `K < D ω_c + D²/M`, is `κ_H = 1 − m_p K/(ω₁ + ω_m) > 0` (Table 3, droop row).

Family and connection conclusions.
None: the module states static evidence about the droop core (a field identity and parameter
identities). Its stability is not published as a connection; the stability conclusions of
`VSMLPF.family` apply to `toVSM` through `field_coord`.
-/

noncomputable section
namespace powerlib.GFM
open powerlib.Dynamics (State mk3 state3_ext)

/-- Parameters of the three-state droop core with a measurement and a droop low-pass. -/
structure DroopTwoFilter where
  mp : ℝ
  ω1 : ℝ
  ωm : ℝ
  Pref : ℝ
  K0 : ℝ

namespace DroopTwoFilter

variable (d : DroopTwoFilter)

/-- The closed-loop field on `(δ, p_m, p_f)`. -/
def field (x : State 3) : State 3 :=
  mk3 (d.mp * (d.Pref - x 2)) (d.ωm * (d.K0 * Real.sin (x 0) - x 1)) (d.ω1 * (x 1 - x 2))

/-- The VSM + power-filter parameters of the droop core. -/
def toVSM : VSMLPF := ⟨1 / (d.mp * d.ω1), 1 / d.mp, d.ωm, d.Pref, d.K0⟩

/-- The coordinate change `(δ, p_m, p_f) ↦ (δ, m_p (P* − p_f), p_m)`. -/
def coord (x : State 3) : State 3 := mk3 (x 0) (d.mp * (d.Pref - x 2)) (x 1)

/-- The linear part of `coord`. -/
def coordLin (y : State 3) : State 3 := mk3 (y 0) (-(d.mp * y 2)) (y 1)

@[tmio M, powerlib_domain] theorem field_coord (hmp : d.mp ≠ 0) (hω1 : d.ω1 ≠ 0) (x : State 3) :
    d.toVSM.field (d.coord x) = d.coordLin (d.field x) := by
  apply state3_ext <;>
    simp [VSMLPF.field, toVSM, coord, coordLin, field, Dynamics.mk3]
  · field_simp
    ring

@[tmio M, powerlib_domain] theorem coord_injective (hmp : d.mp ≠ 0) : Function.Injective d.coord := by
  intro x y h
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  have h2 := congrArg (· 2) h
  simp [coord, Dynamics.mk3] at h0 h1 h2
  apply state3_ext
  · exact h0
  · exact h2
  · rcases h1 with h1 | h1
    · linarith
    · exact absurd h1 hmp

/-- The correspondence (8) in the source's VSG parameters: `m_p = ω₀/D`, `ω₁ = D/2H` give
`M = 2H/ω₀` and `D_VSM = D/ω₀`. -/
@[tmio M, powerlib_domain] theorem toVSM_vsg {H D ω0 ωc P K0 : ℝ} (hH : H ≠ 0) (hD : D ≠ 0)
    (hω0 : ω0 ≠ 0) :
    (DroopTwoFilter.mk (ω0 / D) (D / (2 * H)) ωc P K0).toVSM =
      ⟨2 * H / ω0, D / ω0, ωc, P, K0⟩ := by
  simp only [toVSM, VSMLPF.mk.injEq, and_true]
  constructor <;> field_simp

/-- The characteristic polynomial of `toVSM`, scaled by `m_p ω₁`, is the droop polynomial
`s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m K`. -/
@[tmio M, powerlib_domain] theorem charPoly_toVSM (hmp : d.mp ≠ 0) (hω1 : d.ω1 ≠ 0) (K : ℝ)
    (s : ℂ) :
    ((d.mp * d.ω1 : ℝ) : ℂ) * ((s + d.toVSM.ωc) * (d.toVSM.M * s ^ 2 + d.toVSM.D * s) +
        d.toVSM.ωc * K) =
      s * (s + d.ω1) * (s + d.ωm) + ((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) := by
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp only [toVSM]
  push_cast
  field_simp

/-- The fast-filter Routh condition of `toVSM` is the droop Hopf margin `κ_H > 0`. -/
@[tmio M, powerlib_domain] theorem routh_iff_hopfMargin_pos (hmp : 0 < d.mp) (hω1 : 0 < d.ω1)
    (hωm : 0 < d.ωm) (K : ℝ) :
    K < d.toVSM.D * d.toVSM.ωc + d.toVSM.D ^ 2 / d.toVSM.M ↔
      0 < 1 - d.mp * K / (d.ω1 + d.ωm) := by
  have h : d.toVSM.D * d.toVSM.ωc + d.toVSM.D ^ 2 / d.toVSM.M = (d.ω1 + d.ωm) / d.mp := by
    simp only [toVSM]
    field_simp
    ring
  rw [h, sub_pos, div_lt_one (by positivity), lt_div_iff₀ hmp, mul_comm]

end DroopTwoFilter

end powerlib.GFM
