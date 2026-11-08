import theorem.Transform.PerUnit
import theorem.Passive.Series
import theorem.Passive.Parallel

/-! # The passive elements in per unit

The per-unit forms of the element laws: on an impedance base `Z_B` and a time base `ω_B`, the
series element `Passive.SeriesRLC` becomes `(R / Z_B, ω_B L / Z_B, S/(ω_B Z_B))` and the parallel
element `Passive.ParallelRLC` becomes `(G Z_B, ω_B C Z_B, Γ Z_B/ω_B)`; the R–L equation, the flux,
the telegrapher equations of a line whose unit length is a series and a parallel element, and the
stored energy of a DC-link capacitor keep their form. The bases and the generic per-unit
identities are `theorem/Transform/PerUnit.lean`.

Scope.
All statements are exact identities between SI and per-unit quantities for explicitly given
nonzero bases; no approximation.

Source: work-sync `theory/T-PU.md` §1.6, §1.10, §1.12.

Results.
* `SeriesRLC.perUnit` (`R̂ = R / Z_B`, `L̂ = ω_B L / Z_B`, the per-unit reactance at `ω_B`,
  `Ŝ = S/(ω_B Z_B)`), `ParallelRLC.perUnit` (`Ĝ = G Z_B`, `Ĉ = ω_B C Z_B`, `Γ̂ = Γ Z_B/ω_B`);
  `ParallelRLC.perUnit_C_eq_susceptance`: without a shunt inductor `Ĉ` is the per-unit
  susceptance at `ω_B`.
* `SeriesRLC.perUnit_conventionA_iff`, `SeriesRLC.perUnit_conventionB_iff`: the R–L equation
  `L i̇ = v − R i` holds iff `L̂ ω_B⁻¹ dî/dt = v̂ − R̂ î` (time in seconds, convention (A)) and iff
  `L̂ dî/dτ = v̂ − R̂ î` (per-unit time `τ = ω_B t`, convention (B)); a series capacitor's voltage
  is part of `v`. `SeriesRLC.flux_perUnit_iff`: with the flux base `Ψ_B = V_B / ω_B`,
  `Ψ = L i ⇔ Ψ̂ = L̂ î`.
* `Line.telegrapher_pu_iff`: per-unit scaling of space (`z_B`), time, voltage and current maps
  telegrapher solutions of a line with unit length `(series, shunt)` to telegrapher solutions of
  the per-unit line `(series.perUnit ω_B (Z_B / z_B), shunt.perUnit ω_B (Z_B z_B))`, and back.
* `ParallelRLC.dcInertia` (`H_dc = C_dc (V_B^dc)² / (2 S_B)`), `ParallelRLC.energy_pu`,
  `ParallelRLC.energy_div_S`: the capacitor energy `ParallelRLC.capacitorEnergy` on the energy
  bases `S_B / ω_B` and `S_B`.

Correction (`T-PU.md` §1.12): the note concludes `Ŵ_dc = H_dc V̂_dc²` for the energy base
`S_B / ω_B`. With that base the exact value is `Ŵ_dc = ω_B H_dc V̂_dc²` (`ParallelRLC.energy_pu`);
`H_dc V̂_dc²` is the energy normalised by `S_B` (in seconds), which is the normalisation under
which `W_kin / S_B = H ω̂²` (`ParallelRLC.energy_div_S`).
-/

noncomputable section

namespace powerlib.Passive

open powerlib.Transform.PerUnit (puField)

/-! ## The series element -/

/-- The element in per unit on the impedance base `Z_B` and time base `ω_B`:
`R̂ = R / Z_B`, `L̂ = ω_B L / Z_B`, `Ŝ = S / (ω_B Z_B)`. -/
def SeriesRLC.perUnit (b : SeriesRLC) (ωB Zb : ℝ) : SeriesRLC :=
  ⟨b.R / Zb, ωB * b.L / Zb, b.S / (ωB * Zb)⟩

/-- Convention (A): `L i̇ = v − R i ⇔ L̂ ω_B⁻¹ (d/dt) î = v̂ − R̂ î` (time in seconds). -/
@[tmio M, powerlib_domain] theorem SeriesRLC.perUnit_conventionA_iff {b : SeriesRLC} {ωB Vb Ib : ℝ}
    (hω : ωB ≠ 0) (hV : Vb ≠ 0) (hI : Ib ≠ 0) {i : ℝ → ℝ} {i' v t : ℝ}
    (hi : HasDerivAt i i' t) :
    b.L * i' = v - b.R * i t ↔
      ∃ ihat', HasDerivAt (fun s => i s / Ib) ihat' t ∧
        (b.perUnit ωB (Vb / Ib)).L * ωB⁻¹ * ihat' =
          v / Vb - (b.perUnit ωB (Vb / Ib)).R * (i t / Ib) := by
  have hd : HasDerivAt (fun s => i s / Ib) (i' / Ib) t := hi.div_const Ib
  have key : (b.perUnit ωB (Vb / Ib)).L * ωB⁻¹ * (i' / Ib) = b.L * i' / Vb := by
    simp only [SeriesRLC.perUnit]
    field_simp
  have keyR : v / Vb - (b.perUnit ωB (Vb / Ib)).R * (i t / Ib) = (v - b.R * i t) / Vb := by
    simp only [SeriesRLC.perUnit]
    field_simp
  constructor
  · intro h
    exact ⟨i' / Ib, hd, by rw [key, keyR, h]⟩
  · rintro ⟨ihat', hd', h⟩
    rw [hd'.unique hd, key, keyR] at h
    exact (div_left_inj' hV).mp h

/-- Convention (B): with per-unit time `τ = ω_B t` and `î(τ) = i(τ/ω_B)/I_B`,
`L i̇ = v − R i ⇔ L̂ dî/dτ = v̂ − R̂ î`. -/
@[tmio M, powerlib_domain] theorem SeriesRLC.perUnit_conventionB_iff {b : SeriesRLC} {ωB Vb Ib : ℝ}
    (hω : ωB ≠ 0) (hV : Vb ≠ 0) (hI : Ib ≠ 0) {i : ℝ → ℝ} {i' v τ : ℝ}
    (hi : HasDerivAt i i' (τ / ωB)) :
    b.L * i' = v - b.R * i (τ / ωB) ↔
      ∃ ihat', HasDerivAt (fun σ => i (σ / ωB) / Ib) ihat' τ ∧
        (b.perUnit ωB (Vb / Ib)).L * ihat' =
          v / Vb - (b.perUnit ωB (Vb / Ib)).R * (i (τ / ωB) / Ib) := by
  have hτ : HasDerivAt (fun σ : ℝ => σ / ωB) ωB⁻¹ τ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id τ).mul_const ωB⁻¹
  have hd : HasDerivAt (fun σ => i (σ / ωB) / Ib) (i' * ωB⁻¹ / Ib) τ := by
    have := (hi.comp τ hτ).div_const Ib
    simpa [Function.comp_def] using this
  have key : (b.perUnit ωB (Vb / Ib)).L * (i' * ωB⁻¹ / Ib) = b.L * i' / Vb := by
    simp only [SeriesRLC.perUnit]
    field_simp
  have keyR : v / Vb - (b.perUnit ωB (Vb / Ib)).R * (i (τ / ωB) / Ib) =
      (v - b.R * i (τ / ωB)) / Vb := by
    simp only [SeriesRLC.perUnit]
    field_simp
  constructor
  · intro h
    exact ⟨_, hd, by rw [key, keyR, h]⟩
  · rintro ⟨ihat', hd', h⟩
    rw [hd'.unique hd, key, keyR] at h
    exact (div_left_inj' hV).mp h

/-- Flux base `Ψ_B = V_B / ω_B`; `Ψ = L i ⇔ Ψ̂ = L̂ î`. -/
@[tmio M, powerlib_domain] theorem SeriesRLC.flux_perUnit_iff {b : SeriesRLC} {ωB Vb Ib ψ i : ℝ}
    (hω : ωB ≠ 0) (hV : Vb ≠ 0) (hI : Ib ≠ 0) :
    ψ = b.L * i ↔ ψ / (Vb / ωB) = (b.perUnit ωB (Vb / Ib)).L * (i / Ib) := by
  simp only [SeriesRLC.perUnit]
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp at h; linear_combination h

/-! ## The parallel element -/

/-- The element in per unit on the impedance base `Z_B` and time base `ω_B`:
`Ĝ = G Z_B`, `Ĉ = ω_B C Z_B`, `Γ̂ = Γ Z_B / ω_B`. -/
def ParallelRLC.perUnit (e : ParallelRLC) (ωB Zb : ℝ) : ParallelRLC :=
  ⟨e.G * Zb, ωB * e.C * Zb, e.Γ * Zb / ωB⟩

/-- Without a shunt inductor `Ĉ` is the per-unit susceptance `ω_B C Z_B` at `ω_B`
(`ParallelRLC.susceptance`), the inverse of the per-unit capacitive reactance magnitude. -/
@[tmio M, powerlib_domain] theorem ParallelRLC.perUnit_C_eq_susceptance {e : ParallelRLC}
    (hΓ : e.Γ = 0) (ωB Zb : ℝ) : (e.perUnit ωB Zb).C = e.susceptance ωB * Zb := by
  simp [ParallelRLC.perUnit, ParallelRLC.susceptance, hΓ]

/-- DC equivalent inertia constant `H_dc = C_dc (V_B^dc)² / (2 S_B)` of a DC-link capacitor. -/
def ParallelRLC.dcInertia (e : ParallelRLC) (VBdc SB : ℝ) : ℝ := e.C * VBdc ^ 2 / (2 * SB)

/-- The capacitor energy on the base `S_B / ω_B`: `Ŵ_dc = ω_B H_dc V̂_dc²` (corrected; the note
omits `ω_B`). -/
@[tmio M, powerlib_domain] theorem ParallelRLC.energy_pu {e : ParallelRLC} {VBdc SB ωB Vdc : ℝ}
    (hV : VBdc ≠ 0)
    (hS : SB ≠ 0) (hω : ωB ≠ 0) :
    e.capacitorEnergy Vdc / (SB / ωB) = ωB * e.dcInertia VBdc SB * (Vdc / VBdc) ^ 2 := by
  simp only [ParallelRLC.capacitorEnergy, ParallelRLC.dcInertia]
  field_simp

/-- The capacitor energy normalised by `S_B` (seconds): `W_dc / S_B = H_dc V̂_dc²`. -/
@[tmio M, powerlib_domain] theorem ParallelRLC.energy_div_S {e : ParallelRLC} {VBdc SB Vdc : ℝ}
    (hV : VBdc ≠ 0)
    (hS : SB ≠ 0) : e.capacitorEnergy Vdc / SB = e.dcInertia VBdc SB * (Vdc / VBdc) ^ 2 := by
  simp only [ParallelRLC.capacitorEnergy, ParallelRLC.dcInertia]
  field_simp

/-! ## The telegrapher equations of a line

A telegrapher solution of a line whose unit length is the branch `series` (`R'`, `L'`) and the
shunt `shunt` (`G'`, `C'`) is a pair of fields `v, i` of `(z, t)` satisfying
`∂v/∂z = −R' i − L' ∂i/∂t`, `∂i/∂z = −G' v − C' ∂v/∂t` at every point, the partial derivatives
being one-variable derivatives of the sections `z' ↦ x(z', t)`, `t' ↦ x(z, t')`. The statements
below spell this condition out. -/

namespace Line

/-- Per-unit scaling maps a telegrapher solution for `(R', L', G', C')` to a telegrapher
solution for `(R' z_B I_B / V_B, ω_B L' z_B I_B / V_B, G' z_B V_B / I_B, ω_B C' z_B V_B / I_B)`. -/
@[tmio M, powerlib_domain] private lemma telegrapher_pu_of {R L G C zb ωB Vb Ib : ℝ} (hz : zb ≠ 0)
    (hω : ωB ≠ 0) (hV : Vb ≠ 0) (hI : Ib ≠ 0) {v i : ℝ → ℝ → ℝ}
    (h : ∀ z t, ∃ vz vt iz it : ℝ,
      HasDerivAt (fun z' => v z' t) vz z ∧ HasDerivAt (fun t' => v z t') vt t ∧
      HasDerivAt (fun z' => i z' t) iz z ∧ HasDerivAt (fun t' => i z t') it t ∧
      vz = -R * i z t - L * it ∧ iz = -G * v z t - C * vt) :
    ∀ z t, ∃ vz vt iz it : ℝ,
      HasDerivAt (fun z' => puField Vb zb ωB v z' t) vz z ∧
      HasDerivAt (fun t' => puField Vb zb ωB v z t') vt t ∧
      HasDerivAt (fun z' => puField Ib zb ωB i z' t) iz z ∧
      HasDerivAt (fun t' => puField Ib zb ωB i z t') it t ∧
      vz = -(R * zb * Ib / Vb) * puField Ib zb ωB i z t - ωB * L * zb * Ib / Vb * it ∧
      iz = -(G * zb * Vb / Ib) * puField Vb zb ωB v z t - ωB * C * zb * Vb / Ib * vt := by
  intro z τ
  obtain ⟨vz, vt, iz, it, hvz, hvt, hiz, hit, e1, e2⟩ := h (zb * z) (τ / ωB)
  have hzl : HasDerivAt (fun z : ℝ => zb * z) zb z := by
    simpa using (hasDerivAt_id z).const_mul zb
  have hτl : HasDerivAt (fun τ : ℝ => τ / ωB) ωB⁻¹ τ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id τ).mul_const ωB⁻¹
  refine ⟨vz * zb / Vb, vt * ωB⁻¹ / Vb, iz * zb / Ib, it * ωB⁻¹ / Ib, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [puField, Function.comp_def] using (hvz.comp z hzl).div_const Vb
  · simpa [puField, Function.comp_def] using (hvt.comp τ hτl).div_const Vb
  · simpa [puField, Function.comp_def] using (hiz.comp z hzl).div_const Ib
  · simpa [puField, Function.comp_def] using (hit.comp τ hτl).div_const Ib
  · simp only [puField]; rw [e1]; field_simp
  · simp only [puField]; rw [e2]; field_simp

/-- Per-unit scaling of space (`z_B`), time (`ω_B`), voltage (`V_B`) and current (`I_B`) maps
telegrapher solutions of the line `(series, shunt)` to telegrapher solutions of the per-unit line
`(series.perUnit ω_B (Z_B / z_B), shunt.perUnit ω_B (Z_B z_B))`, `Z_B = V_B / I_B` (§1.10:
`R̂' = R' z_B / Z_B`, `L̂' = ω_B L' z_B / Z_B`, `Ĝ' = G' z_B Z_B`, `Ĉ' = ω_B C' z_B Z_B`), and back:
the per-unit telegrapher equation has the same form. Both sides are the telegrapher condition of
the section header, for `(v, i)` and for the per-unit fields
`(v̂, î) = (puField V_B z_B ω_B v, puField I_B z_B ω_B i)`. -/
@[tmio M, powerlib_domain] theorem telegrapher_pu_iff {series : SeriesRLC} {shunt : ParallelRLC}
    {zb ωB Vb Ib : ℝ}
    (hz : zb ≠ 0) (hω : ωB ≠ 0) (hV : Vb ≠ 0) (hI : Ib ≠ 0) (v i : ℝ → ℝ → ℝ) :
    (∀ z t, ∃ vz vt iz it : ℝ,
      HasDerivAt (fun z' => v z' t) vz z ∧ HasDerivAt (fun t' => v z t') vt t ∧
      HasDerivAt (fun z' => i z' t) iz z ∧ HasDerivAt (fun t' => i z t') it t ∧
      vz = -series.R * i z t - series.L * it ∧ iz = -shunt.G * v z t - shunt.C * vt) ↔
    ∀ z t, ∃ vz vt iz it : ℝ,
      HasDerivAt (fun z' => puField Vb zb ωB v z' t) vz z ∧
      HasDerivAt (fun t' => puField Vb zb ωB v z t') vt t ∧
      HasDerivAt (fun z' => puField Ib zb ωB i z' t) iz z ∧
      HasDerivAt (fun t' => puField Ib zb ωB i z t') it t ∧
      vz = -(series.perUnit ωB (Vb / Ib / zb)).R * puField Ib zb ωB i z t -
        (series.perUnit ωB (Vb / Ib / zb)).L * it ∧
      iz = -(shunt.perUnit ωB (Vb / Ib * zb)).G * puField Vb zb ωB v z t -
        (shunt.perUnit ωB (Vb / Ib * zb)).C * vt := by
  obtain ⟨R, L, Sc⟩ := series
  obtain ⟨G, C, Γ⟩ := shunt
  simp only [SeriesRLC.perUnit, ParallelRLC.perUnit]
  have e1 : R / (Vb / Ib / zb) = R * zb * Ib / Vb := by field_simp
  have e2 : ωB * L / (Vb / Ib / zb) = ωB * L * zb * Ib / Vb := by field_simp
  have e3 : G * (Vb / Ib * zb) = G * zb * Vb / Ib := by field_simp
  have e4 : ωB * C * (Vb / Ib * zb) = ωB * C * zb * Vb / Ib := by field_simp
  rw [e1, e2, e3, e4]
  refine ⟨telegrapher_pu_of hz hω hV hI, fun h => ?_⟩
  have h' := telegrapher_pu_of (v := puField Vb zb ωB v) (i := puField Ib zb ωB i)
    (inv_ne_zero hz) (inv_ne_zero hω) (inv_ne_zero hV) (inv_ne_zero hI) h
  have hv : puField Vb⁻¹ zb⁻¹ ωB⁻¹ (puField Vb zb ωB v) = v := by
    funext z t; simp only [puField]; field_simp
  have hi : puField Ib⁻¹ zb⁻¹ ωB⁻¹ (puField Ib zb ωB i) = i := by
    funext z t; simp only [puField]; field_simp
  have f1 : R * zb * Ib / Vb * zb⁻¹ * Ib⁻¹ / Vb⁻¹ = R := by field_simp
  have f2 : ωB⁻¹ * (ωB * L * zb * Ib / Vb) * zb⁻¹ * Ib⁻¹ / Vb⁻¹ = L := by field_simp
  have f3 : G * zb * Vb / Ib * zb⁻¹ * Vb⁻¹ / Ib⁻¹ = G := by field_simp
  have f4 : ωB⁻¹ * (ωB * C * zb * Vb / Ib) * zb⁻¹ * Vb⁻¹ / Ib⁻¹ = C := by field_simp
  rw [hv, hi, f1, f2, f3, f4] at h'
  exact h'

end Line

end powerlib.Passive
