import theorem.Transform.PerUnit
import theorem.Passive.Series
import theorem.Passive.Parallel
import theorem.Passive.Line.Bergeron

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
* `Line.telegrapher_pu_iff`: per-unit scaling of space (`z_B > 0`), time, voltage and current maps
  telegrapher solutions (`Line.IsTelegrapherSolution`) of a line with unit length
  `(series, shunt)` on `[a, b] × ℝ` to telegrapher solutions of the per-unit line
  `(series.perUnit ω_B (Z_B / z_B), shunt.perUnit ω_B (Z_B z_B))` on `[a/z_B, b/z_B] × ℝ`, and
  back.
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

The telegrapher solutions are those of `theorem/Passive/Line/Bergeron.lean`
(`Line.IsTelegrapherSolution`: partial derivatives within the strip `[a, b] × ℝ`). Per-unit
scaling of space maps the strip `[a, b] × ℝ` to `[a/z_B, b/z_B] × ℝ`. -/

namespace Line

/-- Per-unit scaling maps a telegrapher solution on `[a, b] × ℝ` to one on `[a/z_B, b/z_B] × ℝ`
of any line with the scaled constants
`(R' z_B I_B / V_B, ω_B L' z_B I_B / V_B, G' z_B V_B / I_B, ω_B C' z_B V_B / I_B)`. -/
@[tmio M, powerlib_domain] private lemma telegrapher_pu_of {series series' : SeriesRLC}
    {shunt shunt' : ParallelRLC} {a b zb ωB Vb Ib : ℝ} (hz : 0 < zb) (hω : ωB ≠ 0)
    (hV : Vb ≠ 0) (hI : Ib ≠ 0) (hS : series'.S = 0) (hΓ : shunt'.Γ = 0)
    (hR : series'.R = series.R * zb * Ib / Vb) (hL : series'.L = ωB * series.L * zb * Ib / Vb)
    (hG : shunt'.G = shunt.G * zb * Vb / Ib) (hC : shunt'.C = ωB * shunt.C * zb * Vb / Ib)
    {v i : ℝ × ℝ → ℝ} (h : IsTelegrapherSolution series shunt a b v i) :
    IsTelegrapherSolution series' shunt' (a / zb) (b / zb) (puField Vb zb ωB v)
      (puField Ib zb ωB i) := by
  obtain ⟨-, -, vx, vt, ix, it, hsol⟩ := h
  have hmaps : Set.MapsTo (fun q : ℝ × ℝ => (zb * q.1, q.2 / ωB)) (PDE.strip (a / zb) (b / zb))
      (PDE.strip a b) := fun q hq =>
    ⟨⟨show a ≤ zb * q.1 by rw [mul_comm]; exact (div_le_iff₀ hz).mp hq.1.1,
      show zb * q.1 ≤ b by rw [mul_comm]; exact (le_div_iff₀ hz).mp hq.1.2⟩, trivial⟩
  refine ⟨hS, hΓ, fun q => vx (zb * q.1, q.2 / ωB) * zb / Vb,
    fun q => vt (zb * q.1, q.2 / ωB) / ωB / Vb, fun q => ix (zb * q.1, q.2 / ωB) * zb / Ib,
    fun q => it (zb * q.1, q.2 / ωB) / ωB / Ib, fun q hq => ?_⟩
  have hσ : HasFDerivAt (fun q : ℝ × ℝ => (zb * q.1, q.2 / ωB))
      ((zb • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ωB⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
    (hasFDerivAt_fst.const_mul zb).prodMk (hasFDerivAt_snd.mul_const ωB⁻¹)
  obtain ⟨hv, hi, hkvl, hkcl⟩ := hsol _ (hmaps hq)
  refine ⟨((hv.comp q hσ.hasFDerivWithinAt hmaps).mul_const Vb⁻¹).congr_fderiv
      (by ext <;> simp <;> ring),
    ((hi.comp q hσ.hasFDerivWithinAt hmaps).mul_const Ib⁻¹).congr_fderiv
      (by ext <;> simp <;> ring), ?_, ?_⟩
  · simp only [puField]
    rw [hR, hL, hkvl]
    field_simp
  · simp only [puField]
    rw [hG, hC, hkcl]
    field_simp

/-- Per-unit scaling of space (`z_B > 0`), time (`ω_B`), voltage (`V_B`) and current (`I_B`)
maps telegrapher solutions of the line `(series, shunt)` on `[a, b] × ℝ` to telegrapher
solutions of the per-unit line `(series.perUnit ω_B (Z_B / z_B), shunt.perUnit ω_B (Z_B z_B))`,
`Z_B = V_B / I_B`, on `[a/z_B, b/z_B] × ℝ` (§1.10: `R̂' = R' z_B / Z_B`,
`L̂' = ω_B L' z_B / Z_B`, `Ĝ' = G' z_B Z_B`, `Ĉ' = ω_B C' z_B Z_B`), and back: the per-unit
telegrapher equation has the same form, for the per-unit fields
`(v̂, î) = (puField V_B z_B ω_B v, puField I_B z_B ω_B i)`. -/
@[tmio M, powerlib_domain] theorem telegrapher_pu_iff {series : SeriesRLC} {shunt : ParallelRLC}
    {a b zb ωB Vb Ib : ℝ} (hz : 0 < zb) (hω : ωB ≠ 0) (hV : Vb ≠ 0) (hI : Ib ≠ 0)
    (v i : ℝ × ℝ → ℝ) :
    IsTelegrapherSolution series shunt a b v i ↔
      IsTelegrapherSolution (series.perUnit ωB (Vb / Ib / zb)) (shunt.perUnit ωB (Vb / Ib * zb))
        (a / zb) (b / zb) (puField Vb zb ωB v) (puField Ib zb ωB i) := by
  have hz' := hz.ne'
  constructor
  · intro h
    obtain ⟨hS, hΓ, -⟩ := id h
    refine telegrapher_pu_of hz hω hV hI ?_ ?_ ?_ ?_ ?_ ?_ h <;>
      simp only [SeriesRLC.perUnit, ParallelRLC.perUnit, hS, hΓ, zero_div, zero_mul] <;>
      field_simp
  · intro h
    obtain ⟨hS, hΓ, -⟩ := id h
    have h' := telegrapher_pu_of (series' := series) (shunt' := shunt) (inv_pos.mpr hz)
      (inv_ne_zero hω) (inv_ne_zero hV) (inv_ne_zero hI)
      (by simpa [SeriesRLC.perUnit, hω, hV, hI, hz'] using hS)
      (by simpa [ParallelRLC.perUnit, hω, hV, hI, hz'] using hΓ)
      (by simp only [SeriesRLC.perUnit]; field_simp)
      (by simp only [SeriesRLC.perUnit]; field_simp)
      (by simp only [ParallelRLC.perUnit]; field_simp)
      (by simp only [ParallelRLC.perUnit]; field_simp) h
    have ha : a / zb / zb⁻¹ = a := by field_simp
    have hb : b / zb / zb⁻¹ = b := by field_simp
    have hv : puField Vb⁻¹ zb⁻¹ ωB⁻¹ (puField Vb zb ωB v) = v := by
      funext q; simp only [puField]; field_simp
    have hi : puField Ib⁻¹ zb⁻¹ ωB⁻¹ (puField Ib zb ωB i) = i := by
      funext q; simp only [puField]; field_simp
    rwa [ha, hb, hv, hi] at h'

end Line

end powerlib.Passive
