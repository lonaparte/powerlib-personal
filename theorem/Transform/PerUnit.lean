import dependencies.Mathlib
import theorem.Attributes
import theorem.Transform.ParkABC

/-! # Per-unit bases and per-unit identities

Exact SI ↔ per-unit identities (foundation).

Scope.
All statements are exact identities between SI quantities and per-unit quantities for
explicitly given bases; there is no physical model or approximation in this module.
The swing equations and the telegrapher system are differential equations along signals; they
are written out in the statements that use them (no separate solution predicate), since
behavioural notions are defined only in the semantic layer (`theorem/Flow/Defs.lean`).

Source: work-sync `theory/T-PU.md` §1.2–§1.6, §1.8–§1.10, §1.12, §1.13.

Results.
* `Base`: a single-phase base pair `{S_B, V_B}` with `I_B = S_B / V_B`, `Z_B = V_B² / S_B`.
  Ohm's law and complex power keep their form in per unit (`ohm_pu_iff`, `power_pu_iff`).
* Three-phase bases (§1.3): `V_LN = V_LL / √3`, `I_B = S_B / (√3 V_LL)`,
  `Z_B = V_LL² / S_B = V_LN² / (S_B / 3)`, `S_B = 3 V_LN I_B`.
* Ideal transformer (§1.4): with `V_B¹ / V_B² = a` and a common `S_B`, per-unit voltages and
  currents are equal on both sides and a referred impedance has the same per-unit value.
* Change of base (§1.5), including the inertia constant; the 600 MVA → 100 MVA example gives
  `8 s ↦ 48 s` (`inertia_change_example`).
* Time base (§1.6): `L̂ = ω_B L / Z_B`, `Ĉ = ω_B C Z_B`, `Ψ_B = V_B / ω_B`; the inductor law in
  conventions (A) and (B) (`inductor_pu_conventionA_iff`, `inductor_pu_conventionB_iff`).
* Swing equation (§1.8–§1.9): the two power forms are exactly equivalent
  (`swingPowerSI_iff_swingPowerPU`); the torque form and the power form differ exactly by
  `(ω̂ − 1)(T̂_m − T̂_e)` (`swingTorque_iff_swingPower`).
* Telegrapher equations (§1.10): per-unit scaling of space, time, voltage and current maps
  solutions to solutions with `R̂' = R' z_B / Z_B`, `L̂' = ω_B L' z_B / Z_B`, `Ĝ' = G' z_B Z_B`,
  `Ĉ' = ω_B C' z_B Z_B` (`telegrapher_pu_iff`).
* DC side (§1.12) and PI gains (§1.13).

Correction (`T-PU.md` §1.12): the note concludes `Ŵ_dc = H_dc V̂_dc²` for the energy base
`S_B / ω_B`. With that base the exact value is `Ŵ_dc = ω_B H_dc V̂_dc²`
(`dcEnergy_pu`); `H_dc V̂_dc²` is the energy normalised by `S_B` (in seconds), which is the
normalisation under which `W_kin / S_B = H ω̂²` (`dcEnergy_div_S`).

Correction (`T-PU.md` §1.13): the boxed convention-(A) formula `k̂ = U_B k` assumes the PI output
is NOT scaled, but the power-loop row of the (A) table, `k̂ = (S_B / I_B) k`, assumes the
output current reference IS scaled by `I_B`. `pi_pu_iff` gives the single exact rule
`k̂_p = (U_B / Y_B) k_p`, `k̂_i = U_B k_i / (Y_B W)` with time factor `W` (`1` in (A), `ω_B` in
(B)) and output base `Y_B` (`1` when the output is left in SI); the two (A) statements are its
instances `Y_B = 1` and `Y_B = I_B`, which agree only when `I_B = 1`.

Correction (`T-PU.md` §1.8–§1.9): the note calls the torque-form swing equation of §1.8 and the
power-form "form 2" of §1.9 the same physics. They coincide only where `ω̂ = 1` or
`T̂_m = T̂_e` (`swingTorque_iff_swingPower`).
-/

noncomputable section
namespace powerlib.Transform.PerUnit

/-! ## Base quadruple (§1.2) -/

/-- Single-phase base pair `{S_B, V_B}` (both positive). -/
structure Base where
  S : ℝ
  V : ℝ
  S_pos : 0 < S
  V_pos : 0 < V

namespace Base

variable (b : Base)

/-- Current base `I_B = S_B / V_B`. -/
def I : ℝ := b.S / b.V

/-- Impedance base `Z_B = V_B² / S_B`. -/
def Z : ℝ := b.V ^ 2 / b.S

@[tmio T, powerlib_foundation] theorem I_pos : 0 < b.I := div_pos b.S_pos b.V_pos

@[tmio T, powerlib_foundation] theorem Z_pos : 0 < b.Z := div_pos (pow_pos b.V_pos 2) b.S_pos

@[tmio T, powerlib_foundation] theorem Z_eq_V_div_I : b.Z = b.V / b.I := by
  have := b.S_pos.ne'; have := b.V_pos.ne'
  simp only [Z, I]; field_simp

@[tmio T, powerlib_foundation] theorem S_eq_V_mul_I : b.S = b.V * b.I := by
  have := b.V_pos.ne'
  simp only [I]; field_simp

/-- Ohm's law keeps its form in per unit: `V = Z I ⇔ V̂ = Ẑ Î`. -/
@[tmio T, powerlib_foundation] theorem ohm_pu_iff (v z i : ℂ) :
    v = z * i ↔ v / b.V = (z / b.Z) * (i / b.I) := by
  have hV : (b.V : ℂ) ≠ 0 := by exact_mod_cast b.V_pos.ne'
  have hZ : (b.Z : ℂ) ≠ 0 := by exact_mod_cast b.Z_pos.ne'
  have hI : (b.I : ℂ) ≠ 0 := by exact_mod_cast b.I_pos.ne'
  have hVZI : (b.V : ℂ) = b.Z * b.I := by
    have h := b.Z_eq_V_div_I
    rw [h]; push_cast; field_simp
  rw [hVZI]
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp at h; linear_combination h

/-- Complex power keeps its form in per unit: `S = V I* ⇔ Ŝ = V̂ Î*`. -/
@[tmio T, powerlib_foundation] theorem power_pu_iff (s v i : ℂ) :
    s = v * star i ↔ s / b.S = (v / b.V) * star (i / b.I) := by
  have hV : (b.V : ℂ) ≠ 0 := by exact_mod_cast b.V_pos.ne'
  have hS : (b.S : ℂ) ≠ 0 := by exact_mod_cast b.S_pos.ne'
  have hI : (b.I : ℂ) ≠ 0 := by exact_mod_cast b.I_pos.ne'
  have hSVI : (b.S : ℂ) = b.V * b.I := by exact_mod_cast b.S_eq_V_mul_I
  have hstar : star (i / (b.I : ℂ)) = star i / b.I := by
    rw [star_div₀, Complex.star_def, Complex.conj_ofReal]
  rw [hstar, hSVI]
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp at h; linear_combination h

end Base

/-! ## Three-phase bases (§1.3) -/

/-- Three-phase base `{S_B, V_LL}`. -/
structure ThreePhaseBase where
  S : ℝ
  VLL : ℝ
  S_pos : 0 < S
  VLL_pos : 0 < VLL

namespace ThreePhaseBase

variable (b : ThreePhaseBase)

/-- Line-to-neutral voltage base `V_LL / √3`. -/
def VLN : ℝ := b.VLL / Real.sqrt 3

/-- Line-current base `S_B / (√3 V_LL)`. -/
def I : ℝ := b.S / (Real.sqrt 3 * b.VLL)

/-- Per-phase (Y-equivalent) impedance base `V_LL² / S_B`. -/
def Z : ℝ := b.VLL ^ 2 / b.S

@[tmio T, powerlib_foundation] private lemma sqrt3_pos : 0 < Real.sqrt 3 := by positivity

/-- `Z_B = V_LL² / S_B = V_LN² / (S_B / 3)`: line and phase pairings give the same base. -/
@[tmio T, powerlib_foundation] theorem Z_eq_phase : b.Z = b.VLN ^ 2 / (b.S / 3) := by
  have := b.S_pos.ne'; have := sqrt3_pos.ne'
  simp only [Z, VLN]
  field_simp
  rw [sqrt3_sq]

/-- `S_B = 3 V_LN I_B` and `S_B = √3 V_LL I_B`. -/
@[tmio T, powerlib_foundation] theorem S_eq_three_VLN_I : b.S = 3 * b.VLN * b.I := by
  have := b.VLL_pos.ne'; have := sqrt3_pos.ne'
  simp only [VLN, I]
  field_simp
  rw [sqrt3_sq]

@[tmio T, powerlib_foundation] theorem Z_eq_VLN_div_I : b.Z = b.VLN / b.I := by
  have := b.VLL_pos.ne'; have := b.S_pos.ne'; have := sqrt3_pos.ne'
  simp only [Z, VLN, I]
  field_simp

end ThreePhaseBase

/-! ## Ideal transformer (§1.4) -/

/-- An ideal transformer of ratio `a = N₁/N₂` disappears in per unit when the two voltage bases
follow the ratio and the power base is common: per-unit voltages and currents agree, and an
impedance referred through the transformer (`Z₁ = a² Z₂`) has the same per-unit value. -/
@[tmio T, powerlib_foundation] theorem transformer_pu {a S V₂ v₂ i₂ z₂ : ℝ} (ha : a ≠ 0) (hS : S ≠ 0)
    (hV : V₂ ≠ 0) :
    let V₁ := a * V₂
    let I₁ := S / V₁
    let I₂ := S / V₂
    let Z₁ := V₁ ^ 2 / S
    let Z₂ := V₂ ^ 2 / S
    (a * v₂) / V₁ = v₂ / V₂ ∧ (i₂ / a) / I₁ = i₂ / I₂ ∧ (a ^ 2 * z₂) / Z₁ = z₂ / Z₂ := by
  intro V₁ I₁ I₂ Z₁ Z₂
  simp only [V₁, I₁, I₂, Z₁, Z₂]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-! ## Change of base (§1.5) -/

/-- `Ẑ_new = Ẑ_old (S_new / S_old) (V_old / V_new)²`. -/
@[tmio T, powerlib_foundation] theorem impedance_change_base {z So Vo Sn Vn : ℝ} (hSo : So ≠ 0)
    (hVo : Vo ≠ 0) (hSn : Sn ≠ 0) (hVn : Vn ≠ 0) :
    z / (Vn ^ 2 / Sn) = (z / (Vo ^ 2 / So)) * (Sn / So) * (Vo / Vn) ^ 2 := by
  field_simp

@[tmio T, powerlib_foundation] theorem voltage_change_base {v Vo Vn : ℝ} (hVo : Vo ≠ 0) (hVn : Vn ≠ 0) :
    v / Vn = (v / Vo) * (Vo / Vn) := by
  field_simp

@[tmio T, powerlib_foundation] theorem current_change_base {i So Vo Sn Vn : ℝ} (hSo : So ≠ 0)
    (hVo : Vo ≠ 0) (hSn : Sn ≠ 0) (hVn : Vn ≠ 0) :
    i / (Sn / Vn) = (i / (So / Vo)) * (So / Sn) * (Vn / Vo) := by
  field_simp

/-- Power on a new base: the rule of `voltage_change_base` (one base quantity in the
denominator). -/
@[tmio T, powerlib_foundation] theorem power_change_base {p So Sn : ℝ} (hSo : So ≠ 0) (hSn : Sn ≠ 0) :
    p / Sn = (p / So) * (So / Sn) :=
  voltage_change_base hSo hSn

/-- Inertia constant `H = W_kin / S_B` on a new power base: `H_new = H_old S_old / S_new`. -/
@[tmio T, powerlib_foundation] theorem inertia_change_base {W So Sn : ℝ} (hSo : So ≠ 0) (hSn : Sn ≠ 0) :
    W / Sn = (W / So) * (So / Sn) :=
  voltage_change_base hSo hSn

/-- The §1.5 example: `8 s` on a 600 MVA machine base is `48 s` on a 100 MVA system base. -/
@[tmio T, powerlib_foundation] theorem inertia_change_example {W : ℝ} (h : W / 600 = 8) : W / 100 = 48 := by
  have hW : W = 4800 := by linarith [(div_eq_iff (by norm_num : (600 : ℝ) ≠ 0)).1 h]
  rw [hW]; norm_num

/-! ## Time base, inductance, capacitance and flux (§1.6) -/

/-- Per-unit inductance `L̂ = ω_B L / Z_B` equals the per-unit reactance at `ω_B`. -/
def puInductance (ωB Zb L : ℝ) : ℝ := ωB * L / Zb

/-- Per-unit capacitance `Ĉ = ω_B C Z_B` (inverse per-unit capacitive reactance at `ω_B`). -/
def puCapacitance (ωB Zb C : ℝ) : ℝ := ωB * C * Zb

@[tmio T, powerlib_foundation] theorem puCapacitance_eq_inv_reactance {ωB Zb C : ℝ} (hω : ωB ≠ 0)
    (hZ : Zb ≠ 0) (hC : C ≠ 0) : puCapacitance ωB Zb C = 1 / ((1 / (ωB * C)) / Zb) := by
  unfold puCapacitance; field_simp

/-- Convention (A) inductor law: `v = L i̇ ⇔ v̂ = L̂ ω_B⁻¹ (d/dt) î` (time in seconds). -/
@[powerlib_foundation] theorem inductor_pu_conventionA_iff {ωB Vb Ib L : ℝ} (hω : ωB ≠ 0)
    (hV : Vb ≠ 0) (hI : Ib ≠ 0) {i : ℝ → ℝ} {i' v t : ℝ} (hi : HasDerivAt i i' t) :
    v = L * i' ↔
      ∃ ihat', HasDerivAt (fun s => i s / Ib) ihat' t ∧
        v / Vb = puInductance ωB (Vb / Ib) L * ωB⁻¹ * ihat' := by
  have hd : HasDerivAt (fun s => i s / Ib) (i' / Ib) t := hi.div_const Ib
  constructor
  · intro h
    refine ⟨i' / Ib, hd, ?_⟩
    rw [h, puInductance]; field_simp
  · rintro ⟨ihat', hd', h⟩
    rw [hd'.unique hd, puInductance] at h
    field_simp at h
    linear_combination h

/-- Convention (B) inductor law: with per-unit time `τ = ω_B t` and `î(τ) = i(τ/ω_B)/I_B`,
`v = L i̇ ⇔ v̂ = L̂ dî/dτ`. -/
@[powerlib_foundation] theorem inductor_pu_conventionB_iff {ωB Vb Ib L : ℝ} (hω : ωB ≠ 0)
    (hV : Vb ≠ 0) (hI : Ib ≠ 0) {i : ℝ → ℝ} {i' v τ : ℝ} (hi : HasDerivAt i i' (τ / ωB)) :
    v = L * i' ↔
      ∃ ihat', HasDerivAt (fun σ => i (σ / ωB) / Ib) ihat' τ ∧
        v / Vb = puInductance ωB (Vb / Ib) L * ihat' := by
  have hτ : HasDerivAt (fun σ : ℝ => σ / ωB) ωB⁻¹ τ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id τ).mul_const ωB⁻¹
  have hd : HasDerivAt (fun σ => i (σ / ωB) / Ib) (i' * ωB⁻¹ / Ib) τ := by
    have := (hi.comp τ hτ).div_const Ib
    simpa [Function.comp_def] using this
  constructor
  · intro h
    refine ⟨_, hd, ?_⟩
    rw [h, puInductance]; field_simp
  · rintro ⟨ihat', hd', h⟩
    rw [hd'.unique hd, puInductance] at h
    field_simp at h
    linear_combination h

/-- Flux base `Ψ_B = V_B / ω_B`; `Ψ = L i ⇔ Ψ̂ = L̂ î`. -/
@[tmio T, powerlib_foundation] theorem flux_pu_iff {ωB Vb Ib L ψ i : ℝ} (hω : ωB ≠ 0) (hV : Vb ≠ 0)
    (hI : Ib ≠ 0) : ψ = L * i ↔ ψ / (Vb / ωB) = puInductance ωB (Vb / Ib) L * (i / Ib) := by
  unfold puInductance
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp at h; linear_combination h

/-! ## Swing equation: power forms and torque form (§1.8–§1.9) -/

/-- The two power forms of §1.9 are exactly equivalent under `ω̂ = ω / ω_s`.

* Form 1 (SI angular speed `ω` in rad/s, per-unit powers, SI time):
  `(2H/ω_s) ω̇ = P̂_m − P̂_e − D̂ (ω − ω_s)/ω_s` at every instant.
* Form 2 (per-unit speed `ω̂`, per-unit powers): `2H dω̂/dt = P̂_m − P̂_e − D̂ (ω̂ − 1)` at
  every instant. -/
@[powerlib_foundation] theorem swingPowerSI_iff_swingPowerPU {H D ωs : ℝ} (hω : ωs ≠ 0)
    (Pm Pe ω : ℝ → ℝ) :
    (∀ t, HasDerivAt ω (ωs / (2 * H) * (Pm t - Pe t - D * ((ω t - ωs) / ωs))) t) ↔
      ∀ t, HasDerivAt (fun t => ω t / ωs)
        (1 / (2 * H) * (Pm t - Pe t - D * (ω t / ωs - 1))) t := by
  constructor
  · intro h t
    convert (h t).div_const ωs using 1
    field_simp
  · intro h t
    have h' := (h t).const_mul ωs
    have hfun : (fun t => ωs * (ω t / ωs)) = ω := funext fun t => by field_simp
    rw [hfun] at h'
    convert h' using 1
    field_simp

/-- Exact relation between the torque form (§1.8) and the power form (§1.9 form 2) with
per-unit power `P̂ = ω̂ T̂`: a torque-form solution solves the power form iff
`(ω̂ − 1)(T̂_m − T̂_e) = 0` at every instant. The forms agree only at `ω̂ = 1` or zero
accelerating torque; otherwise they are different equations.

* Torque form (§1.8): `2H dω̂/dt = T̂_m − T̂_e − D̂ (ω̂ − 1)` at every instant (hypothesis `h`).
* Power form (§1.9 form 2): `2H dω̂/dt = P̂_m − P̂_e − D̂ (ω̂ − 1)` with `P̂ = ω̂ T̂`. -/
@[powerlib_foundation] theorem swingTorque_iff_swingPower {H D : ℝ} (hH : H ≠ 0)
    {Tm Te w : ℝ → ℝ} (h : ∀ t, HasDerivAt w (1 / (2 * H) * (Tm t - Te t - D * (w t - 1))) t) :
    (∀ t, HasDerivAt w (1 / (2 * H) * (w t * Tm t - w t * Te t - D * (w t - 1))) t) ↔
      ∀ t, (w t - 1) * (Tm t - Te t) = 0 := by
  constructor
  · intro hp t
    have he := (h t).unique (hp t)
    field_simp at he
    linear_combination -he
  · intro hz t
    convert h t using 1
    have := hz t
    field_simp
    linear_combination this

/-! ## Telegrapher equations (§1.10)

A telegrapher solution with line parameters `R', L', G', C'` is a pair of fields `v, i` of
`(z, t)` satisfying `∂v/∂z = −R' i − L' ∂i/∂t`, `∂i/∂z = −G' v − C' ∂v/∂t` at every point, the
partial derivatives being one-variable derivatives of the sections `z' ↦ x(z', t)`,
`t' ↦ x(z, t')`. The statements below spell this condition out. -/

/-- Per-unit field `x̂(ẑ, τ) = x(z_B ẑ, τ / ω_B) / X_B`. -/
def puField (Xb zb ωB : ℝ) (x : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z τ => x (zb * z) (τ / ωB) / Xb

/-- Per-unit scaling maps a telegrapher solution for `(R', L', G', C')` to a telegrapher
solution for `(R' z_B I_B / V_B, ω_B L' z_B I_B / V_B, G' z_B V_B / I_B, ω_B C' z_B V_B / I_B)`. -/
@[powerlib_foundation] private lemma telegrapher_pu_of {R L G C zb ωB Vb Ib : ℝ} (hz : zb ≠ 0)
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
telegrapher solutions to telegrapher solutions with the §1.10 per-unit line parameters
`R̂' = R' z_B / Z_B`, `L̂' = ω_B L' z_B / Z_B`, `Ĝ' = G' z_B Z_B`, `Ĉ' = ω_B C' z_B Z_B`
(`Z_B = V_B / I_B`), and back: the per-unit telegrapher equation has the same form. Both sides
are the telegrapher condition of the section header, for `(v, i)` and for the per-unit fields
`(v̂, î) = (puField V_B z_B ω_B v, puField I_B z_B ω_B i)`. -/
@[powerlib_foundation] theorem telegrapher_pu_iff {R L G C zb ωB Vb Ib : ℝ} (hz : zb ≠ 0)
    (hω : ωB ≠ 0) (hV : Vb ≠ 0) (hI : Ib ≠ 0) (v i : ℝ → ℝ → ℝ) :
    (∀ z t, ∃ vz vt iz it : ℝ,
      HasDerivAt (fun z' => v z' t) vz z ∧ HasDerivAt (fun t' => v z t') vt t ∧
      HasDerivAt (fun z' => i z' t) iz z ∧ HasDerivAt (fun t' => i z t') it t ∧
      vz = -R * i z t - L * it ∧ iz = -G * v z t - C * vt) ↔
    ∀ z t, ∃ vz vt iz it : ℝ,
      HasDerivAt (fun z' => puField Vb zb ωB v z' t) vz z ∧
      HasDerivAt (fun t' => puField Vb zb ωB v z t') vt t ∧
      HasDerivAt (fun z' => puField Ib zb ωB i z' t) iz z ∧
      HasDerivAt (fun t' => puField Ib zb ωB i z t') it t ∧
      vz = -(R * zb / (Vb / Ib)) * puField Ib zb ωB i z t - ωB * L * zb / (Vb / Ib) * it ∧
      iz = -(G * zb * (Vb / Ib)) * puField Vb zb ωB v z t - ωB * C * zb * (Vb / Ib) * vt := by
  have e1 : R * zb / (Vb / Ib) = R * zb * Ib / Vb := by field_simp
  have e2 : ωB * L * zb / (Vb / Ib) = ωB * L * zb * Ib / Vb := by field_simp
  have e3 : G * zb * (Vb / Ib) = G * zb * Vb / Ib := by field_simp
  have e4 : ωB * C * zb * (Vb / Ib) = ωB * C * zb * Vb / Ib := by field_simp
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

/-! ## Converter DC side (§1.12) -/

/-- DC equivalent inertia constant `H_dc = C_dc (V_B^dc)² / (2 S_B)`. -/
def dcInertia (Cdc VBdc SB : ℝ) : ℝ := Cdc * VBdc ^ 2 / (2 * SB)

/-- DC energy on the base `S_B / ω_B`: `Ŵ_dc = ω_B H_dc V̂_dc²` (corrected; the note omits
`ω_B`). -/
@[tmio T, powerlib_foundation] theorem dcEnergy_pu {Cdc VBdc SB ωB Vdc : ℝ} (hV : VBdc ≠ 0) (hS : SB ≠ 0)
    (hω : ωB ≠ 0) :
    (1 / 2 * Cdc * Vdc ^ 2) / (SB / ωB) = ωB * dcInertia Cdc VBdc SB * (Vdc / VBdc) ^ 2 := by
  unfold dcInertia; field_simp

/-- DC energy normalised by `S_B` (seconds): `W_dc / S_B = H_dc V̂_dc²`. -/
@[tmio T, powerlib_foundation] theorem dcEnergy_div_S {Cdc VBdc SB Vdc : ℝ} (hV : VBdc ≠ 0) (hS : SB ≠ 0) :
    (1 / 2 * Cdc * Vdc ^ 2) / SB = dcInertia Cdc VBdc SB * (Vdc / VBdc) ^ 2 := by
  unfold dcInertia; field_simp

/-- Half-bridge modulation `v_conv = m V_dc / 2` in per unit:
`v̂_conv = m (V̂_dc / 2)(V_B^dc / V_B^ac)`. -/
@[tmio T, powerlib_foundation] theorem modulation_pu {m Vdc VBdc VBac : ℝ} (hdc : VBdc ≠ 0)
    (hac : VBac ≠ 0) : (m * Vdc / 2) / VBac = m * ((Vdc / VBdc) / 2) * (VBdc / VBac) := by
  field_simp

/-! ## PI controller gains (§1.13) -/

/-- Exact per-unit PI rule. Input base `U_B`, output base `Y_B` (`1` if the output stays in SI),
time factor `W` (`1` in convention (A), `ω_B` in (B), `ŝ = s / W`):
`y = (k_p + k_i/s) u ⇔ ŷ = (k̂_p + k̂_i/ŝ) û` with `k̂_p = (U_B/Y_B) k_p`,
`k̂_i = U_B k_i / (Y_B W)`. -/
@[tmio T, powerlib_foundation] theorem pi_pu_iff {UB YB W kp ki : ℝ} (hU : UB ≠ 0) (hY : YB ≠ 0)
    (hW : W ≠ 0) {s : ℂ} (hs : s ≠ 0) (u y : ℂ) :
    y = (kp + ki / s) * u ↔
      y / YB = (((UB / YB * kp : ℝ) : ℂ) + ((UB * ki / (YB * W) : ℝ) : ℂ) / (s / W)) *
        (u / UB) := by
  have hU' : (UB : ℂ) ≠ 0 := by exact_mod_cast hU
  have hY' : (YB : ℂ) ≠ 0 := by exact_mod_cast hY
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  push_cast
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp at h; field_simp; linear_combination h

/-- The rule is forced: a per-unit PI reproduces the SI PI for every `s ≠ 0` only with these
gains. -/
@[tmio T, powerlib_foundation] theorem pi_gains_unique {UB YB W kp ki kp' ki' : ℝ} (hU : UB ≠ 0)
    (hY : YB ≠ 0) (hW : W ≠ 0)
    (h : ∀ s : ℂ, s ≠ 0 → (kp + ki / s : ℂ) = YB / UB * ((kp' : ℂ) + ki' / (s / W))) :
    kp' = UB / YB * kp ∧ ki' = UB * ki / (YB * W) := by
  have h1 := h 1 one_ne_zero
  have h2 := h 2 two_ne_zero
  have hU' : (UB : ℂ) ≠ 0 := by exact_mod_cast hU
  have hY' : (YB : ℂ) ≠ 0 := by exact_mod_cast hY
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  field_simp at h1 h2
  have hki : (ki : ℂ) * UB = YB * ki' * W := by linear_combination 2 * h1 - h2
  have hkp : (kp : ℂ) * UB = YB * kp' := by linear_combination h2 - h1
  have hki' : ki * UB = YB * ki' * W := by exact_mod_cast hki
  have hkp' : kp * UB = YB * kp' := by exact_mod_cast hkp
  constructor
  · field_simp; linear_combination -hkp'
  · field_simp; linear_combination -hki'

/-- PLL in convention (B): `U_B = V_B`, `Y_B = ω_B`, `W = ω_B` gives
`k̂_p = V_B k_p / ω_B`, `k̂_i = V_B k_i / ω_B²` (the §1.13.2 table). -/
@[tmio T, powerlib_foundation] theorem pll_conventionB_gains (VB ωB kp ki : ℝ) :
    VB / ωB * kp = VB * kp / ωB ∧ VB * ki / (ωB * ωB) = VB * ki / ωB ^ 2 := by
  constructor <;> ring

/-- The two convention-(A) statements for the power loop (`U_B = S_B`): the boxed formula
(`Y_B = 1`) and the table row (`Y_B = I_B`) give the same proportional gain only if
`I_B = 1` (for a nonzero SI gain). -/
@[tmio T, powerlib_foundation] theorem pc_conventionA_rows_agree_iff {SB IB kp : ℝ} (hS : SB ≠ 0)
    (hI : IB ≠ 0) (hk : kp ≠ 0) : SB / 1 * kp = SB / IB * kp ↔ IB = 1 := by
  constructor
  · intro h
    rw [div_one] at h
    have h2 : SB / IB * kp * IB = SB * kp := by field_simp
    have : SB * kp * (IB - 1) = 0 := by linear_combination IB * h + h2
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (mul_ne_zero hS hk)
    · linarith
  · intro h; rw [h]

end powerlib.Transform.PerUnit
