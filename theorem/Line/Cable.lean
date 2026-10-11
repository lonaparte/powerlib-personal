import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Trigonometric

/-! # Single-core coaxial cable: geometric identities and the two-loop port relation

Source: work-sync `theory/T-cable.md` §1.2.3, §1.4, §1.5, §1.6, §1.8, §1.8.1, §1.9, §2.3.

Model boundary.
* Single-phase concentric cable: core radius `r_c`, insulation outer radius `r_in`
  (= screen inner radius), screen outer radius `r_sh`, jacket outer radius `r_j`; all
  radii positive and increasing. Loop quantities (Wedepohl–Wilcox): loop 1 = core–screen,
  loop 2 = screen–earth; currents along `+x` (through convention, conventions §D10).
* Quasi-TEM, uniform, constant-per-frequency parameters; Carson earth-return depth `D_e`
  enters only through `ln(D_e/·)`.
* §1.8 port relation: ideal-screen limit `η → 0` (the loop impedance matrix is diagonal, so
  the two loops propagate independently with `(γₖ, Z_{ck})`), single-point bonding: screen
  open at end 1 (`I_s(0) = 0`), bonded through `R_b` at end 2, core loaded by `Z_L` at end 2.
  The theorems are algebraic identities of this closed-form model; the `O(η)` error with
  respect to the coupled 4-state model is *not* formalized.
* Tubular-conductor (Schelkunoff/Bessel) impedances and their high/low-frequency limits are
  not formalized here (they need Bessel functions); the Wedepohl–Wilcox formulas are
  engineering approximations, not theorems.

Results.
* GMR: `ln D_s(r_in, r_sh) → ln r_sh - 1/4` as `r_in → 0` (solid conductor) and
  `→ ln r_sh` as `r_in → r_sh` (thin tube; the two `O(1/ε)` terms cancel exactly);
  `D_s` is homogeneous of degree one, i.e. the expanded coefficients satisfy `A + B = 1`
  (the hidden reference distance of a bare logarithm).
* `ln(r_j/r_sh) + ln(D_e/r_j) = ln(D_e/r_sh)`: `r_j` cancels in `Z₂₂`.
* Naive ladder ⇒ `η ≡ 1` and no ladder represents a loop matrix with `η ≠ 1`.
* `Z₁₁^ext Y₁ = -ω²μ₀ε₀ε_r` independently of the geometry (lossless dielectric, real `ε_r`).
* Closed form `I_c(0) D̂ = I_c(ℓ) N̂`; `R_b = 0` cancellation; `N̂` on `D̂ = 0` and the
  load at which the pole is cancelled.
* `Y₂ = 0` ⇒ `det(ZY) = 0` and a size-2 Jordan chain for the zero mode.
* Cable charging power `Q = -ωC₁ℓ|V|²` (absorb-positive) from `S = V I*`; lumped `LC`
  resonance at `ω² L C = 1`.
-/

noncomputable section
namespace powerlib.Line.Cable
open Filter Topology Real

/-! ## Geometric mean radius -/

/-- `ln D_s` of a tube with inner radius `a` and outer radius `b` (§1.2.3). -/
def lnGMR (a b : ℝ) : ℝ :=
  Real.log b - a ^ 4 / (b ^ 2 - a ^ 2) ^ 2 * Real.log (b / a) + a ^ 2 / (2 * (b ^ 2 - a ^ 2)) - 1 / 4

/-- Solid-conductor limit: `ln D_s → ln r_sh - 1/4` (`D_s → e^{-1/4} r_sh`) as `r_in → 0⁺`. -/
@[powerlib_foundation] theorem lnGMR_solid_limit {b : ℝ} (hb : 0 < b) :
    Tendsto (fun a => lnGMR a b) (𝓝[>] 0) (𝓝 (Real.log b - 1 / 4)) := by
  have hlog : Tendsto (fun a : ℝ => Real.log a * a ^ (4 : ℕ)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := (4 : ℝ)) (by norm_num)
    refine h.congr fun a => ?_
    have e : a ^ (4 : ℝ) = a ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast a 4
    rw [e]
  have hpow : Tendsto (fun a : ℝ => a ^ 4) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => a ^ 4) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 4).tendsto (0 : ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun a : ℝ => a ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => a ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun a : ℝ => (b ^ 2 - a ^ 2)) (𝓝[>] 0) (𝓝 (b ^ 2)) := by
    simpa using hsq.const_sub (b ^ 2)
  have hb2 : b ^ 2 ≠ 0 := by positivity
  -- `a⁴ ln(b/a) = a⁴ ln b - a⁴ ln a → 0`
  have hterm : Tendsto (fun a : ℝ => a ^ 4 * Real.log (b / a)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun a : ℝ => a ^ 4 * Real.log b - Real.log a * a ^ 4) (𝓝[>] 0)
        (𝓝 (0 * Real.log b - 0)) := (hpow.mul_const _).sub hlog
    rw [zero_mul, sub_zero] at h1
    apply h1.congr'
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    rw [Real.log_div hb.ne' ha.ne']
    ring
  have hfull : Tendsto (fun a => Real.log b - a ^ 4 * Real.log (b / a) / (b ^ 2 - a ^ 2) ^ 2 +
      a ^ 2 / (2 * (b ^ 2 - a ^ 2)) - 1 / 4) (𝓝[>] 0)
      (𝓝 (Real.log b - 0 / (b ^ 2) ^ 2 + 0 / (2 * b ^ 2) - 1 / 4)) := by
    refine (((tendsto_const_nhds.sub (hterm.div (hden.pow 2) (pow_ne_zero 2 hb2))).add
      (hsq.div (hden.const_mul 2) (mul_ne_zero two_ne_zero hb2))).sub tendsto_const_nhds)
  simp only [zero_div, sub_zero, add_zero] at hfull
  apply hfull.congr'
  filter_upwards with a
  simp only [lnGMR]
  ring

/-- Thin-tube algebra: with `u = 1 - (a/b)²` the GMR correction equals
`-u²/4 + (1-u)²/(2u²) E`, where `E = ln(1-u) + u + u²/2`. -/
@[powerlib_foundation] theorem lnGMR_thin_identity {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    let u := 1 - (a / b) ^ 2
    lnGMR a b - Real.log b =
      -u ^ 2 / 4 + (1 - u) ^ 2 / (2 * u ^ 2) * (Real.log (1 - u) + u + u ^ 2 / 2) := by
  intro u
  have hb : 0 < b := ha.trans hab
  have hu : u = (b ^ 2 - a ^ 2) / b ^ 2 := by simp only [u]; field_simp
  have hu0 : 0 < b ^ 2 - a ^ 2 := by nlinarith
  have h1u : 1 - u = (a / b) ^ 2 := by simp only [u]; ring
  have hlog : Real.log (b / a) = -(Real.log (1 - u)) / 2 := by
    rw [h1u, Real.log_pow, Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' ha.ne']
    push_cast; ring
  simp only [lnGMR]
  rw [hlog, h1u, hu]
  field_simp
  ring

/-- Thin-tube limit: `ln D_s → ln r_sh` as `r_in → r_sh⁻`; the `O(1/ε)` terms cancel exactly. -/
@[powerlib_foundation] theorem lnGMR_thin_limit {b : ℝ} (hb : 0 < b) :
    Tendsto (fun a => lnGMR a b) (𝓝[<] b) (𝓝 (Real.log b)) := by
  -- bound: `|lnGMR a b - ln b| ≤ u²/4 + u/2` with `u = 1 - (a/b)² → 0`
  have hu : Tendsto (fun a : ℝ => 1 - (a / b) ^ 2) (𝓝[<] b) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => 1 - (a / b) ^ 2) (𝓝 b) (𝓝 (1 - (b / b) ^ 2)) :=
      ((continuous_const.sub ((continuous_id.div_const b).pow 2)).tendsto b)
    rw [div_self hb.ne', one_pow, sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hbound : Tendsto (fun a : ℝ => (1 - (a / b) ^ 2) ^ 2 / 4 + (1 - (a / b) ^ 2) / 2)
      (𝓝[<] b) (𝓝 (0 ^ 2 / 4 + 0 / 2)) := ((hu.pow 2).div_const 4).add (hu.div_const 2)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero]
    at hbound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hbound
  have hpos : ∀ᶠ a in 𝓝[<] b, 0 < a ∧ a < b ∧ 1 - (a / b) ^ 2 < 1 / 2 := by
    have h1 : ∀ᶠ a in 𝓝[<] b, a < b := self_mem_nhdsWithin
    have h2 : ∀ᶠ a in 𝓝[<] b, 0 < a :=
      (lt_mem_nhds (half_lt_self hb)).filter_mono nhdsWithin_le_nhds |>.mono fun a ha =>
        (half_pos hb).trans ha
    have h3 : ∀ᶠ a in 𝓝[<] b, 1 - (a / b) ^ 2 < 1 / 2 := hu (gt_mem_nhds (by norm_num))
    filter_upwards [h1, h2, h3] with a ha1 ha2 ha3 using ⟨ha2, ha1, ha3⟩
  filter_upwards [hpos] with a ⟨ha, hab, hsmall⟩
  have hid := lnGMR_thin_identity ha hab
  simp only at hid
  set u := 1 - (a / b) ^ 2 with hudef
  have hb' : 0 < b := ha.trans hab
  have hupos : 0 < u := by
    have : a / b < 1 := (div_lt_one hb').mpr hab
    have : 0 < a / b := div_pos ha hb'
    nlinarith
  have hE := Real.abs_log_sub_add_sum_range_le (x := u) (by rw [abs_of_pos hupos]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one] at hE
  rw [abs_of_pos hupos] at hE
  have hE' : |Real.log (1 - u) + u + u ^ 2 / 2| ≤ u ^ 3 / (1 - u) := by
    have : u / (0 + 1) + u ^ (1 + 1) / (1 + 1) + Real.log (1 - u) =
        Real.log (1 - u) + u + u ^ 2 / 2 := by norm_num; ring
    rw [← this]
    simpa [pow_succ] using hE
  rw [Real.norm_eq_abs, hid]
  have h1u : 0 < 1 - u := by linarith
  calc |-u ^ 2 / 4 + (1 - u) ^ 2 / (2 * u ^ 2) * (Real.log (1 - u) + u + u ^ 2 / 2)|
      ≤ |-u ^ 2 / 4| + |(1 - u) ^ 2 / (2 * u ^ 2)| * |Real.log (1 - u) + u + u ^ 2 / 2| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ u ^ 2 / 4 + (1 - u) ^ 2 / (2 * u ^ 2) * (u ^ 3 / (1 - u)) := by
        gcongr
        · rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg u)]; norm_num
        · rw [abs_of_nonneg (by positivity)]
    _ = u ^ 2 / 4 + u / 2 * (1 - u) := by field_simp
    _ ≤ u ^ 2 / 4 + u / 2 := by nlinarith

/-- Homogeneity: `ln D_s(λa, λb) = ln λ + ln D_s(a, b)` — the signature `A + B = 1` of a
`ln(D_ref/D_s)` inductance; a bare logarithm silently fixes `D_ref` = one length unit. -/
@[powerlib_foundation] theorem lnGMR_smul {a b lam : ℝ} (ha : 0 < a) (hab : a < b) (hl : 0 < lam) :
    lnGMR (lam * a) (lam * b) = Real.log lam + lnGMR a b := by
  have hb : 0 < b := ha.trans hab
  have hden : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
  simp only [lnGMR]
  rw [Real.log_mul hl.ne' hb.ne', mul_div_mul_left _ _ hl.ne']
  have : (lam * b) ^ 2 - (lam * a) ^ 2 = lam ^ 2 * (b ^ 2 - a ^ 2) := by ring
  rw [this]
  field_simp
  ring

/-- Expanded form `ln D_s = A ln r_sh + B ln r_in + C'` with `A + B = 1`. -/
@[powerlib_foundation] theorem lnGMR_expansion {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let k := a ^ 4 / (b ^ 2 - a ^ 2) ^ 2
    lnGMR a b = (1 - k) * Real.log b + k * Real.log a +
      (a ^ 2 / (2 * (b ^ 2 - a ^ 2)) - 1 / 4) ∧ (1 - k) + k = 1 := by
  intro k
  refine ⟨?_, by ring⟩
  simp only [lnGMR, k]
  rw [Real.log_div hb.ne' ha.ne']
  ring

/-- `r_j` cancels in the screen–earth loop inductance: `ln(r_j/r_sh) + ln(D_e/r_j) = ln(D_e/r_sh)`. -/
@[powerlib_foundation] theorem log_jacket_cancel {rsh rj De : ℝ} (hsh : 0 < rsh) (hj : 0 < rj)
    (hDe : 0 < De) : Real.log (rj / rsh) + Real.log (De / rj) = Real.log (De / rsh) := by
  rw [Real.log_div hj.ne' hsh.ne', Real.log_div hDe.ne' hj.ne', Real.log_div hDe.ne' hsh.ne']
  ring

/-! ## Naive ladder topology -/

/-- Loop impedance matrix of the naive ladder (core branch + shared screen branch). -/
def ladderZ (Zcore Zsh : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![Zcore + Zsh, -Zsh; -Zsh, Zsh]

/-- **Structural negative result**: every naive ladder has screening ratio `η = |Z₁₂/Z₂₂| = 1`. -/
@[powerlib_foundation] theorem ladder_eta_eq_one (Zcore Zsh : ℂ) (h : Zsh ≠ 0) :
    ‖ladderZ Zcore Zsh 0 1 / ladderZ Zcore Zsh 1 1‖ = 1 := by
  simp [ladderZ, neg_div, div_self h]

/-- No naive ladder reproduces a loop matrix with `η ≠ 1` (e.g. a real cable, `η ≈ 10⁻³`). -/
@[powerlib_foundation] theorem not_ladder_of_eta_ne_one {Z : Matrix (Fin 2) (Fin 2) ℂ}
    (hZ : Z 1 1 ≠ 0) (hη : ‖Z 0 1 / Z 1 1‖ ≠ 1) : ¬ ∃ Zcore Zsh, ladderZ Zcore Zsh = Z := by
  rintro ⟨Zcore, Zsh, rfl⟩
  apply hη
  apply ladder_eta_eq_one
  simpa [ladderZ] using hZ

/-- The ladder's loop-1 entry double-counts the screen branch: `Z₁₁ = Z_core + Z_sh`. -/
@[powerlib_foundation] theorem ladder_Z11 (Zcore Zsh : ℂ) :
    ladderZ Zcore Zsh 0 0 = Zcore + Zsh := by simp [ladderZ]

/-! ## Coaxial mode -/

/-- Geometry independence of the coaxial mode (lossless dielectric, real `ε_r`):
`(jω μ₀/(2π) ln(r_in/r_c)) (jω 2π ε₀ ε_r / ln(r_in/r_c)) = -ω² μ₀ ε₀ ε_r`. -/
@[powerlib_foundation] theorem coax_Z11ext_mul_Y1 {ω μ₀ ε₀ εr rc rin : ℝ} (hrc : 0 < rc)
    (hrin : rc < rin) :
    (Complex.I * ω * μ₀ / (2 * π) * Real.log (rin / rc) : ℂ) *
      (Complex.I * ω * (2 * π * ε₀ * εr) / Real.log (rin / rc)) = -(ω ^ 2 * μ₀ * ε₀ * εr : ℝ) := by
  have hlog : Real.log (rin / rc) ≠ 0 := by
    have : 1 < rin / rc := (one_lt_div hrc).mpr hrin
    exact (Real.log_pos this).ne'
  have hlogc : (Real.log (rin / rc) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/-! ## Two-loop port relation in the ideal-screen limit -/

/-- `A = cosh γ₂ℓ + R_b sinh γ₂ℓ / Z_{c2}` (loop 2 seen from end 1 with `R_b` at end 2). -/
def Aterm (c₂ s₂ Y₂ Rb : ℂ) : ℂ := c₂ + Rb * s₂ * Y₂

/-- `N̂ = A (cosh γ₁ℓ + Z_L sinh γ₁ℓ / Z_{c1}) + R_b cosh γ₂ℓ sinh γ₁ℓ / Z_{c1}`. -/
def Nhat (c₁ s₁ Y₁ c₂ s₂ Y₂ Rb ZL : ℂ) : ℂ :=
  Aterm c₂ s₂ Y₂ Rb * (c₁ + ZL * s₁ * Y₁) + Rb * c₂ * s₁ * Y₁

/-- `D̂ = A + R_b sinh γ₁ℓ / Z_{c1}`; it does not involve `Z_L`. -/
def Dhat (_c₁ s₁ Y₁ c₂ s₂ Y₂ Rb : ℂ) : ℂ := Aterm c₂ s₂ Y₂ Rb + Rb * s₁ * Y₁

/-- **Closed-form port relation** (§1.8). Loop `k` propagates with `cₖ = cosh γₖℓ`,
`sₖ = sinh γₖℓ`, `Z_{ck}` (`Yₖ = 1/Z_{ck}`); sending-end data `U₁(0) = a₁`, `U₂(0) = a₂`,
`I₁(0) = I₂(0) = I₀` (screen open at end 1). If the receiving end satisfies the bonding
condition `U₂(ℓ) = R_b (I₂(ℓ) - I₁(ℓ))` and the load condition `U₁(ℓ) + U₂(ℓ) = Z_L I₁(ℓ)`,
then `I_c(0) D̂ = I_c(ℓ) N̂`. -/
@[powerlib_foundation] theorem port_relation {a₁ a₂ I₀ c₁ s₁ c₂ s₂ Z₁ Z₂ Y₁ Y₂ Rb ZL : ℂ}
    (h₁ : c₁ ^ 2 - s₁ ^ 2 = 1) (h₂ : c₂ ^ 2 - s₂ ^ 2 = 1)
    (hY₁ : Z₁ * Y₁ = 1) (hY₂ : Z₂ * Y₂ = 1)
    (hbond : a₂ * c₂ - Z₂ * I₀ * s₂ =
      Rb * ((I₀ * c₂ - a₂ * s₂ * Y₂) - (I₀ * c₁ - a₁ * s₁ * Y₁)))
    (hload : (a₁ * c₁ - Z₁ * I₀ * s₁) + (a₂ * c₂ - Z₂ * I₀ * s₂) =
      ZL * (I₀ * c₁ - a₁ * s₁ * Y₁)) :
    I₀ * Dhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb = (I₀ * c₁ - a₁ * s₁ * Y₁) * Nhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb ZL := by
  simp only [Dhat, Nhat, Aterm]
  linear_combination (-c₂ * s₁ * Y₁) * hbond + (Rb * s₁ * s₂ * Y₁ * Y₂ + c₂ * s₁ * Y₁) * hload +
    (-I₀ * Rb * Y₂ * s₂ - I₀ * c₂) * h₁ + (-I₀ * Rb * Y₁ * s₁) * h₂ +
    (I₀ * Rb * Y₂ * s₁ ^ 2 * s₂ + I₀ * c₂ * s₁ ^ 2) * hY₁ + (I₀ * Rb * Y₁ * s₁ * s₂ ^ 2) * hY₂

/-- `R_b = 0`: `cosh γ₂ℓ` cancels exactly inside the closed form. -/
@[powerlib_foundation] theorem Rb_zero_cancel {c₁ s₁ Y₁ c₂ s₂ Y₂ ZL : ℂ} (hc₂ : c₂ ≠ 0) :
    Nhat c₁ s₁ Y₁ c₂ s₂ Y₂ 0 ZL / Dhat c₁ s₁ Y₁ c₂ s₂ Y₂ 0 = c₁ + ZL * s₁ * Y₁ := by
  simp only [Nhat, Dhat, Aterm, zero_mul, add_zero]
  field_simp

/-- `N̂ - (cosh γ₁ℓ + Z_L sinh γ₁ℓ/Z_{c1}) D̂ = R_b sinh γ₁ℓ/Z_{c1} (cosh γ₂ℓ - cosh γ₁ℓ - Z_L sinh γ₁ℓ/Z_{c1})`;
on `D̂ = 0` this is the value of `N̂`. -/
@[powerlib_foundation] theorem Nhat_on_Dhat_zero {c₁ s₁ Y₁ c₂ s₂ Y₂ Rb ZL : ℂ}
    (hD : Dhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb = 0) :
    Nhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb ZL = Rb * s₁ * Y₁ * (c₂ - c₁ - ZL * s₁ * Y₁) := by
  have : Nhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb ZL - (c₁ + ZL * s₁ * Y₁) * Dhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb =
      Rb * s₁ * Y₁ * (c₂ - c₁ - ZL * s₁ * Y₁) := by
    simp only [Nhat, Dhat, Aterm]; ring
  rw [hD, mul_zero, sub_zero] at this
  exact this

/-- The pole at a zero of `D̂` is cancelled (`N̂ = 0` too) iff `R_b sinh γ₁ℓ = 0` or
`Z_L = Z_{c1} (cosh γ₂ℓ - cosh γ₁ℓ)/sinh γ₁ℓ`. -/
@[powerlib_foundation] theorem Nhat_zero_on_Dhat_zero_iff {c₁ s₁ Y₁ c₂ s₂ Y₂ Rb ZL Z₁ : ℂ}
    (hY₁ : Z₁ * Y₁ = 1) (hD : Dhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb = 0) (hRb : Rb ≠ 0) (hs₁ : s₁ ≠ 0) :
    Nhat c₁ s₁ Y₁ c₂ s₂ Y₂ Rb ZL = 0 ↔ ZL = Z₁ * (c₂ - c₁) / s₁ := by
  have hY : Y₁ ≠ 0 := right_ne_zero_of_mul_eq_one hY₁
  rw [Nhat_on_Dhat_zero hD]
  constructor
  · intro h
    have h' : c₂ - c₁ - ZL * s₁ * Y₁ = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exfalso; simp_all
      · exact h
    field_simp
    linear_combination (-Z₁) * h' - (ZL * s₁) * hY₁
  · intro h
    rw [h, div_mul_cancel₀ _ hs₁]
    linear_combination (-(Rb * s₁ * Y₁ * (c₂ - c₁))) * hY₁

/-! ## Missing screen–earth admittance -/

/-- With `Y₂ = 0` the modal matrix `ZY` is singular: the screen–earth mode disappears. -/
@[powerlib_foundation] theorem det_ZY_of_Y2_zero (Z : Matrix (Fin 2) (Fin 2) ℂ) (Y₁ : ℂ) :
    (Z * Matrix.diagonal ![Y₁, 0]).det = 0 := by
  rw [Matrix.det_mul, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

/-- With `Y₂ ≠ 0` (physical model) `det(ZY) = det Z · Y₁ Y₂`. -/
@[powerlib_foundation] theorem det_ZY (Z : Matrix (Fin 2) (Fin 2) ℂ) (Y₁ Y₂ : ℂ) :
    (Z * Matrix.diagonal ![Y₁, Y₂]).det = Z.det * (Y₁ * Y₂) := by
  rw [Matrix.det_mul, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

/-- Line operator `(U, I) ↦ (Z I, Y U)` of the two-loop cable with `Y = diag(Y₁, 0)`. -/
def lineOp (Z : Matrix (Fin 2) (Fin 2) ℂ) (Y₁ : ℂ) (w : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (Z.mulVec w.2, Matrix.diagonal ![Y₁, 0] |>.mulVec w.1)

/-- `Y₂ = 0`: the zero mode is a 2×2 Jordan block — its kernel is the screen-voltage line,
and there is a generalized eigenvector `w` with `A w ≠ 0`, `A² w = 0`. -/
@[powerlib_foundation] theorem lineOp_jordan (Z : Matrix (Fin 2) (Fin 2) ℂ) (Y₁ : ℂ)
    (hZ : Z.det ≠ 0) :
    ∃ w, lineOp Z Y₁ w ≠ 0 ∧ lineOp Z Y₁ (lineOp Z Y₁ w) = 0 := by
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  refine ⟨(0, Z⁻¹.mulVec (Pi.single 1 1)), ?_, ?_⟩
  · intro h
    have h1 := congrArg Prod.fst h
    simp only [lineOp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec,
      Prod.fst_zero] at h1
    have := congrFun h1 1
    simp at this
  · simp only [lineOp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec,
      Matrix.mulVec_zero]
    ext i <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- Kernel of the `Y₂ = 0` line operator: only the screen voltage `U₂` (one-dimensional). -/
@[powerlib_foundation] theorem lineOp_ker (Z : Matrix (Fin 2) (Fin 2) ℂ) (Y₁ : ℂ)
    (hY : Y₁ ≠ 0) (hZ : Z.det ≠ 0) (w : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    lineOp Z Y₁ w = 0 ↔ w.2 = 0 ∧ w.1 0 = 0 := by
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [lineOp, Prod.fst_zero, Prod.snd_zero] at h1 h2
    refine ⟨?_, ?_⟩
    · have := congrArg (Z⁻¹.mulVec) h1
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
    · have := congrFun h2 0
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply] at this
      tauto
  · rintro ⟨h2, h1⟩
    simp only [lineOp, h2, Matrix.mulVec_zero]
    ext i <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, h1]

/-! ## Charging power and lumped resonance -/

/-- Cable charging power from `S = V I*` with `I = jωC₁ℓ V`: `P = 0`, `Q = -ωC₁ℓ|V|²`
(absorb-positive, so the cable generates reactive power). -/
@[powerlib_foundation] theorem charging_power (ω C ℓ : ℝ) (V : ℂ) :
    V * (starRingEnd ℂ) (Complex.I * (ω * C * ℓ : ℝ) * V) =
      ((-(ω * C * ℓ) * Complex.normSq V : ℝ) : ℂ) * Complex.I := by
  rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have h := Complex.mul_conj V
  push_cast
  rw [show V * (-Complex.I * (ω * C * ℓ) * (starRingEnd ℂ) V) =
    -Complex.I * (ω * C * ℓ) * (V * (starRingEnd ℂ) V) by ring, h]
  ring

/-- Lumped parallel `LC` resonance: the admittance `jωC + 1/(jωL)` vanishes iff `ω² L C = 1`. -/
@[powerlib_foundation] theorem lc_resonance {ω L C : ℝ} (hω : ω ≠ 0) (hL : L ≠ 0) :
    Complex.I * ω * C + 1 / (Complex.I * ω * L) = 0 ↔ ω ^ 2 * L * C = 1 := by
  have hωc : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hden : Complex.I * ω * L ≠ 0 := mul_ne_zero (mul_ne_zero Complex.I_ne_zero hωc) hLc
  rw [← sub_eq_zero (b := (1 : ℝ)), ← Complex.ofReal_eq_zero]
  constructor
  · intro h
    have : (Complex.I * ω * C + 1 / (Complex.I * ω * L)) * (Complex.I * ω * L) = 0 := by
      rw [h, zero_mul]
    field_simp at this
    push_cast
    linear_combination (-1 : ℂ) * this + ((ω : ℂ) ^ 2 * C * L) * Complex.I_sq
  · intro h
    push_cast at h
    field_simp
    linear_combination (-1 : ℂ) * h + ((ω : ℂ) ^ 2 * C * L) * Complex.I_sq

end powerlib.Line.Cable
