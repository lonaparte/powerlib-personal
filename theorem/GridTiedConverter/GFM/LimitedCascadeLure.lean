import theorem.GridTiedConverter.GFM.LimitedCascade
import theorem.Dynamics.LaSalleLipschitz
import theorem.Dynamics.SaturationIntegral

/-! # The voltage-limited grid-forming cascade as a Lur'e system: global asymptotic stability

Model boundary.
* The platform `LimitedCascade` of `theorem/GridTiedConverter/GFM/LimitedCascade.lean` (the
  single-axis grid-forming voltage/current cascade `InnerCascade` behind an LC filter, its bridge
  voltage saturated to the linear modulation range `|e| ≤ V_max = V_dc/√3`), read through the
  same family `LimitedCascade.family`: its field about the operating point `(0, 0, v*, 0)`, state
  `(i, ξ, ṽ, ζ)`, `ṽ = v − v*`, constant reference `v*`, zero load current, no anti-windup.
* Lur'e form. With `φ = sat(e) − v*` the applied voltage about its steady value and
  `u = e − v* = −K_pc i + K_ic ξ + (1 − K_pc K_pv) ṽ + K_pc K_iv ζ` (`deviation`) the bridge
  command about its steady value, the loop is `L i̇ = −R i − ṽ + φ`, `C ṽ̇ = i`, `ζ̇ = −ṽ`,
  `ξ̇ = −K_pv ṽ + K_iv ζ − i`, `φ = sat_{[a,b]}(u)` with `a = −V_max − v*`, `b = V_max − v*`;
  the windup coordinate `η = ζ − L i − R C ṽ` (`windup`) integrates the applied voltage,
  `η̇ = −φ`.
* Parameters: the regions below have `L, C > 0` (`physical`), `V_dc > 0` (`dcLink`),
  `|v*| < V_max` (`headroom`), `K_pc > 0`, `K_ic K_iv > 0` and a filter resistance `R > 0` or
  `R = 0`; the case `R < 0` is decided in `theorem/GridTiedConverter/GFM/LimitedCascade.lean`.
* Excluded (as in the platform): the other axis, the line, synchronization, delays, PWM,
  anti-windup, DC-link dynamics.

Source: the Lur'e–Postnikov Lyapunov function `x'Px + ∫₀ᵘ φ` and the Popov criterion with the
multiplier `s` (positive realness of `s W(s)` for the loop transfer `W` from `φ` to `−u`;
H. K. Khalil, *Nonlinear Systems*, 3rd ed., §7.1, Theorem 7.3, and the positive-real lemma,
Lemma 6.3); the positive-realness test of a biquadratic `(n₂s² + n₁s + n₀)/(d₂s² + d₁s + d₀)`,
`n₁ d₁ ≥ (√(n₀ d₂) − √(n₂ d₀))²`; work-sync `theory/T-gfm-control.md` §1.9 (the inner cascade),
`theory/T-field-oriented-control.md` §1.7 (saturation and integrator windup of the PI loops);
the derivation of the certificate below by exact symbolic computation (sympy) in the batch-Q
study; LaSalle for Lipschitz fields `theorem/Dynamics/LaSalleLipschitz.lean`, the saturation
integral `theorem/Dynamics/SaturationIntegral.lean`.

Results.
* `InnerCascade.popov0`, `InnerCascade.popov1`: `n₀ = K_ic K_pv + K_pc K_iv − R C K_ic K_iv` and
  `n₁ = C K_ic (1 − K_iv L) + K_pc K_pv − 1`. In the study they are the coefficients of `s⁰` and
  `s¹` in `s W(s) = (K_pc C s² + n₁ s + n₀)/(L C s² + R C s + 1) + K_ic K_iv/s`, and the strict
  Popov condition below is the biquadratic test for its first term; in Lean they enter only
  through `lureFunction_rate`.
* `deviation_eq` (the command about its steady value is linear in the state),
  `applied_sub_vref` (`φ = sat_{[a,b]}(u)`), `lipschitzWith_field` (the platform field is
  globally Lipschitz).
* `lureFunction q`: `V = (K_ic K_iv/2) η² + p₁ i² + 2 p₂ i ṽ + p₃ ṽ² + Φ(u)` with
  `p₁ = (L n₁/C + K_pc R)/2`, `2 p₂ = K_pc + L n₀ − 2 L q`, `p₃ = (n₁ + C R n₀)/2` and
  `Φ = Dynamics.satIntegral a b`, `Φ' = sat_{[a,b]}`. `lureFunction_rate` (`L, C, K_pc ≠ 0`,
  `V_dc ≥ 0`, `L q² = K_pc n₀`): along the platform
  `V̇ = −(K_pc (φ − R i) − (K_pc − L q) ṽ)²/(L K_pc) − κ i²`, `κ = (R n₁ − K_pc − L n₀ + 2 L q)/C`,
  whatever the saturation does (the Popov multiplier `s` needs no sector condition).

Family and connection conclusions.
* `mem_den_globallyAsymptoticallyStable_of_popov`: with `L, C, R > 0`, headroom (so `V_dc > 0`),
  `K_pc > 0`, `K_ic K_iv > 0`, `n₀ > 0` and the strict Popov condition
  `(√K_pc − √(L n₀))² < R n₁` the platform is globally asymptotically stable, integrator windup
  included (`q = √(K_pc n₀ / L)`, `κ > 0`; LaSalle on `{V̇ = 0}`: `i ≡ 0` forces `ṽ = 0`, then
  `φ = 0`, `u ≡ 0` forces `ζ = 0`, `ξ = 0`).
* `mem_den_globallyAsymptoticallyStable_of_lossless`: with a lossless filter `R = 0`, `L, C > 0`,
  headroom, `K_pc > 0`, `K_ic K_iv > 0`, the boundary case `K_pc = L n₀` and
  `n₁ > 0`, the platform is globally asymptotically stable (`q = K_pc/L`, `V̇ = −K_pc φ²/L`).
* `unloaded_mem_den_globallyAsymptoticallyStable`: the IMC design `L = R = C = ω_c = K_pv = 1`,
  `K_iv = 1/2` at `v* = 0`, `V_dc = 1` (`LimitedCascade.unloaded`, not globally exponentially
  stable) is globally asymptotically stable (`n₀ = 1 = K_pc/L`, `n₁ = 1/2`).
* Not decided: global asymptotic stability with `R ≥ 0` outside these regions. A Popov
  multiplier `λ + q s` with `λ > 0` fails at low frequency (`W` has the double pole `s = 0` of
  the integrators `η, ξ`), so this certificate cannot be widened within the Popov family; a
  refutation needs an exact non-convergent solution of the saturated loop (a relay-type periodic
  orbit, or an unbounded solution when `R = 0`, `K_pc < L n₀`), which is not given (see
  `theorem/GridTiedConverter/GFM/LimitedCascade.lean`).
-/

noncomputable section
namespace powerlib.GFM
open Matrix Filter Linear LinearSystems TMIO Set
open scoped Topology

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

namespace InnerCascade

/-- The constant coefficient `n₀ = K_ic K_pv + K_pc K_iv − R C K_ic K_iv` of the Popov numerator.
-/
def popov0 (c : InnerCascade) : ℝ := c.Kic * c.Kpv + c.Kpc * c.Kiv - c.R * c.C * c.Kic * c.Kiv

/-- The first-order coefficient `n₁ = C K_ic (1 − K_iv L) + K_pc K_pv − 1` of the Popov
numerator. -/
def popov1 (c : InnerCascade) : ℝ := c.C * c.Kic * (1 - c.Kiv * c.L) + c.Kpc * c.Kpv - 1

end InnerCascade

namespace LimitedCascade

variable (y : LimitedCascade)

/-- The bridge command about its steady value, `u = e − v*`. -/
def deviation (z : ℝ⁴) : ℝ := y.command (z + y.point) - y.vref

/-- The windup coordinate `η = ζ − L i − R C ṽ`, the integral of `−φ`. -/
def windup (z : ℝ⁴) : ℝ := z 3 - y.design.L * z 0 - y.design.R * y.design.C * z 2

/-- **The Lur'e–Postnikov function** `V = (K_ic K_iv/2) η² + p₁ i² + 2 p₂ i ṽ + p₃ ṽ² + Φ(u)`,
`p₁ = (L n₁/C + K_pc R)/2`, `2 p₂ = K_pc + L n₀ − 2 L q`, `p₃ = (n₁ + C R n₀)/2`,
`Φ = ∫₀ᵘ sat_{[a,b]}`, `a = −V_max − v*`, `b = V_max − v*`. -/
def lureFunction (q : ℝ) (z : ℝ⁴) : ℝ :=
  y.design.Kic * y.design.Kiv / 2 * y.windup z ^ 2 +
    (y.design.L * y.design.popov1 / y.design.C + y.design.Kpc * y.design.R) / 2 * z 0 ^ 2 +
    (y.design.Kpc + y.design.L * y.design.popov0 - 2 * y.design.L * q) * (z 0 * z 2) +
    (y.design.popov1 + y.design.C * y.design.R * y.design.popov0) / 2 * z 2 ^ 2 +
    Dynamics.satIntegral (-y.Vmax - y.vref) (y.Vmax - y.vref) (y.deviation z)

/-- The command about its steady value is linear in the state:
`u = −K_pc i + K_ic ξ + (1 − K_pc K_pv) ṽ + K_pc K_iv ζ`. Static evidence. -/
@[tmio M, powerlib_domain] theorem deviation_eq (z : ℝ⁴) :
    y.deviation z = -y.design.Kpc * z 0 + y.design.Kic * z 1 +
      (1 - y.design.Kpc * y.design.Kpv) * z 2 + y.design.Kpc * y.design.Kiv * z 3 := by
  simp [deviation, command, point, InnerCascade.equilibrium, InnerCascade.control,
    InnerCascade.currentRef]
  ring

/-- The applied voltage about its steady value is the saturation of `u` to `[a, b]`,
`a = −V_max − v*`, `b = V_max − v*`. Static evidence. -/
@[tmio M, powerlib_domain] theorem applied_sub_vref (z : ℝ⁴) :
    y.applied (z + y.point) - y.vref =
      max (-y.Vmax - y.vref) (min (y.deviation z) (y.Vmax - y.vref)) := by
  rw [applied, SpecialFunctions.clampSym, deviation, min_sub_sub_right, max_sub_sub_right]

@[tmio M, powerlib_domain] private theorem field_apply (z : ℝ⁴) :
    y.field z 0 = (-y.design.R * z 0 + (y.applied (z + y.point) - y.vref) - z 2) / y.design.L ∧
      y.field z 1 = -y.design.Kpv * z 2 + y.design.Kiv * z 3 - z 0 ∧
      y.field z 2 = z 0 / y.design.C ∧ y.field z 3 = -z 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [field, limitedField, point, InnerCascade.equilibrium]
    ring
  all_goals simp [field, limitedField, point, InnerCascade.equilibrium, InnerCascade.currentRef]

/-- The platform field is globally Lipschitz (the saturation is `1`-Lipschitz). Static
evidence. -/
@[tmio M, powerlib_domain] theorem lipschitzWith_field :
    ∃ K, LipschitzWith K y.field := by
  set c := y.design
  set ku := |c.Kpc| + |c.Kic| + |1 - c.Kpc * c.Kpv| + |c.Kpc * c.Kiv| with hku
  set K := (|c.R| + ku + 1) / |c.L| + (|c.Kpv| + |c.Kiv| + 1) + 1 / |c.C| + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨⟨K, hK0⟩, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  simp only [dist_eq_norm]
  have h0 := Dynamics.abs_apply_le_norm (z - w) 0
  have h1 := Dynamics.abs_apply_le_norm (z - w) 1
  have h2 := Dynamics.abs_apply_le_norm (z - w) 2
  have h3 := Dynamics.abs_apply_le_norm (z - w) 3
  simp only [PiLp.sub_apply] at h0 h1 h2 h3
  set m := ‖z - w‖
  have hm : 0 ≤ m := norm_nonneg _
  obtain ⟨z0, z1, z2, z3⟩ := y.field_apply z
  obtain ⟨w0, w1, w2, w3⟩ := y.field_apply w
  -- the saturation is 1-Lipschitz
  have hsat : |(y.applied (z + y.point) - y.vref) - (y.applied (w + y.point) - y.vref)| ≤
      ku * m := by
    rw [y.applied_sub_vref, y.applied_sub_vref]
    refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), y.deviation_eq, y.deviation_eq]
    have e : -c.Kpc * z 0 + c.Kic * z 1 + (1 - c.Kpc * c.Kpv) * z 2 + c.Kpc * c.Kiv * z 3 -
        (-c.Kpc * w 0 + c.Kic * w 1 + (1 - c.Kpc * c.Kpv) * w 2 + c.Kpc * c.Kiv * w 3) =
        (-c.Kpc * (z 0 - w 0) + c.Kic * (z 1 - w 1) + (1 - c.Kpc * c.Kpv) * (z 2 - w 2)) +
          c.Kpc * c.Kiv * (z 3 - w 3) := by ring
    rw [e]
    have t1 := abs_add_three (-c.Kpc * (z 0 - w 0)) (c.Kic * (z 1 - w 1))
      ((1 - c.Kpc * c.Kpv) * (z 2 - w 2))
    have t2 := abs_add_le (-c.Kpc * (z 0 - w 0) + c.Kic * (z 1 - w 1) +
      (1 - c.Kpc * c.Kpv) * (z 2 - w 2)) (c.Kpc * c.Kiv * (z 3 - w 3))
    simp only [abs_mul, abs_neg] at t1 t2
    have s0 := mul_le_mul_of_nonneg_left h0 (abs_nonneg c.Kpc)
    have s1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c.Kic)
    have s2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg (1 - c.Kpc * c.Kpv))
    have s3 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (abs_nonneg c.Kpc) (abs_nonneg c.Kiv))
    calc _ ≤ |c.Kpc| * m + |c.Kic| * m + |1 - c.Kpc * c.Kpv| * m + |c.Kpc| * |c.Kiv| * m := by
          linarith
      _ = ku * m := by rw [hku, abs_mul c.Kpc c.Kiv]; ring
  refine ((Dynamics.norm_le_sum_abs _).trans_eq (Fin.sum_univ_four _)).trans ?_
  simp only [PiLp.sub_apply]
  rw [z0, z1, z2, z3, w0, w1, w2, w3]
  have e0 : |(-c.R * z 0 + (y.applied (z + y.point) - y.vref) - z 2) / c.L -
      (-c.R * w 0 + (y.applied (w + y.point) - y.vref) - w 2) / c.L| ≤
      (|c.R| + ku + 1) / |c.L| * m := by
    rw [← sub_div, abs_div]
    have e : -c.R * z 0 + (y.applied (z + y.point) - y.vref) - z 2 -
        (-c.R * w 0 + (y.applied (w + y.point) - y.vref) - w 2) =
        -c.R * (z 0 - w 0) + ((y.applied (z + y.point) - y.vref) -
          (y.applied (w + y.point) - y.vref)) + -(z 2 - w 2) := by ring
    rw [e, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
    have t := abs_add_three (-c.R * (z 0 - w 0)) ((y.applied (z + y.point) - y.vref) -
      (y.applied (w + y.point) - y.vref)) (-(z 2 - w 2))
    simp only [abs_mul, abs_neg] at t
    have s0 := mul_le_mul_of_nonneg_left h0 (abs_nonneg c.R)
    calc _ ≤ |c.R| * m + ku * m + m := by linarith
      _ = (|c.R| + ku + 1) * m := by ring
  have e1 : |-c.Kpv * z 2 + c.Kiv * z 3 - z 0 - (-c.Kpv * w 2 + c.Kiv * w 3 - w 0)| ≤
      (|c.Kpv| + |c.Kiv| + 1) * m := by
    have e : -c.Kpv * z 2 + c.Kiv * z 3 - z 0 - (-c.Kpv * w 2 + c.Kiv * w 3 - w 0) =
        -c.Kpv * (z 2 - w 2) + c.Kiv * (z 3 - w 3) + -(z 0 - w 0) := by ring
    rw [e]
    have t := abs_add_three (-c.Kpv * (z 2 - w 2)) (c.Kiv * (z 3 - w 3)) (-(z 0 - w 0))
    simp only [abs_mul, abs_neg] at t
    have s2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg c.Kpv)
    have s3 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c.Kiv)
    calc _ ≤ |c.Kpv| * m + |c.Kiv| * m + m := by linarith
      _ = (|c.Kpv| + |c.Kiv| + 1) * m := by ring
  have e2 : |z 0 / c.C - w 0 / c.C| ≤ 1 / |c.C| * m := by
    rw [← sub_div, abs_div, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right h0 (abs_nonneg _)
  have e3 : |-z 2 - -w 2| ≤ m := by
    rw [show -z 2 - -w 2 = -(z 2 - w 2) by ring, abs_neg]
    exact h2
  change _ ≤ K * m
  calc _ ≤ (|c.R| + ku + 1) / |c.L| * m + (|c.Kpv| + |c.Kiv| + 1) * m + 1 / |c.C| * m + m :=
        add_le_add (add_le_add (add_le_add e0 e1) e2) e3
    _ = K * m := by rw [hK]; ring

/-! ### The Lur'e–Postnikov function and its rate (static evidence) -/

@[tmio M, powerlib_domain] private theorem Vmax_nonneg (hV : 0 ≤ y.Vdc) : 0 ≤ y.Vmax :=
  div_nonneg hV (Real.sqrt_nonneg 3)

@[tmio M, powerlib_domain] private theorem hasFDerivAt_lureFunction (hV : 0 ≤ y.Vdc) (q : ℝ)
    (z : ℝ⁴) : ∃ W' : ℝ⁴ →L[ℝ] ℝ, HasFDerivAt (y.lureFunction q) W' z ∧ ∀ w : ℝ⁴,
      W' w = y.design.Kic * y.design.Kiv * y.windup z * y.windup w +
        (y.design.L * y.design.popov1 / y.design.C + y.design.Kpc * y.design.R) * z 0 * w 0 +
        (y.design.Kpc + y.design.L * y.design.popov0 - 2 * y.design.L * q) *
          (z 0 * w 2 + z 2 * w 0) +
        (y.design.popov1 + y.design.C * y.design.R * y.design.popov0) * z 2 * w 2 +
        (y.applied (z + y.point) - y.vref) * y.deviation w := by
  set c := y.design
  have hp : ∀ k : Fin 4, HasFDerivAt (fun w : ℝ⁴ => w k) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k) z :=
    fun k => (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : ℝ⁴ →L[ℝ] ℝ).hasFDerivAt
  have hη := ((hp 3).sub ((hp 0).const_mul c.L)).sub ((hp 2).const_mul (c.R * c.C))
  have hu0 := ((((hp 0).const_mul (-c.Kpc)).add ((hp 1).const_mul c.Kic)).add
    ((hp 2).const_mul (1 - c.Kpc * c.Kpv))).add ((hp 3).const_mul (c.Kpc * c.Kiv))
  have hu := hu0.congr_of_eventuallyEq (f₁ := y.deviation)
    (Filter.Eventually.of_forall fun w => y.deviation_eq w)
  have hab : -y.Vmax - y.vref ≤ y.Vmax - y.vref := by linarith [y.Vmax_nonneg hV]
  have hΦ := (Dynamics.hasDerivAt_satIntegral hab (y.deviation z)).hasFDerivAt.comp z hu
  have hW := (((((hη.pow 2).const_mul (c.Kic * c.Kiv / 2)).add
    (((hp 0).pow 2).const_mul ((c.L * c.popov1 / c.C + c.Kpc * c.R) / 2))).add
    (((hp 0).mul (hp 2)).const_mul (c.Kpc + c.L * c.popov0 - 2 * c.L * q))).add
    (((hp 2).pow 2).const_mul ((c.popov1 + c.C * c.R * c.popov0) / 2))).add hΦ
  refine ⟨_, hW, fun w => ?_⟩
  rw [← y.applied_sub_vref z]
  have hdw : y.deviation w = -c.Kpc * w 0 + c.Kic * w 1 + (1 - c.Kpc * c.Kpv) * w 2 +
      c.Kpc * c.Kiv * w 3 := y.deviation_eq w
  simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, smul_eq_mul, windup, hdw]
  simp
  ring

/-- **The rate of the Lur'e–Postnikov function** along the platform (`L, C, K_pc ≠ 0`,
`V_dc ≥ 0`, `L q² = K_pc n₀`): with `φ = sat(e) − v*`,
`V̇ = −(K_pc (φ − R i) − (K_pc − L q) ṽ)²/(L K_pc) − κ i²`,
`κ = (R n₁ − K_pc − L n₀ + 2 L q)/C`, for every state, saturated or not. Static evidence on the
implementation. -/
@[tmio M, powerlib_domain] theorem lureFunction_rate (hL : y.design.L ≠ 0)
    (hC : y.design.C ≠ 0) (hK : y.design.Kpc ≠ 0) (hV : 0 ≤ y.Vdc) {q : ℝ}
    (hq : y.design.L * q ^ 2 = y.design.Kpc * y.design.popov0) (z : ℝ⁴) :
    fderiv ℝ (y.lureFunction q) z (y.field z) =
      -(y.design.Kpc * (y.applied (z + y.point) - y.vref - y.design.R * z 0) -
          (y.design.Kpc - y.design.L * q) * z 2) ^ 2 / (y.design.L * y.design.Kpc) -
        (y.design.R * y.design.popov1 - y.design.Kpc - y.design.L * y.design.popov0 +
          2 * y.design.L * q) / y.design.C * z 0 ^ 2 := by
  obtain ⟨W', hW, hW'⟩ := y.hasFDerivAt_lureFunction hV q z
  rw [hW.fderiv, hW']
  obtain ⟨f0, f1, f2, f3⟩ := y.field_apply z
  rw [y.deviation_eq, f0, f1, f2, f3]
  simp only [windup, f0, f2, f3]
  set φ := y.applied (z + y.point) - y.vref
  set c := y.design
  have key : c.Kic * c.Kiv * (z 3 - c.L * z 0 - c.R * c.C * z 2) *
        (-z 2 - c.L * ((-c.R * z 0 + φ - z 2) / c.L) - c.R * c.C * (z 0 / c.C)) +
      (c.L * c.popov1 / c.C + c.Kpc * c.R) * z 0 * ((-c.R * z 0 + φ - z 2) / c.L) +
      (c.Kpc + c.L * c.popov0 - 2 * c.L * q) *
        (z 0 * (z 0 / c.C) + z 2 * ((-c.R * z 0 + φ - z 2) / c.L)) +
      (c.popov1 + c.C * c.R * c.popov0) * z 2 * (z 0 / c.C) +
      φ * (-c.Kpc * ((-c.R * z 0 + φ - z 2) / c.L) +
        c.Kic * (-c.Kpv * z 2 + c.Kiv * z 3 - z 0) + (1 - c.Kpc * c.Kpv) * (z 0 / c.C) +
        c.Kpc * c.Kiv * -z 2) -
      (-(c.Kpc * (φ - c.R * z 0) - (c.Kpc - c.L * q) * z 2) ^ 2 / (c.L * c.Kpc) -
        (c.R * c.popov1 - c.Kpc - c.L * c.popov0 + 2 * c.L * q) / c.C * z 0 ^ 2) =
      z 2 ^ 2 * (c.L * q ^ 2 - c.Kpc * c.popov0) / c.Kpc := by
    simp only [InnerCascade.popov0, InnerCascade.popov1]
    field_simp
    ring
  rw [hq, sub_self, mul_zero, zero_div] at key
  linarith

/-! ### Implementation evidence (private): the Lyapunov argument -/

/-- A linear functional of the state, `a₀ i + a₁ ξ + a₂ ṽ + a₃ ζ`. -/
@[tmio M, powerlib_domain] private theorem hasFDerivAt_lin4 (a0 a1 a2 a3 : ℝ) (z : ℝ⁴) :
    ∃ D : ℝ⁴ →L[ℝ] ℝ, HasFDerivAt (fun w : ℝ⁴ => a0 * w 0 + a1 * w 1 + a2 * w 2 + a3 * w 3) D z ∧
      ∀ v : ℝ⁴, D v = a0 * v 0 + a1 * v 1 + a2 * v 2 + a3 * v 3 := by
  have hp : ∀ k : Fin 4, HasFDerivAt (fun w : ℝ⁴ => w k) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k) z :=
    fun k => (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : ℝ⁴ →L[ℝ] ℝ).hasFDerivAt
  refine ⟨_, ((((hp 0).const_mul a0).add ((hp 1).const_mul a1)).add ((hp 2).const_mul a2)).add
    ((hp 3).const_mul a3), fun v => ?_⟩
  simp

/-- On a positively invariant set where a linear functional vanishes, so does its rate. -/
@[tmio M, powerlib_domain] private theorem lin4_rate_eq_zero {y : LimitedCascade}
    {N : Set ℝ⁴} (hN : IsPositivelyInvariant N y.field) (a0 a1 a2 a3 : ℝ)
    (hzero : ∀ x ∈ N, a0 * x 0 + a1 * x 1 + a2 * x 2 + a3 * x 3 = 0) {z : ℝ⁴} (hz : z ∈ N) :
    a0 * y.field z 0 + a1 * y.field z 1 + a2 * y.field z 2 + a3 * y.field z 3 = 0 := by
  obtain ⟨K, hK⟩ := y.lipschitzWith_field
  have hd : Differentiable ℝ (fun w : ℝ⁴ => a0 * w 0 + a1 * w 1 + a2 * w 2 + a3 * w 3) :=
    fun x => (hasFDerivAt_lin4 a0 a1 a2 a3 x).choose_spec.1.differentiableAt
  have h := Dynamics.LaSalle.lieDeriv_eq_zero_of_isPositivelyInvariant hK hN hd hzero hz
  obtain ⟨D, hD, hD'⟩ := hasFDerivAt_lin4 a0 a1 a2 a3 z
  rwa [hD.fderiv, hD'] at h

@[tmio M, powerlib_domain] private theorem eq_zero_of_sat_eq_zero {a b u : ℝ} (ha : a < 0)
    (hb : 0 < b) (h : max a (min u b) = 0) : u = 0 := by
  rcases le_total u b with hub | hbu
  · rw [min_eq_left hub] at h
    rcases le_total a u with hau | hua
    · rwa [max_eq_right hau] at h
    · rw [max_eq_left hua] at h; linarith
  · rw [min_eq_right hbu, max_eq_right (by linarith)] at h; linarith

@[tmio M, powerlib_domain] private theorem applied_point (hh : |y.vref| < y.Vmax) :
    y.applied (0 + y.point) - y.vref = 0 := by
  rw [zero_add, applied, command_point, SpecialFunctions.clampSym_of_abs_le hh.le, sub_self]

@[tmio M, powerlib_domain] private theorem field_zero (hh : |y.vref| < y.Vmax) : y.field 0 = 0 := by
  obtain ⟨f0, f1, f2, f3⟩ := y.field_apply 0
  rw [y.applied_point hh] at f0
  ext k
  fin_cases k <;> simp_all

/-- The quadratic part of `V` dominates `μ (i² + ṽ²)`, `μ = (p₁ p₃ − p₂²)/(p₁ + p₃)`, and `Φ`
grows linearly: `V ≥ μ (i² + ṽ²) + ε η² + m |u| − m²/2`. -/
@[tmio M, powerlib_domain] private theorem lureFunction_lower {q p1 p2 p3 : ℝ}
    (hp1def : p1 = (y.design.L * y.design.popov1 / y.design.C + y.design.Kpc * y.design.R) / 2)
    (hp2def : p2 = (y.design.Kpc + y.design.L * y.design.popov0 - 2 * y.design.L * q) / 2)
    (hp3def : p3 = (y.design.popov1 + y.design.C * y.design.R * y.design.popov0) / 2)
    (hp1 : 0 < p1) (hdet : p2 ^ 2 < p1 * p3) (z : ℝ⁴) :
    (p1 * p3 - p2 ^ 2) / (p1 + p3) * (z 0 ^ 2 + z 2 ^ 2) +
        y.design.Kic * y.design.Kiv / 2 * y.windup z ^ 2 +
        Dynamics.satIntegral (-y.Vmax - y.vref) (y.Vmax - y.vref) (y.deviation z) ≤
      y.lureFunction q z := by
  have hp3 : 0 < p3 := by
    by_contra h
    nlinarith [sq_nonneg p2, not_lt.mp h]
  have htr : 0 < p1 + p3 := by linarith
  have hq2 : (p1 * p3 - p2 ^ 2) / (p1 + p3) * (z 0 ^ 2 + z 2 ^ 2) ≤
      p1 * z 0 ^ 2 + 2 * p2 * (z 0 * z 2) + p3 * z 2 ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ htr]
    nlinarith [sq_nonneg (p1 * z 0 + p2 * z 2), sq_nonneg (p2 * z 0 + p3 * z 2)]
  have hV : y.lureFunction q z = y.design.Kic * y.design.Kiv / 2 * y.windup z ^ 2 +
      (p1 * z 0 ^ 2 + 2 * p2 * (z 0 * z 2) + p3 * z 2 ^ 2) +
      Dynamics.satIntegral (-y.Vmax - y.vref) (y.Vmax - y.vref) (y.deviation z) := by
    rw [lureFunction, hp1def, hp2def, hp3def]
    ring
  rw [hV]
  linarith

@[tmio M, powerlib_domain] private theorem lureFunction_contDiff (hV : 0 ≤ y.Vdc) (q : ℝ) :
    ContDiff ℝ 1 (y.lureFunction q) := by
  have hp : ∀ k : Fin 4, ContDiff ℝ 1 (fun w : ℝ⁴ => w k) :=
    fun k => (EuclideanSpace.proj k : ℝ⁴ →L[ℝ] ℝ).contDiff
  have hc0 := hp 0
  have hc1 := hp 1
  have hc2 := hp 2
  have hc3 := hp 3
  have hu : ContDiff ℝ 1 y.deviation := by rw [funext y.deviation_eq]; fun_prop
  have hΦ : ContDiff ℝ 1 fun w =>
      Dynamics.satIntegral (-y.Vmax - y.vref) (y.Vmax - y.vref) (y.deviation w) :=
    (Dynamics.contDiff_satIntegral (by linarith [y.Vmax_nonneg hV])).comp hu
  unfold lureFunction windup
  fun_prop

@[tmio M, powerlib_domain] private theorem lureFunction_zero (hh : |y.vref| < y.Vmax) (q : ℝ) :
    y.lureFunction q 0 = 0 := by
  have hd0 : y.deviation 0 = 0 := by rw [y.deviation_eq]; simp
  have hs0 := Dynamics.satIntegral_zero (a := -y.Vmax - y.vref) (b := y.Vmax - y.vref)
    (by linarith [neg_abs_le y.vref]) (by linarith [le_abs_self y.vref])
  simp [lureFunction, windup, hd0, hs0]

/-- With a positive definite quadratic part `V` is positive definite. -/
@[tmio M, powerlib_domain] private theorem lureFunction_pos {q μ : ℝ} (hμ : 0 < μ)
    (hK : 0 < y.design.Kic * y.design.Kiv) (hh : |y.vref| < y.Vmax)
    (hlow : ∀ z : ℝ⁴, μ * (z 0 ^ 2 + z 2 ^ 2) + y.design.Kic * y.design.Kiv / 2 * y.windup z ^ 2 +
      Dynamics.satIntegral (-y.Vmax - y.vref) (y.Vmax - y.vref) (y.deviation z) ≤
        y.lureFunction q z) {z : ℝ⁴} (hz : z ≠ 0) : 0 < y.lureFunction q z := by
  have ha0 : -y.Vmax - y.vref < 0 := by linarith [neg_abs_le y.vref]
  have hb0 : 0 < y.Vmax - y.vref := by linarith [le_abs_self y.vref]
  have hε : 0 < y.design.Kic * y.design.Kiv / 2 := by positivity
  have hKic : y.design.Kic ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hK
    exact lt_irrefl 0 hK
  by_contra hle
  have hl := hlow z
  have e1 : 0 ≤ μ * (z 0 ^ 2 + z 2 ^ 2) := by positivity
  have e2 : 0 ≤ y.design.Kic * y.design.Kiv / 2 * y.windup z ^ 2 := by positivity
  have e3 := Dynamics.satIntegral_nonneg ha0.le hb0.le (y.deviation z)
  have hle' := not_lt.mp hle
  have f1 : μ * (z 0 ^ 2 + z 2 ^ 2) = 0 := by linarith
  have f2 : y.design.Kic * y.design.Kiv / 2 * y.windup z ^ 2 = 0 := by linarith
  have f3 : Dynamics.satIntegral (-y.Vmax - y.vref) (y.Vmax - y.vref) (y.deviation z) = 0 := by
    linarith
  have g02 : z 0 ^ 2 + z 2 ^ 2 = 0 := (mul_eq_zero.mp f1).resolve_left hμ.ne'
  have h00 : z 0 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (z 2)]) (sq_nonneg _)
  have h22 : z 2 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (z 0)]) (sq_nonneg _)
  have z0 : z 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h00
  have z2 : z 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h22
  have hw : y.windup z = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp f2).resolve_left hε.ne')
  have hu : y.deviation z = 0 := by
    by_contra hne
    exact (Dynamics.satIntegral_pos ha0 hb0 hne).ne' f3
  have z3 : z 3 = 0 := by
    simp only [windup, z0, z2, mul_zero, sub_zero] at hw
    exact hw
  have z1 : z 1 = 0 := by
    rw [y.deviation_eq, z0, z2, z3] at hu
    simp only [mul_zero, add_zero, zero_add] at hu
    exact (mul_eq_zero.mp hu).resolve_left hKic
  apply hz
  ext k
  fin_cases k
  · exact z0
  · exact z1
  · exact z2
  · exact z3

/-- The state is bounded by `i`, `ṽ`, `η` and `u`: `‖z‖ ≤ A (|i| + |ṽ| + |η| + |u|)`. -/
@[tmio M, powerlib_domain] private theorem norm_le_coords (hKic : y.design.Kic ≠ 0) (z : ℝ⁴) :
    ‖z‖ ≤ (1 + (1 + |y.design.Kpc| + |1 - y.design.Kpc * y.design.Kpv| +
        |y.design.Kpc * y.design.Kiv| * (1 + |y.design.L| + |y.design.R * y.design.C|)) /
          |y.design.Kic| + (1 + |y.design.L| + |y.design.R * y.design.C|)) *
      (|z 0| + |z 2| + |y.windup z| + |y.deviation z|) := by
  set c := y.design
  set S := |z 0| + |z 2| + |y.windup z| + |y.deviation z| with hS
  have n0 := abs_nonneg (z 0)
  have n2 := abs_nonneg (z 2)
  have nη := abs_nonneg (y.windup z)
  have nu := abs_nonneg (y.deviation z)
  have hs0 : |z 0| ≤ S := by rw [hS]; linarith
  have hs2 : |z 2| ≤ S := by rw [hS]; linarith
  have hsη : |y.windup z| ≤ S := by rw [hS]; linarith
  have hsu : |y.deviation z| ≤ S := by rw [hS]; linarith
  set A3 := 1 + |c.L| + |c.R * c.C| with hA3
  have hz3 : |z 3| ≤ A3 * S := by
    have e : z 3 = y.windup z + c.L * z 0 + c.R * c.C * z 2 := by simp only [windup]; ring
    have t := abs_add_three (y.windup z) (c.L * z 0) (c.R * c.C * z 2)
    rw [← e, abs_mul, abs_mul] at t
    have s0 := mul_le_mul_of_nonneg_left hs0 (abs_nonneg c.L)
    have s2 := mul_le_mul_of_nonneg_left hs2 (abs_nonneg (c.R * c.C))
    calc |z 3| ≤ S + |c.L| * S + |c.R * c.C| * S := by linarith
      _ = A3 * S := by rw [hA3]; ring
  have hKa : 0 < |c.Kic| := abs_pos.mpr hKic
  have hz1 : |c.Kic| * |z 1| ≤
      (1 + |c.Kpc| + |1 - c.Kpc * c.Kpv| + |c.Kpc * c.Kiv| * A3) * S := by
    have e : c.Kic * z 1 = y.deviation z + c.Kpc * z 0 + -((1 - c.Kpc * c.Kpv) * z 2) +
        -(c.Kpc * c.Kiv * z 3) := by rw [y.deviation_eq]; ring
    have t1 := abs_add_three (y.deviation z) (c.Kpc * z 0) (-((1 - c.Kpc * c.Kpv) * z 2))
    have t2 := abs_add_le (y.deviation z + c.Kpc * z 0 + -((1 - c.Kpc * c.Kpv) * z 2))
      (-(c.Kpc * c.Kiv * z 3))
    rw [← e, abs_mul] at t2
    rw [abs_neg] at t2
    rw [abs_neg, abs_mul, abs_mul] at t1
    have s0 := mul_le_mul_of_nonneg_left hs0 (abs_nonneg c.Kpc)
    have s2 := mul_le_mul_of_nonneg_left hs2 (abs_nonneg (1 - c.Kpc * c.Kpv))
    have s3 := mul_le_mul_of_nonneg_left hz3 (abs_nonneg (c.Kpc * c.Kiv))
    rw [abs_mul (c.Kpc * c.Kiv)] at t2
    calc |c.Kic| * |z 1| ≤ S + |c.Kpc| * S + |1 - c.Kpc * c.Kpv| * S +
          |c.Kpc * c.Kiv| * (A3 * S) := by linarith
      _ = (1 + |c.Kpc| + |1 - c.Kpc * c.Kpv| + |c.Kpc * c.Kiv| * A3) * S := by ring
  have hz1' : |z 1| ≤ (1 + |c.Kpc| + |1 - c.Kpc * c.Kpv| + |c.Kpc * c.Kiv| * A3) / |c.Kic| * S := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hKa]
    linarith
  calc ‖z‖ ≤ |z 0| + |z 1| + |z 2| + |z 3| :=
        (Dynamics.norm_le_sum_abs z).trans_eq (Fin.sum_univ_four _)
    _ ≤ S + (1 + |c.Kpc| + |1 - c.Kpc * c.Kpv| + |c.Kpc * c.Kiv| * A3) / |c.Kic| * S +
        A3 * S := by linarith
    _ = _ := by ring

/-- `V` is radially unbounded: `V ≥ (δ/A) ‖z‖ − γ`. -/
@[tmio M, powerlib_domain] private theorem lureFunction_radial {q μ : ℝ} (hμ : 0 < μ)
    (hK : 0 < y.design.Kic * y.design.Kiv) (hh : |y.vref| < y.Vmax)
    (hlow : ∀ z : ℝ⁴, μ * (z 0 ^ 2 + z 2 ^ 2) + y.design.Kic * y.design.Kiv / 2 * y.windup z ^ 2 +
      Dynamics.satIntegral (-y.Vmax - y.vref) (y.Vmax - y.vref) (y.deviation z) ≤
        y.lureFunction q z) :
    Tendsto (y.lureFunction q) (comap norm atTop) atTop := by
  set c := y.design
  have hε : 0 < c.Kic * c.Kiv / 2 := by positivity
  have hKic : c.Kic ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hK
    exact lt_irrefl 0 hK
  set m := min (y.Vmax - y.vref) (y.Vmax + y.vref) with hm
  have hm0 : 0 < m := lt_min (by linarith [le_abs_self y.vref]) (by linarith [neg_abs_le y.vref])
  set δ := min (min μ (c.Kic * c.Kiv / 2)) m with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hμ hε) hm0
  set A := 1 + (1 + |c.Kpc| + |1 - c.Kpc * c.Kpv| +
        |c.Kpc * c.Kiv| * (1 + |c.L| + |c.R * c.C|)) / |c.Kic| + (1 + |c.L| + |c.R * c.C|)
    with hA
  have hAp : 0 < A := by positivity
  set γ := μ / 4 + μ / 4 + c.Kic * c.Kiv / 2 / 4 + m ^ 2 / 2 with hγ
  have hbd : ∀ z : ℝ⁴, δ / A * ‖z‖ + -γ ≤ y.lureFunction q z := by
    intro z
    set S := |z 0| + |z 2| + |y.windup z| + |y.deviation z| with hS
    have hn : ‖z‖ ≤ A * S := y.norm_le_coords hKic z
    have hl := hlow z
    have hΦ := Dynamics.le_satIntegral hm0.le (min_le_left _ _)
      (by rw [hm]; linarith [min_le_right (y.Vmax - y.vref) (y.Vmax + y.vref)])
      (y.deviation z) (a := -y.Vmax - y.vref)
    have q0 : μ * |z 0| - μ / 4 ≤ μ * z 0 ^ 2 := by
      have := mul_le_mul_of_nonneg_left (show |z 0| - 1 / 4 ≤ z 0 ^ 2 by
        nlinarith [sq_nonneg (|z 0| - 1 / 2), sq_abs (z 0)]) hμ.le
      linarith
    have q2 : μ * |z 2| - μ / 4 ≤ μ * z 2 ^ 2 := by
      have := mul_le_mul_of_nonneg_left (show |z 2| - 1 / 4 ≤ z 2 ^ 2 by
        nlinarith [sq_nonneg (|z 2| - 1 / 2), sq_abs (z 2)]) hμ.le
      linarith
    have qη : c.Kic * c.Kiv / 2 * |y.windup z| - c.Kic * c.Kiv / 2 / 4 ≤
        c.Kic * c.Kiv / 2 * y.windup z ^ 2 := by
      have := mul_le_mul_of_nonneg_left (show |y.windup z| - 1 / 4 ≤ y.windup z ^ 2 by
        nlinarith [sq_nonneg (|y.windup z| - 1 / 2), sq_abs (y.windup z)]) hε.le
      linarith
    have d1 : δ * |z 0| ≤ μ * |z 0| :=
      mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (abs_nonneg _)
    have d2 : δ * |z 2| ≤ μ * |z 2| :=
      mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (abs_nonneg _)
    have d3 : δ * |y.windup z| ≤ c.Kic * c.Kiv / 2 * |y.windup z| :=
      mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (abs_nonneg _)
    have d4 : δ * |y.deviation z| ≤ m * |y.deviation z| :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
    have hdA : δ / A * ‖z‖ ≤ δ * S := by
      have := mul_le_mul_of_nonneg_left hn (div_pos hδ0 hAp).le
      calc δ / A * ‖z‖ ≤ δ / A * (A * S) := this
        _ = δ * S := by field_simp
    have eμ : μ * (z 0 ^ 2 + z 2 ^ 2) = μ * z 0 ^ 2 + μ * z 2 ^ 2 := by ring
    have eS : δ * S = δ * |z 0| + δ * |z 2| + δ * |y.windup z| + δ * |y.deviation z| := by
      rw [hS]; ring
    rw [hγ]
    linarith
  refine tendsto_atTop_mono hbd ?_
  exact tendsto_atTop_add_const_right _ (-γ) (tendsto_comap.const_mul_atTop (div_pos hδ0 hAp))

/-- **The certificate gives global asymptotic stability.** With `L, C, K_pc > 0`,
`K_ic K_iv > 0`, headroom, `L q² = K_pc n₀`, `κ ≥ 0`, a positive definite quadratic part
(`p₁ > 0`, `p₂² < p₁ p₃`) and the LaSalle condition on `{V̇ = 0}`, the platform is globally
asymptotically stable (`Dynamics.LaSalle.globallyAsymptoticallyStable_of_lasalle_lipschitz`). -/
@[tmio TM, powerlib_domain] private theorem gas_of_certificate {y : LimitedCascade}
    (hL : 0 < y.design.L) (hC : 0 < y.design.C) (hKpc : 0 < y.design.Kpc)
    (hK : 0 < y.design.Kic * y.design.Kiv) (hh : |y.vref| < y.Vmax) {q : ℝ}
    (hq : y.design.L * q ^ 2 = y.design.Kpc * y.design.popov0)
    (hκ : 0 ≤ y.design.R * y.design.popov1 - y.design.Kpc - y.design.L * y.design.popov0 +
      2 * y.design.L * q)
    (hp1 : 0 < (y.design.L * y.design.popov1 / y.design.C + y.design.Kpc * y.design.R) / 2)
    (hdet : ((y.design.Kpc + y.design.L * y.design.popov0 - 2 * y.design.L * q) / 2) ^ 2 <
      (y.design.L * y.design.popov1 / y.design.C + y.design.Kpc * y.design.R) / 2 *
        ((y.design.popov1 + y.design.C * y.design.R * y.design.popov0) / 2))
    (hM : ∀ N : Set ℝ⁴, N ⊆ {z | fderiv ℝ (y.lureFunction q) z (y.field z) = 0} →
      IsPositivelyInvariant N y.field → N ⊆ {0}) :
    Flow.GloballyAsymptoticallyStable y.field 0 := by
  have hVm : 0 ≤ y.Vmax := le_trans (abs_nonneg _) hh.le
  have hV : 0 ≤ y.Vdc := by
    by_contra h
    have : y.Vmax < 0 := div_neg_of_neg_of_pos (not_le.mp h) (Real.sqrt_pos.mpr (by norm_num))
    linarith
  set p1 := (y.design.L * y.design.popov1 / y.design.C + y.design.Kpc * y.design.R) / 2
    with hp1def
  set p2 := (y.design.Kpc + y.design.L * y.design.popov0 - 2 * y.design.L * q) / 2 with hp2def
  set p3 := (y.design.popov1 + y.design.C * y.design.R * y.design.popov0) / 2 with hp3def
  have hp3 : 0 < p3 := by
    by_contra h
    nlinarith [sq_nonneg p2, not_lt.mp h]
  have hμ : 0 < (p1 * p3 - p2 ^ 2) / (p1 + p3) := div_pos (by linarith) (by linarith)
  have hlow := y.lureFunction_lower (q := q) hp1def hp2def hp3def hp1 hdet
  have hdec : ∀ z, fderiv ℝ (y.lureFunction q) z (y.field z) ≤ 0 := fun z => by
    rw [y.lureFunction_rate hL.ne' hC.ne' hKpc.ne' hV hq z]
    have e1 : 0 ≤ (y.design.Kpc * (y.applied (z + y.point) - y.vref - y.design.R * z 0) -
        (y.design.Kpc - y.design.L * q) * z 2) ^ 2 / (y.design.L * y.design.Kpc) := by
      positivity
    have e2 : 0 ≤ (y.design.R * y.design.popov1 - y.design.Kpc - y.design.L * y.design.popov0 +
        2 * y.design.L * q) / y.design.C * z 0 ^ 2 :=
      mul_nonneg (div_nonneg hκ hC.le) (sq_nonneg _)
    rw [neg_div]
    linarith
  obtain ⟨K, hlip⟩ := y.lipschitzWith_field
  exact Dynamics.LaSalle.globallyAsymptoticallyStable_of_lasalle_lipschitz (by norm_num) hlip
    (y.field_zero hh) (y.lureFunction_contDiff hV q) (y.lureFunction_zero hh q)
    (fun z hz => y.lureFunction_pos hμ hK hh hlow hz) (y.lureFunction_radial hμ hK hh hlow) hdec
    hM

/-- On `{V̇ = 0}` (with `κ ≥ 0`) the square term vanishes, and so does `κ i²`. -/
@[tmio M, powerlib_domain] private theorem rate_eq_zero {y : LimitedCascade} (hL : 0 < y.design.L)
    (hC : 0 < y.design.C) (hKpc : 0 < y.design.Kpc) (hV : 0 ≤ y.Vdc) {q : ℝ}
    (hq : y.design.L * q ^ 2 = y.design.Kpc * y.design.popov0)
    (hκ : 0 ≤ y.design.R * y.design.popov1 - y.design.Kpc - y.design.L * y.design.popov0 +
      2 * y.design.L * q) {z : ℝ⁴} (h : fderiv ℝ (y.lureFunction q) z (y.field z) = 0) :
    y.design.Kpc * (y.applied (z + y.point) - y.vref - y.design.R * z 0) -
        (y.design.Kpc - y.design.L * q) * z 2 = 0 ∧
      (y.design.R * y.design.popov1 - y.design.Kpc - y.design.L * y.design.popov0 +
        2 * y.design.L * q) * z 0 ^ 2 = 0 := by
  rw [y.lureFunction_rate hL.ne' hC.ne' hKpc.ne' hV hq z, neg_div] at h
  set X := y.design.Kpc * (y.applied (z + y.point) - y.vref - y.design.R * z 0) -
    (y.design.Kpc - y.design.L * q) * z 2
  set κ := y.design.R * y.design.popov1 - y.design.Kpc - y.design.L * y.design.popov0 +
    2 * y.design.L * q
  have hLK : 0 < y.design.L * y.design.Kpc := mul_pos hL hKpc
  have e1 : 0 ≤ X ^ 2 / (y.design.L * y.design.Kpc) := by positivity
  have e2 : 0 ≤ κ / y.design.C * z 0 ^ 2 := mul_nonneg (div_nonneg hκ hC.le) (sq_nonneg _)
  have f1 : X ^ 2 / (y.design.L * y.design.Kpc) = 0 := by linarith
  have f2 : κ / y.design.C * z 0 ^ 2 = 0 := by linarith
  refine ⟨?_, ?_⟩
  · rcases div_eq_zero_iff.mp f1 with h1 | h1
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    · exact absurd h1 hLK.ne'
  · rw [div_mul_eq_mul_div, div_eq_zero_iff] at f2
    exact f2.resolve_right hC.ne'

@[tmio M, powerlib_domain] private theorem Vdc_nonneg (hh : |y.vref| < y.Vmax) : 0 ≤ y.Vdc := by
  by_contra h
  have : y.Vmax < 0 := div_neg_of_neg_of_pos (not_le.mp h) (Real.sqrt_pos.mpr (by norm_num))
  linarith [abs_nonneg y.vref]

@[tmio M, powerlib_domain] private theorem deviation_eq_zero_of (hh : |y.vref| < y.Vmax)
    {z : ℝ⁴} (h : y.applied (z + y.point) - y.vref = 0) : y.deviation z = 0 := by
  rw [y.applied_sub_vref] at h
  exact eq_zero_of_sat_eq_zero (by linarith [neg_abs_le y.vref]) (by linarith [le_abs_self y.vref])
    h

/-! ## Global asymptotic stability -/

/-- **Global asymptotic stability on the Popov region, integrator windup included.** With a lossy
filter `R > 0`, `L, C > 0`, headroom `|v*| < V_max`, `K_pc > 0`, `K_ic K_iv > 0`,
`n₀ = K_ic K_pv + K_pc K_iv − R C K_ic K_iv > 0` and the strict Popov condition
`(√K_pc − √(L n₀))² < R n₁`, `n₁ = C K_ic (1 − K_iv L) + K_pc K_pv − 1`, the voltage-limited
cascade is globally asymptotically stable. The Lur'e–Postnikov function `lureFunction q`,
`q = √K_pc √(L n₀)/L`, has `V̇ = −(K_pc (φ − R i) − (K_pc − L q) ṽ)²/(L K_pc) − κ i²` with
`κ > 0`; on a positively invariant subset of `{V̇ = 0}` the current vanishes, hence
`φ = ṽ = 0`, `u = 0`, and `u̇ = K_ic K_iv ζ = 0`, so only the operating point remains (LaSalle
for the Lipschitz saturated field). -/
@[tmio TM, powerlib_domain] theorem mem_den_globallyAsymptoticallyStable_of_popov
    (y : LimitedCascade) (hL : 0 < y.design.L) (hC : 0 < y.design.C) (hR : 0 < y.design.R)
    (hh : |y.vref| < y.Vmax) (hKpc : 0 < y.design.Kpc) (hK : 0 < y.design.Kic * y.design.Kiv)
    (h0 : 0 < y.design.popov0)
    (hP : (Real.sqrt y.design.Kpc - Real.sqrt (y.design.L * y.design.popov0)) ^ 2 <
      y.design.R * y.design.popov1) :
    connection% (y ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Flow.GloballyAsymptoticallyStable y.field 0
  have hV := y.Vdc_nonneg hh
  set c := y.design with hc
  have hLn : 0 < c.L * c.popov0 := mul_pos hL h0
  set r := Real.sqrt c.Kpc * Real.sqrt (c.L * c.popov0) with hr
  have hr0 : 0 < r := mul_pos (Real.sqrt_pos.mpr hKpc) (Real.sqrt_pos.mpr hLn)
  have hr2 : r ^ 2 = c.Kpc * (c.L * c.popov0) := by
    rw [hr, mul_pow, Real.sq_sqrt hKpc.le, Real.sq_sqrt hLn.le]
  set q := r / c.L with hqdef
  have hLq : c.L * q = r := by rw [hqdef]; field_simp
  have hq : c.L * q ^ 2 = c.Kpc * c.popov0 := by
    have e : c.L * q ^ 2 = r ^ 2 / c.L := by rw [hqdef]; field_simp
    rw [e, hr2]
    field_simp
  have hs : (Real.sqrt c.Kpc - Real.sqrt (c.L * c.popov0)) ^ 2 =
      c.Kpc + c.L * c.popov0 - 2 * r := by
    rw [sub_sq, Real.sq_sqrt hKpc.le, Real.sq_sqrt hLn.le, hr]
    ring
  have hs0 : 0 ≤ c.Kpc + c.L * c.popov0 - 2 * r := by rw [← hs]; positivity
  rw [hs] at hP
  have hn1 : 0 < c.popov1 := pos_of_mul_pos_right (lt_of_le_of_lt hs0 hP) hR.le
  have hκ : 0 < c.R * c.popov1 - c.Kpc - c.L * c.popov0 + 2 * c.L * q := by
    rw [mul_assoc, hLq]; linarith
  refine gas_of_certificate hL hC hKpc hK hh hq hκ.le ?_ ?_ ?_
  · have e1 := div_pos (mul_pos hL hn1) hC
    have e2 := mul_pos hKpc hR
    linarith
  · rw [mul_assoc 2 c.L q, hLq]
    set s := c.Kpc + c.L * c.popov0 - 2 * r with hsdef
    have hss : s ^ 2 ≤ s * (c.R * c.popov1) := by nlinarith
    have hsK : s ≤ c.Kpc + c.L * c.popov0 := by linarith
    have hsR : 0 < c.R * c.popov1 := lt_of_le_of_lt hs0 hP
    have key : (c.L * c.popov1 / c.C + c.Kpc * c.R) / 2 * ((c.popov1 + c.C * c.R * c.popov0) / 2) -
        (s / 2) ^ 2 = ((c.Kpc + c.L * c.popov0) * (c.R * c.popov1) - s ^ 2 +
          c.L * c.popov1 ^ 2 / c.C + c.C * c.Kpc * c.R ^ 2 * c.popov0) / 4 := by
      field_simp
      ring
    have t1 : 0 < c.L * c.popov1 ^ 2 / c.C := by positivity
    have t2 : 0 ≤ c.C * c.Kpc * c.R ^ 2 * c.popov0 := by positivity
    have t3 : s * (c.R * c.popov1) ≤ (c.Kpc + c.L * c.popov0) * (c.R * c.popov1) :=
      mul_le_mul_of_nonneg_right hsK hsR.le
    linarith
  · intro N hN hNi z hz
    -- on `N`: `i = 0`, `ṽ = 0`, `u = 0`
    have hE : ∀ x ∈ N, x 0 = 0 ∧ x 2 = 0 ∧ y.applied (x + y.point) - y.vref = 0 := by
      intro x hx
      obtain ⟨hX, hκx⟩ := rate_eq_zero hL hC hKpc hV hq hκ.le (hN hx)
      have hx0 : x 0 = 0 := by
        rcases mul_eq_zero.mp hκx with h | h
        · exact absurd h hκ.ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      have hi := lin4_rate_eq_zero hNi 1 0 0 0
        (fun w hw => by
          have := (rate_eq_zero hL hC hKpc hV hq hκ.le (hN hw)).2
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hκ.ne'
          · simp [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h]) hx
      obtain ⟨f0, -, -, -⟩ := y.field_apply x
      rw [f0, hx0] at hi
      simp only [one_mul, zero_mul, add_zero, mul_zero, zero_add] at hi
      have hφ : y.applied (x + y.point) - y.vref = x 2 := by
        rcases div_eq_zero_iff.mp hi with h | h
        · linarith
        · exact absurd h hL.ne'
      rw [hφ, hx0, mul_zero, sub_zero, hLq] at hX
      have hx2 : x 2 = 0 := by
        have : r * x 2 = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hr0.ne'
      exact ⟨hx0, hx2, by rw [hφ, hx2]⟩
    have hu : ∀ x ∈ N, -c.Kpc * x 0 + c.Kic * x 1 + (1 - c.Kpc * c.Kpv) * x 2 +
        c.Kpc * c.Kiv * x 3 = 0 := fun x hx => by
      rw [← y.deviation_eq]
      exact y.deviation_eq_zero_of hh (hE x hx).2.2
    have hrate := lin4_rate_eq_zero hNi _ _ _ _ hu hz
    obtain ⟨hz0, hz2, hzφ⟩ := hE z hz
    obtain ⟨f0, f1, f2, f3⟩ := y.field_apply z
    rw [f0, f1, f2, f3, hz0, hz2, hzφ] at hrate
    simp only [mul_zero, neg_zero, add_zero, zero_div, sub_zero, zero_add] at hrate
    have hz3 : z 3 = 0 := by
      have : c.Kic * c.Kiv * z 3 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hK.ne'
    have hz1 : z 1 = 0 := by
      have h := hu z hz
      rw [hz0, hz2, hz3] at h
      simp only [mul_zero, add_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left (left_ne_zero_of_mul hK.ne')
    show z = 0
    ext k
    fin_cases k
    · exact hz0
    · exact hz1
    · exact hz2
    · exact hz3

/-- **Global asymptotic stability with a lossless filter.** With `R = 0`, `L, C > 0`, headroom,
`K_pc > 0`, `K_ic K_iv > 0`, the boundary of the Popov region `K_pc = L (K_ic K_pv + K_pc K_iv)`
(`K_pc = L n₀`) and `n₁ > 0`, the voltage-limited cascade is globally asymptotically stable:
`q = K_pc/L`, `V = (K_ic K_iv/2) η² + (n₁/(2C)) (L i² + C ṽ²) + Φ(u)` and `V̇ = −K_pc φ²/L`; on a
positively invariant subset of `{φ = 0}`, `u ≡ 0` forces `(n₁/C) i = K_ic K_iv η`, its rate
`n₁ ṽ/(L C) = 0`, then `i = 0`, `η = 0`, `ξ = 0`. Off this boundary (`K_pc ≠ L n₀`) the Popov
condition fails at `R = 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_globallyAsymptoticallyStable_of_lossless
    (y : LimitedCascade) (hL : 0 < y.design.L) (hC : 0 < y.design.C) (hR : y.design.R = 0)
    (hh : |y.vref| < y.Vmax) (hKpc : 0 < y.design.Kpc) (hK : 0 < y.design.Kic * y.design.Kiv)
    (hb : y.design.Kpc = y.design.L * y.design.popov0) (h1 : 0 < y.design.popov1) :
    connection% (y ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Flow.GloballyAsymptoticallyStable y.field 0
  have hV := y.Vdc_nonneg hh
  set c := y.design with hc
  set q := c.Kpc / c.L with hqdef
  have hLq : c.L * q = c.Kpc := by rw [hqdef]; field_simp
  have hq : c.L * q ^ 2 = c.Kpc * c.popov0 := by
    have e : c.L * q ^ 2 = c.Kpc * (c.Kpc / c.L) := by rw [hqdef]; field_simp
    rw [e, hb]
    field_simp
  have hκ : c.R * c.popov1 - c.Kpc - c.L * c.popov0 + 2 * c.L * q = 0 := by
    rw [mul_assoc, hLq, hR, ← hb]; ring
  have hn0 : c.popov0 = c.Kic * c.Kpv + c.Kpc * c.Kiv := by
    simp only [InnerCascade.popov0, hR, zero_mul, sub_zero]
  refine gas_of_certificate hL hC hKpc hK hh hq hκ.ge ?_ ?_ ?_
  · rw [hR, mul_zero, add_zero]; positivity
  · rw [← hc, mul_assoc 2 c.L q, hLq, hR, ← hb]
    have e : (c.Kpc + c.Kpc - 2 * c.Kpc) / 2 = 0 := by ring
    rw [e, mul_zero, add_zero]
    have : 0 < c.L * c.popov1 / c.C / 2 * (c.popov1 / 2) := by positivity
    simpa using this
  · intro N hN hNi z hz
    -- on `N`: `φ = 0`, hence `u = 0`
    have hφ : ∀ x ∈ N, y.applied (x + y.point) - y.vref = 0 := fun x hx => by
      have hX := (rate_eq_zero hL hC hKpc hV hq hκ.ge (hN hx)).1
      rw [hLq, sub_self, zero_mul, sub_zero, hR, zero_mul, sub_zero] at hX
      exact (mul_eq_zero.mp hX).resolve_left hKpc.ne'
    have hu : ∀ x ∈ N, -c.Kpc * x 0 + c.Kic * x 1 + (1 - c.Kpc * c.Kpv) * x 2 +
        c.Kpc * c.Kiv * x 3 = 0 := fun x hx => by
      rw [← y.deviation_eq]
      exact y.deviation_eq_zero_of hh (hφ x hx)
    -- `u̇ = 0`: `((1 − K_pc K_pv)/C − K_ic) i + K_ic K_iv ζ = 0`
    have hg : ∀ x ∈ N, ((1 - c.Kpc * c.Kpv) / c.C - c.Kic) * x 0 + 0 * x 1 + 0 * x 2 +
        c.Kic * c.Kiv * x 3 = 0 := fun x hx => by
      have h := lin4_rate_eq_zero hNi _ _ _ _ hu hx
      obtain ⟨f0, f1, f2, f3⟩ := y.field_apply x
      rw [f0, f1, f2, f3, hφ x hx, hR] at h
      have e : -c.Kpc * ((-0 * x 0 + 0 - x 2) / c.L) + c.Kic * (-c.Kpv * x 2 + c.Kiv * x 3 - x 0) +
          (1 - c.Kpc * c.Kpv) * (x 0 / c.C) + c.Kpc * c.Kiv * -x 2 =
          ((1 - c.Kpc * c.Kpv) / c.C - c.Kic) * x 0 + 0 * x 1 + 0 * x 2 +
            c.Kic * c.Kiv * x 3 + (c.Kpc / c.L - c.popov0) * x 2 := by
        rw [hn0]; field_simp; ring
      have e2 : c.Kpc / c.L - c.popov0 = 0 := by
        rw [hb]; field_simp; ring
      rw [e, e2] at h
      linarith
    -- its rate: `n₁ ṽ/(L C) = 0`
    have hv : ∀ x ∈ N, 0 * x 0 + 0 * x 1 + 1 * x 2 + 0 * x 3 = 0 := fun x hx => by
      have h := lin4_rate_eq_zero hNi _ _ _ _ hg hx
      obtain ⟨f0, -, -, f3⟩ := y.field_apply x
      rw [f0, f3, hφ x hx, hR] at h
      have e : ((1 - c.Kpc * c.Kpv) / c.C - c.Kic) * ((-0 * x 0 + 0 - x 2) / c.L) +
          0 * y.field x 1 + 0 * y.field x 2 + c.Kic * c.Kiv * -x 2 =
          c.popov1 / (c.L * c.C) * x 2 := by
        simp only [InnerCascade.popov1]
        field_simp
        ring
      rw [e] at h
      have hx2 : x 2 = 0 := (mul_eq_zero.mp h).resolve_left (by positivity)
      simp [hx2]
    have hi : ∀ x ∈ N, 1 * x 0 + 0 * x 1 + 0 * x 2 + 0 * x 3 = 0 := fun x hx => by
      have h := lin4_rate_eq_zero hNi _ _ _ _ hv hx
      obtain ⟨-, -, f2, -⟩ := y.field_apply x
      rw [f2] at h
      simp only [zero_mul, zero_add, one_mul, add_zero] at h
      have hx0 : x 0 = 0 := by
        rcases div_eq_zero_iff.mp h with h' | h'
        · exact h'
        · exact absurd h' hC.ne'
      simp [hx0]
    have hz0 : z 0 = 0 := by simpa using hi z hz
    have hz2 : z 2 = 0 := by simpa using hv z hz
    have hz3 : z 3 = 0 := by
      have h := hg z hz
      rw [hz0] at h
      simp only [mul_zero, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hK.ne'
    have hz1 : z 1 = 0 := by
      have h := hu z hz
      rw [hz0, hz2, hz3] at h
      simp only [mul_zero, add_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left (left_ne_zero_of_mul hK.ne')
    show z = 0
    ext k
    fin_cases k
    · exact hz0
    · exact hz1
    · exact hz2
    · exact hz3

/-- **The IMC-tuned cascade is globally asymptotically stable under the limit**: the platform
`unloaded` (`L = R = C = ω_c = K_pv = 1`, `K_iv = 1/2`, `v* = 0`, `V_dc = 1`; `n₀ = 1`,
`n₁ = 1/2`, `(√1 − √1)² = 0 < 1/2`), which is not globally exponentially stable
(`not_mem_den_globallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem unloaded_mem_den_globallyAsymptoticallyStable :
    connection% (unloaded ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  have hpop0 : unloaded.design.popov0 = 1 := by
    norm_num [unloaded, InnerCascade.imcTuned, InnerCascade.popov0]
  have hpop1 : unloaded.design.popov1 = 1 / 2 := by
    norm_num [unloaded, InnerCascade.imcTuned, InnerCascade.popov1]
  refine mem_den_globallyAsymptoticallyStable_of_popov unloaded
    (by norm_num [unloaded, InnerCascade.imcTuned]) (by norm_num [unloaded, InnerCascade.imcTuned])
    (by norm_num [unloaded, InnerCascade.imcTuned]) ?_
    (by norm_num [unloaded, InnerCascade.imcTuned]) (by norm_num [unloaded, InnerCascade.imcTuned])
    (by rw [hpop0]; norm_num) ?_
  · show |(0 : ℝ)| < 1 / Real.sqrt 3
    rw [abs_zero]
    positivity
  · rw [hpop0, hpop1]
    have hK : unloaded.design.Kpc = 1 := by norm_num [unloaded, InnerCascade.imcTuned]
    have hL : unloaded.design.L = 1 := by norm_num [unloaded, InnerCascade.imcTuned]
    have hR : unloaded.design.R = 1 := by norm_num [unloaded, InnerCascade.imcTuned]
    rw [hK, hL, hR]
    norm_num

end LimitedCascade

end powerlib.GFM
