import theorem.GridTiedConverter.GFM.VoltageModulationFloquet
import theorem.ParametricResonance.ForcedOrbitFloquet

/-! # The voltage-modulated VSG: forced orbit and Floquet multipliers of the nonlinear model

End-to-end statement for the nonlinear VSG with a grid-voltage amplitude modulation. The model
`ẋ = f(x, V(t))` with `V(t) = V₀ + ε V̂ cos(2Ωt)` and the state matrix moved by `ε A₀'` (for
instance the damping `D + εD'`) is written as `ẏ = A₀ y + ε b(t) + N_ε(t, y)`; all estimates of
`ForcedOrbitFloquet` are proved for the `sin` nonlinearity. Hence, at a Hopf point of the core, the forced orbit exists and
is unique near the operating point for small `ε`, and the Floquet multipliers of its variational
equation lie inside the unit circle when `|g_V/2| < |λ₁|` (`Re λ₁ < 0`) and outside when
`|λ₁| < |g_V/2|`, with the closed-form voltage pump `g_V` of `pump_voltage_hopf`.

Model boundary.
* `VoltageModulation.Model` (VSG core `(δ, Δω, P_f)`, constant EMF `E`, quasi-static lossless link
  `X`), operating point `(δ₀, V₀)`, deviation coordinates `y = (δ − δ₀, Δω, P_f − P*)`; the core is
  `core` (`P_δ = EV₀ cos δ₀/X`, `P_V = E sin δ₀/X`, `P_δδ = −EV₀ sin δ₀/X`, `P_δV = E cos δ₀/X`).
* Grid voltage `V₀ + ε V̂ cos(2Ωt)`; state matrix `A₀ + ε A₀'` with any real `A₀'` (a parameter
  change that keeps the operating point, e.g. damping); Hopf point of the core
  (`a ω_c = Ω²`, `d₀ = d₂Ω²`, `d₂ > 0`); no network dynamics, Q–V droop or limits.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2 (framework, first-order averaging), §3 (VSG core); the voltage
excitation is new.

Results.
* `abs_sub_le_of_deriv_le`, `sin_remainder`, `cos_remainder` — scalar remainder estimates.
* `core`, `e2`, `E20`, `nl`, `nlD`, `hasDerivAt_nl`, `orbN`, `orbJ`, `orbB`, `orbDx`, `orbDu` — the
  forced system of the model; `orbN_zero`, `orbN_lip`, `orbJ_taylor`, `E20_mulVec`,
  `orbJ_hasFDerivAt` (`orbJ` is the Jacobian of the vector field), `nl_periodic`, `nlD_periodic`,
  `continuous_orbN`, `continuous_orbJ`, `continuous_orbDu`, `orbDx_bound` — its estimates.
* `orbit_data` — the data at the Hopf point (`(I − e^{TA₀})⁻¹`, `y_p = Re{z_V e^{2jΩt}}`, `D_x y_p + D_u = A₀' +
  Re{A₁ e^{2jΩt}}`, `u A₁ r̄ = g_V`).
* `orbit_voltage_stable`, `orbit_voltage_unstable` — the end-to-end Floquet statements.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated VSG (forced orbit, Floquet multipliers).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
open Complex Matrix Filter Topology
open scoped Matrix.Norms.Operator
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (harm mulVecCLM)

/-! ### Scalar remainder estimates -/

/-- `|g(a) − g(b)| ≤ (|a| + |b|)|a − b|` when `|g'(x)| ≤ |x|`. -/
@[tmio T, powerlib_foundation] theorem abs_sub_le_of_deriv_le {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hb : ∀ x, |g' x| ≤ |x|) (a b : ℝ) :
    |g a - g b| ≤ (|a| + |b|) * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g')
    (C := |a| + |b|) (s := Set.uIcc b a) (fun x _ => (hg x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      refine (hb x).trans ?_
      rcases Set.mem_uIcc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.2 ⟨by linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b],
          by linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]⟩)
    (convex_uIcc b a) Set.right_mem_uIcc Set.left_mem_uIcc
  have h' : |g b - g a| ≤ (|a| + |b|) * |b - a| := by simpa [Real.norm_eq_abs] using h
  rwa [abs_sub_comm (g b), abs_sub_comm b] at h'

/-- `|(sin(δ₀ + a) − a cos δ₀) − (sin(δ₀ + b) − b cos δ₀)| ≤ (|a| + |b|)|a − b|`. -/
@[tmio T, powerlib_foundation] theorem sin_remainder (δ0 a b : ℝ) :
    |(Real.sin (δ0 + a) - a * Real.cos δ0) - (Real.sin (δ0 + b) - b * Real.cos δ0)| ≤
      (|a| + |b|) * |a - b| := by
  refine abs_sub_le_of_deriv_le (g := fun x => Real.sin (δ0 + x) - x * Real.cos δ0)
    (g' := fun x => Real.cos (δ0 + x) - Real.cos δ0) (fun x => ?_) (fun x => ?_) a b
  · have h := (((hasDerivAt_id' x).const_add δ0).sin).sub
      ((hasDerivAt_id' x).mul_const (Real.cos δ0))
    exact h.congr_deriv (by ring)
  · simpa using Real.abs_cos_sub_cos_le (δ0 + x) δ0

/-- `|cos(δ₀ + a) + a sin δ₀ − cos δ₀| ≤ a²`. -/
@[tmio T, powerlib_foundation] theorem cos_remainder (δ0 a : ℝ) :
    |Real.cos (δ0 + a) + a * Real.sin δ0 - Real.cos δ0| ≤ a ^ 2 := by
  have h := abs_sub_le_of_deriv_le (g := fun x => Real.cos (δ0 + x) + x * Real.sin δ0)
    (g' := fun x => -Real.sin (δ0 + x) + Real.sin δ0) (fun x => ?_) (fun x => ?_) a 0
  · simpa [sq, abs_mul_abs_self] using h
  · have h := (((hasDerivAt_id' x).const_add δ0).cos).add
      ((hasDerivAt_id' x).mul_const (Real.sin δ0))
    exact h.congr_deriv (by ring)
  · have := Real.abs_sin_sub_sin_le (δ0 + x) δ0
    rw [show -Real.sin (δ0 + x) + Real.sin δ0 = -(Real.sin (δ0 + x) - Real.sin δ0) by ring, abs_neg]
    simpa using this

namespace Model

variable (p : Model)

/-- The synchronizing core of the model at `(δ₀, V₀)`. -/
def core (δ0 V0 : ℝ) : Core :=
  ⟨p.ω0, p.H, p.D, p.ωc, p.E * V0 * Real.cos δ0 / p.X, p.E * Real.sin δ0 / p.X,
    -(p.E * V0 * Real.sin δ0 / p.X), p.E * Real.cos δ0 / p.X⟩

/-- The unit vector of the filtered power and the matrix unit `(P_f, δ)`. -/
def e2 : Fin 3 → ℝ := ![0, 0, 1]
def E20 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; 1, 0, 0]

/-- The nonlinear part of `ω_c (E V sin δ/X − P_f)` in deviation coordinates, with the grid voltage
`V₀ + ε V̂ cos ωt`. -/
def nl (δ0 V0 Vh ω ε t a : ℝ) : ℝ :=
  p.ωc * (p.E / p.X) * ((V0 + ε * (Vh * Real.cos (ω * t))) * Real.sin (δ0 + a) -
    V0 * Real.sin δ0 - V0 * Real.cos δ0 * a - ε * (Vh * Real.cos (ω * t)) * Real.sin δ0)

/-- Its derivative in `a`. -/
def nlD (δ0 V0 Vh ω ε t a : ℝ) : ℝ :=
  p.ωc * (p.E / p.X) * ((V0 + ε * (Vh * Real.cos (ω * t))) * Real.cos (δ0 + a) -
    V0 * Real.cos δ0)

@[tmio M, powerlib_domain] theorem hasDerivAt_nl (δ0 V0 Vh ω ε t a : ℝ) :
    HasDerivAt (p.nl δ0 V0 Vh ω ε t) (p.nlD δ0 V0 Vh ω ε t a) a := by
  have hs := (Real.hasDerivAt_sin (δ0 + a)).comp a ((hasDerivAt_id a).const_add δ0)
  have h := ((((hs.const_mul (V0 + ε * (Vh * Real.cos (ω * t)))).sub_const (V0 * Real.sin δ0)).sub
    ((hasDerivAt_id a).const_mul (V0 * Real.cos δ0))).sub_const
    (ε * (Vh * Real.cos (ω * t)) * Real.sin δ0)).const_mul (p.ωc * (p.E / p.X))
  convert h using 1
  · funext x; simp [nl]
  · simp [nlD]

/-- The nonlinearity `N_ε(t, y) = ε A₀' y + nl(y_δ) e_P`. -/
def orbN (δ0 V0 Vh ω : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ) (ε t : ℝ) (y : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  ε • (A0' *ᵥ y) + p.nl δ0 V0 Vh ω ε t (y 0) • e2

/-- The Jacobian `J_ε(t, y) = A₀ + ε A₀' + nl'(y_δ) E_{P δ}`. -/
def orbJ (δ0 V0 Vh ω : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ) (ε t : ℝ) (y : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (p.core δ0 V0).A0r + ε • A0' + p.nlD δ0 V0 Vh ω ε t (y 0) • E20

/-- The voltage forcing `b(t) = Re{V̂ B_V e^{jωt}} = (0, 0, ω_c (E sin δ₀/X) V̂ cos ωt)`. -/
def orbB (δ0 V0 Vh ω : ℝ) : ℝ → Fin 3 → ℝ := harm ((Vh : ℂ) • (p.core δ0 V0).Bv) ω

/-- `D_x y = ω_c P_δδ y_δ E_{Pδ}`. -/
def orbDx (δ0 V0 : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun y := (p.ωc * (p.core δ0 V0).Pδδ * y 0) • E20
  map_add' y z := by simp only [Pi.add_apply, mul_add, add_smul]
  map_smul' c y := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]; ring_nf

/-- `D_u(t) = A₀' + ω_c P_δV V̂ cos(ωt) E_{Pδ}`. -/
def orbDu (δ0 V0 Vh ω : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  A0' + (p.ωc * (p.core δ0 V0).PδV * (Vh * Real.cos (ω * t))) • E20

@[tmio M, powerlib_domain] theorem orbN_zero (δ0 V0 Vh ω : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (ε t : ℝ) : p.orbN δ0 V0 Vh ω A0' ε t 0 = 0 := by
  have h : p.nl δ0 V0 Vh ω ε t 0 = 0 := by simp only [nl, add_zero, mul_zero, sub_zero]; ring
  simp [orbN, h]

@[tmio M, powerlib_domain] theorem orbN_lip (δ0 V0 Vh ω : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) (y1 y2 : Fin 3 → ℝ) :
    ‖p.orbN δ0 V0 Vh ω A0' ε t y1 - p.orbN δ0 V0 Vh ω A0' ε t y2‖ ≤
      (|p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * ‖(e2 : Fin 3 → ℝ)‖ + ‖A0'‖) *
        (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := by
  set v := Vh * Real.cos (ω * t)
  have hv : |v| ≤ |Vh| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have ha1 : |y1 0| ≤ ‖y1‖ := by simpa using norm_le_pi_norm y1 0
  have ha2 : |y2 0| ≤ ‖y2‖ := by simpa using norm_le_pi_norm y2 0
  have hd : |y1 0 - y2 0| ≤ ‖y1 - y2‖ := by simpa using norm_le_pi_norm (y1 - y2) 0
  have e : p.orbN δ0 V0 Vh ω A0' ε t y1 - p.orbN δ0 V0 Vh ω A0' ε t y2 =
      ε • (A0' *ᵥ (y1 - y2)) + (p.nl δ0 V0 Vh ω ε t (y1 0) - p.nl δ0 V0 Vh ω ε t (y2 0)) • e2 := by
    simp only [orbN, Matrix.mulVec_sub, smul_sub, sub_smul]; abel
  have enl : p.nl δ0 V0 Vh ω ε t (y1 0) - p.nl δ0 V0 Vh ω ε t (y2 0) =
      p.ωc * (p.E / p.X) * (V0 * ((Real.sin (δ0 + y1 0) - y1 0 * Real.cos δ0) -
        (Real.sin (δ0 + y2 0) - y2 0 * Real.cos δ0)) +
        ε * v * (Real.sin (δ0 + y1 0) - Real.sin (δ0 + y2 0))) := by
    simp only [nl, v]; ring
  have hnl : |p.nl δ0 V0 Vh ω ε t (y1 0) - p.nl δ0 V0 Vh ω ε t (y2 0)| ≤
      |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := by
    rw [enl, abs_mul]
    have h1 := sin_remainder δ0 (y1 0) (y2 0)
    have h2 := Real.abs_sin_sub_sin_le (δ0 + y1 0) (δ0 + y2 0)
    rw [show δ0 + y1 0 - (δ0 + y2 0) = y1 0 - y2 0 by ring] at h2
    have inner : |V0 * ((Real.sin (δ0 + y1 0) - y1 0 * Real.cos δ0) -
          (Real.sin (δ0 + y2 0) - y2 0 * Real.cos δ0)) +
          ε * v * (Real.sin (δ0 + y1 0) - Real.sin (δ0 + y2 0))| ≤
        (|V0| + |Vh|) * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := by
     calc |V0 * ((Real.sin (δ0 + y1 0) - y1 0 * Real.cos δ0) -
           (Real.sin (δ0 + y2 0) - y2 0 * Real.cos δ0)) +
           ε * v * (Real.sin (δ0 + y1 0) - Real.sin (δ0 + y2 0))|
         ≤ |V0| * ((|y1 0| + |y2 0|) * |y1 0 - y2 0|) + ε * |Vh| * |y1 0 - y2 0| := by
           refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
           · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
           · rw [abs_mul, abs_mul, abs_of_nonneg hε]
             exact mul_le_mul (mul_le_mul_of_nonneg_left hv hε) h2 (abs_nonneg _) (by positivity)
       _ ≤ |V0| * ((‖y1‖ + ‖y2‖) * ‖y1 - y2‖) + ε * |Vh| * ‖y1 - y2‖ := by gcongr
       _ ≤ (|V0| + |Vh|) * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := by
           have := norm_nonneg y1; have := norm_nonneg y2; have := norm_nonneg (y1 - y2)
           have := abs_nonneg V0; have := abs_nonneg Vh
           nlinarith [mul_nonneg (mul_nonneg (abs_nonneg V0) hε) (norm_nonneg (y1 - y2)),
             mul_nonneg (mul_nonneg (abs_nonneg Vh) (add_nonneg (norm_nonneg y1) (norm_nonneg y2)))
               (norm_nonneg (y1 - y2))]
    exact (mul_le_mul_of_nonneg_left inner (abs_nonneg (p.ωc * (p.E / p.X)))).trans
      (le_of_eq (by ring))
  rw [e]
  have hA : ‖ε • (A0' *ᵥ (y1 - y2))‖ ≤ ‖A0'‖ * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    calc ε * ‖A0' *ᵥ (y1 - y2)‖ ≤ ε * (‖A0'‖ * ‖y1 - y2‖) :=
          mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) hε
      _ ≤ ‖A0'‖ * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := by
          have := norm_nonneg y1; have := norm_nonneg y2
          have := norm_nonneg A0'; have := norm_nonneg (y1 - y2)
          nlinarith [mul_nonneg (mul_nonneg (norm_nonneg A0') (add_nonneg (norm_nonneg y1)
            (norm_nonneg y2))) (norm_nonneg (y1 - y2))]
  have hB : ‖(p.nl δ0 V0 Vh ω ε t (y1 0) - p.nl δ0 V0 Vh ω ε t (y2 0)) • e2‖ ≤
      |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * ‖(e2 : Fin 3 → ℝ)‖ * (‖y1‖ + ‖y2‖ + ε) *
        ‖y1 - y2‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ *
          ‖(e2 : Fin 3 → ℝ)‖ :=
          mul_le_mul_of_nonneg_right hnl (norm_nonneg _)
      _ = _ := by ring
  calc _ ≤ ‖ε • (A0' *ᵥ (y1 - y2))‖ +
        ‖(p.nl δ0 V0 Vh ω ε t (y1 0) - p.nl δ0 V0 Vh ω ε t (y2 0)) • e2‖ := norm_add_le _ _
    _ ≤ _ := by
        have := add_le_add hA hB
        refine this.trans (le_of_eq ?_)
        ring

@[tmio M, powerlib_domain] theorem orbJ_taylor (δ0 V0 Vh ω : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) (y : Fin 3 → ℝ) :
    ‖p.orbJ δ0 V0 Vh ω A0' ε t y - (p.core δ0 V0).A0r - p.orbDx δ0 V0 y -
        ε • p.orbDu δ0 V0 Vh ω A0' t‖ ≤
      |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * ‖E20‖ * (‖y‖ ^ 2 + ε ^ 2) := by
  set v := Vh * Real.cos (ω * t)
  have hv : |v| ≤ |Vh| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have ha : |y 0| ≤ ‖y‖ := by simpa using norm_le_pi_norm y 0
  set sc := p.ωc * (p.E / p.X) * (V0 * (Real.cos (δ0 + y 0) + y 0 * Real.sin δ0 - Real.cos δ0) +
    ε * v * (Real.cos (δ0 + y 0) - Real.cos δ0)) with hsc
  have e : p.orbJ δ0 V0 Vh ω A0' ε t y - (p.core δ0 V0).A0r - p.orbDx δ0 V0 y -
      ε • p.orbDu δ0 V0 Vh ω A0' t = sc • E20 := by
    have hs : p.nlD δ0 V0 Vh ω ε t (y 0) - p.ωc * (p.core δ0 V0).Pδδ * y 0 -
        ε * (p.ωc * (p.core δ0 V0).PδV * v) = sc := by
      simp only [nlD, core, hsc, v]; ring
    rw [← hs]
    simp only [orbJ, orbDx, orbDu, LinearMap.coe_mk, AddHom.coe_mk, smul_add, smul_smul, sub_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 := cos_remainder δ0 (y 0)
  have h2 := Real.abs_cos_sub_cos_le (δ0 + y 0) δ0
  rw [show δ0 + y 0 - δ0 = y 0 by ring] at h2
  have hy2 : (y 0) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hεa : ε * |y 0| ≤ ‖y‖ ^ 2 + ε ^ 2 := by
    nlinarith [sq_nonneg (|y 0| - ε), abs_nonneg (y 0), sq_abs (y 0)]
  have hsc_le : |sc| ≤ |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * (‖y‖ ^ 2 + ε ^ 2) := by
    rw [hsc, abs_mul]
    have inner : |V0 * (Real.cos (δ0 + y 0) + y 0 * Real.sin δ0 - Real.cos δ0) +
        ε * v * (Real.cos (δ0 + y 0) - Real.cos δ0)| ≤ (|V0| + |Vh|) * (‖y‖ ^ 2 + ε ^ 2) := by
     calc |V0 * (Real.cos (δ0 + y 0) + y 0 * Real.sin δ0 - Real.cos δ0) +
           ε * v * (Real.cos (δ0 + y 0) - Real.cos δ0)|
         ≤ |V0| * (y 0) ^ 2 + ε * |Vh| * |y 0| := by
           refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
           · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
           · rw [abs_mul, abs_mul, abs_of_nonneg hε]
             exact mul_le_mul (mul_le_mul_of_nonneg_left hv hε) h2 (abs_nonneg _) (by positivity)
       _ ≤ |V0| * (‖y‖ ^ 2 + ε ^ 2) + |Vh| * (‖y‖ ^ 2 + ε ^ 2) := by
           have := abs_nonneg V0; have := abs_nonneg Vh
           have h3 : |V0| * (y 0) ^ 2 ≤ |V0| * (‖y‖ ^ 2 + ε ^ 2) :=
             mul_le_mul_of_nonneg_left (show (y 0) ^ 2 ≤ ‖y‖ ^ 2 + ε ^ 2 by nlinarith [sq_nonneg ε])
               (abs_nonneg _)
           have h4 : ε * |Vh| * |y 0| ≤ |Vh| * (‖y‖ ^ 2 + ε ^ 2) := by
             rw [mul_comm ε, mul_assoc]; exact mul_le_mul_of_nonneg_left hεa (abs_nonneg _)
           linarith
       _ = (|V0| + |Vh|) * (‖y‖ ^ 2 + ε ^ 2) := by ring
    exact (mul_le_mul_of_nonneg_left inner (abs_nonneg (p.ωc * (p.E / p.X)))).trans
      (le_of_eq (by ring))
  calc |sc| * ‖E20‖ ≤ |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * (‖y‖ ^ 2 + ε ^ 2) * ‖E20‖ :=
        mul_le_mul_of_nonneg_right hsc_le (norm_nonneg _)
    _ = _ := by ring

@[tmio M, powerlib_domain] theorem E20_mulVec (v : Fin 3 → ℝ) : E20 *ᵥ v = v 0 • e2 := by
  funext i; fin_cases i <;> simp [E20, e2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `J_ε(t, y)` is the Jacobian of the vector field. -/
@[tmio M, powerlib_domain] theorem orbJ_hasFDerivAt (δ0 V0 Vh ω : ℝ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (ε t : ℝ) (y : Fin 3 → ℝ) :
    HasFDerivAt (fun y => (p.core δ0 V0).A0r *ᵥ y +
        (ε • p.orbB δ0 V0 Vh ω t + p.orbN δ0 V0 Vh ω A0' ε t y))
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (p.orbJ δ0 V0 Vh ω A0' ε t y))) y := by
  have hA := (mulVecCLM (p.core δ0 V0).A0r).hasFDerivAt (x := y)
  have hA' := ((mulVecCLM A0').hasFDerivAt (x := y)).const_smul ε
  have hproj := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) y
  have hnl := (p.hasDerivAt_nl δ0 V0 Vh ω ε t (y 0)).comp_hasFDerivAt y hproj
  have he := hnl.smul_const e2
  have h := hA.add ((hasFDerivAt_const (ε • p.orbB δ0 V0 Vh ω t) y).add (hA'.add he))
  convert h using 1
  · funext z; simp [orbN, ForcedOrbit.mulVecCLM_apply, Function.comp]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [orbJ, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
      _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, ForcedOrbit.mulVecCLM_apply, Matrix.add_mulVec,
      Matrix.smul_mulVec, E20_mulVec, smul_smul, zero_add]
    rw [add_assoc, smul_eq_mul, mul_comm]

@[tmio M, powerlib_domain] theorem nl_periodic (δ0 V0 Vh : ℝ) {ω : ℝ} (hω : ω ≠ 0) (ε t a : ℝ) :
    p.nl δ0 V0 Vh ω ε (t + 2 * Real.pi / ω) a = p.nl δ0 V0 Vh ω ε t a := by
  have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
  simp only [nl, e, Real.cos_add_two_pi]

@[tmio M, powerlib_domain] theorem nlD_periodic (δ0 V0 Vh : ℝ) {ω : ℝ} (hω : ω ≠ 0) (ε t a : ℝ) :
    p.nlD δ0 V0 Vh ω ε (t + 2 * Real.pi / ω) a = p.nlD δ0 V0 Vh ω ε t a := by
  have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
  simp only [nlD, e, Real.cos_add_two_pi]

@[tmio M, powerlib_domain] theorem continuous_orbN (δ0 V0 Vh ω : ℝ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) :
    Continuous (fun q : ℝ × (Fin 3 → ℝ) => p.orbN δ0 V0 Vh ω A0' ε q.1 q.2) := by
  have h1 : Continuous fun q : ℝ × (Fin 3 → ℝ) => p.nl δ0 V0 Vh ω ε q.1 (q.2 0) := by
    unfold nl; fun_prop
  show Continuous fun q : ℝ × (Fin 3 → ℝ) =>
    ε • (A0' *ᵥ q.2) + p.nl δ0 V0 Vh ω ε q.1 (q.2 0) • e2
  exact ((continuous_const.matrix_mulVec continuous_snd).const_smul ε).add
    (h1.smul continuous_const)

@[tmio M, powerlib_domain] theorem continuous_orbJ (δ0 V0 Vh ω : ℝ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) :
    Continuous (fun q : ℝ × (Fin 3 → ℝ) => p.orbJ δ0 V0 Vh ω A0' ε q.1 q.2) := by
  have h1 : Continuous fun q : ℝ × (Fin 3 → ℝ) => p.nlD δ0 V0 Vh ω ε q.1 (q.2 0) := by
    unfold nlD; fun_prop
  show Continuous fun q : ℝ × (Fin 3 → ℝ) =>
    (p.core δ0 V0).A0r + ε • A0' + p.nlD δ0 V0 Vh ω ε q.1 (q.2 0) • E20
  exact continuous_const.add (h1.smul continuous_const)

@[tmio M, powerlib_domain] theorem continuous_orbDu (δ0 V0 Vh ω : ℝ)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) : Continuous (p.orbDu δ0 V0 Vh ω A0') := by
  have h : Continuous fun t : ℝ => p.ωc * (p.core δ0 V0).PδV * (Vh * Real.cos (ω * t)) := by
    fun_prop
  exact continuous_const.add (h.smul continuous_const)

@[tmio M, powerlib_domain] theorem orbDx_bound (δ0 V0 : ℝ) (v : Fin 3 → ℝ) :
    ‖p.orbDx δ0 V0 v‖ ≤ |p.ωc * (p.core δ0 V0).Pδδ| * ‖E20‖ * ‖v‖ := by
  have ha : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  show ‖(p.ωc * (p.core δ0 V0).Pδδ * v 0) • E20‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  calc |p.ωc * (p.core δ0 V0).Pδδ| * |v 0| * ‖E20‖
      ≤ |p.ωc * (p.core δ0 V0).Pδδ| * ‖v‖ * ‖E20‖ := by gcongr
    _ = _ := by ring

/-! ### The forced orbit of the voltage-modulated VSG and its Floquet multipliers -/

/-- The data shared by the two end-to-end statements: `(I − e^{TA₀})⁻¹`, the first-order orbit
`y_p = Re{z_V e^{2jΩt}}`, the link `D_x y_p + D_u = A₀' + Re{A₁ e^{2jΩt}}` and the pump. -/
@[tmio M, powerlib_domain] theorem orbit_data {δ0 V0 Vh Ω : ℝ} (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hΩ : 0 < Ω) (hω0 : p.ω0 ≠ 0) (hH : p.H ≠ 0) (hd2 : 0 < (p.core δ0 V0).d2)
    (hPδ : (p.core δ0 V0).Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : (p.core δ0 V0).a * (p.core δ0 V0).ωc = (Ω : ℂ) ^ 2)
    (hH2 : (p.core δ0 V0).d0 = ((p.core δ0 V0).a + (p.core δ0 V0).ωc) * (Ω : ℂ) ^ 2) :
    ∃ Minv : Matrix (Fin 3) (Fin 3) ℝ, Minv * (1 - BlockAveraging.expS (p.core δ0 V0).A0r
        (2 * Real.pi / (2 * Ω))) = 1 ∧ (1 - BlockAveraging.expS (p.core δ0 V0).A0r
        (2 * Real.pi / (2 * Ω))) * Minv = 1 ∧
      (∀ t, harm ((p.core δ0 V0).forcedV (2 * Ω * I) Vh) (2 * Ω) (t + 2 * Real.pi / (2 * Ω)) =
        harm ((p.core δ0 V0).forcedV (2 * Ω * I) Vh) (2 * Ω) t) ∧
      (∀ t, HasDerivAt (harm ((p.core δ0 V0).forcedV (2 * Ω * I) Vh) (2 * Ω))
        ((p.core δ0 V0).A0r *ᵥ harm ((p.core δ0 V0).forcedV (2 * Ω * I) Vh) (2 * Ω) t +
          p.orbB δ0 V0 Vh (2 * Ω) t) t) ∧
      (∀ t, p.orbDx δ0 V0 (harm ((p.core δ0 V0).forcedV (2 * Ω * I) Vh) (2 * Ω) t) +
          p.orbDu δ0 V0 Vh (2 * Ω) A0' t =
        A0' + BlockAveraging.modX ((p.core δ0 V0).A1 ((p.core δ0 V0).forcedVδ (2 * Ω * I) Vh) Vh)
          (2 * Ω) t) ∧
      (p.core δ0 V0).left (Ω * I) ⬝ᵥ ((p.core δ0 V0).A1 ((p.core δ0 V0).forcedVδ (2 * Ω * I) Vh)
          Vh *ᵥ star ((p.core δ0 V0).right (Ω * I))) = (p.core δ0 V0).gV V0 Ω Vh := by
  set cr := p.core δ0 V0 with hcr
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := cr.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  obtain ⟨hQP, hPQ, hQAP, -, -⟩ := BlockAveraging.modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : BlockAveraging.modalQ (cr.left (Ω * I)) cr.u3 * cr.A0r *
      BlockAveraging.modalP (cr.right (Ω * I)) cr.r3 =
      fromBlocks (TwoToOne.base 0 (2 * Ω / 2)) 0 0 !![-cr.d2] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖BlockAveraging.expS (!![-cr.d2] : Matrix (Fin 1) (Fin 1) ℝ)
      (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [BlockAveraging.norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) (neg_neg_of_pos hd2)
  obtain ⟨Minv, hL, hR⟩ := ForcedOrbit.exists_minv_of_modal hω hPQ hQP _ hA0 hq
  have hΩ2 : (2 * Ω) ≠ 0 := by positivity
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hchar : cr.charP (2 * Ω * I) ≠ 0 := by
    rw [cr.charP_hopf Ω hH1 hH2, Core.a_add_ωc]
    refine mul_ne_zero (by simpa using hΩc) ?_
    have := Model.add_mul_I_ne (x := cr.d2) (y := 2 * Ω) (by positivity)
    push_cast at this
    exact this
  have hz : (((2 * Ω : ℝ) : ℂ) * I) • cr.forcedV (2 * Ω * I) Vh -
      cr.A0r.map (algebraMap ℝ ℂ) *ᵥ cr.forcedV (2 * Ω * I) Vh = (Vh : ℂ) • cr.Bv := by
    have hf := cr.forcedV_eq (s := 2 * Ω * I) (Vh : ℂ) hω0 hH hchar
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hf
    rw [Core.A0r_map]; push_cast; exact hf
  refine ⟨Minv, hL, hR, fun t => ForcedOrbit.harm_periodic _ hΩ2 t,
    fun t => ForcedOrbit.harm_hasDerivAt hz t, fun t => ?_, ?_⟩
  · have hωc : cr.ωc = p.ωc := rfl
    have hPδδ : (p.core δ0 V0).Pδδ = cr.Pδδ := rfl
    have hPδV : (p.core δ0 V0).PδV = cr.PδV := rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [orbDx, orbDu, E20, harm, Core.forcedV, Core.A1, BlockAveraging.modX, hωc, hPδδ,
        hPδV]
    ring
  · have hp := cr.pump_voltage_hopf V0 Ω Vh hPδ hV0 hH hΩ.ne' hd2.ne' hH1 hH2
    rw [Element.pump] at hp
    rw [hp]; rfl

/-- End-to-end, voltage-modulated VSG, stability. At a Hopf point of the core (`a ω_c = Ω²`,
`d₀ = d₂Ω²`, `d₂ > 0`), with grid voltage `V₀ + ε V̂ cos(2Ωt)` and state matrix `A₀ + ε A₀'`: the
nonlinear model has, for all small `ε > 0`, a `2π/(2Ω)`-periodic forced orbit in the ball of radius
`cε`, unique there; if `Re λ₁ < 0` and `|g_V/2| < |λ₁|` (`λ₁ = u A₀' r`, `g_V` of
`pump_voltage_hopf`), every Floquet multiplier of the variational equation along that orbit
(`orbJ` is the Jacobian of the vector field, `orbJ_hasFDerivAt`) lies inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_voltage_stable {δ0 V0 Vh Ω : ℝ}
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (hΩ : 0 < Ω) (hω0 : p.ω0 ≠ 0) (hH : p.H ≠ 0)
    (hd2 : 0 < (p.core δ0 V0).d2) (hPδ : (p.core δ0 V0).Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : (p.core δ0 V0).a * (p.core δ0 V0).ωc = (Ω : ℂ) ^ 2)
    (hH2 : (p.core δ0 V0).d0 = ((p.core δ0 V0).a + (p.core δ0 V0).ωc) * (Ω : ℂ) ^ 2)
    (hs : ((p.core δ0 V0).left (Ω * I) ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ (p.core δ0 V0).right (Ω * I))).re < 0)
    (hg : ‖(p.core δ0 V0).gV V0 Ω Vh / 2‖ ^ 2 < ‖(p.core δ0 V0).left (Ω * I) ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ (p.core δ0 V0).right (Ω * I))‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y ((p.core δ0 V0).A0r *ᵥ y t + (ε • p.orbB δ0 V0 Vh (2 * Ω) t +
            p.orbN δ0 V0 Vh (2 * Ω) A0' ε t (y t))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y ((p.core δ0 V0).A0r *ᵥ y t + (ε • p.orbB δ0 V0 Vh (2 * Ω) t +
            p.orbN δ0 V0 Vh (2 * Ω) A0' ε t (y t))) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => p.orbJ δ0 V0 Vh (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨Minv, hL, hR, hpp, hpd, hlink, hpump⟩ :=
    p.orbit_data (Vh := Vh) A0' hΩ hω0 hH hd2 hPδ hV0 hH1 hH2
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := (p.core δ0 V0).hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hΩ2 : (2 * Ω) ≠ 0 := by positivity
  have hg' : ‖(p.core δ0 V0).left (Ω * I) ⬝ᵥ ((p.core δ0 V0).A1
      ((p.core δ0 V0).forcedVδ (2 * Ω * I) Vh) Vh *ᵥ star ((p.core δ0 V0).right (Ω * I))) / 2‖ ^ 2 <
      ‖(p.core δ0 V0).left (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ (p.core δ0 V0).right (Ω * I))‖ ^ 2 := by
    rw [hpump]; exact hg
  exact ForcedOrbit.orbit_floquet_three_stable (Minv := Minv) (K := |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * ‖(e2 : Fin 3 → ℝ)‖ + ‖A0'‖)
    (KJ := |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * ‖E20‖) (KD := |p.ωc * (p.core δ0 V0).Pδδ| * ‖E20‖)
    (ρ := 1) (ε0 := 1) (by positivity) hL hR (ForcedOrbit.continuous_harm _ _)
    (ForcedOrbit.harm_periodic _ hΩ2) (by positivity) one_pos one_pos
    (p.continuous_orbN δ0 V0 Vh (2 * Ω) A0')
    (fun ε t y => by simp only [orbN, p.nl_periodic δ0 V0 Vh hΩ2])
    (fun ε _ _ t => by rw [p.orbN_zero, norm_zero]; positivity)
    (fun ε hε _ t y1 y2 _ _ => p.orbN_lip δ0 V0 Vh (2 * Ω) A0' hε t y1 y2)
    (by positivity) (by positivity) (fun v => p.orbDx_bound δ0 V0 v)
    (p.continuous_orbDu δ0 V0 Vh (2 * Ω) A0') (p.continuous_orbJ δ0 V0 Vh (2 * Ω) A0')
    (fun ε hε _ t y _ => p.orbJ_taylor δ0 V0 Vh (2 * Ω) A0' hε t y) hpp hpd
    hΩ (neg_neg_of_pos hd2) rfl hr hu hur hr3 hu3 hur3 A0' _ hlink hs hg'

/-- End-to-end, voltage-modulated VSG, parametric instability: with `|λ₁| < |g_V/2|` the
variational equation along the forced orbit is Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_voltage_unstable {δ0 V0 Vh Ω : ℝ}
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (hΩ : 0 < Ω) (hω0 : p.ω0 ≠ 0) (hH : p.H ≠ 0)
    (hd2 : 0 < (p.core δ0 V0).d2) (hPδ : (p.core δ0 V0).Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : (p.core δ0 V0).a * (p.core δ0 V0).ωc = (Ω : ℂ) ^ 2)
    (hH2 : (p.core δ0 V0).d0 = ((p.core δ0 V0).a + (p.core δ0 V0).ωc) * (Ω : ℂ) ^ 2)
    (hg : ‖(p.core δ0 V0).left (Ω * I) ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ (p.core δ0 V0).right (Ω * I))‖ ^ 2 <
        ‖(p.core δ0 V0).gV V0 Ω Vh / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y ((p.core δ0 V0).A0r *ᵥ y t + (ε • p.orbB δ0 V0 Vh (2 * Ω) t +
            p.orbN δ0 V0 Vh (2 * Ω) A0' ε t (y t))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y ((p.core δ0 V0).A0r *ᵥ y t + (ε • p.orbB δ0 V0 Vh (2 * Ω) t +
            p.orbN δ0 V0 Vh (2 * Ω) A0' ε t (y t))) t) →
        Periodic.FloquetUnstable (fun t => p.orbJ δ0 V0 Vh (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨Minv, hL, hR, hpp, hpd, hlink, hpump⟩ :=
    p.orbit_data (Vh := Vh) A0' hΩ hω0 hH hd2 hPδ hV0 hH1 hH2
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := (p.core δ0 V0).hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hΩ2 : (2 * Ω) ≠ 0 := by positivity
  have hg' : ‖(p.core δ0 V0).left (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ (p.core δ0 V0).right (Ω * I))‖ ^ 2 <
      ‖(p.core δ0 V0).left (Ω * I) ⬝ᵥ ((p.core δ0 V0).A1
        ((p.core δ0 V0).forcedVδ (2 * Ω * I) Vh) Vh *ᵥ star ((p.core δ0 V0).right (Ω * I))) / 2‖ ^ 2 := by
    rw [hpump]; exact hg
  exact ForcedOrbit.orbit_floquet_three_unstable (Minv := Minv) (K := |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * ‖(e2 : Fin 3 → ℝ)‖ + ‖A0'‖)
    (KJ := |p.ωc * (p.E / p.X)| * (|V0| + |Vh|) * ‖E20‖) (KD := |p.ωc * (p.core δ0 V0).Pδδ| * ‖E20‖)
    (ρ := 1) (ε0 := 1) (by positivity) hL hR (ForcedOrbit.continuous_harm _ _)
    (ForcedOrbit.harm_periodic _ hΩ2) (by positivity) one_pos one_pos
    (p.continuous_orbN δ0 V0 Vh (2 * Ω) A0')
    (fun ε t y => by simp only [orbN, p.nl_periodic δ0 V0 Vh hΩ2])
    (fun ε _ _ t => by rw [p.orbN_zero, norm_zero]; positivity)
    (fun ε hε _ t y1 y2 _ _ => p.orbN_lip δ0 V0 Vh (2 * Ω) A0' hε t y1 y2)
    (by positivity) (by positivity) (fun v => p.orbDx_bound δ0 V0 v)
    (p.continuous_orbDu δ0 V0 Vh (2 * Ω) A0') (p.continuous_orbJ δ0 V0 Vh (2 * Ω) A0')
    (fun ε hε _ t y _ => p.orbJ_taylor δ0 V0 Vh (2 * Ω) A0' hε t y) hpp hpd
    hΩ (neg_neg_of_pos hd2) rfl hr hu hur hr3 hu3 hur3 A0' _ hlink hg'

end Model
end VoltageModulation
end powerlib.GFM
