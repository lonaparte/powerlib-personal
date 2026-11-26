import theorem.ParametricResonance.FieldTransfer
import theorem.GridTiedConverter.GFM.PSCOrbit
import theorem.GridTiedConverter.GFM.DVOCOrbit
import theorem.GridTiedConverter.GFM.DroopVoltageOrbit
import theorem.GridTiedConverter.GFM.MatchingVoltageOrbit

/-! # Five grid-forming cores: design-parameter changes and inactive limits, end-to-end

The end-to-end statements take the first-order state perturbation `εA₀'` as an input. Here it is
derived from a change of a physical design parameter of each core, `p → p + εp₁`: the changed
model's field is exactly the original field plus `εA₀'(x − x₀)` (`FieldTransfer`), `λ₁ = u A₀' r`
is computed in closed form, and the conclusions are restated for the changed model itself (its
own field and the Jacobian of its own variational equation). For three cores a static saturation
of the port map that is inactive at the operating point is also covered.

Model boundary.
* The models, operating points and Hopf conditions of `VoltageModulationSmooth` (VSG core),
  `PSCOrbit`, `DVOCOrbit`, `DroopVoltageOrbit` and `MatchingVoltageOrbit`, with grid voltage
  `V₀ + εV̂ cos 2Ωt`. The operating point is the Hopf point of the unperturbed parameters; the
  parameter change is `O(ε)` (the distinguished limit of the averaging step).
* Parameters that enter the field affinely in the state: VSG damping `D`, PSC gain `k`, dVOC
  proportional gain `k_p` (the dVOC synchronization gain `η` multiplies the port power and does
  not give a constant `A₀'`), droop gain `m_p`, matching DC gain `k_dc`.
* Saturation `max(−M, min(M, ·))` of the power map (VSG, droop) or the DC current (matching) with
  `|·| < M` at the operating point; the switching boundary is not covered. A current limiter acting
  on internal current references and network dynamics are not modelled; the dynamic Q–V loop is
  `VoltageModulationQVOrbit`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1 (`A₀(ε) = A₀c + εA₀'`, `λ₁ = l_mᴴ A₀' r_m`), §3 (the five
cores); the voltage excitation and the limits are new.

Results.
* VSG core: `damped`, `dampMat`, `sfield_damped`; `shift_damped` —
  `λ₁ = −(D₁/4H)(ω_c + jΩ)/(d₂ + jΩ)`; `re_shift_damped` — added damping gives `Re λ₁ < 0`;
  `orbit_damped_stable`, `orbit_damped_unstable`; `orbit_limited_stable`,
  `orbit_limited_unstable` (saturated power map).
* PSC: `gained`, `gainMat`, `rfield_gained`; `shift_gained` — `λ₁ = (k₁/k) jΩ(jΩ + ω_f)/D'(jΩ)`;
  `orbit_gained_stable`, `orbit_gained_unstable`.
* dVOC: `kpShift`, `kpMat`, `rfieldV_kp`; `shift_kp` — `λ₁ = ν_K η k_{p1}/(2(ν_P − ν_δ − j))`;
  `re_shift_kp` — `Re λ₁ = ν_K η k_{p1}(ν_P − ν_δ)/(2(1 + (ν_P − ν_δ)²))`;
  `differentiableAt_tube`; `orbit_kp_stable`, `orbit_kp_unstable`.
* Droop: `mpMat`, `dfield_mp`; `shift_mp` — `λ₁ = (m_{p1}/2m_p) jΩ(ω₁ + ω_m)/(ω₁ + ω_m + jΩ)`;
  `re_shift_mp` — `Re λ₁ = (m_{p1}/2m_p) Ω²(ω₁ + ω_m)/((ω₁ + ω_m)² + Ω²)`, so a lower droop gain
  stabilizes; `orbit_mp_stable`, `orbit_mp_unstable`; `orbit_droop_limited_stable`,
  `orbit_droop_limited_unstable`.
* Matching: `kdcShift`, `kdcMat`, `mfield_kdc`; `shift_kdc` — `λ₁ = −(k₁/τ) u_{i_s} r_v`;
  `orbit_kdc_stable`, `orbit_kdc_unstable`; `orbit_matching_limited_stable`,
  `orbit_matching_limited_unstable` (saturated DC current).

Corrections.
None: an extension (the unfolding `A₀'` from the design parameters, and inactive limits).

Family and connection conclusions.
None: static evidence on the voltage-modulated cores (forced orbit and Floquet multipliers of the
model with the changed parameter or with an inactive limit).
-/

noncomputable section
open Complex Matrix Filter Topology
open powerlib.ParametricResonance.ForcedOrbit (matX smJ smJ_shift smJ_congr_ball eventually_tube
  satMap exists_ball_sat_eq)

/-! ### Synchronizing core (VSG): damping `D + ε D₁`, power saturation -/

namespace powerlib.GFM.VoltageModulation.Core
variable (c : Core)

/-- The core with damping `D + ε D₁`. -/
def damped (ε D1 : ℝ) : Core := { c with D := c.D + ε * D1 }

/-- The state-matrix change of a damping change. -/
def dampMat (D1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, -(D1 / (2 * c.H)), 0; 0, 0, 0]

/-- A damping change `D → D + ε D₁` is exactly the perturbation `ε A₀'(x − x₀)`,
`A₀' = dampMat D₁`, of the end-to-end theorems. -/
@[tmio M, powerlib_domain] theorem sfield_damped (P : ℝ × ℝ → ℝ) (Pset δ0 V0 ε D1 : ℝ)
    (x : Fin 3 → ℝ) (w : ℝ) : (c.damped ε D1).sfield P Pset (x, w) =
      c.sfield P Pset (x, w) + ε • (c.dampMat D1 *ᵥ (x - sxeq P δ0 V0)) := by
  funext i
  fin_cases i <;> simp [sfield, damped, dampMat, sxeq, vecHead, vecTail]
  field_simp; ring

/-- `λ₁ = u A₀' r = −(D₁/4H)(ω_c + jΩ)/(d₂ + jΩ)` at the Hopf point. -/
@[tmio M, powerlib_domain] theorem shift_damped {Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (D1 : ℝ) :
    c.left (Ω * I) ⬝ᵥ ((c.dampMat D1).map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I)) =
      -((D1 / (4 * c.H) : ℝ) : ℂ) * ((c.ωc + Ω * I) / (c.d2 + Ω * I)) := by
  have hD := c.charD_hopf Ω hH1
  rw [a_add_ωc] at hD
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hn : (c.d2 : ℂ) + Ω * I ≠ 0 := Model.add_mul_I_ne hΩ
  simp only [left, right, dampMat, dotProduct, mulVec, Fin.sum_univ_three, Matrix.map_apply]
  simp only [hD]
  simp
  field_simp
  ring

/-- Re `λ₁ = −(D₁/4H)(ω_c d₂ + Ω²)/(d₂² + Ω²) < 0`: added damping (`D₁ > 0`, `H > 0`,
`ω_c ≥ 0`, `d₂ > 0`) moves the critical pair into the left half plane. -/
@[tmio M, powerlib_domain] theorem re_shift_damped {Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0)
    (hH : 0 < c.H) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hd2 : 0 < c.d2) (hωc : 0 ≤ c.ωc)
    {D1 : ℝ} (hD1 : 0 < D1) :
    (c.left (Ω * I) ⬝ᵥ ((c.dampMat D1).map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0 := by
  rw [c.shift_damped hΩ hω0 hH.ne' hH1]
  have hden : 0 < c.d2 ^ 2 + Ω ^ 2 := by positivity
  have hre : ((c.ωc + Ω * I) / (c.d2 + Ω * I)).re =
      (c.ωc * c.d2 + Ω ^ 2) / (c.d2 ^ 2 + Ω ^ 2) := by
    rw [Complex.div_re]; simp [Complex.normSq_apply]; field_simp
  have : (-((D1 / (4 * c.H) : ℝ) : ℂ) * ((c.ωc + Ω * I) / (c.d2 + Ω * I))).re =
      -(D1 / (4 * c.H)) * ((c.ωc * c.d2 + Ω ^ 2) / (c.d2 ^ 2 + Ω ^ 2)) := by
    rw [Complex.mul_re, hre]
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
      zero_mul, sub_zero]
  rw [this]
  have h1 : 0 < D1 / (4 * c.H) := by positivity
  have h2 : 0 < (c.ωc * c.d2 + Ω ^ 2) / (c.d2 ^ 2 + Ω ^ 2) := by
    have : 0 < Ω ^ 2 := by positivity
    positivity
  nlinarith

/-- VSG core with damping `D + εD₁` and grid voltage `V₀ + εV̂ cos 2Ωt`, end-to-end: the damping
change itself supplies `A₀'`. With `D₁ > 0` and `|g_V/2| < |λ₁|`,
`λ₁ = −(D₁/4H)(ω_c + jΩ)/(d₂ + jΩ)`, the system with the changed damping has, for all small
`ε > 0`, a forced periodic orbit whose variational equation has all Floquet multipliers inside
the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_damped_stable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : 0 < c.H) (hd2 : 0 < c.d2)
    (hωc : 0 ≤ c.ωc) (hPδ0 : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh : ℝ) {D1 : ℝ} (hD1 : 0 < D1)
    (hg : ‖c.gV V0 Ω Vh / 2‖ ^ 2 <
      ‖-((D1 / (4 * c.H) : ℝ) : ℂ) * ((c.ωc + Ω * I) / (c.d2 + Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((c.damped ε D1).sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((c.damped ε D1).sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => matX ((c.damped ε D1).sfield P (P (δ0, V0)))
            (sxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hd : ∀ q, DifferentiableAt ℝ (c.sfield P (P (δ0, V0))) q :=
    (c.contDiff_sfield hP _).differentiable (by norm_num)
  obtain ⟨k, hk, h1, h2⟩ := c.orbit_smooth_stable hP hΩ hω0 hH.ne' hd2 hPδ0 hV0 hH1 hH2 hPδ hPV
    hPδδ hPδV Vh (c.dampMat D1) (c.re_shift_damped hΩ.ne' hω0 hH hH1 hd2 hωc hD1)
    (by rw [c.shift_damped hΩ.ne' hω0 hH.ne' hH1]; exact hg)
  have hG := fun ε => c.sfield_damped P (P (δ0, V0)) δ0 V0 ε D1
  refine ⟨k, hk, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2.mono fun ε h y hy1 hy2 hy3 μ v hv hμ => h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · have := hy3 t; rwa [hG, add_sub_cancel_left] at this
  · rwa [smJ_shift (sxeq P δ0 V0, V0) (hG ε) Vh (2 * Ω) y fun t => hd _]

/-- VSG core with a damping change, parametric instability: `|λ₁| < |g_V/2|` makes the forced
orbit of the system with damping `D + εD₁` Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_damped_unstable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hPδ0 : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh D1 : ℝ)
    (hg : ‖-((D1 / (4 * c.H) : ℝ) : ℂ) * ((c.ωc + Ω * I) / (c.d2 + Ω * I))‖ ^ 2 <
      ‖c.gV V0 Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((c.damped ε D1).sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((c.damped ε D1).sfield P (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        Periodic.FloquetUnstable (fun t => matX ((c.damped ε D1).sfield P (P (δ0, V0)))
          (sxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t)))) (2 * Real.pi / (2 * Ω)) := by
  have hd : ∀ q, DifferentiableAt ℝ (c.sfield P (P (δ0, V0))) q :=
    (c.contDiff_sfield hP _).differentiable (by norm_num)
  obtain ⟨k, hk, h1, h2⟩ := c.orbit_smooth_unstable hP hΩ hω0 hH hd2 hPδ0 hV0 hH1 hH2 hPδ hPV
    hPδδ hPδV Vh (c.dampMat D1) (by rw [c.shift_damped hΩ.ne' hω0 hH hH1]; exact hg)
  have hG := fun ε => c.sfield_damped P (P (δ0, V0)) δ0 V0 ε D1
  refine ⟨k, hk, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2.mono fun ε h y hy1 hy2 hy3 => ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · rw [← smJ_shift (sxeq P δ0 V0, V0) (hG ε) Vh (2 * Ω) y fun t => hd _]
    exact h y hy1 hy2 fun t => by have := hy3 t; rwa [hG, add_sub_cancel_left] at this

/-- VSG core with a saturated power map `sat_M ∘ P` (a static power/current limit), end-to-end:
if the limit is inactive at the operating point (`|P(δ₀, V₀)| < M`), every conclusion of
`orbit_smooth_stable` holds for the limited system (its own field and its own Jacobian),
although `sat_M ∘ P` is not smooth. -/
@[tmio M, powerlib_domain] theorem orbit_limited_stable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hPδ0 : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV V0 Ω Vh / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2)
    {M : ℝ} (hM : |P (δ0, V0)| < M) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.sfield (satMap M P) (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.sfield (satMap M P) (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (c.sfield (satMap M P) (P (δ0, V0)))
            (sxeq P δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨k, hk, h1, h2⟩ := c.orbit_smooth_stable hP hΩ hω0 hH hd2 hPδ0 hV0 hH1 hH2 hPδ hPV
    hPδδ hPδV Vh A0' hs hg
  obtain ⟨r, hr, hsat⟩ := exists_ball_sat_eq (q0 := (sxeq P δ0 V0, V0)) 0
    hP.continuous.continuousAt (by simpa [sxeq] using hM)
  have hGF : ∀ q, ‖q - (sxeq P δ0 V0, V0)‖ < r →
      c.sfield (satMap M P) (P (δ0, V0)) q = c.sfield P (P (δ0, V0)) q := fun q hq => by
    simp only [sfield, hsat q hq]
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, ‖y t‖ ≤ k * ε) → ∀ t,
      ‖(sxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) - (sxeq P δ0 V0, V0)‖ < r :=
    (eventually_tube (sxeq P δ0 V0, V0) hr k Vh).mono fun ε h y hy t =>
      h (y t) _ (hy t) (Real.abs_cos_le_one _)
  refine ⟨k, hk, (h1.and hin).mono fun ε ⟨⟨y, hy1, hy2, hy3⟩, hε⟩ =>
    ⟨y, hy1, hy2, fun t => ?_⟩, (h2.and hin).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 μ v hv hμ =>
      h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hGF _ (hε y hy2 t)]; exact hy3 t
  · rw [← hGF _ (hε y hy2 t)]; exact hy3 t
  · rwa [smJ_congr_ball hGF Vh (2 * Ω) A0' ε y (hε y hy2)] at hμ

/-- VSG core with a saturated power map, parametric instability: with the limit inactive at the
operating point, `|λ₁| < |g_V/2|` makes the forced orbit of the limited system Floquet
unstable. -/
@[tmio M, powerlib_domain] theorem orbit_limited_unstable {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2)
    (hPδ0 : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (hPδ : Pd P (δ0, V0) = c.Pδ) (hPV : fderiv ℝ P (δ0, V0) (0, 1) = c.PV)
    (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = c.Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = c.PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖c.gV V0 Ω Vh / 2‖ ^ 2)
    {M : ℝ} (hM : |P (δ0, V0)| < M) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.sfield (satMap M P) (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.sfield (satMap M P) (P (δ0, V0)) (sxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (c.sfield (satMap M P) (P (δ0, V0)))
          (sxeq P δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨k, hk, h1, h2⟩ := c.orbit_smooth_unstable hP hΩ hω0 hH hd2 hPδ0 hV0 hH1 hH2 hPδ hPV
    hPδδ hPδV Vh A0' hg
  obtain ⟨r, hr, hsat⟩ := exists_ball_sat_eq (q0 := (sxeq P δ0 V0, V0)) 0
    hP.continuous.continuousAt (by simpa [sxeq] using hM)
  have hGF : ∀ q, ‖q - (sxeq P δ0 V0, V0)‖ < r →
      c.sfield (satMap M P) (P (δ0, V0)) q = c.sfield P (P (δ0, V0)) q := fun q hq => by
    simp only [sfield, hsat q hq]
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, ‖y t‖ ≤ k * ε) → ∀ t,
      ‖(sxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) - (sxeq P δ0 V0, V0)‖ < r :=
    (eventually_tube (sxeq P δ0 V0, V0) hr k Vh).mono fun ε h y hy t =>
      h (y t) _ (hy t) (Real.abs_cos_le_one _)
  refine ⟨k, hk, (h1.and hin).mono fun ε ⟨⟨y, hy1, hy2, hy3⟩, hε⟩ =>
    ⟨y, hy1, hy2, fun t => ?_⟩, (h2.and hin).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 => ?_⟩
  · rw [hGF _ (hε y hy2 t)]; exact hy3 t
  · rw [smJ_congr_ball hGF Vh (2 * Ω) A0' ε y (hε y hy2)]
    exact h y hy1 hy2 fun t => by rw [← hGF _ (hε y hy2 t)]; exact hy3 t

end powerlib.GFM.VoltageModulation.Core


/-! ### PSC: synchronization gain `k + ε k₁` -/

namespace powerlib.GFM.PSCFull.Model
variable (p : Model)

/-- The PSC with gain `k + ε k₁`. -/
def gained (ε k1 : ℝ) : Model := { p with k := p.k + ε * k1 }

/-- The state-matrix change of a gain change (real coordinates). -/
def gainMat (k1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -k1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- A gain change `k → k + ε k₁` is exactly the perturbation `ε A₀'(x − x₀)`,
`A₀' = gainMat k₁`. -/
@[tmio M, powerlib_domain] theorem rfield_gained (δ0 ε k1 : ℝ) (x : Fin 4 → ℝ) (V : ℝ) :
    (p.gained ε k1).rfield (p.Peq δ0) (x, V) =
      p.rfield (p.Peq δ0) (x, V) + ε • (gainMat k1 *ᵥ (x - p.xeq δ0)) := by
  funext i
  fin_cases i
  · simp [rfield, gained, gainMat, xeq, vecHead, vecTail]; ring
  all_goals
    simp only [Pi.add_apply, Pi.smul_apply, gainMat]
    simp [mulVec, dotProduct, Fin.sum_univ_four]
    rfl

/-- `λ₁ = u A₀' r = (k₁/k) λ(λ + ω_f)/D'(λ)` at `λ = jΩ`. -/
@[tmio M, powerlib_domain] theorem shift_gained (δ0 Ω k1 : ℝ) (hk : p.k ≠ 0) :
    p.shift δ0 Ω (gainMat k1) = ((k1 / p.k : ℝ) : ℂ) * (((Ω : ℂ) * I) * ((Ω : ℂ) * I + p.ωf) /
      (p.coeffs δ0).Dd ((Ω : ℂ) * I)) := by
  have hkc : (p.k : ℂ) ≠ 0 := by exact_mod_cast hk
  simp only [shift, umode, rmode]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]
  simp [gainMat, realify, realifyInv, Coeffs.left, Coeffs.right, coeffs, vecMul, mulVec,
    dotProduct, Fin.sum_univ_four, Matrix.mul_apply]
  field_simp
  ring

/-- PSC with gain `k + εk₁` and grid voltage `V + εV̂ cos 2Ωt`, end-to-end without a stable
basis among the hypotheses: the gain change supplies `A₀'`, `λ₁ = (k₁/k) jΩ(jΩ + ω_f)/D'(jΩ)`;
`Re λ₁ < 0` and `|g_V/2| < |λ₁|` give the forced orbit of the system with the changed gain and
all Floquet multipliers of its variational equation inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_gained_stable (δ0 : ℝ) (hZ : p.Z ≠ 0)
    (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    (hD2 : (p.coeffs δ0).D (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (h12 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h22 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (p.Jreal δ0)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (p.rmode δ0 Ω) *
        ParametricResonance.ForcedOrbit.critQ (p.umode δ0 Ω))).map (algebraMap ℝ ℂ)) < 1)
    (Vh k1 : ℝ)
    (hs : (((k1 / p.k : ℝ) : ℂ) * (((Ω : ℂ) * I) * ((Ω : ℂ) * I + p.ωf) /
      (p.coeffs δ0).Dd ((Ω : ℂ) * I))).re < 0)
    (hg : ‖p.pumpV δ0 Ω Vh / 2‖ ^ 2 < ‖((k1 / p.k : ℝ) : ℂ) * (((Ω : ℂ) * I) *
      ((Ω : ℂ) * I + p.ωf) / (p.coeffs δ0).Dd ((Ω : ℂ) * I))‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y ((p.gained ε k1).rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y ((p.gained ε k1).rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => matX ((p.gained ε k1).rfield (p.Peq δ0))
            (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t))))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hd : ∀ q, DifferentiableAt ℝ (p.rfield (p.Peq δ0)) q :=
    (p.contDiff_rfield (p.Peq δ0) (n := 1)).differentiable (by norm_num)
  obtain ⟨c, hc, h1', h2'⟩ := p.orbit_voltage_stable_spec δ0 hZ hZ0 hΩ hk h1 h2 hD hDd hD2 h12
    h22 hsr Vh (gainMat k1) (by rw [p.shift_gained δ0 Ω k1 hk]; exact hs)
    (by rw [p.shift_gained δ0 Ω k1 hk]; exact hg)
  have hG := fun ε => p.rfield_gained δ0 ε k1
  refine ⟨c, hc, h1'.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2'.mono fun ε h y hy1 hy2 hy3 μ v hv hμ => h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · have := hy3 t; rwa [hG, add_sub_cancel_left] at this
  · rwa [smJ_shift (p.xeq δ0, p.V) (hG ε) Vh (2 * Ω) y fun t => hd _]

/-- PSC with a gain change, parametric instability: `|λ₁| < |g_V/2|` makes the forced orbit of
the system with gain `k + εk₁` Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_gained_unstable (δ0 : ℝ) (hZ : p.Z ≠ 0)
    (hZ0 : p.Z0 ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    (hD2 : (p.coeffs δ0).D (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (h12 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h22 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (p.Jreal δ0)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (p.rmode δ0 Ω) *
        ParametricResonance.ForcedOrbit.critQ (p.umode δ0 Ω))).map (algebraMap ℝ ℂ)) < 1)
    (Vh k1 : ℝ)
    (hg : ‖((k1 / p.k : ℝ) : ℂ) * (((Ω : ℂ) * I) * ((Ω : ℂ) * I + p.ωf) /
      (p.coeffs δ0).Dd ((Ω : ℂ) * I))‖ ^ 2 < ‖p.pumpV δ0 Ω Vh / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y ((p.gained ε k1).rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y ((p.gained ε k1).rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        Periodic.FloquetUnstable (fun t => matX ((p.gained ε k1).rfield (p.Peq δ0))
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t)))) (2 * Real.pi / (2 * Ω)) := by
  have hd : ∀ q, DifferentiableAt ℝ (p.rfield (p.Peq δ0)) q :=
    (p.contDiff_rfield (p.Peq δ0) (n := 1)).differentiable (by norm_num)
  obtain ⟨c, hc, h1', h2'⟩ := p.orbit_voltage_unstable_spec δ0 hZ hZ0 hΩ hk h1 h2 hD hDd hD2 h12
    h22 hsr Vh (gainMat k1) (by rw [p.shift_gained δ0 Ω k1 hk]; exact hg)
  have hG := fun ε => p.rfield_gained δ0 ε k1
  refine ⟨c, hc, h1'.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2'.mono fun ε h y hy1 hy2 hy3 => ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · rw [← smJ_shift (p.xeq δ0, p.V) (hG ε) Vh (2 * Ω) y fun t => hd _]
    exact h y hy1 hy2 fun t => by have := hy3 t; rwa [hG, add_sub_cancel_left] at this

end powerlib.GFM.PSCFull.Model


/-! ### dVOC: proportional DC gain `k_p + ε k_{p1}` -/

namespace powerlib.GFM.DVOCCore
variable (d : DVOCCore)

/-- The dVOC core with proportional gain `k_p + ε k_{p1}`. -/
def kpShift (ε kp1 : ℝ) : DVOCCore := { d with kp := d.kp + ε * kp1 }

/-- The state-matrix change of a `k_p` change. -/
def kpMat (η kp1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, η * kp1, 0; 0, 0, 0; 0, 0, 0]

/-- A gain change `k_p → k_p + ε k_{p1}` is exactly the perturbation `ε A₀'(x − x₀)`,
`A₀' = kpMat η k_{p1}`. -/
@[tmio M, powerlib_domain] theorem rfieldV_kp (V0 Ψ0 ε kp1 : ℝ) (x : Fin 3 → ℝ) (V : ℝ) :
    (d.kpShift ε kp1).rfieldV V0 (x, V) =
      d.rfieldV V0 (x, V) + ε • (kpMat d.η kp1 *ᵥ (x - xeq Ψ0)) := by
  funext i
  fin_cases i <;> simp [rfieldV, kpShift, kpMat, xeq, vecHead, vecTail]
  ring

omit d in
/-- `λ₁ = u A₀' r = ν_K η k_{p1}/(2(ν_P − ν_δ − j))` at the normalized Hopf point. -/
@[tmio M, powerlib_domain] theorem shift_kp (νδ νP νK η kp1 : ℝ) :
    left νδ νP νK ⬝ᵥ ((kpMat η kp1).map (algebraMap ℝ ℂ) *ᵥ right νP νK) =
      ((νK * (η * kp1) : ℝ) : ℂ) / (2 * ((νP : ℂ) - νδ - I)) := by
  simp [left, right, kpMat, dotProduct, mulVec, Fin.sum_univ_three]
  ring_nf
  rw [I_sq]
  ring

omit d in
/-- Re `λ₁ = ν_K η k_{p1}(ν_P − ν_δ)/(2(1 + (ν_P − ν_δ)²))`. -/
@[tmio M, powerlib_domain] theorem re_shift_kp (νδ νP νK η kp1 : ℝ) :
    (left νδ νP νK ⬝ᵥ ((kpMat η kp1).map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re =
      νK * (η * kp1) * (νP - νδ) / (2 * (1 + (νP - νδ) ^ 2)) := by
  rw [shift_kp, Complex.div_re]
  simp [Complex.normSq_apply]
  field_simp
  ring

/-- The state `xeq Ψ₀ + y` keeps `v_dc ≠ 0` while `‖y‖ < 1`, so the dVOC field is differentiable
along every orbit of the tube for `cε < 1`. -/
@[tmio M, powerlib_domain] theorem differentiableAt_tube (hp : ContDiff ℝ 3 d.p) (V0 Ψ0 : ℝ)
    {y : Fin 3 → ℝ} (hy : ‖y‖ < 1) (V : ℝ) :
    DifferentiableAt ℝ (d.rfieldV V0) (xeq Ψ0 + y, V) := by
  have h1 := norm_le_pi_norm y 1
  rw [Real.norm_eq_abs] at h1
  have hx : (xeq Ψ0 + y) 1 ≠ 0 := by
    simp only [xeq, Pi.add_apply]
    intro h
    have := (abs_lt.1 (lt_of_le_of_lt h1 hy)).1
    simp at h
    linarith
  exact (d.contDiffAt_rfieldV V0 hp hx).differentiableAt (by norm_num)

/-- dVOC with gain `k_p + εk_{p1}` and grid voltage `V₀ + εV̂ cos 2t`, end-to-end: the gain
change supplies `A₀'`. With `ν_P < ν_δ` and `ν_K η k_{p1} > 0` (`Re λ₁ < 0`) and
`|g_V/2| < |λ₁|`, the system with the changed gain has the forced periodic orbit with all
Floquet multipliers of its variational equation inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_kp_stable {V0 Ψ0 K P2 τ νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (hτ : P2 = -(τ * K)) (hδ : d.η * K = νδ)
    (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ) (Vh : ℝ) {kp1 : ℝ} (hkp1 : 0 < νK * (d.η * kp1))
    (hg : ‖-(I * ((Vh / V0 : ℝ) : ℂ) / (6 * νK)) * (numV νδ νP νK τ / denD νδ νP) / 2‖ ^ 2 <
      ‖((νK * (d.η * kp1) : ℝ) : ℂ) / (2 * ((νP : ℂ) - νδ - I))‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) ∧
        (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y ((d.kpShift ε kp1).rfieldV V0
          (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y ((d.kpShift ε kp1).rfieldV V0
          (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t)))) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => matX ((d.kpShift ε kp1).rfieldV V0)
            (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t)))) (2 * Real.pi / 2) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hre : (left νδ νP νK ⬝ᵥ ((kpMat d.η kp1).map (algebraMap ℝ ℂ) *ᵥ right νP νK)).re < 0 := by
    rw [re_shift_kp]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hkp1 (by linarith)) (by positivity)
  obtain ⟨c, hc, h1, h2⟩ := d.orbit_voltage_stable hp hpe hP hP2 hτ hδ hPn hKn hνK hkp hki hV0
    hi Vh (kpMat d.η kp1) hre (by rw [shift_kp]; exact hg)
  have hG := fun ε => d.rfieldV_kp V0 Ψ0 ε kp1
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * ε < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (c + 1) by positivity)] with ε hε
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < c + 1)).1 hε.2
    nlinarith [hε.1]
  refine ⟨c, hc, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    (h2.and hsmall).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 μ v hv hμ =>
      h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · have := hy3 t; rwa [hG, add_sub_cancel_left] at this
  · rwa [smJ_shift (xeq Ψ0, V0) (hG ε) Vh 2 y fun t =>
      d.differentiableAt_tube hp V0 Ψ0 ((hy2 t).trans_lt hε) _]

/-- dVOC with a `k_p` change, parametric instability: `|λ₁| < |g_V/2|` makes the forced orbit
of the system with gain `k_p + εk_{p1}` Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_kp_unstable {V0 Ψ0 K P2 τ νδ νP νK : ℝ}
    (hp : ContDiff ℝ 3 d.p) (hpe : d.p Ψ0 = d.P0) (hP : HasDerivAt d.p K Ψ0)
    (hP2 : HasDerivAt (deriv d.p) P2 Ψ0) (hτ : P2 = -(τ * K)) (hδ : d.η * K = νδ)
    (hPn : d.P0 / d.C = νP) (hKn : K / d.C = νK) (hνK : νK ≠ 0)
    (hkp : d.η * d.kp = (1 + νδ * νP) / νK) (hki : d.η * d.ki = (νδ - νP) / νK)
    (hV0 : V0 ≠ 0) (hi : νP < νδ) (Vh kp1 : ℝ)
    (hg : ‖((νK * (d.η * kp1) : ℝ) : ℂ) / (2 * ((νP : ℂ) - νδ - I))‖ ^ 2 <
      ‖-(I * ((Vh / V0 : ℝ) : ℂ) / (6 * νK)) * (numV νδ νP νK τ / denD νδ νP) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) ∧
        (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y ((d.kpShift ε kp1).rfieldV V0
          (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / 2) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y ((d.kpShift ε kp1).rfieldV V0
          (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t)))) t) →
        Periodic.FloquetUnstable (fun t => matX ((d.kpShift ε kp1).rfieldV V0)
          (xeq Ψ0 + y t, V0 + ε * (Vh * Real.cos (2 * t)))) (2 * Real.pi / 2) := by
  obtain ⟨c, hc, h1, h2⟩ := d.orbit_voltage_unstable hp hpe hP hP2 hτ hδ hPn hKn hνK hkp hki
    hV0 hi Vh (kpMat d.η kp1) (by rw [shift_kp]; exact hg)
  have hG := fun ε => d.rfieldV_kp V0 Ψ0 ε kp1
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * ε < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (c + 1) by positivity)] with ε hε
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < c + 1)).1 hε.2
    nlinarith [hε.1]
  refine ⟨c, hc, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    (h2.and hsmall).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 => ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · rw [← smJ_shift (xeq Ψ0, V0) (hG ε) Vh 2 y fun t =>
      d.differentiableAt_tube hp V0 Ψ0 ((hy2 t).trans_lt hε) _]
    exact h y hy1 hy2 fun t => by have := hy3 t; rwa [hG, add_sub_cancel_left] at this

end powerlib.GFM.DVOCCore


/-! ### Droop with two filters: droop gain `m_p + ε m_{p1}`, power saturation -/

namespace powerlib.GFM.VoltageModulation.Droop
open powerlib.GFM.VoltageModulation.Core (Pd)

/-- The state-matrix change of a droop-gain change. -/
def mpMat (mp1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, -mp1; 0, 0, 0; 0, 0, 0]

/-- A droop-gain change `m_p → m_p + ε m_{p1}` is exactly the perturbation `ε A₀'(x − x₀)`,
`A₀' = mpMat m_{p1}`. -/
@[tmio M, powerlib_domain] theorem dfield_mp (mp ω1 ωm ε mp1 : ℝ) (P : ℝ × ℝ → ℝ) (δ0 V0 : ℝ)
    (x : Fin 3 → ℝ) (V : ℝ) :
    dfield (mp + ε * mp1) ω1 ωm P (P (δ0, V0)) (x, V) =
      dfield mp ω1 ωm P (P (δ0, V0)) (x, V) + ε • (mpMat mp1 *ᵥ (x - dxeq P δ0 V0)) := by
  funext i
  fin_cases i <;> simp [dfield, mpMat, dxeq, vecHead, vecTail]
  ring

/-- `λ₁ = u_d A₀' r_d = (m_{p1}/2m_p) jΩ(ω₁ + ω_m)/(ω₁ + ω_m + jΩ)` at the Hopf point. -/
@[tmio M, powerlib_domain] theorem shift_mp {mp ω1 ωm Ω : ℝ} (Pδ PV Pδδ PδV : ℝ) (hΩ : Ω ≠ 0)
    (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2) (mp1 : ℝ) :
    dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        ((mpMat mp1).map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω) =
      ((mp1 / (2 * mp) : ℝ) : ℂ) * ((Ω : ℂ) * I * (ω1 + ωm) / (((ω1 + ωm : ℝ) : ℂ) + Ω * I)) := by
  have ha := core_a mp ω1 ωm Pδ PV Pδδ PδV hmp hω1
  have hH1c : (ω1 : ℂ) * ωm = (Ω : ℂ) ^ 2 := by exact_mod_cast hH1
  have hD := (core mp ω1 ωm Pδ PV Pδδ PδV).charD_hopf Ω (by rw [ha]; exact hH1c)
  rw [ha] at hD
  have hn : ((ω1 + ωm : ℝ) : ℂ) + Ω * I ≠ 0 := Model.add_mul_I_ne hΩ
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hmpc : (mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hω1c : (ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  have hn2 : (ω1 : ℂ) + ωm + Ω * I ≠ 0 := by simpa using hn
  simp only [dleft, dright, Core.left, Core.right, hD, ha]
  simp [core, Lm, Li, mpMat, vecMul, mulVec, dotProduct, Fin.sum_univ_three]
  field_simp
  linear_combination (mp1 : ℂ) * hH1c + ((mp1 : ℂ) * (Ω : ℂ) ^ 2) * I_sq

/-- Re `λ₁ = (m_{p1}/2m_p) Ω²(ω₁ + ω_m)/((ω₁ + ω_m)² + Ω²)`: raising the droop gain
(`m_{p1}/m_p > 0`) pushes the critical pair to the right, lowering it to the left. -/
@[tmio M, powerlib_domain] theorem re_shift_mp {mp ω1 ωm Ω : ℝ} (Pδ PV Pδδ PδV : ℝ)
    (hΩ : Ω ≠ 0) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2) (hd2 : 0 < ω1 + ωm)
    (mp1 : ℝ) :
    (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        ((mpMat mp1).map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)).re =
      mp1 / (2 * mp) * (Ω ^ 2 * (ω1 + ωm) / ((ω1 + ωm) ^ 2 + Ω ^ 2)) := by
  rw [shift_mp Pδ PV Pδδ PδV hΩ hmp hω1 hH1, Complex.re_ofReal_mul, Complex.div_re]
  have : 0 < (ω1 + ωm) ^ 2 + Ω ^ 2 := by positivity
  simp [Complex.normSq_apply, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  field_simp

/-- Droop with droop gain `m_p + εm_{p1}` and grid voltage `V₀ + εV̂ cos 2Ωt`, end-to-end: the
gain change supplies `A₀'`. A lowered gain (`m_{p1}/m_p < 0`, hence `Re λ₁ < 0`) with
`|g_V/2| < |λ₁|` gives the forced orbit of the system with the changed gain and all Floquet
multipliers of its variational equation inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_mp_stable {mp ω1 ωm : ℝ} {P : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) {mp1 : ℝ} (hmp1 : mp1 / mp < 0)
    (hg : ‖(core mp ω1 ωm Pδ PV Pδδ PδV).gV V0 Ω Vh / 2‖ ^ 2 <
      ‖((mp1 / (2 * mp) : ℝ) : ℂ) * ((Ω : ℂ) * I * (ω1 + ωm) / (((ω1 + ωm : ℝ) : ℂ) + Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (dfield (mp + ε * mp1) ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (dfield (mp + ε * mp1) ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => matX (dfield (mp + ε * mp1) ω1 ωm P (P (δ0, V0)))
            (dxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hd : ∀ q, DifferentiableAt ℝ (dfield mp ω1 ωm P (P (δ0, V0))) q :=
    (contDiff_dfield mp ω1 ωm hP _).differentiable (by norm_num)
  have hre : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
      ((mpMat mp1).map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)).re < 0 := by
    rw [re_shift_mp Pδ PV Pδδ PδV hΩ.ne' hmp hω1 hH1 hd2, show mp1 / (2 * mp) = mp1 / mp / 2 by
      rw [div_div, mul_comm]]
    have : 0 < Ω ^ 2 := by positivity
    exact mul_neg_of_neg_of_pos (by linarith) (by positivity)
  obtain ⟨k, hk, h1, h2⟩ := orbit_droop_stable mp ω1 ωm hP hΩ hmp hω1 hd2 hPδ0 hV0 hH1 hH2 hPδ
    hPV hPδδ hPδV Vh (mpMat mp1) hre
    (by rw [shift_mp Pδ PV Pδδ PδV hΩ.ne' hmp hω1 hH1]; exact hg)
  have hG := fun ε => dfield_mp mp ω1 ωm ε mp1 P δ0 V0
  refine ⟨k, hk, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2.mono fun ε h y hy1 hy2 hy3 μ v hv hμ => h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · have := hy3 t; rwa [hG, add_sub_cancel_left] at this
  · rwa [smJ_shift (dxeq P δ0 V0, V0) (hG ε) Vh (2 * Ω) y fun t => hd _]

/-- Droop with a droop-gain change, parametric instability: `|λ₁| < |g_V/2|` makes the forced
orbit of the system with gain `m_p + εm_{p1}` Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_mp_unstable {mp ω1 ωm : ℝ} {P : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh mp1 : ℝ)
    (hg : ‖((mp1 / (2 * mp) : ℝ) : ℂ) * ((Ω : ℂ) * I * (ω1 + ωm) /
      (((ω1 + ωm : ℝ) : ℂ) + Ω * I))‖ ^ 2 < ‖(core mp ω1 ωm Pδ PV Pδδ PδV).gV V0 Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (dfield (mp + ε * mp1) ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (dfield (mp + ε * mp1) ω1 ωm P (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        Periodic.FloquetUnstable (fun t => matX (dfield (mp + ε * mp1) ω1 ωm P (P (δ0, V0)))
          (dxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t)))) (2 * Real.pi / (2 * Ω)) := by
  have hd : ∀ q, DifferentiableAt ℝ (dfield mp ω1 ωm P (P (δ0, V0))) q :=
    (contDiff_dfield mp ω1 ωm hP _).differentiable (by norm_num)
  obtain ⟨k, hk, h1, h2⟩ := orbit_droop_unstable mp ω1 ωm hP hΩ hmp hω1 hd2 hPδ0 hV0 hH1 hH2
    hPδ hPV hPδδ hPδV Vh (mpMat mp1)
    (by rw [shift_mp Pδ PV Pδδ PδV hΩ.ne' hmp hω1 hH1]; exact hg)
  have hG := fun ε => dfield_mp mp ω1 ωm ε mp1 P δ0 V0
  refine ⟨k, hk, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2.mono fun ε h y hy1 hy2 hy3 => ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · rw [← smJ_shift (dxeq P δ0 V0, V0) (hG ε) Vh (2 * Ω) y fun t => hd _]
    exact h y hy1 hy2 fun t => by have := hy3 t; rwa [hG, add_sub_cancel_left] at this

/-- Droop with a saturated power map `sat_M ∘ P`, end-to-end: with the limit inactive at the
operating point (`|P(δ₀, V₀)| < M`), every conclusion of `orbit_droop_stable` holds for the
limited system. -/
@[tmio M, powerlib_domain] theorem orbit_droop_limited_stable {mp ω1 ωm : ℝ} {P : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)).re < 0)
    (hg : ‖(core mp ω1 ωm Pδ PV Pδδ PδV).gV V0 Ω Vh / 2‖ ^ 2 <
      ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2)
    {M : ℝ} (hM : |P (δ0, V0)| < M) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (dfield mp ω1 ωm (satMap M P) (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (dfield mp ω1 ωm (satMap M P) (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (dfield mp ω1 ωm (satMap M P) (P (δ0, V0)))
            (dxeq P δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨k, hk, h1, h2⟩ := orbit_droop_stable mp ω1 ωm hP hΩ hmp hω1 hd2 hPδ0 hV0 hH1 hH2 hPδ
    hPV hPδδ hPδV Vh A0' hs hg
  obtain ⟨r, hr, hsat⟩ := exists_ball_sat_eq (q0 := (dxeq P δ0 V0, V0)) 0
    hP.continuous.continuousAt (by simpa [dxeq] using hM)
  have hGF : ∀ q, ‖q - (dxeq P δ0 V0, V0)‖ < r →
      dfield mp ω1 ωm (satMap M P) (P (δ0, V0)) q = dfield mp ω1 ωm P (P (δ0, V0)) q :=
    fun q hq => by simp only [dfield, hsat q hq]
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, ‖y t‖ ≤ k * ε) → ∀ t,
      ‖(dxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) - (dxeq P δ0 V0, V0)‖ < r :=
    (eventually_tube (dxeq P δ0 V0, V0) hr k Vh).mono fun ε h y hy t =>
      h (y t) _ (hy t) (Real.abs_cos_le_one _)
  refine ⟨k, hk, (h1.and hin).mono fun ε ⟨⟨y, hy1, hy2, hy3⟩, hε⟩ =>
    ⟨y, hy1, hy2, fun t => ?_⟩, (h2.and hin).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 μ v hv hμ =>
      h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hGF _ (hε y hy2 t)]; exact hy3 t
  · rw [← hGF _ (hε y hy2 t)]; exact hy3 t
  · rwa [smJ_congr_ball hGF Vh (2 * Ω) A0' ε y (hε y hy2)] at hμ

/-- Droop with a saturated power map, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_droop_limited_unstable {mp ω1 ωm : ℝ}
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    {δ0 V0 Ω Pδ PV Pδδ PδV : ℝ} (hΩ : 0 < Ω) (hmp : mp ≠ 0) (hω1 : ω1 ≠ 0)
    (hd2 : 0 < ω1 + ωm) (hPδ0 : Pδ ≠ 0) (hV0 : V0 ≠ 0) (hH1 : ω1 * ωm = Ω ^ 2)
    (hH2 : mp * ω1 * ωm * Pδ = (ω1 + ωm) * Ω ^ 2) (hPδ : Pd P (δ0, V0) = Pδ)
    (hPV : fderiv ℝ P (δ0, V0) (0, 1) = PV) (hPδδ : fderiv ℝ (Pd P) (δ0, V0) (1, 0) = Pδδ)
    (hPδV : fderiv ℝ (Pd P) (δ0, V0) (0, 1) = PδV) (Vh : ℝ) (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖dleft mp ω1 ωm Pδ PV Pδδ PδV Ω ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ dright mp ω1 ωm Pδ PV Pδδ PδV Ω)‖ ^ 2 <
      ‖(core mp ω1 ωm Pδ PV Pδδ PδV).gV V0 Ω Vh / 2‖ ^ 2)
    {M : ℝ} (hM : |P (δ0, V0)| < M) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (dfield mp ω1 ωm (satMap M P) (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (dfield mp ω1 ωm (satMap M P) (P (δ0, V0)) (dxeq P δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (dfield mp ω1 ωm (satMap M P) (P (δ0, V0)))
          (dxeq P δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨k, hk, h1, h2⟩ := orbit_droop_unstable mp ω1 ωm hP hΩ hmp hω1 hd2 hPδ0 hV0 hH1 hH2
    hPδ hPV hPδδ hPδV Vh A0' hg
  obtain ⟨r, hr, hsat⟩ := exists_ball_sat_eq (q0 := (dxeq P δ0 V0, V0)) 0
    hP.continuous.continuousAt (by simpa [dxeq] using hM)
  have hGF : ∀ q, ‖q - (dxeq P δ0 V0, V0)‖ < r →
      dfield mp ω1 ωm (satMap M P) (P (δ0, V0)) q = dfield mp ω1 ωm P (P (δ0, V0)) q :=
    fun q hq => by simp only [dfield, hsat q hq]
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, ‖y t‖ ≤ k * ε) → ∀ t,
      ‖(dxeq P δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) - (dxeq P δ0 V0, V0)‖ < r :=
    (eventually_tube (dxeq P δ0 V0, V0) hr k Vh).mono fun ε h y hy t =>
      h (y t) _ (hy t) (Real.abs_cos_le_one _)
  refine ⟨k, hk, (h1.and hin).mono fun ε ⟨⟨y, hy1, hy2, hy3⟩, hε⟩ =>
    ⟨y, hy1, hy2, fun t => ?_⟩, (h2.and hin).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 => ?_⟩
  · rw [hGF _ (hε y hy2 t)]; exact hy3 t
  · rw [smJ_congr_ball hGF Vh (2 * Ω) A0' ε y (hε y hy2)]
    exact h y hy1 hy2 fun t => by rw [← hGF _ (hε y hy2 t)]; exact hy3 t

end powerlib.GFM.VoltageModulation.Droop


/-! ### Matching control: DC gain `k_dc + ε k₁`, DC-current saturation -/

namespace powerlib.GFM.Matching.MatchingCore
open powerlib.GFM.VoltageModulation.Core (Pd)
variable (d : MatchingCore)

/-- The matching core with DC gain `k_dc + ε k₁`. -/
def kdcShift (ε k1 : ℝ) : MatchingCore := { d with kdc := d.kdc + ε * k1 }

/-- The state-matrix change of a `k_dc` change. -/
def kdcMat (τ k1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, -(k1 / τ), 0]

/-- A gain change `k_dc → k_dc + ε k₁` is exactly the perturbation `ε A₀'(x − x₀)`,
`A₀' = kdcMat τ k₁`. -/
@[tmio M, powerlib_domain] theorem mfield_kdc (ixV : ℝ × ℝ → ℝ) (Istar δ0 V0 ε k1 : ℝ)
    (x : Fin 4 → ℝ) (V : ℝ) :
    (d.kdcShift ε k1).mfield ixV Istar (x, V) =
      d.mfield ixV Istar (x, V) + ε • (kdcMat d.τ k1 *ᵥ (x - d.meq ixV δ0 V0)) := by
  funext i
  fin_cases i <;> simp [mfield, kdcShift, kdcMat, meq, vecHead, vecTail]
  ring

omit d in
/-- `λ₁ = u A₀' r = −(k₁/τ) u_{i_s} r_v`. -/
@[tmio M, powerlib_domain] theorem shift_kdc (τ k1 : ℝ) (u r : Fin 4 → ℂ) :
    u ⬝ᵥ ((kdcMat τ k1).map (algebraMap ℝ ℂ) *ᵥ r) = -((k1 / τ : ℝ) : ℂ) * (u 3 * r 2) := by
  simp [kdcMat, dotProduct, mulVec, Fin.sum_univ_four]
  ring

/-- Matching control with DC gain `k_dc + εk₁` and grid voltage `V₀ + εV̂ cos 2Ωt`,
end-to-end without a stable basis among the hypotheses: the gain change supplies `A₀'`,
`λ₁ = −(k₁/τ) u_{i_s} r_v`; `Re λ₁ < 0` and `|g_V/2| < |λ₁|` give the forced orbit of the system
with the changed gain and all Floquet multipliers of its variational equation inside the unit
circle. -/
@[tmio M, powerlib_domain] theorem orbit_kdc_stable {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV Kδδ KδV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (d.jacobian K)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP r *
        ParametricResonance.ForcedOrbit.critQ u)).map (algebraMap ℝ ℂ)) < 1)
    (Vh k1 : ℝ) (hs : (-((k1 / d.τ : ℝ) : ℂ) * (u 3 * r 2)).re < 0)
    (hg : ‖d.mpumpV u r K Kδδ KδV KV Ω Vh / 2‖ ^ 2 < ‖-((k1 / d.τ : ℝ) : ℂ) * (u 3 * r 2)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y ((d.kdcShift ε k1).mfield ixV (d.G + ixV (δ0, V0))
          (d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y ((d.kdcShift ε k1).mfield ixV (d.G + ixV (δ0, V0))
          (d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => matX ((d.kdcShift ε k1).mfield ixV (d.G + ixV (δ0, V0)))
            (d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hd : ∀ q, DifferentiableAt ℝ (d.mfield ixV (d.G + ixV (δ0, V0))) q :=
    (d.contDiff_mfield hP _).differentiable (by norm_num)
  obtain ⟨c, hc, h1, h2⟩ := d.orbit_matching_stable_spec hP hΩ hωb hωf hC hτ hK hKV hKδδ hKδV
    hD2 hr hu hur hsr Vh (kdcMat d.τ k1) (by rw [shift_kdc]; exact hs)
    (by rw [shift_kdc]; exact hg)
  have hG := fun ε => d.mfield_kdc ixV (d.G + ixV (δ0, V0)) δ0 V0 ε k1
  refine ⟨c, hc, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2.mono fun ε h y hy1 hy2 hy3 μ v hv hμ => h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · have := hy3 t; rwa [hG, add_sub_cancel_left] at this
  · rwa [smJ_shift (d.meq ixV δ0 V0, V0) (hG ε) Vh (2 * Ω) y fun t => hd _]

/-- Matching control with a `k_dc` change, parametric instability: `|λ₁| < |g_V/2|` makes the
forced orbit of the system with gain `k_dc + εk₁` Floquet unstable for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem orbit_kdc_unstable {ixV : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV Kδδ KδV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (d.jacobian K)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP r *
        ParametricResonance.ForcedOrbit.critQ u)).map (algebraMap ℝ ℂ)) < 1)
    (Vh k1 : ℝ)
    (hg : ‖-((k1 / d.τ : ℝ) : ℂ) * (u 3 * r 2)‖ ^ 2 < ‖d.mpumpV u r K Kδδ KδV KV Ω Vh / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y ((d.kdcShift ε k1).mfield ixV (d.G + ixV (δ0, V0))
          (d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y ((d.kdcShift ε k1).mfield ixV (d.G + ixV (δ0, V0))
          (d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t)))) t) →
        Periodic.FloquetUnstable (fun t => matX ((d.kdcShift ε k1).mfield ixV (d.G + ixV (δ0, V0)))
          (d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))))
          (2 * Real.pi / (2 * Ω)) := by
  have hd : ∀ q, DifferentiableAt ℝ (d.mfield ixV (d.G + ixV (δ0, V0))) q :=
    (d.contDiff_mfield hP _).differentiable (by norm_num)
  obtain ⟨c, hc, h1, h2⟩ := d.orbit_matching_unstable_spec hP hΩ hωb hωf hC hτ hK hKV hKδδ hKδV
    hD2 hr hu hur hsr Vh (kdcMat d.τ k1) (by rw [shift_kdc]; exact hg)
  have hG := fun ε => d.mfield_kdc ixV (d.G + ixV (δ0, V0)) δ0 V0 ε k1
  refine ⟨c, hc, h1.mono fun ε ⟨y, hy1, hy2, hy3⟩ => ⟨y, hy1, hy2, fun t => ?_⟩,
    h2.mono fun ε h y hy1 hy2 hy3 => ?_⟩
  · rw [hG, add_sub_cancel_left]; exact hy3 t
  · rw [← smJ_shift (d.meq ixV δ0 V0, V0) (hG ε) Vh (2 * Ω) y fun t => hd _]
    exact h y hy1 hy2 fun t => by have := hy3 t; rwa [hG, add_sub_cancel_left] at this

/-- Matching control with a saturated DC current `sat_M ∘ i_x` (a static DC-side current limit),
end-to-end without a stable basis among the hypotheses: with the limit inactive at the operating
point (`|i_x(δ₀, V₀)| < M`), every conclusion of `orbit_matching_stable_spec` holds for the
limited system. -/
@[tmio M, powerlib_domain] theorem orbit_matching_limited_stable {ixV : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV Kδδ KδV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (d.jacobian K)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP r *
        ParametricResonance.ForcedOrbit.critQ u)).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖d.mpumpV u r K Kδδ KδV KV Ω Vh / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2)
    {M : ℝ} (hM : |ixV (δ0, V0)| < M) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)))
            (d.meq ixV δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨c, hc, h1, h2⟩ := d.orbit_matching_stable_spec hP hΩ hωb hωf hC hτ hK hKV hKδδ hKδV
    hD2 hr hu hur hsr Vh A0' hs hg
  obtain ⟨r, hr, hsat⟩ := exists_ball_sat_eq (q0 := (d.meq ixV δ0 V0, V0)) 0
    hP.continuous.continuousAt (by simpa [meq] using hM)
  have hGF : ∀ q, ‖q - (d.meq ixV δ0 V0, V0)‖ < r →
      d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)) q = d.mfield ixV (d.G + ixV (δ0, V0)) q :=
    fun q hq => by simp only [mfield, hsat q hq]
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, ‖y t‖ ≤ c * ε) → ∀ t,
      ‖(d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) -
        (d.meq ixV δ0 V0, V0)‖ < r :=
    (eventually_tube (d.meq ixV δ0 V0, V0) hr c Vh).mono fun ε h y hy t =>
      h (y t) _ (hy t) (Real.abs_cos_le_one _)
  refine ⟨c, hc, (h1.and hin).mono fun ε ⟨⟨y, hy1, hy2, hy3⟩, hε⟩ =>
    ⟨y, hy1, hy2, fun t => ?_⟩, (h2.and hin).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 μ v hv hμ =>
      h y hy1 hy2 (fun t => ?_) μ v hv ?_⟩
  · rw [hGF _ (hε y hy2 t)]; exact hy3 t
  · rw [← hGF _ (hε y hy2 t)]; exact hy3 t
  · rwa [smJ_congr_ball hGF Vh (2 * Ω) A0' ε y (hε y hy2)] at hμ

/-- Matching control with a saturated DC current, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_matching_limited_unstable {ixV : ℝ × ℝ → ℝ}
    (hP : ContDiff ℝ 3 ixV)
    {δ0 V0 Ω K KV Kδδ KδV : ℝ} (hΩ : 0 < Ω) (hωb : d.ωb ≠ 0) (hωf : d.ωf ≠ 0) (hC : d.C ≠ 0)
    (hτ : d.τ ≠ 0) (hK : Pd ixV (δ0, V0) = K) (hKV : fderiv ℝ ixV (δ0, V0) (0, 1) = KV)
    (hKδδ : fderiv ℝ (Pd ixV) (δ0, V0) (1, 0) = Kδδ)
    (hKδV : fderiv ℝ (Pd ixV) (δ0, V0) (0, 1) = KδV)
    (hD2 : d.Dm K (((2 * Ω : ℝ) : ℂ) * I) ≠ 0) {r u : Fin 4 → ℂ}
    (hr : (d.jacobian K).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (d.jacobian K).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS (d.jacobian K)
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP r *
        ParametricResonance.ForcedOrbit.critQ u)).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖d.mpumpV u r K Kδδ KδV KV Ω Vh / 2‖ ^ 2)
    {M : ℝ} (hM : |ixV (δ0, V0)| < M) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)) (d.meq ixV δ0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)))
          (d.meq ixV δ0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨c, hc, h1, h2⟩ := d.orbit_matching_unstable_spec hP hΩ hωb hωf hC hτ hK hKV hKδδ hKδV
    hD2 hr hu hur hsr Vh A0' hg
  obtain ⟨r, hr, hsat⟩ := exists_ball_sat_eq (q0 := (d.meq ixV δ0 V0, V0)) 0
    hP.continuous.continuousAt (by simpa [meq] using hM)
  have hGF : ∀ q, ‖q - (d.meq ixV δ0 V0, V0)‖ < r →
      d.mfield (satMap M ixV) (d.G + ixV (δ0, V0)) q = d.mfield ixV (d.G + ixV (δ0, V0)) q :=
    fun q hq => by simp only [mfield, hsat q hq]
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, ‖y t‖ ≤ c * ε) → ∀ t,
      ‖(d.meq ixV δ0 V0 + y t, V0 + ε * (Vh * Real.cos (2 * Ω * t))) -
        (d.meq ixV δ0 V0, V0)‖ < r :=
    (eventually_tube (d.meq ixV δ0 V0, V0) hr c Vh).mono fun ε h y hy t =>
      h (y t) _ (hy t) (Real.abs_cos_le_one _)
  refine ⟨c, hc, (h1.and hin).mono fun ε ⟨⟨y, hy1, hy2, hy3⟩, hε⟩ =>
    ⟨y, hy1, hy2, fun t => ?_⟩, (h2.and hin).mono fun ε ⟨h, hε⟩ y hy1 hy2 hy3 => ?_⟩
  · rw [hGF _ (hε y hy2 t)]; exact hy3 t
  · rw [smJ_congr_ball hGF Vh (2 * Ω) A0' ε y (hε y hy2)]
    exact h y hy1 hy2 fun t => by rw [← hGF _ (hε y hy2 t)]; exact hy3 t

end powerlib.GFM.Matching.MatchingCore
