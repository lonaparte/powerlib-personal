import theorem.GridTiedConverter.GFM.DroopPump

/-! # The droop core with the first-order network sideband: the effective ratio (21)

The three-state droop core whose measured power carries the first-order network terms
`p_M = P(Ψ)(1 − θ̇/ω_b) − K_d(Ψ) Ψ̇` (port power with the grid-frequency factor, and the
`−(x_up/(2ω_b)) d|i|²/dt` term of a measurement point behind the reactance `x_up`): its Jacobian
with the shortcut element `(p_m, p_f)`, the modulation `A₁` along the forced response of the drive
`θ = Re e^{jωt}`, the eigentriple, and the exact combination of the stiffness and shortcut
contributions into one effective ratio on the stiffness weight.

Model boundary.
* State `x = (δ, p_m, p_f) : Dynamics.State 3` (converter angle, measured power after the
  measurement low-pass `ω_m`, filtered power after the droop low-pass `ω_1`); input
  `u = (θ, θ̇)` (grid angle and grid frequency deviation, treated as independent inputs, driven
  as `θ̂ = 1`, `θ̇̂ = jω`); continuous time:
  `δ̇ = m_p (P* − p_f)`, `ṗ_m = ω_m (p_M − p_m)`, `ṗ_f = ω_1 (p_m − p_f)` with
  `p_M = P(Ψ)(1 − θ̇/ω_b) − K_d(Ψ)(m_p(P* − p_f) − θ̇)`, `Ψ = δ − θ` (`power`, `field`), where
  `Ψ̇ = m_p(P* − p_f) − θ̇` is substituted from the angle law.
* `P` and `K_d` are arbitrary static maps of the relative angle (`K = P'(Ψ₀)`, `P₂ = P''(Ψ₀)`,
  `K_d(Ψ₀)`, `κ_d = K_d'(Ψ₀)`). For a lossless series link, `P = (EV/X) sin` and
  `K_d = x_up E V sin/(ω_b X²)` are the first-order network terms of
  `Grid.MeasurementPoint` (`portPower_firstOrder`, `pointPower_eq`, `normSq_quasiStatic`,
  `hasDerivAt_shortcut`); the network itself (currents as states), second-order terms in
  `d/dt ÷ ω_b`, resistance in the dynamic terms, Q–V droop, inner loops, limits, PLL, delay and
  PWM are excluded.
* Equilibrium: `θ̇ = 0`, `p_f = p_m = P*`, `P(Ψ₀) = P₀`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §5.4 ((20) `p_conv = p₀(Ψ)(1 − θ̇_g/ω_b)`,
`p_M = p_conv − (x_up/(2ω_b)) d|i|²/dt`, (21)
`ρ^eff = S_m[tan(δ₀ + φ_R) + j(x_up/(2X))μ_p] − jμ_p + O(μ_p², μ_p R/X)`), Appendix B (the
stiffness element `−j(x_up/X)μ_p z_Ψ`, the shortcut element `(p_m, p_f) = ω_m m_p K_d` and its
folding `−(K_d'/K)λ̄ z_Ψ ≈ +j(x_up/X)(μ_p/2) z_Ψ`), §4.4 (the lag `p ≈ K_s δ − K_d δ̇`).

Results.
* `hasFDerivAt_field`, `hasDerivAt_field_angle`, `hasDerivAt_field_rate` — the Jacobian
  (`jacobian (stiff K κ u x) (K_d(Ψ))`, with the shortcut entry `(p_m, p_f) = ω_m m_p K_d`) and the
  input vectors `∂f/∂θ`, `∂f/∂θ̇ = (0, ω_m(K_d − P/ω_b), 0)`.
* `jacAt_const`, `modulation_eq` — only `(p_m, δ)` and `(p_m, p_f)` are modulated (Lemma 1), with
  `(A₁)_{p_m δ} = ω_m[P₂(z_δ − 1) − jωK/ω_b + κ_d(m_p z_{p_f} + jω)]`,
  `(A₁)_{p_m p_f} = ω_m m_p κ_d (z_δ − 1)` (`modMatrix`).
* `charPoly` — `D(s) = s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m (K − K_d s)`: the lag `K_d` enters as
  `d₁ ↦ d₁ − d₀ τ`, `τ = K_d/K` (`ThirdOrderCore.lagged_roots_re_neg_iff`).
* `forced_eq`, `forced_angle_row` — the forced response
  `z_δ = m_p ω₁ ω_m (K + jω(P₀/ω_b − K_d))/D(jω)`.
* `right_eig`, `left_eig`, `left_right`, `weight_eq` (`w_{p_m δ} = −m_p ω₁ ω_m K/D'(λ)`),
  `contribution_eq_zero`.
* `pump_eq` — exactly `g = ρ_eff · w_{p_m δ}` with
  `ρ_eff = (P₂/K)(z_δ − 1) − jω/ω_b − (κ_d/K)(jω + λ̄)(z_δ − 1)` (`effRatio`), i.e.
  `ρ_eff = S[−P₂/K + (κ_d/K)(jω + λ̄)] − jω/ω_b`, `S = 1 − z_δ` (`effRatio_eq`).
* `effRatio_lossless` — lossless link, `λ = −σ + jΩ`, `ω = 2Ω`:
  `ρ_eff = S[tan Ψ₀ + (x_up/X)(jΩ − σ)/ω_b] − 2jΩ/ω_b`.
* `effRatio_port`, `charPolyEval_port` — port measurement (`K_d = 0`) with `−P₂/K = P₀/K = t`:
  `ρ_eff = t S₀ − j(ω/ω_b)(1 + t²(1 − S₀))`, `S₀` the quasi-static loop sensitivity of the
  droop core (`DroopCore.one_sub_forced_zero`, Table 6).
* `hasDerivAt_shortcut` — `K_d = x_up E V sin Ψ/(ω_b X²)` from `|i₀|²`.

Corrections.
* Within the first-order network model, (21) is exact up to one term: the folding factor of the
  shortcut element is `(jω + λ̄)/ω_b = (jΩ − σ)/ω_b`, not `jμ_p/2`; the difference is
  `−S (x_up/X) σ/ω_b` (`effRatio_lossless`), of relative order `σ_m/Ω_m`.
* `S` in (21) is the forced response of the sideband model, not the quasi-static `S_m` of
  Table 6: the grid-frequency factor `−P₀θ̇/ω_b` of the port power also drives the loop. With the
  quasi-static `S₀` the port ratio is `t S₀ − jμ_p(1 + t²(1 − S₀))` (`effRatio_port`); Appendix B's
  `ρ^eff = S_m tan δ₀ − jμ_p` with Table 6's `S_m` omits `−jμ_p t²(1 − S₀) ≈ +jμ_p tan²δ₀/3`.
* The full-order form (22), `(tan(δ₀ + φ_R)S_m − jμ_p)/(1 − μ_p²)`, is outside this first-order
  model; it is not formalized (see `Grid.MeasurementPoint.tone_solves` for the sideband
  reactances `X(1 ± μ_p)`).

Family and connection conclusions.
None: static evidence on the droop core with the first-order sideband (Jacobian, modulation,
forced response, eigentriple, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
open powerlib.Dynamics (State mk3 state3_ext toEuclideanCLM_apply3)
open Complex ComplexConjugate Matrix

/-- Parameters of the droop core with the first-order network sideband in the measured power. -/
structure DroopSideband where
  mp : ℝ
  ω1 : ℝ
  ωm : ℝ
  Pref : ℝ
  ωb : ℝ
  P : ℝ → ℝ
  Kd : ℝ → ℝ

namespace DroopSideband

variable (d : DroopSideband)

/-- Measured power `p_M = P(Ψ)(1 − θ̇/ω_b) − K_d(Ψ) Ψ̇` with `Ψ = δ − θ`,
`Ψ̇ = m_p(P* − p_f) − θ̇`. -/
def power (u : ℝ × ℝ) (x : State 3) : ℝ :=
  d.P (x 0 - u.1) * (1 - u.2 / d.ωb) - d.Kd (x 0 - u.1) * (d.mp * (d.Pref - x 2) - u.2)

/-- The droop core field with the input `u = (θ, θ̇)`. -/
def field (u : ℝ × ℝ) (x : State 3) : State 3 :=
  mk3 (d.mp * (d.Pref - x 2)) (d.ωm * (d.power u x - x 1)) (d.ω1 * (x 1 - x 2))

/-- The Jacobian with stiffness entry `a` and shortcut coefficient `c`. -/
def jacobian (a c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, -d.mp; d.ωm * a, -d.ωm, d.ωm * d.mp * c; 0, d.ω1, -d.ω1]

/-- The stiffness entry `P'(Ψ)(1 − θ̇/ω_b) − K_d'(Ψ) Ψ̇`. -/
def stiff (K κ : ℝ) (u : ℝ × ℝ) (x : State 3) : ℝ :=
  K * (1 - u.2 / d.ωb) - κ * (d.mp * (d.Pref - x 2) - u.2)

@[tmio M, powerlib_domain] theorem hasFDerivAt_field {u : ℝ × ℝ} {K κ : ℝ} {x : State 3}
    (hP : HasDerivAt d.P K (x 0 - u.1)) (hK : HasDerivAt d.Kd κ (x 0 - u.1)) :
    HasFDerivAt (d.field u)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
        (d.jacobian (d.stiff K κ u x) (d.Kd (x 0 - u.1)))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  fin_cases i
  · have h := ((hasFDerivAt_const d.Pref x).sub h2).const_mul d.mp
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
  · have hs := hP.comp_hasFDerivAt x (h0.sub_const u.1)
    have hk := hK.comp_hasFDerivAt x (h0.sub_const u.1)
    have hv : HasFDerivAt (fun y : State 3 => d.mp * (d.Pref - y 2) - u.2)
        (d.mp • ((0 : State 3 →L[ℝ] ℝ) - (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)))) x :=
      (((hasFDerivAt_const d.Pref x).sub h2).const_mul d.mp).sub_const u.2
    have h := (((hs.mul_const (1 - u.2 / d.ωb)).sub (hk.mul hv)).sub h1).const_mul d.ωm
    convert h using 1
    · funext y; simp [field, power]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, stiff, toEuclideanCLM_apply3]
      ring
  · have h := (h1.sub h2).const_mul d.ω1
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
      ring

/-- `∂f/∂θ = (0, −ω_m a, 0)` with the stiffness entry `a`. -/
def inputAngle (a : ℝ) : Fin 3 → ℝ := ![0, -(d.ωm * a), 0]

/-- `∂f/∂θ̇ = (0, ω_m (K_d(Ψ) − P(Ψ)/ω_b), 0)`. -/
def inputRate (P0 Kd0 : ℝ) : Fin 3 → ℝ := ![0, d.ωm * (Kd0 - P0 / d.ωb), 0]

@[tmio M, powerlib_domain] theorem hasDerivAt_field_angle {u : ℝ × ℝ} {K κ : ℝ} {x : State 3}
    (hP : HasDerivAt d.P K (x 0 - u.1)) (hK : HasDerivAt d.Kd κ (x 0 - u.1)) (i : Fin 3) :
    HasDerivAt (fun θ => d.field (θ, u.2) x i) (d.inputAngle (d.stiff K κ u x) i) u.1 := by
  have h1 : HasDerivAt (fun θ : ℝ => x 0 - θ) (-1) u.1 := by
    simpa using (hasDerivAt_id u.1).const_sub (x 0)
  fin_cases i
  · simpa [field, inputAngle] using hasDerivAt_const u.1 (d.mp * (d.Pref - x 2))
  · have h := ((((hP.comp u.1 h1).mul_const (1 - u.2 / d.ωb)).sub
      ((hK.comp u.1 h1).mul_const (d.mp * (d.Pref - x 2) - u.2))).sub_const (x 1)).const_mul d.ωm
    convert h using 1
    · funext θ; simp [field, power]
    · simp [inputAngle, stiff]; ring
  · simpa [field, inputAngle] using hasDerivAt_const u.1 (d.ω1 * (x 1 - x 2))

@[tmio M, powerlib_domain] theorem hasDerivAt_field_rate (u : ℝ × ℝ) (x : State 3) (i : Fin 3) :
    HasDerivAt (fun θd => d.field (u.1, θd) x i)
      (d.inputRate (d.P (x 0 - u.1)) (d.Kd (x 0 - u.1)) i) u.2 := by
  fin_cases i
  · simpa [field, inputRate] using hasDerivAt_const u.2 (d.mp * (d.Pref - x 2))
  · have hl : HasDerivAt (fun θd : ℝ => d.P (x 0 - u.1) * (1 - θd / d.ωb) -
        d.Kd (x 0 - u.1) * (d.mp * (d.Pref - x 2) - θd))
        (d.P (x 0 - u.1) * (-(1 / d.ωb)) - d.Kd (x 0 - u.1) * (-1)) u.2 := by
      have ha : HasDerivAt (fun θd : ℝ => 1 - θd / d.ωb) (-(1 / d.ωb)) u.2 := by
        simpa using ((hasDerivAt_id u.2).div_const d.ωb).const_sub 1
      have hb : HasDerivAt (fun θd : ℝ => d.mp * (d.Pref - x 2) - θd) (-1) u.2 := by
        simpa using (hasDerivAt_id u.2).const_sub (d.mp * (d.Pref - x 2))
      exact (ha.const_mul _).sub (hb.const_mul _)
    have h := (hl.sub_const (x 1)).const_mul d.ωm
    convert h using 1
    · funext θd; simp [field, power]
    · change d.ωm * (d.Kd (x 0 - u.1) - d.P (x 0 - u.1) / d.ωb) = _
      ring
  · simpa [field, inputRate] using hasDerivAt_const u.2 (d.ω1 * (x 1 - x 2))

/-! ## The modulation `A₁` -/

/-- The Jacobian at the point `(x, u)`. -/
def jacAt (q : State 3 × (ℝ × ℝ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  d.jacobian (d.stiff (deriv d.P (q.1 0 - q.2.1)) (deriv d.Kd (q.1 0 - q.2.1)) q.2 q.1)
    (d.Kd (q.1 0 - q.2.1))

/-- Lemma 1: only the stiffness element `(p_m, δ)` and the shortcut element `(p_m, p_f)` can be
modulated. -/
@[tmio M, powerlib_domain] theorem jacAt_const {i k : Fin 3}
    (h : ¬ ((i = 1 ∧ k = 0) ∨ (i = 1 ∧ k = 2))) :
    ∃ c : ℝ, ∀ q, d.jacAt q i k = c := by
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;> simp [jacAt, jacobian]

/-- The modulation along the forced direction `(z, û)`, `û = (1, jω)`:
`(A₁)_{p_m δ} = ω_m [P₂ (z_δ − 1) − jωK/ω_b + κ_d (m_p z_{p_f} + jω)]`,
`(A₁)_{p_m p_f} = ω_m m_p κ_d (z_δ − 1)`. -/
def modMatrix (P2 K κ ω : ℝ) (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
    (d.ωm : ℂ) * (P2 * (z 0 - 1) - I * (K * ω / d.ωb : ℝ) + κ * (d.mp * z 2 + I * ω)), 0,
      (d.ωm * d.mp * κ : ℝ) * (z 0 - 1);
    0, 0, 0]

@[tmio M, powerlib_domain] theorem modulation_eq {x : State 3} {u : ℝ × ℝ} {P2 Kd2 κ ω : ℝ}
    (hu : u.2 = 0) (hx : x 2 = d.Pref)
    (hP2 : HasDerivAt (deriv d.P) P2 (x 0 - u.1))
    (hK2 : HasDerivAt (deriv d.Kd) Kd2 (x 0 - u.1))
    (hK1 : HasDerivAt d.Kd κ (x 0 - u.1)) (z : Fin 3 → ℂ) :
    ParametricResonance.Element.modulation d.jacAt (x, u)
        (WithLp.toLp 2 (fun i => (z i).re), (1, 0)) (WithLp.toLp 2 (fun i => (z i).im), (0, ω)) =
      d.modMatrix P2 (deriv d.P (x 0 - u.1)) κ ω z := by
  set q : State 3 × (ℝ × ℝ) := (x, u)
  have hΨ := ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).hasFDerivAt.comp q
    (hasFDerivAt_fst (𝕜 := ℝ) (p := q))).sub
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := q.2)).comp q (hasFDerivAt_snd (𝕜 := ℝ) (p := q)))
  have hθd : HasFDerivAt (fun q : State 3 × (ℝ × ℝ) => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (State 3) (ℝ × ℝ))) q :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := q.2)).comp q (hasFDerivAt_snd (𝕜 := ℝ) (p := q))
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).hasFDerivAt.comp q
    (hasFDerivAt_fst (𝕜 := ℝ) (p := q))
  have hP2' := hP2.comp_hasFDerivAt q hΨ
  have hK2' := hK2.comp_hasFDerivAt q hΨ
  have hK1' := hK1.comp_hasFDerivAt q hΨ
  have hfac := (hasFDerivAt_const (1 : ℝ) q).sub (hθd.const_mul (1 / d.ωb))
  have hν := (((hasFDerivAt_const d.Pref q).sub h2).const_mul d.mp).sub hθd
  have h10 := ((hP2'.mul hfac).sub (hK2'.mul hν)).const_mul d.ωm
  have h12 := hK1'.const_mul (d.ωm * d.mp)
  have hKd : deriv d.Kd (x 0 - u.1) = κ := hK1.deriv
  ext i k
  by_cases hik : (i = 1 ∧ k = 0) ∨ (i = 1 ∧ k = 2)
  · rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h10' : HasFDerivAt (fun q : State 3 × (ℝ × ℝ) => d.jacAt q 1 0) _ q :=
        h10.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
          simp [jacAt, jacobian, stiff, -mul_eq_mul_left_iff]; ring)
      simp only [ParametricResonance.Element.modulation, h10'.fderiv, modMatrix]
      simp [q, hu, hx, hKd]
      apply Complex.ext
      · simp [-mul_eq_mul_left_iff]
      · simp [-mul_eq_mul_left_iff]; ring
    · have h12' : HasFDerivAt (fun q : State 3 × (ℝ × ℝ) => d.jacAt q 1 2) _ q :=
        h12.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
          simp [jacAt, jacobian])
      simp only [ParametricResonance.Element.modulation, h12'.fderiv, modMatrix]
      simp
      apply Complex.ext <;> simp [-mul_eq_mul_left_iff] <;> ring
  · obtain ⟨c, hc⟩ := d.jacAt_const hik
    rw [ParametricResonance.Element.modulation_eq_zero_of_const hc]
    fin_cases i <;> fin_cases k <;> simp at hik ⊢ <;> simp [modMatrix]

/-! ## Characteristic polynomial and forced response at the equilibrium -/

/-- `D(s) = s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m (K − K_d s)`. -/
def charPolyEval (K Kd0 : ℝ) (s : ℂ) : ℂ :=
  s * (s + d.ω1) * (s + d.ωm) + ((d.mp * d.ω1 * d.ωm : ℝ) : ℂ) * (K - Kd0 * s)

@[tmio M, powerlib_domain] theorem charPoly (K Kd0 : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (d.jacobian K Kd0) s).det = d.charPolyEval K Kd0 s := by
  simp [Linear.characteristicMatrix, jacobian, charPolyEval, Matrix.det_fin_three]
  ring

/-- The complex input vector of the drive `θ = Re e^{jωt}`: `B_θ + jω B_θ̇`. -/
def inputVec (K Kd0 P0 ω : ℝ) : Fin 3 → ℂ :=
  fun i => (d.inputAngle K i : ℂ) + I * ω * (d.inputRate P0 Kd0 i : ℂ)

/-- The forced response `z⁽¹⁾(jω)`: `z_δ = m_p ω₁ ω_m (K + jω(P₀/ω_b − K_d))/D(jω)`,
`z_{p_f} = −jω z_δ/m_p`, `z_{p_m} = (jω + ω₁) z_{p_f}/ω₁`. -/
def forced (K Kd0 P0 ω : ℝ) : Fin 3 → ℂ :=
  let zδ := ((d.mp * d.ω1 * d.ωm : ℝ) : ℂ) * (K + I * ω * (P0 / d.ωb - Kd0)) /
    d.charPolyEval K Kd0 (ω * I)
  ![zδ, ((ω : ℂ) * I + d.ω1) * (-((ω : ℂ) * I) * zδ / d.mp) / d.ω1, -((ω : ℂ) * I) * zδ / d.mp]

/-- `(jωI − A₀) z⁽¹⁾ = B_θ + jω B_θ̇`. -/
@[tmio M, powerlib_domain] theorem forced_eq {K Kd0 P0 ω : ℝ} (hmp : d.mp ≠ 0) (hω1 : d.ω1 ≠ 0)
    (hD : d.charPolyEval K Kd0 (ω * I) ≠ 0) :
    Linear.characteristicMatrix (d.jacobian K Kd0) ((ω : ℂ) * I) *ᵥ d.forced K Kd0 P0 ω =
      d.inputVec K Kd0 P0 ω := by
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  have hDdef : d.charPolyEval K Kd0 ((ω : ℂ) * I) =
      (ω : ℂ) * I * ((ω : ℂ) * I + d.ω1) * ((ω : ℂ) * I + d.ωm) +
        ((d.mp * d.ω1 * d.ωm : ℝ) : ℂ) * (K - Kd0 * ((ω : ℂ) * I)) := rfl
  funext i
  fin_cases i <;>
    simp [Linear.characteristicMatrix, jacobian, forced, inputVec, inputAngle, inputRate, mulVec,
      dotProduct, Fin.sum_univ_three] <;>
    generalize hDg : d.charPolyEval K Kd0 ((ω : ℂ) * I) = D at hD hDdef ⊢ <;>
    field_simp
  · ring
  · rw [hDdef]
    push_cast
    ring
  · ring

/-- The forced response satisfies the angle row `jω z_δ + m_p z_{p_f} = 0`. -/
@[tmio M, powerlib_domain] theorem forced_angle_row {K Kd0 P0 ω : ℝ} (hmp : d.mp ≠ 0) :
    (ω : ℂ) * I * d.forced K Kd0 P0 ω 0 + d.mp * d.forced K Kd0 P0 ω 2 = 0 := by
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  simp only [forced, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  field_simp
  ring

/-! ## The eigentriple -/

/-- `D'(λ) = (λ + ω₁)(λ + ω_m) + λ(λ + ω_m) + λ(λ + ω₁) − m_p ω₁ ω_m K_d`. -/
def charPolyDeriv (Kd0 : ℝ) (s : ℂ) : ℂ :=
  (s + d.ω1) * (s + d.ωm) + s * (s + d.ωm) + s * (s + d.ω1) - ((d.mp * d.ω1 * d.ωm * Kd0 : ℝ) : ℂ)

/-- Right eigenvector `(1, −λ(λ + ω₁)/(m_p ω₁), −λ/m_p)` (as for the quasi-static core). -/
def right (lam : ℂ) : Fin 3 → ℂ :=
  ![1, -(lam * (lam + d.ω1)) / ((d.mp : ℂ) * d.ω1), -lam / d.mp]

/-- Left eigenvector `c (ω_m K/λ, 1, (λ + ω_m)/ω₁)`, `c = −m_p ω₁/D'(λ)`. -/
def left (K Kd0 : ℝ) (lam : ℂ) : Fin 3 → ℂ :=
  let c := -((d.mp : ℂ) * d.ω1) / d.charPolyDeriv Kd0 lam
  ![c * ((d.ωm * K : ℝ) / lam), c, c * ((lam + d.ωm) / d.ω1)]

@[tmio M, powerlib_domain] theorem right_eig {K Kd0 : ℝ} {lam : ℂ} (hmp : d.mp ≠ 0)
    (hω1 : d.ω1 ≠ 0) (hroot : d.charPolyEval K Kd0 lam = 0) :
    Linear.complexify (d.jacobian K Kd0) *ᵥ d.right lam = lam • d.right lam := by
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp only [charPolyEval] at hroot
  push_cast at hroot
  funext i
  fin_cases i <;>
    simp [Linear.complexify, jacobian, right, mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp
  · linear_combination hroot
  · ring

@[tmio M, powerlib_domain] theorem left_eig {K Kd0 : ℝ} {lam : ℂ} (hω1 : d.ω1 ≠ 0)
    (hlam : lam ≠ 0) (hroot : d.charPolyEval K Kd0 lam = 0) :
    vecMul (d.left K Kd0 lam) (Linear.complexify (d.jacobian K Kd0)) = lam • d.left K Kd0 lam := by
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp only [charPolyEval] at hroot
  push_cast at hroot
  simp only [left]
  generalize -((d.mp : ℂ) * d.ω1) / d.charPolyDeriv Kd0 lam = c
  funext i
  fin_cases i <;>
    simp [Linear.complexify, jacobian, vecMul, dotProduct, Fin.sum_univ_three] <;>
    field_simp
  · ring
  · linear_combination (-c) * hroot

@[tmio M, powerlib_domain] theorem left_right {K Kd0 : ℝ} {lam : ℂ} (hmp : d.mp ≠ 0)
    (hω1 : d.ω1 ≠ 0) (hlam : lam ≠ 0) (hroot : d.charPolyEval K Kd0 lam = 0)
    (hD' : d.charPolyDeriv Kd0 lam ≠ 0) :
    d.left K Kd0 lam ⬝ᵥ d.right lam = 1 := by
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hω1' : (d.ω1 : ℂ) ≠ 0 := by exact_mod_cast hω1
  simp only [charPolyEval] at hroot
  push_cast at hroot
  simp only [left, right, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  field_simp
  simp only [charPolyDeriv]
  push_cast
  linear_combination (-1 : ℂ) * hroot

/-! ## The pump coefficient and the effective ratio -/

/-- The stiffness weight `w_{p_m δ} = −m_p ω₁ ω_m K/D'(λ)`. -/
@[tmio M, powerlib_domain] theorem weight_eq (K Kd0 : ℝ) (lam : ℂ) :
    ParametricResonance.Element.weight (Linear.complexify (d.jacobian K Kd0)) (d.left K Kd0 lam)
        (d.right lam) 1 0 =
      -((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) / d.charPolyDeriv Kd0 lam := by
  simp [ParametricResonance.Element.weight, Linear.complexify, jacobian, left, right]
  ring

/-- Lemma 1: only `Γ_{p_m δ}` and `Γ_{p_m p_f}` can be nonzero. -/
@[tmio M, powerlib_domain] theorem contribution_eq_zero (P2 K κ ω : ℝ) (z u r : Fin 3 → ℂ)
    {i k : Fin 3} (h : ¬ ((i = 1 ∧ k = 0) ∨ (i = 1 ∧ k = 2))) :
    ParametricResonance.Element.contribution (d.modMatrix P2 K κ ω z) u r i k = 0 := by
  fin_cases i <;> fin_cases k <;> simp at h ⊢ <;>
    simp [ParametricResonance.Element.contribution, modMatrix]

/-- The effective ratio `ρ_eff = (P₂/K)(z_δ − 1) − jω/ω_b − (κ_d/K)(jω + λ̄)(z_δ − 1)`. -/
def effRatio (P2 K κ ω : ℝ) (lam zδ : ℂ) : ℂ :=
  (P2 / K : ℝ) * (zδ - 1) - I * (ω / d.ωb : ℝ) - (κ / K : ℝ) * ((ω : ℂ) * I + conj lam) * (zδ - 1)

/-- `g = ρ_eff · w_{p_m δ}`: the stiffness element and its shortcut element `(p_m, p_f)` combine
exactly into one effective ratio on the stiffness weight. Only the angle row of the forced
response (`forced_angle_row`) is used. -/
@[tmio M, powerlib_domain] theorem pump_eq {K Kd0 P2 κ ω : ℝ} (hK : K ≠ 0) (hmp : d.mp ≠ 0)
    (hωm : d.ωm ≠ 0) (z : Fin 3 → ℂ) (hz : (ω : ℂ) * I * z 0 + d.mp * z 2 = 0) (lam : ℂ) :
    ParametricResonance.Element.pump (d.modMatrix P2 K κ ω z) (d.left K Kd0 lam) (d.right lam) =
      d.effRatio P2 K κ ω lam (z 0) *
        (-((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) / d.charPolyDeriv Kd0 lam) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hmp' : (d.mp : ℂ) ≠ 0 := by exact_mod_cast hmp
  have hωm' : (d.ωm : ℂ) ≠ 0 := by exact_mod_cast hωm
  have hz2 : z 2 = -((ω : ℂ) * I * z 0) / d.mp := by
    field_simp; linear_combination hz
  simp [ParametricResonance.Element.pump, modMatrix, left, right, mulVec, dotProduct,
    Fin.sum_univ_three, effRatio, hz2]
  field_simp
  ring

/-- The effective ratio in terms of `S = 1 − z_δ`:
`ρ_eff = S [−P₂/K + (κ_d/K)(jω + λ̄)] − jω/ω_b`. -/
@[tmio M, powerlib_domain] theorem effRatio_eq (P2 K κ ω : ℝ) (lam zδ : ℂ) :
    d.effRatio P2 K κ ω lam zδ =
      (1 - zδ) * (((-(P2 / K) : ℝ) : ℂ) + (κ / K : ℝ) * ((ω : ℂ) * I + conj lam)) -
        I * (ω / d.ωb : ℝ) := by
  simp only [effRatio]
  push_cast
  ring

/-- Lossless link measured behind the reactance `x_up` (`P = K₀ sin`, `K_d = (x_up/(ω_b X)) K₀ sin`,
so `−P₂/K = tan Ψ₀` and `κ_d/K = x_up/(ω_b X)`), at a mode `λ = −σ + jΩ` and the 2:1 drive
`ω = 2Ω`: `ρ_eff = S [tan Ψ₀ + (x_up/X)(jΩ − σ)/ω_b] − 2jΩ/ω_b`. With `μ_p = 2Ω/ω_b` this is (21)
plus the term `−S (x_up/X) σ/ω_b`. -/
@[tmio M, powerlib_domain] theorem effRatio_lossless {P2 K κ xup X Ψ0 σ Ω : ℝ} (zδ : ℂ)
    (hP : -(P2 / K) = Real.tan Ψ0) (hκ : κ / K = xup / (d.ωb * X)) :
    d.effRatio P2 K κ (2 * Ω) ((-σ : ℝ) + (Ω : ℂ) * I) zδ =
      (1 - zδ) * ((Real.tan Ψ0 : ℂ) + (xup / X : ℝ) * (((Ω : ℂ) * I - σ) / d.ωb)) -
        I * (2 * Ω / d.ωb : ℝ) := by
  rw [effRatio_eq, hP, hκ]
  simp only [map_add, map_mul, conj_ofReal, conj_I]
  push_cast
  ring

/-- With port measurement (`K_d = 0`) the quasi-static characteristic polynomial is that of the
droop core. -/
@[tmio M, powerlib_domain] theorem charPolyEval_port (K : ℝ) (s : ℂ) :
    d.charPolyEval K 0 s = (DroopCore.mk d.mp d.ω1 d.ωm d.Pref d.P).charPolyEval K s := by
  simp [charPolyEval, DroopCore.charPolyEval]

/-- Port measurement (`K_d = 0`), lossless curve (`−P₂/K = P₀/K = t = tan Ψ₀`): with the
quasi-static loop sensitivity `S₀ = 1 − m_p ω₁ ω_m K/D₀(jω)` (Table 6), the exact effective ratio
along the forced response of the sideband model is
`ρ_eff = t S₀ − j(ω/ω_b)(1 + t²(1 − S₀))`: the grid-frequency term `−P₀ θ̇/ω_b` of the measured
power also drives the forced response. -/
@[tmio M, powerlib_domain] theorem effRatio_port {P2 K P0 ω t : ℝ} (hK : K ≠ 0)
    (hD : d.charPolyEval K 0 ((ω : ℂ) * I) ≠ 0) (hP2 : -(P2 / K) = t) (hP0 : P0 / K = t)
    (lam : ℂ) :
    d.effRatio P2 K 0 ω lam (d.forced K 0 P0 ω 0) =
      (t : ℂ) * (1 - ((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) / d.charPolyEval K 0 ((ω : ℂ) * I)) -
        I * (ω / d.ωb : ℝ) *
          (1 + (t : ℂ) ^ 2 * (((d.mp * d.ω1 * d.ωm * K : ℝ) : ℂ) /
            d.charPolyEval K 0 ((ω : ℂ) * I))) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have hP2' : (P2 : ℂ) = -t * K := by
    have : P2 = -t * K := by field_simp at hP2; linarith
    exact_mod_cast this
  have hP0' : (P0 : ℂ) = t * K := by
    have : P0 = t * K := by field_simp at hP0; linarith
    exact_mod_cast this
  simp only [effRatio, forced, Matrix.cons_val_zero]
  generalize d.charPolyEval K 0 ((ω : ℂ) * I) = D at hD ⊢
  push_cast
  rw [hP2', hP0']
  field_simp
  ring

/-- The shortcut coefficient of a lossless link: `(x_up/(2ω_b)) d|i₀|²/dΨ = x_up E V sin Ψ/(ω_b X²)`
with `|i₀|² = (E² + V² − 2EV cos Ψ)/X²` (`Grid.MeasurementPoint.normSq_quasiStatic`), so
`K_d(Ψ) = x_up E V sin Ψ/(ω_b X²)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_shortcut (E V X xup ωb Ψ : ℝ) :
    HasDerivAt (fun Ψ => xup / (2 * ωb) * ((E ^ 2 + V ^ 2 - 2 * E * V * Real.cos Ψ) / X ^ 2))
      (xup * E * V * Real.sin Ψ / (ωb * X ^ 2)) Ψ := by
  have h := (((Real.hasDerivAt_cos Ψ).const_mul (2 * E * V)).const_sub (E ^ 2 + V ^ 2)).div_const
    (X ^ 2) |>.const_mul (xup / (2 * ωb))
  convert h using 1
  rcases eq_or_ne ωb 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne X 0 with h1 | h1
  · simp [h1]
  field_simp

end DroopSideband
end powerlib.GFM
