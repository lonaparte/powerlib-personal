import theorem.ParametricResonance.PortDisturbance

/-! # Grid-synchronized models under the VI and PQV port disturbances

`PortDisturbance` proves the end-to-end Floquet statements for a disturbance of any chart `Φ` with
Thevenin amplitudes `(V̂, θ̂)`. Here the chart is the VI chart of a port `pt` (grid-voltage
magnitude and angle, injected-current magnitude and angle; `Port.linCV_polarAbs`) or the PQV chart
of a port `pq` (grid-voltage magnitude and angle, injected active and reactive power;
`PQVPort.linCV_polarAbs`), with the absolute Thevenin magnitude: `Φ = thPolarAbs e_th V₀`,
`V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff`. The pump, the forced equation and the thresholds are those of the
chart theorems with these amplitudes.

Model boundary.
* As in `PortDisturbance`: a phasor-ized scalar-voltage model `G` or a fixed-frame model `H` with
  slice `G`, operating voltage `u₀` equal to the port Thevenin magnitude `V₀` at the operating
  point `e_th(0) = V₀ > 0`; the PQV source is the injected current at the reference voltage
  (`PQVPort.power_jinj`, `U₀ ≠ 0`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1–§2.2; the port
disturbances are new.

Results.
* `orbit_phasor_vi_stable`, `orbit_phasor_pqv_stable`, `orbit_phasor_vi_unstable`,
  `orbit_phasor_pqv_unstable`, `orbit_phasor_vi_exp_stable`, `orbit_phasor_pqv_exp_stable` —
  phasor-ized models, VI and PQV, any number of states.
* `orbit_phasor_vi_three_stable`, `orbit_phasor_pqv_three_stable`, `orbit_phasor_vi_three_unstable`,
  `orbit_phasor_pqv_three_unstable`, `orbit_phasor_vi_three_exp_stable`,
  `orbit_phasor_pqv_three_exp_stable` — phasor-ized models, three states.
* `orbit_slice_vi_stable`, `orbit_slice_pqv_stable`, `orbit_slice_vi_unstable`,
  `orbit_slice_pqv_unstable`, `orbit_slice_vi_exp_stable`, `orbit_slice_pqv_exp_stable` —
  fixed-frame models.

Corrections.
None: an extension.

Family and connection conclusions.
* The instances are `GFM.VoltageModulationPortVariantsVIPQV` (every GFM model); the GFL converter
  and the GFM synchronizing core have their own VI and PQV corollaries in
  `GFL.Parametric.PortModulation` and `GFM.VoltageModulationPort`.
-/

noncomputable section

namespace powerlib.ParametricResonance
open Complex Filter Topology Matrix

namespace PortDisturbance

open ForcedOrbit
open TwoToOne (base)
open BlockAveraging (expS physLeft physRight)
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A phasor-ized scalar-voltage model under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_phasor_port_stable` with the Thevenin amplitudes `V̂ =
V₀ v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_vi_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ) (pt : Port)
    (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * (pt.effθ w)) • ofv e)
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : X → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (phasor G e) (thPolarAbs pt.eth pt.V0))
              (x0, 0) w ω A0' ε t (y t))
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 :=
  orbit_phasor_port_stable (hG := hG) (hG0 := hG0) (e := e) (hω := hω) (hPQ := hPQ) (hQP := hQP)
      (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A phasor-ized scalar-voltage model under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a
port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end,
stability (all Floquet multipliers inside the unit circle): `orbit_phasor_port_stable` with the
Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_pqv_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ) (pq : PQVPort)
    (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ)
    {ω : ℝ} (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * (pq.effθ w)) • ofv e)
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : X → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (phasor G e) (thPolarAbs pq.eth pq.V0))
              (x0, 0) w ω A0' ε t (y t))
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 :=
  orbit_phasor_port_stable (hG := hG) (hG0 := hG0) (e := e) (hω := hω) (hPQ := hPQ) (hQP := hQP)
      (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs) (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A phasor-ized scalar-voltage model under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_phasor_port_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_vi_unstable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ) (pt : Port)
    (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * (pt.effθ w)) • ofv e)
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ))
        *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)) (x0, 0) w ω A0' ε t (y t))
          (2 * Real.pi / ω) :=
  orbit_phasor_port_unstable (hG := hG) (hG0 := hG0) (e := e) (hω := hω) (hPQ := hPQ) (hQP := hQP)
      (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A phasor-ized scalar-voltage model under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a
port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end,
parametric instability: `orbit_phasor_port_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`,
`θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_pqv_unstable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ) (pq : PQVPort)
    (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ)
    {ω : ℝ} (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * (pq.effθ w)) • ofv e)
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ))
        *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)) (x0, 0) w ω A0' ε t (y t))
          (2 * Real.pi / ω) :=
  orbit_phasor_port_unstable (hG := hG) (hG0 := hG0) (e := e) (hω := hω) (hPQ := hPQ) (hQP := hQP)
      (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A phasor-ized scalar-voltage model under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability: `orbit_phasor_port_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_vi_exp_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ) (pt : Port)
    (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * (pt.effθ w)) • ofv e)
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
          ((x0, (0 : Fin 4 → ℝ)).1 + y t,
        (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
            ((x0, (0 : Fin 4 → ℝ)).1 + a,
          (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_phasor_port_exp_stable (hG := hG) (hG0 := hG0) (e := e) (hω := hω) (hPQ := hPQ)
      (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A phasor-ized scalar-voltage model under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a
port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability: `orbit_phasor_port_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_pqv_exp_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ} {u0 : ℝ}
    (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0) (e : X → ℝ) (pq : PQVPort)
    (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ)
    {ω : ℝ} (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) - (((ω : ℂ) * I) * (pq.effθ w)) • ofv e)
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
          ((x0, (0 : Fin 4 → ℝ)).1 + y t,
        (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
            ((x0, (0 : Fin 4 → ℝ)).1 + a,
          (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_phasor_port_exp_stable (hG := hG) (hG0 := hG0) (e := e) (hω := hω) (hPQ := hPQ)
      (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A phasor-ized scalar-voltage model under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, stability, three states:
`orbit_phasor_port_three_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_vi_three_stable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 3 G (x0, u0))
    (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ) (pt : Port) (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {Ω : ℝ} (hΩ : 0 < Ω) {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ}
    {r3 u3 : Fin 3 → ℝ} (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
        (pt.V0 * pt.effV w) • ofv (fderiv ℝ G (x0, u0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (phasor G e) (thPolarAbs pt.eth pt.V0))
              (x0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_phasor_port_three_stable (hG := hG) (hG0 := hG0) (e := e) (hΩ := hΩ) (hl3 := hl3)
      (hr := hr) (hu := hu) (hur := hur) (hr3 := hr3) (hu3 := hu3) (hur3 := hur3) (hz := hz)
      (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A phasor-ized scalar-voltage model under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a
port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end,
stability, three states: `orbit_phasor_port_three_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_pqv_three_stable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 3 G (x0, u0))
    (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ) (pq : PQVPort) (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0)
    (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) {Ω : ℝ} (hΩ : 0 < Ω) {l3 : ℝ} (hl3 : l3 < 0)
    {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
        (pq.V0 * pq.effV w) • ofv (fderiv ℝ G (x0, u0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (a : Fin 3 → ℂ), a ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam (phasor G e) (thPolarAbs pq.eth pq.V0))
              (x0, 0) w (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ a = μ • a → ‖μ‖ < 1 :=
  orbit_phasor_port_three_stable (hG := hG) (hG0 := hG0) (e := e) (hΩ := hΩ) (hl3 := hl3)
      (hr := hr) (hu := hu) (hur := hur) (hr3 := hr3) (hu3 := hu3) (hur3 := hur3) (hz := hz)
      (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A phasor-ized scalar-voltage model under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability,
three states: `orbit_phasor_port_three_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂
= θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_vi_three_unstable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 3 G (x0, u0))
    (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ) (pt : Port) (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {Ω : ℝ} (hΩ : 0 < Ω) {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ}
    {r3 u3 : Fin 3 → ℝ} (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
        (pt.V0 * pt.effV w) • ofv (fderiv ℝ G (x0, u0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ
        ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ))
        *ᵥ star r) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)) (x0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_phasor_port_three_unstable (hG := hG) (hG0 := hG0) (e := e) (hΩ := hΩ) (hl3 := hl3)
      (hr := hr) (hu := hu) (hur := hur) (hr3 := hr3) (hu3 := hu3) (hur3 := hur3) (hz := hz)
      (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A phasor-ized scalar-voltage model under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a
port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end,
parametric instability, three states: `orbit_phasor_port_three_unstable` with the Thevenin
amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_pqv_three_unstable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 3 G (x0, u0))
    (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ) (pq : PQVPort) (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0)
    (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) {Ω : ℝ} (hΩ : 0 < Ω) {l3 : ℝ} (hl3 : l3 < 0)
    {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
        (pq.V0 * pq.effV w) • ofv (fderiv ℝ G (x0, u0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ
        ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ))
        *ᵥ star r) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
              ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable
          (fun t => smJV (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)) (x0, 0) w (2 * Ω) A0' ε t
              (y t))
          (2 * Real.pi / (2 * Ω)) :=
  orbit_phasor_port_three_unstable (hG := hG) (hG0 := hG0) (e := e) (hΩ := hΩ) (hl3 := hl3)
      (hr := hr) (hu := hu) (hur := hur) (hr3 := hr3) (hu3 := hu3) (hur3 := hur3) (hz := hz)
      (A0' := A0') (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A phasor-ized scalar-voltage model under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port
`pt` (grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability, three states: `orbit_phasor_port_three_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_vi_three_exp_stable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 3 G (x0, u0))
    (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ) (pt : Port) (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0)
    (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {Ω : ℝ} (hΩ : 0 < Ω) {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ}
    {r3 u3 : Fin 3 → ℝ} (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
        (pt.V0 * pt.effV w) • ofv (fderiv ℝ G (x0, u0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * (pt.effθ w)) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
          ((x0, (0 : Fin 4 → ℝ)).1 + y t,
        (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (phasor G e) (thPolarAbs pt.eth pt.V0)
            ((x0, (0 : Fin 4 → ℝ)).1 + a,
          (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_phasor_port_three_exp_stable (hG := hG) (hG0 := hG0) (e := e) (hΩ := hΩ) (hl3 := hl3)
      (hr := hr) (hu := hu) (hur := hur) (hr3 := hr3) (hu3 := hu3) (hur3 := hur3) (hz := hz)
      (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A phasor-ized scalar-voltage model under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a
port `pq` (grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability, three states: `orbit_phasor_port_three_exp_stable` with the Thevenin
amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_phasor_pqv_three_exp_stable
    {G : (Fin 3 → ℝ) × ℝ → Fin 3 → ℝ} {x0 : Fin 3 → ℝ} {u0 : ℝ} (hG : ContDiffAt ℝ 3 G (x0, u0))
    (hG0 : G (x0, u0) = 0) (e : Fin 3 → ℝ) (pq : PQVPort) (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0)
    (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0) (w : Fin 4 → ℂ) {Ω : ℝ} (hΩ : 0 < Ω) {l3 : ℝ} (hl3 : l3 < 0)
    {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX G (x0, u0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX G (x0, u0) *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX G (x0, u0) = l3 • u3)
    (hur3 : u3 ⬝ᵥ r3 = 1) {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z =
        (pq.V0 * pq.effV w) • ofv (fderiv ℝ G (x0, u0) (0, 1)) -
        ((((2 * Ω : ℝ) : ℂ) * I) * (pq.effθ w)) • ofv e)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ)) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
          ((x0, (0 : Fin 4 → ℝ)).1 + y t,
        (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t a => reparam (phasor G e) (thPolarAbs pq.eth pq.V0)
            ((x0, (0 : Fin 4 → ℝ)).1 + a,
          (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_phasor_port_three_exp_stable (hG := hG) (hG0 := hG0) (e := e) (hΩ := hΩ) (hl3 := hl3)
      (hr := hr) (hu := hu) (hur := hur) (hr3 := hr3) (hu3 := hu3) (hur3 := hur3) (hz := hz)
      (A0' := A0') (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN
      hV) (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A model in a fixed frame under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, stability (all Floquet
multipliers inside the unit circle): `orbit_slice_port_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_slice_vi_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    (pt : Port) (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {ω : ℝ}
    (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) + (pt.effθ w) • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ) + (pt.effθ w) • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ
        star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^
        2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam H (thPolarAbs pt.eth pt.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam H (thPolarAbs pt.eth pt.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : X → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam H (thPolarAbs pt.eth pt.V0)) (x0, 0) w ω A0'
              ε t (y t))
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 :=
  orbit_slice_port_stable (hHG := hHG) (hH := hH) (hG := hG) (hG0 := hG0) (hω := hω) (hPQ := hPQ)
      (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A model in a fixed frame under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, stability (all
Floquet multipliers inside the unit circle): `orbit_slice_port_stable` with the Thevenin amplitudes
`V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_slice_pqv_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    (pq : PQVPort) (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {ω : ℝ} (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) + (pq.effθ w) • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ) + (pq.effθ w) • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ
        star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^
        2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam H (thPolarAbs pq.eth pq.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam H (thPolarAbs pq.eth pq.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (u : X → ℂ), u ≠ 0 →
          (Periodic.monodromy (fun t => smJV (reparam H (thPolarAbs pq.eth pq.V0)) (x0, 0) w ω A0'
              ε t (y t))
            (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ u = μ • u → ‖μ‖ < 1 :=
  orbit_slice_port_stable (hHG := hHG) (hH := hH) (hG := hG) (hG0 := hG0) (hω := hω) (hPQ := hPQ)
      (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hs := hs)
      (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A model in a fixed frame under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, parametric instability:
`orbit_slice_port_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ = θ̂_eff` of
`Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_slice_vi_unstable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    (pt : Port) (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {ω : ℝ}
    (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) + (pt.effθ w) • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) +
        (pt.effθ w) • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) /
        2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam H (thPolarAbs pt.eth pt.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam H (thPolarAbs pt.eth pt.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam H (thPolarAbs pt.eth pt.V0)) (x0, 0) w ω
            A0' ε t (y t))
          (2 * Real.pi / ω) :=
  orbit_slice_port_unstable (hHG := hHG) (hH := hH) (hG := hG) (hG0 := hG0) (hω := hω) (hPQ := hPQ)
      (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A model in a fixed frame under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, parametric
instability: `orbit_slice_port_unstable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_slice_pqv_unstable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    (pq : PQVPort) (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {ω : ℝ} (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) + (pq.effθ w) • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 < ‖physLeft Q ⬝ᵥ
        ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map (algebraMap ℝ ℂ) +
        (pq.effθ w) • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ star (physRight P)) /
        2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (reparam H (thPolarAbs pq.eth pq.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (reparam H (thPolarAbs pq.eth pq.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
            (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV (reparam H (thPolarAbs pq.eth pq.V0)) (x0, 0) w ω
            A0' ε t (y t))
          (2 * Real.pi / ω) :=
  orbit_slice_port_unstable (hHG := hHG) (hH := hH) (hG := hG) (hG0 := hG0) (hω := hω) (hPQ := hPQ)
      (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0') (hg := hg)
      (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

/-- A model in a fixed frame under the VI port disturbance `ŵ = (ê, θ̂, ι̂, φ̂)` of a port `pt`
(grid-voltage and injected-current magnitude and angle), end-to-end, local exponential orbital
stability: `orbit_slice_port_exp_stable` with the Thevenin amplitudes `V̂ = V₀ v̂_eff`, `θ̂ =
θ̂_eff` of `Port.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_slice_vi_exp_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    (pt : Port) (hpV : pt.V0 = u0) (hN : pt.eth 0 = pt.V0) (hV : 0 < pt.V0) (w : Fin 4 → ℂ) {ω : ℝ}
    (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pt.V0 * pt.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) + (pt.effθ w) • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pt.V0 * pt.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ) + (pt.effθ w) • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ
        star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^
        2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam H (thPolarAbs pt.eth pt.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
        (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t a => reparam H (thPolarAbs pt.eth pt.V0)
            ((x0, (0 : Fin 4 → ℝ)).1 + a,
          (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_slice_port_exp_stable (hHG := hHG) (hH := hH) (hG := hG) (hG0 := hG0) (hω := hω)
      (hPQ := hPQ) (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0')
      (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pt.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pt.linCV_polarAbs hN hV w)

/-- A model in a fixed frame under the PQV port disturbance `ŵ = (ê, θ̂, P̂, Q̂)` of a port `pq`
(grid-voltage magnitude and angle, injected active and reactive power), end-to-end, local
exponential orbital stability: `orbit_slice_port_exp_stable` with the Thevenin amplitudes `V̂ = V₀
v̂_eff`, `θ̂ = θ̂_eff` of `PQVPort.linCV_polarAbs`. -/
@[tmio M, powerlib_domain] theorem orbit_slice_pqv_exp_stable
    {Y : Type*} [Fintype Y] [DecidableEq Y] {H : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} (hHG : ∀ x V, H (x, ![V, 0]) = G (x, V)) {x0 : X → ℝ} {u0 : ℝ}
    (hH : ContDiffAt ℝ 3 H (x0, ![u0, 0])) (hG : ContDiffAt ℝ 3 G (x0, u0)) (hG0 : G (x0, u0) = 0)
    (pq : PQVPort) (hpV : pq.V0 = u0) (hN : pq.eth 0 = pq.V0) (hV : 0 < pq.V0) (hU : pq.U0 ≠ 0)
    (w : Fin 4 → ℂ) {ω : ℝ} (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * matX G (x0, u0) * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX G (x0, u0)).map (algebraMap ℝ ℂ) *ᵥ z = (pq.V0 * pq.effV w) •
        ofv (fderiv ℝ G (x0, u0) (0, 1)) + (pq.effθ w) • ofv (fderiv ℝ H (x0, ![u0, 0]) (0, uAng)))
    (A0' : Matrix X X ℝ) (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ ((DxC (smDx G (x0, u0)) z + (pq.V0 * pq.effV w) • (smM1 G (x0, u0)).map
        (algebraMap ℝ ℂ) + (pq.effθ w) • (smMwV H (x0, ![u0, 0]) uAng).map (algebraMap ℝ ℂ)) *ᵥ
        star (physRight P)) / 2‖ ^ 2 < ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^
        2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (reparam H (thPolarAbs pq.eth pq.V0) ((x0, (0 : Fin 4 → ℝ)).1 + y t,
        (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t a => reparam H (thPolarAbs pq.eth pq.V0)
            ((x0, (0 : Fin 4 → ℝ)).1 + a,
          (x0, (0 : Fin 4 → ℝ)).2 + ε • harm w ω t) + ε • (A0' *ᵥ a)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ :=
  orbit_slice_port_exp_stable (hHG := hHG) (hH := hH) (hG := hG) (hG0 := hG0) (hω := hω)
      (hPQ := hPQ) (hQP := hQP) (As := As) (hA0 := hA0) (hsr := hsr) (hz := hz) (A0' := A0')
      (hs := hs) (hg := hg) (hΦ := contDiffAt_thPolarAbs pq.contDiff_eth.contDiffAt hN hV)
      (hΦ0 := by rw [thPolarAbs_zero hN hV.ne', hpV]) (hvθ := pq.linCV_polarAbs hN hV hU w)

end PortDisturbance

end powerlib.ParametricResonance
