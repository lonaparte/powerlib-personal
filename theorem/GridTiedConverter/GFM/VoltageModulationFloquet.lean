import theorem.GridTiedConverter.GFM.VoltageModulationQV
import theorem.ParametricResonance.BlockAveragingDetuned

/-! # Floquet stability of the voltage-modulated synchronizing core

Composition of the voltage pump with the rigorous averaging theorem. For the synchronizing core
`VoltageModulation.Core` (any power map `P(δ, V)`: constant EMF, losses, Q–V droop) at its Hopf
point, the real modal coordinates are built from the eigenvectors (`hopf_eigendata`,
`BlockAveraging.modal_three`), and the complete three-state variational system
`A₀c + ε(A₀' + Re{A₁ e^{2jΩt}})`, with `A₁` the modulation along the voltage-forced response,
is Floquet stable or unstable according to `|g_V/2| ≶ |λ₁|`, `λ₁ = u A₀' r`, with the closed-form
voltage pump `g_V` of `pump_voltage_hopf`.

Model boundary.
* `VoltageModulation.Core` at the Hopf point `a ω_c = Ω²`, `d₀ = d₂Ω²` (`A0r`): pair `±jΩ`, real
  pole `−d₂ < 0`. The family `A₀(ε) = A₀c + ε A₀'` (any real `A₀'`: damping and detuning away from
  the Hopf point) and the grid voltage `V₀ + ε Re{V̂ e^{2jΩt}}`; the variational matrix is taken
  to first order in `ε` (`BlockAveraging.physJ`).
* The forced response is that of `A₀c` at `2jΩ`; the existence of the forced periodic orbit and
  its `O(ε²)` terms are not covered.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (first-order averaging, `ε_crit = 4(σ_m/Ω_m)/ĝ_m`), §3
(VSG core); the voltage excitation is new.

Results.
* `A0r`, `A0r_map` — the real state matrix; `charP_factor` — at the Hopf point
  `D(s) = (s + d₂)(s² + Ω²)`.
* `r3`, `u3`, `cD3`, `r3_cast`, `u3_cast` — the real eigenvectors of the pole `−d₂`;
  `real_right_of_cast`, `real_left_of_cast`.
* `hopf_eigendata` — `A r = jΩ r`, `u A = jΩ u`, `u r = 1`, `A r₃ = −d₂ r₃`, `u₃ A = −d₂ u₃`,
  `u₃ r₃ = 1` with `r = right(jΩ)`, `u = left(jΩ)`.
* `gV` — `g_V = (jΩ/2)(V̂/V₀)(κ₁(3 + 6jβ) + κ₂)/((3 + 6jβ)(1 + jβ))`.
* `floquet_voltage_stable` — `Re λ₁ < 0`, `|g_V/2| < |λ₁|`: all Floquet multipliers inside the
  unit circle for all small `ε > 0`; `floquet_voltage_unstable` — `|λ₁| < |g_V/2|`: Floquet
  unstable. With `σ = −ε Re λ₁` and detuning `ε Im λ₁` this is `ε|g_V| ≶ 2√(σ² + Δ²)`, the
  threshold `ε_crit = 4(σ/Ω)/ĝ_V` at exact tuning.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated synchronizing core (Floquet multipliers).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace Core
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.BlockAveraging

variable (c : Core)

/-- The real state matrix of the core. -/
def A0r : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, c.ω0, 0; 0, -c.D / (2 * c.H), -1 / (2 * c.H); c.ωc * c.Pδ, 0, -c.ωc]

@[tmio M, powerlib_domain] theorem A0r_map : c.A0r.map (algebraMap ℝ ℂ) = c.A0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A0r, A0]

/-- At the Hopf point the characteristic polynomial is `(s + d₂)(s² + Ω²)`. -/
@[tmio M, powerlib_domain] theorem charP_factor (Ω : ℝ) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) (s : ℂ) :
    c.charP s = (s + c.d2) * (s ^ 2 + (Ω : ℂ) ^ 2) := by
  simp only [charP]
  rw [hH2, ← a_add_ωc]
  linear_combination s * hH1

/-- The real eigenvector of the third pole `−d₂`. -/
def r3 : Fin 3 → ℝ := ![1, -c.d2 / c.ω0, -(2 * c.H * -c.d2 + c.D) * -c.d2 / c.ω0]

/-- `D'(−d₂)` (real). -/
def cD3 : ℝ := 3 * c.d2 ^ 2 + 2 * (c.D / (2 * c.H) + c.ωc) * -c.d2 + c.D / (2 * c.H) * c.ωc

/-- The real left eigenvector of the third pole, normalized `u₃ r₃ = 1`. -/
def u3 : Fin 3 → ℝ :=
  let k := -c.ω0 / (2 * c.H * c.cD3)
  ![k * (-(2 * c.H * (-c.d2 + c.ωc) * (-c.d2 + c.D / (2 * c.H))) / c.ω0),
    k * (-(2 * c.H * (-c.d2 + c.ωc))), k]

@[tmio M, powerlib_domain] theorem r3_cast : (fun i => ((c.r3 i : ℝ) : ℂ)) = c.right (-(c.d2 : ℂ)) := by
  funext i; fin_cases i <;> simp [r3, right]

@[tmio M, powerlib_domain] theorem u3_cast : (fun i => ((c.u3 i : ℝ) : ℂ)) = c.left (-(c.d2 : ℂ)) := by
  funext i; fin_cases i <;> simp [u3, left, cD3, charD, a]

@[tmio T, powerlib_foundation] theorem real_right_of_cast {A : Matrix (Fin 3) (Fin 3) ℝ}
    {w : Fin 3 → ℝ} {l : ℝ}
    (h : A.map (algebraMap ℝ ℂ) *ᵥ (fun i => (w i : ℂ)) = (l : ℂ) • (fun i => (w i : ℂ))) :
    A *ᵥ w = l • w := by
  funext i
  have := congrArg Complex.re (congrFun h i)
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this

@[tmio T, powerlib_foundation] theorem real_left_of_cast {A : Matrix (Fin 3) (Fin 3) ℝ}
    {w : Fin 3 → ℝ} {l : ℝ}
    (h : (fun i => (w i : ℂ)) ᵥ* A.map (algebraMap ℝ ℂ) = (l : ℂ) • (fun i => (w i : ℂ))) :
    w ᵥ* A = l • w := by
  funext i
  have := congrArg Complex.re (congrFun h i)
  simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this

/-- The eigen-data of the core at the Hopf point (`a ω_c = Ω²`, `d₀ = d₂ Ω²`): the pair `±jΩ`
with `r = right(jΩ)`, `u = left(jΩ)`, `u r = 1`, and the real pole `−d₂` with `r₃`, `u₃`,
`u₃ r₃ = 1`. -/
@[tmio M, powerlib_domain] theorem hopf_eigendata {Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) :
    c.A0r.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I) = ((Ω : ℂ) * I) • c.right (Ω * I) ∧
      c.left (Ω * I) ᵥ* c.A0r.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • c.left (Ω * I) ∧
      c.left (Ω * I) ⬝ᵥ c.right (Ω * I) = 1 ∧
      c.A0r *ᵥ c.r3 = (-c.d2) • c.r3 ∧ c.u3 ᵥ* c.A0r = (-c.d2) • c.u3 ∧ c.u3 ⬝ᵥ c.r3 = 1 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hP1 : c.charP ((Ω : ℂ) * I) = 0 := by
    have h0 : ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 := by linear_combination (Ω : ℂ) ^ 2 * I_sq
    rw [c.charP_factor Ω hH1 hH2, h0, mul_zero]
  have hP3 : c.charP (-(c.d2 : ℂ)) = 0 := by rw [c.charP_factor Ω hH1 hH2]; ring
  have hD1 : c.charD ((Ω : ℂ) * I) ≠ 0 := by
    rw [c.charD_hopf Ω hH1, a_add_ωc]
    refine mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero)) ?_
    exact Model.add_mul_I_ne hΩ
  have hD3 : c.charD (-(c.d2 : ℂ)) = (c.d2 : ℂ) ^ 2 + (Ω : ℂ) ^ 2 := by
    simp only [charD]; rw [a_add_ωc, hH1]; ring
  have hD3' : c.charD (-(c.d2 : ℂ)) ≠ 0 := by
    rw [hD3]
    have : (0 : ℝ) < c.d2 ^ 2 + Ω ^ 2 := by positivity
    exact_mod_cast this.ne'
  refine ⟨by rw [A0r_map]; exact c.right_eig hω0 hH hP1, by rw [A0r_map]; exact c.left_eig hω0 hH hP1,
    c.left_right hω0 hH hD1, ?_, ?_, ?_⟩
  · apply real_right_of_cast
    rw [r3_cast, A0r_map, c.right_eig hω0 hH hP3]; push_cast; rfl
  · apply real_left_of_cast
    rw [u3_cast, A0r_map, c.left_eig hω0 hH hP3]; push_cast; rfl
  · have h := c.left_right hω0 hH hD3'
    rw [← u3_cast, ← r3_cast] at h
    have h' : ((c.u3 ⬝ᵥ c.r3 : ℝ) : ℂ) = 1 := by
      rw [← h]; simp [dotProduct, Fin.sum_univ_three]
    exact_mod_cast h'

/-- The pump `g_V` of a voltage modulation of amplitude `V̂` at `ω = 2Ω` (closed form of
`pump_voltage_hopf`). -/
def gV (V0 Ω V : ℝ) : ℂ :=
  Ω * I / 2 * (V / V0) * ((c.κ1 V0 : ℂ) * (3 + 6 * ((Ω / c.d2 : ℝ) : ℂ) * I) + (c.κ2 V0 : ℂ)) /
    ((3 + 6 * ((Ω / c.d2 : ℝ) : ℂ) * I) * (1 + ((Ω / c.d2 : ℝ) : ℂ) * I))

/-- Floquet stability of the voltage-modulated core (first-order averaging, complete three-state
system). The family `A₀c + ε A₀'` passes through the Hopf point at `ε = 0` (`A₀c = A0r`), the
grid voltage is `V₀ + ε Re{V̂ e^{2jΩt}}`, and `A₁ = A₁(z_V, V̂)` is the modulation along the
forced response. With `λ₁ = u A₀' r` (first-order shift of the critical eigenvalue) and
`g_V = gV`: `Re λ₁ < 0`, `|g_V/2| < |λ₁|` give Floquet stability for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem floquet_voltage_stable {V0 Ω V : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2) (hPδ : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV V0 Ω V / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
      (Periodic.monodromy (physJ c.A0r A0' (c.A1 (c.forcedVδ (2 * Ω * I) V) V) (2 * Ω) ε)
          (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hp := c.pump_voltage_hopf V0 Ω V hPδ hV0 hH hΩ.ne' hd2.ne' hH1 hH2
  rw [Element.pump] at hp
  have hg' : ‖c.left (Ω * I) ⬝ᵥ (c.A1 (c.forcedVδ (2 * Ω * I) V) V *ᵥ star (c.right (Ω * I))) / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 := by
    rw [hp]; exact hg
  exact three_stable hΩ (neg_neg_of_pos hd2) hr hu hur hr3 hu3 hur3 A0' _ hs hg'

/-- Parametric instability of the voltage-modulated core: `|λ₁| < |g_V/2|` gives Floquet
instability of the complete three-state system for all small `ε > 0`. -/
@[tmio M, powerlib_domain] theorem floquet_voltage_unstable {V0 Ω V : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hd2 : 0 < c.d2) (hPδ : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖c.gV V0 Ω V / 2‖ ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
      (physJ c.A0r A0' (c.A1 (c.forcedVδ (2 * Ω * I) V) V) (2 * Ω) ε) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hr, hu, hur, hr3, hu3, hur3⟩ := c.hopf_eigendata hΩ.ne' hω0 hH hH1 hH2
  have hp := c.pump_voltage_hopf V0 Ω V hPδ hV0 hH hΩ.ne' hd2.ne' hH1 hH2
  rw [Element.pump] at hp
  have hg' : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (c.A1 (c.forcedVδ (2 * Ω * I) V) V *ᵥ star (c.right (Ω * I))) / 2‖ ^ 2 := by
    rw [hp]; exact hg
  exact three_unstable hΩ (neg_neg_of_pos hd2) hr hu hur hr3 hu3 hur3 A0' _ hg'

end Core
end VoltageModulation
end powerlib.GFM
