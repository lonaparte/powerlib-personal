import theorem.GridTiedConverter.GFM.VoltageModulationQVOrbit

/-! # Dynamic Q–V loop: EMF behind a reactance, and the closed form at no load

The instance `P = EV sin δ/X`, `Q = (E² − EV cos δ)/X` of `VoltageModulationQVOrbit`, at any
operating point, and in closed form at no load. At no load the EMF decouples from the angle in
the linearization (`P_E = Q_δ = 0`), the stable modes are the real pole `−d₂` of the core and the
Q–V pole `−b/τ`, and the voltage pump is the three-state pump with a complex factor:
`g_V = (jΩ/2)(V̂/V₀) κ_dyn/(1 + jβ)`, `κ_dyn = 1 + k_q V₀/(X(b + 2jΩτ))`. Hence
`|κ_dyn|² = 1 + (κ_st² − 1)/(1 + θ²)`, `θ = 2Ωτ/b`: the Q–V lag passes the quasi-static
enhancement `κ_st² − 1` of the voltage pump (`VoltageModulationQV.qv_noload_kappa`) through a
first-order low-pass at the pump frequency `2Ω`, and `1 ≤ |κ_dyn|² ≤ κ_st²` when `κ_st² ≥ 1`.

Model boundary.
* The field of `VoltageModulationQVOrbit` with the lossless link (`linkP`, `linkQ`); operating
  point `(δ₀, 0, P, E₀)`, grid voltage `V₀ + εV̂ cos 2Ωt`, state perturbation `εA₀'`.
* General load: the Hopf root of the characteristic function and the spectral condition on the
  stable part are hypotheses (`orbit_link_stable`). No load (`δ₀ = 0`): every hypothesis is
  explicit — the Hopf point of the core `(D/2H)ω_c = Ω²`, `ω₀ω_c E₀V₀/(2HX) = d₂Ω²`, `d₂ > 0`, and a
  stable Q–V pole `b/τ > 0`, `b = 1 + k_q(2E₀ − V₀)/X`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (VSG core); the dynamic Q–V loop and the voltage excitation are new.

Results.
* `charF_decoupled`, `charFd_decoupled`, `kdyn`, `gV_decoupled`, `norm_gV_decoupled` — a
  decoupled EMF (`P_E = Q_δ = 0`, `P_V = 0`): the core's characteristic polynomial and
  `|g_V|² = (Ω/2)²(V̂/V₀)²|κ_dyn|²/(1 + β²)`.
* `dotProduct_eq_zero_of_eig`, `Wd`, `Wd'`, `Asd`, `decoupled_basis`, `norm_expS_Asd` — the explicit
  stable basis and `‖e^{T diag(−d₂, −b/τ)}‖ < 1`.
* `orbit_qv_decoupled_stable`, `orbit_qv_decoupled_unstable`, `orbit_qv_decoupled_exp_stable` —
  end-to-end without a spectral hypothesis.
* `fderiv_eq_of_line`, `dδ_eq_of`, `dE_eq_of`, `dV_eq_of`, `linkP`, `linkQ`, `contDiff_linkP`,
  `contDiff_linkQ`, and the sixteen partial derivatives `dδ_linkP` … `dV_dE_linkQ`; `linkCore`.
* `orbit_link_stable` — the link at any operating point.
* `linkCore_noload`, `kdyn_link`, `normSq_kdyn_link`, `kdyn_link_static`,
  `normSq_kdyn_link_bounds`, `link_noload_data` — the no-load closed forms; at `τ = 0`,
  `κ_dyn` is the static `κ₁ = 1 + k_q V₀/(X + k_q(2E₀ − V₀))`.
* `orbit_link_noload_stable`, `orbit_link_noload_unstable`, `orbit_link_noload_exp_stable` — the
  explicit criterion
  `(Ω²/16)(V̂/V₀)²(1 + (κ_st² − 1)/(1 + θ²))/(1 + β²) ≶ |λ₁|²`.

Corrections.
None: an extension (the quasi-static Q–V result of `VoltageModulationQV` is the `τ = 0` limit).

Family and connection conclusions.
None: static evidence on the voltage-modulated dynamic Q–V core with a lossless link (forced
orbit, Floquet multipliers, local exponential stability).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open scoped Matrix.Norms.Operator
open powerlib.ParametricResonance.ForcedOrbit (matX)

variable (c : DynQV)

/-! ### Decoupled EMF: `P_E = Q_δ = 0` -/

/-- With `P_E = 0` the characteristic function is that of the three-state core. -/
@[tmio M, powerlib_domain] theorem charF_decoupled (hPE : c.PE = 0) (s : ℂ) :
    c.charF s = c.core3.charP s := by
  simp [charF, Keff, hPE, Core.charP, Core.d0, a, Core.a, core3]

/-- With `P_E = 0` the derivative of the characteristic function is that of the core. -/
@[tmio M, powerlib_domain] theorem charFd_decoupled (hPE : c.PE = 0) (s : ℂ) :
    c.charFd s = c.core3.charD s := by
  simp [charFd, hPE, Core.charD, a, Core.a, core3]

/-- The voltage-pump factor of the decoupled core:
`κ_dyn = V₀ (P_δV − P_δE k_q Q_V/(2jΩτ + b))/P_δ`. -/
def kdyn (V0 Ω : ℝ) : ℂ := V0 * (c.PδV - c.PδE * c.kq * c.QV / c.lag (2 * Ω * I)) / c.Pδ

/-- At no load (`P_E = Q_δ = P_V = 0`) and the Hopf point of the core (`a ω_c = Ω²`,
`d₀ = d₂Ω²`): `g_V = (jΩ/2)(V̂/V₀) κ_dyn/(1 + jβ)`, `β = Ω/d₂`. The Q–V loop enters only through
the EMF response `z_E = −k_q Q_V V̂/(2jΩτ + b)` at the pump frequency. -/
@[tmio M, powerlib_domain] theorem gV_decoupled (hPE : c.PE = 0) (hQδ : c.Qδ = 0)
    (hPV : c.PV = 0) {Ω V0 : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hPδ : c.Pδ ≠ 0) (hV0 : V0 ≠ 0) (hd2 : c.core3.d2 ≠ 0)
    (hH1 : c.core3.a * c.core3.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.core3.d0 = (c.core3.a + c.core3.ωc) * (Ω : ℂ) ^ 2) (Vh : ℝ) :
    c.gV Ω Vh = Ω * I / 2 * (Vh / V0) * c.kdyn V0 Ω / (1 + ((Ω / c.core3.d2 : ℝ) : ℂ) * I) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hPc : (c.Pδ : ℂ) ≠ 0 := by exact_mod_cast hPδ
  have hVc : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
  have hdc : (c.core3.d2 : ℂ) ≠ 0 := by exact_mod_cast hd2
  have hD := c.core3.charD_hopf Ω hH1
  rw [Core.a_add_ωc] at hD
  have hn : (c.core3.d2 : ℂ) + Ω * I ≠ 0 := Model.add_mul_I_ne hΩ
  have hn' : 1 + ((Ω / c.core3.d2 : ℝ) : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hd0 : (c.ω0 * c.ωc * c.Pδ / (2 * c.H) : ℂ) = c.core3.d2 * (Ω : ℂ) ^ 2 := by
    have := hH2; rw [Core.a_add_ωc] at this; simpa [Core.d0, core3] using this
  rw [gV_eq]
  have hl3 : c.left (Ω * I) 3 = 0 := by simp [left, hPE]
  have hr3 : c.right (Ω * I) 3 = 0 := by simp [right, hQδ]
  have hz0 : c.forced (2 * Ω * I) Vh 0 = 0 := by simp [forced, forcedδ, PVeff, hPV, hPE]
  have hz3 : c.forced (2 * Ω * I) Vh 3 = -(c.kq * c.QV * Vh) / c.lag (2 * Ω * I) := by
    simp [forced, hQδ]; ring
  have hl2 : c.left (Ω * I) 2 = -(c.ω0 : ℂ) / (2 * c.H * (2 * (Ω * I) * (c.core3.d2 + Ω * I))) := by
    simp only [left]; rw [charFd_decoupled c hPE, hD]; simp
  rw [hl3, hr3, hz0, hz3, hl2]
  simp only [kdyn, star_zero, mul_zero, add_zero, zero_mul, sub_zero]
  push_cast
  have hd0' : (c.ω0 * c.ωc * c.Pδ : ℂ) = 2 * c.H * c.core3.d2 * (Ω : ℂ) ^ 2 := by
    field_simp at hd0; linear_combination hd0
  field_simp
  linear_combination (-((Vh : ℂ) * (c.PδV - c.PδE * c.kq * c.QV / c.lag (2 * Ω * I))) * hd0') +
    (-(2 * c.H * (Ω : ℂ) ^ 2 * c.core3.d2 * Vh *
      (c.PδV - c.PδE * c.kq * c.QV / c.lag (2 * Ω * I)))) * I_sq

omit c in
/-- Left and right eigenvectors of distinct eigenvalues are orthogonal. -/
@[tmio T, powerlib_foundation] theorem dotProduct_eq_zero_of_eig {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} {u r : n → ℂ} {μ ν : ℂ} (hu : u ᵥ* A = μ • u) (hr : A *ᵥ r = ν • r)
    (h : μ ≠ ν) : u ⬝ᵥ r = 0 := by
  have h1 : u ⬝ᵥ (A *ᵥ r) = ν * (u ⬝ᵥ r) := by rw [hr, dotProduct_smul, smul_eq_mul]
  have h2 : u ⬝ᵥ (A *ᵥ r) = μ * (u ⬝ᵥ r) := by
    rw [dotProduct_mulVec, hu, smul_dotProduct, smul_eq_mul]
  have h3 : (μ - ν) * (u ⬝ᵥ r) = 0 := by linear_combination h1 - h2
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h)

/-- The stable basis of the decoupled core: the real pole `−d₂` of the three-state core and the
EMF pole `−b/τ`. -/
def Wd : Matrix (Fin 4) (Fin 2) ℝ :=
  !![c.core3.r3 0, 0; c.core3.r3 1, 0; c.core3.r3 2, 0; 0, 1]

/-- Its left inverse. -/
def Wd' : Matrix (Fin 2) (Fin 4) ℝ :=
  !![c.core3.u3 0, c.core3.u3 1, c.core3.u3 2, 0; 0, 0, 0, 1]

/-- The stable block `diag(−d₂, −b/τ)`. -/
def Asd : Matrix (Fin 2) (Fin 2) ℝ := !![-c.core3.d2, 0; 0, -c.b / c.τ]

@[tmio M, powerlib_domain] theorem decoupled_basis (hPE : c.PE = 0) (hQδ : c.Qδ = 0) {Ω : ℝ}
    (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hH1 : c.core3.a * c.core3.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.core3.d0 = (c.core3.a + c.core3.ωc) * (Ω : ℂ) ^ 2) :
    c.A0r * c.Wd = c.Wd * c.Asd ∧ c.Wd' * c.Wd = 1 ∧
      c.left (Ω * I) ᵥ* c.Wd.map (algebraMap ℝ ℂ) = 0 ∧
      c.Wd'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I) = 0 := by
  obtain ⟨hr, hu, -, hr3, hu3, hur3⟩ := c.core3.hopf_eigendata hΩ hω0 hH hH1 hH2
  have e0 := congrFun hr3 0
  have e1 := congrFun hr3 1
  have e2 := congrFun hr3 2
  have k0 : c.core3.ω0 = c.ω0 := rfl
  have k1 : c.core3.H = c.H := rfl
  have k2 : c.core3.D = c.D := rfl
  have k3 : c.core3.ωc = c.ωc := rfl
  have k4 : c.core3.Pδ = c.Pδ := rfl
  simp only [Core.A0r, mulVec, dotProduct, Fin.sum_univ_three, k0, k1, k2, k3, k4] at e0 e1 e2
  simp at e0 e1 e2
  have hur3' : c.core3.u3 0 * c.core3.r3 0 + c.core3.u3 1 * c.core3.r3 1 +
      c.core3.u3 2 * c.core3.r3 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three] using hur3
  have hne : ((Ω : ℂ) * I) ≠ -(c.core3.d2 : ℂ) := by
    intro h; have := congrArg Complex.im h; simp at this; exact hΩ this
  have hne' : -(c.core3.d2 : ℂ) ≠ (Ω : ℂ) * I := fun h => hne h.symm
  have hr3c : c.core3.A0r.map (algebraMap ℝ ℂ) *ᵥ (fun i => (c.core3.r3 i : ℂ)) =
      (-(c.core3.d2 : ℂ)) • fun i => (c.core3.r3 i : ℂ) := by
    funext i
    have := congrArg (fun v : Fin 3 → ℝ => ((v i : ℝ) : ℂ)) hr3
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using this
  have hu3c : (fun i => (c.core3.u3 i : ℂ)) ᵥ* c.core3.A0r.map (algebraMap ℝ ℂ) =
      (-(c.core3.d2 : ℂ)) • fun i => (c.core3.u3 i : ℂ) := by
    funext i
    have := congrArg (fun v : Fin 3 → ℝ => ((v i : ℝ) : ℂ)) hu3
    simpa [vecMul, dotProduct, Fin.sum_univ_three] using this
  have o1 := dotProduct_eq_zero_of_eig hu hr3c hne
  have o2 := dotProduct_eq_zero_of_eig hu3c hr hne'
  have hl : ∀ k : Fin 3, c.left (Ω * I) k.castSucc = c.core3.left (Ω * I) k := by
    intro k; fin_cases k <;> simp [left, Core.left, charFd_decoupled c hPE, core3, a, Core.a]
  have hrr : ∀ k : Fin 3, c.right (Ω * I) k.castSucc = c.core3.right (Ω * I) k := by
    intro k; fin_cases k <;> simp [right, Core.right, core3]
  have hl3 : c.left (Ω * I) 3 = 0 := by simp [left, hPE]
  have hr3' : c.right (Ω * I) 3 = 0 := by simp [right, hQδ]
  simp only [dotProduct, Fin.sum_univ_three] at o1 o2
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A0r, Wd, Asd, b, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, hPE, hQδ] <;>
      linarith
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Wd, Wd', Matrix.mul_apply, Fin.sum_univ_four]
    linarith
  · funext j
    fin_cases j
    · have h0 := hl 0; have h1 := hl 1; have h2 := hl 2
      simp at h0 h1 h2
      simp [vecMul, dotProduct, Fin.sum_univ_four, Wd, h0, h1, h2, hl3]
      linear_combination o1
    · simp [vecMul, dotProduct, Fin.sum_univ_four, Wd, hl3]
  · funext j
    fin_cases j
    · have h0 := hrr 0; have h1 := hrr 1; have h2 := hrr 2
      simp at h0 h1 h2
      simp [mulVec, dotProduct, Fin.sum_univ_four, Wd', h0, h1, h2, hr3']
      linear_combination o2
    · simp [mulVec, dotProduct, Fin.sum_univ_four, Wd', hr3']

/-- The stable block `diag(−d₂, −b/τ)` contracts over any positive time when both poles are in
the left half plane. -/
@[tmio M, powerlib_domain] theorem norm_expS_Asd (hd2 : 0 < c.core3.d2) (hb : 0 < c.b / c.τ)
    {T : ℝ} (hT : 0 < T) : ‖BlockAveraging.expS c.Asd T‖ < 1 := by
  have hd : (T • c.Asd : Matrix (Fin 2) (Fin 2) ℝ) =
      diagonal ![T * -c.core3.d2, T * (-c.b / c.τ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Asd]
  rw [BlockAveraging.expS, hd, Matrix.exp_diagonal, Matrix.linfty_opNorm_diagonal]
  rw [pi_norm_lt_iff one_pos]
  intro i
  have he : (NormedSpace.exp ![T * -c.core3.d2, T * (-c.b / c.τ)] : Fin 2 → ℝ) i =
      Real.exp (![T * -c.core3.d2, T * (-c.b / c.τ)] i) := by
    rw [Pi.exp_def, Real.exp_eq_exp_ℝ]
  rw [he, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  fin_cases i
  · show T * -c.core3.d2 < 0
    nlinarith
  · show T * (-c.b / c.τ) < 0
    rw [neg_div]
    nlinarith

/-- The synchronizing core with a dynamic Q–V loop whose EMF is decoupled from the angle in the
linearization (`P_E = Q_δ = 0`, e.g. no load on an inductive link), grid-voltage modulation,
end-to-end, stability, with no hypothesis on the stable modes beyond their poles: at the Hopf
point of the three-state core (`a ω_c = Ω²`, `d₀ = d₂Ω²`, `d₂ > 0`) and a stable EMF pole
(`b/τ > 0`), `Re λ₁ < 0` and `|g_V/2| < |λ₁|` give the forced periodic orbit with all Floquet
multipliers inside the unit circle. The stable basis is explicit (`Wd`, `Wd'`,
`Asd = diag(−d₂, −b/τ)`). -/
@[tmio M, powerlib_domain] theorem orbit_qv_decoupled_stable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hPE0 : c.PE = 0) (hQδ0 : c.Qδ = 0)
    (hH1 : c.core3.a * c.core3.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.core3.d0 = (c.core3.a + c.core3.ωc) * (Ω : ℂ) ^ 2) (hd2 : 0 < c.core3.d2)
    (hb : 0 < c.b / c.τ) (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV Ω Vh / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => ParametricResonance.ForcedOrbit.smJ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
            (qxeq P δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  have hF : c.charF (Ω * I) = 0 := by
    have h0 : ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 := by linear_combination (Ω : ℂ) ^ 2 * I_sq
    rw [charF_decoupled c hPE0, c.core3.charP_factor Ω hH1 hH2, h0, mul_zero]
  have hFd : c.charFd (Ω * I) ≠ 0 := by
    rw [charFd_decoupled c hPE0, c.core3.charD_hopf Ω hH1, Core.a_add_ωc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero))
      (Model.add_mul_I_ne hΩ.ne')
  have hF2 : c.charF (2 * Ω * I) ≠ 0 := by
    rw [charF_decoupled c hPE0, c.core3.charP_factor Ω hH1 hH2]
    refine mul_ne_zero ?_ ?_
    · intro h; have := congrArg Complex.im h; simp at this; exact hΩ.ne' this
    · have : (2 * (Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
        linear_combination 4 * (Ω : ℂ) ^ 2 * I_sq
      rw [this]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hΩc)
  obtain ⟨hW, hWW, huW, hWr⟩ := c.decoupled_basis hPE0 hQδ0 hΩ.ne' hω0 hH hH1 hH2
  obtain ⟨hQP, hPQ, hA0, hL, hR⟩ := ParametricResonance.ForcedOrbit.modal_of_basis
    finSumFinEquiv.symm hΩ.ne' (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF)
    (c.left_right hω0 hH hl hFd) hW hWW huW hWr
  have hsrs := BlockAveraging.spectralRadius_lt_one_of_norm _
    (c.norm_expS_Asd hd2 hb (T := 2 * Real.pi / (2 * Ω)) (by positivity))
  have hA0' : ParametricResonance.ForcedOrbit.basisQ (c.left (Ω * I)) c.Wd' *
      matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) *
        ParametricResonance.ForcedOrbit.basisP (c.right (Ω * I)) c.Wd =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 c.Asd := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP c.Asd hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

/-- The decoupled dynamic Q–V core, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_qv_decoupled_unstable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hPE0 : c.PE = 0) (hQδ0 : c.Qδ = 0)
    (hH1 : c.core3.a * c.core3.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.core3.d0 = (c.core3.a + c.core3.ωc) * (Ω : ℂ) ^ 2) (hd2 : 0 < c.core3.d2)
    (hb : 0 < c.b / c.τ) (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2 <
      ‖c.gV Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => ParametricResonance.ForcedOrbit.smJ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
          (qxeq P δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  have hF : c.charF (Ω * I) = 0 := by
    have h0 : ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 := by linear_combination (Ω : ℂ) ^ 2 * I_sq
    rw [charF_decoupled c hPE0, c.core3.charP_factor Ω hH1 hH2, h0, mul_zero]
  have hFd : c.charFd (Ω * I) ≠ 0 := by
    rw [charFd_decoupled c hPE0, c.core3.charD_hopf Ω hH1, Core.a_add_ωc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero))
      (Model.add_mul_I_ne hΩ.ne')
  have hF2 : c.charF (2 * Ω * I) ≠ 0 := by
    rw [charF_decoupled c hPE0, c.core3.charP_factor Ω hH1 hH2]
    refine mul_ne_zero ?_ ?_
    · intro h; have := congrArg Complex.im h; simp at this; exact hΩ.ne' this
    · have : (2 * (Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
        linear_combination 4 * (Ω : ℂ) ^ 2 * I_sq
      rw [this]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hΩc)
  obtain ⟨hW, hWW, huW, hWr⟩ := c.decoupled_basis hPE0 hQδ0 hΩ.ne' hω0 hH hH1 hH2
  obtain ⟨hQP, hPQ, hA0, hL, hR⟩ := ParametricResonance.ForcedOrbit.modal_of_basis
    finSumFinEquiv.symm hΩ.ne' (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF)
    (c.left_right hω0 hH hl hFd) hW hWW huW hWr
  have hsrs := BlockAveraging.spectralRadius_lt_one_of_norm _
    (c.norm_expS_Asd hd2 hb (T := 2 * Real.pi / (2 * Ω)) (by positivity))
  have hA0' : ParametricResonance.ForcedOrbit.basisQ (c.left (Ω * I)) c.Wd' *
      matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) *
        ParametricResonance.ForcedOrbit.basisP (c.right (Ω * I)) c.Wd =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 c.Asd := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP c.Asd hA0' hsrs hz A0' ?_
  rw [hL, hR, hA1]; exact hg

/-- The decoupled dynamic Q–V core: the forced orbit exists and is locally exponentially stable
for the nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_qv_decoupled_exp_stable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hPE0 : c.PE = 0) (hQδ0 : c.Qδ = 0)
    (hH1 : c.core3.a * c.core3.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.core3.d0 = (c.core3.a + c.core3.ωc) * (Ω : ℂ) ^ 2) (hd2 : 0 < c.core3.d2)
    (hb : 0 < c.b / c.τ) (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : (c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))).re < 0)
    (hg : ‖c.gV Ω Vh / 2‖ ^ 2 <
      ‖c.left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + y t,
        V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t v => c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0 + v,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  have hF : c.charF (Ω * I) = 0 := by
    have h0 : ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 := by linear_combination (Ω : ℂ) ^ 2 * I_sq
    rw [charF_decoupled c hPE0, c.core3.charP_factor Ω hH1 hH2, h0, mul_zero]
  have hFd : c.charFd (Ω * I) ≠ 0 := by
    rw [charFd_decoupled c hPE0, c.core3.charD_hopf Ω hH1, Core.a_add_ωc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero))
      (Model.add_mul_I_ne hΩ.ne')
  have hF2 : c.charF (2 * Ω * I) ≠ 0 := by
    rw [charF_decoupled c hPE0, c.core3.charP_factor Ω hH1 hH2]
    refine mul_ne_zero ?_ ?_
    · intro h; have := congrArg Complex.im h; simp at this; exact hΩ.ne' this
    · have : (2 * (Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
        linear_combination 4 * (Ω : ℂ) ^ 2 * I_sq
      rw [this]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hΩc)
  obtain ⟨hW, hWW, huW, hWr⟩ := c.decoupled_basis hPE0 hQδ0 hΩ.ne' hω0 hH hH1 hH2
  obtain ⟨hQP, hPQ, hA0, hL, hR⟩ := ParametricResonance.ForcedOrbit.modal_of_basis
    finSumFinEquiv.symm hΩ.ne' (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF)
    (c.left_right hω0 hH hl hFd) hW hWW huW hWr
  have hsrs := BlockAveraging.spectralRadius_lt_one_of_norm _
    (c.norm_expS_Asd hd2 hb (T := 2 * Real.pi / (2 * Ω)) (by positivity))
  have hA0' : ParametricResonance.ForcedOrbit.basisQ (c.left (Ω * I)) c.Wd' *
      matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) *
        ParametricResonance.ForcedOrbit.basisP (c.right (Ω * I)) c.Wd =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 c.Asd := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP c.Asd hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

/-! ### Directional derivatives from line derivatives -/

@[tmio T, powerlib_foundation] theorem fderiv_eq_of_line {G : (ℝ × ℝ) × ℝ → ℝ}
    {p e : (ℝ × ℝ) × ℝ} (hG : DifferentiableAt ℝ G p) {a : ℝ}
    (h : HasDerivAt (fun s : ℝ => G (p + s • e)) a 0) : fderiv ℝ G p e = a := by
  have hl : HasDerivAt (fun s : ℝ => p + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p
  exact (hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)).unique h

@[tmio T, powerlib_foundation] theorem dδ_eq_of {G g : (ℝ × ℝ) × ℝ → ℝ}
    (hG : Differentiable ℝ G)
    (h : ∀ p : (ℝ × ℝ) × ℝ, HasDerivAt (fun s : ℝ => G ((p.1.1 + s, p.1.2), p.2)) (g p) 0) :
    dδ G = g := funext fun p => fderiv_eq_of_line (hG p) (by
      convert h p using 2 with s
      congr 1; ext <;> simp)

@[tmio T, powerlib_foundation] theorem dE_eq_of {G g : (ℝ × ℝ) × ℝ → ℝ}
    (hG : Differentiable ℝ G)
    (h : ∀ p : (ℝ × ℝ) × ℝ, HasDerivAt (fun s : ℝ => G ((p.1.1, p.1.2 + s), p.2)) (g p) 0) :
    dE G = g := funext fun p => fderiv_eq_of_line (hG p) (by
      convert h p using 2 with s
      congr 1; ext <;> simp)

@[tmio T, powerlib_foundation] theorem dV_eq_of {G g : (ℝ × ℝ) × ℝ → ℝ}
    (hG : Differentiable ℝ G)
    (h : ∀ p : (ℝ × ℝ) × ℝ, HasDerivAt (fun s : ℝ => G ((p.1.1, p.1.2), p.2 + s)) (g p) 0) :
    dV G = g := funext fun p => fderiv_eq_of_line (hG p) (by
      convert h p using 2 with s
      congr 1; ext <;> simp)

/-! ### EMF behind a reactance -/

/-- Active power of the EMF `E∠δ` behind a reactance `X` against the grid `V∠0`. -/
def linkP (X : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ := p.1.2 * p.2 * Real.sin p.1.1 / X

/-- Reactive power at the EMF, `Q = (E² − E V cos δ)/X`. -/
def linkQ (X : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ := (p.1.2 ^ 2 - p.1.2 * p.2 * Real.cos p.1.1) / X

@[tmio M, powerlib_domain] theorem contDiff_linkP (X : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (linkP X) := by
  unfold linkP; fun_prop

@[tmio M, powerlib_domain] theorem contDiff_linkQ (X : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (linkQ X) := by
  unfold linkQ; fun_prop

@[tmio M, powerlib_domain] theorem dδ_linkP (X : ℝ) :
    dδ (linkP X) = fun p => p.1.2 * p.2 * Real.cos p.1.1 / X :=
  dδ_eq_of ((contDiff_linkP X (n := 1)).differentiable (by norm_num)) fun p => by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_add p.1.1).sin.const_mul (p.1.2 * p.2)).div_const X
    convert h using 1 <;> simp [linkP]

@[tmio M, powerlib_domain] theorem dE_linkP (X : ℝ) :
    dE (linkP X) = fun p => p.2 * Real.sin p.1.1 / X :=
  dE_eq_of ((contDiff_linkP X (n := 1)).differentiable (by norm_num)) fun p => by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add p.1.2).mul_const (p.2 * Real.sin p.1.1))).div_const X
    convert h using 1
    · funext s; simp [linkP]; ring
    · simp

@[tmio M, powerlib_domain] theorem dV_linkP (X : ℝ) :
    dV (linkP X) = fun p => p.1.2 * Real.sin p.1.1 / X :=
  dV_eq_of ((contDiff_linkP X (n := 1)).differentiable (by norm_num)) fun p => by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add p.2).const_mul p.1.2).mul_const
      (Real.sin p.1.1)).div_const X
    convert h using 1 <;> simp [linkP]

@[tmio M, powerlib_domain] theorem dδ_linkQ (X : ℝ) :
    dδ (linkQ X) = fun p => p.1.2 * p.2 * Real.sin p.1.1 / X :=
  dδ_eq_of ((contDiff_linkQ X (n := 1)).differentiable (by norm_num)) fun p => by
    have h := ((hasDerivAt_const (0 : ℝ) (p.1.2 ^ 2)).sub
      ((((hasDerivAt_id' (0 : ℝ)).const_add p.1.1).cos).const_mul (p.1.2 * p.2))).div_const X
    convert h using 1 <;> simp [linkQ]

@[tmio M, powerlib_domain] theorem dE_linkQ (X : ℝ) :
    dE (linkQ X) = fun p => (2 * p.1.2 - p.2 * Real.cos p.1.1) / X :=
  dE_eq_of ((contDiff_linkQ X (n := 1)).differentiable (by norm_num)) fun p => by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add p.1.2).pow 2).sub
      (((hasDerivAt_id' (0 : ℝ)).const_add p.1.2).mul_const (p.2 * Real.cos p.1.1))).div_const X
    convert h using 1
    · funext s; simp [linkQ]; ring
    · simp

@[tmio M, powerlib_domain] theorem dV_linkQ (X : ℝ) :
    dV (linkQ X) = fun p => -(p.1.2 * Real.cos p.1.1) / X :=
  dV_eq_of ((contDiff_linkQ X (n := 1)).differentiable (by norm_num)) fun p => by
    have h := ((hasDerivAt_const (0 : ℝ) (p.1.2 ^ 2)).sub
      ((((hasDerivAt_id' (0 : ℝ)).const_add p.2).const_mul p.1.2).mul_const
        (Real.cos p.1.1))).div_const X
    convert h using 1 <;> simp [linkQ]

/-! Second partials. -/

@[tmio M, powerlib_domain] theorem dδ_dδ_linkP (X : ℝ) :
    dδ (dδ (linkP X)) = fun p => -(p.1.2 * p.2 * Real.sin p.1.1) / X := by
  rw [dδ_linkP]
  refine dδ_eq_of (by fun_prop) fun p => ?_
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add p.1.1).cos.const_mul (p.1.2 * p.2)).div_const X
  convert h using 1; simp

@[tmio M, powerlib_domain] theorem dE_dδ_linkP (X : ℝ) :
    dE (dδ (linkP X)) = fun p => p.2 * Real.cos p.1.1 / X := by
  rw [dδ_linkP]
  refine dE_eq_of (by fun_prop) fun p => ?_
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add p.1.2).mul_const
    (p.2 * Real.cos p.1.1)).div_const X
  convert h using 1
  · funext s; ring
  · simp

@[tmio M, powerlib_domain] theorem dE_dE_linkP (X : ℝ) : dE (dE (linkP X)) = fun _ => 0 := by
  rw [dE_linkP]
  exact dE_eq_of (by fun_prop) fun p => hasDerivAt_const (0 : ℝ) (p.2 * Real.sin p.1.1 / X)

@[tmio M, powerlib_domain] theorem dV_dδ_linkP (X : ℝ) :
    dV (dδ (linkP X)) = fun p => p.1.2 * Real.cos p.1.1 / X := by
  rw [dδ_linkP]
  refine dV_eq_of (by fun_prop) fun p => ?_
  have h := ((((hasDerivAt_id' (0 : ℝ)).const_add p.2).const_mul p.1.2).mul_const
    (Real.cos p.1.1)).div_const X
  convert h using 1; simp

@[tmio M, powerlib_domain] theorem dV_dE_linkP (X : ℝ) :
    dV (dE (linkP X)) = fun p => Real.sin p.1.1 / X := by
  rw [dE_linkP]
  refine dV_eq_of (by fun_prop) fun p => ?_
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add p.2).mul_const (Real.sin p.1.1)).div_const X
  convert h using 1; simp

@[tmio M, powerlib_domain] theorem dδ_dδ_linkQ (X : ℝ) :
    dδ (dδ (linkQ X)) = fun p => p.1.2 * p.2 * Real.cos p.1.1 / X := by
  rw [dδ_linkQ]
  refine dδ_eq_of (by fun_prop) fun p => ?_
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add p.1.1).sin.const_mul (p.1.2 * p.2)).div_const X
  convert h using 1; simp

@[tmio M, powerlib_domain] theorem dE_dδ_linkQ (X : ℝ) :
    dE (dδ (linkQ X)) = fun p => p.2 * Real.sin p.1.1 / X := by
  rw [dδ_linkQ]
  refine dE_eq_of (by fun_prop) fun p => ?_
  have h := (((hasDerivAt_id' (0 : ℝ)).const_add p.1.2).mul_const
    (p.2 * Real.sin p.1.1)).div_const X
  convert h using 1
  · funext s; ring
  · simp

@[tmio M, powerlib_domain] theorem dE_dE_linkQ (X : ℝ) : dE (dE (linkQ X)) = fun _ => 2 / X := by
  rw [dE_linkQ]
  refine dE_eq_of (by fun_prop) fun p => ?_
  have h := ((((hasDerivAt_id' (0 : ℝ)).const_add p.1.2).const_mul 2).sub_const
    (p.2 * Real.cos p.1.1)).div_const X
  convert h using 1; simp

@[tmio M, powerlib_domain] theorem dV_dδ_linkQ (X : ℝ) :
    dV (dδ (linkQ X)) = fun p => p.1.2 * Real.sin p.1.1 / X := by
  rw [dδ_linkQ]
  refine dV_eq_of (by fun_prop) fun p => ?_
  have h := ((((hasDerivAt_id' (0 : ℝ)).const_add p.2).const_mul p.1.2).mul_const
    (Real.sin p.1.1)).div_const X
  convert h using 1; simp

@[tmio M, powerlib_domain] theorem dV_dE_linkQ (X : ℝ) :
    dV (dE (linkQ X)) = fun p => -Real.cos p.1.1 / X := by
  rw [dE_linkQ]
  refine dV_eq_of (by fun_prop) fun p => ?_
  have h := ((hasDerivAt_const (0 : ℝ) (2 * p.1.2)).sub
    (((hasDerivAt_id' (0 : ℝ)).const_add p.2).mul_const (Real.cos p.1.1))).div_const X
  convert h using 1; simp


/-! ### The link at an operating point -/

/-- The dynamic Q–V core of the EMF behind a reactance at `(δ₀, E₀, V₀)`: the partial derivatives
of `linkP`, `linkQ` there. -/
def linkCore (ω0 H D ωc τ kq X δ0 E0 V0 : ℝ) : DynQV where
  ω0 := ω0
  H := H
  D := D
  ωc := ωc
  τ := τ
  kq := kq
  Pδ := E0 * V0 * Real.cos δ0 / X
  PE := V0 * Real.sin δ0 / X
  PV := E0 * Real.sin δ0 / X
  Qδ := E0 * V0 * Real.sin δ0 / X
  QE := (2 * E0 - V0 * Real.cos δ0) / X
  QV := -(E0 * Real.cos δ0) / X
  Pδδ := -(E0 * V0 * Real.sin δ0) / X
  PδE := V0 * Real.cos δ0 / X
  PEE := 0
  PδV := E0 * Real.cos δ0 / X
  PEV := Real.sin δ0 / X
  Qδδ := E0 * V0 * Real.cos δ0 / X
  QδE := V0 * Real.sin δ0 / X
  QEE := 2 / X
  QδV := E0 * Real.sin δ0 / X
  QEV := -Real.cos δ0 / X

/-- The EMF behind a reactance with a dynamic Q–V loop at any operating point `(δ₀, E₀, V₀)`,
grid-voltage modulation, end-to-end, stability: `orbit_qv_stable` with the port maps
`P = EV sin δ/X`, `Q = (E² − EV cos δ)/X`, whose sixteen partial derivatives are those of
`linkCore`. -/
@[tmio M, powerlib_domain] theorem orbit_link_stable {ω0 H D ωc τ kq X δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : τ ≠ 0)
    (hF : (linkCore ω0 H D ωc τ kq X δ0 E0 V0).charF (Ω * I) = 0)
    (hFd : (linkCore ω0 H D ωc τ kq X δ0 E0 V0).charFd (Ω * I) ≠ 0)
    (hF2 : (linkCore ω0 H D ωc τ kq X δ0 E0 V0).charF (2 * Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS
      (linkCore ω0 H D ωc τ kq X δ0 E0 V0).A0r (2 * Real.pi / (2 * Ω)) *
      (1 - ParametricResonance.ForcedOrbit.critP
        ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ
          ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).left (Ω * I) ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X δ0 E0 V0).right (Ω * I))).re < 0)
    (hg : ‖(linkCore ω0 H D ωc τ kq X δ0 E0 V0).gV Ω Vh / 2‖ ^ 2 <
      ‖(linkCore ω0 H D ωc τ kq X δ0 E0 V0).left (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X δ0 E0 V0).right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X)
          (linkP X ((δ0, E0), V0)) E0 (linkQ X ((δ0, E0), V0)) (qxeq (linkP X) δ0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X)
          (linkP X ((δ0, E0), V0)) E0 (linkQ X ((δ0, E0), V0)) (qxeq (linkP X) δ0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => ParametricResonance.ForcedOrbit.smJ
            ((linkCore ω0 H D ωc τ kq X δ0 E0 V0).qfield (linkP X) (linkQ X)
              (linkP X ((δ0, E0), V0)) E0 (linkQ X ((δ0, E0), V0)))
            (qxeq (linkP X) δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 :=
  (linkCore ω0 H D ωc τ kq X δ0 E0 V0).orbit_qv_stable (contDiff_linkP X) (contDiff_linkQ X)
    hΩ hω0 hH hτ (by rw [dδ_linkP]; rfl) (by rw [dE_linkP]; rfl) (by rw [dV_linkP]; rfl)
    (by rw [dδ_linkQ]; rfl) (by rw [dE_linkQ]; rfl) (by rw [dV_linkQ]; rfl)
    (by rw [dδ_dδ_linkP]; rfl) (by rw [dE_dδ_linkP]; rfl) (by rw [dE_dE_linkP]; rfl)
    (by rw [dV_dδ_linkP]; rfl) (by rw [dV_dE_linkP]; rfl) (by rw [dδ_dδ_linkQ]; rfl)
    (by rw [dE_dδ_linkQ]; rfl) (by rw [dE_dE_linkQ]; rfl) (by rw [dV_dδ_linkQ]; rfl)
    (by rw [dV_dE_linkQ]; rfl) hF hFd hF2 hsr Vh A0' hs hg

/-! ### No load: closed form -/

/-- At no load (`δ₀ = 0`) the EMF is decoupled from the angle (`P_E = Q_δ = 0`) and the port power
does not depend on the grid voltage (`P_V = 0`). -/
@[tmio M, powerlib_domain] theorem linkCore_noload (ω0 H D ωc τ kq X E0 V0 : ℝ) :
    (linkCore ω0 H D ωc τ kq X 0 E0 V0).PE = 0 ∧ (linkCore ω0 H D ωc τ kq X 0 E0 V0).Qδ = 0 ∧
      (linkCore ω0 H D ωc τ kq X 0 E0 V0).PV = 0 := by
  simp [linkCore]

/-- The voltage-pump factor of the link at no load:
`κ_dyn = 1 + k_q V₀/(X(b + 2jΩτ))`, `b = 1 + k_q(2E₀ − V₀)/X`. -/
@[tmio M, powerlib_domain] theorem kdyn_link {ω0 H D ωc τ kq X E0 V0 : ℝ} (Ω : ℝ) (hX : X ≠ 0)
    (hE0 : E0 ≠ 0) (hV0 : V0 ≠ 0) :
    (linkCore ω0 H D ωc τ kq X 0 E0 V0).kdyn V0 Ω =
      1 + kq * V0 / (X * (linkCore ω0 H D ωc τ kq X 0 E0 V0).lag (2 * Ω * I)) := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hEc : (E0 : ℂ) ≠ 0 := by exact_mod_cast hE0
  have hVc : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
  simp only [kdyn]
  generalize (linkCore ω0 H D ωc τ kq X 0 E0 V0).lag (2 * Ω * I) = L
  simp [linkCore]
  rcases eq_or_ne L 0 with h | h
  · simp [h]; field_simp
  · field_simp; ring

/-- `|κ_dyn|² = 1 + (κ_st² − 1)/(1 + θ²)`, `κ_st = 1 + k_q V₀/(X b)` (the quasi-static
`κ₁` of `qv_noload_kappa`), `θ = 2Ωτ/b`: the Q–V lag passes the static enhancement `κ_st² − 1`
of the voltage pump through a first-order low-pass at the pump frequency `2Ω`. -/
@[tmio M, powerlib_domain] theorem normSq_kdyn_link {ω0 H D ωc τ kq X E0 V0 : ℝ} (Ω : ℝ)
    (hX : X ≠ 0) (hE0 : E0 ≠ 0) (hV0 : V0 ≠ 0) (hb : (linkCore ω0 H D ωc τ kq X 0 E0 V0).b ≠ 0) :
    ‖(linkCore ω0 H D ωc τ kq X 0 E0 V0).kdyn V0 Ω‖ ^ 2 =
      1 + ((1 + kq * V0 / (X * (linkCore ω0 H D ωc τ kq X 0 E0 V0).b)) ^ 2 - 1) /
        (1 + (2 * Ω * τ / (linkCore ω0 H D ωc τ kq X 0 E0 V0).b) ^ 2) := by
  rw [kdyn_link Ω hX hE0 hV0]
  set b := (linkCore ω0 H D ωc τ kq X 0 E0 V0).b with hbd
  have hl : (linkCore ω0 H D ωc τ kq X 0 E0 V0).lag (2 * Ω * I) = (b : ℂ) + (2 * Ω * τ : ℝ) * I := by
    simp only [lag]; rw [← hbd]; push_cast
    show (τ : ℂ) * (2 * Ω * I) + b = b + 2 * Ω * τ * I
    ring
  rw [hl, Complex.sq_norm, Complex.normSq_apply]
  have hden : (0 : ℝ) < b ^ 2 + (2 * Ω * τ) ^ 2 := by positivity
  have hre : (1 + (kq * V0 : ℂ) / (X * ((b : ℂ) + (2 * Ω * τ : ℝ) * I))).re =
      1 + kq * V0 * b / (X * (b ^ 2 + (2 * Ω * τ) ^ 2)) := by
    rw [show (kq * V0 : ℂ) / (X * ((b : ℂ) + (2 * Ω * τ : ℝ) * I)) =
      ((kq * V0 / X : ℝ) : ℂ) / ((b : ℂ) + (2 * Ω * τ : ℝ) * I) by push_cast; field_simp]
    rw [Complex.add_re, Complex.one_re, Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
  have him : (1 + (kq * V0 : ℂ) / (X * ((b : ℂ) + (2 * Ω * τ : ℝ) * I))).im =
      -(kq * V0 * (2 * Ω * τ)) / (X * (b ^ 2 + (2 * Ω * τ) ^ 2)) := by
    rw [show (kq * V0 : ℂ) / (X * ((b : ℂ) + (2 * Ω * τ : ℝ) * I)) =
      ((kq * V0 / X : ℝ) : ℂ) / ((b : ℂ) + (2 * Ω * τ : ℝ) * I) by push_cast; field_simp]
    rw [Complex.add_im, Complex.one_im, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
  rw [hre, him]
  field_simp
  ring

/-- `|g_V|² = (Ω/2)²(V̂/V₀)²|κ_dyn|²/(1 + β²)` for the decoupled core at its Hopf point. -/
@[tmio M, powerlib_domain] theorem norm_gV_decoupled (hPE : c.PE = 0) (hQδ : c.Qδ = 0)
    (hPV : c.PV = 0) {Ω V0 : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hPδ : c.Pδ ≠ 0) (hV0 : V0 ≠ 0) (hd2 : c.core3.d2 ≠ 0)
    (hH1 : c.core3.a * c.core3.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.core3.d0 = (c.core3.a + c.core3.ωc) * (Ω : ℂ) ^ 2) (Vh : ℝ) :
    ‖c.gV Ω Vh‖ ^ 2 =
      (Ω / 2) ^ 2 * (Vh / V0) ^ 2 * ‖c.kdyn V0 Ω‖ ^ 2 / (1 + (Ω / c.core3.d2) ^ 2) := by
  rw [c.gV_decoupled hPE hQδ hPV hΩ hω0 hH hPδ hV0 hd2 hH1 hH2]
  have h1 : ‖1 + ((Ω / c.core3.d2 : ℝ) : ℂ) * I‖ ^ 2 = 1 + (Ω / c.core3.d2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖(Ω : ℂ) * I / 2‖ = |Ω| / 2 := by simp
  have h3 : ‖(Vh : ℂ) / V0‖ = |Vh / V0| := by
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_div, norm_mul, norm_mul, h2, h3, div_pow, mul_pow, mul_pow, h1, div_pow, sq_abs,
    sq_abs]
  ring

/-- The link at no load, data of the decoupled theorems: the Hopf conditions of the core in real
form, and the voltage pump in closed form,
`|g_V/2|² = (Ω²/16)(V̂/V₀)² (1 + (κ_st² − 1)/(1 + θ²))/(1 + β²)`, `κ_st = 1 + k_q V₀/(X + k_q(2E₀ − V₀))`,
`θ = 2ΩτX/(X + k_q(2E₀ − V₀))`, `β = Ω/d₂`. -/
@[tmio M, powerlib_domain] theorem link_noload_data {ω0 H D ωc τ kq X E0 V0 Ω : ℝ} (hΩ : Ω ≠ 0)
    (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hX : X ≠ 0) (hE0 : E0 ≠ 0) (hV0 : V0 ≠ 0)
    (hH1 : D / (2 * H) * ωc = Ω ^ 2)
    (hH2 : ω0 * ωc * (E0 * V0 / X) / (2 * H) = (D / (2 * H) + ωc) * Ω ^ 2)
    (hd2 : 0 < D / (2 * H) + ωc) (hb : 0 < (1 + kq * (2 * E0 - V0) / X) / τ) (Vh : ℝ) :
    (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.a * (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.ωc = (Ω : ℂ) ^ 2 ∧
      (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.d0 = ((linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.a + (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.ωc) * (Ω : ℂ) ^ 2 ∧
      0 < (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.d2 ∧ 0 < (linkCore ω0 H D ωc τ kq X 0 E0 V0).b / (linkCore ω0 H D ωc τ kq X 0 E0 V0).τ ∧
      ‖(linkCore ω0 H D ωc τ kq X 0 E0 V0).gV Ω Vh / 2‖ ^ 2 = Ω ^ 2 / 16 * (Vh / V0) ^ 2 *
        (1 + ((1 + kq * V0 / (X + kq * (2 * E0 - V0))) ^ 2 - 1) /
          (1 + (2 * Ω * τ * X / (X + kq * (2 * E0 - V0))) ^ 2)) /
        (1 + (Ω / (D / (2 * H) + ωc)) ^ 2) := by
  obtain ⟨hPE, hQδ, hPV⟩ := linkCore_noload ω0 H D ωc τ kq X E0 V0
  have hbe : (linkCore ω0 H D ωc τ kq X 0 E0 V0).b = 1 + kq * (2 * E0 - V0) / X := by simp [b, linkCore]; ring
  have hbn : (linkCore ω0 H D ωc τ kq X 0 E0 V0).b ≠ 0 := by
    rw [hbe]; intro h; rw [h, zero_div] at hb; exact lt_irrefl 0 hb
  have hXb : X + kq * (2 * E0 - V0) ≠ 0 := by
    intro h; apply hbn; rw [hbe]; field_simp; linarith
  have hd2e : (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.d2 = D / (2 * H) + ωc := by simp [Core.d2, core3, linkCore]
  have hPδ : (linkCore ω0 H D ωc τ kq X 0 E0 V0).Pδ ≠ 0 := by simp [linkCore]; exact ⟨⟨hE0, hV0⟩, hX⟩
  have hH1' : (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.a * (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.ωc = (Ω : ℂ) ^ 2 := by
    have : ((D / (2 * H) * ωc : ℝ) : ℂ) = (Ω : ℂ) ^ 2 := by exact_mod_cast hH1
    simpa [Core.a, core3, linkCore] using this
  have hH2' : (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.d0 = ((linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.a + (linkCore ω0 H D ωc τ kq X 0 E0 V0).core3.ωc) * (Ω : ℂ) ^ 2 := by
    have : ((ω0 * ωc * (E0 * V0 / X) / (2 * H) : ℝ) : ℂ) =
        ((D / (2 * H) + ωc) * Ω ^ 2 : ℝ) := by exact_mod_cast hH2
    simpa [Core.d0, Core.a, core3, linkCore] using this
  refine ⟨hH1', hH2', by rw [hd2e]; exact hd2, by rw [hbe]; exact hb, ?_⟩
  rw [norm_div, div_pow, (linkCore ω0 H D ωc τ kq X 0 E0 V0).norm_gV_decoupled hPE hQδ hPV hΩ hω0 hH hPδ hV0
    (by rw [hd2e]; exact hd2.ne') hH1' hH2' Vh, normSq_kdyn_link Ω hX hE0 hV0 hbn, hbe, hd2e]
  have e1 : X * (1 + kq * (2 * E0 - V0) / X) = X + kq * (2 * E0 - V0) := by field_simp
  have e2 : 2 * Ω * τ / (1 + kq * (2 * E0 - V0) / X) = 2 * Ω * τ * X / (X + kq * (2 * E0 - V0)) := by
    rw [← e1]; field_simp
  rw [e1, e2]
  norm_num
  ring

/-- The EMF behind a reactance with a dynamic Q–V loop at no load, grid-voltage modulation,
end-to-end, stability, fully explicit: at the Hopf point of the core
(`(D/2H) ω_c = Ω²`, `ω₀ω_c E₀V₀/(2HX) = d₂Ω²`, `d₂ = D/2H + ω_c > 0`) with a stable Q–V pole
(`b/τ > 0`), `Re λ₁ < 0` and
`(Ω²/16)(V̂/V₀)²(1 + (κ_st² − 1)/(1 + θ²))/(1 + β²) < |λ₁|²` give the forced periodic orbit with
all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_link_noload_stable {ω0 H D ωc τ kq X E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : τ ≠ 0) (hX : X ≠ 0) (hE0 : E0 ≠ 0)
    (hV0 : V0 ≠ 0) (hH1 : D / (2 * H) * ωc = Ω ^ 2)
    (hH2 : ω0 * ωc * (E0 * V0 / X) / (2 * H) = (D / (2 * H) + ωc) * Ω ^ 2)
    (hd2 : 0 < D / (2 * H) + ωc) (hb : 0 < (1 + kq * (2 * E0 - V0) / X) / τ) (Vh : ℝ)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ((linkCore ω0 H D ωc τ kq X 0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X 0 E0 V0).right (Ω * I))).re < 0)
    (hg : Ω ^ 2 / 16 * (Vh / V0) ^ 2 *
        (1 + ((1 + kq * V0 / (X + kq * (2 * E0 - V0))) ^ 2 - 1) /
          (1 + (2 * Ω * τ * X / (X + kq * (2 * E0 - V0))) ^ 2)) /
        (1 + (Ω / (D / (2 * H) + ωc)) ^ 2) <
      ‖(linkCore ω0 H D ωc τ kq X 0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X 0 E0 V0).right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0)) E0
          (linkQ X ((0, E0), V0)) (qxeq (linkP X) 0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0)) E0
          (linkQ X ((0, E0), V0)) (qxeq (linkP X) 0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => ParametricResonance.ForcedOrbit.smJ
            ((linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0)) E0 (linkQ X ((0, E0), V0)))
            (qxeq (linkP X) 0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hPE, hQδ, -⟩ := linkCore_noload ω0 H D ωc τ kq X E0 V0
  obtain ⟨hH1', hH2', hd2', hb', hgV⟩ :=
    link_noload_data hΩ.ne' hω0 hH hX hE0 hV0 hH1 hH2 hd2 hb Vh
  exact (linkCore ω0 H D ωc τ kq X 0 E0 V0).orbit_qv_decoupled_stable (contDiff_linkP X) (contDiff_linkQ X)
    hΩ hω0 hH hτ (by rw [dδ_linkP]; rfl) (by rw [dE_linkP]; rfl) (by rw [dV_linkP]; rfl)
    (by rw [dδ_linkQ]; rfl) (by rw [dE_linkQ]; rfl) (by rw [dV_linkQ]; rfl)
    (by rw [dδ_dδ_linkP]; rfl) (by rw [dE_dδ_linkP]; rfl) (by rw [dE_dE_linkP]; rfl)
    (by rw [dV_dδ_linkP]; rfl) (by rw [dV_dE_linkP]; rfl) (by rw [dδ_dδ_linkQ]; rfl)
    (by rw [dE_dδ_linkQ]; rfl) (by rw [dE_dE_linkQ]; rfl) (by rw [dV_dδ_linkQ]; rfl)
    (by rw [dV_dE_linkQ]; rfl) hPE hQδ hH1' hH2' hd2' hb' Vh A0' hs (by rw [hgV]; exact hg)

/-- The EMF behind a reactance with a dynamic Q–V loop at no load, end-to-end, parametric
instability: `|λ₁|² < (Ω²/16)(V̂/V₀)²(1 + (κ_st² − 1)/(1 + θ²))/(1 + β²)` makes the forced orbit
Floquet unstable. -/
@[tmio M, powerlib_domain] theorem orbit_link_noload_unstable {ω0 H D ωc τ kq X E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : τ ≠ 0) (hX : X ≠ 0) (hE0 : E0 ≠ 0)
    (hV0 : V0 ≠ 0) (hH1 : D / (2 * H) * ωc = Ω ^ 2)
    (hH2 : ω0 * ωc * (E0 * V0 / X) / (2 * H) = (D / (2 * H) + ωc) * Ω ^ 2)
    (hd2 : 0 < D / (2 * H) + ωc) (hb : 0 < (1 + kq * (2 * E0 - V0) / X) / τ) (Vh : ℝ)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖(linkCore ω0 H D ωc τ kq X 0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X 0 E0 V0).right (Ω * I))‖ ^ 2 <
      Ω ^ 2 / 16 * (Vh / V0) ^ 2 *
        (1 + ((1 + kq * V0 / (X + kq * (2 * E0 - V0))) ^ 2 - 1) /
          (1 + (2 * Ω * τ * X / (X + kq * (2 * E0 - V0))) ^ 2)) /
        (1 + (Ω / (D / (2 * H) + ωc)) ^ 2)) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0)) E0
          (linkQ X ((0, E0), V0)) (qxeq (linkP X) 0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0)) E0
          (linkQ X ((0, E0), V0)) (qxeq (linkP X) 0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => ParametricResonance.ForcedOrbit.smJ
          ((linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0)) E0 (linkQ X ((0, E0), V0)))
          (qxeq (linkP X) 0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hPE, hQδ, -⟩ := linkCore_noload ω0 H D ωc τ kq X E0 V0
  obtain ⟨hH1', hH2', hd2', hb', hgV⟩ :=
    link_noload_data hΩ.ne' hω0 hH hX hE0 hV0 hH1 hH2 hd2 hb Vh
  exact (linkCore ω0 H D ωc τ kq X 0 E0 V0).orbit_qv_decoupled_unstable (contDiff_linkP X) (contDiff_linkQ X)
    hΩ hω0 hH hτ (by rw [dδ_linkP]; rfl) (by rw [dE_linkP]; rfl) (by rw [dV_linkP]; rfl)
    (by rw [dδ_linkQ]; rfl) (by rw [dE_linkQ]; rfl) (by rw [dV_linkQ]; rfl)
    (by rw [dδ_dδ_linkP]; rfl) (by rw [dE_dδ_linkP]; rfl) (by rw [dE_dE_linkP]; rfl)
    (by rw [dV_dδ_linkP]; rfl) (by rw [dV_dE_linkP]; rfl) (by rw [dδ_dδ_linkQ]; rfl)
    (by rw [dE_dδ_linkQ]; rfl) (by rw [dE_dE_linkQ]; rfl) (by rw [dV_dδ_linkQ]; rfl)
    (by rw [dV_dE_linkQ]; rfl) hPE hQδ hH1' hH2' hd2' hb' Vh A0' (by rw [hgV]; exact hg)

/-- The quasi-static limit `τ = 0`: `κ_dyn` is the static `κ₁ = 1 + k_q V₀/(X + k_q(2E₀ − V₀))` of
the Q–V droop (`VoltageModulationQV.qv_noload_kappa`). -/
@[tmio M, powerlib_domain] theorem kdyn_link_static {ω0 H D ωc kq X E0 V0 : ℝ} (Ω : ℝ)
    (hX : X ≠ 0) (hE0 : E0 ≠ 0) (hV0 : V0 ≠ 0) :
    (linkCore ω0 H D ωc 0 kq X 0 E0 V0).kdyn V0 Ω = 1 + kq * V0 / (X + kq * (2 * E0 - V0)) := by
  rw [kdyn_link Ω hX hE0 hV0]
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  simp only [lag, b, linkCore]
  push_cast
  simp only [zero_mul, zero_add]
  congr 1
  simp only [Complex.cos_zero, mul_one]
  congr 1
  field_simp

/-- The dynamic Q–V loop pumps between the constant EMF and the quasi-static droop: with
`κ_st² ≥ 1` (e.g. `k_q ≥ 0`), `1 ≤ |κ_dyn|² ≤ κ_st²`, the upper bound attained at `τ = 0`, the
lower one approached as `τ → ∞`. -/
@[tmio M, powerlib_domain] theorem normSq_kdyn_link_bounds {ω0 H D ωc τ kq X E0 V0 : ℝ} (Ω : ℝ)
    (hX : X ≠ 0) (hE0 : E0 ≠ 0) (hV0 : V0 ≠ 0) (hb : (linkCore ω0 H D ωc τ kq X 0 E0 V0).b ≠ 0)
    (hk : 1 ≤ (1 + kq * V0 / (X * (linkCore ω0 H D ωc τ kq X 0 E0 V0).b)) ^ 2) :
    1 ≤ ‖(linkCore ω0 H D ωc τ kq X 0 E0 V0).kdyn V0 Ω‖ ^ 2 ∧ ‖(linkCore ω0 H D ωc τ kq X 0 E0 V0).kdyn V0 Ω‖ ^ 2 ≤ (1 + kq * V0 / (X * (linkCore ω0 H D ωc τ kq X 0 E0 V0).b)) ^ 2 := by
  rw [normSq_kdyn_link Ω hX hE0 hV0 hb]
  set κ := (1 + kq * V0 / (X * (linkCore ω0 H D ωc τ kq X 0 E0 V0).b)) ^ 2
  set θ := (2 * Ω * τ / (linkCore ω0 H D ωc τ kq X 0 E0 V0).b) ^ 2
  have hθ : 0 ≤ θ := sq_nonneg _
  have h1 : 0 < 1 + θ := by linarith
  have h2 : 0 ≤ (κ - 1) / (1 + θ) := div_nonneg (by linarith) h1.le
  refine ⟨by linarith, ?_⟩
  have h3 : (κ - 1) / (1 + θ) ≤ κ - 1 := div_le_self (by linarith) (by linarith)
  linarith

/-- The EMF behind a reactance with a dynamic Q–V loop at no load: under the hypotheses of
`orbit_link_noload_stable` the forced orbit exists and is locally exponentially stable for the
nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_link_noload_exp_stable {ω0 H D ωc τ kq X E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : τ ≠ 0) (hX : X ≠ 0) (hE0 : E0 ≠ 0)
    (hV0 : V0 ≠ 0) (hH1 : D / (2 * H) * ωc = Ω ^ 2)
    (hH2 : ω0 * ωc * (E0 * V0 / X) / (2 * H) = (D / (2 * H) + ωc) * Ω ^ 2)
    (hd2 : 0 < D / (2 * H) + ωc) (hb : 0 < (1 + kq * (2 * E0 - V0) / X) / τ) (Vh : ℝ)
    (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ((linkCore ω0 H D ωc τ kq X 0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X 0 E0 V0).right (Ω * I))).re < 0)
    (hg : Ω ^ 2 / 16 * (Vh / V0) ^ 2 *
        (1 + ((1 + kq * V0 / (X + kq * (2 * E0 - V0))) ^ 2 - 1) /
          (1 + (2 * Ω * τ * X / (X + kq * (2 * E0 - V0))) ^ 2)) /
        (1 + (Ω / (D / (2 * H) + ωc)) ^ 2) <
      ‖(linkCore ω0 H D ωc τ kq X 0 E0 V0).left (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (linkCore ω0 H D ωc τ kq X 0 E0 V0).right (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y ((linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0)) E0
        (linkQ X ((0, E0), V0)) (qxeq (linkP X) 0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 4 → ℝ),
        IsIntegralCurveOn x (fun t v => (linkCore ω0 H D ωc τ kq X 0 E0 V0).qfield (linkP X) (linkQ X) (linkP X ((0, E0), V0))
          E0 (linkQ X ((0, E0), V0)) (qxeq (linkP X) 0 E0 V0 + v,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hPE, hQδ, -⟩ := linkCore_noload ω0 H D ωc τ kq X E0 V0
  obtain ⟨hH1', hH2', hd2', hb', hgV⟩ :=
    link_noload_data hΩ.ne' hω0 hH hX hE0 hV0 hH1 hH2 hd2 hb Vh
  exact (linkCore ω0 H D ωc τ kq X 0 E0 V0).orbit_qv_decoupled_exp_stable (contDiff_linkP X) (contDiff_linkQ X)
    hΩ hω0 hH hτ (by rw [dδ_linkP]; rfl) (by rw [dE_linkP]; rfl) (by rw [dV_linkP]; rfl)
    (by rw [dδ_linkQ]; rfl) (by rw [dE_linkQ]; rfl) (by rw [dV_linkQ]; rfl)
    (by rw [dδ_dδ_linkP]; rfl) (by rw [dE_dδ_linkP]; rfl) (by rw [dE_dE_linkP]; rfl)
    (by rw [dV_dδ_linkP]; rfl) (by rw [dV_dE_linkP]; rfl) (by rw [dδ_dδ_linkQ]; rfl)
    (by rw [dE_dδ_linkQ]; rfl) (by rw [dE_dE_linkQ]; rfl) (by rw [dV_dδ_linkQ]; rfl)
    (by rw [dV_dE_linkQ]; rfl) hPE hQδ hH1' hH2' hd2' hb' Vh A0' hs (by rw [hgV]; exact hg)

end DynQV
end VoltageModulation
end powerlib.GFM
