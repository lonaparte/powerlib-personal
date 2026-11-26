import theorem.GridTiedConverter.GFM.VoltageModulationQVDynamic
import theorem.ParametricResonance.StableBasis
import theorem.ParametricResonance.SmoothOrbitStability
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Dynamic Q–V loop under grid-voltage modulation: forced orbit, Floquet multipliers, stability

The nonlinear synchronizing core with a dynamic Q–V loop and `C³` port maps `P(δ, E, V)`,
`Q(δ, E, V)`. Its Jacobian, voltage input and second derivatives are identified with the data of
`DynQV`, so `SmoothForcedOrbit` and `StableBasis` give the end-to-end statements: at a simple root
`jΩ` of the characteristic function, with `V = V₀ + εV̂ cos 2Ωt` and `εA₀'`, the forced orbit exists
for small `ε > 0`, its Floquet multipliers follow `|g_V/2| ≶ |λ₁|`, and in the stable case it is
locally exponentially stable for the nonlinear system.

Model boundary.
* States `(δ, Δω, P_f, E)` (`qfield`), port maps of class `C³`, setpoints at the operating point
  `x₀ = (δ₀, 0, P(δ₀, E₀, V₀), E₀)` (`qxeq`); quasi-static network.
* Hypotheses: the sixteen partial derivatives of `P`, `Q` at `(δ₀, E₀, V₀)` (the mixed ones are
  symmetric, `dδ_dE`); `F(jΩ) = 0`, `F'(jΩ) ≠ 0`, `F(2jΩ) ≠ 0`; the stable part through the
  spectral radius of `e^{TA₀}(I − Π)` below one (`T = π/Ω`, `Π` the real projector onto the critical
  plane). `VoltageModulationQVLink` removes the last hypothesis when the EMF is decoupled.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (first-order averaging along the forced trajectory), §3 (VSG core); the
dynamic Q–V loop and the voltage excitation are new.

Results.
* `dδ`, `dE`, `dV`, `contDiff_dδ`, `contDiff_dE`, `fderiv_split`, `hasDerivAt_port_line`,
  `dδ_dE` — partial derivatives of a port map along lines; symmetry of the mixed partial.
* `port`, `qfield`, `contDiff_port`, `contDiff_qfield`, `qjac`, `matX_qfield`, `qxeq`,
  `qfield_eq_zero`, `qjac_eq` — the field, its Jacobian at every state, `∂ₓF(x₀) = A₀`.
* `fderivW_qfield`, `smDx_qfield`, `smM1_qfield`, `smA1_qfield`, `zorb_qfield` — the voltage
  input, the second derivatives, `smA1 = A₁(z_δ, z_E, V̂)` and the first-order orbit.
* `orbit_qv_stable`, `orbit_qv_unstable`, `orbit_qv_exp_stable` — the end-to-end Floquet and
  exponential-stability statements.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated dynamic Q–V core (forced orbit, Floquet
multipliers, local exponential stability).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)

variable (c : DynQV)

/-! ### Port maps `G((δ, E), V)` and their partial derivatives -/

/-- `∂G/∂δ`. -/
def dδ (G : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ := fderiv ℝ G p ((1, 0), 0)
/-- `∂G/∂E`. -/
def dE (G : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ := fderiv ℝ G p ((0, 1), 0)
/-- `∂G/∂V`. -/
def dV (G : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ := fderiv ℝ G p ((0, 0), 1)

omit c in
@[tmio T, powerlib_foundation] theorem contDiff_dδ {G : (ℝ × ℝ) × ℝ → ℝ} (hG : ContDiff ℝ 3 G) :
    ContDiff ℝ 2 (dδ G) :=
  (hG.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

omit c in
@[tmio T, powerlib_foundation] theorem contDiff_dE {G : (ℝ × ℝ) × ℝ → ℝ} (hG : ContDiff ℝ 3 G) :
    ContDiff ℝ 2 (dE G) :=
  (hG.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

omit c in
/-- A directional derivative in partials: `G'((u, v), w) = u ∂_δG + v ∂_EG + w ∂_VG`. -/
@[tmio T, powerlib_foundation] theorem fderiv_split (G : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ)
    (u v w : ℝ) : fderiv ℝ G p ((u, v), w) = u * dδ G p + v * dE G p + w * dV G p := by
  have e : (((u, v), w) : (ℝ × ℝ) × ℝ) = u • ((1, 0), 0) + v • ((0, 1), 0) + w • ((0, 0), 1) := by
    ext <;> simp
  rw [e, map_add, map_add, map_smul, map_smul, map_smul]
  simp [dδ, dE, dV]

omit c in
@[tmio T, powerlib_foundation] theorem hasDerivAt_port_line {G : (ℝ × ℝ) × ℝ → ℝ} {α β γ : ℝ}
    (hG : DifferentiableAt ℝ G ((α, β), γ)) (u v w : ℝ) :
    HasDerivAt (fun s : ℝ => G ((α + s * u, β + s * v), γ + s * w))
      (u * dδ G ((α, β), γ) + v * dE G ((α, β), γ) + w * dV G ((α, β), γ)) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => α + s * u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add α
  have h2 : HasDerivAt (fun s : ℝ => β + s * v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add β
  have h3 : HasDerivAt (fun s : ℝ => γ + s * w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w).const_add γ
  rw [← fderiv_split]
  exact hG.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ((h1.prodMk h2).prodMk h3) (by simp)

omit c in
/-- The mixed partials of a `C³` port map agree: `∂_δ∂_E G = ∂_E∂_δ G`. -/
@[tmio T, powerlib_foundation] theorem dδ_dE {G : (ℝ × ℝ) × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    (p : (ℝ × ℝ) × ℝ) : dδ (dE G) p = dE (dδ G) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) p :=
    ((hG.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) p
  have e1 : ∀ e v, fderiv ℝ (fun p => fderiv ℝ G p e) p v = fderiv ℝ (fderiv ℝ G) p v e :=
    fun e v => by rw [fderiv_clm_apply hd (differentiableAt_const e)]; simp
  have hs : IsSymmSndFDerivAt ℝ G p :=
    (hG.contDiffAt : ContDiffAt ℝ 3 G p).isSymmSndFDerivAt (by simp; norm_num)
  show fderiv ℝ (fun p => fderiv ℝ G p ((0, 1), 0)) p ((1, 0), 0) =
    fderiv ℝ (fun p => fderiv ℝ G p ((1, 0), 0)) p ((0, 1), 0)
  rw [e1, e1, hs]

/-! ### The field -/

/-- The port point `((δ, E), V)` of a state. -/
def port (q : (Fin 4 → ℝ) × ℝ) : (ℝ × ℝ) × ℝ := ((q.1 0, q.1 3), q.2)

/-- The synchronizing core with a dynamic Q–V loop: states `(δ, Δω, P_f, E)`,
`δ̇ = ω₀ Δω`, `Δω̇ = (P* − P_f − D Δω)/(2H)`, `Ṗ_f = ω_c(P(δ, E, V) − P_f)`,
`τ Ė = E* − E − k_q(Q(δ, E, V) − Q*)`. -/
def qfield (P Q : (ℝ × ℝ) × ℝ → ℝ) (Pset Eset Qset : ℝ) (q : (Fin 4 → ℝ) × ℝ) : Fin 4 → ℝ :=
  ![c.ω0 * q.1 1, (Pset - q.1 2 - c.D * q.1 1) / (2 * c.H), c.ωc * (P (port q) - q.1 2),
    (Eset - q.1 3 - c.kq * (Q (port q) - Qset)) / c.τ]

omit c in
@[tmio T, powerlib_foundation] theorem contDiff_port {n : WithTop ℕ∞} :
    ContDiff ℝ n port :=
  (((contDiff_apply ℝ ℝ (0 : Fin 4)).comp contDiff_fst).prodMk
    ((contDiff_apply ℝ ℝ (3 : Fin 4)).comp contDiff_fst)).prodMk contDiff_snd

@[tmio M, powerlib_domain] theorem contDiff_qfield {P Q : (ℝ × ℝ) × ℝ → ℝ} {n : WithTop ℕ∞}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) (Pset Eset Qset : ℝ) :
    ContDiff ℝ n (c.qfield P Q Pset Eset Qset) := by
  have hx : ∀ i : Fin 4, ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hPq : ContDiff ℝ n fun q => P (port q) := hP.comp contDiff_port
  have hQq : ContDiff ℝ n fun q => Q (port q) := hQ.comp contDiff_port
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (hx 1)
  · exact ((contDiff_const.sub (hx 2)).sub (contDiff_const.mul (hx 1))).div_const _
  · exact contDiff_const.mul (hPq.sub (hx 2))
  · exact ((contDiff_const.sub (hx 3)).sub
      (contDiff_const.mul (hQq.sub contDiff_const))).div_const _

/-- The Jacobian of the field at `(x, V)`. -/
def qjac (P Q : (ℝ × ℝ) × ℝ → ℝ) (q : (Fin 4 → ℝ) × ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, c.ω0, 0, 0;
    0, -c.D / (2 * c.H), -1 / (2 * c.H), 0;
    c.ωc * dδ P (port q), 0, -c.ωc, c.ωc * dE P (port q);
    -(c.kq * dδ Q (port q)) / c.τ, 0, 0, -(1 + c.kq * dE Q (port q)) / c.τ]

@[tmio M, powerlib_domain] theorem matX_qfield {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) (Pset Eset Qset : ℝ) (q : (Fin 4 → ℝ) × ℝ) :
    matX (c.qfield P Q Pset Eset Qset) q = c.qjac P Q q := by
  refine ParametricResonance.ForcedOrbit.matX_of_line
    ((c.contDiff_qfield hP hQ _ _ _).differentiable (by norm_num) _) fun y => ?_
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (q.1 + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (q.1 i)
  have hline : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 3 G →
      HasDerivAt (fun s : ℝ => G (port (q.1 + s • y, q.2)))
        (y 0 * dδ G (port q) + y 3 * dE G (port q)) 0 := fun G hG => by
    have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) (port q)) (y 0) (y 3) 0
    simp only [zero_mul, add_zero, port] at h ⊢
    convert h using 1
    funext s; simp
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine ((hl 1).const_mul c.ω0).congr_deriv ?_
    show _ = (c.qjac P Q q *ᵥ y) 0
    simp [qjac, mulVec, dotProduct, Fin.sum_univ_four]
  · refine ((((hasDerivAt_const (0 : ℝ) Pset).sub (hl 2)).sub
      ((hl 1).const_mul c.D)).div_const (2 * c.H)).congr_deriv ?_
    show _ = (c.qjac P Q q *ᵥ y) 1
    simp [qjac, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · refine (((hline P hP).sub (hl 2)).const_mul c.ωc).congr_deriv ?_
    show _ = (c.qjac P Q q *ᵥ y) 2
    simp [qjac, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · refine ((((hasDerivAt_const (0 : ℝ) Eset).sub (hl 3)).sub
      (((hline Q hQ).sub_const Qset).const_mul c.kq)).div_const c.τ).congr_deriv ?_
    show _ = (c.qjac P Q q *ᵥ y) 3
    simp [qjac, mulVec, dotProduct, Fin.sum_univ_four]; ring

/-- The operating point `x₀ = (δ₀, 0, P(δ₀, E₀, V₀), E₀)`. -/
def qxeq (P : (ℝ × ℝ) × ℝ → ℝ) (δ0 E0 V0 : ℝ) : Fin 4 → ℝ := ![δ0, 0, P ((δ0, E0), V0), E0]

@[tmio M, powerlib_domain] theorem qfield_eq_zero (P Q : (ℝ × ℝ) × ℝ → ℝ) (δ0 E0 V0 : ℝ) :
    c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeq P δ0 E0 V0, V0) = 0 := by
  funext i
  fin_cases i <;> simp [qfield, qxeq, port]

@[tmio M, powerlib_domain] theorem qjac_eq {P Q : (ℝ × ℝ) × ℝ → ℝ} {δ0 E0 V0 : ℝ}
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) :
    c.qjac P Q (qxeq P δ0 E0 V0, V0) = c.A0r := by
  have e : port (qxeq P δ0 E0 V0, V0) = ((δ0, E0), V0) := by simp [port, qxeq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qjac, A0r, e, hPδ, hPE, hQδ, hQE]

/-- `∂_V F(x₀, V₀) = B_V`. -/
@[tmio M, powerlib_domain] theorem fderivW_qfield {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ} (hPV : dV P ((δ0, E0), V0) = c.PV)
    (hQV : dV Q ((δ0, E0), V0) = c.QV) :
    ofv (fderiv ℝ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
      (qxeq P δ0 E0 V0, V0) (0, 1)) = c.Bv := by
  have hlv : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 3 G →
      HasDerivAt (fun s : ℝ => G (port (qxeq P δ0 E0 V0, V0 + s))) (dV G ((δ0, E0), V0)) 0 :=
    fun G hG => by
      have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) ((δ0, E0), V0)) 0 0 1
      simp only [zero_mul, mul_zero, add_zero, mul_one, one_mul, zero_add] at h
      convert h using 1
      funext s; simp [port, qxeq]
  have e : fderiv ℝ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
      (qxeq P δ0 E0 V0, V0) (0, 1) = ![0, 0, c.ωc * c.PV, -(c.kq * c.QV) / c.τ] := by
    refine ParametricResonance.ForcedOrbit.fderivW_of_line
      ((c.contDiff_qfield hP hQ _ _ _).differentiable (by norm_num) _) (hasDerivAt_pi.2 fun i => ?_)
    fin_cases i
    · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [qfield, qxeq])
    · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [qfield, qxeq])
    · have h := ((hlv P hP).sub_const (P ((δ0, E0), V0))).const_mul c.ωc
      rw [hPV] at h
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [qfield, qxeq])
    · have h := ((((hlv Q hQ).sub_const (Q ((δ0, E0), V0))).const_mul c.kq).neg).div_const c.τ
      rw [hQV] at h
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp [qfield, qxeq]
  rw [e]
  funext i
  fin_cases i <;> simp [ofv, Bv]

@[tmio M, powerlib_domain] theorem smDx_qfield {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ}
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (y : Fin 4 → ℝ) :
    smDx (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) y =
      !![0, 0, 0, 0;
        0, 0, 0, 0;
        c.ωc * (y 0 * c.Pδδ + y 3 * c.PδE), 0, 0, c.ωc * (y 0 * c.PδE + y 3 * c.PEE);
        -(c.kq * (y 0 * c.Qδδ + y 3 * c.QδE)) / c.τ, 0, 0,
          -(c.kq * (y 0 * c.QδE + y 3 * c.QEE)) / c.τ] := by
  have hline : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 2 G →
      HasDerivAt (fun t : ℝ => G (port (qxeq P δ0 E0 V0 + t • y, V0)))
        (y 0 * dδ G ((δ0, E0), V0) + y 3 * dE G ((δ0, E0), V0)) 0 := fun G hG => by
    have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) ((δ0, E0), V0))
      (y 0) (y 3) 0
    simp only [zero_mul, mul_zero, add_zero] at h
    convert h using 1
    funext t; simp [port, qxeq]
  have hPd := hline _ (contDiff_dδ hP)
  rw [hPδδ, hPδE] at hPd
  have hPe := hline _ (contDiff_dE hP)
  rw [dδ_dE hP, hPδE, hPEE] at hPe
  have hQd := hline _ (contDiff_dδ hQ)
  rw [hQδδ, hQδE] at hQd
  have hQe := hline _ (contDiff_dE hQ)
  rw [dδ_dE hQ, hQδE, hQEE] at hQe
  have hF2 : ContDiffAt ℝ 2 (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
      (qxeq P δ0 E0 V0, V0) :=
    (c.contDiff_qfield (hP.of_le (by norm_num)) (hQ.of_le (by norm_num)) _ _ _).contDiffAt
  have hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
      (qxeq P δ0 E0 V0 + t • y, V0) = c.qjac P Q (qxeq P δ0 E0 V0 + t • y, V0) :=
    Filter.Eventually.of_forall fun t => c.matX_qfield hP hQ _ _ _ _
  refine ParametricResonance.ForcedOrbit.smDx_of_line hF2 y hJ fun i j => ?_
  have ev : ∀ {f g : ℝ → ℝ}, (∀ t, f t = g t) → f =ᶠ[𝓝 (0 : ℝ)] g :=
    fun h => Filter.Eventually.of_forall h
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) c.ω0
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.D / (2 * c.H))
  · exact hasDerivAt_const (0 : ℝ) (-1 / (2 * c.H))
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact (hPd.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.ωc)
  · exact (hPe.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjac])
  · exact (((hQd.const_mul c.kq).neg).div_const c.τ).congr_of_eventuallyEq
      (ev fun t => by simp [qjac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact ((((hQe.const_mul c.kq).const_add 1).neg).div_const c.τ).congr_of_eventuallyEq
      (ev fun t => by simp [qjac])

@[tmio M, powerlib_domain] theorem smM1_qfield {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ}
    (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV) (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV) :
    smM1 (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) =
      !![0, 0, 0, 0;
        0, 0, 0, 0;
        c.ωc * c.PδV, 0, 0, c.ωc * c.PEV;
        -(c.kq * c.QδV) / c.τ, 0, 0, -(c.kq * c.QEV) / c.τ] := by
  have hline : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 2 G →
      HasDerivAt (fun t : ℝ => G (port (qxeq P δ0 E0 V0, V0 + t))) (dV G ((δ0, E0), V0)) 0 :=
    fun G hG => by
      have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) ((δ0, E0), V0)) 0 0 1
      simp only [zero_mul, mul_zero, add_zero, mul_one, one_mul, zero_add] at h
      convert h using 1
      funext t; simp [port, qxeq]
  have hPd := hline _ (contDiff_dδ hP)
  rw [hPδV] at hPd
  have hPe := hline _ (contDiff_dE hP)
  rw [hPEV] at hPe
  have hQd := hline _ (contDiff_dδ hQ)
  rw [hQδV] at hQd
  have hQe := hline _ (contDiff_dE hQ)
  rw [hQEV] at hQe
  have hF2 : ContDiffAt ℝ 2 (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
      (qxeq P δ0 E0 V0, V0) :=
    (c.contDiff_qfield (hP.of_le (by norm_num)) (hQ.of_le (by norm_num)) _ _ _).contDiffAt
  have hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)))
      (qxeq P δ0 E0 V0, V0 + t) = c.qjac P Q (qxeq P δ0 E0 V0, V0 + t) :=
    Filter.Eventually.of_forall fun t => c.matX_qfield hP hQ _ _ _ _
  refine ParametricResonance.ForcedOrbit.smM1_of_line hF2 hJ fun i j => ?_
  have ev : ∀ {f g : ℝ → ℝ}, (∀ t, f t = g t) → f =ᶠ[𝓝 (0 : ℝ)] g :=
    fun h => Filter.Eventually.of_forall h
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) c.ω0
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.D / (2 * c.H))
  · exact hasDerivAt_const (0 : ℝ) (-1 / (2 * c.H))
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact (hPd.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.ωc)
  · exact (hPe.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjac])
  · exact (((hQd.const_mul c.kq).neg).div_const c.τ).congr_of_eventuallyEq
      (ev fun t => by simp [qjac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact ((((hQe.const_mul c.kq).const_add 1).neg).div_const c.τ).congr_of_eventuallyEq
      (ev fun t => by simp [qjac])

/-- The modulation of the field along `(z, V̂)` is the core's `A₁(z_δ, z_E, V̂)`. -/
@[tmio M, powerlib_domain] theorem smA1_qfield {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ}
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV) (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (Vh : ℝ) (z : Fin 4 → ℂ) :
    smA1 (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) Vh z =
      c.A1 (z 0) (z 3) Vh := by
  have hdx := c.smDx_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE
  have hm := c.smM1_qfield hP hQ hPδV hPEV hQδV hQEV
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC, hdx, hm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [A1, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- The first-order orbit `z = z(2jΩ, V̂)` solves `(2jΩ − ∂ₓF) z = V̂ ∂_V F`. -/
@[tmio M, powerlib_domain] theorem zorb_qfield {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hF2 : c.charF (2 * Ω * I) ≠ 0) (Vh : ℝ) :
    (((2 * Ω : ℝ) : ℂ) * I) • c.forced (2 * Ω * I) Vh -
        (matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ c.forced (2 * Ω * I) Vh =
      (Vh : ℂ) • fun i => ((fderiv ℝ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ) := by
  have hl : c.lag (2 * Ω * I) ≠ 0 := by
    have := c.lag_ne (ω := 2 * Ω) hτ (mul_ne_zero two_ne_zero hΩ)
    push_cast at this
    exact this
  have hf := c.forced_eq (Vh : ℂ) hω0 hH hτ hl hF2
  have hb : (fun i => ((fderiv ℝ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ)) = c.Bv :=
    c.fderivW_qfield hP hQ hPV hQV
  rw [hb, c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  push_cast
  exact hf

/-- The synchronizing core with a dynamic Q–V loop (`C³` port maps `P`, `Q` of angle, EMF and
grid voltage), grid-voltage modulation, end-to-end, stability. At an operating point where the
characteristic function has the simple root `jΩ` (`F(jΩ) = 0`, `F'(jΩ) ≠ 0`, `F(2jΩ) ≠ 0`) and the
rest of the one-period map is contracting (`ρ(e^{TA₀}(I − Π)) < 1`), with
`V = V₀ + ε V̂ cos 2Ωt` and `ε A₀'`: `Re λ₁ < 0` and `|g_V/2| < |λ₁|` (`λ₁ = u A₀' r`,
`g_V = gV`) give, for all small `ε > 0`, the forced periodic orbit with all Floquet multipliers
inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_qv_stable {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0) (hF2 : c.charF (2 * Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
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
          (Periodic.monodromy (fun t => smJ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF) (c.left_right hω0 hH hl hFd) _
      hsr
  have hA0' : Qm * matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

/-- The synchronizing core with a dynamic Q–V loop, grid-voltage modulation, end-to-end,
parametric instability: `|λ₁| < |g_V/2|` makes the forced orbit Floquet unstable. -/
@[tmio M, powerlib_domain] theorem orbit_qv_unstable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0) (hF2 : c.charF (2 * Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
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
        Periodic.FloquetUnstable (fun t => smJ (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t
          (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF) (c.left_right hω0 hH hl hFd) _
      hsr
  have hA0' : Qm * matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_
  rw [hL, hR, hA1]; exact hg

/-- The synchronizing core with a dynamic Q–V loop: under the hypotheses of `orbit_qv_stable` the
forced orbit exists and is locally exponentially stable for the nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_qv_exp_stable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (hF : c.charF (Ω * I) = 0) (hFd : c.charFd (Ω * I) ≠ 0) (hF2 : c.charF (2 * Ω * I) ≠ 0)
    (hsr : spectralRadius ℂ ((ParametricResonance.BlockAveraging.expS c.A0r
      (2 * Real.pi / (2 * Ω)) * (1 - ParametricResonance.ForcedOrbit.critP (c.right (Ω * I)) *
        ParametricResonance.ForcedOrbit.critQ (c.left (Ω * I)))).map (algebraMap ℝ ℂ)) < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
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
  have hm : matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) = c.A0r := by
    rw [c.matX_qfield hP hQ, c.qjac_eq hPδ hPE hQδ hQE]
  have hl := c.lag_ne hτ hΩ.ne'
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_eig (n := 4) (m := 2) rfl hΩ.ne'
      (c.right_eig hω0 hH hτ hl hF) (c.left_eig hω0 hH hτ hl hF) (c.left_right hω0 hH hl hFd) _
      hsr
  have hA0' : Qm * matX (c.qfield P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeq P δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorb_qfield hP hQ hΩ.ne' hω0 hH hτ hPδ hPE hQδ hQE hPV hQV hF2 Vh
  have hA1 := c.smA1_qfield hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forced (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable
    (c.contDiff_qfield hP hQ _ _ _).contDiffAt (c.qfield_eq_zero P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

end DynQV
end VoltageModulation
end powerlib.GFM
