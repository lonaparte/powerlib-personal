import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.KleinKramers
import theorem.GridTiedConverter.GFM.Noise.Embedding
import theorem.GridTiedConverter.GFL.Noise.Escape

/-! # Gibbs density, circle partition function and Langer factor of the noisy two-state GFM

Domain module: the generic Klein–Kramers laws of `theorem/Stochastic/KleinKramers.lean` read on
the reduced two-state GFM of `theorem/GridTiedConverter/GFM/Noise/Embedding.lean`.

Model boundary.
* The model of `GFM.Noise.Embedding` (voltage source behind a lossy quasi-static line, VSM
  synchronization, export-positive power) in the shifted angle `θ = δ − α` and the momentum
  `p = M Δω`: the classical machine `Synchronous.classicalSM` with `b = A`, `P_m = P_ref − c₀`,
  Hamiltonian `H = p²/(2M) − P_m θ − A cos θ`. Nominal damping reference (`κ = 0`), so the
  diffusion matrix is `diag(ε², a(θ))` with the momentum diffusion
  `a(θ) = σ_P² + k²(σ_d² sin²θ + σ_q² cos²θ)` (`diffusion_eq_diag`).
* The stationarity statements are pointwise identities of the Klein–Kramers operator
  `Stochastic.KleinKramers.kkOp`; that the Gibbs function is the law of the SDE solution is not
  claimed. The partition function is the Lebesgue integral over one period of the angle times the
  momentum line. The Langer statements are eigenvalue computations of the saddle linearization.
* Excluded as in `GFM.Noise.Embedding` (no line or filter dynamics, constant `E`, continuous time);
  the three-state (power-filter) model has no Gibbs density in the swing energy and its escape
  rate is not formalized (`theorem/GridTiedConverter/GFM/Noise/FilterEscape.lean`).

Source: GFM counterpart study, note t2-noise items 5 and 7 (Gibbs density per channel,
normalizability on the circle, Langer factor; derived and checked symbolically, scratch notes
outside the repository); Kramers, Physica 7 (1940) 284; Langer, Ann. Phys. 54 (1969) 258;
Hänggi, Talkner, Borkovec, Rev. Mod. Phys. 62 (1990) 251, §IV; the GFL counterpart
`theorem/GridTiedConverter/GFL/Noise/Escape.lean`.

Results.
* The reading: `kkDrift_eq_field` (the Klein–Kramers drift with the potential `potential` is the
  classical-machine field), `gibbs_eq_hamiltonian` (`e^{−H/T}` with the machine Hamiltonian),
  `diffusion_eq_diag` (the diffusion matrix of `GFM.Noise.Params.diffusion` is
  `diag(ε², a(θ))`).
* `gibbs_stationary_iff`: without the frequency channel, `e^{−H/T}` solves the stationary
  Klein–Kramers equation everywhere iff `σ_d² = σ_q²` and `σ_P² + k² σ_q² = 2 D T` (isotropic
  voltage noise, temperature `T = (σ_P² + k² σ_v²)/(2D)`; the generic
  `Stochastic.KleinKramers.kkOp_gibbs_eq_zero_iff`); `gibbs_not_stationary_freq`: the grid-frequency
  channel alone never has a Gibbs stationary density (`D ≠ 0`), whatever `T`
  (`Stochastic.KleinKramers.kkOp_gibbs_not_stationary`).
* `gibbs_periodic_iff`: `e^{−H/T}` is a function on the circle iff `P_ref = c₀ = E²R/|Z|²`;
  `integrable_gibbs_circle`, `partition_circle`: then it is normalizable with
  `Z = 2π I₀(A/T) √(2π M T)`; `gibbs_not_integrable_plane`: on the whole plane it is never
  normalizable (`GFL.Noise.Escape.gibbs2_not_integrable`, the potential being bounded above on a
  half-line). Otherwise the stationary state, if any, carries a probability current
  (not formalized).
* `linearization_eq`, `langer_eigen`, `langer_factor`: at a saddle (`cos(δ − α) < 0`,
  `κ_b = −A cos(δ − α)`) the linearization `(J − R)∇²H` is `kkJacobian M D κ_b`, with unstable
  eigenvalue `λ₊` and `λ₊/ω_b = √(1 + ζ_b²) − ζ_b`, `ω_b = √(κ_b/M)`,
  `ζ_b = GFL.Noise.zetaA M D κ_b` (momentum damping: Langer's textbook factor, `≤ 1`).
* `langer_factor_eq_inv`, `langer_factor_mul_gfl`: it is the reciprocal of `√(1 + ζ_b²) + ζ_b`
  (`GFL.Noise.Escape.langer_factor_mul_textbook`), hence of the GFL factor
  `λ_b/ω_b` (`GFL.Noise.Escape.langer_factor`) at a GFL saddle with the same damping ratio.
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Matrix MeasureTheory Set
open powerlib.Dynamics (State)
open powerlib.Stochastic.KleinKramers (kkOp gibbs kkJacobian kkLambda)

namespace Params

variable (p : Params)

/-! ## The Klein–Kramers reading -/

/-- Potential `V(θ) = −P_m θ − A cos θ` of the shifted angle (the machine potential). -/
def potential (θ : ℝ) : ℝ := -p.toSM.Pm * θ - p.toSM.b * Real.cos θ

/-- Its derivative `V'(θ) = A sin θ − P_m`. -/
def potentialDeriv (θ : ℝ) : ℝ := p.toSM.b * Real.sin θ - p.toSM.Pm

/-- Momentum diffusion `a(θ) = σ_P² + k²(σ_d² sin²θ + σ_q² cos²θ)`. -/
def momentumDiffusion (σ : Fin 4 → ℝ) (θ : ℝ) : ℝ :=
  σ 0 ^ 2 + p.k ^ 2 * (σ 2 ^ 2 * Real.sin θ ^ 2 + σ 3 ^ 2 * Real.cos θ ^ 2)

@[tmio M, powerlib_domain] theorem hasDerivAt_potential (θ : ℝ) :
    HasDerivAt p.potential (p.potentialDeriv θ) θ := by
  have h := ((hasDerivAt_id θ).const_mul (-p.toSM.Pm)).sub ((Real.hasDerivAt_cos θ).const_mul
    p.toSM.b)
  convert h using 1
  · funext x; simp [potential]
  · simp [potentialDeriv]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_potentialDeriv (θ : ℝ) :
    HasDerivAt p.potentialDeriv (p.toSM.b * Real.cos θ) θ := by
  exact ((Real.hasDerivAt_sin θ).const_mul p.toSM.b).sub_const p.toSM.Pm

/-- The Klein–Kramers drift `(p/M, −V'(θ) − D p/M)` is the classical-machine field at `(θ, p)`. -/
@[tmio M, powerlib_domain] theorem kkDrift_eq_field (θ q : ℝ) :
    ![q / p.M, -p.potentialDeriv θ - p.D * (q / p.M)] =
      WithLp.ofLp ((Synchronous.classicalSM p.toSM).field (WithLp.toLp 2 ![θ, q]) 0) := by
  rw [Synchronous.classicalSM_field]
  ext i; fin_cases i <;> simp [potentialDeriv, toSM]

/-- The Gibbs function is `e^{−H/T}` with the machine Hamiltonian `H(θ, p)`. -/
@[tmio M, powerlib_domain] theorem gibbs_eq_hamiltonian (T θ q : ℝ) :
    gibbs p.potential p.M T θ q =
      Real.exp (-(Synchronous.classicalSM p.toSM).H (WithLp.toLp 2 ![θ, q]) / T) := by
  simp only [gibbs, Synchronous.classicalSM, PhasePlane.Conservative.separableEnergy, potential]
  congr 1
  simp [toSM]
  ring

/-- With nominal damping (`κ = 0`) the diffusion matrix at the angle `θ + α` is
`diag(ε², a(θ))`. -/
@[tmio M, powerlib_domain] theorem diffusion_eq_diag (σ : Fin 4 → ℝ) (θ : ℝ) :
    p.diffusion 0 σ (θ + p.α) * (p.diffusion 0 σ (θ + p.α))ᵀ =
      !![σ 1 ^ 2, 0; 0, p.momentumDiffusion σ θ] := by
  rw [diffusion_mul_transpose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [momentumDiffusion]

/-! ## Gibbs stationarity per channel -/

/-- **Gibbs stationarity iff isotropic voltage noise**: without the frequency channel,
`e^{−H/T}` solves the stationary Klein–Kramers equation at every `(θ, p)` iff `σ_d² = σ_q²` and
`σ_P² + k² σ_q² = 2 D T`. -/
@[tmio M, powerlib_domain] theorem gibbs_stationary_iff (σ : Fin 4 → ℝ) {T : ℝ} (hT : T ≠ 0) :
    (∀ θ q, kkOp p.M p.D 0 p.potentialDeriv (p.momentumDiffusion σ)
        (gibbs p.potential p.M T) θ q = 0) ↔
      σ 2 ^ 2 = σ 3 ^ 2 ∧ σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2 = 2 * p.D * T := by
  have hk := p.k_pos.ne'
  rw [Stochastic.KleinKramers.kkOp_gibbs_eq_zero_iff p.hasDerivAt_potential
    p.hasDerivAt_potentialDeriv p.M_pos.ne' hT]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h (π / 2)
    simp [momentumDiffusion] at h0 h1
    refine ⟨?_, h0⟩
    have : p.k ^ 2 * (σ 2 ^ 2 - σ 3 ^ 2) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hk)
    linarith
  · rintro ⟨h2, h3⟩ θ
    have hsc := Real.sin_sq_add_cos_sq θ
    simp only [momentumDiffusion, h2]
    linear_combination h3 + p.k ^ 2 * σ 3 ^ 2 * hsc

/-- **The frequency channel is never Gibbs**: with the grid-frequency channel alone (diffusion
`diag(ε², 0)`) and `D ≠ 0`, at no angle does `e^{−H/T}` solve the stationary equation for every
momentum, whatever `T ≠ 0`. -/
@[tmio M, powerlib_domain] theorem gibbs_not_stationary_freq {ε T : ℝ} (hD : p.D ≠ 0)
    (hT : T ≠ 0) (θ : ℝ) :
    ¬ ∀ q, kkOp p.M p.D (ε ^ 2) p.potentialDeriv (p.momentumDiffusion (freqOnly ε))
      (gibbs p.potential p.M T) θ q = 0 := by
  have e : p.momentumDiffusion (freqOnly ε) = fun _ => 0 := by
    funext x; simp [momentumDiffusion, freqOnly]
  rw [e]
  exact Stochastic.KleinKramers.kkOp_gibbs_not_stationary p.hasDerivAt_potential
    p.hasDerivAt_potentialDeriv p.M_pos.ne' hD hT θ

/-! ## The plane and the circle -/

/-- **Never normalizable on the plane** (`T > 0`): the potential stays below `A` on a half-line,
so `e^{−H/T}` is not integrable on `ℝ²` (`GFL.Noise.Escape.gibbs2_not_integrable`). -/
@[tmio M, powerlib_domain] theorem gibbs_not_integrable_plane {T : ℝ} (hT : 0 < T) :
    ¬ Integrable (fun z : ℝ × ℝ => gibbs p.potential p.M T z.1 z.2) (volume.prod volume) := by
  have e : (fun z : ℝ × ℝ => gibbs p.potential p.M T z.1 z.2) =
      fun z => GFL.Noise.Escape.gibbs2 p.potential (1 / p.M) T z.1 z.2 := by
    funext z; simp only [gibbs, GFL.Noise.Escape.gibbs2]; congr 1; ring
  rw [e]
  have hb : ∀ θ, -(p.toSM.b * Real.cos θ) ≤ p.A := fun θ => by
    have := Real.neg_one_le_cos θ; have := p.A_pos; simp only [toSM]; nlinarith
  rcases le_or_gt 0 p.toSM.Pm with h | h
  · refine GFL.Noise.Escape.gibbs2_not_integrable (C := p.A) (S := Ici 0) hT measurableSet_Ici
      Real.volume_Ici (fun θ (hθ : θ ∈ Ici 0) => ?_)
    have : 0 ≤ p.toSM.Pm * θ := mul_nonneg h hθ
    simp only [potential]; linarith [hb θ]
  · refine GFL.Noise.Escape.gibbs2_not_integrable (C := p.A) (S := Iic 0) hT measurableSet_Iic
      Real.volume_Iic (fun θ (hθ : θ ∈ Iic 0) => ?_)
    have : 0 ≤ p.toSM.Pm * θ := mul_nonneg_of_nonpos_of_nonpos h.le hθ
    simp only [potential]; linarith [hb θ]

/-- **A density on the circle iff `P_ref = c₀`**: `e^{−H/T}` is `2π`-periodic in the angle iff
the set-point equals the load offset `c₀ = E²R/|Z|²`. -/
@[tmio M, powerlib_domain] theorem gibbs_periodic_iff {T : ℝ} (hT : T ≠ 0) :
    (∀ θ q, gibbs p.potential p.M T (θ + 2 * π) q = gibbs p.potential p.M T θ q) ↔
      p.Pref = p.c0 := by
  have e : p.potential = fun x => -(p.toSM.Pm * x) - p.toSM.b * Real.cos (x - 0) := by
    funext x; simp [potential]
  rw [e, Stochastic.KleinKramers.gibbs_washboard_periodic_iff hT]
  simp [toSM, sub_eq_zero]

@[tmio M, powerlib_domain] private lemma potential_of_balanced (h : p.Pref = p.c0) :
    p.potential = fun x => -(p.A * Real.cos (x - 0)) := by
  funext x; simp [potential, toSM, h]

/-- For `P_ref = c₀`, `M T > 0` the circle density is normalizable. -/
@[tmio M, powerlib_domain] theorem integrable_gibbs_circle (h : p.Pref = p.c0) {T : ℝ}
    (hT : 0 < T) :
    Integrable (fun z : ℝ × ℝ => gibbs p.potential p.M T z.1 z.2)
      ((volume.restrict (Ioc 0 (2 * π))).prod volume) := by
  rw [p.potential_of_balanced h]
  exact Stochastic.KleinKramers.integrable_gibbs_circle (mul_pos p.M_pos hT) p.A 0

/-- **Partition function on the circle**: for `P_ref = c₀`,
`Z = 2π I₀(A/T) √(2π M T)`. -/
@[tmio M, powerlib_domain] theorem partition_circle (h : p.Pref = p.c0) (T : ℝ) :
    (((∫ z, gibbs p.potential p.M T z.1 z.2
        ∂((volume.restrict (Ioc 0 (2 * π))).prod volume)) : ℝ) : ℂ) =
      2 * π * SpecialFunctions.besselI0 ((p.A / T : ℝ) : ℂ) * √(2 * π * p.M * T) := by
  rw [p.potential_of_balanced h]
  exact Stochastic.KleinKramers.integral_gibbs_circle p.M T p.A 0

/-! ## Langer factor at the saddle -/

/-- The linearization `(J − R)∇²H` at `x` is the Klein–Kramers Jacobian with
`κ = −A cos(δ − α)`. -/
@[tmio M, powerlib_domain] theorem linearization_eq (x : State 2) :
    ((Synchronous.classicalSM p.toSM).J (p.shift x) -
        (Synchronous.classicalSM p.toSM).R (p.shift x)) * p.hessian x =
      kkJacobian p.M p.D (-(p.A * Real.cos (x 0 - p.α))) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Synchronous.classicalSM, hessian, kkJacobian, toSM, Matrix.diagonal_vec2,
      Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- At a saddle (`cos(δ − α) < 0`) the linearization has the unstable eigenvalue
`λ₊ = −D/(2M) + √(D²/(4M²) + κ_b/M)` with eigenvector `(1, M λ₊)`. -/
@[tmio M, powerlib_domain] theorem langer_eigen {x : State 2} (hc : Real.cos (x 0 - p.α) < 0) :
    (((Synchronous.classicalSM p.toSM).J (p.shift x) -
        (Synchronous.classicalSM p.toSM).R (p.shift x)) * p.hessian x) *ᵥ
        ![1, p.M * kkLambda p.M p.D (-(p.A * Real.cos (x 0 - p.α)))] =
      kkLambda p.M p.D (-(p.A * Real.cos (x 0 - p.α))) •
        ![1, p.M * kkLambda p.M p.D (-(p.A * Real.cos (x 0 - p.α)))] := by
  have hM := p.M_pos
  have hκ : 0 < -(p.A * Real.cos (x 0 - p.α)) := by nlinarith [p.A_pos]
  rw [linearization_eq]
  exact Stochastic.KleinKramers.kkJacobian_mulVec hM.ne' (by positivity)

/-- **GFM Langer factor**: `λ₊/ω_b = √(1 + ζ_b²) − ζ_b` with `ω_b = √(κ_b/M)` and
`ζ_b = GFL.Noise.zetaA M D κ_b`, `κ_b = −A cos(δ − α) > 0`. -/
@[tmio M, powerlib_domain] theorem langer_factor {x : State 2} (hc : Real.cos (x 0 - p.α) < 0) :
    kkLambda p.M p.D (-(p.A * Real.cos (x 0 - p.α))) /
        √(-(p.A * Real.cos (x 0 - p.α)) / p.M) =
      √(1 + GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))) ^ 2) -
        GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))) := by
  have hκ : 0 < -(p.A * Real.cos (x 0 - p.α)) := by nlinarith [p.A_pos]
  exact Stochastic.KleinKramers.kkLambda_div p.M_pos hκ

/-- The GFM factor is the reciprocal of `√(1 + ζ_b²) + ζ_b`
(`GFL.Noise.Escape.langer_factor_mul_textbook`). -/
@[tmio M, powerlib_domain] theorem langer_factor_eq_inv {x : State 2}
    (hc : Real.cos (x 0 - p.α) < 0) :
    kkLambda p.M p.D (-(p.A * Real.cos (x 0 - p.α))) /
        √(-(p.A * Real.cos (x 0 - p.α)) / p.M) =
      (√(1 + GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))) ^ 2) +
        GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α))))⁻¹ := by
  rw [p.langer_factor hc]
  exact eq_inv_of_mul_eq_one_right (GFL.Noise.Escape.langer_factor_mul_textbook _)

/-- **Reciprocal of the GFL factor**: at a GFL saddle (`K_i, c > 0`) with the same damping ratio
`PLL.zeta c K_p K_i = ζ_b`, the GFM factor times the GFL factor `λ_b/ω_b`
(`GFL.Noise.Escape.langer_factor`) is one. -/
@[tmio M, powerlib_domain] theorem langer_factor_mul_gfl {x : State 2}
    (hc : Real.cos (x 0 - p.α) < 0) {Kp Ki c : ℝ} (hKi : 0 < Ki) (hc' : 0 < c)
    (hζ : PLL.zeta c Kp Ki = GFL.Noise.zetaA p.M p.D (-(p.A * Real.cos (x 0 - p.α)))) :
    kkLambda p.M p.D (-(p.A * Real.cos (x 0 - p.α))) /
        √(-(p.A * Real.cos (x 0 - p.α)) / p.M) *
      (GFL.Noise.Escape.lambdaB Kp Ki c / PLL.omegaN c Ki) = 1 := by
  rw [p.langer_factor hc, GFL.Noise.Escape.langer_factor hKi hc', hζ, mul_comm]
  exact GFL.Noise.Escape.langer_factor_mul_textbook _

end Params

end powerlib.GFM.Noise
