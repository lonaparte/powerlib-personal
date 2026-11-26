import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.DetailedBalance
import theorem.Stochastic.DetailedBalanceUnique
import theorem.GridTiedConverter.GFM.Noise.FilterEmbedding
import theorem.GridTiedConverter.GFM.Noise.FilterEscape
import theorem.GridTiedConverter.GFM.Noise.Escape
import theorem.GridTiedConverter.GFM.Bifurcation
import theorem.GridTiedConverter.GFM.Port.VSMLPFPH

/-! # The noisy three-state GFM is not reversible: why no Kramers–Langer rate applies

Domain module: exact statements in place of the study's claim that "the escape rate of the
three-state model (VSM + power filter) has no closed form", which is not a mathematical
proposition. The Kramers–Langer (Eyring–Kramers) rate of an underdamped system rests on
generalized detailed balance — a stationary density satisfying the coefficient conditions of
time-reversal symmetry with the frequency odd, the Gibbs density `e^{−H/T}` under
fluctuation–dissipation — and on an index-one saddle whose unstable eigenvalue gives the
prefactor. The noisy three-state model satisfies generalized detailed balance for no positive
differentiable density, for every noise channel and damping reference; its drift has no
constant-structure port-Hamiltonian form; its saddle is of index one with an unstable eigenvalue
strictly below the two-state (Langer) value. The two-state model satisfies generalized detailed
balance under fluctuation–dissipation.

Model boundary.
* The noisy model of `theorem/GridTiedConverter/GFM/Noise/FilterEmbedding.lean` (`Params3`):
  state `(δ, ω, P_f)`, read on `Fin 3 → ℝ`; drift `sdeDrift`, the field `GFM.VSMLPFLossy.field`
  of `Params3.toLossy` (`δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P(δ) − P_f)`,
  `P(δ) = c₀ + A sin(δ − α)`, export-positive power, per unit; `M, ω_c, A, k > 0`, `D ≥ 0`);
  white-noise channels with intensities `σ = (σ_P, σ_g, σ_d, σ_q)` (set point, grid frequency,
  written `ε` in `FilterEmbedding`, d- and q-axis grid voltage) and damping reference `κ`,
  diffusion matrix `h hᵀ` (`sdeDiffusion`, from `Params3.diffusion`). The Itô and Stratonovich
  drifts coincide (`Params3.strat_eq_zero`), so the drift is unambiguous.
* Reversibility is the coefficient characterization
  `Stochastic.DetailedBalance.GenDetailedBalance` (Gardiner (5.3.53)): a parity, a positive
  density, the diffusion and drift conditions and stationarity of the divergence-form operator
  (with set-point noise it is `Params3.fpOp` of `FilterEscape`, `fpOp_setPoint`). Parities: `ε ≡ 1`
  (detailed balance proper, zero probability current) and the momentum flip
  `(δ, ω, P_f) ↦ (δ, −ω, P_f)` (`momentumFlip`); without voltage noise every parity. Densities:
  positive and differentiable on `Fin 3 → ℝ`, not necessarily normalizable; without voltage noise
  any positive function. That these conditions are the time-reversal symmetry of the stationary
  diffusion, and every statement about laws, paths or exit times, are not formalized (Rules §3).
* Excluded as in `GFM.Noise.FilterEmbedding`.
* The escape rate itself stays outside the library. (i) That the operator governs the law of the
  diffusion (Kolmogorov / Itô) is not formalized. (ii) The Kramers–Langer asymptotics need the
  detailed balance refuted here. (iii) Without it the exponent is the Freidlin–Wentzell
  quasi-potential at the saddle. With set-point noise alone the diffusion has rank one;
  `theorem/Stochastic/ControlledAction.lean` defines the quasi-potential for such degenerate noise
  and `theorem/GridTiedConverter/GFM/Noise/FilterQuasiPotential.lean` bounds this one from
  below by the two-state value `2D ΔU/σ_P²` with `D` replaced by `D − A/ω_c` (a Hamilton–Jacobi
  subsolution) and shows that the exact two-state solution has no separable three-state extension;
  `theorem/GridTiedConverter/GFM/Noise/EscapeExponent.lean` proves that it tends to the two-state
  value as `ω_c → ∞`. The large-deviation principle of the noisy models is proved
  (`GFM.Noise.Params3.isLDP_setPoint`), the quasi-potential of its rate equals this exponent
  (`GFM.Noise.Params3.fwQP_eq_setPointQP`) and the mean exit time from a compact set obeys the
  Freidlin–Wentzell upper bound (`GFM.Noise.Params3.limsup_log_exitTime_le`); from the sublevel
  wells of the filter-lag function the mean exit time is bounded below at the Hamilton–Jacobi
  rate (`GFM.Noise.Params3.le_liminf_log_exitTime_filterWell`, `A < D ω_c`); the matching value
  at the saddle, the exit place and the exponential law of `τ/E τ` are not formalized, and no
  closed form at finite `ω_c` is known. "No closed form"
  describes the state of knowledge; it is not a theorem.
* Two-state stationary states: positive differentiable densities on `Fin 2 → ℝ` in the
  coordinates `(δ − α, M Δω)` of `Params.genDetailedBalance_gibbs`, nominal damping, any noise
  intensities; "on the circle" means `2π`-periodic in the angle. Existence of a stationary
  density on the circle (a hypoelliptic problem) is not formalized.

Source: GFM counterpart study, note t2-noise items 6 and 7 (no constant-structure pH form,
broken equipartition, Monte-Carlo rates departing from the two-state Kramers–Langer rate as
`ω_c` decreases; scratch notes outside the repository); C. W. Gardiner, *Handbook of Stochastic
Methods* (3rd ed., 2004), §5.3.5; H. Risken, *The Fokker–Planck Equation* (2nd ed., 1989), §6.4;
J. S. Langer, Ann. Phys. 54 (1969) 258 (prefactor from the unstable eigenvalue of the saddle
linearization, for a Gibbs stationary density); Hänggi, Talkner, Borkovec, Rev. Mod. Phys. 62
(1990) 251, §IV–§V (detailed balance as the hypothesis of the Kramers–Langer rate; non-equilibrium
escape); M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 (quasi-potential, exit problem); the two-state counterpart
`theorem/GridTiedConverter/GFM/Noise/Escape.lean`.

Results.
* `not_genDetailedBalance_of_noiselessFilter`: without voltage noise (`σ_d = σ_q = 0`, any
  `σ_P`, `σ_g`, `κ`), for every parity and every positive function, no generalized detailed
  balance: the filter row is noiseless, so its irreversible drift
  `½ ω_c (P(δ) + ε₂ P(ε₀ δ) − 2 P_f)` would vanish identically
  (`Stochastic.DetailedBalance.irrDrift_eq_zero_of_noiseless`).
* `not_detailedBalance`: for every `σ` and `κ`, no positive differentiable density has zero
  probability current.
* `not_genDetailedBalance_momentumFlip`: for every `σ` and `κ`, no positive differentiable
  density satisfies generalized detailed balance under the momentum flip: the filter row and
  stationarity alone are contradictory (they force a constant filter noise and then
  `P''(δ) = −A sin(δ − α) ≡ 0`).
* `Params.genDetailedBalance_gibbs` (contrast): the two-state model in `(δ − α, M Δω)`, without
  frequency noise, with isotropic voltage noise and `σ_P² + k² σ_q² = 2 D T`, satisfies
  generalized detailed balance under the momentum flip with `e^{−H/T}`
  (`Stochastic.DetailedBalance.kk_genDetailedBalance`).
* `Params.eq_gibbs_of_genDetailedBalance` (converse, `D > 0`): a positive differentiable
  density in generalized detailed balance under the momentum flip exists only without
  grid-frequency noise and with isotropic voltage noise, and it is the Gibbs density
  `ρ(0, 0) e^{V(0)/T} e^{−H/T}`, `T = (σ_P² + k² σ_q²)/(2D)`
  (`Stochastic.DetailedBalance.eq_gibbs_of_kk_genDetailedBalance`).
* `Params.not_genDetailedBalance_of_periodic` (**non-Gibbs stationary states**): for `D > 0` and
  `P_ref ≠ c₀` no positive differentiable density on the circle satisfies generalized detailed
  balance under the momentum flip, for any noise: a stationary density on the circle, if any,
  carries an irreversible probability current; the Kramers–Langer rate does not apply.
* `not_exists_constPH`: for `D > 0` the drift is `(J − R)∇H` for no constant `J`, `R ⪰ 0` and
  no `H` (`VSMLPF.not_exists_constPH` through `VSMLPFLossy.field_eq`); `exists_constPH_iff`: such
  a form (without ports) exists iff `D = 0`. With the non-Gibbs result
  `Params3.maxwellian_not_stationary` of `FilterEscape`.
* `saddle_eigenvalue`: at `cos(δ − α) < 0` (`κ_b = −A cos(δ − α)`) the Jacobian of the field has
  exactly one eigenvalue outside the open left half plane, a real `ℓ > 0`, with
  `0 < λ₊ − ℓ < κ_b/(M ω_c)`, `λ₊ = kkLambda M D κ_b` the unstable eigenvalue of the two-state
  saddle (`GFM.Noise.Params.langer_eigen`): the two-state Langer eigenvalue is not the saddle
  eigenvalue of the three-state model at any finite `ω_c`; the gap is below `κ_b/(M ω_c)`.
* `fpOp_setPoint`: with set-point noise the divergence-form operator is `Params3.fpOp`.
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Matrix
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two)
open powerlib.Stochastic.DetailedBalance

namespace Params3

variable (p : Params3)

/-! ## The diffusion on `Fin 3 → ℝ` -/

/-- Drift of the noisy three-state model at a state `x = (δ, ω, P_f)`: the undisturbed lossy
field `GFM.VSMLPFLossy.field` (the Itô and Stratonovich drifts coincide, `strat_eq_zero`). -/
def sdeDrift (x : Fin 3 → ℝ) : Fin 3 → ℝ := WithLp.ofLp (p.toLossy.field (WithLp.toLp 2 x))

/-- Diffusion matrix `h hᵀ` of the noisy three-state model at a state, `h = B(δ) diag σ`
(`Params3.diffusion`), with the damping reference `κ` and the intensities
`σ = (σ_P, σ_g, σ_d, σ_q)` (`σ_g` the grid-frequency intensity). -/
def sdeDiffusion (κ : ℝ) (σ : Fin 4 → ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  p.diffusion κ σ (x 0) * (p.diffusion κ σ (x 0))ᵀ

/-- The momentum flip `(δ, ω, P_f) ↦ (δ, −ω, P_f)`: angle and filtered power even, frequency
odd. -/
def momentumFlip : Fin 3 → ℝ := ![1, -1, 1]

@[tmio M, powerlib_domain] theorem sdeDrift_apply (x : Fin 3 → ℝ) :
    p.sdeDrift x =
      ![x 1, (p.Pref - x 2 - p.D * x 1) / p.M, p.ωc * (p.toLossy.Pe (x 0) - x 2)] := by
  funext i; fin_cases i <;> simp [sdeDrift, VSMLPFLossy.field, toLossy]

@[tmio M, powerlib_domain] private lemma sdeDiffusion_apply (κ : ℝ) (σ : Fin 4 → ℝ)
    (x : Fin 3 → ℝ) :
    p.sdeDiffusion κ σ x =
      !![σ 1 ^ 2, -(κ * p.D * σ 1 ^ 2 / p.M), 0;
         -(κ * p.D * σ 1 ^ 2 / p.M), (σ 0 ^ 2 + κ ^ 2 * p.D ^ 2 * σ 1 ^ 2) / p.M ^ 2, 0;
         0, 0, p.ωc ^ 2 * p.k ^ 2 *
           (σ 2 ^ 2 * Real.sin (x 0 - p.α) ^ 2 + σ 3 ^ 2 * Real.cos (x 0 - p.α) ^ 2)] :=
  p.diffusion_mul_transpose κ σ (x 0)

/-- Every entry `(i, j)` is constant along the coordinate `j`, so the divergence terms of the
drift condition are `Σⱼ Bᵢⱼ(x) ∂ⱼρ(x)`. -/
@[tmio M, powerlib_domain] private lemma sum_pd (κ : ℝ) (σ : Fin 4 → ℝ) (ρ : (Fin 3 → ℝ) → ℝ)
    (x : Fin 3 → ℝ) (i : Fin 3) :
    ∑ j, pd (fun y => p.sdeDiffusion κ σ y i j * ρ y) j x =
      ∑ j, p.sdeDiffusion κ σ x i j * pd ρ j x := by
  refine Finset.sum_congr rfl fun j _ => pd_mul_of_update fun t => ?_
  rw [sdeDiffusion_apply, sdeDiffusion_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- The drift condition at `(δ, ω, P_f)` in coordinates. -/
@[tmio M, powerlib_domain] private lemma drift_vec {κ : ℝ} {σ : Fin 4 → ℝ} {ε : Fin 3 → ℝ}
    {ρ : (Fin 3 → ℝ) → ℝ} (h : GenDetailedBalance p.sdeDrift (p.sdeDiffusion κ σ) ε ρ)
    (δ ω z : ℝ) (i : Fin 3) :
    ε i * p.sdeDrift ![ε 0 * δ, ε 1 * ω, ε 2 * z] i * ρ ![δ, ω, z] =
      -(p.sdeDrift ![δ, ω, z] i * ρ ![δ, ω, z]) +
        ∑ j, p.sdeDiffusion κ σ ![δ, ω, z] i j * pd ρ j ![δ, ω, z] := by
  have e := h.drift ![δ, ω, z] i
  rw [sum_pd] at e
  convert e using 4
  funext j; fin_cases j <;> simp [reversal]

/-! ## Detailed balance and generalized detailed balance refuted -/

/-- **With the voltage channels off the filter coordinate is noiseless, and no parity is
reversible.** If `σ_d = σ_q = 0` (set-point and grid-frequency noise, any damping reference
`κ`), then for every parity `ε` (in particular `ε ≡ 1`, detailed balance, and the momentum flip)
and every positive function `ρ` (no regularity), generalized detailed balance fails: the
filtered-power row has no noise, so its irreversible drift
`½ ω_c (P(δ) + ε₂ P(ε₀ δ) − 2 P_f)` would vanish at every state
(`Stochastic.DetailedBalance.irrDrift_eq_zero_of_noiseless`), while the filter contraction
`−ω_c P_f` is even under every parity. -/
@[tmio M, powerlib_domain] theorem not_genDetailedBalance_of_noiselessFilter (κ : ℝ)
    {σ : Fin 4 → ℝ} (h2 : σ 2 = 0) (h3 : σ 3 = 0) (ε : Fin 3 → ℝ) (ρ : (Fin 3 → ℝ) → ℝ) :
    ¬ GenDetailedBalance p.sdeDrift (p.sdeDiffusion κ σ) ε ρ := by
  intro h
  have hB : ∀ y j, p.sdeDiffusion κ σ y 2 j = 0 := fun y j => by
    rw [sdeDiffusion_apply]; fin_cases j <;> simp [h2, h3]
  have hirr : ∀ x, irrDrift p.sdeDrift ε x 2 = 0 := fun x =>
    irrDrift_eq_zero_of_noiseless hB (h.pos x).ne' (h.drift x 2)
  have e0 := hirr ![0, 0, 0]
  have e1 := hirr ![0, 0, 1]
  simp only [irrDrift, sdeDrift_apply, reversal] at e0 e1
  simp at e0 e1
  have hε : ε 2 * ε 2 = 1 := by rcases h.parity 2 with h' | h' <;> rw [h'] <;> norm_num
  have hω := p.ωc_pos
  nlinarith

/-- The divergence terms of the three rows in coordinates. -/
@[tmio M, powerlib_domain] private lemma rows (κ : ℝ) (σ : Fin 4 → ℝ) (ρ : (Fin 3 → ℝ) → ℝ)
    (δ ω z : ℝ) :
    (∑ j, p.sdeDiffusion κ σ ![δ, ω, z] 0 j * pd ρ j ![δ, ω, z] =
      σ 1 ^ 2 * pd ρ 0 ![δ, ω, z] - κ * p.D * σ 1 ^ 2 / p.M * pd ρ 1 ![δ, ω, z]) ∧
    (∑ j, p.sdeDiffusion κ σ ![δ, ω, z] 1 j * pd ρ j ![δ, ω, z] =
      -(κ * p.D * σ 1 ^ 2 / p.M) * pd ρ 0 ![δ, ω, z] +
        (σ 0 ^ 2 + κ ^ 2 * p.D ^ 2 * σ 1 ^ 2) / p.M ^ 2 * pd ρ 1 ![δ, ω, z]) ∧
    (∑ j, p.sdeDiffusion κ σ ![δ, ω, z] 2 j * pd ρ j ![δ, ω, z] =
      p.ωc ^ 2 * p.k ^ 2 * (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 + σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) *
        pd ρ 2 ![δ, ω, z]) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sdeDiffusion_apply, Fin.sum_univ_three]
  ring

/-- **Not reversible: no positive differentiable density satisfies detailed balance** (parity
`ε ≡ 1`, zero probability current), for every noise intensity `σ = (σ_P, σ_g, σ_d, σ_q)` and
damping reference `κ`. Without grid-frequency noise the angle row has the drift `ω` and no
noise; otherwise the angle and frequency rows force `∂_ω log ρ` to depend on `P_f` with slope
`−2M/σ_P²` (or are inconsistent when `σ_P = 0`), while the filter row makes `∂_{P_f} log ρ`
independent of `ω`; the two slices `ω = 0, 1` (`Stochastic.DetailedBalance.slice_of_affine`) then
force the filter-row noise to vanish, where the filter drift contradicts the filter row. -/
@[tmio M, powerlib_domain] theorem not_detailedBalance (κ : ℝ) (σ : Fin 4 → ℝ)
    {ρ : (Fin 3 → ℝ) → ℝ} (hρ : Differentiable ℝ ρ) :
    ¬ GenDetailedBalance p.sdeDrift (p.sdeDiffusion κ σ) (fun _ => 1) ρ := by
  intro h
  have hM := p.M_pos
  have hω := p.ωc_pos
  set bf : ℝ → ℝ := fun δ => p.ωc ^ 2 * p.k ^ 2 *
    (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 + σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) with hbf
  have r0 : ∀ δ ω z, σ 1 ^ 2 * pd ρ 0 ![δ, ω, z] -
      κ * p.D * σ 1 ^ 2 / p.M * pd ρ 1 ![δ, ω, z] = 2 * ω * ρ ![δ, ω, z] := by
    intro δ ω z
    have e := p.drift_vec h δ ω z 0
    rw [(p.rows κ σ ρ δ ω z).1] at e
    simp [sdeDrift_apply] at e
    linarith
  have r1 : ∀ δ ω z, -(κ * p.D * σ 1 ^ 2 / p.M) * pd ρ 0 ![δ, ω, z] +
      (σ 0 ^ 2 + κ ^ 2 * p.D ^ 2 * σ 1 ^ 2) / p.M ^ 2 * pd ρ 1 ![δ, ω, z] =
        2 * ((p.Pref - z - p.D * ω) / p.M) * ρ ![δ, ω, z] := by
    intro δ ω z
    have e := p.drift_vec h δ ω z 1
    rw [(p.rows κ σ ρ δ ω z).2.1] at e
    simp [sdeDrift_apply] at e
    linarith
  have r2 : ∀ δ ω z, bf δ * pd ρ 2 ![δ, ω, z] =
      2 * (p.ωc * (p.toLossy.Pe δ - z)) * ρ ![δ, ω, z] := by
    intro δ ω z
    have e := p.drift_vec h δ ω z 2
    rw [(p.rows κ σ ρ δ ω z).2.2] at e
    simp [sdeDrift_apply] at e
    simp only [hbf]
    linarith
  by_cases hs1 : σ 1 = 0
  · have e := r0 0 1 0
    rw [hs1] at e
    simp only [zero_pow two_ne_zero, zero_mul, mul_zero, zero_div, sub_zero] at e
    have hp := h.pos ![0, 1, 0]
    have e' : 2 * ρ ![0, 1, 0] = 0 := by linarith
    linarith
  -- The angle and frequency rows give `(σ_P²/M²) ∂_ω ρ = (2/M)(P_ref − P_f − (1 − κ) D ω) ρ`.
  have hcomb : ∀ δ ω z, σ 1 ^ 2 * (σ 0 ^ 2 / p.M ^ 2 * pd ρ 1 ![δ, ω, z]) =
      σ 1 ^ 2 * (2 / p.M * (p.Pref - z - (1 - κ) * p.D * ω) * ρ ![δ, ω, z]) := fun δ ω z => by
    linear_combination σ 1 ^ 2 * r1 δ ω z + κ * p.D * σ 1 ^ 2 / p.M * r0 δ ω z
  have hs1' : σ 1 ^ 2 ≠ 0 := pow_ne_zero 2 hs1
  by_cases hs0 : σ 0 = 0
  · have e := mul_left_cancel₀ hs1' (hcomb 0 0 (p.Pref + 1))
    rw [hs0] at e
    simp only [zero_pow two_ne_zero, zero_mul, mul_zero, zero_div, sub_zero] at e
    have hp := h.pos ![0, 0, p.Pref + 1]
    have e' : 2 / p.M * ρ ![0, 0, p.Pref + 1] = 0 := by linarith
    have : 0 < 2 / p.M * ρ ![0, 0, p.Pref + 1] := by positivity
    linarith
  set c := 2 * p.M / σ 0 ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have h1 : ∀ δ ω z, pd ρ 1 ![δ, ω, z] =
      (2 * p.M / σ 0 ^ 2 * (p.Pref - (1 - κ) * p.D * ω) - c * z) * ρ ![δ, ω, z] := by
    intro δ ω z
    have e := mul_left_cancel₀ hs1' (hcomb δ ω z)
    have hq : σ 0 ^ 2 / p.M ^ 2 ≠ 0 := by positivity
    have e' : pd ρ 1 ![δ, ω, z] =
        2 / p.M * (p.Pref - z - (1 - κ) * p.D * ω) * ρ ![δ, ω, z] / (σ 0 ^ 2 / p.M ^ 2) := by
      rw [← e]; field_simp
    rw [e', hc]
    field_simp
    ring
  -- Slices `ω = 0, 1` at the angle `0`.
  have hd1 : ∀ z, Differentiable ℝ (fun t => ρ ![0, t, z]) := fun z => by
    simpa [update_vec3_one] using differentiable_comp_update hρ ![0, 0, z] 1
  have hd2 : ∀ ω, Differentiable ℝ (fun t => ρ ![0, ω, t]) := fun ω => by
    simpa [update_vec3_two] using differentiable_comp_update hρ ![0, ω, 0] 2
  have hr : ∀ t z, HasDerivAt (fun s => ρ ![0, s, z])
      ((2 * p.M / σ 0 ^ 2 * (p.Pref - (1 - κ) * p.D * t) - c * z) * ρ ![0, t, z]) t := by
    intro t z
    have hh := (hd1 z t).hasDerivAt
    rwa [← pd_vec3_one, h1] at hh
  have hC : ∀ t, HasDerivAt (fun t => 2 * p.M / σ 0 ^ 2 * (p.Pref * t - (1 - κ) * p.D * t ^ 2 / 2))
      (2 * p.M / σ 0 ^ 2 * (p.Pref - (1 - κ) * p.D * t)) t := by
    intro t
    have hh := (((hasDerivAt_id' t).const_mul p.Pref).sub
      (((hasDerivAt_pow 2 t).const_mul ((1 - κ) * p.D)).div_const 2)).const_mul
        (2 * p.M / σ 0 ^ 2)
    convert hh using 1
    push_cast
    ring
  obtain ⟨hv, hdv⟩ := slice_of_affine (r := fun t y => ρ ![0, t, y]) hC hr (t₁ := 0) (z := 0)
    (hd2 0 0) 1
  set E := exp (2 * p.M / σ 0 ^ 2 * (p.Pref * 1 - (1 - κ) * p.D * 1 ^ 2 / 2) -
    2 * p.M / σ 0 ^ 2 * (p.Pref * 0 - (1 - κ) * p.D * 0 ^ 2 / 2) - c * 0 * (1 - 0)) with hE
  have e1 := r2 0 1 0
  have e0 := r2 0 0 0
  rw [pd_vec3_two] at e1 e0
  rw [hdv, hv] at e1
  have key : bf 0 * c * (ρ ![0, 0, 0] * E) = 0 := by linear_combination (-1 : ℝ) * e1 + E * e0
  have hb0 : bf 0 = 0 := by
    have : 0 < c * (ρ ![0, 0, 0] * E) := by have := h.pos ![0, 0, 0]; positivity
    rw [mul_assoc] at key
    exact (mul_eq_zero.mp key).resolve_right this.ne'
  have e := r2 0 0 (p.toLossy.Pe 0 + 1)
  rw [hb0, zero_mul] at e
  have hp := h.pos ![0, 0, p.toLossy.Pe 0 + 1]
  have : 0 < p.ωc * ρ ![0, 0, p.toLossy.Pe 0 + 1] := by positivity
  linarith

/-- The core of the momentum-flip refutation: the filter row of the drift condition and the
divergence-free reversible current `(ω, (P_ref − P_f)/M, 0) ρ` have no common positive
differentiable solution. The filter row integrates in `P_f`
(`ρ = ρ|_{P_f = 0} e^{G}`, `G = 2 ω_c (P(δ) P_f − P_f²/2)/b(δ)`); the current condition at
`P_f = ±1` forces `b' = 0`, then `∂_ω log ρ = 2 K(δ) ω` with `K = M ω_c P'(δ)/b`, and the slices
`ω = 1, 2` force `K' = 0`, i.e. `P'' = −A sin(δ − α) = 0`. -/
@[tmio M, powerlib_domain] private lemma flip_core (σ : Fin 4 → ℝ) {r : ℝ → ℝ → ℝ → ℝ}
    (hpos : ∀ δ ω z, 0 < r δ ω z) (hdδ : ∀ ω z, Differentiable ℝ (fun t => r t ω z))
    (hdω : ∀ δ z, Differentiable ℝ (fun t => r δ t z))
    (hdz : ∀ δ ω, Differentiable ℝ (fun t => r δ ω t))
    (R2 : ∀ δ ω z, p.ωc ^ 2 * p.k ^ 2 *
      (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 + σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) *
        deriv (fun t => r δ ω t) z = 2 * (p.ωc * (p.toLossy.Pe δ - z)) * r δ ω z)
    (ST : ∀ δ ω z, ω * deriv (fun t => r t ω z) δ +
      (p.Pref - z) / p.M * deriv (fun t => r δ t z) ω = 0) : False := by
  have hM := p.M_pos
  have hω := p.ωc_pos
  have hA := p.A_pos
  set b : ℝ → ℝ := fun δ => p.ωc ^ 2 * p.k ^ 2 *
    (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 + σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) with hb
  set P : ℝ → ℝ := p.toLossy.Pe with hPdef
  have hPe : ∀ δ, P δ = p.c0 + p.A * Real.sin (δ - p.α) := fun δ => by
    simp [hPdef, VSMLPFLossy.Pe, toLossy]
  -- The filter noise is positive at every angle.
  have hbpos : ∀ δ, 0 < b δ := by
    intro δ
    rcases (show 0 ≤ b δ by simp only [hb]; positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      have e := R2 δ 0 (P δ + 1)
      rw [show p.ωc ^ 2 * p.k ^ 2 * (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 +
        σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) = b δ from rfl, ← h, zero_mul] at e
      have := hpos δ 0 (P δ + 1)
      have : 0 < p.ωc * r δ 0 (P δ + 1) := by positivity
      linarith
  -- Derivatives of `b` and `P`.
  set b' : ℝ → ℝ := fun δ => p.ωc ^ 2 * p.k ^ 2 *
    (σ 2 ^ 2 * (2 * Real.sin (δ - p.α) * Real.cos (δ - p.α)) +
      σ 3 ^ 2 * (2 * Real.cos (δ - p.α) * -Real.sin (δ - p.α))) with hb'
  have hbd : ∀ δ, HasDerivAt b (b' δ) δ := by
    intro δ
    have hs := ((hasDerivAt_id' δ).sub_const p.α).sin
    have hc := ((hasDerivAt_id' δ).sub_const p.α).cos
    have h := (((hs.pow 2).const_mul (σ 2 ^ 2)).add ((hc.pow 2).const_mul (σ 3 ^ 2))).const_mul
      (p.ωc ^ 2 * p.k ^ 2)
    convert h using 1
    simp only [hb']
    push_cast
    ring
  have hPd : ∀ δ, HasDerivAt P (p.A * Real.cos (δ - p.α)) δ := by
    intro δ
    have h := ((((hasDerivAt_id' δ).sub_const p.α).sin).const_mul p.A).const_add p.c0
    convert h using 1
    · funext t; simp [hPe]
    · ring
  -- The `P_f`-integral of the filter row.
  set G : ℝ → ℝ → ℝ := fun δ z => 2 * p.ωc * (P δ * z - z ^ 2 / 2) / b δ with hG
  set Gd : ℝ → ℝ → ℝ := fun δ z => (2 * p.ωc * (p.A * Real.cos (δ - p.α) * z) * b δ -
    2 * p.ωc * (P δ * z - z ^ 2 / 2) * b' δ) / b δ ^ 2 with hGd
  have hGδ : ∀ δ z, HasDerivAt (fun t => G t z) (Gd δ z) δ := by
    intro δ z
    have h := (((hPd δ).mul_const z).sub_const (z ^ 2 / 2)).const_mul (2 * p.ωc)
    exact h.fun_div (hbd δ) (hbpos δ).ne'
  have hrep : ∀ δ ω z, r δ ω z = r δ ω 0 * exp (G δ z) := by
    intro δ ω z
    have hf : ∀ t, HasDerivAt (fun t => r δ ω t) (2 * p.ωc * (P δ - t) / b δ * r δ ω t) t := by
      intro t
      have hh := (hdz δ ω t).hasDerivAt
      have e := R2 δ ω t
      have e' : b δ * deriv (fun t => r δ ω t) t = 2 * (p.ωc * (P δ - t)) * r δ ω t := e
      have hd : deriv (fun t => r δ ω t) t = 2 * p.ωc * (P δ - t) / b δ * r δ ω t := by
        rw [div_mul_eq_mul_div, eq_div_iff (hbpos δ).ne']
        linarith
      rwa [hd] at hh
    have hC : ∀ t, HasDerivAt (fun t => G δ t) (2 * p.ωc * (P δ - t) / b δ) t := by
      intro t
      have h := ((((hasDerivAt_id' t).const_mul (P δ)).sub
        ((hasDerivAt_pow 2 t).div_const 2)).const_mul (2 * p.ωc)).div_const (b δ)
      convert h using 1
      push_cast
      ring
    have e := eq_mul_exp_of_hasDerivAt hf hC 0 z
    simpa [hG] using e
  -- The `ω`- and `δ`-derivatives of the representation.
  have hω' : ∀ δ ω z, deriv (fun t => r δ t z) ω = deriv (fun t => r δ t 0) ω * exp (G δ z) := by
    intro δ ω z
    rw [show (fun t => r δ t z) = fun t => r δ t 0 * exp (G δ z) from
      funext fun t => hrep δ t z]
    exact deriv_mul_const_field _
  have hδ' : ∀ δ ω z, deriv (fun t => r t ω z) δ =
      (deriv (fun t => r t ω 0) δ + r δ ω 0 * Gd δ z) * exp (G δ z) := by
    intro δ ω z
    have hd : HasDerivAt (fun t => r t ω 0 * exp (G t z))
        (deriv (fun t => r t ω 0) δ * exp (G δ z) + r δ ω 0 * (exp (G δ z) * Gd δ z)) δ :=
      (hdδ ω 0 δ).hasDerivAt.mul (hGδ δ z).exp
    rw [show (fun t => r t ω z) = fun t => r t ω 0 * exp (G t z) from
      funext fun t => hrep t ω z, hd.deriv]
    ring
  -- The current condition at `P_f` minus that at `P_f = 0`.
  have hdia : ∀ δ ω z, ω * r δ ω 0 * Gd δ z = z / p.M * deriv (fun t => r δ t 0) ω := by
    intro δ ω z
    have e1 := ST δ ω z
    have e0 := ST δ ω 0
    rw [hδ', hω'] at e1
    have e1' : ω * deriv (fun t => r t ω 0) δ + ω * r δ ω 0 * Gd δ z +
        (p.Pref - z) / p.M * deriv (fun t => r δ t 0) ω = 0 := by
      have h : (ω * deriv (fun t => r t ω 0) δ + ω * r δ ω 0 * Gd δ z +
          (p.Pref - z) / p.M * deriv (fun t => r δ t 0) ω) * exp (G δ z) = 0 := by
        linear_combination e1
      exact (mul_eq_zero.mp h).resolve_right (exp_pos _).ne'
    linear_combination e1' - e0
  -- `P_f = ±1`: the filter noise is constant.
  have hb'0 : ∀ δ, b' δ = 0 := by
    intro δ
    have hsum : r δ 1 0 * (Gd δ 1 + Gd δ (-1)) = 0 := by
      linear_combination hdia δ 1 1 + hdia δ 1 (-1)
    have hGsum : Gd δ 1 + Gd δ (-1) = 2 * p.ωc * b' δ / b δ ^ 2 := by
      simp only [hGd]
      ring
    rw [hGsum] at hsum
    have h := (mul_eq_zero.mp hsum).resolve_left (hpos δ 1 0).ne'
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by positivity)
    · exact absurd h (pow_ne_zero 2 (hbpos δ).ne')
  have hbc : ∀ δ, b δ = b 0 := fun δ =>
    is_const_of_deriv_eq_zero (fun t => (hbd t).differentiableAt)
      (fun t => by rw [(hbd t).deriv, hb'0]) δ 0
  -- `∂_ω ρ = 2 K(δ) ω ρ` at `P_f = 0`, `K = M ω_c P'(δ)/b`.
  set K : ℝ → ℝ := fun δ => p.M * p.ωc * (p.A * Real.cos (δ - p.α)) / b 0 with hK
  have hωK : ∀ δ ω, deriv (fun t => r δ t 0) ω = 2 * K δ * ω * r δ ω 0 := by
    intro δ ω
    have e := hdia δ ω 1
    have hGd1 : Gd δ 1 = 2 * p.ωc * (p.A * Real.cos (δ - p.α)) / b 0 := by
      have hb0 := (hbpos 0).ne'
      simp only [hGd, hb'0, hbc δ]
      field_simp
      ring
    rw [hGd1] at e
    have h : deriv (fun t => r δ t 0) ω =
        p.M * (ω * r δ ω 0 * (2 * p.ωc * (p.A * Real.cos (δ - p.α)) / b 0)) := by
      rw [e]; field_simp
    rw [h, hK]
    ring
  have hrepω : ∀ δ ω, r δ ω 0 = r δ 0 0 * exp (K δ * ω ^ 2) := by
    intro δ ω
    have hf : ∀ t, HasDerivAt (fun t => r δ t 0) (2 * K δ * t * r δ t 0) t := fun t => by
      have hh := (hdω δ 0 t).hasDerivAt
      rwa [hωK] at hh
    have hC : ∀ t, HasDerivAt (fun t => K δ * t ^ 2) (2 * K δ * t) t := fun t => by
      have h := (hasDerivAt_pow 2 t).const_mul (K δ)
      convert h using 1
      push_cast
      ring
    have e := eq_mul_exp_of_hasDerivAt hf hC 0 ω
    simpa using e
  -- `∂_δ ρ` at `P_f = 0`, `ω ≠ 0`, from the current condition.
  have hδ0 : ∀ δ ω, ω ≠ 0 →
      deriv (fun t => r t ω 0) δ = -(2 * p.Pref * K δ / p.M) * r δ ω 0 := by
    intro δ ω hω0
    have e := ST δ ω 0
    rw [hωK] at e
    apply mul_left_cancel₀ hω0
    linear_combination e
  -- The same derivative from the representation, through `K'`.
  set K' : ℝ → ℝ := fun δ => p.M * p.ωc * (p.A * -Real.sin (δ - p.α)) / b 0 with hK'
  have hKd : ∀ δ, HasDerivAt K (K' δ) δ := by
    intro δ
    have h := (((((hasDerivAt_id' δ).sub_const p.α).cos).const_mul p.A).const_mul
      (p.M * p.ωc)).div_const (b 0)
    convert h using 1
    simp only [hK']
    ring
  have hprod : ∀ δ ω, deriv (fun t => r t ω 0) δ =
      (deriv (fun t => r t 0 0) δ + r δ 0 0 * (K' δ * ω ^ 2)) * exp (K δ * ω ^ 2) := by
    intro δ ω
    have hd : HasDerivAt (fun t => r t 0 0 * exp (K t * ω ^ 2))
        (deriv (fun t => r t 0 0) δ * exp (K δ * ω ^ 2) +
          r δ 0 0 * (exp (K δ * ω ^ 2) * (K' δ * ω ^ 2))) δ :=
      (hdδ 0 0 δ).hasDerivAt.mul ((hKd δ).mul_const (ω ^ 2)).exp
    rw [show (fun t => r t ω 0) = fun t => r t 0 0 * exp (K t * ω ^ 2) from
      funext fun t => hrepω t ω, hd.deriv]
    ring
  -- `ω = 1, 2` at `δ = α + π/2`: `K' = 0`, while `K' = −M ω_c A/b < 0` there.
  set δ₀ := p.α + π / 2
  have hslice : ∀ ω, ω ≠ 0 → deriv (fun t => r t 0 0) δ₀ + r δ₀ 0 0 * (K' δ₀ * ω ^ 2) =
      -(2 * p.Pref * K δ₀ / p.M) * r δ₀ 0 0 := by
    intro ω hω0
    have e : (deriv (fun t => r t 0 0) δ₀ + r δ₀ 0 0 * (K' δ₀ * ω ^ 2)) * exp (K δ₀ * ω ^ 2) =
        (-(2 * p.Pref * K δ₀ / p.M) * r δ₀ 0 0) * exp (K δ₀ * ω ^ 2) := by
      rw [← hprod, hδ0 δ₀ ω hω0, hrepω δ₀ ω]
      ring
    exact mul_right_cancel₀ (exp_pos _).ne' e
  have h3 : r δ₀ 0 0 * K' δ₀ * 3 = 0 := by
    linear_combination hslice 2 two_ne_zero - hslice 1 one_ne_zero
  have hK'0 : K' δ₀ < 0 := by
    have hs : Real.sin (δ₀ - p.α) = 1 := by simp [δ₀]
    simp only [hK', hs]
    have := hbpos 0
    have : 0 < p.M * p.ωc * p.A / b 0 := by positivity
    linarith [show p.M * p.ωc * (p.A * -1) / b 0 = -(p.M * p.ωc * p.A / b 0) by ring]
  have := hpos δ₀ 0 0
  nlinarith

/-- **Not reversible up to the momentum flip**: for every noise intensity
`σ = (σ_P, σ_g, σ_d, σ_q)` and damping reference `κ`, no positive differentiable density
satisfies generalized detailed balance under `(δ, ω, P_f) ↦ (δ, −ω, P_f)`. Its filter row and its
stationarity, the divergence-free reversible current `(ω, (P_ref − P_f)/M, 0) ρ`
(`Stochastic.DetailedBalance.fpOp_eq_of_drift`), already contradict each other: a solution would
make the filter noise constant and then force `P''(δ) = −A sin(δ − α) ≡ 0`. -/
@[tmio M, powerlib_domain] theorem not_genDetailedBalance_momentumFlip (κ : ℝ) (σ : Fin 4 → ℝ)
    {ρ : (Fin 3 → ℝ) → ℝ} (hρ : Differentiable ℝ ρ) :
    ¬ GenDetailedBalance p.sdeDrift (p.sdeDiffusion κ σ) momentumFlip ρ := by
  intro h
  have r2 : ∀ δ ω z, p.ωc ^ 2 * p.k ^ 2 *
      (σ 2 ^ 2 * Real.sin (δ - p.α) ^ 2 + σ 3 ^ 2 * Real.cos (δ - p.α) ^ 2) *
        deriv (fun t => ρ ![δ, ω, t]) z = 2 * (p.ωc * (p.toLossy.Pe δ - z)) * ρ ![δ, ω, z] := by
    intro δ ω z
    have e := p.drift_vec h δ ω z 2
    rw [(p.rows κ σ ρ δ ω z).2.2, pd_vec3_two] at e
    simp [sdeDrift_apply, momentumFlip] at e
    linarith
  -- Stationarity: the reversible current `(ω, (P_ref − P_f)/M, 0) ρ` is divergence free.
  have hst : ∀ δ ω z, ω * deriv (fun t => ρ ![t, ω, z]) δ +
      (p.Pref - z) / p.M * deriv (fun t => ρ ![δ, t, z]) ω = 0 := by
    intro δ ω z
    have e := h.stationary ![δ, ω, z]
    rw [fpOp_eq_of_drift h.drift, Fin.sum_univ_three] at e
    have q0 : (fun y => revDrift p.sdeDrift momentumFlip y 0 * ρ y) = fun y => y 1 * ρ y := by
      funext y; congr 1; simp [revDrift, sdeDrift_apply, momentumFlip, reversal]
    have q1 : (fun y => revDrift p.sdeDrift momentumFlip y 1 * ρ y) =
        fun y => (p.Pref - y 2) / p.M * ρ y := by
      funext y; congr 1; simp [revDrift, sdeDrift_apply, momentumFlip, reversal]; ring
    have q2 : (fun y => revDrift p.sdeDrift momentumFlip y 2 * ρ y) = fun y => 0 * ρ y := by
      funext y; congr 1; simp [revDrift, sdeDrift_apply, momentumFlip, reversal]
    rw [q0, q1, q2, pd_mul_of_update (a := fun y => y 1) (j := 0) (x := ![δ, ω, z])
      (fun t => by simp), pd_mul_of_update (a := fun y => (p.Pref - y 2) / p.M)
      (j := 1) (x := ![δ, ω, z]) (fun t => by simp),
      pd_mul_of_update (a := fun _ => (0 : ℝ)) (j := 2) (x := ![δ, ω, z]) (fun t => rfl),
      pd_vec3_zero, pd_vec3_one] at e
    simp at e
    linarith
  refine p.flip_core σ (r := fun δ ω z => ρ ![δ, ω, z]) (fun δ ω z => h.pos _) (fun ω z => ?_)
    (fun δ z => ?_) (fun δ ω => ?_) r2 hst
  · simpa [update_vec3_zero] using differentiable_comp_update hρ ![0, ω, z] 0
  · simpa [update_vec3_one] using differentiable_comp_update hρ ![δ, 0, z] 1
  · simpa [update_vec3_two] using differentiable_comp_update hρ ![δ, ω, 0] 2

/-! ## No constant-structure port-Hamiltonian drift -/

/-- **No constant port-Hamiltonian structure** of the noisy model's drift: for `D > 0` no
nonlinear pH model with constant `J` and `R ⪰ 0` (any Hamiltonian, any ports) has the lossy
three-state field as its zero-input field. The lossless refutation `VSMLPF.not_exists_constPH`,
read through the translation `VSMLPFLossy.field_eq` (`PH.NonlinearModel.shift`). -/
@[tmio M, powerlib_domain] theorem not_exists_constPH (hD : 0 < p.D) {m : ℕ} :
    ¬ ∃ P : PH.NonlinearModel 3 m, (∀ x, P.J x = P.J 0) ∧ (∀ x, P.R x = P.R 0) ∧
      P.zeroInputField = p.toLossy.field := by
  rintro ⟨P, hJ, hR, hf⟩
  refine p.toLossy.toVSMLPF.not_exists_constPH p.M_pos (mul_pos hD p.ωc_pos) p.A_pos.ne'
    ⟨P.shift p.toLossy.offset, fun x => ?_, fun x => ?_, ?_⟩
  · change P.J (x + p.toLossy.offset) = P.J (0 + p.toLossy.offset)
    rw [hJ, hJ (0 + _)]
  · change P.R (x + p.toLossy.offset) = P.R (0 + p.toLossy.offset)
    rw [hR, hR (0 + _)]
  · rw [PH.NonlinearModel.shift_zeroInputField, hf]
    funext z
    rw [VSMLPFLossy.field_eq, add_sub_cancel_right]

/-- **The damping hypothesis is sharp**: a constant-structure port-Hamiltonian form of the drift
(no ports) exists iff `D = 0` (then with an indefinite Hamiltonian,
`VSMLPF.exists_constPH_of_D_eq_zero`, translated by `VSMLPFLossy.field_eq`). -/
@[tmio M, powerlib_domain] theorem exists_constPH_iff :
    (∃ P : PH.NonlinearModel 3 0, (∀ x, P.J x = P.J 0) ∧ (∀ x, P.R x = P.R 0) ∧
      P.zeroInputField = p.toLossy.field) ↔ p.D = 0 := by
  constructor
  · intro h
    by_contra hD
    exact p.not_exists_constPH (lt_of_le_of_ne p.D_nonneg (Ne.symm hD)) h
  · intro hD
    obtain ⟨P, hJ, hR, hf⟩ := p.toLossy.toVSMLPF.exists_constPH_of_D_eq_zero hD p.M_pos
    refine ⟨P.shift (-p.toLossy.offset), fun x => ?_, fun x => ?_, ?_⟩
    · change P.J (x + -p.toLossy.offset) = P.J (0 + -p.toLossy.offset)
      rw [hJ, hJ (0 + _)]
    · change P.R (x + -p.toLossy.offset) = P.R (0 + -p.toLossy.offset)
      rw [hR, hR (0 + _)]
    · rw [PH.NonlinearModel.shift_zeroInputField, hf]
      funext z
      rw [VSMLPFLossy.field_eq, sub_eq_add_neg]

/-! ## The saddle linearization -/

open powerlib.Stochastic.KleinKramers (kkLambda kkLambda_quadratic)

/-- **Index-one saddle with a slower unstable eigenvalue than the two-state saddle.** At an
angle with `cos(δ − α) < 0` (`κ_b = −A cos(δ − α) > 0`) the Jacobian of the lossy field
(`VSMLPFLossy.hasFDerivAt_field`: the lossless Jacobian at `δ − α`) has exactly one eigenvalue
outside the open left half plane, a real `ℓ > 0`, and `0 < λ₊ − ℓ < κ_b/(M ω_c)`, where
`λ₊ = kkLambda M D κ_b` is the unstable eigenvalue of the two-state saddle
(`GFM.Noise.Params.langer_eigen`), whose ratio to `ω_b = √(κ_b/M)` is Langer's factor
(`GFM.Noise.Params.langer_factor`). The two-state value is reached only as `ω_c → ∞`. -/
@[tmio M, powerlib_domain] theorem saddle_eigenvalue {δ : ℝ} (hc : Real.cos (δ - p.α) < 0) :
    ∃ ℓ : ℝ, 0 < ℓ ∧
      (Linear.characteristicMatrix (p.toLossy.toVSMLPF.jacobian (δ - p.α)) (ℓ : ℂ)).det = 0 ∧
      (∀ s : ℂ, (Linear.characteristicMatrix (p.toLossy.toVSMLPF.jacobian (δ - p.α)) s).det = 0 →
        s = ℓ ∨ s.re < 0) ∧
      0 < kkLambda p.M p.D (-(p.A * Real.cos (δ - p.α))) - ℓ ∧
      kkLambda p.M p.D (-(p.A * Real.cos (δ - p.α))) - ℓ <
        -(p.A * Real.cos (δ - p.α)) / (p.M * p.ωc) := by
  have hM := p.M_pos
  have hω := p.ωc_pos
  have hD := p.D_nonneg
  have hκ : 0 < -(p.A * Real.cos (δ - p.α)) := by nlinarith [p.A_pos]
  have hdet : ∀ s : ℂ,
      (Linear.characteristicMatrix (p.toLossy.toVSMLPF.jacobian (δ - p.α)) s).det =
        s ^ 3 + ((p.D / p.M + p.ωc : ℝ) : ℂ) * s ^ 2 + ((p.D * p.ωc / p.M : ℝ) : ℂ) * s +
          ((-(-(p.A * Real.cos (δ - p.α)) * p.ωc / p.M) : ℝ) : ℂ) := fun s => by
    rw [Criteria.det_characteristicMatrix_fin_three', VSMLPF.trace_jacobian,
      VSMLPF.principalMinorSum_jacobian, VSMLPF.det_jacobian]
    simp only [VSMLPFLossy.toVSMLPF, toLossy]
    push_cast
    ring
  generalize -(p.A * Real.cos (δ - p.α)) = κb at hκ hdet ⊢
  have ha0 : -(κb * p.ωc / p.M) < 0 := by
    have : 0 < κb * p.ωc / p.M := by positivity
    linarith
  obtain ⟨ℓ, hℓ, hroot⟩ := Criteria.exists_cubic_root_pos_of_const_neg
    (a2 := p.D / p.M + p.ωc) (a1 := p.D * p.ωc / p.M) ha0
  refine ⟨ℓ, hℓ, by rw [hdet]; exact Criteria.cubic_real_root_complex hroot, ?_, ?_⟩
  · intro s hs
    rw [hdet, Criteria.cubic_factor_of_root hroot] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      refine (Criteria.quadratic_roots_re_neg_iff _ _).mpr ⟨by positivity, by positivity⟩ s h
  · have hq := kkLambda_quadratic (M := p.M) (D := p.D) (κ := κb) hM.ne' (by positivity)
    have hlam : 0 < kkLambda p.M p.D κb := by
      have h1 : √(p.D ^ 2 / (4 * p.M ^ 2)) = p.D / (2 * p.M) := by
        rw [show p.D ^ 2 / (4 * p.M ^ 2) = (p.D / (2 * p.M)) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      have h2 : √(p.D ^ 2 / (4 * p.M ^ 2)) < √(p.D ^ 2 / (4 * p.M ^ 2) + κb / p.M) := by
        have : 0 < κb / p.M := by positivity
        exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
      rw [h1] at h2
      unfold kkLambda
      have : -p.D / (2 * p.M) = -(p.D / (2 * p.M)) := by ring
      linarith
    generalize kkLambda p.M p.D κb = lam at hq hlam ⊢
    have hMM : p.M * p.M⁻¹ = 1 := mul_inv_cancel₀ hM.ne'
    -- `(ℓ + ω_c)(λ₊ − ℓ)(M(ℓ + λ₊) + D) = κ_b ℓ`.
    have hid : (ℓ + p.ωc) * ((lam - ℓ) * (p.M * (ℓ + lam) + p.D)) = κb * ℓ := by
      linear_combination (ℓ + p.ωc) * hq - p.M * hroot +
        (p.D * ℓ ^ 2 + p.D * p.ωc * ℓ - κb * p.ωc) * hMM
    have hX : 0 < (ℓ + p.ωc) * (p.M * (ℓ + lam) + p.D) := by positivity
    have hpos : 0 < lam - ℓ := by
      by_contra hn
      push Not at hn
      have : (ℓ + p.ωc) * ((lam - ℓ) * (p.M * (ℓ + lam) + p.D)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonpos_of_nonneg hn (by positivity))
      nlinarith
    refine ⟨hpos, ?_⟩
    rw [lt_div_iff₀ (by positivity)]
    -- `(λ₊ − ℓ) M ω_c X = κ_b ℓ ω_c M < κ_b M X`, `X = (ℓ + ω_c)(M(ℓ + λ₊) + D)`.
    have hlt : p.M * ℓ * p.ωc < (ℓ + p.ωc) * (p.M * (ℓ + lam) + p.D) := by
      nlinarith [mul_pos hM hℓ, mul_pos hM hlam, mul_pos hℓ hlam]
    have : (lam - ℓ) * (p.M * p.ωc) * ((ℓ + p.ωc) * (p.M * (ℓ + lam) + p.D)) <
        κb * ((ℓ + p.ωc) * (p.M * (ℓ + lam) + p.D)) := by
      have e : (lam - ℓ) * (p.M * p.ωc) * ((ℓ + p.ωc) * (p.M * (ℓ + lam) + p.D)) =
          κb * (p.M * ℓ * p.ωc) := by linear_combination (p.M * p.ωc) * hid
      rw [e]
      exact mul_lt_mul_of_pos_left hlt hκ
    exact lt_of_mul_lt_mul_right this hX.le

/-! ## The operator of `FilterEscape` -/

/-- **The divergence-form operator is the operator of `GFM.Noise.Params3.fpOp`**: with set-point
noise alone (`σ = (σ_P, 0, 0, 0)`, any `κ`), at a point where `ρ` is differentiable and
`∂_ω ρ` is differentiable in `ω`, the stationary operator `Stochastic.DetailedBalance.fpOp` of
the noisy model equals the expanded operator of `FilterEscape`. -/
@[tmio M, powerlib_domain] theorem fpOp_setPoint (κ σP : ℝ) {ρ : (Fin 3 → ℝ) → ℝ}
    (hρ : Differentiable ℝ ρ) {δ ω z : ℝ}
    (h2 : DifferentiableAt ℝ (fun t => deriv (fun y => ρ ![δ, y, z]) t) ω) :
    Stochastic.DetailedBalance.fpOp p.sdeDrift (p.sdeDiffusion κ ![σP, 0, 0, 0]) ρ ![δ, ω, z] =
      p.fpOp σP (fun a b c => ρ ![a, b, c]) δ ω z := by
  have hB : ∀ y, p.sdeDiffusion κ ![σP, 0, 0, 0] y = !![0, 0, 0; 0, σP ^ 2 / p.M ^ 2, 0; 0, 0, 0] :=
    fun y => by rw [sdeDiffusion_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hJ : ∀ i, (fun y => current p.sdeDrift (p.sdeDiffusion κ ![σP, 0, 0, 0]) ρ y i) =
      fun y => p.sdeDrift y i * ρ y - ![0, σP ^ 2 / (2 * p.M ^ 2) * pd ρ 1 y, 0] i := by
    intro i; funext y
    simp only [current, hB, Fin.sum_univ_three]
    rw [pd_mul_of_update (a := fun _ => (!![0, 0, 0; 0, σP ^ 2 / p.M ^ 2, 0; 0, 0, 0] :
      Matrix (Fin 3) (Fin 3) ℝ) i 0) (fun _ => rfl),
      pd_mul_of_update (a := fun _ => (!![0, 0, 0; 0, σP ^ 2 / p.M ^ 2, 0; 0, 0, 0] :
      Matrix (Fin 3) (Fin 3) ℝ) i 1) (fun _ => rfl),
      pd_mul_of_update (a := fun _ => (!![0, 0, 0; 0, σP ^ 2 / p.M ^ 2, 0; 0, 0, 0] :
      Matrix (Fin 3) (Fin 3) ℝ) i 2) (fun _ => rfl)]
    fin_cases i <;> simp
    ring
  have hd1 : DifferentiableAt ℝ (fun t => p.sdeDrift ![δ, t, z] 1 * ρ ![δ, t, z]) ω := by
    have hc : DifferentiableAt ℝ (fun t => ρ ![δ, t, z]) ω := by
      simpa [update_vec3_one] using differentiable_comp_update hρ ![δ, 0, z] 1 ω
    simp only [sdeDrift_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have hl : DifferentiableAt ℝ (fun t : ℝ => (p.Pref - z - p.D * t) / p.M) ω := by fun_prop
    exact hl.mul hc
  unfold Stochastic.DetailedBalance.fpOp Params3.fpOp
  rw [Fin.sum_univ_three, hJ 0, hJ 1, hJ 2, pd_vec3_zero, pd_vec3_one, pd_vec3_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, sub_zero, pd_vec3_one]
  have hsub : deriv (fun t => p.sdeDrift ![δ, t, z] 1 * ρ ![δ, t, z] -
      σP ^ 2 / (2 * p.M ^ 2) * deriv (fun t => ρ ![δ, t, z]) t) ω =
        deriv (fun t => p.sdeDrift ![δ, t, z] 1 * ρ ![δ, t, z]) ω -
          σP ^ 2 / (2 * p.M ^ 2) * deriv (fun y => deriv (fun t => ρ ![δ, t, z]) y) ω :=
    (hd1.hasDerivAt.sub (h2.hasDerivAt.const_mul (σP ^ 2 / (2 * p.M ^ 2)))).deriv
  rw [hsub]
  have hm : ∀ a b c, p.sdeDrift ![a, b, c] = WithLp.ofLp (p.toLossy.field (mk3 a b c)) :=
    fun _ _ _ => rfl
  simp only [hm]
  ring

end Params3

/-! ## The two-state contrast -/

namespace Params

variable (p : Params)

open powerlib.Stochastic.KleinKramers (gibbs)

/-- **The two-state model is reversible up to the momentum flip under fluctuation–dissipation.**
In the shifted angle and the momentum `(θ, p)` of `GFM.Noise.Escape`, with nominal damping, no
grid-frequency noise (`σ_g = 0`), isotropic voltage noise (`σ_d² = σ_q²`) and
`σ_P² + k² σ_q² = 2 D T` (`T ≠ 0`), the classical-machine field and the diffusion matrix of
`Params.diffusion` at the angle `θ + α` satisfy generalized detailed balance under
`(θ, p) ↦ (θ, −p)` with the Gibbs density `e^{−H/T}`
(`Stochastic.DetailedBalance.kk_genDetailedBalance`, through `Params.kkDrift_eq_field` and
`Params.diffusion_eq_diag`): the hypothesis of the Kramers–Langer escape rate, which the
three-state model never satisfies (`Params3.not_genDetailedBalance_momentumFlip`). -/
@[tmio M, powerlib_domain] theorem genDetailedBalance_gibbs {σ : Fin 4 → ℝ} (h1 : σ 1 = 0)
    (h23 : σ 2 ^ 2 = σ 3 ^ 2) {T : ℝ} (hT : T ≠ 0)
    (hfdt : σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2 = 2 * p.D * T) :
    GenDetailedBalance
      (fun x => WithLp.ofLp ((Synchronous.classicalSM p.toSM).field (WithLp.toLp 2 x) 0))
      (fun x => p.diffusion 0 σ (x 0 + p.α) * (p.diffusion 0 σ (x 0 + p.α))ᵀ) kkFlip
      (fun x => gibbs p.potential p.M T (x 0) (x 1)) := by
  have hA : (fun x : Fin 2 → ℝ =>
      WithLp.ofLp ((Synchronous.classicalSM p.toSM).field (WithLp.toLp 2 x) 0)) =
        kkDrift p.M p.D p.potentialDeriv := by
    funext x
    have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
    rw [hx, ← p.kkDrift_eq_field]
    rfl
  have hB : (fun x : Fin 2 → ℝ => p.diffusion 0 σ (x 0 + p.α) * (p.diffusion 0 σ (x 0 + p.α))ᵀ) =
      kkDiffusion p.D T := by
    funext x
    rw [p.diffusion_eq_diag]
    have hsc := Real.sin_sq_add_cos_sq (x 0)
    ext i j; fin_cases i <;> fin_cases j <;> simp [kkDiffusion, momentumDiffusion, h1, h23]
    linear_combination hfdt + p.k ^ 2 * σ 3 ^ 2 * hsc
  rw [hA, hB]
  exact kk_genDetailedBalance p.hasDerivAt_potential p.M_pos.ne' hT

/-- **The generalized detailed-balance density of the two-state model is the Gibbs density.**
In the coordinates of `Params.genDetailedBalance_gibbs` (nominal damping, any noise intensities
`σ`), with `D > 0`, a positive differentiable density in generalized detailed balance under the
momentum flip forces no grid-frequency noise, isotropic voltage noise, a nonzero momentum
diffusion `σ_P² + k² σ_q²`, and `ρ = ρ(0, 0) e^{V(0)/T} e^{−H/T}` with
`T = (σ_P² + k² σ_q²)/(2D)` (`Stochastic.DetailedBalance.eq_gibbs_of_kk_genDetailedBalance`). -/
@[tmio M, powerlib_domain] theorem eq_gibbs_of_genDetailedBalance (hD : 0 < p.D)
    (σ : Fin 4 → ℝ) {ρ : (Fin 2 → ℝ) → ℝ} (hρ : Differentiable ℝ ρ)
    (h : GenDetailedBalance
      (fun x => WithLp.ofLp ((Synchronous.classicalSM p.toSM).field (WithLp.toLp 2 x) 0))
      (fun x => p.diffusion 0 σ (x 0 + p.α) * (p.diffusion 0 σ (x 0 + p.α))ᵀ) kkFlip ρ) :
    σ 1 = 0 ∧ σ 2 ^ 2 = σ 3 ^ 2 ∧ σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2 ≠ 0 ∧
      ∀ θ q, ρ ![θ, q] = ρ ![0, 0] *
        Real.exp (p.potential 0 / ((σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2) / (2 * p.D))) *
          gibbs p.potential p.M ((σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2) / (2 * p.D)) θ q := by
  have hA : (fun x : Fin 2 → ℝ =>
      WithLp.ofLp ((Synchronous.classicalSM p.toSM).field (WithLp.toLp 2 x) 0)) =
        kkDrift p.M p.D p.potentialDeriv := by
    funext x
    have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
    rw [hx, ← p.kkDrift_eq_field]
    rfl
  have hB : (fun x : Fin 2 → ℝ => p.diffusion 0 σ (x 0 + p.α) * (p.diffusion 0 σ (x 0 + p.α))ᵀ) =
      fun x => !![σ 1 ^ 2, 0; 0, p.momentumDiffusion σ (x 0)] := by
    funext x
    rw [p.diffusion_eq_diag]
  rw [hA, hB] at h
  obtain ⟨hs, ha, ha0, hρg⟩ := eq_gibbs_of_kk_genDetailedBalance p.hasDerivAt_potential
    p.M_pos.ne' hD.ne' hρ h
  have hm0 : p.momentumDiffusion σ 0 = σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2 := by
    simp [momentumDiffusion]
  have hσ1 : σ 1 = 0 := by
    rcases hs with hs | hs
    · exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hs
    · have h1 := hs (π / 2)
      have h2 := hs (-(π / 2))
      simp only [potentialDeriv, Real.sin_pi_div_two, Real.sin_neg] at h1 h2
      have hb : p.toSM.b = p.A := rfl
      have := p.A_pos
      rw [hb] at h1 h2
      linarith
  have hσ23 : σ 2 ^ 2 = σ 3 ^ 2 := by
    have h := ha (π / 2)
    rw [hm0] at h
    simp only [momentumDiffusion, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
    have hk := pow_ne_zero 2 p.k_pos.ne'
    have : p.k ^ 2 * (σ 2 ^ 2 - σ 3 ^ 2) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hk
    linarith
  refine ⟨hσ1, hσ23, hm0 ▸ ha0, fun θ q => ?_⟩
  rw [hρg θ q, hm0]

/-- **No density on the circle is in generalized detailed balance unless `P_ref = c₀`**: with
`D > 0` and `P_ref ≠ c₀`, for every noise intensity `σ` (nominal damping), no positive
differentiable density `2π`-periodic in the angle satisfies generalized detailed balance under
the momentum flip. The only candidate is the Gibbs density
(`Params.eq_gibbs_of_genDetailedBalance`), which is periodic only for `P_ref = c₀`
(`Params.gibbs_periodic_iff`): a stationary density on the circle, if any, carries an
irreversible probability current (it is not of Kramers–Langer type). -/
@[tmio M, powerlib_domain] theorem not_genDetailedBalance_of_periodic (hD : 0 < p.D)
    (hP : p.Pref ≠ p.c0) (σ : Fin 4 → ℝ) {ρ : (Fin 2 → ℝ) → ℝ} (hρ : Differentiable ℝ ρ)
    (hper : ∀ θ q, ρ ![θ + 2 * π, q] = ρ ![θ, q]) :
    ¬ GenDetailedBalance
      (fun x => WithLp.ofLp ((Synchronous.classicalSM p.toSM).field (WithLp.toLp 2 x) 0))
      (fun x => p.diffusion 0 σ (x 0 + p.α) * (p.diffusion 0 σ (x 0 + p.α))ᵀ) kkFlip ρ := by
  intro h
  obtain ⟨-, -, ha0, hρg⟩ := p.eq_gibbs_of_genDetailedBalance hD σ hρ h
  set T := (σ 0 ^ 2 + p.k ^ 2 * σ 3 ^ 2) / (2 * p.D) with hT
  have hT0 : T ≠ 0 := div_ne_zero ha0 (mul_ne_zero two_ne_zero hD.ne')
  have hc : 0 < ρ ![0, 0] * Real.exp (p.potential 0 / T) :=
    mul_pos (h.pos _) (Real.exp_pos _)
  refine hP ((p.gibbs_periodic_iff hT0).mp fun θ q => ?_)
  have e := hper θ q
  rw [hρg (θ + 2 * π) q, hρg θ q] at e
  exact mul_left_cancel₀ hc.ne' e

end Params

end powerlib.GFM.Noise
