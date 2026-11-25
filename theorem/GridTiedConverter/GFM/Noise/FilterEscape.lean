import dependencies.Mathlib
import theorem.Attributes
import theorem.GridTiedConverter.GFM.Noise.FilterEmbedding
import theorem.GridTiedConverter.GFM.Noise.Escape
import theorem.GridTiedConverter.GFM.Noise.NoiseLyapunov

/-! # The three-state GFM (VSM + power filter) has no Gibbs density in the swing energy

Domain module: the stationary Fokker–Planck operator of the three-state model of
`theorem/GridTiedConverter/GFM/Noise/FilterEmbedding.lean` with set-point noise, evaluated on
Gibbs functions whose energy is the swing kinetic energy plus an arbitrary function of the angle
and the filtered power. The two-state model has such a stationary density exactly under
fluctuation–dissipation (`GFM.Noise.Params.gibbs_stationary_iff`); the three-state model has
none, at any temperature and any noise intensity.

Model boundary.
* The undisturbed field is `GFM.VSMLPFLossy.field` of `GFM.Noise.Params3.toLossy`, state
  `(δ, ω, P_f)`: `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (c₀ + A sin(δ − α) − P_f)`
  (voltage source behind a lossy quasi-static line, export-positive power, per unit; `M, ω_c > 0`,
  `D ≥ 0`). Noise: the power set-point channel alone, column `(0, σ_P/M, 0)ᵀ`, diffusion matrix
  `diag(0, σ_P²/M², 0)` (`GFM.Noise.Params3.diffusion_mul_transpose` at `σ = (σ_P, 0, 0, 0)`).
* `Params3.fpOp` is the **differential operator**
  `L*ρ = −∂_δ(f₀ ρ) − ∂_ω(f₁ ρ) − ∂_{P_f}(f₂ ρ) + (σ_P²/(2M²)) ∂²_ω ρ` with the components `f_i`
  of the model field; that it governs the density of an Itô diffusion, and every statement about
  laws, expectations or escape times, is not formalized. The statements are pointwise identities.
* Excluded as in `GFM.Noise.FilterEmbedding`; the grid-frequency and voltage channels (their
  diffusion acts on the angle and the filtered power, where the energy below is arbitrary).

Source: GFM counterpart study, note t2-noise items 6 and 7 (three-state model: no
constant-structure port-Hamiltonian form, broken equipartition, escape rate without a closed form;
derived and checked symbolically and by Monte-Carlo, scratch notes outside the repository);
work-sync `theory/T-fokker-planck.md` §1.1, §1.4 (stationary Fokker–Planck operator, Gibbs form);
Hänggi, Talkner, Borkovec, Rev. Mod. Phys. 62 (1990) 251, §IV–§V (Langer's prefactor needs the
Gibbs density at the barrier; non-equilibrium escape); the two-state counterpart
`theorem/GridTiedConverter/GFM/Noise/Escape.lean`.

Results.
* `Params3.fpOp_maxwellian`: for `ρ = exp(−(M ω²/2 + W(δ, P_f))/T)` (`Params3.maxwellian`, `W`
  differentiable in `δ` and in `P_f` at the point), `L*ρ = ρ [D/M + ω_c + ω ∂_δW/T +
  (P_ref − P_f − D ω) ω/T + ω_c (P(δ) − P_f) ∂_{P_f}W/T + (σ_P²/(2M²))(M² ω²/T² − M/T)]`.
* `Params3.maxwellian_not_stationary`: at every angle, on the filter's slow set
  `P_f = P(δ)`, the Gibbs function of an energy `M ω²/2 + W(δ, P_f)` does not solve the
  stationary equation for all `ω`, whatever `W`, `T ≠ 0` and `σ_P`: the `ω²` coefficient forces
  fluctuation–dissipation `σ_P² = 2 D T`, which compensates the momentum damping `D/M` and leaves
  the filter contraction `ω_c > 0` uncompensated. In particular the two-state Gibbs density
  (`GFM.Noise.Params.gibbs_stationary_iff`) extended by any dependence on `P_f` is not stationary;
  at linear order this is the broken equipartition `GFM.Noise.VSM3.cov3Pref_omega_ne` of the
  unique Lyapunov solution `GFM.Noise.VSM3.cov3Pref` (the linear Gaussian approximation).
* Escape rate: "no closed form" is not a proposition; its exact replacements are in
  `theorem/GridTiedConverter/GFM/Noise/FilterReversibility.lean`. Langer's (Eyring–Kramers) rate
  presupposes generalized detailed balance, which the two-state model satisfies under
  fluctuation–dissipation (`GFM.Noise.Params.genDetailedBalance_gibbs`, prefactor
  `GFM.Noise.Params.langer_factor`); for the three-state model no positive differentiable density
  satisfies detailed balance or generalized detailed balance under the momentum flip, for any
  noise channel (`GFM.Noise.Params3.not_detailedBalance`,
  `GFM.Noise.Params3.not_genDetailedBalance_momentumFlip`), and its saddle eigenvalue lies
  strictly below the two-state one (`GFM.Noise.Params3.saddle_eigenvalue`). The law of the exit
  time is not formalized (only the upper bound for its mean,
  `GFM.Noise.Params3.limsup_log_exitTime_le`); its Freidlin–Wentzell exponent (the
  quasi-potential at the saddle) is bounded below in
  `theorem/GridTiedConverter/GFM/Noise/FilterQuasiPotential.lean`
  (`GFM.Noise.Params3.setPointQP_rest_ge`: the two-state value with `D` replaced by
  `D − A/ω_c`) and tends to the two-state value as `ω_c → ∞`
  (`GFM.Noise.Params.tendsto_setPointQP`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two)

namespace Params3

variable (p : Params3)

/-- Stationary Fokker–Planck operator of the three-state field with set-point noise of intensity
`σ_P` (diffusion matrix `diag(0, σ_P²/M², 0)`), on a function `ρ(δ, ω, P_f)`. -/
def fpOp (σP : ℝ) (ρ : ℝ → ℝ → ℝ → ℝ) (δ ω z : ℝ) : ℝ :=
  -deriv (fun x => p.toLossy.field (mk3 x ω z) 0 * ρ x ω z) δ -
    deriv (fun y => p.toLossy.field (mk3 δ y z) 1 * ρ δ y z) ω -
    deriv (fun y => p.toLossy.field (mk3 δ ω y) 2 * ρ δ ω y) z +
    σP ^ 2 / (2 * p.M ^ 2) * deriv (fun y => deriv (fun y' => ρ δ y' z) y) ω

/-- Gibbs function `exp(−(M ω²/2 + W(δ, P_f))/T)` of the swing kinetic energy plus an arbitrary
function `W` of the angle and the filtered power. -/
def maxwellian (W : ℝ → ℝ → ℝ) (T δ ω z : ℝ) : ℝ := exp (-(p.M * ω ^ 2 / 2 + W δ z) / T)

@[tmio M, powerlib_domain] private lemma maxwellian_hasDerivAt_δ {W : ℝ → ℝ → ℝ} {T δ ω z w0 : ℝ}
    (h0 : HasDerivAt (fun x => W x z) w0 δ) :
    HasDerivAt (fun x => p.maxwellian W T x ω z) (-w0 / T * p.maxwellian W T δ ω z) δ := by
  have hq : HasDerivAt (fun x => -(p.M * ω ^ 2 / 2 + W x z) / T) (-w0 / T) δ := by
    have := (h0.const_add (p.M * ω ^ 2 / 2)).neg.div_const T
    convert this using 1
  have h := hq.exp
  unfold maxwellian
  convert h using 1
  ring

@[tmio M, powerlib_domain] private lemma maxwellian_hasDerivAt_ω (W : ℝ → ℝ → ℝ) (T δ z y : ℝ) :
    HasDerivAt (fun y => p.maxwellian W T δ y z) (-(p.M * y / T) * p.maxwellian W T δ y z) y := by
  have hq : HasDerivAt (fun y : ℝ => p.M * y ^ 2 / 2 + W δ z) (p.M * y) y := by
    have := (((hasDerivAt_pow 2 y).const_mul p.M).div_const 2).add_const (W δ z)
    convert this using 1; push_cast; ring
  have hq' : HasDerivAt (fun y => -(p.M * y ^ 2 / 2 + W δ z) / T) (-(p.M * y) / T) y := by
    have := hq.neg.div_const T
    convert this using 1
  have h := hq'.exp
  unfold maxwellian
  convert h using 1
  ring

@[tmio M, powerlib_domain] private lemma maxwellian_hasDerivAt_z {W : ℝ → ℝ → ℝ} {T δ ω z w2 : ℝ}
    (h2 : HasDerivAt (fun y => W δ y) w2 z) :
    HasDerivAt (fun y => p.maxwellian W T δ ω y) (-w2 / T * p.maxwellian W T δ ω z) z := by
  have hq : HasDerivAt (fun y => -(p.M * ω ^ 2 / 2 + W δ y) / T) (-w2 / T) z := by
    have := (h2.const_add (p.M * ω ^ 2 / 2)).neg.div_const T
    convert this using 1
  have h := hq.exp
  unfold maxwellian
  convert h using 1
  ring

/-- **Fokker–Planck residual of the Maxwellian**: with `ρ = exp(−(M ω²/2 + W)/T)`,
`L*ρ = ρ [D/M + ω_c + ω ∂_δW/T + (P_ref − P_f − D ω) ω/T + ω_c (P(δ) − P_f) ∂_{P_f}W/T +
(σ_P²/(2M²))(M² ω²/T² − M/T)]`. -/
@[tmio M, powerlib_domain] theorem fpOp_maxwellian {W : ℝ → ℝ → ℝ} {T δ ω z w0 w2 : ℝ}
    (hT : T ≠ 0) (h0 : HasDerivAt (fun x => W x z) w0 δ)
    (h2 : HasDerivAt (fun y => W δ y) w2 z) (σP : ℝ) :
    p.fpOp σP (p.maxwellian W T) δ ω z = p.maxwellian W T δ ω z *
      (p.D / p.M + p.ωc + ω * w0 / T + (p.Pref - z - p.D * ω) * ω / T +
        p.ωc * (p.toLossy.Pe δ - z) * w2 / T +
        σP ^ 2 / (2 * p.M ^ 2) * (p.M ^ 2 * ω ^ 2 / T ^ 2 - p.M / T)) := by
  have hM := p.M_pos.ne'
  set ρ := p.maxwellian W T with hρ
  have f0 : (fun x => p.toLossy.field (mk3 x ω z) 0 * ρ x ω z) = fun x => ω * ρ x ω z := by
    funext x; simp [VSMLPFLossy.field]
  have f1 : (fun y => p.toLossy.field (mk3 δ y z) 1 * ρ δ y z) =
      fun y => (p.Pref - z - p.D * y) / p.M * ρ δ y z := by
    funext y; simp [VSMLPFLossy.field, toLossy]
  have f2 : (fun y => p.toLossy.field (mk3 δ ω y) 2 * ρ δ ω y) =
      fun y => p.ωc * (p.toLossy.Pe δ - y) * ρ δ ω y := by
    funext y; simp [VSMLPFLossy.field, toLossy]
  have d0 : deriv (fun x => ω * ρ x ω z) δ = ω * (-w0 / T * ρ δ ω z) :=
    ((p.maxwellian_hasDerivAt_δ (T := T) (ω := ω) h0).const_mul ω).deriv
  have d1 : deriv (fun y => (p.Pref - z - p.D * y) / p.M * ρ δ y z) ω =
      -(p.D / p.M) * ρ δ ω z + (p.Pref - z - p.D * ω) / p.M * (-(p.M * ω / T) * ρ δ ω z) := by
    have hl : HasDerivAt (fun y : ℝ => (p.Pref - z - p.D * y) / p.M) (-(p.D / p.M)) ω := by
      have := (((hasDerivAt_id ω).const_mul p.D).const_sub (p.Pref - z)).div_const p.M
      convert this using 1; simp; ring
    exact (hl.mul (p.maxwellian_hasDerivAt_ω W T δ z ω)).deriv
  have d2 : deriv (fun y => p.ωc * (p.toLossy.Pe δ - y) * ρ δ ω y) z =
      -p.ωc * ρ δ ω z + p.ωc * (p.toLossy.Pe δ - z) * (-w2 / T * ρ δ ω z) := by
    have hl : HasDerivAt (fun y : ℝ => p.ωc * (p.toLossy.Pe δ - y)) (-p.ωc) z := by
      have := ((hasDerivAt_id z).const_sub (p.toLossy.Pe δ)).const_mul p.ωc
      convert this using 1
      · rfl
      · ring
    exact (hl.mul (p.maxwellian_hasDerivAt_z (T := T) (ω := ω) h2)).deriv
  have dω : (fun y => deriv (fun y' => ρ δ y' z) y) =
      fun y => -(p.M * y / T) * ρ δ y z := by
    funext y; exact (p.maxwellian_hasDerivAt_ω W T δ z y).deriv
  have d3 : deriv (fun y => -(p.M * y / T) * ρ δ y z) ω =
      -(p.M / T) * ρ δ ω z + -(p.M * ω / T) * (-(p.M * ω / T) * ρ δ ω z) := by
    have hl : HasDerivAt (fun y : ℝ => -(p.M * y / T)) (-(p.M / T)) ω := by
      have := (hasDerivAt_id ω).const_mul (-(p.M / T))
      convert this using 1
      · funext y; simp only [id]; ring
      · ring
    exact (hl.mul (p.maxwellian_hasDerivAt_ω W T δ z ω)).deriv
  unfold fpOp
  rw [f0, f1, f2, dω, d0, d1, d2, d3]
  field_simp
  ring

/-- **No Gibbs density in the swing energy**: at every angle `δ`, on the slow set `P_f = P(δ)`,
the Gibbs function of `M ω²/2 + W(δ, P_f)` (`W` differentiable in each argument there) does not
solve the stationary Fokker–Planck equation for every `ω`, whatever `W`, `T ≠ 0` and the
set-point noise intensity `σ_P`. -/
@[tmio M, powerlib_domain] theorem maxwellian_not_stationary {W : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : T ≠ 0) (σP δ : ℝ) (h0 : DifferentiableAt ℝ (fun x => W x (p.toLossy.Pe δ)) δ)
    (h2 : DifferentiableAt ℝ (fun y => W δ y) (p.toLossy.Pe δ)) :
    ¬ ∀ ω, p.fpOp σP (p.maxwellian W T) δ ω (p.toLossy.Pe δ) = 0 := by
  intro h
  have hM := p.M_pos.ne'
  have hω := p.ωc_pos.ne'
  set w0 := deriv (fun x => W x (p.toLossy.Pe δ)) δ
  set c0 := p.D / p.M + p.ωc - σP ^ 2 / (2 * p.M * T) with hc0
  set c1 := (w0 + p.Pref - p.toLossy.Pe δ) / T with hc1
  set c2 := σP ^ 2 / (2 * T ^ 2) - p.D / T with hc2
  have hc : ∀ ω, c0 + c1 * ω + c2 * ω ^ 2 = 0 := by
    intro ω
    have e := p.fpOp_maxwellian (ω := ω) hT h0.hasDerivAt h2.hasDerivAt σP
    rw [h ω, sub_self, mul_zero, zero_mul, zero_div, add_zero] at e
    have hpos : 0 < p.maxwellian W T δ ω (p.toLossy.Pe δ) := exp_pos _
    have e' := (mul_eq_zero.mp e.symm).resolve_left hpos.ne'
    rw [hc0, hc1, hc2, ← e']
    field_simp
    ring
  have e0 := hc 0
  have e1 := hc 1
  have e2 := hc (-1)
  have hc0' : c0 = 0 := by simpa using e0
  have hc2' : c2 = 0 := by nlinarith
  have key : p.ωc = c0 + T / p.M * c2 := by
    rw [hc0, hc2]; field_simp; ring
  exact hω (by rw [key, hc0', hc2']; ring)

end Params3

end powerlib.GFM.Noise
