import theorem.GridTiedConverter.GFM.Port.LinePH
import theorem.Dynamics.BoundedConvergence
import theorem.PowerSystem.Synchronous.DampedEAC

/-! # VSM, VSM + power filter and PSC on a dynamic R–L line: convergence and energy-well basins

The four-state Layer-0 VSM on a lossy R–L line to a stiff grid (`Line.VSM`) with the weighted
energy `H_c = U(δ) + ½ M ω² + (c L/2) |i − i_s(δ)|²` of
`theorem/GridTiedConverter/GFM/Port/LinePH.lean`, and the three-state power-synchronization law
on the same line (`Line.PSC`) with `H_c = U(δ) + (c L/2) |i − i_s(δ)|²`, and the five-state VSM
with a power filter (`Line.VSMLPF`) with a Barbashin-type function (below): under the strict
dissipation conditions `E² (R² + (X + c L)²) < 4 D c R |Z|²`, resp.
`K_p E² (R² + (X + c L)²) < 4 c R |Z|²` (the same condition with `K_p = 1/D`), the energy
decreases strictly off `{ω = 0, i = i_s(δ)}`, resp. off the equilibria (and, for the power filter,
under explicit conditions on two weights `ε, k`), every bounded forward
solution converges to an equilibrium, and the energy sublevel sets of the potential well lie in
the region of attraction of the operating point. The GFM counterparts of the GFL
`theorem/GridTiedConverter/GFL/LCLine/Convergence.lean` and
`theorem/GridTiedConverter/PLL/Basin.lean` for the line models.

Model boundary.
* The law of `Line.VSM` (`theorem/GridTiedConverter/GFM/Line/Model.lean`): state
  `x = (δ, ω, i_d, i_q) : State 4`, dq frame at the nominal `ω₀` aligned with the stiff grid
  `V ∠ 0`, `δ̇ = ω`, `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`, `X = ω₀ L`,
  constant EMF magnitude `E`, current out of the converter, export-positive
  `P_e = E (cos δ i_d + sin δ i_q)`; quasi-steady current `i_s(δ)` and power
  `P(δ) = c₀ + A sin(δ − α)`. The law of `Line.PSC`: state `x = (δ, i_d, i_q) : State 3`,
  `δ̇ = K_p (P_ref − P_e)` with the same line. The law of `Line.VSMLPF`: state
  `x = (δ, ω, P_f, i_d, i_q) : State 5`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P_e − P_f)`.
* Parameters: `M, D > 0` (VSM), `K_p > 0` (PSC), `M, ω_c > 0` (power filter), a lossy line
  `R > 0`, `L > 0`, `E, V > 0` (`E V > 0` is what is used), a weight `c > 0`,
  `|Z|² = R² + X² > 0`; constant `P_ref`. Continuous time; no voltage loop, inner loops,
  limiter, PLL, delay, PWM, grid-frequency variation.
* Solutions are `IsIntegralCurveOn` curves on `[0, ∞)`; convergence concerns one forward solution,
  the basin the region of attraction `Flow.regionOfAttraction`.

Source: GFM port-structure study note (t1-port, §(c) "pH form", Layer 0 with line, the candidate
energy and `Ḣ = −D ω² − R |ĩ|² − ω ĩ·w(δ)`); the weighted energy and its dissipation condition
`Line.VSM.exists_structure_iff`; work-sync `theory/T-lyapunov-function-method.md` §1.4 (LaSalle).

Results.
* `Line.VSM.phEnergy_lie` (`Ḣ_c = −(D ω² + c R |ĩ|² + ω ĩ·w_c(δ))` as a Lie derivative),
  `Line.VSM.phEnergy_lie_nonpos` (`Ḣ_c ≤ 0` under `E² (R² + (X + c L)²) ≤ 4 D c R |Z|²`) and
  `Line.VSM.eq_of_phEnergy_lie_eq_zero` (under the strict condition `Ḣ_c = 0` forces `ω = 0` and
  `i = i_s(δ)`: `4D(−Ḣ_c) = (2Dω + ĩ·w_c)² + 4DcR|ĩ|² − (ĩ·w_c)²` and
  `(ĩ·w_c)² ≤ |w_c|² |ĩ|²`).
* `Line.VSM.field_zero_isolated`: the equilibria `(δ*, 0, i_s(δ*))`, `P(δ*) = P_ref`, are isolated
  (`A > 0`, `Dynamics.sinusoid_level_isolated`).
* Well geometry: the window `δ_u − 2π < δ < δ_u` of the reduced swing machine
  `Line.VSM.swingParams` (`Line.VSM.wellWindow`), the potential bound
  `U(δ) ≤ H_c` (`Line.VSM.potential_le_phEnergy`), the only equilibrium in it is
  `qss(δ_s, 0)` (`Line.VSM.eq_point_of_field_eq_zero`), and the sublevel sets of `H_c` in it below
  both saddle levels are compact (`Line.VSM.isCompact_wellSublevel`).
* Implementation evidence (private): `Line.VSM.exists_tendsto_of_bounded` (strict dissipation:
  every bounded forward solution converges to an equilibrium, `Dynamics.exists_tendsto_of_bounded`
  with `H_c`) and `Line.VSM.regionOfAttraction_well` (strict dissipation, `|P_ref − c₀| < A`: every
  sublevel set `{δ_u − 2π < δ < δ_u, H_c ≤ c₁}` with `c₁` below both saddle levels `U(δ_u)`,
  `U(δ_u − 2π)` lies in the region of attraction of `qss(δ_s, 0)`; LaSalle
  `Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel`).
* Line PSC (symbolic derivation: sympy, symbolic parameters, batch N8 log): the energy
  `Line.PSC.pscEnergy` (`H_c = U(δ) + (c L/2) |ĩ|²`, `U` the potential of
  `Line.PSC.wellParams = ⟨1, 1, P_ref, c₀, A, α⟩`), its derivative
  (`Line.PSC.hasFDerivAt_pscEnergy`) and the exact rate
  `Ḣ_c = −(K_p (y − c L b)(y + a) + c R |ĩ|²)`, `y = P(δ) − P_ref`, `a = P_e − P(δ)`,
  `b = i_s'(δ)·ĩ` (`Line.PSC.pscEnergy_lie`); with `a + c L b = w_c(δ)·ĩ` (the coupling vector of
  the VSM energy) and `4K_p(−Ḣ_c) = (2K_p y + K_p(a − c L b))² + K_p (4 c R |ĩ|² − K_p (w_c·ĩ)²)`:
  `Ḣ_c ≤ 0` under `K_p E² (R² + (X + c L)²) ≤ 4 c R |Z|²` (`Line.PSC.pscEnergy_lie_nonpos`), and
  under the strict condition `Ḣ_c = 0` only at equilibria
  (`Line.PSC.field_eq_zero_of_pscEnergy_lie_eq_zero`); isolated equilibria
  (`Line.PSC.field_zero_isolated`); well geometry (`Line.PSC.wellWindow`,
  `Line.PSC.potential_le_pscEnergy`, `Line.PSC.eq_point_of_field_eq_zero`,
  `Line.PSC.isCompact_wellSublevel`); private `Line.PSC.exists_tendsto_of_bounded` and
  `Line.PSC.regionOfAttraction_well` (the region of attraction of `qss(δ_s)`). The condition is the
  VSM condition with `D = 1/K_p`; by the algebra of `Line.VSM.exists_phR_posSemidef_iff` (not
  restated for the PSC) some weight satisfies its non-strict form iff
  `K_p E² L (X + |Z|) ≤ 2 R |Z|²`, a gain below the critical droop gain
  `K_p,crit = 2 R |Z|²/(E² L X)` at zero reactive power (`Line.Network.KpCrit`).
* Line VSM + power filter (`Line.VSMLPF`, five states; symbolic derivation: sympy, symbolic
  parameters, batch N8 log): the Lyapunov function with weights `ε, k`
  `V = (M ω_c + D − ε ω_c) U(δ) + M y ω + (M D/2) ω² − ε ω z + z²/(2 ω_c) + (k/2) |ĩ|²`,
  `y = P(δ) − P_ref`, `z = ω_c M ω + P_ref − P_f` (`Line.VSMLPF.lyap`; Barbashin's function of the
  three-state loop with the cross term `−ε ω z` and a magnetic term), its derivative
  (`Line.VSMLPF.hasFDerivAt_lyap`) and the exact rate
  `V̇ = −(D² + D M ω_c − M P'(δ) − ε ω_c D) ω² − (ε/M) z² + (ε (M ω_c + D)/M) ω z − (k R/L) |ĩ|²`
  `− z a + ω (ε ω_c a − k b)`, `a = P_e − P(δ)`, `b = i_s'(δ)·ĩ` (`Line.VSMLPF.lyap_lie`). With
  `μ = D² + D M ω_c − M A − ε ω_c D − ε (M ω_c + D)²/(2M)`, `ν = k R/L − M E²/(2ε)` and
  `Γ² = E² (ε² ω_c² − 2 ε ω_c k X/|Z|² + k²/|Z|²)` (`Line.VSMLPF.lyapMu`, `lyapNu`, `lyapGammaSq`;
  `Γ²` is the angle-independent size of the coupling vector, `Line.VSMLPF.normSq_lyapCoupling`):
  under `ε > 0`, `μ > 0`, `Γ² < 4 μ ν` the rate is `≤ 0` (`Line.VSMLPF.lyap_lie_nonpos`) and
  vanishes only at `ω = 0`, `P_f = P_ref`, `i = i_s(δ)` (`Line.VSMLPF.eq_of_lyap_lie_eq_zero`).
  Isolated equilibria (`Line.VSMLPF.field_zero_isolated`); the well form
  `V = W(δ) + ((M D − ε² ω_c)/2)(ω + M y/(M D − ε² ω_c))² + (z − ε ω_c ω)²/(2 ω_c) + (k/2)|ĩ|²`,
  `W = (M ω_c + D − ε ω_c) U − M² y²/(2 (M D − ε² ω_c))` (`Line.VSMLPF.lyapWell`,
  `Line.VSMLPF.lyap_eq_well`, `Line.VSMLPF.lyapWell_le_lyap`), the window, the equilibrium in it
  and compact sublevel sets (`Line.VSMLPF.wellWindow`, `Line.VSMLPF.eq_point_of_field_eq_zero`,
  `Line.VSMLPF.isCompact_wellSublevel`, `M D > ε² ω_c`, `k > 0`); private
  `Line.VSMLPF.exists_tendsto_of_bounded` and `Line.VSMLPF.regionOfAttraction_well`. The conditions
  are met (`Line.VSMLPF.witness_conditions`): `E = V = 1`, `R = 3`, `L = 4`, `ω₀ = 1`, `M = 1`,
  `D = 2`, `ω_c = 1`, `P_ref = c₀ = 3/25`, `ε = 1/2`, `k = 4` give `μ = 51/20`, `ν = 2`,
  `Γ² = 1/4`.

Family and connection conclusions.
No family and no connection conclusion: the convergence of one bounded solution and the region of
attraction are outside the sentence language, kept as private implementation evidence (as the GFL
`piPLL_tendsto_of_bounded` and the PLL basins); the energy rate, its zero set and the well
geometry are static domain evidence. The local sentences of the operating points are the connection
statements of `Line.VSM.family` (`theorem/GridTiedConverter/GFM/Line/VSM.lean`),
`Line.VSMLPF.family` (`theorem/GridTiedConverter/GFM/Line/VSMLPF.lean`) and `Line.PSC.family`
(`theorem/GridTiedConverter/GFM/Line/PSC.lean`).

Scope.
* The dissipation condition is the strict form of `Line.VSM.forall_phR_posSemidef_iff`; some
  weight satisfies the non-strict form iff `E² L (X + |Z|) ≤ 2 D R |Z|²`
  (`Line.VSM.exists_phR_posSemidef_iff`). Outside it no convergence or basin statement is made
  (the line VSM has Hopf points, `Line.VSM.Model.sign_firstLyapunov_crit`).
* For the VSM with a power filter on the line (`Line.VSMLPF`) Barbashin's function of the
  three-state loop plus a magnetic term alone does not work: the filter error `z` enters its rate
  only through the cross term `−z (P_e − P(δ))`, with no `z²` dissipation. The cross term `−ε ω z`
  of `Line.VSMLPF.lyap` creates the dissipation `−(ε/M) z²`, at the price of `ε ω_c D ω²` and the
  `ω z`, `ω ĩ` couplings measured by `μ`, `Γ²`; the conditions are sufficient, not necessary.
-/

noncomputable section
namespace powerlib.GFM.Line
open Set Filter Topology
open powerlib.Dynamics (State coord)

namespace VSM

variable (g : VSM)

/-! ## The energy rate -/

/-- The energy rate as a Lie derivative: `Ḣ_c = −(D ω² + c R |ĩ|² + ω ĩ·w_c(δ))`. -/
@[tmio M, powerlib_domain] theorem phEnergy_lie (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (c : ℝ) (x : State 4) :
    fderiv ℝ (g.phEnergy c) x (g.field x) =
      -(g.D * x 1 ^ 2 + c * g.R * ((x 2 - (g.is (x 0)).re) ^ 2 + (x 3 - (g.is (x 0)).im) ^ 2) +
        x 1 * (g.couplingD c (x 0) * (x 2 - (g.is (x 0)).re) +
          g.couplingQ c (x 0) * (x 3 - (g.is (x 0)).im))) := by
  rw [(g.hasGradientAt_phEnergy c x).hasFDerivAt.fderiv, InnerProductSpace.toDual_apply_apply,
    PH.inner_eq_dotProduct, g.phGrad_dotProduct_field hM hL hZ]

@[tmio M, powerlib_domain] theorem differentiable_phEnergy (c : ℝ) :
    Differentiable ℝ (g.phEnergy c) :=
  fun x => (g.hasGradientAt_phEnergy c x).hasFDerivAt.differentiableAt

/-- The quadratic form of the rate: `4D (D ω² + c R q + ω a) ≥ (4 D c R − W) q` when
`a² ≤ W q` (`q = |ĩ|²`, `a = ĩ·w_c`, `W = |w_c|²`). -/
@[tmio T, powerlib_foundation] private theorem quad_lower {D c R ω q a W : ℝ}
    (ha : a ^ 2 ≤ W * q) :
    (4 * D * c * R - W) * q ≤ 4 * D * (D * ω ^ 2 + c * R * q + ω * a) := by
  nlinarith [sq_nonneg (2 * D * ω + a)]

/-- Cauchy–Schwarz in the plane: `(w_d ĩ_d + w_q ĩ_q)² ≤ (w_d² + w_q²)(ĩ_d² + ĩ_q²)`. -/
@[tmio T, powerlib_foundation] private theorem cs2 (a b u v : ℝ) :
    (a * u + b * v) ^ 2 ≤ (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (a * v - b * u)]

/-- **The energy does not increase** under `E² (R² + (X + c L)²) ≤ 4 D c R |Z|²` (`D > 0`). -/
@[tmio M, powerlib_domain] theorem phEnergy_lie_nonpos (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hD : 0 < g.D) {c : ℝ}
    (hdiss : g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) ≤ 4 * g.D * c * g.R * g.absSq)
    (x : State 4) : fderiv ℝ (g.phEnergy c) x (g.field x) ≤ 0 := by
  rw [g.phEnergy_lie hM hL hZ]
  have hW := g.normSq_coupling hZ.ne' c (x 0)
  have h := quad_lower (D := g.D) (c := c) (R := g.R) (ω := x 1)
    (cs2 (g.couplingD c (x 0)) (g.couplingQ c (x 0)) (x 2 - (g.is (x 0)).re)
      (x 3 - (g.is (x 0)).im))
  set W := g.couplingD c (x 0) ^ 2 + g.couplingQ c (x 0) ^ 2
  have hW' : W ≤ 4 * g.D * c * g.R := by
    rw [hW, div_le_iff₀ hZ]; linarith
  have hq : 0 ≤ (x 2 - (g.is (x 0)).re) ^ 2 + (x 3 - (g.is (x 0)).im) ^ 2 := by positivity
  have : 0 ≤ (4 * g.D * c * g.R - W) *
      ((x 2 - (g.is (x 0)).re) ^ 2 + (x 3 - (g.is (x 0)).im) ^ 2) :=
    mul_nonneg (by linarith) hq
  nlinarith

/-- **The energy is stationary only at rest on the quasi-steady current** under the strict
condition `E² (R² + (X + c L)²) < 4 D c R |Z|²` (`D > 0`): `Ḣ_c = 0` forces `ω = 0` and
`i = i_s(δ)`. -/
@[tmio M, powerlib_domain] theorem eq_of_phEnergy_lie_eq_zero (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hD : 0 < g.D) {c : ℝ}
    (hdiss : g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) < 4 * g.D * c * g.R * g.absSq)
    {x : State 4} (hx : fderiv ℝ (g.phEnergy c) x (g.field x) = 0) :
    x 1 = 0 ∧ x 2 = (g.is (x 0)).re ∧ x 3 = (g.is (x 0)).im := by
  rw [g.phEnergy_lie hM hL hZ] at hx
  have hW := g.normSq_coupling hZ.ne' c (x 0)
  have h := quad_lower (D := g.D) (c := c) (R := g.R) (ω := x 1)
    (cs2 (g.couplingD c (x 0)) (g.couplingQ c (x 0)) (x 2 - (g.is (x 0)).re)
      (x 3 - (g.is (x 0)).im))
  set W := g.couplingD c (x 0) ^ 2 + g.couplingQ c (x 0) ^ 2
  have hW' : W < 4 * g.D * c * g.R := by
    rw [hW, div_lt_iff₀ hZ]; linarith
  set q := (x 2 - (g.is (x 0)).re) ^ 2 + (x 3 - (g.is (x 0)).im) ^ 2
  have hq : 0 ≤ q := by positivity
  rw [neg_eq_zero.mp hx, mul_zero] at h
  have hq0 : q = 0 := by
    by_contra hne
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
    have := mul_pos (show 0 < 4 * g.D * c * g.R - W by linarith) hqpos
    linarith
  have h2 : x 2 - (g.is (x 0)).re = 0 := by
    have : (x 2 - (g.is (x 0)).re) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 3 - (g.is (x 0)).im)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have h3 : x 3 - (g.is (x 0)).im = 0 := by
    have : (x 3 - (g.is (x 0)).im) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 2 - (g.is (x 0)).re)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  rw [h2, h3] at hx
  have h1 : g.D * x 1 ^ 2 = 0 := by nlinarith
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h1).resolve_left hD.ne'),
    by linarith, by linarith⟩

/-! ## Isolated equilibria and bounded solutions -/

/-- The equilibria `(δ*, 0, i_s(δ*))`, `P(δ*) = P_ref`, are isolated (`E V > 0`). -/
@[tmio M, powerlib_domain] theorem field_zero_isolated (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) (z : State 4) (hz : g.field z = 0) :
    ∃ ε > 0, ∀ y, g.field y = 0 → dist y z < ε → y = z := by
  have hA : g.A ≠ 0 := (div_pos hEV (Real.sqrt_pos.mpr hZ)).ne'
  obtain ⟨hz1, hz2, hz3, -⟩ := (g.field_eq_zero_iff hM hL hZ.ne' z).mp hz
  obtain ⟨ε, hε, hiso⟩ :=
    Dynamics.sinusoid_level_isolated (c := g.c0) (α := g.α) (p := g.Pref) hA (z 0)
  refine ⟨ε, hε, fun y hy hyz => ?_⟩
  obtain ⟨hy1, hy2, hy3, hy4⟩ := (g.field_eq_zero_iff hM hL hZ.ne' y).mp hy
  have hd : |y 0 - z 0| < ε := by
    have := Dynamics.abs_apply_le_norm (y - z) 0
    simp only [PiLp.sub_apply] at this
    exact lt_of_le_of_lt this (by rwa [← dist_eq_norm])
  have h0 := hiso (y 0) (by rw [← g.qssPower_eq_polar hZ]; exact hy4) hd
  ext i; fin_cases i
  · exact h0
  · simp [hy1, hz1]
  · simp [hy2, hz2, h0]
  · simp [hy3, hz3, h0]

/-- **Bounded solutions of the line VSM converge** under the strict dissipation condition
`E² (R² + (X + c L)²) < 4 D c R |Z|²` (`M, D, L > 0`, `E V > 0`): every bounded forward solution
converges to an equilibrium `qss(δ*, 0) = (δ*, 0, i_s(δ*))` with `P(δ*) = P_ref` (the energy
`H_c` decreases off `{ω = 0, i = i_s(δ)}`; a solution with `ω ≡ 0` has `ω̇ = 0`, i.e.
`P_e = P_ref`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem exists_tendsto_of_bounded (hM : 0 < g.M)
    (hD : 0 < g.D) (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {c : ℝ}
    (hdiss : g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) < 4 * g.D * c * g.R * g.absSq)
    {φ : ℝ → State 4} (hφ : IsIntegralCurveOn φ (fun _ y => g.field y) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ δs, g.qssPower δs = g.Pref ∧ Tendsto φ atTop (𝓝 (g.qss (PhasePlane.mk δs 0))) := by
  obtain ⟨z, hz, hzt⟩ := Dynamics.exists_tendsto_of_bounded g.contDiff_field
    (g.differentiable_phEnergy c) hφ hb
    (fun t _ => g.phEnergy_lie_nonpos hM.ne' hL.ne' hZ hD hdiss.le (φ t))
    (fun ψ hψ _ h0 => by
      have hr : ∀ t, 0 ≤ t → ψ t 1 = 0 ∧ ψ t 2 = (g.is (ψ t 0)).re ∧
          ψ t 3 = (g.is (ψ t 0)).im := fun t ht =>
        g.eq_of_phEnergy_lie_eq_zero hM.ne' hL.ne' hZ hD hdiss (h0 t ht)
      have h1 := Dynamics.field_apply_eq_zero_of_coord_const hψ 1 (fun t ht => (hr t ht).1)
        le_rfl
      obtain ⟨r1, r2, r3⟩ := hr 0 le_rfl
      rw [field_apply_one, r1, mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM.ne',
        sub_eq_zero] at h1
      exact (g.field_eq_zero_iff hM.ne' hL.ne' hZ.ne' _).mpr
        ⟨r1, r2, r3, by rw [Network.qssPower, ← r2, ← r3]; exact h1.symm⟩)
    (fun z _ hz => g.field_zero_isolated hM.ne' hL.ne' hZ hEV z hz)
  obtain ⟨h1, h2, h3, h4⟩ := (g.field_eq_zero_iff hM.ne' hL.ne' hZ.ne' z).mp hz
  refine ⟨z 0, h4, ?_⟩
  have : z = g.qss (PhasePlane.mk (z 0) 0) := by
    ext i; fin_cases i <;> simp [qss, h1, h2, h3]
  rwa [← this]

/-! ## The potential well and its region of attraction -/

/-- The well window `δ_u − 2π < δ < δ_u` of the reduced swing machine `swingParams`. -/
def wellWindow : Set (State 4) :=
  {x | g.swingParams.deltaU - 2 * Real.pi < x 0 ∧ x 0 < g.swingParams.deltaU}

@[tmio M, powerlib_domain] theorem isOpen_wellWindow : IsOpen g.wellWindow :=
  (isOpen_lt continuous_const (Dynamics.contDiff_coord (k := 0) 0).continuous).inter
    (isOpen_lt (Dynamics.contDiff_coord (k := 0) 0).continuous continuous_const)

/-- The energy dominates the potential of the reduced swing machine (`M ≥ 0`, `c L ≥ 0`). -/
@[tmio M, powerlib_domain] theorem potential_le_phEnergy (hM : 0 ≤ g.M) {c : ℝ}
    (hcL : 0 ≤ c * g.L) (x : State 4) :
    g.swingParams.potential 0 (x 0) ≤ g.phEnergy c x := by
  have h1 : 0 ≤ g.M * x 1 ^ 2 / 2 := by positivity
  have h2 : 0 ≤ c * g.L / 2 * ((x 2 - (g.is (x 0)).re) ^ 2 + (x 3 - (g.is (x 0)).im) ^ 2) := by
    positivity
  simp only [phEnergy]
  linarith

/-- In the well window the only equilibrium is the operating point `qss(δ_s, 0)` (`|P_ref − c₀| <
A`; the swing well geometry `Synchronous.SwingParams.eq_deltaS_of_field_eq_zero`). -/
@[tmio M, powerlib_domain] theorem eq_point_of_field_eq_zero (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) (h : |g.Pref - g.c0| < g.A) {x : State 4}
    (hx : x ∈ g.wellWindow) (hf : g.field x = 0) :
    x = g.qss (PhasePlane.mk g.swingParams.deltaS 0) := by
  have hA : 0 < g.A := div_pos hEV (Real.sqrt_pos.mpr hZ)
  obtain ⟨h1, h2, h3, h4⟩ := (g.field_eq_zero_iff hM hL hZ.ne' x).mp hf
  have hs := g.swingParams.eq_deltaS_of_field_eq_zero hM hA h (x := PhasePlane.mk (x 0) 0)
    ⟨by simpa using hx.1, by simpa using hx.2⟩
    ((g.swingParams.field_eq_zero_iff hM _).mpr ⟨by simp, by
      simp only [PhasePlane.mk_apply_zero, Synchronous.SwingParams.Pe, swingParams]
      rw [← g.qssPower_eq_polar hZ]; exact h4⟩)
  have h0 : x 0 = g.swingParams.deltaS := by
    simpa using congrArg (fun y : State 2 => y 0) hs
  ext i; fin_cases i <;> simp [qss, h0, h1, h2, h3]

/-- Energy sublevel sets of the well below both saddle levels `U(δ_u)`, `U(δ_u − 2π)` are compact
(`M, L, c > 0`). -/
@[tmio M, powerlib_domain] theorem isCompact_wellSublevel (hM : 0 < g.M) (hL : 0 < g.L) {c : ℝ}
    (hc : 0 < c) {c₁ : ℝ} (hc1 : c₁ < g.swingParams.potential 0 g.swingParams.deltaU)
    (hc2 : c₁ < g.swingParams.potential 0 (g.swingParams.deltaU - 2 * Real.pi)) :
    IsCompact {x ∈ g.wellWindow | g.phEnergy c x ≤ c₁} := by
  set a := g.swingParams.deltaU - 2 * Real.pi
  set b := g.swingParams.deltaU
  have hab : a ≤ b := by have := Real.pi_pos; simp only [a, b]; linarith
  have hcL : 0 ≤ c * g.L := by positivity
  have hcU : Continuous (g.swingParams.potential 0) := by
    unfold Synchronous.SwingParams.potential; fun_prop
  have hcH : Continuous (g.phEnergy c) := (g.differentiable_phEnergy c).continuous
  have hc0 : Continuous fun x : State 4 => x 0 := (Dynamics.contDiff_coord (k := 0) 0).continuous
  have hcis : Continuous g.is := by unfold Network.is; fun_prop
  have hEq : {x ∈ g.wellWindow | g.phEnergy c x ≤ c₁} =
      {x : State 4 | a ≤ x 0} ∩ {x | x 0 ≤ b} ∩ {x | g.phEnergy c x ≤ c₁} := by
    ext x
    simp only [wellWindow, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.le, h2.le⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hU := g.potential_le_phEnergy hM.le hcL x
      refine ⟨⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩, h3⟩
      · intro he; rw [← he] at hU; linarith
      · intro he; rw [he] at hU; linarith
  rw [hEq]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact ((isClosed_le continuous_const hc0).inter (isClosed_le hc0 continuous_const)).inter
      (isClosed_le hcH continuous_const)
  obtain ⟨δm, -, hδm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcU.continuousOn
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcis.continuousOn
  set C := c₁ - g.swingParams.potential 0 δm
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨|a| + |b| + (1 + 2 * C / g.M) + 2 * (1 + 2 * C / (c * g.L) + S), ?_⟩
  rintro x ⟨⟨h1, h2⟩, h3⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [mem_ofPred_eq] at h1 h2 h3
  have hU : g.swingParams.potential 0 δm ≤ g.swingParams.potential 0 (x 0) :=
    hδm (show x 0 ∈ Icc a b from ⟨h1, h2⟩)
  have hSx : ‖g.is (x 0)‖ ≤ S := hS (x 0) ⟨h1, h2⟩
  simp only [phEnergy] at h3
  set u := x 2 - (g.is (x 0)).re
  set v := x 3 - (g.is (x 0)).im
  have hkin : 0 ≤ g.M * x 1 ^ 2 / 2 := by positivity
  have hmag : 0 ≤ c * g.L / 2 * (u ^ 2 + v ^ 2) := by positivity
  have hx1 : x 1 ^ 2 ≤ 2 * C / g.M := by
    rw [le_div_iff₀ hM]; simp only [C]; nlinarith
  have huv : u ^ 2 + v ^ 2 ≤ 2 * C / (c * g.L) := by
    rw [le_div_iff₀ (by positivity)]; simp only [C]; nlinarith
  have habs : ∀ w : ℝ, |w| ≤ 1 + w ^ 2 := fun w => by
    rcases abs_cases w with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith [sq_nonneg (w - 1),
      sq_nonneg (w + 1)]
  have hre : |(g.is (x 0)).re| ≤ S := (Complex.abs_re_le_norm _).trans hSx
  have him : |(g.is (x 0)).im| ≤ S := (Complex.abs_im_le_norm _).trans hSx
  have hx2 : |x 2| ≤ 1 + 2 * C / (c * g.L) + S := by
    have : x 2 = u + (g.is (x 0)).re := by simp only [u]; ring
    rw [this]
    have := abs_add_le u (g.is (x 0)).re
    nlinarith [habs u, sq_nonneg v]
  have hx3 : |x 3| ≤ 1 + 2 * C / (c * g.L) + S := by
    have : x 3 = v + (g.is (x 0)).im := by simp only [v]; ring
    rw [this]
    have := abs_add_le v (g.is (x 0)).im
    nlinarith [habs v, sq_nonneg u]
  have hx0 : |x 0| ≤ |a| + |b| := by
    rw [abs_le]; constructor <;>
      cases abs_cases a <;> cases abs_cases b <;> linarith [abs_nonneg a, abs_nonneg b]
  have hx1' : |x 1| ≤ 1 + 2 * C / g.M := (habs (x 1)).trans (by linarith)
  have hnorm := (Dynamics.norm_le_sum_abs x).trans_eq (Fin.sum_univ_four _)
  linarith

/-- **LaSalle on the energy well of the line VSM** (strict dissipation, `M, D, L > 0`, `E V > 0`,
`|P_ref − c₀| < A`): every sublevel set of `H_c` in the well window below both saddle levels lies
in the region of attraction of the operating point `qss(δ_s, 0)` (on the zero set of `Ḣ_c`,
`ω = 0` and `i = i_s(δ)`; there `ω̇ = 0` is power balance, so the point is the equilibrium of the
window). Implementation evidence: trajectory-level result outside the sentence language
(Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem regionOfAttraction_well (hM : 0 < g.M)
    (hD : 0 < g.D) (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {c : ℝ}
    (hc : 0 < c)
    (hdiss : g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) < 4 * g.D * c * g.R * g.absSq)
    (h : |g.Pref - g.c0| < g.A) {c₁ : ℝ}
    (hc1 : c₁ < g.swingParams.potential 0 g.swingParams.deltaU)
    (hc2 : c₁ < g.swingParams.potential 0 (g.swingParams.deltaU - 2 * Real.pi)) :
    {x ∈ g.wellWindow | g.phEnergy c x ≤ c₁} ⊆
      Flow.regionOfAttraction g.field (g.qss (PhasePlane.mk g.swingParams.deltaS 0)) := by
  have hHc : ContDiff ℝ 1 (g.phEnergy c) := by
    unfold phEnergy Synchronous.SwingParams.potential
    simp only [Network.is_re, Network.is_im]
    fun_prop
  refine Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel g.isOpen_wellWindow
    g.contDiff_field hHc (fun x _ => g.phEnergy_lie_nonpos hM.ne' hL.ne' hZ hD hdiss.le x)
    (g.isCompact_wellSublevel hM hL hc hc1 hc2) ?_
  refine Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem g.contDiff_field
    (Dynamics.contDiff_coord (n := 4) (k := 1) 1) (fun x hx => ?_) (fun x hx hd => ?_)
  · rw [Dynamics.LaSalle.lieDerivZeroSet_def] at hx
    exact (g.eq_of_phEnergy_lie_eq_zero hM.ne' hL.ne' hZ hD hdiss hx.2).1
  · rw [Dynamics.LaSalle.lieDerivZeroSet_def] at hx
    obtain ⟨h1, h2, h3⟩ := g.eq_of_phEnergy_lie_eq_zero hM.ne' hL.ne' hZ hD hdiss hx.2
    rw [(Dynamics.hasFDerivAt_coord _ _).fderiv, Dynamics.coord_apply, field_apply_one, h1,
      mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM.ne', sub_eq_zero] at hd
    have hf : g.field x = 0 := (g.field_eq_zero_iff hM.ne' hL.ne' hZ.ne' x).mpr
      ⟨h1, h2, h3, by rw [Network.qssPower, ← h2, ← h3]; exact hd.symm⟩
    exact g.eq_point_of_field_eq_zero hM.ne' hL.ne' hZ hEV h hx.1.1 hf

end VSM

/-! ## Power synchronization on the line -/

namespace PSC

variable (g : PSC)

/-- The network of the PSC read as a VSM network (inertia and damping `1`): only its line data
enter the coupling vector `w_c(δ) = E e^{jδ} + c L i_s'(δ)` (`VSM.couplingD`, `VSM.couplingQ`). -/
def toVSM : VSM := ⟨g.toNetwork, 1, 1, g.Pref⟩

/-- The reduced swing parameters of the well, `⟨1, 1, P_ref, c₀, A, α⟩`: the potential
`U(δ) = ∫ (P(δ) − P_ref)` and the angles `δ_s`, `δ_u` of the PSC law (inertia and damping do not
enter them). -/
def wellParams : Synchronous.SwingParams := ⟨1, 1, g.Pref, g.c0, g.A, g.α⟩

/-- The PSC energy `H_c = U(δ) + (c L/2) |i − i_s(δ)|²`. -/
def pscEnergy (c : ℝ) (x : State 3) : ℝ :=
  g.wellParams.potential 0 (x 0) +
    c * g.L / 2 * ((x 1 - (g.is (x 0)).re) ^ 2 + (x 2 - (g.is (x 0)).im) ^ 2)

@[tmio M, powerlib_domain] private theorem hasDerivAt_is_re (δ : ℝ) :
    HasDerivAt (fun δ => (g.is δ).re) (g.toVSM.isRateD δ) δ := by
  have h := ((((Real.hasDerivAt_cos δ).const_mul g.E).sub_const g.V).const_mul g.R).add
    ((Real.hasDerivAt_sin δ).const_mul g.E |>.const_mul g.X) |>.div_const g.absSq
  convert h using 1
  · funext y; rw [Network.is_re]; rfl
  · simp only [VSM.isRateD, toVSM]; ring

@[tmio M, powerlib_domain] private theorem hasDerivAt_is_im (δ : ℝ) :
    HasDerivAt (fun δ => (g.is δ).im) (g.toVSM.isRateQ δ) δ := by
  have h := (((Real.hasDerivAt_sin δ).const_mul g.E).const_mul g.R).sub
    ((((Real.hasDerivAt_cos δ).const_mul g.E).sub_const g.V).const_mul g.X) |>.div_const g.absSq
  convert h using 1
  · funext y; rw [Network.is_im]; rfl
  · simp only [VSM.isRateQ, toVSM]; ring

/-- The derivative of the PSC energy. -/
def pscDeriv (c : ℝ) (x : State 3) : State 3 →L[ℝ] ℝ :=
  (g.wellParams.Pe (x 0) - g.Pref - c * g.L * ((x 1 - (g.is (x 0)).re) * g.toVSM.isRateD (x 0) +
      (x 2 - (g.is (x 0)).im) * g.toVSM.isRateQ (x 0))) • coord 0 +
    (c * g.L * (x 1 - (g.is (x 0)).re)) • coord 1 + (c * g.L * (x 2 - (g.is (x 0)).im)) • coord 2

@[tmio M, powerlib_domain] theorem hasFDerivAt_pscEnergy (c : ℝ) (x : State 3) :
    HasFDerivAt (g.pscEnergy c) (g.pscDeriv c x) x := by
  have h0 := Dynamics.hasFDerivAt_coord 0 x
  have hU := (g.wellParams.hasDerivAt_potential 0 (x 0)).comp_hasFDerivAt x h0
  have e1 := (Dynamics.hasFDerivAt_coord 1 x).sub ((g.hasDerivAt_is_re (x 0)).comp_hasFDerivAt x h0)
  have e2 := (Dynamics.hasFDerivAt_coord 2 x).sub ((g.hasDerivAt_is_im (x 0)).comp_hasFDerivAt x h0)
  have h := hU.add (((e1.mul e1).add (e2.mul e2)).const_mul (c * g.L / 2))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
  · simp only [pscEnergy, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  · ext v
    simp only [pscDeriv, add_apply, smul_apply,
      sub_apply, Dynamics.coord_apply, smul_eq_mul, Pi.sub_apply,
      Function.comp_apply, wellParams]
    ring

@[tmio M, powerlib_domain] theorem differentiable_pscEnergy (c : ℝ) :
    Differentiable ℝ (g.pscEnergy c) :=
  fun x => (g.hasFDerivAt_pscEnergy c x).differentiableAt

/-- **The PSC energy rate** (`L ≠ 0`, `|Z|² > 0`): with `y = P(δ) − P_ref`,
`a = E (cos δ ĩ_d + sin δ ĩ_q)` (`P_e = P(δ) + a`) and `b = i_s'(δ)·ĩ`,
`Ḣ_c = −(K_p (y − c L b)(y + a) + c R |ĩ|²)`. -/
@[tmio M, powerlib_domain] theorem pscEnergy_lie (hL : g.L ≠ 0) (hZ : 0 < g.absSq) (c : ℝ)
    (x : State 3) :
    fderiv ℝ (g.pscEnergy c) x (g.field x) =
      -(g.Kp * (g.qssPower (x 0) - g.Pref - c * g.L *
          ((x 1 - (g.is (x 0)).re) * g.toVSM.isRateD (x 0) +
            (x 2 - (g.is (x 0)).im) * g.toVSM.isRateQ (x 0))) *
        (g.qssPower (x 0) - g.Pref + g.E * (Real.cos (x 0) * (x 1 - (g.is (x 0)).re) +
          Real.sin (x 0) * (x 2 - (g.is (x 0)).im))) +
        c * g.R * ((x 1 - (g.is (x 0)).re) ^ 2 + (x 2 - (g.is (x 0)).im) ^ 2)) := by
  have hP : g.wellParams.Pe (x 0) = g.qssPower (x 0) := by
    rw [g.qssPower_eq_polar hZ]; simp [wellParams, Synchronous.SwingParams.Pe]
  have hl := (g.rate_eq_zero_iff hL hZ.ne' (x 0) (g.is (x 0)).re (g.is (x 0)).im).mpr ⟨rfl, rfl⟩
  obtain ⟨hd, hq⟩ := hl
  simp only [Network.rateD, Network.rateQ, div_eq_zero_iff, hL, or_false] at hd hq
  rw [(g.hasFDerivAt_pscEnergy c x).fderiv]
  simp only [pscDeriv, hP, add_apply, smul_apply,
    Dynamics.coord_apply, smul_eq_mul, field_apply_zero, field_apply_one, field_apply_two,
    Network.rateD, Network.rateQ, Network.qssPower, Network.power_eq]
  field_simp
  linear_combination (c * (x 1 - (g.is (x 0)).re)) * hd + (c * (x 2 - (g.is (x 0)).im)) * hq

/-- The quadratic form of the PSC rate:
`4K (K (y − c L b)(y + a) + c R q) = (2K y + K (a − c L b))² + K (4 c R q − K (a + c L b)²)`. -/
@[tmio T, powerlib_foundation] private theorem psc_quad (K y a b c L R q : ℝ) :
    4 * K * (K * (y - c * L * b) * (y + a) + c * R * q) =
      (2 * K * y + K * (a - c * L * b)) ^ 2 + K * (4 * c * R * q - K * (a + c * L * b) ^ 2) := by
  ring

/-- The rate in the coupling form: `a + c L b = w_c(δ)·ĩ` (`VSM.couplingD`, `VSM.couplingQ` of the
network). -/
@[tmio M, powerlib_domain] private theorem coupling_dot (c : ℝ) (x : State 3) :
    g.E * (Real.cos (x 0) * (x 1 - (g.is (x 0)).re) + Real.sin (x 0) * (x 2 - (g.is (x 0)).im)) +
        c * g.L * ((x 1 - (g.is (x 0)).re) * g.toVSM.isRateD (x 0) +
          (x 2 - (g.is (x 0)).im) * g.toVSM.isRateQ (x 0)) =
      g.toVSM.couplingD c (x 0) * (x 1 - (g.is (x 0)).re) +
        g.toVSM.couplingQ c (x 0) * (x 2 - (g.is (x 0)).im) := by
  simp only [VSM.couplingD, VSM.couplingQ, toVSM]
  ring

/-- **The PSC energy does not increase** under `K_p E² (R² + (X + c L)²) ≤ 4 c R |Z|²`
(`K_p > 0`). -/
@[tmio M, powerlib_domain] theorem pscEnergy_lie_nonpos (hL : g.L ≠ 0) (hZ : 0 < g.absSq)
    (hK : 0 < g.Kp) {c : ℝ}
    (hdiss : g.Kp * (g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2)) ≤ 4 * c * g.R * g.absSq)
    (x : State 3) : fderiv ℝ (g.pscEnergy c) x (g.field x) ≤ 0 := by
  rw [g.pscEnergy_lie hL hZ]
  have hW : g.toVSM.couplingD c (x 0) ^ 2 + g.toVSM.couplingQ c (x 0) ^ 2 =
      g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) / g.absSq :=
    g.toVSM.normSq_coupling hZ.ne' c (x 0)
  have hcd := g.coupling_dot c x
  set u := x 1 - (g.is (x 0)).re
  set v := x 2 - (g.is (x 0)).im
  set a := g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)
  set b := u * g.toVSM.isRateD (x 0) + v * g.toVSM.isRateQ (x 0)
  set y := g.qssPower (x 0) - g.Pref
  set q := u ^ 2 + v ^ 2
  set W := g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) / g.absSq
  have hcs : (a + c * g.L * b) ^ 2 ≤ W * q := by
    rw [hcd, ← hW]; exact VSM.cs2 _ _ _ _
  have hKW : g.Kp * W ≤ 4 * c * g.R := by
    simp only [W]; rw [mul_div_assoc', div_le_iff₀ hZ]; exact hdiss
  have hq : 0 ≤ q := by positivity
  have h2 : g.Kp * (a + c * g.L * b) ^ 2 ≤ 4 * c * g.R * q := by
    calc g.Kp * (a + c * g.L * b) ^ 2 ≤ g.Kp * (W * q) := mul_le_mul_of_nonneg_left hcs hK.le
      _ = (g.Kp * W) * q := by ring
      _ ≤ 4 * c * g.R * q := mul_le_mul_of_nonneg_right hKW hq
  have key := psc_quad g.Kp y a b c g.L g.R q
  have h3 : 0 ≤ 4 * g.Kp * (g.Kp * (y - c * g.L * b) * (y + a) + c * g.R * q) := by
    rw [key]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hK.le (sub_nonneg.mpr h2))
  have h4 := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * g.Kp)).mp h3
  linarith

/-- **The PSC energy is stationary only at equilibria** under the strict condition
`K_p E² (R² + (X + c L)²) < 4 c R |Z|²` (`K_p > 0`): `Ḣ_c = 0` forces `i = i_s(δ)` and
`P(δ) = P_ref`. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_of_pscEnergy_lie_eq_zero (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hK : 0 < g.Kp) {c : ℝ}
    (hdiss : g.Kp * (g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2)) < 4 * c * g.R * g.absSq)
    {x : State 3} (hx : fderiv ℝ (g.pscEnergy c) x (g.field x) = 0) : g.field x = 0 := by
  rw [g.pscEnergy_lie hL hZ, neg_eq_zero] at hx
  have hW : g.toVSM.couplingD c (x 0) ^ 2 + g.toVSM.couplingQ c (x 0) ^ 2 =
      g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) / g.absSq :=
    g.toVSM.normSq_coupling hZ.ne' c (x 0)
  have hcd := g.coupling_dot c x
  set u := x 1 - (g.is (x 0)).re
  set v := x 2 - (g.is (x 0)).im
  set a := g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)
  set b := u * g.toVSM.isRateD (x 0) + v * g.toVSM.isRateQ (x 0)
  set y := g.qssPower (x 0) - g.Pref
  set q := u ^ 2 + v ^ 2
  set W := g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) / g.absSq
  have hcs : (a + c * g.L * b) ^ 2 ≤ W * q := by
    rw [hcd, ← hW]; exact VSM.cs2 _ _ _ _
  have hKW : g.Kp * W < 4 * c * g.R := by
    simp only [W]; rw [mul_div_assoc', div_lt_iff₀ hZ]; exact hdiss
  have hq : 0 ≤ q := by positivity
  have h2 : g.Kp * (a + c * g.L * b) ^ 2 ≤ g.Kp * W * q := by
    calc g.Kp * (a + c * g.L * b) ^ 2 ≤ g.Kp * (W * q) := mul_le_mul_of_nonneg_left hcs hK.le
      _ = g.Kp * W * q := by ring
  have key := psc_quad g.Kp y a b c g.L g.R q
  rw [hx, mul_zero] at key
  have hq0 : q = 0 := by
    by_contra hne
    have hpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
    have h6 : 0 < (4 * c * g.R - g.Kp * W) * q := mul_pos (by linarith) hpos
    have e : (4 * c * g.R - g.Kp * W) * q = 4 * c * g.R * q - g.Kp * W * q := by ring
    have h7 : 0 < g.Kp * (4 * c * g.R * q - g.Kp * (a + c * g.L * b) ^ 2) :=
      mul_pos hK (by linarith)
    linarith [sq_nonneg (2 * g.Kp * y + g.Kp * (a - c * g.L * b))]
  have hu : u = 0 := by
    have : u ^ 2 = 0 := by linarith [sq_nonneg u, sq_nonneg v]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hv : v = 0 := by
    have : v ^ 2 = 0 := by linarith [sq_nonneg u, sq_nonneg v]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have ha : a = 0 := by simp only [a, hu, hv, mul_zero, add_zero]
  have hb : b = 0 := by simp only [b, hu, hv, zero_mul, add_zero]
  rw [ha, hb, hq0] at key
  have e2 : (2 * g.Kp * y + g.Kp * (0 - c * g.L * 0)) ^ 2 +
      g.Kp * (4 * c * g.R * 0 - g.Kp * (0 + c * g.L * 0) ^ 2) = (2 * g.Kp * y) ^ 2 := by ring
  rw [e2] at key
  have hy : y = 0 := by
    have h8 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key.symm
    rcases mul_eq_zero.mp h8 with h | h
    · exact absurd h (by positivity)
    · exact h
  refine (g.field_eq_zero_iff hK.ne' hL hZ.ne' x).mpr ⟨?_, ?_, ?_⟩
  · simp only [u] at hu; linarith
  · simp only [v] at hv; linarith
  · simp only [y] at hy; linarith

/-- The equilibria `(δ*, i_s(δ*))`, `P(δ*) = P_ref`, are isolated (`K_p ≠ 0`, `E V > 0`). -/
@[tmio M, powerlib_domain] theorem field_zero_isolated (hK : g.Kp ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) (z : State 3) (hz : g.field z = 0) :
    ∃ ε > 0, ∀ y, g.field y = 0 → dist y z < ε → y = z := by
  have hA : g.A ≠ 0 := (div_pos hEV (Real.sqrt_pos.mpr hZ)).ne'
  obtain ⟨hz1, hz2, -⟩ := (g.field_eq_zero_iff hK hL hZ.ne' z).mp hz
  obtain ⟨ε, hε, hiso⟩ :=
    Dynamics.sinusoid_level_isolated (c := g.c0) (α := g.α) (p := g.Pref) hA (z 0)
  refine ⟨ε, hε, fun y hy hyz => ?_⟩
  obtain ⟨hy1, hy2, hy3⟩ := (g.field_eq_zero_iff hK hL hZ.ne' y).mp hy
  have hd : |y 0 - z 0| < ε := by
    have := Dynamics.abs_apply_le_norm (y - z) 0
    simp only [PiLp.sub_apply] at this
    exact lt_of_le_of_lt this (by rwa [← dist_eq_norm])
  have h0 := hiso (y 0) (by rw [← g.qssPower_eq_polar hZ]; exact hy3) hd
  ext i; fin_cases i
  · exact h0
  · simp [hy1, hz1, h0]
  · simp [hy2, hz2, h0]

/-- **Bounded solutions of the line PSC converge** under the strict dissipation condition
`K_p E² (R² + (X + c L)²) < 4 c R |Z|²` (`K_p, L > 0`, `E V > 0`): every bounded forward solution
converges to an equilibrium `qss(δ*) = (δ*, i_s(δ*))` with `P(δ*) = P_ref` (the zero set of the
rate of `H_c` is the equilibrium set). Implementation evidence: trajectory-level result outside
the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem exists_tendsto_of_bounded (hK : 0 < g.Kp)
    (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {c : ℝ}
    (hdiss : g.Kp * (g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2)) < 4 * c * g.R * g.absSq)
    {φ : ℝ → State 3} (hφ : IsIntegralCurveOn φ (fun _ y => g.field y) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ δs, g.qssPower δs = g.Pref ∧ Tendsto φ atTop (𝓝 (g.qss δs)) := by
  obtain ⟨z, hz, hzt⟩ := Dynamics.exists_tendsto_of_bounded g.contDiff_field
    (g.differentiable_pscEnergy c) hφ hb
    (fun t _ => g.pscEnergy_lie_nonpos hL.ne' hZ hK hdiss.le (φ t))
    (fun ψ _ _ h0 => g.field_eq_zero_of_pscEnergy_lie_eq_zero hL.ne' hZ hK hdiss (h0 0 le_rfl))
    (fun z _ hz => g.field_zero_isolated hK.ne' hL.ne' hZ hEV z hz)
  obtain ⟨h1, h2, h3⟩ := (g.field_eq_zero_iff hK.ne' hL.ne' hZ.ne' z).mp hz
  refine ⟨z 0, h3, ?_⟩
  have : z = g.qss (z 0) := by
    ext i; fin_cases i <;> simp [qss, h1, h2]
  rwa [← this]

/-- The well window `δ_u − 2π < δ < δ_u` of the PSC law (`wellParams`). -/
def wellWindow : Set (State 3) :=
  {x | g.wellParams.deltaU - 2 * Real.pi < x 0 ∧ x 0 < g.wellParams.deltaU}

@[tmio M, powerlib_domain] theorem isOpen_wellWindow : IsOpen g.wellWindow :=
  (isOpen_lt continuous_const (Dynamics.contDiff_coord (k := 0) 0).continuous).inter
    (isOpen_lt (Dynamics.contDiff_coord (k := 0) 0).continuous continuous_const)

/-- The PSC energy dominates the potential (`c L ≥ 0`). -/
@[tmio M, powerlib_domain] theorem potential_le_pscEnergy {c : ℝ} (hcL : 0 ≤ c * g.L)
    (x : State 3) : g.wellParams.potential 0 (x 0) ≤ g.pscEnergy c x := by
  have h2 : 0 ≤ c * g.L / 2 * ((x 1 - (g.is (x 0)).re) ^ 2 + (x 2 - (g.is (x 0)).im) ^ 2) := by
    positivity
  simp only [pscEnergy]
  linarith

/-- In the well window the only equilibrium is the operating point `qss(δ_s)`
(`|P_ref − c₀| < A`). -/
@[tmio M, powerlib_domain] theorem eq_point_of_field_eq_zero (hK : g.Kp ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) (h : |g.Pref - g.c0| < g.A) {x : State 3}
    (hx : x ∈ g.wellWindow) (hf : g.field x = 0) : x = g.qss g.wellParams.deltaS := by
  have hA : 0 < g.A := div_pos hEV (Real.sqrt_pos.mpr hZ)
  obtain ⟨h1, h2, h3⟩ := (g.field_eq_zero_iff hK hL hZ.ne' x).mp hf
  have hs := g.wellParams.eq_deltaS_of_field_eq_zero one_ne_zero hA h
    (x := PhasePlane.mk (x 0) 0) ⟨by simpa using hx.1, by simpa using hx.2⟩
    ((g.wellParams.field_eq_zero_iff one_ne_zero _).mpr ⟨by simp, by
      simp only [PhasePlane.mk_apply_zero, Synchronous.SwingParams.Pe, wellParams]
      rw [← g.qssPower_eq_polar hZ]; exact h3⟩)
  have h0 : x 0 = g.wellParams.deltaS := by
    simpa using congrArg (fun y : State 2 => y 0) hs
  ext i; fin_cases i <;> simp [qss, h0, h1, h2]

/-- Sublevel sets of the PSC energy in the well window below both saddle levels are compact
(`L, c > 0`). -/
@[tmio M, powerlib_domain] theorem isCompact_wellSublevel (hL : 0 < g.L) {c : ℝ} (hc : 0 < c)
    {c₁ : ℝ} (hc1 : c₁ < g.wellParams.potential 0 g.wellParams.deltaU)
    (hc2 : c₁ < g.wellParams.potential 0 (g.wellParams.deltaU - 2 * Real.pi)) :
    IsCompact {x ∈ g.wellWindow | g.pscEnergy c x ≤ c₁} := by
  set a := g.wellParams.deltaU - 2 * Real.pi
  set b := g.wellParams.deltaU
  have hab : a ≤ b := by have := Real.pi_pos; simp only [a, b]; linarith
  have hcL : 0 ≤ c * g.L := by positivity
  have hcU : Continuous (g.wellParams.potential 0) := by
    unfold Synchronous.SwingParams.potential; fun_prop
  have hcH : Continuous (g.pscEnergy c) := (g.differentiable_pscEnergy c).continuous
  have hc0 : Continuous fun x : State 3 => x 0 := (Dynamics.contDiff_coord (k := 0) 0).continuous
  have hcis : Continuous g.is := by unfold Network.is; fun_prop
  have hEq : {x ∈ g.wellWindow | g.pscEnergy c x ≤ c₁} =
      {x : State 3 | a ≤ x 0} ∩ {x | x 0 ≤ b} ∩ {x | g.pscEnergy c x ≤ c₁} := by
    ext x
    simp only [wellWindow, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.le, h2.le⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hU := g.potential_le_pscEnergy hcL x
      refine ⟨⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩, h3⟩
      · intro he; rw [← he] at hU; linarith
      · intro he; rw [he] at hU; linarith
  rw [hEq]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact ((isClosed_le continuous_const hc0).inter (isClosed_le hc0 continuous_const)).inter
      (isClosed_le hcH continuous_const)
  obtain ⟨δm, -, hδm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcU.continuousOn
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcis.continuousOn
  set C := c₁ - g.wellParams.potential 0 δm
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨|a| + |b| + 2 * (1 + 2 * C / (c * g.L) + S), ?_⟩
  rintro x ⟨⟨h1, h2⟩, h3⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [mem_ofPred_eq] at h1 h2 h3
  have hU : g.wellParams.potential 0 δm ≤ g.wellParams.potential 0 (x 0) :=
    hδm (show x 0 ∈ Icc a b from ⟨h1, h2⟩)
  have hSx : ‖g.is (x 0)‖ ≤ S := hS (x 0) ⟨h1, h2⟩
  simp only [pscEnergy] at h3
  set u := x 1 - (g.is (x 0)).re
  set v := x 2 - (g.is (x 0)).im
  have hmag : 0 ≤ c * g.L / 2 * (u ^ 2 + v ^ 2) := by positivity
  have huv : u ^ 2 + v ^ 2 ≤ 2 * C / (c * g.L) := by
    rw [le_div_iff₀ (by positivity)]; simp only [C]; nlinarith
  have habs : ∀ w : ℝ, |w| ≤ 1 + w ^ 2 := fun w => by
    rcases abs_cases w with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith [sq_nonneg (w - 1),
      sq_nonneg (w + 1)]
  have hre : |(g.is (x 0)).re| ≤ S := (Complex.abs_re_le_norm _).trans hSx
  have him : |(g.is (x 0)).im| ≤ S := (Complex.abs_im_le_norm _).trans hSx
  have hx1 : |x 1| ≤ 1 + 2 * C / (c * g.L) + S := by
    have : x 1 = u + (g.is (x 0)).re := by simp only [u]; ring
    rw [this]
    have := abs_add_le u (g.is (x 0)).re
    nlinarith [habs u, sq_nonneg v]
  have hx2 : |x 2| ≤ 1 + 2 * C / (c * g.L) + S := by
    have : x 2 = v + (g.is (x 0)).im := by simp only [v]; ring
    rw [this]
    have := abs_add_le v (g.is (x 0)).im
    nlinarith [habs v, sq_nonneg u]
  have hx0 : |x 0| ≤ |a| + |b| := by
    rw [abs_le]; constructor <;>
      cases abs_cases a <;> cases abs_cases b <;> linarith [abs_nonneg a, abs_nonneg b]
  have hnorm := (Dynamics.norm_le_sum_abs x).trans_eq (Fin.sum_univ_three _)
  linarith

/-- **LaSalle on the energy well of the line PSC** (strict dissipation, `K_p, L > 0`, `E V > 0`,
`|P_ref − c₀| < A`): every sublevel set of `H_c` in the well window below both saddle levels lies
in the region of attraction of the operating point `qss(δ_s)` (the zero set of the rate is the
equilibrium set, and the window holds only `qss(δ_s)`). Implementation evidence:
trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem regionOfAttraction_well (hK : 0 < g.Kp)
    (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {c : ℝ} (hc : 0 < c)
    (hdiss : g.Kp * (g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2)) < 4 * c * g.R * g.absSq)
    (h : |g.Pref - g.c0| < g.A) {c₁ : ℝ}
    (hc1 : c₁ < g.wellParams.potential 0 g.wellParams.deltaU)
    (hc2 : c₁ < g.wellParams.potential 0 (g.wellParams.deltaU - 2 * Real.pi)) :
    {x ∈ g.wellWindow | g.pscEnergy c x ≤ c₁} ⊆
      Flow.regionOfAttraction g.field (g.qss g.wellParams.deltaS) := by
  have hHc : ContDiff ℝ 1 (g.pscEnergy c) := by
    unfold pscEnergy Synchronous.SwingParams.potential
    simp only [Network.is_re, Network.is_im]
    fun_prop
  refine Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel g.isOpen_wellWindow
    g.contDiff_field hHc (fun x _ => g.pscEnergy_lie_nonpos hL.ne' hZ hK hdiss.le x)
    (g.isCompact_wellSublevel hL hc hc1 hc2) ?_
  intro N hN _ x hx
  have hx' := hN hx
  rw [Dynamics.LaSalle.lieDerivZeroSet_def] at hx'
  exact g.eq_point_of_field_eq_zero hK.ne' hL.ne' hZ hEV h hx'.1.1
    (g.field_eq_zero_of_pscEnergy_lie_eq_zero hL.ne' hZ hK hdiss hx'.2)

end PSC

/-! ## The VSM with a power filter on the line -/

namespace VSMLPF

variable (g : VSMLPF)

/-- The Lyapunov function of the line VSM + power filter (weights `ε`, `k`):
`V = (M ω_c + D − ε ω_c) U(δ) + M y ω + (M D/2) ω² − ε ω z + z²/(2 ω_c) + (k/2) |ĩ|²`, with
`y = P(δ) − P_ref`, the filter error `z = ω_c M ω + P_ref − P_f` and `ĩ = i − i_s(δ)`. -/
def lyap (ε k : ℝ) (x : State 5) : ℝ :=
  (g.M * g.ωc + g.D - ε * g.ωc) * g.swingParams.potential 0 (x 0) +
    g.M * (g.swingParams.Pe (x 0) - g.Pref) * x 1 + g.M * g.D / 2 * x 1 ^ 2 -
      ε * x 1 * (g.ωc * g.M * x 1 + g.Pref - x 2) +
        (g.ωc * g.M * x 1 + g.Pref - x 2) ^ 2 / (2 * g.ωc) +
          k / 2 * ((x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2)

@[tmio M, powerlib_domain] private theorem hasDerivAt_is_re (δ : ℝ) :
    HasDerivAt (fun δ => (g.is δ).re) (g.isRateD δ) δ := by
  have h := ((((Real.hasDerivAt_cos δ).const_mul g.E).sub_const g.V).const_mul g.R).add
    ((Real.hasDerivAt_sin δ).const_mul g.E |>.const_mul g.X) |>.div_const g.absSq
  convert h using 1
  · funext y; rw [Network.is_re]; rfl
  · simp only [VSM.isRateD]; ring

@[tmio M, powerlib_domain] private theorem hasDerivAt_is_im (δ : ℝ) :
    HasDerivAt (fun δ => (g.is δ).im) (g.isRateQ δ) δ := by
  have h := (((Real.hasDerivAt_sin δ).const_mul g.E).const_mul g.R).sub
    ((((Real.hasDerivAt_cos δ).const_mul g.E).sub_const g.V).const_mul g.X) |>.div_const g.absSq
  convert h using 1
  · funext y; rw [Network.is_im]; rfl
  · simp only [VSM.isRateQ]; ring

/-- The derivative of the Lyapunov function at `x`. -/
def lyapDeriv (ε k : ℝ) (x : State 5) : State 5 →L[ℝ] ℝ :=
  ((g.M * g.ωc + g.D - ε * g.ωc) * (g.swingParams.Pe (x 0) - g.Pref) +
      g.M * g.swingParams.syncCoeff (x 0) * x 1 -
        k * ((x 3 - (g.is (x 0)).re) * g.isRateD (x 0) +
          (x 4 - (g.is (x 0)).im) * g.isRateQ (x 0))) • coord 0 +
    (g.M * (g.swingParams.Pe (x 0) - g.Pref) + g.M * g.D * x 1 -
        ε * (g.ωc * g.M * x 1 + g.Pref - x 2) - ε * (g.ωc * g.M) * x 1 +
          g.M * (g.ωc * g.M * x 1 + g.Pref - x 2)) • coord 1 +
    (ε * x 1 - (g.ωc * g.M * x 1 + g.Pref - x 2) / g.ωc) • coord 2 +
    (k * (x 3 - (g.is (x 0)).re)) • coord 3 + (k * (x 4 - (g.is (x 0)).im)) • coord 4

@[tmio M, powerlib_domain] theorem hasFDerivAt_lyap (hω : g.ωc ≠ 0) (ε k : ℝ) (x : State 5) :
    HasFDerivAt (g.lyap ε k) (g.lyapDeriv ε k x) x := by
  have h0 := Dynamics.hasFDerivAt_coord 0 x
  have h1 := Dynamics.hasFDerivAt_coord 1 x
  have h2 := Dynamics.hasFDerivAt_coord 2 x
  have hU := (g.swingParams.hasDerivAt_potential 0 (x 0)).comp_hasFDerivAt x h0
  have hP := ((g.swingParams.hasDerivAt_Pe (x 0)).comp_hasFDerivAt x h0).sub_const g.Pref
  have hz := ((h1.const_mul (g.ωc * g.M)).add_const g.Pref).sub h2
  have e1 := (Dynamics.hasFDerivAt_coord 3 x).sub
    ((g.hasDerivAt_is_re (x 0)).comp_hasFDerivAt x h0)
  have e2 := (Dynamics.hasFDerivAt_coord 4 x).sub
    ((g.hasDerivAt_is_im (x 0)).comp_hasFDerivAt x h0)
  have h := ((((hU.const_mul (g.M * g.ωc + g.D - ε * g.ωc)).add
    ((hP.const_mul g.M).mul h1)).add ((h1.pow 2).const_mul (g.M * g.D / 2))).sub
      ((h1.const_mul ε).mul hz)).add ((hz.pow 2).const_mul (1 / (2 * g.ωc))) |>.add
        (((e1.mul e1).add (e2.mul e2)).const_mul (k / 2))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
  · simp only [lyap, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  · ext v
    simp only [lyapDeriv, add_apply, smul_apply, sub_apply, Dynamics.coord_apply, smul_eq_mul,
      Pi.sub_apply, Function.comp_apply, VSM.swingParams]
    field_simp
    ring

@[tmio M, powerlib_domain] theorem differentiable_lyap (hω : g.ωc ≠ 0) (ε k : ℝ) :
    Differentiable ℝ (g.lyap ε k) :=
  fun x => (g.hasFDerivAt_lyap hω ε k x).differentiableAt

/-- **The rate of the Lyapunov function** (`M, ω_c, L ≠ 0`, `|Z|² > 0`): with `z`, `ĩ` as in
`lyap`, `a = E (cos δ ĩ_d + sin δ ĩ_q)` (`P_e = P(δ) + a`) and `b = i_s'(δ)·ĩ`,
`V̇ = −(D² + D M ω_c − M P'(δ) − ε ω_c D) ω² − (ε/M) z² + (ε (M ω_c + D)/M) ω z − (k R/L) |ĩ|²`
`− z a + ω (ε ω_c a − k b)`. -/
@[tmio M, powerlib_domain] theorem lyap_lie (hM : g.M ≠ 0) (hω : g.ωc ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (ε k : ℝ) (x : State 5) :
    fderiv ℝ (g.lyap ε k) x (g.field x) =
      -((g.D ^ 2 + g.D * g.M * g.ωc - g.M * g.swingParams.syncCoeff (x 0) - ε * g.ωc * g.D) *
          x 1 ^ 2) - ε / g.M * (g.ωc * g.M * x 1 + g.Pref - x 2) ^ 2 +
        ε * (g.M * g.ωc + g.D) / g.M * x 1 * (g.ωc * g.M * x 1 + g.Pref - x 2) -
        k * g.R / g.L * ((x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2) -
        (g.ωc * g.M * x 1 + g.Pref - x 2) *
          (g.E * (Real.cos (x 0) * (x 3 - (g.is (x 0)).re) +
            Real.sin (x 0) * (x 4 - (g.is (x 0)).im))) +
        x 1 * (ε * g.ωc * (g.E * (Real.cos (x 0) * (x 3 - (g.is (x 0)).re) +
            Real.sin (x 0) * (x 4 - (g.is (x 0)).im))) -
          k * ((x 3 - (g.is (x 0)).re) * g.isRateD (x 0) +
            (x 4 - (g.is (x 0)).im) * g.isRateQ (x 0))) := by
  have hP : g.swingParams.Pe (x 0) = g.qssPower (x 0) := (g.qssPower_eq_polar hZ (x 0)).symm
  have hl := (g.rate_eq_zero_iff hL hZ.ne' (x 0) (g.is (x 0)).re (g.is (x 0)).im).mpr ⟨rfl, rfl⟩
  obtain ⟨hd, hq⟩ := hl
  simp only [Network.rateD, Network.rateQ, div_eq_zero_iff, hL, or_false] at hd hq
  rw [(g.hasFDerivAt_lyap hω ε k x).fderiv]
  simp only [lyapDeriv, hP, add_apply, smul_apply, Dynamics.coord_apply, smul_eq_mul,
    field_apply_zero, field_apply_one, field_apply_two, field_apply_three, field_apply_four,
    Network.rateD, Network.rateQ, Network.qssPower, Network.power_eq]
  field_simp
  linear_combination (g.M * k * (x 3 - (g.is (x 0)).re)) * hd +
    (g.M * k * (x 4 - (g.is (x 0)).im)) * hq

/-- The `ω²` margin `μ = D² + D M ω_c − M A − ε ω_c D − ε (M ω_c + D)²/(2M)` (`A` the amplitude of
`P(δ) = c₀ + A sin(δ − α)`, the largest synchronizing coefficient). -/
def lyapMu (ε : ℝ) : ℝ :=
  g.D ^ 2 + g.D * g.M * g.ωc - g.M * g.A - ε * g.ωc * g.D -
    ε * (g.M * g.ωc + g.D) ^ 2 / (2 * g.M)

/-- The magnetic margin `ν = k R/L − M E²/(2ε)`. -/
def lyapNu (ε k : ℝ) : ℝ := k * g.R / g.L - g.M * g.E ^ 2 / (2 * ε)

/-- The squared size `Γ² = E² (ε² ω_c² − 2 ε ω_c k X/|Z|² + k²/|Z|²)` of the coupling vector
`ε ω_c E e^{jδ} − k i_s'(δ)` (angle-independent). -/
def lyapGammaSq (ε k : ℝ) : ℝ :=
  g.E ^ 2 * (ε ^ 2 * g.ωc ^ 2 - 2 * ε * g.ωc * k * g.X / g.absSq + k ^ 2 / g.absSq)

/-- The coupling vector of the rate has the angle-independent size `Γ²`. -/
@[tmio M, powerlib_domain] theorem normSq_lyapCoupling (hZ : g.absSq ≠ 0) (ε k δ : ℝ) :
    (ε * g.ωc * (g.E * Real.cos δ) - k * g.isRateD δ) ^ 2 +
        (ε * g.ωc * (g.E * Real.sin δ) - k * g.isRateQ δ) ^ 2 = g.lyapGammaSq ε k := by
  have hZ' : g.R ^ 2 + g.X ^ 2 ≠ 0 := hZ
  simp only [lyapGammaSq, VSM.isRateD, VSM.isRateQ]
  unfold Network.absSq at hZ ⊢
  field_simp
  linear_combination (g.E ^ 2 * ((ε * g.ωc * (g.R ^ 2 + g.X ^ 2) - k * g.X) ^ 2 +
    (k * g.R) ^ 2)) * Real.sin_sq_add_cos_sq δ

/-- The algebra of the rate bound: with `a² ≤ E₂ q`, `c² ≤ G q`, `μ ≤ m − ε b²/(2M)` and
`ν ≤ κ − M E₂/(2ε)`, the rate `S = m ω² + (ε/M) z² − (ε b/M) ω z + κ q + z a − ω c` dominates
`μ ω² + ν q − ω c`, and `4μ (μ ω² + ν q − ω c) ≥ (4μν − G) q`. -/
@[tmio T, powerlib_foundation] private theorem lyap_core {m μ ν G ε M b κ E2 ω z a c q : ℝ}
    (hM : 0 < M) (hε : 0 < ε) (hq : 0 ≤ q) (hm : μ ≤ m - ε * b ^ 2 / (2 * M))
    (hν : ν ≤ κ - M * E2 / (2 * ε)) (ha : a ^ 2 ≤ E2 * q) (hc : c ^ 2 ≤ G * q) :
    μ * ω ^ 2 + ν * q - ω * c ≤
        m * ω ^ 2 + ε / M * z ^ 2 - ε * b / M * ω * z + κ * q + z * a - ω * c ∧
      (4 * μ * ν - G) * q ≤ 4 * μ * (μ * ω ^ 2 + ν * q - ω * c) := by
  constructor
  · have key : ε / (2 * M) * (z - b * ω) ^ 2 + ε / (2 * M) * (z + M / ε * a) ^ 2 =
        ε * b ^ 2 / (2 * M) * ω ^ 2 + ε / M * z ^ 2 - ε * b / M * ω * z + M / (2 * ε) * a ^ 2 +
          z * a := by
      field_simp; ring
    have h1 : 0 ≤ ε / (2 * M) * (z - b * ω) ^ 2 := by positivity
    have h2 : 0 ≤ ε / (2 * M) * (z + M / ε * a) ^ 2 := by positivity
    have h3 : (μ - (m - ε * b ^ 2 / (2 * M))) * ω ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg ω)
    have h4 : (ν - (κ - M * E2 / (2 * ε))) * q ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hq
    have h5 : M / (2 * ε) * a ^ 2 ≤ M / (2 * ε) * (E2 * q) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    have e1 : M / (2 * ε) * (E2 * q) = M * E2 / (2 * ε) * q := by ring
    nlinarith
  · nlinarith [sq_nonneg (2 * μ * ω - c)]

/-- The rate bounds at a state (`M, ω_c, L > 0`, `|Z|² > 0`, `E V > 0`, `ε > 0`): with
`S = −V̇`, `μ ω² + ν |ĩ|² − ω c ≤ S` and `(4μν − Γ²) |ĩ|² ≤ 4μ (μ ω² + ν |ĩ|² − ω c)`, where
`c = ε ω_c a − k b`. -/
@[tmio M, powerlib_domain] private theorem lyap_bounds (hM : 0 < g.M) (hω : 0 < g.ωc)
    (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {ε k : ℝ} (hε : 0 < ε)
    (x : State 5) :
    g.lyapMu ε * x 1 ^ 2 + g.lyapNu ε k *
          ((x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2) -
        x 1 * (ε * g.ωc * (g.E * (Real.cos (x 0) * (x 3 - (g.is (x 0)).re) +
            Real.sin (x 0) * (x 4 - (g.is (x 0)).im))) -
          k * ((x 3 - (g.is (x 0)).re) * g.isRateD (x 0) +
            (x 4 - (g.is (x 0)).im) * g.isRateQ (x 0))) ≤
        -fderiv ℝ (g.lyap ε k) x (g.field x) ∧
      (4 * g.lyapMu ε * g.lyapNu ε k - g.lyapGammaSq ε k) *
          ((x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2) ≤
        4 * g.lyapMu ε * (g.lyapMu ε * x 1 ^ 2 + g.lyapNu ε k *
          ((x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2) -
        x 1 * (ε * g.ωc * (g.E * (Real.cos (x 0) * (x 3 - (g.is (x 0)).re) +
            Real.sin (x 0) * (x 4 - (g.is (x 0)).im))) -
          k * ((x 3 - (g.is (x 0)).re) * g.isRateD (x 0) +
            (x 4 - (g.is (x 0)).im) * g.isRateQ (x 0)))) := by
  rw [g.lyap_lie hM.ne' hω.ne' hL.ne' hZ]
  set u := x 3 - (g.is (x 0)).re
  set v := x 4 - (g.is (x 0)).im
  have hA : 0 ≤ g.A := (div_pos hEV (Real.sqrt_pos.mpr hZ)).le
  have hsync : g.swingParams.syncCoeff (x 0) ≤ g.A := by
    simp only [Synchronous.SwingParams.syncCoeff, VSM.swingParams]
    nlinarith [Real.cos_le_one (x 0 - g.α)]
  have ha : (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) ^ 2 ≤ g.E ^ 2 * (u ^ 2 + v ^ 2) := by
    have h := VSM.cs2 (g.E * Real.cos (x 0)) (g.E * Real.sin (x 0)) u v
    have hs := Real.sin_sq_add_cos_sq (x 0)
    have e1 : (g.E * Real.cos (x 0)) ^ 2 + (g.E * Real.sin (x 0)) ^ 2 = g.E ^ 2 := by
      linear_combination g.E ^ 2 * hs
    rw [e1] at h
    calc (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) ^ 2
        = (g.E * Real.cos (x 0) * u + g.E * Real.sin (x 0) * v) ^ 2 := by ring
      _ ≤ g.E ^ 2 * (u ^ 2 + v ^ 2) := h
  have hc : (ε * g.ωc * (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) -
      k * (u * g.isRateD (x 0) + v * g.isRateQ (x 0))) ^ 2 ≤
      g.lyapGammaSq ε k * (u ^ 2 + v ^ 2) := by
    have h := VSM.cs2 (ε * g.ωc * (g.E * Real.cos (x 0)) - k * g.isRateD (x 0))
      (ε * g.ωc * (g.E * Real.sin (x 0)) - k * g.isRateQ (x 0)) u v
    rw [g.normSq_lyapCoupling hZ.ne'] at h
    calc _ = ((ε * g.ωc * (g.E * Real.cos (x 0)) - k * g.isRateD (x 0)) * u +
          (ε * g.ωc * (g.E * Real.sin (x 0)) - k * g.isRateQ (x 0)) * v) ^ 2 := by ring
      _ ≤ _ := h
  have hcore := lyap_core (m := g.D ^ 2 + g.D * g.M * g.ωc - g.M * g.swingParams.syncCoeff (x 0) -
      ε * g.ωc * g.D) (μ := g.lyapMu ε) (ν := g.lyapNu ε k) (b := g.M * g.ωc + g.D)
    (κ := k * g.R / g.L) (ω := x 1) (z := g.ωc * g.M * x 1 + g.Pref - x 2) hM hε
    (by positivity) (by
      simp only [lyapMu]
      nlinarith [mul_le_mul_of_nonneg_left hsync hM.le]) (le_of_eq (by simp only [lyapNu]))
    ha hc
  refine ⟨?_, hcore.2⟩
  have e : -(-((g.D ^ 2 + g.D * g.M * g.ωc - g.M * g.swingParams.syncCoeff (x 0) -
      ε * g.ωc * g.D) * x 1 ^ 2) - ε / g.M * (g.ωc * g.M * x 1 + g.Pref - x 2) ^ 2 +
        ε * (g.M * g.ωc + g.D) / g.M * x 1 * (g.ωc * g.M * x 1 + g.Pref - x 2) -
        k * g.R / g.L * (u ^ 2 + v ^ 2) -
        (g.ωc * g.M * x 1 + g.Pref - x 2) * (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) +
        x 1 * (ε * g.ωc * (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) -
          k * (u * g.isRateD (x 0) + v * g.isRateQ (x 0)))) =
      (g.D ^ 2 + g.D * g.M * g.ωc - g.M * g.swingParams.syncCoeff (x 0) - ε * g.ωc * g.D) *
          x 1 ^ 2 + ε / g.M * (g.ωc * g.M * x 1 + g.Pref - x 2) ^ 2 -
        ε * (g.M * g.ωc + g.D) / g.M * x 1 * (g.ωc * g.M * x 1 + g.Pref - x 2) +
        k * g.R / g.L * (u ^ 2 + v ^ 2) +
        (g.ωc * g.M * x 1 + g.Pref - x 2) * (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) -
        x 1 * (ε * g.ωc * (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) -
          k * (u * g.isRateD (x 0) + v * g.isRateQ (x 0))) := by ring
  rw [e]
  exact hcore.1

/-- **The Lyapunov function does not increase** (`M, ω_c, L > 0`, `|Z|² > 0`, `E V > 0`) under the
explicit condition: some weights `ε, k` with `ε > 0`, `μ > 0`, `ν > 0` and `Γ² < 4 μ ν`
(`lyapMu`, `lyapNu`, `lyapGammaSq`). -/
@[tmio M, powerlib_domain] theorem lyap_lie_nonpos (hM : 0 < g.M) (hω : 0 < g.ωc)
    (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {ε k : ℝ} (hε : 0 < ε)
    (hμ : 0 < g.lyapMu ε) (hΓ : g.lyapGammaSq ε k < 4 * g.lyapMu ε * g.lyapNu ε k)
    (x : State 5) : fderiv ℝ (g.lyap ε k) x (g.field x) ≤ 0 := by
  obtain ⟨h1, h2⟩ := g.lyap_bounds hM hω hL hZ hEV (k := k) hε x
  have hq : 0 ≤ (x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2 := by positivity
  have h3 := mul_nonneg (sub_nonneg.mpr hΓ.le) hq
  have h4 := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * g.lyapMu ε)).mp
    (h3.trans h2)
  linarith

/-- **The Lyapunov function is stationary only at rest** under the same condition: `V̇ = 0`
forces `ω = 0`, `P_f = P_ref` and `i = i_s(δ)`. -/
@[tmio M, powerlib_domain] theorem eq_of_lyap_lie_eq_zero (hM : 0 < g.M) (hω : 0 < g.ωc)
    (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {ε k : ℝ} (hε : 0 < ε)
    (hμ : 0 < g.lyapMu ε) (hΓ : g.lyapGammaSq ε k < 4 * g.lyapMu ε * g.lyapNu ε k)
    {x : State 5} (hx : fderiv ℝ (g.lyap ε k) x (g.field x) = 0) :
    x 1 = 0 ∧ x 2 = g.Pref ∧ x 3 = (g.is (x 0)).re ∧ x 4 = (g.is (x 0)).im := by
  obtain ⟨h1, h2⟩ := g.lyap_bounds hM hω hL hZ hEV (k := k) hε x
  rw [hx, neg_zero] at h1
  set u := x 3 - (g.is (x 0)).re
  set v := x 4 - (g.is (x 0)).im
  have hq : 0 ≤ u ^ 2 + v ^ 2 := by positivity
  have hq0 : u ^ 2 + v ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < u ^ 2 + v ^ 2 := lt_of_le_of_ne hq (Ne.symm hne)
    have h5 := mul_pos (sub_pos.mpr hΓ) hpos
    have h6 : 4 * g.lyapMu ε * (g.lyapMu ε * x 1 ^ 2 + g.lyapNu ε k * (u ^ 2 + v ^ 2) -
        x 1 * (ε * g.ωc * (g.E * (Real.cos (x 0) * u + Real.sin (x 0) * v)) -
          k * (u * g.isRateD (x 0) + v * g.isRateQ (x 0)))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    linarith
  have hu : u = 0 := by
    have : u ^ 2 = 0 := by linarith [sq_nonneg u, sq_nonneg v]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hv : v = 0 := by
    have : v ^ 2 = 0 := by linarith [sq_nonneg u, sq_nonneg v]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  rw [hu, hv] at h1
  have hw : x 1 = 0 := by
    have : g.lyapMu ε * x 1 ^ 2 ≤ 0 := by
      have e : g.lyapMu ε * x 1 ^ 2 + g.lyapNu ε k * (0 ^ 2 + 0 ^ 2) -
          x 1 * (ε * g.ωc * (g.E * (Real.cos (x 0) * 0 + Real.sin (x 0) * 0)) -
            k * (0 * g.isRateD (x 0) + 0 * g.isRateQ (x 0))) = g.lyapMu ε * x 1 ^ 2 := by ring
      linarith
    have : x 1 ^ 2 = 0 := le_antisymm (nonpos_of_mul_nonpos_right this hμ) (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hz := hx
  rw [g.lyap_lie hM.ne' hω.ne' hL.ne' hZ] at hz
  simp only [← show u = x 3 - (g.is (x 0)).re from rfl, ← show v = x 4 - (g.is (x 0)).im from rfl,
    hu, hv, hw] at hz
  have hz2 : ε / g.M * (g.Pref - x 2) ^ 2 = 0 := by linarith
  have hz3 : (g.Pref - x 2) ^ 2 = 0 :=
    (mul_eq_zero.mp hz2).resolve_left (div_pos hε hM).ne'
  have hP := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz3
  exact ⟨hw, by linarith, by simp only [u] at hu; linarith, by simp only [v] at hv; linarith⟩

/-! ### Isolated equilibria and bounded solutions -/

/-- The equilibria `(δ*, 0, P_ref, i_s(δ*))`, `P(δ*) = P_ref`, are isolated (`E V > 0`). -/
@[tmio M, powerlib_domain] theorem field_zero_isolated (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (hL : g.L ≠ 0) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) (z : State 5) (hz : g.field z = 0) :
    ∃ ε > 0, ∀ y, g.field y = 0 → dist y z < ε → y = z := by
  have hA : g.A ≠ 0 := (div_pos hEV (Real.sqrt_pos.mpr hZ)).ne'
  obtain ⟨hz1, hz2, hz3, hz4, -⟩ := (g.field_eq_zero_iff hM hω hL hZ.ne' z).mp hz
  obtain ⟨ε, hε, hiso⟩ :=
    Dynamics.sinusoid_level_isolated (c := g.c0) (α := g.α) (p := g.Pref) hA (z 0)
  refine ⟨ε, hε, fun y hy hyz => ?_⟩
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := (g.field_eq_zero_iff hM hω hL hZ.ne' y).mp hy
  have hd : |y 0 - z 0| < ε := by
    have := Dynamics.abs_apply_le_norm (y - z) 0
    simp only [PiLp.sub_apply] at this
    exact lt_of_le_of_lt this (by rwa [← dist_eq_norm])
  have h0 := hiso (y 0) (by rw [← g.qssPower_eq_polar hZ]; exact hy5) hd
  ext i; fin_cases i
  · exact h0
  · simp [hy1, hz1]
  · simp [hy2, hz2]
  · simp [hy3, hz3, h0]
  · simp [hy4, hz4, h0]

/-- **Bounded solutions of the line VSM + power filter converge** under the explicit condition
(`M, ω_c, L > 0`, `|Z|² > 0`, `E V > 0`, weights `ε > 0`, `k` with `μ > 0`, `Γ² < 4 μ ν`): every
bounded forward solution converges to an equilibrium `qss(δ*, 0, P_ref)` with `P(δ*) = P_ref`
(`V̇ = 0` forces `ω = 0`, `P_f = P_ref`, `i = i_s(δ)`; then `Ṗ_f = 0` is power balance).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem exists_tendsto_of_bounded (hM : 0 < g.M)
    (hω : 0 < g.ωc) (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {ε k : ℝ}
    (hε : 0 < ε) (hμ : 0 < g.lyapMu ε) (hΓ : g.lyapGammaSq ε k < 4 * g.lyapMu ε * g.lyapNu ε k)
    {φ : ℝ → State 5} (hφ : IsIntegralCurveOn φ (fun _ y => g.field y) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ δs, g.qssPower δs = g.Pref ∧
      Tendsto φ atTop (𝓝 (g.qss (Dynamics.mk3 δs 0 g.Pref))) := by
  obtain ⟨z, hz, hzt⟩ := Dynamics.exists_tendsto_of_bounded g.contDiff_field
    (g.differentiable_lyap hω.ne' ε k) hφ hb
    (fun t _ => g.lyap_lie_nonpos hM hω hL hZ hEV hε hμ hΓ (φ t))
    (fun ψ hψ _ h0 => by
      have hr : ∀ t, 0 ≤ t → ψ t 1 = 0 ∧ ψ t 2 = g.Pref ∧ ψ t 3 = (g.is (ψ t 0)).re ∧
          ψ t 4 = (g.is (ψ t 0)).im := fun t ht =>
        g.eq_of_lyap_lie_eq_zero hM hω hL hZ hEV hε hμ hΓ (h0 t ht)
      have h2 := Dynamics.field_apply_eq_zero_of_coord_const hψ 2 (fun t ht => (hr t ht).2.1)
        le_rfl
      obtain ⟨r1, r2, r3, r4⟩ := hr 0 le_rfl
      rw [field_apply_two, mul_eq_zero, or_iff_right hω.ne', sub_eq_zero, r2] at h2
      exact (g.field_eq_zero_iff hM.ne' hω.ne' hL.ne' hZ.ne' _).mpr
        ⟨r1, r2, r3, r4, by rw [Network.qssPower, ← r3, ← r4]; exact h2⟩)
    (fun z _ hz => g.field_zero_isolated hM.ne' hω.ne' hL.ne' hZ hEV z hz)
  obtain ⟨h1, h2, h3, h4, h5⟩ := (g.field_eq_zero_iff hM.ne' hω.ne' hL.ne' hZ.ne' z).mp hz
  refine ⟨z 0, h5, ?_⟩
  have : z = g.qss (Dynamics.mk3 (z 0) 0 g.Pref) := by
    ext i; fin_cases i <;> simp [qss, h1, h2, h3, h4]
  rwa [← this]

/-! ### The potential well and its region of attraction -/

/-- The well potential `W(δ) = (M ω_c + D − ε ω_c) U(δ) − M² (P(δ) − P_ref)²/(2 (M D − ε² ω_c))`. -/
def lyapWell (ε : ℝ) (δ : ℝ) : ℝ :=
  (g.M * g.ωc + g.D - ε * g.ωc) * g.swingParams.potential 0 δ -
    g.M ^ 2 * (g.swingParams.Pe δ - g.Pref) ^ 2 / (2 * (g.M * g.D - ε ^ 2 * g.ωc))

/-- The well form `V = W(δ) + ((M D − ε² ω_c)/2)(ω + M y/(M D − ε² ω_c))² + (z − ε ω_c ω)²/(2 ω_c)`
`+ (k/2) |ĩ|²` (`ω_c ≠ 0`, `M D ≠ ε² ω_c`). -/
@[tmio M, powerlib_domain] theorem lyap_eq_well (hω : g.ωc ≠ 0)
    {ε : ℝ} (hMD : g.M * g.D - ε ^ 2 * g.ωc ≠ 0) (k : ℝ) (x : State 5) :
    g.lyap ε k x = g.lyapWell ε (x 0) +
      (g.M * g.D - ε ^ 2 * g.ωc) / 2 * (x 1 + g.M * (g.swingParams.Pe (x 0) - g.Pref) /
        (g.M * g.D - ε ^ 2 * g.ωc)) ^ 2 +
      (g.ωc * g.M * x 1 + g.Pref - x 2 - ε * g.ωc * x 1) ^ 2 / (2 * g.ωc) +
      k / 2 * ((x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2) := by
  simp only [lyap, lyapWell]
  set κ := g.M * g.D - ε ^ 2 * g.ωc with hκ
  set y := g.swingParams.Pe (x 0) - g.Pref
  have e1 : κ / 2 * (x 1 + g.M * y / κ) ^ 2 =
      κ / 2 * x 1 ^ 2 + g.M * y * x 1 + g.M ^ 2 * y ^ 2 / (2 * κ) := by
    field_simp; ring
  have e2 : (g.ωc * g.M * x 1 + g.Pref - x 2 - ε * g.ωc * x 1) ^ 2 / (2 * g.ωc) =
      (g.ωc * g.M * x 1 + g.Pref - x 2) ^ 2 / (2 * g.ωc) -
        ε * x 1 * (g.ωc * g.M * x 1 + g.Pref - x 2) + ε ^ 2 * g.ωc / 2 * x 1 ^ 2 := by
    field_simp; ring
  rw [e1, e2, hκ]
  ring

/-- The well potential bounds the Lyapunov function from below (`ω_c > 0`, `M D > ε² ω_c`,
`k ≥ 0`). -/
@[tmio M, powerlib_domain] theorem lyapWell_le_lyap (hω : 0 < g.ωc) {ε : ℝ}
    (hMD : 0 < g.M * g.D - ε ^ 2 * g.ωc) {k : ℝ} (hk : 0 ≤ k) (x : State 5) :
    g.lyapWell ε (x 0) ≤ g.lyap ε k x := by
  rw [g.lyap_eq_well hω.ne' hMD.ne' k x]
  have h1 : 0 ≤ (g.M * g.D - ε ^ 2 * g.ωc) / 2 * (x 1 + g.M * (g.swingParams.Pe (x 0) - g.Pref) /
      (g.M * g.D - ε ^ 2 * g.ωc)) ^ 2 := by positivity
  have h2 : 0 ≤ (g.ωc * g.M * x 1 + g.Pref - x 2 - ε * g.ωc * x 1) ^ 2 / (2 * g.ωc) := by
    positivity
  have h3 : 0 ≤ k / 2 * ((x 3 - (g.is (x 0)).re) ^ 2 + (x 4 - (g.is (x 0)).im) ^ 2) := by
    positivity
  linarith

/-- The well window `δ_u − 2π < δ < δ_u` of the reduced swing machine `swingParams`. -/
def wellWindow : Set (State 5) :=
  {x | g.swingParams.deltaU - 2 * Real.pi < x 0 ∧ x 0 < g.swingParams.deltaU}

@[tmio M, powerlib_domain] theorem isOpen_wellWindow : IsOpen g.wellWindow :=
  (isOpen_lt continuous_const (Dynamics.contDiff_coord (k := 0) 0).continuous).inter
    (isOpen_lt (Dynamics.contDiff_coord (k := 0) 0).continuous continuous_const)

/-- In the well window the only equilibrium is the operating point `qss(δ_s, 0, P_ref)`
(`|P_ref − c₀| < A`). -/
@[tmio M, powerlib_domain] theorem eq_point_of_field_eq_zero (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (hL : g.L ≠ 0) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) (h : |g.Pref - g.c0| < g.A)
    {x : State 5} (hx : x ∈ g.wellWindow) (hf : g.field x = 0) :
    x = g.qss (Dynamics.mk3 g.swingParams.deltaS 0 g.Pref) := by
  have hA : 0 < g.A := div_pos hEV (Real.sqrt_pos.mpr hZ)
  obtain ⟨h1, h2, h3, h4, h5⟩ := (g.field_eq_zero_iff hM hω hL hZ.ne' x).mp hf
  have hs := g.swingParams.eq_deltaS_of_field_eq_zero hM hA h (x := PhasePlane.mk (x 0) 0)
    ⟨by simpa using hx.1, by simpa using hx.2⟩
    ((g.swingParams.field_eq_zero_iff hM _).mpr ⟨by simp, by
      simp only [PhasePlane.mk_apply_zero, Synchronous.SwingParams.Pe, VSM.swingParams]
      rw [← g.qssPower_eq_polar hZ]; exact h5⟩)
  have h0 : x 0 = g.swingParams.deltaS := by
    simpa using congrArg (fun y : State 2 => y 0) hs
  ext i; fin_cases i <;> simp [qss, h0, h1, h2, h3, h4]

/-- Sublevel sets of the Lyapunov function in the well window below both saddle levels
`W(δ_u)`, `W(δ_u − 2π)` are compact (`M, ω_c > 0`, `ε > 0`, `M D > ε² ω_c`, `k > 0`). -/
@[tmio M, powerlib_domain] theorem isCompact_wellSublevel (hM : 0 < g.M) (hω : 0 < g.ωc)
    {ε k : ℝ} (hε : 0 < ε) (hMD : 0 < g.M * g.D - ε ^ 2 * g.ωc) (hk : 0 < k) {c₁ : ℝ}
    (hc1 : c₁ < g.lyapWell ε g.swingParams.deltaU)
    (hc2 : c₁ < g.lyapWell ε (g.swingParams.deltaU - 2 * Real.pi)) :
    IsCompact {x ∈ g.wellWindow | g.lyap ε k x ≤ c₁} := by
  set a := g.swingParams.deltaU - 2 * Real.pi
  set b := g.swingParams.deltaU
  set κ := g.M * g.D - ε ^ 2 * g.ωc
  have hab : a ≤ b := by have := Real.pi_pos; simp only [a, b]; linarith
  have hcW : Continuous (g.lyapWell ε) := by
    unfold lyapWell Synchronous.SwingParams.potential Synchronous.SwingParams.Pe; fun_prop
  have hcV : Continuous (g.lyap ε k) := (g.differentiable_lyap hω.ne' ε k).continuous
  have hc0 : Continuous fun x : State 5 => x 0 := (Dynamics.contDiff_coord (k := 0) 0).continuous
  have hcis : Continuous g.is := by unfold Network.is; fun_prop
  have hcy : Continuous fun δ => g.swingParams.Pe δ - g.Pref := by
    unfold Synchronous.SwingParams.Pe; fun_prop
  have hEq : {x ∈ g.wellWindow | g.lyap ε k x ≤ c₁} =
      {x : State 5 | a ≤ x 0} ∩ {x | x 0 ≤ b} ∩ {x | g.lyap ε k x ≤ c₁} := by
    ext x
    simp only [wellWindow, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.le, h2.le⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hW := g.lyapWell_le_lyap hω hMD hk.le x
      refine ⟨⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩, h3⟩
      · intro he; rw [← he] at hW; linarith
      · intro he; rw [he] at hW; linarith
  rw [hEq]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact ((isClosed_le continuous_const hc0).inter (isClosed_le hc0 continuous_const)).inter
      (isClosed_le hcV continuous_const)
  obtain ⟨δm, -, hδm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcW.continuousOn
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcis.continuousOn
  obtain ⟨Y, hY⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcy.continuousOn
  set C := c₁ - g.lyapWell ε δm
  set X1 := 1 + 2 * C / κ + g.M * |Y| / κ
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨|a| + |b| + X1 + (g.ωc * g.M * X1 + |g.Pref| + (1 + 2 * g.ωc * C) + ε * g.ωc * X1) +
    2 * (1 + 2 * C / k + S), ?_⟩
  rintro x ⟨⟨h1, h2⟩, h3⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [mem_ofPred_eq] at h1 h2 h3
  have hW : g.lyapWell ε δm ≤ g.lyapWell ε (x 0) := hδm (show x 0 ∈ Icc a b from ⟨h1, h2⟩)
  have hSx : ‖g.is (x 0)‖ ≤ S := hS (x 0) ⟨h1, h2⟩
  have hYx : ‖g.swingParams.Pe (x 0) - g.Pref‖ ≤ Y := hY (x 0) ⟨h1, h2⟩
  rw [Real.norm_eq_abs] at hYx
  rw [g.lyap_eq_well hω.ne' hMD.ne' k x] at h3
  set y := g.swingParams.Pe (x 0) - g.Pref
  set p := x 1 + g.M * y / κ
  set r := g.ωc * g.M * x 1 + g.Pref - x 2 - ε * g.ωc * x 1
  set u := x 3 - (g.is (x 0)).re
  set v := x 4 - (g.is (x 0)).im
  have hp0 : 0 ≤ κ / 2 * p ^ 2 := by positivity
  have hr0 : 0 ≤ r ^ 2 / (2 * g.ωc) := by positivity
  have huv0 : 0 ≤ k / 2 * (u ^ 2 + v ^ 2) := by positivity
  have hp : p ^ 2 ≤ 2 * C / κ := by
    rw [le_div_iff₀ hMD]; simp only [C]; linarith
  have hr : r ^ 2 ≤ 2 * g.ωc * C := by
    have : r ^ 2 / (2 * g.ωc) ≤ C := by simp only [C]; linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have huv : u ^ 2 + v ^ 2 ≤ 2 * C / k := by
    rw [le_div_iff₀ hk]; simp only [C]; linarith
  have habs : ∀ w : ℝ, |w| ≤ 1 + w ^ 2 := fun w => by
    rcases abs_cases w with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith [sq_nonneg (w - 1),
      sq_nonneg (w + 1)]
  have hx1 : |x 1| ≤ X1 := by
    have e : x 1 = p - g.M * y / κ := by simp only [p]; ring
    have hy : |g.M * y / κ| ≤ g.M * |Y| / κ := by
      rw [abs_div, abs_mul, abs_of_pos hM, abs_of_pos hMD]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hYx.trans (le_abs_self Y)) hM.le) hMD.le
    rw [e]
    calc |p - g.M * y / κ| ≤ |p| + |g.M * y / κ| := abs_sub _ _
      _ ≤ X1 := by simp only [X1]; linarith [habs p]
  have hx2 : |x 2| ≤ g.ωc * g.M * X1 + |g.Pref| + (1 + 2 * g.ωc * C) + ε * g.ωc * X1 := by
    have e : x 2 = g.ωc * g.M * x 1 + g.Pref - r - ε * g.ωc * x 1 := by simp only [r]; ring
    rw [e]
    have hωM : 0 < g.ωc * g.M := mul_pos hω hM
    have hεω : 0 < ε * g.ωc := mul_pos hε hω
    have t1 : |g.ωc * g.M * x 1| ≤ g.ωc * g.M * X1 := by
      rw [abs_mul, abs_of_pos hωM]; exact mul_le_mul_of_nonneg_left hx1 hωM.le
    have t2 : |ε * g.ωc * x 1| ≤ ε * g.ωc * X1 := by
      rw [abs_mul, abs_of_pos hεω]; exact mul_le_mul_of_nonneg_left hx1 hεω.le
    have t3 : |r| ≤ 1 + 2 * g.ωc * C := (habs r).trans (by linarith)
    calc |g.ωc * g.M * x 1 + g.Pref - r - ε * g.ωc * x 1|
        ≤ |g.ωc * g.M * x 1| + |g.Pref| + |r| + |ε * g.ωc * x 1| := by
          have := abs_sub (g.ωc * g.M * x 1 + g.Pref - r) (ε * g.ωc * x 1)
          have := abs_sub (g.ωc * g.M * x 1 + g.Pref) r
          have := abs_add_le (g.ωc * g.M * x 1) g.Pref
          linarith
      _ ≤ _ := by linarith
  have hre : |(g.is (x 0)).re| ≤ S := (Complex.abs_re_le_norm _).trans hSx
  have him : |(g.is (x 0)).im| ≤ S := (Complex.abs_im_le_norm _).trans hSx
  have hx3 : |x 3| ≤ 1 + 2 * C / k + S := by
    have e : x 3 = u + (g.is (x 0)).re := by simp only [u]; ring
    rw [e]
    have := abs_add_le u (g.is (x 0)).re
    linarith [habs u, sq_nonneg v]
  have hx4 : |x 4| ≤ 1 + 2 * C / k + S := by
    have e : x 4 = v + (g.is (x 0)).im := by simp only [v]; ring
    rw [e]
    have := abs_add_le v (g.is (x 0)).im
    linarith [habs v, sq_nonneg u]
  have hx0 : |x 0| ≤ |a| + |b| := by
    rw [abs_le]; constructor <;>
      cases abs_cases a <;> cases abs_cases b <;> linarith [abs_nonneg a, abs_nonneg b]
  have hnorm := (Dynamics.norm_le_sum_abs x).trans_eq (Fin.sum_univ_five _)
  linarith

/-- **LaSalle on the well of the line VSM + power filter** (the conditions of
`exists_tendsto_of_bounded`, `M D > ε² ω_c`, `k > 0`, `|P_ref − c₀| < A`): every sublevel set of
`V` in the well window below both saddle levels `W(δ_u)`, `W(δ_u − 2π)` lies in the region of
attraction of the operating point `qss(δ_s, 0, P_ref)` (on the zero set of `V̇`: `ω = 0`,
`P_f = P_ref`, `i = i_s(δ)`; there `Ṗ_f = 0` is power balance). Implementation evidence:
trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem regionOfAttraction_well (hM : 0 < g.M)
    (hω : 0 < g.ωc) (hL : 0 < g.L) (hZ : 0 < g.absSq) (hEV : 0 < g.E * g.V) {ε k : ℝ}
    (hε : 0 < ε) (hμ : 0 < g.lyapMu ε) (hΓ : g.lyapGammaSq ε k < 4 * g.lyapMu ε * g.lyapNu ε k)
    (hMD : 0 < g.M * g.D - ε ^ 2 * g.ωc) (hk : 0 < k) (h : |g.Pref - g.c0| < g.A) {c₁ : ℝ}
    (hc1 : c₁ < g.lyapWell ε g.swingParams.deltaU)
    (hc2 : c₁ < g.lyapWell ε (g.swingParams.deltaU - 2 * Real.pi)) :
    {x ∈ g.wellWindow | g.lyap ε k x ≤ c₁} ⊆
      Flow.regionOfAttraction g.field (g.qss (Dynamics.mk3 g.swingParams.deltaS 0 g.Pref)) := by
  have hVc : ContDiff ℝ 1 (g.lyap ε k) := by
    unfold lyap Synchronous.SwingParams.potential Synchronous.SwingParams.Pe
    simp only [Network.is_re, Network.is_im]
    fun_prop
  refine Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel g.isOpen_wellWindow
    g.contDiff_field hVc (fun x _ => g.lyap_lie_nonpos hM hω hL hZ hEV hε hμ hΓ x)
    (g.isCompact_wellSublevel hM hω hε hMD hk hc1 hc2) ?_
  refine Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem g.contDiff_field
    ((Dynamics.contDiff_coord (n := 5) (k := 1) 2).sub contDiff_const)
    (h := fun x : State 5 => x 2 - g.Pref) (fun x hx => ?_) (fun x hx hd => ?_)
  · rw [Dynamics.LaSalle.lieDerivZeroSet_def] at hx
    exact sub_eq_zero.mpr (g.eq_of_lyap_lie_eq_zero hM hω hL hZ hEV hε hμ hΓ hx.2).2.1
  · rw [Dynamics.LaSalle.lieDerivZeroSet_def] at hx
    obtain ⟨h1, h2, h3, h4⟩ := g.eq_of_lyap_lie_eq_zero hM hω hL hZ hEV hε hμ hΓ hx.2
    rw [((Dynamics.hasFDerivAt_coord _ _).sub_const g.Pref).fderiv, Dynamics.coord_apply,
      field_apply_two, mul_eq_zero, or_iff_right hω.ne', sub_eq_zero, h2] at hd
    have hf : g.field x = 0 := (g.field_eq_zero_iff hM.ne' hω.ne' hL.ne' hZ.ne' x).mpr
      ⟨h1, h2, h3, h4, by rw [Network.qssPower, ← h3, ← h4]; exact hd⟩
    exact g.eq_point_of_field_eq_zero hM.ne' hω.ne' hL.ne' hZ hEV h hx.1.1 hf

/-! ### The condition is met -/

/-- An explicit line: `E = V = 1`, `R = 3`, `L = 4`, `ω₀ = 1` (`X = 4`, `|Z| = 5`, `A = 1/5`,
`c₀ = 3/25`), with `M = 1`, `D = 2`, `ω_c = 1` and `P_ref = c₀`. -/
def witness : VSMLPF := ⟨⟨⟨1, 1, 3, 4, 1⟩, 1, 2, 3 / 25⟩, 1⟩

/-- **The conditions are not vacuous**: on `witness` with the weights `ε = 1/2`, `k = 4`,
`μ = 51/20 > 0`, `ν = 2`, `Γ² = 1/4 < 4 μ ν = 102/5`, `M D − ε² ω_c = 7/4 > 0` and
`|P_ref − c₀| = 0 < A = 1/5`, together with the physical signs. -/
@[tmio M, powerlib_domain] theorem witness_conditions :
    0 < witness.M ∧ 0 < witness.ωc ∧ 0 < witness.L ∧ 0 < witness.absSq ∧
      0 < witness.E * witness.V ∧ 0 < witness.lyapMu (1 / 2) ∧
      witness.lyapGammaSq (1 / 2) 4 < 4 * witness.lyapMu (1 / 2) * witness.lyapNu (1 / 2) 4 ∧
      0 < witness.M * witness.D - (1 / 2) ^ 2 * witness.ωc ∧
      |witness.Pref - witness.c0| < witness.A := by
  have hs : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hZ : witness.absSq = 25 := by
    simp only [witness, Network.absSq, Network.X]; norm_num
  have hA : witness.A = 1 / 5 := by
    rw [show witness.A = witness.E * witness.V / Real.sqrt witness.absSq from rfl, hZ, hs]
    simp only [witness]; norm_num
  have hc0 : witness.c0 = 3 / 25 := by
    rw [show witness.c0 = witness.E ^ 2 * witness.R / witness.absSq from rfl, hZ]
    simp only [witness]; norm_num
  have hX : witness.X = 4 := by simp only [witness, Network.X]; norm_num
  refine ⟨by simp [witness], by simp [witness], by simp [witness], by rw [hZ]; norm_num,
    by simp [witness], ?_, ?_, by simp [witness]; norm_num, ?_⟩
  · simp only [lyapMu, hA]; simp only [witness]; norm_num
  · simp only [lyapMu, lyapNu, lyapGammaSq, hA, hZ, hX]; simp only [witness]; norm_num
  · rw [hA, hc0]; simp only [witness]; norm_num

end VSMLPF

end powerlib.GFM.Line
