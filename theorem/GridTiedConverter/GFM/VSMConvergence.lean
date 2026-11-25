import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.Dynamics.BoundedConvergence
import theorem.PowerSystem.Synchronous.DampedEAC

/-! # Bounded solutions of the VSM and the VSM + power filter converge; Barbashin basins

The GFM counterparts of the GFL convergence and basin results
(`theorem/GridTiedConverter/GFL/LCLine/Convergence.lean`, `piPLL_tendsto_of_bounded`;
`theorem/GridTiedConverter/PLL/Basin.lean`): every bounded forward solution of the VSM with an
arbitrary power curve converges to a balanced state, and, for the three-state VSM + power filter,
an explicit Lyapunov function of Barbashin type gives the same convergence and potential-well
estimates of the region of attraction under the global fast-filter condition
`|K₀| < D ω_c + D²/M`.

Model boundary.
* VSM (`DroopVSM.VSMModel`, `theorem/GridTiedConverter/GFM/DroopVSM.lean`): state `(θ, ω)`,
  `θ̇ = ω`, `M ω̇ = P_ref − P(θ) − D (ω − ω_s)`, an arbitrary `C¹` power map `P` (export-positive),
  `M, D > 0`, balance points `P(θ*) = P_ref + D ω_s` isolated; any rotating frame.
* VSM + power filter (`GFM.VSMLPF`, `theorem/GridTiedConverter/GFM/VSMLPF.lean`): state
  `(δ, ω, P_f)`, `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)` on an infinite bus
  (lossless line, constant EMF, export-positive power), `M, D, ω_c > 0`, `K₀ ≠ 0`, constant `P₀`;
  continuous time, no voltage loop, inner loops, limiter, PLL, delay, PWM or line dynamics.
* Solutions are `IsIntegralCurveOn` curves on `[0, ∞)`; the convergence statements concern one
  forward solution (ω-limit level), the basin statements the region of attraction
  `Flow.regionOfAttraction` (every forward solution from the set exists and converges).

Source: work-sync `theory/T-gfm-control.md` §1.2, §1.4 (VSM swing law, power filter),
`theory/T-lyapunov-function-method.md` §1.4 (LaSalle); E. A. Barbashin, *Lyapunov Functions*
(Nauka, 1970), the function `V = a H(x) + h(x) y + (b/2) y² + ½(a y + z)²` of
`x⃛ + a ẍ + b ẋ + h(x) = 0` with `V̇ = −(a b − h'(x)) ẋ²`; derivation of the scaled form and of
its well potential by exact symbolic computation (sympy, symbolic parameters; batch N8 log).

Results.
* Barbashin's function of the VSM + power filter, scaled by `M²/ω_c`:
  `B = (M ω_c + D)(−K₀ cos δ − P₀ δ) + M (K₀ sin δ − P₀) ω + (M D/2) ω²`
  `+ (ω_c M ω + P₀ − P_f)²/(2 ω_c)` (`VSMLPF.barbashin`), its derivative
  (`VSMLPF.hasFDerivAt_barbashin`) and the exact rate `Ḃ = −(D² + D M ω_c − K₀ M cos δ) ω²`
  (`VSMLPF.barbashin_lie`); the margin `D² + D M ω_c − K₀ M cos δ` (`VSMLPF.barbashinMargin`) is
  positive at every angle under the global fast-filter condition `|K₀| < D ω_c + D²/M`
  (`VSMLPF.barbashinMargin_pos`; at `K₀ cos δ` it is `M` times the Routh margin of
  `VSMLPF.Meets .fastFilter`).
* The well form `B = W(δ) + (M D/2)(ω + (K₀ sin δ − P₀)/D)² + (ω_c M ω + P₀ − P_f)²/(2 ω_c)`
  (`VSMLPF.barbashin_eq_well`) with the well potential
  `W(δ) = (M ω_c + D)(−K₀ cos δ − P₀ δ) − M (K₀ sin δ − P₀)²/(2D)` (`VSMLPF.wellPotential`,
  `W' = (K₀ sin δ − P₀)(D² + D M ω_c − K₀ M cos δ)/D`, `VSMLPF.hasDerivAt_wellPotential`: under the
  margin its critical points are exactly the balanced angles, minima at `δ₀ + 2kπ`, maxima at
  `π − δ₀ + 2kπ`), so `W(δ) ≤ B` (`VSMLPF.wellPotential_le_barbashin`).
* Well geometry: the window `−π − δ₀ < δ < π − δ₀` (`VSMLPF.wellWindow`, open), the only balanced
  angle in it is `δ₀ = arcsin(P₀/K₀)` (`VSMLPF.eq_δ0_of_balanced`, `|P₀| < K₀`), and the sublevel
  sets of `B` in the window below both saddle levels `W(π − δ₀)`, `W(−π − δ₀)` are compact
  (`VSMLPF.isCompact_wellSublevel`).
* Implementation evidence (private, trajectory level): `DroopVSM.vsm_exists_tendsto_of_bounded`
  (every bounded forward solution of a VSM with a `C¹` power map and isolated balance points
  converges to a balanced state `(θ*, 0)`, through `Dynamics.conservative_exists_tendsto_of_bounded`
  and `VSMModel.vector_eq_conservative`); `VSMLPF.exists_tendsto_of_bounded` (under
  `|K₀| < D ω_c + D²/M`, `K₀ ≠ 0`, every bounded forward solution converges to an equilibrium
  `(δ*, 0, P₀)`, `K₀ sin δ* = P₀`, through `Dynamics.exists_tendsto_of_bounded` with the function
  `B`); `VSMLPF.regionOfAttraction_well` (under the same condition, `0 < K₀`, `|P₀| < K₀`: every
  sublevel set `{−π − δ₀ < δ < π − δ₀, B ≤ c}` with `c` below both saddle levels lies in the
  region of attraction of `(δ₀, 0, P₀)`, LaSalle
  `Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel`).

Family and connection conclusions.
No family and no connection conclusion: convergence of one bounded solution and region-of-
attraction estimates are outside the sentence language (as their GFL counterparts), so they are
private implementation evidence; Barbashin's function, its rate, the well potential and the well
geometry are static domain evidence. The local sentences of the same equilibria are the connection
statements of `DroopVSM.vsmFamily` and `VSMLPF.family`.

Scope.
* No convergence or basin claim is made beyond the global margin `|K₀| < D ω_c + D²/M`: there the
  Barbashin rate changes sign at some angles, and at a balanced angle with
  `K₀ cos δ* > D ω_c + D²/M` the equilibrium is unstable (`VSMLPF.mem_den_unstable`), beyond the
  Hopf boundary of `theorem/GridTiedConverter/GFM/VSMLPFHopf.lean`.
* Boundedness of the forward solution is a hypothesis; the limit equilibrium may be a saddle
  (reached on its stable set). The droop + LPF loop is the VSM in the coordinates
  `(θ, ω_s − (P_f − P_ref)/K_R)` (`DroopVSM.vsmField_eq_transport`); its bounded solutions are not
  restated.
-/

noncomputable section
namespace powerlib.GFM
open Set Filter Topology
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext coord)

/-! ## The VSM with an arbitrary power curve -/

namespace DroopVSM

/-- **Bounded VSM solutions converge.** Every bounded forward solution of a VSM with a `C¹` power
map, positive inertia and damping, and isolated balance points converges to a balanced state
`(θ*, 0)`, `P(θ*) = P_ref + D ω_s`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem vsm_exists_tendsto_of_bounded (m : VSMModel)
    (hM : 0 < m.M) (hD : 0 < m.D) (hs : ContDiff ℝ 1 m.P)
    (hiso : ∀ θ, m.P θ = m.Pref + m.D * m.ωs →
      ∀ᶠ θ' in 𝓝[≠] θ, m.P θ' ≠ m.Pref + m.D * m.ωs)
    {φ : ℝ → State 2} (hφ : IsIntegralCurveOn φ (fun _ y => m.vector y) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ θs, m.P θs = m.Pref + m.D * m.ωs ∧ Tendsto φ atTop (𝓝 (PhasePlane.mk θs 0)) := by
  rw [m.vector_eq_conservative] at hφ
  obtain ⟨θs, h0, ht⟩ := Dynamics.conservative_exists_tendsto_of_bounded hM hD
    (hs.sub contDiff_const)
    (fun θ hθ => (hiso θ (sub_eq_zero.mp hθ)).mono fun _ h => sub_ne_zero.mpr h) hφ hb
  exact ⟨θs, sub_eq_zero.mp h0, ht⟩

end DroopVSM

/-! ## Barbashin's function of the VSM + power filter -/

namespace VSMLPF

variable (g : VSMLPF)

/-- Barbashin's function, scaled by `M²/ω_c`: `B = (M ω_c + D)(−K₀ cos δ − P₀ δ)`
`+ M (K₀ sin δ − P₀) ω + (M D/2) ω² + (ω_c M ω + P₀ − P_f)²/(2 ω_c)`. -/
def barbashin (x : State 3) : ℝ :=
  (g.M * g.ωc + g.D) * (-g.K0 * Real.cos (x 0) - g.P0 * x 0) +
    g.M * (g.K0 * Real.sin (x 0) - g.P0) * x 1 + g.M * g.D / 2 * x 1 ^ 2 +
      (g.ωc * g.M * x 1 + g.P0 - x 2) ^ 2 / (2 * g.ωc)

/-- The margin `D² + D M ω_c − K₀ M cos δ` of the rate `Ḃ = −margin · ω²`. -/
def barbashinMargin (δ : ℝ) : ℝ := g.D ^ 2 + g.D * g.M * g.ωc - g.K0 * g.M * Real.cos δ

/-- The well potential `W(δ) = (M ω_c + D)(−K₀ cos δ − P₀ δ) − M (K₀ sin δ − P₀)²/(2D)`. -/
def wellPotential (δ : ℝ) : ℝ :=
  (g.M * g.ωc + g.D) * (-g.K0 * Real.cos δ - g.P0 * δ) -
    g.M * (g.K0 * Real.sin δ - g.P0) ^ 2 / (2 * g.D)

/-- The derivative of Barbashin's function at `x`. -/
def barbashinDeriv (x : State 3) : State 3 →L[ℝ] ℝ :=
  ((g.M * g.ωc + g.D) * (g.K0 * Real.sin (x 0) - g.P0) +
      g.M * g.K0 * Real.cos (x 0) * x 1) • coord 0 +
    (g.M * (g.K0 * Real.sin (x 0) - g.P0) + g.M * g.D * x 1 +
      g.M * (g.ωc * g.M * x 1 + g.P0 - x 2)) • coord 1 +
    (-(g.ωc * g.M * x 1 + g.P0 - x 2) / g.ωc) • coord 2

@[tmio M, powerlib_domain] theorem hasFDerivAt_barbashin (hω : g.ωc ≠ 0) (x : State 3) :
    HasFDerivAt g.barbashin (g.barbashinDeriv x) x := by
  have h0 := Dynamics.hasFDerivAt_coord 0 x
  have h1 := Dynamics.hasFDerivAt_coord 1 x
  have h2 := Dynamics.hasFDerivAt_coord 2 x
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  have hq := ((h1.const_mul (g.ωc * g.M)).add_const g.P0).sub h2
  have h := ((((hc.const_mul (-g.K0)).sub (h0.const_mul g.P0)).const_mul (g.M * g.ωc + g.D)).add
    ((((hs.const_mul g.K0).sub_const g.P0).const_mul g.M).mul h1)).add
      ((h1.pow 2).const_mul (g.M * g.D / 2)) |>.add ((hq.pow 2).const_mul (1 / (2 * g.ωc)))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_fderiv ?_
  · simp [barbashin]; ring
  · ext v
    simp [barbashinDeriv]
    field_simp
    ring

@[tmio M, powerlib_domain] theorem differentiable_barbashin (hω : g.ωc ≠ 0) :
    Differentiable ℝ g.barbashin :=
  fun x => (g.hasFDerivAt_barbashin hω x).differentiableAt

/-- **The rate of Barbashin's function**: `Ḃ = −(D² + D M ω_c − K₀ M cos δ) ω²` (`M, ω_c ≠ 0`). -/
@[tmio M, powerlib_domain] theorem barbashin_lie (hM : g.M ≠ 0) (hω : g.ωc ≠ 0) (x : State 3) :
    fderiv ℝ g.barbashin x (g.field x) = -(g.barbashinMargin (x 0) * x 1 ^ 2) := by
  rw [(g.hasFDerivAt_barbashin hω x).fderiv]
  simp [barbashinDeriv, barbashinMargin]
  field_simp
  ring

/-- Under the global fast-filter condition `|K₀| < D ω_c + D²/M` the margin is positive at every
angle. -/
@[tmio M, powerlib_domain] theorem barbashinMargin_pos (hM : 0 < g.M)
    (hK : |g.K0| < g.D * g.ωc + g.D ^ 2 / g.M) (δ : ℝ) : 0 < g.barbashinMargin δ := by
  have h1 : g.K0 * Real.cos δ ≤ |g.K0| := by
    calc g.K0 * Real.cos δ ≤ |g.K0 * Real.cos δ| := le_abs_self _
      _ = |g.K0| * |Real.cos δ| := abs_mul _ _
      _ ≤ |g.K0| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one δ) (abs_nonneg _)
      _ = |g.K0| := mul_one _
  have h2 : g.M * (g.D * g.ωc + g.D ^ 2 / g.M) = g.D ^ 2 + g.D * g.M * g.ωc := by
    field_simp; ring
  have h3 := mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 hK) hM
  simp only [barbashinMargin]
  nlinarith

/-- The well form of Barbashin's function (`D ≠ 0`). -/
@[tmio M, powerlib_domain] theorem barbashin_eq_well (hD : g.D ≠ 0) (x : State 3) :
    g.barbashin x = g.wellPotential (x 0) +
      g.M * g.D / 2 * (x 1 + (g.K0 * Real.sin (x 0) - g.P0) / g.D) ^ 2 +
        (g.ωc * g.M * x 1 + g.P0 - x 2) ^ 2 / (2 * g.ωc) := by
  simp only [barbashin, wellPotential]
  field_simp
  ring

/-- The well potential dominates Barbashin's function from below (`M, D, ω_c > 0`). -/
@[tmio M, powerlib_domain] theorem wellPotential_le_barbashin (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) (x : State 3) : g.wellPotential (x 0) ≤ g.barbashin x := by
  rw [g.barbashin_eq_well hD.ne']
  have : 0 ≤ g.M * g.D / 2 * (x 1 + (g.K0 * Real.sin (x 0) - g.P0) / g.D) ^ 2 := by positivity
  have : 0 ≤ (g.ωc * g.M * x 1 + g.P0 - x 2) ^ 2 / (2 * g.ωc) := by positivity
  linarith

/-- `W'(δ) = (K₀ sin δ − P₀)(D² + D M ω_c − K₀ M cos δ)/D`: under a positive margin the critical
points of the well potential are the balanced angles. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_wellPotential (hD : g.D ≠ 0) (δ : ℝ) :
    HasDerivAt g.wellPotential
      ((g.K0 * Real.sin δ - g.P0) * g.barbashinMargin δ / g.D) δ := by
  have h := ((((Real.hasDerivAt_cos δ).const_mul (-g.K0)).sub
    ((hasDerivAt_id δ).const_mul g.P0)).const_mul (g.M * g.ωc + g.D)).sub
      (((((Real.hasDerivAt_sin δ).const_mul g.K0).sub_const g.P0).pow 2).const_mul g.M
        |>.div_const (2 * g.D))
  convert h using 1
  · funext y; simp [wellPotential]
  · simp only [barbashinMargin]
    field_simp
    ring

/-! ## Bounded solutions converge -/

/-- With `K₀ ≠ 0` the equilibria `(δ*, 0, P₀)`, `K₀ sin δ* = P₀`, are isolated. -/
@[tmio M, powerlib_domain] theorem field_zero_isolated (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (hK0 : g.K0 ≠ 0) (z : State 3) (hz : g.field z = 0) :
    ∃ ε > 0, ∀ y, g.field y = 0 → dist y z < ε → y = z := by
  obtain ⟨hz1, hz2, -⟩ := (g.field_eq_zero_iff hM hω z).mp hz
  obtain ⟨ε, hε, hiso⟩ :=
    Dynamics.sinusoid_level_isolated (c := 0) (α := 0) (p := g.P0) hK0 (z 0)
  refine ⟨ε, hε, fun y hy hyz => ?_⟩
  obtain ⟨hy1, hy2, hy0⟩ := (g.field_eq_zero_iff hM hω y).mp hy
  have hd : |y 0 - z 0| < ε := by
    have := Dynamics.abs_apply_le_norm (y - z) 0
    simp only [PiLp.sub_apply] at this
    exact lt_of_le_of_lt this (by rwa [← dist_eq_norm])
  exact state3_ext (hiso (y 0) (by simpa using hy0) hd) (by rw [hy1, hz1]) (by rw [hy2, hz2])

/-- **Bounded solutions of the VSM + power filter converge** under the global fast-filter
condition `|K₀| < D ω_c + D²/M` (`M, D, ω_c > 0`, `K₀ ≠ 0`): every bounded forward solution
converges to an equilibrium `(δ*, 0, P₀)`, `K₀ sin δ* = P₀` (Barbashin's function decreases at
the rate `margin · ω²`; a solution with `ω ≡ 0` has `P_f ≡ P₀` and then `K₀ sin δ = P₀`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem exists_tendsto_of_bounded (hM : 0 < g.M)
    (hD : 0 < g.D) (hω : 0 < g.ωc) (hK0 : g.K0 ≠ 0) (hK : |g.K0| < g.D * g.ωc + g.D ^ 2 / g.M)
    {φ : ℝ → State 3} (hφ : IsIntegralCurveOn φ (fun _ y => g.field y) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ δs, g.K0 * Real.sin δs = g.P0 ∧ Tendsto φ atTop (𝓝 (mk3 δs 0 g.P0)) := by
  have hD' := hD
  obtain ⟨z, hz, hzt⟩ := Dynamics.exists_tendsto_of_bounded g.contDiff_field
    (g.differentiable_barbashin hω.ne') hφ hb
    (fun t _ => by
      rw [g.barbashin_lie hM.ne' hω.ne']
      have := g.barbashinMargin_pos hM hK (φ t 0)
      nlinarith [sq_nonneg (φ t 1)])
    (fun ψ hψ _ h0 => by
      have hv : ∀ t, 0 ≤ t → ψ t 1 = 0 := fun t ht => by
        have h := h0 t ht
        rw [g.barbashin_lie hM.ne' hω.ne'] at h
        have hm := g.barbashinMargin_pos hM hK (ψ t 0)
        have : g.barbashinMargin (ψ t 0) * ψ t 1 ^ 2 = 0 := by linarith
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp this).resolve_left hm.ne')
      have hP : ∀ t, 0 ≤ t → ψ t 2 = g.P0 := fun t ht => by
        have h1 := Dynamics.field_apply_eq_zero_of_coord_const hψ 1 hv ht
        rw [field_apply_one, hv t ht, mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM.ne',
          sub_eq_zero] at h1
        exact h1.symm
      have h2 := Dynamics.field_apply_eq_zero_of_coord_const hψ 2 hP le_rfl
      rw [field_apply_two, mul_eq_zero, or_iff_right hω.ne', sub_eq_zero, hP 0 le_rfl] at h2
      exact (g.field_eq_zero_iff hM.ne' hω.ne' _).mpr ⟨hv 0 le_rfl, hP 0 le_rfl, h2⟩)
    (fun z _ hz => g.field_zero_isolated hM.ne' hω.ne' hK0 z hz)
  obtain ⟨hz1, hz2, hz0⟩ := (g.field_eq_zero_iff hM.ne' hω.ne' z).mp hz
  refine ⟨z 0, hz0, ?_⟩
  have : z = mk3 (z 0) 0 g.P0 := state3_ext (by simp) (by simp [hz1]) (by simp [hz2])
  rwa [← this]

/-! ## The potential well and its region of attraction -/

/-- The well window `−π − δ₀ < δ < π − δ₀` around the loading angle `δ₀ = arcsin(P₀/K₀)`. -/
def wellWindow : Set (State 3) := {x | -Real.pi - g.δ0 < x 0 ∧ x 0 < Real.pi - g.δ0}

@[tmio M, powerlib_domain] theorem isOpen_wellWindow : IsOpen g.wellWindow :=
  (isOpen_lt continuous_const (Dynamics.contDiff_coord (k := 0) 0).continuous).inter
    (isOpen_lt (Dynamics.contDiff_coord (k := 0) 0).continuous continuous_const)

/-- In the well window the only balanced angle is the loading angle `δ₀` (`|P₀| < K₀`; the swing
well geometry `Synchronous.SwingParams.eq_deltaS_of_field_eq_zero` of the sinusoid). -/
@[tmio M, powerlib_domain] theorem eq_δ0_of_balanced (hK0 : 0 < g.K0) (h : |g.P0| < g.K0)
    {δ : ℝ} (h1 : -Real.pi - g.δ0 < δ) (h2 : δ < Real.pi - g.δ0)
    (hb : g.K0 * Real.sin δ = g.P0) : δ = g.δ0 := by
  set p := Synchronous.SwingParams.sinusoid 1 0 g.P0 g.K0
  have hk : 0 < p.k₂ := hK0
  have hp : |p.Pm - p.k₁| < p.k₂ := by
    simpa [p, Synchronous.SwingParams.sinusoid] using h
  have hU : p.deltaU = Real.pi - g.δ0 := by
    simp [p, Synchronous.SwingParams.deltaU, Synchronous.SwingParams.loadRatio,
      Synchronous.SwingParams.sinusoid, δ0]
  have hS : p.deltaS = g.δ0 := by
    simp [p, Synchronous.SwingParams.deltaS, Synchronous.SwingParams.loadRatio,
      Synchronous.SwingParams.sinusoid, δ0]
  have hx := p.eq_deltaS_of_field_eq_zero one_ne_zero hk hp (x := PhasePlane.mk δ 0)
    ⟨by simp only [PhasePlane.mk_apply_zero]; rw [hU]; linarith,
      by simp only [PhasePlane.mk_apply_zero]; rw [hU]; exact h2⟩
    ((p.field_eq_zero_iff one_ne_zero _).mpr ⟨by simp,
      by simp [p, Synchronous.SwingParams.Pe, Synchronous.SwingParams.sinusoid, hb]⟩)
  have := congrArg (fun y : State 2 => y 0) hx
  simpa [hS] using this

/-- Sublevel sets of Barbashin's function in the well window below both saddle levels
`W(π − δ₀)`, `W(−π − δ₀)` are compact (`M, D, ω_c > 0`). -/
@[tmio M, powerlib_domain] theorem isCompact_wellSublevel (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) {c : ℝ} (hc1 : c < g.wellPotential (Real.pi - g.δ0))
    (hc2 : c < g.wellPotential (-Real.pi - g.δ0)) :
    IsCompact {x ∈ g.wellWindow | g.barbashin x ≤ c} := by
  set a := -Real.pi - g.δ0
  set b := Real.pi - g.δ0
  have hab : a ≤ b := by have := Real.pi_pos; simp only [a, b]; linarith
  have hcW : Continuous g.wellPotential := by unfold wellPotential; fun_prop
  have hcB : Continuous g.barbashin := (g.differentiable_barbashin hω.ne').continuous
  have hc0 : Continuous fun x : State 3 => x 0 := (Dynamics.contDiff_coord (k := 0) 0).continuous
  have hEq : {x ∈ g.wellWindow | g.barbashin x ≤ c} =
      {x : State 3 | a ≤ x 0} ∩ {x | x 0 ≤ b} ∩ {x | g.barbashin x ≤ c} := by
    ext x
    simp only [wellWindow, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.le, h2.le⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hW := g.wellPotential_le_barbashin hM hD hω x
      refine ⟨⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩, h3⟩
      · intro he; rw [← he] at hW; linarith
      · intro he; rw [he] at hW; linarith
  rw [hEq]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact ((isClosed_le continuous_const hc0).inter (isClosed_le hc0 continuous_const)).inter
      (isClosed_le hcB continuous_const)
  obtain ⟨δm, -, hδm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcW.continuousOn
  set C := c - g.wellPotential δm
  set X1 := 1 + 2 * C / (g.M * g.D) + (|g.K0| + |g.P0|) / g.D
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨|a| + |b| + X1 * (1 + g.ωc * g.M) + 1 + 2 * g.ωc * C + |g.P0|, ?_⟩
  rintro x ⟨⟨h1, h2⟩, h3⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [mem_ofPred_eq] at h1 h2 h3
  have hW : g.wellPotential δm ≤ g.wellPotential (x 0) := hδm (show x 0 ∈ Icc a b from ⟨h1, h2⟩)
  rw [g.barbashin_eq_well hD.ne'] at h3
  set u := x 1 + (g.K0 * Real.sin (x 0) - g.P0) / g.D
  set v := g.ωc * g.M * x 1 + g.P0 - x 2
  have hq1 : 0 ≤ g.M * g.D / 2 * u ^ 2 := by positivity
  have hq2 : 0 ≤ v ^ 2 / (2 * g.ωc) := by positivity
  have hu2 : u ^ 2 ≤ 2 * C / (g.M * g.D) := by
    rw [le_div_iff₀ (mul_pos hM hD)]
    have : g.M * g.D / 2 * u ^ 2 ≤ C := by simp only [C]; linarith
    nlinarith
  have hv2 : v ^ 2 ≤ 2 * g.ωc * C := by
    have : v ^ 2 / (2 * g.ωc) ≤ C := by simp only [C]; linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have habs : ∀ w : ℝ, |w| ≤ 1 + w ^ 2 := fun w => by
    rcases abs_cases w with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith [sq_nonneg (w - 1),
      sq_nonneg (w + 1)]
  have hs : |(g.K0 * Real.sin (x 0) - g.P0) / g.D| ≤ (|g.K0| + |g.P0|) / g.D := by
    rw [abs_div, abs_of_pos hD]
    refine div_le_div_of_nonneg_right ?_ hD.le
    calc |g.K0 * Real.sin (x 0) - g.P0| ≤ |g.K0 * Real.sin (x 0)| + |g.P0| := abs_sub _ _
      _ ≤ |g.K0| + |g.P0| := by
        rw [abs_mul]
        nlinarith [Real.abs_sin_le_one (x 0), abs_nonneg g.K0]
  have hx1 : |x 1| ≤ X1 := by
    have : x 1 = u - (g.K0 * Real.sin (x 0) - g.P0) / g.D := by simp only [u]; ring
    rw [this]
    calc |u - (g.K0 * Real.sin (x 0) - g.P0) / g.D|
        ≤ |u| + |(g.K0 * Real.sin (x 0) - g.P0) / g.D| := abs_sub _ _
      _ ≤ X1 := by simp only [X1]; linarith [habs u]
  have hx2 : |x 2| ≤ g.ωc * g.M * X1 + |g.P0| + 1 + 2 * g.ωc * C := by
    have : x 2 = g.ωc * g.M * x 1 + g.P0 - v := by simp only [v]; ring
    rw [this]
    have hωM : 0 < g.ωc * g.M := mul_pos hω hM
    calc |g.ωc * g.M * x 1 + g.P0 - v| ≤ |g.ωc * g.M * x 1| + |g.P0| + |v| := by
          have := abs_sub (g.ωc * g.M * x 1 + g.P0) v
          have := abs_add_le (g.ωc * g.M * x 1) g.P0
          linarith
      _ ≤ g.ωc * g.M * X1 + |g.P0| + 1 + 2 * g.ωc * C := by
          rw [abs_mul, abs_of_pos hωM]
          nlinarith [habs v]
  have hx0 : |x 0| ≤ |a| + |b| := by
    rw [abs_le]; constructor <;>
      cases abs_cases a <;> cases abs_cases b <;> linarith [abs_nonneg a, abs_nonneg b]
  have hnorm := (Dynamics.norm_le_sum_abs x).trans_eq (Fin.sum_univ_three _)
  nlinarith

/-- **LaSalle on Barbashin's well** (`M, D, ω_c > 0`, `0 < K₀ < D ω_c + D²/M`, `|P₀| < K₀`):
every sublevel set of Barbashin's function in the well window below both saddle levels lies in
the region of attraction of the loading equilibrium `(δ₀, 0, P₀)` (the generic
`Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel`; on the zero set of `Ḃ` the frequency
vanishes, then `P_f = P₀`, then the angle is balanced).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem regionOfAttraction_well (hM : 0 < g.M)
    (hD : 0 < g.D) (hω : 0 < g.ωc) (hK0 : 0 < g.K0) (h : |g.P0| < g.K0)
    (hK : |g.K0| < g.D * g.ωc + g.D ^ 2 / g.M) {c : ℝ}
    (hc1 : c < g.wellPotential (Real.pi - g.δ0)) (hc2 : c < g.wellPotential (-Real.pi - g.δ0)) :
    {x ∈ g.wellWindow | g.barbashin x ≤ c} ⊆
      Flow.regionOfAttraction g.field (mk3 g.δ0 0 g.P0) := by
  have hBc : ContDiff ℝ 1 g.barbashin := by unfold barbashin; fun_prop
  have hv0 : ∀ x : State 3, fderiv ℝ g.barbashin x (g.field x) = 0 → x 1 = 0 := fun x hx => by
    rw [g.barbashin_lie hM.ne' hω.ne'] at hx
    have hm := g.barbashinMargin_pos hM hK (x 0)
    have : g.barbashinMargin (x 0) * x 1 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp this).resolve_left hm.ne')
  refine Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel g.isOpen_wellWindow
    g.contDiff_field hBc (fun x _ => ?_) (g.isCompact_wellSublevel hM hD hω hc1 hc2) ?_
  · rw [g.barbashin_lie hM.ne' hω.ne']
    have := g.barbashinMargin_pos hM hK (x 0)
    nlinarith [sq_nonneg (x 1)]
  intro N hN hNinv
  set Ω := {x ∈ g.wellWindow | g.barbashin x ≤ c}
  have hstep1 : N ⊆ {x | x ∈ Ω ∧ x 1 = 0 ∧ x 2 = g.P0} :=
    Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem g.contDiff_field
      (Dynamics.contDiff_coord (n := 3) (k := 1) 1)
      (fun x hx => by
        rw [Dynamics.LaSalle.lieDerivZeroSet_def] at hx
        exact hv0 x hx.2)
      (fun x hx hd => by
        rw [Dynamics.LaSalle.lieDerivZeroSet_def] at hx
        have h1 := hv0 x hx.2
        rw [(Dynamics.hasFDerivAt_coord _ _).fderiv, Dynamics.coord_apply, field_apply_one, h1,
          mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM.ne', sub_eq_zero] at hd
        exact ⟨hx.1, h1, hd.symm⟩) N hN hNinv
  refine Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem g.contDiff_field
    ((Dynamics.contDiff_coord (n := 3) (k := 1) 2).sub contDiff_const)
    (h := fun x : State 3 => x 2 - g.P0) (fun x hx => sub_eq_zero.mpr hx.2.2)
    (fun x hx hd => ?_) N hstep1 hNinv
  obtain ⟨⟨⟨hx1, hx2⟩, -⟩, h1, h2⟩ := hx
  rw [((Dynamics.hasFDerivAt_coord _ _).sub_const g.P0).fderiv, Dynamics.coord_apply,
    field_apply_two, mul_eq_zero, or_iff_right hω.ne', sub_eq_zero, h2] at hd
  have h0 := g.eq_δ0_of_balanced hK0 h hx1 hx2 hd
  exact state3_ext (by simp [h0]) (by simp [h1]) (by simp [h2])

end VSMLPF

end powerlib.GFM
