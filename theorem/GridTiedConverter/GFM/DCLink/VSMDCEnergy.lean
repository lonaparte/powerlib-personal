import theorem.GridTiedConverter.GFM.DCLink.VSMDC

/-! # The VSM–DC converter: no Lyapunov function of separable energy type

Model boundary.
The four-state VSM with DC link and DC-voltage PI loop `VSMDC.Model` of
`theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`: state `(δ, ω, V, ζ)`, `δ̇ = ω`,
`M ω̇ = P_ff + K_p (V − V*) + K_i ζ − P_e(δ) − D ω`, `C V̇ = (P_src(V) − P_e(δ))/V`,
`ζ̇ = V − V*`, `P_e(δ) = c₀ + A sin(δ − α)`, `P_src(V) = P_s + I_s V`; continuous time,
autonomous, export-positive power; parameters arbitrary reals, read at a balanced selected point
`(δ*, 0, V*, ζ*)` with `V* ≠ 0`, `M ≠ 0` and an integral DC gain `K_i ≠ 0` (without it the
integrator is neutral and the point is never asymptotically stable). Excluded as in `VSMDC.lean`.
Level: static properties of candidate Lyapunov functions (their rate along the field).

Source: the energy-function method for power systems (M. A. Pai, *Energy Function Analysis for
Power System Stability*, Kluwer, 1989: swing energy `M ω²/2 + Π(δ)`) and Lyapunov's direct method
(Khalil, *Nonlinear Systems*, 3rd ed., 2002, Theorem 4.1); the computation of the rate on the
frequency–integrator plane is this module's.

Results.
* `VSMDC.Model.separableEnergy a s₁ s₂ s₃ b e d`: the candidates of separable energy type, the
  swing energy `a (M ω²/2 + Π(θ))` (`Π` the potential of the power curve about `δ*`) plus a
  quadratic form in the swing deviations `(θ, ω)` plus a quadratic form in the DC and integrator
  deviations `(v, z) = (V − V*, ζ − ζ*)`, with no term coupling the swing to the DC side.
* `VSMDC.Model.separableEnergy_lie`: on the frequency–integrator plane through the point
  (`θ = 0`, `V = V*`) the rate along the closed loop is
  `ω² (2 s₂ − (a M + 2 s₃) D/M) + ω z K_i (a M + 2 s₃)/M`.
* `VSMDC.Model.separableEnergy_axis_of_lie_nonpos`: if the rate is `≤ 0` near the point, then
  `a M + 2 s₃ = 0` and the function is constant along the frequency axis `(δ*, ω, V*, ζ*)`;
  `VSMDC.Model.not_strictMin_separableEnergy_of_lie_nonpos`: such a function has no strict local
  minimum at the point. So no Lyapunov function of separable energy type exists, for any
  parameters (Routh-stable or not): an energy-type Lyapunov function must couple the swing to the
  DC link or to the integrator, as the quadratic Lyapunov functions of the linearization do
  (`theorem/GridTiedConverter/GFM/DCLink/VSMDCBasin.lean`).

Not proved here: a coupled energy-type Lyapunov function (swing energy + DC storage + integrator
+ cross terms) valid on the whole Routh region or an explicit sub-region, with a basin larger than
the quadratic one of `VSMDCBasin.lean`.

Family and connection conclusions.
No family and no connection conclusion: static evidence on the model `VSMDC.Model`.
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter Topology
open powerlib.Dynamics (State coord)

namespace VSMDC

/-- A Lyapunov candidate of separable energy type about the selected point: the swing energy
`a (M ω²/2 + Π(θ))` (`Π` the potential of the power curve about `δ*`), a quadratic form in the
swing deviations `(θ, ω)`, and a quadratic form in the DC and integrator deviations `(v, z)`,
with no term coupling the swing to the DC link or the integrator:
`a (M ω²/2 + Π(θ)) + s₁ θ² + 2 s₂ θ ω + s₃ ω² + b v² + 2 e v z + d z²`,
`θ = δ − δ*`, `v = V − V*`, `z = ζ − ζ*`. -/
def Model.separableEnergy (m : Model) (a s₁ s₂ s₃ b e d : ℝ) (y : State 4) : ℝ :=
  a * (m.p.M / 2 * y 1 ^ 2 + (m.p.A * (Real.cos (m.δ - m.p.α) -
    Real.cos (m.δ - m.p.α + (y 0 - m.δ))) - m.p.A * Real.sin (m.δ - m.p.α) * (y 0 - m.δ))) +
    s₁ * (y 0 - m.δ) ^ 2 + 2 * s₂ * (y 0 - m.δ) * y 1 + s₃ * y 1 ^ 2 +
    b * (y 2 - m.p.Vref) ^ 2 + 2 * e * (y 2 - m.p.Vref) * (y 3 - m.ζ) + d * (y 3 - m.ζ) ^ 2

/-- The rate of `Model.separableEnergy` along the closed loop on the frequency–integrator plane
through a balanced point (`θ = 0`, `V = V*`, `V* ≠ 0`): with `ω` and `z = ζ − ζ*`,
`Ė = ω² (2 s₂ − (a M + 2 s₃) D/M) + ω z K_i (a M + 2 s₃)/M`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.separableEnergy_lie (m : Model) (hV : m.p.Vref ≠ 0)
    (hb : m.Balanced) (a s₁ s₂ s₃ b e d ω z : ℝ) :
    fderiv ℝ (m.separableEnergy a s₁ s₂ s₃ b e d)
        (m.point + EuclideanSpace.single 1 ω + EuclideanSpace.single 3 z)
        (m.p.field (m.point + EuclideanSpace.single 1 ω + EuclideanSpace.single 3 z)) =
      ω ^ 2 * (2 * s₂ - (a * m.p.M + 2 * s₃) * m.p.D / m.p.M) +
        ω * z * (m.p.Ki * (a * m.p.M + 2 * s₃) / m.p.M) := by
  set y := m.point + EuclideanSpace.single 1 ω + EuclideanSpace.single 3 z with hy
  have c0 : y 0 = m.δ := by simp [hy, Model.point]
  have c1 : y 1 = ω := by simp [hy, Model.point]
  have c2 : y 2 = m.p.Vref := by simp [hy, Model.point]
  have c3 : y 3 = m.ζ + z := by simp [hy, Model.point]
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h2 := Dynamics.hasFDerivAt_coord 2 y
  have h3 := Dynamics.hasFDerivAt_coord 3 y
  have hθ := h0.sub_const m.δ
  have hcos := (Real.hasDerivAt_cos (m.δ - m.p.α + (y 0 - m.δ))).comp_hasFDerivAt y
    (hθ.const_add (m.δ - m.p.α))
  have hP := ((hcos.const_sub (Real.cos (m.δ - m.p.α))).const_mul m.p.A).sub
    (hθ.const_mul (m.p.A * Real.sin (m.δ - m.p.α)))
  have hS := ((((h1.pow 2).const_mul (m.p.M / 2)).add hP).const_mul a).add
    ((hθ.pow 2).const_mul s₁) |>.add (((hθ.const_mul (2 * s₂)).mul h1)) |>.add
    ((h1.pow 2).const_mul s₃) |>.add (((h2.sub_const m.p.Vref).pow 2).const_mul b) |>.add
    ((((h2.sub_const m.p.Vref).const_mul (2 * e)).mul (h3.sub_const m.ζ))) |>.add
    (((h3.sub_const m.ζ).pow 2).const_mul d)
  have hE : HasFDerivAt (m.separableEnergy a s₁ s₂ s₃ b e d) _ y := hS
  rw [hE.fderiv]
  obtain ⟨hb1, hb2⟩ := hb
  have f0 : m.p.field y 0 = ω := by rw [Params.field_apply_zero, c1]
  have f1 : m.p.field y 1 = (m.p.Ki * z - m.p.D * ω) / m.p.M := by
    rw [Params.field_apply_one, c0, c1, c2, c3]
    simp only [Plant.swingRate, Params.Pref, sub_self, mul_zero, add_zero]
    congr 1
    linarith
  have f2 : m.p.field y 2 = 0 := by
    rw [Params.field_apply_two, c0, c2]
    simp only [Plant.nodeRate, GFL.DCLink.nodeRate]
    simp only [Plant.Psrc] at hb2
    rw [div_eq_zero_iff]
    left
    field_simp
    linarith
  have f3 : m.p.field y 3 = 0 := by rw [Params.field_apply_three, c2, sub_self]
  simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, _root_.neg_apply,
    smul_eq_mul, Dynamics.coord_apply]
  simp only [c0, c1, c2, c3, f0, f1, f2, f3, sub_self, add_sub_cancel_left, add_zero, mul_zero,
    zero_mul, nsmul_eq_mul]
  field_simp
  ring

/-- **No Lyapunov function of separable energy type.** At a balanced point with `V* ≠ 0`, `M ≠ 0`
and an integral DC gain `K_i ≠ 0`, if the rate of `Model.separableEnergy` along the closed loop is
`≤ 0` near the point, then the function is constant along the frequency axis
`(δ*, ω, V*, ζ*)`: the rate on the frequency–integrator plane is
`ω² c₂ + ω z K_i (a M + 2 s₃)/M`, whose cross term must vanish, `a M + 2 s₃ = 0`, which cancels the
`ω²` term of the function. Static evidence on the model: an energy-type Lyapunov function must
couple the swing to the DC link or to the integrator. -/
@[tmio M, powerlib_domain] theorem Model.separableEnergy_axis_of_lie_nonpos (m : Model)
    (hV : m.p.Vref ≠ 0) (hb : m.Balanced) (hM : m.p.M ≠ 0) (hKi : m.p.Ki ≠ 0)
    {a s₁ s₂ s₃ b e d : ℝ}
    (h : ∀ᶠ y in 𝓝 m.point, fderiv ℝ (m.separableEnergy a s₁ s₂ s₃ b e d) y (m.p.field y) ≤ 0)
    (ω : ℝ) :
    m.separableEnergy a s₁ s₂ s₃ b e d (m.point + EuclideanSpace.single 1 ω) =
      m.separableEnergy a s₁ s₂ s₃ b e d m.point := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  set c₂ := 2 * s₂ - (a * m.p.M + 2 * s₃) * m.p.D / m.p.M
  set c₁ := m.p.Ki * (a * m.p.M + 2 * s₃) / m.p.M
  have hline : ∀ l : ℝ, c₂ + l * c₁ ≤ 0 := by
    intro l
    set t := ε / (2 * (1 + |l|)) with ht
    have ht0 : 0 < t := by positivity
    have hy : m.point + EuclideanSpace.single 1 t + EuclideanSpace.single 3 (l * t) ∈
        Metric.ball m.point ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
      have hn := norm_add_le (EuclideanSpace.single 1 t : State 4)
        (EuclideanSpace.single 3 (l * t))
      simp only [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs] at hn
      have e1 : |t| + |l * t| = ε / 2 := by
        rw [abs_mul, abs_of_pos ht0, ht]; field_simp
      linarith
    have hr := hball _ hy
    rw [m.separableEnergy_lie hV hb] at hr
    have : t ^ 2 * (c₂ + l * c₁) ≤ 0 := by nlinarith
    by_contra hX
    push Not at hX
    have := mul_pos (pow_pos ht0 2) hX
    linarith
  have hc₁ : c₁ = 0 := by
    by_contra hne
    have := hline ((|c₂| + 1) / c₁)
    rw [div_mul_cancel₀ _ hne] at this
    linarith [le_abs_self c₂, neg_abs_le c₂]
  have hs : a * m.p.M + 2 * s₃ = 0 := by
    have := hc₁
    rw [div_eq_zero_iff, or_iff_left hM, mul_eq_zero, or_iff_right hKi] at this
    exact this
  simp only [Model.separableEnergy, Model.point]
  simp
  linear_combination ω ^ 2 / 2 * hs

/-- **No strict Lyapunov function of separable energy type.** At a balanced point with `V* ≠ 0`,
`M ≠ 0` and `K_i ≠ 0`, a function `Model.separableEnergy` whose rate along the closed loop is
`≤ 0` near the point has no strict local minimum there (it is constant along the frequency axis,
`Model.separableEnergy_axis_of_lie_nonpos`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.not_strictMin_separableEnergy_of_lie_nonpos (m : Model)
    (hV : m.p.Vref ≠ 0) (hb : m.Balanced) (hM : m.p.M ≠ 0) (hKi : m.p.Ki ≠ 0)
    {a s₁ s₂ s₃ b e d : ℝ}
    (h : ∀ᶠ y in 𝓝 m.point, fderiv ℝ (m.separableEnergy a s₁ s₂ s₃ b e d) y (m.p.field y) ≤ 0) :
    ¬ ∀ᶠ y in 𝓝 m.point, y ≠ m.point →
      m.separableEnergy a s₁ s₂ s₃ b e d m.point < m.separableEnergy a s₁ s₂ s₃ b e d y := by
  intro hmin
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hmin
  have hin : m.point + EuclideanSpace.single 1 (ε / 2) ∈ Metric.ball m.point ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.single,
      PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hne : m.point + EuclideanSpace.single 1 (ε / 2) ≠ m.point := by
    intro h0
    have := congrArg (fun y : State 4 => y 1) h0
    simp at this
    linarith
  have hlt := hball _ hin hne
  rw [m.separableEnergy_axis_of_lie_nonpos hV hb hM hKi h] at hlt
  exact lt_irrefl _ hlt

end VSMDC

end powerlib.GFM.DCLink
