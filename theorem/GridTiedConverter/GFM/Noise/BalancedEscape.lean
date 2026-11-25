import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ControlledAction
import theorem.Dynamics.LipschitzFlow
import theorem.Dynamics.OrbitLaSalle
import theorem.Dynamics.LagFilter
import theorem.GridTiedConverter.GFM.Noise.UphillAction
import theorem.GridTiedConverter.GFM.Noise.EscapeExponent

/-! # The power filter lowers the escape exponent at every bandwidth (balanced set point)

Domain module: for the balanced set point `P_ref = c₀`, the three-state escape exponent
`V₃ = GFM.Noise.Params3.setPointQP` from the stable equilibrium to the saddle is strictly below
the two-state value `V₂ = 2D ΔU/σ_P²` for every filter bandwidth `ω_c > 0`, with the explicit
deficit `V₂ − V₃ ≥ D M J/(σ_P² ω_c)`, `J = Params3.balancedGain > 0`. No perturbation in `ω_c`:
the upper bound is an admissible pair built from a trajectory of the uphill field
(`GFM.Noise.UphillAction`), obtained by a shooting argument on the time-reversed field.

Model boundary.
* The models of `GFM.Noise.EscapeExponent` (voltage source behind a lossy quasi-static line,
  `P(δ) = c₀ + A sin(δ − α)`, per unit; three states `(δ, ω, P_f)`, set-point noise column
  `(0, σ_P/M, 0)`) with `P_ref = c₀` (`s = 0`): stable equilibrium `(α, 0, c₀)`, saddle
  `(π + α, 0, c₀)`, barrier `ΔU = 2A`; `D > 0`, `σ_P ≠ 0`, any `M, A, ω_c > 0`.
* The reversed field `Params3.downField` (the uphill field `Params3.upField` reversed in time
  with the frequency flipped: the damped swing with the anti-stable filter
  `Ṗ_f = ω_c (P_f − P(δ))`) is used inside proofs through its forward flow
  (`Dynamics.forwardSolution`, globally Lipschitz); no behavioural statement about it is made.
* `P_ref ≠ c₀` is excluded: the shooting argument below uses the point reflection about the
  saddle (`Params3.reflect`), a symmetry of the reversed field only when `P_ref = c₀`.
* Deterministic variational statements only, as in `GFM.Noise.EscapeExponent`.

Source: Freidlin, Wentzell, *Random Perturbations of Dynamical Systems* (1984), Ch. 4 (uphill
paths, quasi-potential); the uphill energy identity of `GFM.Noise.UphillAction` (derived and
checked symbolically, sympy, exact, symbolic parameters, in the audit scratch notes outside the
repository, together with the reversal and the reflection symmetry used here); LaSalle along an
orbit (`Dynamics.tendsto_nhdsSet_of_antitone`; Khalil, *Nonlinear Systems*, Thm. 4.4); the
shooting (connectedness) argument for heteroclinic orbits, e.g. J. Hale, H. Koçak,
*Dynamics and Bifurcations* (1991), Ch. 1.

Results.
* `Params3.setPointQP_le_balanced_rest`, `Params.setPointQP_le_balanced`: for every `ω_c > 0`,
  `V₃ ≤ 2D (U(δ_u) − U(δ_s))/σ_P² − D M J/(σ_P² ω_c)`, `J = Params3.balancedGain =
  3 D w₀⁴/(64 A)`, `w₀ = Params3.balancedSpeed = min(A/(8D), π ω_c/12, √(π A/(48 M)))`.
* `Params.setPointQP_lt_swingQP_balanced`: `V₃ < V₂ = Params.swingQP` for every `ω_c > 0`.
* `Params3.downField`, `Params3.lipschitzWith_downField`, `Params3.reflect`,
  `Params3.downField_reflect` (the reflection about the saddle reverses the reversed field,
  `P_ref = c₀`), `Params3.downEnergy`, `Params3.hasFDerivAt_downEnergy`,
  `Params3.uphillEnergy_flip` (`F_R(x) = F(δ, −ω, P_f)`), `Params3.upField`,
  `Params3.uphill_field` (the controlled field with the feedback `σ_P u = 2Dω`),
  `Params3.balancedGain_pos`.
* Proof. (1) Shooting: on the arc `a ↦ (π + α + ε cos a, −η sin a, c₀ + ε sin a)`,
  `a ∈ [0, π]` (its ends exchanged by the reflection; `F_R < A` on it), the sets of starts whose
  reversed orbit leaves the strip `(π + α − 2π, π + α + 2π)` first to the right, resp. first
  to the left, are open (continuity of the flow), disjoint and exchanged by the reflection;
  the arc is connected, so some start does neither. Since `F_R` decreases along the reversed
  flow and `F_R = A` at a rest point on the walls, every contact with a wall is a strict
  crossing, so that orbit stays in the strip; there `|P_f − c₀| ≤ A` (else `M ω + D δ` drifts
  out) and `|ω| ≤ A/D`, and LaSalle along the orbit gives convergence to `(α, 0, c₀)` or, after
  the reflection, from the reflected start. (2) Read backwards, the orbit is an uphill pair of
  action `(2D/σ_P²)(F(end) − F(start) − (M/ω_c)∫ ω̇²)`; its angle crosses `[π/6, 5π/6]`,
  where the filter, after `2/ω_c`, is above `c₀ + A/4` and decelerates the frequency, so
  `|ω|` exceeds `w₀` there and `∫ ω̇² ≥ J` (interpolation, `Dynamics.abs_sq_sub_sq_le`).
  (3) Cubic angle profiles with an end bump, its amplitude fixed by the intermediate value
  theorem, join the equilibria to the ends with action `O(ρ²)` (local controllability through
  the frequency row and the filter, `cos(δ_r − α) ≠ 0`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Set Filter Topology
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP
open powerlib.Dynamics (forwardSolution lipschitzFlow_solution forwardSolution_zero
  dist_forwardSolution_le forwardSolution_unique tendsto_nhdsSet_of_antitone)

namespace Params3

variable (q : Params3)

/-! ## The reversed uphill field and its flow -/

/-- The uphill field reversed in time, frequency flipped: the damped swing
`δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω` with the anti-stable filter `Ṗ_f = ω_c (P_f − P(δ))`. -/
def downField (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 1, (q.Pref - x 2 - q.D * x 1) / q.M, q.ωc * (x 2 - (q.c0 + q.A * Real.sin (x 0 - q.α)))]

/-- A Lipschitz constant of `downField` (sup norm). -/
def downLip : ℝ≥0 :=
  ⟨1 + (1 + q.D) / q.M + q.ωc * (1 + q.A), by
    have := q.M_pos; have := q.D_nonneg; have := q.ωc_pos; have := q.A_pos; positivity⟩

@[tmio M, powerlib_domain] theorem lipschitzWith_downField :
    LipschitzWith q.downLip q.downField := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hM := q.M_pos; have hD := q.D_nonneg; have hω := q.ωc_pos; have hA := q.A_pos
  have hc : ∀ i, |x i - y i| ≤ dist x y := fun i => by
    have := dist_le_pi_dist x y i; rwa [Real.dist_eq] at this
  have hd : 0 ≤ dist x y := dist_nonneg
  have hs : |Real.sin (x 0 - q.α) - Real.sin (y 0 - q.α)| ≤ dist x y :=
    (Real.abs_sin_sub_sin_le _ _).trans (by rw [sub_sub_sub_cancel_right]; exact hc 0)
  have hK : ((q.downLip : ℝ≥0) : ℝ) = 1 + (1 + q.D) / q.M + q.ωc * (1 + q.A) := rfl
  have hK1 : 1 ≤ ((q.downLip : ℝ≥0) : ℝ) := by
    rw [hK]
    have h1 : 0 ≤ (1 + q.D) / q.M := by positivity
    have h2 : 0 ≤ q.ωc * (1 + q.A) := by positivity
    linarith
  have d0 : ∀ z, q.downField z 0 = z 1 := fun z => rfl
  have d1 : ∀ z, q.downField z 1 = (q.Pref - z 2 - q.D * z 1) / q.M := fun z => rfl
  have d2 : ∀ z, q.downField z 2 = q.ωc * (z 2 - (q.c0 + q.A * Real.sin (z 0 - q.α))) :=
    fun z => rfl
  rw [dist_pi_le_iff (by positivity)]
  intro i; rw [Real.dist_eq]
  fin_cases i
  · show |q.downField x 0 - q.downField y 0| ≤ _
    rw [d0, d0]
    nlinarith [hc 1]
  · show |q.downField x 1 - q.downField y 1| ≤ _
    rw [d1, d1]
    have e : (q.Pref - x 2 - q.D * x 1) / q.M - (q.Pref - y 2 - q.D * y 1) / q.M =
        ((y 2 - x 2) + q.D * (y 1 - x 1)) / q.M := by field_simp; ring
    rw [e, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    have h1 : |(y 2 - x 2) + q.D * (y 1 - x 1)| ≤ (1 + q.D) * dist x y := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hD, abs_sub_comm, abs_sub_comm (y 1)]
      nlinarith [hc 1, hc 2]
    have h2 : (1 + q.D) * dist x y ≤ (1 + (1 + q.D) / q.M + q.ωc * (1 + q.A)) * dist x y * q.M := by
      have : (1 + (1 + q.D) / q.M + q.ωc * (1 + q.A)) * q.M = q.M + (1 + q.D) +
          q.ωc * (1 + q.A) * q.M := by field_simp
      nlinarith [mul_nonneg (mul_nonneg hω.le (by linarith : (0 : ℝ) ≤ 1 + q.A)) hM.le]
    rw [hK]; linarith
  · show |q.downField x 2 - q.downField y 2| ≤ _
    rw [d2, d2]
    have e : q.ωc * (x 2 - (q.c0 + q.A * Real.sin (x 0 - q.α))) -
        q.ωc * (y 2 - (q.c0 + q.A * Real.sin (y 0 - q.α))) =
        q.ωc * ((x 2 - y 2) - q.A * (Real.sin (x 0 - q.α) - Real.sin (y 0 - q.α))) := by ring
    rw [e, abs_mul, abs_of_pos hω]
    have h1 : |(x 2 - y 2) - q.A * (Real.sin (x 0 - q.α) - Real.sin (y 0 - q.α))| ≤
        (1 + q.A) * dist x y := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos hA]
      nlinarith [hc 2]
    have h2 : q.ωc * ((1 + q.A) * dist x y) ≤
        (1 + (1 + q.D) / q.M + q.ωc * (1 + q.A)) * dist x y := by
      have : 0 ≤ (1 + (1 + q.D) / q.M) * dist x y := by positivity
      nlinarith
    rw [hK]
    calc q.ωc * |(x 2 - y 2) - q.A * (Real.sin (x 0 - q.α) - Real.sin (y 0 - q.α))|
        ≤ q.ωc * ((1 + q.A) * dist x y) := mul_le_mul_of_nonneg_left h1 hω.le
      _ ≤ _ := h2

/-- The forward flow of `downField`. -/
private def dsol (x : Fin 3 → ℝ) : ℝ → Fin 3 → ℝ :=
  forwardSolution q.lipschitzWith_downField x

@[tmio M, powerlib_domain] private theorem dsol_zero (x : Fin 3 → ℝ) : q.dsol x 0 = x :=
  forwardSolution_zero _ x

@[tmio M, powerlib_domain] private theorem dsol_within (x : Fin 3 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (q.dsol x) (q.downField (q.dsol x t)) (Ici 0) t :=
  lipschitzFlow_solution q.lipschitzWith_downField x t ht

@[tmio M, powerlib_domain] private theorem dsol_hasDerivAt (x : Fin 3 → ℝ) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (q.dsol x) (q.downField (q.dsol x t)) t :=
  (q.dsol_within x ht.le).hasDerivAt (Ici_mem_nhds ht)

@[tmio M, powerlib_domain] private theorem dsol_continuousOn (x : Fin 3 → ℝ) :
    ContinuousOn (q.dsol x) (Ici 0) :=
  (lipschitzFlow_solution q.lipschitzWith_downField x).continuousOn

@[tmio M, powerlib_domain] private theorem dist_dsol_le (x y : Fin 3 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    dist (q.dsol x t) (q.dsol y t) ≤ dist x y * Real.exp (q.downLip * t) :=
  dist_forwardSolution_le _ x y ht

/-- A coordinate along the flow has the derivative of that row of the field. -/
@[tmio M, powerlib_domain] private theorem dsol_coord_within (x : Fin 3 → ℝ) (i : Fin 3)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => q.dsol x s i) (q.downField (q.dsol x t) i) (Ici 0) t :=
  hasDerivWithinAt_pi.1 (q.dsol_within x ht) i

@[tmio M, powerlib_domain] private theorem dsol_coord_hasDerivAt (x : Fin 3 → ℝ) (i : Fin 3)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => q.dsol x s i) (q.downField (q.dsol x t) i) t :=
  hasDerivAt_pi.1 (q.dsol_hasDerivAt x ht) i

/-! ## The reflection about the saddle (balanced set point) -/

/-- The point reflection about the saddle `(π + α, 0, c₀)`: `x ↦ (2(π + α), 0, 2c₀) − x`. -/
def reflect (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![2 * (π + q.α), 0, 2 * q.c0] - x

@[tmio M, powerlib_domain] theorem downField_reflect (hP : q.Pref = q.c0) (x : Fin 3 → ℝ) :
    q.downField (q.reflect x) = -q.downField x := by
  have hs : Real.sin (2 * (π + q.α) - x 0 - q.α) = -Real.sin (x 0 - q.α) := by
    rw [show 2 * (π + q.α) - x 0 - q.α = -(x 0 - q.α) + 2 * π by ring, Real.sin_add_two_pi,
      Real.sin_neg]
  have hM := q.M_pos.ne'
  ext i; fin_cases i
  · simp [downField, reflect]
  · simp [downField, reflect, hP]; field_simp; ring
  · simp [downField, reflect, hs]; ring

/-- The flow commutes with the reflection (`P_ref = c₀`). -/
@[tmio M, powerlib_domain] private theorem dsol_reflect (hP : q.Pref = q.c0) (x : Fin 3 → ℝ)
    {t : ℝ} (ht : 0 ≤ t) : q.dsol (q.reflect x) t = q.reflect (q.dsol x t) := by
  have hcurve : IsIntegralCurveOn (fun s => q.reflect (q.dsol x s))
      (fun _ y => q.downField y) (Ici 0) := by
    intro s hs
    have h := (q.dsol_within x hs).const_sub (![2 * (π + q.α), 0, 2 * q.c0] : Fin 3 → ℝ)
    show HasDerivWithinAt (fun s => q.reflect (q.dsol x s))
      (q.downField (q.reflect (q.dsol x s))) (Ici 0) s
    rw [q.downField_reflect hP]
    exact h
  have := forwardSolution_unique q.lipschitzWith_downField (q.reflect x)
    (fun s => q.reflect (q.dsol x s)) (by simp [q.dsol_zero]) hcurve ht
  exact this.symm

/-! ## The reversed energy -/

/-- The uphill energy read on the reversed states: `F_R(x) = F(δ, −ω, P_f)`. -/
def downEnergy (x : Fin 3 → ℝ) : ℝ :=
  q.M * x 1 ^ 2 / 2 + q.potential (x 0 - q.α) + x 1 * (x 2 - q.Pref) / q.ωc +
    q.D * x 1 ^ 2 / (2 * q.ωc)

@[tmio M, powerlib_domain] theorem uphillEnergy_flip (x : Fin 3 → ℝ) :
    q.uphillEnergy ![x 0, -x 1, x 2] = q.downEnergy x := by
  simp [uphillEnergy, downEnergy]; ring

@[tmio M, powerlib_domain] private theorem continuous_downEnergy : Continuous q.downEnergy := by
  unfold downEnergy Params.potential
  fun_prop

local notation "π₃" i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

/-- The derivative of `F_R`. -/
def downEnergyDeriv (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  q.potentialDeriv (x 0 - q.α) • (π₃ 0) +
    (q.M * x 1 + (x 2 - q.Pref) / q.ωc + q.D * x 1 / q.ωc) • (π₃ 1) + (x 1 / q.ωc) • (π₃ 2)

@[tmio M, powerlib_domain] theorem hasFDerivAt_downEnergy (x : Fin 3 → ℝ) :
    HasFDerivAt q.downEnergy (q.downEnergyDeriv x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hU := (q.hasDerivAt_potential (x 0 - q.α)).comp_hasFDerivAt x (h0.sub_const q.α)
  have hK := (h1.pow 2).const_mul (q.M / 2 + q.D / (2 * q.ωc))
  have hC := (h1.mul (h2.sub_const q.Pref)).const_mul (1 / q.ωc)
  have h := (hK.add hU).add hC
  have hf : q.downEnergy = fun y => ((q.M / 2 + q.D / (2 * q.ωc)) * y 1 ^ 2 +
      (q.potential ∘ fun y => y 0 - q.α) y) + 1 / q.ωc * (y 1 * (y 2 - q.Pref)) := by
    funext y; simp only [downEnergy, Function.comp]; ring
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have hω := q.ωc_pos.ne'
  simp [downEnergyDeriv]
  field_simp
  ring

/-- The decay rate of `F_R` along `downField`: `−(D ω² + (M/ω_c) a²)`,
`a = (P_ref − P_f − D ω)/M`. -/
@[tmio M, powerlib_domain] private theorem hasDerivWithinAt_downEnergy (x : Fin 3 → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => q.downEnergy (q.dsol x s))
      (-(q.D * q.dsol x t 1 ^ 2 + q.M / q.ωc *
        ((q.Pref - q.dsol x t 2 - q.D * q.dsol x t 1) / q.M) ^ 2)) (Ici 0) t := by
  have h := (q.hasFDerivAt_downEnergy (q.dsol x t)).comp_hasDerivWithinAt t (q.dsol_within x ht)
  refine h.congr_deriv ?_
  have hM := q.M_pos.ne'
  have hω := q.ωc_pos.ne'
  simp [downEnergyDeriv, downField, Params.potentialDeriv, Params.toSM]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem downEnergy_antitone (x : Fin 3 → ℝ) :
    AntitoneOn (fun s => q.downEnergy (q.dsol x s)) (Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (f' := fun t => -(q.D * q.dsol x t 1 ^ 2 + q.M / q.ωc *
        ((q.Pref - q.dsol x t 2 - q.D * q.dsol x t 1) / q.M) ^ 2))
    (q.continuous_downEnergy.comp_continuousOn (q.dsol_continuousOn x)) (fun t ht => ?_)
    (fun t _ => ?_)
  · rw [interior_Ici] at ht ⊢
    exact (q.hasDerivWithinAt_downEnergy x ht.le).mono Ioi_subset_Ici_self
  · have := q.D_nonneg; have := q.M_pos; have := q.ωc_pos
    have : 0 ≤ q.D * q.dsol x t 1 ^ 2 + q.M / q.ωc *
        ((q.Pref - q.dsol x t 2 - q.D * q.dsol x t 1) / q.M) ^ 2 := by positivity
    linarith

@[tmio M, powerlib_domain] private theorem downEnergy_le (x : Fin 3 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    q.downEnergy (q.dsol x t) ≤ q.downEnergy x := by
  have := q.downEnergy_antitone x (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simpa [q.dsol_zero] using this

@[tmio M, powerlib_domain] private theorem potential_balanced (hP : q.Pref = q.c0) (θ : ℝ) :
    q.potential θ = -(q.A * Real.cos θ) := by
  simp [Params.potential, Params.toSM, hP]

@[tmio M, powerlib_domain] private theorem downEnergy_reflect (hP : q.Pref = q.c0)
    (x : Fin 3 → ℝ) : q.downEnergy (q.reflect x) = q.downEnergy x := by
  have hc : Real.cos (2 * (π + q.α) - x 0 - q.α) = Real.cos (x 0 - q.α) := by
    rw [show 2 * (π + q.α) - x 0 - q.α = -(x 0 - q.α) + 2 * π by ring, Real.cos_add_two_pi,
      Real.cos_neg]
  simp only [downEnergy, q.potential_balanced hP, reflect]
  simp [hc, hP]
  ring

/-! ## The shooting arc and the two exits -/

/-- The shooting arc near the saddle: `a ↦ (π + α + ε cos a, −η sin a, c₀ + ε sin a)`,
`η = ε/(1 + M ω_c + D)`. -/
private def arc (ε a : ℝ) : Fin 3 → ℝ :=
  ![π + q.α + ε * Real.cos a, -(ε / (1 + q.M * q.ωc + q.D) * Real.sin a),
    q.c0 + ε * Real.sin a]

@[tmio M, powerlib_domain] private theorem continuous_arc (ε : ℝ) : Continuous (q.arc ε) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [arc] <;> fun_prop

@[tmio M, powerlib_domain] private theorem arc_pi (ε : ℝ) : q.arc ε π = q.reflect (q.arc ε 0) := by
  ext i; fin_cases i <;> simp [arc, reflect] <;> ring

@[tmio M, powerlib_domain] private theorem reflect_apply (x : Fin 3 → ℝ) :
    q.reflect x 0 = 2 * (π + q.α) - x 0 ∧ q.reflect x 1 = -x 1 ∧
      q.reflect x 2 = 2 * q.c0 - x 2 := by
  simp [reflect]

/-- On the arc the reversed energy is strictly below the saddle level `A` (`P_ref = c₀`,
`0 < ε < π`). -/
@[tmio M, powerlib_domain] private theorem downEnergy_arc_lt (hP : q.Pref = q.c0) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < π) (a : ℝ) : q.downEnergy (q.arc ε a) < q.A := by
  have hM := q.M_pos; have hD := q.D_nonneg; have hω := q.ωc_pos; have hA := q.A_pos
  set η := ε / (1 + q.M * q.ωc + q.D) with hη
  have hη0 : 0 < η := by positivity
  have hηε : η * (q.M * q.ωc + q.D) < ε := by
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  have hE : q.downEnergy (q.arc ε a) = q.A * Real.cos (ε * Real.cos a) -
      Real.sin a ^ 2 * (η * (2 * ε - η * (q.M * q.ωc + q.D)) / (2 * q.ωc)) := by
    have hc : Real.cos (π + q.α + ε * Real.cos a - q.α) = -Real.cos (ε * Real.cos a) := by
      rw [show π + q.α + ε * Real.cos a - q.α = ε * Real.cos a + π by ring, Real.cos_add_pi]
    have e0 : q.arc ε a 0 = π + q.α + ε * Real.cos a := rfl
    have e1 : q.arc ε a 1 = -(η * Real.sin a) := rfl
    have e2 : q.arc ε a 2 = q.c0 + ε * Real.sin a := rfl
    simp only [downEnergy, e0, e1, e2, q.potential_balanced hP, hc, hP]
    field_simp
    ring
  rw [hE]
  have hpos : 0 < η * (2 * ε - η * (q.M * q.ωc + q.D)) / (2 * q.ωc) := by
    have : 0 < 2 * ε - η * (q.M * q.ωc + q.D) := by linarith
    positivity
  by_cases hs : Real.sin a = 0
  · have hc2 : Real.cos a ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq a]
    have hcos : Real.cos (ε * Real.cos a) = Real.cos ε := by
      rcases sq_eq_one_iff.1 hc2 with h | h <;> rw [h]
      · ring_nf
      · rw [mul_neg_one, Real.cos_neg]
    have hlt : Real.cos ε < 1 := by
      have h2 : 0 < Real.sin (ε / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have h3 : Real.cos ε = 1 - 2 * Real.sin (ε / 2) ^ 2 := by
        rw [show ε = 2 * (ε / 2) by ring, Real.cos_two_mul, Real.cos_sq']; ring_nf
      nlinarith
    rw [hs, hcos]
    nlinarith
  · have h1 : 0 < Real.sin a ^ 2 := by positivity
    have h2 : Real.cos (ε * Real.cos a) ≤ 1 := Real.cos_le_one _
    nlinarith [mul_pos h1 hpos]

/-- The exit sets are open (continuity of the flow in the initial state, `dist_dsol_le`). -/
@[tmio M, powerlib_domain] private theorem isOpen_exit (g : (Fin 3 → ℝ) → ℝ)
    (hg : ∀ x y, |g x - g y| ≤ dist x y) (c d : ℝ) :
    IsOpen {x | ∃ t, 0 ≤ t ∧ c < g (q.dsol x t) ∧ ∀ s ∈ Icc 0 t, d < g (q.dsol x s)} := by
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    rw [Real.dist_eq, NNReal.coe_one, one_mul]; exact hg x y).continuous
  rw [Metric.isOpen_iff]
  rintro x ⟨t, ht, hct, hall⟩
  have hcont : ContinuousOn (fun s => g (q.dsol x s)) (Icc 0 t) :=
    hgc.comp_continuousOn ((q.dsol_continuousOn x).mono Icc_subset_Ici_self)
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht) hcont
  set η := min (g (q.dsol x t) - c) (g (q.dsol x s₀) - d) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith [hall s₀ hs₀])
  have hE := Real.exp_pos (q.downLip * t)
  refine ⟨η / Real.exp (q.downLip * t), by positivity, fun y hy => ⟨t, ht, ?_, fun s hs => ?_⟩⟩
  · have key : |g (q.dsol y t) - g (q.dsol x t)| < η := by
      refine (hg _ _).trans_lt ((q.dist_dsol_le y x ht).trans_lt ?_)
      rw [Metric.mem_ball] at hy
      rwa [lt_div_iff₀ hE] at hy
    have := (abs_lt.1 key).1
    have := min_le_left (g (q.dsol x t) - c) (g (q.dsol x s₀) - d)
    linarith
  · have key : |g (q.dsol y s) - g (q.dsol x s)| < η := by
      refine (hg _ _).trans_lt ((q.dist_dsol_le y x hs.1).trans_lt ?_)
      rw [Metric.mem_ball] at hy
      have h1 : dist y x * Real.exp (q.downLip * s) ≤ dist y x * Real.exp (q.downLip * t) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2
          (q.downLip).2)) dist_nonneg
      rw [lt_div_iff₀ hE] at hy
      linarith
    have h1 := (abs_lt.1 key).1
    have h2 := min_le_right (g (q.dsol x t) - c) (g (q.dsol x s₀) - d)
    have h3 : g (q.dsol x s₀) ≤ g (q.dsol x s) := hmin hs
    linarith

/-- **Shooting** (`P_ref = c₀`): some point of the arc leaves the strip
`(π + α − 2π, π + α + 2π)` neither to the right first nor to the left first. -/
@[tmio M, powerlib_domain] private theorem exists_arc_stay (hP : q.Pref = q.c0) (ε : ℝ) :
    ∃ a, ¬ (∃ t, 0 ≤ t ∧ π + q.α + 2 * π < q.dsol (q.arc ε a) t 0 ∧
          ∀ s ∈ Icc 0 t, π + q.α - 2 * π < q.dsol (q.arc ε a) s 0) ∧
        ¬ (∃ t, 0 ≤ t ∧ q.dsol (q.arc ε a) t 0 < π + q.α - 2 * π ∧
          ∀ s ∈ Icc 0 t, q.dsol (q.arc ε a) s 0 < π + q.α + 2 * π) := by
  set lo := π + q.α - 2 * π
  set hi := π + q.α + 2 * π
  set R := {x | ∃ t, 0 ≤ t ∧ hi < q.dsol x t 0 ∧ ∀ s ∈ Icc 0 t, lo < q.dsol x s 0}
  set L := {x | ∃ t, 0 ≤ t ∧ q.dsol x t 0 < lo ∧ ∀ s ∈ Icc 0 t, q.dsol x s 0 < hi}
  have hc0 : ∀ x y : Fin 3 → ℝ, |x 0 - y 0| ≤ dist x y := fun x y => by
    have := dist_le_pi_dist x y 0; rwa [Real.dist_eq] at this
  have hRo : IsOpen R := q.isOpen_exit (fun x => x 0) hc0 hi lo
  have hLo : IsOpen L := by
    have h := q.isOpen_exit (fun x => -x 0) (fun x y => by
      rw [show -x 0 - -y 0 = -(x 0 - y 0) by ring, abs_neg]; exact hc0 x y) (-lo) (-hi)
    convert h using 1
    ext x
    exact ⟨fun ⟨t, ht, h1, h2⟩ => ⟨t, ht, neg_lt_neg h1, fun s hs => neg_lt_neg (h2 s hs)⟩,
      fun ⟨t, ht, h1, h2⟩ => ⟨t, ht, neg_lt_neg_iff.1 h1, fun s hs => neg_lt_neg_iff.1 (h2 s hs)⟩⟩
  have hdisj : ∀ x, x ∈ R → x ∈ L → False := by
    rintro x ⟨t₁, ht₁, h₁, a₁⟩ ⟨t₂, ht₂, h₂, a₂⟩
    rcases le_total t₁ t₂ with h | h
    · linarith [a₂ t₁ ⟨ht₁, h⟩]
    · linarith [a₁ t₂ ⟨ht₂, h⟩]
  have hval : ∀ x t, 0 ≤ t → q.dsol (q.reflect x) t 0 = 2 * (π + q.α) - q.dsol x t 0 :=
    fun x t ht => by rw [q.dsol_reflect hP x ht, (q.reflect_apply _).1]
  have hRL : ∀ x, x ∈ R → q.reflect x ∈ L := by
    rintro x ⟨t, ht, h1, h2⟩
    refine ⟨t, ht, ?_, fun s hs => ?_⟩
    · rw [hval x t ht]; linarith
    · rw [hval x s hs.1]; linarith [h2 s hs]
  have hLR : ∀ x, x ∈ L → q.reflect x ∈ R := by
    rintro x ⟨t, ht, h1, h2⟩
    refine ⟨t, ht, ?_, fun s hs => ?_⟩
    · rw [hval x t ht]; linarith
    · rw [hval x s hs.1]; linarith [h2 s hs]
  by_contra hcon
  have hcov : ∀ a, q.arc ε a ∈ R ∨ q.arc ε a ∈ L := fun a => by
    by_contra h'
    push Not at h'
    exact hcon ⟨a, h'.1, h'.2⟩
  have hU := hRo.preimage (q.continuous_arc ε)
  have hV := hLo.preimage (q.continuous_arc ε)
  have hsub : Icc 0 π ⊆ q.arc ε ⁻¹' R ∪ q.arc ε ⁻¹' L := fun a _ => hcov a
  have h0 : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have hπ : π ∈ Icc 0 π := ⟨Real.pi_pos.le, le_rfl⟩
  rcases hcov 0 with h | h
  · obtain ⟨a, -, ha1, ha2⟩ := isPreconnected_Icc _ _ hU hV hsub ⟨0, h0, h⟩
      ⟨π, hπ, by rw [mem_preimage, q.arc_pi]; exact hRL _ h⟩
    exact hdisj _ ha1 ha2
  · obtain ⟨a, -, ha1, ha2⟩ := isPreconnected_Icc _ _ hU hV hsub
      ⟨π, hπ, by rw [mem_preimage, q.arc_pi]; exact hLR _ h⟩ ⟨0, h0, h⟩
    exact hdisj _ ha1 ha2

/-- A contact with the right wall `π + α + 2π` at a time `τ > 0` after staying inside is a right
exit first (the frequency there is not zero, as `F_R < A`). -/
@[tmio M, powerlib_domain] private theorem hit_right (hP : q.Pref = q.c0) {x : Fin 3 → ℝ}
    (hE : q.downEnergy x < q.A)
    (hR : ¬ ∃ t, 0 ≤ t ∧ π + q.α + 2 * π < q.dsol x t 0 ∧
      ∀ s ∈ Icc 0 t, π + q.α - 2 * π < q.dsol x s 0)
    {τ : ℝ} (hτ : 0 < τ) (hτv : q.dsol x τ 0 = π + q.α + 2 * π)
    (hbefore : ∀ t, 0 ≤ t → t < τ → q.dsol x t 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π)) :
    False := by
  set f := fun t => q.dsol x t 0 with hf
  set g := fun t => q.dsol x t 1 with hg
  have hfd : ∀ t, 0 < t → HasDerivAt f (g t) t := fun t ht => q.dsol_coord_hasDerivAt x 0 ht
  have hgc : ∀ t, 0 < t → ContinuousAt g t := fun t ht =>
    (q.dsol_coord_hasDerivAt x 1 ht).continuousAt
  -- the frequency at the contact is not zero
  have hg0 : g τ ≠ 0 := by
    intro h0
    have hEτ := q.downEnergy_le x hτ.le
    have hval : q.downEnergy (q.dsol x τ) = q.A := by
      have hc : Real.cos (π + q.α + 2 * π - q.α) = -1 := by
        rw [show π + q.α + 2 * π - q.α = π + 2 * π by ring, Real.cos_add_two_pi, Real.cos_pi]
      have h1 : q.dsol x τ 1 = 0 := h0
      simp only [downEnergy, h1, hτv, q.potential_balanced hP, hc]
      ring
    linarith
  -- a neighbourhood of `τ` where the frequency keeps its sign
  obtain ⟨h, hh, hhτ, hsign⟩ : ∃ h > 0, h < τ ∧ ∀ t ∈ Ioo (τ - h) (τ + h), 0 < g t * g τ := by
    have hev' : ∀ᶠ t in 𝓝 τ, 0 < g t * g τ := by
      have hm : ContinuousAt (fun t => g t * g τ) τ := (hgc τ hτ).mul continuousAt_const
      exact hm.eventually (lt_mem_nhds (mul_self_pos.2 hg0))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev'
    refine ⟨min r (τ / 2), lt_min hr (by linarith), by
      have := min_le_right r (τ / 2); linarith, fun t ht => hball t ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have := min_le_left r (τ / 2)
    constructor <;> linarith [ht.1, ht.2]
  have hpos : ∀ t ∈ Ioo (τ - h) (τ + h), 0 < t := fun t ht => by linarith [ht.1]
  have hcontI : ContinuousOn f (Icc (τ - h / 2) (τ + h / 2)) := fun t ht =>
    (hfd t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hderI : ∀ t ∈ interior (Icc (τ - h / 2) (τ + h / 2)),
      HasDerivWithinAt f (g t) (interior (Icc (τ - h / 2) (τ + h / 2))) t := fun t ht => by
    rw [interior_Icc] at ht
    exact (hfd t (by linarith [ht.1])).hasDerivWithinAt
  have hin : ∀ t ∈ interior (Icc (τ - h / 2) (τ + h / 2)), t ∈ Ioo (τ - h) (τ + h) :=
    fun t ht => by rw [interior_Icc] at ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hm1 : τ - h / 2 ∈ Icc (τ - h / 2) (τ + h / 2) := ⟨le_rfl, by linarith⟩
  have hm2 : τ ∈ Icc (τ - h / 2) (τ + h / 2) := ⟨by linarith, by linarith⟩
  have hm3 : τ + h / 2 ∈ Icc (τ - h / 2) (τ + h / 2) := ⟨by linarith, le_rfl⟩
  rcases lt_or_gt_of_ne hg0 with hneg | hpos'
  · -- decreasing through the wall: the state was beyond it just before `τ`
    have hanti := strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _) hcontI hderI
      (fun t ht => by
        have := hsign t (hin t ht)
        nlinarith)
    have h1 := hanti hm1 hm2 (by linarith)
    have h2 := (hbefore (τ - h / 2) (by linarith) (by linarith)).2
    simp only [hf] at h1
    linarith
  · -- increasing through the wall: a right exit first
    have hmono := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hcontI hderI
      (fun t ht => by
        have := hsign t (hin t ht)
        nlinarith)
    refine hR ⟨τ + h / 2, by linarith, ?_, fun s hs => ?_⟩
    · have := hmono hm2 hm3 (by linarith)
      simp only [hf] at this
      linarith
    · rcases lt_or_ge s τ with hs1 | hs1
      · exact (hbefore s hs.1 hs1).1
      · rcases hs1.lt_or_eq with hs2 | hs2
        · have := hmono hm2 ⟨by linarith, hs.2⟩ hs2
          simp only [hf] at this
          linarith [Real.pi_pos]
        · rw [← hs2, hτv]; linarith [Real.pi_pos]

/-- **The selected orbit never leaves the strip** (`P_ref = c₀`): a start inside the strip with
`F_R < A` that is neither a right-first nor a left-first exit stays strictly inside forever. -/
@[tmio M, powerlib_domain] private theorem stays_in_strip (hP : q.Pref = q.c0)
    {x : Fin 3 → ℝ} (hx : x 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π))
    (hE : q.downEnergy x < q.A)
    (hR : ¬ ∃ t, 0 ≤ t ∧ π + q.α + 2 * π < q.dsol x t 0 ∧
      ∀ s ∈ Icc 0 t, π + q.α - 2 * π < q.dsol x s 0)
    (hL : ¬ ∃ t, 0 ≤ t ∧ q.dsol x t 0 < π + q.α - 2 * π ∧
      ∀ s ∈ Icc 0 t, q.dsol x s 0 < π + q.α + 2 * π) :
    ∀ t, 0 ≤ t → q.dsol x t 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π) := by
  set lo := π + q.α - 2 * π with hlo
  set hi := π + q.α + 2 * π with hhi
  by_contra hcon
  push Not at hcon
  obtain ⟨t₁, ht₁, hout⟩ := hcon
  set S := Ici (0 : ℝ) ∩ (fun t => q.dsol x t 0) ⁻¹' (Ioo lo hi)ᶜ with hS
  have hfc : ContinuousOn (fun t => q.dsol x t 0) (Ici 0) :=
    (continuous_apply 0).comp_continuousOn (q.dsol_continuousOn x)
  have hSc : IsClosed S := hfc.preimage_isClosed_of_isClosed isClosed_Ici
    isOpen_Ioo.isClosed_compl
  have hSne : S.Nonempty := ⟨t₁, ht₁, hout⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set τ := sInf S with hτdef
  have hτS : τ ∈ S := hSc.csInf_mem hSne hSb
  have hτ0 : 0 < τ := by
    rcases (mem_Ici.1 hτS.1).lt_or_eq with h | h
    · exact h
    · exfalso; have := hτS.2; rw [← h] at this
      simp only [mem_preimage, mem_compl_iff, q.dsol_zero] at this
      exact this hx
  have hbefore : ∀ t, 0 ≤ t → t < τ → q.dsol x t 0 ∈ Ioo lo hi := by
    intro t ht htτ
    by_contra hn
    exact absurd (csInf_le hSb ⟨ht, hn⟩) (not_le.2 htτ)
  have hcτ : ContinuousAt (fun t => q.dsol x t 0) τ :=
    (q.dsol_coord_hasDerivAt x 0 hτ0).continuousAt
  -- the contact value is a wall
  have hwall : q.dsol x τ 0 = lo ∨ q.dsol x τ 0 = hi := by
    have hle : lo ≤ q.dsol x τ 0 ∧ q.dsol x τ 0 ≤ hi := by
      constructor
      · by_contra h; push Not at h
        obtain ⟨t, ht1, ht2⟩ := ((hcτ.eventually (gt_mem_nhds h)).filter_mono
          nhdsWithin_le_nhds |>.and (Ioo_mem_nhdsLT hτ0)).exists
        exact absurd (hbefore t ht2.1.le ht2.2).1 (not_lt.2 ht1.le)
      · by_contra h; push Not at h
        obtain ⟨t, ht1, ht2⟩ := ((hcτ.eventually (lt_mem_nhds h)).filter_mono
          nhdsWithin_le_nhds |>.and (Ioo_mem_nhdsLT hτ0)).exists
        exact absurd (hbefore t ht2.1.le ht2.2).2 (not_lt.2 ht1.le)
    have hn := hτS.2
    simp only [mem_preimage, mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hn
    rcases hn with h | h
    · left; linarith [hle.1]
    · right; linarith [hle.2]
  rcases hwall with hlo' | hhi'
  · -- the left wall: reflect
    have hval : ∀ t, 0 ≤ t → q.dsol (q.reflect x) t 0 = 2 * (π + q.α) - q.dsol x t 0 :=
      fun t ht => by rw [q.dsol_reflect hP x ht, (q.reflect_apply _).1]
    refine q.hit_right hP (x := q.reflect x) (by rwa [q.downEnergy_reflect hP]) ?_ hτ0
      (by rw [hval τ hτ0.le, hlo']; ring) (fun t ht htτ => ?_)
    · rintro ⟨t, ht, h1, h2⟩
      refine hL ⟨t, ht, ?_, fun s hs => ?_⟩
      · rw [hval t ht] at h1; linarith
      · have := h2 s hs; rw [hval s hs.1] at this; linarith
    · have := hbefore t ht htτ
      rw [hval t ht]
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
  · exact q.hit_right hP hE hR hτ0 hhi' hbefore

/-! ## Bounds and convergence of the selected orbit -/

/-- In the strip the filter stays below `c₀ + A` (`P_ref = c₀`): beyond it the filter grows, so
`M ω + D δ` decreases at a rate `≥ A`, the frequency becomes `≤ −1` and the angle leaves the
strip. -/
@[tmio M, powerlib_domain] private theorem filter_le (hP : q.Pref = q.c0) {x : Fin 3 → ℝ}
    (hstay : ∀ t, 0 ≤ t → q.dsol x t 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π)) :
    ∀ t, 0 ≤ t → q.dsol x t 2 ≤ q.c0 + q.A := by
  intro t₀ ht₀
  by_contra hcon
  push Not at hcon
  have hM := q.M_pos; have hA := q.A_pos; have hω := q.ωc_pos; have hD := q.D_nonneg
  set lo := π + q.α - 2 * π with hlo
  have hd : ∀ i : Fin 3, ∀ t, t₀ < t →
      HasDerivAt (fun s => q.dsol x s i) (q.downField (q.dsol x t) i) t :=
    fun i t ht => q.dsol_coord_hasDerivAt x i (by linarith)
  have hcI : ∀ i : Fin 3, ContinuousOn (fun s => q.dsol x s i) (Ici t₀) := fun i =>
    ((continuous_apply i).comp_continuousOn (q.dsol_continuousOn x)).mono
      (Ici_subset_Ici.2 ht₀)
  -- (i) the filter stays above `c₀ + A`
  have hz : ∀ t, t₀ ≤ t → q.c0 + q.A < q.dsol x t 2 := by
    have hmono : MonotoneOn (fun t => (q.dsol x t 2 - q.c0 - q.A) *
        Real.exp (-(q.ωc * (t - t₀)))) (Ici t₀) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t₀)
        (f' := fun t => q.ωc * q.A * (1 - Real.sin (q.dsol x t 0 - q.α)) *
          Real.exp (-(q.ωc * (t - t₀))))
        (((hcI 2).sub continuousOn_const).sub continuousOn_const |>.mul
          (by fun_prop : Continuous fun t => Real.exp (-(q.ωc * (t - t₀)))).continuousOn)
        (fun t ht => ?_) (fun t _ => ?_)
      · rw [interior_Ici] at ht
        have hE : HasDerivAt (fun t => Real.exp (-(q.ωc * (t - t₀))))
            (Real.exp (-(q.ωc * (t - t₀))) * -(q.ωc * 1)) t :=
          (((hasDerivAt_id' t).sub_const t₀).const_mul q.ωc).neg.exp
        refine ((((hd 2 t ht).sub_const q.c0).sub_const q.A).mul hE).hasDerivWithinAt.congr_deriv ?_
        simp only [downField, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        ring
      · have := Real.sin_le_one (q.dsol x t 0 - q.α)
        have : 0 ≤ 1 - Real.sin (q.dsol x t 0 - q.α) := by linarith
        positivity
    intro t ht
    have h := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
    simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    have h1 : 0 < (q.dsol x t 2 - q.c0 - q.A) * Real.exp (-(q.ωc * (t - t₀))) := by linarith
    have h2 := (pos_iff_pos_of_mul_pos h1).2 (Real.exp_pos _)
    linarith
  -- (ii) `M ω + D δ + A t` is antitone after `t₀`
  set G := fun t => q.M * q.dsol x t 1 + q.D * q.dsol x t 0 with hGdef
  have hG : ∀ t, t₀ ≤ t → G t ≤ G t₀ - q.A * (t - t₀) := by
    have hanti : AntitoneOn (fun t => G t + q.A * t) (Ici t₀) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀)
        (f' := fun t => q.Pref - q.dsol x t 2 + q.A)
        ((((hcI 1).const_smul q.M).add ((hcI 0).const_smul q.D)).add
          (continuousOn_const.mul continuousOn_id)) (fun t ht => ?_) (fun t ht => ?_)
      · rw [interior_Ici] at ht
        refine ((((hd 1 t ht).const_mul q.M).add ((hd 0 t ht).const_mul q.D)).add
          ((hasDerivAt_id' t).const_mul q.A)).hasDerivWithinAt.congr_deriv ?_
        simp only [downField, Matrix.cons_val_one, Matrix.cons_val_zero]
        field_simp
        ring
      · rw [interior_Ici] at ht
        have := hz t ht.le
        rw [hP]; linarith
    intro t ht
    have := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
    simp only at this
    linarith
  -- (iii) the frequency is `≤ −1` after `t₁`
  set t₁ := t₀ + |G t₀ - q.D * lo + q.M| / q.A + 1 with ht₁
  have ht₁0 : t₀ < t₁ := by
    have : 0 ≤ |G t₀ - q.D * lo + q.M| / q.A := by positivity
    linarith
  have hw : ∀ t, t₁ ≤ t → q.dsol x t 1 ≤ -1 := by
    intro t ht
    have h1 := hG t (by linarith)
    have h2 : q.D * lo ≤ q.D * q.dsol x t 0 :=
      mul_le_mul_of_nonneg_left (hstay t (by linarith)).1.le hD
    have h3 : G t₀ - q.D * lo + q.M ≤ q.A * (t - t₀) := by
      have := le_abs_self (G t₀ - q.D * lo + q.M)
      have h4 : |G t₀ - q.D * lo + q.M| / q.A ≤ t - t₀ := by linarith
      rw [div_le_iff₀ hA] at h4
      linarith
    have : q.M * q.dsol x t 1 ≤ -q.M := by simp only [hGdef] at h1; linarith
    nlinarith
  -- (iv) the angle leaves the strip
  have hanti2 : AntitoneOn (fun t => q.dsol x t 0 + t) (Ici t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₁)
      (f' := fun t => q.dsol x t 1 + 1)
      (((hcI 0).mono (Ici_subset_Ici.2 ht₁0.le)).add continuousOn_id) (fun t ht => ?_)
      (fun t ht => ?_)
    · rw [interior_Ici] at ht
      exact ((hd 0 t (by linarith [ht.out])).add (hasDerivAt_id' t)).hasDerivWithinAt
    · rw [interior_Ici] at ht
      linarith [hw t ht.out.le]
  set t₂ := t₁ + |q.dsol x t₁ 0 - lo| + 1
  have h1 := hanti2 (mem_Ici.2 le_rfl) (mem_Ici.2 (by
    have := abs_nonneg (q.dsol x t₁ 0 - lo); show t₁ ≤ t₂; linarith))
    (show t₁ ≤ t₂ by have := abs_nonneg (q.dsol x t₁ 0 - lo); linarith)
  have h2 := (hstay t₂ (by have := abs_nonneg (q.dsol x t₁ 0 - lo); linarith)).1
  have h3 := le_abs_self (q.dsol x t₁ 0 - lo)
  simp only at h1
  linarith

/-- In the strip the filter stays within `A` of `c₀` (`filter_le` and the reflection). -/
@[tmio M, powerlib_domain] private theorem abs_filter_le (hP : q.Pref = q.c0) {x : Fin 3 → ℝ}
    (hstay : ∀ t, 0 ≤ t → q.dsol x t 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π)) :
    ∀ t, 0 ≤ t → |q.dsol x t 2 - q.c0| ≤ q.A := by
  intro t ht
  have h1 := q.filter_le hP hstay t ht
  have hstay' : ∀ t, 0 ≤ t →
      q.dsol (q.reflect x) t 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π) := fun t ht => by
    rw [q.dsol_reflect hP x ht, (q.reflect_apply _).1]
    have := hstay t ht
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have h2 := q.filter_le hP hstay' t ht
  rw [q.dsol_reflect hP x ht, (q.reflect_apply _).2.2] at h2
  rw [abs_le]; constructor <;> linarith

/-- The frequency stays within `A/D` (`D > 0`, `|P_f − c₀| ≤ A`, `P_ref = c₀`): beyond it the
damping dominates and `ω²` decreases. -/
@[tmio M, powerlib_domain] private theorem freq_le (hP : q.Pref = q.c0) (hD : 0 < q.D)
    {x : Fin 3 → ℝ} (hx1 : |x 1| ≤ q.A / q.D)
    (hz : ∀ t, 0 ≤ t → |q.dsol x t 2 - q.c0| ≤ q.A) :
    ∀ t, 0 ≤ t → |q.dsol x t 1| ≤ q.A / q.D := by
  have hM := q.M_pos; have hA := q.A_pos
  set c := (q.A / q.D) ^ 2 with hc
  set W := fun t => q.dsol x t 1 * q.dsol x t 1 with hW
  have hWc : ContinuousOn W (Ici 0) := by
    have := (continuous_apply 1).comp_continuousOn (q.dsol_continuousOn x)
    exact this.mul this
  have habs : ∀ t, |q.dsol x t 1| ≤ q.A / q.D ↔ W t ≤ c := fun t => by
    simp only [hW, hc, ← sq]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).symm.trans (by rw [sq_abs])
  intro t₁ ht₁
  rw [habs]
  by_contra hcon
  push Not at hcon
  set K := Icc 0 t₁ ∩ W ⁻¹' Iic c with hK
  have hKc : IsClosed K := (hWc.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_Iic
  have h0K : (0 : ℝ) ∈ K := ⟨⟨le_rfl, ht₁⟩, by
    show W 0 ≤ c; rw [← habs, q.dsol_zero]; exact hx1⟩
  have hKb : BddAbove K := ⟨t₁, fun t ht => ht.1.2⟩
  set T₀ := sSup K
  have hT₀K : T₀ ∈ K := hKc.csSup_mem ⟨0, h0K⟩ hKb
  have hT₀t : T₀ < t₁ := by
    rcases hT₀K.1.2.lt_or_eq with h | h
    · exact h
    · exfalso; have := hT₀K.2; rw [h] at this; exact absurd this (not_le.2 hcon)
  have hgt : ∀ t, T₀ < t → t ≤ t₁ → c < W t := fun t h1 h2 => by
    by_contra h; push Not at h
    have := le_csSup hKb ⟨⟨by linarith [hT₀K.1.1], h2⟩, h⟩
    linarith
  have hT₀0 : 0 ≤ T₀ := hT₀K.1.1
  have hanti : AntitoneOn W (Icc T₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun t => 2 * q.dsol x t 1 * ((q.Pref - q.dsol x t 2 - q.D * q.dsol x t 1) / q.M))
      (hWc.mono fun t ht => mem_Ici.2 (hT₀0.trans ht.1)) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      have h := q.dsol_coord_hasDerivAt x 1 (show 0 < t by linarith [ht.1])
      refine (h.mul h).hasDerivWithinAt.congr_deriv ?_
      simp only [downField, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    · rw [interior_Icc] at ht
      have hWt := hgt t ht.1 ht.2.le
      have hzt := hz t (by linarith [ht.1])
      rw [hP]
      set w := q.dsol x t 1
      set z := q.dsol x t 2
      have hw : q.A / q.D < |w| := by
        by_contra h; push Not at h
        exact absurd ((habs t).1 h) (not_le.2 hWt)
      have hDw : q.A < q.D * |w| := by rwa [div_lt_iff₀ hD, mul_comm] at hw
      have key : w * (q.c0 - z - q.D * w) ≤ |w| * (q.A - q.D * |w|) := by
        have h1 : w * (q.c0 - z) ≤ |w| * q.A := by
          calc w * (q.c0 - z) ≤ |w * (q.c0 - z)| := le_abs_self _
            _ = |w| * |z - q.c0| := by rw [abs_mul, abs_sub_comm]
            _ ≤ |w| * q.A := mul_le_mul_of_nonneg_left hzt (abs_nonneg _)
        have h2 : q.D * w * w = q.D * |w| * |w| := by
          rw [mul_assoc, mul_assoc, ← abs_mul_abs_self w]
        nlinarith
      have hneg : |w| * (q.A - q.D * |w|) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (by linarith)
      have : 2 * w * ((q.c0 - z - q.D * w) / q.M) = 2 * (w * (q.c0 - z - q.D * w)) / q.M := by
        ring
      rw [this]
      apply div_nonpos_of_nonpos_of_nonneg _ hM.le
      linarith
  have := hanti ⟨le_rfl, hT₀t.le⟩ ⟨hT₀t.le, le_rfl⟩ hT₀t.le
  have h5 : W T₀ ≤ c := hT₀K.2
  linarith

/-- The two stable equilibria in the strip. -/
@[tmio M, powerlib_domain] private theorem rest_of_const (hP : q.Pref = q.c0) (hD : 0 < q.D)
    {p : Fin 3 → ℝ} (hp0 : p 0 ∈ Icc (π + q.α - 2 * π) (π + q.α + 2 * π))
    (hpE : q.downEnergy p < q.A)
    (hconst : ∀ t, 0 ≤ t → q.downEnergy (q.dsol p t) = q.downEnergy p) :
    p = ![q.α, 0, q.c0] ∨ p = ![q.α + 2 * π, 0, q.c0] := by
  have hM := q.M_pos; have hω := q.ωc_pos; have hA := q.A_pos
  -- the decay rate vanishes for `t > 0`
  have hrate : ∀ t, 0 < t → q.dsol p t 1 = 0 ∧ q.dsol p t 2 = q.Pref := by
    intro t ht
    have h1 := (q.hasDerivWithinAt_downEnergy p ht.le).hasDerivAt (Ici_mem_nhds ht)
    have h2 : HasDerivAt (fun s => q.downEnergy (q.dsol p s)) 0 t :=
      (hasDerivAt_const t (q.downEnergy p)).congr_of_eventuallyEq
        (Filter.mem_of_superset (Ioi_mem_nhds ht) fun s hs => hconst s (le_of_lt hs))
    have h3 := h1.unique h2
    set w := q.dsol p t 1
    set a := (q.Pref - q.dsol p t 2 - q.D * w) / q.M
    have hw2 : 0 ≤ q.D * w ^ 2 := by positivity
    have ha2 : 0 ≤ q.M / q.ωc * a ^ 2 := by positivity
    have hw : w = 0 := by
      have : q.D * w ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        ((mul_eq_zero.1 this).resolve_left hD.ne')
    have ha : a = 0 := by
      have : q.M / q.ωc * a ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        ((mul_eq_zero.1 this).resolve_left (by positivity))
    refine ⟨hw, ?_⟩
    have : q.Pref - q.dsol p t 2 - q.D * w = 0 := by
      rw [div_eq_zero_iff] at ha; exact ha.resolve_right hM.ne'
    rw [hw] at this; linarith
  have hsin : ∀ t, 0 < t → Real.sin (q.dsol p t 0 - q.α) = 0 := by
    intro t ht
    have h1 := q.dsol_coord_hasDerivAt p 2 ht
    have h2 : HasDerivAt (fun s => q.dsol p s 2) 0 t :=
      (hasDerivAt_const t q.Pref).congr_of_eventuallyEq
        (Filter.mem_of_superset (Ioi_mem_nhds ht) fun s hs => (hrate s hs).2)
    have h3 := h1.unique h2
    simp only [downField, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      (hrate t ht).2, hP] at h3
    have : q.A * Real.sin (q.dsol p t 0 - q.α) = 0 := by
      have := (mul_eq_zero.1 h3).resolve_left hω.ne'; linarith
    exact (mul_eq_zero.1 this).resolve_left hA.ne'
  -- limits at `0⁺`
  have hlim : Tendsto (q.dsol p) (𝓝[>] 0) (𝓝 p) := by
    have := ((q.dsol_continuousOn p) 0 (mem_Ici.2 le_rfl)).tendsto
    rw [q.dsol_zero] at this
    exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hp1 : p 1 = 0 := by
    have h := ((continuous_apply 1).tendsto p).comp hlim
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun t ht =>
      ((hrate t ht).1).symm))
  have hp2 : p 2 = q.c0 := by
    have h := ((continuous_apply 2).tendsto p).comp hlim
    rw [← hP]
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun t ht =>
      ((hrate t ht).2).symm))
  have hp0' : Real.sin (p 0 - q.α) = 0 := by
    have hc : Continuous fun y : Fin 3 → ℝ => Real.sin (y 0 - q.α) := by fun_prop
    have h := (hc.tendsto p).comp hlim
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun t ht =>
      ((hsin t ht)).symm))
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hp0'
  have hpi := Real.pi_pos
  have hn1 : (-1 : ℝ) ≤ n := by
    have : (-1 : ℝ) * π ≤ n * π := by rw [hn]; linarith [hp0.1]
    exact le_of_mul_le_mul_right this hpi
  have hn3 : (n : ℝ) ≤ 3 := by
    have : n * π ≤ 3 * π := by rw [hn]; linarith [hp0.2]
    exact le_of_mul_le_mul_right this hpi
  have hn1' : -1 ≤ n := by exact_mod_cast hn1
  have hn3' : n ≤ 3 := by exact_mod_cast hn3
  have hE : q.downEnergy p = -(q.A * Real.cos (n * π)) := by
    simp only [downEnergy, hp1, q.potential_balanced hP, ← hn]; ring
  have hodd : ∀ m : ℤ, n = m → Real.cos (m * π) = -1 → False := fun m hm hc => by
    rw [hE, hm, hc] at hpE; linarith
  have hp : p = ![q.α + n * π, 0, q.c0] := by
    ext i; fin_cases i
    · simp; linarith
    · simp [hp1]
    · simp [hp2]
  interval_cases n
  · exact (hodd (-1) rfl (by push_cast; rw [neg_one_mul, Real.cos_neg, Real.cos_pi])).elim
  · left; rw [hp]; simp
  · exact (hodd 1 rfl (by push_cast; rw [one_mul, Real.cos_pi])).elim
  · right; rw [hp]; push_cast; ring_nf
  · exact (hodd 3 rfl (by
      push_cast; rw [show (3 : ℝ) * π = π + 2 * π by ring, Real.cos_add_two_pi, Real.cos_pi])).elim

/-- **The selected orbit converges to a stable equilibrium** (`P_ref = c₀`, `D > 0`): an orbit that
stays in the strip with `F_R < A` and `|ω(0)| ≤ A/D` converges to `(α, 0, c₀)` or to
`(α + 2π, 0, c₀)` (LaSalle along the orbit, `Dynamics.tendsto_nhdsSet_of_antitone`). -/
@[tmio M, powerlib_domain] private theorem tendsto_rest (hP : q.Pref = q.c0) (hD : 0 < q.D)
    {x : Fin 3 → ℝ} (hE : q.downEnergy x < q.A) (hx1 : |x 1| ≤ q.A / q.D)
    (hstay : ∀ t, 0 ≤ t → q.dsol x t 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π)) :
    Tendsto (q.dsol x) atTop (𝓝 ![q.α, 0, q.c0]) ∨
      Tendsto (q.dsol x) atTop (𝓝 ![q.α + 2 * π, 0, q.c0]) := by
  set lo := π + q.α - 2 * π
  set hi := π + q.α + 2 * π
  have hz := q.abs_filter_le hP hstay
  have hw := q.freq_le hP hD hx1 hz
  set B := {y : Fin 3 → ℝ | lo ≤ y 0} ∩ {y | y 0 ≤ hi} ∩ {y | |y 1| ≤ q.A / q.D} ∩
    {y | |y 2 - q.c0| ≤ q.A} ∩ {y | q.downEnergy y ≤ q.downEnergy x} with hB
  have hBc : IsCompact B := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine (((isClosed_le continuous_const (continuous_apply 0)).inter
        (isClosed_le (continuous_apply 0) continuous_const)).inter
        (isClosed_le (continuous_apply 1).abs continuous_const)).inter
        (isClosed_le ((continuous_apply 2).sub continuous_const).abs continuous_const) |>.inter
        (isClosed_le q.continuous_downEnergy continuous_const)
    · refine isBounded_iff_forall_norm_le.2 ⟨|lo| + |hi| + q.A / q.D + |q.c0| + q.A, ?_⟩
      rintro y ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩
      have h0 : lo ≤ y 0 := h0
      have h1 : y 0 ≤ hi := h1
      have h2 : |y 1| ≤ q.A / q.D := h2
      have h3 : |y 2 - q.c0| ≤ q.A := h3
      have hA := q.A_pos
      have hAD : 0 ≤ q.A / q.D := by positivity
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      fin_cases i
      · show |y 0| ≤ _
        have : |y 0| ≤ |lo| + |hi| := by
          rw [abs_le]; constructor
          · linarith [neg_abs_le lo, abs_nonneg hi]
          · linarith [le_abs_self hi, abs_nonneg lo]
        linarith [abs_nonneg q.c0]
      · show |y 1| ≤ _
        linarith [abs_nonneg lo, abs_nonneg hi, abs_nonneg q.c0]
      · show |y 2| ≤ _
        have : |y 2| ≤ |q.c0| + q.A := by
          calc |y 2| = |(y 2 - q.c0) + q.c0| := by ring_nf
            _ ≤ |y 2 - q.c0| + |q.c0| := abs_add_le _ _
            _ ≤ q.A + |q.c0| := by linarith
            _ = |q.c0| + q.A := by ring
        linarith [abs_nonneg lo, abs_nonneg hi]
  have hxB : ∀ t : ℝ, 0 ≤ t → forwardSolution q.lipschitzWith_downField x t ∈ B := by
    intro t ht
    exact ⟨⟨⟨⟨(hstay t ht).1.le, (hstay t ht).2.le⟩, hw t ht⟩, hz t ht⟩, q.downEnergy_le x ht⟩
  set Z : Set (Fin 3 → ℝ) := {![q.α, 0, q.c0], ![q.α + 2 * π, 0, q.c0]} with hZdef
  have hT := tendsto_nhdsSet_of_antitone q.lipschitzWith_downField hBc hxB
    q.continuous_downEnergy (Z := Z)
    (fun s t hs hst => q.downEnergy_antitone x (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst)
    (fun p hp hconst => by
      obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, hpE⟩ := hp
      rcases q.rest_of_const hP hD ⟨h0, h1⟩ (hpE.trans_lt hE) hconst with h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr rfl)
  -- two disjoint balls
  set z₁ : Fin 3 → ℝ := ![q.α, 0, q.c0]
  set z₂ : Fin 3 → ℝ := ![q.α + 2 * π, 0, q.c0]
  have hdisj : Disjoint (Metric.ball z₁ 1) (Metric.ball z₂ 1) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    rw [Metric.mem_ball] at h1 h2
    have h3 := dist_triangle_left z₁ z₂ y
    have h4 : 2 * π ≤ dist z₁ z₂ := by
      have := dist_le_pi_dist z₁ z₂ 0
      rw [Real.dist_eq] at this
      simp only [z₁, z₂, Matrix.cons_val_zero] at this
      rw [show q.α - (q.α + 2 * π) = -(2 * π) by ring, abs_neg,
        abs_of_pos (by positivity)] at this
      exact this
    linarith [Real.two_le_pi]
  have hZU : Z ⊆ Metric.ball z₁ 1 ∪ Metric.ball z₂ 1 := by
    intro y hy
    rcases hy with rfl | rfl
    · left; exact Metric.mem_ball_self one_pos
    · right; exact Metric.mem_ball_self one_pos
  have hev : ∀ᶠ t in atTop, q.dsol x t ∈ Metric.ball z₁ 1 ∪ Metric.ball z₂ 1 :=
    hT ((Metric.isOpen_ball.union Metric.isOpen_ball).mem_nhdsSet.2 hZU)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 0))
  have hpre : IsPreconnected (q.dsol x '' Ici (max T₀ 0)) :=
    isPreconnected_Ici.image _ ((q.dsol_continuousOn x).mono (Ici_subset_Ici.2 (le_max_right _ _)))
  have hsub : q.dsol x '' Ici (max T₀ 0) ⊆ Metric.ball z₁ 1 ∪ Metric.ball z₂ 1 := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hT₀ t ((le_max_left _ _).trans ht)).1
  have hconv : ∀ (z w : Fin 3 → ℝ), z ∈ Z → w ∈ Z → z ≠ w →
      Disjoint (Metric.ball z 1) (Metric.ball w 1) →
      q.dsol x '' Ici (max T₀ 0) ⊆ Metric.ball z 1 → Tendsto (q.dsol x) atTop (𝓝 z) := by
    intro z w hz hw hzw hd hs
    refine (nhds_basis_opens z).tendsto_right_iff.2 fun W ⟨hzW, hWo⟩ => ?_
    have hZ' : Z ⊆ (W ∩ Metric.ball z 1) ∪ Metric.ball w 1 := by
      intro y hy
      rcases hy with rfl | rfl
      · rcases hz with rfl | rfl
        · left; exact ⟨hzW, Metric.mem_ball_self one_pos⟩
        · right
          rcases hw with rfl | rfl
          · exact Metric.mem_ball_self one_pos
          · exact absurd rfl hzw
      · rcases hz with rfl | rfl
        · rcases hw with rfl | rfl
          · exact absurd rfl hzw
          · right; exact Metric.mem_ball_self one_pos
        · left; exact ⟨hzW, Metric.mem_ball_self one_pos⟩
    have h1 := hT (((hWo.inter Metric.isOpen_ball).union Metric.isOpen_ball).mem_nhdsSet.2 hZ')
    filter_upwards [h1, eventually_ge_atTop (max T₀ 0)] with t ht ht'
    rcases ht with h | h
    · exact h.1
    · exact absurd h (Set.disjoint_left.1 hd (hs ⟨t, ht', rfl⟩))
  have hne : z₁ ≠ z₂ := by
    intro h
    have := congrFun h 0
    simp only [z₁, z₂, Matrix.cons_val_zero] at this
    linarith [Real.pi_pos]
  rcases hpre.subset_or_subset Metric.isOpen_ball Metric.isOpen_ball hdisj hsub with h | h
  · exact Or.inl (hconv z₁ z₂ (Or.inl rfl) (Or.inr rfl) hne hdisj h)
  · exact Or.inr (hconv z₂ z₁ (Or.inr rfl) (Or.inl rfl) hne.symm hdisj.symm h)

/-- **A reversed orbit from the saddle's neighbourhood to the stable equilibrium**
(`P_ref = c₀`, `D > 0`, `0 < ε < π`, `ε ≤ A/D`): some state `y` within `ε` of the saddle
`(π + α, 0, c₀)`, with `F_R(y) < A`, has its reversed orbit converge to `(α, 0, c₀)` with the
filter within `A` of `c₀` throughout. -/
@[tmio M, powerlib_domain] private theorem exists_saddle_orbit (hP : q.Pref = q.c0)
    (hD : 0 < q.D) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < π) (hεD : ε ≤ q.A / q.D) :
    ∃ y : Fin 3 → ℝ, (∀ i, |y i - ![π + q.α, 0, q.c0] i| ≤ ε) ∧ q.downEnergy y < q.A ∧
      (∀ t, 0 ≤ t → |q.dsol y t 2 - q.c0| ≤ q.A) ∧
      Tendsto (q.dsol y) atTop (𝓝 ![q.α, 0, q.c0]) := by
  have hM := q.M_pos; have hω := q.ωc_pos; have hD0 := q.D_nonneg
  obtain ⟨a, hR, hL⟩ := q.exists_arc_stay hP ε
  set x := q.arc ε a with hxdef
  set η := ε / (1 + q.M * q.ωc + q.D)
  have hηε : η ≤ ε := div_le_self hε0.le (by nlinarith [mul_pos hM hω])
  have hη0 : 0 ≤ η := by positivity
  have hclose : ∀ i, |x i - ![π + q.α, 0, q.c0] i| ≤ ε := fun i => by
    fin_cases i
    · show |π + q.α + ε * Real.cos a - (π + q.α)| ≤ ε
      rw [show π + q.α + ε * Real.cos a - (π + q.α) = ε * Real.cos a by ring, abs_mul,
        abs_of_pos hε0]
      nlinarith [Real.abs_cos_le_one a]
    · show |-(η * Real.sin a) - 0| ≤ ε
      rw [sub_zero, abs_neg, abs_mul, abs_of_nonneg hη0]
      nlinarith [Real.abs_sin_le_one a]
    · show |q.c0 + ε * Real.sin a - q.c0| ≤ ε
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hε0]
      nlinarith [Real.abs_sin_le_one a]
  have hx0 : x 0 ∈ Ioo (π + q.α - 2 * π) (π + q.α + 2 * π) := by
    have := abs_le.1 (hclose 0)
    simp only [Matrix.cons_val_zero] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hE := q.downEnergy_arc_lt hP hε0 hε1 a
  have hx1 : |x 1| ≤ q.A / q.D := by
    have := hclose 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero] at this
    linarith
  have hstay := q.stays_in_strip hP hx0 hE hR hL
  have hz := q.abs_filter_le hP hstay
  rcases q.tendsto_rest hP hD hE hx1 hstay with h | h
  · exact ⟨x, hclose, hE, hz, h⟩
  · refine ⟨q.reflect x, fun i => ?_, by rwa [q.downEnergy_reflect hP], fun t ht => ?_, ?_⟩
    · have hr : q.reflect x i - ![π + q.α, 0, q.c0] i = -(x i - ![π + q.α, 0, q.c0] i) := by
        fin_cases i <;> simp [reflect] <;> ring
      rw [hr, abs_neg]; exact hclose i
    · rw [q.dsol_reflect hP x ht, (q.reflect_apply _).2.2,
        show 2 * q.c0 - q.dsol x t 2 - q.c0 = -(q.dsol x t 2 - q.c0) by ring, abs_neg]
      exact hz t ht
    · have hrc : Continuous q.reflect := by unfold reflect; fun_prop
      have hlim := (hrc.tendsto _).comp h
      have hval : q.reflect ![q.α + 2 * π, 0, q.c0] = ![q.α, 0, q.c0] := by
        ext i; fin_cases i <;> simp [reflect] <;> ring
      rw [hval] at hlim
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact (q.dsol_reflect hP x ht).symm

/-! ## The uphill pair read backwards along the selected orbit -/

/-- The uphill field `δ̇ = ω`, `M ω̇ = P_ref − P_f + D ω`, `Ṗ_f = ω_c (P(δ) − P_f)` (the controlled
field with the feedback `σ_P u = 2Dω`, `uphill_field`). -/
def upField (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 1, (q.Pref - x 2 + q.D * x 1) / q.M, q.ωc * (q.c0 + q.A * Real.sin (x 0 - q.α) - x 2)]

@[tmio M, powerlib_domain] theorem uphill_field {σP : ℝ} (hσ : σP ≠ 0) (x : Fin 3 → ℝ) :
    controlField q.sdeDrift (fun _ (_ : Fin 1) => q.setPointColumn σP) x
      ![2 * q.D * x 1 / σP] = q.upField x := by
  have hM := q.M_pos.ne'
  rw [controlField_setPoint]
  ext i; fin_cases i
  · rfl
  · simp [upField]; field_simp; ring
  · rfl

/-- The momentum flip `(δ, ω, P_f) ↦ (δ, −ω, P_f)`. -/
private def flip3 (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![x 0, -x 1, x 2]

/-- **Reversal**: `t ↦ flip(r(T − t))` solves the uphill field on `[0, T)` when `r` is a forward
orbit of `downField`. -/
@[tmio M, powerlib_domain] private theorem hasDerivAt_reverse (y : Fin 3 → ℝ) {T t : ℝ}
    (ht : t < T) :
    HasDerivAt (fun s => flip3 (q.dsol y (T - s))) (q.upField (flip3 (q.dsol y (T - t)))) t := by
  have hT : 0 < T - t := by linarith
  have hs : HasDerivAt (fun s => T - s) (-1) t := by
    simpa using (hasDerivAt_id' t).const_sub T
  have hc : ∀ i : Fin 3, HasDerivAt (fun s => q.dsol y (T - s) i)
      (q.downField (q.dsol y (T - t)) i * -1) t := fun i =>
    (q.dsol_coord_hasDerivAt y i hT).comp t hs
  refine hasDerivAt_pi.2 fun i => ?_
  set r := q.dsol y (T - t)
  fin_cases i
  · convert hc 0 using 1
    · funext s; simp [flip3]
    · show -(r 1) = r 1 * -1
      ring
  · convert (hc 1).neg using 1
    · funext s; simp [flip3]
    · show (q.Pref - r 2 + q.D * -(r 1)) / q.M = -((q.Pref - r 2 - q.D * r 1) / q.M * -1)
      ring
  · convert hc 2 using 1
    · funext s; simp [flip3]
    show q.ωc * (q.c0 + q.A * Real.sin (r 0 - q.α) - r 2) =
      q.ωc * (r 2 - (q.c0 + q.A * Real.sin (r 0 - q.α))) * -1
    ring

/-! ## The speed of the uphill crossing of the band `[π/6, 5π/6]` -/

/-- The speed reached by every uphill crossing of the band (balanced set point):
`w₀ = min(A/(8D), π ω_c/12, √(π A/(48 M)))`. -/
def balancedSpeed : ℝ := min (min (q.A / (8 * q.D)) (π * q.ωc / 12)) √(π * q.A / (48 * q.M))

/-- The gain constant `J = 3 D w₀⁴/(64 A)`: every uphill path from near the stable equilibrium to
near the saddle has `∫ ω̇² ≥ J` (balanced set point). -/
def balancedGain : ℝ := 3 * q.D * q.balancedSpeed ^ 4 / (64 * q.A)

@[tmio M, powerlib_domain] private theorem balancedSpeed_pos (hD : 0 < q.D) :
    0 < q.balancedSpeed := by
  have := q.A_pos; have := q.ωc_pos; have := q.M_pos
  exact lt_min (lt_min (by positivity) (by positivity)) (Real.sqrt_pos.2 (by positivity))

@[tmio M, powerlib_domain] theorem balancedGain_pos (hD : 0 < q.D) : 0 < q.balancedGain := by
  have := q.A_pos; have := q.balancedSpeed_pos hD
  unfold balancedGain; positivity

/-- `sin θ ≥ 1/2` on `[π/6, 5π/6]`. -/
@[tmio T, powerlib_foundation] private theorem sin_ge_half {θ : ℝ} (h1 : π / 6 ≤ θ)
    (h2 : θ ≤ 5 * π / 6) : 1 / 2 ≤ Real.sin θ := by
  have hpi := Real.pi_pos
  rcases le_total θ (π / 2) with h | h
  · have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
    rwa [Real.sin_pi_div_six] at this
  · have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 6) (y := π - θ) (by linarith)
      (by linarith) (by linarith)
    rwa [Real.sin_pi_div_six, Real.sin_pi_sub] at this

@[tmio T, powerlib_foundation] private theorem exp_two_gt_six : 6 < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

/-- **Speed on the band** (`P_ref = c₀`, `D > 0`): an uphill path on `[0, T]` from an angle
`≤ α + π/6` to an angle `≥ α + 5π/6`, with the filter within `A` of `c₀`, reaches the
frequency `|ω| > w₀ = balancedSpeed`. Otherwise the crossing of `[π/6, 5π/6]` takes at least
`(2π/3)/w₀`, while after `2/ω_c` the filter is `≥ c₀ + A/4` there and decelerates the frequency
at the rate `A/(8M)`, which bounds the crossing time by `2/ω_c + 16 M w₀/A`. -/
@[tmio M, powerlib_domain] private theorem exists_speed (hP : q.Pref = q.c0) (hD : 0 < q.D)
    {T : ℝ} (hT0 : 0 ≤ T) {φ : ℝ → Fin 3 → ℝ} (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivAt φ (q.upField (φ t)) t)
    (hz : ∀ t ∈ Icc 0 T, |φ t 2 - q.c0| ≤ q.A)
    (h0 : φ 0 0 - q.α ≤ π / 6) (hT : 5 * π / 6 ≤ φ T 0 - q.α) :
    ∃ t ∈ Icc 0 T, q.balancedSpeed < |φ t 1| := by
  have hM := q.M_pos; have hA := q.A_pos; have hω := q.ωc_pos; have hpi := Real.pi_pos
  set w₀ := q.balancedSpeed with hw₀
  have hw0 : 0 < w₀ := q.balancedSpeed_pos hD
  have hw1 : w₀ ≤ q.A / (8 * q.D) := (min_le_left _ _).trans (min_le_left _ _)
  have hw2 : w₀ ≤ π * q.ωc / 12 := (min_le_left _ _).trans (min_le_right _ _)
  have hw3 : w₀ ^ 2 ≤ π * q.A / (48 * q.M) := by
    have : w₀ ≤ √(π * q.A / (48 * q.M)) := min_le_right _ _
    calc w₀ ^ 2 ≤ √(π * q.A / (48 * q.M)) ^ 2 := pow_le_pow_left₀ hw0.le this 2
      _ = π * q.A / (48 * q.M) := Real.sq_sqrt (by positivity)
  by_contra hcon
  push Not at hcon
  set θ := fun t => φ t 0 - q.α with hθ
  have hθc : ContinuousOn θ (Icc 0 T) :=
    ((continuous_apply 0).comp_continuousOn hc).sub continuousOn_const
  have hcoord : ∀ i : Fin 3, ∀ t ∈ Ico 0 T,
      HasDerivAt (fun s => φ s i) (q.upField (φ t) i) t := fun i t ht =>
    hasDerivAt_pi.1 (hφ t ht) i
  -- the last entry time `t₂` into `θ ≥ 5π/6`
  set S₂ := Icc 0 T ∩ θ ⁻¹' Ici (5 * π / 6) with hS₂
  have hS₂c : IsClosed S₂ := hθc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS₂n : S₂.Nonempty := ⟨T, ⟨hT0, le_rfl⟩, hT⟩
  have hS₂b : BddBelow S₂ := ⟨0, fun t ht => ht.1.1⟩
  set t₂ := sInf S₂
  have ht₂S : t₂ ∈ S₂ := hS₂c.csInf_mem hS₂n hS₂b
  have hbelow₂ : ∀ t ∈ Icc 0 T, t < t₂ → θ t < 5 * π / 6 := fun t ht htt => by
    by_contra h; push Not at h
    exact absurd (csInf_le hS₂b ⟨ht, h⟩) (not_le.2 htt)
  have ht₂0 : 0 < t₂ := by
    rcases ht₂S.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have := ht₂S.2; rw [← h] at this
      have : 5 * π / 6 ≤ θ 0 := this
      simp only [hθ] at this; linarith
  -- the last exit time `t₁ ≤ t₂` from `θ ≤ π/6`
  set S₁ := Icc 0 t₂ ∩ θ ⁻¹' Iic (π / 6) with hS₁
  have hS₁c : IsClosed S₁ :=
    (hθc.mono (Icc_subset_Icc le_rfl ht₂S.1.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  have hS₁n : S₁.Nonempty := ⟨0, ⟨le_rfl, ht₂0.le⟩, h0⟩
  have hS₁b : BddAbove S₁ := ⟨t₂, fun t ht => ht.1.2⟩
  set t₁ := sSup S₁
  have ht₁S : t₁ ∈ S₁ := hS₁c.csSup_mem hS₁n hS₁b
  have habove₁ : ∀ t ∈ Icc 0 t₂, t₁ < t → π / 6 < θ t := fun t ht htt => by
    by_contra h; push Not at h
    exact absurd (le_csSup hS₁b ⟨ht, h⟩) (not_le.2 htt)
  have hθt₁ : θ t₁ ≤ π / 6 := ht₁S.2
  have hθt₂ : 5 * π / 6 ≤ θ t₂ := ht₂S.2
  have ht₁t₂ : t₁ < t₂ := by
    rcases ht₁S.1.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h] at hθt₁; linarith
  have ht₁0 : 0 ≤ t₁ := ht₁S.1.1
  have ht₂T : t₂ ≤ T := ht₂S.1.2
  have hband : ∀ t ∈ Icc t₁ t₂, π / 6 ≤ θ t ∧ θ t ≤ 5 * π / 6 := by
    intro t ht
    rcases ht.1.lt_or_eq with h1 | h1
    · rcases ht.2.lt_or_eq with h2 | h2
      · exact ⟨(habove₁ t ⟨by linarith, ht.2⟩ h1).le,
          (hbelow₂ t ⟨by linarith, by linarith⟩ h2).le⟩
      · rw [h2]
        refine ⟨by linarith [hθt₂], ?_⟩
        -- `θ(t₂) ≤ 5π/6` by continuity from the left
        by_contra hgt; push Not at hgt
        have hct : ContinuousWithinAt θ (Icc 0 T) t₂ := hθc t₂ ht₂S.1
        have hev := hct.eventually (lt_mem_nhds hgt)
        obtain ⟨s, hs1, hs2⟩ : ∃ s ∈ Ioo t₁ t₂, 5 * π / 6 < θ s := by
          have h3 : ∀ᶠ s in 𝓝[<] t₂, s ∈ Icc 0 T := by
            filter_upwards [Ioo_mem_nhdsLT ht₂0] with s hs
            exact ⟨hs.1.le, hs.2.le.trans ht₂T⟩
          have h4 := (nhdsWithin_le_iff.2 h3 |> fun hle => hev.filter_mono hle)
          exact ((h4.and (Ioo_mem_nhdsLT ht₁t₂))).exists.imp fun s hs => ⟨hs.2, hs.1⟩
        exact absurd (hbelow₂ s ⟨by linarith [hs1.1], by linarith [hs1.2]⟩ hs1.2) (not_lt.2 hs2.le)
    · rw [← h1]; refine ⟨?_, by linarith⟩
      -- `θ(t₁) ≥ π/6` by continuity from the right
      by_contra hlt; push Not at hlt
      have hct : ContinuousWithinAt θ (Icc 0 T) t₁ := hθc t₁ ⟨ht₁0, by linarith⟩
      have hev := hct.eventually (gt_mem_nhds hlt)
      obtain ⟨s, hs1, hs2⟩ : ∃ s ∈ Ioo t₁ t₂, θ s < π / 6 := by
        have h3 : ∀ᶠ s in 𝓝[>] t₁, s ∈ Icc 0 T := by
          filter_upwards [Ioo_mem_nhdsGT ht₁t₂] with s hs
          exact ⟨by linarith [hs.1], hs.2.le.trans ht₂T⟩
        have h4 := (nhdsWithin_le_iff.2 h3 |> fun hle => hev.filter_mono hle)
        exact ((h4.and (Ioo_mem_nhdsGT ht₁t₂))).exists.imp fun s hs => ⟨hs.2, hs.1⟩
      exact absurd (habove₁ s ⟨by linarith [hs1.1], hs1.2.le⟩ hs1.1) (not_lt.2 hs2.le)
  -- (i) the crossing takes at least `(2π/3)/w₀`
  have hcross : 2 * π / 3 ≤ w₀ * (t₂ - t₁) := by
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope θ (fun t => φ t 1) ht₁t₂
      (hθc.mono (Icc_subset_Icc ht₁0 ht₂T))
      (fun t ht => (hcoord 0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩).sub_const q.α)
    have hξw := (abs_le.1 (hcon ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)).2
    rw [hslope, div_le_iff₀ (by linarith)] at hξw
    linarith [hθt₁, hband t₂ ⟨ht₁t₂.le, le_rfl⟩, (hband t₁ ⟨le_rfl, ht₁t₂.le⟩).1]
  -- (ii) the filter is above `c₀ + A/4` after `2/ω_c` on the band
  have hzA : ∀ t ∈ Icc t₁ t₂, t₁ + 2 / q.ωc ≤ t → q.A / 4 ≤ φ t 2 - q.c0 := by
    have hanti : AntitoneOn (fun t => (q.A / 2 - (φ t 2 - q.c0)) *
        Real.exp (q.ωc * (t - t₁))) (Icc t₁ t₂) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (f' := fun t => q.ωc * q.A * (1 / 2 - Real.sin (φ t 0 - q.α)) *
          Real.exp (q.ωc * (t - t₁)))
        ((continuousOn_const.sub (((continuous_apply 2).comp_continuousOn
          (hc.mono (Icc_subset_Icc ht₁0 ht₂T))).sub continuousOn_const)).mul
          (by fun_prop : Continuous fun t => Real.exp (q.ωc * (t - t₁))).continuousOn)
        (fun t ht => ?_) (fun t ht => ?_)
      · rw [interior_Icc] at ht
        have hE : HasDerivAt (fun t => Real.exp (q.ωc * (t - t₁)))
            (Real.exp (q.ωc * (t - t₁)) * (q.ωc * 1)) t :=
          (((hasDerivAt_id' t).sub_const t₁).const_mul q.ωc).exp
        have h2 := hcoord 2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
        refine (((h2.sub_const q.c0).const_sub (q.A / 2)).mul hE).hasDerivWithinAt.congr_deriv ?_
        simp only [upField, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        ring
      · rw [interior_Icc] at ht
        have := sin_ge_half (hband t ⟨ht.1.le, ht.2.le⟩).1 (hband t ⟨ht.1.le, ht.2.le⟩).2
        have h3 : 1 / 2 - Real.sin (φ t 0 - q.α) ≤ 0 := by simp only [hθ] at this; linarith
        have : 0 ≤ q.ωc * q.A := by positivity
        have := mul_nonpos_of_nonneg_of_nonpos this h3
        exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le
    intro t ht htt
    have h1 := hanti ⟨le_rfl, ht₁t₂.le⟩ ht ht.1
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at h1
    have hz1 := (abs_le.1 (hz t₁ ⟨ht₁0, by linarith⟩)).1
    have he : Real.exp (q.ωc * (t - t₁)) ≥ Real.exp 2 := Real.exp_le_exp.2 (by
      have : 2 / q.ωc ≤ t - t₁ := by linarith
      rw [div_le_iff₀ hω] at this; linarith)
    have h6 := exp_two_gt_six
    by_contra hlt; push Not at hlt
    have hpos : 0 < q.A / 2 - (φ t 2 - q.c0) := by linarith
    have : q.A / 4 * 6 < (q.A / 2 - (φ t 2 - q.c0)) * Real.exp (q.ωc * (t - t₁)) := by
      have : q.A / 4 < q.A / 2 - (φ t 2 - q.c0) := by linarith
      nlinarith
    linarith
  -- (iii) the frequency decreases at the rate `A/(8M)` there: the crossing is short
  have hshort : t₂ - t₁ ≤ 2 / q.ωc + 16 * q.M * w₀ / q.A := by
    by_contra hlong; push Not at hlong
    set t₃ := t₁ + 2 / q.ωc
    have ht₃ : t₃ < t₂ := by
      have : 0 ≤ 16 * q.M * w₀ / q.A := by positivity
      simp only [t₃]; linarith
    have ht₁₃ : t₁ ≤ t₃ := by have : 0 < 2 / q.ωc := by positivity
                              simp only [t₃]; linarith
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => φ t 1)
      (fun t => q.upField (φ t) 1) ht₃
      ((continuous_apply 1).comp_continuousOn (hc.mono (Icc_subset_Icc (by linarith) ht₂T)))
      (fun t ht => hcoord 1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hzξ := hzA ξ ⟨by linarith [hξ.1], hξ.2.le⟩ hξ.1.le
    have hwξ := (abs_le.1 (hcon ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)).2
    have hacc : q.upField (φ ξ) 1 ≤ -(q.A / (8 * q.M)) := by
      simp only [upField, Matrix.cons_val_one, Matrix.cons_val_zero, hP]
      rw [div_le_iff₀ hM]
      have : q.D * φ ξ 1 ≤ q.A / 8 := by
        calc q.D * φ ξ 1 ≤ q.D * w₀ := mul_le_mul_of_nonneg_left hwξ hD.le
          _ ≤ q.D * (q.A / (8 * q.D)) := mul_le_mul_of_nonneg_left hw1 hD.le
          _ = q.A / 8 := by field_simp
      have : -(q.A / (8 * q.M)) * q.M = -(q.A / 8) := by field_simp
      linarith
    rw [hslope, div_le_iff₀ (by linarith)] at hacc
    have hb2 := (abs_le.1 (hcon t₂ ⟨by linarith, ht₂T⟩)).1
    have hb3 := (abs_le.1 (hcon t₃ ⟨by linarith, by linarith⟩)).2
    have : q.A / (8 * q.M) * (t₂ - t₃) ≤ 2 * w₀ := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    have : t₂ - t₃ ≤ 16 * q.M * w₀ / q.A := by
      rw [le_div_iff₀ hA]; nlinarith
    simp only [t₃] at this
    linarith
  -- (iv) the two bounds contradict each other
  have h4 : w₀ * (2 / q.ωc) ≤ π / 6 := by
    rw [mul_div_assoc', div_le_iff₀ hω]; nlinarith
  have h5 : w₀ * (16 * q.M * w₀ / q.A) ≤ π / 3 := by
    rw [show w₀ * (16 * q.M * w₀ / q.A) = 16 * q.M * w₀ ^ 2 / q.A by ring,
      div_le_iff₀ hA]
    rw [le_div_iff₀ (by positivity)] at hw3
    nlinarith
  have := mul_le_mul_of_nonneg_left hshort hw0.le
  nlinarith

/-- **The gain of an uphill crossing** (`P_ref = c₀`, `D > 0`): an uphill path as in
`exists_speed` that starts with `ω(0)² ≤ w₀²/4` and has `∫ ω² ≤ N` satisfies
`∫₀ᵀ ω̇² ≥ 9 w₀⁴/(64 N)` (`Dynamics.abs_sq_sub_sq_le` on `[0, t*]`, `|ω(t*)| > w₀`). -/
@[tmio M, powerlib_domain] private theorem gain_le (hP : q.Pref = q.c0) (hD : 0 < q.D)
    {T : ℝ} (hT0 : 0 ≤ T) {φ : ℝ → Fin 3 → ℝ} (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivAt φ (q.upField (φ t)) t)
    (hz : ∀ t ∈ Icc 0 T, |φ t 2 - q.c0| ≤ q.A)
    (h0 : φ 0 0 - q.α ≤ π / 6) (hT : 5 * π / 6 ≤ φ T 0 - q.α)
    (hw0 : φ 0 1 ^ 2 ≤ q.balancedSpeed ^ 2 / 4) {N : ℝ} (hN0 : 0 < N)
    (hN : ∫ t in (0 : ℝ)..T, φ t 1 ^ 2 ≤ N) :
    9 * q.balancedSpeed ^ 4 / (64 * N) ≤ ∫ t in (0 : ℝ)..T, q.uphillAcc (φ t) ^ 2 := by
  obtain ⟨t, ht, hspeed⟩ := q.exists_speed hP hD hT0 hc hφ hz h0 hT
  set w₀ := q.balancedSpeed
  have hw := q.balancedSpeed_pos hD
  have hc1 : ContinuousOn (fun s => φ s 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hc
  have hca : ContinuousOn (fun s => q.uphillAcc (φ s)) (Icc 0 T) := by
    have h2 : ContinuousOn (fun s => φ s 2) (Icc 0 T) := (continuous_apply 2).comp_continuousOn hc
    simp only [uphillAcc]
    exact ((continuousOn_const.sub h2).add (continuousOn_const.mul hc1)).div_const _
  set l := 3 * w₀ ^ 2 / (8 * N) with hl
  have hl0 : 0 < l := by positivity
  have hint := Dynamics.abs_sq_sub_sq_le ht.1 hl0 (x := fun s => φ s 1)
    (x' := fun s => q.uphillAcc (φ s))
    (fun s hs => (hasDerivAt_pi.1 (hφ s ⟨hs.1, hs.2.trans_le ht.2⟩) 1).hasDerivWithinAt)
    (hc1.mono (Icc_subset_Icc le_rfl ht.2)) (hca.mono (Icc_subset_Icc le_rfl ht.2))
  have hmono : ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 T) →
      ∫ s in (0 : ℝ)..t, f s ^ 2 ≤ ∫ s in (0 : ℝ)..T, f s ^ 2 := fun f hf =>
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun s => sq_nonneg _)
      ((hf.pow 2).intervalIntegrable_of_Icc hT0)
  have h1 := hmono _ hc1
  have h2 := hmono _ hca
  set I := ∫ s in (0 : ℝ)..T, q.uphillAcc (φ s) ^ 2
  have hsq : w₀ ^ 2 < φ t 1 ^ 2 := by
    have := abs_nonneg (φ t 1)
    rw [← sq_abs (φ t 1)]
    nlinarith
  have habs := (abs_le.1 hint).2
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hT0 fun s _ => sq_nonneg _
  have key : 3 * w₀ ^ 2 / 4 ≤ l * N + I / l := by
    have : l * (∫ s in (0 : ℝ)..t, φ s 1 ^ 2) ≤ l * N :=
      mul_le_mul_of_nonneg_left (h1.trans hN) hl0.le
    have : (∫ s in (0 : ℝ)..t, q.uphillAcc (φ s) ^ 2) / l ≤ I / l :=
      div_le_div_of_nonneg_right h2 hl0.le
    linarith
  have hlN : l * N = 3 * w₀ ^ 2 / 8 := by rw [hl]; field_simp
  rw [hlN] at key
  have : 3 * w₀ ^ 2 / 8 * l ≤ I := by
    have h3 : 3 * w₀ ^ 2 / 8 ≤ I / l := by linarith
    rwa [le_div_iff₀ hl0] at h3
  calc 9 * w₀ ^ 4 / (64 * N) = 3 * w₀ ^ 2 / 8 * l := by rw [hl]; field_simp; ring
    _ ≤ I := this

/-! ## Local controllability at a rest point -/

/-- Cubic Hermite angle on `[0, 1]` from `(a₀, a₁)` to `(b₀, b₁)` (angle, frequency). -/
private def herm (a b : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  a 0 + (b 0 - a 0) * (3 * t ^ 2 - 2 * t ^ 3) + a 1 * (t - 2 * t ^ 2 + t ^ 3) +
    b 1 * (t ^ 3 - t ^ 2)

private def hermVel (a b : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (b 0 - a 0) * (6 * t - 6 * t ^ 2) + a 1 * (1 - 4 * t + 3 * t ^ 2) + b 1 * (3 * t ^ 2 - 2 * t)

private def hermAcc (a b : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (b 0 - a 0) * (6 - 12 * t) + a 1 * (-4 + 6 * t) + b 1 * (6 * t - 2)

@[tmio T, powerlib_foundation] private theorem hasDerivAt_herm (a b : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (herm a b) (hermVel a b t) t := by
  have h1 := hasDerivAt_id' t
  have h2 := hasDerivAt_pow 2 t
  have h3 := hasDerivAt_pow 3 t
  have h := ((((h2.const_mul 3).sub (h3.const_mul 2)).const_mul (b 0 - a 0)).const_add
    (a 0)).add ((((h1.sub (h2.const_mul 2)).add h3).const_mul (a 1)).add
      ((h3.sub h2).const_mul (b 1)))
  convert h using 1
  · funext s; simp only [herm, Pi.add_apply, Pi.sub_apply]; ring
  · simp only [hermVel]; push_cast; ring

@[tmio T, powerlib_foundation] private theorem hasDerivAt_hermVel (a b : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (hermVel a b) (hermAcc a b t) t := by
  have h1 := hasDerivAt_id' t
  have h2 := hasDerivAt_pow 2 t
  have h := (((h1.const_mul 6).sub (h2.const_mul 6)).const_mul (b 0 - a 0)).add
    ((((h1.const_mul 4).const_sub 1).add (h2.const_mul 3)).const_mul (a 1)) |>.add
      (((h2.const_mul 3).sub (h1.const_mul 2)).const_mul (b 1))
  convert h using 1
  · funext s; simp only [hermVel, Pi.add_apply, Pi.sub_apply]
  · simp only [hermAcc]; push_cast; ring

/-- Bounds of the Hermite profile on `[0, 1]` when the end states are within `ρ` of
`(δ_r, 0)`. -/
@[tmio T, powerlib_foundation] private theorem herm_bounds {a b : Fin 3 → ℝ} {δr ρ t : ℝ}
    (ha0 : |a 0 - δr| ≤ ρ) (hb0 : |b 0 - δr| ≤ ρ) (ha1 : |a 1| ≤ ρ) (hb1 : |b 1| ≤ ρ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |herm a b t - δr| ≤ 5 * ρ ∧ |hermVel a b t| ≤ 5 * ρ ∧ |hermAcc a b t| ≤ 20 * ρ := by
  obtain ⟨t0, t1⟩ := ht
  have hba : |b 0 - a 0| ≤ 2 * ρ := by
    calc |b 0 - a 0| = |(b 0 - δr) - (a 0 - δr)| := by ring_nf
      _ ≤ |b 0 - δr| + |a 0 - δr| := abs_sub _ _
      _ ≤ 2 * ρ := by linarith
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans ha1
  have p1 : |3 * t ^ 2 - 2 * t ^ 3| ≤ 1 := by
    rw [abs_le]; constructor
    · nlinarith [mul_nonneg t0 t0, mul_nonneg (mul_nonneg t0 t0) (sub_nonneg.2 t1)]
    · nlinarith [mul_nonneg (sq_nonneg (1 - t)) (by linarith : (0 : ℝ) ≤ 1 + 2 * t)]
  have p2 : |t - 2 * t ^ 2 + t ^ 3| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg t0 (sq_nonneg (1 - t)),
      mul_nonneg t0 (sub_nonneg.2 t1)]
  have p3 : |t ^ 3 - t ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg (mul_nonneg t0 t0) (sub_nonneg.2 t1),
      mul_nonneg t0 t0]
  have q1 : |6 * t - 6 * t ^ 2| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t - 1 / 2), mul_nonneg t0 (sub_nonneg.2 t1)]
  have q2 : |1 - 4 * t + 3 * t ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t - 2 / 3), mul_nonneg t0 (sub_nonneg.2 t1)]
  have q3 : |3 * t ^ 2 - 2 * t| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t - 1 / 3), mul_nonneg t0 (sub_nonneg.2 t1)]
  have r1 : |6 - 12 * t| ≤ 6 := by rw [abs_le]; constructor <;> linarith
  have r2 : |-4 + 6 * t| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have r3 : |6 * t - 2| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · have e : herm a b t - δr = (a 0 - δr) + (b 0 - a 0) * (3 * t ^ 2 - 2 * t ^ 3) +
        a 1 * (t - 2 * t ^ 2 + t ^ 3) + b 1 * (t ^ 3 - t ^ 2) := by simp only [herm]; ring
    rw [e]
    calc _ ≤ |a 0 - δr| + |b 0 - a 0| * |3 * t ^ 2 - 2 * t ^ 3| +
          |a 1| * |t - 2 * t ^ 2 + t ^ 3| + |b 1| * |t ^ 3 - t ^ 2| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul]
          refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl; rw [abs_mul]
          refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl; rw [abs_mul]
      _ ≤ ρ + 2 * ρ * 1 + ρ * 1 + ρ * 1 := by gcongr
      _ = 5 * ρ := by ring
  · simp only [hermVel]
    calc _ ≤ |b 0 - a 0| * |6 * t - 6 * t ^ 2| + |a 1| * |1 - 4 * t + 3 * t ^ 2| +
          |b 1| * |3 * t ^ 2 - 2 * t| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul]
          refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl; rw [abs_mul, abs_mul]
      _ ≤ 2 * ρ * (3 / 2) + ρ * 1 + ρ * 1 := by gcongr
      _ ≤ 5 * ρ := by linarith
  · simp only [hermAcc]
    calc _ ≤ |b 0 - a 0| * |6 - 12 * t| + |a 1| * |-4 + 6 * t| + |b 1| * |6 * t - 2| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul]
          refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl; rw [abs_mul, abs_mul]
      _ ≤ 2 * ρ * 6 + ρ * 4 + ρ * 4 := by gcongr
      _ = 20 * ρ := by ring

/-- `|sin(θ + x) − sin θ − x cos θ| ≤ x²`. -/
@[tmio T, powerlib_foundation] private theorem sin_taylor (θ x : ℝ) :
    |Real.sin (θ + x) - Real.sin θ - x * Real.cos θ| ≤ x ^ 2 := by
  have hd : ∀ s ∈ uIcc 0 x, HasDerivWithinAt (fun s => Real.sin (θ + s) - s * Real.cos θ)
      (Real.cos (θ + s) - Real.cos θ) (uIcc 0 x) s := fun s _ => by
    have := (((hasDerivAt_id' s).const_add θ).sin.sub ((hasDerivAt_id' s).mul_const
      (Real.cos θ))).hasDerivWithinAt (s := uIcc 0 x)
    convert this using 1; ring
  have hb : ∀ s ∈ uIcc 0 x, ‖Real.cos (θ + s) - Real.cos θ‖ ≤ |x| := fun s hs => by
    rw [Real.norm_eq_abs]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [add_sub_cancel_left]
    rcases le_total 0 x with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg hs.1, abs_of_nonneg h]; exact hs.2
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos hs.2, abs_of_nonpos h]; linarith [hs.1]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_uIcc 0 x)
    left_mem_uIcc right_mem_uIcc
  simp only [add_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  rw [show Real.sin (θ + x) - Real.sin θ - x * Real.cos θ =
    Real.sin (θ + x) - x * Real.cos θ - Real.sin θ by ring]
  calc _ ≤ |x| * |x| := this
    _ = x ^ 2 := by rw [← sq, sq_abs]

/-- The power signal along the glue profile `herm a b + l · endBump`. -/
private def gsig (a b : Fin 3 → ℝ) (l s : ℝ) : ℝ :=
  q.c0 + q.A * Real.sin (herm a b s + l * Dynamics.endBump s - q.α)

@[tmio M, powerlib_domain] private theorem continuous_gsig (a b : Fin 3 → ℝ) (l : ℝ) :
    Continuous (q.gsig a b l) := by
  unfold gsig herm Dynamics.endBump; fun_prop

/-- The glue profile stays within `(5 + K) ρ` of `δ_r` for `|l| ≤ K ρ`. -/
@[tmio T, powerlib_foundation] private theorem glue_angle_le {a b : Fin 3 → ℝ} {δr ρ K l t : ℝ}
    (ha0 : |a 0 - δr| ≤ ρ) (hb0 : |b 0 - δr| ≤ ρ) (ha1 : |a 1| ≤ ρ) (hb1 : |b 1| ≤ ρ)
    (hl : |l| ≤ K * ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |herm a b t + l * Dynamics.endBump t - δr| ≤ (5 + K) * ρ := by
  have h1 := (herm_bounds ha0 hb0 ha1 hb1 ht).1
  have h2 := Dynamics.endBump_bounds ht
  have h3 : |l * Dynamics.endBump t| ≤ K * ρ := by
    rw [abs_mul, abs_of_nonneg h2.1]
    calc |l| * Dynamics.endBump t ≤ (K * ρ) * 1 :=
          mul_le_mul hl h2.2.1 h2.1 ((abs_nonneg l).trans hl)
      _ = K * ρ := mul_one _
  calc |herm a b t + l * Dynamics.endBump t - δr| =
        |(herm a b t - δr) + l * Dynamics.endBump t| := by ring_nf
    _ ≤ |herm a b t - δr| + |l * Dynamics.endBump t| := abs_add_le _ _
    _ ≤ 5 * ρ + K * ρ := by linarith
    _ = (5 + K) * ρ := by ring

/-- **The filter at the end of the glue**: for `|l| ≤ K ρ`, the end value is within
`m + ρ` (`m = 5Aρ + A((5 + K)ρ)²`) of `P_ref + κ l z_b(1)`, `κ = A cos(δ_r − α)`,
`z_b(1) = lagFilter ω_c 0 endBump 1` (comparison of the filter with affine signals). -/
@[tmio M, powerlib_domain] private theorem glue_filter_near {δr : ℝ}
    (hr : q.c0 + q.A * Real.sin (δr - q.α) = q.Pref) {a b : Fin 3 → ℝ} {ρ K l : ℝ}
    (ha0 : |a 0 - δr| ≤ ρ) (hb0 : |b 0 - δr| ≤ ρ) (ha1 : |a 1| ≤ ρ) (hb1 : |b 1| ≤ ρ)
    (ha2 : |a 2 - q.Pref| ≤ ρ) (hl : |l| ≤ K * ρ) :
    |Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) 1 - q.Pref -
        q.A * Real.cos (δr - q.α) * l * Dynamics.lagFilter q.ωc 0 Dynamics.endBump 1| ≤
      5 * q.A * ρ + q.A * ((5 + K) * ρ) ^ 2 + ρ := by
  have hA := q.A_pos; have hω := q.ωc_pos
  set κ := q.A * Real.cos (δr - q.α) with hκ
  set m := 5 * q.A * ρ + q.A * ((5 + K) * ρ) ^ 2 with hm
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans ha1
  have hm0 : 0 ≤ m := by positivity
  have hβc : Continuous Dynamics.endBump := by unfold Dynamics.endBump; fun_prop
  -- pointwise bounds of the signal
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, |q.gsig a b l s - (q.Pref + κ * l * Dynamics.endBump s)| ≤ m := by
    intro s hs
    set x := herm a b s + l * Dynamics.endBump s - δr
    have hx := glue_angle_le ha0 hb0 ha1 hb1 hl hs
    have ht := sin_taylor (δr - q.α) x
    have hh := (herm_bounds ha0 hb0 ha1 hb1 hs).1
    have e : q.gsig a b l s - (q.Pref + κ * l * Dynamics.endBump s) =
        q.A * (Real.sin (δr - q.α + x) - Real.sin (δr - q.α) - x * Real.cos (δr - q.α)) +
          κ * (herm a b s - δr) := by
      simp only [gsig, hκ, x]
      rw [← hr, show δr - q.α + (herm a b s + l * Dynamics.endBump s - δr) =
        herm a b s + l * Dynamics.endBump s - q.α by ring]
      ring
    rw [e]
    have h1 : |q.A * (Real.sin (δr - q.α + x) - Real.sin (δr - q.α) - x * Real.cos (δr - q.α))|
        ≤ q.A * ((5 + K) * ρ) ^ 2 := by
      rw [abs_mul, abs_of_pos hA]
      refine mul_le_mul_of_nonneg_left (ht.trans ?_) hA.le
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have h2 : |κ * (herm a b s - δr)| ≤ 5 * q.A * ρ := by
      rw [abs_mul, hκ, abs_mul, abs_of_pos hA]
      have := Real.abs_cos_le_one (δr - q.α)
      calc q.A * |Real.cos (δr - q.α)| * |herm a b s - δr| ≤ q.A * 1 * (5 * ρ) := by gcongr
        _ = 5 * q.A * ρ := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ q.A * ((5 + K) * ρ) ^ 2 + 5 * q.A * ρ := add_le_add h1 h2
      _ = m := by rw [hm]; ring
  have hlow := Dynamics.lagFilter_mono (z₀ := a 2) hω.le zero_le_one
    (h := fun s => (q.Pref - m) + κ * l * Dynamics.endBump s)
    (continuous_const.add (hβc.const_mul (κ * l))) (q.continuous_gsig a b l)
    (fun s hs => by
      have := (abs_le.1 (hpt s hs)).1
      show q.Pref - m + κ * l * Dynamics.endBump s ≤ q.gsig a b l s; linarith)
  have hupp := Dynamics.lagFilter_mono (z₀ := a 2) hω.le zero_le_one
    (k := fun s => (q.Pref + m) + κ * l * Dynamics.endBump s)
    (q.continuous_gsig a b l) (continuous_const.add (hβc.const_mul (κ * l)))
    (fun s hs => by
      have := (abs_le.1 (hpt s hs)).2
      show q.gsig a b l s ≤ q.Pref + m + κ * l * Dynamics.endBump s; linarith)
  rw [Dynamics.lagFilter_const_add_mul _ _ _ _ hβc, Dynamics.lagFilter_const] at hlow hupp
  have he1 : Real.exp (-(q.ωc * 1)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 : 0 < Real.exp (-(q.ωc * 1)) := Real.exp_pos _
  have ha2' := abs_le.1 ha2
  have hlo : -ρ ≤ (a 2 - (q.Pref - m)) * Real.exp (-(q.ωc * 1)) := by
    have : -ρ ≤ (a 2 - q.Pref) * Real.exp (-(q.ωc * 1)) := by nlinarith
    nlinarith
  have hhi : (a 2 - (q.Pref + m)) * Real.exp (-(q.ωc * 1)) ≤ ρ := by
    have : (a 2 - q.Pref) * Real.exp (-(q.ωc * 1)) ≤ ρ := by nlinarith
    nlinarith
  rw [abs_le]; constructor <;> linarith

/-- **The bump amplitude** (intermediate value theorem): with `K = (5A + 4)/(|κ| ω_c e^{−ω_c}/30)`
and `A((5 + K)ρ)² ≤ ρ`, some `|l| ≤ Kρ` makes the filter arrive exactly at `b₂`. -/
@[tmio M, powerlib_domain] private theorem glue_amplitude {δr : ℝ}
    (hr : q.c0 + q.A * Real.sin (δr - q.α) = q.Pref) (hκ : Real.cos (δr - q.α) ≠ 0)
    {a b : Fin 3 → ℝ} {ρ K : ℝ} (hρ : 0 < ρ)
    (hK : K = (5 * q.A + 4) / (|q.A * Real.cos (δr - q.α)| * (q.ωc * Real.exp (-q.ωc) / 30)))
    (hρK : q.A * ((5 + K) * ρ) ^ 2 ≤ ρ)
    (ha0 : |a 0 - δr| ≤ ρ) (hb0 : |b 0 - δr| ≤ ρ) (ha1 : |a 1| ≤ ρ) (hb1 : |b 1| ≤ ρ)
    (ha2 : |a 2 - q.Pref| ≤ ρ) (hb2 : |b 2 - q.Pref| ≤ ρ) :
    ∃ l, |l| ≤ K * ρ ∧ Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) 1 = b 2 := by
  have hA := q.A_pos; have hω := q.ωc_pos
  set κ := q.A * Real.cos (δr - q.α) with hκdef
  have hκ0 : 0 < |κ| := abs_pos.2 (mul_ne_zero hA.ne' hκ)
  set Iβ := q.ωc * Real.exp (-q.ωc) / 30 with hIβ
  have hIβ0 : 0 < Iβ := by positivity
  have hK0 : 0 < K := by rw [hK]; positivity
  set L := K * ρ with hL
  have hL0 : 0 < L := by positivity
  set Fβ := Dynamics.lagFilter q.ωc 0 Dynamics.endBump 1
  have hFβ : Iβ ≤ Fβ := Dynamics.lagFilter_endBump_ge hω.le
  set g := fun l => Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) 1 with hg
  have hgc : Continuous g := by
    have hint : Continuous fun l => ∫ s in (0 : ℝ)..1, Real.exp (q.ωc * s) * q.gsig a b l s := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      unfold Function.uncurry gsig herm Dynamics.endBump
      fun_prop
    simp only [hg, Dynamics.lagFilter]
    fun_prop
  set ν := κ / |κ| with hν
  have hνκ : ν * κ = |κ| := by
    rw [hν, div_mul_eq_mul_div, ← sq, ← sq_abs, sq, mul_div_assoc, div_self hκ0.ne', mul_one]
  have hν1 : |ν| = 1 := by rw [hν, abs_div, abs_abs, div_self hκ0.ne']
  have hνL : |ν * L| = L := by rw [abs_mul, hν1, one_mul, abs_of_pos hL0]
  have hmL : |-(ν * L)| = L := by rw [abs_neg, hνL]
  have hkey : |κ| * L * Iβ = (5 * q.A + 4) * ρ := by
    rw [hL, hK]; field_simp
  have hgain : (5 * q.A + 4) * ρ ≤ |κ| * L * Fβ := by
    rw [← hkey]; exact mul_le_mul_of_nonneg_left hFβ (by positivity)
  have hb2' := abs_le.1 hb2
  have hup : b 2 < g (ν * L) := by
    have h := abs_le.1 (q.glue_filter_near hr ha0 hb0 ha1 hb1 ha2 hνL.le)
    have e : κ * (ν * L) * Fβ = |κ| * L * Fβ := by rw [← hνκ]; ring
    simp only [hg]
    rw [← hκdef, e] at h
    linarith [h.1]
  have hdown : g (-(ν * L)) < b 2 := by
    have h := abs_le.1 (q.glue_filter_near hr ha0 hb0 ha1 hb1 ha2 hmL.le)
    have e : κ * (-(ν * L)) * Fβ = -(|κ| * L * Fβ) := by rw [← hνκ]; ring
    simp only [hg]
    rw [← hκdef, e] at h
    linarith [h.2]
  obtain ⟨l, hl, hgl⟩ := intermediate_value_uIcc (a := -(ν * L)) (b := ν * L)
    hgc.continuousOn ⟨(min_le_left _ _).trans hdown.le, hup.le.trans (le_max_right _ _)⟩
  refine ⟨l, ?_, hgl⟩
  rcases le_total (-(ν * L)) (ν * L) with h | h
  · rw [uIcc_of_le h] at hl
    exact abs_le.2 ⟨by linarith [hl.1, le_abs_self (ν * L), hνL],
      by linarith [hl.2, le_abs_self (ν * L), hνL]⟩
  · rw [uIcc_of_ge h] at hl
    exact abs_le.2 ⟨by linarith [hl.1, neg_abs_le (ν * L), hνL],
      by linarith [hl.2, neg_abs_le (ν * L), hνL]⟩

/-- The control of the glue pair is `O(ρ)`: `|M δ̈ + (z − P_ref) + D δ̇| ≤ C_u ρ` on `[0, 1]`. -/
@[tmio M, powerlib_domain] private theorem glue_control_le {δr : ℝ}
    (hr : q.c0 + q.A * Real.sin (δr - q.α) = q.Pref) {a b : Fin 3 → ℝ} {ρ K l t : ℝ}
    (hK : 0 ≤ K) (ha0 : |a 0 - δr| ≤ ρ) (hb0 : |b 0 - δr| ≤ ρ) (ha1 : |a 1| ≤ ρ)
    (hb1 : |b 1| ≤ ρ) (ha2 : |a 2 - q.Pref| ≤ ρ) (hl : |l| ≤ K * ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |q.M * (hermAcc a b t + l * Dynamics.endBumpAcc t) +
        (Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) t - q.Pref) +
        q.D * (hermVel a b t + l * Dynamics.endBumpVel t)| ≤
      (q.M * (20 + 2 * K) + (1 + q.ωc * (q.A * (5 + K))) + q.D * (5 + K)) * ρ := by
  have hM := q.M_pos; have hA := q.A_pos; have hω := q.ωc_pos; have hD := q.D_nonneg
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans ha1
  have hh := herm_bounds ha0 hb0 ha1 hb1 ht
  have he := Dynamics.endBump_bounds ht
  have hl0 : 0 ≤ |l| := abs_nonneg l
  have hacc : |hermAcc a b t + l * Dynamics.endBumpAcc t| ≤ (20 + 2 * K) * ρ := by
    have : |l * Dynamics.endBumpAcc t| ≤ 2 * (K * ρ) := by
      rw [abs_mul]
      calc |l| * |Dynamics.endBumpAcc t| ≤ (K * ρ) * 2 := mul_le_mul hl he.2.2.2
            (abs_nonneg _) (hl0.trans hl)
        _ = 2 * (K * ρ) := by ring
    calc _ ≤ |hermAcc a b t| + |l * Dynamics.endBumpAcc t| := abs_add_le _ _
      _ ≤ 20 * ρ + 2 * (K * ρ) := add_le_add hh.2.2 this
      _ = (20 + 2 * K) * ρ := by ring
  have hvel : |hermVel a b t + l * Dynamics.endBumpVel t| ≤ (5 + K) * ρ := by
    have : |l * Dynamics.endBumpVel t| ≤ K * ρ := by
      rw [abs_mul]
      calc |l| * |Dynamics.endBumpVel t| ≤ (K * ρ) * 1 := mul_le_mul hl he.2.2.1
            (abs_nonneg _) (hl0.trans hl)
        _ = K * ρ := by ring
    calc _ ≤ |hermVel a b t| + |l * Dynamics.endBumpVel t| := abs_add_le _ _
      _ ≤ 5 * ρ + K * ρ := add_le_add hh.2.1 this
      _ = (5 + K) * ρ := by ring
  have hB : ∀ s ∈ Icc (0 : ℝ) t, |q.gsig a b l s - q.Pref| ≤ q.A * ((5 + K) * ρ) := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hx := glue_angle_le ha0 hb0 ha1 hb1 hl hs'
    rw [← hr]
    simp only [gsig]
    rw [show q.c0 + q.A * Real.sin (herm a b s + l * Dynamics.endBump s - q.α) -
      (q.c0 + q.A * Real.sin (δr - q.α)) = q.A * (Real.sin (herm a b s +
        l * Dynamics.endBump s - q.α) - Real.sin (δr - q.α)) by ring, abs_mul, abs_of_pos hA]
    refine mul_le_mul_of_nonneg_left ((Real.abs_sin_sub_sin_le _ _).trans ?_) hA.le
    rw [show herm a b s + l * Dynamics.endBump s - q.α - (δr - q.α) =
      herm a b s + l * Dynamics.endBump s - δr by ring]
    exact hx
  have hF := Dynamics.abs_lagFilter_sub_const_le (z₀ := a 2) hω.le ht.1
    (q.continuous_gsig a b l) hB
  have hF' : |Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) t - q.Pref| ≤
      ρ + q.ωc * (q.A * (5 + K)) * ρ := by
    have : q.ωc * t * (q.A * ((5 + K) * ρ)) ≤ q.ωc * (q.A * (5 + K)) * ρ := by
      have h0 : 0 ≤ q.ωc * (q.A * ((5 + K) * ρ)) := by positivity
      have : q.ωc * t * (q.A * ((5 + K) * ρ)) = t * (q.ωc * (q.A * ((5 + K) * ρ))) := by ring
      rw [this]
      calc t * (q.ωc * (q.A * ((5 + K) * ρ))) ≤ 1 * (q.ωc * (q.A * ((5 + K) * ρ))) :=
            mul_le_mul_of_nonneg_right ht.2 h0
        _ = q.ωc * (q.A * (5 + K)) * ρ := by ring
    linarith
  calc _ ≤ |q.M * (hermAcc a b t + l * Dynamics.endBumpAcc t) +
        (Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) t - q.Pref)| +
        |q.D * (hermVel a b t + l * Dynamics.endBumpVel t)| := abs_add_le _ _
    _ ≤ (q.M * |hermAcc a b t + l * Dynamics.endBumpAcc t| +
        |Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) t - q.Pref|) +
        q.D * |hermVel a b t + l * Dynamics.endBumpVel t| := by
        gcongr
        · exact (abs_add_le _ _).trans (by rw [abs_mul, abs_of_pos hM])
        · rw [abs_mul, abs_of_nonneg hD]
    _ ≤ (q.M * ((20 + 2 * K) * ρ) + (ρ + q.ωc * (q.A * (5 + K)) * ρ)) +
        q.D * ((5 + K) * ρ) := by gcongr
    _ = _ := by ring

/-- **The glue pair**: for `|l| ≤ K ρ` the profile `herm a b + l · endBump` with the filter driven
by its power is an admissible pair on `[0, 1]` from `a` to `(b₀, b₁, z(1))` of action
`≤ (C_u²/(2σ_P²)) ρ²`. -/
@[tmio M, powerlib_domain] private theorem glue_pair {σP : ℝ} (hσ : σP ≠ 0) {δr : ℝ}
    (hr : q.c0 + q.A * Real.sin (δr - q.α) = q.Pref) {a b : Fin 3 → ℝ} {ρ K l : ℝ}
    (hK : 0 ≤ K) (ha0 : |a 0 - δr| ≤ ρ) (hb0 : |b 0 - δr| ≤ ρ) (ha1 : |a 1| ≤ ρ)
    (hb1 : |b 1| ≤ ρ) (ha2 : |a 2 - q.Pref| ≤ ρ) (hl : |l| ≤ K * ρ) :
    q.setPointQP σP a ![b 0, b 1, Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) 1] ≤
      ENNReal.ofReal ((q.M * (20 + 2 * K) + (1 + q.ωc * (q.A * (5 + K))) + q.D * (5 + K)) ^ 2 /
        (2 * σP ^ 2) * ρ ^ 2) := by
  have hM := q.M_pos
  set Cu := q.M * (20 + 2 * K) + (1 + q.ωc * (q.A * (5 + K))) + q.D * (5 + K) with hCu
  set F := Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) with hF
  set ang := fun t => herm a b t + l * Dynamics.endBump t with hang
  set vel := fun t => hermVel a b t + l * Dynamics.endBumpVel t with hvel
  set acc := fun t => hermAcc a b t + l * Dynamics.endBumpAcc t with hacc
  set φ := fun t => ![ang t, vel t, F t] with hφ
  set u : ℝ → Fin 1 → ℝ := fun t => ![(q.M * acc t + (F t - q.Pref) + q.D * vel t) / σP] with hu
  have hangd : ∀ t, HasDerivAt ang (vel t) t := fun t => by
    have h := (hasDerivAt_herm a b t).add (Dynamics.hasDerivAt_endBump l 0 t)
    simp only [zero_add] at h
    exact h
  have hveld : ∀ t, HasDerivAt vel (acc t) t := fun t =>
    (hasDerivAt_hermVel a b t).add (Dynamics.hasDerivAt_endBumpVel l t)
  have hFd : ∀ t, HasDerivAt F (q.ωc * (q.gsig a b l t - F t)) t := fun t =>
    Dynamics.hasDerivAt_lagFilter (q.continuous_gsig a b l) t
  have hφd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt φ (controlField q.sdeDrift
      (fun _ (_ : Fin 1) => q.setPointColumn σP) (φ t) (u t)) (Ici t) t := by
    intro t _
    rw [show u t = ![(q.M * acc t + (F t - q.Pref) + q.D * vel t) / σP] from rfl,
      controlField_setPoint]
    convert Dynamics.hasDerivWithinAt_vec_three (hangd t).hasDerivWithinAt
      (hveld t).hasDerivWithinAt (hFd t).hasDerivWithinAt using 1
    ext i; fin_cases i
    · rfl
    · show (q.Pref - F t - q.D * vel t) / q.M +
        (q.M * acc t + (F t - q.Pref) + q.D * vel t) / σP * (σP / q.M) = acc t
      field_simp; ring
    · show q.ωc * (q.c0 + q.A * Real.sin (ang t - q.α) - F t) = q.ωc * (q.gsig a b l t - F t)
      rfl
  have hφc : Continuous φ := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_iff_continuousAt.2 fun t => (hangd t).continuousAt
    · exact continuous_iff_continuousAt.2 fun t => (hveld t).continuousAt
    · exact continuous_iff_continuousAt.2 fun t => (hFd t).continuousAt
  have hφ0 : φ 0 = a := by
    ext i; fin_cases i
    · simp [hφ, hang, herm, Dynamics.endBump]
    · simp [hφ, hvel, hermVel, Dynamics.endBumpVel]
    · simp [hφ, hF, Dynamics.lagFilter_zero]
  have hφ1 : φ 1 = ![b 0, b 1, F 1] := by
    ext i; fin_cases i
    · simp [hφ, hang, herm, Dynamics.endBump]; ring
    · simp [hφ, hvel, hermVel, Dynamics.endBumpVel]; ring
    · rfl
  have huc : Continuous fun t => u t 0 := by
    have h1 : Continuous acc := by simp only [hacc, hermAcc, Dynamics.endBumpAcc]; fun_prop
    have h2 : Continuous vel := continuous_iff_continuousAt.2 fun t => (hveld t).continuousAt
    have h3 : Continuous F := continuous_iff_continuousAt.2 fun t => (hFd t).continuousAt
    simp only [hu, Matrix.cons_val_zero]
    fun_prop
  have hint : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) MeasureTheory.volume 0 1 := by
    simp only [Fin.sum_univ_one]
    exact (huc.pow 2).intervalIntegrable _ _
  have hle := controlQuasiPotential_le (b := q.sdeDrift)
    (σ := fun _ (_ : Fin 1) => q.setPointColumn σP) (u := u) zero_le_one hφ0 hφ1
    hφc.continuousOn hφd hint
  refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
  have hσ0 : 0 < |σP| := abs_pos.2 hσ
  have hub : ∀ t ∈ Icc (0 : ℝ) 1, u t 0 ^ 2 ≤ (Cu * ρ / |σP|) ^ 2 := by
    intro t ht
    have h := q.glue_control_le hr hK ha0 hb0 ha1 hb1 ha2 hl ht
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    show |(q.M * acc t + (F t - q.Pref) + q.D * vel t) / σP| ≤ Cu * ρ / |σP|
    rw [abs_div]
    exact div_le_div_of_nonneg_right h hσ0.le
  have hbound : ∫ t in (0 : ℝ)..1, u t 0 ^ 2 ≤ (Cu * ρ / |σP|) ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
      ((huc.pow 2).intervalIntegrable _ _) intervalIntegrable_const hub
    rwa [intervalIntegral.integral_const, sub_zero, one_smul] at this
  simp only [controlAction, Fin.sum_univ_one]
  have e : (Cu * ρ / |σP|) ^ 2 = Cu ^ 2 / σP ^ 2 * ρ ^ 2 := by
    rw [div_pow, mul_pow, sq_abs]; ring
  rw [e] at hbound
  have e2 : Cu ^ 2 / (2 * σP ^ 2) * ρ ^ 2 = 1 / 2 * (Cu ^ 2 / σP ^ 2 * ρ ^ 2) := by
    field_simp
  rw [e2]
  linarith

/-- **Local controllability at a rest point** (`σ_P ≠ 0`): at a rest angle `δ_r`
(`P(δ_r) = P_ref`) with `cos(δ_r − α) ≠ 0`, any two states within `ρ ≤ ρ₀` of `(δ_r, 0, P_ref)`
are joined by an admissible pair of action `≤ C ρ²` (`glue_pair` with the amplitude of
`glue_amplitude`). -/
@[tmio M, powerlib_domain] private theorem glue {σP : ℝ} (hσ : σP ≠ 0) {δr : ℝ}
    (hr : q.c0 + q.A * Real.sin (δr - q.α) = q.Pref) (hκ : Real.cos (δr - q.α) ≠ 0) :
    ∃ ρ₀ > 0, ∃ C > 0, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ a b : Fin 3 → ℝ,
      (∀ i, |a i - ![δr, 0, q.Pref] i| ≤ ρ) → (∀ i, |b i - ![δr, 0, q.Pref] i| ≤ ρ) →
      q.setPointQP σP a b ≤ ENNReal.ofReal (C * ρ ^ 2) := by
  have hA := q.A_pos; have hω := q.ωc_pos; have hM := q.M_pos; have hD := q.D_nonneg
  have hκ0 : 0 < |q.A * Real.cos (δr - q.α)| := abs_pos.2 (mul_ne_zero hA.ne' hκ)
  set K := (5 * q.A + 4) / (|q.A * Real.cos (δr - q.α)| * (q.ωc * Real.exp (-q.ωc) / 30))
    with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  set Cu := q.M * (20 + 2 * K) + (1 + q.ωc * (q.A * (5 + K))) + q.D * (5 + K)
  refine ⟨1 / (q.A * (5 + K) ^ 2), by positivity, Cu ^ 2 / (2 * σP ^ 2), by positivity,
    fun ρ hρ hρρ a b ha hb => ?_⟩
  have hρK : q.A * ((5 + K) * ρ) ^ 2 ≤ ρ := by
    rw [le_div_iff₀ (by positivity)] at hρρ
    nlinarith
  have ha0 : |a 0 - δr| ≤ ρ := by simpa using ha 0
  have ha1 : |a 1| ≤ ρ := by simpa using ha 1
  have ha2 : |a 2 - q.Pref| ≤ ρ := by simpa using ha 2
  have hb0 : |b 0 - δr| ≤ ρ := by simpa using hb 0
  have hb1 : |b 1| ≤ ρ := by simpa using hb 1
  have hb2 : |b 2 - q.Pref| ≤ ρ := by simpa using hb 2
  obtain ⟨l, hl, hgl⟩ := q.glue_amplitude hr hκ hρ hK hρK ha0 hb0 ha1 hb1 ha2 hb2
  have hb : b = ![b 0, b 1, Dynamics.lagFilter q.ωc (a 2) (q.gsig a b l) 1] := by
    ext i; fin_cases i
    · rfl
    · rfl
    · exact hgl.symm
  rw [hb]
  exact q.glue_pair hσ hr hK0.le ha0 hb0 ha1 hb1 ha2 hl

/-! ## The escape exponent at every bandwidth -/

/-- **The filter lowers the escape exponent at every bandwidth, quantitatively** (`P_ref = c₀`,
`D > 0`, `σ_P ≠ 0`, any `ω_c > 0`): from the stable equilibrium `(α, 0, c₀)` to the saddle
`(π + α, 0, c₀)`, `V₃ ≤ 2D (2A)/σ_P² − D M J/(σ_P² ω_c)`, `J = balancedGain > 0`. Proof: an
orbit of the reversed field from the saddle's neighbourhood to the stable equilibrium
(`exists_saddle_orbit`), read backwards, is an uphill pair of action
`(2D/σ_P²)(F(end) − F(start) − (M/ω_c)∫ω̇²)` (`Params3.setPointQP_le_uphill`) with
`∫ω̇² ≥ J` (`gain_le`); two short pairs of action `O(ρ²)` (`glue`) join its ends to the
equilibria. -/
@[tmio M, powerlib_domain] theorem setPointQP_le_balanced_rest {σP : ℝ} (hσ : σP ≠ 0)
    (hD : 0 < q.D) (hP : q.Pref = q.c0) :
    q.setPointQP σP ![q.α, 0, q.c0] ![π + q.α, 0, q.c0] ≤
      ENNReal.ofReal (2 * q.D * (2 * q.A) / σP ^ 2 -
        q.D * q.M * q.balancedGain / (σP ^ 2 * q.ωc)) := by
  have hM := q.M_pos; have hA := q.A_pos; have hω := q.ωc_pos; have hpi := Real.pi_pos
  have hσ2 : 0 < σP ^ 2 := by positivity
  set J := q.balancedGain with hJ
  have hJ0 : 0 < J := q.balancedGain_pos hD
  set G := 2 * q.D * q.M * J / (σP ^ 2 * q.ωc) with hG
  have hG0 : 0 < G := by positivity
  set w₀ := q.balancedSpeed
  have hw0 : 0 < w₀ := q.balancedSpeed_pos hD
  -- local controllability at both equilibria
  obtain ⟨ρu, hρu, Cu, hCu, hgu⟩ := q.glue hσ (δr := π + q.α)
    (by rw [show π + q.α - q.α = π by ring, Real.sin_pi, mul_zero, add_zero, hP])
    (by rw [show π + q.α - q.α = π by ring, Real.cos_pi]; norm_num)
  obtain ⟨ρs, hρs, Cs, hCs, hgs⟩ := q.glue hσ (δr := q.α)
    (by rw [sub_self, Real.sin_zero, mul_zero, add_zero, hP])
    (by rw [sub_self, Real.cos_zero]; norm_num)
  -- the saddle end
  set ε := min (min ρu (π / 12)) (min (q.A / q.D) √(G / (8 * Cu))) with hεdef
  have hε0 : 0 < ε := lt_min (lt_min hρu (by positivity))
    (lt_min (by positivity) (Real.sqrt_pos.2 (by positivity)))
  have hερ : ε ≤ ρu := (min_le_left _ _).trans (min_le_left _ _)
  have hεπ : ε ≤ π / 12 := (min_le_left _ _).trans (min_le_right _ _)
  have hεD : ε ≤ q.A / q.D := (min_le_right _ _).trans (min_le_left _ _)
  have hεG : Cu * ε ^ 2 ≤ G / 8 := by
    have h1 : ε ≤ √(G / (8 * Cu)) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : ε ^ 2 ≤ G / (8 * Cu) := by
      calc ε ^ 2 ≤ √(G / (8 * Cu)) ^ 2 := pow_le_pow_left₀ hε0.le h1 2
        _ = G / (8 * Cu) := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ (by positivity)] at h2
    linarith
  obtain ⟨y, hyc, hyE, hyz, hylim⟩ := q.exists_saddle_orbit hP hD hε0 (by linarith) hεD
  -- the stable end
  set ρ₁ := min (min ρs (π / 6)) (min (w₀ / 2) √(G / (8 * Cs))) with hρ₁def
  have hρ₁0 : 0 < ρ₁ := lt_min (lt_min hρs (by positivity))
    (lt_min (by positivity) (Real.sqrt_pos.2 (by positivity)))
  have hρ₁s : ρ₁ ≤ ρs := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₁π : ρ₁ ≤ π / 6 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₁w : ρ₁ ≤ w₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₁G : Cs * ρ₁ ^ 2 ≤ G / 8 := by
    have h1 : ρ₁ ≤ √(G / (8 * Cs)) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : ρ₁ ^ 2 ≤ G / (8 * Cs) := by
      calc ρ₁ ^ 2 ≤ √(G / (8 * Cs)) ^ 2 := pow_le_pow_left₀ hρ₁0.le h1 2
        _ = G / (8 * Cs) := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ (by positivity)] at h2
    linarith
  set η := min (G * σP ^ 2 / (16 * q.D)) q.A with hηdef
  have hη0 : 0 < η := lt_min (by positivity) hA
  have hηA : η ≤ q.A := min_le_right _ _
  have hηG : 2 * q.D / σP ^ 2 * η ≤ G / 8 := by
    have h1 : η ≤ G * σP ^ 2 / (16 * q.D) := min_le_left _ _
    have : 2 * q.D / σP ^ 2 * (G * σP ^ 2 / (16 * q.D)) = G / 8 := by field_simp; ring
    calc 2 * q.D / σP ^ 2 * η ≤ 2 * q.D / σP ^ 2 * (G * σP ^ 2 / (16 * q.D)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = G / 8 := this
  have hxs : q.downEnergy ![q.α, 0, q.c0] = -q.A := by
    simp [downEnergy, q.potential_balanced hP]
  have hEc : Tendsto (fun t => q.downEnergy (q.dsol y t)) atTop (𝓝 (-q.A)) := by
    rw [← hxs]; exact (q.continuous_downEnergy.tendsto _).comp hylim
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hylim.eventually (Metric.ball_mem_nhds _ hρ₁0)).and
    ((hEc.eventually (lt_mem_nhds (show -q.A - η < -q.A by linarith))).and
      (eventually_ge_atTop 1)))
  obtain ⟨hTball, hTE, hT1⟩ := hT T le_rfl
  have hT0 : 0 ≤ T := by linarith
  have hTc : ∀ i, |q.dsol y T i - ![q.α, 0, q.c0] i| < ρ₁ := fun i => by
    have := (dist_le_pi_dist (q.dsol y T) ![q.α, 0, q.c0] i).trans_lt hTball
    rwa [Real.dist_eq] at this
  -- the uphill pair: the reversed orbit read backwards
  set ψ := fun t => flip3 (q.dsol y (T - t)) with hψ
  have hψd : ∀ t ∈ Ico 0 T, HasDerivAt ψ (q.upField (ψ t)) t := fun t ht =>
    q.hasDerivAt_reverse y ht.2
  have hflipc : Continuous flip3 := by
    unfold flip3; exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
  have hψc : ContinuousOn ψ (Icc 0 T) := by
    refine hflipc.comp_continuousOn ((q.dsol_continuousOn y).comp
      (continuous_const.sub continuous_id).continuousOn fun t ht => ?_)
    simp only [mem_Ici]; linarith [ht.2]
  have hψpair : ∀ t ∈ Ico 0 T, HasDerivWithinAt ψ (controlField q.sdeDrift
      (fun _ (_ : Fin 1) => q.setPointColumn σP) (ψ t) ![2 * q.D * ψ t 1 / σP]) (Ici t) t := by
    intro t ht
    rw [q.uphill_field hσ]
    exact (hψd t ht).hasDerivWithinAt
  have hψ0 : ψ 0 = flip3 (q.dsol y T) := by simp [hψ]
  have hψT : ψ T = flip3 y := by simp [hψ, q.dsol_zero]
  have hFT : q.uphillEnergy (ψ T) = q.downEnergy y := by
    rw [hψT, ← q.uphillEnergy_flip]; rfl
  have hF0 : q.uphillEnergy (ψ 0) = q.downEnergy (q.dsol y T) := by
    rw [hψ0, ← q.uphillEnergy_flip]; rfl
  have hbal := q.uphillEnergy_sub_eq hσ hD hT0 hψc hψpair
  set I := ∫ t in (0 : ℝ)..T, q.uphillAcc (ψ t) ^ 2 with hI
  set N₁ := ∫ t in (0 : ℝ)..T, ψ t 1 ^ 2 with hN₁
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hT0 fun t _ => sq_nonneg _
  have hN₁0 : 0 ≤ N₁ := intervalIntegral.integral_nonneg hT0 fun t _ => sq_nonneg _
  have hN : N₁ ≤ 3 * q.A / q.D := by
    rw [le_div_iff₀ hD]
    have : 0 ≤ q.M / q.ωc * I := by positivity
    rw [hFT, hF0] at hbal
    nlinarith
  -- the gain
  have hgain : J ≤ I := by
    have h := q.gain_le hP hD hT0 hψc hψd
      (fun t ht => by
        show |(flip3 (q.dsol y (T - t))) 2 - q.c0| ≤ q.A
        exact hyz (T - t) (by linarith [ht.2]))
      (by
        rw [hψ0]
        show q.dsol y T 0 - q.α ≤ π / 6
        have := (abs_lt.1 (hTc 0)).2
        simp only [Matrix.cons_val_zero] at this
        linarith)
      (by
        rw [hψT]
        show 5 * π / 6 ≤ y 0 - q.α
        have := (abs_le.1 (hyc 0)).1
        simp only [Matrix.cons_val_zero] at this
        linarith)
      (by
        rw [hψ0]
        show (-(q.dsol y T 1)) ^ 2 ≤ w₀ ^ 2 / 4
        have := hTc 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero] at this
        have h1 : |q.dsol y T 1| ≤ w₀ / 2 := this.le.trans hρ₁w
        rw [neg_sq, ← sq_abs]
        calc |q.dsol y T 1| ^ 2 ≤ (w₀ / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = w₀ ^ 2 / 4 := by ring)
      (by positivity : (0 : ℝ) < 3 * q.A / q.D) hN
    have e : 9 * w₀ ^ 4 / (64 * (3 * q.A / q.D)) = J := by
      rw [hJ, balancedGain]; field_simp; ring
    rwa [e] at h
  -- the three pieces
  have hmid := q.setPointQP_le_uphill hσ hD hT0 hψc hψpair
  have hs := hgs ρ₁ hρ₁0 hρ₁s ![q.α, 0, q.c0] (ψ 0)
    (fun i => by fin_cases i <;> simp [hP, hρ₁0.le])
    (fun i => by
      rw [hψ0]
      have := (hTc i).le
      fin_cases i
      · simpa [flip3] using this
      · simpa [flip3, abs_neg] using this
      · simpa [flip3, hP] using this)
  have hu := hgu ε hε0 hερ (ψ T) ![π + q.α, 0, q.c0]
    (fun i => by
      rw [hψT]
      have := hyc i
      fin_cases i
      · simpa [flip3] using this
      · simpa [flip3, abs_neg] using this
      · simpa [flip3, hP] using this)
    (fun i => by fin_cases i <;> simp [hP, hε0.le])
  -- assemble with the triangle inequality
  set mid := 2 * q.D / σP ^ 2 * (q.uphillEnergy (ψ T) - q.uphillEnergy (ψ 0) - q.M / q.ωc * I)
    with hmiddef
  have hmid0 : 0 ≤ mid := by
    rw [hmiddef, hbal]
    have h1 : 0 ≤ q.D * N₁ := by positivity
    have h2 : q.D * N₁ + q.M / q.ωc * I - q.M / q.ωc * I = q.D * N₁ := by ring
    rw [h2]
    exact mul_nonneg (by positivity) h1
  have htri : q.setPointQP σP ![q.α, 0, q.c0] ![π + q.α, 0, q.c0] ≤
      ENNReal.ofReal (Cs * ρ₁ ^ 2) + (ENNReal.ofReal mid + ENNReal.ofReal (Cu * ε ^ 2)) := by
    have t1 := controlQuasiPotential_triangle q.sdeDrift (fun _ (_ : Fin 1) => q.setPointColumn σP)
      ![q.α, 0, q.c0] (ψ 0) ![π + q.α, 0, q.c0]
    have t2 := controlQuasiPotential_triangle q.sdeDrift (fun _ (_ : Fin 1) => q.setPointColumn σP)
      (ψ 0) (ψ T) ![π + q.α, 0, q.c0]
    exact t1.trans (add_le_add hs (t2.trans (add_le_add hmid hu)))
  refine htri.trans ?_
  rw [← ENNReal.ofReal_add hmid0 (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hFTA : q.uphillEnergy (ψ T) < q.A := by rw [hFT]; exact hyE
  have hF0A : -q.A - η < q.uphillEnergy (ψ 0) := by rw [hF0]; exact hTE
  have hJI : G ≤ 2 * q.D / σP ^ 2 * (q.M / q.ωc * I) := by
    have : 2 * q.D / σP ^ 2 * (q.M / q.ωc * J) = G := by rw [hG]; field_simp
    rw [← this]
    gcongr
  have hmidle : mid ≤ 2 * q.D / σP ^ 2 * (2 * q.A + η) - G := by
    have h1 : mid = 2 * q.D / σP ^ 2 * (q.uphillEnergy (ψ T) - q.uphillEnergy (ψ 0)) -
        2 * q.D / σP ^ 2 * (q.M / q.ωc * I) := by rw [hmiddef]; ring
    have h2 : 2 * q.D / σP ^ 2 * (q.uphillEnergy (ψ T) - q.uphillEnergy (ψ 0)) ≤
        2 * q.D / σP ^ 2 * (2 * q.A + η) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hfin : 2 * q.D * (2 * q.A) / σP ^ 2 - q.D * q.M * J / (σP ^ 2 * q.ωc) =
      2 * q.D / σP ^ 2 * (2 * q.A) - G / 2 := by rw [hG]; field_simp
  rw [hfin]
  have : 2 * q.D / σP ^ 2 * (2 * q.A + η) = 2 * q.D / σP ^ 2 * (2 * q.A) +
      2 * q.D / σP ^ 2 * η := by ring
  linarith

end Params3

namespace Params

variable (p : Params)

/-- **The power filter lowers the escape exponent at every bandwidth, quantitatively, for the
balanced set point** (`P_ref = c₀`, `D > 0`, `σ_P ≠ 0`, every `ω_c > 0`): from the stable
equilibrium `(δ_s, 0, P(δ_s))` to the saddle `(δ_u, 0, P(δ_u))`
(`δ_s = α`, `δ_u = π + α`), `V₃ ≤ 2D (U(δ_u) − U(δ_s))/σ_P² − D M J/(σ_P² ω_c)` with the
explicit `J = Params3.balancedGain > 0` (`Params3.setPointQP_le_balanced_rest`). -/
@[tmio M, powerlib_domain] theorem setPointQP_le_balanced {σP : ℝ} (hσ : σP ≠ 0)
    (hD : 0 < p.D) (hP : p.Pref = p.c0) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) (ωc : ℝ) (hω : 0 < ωc) :
    (⟨p, ωc, hω⟩ : Params3).setPointQP σP ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)]
        ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)] ≤
      ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2 -
        p.D * p.M * (⟨p, ωc, hω⟩ : Params3).balancedGain / (σP ^ 2 * ωc)) := by
  have hs0 : Real.arcsin ((p.Pref - p.c0) / p.A) = 0 := by
    rw [hP, sub_self, zero_div, Real.arcsin_zero]
  have hs : δs = p.α := by rw [hδs, hs0, zero_add]
  have hu : δu = π + p.α := by rw [hδu, hs0, sub_zero]
  have e1 : p.c0 + p.A * Real.sin (δs - p.α) = p.c0 := by rw [hs, sub_self, Real.sin_zero]; ring
  have e2 : p.c0 + p.A * Real.sin (δu - p.α) = p.c0 := by
    rw [hu, show π + p.α - p.α = π by ring, Real.sin_pi]; ring
  have hpot : p.potential (δu - p.α) - p.potential (δs - p.α) = 2 * p.A := by
    rw [hs, hu, show π + p.α - p.α = π by ring, sub_self]
    simp [Params.potential, Params.toSM, hP]; ring
  rw [e1, e2, hpot, hs, hu]
  exact (⟨p, ωc, hω⟩ : Params3).setPointQP_le_balanced_rest hσ hD hP

/-- **`V₃ < V₂` for every bandwidth, balanced set point** (`P_ref = c₀`, `D > 0`, `σ_P ≠ 0`,
every `ω_c > 0`): the three-state escape exponent (stable equilibrium to saddle, set-point noise)
is strictly below the two-state one `V₂ = Params.swingQP` (`setPointQP_le_balanced`,
`swingQP_saddle_eq`). -/
@[tmio M, powerlib_domain] theorem setPointQP_lt_swingQP_balanced {σP : ℝ} (hσ : σP ≠ 0)
    (hD : 0 < p.D) (hP : p.Pref = p.c0) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) (ωc : ℝ) (hω : 0 < ωc) :
    (⟨p, ωc, hω⟩ : Params3).setPointQP σP ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)]
        ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)] < p.swingQP σP ![δs, 0] ![δu, 0] := by
  have hA := p.A_pos; have hM := p.M_pos
  have h := p.setPointQP_le_balanced hσ hD hP hδs hδu ωc hω
  have hV : p.swingQP σP ![δs, 0] ![δu, 0] =
      ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) := by
    have := p.swingQP_saddle_eq hσ hD hP.ge (by rw [hP]; linarith)
    rw [hδs, hδu]
    simpa only [add_sub_cancel_right] using this
  rw [hV]
  have hg : 0 < (⟨p, ωc, hω⟩ : Params3).balancedGain :=
    (⟨p, ωc, hω⟩ : Params3).balancedGain_pos hD
  have hs0 : Real.arcsin ((p.Pref - p.c0) / p.A) = 0 := by
    rw [hP, sub_self, zero_div, Real.arcsin_zero]
  have hpot : p.potential (δu - p.α) - p.potential (δs - p.α) = 2 * p.A := by
    rw [hδs, hδu, hs0, sub_zero, zero_add, show π + p.α - p.α = π by ring, sub_self]
    simp [Params.potential, Params.toSM, hP]; ring
  have hσ2 : 0 < σP ^ 2 := by positivity
  refine h.trans_lt (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨?_, ?_⟩)
  · have : 0 < p.D * p.M * (⟨p, ωc, hω⟩ : Params3).balancedGain / (σP ^ 2 * ωc) := by
      positivity
    linarith
  · rw [hpot]; positivity

end Params


end powerlib.GFM.Noise
