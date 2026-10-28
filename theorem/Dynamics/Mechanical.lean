import theorem.Dynamics.LaSalle.Ball
import theorem.Dynamics.Instability
import theorem.Dynamics.Coordinates

/-! # Damped mechanical systems: potential minima and local asymptotic stability (foundation)

Positions driven by velocities through a linear map, velocities driven by damping and the
generalized force of a potential. At a state at rest, local asymptotic stability is decided by the
potential alone, whatever the linearization: a strict local minimum that is an isolated critical
point is locally asymptotically stable (LaSalle with the energy), and conversely a locally
asymptotically stable rest point is such a minimum (the energy does not increase, and critical
points are equilibria).

Scope.
* Autonomous continuous-time ODE on `Dynamics.State (m + k) = EuclideanSpace ℝ (Fin (m + k))`:
  positions `q = pos z` (the first `m` coordinates, `qIdx i = Fin.castAdd k i`), then velocities
  `w = vel z` (the last `k`, `vIdx j = Fin.natAdd m j`). The field `field G M D U` is
  `q̇ = G w`, `Mⱼ ẇⱼ = −Dⱼ wⱼ − dU(q)(G eⱼ)`, with a continuous linear map `G : ℝᵏ → ℝᵐ`, masses
  `Mⱼ`, dampings `Dⱼ` and a potential `U : ℝᵐ → ℝ` (the generalized force is `Gᵀ ∇U(q)`).
  `point q` is the state at rest at `q`; it is an equilibrium when `dU(q) ∘ G = 0`
  (`field_point_eq_zero`: `q` is a critical point of `U` along the directions `G` reaches), and
  with nonzero masses only then (`field_point_eq_zero_iff`). No input, delay, switching or time
  variation.
* Every statement is a generic implication about arbitrary `G`, `M`, `D` and `U`, a foundation
  result; no model family is defined or fixed here. `theorem/Network/Swing/Degenerate.lean`
  identifies the reduced swing network at a power-balance point with such a field
  (`reducedField_eq_mechanical`) and applies these results inside its connection proofs.

Source: energy methods for dissipative mechanical systems (Lagrange–Dirichlet; LaSalle's invariance
principle, Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.4 and Corollary 4.1); needed by
work-sync `theory/T-synchronization-manifold.md` §2.2 (energy function of the swing network).

Results.
* Static: `pos`, `vel`, `point`, `field`, `energy`; `apply_eq_sum` and `comp_eq_zero_iff` (the
  generalized force determines `dU(q) ∘ G`), `field_contDiff` (a `C²` potential gives a `C¹`
  field), `hasFDerivAt_energy`, `lie_energy` (`Ė = −∑ⱼ Dⱼ wⱼ²`), `field_point_eq_zero_iff`,
  `energy_point`, `energy_sub_point`.
* `not_localAsymptoticStable_of_potential_lt`: positions arbitrarily close to `q` with a lower
  potential rule out local asymptotic stability of `point q` (masses `Mⱼ ≠ 0`, dampings `Dⱼ ≥ 0`,
  `U` of class `C²`; `Dynamics.not_localAsymptoticStable_of_lie_nonpos` with the energy).
* `not_localAsymptoticStable_of_critical` (critical points accumulating at `q`) and
  `not_localAsymptoticStable_of_critical_line` (a line of critical points through `q`): a
  continuum of equilibria rules it out (`Dynamics.not_localAsymptoticStable_of_equilibria`).
* `localAsymptoticStable_of_strictMin`: a critical point `q` that is a strict local minimum of `U`
  and an isolated critical point is locally asymptotically stable (`Mⱼ > 0`, `Dⱼ > 0`; LaSalle on
  a ball, `LaSalle.localAsymptoticStable_of_lasalle_ball`, with the energy relative to `q`).
* `strictMin_of_localAsymptoticStable`: conversely (`Mⱼ ≠ 0`, `Dⱼ ≥ 0`, `U` of class `C²`), a
  locally asymptotically stable rest point is a strict local minimum of `U` and an isolated
  critical point.
-/

noncomputable section
namespace powerlib.Dynamics.Mechanical
open Set Filter Topology Metric

variable {m k : ℕ}

/-! ## Coordinates -/

/-- Position of the coordinate `qᵢ` in the state. -/
abbrev qIdx (i : Fin m) : Fin (m + k) := Fin.castAdd k i

/-- Position of the velocity `wⱼ` in the state. -/
abbrev vIdx (j : Fin k) : Fin (m + k) := Fin.natAdd m j

/-- A state is determined by its positions and velocities (`Dynamics.state_ext_blocks`). -/
@[tmio T, powerlib_foundation] theorem state_ext {z z' : State (m + k)}
    (hq : ∀ i, z (qIdx i) = z' (qIdx i)) (hv : ∀ j, z (vIdx j) = z' (vIdx j)) : z = z' :=
  state_ext_blocks hq hv

/-- The positions of a state. -/
def pos : State (m + k) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i => PiLp.proj 2 (fun _ : Fin (m + k) => ℝ) (qIdx i)

/-- The velocities of a state. -/
def vel : State (m + k) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun j => PiLp.proj 2 (fun _ : Fin (m + k) => ℝ) (vIdx j)

@[tmio T, simp, powerlib_foundation] theorem pos_apply (z : State (m + k)) (i : Fin m) :
    pos z i = z (qIdx i) := by
  simp [pos]

@[tmio T, simp, powerlib_foundation] theorem vel_apply (z : State (m + k)) (j : Fin k) :
    vel z j = z (vIdx j) := by
  simp [vel]

/-- The positions bound their state. -/
@[tmio T, powerlib_foundation] theorem norm_pos_le (z : State (m + k)) : ‖pos z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun i => by
    simpa using PiLp.norm_apply_le z (qIdx i)

/-- The state at rest with positions `q`. -/
def point : (Fin m → ℝ) →L[ℝ] State (m + k) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ) q (fun _ => 0) r
      map_add' := fun q v => by
        ext r
        refine Fin.addCases (fun i => ?_) (fun j => ?_) r <;> simp
      map_smul' := fun c q => by
        ext r
        refine Fin.addCases (fun i => ?_) (fun j => ?_) r <;> simp }

@[tmio T, simp, powerlib_foundation] theorem point_qIdx (q : Fin m → ℝ) (i : Fin m) :
    point (k := k) q (qIdx i) = q i := by
  simp [point]

@[tmio T, simp, powerlib_foundation] theorem point_vIdx (q : Fin m → ℝ) (j : Fin k) :
    point (k := k) q (vIdx j) = 0 := by
  simp [point]

@[tmio T, simp, powerlib_foundation] theorem pos_point (q : Fin m → ℝ) : pos (point (k := k) q) = q := by
  ext i
  simp

@[tmio T, simp, powerlib_foundation] theorem vel_point (q : Fin m → ℝ) : vel (point (k := k) q) = 0 := by
  ext j
  simp

/-- The distance of a state from a rest point bounds the distance of its positions. -/
@[tmio T, powerlib_foundation] theorem norm_pos_sub_le (z : State (m + k)) (q : Fin m → ℝ) :
    ‖pos z - q‖ ≤ ‖z - point q‖ := by
  have := norm_pos_le (z - point q)
  rwa [map_sub, pos_point] at this

/-- Small positions give rest points close to the origin. -/
@[tmio T, powerlib_foundation] theorem exists_norm_point_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : Fin m → ℝ, ‖v‖ < δ → ‖point (k := k) v‖ < ε := by
  have hc := (point (m := m) (k := k)).continuous.continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc ε hε
  refine ⟨δ, hδ, fun v hv => ?_⟩
  have := @h v (by rwa [dist_zero_right])
  rwa [map_zero, dist_zero_right] at this

/-! ## The field and its energy -/

/-- The damped mechanical field `q̇ = G w`, `Mⱼ ẇⱼ = −Dⱼ wⱼ − dU(q)(G eⱼ)`. -/
def field (G : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ)) (M D : Fin k → ℝ) (U : (Fin m → ℝ) → ℝ)
    (z : State (m + k)) : State (m + k) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ) (G (vel z))
    (fun j => (-(D j * z (vIdx j)) - fderiv ℝ U (pos z) (G (Pi.single j 1))) / M j) r

/-- Kinetic plus potential energy, `E = ½ ∑ⱼ Mⱼ wⱼ² + U(q)`. -/
def energy (M : Fin k → ℝ) (U : (Fin m → ℝ) → ℝ) (z : State (m + k)) : ℝ :=
  (∑ j, M j * z (vIdx j) ^ 2) / 2 + U (pos z)

variable {G : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ)} {M D : Fin k → ℝ} {U : (Fin m → ℝ) → ℝ}

@[simp, powerlib_foundation] theorem field_qIdx (z : State (m + k)) (i : Fin m) :
    field G M D U z (qIdx i) = G (vel z) i := by
  simp [field]

@[simp, powerlib_foundation] theorem field_vIdx (z : State (m + k)) (j : Fin k) :
    field G M D U z (vIdx j) =
      (-(D j * z (vIdx j)) - fderiv ℝ U (pos z) (G (Pi.single j 1))) / M j := by
  simp [field]

@[simp, powerlib_foundation] theorem pos_field (z : State (m + k)) :
    pos (field G M D U z) = G (vel z) := by
  ext i
  simp

/-- A linear functional of `G w` is the combination of its values on the unit velocities. -/
@[tmio T, powerlib_foundation] theorem apply_eq_sum (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ)) (w : Fin k → ℝ) :
    L (G w) = ∑ j, w j * L (G (Pi.single j 1)) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Pi.single j (w j) = w j • Pi.single j (1 : ℝ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, map_smul, smul_eq_mul]

/-- `dU(q) ∘ G` vanishes exactly when the generalized force vanishes. -/
@[tmio T, powerlib_foundation] theorem comp_eq_zero_iff (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ)) :
    L.comp G = 0 ↔ ∀ j, L (G (Pi.single j 1)) = 0 := by
  constructor
  · intro h j
    have := congrArg (fun T : (Fin k → ℝ) →L[ℝ] ℝ => T (Pi.single j 1)) h
    simpa using this
  · intro h
    ext w
    rw [ContinuousLinearMap.comp_apply, apply_eq_sum L G]
    simp [h]

/-- A rest point is an equilibrium when `dU(q) ∘ G = 0`. -/
@[powerlib_foundation] theorem field_point_eq_zero {q : Fin m → ℝ}
    (hq : (fderiv ℝ U q).comp G = 0) : field G M D U (point q) = 0 := by
  have hj := (comp_eq_zero_iff _ G).mp hq
  apply state_ext
  · intro i; simp
  · intro j; simp [hj j]

/-- With nonzero masses, a rest point is an equilibrium exactly when `dU(q) ∘ G = 0`. -/
@[powerlib_foundation] theorem field_point_eq_zero_iff (hM : ∀ j, M j ≠ 0) (q : Fin m → ℝ) :
    field G M D U (point q) = 0 ↔ (fderiv ℝ U q).comp G = 0 := by
  refine ⟨fun h => (comp_eq_zero_iff _ G).mpr fun j => ?_, field_point_eq_zero⟩
  have := congrArg (fun z : State (m + k) => z (vIdx j)) h
  simp only [field_vIdx, pos_point, point_vIdx, mul_zero, neg_zero, zero_sub,
    PiLp.zero_apply, div_eq_zero_iff, neg_eq_zero, hM j, or_false] at this
  exact this

/-- A `C²` potential gives a `C¹` field. -/
@[powerlib_foundation] theorem field_contDiff (hU : ContDiff ℝ 2 U) :
    ContDiff ℝ 1 (field G M D U) := by
  rw [contDiff_euclidean]
  intro r
  refine Fin.addCases (fun i => ?_) (fun j => ?_) r
  · have : (fun z => field G M D U z (qIdx i)) = fun z => G (vel z) i := by
      funext z; exact field_qIdx z i
    rw [this]
    exact (contDiff_apply ℝ ℝ i).comp (G.contDiff.comp vel.contDiff)
  · have : (fun z => field G M D U z (vIdx j)) = fun z =>
        (-(D j * z (vIdx j)) - fderiv ℝ U (pos z) (G (Pi.single j 1))) / M j := by
      funext z; exact field_vIdx z j
    rw [this]
    apply ContDiff.div_const
    apply ContDiff.sub
    · exact (contDiff_const.mul (contDiff_piLp_apply 2)).neg
    · have h1 : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
      exact (h1.comp pos.contDiff).clm_apply contDiff_const

@[powerlib_foundation] theorem energy_contDiff (hU : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (energy M U) := by
  unfold energy
  apply ContDiff.add
  · apply ContDiff.div_const
    exact ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_piLp_apply 2).pow 2)
  · exact hU.comp pos.contDiff

@[powerlib_foundation] theorem hasFDerivAt_energy {z : State (m + k)}
    (hU : DifferentiableAt ℝ U (pos z)) :
    HasFDerivAt (energy M U)
      ((∑ j, (M j * z (vIdx j)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + k) => ℝ) (vIdx j)) +
        (fderiv ℝ U (pos z)).comp pos) z := by
  have hkin : HasFDerivAt (fun y : State (m + k) => (∑ j, M j * y (vIdx j) ^ 2) / 2)
      (∑ j, (M j * z (vIdx j)) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + k) => ℝ)
        (vIdx j)) z := by
    have hs : HasFDerivAt (fun y : State (m + k) => ∑ j, M j * y (vIdx j) ^ 2)
        (∑ j, (2 * (M j * z (vIdx j))) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + k) => ℝ)
          (vIdx j)) z := by
      refine HasFDerivAt.fun_sum fun j _ => ?_
      have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z (vIdx j)
      have h2 := (h1.mul h1).const_mul (M j)
      convert h2 using 1
      · funext y; simp only [Pi.mul_apply]; ring
      · ext v
        simp [smul_eq_mul]
        ring
    convert hs.const_mul (1 / 2 : ℝ) using 1
    · funext y; ring
    · ext v
      simp [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  exact hkin.add (hU.hasFDerivAt.comp z pos.hasFDerivAt)

/-- **Energy balance.** Along the field the energy changes at the rate `−∑ⱼ Dⱼ wⱼ²`: the
generalized force does no work. -/
@[powerlib_foundation] theorem lie_energy (hU : Differentiable ℝ U) (hM : ∀ j, M j ≠ 0)
    (z : State (m + k)) :
    fderiv ℝ (energy M U) z (field G M D U z) = -∑ j, D j * z (vIdx j) ^ 2 := by
  rw [(hasFDerivAt_energy (hU (pos z))).fderiv]
  simp only [add_apply, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    PiLp.proj_apply, smul_eq_mul, ContinuousLinearMap.coe_comp, Function.comp_apply, pos_field,
    field_vIdx]
  rw [apply_eq_sum (fderiv ℝ U (pos z)) G (vel z), ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [vel_apply]
  field_simp [hM j]
  ring

/-- With nonnegative damping the energy does not increase. -/
@[powerlib_foundation] theorem lie_energy_nonpos (hU : Differentiable ℝ U) (hM : ∀ j, M j ≠ 0)
    (hD : ∀ j, 0 ≤ D j) (z : State (m + k)) :
    fderiv ℝ (energy M U) z (field G M D U z) ≤ 0 := by
  rw [lie_energy hU hM, neg_nonpos]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hD j) (sq_nonneg _)

@[simp, powerlib_foundation] theorem energy_point (q : Fin m → ℝ) :
    energy M U (point (k := k) q) = U q := by
  simp [energy]

/-- The energy relative to a rest point: the kinetic energy plus the potential increment. -/
@[powerlib_foundation] theorem energy_sub_point (z : State (m + k)) (q : Fin m → ℝ) :
    energy M U z - energy M U (point q) =
      (∑ j, M j * z (vIdx j) ^ 2) / 2 + (U (pos z) - U q) := by
  rw [energy_point, energy]
  ring

/-! ## Obstructions to local asymptotic stability -/

/-- **A non-minimum of the potential is not asymptotically stable.** Positions arbitrarily close to
`q` with a lower potential rule out local asymptotic stability of the rest point: the energy does
not increase, so a solution started at rest there cannot reach `point q`. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_potential_lt (hU : ContDiff ℝ 2 U)
    (hM : ∀ j, M j ≠ 0) (hD : ∀ j, 0 ≤ D j) {q : Fin m → ℝ}
    (hseed : ∀ ε > 0, ∃ v : Fin m → ℝ, ‖v‖ < ε ∧ U (q + v) < U q) :
    ¬ LocalAsymptoticStable (field G M D U) (point q) := by
  have hU1 : Differentiable ℝ U := hU.differentiable (by norm_num)
  refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := energy M U) (ρ := 1)
    (field_contDiff hU) ((energy_contDiff (hU.of_le (by norm_num))).differentiable one_ne_zero)
    one_pos (fun x _ => lie_energy_nonpos hU1 hM hD x) fun ε hε => ?_
  obtain ⟨δ, hδ, hpt⟩ := exists_norm_point_lt (m := m) (k := k) hε
  obtain ⟨v, hv, hlt⟩ := hseed δ hδ
  refine ⟨point (q + v), ?_, ?_⟩
  · rw [map_add, add_sub_cancel_left]
    exact hpt v hv
  · rw [energy_point, energy_point]
    exact hlt

/-- **Accumulating critical points rule out local asymptotic stability**: each is a rest point of
the field near `point q`. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_critical {q : Fin m → ℝ}
    (h : ∀ ε > 0, ∃ v : Fin m → ℝ, v ≠ 0 ∧ ‖v‖ < ε ∧ (fderiv ℝ U (q + v)).comp G = 0) :
    ¬ LocalAsymptoticStable (field G M D U) (point q) := by
  refine Dynamics.not_localAsymptoticStable_of_equilibria fun ε hε => ?_
  obtain ⟨δ, hδ, hpt⟩ := exists_norm_point_lt (m := m) (k := k) hε
  obtain ⟨v, hv0, hv, hcrit⟩ := h δ hδ
  refine ⟨point (q + v), fun he => hv0 ?_, ?_, field_point_eq_zero hcrit⟩
  · have := congrArg pos he
    simpa using this
  · rw [map_add, add_sub_cancel_left]
    exact hpt v hv

/-- **A line of critical points is not asymptotically stable.** If `dU ∘ G` vanishes along
`q + t v` (`v ≠ 0`), every point of that line is a rest point of the field. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_critical_line {q v : Fin m → ℝ}
    (hv : v ≠ 0) (hline : ∀ t : ℝ, (fderiv ℝ U (q + t • v)).comp G = 0) :
    ¬ LocalAsymptoticStable (field G M D U) (point q) := by
  refine not_localAsymptoticStable_of_critical fun ε hε => ?_
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set t := ε / (2 * ‖v‖) with ht
  have ht0 : 0 < t := by positivity
  refine ⟨t • v, smul_ne_zero ht0.ne' hv, ?_, hline t⟩
  rw [norm_smul, Real.norm_of_nonneg ht0.le, ht]
  field_simp
  linarith

/-! ## Strict isolated minima -/

/-- **LaSalle at a strict isolated minimum.** A critical point `q` of the potential that is a
strict local minimum and an isolated critical point gives a locally asymptotically stable rest
point, whatever the linearization (positive masses and dampings). -/
@[powerlib_foundation] theorem localAsymptoticStable_of_strictMin (hmk : 0 < m + k)
    (hU : ContDiff ℝ 2 U) (hM : ∀ j, 0 < M j) (hD : ∀ j, 0 < D j) {q : Fin m → ℝ}
    (hq : (fderiv ℝ U q).comp G = 0) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ v : Fin m → ℝ, v ≠ 0 → ‖v‖ < r → U q < U (q + v))
    (hcrit : ∀ v : Fin m → ℝ, v ≠ 0 → ‖v‖ < r → (fderiv ℝ U (q + v)).comp G ≠ 0) :
    LocalAsymptoticStable (field G M D U) (point q) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hUd : Differentiable ℝ U := hU1.differentiable one_ne_zero
  have hM0 : ∀ j, M j ≠ 0 := fun j => (hM j).ne'
  refine LaSalle.localAsymptoticStable_of_lasalle_ball hmk (field_contDiff hU)
    (field_point_eq_zero hq) (W := fun z => energy M U z - energy M U (point q))
    ((energy_contDiff hU1).sub contDiff_const) (sub_self _) hr ?_ ?_ ?_
  · intro x hx hne
    show 0 < energy M U x - energy M U (point q)
    rw [energy_sub_point]
    have hkin : 0 ≤ (∑ j, M j * x (vIdx j) ^ 2) / 2 :=
      div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hM j).le (sq_nonneg _)) zero_le_two
    by_cases hv0 : pos x - q = 0
    · rw [sub_eq_zero] at hv0
      rw [hv0, sub_self, add_zero]
      have hw : ∃ j, x (vIdx j) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne
        apply state_ext
        · intro i
          have := congrFun hv0 i
          simp only [pos_apply] at this
          simp [this]
        · intro j; simp [hall j]
      obtain ⟨j₀, hj₀⟩ := hw
      have : 0 < ∑ j, M j * x (vIdx j) ^ 2 :=
        Finset.sum_pos' (fun j _ => mul_nonneg (hM j).le (sq_nonneg _))
          ⟨j₀, Finset.mem_univ _, mul_pos (hM j₀) (by positivity)⟩
      linarith
    · have := hmin _ hv0 ((norm_pos_sub_le x q).trans_lt hx)
      rw [add_sub_cancel] at this
      linarith
  · intro x _
    rw [fderiv_sub_const]
    exact lie_energy_nonpos hUd hM0 (fun j => (hD j).le) x
  · intro T φ hT hφ hin
    have hzero : ∀ t ∈ Set.Icc 0 T, ∀ j, φ t (vIdx j) = 0 := by
      intro t ht j
      have h0 := (hin t ht).2
      rw [fderiv_sub_const, lie_energy hUd hM0, neg_eq_zero] at h0
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hD i).le (sq_nonneg (φ t (vIdx i)))).mp h0 j (Finset.mem_univ j)
      rcases mul_eq_zero.mp hterm with h | h
      · exact absurd h (hD j).ne'
      · exact pow_eq_zero_iff two_ne_zero |>.mp h
    have hmem0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
    -- the velocity equations at the initial state: a critical point
    have hfw : ∀ j, field G M D U (φ 0) (vIdx j) = 0 := by
      intro j
      have hd : HasDerivWithinAt (fun t => φ t (vIdx j)) (field G M D U (φ 0) (vIdx j))
          (Set.Icc 0 T) 0 := by
        have := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + k) => ℝ)
          (vIdx j)).hasFDerivAt.comp_hasDerivWithinAt 0 (hφ 0 hmem0)
        exact this
      have hc : HasDerivWithinAt (fun t => φ t (vIdx j)) 0 (Set.Icc 0 T) 0 :=
        (hasDerivWithinAt_const (0 : ℝ) _ (0 : ℝ)).congr (fun s hs => hzero s hs j)
          (hzero 0 hmem0 j)
      exact (uniqueDiffOn_Icc hT 0 hmem0).eq_deriv _ hd hc
    have hcrit0 : (fderiv ℝ U (pos (φ 0))).comp G = 0 := by
      refine (comp_eq_zero_iff _ G).mpr fun j => ?_
      have h := hfw j
      rw [field_vIdx, hzero 0 hmem0 j, mul_zero, neg_zero, zero_sub, div_eq_zero_iff,
        neg_eq_zero, or_iff_left (hM0 j)] at h
      exact h
    have hq0 : pos (φ 0) = q := by
      by_contra hne
      have hv0 : pos (φ 0) - q ≠ 0 := sub_ne_zero.mpr hne
      refine hcrit _ hv0 ((norm_pos_sub_le (φ 0) q).trans_lt (hin 0 hmem0).1) ?_
      rw [add_sub_cancel]
      exact hcrit0
    apply state_ext
    · intro i
      have := congrFun hq0 i
      simp only [pos_apply] at this
      simp [this]
    · intro j; simp [hzero 0 hmem0 j]

/-- **A locally asymptotically stable rest point is a strict, isolated minimum of the
potential**: a non-minimum is ruled out by the energy, critical points accumulating at `q` by the
rest points they define, and a non-strict minimum is a nearby critical point. -/
@[powerlib_foundation] theorem strictMin_of_localAsymptoticStable (hU : ContDiff ℝ 2 U)
    (hM : ∀ j, M j ≠ 0) (hD : ∀ j, 0 ≤ D j) {q : Fin m → ℝ}
    (hLAS : LocalAsymptoticStable (field G M D U) (point q)) :
    ∃ r > 0, ∀ v : Fin m → ℝ, v ≠ 0 → ‖v‖ < r →
      U q < U (q + v) ∧ (fderiv ℝ U (q + v)).comp G ≠ 0 := by
  -- a local minimum
  obtain ⟨ε₁, hε₁, hmin⟩ : ∃ ε > 0, ∀ v : Fin m → ℝ, ‖v‖ < ε → U q ≤ U (q + v) := by
    by_contra hne
    push Not at hne
    exact not_localAsymptoticStable_of_potential_lt hU hM hD hne hLAS
  -- an isolated critical point
  obtain ⟨ε₂, hε₂, hiso⟩ : ∃ ε > 0, ∀ v : Fin m → ℝ, ‖v‖ < ε →
      (fderiv ℝ U (q + v)).comp G = 0 → v = 0 := by
    by_contra hne
    push Not at hne
    refine not_localAsymptoticStable_of_critical (fun ε hε => ?_) hLAS
    obtain ⟨v, hv, hcrit, hv0⟩ := hne ε hε
    exact ⟨v, hv0, hv, hcrit⟩
  refine ⟨min ε₁ ε₂ / 2, by positivity, fun v hv0 hv => ⟨?_, fun hcrit => ?_⟩⟩
  · have hv₁ : ‖v‖ < ε₁ := hv.trans_le (by linarith [min_le_left ε₁ ε₂])
    have hv₂ : ‖v‖ < ε₂ := hv.trans_le (by linarith [min_le_right ε₁ ε₂])
    rcases (hmin v hv₁).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hv0
      have hlm : IsLocalMin U (q + v) := by
        refine Filter.eventually_of_mem (Metric.ball_mem_nhds (q + v)
          (by positivity : (0 : ℝ) < ε₁ / 2)) fun y hy => ?_
        rw [Metric.mem_ball, dist_eq_norm] at hy
        show U (q + v) ≤ U y
        rw [← heq]
        have hy' : ‖y - q‖ < ε₁ := by
          calc ‖y - q‖ = ‖(y - (q + v)) + v‖ := by congr 1; abel
            _ ≤ ‖y - (q + v)‖ + ‖v‖ := norm_add_le _ _
            _ < ε₁ := by linarith [min_le_left ε₁ ε₂]
        have := hmin (y - q) hy'
        rwa [add_sub_cancel] at this
      refine hiso v hv₂ ?_
      rw [hlm.fderiv_eq_zero, ContinuousLinearMap.zero_comp]
  · exact hv0 (hiso v (hv.trans_le (by linarith [min_le_right ε₁ ε₂])) hcrit)

end powerlib.Dynamics.Mechanical
