import theorem.PLL.PH
import theorem.Dynamics.Basin

/-! # SRF-PLL regions of attraction (LaSalle, potential-well estimates)

Model boundary.
* System: the nonlinear SRF-PLL of `theorem/PLL/Model.lean` (ideal balanced grid of constant
  amplitude `V` and frequency, PI loop filter, VCO, constant frequency offset; no pre-filter,
  delay, PWM, current loop or saturation), continuous time, autonomous.
* Conclusions are `Dynamics.RegionOfAttraction f x_eq S` (from every initial state in `S`
  a forward solution exists and every forward solution converges to `x_eq`), derived with the
  LaSalle invariance principle of `theorem/Dynamics/Basin.lean` (no global Lipschitz bound is
  needed). Positive invariance of the estimates is proved, not assumed.

Two estimates.
1. Port-Hamiltonian energy (T-pll-ph): coordinates `(θ, η)`, field `srfField V K_p K_i δω`,
   `V, K_p, K_i > 0`, equilibrium `(0, δω/K_i)`, shifted Hamiltonian
   `H_s = V(1 − cos θ) + ½K_i(η − δω/K_i)²` with `Ḣ_s = −K_p V² sin²θ ≤ 0` everywhere.
   For `c < 2V` the potential-well piece `{|θ| < π, H_s ≤ c}` lies in the region of
   attraction; hence so does `{|θ| < π, H_s < 2V}` (T-pll-ph: "{H < 2V_g, |θ| < π}").
2. Pendulum energy (T-invariant-coordinates §2, T-gfl-multiscale §1.8): coordinates
   `(θ, ξ)`, field `xiField a b Δω` (`a = V K_p > 0`, `b = V K_i > 0`), equilibrium
   `(0, −Δω/b)`, `E = ½ θ̇² + b(1 − cos θ)` with `θ̇ = Δω − a sin θ + b ξ` written as a function
   of the state, `Ė = −a cos θ · θ̇²` (nonpositive only where `cos θ ≥ 0`). For `c < b` the
   well piece `{|θ| < π/2, E ≤ c}` lies in the region of attraction; hence so does
   `{|θ| < π/2, E < b}`.

The sublevel sets are `2π`-periodic in `θ`; each estimate uses the single potential well
around `θ = 0` (for `c` below the stated bounds the sublevel set splits into disjoint copies of
this piece around `2kπ`, and the piece used here is the one containing the equilibrium).

Source: work-sync `theory/T-pll-ph.md` §1.1–§1.2; `theory/T-invariant-coordinates.md` Part 2
"与 LaSalle / Lyapunov 分析的衔接"; `theory/T-gfl-multiscale-modeling.md` §1.8.

Family and connection conclusions. A region-of-attraction estimate (every forward solution from
a set converges to the equilibrium) is not a sentence of the library's language (flow sentences
about the origin and passivity), so no connection statement is made here: the four former domain
theorems (`srf_regionOfAttraction_hamiltonian`, `srf_regionOfAttraction_hamiltonian_lt`,
`xi_regionOfAttraction_pendulum`, `xi_regionOfAttraction_pendulum_lt`) are private
implementation evidence. Their models are the SRF members of the PI-PLL family
(`GFL.PIPLL.srf V K_p K_i δω 0`, and `srf 1 a b (−Δω) 0` in `(θ, ξ)` coordinates); the local
sentences about these equilibria are connection statements in `theorem/PLL/Model.lean`,
`theorem/PLL/Invariant.lean` and `theorem/PLL/PH.lean`. The pendulum-energy identities are
foundation.

Correction (T-invariant-coordinates, LaSalle paragraph): the note says that `V̇ ≤ 0` on
`|θ_err| < π/2` "gives a hard lower bound of the global basin". A sign condition on a strip is
not a basin estimate (the strip is not positively invariant) and "global" contradicts it. The
correct statement is the sublevel estimate above, which needs the level bound `c < V_g K_i`
(so that the well piece stays inside `|θ| < π/2` and is compact); with it the well piece of
`{E ≤ c}` lies in the region of attraction.
-/

noncomputable section
namespace powerlib.PLL
open Set Filter Matrix
open scoped Topology
open powerlib.Dynamics (State)
open powerlib.GFL (piPLLState)

@[powerlib_foundation] private lemma norm_sq_state (x : State 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]

@[powerlib_foundation] private lemma isCompact_of_bounds {S : Set (State 2)} (hS : IsClosed S)
    {M : ℝ} (hM : ∀ x ∈ S, x 0 ^ 2 + x 1 ^ 2 ≤ M) : IsCompact S := by
  refine Metric.isCompact_of_isClosed_isBounded hS ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt (max M 0), fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply Real.le_sqrt_of_sq_le
  rw [norm_sq_state]
  exact (hM x hx).trans (le_max_left _ _)

@[powerlib_foundation] private lemma contDiff_coord (i : Fin 2) :
    ContDiff ℝ 1 (fun x : State 2 => x i) :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : State 2 →L[ℝ] ℝ).contDiff

@[powerlib_foundation] private lemma fderiv_coord (i : Fin 2) (x v : State 2) :
    fderiv ℝ (fun y : State 2 => y i) x v = v i := by
  have h : HasFDerivAt (fun y : State 2 => y i)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : State 2 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : State 2 →L[ℝ] ℝ).hasFDerivAt
  rw [h.fderiv]
  rfl

/-! ## 1. Port-Hamiltonian energy -/

@[powerlib_foundation] private lemma contDiff_pllHamiltonian (V Ki ηs : ℝ) :
    ContDiff ℝ 1 (pllHamiltonian V Ki ηs) := by
  unfold pllHamiltonian
  exact (contDiff_const.mul (contDiff_const.sub (Real.contDiff_cos.comp (contDiff_coord 0)))).add
    (contDiff_const.mul (((contDiff_coord 1).sub contDiff_const).pow 2))

/-- For `c < 2V` the potential-well piece `{|θ| < π, H_s ≤ c}` of the shifted
port-Hamiltonian energy lies in the region of attraction of the locked equilibrium. 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem srf_regionOfAttraction_hamiltonian {V Kp Ki : ℝ} (hV : 0 < V)
    (hKp : 0 < Kp) (hKi : 0 < Ki) (δω : ℝ) {c : ℝ} (hc : c < 2 * V) :
    Dynamics.RegionOfAttraction (srfField V Kp Ki δω) (piPLLState 0 (δω / Ki))
      {x | |x 0| < Real.pi ∧ pllHamiltonian V Ki (δω / Ki) x ≤ c} := by
  set H := pllHamiltonian V Ki (δω / Ki)
  set W : Set (State 2) := {x | |x 0| < Real.pi}
  have hW : IsOpen W := isOpen_lt (continuous_abs.comp (contDiff_coord 0).continuous)
    continuous_const
  have hLie : ∀ x, fderiv ℝ H x (srfField V Kp Ki δω x) = -(Kp * srfPD V (x 0) ^ 2) :=
    pllHamiltonian_shifted_lie hKp.le hKi.ne' δω
  -- the sublevel piece equals a closed set
  have hset : {x ∈ W | H x ≤ c} = {x : State 2 | |x 0| ≤ Real.pi ∧ H x ≤ c} := by
    ext x
    simp only [mem_ofPred_eq, W]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_le_of_ne h1 fun heq => ?_, h2⟩
      have hcos : Real.cos (x 0) = -1 := by
        rcases abs_eq (Real.pi_pos.le) |>.mp heq with h | h <;> rw [h] <;> simp
      have : 2 * V ≤ H x := by
        simp only [H, pllHamiltonian, hcos]
        nlinarith [sq_nonneg (x 1 - δω / Ki)]
      linarith
  have hcompact : IsCompact {x ∈ W | H x ≤ c} := by
    rw [hset]
    refine isCompact_of_bounds (M := Real.pi ^ 2 + 2 * (2 * |c| / Ki + (δω / Ki) ^ 2)) ?_ ?_
    · exact (isClosed_le (continuous_abs.comp (contDiff_coord 0).continuous) continuous_const).inter
        (isClosed_le (contDiff_pllHamiltonian V Ki _).continuous continuous_const)
    · rintro x ⟨h1, h2⟩
      have hθ : x 0 ^ 2 ≤ Real.pi ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hcos : 0 ≤ V * (1 - Real.cos (x 0)) := by
        have := Real.cos_le_one (x 0); nlinarith
      have hη : (x 1 - δω / Ki) ^ 2 ≤ 2 * |c| / Ki := by
        simp only [H, pllHamiltonian] at h2
        rw [le_div_iff₀ hKi]
        nlinarith [le_abs_self c]
      nlinarith [sq_nonneg (x 1 - 2 * (δω / Ki))]
  refine Dynamics.regionOfAttraction_of_lasalle_sublevel hW (contDiff_srfField V Kp Ki δω)
    (contDiff_pllHamiltonian V Ki _) (fun x _ => by rw [hLie]; nlinarith [sq_nonneg (srfPD V (x 0))])
    hcompact ?_
  refine Dynamics.lasalle_condition_of_lieDeriv (contDiff_srfField V Kp Ki δω) (contDiff_coord 0)
    (fun x hx => ?_) (fun x hx hd => ?_)
  · -- on the zero set of `Ḣ_s` inside the well, `θ = 0`
    rw [Dynamics.lieDerivZeroSet_def] at hx
    obtain ⟨⟨hxW, -⟩, hz⟩ := hx
    rw [hLie] at hz
    have hs : Real.sin (x 0) = 0 := by
      have : srfPD V (x 0) = 0 := by
        have := mul_eq_zero.mp (neg_eq_zero.mp hz)
        rcases this with h | h
        · exact absurd h hKp.ne'
        · exact pow_eq_zero_iff two_ne_zero |>.mp h
      simp only [srfPD, neg_eq_zero, mul_eq_zero] at this
      exact this.resolve_left hV.ne'
    exact (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp hxW).1 (abs_lt.mp hxW).2).mp hs
  · rw [Dynamics.lieDerivZeroSet_def] at hx
    obtain ⟨⟨hxW, -⟩, hz⟩ := hx
    rw [hLie] at hz
    have hθ : x 0 = 0 := by
      have hs : Real.sin (x 0) = 0 := by
        have : srfPD V (x 0) = 0 := by
          have := mul_eq_zero.mp (neg_eq_zero.mp hz)
          rcases this with h | h
          · exact absurd h hKp.ne'
          · exact pow_eq_zero_iff two_ne_zero |>.mp h
        simp only [srfPD, neg_eq_zero, mul_eq_zero] at this
        exact this.resolve_left hV.ne'
      exact (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp hxW).1 (abs_lt.mp hxW).2).mp hs
    rw [fderiv_coord, srfField_apply_zero, hθ, Real.sin_zero] at hd
    rw [GFL.state_two_ext_iff]
    refine ⟨by simp [piPLLState, hθ], ?_⟩
    simp only [GFL.piPLLState_apply_one]
    field_simp
    linarith

/-- T-pll-ph basin: every state with `|θ| < π` and `H_s < 2V` (below the saddle level) is in
the region of attraction of the locked equilibrium. 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem srf_regionOfAttraction_hamiltonian_lt {V Kp Ki : ℝ} (hV : 0 < V)
    (hKp : 0 < Kp) (hKi : 0 < Ki) (δω : ℝ) :
    Dynamics.RegionOfAttraction (srfField V Kp Ki δω) (piPLLState 0 (δω / Ki))
      {x | |x 0| < Real.pi ∧ pllHamiltonian V Ki (δω / Ki) x < 2 * V} := by
  intro x₀ hx₀
  exact srf_regionOfAttraction_hamiltonian hV hKp hKi δω hx₀.2 x₀ ⟨hx₀.1, le_rfl⟩

/-! ## 2. Pendulum energy in `(θ, ξ)` coordinates -/

/-- Frequency error `θ̇ = Δω − a sin θ + b ξ` as a function of the state. -/
def xiRate (a b Δω : ℝ) (x : State 2) : ℝ := Δω - a * Real.sin (x 0) + b * x 1

/-- Pendulum energy `E = ½ θ̇² + b(1 − cos θ)`. -/
def pendulumEnergy (a b Δω : ℝ) (x : State 2) : ℝ :=
  xiRate a b Δω x ^ 2 / 2 + b * (1 - Real.cos (x 0))

@[powerlib_foundation] private lemma contDiff_xiRate (a b Δω : ℝ) : ContDiff ℝ 1 (xiRate a b Δω) := by
  unfold xiRate
  exact (contDiff_const.sub (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_coord 0)))).add
    (contDiff_const.mul (contDiff_coord 1))

@[powerlib_foundation] private lemma hasFDerivAt_xiRate (a b Δω : ℝ) (x : State 2) :
    HasFDerivAt (xiRate a b Δω)
      ((-(a * Real.cos (x 0))) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ) +
        b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ)) x := by
  have h0 : HasFDerivAt (fun z : State 2 => z 0)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun z : State 2 => z 1)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).hasFDerivAt
  have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
  have h := ((hs.const_mul a).const_sub Δω).add (h1.const_mul b)
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

/-- Lie derivative of the pendulum energy: `Ė = −a cos θ · θ̇²`. -/
@[powerlib_foundation] theorem pendulumEnergy_lie (a b Δω : ℝ) (x : State 2) :
    fderiv ℝ (pendulumEnergy a b Δω) x (xiField a b Δω x) =
      -(a * Real.cos (x 0) * xiRate a b Δω x ^ 2) := by
  have h0 : HasFDerivAt (fun z : State 2 => z 0)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).hasFDerivAt
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have hE := (((hasFDerivAt_xiRate a b Δω x).pow 2).const_mul (1 / 2 : ℝ)).add
    ((hc.const_sub 1).const_mul b)
  have hE' : HasFDerivAt (pendulumEnergy a b Δω) _ x :=
    hE.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
      simp only [pendulumEnergy, Pi.add_apply, Function.comp_apply]; ring)
  rw [hE'.fderiv]
  simp [xiField, xiRate]
  ring

@[powerlib_foundation] private lemma contDiff_pendulumEnergy (a b Δω : ℝ) :
    ContDiff ℝ 1 (pendulumEnergy a b Δω) := by
  unfold pendulumEnergy
  exact (((contDiff_xiRate a b Δω).pow 2).div_const 2).add
    (contDiff_const.mul (contDiff_const.sub (Real.contDiff_cos.comp (contDiff_coord 0))))

@[powerlib_foundation] private lemma contDiff_xiField (a b Δω : ℝ) : ContDiff ℝ 1 (xiField a b Δω) := by
  rw [xiField_eq_srfField]; exact contDiff_srfField _ _ _ _

/-- For `a, b > 0` and `c < b` the well piece `{|θ| < π/2, E ≤ c}` of the pendulum energy lies
in the region of attraction of `(0, −Δω/b)`. 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem xi_regionOfAttraction_pendulum {a b Δω : ℝ} (ha : 0 < a) (hb : 0 < b)
    {c : ℝ} (hc : c < b) :
    Dynamics.RegionOfAttraction (xiField a b Δω) (piPLLState 0 (-Δω / b))
      {x | |x 0| < Real.pi / 2 ∧ pendulumEnergy a b Δω x ≤ c} := by
  set E := pendulumEnergy a b Δω
  set W : Set (State 2) := {x | |x 0| < Real.pi / 2}
  have hW : IsOpen W := isOpen_lt (continuous_abs.comp (contDiff_coord 0).continuous)
    continuous_const
  have hcosW : ∀ x ∈ W, 0 < Real.cos (x 0) := fun x hx =>
    Real.cos_pos_of_mem_Ioo ⟨(abs_lt.mp hx).1, (abs_lt.mp hx).2⟩
  have hset : {x ∈ W | E x ≤ c} = {x : State 2 | |x 0| ≤ Real.pi / 2 ∧ E x ≤ c} := by
    ext x
    simp only [mem_ofPred_eq, W]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_le_of_ne h1 fun heq => ?_, h2⟩
      have hcos : Real.cos (x 0) = 0 := by
        rcases abs_eq (by positivity : (0 : ℝ) ≤ Real.pi / 2) |>.mp heq with h | h <;>
          rw [h] <;> simp
      have : b ≤ E x := by
        simp only [E, pendulumEnergy, hcos]
        nlinarith [sq_nonneg (xiRate a b Δω x)]
      linarith
  have hcompact : IsCompact {x ∈ W | E x ≤ c} := by
    rw [hset]
    refine isCompact_of_bounds
      (M := Real.pi ^ 2 + ((Real.sqrt (2 * |c|) + |Δω| + a) / b) ^ 2) ?_ ?_
    · exact (isClosed_le (continuous_abs.comp (contDiff_coord 0).continuous) continuous_const).inter
        (isClosed_le (contDiff_pendulumEnergy a b Δω).continuous continuous_const)
    · rintro x ⟨h1, h2⟩
      have hθ : x 0 ^ 2 ≤ Real.pi ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans (by linarith [Real.pi_pos])) 2
      have hcos1 : 0 ≤ b * (1 - Real.cos (x 0)) := by
        have := Real.cos_le_one (x 0); nlinarith
      have hw : xiRate a b Δω x ^ 2 ≤ 2 * |c| := by
        simp only [E, pendulumEnergy] at h2
        nlinarith [le_abs_self c]
      have hw' : |xiRate a b Δω x| ≤ Real.sqrt (2 * |c|) :=
        Real.abs_le_sqrt hw
      have hξ : |x 1| ≤ (Real.sqrt (2 * |c|) + |Δω| + a) / b := by
        rw [le_div_iff₀ hb]
        have hrel : b * x 1 = xiRate a b Δω x - Δω + a * Real.sin (x 0) := by
          simp only [xiRate]; ring
        have hsin : |a * Real.sin (x 0)| ≤ a := by
          rw [abs_mul, abs_of_pos ha]
          exact mul_le_of_le_one_right ha.le (Real.abs_sin_le_one _)
        calc |x 1| * b = |b * x 1| := by rw [abs_mul, abs_of_pos hb, mul_comm]
          _ = |xiRate a b Δω x - Δω + a * Real.sin (x 0)| := by rw [hrel]
          _ ≤ |xiRate a b Δω x| + |Δω| + |a * Real.sin (x 0)| := by
              calc _ ≤ |xiRate a b Δω x - Δω| + |a * Real.sin (x 0)| := abs_add_le _ _
                _ ≤ |xiRate a b Δω x| + |Δω| + |a * Real.sin (x 0)| := by
                    gcongr; exact abs_sub _ _
          _ ≤ Real.sqrt (2 * |c|) + |Δω| + a := by linarith
      have : x 1 ^ 2 ≤ ((Real.sqrt (2 * |c|) + |Δω| + a) / b) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hξ 2
      linarith
  refine Dynamics.regionOfAttraction_of_lasalle_sublevel hW (contDiff_xiField a b Δω)
    (contDiff_pendulumEnergy a b Δω) (fun x hx => ?_) hcompact ?_
  · rw [pendulumEnergy_lie]
    have := mul_nonneg (mul_pos ha (hcosW x hx)).le (sq_nonneg (xiRate a b Δω x))
    linarith
  -- on the zero set of `Ė` inside the well, `θ̇ = 0`; then `θ = 0` and `ξ = −Δω/b`
  have hzero : ∀ x ∈ Dynamics.LieDerivZeroSet (xiField a b Δω) E {x ∈ W | E x ≤ c},
      xiRate a b Δω x = 0 := by
    intro x hx
    rw [Dynamics.lieDerivZeroSet_def] at hx
    obtain ⟨⟨hxW, -⟩, hz⟩ := hx
    rw [pendulumEnergy_lie] at hz
    have hpos : 0 < a * Real.cos (x 0) := mul_pos ha (hcosW x hxW)
    have := mul_eq_zero.mp (neg_eq_zero.mp hz)
    rcases this with h | h
    · exact absurd h hpos.ne'
    · exact pow_eq_zero_iff two_ne_zero |>.mp h
  refine Dynamics.lasalle_condition_of_lieDeriv (contDiff_xiField a b Δω) (contDiff_xiRate a b Δω)
    hzero (fun x hx hd => ?_)
  have hw := hzero x hx
  rw [Dynamics.lieDerivZeroSet_def] at hx
  obtain ⟨⟨hxW, -⟩, -⟩ := hx
  have hxW' : |x 0| < Real.pi / 2 := hxW
  rw [(hasFDerivAt_xiRate a b Δω x).fderiv] at hd
  simp [xiField] at hd
  have hw' : Δω - a * Real.sin (x 0) + b * x 1 = 0 := hw
  have hs : Real.sin (x 0) = 0 := by
    have : -(a * Real.cos (x 0) * (Δω - a * Real.sin (x 0) + b * x 1)) -
        b * Real.sin (x 0) = 0 := by linarith
    rw [hw', mul_zero, neg_zero, zero_sub, neg_eq_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hb.ne'
  have hθ : x 0 = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [(abs_lt.mp hxW').1, Real.pi_pos])
    (by linarith [(abs_lt.mp hxW').2, Real.pi_pos])).mp hs
  rw [hθ, Real.sin_zero, mul_zero, sub_zero] at hw'
  rw [GFL.state_two_ext_iff]
  refine ⟨by simp [piPLLState, hθ], ?_⟩
  simp only [GFL.piPLLState_apply_one]
  field_simp
  linarith

/-- The pendulum-energy estimate below the level `b = V K_i`. 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem xi_regionOfAttraction_pendulum_lt {a b Δω : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    Dynamics.RegionOfAttraction (xiField a b Δω) (piPLLState 0 (-Δω / b))
      {x | |x 0| < Real.pi / 2 ∧ pendulumEnergy a b Δω x < b} := by
  intro x₀ hx₀
  exact xi_regionOfAttraction_pendulum ha hb hx₀.2 x₀ ⟨hx₀.1, le_rfl⟩

end powerlib.PLL
