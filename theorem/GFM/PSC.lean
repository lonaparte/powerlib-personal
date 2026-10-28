import theorem.NormalForm.Scalar
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.SpecialFunctions.Elementary
import theorem.SpecialFunctions.Sinusoid
import theorem.Spectral.Equilibrium

/-! # Power-synchronization control (PSC): quasi-static one-dimensional model and algebra

Model boundary.
* Quasi-static PSC: the converter is a voltage source `V ∠ θ` behind the line reactance
  `X = ω₁ L` to an infinite bus `V_g ∠ θ_g`, `θ_g = ω₁ t + θ_{g0}`; the line current is
  quasi-static (no inductor dynamics), so `P = P_max sin(θ − θ_g)`, `P_max = V V_g / (ω₁ L)`.
* Synchronization law `θ̇ = ω₁ + K_p (P* − P)` with constant `P*`; in the grid-angle frame
  `δ = θ − θ_g` this is the one-dimensional autonomous field `δ̇ = K_p (P* − P_max sin δ)`
  (state `δ : Dynamics.State 1`, continuous time).
* Excluded: active-resistance damping loop and inductor dynamics (the three-pole closed loop of
  T-power-synchronization-control §1.4), DC-link loop, current limiting / PLL backup, delay, PWM.
* Power is export-positive (GFM family exception).

Source: work-sync `theory/T-power-synchronization-control.md` §1.1–§1.3, §1.10;
`theory/T-vsg-control.md` §1.7; `theory/T-gfm-control.md` §1.4.

Results.
* Equilibria `⇔ |P*| ≤ P_max`; equilibria with `cos δ₀ > 0` are locally exponentially stable and
  with `cos δ₀ < 0` unstable (`K_p, P_max > 0`), via the scalar linearization wrappers of
  `theorem/NormalForm/Scalar.lean`; `absoluteAngle_iff` shows that the original law in the
  absolute angle `θ` is equivalent, pointwise in time, to the `δ`-equation.
* Algebra (foundation): the steady-state active power, the converter-side reactive power and
  the grid-side received reactive power from `S̄ = V̄ Ī*` (`Network.converterSide_power`,
  `Network.gridSide_power`, `theorem/Network/PowerFlow.lean`); the active-resistance high-pass
  `R_a (H(s) − 1) = −R_a s/(s + ω_b)`; PSC as pure droop with `D = 1/K_p`.

Family and connection conclusions.
`PSC.family`: a complete system (`PSC.Model`) is a parameter
set with a selected angle `δ*`, read as the scalar field translated so that `δ*` is the origin
(`Flow.Property.holds_shift_iff`).  Static requirements: balance `P_max sin δ* = P*`, a negative
slope `K_p P_max cos δ* > 0` (i.e. `d/dδ [K_p (P* − P_max sin δ)] < 0` at `δ*`), or a positive
slope `K_p P_max cos δ* < 0`.  The local sentences translate into balance and a negative slope,
instability into balance and a positive slope, passivity into nothing (exact), the remaining
sentences into the whole, inconsistent, language.  `PSC.chain_le_semantics` proves soundness;
`PSC.exact_locallyExponentiallyStable` proves the local exponential translation exact (converse
linearization of the scalar field, `Spectral.exactUnder_les_of_jacobian`); the
stability theorems `locallyExponentiallyStable`, `unstable`, `locallyExponentiallyStable_arcsin`
and `unstable_pi_sub_arcsin` are connection statements (members of the denotations), and
`field_eq_zero_iff`, `exists_equilibrium_iff` are static evidence on the model. The instability
translation is not exact (`PSC.not_exact_unstable`): instability is the failure of Lyapunov
stability, so an unbalanced angle (`PSC.offEquilibrium`) is unstable
(`PSC.offEquilibrium_mem_den_unstable`, `Dynamics.unstable_of_ne_zero`).
The local asymptotic translation is exact (`PSC.exact_locallyAsymptoticallyStable`, by
`Spectral.exact_of_equilibrium`), although the linearization does not decide the degenerate slope
`K_p P_max cos δ* = 0`: there the model's structure does. A vanishing gain or curve (`K_p = 0`,
or `P_max = P* = 0`) makes every state an equilibrium
(`Dynamics.not_localAsymptoticStable_of_equilibria`), and at a balanced fold angle
(`cos δ* = 0`) the field is `k (1 − cos(δ − δ*))`, `k = K_p P_max sin δ*` (`PSC.rhs_eq_fold`), of
one sign on both sides, so the coordinate `k δ` never decreases
(`Dynamics.not_localAsymptoticStable_of_lie_nonpos`). The Lyapunov translation is not exact
(`PSC.not_exact_lyapunovStable`: the frozen loop `PSC.frozen`, `K_p = 0`, is Lyapunov stable,
`PSC.frozen_mem_den_lyapunovStable`); its denotation is `PSC.mem_den_lyapunovStable_iff`: a balanced
angle with a negative slope, or a vanishing scalar field (the fold angle is unstable by Chetaev's
theorem, `Dynamics.unstable_of_chetaev`).

Corrections.
* T-power-synchronization-control §1.1 calls `Q₀ = (V V_g cos θ₀ − V_g²)/(ω₁ L)` the reactive
  power exported by the converter; that expression is the reactive power *received at the grid
  bus*.  The converter-side output reactive power is `(V² − V V_g cos θ₀)/(ω₁ L)`
  (`Network.converterSide_power`, `Network.gridSide_power`).
* The same section declares the current IN-positive (into the converter) while the line equation
  `L dĪ/dt = V̄_conv − V̄_g − jω₁ L Ī` makes `Ī` flow from the converter to the grid; here `Ī` is
  the converter-to-grid (export) current.
-/

noncomputable section
namespace powerlib.GFM
open Set
open powerlib.Dynamics (State)
open powerlib.NormalForm (lift embed)

/-- Parameters of quasi-static PSC: gain `K_p`, set-point `P*`, maximum power `P_max`. -/
structure PSC where
  Kp : ℝ
  Pstar : ℝ
  Pmax : ℝ

namespace PSC

variable (c : PSC)

/-- Scalar right-hand side `K_p (P* − P_max sin δ)`. -/
def rhs (δ : ℝ) : ℝ := c.Kp * (c.Pstar - c.Pmax * Real.sin δ)

/-- The one-dimensional PSC field on `State 1`. -/
def field : State 1 → State 1 := lift c.rhs

@[tmio M, powerlib_foundation] theorem rhs_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k c.rhs := by
  unfold rhs; fun_prop

@[powerlib_foundation] theorem hasDerivAt_rhs (δ : ℝ) :
    HasDerivAt c.rhs (-(c.Kp * c.Pmax * Real.cos δ)) δ := by
  unfold rhs
  have h := ((Real.hasDerivAt_sin δ).const_mul c.Pmax).const_sub c.Pstar |>.const_mul c.Kp
  convert h using 1
  ring

/-- Equilibria: `δ₀` is an equilibrium iff `P_max sin δ₀ = P*` (`K_p ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_iff (hK : c.Kp ≠ 0) (δ : ℝ) :
    c.field (embed δ) = 0 ↔ c.Pmax * Real.sin δ = c.Pstar := by
  rw [field, NormalForm.lift_eq_zero_iff, rhs, mul_eq_zero, or_iff_right hK, sub_eq_zero, eq_comm]

/-- Equilibria exist iff `|P*| ≤ P_max` (`K_p ≠ 0`, `P_max > 0`).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem exists_equilibrium_iff (hK : c.Kp ≠ 0) (hP : 0 < c.Pmax) :
    (∃ x, c.field x = 0) ↔ |c.Pstar| ≤ c.Pmax := by
  rw [← SpecialFunctions.exists_sinusoid_zero_iff (φ := 0) hP]
  constructor
  · rintro ⟨x, hx⟩
    rw [← NormalForm.embed_coord x, c.field_eq_zero_iff hK] at hx
    exact ⟨x 0, by rw [add_zero, hx, sub_self]⟩
  · rintro ⟨δ, hδ⟩
    exact ⟨embed δ, (c.field_eq_zero_iff hK δ).mpr (by rw [add_zero] at hδ; linarith)⟩

/-! ## The PSC family -/

/-- A quasi-static PSC model read about a selected angle `δ*`. -/
structure Model where
  /-- The parameters. -/
  c : PSC
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The one-dimensional field translated so that the selected angle is the origin. -/
def Model.field (m : Model) (z : State 1) : State 1 := m.c.field (z + embed m.δ)

/-- Static requirements on PSC models. -/
inductive Requirement
  /-- Power balance at the selected angle: `P_max sin δ* = P*`. -/
  | balanced
  /-- Negative slope of the scalar field: `K_p P_max cos δ* > 0`. -/
  | stableSlope
  /-- Positive slope of the scalar field: `K_p P_max cos δ* < 0`. -/
  | unstableSlope

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.c.Pmax * Real.sin m.δ = m.c.Pstar
  | .stableSlope => 0 < m.c.Kp * m.c.Pmax * Real.cos m.δ
  | .unstableSlope => m.c.Kp * m.c.Pmax * Real.cos m.δ < 0

/-- The translation of the sentences: the local ones into balance and a negative slope,
instability into balance and a positive slope, passivity into nothing; the global sentences,
decay rates, sampled contraction and conservation into the whole language, which no model meets
(unavailable translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.balanced, .stableSlope}
  | .flow .unstable => {.balanced, .unstableSlope}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The quasi-static PSC family. -/
def family : Family Model Requirement 1 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.c.field (embed m.δ) :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.c.field) (pt := fun m => embed m.δ)
    family_isAutonomous

private theorem les_of {m : Model} (hb : Meets m .balanced) (hs : Meets m .stableSlope) :
    LocallyExponentiallyStable m.c.field (embed m.δ) := by
  have hb' : m.c.Pmax * Real.sin m.δ = m.c.Pstar := hb
  have hs' : 0 < m.c.Kp * m.c.Pmax * Real.cos m.δ := hs
  apply NormalForm.lift_locallyExponentiallyStable m.c.rhs_contDiff
  · simp [rhs, hb']
  · rw [(m.c.hasDerivAt_rhs m.δ).deriv]
    linarith

private theorem unstable_of {m : Model} (hb : Meets m .balanced) (hs : Meets m .unstableSlope) :
    Unstable m.c.field (embed m.δ) := by
  have hb' : m.c.Pmax * Real.sin m.δ = m.c.Pstar := hb
  have hs' : m.c.Kp * m.c.Pmax * Real.cos m.δ < 0 := hs
  apply NormalForm.lift_unstable m.c.rhs_contDiff
  · simp [rhs, hb']
  · rw [(m.c.hasDerivAt_rhs m.δ).deriv]
    linarith

/-- The whole requirement language is inconsistent: the slope cannot be both negative and
positive. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .stableSlope .unstableSlope fun m h1 h2 => ?_
  have h1 : 0 < m.c.Kp * m.c.Pmax * Real.cos m.δ := h1
  have h2 : m.c.Kp * m.c.Pmax * Real.cos m.δ < 0 := h2
  linarith

/-- Every translation of the PSC family is sound: the scalar linearization at the selected angle
(the slope `−K_p P_max cos δ*`) proves the local sentences and instability, and passivity holds
without requirement. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same (Rs := {.balanced, .stableSlope})
    (Ru := {.balanced, .unstableSlope}) (fun s => ?_) realize_univ (fun m hm => ?_)
    (fun m hm => ?_) family_isAutonomous.den_passive
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  · rw [TMIO.mem_realize] at hm
    exact mem_den_flow_iff.mpr (les_of (hm .balanced (by simp)) (hm .stableSlope (by simp)))
  · rw [TMIO.mem_realize] at hm
    exact mem_den_flow_iff.mpr (unstable_of (hm .balanced (by simp)) (hm .unstableSlope (by simp)))

/-- Passivity is translated exactly: a system without ports is passive. -/
@[tmio TM, powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- The local exponential translation is exact: a PSC model is locally exponentially stable at
`δ*` exactly when the angle is balanced (`P_max sin δ* = P*`) with a negative slope
(`K_p P_max cos δ* > 0`). Converse linearization of the scalar field
`δ̇ = K_p (P* − P_max sin δ)`: local exponential stability forces a zero with negative slope. -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.exact_of_exactUnder_empty (Spectral.exactUnder_les_of_jacobian
    (fun m P => mem_den_flow_iff) ∅ (fun m => !![-(m.c.Kp * m.c.Pmax * Real.cos m.δ)])
    (fun m _ hm => ?_) (fun m _ => NormalForm.lift_contDiff m.c.rhs_contDiff)
    (fun m _ => (NormalForm.hasFDerivAt_lift (by simpa using m.c.hasDerivAt_rhs m.δ)).fderiv)
    fun m _ heq hH => ?_)
  · rw [TMIO.mem_realize] at hm
    exact mem_den_flow_iff.mpr (les_of (hm .balanced (by simp [family, translate]))
      (hm .stableSlope (by simp [family, translate])))
  rw [field, NormalForm.lift_eq_zero_iff, rhs] at heq
  rw [Linear.isHurwitz_one_iff, neg_lt_zero] at hH
  have hK : m.c.Kp ≠ 0 := by
    rintro h
    rw [h, zero_mul, zero_mul] at hH
    exact lt_irrefl 0 hH
  have hb : m.c.Pmax * Real.sin m.δ = m.c.Pstar := by
    have := (mul_eq_zero.mp heq).resolve_left hK
    linarith
  rw [TMIO.mem_realize]
  rintro q (rfl | rfl)
  · exact hb
  · exact hH

/-- An equilibrium with `cos δ₀ > 0` is locally exponentially stable (`K_p, P_max > 0`). -/
@[tmio TM, powerlib_domain] theorem locallyExponentiallyStable (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    {δ₀ : ℝ} (heq : c.Pmax * Real.sin δ₀ = c.Pstar) (hcos : 0 < Real.cos δ₀) :
    connection% (Model.mk c δ₀ ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (les_of (m := ⟨c, δ₀⟩) heq (by
    show 0 < c.Kp * c.Pmax * Real.cos δ₀
    positivity))

/-- An equilibrium with `cos δ₀ < 0` is unstable (`K_p, P_max > 0`). -/
@[tmio TM, powerlib_domain] theorem unstable (hK : 0 < c.Kp) (hP : 0 < c.Pmax) {δ₀ : ℝ}
    (heq : c.Pmax * Real.sin δ₀ = c.Pstar) (hcos : Real.cos δ₀ < 0) :
    connection% (Model.mk c δ₀ ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (unstable_of (m := ⟨c, δ₀⟩) heq
    (mul_neg_of_pos_of_neg (mul_pos hK hP) hcos))

/-- The loading angle `arcsin(P*/P_max)` is locally exponentially stable when
`|P*| < P_max`. -/
@[tmio TM, powerlib_domain] theorem locallyExponentiallyStable_arcsin (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    (h : |c.Pstar| < c.Pmax) :
    connection% (Model.mk c (Real.arcsin (c.Pstar / c.Pmax)) ∈
      family.den (.flow .locallyExponentiallyStable)) := by
  exact c.locallyExponentiallyStable hK hP (SpecialFunctions.mul_sin_arcsin_div h.le hP)
    (SpecialFunctions.cos_arcsin_div_pos h hP)

/-- The second equilibrium `π − arcsin(P*/P_max)` is unstable when `|P*| < P_max`. -/
@[tmio TM, powerlib_domain] theorem unstable_pi_sub_arcsin (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    (h : |c.Pstar| < c.Pmax) :
    connection% (Model.mk c (Real.pi - Real.arcsin (c.Pstar / c.Pmax)) ∈
      family.den (.flow .unstable)) := by
  exact c.unstable hK hP (SpecialFunctions.mul_sin_pi_sub_arcsin_div h.le hP)
    (SpecialFunctions.cos_pi_sub_arcsin_div_neg h hP)

/-- Bridge to the original law in the absolute angle `θ` against the grid angle
`θ_g(t) = ω₁ t + θ_{g0}`: `θ̇ = ω₁ + K_p (P* − P_max sin(θ − θ_g))` at time `t` iff the relative
angle `δ = θ − θ_g` satisfies `δ̇ = K_p (P* − P_max sin δ)` at `t` (the scalar field `rhs` that
`field` lifts). -/
@[powerlib_foundation] theorem absoluteAngle_iff (ω₁ θg0 : ℝ) (θ : ℝ → ℝ) (t : ℝ) :
    HasDerivAt θ (ω₁ + c.Kp * (c.Pstar - c.Pmax * Real.sin (θ t - (ω₁ * t + θg0)))) t ↔
      HasDerivAt (fun s => θ s - (ω₁ * s + θg0)) (c.rhs (θ t - (ω₁ * t + θg0))) t := by
  have hg : HasDerivAt (fun s => ω₁ * s + θg0) ω₁ t := by
    simpa using ((hasDerivAt_id t).const_mul ω₁).add_const θg0
  constructor
  · intro h
    convert h.sub hg using 1
    simp only [rhs]
    ring
  · intro h
    convert h.add hg using 1
    · funext s; simp only [Pi.add_apply]; ring
    · simp only [rhs]; ring

/-! ### The local asymptotic and Lyapunov translations -/

/-- At a balanced fold angle (`cos δ₀ = 0`) the scalar field is `k (1 − cos(δ − δ₀))` with
`k = K_p P_max sin δ₀`: it has one sign on both sides of `δ₀`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem rhs_eq_fold {δ₀ : ℝ} (hb : c.Pmax * Real.sin δ₀ = c.Pstar)
    (hcos : Real.cos δ₀ = 0) (z : ℝ) :
    c.rhs z = c.Kp * c.Pmax * Real.sin δ₀ * (1 - Real.cos (z - δ₀)) := by
  have hs : Real.sin z = Real.sin δ₀ * Real.cos (z - δ₀) := by
    have h := Real.sin_add δ₀ (z - δ₀)
    rw [add_sub_cancel] at h
    rw [h, hcos]
    ring
  rw [rhs, ← hb, hs]
  ring

private theorem hasFDerivAt_coord (k : ℝ) (z : State 1) :
    HasFDerivAt (fun y : State 1 => k * y 0) (k • NormalForm.coordCLM) z :=
  (NormalForm.coordCLM.hasFDerivAt (x := z)).const_mul k

private theorem fderiv_coord_apply (k : ℝ) (z v : State 1) :
    fderiv ℝ (fun y : State 1 => k * y 0) z v = k * v 0 := by
  rw [(hasFDerivAt_coord k z).fderiv]
  rfl

private theorem norm_embed_add_sub (δ₀ s : ℝ) : ‖embed (δ₀ + s) - embed δ₀‖ = |s| := by
  rw [NormalForm.embed_sub, NormalForm.norm_embed, add_sub_cancel_left]

/-- With a vanishing scalar field every state is an equilibrium: no point is locally
asymptotically stable. -/
private theorem not_las_of_rhs_zero {c : PSC} (h : ∀ z, c.rhs z = 0) (δ₀ : ℝ) :
    ¬ LocalAsymptoticStable c.field (embed δ₀) := by
  refine Dynamics.not_localAsymptoticStable_of_equilibria fun ε hε =>
    ⟨embed (δ₀ + ε / 2), ?_, ?_, ?_⟩
  · rw [Ne, NormalForm.embed_eq_iff]
    linarith
  · rw [norm_embed_add_sub, abs_of_pos (by linarith)]
    linarith
  · rw [field, NormalForm.lift_embed, h, NormalForm.embed_zero]

/-- A balanced fold angle with `K_p P_max ≠ 0` is not locally asymptotically stable: the
coordinate `−k δ` never increases along the field and is below its value at `δ₀` on one side. -/
private theorem not_las_fold {c : PSC} {δ₀ : ℝ} (hb : c.Pmax * Real.sin δ₀ = c.Pstar)
    (hcos : Real.cos δ₀ = 0) (hk : c.Kp * c.Pmax ≠ 0) :
    ¬ LocalAsymptoticStable c.field (embed δ₀) := by
  set k := c.Kp * c.Pmax * Real.sin δ₀ with hkdef
  have hk0 : k ≠ 0 := mul_ne_zero hk (SpecialFunctions.sin_ne_zero_of_cos hcos)
  refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := fun z : State 1 => -k * z 0)
    (ρ := 1) (NormalForm.lift_contDiff c.rhs_contDiff)
    (fun z => (hasFDerivAt_coord (-k) z).differentiableAt) one_pos (fun z _ => ?_)
    (fun ε hε => ?_)
  · rw [fderiv_coord_apply, field, NormalForm.lift_apply, c.rhs_eq_fold hb hcos]
    have := Real.cos_le_one (z 0 - δ₀)
    nlinarith [sq_nonneg k]
  · rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · refine ⟨embed (δ₀ + -(ε / 2)), ?_, ?_⟩
      · rw [norm_embed_add_sub, abs_neg, abs_of_pos (by linarith)]
        linarith
      · simp only [NormalForm.embed_apply]
        nlinarith
    · refine ⟨embed (δ₀ + ε / 2), ?_, ?_⟩
      · rw [norm_embed_add_sub, abs_of_pos (by linarith)]
        linarith
      · simp only [NormalForm.embed_apply]
        nlinarith

/-- A balanced fold angle with `K_p P_max ≠ 0` is unstable (Chetaev's theorem with the
coordinate `k (δ − δ₀)`, which grows at the rate `k² (1 − cos(δ − δ₀)) > 0` where it is
positive). -/
private theorem unstable_fold {c : PSC} {δ₀ : ℝ} (hb : c.Pmax * Real.sin δ₀ = c.Pstar)
    (hcos : Real.cos δ₀ = 0) (hk : c.Kp * c.Pmax ≠ 0) :
    Unstable c.field (embed δ₀) := by
  set k := c.Kp * c.Pmax * Real.sin δ₀ with hkdef
  have hk0 : k ≠ 0 := mul_ne_zero hk (SpecialFunctions.sin_ne_zero_of_cos hcos)
  have hW : ContDiff ℝ 1 fun z : State 1 => k * z 0 - k * δ₀ :=
    (contDiff_const.mul (NormalForm.coordCLM.contDiff)).sub contDiff_const
  refine Dynamics.unstable_of_chetaev (W := fun z : State 1 => k * z 0 - k * δ₀) (r := 1)
    (NormalForm.lift_contDiff c.rhs_contDiff) hW one_pos (fun ε hε => ?_) (fun z hz hWz => ?_)
  · rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · refine ⟨embed (δ₀ + -(ε / 2)), ?_, ?_⟩
      · rw [norm_embed_add_sub, abs_neg, abs_of_pos (by linarith)]
        linarith
      · simp only [NormalForm.embed_apply]
        nlinarith
    · refine ⟨embed (δ₀ + ε / 2), ?_, ?_⟩
      · rw [norm_embed_add_sub, abs_of_pos (by linarith)]
        linarith
      · simp only [NormalForm.embed_apply]
        nlinarith
  · have hd : HasFDerivAt (fun z : State 1 => k * z 0 - k * δ₀) (k • NormalForm.coordCLM) z :=
      (hasFDerivAt_coord k z).sub_const _
    rw [hd.fderiv]
    change 0 < k * (c.field z) 0
    rw [field, NormalForm.lift_apply, c.rhs_eq_fold hb hcos]
    have hne : z 0 - δ₀ ≠ 0 := by
      intro h
      apply (lt_irrefl (0 : ℝ))
      calc (0 : ℝ) < k * z 0 - k * δ₀ := hWz
        _ = k * (z 0 - δ₀) := by ring
        _ = 0 := by rw [h, mul_zero]
    have hlt : |z 0 - δ₀| ≤ 1 := by
      have : ‖z - embed δ₀‖ = |z 0 - δ₀| := by
        rw [← NormalForm.embed_coord z, NormalForm.embed_sub, NormalForm.norm_embed,
          NormalForm.embed_coord]
      linarith
    have hcos1 : Real.cos (z 0 - δ₀) < 1 := by
      refine lt_of_le_of_ne (Real.cos_le_one _) fun h => hne ?_
      refine (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp h <;>
        [linarith [neg_abs_le (z 0 - δ₀), Real.two_le_pi];
          linarith [le_abs_self (z 0 - δ₀), Real.two_le_pi]]
    have : 0 < 1 - Real.cos (z 0 - δ₀) := by linarith
    have hk2 : 0 < k * k := mul_self_pos.mpr hk0
    nlinarith

/-- The local asymptotic translation is exact: a PSC model is locally asymptotically stable at
`δ*` exactly when the angle is balanced with a negative slope (`K_p P_max cos δ* > 0`). Local
asymptotic stability forces an equilibrium (`Dynamics.isEquilibrium_of_lyapunovStable`); a vanishing
gain `K_p = 0` or a vanishing curve `P_max = P* = 0` makes every state an equilibrium; a positive
slope is unstable; and at a balanced fold angle (`cos δ* = 0`, `K_p P_max ≠ 0`) the field
`k (1 − cos(δ − δ*))` keeps the coordinate `k δ` nondecreasing, so the solutions from one side
never return (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`). The linearization alone does
not decide the fold, the model's structure does (`Spectral.exact_of_equilibrium` with the guard
`K_p P_max cos δ* > 0`). -/
@[tmio TM, powerlib_domain] theorem exact_locallyAsymptoticallyStable :
    connection% (family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  unfold powerlib.TMIO.Statement at hsound
  refine Spectral.exact_of_equilibrium (fun m P => mem_den_flow_iff) (Or.inr (Or.inl rfl))
    (fun m => 0 < m.c.Kp * m.c.Pmax * Real.cos m.δ) (Family.chain_le_semantics_iff.mp hsound _)
    (fun m => NormalForm.lift_contDiff m.c.rhs_contDiff) (fun m heq hs hm => ?_)
    fun m heq hs => ?_
  · have hlas : LocalAsymptoticStable m.c.field (embed m.δ) := mem_den_flow_iff.mp hm
    have hK : m.c.Kp ≠ 0 := fun hK =>
      not_las_of_rhs_zero (fun z => by simp [rhs, hK]) m.δ hlas
    have hb := (m.c.field_eq_zero_iff hK m.δ).mp heq
    have hzero : m.c.Pmax ≠ 0 := fun hP => by
      have hP' : m.c.Pstar = 0 := by rw [← hb, hP, zero_mul]
      exact not_las_of_rhs_zero (fun z => by simp [rhs, hP, hP']) m.δ hlas
    rcases lt_trichotomy (m.c.Kp * m.c.Pmax * Real.cos m.δ) 0 with h | h | h
    · exact absurd hlas.1 (unstable_of (m := m) hb h)
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hzero ((mul_eq_zero.mp h').resolve_left hK)
      · exact not_las_fold hb h' (mul_ne_zero hK hzero) hlas
    · exact hs h
  · have hK : m.c.Kp ≠ 0 := fun hK => by
      rw [hK, zero_mul, zero_mul] at hs
      exact lt_irrefl 0 hs
    rw [TMIO.mem_realize]
    rintro q (rfl | rfl)
    · exact (m.c.field_eq_zero_iff hK m.δ).mp heq
    · exact hs

/-- Lyapunov stability holds exactly at a balanced angle with a negative slope, or for a
vanishing scalar field (`K_p = 0`, or `P_max = P* = 0`, where every state is an equilibrium). A
positive slope is unstable, and so is a balanced fold angle (`cos δ* = 0`, `K_p P_max ≠ 0`), by
Chetaev's theorem (`Dynamics.unstable_of_chetaev`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff (m : Model) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | (m.c.Pmax * Real.sin m.δ = m.c.Pstar ∧
          0 < m.c.Kp * m.c.Pmax * Real.cos m.δ) ∨
        m.c.Kp = 0 ∨ (m.c.Pmax = 0 ∧ m.c.Pstar = 0)}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hm
    have hls : LyapunovStable m.c.field (embed m.δ) := mem_den_flow_iff.mp hm
    have hC : ContDiff ℝ 1 m.c.field := NormalForm.lift_contDiff m.c.rhs_contDiff
    have heq : m.c.rhs m.δ = 0 := by
      have h := Dynamics.isEquilibrium_of_lyapunovStable hC hls
      rwa [IsEquilibrium, field, NormalForm.lift_eq_zero_iff] at h
    by_cases hK : m.c.Kp = 0
    · exact Or.inr (Or.inl hK)
    have hb : m.c.Pmax * Real.sin m.δ = m.c.Pstar := by
      have := (mul_eq_zero.mp heq).resolve_left hK
      linarith
    by_cases hP : m.c.Pmax = 0
    · exact Or.inr (Or.inr ⟨hP, by rw [← hb, hP, zero_mul]⟩)
    rcases lt_trichotomy (m.c.Kp * m.c.Pmax * Real.cos m.δ) 0 with h | h | h
    · exact absurd hls (unstable_of (m := m) hb h)
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd ((mul_eq_zero.mp h').resolve_left hK) hP
      · exact absurd hls (unstable_fold hb h' (mul_ne_zero hK hP))
    · exact Or.inl ⟨hb, h⟩
  · rintro (⟨hb, hs⟩ | hK | ⟨hP, hP'⟩)
    · exact mem_den_flow_iff.mpr (les_of (m := m) hb hs).lyapunovStable
    all_goals
      rw [family_isAutonomous.mem_den_flow]
      refine Dynamics.lyapunovStable_of_inner_nonpos one_pos
        (ContinuousLinearMap.id ℝ (State 1)) Function.injective_id fun z => ?_
      simp [Model.field, field, rhs, NormalForm.lift, *]

/-- A frozen synchronization loop: `K_p = 0` (and `P* = P_max = 0`, `δ* = 0`); the scalar field
vanishes and every state is an equilibrium. -/
def frozen : Model := ⟨⟨0, 0, 0⟩, 0⟩

/-- The frozen loop is Lyapunov stable (every solution is constant) although its slope
`K_p P_max cos δ*` is zero. -/
@[tmio TM, powerlib_domain] theorem frozen_mem_den_lyapunovStable :
    connection% (frozen ∈ family.den (.flow .lyapunovStable)) := by
  have h := mem_den_lyapunovStable_iff frozen
  unfold powerlib.TMIO.Statement at h ⊢
  exact h.mpr (Or.inr (Or.inl rfl))

/-- The Lyapunov translation is sound but not exact: the frozen loop is Lyapunov stable without a
negative slope. -/
@[tmio TM, powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness frozen_mem_den_lyapunovStable (q := .stableSlope)
    (by simp [family, translate]) (by simp [family, Meets, frozen])

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: `K_p = P* = 1`, `P_max = 0`, `δ* = 0`. -/
def offEquilibrium : Model := ⟨⟨1, 1, 0⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[tmio TM, powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.mem_den_unstable_of_ne_zero (fun m P => mem_den_flow_iff)
    (NormalForm.lift_contDiff offEquilibrium.c.rhs_contDiff) fun h => ?_
  change NormalForm.lift offEquilibrium.c.rhs (NormalForm.embed offEquilibrium.δ) = 0 at h
  rw [NormalForm.lift_eq_zero_iff] at h
  simp [offEquilibrium, rhs] at h

/-- The instability translation is sound but not exact: every non-equilibrium angle is unstable,
while the translation asks for a balanced one. -/
@[tmio TM, powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_exact_of_witness offEquilibrium_mem_den_unstable (q := .balanced)
    (by simp [family, translate]) (by simp [family, Meets, offEquilibrium])

end PSC

/-! ## Algebra (foundation) -/

/-- Active resistance: with `H(s) = ω_b/(s + ω_b)`, `R_a (H(s) − 1) = −R_a s/(s + ω_b)`. -/
@[powerlib_foundation] theorem activeResistance_highPass (Ra ωb : ℝ) (s : ℂ)
    (hs : s + (ωb : ℂ) ≠ 0) :
    (Ra : ℂ) * ((ωb : ℂ) / (s + (ωb : ℂ)) - 1) = -(Ra : ℂ) * s / (s + (ωb : ℂ)) := by
  field_simp
  ring

/-- PSC frequency law `Δω = K_p (P* − P)` is the pure droop / zero-inertia swing law
`0 = (P* − P) − D Δω` with `D = 1/K_p`. -/
@[powerlib_foundation] theorem psc_eq_droop {Kp Δω Pstar P : ℝ} (hK : Kp ≠ 0) :
    Δω = Kp * (Pstar - P) ↔ 0 = (Pstar - P) - (1 / Kp) * Δω := by
  constructor
  · intro h; rw [h]; field_simp; ring
  · intro h; field_simp at h; linarith

end powerlib.GFM
