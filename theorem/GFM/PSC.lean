import theorem.NormalForm.Scalar
import theorem.Family.Basic
import theorem.Flow.Shift
import theorem.TMIO.ClaimElab

/-! # Power-synchronization control (PSC): quasi-static one-dimensional model and algebra

Model boundary (domain part).
* Quasi-static PSC: the converter is a voltage source `V ∠ θ` behind the line reactance
  `X = ω₁ L` to an infinite bus `V_g ∠ θ_g`, `θ_g = ω₁ t + θ_{g0}`; the line current is
  quasi-static (no inductor dynamics), so `P = P_max sin(θ − θ_g)`, `P_max = V V_g / (ω₁ L)`.
* Synchronization law `θ̇ = ω₁ + K_p (P* − P)` with constant `P*`; in the grid-angle frame
  `δ = θ − θ_g` this is the one-dimensional autonomous field `δ̇ = K_p (P* − P_max sin δ)`
  (state `δ : Dynamics.State 1`, continuous time).
* Excluded: active-resistance damping loop and inductor dynamics (the three-pole closed loop of
  T-power-synchronization-control §1.4), DC-link loop, current limiting / PLL backup, delay, PWM.
* Power is export-positive (GFM family exception).

Results: equilibria `⇔ |P*| ≤ P_max`; equilibria with `cos δ₀ > 0` are locally exponentially
stable and with `cos δ₀ < 0` unstable (`K_p, P_max > 0`), via the scalar linearization
wrappers of `theorem/NormalForm/Scalar.lean`; `absoluteAngle_iff` shows that the original law in
the absolute angle `θ` is equivalent, pointwise in time, to the `δ`-equation.

Family and connection conclusions.  `PSC.family`: a complete system (`PSC.Model`) is a parameter
set with a selected angle `δ*`, read as the scalar field translated so that `δ*` is the origin
(`Flow.Property.holds_shift_iff`).  Static requirements: balance `P_max sin δ* = P*`, a negative
slope `K_p P_max cos δ* > 0` (i.e. `d/dδ [K_p (P* − P_max sin δ)] < 0` at `δ*`), or a positive
slope `K_p P_max cos δ* < 0`.  The local sentences translate into balance and a negative slope,
instability into balance and a positive slope, passivity into nothing (exact), the remaining
sentences into the whole, inconsistent, language.  `PSC.chain_le_semantics` proves soundness; the
former domain theorems `locallyExponentiallyStable`, `unstable`, `locallyExponentiallyStable_arcsin`
and `unstable_pi_sub_arcsin` are connection statements (members of the denotations), and
`field_eq_zero_iff`, `exists_equilibrium_iff` are static evidence on the model.

Algebra (foundation): the steady-state active power, the converter-side reactive power and the
grid-side received reactive power from `S̄ = V̄ Ī*`; the active-resistance high-pass
`R_a (H(s) − 1) = −R_a s/(s + ω_b)`; PSC as pure droop with `D = 1/K_p`.

Corrections.
* T-power-synchronization-control §1.1 calls `Q₀ = (V V_g cos θ₀ − V_g²)/(ω₁ L)` the reactive
  power exported by the converter; that expression is the reactive power *received at the grid
  bus*.  The converter-side output reactive power is `(V² − V V_g cos θ₀)/(ω₁ L)`
  (`converterSide_power`, `gridSide_power`).
* The same section declares the current IN-positive (into the converter) while the line equation
  `L dĪ/dt = V̄_conv − V̄_g − jω₁ L Ī` makes `Ī` flow from the converter to the grid; here `Ī` is
  the converter-to-grid (export) current.

Source: work-sync theory/T-power-synchronization-control.md §1.1–§1.3, §1.10;
theory/T-vsg-control.md §1.7; theory/T-gfm-control.md §1.4.
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

@[powerlib_foundation] theorem rhs_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k c.rhs := by
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
  constructor
  · rintro ⟨x, hx⟩
    rw [← NormalForm.embed_coord x, c.field_eq_zero_iff hK] at hx
    rw [← hx, abs_mul, abs_of_pos hP]
    exact mul_le_of_le_one_right hP.le (Real.abs_sin_le_one _)
  · intro h
    have ha : |c.Pstar / c.Pmax| ≤ 1 := by rw [abs_div, abs_of_pos hP, div_le_one hP]; exact h
    refine ⟨embed (Real.arcsin (c.Pstar / c.Pmax)), (c.field_eq_zero_iff hK _).mpr ?_⟩
    rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]
    field_simp

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

/-- The quasi-static PSC family. -/
def family : Family Model Requirement 1 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.c.field (embed m.δ) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

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
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : 0 < m.c.Kp * m.c.Pmax * Real.cos m.δ := h .stableSlope
  have h2 : m.c.Kp * m.c.Pmax * Real.cos m.δ < 0 := h .unstableSlope
  linarith

/-- Every translation of the PSC family is sound: the scalar linearization at the selected angle
(the slope `−K_p P_max cos δ*`) proves the local sentences and instability, and passivity holds
without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · rw [mem_den_flow_iff]
    cases P
    case unstable =>
      exact unstable_of (hm .balanced (by simp [translate]))
        (hm .unstableSlope (by simp [translate]))
    case lyapunovStable =>
      exact (les_of (hm .balanced (by simp [translate]))
        (hm .stableSlope (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (les_of (hm .balanced (by simp [translate])) (hm .stableSlope (by simp [translate])))
    case locallyExponentiallyStable =>
      exact les_of (hm .balanced (by simp [translate])) (hm .stableSlope (by simp [translate]))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- An equilibrium with `cos δ₀ > 0` is locally exponentially stable (`K_p, P_max > 0`). -/
@[powerlib_domain] theorem locallyExponentiallyStable (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    {δ₀ : ℝ} (heq : c.Pmax * Real.sin δ₀ = c.Pstar) (hcos : 0 < Real.cos δ₀) :
    connection% (Model.mk c δ₀ ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (les_of (m := ⟨c, δ₀⟩) heq (by
    show 0 < c.Kp * c.Pmax * Real.cos δ₀
    positivity))

/-- An equilibrium with `cos δ₀ < 0` is unstable (`K_p, P_max > 0`). -/
@[powerlib_domain] theorem unstable (hK : 0 < c.Kp) (hP : 0 < c.Pmax) {δ₀ : ℝ}
    (heq : c.Pmax * Real.sin δ₀ = c.Pstar) (hcos : Real.cos δ₀ < 0) :
    connection% (Model.mk c δ₀ ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (unstable_of (m := ⟨c, δ₀⟩) heq
    (mul_neg_of_pos_of_neg (mul_pos hK hP) hcos))

/-- The loading angle `arcsin(P*/P_max)` is locally exponentially stable when
`|P*| < P_max`. -/
@[powerlib_domain] theorem locallyExponentiallyStable_arcsin (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    (h : |c.Pstar| < c.Pmax) :
    connection% (Model.mk c (Real.arcsin (c.Pstar / c.Pmax)) ∈
      family.den (.flow .locallyExponentiallyStable)) := by
  have ha : |c.Pstar / c.Pmax| < 1 := by rw [abs_div, abs_of_pos hP, div_lt_one hP]; exact h
  apply c.locallyExponentiallyStable hK hP
  · rw [Real.sin_arcsin (abs_lt.mp ha).1.le (abs_lt.mp ha).2.le]; field_simp
  · rw [Real.cos_arcsin]; apply Real.sqrt_pos.mpr
    have : (c.Pstar / c.Pmax) ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (c.Pstar / c.Pmax)]
    linarith

/-- The second equilibrium `π − arcsin(P*/P_max)` is unstable when `|P*| < P_max`. -/
@[powerlib_domain] theorem unstable_pi_sub_arcsin (hK : 0 < c.Kp) (hP : 0 < c.Pmax)
    (h : |c.Pstar| < c.Pmax) :
    connection% (Model.mk c (Real.pi - Real.arcsin (c.Pstar / c.Pmax)) ∈
      family.den (.flow .unstable)) := by
  have ha : |c.Pstar / c.Pmax| < 1 := by rw [abs_div, abs_of_pos hP, div_lt_one hP]; exact h
  apply c.unstable hK hP
  · rw [Real.sin_pi_sub, Real.sin_arcsin (abs_lt.mp ha).1.le (abs_lt.mp ha).2.le]; field_simp
  · rw [Real.cos_pi_sub, Real.cos_arcsin, neg_lt_zero]; apply Real.sqrt_pos.mpr
    have : (c.Pstar / c.Pmax) ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (c.Pstar / c.Pmax)]
    linarith

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

end PSC

/-! ## Algebra (foundation) -/

/-- Converter-side complex power `S̄ = V̄_conv Ī*`, `Ī = (V e^{jθ} − V_g)/(jX)` (export current):
`P = V V_g sin θ / X`, `Q_conv = (V² − V V_g cos θ)/X`. -/
@[powerlib_foundation] theorem converterSide_power (V Vg θ X : ℝ) (hX : X ≠ 0) :
    (V : ℂ) * Complex.exp (θ * Complex.I) *
        (starRingEnd ℂ) (((V : ℂ) * Complex.exp (θ * Complex.I) - (Vg : ℂ)) /
          ((X : ℂ) * Complex.I)) =
      ((V * Vg * Real.sin θ / X : ℝ) : ℂ) +
        ((V ^ 2 - V * Vg * Real.cos θ) / X : ℝ) * Complex.I := by
  rw [show V ^ 2 - V * Vg * Real.cos θ =
      V ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) - V * Vg * Real.cos θ by
    rw [Real.sin_sq_add_cos_sq]; ring]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;>
    field_simp <;> ring

/-- Grid-side received complex power `S̄_g = V̄_g Ī*`: `P = V V_g sin θ / X`,
`Q_g = (V V_g cos θ − V_g²)/X` (the note's `Q₀`). -/
@[powerlib_foundation] theorem gridSide_power (V Vg θ X : ℝ) (hX : X ≠ 0) :
    (Vg : ℂ) * (starRingEnd ℂ) (((V : ℂ) * Complex.exp (θ * Complex.I) - (Vg : ℂ)) /
          ((X : ℂ) * Complex.I)) =
      ((V * Vg * Real.sin θ / X : ℝ) : ℂ) +
        ((V * Vg * Real.cos θ - Vg ^ 2) / X : ℝ) * Complex.I := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;>
    field_simp <;> ring

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
