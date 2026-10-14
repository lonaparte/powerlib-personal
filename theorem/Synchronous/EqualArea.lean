import theorem.Synchronous.Swing
import theorem.Dynamics.Calculus

/-! # Equal-area criterion for the single-machine infinite-bus swing equation: static part

Model boundary.  Each stage of the three-stage fault sequence (pre-fault, during-fault,
post-fault) is one instance of the canonical swing model `SwingParams`
(`theorem/Synchronous/Swing.lean`): state `(δ, ω)` (rotor angle, frequency deviation in
rad/s), `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`, constant `P_m`, generator OUT-positive
(Kundur) convention, continuous time, no AVR / governor / PLL / limiter.

Contents (all static or generic foundation).
* Closed-form integrals of the power-angle curve; accelerating and decelerating areas
  `A_acc`, `A_dec` in closed form, and their expression through the potential
  (`Aacc_eq_neg_potential`, `Adec_eq_potential_sub`).
* `g(δ_cc) = A_acc − A_dec`: derivative `g′ = P_e^post − P_e^f` and uniqueness/existence of the
  critical clearing angle.
* The sign of `P_e − P_m` between the equilibria and the bound of the potential on the well.
* Trajectory calculus of the swing field (coordinate derivatives along an integral curve, the
  constant solution at an equilibrium) and a continuous-induction helper, used by the
  trajectory-level criteria.

Family and connection conclusions.  None: the equal-area criterion, the critical clearing time and
the three-stage (switched) fault sequence are trajectory-level results outside the sentence
language of the swing family (`Synchronous.Swing.family`) (Rules §3a).  The exact first-swing
criterion (`firstSwing_iff`), its sufficiency and necessity halves, energy conservation, the
bolted-fault trajectory and clearing time, and the clearing-time bound (formerly public domain
theorems of this module) are kept as private implementation evidence in
`theorem/Synchronous/FaultSequence.lean`, next to the switched-model results that are proved from
them (a private theorem cannot be used across modules).

Corrections.
* T-transient-stability §1.5 states `g′(δ_cc) = 2(P_m − P_e^f(δ_cc))`; the derivative of
  `g = A_acc − A_dec` is `g′ = (P_m − P_e^f) + (P_e^post − P_m) = P_e^post − P_e^f`
  (`hasDerivAt_eacG`).  Uniqueness holds where `P_e^f < P_e^post`, not merely where `P_e^f < P_m`.
* §1.5 calls `A_acc = A_dec` (with `δ_max = δ_u`) a criterion but only derives it from energy
  conservation along one trajectory; the formal version (private `firstSwing_iff`,
  `FaultSequence.lean`) shows the boundary case `½ M ω_c² = ∫_{δ_c}^{δ_u}(P_e − P_m)` belongs to
  the "does not cross" side.
* §1.6 bounds `t_cc` with `max_{[δ₀, δ_cc]} P_e^f`; the formal bound (private
  `time_in_window_le`) controls the time the trajectory spends inside `[δ₀, δ_cc]`.
* §1.8 writes `A_dec^{D>0} = A_dec^{D=0} − ∫ D Δω² > A_dec^{D=0}`, which is self-contradictory
  (subtracting a positive quantity cannot increase it); see `theorem/Synchronous/DampedEAC.lean`.

Source: work-sync theory/T-transient-stability.md §1.3–§1.6, §1.8.
-/

noncomputable section
namespace powerlib.Synchronous
open Set Filter Topology intervalIntegral
open powerlib.Dynamics (State)

namespace SwingParams

variable (p : SwingParams)

/-! ## Closed-form areas -/

/-- `∫_a^b P_e = k₁ (b − a) + k₂ (cos(a − k₃) − cos(b − k₃))`. -/
@[powerlib_foundation] theorem integral_Pe (a b : ℝ) :
    ∫ s in a..b, p.Pe s = p.k₁ * (b - a) + p.k₂ * (Real.cos (a - p.k₃) - Real.cos (b - p.k₃)) := by
  have h2 : IntervalIntegrable (fun s => p.k₂ * Real.sin (s - p.k₃)) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun s => p.k₂ * Real.sin (s - p.k₃)).intervalIntegrable _ _
  simp only [Pe]
  rw [integral_add intervalIntegrable_const h2, integral_const, integral_const_mul,
    integral_comp_sub_right (fun x => Real.sin x), integral_sin]
  simp only [smul_eq_mul]
  ring

/-- The potential is the area under `P_e − P_m`: `U_{δ₀}(δ) = ∫_{δ₀}^{δ} (P_e − P_m)`. -/
@[powerlib_foundation] theorem potential_eq_integral (δ₀ δ : ℝ) :
    p.potential δ₀ δ = ∫ s in δ₀..δ, (p.Pe s - p.Pm) := by
  have h1 : IntervalIntegrable p.Pe MeasureTheory.volume δ₀ δ :=
    (by unfold Pe; fun_prop : Continuous p.Pe).intervalIntegrable _ _
  rw [integral_sub h1 intervalIntegrable_const, integral_Pe, integral_const, potential]
  simp only [smul_eq_mul]
  ring

/-- Accelerating area `A_acc(x) = ∫_{δ₀}^{x} (P_m − P_e)` of a (during-fault) stage. -/
def Aacc (δ₀ x : ℝ) : ℝ := ∫ s in δ₀..x, (p.Pm - p.Pe s)

/-- Decelerating area `A_dec(x) = ∫_{x}^{δ_max} (P_e − P_m)` of a (post-fault) stage. -/
def Adec (x δmax : ℝ) : ℝ := ∫ s in x..δmax, (p.Pe s - p.Pm)

@[powerlib_foundation] theorem Aacc_eq (δ₀ x : ℝ) :
    p.Aacc δ₀ x = (p.Pm - p.k₁) * (x - δ₀) +
      p.k₂ * (Real.cos (x - p.k₃) - Real.cos (δ₀ - p.k₃)) := by
  have h1 : IntervalIntegrable p.Pe MeasureTheory.volume δ₀ x :=
    (by unfold Pe; fun_prop : Continuous p.Pe).intervalIntegrable _ _
  rw [Aacc, integral_sub intervalIntegrable_const h1, integral_Pe, integral_const]
  simp only [smul_eq_mul]
  ring

@[powerlib_foundation] theorem Adec_eq (x δmax : ℝ) :
    p.Adec x δmax = p.k₂ * (Real.cos (x - p.k₃) - Real.cos (δmax - p.k₃)) -
      (p.Pm - p.k₁) * (δmax - x) := by
  rw [Adec, ← potential_eq_integral, potential]
  ring

end SwingParams

/-- `g(x) = A_acc^f(x) − A_dec^post(x)` for a during-fault stage `f` and a post-fault stage `q`. -/
def eacG (f q : SwingParams) (δ₀ δmax x : ℝ) : ℝ := f.Aacc δ₀ x - q.Adec x δmax

/-- `g′(x) = P_e^post(x) − P_e^f(x)` when both stages share `P_m`. -/
@[powerlib_foundation] theorem hasDerivAt_eacG (f q : SwingParams) (hPm : f.Pm = q.Pm)
    (δ₀ δmax x : ℝ) : HasDerivAt (eacG f q δ₀ δmax) (q.Pe x - f.Pe x) x := by
  have hfun : eacG f q δ₀ δmax = fun y =>
      ((f.Pm - f.k₁) * (y - δ₀) + f.k₂ * (Real.cos (y - f.k₃) - Real.cos (δ₀ - f.k₃))) -
        (q.k₂ * (Real.cos (y - q.k₃) - Real.cos (δmax - q.k₃)) - (q.Pm - q.k₁) * (δmax - y)) := by
    funext y; simp only [eacG, SwingParams.Aacc_eq, SwingParams.Adec_eq]
  rw [hfun]
  have hc (k : ℝ) : HasDerivAt (fun y => Real.cos (y - k)) (-Real.sin (x - k)) x := by
    have := ((hasDerivAt_id x).sub_const k).cos
    simpa using this
  have h := ((((hasDerivAt_id x).sub_const δ₀).const_mul (f.Pm - f.k₁)).add
    (((hc f.k₃).sub_const (Real.cos (δ₀ - f.k₃))).const_mul f.k₂)).sub
    ((((hc q.k₃).sub_const (Real.cos (δmax - q.k₃))).const_mul q.k₂).sub
      (((hasDerivAt_const x δmax).sub (hasDerivAt_id x)).const_mul (q.Pm - q.k₁)))
  convert h using 1
  · funext y; simp
  · simp only [SwingParams.Pe]; rw [hPm]; ring

/-- Uniqueness of the critical clearing angle: where the post-fault curve lies strictly above
the during-fault curve, `g` is strictly increasing, so it has at most one zero. -/
@[powerlib_foundation] theorem eacG_root_unique (f q : SwingParams) (hPm : f.Pm = q.Pm)
    {δ₀ δmax a b : ℝ} (hgap : ∀ x ∈ Ioo a b, f.Pe x < q.Pe x) {x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hgx : eacG f q δ₀ δmax x = 0)
    (hgy : eacG f q δ₀ δmax y = 0) : x = y := by
  have hmono : StrictMonoOn (eacG f q δ₀ δmax) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · exact fun z _ => (hasDerivAt_eacG f q hPm δ₀ δmax z).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hasDerivAt_eacG f q hPm δ₀ δmax z).deriv]
      linarith [hgap z hz]
  exact hmono.injOn hx hy (hgx.trans hgy.symm)

/-- Existence of the critical clearing angle by the intermediate value theorem. -/
@[powerlib_foundation] theorem exists_eacG_root (f q : SwingParams) (hPm : f.Pm = q.Pm)
    {δ₀ δmax a b : ℝ} (hab : a ≤ b) (ha : eacG f q δ₀ δmax a ≤ 0)
    (hb : 0 ≤ eacG f q δ₀ δmax b) : ∃ x ∈ Icc a b, eacG f q δ₀ δmax x = 0 :=
  intermediate_value_Icc hab
    (fun z _ => (hasDerivAt_eacG f q hPm δ₀ δmax z).continuousAt.continuousWithinAt) ⟨ha, hb⟩

namespace SwingParams

variable (p : SwingParams)

/-! ## Trajectory calculus for the swing field -/

/-- Coordinate derivatives along a solution, at interior points of the time set. -/
@[powerlib_foundation] theorem coord_hasDerivAt {φ : ℝ → State 2} {s : Set ℝ} {t : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) s) (ht : t ∈ s) (hs : s ∈ 𝓝 t)
    (j : Fin 2) : HasDerivAt (fun τ => φ τ j) (p.field (φ t) j) t := by
  have h := ((hφ t ht).hasDerivAt hs)
  have := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using this

@[powerlib_foundation] theorem coord_continuousOn {φ : ℝ → State 2} {s : Set ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) s) (j : Fin 2) :
    ContinuousOn (fun τ => φ τ j) s :=
  ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
    hφ.continuousOn

/-- A constant curve at an equilibrium is a solution. -/
@[powerlib_foundation] theorem isIntegralCurveOn_const {x : State 2} (hx : p.field x = 0)
    (s : Set ℝ) : IsIntegralCurveOn (fun _ => x) (fun _ y => p.field y) s := by
  intro t _
  show HasDerivWithinAt _ (p.field x) s t
  rw [hx]
  exact hasDerivWithinAt_const _ _ _

/-! ## Sign of `P_e − P_m` between the equilibria -/

@[powerlib_foundation] theorem arcsin_loadRatio_mem (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    Real.arcsin p.loadRatio ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have ha := abs_lt.mp (p.abs_loadRatio_lt hk h)
  exact ⟨Real.neg_pi_div_two_lt_arcsin.mpr ha.1, Real.arcsin_lt_pi_div_two.mpr ha.2⟩

/-- `P_e > P_m` strictly between `δ_s` and `δ_u`. -/
@[powerlib_foundation] theorem Pm_lt_Pe_of_mem (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂)
    {δ : ℝ} (hδ : δ ∈ Ioo p.deltaS p.deltaU) : p.Pm < p.Pe δ := by
  obtain ⟨hy1, hy2⟩ := p.arcsin_loadRatio_mem hk h
  have hs := p.sin_loadRatio hk h.le
  set y := Real.arcsin p.loadRatio
  simp only [deltaS, deltaU] at hδ
  have hdiff : p.Pe δ - p.Pm = p.k₂ * (Real.sin (δ - p.k₃) - Real.sin y) := by
    simp only [Pe]; linear_combination hs
  rw [Real.sin_sub_sin] at hdiff
  have h1 : 0 < Real.sin ((δ - p.k₃ - y) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ.1]) (by linarith [hδ.2])
  have h2 : 0 < Real.cos ((δ - p.k₃ + y) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
  have : 0 < p.Pe δ - p.Pm := by rw [hdiff]; positivity
  linarith

/-- `P_e < P_m` strictly between `δ_u − 2π` and `δ_s`. -/
@[powerlib_foundation] theorem Pe_lt_Pm_of_mem (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂)
    {δ : ℝ} (hδ : δ ∈ Ioo (p.deltaU - 2 * Real.pi) p.deltaS) : p.Pe δ < p.Pm := by
  obtain ⟨hy1, hy2⟩ := p.arcsin_loadRatio_mem hk h
  have hs := p.sin_loadRatio hk h.le
  set y := Real.arcsin p.loadRatio
  simp only [deltaS, deltaU] at hδ
  have hdiff : p.Pe δ - p.Pm = p.k₂ * (Real.sin (δ - p.k₃) - Real.sin y) := by
    simp only [Pe]; linear_combination hs
  rw [Real.sin_sub_sin] at hdiff
  have h1 : Real.sin ((δ - p.k₃ - y) / 2) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hδ.2]) (by linarith [hδ.1])
  have h2 : 0 < Real.cos ((δ - p.k₃ + y) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
  have : p.Pe δ - p.Pm < 0 := by
    rw [hdiff]
    have : 2 * Real.sin ((δ - p.k₃ - y) / 2) * Real.cos ((δ - p.k₃ + y) / 2) < 0 := by
      nlinarith
    exact mul_neg_of_pos_of_neg hk this
  linarith

@[powerlib_foundation] theorem deltaS_lt_deltaU (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) :
    p.deltaS < p.deltaU := by
  obtain ⟨_, hy2⟩ := p.arcsin_loadRatio_mem hk h
  simp only [deltaS, deltaU]; linarith

@[powerlib_foundation] theorem deltaU_sub_two_pi_lt_deltaS (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) : p.deltaU - 2 * Real.pi < p.deltaS := by
  obtain ⟨hy1, _⟩ := p.arcsin_loadRatio_mem hk h
  simp only [deltaS, deltaU]; linarith

/-- In the potential well `(δ_u − 2π, δ_u]`, the potential on `[δ_c, δ_u]` is bounded by its
values at the endpoints. -/
@[powerlib_foundation] theorem potential_le_max (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂)
    {δ₀ δc δ : ℝ} (hc : p.deltaU - 2 * Real.pi < δc) (hδ : δ ∈ Icc δc p.deltaU) :
    p.potential δ₀ δ ≤ max (p.potential δ₀ δc) (p.potential δ₀ p.deltaU) := by
  have hcont : ∀ u v, ContinuousOn (p.potential δ₀) (Icc u v) := fun u v =>
    fun z _ => (p.hasDerivAt_potential δ₀ z).continuousAt.continuousWithinAt
  rcases le_or_gt p.deltaS δ with hs | hs
  · have hmono : MonotoneOn (p.potential δ₀) (Icc p.deltaS p.deltaU) :=
      Dynamics.monotoneOn_Icc_of_hasDerivAt (hcont _ _) (fun z _ => p.hasDerivAt_potential δ₀ z)
        (fun z hz => by linarith [p.Pm_lt_Pe_of_mem hk h hz])
    exact (hmono ⟨hs, hδ.2⟩ ⟨(p.deltaS_lt_deltaU hk h).le, le_rfl⟩ hδ.2).trans (le_max_right _ _)
  · have hanti : AntitoneOn (p.potential δ₀) (Icc δc p.deltaS) := by
      have := Dynamics.monotoneOn_Icc_of_hasDerivAt (h := fun z => -p.potential δ₀ z)
        (h' := fun z => -(p.Pe z - p.Pm)) (a := δc) (b := p.deltaS)
        (fun z hz => ((p.hasDerivAt_potential δ₀ z).continuousAt.neg).continuousWithinAt)
        (fun z _ => (p.hasDerivAt_potential δ₀ z).neg)
        (fun z hz => by linarith [p.Pe_lt_Pm_of_mem hk h ⟨by linarith [hz.1], hz.2⟩])
      intro u hu v hv huv
      have := this hu hv huv
      simp only at this
      linarith
    exact (hanti ⟨le_rfl, (hδ.1.trans hs.le)⟩ ⟨hδ.1, hs.le⟩ hδ.1).trans (le_max_left _ _)

/-- The accelerating area is minus the potential: `A_acc(δ₀, x) = −U_{δ₀}(x)`. -/
@[powerlib_foundation] theorem Aacc_eq_neg_potential (δ₀ x : ℝ) :
    p.Aacc δ₀ x = -p.potential δ₀ x := by
  rw [Aacc_eq, potential]
  ring

/-- `A_dec(x, δ_max) = U_{δ₀}(δ_max) − U_{δ₀}(x)` for any reference angle `δ₀`. -/
@[powerlib_foundation] theorem Adec_eq_potential_sub (δ₀ x δmax : ℝ) :
    p.Adec x δmax = p.potential δ₀ δmax - p.potential δ₀ x := by
  rw [Adec_eq, potential, potential]
  ring

end SwingParams
end powerlib.Synchronous
