import theorem.Synchronous.Swing

/-! # Equal-area criterion for the single-machine infinite-bus swing equation

Model boundary.  Each stage of the three-stage fault sequence (pre-fault, during-fault,
post-fault) is one instance of the canonical swing model `SwingParams`
(`theorem/Synchronous/Swing.lean`): state `(δ, ω)` (rotor angle, frequency deviation in
rad/s), `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`, constant `P_m`, generator OUT-positive
(Kundur) convention, continuous time, no AVR / governor / PLL / limiter.  The stages are
glued by continuity of the state at the switching instants: a post-fault statement starts
from the clearing state `(δ_c, ω_c)` at the clearing time `t_c`, a during-fault statement from
the pre-fault equilibrium `(δ₀, 0)` at the fault time `t_f`.  Every statement is at trajectory
level and quantifies over every solution of the relevant stage on the stated time set.

Contents.
* Closed-form integrals of the power-angle curve; accelerating and decelerating areas
  `A_acc`, `A_dec` in closed form.
* `g(δ_cc) = A_acc − A_dec`: derivative `g′ = P_e^post − P_e^f` and uniqueness/existence of the
  critical clearing angle.
* Energy conservation for `D = 0` and the **exact first-swing equal-area criterion**: a
  post-fault trajectory starting at `(δ_c, ω_c)`, `ω_c > 0`, `δ_u − 2π < δ_c ≤ δ_u`, never
  exceeds the unstable equilibrium angle `δ_u` iff `½ M ω_c² ≤ ∫_{δ_c}^{δ_u} (P_e − P_m)`.
* Bolted three-phase fault (`P_e^f ≡ 0`, `D = 0`): explicit during-fault trajectory and the
  exact critical clearing time `t_cc = √(2M(δ_cc − δ₀)/P_m)`; general during-fault curve:
  time spent in `[δ₀, δ_cc]` is at most `√(2M(δ_cc − δ₀)/(P_m − max P_e^f))`.

Corrections.
* T-transient-stability §1.5 states `g′(δ_cc) = 2(P_m − P_e^f(δ_cc))`; the derivative of
  `g = A_acc − A_dec` is `g′ = (P_m − P_e^f) + (P_e^post − P_m) = P_e^post − P_e^f`
  (`hasDerivAt_eacG`).  Uniqueness holds where `P_e^f < P_e^post`, not merely where `P_e^f < P_m`.
* §1.5 calls `A_acc = A_dec` (with `δ_max = δ_u`) a criterion but only derives it from energy
  conservation along one trajectory; the formal version (`firstSwing_iff`) shows the boundary
  case `½ M ω_c² = ∫_{δ_c}^{δ_u}(P_e − P_m)` belongs to the "does not cross" side.
* §1.6 bounds `t_cc` with `max_{[δ₀, δ_cc]} P_e^f`; the formal bound
  (`time_in_window_le`) controls the time the trajectory spends inside `[δ₀, δ_cc]`.
* §1.8 writes `A_dec^{D>0} = A_dec^{D=0} − ∫ D Δω² > A_dec^{D=0}`, which is self-contradictory
  (subtracting a positive quantity cannot increase it); not formalized (see report).

Source: work-sync theory/T-transient-stability.md §1.3–§1.6, §1.8.
-/

noncomputable section
namespace powerlib.Synchronous
open Set Filter Topology intervalIntegral
open powerlib.Dynamics (State)

/-! ## A continuous-induction helper -/

/-- If `g` is continuous on `[a, b]`, `g a > 0`, and positivity on `[a, t)` always propagates to
`t`, then `g > 0` on `[a, b]`. -/
@[powerlib_foundation] theorem pos_on_Icc_of_propagate {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) (ha : 0 < g a)
    (h : ∀ t ∈ Ioc a b, (∀ s ∈ Ico a t, 0 < g s) → 0 < g t) :
    ∀ t ∈ Icc a b, 0 < g t := by
  by_contra hne
  push Not at hne
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne
  set S := Icc a b ∩ g ⁻¹' Iic 0 with hSdef
  have hS : IsClosed S := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t₁, ht₁, hgt₁⟩
  have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hmem : sInf S ∈ S := hS.csInf_mem hSne hbdd
  have hle : g (sInf S) ≤ 0 := hmem.2
  have hat : a ≤ sInf S := hmem.1.1
  have hne_a : sInf S ≠ a := by
    intro he; rw [he] at hle; linarith
  have hpos : 0 < g (sInf S) := by
    refine h _ ⟨lt_of_le_of_ne hat (Ne.symm hne_a), hmem.1.2⟩ fun s hs => ?_
    by_contra hs'
    push Not at hs'
    have : sInf S ≤ s := csInf_le hbdd ⟨⟨hs.1, hs.2.le.trans hmem.1.2⟩, hs'⟩
    linarith [hs.2]
  linarith

/-- Monotonicity on `[a, b]` from a nonnegative derivative on `(a, b)`. -/
@[powerlib_foundation] theorem monotoneOn_Icc_of_hasDerivAt {h h' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn h (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hnn : ∀ x ∈ Ioo a b, 0 ≤ h' x) : MonotoneOn h (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc
  · rw [interior_Icc]; exact fun x hx => (hd x hx).hasDerivWithinAt
  · rw [interior_Icc]; exact hnn

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
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) s) (ht : t ∈ s) (hs : s ∈ 𝓝 t)
    (j : Fin 2) : HasDerivAt (fun τ => φ τ j) (p.field (φ t) j) t := by
  have h := ((hφ t ht).hasDerivAt hs)
  have := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using this

@[powerlib_foundation] theorem coord_continuousOn {φ : ℝ → State 2} {s : Set ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) s) (j : Fin 2) :
    ContinuousOn (fun τ => φ τ j) s :=
  ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
    hφ.continuousOn

/-- Energy is conserved along every solution of the undamped (`D = 0`) swing equation. -/
@[powerlib_domain] theorem energy_conserved (hM : p.M ≠ 0) (hD : p.D = 0) (δ₀ : ℝ)
    {φ : ℝ → State 2} {a : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Ici a)) :
    ∀ t ∈ Ici a, p.energy δ₀ (φ t) = p.energy δ₀ (φ a) := by
  have hdiff : Differentiable ℝ (p.energy δ₀) :=
    (p.contDiff_energy (k := 1) δ₀).differentiable (by norm_num)
  have h1 := Dynamics.antitoneOn_lyapunov_of_integralCurve hdiff
    (fun x => by rw [p.energy_lie hM, hD]; simp) hφ
  have hneg : ∀ x, fderiv ℝ (fun y => -p.energy δ₀ y) x (p.field x) ≤ 0 := by
    intro x
    rw [fderiv_fun_neg, _root_.neg_apply, p.energy_lie hM, hD]
    simp
  have h2 := Dynamics.antitoneOn_lyapunov_of_integralCurve (V := fun x => -p.energy δ₀ x)
    hdiff.neg hneg hφ
  intro t ht
  have ha : a ∈ Ici a := mem_Ici.mpr le_rfl
  have e1 := h1 ha ht ht
  have e2 := h2 ha ht ht
  simp only [Function.comp_apply] at e1 e2
  linarith

/-- A constant curve at an equilibrium is a solution. -/
@[powerlib_foundation] theorem isIntegralCurveOn_const {x : State 2} (hx : p.field x = 0)
    (s : Set ℝ) : Dynamics.IsIntegralCurveOn (fun _ => x) (fun _ y => p.field y) s := by
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
      monotoneOn_Icc_of_hasDerivAt (hcont _ _) (fun z _ => p.hasDerivAt_potential δ₀ z)
        (fun z hz => by linarith [p.Pm_lt_Pe_of_mem hk h hz])
    exact (hmono ⟨hs, hδ.2⟩ ⟨(p.deltaS_lt_deltaU hk h).le, le_rfl⟩ hδ.2).trans (le_max_right _ _)
  · have hanti : AntitoneOn (p.potential δ₀) (Icc δc p.deltaS) := by
      have := monotoneOn_Icc_of_hasDerivAt (h := fun z => -p.potential δ₀ z)
        (h' := fun z => -(p.Pe z - p.Pm)) (a := δc) (b := p.deltaS)
        (fun z hz => ((p.hasDerivAt_potential δ₀ z).continuousAt.neg).continuousWithinAt)
        (fun z _ => (p.hasDerivAt_potential δ₀ z).neg)
        (fun z hz => by linarith [p.Pe_lt_Pm_of_mem hk h ⟨by linarith [hz.1], hz.2⟩])
      intro u hu v hv huv
      have := this hu hv huv
      simp only at this
      linarith
    exact (hanti ⟨le_rfl, (hδ.1.trans hs.le)⟩ ⟨hδ.1, hs.le⟩ hδ.1).trans (le_max_left _ _)

/-! ## Exact first-swing equal-area criterion (`D = 0`) -/

/-- Sufficiency: if the clearing kinetic energy does not exceed the decelerating area up to the
unstable angle, the post-fault trajectory never goes beyond `δ_u`. -/
@[powerlib_domain] theorem firstSwing_le_deltaU (hM : 0 < p.M) (hD : p.D = 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {φ : ℝ → State 2} {tc δc ωc : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = mkState δc ωc) (hδc : δc ≤ p.deltaU)
    (hE : p.M / 2 * ωc ^ 2 ≤ ∫ s in δc..p.deltaU, (p.Pe s - p.Pm)) :
    ∀ t ∈ Ici tc, φ t 0 ≤ p.deltaU := by
  intro t ht
  by_contra hlt
  push Not at hlt
  have hcont : ContinuousOn (fun τ => φ τ 0) (Icc tc t) :=
    (p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self
  obtain ⟨ts, hts, hδs⟩ := intermediate_value_Icc ht hcont
    ⟨by simpa [h0] using hδc, hlt.le⟩
  simp only at hδs
  have hcons := p.energy_conserved hM.ne' hD δc hφ ts hts.1
  rw [h0] at hcons
  simp only [energy, mkState_zero, mkState_one, potential_self, add_zero, hδs] at hcons
  rw [← potential_eq_integral] at hE
  have hω : φ ts 1 = 0 := by
    have : p.M / 2 * φ ts 1 ^ 2 ≤ 0 := by linarith
    have h2 : 0 < p.M / 2 := by positivity
    have := nonpos_of_mul_nonpos_right this h2 |>.antisymm (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hsteq : φ ts = mkState p.deltaU 0 := state_ext (by simpa using hδs) (by simpa using hω)
  have heqf := p.field_mkState_deltaU hM.ne' hk h.le
  have huniq := Dynamics.eqOn_of_isIntegralCurveOn_Icc (f := fun _ x => p.field x)
    (fun _ => p.lipschitzWith_field) (hφ.mono (Icc_subset_Ici_iff hts.2 |>.mpr hts.1))
    (p.isIntegralCurveOn_const heqf (Icc ts t)) (by simpa using hsteq)
  have := huniq ⟨hts.2, le_rfl⟩
  simp only at this
  rw [this] at hlt
  simp at hlt

/-- Necessity: a forward swing (`ω_c > 0`) from the potential well whose kinetic energy exceeds
the decelerating area goes beyond `δ_u` in finite time. -/
@[powerlib_domain] theorem exists_gt_deltaU (hM : 0 < p.M) (hD : p.D = 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {φ : ℝ → State 2} {tc δc ωc : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = mkState δc ωc) (hwell : p.deltaU - 2 * Real.pi < δc) (hδc : δc ≤ p.deltaU)
    (hω : 0 < ωc) (hE : ∫ s in δc..p.deltaU, (p.Pe s - p.Pm) < p.M / 2 * ωc ^ 2) :
    ∃ t ∈ Ici tc, p.deltaU < φ t 0 := by
  by_contra hno
  push Not at hno
  rw [← potential_eq_integral] at hE
  set W0 := p.M / 2 * ωc ^ 2
  set c := min W0 (W0 - p.potential δc p.deltaU) with hcdef
  have hW0 : 0 < W0 := by positivity
  have hc : 0 < c := lt_min hW0 (by linarith)
  have hcons : ∀ t ∈ Ici tc, p.M / 2 * φ t 1 ^ 2 + p.potential δc (φ t 0) = W0 := by
    intro t ht
    have := p.energy_conserved hM.ne' hD δc hφ t ht
    rw [h0] at this
    simpa [energy] using this
  -- inside the window `[δ_c, δ_u]` the kinetic energy is at least `c`
  have hkin : ∀ t ∈ Ici tc, φ t 0 ∈ Icc δc p.deltaU → c ≤ p.M / 2 * φ t 1 ^ 2 := by
    intro t ht hwin
    have hU := p.potential_le_max hk h (δ₀ := δc) hwell hwin
    have := hcons t ht
    rw [potential_self] at hU
    rcases le_total (p.potential δc p.deltaU) 0 with hl | hl
    · rw [max_eq_left hl] at hU
      exact (min_le_left _ _).trans (by linarith)
    · rw [max_eq_right hl] at hU
      exact (min_le_right _ _).trans (by linarith)
  have hδ0 : φ tc 0 = δc := by simp [h0]
  have hω0 : φ tc 1 = ωc := by simp [h0]
  have hderiv : ∀ x ∈ Ioi tc, HasDerivAt (fun τ => φ τ 0) (φ x 1) x := by
    intro x hx
    have := p.coord_hasDerivAt hφ (mem_Ici.mpr (le_of_lt hx)) (Ici_mem_nhds hx) 0
    simpa using this
  -- the frequency deviation stays positive
  have hpos : ∀ T ∈ Ici tc, ∀ t ∈ Icc tc T, 0 < φ t 1 := by
    intro T hT
    apply pos_on_Icc_of_propagate ((p.coord_continuousOn hφ 1).mono Icc_subset_Ici_self)
      (by rw [hω0]; exact hω)
    intro t ht hbefore
    have hmono : MonotoneOn (fun τ => φ τ 0) (Icc tc t) :=
      monotoneOn_Icc_of_hasDerivAt ((p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self)
        (fun x hx => hderiv x hx.1) (fun x hx => (hbefore x ⟨hx.1.le, hx.2⟩).le)
    have hwin : φ t 0 ∈ Icc δc p.deltaU :=
      ⟨by simpa [hδ0] using hmono ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1.le,
        hno t ht.1.le⟩
    have hk2 := hkin t ht.1.le hwin
    have hne : φ t 1 ≠ 0 := by
      intro h0'; rw [h0'] at hk2; simp at hk2; linarith
    rcases lt_or_gt_of_ne hne with hneg | hp
    · exfalso
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1.le
        ((p.coord_continuousOn hφ 1).mono Icc_subset_Ici_self)
        ⟨hneg.le, by rw [hω0]; exact hω.le⟩
      simp only at hs0
      have hst : s ≠ t := by rintro rfl; linarith
      have := hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
      linarith
    · exact hp
  -- hence the angle grows at least linearly
  set w := Real.sqrt (2 * c / p.M) with hwdef
  have hw : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hωw : ∀ t ∈ Ici tc, w ≤ φ t 1 := by
    intro t ht
    have hmono : MonotoneOn (fun τ => φ τ 0) (Icc tc t) :=
      monotoneOn_Icc_of_hasDerivAt ((p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self)
        (fun x hx => hderiv x hx.1) (fun x hx => (hpos t ht x ⟨hx.1.le, hx.2.le⟩).le)
    have hwin : φ t 0 ∈ Icc δc p.deltaU :=
      ⟨by simpa [hδ0] using hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht, hno t ht⟩
    have hk2 := hkin t ht hwin
    have hp := hpos t ht t ⟨ht, le_rfl⟩
    rw [hwdef, ← Real.sqrt_sq hp.le]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hM]
    linarith
  set T := tc + (p.deltaU - δc) / w + 1
  have hT : T ∈ Ici tc := by
    show tc ≤ T
    have : 0 ≤ (p.deltaU - δc) / w := div_nonneg (by linarith) hw.le
    linarith
  have hlin : MonotoneOn (fun τ => φ τ 0 - w * τ) (Icc tc T) :=
    monotoneOn_Icc_of_hasDerivAt
      (((p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self).sub (by fun_prop))
      (fun x hx => (hderiv x hx.1).sub ((hasDerivAt_id x).const_mul w))
      (fun x hx => by simp only [mul_one]; linarith [hωw x hx.1.le])
  have := hlin ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  simp only [hδ0] at this
  have hTval : w * (T - tc) = (p.deltaU - δc) + w := by
    simp only [T]; field_simp; ring
  have := hno T hT
  nlinarith

/-- **Exact first-swing equal-area criterion** (`D = 0`, `ω_c > 0`, clearing angle in the
potential well `δ_u − 2π < δ_c ≤ δ_u`): the post-fault trajectory never exceeds the unstable
equilibrium angle iff `½ M ω_c² ≤ ∫_{δ_c}^{δ_u} (P_e − P_m) dδ`. -/
@[powerlib_domain] theorem firstSwing_iff (hM : 0 < p.M) (hD : p.D = 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {φ : ℝ → State 2} {tc δc ωc : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = mkState δc ωc) (hwell : p.deltaU - 2 * Real.pi < δc) (hδc : δc ≤ p.deltaU)
    (hω : 0 < ωc) :
    (∀ t ∈ Ici tc, φ t 0 ≤ p.deltaU) ↔
      p.M / 2 * ωc ^ 2 ≤ ∫ s in δc..p.deltaU, (p.Pe s - p.Pm) := by
  constructor
  · intro hle
    by_contra hgt
    push Not at hgt
    obtain ⟨t, ht, hlt⟩ := p.exists_gt_deltaU hM hD hk h hφ h0 hwell hδc hω hgt
    exact absurd (hle t ht) (not_le.mpr hlt)
  · exact p.firstSwing_le_deltaU hM hD hk h hφ h0 hδc

/-! ## Critical clearing time -/

/-- Bolted fault at the receiving bus (`P_e^f ≡ 0`, `D = 0`): the during-fault trajectory from
the pre-fault equilibrium `(δ₀, 0)` is `ω = (P_m/M)(t − t_f)`,
`δ = δ₀ + (P_m/(2M))(t − t_f)²`. -/
@[powerlib_domain] theorem boltedFault_trajectory (hM : 0 < p.M) (hD : p.D = 0)
    (hk₁ : p.k₁ = 0) (hk₂ : p.k₂ = 0) {φ : ℝ → State 2} {tf T δ₀ : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Icc tf T))
    (h0 : φ tf = mkState δ₀ 0) :
    ∀ t ∈ Icc tf T, φ t 1 = p.Pm / p.M * (t - tf) ∧
      φ t 0 = δ₀ + p.Pm / (2 * p.M) * (t - tf) ^ 2 := by
  have hacc : ∀ x : State 2, p.field x 1 = p.Pm / p.M := by
    intro x; simp [accel, Pe, hD, hk₁, hk₂]
  have hd := Dynamics.hasDerivWithinAt_Ici_of_isIntegralCurveOn hφ
  have hcont := hφ.continuousOn
  have hproj (j : Fin 2) := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State 2 →L[ℝ] ℝ)
  have h1 : ∀ t ∈ Icc tf T, φ t 1 - p.Pm / p.M * (t - tf) = φ tf 1 - p.Pm / p.M * (tf - tf) := by
    apply constant_of_has_deriv_right_zero
    · exact (((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
        hcont).sub (by fun_prop)
    · intro x hx
      have := ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
        x (hd x hx)).sub (((hasDerivAt_id x).sub_const tf).const_mul (p.Pm / p.M)).hasDerivWithinAt
      convert this using 1
      · funext y; simp [Function.comp_def]
      · simp [hacc]
  have hω : ∀ t ∈ Icc tf T, φ t 1 = p.Pm / p.M * (t - tf) := by
    intro t ht; have := h1 t ht; simp [h0] at this; linarith
  have h2 : ∀ t ∈ Icc tf T, φ t 0 - p.Pm / (2 * p.M) * (t - tf) ^ 2 =
      φ tf 0 - p.Pm / (2 * p.M) * (tf - tf) ^ 2 := by
    apply constant_of_has_deriv_right_zero
    · exact (((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
        hcont).sub (by fun_prop)
    · intro x hx
      have := ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
        x (hd x hx)).sub ((((hasDerivAt_id x).sub_const tf).pow 2).const_mul
          (p.Pm / (2 * p.M))).hasDerivWithinAt
      convert this using 1
      · funext y; simp [Function.comp_def]
      · simp only [PiLp.proj_apply, field_apply_zero, id_eq]
        rw [hω x ⟨hx.1, hx.2.le⟩]
        field_simp
        ring
  intro t ht
  refine ⟨hω t ht, ?_⟩
  have := h2 t ht
  simp [h0] at this
  linarith

/-- Exact critical clearing time for a bolted fault (`P_e^f ≡ 0`, `D = 0`, `P_m > 0`): the
during-fault angle reaches `δ_cc ≥ δ₀` exactly at `t = t_f + √(2M(δ_cc − δ₀)/P_m)`. -/
@[powerlib_domain] theorem boltedFault_clearingTime (hM : 0 < p.M) (hD : p.D = 0)
    (hk₁ : p.k₁ = 0) (hk₂ : p.k₂ = 0) (hPm : 0 < p.Pm) {φ : ℝ → State 2} {tf T δ₀ δcc : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Icc tf T))
    (h0 : φ tf = mkState δ₀ 0) (hcc : δ₀ ≤ δcc) {t : ℝ} (ht : t ∈ Icc tf T) :
    φ t 0 = δcc ↔ t = tf + Real.sqrt (2 * p.M * (δcc - δ₀) / p.Pm) := by
  rw [(p.boltedFault_trajectory hM hD hk₁ hk₂ hφ h0 t ht).2]
  have hτ : 0 ≤ t - tf := by linarith [ht.1]
  constructor
  · intro he
    have hsq : (t - tf) ^ 2 = 2 * p.M * (δcc - δ₀) / p.Pm := by
      field_simp; field_simp at he; linarith
    have := Real.sqrt_sq hτ
    rw [hsq] at this
    linarith
  · intro he
    have hs : (t - tf) = Real.sqrt (2 * p.M * (δcc - δ₀) / p.Pm) := by linarith
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * p.M * (δcc - δ₀) / p.Pm by
      apply div_nonneg _ hPm.le; nlinarith)
    rw [hs, hsq]
    field_simp
    ring

/-- Clearing-time bound for a general during-fault curve (`D = 0`): if `P_e^f ≤ p_max < P_m`
on `[δ₀, δ_cc]`, a trajectory starting from `(δ₀, 0)` cannot stay inside the angle window
`[δ₀, δ_cc]` for longer than `√(2M(δ_cc − δ₀)/(P_m − p_max))`. -/
@[powerlib_domain] theorem time_in_window_le (hM : 0 < p.M) (hD : p.D = 0) {pmax δ₀ δcc : ℝ}
    (hgap : pmax < p.Pm) (hbound : ∀ δ ∈ Icc δ₀ δcc, p.Pe δ ≤ pmax) {φ : ℝ → State 2}
    {tf T : ℝ} (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Icc tf T))
    (h0 : φ tf = mkState δ₀ 0) {t : ℝ} (ht : t ∈ Icc tf T)
    (hwin : ∀ s ∈ Icc tf t, φ s 0 ∈ Icc δ₀ δcc) :
    t - tf ≤ Real.sqrt (2 * p.M * (δcc - δ₀) / (p.Pm - pmax)) := by
  set a := (p.Pm - pmax) / p.M with hadef
  have ha : 0 < a := div_pos (by linarith) hM
  have hsub : Icc tf t ⊆ Icc tf T := Icc_subset_Icc_right ht.2
  have hφ' := hφ.mono hsub
  have hder : ∀ x ∈ Ioo tf t, ∀ j, HasDerivAt (fun τ => φ τ j) (p.field (φ x) j) x :=
    fun x hx j => p.coord_hasDerivAt hφ' ⟨hx.1.le, hx.2.le⟩ (Icc_mem_nhds hx.1 hx.2) j
  have hc (j : Fin 2) : ContinuousOn (fun τ => φ τ j) (Icc tf t) := p.coord_continuousOn hφ' j
  have hω : MonotoneOn (fun τ => φ τ 1 - a * (τ - tf)) (Icc tf t) := by
    apply monotoneOn_Icc_of_hasDerivAt ((hc 1).sub (by fun_prop))
      (fun x hx => (hder x hx 1).sub (((hasDerivAt_id x).sub_const tf).const_mul a))
    intro x hx
    have hb := hbound _ (hwin x ⟨hx.1.le, hx.2.le⟩)
    simp only [field_apply_one, accel, hD, zero_mul, sub_zero, mul_one]
    rw [hadef, ← sub_div]
    exact div_nonneg (by linarith) hM.le
  have hωlow : ∀ x ∈ Icc tf t, a * (x - tf) ≤ φ x 1 := by
    intro x hx
    have := hω ⟨le_rfl, ht.1⟩ hx hx.1
    simp [h0] at this
    linarith
  have hδ : MonotoneOn (fun τ => φ τ 0 - a / 2 * (τ - tf) ^ 2) (Icc tf t) := by
    apply monotoneOn_Icc_of_hasDerivAt ((hc 0).sub (by fun_prop))
      (fun x hx => (hder x hx 0).sub ((((hasDerivAt_id x).sub_const tf).pow 2).const_mul (a / 2)))
    intro x hx
    have := hωlow x ⟨hx.1.le, hx.2.le⟩
    simp only [field_apply_zero, id_eq]
    norm_num
    linarith
  have hfin := hδ ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  simp [h0] at hfin
  have hupper := (hwin t ⟨ht.1, le_rfl⟩).2
  have hτ : 0 ≤ t - tf := by linarith [ht.1]
  rw [← Real.sqrt_sq hτ]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ (by linarith)]
  have : (t - tf) ^ 2 * (p.Pm - pmax) = 2 * p.M * (a / 2 * (t - tf) ^ 2) := by
    rw [hadef]; field_simp
  rw [this]
  nlinarith

end SwingParams
end powerlib.Synchronous
