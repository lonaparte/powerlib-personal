import dependencies.Mathlib
import theorem.Lyapunov

noncomputable section
namespace powerlib.Passivity
open Set Filter MeasureTheory
open scoped Topology

structure System (E : Type*) (ι : Type*) where
  field : E → (ι → ℝ) → E
  output : E → (ι → ℝ) → (ι → ℝ)

variable {E ι : Type*} [Fintype ι]

def supply (s : System E ι) (x : E) (u : ι → ℝ) : ℝ :=
  ∑ i, u i * s.output x u i

@[simp, powerlib_foundation] theorem supply_zero (s : System E ι) (x : E) :
    supply s x 0 = 0 := by simp [supply]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsTrajectory (s : System E ι) (u : ℝ → (ι → ℝ)) (x : ℝ → E) : Prop :=
  ∀ t ∈ Ici (0 : ℝ),
    HasDerivWithinAt x (s.field (x t) (u t)) (Ici 0) t

def IsEquilibrium (s : System E ι) (e : E) : Prop := s.field e 0 = 0

def LyapunovStable (s : System E ι) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, IsTrajectory s (fun _ => 0) x → ‖x 0‖ < δ →
    ∀ t ≥ 0, ‖x t‖ < ε

def PassiveWithStorage (s : System E ι) (energy : E → ℝ) : Prop :=
  (∀ y, 0 ≤ energy y) ∧
    ∀ {u : ℝ → (ι → ℝ)} {x : ℝ → E}, IsTrajectory s u x →
      ∀ {t : ℝ}, 0 ≤ t →
        IntervalIntegrable (fun τ => supply s (x τ) (u τ)) volume 0 t →
          energy (x t) - energy (x 0) ≤ ∫ τ in (0 : ℝ)..t, supply s (x τ) (u τ)

structure DissipativeStorage (s : System E ι) where
  energy : E → ℝ
  rate : E → (ι → ℝ) → ℝ
  energyDerivative : ∀ {u : ℝ → (ι → ℝ)} {x : ℝ → E}, IsTrajectory s u x →
    ∀ {t : ℝ}, 0 ≤ t →
      HasDerivWithinAt (fun τ => energy (x τ)) (rate (x t) (u t)) (Ici 0) t
  dissipation : ∀ x u, rate x u ≤ supply s x u

structure QuadraticStorage (s : System E ι) extends DissipativeStorage s where
  continuous : Continuous energy
  homogeneous : ∀ (a : ℝ) (x : E), energy (a • x) = a ^ 2 * energy x
  positive : ∀ x ≠ 0, 0 < energy x

@[powerlib_domain] theorem DissipativeStorage.integral_dissipation
    {s : System E ι} (V : DissipativeStorage s)
    {u : ℝ → (ι → ℝ)} {x : ℝ → E} (hx : IsTrajectory s u x)
    {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun τ => supply s (x τ) (u τ)) volume 0 t) :
    V.energy (x t) - V.energy (x 0) ≤ ∫ τ in (0 : ℝ)..t, supply s (x τ) (u τ) := by
  apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht
    (fun τ hτ => (V.energyDerivative hx hτ.1).continuousWithinAt.mono
      (fun _ h => h.1))
    (fun τ hτ => (V.energyDerivative hx hτ.1.le).mono
      (fun r hr => hτ.1.le.trans hr.le))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le ht).mp hsupply)
  intro τ _
  exact V.dissipation (x τ) (u τ)

@[powerlib_domain] theorem PassiveWithStorage.zeroInput_energy_le
    {s : System E ι} {energy : E → ℝ} (hp : PassiveWithStorage s energy)
    {x : ℝ → E} (hx : IsTrajectory s (fun _ => 0) x)
    {t : ℝ} (ht : 0 ≤ t) : energy (x t) ≤ energy (x 0) := by
  have hpower : IntervalIntegrable (fun τ => supply s (x τ) 0) volume 0 t := by
    simp only [supply_zero]
    exact intervalIntegrable_const
  have h := hp.2 hx ht hpower
  exact sub_nonpos.mp (by simpa only [supply_zero, intervalIntegral.integral_zero] using h)

@[powerlib_domain] theorem DissipativeStorage.zeroInput_energy_antitone
    {s : System E ι} (V : DissipativeStorage s)
    {x : ℝ → E} (hx : IsTrajectory s (fun _ => 0) x) :
    AntitoneOn (fun t => V.energy (x t)) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun τ hτ => (V.energyDerivative hx hτ).continuousWithinAt)
    (fun τ hτ => (V.energyDerivative hx (interior_subset hτ)).mono interior_subset)
  intro τ _
  simpa only [supply_zero] using V.dissipation (x τ) 0

@[powerlib_domain] theorem DissipativeStorage.trajectory_norm_bound
    {s : System E ι} (V : DissipativeStorage s)
    {α β C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hαC : β ≤ α * C ^ 2)
    (hb : ∀ y : E, α * ‖y‖ ^ 2 ≤ V.energy y ∧ V.energy y ≤ β * ‖y‖ ^ 2)
    {x : ℝ → E} (hx : IsTrajectory s (fun _ => 0) x)
    {t : ℝ} (ht : 0 ≤ t) : ‖x t‖ ≤ C * ‖x 0‖ := by
  have hen := V.zeroInput_energy_antitone hx (by simp) ht ht
  have hl := (hb (x t)).1
  have hu := (hb (x 0)).2
  have hsq := mul_le_mul_of_nonneg_right hαC (sq_nonneg ‖x 0‖)
  have hsq' : α * ‖x t‖ ^ 2 ≤ α * (C * ‖x 0‖) ^ 2 := by
    nlinarith only [hl, hen, hu, hsq]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    ((mul_le_mul_iff_right₀ hα).mp hsq')

@[powerlib_domain] theorem PassiveWithStorage.lyapunovStable_of_bounds
    {s : System E ι} {energy : E → ℝ} (hp : PassiveWithStorage s energy)
    (_he : IsEquilibrium s 0)
    {α β : ℝ} (hα : 0 < α) (hβα : α ≤ β)
    (hb : ∀ y : E, α * ‖y‖ ^ 2 ≤ energy y ∧ energy y ≤ β * ‖y‖ ^ 2) :
    LyapunovStable s := by
  let C := β / α + 1
  have hratio : 1 ≤ β / α := (le_div_iff₀ hα).mpr (by simpa using hβα)
  have hC : 0 < C := by dsimp [C]; linarith
  have hαC : β ≤ α * C ^ 2 := by
    have heq : α * (β / α) = β := mul_div_cancel₀ β (ne_of_gt hα)
    dsimp [C]
    nlinarith [sq_nonneg (β / α)]
  intro ε hε
  refine ⟨ε / C, div_pos hε hC, ?_⟩
  intro x hx h0 t ht
  have hen := hp.zeroInput_energy_le hx ht
  have hl := (hb (x t)).1
  have hu := (hb (x 0)).2
  have hsq := mul_le_mul_of_nonneg_right hαC (sq_nonneg ‖x 0‖)
  have hsq' : α * ‖x t‖ ^ 2 ≤ α * (C * ‖x 0‖) ^ 2 := by
    nlinarith only [hl, hen, hu, hsq]
  have hnorm : ‖x t‖ ≤ C * ‖x 0‖ :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mp
      ((mul_le_mul_iff_right₀ hα).mp hsq')
  exact hnorm.trans_lt
    (by simpa [mul_comm] using (lt_div_iff₀ hC).mp h0)

@[powerlib_domain] theorem DissipativeStorage.lyapunovStable_of_bounds
    {s : System E ι} (V : DissipativeStorage s)
    (he : IsEquilibrium s 0)
    {α β : ℝ} (hα : 0 < α) (hβα : α ≤ β)
    (hb : ∀ y : E, α * ‖y‖ ^ 2 ≤ V.energy y ∧ V.energy y ≤ β * ‖y‖ ^ 2) :
    LyapunovStable s := by
  have hp : PassiveWithStorage s V.energy := by
    refine ⟨fun y => (mul_nonneg hα.le (sq_nonneg ‖y‖)).trans (hb y).1, ?_⟩
    intro u x hx t ht hpower
    exact V.integral_dissipation hx ht hpower
  exact hp.lyapunovStable_of_bounds he hα hβα hb

@[powerlib_foundation] theorem QuadraticStorage.energy_nonneg
    {s : System E ι} (V : QuadraticStorage s) (y : E) : 0 ≤ V.energy y := by
  have hzero : V.energy 0 = 0 := by simpa using V.homogeneous 0 0
  by_cases hy : y = 0
  · simp [hy, hzero]
  · exact (V.positive y hy).le

@[powerlib_domain, aesop norm forward (immediate := [V])] theorem QuadraticStorage.passiveWithStorage
    {s : System E ι} (V : QuadraticStorage s) : PassiveWithStorage s V.energy := by
  refine ⟨V.energy_nonneg, ?_⟩
  intro u x hx t ht hpower
  exact V.toDissipativeStorage.integral_dissipation hx ht hpower

@[powerlib_domain] theorem QuadraticStorage.integral_passivity
    {s : System E ι} (V : QuadraticStorage s)
    {u : ℝ → (ι → ℝ)} {x : ℝ → E} (hx : IsTrajectory s u x)
    {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun τ => supply s (x τ) (u τ)) volume 0 t) :
    V.energy (x t) - V.energy (x 0) ≤ ∫ τ in (0 : ℝ)..t, supply s (x τ) (u τ) :=
  V.passiveWithStorage.2 hx ht hsupply

variable [FiniteDimensional ℝ E] [Nontrivial E]

@[powerlib_foundation] theorem QuadraticStorage.energy_bounds
    {s : System E ι} (V : QuadraticStorage s) :
    ∃ α > 0, ∃ β ≥ α, ∀ y : E,
      α * ‖y‖ ^ 2 ≤ V.energy y ∧ V.energy y ≤ β * ‖y‖ ^ 2 :=
  powerlib.quadratic_bounds V.energy V.continuous V.homogeneous V.positive

@[powerlib_domain, aesop norm forward (immediate := [V, he])] theorem QuadraticStorage.lyapunovStable
    {s : System E ι} (V : QuadraticStorage s) (he : IsEquilibrium s 0) :
    LyapunovStable s := by
  obtain ⟨α, hα, β, hβα, hb⟩ := V.energy_bounds
  exact V.passiveWithStorage.lyapunovStable_of_bounds he hα hβα hb

end powerlib.Passivity
