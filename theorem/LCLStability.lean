import theorem.LCLTrajectory
import theorem.Lyapunov

noncomputable section
namespace powerlib.LCL
open Set Filter
open scoped Topology

def quadraticEnergy (p : SymmetricMatrix) (x : State) : ℝ := energy p (x 0) (x 1) (x 2)
def squaredSize (x : State) : ℝ := (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2

@[simp, powerlib_foundation] theorem quadraticEnergy_zero (p : SymmetricMatrix) :
    quadraticEnergy p 0 = 0 := by simp [quadraticEnergy, energy]

@[powerlib_foundation] theorem quadraticEnergy_continuous (p : SymmetricMatrix) :
    Continuous (quadraticEnergy p) := by
  unfold quadraticEnergy energy
  fun_prop

@[powerlib_foundation] theorem quadraticEnergy_smul (p : SymmetricMatrix) (a : ℝ) (x : State) :
    quadraticEnergy p (a • x) = a ^ 2 * quadraticEnergy p x := by
  simp [quadraticEnergy, energy]
  ring

@[powerlib_foundation] theorem state_ne_zero_iff (x : State) :
    x ≠ 0 ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
  constructor
  · intro hx
    by_contra h
    push Not at h
    apply hx
    ext j
    fin_cases j <;> simp [h.1, h.2.1, h.2.2]
  · rintro (h | h | h) he <;> simp [he] at h

@[powerlib_foundation] theorem squaredSize_nonneg (x : State) : 0 ≤ squaredSize x := by
  unfold squaredSize
  positivity

@[powerlib_foundation] theorem norm_sq_le_squaredSize (x : State) : ‖x‖ ^ 2 ≤ squaredSize x := by
  have hq := squaredSize_nonneg x
  have hs := Real.sq_sqrt hq
  have hn : ‖x‖ ≤ Real.sqrt (squaredSize x) := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (by
    intro j
    have hj : (x j) ^ 2 ≤ squaredSize x := by
      fin_cases j <;> dsimp [squaredSize] <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (x j), abs_nonneg (x j), Real.sqrt_nonneg (squaredSize x)])
  nlinarith [norm_nonneg x, Real.sqrt_nonneg (squaredSize x)]

@[powerlib_foundation] theorem Accepted.energy_bounds {m : Circuit} (c : Accepted m) :
    ∃ α > 0, ∃ β ≥ α, ∀ x : State,
      α * ‖x‖ ^ 2 ≤ quadraticEnergy c.p x ∧ quadraticEnergy c.p x ≤ β * ‖x‖ ^ 2 :=
  powerlib.quadratic_bounds (quadraticEnergy c.p) (quadraticEnergy_continuous c.p)
    (quadraticEnergy_smul c.p) (fun x hx => c.positive _ _ _ ((state_ne_zero_iff x).mp hx))

@[powerlib_foundation] theorem quadraticEnergy_derivative
    (p : SymmetricMatrix) {x : ℝ → State} {dx : State} {t : ℝ}
    (hx : HasDerivWithinAt x dx (Ici 0) t) :
    HasDerivWithinAt (fun s => quadraticEnergy p (x s))
      (energyDerivative p (x t 0) (x t 1) (x t 2) (dx 0) (dx 1) (dx 2)) (Ici 0) t := by
  have hd (j : Fin 3) : HasDerivWithinAt (fun s => x s j) (dx j) (Ici 0) t := by
    exact (ContinuousLinearMap.proj j : State →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hx
  have h11 := ((hd 0).pow 2).const_mul p.p11
  have h12 := ((hd 0).const_mul (2 * p.p12)).mul (hd 1)
  have h13 := ((hd 0).const_mul (2 * p.p13)).mul (hd 2)
  have h22 := ((hd 1).pow 2).const_mul p.p22
  have h23 := ((hd 1).const_mul (2 * p.p23)).mul (hd 2)
  have h33 := ((hd 2).pow 2).const_mul p.p33
  have h := ((((h11.add h12).add h13).add h22).add h23).add h33
  convert! h using 1
  dsimp [energyDerivative]
  ring

@[powerlib_domain, aesop safe apply] theorem Accepted.energy_derivative {m : Circuit} (c : Accepted m)
    {u vg : ℝ} {e : State} {x : ℝ → State}
    (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => quadraticEnergy c.p (x s - e))
      (-squaredSize (x t - e)) (Ici 0) t := by
  have h := quadraticEnergy_derivative c.p ((trajectory_shift he hx) t ht)
  simpa [StateSpace.vectorField, c.dissipation, squaredSize] using h

@[powerlib_domain] theorem Accepted.trajectory_energy_decay {m : Circuit} (c : Accepted m)
    {α β : ℝ} (hβ : 0 < β)
    (hb : ∀ y : State, α * ‖y‖ ^ 2 ≤ quadraticEnergy c.p y ∧ quadraticEnergy c.p y ≤ β * ‖y‖ ^ 2)
    {u vg : ℝ} {e : State} {x : ℝ → State}
    (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x) {t : ℝ} (ht : 0 ≤ t) :
    quadraticEnergy c.p (x t - e) ≤ quadraticEnergy c.p (x 0 - e) * Real.exp (-t / β) := by
  apply powerlib.exponential_bound_of_derivative hβ (fun s hs => c.energy_derivative he hx hs) ?_ ht
  intro s _
  have h := (div_le_iff₀ hβ).mpr (by simpa [mul_comm] using (hb (x s - e)).2)
  have hn := norm_sq_le_squaredSize (x s - e)
  linarith

def LyapunovStable (m : Circuit) (u vg : ℝ) (e : State) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, IsTrajectory m u vg x → ‖x 0 - e‖ < δ →
    ∀ t ≥ 0, ‖x t - e‖ < ε

def AsymptoticallyStable (m : Circuit) (u vg : ℝ) (e : State) : Prop :=
  LyapunovStable m u vg e ∧ ∃ δ > 0, ∀ x, IsTrajectory m u vg x → ‖x 0 - e‖ < δ →
    Tendsto x atTop (𝓝 e)

def GloballyAsymptoticallyStable (m : Circuit) (u vg : ℝ) (e : State) : Prop :=
  LyapunovStable m u vg e ∧ ∀ x, IsTrajectory m u vg x → Tendsto x atTop (𝓝 e)

def GloballyExponentiallyStable (m : Circuit) (u vg : ℝ) (e : State) : Prop :=
  ∃ C ≥ (1 : ℝ), ∃ rate > 0, ∀ x, IsTrajectory m u vg x → ∀ t ≥ 0,
    ‖x t - e‖ ≤ C * ‖x 0 - e‖ * Real.exp (-rate * t)

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.globallyExponentiallyStable {m : Circuit} (c : Accepted m)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    GloballyExponentiallyStable m u vg e := by
  obtain ⟨α, hα, β, hβα, hb⟩ := c.energy_bounds
  have hβ : 0 < β := hα.trans_le hβα
  let C := β / α + 1
  have hratio : 1 ≤ β / α := (le_div_iff₀ hα).mpr (by simpa using hβα)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hαC : β ≤ α * C ^ 2 := by
    have heq : α * (β / α) = β := mul_div_cancel₀ β (ne_of_gt hα)
    dsimp [C]
    nlinarith [sq_nonneg (β / α)]
  refine ⟨C, hC, 1 / (2 * β), by positivity, ?_⟩
  intro x hx t ht
  have henergy := c.trajectory_energy_decay hβ hb he hx ht
  have hlow := (hb (x t - e)).1
  have hupp := (hb (x 0 - e)).2
  have hexp : Real.exp (-t / β) = (Real.exp (-(1 / (2 * β)) * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h0 : α * ‖x t - e‖ ^ 2 ≤ β * ‖x 0 - e‖ ^ 2 * Real.exp (-t / β) :=
    hlow.trans (henergy.trans (mul_le_mul_of_nonneg_right hupp (Real.exp_pos _).le))
  rw [hexp] at h0
  have h1 := mul_le_mul_of_nonneg_right hαC
    (mul_nonneg (sq_nonneg ‖x 0 - e‖) (sq_nonneg (Real.exp (-(1 / (2 * β)) * t))))
  have hbound : 0 ≤ C * ‖x 0 - e‖ * Real.exp (-(1 / (2 * β)) * t) := by positivity
  have hsquare : α * ‖x t - e‖ ^ 2 ≤
      α * (C * ‖x 0 - e‖ * Real.exp (-(1 / (2 * β)) * t)) ^ 2 := by
    nlinarith only [h0, h1]
  exact (sq_le_sq₀ (norm_nonneg (x t - e)) hbound).mp ((mul_le_mul_iff_right₀ hα).mp hsquare)

@[powerlib_domain] theorem lyapunovStable_of_globallyExponentiallyStable
    {m : Circuit} {u vg : ℝ} {e : State} (h : GloballyExponentiallyStable m u vg e) :
    LyapunovStable m u vg e := by
  obtain ⟨C, hC, rate, hr, h⟩ := h
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  intro ε hε
  refine ⟨ε / C, div_pos hε hCp, ?_⟩
  intro x hx h0 t ht
  have hsmall : C * ‖x 0 - e‖ < ε := by
    simpa [mul_comm] using (lt_div_iff₀ hCp).mp h0
  have hexp : Real.exp (-rate * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact (h x hx t ht).trans_lt ((mul_le_of_le_one_right (by positivity) hexp).trans_lt hsmall)

@[powerlib_domain] theorem trajectory_tendsto_of_globallyExponentiallyStable
    {m : Circuit} {u vg : ℝ} {e : State} (h : GloballyExponentiallyStable m u vg e)
    {x : ℝ → State} (hx : IsTrajectory m u vg x) : Tendsto x atTop (𝓝 e) := by
  obtain ⟨C, _, rate, hr, h⟩ := h
  have hexp : Tendsto (fun t : ℝ => Real.exp (-rate * t)) atTop (𝓝 0) := by
    simpa only [neg_mul] using! Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hr)
  have hu : Tendsto (fun t : ℝ => C * ‖x 0 - e‖ * Real.exp (-rate * t)) atTop (𝓝 0) := by
    simpa using hexp.const_mul (C * ‖x 0 - e‖)
  have hn : Tendsto (fun t => ‖x t - e‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact h x hx t ht) hu
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.lyapunovStable {m : Circuit} (c : Accepted m)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : LyapunovStable m u vg e :=
  lyapunovStable_of_globallyExponentiallyStable (c.globallyExponentiallyStable he)

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.trajectory_tendsto {m : Circuit} (c : Accepted m)
    {u vg : ℝ} {e : State} {x : ℝ → State}
    (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x) : Tendsto x atTop (𝓝 e) :=
  trajectory_tendsto_of_globallyExponentiallyStable (c.globallyExponentiallyStable he) hx

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.globallyAsymptoticallyStable {m : Circuit} (c : Accepted m)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : GloballyAsymptoticallyStable m u vg e :=
  ⟨c.lyapunovStable he, fun _ hx => c.trajectory_tendsto he hx⟩

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.asymptoticallyStable {m : Circuit} (c : Accepted m)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : AsymptoticallyStable m u vg e :=
  ⟨c.lyapunovStable he, 1, zero_lt_one, fun _ hx _ => c.trajectory_tendsto he hx⟩

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.equilibrium_exists {m : Circuit} (c : Accepted m) (u vg : ℝ) :
    IsEquilibrium m u vg (equilibrium m u vg) :=
  powerlib.LCL.equilibrium_exists (ne_of_gt c.a0_pos) u vg

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.trajectory_exists {m : Circuit} (c : Accepted m)
    (u vg : ℝ) (initial : State) : ∃ x, IsTrajectory m u vg x ∧ x 0 = initial :=
  powerlib.LCL.trajectory_exists (c.equilibrium_exists u vg) initial

end powerlib.LCL
