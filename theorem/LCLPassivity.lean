import theorem.LCLStability

noncomputable section
namespace powerlib.LCL
open Set Filter
open scoped Topology

def physicalWeights (m : Circuit) : SymmetricMatrix :=
  ⟨m.first.inductance.val, 0, 0, m.capacitance.val, 0, m.second.inductance.val⟩

@[powerlib_foundation, aesop safe apply] theorem physicalEnergy_positive (m : Circuit) (x : State) (hx : x ≠ 0) :
    0 < quadraticEnergy (physicalWeights m) x := by
  apply energy_positive
  · exact m.first.inductance.property
  · dsimp [physicalWeights, SymmetricMatrix.minor2]
    nlinarith [mul_pos m.first.inductance.property m.capacitance.property]
  · dsimp [physicalWeights, SymmetricMatrix.det]
    nlinarith [mul_pos m.first.inductance.property
      (mul_pos m.capacitance.property m.second.inductance.property)]
  · exact (state_ne_zero_iff x).mp hx

@[powerlib_domain] theorem physicalEnergy_derivative {m : Circuit} {u vg : ℝ} {e : State}
    {x : ℝ → State} (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => quadraticEnergy (physicalWeights m) (x s - e))
      (-2 * m.first.resistance * ((x t - e) 0) ^ 2 -
        2 * m.second.resistance * ((x t - e) 2) ^ 2) (Ici 0) t := by
  have h := quadraticEnergy_derivative (physicalWeights m) ((trajectory_shift he hx) t ht)
  convert! h using 1
  dsimp [StateSpace.vectorField]
  rw [same_dynamics]
  dsimp [energyDerivative, physicalWeights]
  field_simp [ne_of_gt m.first.inductance.property, ne_of_gt m.second.inductance.property,
    ne_of_gt m.capacitance.property]
  ring

@[powerlib_domain] theorem passive_energy_nonincreasing {m : Circuit} (hp : m.Passive)
    {u vg : ℝ} {e : State} {x : ℝ → State}
    (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x) :
    AntitoneOn (fun t => quadraticEnergy (physicalWeights m) (x t - e)) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun s hs => (physicalEnergy_derivative he hx hs).continuousWithinAt)
    (fun s hs => (physicalEnergy_derivative he hx (interior_subset hs)).mono interior_subset)
  intro s _
  exact sub_nonpos.mpr (le_trans
    (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hp.1]) (sq_nonneg _))
    (mul_nonneg (by nlinarith [hp.2]) (sq_nonneg _)))

@[powerlib_domain, aesop unsafe 80% apply] theorem passive_lyapunovStable {m : Circuit} (hp : m.Passive)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : LyapunovStable m u vg e := by
  obtain ⟨α, hα, β, hβα, hb⟩ := powerlib.quadratic_bounds
    (quadraticEnergy (physicalWeights m)) (quadraticEnergy_continuous _)
    (quadraticEnergy_smul _) (physicalEnergy_positive m)
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
  have hen := passive_energy_nonincreasing hp he hx (by simp) ht ht
  have hl := (hb (x t - e)).1
  have hu := (hb (x 0 - e)).2
  have hsq := mul_le_mul_of_nonneg_right hαC (sq_nonneg ‖x 0 - e‖)
  have hn : ‖x t - e‖ ≤ C * ‖x 0 - e‖ := by
    have hsq' : α * ‖x t - e‖ ^ 2 ≤ α * (C * ‖x 0 - e‖) ^ 2 := by
      nlinarith only [hl, hen, hu, hsq]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ((mul_le_mul_iff_right₀ hα).mp hsq')
  exact hn.trans_lt (by simpa [mul_comm] using (lt_div_iff₀ hC).mp h0)

@[powerlib_domain] theorem lossless_energy_conserved {m : Circuit}
    (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0)
    {u vg : ℝ} {e : State} {x : ℝ → State}
    (he : IsEquilibrium m u vg e) (hx : IsTrajectory m u vg x) {t : ℝ} (ht : 0 ≤ t) :
    quadraticEnergy (physicalWeights m) (x t - e) = quadraticEnergy (physicalWeights m) (x 0 - e) := by
  have hd : ∀ s ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun r => quadraticEnergy (physicalWeights m) (x r - e)) 0 (Ici 0) s := by
    intro s hs
    simpa [h1, h2] using physicalEnergy_derivative he hx hs
  have hb := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hd (fun _ _ => by simp) (show (0 : ℝ) ∈ Ici 0 by simp) ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))

@[powerlib_domain, aesop safe apply] theorem constant_trajectory {m : Circuit} {u vg : ℝ} {e : State}
    (he : IsEquilibrium m u vg e) : IsTrajectory m u vg (fun _ => e) := by
  intro t _
  rw [he]
  exact (hasDerivAt_const t e).hasDerivWithinAt

@[powerlib_domain] theorem lossless_equilibrium_iff (m : Circuit)
    (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0) (u vg : ℝ) (e : State) :
    IsEquilibrium m u vg e ↔ e 0 = e 2 ∧ e 1 = u ∧ u = vg := by
  simp only [IsEquilibrium, StateSpace.vectorField, same_dynamics, h1, h2, zero_mul, sub_zero]
  constructor
  · intro he
    have ha := congrFun he 0
    have hb := congrFun he 1
    have hc := congrFun he 2
    simp [div_eq_zero_iff, ne_of_gt m.first.inductance.property] at ha
    simp [div_eq_zero_iff, ne_of_gt m.capacitance.property] at hb
    simp [div_eq_zero_iff, ne_of_gt m.second.inductance.property] at hc
    exact ⟨sub_eq_zero.mp hb, (sub_eq_zero.mp ha).symm, by linarith⟩
  · rintro ⟨ha, hb, hc⟩
    ext j
    fin_cases j <;> simp [ha, hb, hc]

@[powerlib_domain, aesop norm forward (immediate := [h1, h2, he])]
theorem lossless_not_asymptoticallyStable {m : Circuit}
    (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : ¬ AsymptoticallyStable m u vg e := by
  intro hs
  obtain ⟨δ, hδ, ha⟩ := hs.2
  let k := δ / 2
  let v : State := ![1, 0, 1]
  let q : State := e + k • v
  have he' := (lossless_equilibrium_iff m h1 h2 u vg e).mp he
  have hq : IsEquilibrium m u vg q := (lossless_equilibrium_iff m h1 h2 u vg q).mpr (by
    dsimp [q, v]
    exact ⟨by linarith [he'.1], by simpa using he'.2.1, he'.2.2⟩)
  have hv : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
    intro j
    fin_cases j <;> norm_num [v])
  have hk : 0 < k := by dsimp [k]; linarith
  have hsmall : ‖q - e‖ < δ := by
    have hqe : q - e = k • v := by dsimp [q]; abel
    rw [hqe, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    exact (mul_le_mul_of_nonneg_left hv hk.le).trans_lt (by dsimp [k]; linarith)
  have hl := ha (fun _ => q) (constant_trajectory hq) hsmall
  have hqe : q = e := tendsto_nhds_unique tendsto_const_nhds hl
  have hzero := congrFun hqe 0
  dsimp [q, v] at hzero
  linarith

@[powerlib_domain] theorem asymptoticallyStable_requires_damping {m : Circuit}
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) (hs : AsymptoticallyStable m u vg e) :
    m.Damped := by
  by_contra hd
  simp only [Circuit.Damped, not_or, not_not] at hd
  exact lossless_not_asymptoticallyStable hd.1 hd.2 he hs

@[powerlib_domain] theorem passive_equilibrium_exists {m : Circuit}
    (hp : m.Passive) (hd : m.Damped) (u vg : ℝ) :
    IsEquilibrium m u vg (equilibrium m u vg) :=
  equilibrium_exists (ne_of_gt (passive_hurwitz m hp hd).2.2.1) u vg

@[powerlib_domain] theorem lossless_not_globallyAsymptoticallyStable {m : Circuit}
    (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    ¬ GloballyAsymptoticallyStable m u vg e := by
  intro h
  exact lossless_not_asymptoticallyStable h1 h2 he
    ⟨h.1, 1, zero_lt_one, fun x hx _ => h.2 x hx⟩

@[powerlib_domain] theorem lossless_not_globallyExponentiallyStable {m : Circuit}
    (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    ¬ GloballyExponentiallyStable m u vg e := by
  intro h
  exact lossless_not_globallyAsymptoticallyStable h1 h2 he
    ⟨lyapunovStable_of_globallyExponentiallyStable h,
      fun _ hx => trajectory_tendsto_of_globallyExponentiallyStable h hx⟩

end powerlib.LCL
