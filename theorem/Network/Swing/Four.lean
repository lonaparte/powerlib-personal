import theorem.Network.Swing.Degenerate

/-! # Networked swing equations: four machines

Cut and flat-direction tests for local asymptotic stability of the swing network (every number of
machines), and exactness of the local asymptotic translation for four machines with at most four
lines.

Model boundary.
* Exactly the model of `theorem/Network/Swing/Basic.lean` (`Swing.family`): `n + 1` machines,
  reduced state `(δ, ω)`, positive inertia and damping, constant power, symmetric nonnegative
  lossless couplings, constant voltages; no governor, AVR, PLL, converter control, delay or PWM;
  continuous time. Statements concern the selected angle profile `θ*` of a model. The
  four-machine results are for `n = 3`; the cut lemmas hold for every `n`.

Source: work-sync `theory/T-synchronization-manifold.md` §1.7 and §2.2 (swing network
`Mᵢ θ̈ᵢ = P_{m,i} − Dᵢ θ̇ᵢ − ∑ⱼ Bᵢⱼ sin(θᵢ − θⱼ)` and its energy function); the potential, the
Hessian and cubic forms and the characterization of local asymptotic stability are in
`theorem/Network/Swing/Degenerate.lean`.

Results.
* Static cut identities, every number of machines: `potential_add_groupIndicator` (turning a
  group `X` of machines rigidly by `t` changes the potential by `W (1 − cos t) + K (sin t − t)`,
  `W = ∑ Bᵢⱼ cos(θᵢ − θⱼ)` the total linearization weight and `K` the total flow of the lines
  leaving `X`), `hessForm_groupIndicator` (`A₂` of the turn is `2W`), `ground_groupIndicator`,
  `cubicForm_add_const`, `ground_sub_zero`.
* The four-cycle (superadditivity of `tan`): `tan_add_tan_lt`, `sq_sum_le_mul`
  (Cauchy–Schwarz), `tan_sum_mul_sq_lt` (three angles in `(−π/2, π/2)` summing past `π/2`:
  `tan(∑β)(∑a)² < ∑ a² tan β`), `exists_rep_of_cos_pos`, `quad_tan_ne_zero`,
  `quad_cubic_ne_zero` and `ring_cubic_ne_zero` (a circulation `κ ≠ 0` through four lines whose
  weights have nonnegative pairwise sums has a nonzero cubic term: exactly one weight is
  negative, and with representatives `βᵢ ∈ (−π/2, π/2)` of the three positive lines the cubic
  term is `κ³` times `∑ aᵢ² tan βᵢ − tan(∑βᵢ)(∑aᵢ)² ≠ 0`, `aᵢ = 1/Wᵢ`).
* Four machines in a labelled order `σ`: `hessForm_four`, `cubicForm_four` (the forms as six
  line terms, `weightOf`, `flowOf`), `null_four` (node balances of a null direction).
* The remaining four-machine networks (at least five lines: the diamond and the complete graph)
  are decided in `theorem/Network/Swing/FourDense.lean` (`diamond_cubic_ne_zero` by a branch
  identity, `sorted_cubic_ne_zero` by sorted lifted angles and cycle bounds from
  `tan_sum_mul_sq_lt`). No UNPROVED residual remains for `n = 3`.

Family and connection conclusions.
* The family is `Swing.family`; the public behavioural conclusions are `connection%` statements
  on its generated denotation, with static premises. The cut, form and trigonometric lemmas are
  static or generic implications (foundation); the field-level forms of the statements below are
  private implementation evidence.
* Necessary conditions for local asymptotic stability, every number of machines (the model is
  outside the local asymptotic denotation): `not_localAsymptoticStable_of_cut` (a nonempty proper
  group `X` of machines whose lines to the rest have total weight `W ≤ 0`: a saddle if `W < 0`, a
  fold if `W = 0` and `K ≠ 0`, a non-strict minimum otherwise), its special case
  `not_localAsymptoticStable_of_zero_cut` (every line of the cut has zero weight),
  `not_localAsymptoticStable_of_flat` (a non-constant direction carrying no linearized flow
  `Bᵢⱼ cos(θᵢ − θⱼ)(uᵢ − uⱼ)` on any line), `not_localAsymptoticStable_of_hessForm_neg` (a
  negative Hessian value) and `not_localAsymptoticStable_of_cubicForm_ne_zero` (a nonzero cubic
  term along a null direction of the Hessian form).
* `not_localAsymptoticStable_four` — four machines with two uncoupled pairs (the lines form a
  subgraph of a four-cycle, or of a triangle with a pendant line): every power-balance point with
  a non-Hurwitz reduced Jacobian fails local asymptotic stability.
* `mem_den_locallyAsymptoticallyStable_iff_four` — for four machines with at most four lines
  (two uncoupled pairs, labelled by `σ`), local asymptotic stability holds exactly when the
  profile is a power-balance point with a Hurwitz reduced Jacobian: on this class the local
  asymptotic translation `{powerFlow, jacobianStable}` is exact. In `FourDense.lean`,
  `exact_locallyAsymptoticallyStable_four` states that the local asymptotic translation of
  `family (n := 3)` is exact, and `mem_den_locallyAsymptoticallyStable_iff_four_machines` drops
  the line restriction.
-/

noncomputable section
namespace powerlib.Network.Swing
open Matrix Finset Filter Topology Metric
open powerlib.Dynamics (State)
open scoped Real

variable {n : ℕ}

private theorem mem_den_flow_iff_four {m : Model n} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (reducedField m.params) (equilibrium m.θ) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

private theorem mem_den_of_localAsymptoticStable {p : Params n} {θ : Fin (n + 1) → ℝ}
    (h : LocalAsymptoticStable (reducedField p) (equilibrium θ)) :
    (⟨p, θ⟩ : Model n) ∈ family.den (.flow .locallyAsymptoticallyStable) :=
  mem_den_flow_iff_four.mpr h

/-- A locally asymptotically stable selected point is a strict, isolated minimum of the potential
(`mem_den_locallyAsymptoticallyStable_iff`). -/
private theorem strictMin_of_localAsymptoticStable_four {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hLAS : LocalAsymptoticStable (reducedField p) (equilibrium θ)) :
    ∃ r > 0, ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖ < r →
      potential p θ < potential p (θ + ground v) ∧
        ¬ ∀ k, p.P k = powerInjection p.B (θ + ground v) k := by
  have hmem := mem_den_locallyAsymptoticallyStable_iff (⟨p, θ⟩ : Model n)
  unfold powerlib.TMIO.Statement at hmem
  exact (hmem.mp (mem_den_of_localAsymptoticStable hLAS)).2

/-! ## Cuts -/

/-- Indicator of a group of machines. -/
def groupIndicator (X : Finset (Fin (n + 1))) (k : Fin (n + 1)) : ℝ := if k ∈ X then 1 else 0

/-- A double sum over ordered pairs of machines split by a group `X`. -/
@[powerlib_foundation] theorem sum_sum_cross (X : Finset (Fin (n + 1)))
    (F : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∑ k, ∑ j, ((if k ∈ X ∧ j ∉ X then F k j else 0) + (if k ∉ X ∧ j ∈ X then F j k else 0)) =
      2 * ∑ i ∈ X, ∑ j ∈ Xᶜ, F i j := by
  have hdouble : ∀ g : Fin (n + 1) → Fin (n + 1) → ℝ,
      ∑ k, ∑ j, (if k ∈ X ∧ j ∉ X then g k j else 0) = ∑ i ∈ X, ∑ j ∈ Xᶜ, g i j := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ X)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun k => ¬ k ∈ X) fun k hk => by
      simp only [Finset.mem_filter] at hk; simp [hk.2]]
    rw [add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    ext j; simp [hk]
  have hswap : ∑ k, ∑ j, (if k ∉ X ∧ j ∈ X then F j k else 0) =
      ∑ k, ∑ j, (if k ∈ X ∧ j ∉ X then F k j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    exact if_congr and_comm rfl rfl
  simp only [Finset.sum_add_distrib]
  rw [hswap, hdouble]
  ring

set_option linter.unusedSimpArgs false in
/-- Turning a group `X` of machines rigidly by `t` changes the potential by
`W (1 − cos t) + K (sin t − t)`, with `W` the total linearization weight and `K` the total flow of
the lines leaving `X`. -/
@[powerlib_foundation] theorem potential_add_groupIndicator {p : Params n} {θ : Fin (n + 1) → ℝ}
    (hbal : ∀ k, p.P k = powerInjection p.B θ k) (X : Finset (Fin (n + 1))) (t : ℝ) :
    potential p (θ + t • groupIndicator X) - potential p θ =
      (∑ i ∈ X, ∑ j ∈ Xᶜ, p.B i j * Real.cos (θ i - θ j)) * (1 - Real.cos t) +
      (∑ i ∈ X, ∑ j ∈ Xᶜ, p.B i j * Real.sin (θ i - θ j)) * (Real.sin t - t) := by
  rw [potential_add_sub hbal]
  set F : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    p.B i j * Real.cos (θ i - θ j) * (1 - Real.cos t) +
      p.B i j * Real.sin (θ i - θ j) * (Real.sin t - t) with hF
  have hterm : ∀ k j, p.B k j * edgeIncrement (θ k - θ j)
      ((t • groupIndicator X) k - (t • groupIndicator X) j) =
      (if k ∈ X ∧ j ∉ X then F k j else 0) + (if k ∉ X ∧ j ∈ X then F j k else 0) := by
    intro k j
    simp only [Pi.smul_apply, smul_eq_mul, groupIndicator, hF]
    by_cases hk : k ∈ X <;> by_cases hj : j ∈ X <;> simp only [hk, hj, ↓reduceIte,
      not_true, not_false_eq_true, and_true, and_false, true_and, false_and, mul_one, mul_zero,
      sub_self, add_zero, zero_add]
    · simp [edgeIncrement]
    · simp only [edgeIncrement, Real.cos_add, sub_zero]
      ring
    · simp only [edgeIncrement, Real.cos_add, zero_sub, Real.cos_neg, Real.sin_neg]
      rw [show θ j - θ k = -(θ k - θ j) by ring, Real.sin_neg, Real.cos_neg, p.B_symm j k]
      ring
    · simp [edgeIncrement]
  simp only [hterm]
  rw [sum_sum_cross X F]
  simp only [hF, Finset.sum_add_distrib, Finset.sum_mul]
  ring

/-- The Hessian form of a rigid turn of a group `X` is twice the total linearization weight of
the lines leaving `X`. -/
@[powerlib_foundation] theorem hessForm_groupIndicator (p : Params n) (θ : Fin (n + 1) → ℝ)
    (X : Finset (Fin (n + 1))) :
    hessForm p θ (groupIndicator X) =
      2 * ∑ i ∈ X, ∑ j ∈ Xᶜ, p.B i j * Real.cos (θ i - θ j) := by
  unfold hessForm
  rw [← sum_sum_cross X (fun i j => p.B i j * Real.cos (θ i - θ j))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [groupIndicator]
  by_cases hk : k ∈ X <;> by_cases hj : j ∈ X <;> simp [hk, hj]
  rw [p.B_symm, show θ j - θ k = -(θ k - θ j) by ring, Real.cos_neg]

/-- The grounded relative-angle direction that turns a group `X` rigidly. -/
@[powerlib_foundation] theorem ground_groupIndicator (X : Finset (Fin (n + 1))) :
    ground (fun i : Fin n => groupIndicator X i.succ - groupIndicator X 0) =
      fun k => groupIndicator X k + -groupIndicator X 0 := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [ground]
  · simp only [ground_succ]; ring

/-- Implementation evidence for `not_localAsymptoticStable_of_cut`, at the selected point of the
untranslated field. -/
private theorem reducedSwing_not_localAsymptoticStable_of_cut {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (X : Finset (Fin (n + 1))) (hW : ∑ i ∈ X, ∑ j ∈ Xᶜ, p.B i j * Real.cos (θ i - θ j) ≤ 0)
    {i₀ j₀ : Fin (n + 1)} (hi₀ : i₀ ∈ X) (hj₀ : j₀ ∉ X) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  set K := ∑ i ∈ X, ∑ j ∈ Xᶜ, p.B i j * Real.sin (θ i - θ j) with hKdef
  set v : Fin n → ℝ := fun i => groupIndicator X i.succ - groupIndicator X 0 with hv
  rcases hW.lt_or_eq with hneg | hzero
  · intro hLAS
    refine not_localAsymptoticStable_of_forms ⟨p, θ⟩ hbal v (Or.inl ?_)
      (mem_den_of_localAsymptoticStable hLAS)
    show hessForm p θ (ground v) < 0
    rw [hv, ground_groupIndicator, hessForm_add_const, hessForm_groupIndicator]
    linarith
  have hground : ∀ t : ℝ, θ + ground (t • v) =
      fun k => (θ + t • groupIndicator X) k + -(t * groupIndicator X 0) := by
    intro t
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [ground, groupIndicator]
    · simp only [Pi.add_apply, ground_succ, Pi.smul_apply, smul_eq_mul, hv]
      ring
  have hpot : ∀ t : ℝ, potential p (θ + ground (t • v)) - potential p θ =
      K * (Real.sin t - t) := by
    intro t
    rw [hground t, potential_add_const, sum_P_of_balance hbal, mul_zero, sub_zero,
      potential_add_groupIndicator hbal X t, hzero, zero_mul, zero_add]
  have hv0 : v ≠ 0 := by
    intro h
    have hconst : ∀ k, groupIndicator X k = groupIndicator X 0 := by
      intro k
      refine Fin.cases rfl (fun i => ?_) k
      have := congrFun h i
      simp only [hv, Pi.zero_apply] at this
      linarith
    have h1 := hconst i₀
    have h2 := hconst j₀
    simp only [groupIndicator, hi₀, hj₀, ↓reduceIte] at h1 h2
    linarith
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  by_cases hK : K = 0
  · intro hLAS
    obtain ⟨r, hr, hmin⟩ := strictMin_of_localAsymptoticStable_four hLAS
    set t := r / (2 * ‖v‖) with ht
    have htpos : 0 < t := by positivity
    have htv : t • v ≠ 0 := smul_ne_zero htpos.ne' hv0
    have hnorm : ‖t • v‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg htpos.le, ht]
      field_simp
      linarith
    have := (hmin (t • v) htv hnorm).1
    have h0 := hpot t
    rw [hK, zero_mul] at h0
    linarith
  · have hseed : ∀ ε > 0, ∃ w : Fin n → ℝ, ‖angleState w‖ < ε ∧
        potential p (θ + ground w) < potential p θ := by
      intro ε hε
      have hA : 0 < ‖angleState v‖ := norm_pos_iff.mpr ((angleState_eq_zero_iff v).not.mpr hv0)
      set τ := ε / (2 * ‖angleState v‖) with hτ
      have hτpos : 0 < τ := by positivity
      have hτε : τ * ‖angleState v‖ < ε := by
        rw [hτ]; field_simp; linarith
      rcases lt_or_gt_of_ne hK with hneg | hpos
      · refine ⟨(-τ) • v, ?_, ?_⟩
        · rw [angleState_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hτpos]
          exact hτε
        · have h0 := hpot (-τ)
          have hs : -τ < Real.sin (-τ) := by
            rw [Real.sin_neg]; linarith [Real.sin_lt hτpos]
          nlinarith
      · refine ⟨τ • v, ?_, ?_⟩
        · rw [angleState_smul, norm_smul, Real.norm_of_nonneg hτpos.le]
          exact hτε
        · have h0 := hpot τ
          have hs := Real.sin_lt hτpos
          nlinarith
    intro hLAS
    obtain ⟨r, hr, hmin⟩ := strictMin_of_localAsymptoticStable_four hLAS
    obtain ⟨w, hw, hlt⟩ := hseed r hr
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp [ground_zero_vec] at hlt
    have hwr : ‖w‖ < r := lt_of_le_of_lt (by simpa using norm_le_of_dIdx (angleState w)) hw
    exact absurd (hmin w hw0 hwr).1 (not_lt.mpr hlt.le)

/-- **A cut of nonpositive total weight rules out local asymptotic stability** (any number of
machines). If the lines between a nonempty proper group `X` of machines and the rest have total
linearization weight `W = ∑ Bᵢⱼ cos(θᵢ − θⱼ) ≤ 0`, turning `X` rigidly changes the potential by
`W (1 − cos t) + K (sin t − t)`: a saddle if `W < 0`; if `W = 0` a fold when the flow `K` out of
`X` is nonzero and a non-strict minimum when it vanishes. -/
@[powerlib_domain] theorem not_localAsymptoticStable_of_cut (m : Model n)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) (X : Finset (Fin (n + 1)))
    (hW : ∑ i ∈ X, ∑ j ∈ Xᶜ, m.params.B i j * Real.cos (m.θ i - m.θ j) ≤ 0)
    {i₀ j₀ : Fin (n + 1)} (hi₀ : i₀ ∈ X) (hj₀ : j₀ ∉ X) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_four]
  exact reducedSwing_not_localAsymptoticStable_of_cut hbal X hW hi₀ hj₀

/-- Implementation evidence for `not_localAsymptoticStable_of_zero_cut`. -/
private theorem reducedSwing_not_localAsymptoticStable_of_zero_cut {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (X : Finset (Fin (n + 1))) (hX : ∀ i ∈ X, ∀ j ∉ X, p.B i j * Real.cos (θ i - θ j) = 0)
    {i₀ j₀ : Fin (n + 1)} (hi₀ : i₀ ∈ X) (hj₀ : j₀ ∉ X) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) :=
  reducedSwing_not_localAsymptoticStable_of_cut hbal X (le_of_eq (Finset.sum_eq_zero fun i hi =>
    Finset.sum_eq_zero fun j hj => hX i hi j (Finset.mem_compl.mp hj))) hi₀ hj₀

/-- **A cut of zero-weight lines** (each line between `X` and the rest open or at `±π/2`) rules
out local asymptotic stability. -/
@[powerlib_domain] theorem not_localAsymptoticStable_of_zero_cut (m : Model n)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) (X : Finset (Fin (n + 1)))
    (hX : ∀ i ∈ X, ∀ j ∉ X, m.params.B i j * Real.cos (m.θ i - m.θ j) = 0)
    {i₀ j₀ : Fin (n + 1)} (hi₀ : i₀ ∈ X) (hj₀ : j₀ ∉ X) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_four]
  exact reducedSwing_not_localAsymptoticStable_of_zero_cut hbal X hX hi₀ hj₀

/-- Implementation evidence for `not_localAsymptoticStable_of_flat`. -/
private theorem reducedSwing_not_localAsymptoticStable_of_flat {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k) (u : Fin (n + 1) → ℝ)
    {k₁ k₂ : Fin (n + 1)} (hne : u k₁ ≠ u k₂)
    (h : ∀ k j, p.B k j * Real.cos (θ k - θ j) * (u k - u j) = 0) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  obtain ⟨i₀, -, -⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  obtain ⟨j₀, hj₀⟩ : ∃ j, u j ≠ u i₀ := by
    by_cases h1 : u k₁ = u i₀
    · exact ⟨k₂, fun h2 => hne (h1.trans h2.symm)⟩
    · exact ⟨k₁, h1⟩
  refine reducedSwing_not_localAsymptoticStable_of_zero_cut hbal
    (Finset.univ.filter fun k => u k = u i₀)
    ?_ (i₀ := i₀) (j₀ := j₀) (by simp) (by simp [hj₀])
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rcases mul_eq_zero.mp (h i j) with h' | h'
  · exact h'
  · exact absurd (by linarith : u j = u i₀) hj

/-- A null direction without circulation: if every line carries no linearized flow
`Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)` along a non-constant `u`, the machines at the top value of `u` are cut
off by zero-weight lines, so the model is not locally asymptotically stable. -/
@[powerlib_domain] theorem not_localAsymptoticStable_of_flat (m : Model n)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) (u : Fin (n + 1) → ℝ)
    {k₁ k₂ : Fin (n + 1)} (hne : u k₁ ≠ u k₂)
    (h : ∀ k j, m.params.B k j * Real.cos (m.θ k - m.θ j) * (u k - u j) = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_four]
  exact reducedSwing_not_localAsymptoticStable_of_flat hbal u hne h

@[powerlib_foundation] theorem cubicForm_add_const (p : Params n) (θ u : Fin (n + 1) → ℝ)
    (c : ℝ) : cubicForm p θ (fun k => u k + c) = cubicForm p θ u := by
  simp [cubicForm]

@[powerlib_foundation] theorem ground_sub_zero (u : Fin (n + 1) → ℝ) :
    ground (fun i => u i.succ - u 0) = fun k => u k + -u 0 := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [ground]
  · simp only [ground_succ]; ring

/-- Implementation evidence: at a locally asymptotically stable power-balance point the Hessian
form is positive semidefinite. -/
private theorem reducedSwing_hessForm_nonneg_of_localAsymptoticStable {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hLAS : LocalAsymptoticStable (reducedField p) (equilibrium θ)) (u : Fin (n + 1) → ℝ) :
    0 ≤ hessForm p θ u := by
  by_contra h
  push Not at h
  refine not_localAsymptoticStable_of_forms ⟨p, θ⟩ hbal (fun i => u i.succ - u 0) (Or.inl ?_)
    (mem_den_of_localAsymptoticStable hLAS)
  show hessForm p θ (ground fun i => u i.succ - u 0) < 0
  rw [ground_sub_zero, hessForm_add_const]
  exact h

/-- Implementation evidence: at a locally asymptotically stable power-balance point the cubic
form vanishes on every null direction of the Hessian form. -/
private theorem reducedSwing_cubicForm_eq_zero_of_localAsymptoticStable {p : Params n}
    {θ : Fin (n + 1) → ℝ} (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hLAS : LocalAsymptoticStable (reducedField p) (equilibrium θ)) (u : Fin (n + 1) → ℝ)
    (h0 : hessForm p θ u = 0) : cubicForm p θ u = 0 := by
  by_contra h
  refine not_localAsymptoticStable_of_forms ⟨p, θ⟩ hbal (fun i => u i.succ - u 0)
    (Or.inr ⟨?_, ?_⟩) (mem_den_of_localAsymptoticStable hLAS)
  · show hessForm p θ (ground fun i => u i.succ - u 0) = 0
    rw [ground_sub_zero, hessForm_add_const]; exact h0
  · show cubicForm p θ (ground fun i => u i.succ - u 0) ≠ 0
    rw [ground_sub_zero, cubicForm_add_const]; exact h

/-- **A negative value of the Hessian form rules out local asymptotic stability**: at a
power-balance point a locally asymptotically stable model has a positive semidefinite Hessian
form. -/
@[powerlib_domain] theorem not_localAsymptoticStable_of_hessForm_neg (m : Model n)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) (u : Fin (n + 1) → ℝ)
    (h : hessForm m.params m.θ u < 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_four]
  exact fun hLAS => absurd
    (reducedSwing_hessForm_nonneg_of_localAsymptoticStable hbal hLAS u) (not_le.mpr h)

/-- **A nonzero cubic form along a null direction of the Hessian form rules out local asymptotic
stability**: at a power-balance point a locally asymptotically stable model has a cubic form
vanishing on every null direction of its Hessian form. -/
@[powerlib_domain] theorem not_localAsymptoticStable_of_cubicForm_ne_zero (m : Model n)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k) (u : Fin (n + 1) → ℝ)
    (h0 : hessForm m.params m.θ u = 0) (h : cubicForm m.params m.θ u ≠ 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_four]
  exact fun hLAS => h (reducedSwing_cubicForm_eq_zero_of_localAsymptoticStable hbal hLAS u h0)

/-! ## The four-cycle: superadditivity of `tan` -/

/-- Superadditivity of `tan` on `(0, π/2)`. -/
@[powerlib_foundation] theorem tan_add_tan_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y < π / 2) :
    Real.tan x + Real.tan y < Real.tan (x + y) := by
  have cx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have cy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have cxy : 0 < Real.cos (x + y) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxy⟩
  have sx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have sy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy (by linarith [Real.pi_pos])
  have sxy : 0 < Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
    rw [← Real.sin_add]; exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
    div_add_div _ _ cx.ne' cy.ne', div_lt_div_iff₀ (mul_pos cx cy) cxy, Real.sin_add,
    Real.cos_add]
  rw [Real.cos_add] at cxy
  nlinarith [mul_pos sxy (mul_pos sx sy)]

/-- Cauchy–Schwarz with three positive weights. -/
@[powerlib_foundation] theorem sq_sum_le_mul {a₂ a₃ a₄ r₂ r₃ r₄ : ℝ} (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hr₄ : 0 < r₄) :
    (a₂ + a₃ + a₄) ^ 2 ≤ (a₂ ^ 2 / r₂ + a₃ ^ 2 / r₃ + a₄ ^ 2 / r₄) * (r₂ + r₃ + r₄) := by
  obtain ⟨b₂, rfl⟩ : ∃ b, a₂ = b * r₂ := ⟨a₂ / r₂, by field_simp⟩
  obtain ⟨b₃, rfl⟩ : ∃ b, a₃ = b * r₃ := ⟨a₃ / r₃, by field_simp⟩
  obtain ⟨b₄, rfl⟩ : ∃ b, a₄ = b * r₄ := ⟨a₄ / r₄, by field_simp⟩
  have e₂ : (b₂ * r₂) ^ 2 / r₂ = b₂ ^ 2 * r₂ := by field_simp
  have e₃ : (b₃ * r₃) ^ 2 / r₃ = b₃ ^ 2 * r₃ := by field_simp
  have e₄ : (b₄ * r₄) ^ 2 / r₄ = b₄ ^ 2 * r₄ := by field_simp
  rw [e₂, e₃, e₄]
  nlinarith [mul_nonneg (mul_pos hr₂ hr₃).le (sq_nonneg (b₂ - b₃)),
    mul_nonneg (mul_pos hr₂ hr₄).le (sq_nonneg (b₂ - b₄)),
    mul_nonneg (mul_pos hr₃ hr₄).le (sq_nonneg (b₃ - b₄))]

/-- **Three angles in `(−π/2, π/2)` summing past `π/2`.** For positive `a`,
`tan(β₂ + β₃ + β₄) (a₂ + a₃ + a₄)² < ∑ aᵢ² tan βᵢ`. -/
@[powerlib_foundation] theorem tan_sum_mul_sq_lt {β₂ β₃ β₄ a₂ a₃ a₄ : ℝ}
    (h₂ : -(π / 2) < β₂ ∧ β₂ < π / 2) (h₃ : -(π / 2) < β₃ ∧ β₃ < π / 2)
    (h₄ : -(π / 2) < β₄ ∧ β₄ < π / 2) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄)
    (hσ : π / 2 < β₂ + β₃ + β₄) :
    Real.tan (β₂ + β₃ + β₄) * (a₂ + a₃ + a₄) ^ 2 <
      a₂ ^ 2 * Real.tan β₂ + a₃ ^ 2 * Real.tan β₃ + a₄ ^ 2 * Real.tan β₄ := by
  set σ := β₂ + β₃ + β₄ with hσdef
  have htanσ : Real.tan σ = Real.tan (σ - π) := (Real.tan_periodic.sub_eq σ).symm
  rcases le_or_gt σ π with hle | hlt
  · have hlow : -(π / 2) < σ - π := by linarith
    have hup : σ - π < π / 2 := by linarith [Real.pi_pos]
    have key : ∀ β, -(π / 2) < β → β < π / 2 → σ - π < β → Real.tan σ < Real.tan β := by
      intro β h1 h2 h3
      rw [htanσ]
      exact Real.strictMonoOn_tan ⟨hlow, hup⟩ ⟨h1, h2⟩ h3
    have t₂ := key β₂ h₂.1 h₂.2 (by linarith [h₃.2, h₄.2])
    have t₃ := key β₃ h₃.1 h₃.2 (by linarith [h₂.2, h₄.2])
    have t₄ := key β₄ h₄.1 h₄.2 (by linarith [h₂.2, h₃.2])
    have hnp : Real.tan σ ≤ 0 := by
      rw [htanσ]
      have := Real.strictMonoOn_tan.monotoneOn ⟨hlow, hup⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (show σ - π ≤ 0 by linarith)
      simpa using this
    have e : a₂ ^ 2 * Real.tan β₂ + a₃ ^ 2 * Real.tan β₃ + a₄ ^ 2 * Real.tan β₄ -
        Real.tan σ * (a₂ + a₃ + a₄) ^ 2 =
        a₂ ^ 2 * (Real.tan β₂ - Real.tan σ) + a₃ ^ 2 * (Real.tan β₃ - Real.tan σ) +
          a₄ ^ 2 * (Real.tan β₄ - Real.tan σ) +
          (-Real.tan σ) * (2 * (a₂ * a₃ + a₂ * a₄ + a₃ * a₄)) := by ring
    have p₂ := mul_pos (pow_pos ha₂ 2) (sub_pos.mpr t₂)
    have p₃ := mul_pos (pow_pos ha₃ 2) (sub_pos.mpr t₃)
    have p₄ := mul_pos (pow_pos ha₄ 2) (sub_pos.mpr t₄)
    have p₅ : 0 ≤ (-Real.tan σ) * (2 * (a₂ * a₃ + a₂ * a₄ + a₃ * a₄)) :=
      mul_nonneg (by linarith) (by positivity)
    linarith
  · -- complementary angles `γᵢ = π/2 − βᵢ` in `(0, π/2)` with sum `3π/2 − σ < π/2`
    have b₂ : 0 < β₂ := by linarith [h₃.2, h₄.2]
    have b₃ : 0 < β₃ := by linarith [h₂.2, h₄.2]
    have b₄ : 0 < β₄ := by linarith [h₂.2, h₃.2]
    have hΓ : 0 < (π / 2 - β₂) + (π / 2 - β₃) + (π / 2 - β₄) := by linarith [h₂.2, h₃.2, h₄.2]
    have hΓ' : (π / 2 - β₂) + (π / 2 - β₃) + (π / 2 - β₄) < π / 2 := by linarith
    have r₂ := Real.tan_pos_of_pos_of_lt_pi_div_two (x := π / 2 - β₂) (by linarith [h₂.2])
      (by linarith)
    have r₃ := Real.tan_pos_of_pos_of_lt_pi_div_two (x := π / 2 - β₃) (by linarith [h₃.2])
      (by linarith)
    have r₄ := Real.tan_pos_of_pos_of_lt_pi_div_two (x := π / 2 - β₄) (by linarith [h₄.2])
      (by linarith)
    have hR := Real.tan_pos_of_pos_of_lt_pi_div_two hΓ hΓ'
    have hsup : Real.tan (π / 2 - β₂) + Real.tan (π / 2 - β₃) + Real.tan (π / 2 - β₄) <
        Real.tan ((π / 2 - β₂) + (π / 2 - β₃) + (π / 2 - β₄)) := by
      have s1 := tan_add_tan_lt (x := π / 2 - β₂) (y := π / 2 - β₃) (by linarith [h₂.2])
        (by linarith [h₃.2]) (by linarith [h₄.2])
      have s2 := tan_add_tan_lt (x := (π / 2 - β₂) + (π / 2 - β₃)) (y := π / 2 - β₄)
        (by linarith [h₂.2, h₃.2]) (by linarith [h₄.2]) hΓ'
      linarith
    have tβ : ∀ β, Real.tan β = (Real.tan (π / 2 - β))⁻¹ := by
      intro β
      rw [Real.tan_pi_div_two_sub, inv_inv]
    have tσ : Real.tan σ = (Real.tan ((π / 2 - β₂) + (π / 2 - β₃) + (π / 2 - β₄)))⁻¹ := by
      rw [← Real.tan_pi_div_two_sub, ← Real.tan_periodic (π / 2 - _)]
      congr 1
      rw [hσdef]; ring
    rw [tσ, tβ β₂, tβ β₃, tβ β₄]
    set R := Real.tan ((π / 2 - β₂) + (π / 2 - β₃) + (π / 2 - β₄))
    set q₂ := Real.tan (π / 2 - β₂)
    set q₃ := Real.tan (π / 2 - β₃)
    set q₄ := Real.tan (π / 2 - β₄)
    have hcs := sq_sum_le_mul (a₂ := a₂) (a₃ := a₃) (a₄ := a₄) r₂ r₃ r₄
    have hS : 0 < a₂ ^ 2 / q₂ + a₃ ^ 2 / q₃ + a₄ ^ 2 / q₄ := by positivity
    have e : a₂ ^ 2 * q₂⁻¹ + a₃ ^ 2 * q₃⁻¹ + a₄ ^ 2 * q₄⁻¹ =
        a₂ ^ 2 / q₂ + a₃ ^ 2 / q₃ + a₄ ^ 2 / q₄ := by simp [div_eq_mul_inv]
    rw [e, inv_mul_lt_iff₀ hR]
    calc (a₂ + a₃ + a₄) ^ 2 ≤ (a₂ ^ 2 / q₂ + a₃ ^ 2 / q₃ + a₄ ^ 2 / q₄) * (q₂ + q₃ + q₄) := hcs
      _ < (a₂ ^ 2 / q₂ + a₃ ^ 2 / q₃ + a₄ ^ 2 / q₄) * R := mul_lt_mul_of_pos_left hsup hS
      _ = R * (a₂ ^ 2 / q₂ + a₃ ^ 2 / q₃ + a₄ ^ 2 / q₄) := mul_comm _ _

/-- An angle with positive cosine has a representative in `(−π/2, π/2)` with the same sine and
cosine. -/
@[powerlib_foundation] theorem exists_rep_of_cos_pos {φ : ℝ} (hc : 0 < Real.cos φ) :
    ∃ β, (-(π / 2) < β ∧ β < π / 2) ∧ Real.sin β = Real.sin φ ∧ Real.cos β = Real.cos φ := by
  refine ⟨Real.arcsin (Real.sin φ), ?_, Real.sin_arcsin (Real.neg_one_le_sin φ)
    (Real.sin_le_one φ), ?_⟩
  swap
  · rw [Real.cos_arcsin]
    have : 1 - Real.sin φ ^ 2 = Real.cos φ ^ 2 := by rw [← Real.sin_sq_add_cos_sq φ]; ring
    rw [this, Real.sqrt_sq hc.le]
  have hcb : Real.cos (Real.arcsin (Real.sin φ)) = Real.cos φ := by
    rw [Real.cos_arcsin]
    have : 1 - Real.sin φ ^ 2 = Real.cos φ ^ 2 := by rw [← Real.sin_sq_add_cos_sq φ]; ring
    rw [this, Real.sqrt_sq hc.le]
  refine ⟨lt_of_le_of_ne (Real.neg_pi_div_two_le_arcsin _) fun h => ?_,
    lt_of_le_of_ne (Real.arcsin_le_pi_div_two _) fun h => ?_⟩
  · rw [← h, Real.cos_neg, Real.cos_pi_div_two] at hcb; linarith
  · rw [h, Real.cos_pi_div_two] at hcb; linarith

/-- **The cubic term on a four-cycle with one negative line (tangent form).** Four angles summing
to zero, the first with negative cosine and the others with positive cosine, and positive `a`:
`tan φ₁ (a₂ + a₃ + a₄)² + ∑ aᵢ² tan φᵢ ≠ 0` (superadditivity of `tan` and Cauchy–Schwarz). -/
@[powerlib_foundation] theorem quad_tan_ne_zero {φ₁ φ₂ φ₃ φ₄ a₂ a₃ a₄ : ℝ}
    (hsum : φ₁ + φ₂ + φ₃ + φ₄ = 0)
    (hc₁ : Real.cos φ₁ < 0) (hc₂ : 0 < Real.cos φ₂) (hc₃ : 0 < Real.cos φ₃)
    (hc₄ : 0 < Real.cos φ₄) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    Real.tan φ₁ * (a₂ + a₃ + a₄) ^ 2 + a₂ ^ 2 * Real.tan φ₂ + a₃ ^ 2 * Real.tan φ₃ +
      a₄ ^ 2 * Real.tan φ₄ ≠ 0 := by
  obtain ⟨β₂, hb₂, hs₂, hk₂⟩ := exists_rep_of_cos_pos hc₂
  obtain ⟨β₃, hb₃, hs₃, hk₃⟩ := exists_rep_of_cos_pos hc₃
  obtain ⟨β₄, hb₄, hs₄, hk₄⟩ := exists_rep_of_cos_pos hc₄
  have ht : ∀ {β φ : ℝ}, Real.sin β = Real.sin φ → Real.cos β = Real.cos φ →
      Real.tan φ = Real.tan β := by
    intro β φ hs hk
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, hs, hk]
  have hφ₁ : φ₁ = -(φ₂ + φ₃ + φ₄) := by linarith
  have hsσ : Real.sin (β₂ + β₃ + β₄) = -Real.sin φ₁ := by
    rw [hφ₁, Real.sin_neg, neg_neg, Real.sin_add, Real.sin_add, Real.cos_add, Real.sin_add,
      Real.sin_add, Real.cos_add, hs₂, hs₃, hs₄, hk₂, hk₃, hk₄]
  have hkσ : Real.cos (β₂ + β₃ + β₄) = Real.cos φ₁ := by
    rw [hφ₁, Real.cos_neg, Real.cos_add, Real.cos_add, Real.sin_add, Real.cos_add,
      Real.cos_add, Real.sin_add, hs₂, hs₃, hs₄, hk₂, hk₃, hk₄]
  have ht₁ : Real.tan φ₁ = -Real.tan (β₂ + β₃ + β₄) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, hsσ, hkσ, neg_div, neg_neg]
  rw [ht₁, ht hs₂ hk₂, ht hs₃ hk₃, ht hs₄ hk₄]
  have hσ : π / 2 < β₂ + β₃ + β₄ ∨ β₂ + β₃ + β₄ < -(π / 2) := by
    by_contra h
    push Not at h
    have := Real.cos_nonneg_of_mem_Icc ⟨h.2, h.1⟩
    linarith
  rcases hσ with hσ | hσ
  · have := tan_sum_mul_sq_lt hb₂ hb₃ hb₄ ha₂ ha₃ ha₄ hσ
    linarith
  · have := tan_sum_mul_sq_lt (β₂ := -β₂) (β₃ := -β₃) (β₄ := -β₄)
      ⟨by linarith [hb₂.2], by linarith [hb₂.1]⟩ ⟨by linarith [hb₃.2], by linarith [hb₃.1]⟩
      ⟨by linarith [hb₄.2], by linarith [hb₄.1]⟩ ha₂ ha₃ ha₄ (by linarith)
    rw [show -β₂ + -β₃ + -β₄ = -(β₂ + β₃ + β₄) by ring, Real.tan_neg, Real.tan_neg,
      Real.tan_neg, Real.tan_neg] at this
    linarith

/-- **Cubic term on a four-cycle.** A circulation `κ ≠ 0` through four lines with weights
`Bᵢ cos φᵢ` (`B > 0`, angles summing to zero, increments summing to zero), the first weight
negative and the other three positive, has a nonzero cubic term:
`∑ Bᵢ sin φᵢ xᵢ³ ≠ 0` for `Bᵢ cos φᵢ xᵢ = κ`. -/
@[powerlib_foundation] theorem quad_cubic_ne_zero {B₁ B₂ B₃ B₄ φ₁ φ₂ φ₃ φ₄ x₁ x₂ x₃ x₄ κ : ℝ}
    (hB₂ : 0 < B₂) (hB₃ : 0 < B₃) (hB₄ : 0 < B₄)
    (hsum : φ₁ + φ₂ + φ₃ + φ₄ = 0) (hx : x₁ + x₂ + x₃ + x₄ = 0)
    (h₁ : B₁ * Real.cos φ₁ * x₁ = κ) (h₂ : B₂ * Real.cos φ₂ * x₂ = κ)
    (h₃ : B₃ * Real.cos φ₃ * x₃ = κ) (h₄ : B₄ * Real.cos φ₄ * x₄ = κ) (hκ : κ ≠ 0)
    (hc₁ : Real.cos φ₁ < 0) (hc₂ : 0 < Real.cos φ₂) (hc₃ : 0 < Real.cos φ₃)
    (hc₄ : 0 < Real.cos φ₄) :
    B₁ * Real.sin φ₁ * x₁ ^ 3 + B₂ * Real.sin φ₂ * x₂ ^ 3 + B₃ * Real.sin φ₃ * x₃ ^ 3 +
      B₄ * Real.sin φ₄ * x₄ ^ 3 ≠ 0 := by
  have term : ∀ {B φ x : ℝ}, Real.cos φ ≠ 0 → B * Real.cos φ * x = κ →
      B * Real.sin φ * x ^ 3 = κ * Real.tan φ * x ^ 2 := by
    intro B φ x hc hx
    rw [← hx, Real.tan_eq_sin_div_cos]
    field_simp
  have pos : ∀ {B φ x : ℝ}, 0 < B → 0 < Real.cos φ → B * Real.cos φ * x = κ → 0 < x / κ := by
    intro B φ x hB hc hx
    have hx0 : x ≠ 0 := fun h => hκ (by rw [← hx, h, mul_zero])
    have e : x / κ * (B * Real.cos φ) = 1 := by rw [← hx]; field_simp
    have hw : 0 < B * Real.cos φ := mul_pos hB hc
    by_contra hle
    push Not at hle
    nlinarith
  have ha₂ := pos hB₂ hc₂ h₂
  have ha₃ := pos hB₃ hc₃ h₃
  have ha₄ := pos hB₄ hc₄ h₄
  have hne := quad_tan_ne_zero hsum hc₁ hc₂ hc₃ hc₄ ha₂ ha₃ ha₄
  rw [term hc₁.ne h₁, term hc₂.ne' h₂, term hc₃.ne' h₃, term hc₄.ne' h₄]
  have hx₁ : x₁ = -(x₂ + x₃ + x₄) := by linarith
  have e : κ * Real.tan φ₁ * x₁ ^ 2 + κ * Real.tan φ₂ * x₂ ^ 2 + κ * Real.tan φ₃ * x₃ ^ 2 +
      κ * Real.tan φ₄ * x₄ ^ 2 = κ ^ 3 * (Real.tan φ₁ * (x₂ / κ + x₃ / κ + x₄ / κ) ^ 2 +
        (x₂ / κ) ^ 2 * Real.tan φ₂ + (x₃ / κ) ^ 2 * Real.tan φ₃ +
        (x₄ / κ) ^ 2 * Real.tan φ₄) := by
    rw [hx₁]; field_simp
  rw [e]
  exact mul_ne_zero (pow_ne_zero 3 hκ) hne

/-- **The cubic term on a four-cycle with one negative line**, in any position: a circulation
`κ ≠ 0` through four lines (`B > 0`, angles and increments summing to zero) whose weights
`Bᵢ cos φᵢ` have nonnegative pairwise sums has a nonzero cubic term. -/
@[powerlib_foundation] theorem ring_cubic_ne_zero {B₁ B₂ B₃ B₄ φ₁ φ₂ φ₃ φ₄ x₁ x₂ x₃ x₄ κ : ℝ}
    (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB₃ : 0 < B₃) (hB₄ : 0 < B₄)
    (hsum : φ₁ + φ₂ + φ₃ + φ₄ = 0) (hx : x₁ + x₂ + x₃ + x₄ = 0)
    (h₁ : B₁ * Real.cos φ₁ * x₁ = κ) (h₂ : B₂ * Real.cos φ₂ * x₂ = κ)
    (h₃ : B₃ * Real.cos φ₃ * x₃ = κ) (h₄ : B₄ * Real.cos φ₄ * x₄ = κ) (hκ : κ ≠ 0)
    (p₁₂ : 0 ≤ B₁ * Real.cos φ₁ + B₂ * Real.cos φ₂) (p₁₃ : 0 ≤ B₁ * Real.cos φ₁ + B₃ * Real.cos φ₃)
    (p₁₄ : 0 ≤ B₁ * Real.cos φ₁ + B₄ * Real.cos φ₄) (p₂₃ : 0 ≤ B₂ * Real.cos φ₂ + B₃ * Real.cos φ₃)
    (p₂₄ : 0 ≤ B₂ * Real.cos φ₂ + B₄ * Real.cos φ₄)
    (p₃₄ : 0 ≤ B₃ * Real.cos φ₃ + B₄ * Real.cos φ₄) :
    B₁ * Real.sin φ₁ * x₁ ^ 3 + B₂ * Real.sin φ₂ * x₂ ^ 3 + B₃ * Real.sin φ₃ * x₃ ^ 3 +
      B₄ * Real.sin φ₄ * x₄ ^ 3 ≠ 0 := by
  have nz : ∀ {B φ x : ℝ}, B * Real.cos φ * x = κ → Real.cos φ ≠ 0 := fun hx hc =>
    hκ (by rw [← hx, hc, mul_zero, zero_mul])
  have hc₁ := nz h₁
  have hc₂ := nz h₂
  have hc₃ := nz h₃
  have hc₄ := nz h₄
  -- the sign of a weight is the sign of its cosine
  have neg : ∀ {B φ : ℝ}, 0 < B → Real.cos φ < 0 → B * Real.cos φ < 0 := fun hB hc =>
    mul_neg_of_pos_of_neg hB hc
  have pos : ∀ {B φ : ℝ}, 0 < B → 0 < Real.cos φ → 0 < B * Real.cos φ := fun hB hc =>
    mul_pos hB hc
  have other : ∀ {B φ C ψ : ℝ}, 0 < B → 0 < C → Real.cos φ < 0 → Real.cos ψ ≠ 0 →
      0 ≤ B * Real.cos φ + C * Real.cos ψ → 0 < Real.cos ψ := by
    intro B φ C ψ hB hC hφ hψ hp
    rcases lt_or_gt_of_ne hψ with h | h
    · have := neg hB hφ; have := neg hC h; linarith
    · exact h
  rcases lt_or_gt_of_ne hc₁ with n₁ | q₁
  · exact quad_cubic_ne_zero hB₂ hB₃ hB₄ hsum hx h₁ h₂ h₃ h₄ hκ n₁
      (other hB₁ hB₂ n₁ hc₂ p₁₂) (other hB₁ hB₃ n₁ hc₃ p₁₃) (other hB₁ hB₄ n₁ hc₄ p₁₄)
  rcases lt_or_gt_of_ne hc₂ with n₂ | q₂
  · have := quad_cubic_ne_zero hB₃ hB₄ hB₁ (φ₁ := φ₂) (φ₂ := φ₃) (φ₃ := φ₄) (φ₄ := φ₁)
      (x₁ := x₂) (x₂ := x₃) (x₃ := x₄) (x₄ := x₁) (by linarith) (by linarith) h₂ h₃ h₄ h₁ hκ n₂
      (other hB₂ hB₃ n₂ hc₃ p₂₃) (other hB₂ hB₄ n₂ hc₄ p₂₄) q₁
    intro h; apply this; linarith
  rcases lt_or_gt_of_ne hc₃ with n₃ | q₃
  · have := quad_cubic_ne_zero hB₄ hB₁ hB₂ (φ₁ := φ₃) (φ₂ := φ₄) (φ₃ := φ₁) (φ₄ := φ₂)
      (x₁ := x₃) (x₂ := x₄) (x₃ := x₁) (x₄ := x₂) (by linarith) (by linarith) h₃ h₄ h₁ h₂ hκ n₃
      (other hB₃ hB₄ n₃ hc₄ p₃₄) q₁ q₂
    intro h; apply this; linarith
  rcases lt_or_gt_of_ne hc₄ with n₄ | q₄
  · have := quad_cubic_ne_zero hB₁ hB₂ hB₃ (φ₁ := φ₄) (φ₂ := φ₁) (φ₃ := φ₂) (φ₄ := φ₃)
      (x₁ := x₄) (x₂ := x₁) (x₃ := x₂) (x₄ := x₃) (by linarith) (by linarith) h₄ h₁ h₂ h₃ hκ n₄
      q₁ q₂ q₃
    intro h; apply this; linarith
  -- all weights positive: the increments share the sign of `κ`, against `∑ xᵢ = 0`
  exfalso
  have w₁ := pos hB₁ q₁
  have w₂ := pos hB₂ q₂
  have w₃ := pos hB₃ q₃
  have w₄ := pos hB₄ q₄
  rcases lt_or_gt_of_ne hκ with hk | hk
  · have : x₁ < 0 := by by_contra hc; push Not at hc; nlinarith
    have : x₂ < 0 := by by_contra hc; push Not at hc; nlinarith
    have : x₃ < 0 := by by_contra hc; push Not at hc; nlinarith
    have : x₄ < 0 := by by_contra hc; push Not at hc; nlinarith
    linarith
  · have : 0 < x₁ := by by_contra hc; push Not at hc; nlinarith
    have : 0 < x₂ := by by_contra hc; push Not at hc; nlinarith
    have : 0 < x₃ := by by_contra hc; push Not at hc; nlinarith
    have : 0 < x₄ := by by_contra hc; push Not at hc; nlinarith
    linarith

/-! ## Four machines in a labelled order -/

/-- A symmetric double sum over four indices with zero diagonal. -/
@[powerlib_foundation] theorem sum_four_pairs (F : Fin 4 → Fin 4 → ℝ)
    (hs : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 * (F 0 1 + F 0 2 + F 0 3 + F 1 2 + F 1 3 + F 2 3) := by
  simp only [Fin.sum_univ_four, hd]
  rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]
  ring

/-- Linearization weight of the line between the machines labelled `i` and `j`. -/
def weightOf (p : Params 3) (θ : Fin (3 + 1) → ℝ) (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) : ℝ :=
  p.B (σ i) (σ j) * Real.cos (θ (σ i) - θ (σ j))

/-- Flow on the line between the machines labelled `i` and `j`. -/
def flowOf (p : Params 3) (θ : Fin (3 + 1) → ℝ) (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) : ℝ :=
  p.B (σ i) (σ j) * Real.sin (θ (σ i) - θ (σ j))

@[powerlib_foundation] theorem hessForm_four (p : Params 3) (θ u : Fin (3 + 1) → ℝ)
    (σ : Equiv.Perm (Fin 4)) :
    hessForm p θ u = 2 * (weightOf p θ σ 0 1 * (u (σ 0) - u (σ 1)) ^ 2 +
      weightOf p θ σ 0 2 * (u (σ 0) - u (σ 2)) ^ 2 + weightOf p θ σ 0 3 * (u (σ 0) - u (σ 3)) ^ 2 +
      weightOf p θ σ 1 2 * (u (σ 1) - u (σ 2)) ^ 2 + weightOf p θ σ 1 3 * (u (σ 1) - u (σ 3)) ^ 2 +
      weightOf p θ σ 2 3 * (u (σ 2) - u (σ 3)) ^ 2) := by
  unfold hessForm
  rw [← Equiv.sum_comp σ]
  simp_rw [← Equiv.sum_comp σ (fun j => p.B _ j * _ * _)]
  refine (sum_four_pairs (fun i j => p.B (σ i) (σ j) * Real.cos (θ (σ i) - θ (σ j)) *
    (u (σ i) - u (σ j)) ^ 2) (fun i j => ?_) (fun i => by simp)).trans (by simp [weightOf])
  rw [p.B_symm, show θ (σ j) - θ (σ i) = -(θ (σ i) - θ (σ j)) by ring, Real.cos_neg]
  ring

@[powerlib_foundation] theorem cubicForm_four (p : Params 3) (θ u : Fin (3 + 1) → ℝ)
    (σ : Equiv.Perm (Fin 4)) :
    cubicForm p θ u = 2 * (flowOf p θ σ 0 1 * (u (σ 0) - u (σ 1)) ^ 3 +
      flowOf p θ σ 0 2 * (u (σ 0) - u (σ 2)) ^ 3 + flowOf p θ σ 0 3 * (u (σ 0) - u (σ 3)) ^ 3 +
      flowOf p θ σ 1 2 * (u (σ 1) - u (σ 2)) ^ 3 + flowOf p θ σ 1 3 * (u (σ 1) - u (σ 3)) ^ 3 +
      flowOf p θ σ 2 3 * (u (σ 2) - u (σ 3)) ^ 3) := by
  unfold cubicForm
  rw [← Equiv.sum_comp σ]
  simp_rw [← Equiv.sum_comp σ (fun j => p.B _ j * _ * _)]
  refine (sum_four_pairs (fun i j => p.B (σ i) (σ j) * Real.sin (θ (σ i) - θ (σ j)) *
    (u (σ i) - u (σ j)) ^ 3) (fun i j => ?_) (fun i => by simp)).trans (by simp [flowOf])
  rw [p.B_symm, show θ (σ j) - θ (σ i) = -(θ (σ i) - θ (σ j)) by ring, Real.sin_neg]
  ring

@[powerlib_foundation] theorem weightOf_swap (p : Params 3) (θ : Fin (3 + 1) → ℝ)
    (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    p.B (σ j) (σ i) * Real.cos (θ (σ j) - θ (σ i)) = weightOf p θ σ i j := by
  rw [weightOf, p.B_symm, show θ (σ j) - θ (σ i) = -(θ (σ i) - θ (σ j)) by ring, Real.cos_neg]

@[powerlib_foundation] theorem flowOf_swap (p : Params 3) (θ : Fin (3 + 1) → ℝ)
    (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    p.B (σ j) (σ i) * Real.sin (θ (σ j) - θ (σ i)) = -flowOf p θ σ i j := by
  rw [flowOf, p.B_symm, show θ (σ j) - θ (σ i) = -(θ (σ i) - θ (σ j)) by ring, Real.sin_neg]
  ring

@[powerlib_foundation] theorem B_pos_of_weightOf_ne (p : Params 3) (θ : Fin (3 + 1) → ℝ)
    (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (h : weightOf p θ σ i j ≠ 0) :
    0 < p.B (σ i) (σ j) :=
  lt_of_le_of_ne (p.B_nonneg _ _) fun h0 => h (by rw [weightOf, ← h0, zero_mul])

/-- No linearized flow on the six labelled lines means no linearized flow on any line. -/
@[powerlib_foundation] theorem flat_of_labelled {p : Params 3} {θ u : Fin (3 + 1) → ℝ}
    {σ : Equiv.Perm (Fin 4)} (h01 : weightOf p θ σ 0 1 * (u (σ 0) - u (σ 1)) = 0)
    (h02 : weightOf p θ σ 0 2 * (u (σ 0) - u (σ 2)) = 0)
    (h03 : weightOf p θ σ 0 3 * (u (σ 0) - u (σ 3)) = 0)
    (h12 : weightOf p θ σ 1 2 * (u (σ 1) - u (σ 2)) = 0)
    (h13 : weightOf p θ σ 1 3 * (u (σ 1) - u (σ 3)) = 0)
    (h23 : weightOf p θ σ 2 3 * (u (σ 2) - u (σ 3)) = 0) :
    ∀ k j, p.B k j * Real.cos (θ k - θ j) * (u k - u j) = 0 := by
  have h : ∀ i j : Fin 4, i < j → weightOf p θ σ i j * (u (σ i) - u (σ j)) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption
  intro k j
  rw [← σ.apply_symm_apply k, ← σ.apply_symm_apply j]
  rcases lt_trichotomy (σ.symm k) (σ.symm j) with hlt | heq | hgt
  · exact h _ _ hlt
  · rw [heq]; simp
  · have := h _ _ hgt
    rw [← weightOf_swap] at this
    linear_combination -this

/-- Node balances of a null direction of a positive semidefinite form on four machines. -/
@[powerlib_foundation] theorem null_four {w01 w02 w03 w12 w13 w23 g₀ g₁ g₂ g₃ : ℝ}
    (hQ : ∀ a b c d : ℝ, 0 ≤ w01 * (a - b) ^ 2 + w02 * (a - c) ^ 2 + w03 * (a - d) ^ 2 +
      w12 * (b - c) ^ 2 + w13 * (b - d) ^ 2 + w23 * (c - d) ^ 2)
    (h0 : w01 * (g₀ - g₁) ^ 2 + w02 * (g₀ - g₂) ^ 2 + w03 * (g₀ - g₃) ^ 2 +
      w12 * (g₁ - g₂) ^ 2 + w13 * (g₁ - g₃) ^ 2 + w23 * (g₂ - g₃) ^ 2 = 0) :
    w01 * (g₀ - g₁) + w02 * (g₀ - g₂) + w03 * (g₀ - g₃) = 0 ∧
    w01 * (g₁ - g₀) + w12 * (g₁ - g₂) + w13 * (g₁ - g₃) = 0 ∧
    w02 * (g₂ - g₀) + w12 * (g₂ - g₁) + w23 * (g₂ - g₃) = 0 ∧
    w03 * (g₃ - g₀) + w13 * (g₃ - g₁) + w23 * (g₃ - g₂) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := eq_zero_of_forall_linear_quadratic_nonneg
      (L := 2 * (w01 * (g₀ - g₁) + w02 * (g₀ - g₂) + w03 * (g₀ - g₃)))
      (Q := w01 + w02 + w03) fun x => by
        have h := hQ (g₀ + x) g₁ g₂ g₃
        linear_combination h + h0
    linarith
  · have := eq_zero_of_forall_linear_quadratic_nonneg
      (L := 2 * (w01 * (g₁ - g₀) + w12 * (g₁ - g₂) + w13 * (g₁ - g₃)))
      (Q := w01 + w12 + w13) fun x => by
        have h := hQ g₀ (g₁ + x) g₂ g₃
        linear_combination h + h0
    linarith
  · have := eq_zero_of_forall_linear_quadratic_nonneg
      (L := 2 * (w02 * (g₂ - g₀) + w12 * (g₂ - g₁) + w23 * (g₂ - g₃)))
      (Q := w02 + w12 + w23) fun x => by
        have h := hQ g₀ g₁ (g₂ + x) g₃
        linear_combination h + h0
    linarith
  · have := eq_zero_of_forall_linear_quadratic_nonneg
      (L := 2 * (w03 * (g₃ - g₀) + w13 * (g₃ - g₁) + w23 * (g₃ - g₂)))
      (Q := w03 + w13 + w23) fun x => by
        have h := hQ g₀ g₁ g₂ (g₃ + x)
        linear_combination h + h0
    linarith

/-- Implementation evidence for `not_localAsymptoticStable_four`, at the selected point of the
untranslated field. -/
private theorem reducedSwing_not_localAsymptoticStable_four (p : Params 3)
    (θ : Fin (3 + 1) → ℝ) (σ : Equiv.Perm (Fin 4)) (h13 : p.B (σ 1) (σ 3) = 0)
    (hsp : p.B (σ 0) (σ 2) = 0 ∨ p.B (σ 0) (σ 3) = 0)
    (hbal : ∀ k, p.P k = powerInjection p.B θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian p θ)) :
    ¬ LocalAsymptoticStable (reducedField p) (equilibrium θ) := by
  intro hLAS
  have hF := reducedSwing_hessForm_nonneg_of_localAsymptoticStable hbal hLAS
  have hK := reducedSwing_cubicForm_eq_zero_of_localAsymptoticStable hbal hLAS
  obtain ⟨u, hu0, hu, hle⟩ := exists_hessForm_nonpos hH
  have hQ0 : hessForm p θ u = 0 := le_antisymm hle (hF u)
  have hC0 := hK u hQ0
  obtain ⟨k₁, hk₁⟩ : ∃ k, u k ≠ u 0 := by
    by_contra h
    push Not at h
    apply hu
    funext k
    rw [h k, hu0]
    rfl
  have hflat : weightOf p θ σ 0 1 * (u (σ 0) - u (σ 1)) = 0 →
      weightOf p θ σ 0 2 * (u (σ 0) - u (σ 2)) = 0 →
      weightOf p θ σ 0 3 * (u (σ 0) - u (σ 3)) = 0 →
      weightOf p θ σ 1 2 * (u (σ 1) - u (σ 2)) = 0 →
      weightOf p θ σ 1 3 * (u (σ 1) - u (σ 3)) = 0 →
      weightOf p θ σ 2 3 * (u (σ 2) - u (σ 3)) = 0 → False :=
    fun h01 h02 h03 h12 h13 h23 => reducedSwing_not_localAsymptoticStable_of_flat hbal u hk₁
      (flat_of_labelled h01 h02 h03 h12 h13 h23) hLAS
  -- the forms in labelled coordinates
  have hQ : ∀ g₀ g₁ g₂ g₃ : ℝ, 0 ≤ weightOf p θ σ 0 1 * (g₀ - g₁) ^ 2 +
      weightOf p θ σ 0 2 * (g₀ - g₂) ^ 2 + weightOf p θ σ 0 3 * (g₀ - g₃) ^ 2 +
      weightOf p θ σ 1 2 * (g₁ - g₂) ^ 2 + weightOf p θ σ 1 3 * (g₁ - g₃) ^ 2 +
      weightOf p θ σ 2 3 * (g₂ - g₃) ^ 2 := by
    intro g₀ g₁ g₂ g₃
    have := hF (fun k => ![g₀, g₁, g₂, g₃] (σ.symm k))
    rw [hessForm_four p θ _ σ] at this
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
    linarith
  rw [hessForm_four p θ u σ] at hQ0
  rw [cubicForm_four p θ u σ] at hC0
  have hw13 : weightOf p θ σ 1 3 = 0 := by rw [weightOf, h13, zero_mul]
  have hf13 : flowOf p θ σ 1 3 = 0 := by rw [flowOf, h13, zero_mul]
  generalize hg₀ : u (σ 0) = g₀ at hQ0 hC0 hflat
  generalize hg₁ : u (σ 1) = g₁ at hQ0 hC0 hflat
  generalize hg₂ : u (σ 2) = g₂ at hQ0 hC0 hflat
  generalize hg₃ : u (σ 3) = g₃ at hQ0 hC0 hflat
  obtain ⟨N0, N1, N2, N3⟩ := null_four hQ (g₀ := g₀) (g₁ := g₁) (g₂ := g₂) (g₃ := g₃)
    (by linarith)
  rw [hw13] at N1 N3 hQ hflat
  rw [hf13] at hC0
  rw [hw13] at hQ0
  simp only [zero_mul, add_zero] at N1 N3 hQ hC0 hflat hQ0
  rcases hsp with h02 | h03
  · -- the lines lie on the four-cycle `σ0 σ1 σ2 σ3`
    have hw02 : weightOf p θ σ 0 2 = 0 := by rw [weightOf, h02, zero_mul]
    have hf02 : flowOf p θ σ 0 2 = 0 := by rw [flowOf, h02, zero_mul]
    rw [hw02] at N0 N2 hQ hflat
    rw [hf02] at hC0
    simp only [zero_mul, add_zero, zero_add] at N0 N2 hQ hC0 hflat
    have e₂ : weightOf p θ σ 1 2 * (g₁ - g₂) = weightOf p θ σ 0 1 * (g₀ - g₁) := by
      linear_combination N1
    have e₃ : weightOf p θ σ 2 3 * (g₂ - g₃) = weightOf p θ σ 0 1 * (g₀ - g₁) := by
      linear_combination N1 + N2
    have e₄ : p.B (σ 3) (σ 0) * Real.cos (θ (σ 3) - θ (σ 0)) * (g₃ - g₀) =
        weightOf p θ σ 0 1 * (g₀ - g₁) := by rw [weightOf_swap]; linear_combination -N0
    by_cases hκ : weightOf p θ σ 0 1 * (g₀ - g₁) = 0
    · exact hflat hκ trivial (by linear_combination N0 - hκ) (by linear_combination N1 + hκ)
        trivial (by linear_combination N1 + N2 + hκ)
    have hne : ∀ {i j : Fin 4} {x : ℝ}, weightOf p θ σ i j * x =
        weightOf p θ σ 0 1 * (g₀ - g₁) → 0 < p.B (σ i) (σ j) := fun h =>
      B_pos_of_weightOf_ne p θ σ fun h0 => hκ (by rw [← h, h0, zero_mul])
    have hB₄ : 0 < p.B (σ 3) (σ 0) := by
      rw [p.B_symm]
      exact hne (x := g₃ - g₀) (by linear_combination -N0)
    have p₁₂ := hQ 1 0 1 1
    have p₁₃ := hQ 1 0 0 1
    have p₁₄ := hQ 1 0 0 0
    have p₂₃ := hQ 0 0 1 0
    have p₂₄ := hQ 0 0 1 1
    have p₃₄ := hQ 0 0 0 1
    norm_num at p₁₂ p₁₃ p₁₄ p₂₃ p₂₄ p₃₄
    have hcub := ring_cubic_ne_zero (φ₁ := θ (σ 0) - θ (σ 1)) (φ₂ := θ (σ 1) - θ (σ 2))
      (φ₃ := θ (σ 2) - θ (σ 3)) (φ₄ := θ (σ 3) - θ (σ 0)) (x₁ := g₀ - g₁) (x₂ := g₁ - g₂)
      (x₃ := g₂ - g₃) (x₄ := g₃ - g₀) (hne rfl) (hne e₂) (hne e₃) hB₄ (by ring) (by ring) rfl e₂
      e₃ e₄ hκ (by unfold weightOf at p₁₂; linarith) (by unfold weightOf at p₁₃; linarith)
      (by rw [weightOf_swap p θ σ 0 3]; unfold weightOf at p₁₄ ⊢; linarith)
      (by unfold weightOf at p₂₃; linarith)
      (by rw [weightOf_swap p θ σ 0 3]; unfold weightOf at p₂₄ ⊢; linarith)
      (by rw [weightOf_swap p θ σ 0 3]; unfold weightOf at p₃₄ ⊢; linarith)
    rw [flowOf_swap p θ σ 0 3] at hcub
    apply hcub
    change flowOf p θ σ 0 1 * (g₀ - g₁) ^ 3 + flowOf p θ σ 1 2 * (g₁ - g₂) ^ 3 +
      flowOf p θ σ 2 3 * (g₂ - g₃) ^ 3 + -flowOf p θ σ 0 3 * (g₃ - g₀) ^ 3 = 0
    linear_combination hC0 / 2
  · -- a triangle `σ0 σ1 σ2` with the pendant line `σ2 σ3`
    have hw03 : weightOf p θ σ 0 3 = 0 := by rw [weightOf, h03, zero_mul]
    have hf03 : flowOf p θ σ 0 3 = 0 := by rw [flowOf, h03, zero_mul]
    rw [hw03] at N0 N3 hQ hflat hQ0
    rw [hf03] at hC0
    simp only [zero_mul, add_zero, zero_add] at N0 N3 hQ hC0 hflat hQ0
    by_cases hw23 : weightOf p θ σ 2 3 = 0
    · -- the pendant machine is cut off by zero-weight lines
      refine reducedSwing_not_localAsymptoticStable_of_zero_cut hbal {σ 3} ?_ (i₀ := σ 3)
        (j₀ := σ 0)
        (Finset.mem_singleton_self _) (by simp) hLAS
      intro i hi j hj
      rw [Finset.mem_singleton] at hi hj
      subst hi
      rw [← σ.apply_symm_apply j] at hj ⊢
      have h3 : σ.symm j ≠ 3 := fun h => hj (by rw [h])
      generalize σ.symm j = i' at h3 ⊢
      fin_cases i'
      · exact (weightOf_swap p θ σ 0 3).trans hw03
      · exact (weightOf_swap p θ σ 1 3).trans hw13
      · exact (weightOf_swap p θ σ 2 3).trans hw23
      · exact absurd rfl h3
    have hg₃₂ : g₃ = g₂ := by
      have := (mul_eq_zero.mp N3).resolve_left hw23
      linarith
    subst hg₃₂
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, add_zero] at hC0 hQ0
    have e₂ : weightOf p θ σ 1 2 * (g₁ - g₃) = weightOf p θ σ 0 1 * (g₀ - g₁) := by
      linear_combination N1
    have e₃ : p.B (σ 2) (σ 0) * Real.cos (θ (σ 2) - θ (σ 0)) * (g₃ - g₀) =
        weightOf p θ σ 0 1 * (g₀ - g₁) := by rw [weightOf_swap]; linear_combination -N0
    by_cases hκ : weightOf p θ σ 0 1 * (g₀ - g₁) = 0
    · exact hflat hκ (by linear_combination N0 - hκ) trivial (by linear_combination N1 + hκ)
        trivial (by ring)
    have hne : ∀ {i j : Fin 4} {x : ℝ}, weightOf p θ σ i j * x =
        weightOf p θ σ 0 1 * (g₀ - g₁) → 0 < p.B (σ i) (σ j) := fun h =>
      B_pos_of_weightOf_ne p θ σ fun h0 => hκ (by rw [← h, h0, zero_mul])
    have hB₃ : 0 < p.B (σ 2) (σ 0) := by
      rw [p.B_symm]
      exact hne (x := g₃ - g₀) (by linear_combination -N0)
    have p₁₂ := hQ 1 0 1 1
    have p₂₃ := hQ 0 0 1 1
    have p₁₃ := hQ 1 0 0 0
    norm_num at p₁₂ p₂₃ p₁₃
    have hnot : ¬ (0 < Real.cos (θ (σ 0) - θ (σ 1)) ∧ 0 < Real.cos (θ (σ 1) - θ (σ 2)) ∧
        0 < Real.cos (θ (σ 2) - θ (σ 0))) := by
      rintro ⟨c₁, c₂, c₃⟩
      have w₁ : 0 < weightOf p θ σ 0 1 := mul_pos (hne rfl) c₁
      have w₂ : 0 < weightOf p θ σ 1 2 := mul_pos (hne e₂) c₂
      have w₃ : 0 < weightOf p θ σ 0 2 := by rw [← weightOf_swap]; exact mul_pos hB₃ c₃
      have hx : g₀ - g₁ ≠ 0 := fun h => hκ (by rw [h, mul_zero])
      have : 0 < weightOf p θ σ 0 1 * (g₀ - g₁) ^ 2 := mul_pos w₁ (by positivity)
      have : 0 ≤ weightOf p θ σ 0 2 * (g₀ - g₃) ^ 2 := mul_nonneg w₃.le (sq_nonneg _)
      have : 0 ≤ weightOf p θ σ 1 2 * (g₁ - g₃) ^ 2 := mul_nonneg w₂.le (sq_nonneg _)
      linarith
    have hcub := triangle_cubic_ne_zero (α := θ (σ 0) - θ (σ 1)) (β := θ (σ 1) - θ (σ 2))
      (γ := θ (σ 2) - θ (σ 0)) (x₁ := g₀ - g₁) (x₂ := g₁ - g₃) (x₃ := g₃ - g₀) (hne rfl)
      (hne e₂) hB₃ (by ring) rfl e₂ e₃ hκ (by unfold weightOf at p₁₂; linarith)
      (by rw [weightOf_swap p θ σ 0 2]; unfold weightOf at p₂₃ ⊢; linarith)
      (by rw [weightOf_swap p θ σ 0 2]; unfold weightOf at p₁₃ ⊢; linarith) hnot
    rw [flowOf_swap p θ σ 0 2] at hcub
    apply hcub
    change flowOf p θ σ 0 1 * (g₀ - g₁) ^ 3 + flowOf p θ σ 1 2 * (g₁ - g₃) ^ 3 +
      -flowOf p θ σ 0 2 * (g₃ - g₀) ^ 3 = 0
    linear_combination hC0 / 2

/-- **Four machines with two uncoupled pairs (at most four lines).** Label the machines by `σ` so
that the pair `σ1, σ3` is uncoupled and so is `σ0, σ2` (the lines form a subgraph of the
four-cycle `σ0 σ1 σ2 σ3`) or `σ0, σ3` (a triangle `σ0 σ1 σ2` with the pendant line `σ2 σ3`). At a
power-balance point with a non-Hurwitz reduced Jacobian the model is not locally asymptotically
stable: a negative Hessian value is a saddle; a null direction without circulation
cuts off zero-weight lines (`not_localAsymptoticStable_of_flat`); a circulation on the four-cycle
has exactly one negative weight and a nonzero cubic term (`ring_cubic_ne_zero`); a circulation on
the triangle has a nonzero cubic term (`triangle_cubic_ne_zero`); a zero-weight pendant line is a
zero-weight cut (`not_localAsymptoticStable_of_zero_cut`). -/
@[powerlib_domain] theorem not_localAsymptoticStable_four (m : Model 3)
    (σ : Equiv.Perm (Fin 4)) (h13 : m.params.B (σ 1) (σ 3) = 0)
    (hsp : m.params.B (σ 0) (σ 2) = 0 ∨ m.params.B (σ 0) (σ 3) = 0)
    (hbal : ∀ k, m.params.P k = powerInjection m.params.B m.θ k)
    (hH : ¬ LinearSystems.IsHurwitz (jacobian m.params m.θ)) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_four]
  exact reducedSwing_not_localAsymptoticStable_four m.params m.θ σ h13 hsp hbal hH

/-! ## The family: four machines with at most four lines -/

private theorem powerFlow_of_equilibrium_four {p : Params n} {θ : Fin (n + 1) → ℝ}
    (h : reducedField p (equilibrium θ) = 0) : ∀ k, p.P k = powerInjection p.B θ k := by
  intro k
  have hk := congrArg (fun z : State (n + (n + 1)) => z (wIdx k)) h
  simp only [reducedField_wIdx, equilibrium, reduce_wIdx, angleMap_reduce,
    powerInjection_add_const, PiLp.zero_apply] at hk
  rw [div_eq_zero_iff, or_iff_left (p.M_pos k).ne'] at hk
  simp only [Pi.zero_apply, mul_zero, sub_zero] at hk
  linarith

/-- **Four machines with at most four lines: the local asymptotic translation is exact.** Label
the machines by `σ` so that the pairs `σ1, σ3` and either `σ0, σ2` (the lines lie on the four-cycle
`σ0 σ1 σ2 σ3`) or `σ0, σ3` (a triangle `σ0 σ1 σ2` with the pendant line `σ2 σ3`) are uncoupled;
every four-machine network with two uncoupled pairs has such a labelling. Then the model is
locally asymptotically stable exactly when its profile is a power-balance point with a Hurwitz
reduced Jacobian. -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_four (m : Model 3)
    (σ : Equiv.Perm (Fin 4)) (h13 : m.params.B (σ 1) (σ 3) = 0)
    (hsp : m.params.B (σ 0) (σ 2) = 0 ∨ m.params.B (σ 0) (σ 3) = 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      (∀ k, m.params.P k = powerInjection m.params.B m.θ k) ∧
      LinearSystems.IsHurwitz (jacobian m.params m.θ)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow_iff_four]
  change LocalAsymptoticStable _ _ ↔ _
  constructor
  · intro hLAS
    have hp := powerFlow_of_equilibrium_four (Dynamics.isEquilibrium_of_lyapunovStable
      (reducedField_contDiff m.params) hLAS.1)
    refine ⟨hp, ?_⟩
    by_contra hH
    exact reducedSwing_not_localAsymptoticStable_four m.params m.θ σ h13 hsp hp hH hLAS
  · rintro ⟨hp, hH⟩
    exact Flow.locallyExponentiallyStable_localAsymptoticStable
      (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian (jacobian m.params m.θ)
        (reducedField_contDiff m.params) (reducedField_equilibrium m.params m.θ hp)
        (hasFDerivAt_reducedField m.params m.θ).fderiv hH)

end powerlib.Network.Swing
