import theorem.PortHamiltonian
import theorem.Dynamics.ExponentialStability

/-! # Staggered-grid RLCG ladder as a port-Hamiltonian model

Source: work-sync `theory/T-method-of-lines.md` §1.3 (staggered grid,
`L' i̇_{j+1/2} = -(v_{j+1}-v_j)/Δx - R' i_{j+1/2}`,
`C' v̇_j = -(i_{j+1/2}-i_{j-1/2})/Δx - G' v_j`), and the passivity remark of
`theory/T-pde-systems.md` §2.7.

Model boundary.
* A uniform line cut into `N` cells of length `Δx > 0`. Cell `k` (`k = 0, …, N-1`)
  is a series inductor `L'Δx` with series resistor `R'Δx`, followed by a shunt
  capacitor `C'Δx` with shunt conductance `G'Δx` at node `k`.
* State order `ι = Fin N ⊕ Fin N`: `inl k` is the inductor flux `φ_k = L'Δx · i_k`,
  `inr k` is the capacitor charge `q_k = C'Δx · v_k`.
* Ports `Fin 2`: port `0` is an ideal voltage source `v₁` at the sending end
  (driving inductor `0`); port `1` is an ideal current sink `i₂` drawn out of node
  `N-1` at the receiving end. Through-convention (work-sync `conventions` §D10):
  `i_0` flows into the line at end 1, `i₂` flows out of it at end 2; the port
  supply is `v₁ i_0 - v_{N-1} i₂`.
* Constant parameters `L', C' > 0`, `R', G' ≥ 0`; no frequency dependence, no PWM,
  no delay, no controller, continuous time. The theorems concern this finite
  lumped ladder only: nothing here claims convergence to the telegrapher PDE.

Results: the ladder is a `PortHamiltonian.Model` (skew interconnection, nonnegative
diagonal damping, positive weights), hence passive with the stored electric plus
magnetic energy and Lyapunov stable. With `R' > 0` and `G' > 0` the zero-input
ladder is globally exponentially stable (trajectory level). The general step,
"every strictly damped diagonal port-Hamiltonian model is globally exponentially
stable", is proved with the stored energy as Lyapunov function.

Correction (T-pde-systems §2.7 "电报方程满足能量守恒"): the lossy ladder does
not conserve energy; along every nonzero zero-input solution the stored energy
strictly decreases (`lossyLadder_energy_strictly_decreases`). Energy is conserved
only in the lossless case `R' = G' = 0` (`losslessLadder_energy_conserved`).
-/

noncomputable section
namespace powerlib.Line
open Matrix Set

/-! ## Strictly damped port-Hamiltonian models -/

namespace PHStrict

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

@[powerlib_foundation] theorem exists_pos_lower {ι : Type*} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ c > 0, ∀ i, c ≤ f i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_hasFDerivAt (m : PortHamiltonian.Model ι κ)
    (x : ι → ℝ) :
    HasFDerivAt (PortHamiltonian.energy m)
      (∑ i, (m.w i * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) x := by
  have h : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun y : ι → ℝ => m.w i * y i ^ 2 / 2)
      ((m.w i * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) x := by
    intro i _
    have hp := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) i x).pow 2).const_mul
      (m.w i / 2)
    convert hp using 1
    · funext y; ring
    · ext v
      simp
      ring
  exact HasFDerivAt.fun_sum h

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem fderiv_energy_apply (m : PortHamiltonian.Model ι κ)
    (x v : ι → ℝ) :
    fderiv ℝ (PortHamiltonian.energy m) x v = dotProduct (PortHamiltonian.gradient m x) v := by
  rw [(energy_hasFDerivAt m x).fderiv]
  simp [dotProduct, PortHamiltonian.gradient]

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_contDiff (m : PortHamiltonian.Model ι κ) :
    ContDiff ℝ 1 (PortHamiltonian.energy m) := by
  unfold PortHamiltonian.energy
  apply ContDiff.sum
  intro i _
  exact ((contDiff_const.mul ((contDiff_apply ℝ ℝ i).pow 2)).div_const 2)

@[powerlib_foundation] theorem zeroInput_contDiff (m : PortHamiltonian.Model ι κ) :
    ContDiff ℝ 1 (fun x => PortHamiltonian.field m x 0) := by
  have h : (fun x => PortHamiltonian.field m x 0) = PortHamiltonian.operator m := by
    funext x
    exact (PortHamiltonian.operator_field m x).symm
  rw [h]
  exact (PortHamiltonian.operator m).contDiff

/-- The stored energy as an exponential-decay certificate, for strictly positive damping. -/
def certificate (m : PortHamiltonian.Model ι κ) (hd : ∀ i, 0 < m.d i) :
    Dynamics.QuadraticDecayCertificate (fun x => PortHamiltonian.field m x 0)
      (PortHamiltonian.energy m) 0 :=
  let hw := exists_pos_lower m.w m.weights_pos
  let hr := exists_pos_lower (fun i => 2 * m.d i * m.w i)
    (fun i => mul_pos (mul_pos two_pos (hd i)) (m.weights_pos i))
  { lower := hw.choose / 2
    upper := (∑ i, m.w i) / 2 + 1
    rate := hr.choose
    lower_pos := half_pos hw.choose_spec.1
    upper_pos := by
      have : 0 ≤ ∑ i, m.w i := Finset.sum_nonneg fun i _ => (m.weights_pos i).le
      positivity
    rate_pos := hr.choose_spec.1
    smooth := energy_contDiff m
    equilibrium_field := by simp [PortHamiltonian.field]
    equilibrium_value := PortHamiltonian.energy_zero m
    lower_bound := by
      intro x
      simp only [sub_zero]
      have hsq : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
        have hle : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
          refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
          rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
          exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => x j ^ 2)
            (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
        calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hle 2
          _ = ∑ i, x i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
      calc hw.choose / 2 * ‖x‖ ^ 2 ≤ hw.choose / 2 * ∑ i, x i ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (half_pos hw.choose_spec.1).le
        _ = ∑ i, hw.choose * x i ^ 2 / 2 := by rw [Finset.mul_sum]; congr 1; ext i; ring
        _ ≤ ∑ i, m.w i * x i ^ 2 / 2 := by
            apply Finset.sum_le_sum
            intro i _
            have := hw.choose_spec.2 i
            have := sq_nonneg (x i)
            nlinarith
    upper_bound := by
      intro x
      simp only [sub_zero]
      have hx : ∀ i, x i ^ 2 ≤ ‖x‖ ^ 2 := fun i => by
        have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at h1
        calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
          _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc PortHamiltonian.energy m x = ∑ i, m.w i * x i ^ 2 / 2 := rfl
        _ ≤ ∑ i, m.w i * ‖x‖ ^ 2 / 2 := by
            apply Finset.sum_le_sum
            intro i _
            have := m.weights_pos i
            have := hx i
            nlinarith
        _ = (∑ i, m.w i) / 2 * ‖x‖ ^ 2 := by rw [Finset.sum_div, Finset.sum_mul]; congr 1; ext i; ring
        _ ≤ ((∑ i, m.w i) / 2 + 1) * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    dissipation := by
      intro x
      rw [fderiv_energy_apply, PortHamiltonian.power_balance, Passivity.supply_zero, zero_sub]
      have hterm : ∀ i, hr.choose * (m.w i * x i ^ 2 / 2) ≤
          m.d i * PortHamiltonian.gradient m x i ^ 2 := by
        intro i
        have h1 := hr.choose_spec.2 i
        have h2 : 0 ≤ m.w i * x i ^ 2 / 2 := by
          have := (m.weights_pos i).le; positivity
        have h3 : m.d i * PortHamiltonian.gradient m x i ^ 2 =
            (2 * m.d i * m.w i) * (m.w i * x i ^ 2 / 2) := by
          simp only [PortHamiltonian.gradient]; ring
        rw [h3]
        exact mul_le_mul_of_nonneg_right h1 h2
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hterm i)
      rw [← Finset.mul_sum] at hsum
      change -(∑ i, m.d i * PortHamiltonian.gradient m x i ^ 2) ≤
        -hr.choose * ∑ i, m.w i * x i ^ 2 / 2
      linarith }

/-- A diagonal port-Hamiltonian model whose every state is damped is globally
exponentially stable with zero input: equilibrium, global existence, and a uniform
exponential bound on every solution segment. -/
@[powerlib_domain] theorem globallyExponentiallyStable (m : PortHamiltonian.Model ι κ)
    (hd : ∀ i, 0 < m.d i) :
    Dynamics.GloballyExponentiallyStable (fun x => PortHamiltonian.field m x 0) 0 :=
  (certificate m hd).globallyExponentiallyStable (zeroInput_contDiff m)

end PHStrict

/-! ## The RLCG ladder -/

/-- Per-unit-length line constants and the cell length. -/
structure LadderParams where
  L' : ℝ
  C' : ℝ
  R' : ℝ
  G' : ℝ
  Δx : ℝ
  L'_pos : 0 < L'
  C'_pos : 0 < C'
  R'_nonneg : 0 ≤ R'
  G'_nonneg : 0 ≤ G'
  Δx_pos : 0 < Δx

namespace Ladder

variable (p : LadderParams) (N : ℕ)

/-- Index of the ladder state: `inl k` = inductor flux `φ_k`, `inr k` = capacitor charge `q_k`. -/
abbrev Idx (N : ℕ) := Fin N ⊕ Fin N

/-- Interconnection entries: KVL for each inductor, KCL for each capacitor node. -/
def Jfun : Idx N → Idx N → ℝ
  | .inl k, .inr j => if j = k then -1 else if j.val + 1 = k.val then 1 else 0
  | .inr k, .inl j => if j = k then 1 else if j.val = k.val + 1 then -1 else 0
  | .inl _, .inl _ => 0
  | .inr _, .inr _ => 0

/-- Port entries: the source voltage drives inductor `0`; the sink current leaves node `N-1`. -/
def Bfun : Idx N → Fin 2 → ℝ
  | .inl k, c => if c = 0 ∧ k.val = 0 then 1 else 0
  | .inr k, c => if c = 1 ∧ k.val + 1 = N then -1 else 0

def J : Matrix (Idx N) (Idx N) ℝ := Matrix.of (Jfun N)

def B : Matrix (Idx N) (Fin 2) ℝ := Matrix.of (Bfun N)

@[powerlib_foundation] theorem J_skew : (J N).transpose = -(J N) := by
  ext a b
  rcases a with k | k <;> rcases b with j | j <;>
    simp only [transpose_apply, J, of_apply, Jfun, Matrix.neg_apply, neg_zero]
  · split_ifs <;> (try subst_vars) <;> simp_all
  · split_ifs <;> (try subst_vars) <;> simp_all

/-- The staggered RLCG ladder as a port-Hamiltonian model. -/
def model : PortHamiltonian.Model (Idx N) (Fin 2) where
  J := J N
  d := Sum.elim (fun _ => p.R' * p.Δx) (fun _ => p.G' * p.Δx)
  w := Sum.elim (fun _ => 1 / (p.L' * p.Δx)) (fun _ => 1 / (p.C' * p.Δx))
  B := B N
  skew := J_skew N
  damping_nonneg := fun a => by
    rcases a with _ | _
    · exact mul_nonneg p.R'_nonneg p.Δx_pos.le
    · exact mul_nonneg p.G'_nonneg p.Δx_pos.le
  weights_pos := fun a => by
    rcases a with _ | _
    · exact one_div_pos.mpr (mul_pos p.L'_pos p.Δx_pos)
    · exact one_div_pos.mpr (mul_pos p.C'_pos p.Δx_pos)

/-- Inductor current `i_k = φ_k / (L'Δx)`. -/
def current (x : Idx N → ℝ) (k : Fin N) : ℝ := x (.inl k) / (p.L' * p.Δx)

/-- Node voltage `v_k = q_k / (C'Δx)`. -/
def voltage (x : Idx N → ℝ) (k : Fin N) : ℝ := x (.inr k) / (p.C' * p.Δx)

/-- Voltage at the left terminal of inductor `k`: the source for `k = 0`, else node `k-1`. -/
def leftVoltage (x : Idx N → ℝ) (u : Fin 2 → ℝ) (k : Fin N) : ℝ :=
  if h : k.val = 0 then u 0 else voltage p N x ⟨k.val - 1, by omega⟩

/-- Current leaving node `k` to the right: the next inductor, or the sink at the end. -/
def rightCurrent (x : Idx N → ℝ) (u : Fin 2 → ℝ) (k : Fin N) : ℝ :=
  if h : k.val + 1 = N then u 1 else current p N x ⟨k.val + 1, by omega⟩

omit p in
@[powerlib_foundation] theorem sum_prev (k : Fin N) (g : Fin N → ℝ) :
    ∑ j : Fin N, (if j.val + 1 = k.val then g j else 0) =
      if h : k.val = 0 then 0 else g ⟨k.val - 1, by omega⟩ := by
  split_ifs with h
  · exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
  · rw [Finset.sum_eq_single ⟨k.val - 1, by omega⟩]
    · exact if_pos (by simp only; omega)
    · intro j _ hj
      exact if_neg fun h' => hj (Fin.ext (by simp only; omega))
    · exact fun h' => absurd (Finset.mem_univ _) h'

omit p in
@[powerlib_foundation] theorem sum_next (k : Fin N) (g : Fin N → ℝ) :
    ∑ j : Fin N, (if j.val = k.val + 1 then g j else 0) =
      if h : k.val + 1 = N then 0 else g ⟨k.val + 1, by omega⟩ := by
  split_ifs with h
  · exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
  · rw [Finset.sum_eq_single ⟨k.val + 1, by omega⟩]
    · exact if_pos rfl
    · intro j _ hj
      exact if_neg fun h' => hj (Fin.ext h')
    · exact fun h' => absurd (Finset.mem_univ _) h'

omit p in
@[powerlib_foundation] theorem sum_kvl (k : Fin N) (g : Fin N → ℝ) :
    ∑ j : Fin N, (if j = k then -1 else if j.val + 1 = k.val then 1 else 0) * g j =
      -g k + if h : k.val = 0 then 0 else g ⟨k.val - 1, by omega⟩ := by
  rw [← sum_prev N k g]
  calc ∑ j : Fin N, (if j = k then -1 else if j.val + 1 = k.val then 1 else 0) * g j
      = ∑ j : Fin N, ((if j = k then -g j else 0) + (if j.val + 1 = k.val then g j else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k
        · subst hj; simp
        · by_cases h' : j.val + 1 = k.val <;> simp [hj, h']
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp

omit p in
@[powerlib_foundation] theorem sum_kcl (k : Fin N) (g : Fin N → ℝ) :
    ∑ j : Fin N, (if j = k then 1 else if j.val = k.val + 1 then -1 else 0) * g j =
      g k - if h : k.val + 1 = N then 0 else g ⟨k.val + 1, by omega⟩ := by
  rw [← sum_next N k g]
  calc ∑ j : Fin N, (if j = k then 1 else if j.val = k.val + 1 then -1 else 0) * g j
      = ∑ j : Fin N, ((if j = k then g j else 0) - (if j.val = k.val + 1 then g j else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k
        · subst hj; simp
        · by_cases h' : j.val = k.val + 1 <;> simp [hj, h']
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']; simp

@[powerlib_foundation] theorem gradient_inl (x : Idx N → ℝ) (k : Fin N) :
    PortHamiltonian.gradient (model p N) x (.inl k) = current p N x k := by
  simp [PortHamiltonian.gradient, model, current]; ring

@[powerlib_foundation] theorem gradient_inr (x : Idx N → ℝ) (k : Fin N) :
    PortHamiltonian.gradient (model p N) x (.inr k) = voltage p N x k := by
  simp [PortHamiltonian.gradient, model, voltage]; ring

/-- KVL of cell `k`: `φ̇_k = v_left - v_k - R'Δx i_k`. -/
@[powerlib_domain] theorem field_flux (x : Idx N → ℝ) (u : Fin 2 → ℝ) (k : Fin N) :
    PortHamiltonian.field (model p N) x u (.inl k) =
      leftVoltage p N x u k - voltage p N x k - p.R' * p.Δx * current p N x k := by
  simp only [PortHamiltonian.field, sub_mulVec, Pi.add_apply, Pi.sub_apply, mulVec,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, gradient_inl, gradient_inr]
  simp only [model, J, B, of_apply, Jfun, Bfun, diagonal_apply, Sum.elim_inl,
    reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
    Sum.inl.injEq, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    sum_kvl, true_and, Fin.isValue, one_ne_zero, false_and]
  unfold leftVoltage
  split_ifs <;> simp_all <;> ring

/-- KCL of node `k`: `q̇_k = i_k - i_right - G'Δx v_k`. -/
@[powerlib_domain] theorem field_charge (x : Idx N → ℝ) (u : Fin 2 → ℝ) (k : Fin N) :
    PortHamiltonian.field (model p N) x u (.inr k) =
      current p N x k - rightCurrent p N x u k - p.G' * p.Δx * voltage p N x k := by
  simp only [PortHamiltonian.field, sub_mulVec, Pi.add_apply, Pi.sub_apply, mulVec,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, gradient_inl, gradient_inr]
  simp only [model, J, B, of_apply, Jfun, Bfun, diagonal_apply, Sum.elim_inr,
    reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
    Sum.inr.injEq, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    sum_kcl, true_and, Fin.isValue, zero_ne_one, false_and]
  unfold rightCurrent
  split_ifs <;> simp_all <;> ring

/-- Port supply: `v₁ i_0 - i₂ v_{N-1}`, the electrical power entering the ladder. -/
@[powerlib_domain] theorem supply_eq (n : ℕ) (x : Idx (n + 1) → ℝ) (u : Fin 2 → ℝ) :
    Passivity.supply (PortHamiltonian.system (model p (n + 1))) x u =
      u 0 * current p (n + 1) x 0 - u 1 * voltage p (n + 1) x (Fin.last n) := by
  simp only [Passivity.supply, PortHamiltonian.system, PortHamiltonian.output, mulVec,
    dotProduct, transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two, gradient_inl,
    gradient_inr]
  simp only [model, B, of_apply, Bfun, Fin.isValue, true_and, one_ne_zero, zero_ne_one,
    false_and, if_false, zero_mul, Finset.sum_const_zero, add_zero, zero_add, ite_mul,
    one_mul, neg_mul]
  have h0 : (∑ j : Fin (n + 1), if j.val = 0 then current p (n + 1) x j else 0) =
      current p (n + 1) x 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; exact if_neg fun h => hj (Fin.ext h)
    · simp
  have h1 : (∑ j : Fin (n + 1), if j.val + 1 = n + 1 then -voltage p (n + 1) x j else 0) =
      -voltage p (n + 1) x (Fin.last n) := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp
    · intro j _ hj; exact if_neg fun h => hj (Fin.ext (by simp; omega))
    · simp
  rw [h0, h1]
  ring

/-- The ladder is passive with its stored magnetic plus electric energy
`∑ φ_k²/(2L'Δx) + ∑ q_k²/(2C'Δx)`. -/
@[powerlib_domain] theorem passiveWithStorage :
    Passivity.PassiveWithStorage (PortHamiltonian.system (model p N))
      (PortHamiltonian.energy (model p N)) :=
  PortHamiltonian.passiveWithStorage (model p N)

/-- With both ports shorted/opened (`v₁ = 0`, `i₂ = 0`) the ladder is Lyapunov stable. -/
@[powerlib_domain] theorem lyapunovStable (n : ℕ) :
    Passivity.LyapunovStable (PortHamiltonian.system (model p (n + 1))) :=
  PortHamiltonian.lyapunovStable (model p (n + 1))

@[powerlib_foundation] theorem damping_pos (hR : 0 < p.R') (hG : 0 < p.G') (a : Idx N) :
    0 < (model p N).d a := by
  rcases a with _ | _
  · exact mul_pos hR p.Δx_pos
  · exact mul_pos hG p.Δx_pos

/-- With `R' > 0` and `G' > 0` the zero-input ladder (`v₁ = 0`, `i₂ = 0`) is globally
exponentially stable: every solution exists for all forward time and decays
exponentially, for every initial flux and charge distribution. -/
@[powerlib_domain] theorem lossyLadder_globallyExponentiallyStable
    (hR : 0 < p.R') (hG : 0 < p.G') :
    Dynamics.GloballyExponentiallyStable
      (fun x => PortHamiltonian.field (model p N) x 0) 0 :=
  PHStrict.globallyExponentiallyStable (model p N) (damping_pos p N hR hG)

/-- Correction of "the telegrapher line conserves energy": with losses, the stored
energy strictly decreases along every zero-input solution that is not identically 0. -/
@[powerlib_domain] theorem lossyLadder_energy_strictly_decreases
    (hR : 0 < p.R') (hG : 0 < p.G') {φ : ℝ → Idx N → ℝ} {a b t : ℝ}
    (hφ : Dynamics.IsTrajectoryOn φ (fun x => PortHamiltonian.field (model p N) x 0) a b)
    (ht : t ∈ Set.Ioc a b) (h0 : φ a ≠ 0) :
    PortHamiltonian.energy (model p N) (φ t) < PortHamiltonian.energy (model p N) (φ a) := by
  let c := PHStrict.certificate (model p N) (damping_pos p N hR hG)
  have hb := c.energy_bound hφ ⟨ht.1.le, ht.2⟩
  have hpos := PortHamiltonian.energy_positive (model p N) (φ a) h0
  have hexp : Real.exp (-(c.rate * (t - a))) < 1 := by
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    exact mul_pos c.rate_pos (sub_pos.mpr ht.1)
  calc PortHamiltonian.energy (model p N) (φ t)
      ≤ Real.exp (-(c.rate * (t - a))) * PortHamiltonian.energy (model p N) (φ a) := hb
    _ < 1 * PortHamiltonian.energy (model p N) (φ a) := mul_lt_mul_of_pos_right hexp hpos
    _ = _ := one_mul _

@[powerlib_foundation] theorem const_of_hasDerivWithinAt_Icc_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Set.Icc a b, HasDerivWithinAt f 0 (Set.Icc a b) t) :
    ∀ t ∈ Set.Icc a b, f t = f a := by
  apply constant_of_has_deriv_right_zero
  · exact fun t ht => (hf t ht).continuousWithinAt
  · intro t ht
    apply (hf t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Set.Icc_subset_Icc_left ht.1)

/-- In the lossless case `R' = G' = 0` the stored energy is constant along every
zero-input solution segment. -/
@[powerlib_domain] theorem losslessLadder_energy_conserved
    (hR : p.R' = 0) (hG : p.G' = 0) {φ : ℝ → Idx N → ℝ} {a b : ℝ}
    (hφ : Dynamics.IsTrajectoryOn φ (fun x => PortHamiltonian.field (model p N) x 0) a b) :
    ∀ t ∈ Set.Icc a b,
      PortHamiltonian.energy (model p N) (φ t) = PortHamiltonian.energy (model p N) (φ a) := by
  apply const_of_hasDerivWithinAt_Icc_zero
  intro t ht
  have hd := (PHStrict.energy_hasFDerivAt (model p N) (φ t)).comp_hasDerivWithinAt t (hφ t ht)
  have hzero : (∑ i, ((model p N).w i * φ t i) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Idx N => ℝ) i)
      (PortHamiltonian.field (model p N) (φ t) 0) = 0 := by
    have h1 := PHStrict.fderiv_energy_apply (model p N) (φ t)
      (PortHamiltonian.field (model p N) (φ t) 0)
    rw [(PHStrict.energy_hasFDerivAt (model p N) (φ t)).fderiv,
      PortHamiltonian.power_balance, Passivity.supply_zero] at h1
    rw [h1]
    have : PortHamiltonian.dampingPower (model p N) (φ t) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases i with _ | _ <;> simp [model, hR, hG]
    rw [this]; ring
  rw [hzero] at hd
  exact hd

end Ladder

end powerlib.Line
