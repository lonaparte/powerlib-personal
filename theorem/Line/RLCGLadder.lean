import theorem.PH.Composition

/-! # Staggered-grid RLCG ladder as a port-Hamiltonian model

The method-of-lines (staggered-grid) RLCG ladder of a transmission line as diagonal
port-Hamiltonian data: passivity, Lyapunov stability, exponential stability of the lossy ladder
and energy conservation only in the lossless case.

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

Source: work-sync `theory/T-method-of-lines.md` §1.3 (staggered grid,
`L' i̇_{j+1/2} = -(v_{j+1}-v_j)/Δx - R' i_{j+1/2}`,
`C' v̇_j = -(i_{j+1/2}-i_{j-1/2})/Δx - G' v_j`), and the passivity remark of
`theory/T-pde-systems.md` §2.7.

Results (static evidence on the model).
* `field_flux`, `field_charge` — the KVL/KCL rows of the ladder; `supply_eq` — the port supply
  `v₁ i_0 - v_{N-1} i₂`; `ladderPH_dissipation_pos` — the lossy ladder is strictly damped.

Family and connection conclusions.
* The ladder is diagonal port-Hamiltonian data
  (`Ladder.model : DiagonalPH (Fin N ⊕ Fin N) (Fin 2)`, `theorem/PH/Composition.lean`);
  numbering the state `(φ, q)` by `finSumFinEquiv` gives the linear port-Hamiltonian plant
  `Ladder.ladderPH p N : Port.PortHamiltonian (N + N) 2`, a member of the existing family
  `Port.PortHamiltonian.family` (system map: the plant's port system; sentences read at the
  origin, the unforced state with `v₁ = 0`, `i₂ = 0`).
* Connection conclusions: passivity and Lyapunov stability (`ladderPH_mem_den_passive`,
  `ladderPH_mem_den_lyapunovStable`); global exponential stability of the lossy ladder
  `R' > 0`, `G' > 0` (`lossyLadder_mem_den_globallyExponentiallyStable`, an instance of the
  general `PH.toPH_mem_den_globallyExponentiallyStable` for strictly damped diagonal models,
  `theorem/PH/Composition.lean`); the correction in sentence form — the lossy ladder with at least
  one cell conserves **no** positive definite energy (`lossyLadder_not_mem_den_conservative`) —
  and conservation in the lossless case (`losslessLadder_mem_den_conservative`).
* The KVL/KCL fields and the port supply are static evidence. The trajectory-level statements
  about the stored energy itself — strict decrease along nonzero lossy solutions and constancy
  along lossless solutions — are private implementation evidence
  (`lossyLadder_energy_strictly_decreases`, from the generic energy certificate
  `PH.exists_quadraticDecay`, and `losslessLadder_energy_conserved`).

Correction (T-pde-systems §2.7 "电报方程满足能量守恒").
* The lossy ladder does not conserve energy. Energy is conserved only in the lossless case
  `R' = G' = 0`.
-/

noncomputable section
namespace powerlib.Line
open Matrix Set PH

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

@[tmio M, powerlib_foundation] theorem J_skew : (J N).transpose = -(J N) := by
  ext a b
  rcases a with k | k <;> rcases b with j | j <;>
    simp only [transpose_apply, J, of_apply, Jfun, Matrix.neg_apply, neg_zero]
  · split_ifs <;> (try subst_vars) <;> simp_all
  · split_ifs <;> (try subst_vars) <;> simp_all

/-- The staggered RLCG ladder as diagonal port-Hamiltonian data. -/
def model : DiagonalPH (Idx N) (Fin 2) where
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
  · exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)
  · rw [Finset.sum_eq_single ⟨k.val - 1, by omega⟩]
    · exact ite_eq_left (by simp only; omega)
    · intro j _ hj
      exact ite_eq_right fun h' => hj (Fin.ext (by simp only; omega))
    · exact fun h' => absurd (Finset.mem_univ _) h'

omit p in
@[powerlib_foundation] theorem sum_next (k : Fin N) (g : Fin N → ℝ) :
    ∑ j : Fin N, (if j.val = k.val + 1 then g j else 0) =
      if h : k.val + 1 = N then 0 else g ⟨k.val + 1, by omega⟩ := by
  split_ifs with h
  · exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)
  · rw [Finset.sum_eq_single ⟨k.val + 1, by omega⟩]
    · exact ite_eq_left rfl
    · intro j _ hj
      exact ite_eq_right fun h' => hj (Fin.ext h')
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
    (model p N).gradient x (.inl k) = current p N x k := by
  simp [DiagonalPH.gradient, model, current]; ring

@[powerlib_foundation] theorem gradient_inr (x : Idx N → ℝ) (k : Fin N) :
    (model p N).gradient x (.inr k) = voltage p N x k := by
  simp [DiagonalPH.gradient, model, voltage]; ring

/-- KVL of cell `k`: `φ̇_k = v_left - v_k - R'Δx i_k`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_flux (x : Idx N → ℝ) (u : Fin 2 → ℝ) (k : Fin N) :
    (model p N).field x u (.inl k) =
      leftVoltage p N x u k - voltage p N x k - p.R' * p.Δx * current p N x k := by
  simp only [DiagonalPH.field, sub_mulVec, Pi.add_apply, Pi.sub_apply, mulVec,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, gradient_inl, gradient_inr]
  simp only [model, J, B, of_apply, Jfun, Bfun, diagonal_apply, Sum.elim_inl,
    reduceCtorEq, ite_false, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
    Sum.inl.injEq, sum_kvl, true_and, Fin.isValue, one_ne_zero, false_and]
  unfold leftVoltage
  split_ifs <;> simp_all <;> ring

/-- KCL of node `k`: `q̇_k = i_k - i_right - G'Δx v_k`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_charge (x : Idx N → ℝ) (u : Fin 2 → ℝ) (k : Fin N) :
    (model p N).field x u (.inr k) =
      current p N x k - rightCurrent p N x u k - p.G' * p.Δx * voltage p N x k := by
  simp only [DiagonalPH.field, sub_mulVec, Pi.add_apply, Pi.sub_apply, mulVec,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, gradient_inl, gradient_inr]
  simp only [model, J, B, of_apply, Jfun, Bfun, diagonal_apply, Sum.elim_inr,
    reduceCtorEq, ite_false, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
    Sum.inr.injEq, sum_kcl, true_and, Fin.isValue, zero_ne_one, false_and]
  unfold rightCurrent
  split_ifs <;> simp_all
  ring

/-- Port supply: `v₁ i_0 - i₂ v_{N-1}`, the electrical power entering the ladder.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem supply_eq (n : ℕ) (x : Idx (n + 1) → ℝ) (u : Fin 2 → ℝ) :
    (model p (n + 1)).supply x u =
      u 0 * current p (n + 1) x 0 - u 1 * voltage p (n + 1) x (Fin.last n) := by
  simp only [DiagonalPH.supply, DiagonalPH.output, mulVec,
    dotProduct, transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two, gradient_inl,
    gradient_inr]
  simp only [model, B, of_apply, Bfun, Fin.isValue, true_and, one_ne_zero, zero_ne_one,
    false_and, ite_false, zero_mul, Finset.sum_const_zero, add_zero, zero_add, ite_mul,
    one_mul, neg_mul]
  have h0 : (∑ j : Fin (n + 1), if j.val = 0 then current p (n + 1) x j else 0) =
      current p (n + 1) x 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; exact ite_eq_right fun h => hj (Fin.ext h)
    · simp
  have h1 : (∑ j : Fin (n + 1), if j.val + 1 = n + 1 then -voltage p (n + 1) x j else 0) =
      -voltage p (n + 1) x (Fin.last n) := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp
    · intro j _ hj; exact ite_eq_right fun h => hj (Fin.ext (by simp; omega))
    · simp
  rw [h0, h1]
  ring

/-! ### The ladder as a linear port-Hamiltonian plant -/

/-- The ladder with the state `(φ, q)` numbered by `finSumFinEquiv`. -/
def ladderPH : Port.PortHamiltonian (N + N) 2 :=
  (model p N).toPH finSumFinEquiv (Equiv.refl _)

/-- The ladder is passive; the storage is the magnetic plus electric energy
`∑ φ_k²/(2L'Δx) + ∑ q_k²/(2C'Δx)` (`toPH_storage`). -/
@[tmio TM, powerlib_domain] theorem ladderPH_mem_den_passive :
    connection% (ladderPH p N ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- With both ports shorted/opened (`v₁ = 0`, `i₂ = 0`) the ladder is Lyapunov stable. -/
@[tmio TM, powerlib_domain] theorem ladderPH_mem_den_lyapunovStable :
    connection% (ladderPH p N ∈ Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

@[powerlib_foundation] theorem damping_pos (hR : 0 < p.R') (hG : 0 < p.G') (a : Idx N) :
    0 < (model p N).d a := by
  rcases a with _ | _
  · exact mul_pos hR p.Δx_pos
  · exact mul_pos hG p.Δx_pos

@[powerlib_foundation] theorem ladderPH_dissipation_pos (hR : 0 < p.R') (hG : 0 < p.G') :
    ∀ x : Fin (N + N) → ℝ, x ≠ 0 → 0 < x ⬝ᵥ ((ladderPH p N).R *ᵥ x) :=
  (model p N).toPH_dissipation_pos _ _ (damping_pos p N hR hG)

/-- With `R' > 0` and `G' > 0` the zero-input ladder (`v₁ = 0`, `i₂ = 0`) is globally
exponentially stable: every solution exists for all forward time and decays
exponentially, for every initial flux and charge distribution. -/
@[tmio TM, powerlib_domain] theorem lossyLadder_mem_den_globallyExponentiallyStable
    (hR : 0 < p.R') (hG : 0 < p.G') :
    connection% (ladderPH p N ∈
      Port.PortHamiltonian.family.den (.flow .globallyExponentiallyStable)) :=
  mem_den_globallyExponentiallyStable_of_dissipation_pos _ (ladderPH_dissipation_pos p N hR hG)

/-- Correction of "the telegrapher line conserves energy": a lossy ladder with at least one cell
conserves no positive definite energy. -/
@[tmio TM, powerlib_domain] theorem lossyLadder_not_mem_den_conservative (hR : 0 < p.R') (hG : 0 < p.G')
    (hN : 0 < N) :
    connection% (ladderPH p N ∉ Port.PortHamiltonian.family.den (.flow .conservative)) :=
  not_mem_den_conservative_of_dissipation_pos _ (by omega) (ladderPH_dissipation_pos p N hR hG)

/-- In the lossless case `R' = G' = 0` the zero-input ladder conserves its stored energy. -/
@[tmio TM, powerlib_domain] theorem losslessLadder_mem_den_conservative (hR : p.R' = 0) (hG : p.G' = 0) :
    connection% (ladderPH p N ∈ Port.PortHamiltonian.family.den (.flow .conservative)) := by
  refine mem_den_conservative_of_lossless _ (DiagonalPH.toPH_R_eq_zero _ _ _ ?_)
  ext a
  rcases a with _ | _ <;> simp [model, hR, hG]

/-! ### The stored energy along solutions (implementation evidence) -/

/-- With losses, the stored energy strictly decreases along every zero-input solution segment
that does not start at 0.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem lossyLadder_energy_strictly_decreases
    (hR : 0 < p.R') (hG : 0 < p.G') {φ : ℝ → EuclideanSpace ℝ (Fin (N + N))} {a b t : ℝ}
    (hφ : IsTrajectoryOn φ (ladderPH p N).plant.system.zeroInput a b)
    (ht : t ∈ Set.Ioc a b) (h0 : φ a ≠ 0) :
    (model p N).energy (WithLp.ofLp (φ t) ∘ finSumFinEquiv) <
      (model p N).energy (WithLp.ofLp (φ a) ∘ finSumFinEquiv) := by
  obtain ⟨c⟩ := exists_quadraticDecay (ladderPH p N) (ladderPH_dissipation_pos p N hR hG)
  have hb := c.energy_bound hφ ⟨ht.1.le, ht.2⟩
  have hpos : 0 < (ladderPH p N).kyp.storage (φ a) :=
    div_pos ((ladderPH p N).energy_pos _ (by simpa using h0)) two_pos
  have hexp : Real.exp (-(c.rate * (t - a))) < 1 := by
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    exact mul_pos c.rate_pos (sub_pos.mpr ht.1)
  simp only [ladderPH, DiagonalPH.toPH_storage] at hb hpos
  calc (model p N).energy (WithLp.ofLp (φ t) ∘ finSumFinEquiv)
      ≤ Real.exp (-(c.rate * (t - a))) *
          (model p N).energy (WithLp.ofLp (φ a) ∘ finSumFinEquiv) := hb
    _ < 1 * (model p N).energy (WithLp.ofLp (φ a) ∘ finSumFinEquiv) :=
        mul_lt_mul_of_pos_right hexp hpos
    _ = _ := one_mul _

/-- In the lossless case `R' = G' = 0` the stored energy is constant along every zero-input
solution segment.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem losslessLadder_energy_conserved
    (hR : p.R' = 0) (hG : p.G' = 0) {φ : ℝ → EuclideanSpace ℝ (Fin (N + N))} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (ladderPH p N).plant.system.zeroInput a b) :
    ∀ t ∈ Set.Icc a b, (model p N).energy (WithLp.ofLp (φ t) ∘ finSumFinEquiv) =
      (model p N).energy (WithLp.ofLp (φ a) ∘ finSumFinEquiv) := by
  intro t ht
  have hR0 : (ladderPH p N).R = 0 := by
    refine DiagonalPH.toPH_R_eq_zero _ _ _ ?_
    ext a
    rcases a with _ | _ <;> simp [model, hR, hG]
  rw [Linear.Plant.system_zeroInput] at hφ
  have h := (ladderPH p N).kyp.storage_conserved (lossless_lyapunov _ hR0) hφ t ht
  simpa only [ladderPH, DiagonalPH.toPH_storage] using h

end Ladder

end powerlib.Line
