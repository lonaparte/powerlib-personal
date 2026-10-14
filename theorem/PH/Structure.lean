import theorem.PH.Linear
import theorem.Flow.Certificate
import theorem.TMIO.ClaimElab

/-! # Structural results for port-Hamiltonian systems (foundation layer)

All statements are about the abstract objects below; none of them is an engineering claim
about a specific power system.

* Dirac structures (T-ph §1.3): flow and effort spaces are both `ι → ℝ` (`ι` finite),
  pairing `⟪(f₁,e₁),(f₂,e₂)⟫ = f₁·e₂ + f₂·e₁`. A Dirac structure is a set `D` with
  `D^⊥ = D`. Results: power conservation `eᵀ f = 0` on `D` (1.6); the graph of a skew `J`
  is a Dirac structure (the explicit form (1.1) is a special case); with storage, resistive
  and control ports, `D` plus the constitutive relations (1.7) gives the energy balance (1.2).
* pH-DAE (§1.4): a Lagrange-multiplier term `G(x) λ` with `G(x)ᵀ ∇H(x) = 0` does no work.
* Strict output passivity (§1.2): uniformly positive definite `R(x)` plus a uniformly bounded
  `g(x)` give `Ḣ ≤ uᵀ y − ε |y|²`.
  Correction: the note states "R ≻ 0 ⇒ strictly output passive". A uniform lower bound
  `R(x) ⪰ ρ I` (ρ > 0) and a uniform bound `|g(x)ᵀ w|² ≤ γ |w|²` are needed for a uniform `ε`.
* IDA-PBC (§1.9): the matching equation (1.13) makes the closed loop the target pH system,
  whose Hamiltonian `H_d` is nonincreasing; a strict local minimum of `H_d` is Lyapunov stable.
  The control law (1.14) solves (1.13) exactly when the bracket lies in `range g(x)` and
  `g(x)ᵀ g(x)` is invertible; outside `range g(x)` no input solves (1.13).
* Zero-input stability (§1.2 corollary).
  Correction: the corollary "argmin H = {x*} and R ≻ 0 on {∇H ≠ 0} ⇒ (LaSalle) GAS" is false.
  Counterexample (`phLaSalle_counterexample_*`): the gradient system `J = 0, R = I` on `ℝ²` with
  the tilted double well `H = x₀⁴/4 + x₀³/3 − x₀² + x₁²/2` has the unique global minimizer
  `(−2, 0)` and `R ≻ 0` everywhere, but the second critical point `(1, 0)` is an equilibrium,
  so `(−2, 0)` is not globally attractive. Corrected version (`phGAS_of_unique_critical`):
  add "∇H = 0 only at x*" and "H radially unbounded" (plus `C¹` regularity); then
  `H − H(x*)` is a strict radially unbounded Lyapunov function and GAS follows without LaSalle.
* Discrete gradient method (§2.5): `theorem/Numerics/DiscreteGradient.lean`
  (`Numerics.DiscreteGradient`, `Numerics.discreteGradient_energy_step`).

Family and connection conclusions. The structural results are generic (Dirac structures and
implications for every `NonlinearModel`, the generic framework of
`theorem/PH/Nonlinear.lean`, which no family takes as model type); they remain public foundation,
including the generic IDA-PBC stability theorems and the corrected GAS criterion
`phGAS_of_unique_critical` (now concluding `Flow.GloballyAsymptoticallyStable`, which includes
forward completeness, through LeanForControl's `asymptotic_implies_strict` and
`Flow.globallyAsymptoticallyStable_of_strictLyapunov`). The single concrete model, the tilted
double-well counterexample, gets a family `LaSalle.family`: a complete system is the
counterexample read about a selected point (`LaSalle.Model`; system map: the pH system centred
there, `NonlinearModel.shift`); its requirement language has the note's hypothesis "the point is
the unique global minimizer of `H`" (static); Lyapunov stability translates into it, passivity
into nothing (exact: `H` is bounded below), all other sentences into the whole inconsistent
language. Connection conclusions: `LaSalle.chain_le_semantics`, `LaSalle.exact_passive`,
`LaSalle.mem_den_lyapunovStable` (the minimizer is Lyapunov stable) and the refutation in
connection form — the minimizer is not globally asymptotically stable
(`LaSalle.not_mem_den_globallyAsymptoticallyStable`, formerly the raw
`phLaSalle_counterexample_not_GAS`), so the unique-minimizer requirement does not translate
global asymptotic stability soundly (`LaSalle.uniqueMin_not_sound_globallyAsymptoticallyStable`).

Source: work-sync `theory/T-ph.md` §1.2, §1.3 (1.5)–(1.7), §1.4 (1.8), §1.9 (1.13)–(1.14),
§2.5.
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter MeasureTheory
open scoped Topology
open powerlib.Dynamics (State)

/-! ## Dirac structures -/

section Dirac

variable {ι : Type*} [Fintype ι]

/-- The symmetric power pairing `⟪(f₁, e₁), (f₂, e₂)⟫ = f₁ · e₂ + f₂ · e₁`. -/
def diracPairing (a b : (ι → ℝ) × (ι → ℝ)) : ℝ := a.1 ⬝ᵥ b.2 + b.1 ⬝ᵥ a.2

/-- Orthogonal complement with respect to `diracPairing`. -/
def diracOrth (D : Set ((ι → ℝ) × (ι → ℝ))) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {a | ∀ b ∈ D, diracPairing a b = 0}

/-- A Dirac structure: `D^⊥ = D` (T-ph (1.5)). -/
def IsDiracStructure (D : Set ((ι → ℝ) × (ι → ℝ))) : Prop := diracOrth D = D

/-- Power conservation (T-ph (1.6)): `eᵀ f = 0` for every `(f, e)` in a Dirac structure. -/
@[powerlib_foundation] theorem dirac_power_conserving {D : Set ((ι → ℝ) × (ι → ℝ))}
    (hD : IsDiracStructure D) {a : (ι → ℝ) × (ι → ℝ)} (ha : a ∈ D) : a.2 ⬝ᵥ a.1 = 0 := by
  have h : a ∈ diracOrth D := by rw [hD]; exact ha
  have h2 := h a ha
  simp only [diracPairing] at h2
  rw [dotProduct_comm] at h2
  linarith

/-- The graph `{(f, e) | f = J e}` of a skew-symmetric `J` is a Dirac structure. -/
@[powerlib_foundation] theorem dirac_graph_skew [DecidableEq ι] {J : Matrix ι ι ℝ}
    (hJ : Jᵀ = -J) : IsDiracStructure {a : (ι → ℝ) × (ι → ℝ) | a.1 = J *ᵥ a.2} := by
  have hskew : ∀ v w : ι → ℝ, (J *ᵥ w) ⬝ᵥ v = -(w ⬝ᵥ (J *ᵥ v)) := by
    intro v w
    have h : w ⬝ᵥ (Jᵀ *ᵥ v) = (J *ᵥ w) ⬝ᵥ v := by
      rw [mulVec_transpose, dotProduct_comm (J *ᵥ w) v, dotProduct_mulVec, dotProduct_comm]
    rw [← h, hJ, neg_mulVec, dotProduct_neg]
  ext a
  constructor
  · intro ha
    have h := ha (J *ᵥ (a.1 - J *ᵥ a.2), a.1 - J *ᵥ a.2) rfl
    simp only [diracPairing] at h
    rw [hskew, ← sub_eq_add_neg, dotProduct_comm a.1, ← dotProduct_sub] at h
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h)
  · intro ha b hb
    change a.1 = J *ᵥ a.2 at ha
    change b.1 = J *ᵥ b.2 at hb
    simp only [diracPairing, ha, hb]
    rw [hskew b.2 a.2, dotProduct_comm (J *ᵥ b.2) a.2]
    ring

variable {σ ρ κ : Type*} [Fintype σ] [Fintype ρ] [Fintype κ]

/-- Energy balance from a Dirac structure (T-ph (1.6)–(1.7)): the port set is split into
storage `σ`, resistive `ρ` and control `κ` ports. If `(f, e) ∈ D` with `f_S = −ẋ`,
`e_S = ∇H`, `f_R = −Φ(e_R)` and `(u, y) = (e_C, f_C)`, then `∇H · ẋ = uᵀ y − e_Rᵀ Φ(e_R)`. -/
@[powerlib_foundation] theorem dirac_energy_balance
    {D : Set (((σ ⊕ ρ ⊕ κ) → ℝ) × ((σ ⊕ ρ ⊕ κ) → ℝ))} (hD : IsDiracStructure D)
    {a : ((σ ⊕ ρ ⊕ κ) → ℝ) × ((σ ⊕ ρ ⊕ κ) → ℝ)} (ha : a ∈ D)
    (xdot gradH : σ → ℝ) (Φ : (ρ → ℝ) → (ρ → ℝ)) (u y : κ → ℝ)
    (hfS : ∀ i, a.1 (Sum.inl i) = -xdot i) (heS : ∀ i, a.2 (Sum.inl i) = gradH i)
    (hfR : (fun r => a.1 (Sum.inr (Sum.inl r))) = -Φ (fun r => a.2 (Sum.inr (Sum.inl r))))
    (heC : ∀ k, a.2 (Sum.inr (Sum.inr k)) = u k) (hfC : ∀ k, a.1 (Sum.inr (Sum.inr k)) = y k) :
    gradH ⬝ᵥ xdot = u ⬝ᵥ y -
      (fun r => a.2 (Sum.inr (Sum.inl r))) ⬝ᵥ Φ (fun r => a.2 (Sum.inr (Sum.inl r))) := by
  have h := dirac_power_conserving hD ha
  have hR := congrFun hfR
  simp only [dotProduct, Fintype.sum_sum_type] at h ⊢
  simp only [hfS, heS, heC, hfC] at h
  simp only [Pi.neg_apply] at hR
  simp only [hR] at h
  have e1 : ∑ i, gradH i * -xdot i = -∑ i, gradH i * xdot i := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ r, a.2 (Sum.inr (Sum.inl r)) * -Φ (fun r => a.2 (Sum.inr (Sum.inl r))) r =
      -∑ r, a.2 (Sum.inr (Sum.inl r)) * Φ (fun r => a.2 (Sum.inr (Sum.inl r))) r := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2] at h
  linarith

/-- With a passive resistive relation `e_Rᵀ Φ(e_R) ≥ 0`: `∇H · ẋ ≤ uᵀ y`. -/
@[powerlib_foundation] theorem dirac_dissipation_inequality
    {D : Set (((σ ⊕ ρ ⊕ κ) → ℝ) × ((σ ⊕ ρ ⊕ κ) → ℝ))} (hD : IsDiracStructure D)
    {a : ((σ ⊕ ρ ⊕ κ) → ℝ) × ((σ ⊕ ρ ⊕ κ) → ℝ)} (ha : a ∈ D)
    (xdot gradH : σ → ℝ) (Φ : (ρ → ℝ) → (ρ → ℝ)) (u y : κ → ℝ)
    (hfS : ∀ i, a.1 (Sum.inl i) = -xdot i) (heS : ∀ i, a.2 (Sum.inl i) = gradH i)
    (hfR : (fun r => a.1 (Sum.inr (Sum.inl r))) = -Φ (fun r => a.2 (Sum.inr (Sum.inl r))))
    (heC : ∀ k, a.2 (Sum.inr (Sum.inr k)) = u k) (hfC : ∀ k, a.1 (Sum.inr (Sum.inr k)) = y k)
    (hΦ : ∀ e, 0 ≤ e ⬝ᵥ Φ e) :
    gradH ⬝ᵥ xdot ≤ u ⬝ᵥ y := by
  rw [dirac_energy_balance hD ha xdot gradH Φ u y hfS heS hfR heC hfC]
  linarith [hΦ (fun r => a.2 (Sum.inr (Sum.inl r)))]

end Dirac

/-! ## pH-DAE: constraint forces do no work -/

variable {n m k : ℕ}

/-- The field of the pH-DAE (1.8): `(J − R)∇H + g u + G λ`. -/
def phDAE_field (M : NonlinearModel n m) (G : State n → Matrix (Fin n) (Fin k) ℝ)
    (x : State n) (u : Fin m → ℝ) (lam : Fin k → ℝ) : State n :=
  M.field x u + WithLp.toLp 2 (G x *ᵥ lam)

/-- T-ph §1.4: on the constraint manifold `G(x)ᵀ ∇H(x) = 0` the multiplier term does no work,
so the energy balance (1.2) is unchanged. -/
@[powerlib_foundation] theorem phDAE_power_balance (M : NonlinearModel n m)
    (G : State n → Matrix (Fin n) (Fin k) ℝ) (x : State n) (u : Fin m → ℝ) (lam : Fin k → ℝ)
    (hc : (G x)ᵀ *ᵥ WithLp.ofLp (M.dH x) = 0) :
    fderiv ℝ M.H x (phDAE_field M G x u lam) = M.supply x u - M.dampingPower x := by
  rw [phDAE_field, map_add, M.power_balance, M.fderiv_H_apply, WithLp.ofLp_toLp,
    dotProduct_mulVec, ← mulVec_transpose, hc, zero_dotProduct, add_zero]

/-! ## Strict output passivity -/

/-- Uniformly positive definite dissipation and uniformly bounded input matrix give strict
output passivity: `Ḣ ≤ uᵀ y − ε |y|²` with `ε = ρ / (γ + 1)`. -/
@[powerlib_foundation] theorem strictOutputPassive_of_uniform (M : NonlinearModel n m)
    {ρ γ : ℝ} (hρ : 0 < ρ) (hγ : 0 ≤ γ)
    (hR : ∀ x (w : Fin n → ℝ), ρ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (M.R x *ᵥ w))
    (hg : ∀ x (w : Fin n → ℝ), ((M.g x)ᵀ *ᵥ w) ⬝ᵥ ((M.g x)ᵀ *ᵥ w) ≤ γ * (w ⬝ᵥ w)) :
    ∃ ε > 0, ∀ x u, fderiv ℝ M.H x (M.field x u) ≤
      M.supply x u - ε * (M.output x ⬝ᵥ M.output x) := by
  refine ⟨ρ / (γ + 1), div_pos hρ (by linarith), fun x u => ?_⟩
  rw [M.power_balance]
  set w := WithLp.ofLp (M.dH x)
  have h1 := hR x w
  have h2 := hg x w
  have hw : 0 ≤ w ⬝ᵥ w := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hy : M.output x = (M.g x)ᵀ *ᵥ w := rfl
  have hdamp : M.dampingPower x = w ⬝ᵥ (M.R x *ᵥ w) := rfl
  rw [hy, hdamp]
  have hγ1 : 0 < γ + 1 := by linarith
  have key : ρ / (γ + 1) * (((M.g x)ᵀ *ᵥ w) ⬝ᵥ ((M.g x)ᵀ *ᵥ w)) ≤ ρ * (w ⬝ᵥ w) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hγ1]
    nlinarith
  linarith

/-! ## IDA-PBC -/

/-- If the feedback `β` satisfies the matching equation (1.13) at every state, the closed loop
`ẋ = F(x, β(x))` is the target pH system `ẋ = (J_d − R_d)∇H_d`. -/
@[powerlib_foundation] theorem idaPbc_closedLoop (M Md : NonlinearModel n m)
    (β : State n → Fin m → ℝ)
    (hmatch : ∀ x, (M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x) + M.g x *ᵥ β x =
      (Md.J x - Md.R x) *ᵥ WithLp.ofLp (Md.dH x)) :
    (fun x => M.field x (β x)) = Md.zeroInputField := by
  funext x
  apply WithLp.ofLp_injective 2
  rw [NonlinearModel.ofLp_field, hmatch, NonlinearModel.zeroInputField, NonlinearModel.ofLp_field,
    mulVec_zero, add_zero]

/-- Under matching, the target Hamiltonian is nonincreasing along the closed loop. -/
@[powerlib_foundation] theorem idaPbc_lie_nonpos (M Md : NonlinearModel n m)
    (β : State n → Fin m → ℝ)
    (hmatch : ∀ x, (M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x) + M.g x *ᵥ β x =
      (Md.J x - Md.R x) *ᵥ WithLp.ofLp (Md.dH x)) (x : State n) :
    fderiv ℝ Md.H x (M.field x (β x)) ≤ 0 := by
  rw [show M.field x (β x) = Md.zeroInputField x from congrFun (idaPbc_closedLoop M Md β hmatch) x]
  exact Md.zeroInput_lie_nonpos x

/-- IDA-PBC (T-ph §1.9): matching plus a strict local minimum of `H_d` at `x*` gives Lyapunov
stability of `x*` for the closed loop; `H_d − H_d(x*)` is the Lyapunov function. -/
@[powerlib_foundation] theorem idaPbc_lyapunovStable (M Md : NonlinearModel n m)
    (β : State n → Fin m → ℝ)
    (hmatch : ∀ x, (M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x) + M.g x *ᵥ β x =
      (Md.J x - Md.R x) *ᵥ WithLp.ofLp (Md.dH x))
    {xs : State n} (hmin : Md.IsStrictLocalMin xs) :
    LyapunovStable (fun x => M.field x (β x)) xs := by
  rw [idaPbc_closedLoop M Md β hmatch]
  exact hmin.lyapunovStable

/-- The bracket of the matching equation: `(J_d − R_d)∇H_d − (J − R)∇H`. -/
def idaPbc_bracket (M Md : NonlinearModel n m) (x : State n) : Fin n → ℝ :=
  (Md.J x - Md.R x) *ᵥ WithLp.ofLp (Md.dH x) - (M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x)

/-- The control law (1.14): `u = (gᵀ g)⁻¹ gᵀ [(J_d − R_d)∇H_d − (J − R)∇H]`. -/
def idaPbc_law (M Md : NonlinearModel n m) (x : State n) : Fin m → ℝ :=
  ((M.g x)ᵀ * M.g x)⁻¹ *ᵥ ((M.g x)ᵀ *ᵥ idaPbc_bracket M Md x)

/-- When the bracket lies in `range g(x)` and `g(x)ᵀ g(x)` is invertible, the law (1.14) solves
the matching equation (1.13) at `x`. -/
@[powerlib_foundation] theorem idaPbc_law_matches (M Md : NonlinearModel n m) (x : State n)
    (hinv : IsUnit ((M.g x)ᵀ * M.g x).det) {w : Fin m → ℝ}
    (hw : idaPbc_bracket M Md x = M.g x *ᵥ w) :
    (M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x) + M.g x *ᵥ idaPbc_law M Md x =
      (Md.J x - Md.R x) *ᵥ WithLp.ofLp (Md.dH x) := by
  have hlaw : idaPbc_law M Md x = w := by
    rw [idaPbc_law, hw, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hinv,
      one_mulVec]
  rw [hlaw, ← hw, idaPbc_bracket]
  abel

/-- Outside `range g(x)` no input solves the matching equation at `x`. -/
@[powerlib_foundation] theorem idaPbc_no_matching (M Md : NonlinearModel n m) (x : State n)
    (hnot : ∀ w, idaPbc_bracket M Md x ≠ M.g x *ᵥ w) (u : Fin m → ℝ) :
    (M.J x - M.R x) *ᵥ WithLp.ofLp (M.dH x) + M.g x *ᵥ u ≠
      (Md.J x - Md.R x) *ᵥ WithLp.ofLp (Md.dH x) := by
  intro h
  apply hnot u
  rw [idaPbc_bracket, ← h]
  abel

/-- IDA-PBC with the law (1.14): if the matching bracket lies in `range g(x)` and `gᵀ g` is
invertible at every state, the closed loop under (1.14) is the target system and a strict
local minimum of `H_d` is Lyapunov stable. -/
@[powerlib_foundation] theorem idaPbc_law_lyapunovStable (M Md : NonlinearModel n m)
    (hinv : ∀ x, IsUnit ((M.g x)ᵀ * M.g x).det)
    (hrange : ∀ x, ∃ w, idaPbc_bracket M Md x = M.g x *ᵥ w)
    {xs : State n} (hmin : Md.IsStrictLocalMin xs) :
    LyapunovStable (fun x => M.field x (idaPbc_law M Md x)) xs :=
  idaPbc_lyapunovStable M Md (idaPbc_law M Md)
    (fun x => (hrange x).elim fun _ hw => idaPbc_law_matches M Md x (hinv x) hw) hmin

/-! ## Zero-input global asymptotic stability: counterexample and corrected statement -/

/-- Tilted double well `H(x) = x₀⁴/4 + x₀³/3 − x₀² + x₁²/2`. -/
def phLaSalle_H (x : State 2) : ℝ :=
  1 / 4 * x 0 ^ 4 + 1 / 3 * x 0 ^ 3 - x 0 ^ 2 + 1 / 2 * x 1 ^ 2

/-- Its gradient `(x₀³ + x₀² − 2 x₀, x₁) = (x₀ (x₀ − 1)(x₀ + 2), x₁)`. -/
def phLaSalle_dH (x : State 2) : State 2 :=
  WithLp.toLp 2 ![x 0 ^ 3 + x 0 ^ 2 - 2 * x 0, x 1]

@[powerlib_foundation] theorem phLaSalle_hasGradientAt (x : State 2) :
    HasGradientAt phLaSalle_H (phLaSalle_dH x) x := by
  let P : Fin 2 → State 2 →L[ℝ] ℝ := fun i => PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
  have h := (((((P 0).hasFDerivAt (x := x)).pow 4).const_mul (1 / 4)).add
    ((((P 0).hasFDerivAt (x := x)).pow 3).const_mul (1 / 3))).sub
    (((P 0).hasFDerivAt (x := x)).pow 2) |>.add ((((P 1).hasFDerivAt (x := x)).pow 2).const_mul (1 / 2))
  refine hasGradientAt_of_hasFDerivAt h (fun v => ?_)
  simp [phLaSalle_dH, P, dotProduct, Fin.sum_univ_two]
  ring

/-- The counterexample model: `J = 0`, `R = I`, no inputs, `H` the tilted double well. -/
def phLaSalle_counterexample : NonlinearModel 2 0 where
  J _ := 0
  R _ := 1
  g _ := 0
  H := phLaSalle_H
  dH := phLaSalle_dH
  skew _ := by simp
  dissipation_posSemidef _ := PosSemidef.one
  hasGradient := phLaSalle_hasGradientAt

/-- The unique global minimizer `x* = (−2, 0)`. -/
def phLaSalle_xs : State 2 := WithLp.toLp 2 ![-2, 0]

/-- The second critical point `(1, 0)`. -/
def phLaSalle_xo : State 2 := WithLp.toLp 2 ![1, 0]

/-- Hypothesis "argmin H = {x*}" of the note holds: `H(x) > H(x*)` for `x ≠ x*`. -/
@[powerlib_foundation] theorem phLaSalle_counterexample_unique_min (x : State 2)
    (hx : x ≠ phLaSalle_xs) :
    phLaSalle_counterexample.H phLaSalle_xs < phLaSalle_counterexample.H x := by
  simp only [phLaSalle_counterexample, phLaSalle_H, phLaSalle_xs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hfac : 1 / 4 * x 0 ^ 4 + 1 / 3 * x 0 ^ 3 - x 0 ^ 2 + 8 / 3 =
      (x 0 + 2) ^ 2 * (3 * x 0 ^ 2 - 8 * x 0 + 8) / 12 := by ring
  have hq : 0 < 3 * x 0 ^ 2 - 8 * x 0 + 8 := by nlinarith [sq_nonneg (3 * x 0 - 4)]
  by_cases h0 : x 0 = -2
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      ext i
      fin_cases i <;> simp [phLaSalle_xs, h0, h1]
    have : 0 < x 1 ^ 2 := by positivity
    nlinarith
  · have : 0 < (x 0 + 2) ^ 2 := by
      have : x 0 + 2 ≠ 0 := fun h => h0 (by linarith)
      positivity
    have : 0 < (x 0 + 2) ^ 2 * (3 * x 0 ^ 2 - 8 * x 0 + 8) := mul_pos this hq
    nlinarith [sq_nonneg (x 1)]

/-- Hypothesis "R ≻ 0" of the note holds everywhere: the damping power is `|∇H|²`. -/
@[powerlib_foundation] theorem phLaSalle_counterexample_damping_pos (x : State 2)
    (hx : phLaSalle_counterexample.dH x ≠ 0) : 0 < phLaSalle_counterexample.dampingPower x := by
  have hne : WithLp.ofLp (phLaSalle_counterexample.dH x) ≠ 0 := fun h =>
    hx (WithLp.ofLp_injective 2 (by rw [h, WithLp.ofLp_zero]))
  have hR : phLaSalle_counterexample.R x = 1 := rfl
  rw [NonlinearModel.dampingPower, hR, one_mulVec]
  have h0 : 0 ≤ WithLp.ofLp (phLaSalle_counterexample.dH x) ⬝ᵥ
      WithLp.ofLp (phLaSalle_counterexample.dH x) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  exact lt_of_le_of_ne h0 (fun h => hne (dotProduct_self_eq_zero.mp h.symm))

/-- `(1, 0) ≠ x*` is an equilibrium of the unforced counterexample. -/
@[powerlib_foundation] theorem phLaSalle_counterexample_equilibrium :
    phLaSalle_counterexample.zeroInputField phLaSalle_xo = 0 := by
  apply phLaSalle_counterexample.zeroInputField_eq_zero_of_dH_eq_zero
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> norm_num [phLaSalle_counterexample, phLaSalle_dH, phLaSalle_xo]

/-- The tilted double well is bounded below by its minimum `H(x*) = −8/3`. -/
@[powerlib_foundation] theorem phLaSalle_H_lowerBound (x : State 2) : -(8 / 3) ≤ phLaSalle_H x := by
  have h := phLaSalle_counterexample_unique_min x
  by_cases hx : x = phLaSalle_xs
  · subst hx
    norm_num [phLaSalle_H, phLaSalle_xs]
  · have := (h hx).le
    have hxs : phLaSalle_counterexample.H phLaSalle_xs = -(8 / 3) := by
      norm_num [phLaSalle_counterexample, phLaSalle_H, phLaSalle_xs]
    rw [hxs] at this
    exact this

/-! ### The counterexample family -/

namespace LaSalle

/-- The counterexample read about a selected point. -/
structure Model where
  /-- The selected point. -/
  point : State 2

/-- Requirements on a selected point, all static. -/
inductive Requirement
  /-- The note's hypothesis: the point is the unique global minimizer of `H`. -/
  | uniqueMin
  /-- Unavailable translation. -/
  | impossible

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .uniqueMin => ∀ x, x ≠ m.point → phLaSalle_H m.point < phLaSalle_H x
  | .impossible => False

/-- Lyapunov stability translates into the unique-minimizer hypothesis, passivity into nothing;
the other sentences have no translation. -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable => {.uniqueMin}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The counterexample family: the gradient pH system centred at the selected point. -/
def family : Family Model Requirement 2 0 :=
  ⟨fun m => (phLaSalle_counterexample.shift m.point).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isNonlinearPH :
    family.IsNonlinearPH fun m => phLaSalle_counterexample.shift m.point := fun _ => rfl

@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  exact fun h => h .impossible

/-- The minimizer `x* = (−2, 0)` meets the note's hypothesis.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem meets_uniqueMin : Meets ⟨phLaSalle_xs⟩ .uniqueMin :=
  fun x hx => phLaSalle_counterexample_unique_min x hx

/-- A unique global minimizer of `H` is Lyapunov stable. -/
@[powerlib_domain] theorem mem_den_lyapunovStable (m : Model) (h : Meets m .uniqueMin) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine family_isNonlinearPH.mem_den_lyapunovStable_shift
    (base := fun _ => phLaSalle_counterexample) (point := Model.point) ?_
  exact eventually_nhdsWithin_of_forall fun x hx => h x hx

/-- The counterexample is passive at every point: `H ≥ −8/3`. -/
@[powerlib_domain] theorem mem_den_passive (m : Model) :
    connection% (m ∈ family.den .passive) :=
  family_isNonlinearPH.mem_den_passive
    (phLaSalle_counterexample.bddBelow_range_shift_H.mpr
      ⟨-(8 / 3), by rintro _ ⟨x, rfl⟩; exact phLaSalle_H_lowerBound x⟩)

@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  refine Family.exact_of_translate_eq_empty rfl ?_
  ext m
  simp only [Set.mem_univ, iff_true]
  exact mem_den_passive m

/-- Every translation of the counterexample family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  rcases s with P | _
  · cases P
    case lyapunovStable => exact mem_den_lyapunovStable m (hm .uniqueMin rfl)
    all_goals exact (hm .impossible trivial).elim
  · exact mem_den_passive m

/-- Refutation of the T-ph §1.2 corollary: the counterexample satisfies "argmin H = {x*}" and
"R ≻ 0 on ∇H ≠ 0" (`meets_uniqueMin`, `phLaSalle_counterexample_damping_pos`), yet `x*` is not
globally asymptotically stable: the second critical point `(1, 0)` is an equilibrium. -/
@[powerlib_domain] theorem not_mem_den_globallyAsymptoticallyStable :
    connection% ((⟨phLaSalle_xs⟩ : Model) ∉
      family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  rw [family_isNonlinearPH.mem_den_flow_shift (base := fun _ => phLaSalle_counterexample)
    (point := Model.point)] at h
  obtain ⟨-, -, -, hattr⟩ := h
  have hcurve : IsIntegralCurveOn (fun _ : ℝ => phLaSalle_xo)
      (fun _ y => phLaSalle_counterexample.zeroInputField y) (Ici 0) := by
    intro t _
    show HasDerivWithinAt (fun _ => phLaSalle_xo)
      (phLaSalle_counterexample.zeroInputField phLaSalle_xo) (Ici 0) t
    rw [phLaSalle_counterexample_equilibrium]
    exact (hasDerivAt_const t phLaSalle_xo).hasDerivWithinAt
  have hlim := hattr 0 _ hcurve
  have heq : phLaSalle_xo = phLaSalle_xs := tendsto_nhds_unique tendsto_const_nhds hlim
  have := congrArg (fun z : State 2 => z 0) heq
  norm_num [phLaSalle_xo, phLaSalle_xs] at this

/-- The note's hypothesis does not translate global asymptotic stability soundly. -/
@[powerlib_domain] theorem uniqueMin_not_sound_globallyAsymptoticallyStable :
    connection% (¬ ∀ m : Model, m ∈ TMIO.realize Meets {.uniqueMin} →
      m ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro H
  have hm : (⟨phLaSalle_xs⟩ : Model) ∈ TMIO.realize Meets {.uniqueMin} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact meets_uniqueMin
  exact not_mem_den_globallyAsymptoticallyStable (H _ hm)

end LaSalle

/-- Corrected §1.2 corollary: if `x*` is the unique global minimizer of `H`, `∇H` vanishes
only at `x*`, the damping power is positive wherever `∇H ≠ 0`, `H` is radially unbounded,
and `H` and the zero-input field are `C¹`, then `x*` is a globally asymptotically stable
equilibrium of the unforced pH system (forward completeness included). -/
@[powerlib_foundation] theorem phGAS_of_unique_critical (M : NonlinearModel n m) {xs : State n}
    (hn : 0 < n) (hH : ContDiff ℝ 1 M.H) (hf : ContDiff ℝ 1 M.zeroInputField)
    (hmin : ∀ x, x ≠ xs → M.H xs < M.H x) (hcrit : ∀ x, M.dH x = 0 → x = xs)
    (hdiss : ∀ x, M.dH x ≠ 0 → 0 < M.dampingPower x)
    (hradial : Tendsto M.H (comap norm atTop) atTop) :
    Flow.GloballyAsymptoticallyStable M.zeroInputField xs := by
  have hloc : IsLocalMin M.H xs :=
    Filter.Eventually.of_forall fun x => by
      by_cases hx : x = xs
      · rw [hx]
      · exact (hmin x hx).le
  have h0 : M.dH xs = 0 := M.dH_eq_zero_of_isLocalMin hloc
  refine Flow.globallyAsymptoticallyStable_of_strictLyapunov (V := fun x => M.H x - M.H xs)
    hn hf (asymptotic_implies_strict ?_)
  exact
    { hcont := M.continuous_H.sub continuous_const
      hV_c1 := hH.sub contDiff_const
      hzero := sub_self _
      hpos := fun x hx => sub_pos.mpr (hmin x hx)
      hequil := M.zeroInputField_eq_zero_of_dH_eq_zero h0
      hLie_neg := fun x hx => by
        rw [fderiv_sub_const, M.zeroInput_power_balance]
        have := hdiss x (fun h => hx (hcrit x h))
        linarith
      hradial := tendsto_atTop_add_const_right _ (-M.H xs) hradial }

end powerlib.PH
