import theorem.Attributes
import dependencies.Mathlib

/-! # Trapezoidal companion models and the EMT nodal equation

The trapezoidal rule on R, L, C branches is exactly the companion form, and the network
discretization is the constant symmetric nodal equation, positive definite when every node is
grounded through positive conductances.

Model boundary.
* A lumped network with `N` non-ground nodes and a finite set of two-terminal branches; every
  branch is a linear resistor, inductor or capacitor with a constant parameter (no switches, no
  controlled sources, no mutual coupling, no transmission lines), fixed step `h`.
* Each branch runs from terminal `p` to terminal `q` (a node or ground); branch voltage
  `v_b = V_p - V_q`, branch current `i_b` flows from `p` to `q` (passive sign convention). KCL
  at node `k`: the branch currents leaving `k` sum to the external injection `J_k`.
* Time is discrete (`n : ℕ`); the element laws are the trapezoidal rule applied to
  `L di/dt = v` and `C dv/dt = i` (resistor laws are algebraic at every step).

Source: work-sync theory/T-emt-simulation.md §1.2–§1.6, §2.2.

Results.
* `inductor_companion_iff`, `capacitor_companion_iff` — the trapezoidal rule on the branch ODE is
  exactly the companion form `i_{n+1} = G v_{n+1} + i_h` with `G_L = h/(2L)`,
  `i_h^L = i_n + G_L v_n` and `G_C = 2C/h`, `i_h^C = -(i_n + G_C v_n)` (coefficients checked).
* `trapezoidalNetwork_iff_companion` — trapezoidal branch laws + KCL at every step ⇔ the nodal
  companion equation `G_n V_{n+1} = J_{n+1} - Σ_b i_h,b a_b` plus the branch-current update.
  The matrix `G_n = Σ_b G_b a_b a_bᵀ` does not depend on the step index (constant matrix).
* `nodalMatrix_transpose` — `G_n` is symmetric (every branch stamp `G_b a_b a_bᵀ` is).
* `nodalMatrix_posSemidef` — nonnegative branch conductances ⇒ `G_n ⪰ 0`.
* `nodalMatrix_posDef` — if additionally every node is joined to ground by a chain of
  positive-conductance branches, `G_n ≻ 0`; `network_nodalMatrix_posDef` applies this to
  positive `R, L, C` and `h > 0`, so every implicit EMT step is uniquely solvable.

Corrections.
* T-emt-simulation.md §2.2: the note attributes the symmetry of `G_n^disc` to "`G_L = G_C⁻¹`".
  That relation is false in general (`G_L G_C = L⁻¹ C`, not `1`) and is irrelevant: `G_n` is
  symmetric because each branch contributes the symmetric stamp `G_b a_b a_bᵀ`
  (`nodalMatrix_transpose`), for any real branch conductances.
-/

noncomputable section
namespace powerlib.Numerics.EMT
open Matrix

/-! ### Element companion models -/

/-- Inductor `L di/dt = v`: the trapezoidal step equals the companion form. -/
@[powerlib_foundation] theorem inductor_companion_iff {L h : ℝ} (hL : L ≠ 0)
    (i₀ v₀ i₁ v₁ : ℝ) :
    i₁ = i₀ + h / 2 * (v₀ / L + v₁ / L) ↔ i₁ = h / (2 * L) * v₁ + (i₀ + h / (2 * L) * v₀) := by
  constructor <;> intro hk <;> rw [hk] <;> field_simp <;> ring

/-- Capacitor `C dv/dt = i`: the trapezoidal step equals the companion form. -/
@[powerlib_foundation] theorem capacitor_companion_iff {C h : ℝ} (hC : C ≠ 0) (hh : h ≠ 0)
    (i₀ v₀ i₁ v₁ : ℝ) :
    v₁ = v₀ + h / 2 * (i₀ / C + i₁ / C) ↔ i₁ = 2 * C / h * v₁ - (i₀ + 2 * C / h * v₀) := by
  constructor <;> intro hk
  · rw [hk]; field_simp; ring
  · rw [hk]; field_simp; ring

/-- A linear two-terminal element. -/
inductive Element
  | resistor (R : ℝ)
  | inductor (L : ℝ)
  | capacitor (C : ℝ)

namespace Element

/-- Companion conductance. -/
def conductance (h : ℝ) : Element → ℝ
  | resistor R => 1 / R
  | inductor L => h / (2 * L)
  | capacitor C => 2 * C / h

/-- Companion history current from the previous branch current and voltage. -/
def history (h : ℝ) : Element → ℝ → ℝ → ℝ
  | resistor _, _, _ => 0
  | inductor L, i₀, v₀ => i₀ + h / (2 * L) * v₀
  | capacitor C, i₀, v₀ => -(i₀ + 2 * C / h * v₀)

/-- The element law over one step: Ohm's law, or the trapezoidal rule on the branch ODE. -/
def StepLaw (h : ℝ) : Element → ℝ → ℝ → ℝ → ℝ → Prop
  | resistor R, _, _, i₁, v₁ => v₁ = R * i₁
  | inductor L, i₀, v₀, i₁, v₁ => i₁ = i₀ + h / 2 * (v₀ / L + v₁ / L)
  | capacitor C, i₀, v₀, i₁, v₁ => v₁ = v₀ + h / 2 * (i₀ / C + i₁ / C)

/-- Nonzero parameter. -/
def Valid : Element → Prop
  | resistor R => R ≠ 0
  | inductor L => L ≠ 0
  | capacitor C => C ≠ 0

/-- Positive parameter (passive element). -/
def Positive : Element → Prop
  | resistor R => 0 < R
  | inductor L => 0 < L
  | capacitor C => 0 < C

@[powerlib_foundation] theorem stepLaw_iff_companion {h : ℝ} (hh : h ≠ 0) (e : Element)
    (he : e.Valid) (i₀ v₀ i₁ v₁ : ℝ) :
    e.StepLaw h i₀ v₀ i₁ v₁ ↔ i₁ = e.conductance h * v₁ + e.history h i₀ v₀ := by
  cases e with
  | resistor R =>
    simp only [StepLaw, conductance, history, add_zero]
    have hR : R ≠ 0 := he
    constructor <;> intro hk
    · rw [hk]; field_simp
    · rw [hk]; field_simp
  | inductor L => exact inductor_companion_iff (h := h) he i₀ v₀ i₁ v₁
  | capacitor C =>
    simp only [StepLaw, conductance, history]
    rw [capacitor_companion_iff (h := h) he hh, sub_eq_add_neg]

@[powerlib_foundation] theorem conductance_pos {h : ℝ} (hh : 0 < h) (e : Element)
    (he : e.Positive) : 0 < e.conductance h := by
  cases e with
  | resistor R => exact one_div_pos.mpr he
  | inductor L => exact div_pos hh (mul_pos two_pos he)
  | capacitor C => exact div_pos (mul_pos two_pos he) hh

@[powerlib_foundation] theorem Positive.valid {e : Element} (he : e.Positive) : e.Valid := by
  cases e with
  | resistor R => exact ne_of_gt he
  | inductor L => exact ne_of_gt he
  | capacitor C => exact ne_of_gt he

end Element

/-! ### Network assembly -/

/-- A branch terminal: a non-ground node or ground. -/
inductive Terminal (N : ℕ)
  | node (i : Fin N)
  | ground

/-- Node-incidence vector of a terminal. -/
def Terminal.vec {N : ℕ} : Terminal N → Fin N → ℝ
  | .node i => Pi.single i 1
  | .ground => 0

/-- Terminal potential (`0` at ground). -/
def Terminal.potential {N : ℕ} (V : Fin N → ℝ) : Terminal N → ℝ
  | .node i => V i
  | .ground => 0

@[powerlib_foundation] theorem Terminal.vec_dotProduct {N : ℕ} (t : Terminal N)
    (V : Fin N → ℝ) : t.vec ⬝ᵥ V = t.potential V := by
  cases t <;> simp [Terminal.vec, Terminal.potential]

variable {N : ℕ} {β : Type*} [Fintype β]

/-- Branch incidence vector `a_b = e_p - e_q`. -/
def incidence (p q : β → Terminal N) (b : β) : Fin N → ℝ := (p b).vec - (q b).vec

/-- Nodal matrix `G_n = Σ_b G_b a_b a_bᵀ`. -/
def nodalMatrix (p q : β → Terminal N) (G : β → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ b, G b • vecMulVec (incidence p q b) (incidence p q b)

omit [Fintype β] in
@[powerlib_foundation] theorem incidence_dotProduct (p q : β → Terminal N) (b : β)
    (V : Fin N → ℝ) :
    incidence p q b ⬝ᵥ V = (p b).potential V - (q b).potential V := by
  rw [incidence, sub_dotProduct, Terminal.vec_dotProduct, Terminal.vec_dotProduct]

@[powerlib_foundation] theorem nodalMatrix_mulVec (p q : β → Terminal N) (G : β → ℝ)
    (V : Fin N → ℝ) :
    nodalMatrix p q G *ᵥ V = ∑ b, (G b * (incidence p q b ⬝ᵥ V)) • incidence p q b := by
  ext k
  simp [nodalMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The nodal matrix is symmetric: each branch stamp is symmetric. -/
@[powerlib_foundation] theorem nodalMatrix_transpose (p q : β → Terminal N) (G : β → ℝ) :
    (nodalMatrix p q G)ᵀ = nodalMatrix p q G := by
  simp [nodalMatrix, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

@[powerlib_foundation] theorem nodalMatrix_quadratic (p q : β → Terminal N) (G : β → ℝ)
    (V : Fin N → ℝ) :
    V ⬝ᵥ (nodalMatrix p q G *ᵥ V) = ∑ b, G b * (incidence p q b ⬝ᵥ V) ^ 2 := by
  rw [nodalMatrix_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

@[powerlib_foundation] theorem nodalMatrix_posSemidef (p q : β → Terminal N) (G : β → ℝ)
    (hG : ∀ b, 0 ≤ G b) : (nodalMatrix p q G).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun V => ?_
  · exact nodalMatrix_transpose p q G
  · rw [star_trivial, nodalMatrix_quadratic]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hG b) (sq_nonneg _)

/-- Terminals joined by a positive-conductance branch. -/
def Adjacent (p q : β → Terminal N) (G : β → ℝ) (s t : Terminal N) : Prop :=
  ∃ b, 0 < G b ∧ ((s = p b ∧ t = q b) ∨ (s = q b ∧ t = p b))

/-- Every node reaches ground through positive-conductance branches. -/
def GroundConnected (p q : β → Terminal N) (G : β → ℝ) : Prop :=
  ∀ i : Fin N, Relation.ReflTransGen (Adjacent p q G) (.node i) .ground

@[powerlib_foundation] theorem nodalMatrix_posDef (p q : β → Terminal N) (G : β → ℝ)
    (hG : ∀ b, 0 ≤ G b) (hconn : GroundConnected p q G) : (nodalMatrix p q G).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (nodalMatrix_transpose p q G) fun V hV => ?_
  rw [star_trivial, nodalMatrix_quadratic]
  have hnn : ∀ b ∈ Finset.univ, 0 ≤ G b * (incidence p q b ⬝ᵥ V) ^ 2 :=
    fun b _ => mul_nonneg (hG b) (sq_nonneg _)
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => hV ?_
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0.symm
  have hedge : ∀ s t, Adjacent p q G s t → s.potential V = t.potential V := by
    rintro s t ⟨b, hb, hst⟩
    have h1 := hzero b (Finset.mem_univ b)
    have h2 : incidence p q b ⬝ᵥ V = 0 := by
      have := (mul_eq_zero.mp h1).resolve_left hb.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    rw [incidence_dotProduct] at h2
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  funext i
  have key : ∀ t, Relation.ReflTransGen (Adjacent p q G) (.node i) t →
      (Terminal.node i : Terminal N).potential V = t.potential V := by
    intro t ht
    induction ht with
    | refl => rfl
    | tail _ hst ih => exact ih.trans (hedge _ _ hst)
  simpa [Terminal.potential] using key _ (hconn i)

/-! ### Trapezoidal network ⇔ nodal companion equation -/

/-- KCL with affine branch laws `i_b = G_b v_b + i_h,b` is the nodal equation. -/
@[powerlib_foundation] theorem kcl_iff_nodal (p q : β → Terminal N) (G ih : β → ℝ)
    (V J : Fin N → ℝ) :
    (∑ b, (G b * (incidence p q b ⬝ᵥ V) + ih b) • incidence p q b = J) ↔
      nodalMatrix p q G *ᵥ V = J - ∑ b, ih b • incidence p q b := by
  rw [nodalMatrix_mulVec, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  simp only [add_smul]

/-- A trapezoidal EMT network trajectory: element step laws for every branch and KCL at every
new step. -/
def IsTrapezoidalNetwork (h : ℝ) (e : β → Element) (p q : β → Terminal N)
    (V : ℕ → Fin N → ℝ) (I : ℕ → β → ℝ) (J : ℕ → Fin N → ℝ) : Prop :=
  ∀ n, (∀ b, (e b).StepLaw h (I n b) (incidence p q b ⬝ᵥ V n) (I (n + 1) b)
      (incidence p q b ⬝ᵥ V (n + 1))) ∧
    ∑ b, I (n + 1) b • incidence p q b = J (n + 1)

/-- Companion nodal equations: the constant matrix `G_n` times the new node voltages equals
the injections minus the history sources, and branch currents follow the companion law. -/
def IsCompanionNetwork (h : ℝ) (e : β → Element) (p q : β → Terminal N)
    (V : ℕ → Fin N → ℝ) (I : ℕ → β → ℝ) (J : ℕ → Fin N → ℝ) : Prop :=
  ∀ n, nodalMatrix p q (fun b => (e b).conductance h) *ᵥ V (n + 1) =
      J (n + 1) - ∑ b, (e b).history h (I n b) (incidence p q b ⬝ᵥ V n) • incidence p q b ∧
    ∀ b, I (n + 1) b = (e b).conductance h * (incidence p q b ⬝ᵥ V (n + 1)) +
      (e b).history h (I n b) (incidence p q b ⬝ᵥ V n)

/-- The companion nodal formulation is exactly the trapezoidal discretization of the
network. -/
@[powerlib_foundation] theorem trapezoidalNetwork_iff_companion {h : ℝ} (hh : h ≠ 0)
    (e : β → Element) (he : ∀ b, (e b).Valid) (p q : β → Terminal N) (V : ℕ → Fin N → ℝ)
    (I : ℕ → β → ℝ) (J : ℕ → Fin N → ℝ) :
    IsTrapezoidalNetwork h e p q V I J ↔ IsCompanionNetwork h e p q V I J := by
  simp only [IsTrapezoidalNetwork, IsCompanionNetwork]
  refine forall_congr' fun n => ?_
  simp only [fun b => Element.stepLaw_iff_companion hh (e b) (he b)]
  constructor
  · rintro ⟨hlaw, hkcl⟩
    refine ⟨?_, hlaw⟩
    rw [← kcl_iff_nodal]
    rw [← hkcl]
    exact Finset.sum_congr rfl fun b _ => by rw [hlaw b]
  · rintro ⟨hnod, hlaw⟩
    refine ⟨hlaw, ?_⟩
    rw [← (kcl_iff_nodal p q _ _ _ _).mpr hnod]
    exact Finset.sum_congr rfl fun b _ => by rw [hlaw b]

/-- Positive `R, L, C`, `h > 0` and ground connectivity: the EMT nodal matrix is positive
definite, hence every implicit step has a unique solution. -/
@[powerlib_foundation] theorem network_nodalMatrix_posDef {h : ℝ} (hh : 0 < h)
    (e : β → Element) (he : ∀ b, (e b).Positive) (p q : β → Terminal N)
    (hconn : ∀ i : Fin N, Relation.ReflTransGen
      (fun s t => ∃ b, (s = p b ∧ t = q b) ∨ (s = q b ∧ t = p b)) (.node i) .ground) :
    (nodalMatrix p q (fun b => (e b).conductance h)).PosDef := by
  refine nodalMatrix_posDef p q _ (fun b => (Element.conductance_pos hh (e b) (he b)).le) ?_
  intro i
  refine Relation.ReflTransGen.mono (fun s t hst => ?_) _ _ (hconn i)
  obtain ⟨b, hb⟩ := hst
  exact ⟨b, Element.conductance_pos hh (e b) (he b), hb⟩

end powerlib.Numerics.EMT
