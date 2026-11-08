import theorem.Attributes
import theorem.Passive.Series
import theorem.Passive.Parallel
import dependencies.Mathlib

/-! # Trapezoidal companion models and the EMT nodal equation

The trapezoidal rule on R, L, C branches is exactly the companion form, and the network
discretization is the constant symmetric nodal equation, positive definite when every node is
grounded through positive conductances.

Model boundary.
* A lumped network with `N` non-ground nodes and a finite set of two-terminal branches; every
  branch is a linear resistor, a series RL branch `Passive.SeriesRLC` or a shunt G–C element
  `Passive.ParallelRLC` with constant parameters (an ideal inductor or capacitor is the lossless
  one; no switches, no controlled sources, no mutual coupling, no transmission lines), fixed step
  `h`.
* Each branch runs from terminal `p` to terminal `q` (a node or ground); branch voltage
  `v_b = V_p - V_q`, branch current `i_b` flows from `p` to `q` (passive sign convention). KCL
  at node `k`: the branch currents leaving `k` sum to the external injection `J_k`.
* Time is discrete (`n : ℕ`); the element laws are the trapezoidal rule applied to
  `L di/dt = v − R i` and `C dv/dt = i − G v` (resistor laws are algebraic at every step).

Source: work-sync theory/T-emt-simulation.md §1.2–§1.6, §2.2.

Results.
* `branch_companion_iff`, `shunt_companion_iff` — the trapezoidal rule on the element ODE is
  exactly the companion form `i_{n+1} = G v_{n+1} + i_h` with `G_L = h/(2L + hR)`,
  `i_h^L = ((2L − hR) i_n + h v_n)/(2L + hR)` and `G_C = 2C/h + G`,
  `i_h^C = -(i_n + (2C/h − G) v_n)` (coefficients checked; `R = 0`, `G = 0` give the ideal
  inductor `h/(2L)`, `i_n + G_L v_n` and capacitor `2C/h`, `-(i_n + G_C v_n)`).
* `trapezoidalNetwork_iff_companion` — trapezoidal branch laws + KCL at every step ⇔ the nodal
  companion equation `G_n V_{n+1} = J_{n+1} - Σ_b i_h,b a_b` plus the branch-current update.
  The matrix `G_n = Σ_b G_b a_b a_bᵀ` does not depend on the step index (constant matrix).
* `nodalMatrix_transpose` — `G_n` is symmetric (every branch stamp `G_b a_b a_bᵀ` is).
* `nodalMatrix_posSemidef` — nonnegative branch conductances ⇒ `G_n ⪰ 0`.
* `nodalMatrix_posDef` — if additionally every node is joined to ground by a chain of
  positive-conductance branches, `G_n ≻ 0`; `network_nodalMatrix_posDef` applies this to
  positive `R, L, C`, nonnegative losses and `h > 0`, so every implicit EMT step is uniquely
  solvable.

Corrections.
* T-emt-simulation.md §2.2: the note attributes the symmetry of `G_n^disc` to "`G_L = G_C⁻¹`".
  That relation is false in general (for ideal elements `G_L G_C = L⁻¹ C`, not `1`) and is
  irrelevant: `G_n` is
  symmetric because each branch contributes the symmetric stamp `G_b a_b a_bᵀ`
  (`nodalMatrix_transpose`), for any real branch conductances.
-/

noncomputable section
namespace powerlib.Numerics.EMT
open Matrix

/-! ### Element companion models -/

/-- Series RL branch `L di/dt = v − R i`: the trapezoidal step equals the companion form
`i₁ = G v₁ + i_h`, `G = h/(2L + hR)`, `i_h = ((2L − hR) i₀ + h v₀)/(2L + hR)`. -/
@[tmio M, powerlib_domain] theorem branch_companion_iff {b : Passive.SeriesRLC} {h : ℝ}
    (hL : b.L ≠ 0)
    (hD : 2 * b.L + h * b.R ≠ 0) (i₀ v₀ i₁ v₁ : ℝ) :
    i₁ = i₀ + h / 2 * ((v₀ - b.R * i₀) / b.L + (v₁ - b.R * i₁) / b.L) ↔
      i₁ = h / (2 * b.L + h * b.R) * v₁ +
        ((2 * b.L - h * b.R) * i₀ + h * v₀) / (2 * b.L + h * b.R) := by
  have e1 : i₀ + h / 2 * ((v₀ - b.R * i₀) / b.L + (v₁ - b.R * i₁) / b.L) =
      (2 * b.L * i₀ + h * (v₀ - b.R * i₀ + v₁ - b.R * i₁)) / (2 * b.L) := by
    field_simp; ring
  have e2 : h / (2 * b.L + h * b.R) * v₁ + ((2 * b.L - h * b.R) * i₀ + h * v₀) /
      (2 * b.L + h * b.R) = (h * v₁ + (2 * b.L - h * b.R) * i₀ + h * v₀) / (2 * b.L + h * b.R) := by
    field_simp; ring
  rw [e1, e2, eq_div_iff (mul_ne_zero two_ne_zero hL), eq_div_iff hD]
  constructor <;> intro hk <;> linarith

/-- Shunt G–C element `C dv/dt = i − G v`: the trapezoidal step equals the companion form
`i₁ = G_eq v₁ + i_h`, `G_eq = 2C/h + G`, `i_h = −(i₀ + (2C/h − G) v₀)`. -/
@[tmio M, powerlib_domain] theorem shunt_companion_iff {e : Passive.ParallelRLC} {h : ℝ}
    (hC : e.C ≠ 0)
    (hh : h ≠ 0) (i₀ v₀ i₁ v₁ : ℝ) :
    v₁ = v₀ + h / 2 * ((i₀ - e.G * v₀) / e.C + (i₁ - e.G * v₁) / e.C) ↔
      i₁ = (2 * e.C / h + e.G) * v₁ - (i₀ + (2 * e.C / h - e.G) * v₀) := by
  have e1 : v₀ + h / 2 * ((i₀ - e.G * v₀) / e.C + (i₁ - e.G * v₁) / e.C) =
      (2 * e.C * v₀ + h * (i₀ - e.G * v₀ + i₁ - e.G * v₁)) / (2 * e.C) := by
    field_simp; ring
  have e2 : (2 * e.C / h + e.G) * v₁ - (i₀ + (2 * e.C / h - e.G) * v₀) =
      (2 * e.C * v₁ + h * e.G * v₁ - h * i₀ - 2 * e.C * v₀ + h * e.G * v₀) / h := by
    field_simp; ring
  rw [e1, e2, eq_div_iff (mul_ne_zero two_ne_zero hC), eq_div_iff hh]
  constructor <;> intro hk <;> linarith

/-- A linear two-terminal element: a resistor, a series RL branch (`Passive.SeriesRLC`) or a shunt
G–C element (`Passive.ParallelRLC`); an ideal inductor or capacitor is the lossless branch or
element. -/
inductive Element
  | resistor (R : ℝ)
  | inductor (b : Passive.SeriesRLC)
  | capacitor (e : Passive.ParallelRLC)

namespace Element

/-- Companion conductance. -/
def conductance (h : ℝ) : Element → ℝ
  | resistor R => 1 / R
  | inductor b => h / (2 * b.L + h * b.R)
  | capacitor e => 2 * e.C / h + e.G

/-- Companion history current from the previous branch current and voltage. -/
def history (h : ℝ) : Element → ℝ → ℝ → ℝ
  | resistor _, _, _ => 0
  | inductor b, i₀, v₀ => ((2 * b.L - h * b.R) * i₀ + h * v₀) / (2 * b.L + h * b.R)
  | capacitor e, i₀, v₀ => -(i₀ + (2 * e.C / h - e.G) * v₀)

/-- The element law over one step: Ohm's law, or the trapezoidal rule on the element ODE
(`Passive.SeriesRLC`: `L di/dt = v − R i`; `Passive.ParallelRLC`: `C dv/dt = i − G v`). -/
def StepLaw (h : ℝ) : Element → ℝ → ℝ → ℝ → ℝ → Prop
  | resistor R, _, _, i₁, v₁ => v₁ = R * i₁
  | inductor b, i₀, v₀, i₁, v₁ =>
      i₁ = i₀ + h / 2 * ((v₀ - b.R * i₀) / b.L + (v₁ - b.R * i₁) / b.L)
  | capacitor e, i₀, v₀, i₁, v₁ =>
      v₁ = v₀ + h / 2 * ((i₀ - e.G * v₀) / e.C + (i₁ - e.G * v₁) / e.C)

/-- Nonzero parameters for the step `h`. -/
def Valid (h : ℝ) : Element → Prop
  | resistor R => R ≠ 0
  | inductor b => b.L ≠ 0 ∧ 2 * b.L + h * b.R ≠ 0
  | capacitor e => e.C ≠ 0

/-- Positive storage and nonnegative loss (passive element). -/
def Positive : Element → Prop
  | resistor R => 0 < R
  | inductor b => 0 < b.L ∧ 0 ≤ b.R
  | capacitor e => 0 < e.C ∧ 0 ≤ e.G

@[tmio M, powerlib_domain] theorem stepLaw_iff_companion {h : ℝ} (hh : h ≠ 0) (e : Element)
    (he : e.Valid h) (i₀ v₀ i₁ v₁ : ℝ) :
    e.StepLaw h i₀ v₀ i₁ v₁ ↔ i₁ = e.conductance h * v₁ + e.history h i₀ v₀ := by
  cases e with
  | resistor R =>
    simp only [StepLaw, conductance, history, add_zero]
    have hR : R ≠ 0 := he
    constructor <;> intro hk
    · rw [hk]; field_simp
    · rw [hk]; field_simp
  | inductor b => exact branch_companion_iff (h := h) he.1 he.2 i₀ v₀ i₁ v₁
  | capacitor e =>
    simp only [StepLaw, conductance, history]
    rw [shunt_companion_iff (h := h) he hh, sub_eq_add_neg]

@[tmio M, powerlib_domain] theorem conductance_pos {h : ℝ} (hh : 0 < h) (e : Element)
    (he : e.Positive) : 0 < e.conductance h := by
  cases e with
  | resistor R => exact one_div_pos.mpr he
  | inductor b =>
    have : 0 < 2 * b.L + h * b.R := by nlinarith [he.1, he.2]
    exact div_pos hh this
  | capacitor e =>
    have : 0 < 2 * e.C / h := div_pos (mul_pos two_pos he.1) hh
    exact add_pos_of_pos_of_nonneg this he.2

@[tmio M, powerlib_domain] theorem Positive.valid {e : Element} {h : ℝ} (hh : 0 < h)
    (he : e.Positive) : e.Valid h := by
  cases e with
  | resistor R => exact ne_of_gt he
  | inductor b => exact ⟨ne_of_gt he.1, by nlinarith [he.1, he.2]⟩
  | capacitor e => exact ne_of_gt he.1

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

@[tmio T, powerlib_foundation] theorem Terminal.vec_dotProduct {N : ℕ} (t : Terminal N)
    (V : Fin N → ℝ) : t.vec ⬝ᵥ V = t.potential V := by
  cases t <;> simp [Terminal.vec, Terminal.potential]

variable {N : ℕ} {β : Type*} [Fintype β]

/-- Branch incidence vector `a_b = e_p - e_q`. -/
def incidence (p q : β → Terminal N) (b : β) : Fin N → ℝ := (p b).vec - (q b).vec

/-- Nodal matrix `G_n = Σ_b G_b a_b a_bᵀ`. -/
def nodalMatrix (p q : β → Terminal N) (G : β → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ b, G b • vecMulVec (incidence p q b) (incidence p q b)

omit [Fintype β] in
@[tmio T, powerlib_foundation] theorem incidence_dotProduct (p q : β → Terminal N) (b : β)
    (V : Fin N → ℝ) :
    incidence p q b ⬝ᵥ V = (p b).potential V - (q b).potential V := by
  rw [incidence, sub_dotProduct, Terminal.vec_dotProduct, Terminal.vec_dotProduct]

@[tmio T, powerlib_foundation] theorem nodalMatrix_mulVec (p q : β → Terminal N) (G : β → ℝ)
    (V : Fin N → ℝ) :
    nodalMatrix p q G *ᵥ V = ∑ b, (G b * (incidence p q b ⬝ᵥ V)) • incidence p q b := by
  ext k
  simp [nodalMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The nodal matrix is symmetric: each branch stamp is symmetric. -/
@[tmio T, powerlib_foundation] theorem nodalMatrix_transpose (p q : β → Terminal N) (G : β → ℝ) :
    (nodalMatrix p q G)ᵀ = nodalMatrix p q G := by
  simp [nodalMatrix, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

@[tmio T, powerlib_foundation] theorem nodalMatrix_quadratic (p q : β → Terminal N) (G : β → ℝ)
    (V : Fin N → ℝ) :
    V ⬝ᵥ (nodalMatrix p q G *ᵥ V) = ∑ b, G b * (incidence p q b ⬝ᵥ V) ^ 2 := by
  rw [nodalMatrix_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

@[tmio T, powerlib_foundation] theorem nodalMatrix_posSemidef (p q : β → Terminal N) (G : β → ℝ)
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

@[tmio T, powerlib_foundation] theorem nodalMatrix_posDef (p q : β → Terminal N) (G : β → ℝ)
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
@[tmio T, powerlib_foundation] theorem kcl_iff_nodal (p q : β → Terminal N) (G ih : β → ℝ)
    (V J : Fin N → ℝ) :
    (∑ b, (G b * (incidence p q b ⬝ᵥ V) + ih b) • incidence p q b = J) ↔
      nodalMatrix p q G *ᵥ V = J - ∑ b, ih b • incidence p q b := by
  rw [nodalMatrix_mulVec, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  simp only [add_smul]

/-- The companion nodal formulation is exactly the trapezoidal discretization of the
network: a trapezoidal network trajectory (element step laws for every branch and KCL at every
new step) is exactly a solution of the companion nodal equations (the constant matrix `G_n` times
the new node voltages equals the injections minus the history sources, and branch currents follow
the companion law). Discrete trajectories are written out, not defined: discrete behaviour is
defined only in the semantic layer. -/
@[tmio M, powerlib_domain] theorem trapezoidalNetwork_iff_companion {h : ℝ} (hh : h ≠ 0)
    (e : β → Element) (he : ∀ b, (e b).Valid h) (p q : β → Terminal N) (V : ℕ → Fin N → ℝ)
    (I : ℕ → β → ℝ) (J : ℕ → Fin N → ℝ) :
    (∀ n, (∀ b, (e b).StepLaw h (I n b) (incidence p q b ⬝ᵥ V n) (I (n + 1) b)
        (incidence p q b ⬝ᵥ V (n + 1))) ∧
      ∑ b, I (n + 1) b • incidence p q b = J (n + 1)) ↔
    ∀ n, nodalMatrix p q (fun b => (e b).conductance h) *ᵥ V (n + 1) =
        J (n + 1) - ∑ b, (e b).history h (I n b) (incidence p q b ⬝ᵥ V n) • incidence p q b ∧
      ∀ b, I (n + 1) b = (e b).conductance h * (incidence p q b ⬝ᵥ V (n + 1)) +
        (e b).history h (I n b) (incidence p q b ⬝ᵥ V n) := by
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
@[tmio M, powerlib_domain] theorem network_nodalMatrix_posDef {h : ℝ} (hh : 0 < h)
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
