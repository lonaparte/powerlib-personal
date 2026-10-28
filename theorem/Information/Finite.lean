import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Field

/-! # Finite-state maximum entropy, Gibbs inequality and the Boltzmann–Gibbs law

On a finite index set: the Gibbs inequality, the Pythagorean identity of relative entropy, the
unique MaxEnt (Gibbs) solution, and the Boltzmann–Gibbs law as the Shannon-entropy maximiser.

Scope.
* General probability, not an engineering result.
* A finite index type `ι` (states, or whole paths). A probability vector `p` (nonnegative,
  `∑ p = 1`), a strictly positive reference weight `q` (not necessarily normalised; `q = 1` is
  the counting measure), and a log-tilt `g`. The Gibbs vector is
  `gibbsVec q g i = q i exp(g i) / Z`, `Z = ∑ q exp g`. For one constraint `E[f] = F` with
  multiplier `λ`, `g = -λ f`.
* `klSum p q = ∑ p log (p / q)` is the discrete relative entropy (`0 · log 0 = 0` holds by
  Lean's convention `0 * x = 0`). `shannon p = ∑ -p log p`.

Source: work-sync theory/T-maximum-entropy.md head (boxed MaxEnt form with reference measure
`m`), §1.3 (Boltzmann–Gibbs), §1.6 (exponential family); theory/T-maximum-caliber.md uses the
same statement on a finite path space (see `theorem/Information/MaxCaliber.lean`).

Results.
* `klSum_nonneg`, `klSum_eq_zero_iff` — Gibbs inequality on a finite set.
* `klSum_eq_klSum_gibbsVec_add` — Pythagorean identity.
* `klSum_gibbsVec_le`, `klSum_eq_klSum_gibbsVec_iff` — unique MaxEnt solution.
* `shannon_le_shannon_boltzmann`, `shannon_eq_shannon_boltzmann_iff` — Boltzmann–Gibbs
  maximises Shannon entropy at fixed mean energy.
* `shannon_boltzmann` — `S = β⟨E⟩ + log Z`.
-/

noncomputable section
namespace powerlib.Information
open Real Finset

variable {ι : Type*} [Fintype ι]

/-- Discrete relative entropy `∑ pᵢ log (pᵢ / qᵢ)`. -/
def klSum (p q : ι → ℝ) : ℝ := ∑ i, p i * log (p i / q i)

/-- Shannon entropy `-∑ pᵢ log pᵢ`. -/
def shannon (p : ι → ℝ) : ℝ := ∑ i, negMulLog (p i)

/-- Partition function `Z = ∑ qᵢ exp gᵢ`. -/
def partitionSum (q g : ι → ℝ) : ℝ := ∑ i, q i * exp (g i)

/-- Gibbs vector `qᵢ exp gᵢ / Z`. -/
def gibbsVec (q g : ι → ℝ) (i : ι) : ℝ := q i * exp (g i) / partitionSum q g

/-- Boltzmann–Gibbs law `exp(-β Eᵢ) / Z(β)` (uniform reference). -/
def boltzmann (β : ℝ) (E : ι → ℝ) : ι → ℝ := gibbsVec (fun _ => 1) (fun i => -β * E i)

@[tmio T, powerlib_foundation] theorem shannon_eq_neg_klSum_one (p : ι → ℝ) :
    shannon p = -klSum p (fun _ => 1) := by
  simp [shannon, klSum, negMulLog, Finset.sum_neg_distrib]

/-- Termwise Gibbs bound `p - q ≤ p log (p / q)` for `p ≥ 0`, `q > 0`, strict unless `p = q`. -/
@[powerlib_foundation] private theorem term_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * log (a / b) := by
  have h := Real.self_sub_one_le_mul_log (div_nonneg ha hb.le)
  have h2 : b * (a / b - 1) ≤ b * (a / b * log (a / b)) := mul_le_mul_of_nonneg_left h hb.le
  have e1 : b * (a / b - 1) = a - b := by field_simp
  have e2 : b * (a / b * log (a / b)) = a * log (a / b) := by field_simp
  linarith

@[powerlib_foundation] private theorem term_bound_strict {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a ≠ b) : a - b < a * log (a / b) := by
  have hne : a / b ≠ 1 := by
    intro h; apply hab; field_simp at h; linarith
  have h := Real.self_sub_one_lt_mul_log (div_nonneg ha hb.le) hne
  have h2 : b * (a / b - 1) < b * (a / b * log (a / b)) := mul_lt_mul_of_pos_left h hb
  have e1 : b * (a / b - 1) = a - b := by field_simp
  have e2 : b * (a / b * log (a / b)) = a * log (a / b) := by field_simp
  linarith

/-- **Gibbs inequality** on a finite set. -/
@[powerlib_foundation] theorem klSum_nonneg {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) : 0 ≤ klSum p q := by
  have h : ∑ i, (p i - q i) ≤ klSum p q :=
    Finset.sum_le_sum fun i _ => term_bound (hp i) (hq i)
  rw [Finset.sum_sub_distrib, hp1, hq1, sub_self] at h
  exact h

/-- **Converse Gibbs inequality**: `klSum p q = 0` iff `p = q`. -/
@[powerlib_foundation] theorem klSum_eq_zero_iff {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 < q i) (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    klSum p q = 0 ↔ p = q := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hlt : ∑ i, (p i - q i) < klSum p q :=
      Finset.sum_lt_sum (fun i _ => term_bound (hp i) (hq i))
        ⟨j, Finset.mem_univ _, term_bound_strict (hp j) (hq j) hj⟩
    rw [Finset.sum_sub_distrib, hp1, hq1, sub_self, h] at hlt
    exact lt_irrefl _ hlt
  · rintro rfl
    simp only [klSum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [div_self (hq i).ne', log_one, mul_zero]

section Gibbs

variable {q g : ι → ℝ}

@[powerlib_foundation] theorem partitionSum_pos [Nonempty ι] (hq : ∀ i, 0 < q i) :
    0 < partitionSum q g :=
  Finset.sum_pos (fun i _ => mul_pos (hq i) (exp_pos _)) Finset.univ_nonempty

@[powerlib_foundation] theorem gibbsVec_pos [Nonempty ι] (hq : ∀ i, 0 < q i) (i : ι) :
    0 < gibbsVec q g i :=
  div_pos (mul_pos (hq i) (exp_pos _)) (partitionSum_pos hq)

@[powerlib_foundation] theorem sum_gibbsVec [Nonempty ι] (hq : ∀ i, 0 < q i) :
    ∑ i, gibbsVec q g i = 1 := by
  simp only [gibbsVec, ← Finset.sum_div]
  exact div_self (partitionSum_pos (g := g) hq).ne'

@[powerlib_foundation] theorem log_gibbsVec_div [Nonempty ι] (hq : ∀ i, 0 < q i) (i : ι) :
    log (gibbsVec q g i / q i) = g i - log (partitionSum q g) := by
  have hZ := partitionSum_pos (g := g) hq
  rw [gibbsVec, show q i * exp (g i) / partitionSum q g / q i = exp (g i) / partitionSum q g by
    field_simp [(hq i).ne'], log_div (exp_pos _).ne' hZ.ne', log_exp]

/-- Relative entropy of an arbitrary probability vector against the reference, split through
`log(gᵢ)`: `∑ p log (gibbs/q) = E_p[g] - log Z`. -/
@[powerlib_foundation] private theorem sum_mul_log_gibbsVec_div [Nonempty ι] (hq : ∀ i, 0 < q i)
    {p : ι → ℝ} (hp1 : ∑ i, p i = 1) :
    ∑ i, p i * log (gibbsVec q g i / q i) = ∑ i, p i * g i - log (partitionSum q g) := by
  simp only [log_gibbsVec_div hq, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]

@[powerlib_foundation] theorem klSum_gibbsVec [Nonempty ι] (hq : ∀ i, 0 < q i) :
    klSum (gibbsVec q g) q = ∑ i, gibbsVec q g i * g i - log (partitionSum q g) :=
  sum_mul_log_gibbsVec_div hq (sum_gibbsVec hq)

/-- **Pythagorean identity** (finite MaxEnt). If `E_p[g] = E_{gibbs}[g]` then
`klSum p q = klSum p gibbs + klSum gibbs q`. -/
@[powerlib_foundation] theorem klSum_eq_klSum_gibbsVec_add [Nonempty ι] (hq : ∀ i, 0 < q i)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hmom : ∑ i, p i * g i = ∑ i, gibbsVec q g i * g i) :
    klSum p q = klSum p (gibbsVec q g) + klSum (gibbsVec q g) q := by
  have hsplit : ∀ i, p i * log (p i / q i) =
      p i * log (p i / gibbsVec q g i) + p i * log (gibbsVec q g i / q i) := by
    intro i
    rcases (hp i).eq_or_lt with h | h
    · rw [← h]; ring
    · rw [← mul_add, ← log_mul (div_pos h (gibbsVec_pos hq i)).ne'
        (div_pos (gibbsVec_pos hq i) (hq i)).ne']
      congr 2
      field_simp [(gibbsVec_pos (g := g) hq i).ne', (hq i).ne']
  have h1 : klSum p q = klSum p (gibbsVec q g) + ∑ i, p i * log (gibbsVec q g i / q i) := by
    simp only [klSum, hsplit, Finset.sum_add_distrib]
  rw [h1, sum_mul_log_gibbsVec_div hq hp1, hmom, klSum_gibbsVec hq]

/-- The Gibbs vector minimises relative entropy (maximises `H[·‖q]`) in its moment class. -/
@[powerlib_foundation] theorem klSum_gibbsVec_le [Nonempty ι] (hq : ∀ i, 0 < q i)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hmom : ∑ i, p i * g i = ∑ i, gibbsVec q g i * g i) :
    klSum (gibbsVec q g) q ≤ klSum p q := by
  rw [klSum_eq_klSum_gibbsVec_add hq hp hp1 hmom]
  linarith [klSum_nonneg hp (gibbsVec_pos (g := g) hq) hp1 (sum_gibbsVec (g := g) hq)]

/-- Uniqueness of the finite MaxEnt solution. -/
@[powerlib_foundation] theorem klSum_eq_klSum_gibbsVec_iff [Nonempty ι] (hq : ∀ i, 0 < q i)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hmom : ∑ i, p i * g i = ∑ i, gibbsVec q g i * g i) :
    klSum p q = klSum (gibbsVec q g) q ↔ p = gibbsVec q g := by
  rw [klSum_eq_klSum_gibbsVec_add hq hp hp1 hmom, add_eq_right,
    klSum_eq_zero_iff hp (gibbsVec_pos (g := g) hq) hp1 (sum_gibbsVec (g := g) hq)]

end Gibbs

section Boltzmann

variable [Nonempty ι] {β : ℝ} {E : ι → ℝ}

@[powerlib_foundation] theorem boltzmann_pos (i : ι) : 0 < boltzmann β E i :=
  gibbsVec_pos (fun _ => one_pos) i

@[powerlib_foundation] theorem sum_boltzmann : ∑ i, boltzmann β E i = 1 :=
  sum_gibbsVec fun _ => one_pos

/-- Thermodynamic identity `S = β⟨E⟩ + log Z` for the Boltzmann–Gibbs law. -/
@[powerlib_foundation] theorem shannon_boltzmann :
    shannon (boltzmann β E) = β * ∑ i, boltzmann β E i * E i +
      log (∑ i, exp (-β * E i)) := by
  have h := klSum_gibbsVec (q := fun _ : ι => (1 : ℝ)) (g := fun i => -β * E i)
    (fun _ => one_pos)
  rw [shannon_eq_neg_klSum_one, boltzmann, h, partitionSum, Finset.mul_sum]
  simp only [one_mul, neg_sub, mul_neg, neg_mul, Finset.sum_neg_distrib]
  ring_nf

/-- **Boltzmann–Gibbs is the MaxEnt law at fixed mean energy.** -/
@[powerlib_foundation] theorem shannon_le_shannon_boltzmann {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hE : ∑ i, p i * E i = ∑ i, boltzmann β E i * E i) :
    shannon p ≤ shannon (boltzmann β E) := by
  have hmom : ∑ i, p i * (-β * E i) = ∑ i, boltzmann β E i * (-β * E i) := by
    simp only [mul_left_comm _ (-β), ← Finset.mul_sum, hE]
  rw [shannon_eq_neg_klSum_one, shannon_eq_neg_klSum_one, neg_le_neg_iff]
  exact klSum_gibbsVec_le (fun _ => one_pos) hp hp1 hmom

@[powerlib_foundation] theorem shannon_eq_shannon_boltzmann_iff {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hE : ∑ i, p i * E i = ∑ i, boltzmann β E i * E i) :
    shannon p = shannon (boltzmann β E) ↔ p = boltzmann β E := by
  have hmom : ∑ i, p i * (-β * E i) = ∑ i, boltzmann β E i * (-β * E i) := by
    simp only [mul_left_comm _ (-β), ← Finset.mul_sum, hE]
  rw [shannon_eq_neg_klSum_one, shannon_eq_neg_klSum_one, neg_inj]
  exact klSum_eq_klSum_gibbsVec_iff (fun _ => one_pos) hp hp1 hmom

end Boltzmann

end powerlib.Information
