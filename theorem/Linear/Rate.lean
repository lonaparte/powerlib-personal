import theorem.Linear.Family

/-! # Static requirements for rates

A strict spectral margin at a specified real rate is a finite matrix condition. It gives a
sound decay requirement at every rate, including zero and negative rates. The strict condition
is intentionally not claimed exact at a spectral boundary. -/

noncomputable section
namespace powerlib.Linear

open Matrix LinearSystems
open scoped RealInnerProductSpace

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Shifting the spectrum turns a requested rate into the hub's Hurwitz requirement. -/
def RateMargin (A : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : Prop := IsHurwitz (A + a • 1)

/-- A strict matrix margin supplies the specified rate by the generic energy estimate. -/
@[powerlib_foundation] theorem decay_of_rateMargin {A : Matrix (Fin n) (Fin n) ℝ} {a : ℝ}
    (h : RateMargin A a) : Flow.Decay (affineLinearVectorField A 0) 0 a := by
  obtain ⟨c⟩ := (nonempty_certificate_iff (A + a • 1)).mpr h
  obtain ⟨lo, hlo, hi, hhi, bounds⟩ := c.exists_energy_bounds
  have hmat : Aᵀ * c.P + c.P * A = -1 - (2 * a) • c.P := by
    have hl := c.lyapunov
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one] at hl
    have he : Aᵀ * c.P + c.P * A + (2 * a) • c.P = -1 := by
      convert hl using 1
      module
    exact eq_sub_of_add_eq he
  have hd : ∀ x : ℝⁿ, fderiv ℝ (c.energy 0) x (affineLinearVectorField A 0 x) ≤
      -(2 * a) * c.energy 0 x := by
    intro x
    rw [c.lie_energy_matrix, hmat, Matrix.sub_mulVec, dotProduct_sub,
      Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    simp only [Certificate.energy, sub_zero, inner_op]
    have : 0 ≤ WithLp.ofLp x ⬝ᵥ WithLp.ofLp x :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  refine ⟨Real.sqrt (hi / lo), fun t₀ t₁ φ hφ t ht => ?_⟩
  have hb := Flow.norm_bound_of_dissipation (e := 0) (rate := 2 * a) (c.energy_contDiff 0) hlo (hlo.trans_le hhi)
    (fun x => by simpa [Certificate.energy] using (bounds x).1)
    (fun x => by simpa [Certificate.energy] using (bounds x).2) hd hφ ht
  simpa only [show 2 * a / 2 = a by ring] using hb

end powerlib.Linear

namespace powerlib.Family

open Linear LinearSystems
variable {X Q : Type*} {n p : ℕ} {F : Family X Q n p} {plant : X → Plant n p}

/-- Every linear family consumes the matrix rate criterion through its generated denotation. -/
@[powerlib_foundation] theorem IsLinear.mem_den_decay_of_rateMargin (hF : F.IsLinear plant)
    {x : X} {a : ℝ} (h : RateMargin (plant x).A a) : x ∈ F.den (.flow (.decay a)) :=
  hF.mem_den_flow.mpr (decay_of_rateMargin h)

end powerlib.Family
