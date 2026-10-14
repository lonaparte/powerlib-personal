import theorem.PDE.Partial

/-! # The transport equation `u_t + a u_x = 0` (foundation)

Existence by the travelling-wave formula and uniqueness along characteristics.

Model boundary.
* The one-dimensional transport equation `u_t + a u_x = 0` on the whole plane with constant speed
  `a`; differentiable initial profile `u₀`, C¹ solutions.
* A canonical PDE, not an engineering model: no model family; foundation results.

Source: work-sync `theory/T-pde-systems.md` §1.4.4 (transport equation).

Results.
* `transport_solution`: `u₀(x − at)` solves the transport equation for differentiable `u₀`.
* `transport_eq_initial`: uniqueness — every C¹ solution on the plane is constant along the
  characteristics, `u(x, t) = u(x − at, 0)` (through `const_along_segment`).
-/

noncomputable section
namespace powerlib.PDE
open Set

/-- `u₀(x - at)` solves the transport equation `u_t + a u_x = 0`. -/
@[powerlib_foundation] theorem transport_solution {u₀ u₀' : ℝ → ℝ} (a : ℝ)
    (hu : ∀ y, HasDerivAt u₀ (u₀' y) y) (q : ℝ × ℝ) :
    HasPartialsWithin (fun q => u₀ (q.1 - a * q.2)) (fun q => u₀' (q.1 - a * q.2))
      (fun q => -a * u₀' (q.1 - a * q.2)) univ q ∧
      -a * u₀' (q.1 - a * q.2) + a * u₀' (q.1 - a * q.2) = 0 := by
  refine ⟨?_, by ring⟩
  have hm : HasFDerivAt (fun q : ℝ × ℝ => q.1 - a * q.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ - a • ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    (hasFDerivAt_fst).sub ((hasFDerivAt_snd).const_mul a)
  have := (hu _).comp_hasFDerivAt q hm
  exact (this.congr_fderiv (by ext <;> simp <;> ring)).hasFDerivWithinAt

/-- Uniqueness for the transport equation: every C¹ solution of `u_t + a u_x = 0` on the
plane is constant along the characteristics, `u(x, t) = u(x - at, 0)`. -/
@[powerlib_foundation] theorem transport_eq_initial {u ux ut : ℝ × ℝ → ℝ} (a : ℝ)
    (hu : ∀ q, HasPartialsWithin u ux ut univ q) (hpde : ∀ q, ut q + a * ux q = 0)
    (x t : ℝ) : u (x, t) = u (x - a * t, 0) := by
  have hpt : ∀ s : ℝ, ((x - a * t, 0) : ℝ × ℝ) + s • (a, (1 : ℝ)) = (x - a * t + a * s, s) := by
    intro s; ext <;> simp; ring
  have hdir : ∀ s : ℝ, ux (((x - a * t, 0) : ℝ × ℝ) + s • (a, (1 : ℝ))) * a +
      ut (((x - a * t, 0) : ℝ × ℝ) + s • (a, (1 : ℝ))) * 1 = 0 := by
    intro s; linarith [hpde (((x - a * t, 0) : ℝ × ℝ) + s • (a, (1 : ℝ)))]
  rcases le_total 0 t with ht | ht
  · have := const_along_segment (U := u) (Ux := ux) (Ut := ut) (S := univ)
      (p₀ := (x - a * t, 0)) (d := (a, 1)) ht (fun _ _ => trivial) (fun s _ => hu _)
      (fun s _ => hdir s)
    rw [hpt, hpt] at this
    simpa using this
  · have := const_along_segment (U := u) (Ux := ux) (Ut := ut) (S := univ)
      (p₀ := (x - a * t, 0)) (d := (a, 1)) ht (fun _ _ => trivial) (fun s _ => hu _)
      (fun s _ => hdir s)
    rw [hpt, hpt] at this
    simpa using this.symm

end powerlib.PDE
