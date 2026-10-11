import theorem.PortHamiltonian
import theorem.Criteria.Hurwitz2

/-! # Series RLC loop as a linear port-Hamiltonian system

Model boundary.
* Circuit: one series loop of an inductor `L > 0`, a capacitor `C > 0`, a resistor `r ≥ 0`
  in series with the inductor branch, and an ideal voltage source `u` (one port).
  Lumped, linear, time-invariant, continuous time. No switching, PWM, PLL, delay,
  saturation, controller, or grid connection; stationary (not dq) coordinates.
* State order: `x = (φ, q)` with `φ = L i` the inductor flux linkage and `q = C v` the
  capacitor charge. Co-energy: `∇H = (φ / L, q / C) = (i, v)`.
* Hamiltonian `H(φ, q) = φ² / (2L) + q² / (2C)`.
* Kirchhoff equations (incoming-positive source power, `u · i` is the power delivered by
  the source into the loop): `φ̇ = u − r i − v`, `q̇ = i`. Collocated output `y = i`.
* pH data: `J = !![0, −1; 1, 0]`, `R = diag(r, 0)`, `g = (1, 0)ᵀ`, i.e. the
  `PortHamiltonian.Model` with `d = ![r, 0]`, `w = ![1/L, 1/C]`, `B = !![1; 0]`.
* Results: the pH field is exactly the Kirchhoff field; the energy is the circuit energy;
  passivity with storage `H` and Lyapunov stability of the zero-input origin (trajectory
  level, all `r ≥ 0`); exponential stability of the zero-input LTI model **iff** `r > 0`;
  and exponential decay of every zero-input pH trajectory on `[0, ∞)` when `r > 0`.

Source: work-sync `theory/T-ph.md` §1.6 (1.11) and §1.2 (energy balance (1.2)).
-/

noncomputable section
namespace powerlib.PH
open Matrix Set

/-- Physical parameters of the series RLC loop. -/
structure SeriesRLCParams where
  L : ℝ
  C : ℝ
  r : ℝ
  L_pos : 0 < L
  C_pos : 0 < C
  r_nonneg : 0 ≤ r

/-- The series RLC loop (T-ph (1.11)) as a constant-`J`, diagonal-damping,
diagonal-quadratic port-Hamiltonian model. State `(φ, q)`, one voltage port. -/
def seriesRLC (p : SeriesRLCParams) : PortHamiltonian.Model (Fin 2) (Fin 1) where
  J := !![0, -1; 1, 0]
  d := ![p.r, 0]
  w := ![1 / p.L, 1 / p.C]
  B := !![1; 0]
  skew := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  damping_nonneg := by
    intro i
    fin_cases i <;> simp [p.r_nonneg]
  weights_pos := by
    intro i
    fin_cases i <;> simp [p.L_pos, p.C_pos]

/-- Kirchhoff (KVL/KCL) right-hand side of the series loop:
`φ̇ = u − r (φ/L) − q/C`, `q̇ = φ/L`. -/
def seriesRLC_kirchhoffField (p : SeriesRLCParams) (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    Fin 2 → ℝ :=
  ![u 0 - p.r * (x 0 / p.L) - x 1 / p.C, x 0 / p.L]

/-- (1.11): the pH vector field `(J − R)∇H + g u` is exactly the Kirchhoff field. -/
@[powerlib_domain] theorem seriesRLC_field_eq_kirchhoff (p : SeriesRLCParams)
    (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    PortHamiltonian.field (seriesRLC p) x u = seriesRLC_kirchhoffField p x u := by
  ext i
  fin_cases i <;>
    simp [PortHamiltonian.field, PortHamiltonian.gradient, seriesRLC,
      seriesRLC_kirchhoffField, Matrix.diagonal_vec2, dotProduct,
      Fin.sum_univ_two] <;> ring

/-- The collocated output is the loop current `i = φ / L`. -/
@[powerlib_domain] theorem seriesRLC_output (p : SeriesRLCParams) (x : Fin 2 → ℝ) :
    PortHamiltonian.output (seriesRLC p) x = ![x 0 / p.L] := by
  ext i
  fin_cases i
  simp [PortHamiltonian.output, PortHamiltonian.gradient, seriesRLC, mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The pH energy is the circuit energy `φ²/(2L) + q²/(2C)`. -/
@[powerlib_foundation] theorem seriesRLC_energy (p : SeriesRLCParams) (x : Fin 2 → ℝ) :
    PortHamiltonian.energy (seriesRLC p) x = x 0 ^ 2 / (2 * p.L) + x 1 ^ 2 / (2 * p.C) := by
  simp [PortHamiltonian.energy, seriesRLC, Fin.sum_univ_two]
  ring

/-- Energy balance (1.2) for the loop: `Ḣ = u i − r i²`. -/
@[powerlib_domain] theorem seriesRLC_power_balance (p : SeriesRLCParams)
    (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    dotProduct (PortHamiltonian.gradient (seriesRLC p) x)
        (PortHamiltonian.field (seriesRLC p) x u) =
      u 0 * (x 0 / p.L) - p.r * (x 0 / p.L) ^ 2 := by
  rw [PortHamiltonian.power_balance]
  simp only [Passivity.supply, PortHamiltonian.system]
  rw [seriesRLC_output]
  simp only [PortHamiltonian.dampingPower, PortHamiltonian.gradient, seriesRLC,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Passivity of the series RLC loop with storage `H` (instance of
`PortHamiltonian.passiveWithStorage`). -/
@[powerlib_domain] theorem seriesRLC_passiveWithStorage (p : SeriesRLCParams) :
    Passivity.PassiveWithStorage (PortHamiltonian.system (seriesRLC p))
      (PortHamiltonian.energy (seriesRLC p)) :=
  PortHamiltonian.passiveWithStorage (seriesRLC p)

/-- Lyapunov stability of the zero-input origin for every `r ≥ 0`
(instance of `PortHamiltonian.lyapunovStable`). -/
@[powerlib_domain] theorem seriesRLC_lyapunovStable (p : SeriesRLCParams) :
    Passivity.LyapunovStable (PortHamiltonian.system (seriesRLC p)) :=
  PortHamiltonian.lyapunovStable (seriesRLC p)

/-- The state matrix `(J − R) Q` of the loop. -/
@[powerlib_foundation] theorem seriesRLC_stateMatrix (p : SeriesRLCParams) :
    PortHamiltonian.stateMatrix (seriesRLC p) = !![-(p.r / p.L), -(1 / p.C); 1 / p.L, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PortHamiltonian.stateMatrix, seriesRLC, Matrix.diagonal_vec2]
  all_goals ring

/-- Exponential stability of the zero-input series RLC LTI model holds **iff** `r > 0`
(lossless `r = 0` gives a centre). -/
@[powerlib_domain] theorem seriesRLC_exponentiallyStable_iff (p : SeriesRLCParams) :
    LTI.ExponentiallyStable (PortHamiltonian.linearModel (seriesRLC p)).autonomous ↔ 0 < p.r := by
  rw [LTI.exponentiallyStable_iff_isHurwitz]
  change LinearSystems.IsHurwitz (PortHamiltonian.stateMatrix (seriesRLC p)) ↔ _
  rw [seriesRLC_stateMatrix, Criteria.isHurwitz_fin_two_of_iff]
  have hL := p.L_pos
  have hC := p.C_pos
  have hdet : 0 < -(p.r / p.L) * 0 - -(1 / p.C) * (1 / p.L) := by
    have : 0 < 1 / p.C * (1 / p.L) := by positivity
    linarith
  constructor
  · rintro ⟨htr, -⟩
    have : 0 < p.r / p.L := by linarith
    exact (div_pos_iff_of_pos_right hL).mp this
  · intro hr
    refine ⟨?_, hdet⟩
    have : 0 < p.r / p.L := div_pos hr hL
    linarith

/-- `r > 0`: the zero-input series RLC LTI model is exponentially stable. -/
@[powerlib_domain] theorem seriesRLC_exponentiallyStable (p : SeriesRLCParams) (hr : 0 < p.r) :
    LTI.ExponentiallyStable (PortHamiltonian.linearModel (seriesRLC p)).autonomous :=
  (seriesRLC_exponentiallyStable_iff p).mpr hr

/-- `r > 0`: every zero-input trajectory of the pH loop on `[0, ∞)` decays exponentially
in the Euclidean norm of `(φ, q)`, with constants independent of the trajectory. -/
@[powerlib_domain] theorem seriesRLC_trajectory_exponential_decay (p : SeriesRLCParams)
    (hr : 0 < p.r) :
    ∃ K > 0, ∃ rate > 0, ∀ x : ℝ → (Fin 2 → ℝ),
      Passivity.IsTrajectory (PortHamiltonian.system (seriesRLC p)) (fun _ => 0) x →
        ∀ t, 0 ≤ t → ‖LTI.euclidean (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖LTI.euclidean (x 0)‖ := by
  obtain ⟨K, hK, rate, hrate, hbound⟩ := seriesRLC_exponentiallyStable p hr
  refine ⟨K, hK, rate, hrate, fun x hx t ht => ?_⟩
  have hresp := hbound (LTI.response (PortHamiltonian.linearModel (seriesRLC p)).autonomous (x 0))
    (LTI.response_solves _ _) t ht
  rw [PortHamiltonian.trajectory_eq_response (seriesRLC p) hx ht]
  simpa [PortHamiltonian.response, LTI.Model.response_autonomous] using hresp

end powerlib.PH
