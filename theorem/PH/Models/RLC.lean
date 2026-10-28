import theorem.PH.Composition
import theorem.Criteria.Hurwitz2

/-! # Series RLC loop as a linear port-Hamiltonian system

The series RLC loop as a linear port-Hamiltonian plant: passivity, Lyapunov stability, exponential
stability iff `r > 0`, and the complex normal modes of an LC pair.

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
* pH data: `J = !![0, −1; 1, 0]`, `R = diag(r, 0)`, `g = (1, 0)ᵀ`, i.e. the diagonal data
  `DiagonalPH` with `d = ![r, 0]`, `w = ![1/L, 1/C]`, `B = !![1; 0]`.

Source: work-sync `theory/T-ph.md` §1.6 (1.11) and §1.2 (energy balance (1.2));
`theory/T-invariant-coordinates.md` §1.4 (normal modes).

Results.
* `seriesRLCPH_field`, `seriesRLC_field_eq_kirchhoff` — the plant's field is exactly the
  Kirchhoff field; `seriesRLC_power_balance` — energy balance `Ḣ = u i − r i²`;
  `seriesRLCPH_isHurwitz_iff` — the loop is Hurwitz iff `r > 0`.
* Complex normal modes of an LC pair (T-invariant-coordinates §1.4): `a± = √L Ī ± j √C V̄` give
  `|a₊|² + |a₋|² = 2(L|I|² + C|V|²) = 2η₊` (`normalMode_sum`) and
  `|a₊|² − |a₋|² = 4 √(LC) Im(Ī V̄*)` (`normalMode_diff`); identities for arbitrary phasors,
  foundation.

Family and connection conclusions.
* The loop is a member of the linear port-Hamiltonian family `Port.PortHamiltonian.family`
  (`theorem/Port/PortHamiltonian.lean`) through `seriesRLCPH p : Port.PortHamiltonian 2 1`
  (states and port numbered in the order above); the system map is the plant's port system and
  the sentences are read at the origin, the unforced operating point.
* Connection conclusions: passivity and Lyapunov stability for every `r ≥ 0`
  (`seriesRLCPH_mem_den_passive`, `seriesRLCPH_mem_den_lyapunovStable`); every attractive
  sentence and sampled contraction hold **iff** `r > 0` (`seriesRLCPH_mem_den_iff`); global
  exponential stability and a positive decay rate when `r > 0`
  (`seriesRLCPH_mem_den_globallyExponentiallyStable`, `seriesRLCPH_exists_decay`); and for the
  lossless loop `r = 0`, conservation of `H` and failure of local asymptotic stability
  (`seriesRLCPH_mem_den_conservative`, `seriesRLCPH_not_mem_den_locallyAsymptoticallyStable`).
  The field, output, energy, power balance and state-matrix identities are static evidence.
* The lossless case `r = 0` with `L = C = 1` is the loop `losslessLC` of
  `theorem/PH/Observability.lean` (same `J`, `R = 0`, `g`, `Q = I`), the counterexample to
  "passive and observable ⇒ asymptotically stable".

Correction (T-invariant-coordinates §1.4).
* The difference of the normal-mode energies is `|a₊|² − |a₋|² = 4√(L_f C_f) Im(Ī V̄*)`; the
  note's "∝ Im(L_f Ī V̄*)" has the wrong scale factor (`L_f` instead of `√(L_f C_f)`,
  `normalMode_diff_ne_note`). The note also labels `|a₊|² + |a₋|² = 2η₊` "conserved": by
  `normalMode_sum` this is `4H` with `H = ½L|I|² + ½C|V|²`, so it is conserved exactly when `H`
  is, i.e. (energy balance `Ḣ = P_src − P_conv`, the dq LC model of
  `theorem/PH/Models/Instances.lean`) only while the port power vanishes, not in general.
-/

noncomputable section
namespace powerlib.PH.Models
open Matrix Set LinearSystems

/-- Physical parameters of the series RLC loop. -/
structure SeriesRLCParams where
  L : ℝ
  C : ℝ
  r : ℝ
  L_pos : 0 < L
  C_pos : 0 < C
  r_nonneg : 0 ≤ r

/-- The series RLC loop (T-ph (1.11)) as constant-`J`, diagonal-damping, diagonal-quadratic
port-Hamiltonian data. State `(φ, q)`, one voltage port. -/
def seriesRLC (p : SeriesRLCParams) : DiagonalPH (Fin 2) (Fin 1) where
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

/-- (1.11): the pH vector field `(J − R)∇H + g u` is exactly the Kirchhoff field.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem seriesRLC_field_eq_kirchhoff (p : SeriesRLCParams)
    (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    (seriesRLC p).field x u = seriesRLC_kirchhoffField p x u := by
  ext i
  fin_cases i <;>
    simp [DiagonalPH.field, DiagonalPH.gradient, seriesRLC,
      seriesRLC_kirchhoffField, Matrix.diagonal_vec2, dotProduct,
      Fin.sum_univ_two] <;> ring

/-- The collocated output is the loop current `i = φ / L`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem seriesRLC_output (p : SeriesRLCParams) (x : Fin 2 → ℝ) :
    (seriesRLC p).output x = ![x 0 / p.L] := by
  ext i
  fin_cases i
  simp [DiagonalPH.output, DiagonalPH.gradient, seriesRLC, mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The pH energy is the circuit energy `φ²/(2L) + q²/(2C)`. -/
@[powerlib_foundation] theorem seriesRLC_energy (p : SeriesRLCParams) (x : Fin 2 → ℝ) :
    (seriesRLC p).energy x = x 0 ^ 2 / (2 * p.L) + x 1 ^ 2 / (2 * p.C) := by
  simp [DiagonalPH.energy, seriesRLC, Fin.sum_univ_two]
  ring

/-- Energy balance (1.2) for the loop: `Ḣ = u i − r i²`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem seriesRLC_power_balance (p : SeriesRLCParams)
    (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    (seriesRLC p).gradient x ⬝ᵥ (seriesRLC p).field x u =
      u 0 * (x 0 / p.L) - p.r * (x 0 / p.L) ^ 2 := by
  rw [DiagonalPH.power_balance, DiagonalPH.supply, seriesRLC_output]
  simp only [DiagonalPH.dampingPower, DiagonalPH.gradient, seriesRLC, dotProduct,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-! ## The loop as a linear port-Hamiltonian plant -/

/-- The series RLC loop as a linear port-Hamiltonian plant, states `(φ, q)` and the source port
numbered in order. -/
def seriesRLCPH (p : SeriesRLCParams) : Port.PortHamiltonian 2 1 :=
  (seriesRLC p).toPH (Equiv.refl _) (Equiv.refl _)

/-- The state field of the plant is the Kirchhoff field.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem seriesRLCPH_field (p : SeriesRLCParams)
    (x : EuclideanSpace ℝ (Fin 2)) (u : Fin 1 → ℝ) :
    WithLp.ofLp ((seriesRLCPH p).plant.system.field x u) =
      seriesRLC_kirchhoffField p (WithLp.ofLp x) u := by
  rw [seriesRLCPH, DiagonalPH.toPH_field, seriesRLC_field_eq_kirchhoff]
  rfl

/-- The state matrix `(J − R) Q` of the loop.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem seriesRLCPH_stateMatrix (p : SeriesRLCParams) :
    (seriesRLCPH p).plant.A = !![-(p.r / p.L), -(1 / p.C); 1 / p.L, 0] := by
  rw [seriesRLCPH, DiagonalPH.toPH_plant]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DiagonalPH.stateMatrix, seriesRLC, Matrix.diagonal_vec2]
  all_goals ring

/-- The loop is Hurwitz **iff** it is resistive. -/
@[powerlib_foundation] theorem seriesRLCPH_isHurwitz_iff (p : SeriesRLCParams) :
    IsHurwitz (seriesRLCPH p).plant.A ↔ 0 < p.r := by
  rw [seriesRLCPH_stateMatrix, Criteria.isHurwitz_fin_two_of_iff]
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

/-- Passivity of the series RLC loop; the storage is `H` (`toPH_storage`). -/
@[tmio TM]
@[powerlib_domain] theorem seriesRLCPH_mem_den_passive (p : SeriesRLCParams) :
    connection% (seriesRLCPH p ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- Lyapunov stability of the zero-input origin for every `r ≥ 0`. -/
@[tmio TM]
@[powerlib_domain] theorem seriesRLCPH_mem_den_lyapunovStable (p : SeriesRLCParams) :
    connection% (seriesRLCPH p ∈ Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

/-- Every attractive sentence (local or global, asymptotic or exponential) and sampled
contraction hold for the zero-input loop **iff** `r > 0` (the lossless loop `r = 0` is a
centre). -/
@[tmio TM]
@[powerlib_domain] theorem seriesRLCPH_mem_den_iff (p : SeriesRLCParams) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (seriesRLCPH p ∈ Port.PortHamiltonian.family.den (.flow P) ↔ 0 < p.r) := by
  unfold powerlib.TMIO.Statement
  rw [Port.PortHamiltonian.family_isLinear.den_hurwitz hP]
  exact seriesRLCPH_isHurwitz_iff p

/-- `r > 0`: the zero-input loop is globally exponentially stable. -/
@[tmio TM]
@[powerlib_domain] theorem seriesRLCPH_mem_den_globallyExponentiallyStable (p : SeriesRLCParams)
    (hr : 0 < p.r) :
    connection% (seriesRLCPH p ∈
      Port.PortHamiltonian.family.den (.flow .globallyExponentiallyStable)) :=
  (seriesRLCPH_mem_den_iff p (P := .globallyExponentiallyStable) (Or.inl trivial)).mpr hr

/-- `r > 0`: every zero-input solution segment decays at one positive exponential rate, with one
constant for all segments. -/
@[tmio TM]
@[powerlib_domain] theorem seriesRLCPH_exists_decay (p : SeriesRLCParams) (hr : 0 < p.r) :
    connection% (∃ a : ℝ, 0 < a ∧
      seriesRLCPH p ∈ Port.PortHamiltonian.family.den (.flow (.decay a))) := by
  unfold powerlib.TMIO.Statement
  have h := seriesRLCPH_mem_den_globallyExponentiallyStable p hr
  unfold powerlib.TMIO.Statement at h
  rw [Port.PortHamiltonian.family_isLinear.mem_den_flow] at h
  obtain ⟨a, ha, hd⟩ := Flow.GloballyExponentiallyStable.exists_decay h
  exact ⟨a, ha, Port.PortHamiltonian.family_isLinear.mem_den_flow.mpr hd⟩

/-- The lossless loop `r = 0` conserves its energy `H`. -/
@[tmio TM]
@[powerlib_domain] theorem seriesRLCPH_mem_den_conservative (p : SeriesRLCParams)
    (hr : p.r = 0) :
    connection% (seriesRLCPH p ∈ Port.PortHamiltonian.family.den (.flow .conservative)) := by
  refine mem_den_conservative_of_lossless _ (DiagonalPH.toPH_R_eq_zero _ _ _ ?_)
  ext i
  fin_cases i <;> simp [seriesRLC, hr]

/-- The lossless loop `r = 0` is not locally asymptotically stable. -/
@[tmio TM]
@[powerlib_domain] theorem seriesRLCPH_not_mem_den_locallyAsymptoticallyStable
    (p : SeriesRLCParams) (hr : p.r = 0) :
    connection% (seriesRLCPH p ∉
      Port.PortHamiltonian.family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have := (seriesRLCPH_mem_den_iff p (P := .locallyAsymptoticallyStable) (Or.inl trivial)).mp h
  rw [hr] at this
  exact lt_irrefl 0 this

/-! ## Complex normal modes of an LC pair -/

/-- `a± = √L Ī ± j √C V̄`: `|a₊|² + |a₋|² = 2(L|I|² + C|V|²)`. -/
@[powerlib_foundation] theorem normalMode_sum {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (I V : ℂ) :
    Complex.normSq (Real.sqrt L * I + Complex.I * (Real.sqrt C * V)) +
        Complex.normSq (Real.sqrt L * I - Complex.I * (Real.sqrt C * V)) =
      2 * (L * Complex.normSq I + C * Complex.normSq V) := by
  have hl := Real.sq_sqrt hL
  have hc := Real.sq_sqrt hC
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  linear_combination (2 * (I.re ^ 2 + I.im ^ 2)) * hl + (2 * (V.re ^ 2 + V.im ^ 2)) * hc

/-- `|a₊|² − |a₋|² = 4 √(LC) Im(Ī V̄*)`. -/
@[powerlib_foundation] theorem normalMode_diff {L C : ℝ} (hL : 0 ≤ L) (I V : ℂ) :
    Complex.normSq (Real.sqrt L * I + Complex.I * (Real.sqrt C * V)) -
        Complex.normSq (Real.sqrt L * I - Complex.I * (Real.sqrt C * V)) =
      4 * Real.sqrt (L * C) * (I * (starRingEnd ℂ) V).im := by
  rw [Real.sqrt_mul hL]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The note's scale factor is wrong: with `L ≠ C` (both positive) and `Im(Ī V̄*) ≠ 0`,
`|a₊|² − |a₋|²` is not `4 L Im(Ī V̄*)`. -/
@[powerlib_foundation] theorem normalMode_diff_ne_note {L C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (hLC : L ≠ C) {I V : ℂ} (hIV : (I * (starRingEnd ℂ) V).im ≠ 0) :
    Complex.normSq (Real.sqrt L * I + Complex.I * (Real.sqrt C * V)) -
        Complex.normSq (Real.sqrt L * I - Complex.I * (Real.sqrt C * V)) ≠
      4 * L * (I * (starRingEnd ℂ) V).im := by
  rw [normalMode_diff hL.le]
  intro h
  have h1 : Real.sqrt (L * C) = L := by
    have := mul_right_cancel₀ hIV (by linarith : 4 * Real.sqrt (L * C) * _ = 4 * L * _)
    linarith
  have h2 : Real.sqrt (L * C) ^ 2 = L ^ 2 := by rw [h1]
  rw [Real.sq_sqrt (mul_nonneg hL.le hC.le), sq] at h2
  exact hLC (mul_left_cancel₀ hL.ne' h2).symm

end powerlib.PH.Models
