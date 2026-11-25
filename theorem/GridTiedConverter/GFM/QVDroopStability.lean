import theorem.GridTiedConverter.GFM.QVDroop
import theorem.Criteria.DroopJacobian
import theorem.Criteria.RootDerivativeSigns
import theorem.Dynamics.Linearization
import theorem.Spectral.Local

/-! # Grid-forming converter with Q–V droop: the exact stability boundary

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroop.lean`, unchanged: the reduced
  (quasi-static line) grid-forming converter with reactive-power–voltage droop, state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P(δ, E) − D Δω`, `Q̇_f = ω_q (Q(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, line `Z = R + jX` to a stiff grid `V ∠ 0`, export-positive powers,
  continuous time, autonomous, constant set-points. Physical range `M, ω_q, n_q, X, V > 0` and
  `c = E₀ + n_q Q_ref > 0`; `R` and `D` arbitrary unless stated. Excluded as there: the
  active-power filter, line dynamics, inner loops, virtual impedance (its counterpart is
  `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`), limiting, PLL, delay, PWM.
* Level: local exponential stability and instability of an equilibrium from the Jacobian
  (`QVDroop.hasFDerivAt_field`) and the cubic Routh–Hurwitz criterion, both directions; local
  asymptotic and Lyapunov stability off the fold and Hopf surfaces.

Source: study note GFM equilibrium counting (topic t6 (b): the ascending-branch and `E < 0`
observations, sampled there, decided here); the cubic Routh–Hurwitz criterion through the
droop-loop pattern (`theorem/Criteria/DroopJacobian.lean`);
converse linearization (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`). The
symbolic identities below (the Jacobian entries at a balanced point, the fold polynomial and its
relation to the droop quartic, the Hopf polynomial) were derived with exact computer algebra
(rational-function simplification) and are proved here by `field_simp`/`ring`.

Results.
* The generic laws used here are `theorem/Criteria/DroopJacobian.lean` (the Routh conditions of
  the pattern `Criteria.droopJacobian M D ω a b c k = [[0, 1, 0], [−a/M, −D/M, b/M],
  [ω c, 0, −ω k]]`: `Criteria.isHurwitz_droopJacobian_iff`,
  `Criteria.exists_root_re_pos_droopJacobian`, `Criteria.droopJacobian_routh_or_violation`) and
  `theorem/Criteria/RootDerivativeSigns.lean` (`Criteria.derivative_eval_neg_pos_of_two_roots`:
  `p(0) > 0`, at most two positive roots, `p(a) = p(b) = 0`, `0 < a < b` ⇒ `p'(a) < 0 < p'(b)`).
* The Q–V droop Jacobian is this pattern (`jacobian_eq_droopJacobian`) with the voltage-loop gain
  `K = 1 + n_q Q_E` (`gain`), the P–Q coupling `h = n_q P_E Q_δ` (`coupling`) and the Routh
  quantities `A = D + M ω_q K` (`routhTrace`), `C = K P_δ − h` (`routhFold`, `det J = −(ω_q/M) C`,
  `det_jacobian_eq_routhFold`) and `G = D (P_δ + D ω_q K + M ω_q² K²) + M ω_q h` (`routhHopf`):
  `isHurwitz_jacobian_iff`. On the physical branch `C = K P̃'` (`routhFold_eq_slope`).
* Explicit form at a balanced point with EMF `E ≠ 0` (`P = P_ref`, `Q = Q_ref + (E₀ − E)/n_q`):
  `E |Z|² K = n_q X E² + c |Z|²` (`gain_of_balance`), `n_q |Z|² P_δ = n_q X E² + |Z|² E − c |Z|²`
  (`Pδ_of_balance`), `E |Z|² P_E = R E² + |Z|² P_ref` (`PE_of_balance`),
  `|Z|² Q_δ = |Z|² P_ref − R E²` (`Qδ_of_balance`), so
  `E |Z|⁴ h = n_q (|Z|⁴ P_ref² − R² E⁴)` (`coupling_of_balance`); the Routh quantities are
  `E |Z|² A = tracePoly E` (`routhTrace_of_balance`), `E n_q |Z|² C = foldPoly E`
  (`routhFold_of_balance`) and `n_q E² |Z|⁴ G = hopfPoly E` (`routhHopf_of_balance`), with
  `foldPoly E = n_q² E⁴ + n_q X E³ + c |Z|² E − |Z|² (c² + n_q² P_ref²)` (independent of `V`) and
  explicit polynomials `tracePoly`, `hopfPoly`. The fold polynomial is the droop quartic's
  derivative at its roots: `2 foldPoly E = n_q² (E f'(E) − 2 f(E))` (`two_mul_foldPoly`).
  In the physical range it is strictly increasing on `E > 0` (`foldPoly_lt_foldPoly`) and negative
  at `0` (`foldPoly_zero_neg`), so the ascending branch is the EMF range above its unique positive
  root: at a physical equilibrium `P̃'(δ*) > 0 ⇔ foldPoly E* > 0` (`slope_pos_iff_foldPoly_pos`).
* Stable/saddle alternation: of two positive roots `E₁ < E₂` of the droop quartic,
  `foldPoly E₁ < 0 < foldPoly E₂` (`foldPoly_neg_pos_of_two_roots`); so of two physical
  equilibria of one parameter set the one with the larger EMF ascends (`slope_pos_of_lt_emf`).

Family and connection conclusions.
No new family: connection conclusions on `QVDroop.family`.
* `exact_locallyExponentiallyStable`: the local exponential translation of `QVDroop.family` is
  exact (converse linearization).
* `mem_den_locallyExponentiallyStable_iff` (every model with `M, ω_q > 0`): locally
  exponentially stable iff the selected point is an equilibrium with `A, C, G > 0`; in explicit
  form at an equilibrium with EMF `E* ≠ 0` (`mem_den_locallyExponentiallyStable_iff_emf`):
  iff `E* tracePoly E* > 0`, `E* foldPoly E* > 0` and `hopfPoly E* > 0`, both signs of `E*`;
  at a physical equilibrium through the slope (`mem_den_locallyExponentiallyStable_iff_slope`):
  iff `A > 0`, `P̃'(δ*) > 0` and `G > 0`.
* `mem_den_unstable_of_violation`: an equilibrium with `A < 0`, `C < 0` or `G < 0` is unstable
  (the descending branch `QVDroop.mem_den_unstable_of_slope_neg` is the case `C < 0`).
* `mem_den_unstable_of_lt_emf`: of two physical equilibria of one parameter set, the one with the
  smaller EMF descends and is unstable (through `QVDroop.mem_den_unstable_of_slope_neg`).
* Off the fold `C = 0` and the Hopf surface `G = 0` the local asymptotic and Lyapunov
  translations are exact as well: `mem_den_lyapunovStable_iff_of_ne`,
  `mem_den_locallyAsymptoticallyStable_iff_of_ne` (stable iff `A, C, G > 0`).
* The ascending branch: with a nonnegative coupling (`R² E*⁴ ≤ |Z|⁴ P_ref²`, e.g. a lossless line)
  and `D ≥ 0` an ascending equilibrium is locally exponentially stable when `D > 0` or the coupling
  is positive (`mem_den_locallyExponentiallyStable_of_slope_pos`); on a lossless line with `D > 0`
  local exponential stability is exactly the ascending branch
  (`mem_den_locallyExponentiallyStable_iff_slope_pos_of_lossless`).
* Refutations of the study's sampled observations (exact witnesses):
  `not_forall_mem_den_LES_of_slope_pos` — an ascending physical equilibrium with positive damping
  can be unstable (`lossyNoLoad`: `R = X = 1`, `D = 1/20`, no load, `P̃' = 2/3`, `G = −87/800`,
  `lossyNoLoad_mem_den_unstable`); `not_forall_not_mem_den_LES_of_emf_neg` — an equilibrium with
  `E < 0` in the physical parameter range can be locally exponentially stable (`negativeEMF`:
  `E* = −10`, `A = 43/5`, `C = 740`, `G = 1178/5`,
  `negativeEMF_mem_den_locallyExponentiallyStable`); every such equilibrium needs damping
  `D > M ω_q |K| > 0` (`not_mem_den_LES_of_emf_neg`).

Witness values (`lossyNoLoad`, `negativeEMF`) are exact rationals computed by `norm_num` from the
trigonometric values `cos 0 = 1` and `cos δ* = −5/13`, `sin δ* = −12/13`; floating-point
eigenvalues were used only as a labelled sanity check outside the repository.

The boundary, where the linearization decides nothing, is decided in two further modules: the
fold `C = 0` (a simple zero eigenvalue; unstable when the fold coefficient `𝔉 ≠ 0`) in
`theorem/GridTiedConverter/GFM/QVDroopFold.lean`, and the Hopf surface `G = 0, C > 0` (a purely
imaginary pair; the sign of the first Lyapunov coefficient, with the complete local asymptotic and
Lyapunov denotations) in `theorem/GridTiedConverter/GFM/QVDroopHopf.lean`. Located there, not
decided: the cusp set (`C = 0`, `𝔉 = 0`), the double zero `C = G = 0` and the Bautin set.
-/

noncomputable section
namespace powerlib.GFM
open Real Set Polynomial
open powerlib.Criteria (droopJacobian isHurwitz_droopJacobian_iff
  exists_root_re_pos_droopJacobian droopJacobian_routh_or_violation
  derivative_eval_neg_pos_of_two_roots)

namespace QVDroop

variable (q : QVDroop)

/-! ## The Routh quantities of the Q–V droop Jacobian -/

/-- The voltage-loop gain `K = 1 + n_q Q_E` at `(δ, E)`. -/
def gain (δ E : ℝ) : ℝ := 1 + q.nq * q.QE δ E

/-- The P–Q coupling `h = n_q P_E Q_δ` at `(δ, E)`. -/
def coupling (δ E : ℝ) : ℝ := q.nq * q.PE δ E * q.Qδ δ E

/-- The trace quantity `A = D + M ω_q K = −M tr J`. -/
def routhTrace (δ E : ℝ) : ℝ := q.D + q.M * q.ωq * q.gain δ E

/-- The fold quantity `C = K P_δ − h`, `det J = −(ω_q/M) C`. -/
def routhFold (δ E : ℝ) : ℝ := q.gain δ E * q.Pδ δ E - q.coupling δ E

/-- The Hopf quantity `G = D (P_δ + D ω_q K + M ω_q² K²) + M ω_q h = M² (a₂ a₁ − a₀)`. -/
def routhHopf (δ E : ℝ) : ℝ :=
  q.D * (q.Pδ δ E + q.D * q.ωq * q.gain δ E + q.M * q.ωq ^ 2 * q.gain δ E ^ 2) +
    q.M * q.ωq * q.coupling δ E

/-- The Q–V droop Jacobian is the droop-loop pattern with `a = P_δ`, `b = n_q P_E`, `c = Q_δ`,
`k = K`. -/
@[tmio M, powerlib_domain] theorem jacobian_eq_droopJacobian (δ E : ℝ) :
    q.jacobian δ E =
      droopJacobian q.M q.D q.ωq (q.Pδ δ E) (q.nq * q.PE δ E) (q.Qδ δ E) (q.gain δ E) :=
  rfl

/-- `det J = −(ω_q/M) C` (`QVDroop.det_jacobian`). -/
@[tmio M, powerlib_domain] theorem det_jacobian_eq_routhFold (δ E : ℝ) :
    (q.jacobian δ E).det = -(q.ωq / q.M) * q.routhFold δ E := by
  rw [det_jacobian]
  rfl

/-- **Routh–Hurwitz for the Q–V droop Jacobian.** For `M, ω_q > 0`:
`J` is Hurwitz iff `A > 0`, `C > 0` and `G > 0`. -/
@[tmio M, powerlib_domain] theorem isHurwitz_jacobian_iff (hM : 0 < q.M) (hω : 0 < q.ωq)
    (δ E : ℝ) :
    LinearSystems.IsHurwitz (q.jacobian δ E) ↔
      0 < q.routhTrace δ E ∧ 0 < q.routhFold δ E ∧ 0 < q.routhHopf δ E := by
  rw [jacobian_eq_droopJacobian]
  exact isHurwitz_droopJacobian_iff hM hω

/-- On the physical branch the fold quantity is the gain times the slope of the quasi-static
characteristic, `C = K P̃'` (`QVDroop.det_jacobian_eq_slope`). -/
@[tmio M, powerlib_domain] theorem routhFold_eq_slope (hM : q.M ≠ 0) (hω : q.ωq ≠ 0)
    (h2 : 0 < q.a2) (h0 : q.a0 < 0) (δ : ℝ) :
    q.routhFold δ (q.Eplus δ) = q.gain δ (q.Eplus δ) * deriv q.Ptilde δ := by
  have h := (q.det_jacobian_eq_routhFold δ (q.Eplus δ)).symm.trans
    (q.det_jacobian_eq_slope h2 h0 δ)
  have hc : q.ωq / q.M ≠ 0 := div_ne_zero hω hM
  have h' : q.ωq / q.M * (q.routhFold δ (q.Eplus δ) -
      q.gain δ (q.Eplus δ) * deriv q.Ptilde δ) = 0 := by
    simp only [gain] at h ⊢
    linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hc)

/-! ## Explicit form at a balanced point -/

/-- The cleared balance: `n_q E V cos δ = n_q E² + X E − n_q R P_ref − X c`,
`n_q E V sin δ = R E + n_q X P_ref − R c` (`c = E₀ + n_q Q_ref`; `balance_iff`). -/
@[tmio M, powerlib_domain] private theorem balance_cleared (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0)
    {δ E : ℝ} (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    q.nq * (E * q.V * cos δ) =
        q.nq * E ^ 2 + q.X * E - q.nq * q.R * q.Pref - q.X * (q.E0 + q.nq * q.Qref) ∧
      q.nq * (E * q.V * sin δ) =
        q.R * E + q.nq * q.X * q.Pref - q.R * (q.E0 + q.nq * q.Qref) := by
  obtain ⟨hc, hs⟩ := (q.balance_iff hZ δ E).mp h
  rw [hc, hs]
  simp only [u, w, β, ρ, γ, κ, q0]
  constructor <;> field_simp <;> ring

/-- At a balanced point with EMF `E ≠ 0`: `E |Z|² K = n_q X E² + c |Z|²`. -/
@[tmio M, powerlib_domain] theorem gain_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0)
    {δ E : ℝ} (hE : E ≠ 0) (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    q.gain δ E = (q.nq * q.X * E ^ 2 + (q.E0 + q.nq * q.Qref) * q.zsq) / (E * q.zsq) := by
  obtain ⟨hc, hs⟩ := q.balance_cleared hZ hnq h
  have hQ : q.QE δ E * q.zsq = q.X * (2 * E - q.V * cos δ) - q.R * (q.V * sin δ) :=
    div_mul_cancel₀ _ hZ
  rw [eq_div_iff (mul_ne_zero hE hZ),
    show q.gain δ E * (E * q.zsq) = E * q.zsq + q.nq * E * (q.QE δ E * q.zsq) by
      unfold gain; ring, hQ]
  simp only [zsq]
  linear_combination (-q.X) * hc - q.R * hs

/-- At a balanced point: `n_q |Z|² P_δ = n_q X E² + |Z|² E − c |Z|²`. -/
@[tmio M, powerlib_domain] theorem Pδ_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0) {δ E : ℝ}
    (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    q.Pδ δ E = (q.nq * q.X * E ^ 2 + q.zsq * E - (q.E0 + q.nq * q.Qref) * q.zsq) /
      (q.nq * q.zsq) := by
  obtain ⟨hc, hs⟩ := q.balance_cleared hZ hnq h
  have hP : q.Pδ δ E * q.zsq = q.R * (E * q.V * sin δ) + q.X * (E * q.V * cos δ) :=
    div_mul_cancel₀ _ hZ
  rw [eq_div_iff (mul_ne_zero hnq hZ),
    show q.Pδ δ E * (q.nq * q.zsq) = q.nq * (q.Pδ δ E * q.zsq) by ring, hP]
  simp only [zsq]
  linear_combination q.X * hc + q.R * hs

/-- At a balanced point with EMF `E ≠ 0`: `E |Z|² P_E = R E² + |Z|² P_ref`. -/
@[tmio M, powerlib_domain] theorem PE_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0) {δ E : ℝ}
    (hE : E ≠ 0) (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    q.PE δ E = (q.R * E ^ 2 + q.zsq * q.Pref) / (E * q.zsq) := by
  obtain ⟨hc, hs⟩ := q.balance_cleared hZ hnq h
  have hP : q.PE δ E * q.zsq = q.R * (2 * E - q.V * cos δ) + q.X * (q.V * sin δ) :=
    div_mul_cancel₀ _ hZ
  rw [eq_div_iff (mul_ne_zero hE hZ)]
  have key : q.nq * (q.PE δ E * (E * q.zsq) - (q.R * E ^ 2 + q.zsq * q.Pref)) = 0 := by
    rw [show q.PE δ E * (E * q.zsq) = E * (q.PE δ E * q.zsq) by ring, hP]
    simp only [zsq]
    linear_combination (-q.R) * hc + q.X * hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hnq)

/-- At a balanced point: `|Z|² Q_δ = |Z|² P_ref − R E²`. -/
@[tmio M, powerlib_domain] theorem Qδ_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0) {δ E : ℝ}
    (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    q.Qδ δ E = (q.zsq * q.Pref - q.R * E ^ 2) / q.zsq := by
  obtain ⟨hc, hs⟩ := q.balance_cleared hZ hnq h
  have hQ : q.Qδ δ E * q.zsq = q.X * (E * q.V * sin δ) - q.R * (E * q.V * cos δ) :=
    div_mul_cancel₀ _ hZ
  rw [eq_div_iff hZ]
  have key : q.nq * (q.Qδ δ E * q.zsq - (q.zsq * q.Pref - q.R * E ^ 2)) = 0 := by
    rw [hQ]
    simp only [zsq]
    linear_combination q.X * hs - q.R * hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hnq)

/-- At a balanced point with EMF `E ≠ 0`: `E |Z|⁴ h = n_q (|Z|⁴ P_ref² − R² E⁴)`. -/
@[tmio M, powerlib_domain] theorem coupling_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0)
    {δ E : ℝ} (hE : E ≠ 0) (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    q.coupling δ E =
      q.nq * (q.zsq ^ 2 * q.Pref ^ 2 - q.R ^ 2 * E ^ 4) / (E * q.zsq ^ 2) := by
  rw [coupling, q.PE_of_balance hZ hnq hE h, q.Qδ_of_balance hZ hnq h]
  field_simp
  ring

/-- `c = E₀ + n_q Q_ref`, the no-load droop level. -/
def level : ℝ := q.E0 + q.nq * q.Qref

/-- The trace polynomial `D E |Z|² + M ω_q (n_q X E² + c |Z|²)`. -/
def tracePoly (E : ℝ) : ℝ := q.D * E * q.zsq + q.M * q.ωq * (q.nq * q.X * E ^ 2 + q.level * q.zsq)

/-- The fold polynomial `n_q² E⁴ + n_q X E³ + c |Z|² E − |Z|² (c² + n_q² P_ref²)`. -/
def foldPoly (E : ℝ) : ℝ :=
  q.nq ^ 2 * E ^ 4 + q.nq * q.X * E ^ 3 + q.level * q.zsq * E -
    q.zsq * (q.level ^ 2 + q.nq ^ 2 * q.Pref ^ 2)

/-- The Hopf polynomial `n_q E² |Z|⁴ G` at a balanced point. -/
def hopfPoly (E : ℝ) : ℝ :=
  q.D * E ^ 2 * q.zsq * (q.nq * q.X * E ^ 2 + q.zsq * E - q.level * q.zsq) +
    q.D ^ 2 * q.ωq * q.nq * E * q.zsq * (q.nq * q.X * E ^ 2 + q.level * q.zsq) +
    q.D * q.M * q.ωq ^ 2 * q.nq * (q.nq * q.X * E ^ 2 + q.level * q.zsq) ^ 2 +
    q.M * q.ωq * q.nq ^ 2 * E * (q.zsq ^ 2 * q.Pref ^ 2 - q.R ^ 2 * E ^ 4)

/-- At a balanced point with EMF `E ≠ 0`: `E |Z|² A = tracePoly E`. -/
@[tmio M, powerlib_domain] theorem routhTrace_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0)
    {δ E : ℝ} (hE : E ≠ 0) (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    E * q.zsq * q.routhTrace δ E = q.tracePoly E := by
  rw [routhTrace, q.gain_of_balance hZ hnq hE h, tracePoly, level]
  field_simp

/-- At a balanced point with EMF `E ≠ 0`: `E n_q |Z|² C = foldPoly E`. -/
@[tmio M, powerlib_domain] theorem routhFold_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0)
    {δ E : ℝ} (hE : E ≠ 0) (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    E * q.nq * q.zsq * q.routhFold δ E = q.foldPoly E := by
  rw [routhFold, q.gain_of_balance hZ hnq hE h, q.Pδ_of_balance hZ hnq h,
    q.coupling_of_balance hZ hnq hE h, foldPoly, level]
  simp only [zsq] at hZ ⊢
  field_simp
  ring

/-- At a balanced point with EMF `E ≠ 0`: `n_q E² |Z|⁴ G = hopfPoly E`. -/
@[tmio M, powerlib_domain] theorem routhHopf_of_balance (hZ : q.zsq ≠ 0) (hnq : q.nq ≠ 0)
    {δ E : ℝ} (hE : E ≠ 0) (h : q.P δ E = q.Pref ∧ q.Q δ E = q.qOf E) :
    q.nq * E ^ 2 * q.zsq ^ 2 * q.routhHopf δ E = q.hopfPoly E := by
  rw [routhHopf, q.gain_of_balance hZ hnq hE h, q.Pδ_of_balance hZ hnq h,
    q.coupling_of_balance hZ hnq hE h, hopfPoly, level]
  field_simp

/-- **The fold polynomial is the droop quartic's derivative at its roots**:
`2 foldPoly E = n_q² (E f'(E) − 2 f(E))` (`n_q ≠ 0`). -/
@[tmio M, powerlib_domain] theorem two_mul_foldPoly (hnq : q.nq ≠ 0) (E : ℝ) :
    2 * q.foldPoly E =
      q.nq ^ 2 * (E * (derivative q.quartic).eval E - 2 * q.quartic.eval E) := by
  rw [quartic_eq]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero, mul_one,
    foldPoly, level, β, ρ, γ, κ, q0, zsq]
  field_simp
  push_cast
  ring

/-- In the physical range the fold polynomial is strictly increasing on `E > 0`. -/
@[tmio M, powerlib_domain] theorem foldPoly_lt_foldPoly (hnq : 0 < q.nq) (hX : 0 < q.X)
    (hc : 0 < q.level) {E₁ E₂ : ℝ} (h₁ : 0 ≤ E₁) (h₁₂ : E₁ < E₂) :
    q.foldPoly E₁ < q.foldPoly E₂ := by
  have hZ := q.zsq_pos hX.ne'
  have h₂ : 0 < E₂ := h₁.trans_lt h₁₂
  have d1 : E₁ ^ 3 ≤ E₂ ^ 3 := pow_le_pow_left₀ h₁ h₁₂.le 3
  have d2 : E₁ ^ 4 ≤ E₂ ^ 4 := pow_le_pow_left₀ h₁ h₁₂.le 4
  unfold foldPoly
  nlinarith [mul_le_mul_of_nonneg_left d1 (mul_pos hnq hX).le,
    mul_le_mul_of_nonneg_left d2 (sq_nonneg q.nq), mul_pos (mul_pos hc hZ) (sub_pos.mpr h₁₂)]

/-- In the physical range the fold polynomial is negative at `E = 0`. -/
@[tmio M, powerlib_domain] theorem foldPoly_zero_neg (hX : 0 < q.X) (hc : 0 < q.level) :
    q.foldPoly 0 < 0 := by
  have hZ := q.zsq_pos hX.ne'
  unfold foldPoly
  nlinarith [mul_pos hZ (add_pos_of_pos_of_nonneg (pow_pos hc 2)
    (mul_nonneg (sq_nonneg q.nq) (sq_nonneg q.Pref)))]

/-! ## Connection conclusions -/

@[tmio TM, powerlib_domain] private theorem mem_den_flow {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.q.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field) (pt := Model.point)
    family_isAutonomous

@[tmio M, powerlib_domain] private theorem fderiv_at_point (m : Model) :
    fderiv ℝ m.q.field m.point = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jacobian := by
  rw [m.q.fderiv_field]
  simp [Model.point, Model.jacobian]

/-- **The local exponential translation is exact.** A Q–V droop model is locally exponentially
stable at its selected point exactly when the point is an equilibrium with a Hurwitz Jacobian
(`Model.Stable`; converse linearization, `Spectral.local_exact_of_jacobian`). -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_exact_of_jacobian (fun m : Model => m.jacobian)
    (fun m => m.q.contDiff_field.comp (contDiff_id.add contDiff_const)) (fun m => ?_)
    fun m => ?_
  · change fderiv ℝ (fun z => m.q.field (z + m.point)) 0 = _
    rw [fderiv_comp_add_right, zero_add, fderiv_at_point]
  · simp [Model.Stable, Model.field]

/-- **The exact stability boundary.** For `M, ω_q > 0` a Q–V droop model is locally
exponentially stable at its selected point iff the point is an equilibrium and the Routh
quantities at its angle and EMF are positive: `A = D + M ω_q K > 0`, `C = K P_δ − h > 0`,
`G = D (P_δ + D ω_q K + M ω_q² K²) + M ω_q h > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow, Set.mem_ofPred_eq, ← m.q.isHurwitz_jacobian_iff hM hω]
  exact Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ m.q.contDiff_field
    (fderiv_at_point m)

/-- **A strict violation is unstable.** For `M, ω_q > 0` an equilibrium with `A < 0`, `C < 0` or
`G < 0` is unstable (a characteristic root in the open right half plane). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_violation (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (h : m.q.routhTrace m.δ (m.q.emf m.Qf) < 0 ∨ m.q.routhFold m.δ (m.q.emf m.Qf) < 0 ∨
      m.q.routhHopf m.δ (m.q.emf m.Qf) < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow]
  obtain ⟨s, hs, hre⟩ := exists_root_re_pos_droopJacobian (M := m.q.M) (D := m.q.D)
    (ω := m.q.ωq) (a := m.q.Pδ m.δ (m.q.emf m.Qf)) (b := m.q.nq * m.q.PE m.δ (m.q.emf m.Qf))
    (c := m.q.Qδ m.δ (m.q.emf m.Qf)) (k := m.q.gain m.δ (m.q.emf m.Qf)) hM hω h
  exact Dynamics.unstable_of_characteristic_root_re_pos m.jacobian m.q.contDiff_field heq
    (fderiv_at_point m) hs hre

/-- **Lyapunov stability off the fold and the Hopf surface.** For `M, ω_q > 0`, `C ≠ 0` and
`G ≠ 0` at the selected point, the model is Lyapunov stable iff the point is an equilibrium with
`A, C, G > 0` (then locally exponentially stable; otherwise a strict violation, unstable). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_ne (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) ≠ 0)
    (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  unfold powerlib.TMIO.Statement at hles ⊢
  constructor
  · intro hl
    have heq : m.q.field m.point = 0 :=
      Dynamics.isEquilibrium_of_lyapunovStable m.q.contDiff_field (mem_den_flow.mp hl)
    rcases droopJacobian_routh_or_violation hM hω hC hG with h | h
    · exact ⟨heq, h⟩
    · exact absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
        (mem_den_unstable_of_violation m hM hω heq h))
  · intro h
    exact Spectral.den_locallyExponentiallyStable_subset_lyapunovStable (hles.mpr h)

/-- **Local asymptotic stability off the fold and the Hopf surface**: for `M, ω_q > 0`, `C ≠ 0`
and `G ≠ 0`, iff an equilibrium with `A, C, G > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_ne (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) ≠ 0)
    (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  have hly := mem_den_lyapunovStable_iff_of_ne m hM hω hC hG
  unfold powerlib.TMIO.Statement at hles hly ⊢
  exact ⟨fun h => hly.mp (Spectral.den_las_subset_lyapunovStable h),
    fun h => Spectral.den_locallyExponentiallyStable_subset_las (hles.mpr h)⟩

/-- The balance at an equilibrium: `P = P_ref` and `Q = Q_ref + (E₀ − E)/n_q`. -/
@[tmio M, powerlib_domain] private theorem balance_of_eq {m : Model} (hM : m.q.M ≠ 0)
    (hω : m.q.ωq ≠ 0) (hnq : m.q.nq ≠ 0) (heq : m.q.field m.point = 0) :
    m.q.P m.δ (m.q.emf m.Qf) = m.q.Pref ∧
      m.q.Q m.δ (m.q.emf m.Qf) = m.q.qOf (m.q.emf m.Qf) := by
  obtain ⟨-, h1, h2⟩ := (m.q.field_eq_zero_iff hM hω m.point).mp heq
  simp only [Model.point, Dynamics.mk3_zero, Dynamics.mk3_two] at h1 h2
  exact ⟨h1, by rw [h2, m.q.qOf_emf hnq]⟩

/-- **The exact boundary in explicit form.** In the physical range (`M, ω_q, n_q > 0`, `X ≠ 0`)
an equilibrium with EMF `E* ≠ 0` is locally exponentially stable iff `E* tracePoly E* > 0`,
`E* foldPoly E* > 0` and `hopfPoly E* > 0` (polynomials in `E*` and the parameters; for
`E* > 0` the first two read `tracePoly E* > 0`, `foldPoly E* > 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_emf (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : m.q.X ≠ 0)
    (heq : m.q.field m.point = 0) (hE : m.q.emf m.Qf ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | 0 < m.q.emf m.Qf * m.q.tracePoly (m.q.emf m.Qf) ∧
        0 < m.q.emf m.Qf * m.q.foldPoly (m.q.emf m.Qf) ∧ 0 < m.q.hopfPoly (m.q.emf m.Qf)}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  unfold powerlib.TMIO.Statement at hles ⊢
  rw [hles, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  have hZ := m.q.zsq_pos hX
  have hb := balance_of_eq hM.ne' hω.ne' hnq.ne' heq
  set E := m.q.emf m.Qf
  have hA := m.q.routhTrace_of_balance hZ.ne' hnq.ne' hE hb
  have hC := m.q.routhFold_of_balance hZ.ne' hnq.ne' hE hb
  have hG := m.q.routhHopf_of_balance hZ.ne' hnq.ne' hE hb
  have hE2 : 0 < E ^ 2 := by positivity
  have k1 : ∀ r : ℝ, 0 < r ↔ 0 < E * (E * m.q.zsq * r) := fun r => by
    rw [show E * (E * m.q.zsq * r) = (E ^ 2 * m.q.zsq) * r by ring]
    exact (mul_pos_iff_of_pos_left (mul_pos hE2 hZ)).symm
  have k2 : ∀ r : ℝ, 0 < r ↔ 0 < E * (E * m.q.nq * m.q.zsq * r) := fun r => by
    rw [show E * (E * m.q.nq * m.q.zsq * r) = (E ^ 2 * m.q.nq * m.q.zsq) * r by ring]
    exact (mul_pos_iff_of_pos_left (mul_pos (mul_pos hE2 hnq) hZ)).symm
  have k3 : ∀ r : ℝ, 0 < r ↔ 0 < m.q.nq * E ^ 2 * m.q.zsq ^ 2 * r := fun r =>
    (mul_pos_iff_of_pos_left (by positivity)).symm
  rw [k1 (m.q.routhTrace _ _), k2 (m.q.routhFold _ _), k3 (m.q.routhHopf _ _), hA, hC, hG]
  exact ⟨fun h => h.2, fun h => ⟨heq, h⟩⟩

/-- **The exact boundary through the slope.** In the physical range (`M, ω_q, n_q, X > 0`,
`E₀ + n_q Q_ref > 0`) an equilibrium with a positive EMF is locally exponentially stable iff
`A > 0`, the quasi-static characteristic ascends, `P̃'(δ*) > 0`, and `G > 0`
(`routhFold_eq_slope`, `K > 0` on the physical branch). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_slope (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧ 0 < deriv m.q.Ptilde m.δ ∧
        0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  unfold powerlib.TMIO.Statement at hles ⊢
  rw [hles, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  have h2 := m.q.a2_pos hnq hX
  have h0 := m.q.a0_neg hc
  have hEq : m.q.emf m.Qf = m.q.Eplus m.δ := by
    simpa [Model.point] using m.q.emf_eq_Eplus hM.ne' hω.ne' h2 h0 heq (by simpa [Model.point])
  have hK : 0 < m.q.gain m.δ (m.q.Eplus m.δ) := (m.q.one_add_nq_QE_Eplus h2 h0 m.δ).2
  rw [hEq, m.q.routhFold_eq_slope hM.ne' hω.ne' h2 h0, mul_pos_iff_of_pos_left hK]
  exact ⟨fun h => h.2, fun h => ⟨heq, h⟩⟩

/-- **The slope sign in explicit form.** At a physical equilibrium the quasi-static
characteristic ascends iff the fold polynomial is positive at the EMF: `P̃'(δ*) > 0 ⇔
foldPoly E* > 0` (an EMF above the unique positive root of `foldPoly`, `foldPoly_lt_foldPoly`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem slope_pos_iff_foldPoly_pos (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) :
    0 < deriv m.q.Ptilde m.δ ↔ 0 < m.q.foldPoly (m.q.emf m.Qf) := by
  have h2 := m.q.a2_pos hnq hX
  have h0 := m.q.a0_neg hc
  have hZ := m.q.zsq_pos hX.ne'
  have hb := balance_of_eq hM.ne' hω.ne' hnq.ne' heq
  have hC := m.q.routhFold_of_balance hZ.ne' hnq.ne' hE.ne' hb
  have hEq : m.q.emf m.Qf = m.q.Eplus m.δ := by
    simpa [Model.point] using m.q.emf_eq_Eplus hM.ne' hω.ne' h2 h0 heq (by simpa [Model.point])
  have hK : 0 < m.q.gain m.δ (m.q.emf m.Qf) := by
    rw [hEq]; exact (m.q.one_add_nq_QE_Eplus h2 h0 m.δ).2
  have hCs : m.q.routhFold m.δ (m.q.emf m.Qf) = m.q.gain m.δ (m.q.emf m.Qf) *
      deriv m.q.Ptilde m.δ := by
    rw [hEq]; exact m.q.routhFold_eq_slope hM.ne' hω.ne' h2 h0 m.δ
  rw [← hC, hCs, mul_pos_iff_of_pos_left (mul_pos (mul_pos hE hnq) hZ),
    mul_pos_iff_of_pos_left hK]

/-- **The fold polynomial at two physical roots.** In the physical range the smaller of two
positive roots `E₁ < E₂` of the droop quartic has `foldPoly E₁ < 0`, the larger `foldPoly E₂ > 0`
(`two_mul_foldPoly`, `derivative_eval_neg_pos_of_two_roots`). -/
@[tmio M, powerlib_domain] theorem foldPoly_neg_pos_of_two_roots (hnq : 0 < q.nq) (hX : 0 < q.X)
    (hc : 0 < q.E0 + q.nq * q.Qref) {E₁ E₂ : ℝ} (h₁ : 0 < E₁) (h₁₂ : E₁ < E₂)
    (hr₁ : q.quartic.IsRoot E₁) (hr₂ : q.quartic.IsRoot E₂) :
    q.foldPoly E₁ < 0 ∧ 0 < q.foldPoly E₂ := by
  obtain ⟨d₁, d₂⟩ := derivative_eval_neg_pos_of_two_roots (q.eval_zero_quartic_pos hnq hX hc)
    (q.countP_pos_roots_le_two hnq hX) h₁ h₁₂ hr₁ hr₂
  have e₁ := q.two_mul_foldPoly hnq.ne' E₁
  have e₂ := q.two_mul_foldPoly hnq.ne' E₂
  rw [hr₁.eq_zero, mul_zero, sub_zero] at e₁
  rw [hr₂.eq_zero, mul_zero, sub_zero] at e₂
  have hn2 : 0 < q.nq ^ 2 := pow_pos hnq 2
  constructor
  · nlinarith [mul_pos hn2 h₁, mul_neg_of_pos_of_neg (mul_pos hn2 h₁) d₁]
  · nlinarith [mul_pos (mul_pos hn2 (h₁.trans h₁₂)) d₂]

/-- At a physical equilibrium the fold polynomial is the slope scaled by a positive factor:
`foldPoly E* = E* n_q |Z|² K P̃'(δ*)`, `K > 0`. -/
@[tmio M, powerlib_domain] private theorem foldPoly_eq_slope (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) :
    ∃ k > 0, m.q.foldPoly (m.q.emf m.Qf) = k * deriv m.q.Ptilde m.δ := by
  have h2 := m.q.a2_pos hnq hX
  have h0 := m.q.a0_neg hc
  have hZ := m.q.zsq_pos hX.ne'
  have hb := balance_of_eq hM.ne' hω.ne' hnq.ne' heq
  have hC := m.q.routhFold_of_balance hZ.ne' hnq.ne' hE.ne' hb
  have hEq : m.q.emf m.Qf = m.q.Eplus m.δ := by
    simpa [Model.point] using m.q.emf_eq_Eplus hM.ne' hω.ne' h2 h0 heq (by simpa [Model.point])
  have hK : 0 < m.q.gain m.δ (m.q.emf m.Qf) := by
    rw [hEq]; exact (m.q.one_add_nq_QE_Eplus h2 h0 m.δ).2
  have hCs : m.q.routhFold m.δ (m.q.emf m.Qf) = m.q.gain m.δ (m.q.emf m.Qf) *
      deriv m.q.Ptilde m.δ := by
    rw [hEq]; exact m.q.routhFold_eq_slope hM.ne' hω.ne' h2 h0 m.δ
  refine ⟨m.q.emf m.Qf * m.q.nq * m.q.zsq * m.q.gain m.δ (m.q.emf m.Qf), by positivity, ?_⟩
  rw [← hC, hCs]
  ring

/-- **Two physical equilibria: the smaller EMF descends.** If a second equilibrium of the same
parameters has a larger positive EMF, the selected equilibrium lies on the descending branch,
`P̃'(δ*) < 0`, and is unstable (`foldPoly_neg_pos_of_two_roots`,
`QVDroop.mem_den_unstable_of_slope_neg`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_lt_emf (m m' : Model) (hq : m'.q = m.q)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (heq' : m'.q.field m'.point = 0) (hE : 0 < m.q.emf m.Qf)
    (hlt : m.q.emf m.Qf < m'.q.emf m'.Qf) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hZ := (m.q.zsq_pos hX.ne').ne'
  have hr := m.q.quartic_isRoot_of_field_eq_zero hM.ne' hω.ne' hnq.ne' hZ heq
  have hr' := m'.q.quartic_isRoot_of_field_eq_zero (hq ▸ hM.ne') (hq ▸ hω.ne') (hq ▸ hnq.ne')
    (hq ▸ hZ) heq'
  rw [hq] at hr' hlt
  simp only [Model.point, Dynamics.mk3_two] at hr hr'
  obtain ⟨hf, -⟩ := m.q.foldPoly_neg_pos_of_two_roots hnq hX hc hE hlt hr hr'
  obtain ⟨k, hk, hfk⟩ := foldPoly_eq_slope m hM hω hnq hX hc heq hE
  refine mem_den_unstable_of_slope_neg m hM hω hnq hX hc heq hE ?_
  rw [hfk] at hf
  exact neg_of_mul_neg_right hf hk.le

/-- **Two physical equilibria: the larger EMF ascends.** If a second equilibrium of the same
parameters has a smaller positive EMF, the selected equilibrium lies on the ascending branch,
`P̃'(δ*) > 0` (then it is locally exponentially stable iff `A > 0` and `G > 0`,
`mem_den_locallyExponentiallyStable_iff_slope`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem slope_pos_of_lt_emf (m m' : Model) (hq : m'.q = m.q)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (heq' : m'.q.field m'.point = 0) (hE' : 0 < m'.q.emf m'.Qf)
    (hlt : m'.q.emf m'.Qf < m.q.emf m.Qf) :
    0 < deriv m.q.Ptilde m.δ := by
  have hZ := (m.q.zsq_pos hX.ne').ne'
  have hr := m.q.quartic_isRoot_of_field_eq_zero hM.ne' hω.ne' hnq.ne' hZ heq
  have hr' := m'.q.quartic_isRoot_of_field_eq_zero (hq ▸ hM.ne') (hq ▸ hω.ne') (hq ▸ hnq.ne')
    (hq ▸ hZ) heq'
  rw [hq] at hr' hlt hE'
  simp only [Model.point, Dynamics.mk3_two] at hr hr'
  obtain ⟨-, hf⟩ := m.q.foldPoly_neg_pos_of_two_roots hnq hX hc hE' hlt hr' hr
  obtain ⟨k, hk, hfk⟩ := foldPoly_eq_slope m hM hω hnq hX hc heq (hE'.trans hlt)
  rw [hfk] at hf
  exact pos_of_mul_pos_right hf hk.le

/-- **The ascending branch with a nonnegative coupling.** In the physical range, with `D ≥ 0`,
an ascending equilibrium (`P̃'(δ*) > 0`) whose P–Q coupling is nonnegative,
`R² E*⁴ ≤ |Z|⁴ P_ref²` (`coupling_of_balance`), is locally exponentially stable when `D > 0` or the
coupling is positive. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_slope_pos (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) (hD : 0 ≤ m.q.D) (hs : 0 < deriv m.q.Ptilde m.δ)
    (hh : m.q.R ^ 2 * m.q.emf m.Qf ^ 4 ≤ m.q.zsq ^ 2 * m.q.Pref ^ 2)
    (hpos : 0 < m.q.D ∨ m.q.R ^ 2 * m.q.emf m.Qf ^ 4 < m.q.zsq ^ 2 * m.q.Pref ^ 2) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have hiff := mem_den_locallyExponentiallyStable_iff_slope m hM hω hnq hX hc heq hE
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  unfold powerlib.TMIO.Statement at hiff hles ⊢
  have h2 := m.q.a2_pos hnq hX
  have h0 := m.q.a0_neg hc
  have hZ := m.q.zsq_pos hX.ne'
  have hb := balance_of_eq hM.ne' hω.ne' hnq.ne' heq
  set E := m.q.emf m.Qf with hEdef
  have hEq : E = m.q.Eplus m.δ := by
    simpa [Model.point] using m.q.emf_eq_Eplus hM.ne' hω.ne' h2 h0 heq (by simpa [Model.point])
  have hK : 0 < m.q.gain m.δ E := hEq ▸ (m.q.one_add_nq_QE_Eplus h2 h0 m.δ).2
  have hCs : m.q.routhFold m.δ E = m.q.gain m.δ E * deriv m.q.Ptilde m.δ := by
    rw [hEq]; exact m.q.routhFold_eq_slope hM.ne' hω.ne' h2 h0 m.δ
  have hcpl := m.q.coupling_of_balance hZ.ne' hnq.ne' hE.ne' hb
  have hh0 : 0 ≤ m.q.coupling m.δ E := by
    rw [hcpl]; exact div_nonneg (mul_nonneg hnq.le (by linarith)) (by positivity)
  have hC : 0 < m.q.routhFold m.δ E := by rw [hCs]; exact mul_pos hK hs
  have hPδ : 0 < m.q.Pδ m.δ E := by
    have e : m.q.gain m.δ E * m.q.Pδ m.δ E = m.q.routhFold m.δ E + m.q.coupling m.δ E := by
      unfold routhFold; ring
    exact pos_of_mul_pos_right (by rw [e]; linarith) hK.le
  have hrest : 0 < m.q.Pδ m.δ E + m.q.D * m.q.ωq * m.q.gain m.δ E +
      m.q.M * m.q.ωq ^ 2 * m.q.gain m.δ E ^ 2 := by
    have := mul_nonneg (mul_nonneg hD hω.le) hK.le
    have := mul_nonneg (mul_nonneg hM.le (sq_nonneg m.q.ωq)) (sq_nonneg (m.q.gain m.δ E))
    linarith
  have hG : 0 < m.q.routhHopf m.δ E := by
    unfold routhHopf
    rcases hpos with hD' | hR
    · nlinarith [mul_pos hD' hrest, mul_nonneg (mul_pos hM hω).le hh0]
    · have hh1 : 0 < m.q.coupling m.δ E := by
        rw [hcpl]; exact div_pos (mul_pos hnq (by linarith)) (by positivity)
      nlinarith [mul_nonneg hD hrest.le, mul_pos (mul_pos hM hω) hh1]
  exact hles.mpr ⟨heq, add_pos_of_nonneg_of_pos hD (mul_pos (mul_pos hM hω) hK), hC, hG⟩

/-- **A lossless line: the ascending branch is exactly the stable one.** In the physical range
with `R = 0` and `D > 0`, an equilibrium with a positive EMF is locally exponentially stable iff
the quasi-static characteristic ascends, `P̃'(δ*) > 0` (the coupling `n_q P_ref²/E*` is
nonnegative; the descending side is `QVDroop.mem_den_unstable_of_slope_neg`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_slope_pos_of_lossless
    (m : Model) (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (hR : m.q.R = 0) (hD : 0 < m.q.D)
    (heq : m.q.field m.point = 0) (hE : 0 < m.q.emf m.Qf) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | 0 < deriv m.q.Ptilde m.δ}) := by
  have hiff := mem_den_locallyExponentiallyStable_iff_slope m hM hω hnq hX hc heq hE
  unfold powerlib.TMIO.Statement at hiff ⊢
  constructor
  · intro h
    exact (hiff.mp h).2.1
  · intro hs
    have h := mem_den_locallyExponentiallyStable_of_slope_pos m hM hω hnq hX hc heq hE hD.le hs
      (by rw [hR, zero_pow two_ne_zero, zero_mul]; positivity) (Or.inl hD)
    exact h

/-- **Equilibria with `E < 0` need damping.** In the physical range (`M, ω_q, n_q, X > 0`,
`E₀ + n_q Q_ref > 0`) the voltage-loop gain at a negative EMF is negative,
`K = (n_q X E*² + c |Z|²)/(E* |Z|²) < 0` (`gain_of_balance`), so `A = D + M ω_q K > 0` needs
`D > M ω_q |K| > 0`: without positive damping no equilibrium with `E < 0` is locally
exponentially stable. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_LES_of_emf_neg (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (hE : m.q.emf m.Qf < 0)
    (hD : m.q.D ≤ -(m.q.M * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) ∨ m.q.D ≤ 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  unfold powerlib.TMIO.Statement at hles ⊢
  intro h
  obtain ⟨heq, hA, -, -⟩ := hles.mp h
  have hZ := m.q.zsq_pos hX.ne'
  have hb := balance_of_eq hM.ne' hω.ne' hnq.ne' heq
  have hK : m.q.gain m.δ (m.q.emf m.Qf) < 0 := by
    rw [m.q.gain_of_balance hZ.ne' hnq.ne' hE.ne hb]
    exact div_neg_of_pos_of_neg (by positivity) (mul_neg_of_neg_of_pos hE hZ)
  have hMK := mul_neg_of_pos_of_neg (mul_pos hM hω) hK
  unfold routhTrace at hA
  rcases hD with hD | hD <;> linarith

/-! ## Witnesses -/

/-- A lossy no-load point: `M = ω_q = n_q = E₀ = V = R = X = 1`, `D = 1/20`,
`Q_ref = P_ref = 0`, at `δ* = 0`, `Q_f* = 0` (EMF `E* = 1`, zero current). -/
def lossyNoLoad : Model := ⟨⟨1, 1 / 20, 1, 1, 1, 0, 0, 1, 1, 1⟩, 0, 0⟩

@[tmio M, powerlib_domain] private theorem lossyNoLoad_emf : lossyNoLoad.q.emf lossyNoLoad.Qf = 1 :=
  by norm_num [lossyNoLoad, emf]

@[tmio M, powerlib_domain] private theorem lossyNoLoad_eq :
    lossyNoLoad.q.field lossyNoLoad.point = 0 := by
  apply Dynamics.state3_ext <;>
    simp [lossyNoLoad, Model.point, field, P_eq, Q_eq, emf, zsq]

@[tmio M, powerlib_domain] private theorem lossyNoLoad_values :
    lossyNoLoad.q.gain lossyNoLoad.δ 1 = 3 / 2 ∧ lossyNoLoad.q.routhFold lossyNoLoad.δ 1 = 1 ∧
      lossyNoLoad.q.routhHopf lossyNoLoad.δ 1 = -87 / 800 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [lossyNoLoad, gain, routhFold, routhHopf, coupling, Pδ, PE, Qδ, QE, zsq]

/-- The lossy no-load point ascends: `P̃'(0) = C/K = 2/3`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem lossyNoLoad_slope :
    deriv lossyNoLoad.q.Ptilde lossyNoLoad.δ = 2 / 3 := by
  have h2 : 0 < lossyNoLoad.q.a2 := lossyNoLoad.q.a2_pos (by norm_num [lossyNoLoad])
    (by norm_num [lossyNoLoad])
  have h0 : lossyNoLoad.q.a0 < 0 := lossyNoLoad.q.a0_neg (by norm_num [lossyNoLoad])
  have hEq : (1 : ℝ) = lossyNoLoad.q.Eplus lossyNoLoad.δ := by
    have := lossyNoLoad.q.emf_eq_Eplus (by norm_num [lossyNoLoad]) (by norm_num [lossyNoLoad])
      h2 h0 lossyNoLoad_eq (by norm_num [lossyNoLoad, Model.point, emf])
    simpa [lossyNoLoad_emf, Model.point] using this
  have h := lossyNoLoad.q.routhFold_eq_slope (by norm_num [lossyNoLoad])
    (by norm_num [lossyNoLoad]) h2 h0 lossyNoLoad.δ
  rw [← hEq, lossyNoLoad_values.1, lossyNoLoad_values.2.1] at h
  linarith

/-- The lossy no-load point is unstable: `G = −87/800 < 0` (a complex pair in the right half
plane), although it ascends with positive damping. -/
@[tmio TM, powerlib_domain] theorem lossyNoLoad_mem_den_unstable :
    connection% (lossyNoLoad ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable_of_violation lossyNoLoad (by norm_num [lossyNoLoad])
    (by norm_num [lossyNoLoad]) lossyNoLoad_eq (Or.inr (Or.inr ?_))
  rw [lossyNoLoad_emf, lossyNoLoad_values.2.2]
  norm_num

/-- **Refutation: the ascending branch is not always stable.** The study's sampled observation
(ascending equilibria were Hurwitz) fails in the physical range, even with positive damping: the
lossy no-load point (`lossyNoLoad`) has `M, D, ω_q, n_q, X, V > 0`, `E₀ + n_q Q_ref > 0`,
`E* = 1 > 0`, `P̃'(δ*) = 2/3 > 0` and is unstable. -/
@[tmio TM, powerlib_domain] theorem not_forall_mem_den_LES_of_slope_pos :
    connection% (¬ ∀ m : Model, 0 < m.q.M → 0 < m.q.D → 0 < m.q.ωq → 0 < m.q.nq → 0 < m.q.X →
      0 < m.q.V → 0 < m.q.E0 + m.q.nq * m.q.Qref → m.q.field m.point = 0 →
      0 < m.q.emf m.Qf → 0 < deriv m.q.Ptilde m.δ →
      m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hl := h lossyNoLoad (by norm_num [lossyNoLoad]) (by norm_num [lossyNoLoad])
    (by norm_num [lossyNoLoad]) (by norm_num [lossyNoLoad]) (by norm_num [lossyNoLoad])
    (by norm_num [lossyNoLoad]) (by norm_num [lossyNoLoad]) lossyNoLoad_eq
    (by rw [lossyNoLoad_emf]; norm_num) (by rw [lossyNoLoad_slope]; norm_num)
  exact Spectral.not_mem_den_lyapunovStable_of_unstable lossyNoLoad_mem_den_unstable
    (Spectral.den_locallyExponentiallyStable_subset_lyapunovStable hl)

/-- An equilibrium with a negative EMF: `M = n_q = X = 1`, `D = 10`, `ω_q = 1/10`, `E₀ = 40`,
`Q_ref = 0`, `P_ref = 120`, `V = 13`, `R = 0`, at `cos δ* = −5/13`, `sin δ* = −12/13`
(`δ* = −arccos(−5/13)`), `Q_f* = 50` (EMF `E* = −10`). -/
def negativeEMF : Model := ⟨⟨1, 10, 1 / 10, 1, 40, 0, 120, 13, 0, 1⟩, -arccos (-5 / 13), 50⟩

@[tmio M, powerlib_domain] private theorem negativeEMF_trig :
    cos negativeEMF.δ = -5 / 13 ∧ sin negativeEMF.δ = -12 / 13 := by
  have hs : sin (arccos (-5 / 13 : ℝ)) = 12 / 13 := by
    rw [sin_arccos, show (1 : ℝ) - (-5 / 13) ^ 2 = (12 / 13) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_⟩
  · rw [show negativeEMF.δ = -arccos (-5 / 13) from rfl, cos_neg,
      cos_arccos (by norm_num) (by norm_num)]
  · rw [show negativeEMF.δ = -arccos (-5 / 13) from rfl, sin_neg, hs]
    norm_num

@[tmio M, powerlib_domain] private theorem negativeEMF_emf :
    negativeEMF.q.emf negativeEMF.Qf = -10 := by
  norm_num [negativeEMF, emf]

@[tmio M, powerlib_domain] private theorem negativeEMF_eq :
    negativeEMF.q.field negativeEMF.point = 0 := by
  obtain ⟨hc, hs⟩ := negativeEMF_trig
  apply Dynamics.state3_ext <;>
    simp [Model.point, field, P_eq, Q_eq, emf, zsq, hc, hs] <;> norm_num [negativeEMF]

/-- The negative-EMF equilibrium is locally exponentially stable: `A = 43/5`, `C = 740`,
`G = 1178/5`. -/
@[tmio TM, powerlib_domain] theorem negativeEMF_mem_den_locallyExponentiallyStable :
    connection% (negativeEMF ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have hles := mem_den_locallyExponentiallyStable_iff negativeEMF (by norm_num [negativeEMF])
    (by norm_num [negativeEMF])
  unfold powerlib.TMIO.Statement at hles ⊢
  obtain ⟨hc, hs⟩ := negativeEMF_trig
  refine hles.mpr ⟨negativeEMF_eq, ?_, ?_, ?_⟩ <;>
    rw [negativeEMF_emf] <;>
    simp only [routhTrace, routhFold, routhHopf, gain, coupling, Pδ, PE, Qδ, QE, zsq, hc,
      hs] <;> norm_num [negativeEMF]

/-- **Refutation: equilibria with `E < 0` can be stable.** The study's sampled observation (no
`E < 0` equilibrium was Hurwitz) fails in the physical parameter range: `negativeEMF` has
`M, ω_q, n_q, X, V > 0`, `E₀ + n_q Q_ref > 0`, an equilibrium with `E* = −10` and is locally
exponentially stable (it needs `D > M ω_q |K|`, `not_mem_den_LES_of_emf_neg`). -/
@[tmio TM, powerlib_domain] theorem not_forall_not_mem_den_LES_of_emf_neg :
    connection% (¬ ∀ m : Model, 0 < m.q.M → 0 < m.q.ωq → 0 < m.q.nq → 0 < m.q.X →
      0 < m.q.V → 0 < m.q.E0 + m.q.nq * m.q.Qref → m.q.field m.point = 0 →
      m.q.emf m.Qf < 0 → m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have hl := negativeEMF_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hl ⊢
  intro h
  exact h negativeEMF (by norm_num [negativeEMF]) (by norm_num [negativeEMF])
    (by norm_num [negativeEMF]) (by norm_num [negativeEMF]) (by norm_num [negativeEMF])
    (by norm_num [negativeEMF]) negativeEMF_eq (by rw [negativeEMF_emf]; norm_num) hl

end QVDroop

end powerlib.GFM
