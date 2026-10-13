import theorem.Criteria.Hurwitz2
import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Basin
import theorem.Linear.Family
import theorem.TMIO.ClaimElab

/-! # Single-input single-output plant helpers and spectral families (foundation)

Shared helpers for the converter current-loop, DC-link and feedforward modules
(`theorem/CurrentControl/`, `theorem/DCLink/`). Nothing here describes a physical system.

* `transfer_fin_one`, `transfer_fin_two`: closed forms of `Linear.transfer` for one- and
  two-state single-input single-output plants `⟨A, B, C, D⟩` (one port), off the
  characteristic roots. These are plain resolvent computations (adjugate of a 1×1 / 2×2
  matrix).
* `negOutput`, `transfer_negOutput`: reversing the output sign of a plant negates its transfer
  matrix. With the output read as a port current, this is the `Y^IN = −Y^OUT` translation
  between the IN-positive and OUT-positive current conventions (work-sync
  `theory/T-gfl-impedance.md` §1.4 / §2.2, `conventions.md` §D8).
* `tendsto_equilibrium`: under a constant input with an equilibrium `e`, every forward-complete
  solution of a plant with a Hurwitz state matrix converges to `e` (the hub's global asymptotic
  stability, `Linear.globallyAsymptoticallyStable_of_isHurwitz`, about the shifted
  equilibrium). It replaces the former `isTrajectory_sub_equilibrium`,
  `tendsto_of_exponentiallyStable` and `tendsto_equilibrium` on the deleted `LTI` models.

## Spectral families

Many model families of the converter modules are decided by the spectrum of one state matrix: a
static parameter condition makes it Hurwitz, another places a characteristic root in the open
right half plane. `Spectral` packages that shape once, for an arbitrary type `X` of complete
systems, with the generic requirement language `Spectral.Requirement` (`stable`, `unstable`)
whose satisfaction is supplied by the static conditions `S` and `U` of the model:
* `Spectral.linearFamily plant S U` reads every complete system as the port system of its linear
  plant (`Family.IsLinear`). Its translation sends the attractive sentences, sampled contraction
  and Lyapunov stability to `stable`, instability to `unstable`, and decay at a prescribed rate,
  conservation and passivity — which these conditions do not decide — to the whole (inconsistent)
  language: unavailable coverage, not a usable translation. `linear_chain_le_semantics` proves
  every translation sound when `S` gives a Hurwitz matrix and `U` a right-half-plane root;
  `linear_exact` proves the attractive and contractive translations exact when `S` is equivalent
  to the Hurwitz property.
* `Spectral.localFamily field S U` reads every complete system as the autonomous field `field x`
  (already translated so that the selected operating point is the origin). Its translation sends
  the local sentences to `stable`, instability to `unstable`, passivity to nothing and the global
  sentences, decay rates, sampled contraction and conservation to the whole language.
  `local_chain_le_semantics` proves every translation sound when `S` gives local exponential
  stability and `U` instability of the field at the origin; `local_exact_passive` is exact.
  `local_exact_locallyExponentiallyStable` proves the local exponential translation exact when
  `S` is equivalent to local exponential stability at the origin, and `local_exact_of_jacobian`
  when, for `C¹` fields, `S` is equivalent to an equilibrium at the origin with a Hurwitz Jacobian
  (converse linearization, `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`). A
  stability condition that also fixes physical signs (positive inertia, capacitance, …) is not of
  this form; such families publish the exact membership within the physical range and a
  witness that the translation itself is not exact.

Inexactness passes along translations (`Spectral.not_exact_of_den_subset`): if a sound translation
of `s` is not exact and a sentence `s'` with the same translation has a larger denotation, the
translation of `s'` is not exact either; for local families a boundary witness of the local
exponential translation is one of the local asymptotic and Lyapunov translations
(`Spectral.local_not_exact_of_not_exact_les`).

These are generic statements about arbitrary families of the two shapes: foundation results. A
model module instantiates them and publishes its conclusions as connection statements.

## Degenerate linearizations (generic)

Where the Jacobian is not Hurwitz the linearization does not decide local asymptotic or Lyapunov
stability. Generic tools for the degenerate members of model families (any `C¹` field
`f : ℝⁿ → ℝⁿ`, continuous time, the library's segment semantics):
* `Dynamics.exists_forward_of_lyapunovStable`: near a Lyapunov stable point of a `C¹` field every
  state has a solution on the whole forward ray (smooth cutoff, LeanForControl's Picard–Lindelöf,
  first sphere hit).
* `Dynamics.not_localAsymptoticStable_of_lie_nonpos`: a function that does not increase along the
  field near the point and takes values below its value at the point arbitrarily close to it
  rules out local asymptotic stability (conserved energies, fold points with a monotone
  coordinate, dissipated energies with a lower nearby level).
* `Dynamics.not_localAsymptoticStable_of_equilibria`: accumulating equilibria rule it out.
* `Dynamics.lyapunovStable_of_inner_nonpos`: a quadratic energy `‖T x‖²` (`T` injective linear)
  that does not increase gives Lyapunov stability, also with a singular Jacobian.
* `Dynamics.unstable_of_chetaev`: Chetaev's instability theorem in its classical (non-exponential)
  form, for degenerate points where LeanForControl's exponential Chetaev criterion does not apply;
  `Dynamics.unstable_of_lie_nonpos_of_lie_pos`: its variant on the sublevel set of a dissipated
  energy below the level of the point (fold points of dissipative mechanical systems).

Source: standard state-space algebra, used by work-sync `theory/T-gfl-control.md` §1.4,
`theory/T-gfl-impedance.md` §1.4–§1.5, `theory/T-voltage-feedforward.md` §2.2,
`theory/T-vsc-dc-voltage-control.md` §1.4.
-/

noncomputable section
namespace powerlib.CurrentControl
open Matrix Filter Linear LinearSystems
open scoped Topology

/-- Transfer function of a one-state SISO plant `⟨[a], [b], [c], [d]⟩`:
`c b / (s − a) + d` for `s ≠ a`. -/
@[powerlib_foundation] theorem transfer_fin_one (a b c d : ℝ) {s : ℂ} (hs : s - a ≠ 0) :
    transfer (⟨!![a], !![b], !![c], !![d]⟩ : Plant 1 1) s 0 0 =
      (c : ℂ) * b / (s - a) + d := by
  simp [transfer, characteristicMatrix, Matrix.mul_apply]
  field_simp

/-- Characteristic determinant of a 2×2 state matrix in the literal form `!![a, b; c, d]`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_of (a b c d : ℝ) (s : ℂ) :
    (characteristicMatrix !![a, b; c, d] s).det = (s - a) * (s - d) - (b : ℂ) * c := by
  simp [characteristicMatrix, Matrix.det_fin_two]

/-- Transfer function of a two-state SISO plant, off the characteristic roots. -/
@[powerlib_foundation] theorem transfer_fin_two (a b c d b1 b2 c1 c2 d0 : ℝ) {s : ℂ}
    (hs : (s - a) * (s - d) - (b : ℂ) * c ≠ 0) :
    transfer (⟨!![a, b; c, d], !![b1; b2], !![c1, c2], !![d0]⟩ : Plant 2 1) s 0 0 =
      ((c1 : ℂ) * ((s - d) * b1 + b * b2) + c2 * (c * b1 + (s - a) * b2)) /
        ((s - a) * (s - d) - b * c) + d0 := by
  simp only [transfer, Matrix.inv_def, Ring.inverse_eq_inv', det_characteristicMatrix_of]
  simp [characteristicMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

section Sign

variable {n p : ℕ}

/-- The same plant with the output (and feedthrough) sign reversed. -/
def negOutput (m : Plant n p) : Plant n p := ⟨m.A, m.B, -m.C, -m.D⟩

/-- Reversing the output sign negates the transfer matrix. Read with the output as a port
current: `Y^IN(s) = −Y^OUT(s)`. -/
@[powerlib_foundation] theorem transfer_negOutput (m : Plant n p) (s : ℂ) :
    transfer (negOutput m) s = -transfer m s := by
  simp only [transfer, negOutput, complexify_neg, Matrix.neg_mul, neg_add]

@[powerlib_foundation] theorem negOutput_negOutput (m : Plant n p) :
    negOutput (negOutput m) = m := by
  simp [negOutput]

end Sign

section Trajectory

variable {n p : ℕ}

/-- Constant-input solutions of a plant with a Hurwitz state matrix converge to the
equilibrium: generic foundation, the hub's global asymptotic stability about `e`. -/
@[powerlib_foundation] theorem tendsto_equilibrium (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ : ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Set.Ici t₀)) :
    Tendsto x atTop (𝓝 e) := by
  rw [M.inputField_eq he] at hx
  exact (globallyAsymptoticallyStable_of_isHurwitz e hA).2.2.2 t₀ x hx

/-- Componentwise form, for a solution given by its derivative at every time. -/
@[powerlib_foundation] theorem tendsto_equilibrium_apply (M : Plant n p) (hA : IsHurwitz M.A)
    {u : Fin p → ℝ} {e : EuclideanSpace ℝ (Fin n)} (he : IsEquilibrium (M.inputField u) e)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} (hx : ∀ t, HasDerivAt x (M.inputField u (x t)) t)
    (j : Fin n) : Tendsto (fun t => x t j) atTop (𝓝 (e j)) := by
  have h := tendsto_equilibrium M hA he (t₀ := 0) fun t _ => (hx t).hasDerivWithinAt
  exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.tendsto
    e).comp h

end Trajectory

end powerlib.CurrentControl

/-! ## Spectral families -/

namespace powerlib.Spectral

open Matrix Linear LinearSystems TMIO

/-- Requirements of a family decided by the spectrum of a state matrix. -/
inductive Requirement
  /-- The model's static stability condition. -/
  | stable
  /-- The model's static instability condition. -/
  | unstable

variable {X : Type*} {n p : ℕ}

/-- Satisfaction of the two requirements through the static conditions `S` and `U`. -/
def Meets (S U : X → Prop) (x : X) : Requirement → Prop
  | .stable => S x
  | .unstable => U x

@[simp, powerlib_foundation] theorem meets_stable {S U : X → Prop} {x : X} :
    Meets S U x .stable ↔ S x := Iff.rfl

@[simp, powerlib_foundation] theorem meets_unstable {S U : X → Prop} {x : X} :
    Meets S U x .unstable ↔ U x := Iff.rfl

/-- No member meets both requirements when they are mutually exclusive. -/
@[powerlib_foundation] theorem realize_univ_of {S U : X → Prop} (h : ∀ x, S x → U x → False) :
    realize (Meets S U) Set.univ = ∅ := by
  ext x
  simp only [mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact h x (hx .stable) (hx .unstable)

/-! ### Linear families -/

/-- The translation of a linear spectral family. -/
def linearTranslate : Sentence → Set Requirement
  | .flow .unstable => {.unstable}
  | .flow (.decay _) | .flow .conservative | .passive => Set.univ
  | .flow _ => {.stable}

/-- A linear spectral family: every complete system read as the port system of its plant. -/
def linearFamily (plant : X → Plant n p) (S U : X → Prop) : Family X Requirement n p :=
  ⟨fun x => (plant x).system, Meets S U, linearTranslate⟩

@[powerlib_foundation] theorem linearFamily_isLinear (plant : X → Plant n p) (S U : X → Prop) :
    (linearFamily plant S U).IsLinear plant := fun _ => rfl

variable {plant : X → Plant n p} {S U : X → Prop}

/-- A Hurwitz state matrix has no characteristic root in the closed right half plane. -/
@[powerlib_foundation] theorem not_root_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {s : ℂ} (hs : (characteristicMatrix A s).det = 0) : s.re < 0 :=
  (spectrallyStable_iff_isHurwitz A).mpr hA s hs

/-- Soundness of every translation of a linear spectral family: the stability condition gives a
Hurwitz state matrix, the instability condition a characteristic root in the open right half
plane. -/
@[powerlib_foundation] theorem linear_chain_le_semantics
    (hS : ∀ x, S x → IsHurwitz (plant x).A)
    (hU : ∀ x, U x → ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re) :
    ∀ P, (linearFamily plant S U).chain P ≤ (linearFamily plant S U).semantics P := by
  have hF := linearFamily_isLinear plant S U
  have hnone : realize (Meets S U) Set.univ = ∅ := realize_univ_of fun x h1 h2 => by
    obtain ⟨s, hs, hre⟩ := hU x h2
    exact absurd (not_root_of_isHurwitz (hS x h1) hs) (not_lt.mpr hre.le)
  refine Family.chain_le_semantics_iff.mpr fun s x hx => ?_
  rw [mem_realize] at hx
  change ∀ q ∈ linearTranslate s, Meets S U x q at hx
  have huniv : (∀ q, Meets S U x q) → False := fun h => by
    have hx' : x ∈ realize (Meets S U) Set.univ := (mem_realize _ _ _).mpr fun q _ => h q
    rw [hnone] at hx'
    exact hx'
  have hstab : linearTranslate s = {.stable} → IsHurwitz (plant x).A := fun h =>
    hS x (hx .stable (by rw [h]; rfl))
  rcases s with P | _
  · rw [hF.mem_den_flow]
    cases P
    case unstable =>
      obtain ⟨r, hr, hre⟩ := hU x (hx .unstable rfl)
      exact unstable_of_root 0 hr hre
    case lyapunovStable => exact (holds_of_isHurwitz 0 (P := .locallyExponentiallyStable)
      trivial (hstab rfl)).lyapunovStable
    case locallyAsymptoticallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case locallyExponentiallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case globallyAsymptoticallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case globallyExponentiallyStable => exact holds_of_isHurwitz 0 trivial (hstab rfl)
    case contractive => exact sampledContraction_of_isHurwitz 0 (hstab rfl)
    all_goals exact (huniv fun q => hx q trivial).elim
  · exact (huniv fun q => hx q trivial).elim

/-- With a stability condition equivalent to the Hurwitz property, the attractive sentences and
sampled contraction denote exactly the members meeting it. -/
@[powerlib_foundation] theorem linear_den (hS : ∀ x, S x ↔ IsHurwitz (plant x).A)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    (linearFamily plant S U).den (.flow P) = {x | S x} := by
  rw [(linearFamily_isLinear plant S U).den_hurwitz hP]
  ext x
  exact (hS x).symm

/-- With a stability condition equivalent to the Hurwitz property, the attractive and
contractive translations are exact. -/
@[powerlib_foundation] theorem linear_exact (hS : ∀ x, S x ↔ IsHurwitz (plant x).A)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    (linearFamily plant S U).Exact (.flow P) := by
  unfold Family.Exact
  rw [linear_den hS hP]
  have ht : (linearFamily plant S U).translate (.flow P) = {.stable} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact hP.elim
    · rfl
  rw [ht]
  ext x
  simp [mem_realize, linearFamily]

/-! ### Local families -/

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The translation of a local spectral family. -/
def localTranslate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.stable}
  | .flow .unstable => {.unstable}
  | .flow _ => Set.univ
  | .passive => ∅

/-- A local spectral family: every complete system read as its autonomous field about the
selected operating point. -/
def localFamily (field : X → ℝⁿ → ℝⁿ) (S U : X → Prop) : Family X Requirement n 0 :=
  ⟨fun x => Port.System.autonomous (field x), Meets S U, localTranslate⟩

@[powerlib_foundation] theorem localFamily_isAutonomous (field : X → ℝⁿ → ℝⁿ) (S U : X → Prop) :
    (localFamily field S U).IsAutonomous field := fun _ => rfl

/-- Soundness of every translation of a local spectral family: the stability condition gives
local exponential stability of the field at the origin, the instability condition instability. -/
@[powerlib_foundation] theorem local_chain_le_semantics {field : X → ℝⁿ → ℝⁿ}
    (hS : ∀ x, S x → LocallyExponentiallyStable (field x) 0)
    (hU : ∀ x, U x → Unstable (field x) 0) :
    ∀ P, (localFamily field S U).chain P ≤ (localFamily field S U).semantics P := by
  have hF := localFamily_isAutonomous field S U
  have hnone : realize (Meets S U) Set.univ = ∅ :=
    realize_univ_of fun x h1 h2 => hU x h2 (hS x h1).lyapunovStable
  refine Family.chain_le_semantics_iff.mpr fun s x hx => ?_
  rw [mem_realize] at hx
  change ∀ q ∈ localTranslate s, Meets S U x q at hx
  have huniv : (∀ q, Meets S U x q) → False := fun h => by
    have hx' : x ∈ realize (Meets S U) Set.univ := (mem_realize _ _ _).mpr fun q _ => h q
    rw [hnone] at hx'
    exact hx'
  rcases s with P | _
  · rw [hF.mem_den_flow]
    cases P
    case lyapunovStable => exact (hS x (hx .stable rfl)).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable (hS x (hx .stable rfl))
    case locallyExponentiallyStable => exact hS x (hx .stable rfl)
    case unstable => exact hU x (hx .unstable rfl)
    all_goals exact (huniv fun q => hx q trivial).elim
  · rw [hF.den_passive]
    trivial

/-- Passivity is translated exactly in a local spectral family: a system without ports is
passive. -/
@[powerlib_foundation] theorem local_exact_passive (field : X → ℝⁿ → ℝⁿ) (S U : X → Prop) :
    (localFamily field S U).Exact .passive :=
  Family.exact_of_translate_eq_empty rfl (localFamily_isAutonomous field S U).den_passive

/-- With a stability condition equivalent to local exponential stability of the field at the
origin, the local exponential translation of a local spectral family is exact. -/
@[powerlib_foundation] theorem local_exact_locallyExponentiallyStable {field : X → ℝⁿ → ℝⁿ}
    {S U : X → Prop} (hS : ∀ x, S x ↔ LocallyExponentiallyStable (field x) 0) :
    (localFamily field S U).Exact (.flow .locallyExponentiallyStable) := by
  unfold Family.Exact
  ext x
  rw [mem_realize, (localFamily_isAutonomous field S U).mem_den_flow]
  change (∀ q ∈ ({.stable} : Set Requirement), Meets S U x q) ↔
    LocallyExponentiallyStable (field x) 0
  simp [hS x]

/-- With a stability condition equivalent to an equilibrium at the origin with a Hurwitz
Jacobian, for `C¹` fields, the local exponential translation of a local spectral family is exact
(converse linearization, `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`). -/
@[powerlib_foundation] theorem local_exact_of_jacobian {field : X → ℝⁿ → ℝⁿ} {S U : X → Prop}
    (jac : X → Matrix (Fin n) (Fin n) ℝ) (hC : ∀ x, ContDiff ℝ 1 (field x))
    (hJ : ∀ x, fderiv ℝ (field x) 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (jac x))
    (hS : ∀ x, S x ↔ field x 0 = 0 ∧ IsHurwitz (jac x)) :
    (localFamily field S U).Exact (.flow .locallyExponentiallyStable) :=
  local_exact_locallyExponentiallyStable fun x =>
    (hS x).trans (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ (hC x) (hJ x)).symm

/-! ### Inexactness along translations -/

/-- Inexactness passes along translations: if the translation of `s` is sound but not exact, a
sentence `s'` with the same translation whose denotation contains that of `s` is not translated
exactly either (a member of `den s` outside the translated space lies in `den s'`). -/
@[powerlib_foundation] theorem not_exact_of_den_subset {Y Q : Type*} {m q : ℕ}
    {F : Family Y Q m q} {s s' : Sentence} (ht : F.translate s' = F.translate s)
    (hsound : F.Sound s) (hden : F.den s ⊆ F.den s') (h : ¬ F.Exact s) : ¬ F.Exact s' := by
  intro h'
  refine h (Set.Subset.antisymm hsound fun x hx => ?_)
  have hx' := hden hx
  unfold Family.Exact at h'
  rw [← h', ht] at hx'
  exact hx'

/-- In a local spectral family whose stability condition gives local exponential stability, a
boundary witness of the local exponential translation is one of the local asymptotic and Lyapunov
translations. -/
@[powerlib_foundation] theorem local_not_exact_of_not_exact_les {field : X → ℝⁿ → ℝⁿ}
    {S U : X → Prop} (hS : ∀ x, S x → LocallyExponentiallyStable (field x) 0)
    (h : ¬ (localFamily field S U).Exact (.flow .locallyExponentiallyStable))
    {P : Flow.Property} (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable) :
    ¬ (localFamily field S U).Exact (.flow P) := by
  have hF := localFamily_isAutonomous field S U
  refine not_exact_of_den_subset (by rcases hP with rfl | rfl <;> rfl) ?_ ?_ h
  · intro x hx
    rw [mem_realize] at hx
    rw [hF.mem_den_flow]
    exact hS x (hx .stable rfl)
  · intro x hx
    rw [hF.mem_den_flow] at hx ⊢
    rcases hP with rfl | rfl
    · exact hx.lyapunovStable
    · exact Flow.locallyExponentiallyStable_localAsymptoticStable hx

end powerlib.Spectral

/-! ## Degenerate linearizations (generic) -/

namespace powerlib.Dynamics

open Set Filter Topology

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Near a Lyapunov stable point of a `C¹` field every state has a solution on the whole forward
ray, which stays within distance `1/2` of the point. -/
@[powerlib_foundation] theorem exists_forward_of_lyapunovStable {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (h : LyapunovStable f x_eq) :
    ∃ δ > 0, ∀ y : ℝⁿ, ‖y - x_eq‖ < δ → ∃ φ : ℝ → ℝⁿ, φ 0 = y ∧
      IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) ∧ ∀ t, 0 ≤ t → ‖φ t - x_eq‖ < 1 / 2 := by
  obtain ⟨g, K, hK, hg⟩ := exists_lipschitz_cutoff_near hf x_eq
  obtain ⟨δ, hδ, hb⟩ := h (1 / 2) (by norm_num)
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun y hy => ?_⟩
  obtain ⟨ψ, hψ0, hψ⟩ := Flow.forwardComplete_of_lipschitzWith hK 0 y
  have h0 : ‖ψ 0 - x_eq‖ < 1 / 2 := by rw [hψ0]; exact hy.trans_le (min_le_right _ _)
  have hstay : ∀ t, 0 ≤ t → ‖ψ t - x_eq‖ < 1 / 2 := by
    intro t ht
    by_contra hfar0
    have hfar := not_lt.mp hfar0
    obtain ⟨τ, hτ, hτeq, hτin⟩ := exists_first_sphere_hit
      (hψ.continuousOn.mono (Icc_subset_Ici_self : Icc (0 : ℝ) t ⊆ Ici 0)) h0
      ⟨ht, le_rfl⟩ hfar
    have htraj : IsTrajectoryOn ψ f 0 τ := isTrajectoryOn_of_cutoff hg hψ fun s hs => by
      rw [dist_eq_norm]; linarith [hτin s hs]
    have hlt := hb 0 τ ψ htraj (by rw [hψ0]; exact hy.trans_le (min_le_left _ _)) τ
      ⟨hτ.1, le_rfl⟩
    linarith
  refine ⟨ψ, hψ0, fun t ht => ?_, hstay⟩
  have hd := hψ t ht
  have hgt : g (ψ t) = f (ψ t) := hg _ (by rw [dist_eq_norm]; linarith [hstay t ht])
  simp only at hd ⊢
  rw [← hgt]
  exact hd

/-- A function that does not increase along the field near a point, and takes values below its
value at the point arbitrarily close to it, rules out local asymptotic stability of a `C¹`
field: a solution through such a state keeps the function below its value at the point. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_lie_nonpos {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} {V : ℝⁿ → ℝ} {ρ : ℝ} (hf : ContDiff ℝ 1 f) (hV : Differentiable ℝ V)
    (hρ : 0 < ρ) (hLie : ∀ x, ‖x - x_eq‖ < ρ → fderiv ℝ V x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ V x < V x_eq) :
    ¬ LocalAsymptoticStable f x_eq := by
  rintro ⟨hLS, c, hc, hconv⟩
  obtain ⟨δ₁, hδ₁, hex⟩ := exists_forward_of_lyapunovStable hf hLS
  obtain ⟨δ₂, hδ₂, hb⟩ := hLS ρ hρ
  obtain ⟨x, hx, hVx⟩ := hseed (min c (min δ₁ δ₂)) (lt_min hc (lt_min hδ₁ hδ₂))
  obtain ⟨φ, hφ0, hφ, -⟩ := hex x (hx.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hlim : Tendsto φ atTop (𝓝 x_eq) :=
    hconv 0 φ hφ (by rw [hφ0]; exact hx.trans_le (min_le_left _ _))
  have hmono : ∀ t, 0 ≤ t → V (φ t) ≤ V x := by
    intro t ht
    have hseg : IsTrajectoryOn φ f 0 t := hφ.mono Icc_subset_Ici_self
    have hin : ∀ s ∈ Icc 0 t, ‖φ s - x_eq‖ < ρ := fun s hs =>
      hb 0 t φ hseg (by rw [hφ0]; exact hx.trans_le ((min_le_right _ _).trans
        (min_le_right _ _))) s hs
    have hanti := antitoneOn_V_comp_traj hV hV.continuous (convex_Icc 0 t) hseg
      (fun s hs => hLie _ (hin s (interior_subset hs)))
    have := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    simpa [hφ0] using this
  have hlimV : Tendsto (fun t => V (φ t)) atTop (𝓝 (V x_eq)) :=
    (hV.continuous.tendsto x_eq).comp hlim
  have : V x_eq ≤ V x := le_of_tendsto hlimV (eventually_atTop.mpr ⟨0, hmono⟩)
  linarith

/-- Equilibria accumulating at a point rule out its local asymptotic stability: the constant
solution at a nearby equilibrium does not converge to the point. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_of_equilibria {f : ℝⁿ → ℝⁿ}
    {x_eq : ℝⁿ} (h : ∀ ε > 0, ∃ x, x ≠ x_eq ∧ ‖x - x_eq‖ < ε ∧ f x = 0) :
    ¬ LocalAsymptoticStable f x_eq := by
  rintro ⟨-, c, hc, hconv⟩
  obtain ⟨x, hne, hx, hfx⟩ := h c hc
  have hcurve : IsIntegralCurveOn (fun _ : ℝ => x) (fun _ y => f y) (Ici 0) := fun t _ => by
    simp only [hfx]
    exact hasDerivWithinAt_const _ _ _
  exact hne (tendsto_nhds_unique tendsto_const_nhds (hconv 0 _ hcurve hx))

/-- A quadratic energy `‖T x‖²` of an injective linear map `T` that does not increase along the
field makes the origin Lyapunov stable. -/
@[powerlib_foundation] theorem lyapunovStable_of_inner_nonpos {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hn : 0 < n) {f : ℝⁿ → ℝⁿ} (T : ℝⁿ →L[ℝ] E)
    (hT : Function.Injective T) (h : ∀ x, inner ℝ (T x) (T (f x)) ≤ 0) :
    LyapunovStable f 0 := by
  have hd : ∀ x, HasFDerivAt (fun x => ‖T x‖ ^ 2) (2 • (innerSL ℝ (T x)).comp T) x :=
    fun x => T.hasFDerivAt.norm_sq
  refine lyapunov_stable (V := fun x => ‖T x‖ ^ 2) (D := univ) hn
    ⟨isOpen_univ, mem_univ _, by fun_prop, fun x => (hd x).differentiableAt, by simp,
      fun x _ hx => ?_, fun x _ => ?_⟩
  · have : T x ≠ 0 := fun h0 => hx (hT (by rw [h0, map_zero]))
    positivity
  · rw [(hd x).fderiv]
    show (2 : ℕ) • inner ℝ (T x) (T (f x)) ≤ 0
    rw [nsmul_eq_mul]
    nlinarith [h x]

/-- **Chetaev's instability theorem** (classical form). A `C¹` function `W` that is positive at
states arbitrarily close to the point and strictly increases along the field wherever it is
positive within distance `r` makes the point of a `C¹` field unstable. -/
@[powerlib_foundation] theorem unstable_of_chetaev {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {W : ℝⁿ → ℝ}
    {r : ℝ} (hf : ContDiff ℝ 1 f) (hW : ContDiff ℝ 1 W) (hr : 0 < r)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ 0 < W x)
    (hLie : ∀ x, ‖x - x_eq‖ ≤ r → 0 < W x → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  intro hLS
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hLc : Continuous fun x => fderiv ℝ W x (f x) :=
    (hW.continuous_fderiv one_ne_zero).clm_apply hf.continuous
  obtain ⟨δ₁, hδ₁, hex⟩ := exists_forward_of_lyapunovStable hf hLS
  obtain ⟨δ₂, hδ₂, hb⟩ := hLS r hr
  obtain ⟨x₀, hx₀, hW₀⟩ := hseed (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  obtain ⟨φ, hφ0, hφ, -⟩ := hex x₀ (hx₀.trans_le (min_le_left _ _))
  have hin : ∀ t, 0 ≤ t → ‖φ t - x_eq‖ < r := fun t ht =>
    hb 0 t φ (hφ.mono Icc_subset_Ici_self) (by rw [hφ0]; exact hx₀.trans_le (min_le_right _ _))
      t ⟨ht, le_rfl⟩
  -- the solution keeps `W ≥ W x₀`
  have hkeep : ∀ T, 0 ≤ T → ∀ t ∈ Icc 0 T, W x₀ ≤ W (φ t) := by
    intro T hT
    have hc : ContinuousOn φ (Icc 0 T) := hφ.continuousOn.mono Icc_subset_Ici_self
    refine forall_mem_Icc_of_local_step (Ω := {x | W x₀ ≤ W x}) hc
      (isClosed_le continuous_const hW.continuous) (by simp [hφ0]) ?_
    intro s hs hsΩ
    have hpos : 0 < fderiv ℝ W (φ s) (f (φ s)) :=
      hLie _ (hin s hs.1).le (hW₀.trans_le hsΩ)
    obtain ⟨y, hsy, hyT, hy⟩ := exists_Icc_mem_of_isOpen hc
      (isOpen_lt continuous_const hLc) hs hpos
    have hseg : IsIntegralCurveOn φ (fun _ x => f x) (Icc s y) :=
      hφ.mono fun t ht => le_trans hs.1 ht.1
    have hanti := antitoneOn_V_comp_traj (V := fun x => -W x) hWd.neg hWd.continuous.neg
      (convex_Icc s y) hseg fun t ht => by
        have := hy t (interior_subset ht)
        show fderiv ℝ (fun x => -W x) (φ t) (f (φ t)) ≤ 0
        rw [fderiv_fun_neg]
        simpa using this.le
    refine ⟨y, hsy, fun t ht => ?_⟩
    have := hanti ⟨le_rfl, hsy.le⟩ (Ioo_subset_Icc_self ht) ht.1.le
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact (show W x₀ ≤ W (φ s) from hsΩ).trans this
  -- a uniform rate on the compact set `{‖x − x_eq‖ ≤ r, W x ≥ W x₀}`
  set K := {x | ‖x - x_eq‖ ≤ r ∧ W x₀ ≤ W x} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x_eq r).of_isClosed_subset ?_ fun x hx => ?_
    · exact (isClosed_le (continuous_norm.comp (continuous_sub_right x_eq)) continuous_const).inter
        (isClosed_le continuous_const hW.continuous)
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.1
  have hx₀K : x₀ ∈ K := ⟨by simpa [hφ0] using (hin 0 le_rfl).le, le_rfl⟩
  have hφK : ∀ t, 0 ≤ t → φ t ∈ K := fun t ht =>
    ⟨(hin t ht).le, hkeep t ht t ⟨ht, le_rfl⟩⟩
  obtain ⟨xm, hxmK, hmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀K⟩ hLc.continuousOn
  obtain ⟨xM, -, hmax⟩ := hKc.exists_isMaxOn ⟨x₀, hx₀K⟩ hW.continuous.continuousOn
  have hγ : 0 < fderiv ℝ W xm (f xm) := hLie xm hxmK.1 (hW₀.trans_le hxmK.2)
  set γ := fderiv ℝ W xm (f xm)
  set T := (W xM - W x₀) / γ + 1 with hT
  have hT0 : 0 ≤ T := by
    have hle : W x₀ ≤ W xM := hmax hx₀K
    have : 0 ≤ (W xM - W x₀) / γ := div_nonneg (by linarith) hγ.le
    linarith
  have hanti := antitoneOn_V_add_linear (V := fun x => -W x) (c := γ) hWd.neg
    hWd.continuous.neg (convex_Icc 0 T) (hφ.mono Icc_subset_Ici_self) fun t ht => by
      have hmt : γ ≤ fderiv ℝ W (φ t) (f (φ t)) := hmin (hφK t (interior_subset ht).1)
      show fderiv ℝ (fun x => -W x) (φ t) (f (φ t)) ≤ -γ
      rw [fderiv_fun_neg]
      simpa using hmt
  have h1 := hanti ⟨le_rfl, hT0⟩ ⟨hT0, le_rfl⟩ hT0
  simp only [hφ0, mul_zero, add_zero] at h1
  have h2 : W (φ T) ≤ W xM := hmax (hφK T hT0)
  have h3 : γ * T = W xM - W x₀ + γ := by rw [hT]; field_simp
  linarith

/-- **Chetaev's theorem on a dissipated level set.** A `C¹` energy `E` that does not increase
along the field near the point and takes values below `E x*` arbitrarily close to it, together with
a `C¹` function `W` that strictly increases along the field wherever `E < E x*` near the point,
makes the point of a `C¹` field unstable: a solution started below the level of `x*` stays there,
and `W` grows at a uniform rate on the compact part of that sublevel near `x*`. -/
@[powerlib_foundation] theorem unstable_of_lie_nonpos_of_lie_pos {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    {E W : ℝⁿ → ℝ} {r : ℝ} (hf : ContDiff ℝ 1 f) (hE : ContDiff ℝ 1 E) (hW : ContDiff ℝ 1 W)
    (hr : 0 < r) (hELie : ∀ x, ‖x - x_eq‖ ≤ r → fderiv ℝ E x (f x) ≤ 0)
    (hseed : ∀ ε > 0, ∃ x, ‖x - x_eq‖ < ε ∧ E x < E x_eq)
    (hWLie : ∀ x, ‖x - x_eq‖ ≤ r → E x < E x_eq → 0 < fderiv ℝ W x (f x)) :
    Unstable f x_eq := by
  intro hLS
  have hEd : Differentiable ℝ E := hE.differentiable one_ne_zero
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hLc : Continuous fun x => fderiv ℝ W x (f x) :=
    (hW.continuous_fderiv one_ne_zero).clm_apply hf.continuous
  obtain ⟨δ₁, hδ₁, hex⟩ := exists_forward_of_lyapunovStable hf hLS
  obtain ⟨δ₂, hδ₂, hb⟩ := hLS r hr
  obtain ⟨x₀, hx₀, hE₀⟩ := hseed (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  obtain ⟨φ, hφ0, hφ, -⟩ := hex x₀ (hx₀.trans_le (min_le_left _ _))
  have hin : ∀ t, 0 ≤ t → ‖φ t - x_eq‖ < r := fun t ht =>
    hb 0 t φ (hφ.mono Icc_subset_Ici_self) (by rw [hφ0]; exact hx₀.trans_le (min_le_right _ _))
      t ⟨ht, le_rfl⟩
  have hlev : ∀ t, 0 ≤ t → E (φ t) ≤ E x₀ := by
    intro t ht
    have hanti := antitoneOn_V_comp_traj hEd hEd.continuous (convex_Icc 0 t)
      (hφ.mono Icc_subset_Ici_self) fun s hs => hELie _ (hin s (interior_subset hs).1).le
    have := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    simpa [hφ0] using this
  set K := {x | ‖x - x_eq‖ ≤ r ∧ E x ≤ E x₀} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x_eq r).of_isClosed_subset ?_ fun x hx => ?_
    · exact (isClosed_le (continuous_norm.comp (continuous_sub_right x_eq)) continuous_const).inter
        (isClosed_le hE.continuous continuous_const)
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.1
  have hφK : ∀ t, 0 ≤ t → φ t ∈ K := fun t ht => ⟨(hin t ht).le, hlev t ht⟩
  have hx₀K : x₀ ∈ K := by simpa [hφ0] using hφK 0 le_rfl
  obtain ⟨xm, hxmK, hmin⟩ := hKc.exists_isMinOn ⟨x₀, hx₀K⟩ hLc.continuousOn
  obtain ⟨xM, -, hmax⟩ := hKc.exists_isMaxOn ⟨x₀, hx₀K⟩ hW.continuous.continuousOn
  have hγ : 0 < fderiv ℝ W xm (f xm) := hWLie xm hxmK.1 (hxmK.2.trans_lt hE₀)
  set γ := fderiv ℝ W xm (f xm)
  set T := (W xM - W x₀) / γ + 1 with hT
  have hT0 : 0 ≤ T := by
    have hle : W x₀ ≤ W xM := hmax hx₀K
    have : 0 ≤ (W xM - W x₀) / γ := div_nonneg (by linarith) hγ.le
    linarith
  have hanti := antitoneOn_V_add_linear (V := fun x => -W x) (c := γ) hWd.neg
    hWd.continuous.neg (convex_Icc 0 T) (hφ.mono Icc_subset_Ici_self) fun t ht => by
      have hmt : γ ≤ fderiv ℝ W (φ t) (f (φ t)) := hmin (hφK t (interior_subset ht).1)
      show fderiv ℝ (fun x => -W x) (φ t) (f (φ t)) ≤ -γ
      rw [fderiv_fun_neg]
      simpa using hmt
  have h1 := hanti ⟨le_rfl, hT0⟩ ⟨hT0, le_rfl⟩ hT0
  simp only [hφ0, mul_zero, add_zero] at h1
  have h2 : W (φ T) ≤ W xM := hmax (hφK T hT0)
  have h3 : γ * T = W xM - W x₀ + γ := by rw [hT]; field_simp
  linarith

end powerlib.Dynamics
