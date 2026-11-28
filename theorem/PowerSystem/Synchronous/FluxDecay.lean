import theorem.PowerSystem.Synchronous.FluxDecayConverse
import theorem.Spectral.LinearNamed
import theorem.Criteria.Routh3
import theorem.TMIO.ClaimElab

/-! # The flux-decay (one-axis) machine as a linear model family

The linearized one-axis (flux-decay) machine of Heffron–Phillips with constant field voltage,
`Δδ̇ = ω₀Δω`, `2HΔω̇ = −K₁Δδ − K₂ΔE'_q − DΔω`, `T'_{d0}K₃ΔĖ'_q = −ΔE'_q − K₃K₄Δδ`, as a model
family: a model is the data model `FluxDecayParametric.Params` of
`theorem/PowerSystem/Synchronous/FluxDecayParametric.lean` with the sign conditions `H > 0`,
`ω₀ > 0`, `K₃ > 0`, `T'_{d0} > 0`; the system map reads it as the linear plant of its state matrix
`Params.stateMatrix` (`FluxDecayParametric.Params.stateMatrix_mulVec_iff`: the state matrix is the
model), so its flow sentences are those of the linear hub (`Family.IsLinear.den_hurwitz`,
`Linear.holds_iff_isHurwitz`).

The characteristic polynomial is the swing polynomial times the field pole, closed by the
flux-decay torque (`det_characteristicMatrix`):
`2HK₃T'_{d0} det(sI − A) = (1 + sK₃T'_{d0})(2Hs² + Ds + ω₀K₁) − ω₀K₂K₃K₄`. Routh–Hurwitz in the
machine's coefficients (`isHurwitz_stateMatrix_iff`, `mem_den_attractive_iff`): the attractive
sentences hold exactly when `2H + DK₃T'_{d0} > 0`, the steady-state synchronizing coefficient
`K₁ − K₂K₃K₄` is positive, and the Routh quantity
`D(2H + DK₃T'_{d0} + ω₀K₁K₃²T'_{d0}²) + 2Hω₀K₂K₃²K₄T'_{d0}` is positive — the damping torque of
the machine plus the damping torque of the flux decay (deMello–Concordia: for `K₂K₃K₄ > 0` the
flux decay adds damping at the oscillation frequency and removes synchronizing torque at low
frequency).

Model boundary.
* One synchronous machine on an infinite bus, the linearized one-axis model at an operating point
  in the state `(Δδ, Δω, ΔE'_q)` (rotor angle in rad, per-unit speed deviation, transient q-axis
  voltage), in this order; continuous time, linear, autonomous: constant mechanical torque and
  constant field voltage (no AVR, exciter or PSS: `K₅`, `K₆` absent), no damper windings, no
  stator transients, no saturation, no network or multi-machine dynamics.
* Parameters `H > 0`, `ω₀ > 0`, `K₃ > 0`, `T'_{d0} > 0` (fields of `Model`); `K₁`, `K₂`, `K₄`, `D`
  free (heavy loading may make `K₁` or `K₄` negative; negative `D` models a negative damping
  torque of other origin).
* Linearization about an equilibrium of the nonlinear one-axis machine; here the coefficients are
  the data of the model. The nonlinear machine on an infinite bus, whose Jacobian is this state
  matrix with `K₁ … K₄` the partial derivatives of the torque and the field EMF, is
  `theorem/PowerSystem/Synchronous/OneAxis.lean`.

Source: W. G. Heffron, R. A. Phillips, "Effect of a modern amplidyne voltage regulator on
underexcited operation of large turbine generators", AIEE Trans. PAS-71 (1952); F. P. deMello,
C. Concordia, "Concepts of synchronous machine stability as affected by excitation control", IEEE
Trans. PAS-88 (1969) (the coefficients `K₁ … K₄`, the flux-decay block `K₃/(1 + sK₃T'_{d0})`, the
damping and synchronizing torque of the flux decay); P. Kundur, *Power System Stability and
Control* (1994) §12.3; the open item of `theorem/PowerSystem/Synchronous/FluxDecayParametric.lean`
and `theorem/PowerSystem/Synchronous/FluxDecayConverse.lean` (Model boundary: the machine is a
data model, not a model family).

Results.
* Coefficients `coeff3`, `coeff2`, `coeff1`, `coeff0`, `routhQuantity` of
  `a₃s³ + a₂s² + a₁s + a₀`; `routhQuantity_eq`; `trace_stateMatrix`,
  `principalMinorSum_stateMatrix`, `det_stateMatrix`, `det_characteristicMatrix` (static evidence
  on the model).
* `isHurwitz_stateMatrix_iff` (Routh–Hurwitz, `Criteria.isHurwitz_iff_of_coeffs_cubic`),
  `exists_root_of_unstable` (a strict violation of a Routh condition: a root in the open right
  half plane, `Criteria.exists_root_re_pos_of_det`, `Criteria.exists_root_re_pos_of_trace_pos`,
  `Criteria.exists_cubic_root_re_pos_of_gap`).
* The existing data models are models of the family: `Model` is a `Params` with the sign
  conditions (`Model.plant_A`: its plant is the data model's state matrix); the frozen machines of
  the parametric families `FluxDecayParametric.Weak`, `FluxDecayParametric.Driven`,
  `FluxDecayConverse.Converse` at `(ε, t)` are models (`weakModel`, `drivenModel`,
  `converseModel`), at `ε = 0` with the critical state matrix `A₀c` (`weakModel_zero_plant`,
  `drivenModel_zero_plant`, `converseModel_zero_plant`); so are their unpumped machines at `ε`
  (`weakUnpumped`, `drivenUnpumped`, `converseUnpumped`), whose Routh quantity is
  `ε (c₁ + ε c₂)` with `c₁` a positive multiple of the first-order damping of the averaged swing
  pair: `D̂` for `Weak`, `s'` (`Driven.sD`, `Converse.sD`) for the other two
  (`weak_routhQuantity`, `driven_routhQuantity`, `converse_routhQuantity`).

Family and connection conclusions.
* `FluxDecay.family : Family Model Spectral.RateRequirement 3 0` (`Spectral.rateFamily`): every
  model is read as the linear plant of its state matrix, without ports (`family_isLinear`). The
  requirements are static: `stable` the three Routh–Hurwitz conditions, `unstable` a strict
  violation of one of them, `rate a` a strict spectral margin at the rate `a`; Lyapunov stability,
  the attractive sentences and sampled contraction translate into `stable`, instability into
  `unstable`, decay into its margin, conservation and passivity into the whole (inconsistent)
  language.
* `chain_le_semantics` (every translation is sound) and `exact_hurwitz` (the attractive sentences
  and sampled contraction are translated exactly), the rate laws
  `Spectral.chain_le_semantics_of_rate`, `Spectral.exact_of_rate`; `mem_den_attractive_iff` (the
  Routh–Hurwitz conditions in the machine's coefficients), `mem_den_unstable`.
* The flux decay alone: `mem_den_undamped_iff` (without damping, `D = 0`, the machine satisfies
  the attractive sentences exactly when `K₂K₄ > 0` and `K₂K₃K₄ < K₁`, for every `T'_{d0} > 0`);
  `mem_den_of_damped` (`D > 0`, `K₂K₄ ≥ 0`, `K₂K₃K₄ < K₁` suffice).
* The parametric families at `ε = 0` lie on the stability boundary (`weakModel_zero_not_mem_den`,
  `drivenModel_zero_not_mem_den`, `converseModel_zero_not_mem_den`: the undamped swing pair
  `±jν` of `A₀c`).
* Small-signal verdict of the unpumped machines (`weakUnpumped_mem_den_iff`,
  `drivenUnpumped_mem_den_iff`, `converseUnpumped_mem_den_iff`): there is `ε₀ > 0` such that for
  `0 < ε < ε₀` the unpumped machine satisfies an attractive sentence exactly when `D̂ > 0` (`Weak`)
  or `s' > 0` (`Driven`, `Converse`) — the sign of the real part `−D̂/(4H)`, `−s'` of the
  first-order shift `λ₁` of the averaged pair (`FluxDecayParametric.Weak.shift_eq`,
  `FluxDecayParametric.Driven.shift_eq`, `FluxDecayConverse.Converse.shift_eq`): without the
  pump, the small-signal analysis of this family and first-order averaging agree.
* The reading through the classical swing at constant flux is
  `theorem/PowerSystem/Synchronous/FluxDecaySwing.lean`; the nonlinear one-axis machine read
  through this family at an equilibrium is `theorem/PowerSystem/Synchronous/OneAxis.lean`.
-/

noncomputable section
namespace powerlib.Synchronous.FluxDecay

open Matrix LinearSystems TMIO Filter Topology
open powerlib.Synchronous.FluxDecayParametric (Params Weak Driven)
open powerlib.Synchronous.FluxDecayConverse (Converse)

/-! ## The characteristic polynomial -/

/-- The leading coefficient `a₃ = 2H K₃ T'_{d0}` of `2HK₃T'_{d0} det(sI − A)`. -/
def coeff3 (p : Params) : ℝ := 2 * p.H * p.K₃ * p.Td0

/-- `a₂ = 2H + D K₃ T'_{d0}`. -/
def coeff2 (p : Params) : ℝ := 2 * p.H + p.D * p.K₃ * p.Td0

/-- `a₁ = D + ω₀ K₁ K₃ T'_{d0}`. -/
def coeff1 (p : Params) : ℝ := p.D + p.ω₀ * p.K₁ * p.K₃ * p.Td0

/-- `a₀ = ω₀ (K₁ − K₂ K₃ K₄)`: `ω₀` times the steady-state synchronizing coefficient. -/
def coeff0 (p : Params) : ℝ := p.ω₀ * (p.K₁ - p.K₂ * p.K₃ * p.K₄)

/-- The Routh quantity `a₂ a₁ − a₃ a₀`. -/
def routhQuantity (p : Params) : ℝ := coeff2 p * coeff1 p - coeff3 p * coeff0 p

/-- The Routh quantity is the damping torque of the machine plus that of the flux decay:
`D (2H + DK₃T'_{d0} + ω₀K₁K₃²T'_{d0}²) + 2Hω₀K₂K₃²K₄T'_{d0}`. -/
@[tmio M, powerlib_domain] theorem routhQuantity_eq (p : Params) :
    routhQuantity p =
      p.D * (2 * p.H + p.D * p.K₃ * p.Td0 + p.ω₀ * p.K₁ * p.K₃ ^ 2 * p.Td0 ^ 2) +
        2 * p.H * p.ω₀ * p.K₂ * p.K₃ ^ 2 * p.K₄ * p.Td0 := by
  unfold routhQuantity coeff3 coeff2 coeff1 coeff0
  ring

@[tmio M, powerlib_domain] private theorem coeff3_ne (p : Params) (hH : p.H ≠ 0) (hK : p.K₃ ≠ 0)
    (hT : p.Td0 ≠ 0) : coeff3 p ≠ 0 := by
  unfold coeff3
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hH) hK) hT

@[tmio M, powerlib_domain] theorem trace_stateMatrix (p : Params) (hH : p.H ≠ 0) (hK : p.K₃ ≠ 0)
    (hT : p.Td0 ≠ 0) : p.stateMatrix.trace = -coeff2 p / coeff3 p := by
  simp only [Params.stateMatrix, Matrix.trace_fin_three_of, coeff2, coeff3]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem principalMinorSum_stateMatrix (p : Params) (hH : p.H ≠ 0)
    (hK : p.K₃ ≠ 0) (hT : p.Td0 ≠ 0) :
    Criteria.principalMinorSum p.stateMatrix = coeff1 p / coeff3 p := by
  simp only [Params.stateMatrix, Criteria.principalMinorSum, coeff1, coeff3, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.head_fin_const]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem det_stateMatrix (p : Params) (hH : p.H ≠ 0) (hK : p.K₃ ≠ 0)
    (hT : p.Td0 ≠ 0) : p.stateMatrix.det = -coeff0 p / coeff3 p := by
  simp only [Params.stateMatrix, Matrix.det_fin_three, coeff0, coeff3, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.head_fin_const]
  field_simp
  ring

/-- **The characteristic polynomial.** The swing polynomial `2Hs² + Ds + ω₀K₁` times the field
factor `1 + sK₃T'_{d0}`, closed by the flux-decay torque `ω₀K₂K₃K₄`:
`2HK₃T'_{d0} det(sI − A) = (1 + sK₃T'_{d0})(2Hs² + Ds + ω₀K₁) − ω₀K₂K₃K₄`. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix (p : Params) (hH : p.H ≠ 0)
    (hK : p.K₃ ≠ 0) (hT : p.Td0 ≠ 0) (s : ℂ) :
    (coeff3 p : ℂ) * (Linear.characteristicMatrix p.stateMatrix s).det =
      ((p.K₃ * p.Td0 : ℝ) * s + 1) * (2 * p.H * s ^ 2 + p.D * s + p.ω₀ * p.K₁) -
        p.ω₀ * p.K₂ * p.K₃ * p.K₄ := by
  have h3 : (coeff3 p : ℂ) ≠ 0 := by exact_mod_cast coeff3_ne p hH hK hT
  rw [Criteria.det_characteristicMatrix_fin_three, trace_stateMatrix p hH hK hT,
    principalMinorSum_stateMatrix p hH hK hT, det_stateMatrix p hH hK hT]
  push_cast
  field_simp
  simp only [coeff3, coeff2, coeff1, coeff0]
  push_cast
  ring

/-- **Routh–Hurwitz for the flux-decay machine** (`H, K₃, T'_{d0} > 0`): the state matrix is
Hurwitz exactly when `a₂ > 0`, `a₀ > 0` and the Routh quantity is positive. -/
@[tmio TM, powerlib_domain] theorem isHurwitz_stateMatrix_iff (p : Params) (hH : 0 < p.H)
    (hK : 0 < p.K₃) (hT : 0 < p.Td0) :
    IsHurwitz p.stateMatrix ↔ 0 < coeff2 p ∧ 0 < coeff0 p ∧ 0 < routhQuantity p := by
  rw [Criteria.isHurwitz_iff_of_coeffs_cubic _ (by unfold coeff3; positivity)
    (trace_stateMatrix p hH.ne' hK.ne' hT.ne')
    (principalMinorSum_stateMatrix p hH.ne' hK.ne' hT.ne')
    (det_stateMatrix p hH.ne' hK.ne' hT.ne'), routhQuantity, sub_pos]

/-- A strict violation of a Routh condition — `a₀ < 0` (a positive real root), `a₂ < 0` (positive
trace) or a negative Routh quantity (the gap) — gives a characteristic root in the open right half
plane. -/
@[tmio TM, powerlib_domain] theorem exists_root_of_unstable (p : Params) (hH : 0 < p.H)
    (hK : 0 < p.K₃) (hT : 0 < p.Td0) (h : coeff0 p < 0 ∨ coeff2 p < 0 ∨ routhQuantity p < 0) :
    ∃ s : ℂ, (Linear.characteristicMatrix p.stateMatrix s).det = 0 ∧ 0 < s.re := by
  have h3 : 0 < coeff3 p := by unfold coeff3; positivity
  rcases h with h | h | h
  · refine Criteria.exists_root_re_pos_of_det _ ?_
    rw [show ((-1 : ℝ) ^ 3) = -1 by norm_num, neg_one_mul, neg_lt_zero,
      det_stateMatrix p hH.ne' hK.ne' hT.ne', neg_div]
    exact neg_pos.2 (div_neg_of_neg_of_pos h h3)
  · refine Criteria.exists_root_re_pos_of_trace_pos _ ?_
    rw [trace_stateMatrix p hH.ne' hK.ne' hT.ne', neg_div]
    exact neg_pos.2 (div_neg_of_neg_of_pos h h3)
  · have hgap : coeff2 p / coeff3 p * (coeff1 p / coeff3 p) < coeff0 p / coeff3 p := by
      rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) h3]
      unfold routhQuantity at h
      have := mul_neg_of_neg_of_pos h h3
      nlinarith
    obtain ⟨s, hs, hre⟩ := Criteria.exists_cubic_root_re_pos_of_gap hgap
    refine ⟨s, ?_, hre⟩
    rw [Criteria.det_characteristicMatrix_fin_three', trace_stateMatrix p hH.ne' hK.ne' hT.ne',
      principalMinorSum_stateMatrix p hH.ne' hK.ne' hT.ne', det_stateMatrix p hH.ne' hK.ne' hT.ne']
    simpa only [neg_div, neg_neg] using hs

/-! ## The family -/

/-- A flux-decay machine: the Heffron–Phillips data with the sign conditions `H > 0`, `ω₀ > 0`,
`K₃ > 0`, `T'_{d0} > 0`. -/
structure Model where
  /-- The coefficients `K₁ … K₄`, `H`, `D`, `T'_{d0}`, `ω₀`. -/
  p : Params
  H_pos : 0 < p.H
  ω₀_pos : 0 < p.ω₀
  K₃_pos : 0 < p.K₃
  Td0_pos : 0 < p.Td0

/-- The linear plant of a model: its state matrix, no ports. -/
def Model.plant (x : Model) : Linear.Plant 3 0 := ⟨x.p.stateMatrix, 0, 0, 0⟩

/-- The plant of a model is the state matrix of its data (`Params.stateMatrix_mulVec_iff`: the
Heffron–Phillips equations). -/
@[tmio M, powerlib_domain] theorem Model.plant_A (x : Model) : x.plant.A = x.p.stateMatrix := rfl

/-- Requirements on the flux-decay machines, all static: the rate language
(`Spectral.RateRequirement`). -/
abbrev Requirement := Spectral.RateRequirement

/-- The flux-decay family (`Spectral.rateFamily`): every model read as the linear plant of its
state matrix; `stable` the Routh–Hurwitz conditions `a₂ > 0`, `a₀ > 0`, `a₂a₁ − a₃a₀ > 0`,
`unstable` a strict violation of one of them, `rate a` a strict spectral margin at `a`. -/
def family : Family Model Requirement 3 0 :=
  Spectral.rateFamily Model.plant
    (fun x => 0 < coeff2 x.p ∧ 0 < coeff0 x.p ∧ 0 < routhQuantity x.p)
    (fun x => coeff0 x.p < 0 ∨ coeff2 x.p < 0 ∨ routhQuantity x.p < 0)
    fun x a => Linear.RateMargin x.plant.A a

@[tmio M, powerlib_domain] theorem family_isLinear : family.IsLinear Model.plant :=
  Spectral.rateFamily_isLinear _ _ _ _

/-- Every translation of the flux-decay family is sound (`Spectral.chain_le_semantics_of_rate`):
the Routh–Hurwitz conditions make the state matrix Hurwitz, a strict violation gives a
right-half-plane root, the rate requirement is a spectral margin. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.chain_le_semantics_of_rate family_isLinear rfl
    (fun x h => (isHurwitz_stateMatrix_iff x.p x.H_pos x.K₃_pos x.Td0_pos).2 h)
    (fun x h => exists_root_of_unstable x.p x.H_pos x.K₃_pos x.Td0_pos h) fun _ _ h => h

/-- The attractive sentences and sampled contraction are translated exactly: the Routh–Hurwitz
conditions are their translation (`Spectral.exact_of_rate`). -/
@[tmio TM, powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.exact_of_rate family_isLinear rfl
    (fun x => (isHurwitz_stateMatrix_iff x.p x.H_pos x.K₃_pos x.Td0_pos).symm) hP

/-- **The member characterization.** A flux-decay machine satisfies an attractive sentence (or
sampled contraction) exactly when `2H + DK₃T'_{d0} > 0`, the steady-state synchronizing
coefficient `K₁ − K₂K₃K₄` is positive, and the damping torque of the machine and of the flux decay,
`D(2H + DK₃T'_{d0} + ω₀K₁K₃²T'_{d0}²) + 2Hω₀K₂K₃²K₄T'_{d0}`, is positive. -/
@[tmio TM, powerlib_domain] theorem mem_den_attractive_iff (x : Model) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow P) ↔ x ∈ {x : Model |
      0 < 2 * x.p.H + x.p.D * x.p.K₃ * x.p.Td0 ∧ x.p.K₂ * x.p.K₃ * x.p.K₄ < x.p.K₁ ∧
      0 < x.p.D * (2 * x.p.H + x.p.D * x.p.K₃ * x.p.Td0 +
          x.p.ω₀ * x.p.K₁ * x.p.K₃ ^ 2 * x.p.Td0 ^ 2) +
        2 * x.p.H * x.p.ω₀ * x.p.K₂ * x.p.K₃ ^ 2 * x.p.K₄ * x.p.Td0}) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz hP]
  change IsHurwitz x.p.stateMatrix ↔ _
  rw [isHurwitz_stateMatrix_iff x.p x.H_pos x.K₃_pos x.Td0_pos, routhQuantity_eq]
  have e : 0 < coeff0 x.p ↔ x.p.K₂ * x.p.K₃ * x.p.K₄ < x.p.K₁ := by
    unfold coeff0
    rw [mul_pos_iff_of_pos_left x.ω₀_pos, sub_pos]
  exact and_congr Iff.rfl (and_congr e Iff.rfl)

/-- A strict violation of a Routh condition — a negative steady-state synchronizing coefficient
`K₁ < K₂K₃K₄` (aperiodic), `2H + DK₃T'_{d0} < 0`, or a negative damping torque of machine and flux
decay (oscillatory) — places a machine in instability. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (x : Model)
    (h : x.p.K₁ < x.p.K₂ * x.p.K₃ * x.p.K₄ ∨ 2 * x.p.H + x.p.D * x.p.K₃ * x.p.Td0 < 0 ∨
      x.p.D * (2 * x.p.H + x.p.D * x.p.K₃ * x.p.Td0 +
          x.p.ω₀ * x.p.K₁ * x.p.K₃ ^ 2 * x.p.Td0 ^ 2) +
        2 * x.p.H * x.p.ω₀ * x.p.K₂ * x.p.K₃ ^ 2 * x.p.K₄ * x.p.Td0 < 0) :
    connection% (x ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have h' : coeff0 x.p < 0 ∨ coeff2 x.p < 0 ∨ routhQuantity x.p < 0 := by
    rw [routhQuantity_eq]
    rcases h with h | h | h
    · left
      unfold coeff0
      exact mul_neg_of_pos_of_neg x.ω₀_pos (sub_neg.mpr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨s, hs, hre⟩ := exists_root_of_unstable x.p x.H_pos x.K₃_pos x.Td0_pos h'
  exact family_isLinear.mem_den_flow.mpr (Linear.unstable_of_root 0 hs hre)

/-! ## The flux decay alone -/

/-- **The flux decay damps the undamped machine.** Without damping (`D = 0`) a machine satisfies
an attractive sentence exactly when `K₂K₄ > 0` (the flux decay's damping torque is positive) and
the steady-state synchronizing coefficient `K₁ − K₂K₃K₄` is positive — for every `T'_{d0} > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_undamped_iff (x : Model) (hD : x.p.D = 0)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow P) ↔
      0 < x.p.K₂ * x.p.K₄ ∧ x.p.K₂ * x.p.K₃ * x.p.K₄ < x.p.K₁) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_attractive_iff x hP), Set.mem_ofPred_eq, hD]
  have hpos : 0 < 2 * x.p.H * x.p.ω₀ * x.p.K₃ ^ 2 * x.p.Td0 := by
    have := x.H_pos; have := x.ω₀_pos; have := x.K₃_pos; have := x.Td0_pos
    positivity
  have e : 0 * (2 * x.p.H + 0 * x.p.K₃ * x.p.Td0 + x.p.ω₀ * x.p.K₁ * x.p.K₃ ^ 2 * x.p.Td0 ^ 2) +
      2 * x.p.H * x.p.ω₀ * x.p.K₂ * x.p.K₃ ^ 2 * x.p.K₄ * x.p.Td0 =
      2 * x.p.H * x.p.ω₀ * x.p.K₃ ^ 2 * x.p.Td0 * (x.p.K₂ * x.p.K₄) := by ring
  rw [e, mul_pos_iff_of_pos_left hpos]
  have h2 : 0 < 2 * x.p.H + 0 * x.p.K₃ * x.p.Td0 := by have := x.H_pos; linarith
  exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨h2, h.2, h.1⟩⟩

/-- Positive damping, a nonnegative flux-decay coupling `K₂K₄ ≥ 0` and a positive steady-state
synchronizing coefficient make a machine satisfy every attractive sentence. -/
@[tmio TM, powerlib_domain] theorem mem_den_of_damped (x : Model) (hD : 0 < x.p.D)
    (hc : 0 ≤ x.p.K₂ * x.p.K₄) (hs : x.p.K₂ * x.p.K₃ * x.p.K₄ < x.p.K₁) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  refine (connection_proof% mem_den_attractive_iff x hP).mpr ?_
  have hH := x.H_pos; have hω := x.ω₀_pos; have hK := x.K₃_pos; have hT := x.Td0_pos
  have hK₁ : 0 < x.p.K₁ := by
    have : 0 ≤ x.p.K₂ * x.p.K₃ * x.p.K₄ := by
      rw [show x.p.K₂ * x.p.K₃ * x.p.K₄ = x.p.K₃ * (x.p.K₂ * x.p.K₄) by ring]
      exact mul_nonneg hK.le hc
    linarith
  refine ⟨by positivity, hs, ?_⟩
  have h1 : 0 < x.p.D * (2 * x.p.H + x.p.D * x.p.K₃ * x.p.Td0 +
      x.p.ω₀ * x.p.K₁ * x.p.K₃ ^ 2 * x.p.Td0 ^ 2) := by positivity
  have h2 : 0 ≤ 2 * x.p.H * x.p.ω₀ * x.p.K₂ * x.p.K₃ ^ 2 * x.p.K₄ * x.p.Td0 := by
    rw [show 2 * x.p.H * x.p.ω₀ * x.p.K₂ * x.p.K₃ ^ 2 * x.p.K₄ * x.p.Td0 =
      2 * x.p.H * x.p.ω₀ * x.p.K₃ ^ 2 * x.p.Td0 * (x.p.K₂ * x.p.K₄) by ring]
    have : 0 < 2 * x.p.H * x.p.ω₀ * x.p.K₃ ^ 2 * x.p.Td0 := by positivity
    exact mul_nonneg this.le hc
  linarith

/-! ## The parametric families as models -/

/-- The frozen machine of the weak-coupling family (`FluxDecayParametric.Weak`) at `ε` and time
`t`, a model of the family (with `H, ω₀, K₃, T'_{d0} > 0`). -/
def weakModel (f : Weak) (hH : 0 < f.H) (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0)
    (ε t : ℝ) : Model :=
  ⟨f.machine ε t, hH, hω, hK, hT⟩

/-- The frozen machine of the driven-field family (`FluxDecayParametric.Driven`) at `ε`, `t`. -/
def drivenModel (f : Driven) (hH : 0 < f.H) (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0)
    (ε t : ℝ) : Model :=
  ⟨f.machine ε t, hH, hω, hK, hT⟩

/-- The frozen machine of the converse family (`FluxDecayConverse.Converse`) at `ε`, `t`. -/
def converseModel (f : Converse) (hH : 0 < f.H) (hω : 0 < f.ω₀) (hK : 0 < f.K₃)
    (hT : 0 < f.Td0) (ε t : ℝ) : Model :=
  ⟨f.machine ε t, hH, hω, hK, hT⟩

/-- At `ε = 0` the weak-coupling member is the critical machine `A₀c`
(`FluxDecayParametric.Weak.machine_stateMatrix`). -/
@[tmio M, powerlib_domain] theorem weakModel_zero_plant (f : Weak) (hH : 0 < f.H) (hω : 0 < f.ω₀)
    (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) :
    (weakModel f hH hω hK hT 0 t).plant.A = f.critMatrix := by
  rw [Model.plant_A]
  change (f.machine 0 t).stateMatrix = _
  rw [f.machine_stateMatrix hH.ne' hω.ne']
  simp [ParametricResonance.BlockAveraging.physJ]

/-- At `ε = 0` the driven-field member is the critical machine `A₀c`
(`FluxDecayParametric.Driven.machine_stateMatrix`). -/
@[tmio M, powerlib_domain] theorem drivenModel_zero_plant (f : Driven) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) :
    (drivenModel f hH hω hK hT 0 t).plant.A = f.critMatrix := by
  rw [Model.plant_A]
  change (f.machine 0 t).stateMatrix = _
  rw [f.machine_stateMatrix hH.ne' hω.ne']
  simp [ParametricResonance.BlockAveraging.physJ]

/-- At `ε = 0` the converse member is the critical machine `A₀c`
(`FluxDecayConverse.Converse.machine_stateMatrix`). -/
@[tmio M, powerlib_domain] theorem converseModel_zero_plant (f : Converse) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) :
    (converseModel f hH hω hK hT 0 t).plant.A = f.critMatrix := by
  rw [Model.plant_A]
  change (f.machine 0 t).stateMatrix = _
  rw [f.machine_stateMatrix hH.ne' hω.ne']
  simp [ParametricResonance.BlockAveraging.physJ]

/-- An undamped machine whose flux decay does not act (`D = 0`, `K₂K₄ = 0`) lies on the stability
boundary: it satisfies no attractive sentence. -/
@[tmio TM, powerlib_domain] private theorem not_mem_den_of_critical (x : Model) (hD : x.p.D = 0)
    (hc : x.p.K₂ * x.p.K₄ = 0) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∉ family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_undamped_iff x hD hP), hc]
  exact fun h => lt_irrefl 0 h.1

/-- At `ε = 0` the weak-coupling machine (`D = 0`, `K₂ = K₄ = 0`) satisfies no attractive sentence:
its swing pair `±jν` lies on the imaginary axis. -/
@[tmio TM, powerlib_domain] theorem weakModel_zero_not_mem_den (f : Weak) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (weakModel f hH hω hK hT 0 t ∉ family.den (.flow P)) :=
  not_mem_den_of_critical _ (by simp [weakModel, Weak.machine, Weak.params])
    (by simp [weakModel, Weak.machine, Weak.params]) hP

/-- At `ε = 0` the driven-field machine (`D = 0`, `K₂ = 0`) satisfies no attractive sentence. -/
@[tmio TM, powerlib_domain] theorem drivenModel_zero_not_mem_den (f : Driven) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (drivenModel f hH hω hK hT 0 t ∉ family.den (.flow P)) :=
  not_mem_den_of_critical _ (by simp [drivenModel, Driven.machine, Driven.params])
    (by simp [drivenModel, Driven.machine, Driven.params]) hP

/-- At `ε = 0` the converse machine (`D = 0`, `K₄ = 0`) satisfies no attractive sentence. -/
@[tmio TM, powerlib_domain] theorem converseModel_zero_not_mem_den (f : Converse) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (converseModel f hH hω hK hT 0 t ∉ family.den (.flow P)) :=
  not_mem_den_of_critical _ (by simp [converseModel, Converse.machine, Converse.params])
    (by simp [converseModel, Converse.machine, Converse.params]) hP

/-! ## The unpumped machines at small `ε`: the first-order damping decides -/

/-- The unpumped machine of the weak-coupling family at `ε` (`FluxDecayParametric.Weak.params`:
damping `εD̂`, couplings `εK̂₂`, `εK̂₄`, detuned `K₁`), a model of the family. -/
def weakUnpumped (f : Weak) (hH : 0 < f.H) (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0)
    (ε : ℝ) : Model :=
  ⟨f.params ε, hH, hω, hK, hT⟩

/-- The unpumped machine of the driven-field family at `ε` (`FluxDecayParametric.Driven.params`). -/
def drivenUnpumped (f : Driven) (hH : 0 < f.H) (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0)
    (ε : ℝ) : Model :=
  ⟨f.params ε, hH, hω, hK, hT⟩

/-- The unpumped machine of the converse family at `ε` (`FluxDecayConverse.Converse.params`). -/
def converseUnpumped (f : Converse) (hH : 0 < f.H) (hω : 0 < f.ω₀) (hK : 0 < f.K₃)
    (hT : 0 < f.Td0) (ε : ℝ) : Model :=
  ⟨f.params ε, hH, hω, hK, hT⟩

/-- The Routh quantity of the unpumped weak-coupling machine is `ε (2H(1 + ν²τ²) D̂ + ε c)`,
`τ = K₃T'_{d0}`: its first-order part is the damping `D̂` alone (the couplings enter at
`ε²`). -/
@[tmio M, powerlib_domain] theorem weak_routhQuantity (f : Weak) (hω : f.ω₀ ≠ 0) (ε : ℝ) :
    routhQuantity (f.params ε) = ε * (2 * f.H * (1 + f.ν ^ 2 * (f.K₃ * f.Td0) ^ 2) * f.Dh +
      ε * (f.Dh ^ 2 * f.K₃ * f.Td0 - 4 * f.H * f.Dh * f.ν ^ 2 * f.dh * (f.K₃ * f.Td0) ^ 2 +
        2 * f.H * f.ω₀ * f.K2h * f.K₃ ^ 2 * f.K4h * f.Td0)) := by
  rw [routhQuantity_eq]
  simp only [Weak.params]
  field_simp
  ring

/-- The Routh quantity of the unpumped driven-field machine is
`ε (8H²m s' + ε c)`, `m = 1 + ν²τ²`: its first-order part is the first-order damping
`s' = D̂/(4H) + ω₀K₃K₄K̂₂τ/(4Hm)` of the averaged swing pair (`FluxDecayParametric.Driven.sD`,
`FluxDecayParametric.Driven.shift_eq`). -/
@[tmio M, powerlib_domain] theorem driven_routhQuantity (f : Driven) (hω : f.ω₀ ≠ 0)
    (ε : ℝ) :
    routhQuantity (f.params ε) = ε * (8 * f.H ^ 2 * f.mden * f.sD +
      ε * (f.Dh ^ 2 * f.K₃ * f.Td0 - 4 * f.H * f.Dh * f.ν ^ 2 * f.dh * (f.K₃ * f.Td0) ^ 2)) := by
  have hm : 1 + f.ν ^ 2 * (f.K₃ * f.Td0) ^ 2 ≠ 0 := by positivity
  rw [routhQuantity_eq]
  simp only [Driven.params, Driven.sD, Driven.mden, Driven.tau]
  field_simp
  ring

/-- The Routh quantity of the unpumped converse machine is `ε (8H²m s' + ε c)` with the
first-order damping `s' = D̂/(4H) + ω₀K₂K₃K̂₄τ/(4Hm)` (`FluxDecayConverse.Converse.sD`,
`FluxDecayConverse.Converse.shift_eq`). -/
@[tmio M, powerlib_domain] theorem converse_routhQuantity (f : Converse) (hω : f.ω₀ ≠ 0)
    (ε : ℝ) :
    routhQuantity (f.params ε) = ε * (8 * f.H ^ 2 * f.mden * f.sD +
      ε * (f.Dh ^ 2 * f.K₃ * f.Td0 - 4 * f.H * f.Dh * f.ν ^ 2 * f.dh * (f.K₃ * f.Td0) ^ 2)) := by
  have hm : 1 + f.ν ^ 2 * (f.K₃ * f.Td0) ^ 2 ≠ 0 := by positivity
  rw [routhQuantity_eq]
  simp only [Converse.params, Converse.sD, Converse.mden, Converse.tau]
  field_simp
  ring

/-- A family of machines whose Routh quantity is `ε (c₁ + ε c₂)` with `c₁ ≠ 0`, and whose
coefficients `a₂`, `a₀` stay positive as `ε → 0⁺`, is Hurwitz for small `ε > 0` exactly when
`c₁ > 0`. -/
@[tmio M, powerlib_domain] private theorem eventually_isHurwitz_iff (p : ℝ → Params)
    (hH : ∀ ε, 0 < (p ε).H) (hK : ∀ ε, 0 < (p ε).K₃) (hT : ∀ ε, 0 < (p ε).Td0) {c₁ c₂ : ℝ}
    (hc : c₁ ≠ 0) (hR : ∀ ε, routhQuantity (p ε) = ε * (c₁ + ε * c₂))
    (h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < coeff2 (p ε)) (h0 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < coeff0 (p ε)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (IsHurwitz (p ε).stateMatrix ↔ 0 < c₁) := by
  have hlim : Tendsto (fun ε : ℝ => c₁ + ε * c₂) (𝓝 0) (𝓝 c₁) := by
    have h := (tendsto_const_nhds (x := c₁)).add
      ((tendsto_id (x := 𝓝 (0 : ℝ))).mul (tendsto_const_nhds (x := c₂)))
    simpa using h
  have hsign : ∀ᶠ ε in 𝓝 (0 : ℝ), (0 < c₁ + ε * c₂ ↔ 0 < c₁) := by
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · filter_upwards [hlim.eventually (gt_mem_nhds hneg)] with ε h
      exact iff_of_false (not_lt.2 h.le) (not_lt.2 hneg.le)
    · filter_upwards [hlim.eventually (lt_mem_nhds hpos)] with ε h
      exact iff_of_true h hpos
  filter_upwards [nhdsWithin_le_nhds hsign, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h0,
    self_mem_nhdsWithin] with ε hs h2 h0 (hε : 0 < ε)
  rw [isHurwitz_stateMatrix_iff (p ε) (hH ε) (hK ε) (hT ε), hR, mul_pos_iff_of_pos_left hε, hs]
  exact ⟨fun h => h.2.2, fun h => ⟨h2, h0, h⟩⟩

/-- `a₂` of an unpumped machine with damping `εD̂` stays positive as `ε → 0`. -/
@[tmio M, powerlib_domain] private theorem eventually_coeff2_pos (p : ℝ → Params) {H : ℝ}
    (hH : 0 < H) (hc : Continuous fun ε => coeff2 (p ε)) (h0 : coeff2 (p 0) = 2 * H) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < coeff2 (p ε) :=
  (hc.tendsto 0).eventually (lt_mem_nhds (by rw [h0]; positivity))

/-- `a₀` of an unpumped machine at the 2:1 resonance tends to `2Hν² > 0` as `ε → 0`. -/
@[tmio M, powerlib_domain] private theorem eventually_coeff0_pos (p : ℝ → Params) {H ν : ℝ}
    (hH : 0 < H) (hν : ν ≠ 0) (hc : Continuous fun ε => coeff0 (p ε))
    (h0 : coeff0 (p 0) = 2 * H * ν ^ 2) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < coeff0 (p ε) := by
  have : 0 < ν ^ 2 := by positivity
  exact (hc.tendsto 0).eventually (lt_mem_nhds (by rw [h0]; positivity))

/-- **The unpumped weak-coupling machine at small `ε`.** For all small `ε > 0` it satisfies an
attractive sentence exactly when `D̂ > 0`: the sign of the first-order damping `−D̂/(4H)` of the
averaged swing pair (`FluxDecayParametric.Weak.shift_eq`), which the field does not reach. -/
@[tmio TM, powerlib_domain] theorem weakUnpumped_mem_den_iff (f : Weak) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (hν : f.ν ≠ 0) (hD : f.Dh ≠ 0)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (weakUnpumped f hH hω hK hT ε ∈ family.den (.flow P) ↔ 0 < f.Dh)) := by
  unfold powerlib.TMIO.Statement
  have hm : 0 < 2 * f.H * (1 + f.ν ^ 2 * (f.K₃ * f.Td0) ^ 2) := by positivity
  have hev := eventually_isHurwitz_iff (fun ε => f.params ε) (fun _ => hH) (fun _ => hK)
    (fun _ => hT) (mul_ne_zero hm.ne' hD) (weak_routhQuantity f hω.ne')
    (eventually_coeff2_pos _ hH (by simp only [coeff2, Weak.params]; fun_prop)
      (by simp [coeff2, Weak.params]))
    (eventually_coeff0_pos _ hH hν (by simp only [coeff0, Weak.params]; fun_prop)
      (by simp only [coeff0, Weak.params]; field_simp; ring))
  obtain ⟨ε₀, hε₀, h⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨ε₀, hε₀, fun ε hε hlt => ?_⟩
  rw [(connection_proof% family_isLinear.mem_den_hurwitz hP)]
  change IsHurwitz (f.params ε).stateMatrix ↔ _
  rw [h ⟨hε, hlt⟩, mul_pos_iff_of_pos_left hm]

/-- **The unpumped driven-field machine at small `ε`.** For all small `ε > 0` it satisfies an
attractive sentence exactly when the first-order damping `s' = D̂/(4H) + ω₀K₃K₄K̂₂τ/(4Hm)` of the
averaged swing pair is positive (`FluxDecayParametric.Driven.sD`): the small-signal verdict of the
unpumped machine is the first-order averaging verdict without pump. -/
@[tmio TM, powerlib_domain] theorem drivenUnpumped_mem_den_iff (f : Driven) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (hν : f.ν ≠ 0) (hs : f.sD ≠ 0)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (drivenUnpumped f hH hω hK hT ε ∈ family.den (.flow P) ↔ 0 < f.sD)) := by
  unfold powerlib.TMIO.Statement
  have hm : 0 < 8 * f.H ^ 2 * f.mden := by
    have : 0 < f.mden := by unfold Driven.mden; positivity
    positivity
  have hev := eventually_isHurwitz_iff (fun ε => f.params ε) (fun _ => hH) (fun _ => hK)
    (fun _ => hT) (mul_ne_zero hm.ne' hs) (driven_routhQuantity f hω.ne')
    (eventually_coeff2_pos _ hH (by simp only [coeff2, Driven.params]; fun_prop)
      (by simp [coeff2, Driven.params]))
    (eventually_coeff0_pos _ hH hν (by simp only [coeff0, Driven.params]; fun_prop)
      (by simp only [coeff0, Driven.params]; field_simp; ring))
  obtain ⟨ε₀, hε₀, h⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨ε₀, hε₀, fun ε hε hlt => ?_⟩
  rw [(connection_proof% family_isLinear.mem_den_hurwitz hP)]
  change IsHurwitz (f.params ε).stateMatrix ↔ _
  rw [h ⟨hε, hlt⟩, mul_pos_iff_of_pos_left hm]

/-- **The unpumped converse machine at small `ε`.** For all small `ε > 0` it satisfies an
attractive sentence exactly when the first-order damping `s' = D̂/(4H) + ω₀K₂K₃K̂₄τ/(4Hm)` is
positive (`FluxDecayConverse.Converse.sD`). -/
@[tmio TM, powerlib_domain] theorem converseUnpumped_mem_den_iff (f : Converse) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (hν : f.ν ≠ 0) (hs : f.sD ≠ 0)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (converseUnpumped f hH hω hK hT ε ∈ family.den (.flow P) ↔ 0 < f.sD)) := by
  unfold powerlib.TMIO.Statement
  have hm : 0 < 8 * f.H ^ 2 * f.mden := by
    have : 0 < f.mden := by unfold Converse.mden; positivity
    positivity
  have hev := eventually_isHurwitz_iff (fun ε => f.params ε) (fun _ => hH) (fun _ => hK)
    (fun _ => hT) (mul_ne_zero hm.ne' hs) (converse_routhQuantity f hω.ne')
    (eventually_coeff2_pos _ hH (by simp only [coeff2, Converse.params]; fun_prop)
      (by simp [coeff2, Converse.params]))
    (eventually_coeff0_pos _ hH hν (by simp only [coeff0, Converse.params]; fun_prop)
      (by simp only [coeff0, Converse.params]; field_simp; ring))
  obtain ⟨ε₀, hε₀, h⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨ε₀, hε₀, fun ε hε hlt => ?_⟩
  rw [(connection_proof% family_isLinear.mem_den_hurwitz hP)]
  change IsHurwitz (f.params ε).stateMatrix ↔ _
  rw [h ⟨hε, hlt⟩, mul_pos_iff_of_pos_left hm]

end powerlib.Synchronous.FluxDecay
