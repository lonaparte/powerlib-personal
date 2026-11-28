import theorem.PowerSystem.Synchronous.FluxDecay
import theorem.PowerSystem.Synchronous.Swing

/-! # The flux-decay machine read through the classical swing at constant flux

With the transient voltage `E'_q` held constant, the one-axis (flux-decay) machine
(`Synchronous.FluxDecay.family`, `theorem/PowerSystem/Synchronous/FluxDecay.lean`) is the
classical machine: `Δδ̇ = ω₀Δω`, `2HΔω̇ = −K₁Δδ − DΔω`, i.e. the linearized swing machine
`M Δδ̈ + D_s Δδ̇ + K Δδ = 0` with inertia `M = 2H/ω₀`, damping `D_s = D/ω₀` and synchronizing
coefficient `K = K₁` (`K₁ = ∂T_e/∂δ` at constant `E'_q`). This module compares the two families
sentence by sentence. Their plants have different dimensions (three states and two), so the
comparison is not a reading of systems: it compares the denotations on the sentences that the
linear hub decides through the Hurwitz property (the attractive sentences and sampled contraction),
under a condition.

* The characteristic polynomial factors through the swing polynomial
  (`det_characteristicMatrix_swing`):
  `2HK₃T'_{d0} det(sI − A) = 2H(1 + sK₃T'_{d0}) det(sI − J) − ω₀K₂K₃K₄` for every swing model whose
  Jacobian `J` has inertia `2H/ω₀`, damping `D/ω₀` and synchronizing coefficient `K₁` (a matching
  model; `constantFlux` is one, `constantFlux_matches`).
* Exact reading on the decoupled context `K₂K₄ = 0` (the field does not act on the torque,
  `K₂ = 0`, or the angle does not act on the field, `K₄ = 0`): the spectrum is the swing spectrum
  with the field pole `−1/(K₃T'_{d0}) < 0` (`isHurwitz_iff_swing`), so the flux-decay machine
  satisfies an attractive sentence exactly when its constant-flux swing machine does
  (`mem_den_iff_swing`, `mem_den_iff_constantFlux`), and, at a balanced operating angle, exactly
  when the nonlinear swing machine (the hub `Synchronous.Swing.family`) is locally exponentially
  stable (`mem_den_locallyExponentiallyStable_iff_hub`, through
  `Synchronous.Swing.exactUnder_locallyExponentiallyStable`).
* The reading does not hold off the context, in both directions, and for every `T'_{d0} > 0`:
  without damping, a flux decay with `K₂K₄ > 0` and `K₂K₃K₄ < K₁` makes the machine attractive while
  its constant-flux machine is not (`mem_den_not_swing_of_undamped`); a damped machine with
  `0 < K₁ < K₂K₃K₄` is unstable (negative steady-state synchronizing coefficient) while its
  constant-flux machine is attractive (`swing_mem_den_of_steadySync_neg`).
* What survives of `T'_{d0} → ∞` (`exists_Td0_mem_den_iff_constantFlux`): away from the
  degenerate coefficients (`D ≠ 0`, `K₁ ≠ 0`) and with `K₂K₃K₄ < K₁` whenever `D > 0`, `K₁ > 0`,
  a slow enough field gives the constant-flux verdict. None of the conditions can be dropped, for
  any `T'_{d0}`: `D = 0` (`mem_den_not_swing_of_undamped`), `0 < K₁ < K₂K₃K₄`
  (`swing_mem_den_of_steadySync_neg`), `K₁ = 0` (`mem_den_not_swing_of_flat`: with
  `K₂K₃K₄ < 0`, `D > 0` and `D² + 2Hω₀K₂K₃K₄ ≥ 0` the machine is attractive while its constant-flux
  machine has no synchronizing coefficient).
* The parametric families of `theorem/PowerSystem/Synchronous/FluxDecayParametric.lean` and
  `theorem/PowerSystem/Synchronous/FluxDecayConverse.lean` at `ε = 0` lie in the decoupled context
  (`weakModel_zero_decoupled`, `drivenModel_zero_decoupled`, `converseModel_zero_decoupled`).

Model boundary.
* The flux-decay machines of `theorem/PowerSystem/Synchronous/FluxDecay.lean` (state
  `(Δδ, Δω, ΔE'_q)`, `H, ω₀, K₃, T'_{d0} > 0`, constant field voltage and mechanical torque, no
  AVR, exciter, PSS, damper windings or network dynamics) and the swing models of
  `theorem/PowerSystem/Synchronous/Swing.lean` (state `(δ, ω)` with `ω = δ̇` in rad/s, sinusoidal
  power-angle curve, constant mechanical power), linearized (`Swing.Linearized.family`) or
  nonlinear about a balanced selected angle (`Swing.family`).
* The swing model matches the flux-decay machine: `M = 2H/ω₀`, `D_s = D/ω₀` and
  `k₂ cos(δ* − k₃) = K₁`; the per-unit speed of the one-axis model is `ω/ω₀` (the momentum
  coordinates are not involved: only Hurwitz-decided sentences are compared).
* Only the attractive sentences and sampled contraction are compared (for the hub: local
  exponential stability); Lyapunov stability, instability, conservation, decay rates and passivity
  are not transferred (each family keeps its own laws).

Source: Agda scaffold `theorem/PowerSystem/Synchronous/FluxDecaySwing.agda` (the families, the
matching, the decoupled context, the obligations Lean proves, the reading on the context, the
three boundary witnesses and the slow-field threshold); F. P. deMello, C. Concordia, "Concepts
of synchronous machine stability as affected by excitation control", IEEE Trans. PAS-88 (1969)
(the constant-flux machine and the flux-decay torque `−K₂K₃K₄/(1 + sK₃T'_{d0}) Δδ`); P. Kundur,
*Power System Stability and Control* (1994) §12.3; the classical machine
`theorem/PowerSystem/Synchronous/Swing.lean`.

Results.
* `constantFlux`, `constantFlux_matches` — the constant-flux machine of a flux-decay machine.
* `swing_det_characteristicMatrix`, `det_characteristicMatrix_swing`,
  `det_characteristicMatrix_decoupled`, `isHurwitz_iff_swing` — static evidence: the factorization
  of the characteristic polynomial and the Hurwitz property on the decoupled context.
* `weakModel_zero_decoupled`, `drivenModel_zero_decoupled`, `converseModel_zero_decoupled` — the
  parametric families at `ε = 0` are decoupled.
* `exists_Td0_mem_den_iff_constantFlux` — the slow-field threshold.

Family and connection conclusions.
* `mem_den_iff_swing`, `mem_den_iff_constantFlux` (two families, on the context `K₂K₄ = 0`): the
  attractive sentences and sampled contraction of the flux-decay machine are those of every
  matching linearized swing machine.
* `mem_den_locallyExponentiallyStable_iff_hub` (two families, on the context and at a balanced
  angle): local exponential stability of the flux-decay machine is that of the nonlinear swing
  machine.
* Boundary witnesses (two families, off the context, every `T'_{d0} > 0`):
  `mem_den_not_swing_of_undamped`, `swing_mem_den_of_steadySync_neg`, `mem_den_not_swing_of_flat`.
  So the field is not
  decoupled by a slow field: `T'_{d0} → ∞` does not give the constant-flux machine, since the
  steady-state synchronizing coefficient `K₁ − K₂K₃K₄` does not depend on `T'_{d0}` and, without
  other damping, the flux decay's damping torque decides for every `T'_{d0}`.
* `exists_Td0_mem_den_iff_constantFlux` (two families, a threshold): the strongest form of the
  slow-field limit — for `D ≠ 0`, `K₁ ≠ 0` and `K₂K₃K₄ < K₁` when `D, K₁ > 0` there is `τ > 0`
  such that every machine with `T'_{d0} > τ` agrees with its constant-flux machine on the
  attractive sentences (the Routh quantity is `aT'_{d0}² + bT'_{d0} + c` with `a = Dω₀K₁K₃²`,
  `c = 2HD`, and `a₂ = 2H + DK₃T'_{d0}`).
-/

noncomputable section
namespace powerlib.Synchronous.FluxDecay

open Matrix LinearSystems TMIO
open powerlib.Synchronous.FluxDecayParametric (Params Weak Driven)
open powerlib.Synchronous.FluxDecayConverse (Converse)

/-! ## The constant-flux machine -/

/-- The constant-flux (classical) machine of a flux-decay machine: the swing model with inertia
`2H/ω₀`, damping `D/ω₀` and power-angle curve `K₁ sin δ`, read at `δ* = 0` (balanced at zero
power), so that its synchronizing coefficient is `K₁`. -/
def constantFlux (x : Model) : Swing.Model :=
  ⟨⟨2 * x.p.H / x.p.ω₀, x.p.D / x.p.ω₀, 0, 0, x.p.K₁, 0⟩, 0⟩

/-- The constant-flux machine matches the flux-decay machine, and it is balanced. -/
@[tmio M, powerlib_domain] theorem constantFlux_matches (x : Model) :
    (constantFlux x).p.M = 2 * x.p.H / x.p.ω₀ ∧ (constantFlux x).p.D = x.p.D / x.p.ω₀ ∧
      (constantFlux x).p.syncCoeff (constantFlux x).δ = x.p.K₁ ∧
        (constantFlux x).p.Pe (constantFlux x).δ = (constantFlux x).p.Pm := by
  simp [constantFlux, SwingParams.syncCoeff, SwingParams.Pe]

/-! ## The characteristic polynomial through the swing polynomial -/

/-- The characteristic polynomial of a matching swing Jacobian:
`2H det(sI − J) = 2Hs² + Ds + ω₀K₁` (`SwingParams.characteristic_polynomial`). -/
@[tmio M, powerlib_domain] theorem swing_det_characteristicMatrix (x : Model) (m : Swing.Model)
    (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀)
    (hK : m.p.syncCoeff m.δ = x.p.K₁) (s : ℂ) :
    (2 * x.p.H : ℂ) * (Linear.characteristicMatrix (m.p.jacobian m.δ) s).det =
      2 * x.p.H * s ^ 2 + x.p.D * s + x.p.ω₀ * x.p.K₁ := by
  have hH := x.H_pos
  have hω := x.ω₀_pos
  have hM0 : m.p.M ≠ 0 := by rw [hM]; positivity
  have h := m.p.characteristic_polynomial hM0 m.δ s
  rw [hM, hD, hK] at h
  have hω' : (x.p.ω₀ : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  push_cast at h
  field_simp at h
  linear_combination h

/-- **The characteristic polynomial through the swing polynomial.** For a matching swing model,
`2HK₃T'_{d0} det(sI − A) = 2H(1 + sK₃T'_{d0}) det(sI − J) − ω₀K₂K₃K₄`. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_swing (x : Model) (m : Swing.Model)
    (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀)
    (hK : m.p.syncCoeff m.δ = x.p.K₁) (s : ℂ) :
    (coeff3 x.p : ℂ) * (Linear.characteristicMatrix x.p.stateMatrix s).det =
      ((x.p.K₃ * x.p.Td0 : ℝ) * s + 1) * (2 * x.p.H) *
          (Linear.characteristicMatrix (m.p.jacobian m.δ) s).det -
        x.p.ω₀ * x.p.K₂ * x.p.K₃ * x.p.K₄ := by
  have h := swing_det_characteristicMatrix x m hM hD hK s
  rw [det_characteristicMatrix x.p x.H_pos.ne' x.K₃_pos.ne' x.Td0_pos.ne']
  linear_combination (-(((x.p.K₃ * x.p.Td0 : ℝ) : ℂ) * s + 1)) * h

/-- On the decoupled context `K₂K₄ = 0` the characteristic polynomial is the swing polynomial
times the field factor: `det(sI − A) = (s + 1/(K₃T'_{d0})) det(sI − J)`. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_decoupled (x : Model)
    (m : Swing.Model) (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀)
    (hK : m.p.syncCoeff m.δ = x.p.K₁) (hc : x.p.K₂ * x.p.K₄ = 0) (s : ℂ) :
    (Linear.characteristicMatrix x.p.stateMatrix s).det =
      (s + ((1 / (x.p.K₃ * x.p.Td0) : ℝ) : ℂ)) *
        (Linear.characteristicMatrix (m.p.jacobian m.δ) s).det := by
  have h := det_characteristicMatrix_swing x m hM hD hK s
  have hc' : (x.p.ω₀ : ℂ) * x.p.K₂ * x.p.K₃ * x.p.K₄ = 0 := by
    rw [show (x.p.ω₀ : ℂ) * x.p.K₂ * x.p.K₃ * x.p.K₄ =
      (x.p.ω₀ : ℂ) * x.p.K₃ * ((x.p.K₂ * x.p.K₄ : ℝ) : ℂ) by push_cast; ring, hc]
    simp
  rw [hc', sub_zero] at h
  have h3 : (coeff3 x.p : ℂ) ≠ 0 := by
    have := x.H_pos; have := x.K₃_pos; have := x.Td0_pos
    exact_mod_cast (show coeff3 x.p ≠ 0 by unfold coeff3; positivity)
  have hK3 : (x.p.K₃ : ℂ) ≠ 0 := by exact_mod_cast x.K₃_pos.ne'
  have hT : (x.p.Td0 : ℂ) ≠ 0 := by exact_mod_cast x.Td0_pos.ne'
  apply mul_left_cancel₀ h3
  rw [h]
  simp only [coeff3]
  push_cast
  field_simp

/-- **On the decoupled context the flux-decay machine is Hurwitz exactly when its matching swing
Jacobian is**: the spectrum is the swing spectrum together with the field pole
`−1/(K₃T'_{d0}) < 0`. -/
@[tmio TM, powerlib_domain] theorem isHurwitz_iff_swing (x : Model) (m : Swing.Model)
    (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀)
    (hK : m.p.syncCoeff m.δ = x.p.K₁) (hc : x.p.K₂ * x.p.K₄ = 0) :
    IsHurwitz x.p.stateMatrix ↔ IsHurwitz (m.p.jacobian m.δ) := by
  have hτ : 0 < x.p.K₃ * x.p.Td0 := mul_pos x.K₃_pos x.Td0_pos
  simp only [← Linear.spectrallyStable_iff_isHurwitz, Linear.SpectrallyStable,
    det_characteristicMatrix_decoupled x m hM hD hK hc, mul_eq_zero]
  constructor
  · exact fun h s hs => h s (Or.inr hs)
  · rintro h s (hs | hs)
    · rw [add_eq_zero_iff_eq_neg] at hs
      rw [hs, Complex.neg_re, Complex.ofReal_re, neg_neg_iff_pos]
      exact one_div_pos.mpr hτ
    · exact h s hs

/-! ## The reading on the decoupled context -/

/-- **The constant-flux reading.** On the decoupled context `K₂K₄ = 0` a flux-decay machine
satisfies an attractive sentence (or sampled contraction) exactly when every matching linearized
swing machine (inertia `2H/ω₀`, damping `D/ω₀`, synchronizing coefficient `K₁`) does. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_swing (x : Model) (m : Swing.Model)
    (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀)
    (hK : m.p.syncCoeff m.δ = x.p.K₁) (hc : x.p.K₂ * x.p.K₄ = 0) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow P) ↔ m ∈ Swing.Linearized.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isLinear.mem_den_hurwitz hP),
    (connection_proof% Swing.Linearized.family_isLinear.mem_den_hurwitz hP)]
  exact isHurwitz_iff_swing x m hM hD hK hc

/-- The constant-flux reading at the canonical constant-flux machine (`constantFlux`). -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_constantFlux (x : Model)
    (hc : x.p.K₂ * x.p.K₄ = 0) {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow P) ↔
      constantFlux x ∈ Swing.Linearized.family.den (.flow P)) := by
  obtain ⟨hM, hD, hK, -⟩ := constantFlux_matches x
  exact mem_den_iff_swing x (constantFlux x) hM hD hK hc hP

/-- **Through the nonlinear swing hub.** On the decoupled context, a flux-decay machine is locally
exponentially stable exactly when a matching swing machine at a balanced angle is
(`Synchronous.Swing.exactUnder_locallyExponentiallyStable`: balance, damping and synchronization
at positive inertia). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_hub (x : Model)
    (m : Swing.Model) (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀)
    (hK : m.p.syncCoeff m.δ = x.p.K₁) (hb : m.p.Pe m.δ = m.p.Pm) (hc : x.p.K₂ * x.p.K₄ = 0) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ Swing.family.den (.flow .locallyExponentiallyStable)) := by
  have hr := mem_den_iff_swing x m hM hD hK hc (P := .locallyExponentiallyStable)
    (Or.inl trivial)
  have hx := Swing.exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hr hx ⊢
  have hM0 : 0 < m.p.M := by
    have := x.H_pos; have := x.ω₀_pos
    rw [hM]; positivity
  rw [(connection_proof% Spectral.exactUnder_iff_forall)] at hx
  rw [hr, (connection_proof% Swing.Linearized.family_isLinear.mem_den_hurwitz
    (P := .locallyExponentiallyStable) (Or.inl trivial)), ← hx m ((TMIO.mem_realize _ _ _).mpr
      fun q hq => by
        rw [Set.mem_singleton_iff] at hq
        subst hq
        exact hM0)]
  change IsHurwitz (m.p.jacobian m.δ) ↔ _
  rw [m.p.isHurwitz_jacobian_iff hM0 m.δ]
  simp only [TMIO.mem_realize, Swing.family, Swing.translate, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  simp [Swing.Meets, hb, hM0]

/-! ## Off the context: the boundary witnesses -/

/-- **The flux decay damps the undamped machine, for every `T'_{d0}`.** Without damping, with
`K₂K₄ > 0` and `K₂K₃K₄ < K₁`, a flux-decay machine satisfies the attractive sentences while no
matching swing machine does (its damping `D/ω₀` vanishes). -/
@[tmio TM, powerlib_domain] theorem mem_den_not_swing_of_undamped (x : Model) (m : Swing.Model)
    (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀) (hD0 : x.p.D = 0)
    (hc : 0 < x.p.K₂ * x.p.K₄) (hs : x.p.K₂ * x.p.K₃ * x.p.K₄ < x.p.K₁) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow P) ∧ m ∉ Swing.Linearized.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  refine ⟨(connection_proof% mem_den_undamped_iff x hD0 hP).mpr ⟨hc, hs⟩, fun h => ?_⟩
  have hM0 : 0 < m.p.M := by
    have := x.H_pos; have := x.ω₀_pos
    rw [hM]; positivity
  rw [(connection_proof% Swing.Linearized.family_isLinear.mem_den_hurwitz hP)] at h
  have := ((m.p.isHurwitz_jacobian_iff hM0 m.δ).mp h).1
  rw [hD, hD0, zero_div] at this
  exact lt_irrefl 0 this

/-- **The flux decay removes the steady-state synchronizing torque, for every `T'_{d0}`.** A
damped machine with `0 < K₁ < K₂K₃K₄` is unstable (a positive real root: the steady-state
synchronizing coefficient `K₁ − K₂K₃K₄` is negative), while every matching swing machine
satisfies the attractive sentences. -/
@[tmio TM, powerlib_domain] theorem swing_mem_den_of_steadySync_neg (x : Model) (m : Swing.Model)
    (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hD : m.p.D = x.p.D / x.p.ω₀)
    (hK : m.p.syncCoeff m.δ = x.p.K₁) (hD0 : 0 < x.p.D) (hK₁ : 0 < x.p.K₁)
    (hs : x.p.K₁ < x.p.K₂ * x.p.K₃ * x.p.K₄) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ Swing.Linearized.family.den (.flow P) ∧
      x ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have hM0 : 0 < m.p.M := by
    have := x.H_pos; have := x.ω₀_pos
    rw [hM]; positivity
  refine ⟨?_, (connection_proof% mem_den_unstable x (Or.inl hs))⟩
  rw [(connection_proof% Swing.Linearized.family_isLinear.mem_den_hurwitz hP)]
  refine (m.p.isHurwitz_jacobian_iff hM0 m.δ).mpr ⟨?_, by rw [hK]; exact hK₁⟩
  rw [hD]
  exact div_pos hD0 x.ω₀_pos

/-- **A flat constant-flux curve, for every `T'_{d0}`.** With `K₁ = 0`, a damped machine whose
flux decay supplies a steady-state synchronizing torque (`K₂K₃K₄ < 0`) and does not undo the
damping (`D² + 2Hω₀K₂K₃K₄ ≥ 0`) satisfies the attractive sentences, while no matching swing
machine does (its synchronizing coefficient vanishes). -/
@[tmio TM, powerlib_domain] theorem mem_den_not_swing_of_flat (x : Model) (m : Swing.Model)
    (hM : m.p.M = 2 * x.p.H / x.p.ω₀) (hK : m.p.syncCoeff m.δ = x.p.K₁) (hK₁ : x.p.K₁ = 0)
    (hD0 : 0 < x.p.D) (hs : x.p.K₂ * x.p.K₃ * x.p.K₄ < 0)
    (hd : 0 ≤ x.p.D ^ 2 + 2 * x.p.H * x.p.ω₀ * (x.p.K₂ * x.p.K₃ * x.p.K₄)) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (x ∈ family.den (.flow P) ∧ m ∉ Swing.Linearized.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hH := x.H_pos; have hω := x.ω₀_pos; have hK3 := x.K₃_pos; have hT := x.Td0_pos
  refine ⟨(connection_proof% mem_den_attractive_iff x hP).mpr ⟨by positivity, by linarith, ?_⟩,
    fun h => ?_⟩
  · rw [hK₁]
    have e : x.p.D * (2 * x.p.H + x.p.D * x.p.K₃ * x.p.Td0 + x.p.ω₀ * 0 * x.p.K₃ ^ 2 *
        x.p.Td0 ^ 2) + 2 * x.p.H * x.p.ω₀ * x.p.K₂ * x.p.K₃ ^ 2 * x.p.K₄ * x.p.Td0 =
        2 * x.p.H * x.p.D + x.p.K₃ * x.p.Td0 *
          (x.p.D ^ 2 + 2 * x.p.H * x.p.ω₀ * (x.p.K₂ * x.p.K₃ * x.p.K₄)) := by ring
    rw [e]
    have : 0 ≤ x.p.K₃ * x.p.Td0 *
        (x.p.D ^ 2 + 2 * x.p.H * x.p.ω₀ * (x.p.K₂ * x.p.K₃ * x.p.K₄)) :=
      mul_nonneg (by positivity) hd
    have : 0 < 2 * x.p.H * x.p.D := by positivity
    linarith
  · have hM0 : 0 < m.p.M := by rw [hM]; positivity
    rw [(connection_proof% Swing.Linearized.family_isLinear.mem_den_hurwitz hP)] at h
    have := ((m.p.isHurwitz_jacobian_iff hM0 m.δ).mp h).2
    rw [hK, hK₁] at this
    exact lt_irrefl 0 this

/-! ## The parametric families at `ε = 0` -/

/-- At `ε = 0` the weak-coupling machine is decoupled (`K₂ = K₄ = 0`). -/
@[tmio M, powerlib_domain] theorem weakModel_zero_decoupled (f : Weak) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) :
    (weakModel f hH hω hK hT 0 t).p.K₂ * (weakModel f hH hω hK hT 0 t).p.K₄ = 0 := by
  simp [weakModel, Weak.machine, Weak.params]

/-- At `ε = 0` the driven-field machine is decoupled (`K₂ = 0`). -/
@[tmio M, powerlib_domain] theorem drivenModel_zero_decoupled (f : Driven) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) :
    (drivenModel f hH hω hK hT 0 t).p.K₂ * (drivenModel f hH hω hK hT 0 t).p.K₄ = 0 := by
  simp [drivenModel, Driven.machine, Driven.params]

/-- At `ε = 0` the converse machine is decoupled (`K₄ = 0`). -/
@[tmio M, powerlib_domain] theorem converseModel_zero_decoupled (f : Converse) (hH : 0 < f.H)
    (hω : 0 < f.ω₀) (hK : 0 < f.K₃) (hT : 0 < f.Td0) (t : ℝ) :
    (converseModel f hH hω hK hT 0 t).p.K₂ * (converseModel f hH hω hK hT 0 t).p.K₄ = 0 := by
  simp [converseModel, Converse.machine, Converse.params]

/-! ## A slow field -/

/-- The constant-flux machine satisfies an attractive sentence exactly when `D > 0` and
`K₁ > 0`. -/
@[tmio TM, powerlib_domain] private theorem constantFlux_mem_den_iff (x : Model)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (constantFlux x ∈ Swing.Linearized.family.den (.flow P) ↔
      0 < x.p.D ∧ 0 < x.p.K₁) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨hM, hDs, hKs, -⟩ := constantFlux_matches x
  have hM0 : 0 < (constantFlux x).p.M := by
    have := x.H_pos; have := x.ω₀_pos
    rw [hM]; positivity
  rw [(connection_proof% Swing.Linearized.family_isLinear.mem_den_hurwitz hP)]
  change IsHurwitz ((constantFlux x).p.jacobian (constantFlux x).δ) ↔ _
  rw [(constantFlux x).p.isHurwitz_jacobian_iff hM0, hDs, hKs,
    div_pos_iff_of_pos_right x.ω₀_pos]

/-- **A slow field: what survives of `T'_{d0} → ∞`.** Fix `H, ω₀, K₃ > 0` and `D, K₁, K₂, K₄` with
`D ≠ 0`, `K₁ ≠ 0`, and `K₂K₃K₄ < K₁` whenever `D > 0` and `K₁ > 0`. Then there is a `τ > 0` such
that every flux-decay machine with these coefficients and `T'_{d0} > τ` satisfies an attractive
sentence exactly when its constant-flux machine does. Without the conditions it fails for every
`T'_{d0}` (`mem_den_not_swing_of_undamped`: `D = 0`; `swing_mem_den_of_steadySync_neg`:
`0 < K₁ < K₂K₃K₄`). -/
@[tmio TM, powerlib_domain] theorem exists_Td0_mem_den_iff_constantFlux (H D ω₀ K₁ K₂ K₃ K₄ : ℝ)
    (hH : 0 < H) (hω : 0 < ω₀) (hK : 0 < K₃) (hD : D ≠ 0) (hK₁ : K₁ ≠ 0)
    (hs : 0 < D → 0 < K₁ → K₂ * K₃ * K₄ < K₁) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (∃ τ : ℝ, 0 < τ ∧ ∀ x : Model, x.p.H = H → x.p.D = D → x.p.ω₀ = ω₀ →
      x.p.K₁ = K₁ → x.p.K₂ = K₂ → x.p.K₃ = K₃ → x.p.K₄ = K₄ → τ < x.p.Td0 →
        (x ∈ family.den (.flow P) ↔ constantFlux x ∈ Swing.Linearized.family.den (.flow P))) := by
  unfold powerlib.TMIO.Statement
  -- The Routh quantity as a polynomial in `T'_{d0}`: `a T² + b T + c`.
  set a := D * ω₀ * K₁ * K₃ ^ 2 with ha
  set b := D ^ 2 * K₃ + 2 * H * ω₀ * K₂ * K₃ ^ 2 * K₄ with hb
  set c := 2 * H * D with hc
  have hR : ∀ T, D * (2 * H + D * K₃ * T + ω₀ * K₁ * K₃ ^ 2 * T ^ 2) +
      2 * H * ω₀ * K₂ * K₃ ^ 2 * K₄ * T = T * (a * T + b) + c := fun T => by ring
  have key : ∀ τ : ℝ, (∀ T, τ < T → ((0 < 2 * H + D * K₃ * T ∧ K₂ * K₃ * K₄ < K₁ ∧
      0 < T * (a * T + b) + c) ↔ (0 < D ∧ 0 < K₁))) →
      ∀ x : Model, x.p.H = H → x.p.D = D → x.p.ω₀ = ω₀ → x.p.K₁ = K₁ → x.p.K₂ = K₂ →
        x.p.K₃ = K₃ → x.p.K₄ = K₄ → τ < x.p.Td0 →
          (x ∈ family.den (.flow P) ↔ constantFlux x ∈ Swing.Linearized.family.den (.flow P)) := by
    intro τ hτ x eH eD eω e1 e2 e3 e4 hT
    rw [(connection_proof% mem_den_attractive_iff x hP), Set.mem_ofPred_eq,
      (connection_proof% constantFlux_mem_den_iff x hP), eH, eD, eω, e1, e2, e3, e4, hR]
    exact hτ _ hT
  rcases lt_or_gt_of_ne hD with hDn | hDp
  · -- `D < 0`: `a₂ = 2H + DK₃T'_{d0} < 0` for a slow field; the swing machine is not damped.
    have hq : 0 < -D * K₃ := mul_pos (neg_pos.mpr hDn) hK
    refine ⟨2 * H / (-D * K₃) + 1, add_pos (div_pos (by positivity) hq) one_pos, key _ ?_⟩
    intro T hT
    have h1 : 2 * H < T * (-D * K₃) := by
      rw [← div_lt_iff₀ hq]
      linarith
    refine iff_of_false (fun h => ?_) (fun h => absurd h.1 (not_lt.2 hDn.le))
    nlinarith [h.1]
  rcases lt_or_gt_of_ne hK₁ with hKn | hKp
  · -- `D > 0`, `K₁ < 0`: the Routh quantity is eventually negative.
    have haneg : a < 0 := by
      rw [ha]
      have : 0 < D * ω₀ * K₃ ^ 2 := by positivity
      nlinarith
    have hcpos : 0 < c := by rw [hc]; positivity
    have hq : 0 < -a := neg_pos.mpr haneg
    refine ⟨(|b| + c) / (-a) + 1, add_pos (div_pos (by positivity) hq) one_pos, key _ ?_⟩
    intro T hT
    have hT1 : 1 < T := by
      have : 0 ≤ (|b| + c) / (-a) := div_nonneg (by positivity) hq.le
      linarith
    have h1 : |b| + c < T * (-a) := by
      rw [← div_lt_iff₀ hq]
      linarith
    have hbT : b * T ≤ |b| * T := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
    have hneg : T * (a * T + b) + c < 0 := by nlinarith
    exact iff_of_false (fun h => absurd h.2.2 (not_lt.2 hneg.le))
      (fun h => absurd h.2 (not_lt.2 hKn.le))
  · -- `D > 0`, `K₁ > 0`: the Routh quantity is eventually positive.
    have hapos : 0 < a := by rw [ha]; positivity
    have hcpos : 0 < c := by rw [hc]; positivity
    refine ⟨|b| / a + 1, add_pos_of_nonneg_of_pos (div_nonneg (abs_nonneg b) hapos.le) one_pos,
      key _ ?_⟩
    intro T hT
    have hT0 : 0 < T := by
      have : 0 ≤ |b| / a := div_nonneg (abs_nonneg b) hapos.le
      linarith
    have h1 : |b| < T * a := by
      rw [← div_lt_iff₀ hapos]
      linarith
    have hpos : 0 < T * (a * T + b) + c := by
      have : 0 < a * T + b := by nlinarith [neg_abs_le b]
      positivity
    refine iff_of_true ⟨by positivity, hs hDp hKp, hpos⟩ ⟨hDp, hKp⟩

end powerlib.Synchronous.FluxDecay
