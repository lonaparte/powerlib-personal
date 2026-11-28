{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.PowerSystem.Synchronous.FluxDecaySwing where
-- Lean modules: theorem.PowerSystem.Synchronous.FluxDecaySwing

-- Scaffold of the reading of the flux-decay (one-axis) machine through the classical swing machine
-- at constant flux (`Synchronous.FluxDecay.family` of
-- `theorem/PowerSystem/Synchronous/FluxDecay.lean` read through
-- `Synchronous.Swing.Linearized.family` and, at a balanced angle, through the swing hub
-- `Synchronous.Swing.family`; Lean `theorem/PowerSystem/Synchronous/FluxDecaySwing.lean`). A
-- flux-decay machine `(H, D, ω₀, K₁, K₂, K₃, K₄, T'_{d0})` with `H, ω₀, K₃, T'_{d0} > 0` held at
-- constant `E'_q` is a swing machine with inertia `2H/ω₀`, damping `D/ω₀` and synchronizing
-- coefficient `K₁` (`Matches`; `constantFlux` is the canonical one, balanced at `δ* = 0`). The two
-- plants have three and two states, so the connection is not a reading of systems: it compares the
-- denotations sentence by sentence, on the sentences the linear hub decides through the Hurwitz
-- property (`Hurwitzian`: the attractive sentences and sampled contraction), under the condition
-- `K₂K₄ = 0` (`Decoupled`: the field does not act on the torque or the angle does not act on the
-- field). On that context the characteristic polynomial is the swing polynomial times the field
-- factor `s + 1/(K₃T'_{d0})`, so the flux-decay plant is Hurwitz exactly when the matching swing
-- Jacobian is (`block`), and the two families agree on every Hurwitzian sentence (`reading`, at the
-- canonical image `canonical-reading`); at a balanced angle local exponential stability is that of
-- the nonlinear swing hub (`hub-reading`). Off the context the reading fails in both directions
-- and for every `T'_{d0}`: an undamped machine with `K₂K₄ > 0` and `K₂K₃K₄ < K₁` is attractive
-- while its swing machines are not (`undamped-witness`, `no-reading-undamped`), and a damped
-- machine with `0 < K₁ < K₂K₃K₄` is unstable while its swing machines are attractive
-- (`aperiodic-witness`, `no-reading-aperiodic`). Neither witness constrains `T'_{d0}`: a slow
-- field does not decouple (the steady-state synchronizing coefficient `K₁ − K₂K₃K₄` does not
-- depend on `T'_{d0}`). What survives of `T'_{d0} → ∞` is a threshold: for coefficients with
-- `D ≠ 0`, `K₁ ≠ 0` and `K₂K₃K₄ < K₁` when `D, K₁ > 0` (`SlowCondition`) there is `τ > 0` above
-- which every machine with these coefficients is Hurwitz exactly when its constant-flux machine is
-- (`slow-hurwitz`), so the two agree on the Hurwitzian sentences (`slow-reading`).
-- Instability, Lyapunov stability, conservation, decay rates and passivity are not compared, and
-- the requirement languages take no part (they are left empty here). Lean: `flux-linear` and
-- `swing-linear` are `Family.IsLinear.mem_den_hurwitz` (`Synchronous.FluxDecay.family_isLinear`,
-- `Synchronous.Swing.Linearized.family_isLinear`); `block` is
-- `Synchronous.FluxDecay.isHurwitz_iff_swing` (from
-- `Synchronous.FluxDecay.det_characteristicMatrix_decoupled`, itself from
-- `Synchronous.FluxDecay.det_characteristicMatrix_swing`); `canonical` is
-- `Synchronous.FluxDecay.constantFlux_matches`; `reading` is
-- `Synchronous.FluxDecay.mem_den_iff_swing` and `canonical-reading` is
-- `Synchronous.FluxDecay.mem_den_iff_constantFlux`; `hub-les` is the step of the proof of
-- `Synchronous.FluxDecay.mem_den_locallyExponentiallyStable_iff_hub` through
-- `Synchronous.Swing.exactUnder_locallyExponentiallyStable` and
-- `Synchronous.SwingParams.isHurwitz_jacobian_iff`, and `hub-reading` is that theorem;
-- `undamped-witness` is `Synchronous.FluxDecay.mem_den_not_swing_of_undamped` (from
-- `Synchronous.FluxDecay.mem_den_undamped_iff`), `aperiodic-witness` is
-- `Synchronous.FluxDecay.swing_mem_den_of_steadySync_neg` (from
-- `Synchronous.FluxDecay.mem_den_unstable`), `unstable-excludes` is
-- `GloballyExponentiallyStable.lyapunovStable`; `slow-hurwitz` is the step of the proof of
-- `Synchronous.FluxDecay.exists_Td0_mem_den_iff_constantFlux` through
-- `Synchronous.FluxDecay.mem_den_attractive_iff` (the Routh quantity a quadratic in `T'_{d0}`),
-- and `slow-reading` is that theorem. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics using (Scalars)
open import theorem.PowerSystem.Synchronous.Swing

↔-sym : {A B : Type} → A ↔ B → B ↔ A
↔-sym (f , g) = g , f

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  -- A flux-decay machine (Lean `Synchronous.FluxDecay.Model`: the data of
  -- `Synchronous.FluxDecayParametric.Params` with the sign conditions).
  record FluxMachine : Type where
    constructor fluxMachine
    field
      H D ω₀ K₁ K₂ K₃ K₄ Td0 : ℝ
      H-pos : 0r < H
      ω₀-pos : 0r < ω₀
      K₃-pos : 0r < K₃
      Td0-pos : 0r < Td0

  open FluxMachine

  -- The swing machines matching a flux-decay machine at constant flux.
  Matches : FluxMachine → SwingModel → Type
  Matches x m = (SwingParams.M (SwingModel.p m) ≡ (H x + H x) / ω₀ x)
    × (SwingParams.D (SwingModel.p m) ≡ D x / ω₀ x)
    × (syncCoeff (SwingModel.p m) (SwingModel.δ m) ≡ K₁ x)

  -- The decoupled context.
  Decoupled : FluxMachine → Type
  Decoupled x = K₂ x * K₄ x ≡ 0r

  -- A balanced selected angle of a swing machine.
  Balanced : SwingModel → Type
  Balanced m = Pe (SwingModel.p m) (SwingModel.δ m) ≡ SwingParams.Pm (SwingModel.p m)

  -- The coefficients of a machine other than `T'_{d0}`, and the conditions of the slow field.
  record Coefficients : Type where
    constructor coefficients
    field
      cH cD cω₀ cK₁ cK₂ cK₃ cK₄ : ℝ

  coefficientsOf : FluxMachine → Coefficients
  coefficientsOf x = coefficients (H x) (D x) (ω₀ x) (K₁ x) (K₂ x) (K₃ x) (K₄ x)

  SlowCondition : Coefficients → Type
  SlowCondition k = (0r < Coefficients.cH k) × (0r < Coefficients.cω₀ k)
    × (0r < Coefficients.cK₃ k) × (¬ (Coefficients.cD k ≡ 0r)) × (¬ (Coefficients.cK₁ k ≡ 0r))
    × (0r < Coefficients.cD k → 0r < Coefficients.cK₁ k →
        Coefficients.cK₂ k * Coefficients.cK₃ k * Coefficients.cK₄ k < Coefficients.cK₁ k)

  -- The canonical constant-flux machine: the curve `K₁ sin δ` read at `δ* = 0`.
  constantFlux : FluxMachine → SwingModel
  constantFlux x =
    swingModel (swingParams ((H x + H x) / ω₀ x) (D x / ω₀ x) 0r 0r (K₁ x) 0r) 0r

  module Reading (S : Semantics) where
    open Semantics S
    open Readings S

    module _
      -- The Hurwitzian sentences, local and global exponential stability, instability.
      (Hurwitzian : Sentence → Type) (les ges unstable : Sentence)
      -- The port systems of the flux-decay plants and of the linearized swing plants, and the
      -- swing hub's systems (fields at the selected point).
      (fluxSystem : FluxMachine → System) (linSystem hubSystem : SwingModel → System)
      -- Hurwitz state matrices: the flux-decay plant's and the swing Jacobian's.
      (HurwitzF : FluxMachine → Type) (HurwitzJ : SwingModel → Type)
      where

      flux lin hub : Family
      flux = record
        { Model = FluxMachine ; Req = ⊥ ; system = fluxSystem ; meets = λ _ ()
        ; translate = λ _ () }
      lin = record
        { Model = SwingModel ; Req = ⊥ ; system = linSystem ; meets = λ _ () ; translate = λ _ () }
      hub = record
        { Model = SwingModel ; Req = ⊥ ; system = hubSystem ; meets = λ _ () ; translate = λ _ () }

      -- What Lean proves.
      record Obligations : Type where
        field
          les-hurwitzian : Hurwitzian les
          ges-hurwitzian : Hurwitzian ges
          flux-linear : (s : Sentence) → Hurwitzian s → (x : FluxMachine) →
            den flux s x ↔ HurwitzF x
          swing-linear : (s : Sentence) → Hurwitzian s → (m : SwingModel) →
            den lin s m ↔ HurwitzJ m
          block : (x : FluxMachine) (m : SwingModel) → Matches x m → Decoupled x →
            HurwitzF x ↔ HurwitzJ m
          canonical : (x : FluxMachine) → Matches x (constantFlux x) × Balanced (constantFlux x)
          hub-les : (x : FluxMachine) (m : SwingModel) → Matches x m → Balanced m →
            den hub les m ↔ HurwitzJ m
          unstable-excludes : (x : FluxMachine) → den flux unstable x → ¬ den flux ges x
          undamped-witness : (x : FluxMachine) (m : SwingModel) → Matches x m → D x ≡ 0r →
            0r < K₂ x * K₄ x → K₂ x * K₃ x * K₄ x < K₁ x → den flux ges x × (¬ den lin ges m)
          aperiodic-witness : (x : FluxMachine) (m : SwingModel) → Matches x m → 0r < D x →
            0r < K₁ x → K₁ x < K₂ x * K₃ x * K₄ x → den lin ges m × den flux unstable x
          slow-hurwitz : (k : Coefficients) → SlowCondition k →
            Σ[ τ ∈ ℝ ] (0r < τ) × ((x : FluxMachine) → coefficientsOf x ≡ k → τ < Td0 x →
              HurwitzF x ↔ HurwitzJ (constantFlux x))

      module _ (ob : Obligations) where
        open Obligations ob

        -- On the decoupled context the two families agree on every Hurwitzian sentence.
        reading : (x : FluxMachine) (m : SwingModel) → Matches x m → Decoupled x →
          (s : Sentence) → Hurwitzian s → den flux s x ↔ den lin s m
        reading x m p d s h =
          ↔-trans (flux-linear s h x) (↔-trans (block x m p d) (↔-sym (swing-linear s h m)))

        canonical-reading : (x : FluxMachine) → Decoupled x → (s : Sentence) → Hurwitzian s →
          den flux s x ↔ den lin s (constantFlux x)
        canonical-reading x d = reading x (constantFlux x) (fst (canonical x)) d

        -- At a balanced angle local exponential stability is the swing hub's.
        hub-reading : (x : FluxMachine) (m : SwingModel) → Matches x m → Balanced m →
          Decoupled x → den flux les x ↔ den hub les m
        hub-reading x m p b d =
          ↔-trans (flux-linear les les-hurwitzian x)
            (↔-trans (block x m p d) (↔-sym (hub-les x m p b)))

        -- Off the context the reading fails: the undamped machine damped by its flux decay.
        no-reading-undamped : (x : FluxMachine) (m : SwingModel) → Matches x m → D x ≡ 0r →
          0r < K₂ x * K₄ x → K₂ x * K₃ x * K₄ x < K₁ x →
          ¬ ((s : Sentence) → Hurwitzian s → den flux s x ↔ den lin s m)
        no-reading-undamped x m p d c k r =
          snd w (fst (r ges ges-hurwitzian) (fst w))
          where
            w = undamped-witness x m p d c k

        -- And the damped machine that loses its steady-state synchronizing torque.
        no-reading-aperiodic : (x : FluxMachine) (m : SwingModel) → Matches x m → 0r < D x →
          0r < K₁ x → K₁ x < K₂ x * K₃ x * K₄ x →
          ¬ ((s : Sentence) → Hurwitzian s → den flux s x ↔ den lin s m)
        no-reading-aperiodic x m p d k a r =
          unstable-excludes x (snd w) (snd (r ges ges-hurwitzian) (fst w))
          where
            w = aperiodic-witness x m p d k a

        -- What survives of a slow field: a threshold above which the constant-flux verdict holds.
        slow-reading : (k : Coefficients) → SlowCondition k →
          Σ[ τ ∈ ℝ ] (0r < τ) × ((x : FluxMachine) → coefficientsOf x ≡ k → τ < Td0 x →
            (s : Sentence) → Hurwitzian s → den flux s x ↔ den lin s (constantFlux x))
        slow-reading k c =
          let (τ , hτ , below) = slow-hurwitz k c
          in τ , hτ , λ x p t s h → ↔-trans (flux-linear s h x)
               (↔-trans (below x p t) (↔-sym (swing-linear s h (constantFlux x))))
