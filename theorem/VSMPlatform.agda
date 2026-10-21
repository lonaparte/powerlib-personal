{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.VSMPlatform where

-- Scaffold of the VSM with a first-order power filter on a test platform, a four-layer stack
-- (`VSMLPF.stack` of `theorem/GFM/VSMLPFRig.lean`, read as in `theorem/Stack/Basic.lean`): T the
-- sentences, M the VSM + power-filter models (`GFM.VSMLPF.family`), I the platforms
-- (`VSMLPF.rigFamily`: a design model and an execution delay `τ`, the first-order equivalent of
-- computation delay and PWM update), O the identification records (`VSMLPF.Record`: intervals of
-- `M, D, ω_c, K` and a delay bound `τ_hi`). A platform realizes its design model (`ofDesign`,
-- design map `(m, τ) ↦ m`) and may produce the records of `VSMLPF.Produces`. The record layer of
-- a stack is generic (`Stacks`: inference, certification, truth, prediction and their laws).
-- M–I. Within a physical design, a positive delay and the fast-delay constraint `fastLag`, a
-- platform with a locally exponentially stable design is locally exponentially stable
-- (`sound-fast`: the design side is the exact model translation, the platform side the sound
-- platform translation, and between them fast filter and fast delay give the platform Routh
-- condition `H > 0`); within a physical design and a positive delay, for every delay, a locally
-- exponentially stable platform has a locally exponentially stable design (`complete-lag`: `H > 0`
-- forces the fast-filter margin, a delay never stabilizes); so the realization is exact within
-- `fastLag` (`exact-fast`) and not sound without it (`not-sound-lag`, the witness `slowRig`, a
-- stable design with `H = −1`). Instability is realized soundly within a physical destabilizing
-- design, for every delay (`sound-unstable`). T–O. A record passing the worst-corner fast-filter
-- check supports local exponential stability of every realized model (`les-infer`, through the
-- organized seed) and is certified for it (`les-certified`, the whole-chain Galois connection);
-- with the delay check the sentence is true of every producing platform (`les-truth`, through
-- `sound-fast`); without it the inference is about the models only (`lagFree-gap`: `lagFree` is
-- produced by `slowRig`). A slow-filter record supports instability of the models and of every
-- producer (`unstable-infer`, `unstable-truth`), lies outside the records predicted by local
-- exponential stability (`not-predicted`) and so refutes it for every producer (`refuted`).
-- Lean. Generic (`theorem/Stack/Basic.lean`): `Infer`, `CertifiedRecords`, `Truth`, `Predicted`
-- are `Stack.mem_infer`, `Stack.mem_certified`, `Stack.mem_truth`, `Stack.mem_predicted`;
-- `galois` is `Stack.subset_certified_iff`, `infer-of-organized` is `Stack.mem_infer_of_organized`,
-- `truth-of-infer` is `Stack.infer_subset_truth`, `refutes` is `Stack.refutes`. Obligations: the
-- model laws `model-exactUnder`, `model-sound` are `VSMLPF.exactUnder_locallyExponentiallyStable`,
-- `VSMLPF.chain_le_semantics`; the platform laws `rig-sound`, `rig-exactUnder` are
-- `VSMLPF.rig_chain_le_semantics`, `VSMLPF.rig_exactUnder_locallyExponentiallyStable`;
-- `fast-routh` and `routh-margin` are the private `H_pos_of_fastLag`, `margin_pos_of_H_pos`;
-- `unstable-of-destabilizing` is the proof of `VSMLPF.realizationSoundUnder_unstable` (private
-- `H_neg_of_slow`, `VSMLPF.rigField_point_eq_zero_iff`); `unstable-excludes` is
-- `LocallyExponentiallyStable.lyapunovStable`; `slow-design`, `slow-unstable` are
-- `VSMLPF.slowRig_design_mem_den`, `VSMLPF.slowRig_mem_den_unstable`; `model-check`, `lag-check`,
-- `slow-check` are the private `design_fast_of_modelCheck`, `fastLag_of_lagCheck`,
-- `design_slow_of_slowCheck` (`slow-context` reads `VSMLPF.Produces` as well);
-- `slow-produces` is `VSMLPF.slowRig_produces`. Derived: `sound-fast` is
-- `VSMLPF.realizationSoundUnder_locallyExponentiallyStable` (through
-- `Implementation.realizationSoundUnder_of_design`), `complete-lag` is
-- `VSMLPF.realizationCompleteUnder_locallyExponentiallyStable`, `exact-fast` is
-- `VSMLPF.realizationExactUnder_locallyExponentiallyStable`, `not-sound-lag` is
-- `VSMLPF.not_realizationSoundUnder_locallyExponentiallyStable` (through
-- `Implementation.not_realizationSoundUnder_of_design`), `sound-unstable` is
-- `VSMLPF.realizationSoundUnder_unstable`, `les-infer` is
-- `VSMLPF.locallyExponentiallyStable_mem_infer`, `les-certified` is
-- `VSMLPF.mem_certified_locallyExponentiallyStable`, `les-truth` is
-- `VSMLPF.locallyExponentiallyStable_mem_truth`, `lagFree-gap` is
-- `VSMLPF.lagFreeRecord_infer_not_truth`, `unstable-infer`, `unstable-truth` are
-- `VSMLPF.unstable_mem_infer`, `VSMLPF.unstable_mem_truth`, `not-predicted` is
-- `VSMLPF.not_mem_predicted_locallyExponentiallyStable` (`refuted` is its reading by
-- `Stack.refutes`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.Realization
open import theorem.Swing using (only)

-- The record layer of a stack: records `V` that implementations may produce
-- (`Stack.produces`), over an implementation layer.
module Stacks (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (L : Implementation) {V : Type}
    (produces : Family.Model (Implementation.impl L) → V → Type) where
    open Implementation L

    -- Data-driven inference, the whole backward traversal: the sentences every model realized by
    -- a possible producer of a record of `D` satisfies.
    Infer : (V → Type) → Sentence → Type
    Infer D s = (v : V) → D v → (y : Family.Model impl) → produces y v → Certified L s y

    -- Theory-driven certification: the records all of whose possible producers realize only
    -- models of `Φ`.
    CertifiedRecords : (Sentence → Type) → V → Type
    CertifiedRecords Φ v = (y : Family.Model impl) → produces y v →
      (x : Family.Model model) → realizes x y → (s : Sentence) → Φ s → den model s x

    -- The truth at the implementation layer: the sentences every possible producer satisfies.
    Truth : (V → Type) → Sentence → Type
    Truth D s = (v : V) → D v → (y : Family.Model impl) → produces y v → den impl s y

    -- The records predicted by `s`: those some implementation satisfying `s` may produce.
    Predicted : Sentence → V → Type
    Predicted s v = Σ[ y ∈ Family.Model impl ] den impl s y × produces y v

    -- The whole-chain Galois connection: records support sentences exactly when they are
    -- certified for them.
    galois : (D : V → Type) (Φ : Sentence → Type) →
      ((v : V) → D v → CertifiedRecords Φ v) ↔ ((s : Sentence) → Φ s → Infer D s)
    galois D Φ =
      (λ h s φ v d y p x r → h v d y p x r s φ) , (λ h v d y p x r s φ → h s φ v d y p x r)

    -- Inference through the requirement language of the models and a sound translation.
    infer-of-organized : {D : V → Type} {s : Sentence} → Sound model s →
      ((v : V) → D v → (y : Family.Model impl) → produces y v → (x : Family.Model model) →
        realizes x y → realize model (Family.translate model s) x) → Infer D s
    infer-of-organized hS h v d y p x r = hS x (h v d y p x r)

    -- Under realization soundness, with every possible producer within the constraints, the
    -- inferred sentences are true of the implementations.
    truth-of-infer : {Δ : Family.Req impl → Type} {D : V → Type} {s : Sentence} →
      ((v : V) → D v → (y : Family.Model impl) → produces y v → realize impl Δ y) →
      SoundUnder L Δ s → Infer D s → Truth D s
    truth-of-infer hΔ hS hs v d y p = hS y (hΔ v d y p) (hs v d y p)

    -- A record outside the predicted records refutes the sentence for every producer.
    refutes : {s : Sentence} {y : Family.Model impl} {v : V} → produces y v →
      ¬ Predicted s v → ¬ den impl s y
    refutes p hv hs = hv (_ , hs , p)

open import theorem.FlowSemantics using (Sentence; locallyExponentiallyStable; unstable)

-- The platform requirements: the lifted design requirements and the realistic constraints
-- (`VSMLPF.RigRequirement`).
data RigReq (Q : Type) : Type where
  design : Q → RigReq Q
  lag routh lagged fastLag : RigReq Q

module _ (Sys : Type) (holds : Sys → Sentence → Type) where

  platformSemantics : Semantics
  platformSemantics = record { System = Sys ; Sentence = Sentence ; holds = holds }

  open Readings platformSemantics
  open Realizations platformSemantics
  open Stacks platformSemantics

  module _
    -- The model layer: models, systems, requirement language and translation
    -- (`GFM.VSMLPF.family`), with the physical (`M, D, ω_c > 0`) and destabilizing designs.
    (Model Req : Type) (modelSystem : Model → Sys) (meets : Model → Req → Type)
    (translate : Sentence → Req → Type) (physical destabilizing : Req)
    -- The platform layer: delays, the platform system about `(δ*, 0, P₀, δ*)`, the conditions
    -- `0 < τ`, `0 < H`, `H < 0 ∨ K < 0`, `fastLag`, and the platform translation.
    (Delay : Type) (rigSystem : Model × Delay → Sys) (Lag : Delay → Type)
    (Routh Lagged FastLag : Model × Delay → Type) (rigTranslate : Sentence → RigReq Req → Type)
    where

    model : Family
    model = record
      { Model = Model ; Req = Req ; system = modelSystem ; meets = meets ; translate = translate }

    Rig : Type
    Rig = Model × Delay

    rigMeets : Rig → RigReq Req → Type
    rigMeets y (design q) = meets (fst y) q
    rigMeets y lag = Lag (snd y)
    rigMeets y routh = Routh y
    rigMeets y lagged = Lagged y
    rigMeets y fastLag = FastLag y

    rig : Family
    rig = record
      { Model = Rig ; Req = RigReq Req ; system = rigSystem ; meets = rigMeets
      ; translate = rigTranslate }

    open Design model rig fst

    -- The contexts: `{design physical, lag}`, with `fastLag`, and with `design destabilizing`.
    Δlag Δfast Δunst : RigReq Req → Type
    Δlag r = (r ≡ design physical) ⊎ (r ≡ lag)
    Δfast r = Δlag r ⊎ (r ≡ fastLag)
    Δunst r = Δlag r ⊎ (r ≡ design destabilizing)

    -- The observation layer: records, production, the static checks of records, the slow
    -- platform (`VSMLPF.slowRig`) and the record it may produce (`VSMLPF.lagFreeRecord`).
    module _ (Record : Type) (produces : Rig → Record → Type)
      (ModelCheck LagCheck SlowCheck : Record → Type) (slowRig : Rig) (lagFree : Record)
      where

      -- What Lean proves.
      record Obligations : Type where
        field
          model-exactUnder : ExactUnder model (only physical) locallyExponentiallyStable
          model-sound : (s : Sentence) → Sound model s
          rig-sound : (s : Sentence) → Sound rig s
          rig-exactUnder : ExactUnder rig Δlag locallyExponentiallyStable
          fast-routh : (y : Rig) → realize rig Δfast y →
            realize model (translate locallyExponentiallyStable) (fst y) →
            realize rig (rigTranslate locallyExponentiallyStable) y
          routh-margin : (y : Rig) → realize rig Δlag y →
            realize rig (rigTranslate locallyExponentiallyStable) y →
            realize model (translate locallyExponentiallyStable) (fst y)
          unstable-of-destabilizing : (y : Rig) → realize rig Δunst y → den rig unstable y
          unstable-excludes : (a : Sys) → holds a unstable → ¬ holds a locallyExponentiallyStable
          slow-lag : realize rig Δlag slowRig
          slow-design : den model locallyExponentiallyStable (fst slowRig)
          slow-unstable : den rig unstable slowRig
          model-check : (v : Record) → ModelCheck v → (y : Rig) → produces y v →
            realize model (translate locallyExponentiallyStable) (fst y)
          lag-check : (v : Record) → ModelCheck v → LagCheck v → (y : Rig) → produces y v →
            realize rig Δfast y
          slow-check : (v : Record) → SlowCheck v → (y : Rig) → produces y v →
            realize model (translate unstable) (fst y)
          slow-context : (v : Record) → SlowCheck v → (y : Rig) → produces y v →
            realize rig Δunst y
          lagFree-check : ModelCheck lagFree
          slow-produces : produces slowRig lagFree

      module _ (ob : Obligations) where
        open Obligations ob

        les : Sentence
        les = locallyExponentiallyStable

        physicalOf : (y : Rig) → realize rig Δlag y → realize model (only physical) (fst y)
        physicalOf y h q e = subst (meets (fst y)) (sym e) (h (design physical) (inl refl))

        lagOf : (y : Rig) → realize rig Δfast y → realize rig Δlag y
        lagOf y h r e = h r (inl e)

        -- M–I: sound within `fastLag`, complete for every delay, exact within `fastLag`.
        sound-fast : SoundUnder designed Δfast les
        sound-fast y hΔ hc = rig-sound les y (fast-routh y hΔ
          (snd (model-exactUnder (fst y) (physicalOf y (lagOf y hΔ))) (fst (certified↔ les y) hc)))

        complete-lag : CompleteUnder designed Δlag les
        complete-lag y hΔ hd = snd (certified↔ les y)
          (model-sound les (fst y) (routh-margin y hΔ (snd (rig-exactUnder y hΔ) hd)))

        exact-fast : ExactUnder' designed Δfast les
        exact-fast y hΔ = sound-fast y hΔ , complete-lag y (lagOf y hΔ)

        -- Without `fastLag` the realization is not sound.
        not-sound-lag : ¬ SoundUnder designed Δlag les
        not-sound-lag = not-sound-of-witness designed slowRig slow-lag
          (snd (certified↔ les slowRig) slow-design)
          (unstable-excludes (rigSystem slowRig) slow-unstable)

        -- Instability is realized soundly within a physical destabilizing design, for every
        -- delay.
        sound-unstable : SoundUnder designed Δunst unstable
        sound-unstable y hΔ _ = unstable-of-destabilizing y hΔ

        -- T–O: inference, certification and truth of local exponential stability.
        les-infer : (v : Record) → ModelCheck v → Infer designed produces (only v) les
        les-infer v h = infer-of-organized designed produces (model-sound les)
          (λ w e y p x r → subst (realize model (translate les)) r
            (model-check v h y (subst (produces y) e p)))

        les-certified : (v : Record) → ModelCheck v →
          CertifiedRecords designed produces (only les) v
        les-certified v h = snd (galois designed produces (only v) (only les))
          (λ s e → subst (Infer designed produces (only v)) (sym e) (les-infer v h)) v refl

        les-truth : (v : Record) → ModelCheck v → LagCheck v → Truth designed produces (only v) les
        les-truth v hm hl = truth-of-infer designed produces
          (λ w e y p → lag-check v hm hl y (subst (produces y) e p)) sound-fast (les-infer v hm)

        -- Without the delay check the data-driven conclusion is about the models only.
        lagFree-gap : Infer designed produces (only lagFree) les
          × (¬ Truth designed produces (only lagFree) les)
        lagFree-gap = les-infer lagFree lagFree-check
          , λ t → unstable-excludes (rigSystem slowRig) slow-unstable
              (t lagFree refl slowRig slow-produces)

        -- T–O: instability of slow-filter records, and refutation.
        unstable-infer : (v : Record) → SlowCheck v → Infer designed produces (only v) unstable
        unstable-infer v h = infer-of-organized designed produces (model-sound unstable)
          (λ w e y p x r → subst (realize model (translate unstable)) r
            (slow-check v h y (subst (produces y) e p)))

        unstable-truth : (v : Record) → SlowCheck v → Truth designed produces (only v) unstable
        unstable-truth v h = truth-of-infer designed produces
          (λ w e y p → slow-context v h y (subst (produces y) e p)) sound-unstable
          (unstable-infer v h)

        not-predicted : (v : Record) → SlowCheck v → ¬ Predicted designed produces les v
        not-predicted v h (y , hy , p) =
          unstable-excludes (rigSystem y) (unstable-truth v h v refl y p) hy

        refuted : (v : Record) → SlowCheck v → (y : Rig) → produces y v → ¬ den rig les y
        refuted v h y p = refutes designed produces p (not-predicted v h)
