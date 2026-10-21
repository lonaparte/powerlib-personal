{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.VoltageLimit where

-- Scaffold of the PI current loop under the inverter's modulation voltage limit, as an
-- implementation of the PI loop: the model is the single-axis PI current loop
-- (`CurrentControl.PIParams.family`); its implementation `CurrentControl.LimitedPI` holds the
-- reference `i*` constant and applies only `sat_{V_max}(u)`, `V_max = V_dc/√3`, the hardware
-- limit of the linear modulation range, read about the operating point `(i*, R i*/K_i)`; each
-- platform realizes its design (`ofDesign`, design map `(design, i*, V_dc) ↦ design`). The local
-- sentences (Lyapunov stability, local asymptotic and local exponential stability, instability)
-- depend only on the field near the point. With integral action (`K_i ≠ 0`, the integrator holds
-- the operating point) and headroom (`|R i*| < V_max`) the command is in range near the point, so
-- the platform is there the design's linear loop: every local sentence is realized exactly within
-- `{integral, headroom}`, for every sign of `L` (`exact-local`). Within `{headroom}` alone the
-- local attractive sentences are realized soundly, since a stable design has integral action
-- (`sound-attractive`). Without integral action Lyapunov stability is not realized soundly nor
-- instability completely: a drifting design (`K_p = K_i = 0`) is Lyapunov stable while its
-- platform, whose operating point is not an equilibrium, is unstable (`not-sound-lyapunov`,
-- `not-complete-unstable`, within `{inductance, dcLink, headroom}`). Overload
-- (`V_max < |R i*|`, with `L > 0`, `K_i ≠ 0`, `V_dc > 0`) makes every platform unstable, whatever
-- the design: instability is realized soundly and local exponential stability is not
-- (`sound-overload`, `not-sound-overload`, the nominal design `L = R = K_p = K_i = 1` at `i* = 1`,
-- `V_dc = 1`). No platform is globally exponentially stable, the limit bounding how fast a large
-- integrator state unwinds; so global exponential stability is not realized soundly within all
-- realistic constraints with headroom (`not-sound-global`, the nominal design at `i* = 0`,
-- `V_dc = 1`) and is realized completely only vacuously (`complete-global`). Lean
-- (`theorem/CurrentControl/VoltageLimit.lean`): `locality` is `Dynamics.holds_congr_nhds` with
-- the platform field equal, near the operating point, to the design's linear zero-input field
-- (`CurrentControl.LimitedPI.family_isAutonomous` and `CurrentControl.PIParams.family_isLinear`
-- read by `Family.IsAutonomous.mem_den_flow`, `Family.IsLinear.mem_den_flow`), `design-reading`
-- is `CurrentControl.PIParams.exact`,
-- `overload-unstable` is `CurrentControl.LimitedPI.mem_den_unstable_of_overload`, `no-global` is
-- `CurrentControl.LimitedPI.not_mem_den_globallyExponentiallyStable`, `exclusive` is the
-- definition of instability (not Lyapunov stable), `exponential-lyapunov` is
-- `LocallyExponentiallyStable.lyapunovStable`; the witnesses are
-- `CurrentControl.LimitedPI.drifting` (`drifting_design_mem_den_lyapunovStable`,
-- `drifting_mem_den_unstable`), `CurrentControl.LimitedPI.nominal` (`nominal_mem_den`),
-- `CurrentControl.LimitedPI.overloaded` and `CurrentControl.LimitedPI.unloaded`. The laws:
-- `exact-local` is `CurrentControl.LimitedPI.realizationExactUnder_local`, `sound-attractive` is
-- `CurrentControl.LimitedPI.realizationSoundUnder_attractive` (Lean reduces it statically,
-- `Implementation.realizationSoundUnder_of_design`, through the sound platform translation
-- `CurrentControl.LimitedPI.chain_le_semantics`; the scaffold goes through locality),
-- `not-sound-lyapunov` is `CurrentControl.LimitedPI.not_realizationSoundUnder_lyapunovStable`,
-- `not-complete-unstable` is `CurrentControl.LimitedPI.not_realizationCompleteUnder_unstable`,
-- `sound-overload` is `CurrentControl.LimitedPI.realizationSoundUnder_unstable_of_overload`,
-- `not-sound-overload` is
-- `CurrentControl.LimitedPI.not_realizationSoundUnder_locallyExponentiallyStable`,
-- `not-sound-global` is
-- `CurrentControl.LimitedPI.not_realizationSoundUnder_globallyExponentiallyStable`,
-- `complete-global` is
-- `CurrentControl.LimitedPI.realizationCompleteUnder_globallyExponentiallyStable`. Nothing here
-- is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥) renaming (elim to ⊥-elim)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.Realization

-- The requirement language of the PI design family (`Spectral.Requirement`).
data LinearReq : Type where
  stable unstable' : LinearReq

-- The platform requirements (Lean `LimitRequirement`): the lifted design requirements, `0 < L`,
-- `K_i ≠ 0`, `0 < V_dc`, headroom `|R i*| < V_dc/√3` and overload `V_dc/√3 < |R i*|`.
data LimitReq : Type where
  design : LinearReq → LimitReq
  inductance integral dcLink headroom overload : LimitReq

-- The local sentences.
data Local : Type where
  lyapunov asymptotic exponential instability : Local

-- The local attractive sentences.
Attractive : Local → Type
Attractive asymptotic = Unit
Attractive exponential = Unit
Attractive _ = ⊥

-- The contexts of the connection: `{integral, headroom}`, `{headroom}`, the realistic constraints
-- without integral action `{inductance, dcLink, headroom}`, with overload
-- `{inductance, integral, dcLink, overload}`, and with headroom
-- `{inductance, integral, dcLink, headroom}`.
localContext headroomOnly noIntegral overloadContext realistic : LimitReq → Type
localContext integral = Unit
localContext headroom = Unit
localContext _ = ⊥
headroomOnly headroom = Unit
headroomOnly _ = ⊥
noIntegral inductance = Unit
noIntegral dcLink = Unit
noIntegral headroom = Unit
noIntegral _ = ⊥
overloadContext inductance = Unit
overloadContext integral = Unit
overloadContext dcLink = Unit
overloadContext overload = Unit
overloadContext _ = ⊥
realistic inductance = Unit
realistic integral = Unit
realistic dcLink = Unit
realistic headroom = Unit
realistic _ = ⊥

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (PIParams Operating : Type)
    (designSystem : PIParams → System) (platformSystem : PIParams → Operating → System)
    -- The local sentences and global exponential stability.
    (sentence : Local → Sentence) (global : Sentence)
    -- Designs: stable, unstable, `0 < L`, `K_i ≠ 0`; operating points `(i*, V_dc)`:
    -- `0 < V_dc`; platforms: headroom and overload.
    (Stable Unstable Inductance Integral : PIParams → Type) (DCLink : Operating → Type)
    (Headroom Overload : PIParams → Operating → Type)
    where

    -- What Lean proves.
    record Obligations : Type where
      field
        locality : (k : Local) (p : PIParams) (o : Operating) → Integral p → Headroom p o →
          holds (platformSystem p o) (sentence k) ↔ holds (designSystem p) (sentence k)
        design-reading : (k : Local) → Attractive k → (p : PIParams) →
          holds (designSystem p) (sentence k) → Stable p
        stable-integral : (p : PIParams) → Stable p → Integral p
        overload-unstable : (p : PIParams) (o : Operating) → Inductance p → Integral p →
          DCLink o → Overload p o → holds (platformSystem p o) (sentence instability)
        no-global : (p : PIParams) (o : Operating) → ¬ holds (platformSystem p o) global
        exclusive : (a : System) → holds a (sentence lyapunov) →
          ¬ holds a (sentence instability)
        exponential-lyapunov : (a : System) → holds a (sentence exponential) →
          holds a (sentence lyapunov)
        -- The drifting platform: no integral action, with headroom.
        drifting : PIParams
        driftPoint : Operating
        drift-inductance : Inductance drifting
        drift-dcLink : DCLink driftPoint
        drift-headroom : Headroom drifting driftPoint
        drift-design : holds (designSystem drifting) (sentence lyapunov)
        drift-unstable : holds (platformSystem drifting driftPoint) (sentence instability)
        -- The nominal design, overloaded (`i* = 1`) and unloaded (`i* = 0`).
        nominal : PIParams
        overloaded unloaded : Operating
        nominal-inductance : Inductance nominal
        nominal-integral : Integral nominal
        nominal-exponential : holds (designSystem nominal) (sentence exponential)
        nominal-global : holds (designSystem nominal) global
        overloaded-dcLink : DCLink overloaded
        overloaded-overload : Overload nominal overloaded
        unloaded-dcLink : DCLink unloaded
        unloaded-headroom : Headroom nominal unloaded

    Platform : Type
    Platform = PIParams × Operating

    designMeets : PIParams → LinearReq → Type
    designMeets p stable = Stable p
    designMeets p unstable' = Unstable p

    platformMeets : Platform → LimitReq → Type
    platformMeets (p , o) (design q) = designMeets p q
    platformMeets (p , o) inductance = Inductance p
    platformMeets (p , o) integral = Integral p
    platformMeets (p , o) dcLink = DCLink o
    platformMeets (p , o) headroom = Headroom p o
    platformMeets (p , o) overload = Overload p o

    -- The two families; their translations are their own and do not enter the realization laws.
    designFamily : Family
    designFamily = record
      { Model = PIParams ; Req = LinearReq ; system = designSystem ; meets = designMeets
      ; translate = λ _ _ → ⊥ }

    platform : Family
    platform = record
      { Model = Platform ; Req = LimitReq ; system = λ y → platformSystem (fst y) (snd y)
      ; meets = platformMeets ; translate = λ _ _ → ⊥ }

    open Design designFamily platform fst

    module _ (ob : Obligations) where
      open Obligations ob

      -- Within integral action and headroom every local sentence is realized exactly: near the
      -- operating point the limit is inactive.
      exact-local : (k : Local) → ExactUnder' designed localContext (sentence k)
      exact-local k = exactUnder-of-reading (realize platform localContext) (sentence k)
        (λ y h → locality k (fst y) (snd y) (h integral tt) (h headroom tt))

      -- Within headroom alone the local attractive sentences are realized soundly: a stable
      -- design has integral action.
      sound-attractive : (k : Local) → Attractive k → SoundUnder designed headroomOnly (sentence k)
      sound-attractive k a (p , o) h c =
        let d = fst (certified↔ (sentence k) (p , o)) c
        in snd (locality k p o (stable-integral p (design-reading k a p d)) (h headroom tt)) d

      -- Without integral action Lyapunov stability is not realized soundly, nor instability
      -- completely.
      drift-context : realize platform noIntegral (drifting , driftPoint)
      drift-context inductance _ = drift-inductance
      drift-context dcLink _ = drift-dcLink
      drift-context headroom _ = drift-headroom
      drift-context (design _) ()
      drift-context integral ()
      drift-context overload ()

      not-sound-lyapunov : ¬ SoundUnder designed noIntegral (sentence lyapunov)
      not-sound-lyapunov = not-sound-of-witness designed (drifting , driftPoint) drift-context
        (snd (certified↔ (sentence lyapunov) (drifting , driftPoint)) drift-design)
        (λ h → exclusive _ h drift-unstable)

      not-complete-unstable : ¬ CompleteUnder designed noIntegral (sentence instability)
      not-complete-unstable h = exclusive (designSystem drifting) drift-design
        (fst (certified↔ (sentence instability) (drifting , driftPoint))
          (h (drifting , driftPoint) drift-context drift-unstable))

      -- Overload makes every platform unstable: instability is realized soundly, local
      -- exponential stability is not.
      sound-overload : SoundUnder designed overloadContext (sentence instability)
      sound-overload (p , o) h _ =
        overload-unstable p o (h inductance tt) (h integral tt) (h dcLink tt) (h overload tt)

      overload-context : realize platform overloadContext (nominal , overloaded)
      overload-context inductance _ = nominal-inductance
      overload-context integral _ = nominal-integral
      overload-context dcLink _ = overloaded-dcLink
      overload-context overload _ = overloaded-overload
      overload-context (design _) ()
      overload-context headroom ()

      not-sound-overload : ¬ SoundUnder designed overloadContext (sentence exponential)
      not-sound-overload = not-sound-of-witness designed (nominal , overloaded) overload-context
        (snd (certified↔ (sentence exponential) (nominal , overloaded)) nominal-exponential)
        (λ h → exclusive _ (exponential-lyapunov _ h)
          (overload-unstable nominal overloaded nominal-inductance nominal-integral
            overloaded-dcLink overloaded-overload))

      -- Global exponential stability is not realized soundly within the realistic constraints
      -- with headroom; it is realized completely only vacuously.
      unloaded-context : realize platform realistic (nominal , unloaded)
      unloaded-context inductance _ = nominal-inductance
      unloaded-context integral _ = nominal-integral
      unloaded-context dcLink _ = unloaded-dcLink
      unloaded-context headroom _ = unloaded-headroom
      unloaded-context (design _) ()
      unloaded-context overload ()

      not-sound-global : ¬ SoundUnder designed realistic global
      not-sound-global = not-sound-of-witness designed (nominal , unloaded) unloaded-context
        (snd (certified↔ global (nominal , unloaded)) nominal-global) (no-global nominal unloaded)

      complete-global : CompleteUnder designed (λ _ → ⊥) global
      complete-global (p , o) _ h = ⊥-elim (no-global p o h)
