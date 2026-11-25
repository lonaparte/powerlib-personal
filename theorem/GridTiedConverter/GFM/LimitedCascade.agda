{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.LimitedCascade where
-- Lean modules: theorem.GridTiedConverter.GFM.LimitedCascade

-- Scaffold of the grid-forming inner cascade under the inverter's modulation voltage limit, as
-- an implementation of the cascade: the model is the single-axis voltage/current cascade
-- (`GFM.InnerCascade.family`); its implementation `GFM.LimitedCascade` holds the voltage
-- reference `v*` constant and applies only the saturated bridge voltage `sat_{V_max}(e)`,
-- `V_max = V_dc/√3`, the hardware limit of the linear modulation range, read about the operating
-- point `(0, 0, v*, 0)`; each platform realizes its design (`ofDesign`, design map
-- `(design, v*, V_dc) ↦ design`). The local sentences (Lyapunov stability, local asymptotic and
-- local exponential stability, instability) depend only on the field near the point. With
-- headroom (`|v*| < V_max`) the bridge command is in range near the point, so the platform is
-- there the design's linear loop: every local sentence is realized exactly within `{headroom}`,
-- for every parameter sign (`exact-local`; the operating point is an equilibrium of every design,
-- so no integral-action constraint is needed, unlike
-- `theorem/GridTiedConverter/CurrentControl/VoltageLimit.agda`). Overload (`V_max < |v*|`, with
-- `L, C > 0`, `V_dc > 0`) makes every platform unstable, whatever the design: instability is
-- realized soundly and local exponential stability is not (`sound-overload`,
-- `not-sound-overload`, the IMC design `L = R = C = ω_c = K_pv = 1`, `K_iv = 1/2` at `v* = 1`,
-- `V_dc = 1`). No platform is globally exponentially stable, the limit bounding how fast a large
-- integrator state unwinds; so global exponential stability is not realized soundly within all
-- realistic constraints with headroom (`not-sound-global`, the same design at `v* = 0`,
-- `V_dc = 1`) and is realized completely only vacuously (`complete-global`). Lean
-- (`theorem/GridTiedConverter/GFM/LimitedCascade.lean`): `locality` is
-- `Dynamics.holds_congr_nhds` with the platform field equal, near the operating point, to the
-- design's linear zero-input field (`GFM.LimitedCascade.family_isAutonomous` and
-- `GFM.InnerCascade.family_isLinear` read by `Family.IsAutonomous.mem_den_flow`,
-- `Family.IsLinear.mem_den_flow`), `overload-unstable` is
-- `GFM.LimitedCascade.mem_den_unstable_of_overload`, `no-global` is
-- `GFM.LimitedCascade.not_mem_den_globallyExponentiallyStable`, `exclusive` is the definition of
-- instability (not Lyapunov stable), `exponential-lyapunov` is
-- `LocallyExponentiallyStable.lyapunovStable`; the witnesses are `GFM.LimitedCascade.overloaded`
-- (`GFM.InnerCascade.imcTuned_mem_den_iff`, `GFM.LimitedCascade.overloaded_mem_den_unstable`)
-- and `GFM.LimitedCascade.unloaded`.
-- The laws: `exact-local` is `GFM.LimitedCascade.realizationExactUnder_local`, `sound-overload`
-- is `GFM.LimitedCascade.realizationSoundUnder_unstable_of_overload`, `not-sound-overload` is
-- `GFM.LimitedCascade.not_realizationSoundUnder_locallyExponentiallyStable`,
-- `not-sound-global` is
-- `GFM.LimitedCascade.not_realizationSoundUnder_globallyExponentiallyStable`, `complete-global` is
-- `GFM.LimitedCascade.realizationCompleteUnder_globallyExponentiallyStable`. Nothing here is
-- exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥) renaming (elim to ⊥-elim)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading
open import theorem.Stack.Realization

-- The requirement language of the cascade design family (`Spectral.Requirement`).
data LinearReq : Type where
  stable unstable' : LinearReq

-- The platform requirements (Lean `LimitRequirementGFM`): the lifted design requirements, the
-- physical range `L, C > 0`, `0 < V_dc`, headroom `|v*| < V_dc/√3` and overload `V_dc/√3 < |v*|`.
data LimitReq : Type where
  design : LinearReq → LimitReq
  physical dcLink headroom overload : LimitReq

-- The local sentences.
data Local : Type where
  lyapunov asymptotic exponential instability : Local

-- The contexts of the connection: `{headroom}`, the overload constraints
-- `{physical, dcLink, overload}` and the realistic constraints with headroom
-- `{physical, dcLink, headroom}`.
headroomOnly overloadContext realistic : LimitReq → Type
headroomOnly headroom = Unit
headroomOnly _ = ⊥
overloadContext physical = Unit
overloadContext dcLink = Unit
overloadContext overload = Unit
overloadContext _ = ⊥
realistic physical = Unit
realistic dcLink = Unit
realistic headroom = Unit
realistic _ = ⊥

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (Cascade Operating : Type)
    (designSystem : Cascade → System) (platformSystem : Cascade → Operating → System)
    (sentence : Local → Sentence) (global : Sentence)
    -- Designs: stable, unstable, the physical range; operating points `(v*, V_dc)`:
    -- `0 < V_dc`; platforms: headroom and overload.
    (Stable Unstable Physical : Cascade → Type) (DCLink : Operating → Type)
    (Headroom Overload : Cascade → Operating → Type)
    where

    -- What Lean proves.
    record Obligations : Type where
      field
        locality : (k : Local) (c : Cascade) (o : Operating) → Headroom c o →
          holds (platformSystem c o) (sentence k) ↔ holds (designSystem c) (sentence k)
        overload-unstable : (c : Cascade) (o : Operating) → Physical c → DCLink o →
          Overload c o → holds (platformSystem c o) (sentence instability)
        no-global : (c : Cascade) (o : Operating) → ¬ holds (platformSystem c o) global
        exclusive : (a : System) → holds a (sentence lyapunov) →
          ¬ holds a (sentence instability)
        exponential-lyapunov : (a : System) → holds a (sentence exponential) →
          holds a (sentence lyapunov)
        -- The IMC design, overloaded (`v* = 1`) and unloaded (`v* = 0`).
        imc : Cascade
        overloaded unloaded : Operating
        imc-physical : Physical imc
        imc-exponential : holds (designSystem imc) (sentence exponential)
        imc-global : holds (designSystem imc) global
        overloaded-dcLink : DCLink overloaded
        overloaded-overload : Overload imc overloaded
        unloaded-dcLink : DCLink unloaded
        unloaded-headroom : Headroom imc unloaded

    Platform : Type
    Platform = Cascade × Operating

    designMeets : Cascade → LinearReq → Type
    designMeets c stable = Stable c
    designMeets c unstable' = Unstable c

    platformMeets : Platform → LimitReq → Type
    platformMeets (c , o) (design q) = designMeets c q
    platformMeets (c , o) physical = Physical c
    platformMeets (c , o) dcLink = DCLink o
    platformMeets (c , o) headroom = Headroom c o
    platformMeets (c , o) overload = Overload c o

    -- The two families; their translations are their own and do not enter the realization laws.
    designFamily : Family
    designFamily = record
      { Model = Cascade ; Req = LinearReq ; system = designSystem ; meets = designMeets
      ; translate = λ _ _ → ⊥ }

    platform : Family
    platform = record
      { Model = Platform ; Req = LimitReq ; system = λ y → platformSystem (fst y) (snd y)
      ; meets = platformMeets ; translate = λ _ _ → ⊥ }

    open Design designFamily platform fst

    module _ (ob : Obligations) where
      open Obligations ob

      -- Within headroom every local sentence is realized exactly: near the operating point the
      -- limit is inactive.
      exact-local : (k : Local) → ExactUnder' designed headroomOnly (sentence k)
      exact-local k = exactUnder-of-reading (realize platform headroomOnly) (sentence k)
        (λ y h → locality k (fst y) (snd y) (h headroom tt))

      -- Within overload instability is realized soundly: every platform is unstable.
      sound-overload : SoundUnder designed overloadContext (sentence instability)
      sound-overload (c , o) h _ =
        overload-unstable c o (h physical tt) (h dcLink tt) (h overload tt)

      -- Within overload local exponential stability is not realized soundly.
      not-sound-overload : ¬ SoundUnder designed overloadContext (sentence exponential)
      not-sound-overload = not-sound-of-witness designed (imc , overloaded) context
        (snd (certified↔ (sentence exponential) (imc , overloaded)) imc-exponential)
        (λ h → exclusive (platformSystem imc overloaded)
          (exponential-lyapunov (platformSystem imc overloaded) h)
          (overload-unstable imc overloaded imc-physical overloaded-dcLink overloaded-overload))
        where
          context : realize platform overloadContext (imc , overloaded)
          context physical _ = imc-physical
          context dcLink _ = overloaded-dcLink
          context overload _ = overloaded-overload
          context (design _) ()
          context headroom ()

      -- Global exponential stability is not realized soundly within the realistic constraints
      -- with headroom: no platform satisfies it.
      not-sound-global : ¬ SoundUnder designed realistic global
      not-sound-global = not-sound-of-witness designed (imc , unloaded) unloaded-context
        (snd (certified↔ global (imc , unloaded)) imc-global) (no-global imc unloaded)
        where
          unloaded-context : realize platform realistic (imc , unloaded)
          unloaded-context physical _ = imc-physical
          unloaded-context dcLink _ = unloaded-dcLink
          unloaded-context headroom _ = unloaded-headroom
          unloaded-context (design _) ()
          unloaded-context overload ()

      -- It is realized completely only vacuously.
      complete-global : CompleteUnder designed (λ _ → ⊥) global
      complete-global (c , o) _ h = ⊥-elim (no-global c o h)
