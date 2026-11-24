{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.Line.LineSwing where
-- Lean modules: theorem.GridTiedConverter.GFM.Line.VSM theorem.GridTiedConverter.GFM.Line.PSC

-- Scaffold of the comparison of the grid-forming converter on a dynamic R–L line with its
-- quasi-static (phasor) reduction: the four-state VSM on the line (`Line.VSM.family` of
-- `theorem/GridTiedConverter/GFM/Line/VSM.lean`) against the swing family
-- (`Synchronous.Swing.family`), and the three-state PSC on the line (`Line.PSC.family` of
-- `theorem/GridTiedConverter/GFM/Line/PSC.lean`) against the quasi-static PSC family
-- (`GFM.PSC.family`). The two families live on different state spaces, so the map of models is
-- not a reading (no conjugacy relates the systems): it is the reduction, fixed by the
-- quasi-steady set `i = i_s(δ)` (`qssVSM`, `qssPSC`) on which the slow rows of the full field are
-- the reduced field (`reducedVSM`, `reducedPSC`; Lean `VSM.reducedField_eq_swing` and
-- `PSC.reducedRhs_eq_shift`). The map of models sends a line model to the reduced model at the
-- same angle (`toSwing`; Lean `VSM.Model.toSwing`) or at the angle `δ* − α` (`toPSC`; Lean
-- `PSC.Model.toPSC`). The scaffold fixes the contexts in which the two denotations diverge
-- (`Divergence`): on a lossless line, and for the PSC above the critical gain, the reduced model is
-- locally exponentially stable and the full model unstable (Lean
-- `VSM.swing_stable_full_unstable_of_lossless`, `VSM.lowDamping_swing_stable_full_unstable`,
-- `PSC.psc_stable_full_unstable_of_lossless`, `PSC.psc_stable_full_unstable_of_gain`,
-- `PSC.highGain_psc_stable_full_unstable`), and derives that in those contexts the reduction does
-- not carry local exponential stability back to the full model (`notCarried`), so no hub reading
-- along the reduction exists. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing

-- A full family on the states `X` compared with a reduced family on the states `Y` through a map
-- of models, in a context of full models.
module Comparison {X Y : Type}
  (holdsX : System X → Sentence → Type)
  (invX : (A : Affine X) (a : System X) (s : Sentence) →
    holdsX (transportSystem A a) s ≃ holdsX a s)
  (holdsY : System Y → Sentence → Type)
  (invY : (A : Affine Y) (a : System Y) (s : Sentence) →
    holdsY (transportSystem A a) s ≃ holdsY a s)
  where

  module FX = Flows X holdsX invX
  module FY = Flows Y holdsY invY

  module _ (F : FX.Family) (G : FY.Family) (reduce : FX.Family.Model F → FY.Family.Model G)
    (context : FX.Family.Model F → Type)
    where

    -- What Lean proves: in the context the reduced model is locally exponentially stable and the
    -- full model unstable.
    record Divergence : Type where
      field
        divergence : (x : FX.Family.Model F) → context x →
          FY.den G locallyExponentiallyStable (reduce x) × FX.den F unstable x

    -- Instability excludes local exponential stability (a law of the semantic layer), so in the
    -- context the reduced model's stability does not give the full model's.
    module _ (dv : Divergence)
      (exclusive : (a : System X) → holdsX a locallyExponentiallyStable → holdsX a unstable → ⊥)
      where

      notCarried : (x : FX.Family.Model F) → context x →
        ¬ (FY.den G locallyExponentiallyStable (reduce x) → FX.den F locallyExponentiallyStable x)
      notCarried x c h = exclusive (FX.Family.system F x)
        (h (fst (Divergence.divergence dv x c))) (snd (Divergence.divergence dv x c))

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  State4 State3 : Type
  State4 = ℝ × ℝ × ℝ × ℝ
  State3 = ℝ × ℝ × ℝ

  -- The source, the line and the grid (`Line.Network`).
  record LineParams : Type where
    constructor lineParams
    field
      E V R L ω0 : ℝ

  open LineParams

  -- The line rates and the exported power (`Network.rateD`, `Network.rateQ`, `Network.power`).
  reactance : LineParams → ℝ
  reactance n = ω0 n * L n

  rateD rateQ power : LineParams → ℝ → ℝ → ℝ → ℝ
  rateD n δ id iq = (((E n * cos δ - V n) - R n * id) + reactance n * iq) / L n
  rateQ n δ id iq = ((E n * sin δ - R n * iq) - reactance n * id) / L n
  power n δ id iq = E n * (cos δ * id + sin δ * iq)

  -- The quasi-steady current `i_s(δ)` and the one-harmonic curve `c₀ + A sin(δ − α)`, supplied by
  -- Lean (`Network.is`, `Network.c0`, `Network.A`, `Network.α`).
  module Line (isRe isIm : LineParams → ℝ → ℝ) (c0 A α : LineParams → ℝ) where

    -- The VSM on the line (`Line.VSM`).
    record VSMParams : Type where
      constructor vsmParams
      field
        net : LineParams
        M D Pref : ℝ

    record VSMModel : Type where
      constructor vsmModel
      field
        g : VSMParams
        δ : ℝ

    open VSMParams
    open VSMModel

    vsmField : VSMParams → State4 → State4
    vsmField q (x , w , id , iq) =
      w , ((Pref q - power (net q) x id iq) - D q * w) / M q ,
        rateD (net q) x id iq , rateQ (net q) x id iq

    qssVSM : VSMParams → ℝ × ℝ → State4
    qssVSM q (x , w) = x , w , isRe (net q) x , isIm (net q) x

    vsmSystem : VSMModel → System State4
    vsmSystem m = vsmField (g m) , qssVSM (g m) (δ m , 0r)

    -- The slow rows of the full field.
    slowVSM : State4 → ℝ × ℝ
    slowVSM (x , w , _ , _) = x , w

    -- The reduced swing machine and the map of models (`VSM.swingParams`, `VSM.Model.toSwing`).
    swingOf : VSMParams → SwingParams
    swingOf q = swingParams (M q) (D q) (Pref q) (c0 (net q)) (A (net q)) (α (net q))

    toSwing : VSMModel → SwingModel
    toSwing m = swingModel (swingOf (g m)) (δ m)

    -- The PSC on the line (`Line.PSC`) and the quasi-static PSC (`GFM.PSC`).
    record PSCParams : Type where
      constructor pscParams
      field
        net : LineParams
        Kp Pref : ℝ

    record PSCModel : Type where
      constructor pscModel
      field
        g : PSCParams
        δ : ℝ

    record QSParams : Type where
      constructor qsParams
      field
        Kp Pstar Pmax : ℝ

    record QSModel : Type where
      constructor qsModel
      field
        c : QSParams
        δ : ℝ

    pscField : PSCParams → State3 → State3
    pscField q (x , id , iq) =
      PSCParams.Kp q * (PSCParams.Pref q - power (PSCParams.net q) x id iq) ,
        rateD (PSCParams.net q) x id iq , rateQ (PSCParams.net q) x id iq

    qssPSC : PSCParams → ℝ → State3
    qssPSC q x = x , isRe (PSCParams.net q) x , isIm (PSCParams.net q) x

    pscSystem : PSCModel → System State3
    pscSystem m = pscField (PSCModel.g m) , qssPSC (PSCModel.g m) (PSCModel.δ m)

    qsRhs : QSParams → ℝ → ℝ
    qsRhs c x = QSParams.Kp c * (QSParams.Pstar c - QSParams.Pmax c * sin x)

    qsSystem : QSModel → System ℝ
    qsSystem m = qsRhs (QSModel.c m) , QSModel.δ m

    -- The reduced law in the angle `δ − α` (`PSC.toShifted`, `PSC.Model.toPSC`).
    shifted : PSCParams → QSParams
    shifted q = qsParams (PSCParams.Kp q) (PSCParams.Pref q - c0 (PSCParams.net q))
      (A (PSCParams.net q))

    toPSC : PSCModel → QSModel
    toPSC m = qsModel (shifted (PSCModel.g m)) (PSCModel.δ m - α (PSCParams.net (PSCModel.g m)))

    -- What Lean proves by computation on the fields: the slow rows on the quasi-steady set are
    -- the reduced fields (`VSM.reducedField_eq_swing`, `PSC.reducedRhs_eq_shift`).
    record Reductions : Type where
      field
        reducedVSM : (q : VSMParams) (y : ℝ × ℝ) →
          slowVSM (vsmField q (qssVSM q y)) ≡ swingField (swingOf q) y
        reducedPSC : (q : PSCParams) (x : ℝ) →
          fst (pscField q (qssPSC q x)) ≡ qsRhs (shifted q) (x - α (PSCParams.net q))

    -- The requirement languages (Lean `VSM.Requirement`, `PSC.Requirement`, `GFM.PSC.Meets`): the
    -- line families' Routh conditions and their violation are supplied by Lean
    -- (`VSM.Model.Routh`, `VSM.Model.RouthViolation`, `PSC.Model.Routh`,
    -- `PSC.Model.RouthViolation`), as is the quasi-steady power (`Network.qssPower`).
    data LineReq : Type where
      balanced physical routh destabilizing : LineReq

    lineLocal lineUnstable noLine : LineReq → Type
    lineLocal destabilizing = ⊥
    lineLocal _ = Unit
    lineUnstable routh = ⊥
    lineUnstable _ = Unit
    noLine _ = ⊥

    lineTranslate : Sentence → LineReq → Type
    lineTranslate = localTable lineLocal lineLocal lineUnstable noLine

    data QSReq : Type where
      qsBalanced stableSlope unstableSlope : QSReq

    qsMeets : QSModel → QSReq → Type
    qsMeets m qsBalanced =
      QSParams.Pmax (QSModel.c m) * sin (QSModel.δ m) ≡ QSParams.Pstar (QSModel.c m)
    qsMeets m stableSlope =
      0r < (QSParams.Kp (QSModel.c m) * QSParams.Pmax (QSModel.c m)) * cos (QSModel.δ m)
    qsMeets m unstableSlope =
      (QSParams.Kp (QSModel.c m) * QSParams.Pmax (QSModel.c m)) * cos (QSModel.δ m) < 0r

    qsLocal qsUnstable noQS : QSReq → Type
    qsLocal unstableSlope = ⊥
    qsLocal _ = Unit
    qsUnstable stableSlope = ⊥
    qsUnstable _ = Unit
    noQS _ = ⊥

    qsTranslate : Sentence → QSReq → Type
    qsTranslate = localTable qsLocal qsLocal qsUnstable noQS

    module Families (qssPower : LineParams → ℝ → ℝ)
      (physicalVSM routhVSM violationVSM : VSMModel → Type)
      (physicalPSC routhPSC violationPSC : PSCModel → Type)
      where

      vsmMeets : VSMModel → LineReq → Type
      vsmMeets m balanced = qssPower (net (g m)) (δ m) ≡ Pref (g m)
      vsmMeets m physical = physicalVSM m
      vsmMeets m routh = routhVSM m
      vsmMeets m destabilizing = violationVSM m

      pscMeets : PSCModel → LineReq → Type
      pscMeets m balanced =
        qssPower (PSCParams.net (PSCModel.g m)) (PSCModel.δ m) ≡ PSCParams.Pref (PSCModel.g m)
      pscMeets m physical = physicalPSC m
      pscMeets m routh = routhPSC m
      pscMeets m destabilizing = violationPSC m

      -- The two contexts of divergence: a lossless line, and (PSC) zero reactive power above the
      -- critical gain; each with balance, physical parameters and a positive synchronizing
      -- coefficient. The critical-gain condition is supplied by Lean (`Network.KpCrit`).
      lossless : LineParams → Type
      lossless n = R n ≡ 0r

      vsmContext : VSMModel → Type
      vsmContext m = lossless (net (g m)) × vsmMeets m balanced × physicalVSM m ×
        (0r < syncCoeff (swingOf (g m)) (δ m))

      pscContext : (PSCModel → Type) → PSCModel → Type
      pscContext aboveCritical m = (lossless (PSCParams.net (PSCModel.g m)) ⊎ aboveCritical m) ×
        pscMeets m balanced × physicalPSC m

      module OnLayers
        (holds4 : System State4 → Sentence → Type)
        (inv4 : (A' : Affine State4) (a : System State4) (s : Sentence) →
          holds4 (transportSystem A' a) s ≃ holds4 a s)
        (holds3 : System State3 → Sentence → Type)
        (inv3 : (A' : Affine State3) (a : System State3) (s : Sentence) →
          holds3 (transportSystem A' a) s ≃ holds3 a s)
        (holds2 : System (ℝ × ℝ) → Sentence → Type)
        (inv2 : (A' : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
          holds2 (transportSystem A' a) s ≃ holds2 a s)
        (holds1 : System ℝ → Sentence → Type)
        (inv1 : (A' : Affine ℝ) (a : System ℝ) (s : Sentence) →
          holds1 (transportSystem A' a) s ≃ holds1 a s)
        where

        module VSMvsSwing = Comparison holds4 inv4 holds2 inv2
        module PSCvsQS = Comparison holds3 inv3 holds1 inv1

        -- The families (Lean `Line.VSM.family`, `Synchronous.Swing.family`, `Line.PSC.family`,
        -- `GFM.PSC.family`).
        vsmFamily : VSMvsSwing.FX.Family
        vsmFamily = record
          { Model = VSMModel ; Req = LineReq ; system = vsmSystem ; meets = vsmMeets
          ; translate = lineTranslate }

        swingFamily : VSMvsSwing.FY.Family
        swingFamily = SwingContent.SwingFamily.swingFamily Sc holds2 inv2

        pscFamily : PSCvsQS.FX.Family
        pscFamily = record
          { Model = PSCModel ; Req = LineReq ; system = pscSystem ; meets = pscMeets
          ; translate = lineTranslate }

        qsFamily : PSCvsQS.FY.Family
        qsFamily = record
          { Model = QSModel ; Req = QSReq ; system = qsSystem ; meets = qsMeets
          ; translate = qsTranslate }

        -- What Lean proves (`VSM.swing_stable_full_unstable_of_lossless`; for the PSC
        -- `PSC.psc_stable_full_unstable_of_lossless` and `PSC.psc_stable_full_unstable_of_gain`).
        VSMDivergence : Type
        VSMDivergence = VSMvsSwing.Divergence vsmFamily swingFamily toSwing vsmContext

        PSCDivergence : (PSCModel → Type) → Type
        PSCDivergence aboveCritical =
          PSCvsQS.Divergence pscFamily qsFamily toPSC (pscContext aboveCritical)
