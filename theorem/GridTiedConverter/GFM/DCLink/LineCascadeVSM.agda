{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.DCLink.LineCascadeVSM where
-- Lean modules: theorem.GridTiedConverter.GFM.DCLink.LineCascade

-- Scaffold of the connection of the VSM on a dynamic line feeding its DC link
-- (`GFM.DCLink.LineCascade.family` of `theorem/GridTiedConverter/GFM/DCLink/LineCascade.lean`, five
-- states `(δ, ω, i_d, i_q, V)`) with the four-state VSM on the line (`Line.VSM.family` of
-- `theorem/GridTiedConverter/GFM/Line/VSM.lean`). A cascade model is a dynamic line with a selected
-- angle `δ*` and DC voltage `V*`; its AC part (`toVSM`, Lean `LineCascade.Model.toVSM`) is the line
-- VSM at the same angle. The AC rows of the five-state field do not depend on `V` and are the
-- line-VSM field (`acRows`, by computation here), so the system is a cascade: line VSM first, DC
-- node `C V̇ = I_s + (P_s − P_e)/V` second. The two families have systems of different
-- dimension, so the connection is not a reading of systems: in the context `Physical` (a
-- physical network, `M, D > 0`, `C, V* ≠ 0`) Lean characterizes local exponential stability
-- of the cascade by balance, local exponential stability of the AC part in the line-VSM family
-- and a stable DC-node pole `I_s/(C V*) < 0` (`les↔`, Lean
-- `GFM.DCLink.LineCascade.mem_den_locallyExponentiallyStable_iff_vsm`, through the block-triangular
-- spectrum `LineCascade.Model.det_characteristicMatrix` and the converse linearization of
-- `Line.VSM.exactUnder_locallyExponentiallyStable`). From it the scaffold derives the two
-- necessary halves (`ac-necessary`, `dc-necessary`) and the sufficient one (`sufficient`). In
-- the context `Regular` (`V* ≠ 0`, `M, L, C ≠ 0`, `|Z|² > 0`) Lean characterizes local asymptotic
-- stability the same way (`las↔`, Lean
-- `GFM.DCLink.LineCascade.mem_den_locallyAsymptoticallyStable_iff_vsm`, the drive–node laws
-- `Dynamics.localAsymptoticStable_cascade` and
-- `Dynamics.localAsymptoticStable_drive_of_cascade`), and with a source current `I_s ≠ 0`
-- Lyapunov stability (`ls↔`, Lean `GFM.DCLink.LineCascade.mem_den_lyapunovStable_iff_vsm`); the
-- scaffold derives that at a balanced point with a stable DC pole the cascade and its AC part
-- agree on these sentences (`agree-las`, `agree-ls`), on the line-VSM Routh boundary as well.
-- Instability and the global sentences are not related to the line-VSM family. The direction is
-- from the line-VSM family to the cascade; each family keeps its own requirement language (left
-- empty here). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (Sc : Scalars) where
  open Scalars Sc

  State5 State4 : Type
  State5 = ℝ × ℝ × ℝ × ℝ × ℝ
  State4 = ℝ × ℝ × ℝ × ℝ

  -- The source, the line and the grid, the VSM and the DC link (Lean `Line.Network`, `Line.VSM`,
  -- `GFM.DCLink.DynamicLine`).
  record DynamicLine : Type where
    constructor dynamicLine
    field
      E V R L ω0 M D Pref C Ps Is : ℝ

  open DynamicLine

  reactance : DynamicLine → ℝ
  reactance g = ω0 g * L g

  -- The line rates and the exported power (Lean `Network.rateD`, `Network.rateQ`,
  -- `Network.power`).
  rateD rateQ power : DynamicLine → ℝ → ℝ → ℝ → ℝ
  rateD g δ id iq = (((E g * cos δ - V g) - R g * id) + reactance g * iq) / L g
  rateQ g δ id iq = ((E g * sin δ - R g * iq) - reactance g * id) / L g
  power g δ id iq = E g * (cos δ * id + sin δ * iq)

  -- The line-VSM field (Lean `Line.VSM.field`) and the five-state cascade field (Lean
  -- `GFM.DCLink.DynamicLine.field` at `P_ref`).
  vsmField : DynamicLine → State4 → State4
  vsmField g (x , w , id , iq) =
    w , ((Pref g - power g x id iq) - D g * w) / M g , rateD g x id iq , rateQ g x id iq

  cascadeField : DynamicLine → State5 → State5
  cascadeField g (x , w , id , iq , v) =
    w , ((Pref g - power g x id iq) - D g * w) / M g , rateD g x id iq , rateQ g x id iq ,
      (Is g + (Ps g - power g x id iq) / v) / C g

  -- The AC coordinates.
  ac : State5 → State4
  ac (x , w , id , iq , _) = x , w , id , iq

  -- The AC rows of the cascade field are the line-VSM field: they do not read `V`.
  acRows : (g : DynamicLine) (y : State5) → ac (cascadeField g y) ≡ vsmField g (ac y)
  acRows g (x , w , id , iq , v) = refl

  -- The quasi-steady line current `i_s(δ)`, supplied by Lean (`Network.is`).
  module Cascade (isRe isIm : DynamicLine → ℝ → ℝ) (qssPower : DynamicLine → ℝ → ℝ) where

    -- A cascade model and a line-VSM model (Lean `LineCascade.Model`, `Line.VSM.Model`).
    record Model : Type where
      constructor model
      field
        g : DynamicLine
        δ Vdc : ℝ

    record VSMModel : Type where
      constructor vsmModel
      field
        vg : DynamicLine
        vδ : ℝ

    open Model
    open VSMModel

    cascadeSystem : Model → System State5
    cascadeSystem m = cascadeField (g m) , (δ m , 0r , isRe (g m) (δ m) , isIm (g m) (δ m) , Vdc m)

    vsmSystem : VSMModel → System State4
    vsmSystem n = vsmField (vg n) , (vδ n , 0r , isRe (vg n) (vδ n) , isIm (vg n) (vδ n))

    -- The AC part (Lean `LineCascade.Model.toVSM`).
    toVSM : Model → VSMModel
    toVSM m = vsmModel (g m) (δ m)

    -- The operating point of the AC part is the AC coordinates of the cascade's.
    acPoint : (m : Model) → ac (snd (cascadeSystem m)) ≡ snd (vsmSystem (toVSM m))
    acPoint m = refl

    -- Balance and the DC-node pole (Lean `LineCascade.Model.Balanced`, `LineCascade.Model.b`).
    Balanced : Model → Type
    Balanced m = (qssPower (g m) (δ m) ≡ Pref (g m)) ×
      (Ps (g m) + Is (g m) * Vdc m ≡ qssPower (g m) (δ m))

    dcPole : Model → ℝ
    dcPole m = Is (g m) / (C (g m) * Vdc m)

    module OnLayers
      (holds5 : System State5 → Sentence → Type)
      (inv5 : (A' : Affine State5) (a : System State5) (s : Sentence) →
        holds5 (transportSystem A' a) s ≃ holds5 a s)
      (holds4 : System State4 → Sentence → Type)
      (inv4 : (A' : Affine State4) (a : System State4) (s : Sentence) →
        holds4 (transportSystem A' a) s ≃ holds4 a s)
      where

      module F5 = Flows State5 holds5 inv5
      module F4 = Flows State4 holds4 inv4

      -- The cascade family and the line-VSM family (their requirement languages are left empty
      -- here).
      cascade : F5.Family
      cascade = record
        { Model = Model ; Req = ⊥ ; system = cascadeSystem ; meets = λ _ () ; translate = λ _ () }

      vsm : F4.Family
      vsm = record
        { Model = VSMModel ; Req = ⊥ ; system = vsmSystem ; meets = λ _ () ; translate = λ _ () }

      -- What Lean proves: in the context of physical parameters the local exponential
      -- characterization; in the context of regular parameters the local asymptotic one and,
      -- with a source current, the Lyapunov one (the drive–node laws).
      record Obligations (Physical Regular : Model → Type) : Type where
        field
          les↔ : (m : Model) → Physical m →
            F5.den cascade locallyExponentiallyStable m ↔
              (Balanced m × F4.den vsm locallyExponentiallyStable (toVSM m) × (dcPole m < 0r))
          las↔ : (m : Model) → Regular m →
            F5.den cascade locallyAsymptoticallyStable m ↔
              (Balanced m × F4.den vsm locallyAsymptoticallyStable (toVSM m) × (dcPole m < 0r))
          ls↔ : (m : Model) → Regular m → ¬ (Is (g m) ≡ 0r) →
            F5.den cascade lyapunovStable m ↔
              (Balanced m × F4.den vsm lyapunovStable (toVSM m) × (dcPole m < 0r))

      module _ (Physical Regular : Model → Type) (ob : Obligations Physical Regular) where
        open Obligations ob

        -- A locally exponentially stable cascade has a locally exponentially stable AC part and a
        -- stable DC-node pole; the converse holds at a balanced point.
        ac-necessary : (m : Model) → Physical m →
          F5.den cascade locallyExponentiallyStable m →
            F4.den vsm locallyExponentiallyStable (toVSM m)
        ac-necessary m c h = fst (snd (fst (les↔ m c) h))

        dc-necessary : (m : Model) → Physical m →
          F5.den cascade locallyExponentiallyStable m → dcPole m < 0r
        dc-necessary m c h = snd (snd (fst (les↔ m c) h))

        sufficient : (m : Model) → Physical m → Balanced m →
          F4.den vsm locallyExponentiallyStable (toVSM m) → dcPole m < 0r →
            F5.den cascade locallyExponentiallyStable m
        sufficient m c b h d = snd (les↔ m c) (b , h , d)

        -- At a regular balanced point with a stable DC pole the cascade and its AC part agree on
        -- local asymptotic stability, and, with a source current, on Lyapunov stability: the
        -- boundary of the line VSM is carried to the cascade unchanged.
        agree-las : (m : Model) → Regular m → Balanced m → dcPole m < 0r →
          F5.den cascade locallyAsymptoticallyStable m ↔
            F4.den vsm locallyAsymptoticallyStable (toVSM m)
        agree-las m r b d =
          (λ h → fst (snd (fst (las↔ m r) h))) , (λ h → snd (las↔ m r) (b , h , d))

        agree-ls : (m : Model) → Regular m → ¬ (Is (g m) ≡ 0r) → Balanced m → dcPole m < 0r →
          F5.den cascade lyapunovStable m ↔ F4.den vsm lyapunovStable (toVSM m)
        agree-ls m r i b d =
          (λ h → fst (snd (fst (ls↔ m r i) h))) , (λ h → snd (ls↔ m r i) (b , h , d))
