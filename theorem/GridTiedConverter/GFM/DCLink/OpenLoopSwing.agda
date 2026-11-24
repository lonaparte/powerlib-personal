{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.DCLink.OpenLoopSwing where
-- Lean modules: theorem.GridTiedConverter.GFM.DCLink.OpenLoop

-- Scaffold of the comparison of the open-loop VSM–DC model on its invariant singular plane
-- (`GFM.DCLink.OpenLoop.family` of `theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean`) with the
-- swing hub (`Synchronous.Swing.family`, content of
-- `theorem/PowerSystem/Synchronous/Swing.agda`). A model is a plant with a selected angle `δ*` and
-- DC voltage `V*`; its reduction (`toSwing`) is the swing machine `⟨M, D, P_ff, c₀, A, α⟩` of the
-- plant at the same angle (Lean `GFM.DCLink.Plant.swingParams`). On the plane `V = 0` the angle
-- rows of the three-state field are the swing field (`reducedField`, by computation here; Lean
-- `GFM.DCLink.Plant.planeField_eq_swing` with `GFM.DCLink.Plant.planeField_eq`), and for a source
-- current that does not cross the plane (`I_s / C = 0`) the plane is invariant (Lean
-- `GFM.DCLink.Plant.openField_two_of_V_eq_zero`, Lean reading the power term on the plane with
-- `x / 0 = 0`). The two families have systems of different dimension (three against two states),
-- so the connection is not a reading of systems: it compares, in a context of full models, two
-- sentences, and derives their agreement (`agree-ls`, `agree-las`) from the two characterizations
-- Lean proves.
-- * Context `OnPlane`: `V* = 0`, `I_s / C = 0` and `(P_s − P_e(δ*))/C ≤ 0` (the power term does not
--   push `V` off the plane). There Lyapunov stability of the full model is characterized by the
--   swing conditions `LSCond` (Lean `GFM.DCLink.OpenLoop.mem_den_lyapunovStable_iff_of_invariant`:
--   for `(P_s − P_e(δ*))/C < 0` through the collapse onto the plane,
--   `Dynamics.Degenerate.lyapunovStable_iff_of_invariantPlane`; for `= 0` through the first
--   integral `V²/2 − (M ω + D δ)/C` off the plane,
--   `Dynamics.Degenerate.lyapunovStable_iff_of_invariantPlane_firstIntegral`; the plane flow is the
--   swing with `V` relaxed, `Dynamics.Degenerate.lyapunovStable_relaxed_iff`). Within positive
--   inertia the swing machine is characterized by the same conditions (Lean
--   `Synchronous.Swing.mem_den_lyapunovStable_iff_of_inertia`, its conditions divided by `M > 0`).
-- * Context `Collapsing`: the same with `(P_s − P_e(δ*))/C < 0`. There local asymptotic stability
--   of the full model is characterized by `LASCond` (Lean
--   `GFM.DCLink.OpenLoop.mem_den_locallyAsymptoticallyStable_iff_of_invariant`, through
--   `Dynamics.Degenerate.localAsymptoticStable_of_invariantPlane` and
--   `Dynamics.Degenerate.localAsymptoticStable_relaxed_iff`), and within positive inertia so is the
--   swing machine (Lean `Synchronous.Swing.exactUnder_locallyAsymptoticallyStable`).
-- Within negative inertia Lean reads the hub law on the same field with every coefficient negated
-- (a positive-inertia swing machine with the same system), and without inertia both are unstable;
-- the scaffold fixes the positive-inertia comparison only. The direction is from the hub's laws to
-- the full model; each family keeps its own requirement language (left empty here). Nothing here
-- is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing

↔-sym : {A B : Type} → A ↔ B → B ↔ A
↔-sym (f , g) = g , f

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  State3 : Type
  State3 = ℝ × ℝ × ℝ

  -- The plant (Lean `GFM.DCLink.Plant`): inertia, damping, capacitance, power reference, the power
  -- curve `c₀ + A sin(δ − α)` and the affine DC source `P_s + I_s V`.
  record Plant : Type where
    constructor plant
    field
      M D C Pff c0 A α Ps Is : ℝ

  -- A model: a plant with a selected angle `δ*` and DC voltage `V*` (Lean
  -- `GFM.DCLink.OpenLoop.Model`).
  record Model : Type where
    constructor model
    field
      q : Plant
      δ V : ℝ

  open Plant
  open Model

  -- The exported power `P_e(δ)` and the synchronizing coefficient `k(δ) = P_e'(δ)` (Lean
  -- `GFM.DCLink.Plant.Pe`, `GFM.DCLink.Plant.k`).
  power slope : Plant → ℝ → ℝ
  power p x = c0 p + A p * sin (x - α p)
  slope p x = A p * cos (x - α p)

  -- The open-loop field in the coordinates `(δ, ω, V)` (Lean `GFM.DCLink.Plant.openField`) and the
  -- selected point `(δ*, 0, V*)`.
  openField : Plant → State3 → State3
  openField p (x , w , v) =
    w , ((Pff p - power p x) - D p * w) / M p , (Is p + (Ps p - power p x) / v) / C p

  openSystem : Model → System State3
  openSystem m = openField (q m) , (δ m , 0r , V m)

  -- The plane `V = 0` and the angle rows.
  embed : ℝ × ℝ → State3
  embed (x , w) = x , w , 0r

  slow : State3 → ℝ × ℝ
  slow (x , w , _) = x , w

  -- The reduction: the swing machine of the plant at the same angle.
  swingOf : Plant → SwingParams
  swingOf p = swingParams (M p) (D p) (Pff p) (c0 p) (A p) (α p)

  toSwing : Model → SwingModel
  toSwing m = swingModel (swingOf (q m)) (δ m)

  -- On the plane the angle rows of the open-loop field are the swing field.
  reducedField : (p : Plant) (y : ℝ × ℝ) → slow (openField p (embed y)) ≡ swingField (swingOf p) y
  reducedField p (x , w) = refl

  -- The contexts and the conditions of the two characterizations.
  OnPlane Collapsing : Model → Type
  OnPlane m =
    (V m ≡ 0r) × (Is (q m) / C (q m) ≡ 0r) × ((Ps (q m) - power (q m) (δ m)) / C (q m) ≤ 0r)
  Collapsing m =
    (V m ≡ 0r) × (Is (q m) / C (q m) ≡ 0r) × ((Ps (q m) - power (q m) (δ m)) / C (q m) < 0r)

  LSCond LASCond : Model → Type
  LSCond m = ((Pff p - power p (δ m)) / M p ≡ 0r) ×
    (((0r ≤ D p / M p) × (0r < slope p (δ m) / M p)) ⊎ ((A p ≡ 0r) × (0r < D p / M p)))
    where p = q m
  LASCond m = ((Pff p - power p (δ m)) / M p ≡ 0r) × (0r < D p / M p) × (0r < slope p (δ m) / M p)
    where p = q m

  module OnLayers
    (holds3 : System State3 → Sentence → Type)
    (inv3 : (A' : Affine State3) (a : System State3) (s : Sentence) →
      holds3 (transportSystem A' a) s ≃ holds3 a s)
    (holds2 : System (ℝ × ℝ) → Sentence → Type)
    (inv2 : (A' : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds2 (transportSystem A' a) s ≃ holds2 a s)
    where

    module F3 = Flows State3 holds3 inv3
    module F2 = SwingFamily holds2 inv2

    -- The open-loop family (Lean `GFM.DCLink.OpenLoop.family`; its requirement language is left
    -- empty here) and the swing hub.
    full : F3.Family
    full = record
      { Model = Model ; Req = ⊥ ; system = openSystem ; meets = λ _ () ; translate = λ _ () }

    hub : F2.Family
    hub = F2.swingFamily

    -- What Lean proves.
    record Obligations : Type where
      field
        full-ls : (m : Model) → OnPlane m → F3.den full lyapunovStable m ↔ LSCond m
        full-las : (m : Model) → Collapsing m →
          F3.den full locallyAsymptoticallyStable m ↔ LASCond m
        hub-ls : (m : Model) → 0r < M (q m) → F2.den hub lyapunovStable (toSwing m) ↔ LSCond m
        hub-las : (m : Model) → 0r < M (q m) →
          F2.den hub locallyAsymptoticallyStable (toSwing m) ↔ LASCond m

    module _ (ob : Obligations) where
      open Obligations ob

      -- On the plane, within positive inertia, the full model and its swing machine agree on
      -- Lyapunov stability, and under the collapse on local asymptotic stability.
      agree-ls : (m : Model) → OnPlane m → 0r < M (q m) →
        F3.den full lyapunovStable m ↔ F2.den hub lyapunovStable (toSwing m)
      agree-ls m c i = ↔-trans (full-ls m c) (↔-sym (hub-ls m i))

      agree-las : (m : Model) → Collapsing m → 0r < M (q m) →
        F3.den full locallyAsymptoticallyStable m ↔
          F2.den hub locallyAsymptoticallyStable (toSwing m)
      agree-las m c i = ↔-trans (full-las m c) (↔-sym (hub-las m i))
