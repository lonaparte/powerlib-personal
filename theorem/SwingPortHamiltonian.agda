{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.SwingPortHamiltonian where

-- Scaffold of the reading of the linearized swing family through the linear port-Hamiltonian
-- family (`Synchronous.Swing.Linearized.family` read through `Port.PortHamiltonian.family`, in
-- `theorem/Synchronous/SwingPH.lean`). The linearized swing machine at `(p, δ₀)` is the linear
-- plant of the Jacobian `[[0, 1], [−K/M, −D/M]]`, `K = k₂ cos(δ₀ − k₃)`, without a port. On the
-- context `M > 0`, `D ≥ 0`, `K > 0` (`PHContext`) its pH image `linearPH` (`J = [[0, 1], [−1, 0]]`,
-- `R = diag(0, D)`, `Q = diag(K, 1/M)`, `B = (0, 1)ᵀ`, stored energy `½ K Δδ² + (M Δω)²/(2M)`,
-- one port from the power perturbation to `Δω`) has the state matrix
-- `(J − R) Q = diag(1, M) J_swing diag(1, 1/M)`, the Jacobian in the momentum coordinates
-- `(Δδ, M Δω)` (`conjugate`). The flow sentences of a linear plant are those of its state matrix
-- and are invariant under similarity, so on the context the two families agree on every flow
-- sentence (`reading`, `den↔`). Only the flow sentences are read: passivity is read on the pH
-- port, which the linearized swing family does not have. The hub's laws hold at the image
-- (`image-passive`; `image-lyapunovStable`, for every `D ≥ 0`, including `D = 0`); they are not
-- stated of the swing models. The requirement languages of the two families take no part in the
-- connection and are left empty here. Lean: `conjugate` is
-- `Synchronous.SwingParams.stateMatrix_eq_conj` (with `stateMatrix_mul`), `lin-flow` and `ph-flow`
-- are `Family.IsLinear.mem_den_flow` (`Synchronous.Swing.Linearized.family_isLinear`,
-- `Port.PortHamiltonian.family_isLinear`), `similar` is `Linear.holds_conj`, `den↔` is
-- `Synchronous.SwingParams.linearPH_mem_den_flow_iff`; `ph-passive`, `ph-ls` are
-- `Port.PortHamiltonian.mem_den_passive`, `Port.PortHamiltonian.mem_den_lyapunovStable`, read at
-- the image as `Synchronous.SwingParams.linearPH_passive`,
-- `Synchronous.SwingParams.linearPH_lyapunovStable`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics
open import theorem.Swing

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  -- 2 × 2 state matrices `[[a, b], [c, d]]`.
  record Mat₂ : Type where
    constructor mat₂
    field
      a b c d : ℝ

  inertiaOf dampingOf sync : SwingModel → ℝ
  inertiaOf m = SwingParams.M (SwingModel.p m)
  dampingOf m = SwingParams.D (SwingModel.p m)
  sync m = syncCoeff (SwingModel.p m) (SwingModel.δ m)

  -- The context of the pH image (the hypotheses of Lean `linearPH`).
  PHContext : SwingModel → Type
  PHContext m = (0r < inertiaOf m) × (0r ≤ dampingOf m) × (0r < sync m)

  -- The momentum coordinates on state matrices: `A ↦ diag(1, μ) A diag(1, 1/μ)`.
  momentumConj : ℝ → Mat₂ → Mat₂
  momentumConj μ (mat₂ a b c d) = mat₂ a (b / μ) (μ * c) ((μ * d) / μ)

  module Reading (one : ℝ)
    -- Linear plants of the semantic layer (any dimension and number of ports) with their
    -- satisfaction, and the flow sentences of the zero-input field `ẋ = A x` at `0`.
    (Plant : Type) (holds : Plant → Sentence → Type) (holdsMat : Mat₂ → Sentence → Type)
    -- The linear plants of the swing Jacobians (no port), the pH plants with two states and one
    -- port with their state matrices `(J − R) Q`, and the pH image on the context.
    (linPlant : SwingModel → Plant) (PH : Type) (phPlant : PH → Plant) (phMatrix : PH → Mat₂)
    (linearPH : (m : SwingModel) → PHContext m → PH)
    where

    -- The swing Jacobian at the selected angle (Lean `SwingParams.jacobian`).
    jacobian : SwingModel → Mat₂
    jacobian m = mat₂ 0r one ((- sync m) / inertiaOf m) ((- dampingOf m) / inertiaOf m)

    linearSemantics : Semantics
    linearSemantics = record { System = Plant ; Sentence = Sentence ; holds = holds }

    open Readings linearSemantics

    linearized phFamily : Family
    linearized = record
      { Model = SwingModel ; Req = ⊥ ; system = linPlant ; meets = λ _ () ; translate = λ _ () }
    phFamily = record
      { Model = PH ; Req = ⊥ ; system = phPlant ; meets = λ _ () ; translate = λ _ () }

    -- What Lean proves.
    record Obligations : Type where
      field
        lin-flow : (m : SwingModel) (s : Sentence) → Flow s →
          holds (linPlant m) s ≃ holdsMat (jacobian m) s
        ph-flow : (h : PH) (s : Sentence) → Flow s → holds (phPlant h) s ≃ holdsMat (phMatrix h) s
        similar : (μ : ℝ) → ¬ (μ ≡ 0r) → (A : Mat₂) (s : Sentence) → Flow s →
          holdsMat (momentumConj μ A) s ≃ holdsMat A s
        conjugate : (m : SwingModel) (c : PHContext m) →
          phMatrix (linearPH m c) ≡ momentumConj (inertiaOf m) (jacobian m)
        nonzero : {x : ℝ} → 0r < x → ¬ (x ≡ 0r)
        ph-passive : (h : PH) → holds (phPlant h) passive
        ph-ls : (h : PH) → holds (phPlant h) lyapunovStable

    module _ (ob : Obligations) where
      open Obligations ob

      onContext : Family
      onContext = restrictBy linearized PHContext

      -- A flow sentence of the swing Jacobian is the same sentence of its momentum conjugate,
      -- the pH state matrix.
      readOn : (m : SwingModel) (c : PHContext m) (s : Sentence) → Flow s →
        holds (linPlant m) s ≃ holds (phPlant (linearPH m c)) s
      readOn m c s f =
        compEquiv (lin-flow m s f)
          (compEquiv (invEquiv (similar (inertiaOf m) (nonzero (fst c)) (jacobian m) s f))
            (compEquiv (pathToEquiv (cong (λ A → holdsMat A s) (sym (conjugate m c))))
              (invEquiv (ph-flow (linearPH m c) s f))))

      reading : PartialHub Flow onContext phFamily
      reading = record
        { map = λ x → linearPH (fst x) (snd x) ; read = λ x → readOn (fst x) (snd x) }

      -- On the context the pH image and the swing model agree on every flow sentence.
      den↔ : (m : SwingModel) (c : PHContext m) (s : Sentence) → Flow s →
        den phFamily s (linearPH m c) ↔ den linearized s m
      den↔ m c s f = ↔-of-≃ (invEquiv (PartialHub.read reading (m , c) s f))

      -- The hub's laws at the image: passivity and Lyapunov stability.
      image-passive : (m : SwingModel) (c : PHContext m) → den phFamily passive (linearPH m c)
      image-passive m c = ph-passive (linearPH m c)

      image-lyapunovStable : (m : SwingModel) (c : PHContext m) →
        den phFamily lyapunovStable (linearPH m c)
      image-lyapunovStable m c = ph-ls (linearPH m c)
