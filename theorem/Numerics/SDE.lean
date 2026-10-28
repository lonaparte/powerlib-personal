import theorem.Attributes
import dependencies.Mathlib

/-! # Euler–Maruyama and Milstein steps: additive noise and the commutative-noise condition

With additive noise the Milstein step coincides with the Euler–Maruyama step, and the note's
commutative-noise condition is not sufficient.

Model boundary.
* Pathwise (deterministic) step maps driven by given standard-normal samples `ξ`; Wiener
  increments are `ΔW = √Δt ξ`. The state lives in a real normed space `E`; the drift `μ(x, t)`
  and the diffusion columns `σ_k(x, t)` are arbitrary maps, and the Milstein correction uses the
  Fréchet derivative of the diffusion in `x`. For several noise channels the iterated Itô
  integrals `I^{k₁k₂}` (including Lévy areas) are arbitrary given numbers.
* No probability, no convergence order and no implementation API is formalized.

Source: work-sync theory/T-sde-numerical.md §1.1–§1.2, §2.2–§2.3.

Results.
* `milsteinStep_eq_emStep` — scalar noise, state-independent diffusion ⇒ the Milstein step
  equals the Euler–Maruyama step for every sample; `milstein_trajectory_eq_em` lifts this to
  whole trajectories driven by the same samples.
* `milsteinMultiStep_eq_emMultiStep` — several additive channels ⇒ equality for every choice of
  iterated integrals (no Lévy-area sampling needed).
* `noteCommutative_not_sufficient` — correction to the commutative-noise condition (see
  Corrections).

Corrections.
* The note writes the commutative-noise condition as
  `Σ_k Σ_{ik} ∂_{x_j} Σ_{lk} = Σ_k Σ_{lk} ∂_{x_j} Σ_{ik}`. The correct (Kloeden–Platen)
  condition is `L^{k₁} σ_{i k₂} = L^{k₂} σ_{i k₁}` with `L^{k} = Σ_l Σ_{lk} ∂_{x_l}`, i.e.
  `Σ_l Σ_{l k₁} ∂_{x_l} Σ_{i k₂} = Σ_l Σ_{l k₂} ∂_{x_l} Σ_{i k₁}`. For the scalar state with
  diffusion row `σ(x) = (1, x)` the note's condition holds trivially while the correct one
  fails (`noteCommutative_not_sufficient`), so the note's test would wrongly accept a
  non-commutative noise.
-/

noncomputable section
namespace powerlib.Numerics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Scalar noise -/

/-- Euler–Maruyama step with scalar noise. -/
def emStep (μ σ : E → ℝ → E) (dt t ξ : ℝ) (x : E) : E :=
  x + dt • μ x t + (Real.sqrt dt * ξ) • σ x t

/-- Milstein step with scalar noise:
`EM + ½ ((√Δt ξ)² - Δt) (D_xσ · σ)`. -/
def milsteinStep (μ σ : E → ℝ → E) (dt t ξ : ℝ) (x : E) : E :=
  emStep μ σ dt t ξ x +
    ((1 / 2 : ℝ) * ((Real.sqrt dt * ξ) ^ 2 - dt)) • (fderiv ℝ (fun y => σ y t) x) (σ x t)

/-- Additive scalar noise: Milstein equals Euler–Maruyama, sample by sample. -/
@[tmio T, powerlib_foundation] theorem milsteinStep_eq_emStep {μ σ : E → ℝ → E}
    (hσ : ∀ x y t, σ x t = σ y t) (dt t ξ : ℝ) (x : E) :
    milsteinStep μ σ dt t ξ x = emStep μ σ dt t ξ x := by
  have hconst : (fun y => σ y t) = fun _ => σ x t := funext fun y => hσ y x t
  simp [milsteinStep, hconst]

/-- Additive scalar noise: Milstein and Euler–Maruyama trajectories driven by the same
samples coincide. -/
@[powerlib_foundation] theorem milstein_trajectory_eq_em {μ σ : E → ℝ → E}
    (hσ : ∀ x y t, σ x t = σ y t) (dt : ℝ) (ξ : ℕ → ℝ) (x y : ℕ → E) (h0 : x 0 = y 0)
    (hx : ∀ n, x (n + 1) = milsteinStep μ σ dt (n * dt) (ξ n) (x n))
    (hy : ∀ n, y (n + 1) = emStep μ σ dt (n * dt) (ξ n) (y n)) : x = y := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hx n, hy n, ih, milsteinStep_eq_emStep hσ]

/-! ### Several noise channels -/

/-- Euler–Maruyama step with `m` noise channels (columns `σ k`). -/
def emMultiStep {m : ℕ} (μ : E → ℝ → E) (σ : Fin m → E → ℝ → E) (dt t : ℝ) (ξ : Fin m → ℝ)
    (x : E) : E :=
  x + dt • μ x t + ∑ k, (Real.sqrt dt * ξ k) • σ k x t

/-- General Milstein step with given iterated integrals `I k₁ k₂`. -/
def milsteinMultiStep {m : ℕ} (μ : E → ℝ → E) (σ : Fin m → E → ℝ → E) (dt t : ℝ)
    (ξ : Fin m → ℝ) (I : Fin m → Fin m → ℝ) (x : E) : E :=
  emMultiStep μ σ dt t ξ x +
    ∑ k₁, ∑ k₂, I k₁ k₂ • (fderiv ℝ (fun y => σ k₂ y t) x) (σ k₁ x t)

/-- Additive multi-channel noise: Milstein equals Euler–Maruyama for every choice of the
iterated integrals (Lévy areas are irrelevant). -/
@[powerlib_foundation] theorem milsteinMultiStep_eq_emMultiStep {m : ℕ} {μ : E → ℝ → E}
    {σ : Fin m → E → ℝ → E} (hσ : ∀ k x y t, σ k x t = σ k y t) (dt t : ℝ)
    (ξ : Fin m → ℝ) (I : Fin m → Fin m → ℝ) (x : E) :
    milsteinMultiStep μ σ dt t ξ I x = emMultiStep μ σ dt t ξ x := by
  have hconst : ∀ k, (fun y => σ k y t) = fun _ => σ k x t :=
    fun k => funext fun y => hσ k y x t
  simp [milsteinMultiStep, hconst]

/-! ### Commutative noise -/

variable {n m : ℕ}

/-- Partial derivative `∂_{x_j} Σ_{ik}(x)`. -/
def diffusionPartial (S : (Fin n → ℝ) → Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ)
    (i : Fin n) (k : Fin m) (j : Fin n) : ℝ :=
  fderiv ℝ (fun y => S y i k) x (Pi.single j 1)

/-- The commutative-noise condition as written in the source note. -/
def NoteCommutative (S : (Fin n → ℝ) → Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ x i l j, ∑ k, S x i k * diffusionPartial S x l k j =
    ∑ k, S x l k * diffusionPartial S x i k j

/-- The correct commutative-noise condition `L^{k₁} σ_{i k₂} = L^{k₂} σ_{i k₁}`. -/
def Commutative (S : (Fin n → ℝ) → Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ x i k₁ k₂, ∑ l, S x l k₁ * diffusionPartial S x i k₂ l =
    ∑ l, S x l k₂ * diffusionPartial S x i k₁ l

/-- Scalar state, two channels, diffusion row `(1, x)`. -/
def exampleDiffusion (x : Fin 1 → ℝ) : Matrix (Fin 1) (Fin 2) ℝ := !![1, x 0]

/-- The note's condition holds for `σ = (1, x)` but the correct commutativity condition
fails: the note's test is not sufficient. -/
@[powerlib_foundation] theorem noteCommutative_not_sufficient :
    NoteCommutative exampleDiffusion ∧ ¬ Commutative exampleDiffusion := by
  constructor
  · intro x i l j
    rw [Subsingleton.elim i l]
  · intro h
    have h1 := h 0 0 0 1
    have hd1 : diffusionPartial exampleDiffusion 0 0 1 0 = 1 := by
      have : (fun y : Fin 1 → ℝ => exampleDiffusion y 0 1) =
          fun y => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) y := by
        funext y; simp [exampleDiffusion]
      simp only [diffusionPartial, this, ContinuousLinearMap.fderiv]
      simp
    have hd0 : diffusionPartial exampleDiffusion 0 0 0 0 = 0 := by
      have : (fun y : Fin 1 → ℝ => exampleDiffusion y 0 0) = fun _ => 1 := by
        funext y; simp [exampleDiffusion]
      simp only [diffusionPartial, this]
      simp
    simp only [Fin.sum_univ_one, hd1, hd0] at h1
    simp [exampleDiffusion] at h1

end powerlib.Numerics
