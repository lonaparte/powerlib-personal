import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.KleinKramers
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! # Generalized detailed balance of a diffusion: probability current, reversible drift, parity

Laws of the coefficient conditions for (generalized) detailed balance of a diffusion on `ℝⁿ`
with drift `A`, diffusion matrix `B` and a parity `ε` of the coordinates (`+1` even, `−1` odd
under time reversal), with a positive stationary density `ρ`.

Scope.
* Foundation (generic calculus and algebra), for an arbitrary drift, diffusion matrix and density
  on `Fin n → ℝ`. Partial derivatives are one-variable derivatives along a coordinate (`pd`,
  through `Function.update`). The stationary Fokker–Planck operator is written in divergence form
  `L*ρ = −Σᵢ ∂ᵢ Jᵢ` of the probability current `Jᵢ = Aᵢ ρ − ½ Σⱼ ∂ⱼ(Bᵢⱼ ρ)` (`fpOp`, `current`);
  where the terms are differentiable it expands, by linearity of the derivative, to the textbook
  form `−Σᵢ ∂ᵢ(Aᵢ ρ) + ½ Σᵢⱼ ∂ᵢ∂ⱼ(Bᵢⱼ ρ)`.
* `GenDetailedBalance` is the coefficient characterization of detailed balance: a parity
  `εᵢ = ±1`, a positive density `ρ`, `εᵢ εⱼ Bᵢⱼ(εx) = Bᵢⱼ(x)`, the drift condition
  `εᵢ Aᵢ(εx) ρ(x) = −Aᵢ(x) ρ(x) + Σⱼ ∂ⱼ(Bᵢⱼ ρ)(x)` and stationarity `L*ρ = 0`. With `ε ≡ 1` it
  is detailed balance proper (zero probability current, `current_eq_of_drift`). That these
  conditions are equivalent to the time-reversal symmetry of the stationary Markov process
  (`p(x, t; y, 0) = p(εy, t; εx, 0)`), and every statement about laws or paths, is not
  formalized. `ρ` is required positive, not normalized: a refutation covers every positive
  solution, normalizable or not; densities with zeros are not covered.

Source: C. W. Gardiner, *Handbook of Stochastic Methods* (3rd ed., 2004), §5.3.5 (detailed
balance of a Fokker–Planck equation, conditions (5.3.53), reversible and irreversible drift);
H. Risken, *The Fokker–Planck Equation* (2nd ed., 1989), §6.4 (detailed balance, the
irreversible-drift potential condition and the divergence-free reversible current);
work-sync `theory/T-fokker-planck.md` §1.1, §1.3 (operator, probability flux), whose
one-dimensional flux is `Stochastic.FP.flux1` (`theorem/Stochastic/FokkerPlanck.lean`).

Results.
* `current_eq_of_drift`: under the drift condition at `x` the probability current is the
  reversible current, `Jᵢ(x) = A^rev_i(x) ρ(x)` with `A^rev = ½(A(x) − ε A(εx))` (`revDrift`).
* `fpOp_eq_of_drift`: under the drift condition at every state, `L*ρ = −Σᵢ ∂ᵢ(A^rev_i ρ)`;
  stationarity is then the divergence-free reversible current. No regularity is assumed.
* `irrDrift_eq_zero_of_noiseless`: a coordinate without noise (`Bᵢⱼ ≡ 0` for every `j`) carries
  no irreversible drift, `A^irr_i(x) = ½(Aᵢ(x) + εᵢ Aᵢ(εx)) = 0` (`irrDrift`), wherever
  `ρ(x) ≠ 0`.
* Calculus tools: `pd_mul_of_update` (a factor constant along the coordinate leaves the partial
  derivative), `differentiable_comp_update`, `eq_mul_exp_of_hasDerivAt` (`f' = c f` integrates
  to `f(t) = f(s) e^{C(t) − C(s)}`, `C' = c`) and `slice_of_affine`: if
  `∂ₜ r = (a(t) − c z) r`, the slices `r(t₂, ·)`, `r(t₁, ·)` differ by `e^{… − c z (t₂ − t₁)}` and
  their `z`-derivatives by `− c (t₂ − t₁) r` (the integrated mixed-partial identity, first
  derivatives only); coordinate lines of `Fin 3 → ℝ` (`update_vec3_zero`, `pd_vec3_zero`, …).
* `kk_genDetailedBalance` (non-vacuity): the Klein–Kramers system `q̇ = p/M`,
  `ṗ = −V'(q) − D p/M` (`kkDrift`) with momentum diffusion `2 D T` (fluctuation–dissipation)
  satisfies generalized detailed balance under the momentum flip `(q, p) ↦ (q, −p)` with the
  Gibbs density `e^{−H/T}` (`Stochastic.KleinKramers.gibbs`).
-/

noncomputable section
namespace powerlib.Stochastic.DetailedBalance

open Real Matrix

variable {n : ℕ}

/-! ## Current, operator, drift splitting -/

/-- Partial derivative of `g` in the coordinate `j` at `x`. -/
def pd (g : (Fin n → ℝ) → ℝ) (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t => g (Function.update x j t)) (x j)

/-- Time reversal `x ↦ εx`, componentwise, for a parity `ε`. -/
def reversal (ε x : Fin n → ℝ) : Fin n → ℝ := fun i => ε i * x i

/-- Probability current `Jᵢ = Aᵢ ρ − ½ Σⱼ ∂ⱼ(Bᵢⱼ ρ)` of the drift `A`, the diffusion matrix `B`
and the density `ρ`. -/
def current (A : (Fin n → ℝ) → Fin n → ℝ) (B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (ρ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  A x i * ρ x - 1 / 2 * ∑ j, pd (fun y => B y i j * ρ y) j x

/-- Stationary Fokker–Planck operator in divergence form `L*ρ = −Σᵢ ∂ᵢ Jᵢ`. -/
def fpOp (A : (Fin n → ℝ) → Fin n → ℝ) (B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (ρ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  -∑ i, pd (fun y => current A B ρ y i) i x

/-- Reversible part of the drift, `A^rev_i(x) = ½(Aᵢ(x) − εᵢ Aᵢ(εx))`. -/
def revDrift (A : (Fin n → ℝ) → Fin n → ℝ) (ε x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (A x i - ε i * A (reversal ε x) i) / 2

/-- Irreversible part of the drift, `A^irr_i(x) = ½(Aᵢ(x) + εᵢ Aᵢ(εx))`. -/
def irrDrift (A : (Fin n → ℝ) → Fin n → ℝ) (ε x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (A x i + ε i * A (reversal ε x) i) / 2

/-- **Generalized detailed balance** with parity `ε` and stationary density `ρ` (Gardiner
(5.3.53), Risken §6.4): `εᵢ = ±1`, `ρ > 0`, the diffusion condition, the drift condition and
stationarity. With `ε ≡ 1` it is detailed balance (zero probability current). -/
structure GenDetailedBalance (A : (Fin n → ℝ) → Fin n → ℝ)
    (B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ) (ρ : (Fin n → ℝ) → ℝ) :
    Prop where
  parity : ∀ i, ε i = 1 ∨ ε i = -1
  pos : ∀ x, 0 < ρ x
  diffusion : ∀ x i j, ε i * ε j * B (reversal ε x) i j = B x i j
  drift : ∀ x i, ε i * A (reversal ε x) i * ρ x =
    -(A x i * ρ x) + ∑ j, pd (fun y => B y i j * ρ y) j x
  stationary : ∀ x, fpOp A B ρ x = 0

variable {A : (Fin n → ℝ) → Fin n → ℝ} {B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {ε : Fin n → ℝ} {ρ : (Fin n → ℝ) → ℝ}

/-- A factor that is constant along the coordinate `j` through `x` leaves the partial derivative:
`∂ⱼ(a g)(x) = a(x) ∂ⱼ g(x)`. -/
@[tmio T, powerlib_foundation] theorem pd_mul_of_update {a g : (Fin n → ℝ) → ℝ} {j : Fin n}
    {x : Fin n → ℝ} (h : ∀ t, a (Function.update x j t) = a x) :
    pd (fun y => a y * g y) j x = a x * pd g j x := by
  unfold pd
  simp_rw [h]
  exact deriv_const_mul_field _

/-- **The current under the drift condition** is the reversible current `A^rev ρ`. -/
@[tmio T, powerlib_foundation] theorem current_eq_of_drift {x : Fin n → ℝ} {i : Fin n}
    (h : ε i * A (reversal ε x) i * ρ x = -(A x i * ρ x) + ∑ j, pd (fun y => B y i j * ρ y) j x) :
    current A B ρ x i = revDrift A ε x i * ρ x := by
  have hs : ∑ j, pd (fun y => B y i j * ρ y) j x = ε i * A (reversal ε x) i * ρ x + A x i * ρ x :=
    by linarith
  unfold current revDrift
  rw [hs]
  ring

/-- **Stationarity under the drift condition**: if the drift condition holds at every state,
`L*ρ = −Σᵢ ∂ᵢ(A^rev_i ρ)`, the divergence of the reversible current. -/
@[tmio T, powerlib_foundation] theorem fpOp_eq_of_drift
    (h : ∀ x i, ε i * A (reversal ε x) i * ρ x =
      -(A x i * ρ x) + ∑ j, pd (fun y => B y i j * ρ y) j x) (x : Fin n → ℝ) :
    fpOp A B ρ x = -∑ i, pd (fun y => revDrift A ε y i * ρ y) i x := by
  unfold fpOp
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hJ : (fun y => current A B ρ y i) = fun y => revDrift A ε y i * ρ y :=
    funext fun y => current_eq_of_drift (h y i)
  rw [hJ]

/-- **A noise-free coordinate carries no irreversible drift**: if the row `i` of the diffusion
matrix vanishes identically, the drift condition at `x` with `ρ(x) ≠ 0` forces
`½(Aᵢ(x) + εᵢ Aᵢ(εx)) = 0`. -/
@[tmio T, powerlib_foundation] theorem irrDrift_eq_zero_of_noiseless {i : Fin n}
    (hB : ∀ y j, B y i j = 0) {x : Fin n → ℝ} (hρ : ρ x ≠ 0)
    (h : ε i * A (reversal ε x) i * ρ x = -(A x i * ρ x) + ∑ j, pd (fun y => B y i j * ρ y) j x) :
    irrDrift A ε x i = 0 := by
  have hs : ∑ j, pd (fun y => B y i j * ρ y) j x = 0 :=
    Finset.sum_eq_zero fun j _ => by simp [pd, hB]
  rw [hs, add_zero] at h
  have h' : (A x i + ε i * A (reversal ε x) i) * ρ x = 0 := by linarith
  unfold irrDrift
  rw [(mul_eq_zero.mp h').resolve_right hρ, zero_div]

/-- **Integration of `f' = c f`**: with an antiderivative `C` of `c`,
`f(t) = f(s) e^{C(t) − C(s)}`. -/
@[tmio T, powerlib_foundation] theorem eq_mul_exp_of_hasDerivAt {f c C : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (c t * f t) t) (hC : ∀ t, HasDerivAt C (c t) t) (s t : ℝ) :
    f t = f s * exp (C t - C s) := by
  have hg : ∀ u, HasDerivAt (fun u => f u * exp (-C u)) 0 u := by
    intro u
    have h := (hf u).mul (hC u).neg.exp
    convert h using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt)
    (fun u => (hg u).deriv) t s
  have e : ∀ u, f u = f u * exp (-C u) * exp (C u) := fun u => by
    rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
  rw [e t, hconst, mul_assoc, ← exp_add]
  ring_nf

/-- **Slices of an affine logarithmic derivative**: if `∂ₜ r(t, z) = (a(t) − c z) r(t, z)` for all
`t, z` (`C' = a`), then `r(t₂, ·) = r(t₁, ·) e^{C(t₂) − C(t₁) − c z (t₂ − t₁)}`, and the
`z`-derivatives of the two slices differ by the drift of the exponent:
`∂_z r(t₂, z) = (∂_z r(t₁, z) − c (t₂ − t₁) r(t₁, z)) e^{C(t₂) − C(t₁) − c z (t₂ − t₁)}`
(the integrated form of `∂_z ∂ₜ log r = −c`, without second derivatives). -/
@[tmio T, powerlib_foundation] theorem slice_of_affine {r : ℝ → ℝ → ℝ} {a C : ℝ → ℝ} {c : ℝ}
    (hC : ∀ t, HasDerivAt C (a t) t)
    (hr : ∀ t z, HasDerivAt (fun s => r s z) ((a t - c * z) * r t z) t) {t₁ z : ℝ}
    (hz : DifferentiableAt ℝ (fun y => r t₁ y) z) (t₂ : ℝ) :
    r t₂ z = r t₁ z * exp (C t₂ - C t₁ - c * z * (t₂ - t₁)) ∧
      deriv (fun y => r t₂ y) z = (deriv (fun y => r t₁ y) z - c * (t₂ - t₁) * r t₁ z) *
        exp (C t₂ - C t₁ - c * z * (t₂ - t₁)) := by
  have hval : ∀ y, r t₂ y = r t₁ y * exp (C t₂ - C t₁ - c * y * (t₂ - t₁)) := fun y => by
    have h := eq_mul_exp_of_hasDerivAt (f := fun s => r s y) (c := fun s => a s - c * y)
      (C := fun s => C s - c * y * s) (fun t => hr t y)
      (fun t => by
        have h := (hC t).sub ((hasDerivAt_id' t).const_mul (c * y))
        simp only [mul_one] at h
        exact h) t₁ t₂
    rw [h]
    ring_nf
  refine ⟨hval z, ?_⟩
  have hE : HasDerivAt (fun y => exp (C t₂ - C t₁ - c * y * (t₂ - t₁)))
      (exp (C t₂ - C t₁ - c * z * (t₂ - t₁)) * -(c * (t₂ - t₁))) z := by
    have h := ((((hasDerivAt_id z).const_mul c).mul_const (t₂ - t₁)).const_sub
      (C t₂ - C t₁)).exp
    convert h using 1 <;> simp only [id, mul_one]
  have hd : HasDerivAt (fun y => r t₁ y * exp (C t₂ - C t₁ - c * y * (t₂ - t₁)))
      (deriv (fun y => r t₁ y) z * exp (C t₂ - C t₁ - c * z * (t₂ - t₁)) +
        r t₁ z * (exp (C t₂ - C t₁ - c * z * (t₂ - t₁)) * -(c * (t₂ - t₁)))) z :=
    hz.hasDerivAt.mul hE
  rw [show (fun y => r t₂ y) = fun y => r t₁ y * exp (C t₂ - C t₁ - c * y * (t₂ - t₁)) from
    funext hval, hd.deriv]
  ring

/-- A differentiable function restricted to a coordinate line is differentiable. -/
@[tmio T, powerlib_foundation] theorem differentiable_comp_update {g : (Fin n → ℝ) → ℝ}
    (hg : Differentiable ℝ g) (x : Fin n → ℝ) (j : Fin n) :
    Differentiable ℝ (fun t => g (Function.update x j t)) := fun t =>
  (hg _).comp t (hasDerivAt_update x j t).differentiableAt

/-! ## Coordinate lines of `Fin 3 → ℝ` -/

@[tmio T, powerlib_foundation] theorem update_vec3_zero (a b c t : ℝ) :
    Function.update ![a, b, c] 0 t = ![t, b, c] := by
  funext i; fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem update_vec3_one (a b c t : ℝ) :
    Function.update ![a, b, c] 1 t = ![a, t, c] := by
  funext i; fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem update_vec3_two (a b c t : ℝ) :
    Function.update ![a, b, c] 2 t = ![a, b, t] := by
  funext i; fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem pd_vec3_zero (g : (Fin 3 → ℝ) → ℝ) (a b c : ℝ) :
    pd g 0 ![a, b, c] = deriv (fun t => g ![t, b, c]) a := by
  simp [pd, update_vec3_zero]

@[tmio T, powerlib_foundation] theorem pd_vec3_one (g : (Fin 3 → ℝ) → ℝ) (a b c : ℝ) :
    pd g 1 ![a, b, c] = deriv (fun t => g ![a, t, c]) b := by
  simp [pd, update_vec3_one]

@[tmio T, powerlib_foundation] theorem pd_vec3_two (g : (Fin 3 → ℝ) → ℝ) (a b c : ℝ) :
    pd g 2 ![a, b, c] = deriv (fun t => g ![a, b, t]) c := by
  simp [pd, update_vec3_two]

/-! ## Non-vacuity: the Klein–Kramers system -/

open powerlib.Stochastic.KleinKramers (gibbs gibbs_pos gibbs_hasDerivAt_q gibbs_hasDerivAt_p)

/-- Klein–Kramers drift `(q̇, ṗ) = (p/M, −V'(q) − D p/M)` on `Fin 2 → ℝ`. -/
def kkDrift (M D : ℝ) (V' : ℝ → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![x 1 / M, -V' (x 0) - D * (x 1 / M)]

/-- Momentum diffusion `2 D T` (fluctuation–dissipation), no position diffusion. -/
def kkDiffusion (D T : ℝ) (_ : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 2 * D * T]

/-- Momentum flip `(q, p) ↦ (q, −p)`. -/
def kkFlip : Fin 2 → ℝ := ![1, -1]

@[tmio T, powerlib_foundation] private lemma pd_gibbs_zero {V V' : ℝ → ℝ}
    (hV : ∀ q, HasDerivAt V (V' q) q) (M T : ℝ) (x : Fin 2 → ℝ) :
    pd (fun y => gibbs V M T (y 0) (y 1)) 0 x = -(V' (x 0)) / T * gibbs V M T (x 0) (x 1) := by
  unfold pd
  simp only [Function.update_self, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    not_false_eq_true, Function.update_of_ne]
  exact (gibbs_hasDerivAt_q hV M T (x 1) (x 0)).deriv

@[tmio T, powerlib_foundation] private lemma pd_gibbs_one (V : ℝ → ℝ) {M : ℝ} (hM : M ≠ 0)
    (T : ℝ) (x : Fin 2 → ℝ) :
    pd (fun y => gibbs V M T (y 0) (y 1)) 1 x = -(x 1 / (M * T)) * gibbs V M T (x 0) (x 1) := by
  unfold pd
  simp only [Function.update_self, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne]
  exact (gibbs_hasDerivAt_p V hM T (x 0) (x 1)).deriv

@[tmio T, powerlib_foundation] private lemma kk_drift {M D T : ℝ} {V V' : ℝ → ℝ} (hM : M ≠ 0)
    (hT : T ≠ 0) (x : Fin 2 → ℝ) (i : Fin 2) :
    kkFlip i * kkDrift M D V' (reversal kkFlip x) i * gibbs V M T (x 0) (x 1) =
      -(kkDrift M D V' x i * gibbs V M T (x 0) (x 1)) +
        ∑ j, pd (fun y => kkDiffusion D T y i j * gibbs V M T (y 0) (y 1)) j x := by
  have hc : ∀ (i j : Fin 2), pd (fun y => kkDiffusion D T y i j * gibbs V M T (y 0) (y 1)) j x =
      kkDiffusion D T x i j * pd (fun y => gibbs V M T (y 0) (y 1)) j x :=
    fun i j => pd_mul_of_update fun _ => rfl
  simp only [hc, Fin.sum_univ_two]
  fin_cases i
  · simp [kkDrift, kkFlip, kkDiffusion, reversal]
    ring
  · simp [kkDrift, kkFlip, kkDiffusion, reversal, pd_gibbs_one V hM]
    field_simp
    ring

/-- **Klein–Kramers satisfies generalized detailed balance** under the momentum flip with the
Gibbs density `e^{−H/T}`, `H = p²/(2M) + V(q)`, when the momentum diffusion is `2 D T`
(fluctuation–dissipation): the definition is not vacuous, and it holds for the two-state swing
models of the library read as Klein–Kramers systems. -/
@[tmio T, powerlib_foundation] theorem kk_genDetailedBalance {M D T : ℝ} {V V' : ℝ → ℝ}
    (hV : ∀ q, HasDerivAt V (V' q) q) (hM : M ≠ 0) (hT : T ≠ 0) :
    GenDetailedBalance (kkDrift M D V') (kkDiffusion D T) kkFlip
      (fun x => gibbs V M T (x 0) (x 1)) where
  parity i := by fin_cases i <;> simp [kkFlip]
  pos x := gibbs_pos V M T (x 0) (x 1)
  diffusion x i j := by fin_cases i <;> fin_cases j <;> simp [kkFlip, kkDiffusion]
  drift x i := kk_drift hM hT x i
  stationary x := by
    rw [fpOp_eq_of_drift (kk_drift hM hT)]
    have hr : ∀ y : Fin 2 → ℝ, ∀ i,
        revDrift (kkDrift M D V') kkFlip y i = ![y 1 / M, -V' (y 0)] i :=
      fun y i => by fin_cases i <;> simp [revDrift, kkDrift, kkFlip, reversal] <;> ring
    simp only [hr, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [pd_mul_of_update (a := fun y => y 1 / M) (fun t => by simp),
      pd_mul_of_update (a := fun y => -V' (y 0)) (fun t => by simp), pd_gibbs_zero hV,
      pd_gibbs_one V hM]
    field_simp
    ring

end powerlib.Stochastic.DetailedBalance
