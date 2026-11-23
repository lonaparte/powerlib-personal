import theorem.Linear.Transfer
import theorem.Linear.Stability
import theorem.Linear.EigenMap
import theorem.Criteria.Lyapunov

/-! # Hurwitz matrices and exponential decay of linear solutions (foundation)

LTI lemmas, kept beside the `Linear/` modules, relating a real square matrix `A` to the decay of
the solutions of `ẋ = A x`.

Scope.
* Every statement is about arbitrary matrices; nothing here describes a physical system. Every
  behavioural statement is a generic implication about an arbitrary matrix (Rules §3,
  foundation); no family is defined.

Source: standard linear-systems facts, used by work-sync theory/T-dae-systems.md §1.4,
theory/T-small-signal-stability.md §1.3–§1.4 and the frequency / synchronization /
parametric-resonance notes.

Results.
* Coordinate solutions (`x : ℝ → Fin k → ℝ` with `∀ t, HasDerivAt x (A *ᵥ x t) t`, Euclidean
  norm through `WithLp.toLp 2`): `isTrajectoryOn_toLp` links them to LeanForControl's affine
  linear field `affineLinearVectorField A 0`; `hasDerivAt_ofLp_solution`,
  `exists_linear_trajectory` (every initial state has one).
* Curves in `ℝⁿ = EuclideanSpace ℝ (Fin n)` with `∀ t, HasDerivAt e (Linear.op A (e t)) t`:
  `exists_global_bound_of_isHurwitz` (the linear hub
  `Linear.globallyExponentiallyStable_of_isHurwitz`) and `isHurwitz_of_global_bound` (through
  `Linear.holds_iff_isHurwitz`); `linear_decay_of_isHurwitz`, `isHurwitz_of_linear_decay` are
  the same two directions for coordinate solutions, read through `WithLp.toLp 2`.
* `not_decay_of_eigenvector`: a real eigenvector `A v = μ v`, `v ≠ 0`, with `−a < μ` excludes
  `Flow.Decay` of the linear field at the rate `a`.
* Spectral facts: `isHurwitz_sub_smul_one` (if every eigenvalue has real part `< c`, `A − c I` is
  Hurwitz; the shift is the Möbius map `λ ↦ λ − c`, `Linear.isHurwitz_mobius_iff`);
  `spectrallyStable_of_real_pairs` (spectral stability from real eigen-pairs);
  `tendsto_of_spectrallyStable` (on any finite index type, a spectrally stable state matrix makes
  every constant-input forward solution converge to an equilibrium, by transport to `Fin N`).
-/

noncomputable section
namespace powerlib.LTI
open Matrix LinearSystems

/-! ## Coordinate solutions of `ẋ = A x` -/

section Coordinates

variable {k : ℕ}

/-- A global coordinate solution of `ẋ = A x` is, on every interval, a solution segment of
LeanForControl's affine linear field of `A` centred at the origin. -/
@[tmio T, powerlib_foundation] theorem isTrajectoryOn_toLp {A : Matrix (Fin k) (Fin k) ℝ}
    {x : ℝ → Fin k → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) (t₀ t₁ : ℝ) :
    IsTrajectoryOn (fun t => WithLp.toLp 2 (x t)) (affineLinearVectorField A 0) t₀ t₁ := by
  intro t _
  have h := Dynamics.hasDerivAt_toLp (hx t)
  convert h.hasDerivWithinAt using 1
  show Linear.op A (WithLp.toLp 2 (x t) - 0) = _
  rw [sub_zero]
  rfl

/-- The coordinates of the matrix-exponential solution solve `ẋ = A x` globally. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_ofLp_solution (A : Matrix (Fin k) (Fin k) ℝ)
    (x₀ : Fin k → ℝ) (t : ℝ) :
    HasDerivAt (fun s => WithLp.ofLp (Linear.solution A 0 0 (WithLp.toLp 2 x₀) s))
      (A *ᵥ WithLp.ofLp (Linear.solution A 0 0 (WithLp.toLp 2 x₀) t)) t := by
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).hasFDerivAt.comp_hasDerivAt t
    (Linear.solution_hasDerivAt A 0 0 (WithLp.toLp 2 x₀) t)
  convert h using 1
  · rfl
  · show _ = WithLp.ofLp (Linear.op A (Linear.solution A 0 0 (WithLp.toLp 2 x₀) t - 0))
    rw [sub_zero]
    rfl

/-- Every initial state has a global coordinate solution of `ẋ = A x`. -/
@[tmio T, powerlib_foundation] theorem exists_linear_trajectory (A : Matrix (Fin k) (Fin k) ℝ)
    (x₀ : Fin k → ℝ) : ∃ x : ℝ → Fin k → ℝ, (∀ t, HasDerivAt x (A *ᵥ x t) t) ∧ x 0 = x₀ :=
  ⟨fun s => WithLp.ofLp (Linear.solution A 0 0 (WithLp.toLp 2 x₀) s),
    hasDerivAt_ofLp_solution A x₀, by simp⟩

end Coordinates

/-! ## Curves in `ℝⁿ` -/

section Euclidean

open Complex Filter Topology Set

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Hurwitz `A`: every global solution of `ẋ = A x` decays exponentially from time `0` (the
linear hub `Linear.globallyExponentiallyStable_of_isHurwitz`). -/
@[tmio T, powerlib_foundation] theorem exists_global_bound_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) :
    ∃ K > 0, ∃ rate > 0, ∀ e : ℝ → ℝⁿ, (∀ t, HasDerivAt e (Linear.op A (e t)) t) →
      ∀ t, 0 ≤ t → ‖e t‖ ≤ K * Real.exp (-(rate * t)) * ‖e 0‖ := by
  obtain ⟨C, a, hC, ha, hb⟩ :=
    (Linear.globallyExponentiallyStable_of_isHurwitz (0 : ℝⁿ) hA).exists_constant
  refine ⟨C, by linarith, a, ha, fun e he t ht => ?_⟩
  have htraj : IsTrajectoryOn e (affineLinearVectorField A 0) 0 t := fun s _ => by
    simpa [Linear.affine_apply] using (he s).hasDerivWithinAt
  have := hb 0 t e htraj t ⟨ht, le_rfl⟩
  simpa [neg_mul, sub_zero] using this

/-- A uniform exponential bound on every global solution of `ẋ = A x` forces `A` to be Hurwitz
(the linear hub `Linear.holds_iff_isHurwitz`). -/
@[tmio T, powerlib_foundation] theorem isHurwitz_of_global_bound {A : Matrix (Fin n) (Fin n) ℝ}
    {K rate : ℝ} (hrate : 0 < rate)
    (hb : ∀ e : ℝ → ℝⁿ, (∀ t, HasDerivAt e (Linear.op A (e t)) t) →
      ∀ t, 0 ≤ t → ‖e t‖ ≤ K * Real.exp (-(rate * t)) * ‖e 0‖) : IsHurwitz A := by
  refine (Linear.holds_iff_isHurwitz (0 : ℝⁿ)
    Flow.Property.attractive_globallyExponentiallyStable).mp ?_
  show Flow.GloballyExponentiallyStable _ _
  refine ⟨Linear.affine_isEquilibrium A 0, Linear.forwardComplete A 0, rate, hrate, K, ?_⟩
  intro t₀ t₁ φ hφ t ht
  have heq := Linear.trajectory_eq_solution hφ t ht
  set ψ : ℝ → ℝⁿ := fun s => Linear.solution A 0 t₀ (φ t₀) (s + t₀) with hψdef
  have hψ : ∀ s, HasDerivAt ψ (Linear.op A (ψ s)) s := by
    intro s
    have h := (Linear.solution_hasDerivAt A 0 t₀ (φ t₀) (s + t₀)).comp_add_const s t₀
    simpa [Linear.affine_apply, hψdef] using h
  have hψ0 : ψ 0 = φ t₀ := by simp [hψdef]
  have hψt : ψ (t - t₀) = φ t := by simp [hψdef, heq]
  have hbound := hb ψ hψ (t - t₀) (by linarith [ht.1])
  rw [hψt, hψ0] at hbound
  simp only [sub_zero]
  rwa [neg_mul]

end Euclidean

/-! ## The coordinate decay test -/

section CoordinateDecay

variable {k : ℕ}

/-- Hurwitz `A`: every global coordinate solution of `ẋ = A x` decays exponentially in the
Euclidean norm (`exists_global_bound_of_isHurwitz` read through `WithLp.toLp 2`). -/
@[tmio T, powerlib_foundation] theorem linear_decay_of_isHurwitz {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : IsHurwitz A) :
    ∃ K > 0, ∃ rate > 0, ∀ x : ℝ → Fin k → ℝ, (∀ t, HasDerivAt x (A *ᵥ x t) t) → ∀ t, 0 ≤ t →
      ‖WithLp.toLp 2 (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖ := by
  obtain ⟨K, hK, rate, hr, hb⟩ := exists_global_bound_of_isHurwitz hA
  exact ⟨K, hK, rate, hr, fun x hx => hb _ fun s => Dynamics.hasDerivAt_toLp (hx s)⟩

/-- Conversely, exponential decay of every global coordinate solution of `ẋ = A x` forces `A` to
be Hurwitz (`isHurwitz_of_global_bound` read through `WithLp.ofLp`). -/
@[tmio T, powerlib_foundation] theorem isHurwitz_of_linear_decay {A : Matrix (Fin k) (Fin k) ℝ}
    {K rate : ℝ} (hr : 0 < rate)
    (hdecay : ∀ x : ℝ → Fin k → ℝ, (∀ t, HasDerivAt x (A *ᵥ x t) t) → ∀ t, 0 ≤ t →
      ‖WithLp.toLp 2 (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖WithLp.toLp 2 (x 0)‖) :
    IsHurwitz A :=
  isHurwitz_of_global_bound hr fun e he t ht => by
    simpa using hdecay (fun s => WithLp.ofLp (e s)) (fun s =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).hasFDerivAt.comp_hasDerivAt s
        (he s)) t ht

end CoordinateDecay

/-! ## A slow real eigenmode excludes decay -/

section Eigenvector

open Set Filter
open scoped Topology

/-- A real eigenvector `A v = μ v`, `v ≠ 0`, with `−a < μ` excludes decay at the rate `a`: the
eigenmode `e^{μ t} v` is a solution segment that decays too slowly. -/
@[tmio T, powerlib_foundation] theorem not_decay_of_eigenvector {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {μ a : ℝ} {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) (hAv : Linear.op A v = μ • v)
    (hμ : -a < μ) : ¬ Flow.Decay (affineLinearVectorField A 0) 0 a := by
  rintro ⟨C, hC⟩
  have hμa : 0 < μ + a := by linarith
  set T : ℝ := |C| / (μ + a) with hT_def
  have hT0 : 0 ≤ T := div_nonneg (abs_nonneg C) hμa.le
  have hsol : IsTrajectoryOn (fun t => Real.exp (μ * t) • v) (affineLinearVectorField A 0) 0 T := by
    intro t _
    have h : HasDerivAt (fun t => Real.exp (μ * t) • v) ((Real.exp (μ * t) * μ) • v) t := by
      simpa using ((hasDerivAt_id t).const_mul μ).exp.smul_const v
    have e : affineLinearVectorField A 0 (Real.exp (μ * t) • v) = (Real.exp (μ * t) * μ) • v := by
      rw [Linear.affine_apply, sub_zero, map_smul, hAv, smul_smul, mul_comm]
    show HasDerivWithinAt _ (affineLinearVectorField A 0 (Real.exp (μ * t) • v)) _ _
    rw [e]
    exact h.hasDerivWithinAt
  have hb := hC 0 T _ hsol T ⟨hT0, le_rfl⟩
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  simp only [sub_zero, mul_zero, Real.exp_zero, one_smul, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le] at hb
  have h1 : Real.exp (μ * T) ≤ C * Real.exp (-a * T) := le_of_mul_le_mul_right hb hvn
  have h2 : Real.exp ((μ + a) * T) ≤ C := by
    have h := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (a * T)).le
    have e₁ : Real.exp (a * T) * Real.exp (μ * T) = Real.exp ((μ + a) * T) := by
      rw [← Real.exp_add]; congr 1; ring
    have e₂ : Real.exp (a * T) * (C * Real.exp (-a * T)) = C := by
      rw [mul_left_comm, ← Real.exp_add, show a * T + -a * T = 0 by ring, Real.exp_zero, mul_one]
    linarith
  have hprod : (μ + a) * T = |C| := by
    rw [hT_def]
    field_simp
  rw [hprod] at h2
  linarith [Real.add_one_le_exp |C|, le_abs_self C]

end Eigenvector

/-! ## Spectral facts -/

section Spectral

open Set Filter
open scoped Topology

/-- Shifting by `c I` shifts the spectrum: if every eigenvalue of `A` has real part `< c`,
then `A − c I` is Hurwitz. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_sub_smul_one {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    {c : ℝ} (h : ∀ (lam : ℂ) (v : Fin d → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = lam • v →
      lam.re < c) : LinearSystems.IsHurwitz (A - c • 1) := by
  rw [Linear.isHurwitz_mobius_iff (A := A) (α := 1) (β := -c) (γ := 0) (δ := 1) (by norm_num)
    (by simp) (by rw [zero_smul, zero_add, one_smul, Matrix.one_mul, one_smul, neg_smul,
      sub_eq_add_neg])]
  intro lam v hv heig
  have := h lam v hv heig
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_neg, one_mul, zero_mul,
    zero_add, div_one, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  linarith

/-- Spectral stability from real eigen-pairs: if every real pair `(a, b)` with
`A a = x a − y b`, `A b = y a + x b` and `x ≥ 0` vanishes, then `A` is spectrally stable
(`a ± i b` would be an eigenvector for `x ± i y`; the real and imaginary parts of a complex
eigenpair are `Criteria.mulVec_re_im_of_eigenpair`). Generic. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_of_real_pairs {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ∀ (x y : ℝ) (a b : ι → ℝ), A *ᵥ a = x • a - y • b → A *ᵥ b = y • a + x • b →
      0 ≤ x → a = 0 ∧ b = 0) : Linear.SpectrallyStable A := by
  refine Linear.spectrallyStable_iff_forall_eigen.mpr fun s v hv heig => ?_
  by_contra hre
  push Not at hre
  obtain ⟨h1, h2⟩ := Criteria.mulVec_re_im_of_eigenpair heig
  obtain ⟨ha, hb⟩ := h s.re s.im _ _ h1 h2 hre
  exact hv (funext fun j => Complex.ext (by simpa using congrFun ha j)
    (by simpa using congrFun hb j))

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Spectral stability of the state matrix gives convergence of every constant-input forward
solution to an equilibrium, on any finite index type (transport to `Fin N`, then the linear hub
`Linear.globallyAsymptoticallyStable_of_isHurwitz`). Generic in the matrices. -/
@[tmio T, powerlib_foundation] theorem tendsto_of_spectrallyStable {A : Matrix ι ι ℝ}
    {B : Matrix ι κ ℝ} (hA : Linear.SpectrallyStable A) {u : κ → ℝ} {e : ι → ℝ}
    (he : A *ᵥ e + B *ᵥ u = 0) {x : ℝ → ι → ℝ}
    (hx : ∀ t ≥ 0, HasDerivWithinAt x (A *ᵥ x t + B *ᵥ u) (Ici 0) t) :
    Tendsto x atTop (𝓝 e) := by
  set eq := Fintype.equivFin ι
  set A' := A.reindex eq eq
  have hA' : IsHurwitz A' :=
    (Linear.spectrallyStable_iff_isHurwitz _).1 ((Linear.spectrallyStable_reindex eq A).2 hA)
  set e' : EuclideanSpace ℝ (Fin (Fintype.card ι)) := WithLp.toLp 2 (e ∘ eq.symm)
  set y : ℝ → EuclideanSpace ℝ (Fin (Fintype.card ι)) := fun t => WithLp.toLp 2 (x t ∘ eq.symm)
  have hBu : B *ᵥ u = -(A *ᵥ e) := eq_neg_of_add_eq_zero_right he
  have hy : IsIntegralCurveOn y (fun _ z => affineLinearVectorField A' e' z) (Ici 0) := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t => x t ∘ eq.symm) ((A *ᵥ x t + B *ᵥ u) ∘ eq.symm)
        (Ici 0) t :=
      hasDerivWithinAt_pi.2 fun i => hasDerivWithinAt_pi.1 (hx t ht) (eq.symm i)
    have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Fintype.card ι) => ℝ)).symm
      |>.hasFDerivAt.comp_hasDerivWithinAt t h1
    refine h2.congr_deriv ?_
    show _ = affineLinearVectorField A' e' (y t)
    rw [Linear.affine_apply]
    change WithLp.toLp 2 ((A *ᵥ x t + B *ᵥ u) ∘ eq.symm) =
      WithLp.toLp 2 (A' *ᵥ ((x t - e) ∘ eq.symm))
    congr 1
    rw [hBu, show A' = A.submatrix eq.symm eq.symm from rfl, Matrix.submatrix_mulVec_equiv]
    funext i
    simp only [Function.comp_def, Equiv.symm_symm, Pi.add_apply,
      Pi.neg_apply, Pi.sub_apply]
    rw [show (fun j => x t (eq.symm (eq j)) - e (eq.symm (eq j))) = x t - e by
      funext j; simp, Matrix.mulVec_sub]
    simp [sub_eq_add_neg]
  have hlim := (Linear.globallyAsymptoticallyStable_of_isHurwitz e' hA').2.2.2 0 y hy
  have hc : Continuous (fun w : EuclideanSpace ℝ (Fin (Fintype.card ι)) => WithLp.ofLp w ∘ eq) :=
    by fun_prop
  have := (hc.tendsto _).comp hlim
  simpa [Function.comp_def, y, e'] using this

end Reindex

end Spectral

end powerlib.LTI
