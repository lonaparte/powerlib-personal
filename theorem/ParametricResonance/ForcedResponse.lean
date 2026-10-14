import theorem.Linear.Transfer
import theorem.LTI.Decay
import theorem.Dynamics.Coordinates

/-! # Forced response of an LTI plant and the constant-Jacobian obstruction

Generic linear-systems facts used by the parametric-resonance notes: the exact forced response of
a Hurwitz LTI plant, and why a constant state Jacobian rules out parametric instability. No
converter model is fixed here.

Scope.
* Forced LTI plant `ẋ = A₀ x + Re(b e^{jωt})` on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (Euclidean
  norm, `A₀` acting as `Linear.op A₀`), constant real `A₀`, constant complex drive vector `b`
  (`b = f_u + jω f_{u̇}` in the source, which covers both the angle and the angle-rate entry),
  real pump frequency `ω`, continuous time, global solutions: curves `x : ℝ → ℝⁿ` with
  `∀ t, HasDerivAt x (Linear.op A₀ (x t) + forcing b ω t) t`.
* Input-affine plants `ż = f(z, u(t))` whose state Jacobian is a constant matrix `A₀` for all
  `z` and all `u` (i.e. `D²_z f = 0` and `A₁ = ∂_u ∂_z f = 0`), with an arbitrary input signal
  `u : ℝ → U` and an arbitrary reference solution `z_orb` (for instance a forced periodic orbit);
  solutions are global: `∀ t, HasDerivAt z (f (z t) (u t)) t`.
* These solution conditions are written out in the statements (behavioural notions are defined
  only in the semantic layer, `theorem/Flow/Defs.lean`).

Source: work-sync projects/vsc-parametric-oscillation/notes/theory-draft.md §2.1.1
(`x₁ = Re{χ e^{jω_p t}}`, `χ = (jω_pI − A₀)⁻¹ b`), §2.1.2 ("若系统在工作区内完全线性，并且扰动
不直接改变 A₀，则 D²f = 0 且 A₁ = 0，于是 J(t) = A₀"); references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md §2. The uniqueness/attraction statement is a strengthening asked
for in the task list. Additive forcing: projects/gfl-gfm-stability-tree/notes/concepts/
nonautonomous-criteria.md (加性强迫不进雅可比); projects/vsc-parametric-oscillation/references/
gfl-gfm-contrast/archive/notes/concepts/forced-orbit-and-bandwidth.md (冻结 `ζ` 对 `ε` 恒定).

Results.
* `forcedOrbit_solves` — if `jω` is not an eigenvalue of `A₀`, `x₁(t) = Re(χ e^{jωt})` with
  `χ = (jωI − A₀)⁻¹ b` solves the forced equation exactly (first-order forced response).
* `forced_error_bound` — if `A₀` is Hurwitz, every solution converges exponentially to `x₁`
  (`‖x(t) − x₁(t)‖ ≤ K e^{−rate t} ‖x(0) − x₁(0)‖`); `forced_periodic_unique`: `x₁` is the only
  solution of period `T = 2π/ω` (unique attracting periodic solution).
* `affine_of_const_jacobian` — a constant state Jacobian forces `f(z, u) = A₀ z + f(0, u)`;
  the variational matrix along any orbit is `J(t) ≡ A₀` (`jacobian_along_orbit`), and
  `orbitExponentiallyStable_iff`: every orbit is exponentially stable (all solutions converge to
  it at a uniform exponential rate) iff `A₀` is Hurwitz — no parametric instability can arise.
* `jacobian_additive_forcing` — for `f_ε(x, t) = f(x) + ε g(t)` the state Jacobian is `Df(x)`
  for every `ε, t`; in particular the frozen Jacobian at a fixed operating point, and every
  quantity computed from it (frozen damping ratio, frozen spectrum), does not depend on `ε` by
  construction.

Decay and the converse (a uniform exponential bound on every global solution of `ẋ = A x` forces
`A` Hurwitz; `LTI.exists_global_bound_of_isHurwitz`, `LTI.isHurwitz_of_global_bound` in
`theorem/LTI/Decay.lean`) go through the linear stability hub
(`Linear.globallyExponentiallyStable_of_isHurwitz`, `Linear.holds_iff_isHurwitz`) applied to the
field `LinearSystems.affineLinearVectorField A 0`.
-/

noncomputable section
namespace powerlib.ParametricResonance

open Matrix Complex Filter Topology Set LinearSystems

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The first-order forced response -/

/-- Complex amplitude `χ = (jωI − A₀)⁻¹ b`. -/
def forcedAmplitude (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℂ) (ω : ℝ) : Fin n → ℂ :=
  (Linear.characteristicMatrix A ((ω : ℂ) * I))⁻¹ *ᵥ b

/-- First-order forced orbit `x₁(t) = Re(χ e^{jωt})`. -/
def forcedOrbit (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℂ) (ω t : ℝ) : ℝⁿ :=
  WithLp.toLp 2 fun i => (forcedAmplitude A b ω i * Complex.exp ((ω : ℂ) * t * I)).re

/-- Additive drive `Re(b e^{jωt})`. -/
def forcing (b : Fin n → ℂ) (ω t : ℝ) : ℝⁿ :=
  WithLp.toLp 2 fun i => (b i * Complex.exp ((ω : ℂ) * t * I)).re

@[powerlib_foundation] theorem characteristicMatrix_mulVec_forcedAmplitude
    {A : Matrix (Fin n) (Fin n) ℝ} {ω : ℝ} (b : Fin n → ℂ)
    (h : (Linear.characteristicMatrix A ((ω : ℂ) * I)).det ≠ 0) :
    Linear.characteristicMatrix A ((ω : ℂ) * I) *ᵥ forcedAmplitude A b ω = b := by
  rw [forcedAmplitude, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h),
    Matrix.one_mulVec]

/-- `jω χ = A₀ χ + b`. -/
@[powerlib_foundation] theorem forcedAmplitude_eq {A : Matrix (Fin n) (Fin n) ℝ} {ω : ℝ}
    (b : Fin n → ℂ) (h : (Linear.characteristicMatrix A ((ω : ℂ) * I)).det ≠ 0) :
    ((ω : ℂ) * I) • forcedAmplitude A b ω =
      A.map (algebraMap ℝ ℂ) *ᵥ forcedAmplitude A b ω + b := by
  have h1 := characteristicMatrix_mulVec_forcedAmplitude b h
  rw [Linear.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    at h1
  exact sub_eq_iff_eq_add'.mp h1

/-- A Hurwitz matrix has no eigenvalue on the imaginary axis. -/
@[powerlib_foundation] theorem det_characteristicMatrix_imag_ne_zero
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) (ω : ℝ) :
    (Linear.characteristicMatrix A ((ω : ℂ) * I)).det ≠ 0 := by
  intro h
  have := (Linear.spectrallyStable_iff_isHurwitz A).mpr hA _ h
  simp at this

/-- `x₁` is a global solution of the forced LTI equation `ẋ = A₀ x + Re(b e^{jωt})`. -/
@[powerlib_foundation] theorem forcedOrbit_solves {A : Matrix (Fin n) (Fin n) ℝ} {ω : ℝ}
    (b : Fin n → ℂ) (h : (Linear.characteristicMatrix A ((ω : ℂ) * I)).det ≠ 0) :
    ∀ t, HasDerivAt (forcedOrbit A b ω)
      (Linear.op A (forcedOrbit A b ω t) + forcing b ω t) t := by
  intro t
  apply Dynamics.hasDerivAt_of_coords
  intro i
  set χ := forcedAmplitude A b ω with hχdef
  have he : HasDerivAt (fun s : ℂ => χ i * Complex.exp ((ω : ℂ) * s * I))
      (χ i * ((ω : ℂ) * I * Complex.exp ((ω : ℂ) * t * I))) (t : ℂ) := by
    have h1 : HasDerivAt (fun s : ℂ => (ω : ℂ) * s * I) ((ω : ℂ) * I) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul (ω : ℂ)).mul_const I
    have h2 := h1.cexp
    have h3 := h2.const_mul (χ i)
    convert h3 using 1; ring
  have hre := he.real_of_complex
  have hfun : (fun x => forcedOrbit A b ω x i) =
      fun x : ℝ => (χ i * Complex.exp ((ω : ℂ) * x * I)).re := rfl
  rw [hfun]
  convert hre using 1
  -- identify the derivative componentwise
  have hχ := congrFun (forcedAmplitude_eq b h) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hχ
  have hmul : χ i * ((ω : ℂ) * I * Complex.exp ((ω : ℂ) * t * I)) =
      (A.map (algebraMap ℝ ℂ) *ᵥ χ) i * Complex.exp ((ω : ℂ) * t * I) +
        b i * Complex.exp ((ω : ℂ) * t * I) := by
    rw [← add_mul, ← hχ]; ring
  rw [hmul, Complex.add_re]
  change (A *ᵥ (forcedOrbit A b ω t).ofLp) i + (forcing b ω t).ofLp i = _
  simp only [forcing, forcedOrbit, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Finset.sum_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hχdef, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.coe_algebraMap, zero_mul, sub_zero]
  ring

/-- `x₁` has the forcing period `T` when `ω T = 2π`. -/
@[powerlib_foundation] theorem forcedOrbit_periodic {A : Matrix (Fin n) (Fin n) ℝ}
    (b : Fin n → ℂ) {ω T : ℝ} (hT : ω * T = 2 * Real.pi) (t : ℝ) :
    forcedOrbit A b ω (t + T) = forcedOrbit A b ω t := by
  simp only [forcedOrbit]
  congr 1
  funext i
  have hT' : (ω : ℂ) * T = 2 * Real.pi := by exact_mod_cast hT
  have : (ω : ℂ) * ((t + T : ℝ) : ℂ) * I = (ω : ℂ) * t * I + 2 * Real.pi * I := by
    push_cast; linear_combination I * hT'
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The deviation of a global solution `x` of the forced equation from the forced orbit obeys
the homogeneous LTI equation `ė = A₀ e`. -/
@[powerlib_foundation] theorem isTrajectory_sub_forcedOrbit {A : Matrix (Fin n) (Fin n) ℝ}
    {ω : ℝ} {b : Fin n → ℂ} (h : (Linear.characteristicMatrix A ((ω : ℂ) * I)).det ≠ 0)
    {x : ℝ → ℝⁿ} (hx : ∀ t, HasDerivAt x (Linear.op A (x t) + forcing b ω t) t) :
    ∀ t, HasDerivAt (fun t => x t - forcedOrbit A b ω t)
      (Linear.op A (x t - forcedOrbit A b ω t)) t := by
  intro t
  have h1 := (hx t).sub (forcedOrbit_solves b h t)
  convert h1 using 1
  rw [map_sub]; abel

/-- Hurwitz `A₀`: every global solution of the forced equation converges exponentially to the
forced orbit. -/
@[powerlib_foundation] theorem forced_error_bound {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) (b : Fin n → ℂ) (ω : ℝ) :
    ∃ K > 0, ∃ rate > 0, ∀ x : ℝ → ℝⁿ,
      (∀ t, HasDerivAt x (Linear.op A (x t) + forcing b ω t) t) → ∀ t, 0 ≤ t →
      ‖x t - forcedOrbit A b ω t‖ ≤
        K * Real.exp (-(rate * t)) * ‖x 0 - forcedOrbit A b ω 0‖ := by
  obtain ⟨K, hK, rate, hrate, hbound⟩ := LTI.exists_global_bound_of_isHurwitz hA
  exact ⟨K, hK, rate, hrate, fun x hx t ht =>
    hbound _ (isTrajectory_sub_forcedOrbit (det_characteristicMatrix_imag_ne_zero hA ω) hx) t ht⟩

/-- Hurwitz `A₀`: the forced orbit is the only global solution of the forced equation with the
forcing period `T = 2π/ω` (`ω T = 2π`, `T > 0`). -/
@[powerlib_foundation] theorem forced_periodic_unique {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) (b : Fin n → ℂ) {ω T : ℝ} (hT0 : 0 < T)
    (hT : ω * T = 2 * Real.pi) {x : ℝ → ℝⁿ}
    (hx : ∀ t, HasDerivAt x (Linear.op A (x t) + forcing b ω t) t)
    (hper : ∀ t, x (t + T) = x t) : x = forcedOrbit A b ω := by
  obtain ⟨K, hK, rate, hrate, hbound⟩ := forced_error_bound hA b ω
  set e := fun t => x t - forcedOrbit A b ω t with he
  have hep : ∀ t (k : ℕ), e (t + k * T) = e t := by
    intro t k
    induction k with
    | zero => simp
    | succ k ih =>
      have : t + ((k + 1 : ℕ) : ℝ) * T = (t + k * T) + T := by push_cast; ring
      rw [this]
      simp only [he] at ih ⊢
      rw [hper, forcedOrbit_periodic b hT, ih]
  funext t
  rw [← sub_eq_zero]
  change e t = 0
  by_contra hne
  have hpos : 0 < ‖e t‖ := norm_pos_iff.mpr hne
  -- `‖e(t + kT)‖ → 0` along `k → ∞`
  have hlim : Tendsto (fun k : ℕ => K * Real.exp (-(rate * (t + k * T))) *
      ‖e 0‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => rate * (t + k * T)) atTop atTop := by
      apply Tendsto.const_mul_atTop hrate
      apply tendsto_atTop_add_const_left
      exact (tendsto_natCast_atTop_atTop).atTop_mul_const hT0
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := (h2.const_mul K).mul_const ‖e 0‖
    simpa using h3
  obtain ⟨k, hk⟩ := (((eventually_ge_atTop (⌈-t / T⌉₊)).and
    (hlim.eventually (gt_mem_nhds hpos)))).exists
  have hkT : 0 ≤ t + k * T := by
    have h1 : -t / T ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk.1)
    rw [div_le_iff₀ hT0] at h1
    linarith
  have := hbound x hx (t + k * T) hkT
  change ‖e (t + k * T)‖ ≤ K * Real.exp (-(rate * (t + k * T))) * ‖e 0‖ at this
  rw [hep] at this
  linarith [hk.2]

/-! ## Constant state Jacobian: no parametric channel -/

variable {U : Type*}

/-- A constant state Jacobian `A₀` (`D²f = 0`, `A₁ = 0`) forces `f(z, u) = A₀ z + f(0, u)`. -/
@[powerlib_foundation] theorem affine_of_const_jacobian {f : ℝⁿ → U → ℝⁿ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ z u, HasFDerivAt (fun z => f z u) (Linear.op A) z)
    (z : ℝⁿ) (u : U) : f z u = Linear.op A z + f 0 u := by
  have hd : ∀ w, HasFDerivAt (fun w => f w u - Linear.op A w) (0 : ℝⁿ →L[ℝ] ℝⁿ) w := by
    intro w
    have h := (hf w u).sub (Linear.op A).hasFDerivAt
    rw [sub_self] at h
    exact h
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f := fun w => f w u - Linear.op A w)
    (fun w => (hd w).differentiableAt) (fun w => (hd w).fderiv)
  have := hc z 0
  simp only [map_zero, sub_zero] at this
  rw [← this]; abel

/-- Along any orbit the variational matrix is the constant `A₀`. -/
@[powerlib_foundation] theorem jacobian_along_orbit {f : ℝⁿ → U → ℝⁿ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ z u, HasFDerivAt (fun z => f z u) (Linear.op A) z)
    (u : ℝ → U) (z_orb : ℝ → ℝⁿ) (t : ℝ) :
    fderiv ℝ (fun z => f z (u t)) (z_orb t) = Linear.op A :=
  (hf (z_orb t) (u t)).fderiv

/-- With a constant state Jacobian, any reference solution `z_orb` of `ż = f(z, u(t))` is
exponentially stable iff `A₀` is Hurwitz: the forcing can produce a large response but never a
parametric instability. Exponential stability of `z_orb` means that every global solution
converges to it at a uniform exponential rate,
`‖z(t) − z_orb(t)‖ ≤ K e^{−rate t} ‖z(0) − z_orb(0)‖` for `t ≥ 0`. -/
@[powerlib_foundation] theorem orbitExponentiallyStable_iff {f : ℝⁿ → U → ℝⁿ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ z u, HasFDerivAt (fun z => f z u) (Linear.op A) z)
    {u : ℝ → U} {z_orb : ℝ → ℝⁿ} (horb : ∀ t, HasDerivAt z_orb (f (z_orb t) (u t)) t) :
    (∃ K > 0, ∃ rate > 0, ∀ z : ℝ → ℝⁿ, (∀ t, HasDerivAt z (f (z t) (u t)) t) → ∀ t, 0 ≤ t →
      ‖z t - z_orb t‖ ≤ K * Real.exp (-(rate * t)) * ‖z 0 - z_orb 0‖) ↔ IsHurwitz A := by
  have haff := affine_of_const_jacobian hf
  constructor
  · rintro ⟨K, hK, rate, hrate, hb⟩
    refine LTI.isHurwitz_of_global_bound (K := K) hrate fun e he t ht => ?_
    have hz : ∀ s, HasDerivAt (fun s => z_orb s + e s) (f (z_orb s + e s) (u s)) s := by
      intro s
      have h1 := (horb s).add (he s)
      convert h1 using 1
      rw [haff (z_orb s + e s), haff (z_orb s), map_add]; abel
    have := hb _ hz t ht
    simpa using this
  · intro hA
    obtain ⟨K, hK, rate, hrate, hb⟩ := LTI.exists_global_bound_of_isHurwitz hA
    refine ⟨K, hK, rate, hrate, fun z hz t ht => ?_⟩
    have he : ∀ s, HasDerivAt (fun s => z s - z_orb s) (Linear.op A (z s - z_orb s)) s := by
      intro s
      have h1 := (hz s).sub (horb s)
      convert h1 using 1
      rw [haff (z s), haff (z_orb s), map_sub]; abel
    exact hb _ he t ht

/-! ### Additive forcing does not enter the Jacobian -/

/-- For `f_ε(x, t) = f(x) + ε g(t)` the state Jacobian is `Df(x)` for every `ε` and `t`. -/
@[powerlib_foundation] theorem jacobian_additive_forcing {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) (g : ℝ → E) (ε t : ℝ) (x : E) :
    fderiv ℝ (fun y => f y + ε • g t) x = fderiv ℝ f x :=
  fderiv_add_const _

end powerlib.ParametricResonance
