import theorem.Criteria.Routh3
import theorem.Dynamics.ConverseLinearization
import theorem.Synchronous.Swing
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability
import theorem.Spectral.Family

/-! # Grid-forming VSM with a first-order power filter on an infinite bus (three states)

Model boundary.
* State `z = (δ, ω, P_f) : Dynamics.State 3`, in this order: power angle of the internal
  EMF relative to the infinite bus (rad), angular-frequency deviation (rad/s), filtered
  (measured) active power (pu).
* Continuous time, autonomous (the grid-angle perturbation `u` is set to `0` in the
  stability statements):
  `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)`,
  with `K₀ = E V_g / X_g` (constant internal EMF, lossless grid reactance), virtual inertia
  `M`, damping `D`, filter bandwidth `ω_c`, active-power set-point `P₀`.  Active power is
  export-positive (GFM family exception, T-gfm-control §1.0).
* Excluded: voltage / reactive-power loop (constant `E`), inner current and voltage loops,
  current limiting, PLL, delays, PWM, network dynamics.  `M, D, ω_c` are independent (the
  droop+LPF limit `M → 0` is the separate two-state model `DroopLPF` below).
* Conclusions: equilibrium set and existence (`|P₀| ≤ K₀`), local exponential stability /
  instability of the loading equilibrium `(δ₀, 0, P₀)`, `δ₀ = arcsin(P₀/K₀)`, from the
  Jacobian computed by `fderiv` and the three-state Routh–Hurwitz criterion.  With
  `K = K₀ cos δ₀`: `ω_c > K/D − D/M` ⇒ stable, `ω_c < K/D − D/M` ⇒ unstable, hence (boundary
  excluded) stable ⇔ `K < D ω_c + D²/M` — light loading (large `K`) is the dangerous side.  On the
  boundary itself the equilibrium is asymptotically, not exponentially, stable (a supercritical
  Hopf point; `theorem/GFM/VSMLPFHopf.lean`).

Family and connection conclusions.
* `VSMLPF.family`: a complete system (`VSMLPF.Model`) is a parameter set with a selected angle
  `δ*`, read as the field translated so that the operating point `(δ*, 0, P₀)` is the origin
  (`Flow.Property.holds_shift_iff`).  Static requirements: balance `K₀ sin δ* = P₀`, positive
  `M, D, ω_c`, positive synchronizing coefficient `K = K₀ cos δ*`, the fast-filter Routh
  condition `K < D ω_c + D²/M`, and a destabilizing sign (`D ω_c + D²/M < K`, or `K < 0`).  The
  local sentences translate into the first four, instability into balance, positivity and a
  destabilizing sign, passivity into nothing (exact), the remaining sentences into the whole,
  inconsistent, language.  `VSMLPF.chain_le_semantics` proves soundness.  Within positive
  `M, D, ω_c` the local exponential translation is exact
  (`VSMLPF.exactUnder_locallyExponentiallyStable`): by the converse linearization theorem
  (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian`) local exponential stability of
  the operating point holds exactly when it is an equilibrium with a Hurwitz Jacobian, i.e.
  balanced with `0 < K < D ω_c + D²/M`; without positive `M, D, ω_c` it is not exact
  (`VSMLPF.not_exact_locallyExponentiallyStable`: the model `VSMLPF.negativeInertia` with
  `M = D = K₀ = −1`, `ω_c = 1` is locally exponentially stable).  The instability translation
  is not exact (`VSMLPF.not_exact_unstable`): instability is the failure of Lyapunov stability,
  so an unbalanced model (`VSMLPF.offEquilibrium`) is unstable
  (`VSMLPF.offEquilibrium_mem_den_unstable`, `Dynamics.unstable_of_ne_zero`). The local
  asymptotic and Lyapunov translations are not exact (`VSMLPF.not_exact_locallyAsymptoticallyStable`,
  `VSMLPF.not_exact_lyapunovStable`, the negative-inertia model, via
  `Spectral.not_exact_of_den_subset`); the Lyapunov translation is not exact even within positive
  `M, D, ω_c` (`VSMLPF.not_exactUnder_lyapunovStable`: the flat curve `VSMLPF.flatCurve`,
  `K₀ = P₀ = 0`, is Lyapunov stable, `VSMLPF.flatCurve_mem_den_lyapunovStable`). The local
  asymptotic translation is not exact even within positive `M, D, ω_c`
  (`VSMLPF.not_exactUnder_locallyAsymptoticallyStable`, in `theorem/GFM/VSMLPFHopf.lean`): on the
  Hopf boundary `K = D ω_c + D²/M` the Jacobian has a purely imaginary pair, and an explicit
  quartic Lyapunov function (`Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus`) shows
  that every physical boundary model is a weak stable focus
  (`VSMLPF.mem_den_locallyAsymptoticallyStable_of_hopf`; witness `VSMLPF.hopfBoundary`). Its exact
  denotation within positive `M, D, ω_c` is
  `VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`: a balanced angle with
  `0 < K ≤ D ω_c + D²/M`.
* Connection conclusions at the loading angle (`VSMLPF.atLoading`): `locallyExponentiallyStable`,
  `unstable`, and the exact boundary `locallyExponentiallyStable_iff` (a member-equivalence:
  local exponential stability iff `K < D ω_c + D²/M`, boundary excluded); new:
  `unstable_atAntiLoading` (the second equilibrium `π − δ₀` is a saddle) and, in
  `theorem/GFM/VSMLPFHopf.lean`, `locallyAsymptoticallyStable_iff` (local asymptotic stability iff
  `K ≤ D ω_c + D²/M`, boundary included).
* `DroopLPF.family` (two states, the `M → 0` limit) with the same pattern (within positive
  `D, ω_c` the local exponential translation is exact,
  `DroopLPF.exactUnder_locallyExponentiallyStable`, and not exact without that range,
  `DroopLPF.not_exact_locallyExponentiallyStable` with `DroopLPF.negativeDamping`; the
  instability translation is not exact, `DroopLPF.not_exact_unstable` with the unbalanced
  `DroopLPF.offEquilibrium`); within positive `D, ω_c` the local asymptotic translation is exact too
  (`DroopLPF.exactUnder_locallyAsymptoticallyStable`: the loop is the swing equation
  `(D/ω_c) δ̈ + D δ̇ = P₀ − K₀ sin δ` with the dissipated energy `DroopLPF.energy`; a vanishing power
  curve has a continuum of equilibria and a fold leaves the energy below its value on one side,
  `DroopLPF.energy_fold`), and the Lyapunov denotation is
  `DroopLPF.mem_den_lyapunovStable_iff_of_physical` (balanced with `K₀ cos δ* > 0` or `K₀ = 0`; a fold
  is unstable, `Dynamics.unstable_of_lie_nonpos_of_lie_pos`), so the Lyapunov translation is not
  exact within that range (`DroopLPF.not_exactUnder_lyapunovStable`, `DroopLPF.flatCurve`); without
  it neither translation is exact (`DroopLPF.not_exact_locallyAsymptoticallyStable`,
  `DroopLPF.not_exact_lyapunovStable`, the negative-damping model);
  `DroopLPF.locallyExponentiallyStable` (no Hopf boundary) is a connection conclusion; new:
  `DroopLPF.unstable_atAntiLoading`.
* Static evidence on the model: the equilibrium theorems `field_eq_zero_iff`,
  `exists_equilibrium_iff`, `field_equilibrium`.  The transfer functions, the boundary frequency,
  the first-order modulation `A₁`, the periodic time averages and the second-order reduction
  algebra are foundation, as before.

Corrections.
* projects/vsc-parametric-oscillation/…/gfl-gfm-parametric-contrast.md §15:
  `A₁^GFM = ω_c P₀ e_{P_f} e_δᵀ` is nonzero only when `P₀ ≠ 0` (`A₁_ne_zero_iff`); at zero
  load the grid-angle perturbation does not modulate the Jacobian to first order.

Source: work-sync projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md §15–§16; …/gfm-driven-gfl-parametric-resonance/notes/concepts/
gfm-periodic-source.md ("三态局部候选"); notes/theory-draft.md §1.3, §2.4;
references/gfl-gfm-contrast/archive/notes/concepts/contrast-conclusions.md (推论一, 推论二).
-/

noncomputable section
namespace powerlib.GFM
open Set Matrix
open powerlib.Dynamics (State)

/-- The state `(a, b, c)`. -/
def mk3 (a b c : ℝ) : State 3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![a, b, c]

@[simp, powerlib_foundation] theorem mk3_zero (a b c : ℝ) : mk3 a b c 0 = a := by simp [mk3]
@[simp, powerlib_foundation] theorem mk3_one (a b c : ℝ) : mk3 a b c 1 = b := by simp [mk3]
@[simp, powerlib_foundation] theorem mk3_two (a b c : ℝ) : mk3 a b c 2 = c := by simp [mk3]

@[powerlib_foundation] theorem state3_ext {x y : State 3} (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

@[fun_prop, powerlib_foundation] theorem coord3_contDiff {k : WithTop ℕ∞} (j : Fin 3) :
    ContDiff ℝ k (fun x : State 3 => x j) :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : State 3 →L[ℝ] ℝ).contDiff

@[powerlib_foundation] theorem toEuclideanCLM_apply3 (A : Matrix (Fin 3) (Fin 3) ℝ)
    (v : State 3) (i : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A v) i =
      A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 := by
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- If `a₂ a₁ < a₀`, the monic cubic `s³ + a₂ s² + a₁ s + a₀` has a root with positive real
part (strict violation of the Routh gap condition). -/
@[powerlib_foundation] theorem exists_cubic_root_re_pos_of_gap {a2 a1 a0 : ℝ}
    (h : a2 * a1 < a0) :
    ∃ s : ℂ, s ^ 3 + (a2 : ℂ) * s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧ 0 < s.re := by
  obtain ⟨r, hr⟩ := Criteria.exists_cubic_real_root a2 a1 a0
  by_cases hr0 : 0 < r
  · exact ⟨r, Criteria.cubic_real_root_complex hr, by rw [Complex.ofReal_re]; exact hr0⟩
  push Not at hr0
  set b := a2 + r with hb
  set c := a1 + r * a2 + r ^ 2 with hc
  have ha0 : a0 = -r * c := by rw [hc]; linear_combination hr
  have hgap : b * (c - r * b + r ^ 2) < 0 := by
    have : a0 - a2 * a1 = -(b * (c - r * b + r ^ 2)) := by rw [ha0, hb, hc]; ring
    linarith
  rcases lt_trichotomy b 0 with hbn | hb0 | hbp
  · obtain ⟨s, hs, hre⟩ := Criteria.exists_quadratic_root_re_pos_of_linear_neg (a0 := c) hbn
    exact ⟨s, by rw [Criteria.cubic_factor_of_root hr, hs, mul_zero], hre⟩
  · rw [hb0] at hgap; simp at hgap
  · have hcn : c < 0 := by
      have : c - r * b + r ^ 2 < 0 := by
        by_contra hn; push Not at hn; nlinarith
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hr0 hbp.le, sq_nonneg r]
    obtain ⟨q, hq, hqroot⟩ := Criteria.exists_quadratic_root_pos_of_const_neg (a1 := b) hcn
    refine ⟨q, ?_, by rw [Complex.ofReal_re]; exact hq⟩
    rw [Criteria.cubic_factor_of_root hr, Criteria.quadratic_real_root_complex hqroot, mul_zero]

/-- Parameters of the three-state VSM + power-filter model. -/
structure VSMLPF where
  M : ℝ
  D : ℝ
  ωc : ℝ
  P0 : ℝ
  K0 : ℝ

namespace VSMLPF

variable (g : VSMLPF)

/-- The closed-loop vector field (grid angle `u = 0`). -/
def field (x : State 3) : State 3 :=
  mk3 (x 1) ((g.P0 - x 2 - g.D * x 1) / g.M) (g.ωc * (g.K0 * Real.sin (x 0) - x 2))

/-- Loading angle `δ₀ = arcsin(P₀ / K₀)`. -/
def δ0 : ℝ := Real.arcsin (g.P0 / g.K0)

/-- Synchronizing coefficient `K = K₀ cos δ₀`. -/
def K : ℝ := g.K0 * Real.cos g.δ0

/-- Loading equilibrium `(δ₀, 0, P₀)`. -/
def equilibrium : State 3 := mk3 g.δ0 0 g.P0

/-- Jacobian at angle `δ`. -/
def jacobian (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 0, -g.D / g.M, -1 / g.M; g.ωc * (g.K0 * Real.cos δ), 0, -g.ωc]

@[simp, powerlib_foundation] theorem field_apply_zero (x : State 3) : g.field x 0 = x 1 := by
  simp [field]

@[simp, powerlib_foundation] theorem field_apply_one (x : State 3) :
    g.field x 1 = (g.P0 - x 2 - g.D * x 1) / g.M := by simp [field]

@[simp, powerlib_foundation] theorem field_apply_two (x : State 3) :
    g.field x 2 = g.ωc * (g.K0 * Real.sin (x 0) - x 2) := by simp [field]

@[powerlib_foundation] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k g.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa using coord3_contDiff (k := k) 1
  · simp only [Fin.mk_one, Fin.isValue, field_apply_one]; fun_prop
  · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two]; fun_prop

@[powerlib_foundation] theorem hasFDerivAt_field (x : State 3) :
    HasFDerivAt g.field (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (g.jacobian (x 0))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := x)
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, field_apply_zero]
    convert h1 using 1
    · rfl
    apply ContinuousLinearMap.ext; intro v
    simp [jacobian, toEuclideanCLM_apply3]
  · simp only [Fin.mk_one, Fin.isValue, field_apply_one]
    have h := (((hasFDerivAt_const g.P0 x).sub h2).sub (h1.const_mul g.D)).const_mul g.M⁻¹
    convert h using 1
    · funext y; simp [div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, toEuclideanCLM_apply3]
      ring
  · simp only [Fin.reduceFinMk, Fin.isValue, field_apply_two]
    have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
    have h := ((hs.const_mul g.K0).sub h2).const_mul g.ωc
    convert h using 1
    · funext y; simp
    apply ContinuousLinearMap.ext; intro v
    simp [jacobian, toEuclideanCLM_apply3]
    ring

@[powerlib_foundation] theorem fderiv_field (x : State 3) :
    fderiv ℝ g.field x = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (g.jacobian (x 0)) :=
  (g.hasFDerivAt_field x).fderiv

@[simp, powerlib_foundation] theorem trace_jacobian (δ : ℝ) :
    (g.jacobian δ).trace = -g.D / g.M - g.ωc := by
  simp [jacobian, Matrix.trace_fin_three]; ring

@[simp, powerlib_foundation] theorem det_jacobian (δ : ℝ) :
    (g.jacobian δ).det = -(g.ωc * (g.K0 * Real.cos δ)) / g.M := by
  simp [jacobian, Matrix.det_fin_three]; ring

@[simp, powerlib_foundation] theorem principalMinorSum_jacobian (δ : ℝ) :
    Criteria.principalMinorSum (g.jacobian δ) = g.D * g.ωc / g.M := by
  simp [Criteria.principalMinorSum, jacobian]; ring

/-- `M · det(sI − J) = M s³ + (D + M ω_c) s² + D ω_c s + ω_c K₀ cos δ`. -/
@[powerlib_foundation] theorem characteristic_polynomial (hM : g.M ≠ 0) (δ : ℝ) (s : ℂ) :
    (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ) s).det =
      (g.M : ℂ) * s ^ 3 + ((g.D + g.M * g.ωc : ℝ) : ℂ) * s ^ 2 + ((g.D * g.ωc : ℝ) : ℂ) * s +
        ((g.ωc * (g.K0 * Real.cos δ) : ℝ) : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_three', trace_jacobian, det_jacobian,
    principalMinorSum_jacobian]
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp
  ring

/-! ## Equilibria -/

/-- Equilibria: `ω = 0`, `P_f = P₀` and `K₀ sin δ = P₀`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_iff (hM : g.M ≠ 0) (hω : g.ωc ≠ 0) (x : State 3) :
    g.field x = 0 ↔ x 1 = 0 ∧ x 2 = g.P0 ∧ g.K0 * Real.sin (x 0) = g.P0 := by
  constructor
  · intro h
    have e1 := congrArg (fun y : State 3 => y 0) h
    have e2 := congrArg (fun y : State 3 => y 1) h
    have e3 := congrArg (fun y : State 3 => y 2) h
    simp only [field_apply_zero, field_apply_one, field_apply_two, PiLp.zero_apply] at e1 e2 e3
    rw [e1, mul_zero, sub_zero, div_eq_zero_iff, or_iff_left hM, sub_eq_zero] at e2
    rw [mul_eq_zero, or_iff_right hω, sub_eq_zero] at e3
    exact ⟨e1, e2.symm, e3.trans e2.symm⟩
  · rintro ⟨h1, h2, h3⟩
    apply state3_ext <;> simp [h1, h2, h3]

/-- Equilibria exist iff `|P₀| ≤ K₀ = E V_g / X_g`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem exists_equilibrium_iff (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    (hK0 : 0 < g.K0) : (∃ x, g.field x = 0) ↔ |g.P0| ≤ g.K0 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨-, -, h3⟩ := (g.field_eq_zero_iff hM hω x).mp hx
    rw [← h3, abs_mul, abs_of_pos hK0]
    exact mul_le_of_le_one_right hK0.le (Real.abs_sin_le_one _)
  · intro h
    refine ⟨g.equilibrium, (g.field_eq_zero_iff hM hω _).mpr ⟨by simp [equilibrium],
      by simp [equilibrium], ?_⟩⟩
    have ha : |g.P0 / g.K0| ≤ 1 := by rw [abs_div, abs_of_pos hK0, div_le_one hK0]; exact h
    simp only [equilibrium, mk3_zero, δ0]
    rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]
    field_simp

/-- The loading point `(δ₀, 0, P₀)` is an equilibrium when `|P₀| ≤ K₀`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_equilibrium (hM : g.M ≠ 0) (hω : g.ωc ≠ 0) (hK0 : 0 < g.K0)
    (h : |g.P0| ≤ g.K0) : g.field g.equilibrium = 0 := by
  obtain ⟨x, hx⟩ := (g.exists_equilibrium_iff hM hω hK0).mpr h
  have ha : |g.P0 / g.K0| ≤ 1 := by rw [abs_div, abs_of_pos hK0, div_le_one hK0]; exact h
  refine (g.field_eq_zero_iff hM hω _).mpr ⟨by simp [equilibrium], by simp [equilibrium], ?_⟩
  simp only [equilibrium, mk3_zero, δ0]
  rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]
  field_simp

/-- Strictly inside the loadability limit the synchronizing coefficient is positive. -/
@[powerlib_foundation] theorem K_pos (hK0 : 0 < g.K0) (h : |g.P0| < g.K0) : 0 < g.K := by
  have ha : |g.P0 / g.K0| < 1 := by rw [abs_div, abs_of_pos hK0, div_lt_one hK0]; exact h
  simp only [K, δ0, Real.cos_arcsin]
  apply mul_pos hK0 (Real.sqrt_pos.mpr _)
  have : (g.P0 / g.K0) ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (g.P0 / g.K0)]
  linarith

/-! ## Physical parameters -/

/-- Physical parameter positivity. -/
structure Pos : Prop where
  M : 0 < g.M
  D : 0 < g.D
  ωc : 0 < g.ωc
  K0 : 0 < g.K0

variable {g}

/-! ## Linearized transfer function and boundary frequency (foundation) -/

variable (g)

/-- At the Routh boundary `ω_c = K/D − D/M` the characteristic polynomial has the purely
imaginary root `j ω_H`, `ω_H² = K/M − D²/M²`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_boundary (hM : g.M ≠ 0) (hD : g.D ≠ 0)
    (hωc : g.ωc = g.K / g.D - g.D / g.M) {ωH : ℝ}
    (hH : ωH ^ 2 = g.K / g.M - g.D ^ 2 / g.M ^ 2) :
    (Linear.characteristicMatrix (g.jacobian g.δ0) ((ωH : ℂ) * Complex.I)).det = 0 := by
  have hc := g.characteristic_polynomial hM g.δ0 ((ωH : ℂ) * Complex.I)
  have hK' : g.K0 * Real.cos g.δ0 = g.K := rfl
  rw [hK'] at hc
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hzero : (g.M : ℂ) * ((ωH : ℂ) * Complex.I) ^ 3 +
      ((g.D + g.M * g.ωc : ℝ) : ℂ) * ((ωH : ℂ) * Complex.I) ^ 2 +
      ((g.D * g.ωc : ℝ) : ℂ) * ((ωH : ℂ) * Complex.I) + ((g.ωc * g.K : ℝ) : ℂ) = 0 := by
    have h2 : ((ωH : ℂ) * Complex.I) ^ 2 = -((ωH ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    have h3 : ((ωH : ℂ) * Complex.I) ^ 3 = -((ωH ^ 2 : ℝ) : ℂ) * ((ωH : ℂ) * Complex.I) := by
      rw [pow_succ, h2]
    rw [h3, h2]
    have e : (g.M : ℂ) * (-((ωH ^ 2 : ℝ) : ℂ) * ((ωH : ℂ) * Complex.I)) +
        ((g.D + g.M * g.ωc : ℝ) : ℂ) * -((ωH ^ 2 : ℝ) : ℂ) +
        ((g.D * g.ωc : ℝ) : ℂ) * ((ωH : ℂ) * Complex.I) + ((g.ωc * g.K : ℝ) : ℂ) =
        ((g.ωc * g.K - (g.D + g.M * g.ωc) * ωH ^ 2 : ℝ) : ℂ) +
          (((g.D * g.ωc - g.M * ωH ^ 2) * ωH : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e]
    have hre : g.ωc * g.K - (g.D + g.M * g.ωc) * ωH ^ 2 = 0 := by
      rw [hH, hωc]; field_simp; ring
    have him : g.D * g.ωc - g.M * ωH ^ 2 = 0 := by
      rw [hH, hωc]; field_simp; ring
    rw [hre, him]
    simp
  rw [hzero] at hc
  exact (mul_eq_zero.mp hc).resolve_left hM'

/-- Exact `u → δ` transfer function of the three-state model,
`T(s) = ω_c K / ((s + ω_c)(M s² + D s) + ω_c K)`. -/
def Texact (s : ℂ) : ℂ :=
  (g.ωc : ℂ) * (g.K : ℂ) / ((s + (g.ωc : ℂ)) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) +
    (g.ωc : ℂ) * (g.K : ℂ))

/-- Second-order swing reduction `T_red(s) = K / (M s² + D s + K)`. -/
def Tred (s : ℂ) : ℂ := (g.K : ℂ) / ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s + (g.K : ℂ))

/-- `T_exact(2jω₀) = 1 / (−3 − 8 ζ r_c + j(4ζ − 8 r_c))` with `ω₀ = √(K/M)`,
`ζ = D / (2√(MK))`, `r_c = ω₀/ω_c`. -/
@[powerlib_foundation] theorem Texact_two_j_omega0 (hM : 0 < g.M) (hK : 0 < g.K)
    (hω : 0 < g.ωc) :
    g.Texact (2 * Complex.I * (Real.sqrt (g.K / g.M) : ℂ)) =
      1 / (((-3 - 8 * (g.D / (2 * Real.sqrt (g.M * g.K))) *
          (Real.sqrt (g.K / g.M) / g.ωc) : ℝ) : ℂ) +
        ((4 * (g.D / (2 * Real.sqrt (g.M * g.K))) - 8 * (Real.sqrt (g.K / g.M) / g.ωc) : ℝ) : ℂ) *
          Complex.I) := by
  have hsM0 : 0 < Real.sqrt g.M := Real.sqrt_pos.mpr hM
  have hsK0 : 0 < Real.sqrt g.K := Real.sqrt_pos.mpr hK
  have hsM2 : Real.sqrt g.M ^ 2 = g.M := Real.sq_sqrt hM.le
  have hsK2 : Real.sqrt g.K ^ 2 = g.K := Real.sq_sqrt hK.le
  have hω0 : Real.sqrt (g.K / g.M) = Real.sqrt g.K / Real.sqrt g.M := Real.sqrt_div' _ hM.le
  have hMK : Real.sqrt (g.M * g.K) = Real.sqrt g.M * Real.sqrt g.K := Real.sqrt_mul hM.le _
  rw [hω0, hMK]
  set a := Real.sqrt g.M
  set b := Real.sqrt g.K
  have hden : (2 * Complex.I * ((b / a : ℝ) : ℂ) + (g.ωc : ℂ)) *
      ((g.M : ℂ) * (2 * Complex.I * ((b / a : ℝ) : ℂ)) ^ 2 +
        (g.D : ℂ) * (2 * Complex.I * ((b / a : ℝ) : ℂ))) + (g.ωc : ℂ) * (g.K : ℂ) =
      ((g.ωc : ℂ) * (g.K : ℂ)) *
        (((-3 - 8 * (g.D / (2 * (a * b))) * (b / a / g.ωc) : ℝ) : ℂ) +
          ((4 * (g.D / (2 * (a * b))) - 8 * (b / a / g.ωc) : ℝ) : ℂ) * Complex.I) := by
    rw [← hsM2, ← hsK2]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_two, Complex.re_ofNat, Complex.im_ofNat] <;>
      field_simp <;> ring
  have hne : (g.ωc : ℂ) * (g.K : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hω.ne') (by exact_mod_cast hK.ne')
  rw [Texact, hden, div_mul_cancel_left₀ hne, one_div]

/-- `T_red(2jω₀) = 1 / (−3 + 4 j ζ)`, `ζ = D / (2√(MK))`. -/
@[powerlib_foundation] theorem Tred_two_j_omega0 (hM : 0 < g.M) (hK : 0 < g.K) :
    g.Tred (2 * Complex.I * (Real.sqrt (g.K / g.M) : ℂ)) =
      1 / (-3 + 4 * Complex.I * ((g.D / (2 * Real.sqrt (g.M * g.K)) : ℝ) : ℂ)) := by
  have hsM0 : 0 < Real.sqrt g.M := Real.sqrt_pos.mpr hM
  have hsK0 : 0 < Real.sqrt g.K := Real.sqrt_pos.mpr hK
  have hsM2 : Real.sqrt g.M ^ 2 = g.M := Real.sq_sqrt hM.le
  have hsK2 : Real.sqrt g.K ^ 2 = g.K := Real.sq_sqrt hK.le
  have hω0 : Real.sqrt (g.K / g.M) = Real.sqrt g.K / Real.sqrt g.M := Real.sqrt_div' _ hM.le
  have hMK : Real.sqrt (g.M * g.K) = Real.sqrt g.M * Real.sqrt g.K := Real.sqrt_mul hM.le _
  rw [hω0, hMK]
  set a := Real.sqrt g.M
  set b := Real.sqrt g.K
  have hden : (g.M : ℂ) * (2 * Complex.I * ((b / a : ℝ) : ℂ)) ^ 2 +
      (g.D : ℂ) * (2 * Complex.I * ((b / a : ℝ) : ℂ)) + (g.K : ℂ) =
      (g.K : ℂ) * (-3 + 4 * Complex.I * ((g.D / (2 * (a * b)) : ℝ) : ℂ)) := by
    rw [← hsM2, ← hsK2]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_two, Complex.re_ofNat, Complex.im_ofNat,
        Complex.neg_re, Complex.neg_im] <;>
      field_simp <;> ring
  have hne : (g.K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [Tred, hden, div_mul_cancel_left₀ hne, one_div]

/-! ## First-order modulation of the Jacobian by the grid angle -/

/-- The field with grid-angle perturbation `u`: `Ṗ_f = ω_c (K₀ sin(δ − u) − P_f)`. -/
def fieldU (u : ℝ) (x : State 3) : State 3 := g.field (x - mk3 u 0 0)

@[powerlib_foundation] theorem fieldU_apply_two (u : ℝ) (x : State 3) :
    g.fieldU u x 2 = g.ωc * (g.K0 * Real.sin (x 0 - u) - x 2) := by
  simp [fieldU]

/-- The Jacobian of the perturbed field is `J(δ − u)`. -/
@[powerlib_foundation] theorem fderiv_fieldU (u : ℝ) (x : State 3) :
    fderiv ℝ (g.fieldU u) x = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (g.jacobian (x 0 - u)) := by
  have h := (g.hasFDerivAt_field (x - mk3 u 0 0)).comp x
    ((hasFDerivAt_id x).sub_const (mk3 u 0 0))
  have : fieldU g u = g.field ∘ fun y => id y - mk3 u 0 0 := rfl
  rw [this, h.fderiv]
  simp

/-- `A₁ = ∂J/∂u |_{u=0} = ω_c P₀ e_{P_f} e_δᵀ` (entrywise), at the loading equilibrium. -/
def A1 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; g.ωc * g.P0, 0, 0]

@[powerlib_foundation] theorem hasDerivAt_jacobian_u (hK0 : 0 < g.K0) (h : |g.P0| ≤ g.K0)
    (i j : Fin 3) :
    HasDerivAt (fun u => g.jacobian (g.δ0 - u) i j) (g.A1 i j) 0 := by
  have ha : |g.P0 / g.K0| ≤ 1 := by rw [abs_div, abs_of_pos hK0, div_le_one hK0]; exact h
  have hsin : g.K0 * Real.sin g.δ0 = g.P0 := by
    simp only [δ0]; rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]; field_simp
  have h1 : HasDerivAt (fun u : ℝ => g.δ0 - u) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub g.δ0
  have key : HasDerivAt (fun u => g.ωc * (g.K0 * Real.cos (g.δ0 - u))) (g.ωc * g.P0) 0 := by
    have h2 := ((h1.cos).const_mul g.K0).const_mul g.ωc
    convert h2 using 1
    rw [← hsin]; simp
  fin_cases i <;> fin_cases j <;> simp [jacobian, A1] <;>
    first | exact hasDerivAt_const _ _ | exact key

/-- Correction: `A₁ ≠ 0` iff `P₀ ≠ 0` (for `ω_c ≠ 0`). -/
@[powerlib_foundation] theorem A1_ne_zero_iff (hω : g.ωc ≠ 0) : g.A1 ≠ 0 ↔ g.P0 ≠ 0 := by
  constructor
  · intro hA hP
    apply hA
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A1, hP]
  · intro hP hA
    have := congrFun (congrFun hA 2) 0
    simp [A1] at this
    rcases this with h1 | h1
    · exact hω h1
    · exact hP h1

/-! ## Time averages along periodic solutions of the forced model -/

/-- Along a `T`-periodic solution of the forced three-state model with a continuous grid-angle
signal `u`, the averaged filtered power and the averaged electrical power both equal `P₀`:
`∫₀ᵀ P_f = P₀ T` and `∫₀ᵀ K₀ sin(δ − u) = P₀ T`. -/
@[powerlib_foundation] theorem periodic_time_averages (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    {u δ ω Pf : ℝ → ℝ} (hu : Continuous u) {T : ℝ}
    (hδ : ∀ t, HasDerivAt δ (ω t) t)
    (hωd : ∀ t, HasDerivAt ω ((g.P0 - Pf t - g.D * ω t) / g.M) t)
    (hPf : ∀ t, HasDerivAt Pf (g.ωc * (g.K0 * Real.sin (δ t - u t) - Pf t)) t)
    (hpδ : δ T = δ 0) (hpω : ω T = ω 0) (hpP : Pf T = Pf 0) :
    ∫ t in (0 : ℝ)..T, Pf t = g.P0 * T ∧
      ∫ t in (0 : ℝ)..T, g.K0 * Real.sin (δ t - u t) = g.P0 * T := by
  have cδ : Continuous δ := continuous_iff_continuousAt.mpr fun t => (hδ t).continuousAt
  have cω : Continuous ω := continuous_iff_continuousAt.mpr fun t => (hωd t).continuousAt
  have cP : Continuous Pf := continuous_iff_continuousAt.mpr fun t => (hPf t).continuousAt
  have i1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hδ t)
    (cω.intervalIntegrable 0 T)
  have i2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hωd t)
    ((by fun_prop : Continuous fun t => (g.P0 - Pf t - g.D * ω t) / g.M).intervalIntegrable 0 T)
  have i3 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hPf t)
    ((by fun_prop : Continuous fun t =>
      g.ωc * (g.K0 * Real.sin (δ t - u t) - Pf t)).intervalIntegrable 0 T)
  rw [hpδ, sub_self] at i1
  rw [hpω, sub_self] at i2
  rw [hpP, sub_self] at i3
  have iP : IntervalIntegrable Pf MeasureTheory.volume 0 T := cP.intervalIntegrable 0 T
  have iw : IntervalIntegrable (fun t => g.D * ω t) MeasureTheory.volume 0 T :=
    (cω.intervalIntegrable 0 T).const_mul g.D
  have iS : IntervalIntegrable (fun t => g.K0 * Real.sin (δ t - u t)) MeasureTheory.volume 0 T :=
    (by fun_prop : Continuous fun t => g.K0 * Real.sin (δ t - u t)).intervalIntegrable 0 T
  have hA : ∫ t in (0 : ℝ)..T, (g.P0 - Pf t - g.D * ω t) = 0 := by
    rw [intervalIntegral.integral_div, div_eq_zero_iff, or_iff_left hM] at i2
    exact i2
  have hB : ∫ t in (0 : ℝ)..T, (g.P0 - Pf t - g.D * ω t) =
      g.P0 * T - (∫ t in (0 : ℝ)..T, Pf t) - g.D * ∫ t in (0 : ℝ)..T, ω t := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub iP) iw,
      intervalIntegral.integral_sub intervalIntegrable_const iP, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul, sub_zero]
    ring
  have hC : (∫ t in (0 : ℝ)..T, g.K0 * Real.sin (δ t - u t)) - ∫ t in (0 : ℝ)..T, Pf t = 0 := by
    rw [intervalIntegral.integral_const_mul, mul_eq_zero, or_iff_right hω,
      intervalIntegral.integral_sub iS iP] at i3
    exact i3
  rw [i1] at hB
  constructor
  · linarith
  · linarith

end VSMLPF

/-! ## The VSM + power-filter family -/

namespace VSMLPF

/-- A VSM + power-filter model read about a selected angle `δ*`: the operating point is
`(δ*, 0, P₀)`. -/
structure Model where
  /-- The parameters. -/
  g : VSMLPF
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The selected point `(δ*, 0, P₀)`. -/
def Model.point (m : Model) : State 3 := mk3 m.δ 0 m.g.P0

/-- The closed-loop field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 3) : State 3 := m.g.field (z + m.point)

/-- The synchronizing coefficient `K = K₀ cos δ*` at the selected angle. -/
def Model.K (m : Model) : ℝ := m.g.K0 * Real.cos m.δ

/-- Static requirements on VSM + power-filter models. -/
inductive Requirement
  /-- Power balance at the selected angle: `K₀ sin δ* = P₀`. -/
  | balanced
  /-- Positive inertia, damping and filter bandwidth. -/
  | physical
  /-- Positive synchronizing coefficient `K > 0`. -/
  | synchronizing
  /-- The fast-filter Routh condition `K < D ω_c + D²/M` (`ω_c > K/D − D/M`). -/
  | fastFilter
  /-- A destabilizing sign: `D ω_c + D²/M < K` (slow filter) or `K < 0` (saddle). -/
  | destabilizing

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.g.K0 * Real.sin m.δ = m.g.P0
  | .physical => 0 < m.g.M ∧ 0 < m.g.D ∧ 0 < m.g.ωc
  | .synchronizing => 0 < m.K
  | .fastFilter => m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M
  | .destabilizing => m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M < m.K ∨ m.K < 0

/-- The translation of the sentences: the local ones into balance, positivity, synchronization and
the fast-filter condition; instability into balance, positivity and a destabilizing sign;
passivity into nothing; the global sentences, decay rates, sampled contraction and conservation
into the whole language, which no model meets (unavailable translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.balanced, .physical, .synchronizing, .fastFilter}
  | .flow .unstable => {.balanced, .physical, .destabilizing}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The VSM + power-filter family. -/
def family : Family Model Requirement 3 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.g.field m.point :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

private theorem point_eq_zero {m : Model} (hp : Meets m .physical) (hb : Meets m .balanced) :
    m.g.field m.point = 0 :=
  (m.g.field_eq_zero_iff hp.1.ne' hp.2.2.ne' _).mpr
    ⟨by simp [Model.point], by simp [Model.point],
      by have hb' : m.g.K0 * Real.sin m.δ = m.g.P0 := hb; simpa [Model.point] using hb'⟩

private theorem fderiv_point (m : Model) :
    fderiv ℝ m.g.field m.point = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (m.g.jacobian m.δ) := by
  rw [m.g.fderiv_field]
  simp [Model.point]

private theorem les_of {m : Model} (hp : Meets m .physical) (hb : Meets m .balanced)
    (hK : 0 < m.K) (hf : m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    LocallyExponentiallyStable m.g.field m.point := by
  obtain ⟨hM, hD, hwc⟩ := hp
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_three (m.g.jacobian m.δ)
    m.g.contDiff_field (point_eq_zero ⟨hM, hD, hwc⟩ hb) (fderiv_point m) ?_ ?_ ?_
  · rw [trace_jacobian, neg_div]
    have : 0 < m.g.D / m.g.M := div_pos hD hM
    linarith
  · rw [det_jacobian, neg_div]
    exact neg_neg_of_pos (div_pos (mul_pos hwc hK) hM)
  · rw [trace_jacobian, det_jacobian, principalMinorSum_jacobian]
    have key := mul_lt_mul_of_pos_left hf (div_pos hwc hM)
    have e1 : (-m.g.D / m.g.M - m.g.ωc) * (m.g.D * m.g.ωc / m.g.M) =
        -(m.g.ωc / m.g.M * (m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M)) := by ring
    have e2 : -(m.g.ωc * (m.g.K0 * Real.cos m.δ)) / m.g.M = -(m.g.ωc / m.g.M * m.K) := by
      unfold Model.K; ring
    rw [e1, e2]
    linarith

private theorem unstable_of {m : Model} (hp : Meets m .physical) (hb : Meets m .balanced)
    (hs : Meets m .destabilizing) : Unstable m.g.field m.point := by
  obtain ⟨hM, hD, hwc⟩ := hp
  have heq := point_eq_zero ⟨hM, hD, hwc⟩ hb
  rcases hs with hs | hK
  · have hgap : (-(m.g.jacobian m.δ).trace) * Criteria.principalMinorSum (m.g.jacobian m.δ) <
        -(m.g.jacobian m.δ).det := by
      rw [trace_jacobian, det_jacobian, principalMinorSum_jacobian]
      have key := mul_lt_mul_of_pos_left hs (div_pos hwc hM)
      have e1 : -(-m.g.D / m.g.M - m.g.ωc) * (m.g.D * m.g.ωc / m.g.M) =
          m.g.ωc / m.g.M * (m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) := by ring
      have e2 : -(-(m.g.ωc * (m.g.K0 * Real.cos m.δ)) / m.g.M) = m.g.ωc / m.g.M * m.K := by
        unfold Model.K; ring
      rw [e1, e2]
      linarith
    obtain ⟨s, hs, hre⟩ := exists_cubic_root_re_pos_of_gap hgap
    refine Dynamics.unstable_of_characteristic_root_re_pos (m.g.jacobian m.δ) m.g.contDiff_field heq
      (fderiv_point m) (s := s) ?_ hre
    rw [Criteria.det_characteristicMatrix_fin_three']
    exact hs
  · refine Criteria.unstable_of_jacobian_det_pos_fin_three _ m.g.contDiff_field heq
      (fderiv_point m) ?_
    rw [det_jacobian]
    exact div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hwc hK)) hM

/-! ### Soundness of the translation -/

/-- The whole requirement language is inconsistent: a positive synchronizing coefficient below
the fast-filter bound has no destabilizing sign. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : 0 < m.K := h .synchronizing
  have h2 : m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M := h .fastFilter
  rcases (h .destabilizing : Meets m .destabilizing) with h3 | h3 <;> linarith

/-- Every translation of the VSM + power-filter family is sound: the three-state Routh–Hurwitz
conditions of the Jacobian at the selected point prove the local sentences, a destabilizing sign
proves instability (a characteristic root or a real eigenvalue in the open right half plane),
and passivity holds without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · rw [mem_den_flow_iff]
    have hles : LocallyExponentiallyStable m.g.field m.point → P = .locallyExponentiallyStable ∨
        P = .locallyAsymptoticallyStable ∨ P = .lyapunovStable → P.holds m.g.field m.point := by
      rintro h (rfl | rfl | rfl)
      · exact h
      · exact Flow.locallyExponentiallyStable_localAsymptoticStable h
      · exact h.lyapunovStable
    cases P
    case unstable =>
      exact unstable_of (hm .physical (by simp [translate])) (hm .balanced (by simp [translate]))
        (hm .destabilizing (by simp [translate]))
    case lyapunovStable | locallyAsymptoticallyStable | locallyExponentiallyStable =>
      exact hles (les_of (hm .physical (by simp [translate])) (hm .balanced (by simp [translate]))
        (hm .synchronizing (by simp [translate])) (hm .fastFilter (by simp [translate])))
        (by simp)
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- Within positive inertia, damping and filter bandwidth, local exponential stability is
translated exactly: a model with `M, D, ω_c > 0` is locally exponentially stable at
`(δ*, 0, P₀)` exactly when the angle is balanced with `0 < K < D ω_c + D²/M`. Converse
linearization: local exponential stability of the `C¹` field forces an equilibrium whose Jacobian
satisfies the strict 3×3 Routh–Hurwitz conditions. -/
@[powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.physical} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets ({.balanced, .physical, .synchronizing, .fastFilter} ∪ {.physical}) = _
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_inter_iff]
  constructor
  · intro h
    have hp : Meets m .physical := h .physical (by simp)
    exact ⟨mem_den_flow_iff.mpr (les_of hp (h .balanced (by simp)) (h .synchronizing (by simp))
      (h .fastFilter (by simp))), fun q hq => by rw [hq]; exact hp⟩
  · rintro ⟨hd, hI⟩ q hq
    have hp : Meets m .physical := hI .physical rfl
    obtain ⟨hM, hD, hω⟩ := hp
    have hles : LocallyExponentiallyStable m.g.field m.point := mem_den_flow_iff.mp hd
    rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ m.g.contDiff_field
      (fderiv_point m), m.g.field_eq_zero_iff hM.ne' hω.ne', Criteria.isHurwitz_fin_three_iff,
      trace_jacobian, det_jacobian, principalMinorSum_jacobian] at hles
    obtain ⟨⟨-, -, hb⟩, -, hdet, hg⟩ := hles
    have hwM : 0 < m.g.ωc / m.g.M := div_pos hω hM
    have hK : 0 < m.K := by
      have e : -(m.g.ωc * (m.g.K0 * Real.cos m.δ)) / m.g.M = -(m.g.ωc / m.g.M * m.K) := by
        unfold Model.K; ring
      rw [e] at hdet
      exact pos_of_mul_pos_right (by linarith) hwM.le
    have hf : m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M := by
      have e1 : (-m.g.D / m.g.M - m.g.ωc) * (m.g.D * m.g.ωc / m.g.M) =
          -(m.g.ωc / m.g.M * (m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M)) := by ring
      have e2 : -(m.g.ωc * (m.g.K0 * Real.cos m.δ)) / m.g.M = -(m.g.ωc / m.g.M * m.K) := by
        unfold Model.K; ring
      rw [e1, e2] at hg
      exact lt_of_mul_lt_mul_left (by linarith) hwM.le
    rcases hq with ((rfl | rfl | rfl | rfl) | rfl)
    · show m.g.K0 * Real.sin m.δ = m.g.P0
      simpa [Model.point] using hb
    · exact ⟨hM, hD, hω⟩
    · exact hK
    · exact hf
    · exact ⟨hM, hD, hω⟩

/-! ### Members -/

/-- Positive `M, D, ω_c`, a balanced angle, a positive synchronizing coefficient and the
fast-filter Routh condition place a model in local exponential stability. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : 0 < m.K)
    (hf : m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (les_of ⟨hM, hD, hω⟩ hb hK hf)

/-- A slow filter, `D ω_c + D²/M < K`, places a balanced model with positive `M, D, ω_c` in
instability (a characteristic root crosses into the open right half plane). -/
@[powerlib_domain] theorem mem_den_unstable (m : Model) (hM : 0 < m.g.M) (hD : 0 < m.g.D)
    (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0)
    (hs : m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M < m.K) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (unstable_of ⟨hM, hD, hω⟩ hb (Or.inl hs))

/-- A negative synchronizing coefficient places a balanced model with positive `M, D, ω_c` in
instability (a positive real eigenvalue). -/
@[powerlib_domain] theorem mem_den_unstable_of_K_neg (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : m.K < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff.mpr (unstable_of ⟨hM, hD, hω⟩ hb (Or.inr hK))

variable {g : VSMLPF}

/-- The model read about its loading angle `δ₀ = arcsin(P₀/K₀)`. -/
def atLoading (g : VSMLPF) : Model := ⟨g, g.δ0⟩

/-- The model read about the second equilibrium angle `π − δ₀`. -/
def atAntiLoading (g : VSMLPF) : Model := ⟨g, Real.pi - g.δ0⟩

@[simp, powerlib_foundation] theorem atLoading_K (g : VSMLPF) : (atLoading g).K = g.K := rfl

private theorem sin_δ0 (hK0 : 0 < g.K0) (h : |g.P0| ≤ g.K0) :
    g.K0 * Real.sin g.δ0 = g.P0 := by
  have ha : |g.P0 / g.K0| ≤ 1 := by rw [abs_div, abs_of_pos hK0, div_le_one hK0]; exact h
  simp only [δ0]
  rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]
  field_simp

private theorem fast_iff (hp : g.Pos) :
    g.K / g.D - g.D / g.M < g.ωc ↔ g.K < g.D * g.ωc + g.D ^ 2 / g.M := by
  have hM := hp.M; have hD := hp.D
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hD]
  constructor <;> intro h' <;> nlinarith [div_mul_cancel₀ (g.D ^ 2) hM.ne',
    show g.D / g.M * g.D = g.D ^ 2 / g.M by ring]

private theorem slow_iff (hp : g.Pos) :
    g.ωc < g.K / g.D - g.D / g.M ↔ g.D * g.ωc + g.D ^ 2 / g.M < g.K := by
  have hM := hp.M; have hD := hp.D
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hD]
  constructor <;> intro h' <;> nlinarith [div_mul_cancel₀ (g.D ^ 2) hM.ne',
    show g.D / g.M * g.D = g.D ^ 2 / g.M by ring]

/-- `ω_c > K/D − D/M` ⇒ the loading equilibrium is locally exponentially stable. -/
@[powerlib_domain] theorem locallyExponentiallyStable (hp : g.Pos) (h : |g.P0| < g.K0)
    (hω : g.K / g.D - g.D / g.M < g.ωc) :
    connection% (atLoading g ∈ family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_locallyExponentiallyStable _ hp.M hp.D hp.ωc (sin_δ0 hp.K0 h.le) (g.K_pos hp.K0 h)
    ((fast_iff hp).mp hω)

/-- `ω_c < K/D − D/M` ⇒ the loading equilibrium is unstable (a characteristic root crosses
into the open right half-plane). -/
@[powerlib_domain] theorem unstable (hp : g.Pos) (h : |g.P0| < g.K0)
    (hω : g.ωc < g.K / g.D - g.D / g.M) :
    connection% (atLoading g ∈ family.den (.flow .unstable)) :=
  mem_den_unstable _ hp.M hp.D hp.ωc (sin_δ0 hp.K0 h.le) ((slow_iff hp).mp hω)

/-- Exact stability boundary (boundary `K = D ω_c + D²/M` excluded): the loading equilibrium
is locally exponentially stable iff `K < D ω_c + D²/M`.  Since `K = K₀ cos δ₀` decreases with
load, light load is the dangerous side. -/
@[powerlib_domain] theorem locallyExponentiallyStable_iff (hp : g.Pos) (h : |g.P0| < g.K0)
    (hne : g.K ≠ g.D * g.ωc + g.D ^ 2 / g.M) :
    connection% (atLoading g ∈ family.den (.flow .locallyExponentiallyStable) ↔
      atLoading g ∈ {m : Model | m.K < m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M}) := by
  unfold powerlib.TMIO.Statement
  constructor
  · intro hs
    by_contra hn
    have hlt : g.D * g.ωc + g.D ^ 2 / g.M < g.K :=
      lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hne)
    have hu := unstable hp h ((slow_iff hp).mpr hlt)
    unfold powerlib.TMIO.Statement at hu
    rw [mem_den_flow_iff] at hs hu
    exact hu (LocallyExponentiallyStable.lyapunovStable hs)
  · intro hK
    exact locallyExponentiallyStable hp h ((fast_iff hp).mpr hK)

/-- The second equilibrium `(π − δ₀, 0, P₀)` is unstable (a positive real eigenvalue) for every
positive `M, D, ω_c` and `|P₀| < K₀`. -/
@[powerlib_domain] theorem unstable_atAntiLoading (hp : g.Pos) (h : |g.P0| < g.K0) :
    connection% (atAntiLoading g ∈ family.den (.flow .unstable)) := by
  refine mem_den_unstable_of_K_neg _ hp.M hp.D hp.ωc ?_ ?_
  · simp only [atAntiLoading, Real.sin_pi_sub]
    exact sin_δ0 hp.K0 h.le
  · have := g.K_pos hp.K0 h
    simp only [Model.K, atAntiLoading, Real.cos_pi_sub]
    simp only [K] at this
    linarith

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: `M = ω_c = P₀ = 1`, `D = K₀ = 0`, `δ* = 0`. -/
def offEquilibrium : Model := ⟨⟨1, 0, 1, 1, 0⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Dynamics.unstable_of_ne_zero offEquilibrium.g.contDiff_field
    fun h => ?_)
  rw [offEquilibrium.g.field_eq_zero_iff (by norm_num [offEquilibrium])
    (by norm_num [offEquilibrium])] at h
  simp [offEquilibrium, Model.point] at h

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for a balanced angle. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hb : Meets offEquilibrium .balanced := hmem .balanced (by simp [family, translate])
  simp [Meets, offEquilibrium] at hb

/-! ### Boundary witness: negative inertia and damping -/

/-- A model with negative inertia, damping and synchronizing coefficient: `M = D = K₀ = −1`,
`ω_c = 1`, `P₀ = 0`, at `δ* = 0`. -/
def negativeInertia : Model := ⟨⟨-1, -1, 1, 0, -1⟩, 0⟩

/-- The negative-inertia model is locally exponentially stable: its Jacobian has `tr = −2`,
`det = −1` and `tr · Σ₂ = −2 < det` (strict 3×3 Routh–Hurwitz). -/
@[powerlib_domain] theorem negativeInertia_mem_den_locallyExponentiallyStable :
    connection% (negativeInertia ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Criteria.locallyExponentiallyStable_of_jacobian_fin_three _
    negativeInertia.g.contDiff_field ((negativeInertia.g.field_eq_zero_iff
      (by norm_num [negativeInertia]) (by norm_num [negativeInertia]) _).mpr
      (by simp [negativeInertia, Model.point])) (fderiv_point negativeInertia) ?_ ?_ ?_)
  · rw [trace_jacobian]
    norm_num [negativeInertia]
  · rw [det_jacobian]
    norm_num [negativeInertia]
  · rw [trace_jacobian, det_jacobian, principalMinorSum_jacobian]
    norm_num [negativeInertia]

/-- Without positive inertia, damping and bandwidth the local exponential translation is sound
but not exact: the negative-inertia model is locally exponentially stable. -/
@[powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeInertia_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hp : Meets negativeInertia .physical := hmem .physical (by simp [family, translate])
  have := hp.1
  norm_num [negativeInertia] at this

/-! ### The local asymptotic and Lyapunov translations -/

/-- Without positive inertia, damping and bandwidth the local asymptotic translation is sound but
not exact (the negative-inertia model). -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  have hles := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hsound hles
  refine Spectral.not_exact_of_den_subset (s := .flow .locallyExponentiallyStable)
    (s' := .flow .locallyAsymptoticallyStable) rfl
    (Family.chain_le_semantics_iff.mp hsound _) (fun m hm => ?_) hles
  rw [family_isAutonomous.mem_den_flow] at hm ⊢
  exact Flow.locallyExponentiallyStable_localAsymptoticStable hm

/-- Without positive inertia, damping and bandwidth the Lyapunov translation is sound but not
exact (the negative-inertia model). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  have hles := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hsound hles
  refine Spectral.not_exact_of_den_subset (s := .flow .locallyExponentiallyStable)
    (s' := .flow .lyapunovStable) rfl
    (Family.chain_le_semantics_iff.mp hsound _) (fun m hm => ?_) hles
  rw [family_isAutonomous.mem_den_flow] at hm ⊢
  exact hm.lyapunovStable

/-- A flat power curve: `M = D = ω_c = 1`, `P₀ = K₀ = 0`, `δ* = 0`. Every angle is balanced; the
field is `δ̇ = ω`, `ω̇ = −P_f − ω`, `Ṗ_f = −P_f`. -/
def flatCurve : Model := ⟨⟨1, 1, 1, 0, 0⟩, 0⟩

/-- The flat-curve VSM is Lyapunov stable: `(δ + ω − P_f)² + ω² + P_f²` does not increase
(`δ + ω − P_f` is conserved), although its synchronizing coefficient is zero. -/
@[powerlib_domain] theorem flatCurve_mem_den_lyapunovStable :
    connection% (flatCurve ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  refine Dynamics.lyapunovStable_of_inner_nonpos (by norm_num)
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) !![1, 1, -1; 0, 1, 0; 0, 0, 1])
    (fun z w hzw => ?_) fun z => ?_
  · have h0 := congrArg (fun y : State 3 => y 0) hzw
    have h1 := congrArg (fun y : State 3 => y 1) hzw
    have h2 := congrArg (fun y : State 3 => y 2) hzw
    simp only [toEuclideanCLM_apply3] at h0 h1 h2
    simp at h0 h1 h2
    exact state3_ext (by linarith) h1 h2
  · have hf0 : flatCurve.field z 0 = z 1 := by
      simp [Model.field, flatCurve, Model.point, VSMLPF.field]
    have hf1 : flatCurve.field z 1 = -z 2 - z 1 := by
      simp [Model.field, flatCurve, Model.point, VSMLPF.field]
    have hf2 : flatCurve.field z 2 = -z 2 := by
      simp [Model.field, flatCurve, Model.point, VSMLPF.field]
    simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, toEuclideanCLM_apply3,
      hf0, hf1, hf2, RCLike.inner_apply, conj_trivial]
    simp
    nlinarith [sq_nonneg (z 1 + z 2), sq_nonneg (z 1), sq_nonneg (z 2)]

/-- Within positive inertia, damping and bandwidth the Lyapunov translation is not exact: the
flat-curve VSM is physical and Lyapunov stable with a zero synchronizing coefficient. -/
@[powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.physical} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  intro h
  have hmem := flatCurve_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  have hI : flatCurve ∈ TMIO.realize family.meets {.physical} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    show 0 < (1 : ℝ) ∧ 0 < (1 : ℝ) ∧ 0 < (1 : ℝ)
    norm_num
  have h' : flatCurve ∈ TMIO.realize family.meets (family.translate (.flow .lyapunovStable) ∪
      {.physical}) := by
    rw [h]
    exact ⟨hmem, hI⟩
  rw [TMIO.mem_realize] at h'
  have hs : Meets flatCurve .synchronizing := h' .synchronizing (by simp [family, translate])
  simp [Meets, flatCurve, Model.K] at hs

end VSMLPF


/-! ## Second-order swing reduction: the oscillation blind zone `B = 1 − √(1 − ζ₀⁴)` -/

/-- Second-order (quasi-static filter, `ω_c → ∞`) GFM swing model at load `P ∈ [0, K₀)`:
`M δ̈ + D δ̇ = P − K₀ sin δ`, an instance of `Synchronous.SwingParams`. -/
def swingReduced (M D P K0 : ℝ) : Synchronous.SwingParams := ⟨M, D, P, 0, K0, 0⟩

/-- Exact algebra on the second-order swing model: with `ζ₀ = D / (2√(M K₀))` the
linearization at the loading angle `δ_s = arcsin(P/K₀)` has only real eigenvalues (no
oscillatory precursor) iff `P/K₀ ≥ √(1 − ζ₀⁴)`; so the fraction of the load range `[0, K₀)`
without an oscillatory mode is `B = 1 − √(1 − ζ₀⁴)` (for `ζ₀ ≤ 1`). -/
@[powerlib_foundation] theorem swingReduced_eigenvalues_real_iff {M D P K0 : ℝ} (hM : 0 < M)
    (hK0 : 0 < K0) (hP : 0 ≤ P) (hPK : P < K0) :
    (∀ (μ : ℂ) (w : Fin 2 → ℂ), w ≠ 0 →
        ((swingReduced M D P K0).jacobian (swingReduced M D P K0).deltaS).map
          (algebraMap ℝ ℂ) *ᵥ w = μ • w → μ.im = 0) ↔
      Real.sqrt (1 - (D / (2 * Real.sqrt (M * K0))) ^ 4) ≤ P / K0 := by
  rw [Synchronous.SwingParams.eigenvalues_real_iff _ hM]
  set x := P / K0 with hx
  have hx0 : 0 ≤ x := div_nonneg hP hK0.le
  have hx1 : x < 1 := (div_lt_one hK0).mpr hPK
  have hK : (swingReduced M D P K0).syncCoeff (swingReduced M D P K0).deltaS =
      K0 * Real.sqrt (1 - x ^ 2) := by
    simp [Synchronous.SwingParams.syncCoeff, Synchronous.SwingParams.deltaS,
      Synchronous.SwingParams.loadRatio, swingReduced, Real.cos_arcsin, hx]
  rw [hK]
  change 4 * M * (K0 * Real.sqrt (1 - x ^ 2)) ≤ D ^ 2 ↔ _
  have hz : (D / (2 * Real.sqrt (M * K0))) ^ 4 = (D ^ 2 / (4 * M * K0)) ^ 2 := by
    have hs2 := Real.sq_sqrt (show 0 ≤ M * K0 by positivity)
    rw [div_pow, show (2 * Real.sqrt (M * K0)) ^ 4 = 16 * (Real.sqrt (M * K0) ^ 2) ^ 2 by ring,
      hs2, div_pow]
    ring
  rw [hz]
  set z := D ^ 2 / (4 * M * K0) with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hiff1 : 4 * M * (K0 * Real.sqrt (1 - x ^ 2)) ≤ D ^ 2 ↔ Real.sqrt (1 - x ^ 2) ≤ z := by
    rw [hzdef, le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [hiff1]
  have hsx : 0 ≤ 1 - x ^ 2 := by nlinarith
  constructor
  · intro h
    have h2 : 1 - x ^ 2 ≤ z ^ 2 := by
      have := Real.sq_sqrt hsx; nlinarith [Real.sqrt_nonneg (1 - x ^ 2)]
    calc Real.sqrt (1 - z ^ 2) ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = x := Real.sqrt_sq hx0
  · intro h
    rcases le_or_gt (1 - z ^ 2) 0 with hle | hlt
    · have hz1 : 1 ≤ z := by nlinarith
      calc Real.sqrt (1 - x ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
        _ = 1 := Real.sqrt_one
        _ ≤ z := hz1
    · have hs := Real.sq_sqrt hlt.le
      have h2 : 1 - z ^ 2 ≤ x ^ 2 := by nlinarith [Real.sqrt_nonneg (1 - z ^ 2)]
      calc Real.sqrt (1 - x ^ 2) ≤ Real.sqrt (z ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = z := Real.sqrt_sq hz0

/-- The damping ratio of the second-order swing reduction equals one exactly when
`cos δ = ζ₀²` (`ζ(δ) = D / (2√(M K₀ cos δ))`, `cos δ > 0`). -/
@[powerlib_foundation] theorem dampingRatio_eq_one_iff {M D K0 δ : ℝ} (hM : 0 < M)
    (hK0 : 0 < K0) (hD : 0 ≤ D) (hc : 0 < Real.cos δ) :
    D / (2 * Real.sqrt (M * K0 * Real.cos δ)) = 1 ↔
      Real.cos δ = (D / (2 * Real.sqrt (M * K0))) ^ 2 := by
  have hs1 : 0 < Real.sqrt (M * K0 * Real.cos δ) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : 0 < Real.sqrt (M * K0) := Real.sqrt_pos.mpr (by positivity)
  rw [div_eq_one_iff_eq (by positivity), div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  constructor
  · intro h
    have := congrArg (· ^ 2) h
    simp only [mul_pow, Real.sq_sqrt (show 0 ≤ M * K0 * Real.cos δ by positivity)] at this
    field_simp
    nlinarith
  · intro h
    have hsq : D ^ 2 = (2 * Real.sqrt (M * K0 * Real.cos δ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (show 0 ≤ M * K0 * Real.cos δ by positivity), h]
      field_simp
    exact (pow_left_inj₀ hD (by positivity) two_ne_zero).mp hsq

/-! ## Droop + LPF (two states): no oscillatory instability -/

/-- Droop with a first-order power filter: state `(δ, P_f)`,
`δ̇ = (P₀ − P_f)/D` (`D = 1/m_p`), `Ṗ_f = ω_c (K₀ sin δ − P_f)` (the `M → 0` limit). -/
structure DroopLPF where
  D : ℝ
  ωc : ℝ
  P0 : ℝ
  K0 : ℝ

namespace DroopLPF

variable (q : DroopLPF)

def field (x : State 2) : State 2 :=
  Synchronous.mkState ((q.P0 - x 1) / q.D) (q.ωc * (q.K0 * Real.sin (x 0) - x 1))

def jacobian (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1 / q.D; q.ωc * (q.K0 * Real.cos δ), -q.ωc]

def equilibrium : State 2 := Synchronous.mkState (Real.arcsin (q.P0 / q.K0)) q.P0

@[powerlib_foundation] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k q.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [field] <;> fun_prop

@[powerlib_foundation] theorem hasFDerivAt_field (x : State 2) :
    HasFDerivAt q.field (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (q.jacobian (x 0))) x := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  fin_cases i
  · have h := ((hasFDerivAt_const q.P0 x).sub h1).const_mul q.D⁻¹
    convert h using 1
    · funext y; simp [field, div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, PhasePlane.toEuclideanCLM_apply_zero]
      ring
  · have hs := (Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0
    have h := ((hs.const_mul q.K0).sub h1).const_mul q.ωc
    convert h using 1
    · funext y; simp [field]
    · apply ContinuousLinearMap.ext; intro v
      simp [jacobian, PhasePlane.toEuclideanCLM_apply_one]
      ring


/-- Equilibria of droop + LPF: `P_f = P₀` and `K₀ sin δ = P₀`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_iff (hD : q.D ≠ 0) (hω : q.ωc ≠ 0) (x : State 2) :
    q.field x = 0 ↔ x 1 = q.P0 ∧ q.K0 * Real.sin (x 0) = q.P0 := by
  constructor
  · intro h
    have e0 := congrArg (fun y : State 2 => y 0) h
    have e1 := congrArg (fun y : State 2 => y 1) h
    simp only [field, Synchronous.mkState_zero, Synchronous.mkState_one, PiLp.zero_apply] at e0 e1
    rw [div_eq_zero_iff, or_iff_left hD, sub_eq_zero] at e0
    rw [mul_eq_zero, or_iff_right hω, sub_eq_zero] at e1
    exact ⟨e0.symm, e1.trans e0.symm⟩
  · rintro ⟨h1, h2⟩
    apply Synchronous.state_ext <;> simp [field, h1, h2]

/-- A droop + LPF model read about a selected angle `δ*`: the operating point is `(δ*, P₀)`. -/
structure Model where
  /-- The parameters. -/
  q : DroopLPF
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The selected point `(δ*, P₀)`. -/
def Model.point (m : Model) : State 2 := Synchronous.mkState m.δ m.q.P0

/-- The closed-loop field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 2) : State 2 := m.q.field (z + m.point)

/-- Static requirements on droop + LPF models. -/
inductive Requirement
  /-- Power balance at the selected angle: `K₀ sin δ* = P₀`. -/
  | balanced
  /-- Positive droop damping `D = 1/m_p` and filter bandwidth `ω_c`. -/
  | physical
  /-- Positive synchronizing coefficient `K₀ cos δ* > 0`. -/
  | synchronizing
  /-- Negative synchronizing coefficient `K₀ cos δ* < 0` (saddle). -/
  | antiSynchronizing

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .balanced => m.q.K0 * Real.sin m.δ = m.q.P0
  | .physical => 0 < m.q.D ∧ 0 < m.q.ωc
  | .synchronizing => 0 < m.q.K0 * Real.cos m.δ
  | .antiSynchronizing => m.q.K0 * Real.cos m.δ < 0

/-- The translation of the sentences: the local ones into balance, positivity and
synchronization; instability into balance, positivity and a negative synchronizing coefficient;
passivity into nothing; the remaining sentences into the whole, inconsistent, language. -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.balanced, .physical, .synchronizing}
  | .flow .unstable => {.balanced, .physical, .antiSynchronizing}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The droop + LPF family. -/
def family : Family Model Requirement 2 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.q.field m.point :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

private theorem point_eq_zero {m : Model} (hp : Meets m .physical) (hb : Meets m .balanced) :
    m.q.field m.point = 0 :=
  (m.q.field_eq_zero_iff hp.1.ne' hp.2.ne' _).mpr
    ⟨by simp [Model.point],
      by have hb' : m.q.K0 * Real.sin m.δ = m.q.P0 := hb; simpa [Model.point] using hb'⟩

private theorem fderiv_point (m : Model) :
    fderiv ℝ m.q.field m.point = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (m.q.jacobian m.δ) := by
  rw [(m.q.hasFDerivAt_field _).fderiv]
  simp [Model.point]

private theorem trace_jacobian (m : Model) : (m.q.jacobian m.δ).trace = -m.q.ωc := by
  simp [jacobian, Matrix.trace_fin_two]

private theorem det_jacobian (m : Model) :
    (m.q.jacobian m.δ).det = m.q.ωc * (m.q.K0 * Real.cos m.δ) / m.q.D := by
  simp [jacobian, Matrix.det_fin_two]; ring

private theorem les_of {m : Model} (hp : Meets m .physical) (hb : Meets m .balanced)
    (hK : Meets m .synchronizing) : LocallyExponentiallyStable m.q.field m.point :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two _ m.q.contDiff_field
    (point_eq_zero hp hb) (fderiv_point m) (by rw [trace_jacobian]; linarith [hp.2])
    (by rw [det_jacobian]; exact div_pos (mul_pos hp.2 hK) hp.1)

private theorem unstable_of {m : Model} (hp : Meets m .physical) (hb : Meets m .balanced)
    (hK : Meets m .antiSynchronizing) : Unstable m.q.field m.point :=
  Criteria.unstable_of_jacobian_det_neg_fin_two _ m.q.contDiff_field (point_eq_zero hp hb)
    (fderiv_point m) (by
      rw [det_jacobian]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp.2 hK) hp.1)

/-- The whole requirement language is inconsistent: the synchronizing coefficient cannot be
both positive and negative. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have h1 : 0 < m.q.K0 * Real.cos m.δ := h .synchronizing
  have h2 : m.q.K0 * Real.cos m.δ < 0 := h .antiSynchronizing
  linarith

/-- Every translation of the droop + LPF family is sound (`tr J = −ω_c < 0`,
`det J = ω_c K / D`, linearization at the selected point). -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · rw [mem_den_flow_iff]
    cases P
    case unstable =>
      exact unstable_of (hm .physical (by simp [translate])) (hm .balanced (by simp [translate]))
        (hm .antiSynchronizing (by simp [translate]))
    case lyapunovStable =>
      exact (les_of (hm .physical (by simp [translate])) (hm .balanced (by simp [translate]))
        (hm .synchronizing (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (les_of (hm .physical (by simp [translate])) (hm .balanced (by simp [translate]))
          (hm .synchronizing (by simp [translate])))
    case locallyExponentiallyStable =>
      exact les_of (hm .physical (by simp [translate])) (hm .balanced (by simp [translate]))
        (hm .synchronizing (by simp [translate]))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- Within positive droop damping and filter bandwidth, local exponential stability is translated
exactly: a model with `D, ω_c > 0` is locally exponentially stable at `(δ*, P₀)` exactly when the
angle is balanced and synchronizing (`K₀ cos δ* > 0`). Converse linearization: local exponential
stability of the `C¹` field forces an equilibrium with a Hurwitz Jacobian
(`tr = −ω_c`, `det = ω_c K₀ cos δ* / D`). -/
@[powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.physical} (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets ({.balanced, .physical, .synchronizing} ∪ {.physical}) = _
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_inter_iff]
  constructor
  · intro h
    have hp : Meets m .physical := h .physical (by simp)
    exact ⟨mem_den_flow_iff.mpr (les_of hp (h .balanced (by simp)) (h .synchronizing (by simp))),
      fun q hq => by rw [hq]; exact hp⟩
  · rintro ⟨hd, hI⟩ q hq
    have hp : Meets m .physical := hI .physical rfl
    obtain ⟨hD, hω⟩ := hp
    have hles : LocallyExponentiallyStable m.q.field m.point := mem_den_flow_iff.mp hd
    rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ m.q.contDiff_field
      (fderiv_point m), m.q.field_eq_zero_iff hD.ne' hω.ne', Criteria.isHurwitz_fin_two_iff,
      trace_jacobian, det_jacobian] at hles
    obtain ⟨⟨-, hb⟩, -, hdet⟩ := hles
    have hK : 0 < m.q.K0 * Real.cos m.δ := by
      rw [lt_div_iff₀ hD, zero_mul] at hdet
      exact pos_of_mul_pos_right hdet hω.le
    rcases hq with ((rfl | rfl | rfl) | rfl)
    · show m.q.K0 * Real.sin m.δ = m.q.P0
      simpa [Model.point] using hb
    · exact ⟨hD, hω⟩
    · exact hK
    · exact ⟨hD, hω⟩

/-- The model read about its loading angle `arcsin(P₀/K₀)`. -/
def atLoading : Model := ⟨q, Real.arcsin (q.P0 / q.K0)⟩

/-- The model read about the second equilibrium angle `π − arcsin(P₀/K₀)`. -/
def atAntiLoading : Model := ⟨q, Real.pi - Real.arcsin (q.P0 / q.K0)⟩

@[powerlib_foundation] theorem atLoading_point : q.atLoading.point = q.equilibrium := rfl

/-- For every `D, ω_c, K₀ > 0` and `|P₀| < K₀` the loading equilibrium of droop + LPF is
locally exponentially stable (`tr J = −ω_c < 0`, `det J = ω_c K / D > 0`): no Hopf boundary. -/
@[powerlib_domain] theorem locallyExponentiallyStable (hD : 0 < q.D) (hω : 0 < q.ωc)
    (hK0 : 0 < q.K0) (h : |q.P0| < q.K0) :
    connection% (q.atLoading ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have ha : |q.P0 / q.K0| < 1 := by rw [abs_div, abs_of_pos hK0, div_lt_one hK0]; exact h
  have hsin : q.K0 * Real.sin (Real.arcsin (q.P0 / q.K0)) = q.P0 := by
    rw [Real.sin_arcsin (abs_lt.mp ha).1.le (abs_lt.mp ha).2.le]; field_simp
  have hcos : 0 < Real.cos (Real.arcsin (q.P0 / q.K0)) := by
    rw [Real.cos_arcsin]; apply Real.sqrt_pos.mpr
    have : (q.P0 / q.K0) ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (q.P0 / q.K0)]
    linarith
  exact mem_den_flow_iff.mpr (les_of ⟨hD, hω⟩ hsin (mul_pos hK0 hcos))

/-- The second equilibrium `(π − arcsin(P₀/K₀), P₀)` of droop + LPF is a saddle, hence unstable
(`D, ω_c, K₀ > 0`, `|P₀| < K₀`). -/
@[powerlib_domain] theorem unstable_atAntiLoading (hD : 0 < q.D) (hω : 0 < q.ωc)
    (hK0 : 0 < q.K0) (h : |q.P0| < q.K0) :
    connection% (q.atAntiLoading ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have ha : |q.P0 / q.K0| < 1 := by rw [abs_div, abs_of_pos hK0, div_lt_one hK0]; exact h
  have hsin : q.K0 * Real.sin (Real.pi - Real.arcsin (q.P0 / q.K0)) = q.P0 := by
    rw [Real.sin_pi_sub, Real.sin_arcsin (abs_lt.mp ha).1.le (abs_lt.mp ha).2.le]; field_simp
  have hcos : Real.cos (Real.pi - Real.arcsin (q.P0 / q.K0)) < 0 := by
    rw [Real.cos_pi_sub, Real.cos_arcsin, neg_lt_zero]; apply Real.sqrt_pos.mpr
    have : (q.P0 / q.K0) ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (q.P0 / q.K0)]
    linarith
  exact mem_den_flow_iff.mpr (unstable_of ⟨hD, hω⟩ hsin (mul_neg_of_pos_of_neg hK0 hcos))

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: `D = ω_c = P₀ = 1`, `K₀ = 0`, `δ* = 0`. -/
def offEquilibrium : Model := ⟨⟨1, 1, 1, 0⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it. -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Dynamics.unstable_of_ne_zero offEquilibrium.q.contDiff_field
    fun h => ?_)
  rw [offEquilibrium.q.field_eq_zero_iff (by norm_num [offEquilibrium])
    (by norm_num [offEquilibrium])] at h
  simp [offEquilibrium, Model.point] at h

/-- The instability translation is sound but not exact: every non-equilibrium point is unstable,
while the translation asks for a balanced angle. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hb : Meets offEquilibrium .balanced := hmem .balanced (by simp [family, translate])
  simp [Meets, offEquilibrium] at hb

/-! ### Boundary witness: negative damping -/

/-- A droop model with negative damping and synchronizing coefficient: `D = K₀ = −1`,
`ω_c = 1`, `P₀ = 0`, at `δ* = 0`. -/
def negativeDamping : Model := ⟨⟨-1, 1, 0, -1⟩, 0⟩

/-- The negative-damping model is locally exponentially stable: its Jacobian has `tr = −1` and
`det = ω_c K₀ cos δ* / D = 1`. -/
@[powerlib_domain] theorem negativeDamping_mem_den_locallyExponentiallyStable :
    connection% (negativeDamping ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Criteria.locallyExponentiallyStable_of_jacobian_fin_two _
    negativeDamping.q.contDiff_field ((negativeDamping.q.field_eq_zero_iff
      (by norm_num [negativeDamping]) (by norm_num [negativeDamping]) _).mpr
      (by simp [negativeDamping, Model.point])) (fderiv_point negativeDamping) ?_ ?_)
  · rw [trace_jacobian]
    norm_num [negativeDamping]
  · rw [det_jacobian]
    norm_num [negativeDamping]

/-- Without positive damping and bandwidth the local exponential translation is sound but not
exact: the negative-damping model is locally exponentially stable. -/
@[powerlib_domain] theorem not_exact_locallyExponentiallyStable :
    connection% (¬ family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := negativeDamping_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hp : Meets negativeDamping .physical := hmem .physical (by simp [family, translate])
  have := hp.1
  norm_num [negativeDamping] at this

/-! ### The local asymptotic and Lyapunov translations -/

/-- The droop + LPF energy relative to `δ₀`: `(P₀ − P_f)² / (2 D ω_c) + U(δ)` with
`U(δ) = ∫_{δ₀}^{δ} (K₀ sin − P₀) = K₀ (cos δ₀ − cos δ) − P₀ (δ − δ₀)`: the loop is the swing
equation `(D/ω_c) δ̈ + D δ̇ = P₀ − K₀ sin δ`. -/
def energy (δ₀ : ℝ) (x : State 2) : ℝ :=
  (q.P0 - x 1) ^ 2 / (2 * q.D * q.ωc) +
    (q.K0 * (Real.cos δ₀ - Real.cos (x 0)) - q.P0 * (x 0 - δ₀))

@[powerlib_foundation] theorem contDiff_energy (δ₀ : ℝ) : ContDiff ℝ 1 (q.energy δ₀) := by
  unfold energy
  fun_prop

@[powerlib_foundation] theorem hasFDerivAt_energy (δ₀ : ℝ) (x : State 2) :
    HasFDerivAt (q.energy δ₀)
      ((-(q.P0 - x 1) / (q.D * q.ωc)) •
          (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ) +
        (q.K0 * Real.sin (x 0) - q.P0) •
          (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ)) x := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hk := ((h1.const_sub q.P0).pow 2).mul_const (2 * q.D * q.ωc)⁻¹
  have hc := (Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0
  have hU := ((hc.const_sub (Real.cos δ₀)).const_mul q.K0).sub ((h0.sub_const δ₀).const_mul q.P0)
  have h := hk.add hU
  convert h using 1
  · funext y
    simp only [energy, Pi.add_apply, Pi.sub_apply, PiLp.proj_apply, Function.comp_apply]
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp
    ring

/-- Lie derivative of the energy along the field: `Ė = −(P₀ − P_f)² / D` (`D, ω_c ≠ 0`). -/
@[powerlib_foundation] theorem energy_lie (hD : q.D ≠ 0) (hω : q.ωc ≠ 0) (δ₀ : ℝ) (x : State 2) :
    fderiv ℝ (q.energy δ₀) x (q.field x) = -((q.P0 - x 1) ^ 2 / q.D) := by
  rw [(q.hasFDerivAt_energy δ₀ x).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, PiLp.proj_apply, smul_eq_mul, field,
    Synchronous.mkState_zero, Synchronous.mkState_one]
  field_simp
  ring

/-- At a balanced fold angle (`cos δ* = 0`) the energy at `(δ* + s, P₀)` is `−P₀ (s − sin s)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_fold {δ₀ : ℝ} (hb : q.K0 * Real.sin δ₀ = q.P0)
    (hcos : Real.cos δ₀ = 0) (s : ℝ) :
    q.energy δ₀ (Synchronous.mkState (δ₀ + s) q.P0) = -q.P0 * (s - Real.sin s) := by
  simp only [energy, Synchronous.mkState_zero, Synchronous.mkState_one, sub_self]
  rw [Real.cos_add, hcos, ← hb]
  simp
  ring

/-- At a balanced fold angle the restoring power is `P₀ − K₀ sin(δ* + s) = P₀ (1 − cos s)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem restoring_fold {δ₀ : ℝ} (hb : q.K0 * Real.sin δ₀ = q.P0)
    (hcos : Real.cos δ₀ = 0) (s : ℝ) :
    q.P0 - q.K0 * Real.sin (δ₀ + s) = q.P0 * (1 - Real.cos s) := by
  rw [Real.sin_add, hcos, ← hb]
  ring

private theorem norm_state2_le (x : State 2) : ‖x‖ ≤ |x 0| + |x 1| :=
  Synchronous.norm_state_le x

private theorem norm_mkState_sub_point (m : Model) (s t : ℝ) :
    ‖Synchronous.mkState (m.δ + s) (m.q.P0 + t) - m.point‖ ≤ |s| + |t| := by
  refine (norm_state2_le _).trans (le_of_eq ?_)
  simp [Model.point]

private theorem sin_ne_zero_of_cos {δ₀ : ℝ} (hcos : Real.cos δ₀ = 0) : Real.sin δ₀ ≠ 0 := by
  intro h
  have := Real.sin_sq_add_cos_sq δ₀
  rw [h, hcos] at this
  norm_num at this

/-- At a fold the energy takes values below its value at the operating point arbitrarily close
to it. -/
private theorem fold_seeds {m : Model} (hb : m.q.K0 * Real.sin m.δ = m.q.P0)
    (hcos : Real.cos m.δ = 0) (hK : m.q.K0 ≠ 0) :
    ∀ ε > 0, ∃ x, ‖x - m.point‖ < ε ∧ m.q.energy m.δ x < m.q.energy m.δ m.point := by
  intro ε hε
  have hE0 : m.q.energy m.δ m.point = 0 := by simp [energy, Model.point]
  rw [hE0]
  have hP : m.q.P0 ≠ 0 := by rw [← hb]; exact mul_ne_zero hK (sin_ne_zero_of_cos hcos)
  have hε2 : 0 < ε / 2 := by linarith
  have hsin := Real.sin_lt hε2
  rcases lt_or_gt_of_ne hP with hneg | hpos
  · refine ⟨Synchronous.mkState (m.δ + -(ε / 2)) (m.q.P0 + 0), ?_, ?_⟩
    · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
      rw [abs_zero, add_zero, abs_neg, abs_of_pos hε2]
      linarith
    · rw [add_zero, m.q.energy_fold hb hcos, Real.sin_neg]
      nlinarith
  · refine ⟨Synchronous.mkState (m.δ + ε / 2) (m.q.P0 + 0), ?_, ?_⟩
    · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
      rw [abs_zero, add_zero, abs_of_pos hε2]
      linarith
    · rw [add_zero, m.q.energy_fold hb hcos]
      nlinarith

/-- With `D, ω_c > 0`, an equilibrium at the selected point is balanced. -/
private theorem balanced_of_eq {m : Model} (hp : Meets m .physical)
    (heq : m.q.field m.point = 0) : m.q.K0 * Real.sin m.δ = m.q.P0 := by
  simpa [Model.point] using ((m.q.field_eq_zero_iff hp.1.ne' hp.2.ne' _).mp heq).2

/-- A vanishing power curve (`K₀ = 0`) at a balanced angle (`P₀ = 0`): every `(δ, 0)` is an
equilibrium. -/
private theorem field_flat {m : Model} (hK : m.q.K0 = 0) (hP : m.q.P0 = 0) (δ : ℝ) :
    m.q.field (Synchronous.mkState δ m.q.P0) = 0 := by
  apply Synchronous.state_ext <;> simp [field, hK, hP]

/-- Within positive droop damping and bandwidth, local asymptotic stability of `(δ*, P₀)` forces
balance and synchronization. A negative synchronizing coefficient is a saddle; a vanishing power
curve has a continuum of equilibria; and at a fold the dissipated energy is below its value at
the operating point on one side. -/
private theorem las_requirements {m : Model} (hp : Meets m .physical)
    (hlas : LocalAsymptoticStable m.q.field m.point) :
    Meets m .balanced ∧ Meets m .synchronizing := by
  have hC : ContDiff ℝ 1 m.q.field := m.q.contDiff_field
  have hb := balanced_of_eq hp (Dynamics.isEquilibrium_of_lyapunovStable hC hlas.1)
  refine ⟨hb, ?_⟩
  show 0 < m.q.K0 * Real.cos m.δ
  rcases lt_trichotomy (m.q.K0 * Real.cos m.δ) 0 with hK | hK | hK
  · exact absurd hlas.1 (unstable_of hp hb hK)
  · exfalso
    rcases mul_eq_zero.mp hK with hK0 | hc
    · have hP : m.q.P0 = 0 := by rw [← hb, hK0, zero_mul]
      refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
        ⟨Synchronous.mkState (m.δ + ε / 2) (m.q.P0 + 0), fun h => ?_, ?_, ?_⟩) hlas
      · have := congrArg (fun y : State 2 => y 0) h
        simp [Model.point] at this
        linarith
      · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
        rw [abs_zero, add_zero, abs_of_pos (by linarith)]
        linarith
      · rw [add_zero]
        exact field_flat hK0 hP _
    · by_cases hK0 : m.q.K0 = 0
      · have hP : m.q.P0 = 0 := by rw [← hb, hK0, zero_mul]
        refine Dynamics.not_localAsymptoticStable_of_equilibria (fun ε hε =>
          ⟨Synchronous.mkState (m.δ + ε / 2) (m.q.P0 + 0), fun h => ?_, ?_, ?_⟩) hlas
        · have := congrArg (fun y : State 2 => y 0) h
          simp [Model.point] at this
          linarith
        · refine (norm_mkState_sub_point m _ 0).trans_lt ?_
          rw [abs_zero, add_zero, abs_of_pos (by linarith)]
          linarith
        · rw [add_zero]
          exact field_flat hK0 hP _
      refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := m.q.energy m.δ) (ρ := 1) hC
        ((m.q.contDiff_energy _).differentiable one_ne_zero) one_pos (fun x _ => ?_)
        (fold_seeds hb hc hK0) hlas
      rw [m.q.energy_lie hp.1.ne' hp.2.ne']
      have : 0 ≤ (m.q.P0 - x 1) ^ 2 / m.q.D := div_nonneg (sq_nonneg _) hp.1.le
      linarith
  · exact hK

/-- Within positive droop damping and bandwidth the local asymptotic translation is exact: a
model with `D, ω_c > 0` is locally asymptotically stable at `(δ*, P₀)` exactly when the angle is
balanced and synchronizing (`K₀ cos δ* > 0`). The linearization does not decide `K₀ cos δ* = 0`,
the model's structure does: a vanishing power curve has a continuum of equilibria, and at a fold
the energy `(P₀ − P_f)²/(2 D ω_c) + U(δ)`, dissipated at the rate `(P₀ − P_f)²/D`, is
`−P₀ (s − sin s)` at `(δ* + s, P₀)` (`energy_fold`), below its value at the operating point on
one side (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`). -/
@[powerlib_domain] theorem exactUnder_locallyAsymptoticallyStable :
    connection% (family.ExactUnder {.physical} (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement Family.ExactUnder TMIO.ExactUnder
  change TMIO.realize Meets ({.balanced, .physical, .synchronizing} ∪ {.physical}) = _
  ext m
  simp only [TMIO.mem_realize, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_inter_iff]
  constructor
  · intro h
    have hp : Meets m .physical := h .physical (by simp)
    exact ⟨mem_den_flow_iff.mpr (Flow.locallyExponentiallyStable_localAsymptoticStable
      (les_of hp (h .balanced (by simp)) (h .synchronizing (by simp)))),
      fun q hq => by rw [hq]; exact hp⟩
  · rintro ⟨hd, hI⟩ r hr
    have hp : Meets m .physical := hI .physical rfl
    obtain ⟨hb, hK⟩ := las_requirements hp (mem_den_flow_iff.mp hd)
    rcases hr with ((rfl | rfl | rfl) | rfl)
    · exact hb
    · exact hp
    · exact hK
    · exact hp

/-- Within positive droop damping and bandwidth, Lyapunov stability of `(δ*, P₀)` holds exactly
at a balanced angle that is synchronizing (`K₀ cos δ* > 0`) or has a vanishing power curve
(`K₀ = 0`, where `δ − P_f/(D ω_c)` is conserved and `P_f` decays). A negative synchronizing
coefficient is a saddle, and a fold is unstable: below the level of the operating point the
dissipated energy keeps the solution, and there `P₀ ((P₀ − P_f)/ω_c + D δ)` grows at the rate
`P₀² (1 − cos(δ − δ*))` (`Dynamics.unstable_of_lie_nonpos_of_lie_pos`). -/
@[powerlib_domain] theorem mem_den_lyapunovStable_iff_of_physical (m : Model) (hD : 0 < m.q.D)
    (hω : 0 < m.q.ωc) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.q.K0 * Real.sin m.δ = m.q.P0 ∧
        (0 < m.q.K0 * Real.cos m.δ ∨ m.q.K0 = 0)}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  have hp : Meets m .physical := ⟨hD, hω⟩
  have hC : ContDiff ℝ 1 m.q.field := m.q.contDiff_field
  constructor
  · intro hm
    have hls : LyapunovStable m.q.field m.point := mem_den_flow_iff.mp hm
    have hb := balanced_of_eq hp (Dynamics.isEquilibrium_of_lyapunovStable hC hls)
    refine ⟨hb, ?_⟩
    by_cases hK0 : m.q.K0 = 0
    · exact Or.inr hK0
    rcases lt_trichotomy (m.q.K0 * Real.cos m.δ) 0 with hK | hK | hK
    · exact absurd hls (unstable_of hp hb hK)
    · exfalso
      have hc : Real.cos m.δ = 0 := (mul_eq_zero.mp hK).resolve_left hK0
      set a := m.q.P0 with ha
      have h0 := fun x : State 2 =>
        (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
      have h1 := fun x : State 2 =>
        (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
      have hW : ContDiff ℝ 1 fun x : State 2 => a * ((a - x 1) / m.q.ωc + m.q.D * x 0) := by
        fun_prop
      refine Dynamics.unstable_of_lie_nonpos_of_lie_pos (E := m.q.energy m.δ)
        (W := fun x : State 2 => a * ((a - x 1) / m.q.ωc + m.q.D * x 0)) (r := 1) hC
        (m.q.contDiff_energy _) hW one_pos (fun x _ => ?_) (fold_seeds hb hc hK0)
        (fun x hx hEx => ?_) hls
      · rw [m.q.energy_lie hD.ne' hω.ne']
        have : 0 ≤ (m.q.P0 - x 1) ^ 2 / m.q.D := div_nonneg (sq_nonneg _) hD.le
        linarith
      · have hd : HasFDerivAt (fun y : State 2 => a * ((a - y 1) / m.q.ωc + m.q.D * y 0))
            (a • ((-1 / m.q.ωc) • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
                State 2 →L[ℝ] ℝ) +
              m.q.D • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) : State 2 →L[ℝ] ℝ))) x := by
          have h := ((((h1 x).const_sub a).mul_const m.q.ωc⁻¹).add
            ((h0 x).const_mul m.q.D)).const_mul a
          convert h using 1
          · funext y
            simp only [Pi.add_apply, PiLp.proj_apply]
            ring
          · apply ContinuousLinearMap.ext
            intro v
            simp
            ring
        rw [hd.fderiv]
        simp only [_root_.smul_apply, _root_.add_apply, PiLp.proj_apply, smul_eq_mul, field,
          Synchronous.mkState_zero, Synchronous.mkState_one]
        set s₀ := x 0 - m.δ with hs₀
        have hx0 : x 0 = m.δ + s₀ := by rw [hs₀]; ring
        have hrate : -1 / m.q.ωc * (m.q.ωc * (m.q.K0 * Real.sin (x 0) - x 1)) +
            m.q.D * ((m.q.P0 - x 1) / m.q.D) = a * (1 - Real.cos s₀) := by
          rw [hx0, ← m.q.restoring_fold hb hc]
          field_simp
          ring
        rw [hrate]
        have hs1 : |s₀| ≤ 1 := by
          have := Synchronous.abs_coord_le (x - m.point) 0
          simp only [PiLp.sub_apply, Model.point, Synchronous.mkState_zero] at this
          rw [← hs₀] at this
          exact this.trans hx
        have hs0 : s₀ ≠ 0 := by
          intro h
          have hE0 : m.q.energy m.δ m.point = 0 := by simp [energy, Model.point]
          rw [hE0] at hEx
          have hx' : x 0 = m.δ := by rw [hx0, h, add_zero]
          simp only [energy, hx', sub_self, mul_zero] at hEx
          have : 0 ≤ (m.q.P0 - x 1) ^ 2 / (2 * m.q.D * m.q.ωc) :=
            div_nonneg (sq_nonneg _) (by positivity)
          linarith
        have hcos1 : Real.cos s₀ < 1 := by
          refine lt_of_le_of_ne (Real.cos_le_one _) fun h => hs0 ?_
          refine (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp h
          · linarith [neg_abs_le s₀, Real.two_le_pi]
          · linarith [le_abs_self s₀, Real.two_le_pi]
        have ha0 : a ≠ 0 := fun h0 => mul_ne_zero hK0 (sin_ne_zero_of_cos hc) (hb.trans h0)
        have : 0 < a * a := mul_self_pos.mpr ha0
        nlinarith
    · exact Or.inl hK
  · rintro ⟨hb, (hK | hK0)⟩
    · exact mem_den_flow_iff.mpr (les_of hp hb hK).lyapunovStable
    · -- a vanishing power curve: `(δ − P_f/(D ω_c))² + P_f²` does not increase
      have hP : m.q.P0 = 0 := by rw [← hb, hK0, zero_mul]
      rw [family_isAutonomous.mem_den_flow]
      have hDw : m.q.D * m.q.ωc ≠ 0 := mul_ne_zero hD.ne' hω.ne'
      refine Dynamics.lyapunovStable_of_inner_nonpos two_pos
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![1, -1 / (m.q.D * m.q.ωc); 0, 1])
        (fun z w hzw => ?_) fun z => ?_
      · have hz0 := congrArg (fun y : State 2 => y 0) hzw
        have hz1 := congrArg (fun y : State 2 => y 1) hzw
        simp only [PhasePlane.toEuclideanCLM_apply_zero, PhasePlane.toEuclideanCLM_apply_one]
          at hz0 hz1
        simp at hz0 hz1
        refine Synchronous.state_ext ?_ hz1
        rw [hz1] at hz0
        linarith
      · have hf0 : m.field z 0 = -(z 1 / m.q.D) := by
          simp [Model.field, Model.point, field, hP]
          ring
        have hf1 : m.field z 1 = -(m.q.ωc * z 1) := by
          simp [Model.field, Model.point, field, hP, hK0]
        simp only [PiLp.inner_apply, Fin.sum_univ_two, PhasePlane.toEuclideanCLM_apply_zero,
          PhasePlane.toEuclideanCLM_apply_one, hf0, hf1, RCLike.inner_apply, conj_trivial]
        have hcancel : -(z 1 / m.q.D) + -1 / (m.q.D * m.q.ωc) * -(m.q.ωc * z 1) = 0 := by
          field_simp
          ring
        simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Matrix.of_apply, one_mul, zero_mul, zero_add]
        simp only [hcancel]
        nlinarith [sq_nonneg (z 1), hω]

/-- Without positive damping and bandwidth the local asymptotic translation is sound but not
exact (the negative-damping model). -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  have hles := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hsound hles
  refine Spectral.not_exact_of_den_subset (s := .flow .locallyExponentiallyStable)
    (s' := .flow .locallyAsymptoticallyStable) rfl
    (Family.chain_le_semantics_iff.mp hsound _) (fun m hm => ?_) hles
  rw [family_isAutonomous.mem_den_flow] at hm ⊢
  exact Flow.locallyExponentiallyStable_localAsymptoticStable hm

/-- Without positive damping and bandwidth the Lyapunov translation is sound but not exact (the
negative-damping model). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have hsound := chain_le_semantics
  have hles := not_exact_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hsound hles
  refine Spectral.not_exact_of_den_subset (s := .flow .locallyExponentiallyStable)
    (s' := .flow .lyapunovStable) rfl
    (Family.chain_le_semantics_iff.mp hsound _) (fun m hm => ?_) hles
  rw [family_isAutonomous.mem_den_flow] at hm ⊢
  exact hm.lyapunovStable

/-- A vanishing power curve: `D = ω_c = 1`, `P₀ = K₀ = 0`, `δ* = 0`. -/
def flatCurve : Model := ⟨⟨1, 1, 0, 0⟩, 0⟩

/-- Within positive damping and bandwidth the Lyapunov translation is not exact: the flat-curve
droop loop is Lyapunov stable with a zero synchronizing coefficient. -/
@[powerlib_domain] theorem not_exactUnder_lyapunovStable :
    connection% (¬ family.ExactUnder {.physical} (.flow .lyapunovStable)) := by
  have hmem := mem_den_lyapunovStable_iff_of_physical flatCurve one_pos one_pos
  unfold powerlib.TMIO.Statement at hmem ⊢
  unfold Family.ExactUnder TMIO.ExactUnder
  intro h
  have hls : flatCurve ∈ family.den (.flow .lyapunovStable) :=
    hmem.mpr ⟨by simp [flatCurve], Or.inr rfl⟩
  have hI : flatCurve ∈ TMIO.realize family.meets {.physical} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    show 0 < (1 : ℝ) ∧ 0 < (1 : ℝ)
    norm_num
  have h' : flatCurve ∈ TMIO.realize family.meets (family.translate (.flow .lyapunovStable) ∪
      {.physical}) := by
    rw [h]
    exact ⟨hls, hI⟩
  rw [TMIO.mem_realize] at h'
  have hs : Meets flatCurve .synchronizing := h' .synchronizing (by simp [family, translate])
  simp [Meets, flatCurve] at hs

end DroopLPF

end powerlib.GFM
