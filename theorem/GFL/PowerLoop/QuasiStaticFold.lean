import theorem.GFL.PowerLoop.QuasiStatic
import theorem.Dynamics.Calculus
import theorem.Dynamics.Instability
import theorem.Spectral.Equilibrium

/-! # Quasi-static three-state GFL: the fold of the Routh–Hurwitz region

Port current IN-positive (work-sync conventions §D1); active power absorbed-positive (§D3).
Scaffold: `theorem/CurrentDirection.agda`.

Model boundary.
The model of `theorem/GFL/PowerLoop/QuasiStatic.lean`, unchanged: a single
grid-following converter on an infinite bus of amplitude `V` behind a lossless reactance `X_g`;
three-phase balanced averaged dq model in the PLL frame, algebraic (quasi-static) network,
continuous time. States, in order: `θ` (PLL error angle), `x` (PLL integrator), `i_d` (d-axis
current into the converter); `I_q = 0`; absorbed power `P = (3/2) Re(V̄ Ī*) = (3/2) V cos θ i_d`
and absorbed reference `P_ref`. SRF-PLL `θ̇ = k_p v_q + k_i x`, `ẋ = v_q`,
`v_q = −V sin θ − X_g i_d`; pure-integral dispatch `i̇_d = k_P (P_ref − P)`. Ideal current loop;
no line dynamics, resistance, dc link, PWM, delay or limiter. All statements are local, about the
full nonlinear field translated to the selected point `(θ*, 0, i_d*)`
(`QuasiStatic.Model.field`).

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (差别二 `P_SN = 3V²/(4X_g)`, 折叠角 45°; 推论二 准静态无
Hopf); model `GFLQuasiStatic` in `.../archive/simulation/src/gfl_gfm_contrast_sim/models.py`.

Results.
The fold (static). At a balanced point write `A = V cos θ*`, `B = V sin θ* = −X_g i_d*`,
`κ = (3/2) k_P`, `ι' = −X_g (i_d − i_d*)` (the source's `X_g (I_d − I_d*)` with `I_d = −i_d`;
the generic parameter `Xg` of the fold function is `−X_g`). On the fold `cos 2θ* = 0`
(`B² = A²`, the transmission limit `P_ref = ±P_SN`) the Jacobian
`[[−k_pA, k_i, k_p], [−A, 0, 1], [κA², 0, −κA]]` (coordinates `(φ, x, ι')`) has the left null
vector `(0, κA, 1)`: `u = κA x + ι'` has
`u̇ = κ[(1 − cos φ)(2AB + Aι') + Bι' sin φ]`, whose quadratic part `κBφ(Aφ + ι')` does not vanish
on the right null vector `(1, 0, A)` — a saddle-node. The fold function
`foldU = −(B/A) u + S(φ, x, ι')` with the explicit quadratic form `S` (SymPy solution of the
singular Lyapunov equation, `fold_quad_identity`:
`2(Sz)·(Jz) − κAφ(Aφ + ι') = −(κA²φ² + 2k_i(k_p + κ)x² + κι'²)`) has
`U̇ = −(κA²φ² + 2k_i(k_p + κ)x² + κι'²) + O(s³)`, negative on a punctured neighbourhood for
`k_p, k_i, k_P > 0`, while `U = −t B² − t² B² < 0` along `(φ, x, ι') = t(B, 0, AB)`.
`hasFDerivAt_foldU`, `contDiff_foldU` give its derivative.

Family and connection conclusions.
* `mem_den_unstable_of_fold`: positive gains, balanced point, `V cos θ* > 0`, `cos 2θ* = 0` ⇒
  unstable (`Dynamics.unstable_of_eventually_lie_neg`); `mem_den_unstable_of_pi_div_four` at
  `θ* = π/4`, `V > 0`. Together with `mem_den_unstable_of_cos_two_mul_neg` the whole closed fold
  side `cos 2θ* ≤ 0` of the branch is unstable.
* `exactUnder_locallyAsymptoticallyStable`, `exactUnder_lyapunovStable`: within the requirement
  context `positiveGains` (`k_p, k_i, k_P > 0`) the local asymptotic and Lyapunov translations
  (`{equilibrium, jacobianStable}`) are exact: with positive gains every selected point that is not
  an equilibrium with a strict Routh–Hurwitz Jacobian is unstable — non-equilibria; `V = 0` (the
  integrator or current drifts linearly, Chetaev with `θx` or `X_g x ι`); `V cos θ* < 0`
  (`tr J > 0`); `cos θ* = 0` or `cos 2θ* < 0` (`det J > 0`); and the fold. On `V cos θ* > 0`,
  `cos 2θ* > 0` the strict Routh–Hurwitz conditions hold (`a₂a₁ − a₀ > 0` from `a2_mul_a1_sub_a0`).
  Outside positive gains the local asymptotic translation is not exact
  (`QuasiStatic.not_exact_locallyAsymptoticallyStable`,
  `theorem/GFL/PowerLoop/QuasiStaticFoldHopf.lean`).

Correction: the source attributes a Bogdanov–Takens (double-zero, "BT 型退化") degeneracy to the
quasi-static boundary, following its form-B reference; in this three-state model with positive
gains the fold has a simple zero eigenvalue (`a₀ = 0`, `a₁ = V k_i cos θ* > 0`, `a₂ > 0`): it is a
saddle-node, and it is unstable.
-/

noncomputable section
namespace powerlib.GFL.PowerLoop.QuasiStatic
open Filter Topology Asymptotics

/-! ## The fold function (static) -/

/-- The fold function in coordinates `(φ, x, ι)` with a parameter `Xg` (the model reads it with
`(φ, x, ι) = (θ − θ*, x, i_d − i_d*)` and `Xg = −X_g`, `model_fold_form`):
`U = −(B/A)(κA x + Xg ι) + S(φ, x, Xg ι)` with the quadratic form
`S(φ, x, ι') = φ² − 2(k_p + κ) φx − (2/A) φι' + (k_i/A + k_p² + 2k_pκ − Aκ²/2) x²
  + (2k_p/A − κ) xι'`. -/
def foldU (A B Xg kp ki κ φ x ι : ℝ) : ℝ :=
  -(B / A) * (κ * A * x + Xg * ι) +
    (φ ^ 2 + 2 * (-(kp + κ)) * (φ * x) + 2 * (-1 / A) * (φ * (Xg * ι)) +
      (-A * κ ^ 2 / 2 + kp ^ 2 + 2 * kp * κ + ki / A) * x ^ 2 +
      2 * (-κ / 2 + kp / A) * (x * (Xg * ι)))

/-- `(S z)₀` -/
def foldS0 (A Xg kp κ φ x ι : ℝ) : ℝ := φ + -(kp + κ) * x + -1 / A * (Xg * ι)
/-- `(S z)₁` -/
def foldS1 (A Xg kp ki κ φ x ι : ℝ) : ℝ :=
  -(kp + κ) * φ + (-A * κ ^ 2 / 2 + kp ^ 2 + 2 * kp * κ + ki / A) * x +
    (-κ / 2 + kp / A) * (Xg * ι)
/-- `(S z)₂` -/
def foldS2 (A kp κ φ x : ℝ) : ℝ := -1 / A * φ + (-κ / 2 + kp / A) * x

/-- The quadratic Lyapunov identity at the fold: with
`J = [[−k_pA, k_i, k_p], [−A, 0, 1], [κA², 0, −κA]]` (coordinates `(φ, x, ι')`),
`2 (Sz)·(Jz) − κAφ(Aφ + ι') = −(κA²φ² + 2k_i(k_p + κ)x² + κι'²)`. -/
@[tmio M, powerlib_foundation] theorem fold_quad_identity {A : ℝ} (hA : A ≠ 0) (Xg kp ki κ φ x ι : ℝ) :
    2 * (foldS0 A Xg kp κ φ x ι * (-kp * A * φ + ki * x + kp * (Xg * ι)) +
        foldS1 A Xg kp ki κ φ x ι * (-A * φ + Xg * ι) +
        foldS2 A kp κ φ x * (κ * A ^ 2 * φ - κ * A * (Xg * ι))) -
      κ * A * φ * (A * φ + Xg * ι) =
    -(κ * A ^ 2 * φ ^ 2 + 2 * ki * (kp + κ) * x ^ 2 + κ * (Xg * ι) ^ 2) := by
  unfold foldS0 foldS1 foldS2
  field_simp
  ring

/-- Derivative of the fold function. -/
@[powerlib_foundation] theorem hasFDerivAt_foldU (A B Xg kp ki κ : ℝ) (z : Dynamics.State 3) :
    HasFDerivAt (fun z : Dynamics.State 3 => foldU A B Xg kp ki κ (z 0) (z 1) (z 2))
      ((2 * foldS0 A Xg kp κ (z 0) (z 1) (z 2)) •
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 : Dynamics.State 3 →L[ℝ] ℝ) +
        (-(B / A) * (κ * A) + 2 * foldS1 A Xg kp ki κ (z 0) (z 1) (z 2)) •
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1 : Dynamics.State 3 →L[ℝ] ℝ) +
        (-(B / A) * Xg + 2 * Xg * foldS2 A kp κ (z 0) (z 1)) •
          (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Dynamics.State 3 →L[ℝ] ℝ)) z := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) :
    Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) :
    Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) :
    Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have hι := h2.const_mul Xg
  have h := ((((h1.const_mul (κ * A)).add hι).const_mul (-(B / A))).add
    ((((((h0.pow 2).add ((h0.mul h1).const_mul (2 * (-(kp + κ))))).add
      ((h0.mul hι).const_mul (2 * (-1 / A)))).add
      ((h1.pow 2).const_mul (-A * κ ^ 2 / 2 + kp ^ 2 + 2 * kp * κ + ki / A))).add
      ((h1.mul hι).const_mul (2 * (-κ / 2 + kp / A))))))
  unfold foldU
  refine h.congr_fderiv ?_
  ext v
  simp [foldS0, foldS1, foldS2]
  ring

@[powerlib_foundation] theorem contDiff_foldU (A B Xg kp ki κ : ℝ) :
    ContDiff ℝ 1 (fun z : Dynamics.State 3 => foldU A B Xg kp ki κ (z 0) (z 1) (z 2)) := by
  unfold foldU
  fun_prop

/-! ## Local analysis at the fold (implementation evidence) -/

section FoldLocal

/-- The size function `s = |z₀| + |z₁| + |z₂|`. -/
private theorem size3_tendsto :
    Tendsto (fun z : Dynamics.State 3 => |z 0| + |z 1| + |z 2|) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun z : Dynamics.State 3 => |z 0| + |z 1| + |z 2|) := by fun_prop
  simpa using hc.tendsto 0

private theorem coord3_isBigO (i : Fin 3) :
    (fun z : Dynamics.State 3 => z i) =O[𝓝 0] fun z => (|z 0| + |z 1| + |z 2|) ^ 1 :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, pow_one]
    have h0 := abs_nonneg (z 0)
    have h1 := abs_nonneg (z 1)
    have h2 := abs_nonneg (z 2)
    refine le_trans ?_ (le_abs_self _)
    fin_cases i <;> simp <;> linarith)

private theorem mul3_isBigO {f g : Dynamics.State 3 → ℝ} {a b k : ℕ}
    (hf : f =O[𝓝 0] fun z => (|z 0| + |z 1| + |z 2|) ^ a)
    (hg : g =O[𝓝 0] fun z => (|z 0| + |z 1| + |z 2|) ^ b) (hk : k ≤ a + b) :
    (fun z => f z * g z) =O[𝓝 0] fun z => (|z 0| + |z 1| + |z 2|) ^ k :=
  ((hf.mul hg).congr_right fun _ => (pow_add _ _ _).symm).trans
    (Dynamics.isBigO_pow_of_tendsto size3_tendsto hk)

private theorem mono3_isBigO {f : Dynamics.State 3 → ℝ} {a k : ℕ}
    (hf : f =O[𝓝 0] fun z => (|z 0| + |z 1| + |z 2|) ^ a) (hk : k ≤ a) :
    f =O[𝓝 0] fun z => (|z 0| + |z 1| + |z 2|) ^ k :=
  hf.trans (Dynamics.isBigO_pow_of_tendsto size3_tendsto hk)

private theorem trig3_isBigO :
    ((fun z : Dynamics.State 3 => 1 - Real.cos (z 0)) =O[𝓝 0]
        fun z => (|z 0| + |z 1| + |z 2|) ^ 2) ∧
    ((fun z : Dynamics.State 3 => Real.sin (z 0) - z 0) =O[𝓝 0]
        fun z => (|z 0| + |z 1| + |z 2|) ^ 3) ∧
    ((fun z : Dynamics.State 3 => 1 - Real.cos (z 0) - z 0 ^ 2 / 2) =O[𝓝 0]
        fun z => (|z 0| + |z 1| + |z 2|) ^ 4) ∧
    ((fun z : Dynamics.State 3 => Real.sin (z 0)) =O[𝓝 0]
        fun z => (|z 0| + |z 1| + |z 2|) ^ 1) := by
  have ht : Tendsto (fun z : Dynamics.State 3 => z 0) (𝓝 0) (𝓝 0) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) :
      Dynamics.State 3 →L[ℝ] ℝ).continuous.tendsto' 0 0 (by simp)
  have h0 := coord3_isBigO 0
  have h0' : (fun z : Dynamics.State 3 => z 0) =O[𝓝 0] fun z => |z 0| + |z 1| + |z 2| :=
    h0.congr_right fun z => pow_one _
  refine ⟨(Dynamics.one_sub_cos_isBigO.comp_tendsto ht).trans (h0'.pow 2),
    (Dynamics.sin_sub_self_isBigO.comp_tendsto ht).trans (h0'.pow 3),
    (Dynamics.one_sub_cos_sub_isBigO.comp_tendsto ht).trans (h0'.pow 4), ?_⟩
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)).trans h0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
  exact Real.abs_sin_le_abs

variable {A B Xg kp ki κ : ℝ}

/-- The fold Lie derivative: `U̇ = Φ + D` with the negative definite quadratic form `Φ` and a
remainder `D` built from the Taylor remainders of `sin` and `cos`. -/
private theorem fold_lie_eq (hA : A ≠ 0) (hAB : B ^ 2 = A ^ 2)
    {g : Dynamics.State 3 → Dynamics.State 3}
    (hg0 : ∀ z, g z 0 =
      kp * (-A * Real.sin (z 0) + B * (1 - Real.cos (z 0)) + Xg * z 2) + ki * z 1)
    (hg1 : ∀ z, g z 1 = -A * Real.sin (z 0) + B * (1 - Real.cos (z 0)) + Xg * z 2)
    (hg2 : ∀ z, Xg * g z 2 =
      κ * (A * B - (A * Real.cos (z 0) - B * Real.sin (z 0)) * (Xg * z 2 + B)))
    (z : Dynamics.State 3) :
    fderiv ℝ (fun z : Dynamics.State 3 => foldU A B Xg kp ki κ (z 0) (z 1) (z 2)) z (g z) =
      -(κ * A ^ 2 * z 0 ^ 2 + 2 * ki * (kp + κ) * z 1 ^ 2 + κ * (Xg * z 2) ^ 2) +
      (-κ * (2 * A ^ 2 * (1 - Real.cos (z 0) - z 0 ^ 2 / 2) +
          B * Xg * (z 2 * (1 - Real.cos (z 0))) + A * Xg * (z 2 * (Real.sin (z 0) - z 0))) +
        2 * foldS0 A Xg kp κ (z 0) (z 1) (z 2) *
          (kp * (-A * (Real.sin (z 0) - z 0) + B * (1 - Real.cos (z 0)))) +
        2 * foldS1 A Xg kp ki κ (z 0) (z 1) (z 2) *
          (-A * (Real.sin (z 0) - z 0) + B * (1 - Real.cos (z 0))) +
        2 * foldS2 A kp κ (z 0) (z 1) *
          (κ * (A * B * (1 - Real.cos (z 0)) + A * Xg * (z 2 * (1 - Real.cos (z 0))) +
            B * Xg * (z 2 * Real.sin (z 0)) + A ^ 2 * (Real.sin (z 0) - z 0)))) := by
  rw [(hasFDerivAt_foldU A B Xg kp ki κ z).fderiv]
  simp only [add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
  have e2 : (-(B / A) * Xg + 2 * Xg * foldS2 A kp κ (z 0) (z 1)) * g z 2 =
      (-(B / A) + 2 * foldS2 A kp κ (z 0) (z 1)) * (Xg * g z 2) := by ring
  rw [e2, hg0, hg1, hg2]
  have hq := fold_quad_identity hA Xg kp ki κ (z 0) (z 1) (z 2)
  unfold foldS0 foldS1 foldS2 at hq ⊢
  field_simp
  field_simp at hq
  linear_combination hq - (2 * κ * z 0 * Real.sin (z 0) - 2 * kp * κ * z 1 * Real.sin (z 0) +
    2 * κ * A * (1 - Real.cos (z 0)) + κ * Xg * z 2 * Real.sin (z 0) + κ * B * Real.sin (z 0) +
    κ ^ 2 * z 1 * A * Real.sin (z 0)) * hAB

/-- The fold remainder is `O(s³)`. -/
private theorem fold_D_isBigO (A B Xg kp ki κ : ℝ) :
    (fun z : Dynamics.State 3 =>
      -κ * (2 * A ^ 2 * (1 - Real.cos (z 0) - z 0 ^ 2 / 2) +
          B * Xg * (z 2 * (1 - Real.cos (z 0))) + A * Xg * (z 2 * (Real.sin (z 0) - z 0))) +
        2 * foldS0 A Xg kp κ (z 0) (z 1) (z 2) *
          (kp * (-A * (Real.sin (z 0) - z 0) + B * (1 - Real.cos (z 0)))) +
        2 * foldS1 A Xg kp ki κ (z 0) (z 1) (z 2) *
          (-A * (Real.sin (z 0) - z 0) + B * (1 - Real.cos (z 0))) +
        2 * foldS2 A kp κ (z 0) (z 1) *
          (κ * (A * B * (1 - Real.cos (z 0)) + A * Xg * (z 2 * (1 - Real.cos (z 0))) +
            B * Xg * (z 2 * Real.sin (z 0)) + A ^ 2 * (Real.sin (z 0) - z 0)))) =O[𝓝 0]
      fun z => (|z 0| + |z 1| + |z 2|) ^ 3 := by
  obtain ⟨t2, t3, t4, ts⟩ := trig3_isBigO
  have e0 := coord3_isBigO 0
  have e1 := coord3_isBigO 1
  have e2 := coord3_isBigO 2
  -- the trigonometric factors
  have d1 : (fun z : Dynamics.State 3 =>
      -A * (Real.sin (z 0) - z 0) + B * (1 - Real.cos (z 0))) =O[𝓝 0]
      fun z => (|z 0| + |z 1| + |z 2|) ^ 2 :=
    (mono3_isBigO (t3.const_mul_left (-A)) (by norm_num)).add (t2.const_mul_left B)
  have d2 : (fun z : Dynamics.State 3 =>
      κ * (A * B * (1 - Real.cos (z 0)) + A * Xg * (z 2 * (1 - Real.cos (z 0))) +
        B * Xg * (z 2 * Real.sin (z 0)) + A ^ 2 * (Real.sin (z 0) - z 0))) =O[𝓝 0]
      fun z => (|z 0| + |z 1| + |z 2|) ^ 2 :=
    ((((t2.const_mul_left (A * B)).add
      ((mul3_isBigO e2 t2 (by norm_num)).const_mul_left (A * Xg))).add
      ((mul3_isBigO e2 ts (by norm_num)).const_mul_left (B * Xg))).add
      (mono3_isBigO (t3.const_mul_left (A ^ 2)) (by norm_num))).const_mul_left κ
  -- the linear factors
  have s0 : (fun z : Dynamics.State 3 => 2 * foldS0 A Xg kp κ (z 0) (z 1) (z 2)) =O[𝓝 0]
      fun z => (|z 0| + |z 1| + |z 2|) ^ 1 := by
    unfold foldS0
    exact ((e0.add (e1.const_mul_left (-(kp + κ)))).add (e2.const_mul_left (-1 / A * Xg))
      |>.congr_left fun z => by ring).const_mul_left 2
  have s1 : (fun z : Dynamics.State 3 => 2 * foldS1 A Xg kp ki κ (z 0) (z 1) (z 2)) =O[𝓝 0]
      fun z => (|z 0| + |z 1| + |z 2|) ^ 1 := by
    unfold foldS1
    exact (((e0.const_mul_left (-(kp + κ))).add
      (e1.const_mul_left (-A * κ ^ 2 / 2 + kp ^ 2 + 2 * kp * κ + ki / A))).add
      (e2.const_mul_left ((-κ / 2 + kp / A) * Xg)) |>.congr_left fun z => by ring).const_mul_left 2
  have s2 : (fun z : Dynamics.State 3 => 2 * foldS2 A kp κ (z 0) (z 1)) =O[𝓝 0]
      fun z => (|z 0| + |z 1| + |z 2|) ^ 1 := by
    unfold foldS2
    exact ((e0.const_mul_left (-1 / A)).add (e1.const_mul_left (-κ / 2 + kp / A))).const_mul_left 2
  have hR1 : (fun z : Dynamics.State 3 =>
      -κ * (2 * A ^ 2 * (1 - Real.cos (z 0) - z 0 ^ 2 / 2) +
        B * Xg * (z 2 * (1 - Real.cos (z 0))) + A * Xg * (z 2 * (Real.sin (z 0) - z 0))))
      =O[𝓝 0] fun z => (|z 0| + |z 1| + |z 2|) ^ 3 :=
    (((mono3_isBigO (t4.const_mul_left (2 * A ^ 2)) (by norm_num)).add
      ((mul3_isBigO e2 t2 (by norm_num)).const_mul_left (B * Xg))).add
      ((mul3_isBigO e2 t3 (by norm_num)).const_mul_left (A * Xg))).const_mul_left (-κ)
  exact ((hR1.add (mul3_isBigO s0 (d1.const_mul_left kp |>.congr_left fun z => by ring)
    (by norm_num))).add (mul3_isBigO s1 d1 (by norm_num))).add (mul3_isBigO s2 d2 (by norm_num))

/-- `s² ≤ (3/c)(κA²z₀² + 2k_i(k_p+κ)z₁² + κ(X_g z₂)²)`. -/
private theorem fold_size_isBigO (hA : A ≠ 0) (hκ : 0 < κ) (hk : 0 < ki * (kp + κ))
    (hXg : Xg ≠ 0) :
    (fun z : Dynamics.State 3 => (|z 0| + |z 1| + |z 2|) ^ 2) =O[𝓝 0]
      fun z => κ * A ^ 2 * z 0 ^ 2 + 2 * ki * (kp + κ) * z 1 ^ 2 + κ * (Xg * z 2) ^ 2 := by
  set c := min (κ * A ^ 2) (min (2 * ki * (kp + κ)) (κ * Xg ^ 2)) with hc
  have hc0 : 0 < c := lt_min (by positivity) (lt_min (by nlinarith) (by positivity))
  have hc1 : c ≤ κ * A ^ 2 := min_le_left _ _
  have hc2 : c ≤ 2 * ki * (kp + κ) := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : c ≤ κ * Xg ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine IsBigO.of_bound (3 / c) (Eventually.of_forall fun z => ?_)
  have hq : c * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) ≤
      κ * A ^ 2 * z 0 ^ 2 + 2 * ki * (kp + κ) * z 1 ^ 2 + κ * (Xg * z 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hc1 (sq_nonneg (z 0))
    have := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (z 1))
    have := mul_le_mul_of_nonneg_right hc3 (sq_nonneg (z 2))
    nlinarith
  have hs : (|z 0| + |z 1| + |z 2|) ^ 2 ≤ 3 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) := by
    nlinarith [sq_abs (z 0), sq_abs (z 1), sq_abs (z 2), sq_nonneg (|z 0| - |z 1|),
      sq_nonneg (|z 1| - |z 2|), sq_nonneg (|z 0| - |z 2|)]
  have hq0 : 0 ≤ κ * A ^ 2 * z 0 ^ 2 + 2 * ki * (kp + κ) * z 1 ^ 2 + κ * (Xg * z 2) ^ 2 := by
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hq0]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith

/-- **Saddle-node instability.** A `C¹` field with the fold structure (`A ≠ 0`, `B² = A²`,
`X_g ≠ 0`, `κ > 0`, `k_i(k_p + κ) > 0`) is unstable at the origin: the fold function decreases
strictly on a punctured neighbourhood and is negative along the ray `t (B, 0, AB/X_g)`. -/
private theorem fold_unstable (hA : A ≠ 0) (hAB : B ^ 2 = A ^ 2) (hκ : 0 < κ)
    (hk : 0 < ki * (kp + κ)) (hXg : Xg ≠ 0) {g : Dynamics.State 3 → Dynamics.State 3}
    (hgc : ContDiff ℝ 1 g)
    (hg0 : ∀ z, g z 0 =
      kp * (-A * Real.sin (z 0) + B * (1 - Real.cos (z 0)) + Xg * z 2) + ki * z 1)
    (hg1 : ∀ z, g z 1 = -A * Real.sin (z 0) + B * (1 - Real.cos (z 0)) + Xg * z 2)
    (hg2 : ∀ z, Xg * g z 2 =
      κ * (A * B - (A * Real.cos (z 0) - B * Real.sin (z 0)) * (Xg * z 2 + B))) :
    Unstable g 0 := by
  have hB : B ≠ 0 := by
    intro h
    apply hA
    have : A ^ 2 = 0 := by rw [← hAB, h]; ring
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hg00 : g 0 = 0 := by
    have h0 := hg0 0
    have h1 := hg1 0
    have h2 := hg2 0
    simp at h0 h1 h2
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simp only [Fin.reduceFinMk, PiLp.zero_apply]
      rcases h2 with h2 | h2
      · exact absurd h2 hXg
      · ring_nf at h2 ⊢; linarith
  refine Dynamics.unstable_of_eventually_lie_neg hgc hg00 (contDiff_foldU A B Xg kp ki κ) ?_ ?_
  · -- `U̇ = Φ + D`, `D = O(s³) = o(−Φ)`
    have hQ : ∀ᶠ z in 𝓝[≠] (0 : Dynamics.State 3),
        0 < κ * A ^ 2 * z 0 ^ 2 + 2 * ki * (kp + κ) * z 1 ^ 2 + κ * (Xg * z 2) ^ 2 := by
      refine eventually_nhdsWithin_of_forall fun z hz => ?_
      have hz' : z ≠ 0 := hz
      by_contra hle
      push Not at hle
      have hk2 : 0 < 2 * ki * (kp + κ) := by nlinarith
      have t1 : 0 ≤ κ * A ^ 2 * z 0 ^ 2 := by positivity
      have t2 : 0 ≤ 2 * ki * (kp + κ) * z 1 ^ 2 := mul_nonneg hk2.le (sq_nonneg _)
      have t3 : 0 ≤ κ * (Xg * z 2) ^ 2 := by positivity
      have h0 : z 0 = 0 := by
        by_contra h
        have : 0 < κ * A ^ 2 * z 0 ^ 2 := by positivity
        linarith
      have h1 : z 1 = 0 := by
        by_contra h
        have : 0 < 2 * ki * (kp + κ) * z 1 ^ 2 := mul_pos hk2 (by positivity)
        linarith
      have h2 : z 2 = 0 := by
        by_contra h
        have : 0 < κ * (Xg * z 2) ^ 2 := by
          have : Xg * z 2 ≠ 0 := mul_ne_zero hXg h
          positivity
        linarith
      exact hz' (by ext i; fin_cases i <;> simp [h0, h1, h2])
    refine Dynamics.eventually_neg_of_isLittleO
      (q := fun z => κ * A ^ 2 * z 0 ^ 2 + 2 * ki * (kp + κ) * z 1 ^ 2 + κ * (Xg * z 2) ^ 2) hQ ?_
    refine (((fold_D_isBigO A B Xg kp ki κ).trans_isLittleO
      ((Dynamics.isLittleO_pow_of_tendsto size3_tendsto (by norm_num : 2 < 3)).trans_isBigO
        (fold_size_isBigO hA hκ hk hXg))).mono nhdsWithin_le_nhds).congr_left fun z => ?_
    rw [fold_lie_eq hA hAB hg0 hg1 hg2 z]
    ring
  · -- the fold function is negative along `t (B, 0, AB/X_g)`
    refine Dynamics.frequently_of_forall_smul (WithLp.toLp 2 ![B, 0, A * B / Xg]) fun t ht => ?_
    have hU0 : foldU A B Xg kp ki κ ((0 : Dynamics.State 3) 0) ((0 : Dynamics.State 3) 1)
        ((0 : Dynamics.State 3) 2) = 0 := by simp [foldU]
    show foldU A B Xg kp ki κ _ _ _ < foldU A B Xg kp ki κ _ _ _
    rw [hU0]
    simp only [PiLp.smul_apply, smul_eq_mul]
    simp [foldU]
    field_simp
    have hB2 : 0 < B ^ 2 := by positivity
    nlinarith [mul_pos ht hB2, mul_pos (mul_pos ht ht) hB2]

end FoldLocal

/-! ## The quasi-static GFL at the fold and within positive gains -/

section Members

/-- The translated field is `C¹`. -/
@[powerlib_foundation] theorem contDiff_model_field (m : Model) : ContDiff ℝ 1 m.field :=
  (contDiff_field m.params).comp (contDiff_id.add contDiff_const)

private theorem model_field0 (m : Model) (z : Dynamics.State 3) :
    m.field z 0 = m.params.kp * vq m.params (z 0 + m.θ) (z 2 + m.Id) + m.params.ki * z 1 := by
  simp [Model.field, QuasiStatic.field, Dynamics.lift, coordField, point]

private theorem model_field1 (m : Model) (z : Dynamics.State 3) :
    m.field z 1 = vq m.params (z 0 + m.θ) (z 2 + m.Id) := by
  simp [Model.field, QuasiStatic.field, Dynamics.lift, coordField, point]

private theorem model_field2 (m : Model) (z : Dynamics.State 3) :
    m.field z 2 = m.params.kP * (m.params.Pref - power m.params (z 0 + m.θ) (z 2 + m.Id)) := by
  simp [Model.field, QuasiStatic.field, Dynamics.lift, coordField, point]

private theorem vq_shift (p : Params) {θ Id : ℝ} (heq : -(p.Xg * Id) = p.V * Real.sin θ)
    (φ ι : ℝ) : vq p (φ + θ) (ι + Id) =
      -(p.V * Real.cos θ) * Real.sin φ + p.V * Real.sin θ * (1 - Real.cos φ) + -p.Xg * ι := by
  unfold vq
  rw [Real.sin_add]
  linear_combination heq

/-- The translated field of a balanced model, with `A = V cos θ*`, `B = V sin θ*`, `ι = i_d − i_d*`:
`φ̇ = k_p v + k_i x`, `ẋ = v`, `−X_g i̇_d = (3/2)k_P (AB − (A cos φ − B sin φ)(−X_g ι + B))` where
`v = −A sin φ + B(1 − cos φ) − X_g ι`. -/
@[powerlib_foundation] theorem model_fold_form {m : Model} (heq : IsEq m.params m.θ m.Id)
    (z : Dynamics.State 3) :
    m.field z 0 = m.params.kp * (-(m.params.V * Real.cos m.θ) * Real.sin (z 0) +
        m.params.V * Real.sin m.θ * (1 - Real.cos (z 0)) + -m.params.Xg * z 2) +
        m.params.ki * z 1 ∧
    m.field z 1 = -(m.params.V * Real.cos m.θ) * Real.sin (z 0) +
        m.params.V * Real.sin m.θ * (1 - Real.cos (z 0)) + -m.params.Xg * z 2 ∧
    -m.params.Xg * m.field z 2 = 3 / 2 * m.params.kP *
      (m.params.V * Real.cos m.θ * (m.params.V * Real.sin m.θ) -
        (m.params.V * Real.cos m.θ * Real.cos (z 0) - m.params.V * Real.sin m.θ * Real.sin (z 0)) *
          (-m.params.Xg * z 2 + m.params.V * Real.sin m.θ)) := by
  obtain ⟨h1, h2⟩ := heq
  refine ⟨by rw [model_field0, vq_shift m.params h1], by rw [model_field1, vq_shift m.params h1],
    ?_⟩
  rw [model_field2, h2]
  unfold power
  rw [Real.cos_add]
  linear_combination (-(3 / 2) * m.params.kP * (m.params.V * Real.cos m.θ * Real.cos (z 0) -
    m.params.V * Real.sin m.θ * Real.sin (z 0)) + 3 / 2 * m.params.kP *
    (m.params.V * Real.cos m.θ)) * h1

/-- **Saddle-node.** With positive gains, at a balanced point on the fold `cos 2θ* = 0` with
`V cos θ* > 0` the translated field is unstable. -/
private theorem model_fold_unstable {m : Model} (heq : IsEq m.params m.θ m.Id)
    (hkp : 0 < m.params.kp) (hki : 0 < m.params.ki) (hkP : 0 < m.params.kP)
    (hA : 0 < m.params.V * Real.cos m.θ) (hc2 : Real.cos (2 * m.θ) = 0) :
    Unstable m.field 0 := by
  have hAB : (m.params.V * Real.sin m.θ) ^ 2 = (m.params.V * Real.cos m.θ) ^ 2 := by
    rw [Real.cos_two_mul] at hc2
    have := Real.sin_sq_add_cos_sq m.θ
    linear_combination (m.params.V ^ 2) * (this - hc2)
  have hXg : m.params.Xg ≠ 0 := by
    intro h
    have hB : m.params.V * Real.sin m.θ = 0 := by rw [← heq.1, h, zero_mul, neg_zero]
    rw [hB] at hAB
    have : (m.params.V * Real.cos m.θ) ^ 2 = 0 := by rw [← hAB]; ring
    exact hA.ne' (pow_eq_zero_iff two_ne_zero |>.mp this)
  exact fold_unstable (κ := 3 / 2 * m.params.kP) (Xg := -m.params.Xg) hA.ne' hAB (by positivity)
    (by positivity) (neg_ne_zero.mpr hXg) (contDiff_model_field m)
    (fun z => (model_fold_form heq z).1) (fun z => (model_fold_form heq z).2.1)
    (fun z => (model_fold_form heq z).2.2)

/-- Membership through the sound translation. -/
private theorem mem_den_of_meets {m : Model} {s : Sentence}
    (h : ∀ q ∈ translate s, Meets m q) :
    connection% (m ∈ family.den s) := by
  change m ∈ family.den s
  have hs := chain_le_semantics
  unfold powerlib.TMIO.Statement at hs
  exact (Family.chain_le_semantics_iff.mp hs s) ((TMIO.mem_realize _ _ _).mpr h)

private theorem seed_of_frequently {P : Dynamics.State 3 → Prop}
    (h : ∃ᶠ z in 𝓝 (0 : Dynamics.State 3), P z) (ε : ℝ) (hε : 0 < ε) :
    ∃ x, ‖x - 0‖ < ε ∧ P x := by
  obtain ⟨x, hP, hx⟩ := (h.and_eventually (Metric.ball_mem_nhds 0 hε)).exists
  exact ⟨x, by rw [← dist_eq_norm]; exact hx, hP⟩

/-- A dead grid (`V = 0`) with `k_i > 0`: the integrator or the current drifts linearly. -/
private theorem unstable_of_V_eq_zero {m : Model} (heq : IsEq m.params m.θ m.Id)
    (hki : 0 < m.params.ki) (hV : m.params.V = 0) : Unstable m.field 0 := by
  have h1 : m.params.Xg * m.Id = 0 := by
    have := heq.1; rw [hV, zero_mul] at this; linarith
  have hf0 : ∀ z, m.field z 0 = m.params.kp * (-m.params.Xg * z 2) + m.params.ki * z 1 :=
    fun z => by rw [model_field0]; unfold vq; rw [hV]; linear_combination (-m.params.kp) * h1
  have hf1 : ∀ z, m.field z 1 = -m.params.Xg * z 2 := fun z => by
    rw [model_field1]; unfold vq; rw [hV]; linear_combination -h1
  have hf2 : ∀ z, m.field z 2 = 0 := fun z => by
    rw [model_field2, heq.2]; unfold power; rw [hV]; ring
  by_cases hXg : m.params.Xg = 0
  · -- `θ̇ = k_i x`, `ẋ = 0`: Chetaev with `θ x`
    have hd : ∀ z : Dynamics.State 3, HasFDerivAt (fun z : Dynamics.State 3 => z 0 * z 1)
        (z 0 • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1 : Dynamics.State 3 →L[ℝ] ℝ) +
          z 1 • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 : Dynamics.State 3 →L[ℝ] ℝ)) z := fun z => by
      have a := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) :
        Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
      have b := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) :
        Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
      exact (a.mul b).congr_fderiv (by ext v; simp)
    refine Dynamics.unstable_of_chetaev (W := fun z : Dynamics.State 3 => z 0 * z 1)
      (contDiff_model_field m) (by fun_prop) one_pos
      (seed_of_frequently (Dynamics.frequently_of_forall_smul (WithLp.toLp 2 ![1, 1, 0])
        fun t ht => by simp; positivity)) fun z _ hW => ?_
    rw [(hd z).fderiv]
    simp only [add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
    rw [hf0, hf1, hXg]
    have hz1 : z 1 ≠ 0 := fun h => by rw [h, mul_zero] at hW; exact lt_irrefl 0 hW
    simp only [neg_zero, zero_mul, mul_zero, zero_add]
    have : 0 < z 1 * z 1 := mul_self_pos.mpr hz1
    nlinarith
  · -- `ẋ = −X_g ι`, `ι̇ = 0`: Chetaev with `−X_g x ι`
    have hd : ∀ z : Dynamics.State 3, HasFDerivAt
        (fun z : Dynamics.State 3 => -m.params.Xg * (z 1 * z 2))
        ((-m.params.Xg * z 1) • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2 : Dynamics.State 3 →L[ℝ] ℝ) +
          (-m.params.Xg * z 2) • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1 :
            Dynamics.State 3 →L[ℝ] ℝ)) z := fun z => by
      have a := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) :
        Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
      have b := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) :
        Dynamics.State 3 →L[ℝ] ℝ).hasFDerivAt (x := z)
      exact ((a.mul b).const_mul (-m.params.Xg)).congr_fderiv (by ext v; simp; ring)
    refine Dynamics.unstable_of_chetaev
      (W := fun z : Dynamics.State 3 => -m.params.Xg * (z 1 * z 2))
      (contDiff_model_field m) (by fun_prop) one_pos
      (seed_of_frequently (Dynamics.frequently_of_forall_smul
        (WithLp.toLp 2 ![0, -m.params.Xg, 1]) fun t ht => by
          simp
          have : 0 < m.params.Xg ^ 2 := by positivity
          nlinarith [mul_pos (mul_pos ht ht) this])) fun z _ hW => ?_
    rw [(hd z).fderiv]
    simp only [add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul]
    rw [hf1, hf2]
    have hz2 : z 2 ≠ 0 := fun h => by rw [h, mul_zero, mul_zero] at hW; exact lt_irrefl 0 hW
    have : 0 < (m.params.Xg * z 2) * (m.params.Xg * z 2) :=
      mul_self_pos.mpr (mul_ne_zero hXg hz2)
    nlinarith

/-- With positive gains a Lyapunov stable equilibrium has a strict Routh–Hurwitz Jacobian: every
other equilibrium is unstable (`V = 0`; `V cos θ* < 0`, `tr J > 0`; `cos θ* = 0` or
`cos 2θ* < 0`, `det J > 0`; the fold `cos 2θ* = 0`). -/
private theorem jacobianStable_of_lyapunovStable {m : Model} (hpos : Meets m .positiveGains)
    (heq : IsEq m.params m.θ m.Id) (h : LyapunovStable m.field 0) : Meets m .jacobianStable := by
  obtain ⟨hkp, hki, hkP⟩ := hpos
  have hunst : Meets m .jacobianUnstable → False := fun hu => by
    have hd := mem_den_of_meets (m := m) (s := .flow .unstable) (by
      intro q hq
      simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact heq
      · exact hu)
    rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hd
    exact hd h
  have htr := trace_jac m.params m.θ m.Id
  have hm2 := principalMinorSum_jac m.params heq.1
  have hdet := det_jac m.params heq.1
  show (jac m.params m.θ m.Id).trace < 0 ∧ (jac m.params m.θ m.Id).det < 0 ∧
    (jac m.params m.θ m.Id).trace * Criteria.principalMinorSum (jac m.params m.θ m.Id) <
      (jac m.params m.θ m.Id).det
  rw [htr, hm2, hdet]
  by_cases hV : m.params.V = 0
  · exact (unstable_of_V_eq_zero heq hki hV h).elim
  have hV2 : 0 < m.params.V ^ 2 := by positivity
  rcases lt_trichotomy (m.params.V * Real.cos m.θ) 0 with hA | hA | hA
  · refine (hunst (Or.inr ?_)).elim
    show 0 < (jac m.params m.θ m.Id).trace
    rw [htr]; unfold a2; nlinarith
  · have hc : Real.cos m.θ = 0 := (mul_eq_zero.mp hA).resolve_left hV
    have hc2 : Real.cos (2 * m.θ) = -1 := by rw [Real.cos_two_mul, hc]; norm_num
    refine (hunst (Or.inl ?_)).elim
    show 0 < (jac m.params m.θ m.Id).det
    rw [hdet]; unfold a0; rw [hc2]
    have : 0 < m.params.V ^ 2 * m.params.kP * m.params.ki := by positivity
    nlinarith
  · rcases lt_trichotomy (Real.cos (2 * m.θ)) 0 with hc2 | hc2 | hc2
    · refine (hunst (Or.inl ?_)).elim
      show 0 < (jac m.params m.θ m.Id).det
      rw [hdet]; unfold a0
      have : 0 < m.params.V ^ 2 * m.params.kP * m.params.ki := by positivity
      nlinarith
    · exact (model_fold_unstable heq hkp hki hkP hA hc2 h).elim
    · have ha2 : 0 < a2 m.params m.θ := by
        unfold a2
        have : 0 < 3 * m.params.kP + 2 * m.params.kp := by positivity
        have : 0 < m.params.V * Real.cos m.θ / 2 := by positivity
        positivity
      have ha0 : 0 < a0 m.params m.θ := by unfold a0; positivity
      have hcos : Real.cos m.θ ≠ 0 := fun hc => by rw [hc, mul_zero] at hA; exact lt_irrefl 0 hA
      have hgap : a0 m.params m.θ < a2 m.params m.θ * a1 m.params m.θ := by
        have hid := a2_mul_a1_sub_a0 m.params m.θ
        have t1 : 0 ≤ (9 * m.params.V * m.params.kP ^ 2 * m.params.kp +
            6 * m.params.V * m.params.kP * m.params.kp ^ 2) * Real.cos m.θ *
            Real.cos (2 * m.θ) := by
          have : (9 * m.params.V * m.params.kP ^ 2 * m.params.kp +
              6 * m.params.V * m.params.kP * m.params.kp ^ 2) * Real.cos m.θ *
              Real.cos (2 * m.θ) = (9 * m.params.kP ^ 2 * m.params.kp +
              6 * m.params.kP * m.params.kp ^ 2) * (m.params.V * Real.cos m.θ) *
              Real.cos (2 * m.θ) := by ring
          rw [this]; positivity
        have t2 : 0 < 4 * m.params.ki * m.params.kp * Real.cos m.θ ^ 2 := by positivity
        have t3 : 0 ≤ 6 * m.params.kP * m.params.ki * Real.sin m.θ ^ 2 := by positivity
        have : 0 < m.params.V ^ 2 / 4 * ((9 * m.params.V * m.params.kP ^ 2 * m.params.kp +
            6 * m.params.V * m.params.kP * m.params.kp ^ 2) * Real.cos m.θ *
            Real.cos (2 * m.θ) + 4 * m.params.ki * m.params.kp * Real.cos m.θ ^ 2 +
            6 * m.params.kP * m.params.ki * Real.sin m.θ ^ 2) := by positivity
        linarith
      refine ⟨by linarith, by linarith, by nlinarith⟩

/-- Within positive gains the translations of Lyapunov and local asymptotic stability,
`{equilibrium, jacobianStable}`, are exact: a Lyapunov stable point of the `C¹` field is an
equilibrium, and the strict Routh–Hurwitz guard decides (`Spectral.exactUnder_of_equilibrium`). -/
private theorem exactUnder_of_routh {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable) :
    connection% (family.ExactUnder {.positiveGains} (.flow P)) := by
  change family.ExactUnder {.positiveGains} (.flow P)
  have ht : family.translate (.flow P) = {.equilibrium, .jacobianStable} := by
    rcases hP with rfl | rfl <;> rfl
  refine Spectral.exactUnder_of_equilibrium (fun m P => family_isAutonomous.mem_den_flow)
    (hP.imp_right Or.inl) {.positiveGains} (fun m => Meets m .jacobianStable)
    (fun m _ h => mem_den_of_meets ((TMIO.mem_realize _ _ _).mp h))
    (fun m _ => contDiff_model_field m) (fun m hm heq hG hd => hG ?_) fun m hm heq hG => ?_
  · have hpos : Meets m .positiveGains := (TMIO.mem_realize _ _ _).mp hm .positiveGains rfl
    have hls : LyapunovStable m.field 0 := by
      have h := family_isAutonomous.mem_den_flow.mp hd
      rcases hP with rfl | rfl
      · exact h
      · exact h.1
    exact jacobianStable_of_lyapunovStable hpos
      (isEq_of_field_eq_zero hpos.2.2.ne' (by simpa [Model.field] using heq)) hls
  · have hpos : Meets m .positiveGains := (TMIO.mem_realize _ _ _).mp hm .positiveGains rfl
    rw [ht, (connection_proof% TMIO.mem_realize)]
    rintro q (rfl | rfl)
    · exact isEq_of_field_eq_zero hpos.2.2.ne' (by simpa [Model.field] using heq)
    · exact hG

end Members

/-! ### Connection conclusions at the fold and within positive gains -/

/-- Quasi-static GFL with positive gains at a balanced point on the fold `cos 2θ* = 0` with
`V cos θ* > 0` (the transmission limit `P_ref = ±P_SN`): the operating point is unstable — a
saddle-node, whose Jacobian has a simple zero eigenvalue (`det J = 0`) and two stable ones. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold (p : Params) (hkp : 0 < p.kp)
    (hki : 0 < p.ki) (hkP : 0 < p.kP) {θ Id : ℝ} (heq : IsEq p θ Id)
    (hA : 0 < p.V * Real.cos θ) (hc2 : Real.cos (2 * θ) = 0) :
    connection% (Model.mk p θ Id ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  exact model_fold_unstable (m := Model.mk p θ Id) heq hkp hki hkP hA hc2

/-- Same, at the fold angle `θ* = π/4` (`V > 0`): the transmission limit is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_pi_div_four (p : Params) (hV : 0 < p.V)
    (hkp : 0 < p.kp) (hki : 0 < p.ki) (hkP : 0 < p.kP) {Id : ℝ}
    (heq : IsEq p (Real.pi / 4) Id) :
    connection% (Model.mk p (Real.pi / 4) Id ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_fold p hkp hki hkP heq
    (mul_pos hV (by rw [Real.cos_pi_div_four]; positivity))
    (by rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two])

/-- **Within positive gains the local asymptotic translation is exact.** For `k_p, k_i, k_P > 0`
the selected point is locally asymptotically stable exactly when it is an equilibrium with a strict
Routh–Hurwitz Jacobian; in particular the fold `cos 2θ* = 0` (no Hopf pair,
`no_imaginary_eigenvalue`) is a saddle-node and unstable (`mem_den_unstable_of_fold`). -/
@[tmio TM, powerlib_domain] theorem exactUnder_locallyAsymptoticallyStable :
    connection% (family.ExactUnder {.positiveGains} (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact exactUnder_of_routh (Or.inr rfl)

/-- **Within positive gains the Lyapunov translation is exact**: every non-Hurwitz point with
positive gains is unstable (the undamped witness of `not_exact_lyapunovStable` has
`k_p = k_P = 0`). -/
@[tmio TM, powerlib_domain] theorem exactUnder_lyapunovStable :
    connection% (family.ExactUnder {.positiveGains} (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact exactUnder_of_routh (Or.inl rfl)

end powerlib.GFL.PowerLoop.QuasiStatic
