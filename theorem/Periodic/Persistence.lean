import theorem.Periodic.MeanTrace

/-! # Persistence of the small-signal verdicts under small periodic modulation

Small-signal analysis replaces the periodic system `ẋ = (A₀ + ε A₁(t)) x` by its constant matrix
`A₀` (the Jacobian at an equilibrium, or a frozen or averaged matrix). The monodromy matrix
depends continuously on the modulation depth, `M(ε) → e^{T A₀}` as `ε → 0` (a Grönwall estimate,
`‖M(ε) − e^{TA₀}‖ = O(|ε|)`), so the strict small-signal verdicts survive the passage to the
Floquet level for small `ε`, in any dimension:

* `A₀` Hurwitz: Floquet stable for `|ε| < ε₀` (`e^{TA₀}` has a contractive power, and a
  contractive power persists); hence a parametric instability of a system whose small-signal
  matrix is Hurwitz needs a finite modulation depth and disappears as `ε → 0`;
* `A₀` with an eigenvalue `Re λ > 0`: Floquet unstable for `|ε| < ε₀`. Lower semicontinuity of
  the spectral radius comes from the factorization `det(zI − N) = ∏ (z − μᵢ)` over the
  eigenvalues: with `z = e^{λT}`, `det(zI − M(ε)) → det(zI − e^{TA₀}) = 0` forces an eigenvalue of
  `M(ε)` near the circle `|μ| = |z|`, no root continuity being needed;
* the growth rate: the largest Floquet exponent `(1/T) ln |μ|` of `M(ε)` tends to the spectral
  abscissa `α = max Re λ(A₀)`, the small-signal growth rate.

The convergence is not uniform in the depth: at finite `ε` the Floquet verdict can differ from
the small-signal one in both directions (`ParametricResonance.Signature.frozen_damping_paradox`,
and parametric stabilization of a saddle).

Scope.
* `ẋ = (A₀ + ε A₁(t)) x` on `ℝ^X` (finite `X`; `Fin n` where Hurwitz or Schur stability is
  used), constant real `A₀`, continuous real `T`-periodic `A₁`, `T > 0`, real `ε`; transition and
  monodromy matrices of `theorem/Periodic/Transition.lean` with the operator `L∞` norm.
* Hurwitz stability is `LinearSystems.IsHurwitz` (every eigenvalue of the complexification has
  negative real part); Schur stability `LTI.SchurStable` and Floquet instability
  `Periodic.FloquetUnstable` are those of `theorem/LTI/Discrete.lean` and
  `theorem/Periodic/Floquet.lean`.
* Generic mathematics; no model family.

Source: regular perturbation of the monodromy matrix of a periodic linear system (Grönwall's
inequality, Mathlib `norm_le_gronwallBound_of_norm_deriv_right_le`; Yakubovich–Starzhinskii,
*Linear Differential Equations with Periodic Coefficients*, the small-parameter method); the LTI
Floquet criterion `LTI.isHurwitz_iff_schurStable_exp`, the Gelfand power-norm lemma
`LTI.exists_pow_norm_lt_one` and the constant monodromy `Periodic.monodromy_const`.

Results.
* `norm_transition_sub_le` — `‖Φ_A(t, s) − Φ_B(t, s)‖ ≤ η (t − s) ‖I‖ e^{(M_A + M_B)(t − s)}` for
  `‖A − B‖ ≤ η`, `‖A‖ ≤ M_A`, `‖B‖ ≤ M_B`.
* `tendsto_monodromy` — `monodromy (A₀ + ε A₁) T 0 → e^{T A₀}` as `ε → 0`.
* `exists_norm_gt_of_norm_det_lt` — `|det(zI − N)| < (|z| − r)^n` with `r < |z|` gives an
  eigenvalue of `N` of modulus `> r`.
* `schurStable_of_pow_norm_lt_one` — `‖P^k‖ < 1`, `k > 0`, gives Schur stability.
* `transition_sub_smul_one` — `Φ_{A − cI}(t, s) = e^{−c(t − s)} Φ_A(t, s)`.
* `exists_schurStable_of_isHurwitz` — `A₀` Hurwitz: Schur-stable monodromy for `|ε| < ε₀`.
* `exists_floquetUnstable_of_re_pos` — an eigenvalue of `A₀` with `Re λ > 0`: Floquet unstable
  for `|ε| < ε₀`.
* `floquet_exponent_tendsto` — for every `η > 0` and `|ε| < ε₀`: some multiplier has
  `(1/T) ln |μ| > α − η` and every multiplier has `(1/T) ln |μ| < α + η`.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function Filter Topology Polynomial
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Continuous dependence of the transition matrix on the state matrix -/

@[tmio T, powerlib_foundation] private theorem gronwallBound_zero_le {K ε x : ℝ} (hK : 0 ≤ K)
    (hε : 0 ≤ ε) : gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rcases hK.eq_or_lt with rfl | hKpos
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hKpos.ne']
    simp only [zero_mul, zero_add]
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h := Real.add_one_le_exp (-(K * x))
      have hexp : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [mul_le_mul_of_nonneg_right h (Real.exp_pos (K * x)).le]
    rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
    nlinarith [mul_le_mul_of_nonneg_left h1 hε]

/-- **Grönwall estimate for the transition matrix.** For continuous state matrices with
`‖A‖ ≤ M_A`, `‖B‖ ≤ M_B` and `‖A(t) − B(t)‖ ≤ η`:
`‖Φ_A(t, s) − Φ_B(t, s)‖ ≤ η (t − s) ‖I‖ e^{(M_A + M_B)(t − s)}` for `s ≤ t` (Mathlib
`norm_le_gronwallBound_of_norm_deriv_right_le` applied to `Φ_A − Φ_B`, whose derivative is
`B (Φ_A − Φ_B) + (A − B) Φ_A`). -/
@[tmio T, powerlib_foundation] theorem norm_transition_sub_le {A B : ℝ → Matrix X X ℝ}
    {MA MB η : ℝ} (hA : Continuous A) (hB : Continuous B) (hMA : ∀ t, ‖A t‖ ≤ MA)
    (hMB : ∀ t, ‖B t‖ ≤ MB) (hη : ∀ t, ‖A t - B t‖ ≤ η) {s t : ℝ} (hst : s ≤ t) :
    ‖transition A t s - transition B t s‖ ≤
      η * (t - s) * ‖(1 : Matrix X X ℝ)‖ * Real.exp ((MA + MB) * (t - s)) := by
  have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0)
  have hMB0 : 0 ≤ MB := (norm_nonneg _).trans (hMB 0)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0)
  set ε := η * ‖(1 : Matrix X X ℝ)‖ * Real.exp (MA * (t - s)) with hε
  have hε0 : 0 ≤ ε := by positivity
  set f : ℝ → Matrix X X ℝ := fun r => transition A r s - transition B r s with hfdef
  have hf' : ∀ r, HasDerivAt f (A r * transition A r s - B r * transition B r s) r :=
    fun r => (Dynamics.stm_hasDerivAt hA r s).sub (Dynamics.stm_hasDerivAt hB r s)
  have hfc : ContinuousOn f (Icc s t) := fun r _ => (hf' r).continuousAt.continuousWithinAt
  have hbound : ∀ r ∈ Ico s t,
      ‖A r * transition A r s - B r * transition B r s‖ ≤ MB * ‖f r‖ + ε := by
    intro r hr
    have e : A r * transition A r s - B r * transition B r s =
        B r * f r + (A r - B r) * transition A r s := by
      simp only [hfdef]; noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hMB r) (norm_nonneg _))
    · refine (norm_mul_le _ _).trans ?_
      have hΦ := norm_transition_le hMA hr.1
      rw [Real.coe_toNNReal _ hMA0] at hΦ
      have hexp : Real.exp (MA * (r - s)) ≤ Real.exp (MA * (t - s)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hr.2]) hMA0)
      calc ‖A r - B r‖ * ‖transition A r s‖ ≤ η * (‖(1 : Matrix X X ℝ)‖ *
            Real.exp (MA * (r - s))) := mul_le_mul (hη r) hΦ (norm_nonneg _) hη0
        _ ≤ η * (‖(1 : Matrix X X ℝ)‖ * Real.exp (MA * (t - s))) := by gcongr
        _ = ε := by rw [hε]; ring
  have h0 : ‖f s‖ ≤ 0 := by simp [hfdef, LinearSystems.stateTransitionMatrix_self]
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hfc
    (fun r _ => (hf' r).hasDerivWithinAt) h0 hbound t ⟨hst, le_rfl⟩
  refine h.trans ((gronwallBound_zero_le hMB0 hε0).trans_eq ?_)
  rw [hε, add_mul, Real.exp_add]
  ring

variable {A₁ : ℝ → Matrix X X ℝ} {T : ℝ}

/-- **The monodromy depends continuously on the modulation depth.** For a constant `A₀` and a
continuous `T`-periodic `A₁`, the monodromy matrix of `ẋ = (A₀ + ε A₁(t)) x` tends to the
small-signal monodromy `e^{T A₀}` as `ε → 0`; quantitatively
`‖M(ε) − e^{TA₀}‖ ≤ |ε| B T ‖I‖ e^{(2‖A₀‖ + B) T}` for `|ε| ≤ 1`, `B = sup ‖A₁‖`. -/
@[tmio T, powerlib_foundation] theorem tendsto_monodromy (A₀ : Matrix X X ℝ)
    (hA₁ : Continuous A₁) (hP : Periodic A₁ T) (hT : 0 < T) :
    Tendsto (fun ε : ℝ => monodromy (fun t => A₀ + ε • A₁ t) T 0) (𝓝 0)
      (𝓝 (NormedSpace.exp (T • A₀))) := by
  obtain ⟨B, hB⟩ := exists_bound_of_periodic hA₁ hP hT
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [← monodromy_const A₀ hT.le 0]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  set C := B * T * ‖(1 : Matrix X X ℝ)‖ * Real.exp ((‖A₀‖ + B + ‖A₀‖) * T) with hC
  have hlim : Tendsto (fun ε : ℝ => |ε| * C) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  have hball : ∀ᶠ ε : ℝ in 𝓝 0, |ε| ≤ 1 := by
    have : Icc (-1 : ℝ) 1 ∈ 𝓝 0 := Icc_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with ε hε
    exact abs_le.mpr hε
  filter_upwards [hball] with ε hε
  have h := norm_transition_sub_le (A := fun t => A₀ + ε • A₁ t) (B := fun _ => A₀)
    (MA := ‖A₀‖ + B) (MB := ‖A₀‖) (η := |ε| * B) (by fun_prop) continuous_const
    (fun t => by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs]
      calc |ε| * ‖A₁ t‖ ≤ 1 * B := mul_le_mul hε (hB t) (norm_nonneg _) zero_le_one
        _ = B := one_mul B)
    (fun _ => le_rfl)
    (fun t => by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB t) (abs_nonneg ε))
    (show (0 : ℝ) ≤ 0 + T by linarith)
  simp only [monodromy]
  refine h.trans_eq ?_
  rw [hC, zero_add, sub_zero]
  ring

/-! ## Eigenvalues of nearby matrices -/

/-- **An eigenvalue outside a disk persists.** If `|det(z I − N)| < (|z| − r)^n` for some
`|z| > r ≥ 0`, then `N` has an eigenvalue of modulus `> r` (`det(zI − N) = ∏ (z − μᵢ)` over the
eigenvalues with multiplicity, and `|z − μᵢ| ≥ |z| − r` for `|μᵢ| ≤ r`). -/
@[tmio T, powerlib_foundation] theorem exists_norm_gt_of_norm_det_lt {N : Matrix X X ℂ} {z : ℂ}
    {r : ℝ} (hrz : r < ‖z‖)
    (h : ‖(Matrix.scalar X z - N).det‖ < (‖z‖ - r) ^ Fintype.card X) :
    ∃ μ ∈ spectrum ℂ N, r < ‖μ‖ := by
  by_contra hcon
  push Not at hcon
  have hsplit : (N.charpoly.roots.map fun a => Polynomial.X - Polynomial.C a).prod =
      N.charpoly :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq N.charpoly_monic
      IsAlgClosed.card_roots_eq_natDegree
  have hev : (Matrix.scalar X z - N).det = (N.charpoly.roots.map fun μ => z - μ).prod := by
    rw [← Matrix.eval_charpoly]
    conv_lhs => rw [← hsplit]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun μ _ => ?_
    simp
  have hnorm : ‖(Matrix.scalar X z - N).det‖ = (N.charpoly.roots.map fun μ => ‖z - μ‖).prod := by
    rw [hev]
    have := map_multiset_prod (normHom (α := ℂ)) (N.charpoly.roots.map fun μ => z - μ)
    rw [Multiset.map_map] at this
    exact this
  have hle : (N.charpoly.roots.map fun _ => ‖z‖ - r).prod ≤
      (N.charpoly.roots.map fun μ => ‖z - μ‖).prod :=
    Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => by linarith) fun μ hμ => by
      have := hcon μ (mem_spectrum_of_mem_roots hμ)
      have := norm_sub_norm_le z μ
      linarith
  rw [Multiset.map_const', Multiset.prod_replicate, card_roots_charpoly, ← hnorm] at hle
  linarith

/-- A real matrix with a contractive power, `‖P^k‖ < 1` (`k > 0`), is Schur stable: an eigenpair
`P v = μ v` gives `|μ|^k ‖v‖ = ‖P^k v‖ ≤ ‖P^k‖ ‖v‖`. -/
@[tmio T, powerlib_foundation] theorem schurStable_of_pow_norm_lt_one {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} {k : ℕ} (hk : 0 < k) (h : ‖P ^ k‖ < 1) : LTI.SchurStable P := by
  intro μ v hv hPv
  have hpow := Linear.mulVec_pow_of_eigen hPv k
  have hmap : (P ^ k).map (algebraMap ℝ ℂ) = (P.map (algebraMap ℝ ℂ)) ^ k := by
    have h := map_pow ((algebraMap ℝ ℂ).mapMatrix (m := Fin n)) P k
    simpa [RingHom.mapMatrix_apply] using h
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hle : ‖μ‖ ^ k * ‖v‖ ≤ ‖P ^ k‖ * ‖v‖ := by
    calc ‖μ‖ ^ k * ‖v‖ = ‖μ ^ k • v‖ := by rw [norm_smul, norm_pow]
      _ = ‖(P.map (algebraMap ℝ ℂ)) ^ k *ᵥ v‖ := by rw [hpow]
      _ ≤ ‖(P.map (algebraMap ℝ ℂ)) ^ k‖ * ‖v‖ := Matrix.linfty_opNorm_mulVec _ _
      _ = ‖P ^ k‖ * ‖v‖ := by rw [← hmap, LTI.norm_map_algebraMap]
  have hlt : ‖μ‖ ^ k < 1 := lt_of_le_of_lt (le_of_mul_le_mul_right hle hvpos) h
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg μ) hk.ne').mp hlt

/-- Shifting the state matrix by a multiple of the identity rescales the transition matrix:
`Φ_{A − cI}(t, s) = e^{−c (t − s)} Φ_A(t, s)` for `s ≤ t`. -/
@[tmio T, powerlib_foundation] theorem transition_sub_smul_one {A : ℝ → Matrix X X ℝ} {M : ℝ}
    (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (c : ℝ) {s t : ℝ} (hst : s ≤ t) :
    transition (fun r => A r - c • (1 : Matrix X X ℝ)) t s =
      Real.exp (-(c * (t - s))) • transition A t s := by
  have hY : IsIntegralCurveOn (fun r => Real.exp (-(c * (r - s))) • transition A r s)
      (matField (fun r => A r - c • (1 : Matrix X X ℝ))) (Ici s) := by
    intro r _
    have he : HasDerivAt (fun r => Real.exp (-(c * (r - s))))
        (Real.exp (-(c * (r - s))) * -c) r := by
      have h0 : HasDerivAt (fun r => -(c * (r - s))) (-c) r := by
        convert ((hasDerivAt_id r).sub_const s).const_mul (-c) using 1
        · funext x; simp
        · ring
      exact h0.exp
    have h := he.smul (Dynamics.stm_hasDerivAt hA r s)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [matField, sub_mul, smul_mul_assoc, one_mul, mul_smul_comm, transition]
    module
  have h := transition_unique (A := fun r => A r - c • (1 : Matrix X X ℝ))
    (M := M + |c| * ‖(1 : Matrix X X ℝ)‖) (by fun_prop)
    (fun r => (norm_sub_le _ _).trans (add_le_add (hM r) (by rw [norm_smul, Real.norm_eq_abs])))
    hY t hst
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, one_smul,
    LinearSystems.stateTransitionMatrix_self, mul_one] at h
  exact h.symm

/-! ## Persistence of the small-signal verdicts -/

/-- **A Hurwitz small-signal matrix stays Floquet stable under small modulation.** For a
Hurwitz `A₀` and a continuous `T`-periodic `A₁` there is `ε₀ > 0` such that
`ẋ = (A₀ + ε A₁(t)) x` has all Floquet multipliers inside the unit circle for `|ε| < ε₀`
(`e^{TA₀}` has a contractive power, which persists by `tendsto_monodromy`). In particular a
parametric instability of a system whose small-signal matrix is Hurwitz disappears as `ε → 0`. -/
@[tmio T, powerlib_foundation] theorem exists_schurStable_of_isHurwitz {n : ℕ}
    {A₀ : Matrix (Fin n) (Fin n) ℝ} (hH : LinearSystems.IsHurwitz A₀)
    {A₁ : ℝ → Matrix (Fin n) (Fin n) ℝ} (hA₁ : Continuous A₁) (hP : Periodic A₁ T) (hT : 0 < T) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ →
      LTI.SchurStable (monodromy (fun t => A₀ + ε • A₁ t) T 0) := by
  have hS := (LTI.isHurwitz_iff_schurStable_exp A₀ hT).mp hH
  obtain ⟨k, hk, hlt⟩ := LTI.exists_pow_norm_lt_one _
    ((LTI.schurStable_iff_spectralRadius_lt_one _).mp hS)
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, ‖monodromy (fun t => A₀ + ε • A₁ t) T 0 ^ k‖ < 1 :=
    ((tendsto_monodromy A₀ hA₁ hP hT).pow k).norm.eventually (Iio_mem_nhds hlt)
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₀, hε₀, fun ε hε => schurStable_of_pow_norm_lt_one hk (hball ?_)⟩
  rwa [Real.dist_eq, sub_zero]

@[tmio T, powerlib_foundation] private theorem eventually_exists_norm_gt {A₀ : Matrix X X ℝ}
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ))) (hA₁ : Continuous A₁)
    (hP : Periodic A₁ T) (hT : 0 < T) {r : ℝ} (hr : r < Real.exp (lam.re * T)) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∃ μ ∈ spectrum ℂ ((monodromy (fun t => A₀ + ε • A₁ t) T 0).map
      (algebraMap ℝ ℂ)), r < ‖μ‖ := by
  set z := Complex.exp (lam * T) with hz
  have hzn : ‖z‖ = Real.exp (lam.re * T) := norm_exp_mul_eq lam T
  obtain ⟨v, hv, hAv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hlam
  have hz0 : (Matrix.scalar X z - (NormedSpace.exp (T • A₀)).map (algebraMap ℝ ℂ)).det = 0 := by
    have h := monodromy_const_mulVec_eigen A₀ hT.le 0 hAv
    rw [monodromy_const A₀ hT.le] at h
    have hmem : z ∈ spectrum ℂ ((NormedSpace.exp (T • A₀)).map (algebraMap ℝ ℂ)) :=
      LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, h⟩
    rw [← Matrix.eval_charpoly]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hmem
  have hcont : Continuous fun N : Matrix X X ℝ =>
      (Matrix.scalar X z - N.map (algebraMap ℝ ℂ)).det :=
    (continuous_const.sub (continuous_id.matrix_map (continuous_algebraMap ℝ ℂ))).matrix_det
  have ht := (hcont.tendsto _).comp (tendsto_monodromy A₀ hA₁ hP hT)
  rw [hz0] at ht
  have hpos : 0 < (‖z‖ - r) ^ Fintype.card X := pow_pos (by linarith) _
  filter_upwards [ht.norm.eventually (Iio_mem_nhds (by rwa [norm_zero]))] with ε hε
  exact exists_norm_gt_of_norm_det_lt (by linarith) hε

/-- **An unstable small-signal eigenvalue stays Floquet unstable under small modulation**, in
any dimension. If `A₀` has an eigenvalue with `Re λ > 0`, there is `ε₀ > 0` such that
`ẋ = (A₀ + ε A₁(t)) x` has a Floquet multiplier outside the unit circle for `|ε| < ε₀`
(`det(e^{λT} I − M(ε)) → 0`, `exists_norm_gt_of_norm_det_lt`). -/
@[tmio T, powerlib_foundation] theorem exists_floquetUnstable_of_re_pos {A₀ : Matrix X X ℝ}
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ))) (hre : 0 < lam.re)
    (hA₁ : Continuous A₁) (hP : Periodic A₁ T) (hT : 0 < T) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ → FloquetUnstable (fun t => A₀ + ε • A₁ t) T := by
  have hev := eventually_exists_norm_gt hlam hA₁ hP hT (r := 1)
    (Real.one_lt_exp_iff.mpr (mul_pos hre hT))
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₀, hε₀, fun ε hε => hball ?_⟩
  rwa [Real.dist_eq, sub_zero]

/-- **The small-signal growth rate is the limit of the Floquet growth rate.** Let `α` be the
spectral abscissa of `A₀` (every eigenvalue has `Re λ ≤ α`, one has `Re λ = α`). For a continuous
`T`-periodic `A₁` and every `η > 0` there is `ε₀ > 0` such that for `|ε| < ε₀` the largest Floquet
exponent `(1/T) ln |μ|` of `ẋ = (A₀ + ε A₁(t)) x` lies in `(α − η, α + η)`: some multiplier has
`(1/T) ln |μ| > α − η` and every multiplier has `(1/T) ln |μ| < α + η`. Hence
`(1/T) ln ρ(M(ε)) → α` as `ε → 0`. The upper estimate applies `exists_schurStable_of_isHurwitz`
to the Hurwitz matrix `A₀ − (α + η/2) I` (`transition_sub_smul_one`). -/
@[tmio T, powerlib_foundation] theorem floquet_exponent_tendsto {n : ℕ}
    {A₀ : Matrix (Fin n) (Fin n) ℝ} {α : ℝ}
    (hα : ∀ μ ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ)), μ.re ≤ α)
    (hmax : ∃ lam ∈ spectrum ℂ (A₀.map (algebraMap ℝ ℂ)), lam.re = α)
    {A₁ : ℝ → Matrix (Fin n) (Fin n) ℝ} (hA₁ : Continuous A₁) (hP : Periodic A₁ T) (hT : 0 < T)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ →
      (∃ μ ∈ spectrum ℂ ((monodromy (fun t => A₀ + ε • A₁ t) T 0).map (algebraMap ℝ ℂ)),
          α - η < Real.log ‖μ‖ / T) ∧
        ∀ μ ∈ spectrum ℂ ((monodromy (fun t => A₀ + ε • A₁ t) T 0).map (algebraMap ℝ ℂ)),
          Real.log ‖μ‖ / T < α + η := by
  obtain ⟨lam, hlam, hre⟩ := hmax
  -- lower estimate
  have hlow := eventually_exists_norm_gt hlam hA₁ hP hT (r := Real.exp ((α - η) * T))
    (Real.exp_lt_exp.mpr (by rw [hre]; nlinarith))
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.eventually_nhds_iff.mp hlow
  -- upper estimate through the shifted matrix `A₀ − c I`
  set c := α + η / 2 with hc
  have hB : LinearSystems.IsHurwitz (A₀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    intro μ v hv hBv
    have hAv : A₀.map (algebraMap ℝ ℂ) *ᵥ v = (μ + c) • v := by
      have e : (A₀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).map (algebraMap ℝ ℂ) =
          A₀.map (algebraMap ℝ ℂ) - (c : ℂ) • 1 := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
      rw [e, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hBv
      rw [add_smul, ← hBv]
      abel
    have := hα (μ + c) (LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, hAv⟩)
    simp only [Complex.add_re, Complex.ofReal_re] at this
    show μ.re < -0
    linarith
  obtain ⟨ε₂, hε₂, hS⟩ := exists_schurStable_of_isHurwitz hB hA₁ hP hT
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε => ⟨?_, ?_⟩⟩
  · obtain ⟨μ, hμ, hlt⟩ := hball₁
      (by rw [Real.dist_eq, sub_zero]; exact hε.trans_le (min_le_left _ _))
    refine ⟨μ, hμ, ?_⟩
    rw [lt_div_iff₀ hT]
    have h0 : 0 < Real.exp ((α - η) * T) := Real.exp_pos _
    have := Real.log_lt_log h0 hlt
    rwa [Real.log_exp] at this
  · intro μ hμ
    set Aε : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => A₀ + ε • A₁ t with hAε
    have hAεc : Continuous Aε := by fun_prop
    have hAεP : Periodic Aε T := fun t => by simp only [hAε, hP t]
    obtain ⟨M, hM⟩ := exists_bound_of_periodic hAεc hAεP hT
    have hshift : monodromy (fun t => A₀ - c • (1 : Matrix (Fin n) (Fin n) ℝ) + ε • A₁ t) T 0 =
        Real.exp (-(c * T)) • monodromy Aε T 0 := by
      have h := transition_sub_smul_one hAεc hM c (s := 0) (t := 0 + T) (by linarith)
      simp only [monodromy, hAε] at h ⊢
      rw [show (fun t => A₀ - c • (1 : Matrix (Fin n) (Fin n) ℝ) + ε • A₁ t) =
          fun r => A₀ + ε • A₁ r - c • 1 by funext r; abel, h]
      simp
    have hSε := hS ε (hε.trans_le (min_le_right _ _))
    rw [hshift] at hSε
    obtain ⟨v, hv, hMv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
    have hv' : (Real.exp (-(c * T)) • monodromy Aε T 0).map (algebraMap ℝ ℂ) *ᵥ v =
        ((Real.exp (-(c * T)) : ℂ) * μ) • v := by
      rw [show (Real.exp (-(c * T)) • monodromy Aε T 0).map (algebraMap ℝ ℂ) =
          (Real.exp (-(c * T)) : ℂ) • (monodromy Aε T 0).map (algebraMap ℝ ℂ) by
        ext i j; simp [Matrix.map_apply], Matrix.smul_mulVec, hMv, smul_smul]
    have h1 := hSε _ v hv hv'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
    -- `μ ≠ 0` because the monodromy matrix is invertible (Liouville)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      have hdet : (monodromy Aε T 0).det ≠ 0 := by
        rw [det_monodromy hAεc hAεP 0]; exact (Real.exp_pos _).ne'
      have hunit : IsUnit ((monodromy Aε T 0).map (algebraMap ℝ ℂ)) := by
        rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact (isUnit_iff_ne_zero.mpr hdet).map _
      exact (spectrum.zero_mem_iff ℂ).mp hμ hunit
    have hlt : ‖μ‖ < Real.exp (c * T) := by
      have h2 : Real.exp (-(c * T)) * ‖μ‖ * Real.exp (c * T) < 1 * Real.exp (c * T) :=
        mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      rwa [mul_comm (Real.exp _) ‖μ‖, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        mul_one, one_mul] at h2
    rw [div_lt_iff₀ hT]
    have := Real.log_lt_log (norm_pos_iff.mpr hμ0) hlt
    rw [Real.log_exp] at this
    nlinarith

end powerlib.Periodic
