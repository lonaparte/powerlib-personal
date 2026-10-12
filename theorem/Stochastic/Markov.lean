import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Moments.Variance

/-! # Markov processes: Chapman–Kolmogorov, invariance, the Gaussian (OU) semigroup

Source: work-sync `theory/T-markov-processes.md` §1.1 (Markov property, transition kernel
`K_{s,t}`), §1.2 (Chapman–Kolmogorov `K_{t+s} = K_t K_s`, "Markov ⇔ semigroup"), §1.3
(conditional-expectation form `E[f(X_t) | 𝓕_s] = P_{t−s} f(X_s)`), §1.6 (discrete chains,
Brownian motion, OU process); `theory/T-sde-systems.md` §1.8.1 (OU transition law).

Foundation (probability), not an engineering result.

Category C wrappers (Mathlib declaration in brackets): `kernel_comp_assoc`
[`ProbabilityTheory.Kernel.comp_assoc`], `invariant_comp` [`Kernel.Invariant.comp`],
`ionescuTulcea_next` [`Kernel.map_traj_succ_self`: the trajectory law built by the
Ionescu–Tulcea theorem has the prescribed one-step kernel], `ionescuTulcea_marginal`
[`Kernel.traj_map_frestrictLe`].  The Brownian weak Markov property is
`theorem/Stochastic/Brownian.lean` (`brownian_weakMarkov`).

Category B.
* `kpow`, `kpow_add`: discrete-time Chapman–Kolmogorov `K^{m+n} = K^m ∘ K^n` for the iterates of
  a kernel; `kpow_invariant`: an invariant measure is invariant for every iterate.
* `chapmanKolmogorov_ae`: the Markov property in conditional-expectation form with transition
  kernels `K s t` (any time set; written out as the hypothesis: for `s ≤ t` and bounded measurable
  `g`, `E[g(X_t) | 𝓕_s] = ∫ g dK_{s,t}(X_s)` a.s.) implies
  `K_{s,u}(X_s, A) = ∫ K_{t,u}(y, A) K_{s,t}(X_s, dy)` **almost surely**, i.e. only for
  `P_{X_s}`-almost every starting point.
* `gaussian_bind`: `∫ N(c y, v) N(m, w)(dy) = N(c m, c² w + v)`; `ou_chapmanKolmogorov`: the OU
  transition kernels `N(e^{−θt} x, σ²(1 − e^{−2θt})/(2θ))` form a semigroup (OU is Markov with
  these Gaussian kernels).
* `ou_increment_not_indep`: for the exact OU step `X' = aX + Z` (`a = e^{−θh} ≠ 1`, `X ~ N(0, v₀)`,
  `v₀ > 0`, `Z` independent), the increment `X' − X` is **not** independent of `X` — OU does not
  have independent increments (unlike Brownian motion).

Correction (§1.2).  "Markov ⇔ semigroup relation" is too strong: the Markov property only gives
Chapman–Kolmogorov `P_{X_s}`-a.e. (`chapmanKolmogorov_ae`), and the converse direction
(semigroup ⇒ Markov) is false: it is refuted by Feller's three-step example
`semigroup_not_markov` in `theorem/Stochastic/MarkovForms.lean` (transition kernels forming a
Chapman–Kolmogorov semigroup, process not Markov).

The equivalence of the event form and the conditional-expectation form of the Markov property
(bounded measurable test functions) is `theorem/Stochastic/MarkovForms.lean`
(`markovEvent_iff_markovCondExp`).
-/

noncomputable section
namespace powerlib.Stochastic.Markov

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal

/-! ## Category C: kernels -/

section Kernels

variable {α : Type*} {mα : MeasurableSpace α}

/-- Composition of kernels is associative (Mathlib `ProbabilityTheory.Kernel.comp_assoc`). -/
@[powerlib_foundation] theorem kernel_comp_assoc {β γ δ : Type*} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ)
    (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ) :=
  Kernel.comp_assoc ξ η κ

/-- Invariance is preserved by composition (Mathlib `Kernel.Invariant.comp`). -/
@[powerlib_foundation] theorem invariant_comp {κ η : Kernel α α} {μ : Measure α}
    (hκ : κ.Invariant μ) (hη : η.Invariant μ) : (κ ∘ₖ η).Invariant μ :=
  hκ.comp hη

/-- `n`-step kernel `K^n` (iterated composition, `K^0 = id`). -/
def kpow (κ : Kernel α α) : ℕ → Kernel α α
  | 0 => Kernel.id
  | n + 1 => κ ∘ₖ kpow κ n

/-- **Discrete Chapman–Kolmogorov**: `K^{m+n} = K^m ∘ K^n`. -/
@[powerlib_foundation] theorem kpow_add (κ : Kernel α α) (m n : ℕ) :
    kpow κ (m + n) = kpow κ m ∘ₖ kpow κ n := by
  induction m with
  | zero => simp [kpow, Kernel.id_comp]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by ring, kpow, ih, kpow, kernel_comp_assoc]

/-- An invariant measure is invariant for every iterate. -/
@[powerlib_foundation] theorem kpow_invariant {κ : Kernel α α} {μ : Measure α}
    (h : κ.Invariant μ) (n : ℕ) : (kpow κ n).Invariant μ := by
  induction n with
  | zero => simp [kpow, Kernel.Invariant]
  | succ n ih => exact h.comp ih

end Kernels

section IonescuTulcea

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]

/-- **Discrete-time chains (Ionescu–Tulcea)**: the trajectory kernel `traj κ a` has the
prescribed one-step transition (Mathlib `Kernel.map_traj_succ_self`). -/
@[powerlib_foundation] theorem ionescuTulcea_next (a : ℕ) :
    (Kernel.traj κ a).map (fun x => x (a + 1)) = κ a :=
  Kernel.map_traj_succ_self

/-- Its finite-dimensional marginals are the finite compositions (Mathlib
`Kernel.traj_map_frestrictLe`). -/
@[powerlib_foundation] theorem ionescuTulcea_marginal (a b : ℕ) :
    (Kernel.traj κ a).map (Preorder.frestrictLe b) = Kernel.partialTraj κ a b :=
  Kernel.traj_map_frestrictLe a b

end IonescuTulcea

/-! ## Markov property and Chapman–Kolmogorov almost surely -/

section MarkovProperty

variable {Ω E ι : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- **Chapman–Kolmogorov from the Markov property (§1.2), almost surely**. The hypothesis `h` is
the **Markov property with transition kernels** `K s t` (conditional-expectation form,
T-markov §1.3): for `s ≤ t` and bounded measurable `g`, `E[g(X_t) | 𝓕_s] = ∫ g dK_{s,t}(X_s)`
a.s. Then for `s ≤ t ≤ u` and measurable `A`, `K_{s,u}(X_s, A) = (K_{t,u} ∘ K_{s,t})(X_s, A)` for
`P`-a.e. `ω`. -/
@[powerlib_foundation] theorem chapmanKolmogorov_ae {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {K : ι → ι → Kernel E E}
    [∀ s t, IsMarkovKernel (K s t)]
    (h : ∀ s t, s ≤ t → ∀ g : E → ℝ, Measurable g → (∃ C, ∀ y, |g y| ≤ C) →
      P[fun ω => g (X t ω) | 𝓕 s] =ᵐ[P] fun ω => ∫ y, g y ∂(K s t (X s ω)))
    {s t u : ι} (hst : s ≤ t) (htu : t ≤ u) {A : Set E} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂P, K s u (X s ω) A = (K t u ∘ₖ K s t) (X s ω) A := by
  set g : E → ℝ := A.indicator fun _ => 1 with hg
  have hgm : Measurable g := measurable_const.indicator hA
  have hgb : ∃ C, ∀ y, |g y| ≤ C := ⟨1, fun y => by
    simp only [hg, Set.indicator]; split_ifs <;> simp⟩
  set φ : E → ℝ := fun y => (K t u y).real A with hφ
  have hφm : Measurable φ := (Kernel.measurable_coe _ hA).ennreal_toReal
  have hφb : ∃ C, ∀ y, |φ y| ≤ C := ⟨1, fun y => by
    simp only [hφ, measureReal_def]
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩
  have hint_g : ∀ y : E, ∫ z, g z ∂(K t u y) = φ y := by
    intro y; simp [hg, hφ, integral_indicator hA, measureReal_def]
  have hint_g' : ∀ y : E, ∫ z, g z ∂(K s u y) = (K s u y).real A := by
    intro y; simp [hg, integral_indicator hA, measureReal_def]
  have h1 := h s u (hst.trans htu) g hgm hgb
  have h2 := h t u htu g hgm hgb
  have h3 := h s t hst φ hφm hφb
  have htower : P[P[fun ω => g (X u ω) | 𝓕 t] | 𝓕 s] =ᵐ[P] P[fun ω => g (X u ω) | 𝓕 s] :=
    condExp_condExp_of_le (𝓕.mono hst) (𝓕.le t)
  have hcongr : P[P[fun ω => g (X u ω) | 𝓕 t] | 𝓕 s] =ᵐ[P] P[fun ω => φ (X t ω) | 𝓕 s] := by
    refine condExp_congr_ae ?_
    filter_upwards [h2] with ω hω
    rw [hω, hint_g]
  filter_upwards [h1, h3, htower, hcongr] with ω e1 e3 et ec
  -- both sides as real numbers
  have hreal : (K s u (X s ω)).real A = ∫ y, φ y ∂(K s t (X s ω)) := by
    rw [← hint_g', ← e1, ← et, ec, e3]
  rw [Kernel.comp_apply' _ _ _ hA]
  have hfin : ∀ y, K t u y A < ∞ := fun y => measure_lt_top _ _
  have hlhs : ∫ y, φ y ∂(K s t (X s ω)) = (∫⁻ y, K t u y A ∂(K s t (X s ω))).toReal := by
    simp only [hφ, measureReal_def]
    exact integral_toReal (Kernel.measurable_coe _ hA).aemeasurable (Eventually.of_forall hfin)
  rw [hlhs, measureReal_def] at hreal
  have hne1 : K s u (X s ω) A ≠ ∞ := measure_ne_top _ _
  have hne2 : ∫⁻ y, K t u y A ∂(K s t (X s ω)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂(K s t (X s ω))) (by simp) ?_
    exact lintegral_mono fun y => prob_le_one
  exact (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp hreal

end MarkovProperty

/-! ## Gaussian kernels and the OU semigroup -/

/-- **Gaussian location mixture**: `∫ N(c y, v) N(m, w)(dy) = N(c m, c² w + v)`. -/
@[powerlib_foundation] theorem gaussian_bind (m c : ℝ) (w v : ℝ≥0) :
    (gaussianReal m w).bind (fun y => gaussianReal (c * y) v) =
      gaussianReal (c * m) (.mk (c ^ 2) (sq_nonneg _) * w + v) := by
  have hmeas : Measurable fun y : ℝ => gaussianReal (c * y) v :=
    measurable_gaussianReal.comp ((measurable_id.const_mul c).prodMk measurable_const)
  rw [← add_zero (c * m), ← gaussianReal_conv_gaussianReal, ← gaussianReal_map_const_mul]
  ext S hS
  rw [Measure.bind_apply hS hmeas.aemeasurable]
  have hind : Measurable (S.indicator (1 : ℝ → ℝ≥0∞)) := measurable_const.indicator hS
  have hF : Measurable fun x : ℝ => ∫⁻ y, S.indicator 1 (x + y) ∂gaussianReal 0 v :=
    (hind.comp measurable_add).lintegral_prod_right'
  rw [← lintegral_indicator_one hS, Measure.lintegral_conv hind,
    lintegral_map hF (by fun_prop)]
  refine lintegral_congr fun y => ?_
  rw [← lintegral_indicator_one hS]
  have e : gaussianReal (c * y) v = (gaussianReal 0 v).map (fun z => z + c * y) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [e, lintegral_map hind (by fun_prop)]
  congr 1; funext z; rw [add_comm]

/-- OU transition variance `v(t) = σ²(1 − e^{−2θt})/(2θ)` (as `ℝ≥0`). -/
def ouVar (θ σ : ℝ) (t : ℝ≥0) : ℝ≥0 := (σ ^ 2 * (1 - exp (-2 * θ * t)) / (2 * θ)).toNNReal

/-- OU transition law from `x` over time `t`: `N(e^{−θt} x, v(t))`. -/
def ouLaw (θ σ : ℝ) (t : ℝ≥0) (x : ℝ) : Measure ℝ := gaussianReal (exp (-θ * t) * x) (ouVar θ σ t)

@[powerlib_foundation] theorem ouVar_coe {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) (t : ℝ≥0) :
    (ouVar θ σ t : ℝ) = σ ^ 2 * (1 - exp (-2 * θ * t)) / (2 * θ) := by
  rw [ouVar, Real.coe_toNNReal]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (sq_nonneg _)
  rw [sub_nonneg, exp_le_one_iff]
  have : (0 : ℝ) ≤ t := t.2
  nlinarith

/-- Variance composition `e^{−2θt} v(s) + v(t) = v(s + t)`. -/
@[powerlib_foundation] theorem ouVar_add {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) (s t : ℝ≥0) :
    .mk (exp (-θ * t) ^ 2) (sq_nonneg _) * ouVar θ σ s + ouVar θ σ t = ouVar θ σ (s + t) := by
  apply NNReal.eq
  push_cast
  rw [ouVar_coe hθ, ouVar_coe hθ, ouVar_coe hθ, NNReal.coe_add]
  have e1 : exp (-θ * t) ^ 2 = exp (-2 * θ * t) := by rw [← exp_nat_mul]; congr 1; push_cast; ring
  have e2 : exp (-2 * θ * ((s : ℝ) + t)) = exp (-2 * θ * t) * exp (-2 * θ * s) := by
    rw [← exp_add]; congr 1; ring
  rw [e1, e2]
  field_simp
  ring

/-- **OU Chapman–Kolmogorov**: the Gaussian transition laws form a semigroup,
`∫ K_t(y, ·) K_s(x, dy) = K_{s+t}(x, ·)`. -/
@[powerlib_foundation] theorem ou_chapmanKolmogorov {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) (s t : ℝ≥0)
    (x : ℝ) : (ouLaw θ σ s x).bind (ouLaw θ σ t) = ouLaw θ σ (s + t) x := by
  unfold ouLaw
  rw [gaussian_bind, ouVar_add hθ]
  congr 1
  rw [← mul_assoc, ← exp_add]; congr 2; push_cast; ring

/-! ## OU increments are not independent -/

/-- **OU increments are not independent of the current state**: if `X ~ N(0, v₀)` (`v₀ ≠ 0`),
`Z` is independent of `X` and square integrable, and `X' = a X + Z` with `a ≠ 1` (the exact OU step
with `a = e^{−θh}`), then `X' − X` is not independent of `X`. -/
@[powerlib_foundation] theorem ou_increment_not_indep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} {v₀ : ℝ≥0} (hv : v₀ ≠ 0)
    (hX : HasLaw X (gaussianReal 0 v₀) P) (hZ : MemLp Z 2 P) (hXZ : IndepFun X Z P) {a : ℝ}
    (ha : a ≠ 1) : ¬ IndepFun X (fun ω => a * X ω + Z ω - X ω) P := by
  intro hind
  have hX2 : MemLp X 2 P := hX.memLp (memLp_id_gaussianReal 2)
  have hinc2 : MemLp (fun ω => a * X ω + Z ω - X ω) 2 P := ((hX2.const_mul a).add hZ).sub hX2
  have h0 := hind.covariance_eq_zero hX2 hinc2
  have hcov : cov[X, fun ω => a * X ω + Z ω - X ω; P] = (a - 1) * v₀ := by
    have e : (fun ω => a * X ω + Z ω - X ω) = fun ω => (a - 1) * X ω + Z ω := by
      funext ω; ring
    rw [e, show (fun ω => (a - 1) * X ω + Z ω) = (fun ω => (a - 1) * X ω) + Z from rfl,
      covariance_add_right hX2 (hX2.const_mul _) hZ, covariance_const_mul_right,
      covariance_self hX2.aemeasurable, hXZ.covariance_eq_zero hX2 hZ, hX.variance_eq,
      variance_id_gaussianReal]
    ring
  rw [hcov] at h0
  have : (v₀ : ℝ) ≠ 0 := by exact_mod_cast hv
  have : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  exact (mul_ne_zero ‹a - 1 ≠ 0› ‹(v₀ : ℝ) ≠ 0›) h0

end powerlib.Stochastic.Markov
