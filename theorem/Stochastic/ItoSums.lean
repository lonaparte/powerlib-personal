import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.QuadVariation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Adapted sums of Brownian increments: the isometry of martingale transforms

The second moments of the discrete stochastic integrals `∑ aᵢ ξᵢ`: when each coefficient `aᵢ` is
known at time `tᵢ`, bounded, and each noise `ξᵢ` is centred, square integrable and independent of
the past at `tᵢ`, the cross terms vanish and `E(∑ aᵢ ξᵢ)² = ∑ E aᵢ² · E ξᵢ²`. For Brownian
increments `ξᵢ = ΔBᵢ` this is the isometry `E(∑ aᵢ ΔBᵢ)² = ∑ E aᵢ² Δtᵢ` behind the Itô integral;
for `ξᵢ = ΔBᵢ² − Δtᵢ` it is the weighted quadratic variation `E(∑ aᵢ (ΔBᵢ² − Δtᵢ))² =
2 ∑ E aᵢ² Δtᵢ²`. Two convergence-in-probability lemmas complete the toolkit of the Itô and Dynkin
formulas (`theorem/Stochastic/ItoFormula.lean`).

Scope.
* Probability theory, not an engineering result. A discrete filtration `𝓕 : ℕ → MeasurableSpace Ω`
  (monotone, below the ambient σ-algebra); Brownian motion is Mathlib's `IsPreBrownianReal`
  with its natural filtration `Filtration.natural B hm` (each `B t` strongly measurable, an
  explicit hypothesis as in `theorem/Stochastic/Brownian.lean`).
* Bounded coefficients only (`|aᵢ| ≤ C`), which is what the applications use.

Source: I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed. (1991),
§3.2 (the isometry for simple integrands, Lemma 3.2.4 / eq. (3.2.12)) and §3.3 (proof of Itô's
formula: the weighted quadratic variation, eq. (3.3.7)); work-sync theory/T-sde-systems.md §1.2
(`[W]_t = t`).

Results.
* `integral_sq_sum_mul` (**isometry of martingale transforms**): `E(∑_{i<n} aᵢ ξᵢ)² =
  ∑ E aᵢ² E ξᵢ²`; `memLp_sum_mul`, `measurable_sum_mul` (the sums are square integrable and known
  at time `n`).
* `indep_incr_natural`: the increment `B_t − B_s` is independent of `𝓕_s` (natural filtration);
  `indep_comp_incr_natural`, `measurable_incr_natural`.
* `integral_sq_sum_mul_incr` (`E(∑ aᵢ ΔBᵢ)² = ∑ E aᵢ² Δtᵢ`), `integral_sum_mul_incr`
  (`E ∑ aᵢ ΔBᵢ = 0`), `integral_sq_sum_mul_incr_le` (`≤ C² (t_n − t_0)`);
  `integral_sq_sum_mul_qv` (`E(∑ aᵢ (ΔBᵢ² − Δtᵢ))² = 2 ∑ E aᵢ² Δtᵢ²`),
  `integral_sq_sum_mul_qv_le` (`≤ 2 C² δ (t_n − t_0)` when every step is `≤ δ`).
* `integral_sq_le_of_abs_le`, `memLp_mul_of_bound`, `indepFun_of_le` (helpers).
* `tendsto_integral_of_tendstoInMeasure` (convergence in probability with bounded second moments
  gives convergence of the means), `tendstoInMeasure_of_div_one_add` (`|Yₘ|/(1 + Vₘ) → 0`
  pointwise, `Vₘ ≥ 0`, `E Vₘ ≤ C`: `Yₘ → 0` in probability), `tendstoInMeasure_of_integral_sq`
  (`E Xₘ² → 0` gives `Xₘ → 0` in probability), `tendstoInMeasure_add_zero`,
  `tendstoInMeasure_of_sub_of_tendsto`.
-/

noncomputable section
namespace powerlib.Stochastic.Ito

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The isometry of martingale transforms -/

/-- The partial sums `∑_{i<n} aᵢ ξᵢ` are known at time `n`. -/
@[tmio T, powerlib_foundation] theorem measurable_sum_mul {𝓕 : ℕ → MeasurableSpace Ω}
    (hmono : Monotone 𝓕) {a ξ : ℕ → Ω → ℝ} (ha : ∀ i, Measurable[𝓕 i] (a i))
    (hξ : ∀ i, Measurable[𝓕 (i + 1)] (ξ i)) (n : ℕ) :
    Measurable[𝓕 n] fun ω => ∑ i ∈ range n, a i ω * ξ i ω := by
  refine Finset.measurable_fun_sum _ fun i hi => ?_
  have hi' : i + 1 ≤ n := mem_range.mp hi
  exact ((ha i).mono (hmono (by omega)) le_rfl).mul ((hξ i).mono (hmono hi') le_rfl)

/-- A bounded coefficient times a square-integrable noise is square integrable. -/
@[tmio T, powerlib_foundation] theorem memLp_mul_of_bound {a ξ : Ω → ℝ}
    {C : ℝ} (ha : AEStronglyMeasurable a P) (haC : ∀ ω, |a ω| ≤ C) (hξ : MemLp ξ 2 P) :
    MemLp (fun ω => a ω * ξ ω) 2 P := by
  refine (hξ.norm.const_mul C).mono' (ha.mul hξ.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (haC ω) (abs_nonneg _)

/-- The partial sums are square integrable. -/
@[tmio T, powerlib_foundation] theorem memLp_sum_mul {𝓕 : ℕ → MeasurableSpace Ω}
    (hle : ∀ i, 𝓕 i ≤ mΩ) {a ξ : ℕ → Ω → ℝ} {C : ℝ} (ha : ∀ i, Measurable[𝓕 i] (a i))
    (haC : ∀ i ω, |a i ω| ≤ C) (hξ2 : ∀ i, MemLp (ξ i) 2 P) (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ range n, a i ω * ξ i ω) 2 P :=
  memLp_finsetSum _ fun i _ =>
    memLp_mul_of_bound ((ha i).mono (hle i) le_rfl).aestronglyMeasurable (haC i) (hξ2 i)

/-- Independence of a past-measurable variable and the noise. -/
@[tmio T, powerlib_foundation] theorem indepFun_of_le {m : MeasurableSpace Ω} {Z ξ : Ω → ℝ}
    (hZ : Measurable[m] Z) (hind : Indep (MeasurableSpace.comap ξ inferInstance) m P) :
    IndepFun Z ξ P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left hind.symm hZ.comap_le

/-- **Isometry of martingale transforms**: if `aᵢ` is `𝓕ᵢ`-measurable and bounded, `ξᵢ` is
`𝓕ᵢ₊₁`-measurable, independent of `𝓕ᵢ`, centred and square integrable, then
`E(∑_{i<n} aᵢ ξᵢ)² = ∑_{i<n} E aᵢ² · E ξᵢ²`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_sum_mul [IsProbabilityMeasure P]
    {𝓕 : ℕ → MeasurableSpace Ω} (hmono : Monotone 𝓕) (hle : ∀ i, 𝓕 i ≤ mΩ)
    {a ξ : ℕ → Ω → ℝ} {C : ℝ} (ha : ∀ i, Measurable[𝓕 i] (a i)) (haC : ∀ i ω, |a i ω| ≤ C)
    (hξ : ∀ i, Measurable[𝓕 (i + 1)] (ξ i))
    (hind : ∀ i, Indep (MeasurableSpace.comap (ξ i) inferInstance) (𝓕 i) P)
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0) (n : ℕ) :
    ∫ ω, (∑ i ∈ range n, a i ω * ξ i ω) ^ 2 ∂P =
      ∑ i ∈ range n, (∫ ω, a i ω ^ 2 ∂P) * ∫ ω, ξ i ω ^ 2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    set S : Ω → ℝ := fun ω => ∑ i ∈ range n, a i ω * ξ i ω with hSdef
    have hSm : Measurable[𝓕 n] S := measurable_sum_mul hmono ha hξ n
    have hS2 : MemLp S 2 P := memLp_sum_mul hle ha haC hξ2 n
    have ham : Measurable (a n) := (ha n).mono (hle n) le_rfl
    have hξm : Measurable (ξ n) := (hξ n).mono (hle (n + 1)) le_rfl
    have hSa2 : MemLp (fun ω => a n ω * S ω) 2 P :=
      memLp_mul_of_bound ham.aestronglyMeasurable (haC n) hS2
    have h1 : Integrable (fun ω => S ω ^ 2) P := hS2.integrable_sq
    have h2 : Integrable (fun ω => a n ω * S ω * ξ n ω) P :=
      hSa2.integrable_mul (hξ2 n)
    have hax2 : MemLp (fun ω => a n ω * ξ n ω) 2 P :=
      memLp_mul_of_bound ham.aestronglyMeasurable (haC n) (hξ2 n)
    have h3 : Integrable (fun ω => (a n ω * ξ n ω) ^ 2) P := hax2.integrable_sq
    have hindSa : IndepFun (fun ω => a n ω * S ω) (ξ n) P :=
      indepFun_of_le ((ha n).mul hSm) (hind n)
    have hcross : ∫ ω, a n ω * S ω * ξ n ω ∂P = 0 := by
      have := hindSa.integral_fun_mul_eq_mul_integral
        hSa2.aestronglyMeasurable hξm.aestronglyMeasurable
      rw [this, hξ0 n, mul_zero]
    have hindsq : IndepFun (fun ω => a n ω ^ 2) (fun ω => ξ n ω ^ 2) P :=
      (indepFun_of_le (ha n) (hind n)).comp (measurable_id.pow_const 2)
        (measurable_id.pow_const 2)
    have hdiag : ∫ ω, (a n ω * ξ n ω) ^ 2 ∂P = (∫ ω, a n ω ^ 2 ∂P) * ∫ ω, ξ n ω ^ 2 ∂P := by
      have := hindsq.integral_fun_mul_eq_mul_integral
        (ham.pow_const 2).aestronglyMeasurable (hξm.pow_const 2).aestronglyMeasurable
      rw [← this]
      congr 1; funext ω; ring
    have e : (fun ω => (∑ i ∈ range (n + 1), a i ω * ξ i ω) ^ 2) = fun ω =>
        S ω ^ 2 + 2 * (a n ω * S ω * ξ n ω) + (a n ω * ξ n ω) ^ 2 := by
      funext ω; rw [sum_range_succ]; ring
    have h12 : Integrable (fun ω => S ω ^ 2 + 2 * (a n ω * S ω * ξ n ω)) P :=
      h1.add (h2.const_mul 2)
    rw [e, integral_add h12 h3, integral_add h1 (h2.const_mul 2),
      integral_const_mul, hcross, hdiag, sum_range_succ, ← ih]
    ring

/-- `E a² ≤ C²` for `|a| ≤ C` (probability measure). -/
@[tmio T, powerlib_foundation] theorem integral_sq_le_of_abs_le [IsProbabilityMeasure P]
    {a : Ω → ℝ} {C : ℝ} (haC : ∀ ω, |a ω| ≤ C) : ∫ ω, a ω ^ 2 ∂P ≤ C ^ 2 := by
  have h : ∀ ω, a ω ^ 2 ≤ C ^ 2 := fun ω => by
    have := pow_le_pow_left₀ (abs_nonneg _) (haC ω) 2
    rwa [sq_abs] at this
  calc ∫ ω, a ω ^ 2 ∂P ≤ ∫ _, C ^ 2 ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (integrable_const _)
          (ae_of_all _ h)
    _ = C ^ 2 := by simp

/-! ## Brownian increments and the natural filtration -/

variable {B : ℝ≥0 → Ω → ℝ}

open powerlib.Stochastic.BM (incr)
open powerlib.Stochastic.QV (step)

/-- **The increment `B_t − B_s` is independent of the past `𝓕_s`** (natural filtration). -/
@[tmio T, powerlib_foundation] theorem indep_incr_natural (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance)
      (Filtration.natural B hm s) P := by
  have hind := hB.indepFun_shift s
  rw [IndepFun_iff_Indep] at hind
  rw [Filtration.natural_eq_comap B hm s]
  exact indep_of_indep_of_le_left hind (BM.increment_measurable_shift hst).comap_le

/-- A function of the increment is independent of the past. -/
@[tmio T, powerlib_foundation] theorem indep_comp_incr_natural (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {g : ℝ → ℝ}
    (hg : Measurable g) :
    Indep (MeasurableSpace.comap (fun ω => g (B t ω - B s ω)) inferInstance)
      (Filtration.natural B hm s) P := by
  refine indep_of_indep_of_le_left (indep_incr_natural hB hm hst) ?_
  have : (fun ω => g (B t ω - B s ω)) = g ∘ fun ω => B t ω - B s ω := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

/-- The increment is known at the later time. -/
@[tmio T, powerlib_foundation] theorem measurable_incr_natural
    (hm : ∀ t, StronglyMeasurable (B t)) {s t u : ℝ≥0} (hs : s ≤ u) (ht : t ≤ u) :
    Measurable[Filtration.natural B hm u] fun ω => B t ω - B s ω := by
  have ad := Filtration.stronglyAdapted_natural hm
  exact ((ad t).mono ((Filtration.natural B hm).mono ht)).measurable.sub
    ((ad s).mono ((Filtration.natural B hm).mono hs)).measurable

variable [IsProbabilityMeasure P]

/-- **Isometry for adapted sums of Brownian increments**: for a monotone time sequence `t` and
coefficients `aᵢ` bounded and known at `tᵢ`, `E(∑_{i<n} aᵢ ΔBᵢ)² = ∑ E aᵢ² Δtᵢ`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_sum_mul_incr (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {t : ℕ → ℝ≥0} (ht : Monotone t) {a : ℕ → Ω → ℝ}
    {C : ℝ} (ha : ∀ i, Measurable[Filtration.natural B hm (t i)] (a i))
    (haC : ∀ i ω, |a i ω| ≤ C) (n : ℕ) :
    ∫ ω, (∑ i ∈ range n, a i ω * incr B t i ω) ^ 2 ∂P =
      ∑ i ∈ range n, (∫ ω, a i ω ^ 2 ∂P) * step t i := by
  have := integral_sq_sum_mul (𝓕 := fun i => Filtration.natural B hm (t i))
    (fun i j hij => (Filtration.natural B hm).mono (ht hij))
    (fun i => (Filtration.natural B hm).le (t i)) ha haC
    (fun i => measurable_incr_natural hm (ht (Nat.le_succ i)) le_rfl)
    (fun i => indep_incr_natural hB hm (ht (Nat.le_succ i)))
    (fun i => (QV.incr_hasLaw hB ht i).memLp (memLp_id_gaussianReal 2))
    (fun i => by
      have := (QV.incr_hasLaw hB ht i).integral_eq
      simp only [integral_id_gaussianReal] at this
      exact this) n
  refine this.trans (sum_congr rfl fun i _ => ?_)
  rw [← QV.integral_incr_sq hB ht i]
  rfl

/-- `E ∑ aᵢ ΔBᵢ = 0`. -/
@[tmio T, powerlib_foundation] theorem integral_sum_mul_incr (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {t : ℕ → ℝ≥0} (ht : Monotone t) {a : ℕ → Ω → ℝ}
    {C : ℝ} (ha : ∀ i, Measurable[Filtration.natural B hm (t i)] (a i))
    (haC : ∀ i ω, |a i ω| ≤ C) (n : ℕ) :
    ∫ ω, ∑ i ∈ range n, a i ω * incr B t i ω ∂P = 0 := by
  have hint : ∀ i, Integrable (fun ω => a i ω * incr B t i ω) P := fun i =>
    (memLp_mul_of_bound (((ha i).mono ((Filtration.natural B hm).le _) le_rfl).aestronglyMeasurable)
      (haC i) ((QV.incr_hasLaw hB ht i).memLp (memLp_id_gaussianReal 2))).integrable one_le_two
  rw [integral_finsetSum _ fun i _ => hint i]
  refine sum_eq_zero fun i _ => ?_
  have hind : IndepFun (a i) (incr B t i) P :=
    indepFun_of_le (ha i) (indep_incr_natural hB hm (ht (Nat.le_succ i)))
  rw [hind.integral_fun_mul_eq_mul_integral
    ((ha i).mono ((Filtration.natural B hm).le _) le_rfl).aestronglyMeasurable
    (QV.incr_hasLaw hB ht i).aemeasurable.aestronglyMeasurable]
  have := (QV.incr_hasLaw hB ht i).integral_eq
  simp only [integral_id_gaussianReal] at this
  rw [this, mul_zero]

/-- `E(∑ aᵢ ΔBᵢ)² ≤ C² (t_n − t_0)` for `|aᵢ| ≤ C`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_sum_mul_incr_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {t : ℕ → ℝ≥0} (ht : Monotone t) {a : ℕ → Ω → ℝ}
    {C : ℝ} (ha : ∀ i, Measurable[Filtration.natural B hm (t i)] (a i))
    (haC : ∀ i ω, |a i ω| ≤ C) (n : ℕ) :
    ∫ ω, (∑ i ∈ range n, a i ω * incr B t i ω) ^ 2 ∂P ≤ C ^ 2 * ((t n : ℝ) - t 0) := by
  rw [integral_sq_sum_mul_incr hB hm ht ha haC n, ← QV.sum_step t n, mul_sum]
  refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (QV.step_nonneg ht i)
  exact integral_sq_le_of_abs_le (haC i)

/-- **Weighted quadratic variation**: for coefficients `aᵢ` bounded and known at `tᵢ`,
`E(∑_{i<n} aᵢ (ΔBᵢ² − Δtᵢ))² = 2 ∑ E aᵢ² Δtᵢ²`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_sum_mul_qv (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {t : ℕ → ℝ≥0} (ht : Monotone t) {a : ℕ → Ω → ℝ}
    {C : ℝ} (ha : ∀ i, Measurable[Filtration.natural B hm (t i)] (a i))
    (haC : ∀ i ω, |a i ω| ≤ C) (n : ℕ) :
    ∫ ω, (∑ i ∈ range n, a i ω * (incr B t i ω ^ 2 - step t i)) ^ 2 ∂P =
      ∑ i ∈ range n, (∫ ω, a i ω ^ 2 ∂P) * (2 * step t i ^ 2) := by
  have hlaw := QV.incr_hasLaw hB ht
  have := integral_sq_sum_mul (𝓕 := fun i => Filtration.natural B hm (t i))
    (ξ := fun i ω => incr B t i ω ^ 2 - step t i)
    (fun i j hij => (Filtration.natural B hm).mono (ht hij))
    (fun i => (Filtration.natural B hm).le (t i)) ha haC
    (fun i => ((measurable_incr_natural hm (ht (Nat.le_succ i)) le_rfl).pow_const 2).sub_const _)
    (fun i => indep_comp_incr_natural hB hm (ht (Nat.le_succ i))
      ((measurable_id.pow_const 2).sub_const (step t i)))
    (fun i => (QV.memLp_sq_of_hasLaw (hlaw i)).sub (memLp_const _))
    (fun i => by
      rw [integral_sub ((QV.memLp_sq_of_hasLaw (hlaw i)).integrable one_le_two)
        (integrable_const _), QV.integral_incr_sq hB ht i]
      simp) n
  refine this.trans (sum_congr rfl fun i _ => ?_)
  congr 1
  have hv := QV.variance_sq_of_hasLaw_gaussian (hlaw i)
  rw [variance_eq_integral ((hlaw i).aemeasurable.pow_const 2), QV.integral_incr_sq hB ht i,
    QV.coe_step ht] at hv
  exact hv

/-- `E(∑ aᵢ (ΔBᵢ² − Δtᵢ))² ≤ 2 C² δ (t_n − t_0)` when every step is `≤ δ`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_sum_mul_qv_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {t : ℕ → ℝ≥0} (ht : Monotone t) {a : ℕ → Ω → ℝ}
    {C δ : ℝ} (ha : ∀ i, Measurable[Filtration.natural B hm (t i)] (a i))
    (haC : ∀ i ω, |a i ω| ≤ C) (n : ℕ) (hδ : ∀ i < n, step t i ≤ δ) :
    ∫ ω, (∑ i ∈ range n, a i ω * (incr B t i ω ^ 2 - step t i)) ^ 2 ∂P ≤
      2 * C ^ 2 * δ * ((t n : ℝ) - t 0) := by
  rw [integral_sq_sum_mul_qv hB hm ht ha haC n, ← QV.sum_step t n, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have h0 := QV.step_nonneg ht i
  have h1 := hδ i (mem_range.mp hi)
  have h2 := integral_sq_le_of_abs_le (P := P) (haC i)
  have h3 : 0 ≤ ∫ ω, a i ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have h4 : step t i ^ 2 ≤ δ * step t i := by nlinarith
  calc (∫ ω, a i ω ^ 2 ∂P) * (2 * step t i ^ 2) ≤ C ^ 2 * (2 * (δ * step t i)) := by
        apply mul_le_mul h2 (by linarith) (by positivity) (by nlinarith)
    _ = _ := by ring

/-! ## Convergence in probability -/

/-- **Chebyshev**: `E Xₘ² → 0` gives `Xₘ → 0` in probability. -/
@[tmio T, powerlib_foundation] theorem tendstoInMeasure_of_integral_sq {X : ℕ → Ω → ℝ}
    (hX : ∀ m, MemLp (X m) 2 P) (h : Tendsto (fun m => ∫ ω, X m ω ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P X atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  have hle : ∀ m, P.real {ω | ε ≤ dist (X m ω) ((0 : Ω → ℝ) ω)} ≤
      (∫ ω, X m ω ^ 2 ∂P) / ε ^ 2 := by
    intro m
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (ae_of_all _ fun ω => sq_nonneg (X m ω))
      (hX m).integrable_sq (ε ^ 2)
    have hsub : {ω | ε ≤ dist (X m ω) ((0 : Ω → ℝ) ω)} ⊆ {ω | ε ^ 2 ≤ X m ω ^ 2} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero] at hω ⊢
      have := pow_le_pow_left₀ hε.le hω 2
      rwa [sq_abs] at this
    rw [le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_right (measureReal_mono hsub) (by positivity)).trans
      (by linarith [hmk])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun m => measureReal_nonneg) hle
  simpa using h.div_const (ε ^ 2)

/-- **Means converge under convergence in probability with bounded second moments**: if
`Xₘ → 0` in probability and `E Xₘ² ≤ C`, then `E Xₘ → 0`. -/
@[tmio T, powerlib_foundation] theorem tendsto_integral_of_tendstoInMeasure {X : ℕ → Ω → ℝ}
    {C : ℝ} (hXm : ∀ m, Measurable (X m)) (hX2 : ∀ m, MemLp (X m) 2 P)
    (hXC : ∀ m, ∫ ω, X m ω ^ 2 ∂P ≤ C) (hX : TendstoInMeasure P X atTop 0) :
    Tendsto (fun m => ∫ ω, X m ω ∂P) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hX
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε := η / 3 with hεdef
  have hε : 0 < ε := by positivity
  set lam := 3 * (|C| + 1) / η with hlam
  have hlam0 : 0 < lam := by positivity
  have hP := hX ε hε
  rw [Metric.tendsto_atTop] at hP
  obtain ⟨M, hM⟩ := hP (η / (3 * lam)) (by positivity)
  refine ⟨M, fun m hm => ?_⟩
  set A := {ω | ε ≤ dist (X m ω) ((0 : Ω → ℝ) ω)} with hA
  have hAm : MeasurableSet A := by
    simp only [hA, Pi.zero_apply, Real.dist_eq, sub_zero]
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp (hXm m))
  have hPA : P.real A < η / (3 * lam) := by
    have := hM m hm
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
  have hpt : ∀ ω, |X m ω| ≤ ε + X m ω ^ 2 / (2 * lam) + lam / 2 * A.indicator 1 ω := by
    intro ω
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      have : |X m ω| ≤ X m ω ^ 2 / (2 * lam) + lam / 2 := by
        rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (|X m ω| - lam), sq_abs (X m ω)]
      linarith
    · rw [Set.indicator_of_notMem h, mul_zero, add_zero]
      simp only [hA, Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero, not_le] at h
      have : 0 ≤ X m ω ^ 2 / (2 * lam) := by positivity
      linarith
  have hint2 : Integrable (fun ω => X m ω ^ 2) P := (hX2 m).integrable_sq
  have hi1 : Integrable (fun ω => ε + X m ω ^ 2 / (2 * lam)) P :=
    (integrable_const _).add (hint2.div_const _)
  have hi2 : Integrable (fun ω => lam / 2 * A.indicator 1 ω) P :=
    ((integrable_const (1 : ℝ)).indicator hAm).const_mul _
  have hintR : Integrable (fun ω => ε + X m ω ^ 2 / (2 * lam) + lam / 2 * A.indicator 1 ω) P :=
    hi1.add hi2
  have e : ∫ ω, (ε + X m ω ^ 2 / (2 * lam) + lam / 2 * A.indicator 1 ω) ∂P =
      ε + (∫ ω, X m ω ^ 2 ∂P) / (2 * lam) + lam / 2 * P.real A := by
    rw [integral_add hi1 hi2, integral_add (integrable_const _) (hint2.div_const _),
      integral_const_mul, integral_indicator_one hAm,
      show ∫ ω, X m ω ^ 2 / (2 * lam) ∂P = (∫ ω, X m ω ^ 2 ∂P) / (2 * lam) from
        integral_div _ _]
    simp
  have hbound : |∫ ω, X m ω ∂P| ≤ ε + C / (2 * lam) + lam / 2 * P.real A := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono ((hX2 m).integrable one_le_two).abs hintR hpt).trans ?_
    rw [e]
    have := div_le_div_of_nonneg_right (hXC m) (by positivity : (0 : ℝ) ≤ 2 * lam)
    linarith
  have h1 : C / (2 * lam) ≤ η / 6 := by
    rw [hlam, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [le_abs_self C, abs_nonneg C]
  have h2 : lam / 2 * P.real A < η / 6 := by
    have : lam / 2 * P.real A < lam / 2 * (η / (3 * lam)) :=
      mul_lt_mul_of_pos_left hPA (by positivity)
    calc _ < _ := this
      _ = η / 6 := by field_simp; ring
  rw [Real.dist_eq, sub_zero]
  linarith

/-- If `|Yₘ|/(1 + Vₘ) → 0` pointwise, `Vₘ ≥ 0` and `E Vₘ ≤ C`, then `Yₘ → 0` in probability. -/
@[tmio T, powerlib_foundation] theorem tendstoInMeasure_of_div_one_add {Y V : ℕ → Ω → ℝ}
    {C : ℝ} (hYm : ∀ m, Measurable (Y m)) (hVm : ∀ m, Measurable (V m))
    (hV : ∀ m, Integrable (V m) P) (hV0 : ∀ m ω, 0 ≤ V m ω) (hVC : ∀ m, ∫ ω, V m ω ∂P ≤ C)
    (hY : ∀ ω, Tendsto (fun m => |Y m ω| / (1 + V m ω)) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop 0 := by
  set W : ℕ → Ω → ℝ := fun m ω => |Y m ω| / (1 + V m ω) with hW
  have hWm : ∀ m, Measurable (W m) := fun m =>
    (continuous_abs.measurable.comp (hYm m)).div (measurable_const.add (hVm m))
  have hWc : TendstoInMeasure P W atTop 0 :=
    tendstoInMeasure_of_tendsto_ae (fun m => (hWm m).aestronglyMeasurable)
      (ae_of_all _ fun ω => hY ω)
  rw [tendstoInMeasure_iff_measureReal_dist] at hWc ⊢
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro η hη
  set M := 2 * (|C| + 1) / η with hMdef
  have hM : 0 < M := by positivity
  have hW1 := hWc (ε / (1 + M)) (by positivity)
  rw [Metric.tendsto_atTop] at hW1
  obtain ⟨m₀, hm₀⟩ := hW1 (η / 2) (by positivity)
  refine ⟨m₀, fun m hm => ?_⟩
  have hsub : {ω | ε ≤ dist (Y m ω) ((0 : Ω → ℝ) ω)} ⊆
      {ω | ε / (1 + M) ≤ dist (W m ω) ((0 : Ω → ℝ) ω)} ∪ {ω | M ≤ V m ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero, Set.mem_union] at hω ⊢
    by_contra hc
    push Not at hc
    have h1V : 0 < 1 + V m ω := by linarith [hV0 m ω]
    have hWabs : |W m ω| = |Y m ω| / (1 + V m ω) := by
      rw [hW]; exact abs_of_nonneg (div_nonneg (abs_nonneg _) h1V.le)
    rw [hWabs, div_lt_div_iff₀ h1V (by positivity)] at hc
    nlinarith [hc.1, hc.2, abs_nonneg (Y m ω)]
  have hMark : P.real {ω | M ≤ V m ω} ≤ C / M := by
    have := mul_meas_ge_le_integral_of_nonneg (μ := P) (ae_of_all _ fun ω => hV0 m ω) (hV m) M
    rw [le_div_iff₀ hM]
    linarith [hVC m]
  have hCM : C / M < η / 2 := by
    rw [hMdef, div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith [le_abs_self C, abs_nonneg C]
  have hWm' := hm₀ m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hWm'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ < η / 2 + η / 2 := add_lt_add_of_lt_of_le hWm' (hMark.trans hCM.le)
    _ = η := by ring

/-- Sums of sequences converging to `0` in probability converge to `0` in probability. -/
@[tmio T, powerlib_foundation] theorem tendstoInMeasure_add_zero {Y Z : ℕ → Ω → ℝ}
    (hY : TendstoInMeasure P Y atTop 0) (hZ : TendstoInMeasure P Z atTop 0) :
    TendstoInMeasure P (fun m ω => Y m ω + Z m ω) atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hY hZ ⊢
  intro ε hε
  have h := (hY (ε / 2) (by positivity)).add (hZ (ε / 2) (by positivity))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun m => measureReal_nonneg) fun m => ?_
  have hsub : {ω | ε ≤ dist (Y m ω + Z m ω) ((0 : Ω → ℝ) ω)} ⊆
      {ω | ε / 2 ≤ dist (Y m ω) ((0 : Ω → ℝ) ω)} ∪
        {ω | ε / 2 ≤ dist (Z m ω) ((0 : Ω → ℝ) ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero, Set.mem_union] at hω ⊢
    by_contra hc
    push Not at hc
    have := abs_add_le (Y m ω) (Z m ω)
    linarith [hc.1, hc.2]
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

/-- If `Zₘ − Mₘ → 0` in probability and `Zₘ → Y` pointwise (`Zₘ` measurable), then `Mₘ → Y` in
probability. -/
@[tmio T, powerlib_foundation] theorem tendstoInMeasure_of_sub_of_tendsto {Z M : ℕ → Ω → ℝ}
    {Y : Ω → ℝ} (hZm : ∀ m, Measurable (Z m))
    (hD : TendstoInMeasure P (fun m ω => Z m ω - M m ω) atTop 0)
    (hZ : ∀ ω, Tendsto (fun m => Z m ω) atTop (𝓝 (Y ω))) : TendstoInMeasure P M atTop Y := by
  have hZY : TendstoInMeasure P Z atTop Y :=
    tendstoInMeasure_of_tendsto_ae (fun m => (hZm m).aestronglyMeasurable)
      (ae_of_all _ hZ)
  rw [tendstoInMeasure_iff_measureReal_dist] at hD hZY ⊢
  intro ε hε
  have h := (hD (ε / 2) (by positivity)).add (hZY (ε / 2) (by positivity))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun m => measureReal_nonneg) fun m => ?_
  have hsub : {ω | ε ≤ dist (M m ω) (Y ω)} ⊆
      {ω | ε / 2 ≤ dist (Z m ω - M m ω) ((0 : Ω → ℝ) ω)} ∪ {ω | ε / 2 ≤ dist (Z m ω) (Y ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero, Set.mem_union] at hω ⊢
    by_contra hc
    push Not at hc
    have := abs_sub_le (M m ω) (Z m ω) (Y ω)
    rw [abs_sub_comm (M m ω) (Z m ω)] at this
    linarith [hc.1, hc.2]
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

end Ito
end powerlib.Stochastic
