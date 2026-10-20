import theorem.Attributes
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Moments.Tilted

/-! # Maximum entropy: the Gibbs (tilted) measure is the unique I-projection

The Gibbs (tilted) measure minimises relative entropy on the moment class, uniquely, and is the
I-projection of the reference measure onto the linear moment family; the one-constraint dual.

Scope.
* General probability, not an engineering result.
* `m` is a σ-finite reference measure on an arbitrary measurable space (it need not be finite,
  e.g. Lebesgue measure). A log-tilt `g : α → ℝ` with `∫ exp g dm < ∞` defines the Gibbs /
  MaxEnt measure `m.tilted g = m · exp g / Z`, `Z = ∫ exp g dm`. For constraints `E[f_k] = F_k`
  the tilt is `g = -∑ λ_k f_k`, see `gibbs`.
* Jaynes maximises `H[p‖m] = -∫ log (dp/dm) dp`. We work with
  `relEntropy p m = ∫ log (dp/dm) dp` (`= -H[p‖m]`), which is a real number for every
  probability `p ≪ m` and is the Kullback–Leibler divergence when `m` is itself a probability
  measure. Mathlib's `klDiv` is used only between probability measures, where it is the usual
  divergence.

Source: work-sync theory/T-maximum-entropy.md — boxed MaxEnt form (head), §1.1 (dual and its
derivatives), §1.6 (exponential families are MaxEnt solutions), §1.7 (I-projection).

Results.
* `relEntropy_eq_klDiv_tilted_add` — Pythagorean identity: if `E_p g = E_{p_λ} g` then
  `relEntropy p m = KL(p‖p_λ) + relEntropy p_λ m`.
* `relEntropy_tilted_le`, `relEntropy_eq_relEntropy_tilted_iff` — `p_λ` minimises relative
  entropy (maximises `H[·‖m]`) on the moment class, uniquely.
* `gibbs_isIProjection` — for finitely many constraints, the Gibbs measure whose multipliers
  close the constraints is the unique I-projection of `m` onto the linear moment family.
* `gibbs_isIProjection_own_moments` — every exponential-family member is the MaxEnt solution
  for its own moments (§1.6).
* `klDiv_eq_klDiv_tilted_add` — the same identity in `klDiv` form when `m` is a probability
  measure.
* `deriv_dual`, `deriv_dual_eq_zero_iff`, `iteratedDeriv_two_dual`,
  `iteratedDeriv_two_dual_nonneg` — one constraint: the dual `D(λ) = log Z(λ) + λ F` has
  `D' = F - E_{p_λ}[f]` and `D'' = Var_{p_λ}[f] ≥ 0`. These are thin wrappers of Mathlib
  `ProbabilityTheory.integral_tilted_mul_self` and `ProbabilityTheory.variance_tilted_mul`.

Corrections.
* The note states the maximiser exists whenever "the constraints close". The formal statement
  makes the closure hypothesis explicit: the multipliers must satisfy `E_{p_λ}[f_k] = F_k`,
  `exp(-∑ λ_k f_k)` must be `m`-integrable and the constraint functions must be integrable under
  both measures. Existence of such `λ` is not proved here.
-/

noncomputable section
namespace powerlib.Information
open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α}

/-- Real-valued relative entropy `∫ log (dp/dm) dp`, i.e. `-H[p‖m]` in Jaynes's notation. -/
def relEntropy (p m : Measure α) : ℝ := ∫ x, llr p m x ∂p

@[powerlib_foundation] theorem relEntropy_eq_toReal_klDiv {p m : Measure α}
    [IsProbabilityMeasure p] [IsProbabilityMeasure m] (hpm : p ≪ m) :
    relEntropy p m = (klDiv p m).toReal := by
  rw [relEntropy, toReal_klDiv_of_measure_eq hpm (by simp)]

section Tilted

variable {m p : Measure α} [SigmaFinite m] {g : α → ℝ}

omit [SigmaFinite m] in
@[powerlib_foundation] private theorem aemeasurable_of_integrable_exp
    (hg : Integrable (fun x => exp (g x)) m) :
    AEMeasurable g m := by
  simpa using hg.1.aemeasurable.log

/-- The log-likelihood ratio of the Gibbs measure against its reference: `g - log Z`. -/
@[powerlib_foundation] theorem llr_tilted_self_ae (hg : Integrable (fun x => exp (g x)) m) :
    llr (m.tilted g) m =ᵐ[m.tilted g] fun x => g x - log (∫ z, exp (g z) ∂m) := by
  have h1 := llr_tilted_left (μ := m) (ν := m) Measure.AbsolutelyContinuous.rfl hg
    (aemeasurable_of_integrable_exp hg)
  have h2 := llr_self m
  have h : llr (m.tilted g) m =ᵐ[m] fun x => g x - log (∫ z, exp (g z) ∂m) := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2, Pi.zero_apply, add_zero]
  exact (tilted_absolutelyContinuous m g).ae_le h

@[powerlib_foundation] theorem relEntropy_tilted_self [NeZero m]
    (hg : Integrable (fun x => exp (g x)) m) (hgq : Integrable g (m.tilted g)) :
    relEntropy (m.tilted g) m = ∫ x, g x ∂(m.tilted g) - log (∫ z, exp (g z) ∂m) := by
  have : IsProbabilityMeasure (m.tilted g) := isProbabilityMeasure_tilted hg
  rw [relEntropy, integral_congr_ae (llr_tilted_self_ae hg), integral_sub hgq (integrable_const _)]
  simp

@[powerlib_foundation] theorem integrable_llr_tilted_self [NeZero m]
    (hg : Integrable (fun x => exp (g x)) m) (hgq : Integrable g (m.tilted g)) :
    Integrable (llr (m.tilted g) m) (m.tilted g) := by
  have : IsProbabilityMeasure (m.tilted g) := isProbabilityMeasure_tilted hg
  exact (integrable_congr (llr_tilted_self_ae hg)).mpr (hgq.sub (integrable_const _))

/-- **Pythagorean identity of MaxEnt.** If `p` has the same `g`-moment as the Gibbs measure
`p_λ = m.tilted g`, then `relEntropy p m = KL(p‖p_λ) + relEntropy p_λ m`. -/
@[powerlib_foundation] theorem relEntropy_eq_klDiv_tilted_add [NeZero m] [IsProbabilityMeasure p]
    (hg : Integrable (fun x => exp (g x)) m) (hpm : p ≪ m) (hint : Integrable (llr p m) p)
    (hgp : Integrable g p) (hgq : Integrable g (m.tilted g))
    (hmom : ∫ x, g x ∂p = ∫ x, g x ∂(m.tilted g)) :
    relEntropy p m = (klDiv p (m.tilted g)).toReal + relEntropy (m.tilted g) m := by
  have : IsProbabilityMeasure (m.tilted g) := isProbabilityMeasure_tilted hg
  have hpq : p ≪ m.tilted g := hpm.trans (absolutelyContinuous_tilted hg)
  have h1 := integral_llr_tilted_right hpm hgp hg hint
  have h2 : (klDiv p (m.tilted g)).toReal = ∫ x, llr p (m.tilted g) x ∂p :=
    toReal_klDiv_of_measure_eq hpq (by simp)
  rw [relEntropy_tilted_self hg hgq, h2, h1, relEntropy, hmom]
  ring

/-- The Gibbs measure has the least relative entropy (largest `H[·‖m]`) in its moment class. -/
@[powerlib_foundation] theorem relEntropy_tilted_le [NeZero m] [IsProbabilityMeasure p]
    (hg : Integrable (fun x => exp (g x)) m) (hpm : p ≪ m) (hint : Integrable (llr p m) p)
    (hgp : Integrable g p) (hgq : Integrable g (m.tilted g))
    (hmom : ∫ x, g x ∂p = ∫ x, g x ∂(m.tilted g)) :
    relEntropy (m.tilted g) m ≤ relEntropy p m := by
  rw [relEntropy_eq_klDiv_tilted_add hg hpm hint hgp hgq hmom]
  linarith [ENNReal.toReal_nonneg (a := klDiv p (m.tilted g))]

/-- Uniqueness: equality in `relEntropy_tilted_le` holds exactly for the Gibbs measure. -/
@[powerlib_foundation] theorem relEntropy_eq_relEntropy_tilted_iff [NeZero m]
    [IsProbabilityMeasure p]
    (hg : Integrable (fun x => exp (g x)) m) (hpm : p ≪ m) (hint : Integrable (llr p m) p)
    (hgp : Integrable g p) (hgq : Integrable g (m.tilted g))
    (hmom : ∫ x, g x ∂p = ∫ x, g x ∂(m.tilted g)) :
    relEntropy p m = relEntropy (m.tilted g) m ↔ p = m.tilted g := by
  have : IsProbabilityMeasure (m.tilted g) := isProbabilityMeasure_tilted hg
  constructor
  · intro h
    rw [relEntropy_eq_klDiv_tilted_add hg hpm hint hgp hgq hmom] at h
    have h0 : (klDiv p (m.tilted g)).toReal = 0 := by linarith
    have hne : klDiv p (m.tilted g) ≠ ∞ :=
      klDiv_ne_top (hpm.trans (absolutelyContinuous_tilted hg))
        (integrable_llr_tilted_right hpm hgp hint hg)
    have hz : klDiv p (m.tilted g) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
      · exact h
      · exact absurd h hne
    exact klDiv_eq_zero_iff.mp hz
  · intro h
    rw [h]

/-- `klDiv` form of the Pythagorean identity for a probability reference measure. -/
@[powerlib_foundation] theorem klDiv_eq_klDiv_tilted_add [IsProbabilityMeasure m]
    [IsProbabilityMeasure p]
    (hg : Integrable (fun x => exp (g x)) m) (hpm : p ≪ m) (hint : Integrable (llr p m) p)
    (hgp : Integrable g p) (hgq : Integrable g (m.tilted g))
    (hmom : ∫ x, g x ∂p = ∫ x, g x ∂(m.tilted g)) :
    klDiv p m = klDiv p (m.tilted g) + klDiv (m.tilted g) m := by
  have : IsProbabilityMeasure (m.tilted g) := isProbabilityMeasure_tilted hg
  have hqm : m.tilted g ≪ m := tilted_absolutelyContinuous m g
  have hpq : p ≪ m.tilted g := hpm.trans (absolutelyContinuous_tilted hg)
  have h := relEntropy_eq_klDiv_tilted_add hg hpm hint hgp hgq hmom
  rw [relEntropy_eq_toReal_klDiv hpm, relEntropy_eq_toReal_klDiv hqm] at h
  have h1 : klDiv p m ≠ ∞ := klDiv_ne_top hpm hint
  have h2 : klDiv p (m.tilted g) ≠ ∞ :=
    klDiv_ne_top hpq (integrable_llr_tilted_right hpm hgp hint hg)
  have h3 : klDiv (m.tilted g) m ≠ ∞ := klDiv_ne_top hqm (integrable_llr_tilted_self hg hgq)
  rw [← ENNReal.toReal_add h2 h3] at h
  exact (ENNReal.toReal_eq_toReal_iff' h1 (ENNReal.add_ne_top.mpr ⟨h2, h3⟩)).mp h

end Tilted

section Gibbs

variable {ι : Type*} [Fintype ι]

/-- The MaxEnt / Gibbs measure `m(x) exp(-∑ₖ λₖ fₖ(x)) / Z(λ)`. -/
def gibbs (m : Measure α) (f : ι → α → ℝ) (lam : ι → ℝ) : Measure α :=
  m.tilted fun x => -∑ i, lam i * f i x

/-- Probability measures `p ≪ m` with integrable log-likelihood ratio satisfying the linear
moment constraints `E_p[f_k] = F_k`. -/
def momentFamily (m : Measure α) (f : ι → α → ℝ) (F : ι → ℝ) : Set (Measure α) :=
  {p | IsProbabilityMeasure p ∧ p ≪ m ∧ Integrable (llr p m) p ∧
    ∀ i, Integrable (f i) p ∧ ∫ x, f i x ∂p = F i}

@[powerlib_foundation] private theorem integral_tilt {μ : Measure α} {f : ι → α → ℝ} (lam : ι → ℝ)
    (hf : ∀ i, Integrable (f i) μ) :
    ∫ x, -∑ i, lam i * f i x ∂μ = -∑ i, lam i * ∫ x, f i x ∂μ := by
  rw [integral_neg, integral_finsetSum _ (fun i _ => (hf i).const_mul (lam i))]
  simp [integral_const_mul]

@[powerlib_foundation] private theorem integrable_tilt {μ : Measure α} {f : ι → α → ℝ} (lam : ι → ℝ)
    (hf : ∀ i, Integrable (f i) μ) : Integrable (fun x => -∑ i, lam i * f i x) μ :=
  (integrable_finsetSum _ fun i _ => (hf i).const_mul (lam i)).neg

/-- **MaxEnt as I-projection.** If the multipliers `λ` close the constraints
(`gibbs m f λ` lies in the moment family), then `gibbs m f λ` is the unique minimiser of
`relEntropy · m` over the moment family. -/
@[powerlib_foundation] theorem gibbs_isIProjection
    {m : Measure α} [SigmaFinite m] [NeZero m] {f : ι → α → ℝ} {lam F : ι → ℝ}
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hfq : ∀ i, Integrable (f i) (gibbs m f lam))
    (hclose : ∀ i, ∫ x, f i x ∂(gibbs m f lam) = F i) :
    gibbs m f lam ∈ momentFamily m f F ∧
      ∀ p ∈ momentFamily m f F, relEntropy (gibbs m f lam) m ≤ relEntropy p m ∧
        (relEntropy p m = relEntropy (gibbs m f lam) m ↔ p = gibbs m f lam) := by
  have hgq : Integrable (fun x => -∑ i, lam i * f i x) (gibbs m f lam) := integrable_tilt lam hfq
  refine ⟨⟨isProbabilityMeasure_tilted hZ, tilted_absolutelyContinuous m _,
    integrable_llr_tilted_self hZ hgq, fun i => ⟨hfq i, hclose i⟩⟩, ?_⟩
  rintro p ⟨hp, hpm, hint, hpF⟩
  have hfp : ∀ i, Integrable (f i) p := fun i => (hpF i).1
  have hmom : ∫ x, -∑ i, lam i * f i x ∂p = ∫ x, -∑ i, lam i * f i x ∂(gibbs m f lam) := by
    rw [integral_tilt lam hfp, integral_tilt lam hfq]
    simp only [(hpF _).2, hclose]
  exact ⟨relEntropy_tilted_le hZ hpm hint (integrable_tilt lam hfp) hgq hmom,
    relEntropy_eq_relEntropy_tilted_iff hZ hpm hint (integrable_tilt lam hfp) hgq hmom⟩

/-- **Every exponential-family member is a MaxEnt solution** (§1.6): `gibbs m f λ` is the unique
I-projection of `m` onto the family with its own moments `F_k = E_{p_λ}[f_k]`. -/
@[powerlib_foundation] theorem gibbs_isIProjection_own_moments
    {m : Measure α} [SigmaFinite m] [NeZero m] {f : ι → α → ℝ} {lam : ι → ℝ}
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hfq : ∀ i, Integrable (f i) (gibbs m f lam)) :
    ∀ p ∈ momentFamily m f (fun i => ∫ x, f i x ∂(gibbs m f lam)),
      relEntropy (gibbs m f lam) m ≤ relEntropy p m ∧
        (relEntropy p m = relEntropy (gibbs m f lam) m ↔ p = gibbs m f lam) :=
  (gibbs_isIProjection hZ hfq fun _ => rfl).2

end Gibbs

section Dual

/-! One-constraint dual `D(λ) = log Z(λ) + λ F`, `Z(λ) = ∫ exp(-λ f) dm = mgf f m (-λ)`. -/

variable {m : Measure α} {f : α → ℝ}

/-- MaxEnt dual objective for one constraint `E[f] = F`. -/
def dual (m : Measure α) (f : α → ℝ) (F : ℝ) (lam : ℝ) : ℝ := cgf f m (-lam) + lam * F

/-- Dual gradient `D'(λ) = F - E_{p_λ}[f]` with `p_λ = m.tilted (-λ f)`. Wrapper of Mathlib
`ProbabilityTheory.integral_tilted_mul_self` (and `deriv_cgf`). -/
@[powerlib_foundation] theorem deriv_dual {F lam : ℝ}
    (h : -lam ∈ interior (integrableExpSet f m)) :
    deriv (dual m f F) lam = F - (m.tilted ((-lam) * f ·))[f] := by
  have hd : DifferentiableAt ℝ (cgf f m) (-lam) := (analyticAt_cgf h).differentiableAt
  have hd' : DifferentiableAt ℝ (fun l => cgf f m (-l)) lam :=
    differentiableAt_comp_neg.mpr (by simpa using hd)
  have hlin : DifferentiableAt ℝ (fun l : ℝ => l * F) lam := by fun_prop
  rw [show dual m f F = fun l => cgf f m (-l) + l * F from rfl, deriv_fun_add hd' hlin,
    deriv_comp_neg, integral_tilted_mul_self h]
  simp only [deriv_mul_const_field', deriv_id'', one_mul]
  ring

/-- The stationarity condition `D'(λ) = 0` is exactly moment closure `E_{p_λ}[f] = F`. -/
@[powerlib_foundation] theorem deriv_dual_eq_zero_iff {F lam : ℝ}
    (h : -lam ∈ interior (integrableExpSet f m)) :
    deriv (dual m f F) lam = 0 ↔ (m.tilted ((-lam) * f ·))[f] = F := by
  rw [deriv_dual h, sub_eq_zero, eq_comm]

/-- Dual Hessian `D''(λ) = Var_{p_λ}[f]`. Wrapper of Mathlib
`ProbabilityTheory.variance_tilted_mul`. -/
@[powerlib_foundation] theorem iteratedDeriv_two_dual {F lam : ℝ}
    (h : -lam ∈ interior (integrableExpSet f m)) :
    iteratedDeriv 2 (dual m f F) lam = Var[f; m.tilted ((-lam) * f ·)] := by
  have hopen : IsOpen (interior (integrableExpSet f m)) := isOpen_interior
  have hev : deriv (dual m f F) =ᶠ[nhds lam] fun l => F - deriv (cgf f m) (-l) := by
    have : ∀ᶠ l in nhds lam, -l ∈ interior (integrableExpSet f m) :=
      (continuous_neg.tendsto lam).eventually (hopen.mem_nhds (by simpa using h))
    filter_upwards [this] with l hl
    rw [deriv_dual hl, integral_tilted_mul_self hl]
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, variance_tilted_mul h,
    iteratedDeriv_succ, iteratedDeriv_one]
  have hd2 : DifferentiableAt ℝ (deriv (cgf f m)) (-lam) :=
    (analyticAt_cgf h).deriv.differentiableAt
  have hd2' : DifferentiableAt ℝ (fun l => deriv (cgf f m) (-l)) lam :=
    differentiableAt_comp_neg.mpr (by simpa using hd2)
  rw [deriv_fun_sub (differentiableAt_const F) hd2', deriv_comp_neg]
  simp

/-- The dual is convex at every interior point: `D''(λ) ≥ 0`. -/
@[powerlib_foundation] theorem iteratedDeriv_two_dual_nonneg {F lam : ℝ}
    (h : -lam ∈ interior (integrableExpSet f m)) :
    0 ≤ iteratedDeriv 2 (dual m f F) lam := by
  rw [iteratedDeriv_two_dual h]
  exact variance_nonneg _ _

end Dual

end powerlib.Information
