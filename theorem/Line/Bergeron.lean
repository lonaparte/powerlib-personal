import dependencies.Mathlib
import theorem.Attributes
import theorem.PDE.Partial

/-! # Telegrapher equations: characteristics, d'Alembert form and the Bergeron relations

Time-domain lossless line: Riemann invariants along the characteristics, the Bergeron (EMTP
companion) relations for every C¹ solution, and the d'Alembert travelling-wave form.

Model boundary.
* Single-conductor line, uniform constants `L', C' > 0` (and `R', G'` where stated),
  space `x ∈ [a, b]`, time `t ∈ ℝ`, continuous time; no frequency dependence.
* Unknowns `v, i : ℝ × ℝ → ℝ` as functions of `(x, t)`; `i(x, t)` is the conductor
  current in the `+x` direction. A solution on the strip `[a, b] × ℝ` is a pair with
  partial derivatives (Fréchet derivative within the strip, so C¹ up to the
  boundary) satisfying `∂ₓv = -L'∂ₜi - R'i`, `∂ₓi = -C'∂ₜv - G'v` at every point
  (`IsTelegrapherSolution`).
* Port current convention: **both ends use the inflow (node-injection) convention**,
  `i₁(t) = i(0, t)` flows into the line at end 1 and `i₂(t) = -i(ℓ, t)` flows into the
  line at end 2. (T-telegrapher-bergeron uses the through convention for `i₂` and
  T-pde-systems §1.6.5 mixes the two; here one convention is used throughout, and the
  through-convention statements are corollaries `bergeron_forward_through`.)
* `c = 1/√(L'C')`, `Z_c = √(L'/C')`, `τ = ℓ/c`. The identities `c Z_c C' = 1` and
  `c L' = Z_c` (`c_mul_Zc_mul_C`, `c_mul_L`) are what make `v ± Z_c i` invariant.

Source: work-sync `theory/T-telegrapher-bergeron.md` §1.1, §1.1.1, §1.4, §1.4.1;
`theory/T-pde-systems.md` §1.4.4 (transport equation), §1.4.5, §1.6.5.

Results.
* Riemann invariants (`forward_invariant`, `backward_invariant`): for every C¹ solution of the
  lossless equations, `v + Z_c i` is constant along `x - ct = const` and `v - Z_c i` along
  `x + ct = const`.
* Bergeron relations (`bergeron_forward`, `bergeron_backward`, `bergeron_companion`; any C¹
  solution, no d'Alembert ansatz):
  `v₂(t) - Z_c i₂(t) = v₁(t-τ) + Z_c i₁(t-τ)` and `v₁(t) - Z_c i₁(t) = v₂(t-τ) + Z_c i₂(t-τ)`,
  i.e. the EMTP companion `iₖ(t) = (vₖ(t) - eₖ(t))/Z_c` with history source
  `eₖ(t) = v_{k'}(t-τ) + Z_c i_{k'}(t-τ)`.
* d'Alembert: `v = f(x-ct) + g(x+ct)`, `i = (f(x-ct) - g(x+ct))/Z_c` solves the lossless
  system for differentiable `f, g` (`travelling_isSolution`); conversely every C¹ solution on
  the whole plane has this form (`eq_travelling`).
* The partial-derivative predicate `PDE.HasPartialsWithin`, the strip `PDE.strip` and
  `PDE.const_along_segment` are in `theorem/PDE/Partial.lean`; the transport equation
  `u_t + a u_x = 0` is in `theorem/PDE/Transport.lean`.
-/

noncomputable section
namespace powerlib.Line
open Set
open powerlib.PDE (HasPartialsWithin strip const_along_segment)

/-- A solution of the telegrapher equations on the strip `[a, b] × ℝ`. -/
def IsTelegrapherSolution (L C R G a b : ℝ) (v i : ℝ × ℝ → ℝ) : Prop :=
  ∃ vx vt ix it : ℝ × ℝ → ℝ, ∀ q ∈ strip a b,
    HasPartialsWithin v vx vt (strip a b) q ∧ HasPartialsWithin i ix it (strip a b) q ∧
      vx q = -L * it q - R * i q ∧ ix q = -C * vt q - G * v q

/-- Lossless line constants. -/
structure LosslessLine where
  L : ℝ
  C : ℝ
  L_pos : 0 < L
  C_pos : 0 < C

namespace LosslessLine

variable (p : LosslessLine)

/-- Wave speed `c = 1/√(L'C')`. -/
def c : ℝ := 1 / Real.sqrt (p.L * p.C)

/-- Characteristic (surge) impedance `Z_c = √(L'/C')`. -/
def Zc : ℝ := Real.sqrt (p.L / p.C)

@[tmio M, powerlib_foundation] theorem c_pos : 0 < p.c :=
  one_div_pos.mpr (Real.sqrt_pos.mpr (mul_pos p.L_pos p.C_pos))

@[powerlib_foundation] theorem Zc_pos : 0 < p.Zc := Real.sqrt_pos.mpr (div_pos p.L_pos p.C_pos)

@[powerlib_foundation] theorem c_sq_mul : p.c ^ 2 * (p.L * p.C) = 1 := by
  have h := Real.sq_sqrt (mul_pos p.L_pos p.C_pos).le
  have hs : Real.sqrt (p.L * p.C) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos p.L_pos p.C_pos)).ne'
  rw [c, div_pow, one_pow, h]
  exact div_mul_cancel₀ 1 (mul_pos p.L_pos p.C_pos).ne'

/-- `c · Z_c · C' = 1`. -/
@[powerlib_foundation] theorem c_mul_Zc_mul_C : p.c * p.Zc * p.C = 1 := by
  have hL := p.L_pos; have hC := p.C_pos
  rw [c, Zc, Real.sqrt_mul hL.le, Real.sqrt_div hL.le]
  have h1 : 0 < Real.sqrt p.L := Real.sqrt_pos.mpr hL
  have h2 : 0 < Real.sqrt p.C := Real.sqrt_pos.mpr hC
  have h3 : Real.sqrt p.C ^ 2 = p.C := Real.sq_sqrt hC.le
  field_simp
  nlinarith [h3]

/-- `c · L' = Z_c`. -/
@[powerlib_foundation] theorem c_mul_L : p.c * p.L = p.Zc := by
  have hL := p.L_pos; have hC := p.C_pos
  rw [c, Zc, Real.sqrt_mul hL.le, Real.sqrt_div hL.le]
  have h1 : 0 < Real.sqrt p.L := Real.sqrt_pos.mpr hL
  have h2 : 0 < Real.sqrt p.C := Real.sqrt_pos.mpr hC
  have h3 : Real.sqrt p.L ^ 2 = p.L := Real.sq_sqrt hL.le
  field_simp
  nlinarith [h3]

variable {p}
variable {a b : ℝ} {v i : ℝ × ℝ → ℝ}

/-- Forward Riemann invariant: `v + Z_c i` is constant along `x - ct = const`. -/
@[powerlib_foundation] theorem forward_invariant
    (h : IsTelegrapherSolution p.L p.C 0 0 a b v i) (hab : a ≤ b) (t₀ : ℝ) :
    v (b, t₀ + (b - a) / p.c) + p.Zc * i (b, t₀ + (b - a) / p.c) =
      v (a, t₀) + p.Zc * i (a, t₀) := by
  obtain ⟨vx, vt, ix, it, hsol⟩ := h
  have hc := p.c_pos
  have hpt : ∀ s : ℝ, ((a, t₀) : ℝ × ℝ) + s • ((1 : ℝ), 1 / p.c) = (a + s, t₀ + s / p.c) := by
    intro s; ext <;> simp; ring
  have hmaps : ∀ s ∈ Icc (0 : ℝ) (b - a),
      ((a, t₀) : ℝ × ℝ) + s • ((1 : ℝ), 1 / p.c) ∈ strip a b := by
    intro s hs
    rw [hpt]
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, trivial⟩
  have key := const_along_segment (U := fun q => v q + p.Zc * i q)
    (Ux := fun q => vx q + p.Zc * ix q) (Ut := fun q => vt q + p.Zc * it q)
    (S := strip a b) (p₀ := (a, t₀)) (d := ((1 : ℝ), 1 / p.c)) (sub_nonneg.mpr hab) hmaps
    (by
      intro s hs
      obtain ⟨hv, hi, -, -⟩ := hsol _ (hmaps s hs)
      exact (hv.add (hi.const_mul p.Zc)).congr_fderiv (by ext <;> simp))
    (by
      intro s hs
      obtain ⟨-, -, hkvl, hkcl⟩ := hsol _ (hmaps s hs)
      generalize (((a, t₀) : ℝ × ℝ) + s • ((1 : ℝ), 1 / p.c)) = q at hkvl hkcl ⊢
      rw [hkvl, hkcl]
      have hc0 := hc.ne'
      have e : (-p.L * it q - 0 * i q + p.Zc * (-p.C * vt q - 0 * v q)) * (1, 1 / p.c).1 +
          (vt q + p.Zc * it q) * (1, 1 / p.c).2 =
          (it q * (p.Zc - p.c * p.L) + vt q * (1 - p.c * p.Zc * p.C)) / p.c := by
        simp only; field_simp; ring
      rw [e, p.c_mul_Zc_mul_C, p.c_mul_L]; simp)
  simp only [hpt, add_zero, zero_div, add_sub_cancel] at key
  exact key

/-- Backward Riemann invariant: `v - Z_c i` is constant along `x + ct = const`. -/
@[powerlib_foundation] theorem backward_invariant
    (h : IsTelegrapherSolution p.L p.C 0 0 a b v i) (hab : a ≤ b) (t₀ : ℝ) :
    v (b, t₀ - (b - a) / p.c) - p.Zc * i (b, t₀ - (b - a) / p.c) =
      v (a, t₀) - p.Zc * i (a, t₀) := by
  obtain ⟨vx, vt, ix, it, hsol⟩ := h
  have hc := p.c_pos
  have hpt : ∀ s : ℝ, ((a, t₀) : ℝ × ℝ) + s • ((1 : ℝ), -(1 / p.c)) = (a + s, t₀ - s / p.c) := by
    intro s; ext <;> simp; ring
  have hmaps : ∀ s ∈ Icc (0 : ℝ) (b - a),
      ((a, t₀) : ℝ × ℝ) + s • ((1 : ℝ), -(1 / p.c)) ∈ strip a b := by
    intro s hs
    rw [hpt]
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, trivial⟩
  have key := const_along_segment (U := fun q => v q - p.Zc * i q)
    (Ux := fun q => vx q - p.Zc * ix q) (Ut := fun q => vt q - p.Zc * it q)
    (S := strip a b) (p₀ := (a, t₀)) (d := ((1 : ℝ), -(1 / p.c))) (sub_nonneg.mpr hab) hmaps
    (by
      intro s hs
      obtain ⟨hv, hi, -, -⟩ := hsol _ (hmaps s hs)
      exact (hv.sub (hi.const_mul p.Zc)).congr_fderiv (by ext <;> simp))
    (by
      intro s hs
      obtain ⟨-, -, hkvl, hkcl⟩ := hsol _ (hmaps s hs)
      generalize (((a, t₀) : ℝ × ℝ) + s • ((1 : ℝ), -(1 / p.c))) = q at hkvl hkcl ⊢
      rw [hkvl, hkcl]
      have hc0 := hc.ne'
      have e : (-p.L * it q - 0 * i q - p.Zc * (-p.C * vt q - 0 * v q)) * (1, -(1 / p.c)).1 +
          (vt q - p.Zc * it q) * (1, -(1 / p.c)).2 =
          (it q * (p.Zc - p.c * p.L) + vt q * (p.c * p.Zc * p.C - 1)) / p.c := by
        simp only; field_simp; ring
      rw [e, p.c_mul_Zc_mul_C, p.c_mul_L]; simp)
  simp only [hpt, add_zero, zero_div, sub_zero, add_sub_cancel] at key
  exact key

/-! ## Bergeron relations -/

/-- One-way travel time `τ = ℓ/c`. -/
def τ (p : LosslessLine) (ℓ : ℝ) : ℝ := ℓ / p.c

/-- Port voltage at end 1. -/
def v₁ (v : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := v (0, t)
/-- Port voltage at end 2. -/
def v₂ (ℓ : ℝ) (v : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := v (ℓ, t)
/-- Current injected into the line at end 1 (along `+x`). -/
def i₁ (i : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := i (0, t)
/-- Current injected into the line at end 2 (along `-x`). -/
def i₂ (ℓ : ℝ) (i : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := -i (ℓ, t)

/-- **Bergeron relation, forward wave** (inflow convention at both ends):
`v₂(t) - Z_c i₂(t) = v₁(t - τ) + Z_c i₁(t - τ)` for every C¹ lossless solution. -/
@[powerlib_foundation] theorem bergeron_forward {ℓ : ℝ}
    (h : IsTelegrapherSolution p.L p.C 0 0 0 ℓ v i) (hℓ : 0 ≤ ℓ) (t : ℝ) :
    v₂ ℓ v t - p.Zc * i₂ ℓ i t = v₁ v (t - τ p ℓ) + p.Zc * i₁ i (t - τ p ℓ) := by
  have := forward_invariant h hℓ (t - τ p ℓ)
  simp only [sub_zero, τ, sub_add_cancel] at this
  simp only [v₁, v₂, i₁, i₂, τ]
  linarith

/-- **Bergeron relation, backward wave** (inflow convention at both ends):
`v₁(t) - Z_c i₁(t) = v₂(t - τ) + Z_c i₂(t - τ)`. -/
@[powerlib_foundation] theorem bergeron_backward {ℓ : ℝ}
    (h : IsTelegrapherSolution p.L p.C 0 0 0 ℓ v i) (hℓ : 0 ≤ ℓ) (t : ℝ) :
    v₁ v t - p.Zc * i₁ i t = v₂ ℓ v (t - τ p ℓ) + p.Zc * i₂ ℓ i (t - τ p ℓ) := by
  have := backward_invariant h hℓ t
  simp only [sub_zero] at this
  simp only [v₁, v₂, i₁, i₂, τ]
  linarith

/-- History source of the Bergeron companion at end 2. -/
def history₂ (ℓ : ℝ) (v i : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  v₁ v (t - τ p ℓ) + p.Zc * i₁ i (t - τ p ℓ)

/-- History source of the Bergeron companion at end 1. -/
def history₁ (ℓ : ℝ) (v i : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  v₂ ℓ v (t - τ p ℓ) + p.Zc * i₂ ℓ i (t - τ p ℓ)

/-- EMTP companion form: each end is a conductance `1/Z_c` in parallel with a history
current source, `iₖ(t) = vₖ(t)/Z_c - eₖ(t)/Z_c`. -/
@[powerlib_foundation] theorem bergeron_companion {ℓ : ℝ}
    (h : IsTelegrapherSolution p.L p.C 0 0 0 ℓ v i) (hℓ : 0 ≤ ℓ) (t : ℝ) :
    i₁ i t = v₁ v t / p.Zc - history₁ (p := p) ℓ v i t / p.Zc ∧
      i₂ ℓ i t = v₂ ℓ v t / p.Zc - history₂ (p := p) ℓ v i t / p.Zc := by
  have hZ := p.Zc_pos.ne'
  have h1 := bergeron_backward h hℓ t
  have h2 := bergeron_forward h hℓ t
  constructor
  · rw [history₁]; field_simp; linarith
  · rw [history₂]; field_simp; linarith

/-- The same forward relation in the through convention (`i(ℓ, t)` along `+x`). -/
@[powerlib_foundation] theorem bergeron_forward_through {ℓ : ℝ}
    (h : IsTelegrapherSolution p.L p.C 0 0 0 ℓ v i) (hℓ : 0 ≤ ℓ) (t : ℝ) :
    v (ℓ, t) + p.Zc * i (ℓ, t) = v (0, t - τ p ℓ) + p.Zc * i (0, t - τ p ℓ) := by
  have := bergeron_forward h hℓ t
  simp only [v₁, v₂, i₁, i₂] at this
  linarith

/-! ## d'Alembert form -/

/-- Travelling-wave pair `v = f(x - ct) + g(x + ct)`, `i = (f(x - ct) - g(x + ct))/Z_c`. -/
def travellingV (p : LosslessLine) (f g : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  f (q.1 - p.c * q.2) + g (q.1 + p.c * q.2)

def travellingI (p : LosslessLine) (f g : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  (f (q.1 - p.c * q.2) - g (q.1 + p.c * q.2)) / p.Zc

/-- Travelling waves solve the lossless telegrapher equations on every strip. -/
@[powerlib_foundation] theorem travelling_isSolution {f g f' g' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hg : ∀ y, HasDerivAt g (g' y) y) (a b : ℝ) :
    IsTelegrapherSolution p.L p.C 0 0 a b (travellingV p f g) (travellingI p f g) := by
  have hZ := p.Zc_pos.ne'
  have hc := p.c_pos.ne'
  refine ⟨fun q => f' (q.1 - p.c * q.2) + g' (q.1 + p.c * q.2),
    fun q => -p.c * f' (q.1 - p.c * q.2) + p.c * g' (q.1 + p.c * q.2),
    fun q => (f' (q.1 - p.c * q.2) - g' (q.1 + p.c * q.2)) / p.Zc,
    fun q => (-p.c * f' (q.1 - p.c * q.2) - p.c * g' (q.1 + p.c * q.2)) / p.Zc,
    fun q _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · have hm : HasFDerivAt (fun q : ℝ × ℝ => q.1 - p.c * q.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ - p.c • ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
      (hasFDerivAt_fst).sub ((hasFDerivAt_snd).const_mul p.c)
    have hp : HasFDerivAt (fun q : ℝ × ℝ => q.1 + p.c * q.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ + p.c • ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
      (hasFDerivAt_fst).add ((hasFDerivAt_snd).const_mul p.c)
    have := ((hf _).comp_hasFDerivAt q hm).add ((hg _).comp_hasFDerivAt q hp)
    exact (this.congr_fderiv (by ext <;> simp; ring)).hasFDerivWithinAt
  · have hm : HasFDerivAt (fun q : ℝ × ℝ => q.1 - p.c * q.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ - p.c • ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
      (hasFDerivAt_fst).sub ((hasFDerivAt_snd).const_mul p.c)
    have hp : HasFDerivAt (fun q : ℝ × ℝ => q.1 + p.c * q.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ + p.c • ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
      (hasFDerivAt_fst).add ((hasFDerivAt_snd).const_mul p.c)
    have := (((hf _).comp_hasFDerivAt q hm).sub ((hg _).comp_hasFDerivAt q hp)).mul_const
      p.Zc⁻¹
    exact (this.congr_fderiv (by ext <;> simp <;> field_simp)).hasFDerivWithinAt
  · simp only [zero_mul, sub_zero]
    have h2 := p.c_mul_L
    field_simp
    linear_combination (-(f' (q.1 - p.c * q.2)) - g' (q.1 + p.c * q.2)) * h2
  · simp only [zero_mul, sub_zero]
    have h1 := p.c_mul_Zc_mul_C
    field_simp
    linear_combination (g' (q.1 + p.c * q.2) - f' (q.1 - p.c * q.2)) * h1

/-- Riemann invariants of a travelling-wave pair: `v ± Z_c i = 2f(x - ct)`, `2g(x + ct)`. -/
@[powerlib_foundation] theorem travelling_invariants (f g : ℝ → ℝ) (q : ℝ × ℝ) :
    travellingV p f g q + p.Zc * travellingI p f g q = 2 * f (q.1 - p.c * q.2) ∧
      travellingV p f g q - p.Zc * travellingI p f g q = 2 * g (q.1 + p.c * q.2) := by
  have hZ := p.Zc_pos.ne'
  constructor <;> simp only [travellingV, travellingI] <;> field_simp <;> ring

/-- **Every C¹ solution of the lossless telegrapher equations on the plane is a
travelling-wave pair**, with `f(ξ) = (v + Z_c i)(ξ, 0)/2`, `g(η) = (v - Z_c i)(η, 0)/2`. -/
@[powerlib_foundation] theorem eq_travelling
    (h : ∀ a b, IsTelegrapherSolution p.L p.C 0 0 a b v i) (q : ℝ × ℝ) :
    v q = travellingV p (fun ξ => (v (ξ, 0) + p.Zc * i (ξ, 0)) / 2)
        (fun η => (v (η, 0) - p.Zc * i (η, 0)) / 2) q ∧
      i q = travellingI p (fun ξ => (v (ξ, 0) + p.Zc * i (ξ, 0)) / 2)
        (fun η => (v (η, 0) - p.Zc * i (η, 0)) / 2) q := by
  obtain ⟨x, t⟩ := q
  have hc := p.c_pos
  have hZ := p.Zc_pos.ne'
  have hplus : v (x, t) + p.Zc * i (x, t) = v (x - p.c * t, 0) + p.Zc * i (x - p.c * t, 0) := by
    rcases le_total 0 t with ht | ht
    · have := forward_invariant (h (x - p.c * t) x) (by nlinarith) 0
      have e : (0 : ℝ) + (x - (x - p.c * t)) / p.c = t := by field_simp; ring
      rw [e] at this
      exact this
    · have := forward_invariant (h x (x - p.c * t)) (by nlinarith) t
      have e : t + (x - p.c * t - x) / p.c = 0 := by field_simp; ring
      rw [e] at this
      exact this.symm
  have hminus : v (x, t) - p.Zc * i (x, t) = v (x + p.c * t, 0) - p.Zc * i (x + p.c * t, 0) := by
    rcases le_total 0 t with ht | ht
    · have := backward_invariant (h x (x + p.c * t)) (by nlinarith) t
      have e : t - (x + p.c * t - x) / p.c = 0 := by field_simp; ring
      rw [e] at this
      exact this.symm
    · have := backward_invariant (h (x + p.c * t) x) (by nlinarith) 0
      have e : (0 : ℝ) - (x - (x + p.c * t)) / p.c = t := by field_simp; ring
      rw [e] at this
      exact this
  simp only [travellingV, travellingI]
  constructor
  · linarith
  · field_simp
    linarith

end LosslessLine

end powerlib.Line
