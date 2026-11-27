import theorem.Map.AsymptoticPhase

/-! # Hölder continuity of the asymptotic phase

The asymptotic phase `φ` of `theorem/Map/AsymptoticPhase.lean` (for `F(x, y) = (A x + f(x, y),
B y + g(x, y))` with an invariant `1`-Lipschitz graph `y = h(x)`) is the limit of the
finite-horizon phases `φ_N(p) = r^{−N}((F^N p)₁)`, with the tail
`‖φ_N(p) − φ(p)‖ ≤ C μᴺ`, `C = ε ‖p₂ − h(p₁)‖/(a − b − 3ε)`, `μ = (b + 2ε)/(a − ε)`
(`norm_phaseApprox_sub_le`). Each `φ_N` is Lipschitz: for `‖A x‖ ≤ α ‖x‖` the map `F` is
`(α + ε)`-Lipschitz and `r⁻¹` is `1/(a − ε)`-Lipschitz, so `Lip φ_N ≤ λᴺ`,
`λ = (α + ε)/(a − ε)` (`norm_phaseApprox_sub_phaseApprox_le`). For `d = ‖p − p'‖ ≤ 1` the
horizon `N = ⌈log(1/d)/log(λ/μ)⌉` balances `2C μᴺ` against `λᴺ d` and gives
`‖φ(p) − φ(p')‖ ≤ (2C + λ) d^θ`, `θ = log(1/μ)/log(λ/μ) = log((a − ε)/(b + 2ε)) /
log((α + ε)/(b + 2ε)) ∈ (0, 1]` (`norm_asymptoticPhase_sub_le_rpow`). As `ε → 0` the exponent
tends to `log(a/b)/log(α/b)`, which is `1` for an isometric centre part (`a = α`, e.g. a simple
multiplier `−1` with `A = −id`, the setting of `theorem/Periodic/FlipReduction.lean`): near the
fixed point, where the cut-off makes `ε` as small as wished, the phase is Hölder of every order
below one.

Scope.
* The setting of `theorem/Map/AsymptoticPhase.lean`: real normed spaces `X` (complete), `Y`,
  `X × Y` with the max norm; `A` onto with `a ‖x‖ ≤ ‖A x‖ ≤ α ‖x‖`, `a ≤ α`; `‖B y‖ ≤ b ‖y‖`,
  `0 ≤ b`, `0 < b + 2ε`; `f`, `g` globally `ε`-Lipschitz; the gap `b + 3ε < a`; `h` any
  invariant `1`-Lipschitz graph. The constant of the bound grows linearly with a bound `Z` on
  the distances `‖p₂ − h(p₁)‖`, `‖p'₂ − h(p'₁)‖`, and the bound is stated for `‖p − p'‖ ≤ 1`
  (at large distances `φ` is within `C` of the centre coordinate, `norm_sub_asymptoticPhase_le`).
* **Lipschitz continuity of the phase is not proved.** The two estimates available for merely
  Lipschitz `f`, `g` (the geometric tail `C μᴺ` and the geometric Lipschitz growth `λᴺ` of the
  finite-horizon phases) can only be balanced, which gives the exponent `θ` (equal to `1` only
  for `λ = 1`). A Lipschitz phase needs Lipschitz bounds on the increments `φ_{N+1} − φ_N`, i.e.
  on differences of differences of `f` along pairs of orbits; these are available for `f`, `g` of
  class `C¹` with Lipschitz derivatives under a bunching condition of the type
  `(b + 2ε)(α + ε) < (a − ε)²` (`μ λ < 1`), and they also need the graph `h` and the inverse of
  the reduced map to be `C¹` with Lipschitz derivatives. The `C¹` theory of the centre manifold
  and of its stable fibres is not formalized in the library, so no Lipschitz statement is made;
  without bunching, stable foliations are in general only Hölder even for smooth maps.
* Generic; nothing here describes a physical system (foundation).

Source: Hirsch, Pugh and Shub, *Invariant Manifolds* (LNM 583, 1977) (Hölder continuity of
invariant foliations with an exponent from the ratio of the rates; `C¹` fibres under bunching);
Hasselblatt, "Regularity of the Anosov splitting and of horospheric foliations", Ergodic Theory
Dynam. Systems 14 (1994) (Hölder exponents as ratios of logarithms of contraction and expansion
rates); Hasselblatt and Wilkinson, "Prevalence of non-Lipschitz Anosov foliations", Ergodic
Theory Dynam. Systems 19 (1999); Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2
(the asymptotic phase); the open item of `theorem/Map/AsymptoticPhase.lean` (Scope: "Lipschitz
dependence of the phase on `p` is not proved").

Results.
* `holderExponent` (`θ`), `holderExponent_pos_le_one` (`0 < θ ≤ 1`), `tendsto_holderExponent`
  (`θ(ε) → log(a/b)/log(α/b)` as `ε → 0`), `tendsto_holderExponent_self` (`→ 1` for `a = α`).
* `norm_splitMap_sub_le` (`F` is `(α + ε)`-Lipschitz), `norm_iterate_splitMap_sub_le`,
  `norm_phaseApprox_sub_phaseApprox_le` (`(a − ε)ᴺ ‖φ_N(p) − φ_N(p')‖ ≤ (α + ε)ᴺ ‖p − p'‖`).
* **The theorem** `norm_asymptoticPhase_sub_le_rpow`:
  `‖φ(p) − φ(p')‖ ≤ (2εZ/(a − b − 3ε) + (α + ε)/(a − ε)) ‖p − p'‖^θ`.

Corrections.
None: an extension (the regularity of the asymptotic phase beyond continuity, which
`theorem/Map/AsymptoticPhase.lean` left open).

Family and connection conclusions.
None: static evidence on maps.
-/

noncomputable section

open Filter Topology

namespace powerlib.Map.CenterManifold

/-- The Hölder exponent of the asymptotic phase:
`θ = log((a − ε)/(b + 2ε)) / log((α + ε)/(b + 2ε))`, i.e. `log(1/μ)/log(λ/μ)` with the rate
`μ = (b + 2ε)/(a − ε)` of the finite-horizon phases and their Lipschitz growth
`λ = (α + ε)/(a − ε)`. -/
def holderExponent (a b α ε : ℝ) : ℝ :=
  Real.log ((a - ε) / (b + 2 * ε)) / Real.log ((α + ε) / (b + 2 * ε))

/-- The exponent lies in `(0, 1]` when `0 < b + 2ε`, `b + 3ε < a ≤ α`, `0 ≤ ε`. -/
@[tmio T, powerlib_foundation] theorem holderExponent_pos_le_one {a b α ε : ℝ} (hε : 0 ≤ ε)
    (hb2 : 0 < b + 2 * ε) (hgap : b + 3 * ε < a) (haα : a ≤ α) :
    0 < holderExponent a b α ε ∧ holderExponent a b α ε ≤ 1 := by
  have hpos : 0 < a - ε := by linarith
  have hL₁ : 0 < Real.log ((a - ε) / (b + 2 * ε)) :=
    Real.log_pos (by rw [one_lt_div hb2]; linarith)
  have hle : Real.log ((a - ε) / (b + 2 * ε)) ≤ Real.log ((α + ε) / (b + 2 * ε)) :=
    Real.log_le_log (div_pos hpos hb2) (div_le_div_of_nonneg_right (by linarith) hb2.le)
  exact ⟨div_pos hL₁ (hL₁.trans_le hle), (div_le_one (hL₁.trans_le hle)).mpr hle⟩

/-- **The exponent as the nonlinearity vanishes:** for `0 < b < a ≤ α`,
`θ(ε) → log(a/b)/log(α/b)` as `ε → 0`; for an isometric centre part (`a = α`, e.g. the multiplier
`−1`, `A = −id`) the limit is `1`, so the phase of the cut-off map of a small enough
neighbourhood is Hölder of every order below one. -/
@[tmio T, powerlib_foundation] theorem tendsto_holderExponent {a b α : ℝ} (hb : 0 < b)
    (hba : b < a) (haα : a ≤ α) :
    Tendsto (fun ε => holderExponent a b α ε) (𝓝 0)
      (𝓝 (Real.log (a / b) / Real.log (α / b))) := by
  have ha : 0 < a := hb.trans hba
  have hα : 0 < α := ha.trans_le haα
  have hlog : Real.log (α / b) ≠ 0 :=
    (Real.log_pos (by rw [one_lt_div hb]; linarith)).ne'
  have hd : Tendsto (fun ε : ℝ => b + 2 * ε) (𝓝 0) (𝓝 b) := by
    simpa using (tendsto_const_nhds (x := b)).add ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2)
  have h1 : Tendsto (fun ε : ℝ => (a - ε) / (b + 2 * ε)) (𝓝 0) (𝓝 (a / b)) := by
    have hn : Tendsto (fun ε : ℝ => a - ε) (𝓝 0) (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact hn.div hd hb.ne'
  have h2 : Tendsto (fun ε : ℝ => (α + ε) / (b + 2 * ε)) (𝓝 0) (𝓝 (α / b)) := by
    have hn : Tendsto (fun ε : ℝ => α + ε) (𝓝 0) (𝓝 α) := by
      simpa using (tendsto_const_nhds (x := α)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact hn.div hd hb.ne'
  exact (h1.log (div_pos ha hb).ne').div (h2.log (div_pos hα hb).ne') hlog

/-- For an isometric centre part (`a = α`) the Hölder exponent tends to `1` as `ε → 0`. -/
@[tmio T, powerlib_foundation] theorem tendsto_holderExponent_self {a b : ℝ} (hb : 0 < b)
    (hba : b < a) : Tendsto (fun ε => holderExponent a b a ε) (𝓝 0) (𝓝 1) := by
  have h := tendsto_holderExponent hb hba le_rfl
  rwa [div_self (Real.log_pos (by rw [one_lt_div hb]; linarith)).ne'] at h

section Regularity

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

variable {A : X →L[ℝ] X} {B : Y →L[ℝ] Y} {f : X × Y → X} {g : X × Y → Y} {a b α : ℝ}
  {ε : NNReal} {h : X → Y}

/-- **The split map is Lipschitz** with constant `α + ε` when `‖A x‖ ≤ α ‖x‖`, `‖B y‖ ≤ b ‖y‖`,
`0 ≤ b ≤ α` and `f`, `g` are `ε`-Lipschitz (max norm on `X × Y`). -/
@[tmio T, powerlib_foundation] theorem norm_splitMap_sub_le (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hbα : b ≤ α) (hf : LipschitzWith ε f)
    (hg : LipschitzWith ε g) (p p' : X × Y) :
    ‖splitMap A B f g p - splitMap A B f g p'‖ ≤ (α + ε) * ‖p - p'‖ := by
  have hα : 0 ≤ α := hb.trans hbα
  have h1 : ‖p.1 - p'.1‖ ≤ ‖p - p'‖ := norm_fst_le (p - p')
  have h2 : ‖p.2 - p'.2‖ ≤ ‖p - p'‖ := norm_snd_le (p - p')
  have hfl : ‖f p - f p'‖ ≤ ε * ‖p - p'‖ := hf.norm_sub_le p p'
  have hgl : ‖g p - g p'‖ ≤ ε * ‖p - p'‖ := hg.norm_sub_le p p'
  rw [Prod.norm_def]
  simp only [splitMap, Prod.fst_sub, Prod.snd_sub]
  refine max_le ?_ ?_
  · calc ‖A p.1 + f p - (A p'.1 + f p')‖ = ‖A (p.1 - p'.1) + (f p - f p')‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ α * ‖p.1 - p'.1‖ + ε * ‖p - p'‖ := (norm_add_le _ _).trans (add_le_add (hAα _) hfl)
      _ ≤ α * ‖p - p'‖ + ε * ‖p - p'‖ := by gcongr
      _ = (α + ε) * ‖p - p'‖ := by ring
  · calc ‖B p.2 + g p - (B p'.2 + g p')‖ = ‖B (p.2 - p'.2) + (g p - g p')‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ b * ‖p.2 - p'.2‖ + ε * ‖p - p'‖ := (norm_add_le _ _).trans (add_le_add (hB _) hgl)
      _ ≤ α * ‖p - p'‖ + ε * ‖p - p'‖ := by gcongr
      _ = (α + ε) * ‖p - p'‖ := by ring

/-- Iterates of the split map: `‖Fᴺ p − Fᴺ p'‖ ≤ (α + ε)ᴺ ‖p − p'‖`. -/
@[tmio T, powerlib_foundation] theorem norm_iterate_splitMap_sub_le
    (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hbα : b ≤ α)
    (hf : LipschitzWith ε f) (hg : LipschitzWith ε g) (N : ℕ) (p p' : X × Y) :
    ‖(splitMap A B f g)^[N] p - (splitMap A B f g)^[N] p'‖ ≤ (α + ε) ^ N * ‖p - p'‖ := by
  have h0 : 0 ≤ α + ε := by have := ε.coe_nonneg; linarith
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    calc _ ≤ (α + ε) * ‖(splitMap A B f g)^[N] p - (splitMap A B f g)^[N] p'‖ :=
          norm_splitMap_sub_le hAα hB hb hbα hf hg _ _
      _ ≤ (α + ε) * ((α + ε) ^ N * ‖p - p'‖) := mul_le_mul_of_nonneg_left ih h0
      _ = _ := by ring

variable [CompleteSpace X]

/-- **The finite-horizon phases are Lipschitz**, with constants growing geometrically:
`(a − ε)ᴺ ‖φ_N(p) − φ_N(p')‖ ≤ (α + ε)ᴺ ‖p − p'‖`. -/
@[tmio T, powerlib_foundation] theorem norm_phaseApprox_sub_phaseApprox_le
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hbα : b ≤ α) (hf : LipschitzWith ε f)
    (hg : LipschitzWith ε g) (hεa : (ε : ℝ) < a) (hh : LipschitzWith 1 h) (N : ℕ)
    (p p' : X × Y) :
    (a - ε) ^ N * ‖phaseApprox A B f g h N p - phaseApprox A B f g h N p'‖ ≤
      (α + ε) ^ N * ‖p - p'‖ := by
  refine (le_norm_iterate_invFun_sub hAs hA hf hεa hh N _ _).trans ?_
  refine le_trans ?_ (norm_iterate_splitMap_sub_le hAα hB hb hbα hf hg N p p')
  rw [← Prod.fst_sub]
  exact norm_fst_le _

/-- **The asymptotic phase is Hölder continuous.** Let `A` be onto with
`a ‖x‖ ≤ ‖A x‖ ≤ α ‖x‖` (`a ≤ α`), `‖B y‖ ≤ b ‖y‖`, `0 ≤ b`, `f`, `g` globally `ε`-Lipschitz,
`b + 3ε < a`, `0 < b + 2ε`, and `h` an invariant `1`-Lipschitz graph. For points `p`, `p'` with
`‖p₂ − h(p₁)‖, ‖p'₂ − h(p'₁)‖ ≤ Z` and `‖p − p'‖ ≤ 1`,
`‖φ(p) − φ(p')‖ ≤ (2εZ/(a − b − 3ε) + (α + ε)/(a − ε)) ‖p − p'‖^θ`,
`θ = log((a − ε)/(b + 2ε)) / log((α + ε)/(b + 2ε)) ∈ (0, 1]`.
With `μ = (b + 2ε)/(a − ε)` (the rate of the phases, `‖φ − φ_N‖ ≤ C μᴺ`) and
`λ = (α + ε)/(a − ε)` (their Lipschitz growth, `Lip φ_N ≤ λᴺ`) this is
`θ = log(1/μ)/(log(1/μ) + log λ)`: the horizon `N = ⌈log(1/‖p − p'‖)/log(λ/μ)⌉` balances the
two errors. -/
@[tmio T, powerlib_foundation] theorem norm_asymptoticPhase_sub_le_rpow
    (hAs : Function.Surjective A) (hA : ∀ x, a * ‖x‖ ≤ ‖A x‖) (hAα : ∀ x, ‖A x‖ ≤ α * ‖x‖)
    (haα : a ≤ α) (hB : ∀ y, ‖B y‖ ≤ b * ‖y‖) (hb : 0 ≤ b) (hf : LipschitzWith ε f)
    (hg : LipschitzWith ε g) (hgap : b + 3 * ε < a) (hb2 : 0 < b + 2 * ε)
    (hh : LipschitzWith 1 h) (hinv : ∀ x, h (A x + f (x, h x)) = B (h x) + g (x, h x))
    {Z : ℝ} {p p' : X × Y} (hp : ‖p.2 - h p.1‖ ≤ Z) (hp' : ‖p'.2 - h p'.1‖ ≤ Z)
    (hd : ‖p - p'‖ ≤ 1) :
    ‖asymptoticPhase A B f g h p - asymptoticPhase A B f g h p'‖ ≤
      (2 * (ε * Z / (a - b - 3 * ε)) + (α + ε) / (a - ε)) *
        ‖p - p'‖ ^ holderExponent a b α ε := by
  have hε := ε.coe_nonneg
  have hεa : (ε : ℝ) < a := by linarith
  have hpos : 0 < a - ε := by linarith
  have hgap' : 0 < a - b - 3 * ε := by linarith
  have hbα : b ≤ α := by linarith
  have hZ : 0 ≤ Z := (norm_nonneg _).trans hp
  set d := ‖p - p'‖ with hddef
  set C := ε * Z / (a - b - 3 * ε) with hC
  have hC0 : 0 ≤ C := by positivity
  set μ := (b + 2 * ε) / (a - ε) with hμ
  set lam := (α + ε) / (a - ε) with hlam
  have hμ0 : 0 < μ := div_pos hb2 hpos
  have hμ1 : μ < 1 := by rw [hμ, div_lt_one hpos]; linarith
  have hlam1 : 1 ≤ lam := by rw [hlam, one_le_div hpos]; linarith
  set L₁ := Real.log ((a - ε) / (b + 2 * ε)) with hL₁
  set L := Real.log ((α + ε) / (b + 2 * ε)) with hL
  have hlogμ : Real.log μ = -L₁ := by
    rw [hμ, hL₁, ← Real.log_inv, inv_div]
  have hloglam : Real.log lam = L - L₁ := by
    rw [hlam, hL, hL₁, ← Real.log_div (div_pos (by linarith) hb2).ne' (div_pos hpos hb2).ne']
    congr 1
    rw [div_div_div_cancel_right₀ hb2.ne']
  have hL₁0 : 0 < L₁ := by
    rw [hL₁]; exact Real.log_pos (by rw [one_lt_div hb2]; linarith)
  have hLL₁ : L₁ ≤ L := by
    have := Real.log_nonneg hlam1
    linarith
  have hL0 : 0 < L := hL₁0.trans_le hLL₁
  set θ := L₁ / L with hθ
  have hθdef : holderExponent a b α ε = θ := rfl
  rw [hθdef]
  -- the bound at every horizon
  have hN : ∀ N : ℕ, ‖asymptoticPhase A B f g h p - asymptoticPhase A B f g h p'‖ ≤
      2 * C * μ ^ N + lam ^ N * d := by
    intro N
    have h1 := norm_phaseApprox_sub_le hAs hA hB hb hf hg hgap hh hinv p N
    have h2 := norm_phaseApprox_sub_le hAs hA hB hb hf hg hgap hh hinv p' N
    have h3 := norm_phaseApprox_sub_phaseApprox_le hAs hA hAα hB hb hbα hf hg hεa hh N p p'
    have hμN : 0 ≤ μ ^ N := pow_nonneg hμ0.le N
    have h1' : ‖phaseApprox A B f g h N p - asymptoticPhase A B f g h p‖ ≤ C * μ ^ N := by
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hμN)
      rw [hC]; gcongr
    have h2' : ‖phaseApprox A B f g h N p' - asymptoticPhase A B f g h p'‖ ≤ C * μ ^ N := by
      refine h2.trans (mul_le_mul_of_nonneg_right ?_ hμN)
      rw [hC]; gcongr
    have h3' : ‖phaseApprox A B f g h N p - phaseApprox A B f g h N p'‖ ≤ lam ^ N * d := by
      have hk : 0 < (a - ε) ^ N := pow_pos hpos N
      rw [hlam, div_pow, div_mul_eq_mul_div, le_div_iff₀ hk, mul_comm]
      exact h3
    calc _ = ‖(asymptoticPhase A B f g h p - phaseApprox A B f g h N p) +
          (phaseApprox A B f g h N p - phaseApprox A B f g h N p') +
          (phaseApprox A B f g h N p' - asymptoticPhase A B f g h p')‖ := by
          congr 1; abel
      _ ≤ ‖asymptoticPhase A B f g h p - phaseApprox A B f g h N p‖ +
          ‖phaseApprox A B f g h N p - phaseApprox A B f g h N p'‖ +
          ‖phaseApprox A B f g h N p' - asymptoticPhase A B f g h p'‖ := norm_add₃_le
      _ ≤ C * μ ^ N + lam ^ N * d + C * μ ^ N := by
          rw [norm_sub_rev] at h1'
          gcongr
      _ = _ := by ring
  -- the balancing horizon
  rcases (norm_nonneg (p - p')).eq_or_lt with hd0 | hd0
  · have hpp : p = p' := sub_eq_zero.mp (norm_eq_zero.mp hd0.symm)
    rw [hpp, sub_self, norm_zero]
    have hlam0 : 0 ≤ lam := by linarith
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [← hddef] at hd0
  set x := -Real.log d / L with hx
  have hx0 : 0 ≤ x := div_nonneg (neg_nonneg.mpr (Real.log_nonpos hd0.le hd)) hL0.le
  set N := ⌈x⌉₊ with hNdef
  have hN1 : x ≤ N := Nat.le_ceil x
  have hN2 : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hdθ : d ^ θ = Real.exp (θ * Real.log d) := by
    rw [Real.rpow_def_of_pos hd0, mul_comm]
  have hμpow : μ ^ N ≤ d ^ θ := by
    rw [hdθ, ← Real.exp_log hμ0, ← Real.exp_nat_mul, Real.exp_le_exp, hlogμ]
    have : θ * Real.log d = x * (-L₁) := by
      rw [hθ, hx]; field_simp
    rw [this]
    exact mul_le_mul_of_nonpos_right hN1 (by linarith)
  have hlampow : lam ^ N * d ≤ lam * d ^ θ := by
    have hlam0 : 0 < lam := by linarith
    rw [hdθ, ← Real.exp_log hlam0, ← Real.exp_nat_mul, ← Real.exp_log hd0, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp, Real.exp_log hd0, hloglam]
    have hlL : 0 ≤ L - L₁ := by linarith
    have e1 : (x + 1) * (L - L₁) + Real.log d = (L - L₁) + θ * Real.log d := by
      rw [hθ, hx]; field_simp; ring
    calc (N : ℝ) * (L - L₁) + Real.log d ≤ (x + 1) * (L - L₁) + Real.log d := by
          gcongr
      _ = _ := e1
  calc _ ≤ 2 * C * μ ^ N + lam ^ N * d := hN N
    _ ≤ 2 * C * d ^ θ + lam * d ^ θ := by gcongr
    _ = _ := by ring

end Regularity

end powerlib.Map.CenterManifold
