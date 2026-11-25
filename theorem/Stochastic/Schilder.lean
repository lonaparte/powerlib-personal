import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.BrownianMaximal
import theorem.Stochastic.SchilderGood
import theorem.Stochastic.ExpApprox
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Schilder's theorem

For a Brownian motion `B` (Mathlib's `IsBrownianReal`) and a measurable path-space version `X` of
it on `[0, T]` (`exists_version`), the laws of `√ε X` on `C([0, T], ℝ)` satisfy the
large-deviation principle as `ε → 0⁺` with the good rate `½ ∫₀ᵀ ẇ²` on `H¹₀` and `∞` elsewhere
(`schilderRate`).

Scope.
* Probability theory, not an engineering result. Paths in `C([0, T], ℝ)` written
  `C([0, T], Fin 1 → ℝ)` (the noise space of `theorem/Stochastic/AdditiveNoise.lean`), `T > 0`,
  Borel sets.
* Proof (Dembo–Zeitouni Thm 5.2.3): the polygonal interpolations `√ε π_n X` satisfy the principle
  with the Schilder rate on polygonal paths (`isLDP_polygon`); they are exponentially good
  approximations of `√ε X` (`expApprox_polyInterp`, from the Gaussian maximal inequality); the
  Schilder rate is good and lower semicontinuous (`isGoodRate_schilderRate`), is at most the
  polygonal rates, and every path of finite rate is the uniform limit of its interpolations, whose
  rates do not exceed it (`tendsto_polyInterp`, `schilderRate_polyInterp_le`); the transfer is
  `isLDP_of_expApprox`.

Source: M. Schilder, *Some asymptotic formulas for Wiener integrals*, Trans. AMS 125 (1966);
A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998),
Thm 5.2.3 and Thm 4.2.16.

Results.
* `isLDP_schilder`: **Schilder's theorem** for any measurable path-space version of a Brownian
  motion; `exists_isLDP_schilder`: such a version exists, so the statement is not vacuous.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- `polyPath` is linear in the increments: `polyPath (c • y) = c • polyPath y`. -/
@[tmio T, powerlib_foundation] theorem polyPath_smul {n : ℕ} (c : ℝ) (y : Fin n → ℝ) :
    polyPath T n (c • y) = c • polyPath T n y := by
  ext t j
  simp only [polyPath, ContinuousMap.coe_mk, ContinuousMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  have : ∑ k : Fin n, c * y k * ramp (mesh T n) ((k : ℕ) * mesh T n) t =
      c * ∑ k : Fin n, y k * ramp (mesh T n) ((k : ℕ) * mesh T n) t := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]; ring

/-- **Schilder's theorem**: for a Brownian motion `B` and a measurable path-space version `X`
(`X(ω)(t) = B_t(ω)` for almost every `ω`), the laws of `√ε X` on `C([0, T])` satisfy the
large-deviation principle as `ε → 0⁺` with the good rate `schilderRate T = ½ ∫ ẇ²`. -/
@[tmio T, powerlib_foundation] theorem isLDP_schilder (hB : IsBrownianReal B P)
    (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)}
    (hX : Measurable X) (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) :
    IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map fun ω => √ε • X ω) (schilderRate T) := by
  have hB' := hB.toIsPreBrownianReal
  set In : ℕ → C(Icc (0 : ℝ) T, Fin 1 → ℝ) → ℝ≥0∞ := fun n w =>
    if w ∈ range (polyPath T (n + 1)) then schilderRate T w else ⊤ with hIn
  set Z : ℝ → Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ) := fun ε ω => √ε • X ω with hZ
  set Zn : ℕ → ℝ → Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ) :=
    fun n ε ω => √ε • polyInterp T (n + 1) (X ω) with hZn
  have hZm : ∀ ε, Measurable (Z ε) := fun ε => by exact hX.const_smul (√ε)
  have hZnm : ∀ n ε, Measurable (Zn n ε) := fun n ε => by
    exact (continuous_polyInterp.measurable.comp hX).const_smul (√ε)
  have hLDP : ∀ n, IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map (Zn n ε)) (In n) := by
    intro n
    refine (isLDP_polygon hB' hT (Nat.succ_pos n)).congr ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine Measure.map_congr ?_
    filter_upwards [hXB] with ω hω
    simp only [hZn, polyInterp]
    rw [← polyPath_smul]
    congr 1
    funext k
    have hk := k.2
    simp only [Pi.smul_apply, smul_eq_mul, nodeIncr, polyNoise]
    rw [pathExt_of_mem _ (node_mem (Nat.succ_pos n) hk),
      pathExt_of_mem _ (node_mem (Nat.succ_pos n) hk.le), hω, hω]
    have hη : ∀ (y : ℝ≥0) (h : 0 ≤ (y : ℝ)), (⟨(y : ℝ), h⟩ : ℝ≥0) = y := fun y h => rfl
    simp only [hη]
    ring
  have hle : ∀ n x, schilderRate T x ≤ In n x := by
    intro n x
    simp only [hIn]
    split_ifs
    · exact le_rfl
    · exact le_top
  have happ : ∀ x, schilderRate T x ≠ ⊤ → ∀ δ > 0, ∃ n₀, ∀ n ≥ n₀,
      ∃ y, dist y x < δ ∧ In n y ≤ schilderRate T x := by
    intro x hx δ hδ
    have h0 := pathExt_zero_of_schilderRate_ne_top hx
    have ht := (tendsto_polyInterp hT x h0).comp (tendsto_add_atTop_nat 1)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (ht.eventually (Metric.ball_mem_nhds x hδ))
    refine ⟨n₀, fun n hn => ⟨polyInterp T (n + 1) x, hn₀ n hn, ?_⟩⟩
    simp only [hIn, polyInterp, mem_range, exists_apply_eq_apply, ↓reduceIte]
    exact schilderRate_polyInterp_le hT (Nat.succ_pos n) x
  have hexp : ∀ δ > 0, ∀ M : ℝ, ∃ n₀, ∀ n ≥ n₀, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((ε : ℝ) : EReal) * ENNReal.log (P {ω | δ < dist (Zn n ε ω) (Z ε ω)}) ≤ M := by
    intro δ hδ M
    obtain ⟨n₀, hn₀⟩ := expApprox_polyInterp hB' hXB hT δ hδ M
    exact ⟨n₀, fun n hn => hn₀ (n + 1) (by omega)⟩
  exact isLDP_of_expApprox hZm hZnm (lowerSemicontinuous_schilderRate hT)
    (isGoodRate_schilderRate hT) hLDP hle happ hexp

/-- **Schilder's theorem, existence form**: every Brownian motion has a measurable path-space
version `X` on `[0, T]`, and the laws of `√ε X` satisfy the large-deviation principle with the
rate `schilderRate T`. -/
@[tmio T, powerlib_foundation] theorem exists_isLDP_schilder (hB : IsBrownianReal B P)
    (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] :
    ∃ X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ), Measurable X ∧
      (∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) ∧
      IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map fun ω => √ε • X ω) (schilderRate T) := by
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT
  exact ⟨X, hX, hXB, isLDP_schilder hB hT hX hXB⟩

end powerlib.Stochastic.LDP
