import theorem.GridTiedConverter.GFM.VSMLPF
import theorem.PhasePlane.Conservative

/-! # Equilibrium count and fold of the reduced grid-forming model

Domain module.

Model boundary.
* The reduced (quasi-static line) grid-forming converter: an internal EMF `E ∠ δ` of constant
  amplitude behind the lumped series impedance `Z = R + jX` (`|Z| = √(R² + X²)`,
  `α = atan2(R, X)`) to a stiff grid `V ∠ 0`, in a dq frame rotating at the nominal frequency.
  The line current is quasi-steady, `Ī = (E e^{jδ} − V)/Z`, positive out of the converter, and
  the active power at the EMF is export-positive (GFM family exception, as in
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`): `P(δ) = Re(Ē Ī*) = c₀ + A sin(δ − α)`,
  `c₀ = E² R/|Z|²`, `A = E V/|Z|` (`Synchronous.electricalPower_eq`,
  `Synchronous.PostFaultSMIB.Pe_eq_complexPower` at grid angle `0`).
* Two states (no power filter): `x = (δ, Δω) : Dynamics.State 2` in this order, `δ̇ = Δω`,
  `M Δω̇ = P_ref − P(δ) − D Δω`: the canonical swing model
  `Synchronous.SwingParams ⟨M, D, P_ref, c₀, A, α⟩` (`P_m = P_ref`, `k₁ = c₀`, `k₂ = A`,
  `k₃ = α`). The statements hold for every `SwingParams` with `M ≠ 0` and `k₂ > 0`.
* Three states (first-order power filter, bandwidth `ω_c`): the model `VSMLPF` of
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`, state `(δ, Δω, P_f)`; the lossy line enters it
  as `P₀ = P_ref − c₀`, `K₀ = A` after the shift `δ ↦ δ − α`, `P_f ↦ P_f − c₀`. Fold statements
  use the physical range `M, D, ω_c, K₀ > 0` (`VSMLPF.Pos`).
* Continuous time, autonomous; equilibrium sets per period window `[a, a + 2π)` of the angle and
  Jacobians at equilibria. Excluded: Q–V droop (constant `E`; see
  `theorem/GridTiedConverter/GFM/QVDroop.lean`), line dynamics, inner voltage and current loops,
  current limiting, PLL, delay, PWM.

Source: study note GFM equilibrium counting (topic t6 (a): count per window, classification,
fold Jacobian; checked numerically there, derived here); the power-angle curve of the lossy line
from `S̄ = Ē Ī*` as in `theorem/PowerSystem/Synchronous/Instances.lean`.

Results.
* `Reduced.zerosIco_eq`: the equilibrium angles in a window are the zeros of the sinusoid
  `(P_m − k₁) − k₂ sin(δ − k₃)` (`SpecialFunctions.sinusoidZeros`); `Reduced.equilibria_window`
  and `Reduced.ncard_equilibria_window`: the equilibria `(δ*, 0)` in the window are their images
  and as many (`PhasePlane.Conservative.equilibria_window`,
  `PhasePlane.Conservative.ncard_equilibria_window`, through
  `Synchronous.SwingParams.field_eq_conservative`).
* `Reduced.stableRoot_eq`, `Reduced.saddleRoot_eq`: the two window zeros are the library's
  branches `δ_s`, `δ_u` (`SwingParams.deltaS`, `SwingParams.deltaU`) reduced into the window.
* The count per window: `Reduced.two_equilibria_per_period` (`|P_m − k₁| < k₂`: exactly two,
  `(δ_s, 0)` and `(δ_u, 0)`), `Reduced.fold_equilibrium_per_period` (`|P_m − k₁| = k₂`: exactly
  one, the double zero `δ_s = δ_u`), `Reduced.no_equilibrium_per_period` (`|P_m − k₁| > k₂`:
  none).
* The three-state fold: `VSMLPF.K_eq_zero_of_fold` (`|P₀| = K₀` gives `K = K₀ cos δ₀ = 0`),
  `VSMLPF.fold_characteristic_polynomial` (`M det(sI − J) = s (M s + D)(s + ω_c)` at a fold angle:
  eigenvalues `0`, `−D/M`, `−ω_c`), `VSMLPF.jacobian_not_isNilpotent` (no Jacobian of the model is
  nilpotent when `D/M + ω_c ≠ 0`: the trace is `−D/M − ω_c`) and `VSMLPF.fold_jacobian` (the
  fold Jacobian is singular and not nilpotent in the physical range).
* Cited, not restated (already in the library): the two-state classification
  `SwingParams.eigenvalues_real_iff` (a node iff `D² ≥ 4 M K`, `K = k₂ cos(δ* − k₃)`),
  `Swing.deltaS_mem_den_locallyExponentiallyStable` (`δ_s`, `D > 0`) and
  `Swing.deltaU_mem_den_unstable` (`δ_u`, a saddle); the two-state fold Jacobian is not nilpotent
  for `D/M ≠ 0` (`GFL.Noise.classA_not_nilpotent`); the three-state boundary
  `VSMLPF.locallyExponentiallyStable_iff` (`K < D ω_c + D²/M`) and saddle
  `VSMLPF.unstable_atAntiLoading`.

Family and connection conclusions.
No new family and no connection conclusion: the equilibrium sets, their counts, the window
representatives and the fold Jacobians are static evidence on the models. The behavioural
conclusions about these equilibria are those of `Synchronous.Swing.family` and `VSMLPF.family`
cited above.

Correction (GFL–GFM contrast). The reduced GFL-PLL fold has the nonzero nilpotent Jacobian
`[[0, K_i], [0, 0]]` (`GFL.LCLine.Params.fold_jacobian_nilpotent`, a double zero eigenvalue). This
does not carry over to the grid-forming model: its fold eigenvalues are `0, −D/M` (two states)
and `0, −D/M, −ω_c` (three states), an ordinary saddle-node; the two-state fold Jacobian is
nilpotent only when `D = 0`.
-/

noncomputable section
namespace powerlib.GFM
open Real Set
open powerlib.Dynamics (State)
open powerlib.SpecialFunctions (zerosIco sinusoidZeros stableRoot saddleRoot)
open powerlib.Synchronous (SwingParams)

/-! ## The two-state reduced model: count per window -/

namespace Reduced

variable (p : SwingParams)

/-- The equilibrium angles in a window `[a, a + 2π)` — the zeros of the restoring force
`P_e − P_m` — are the zeros of the sinusoid `(P_m − k₁) − k₂ sin(δ − k₃)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem zerosIco_eq (a : ℝ) :
    zerosIco (fun δ => p.Pe δ - p.Pm) a (2 * π) =
      sinusoidZeros (p.Pm - p.k₁) p.k₂ (-p.k₃) a := by
  ext δ
  simp only [sinusoidZeros, zerosIco, Set.mem_ofPred_eq, SwingParams.Pe, ← sub_eq_add_neg]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by linarith⟩

/-- The equilibria with angle in a window `[a, a + 2π)` are the points `(δ*, 0)`, `δ*` a zero of
the sinusoid `(P_m − k₁) − k₂ sin(δ − k₃)` in the window (`M ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibria_window (hM : p.M ≠ 0) (a : ℝ) :
    {x : State 2 | p.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π)} =
      (fun δ => PhasePlane.mk δ 0) '' sinusoidZeros (p.Pm - p.k₁) p.k₂ (-p.k₃) a := by
  rw [p.field_eq_conservative, PhasePlane.Conservative.equilibria_window hM, zerosIco_eq]

/-- Counting law: the equilibria with angle in a window `[a, a + 2π)` are as many as the zeros of
the sinusoid `(P_m − k₁) − k₂ sin(δ − k₃)` there (`M ≠ 0`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem ncard_equilibria_window (hM : p.M ≠ 0) (a : ℝ) :
    {x : State 2 | p.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π)}.ncard =
      (sinusoidZeros (p.Pm - p.k₁) p.k₂ (-p.k₃) a).ncard := by
  rw [p.field_eq_conservative, PhasePlane.Conservative.ncard_equilibria_window hM, zerosIco_eq]

/-- The window zero `stableRoot` is the stable branch `δ_s = arcsin a + k₃` reduced into the
window. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem stableRoot_eq (a : ℝ) :
    stableRoot (p.Pm - p.k₁) p.k₂ (-p.k₃) a = toIcoMod two_pi_pos a p.deltaS := by
  simp only [SpecialFunctions.stableRoot, SwingParams.deltaS, SwingParams.loadRatio,
    sub_neg_eq_add]

/-- The window zero `saddleRoot` is the saddle branch `δ_u = π − arcsin a + k₃` reduced into the
window. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem saddleRoot_eq (a : ℝ) :
    saddleRoot (p.Pm - p.k₁) p.k₂ (-p.k₃) a = toIcoMod two_pi_pos a p.deltaU := by
  simp only [SpecialFunctions.saddleRoot, SwingParams.deltaU, SwingParams.loadRatio,
    sub_neg_eq_add]

/-- `|P_m − k₁| < k₂`: in every window `[a, a + 2π)` exactly two equilibria, `(δ_s, 0)` and
`(δ_u, 0)` reduced into the window (`SpecialFunctions.ncard_sinusoidZeros_of_lt`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem two_equilibria_per_period (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) (a : ℝ) :
    {x : State 2 | p.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π)}.ncard = 2 ∧
      {x : State 2 | p.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π)} =
        {PhasePlane.mk (toIcoMod two_pi_pos a p.deltaS) 0,
          PhasePlane.mk (toIcoMod two_pi_pos a p.deltaU) 0} := by
  refine ⟨?_, ?_⟩
  · rw [ncard_equilibria_window p hM, SpecialFunctions.ncard_sinusoidZeros_of_lt h hk]
  · rw [equilibria_window p hM, SpecialFunctions.sinusoidZeros_eq h.le hk, Set.image_pair,
      stableRoot_eq, saddleRoot_eq]

/-- `|P_m − k₁| = k₂` (fold of the power-angle curve): in every window exactly one equilibrium,
the double zero `δ_s = δ_u` (`SpecialFunctions.ncard_sinusoidZeros_of_eq`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fold_equilibrium_per_period (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| = p.k₂) (a : ℝ) :
    {x : State 2 | p.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π)}.ncard = 1 ∧
      {x : State 2 | p.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π)} =
        {PhasePlane.mk (toIcoMod two_pi_pos a p.deltaS) 0} := by
  refine ⟨?_, ?_⟩
  · rw [ncard_equilibria_window p hM, SpecialFunctions.ncard_sinusoidZeros_of_eq h hk]
  · rw [equilibria_window p hM, SpecialFunctions.sinusoidZeros_eq h.le hk,
      ← SpecialFunctions.stableRoot_eq_saddleRoot h hk, Set.pair_eq_singleton,
      Set.image_singleton, stableRoot_eq]

/-- `|P_m − k₁| > k₂`: no equilibrium in any window (`SpecialFunctions.sinusoidZeros_eq_empty`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem no_equilibrium_per_period (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : p.k₂ < |p.Pm - p.k₁|) (a : ℝ) :
    {x : State 2 | p.field x = 0 ∧ x 0 ∈ Ico a (a + 2 * π)} = ∅ := by
  rw [equilibria_window p hM, SpecialFunctions.sinusoidZeros_eq_empty hk.le h, Set.image_empty]

end Reduced

/-! ## The three-state model at the fold -/

namespace VSMLPF

variable (g : VSMLPF)

/-- At the loadability limit `|P₀| = K₀` the loading angle is a fold of the power curve:
`cos δ₀ = 0`, so the synchronizing coefficient vanishes, `K = K₀ cos δ₀ = 0`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem K_eq_zero_of_fold (hK0 : 0 < g.K0) (h : |g.P0| = g.K0) :
    g.K = 0 := by
  rw [K, δ0, Real.cos_arcsin, SpecialFunctions.sqrt_one_sub_sq_eq_zero h hK0, mul_zero]

/-- At a fold angle (`K₀ cos δ = 0`) the characteristic polynomial factors as
`M det(sI − J) = s (M s + D)(s + ω_c)`: the eigenvalues are `0`, `−D/M` and `−ω_c`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fold_characteristic_polynomial (hM : g.M ≠ 0) {δ : ℝ}
    (hK : g.K0 * Real.cos δ = 0) (s : ℂ) :
    (g.M : ℂ) * (Linear.characteristicMatrix (g.jacobian δ) s).det =
      s * ((g.M : ℂ) * s + (g.D : ℂ)) * (s + (g.ωc : ℂ)) := by
  rw [g.characteristic_polynomial hM δ s, hK]
  push_cast
  ring

/-- No Jacobian of the three-state model is nilpotent when `D/M + ω_c ≠ 0`: its trace is
`−D/M − ω_c`, and a nilpotent matrix has trace zero.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem jacobian_not_isNilpotent (h : g.D / g.M + g.ωc ≠ 0) (δ : ℝ) :
    ¬ IsNilpotent (g.jacobian δ) := by
  intro hn
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hn).eq_zero
  rw [trace_jacobian, neg_div] at ht
  exact h (by linarith)

/-- The three-state fold (`|P₀| = K₀`, positive `M, D, ω_c, K₀`): the Jacobian at the loading
angle is singular (`det J = 0`, the eigenvalue `0`) but not nilpotent (the eigenvalues `−D/M`,
`−ω_c` stay in the left half plane): an ordinary saddle-node, unlike the GFL fold.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fold_jacobian (hp : g.Pos) (h : |g.P0| = g.K0) :
    (g.jacobian g.δ0).det = 0 ∧ ¬ IsNilpotent (g.jacobian g.δ0) := by
  refine ⟨?_, g.jacobian_not_isNilpotent (add_pos (div_pos hp.D hp.M) hp.ωc).ne' _⟩
  have hK : g.K0 * Real.cos g.δ0 = 0 := g.K_eq_zero_of_fold hp.K0 h
  rw [det_jacobian, hK, mul_zero, neg_zero, zero_div]

end VSMLPF

end powerlib.GFM
