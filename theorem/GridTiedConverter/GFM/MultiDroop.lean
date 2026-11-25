import theorem.GridTiedConverter.GFM.DroopAlgebra
import theorem.PowerSystem.Network.Swing.Degenerate
import theorem.Family.Reading

/-! # N droop units on a network: power sharing and the stability of the synchronous state

Model boundary.
* `N` grid-forming units with droop + first-order power filter, state
  `x = (θ, P_f) ∈ (Fin N → ℝ) × (Fin N → ℝ)` (unit angles in a frame rotating at an arbitrary
  constant speed, filtered powers):
  `θ̇_k = ω_s − (P_{f,k} − P*_k)/K_{R,k}`, `τ_k Ṗ_{f,k} = P_k(θ) − P_{f,k}`.
* Network: an arbitrary static map `P : (Fin N → ℝ) → (Fin N → ℝ)` (export-positive unit
  powers) that depends only on angle differences (`P (θ + c·1) = P θ`); for the frequency
  formula, additionally a constant total load `Σ_k P_k(θ) = P_L` (lossless network with
  constant-power loads).  Continuous time; no voltage loops, inner loops, PLL, limiters.
* A *synchronous steady state* is a solution of the form `θ(t) = θ₀ + ω t · 1`,
  `P_f(t) ≡ P_{f0}` — an equilibrium of the closed loop in the frame rotating with the common
  frequency `ω`.
* Stability (`MultiDroop.Net`, `N = n + 1`): the network is lossless and Kron-reduced with
  constant-power local loads, `P_k(θ) = P_{L,k} + ∑ⱼ Bₖⱼ sin(θₖ − θⱼ)` (`Bₖⱼ = Bⱼₖ ≥ 0`,
  constant voltage magnitudes), gains `K_{R,k} > 0`, filters `τ_k > 0`. Reduced state, order
  `Fin (n + (n + 1))`: relative angles `δᵢ = θ_{i+1} − θ₀`, then the filtered powers (the
  rotation `θ + c·1` is removed). The selected state of a model is its angle profile `θ*` with
  every droop frequency at the synchronous frequency `Ω = ω_s + (Σ P* − Σ P_L)/Σ K_R`.

Source: work-sync `theory/T-droop-control.md` §1.6–§1.8; `theory/T-gfm-control.md` §2.3;
`theory/T-synchronization-manifold.md` §1.7 (the swing network the units are read as).

Results.
The rotating curve's initial state is a relative equilibrium — the field there is the
uniform rotation `(ω·1, 0)` — iff `P_{f0} = P(θ₀)` and every unit's droop frequency equals `ω`
(`relativeEquilibrium_iff`); then every unit obeys `ΔP_k = −K_{R,k} (ω − ω_s)`
(`synchronous_sharing`), the common frequency is `ω = ω_s − (P_L − Σ P*)/Σ K` (consensus
formula, `steadyState_frequency` with `D_eff = 0`), and the per-rating shares are equal iff
`K_{R,k} ∝ S_{N,k}`.
Units on a lossless network (static): `Net.reducedField_reduce` (the reduction intertwines the
units' field and the reduced field), `Net.sum_toSwing_P`, `Model.relativeEquilibrium_iff_balanced`
(at a balanced profile the selected state is the relative equilibrium rotating at `Ω`), and
`Net.swing_reducedField_eq_transport`: in the coordinates `(δ, ω_s − Ω − (P_f − P*)/K_R)` the
reduced field is the reduced swing-network field (`Network.Swing.reducedField`) with inertia
`τ K_R`, damping `K_R` and power `P* − P_L + K_R(ω_s − Ω)` (`Net.toSwing`).
`isHurwitz_jacobian_iff` (the exact Laplacian test of the swing network): the reduced swing
Jacobian at `θ` is Hurwitz iff `A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)² > 0` for every nonzero
grounded `u`, i.e. the Laplacian of `Bₖⱼ cos(θₖ − θⱼ)` is positive definite on `u₀ = 0`
(necessity added here to `Network.Swing.jacobian_isHurwitz_of_hessForm`).

Family and connection conclusions.
* `family : Family (Model n) Spectral.Requirement (n + (n + 1)) 0` reads a droop network with an
  angle profile as its reduced field translated to the selected state (`Spectral.localFamily`).
  Stability condition: `Balanced` (`P_{L,k} + ∑ⱼ Bₖⱼ sin(θ*ₖ − θ*ⱼ) = P*ₖ + K_{R,k}(ω_s − Ω)`) and
  `Synchronizing` (the Laplacian test above at `θ*`); instability condition: balance and a root
  of the reduced swing Jacobian in the open right half plane.
* `mem_den_iff_swing` (connection comparison): for every sentence a model satisfies it exactly
  when its swing network `Model.toSwing` does (`Spectral.mem_den_flow_iff_of_hub_transport`,
  `Spectral.mem_den_iff_of_flow`). Scaffold: `theorem/GridTiedConverter/GFM/MultiDroopSwing.agda`.
* `mem_den_locallyExponentiallyStable_iff`: the synchronous state is locally exponentially stable
  exactly when the profile is balanced and the Laplacian of `Bₖⱼ cos(θ*ₖ − θ*ⱼ)` is positive
  definite on the grounded directions, for all positive droop gains and filter constants
  (`exact_locallyExponentiallyStable`; soundness `chain_le_semantics`);
  `mem_den_locallyExponentiallyStable_of_angle` (static sufficient condition: coupled angle
  differences below `π/2` on a connected network);
  `mem_den_locallyAsymptoticallyStable_iff` (complete characterization: balance, a strict local
  minimum of the network potential in relative angles, and an isolated balanced profile — the
  swing network's `Network.Swing.mem_den_locallyAsymptoticallyStable_iff`). The local asymptotic
  translation is therefore not exact from five units on (`Network.Swing` DegenerateRing).
* For the arbitrary network map a synchronous steady state is a relative equilibrium
  (an equilibrium of the closed loop in the frame rotating with `ω`), characterized by static
  conditions exactly as an equilibrium set is characterized; the sharing, frequency and
  proportional-sharing formulas take this static condition as their premise and are static
  evidence on the model (domain), not connection conclusions.  That the rotating curve is then
  a solution of the field (`synchronous_solution_iff`) is trajectory-level and kept as private
  implementation evidence (Rules §3a).  Stability for an arbitrary (lossy, voltage-dependent)
  network map is not formalized: only the lossless Kron-reduced network has a family.
-/

noncomputable section
namespace powerlib.GFM

/-- Parameters of `N` droop + LPF units on a static network. -/
structure MultiDroop (N : ℕ) where
  KR : Fin N → ℝ
  τ : Fin N → ℝ
  Pstar : Fin N → ℝ
  ωs : ℝ
  P : (Fin N → ℝ) → (Fin N → ℝ)

namespace MultiDroop

variable {N : ℕ} (m : MultiDroop N)

/-- Closed-loop field on `(θ, P_f)`. -/
def field (x : (Fin N → ℝ) × (Fin N → ℝ)) : (Fin N → ℝ) × (Fin N → ℝ) :=
  (fun k => m.ωs - (x.2 k - m.Pstar k) / m.KR k, fun k => (m.P x.1 k - x.2 k) / m.τ k)

/-- The uniformly rotating candidate `t ↦ (θ₀ + ω t · 1, P_{f0})`. -/
def syncCurve (θ₀ Pf₀ : Fin N → ℝ) (ω : ℝ) (t : ℝ) : (Fin N → ℝ) × (Fin N → ℝ) :=
  (fun k => θ₀ k + ω * t, Pf₀)

@[tmio M, powerlib_domain] theorem hasDerivAt_syncCurve (θ₀ Pf₀ : Fin N → ℝ) (ω t : ℝ) :
    HasDerivAt (syncCurve θ₀ Pf₀ ω) ((fun _ => ω), (0 : Fin N → ℝ)) t := by
  apply HasDerivAt.prodMk
  · apply hasDerivAt_pi.mpr
    intro k
    simpa using ((hasDerivAt_id t).const_mul ω).const_add (θ₀ k)
  · exact hasDerivAt_const _ _

/-- The rotating candidate's initial state is a relative equilibrium — the field there is the
uniform rotation `(ω·1, 0)` — iff the filtered powers equal the network powers and every unit's
droop frequency equals the common frequency `ω`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem relativeEquilibrium_iff (hτ : ∀ k, m.τ k ≠ 0)
    (θ₀ Pf₀ : Fin N → ℝ) (ω : ℝ) :
    m.field (θ₀, Pf₀) = ((fun _ => ω), (0 : Fin N → ℝ)) ↔
      (∀ k, Pf₀ k = m.P θ₀ k) ∧ ∀ k, m.ωs - (Pf₀ k - m.Pstar k) / m.KR k = ω := by
  simp only [field, Prod.mk.injEq, funext_iff, Pi.zero_apply, div_eq_zero_iff, hτ, or_false,
    sub_eq_zero]
  exact ⟨fun h => ⟨fun k => (h.2 k).symm, h.1⟩, fun h => ⟨h.2, fun k => (h.1 k).symm⟩⟩

/-- A uniformly rotating curve is a solution iff the filtered powers equal the network powers
and every unit's droop frequency equals the common frequency `ω`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem synchronous_solution_iff (hτ : ∀ k, m.τ k ≠ 0)
    (hshift : ∀ θ c, m.P (fun k => θ k + c) = m.P θ) (θ₀ Pf₀ : Fin N → ℝ) (ω : ℝ) :
    (∀ t, HasDerivAt (syncCurve θ₀ Pf₀ ω) (m.field (syncCurve θ₀ Pf₀ ω t)) t) ↔
      (∀ k, Pf₀ k = m.P θ₀ k) ∧ ∀ k, m.ωs - (Pf₀ k - m.Pstar k) / m.KR k = ω := by
  have hval : ∀ t, m.field (syncCurve θ₀ Pf₀ ω t) = m.field (θ₀, Pf₀) := by
    intro t
    simp only [field, syncCurve]
    rw [hshift θ₀ (ω * t)]
  rw [← m.relativeEquilibrium_iff hτ θ₀ Pf₀ ω]
  constructor
  · intro h
    rw [← hval 0]
    exact (h 0).unique (hasDerivAt_syncCurve θ₀ Pf₀ ω 0)
  · intro h t
    rw [hval t, h]
    exact hasDerivAt_syncCurve θ₀ Pf₀ ω t

/-- In a synchronous steady state (a relative equilibrium) every unit shares
`ΔP_k = P_k − P*_k = −K_{R,k} (ω − ω_s)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem synchronous_sharing (hτ : ∀ k, m.τ k ≠ 0) (hK : ∀ k, m.KR k ≠ 0)
    {θ₀ Pf₀ : Fin N → ℝ} {ω : ℝ}
    (hsync : m.field (θ₀, Pf₀) = ((fun _ => ω), (0 : Fin N → ℝ))) :
    ∀ k, m.P θ₀ k - m.Pstar k = -m.KR k * (ω - m.ωs) := by
  obtain ⟨h1, h2⟩ := (m.relativeEquilibrium_iff hτ θ₀ Pf₀ ω).mp hsync
  intro k
  have := h2 k
  rw [h1 k] at this
  have hk := hK k
  field_simp at this ⊢
  linarith

/-- The common frequency of any synchronous steady state is
`ω = ω_s − (P_L − Σ P*_k)/Σ K_{R,k}` when the network delivers the constant total load `P_L`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem synchronous_frequency (hτ : ∀ k, m.τ k ≠ 0)
    (hK : ∀ k, m.KR k ≠ 0) {PL : ℝ}
    (hload : ∀ θ, ∑ k, m.P θ k = PL) (hsum : ∑ k, m.KR k ≠ 0) {θ₀ Pf₀ : Fin N → ℝ} {ω : ℝ}
    (hsync : m.field (θ₀, Pf₀) = ((fun _ => ω), (0 : Fin N → ℝ))) :
    ω = m.ωs - (PL - ∑ k, m.Pstar k) / ∑ k, m.KR k := by
  have hs := m.synchronous_sharing hτ hK hsync
  have h := steadyState_frequency m.KR (fun k => m.P θ₀ k - m.Pstar k) (Δω := ω - m.ωs)
    (ΔPL := PL - ∑ k, m.Pstar k) (Deff := 0) (by rwa [add_zero])
    (fun k => by have := hs k; linarith) (by rw [Finset.sum_sub_distrib, hload θ₀]; ring)
  rw [add_zero, neg_div] at h
  linarith

/-- Proportional (per-rating) sharing in a synchronous steady state off nominal frequency holds
iff the droop gains are proportional to the ratings.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem synchronous_proportionalSharing_iff (hτ : ∀ k, m.τ k ≠ 0)
    (hK : ∀ k, m.KR k ≠ 0) (S : Fin N → ℝ)
    (hS : ∀ k, S k ≠ 0) {θ₀ Pf₀ : Fin N → ℝ} {ω : ℝ} (hω : ω ≠ m.ωs)
    (hsync : m.field (θ₀, Pf₀) = ((fun _ => ω), (0 : Fin N → ℝ))) :
    (∃ ρ, ∀ k, (m.P θ₀ k - m.Pstar k) / S k = ρ) ↔ ∃ κ, ∀ k, m.KR k = κ * S k :=
  proportionalSharing_iff m.KR S (fun k => m.P θ₀ k - m.Pstar k) hS (sub_ne_zero.mpr hω)
    (m.synchronous_sharing hτ hK hsync)

open powerlib.Network.Swing (dIdx wIdx ground angleMap reduce hessForm)
open powerlib.Grid (powerInjection flowWeights)
open powerlib.Network (laplacian)
open powerlib.Dynamics (State)
open Matrix

variable {n : ℕ}

/-! ## Units on a lossless network: the synchronous state read through the swing network -/

/-- `n + 1` droop + LPF units on a lossless Kron-reduced network with constant-power local loads:
unit `k` exports `P_{L,k} + ∑ⱼ Bₖⱼ sin(θₖ − θⱼ)`; positive droop gains and filter constants,
symmetric nonnegative couplings. -/
structure Net (n : ℕ) where
  KR : Fin (n + 1) → ℝ
  τ : Fin (n + 1) → ℝ
  Pstar : Fin (n + 1) → ℝ
  ωs : ℝ
  PL : Fin (n + 1) → ℝ
  B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
  KR_pos : ∀ k, 0 < KR k
  τ_pos : ∀ k, 0 < τ k
  B_symm : ∀ i j, B i j = B j i
  B_nonneg : ∀ i j, 0 ≤ B i j

namespace Net

variable (m : Net n)

/-- The units on the network as a `MultiDroop` parameter set (network powers
`P_{L,k} + ∑ⱼ Bₖⱼ sin(θₖ − θⱼ)`). -/
def toMultiDroop : MultiDroop (n + 1) :=
  ⟨m.KR, m.τ, m.Pstar, m.ωs, fun θ k => m.PL k + powerInjection m.B θ k⟩

/-- The synchronous frequency `Ω = ω_s + (∑ₖ (P*ₖ − P_{L,k}))/∑ₖ K_{R,k}`. -/
def syncFreq : ℝ := m.ωs + (∑ k, (m.Pstar k - m.PL k)) / ∑ k, m.KR k

/-- The droop frequency `ω_s − (P_{f,k} − P*ₖ)/K_{R,k}` of unit `k` in a reduced state. -/
def droopFreq (z : State (n + (n + 1))) (k : Fin (n + 1)) : ℝ :=
  m.ωs - (z (wIdx k) - m.Pstar k) / m.KR k

/-- The reduced field on `(δ, P_f)`: relative angles `δᵢ = θ_{i+1} − θ₀`, then filtered powers. -/
def reducedField (z : State (n + (n + 1))) : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun i => m.droopFreq z i.succ - m.droopFreq z 0)
    (fun k => (m.PL k + powerInjection m.B (angleMap z) k - z (wIdx k)) / m.τ k) r

@[tmio M, simp, powerlib_domain] theorem reducedField_dIdx (z : State (n + (n + 1))) (i : Fin n) :
    m.reducedField z (dIdx i) = m.droopFreq z i.succ - m.droopFreq z 0 := by
  simp [reducedField]

@[tmio M, simp, powerlib_domain] theorem reducedField_wIdx (z : State (n + (n + 1)))
    (k : Fin (n + 1)) : m.reducedField z (wIdx k) =
      (m.PL k + powerInjection m.B (angleMap z) k - z (wIdx k)) / m.τ k := by
  simp [reducedField]

/-- The reduction `(θ, P_f) ↦ (θ_{i+1} − θ₀, P_f)` intertwines the field of the units
(`MultiDroop.field`) and the reduced field. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem reducedField_reduce (x : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    m.reducedField (reduce x) = reduce (m.toMultiDroop.field x) := by
  apply Dynamics.state_ext_blocks
  · intro i
    simp only [reducedField_dIdx, droopFreq, Network.Swing.reduce_wIdx, toMultiDroop]
    simp [MultiDroop.field]
  · intro k
    simp only [reducedField_wIdx, Network.Swing.reduce_wIdx, Network.Swing.angleMap_reduce,
      Network.Swing.powerInjection_add_const, toMultiDroop]
    simp [MultiDroop.field]

/-- The swing network of the units at the synchronous frequency `Ω`: inertia `τₖ K_{R,k}`,
damping `K_{R,k}`, power `P*ₖ − P_{L,k} + K_{R,k} (ω_s − Ω)`, the same couplings. -/
def toSwing : Network.Swing.Params n :=
  ⟨fun k => m.τ k * m.KR k, m.KR, fun k => m.Pstar k - m.PL k + m.KR k * (m.ωs - m.syncFreq),
    m.B, fun k => mul_pos (m.τ_pos k) (m.KR_pos k), m.KR_pos, m.B_symm, m.B_nonneg⟩

/-- The swing powers of the units sum to zero (`Ω` is the synchronous frequency). Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem sum_toSwing_P : ∑ k, m.toSwing.P k = 0 := by
  have hK : 0 < ∑ k, m.KR k := Finset.sum_pos (fun k _ => m.KR_pos k) Finset.univ_nonempty
  simp only [toSwing, syncFreq, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [Finset.sum_sub_distrib] at *
  field_simp
  ring

/-- Diagonal of the change of coordinates `(δ, P_f) ↦ (δ, −P_f/K_R)`. -/
def coordDiag : Fin (n + (n + 1)) → ℝ := fun r => Fin.addCases (motive := fun _ => ℝ)
  (fun _ => 1) (fun k => -(m.KR k)⁻¹) r

@[tmio M, powerlib_domain] private theorem coordDiag_isUnit :
    IsUnit (Matrix.diagonal m.coordDiag) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  intro r _
  refine Fin.addCases (fun i => ?_) (fun k => ?_) r
  · simp [coordDiag]
  · simp [coordDiag, (m.KR_pos k).ne']

/-- The change of coordinates `(δ, P_f) ↦ (δ, −P_f/K_R)` (linear part of the droop reading). -/
def coord : State (n + (n + 1)) ≃L[ℝ] State (n + (n + 1)) :=
  Dynamics.matrixCoord (Matrix.diagonal m.coordDiag) m.coordDiag_isUnit

@[tmio M, simp, powerlib_domain] theorem coord_dIdx (x : State (n + (n + 1))) (i : Fin n) :
    m.coord x (dIdx i) = x (dIdx i) := by
  rw [coord, Dynamics.ofLp_matrixCoord, Matrix.mulVec_diagonal]
  simp [coordDiag]

@[tmio M, simp, powerlib_domain] theorem coord_wIdx (x : State (n + (n + 1))) (k : Fin (n + 1)) :
    m.coord x (wIdx k) = -(x (wIdx k) / m.KR k) := by
  rw [coord, Dynamics.ofLp_matrixCoord, Matrix.mulVec_diagonal]
  simp [coordDiag]
  ring

/-- Offset of the droop reading: `ω = ω_s − Ω − (P_f − P*)/K_R`. -/
def offset : State (n + (n + 1)) :=
  WithLp.toLp 2 fun r => Fin.addCases (motive := fun _ => ℝ)
    (fun _ => 0) (fun k => m.ωs - m.syncFreq + m.Pstar k / m.KR k) r

@[tmio M, simp, powerlib_domain] theorem offset_dIdx (i : Fin n) : m.offset (dIdx i) = 0 := by
  simp [offset]

@[tmio M, simp, powerlib_domain] theorem offset_wIdx (k : Fin (n + 1)) :
    m.offset (wIdx k) = m.ωs - m.syncFreq + m.Pstar k / m.KR k := by
  simp [offset]

@[tmio M, powerlib_domain] private theorem angleMap_affine (x : State (n + (n + 1))) :
    angleMap (Dynamics.affineCoord m.coord m.offset x) = angleMap x := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [Dynamics.affineCoord]

/-- **The droop network is the swing network.** In the coordinates
`(δ, ω) = (δ, ω_s − Ω − (P_f − P*)/K_R)` the reduced field of the units is the reduced swing
field with inertia `τ K_R`, damping `K_R` and power `P* − P_L + K_R (ω_s − Ω)`. Static evidence
on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem swing_reducedField_eq_transport :
    Network.Swing.reducedField m.toSwing =
      Dynamics.transportField m.coord m.offset m.reducedField := by
  funext y
  have hy : y = Dynamics.affineCoord m.coord m.offset (m.coord.symm (y - m.offset)) := by
    simp [Dynamics.affineCoord]
  rw [hy, Dynamics.transportField_affineCoord]
  set x := m.coord.symm (y - m.offset)
  apply Dynamics.state_ext_blocks
  · intro i
    have h0 := (m.KR_pos 0).ne'
    have h1 := (m.KR_pos i.succ).ne'
    change Network.Swing.reducedField m.toSwing _ (dIdx i) = m.coord _ (dIdx i)
    rw [Network.Swing.reducedField_dIdx, coord_dIdx, reducedField_dIdx]
    simp only [Dynamics.affineCoord, PiLp.add_apply, coord_wIdx, offset_wIdx, droopFreq]
    field_simp
    ring
  · intro k
    have hk := (m.KR_pos k).ne'
    have hτ := (m.τ_pos k).ne'
    change Network.Swing.reducedField m.toSwing _ (wIdx k) = m.coord _ (wIdx k)
    rw [Network.Swing.reducedField_wIdx, coord_wIdx, reducedField_wIdx, angleMap_affine]
    simp only [Dynamics.affineCoord, PiLp.add_apply, coord_wIdx, offset_wIdx, toSwing]
    field_simp
    ring

end Net

/-! ### The exact Hurwitz test of the reduced swing Jacobian -/

/-- **The Hessian-form test is exact.** The reduced swing Jacobian at `θ` is Hurwitz exactly when
the form `A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)(uₖ − uⱼ)²` (twice the quadratic form of the Laplacian of
`Bₖⱼ cos(θₖ − θⱼ)`) is positive on every nonzero grounded direction. Sufficiency is
`Network.Swing.jacobian_isHurwitz_of_hessForm`. Necessity: the Jacobian does not depend on the
powers, so `θ` is a power-balance point of the network with powers `P := P(θ)`, where a Hurwitz
Jacobian gives local asymptotic stability and a negative value of `A₂` rules it out
(`Network.Swing.not_localAsymptoticStable_of_hessForm_neg`); a zero of the positive semidefinite
form is a kernel vector of the Laplacian (`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`), hence
an eigenvector of the Jacobian with eigenvalue `0`. -/
@[tmio M, powerlib_domain] theorem isHurwitz_jacobian_iff (p : Network.Swing.Params n)
    (θ : Fin (n + 1) → ℝ) :
    LinearSystems.IsHurwitz (Network.Swing.jacobian p θ) ↔
      ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm p θ u := by
  refine ⟨fun hH => ?_, fun h => (TMIO.mem_realize _ _ _).mp
    (Network.Swing.jacobian_isHurwitz_of_hessForm p θ h) .jacobianStable (by simp)⟩
  -- the balanced network with the same Jacobian
  let p' : Network.Swing.Params n := { p with P := fun k => powerInjection p.B θ k }
  have hnn : ∀ v, 0 ≤ hessForm p θ v := by
    intro v
    by_contra hv
    push Not at hv
    have hsound := Network.Swing.chain_le_semantics (n := n)
    unfold powerlib.TMIO.Statement at hsound
    have hm : (⟨p', θ⟩ : Network.Swing.Model n) ∈
        Network.Swing.family.den (.flow .locallyAsymptoticallyStable) := by
      refine Family.chain_le_semantics_iff.mp hsound _ ((TMIO.mem_realize _ _ _).mpr ?_)
      rintro q (rfl | rfl)
      · exact fun k => rfl
      · exact hH
    have hn := Network.Swing.not_localAsymptoticStable_of_hessForm_neg ⟨p', θ⟩ (fun k => rfl) v hv
    unfold powerlib.TMIO.Statement at hn
    exact hn hm
  intro u hu0 hu
  refine lt_of_le_of_ne (hnn u) fun h0 => ?_
  -- the Laplacian of the linearization weights kills `u`
  set L := laplacian (flowWeights p.B θ) with hLdef
  have hW := Network.Swing.flowWeights_symm p θ
  have hform : ∀ v : Fin (n + 1) → ℝ, hessForm p θ v = 2 * dotProduct v (L *ᵥ v) := by
    intro v
    rw [hLdef, Network.dotProduct_laplacian_mulVec hW]
    simp only [hessForm, flowWeights, of_apply]
    ring
  have hpsd : L.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · change Lᴴ = L
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, hLdef, Network.laplacian_transpose hW]
    · have := hnn v
      rw [hform] at this
      simp only [star_trivial]
      linarith
  have hLu : L *ᵥ u = 0 := by
    refine (hpsd.dotProduct_mulVec_zero_iff).mp ?_
    simp only [star_trivial]
    linarith [hform u]
  -- an eigenvector of the Jacobian with eigenvalue `0`
  have hex : ∃ i : Fin n, u i.succ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hu (funext fun k => Fin.cases hu0 (fun i => hall i) k)
  obtain ⟨i₀, hi₀⟩ := hex
  let v : Fin (n + (n + 1)) → ℂ := fun r => Fin.addCases (motive := fun _ => ℂ)
    (fun i => (u i.succ : ℂ)) (fun _ => 0) r
  have hv : v ≠ 0 := by
    intro hv0
    have := congrFun hv0 (dIdx i₀)
    simp only [v, Fin.addCases_left, Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact hi₀ this
  have heig : (Network.Swing.jacobian p θ).map (algebraMap ℝ ℂ) *ᵥ v = (0 : ℂ) • v := by
    rw [zero_smul]
    funext r
    refine Fin.addCases (fun i => ?_) (fun k => ?_) r
    · simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, Fin.sum_univ_add]
      simp [v, Network.Swing.jacobian_dd, Network.Swing.jacobian_dw]
    · simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, Fin.sum_univ_add]
      have hk := congrFun hLu k
      simp only [mulVec, dotProduct, Pi.zero_apply, Fin.sum_univ_succ, hu0, mul_zero,
        zero_add] at hk
      simp only [v, Network.Swing.jacobian_wd, Network.Swing.jacobian_ww]
      simp only [Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero,
        add_zero]
      have hreal : ∑ x : Fin n, -(L k x.succ) / p.M k * u x.succ = 0 := by
        simp_rw [neg_div, neg_mul, Finset.sum_neg_distrib, div_mul_eq_mul_div, ← Finset.sum_div,
          hk, zero_div, neg_zero]
      have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hc
      rw [← hLdef]
      simpa using hc
  have := hH 0 v hv heig
  simp at this

/-! ### The family -/

/-- A droop network read about a selected angle profile `θ*`, every unit at the synchronous
frequency `Ω`. -/
structure Model (n : ℕ) where
  /-- The units and the network. -/
  net : Net n
  /-- The selected angle profile `θ*`. -/
  θ : Fin (n + 1) → ℝ

namespace Model

variable (x : Model n)

/-- The selected point: the relative angles of `θ*` and the filtered powers
`P*ₖ + K_{R,k}(ω_s − Ω)`, at which every droop frequency is `Ω`. -/
def point : State (n + (n + 1)) :=
  reduce (x.θ, fun k => x.net.Pstar k + x.net.KR k * (x.net.ωs - x.net.syncFreq))

/-- The reduced field translated so that the selected point is the origin. -/
def field (z : State (n + (n + 1))) : State (n + (n + 1)) := x.net.reducedField (z + x.point)

/-- The swing-network model of the units: `Net.toSwing` about the same angle profile. -/
def toSwing : Network.Swing.Model n := ⟨x.net.toSwing, x.θ⟩

/-- Power balance at `θ*`: every unit exports `P*ₖ + K_{R,k}(ω_s − Ω)`. -/
def Balanced : Prop :=
  ∀ k, x.net.PL k + powerInjection x.net.B x.θ k =
    x.net.Pstar k + x.net.KR k * (x.net.ωs - x.net.syncFreq)

/-- The Laplacian of the linearization weights `Bₖⱼ cos(θ*ₖ − θ*ⱼ)` is positive definite on the
grounded directions: `A₂(u) = ∑ₖ ∑ⱼ Bₖⱼ cos(θ*ₖ − θ*ⱼ)(uₖ − uⱼ)² > 0` for every `u ≠ 0` with
`u₀ = 0` (the form does not depend on the droop gains, filters and powers). -/
def Synchronizing : Prop :=
  ∀ u : Fin (n + 1) → ℝ, u 0 = 0 → u ≠ 0 → 0 < hessForm x.net.toSwing x.θ u

/-- Instability condition: balance and a characteristic root of the reduced swing Jacobian at
`θ*` in the open right half plane. -/
def Unstable : Prop :=
  x.Balanced ∧ ∃ s : ℂ,
    (Linear.characteristicMatrix (Network.Swing.jacobian x.net.toSwing x.θ) s).det = 0 ∧
      0 < s.re

/-- Balance is the power-flow requirement of the swing reading. Static evidence on the model, not
a connection conclusion. -/
@[tmio M, powerlib_domain] theorem balanced_iff :
    x.Balanced ↔ ∀ k, x.net.toSwing.P k = powerInjection x.net.B x.θ k := by
  refine forall_congr' fun k => ?_
  simp only [Net.toSwing]
  constructor <;> intro h <;> linarith

/-- At a balanced profile the selected state is the relative equilibrium of the units rotating at
`Ω` (`MultiDroop.relativeEquilibrium_iff`), so the sharing, frequency and proportional-sharing
results of `MultiDroop` apply to it. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem relativeEquilibrium_iff_balanced :
    x.net.toMultiDroop.field
        (x.θ, fun k => x.net.Pstar k + x.net.KR k * (x.net.ωs - x.net.syncFreq)) =
      ((fun _ => x.net.syncFreq), (0 : Fin (n + 1) → ℝ)) ↔ x.Balanced := by
  rw [MultiDroop.relativeEquilibrium_iff _ fun k => (x.net.τ_pos k).ne']
  have hfreq : ∀ k, x.net.toMultiDroop.ωs -
      ((x.net.Pstar k + x.net.KR k * (x.net.ωs - x.net.syncFreq)) -
        x.net.toMultiDroop.Pstar k) / x.net.toMultiDroop.KR k = x.net.syncFreq := by
    intro k
    have hk := (x.net.KR_pos k).ne'
    simp only [Net.toMultiDroop]
    field_simp
    ring
  simp only [hfreq, implies_true, and_true]
  exact forall_congr' fun k => eq_comm

/-- The selected point is the image of the swing network's synchronous point. Static evidence on
the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibrium_eq :
    Network.Swing.equilibrium x.θ = Dynamics.affineCoord x.net.coord x.net.offset x.point := by
  apply Dynamics.state_ext_blocks
  · intro i
    simp [Network.Swing.equilibrium, point, Dynamics.affineCoord]
  · intro k
    have hk := (x.net.KR_pos k).ne'
    simp only [Network.Swing.equilibrium, point, Dynamics.affineCoord, PiLp.add_apply,
      Net.coord_wIdx, Net.offset_wIdx, Network.Swing.reduce_wIdx, Pi.zero_apply]
    field_simp
    ring

end Model

/-- The droop-network family: each model read as its reduced field translated to the selected
point. Stability condition: balance with a synchronizing Laplacian; instability condition:
balance with an unstable reduced swing Jacobian. -/
def family : Family (Model n) Spectral.Requirement (n + (n + 1)) 0 :=
  Spectral.localFamily Model.field (fun x => x.Balanced ∧ x.Synchronizing) Model.Unstable

@[tmio M, powerlib_domain] theorem family_isAutonomous :
    (family (n := n)).IsAutonomous Model.field :=
  Spectral.localFamily_isAutonomous _ _ _

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {x : Model n} {P : Flow.Property} :
    x ∈ family.den (.flow P) ↔ P.holds x.net.reducedField x.point :=
  Spectral.mem_den_flow_iff_shift (f := fun x : Model n => x.net.reducedField)
    (pt := Model.point) family_isAutonomous

/-- **The droop network reads through the swing network**: for every sentence a model satisfies
it exactly when its swing network `Model.toSwing` (inertia `τ K_R`, damping `K_R`, power
`P* − P_L + K_R (ω_s − Ω)`) does at the same angle profile — the reduced fields are conjugate by
`(δ, P_f) ↦ (δ, ω_s − Ω − (P_f − P*)/K_R)` (`Net.swing_reducedField_eq_transport`). Scaffold:
`theorem/GridTiedConverter/GFM/MultiDroopSwing.agda`. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_swing (x : Model n) (s : Sentence) :
    connection% (x ∈ family.den s ↔ x.toSwing ∈ Network.Swing.family.den s) := by
  have hflow : ∀ P : Flow.Property,
      x ∈ family.den (.flow P) ↔ x.toSwing ∈ Network.Swing.family.den (.flow P) := fun P => by
    have h := Spectral.mem_den_flow_iff_of_hub_transport (F := family)
      (G := Network.Swing.family) (fun _ _ => mem_den_flow_iff)
      (fun _ _ => Spectral.mem_den_flow_iff_shift
        (f := fun m : Network.Swing.Model n => Network.Swing.reducedField m.params)
        (pt := fun m => Network.Swing.equilibrium m.θ) Network.Swing.family_isAutonomous)
      (g := Model.toSwing) x.net.coord x.net.offset x.net.swing_reducedField_eq_transport
      x.equilibrium_eq P
    unfold powerlib.TMIO.Statement at h
    exact h
  have h := Spectral.mem_den_iff_of_flow family_isAutonomous Network.Swing.family_isAutonomous
    hflow s
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- **Local exponential stability of the synchronous state, exact.** A droop network is locally
exponentially stable at its selected angle profile (relative angles and filtered powers) exactly
when the profile is balanced and the Laplacian of `Bₖⱼ cos(θ*ₖ − θ*ⱼ)` is positive definite on the
grounded directions — for all positive droop gains and filter constants. Through the swing reading
(`mem_den_iff_swing`), the swing network's exactness
(`Network.Swing.exact_locallyExponentiallyStable`) and the exact Hurwitz test
(`isHurwitz_jacobian_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (x : Model n) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable) ↔
      x ∈ {x : Model n | x.Balanced ∧ x.Synchronizing}) := by
  have hr := mem_den_iff_swing x (.flow .locallyExponentiallyStable)
  have hx := Network.Swing.exact_locallyExponentiallyStable (n := n)
  unfold powerlib.TMIO.Statement at hr hx ⊢
  rw [hr, ← hx, (connection_proof% TMIO.mem_realize)]
  simp only [Network.Swing.family, Network.Swing.translate, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_ofPred_eq]
  change ((∀ k, x.net.toSwing.P k = powerInjection x.net.B x.θ k) ∧
    LinearSystems.IsHurwitz (Network.Swing.jacobian x.net.toSwing x.θ)) ↔ _
  rw [isHurwitz_jacobian_iff, ← x.balanced_iff]
  rfl

/-- Every translation of the droop-network family is sound: the stability condition gives local
exponential stability (`mem_den_locallyExponentiallyStable_iff`), the instability condition
instability (the swing network's, `Network.Swing.mem_den_unstable`, through the reading). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, (family (n := n)).chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun x hS => ?_) (fun x hU => ?_)
  · have h := (mem_den_locallyExponentiallyStable_iff x).mpr hS
    exact family_isAutonomous.mem_den_flow.mp h
  · obtain ⟨hb, s, hs, hre⟩ := hU
    have hu := Network.Swing.mem_den_unstable x.toSwing (x.balanced_iff.mp hb) hs hre
    have hr := mem_den_iff_swing x (.flow .unstable)
    unfold powerlib.TMIO.Statement at hu hr
    exact family_isAutonomous.mem_den_flow.mp (hr.mpr hu)

/-- The local exponential translation of the droop-network family is exact. -/
@[tmio TM, powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% ((family (n := n)).Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_exact_locallyExponentiallyStable fun x => ?_
  have h := mem_den_locallyExponentiallyStable_iff x
  unfold powerlib.TMIO.Statement at h
  exact h.symm.trans family_isAutonomous.mem_den_flow

/-- **The angle condition.** A balanced droop network whose coupled units differ in angle by less
than `π/2` on a connected network is locally exponentially stable (the swing network's angle
condition, `Network.Swing.mem_den_locallyExponentiallyStable`, through the reading). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_angle (x : Model n)
    (hbal : x.Balanced) (hangle : ∀ i j, 0 < x.net.B i j → |x.θ i - x.θ j| < Real.pi / 2)
    (hconn : ∀ i j, Network.Reach x.net.B i j) :
    connection% (x ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := Network.Swing.mem_den_locallyExponentiallyStable x.toSwing (x.balanced_iff.mp hbal)
    hangle hconn
  have hr := mem_den_iff_swing x (.flow .locallyExponentiallyStable)
  unfold powerlib.TMIO.Statement at h hr ⊢
  exact hr.mpr h

/-- **Local asymptotic stability, complete characterization.** A droop network is locally
asymptotically stable at its selected angle profile exactly when the profile is balanced, a strict
local minimum in relative angles of the network potential
`U(θ) = −∑ₖ (P*ₖ − P_{L,k} + K_{R,k}(ω_s − Ω)) θₖ − ½ ∑ₖ ∑ⱼ Bₖⱼ cos(θₖ − θⱼ)`, and an isolated
balanced profile (the swing network's characterization,
`Network.Swing.mem_den_locallyAsymptoticallyStable_iff`, through the reading). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (x : Model n) :
    connection% (x ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      x.Balanced ∧ ∃ r > 0, ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖ < r →
        Network.Swing.potential x.net.toSwing x.θ <
          Network.Swing.potential x.net.toSwing (x.θ + ground v) ∧
        ¬ (⟨x.net, x.θ + ground v⟩ : Model n).Balanced) := by
  have hr := mem_den_iff_swing x (.flow .locallyAsymptoticallyStable)
  have hs := Network.Swing.mem_den_locallyAsymptoticallyStable_iff x.toSwing
  unfold powerlib.TMIO.Statement at hr hs ⊢
  rw [hr, hs, x.balanced_iff]
  simp only [Model.balanced_iff]
  rfl

end MultiDroop
end powerlib.GFM
