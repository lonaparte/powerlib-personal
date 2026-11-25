import theorem.GridTiedConverter.GFM.VSMLPF

/-! # Reduced-layer algebra of the GFM VSM + power-filter model

Algebraic model identities for the three-state VSM + power-filter model.  None of them is a
stability statement; the domain results live in `VSMLPF.lean`.

Model boundary.
The three-state model of `theorem/GridTiedConverter/GFM/VSMLPF.lean` (state `(δ, ω, P_f)`, `δ̇ = ω`,
`M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin(δ − u) − P_f)`, `K₀ = E V_g / X_g`, export-positive
active power, continuous time), with the grid-angle or `P_ref` modulation `u` as input.

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md` §15 ("摆动二阶约化", "混合张量"); `notes/theory-draft.md` §2.4,
§1.3 (GFM model); GFM channels: `projects/gfl-gfm-stability-tree/notes/concepts/
nonautonomous-criteria.md` (GFM `P_ref` 通道 `A_u = 0`).

Results.
* The synchronizing coefficient `K = ∂P/∂δ = K₀ cos δ₀` (`= E V_g cos δ₀ / X_g`) is the slope of
  the power-angle curve at the loading angle: `Synchronous.SwingParams.hasDerivAt_Pe` of the
  second-order swing reduction `swingReduced M D P₀ K₀` (`GFM.swingReduced`) at `δ₀`; with
  `K₀ = E V_g / X_g` equilibria exist iff `|P₀| ≤ E V_g / X_g` (`VSMLPF.exists_equilibrium_iff`).
* `texact_denominator_expansion`: the exact identity
  `[(s + ω_c)(M s² + D s) + ω_c K] / (M (s + ω_c)) = s² + 2α_red s + K/M + R(s)`,
  `2α_red = D/M − K/(M ω_c)`, `R(s) = K s² / (M ω_c (s + ω_c))` (the first-order filter
  expansion behind the reduced swing layer).
* `reduced_root_re`: a non-real root of `s² + 2α s + ω₀²` has real part `−α`.
* `twoAlphaRed_pos_iff`: `2α_red > 0 ⇔ r_c < 2ζ_sw` (`r_c = ω₀/ω_c`, `ζ_sw = D/(2√(MK))`);
  `twoAlphaRed_eq_zero_iff`: the zero of `α_red` is `ω_c = K/D`, which differs from the exact
  Routh–Hurwitz boundary `ω_c = K/D − D/M` by `D/M`.
* `iteratedDeriv_jacobian_u`: `f_xuu = ∂²J/∂u² |_{u=0} = −(A₀)_{P_f δ} e_{P_f} e_δᵀ`.
* `boundary_eigenpairs`: on the Routh boundary both `±j ω_H` are eigenvalues of `A₀`.
* GFM channels (no separate model): a `P_ref` deviation `u` is the parameter map `P₀ ↦ P₀ + u` of
  `VSMLPF`, which leaves the Jacobian `VSMLPF.jacobian δ` unchanged (it does not contain `P₀`), so
  `A_u = ∂_u ∂_z f = 0`; a grid-angle deviation `u` is `VSMLPF.fieldU u`, with Jacobian `J(δ − u)`
  (`VSMLPF.fderiv_fieldU`), whose `u`-derivative at `0` is `A₁ = ω_c P₀ e_{P_f} e_δᵀ`
  (`VSMLPF.hasDerivAt_jacobian_u`, entrywise `hasDerivAt_jacobian_entry`), nonzero exactly at a
  loaded operating point `P₀ ≠ 0` (`VSMLPF.A1_ne_zero_iff`).
* Hurwitz region of the Jacobian at an angle (`M, D, ω_c > 0`): `J(δ)` is Hurwitz iff
  `0 < K₀ cos δ < D ω_c + D²/M` (`VSMLPF.isHurwitz_jacobian_iff`, the cubic Routh criterion;
  `VSMLPF.fastBound = D ω_c + D²/M`).
* Frozen-coefficient thresholds (the counterpart of the GFL `GFL.RatePLL.frozen_hurwitz_forall_iff`,
  a statement about families of constant matrices: frozen-time Hurwitz stability does not imply
  stability of the periodic linear time-varying system). Grid-amplitude channel
  `K₀(t) = K₀ + ε cos(ω_p t)` at a fixed angle with `cos δ > 0` (`VSMLPF.withK0`): Hurwitz at every
  instant iff `ε < min(K₀, (D ω_c + D²/M)/cos δ − K₀)` (`VSMLPF.frozen_hurwitz_forall_iff`,
  `VSMLPF.epsFrozen`: the fold side and the light-load Hopf side). `P_ref` channel
  `P₀ + ε cos(ω_p t)` (`VSMLPF.withP0`, the GFM pump channel with `A_u = 0`) at the frozen loading
  angle `arcsin(P/K₀)`: Hurwitz iff `P² < K₀²` and `K₀² − (D ω_c + D²/M)² < P²`
  (`VSMLPF.frozenLoading_isHurwitz_iff`), at every instant iff `ε < K₀ − |P₀|` when
  `K₀ < D ω_c + D²/M` and `ε < min(K₀ − |P₀|, |P₀| − √(K₀² − (D ω_c + D²/M)²))` otherwise
  (`VSMLPF.frozen_pref_hurwitz_forall_iff`, `VSMLPF.prefFrozen`). Grid-angle channel
  `u(t) = ε cos(ω_p t)` (the input of `VSMLPF.fieldU`, Jacobian `J(δ − u)`) at an angle `|δ| < π/2`,
  `K₀ > 0`: Hurwitz at every instant iff `ε < π/2 − |δ|` when `K₀ < D ω_c + D²/M`, and
  `ε < min(π/2 − |δ|, |δ| − arccos((D ω_c + D²/M)/K₀))` otherwise
  (`VSMLPF.frozen_angle_hurwitz_forall_iff`, `VSMLPF.angleFrozen`: the frozen angles
  `[δ − ε, δ + ε]` must avoid the fold angles `±π/2` and, at light load, the Hopf band
  `|θ| ≤ arccos((D ω_c + D²/M)/K₀)`).
Family and connection conclusions.
None.  The stability conclusions of the model are the connection statements of `VSMLPF.family`
(`theorem/GridTiedConverter/GFM/VSMLPF.lean`).
-/

noncomputable section
namespace powerlib.GFM
open Set Matrix

namespace VSMLPF

variable (g : VSMLPF)

/-- Reduced-layer damping `2α_red = D/M − K/(M ω_c)`. -/
def twoAlphaRed : ℝ := g.D / g.M - g.K / (g.M * g.ωc)

/-- Exact first-order filter expansion of the `u → δ` denominator:
`[(s + ω_c)(M s² + D s) + ω_c K] / (M (s + ω_c)) = s² + 2α_red s + K/M + K s²/(M ω_c (s + ω_c))`. -/
@[tmio M, powerlib_domain] theorem texact_denominator_expansion (hM : g.M ≠ 0) (hω : g.ωc ≠ 0)
    {s : ℂ} (hs : s + (g.ωc : ℂ) ≠ 0) :
    ((s + (g.ωc : ℂ)) * ((g.M : ℂ) * s ^ 2 + (g.D : ℂ) * s) + (g.ωc : ℂ) * (g.K : ℂ)) /
        ((g.M : ℂ) * (s + (g.ωc : ℂ))) =
      s ^ 2 + (g.twoAlphaRed : ℂ) * s + (g.K : ℂ) / (g.M : ℂ) +
        (g.K : ℂ) * s ^ 2 / ((g.M : ℂ) * (g.ωc : ℂ) * (s + (g.ωc : ℂ))) := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hω' : (g.ωc : ℂ) ≠ 0 := by exact_mod_cast hω
  simp only [twoAlphaRed]
  push_cast
  field_simp
  ring

variable {g}

/-- `2α_red > 0 ⇔ r_c < 2 ζ_sw` with `r_c = √(K/M)/ω_c`, `ζ_sw = D/(2√(MK))`
(`M, K, ω_c > 0`). -/
@[tmio M, powerlib_domain] theorem twoAlphaRed_pos_iff (hM : 0 < g.M) (hK : 0 < g.K)
    (hω : 0 < g.ωc) :
    0 < g.twoAlphaRed ↔
      Real.sqrt (g.K / g.M) / g.ωc < 2 * (g.D / (2 * Real.sqrt (g.M * g.K))) := by
  have hs : 0 < Real.sqrt (g.M * g.K) := Real.sqrt_pos.mpr (mul_pos hM hK)
  have hprod : Real.sqrt (g.K / g.M) * Real.sqrt (g.M * g.K) = g.K := by
    rw [← Real.sqrt_mul (div_nonneg hK.le hM.le), show g.K / g.M * (g.M * g.K) = g.K ^ 2 by
      field_simp, Real.sqrt_sq hK.le]
  have e1 : 0 < g.twoAlphaRed ↔ g.K < g.D * g.ωc := by
    rw [twoAlphaRed, sub_pos, div_lt_div_iff₀ (mul_pos hM hω) hM]
    constructor <;> intro h <;> nlinarith
  have e2 : Real.sqrt (g.K / g.M) / g.ωc < 2 * (g.D / (2 * Real.sqrt (g.M * g.K))) ↔
      g.K < g.D * g.ωc := by
    rw [show 2 * (g.D / (2 * Real.sqrt (g.M * g.K))) = g.D / Real.sqrt (g.M * g.K) by
      field_simp, div_lt_div_iff₀ hω hs, hprod]
  rw [e1, e2]

/-- The zero of `α_red` is `ω_c = K/D`; it differs from the exact Routh–Hurwitz (Hopf) boundary
`ω_c* = K/D − D/M` by `D/M`. -/
@[tmio M, powerlib_domain] theorem twoAlphaRed_eq_zero_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) :
    g.twoAlphaRed = 0 ↔ g.ωc = g.K / g.D := by
  rw [twoAlphaRed, sub_eq_zero, div_eq_div_iff hM.ne' (mul_pos hM hω).ne',
    eq_div_iff hD.ne']
  constructor <;> intro h <;> nlinarith

/-- A non-real root of the reduced quadratic `s² + 2α s + ω₀²` has real part `−α`
(so `α_red` is the decay rate of the reduced swing pair). -/
@[tmio T, powerlib_foundation] theorem reduced_root_re {α ω0sq : ℝ} {s : ℂ}
    (hs : s ^ 2 + 2 * (α : ℂ) * s + (ω0sq : ℂ) = 0) (him : s.im ≠ 0) : s.re = -α := by
  have h := Criteria.quadratic_root_im (a1 := 2 * α) (a0 := ω0sq) (by push_cast; exact hs)
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 him
  · linarith

variable (g)

/-- `∂J/∂u` along `u ↦ J(δ₀ − u)` at a general `u`: only the `(P_f, δ)` entry varies. -/
def jacobianU' (u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, 0, 0; g.ωc * (g.K0 * Real.sin (g.δ0 - u)), 0, 0]

/-- `f_xuu = −(A₀)_{P_f δ} e_{P_f} e_δᵀ`, `A₀ = J(δ₀)`. -/
def fxuu : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; -(g.jacobian g.δ0 2 0), 0, 0]

@[tmio M, powerlib_domain] theorem hasDerivAt_jacobian_entry (u : ℝ) (i j : Fin 3) :
    HasDerivAt (fun v => g.jacobian (g.δ0 - v) i j) (g.jacobianU' u i j) u := by
  have h1 : HasDerivAt (fun v : ℝ => g.δ0 - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub g.δ0
  have key : HasDerivAt (fun v => g.ωc * (g.K0 * Real.cos (g.δ0 - v)))
      (g.ωc * (g.K0 * Real.sin (g.δ0 - u))) u := by
    convert ((h1.cos).const_mul g.K0).const_mul g.ωc using 1
    ring
  fin_cases i <;> fin_cases j <;> simp [jacobian, jacobianU'] <;>
    first | exact hasDerivAt_const _ _ | exact key

/-- `∂J/∂u |_{u=0} = A₁` at the loading equilibrium: `hasDerivAt_jacobian_entry` at `u = 0`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_jacobian_u (hK0 : 0 < g.K0) (h : |g.P0| ≤ g.K0)
    (i j : Fin 3) :
    HasDerivAt (fun u => g.jacobian (g.δ0 - u) i j) (g.A1 i j) 0 := by
  have hsin : g.K0 * Real.sin g.δ0 = g.P0 := by
    simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, VSMLPF.Meets,
      VSMLPF.Model.K, VSMLPF.K] using g.sin_δ0 hK0 h
  convert g.hasDerivAt_jacobian_entry 0 i j using 1
  fin_cases i <;> fin_cases j <;> simp [A1, jacobianU', hsin]

/-- **Mixed tensor `f_xuu`**: `∂²/∂u² J(δ₀ − u) |_{u=0} = −(A₀)_{P_f δ} e_{P_f} e_δᵀ`
(entrywise). -/
@[tmio M, powerlib_domain] theorem iteratedDeriv_jacobian_u (i j : Fin 3) :
    iteratedDeriv 2 (fun u => g.jacobian (g.δ0 - u) i j) 0 = g.fxuu i j := by
  have hd : deriv (fun u => g.jacobian (g.δ0 - u) i j) = fun u => g.jacobianU' u i j :=
    funext fun u => (g.hasDerivAt_jacobian_entry u i j).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  have h1 : HasDerivAt (fun v : ℝ => g.δ0 - v) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub g.δ0
  have key : HasDerivAt (fun v => g.ωc * (g.K0 * Real.sin (g.δ0 - v)))
      (-(g.ωc * (g.K0 * Real.cos g.δ0))) 0 := by
    convert ((h1.sin).const_mul g.K0).const_mul g.ωc using 1
    simp
  have h2 : HasDerivAt (fun u => g.jacobianU' u i j) (g.fxuu i j) 0 := by
    fin_cases i <;> fin_cases j <;> simp [jacobianU', fxuu, jacobian] <;>
      first | exact hasDerivAt_const _ _ | exact key
  exact h2.deriv

/-- On the Routh–Hurwitz boundary `ω_c = K/D − D/M` both `±j ω_H`, `ω_H² = K/M − D²/M²`, are
eigenvalues of the Jacobian at the loading equilibrium. -/
@[tmio M, powerlib_domain] theorem boundary_eigenpairs (hM : g.M ≠ 0) (hD : g.D ≠ 0)
    (hωc : g.ωc = g.K / g.D - g.D / g.M) {ωH : ℝ}
    (hH : ωH ^ 2 = g.K / g.M - g.D ^ 2 / g.M ^ 2) :
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧
        (g.jacobian g.δ0).map (algebraMap ℝ ℂ) *ᵥ v = ((ωH : ℂ) * Complex.I) • v) ∧
      ∃ v : Fin 3 → ℂ, v ≠ 0 ∧
        (g.jacobian g.δ0).map (algebraMap ℝ ℂ) *ᵥ v = (((-ωH : ℝ) : ℂ) * Complex.I) • v := by
  refine ⟨Linear.exists_eigenvector_of_root
      (g.det_characteristicMatrix_boundary hM hD hωc hH),
    Linear.exists_eigenvector_of_root
      (g.det_characteristicMatrix_boundary hM hD hωc (by rw [neg_sq]; exact hH))⟩

/-! ## Frozen-coefficient thresholds (N1) -/

/-- The fast-filter bound `D ω_c + D²/M` of the Routh condition. -/
def fastBound : ℝ := g.D * g.ωc + g.D ^ 2 / g.M

/-- The same model with the infinite-bus amplitude `K₀ = E V_g/X_g` replaced by `K₀'`
(frozen-time evaluation under a grid-amplitude modulation). -/
def withK0 (K0' : ℝ) : VSMLPF := { g with K0 := K0' }

/-- The same model with the set point `P₀` replaced by `P₀'` (frozen-time evaluation under a
`P_ref` modulation). -/
def withP0 (P0' : ℝ) : VSMLPF := { g with P0 := P0' }

/-- **The Jacobian at an angle is Hurwitz iff `0 < K₀ cos δ < D ω_c + D²/M`** (`M, D, ω_c > 0`;
the cubic Routh criterion of `M s³ + (D + M ω_c) s² + D ω_c s + ω_c K₀ cos δ`,
`Criteria.isHurwitz_iff_of_coeffs_cubic`). -/
@[tmio M, powerlib_domain] theorem isHurwitz_jacobian_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) (δ : ℝ) :
    LinearSystems.IsHurwitz (g.jacobian δ) ↔
      0 < g.K0 * Real.cos δ ∧ g.K0 * Real.cos δ < g.fastBound := by
  have e : g.M * g.ωc * g.fastBound = (g.D + g.M * g.ωc) * (g.D * g.ωc) := by
    simp only [fastBound]; field_simp; ring
  rw [Criteria.isHurwitz_iff_of_coeffs_cubic _ hM (a2 := g.D + g.M * g.ωc)
    (a1 := g.D * g.ωc) (a0 := g.ωc * (g.K0 * Real.cos δ))
    (by rw [trace_jacobian]; field_simp; ring) (principalMinorSum_jacobian _ _)
    (by rw [det_jacobian])]
  have hMω := mul_pos hM hω
  constructor
  · rintro ⟨-, h0, hg⟩
    refine ⟨pos_of_mul_pos_right h0 hω.le, lt_of_mul_lt_mul_left ?_ hMω.le⟩
    rw [e]; linarith
  · rintro ⟨h0, hf⟩
    have := mul_lt_mul_of_pos_left hf hMω
    rw [e] at this
    exact ⟨by positivity, mul_pos hω h0, by linarith⟩

/-- Frozen threshold of the grid-amplitude channel at the angle `δ`:
`ε_frozen = min(K₀, (D ω_c + D²/M)/cos δ − K₀)`. -/
def epsFrozen (δ : ℝ) : ℝ := min g.K0 (g.fastBound / Real.cos δ - g.K0)

/-- **Frozen-coefficient criterion, grid-amplitude channel** (the GFM counterpart of the GFL
`GFL.RatePLL.frozen_hurwitz_forall_iff`): with the infinite-bus amplitude modulated as
`K₀(t) = K₀ + ε cos(ω_p t)` (`K₀ = E V_g/X_g`, a grid-voltage modulation `ε = E ε_V/X_g`),
`ε ≥ 0`, `ω_p ≠ 0`, the frozen Jacobian at a fixed angle `δ` with `cos δ > 0` is Hurwitz at every
instant iff `ε < min(K₀, (D ω_c + D²/M)/cos δ − K₀)`: the frozen synchronizing coefficient
`K₀(t) cos δ` must stay above the fold value `0` and below the Hopf value `D ω_c + D²/M`. A
statement about a family of constant matrices: frozen-time Hurwitz stability does not imply
stability of the periodic linear time-varying system. -/
@[tmio M, powerlib_domain] theorem frozen_hurwitz_forall_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) {δ : ℝ} (hcos : 0 < Real.cos δ) {ε ωp : ℝ} (hε : 0 ≤ ε) (hωp : ωp ≠ 0) :
    (∀ t : ℝ, LinearSystems.IsHurwitz
        ((g.withK0 (g.K0 + ε * Real.cos (ωp * t))).jacobian δ)) ↔ ε < g.epsFrozen δ := by
  rw [forall_congr' fun t => isHurwitz_jacobian_iff (g.withK0 (g.K0 + ε * Real.cos (ωp * t)))
    hM hD hω δ]
  simp only [withK0, fastBound, epsFrozen, lt_min_iff, lt_sub_iff_add_lt, lt_div_iff₀ hcos]
  constructor
  · intro h
    have h1 := (h (Real.pi / ωp)).1
    rw [mul_div_cancel₀ _ hωp, Real.cos_pi] at h1
    have h2 := (h 0).2
    rw [mul_zero, Real.cos_zero] at h2
    constructor
    · nlinarith
    · linarith
  · rintro ⟨h1, h2⟩ t
    have hc1 := Real.neg_one_le_cos (ωp * t)
    have hc2 := Real.cos_le_one (ωp * t)
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hc2 hε, mul_le_mul_of_nonneg_left hc1 hε]

/-- At the frozen loading angle `arcsin(P/K₀)` of a set point `P` the Jacobian is Hurwitz iff
`P² < K₀²` (the frozen equilibrium exists away from the fold) and `K₀² − (D ω_c + D²/M)² < P²`
(the frozen synchronizing coefficient `√(K₀² − P²)` stays below the Hopf value). -/
@[tmio M, powerlib_domain] theorem frozenLoading_isHurwitz_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) (hK0 : 0 < g.K0) (P : ℝ) :
    LinearSystems.IsHurwitz ((g.withP0 P).jacobian (g.withP0 P).δ0) ↔
      P ^ 2 < g.K0 ^ 2 ∧ g.K0 ^ 2 - g.fastBound ^ 2 < P ^ 2 := by
  have hB : 0 < g.fastBound := by simp only [fastBound]; positivity
  have hK : g.K0 * Real.cos (Real.arcsin (P / g.K0)) = Real.sqrt (g.K0 ^ 2 - P ^ 2) := by
    rw [Real.cos_arcsin, ← Real.sqrt_sq hK0.le, ← Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hK0.le]
    congr 1
    field_simp
  rw [isHurwitz_jacobian_iff (g.withP0 P) hM hD hω]
  change 0 < g.K0 * Real.cos (Real.arcsin (P / g.K0)) ∧
    g.K0 * Real.cos (Real.arcsin (P / g.K0)) < g.fastBound ↔ _
  rw [hK, Real.sqrt_pos, Real.sqrt_lt' hB]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Frozen threshold of the `P_ref` channel at the frozen loading equilibrium: the fold margin
`K₀ − |P₀|`, and, when `K₀ ≥ D ω_c + D²/M`, the light-load Hopf margin
`|P₀| − √(K₀² − (D ω_c + D²/M)²)`. -/
def prefFrozen : ℝ :=
  if g.K0 < g.fastBound then g.K0 - |g.P0|
  else min (g.K0 - |g.P0|) (|g.P0| - Real.sqrt (g.K0 ^ 2 - g.fastBound ^ 2))

/-- **Frozen-coefficient criterion, `P_ref` channel** (the GFM pump channel, `A_u = 0`): with the
set point modulated as `P₀ + ε cos(ω_p t)`, `ε ≥ 0`, `ω_p ≠ 0`, the frozen Jacobian at the frozen
loading equilibrium `arcsin((P₀ + ε cos(ω_p t))/K₀)` is Hurwitz at every instant iff
`ε < prefFrozen`: the swing must keep `|P|` below the fold power `K₀` (a frozen equilibrium
exists) and, at light load (`K₀ ≥ D ω_c + D²/M`), `|P|` above the Hopf power
`√(K₀² − (D ω_c + D²/M)²)`. A statement about a family of constant matrices only. -/
@[tmio M, powerlib_domain] theorem frozen_pref_hurwitz_forall_iff (hM : 0 < g.M) (hD : 0 < g.D)
    (hω : 0 < g.ωc) (hK0 : 0 < g.K0) {ε ωp : ℝ} (hε : 0 ≤ ε) (hωp : ωp ≠ 0) :
    (∀ t : ℝ, LinearSystems.IsHurwitz
        ((g.withP0 (g.P0 + ε * Real.cos (ωp * t))).jacobian
          (g.withP0 (g.P0 + ε * Real.cos (ωp * t))).δ0)) ↔ ε < g.prefFrozen := by
  rw [forall_congr' fun t => frozenLoading_isHurwitz_iff g hM hD hω hK0
    (g.P0 + ε * Real.cos (ωp * t))]
  have hB : 0 < g.fastBound := by simp only [fastBound]; positivity
  -- every value of `cos (ω_p t)` in `[−1, 1]` is attained
  have hatt : ∀ c, -1 ≤ c → c ≤ 1 → ∃ t, Real.cos (ωp * t) = c := fun c h1 h2 =>
    ⟨Real.arccos c / ωp, by rw [mul_div_cancel₀ _ hωp, Real.cos_arccos h1 h2]⟩
  -- the fold side
  have hfold : (∀ c : ℝ, -1 ≤ c → c ≤ 1 → (g.P0 + ε * c) ^ 2 < g.K0 ^ 2) ↔
      ε < g.K0 - |g.P0| := by
    constructor
    · intro h
      rcases abs_cases g.P0 with ⟨hP, -⟩ | ⟨hP, -⟩
      · have := h 1 (by norm_num) le_rfl
        rw [hP]; nlinarith
      · have := h (-1) le_rfl (by norm_num)
        rw [hP]; nlinarith
    · intro h c h1 h2
      have hb : |g.P0 + ε * c| < g.K0 := by
        calc |g.P0 + ε * c| ≤ |g.P0| + |ε * c| := abs_add_le _ _
          _ ≤ |g.P0| + ε := by
              rw [abs_mul, abs_of_nonneg hε]
              nlinarith [abs_le.mpr ⟨h1, h2⟩]
          _ < g.K0 := by linarith
      nlinarith [abs_nonneg (g.P0 + ε * c), sq_abs (g.P0 + ε * c)]
  -- the Hopf side
  have hhopf : g.fastBound ≤ g.K0 →
      ((∀ c : ℝ, -1 ≤ c → c ≤ 1 → g.K0 ^ 2 - g.fastBound ^ 2 < (g.P0 + ε * c) ^ 2) ↔
        ε < |g.P0| - Real.sqrt (g.K0 ^ 2 - g.fastBound ^ 2)) := by
    intro hKB
    have hh : 0 ≤ g.K0 ^ 2 - g.fastBound ^ 2 := by nlinarith
    set s := Real.sqrt (g.K0 ^ 2 - g.fastBound ^ 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = g.K0 ^ 2 - g.fastBound ^ 2 := Real.sq_sqrt hh
    constructor
    · intro h
      by_cases hle : ε ≤ |g.P0|
      · -- the frozen power closest to zero is `sign P₀ (|P₀| − ε)`
        rcases abs_cases g.P0 with ⟨hP, hP0⟩ | ⟨hP, hP0⟩
        · have := h (-1) le_rfl (by norm_num)
          rw [hP] at hle ⊢
          nlinarith
        · have := h 1 (by norm_num) le_rfl
          rw [hP] at hle ⊢
          nlinarith
      · exfalso
        push Not at hle
        have hε0 : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hle
        have hc1 : -1 ≤ -g.P0 / ε := by
          rw [le_div_iff₀ hε0]; nlinarith [le_abs_self g.P0]
        have hc2 : -g.P0 / ε ≤ 1 := by
          rw [div_le_iff₀ hε0]; nlinarith [neg_abs_le g.P0]
        have := h _ hc1 hc2
        rw [mul_div_cancel₀ _ hε0.ne'] at this
        nlinarith
    · intro h c h1 h2
      have hlow : s < |g.P0 + ε * c| := by
        calc s < |g.P0| - ε := by linarith
          _ ≤ |g.P0| - |ε * c| := by
              rw [abs_mul, abs_of_nonneg hε]
              nlinarith [abs_le.mpr ⟨h1, h2⟩]
          _ ≤ |g.P0 + ε * c| := by
              have := abs_sub_abs_le_abs_sub g.P0 (-(ε * c))
              rw [abs_neg, sub_neg_eq_add] at this
              exact this
      nlinarith [sq_abs (g.P0 + ε * c), abs_nonneg (g.P0 + ε * c)]
  have hforall : (∀ t : ℝ, (g.P0 + ε * Real.cos (ωp * t)) ^ 2 < g.K0 ^ 2 ∧
      g.K0 ^ 2 - g.fastBound ^ 2 < (g.P0 + ε * Real.cos (ωp * t)) ^ 2) ↔
      ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (g.P0 + ε * c) ^ 2 < g.K0 ^ 2 ∧
        g.K0 ^ 2 - g.fastBound ^ 2 < (g.P0 + ε * c) ^ 2 := by
    constructor
    · intro h c h1 h2
      obtain ⟨t, ht⟩ := hatt c h1 h2
      rw [← ht]; exact h t
    · intro h t
      exact h _ (Real.neg_one_le_cos _) (Real.cos_le_one _)
  rw [hforall]
  unfold prefFrozen
  split_ifs with hKB
  · rw [← hfold]
    constructor
    · intro h c h1 h2; exact (h c h1 h2).1
    · intro h c h1 h2
      refine ⟨h c h1 h2, ?_⟩
      have : g.K0 ^ 2 < g.fastBound ^ 2 := by nlinarith
      nlinarith [sq_nonneg (g.P0 + ε * c)]
  · push Not at hKB
    rw [lt_min_iff, ← hfold, ← hhopf hKB]
    constructor
    · intro h
      exact ⟨fun c h1 h2 => (h c h1 h2).1, fun c h1 h2 => (h c h1 h2).2⟩
    · rintro ⟨h1, h2⟩ c hc1 hc2
      exact ⟨h1 c hc1 hc2, h2 c hc1 hc2⟩

/-- Frozen threshold of the grid-angle channel at the angle `δ` (`|δ| < π/2`, `K₀ > 0`): the fold
margin `π/2 − |δ|`, and, when `K₀ ≥ D ω_c + D²/M`, the light-load Hopf margin
`|δ| − arccos((D ω_c + D²/M)/K₀)`. -/
def angleFrozen (δ : ℝ) : ℝ :=
  if g.K0 < g.fastBound then Real.pi / 2 - |δ|
  else min (Real.pi / 2 - |δ|) (|δ| - Real.arccos (g.fastBound / g.K0))

/-- **Frozen-coefficient criterion, grid-angle channel**: with the grid angle modulated as
`u(t) = ε cos(ω_p t)` (the input of `VSMLPF.fieldU`, whose Jacobian at the angle `δ` is
`J(δ − u)`, `VSMLPF.fderiv_fieldU`), `ε ≥ 0`, `ω_p ≠ 0`, `K₀ > 0`, `|δ| < π/2`, the frozen
Jacobian `J(δ − ε cos(ω_p t))` is Hurwitz at every instant iff `ε < angleFrozen δ`: the swing
`[δ − ε, δ + ε]` of the frozen angle must stay inside `(−π/2, π/2)` (fold side) and, at light load
`K₀ ≥ D ω_c + D²/M`, outside `[−arccos((D ω_c + D²/M)/K₀), arccos((D ω_c + D²/M)/K₀)]` (Hopf
side). A statement about a family of constant matrices only. -/
@[tmio M, powerlib_domain] theorem frozen_angle_hurwitz_forall_iff (hM : 0 < g.M)
    (hD : 0 < g.D) (hω : 0 < g.ωc) (hK0 : 0 < g.K0) {δ : ℝ} (hδ : |δ| < Real.pi / 2)
    {ε ωp : ℝ} (hε : 0 ≤ ε) (hωp : ωp ≠ 0) :
    (∀ t : ℝ, LinearSystems.IsHurwitz (g.jacobian (δ - ε * Real.cos (ωp * t)))) ↔
      ε < g.angleFrozen δ := by
  have hB : 0 < g.fastBound := by simp only [fastBound]; positivity
  rw [forall_congr' fun t => g.isHurwitz_jacobian_iff hM hD hω (δ - ε * Real.cos (ωp * t))]
  -- the frozen angles fill the interval `[δ − ε, δ + ε]`
  have hint : (∀ t : ℝ, 0 < g.K0 * Real.cos (δ - ε * Real.cos (ωp * t)) ∧
      g.K0 * Real.cos (δ - ε * Real.cos (ωp * t)) < g.fastBound) ↔
      ∀ θ, δ - ε ≤ θ → θ ≤ δ + ε → 0 < g.K0 * Real.cos θ ∧ g.K0 * Real.cos θ < g.fastBound := by
    constructor
    · intro h θ h1 h2
      rcases hε.eq_or_lt with h0 | h0
      · have hθ : θ = δ := by rw [← h0] at h1 h2; linarith
        have := h 0
        rwa [← h0, zero_mul, sub_zero, ← hθ] at this
      · have hc1 : -1 ≤ (δ - θ) / ε := by rw [le_div_iff₀ h0]; linarith
        have hc2 : (δ - θ) / ε ≤ 1 := by rw [div_le_iff₀ h0]; linarith
        have := h (Real.arccos ((δ - θ) / ε) / ωp)
        rwa [mul_div_cancel₀ _ hωp, Real.cos_arccos hc1 hc2, mul_div_cancel₀ _ h0.ne',
          sub_sub_cancel] at this
    · intro h t
      have hc1 := Real.neg_one_le_cos (ωp * t)
      have hc2 := Real.cos_le_one (ωp * t)
      exact h _ (by nlinarith) (by nlinarith)
  rw [hint]
  have hπ := Real.pi_pos
  -- the fold side
  have hfold : (∀ θ, δ - ε ≤ θ → θ ≤ δ + ε → 0 < g.K0 * Real.cos θ) ↔
      ε < Real.pi / 2 - |δ| := by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      rcases le_or_gt 0 δ with h0 | h0
      · have := h (Real.pi / 2) (by rw [abs_of_nonneg h0] at hδ; linarith)
          (by rw [abs_of_nonneg h0] at hc; linarith)
        rw [Real.cos_pi_div_two, mul_zero] at this
        exact lt_irrefl _ this
      · have := h (-(Real.pi / 2)) (by rw [abs_of_neg h0] at hc; linarith)
          (by rw [abs_of_neg h0] at hδ; linarith)
        rw [Real.cos_neg, Real.cos_pi_div_two, mul_zero] at this
        exact lt_irrefl _ this
    · intro h θ h1 h2
      refine mul_pos hK0 (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
        cases abs_cases δ <;> linarith
  -- the Hopf side, at light load
  set r := Real.arccos (g.fastBound / g.K0)
  have hr0 : 0 ≤ r := Real.arccos_nonneg _
  have hrπ : r ≤ Real.pi := Real.arccos_le_pi _
  have hcr : ∀ hKB : g.fastBound ≤ g.K0, Real.cos r = g.fastBound / g.K0 := fun hKB =>
    Real.cos_arccos (by
      have : 0 < g.fastBound / g.K0 := div_pos hB hK0
      linarith) ((div_le_one hK0).mpr hKB)
  have hhopf1 : g.fastBound ≤ g.K0 →
      (∀ θ, δ - ε ≤ θ → θ ≤ δ + ε → g.K0 * Real.cos θ < g.fastBound) → ε < |δ| - r := by
    intro hKB h
    by_contra hc
    push Not at hc
    -- the frozen angle of the swing closest to zero
    have key : ∃ θ, δ - ε ≤ θ ∧ θ ≤ δ + ε ∧ |θ| ≤ r := by
      rcases le_or_gt 0 δ with h0 | h0
      · refine ⟨max (δ - ε) 0, le_max_left _ _, by
          rcases le_total (δ - ε) 0 with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith, ?_⟩
        rw [abs_of_nonneg (le_max_right _ _)]
        rw [abs_of_nonneg h0] at hc
        exact max_le (by linarith) hr0
      · refine ⟨min (δ + ε) 0, by
          rcases le_total (δ + ε) 0 with h' | h'
          · rw [min_eq_left h']; linarith
          · rw [min_eq_right h']; linarith, min_le_left _ _, ?_⟩
        rw [abs_of_nonpos (min_le_right _ _)]
        rw [abs_of_neg h0] at hc
        rw [neg_le]
        exact le_min (by linarith) (by linarith)
    obtain ⟨θ, h1, h2, h3⟩ := key
    have hcos : g.fastBound / g.K0 ≤ Real.cos θ := by
      rw [← hcr hKB, ← Real.cos_abs θ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hrπ h3
    have := h θ h1 h2
    rw [div_le_iff₀ hK0] at hcos
    linarith
  have hhopf2 : g.fastBound ≤ g.K0 → ε < Real.pi / 2 - |δ| → ε < |δ| - r →
      ∀ θ, δ - ε ≤ θ → θ ≤ δ + ε → g.K0 * Real.cos θ < g.fastBound := by
    intro hKB hf hh θ h1 h2
    have habs : |δ| - ε ≤ |θ| := by
      have h3 := abs_sub_abs_le_abs_sub δ θ
      have h4 : |δ - θ| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      have : |θ| ≤ |δ| + ε := by
        have := abs_add_le δ (θ - δ)
        rw [add_sub_cancel] at this
        have : |θ - δ| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      linarith
    have hcos : Real.cos θ < g.fastBound / g.K0 := by
      rw [← hcr hKB, ← Real.cos_abs θ]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hr0 hθπ (by linarith)
    rw [lt_div_iff₀ hK0] at hcos
    linarith
  unfold angleFrozen
  split_ifs with hKB
  · rw [← hfold]
    constructor
    · intro h θ h1 h2; exact (h θ h1 h2).1
    · intro h θ h1 h2
      refine ⟨h θ h1 h2, ?_⟩
      have := Real.cos_le_one θ
      nlinarith
  · push Not at hKB
    rw [lt_min_iff]
    constructor
    · intro h
      exact ⟨hfold.mp fun θ h1 h2 => (h θ h1 h2).1,
        hhopf1 hKB fun θ h1 h2 => (h θ h1 h2).2⟩
    · rintro ⟨hf, hh⟩ θ h1 h2
      exact ⟨hfold.mpr hf θ h1 h2, hhopf2 hKB hf hh θ h1 h2⟩

end VSMLPF

end powerlib.GFM
