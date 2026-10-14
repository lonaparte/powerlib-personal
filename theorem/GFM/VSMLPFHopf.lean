import theorem.GFM.VSMLPF
import theorem.Dynamics.Degenerate.WeakFocus

/-! # VSM with a power filter on its Hopf boundary: local asymptotic stability (three states)

Model boundary.
The three-state family `VSMLPF.family` of `theorem/GFM/VSMLPF.lean`, unchanged:
state `z = (δ − δ*, ω, P_f − P₀)`, the field translated so that the selected point `(δ*, 0, P₀)` is
the origin; continuous time, autonomous (grid angle `u = 0`),
`δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)`; constant internal EMF, lossless
grid reactance, export-positive active power; no voltage / reactive-power loop, inner current and
voltage loops, current limiting, PLL, delay, PWM or network dynamics. `K = K₀ cos δ*`
(`VSMLPF.Model.K`). The physical range is `M, D, ω_c > 0` (requirement `.physical`).

Source: work-sync `projects/vsc-parametric-oscillation/…/gfm-driven-gfl-parametric-resonance/
notes/concepts/gfm-periodic-source.md` ("三态局部候选"); `notes/theory-draft.md` §1.3. This module
settles the Hopf-boundary case of `theorem/GFM/VSMLPF.lean`.

Results.
On the Hopf boundary `K = D ω_c + D²/M` (at a balanced angle) the Jacobian has the eigenvalues
`±j√(D ω_c / M)` and `−(ω_c + D/M)`, so local exponential stability fails
(`VSMLPF.exactUnder_locallyExponentiallyStable`) and the nonlinear terms decide. With
`H = D ω_c / M`, `λ = ω_c + D/M` and the coordinates (`VSMLPF.hopfCoord`)
`a = λ (δ − δ*) + ω`, `b = ω_c ω − (P_f − P₀)/M`, `c = H (δ − δ*) − (D/M) ω − (P_f − P₀)/M`,
the loop is exactly `ȧ = b`, `ḃ = −H a − G`, `ċ = −λ c − G`, where
`G = (ω_c/M) (K (sin x − x) + P₀ (cos x − 1))` and `x = δ − δ* = (λ a − b + c)/(H + λ²)`.
Hence `g₂ = −ω_c P₀ / (2M)`, `g₃ = −ω_c K / (6M)` and the weak-focus coefficient of
`Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus` is
`κ = (ω_c P₀ / M)² (8H + λ²)/2 + H λ ω_c K (4H + λ²)/(2M) > 0`: every physical boundary model is a
weak stable focus (a supercritical Hopf point), at every load.

Family and connection conclusions.
No new family: connection conclusions on `VSMLPF.family`.
* `VSMLPF.mem_den_locallyAsymptoticallyStable_of_hopf`: positive `M, D, ω_c`, a balanced angle and
  `K = D ω_c + D²/M` place a model in local asymptotic stability.
* `VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`: within positive `M, D, ω_c`, local
  asymptotic stability of `(δ*, 0, P₀)` holds exactly at a balanced angle with
  `0 < K ≤ D ω_c + D²/M`. A slow filter or `K < 0` is unstable (`VSMLPF.mem_den_unstable`,
  `VSMLPF.mem_den_unstable_of_K_neg`); at `K = 0` (a fold, or a vanishing power curve)
  `S = D ω_c (δ − δ*) + M ω_c ω − (P_f − P₀)` changes at the rate `ω_c P₀ (1 − cos(δ − δ*))`, which
  has one sign, so states arbitrarily close with `S` of the other sign never reach the operating
  point (`Dynamics.not_localAsymptoticStable_of_lie_nonpos`). No case is left open.
* `VSMLPF.not_exactUnder_locallyAsymptoticallyStable` (the local asymptotic translation is **not**
  exact within positive `M, D, ω_c`): it asks for the strict fast-filter condition, but the
  boundary model `VSMLPF.hopfBoundary` (`M = D = ω_c = 1`, `P₀ = 0`, `K₀ = 2`, `δ* = 0`, so
  `K = 2 = D ω_c + D²/M`) is locally asymptotically stable
  (`VSMLPF.hopfBoundary_mem_den_locallyAsymptoticallyStable`) and not locally exponentially stable
  (`VSMLPF.hopfBoundary_not_mem_den_locallyExponentiallyStable`).
* `VSMLPF.locallyAsymptoticallyStable_iff`: at the loading angle (`|P₀| < K₀`, positive
  parameters) local asymptotic stability holds iff `K ≤ D ω_c + D²/M`, the boundary included
  (compare `VSMLPF.locallyExponentiallyStable_iff`, which must exclude it).

Scope note: a SymPy computation (untrusted, not a library result) gives the first Lyapunov
coefficient on the boundary as a negative multiple of
`D⁸ + 8D⁶M²h² + 14D⁴M⁴h⁴ + 8D²M⁶h⁶ + M⁸h⁸ + P₀² M² (D⁴ + 10 D²M²h² + M⁴h⁴)`, `h² = D ω_c / M`;
the formal proof uses only the explicit Lyapunov function.
-/

noncomputable section
namespace powerlib.GFM
namespace VSMLPF
open Set Matrix
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)

private theorem mem_den_flow_iff' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.g.field m.point :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- The Hopf coordinates `(a, b, c)` of the translated state `z = (δ − δ*, ω, P_f − P₀)`:
`a = λ z₀ + z₁`, `b = ω_c z₁ − z₂/M`, `c = H z₀ − (D/M) z₁ − z₂/M` with `λ = ω_c + D/M`,
`H = D ω_c / M`. -/
def hopfCoord (m : Model) : State 3 →L[ℝ] State 3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
    !![m.g.ωc + m.g.D / m.g.M, 1, 0;
      0, m.g.ωc, -(1 / m.g.M);
      m.g.D * m.g.ωc / m.g.M, -(m.g.D / m.g.M), -(1 / m.g.M)]

@[simp, powerlib_foundation] theorem hopfCoord_apply_zero (m : Model) (z : State 3) :
    hopfCoord m z 0 = (m.g.ωc + m.g.D / m.g.M) * z 0 + z 1 := by
  simp [hopfCoord, toEuclideanCLM_apply3]

@[simp, powerlib_foundation] theorem hopfCoord_apply_one (m : Model) (z : State 3) :
    hopfCoord m z 1 = m.g.ωc * z 1 - z 2 / m.g.M := by
  simp [hopfCoord, toEuclideanCLM_apply3]; ring

@[simp, powerlib_foundation] theorem hopfCoord_apply_two (m : Model) (z : State 3) :
    hopfCoord m z 2 = m.g.D * m.g.ωc / m.g.M * z 0 - m.g.D / m.g.M * z 1 - z 2 / m.g.M := by
  simp [hopfCoord, toEuclideanCLM_apply3]; ring

/-- The angle deviation is recovered from the Hopf coordinates:
`(λ a − b + c)/(H + λ²) = δ − δ*`. -/
@[powerlib_foundation] theorem hopfCoord_angle (m : Model) (hM : 0 < m.g.M) (hD : 0 < m.g.D)
    (hω : 0 < m.g.ωc) (z : State 3) :
    ((m.g.ωc + m.g.D / m.g.M) * hopfCoord m z 0 - hopfCoord m z 1 + hopfCoord m z 2) /
      (m.g.D * m.g.ωc / m.g.M + (m.g.ωc + m.g.D / m.g.M) ^ 2) = z 0 := by
  have hS : m.g.D * m.g.ωc / m.g.M + (m.g.ωc + m.g.D / m.g.M) ^ 2 ≠ 0 := by positivity
  rw [div_eq_iff hS, hopfCoord_apply_zero, hopfCoord_apply_one, hopfCoord_apply_two]
  ring

/-- Components of the translated field. -/
private theorem field_apply (m : Model) (z : State 3) :
    m.field z 0 = z 1 ∧ m.field z 1 = (-z 2 - m.g.D * z 1) / m.g.M ∧
      m.field z 2 = m.g.ωc * (m.g.K0 * Real.sin (z 0 + m.δ) - z 2 - m.g.P0) := by
  simp only [Model.field, VSMLPF.field_apply_zero, VSMLPF.field_apply_one, VSMLPF.field_apply_two,
    PiLp.add_apply, Model.point, mk3_zero, mk3_one, mk3_two]
  exact ⟨by ring, by ring, by ring⟩

/-- At a balanced angle the restoring power is `K₀ sin(x + δ*) − P₀ = K sin x + P₀ (cos x − 1)`. -/
private theorem restoring (m : Model) (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (x : ℝ) :
    m.g.K0 * Real.sin (x + m.δ) - m.g.P0 = m.K * Real.sin x + m.g.P0 * (Real.cos x - 1) := by
  rw [Real.sin_add, ← hb, Model.K]
  ring

/-- The boundary loop in Hopf coordinates (local asymptotic stability). -/
private theorem las_of_hopf {m : Model} (hM : 0 < m.g.M) (hD : 0 < m.g.D) (hω : 0 < m.g.ωc)
    (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    LocalAsymptoticStable m.field 0 := by
  have hMne : m.g.M ≠ 0 := hM.ne'
  have hC : ContDiff ℝ 1 m.field := by
    show ContDiff ℝ 1 fun z => m.g.field (z + m.point)
    exact m.g.contDiff_field.comp (contDiff_id.add contDiff_const)
  have hT : Function.Injective (hopfCoord m) := by
    refine (injective_iff_map_eq_zero (hopfCoord m)).mpr fun z hz => ?_
    have h0 := congrArg (fun w : State 3 => w 0) hz
    have h1 := congrArg (fun w : State 3 => w 1) hz
    have h2 := hopfCoord_angle m hM hD hω z
    simp only [PiLp.zero_apply] at h0 h1
    rw [h0, h1, congrArg (fun w : State 3 => w 2) hz] at h2
    simp only [PiLp.zero_apply, mul_zero, sub_zero, add_zero, zero_div] at h2
    rw [hopfCoord_apply_zero, ← h2, mul_zero, zero_add] at h0
    rw [hopfCoord_apply_one, h0, mul_zero, zero_sub, neg_eq_zero, div_eq_zero_iff,
      or_iff_left hMne] at h1
    exact state3_ext (by rw [← h2]; rfl) (by rw [h0]; rfl) (by rw [h1]; rfl)
  refine Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus (T := hopfCoord m)
    (G := fun z => m.g.ωc / m.g.M * (m.K * (Real.sin (z 0) - z 0) +
      m.g.P0 * (Real.cos (z 0) - 1)))
    (H := m.g.D * m.g.ωc / m.g.M) (lam := m.g.ωc + m.g.D / m.g.M)
    (g2 := -(m.g.ωc / m.g.M * m.g.P0) / 2) (g3 := -(m.g.ωc / m.g.M * m.K) / 6)
    hC hT (by positivity) (by positivity) (fun z => ?_) (fun z => ?_) (fun z => ?_) ?_ ?_
  · obtain ⟨f0, f1, -⟩ := field_apply m z
    rw [hopfCoord_apply_zero, hopfCoord_apply_one, f0, f1]
    field_simp
    ring
  · obtain ⟨-, f1, f2⟩ := field_apply m z
    have hs : m.g.K0 * Real.sin (z 0 + m.δ) =
        m.K * Real.sin (z 0) + m.g.P0 * (Real.cos (z 0) - 1) + m.g.P0 := by
      linarith [restoring m hb (z 0)]
    show hopfCoord m (m.field z) 1 = -(m.g.D * m.g.ωc / m.g.M) * hopfCoord m z 0 -
      m.g.ωc / m.g.M * (m.K * (Real.sin (z 0) - z 0) + m.g.P0 * (Real.cos (z 0) - 1))
    rw [hopfCoord_apply_one, hopfCoord_apply_zero, f1, f2, hs, hK]
    field_simp
    ring
  · obtain ⟨f0, f1, f2⟩ := field_apply m z
    have hs : m.g.K0 * Real.sin (z 0 + m.δ) =
        m.K * Real.sin (z 0) + m.g.P0 * (Real.cos (z 0) - 1) + m.g.P0 := by
      linarith [restoring m hb (z 0)]
    show hopfCoord m (m.field z) 2 = -(m.g.ωc + m.g.D / m.g.M) * hopfCoord m z 2 -
      m.g.ωc / m.g.M * (m.K * (Real.sin (z 0) - z 0) + m.g.P0 * (Real.cos (z 0) - 1))
    rw [hopfCoord_apply_two, hopfCoord_apply_two, f0, f1, f2, hs, hK]
    field_simp
    ring
  · refine ⟨1, one_pos, m.g.ωc / m.g.M * (|m.K| / 100 + |m.g.P0| * (5 / 96)), fun z hz => ?_⟩
    rw [hopfCoord_angle m hM hD hω z] at hz ⊢
    set x := z 0
    have hs := Real.sin_bound hz
    have hc := Real.cos_bound hz
    have hx5 : |x| ^ 5 ≤ |x| ^ 4 := pow_le_pow_of_le_one (abs_nonneg x) hz (by norm_num)
    have hx4 : |x| ^ 4 = x ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
    have hwM : 0 < m.g.ωc / m.g.M := div_pos hω hM
    have e : m.g.ωc / m.g.M * (m.K * (Real.sin x - x) + m.g.P0 * (Real.cos x - 1)) -
        (-(m.g.ωc / m.g.M * m.g.P0) / 2 * x ^ 2 + -(m.g.ωc / m.g.M * m.K) / 6 * x ^ 3) =
        m.g.ωc / m.g.M * (m.K * (Real.sin x - (x - x ^ 3 / 6)) +
          m.g.P0 * (Real.cos x - (1 - x ^ 2 / 2))) := by ring
    show |m.g.ωc / m.g.M * (m.K * (Real.sin x - x) + m.g.P0 * (Real.cos x - 1)) -
        (-(m.g.ωc / m.g.M * m.g.P0) / 2 * x ^ 2 + -(m.g.ωc / m.g.M * m.K) / 6 * x ^ 3)| ≤ _
    rw [e, abs_mul, abs_of_pos hwM, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hwM.le
    calc |m.K * (Real.sin x - (x - x ^ 3 / 6)) + m.g.P0 * (Real.cos x - (1 - x ^ 2 / 2))|
        ≤ |m.K| * |Real.sin x - (x - x ^ 3 / 6)| + |m.g.P0| * |Real.cos x - (1 - x ^ 2 / 2)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |m.K| * (|x| ^ 4 / 100) + |m.g.P0| * (|x| ^ 4 * (5 / 96)) := by
          gcongr
          exact hs.trans (by linarith)
      _ = (|m.K| / 100 + |m.g.P0| * (5 / 96)) * x ^ 4 := by rw [hx4]; ring
  · have hKpos : 0 < m.K := by rw [hK]; positivity
    have e : Dynamics.Degenerate.hopfCoeff (m.g.D * m.g.ωc / m.g.M) (m.g.ωc + m.g.D / m.g.M)
        (-(m.g.ωc / m.g.M * m.g.P0) / 2) (-(m.g.ωc / m.g.M * m.K) / 6) =
        (m.g.ωc / m.g.M * m.g.P0) ^ 2 / 2 *
            (8 * (m.g.D * m.g.ωc / m.g.M) + (m.g.ωc + m.g.D / m.g.M) ^ 2) +
          m.g.D * m.g.ωc / m.g.M * (m.g.ωc + m.g.D / m.g.M) * (m.g.ωc / m.g.M) * m.K / 2 *
            (4 * (m.g.D * m.g.ωc / m.g.M) + (m.g.ωc + m.g.D / m.g.M) ^ 2) := by
      unfold Dynamics.Degenerate.hopfCoeff; ring
    rw [e]
    have h1 : 0 ≤ (m.g.ωc / m.g.M * m.g.P0) ^ 2 / 2 *
        (8 * (m.g.D * m.g.ωc / m.g.M) + (m.g.ωc + m.g.D / m.g.M) ^ 2) := by positivity
    have h2 : 0 < m.g.D * m.g.ωc / m.g.M * (m.g.ωc + m.g.D / m.g.M) * (m.g.ωc / m.g.M) * m.K / 2 *
        (4 * (m.g.D * m.g.ωc / m.g.M) + (m.g.ωc + m.g.D / m.g.M) ^ 2) := by positivity
    linarith

/-- `‖(0, 0, t)‖ = |t|`. -/
private theorem norm_mk3_zero_zero (t : ℝ) : ‖mk3 0 0 t‖ = |t| := by
  have h : ‖mk3 0 0 t‖ ^ 2 = t ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp
  rw [← abs_norm, ← sq_eq_sq_iff_abs_eq_abs]
  exact h

/-- With `K = 0` at a balanced angle, `S = D ω_c (δ − δ*) + M ω_c ω − (P_f − P₀)` changes at the
rate `ω_c P₀ (1 − cos(δ − δ*))`, of one sign: the operating point is not attractive. -/
private theorem not_las_of_K_zero {m : Model} (hM : 0 < m.g.M) (hω : 0 < m.g.ωc)
    (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : m.K = 0) :
    ¬ LocalAsymptoticStable m.field 0 := by
  have hC : ContDiff ℝ 1 m.field := by
    show ContDiff ℝ 1 fun z => m.g.field (z + m.point)
    exact m.g.contDiff_field.comp (contDiff_id.add contDiff_const)
  set S : State 3 →L[ℝ] ℝ := (m.g.D * m.g.ωc) • EuclideanSpace.proj (0 : Fin 3) +
    (m.g.M * m.g.ωc) • EuclideanSpace.proj (1 : Fin 3) - EuclideanSpace.proj (2 : Fin 3) with hS
  have hSz : ∀ z : State 3, S z = m.g.D * m.g.ωc * z 0 + m.g.M * m.g.ωc * z 1 - z 2 := by
    intro z; simp [hS]
  have hSlie : ∀ z : State 3, S (m.field z) = m.g.ωc * m.g.P0 * (1 - Real.cos (z 0)) := by
    intro z
    obtain ⟨f0, f1, f2⟩ := field_apply m z
    have hs : m.g.K0 * Real.sin (z 0 + m.δ) = m.g.P0 * (Real.cos (z 0) - 1) + m.g.P0 := by
      have hr := restoring m hb (z 0)
      rw [hK, zero_mul, zero_add] at hr
      linarith
    rw [hSz, f0, f1, f2, hs]
    field_simp
    ring
  have hcos : ∀ z : State 3, 0 ≤ 1 - Real.cos (z 0) := fun z => by
    linarith [Real.cos_le_one (z 0)]
  rcases le_or_gt 0 m.g.P0 with hP | hP
  · refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := ⇑(-S)) (ρ := 1) hC
      (-S).differentiable one_pos (fun x _ => ?_) (fun ε hε => ⟨mk3 0 0 (-(ε / 2)), ?_, ?_⟩)
    · rw [(-S).fderiv]
      show -S (m.field x) ≤ 0
      rw [hSlie]
      have := mul_nonneg (mul_nonneg hω.le hP) (hcos x)
      linarith
    · rw [sub_zero, norm_mk3_zero_zero, abs_neg, abs_of_pos (by linarith)]; linarith
    · show -S (mk3 0 0 (-(ε / 2))) < -S 0
      rw [hSz, hSz]
      simp
      linarith
  · refine Dynamics.not_localAsymptoticStable_of_lie_nonpos (V := ⇑S) (ρ := 1) hC
      S.differentiable one_pos (fun x _ => ?_) (fun ε hε => ⟨mk3 0 0 (ε / 2), ?_, ?_⟩)
    · rw [S.fderiv, hSlie]
      have h1 : 0 ≤ m.g.ωc * -m.g.P0 * (1 - Real.cos (x 0)) :=
        mul_nonneg (mul_nonneg hω.le (neg_nonneg.mpr hP.le)) (hcos x)
      have e : m.g.ωc * m.g.P0 * (1 - Real.cos (x 0)) =
          -(m.g.ωc * -m.g.P0 * (1 - Real.cos (x 0))) := by ring
      rw [e]
      linarith
    · rw [sub_zero, norm_mk3_zero_zero, abs_of_pos (by linarith)]; linarith
    · rw [hSz, hSz]
      simp
      linarith

/-! ### Connection conclusions -/

/-- **Hopf boundary.** Positive `M, D, ω_c`, a balanced angle and `K = D ω_c + D²/M` place a model
in local asymptotic stability: the boundary point is a weak stable focus (supercritical Hopf), at
every load. -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_hopf (m : Model)
    (hM : 0 < m.g.M) (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0)
    (hK : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact family_isAutonomous.mem_den_flow.mpr (las_of_hopf hM hD hω hb hK)

/-- **Local asymptotic stability within positive `M, D, ω_c`.** The operating point `(δ*, 0, P₀)`
is locally asymptotically stable exactly when the angle is balanced and
`0 < K ≤ D ω_c + D²/M` (the Hopf boundary included). -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_physical (m : Model)
    (hM : 0 < m.g.M) (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.g.K0 * Real.sin m.δ = m.g.P0 ∧ 0 < m.K ∧
        m.K ≤ m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hm
    have hlas : LocalAsymptoticStable m.field 0 := family_isAutonomous.mem_den_flow.mp hm
    have hls : LyapunovStable m.g.field m.point :=
      mem_den_flow_iff'.mp (family_isAutonomous.mem_den_flow (P := .lyapunovStable) |>.mpr hlas.1)
    have heq := Dynamics.isEquilibrium_of_lyapunovStable m.g.contDiff_field hls
    have hb : m.g.K0 * Real.sin m.δ = m.g.P0 := by
      have := ((m.g.field_eq_zero_iff hM.ne' hω.ne' _).mp heq).2.2
      simpa [Model.point] using this
    refine ⟨hb, ?_, ?_⟩
    · rcases lt_trichotomy m.K 0 with hK | hK | hK
      · have hu := mem_den_unstable_of_K_neg m hM hD hω hb hK
        unfold powerlib.TMIO.Statement at hu
        exact absurd hls (mem_den_flow_iff'.mp hu)
      · exact absurd hlas (not_las_of_K_zero hM hω hb hK)
      · exact hK
    · by_contra hn
      have hu := mem_den_unstable m hM hD hω hb (lt_of_not_ge hn)
      unfold powerlib.TMIO.Statement at hu
      exact absurd hls (mem_den_flow_iff'.mp hu)
  · rintro ⟨hb, hK0, hKle⟩
    rcases lt_or_eq_of_le hKle with hlt | heq
    · have hl := mem_den_locallyExponentiallyStable m hM hD hω hb hK0 hlt
      unfold powerlib.TMIO.Statement at hl
      exact family_isAutonomous.mem_den_flow.mpr
        (Flow.locallyExponentiallyStable_localAsymptoticStable
          (family_isAutonomous.mem_den_flow.mp hl))
    · exact family_isAutonomous.mem_den_flow.mpr (las_of_hopf hM hD hω hb heq)

/-- The Hopf boundary model `M = D = ω_c = 1`, `P₀ = 0`, `K₀ = 2`, `δ* = 0`:
`K = 2 = D ω_c + D²/M`. -/
def hopfBoundary : Model := ⟨⟨1, 1, 1, 0, 2⟩, 0⟩

/-- The Hopf boundary model is locally asymptotically stable. -/
@[powerlib_domain] theorem hopfBoundary_mem_den_locallyAsymptoticallyStable :
    connection% (hopfBoundary ∈ family.den (.flow .locallyAsymptoticallyStable)) :=
  mem_den_locallyAsymptoticallyStable_of_hopf hopfBoundary one_pos one_pos one_pos
    (by simp [hopfBoundary]) (by norm_num [hopfBoundary, Model.K])

/-- The Hopf boundary model is not locally exponentially stable (its Jacobian is not Hurwitz). -/
@[powerlib_domain] theorem hopfBoundary_not_mem_den_locallyExponentiallyStable :
    connection% (hopfBoundary ∉ family.den (.flow .locallyExponentiallyStable)) := by
  have hex := exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hex ⊢
  unfold Family.ExactUnder TMIO.ExactUnder at hex
  intro h
  have hI : hopfBoundary ∈ TMIO.realize family.meets {.physical} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    show 0 < (1 : ℝ) ∧ 0 < (1 : ℝ) ∧ 0 < (1 : ℝ)
    norm_num
  have h' : hopfBoundary ∈ TMIO.realize family.meets
      (family.translate (.flow .locallyExponentiallyStable) ∪ {.physical}) := by
    rw [hex]
    exact ⟨h, hI⟩
  rw [TMIO.mem_realize] at h'
  have hf : Meets hopfBoundary .fastFilter := h' .fastFilter (by simp [family, translate])
  norm_num [Meets, hopfBoundary, Model.K] at hf

/-- **The local asymptotic translation is not exact within positive `M, D, ω_c`.** The translation
asks for the strict fast-filter condition `K < D ω_c + D²/M`, but the Hopf boundary model is
locally asymptotically stable. -/
@[powerlib_domain] theorem not_exactUnder_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.physical} (.flow .locallyAsymptoticallyStable)) := by
  have hmem := hopfBoundary_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem ⊢
  unfold Family.ExactUnder TMIO.ExactUnder
  intro h
  have hI : hopfBoundary ∈ TMIO.realize family.meets {.physical} := by
    rw [TMIO.mem_realize]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    show 0 < (1 : ℝ) ∧ 0 < (1 : ℝ) ∧ 0 < (1 : ℝ)
    norm_num
  have h' : hopfBoundary ∈ TMIO.realize family.meets
      (family.translate (.flow .locallyAsymptoticallyStable) ∪ {.physical}) := by
    rw [h]
    exact ⟨hmem, hI⟩
  rw [TMIO.mem_realize] at h'
  have hf : Meets hopfBoundary .fastFilter := h' .fastFilter (by simp [family, translate])
  norm_num [Meets, hopfBoundary, Model.K] at hf

private theorem sin_δ0' {g : VSMLPF} (hK0 : 0 < g.K0) (h : |g.P0| ≤ g.K0) :
    g.K0 * Real.sin g.δ0 = g.P0 := by
  have ha : |g.P0 / g.K0| ≤ 1 := by rw [abs_div, abs_of_pos hK0, div_le_one hK0]; exact h
  simp only [δ0]
  rw [Real.sin_arcsin (abs_le.mp ha).1 (abs_le.mp ha).2]
  field_simp

/-- At the loading angle (`|P₀| < K₀`, positive parameters) the equilibrium is locally
asymptotically stable iff `K ≤ D ω_c + D²/M`: the Hopf boundary is included. -/
@[powerlib_domain] theorem locallyAsymptoticallyStable_iff {g : VSMLPF} (hp : g.Pos)
    (h : |g.P0| < g.K0) :
    connection% (atLoading g ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      atLoading g ∈ {m : Model | m.K ≤ m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M}) := by
  have hiff := mem_den_locallyAsymptoticallyStable_iff_of_physical (atLoading g) hp.M hp.D hp.ωc
  unfold powerlib.TMIO.Statement at hiff ⊢
  rw [hiff, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · exact fun h' => h'.2.2
  · exact fun hK => ⟨sin_δ0' hp.K0 h.le, g.K_pos hp.K0 h, hK⟩

end VSMLPF
end powerlib.GFM
