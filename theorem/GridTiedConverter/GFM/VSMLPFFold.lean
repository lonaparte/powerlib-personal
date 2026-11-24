import theorem.GridTiedConverter.GFM.VSMLPFLossy

/-! # VSM with a power filter at the fold: instability, and the Lyapunov-stability denotation

Model boundary.
The three-state family `VSMLPF.family` of `theorem/GridTiedConverter/GFM/VSMLPF.lean`, unchanged:
state `z = (δ − δ*, ω, P_f − P₀)`, the field translated so that the selected point `(δ*, 0, P₀)`
is the origin; continuous time, autonomous, `δ̇ = ω`, `M ω̇ = P₀ − P_f − D ω`,
`Ṗ_f = ω_c (K₀ sin δ − P_f)`; constant EMF, lossless line, export-positive active power; no
voltage loop, inner loops, limiting, PLL, delay, PWM or line dynamics. `K = K₀ cos δ*`
(`VSMLPF.Model.K`); physical range `M, D, ω_c > 0`. The lossy line `P(δ) = c₀ + A sin(δ − α)`
(`VSMLPFLossy.family`, `theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`) is read through
`VSMLPFLossy.den_eq_preimage`.

Source: GFM counterpart study, note t3-bifurcation (d) (`F2`, `F3`: the fold is a nondegenerate
saddle-node; fold function `U = −σ S + zᵀ S_q z`, checked numerically there; scratch notes outside
the repository); Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.3 (Chetaev). The fold function
here keeps only the stable-mode quadratic form (it solves the singular Lyapunov equation with the
angle term absorbed by `S`), so no Taylor remainder is needed.

Results.
At a fold of the power curve (`K = K₀ cos δ* = 0`, `K₀ ≠ 0`, a balanced angle, so
`P₀ = ±K₀ ≠ 0`) the Jacobian has the simple eigenvalue `0` and `−D/M`, `−ω_c`
(`VSMLPF.rootMultiplicity_zero_le_one`), so the linearization decides nothing. With
`S = D ω_c (δ − δ*) + M ω_c ω − (P_f − P₀)` (`Ṡ = ω_c P₀ (1 − cos(δ − δ*))`, the left null vector)
and the quadratic form `V = a ω² + b ω (P_f − P₀) + c (P_f − P₀)²`, `a = M/(2D)`,
`b = −M/(D(D + M ω_c))`, `c = (D(D + M ω_c) + 1)/(2 ω_c D (D + M ω_c))` (`V̇ = −ω² − (P_f − P₀)²`
along the linear part), the fold function `U = −P₀ S + V` (`VSMLPF.foldU`) has, exactly,
`U̇ = −ω_c P₀² (1 − cos x) − ω² − p² − ω_c P₀ (1 − cos x)(b ω + 2c p)` (`x = δ − δ*`,
`p = P_f − P₀`), negative on a punctured neighbourhood, and `U < 0` along `t (P₀, 0, 0)`, `t > 0`:
the operating point is unstable (`Dynamics.unstable_of_eventually_lie_neg`). With a vanishing
power curve (`K₀ = 0`, so `P₀ = 0`) the angle is a conserved direction and the point is Lyapunov
stable: `|S|² + ω² + β² p²`, `β = 1 + 1/(D M ω_c)`, does not increase
(`Dynamics.lyapunovStable_of_inner_nonpos`).

Family and connection conclusions.
No new family: connection conclusions on `VSMLPF.family` and `VSMLPFLossy.family`.
* `VSMLPF.mem_den_unstable_of_fold`: positive `M, D, ω_c`, a balanced angle, `K = 0` and `K₀ ≠ 0`
  place a model in instability.
* `VSMLPF.mem_den_lyapunovStable_iff_of_physical`: within positive `M, D, ω_c`, the operating point
  is Lyapunov stable exactly at a balanced angle with `0 < K ≤ D ω_c + D²/M`, or with a vanishing
  power curve `K₀ = 0` (then `P₀ = 0`). A slow filter, `K < 0` and the fold are unstable
  (`VSMLPF.mem_den_unstable`, `VSMLPF.mem_den_unstable_of_K_neg`,
  `VSMLPF.mem_den_unstable_of_fold`); `0 < K ≤ D ω_c + D²/M` is locally asymptotically stable
  (`VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`). This completes the Lyapunov
  column of `VSMLPF.not_exactUnder_lyapunovStable` (the flat curve is the only gap).
* On a lossy line (through `VSMLPFLossy.den_eq_preimage`):
  `VSMLPFLossy.mem_den_unstable_of_fold` (balanced, `K = A cos(δ* − α) = 0`, `A ≠ 0`) and
  `VSMLPFLossy.mem_den_lyapunovStable_iff_of_physical` (a balanced angle with
  `0 < K ≤ D ω_c + D²/M`, or `A = 0`).
-/

noncomputable section
namespace powerlib.GFM
open Set Filter Topology
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)

namespace VSMLPF

/-! ## The translated field (implementation evidence) -/

@[tmio M, powerlib_domain] private theorem field_zero (m : Model) (z : State 3) :
    m.field z 0 = z 1 := by
  simp only [Model.field, VSMLPF.field_apply_zero, PiLp.add_apply, Model.point, mk3_one]
  ring

@[tmio M, powerlib_domain] private theorem field_one (m : Model) (z : State 3) :
    m.field z 1 = (-z 2 - m.g.D * z 1) / m.g.M := by
  simp only [Model.field, VSMLPF.field_apply_one, PiLp.add_apply, Model.point, mk3_one, mk3_two]
  ring

@[tmio M, powerlib_domain] private theorem field_two (m : Model) (z : State 3) :
    m.field z 2 = m.g.ωc * (m.g.K0 * Real.sin (z 0 + m.δ) - z 2 - m.g.P0) := by
  simp only [Model.field, VSMLPF.field_apply_two, PiLp.add_apply, Model.point, mk3_zero, mk3_two]
  ring

/-- At a balanced angle with `K = 0`: `K₀ sin(x + δ*) = P₀ cos x`. -/
@[tmio M, powerlib_domain] private theorem restoring_fold {m : Model}
    (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : m.K = 0) (x : ℝ) :
    m.g.K0 * Real.sin (x + m.δ) = m.g.P0 * Real.cos x := by
  have hK' : m.g.K0 * Real.cos m.δ = 0 := hK
  rw [Real.sin_add, ← hb]
  linear_combination Real.sin x * hK'

@[tmio M, powerlib_domain] private theorem field_origin {m : Model} (hM : 0 < m.g.M)
    (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0) : m.field 0 = 0 := by
  rw [Model.field, zero_add]
  exact (m.field_point_eq_zero_iff hM.ne' hω.ne').mpr hb

/-! ## The fold function -/

/-- The terms `(coefficient, power of x, power of ω, power of p)` of the fold function
`U = −P₀ (D ω_c x + M ω_c ω − p) + a ω² + b ω p + c p²`. -/
def foldTerms (m : Model) : List (ℝ × ℕ × ℕ × ℕ) :=
  [(-(m.g.P0 * (m.g.D * m.g.ωc)), 1, 0, 0), (-(m.g.P0 * (m.g.M * m.g.ωc)), 0, 1, 0),
    (m.g.P0, 0, 0, 1), (m.g.M / (2 * m.g.D), 0, 2, 0),
    (-(m.g.M / (m.g.D * (m.g.D + m.g.M * m.g.ωc))), 0, 1, 1),
    ((m.g.D * (m.g.D + m.g.M * m.g.ωc) + 1) / (2 * m.g.ωc * m.g.D * (m.g.D + m.g.M * m.g.ωc)),
      0, 0, 2)]

/-- The fold function in the translated coordinates `z = (x, ω, p)`, the polynomial
`Dynamics.Degenerate.poly3` of `foldTerms`. -/
def foldU (m : Model) (z : State 3) : ℝ :=
  Dynamics.Degenerate.poly3 (foldTerms m) (z 0) (z 1) (z 2)

@[tmio M, powerlib_domain] private theorem contDiff_foldU (m : Model) : ContDiff ℝ 1 (foldU m) :=
  Dynamics.Degenerate.contDiff_poly3 _ (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1) (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)

@[tmio M, powerlib_domain] private theorem fderiv_foldU (m : Model) (z v : State 3) :
    fderiv ℝ (foldU m) z v =
      Dynamics.Degenerate.dpoly3 (foldTerms m) (z 0) (z 1) (z 2) (v 0) (v 1) (v 2) :=
  Dynamics.Degenerate.fderiv_poly3_apply (foldTerms m) (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1) (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2) z v

/-- The exact derivative of the fold function along the field at a fold. -/
@[tmio M, powerlib_domain] private theorem foldU_lie {m : Model} (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : m.K = 0)
    (z : State 3) :
    fderiv ℝ (foldU m) z (m.field z) =
      -(m.g.ωc * m.g.P0 ^ 2 * (1 - Real.cos (z 0))) - z 1 ^ 2 - z 2 ^ 2 -
        m.g.ωc * m.g.P0 * (1 - Real.cos (z 0)) *
          (-(m.g.M / (m.g.D * (m.g.D + m.g.M * m.g.ωc))) * z 1 +
            2 * ((m.g.D * (m.g.D + m.g.M * m.g.ωc) + 1) /
              (2 * m.g.ωc * m.g.D * (m.g.D + m.g.M * m.g.ωc))) * z 2) := by
  have hQ : 0 < m.g.D + m.g.M * m.g.ωc := by positivity
  rw [fderiv_foldU, field_zero, field_one, field_two, restoring_fold hb hK]
  simp only [foldTerms, Dynamics.Degenerate.dpoly3_cons, Dynamics.Degenerate.dpoly3_nil]
  norm_num
  field_simp
  ring

/-- A linear form of two small coordinates is bounded by `|P|/2`. -/
@[tmio T, powerlib_foundation] private theorem fold_lin_aux {b c P r y1 y2 : ℝ}
    (hr2 : r ≤ |P| / (2 * (|b| + 2 * |c| + 1))) (h1 : |y1| < r) (h2 : |y2| < r) :
    |b * y1 + 2 * c * y2| ≤ |P| / 2 := by
  have hr0 : 0 ≤ r := (abs_nonneg y1).trans h1.le
  have e1 : |b * y1| ≤ |b| * r := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1.le (abs_nonneg b)
  have e2 : |2 * c * y2| ≤ 2 * |c| * r := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left h2.le (by positivity)
  have h3 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (|b| + 2 * |c| + 1))).mp hr2
  have e3 := abs_add_le (b * y1) (2 * c * y2)
  nlinarith

/-- The cross term is at most half the angle term. -/
@[tmio T, powerlib_foundation] private theorem fold_bound_aux {ω P u y1 y2 L : ℝ} (hω : 0 < ω)
    (hu : 0 ≤ u) (hL : |L| ≤ |P| / 2) :
    -(ω * P ^ 2 * u) - y1 ^ 2 - y2 ^ 2 - ω * P * u * L ≤
      -(ω * P ^ 2 * u / 2) - y1 ^ 2 - y2 ^ 2 := by
  have hwu : 0 ≤ ω * u := mul_nonneg hω.le hu
  have habs : |P * L| ≤ P ^ 2 / 2 := by
    rw [abs_mul]
    calc |P| * |L| ≤ |P| * (|P| / 2) := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      _ = P ^ 2 / 2 := by rw [← sq_abs]; ring
  have hPL : -(P ^ 2 / 2) ≤ P * L := by linarith [neg_abs_le (P * L)]
  have := mul_le_mul_of_nonneg_left hPL hwu
  nlinarith

/-- The bound is positive off the point, for `|x| < 1`. -/
@[tmio T, powerlib_foundation] private theorem fold_pos_aux {ω P x y1 y2 : ℝ} (hω : 0 < ω)
    (hP : P ≠ 0) (hx : |x| < 1) (hne : ¬(x = 0 ∧ y1 = 0 ∧ y2 = 0)) :
    0 < ω * P ^ 2 * (1 - Real.cos x) / 2 + y1 ^ 2 + y2 ^ 2 := by
  have hu : 0 ≤ 1 - Real.cos x := by linarith [Real.cos_le_one x]
  have hA : 0 ≤ ω * P ^ 2 * (1 - Real.cos x) / 2 := by positivity
  by_contra hcon
  push Not at hcon
  have h1 : y1 = 0 := by nlinarith [sq_nonneg y1, sq_nonneg y2]
  have h2 : y2 = 0 := by nlinarith [sq_nonneg y1, sq_nonneg y2]
  have hc : Real.cos x = 1 := by
    have h0 : ω * P ^ 2 * (1 - Real.cos x) = 0 := by nlinarith [sq_nonneg y1, sq_nonneg y2]
    have hωP : ω * P ^ 2 ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp h0).resolve_left hωP]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
  have hx0 : x = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.two_le_pi])
      (by linarith [Real.two_le_pi])).mp hc
  exact hne ⟨hx0, h1, h2⟩

/-- **Saddle-node instability (implementation).** -/
@[tmio TM, powerlib_domain] private theorem unstable_of_fold' {m : Model} (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : m.K = 0)
    (hP : m.g.P0 ≠ 0) : Unstable m.field 0 := by
  set b := -(m.g.M / (m.g.D * (m.g.D + m.g.M * m.g.ωc))) with hbdef
  set c := (m.g.D * (m.g.D + m.g.M * m.g.ωc) + 1) /
    (2 * m.g.ωc * m.g.D * (m.g.D + m.g.M * m.g.ωc)) with hcdef
  have hPpos : 0 < |m.g.P0| := abs_pos.mpr hP
  set r := min 1 (|m.g.P0| / (2 * (|b| + 2 * |c| + 1))) with hrdef
  have hr : 0 < r := lt_min one_pos (by positivity)
  refine Dynamics.unstable_of_eventually_lie_neg m.contDiff_field (field_origin hM hω hb)
    (contDiff_foldU m) ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : State 3) hr),
      self_mem_nhdsWithin] with z hz hne
    rw [foldU_lie hM hD hω hb hK z]
    have hzn : ‖z‖ < r := by simpa using hz
    have hz' : ∀ i : Fin 3, |z i| < r := fun i =>
      lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i) hzn
    have hu : 0 ≤ 1 - Real.cos (z 0) := by linarith [Real.cos_le_one (z 0)]
    have hlin := fold_lin_aux (min_le_right _ _) (hz' 1) (hz' 2)
    have hle := fold_bound_aux (y1 := z 1) (y2 := z 2) hω hu hlin
    have hpos := fold_pos_aux (y1 := z 1) (y2 := z 2) hω hP
      ((hz' 0).trans_le (min_le_left _ _)) fun h =>
        hne (state3_ext (by simpa using h.1) (by simpa using h.2.1) (by simpa using h.2.2))
    linarith
  · refine Dynamics.frequently_of_forall_smul (mk3 m.g.P0 0 0) fun t ht => ?_
    show foldU m (t • mk3 m.g.P0 0 0) < foldU m 0
    simp only [foldU, foldTerms, Dynamics.Degenerate.poly3_cons, Dynamics.Degenerate.poly3_nil,
      PiLp.smul_apply, PiLp.zero_apply, mk3_zero, mk3_one, mk3_two, smul_eq_mul]
    norm_num
    have : 0 < m.g.P0 ^ 2 := by positivity
    nlinarith [mul_pos (mul_pos ht this) (mul_pos hD hω)]

/-- With a vanishing power curve (`K₀ = P₀ = 0`) the operating point is Lyapunov stable:
`|S|² + ω² + β² p²`, `β = 1 + 1/(D M ω_c)`, does not increase. -/
@[tmio TM, powerlib_domain] private theorem lyapunovStable_of_flat {m : Model} (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hK0 : m.g.K0 = 0) (hP : m.g.P0 = 0) :
    LyapunovStable m.field 0 := by
  set β := 1 + 1 / (m.g.D * m.g.M * m.g.ωc) with hβ
  have hβ1 : 1 ≤ β := by rw [hβ]; have : 0 < 1 / (m.g.D * m.g.M * m.g.ωc) := by positivity
                         linarith
  refine Dynamics.lyapunovStable_of_inner_nonpos (by norm_num)
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
      !![m.g.D * m.g.ωc, m.g.M * m.g.ωc, -1; 0, 1, 0; 0, 0, β]) (fun z w hzw => ?_) fun z => ?_
  · have h0 := congrArg (fun y : State 3 => y 0) hzw
    have h1 := congrArg (fun y : State 3 => y 1) hzw
    have h2 := congrArg (fun y : State 3 => y 2) hzw
    simp only [toEuclideanCLM_apply3, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.tail_cons, Matrix.vecHead, zero_mul, one_mul, zero_add,
      add_zero] at h0 h1 h2
    have hβ0 : β ≠ 0 := by positivity
    have e2 : z 2 = w 2 := mul_left_cancel₀ hβ0 h2
    have e0 : z 0 = w 0 := by
      have hDω : m.g.D * m.g.ωc ≠ 0 := by positivity
      apply mul_left_cancel₀ hDω
      linear_combination h0 - m.g.M * m.g.ωc * h1 + e2
    exact state3_ext e0 h1 e2
  · have f0 := field_zero m z
    have f1 := field_one m z
    have f2 := field_two m z
    rw [hK0, hP] at f2
    simp only [zero_mul, zero_sub, sub_zero] at f2
    simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, toEuclideanCLM_apply3,
      RCLike.inner_apply, conj_trivial]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.tail_cons, Matrix.vecHead, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, f0, f1, f2,
      zero_mul, one_mul, zero_add, add_zero]
    have hbr : m.g.D * m.g.ωc * z 1 + m.g.M * m.g.ωc * ((-z 2 - m.g.D * z 1) / m.g.M) +
        -1 * (m.g.ωc * -z 2) = 0 := by field_simp; ring
    rw [hbr, zero_mul, zero_add]
    have hq : (-z 2 - m.g.D * z 1) / m.g.M * z 1 + β * (m.g.ωc * -z 2) * (β * z 2) =
        -(m.g.D / m.g.M) * (z 1 + z 2 / (2 * m.g.D)) ^ 2 -
          (β ^ 2 * m.g.ωc - 1 / (4 * m.g.D * m.g.M)) * z 2 ^ 2 := by
      field_simp; ring
    rw [hq]
    have hβ2 : 1 / (4 * m.g.D * m.g.M) ≤ β ^ 2 * m.g.ωc := by
      have hy : β ^ 2 * m.g.ωc ≥ (1 / (m.g.D * m.g.M * m.g.ωc)) * m.g.ωc := by
        have : 1 / (m.g.D * m.g.M * m.g.ωc) ≤ β ^ 2 := by
          have : 1 / (m.g.D * m.g.M * m.g.ωc) ≤ β := by rw [hβ]; linarith
          nlinarith
        exact mul_le_mul_of_nonneg_right this hω.le
      have e : 1 / (m.g.D * m.g.M * m.g.ωc) * m.g.ωc = 1 / (m.g.D * m.g.M) := by
        field_simp
      have : 1 / (4 * m.g.D * m.g.M) ≤ 1 / (m.g.D * m.g.M) := by
        apply one_div_le_one_div_of_le (by positivity); nlinarith [mul_pos hD hM]
      linarith
    nlinarith [sq_nonneg (z 1 + z 2 / (2 * m.g.D)), sq_nonneg (z 2), div_pos hD hM,
      mul_nonneg (sub_nonneg.mpr hβ2) (sq_nonneg (z 2))]

/-! ## Connection conclusions -/

/-- **The fold is unstable.** Positive `M, D, ω_c`, a balanced angle and a fold of a nonvanishing
power curve (`K = K₀ cos δ* = 0`, `K₀ ≠ 0`) place a model in instability: a saddle-node, unstable
from the side `sign(δ − δ*) = sign P₀` (the fold function `foldU`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold (m : Model) (hM : 0 < m.g.M)
    (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) (hb : m.g.K0 * Real.sin m.δ = m.g.P0) (hK : m.K = 0)
    (hK0 : m.g.K0 ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have hc : Real.cos m.δ = 0 :=
    (mul_eq_zero.mp (show m.g.K0 * Real.cos m.δ = 0 from hK)).resolve_left hK0
  have hP : m.g.P0 ≠ 0 := by
    intro h0
    rw [h0, mul_eq_zero, or_iff_right hK0] at hb
    have := Real.sin_sq_add_cos_sq m.δ
    rw [hb, hc] at this
    norm_num at this
  exact unstable_of_fold' hM hD hω hb hK hP

/-- **Lyapunov stability within positive `M, D, ω_c`.** The operating point `(δ*, 0, P₀)` is
Lyapunov stable exactly when the angle is balanced and either `0 < K ≤ D ω_c + D²/M` or the power
curve vanishes (`K₀ = 0`, then `P₀ = 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_physical (m : Model)
    (hM : 0 < m.g.M) (hD : 0 < m.g.D) (hω : 0 < m.g.ωc) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.g.K0 * Real.sin m.δ = m.g.P0 ∧
        ((0 < m.K ∧ m.K ≤ m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) ∨ m.g.K0 = 0)}) := by
  have hlas := mem_den_locallyAsymptoticallyStable_iff_of_physical m hM hD hω
  unfold powerlib.TMIO.Statement at hlas ⊢
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hm
    have hls : LyapunovStable m.field 0 := family_isAutonomous.mem_den_flow.mp hm
    have hls' : LyapunovStable m.g.field m.point :=
      (Flow.Property.holds_shift_iff (P := .lyapunovStable)).mp hls
    have heq := Dynamics.isEquilibrium_of_lyapunovStable m.g.contDiff_field hls'
    have hb : m.g.K0 * Real.sin m.δ = m.g.P0 := (m.field_point_eq_zero_iff hM.ne' hω.ne').mp heq
    refine ⟨hb, ?_⟩
    have notUnst : m ∉ family.den (.flow .unstable) := fun hu =>
      (family_isAutonomous.mem_den_flow.mp hu : Unstable m.field 0) hls
    rcases lt_trichotomy m.K 0 with hK | hK | hK
    · exact absurd (mem_den_unstable_of_K_neg m hM hD hω hb hK) notUnst
    · by_cases hK0 : m.g.K0 = 0
      · exact Or.inr hK0
      · exact absurd (mem_den_unstable_of_fold m hM hD hω hb hK hK0) notUnst
    · by_cases hf : m.K ≤ m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M
      · exact Or.inl ⟨hK, hf⟩
      · exact absurd (mem_den_unstable m hM hD hω hb (lt_of_not_ge hf)) notUnst
  · rintro ⟨hb, hK | hK0⟩
    · have hl := hlas.mpr ⟨hb, hK⟩
      exact family_isAutonomous.mem_den_flow.mpr (family_isAutonomous.mem_den_flow.mp hl).1
    · have hP : m.g.P0 = 0 := by rw [← hb, hK0, zero_mul]
      exact family_isAutonomous.mem_den_flow.mpr (lyapunovStable_of_flat hM hD hω hK0 hP)

end VSMLPF

/-! ## On a lossy line -/

namespace VSMLPFLossy

/-- **The fold is unstable on a lossy line**: positive `M, D, ω_c`, a balanced angle
`c₀ + A sin(δ* − α) = P_ref`, `K = A cos(δ* − α) = 0` and `A ≠ 0`
(`VSMLPF.mem_den_unstable_of_fold` through `VSMLPFLossy.den_eq_preimage`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold (m : Model) (hM : 0 < m.p.M)
    (hD : 0 < m.p.D) (hω : 0 < m.p.ωc) (hb : m.p.Pe m.δ = m.p.Pref) (hK : m.K = 0)
    (hA : m.p.A ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hv := VSMLPF.mem_den_unstable_of_fold m.toVSMLPF hM hD hω
    (by show m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref - m.p.c0
        rw [Pe] at hb; linarith) hK hA
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hv hd ⊢
  rw [hd, Set.mem_preimage]
  exact hv

/-- **Lyapunov stability on a lossy line within positive `M, D, ω_c`**: exactly a balanced angle
with `0 < K ≤ D ω_c + D²/M`, or a vanishing characteristic amplitude `A = 0`
(`VSMLPF.mem_den_lyapunovStable_iff_of_physical` through `VSMLPFLossy.den_eq_preimage`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_physical (m : Model)
    (hM : 0 < m.p.M) (hD : 0 < m.p.D) (hω : 0 < m.p.ωc) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.p.Pe m.δ = m.p.Pref ∧
        ((0 < m.K ∧ m.K ≤ m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M) ∨ m.p.A = 0)}) := by
  have hv := VSMLPF.mem_den_lyapunovStable_iff_of_physical m.toVSMLPF hM hD hω
  have hd := den_eq_preimage
  unfold powerlib.TMIO.Statement at hv hd ⊢
  rw [hd, Set.mem_preimage, hv, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  refine and_congr ?_ Iff.rfl
  show m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref - m.p.c0 ↔ m.p.Pe m.δ = m.p.Pref
  rw [Pe]
  constructor <;> intro h <;> linarith

end VSMLPFLossy
end powerlib.GFM
