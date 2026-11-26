import theorem.GridTiedConverter.GFM.DCLink.VSMDCPlane
import theorem.SingularPerturbation.UniformBasin

/-! # The VSM–DC converter on `V > 0`: an explicit region-of-attraction estimate

Model boundary.
* The four-state VSM with DC link and DC-voltage PI loop `VSMDC.Model` of
  `theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`: state `(δ, ω, V, ζ)`,
  `δ̇ = ω`, `M ω̇ = P_ff + K_p (V − V*) + K_i ζ − P_e(δ) − D ω`, `C V̇ = (P_src(V) − P_e(δ))/V`,
  `ζ̇ = V − V*`, `P_e(δ) = c₀ + A sin(δ − α)`, `P_src(V) = P_s + I_s V`; continuous time,
  autonomous, export-positive power; parameters arbitrary reals except `V* > 0`.
* The estimate is made on the open half space `V > 0` (the field is singular on `V = 0`): on the
  ball of radius `ρ < V*` about the balanced point `(δ*, 0, V*, ζ*)` the field agrees with a
  globally `C¹` field (`Params.exists_contDiff_eq_field_of_sign`). Excluded as in `VSMDC.lean`.

Source: Khalil, *Nonlinear Systems* (3rd ed., 2002), §8.2 (estimating the region of attraction
from a quadratic Lyapunov function of the linearization and a quadratic remainder bound);
work-sync `theory/T-lyapunov-function-method.md` §1.4 (LaSalle), `theory/T-dc-voltage-gfm.md`
(the DC link as an energy storage of the grid-forming converter); the generic law
`SingularPerturbation.sublevel_subset_regionOfAttraction_of_quadratic`
(`theorem/SingularPerturbation/UniformBasin.lean`).

Results.
* `VSMDC.Model.remainder ρ = |A|/|M| + (V* |A| + |I_s| + |k|)/(|C| V* (V* − ρ))` and
  `VSMDC.Model.norm_field_sub_jacobian_le`: at a balanced point with `V* > 0`, for `|z| < ρ < V*`
  the closed loop differs from its linearization by at most `K(ρ) |z|²`
  (`|f(x* + z) − J z| ≤ K(ρ) |z|²`, `J = Params.jacobian` at the point): the swing row carries the
  sinusoid's second-order remainder `|A| z_δ²/|M|`, the DC row the remainders of the sinusoid and of
  the factor `1/V` on `V ≥ V* − ρ`; the two other rows are linear. Static evidence on the model.
* Implementation evidence (private, trajectory level): `VSMDC.Model.sublevel_subset_basin` —
  for every symmetric `P` with `P J + Jᵀ P = −1`, lower bound `l |z|² ≤ ⟪z, P z⟫` and `‖P‖ ≤ p`, the
  sublevel set `{⟪x − x*, P (x − x*)⟫ ≤ l (r/2)²}`, `r = min ρ (1/(4 p K(ρ) + 1))`, lies in the
  region of attraction of `(δ*, 0, V*, ζ*)`: the quadratic form in the deviations of the swing
  energy coordinates `(δ − δ*, ω)`, of the DC storage coordinate `V − V*` and of the integrator
  `ζ − ζ*` is a Lyapunov function on `V > 0` with an explicit sublevel set; and
  `VSMDC.Model.exists_lyapunov_basin` — under the quartic Routh conditions (`VSMDC.Model.Stable`)
  such a positive definite `P` exists, so the explicit sublevel sets exist exactly where the
  equilibrium is locally exponentially stable (`VSMDC.mem_den_locallyExponentiallyStable_iff`).

Family and connection conclusions.
No family and no connection conclusion: a region of attraction is a set of initial states outside
the sentence language (private implementation evidence); the remainder bound is static domain
evidence; the local sentences are the connection statements of `VSMDC.family`.

Not proved here: a Lyapunov function of energy type (swing energy + DC storage + integrator
terms with swing–DC cross terms, not quadratic) valid for every Routh-stable parameter, and an
estimate reaching the plane `V = 0`. Without swing–DC cross terms no such function exists:
`VSMDC.Model.not_strictMin_separableEnergy_of_lie_nonpos`
(`theorem/GridTiedConverter/GFM/DCLink/VSMDCEnergy.lean`).
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Set Metric Matrix
open scoped RealInnerProductSpace
open powerlib.Dynamics (State)

/-- A vector of `ℝ⁴` with vanishing first and last coordinates has norm at most
`|v₁| + |v₂|`. -/
@[tmio T, powerlib_foundation] private theorem norm_le_of_zero_three (v : State 4) (h0 : v 0 = 0)
    (h3 : v 3 = 0) : ‖v‖ ≤ |v 1| + |v 2| := by
  have hsq : ‖v‖ ^ 2 = v 1 ^ 2 + v 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, h0, h3]; ring
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
  rw [hsq]
  nlinarith [abs_nonneg (v 1), abs_nonneg (v 2), sq_abs (v 1), sq_abs (v 2),
    mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

namespace VSMDC

/-- The quadratic remainder constant of the closed loop about the selected point on the ball of
radius `ρ < V*`: `K(ρ) = |A|/|M| + (V* |A| + |I_s| + |k|)/(|C| V* (V* − ρ))`. -/
def Model.remainder (m : Model) (ρ : ℝ) : ℝ :=
  |m.p.A| / |m.p.M| +
    (m.p.Vref * |m.p.A| + |m.p.Is| + |m.k|) / (|m.p.C| * m.p.Vref * (m.p.Vref - ρ))

@[tmio M, powerlib_domain] theorem Model.remainder_nonneg (m : Model) (hV : 0 < m.p.Vref)
    {ρ : ℝ} (hρ : ρ < m.p.Vref) : 0 ≤ m.remainder ρ := by
  unfold Model.remainder
  have : 0 < m.p.Vref - ρ := by linarith
  positivity

/-- **The quadratic remainder of the closed loop.** At a balanced point with `V* > 0`, for
`|z| < ρ < V*`: `|f(x* + z) − J z| ≤ K(ρ) |z|²` with `J = Params.jacobian` at the point and
`K(ρ) = Model.remainder ρ`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.norm_field_sub_jacobian_le (m : Model)
    (hb : m.Balanced) (hV : 0 < m.p.Vref) {ρ : ℝ} (hρ : ρ < m.p.Vref) {z : State 4}
    (hz : ‖z‖ < ρ) :
    ‖m.p.field (m.point + z) - Matrix.toEuclideanCLM (𝕜 := ℝ) (m.p.jacobian m.point) z‖ ≤
      m.remainder ρ * ‖z‖ ^ 2 := by
  set v := m.p.field (m.point + z) - Matrix.toEuclideanCLM (𝕜 := ℝ) (m.p.jacobian m.point) z
    with hv
  have hz0 := Dynamics.abs_apply_le_norm z 0
  have hz2 := Dynamics.abs_apply_le_norm z 2
  have hpt0 : m.point 0 = m.δ := rfl
  have hpt1 : m.point 1 = 0 := rfl
  have hpt2 : m.point 2 = m.p.Vref := rfl
  have hpt3 : m.point 3 = m.ζ := rfl
  have hJ : ∀ i, (Matrix.toEuclideanCLM (𝕜 := ℝ) (m.p.jacobian m.point) z) i =
      m.p.jacobian m.point i 0 * z 0 + m.p.jacobian m.point i 1 * z 1 +
        m.p.jacobian m.point i 2 * z 2 + m.p.jacobian m.point i 3 * z 3 := fun i => by
    rw [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
  -- the sinusoid's remainder
  set E := m.p.Pe (m.δ + z 0) - m.p.Pe m.δ - m.k * z 0 with hE
  have hEb : |E| ≤ |m.p.A| * z 0 ^ 2 := by rw [hE]; exact m.p.abs_Pe_add_sub_le m.δ (z 0)
  have hzz : z 0 ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz0 2
  have hz22 : z 2 ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz2 2
  have hz02 : |z 0| * |z 2| ≤ ‖z‖ ^ 2 := by
    rw [sq]; exact mul_le_mul hz0 hz2 (abs_nonneg _) (norm_nonneg _)
  -- the four rows
  have hv0 : v 0 = 0 := by
    simp only [hv, PiLp.sub_apply, hJ, Params.field_apply_zero, PiLp.add_apply, hpt1]
    simp [Params.jacobian]
  have hv3 : v 3 = 0 := by
    simp only [hv, PiLp.sub_apply, hJ, Params.field_apply_three, PiLp.add_apply, hpt2]
    simp [Params.jacobian]
  have hv1 : v 1 = -E / m.p.M := by
    simp only [hv, PiLp.sub_apply, hJ, Params.field_apply_one, PiLp.add_apply, hpt0, hpt1, hpt2,
      hpt3]
    simp only [Params.jacobian, Plant.swingRate, Params.Pref, hE, Model.k, hpt0]
    simp
    have h1 : m.p.Pff = m.p.Pe m.δ - m.p.Ki * m.ζ := by linarith [hb.1]
    rw [h1]
    ring
  have hv2 : v 2 = (-m.p.Vref * E - z 2 * (m.p.Is * z 2 - m.k * z 0)) /
      (m.p.C * (m.p.Vref + z 2) * m.p.Vref) := by
    have hu : 0 < m.p.Vref + z 2 := by
      have := neg_abs_le (z 2); linarith [hz2, hz]
    simp only [hv, PiLp.sub_apply, hJ, Params.field_apply_two, PiLp.add_apply, hpt0, hpt2]
    simp only [Params.jacobian, Plant.nodeRate, Plant.nodeSlope, GFL.DCLink.nodeRate, hE,
      Model.k, hpt0, hpt2]
    simp
    have h2 := hb.2
    simp only [Plant.Psrc] at h2
    have hPs : m.p.Ps = m.p.Pe m.δ - m.p.Is * m.p.Vref := by linarith
    rw [hPs]
    by_cases hC : m.p.C = 0
    · simp [hC]
    · have hu0 : m.p.Vref + z 2 ≠ 0 := hu.ne'
      have hV0 : m.p.Vref ≠ 0 := hV.ne'
      field_simp
      ring
  -- the bounds of the two nonlinear rows
  have hb1 : |v 1| ≤ |m.p.A| / |m.p.M| * ‖z‖ ^ 2 := by
    rw [hv1, abs_div, abs_neg]
    calc |E| / |m.p.M| ≤ |m.p.A| * z 0 ^ 2 / |m.p.M| := by gcongr
      _ ≤ |m.p.A| * ‖z‖ ^ 2 / |m.p.M| := by gcongr
      _ = |m.p.A| / |m.p.M| * ‖z‖ ^ 2 := by ring
  have hb2 : |v 2| ≤ (m.p.Vref * |m.p.A| + |m.p.Is| + |m.k|) /
      (|m.p.C| * m.p.Vref * (m.p.Vref - ρ)) * ‖z‖ ^ 2 := by
    have hlow : m.p.Vref - ρ ≤ m.p.Vref + z 2 := by have := neg_abs_le (z 2); linarith
    have hρ' : 0 < m.p.Vref - ρ := by linarith
    have hnum : |-m.p.Vref * E - z 2 * (m.p.Is * z 2 - m.k * z 0)| ≤
        (m.p.Vref * |m.p.A| + |m.p.Is| + |m.k|) * ‖z‖ ^ 2 := by
      calc |-m.p.Vref * E - z 2 * (m.p.Is * z 2 - m.k * z 0)|
          ≤ m.p.Vref * |E| + (|m.p.Is| * z 2 ^ 2 + |m.k| * (|z 0| * |z 2|)) := by
            have h1 := abs_sub (-m.p.Vref * E) (z 2 * (m.p.Is * z 2 - m.k * z 0))
            have h2 : |-m.p.Vref * E| = m.p.Vref * |E| := by
              rw [abs_mul, abs_neg, abs_of_pos hV]
            have h3 : |z 2 * (m.p.Is * z 2 - m.k * z 0)| ≤
                |m.p.Is| * z 2 ^ 2 + |m.k| * (|z 0| * |z 2|) := by
              rw [abs_mul]
              have h4 := abs_sub (m.p.Is * z 2) (m.k * z 0)
              rw [abs_mul, abs_mul] at h4
              calc |z 2| * |m.p.Is * z 2 - m.k * z 0| ≤
                    |z 2| * (|m.p.Is| * |z 2| + |m.k| * |z 0|) :=
                    mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
                _ = |m.p.Is| * z 2 ^ 2 + |m.k| * (|z 0| * |z 2|) := by
                    rw [← sq_abs (z 2)]; ring
            linarith
        _ ≤ m.p.Vref * (|m.p.A| * ‖z‖ ^ 2) + (|m.p.Is| * ‖z‖ ^ 2 + |m.k| * ‖z‖ ^ 2) := by
            gcongr
            exact hEb.trans (mul_le_mul_of_nonneg_left hzz (abs_nonneg _))
        _ = (m.p.Vref * |m.p.A| + |m.p.Is| + |m.k|) * ‖z‖ ^ 2 := by ring
    rw [hv2, abs_div]
    have hden : |m.p.C| * m.p.Vref * (m.p.Vref - ρ) ≤ |m.p.C * (m.p.Vref + z 2) * m.p.Vref| := by
      rw [abs_mul, abs_mul, abs_of_pos hV, abs_of_pos (hρ'.trans_le hlow)]
      calc |m.p.C| * m.p.Vref * (m.p.Vref - ρ) ≤ |m.p.C| * m.p.Vref * (m.p.Vref + z 2) :=
            mul_le_mul_of_nonneg_left hlow (mul_nonneg (abs_nonneg _) hV.le)
        _ = |m.p.C| * (m.p.Vref + z 2) * m.p.Vref := by ring
    rcases (abs_nonneg m.p.C).eq_or_lt with hC | hC
    · have hC0 : m.p.C = 0 := abs_eq_zero.mp hC.symm
      simp [hC0]
    · have hd0 : 0 < |m.p.C| * m.p.Vref * (m.p.Vref - ρ) := by positivity
      calc |-m.p.Vref * E - z 2 * (m.p.Is * z 2 - m.k * z 0)| /
            |m.p.C * (m.p.Vref + z 2) * m.p.Vref|
          ≤ (m.p.Vref * |m.p.A| + |m.p.Is| + |m.k|) * ‖z‖ ^ 2 /
              (|m.p.C| * m.p.Vref * (m.p.Vref - ρ)) :=
            div_le_div₀ (by positivity) hnum hd0 hden
        _ = _ := by ring
  calc ‖v‖ ≤ |v 1| + |v 2| := norm_le_of_zero_three v hv0 hv3
    _ ≤ |m.p.A| / |m.p.M| * ‖z‖ ^ 2 + (m.p.Vref * |m.p.A| + |m.p.Is| + |m.k|) /
          (|m.p.C| * m.p.Vref * (m.p.Vref - ρ)) * ‖z‖ ^ 2 := add_le_add hb1 hb2
    _ = m.remainder ρ * ‖z‖ ^ 2 := by rw [Model.remainder]; ring

/-- **An explicit region-of-attraction estimate on `V > 0`.** At a balanced point with `V* > 0`
and `0 < ρ < V*`, for every symmetric `P` with `P J + Jᵀ P = −1` (`J = Params.jacobian` at the
point), `l |z|² ≤ ⟪z, P z⟫` (`l > 0`) and `‖P‖ ≤ p`: the sublevel set
`{⟪x − x*, P (x − x*)⟫ ≤ l (r/2)²}`, `r = min ρ (1/(4 p K(ρ) + 1))`, `K(ρ) = Model.remainder ρ`,
lies in the region of attraction of `(δ*, 0, V*, ζ*)`
(`SingularPerturbation.sublevel_subset_regionOfAttraction_of_quadratic`, with the `C¹` field of
`Params.exists_contDiff_eq_field_of_sign` that equals the model on `V ≥ V* − ρ`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem Model.sublevel_subset_basin (m : Model)
    (hb : m.Balanced) (hV : 0 < m.p.Vref) {ρ : ℝ} (hρ : 0 < ρ) (hρV : ρ < m.p.Vref)
    {P : Matrix (Fin 4) (Fin 4) ℝ} (hPs : Pᵀ = P)
    (hL : P * m.p.jacobian m.point + (m.p.jacobian m.point)ᵀ * P = -1) {l p : ℝ} (hl : 0 < l)
    (hlb : ∀ z, l * ‖z‖ ^ 2 ≤ ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) P z⟫)
    (hp : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P‖ ≤ p) :
    {x | ⟪x - m.point, Matrix.toEuclideanCLM (𝕜 := ℝ) P (x - m.point)⟫ ≤
      SingularPerturbation.quadraticBasinLevel l p (m.remainder ρ) ρ} ⊆
      Flow.regionOfAttraction m.p.field m.point := by
  obtain ⟨g, hg, hgf⟩ :=
    m.p.exists_contDiff_eq_field_of_sign (Or.inl rfl) (by linarith : 0 < m.p.Vref - ρ)
  have hfg : ∀ x ∈ ball m.point ρ, m.p.field x = g x := fun x hx => by
    refine (hgf x ?_).symm
    have hx' : ‖x - m.point‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp hx
    have h2 := Dynamics.abs_apply_le_norm (x - m.point) 2
    simp only [PiLp.sub_apply] at h2
    have hpt2 : m.point 2 = m.p.Vref := rfl
    rw [hpt2] at h2
    have := neg_abs_le (x 2 - m.p.Vref)
    linarith
  refine SingularPerturbation.sublevel_subset_regionOfAttraction_of_quadratic hg hρ hfg hPs hL hl
    hlb hp (m.remainder_nonneg hV hρV) fun z hz => ?_
  rw [← hfg (m.point + z) (mem_ball.mpr (by rw [dist_eq_norm, add_sub_cancel_left]; exact hz))]
  exact m.norm_field_sub_jacobian_le hb hV hρV hz

/-- **Lyapunov sublevel sets exist exactly under the Routh conditions.** Under the quartic Routh
conditions (`Model.Stable`) and `V* > 0` there is a positive definite `P` with `P J + Jᵀ P = −1`
and a lower bound `l > 0` of its form such that for every `ρ ∈ (0, V*)` the sublevel set
`{⟪x − x*, P (x − x*)⟫ ≤ l (r/2)²}` of `Model.sublevel_subset_basin` (with `p = ‖P‖`) lies in the
region of attraction. Implementation evidence, as above. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_lyapunov_basin (m : Model)
    (h : m.Stable) (hV : 0 < m.p.Vref) :
    ∃ P : Matrix (Fin 4) (Fin 4) ℝ, P.PosDef ∧
      P * m.p.jacobian m.point + (m.p.jacobian m.point)ᵀ * P = -1 ∧ ∃ l > 0,
        (∀ z, l * ‖z‖ ^ 2 ≤ ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) P z⟫) ∧
        ∀ ρ, 0 < ρ → ρ < m.p.Vref →
          {x | ⟪x - m.point, Matrix.toEuclideanCLM (𝕜 := ℝ) P (x - m.point)⟫ ≤
            SingularPerturbation.quadraticBasinLevel l ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P‖
              (m.remainder ρ) ρ} ⊆ Flow.regionOfAttraction m.p.field m.point := by
  obtain ⟨hV0, hb, h3, h1, h0, hg⟩ := h
  have hx := Model.field_point_of_balanced hV0 hb
  have hH := (Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
    (m.det_characteristicMatrix_quartic hV0 hx)).2 ⟨h3, h1, h0, hg⟩
  obtain ⟨P, hP, hL⟩ := SingularPerturbation.exists_posDef_lyapunov_of_spectrallyStable
    ((Linear.spectrallyStable_iff_isHurwitz _).mpr hH)
  obtain ⟨l, hl, hlb⟩ := SingularPerturbation.exists_lower_bound_of_posDef hP
  exact ⟨P, hP, hL, l, hl, hlb, fun ρ hρ hρV =>
    m.sublevel_subset_basin hb hV hρ hρV hP.isHermitian.isSymm hL hl hlb le_rfl⟩

end VSMDC

end powerlib.GFM.DCLink
