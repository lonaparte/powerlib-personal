import theorem.GridTiedConverter.GFM.QVDroopVirtualHopf
import theorem.GridTiedConverter.GFM.QVDroopHopfCycle
import theorem.Dynamics.HopfCycle

/-! # Q–V droop with a virtual impedance: Hopf cycles along the damping

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`, unchanged (state
  `(δ, Δω, Q_f)`, quasi-static line, powers measured at the terminal behind the virtual impedance,
  export-positive, `E = E₀ − n_q (Q_f − Q_ref)`; excluded as there), read about a selected point
  on the Hopf surface of `theorem/GridTiedConverter/GFM/QVDroopVirtualHopf.lean` (an equilibrium
  with `A > 0`, `C > 0`, `G = 0`; `M, D, ω_q > 0`, `E* ≠ 0`), and unfolded in the damping: the
  parameter `μ` replaces `D` by `D + μ` (`QVDroopVirtual.dampShift`). The equilibrium conditions
  `Δω = 0`, `P_t = P_ref`, `Q_t = Q_f` do not contain `D`, so the translated family
  `QVDroopVirtual.Model.dampFamily` keeps the origin as an equilibrium for every `μ`.
* Level: the transversality coefficient `τ` of the critical pair along the damping, in closed form
  on the whole Hopf surface, with its sign and zero set; and the cycles of the generic Hopf theorem
  `Dynamics.HopfCycle.exists_hopfCycle` for this family wherever `ℓ₁ ≠ 0` and `τ ≠ 0`. Periodic
  orbits are not sentences of `QVDroopVirtual.family`, so the cycles are private evidence; no new
  family, no connection conclusion. Not proved: uniqueness and orbital stability of the cycles;
  cycles at the Bautin set (`hopfNum = 0`) or where `τ = 0`.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3,
the transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`). The damping enters the Jacobian
only through the entry `−D/M`, as without virtual impedance, and the critical pair is the one of
the droop Jacobian on its Hopf surface, so the transversality coefficient is the generic
`QVDroop.paramTrace_dampJac` of `theorem/GridTiedConverter/GFM/QVDroopHopfCycle.lean` (stated for
every datum of the Hopf surface), read at the data of this model; `∂J/∂D` is `VSMLPF.dampJac`
(`theorem/GridTiedConverter/GFM/VSMLPFHopfCycle.lean`). Only the family, its smoothness and the
gain of the physical branch (`gain_of_balance`) are derived here.

Results.
* `QVDroopVirtual.dampShift`, `QVDroopVirtual.Model.dampFamily`; `dampShift_field` (the field
  with the damping `D + μ` is `F(x) + μ (∂J/∂D) x`), `dampShift_jacobian`,
  `Model.dampFamily_zero_param`, `Model.dampFamily_origin`, `Model.fderiv_dampFamily`,
  `Model.hasDerivAt_fderiv_dampFamily` (the Jacobian is affine in `μ` with slope `∂J/∂D`).
* On the model (`Model.hopfQAt`, `Model.hopfPAt`: the critical pair at the data of the point):
  `Model.paramTrace_damping`, `τ = −T/(A² + M² ω²)` with the transversality numerator
  `T = ∂P_t/∂δ + 2 D ω_q K_t + M ω_q² K_t²` (`Model.dampTransNum`); the sign law
  `Model.sign_paramTrace_damping` (`sign τ = −sign T`, so `τ = 0` exactly on `T = 0`);
  `Model.dampTransNum_pos_of_gain_nonneg` (`K_t ≥ 0 ⇒ T = M ω² + ω_q K_t A > 0`: `τ` can vanish
  only where `K_t < 0`) and `Model.dampTransNum_pos_of_physical` (physical range `n_q > 0`,
  `X_g > 0`, `X_v ≥ 0`, `E₀ + n_q Q_ref > 0`, every virtual impedance, `E* > 0`:
  `E* |Z_t|² K_t = gainPoly E* > 0`, so `τ < 0`; the zero set of `τ` lies in `E* < 0`).
* Private evidence `Model.exists_hopfCycle_damping`: for `hopfNum ≠ 0` and `T ≠ 0` there are
  `δ > 0` and `κ` with `sign κ = sign (T · hopfNum)` such that for every `μ` with `|μ| < δ` and
  `κ μ > 0` the model with the damping `D + μ` has a nonconstant periodic orbit around the
  operating point, of period at most `4π/ω`, with `κμ/8 ≤ ‖critπ p z(t)‖² ≤ 8κμ`; on the physical
  branch (`Model.exists_hopfCycle_damping_of_physical`, `E* > 0`, wherever `hopfNum ≠ 0`)
  `sign κ = sign hopfNum`: a supercritical point (`hopfNum < 0`, e.g. `hopfSuper`) has its cycles
  for damping just below the Hopf value, a subcritical one (`hopfNum > 0`, e.g. `hopfSub`) just
  above it. With it the private evidence `Model.contDiff_augField_dampFamily`.
-/

noncomputable section
namespace powerlib.GFM.QVDroopVirtual
open Complex Matrix Polynomial
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)
open powerlib.Dynamics.HopfCycle (augField xpart mpart xin)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold (critπ critι)

/-! ## The damping family -/

/-- The parameters with the damping shifted by `μ`: `D ↦ D + μ`. -/
def dampShift (q : QVDroopVirtual) (μ : ℝ) : QVDroopVirtual :=
  ⟨q.M, q.D + μ, q.ωq, q.nq, q.E0, q.Qref, q.Pref, q.V, q.Rg, q.Xg, q.Rv, q.Xv⟩

/-- The translated field of the model with the damping `D + μ`, as a family in `μ`
(`z = x − (δ*, 0, Q_f*)`; the equilibrium conditions do not contain the damping). -/
def Model.dampFamily (m : Model) (z : State 3) (μ : ℝ) : State 3 :=
  (m.q.dampShift μ).field (z + m.point)

@[tmio M, simp, powerlib_domain] theorem dampShift_zero (q : QVDroopVirtual) :
    q.dampShift 0 = q := by
  cases q; simp [dampShift]

/-- The damping enters the field only through `−D Δω/M`: the field with the damping `D + μ` is
`F(x) + μ (∂J/∂D) x`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dampShift_field (q : QVDroopVirtual) (μ : ℝ) (x : State 3) :
    (q.dampShift μ).field x =
      q.field x + μ • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac q.M) x := by
  have hP : (q.dampShift μ).Pt = q.Pt := rfl
  have hQ : (q.dampShift μ).Qt = q.Qt := rfl
  have hE : (q.dampShift μ).emf = q.emf := rfl
  apply state3_ext
  · simp [toEuclideanCLM_apply3, VSMLPF.dampJac]
  · rw [field_apply_one, hP, hE]
    simp [toEuclideanCLM_apply3, VSMLPF.dampJac, dampShift]
    ring
  · rw [field_apply_two, hQ, hE]
    simp [toEuclideanCLM_apply3, VSMLPF.dampJac, dampShift]

/-- The parameter derivative of the Jacobian: `∂J/∂D = −(1/M) e₁ e₁ᵀ` (`VSMLPF.dampJac`). -/
@[tmio M, powerlib_domain] theorem dampShift_jacobian (q : QVDroopVirtual) (μ δ E : ℝ) :
    (q.dampShift μ).jacobian δ E = q.jacobian δ E + μ • VSMLPF.dampJac q.M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobian, dampShift, VSMLPF.dampJac, Ptδ, PtE, Qtδ, QtE, ztsq]
  ring

@[tmio M, powerlib_domain] theorem Model.dampFamily_zero_param (m : Model) :
    (fun z => m.dampFamily z 0) = m.field := by
  funext z; simp [Model.dampFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.dampFamily_origin (m : Model)
    (heq : m.q.field m.point = 0) (μ : ℝ) : m.dampFamily 0 μ = 0 := by
  have hB : Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M) m.point = 0 := by
    apply state3_ext <;> simp [toEuclideanCLM_apply3, VSMLPF.dampJac, Model.point]
  rw [Model.dampFamily, zero_add, dampShift_field, heq, hB, smul_zero, add_zero]

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_dampFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.dampFamily) := by
  have e : augField m.dampFamily = fun w => xin (m.q.field (xpart w + m.point) +
      mpart w • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)
        (xpart w + m.point)) := by
    funext w
    simp only [augField, Model.dampFamily, dampShift_field]
  rw [e]
  have hx : ContDiff ℝ k fun w : State (3 + 1) => xpart w + m.point :=
    xpart.contDiff.add contDiff_const
  exact xin.contDiff.comp ((m.q.contDiff_field.comp hx).add (mpart.contDiff.smul
    ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).contDiff.comp hx)))

@[tmio M, powerlib_domain] theorem Model.fderiv_dampFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.dampFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jacobian +
        μ • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M) := by
  have hE : (m.q.dampShift μ).emf = m.q.emf := rfl
  rw [show (fun z => m.dampFamily z μ) = fun z => (m.q.dampShift μ).field (z + m.point) from rfl,
    fderiv_comp_add_right, zero_add, QVDroopVirtual.fderiv_field, dampShift_jacobian, hE]
  simp [Model.point, Model.jacobian, map_add, map_smul]

/-- **Transversality data**: `μ ↦ D_z F(0, μ)` is affine with slope `toEuclideanCLM (∂J/∂D)`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_dampFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.dampFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)) 0 := by
  simp only [Model.fderiv_dampFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M))).const_add
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jacobian)

/-! ## The transversality coefficient on the Hopf surface -/

/-- The critical right eigenvector `QVDroop.hopfQ` at the data of the selected point
(`ω = hopfFreq`, `k = K_t`, `c = Q_tδ`). -/
def Model.hopfQAt (m : Model) : Fin 3 → ℂ :=
  QVDroop.hopfQ m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))

/-- The normalised left eigenvector `QVDroop.hopfP` at the data of the selected point. -/
def Model.hopfPAt (m : Model) : Fin 3 → ℂ :=
  QVDroop.hopfP m.q.M m.q.D m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf))
    (m.q.Qtδ m.δ (m.q.emf m.Qf))

/-- The transversality numerator `T = P_tδ + 2 D ω_q K_t + M ω_q² K_t²` at the selected point. -/
def Model.dampTransNum (m : Model) : ℝ :=
  m.q.Ptδ m.δ (m.q.emf m.Qf) + 2 * m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) +
    m.q.M * m.q.ωq ^ 2 * m.q.gain m.δ (m.q.emf m.Qf) ^ 2

/-- **The transversality coefficient of the model.** At a Hopf point (`A > 0`, `C > 0`, `G = 0`)
with `M, D, ω_q > 0`: `τ = −T/(A² + M² ω²)`, `T = P_tδ + 2 D ω_q K_t + M ω_q² K_t²`,
`ω = hopfFreq` (`QVDroop.paramTrace_dampJac` at the data of the point). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_damping (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (h : m.IsHopf) :
    Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
          (critι m.hopfQAt))) =
      -m.dampTransNum /
        (m.q.routhTrace m.δ (m.q.emf m.Qf) ^ 2 + m.q.M ^ 2 * m.hopfFreq ^ 2) := by
  obtain ⟨hw, ha, -, -⟩ := m.hopf_relations hM hD hω h
  rw [Model.hopfPAt, Model.hopfQAt, QVDroop.paramTrace_dampJac hM.ne' hw.ne', Model.dampTransNum,
    ha]
  simp only [QVDroop.hopfQ1, QVDroop.hopfL, QVDroop.hopfA, routhTrace]
  congr 1 <;> ring

/-- **The sign law of the transversality coefficient.** At a Hopf point with `M, D, ω_q > 0`,
`sign τ = −sign T`; in particular `τ = 0` exactly on `T = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_damping (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (h : m.IsHopf) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
          (critι m.hopfQAt)))) = -SignType.sign m.dampTransNum := by
  rw [m.paramTrace_damping hM hD hω h]
  have hA := h.2.1
  have hd : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ^ 2 + m.q.M ^ 2 * m.hopfFreq ^ 2 := by
    positivity
  rcases lt_trichotomy m.dampTransNum 0 with h0 | h0 | h0
  · rw [sign_neg h0, sign_pos (div_pos (neg_pos.mpr h0) hd)]
    rfl
  · rw [h0, neg_zero, zero_div, sign_zero, neg_zero]
  · rw [sign_pos h0, sign_neg (div_neg_of_neg_of_pos (neg_neg_of_pos h0) hd)]

/-- **`T > 0` for a nonnegative voltage-loop gain.** At a Hopf point with `M, D, ω_q > 0` and
`K_t ≥ 0`, `T = M ω² + ω_q K_t A > 0`, so `τ < 0`; `τ` can vanish only where `K_t < 0`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.dampTransNum_pos_of_gain_nonneg (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (h : m.IsHopf)
    (hK : 0 ≤ m.q.gain m.δ (m.q.emf m.Qf)) : 0 < m.dampTransNum := by
  obtain ⟨hw, ha, -, -⟩ := m.hopf_relations hM hD hω h
  have hA := h.2.1
  have e : m.dampTransNum = m.q.M * m.hopfFreq ^ 2 +
      m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) * m.q.routhTrace m.δ (m.q.emf m.Qf) := by
    rw [Model.dampTransNum, ha, QVDroop.hopfA, routhTrace]; ring
  rw [e]
  have h1 : 0 < m.q.M * m.hopfFreq ^ 2 := by positivity
  have h2 := mul_nonneg (mul_nonneg hω.le hK) hA.le
  linarith

/-- **The physical branch.** In the physical range (`M, D, ω_q, n_q, X_g > 0`, `X_v ≥ 0`,
`E₀ + n_q Q_ref > 0`, every `R_g`, `R_v`) a Hopf point with a positive EMF has
`K_t = gainPoly E*/(E* |Z_t|²) > 0` (`gain_of_balance`), hence `T > 0` and `τ < 0`: more damping
moves the critical eigenvalues to the left, and the zero set of `τ` lies in `E* < 0`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.dampTransNum_pos_of_physical (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hXg : 0 < m.q.Xg)
    (hXv : 0 ≤ m.q.Xv) (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (h : m.IsHopf)
    (hE : 0 < m.q.emf m.Qf) : 0 < m.dampTransNum := by
  refine m.dampTransNum_pos_of_gain_nonneg hM hD hω h ?_
  have hZ := m.q.ztsq_pos hXg hXv
  have hb := m.q.balance_of_field_eq_zero hM.ne' hω.ne' hnq.ne' h.1
  simp only [Model.point, mk3_zero, mk3_two] at hb
  rw [m.q.gain_of_balance hZ.ne' hnq.ne' hE.ne' hb.2]
  exact (div_pos (by positivity) (mul_pos hE hZ)).le

/-! ## The Hopf cycles -/

/-- **Hopf cycles along the damping.** At a Hopf point (`A > 0`, `C > 0`, `G = 0`) with
`M, D, ω_q > 0`, `E* ≠ 0`, `hopfNum ≠ 0` (`ℓ₁ ≠ 0`, `Model.sign_firstLyapunov_hopf`) and `T ≠ 0`
(`τ ≠ 0`, `Model.sign_paramTrace_damping`), there are `δ > 0` and `κ` with
`sign κ = sign (T · hopfNum)` such that for every `μ` with `|μ| < δ` and `κ μ > 0` the translated
model field with the damping `D + μ` has a nonconstant periodic orbit around the operating point,
of period at most `4π/ω`, whose critical coordinates satisfy `κμ/8 ≤ ‖critπ p z(t)‖² ≤ 8κμ`
(`HopfCycle.exists_hopfCycle`, `κ = −τ/(ω ℓ₁)`). Private evidence: periodic orbits are not
sentences of the family. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_damping (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hE : m.q.emf m.Qf ≠ 0)
    (h : m.IsHopf) (hN : m.hopfNumAt ≠ 0) (hT : m.dampTransNum ≠ 0) :
    ∃ δ > 0, ∃ κ : ℝ, SignType.sign κ = SignType.sign (m.dampTransNum * m.hopfNumAt) ∧
      ∀ μ, |μ| < δ → 0 < κ * μ →
        ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / m.hopfFreq ∧
          (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
          (∃ t, z t ≠ z 0) ∧
          ∀ t, κ * μ / 8 ≤ ‖critπ m.hopfPAt (z t)‖ ^ 2 ∧
            ‖critπ m.hopfPAt (z t)‖ ^ 2 ≤ 8 * (κ * μ) := by
  obtain ⟨hcp0, -, hchar0⟩ := m.hopf_data hM hD hω hE h
  have hw : 0 < m.hopfFreq := (m.hopf_relations hM hD hω h).1
  have hz := m.dampFamily_zero_param
  have hcp : IsCriticalPair (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt := by
    rw [hz]; exact hcp0
  have hchar : (jacobianC (fun z => m.dampFamily z 0) 0).charpoly =
      (Polynomial.X ^ 2 + Polynomial.C ((m.hopfFreq : ℂ) ^ 2)) *
        (Polynomial.X +
          Polynomial.C (((m.q.routhTrace m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ)) := by
    rw [hz]; exact hchar0
  have hls : SignType.sign (firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt
      m.hopfPAt) = SignType.sign m.hopfNumAt := by
    rw [hz]; exact m.sign_firstLyapunov_hopf hM hD hω hE h hcp0
  have hl : firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at hls
    exact hN (sign_eq_zero_iff.mp hls.symm)
  have hτs := m.sign_paramTrace_damping hM hD hω h
  have hτ : Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
        (critι m.hopfQAt))) ≠ 0 := by
    rw [m.paramTrace_damping hM hD hω h]
    have hA := h.2.1
    have hd : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ^ 2 + m.q.M ^ 2 * m.hopfFreq ^ 2 := by
      positivity
    exact div_ne_zero (neg_ne_zero.mpr hT) hd.ne'
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle m.contDiff_augField_dampFamily
    (m.contDiff_augField_dampFamily (k := ⊤)).contDiffAt.analyticAt (m.dampFamily_origin h.1)
    hcp hchar (re_neg_of_eval_X_add_C (div_pos h.2.1 hM)) m.hasDerivAt_fderiv_dampFamily hτ hl
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
        (critι m.hopfQAt))) with hτdef
  set ℓ := firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt
    with hℓdef
  have hc : 0 < m.hopfFreq * ℓ ^ 2 := mul_pos hw (sq_pos_of_ne_zero hl)
  have key : -τ / (m.hopfFreq * ℓ) * (m.hopfFreq * ℓ ^ 2) = -(τ * ℓ) := by
    field_simp
  refine ⟨δ, hδ, -τ / (m.hopfFreq * ℓ), ?_, fun μ hμ hκμ => ?_⟩
  · calc SignType.sign (-τ / (m.hopfFreq * ℓ))
        = SignType.sign (-τ / (m.hopfFreq * ℓ)) * SignType.sign (m.hopfFreq * ℓ ^ 2) := by
          rw [sign_pos hc, mul_one]
      _ = SignType.sign (-τ / (m.hopfFreq * ℓ) * (m.hopfFreq * ℓ ^ 2)) := (sign_mul _ _).symm
      _ = -(SignType.sign τ * SignType.sign ℓ) := by rw [key, Left.sign_neg, sign_mul]
      _ = SignType.sign m.dampTransNum * SignType.sign m.hopfNumAt := by
          rw [hτs, hls, neg_mul, neg_neg]
      _ = SignType.sign (m.dampTransNum * m.hopfNumAt) := (sign_mul _ _).symm
  · have e : μ * τ * ℓ = -((-τ / (m.hopfFreq * ℓ) * μ) * (m.hopfFreq * ℓ ^ 2)) := by
      linear_combination μ * key
    have hs : μ * τ * ℓ < 0 := by
      rw [e]; exact neg_neg_of_pos (mul_pos hκμ hc)
    obtain ⟨z, T, hT0, hTle, hz', hzT, hznc, hamp⟩ := hcyc μ hμ hs
    refine ⟨z, T, hT0, hTle, hz', hzT, hznc, fun t => ?_⟩
    have hν : -(μ * τ) / (m.hopfFreq * ℓ) = -τ / (m.hopfFreq * ℓ) * μ := by ring
    have ht := hamp t
    rw [hν] at ht
    exact ht

/-- **Hopf cycles on the physical branch.** In the physical range (`M, D, ω_q, n_q, X_g > 0`,
`X_v ≥ 0`, `E₀ + n_q Q_ref > 0`) at a Hopf point with `E* > 0` and `hopfNum ≠ 0` (`T > 0` there,
`Model.dampTransNum_pos_of_physical`) the cycles of `Model.exists_hopfCycle_damping` exist with
`sign κ = sign hopfNum`: for damping just below the Hopf value at a supercritical point, just
above it at a subcritical one. Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_damping_of_physical
    (m : Model) (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq)
    (hXg : 0 < m.q.Xg) (hXv : 0 ≤ m.q.Xv) (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (h : m.IsHopf)
    (hE : 0 < m.q.emf m.Qf) (hN : m.hopfNumAt ≠ 0) :
    ∃ δ > 0, ∃ κ : ℝ, SignType.sign κ = SignType.sign m.hopfNumAt ∧
      ∀ μ, |μ| < δ → 0 < κ * μ →
        ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / m.hopfFreq ∧
          (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
          (∃ t, z t ≠ z 0) ∧
          ∀ t, κ * μ / 8 ≤ ‖critπ m.hopfPAt (z t)‖ ^ 2 ∧
            ‖critπ m.hopfPAt (z t)‖ ^ 2 ≤ 8 * (κ * μ) := by
  have hT := m.dampTransNum_pos_of_physical hM hD hω hnq hXg hXv hc h hE
  obtain ⟨δ, hδ, κ, hs, hcyc⟩ := m.exists_hopfCycle_damping hM hD hω hE.ne' h hN hT.ne'
  refine ⟨δ, hδ, κ, ?_, hcyc⟩
  rw [hs, sign_mul, sign_pos hT, one_mul]

end QVDroopVirtual

end powerlib.GFM
