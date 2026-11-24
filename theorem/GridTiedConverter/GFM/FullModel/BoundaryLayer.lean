import theorem.GridTiedConverter.GFM.FullModel.TimeScale
import theorem.SingularPerturbation.Converse
import theorem.Criteria.ComplexQuadratic
import theorem.Criteria.RouthComplex
import theorem.Linear.Synthesis

/-! # The 13-state grid-forming converter: the boundary layer and the controller gains

Model boundary.
The fast block of the 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean`:
the ten fast rows (filter current `i`, capacitor voltage `v_c`, line current `i_g`, current-loop
integrator `ξ`, voltage-loop integrator `ζ`, dq components, system frame for the plant,
controller frame for the integrators, currents out of the converter positive) linearized in the
fast states, `fastBlock δ`, the real form of the complex `5 × 5` matrix `fastMatrix δ`
(`theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`). Continuous time, constant matrices;
the boundary layer of the time-scale transfer of
`theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean`. Parameters are free reals; the
"ideal design" is full line-current feed-forward and capacitor-current decoupling
(`k_ff = k_dv = 1`) without virtual impedance (`Z_v = 0`), with resistive damping `R_f, R_g > 0`;
the exact block conditions and the sufficient condition need only `k_ff = 1`, `Z_v = 0`.
The current-loop time scale `μ` (`Params.currentScaled μ`): `L_f ↦ μ L_f`, `K_ic ↦ K_ic/μ`, so
the current-loop characteristic polynomial `L_f s² + (K_pc + R_f) s + K_ic` has its roots
multiplied by `μ⁻¹` and the decoupling `ω₀L_f` follows `L_f`; all other parameters unchanged
(the quasi-steady set, the powers and the reduced model do not change).
Excluded: a closed form of the characteristic polynomial of the fast block for symbolic gains
(its Routh table decides it at fixed gains:
`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayerRouth.lean`), and everything excluded by
the full-order model.

Source: GFM counterpart study, full-order model note (t5: "fast block Hurwitz only numerically";
"UNPROVED: stability of δ+ in full model"); the cascaded control of S. D'Arco, J. A. Suul and
O. B. Fosso, Electr. Power Syst. Res. 122 (2015) 180–197 (inner current loop faster than the
voltage loop); Kokotović–Khalil–O'Reilly, *Singular Perturbation Methods in Control* (1986),
Ch. 2 (linear two-time-scale stability); the real form of a complex matrix
(`theorem/SingularPerturbation/Realification.lean`). The witness was found by solving the
characteristic equation (affine in `K_pv, K_iv`) at the target root `1 + 3j` and is certified
here exactly.

Results.
* `Params.fastBlock_eq_realify`, `Params.angleScale`, `Params.angleScale_mul`,
  `Params.fastMatrix_eq_conj`: the fast matrix at the angle `δ` is the one at `0` conjugated by
  `diag(1, 1, 1, e^{jδ}, e^{jδ})`;
  `Params.spectrallyStable_fastBlock_iff`: spectral stability of the fast block does not depend on
  the angle.
* Positive gains do not suffice: `blWitness` (ideal design with resistive damping: `ω₀ = 1`,
  `L_f = C_f = 1`, `L_g = R_f = R_g = 1/10`, `K_pc = 1`, `K_ic = 2`, `K_pv = 28/15`, `K_iv = 24`)
  has the fast-matrix eigenvalue `1 + 3j` (`blWitness_fastMatrix_mulVec`, eigenvector
  `blWitnessVec`), so `blWitness_not_spectrallyStable`: its fast block is not spectrally stable
  at any angle, and `not_forall_spectrallyStable_fastBlock`: "all gains positive (with full
  decoupling, feed-forward and resistive damping) ⇒ fast block Hurwitz" is false.
* The current-loop / voltage-level split `loopSplit` of the five fast phasors:
  `Params.currentMatrix` (`(i, ξ)` at rest of the voltage level),
  `Params.currentGain` (the quasi-steady current loop `i = i*`, `ξ = R_f i*/K_ic`) and
  `Params.voltageMatrix` (the voltage level with an ideal current loop, the Schur complement):
  `Params.fastMatrix_blocks`. Exactly: `Params.spectrallyStable_currentMatrix_iff`, the current
  loop is stable iff `(K_pc + R_f)/L_f > 0` and `K_ic/L_f > 0`;
  `Params.spectrallyStable_voltageMatrix_iff` (`k_ff = 1`, `Z_v = 0`, any `k_dv`), the voltage
  level is stable iff `K_pv/C_f, K_iv/C_f, R_g/L_g > 0` (the decoupling gain only rotates the
  voltage PI loop: `Criteria.complexQuadratic_realConst_roots_re_neg_iff`);
  `Params.spectrallyStable_voltageMatrix_of_kff_le_one` (`k_ff ≤ 1`, `Z_v = 0`, any `k_dv`): the
  voltage level is stable for positive `C_f, L_g, R_g, K_pv, K_iv` (the real part of the scalar
  eigenvalue equation `s + (K_pv − (k_dv − 1) jω₀C_f)/C_f + κ/(s + Z_g/L_g) + (K_iv/C_f)/s = 0`,
  `κ = (1 − k_ff)/(C_f L_g) ≥ 0`, is positive on `Re s ≥ 0`). Beyond it positive gains do not
  suffice: `kffWitness` (`k_ff = 2`, eigenvalue `1 + j`, `kffWitness_voltageMatrix_mulVec`,
  `not_forall_spectrallyStable_voltageMatrix_of_kff`) and `rvWitness` (virtual resistance
  `R_v = 1`, eigenvalue `1 + 3j`, `rvWitness_voltageMatrix_mulVec`,
  `not_forall_spectrallyStable_voltageMatrix_of_virtualResistance`), whose boundary layers are
  unstable for every fast current loop (`kffWitness_eventually_not_spectrallyStable`,
  `rvWitness_eventually_not_spectrallyStable`).
* **The voltage level, exactly, for every `k_ff`, `k_dv`, `Z_v`** (`C_f, L_g ≠ 0`):
  `Params.det_voltageMatrix`, its characteristic polynomial is the complex cubic
  `s³ + a₂ s² + a₁ s + a₀ = (s + Z_g/L_g)(s² + α_v s + K_iv/C_f) +
  ((1 − k_ff + K_pv Z_v) s + K_iv Z_v)/(C_f L_g)` (`Params.voltageA2`, `Params.voltageA1`,
  `Params.voltageA0`; real and imaginary parts in the parameters: `Params.voltageA_parts`);
  `Params.spectrallyStable_voltageMatrix_iff_cubic`, and
  `Params.spectrallyStable_voltageMatrix_iff_routh`: the voltage level is stable iff
  `Re a₂ > 0`, `Re a₂ (Re a₁ Re a₂ + Im a₁ Im a₂ − Re a₀) > (Im a₁)²` and
  `Criteria.complexCubicDet a₂ a₁ a₀ > 0` (Routh–Hurwitz for the complex cubic,
  `Criteria.complexCubic_roots_re_neg_iff`); such a level has `K_iv ≠ 0`, `Z_t ≠ 0`
  (`Params.kiv_ne_zero_and_zt_ne_zero_of_spectrallyStable`).
* `Params.currentScaled_imp` (the nominal-frequency quantities do not change),
  `Params.xiScale`, `Params.xiScale_mul`, `Params.fastMatrix_currentScaled`: the fast matrix of
  `currentScaled μ` is similar to the fast matrix with its current-loop rows multiplied by `μ⁻¹`
  (`SingularPerturbation.phasorScale`), hence
  `Params.spectrallyStable_fastBlock_currentScaled_iff`.
* **Sufficient condition** `Params.exists_muStar_spectrallyStable_fastBlock`: with a stable current
  loop and a stable voltage level (from the gains and the three voltage-level inequalities, any
  `k_ff`, `Z_v`: `Params.exists_muStar_spectrallyStable_fastBlock_of_routh`; in particular with
  `k_ff ≤ 1`, `Z_v = 0`, all gains positive and `R_g > 0`:
  `Params.exists_muStar_spectrallyStable_fastBlock_of_gains`), there is `μ* > 0` such
  that the fast block of `currentScaled μ` is spectrally stable for every `μ ∈ (0, μ*)` and every
  angle (`SingularPerturbation.exists_epsStar_spectrallyStable_realify`);
  `Params.spectrallyStable_fastBlock_currentScaled_of_lt`: explicitly for every
  `μ ∈ (0, Params.muStar P₀ P₂)` (Kokotović's bound for Lyapunov matrices `P₀` of the voltage level
  and `P₂` of the current loop).
* **Necessity for a fast current loop**:
  `Params.eventually_not_spectrallyStable_fastBlock_of_current` and
  `Params.eventually_not_spectrallyStable_fastBlock_of_voltage` (an eigenvalue with positive real
  part of the current loop, resp. of the voltage level, makes the boundary layer of
  `currentScaled μ` unstable for every small `μ > 0`;
  `theorem/SingularPerturbation/Converse.lean`), with
  `Params.fastMatrix_toBlocks₁₁`, `Params.isUnit_det_fastMatrix`; the eigenvalues from the gains
  `Params.exists_currentMatrix_eigen_re_pos`, `Params.exists_voltageMatrix_eigen_re_pos` (through
  `Params.voltageMatrix_mulVec_line`, `Params.voltageMatrix_eigen_of_root`); and
  `Params.eventually_not_spectrallyStable_fastBlock_of_gains`: with `k_ff = 1`, `Z_v = 0`, a
  strictly violated block condition makes the boundary layer unstable for every small `μ`. So for
  a fast current loop the boundary layer is decided by the block conditions, up to boundary cases.
  Closed-form `μ*`: `theorem/GridTiedConverter/GFM/FullModel/ExplicitScales.lean`.
* At the witness: `blWitness_currentScaled_spectrallyStable`, the boundary layer of
  `blWitness.currentScaled (1/10)` is spectrally stable at every angle (its real fast block is the
  rational `blFastA10` built from `blFastRe`, `blFastIm`, `blFast_fastBlock_reindex`, with the
  kernel-checked rational Lyapunov certificate `blFastCertificate` of
  `theorem/Linear/Synthesis.lean`): a ten times faster current loop turns the unstable boundary
  layer of `blWitness` into a stable one.

Family and connection conclusions.
* `Model.currentScaled`: the full model at the parameters `currentScaled μ`, same point.
* `exists_muStar_epsStar_mem_den_LES_of_routh` (connection, `FullModel.family`): for every
  `k_ff`, `k_dv`, `Z_v`, with a stable current loop and the three Routh–Hurwitz inequalities of
  the voltage level, at a balanced quasi-steady point with a Hurwitz reduced Jacobian, for every
  fast enough current loop (`μ < μ*`) the time-scaled model `(currentScaled μ).timeScaled ε` is
  locally exponentially stable for every `ε ∈ (0, ε*(μ))` — the time-scale transfer of
  `exists_epsStar_mem_den_LES` with the boundary-layer hypothesis replaced by explicit
  inequalities; `exists_muStar_epsStar_mem_den_LES` (connection): its case `k_ff ≤ 1`, `Z_v = 0`,
  positive gains and `R_g > 0`;
  `exists_muStar_epsStar_mem_den_LES_of_qvDroop` (connection, reading `QVDroop.family`): the same
  from a locally exponentially stable reduced Q–V droop model (scaffold
  `theorem/GridTiedConverter/GFM/FullModel/FullModelTimeScale.agda`).
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex Matrix Filter Topology
open powerlib.Dynamics (State)
open powerlib.SingularPerturbation (realify)

namespace Params

variable (p : Params)

/-! ### The angle drops out of the spectrum -/

@[tmio M, powerlib_domain] theorem fastBlock_eq_realify (δ : ℝ) :
    p.fastBlock δ = realify (p.fastMatrix δ) := rfl

/-- `diag(1, 1, 1, e^{jδ}, e^{jδ})`: the integrators rotated by the angle. -/
def angleScale (δ : ℝ) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal ![1, 1, 1, ej δ, ej δ]

@[tmio M, powerlib_domain] theorem angleScale_mul (δ : ℝ) :
    angleScale δ * angleScale (-δ) = 1 := by
  have he : ej δ * ej (-δ) = 1 := by simp [ej, ← Complex.exp_add]
  rw [angleScale, angleScale, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  fin_cases a <;> simp [he]

/-- The fast matrix at the angle `δ` is the fast matrix at `0` conjugated by `angleScale`. -/
@[tmio M, powerlib_domain] theorem fastMatrix_eq_conj (δ : ℝ) :
    p.fastMatrix δ = angleScale (-δ) * p.fastMatrix 0 * angleScale δ := by
  have he : ej (-δ) * ej δ = 1 := by simp [ej, ← Complex.exp_add]
  have h0 : ej 0 = 1 := by simp [ej]
  ext a b
  rw [angleScale, angleScale, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [fastMatrix, h0] <;>
    first | ring1 | linear_combination (-(p.Kiv : ℂ)) * he

/-- **The spectrum of the fast block does not depend on the angle.** -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff (δ : ℝ) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔ Linear.SpectrallyStable (p.fastBlock 0) := by
  rw [fastBlock_eq_realify, fastMatrix_eq_conj, SingularPerturbation.realify_mul,
    SingularPerturbation.realify_mul, fastBlock_eq_realify]
  refine Linear.spectrallyStable_conj ?_ _
  rw [← SingularPerturbation.realify_mul, angleScale_mul, SingularPerturbation.realify_one]

end Params

/-! ### Positive gains do not suffice -/

/-- The witness: ideal design (`k_ff = k_dv = 1`, `Z_v = 0`) with resistive damping,
`ω₀ = 1`, `L_f = C_f = 1`, `L_g = R_f = R_g = 1/10`, `K_pc = 1`, `K_ic = 2`, `K_pv = 28/15`,
`K_iv = 24`; the slow parameters are irrelevant to the fast block. -/
def blWitness : Params where
  ω0 := 1
  Lf := 1
  Rf := 1 / 10
  Cf := 1
  Lg := 1 / 10
  Rg := 1 / 10
  V := 1
  Rv := 0
  Xv := 0
  Kpv := 28 / 15
  Kiv := 24
  Kpc := 1
  Kic := 2
  kff := 1
  kdv := 1
  M := 1
  D := 1
  Pref := 0
  E0 := 1
  nq := 0
  Qref := 0
  ωq := 1

/-- An eigenvector of the witness's fast matrix at `δ = 0`. -/
def blWitnessVec : Fin 5 → ℂ := ![60, 15 - 15 * I, -15 - 45 * I, 41 + 19 * I, 3 + 6 * I]

/-- The witness's fast matrix has the eigenvalue `1 + 3j` (positive real part). -/
@[tmio M, powerlib_domain] theorem blWitness_fastMatrix_mulVec :
    blWitness.fastMatrix 0 *ᵥ blWitnessVec = (1 + 3 * I) • blWitnessVec := by
  have h0 : ej 0 = 1 := by simp [ej]
  funext a
  fin_cases a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, Params.fastMatrix, blWitnessVec, h0,
      Params.Bf, Params.Zg_eq, Params.Zv, blWitness] <;>
    apply Complex.ext <;> simp <;> norm_num

/-- **The witness's boundary layer is unstable**, at every angle. -/
@[tmio M, powerlib_domain] theorem blWitness_not_spectrallyStable (δ : ℝ) :
    ¬ Linear.SpectrallyStable (blWitness.fastBlock δ) := by
  rw [blWitness.spectrallyStable_fastBlock_iff, Params.fastBlock_eq_realify]
  refine SingularPerturbation.not_spectrallyStable_realify (w := blWitnessVec) ?_
    blWitness_fastMatrix_mulVec (by simp)
  intro h
  have := congrFun h 0
  simp [blWitnessVec] at this

/-- **Positive gains do not make the boundary layer stable.** Even in the ideal design (full
feed-forward and decoupling, no virtual impedance) with positive frequency, filter, line,
resistances and controller gains, the fast block need not be spectrally stable. -/
@[tmio M, powerlib_domain] theorem not_forall_spectrallyStable_fastBlock :
    ¬ ∀ p : Params, 0 < p.ω0 → 0 < p.Lf → 0 < p.Rf → 0 < p.Cf → 0 < p.Lg → 0 < p.Rg →
      0 < p.Kpv → 0 < p.Kiv → 0 < p.Kpc → 0 < p.Kic → p.kff = 1 → p.kdv = 1 → p.Zv = 0 →
      ∀ δ, Linear.SpectrallyStable (p.fastBlock δ) := by
  intro h
  refine blWitness_not_spectrallyStable 0
    (h blWitness ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl ?_ 0) <;> norm_num [blWitness, Params.Zv]

/-! ### Current loop and voltage level -/

/-- The splitting of the five fast phasors `(i, v_c, i_g, ξ, ζ)` into the current loop `(i, ξ)`
(fast) and the voltage level `(v_c, i_g, ζ)` (slow). -/
def loopSplit : Fin 5 ≃ Fin 2 ⊕ Fin 3 where
  toFun := ![.inl 0, .inr 0, .inr 1, .inl 1, .inr 2]
  invFun := Sum.elim ![0, 3] ![1, 2, 4]
  left_inv := by decide
  right_inv := by decide

namespace Params

variable (p : Params)

/-- The current loop `(i, ξ)` with the voltage level at rest (angle `0`):
`L_f i̇ = −(K_pc + R_f) i + K_ic ξ`, `ξ̇ = −i`. -/
def currentMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![-(p.Kpc + p.Rf) / p.Lf, p.Kic / p.Lf; -1, 0]

/-- The quasi-steady current loop over the voltage level: `i = i*`, `ξ = R_f i*/K_ic` with
`i* = a_v v_c + a_g i_g + K_iv ζ`, `a_v = −K_pv + k_dv jω₀C_f`, `a_g = k_ff − K_pv Z_v`. -/
def currentGain : Matrix (Fin 2) (Fin 3) ℂ :=
  !![-p.Kpv + p.kdv * (p.Bf * I), p.kff - p.Kpv * p.Zv, p.Kiv;
    p.Rf * (-p.Kpv + p.kdv * (p.Bf * I)) / p.Kic, p.Rf * (p.kff - p.Kpv * p.Zv) / p.Kic,
      p.Rf * p.Kiv / p.Kic]

/-- The voltage level `(v_c, i_g, ζ)` with an ideal current loop (`i = i*`): the Schur complement
of the current loop in the fast matrix at angle `0`. -/
def voltageMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-p.Kpv + p.kdv * (p.Bf * I) - p.Bf * I) / p.Cf, (p.kff - p.Kpv * p.Zv - 1) / p.Cf,
      p.Kiv / p.Cf;
    1 / p.Lg, -p.Zg / p.Lg, 0;
    -1, -p.Zv, 0]

/-- The blocks of the fast matrix (angle `0`) along `loopSplit`: the current loop
`currentMatrix`, and the quasi-steady gain `currentGain` solving `A H + B = 0` with
`C H + D = voltageMatrix`. -/
@[tmio M, powerlib_domain] theorem fastMatrix_blocks (hKic : p.Kic ≠ 0) :
    ((p.fastMatrix 0).reindex loopSplit loopSplit).toBlocks₁₁ = p.currentMatrix ∧
      p.currentMatrix * p.currentGain +
        ((p.fastMatrix 0).reindex loopSplit loopSplit).toBlocks₁₂ = 0 ∧
      ((p.fastMatrix 0).reindex loopSplit loopSplit).toBlocks₂₁ * p.currentGain +
        ((p.fastMatrix 0).reindex loopSplit loopSplit).toBlocks₂₂ = p.voltageMatrix := by
  have h0 : ej 0 = 1 := by simp [ej]
  have hK : (p.Kic : ℂ) ≠ 0 := by exact_mod_cast hKic
  refine ⟨?_, ?_, ?_⟩ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, loopSplit,
      fastMatrix, currentMatrix, currentGain, voltageMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      h0] <;>
    first | ring1 | (field_simp; ring1)

/-- **The current loop, exactly.** Its real form is spectrally stable iff
`(K_pc + R_f)/L_f > 0` and `K_ic/L_f > 0`: its eigenvalues are the roots of
`s² + (K_pc + R_f)/L_f · s + K_ic/L_f` (`Criteria.quadratic_roots_re_neg_iff`). -/
@[tmio M, powerlib_domain] theorem spectrallyStable_currentMatrix_iff :
    Linear.SpectrallyStable (realify p.currentMatrix) ↔
      0 < (p.Kpc + p.Rf) / p.Lf ∧ 0 < p.Kic / p.Lf := by
  rw [SingularPerturbation.spectrallyStable_realify_iff, ← Criteria.quadratic_roots_re_neg_iff]
  constructor
  · intro h μ hμ
    refine h μ ![-μ, 1] (fun h0 => by simpa using congrFun h0 1) ?_
    push_cast at hμ
    funext k
    fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, currentMatrix]
    linear_combination hμ
  · intro hq μ w hw heig
    have e0 := congrFun heig 0
    have e1 := congrFun heig 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, currentMatrix] at e0 e1
    have hw1 : w 1 ≠ 0 := by
      intro h1'
      apply hw
      funext k
      fin_cases k
      · simpa [h1'] using e1
      · exact h1'
    refine hq μ ?_
    have hw0 : w 0 = -(μ * w 1) := by linear_combination -e1
    rw [hw0] at e0
    apply mul_right_cancel₀ hw1
    push_cast
    linear_combination e0

/-- The line eigenvector of the voltage level (`k_ff = 1`, `Z_v = 0`): eigenvalue `−Z_g/L_g`. -/
@[tmio M, powerlib_domain] theorem voltageMatrix_mulVec_line (hkff : p.kff = 1) (hZv : p.Zv = 0) :
    p.voltageMatrix *ᵥ ![0, 1, 0] = (-p.Zg / p.Lg) • ![0, 1, 0] := by
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, voltageMatrix, hkff, hZv]

/-- Every root of the voltage PI polynomial `s² + (K_pv + (1 − k_dv) jω₀C_f)/C_f · s + K_iv/C_f`
is an eigenvalue of the voltage level (`k_ff = 1`, `Z_v = 0`). -/
@[tmio M, powerlib_domain] theorem voltageMatrix_eigen_of_root (hkff : p.kff = 1)
    (hZv : p.Zv = 0) {μ : ℂ}
    (hμ : μ ^ 2 + (⟨p.Kpv / p.Cf, (1 - p.kdv) * p.Bf / p.Cf⟩ : ℂ) * μ +
      ((p.Kiv / p.Cf : ℝ) : ℂ) = 0) :
    ∃ w : Fin 3 → ℂ, w ≠ 0 ∧ p.voltageMatrix *ᵥ w = μ • w := by
  have hα : (⟨p.Kpv / p.Cf, (1 - p.kdv) * p.Bf / p.Cf⟩ : ℂ) =
      -((-p.Kpv + p.kdv * (p.Bf * I) - p.Bf * I) / p.Cf) := by
    rw [Complex.mk_eq_add_mul_I]; push_cast; ring
  by_cases hc : μ + p.Zg / p.Lg = 0
  · have hμe : μ = -p.Zg / p.Lg := by rw [neg_div]; linear_combination hc
    exact ⟨![0, 1, 0], fun h0 => by simpa using congrFun h0 1,
      by rw [hμe]; exact p.voltageMatrix_mulVec_line hkff hZv⟩
  · refine ⟨![-μ * (μ + p.Zg / p.Lg), -μ / p.Lg, μ + p.Zg / p.Lg],
      fun h0 => hc (by simpa using congrFun h0 2), ?_⟩
    push_cast at hμ
    funext k
    fin_cases k <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, voltageMatrix, hkff, hZv]
    · linear_combination (μ + p.Zg / p.Lg) * hμ - (μ * (μ + p.Zg / p.Lg)) * hα
    · ring

/-- **The voltage level, exactly** (full line-current feed-forward `k_ff = 1`, no virtual
impedance, any decoupling gain `k_dv`). Its real form is spectrally stable iff `K_pv/C_f`,
`K_iv/C_f` and `R_g/L_g` are positive: it is block triangular, the voltage PI loop
`s² + (K_pv + (1 − k_dv) jω₀C_f)/C_f · s + K_iv/C_f`
(`Criteria.complexQuadratic_realConst_roots_re_neg_iff`) feeding the line `−Z_g/L_g`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_voltageMatrix_iff (hkff : p.kff = 1)
    (hZv : p.Zv = 0) :
    Linear.SpectrallyStable (realify p.voltageMatrix) ↔
      0 < p.Kpv / p.Cf ∧ 0 < p.Kiv / p.Cf ∧ 0 < p.Rg / p.Lg := by
  have hα : (⟨p.Kpv / p.Cf, (1 - p.kdv) * p.Bf / p.Cf⟩ : ℂ) =
      -((-p.Kpv + p.kdv * (p.Bf * I) - p.Bf * I) / p.Cf) := by
    rw [Complex.mk_eq_add_mul_I]; push_cast; ring
  have hq := Criteria.complexQuadratic_realConst_roots_re_neg_iff (p.Kpv / p.Cf)
    ((1 - p.kdv) * p.Bf / p.Cf) (p.Kiv / p.Cf)
  have hline := p.voltageMatrix_mulVec_line hkff hZv
  have hne : (![0, 1, 0] : Fin 3 → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 1
  have hre : (-p.Zg / p.Lg).re = -(p.Rg / p.Lg) := by
    rw [neg_div, Complex.neg_re, Complex.div_ofReal_re, Zg_eq]
    simp
  constructor
  · intro hs
    have hRg : 0 < p.Rg / p.Lg := by
      by_contra h
      exact SingularPerturbation.not_spectrallyStable_realify hne hline (by rw [hre]; linarith) hs
    have hquad : ∀ s : ℂ, s ^ 2 + (⟨p.Kpv / p.Cf, (1 - p.kdv) * p.Bf / p.Cf⟩ : ℂ) * s +
        ((p.Kiv / p.Cf : ℝ) : ℂ) = 0 → s.re < 0 := by
      intro μ hμ
      by_contra hneg
      obtain ⟨w, hw, hwμ⟩ := p.voltageMatrix_eigen_of_root hkff hZv hμ
      exact SingularPerturbation.not_spectrallyStable_realify hw hwμ (not_lt.mp hneg) hs
    obtain ⟨h1, h0⟩ := hq.mp hquad
    exact ⟨h1, h0, hRg⟩
  · rintro ⟨h1, h0, hg⟩
    have hquad := hq.mpr ⟨h1, h0⟩
    refine SingularPerturbation.spectrallyStable_realify_of_eigen fun μ w hw heig => ?_
    have e0 := congrFun heig 0
    have e1 := congrFun heig 1
    have e2 := congrFun heig 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, voltageMatrix, hkff, hZv] at e0 e1 e2
    by_cases hw2 : w 2 = 0
    · have hw0 : w 0 = 0 := by simpa [hw2] using e2
      have hw1 : w 1 ≠ 0 := by
        intro h'
        apply hw
        funext k
        fin_cases k
        · exact hw0
        · exact h'
        · exact hw2
      rw [hw0] at e1
      have hμ : μ = -p.Zg / p.Lg := by
        apply mul_right_cancel₀ hw1
        linear_combination -e1
      rw [hμ, hre]
      linarith
    · refine hquad μ ?_
      have hw0 : w 0 = -(μ * w 2) := by linear_combination -e2
      rw [hw0] at e0
      apply mul_right_cancel₀ hw2
      push_cast
      linear_combination e0 + (μ * w 2) * hα

/-- **The voltage level with partial line-current feed-forward** (`k_ff ≤ 1`, no virtual
impedance, any `k_dv`) is stable for positive `C_f, L_g, R_g, K_pv, K_iv`. An eigenvalue `s ≠ 0`
satisfies `s + (K_pv − (k_dv − 1) jω₀C_f)/C_f + κ/(s + Z_g/L_g) + (K_iv/C_f)/s = 0` with
`κ = (1 − k_ff)/(C_f L_g) ≥ 0`, whose real part is positive on `Re s ≥ 0`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_voltageMatrix_of_kff_le_one (hZv : p.Zv = 0)
    (hkff : p.kff ≤ 1) (hCf : 0 < p.Cf) (hLg : 0 < p.Lg) (hRg : 0 < p.Rg) (hKpv : 0 < p.Kpv)
    (hKiv : 0 < p.Kiv) : Linear.SpectrallyStable (realify p.voltageMatrix) := by
  refine SingularPerturbation.spectrallyStable_realify_of_eigen fun μ w hw heig => ?_
  have e0 := congrFun heig 0
  have e1 := congrFun heig 1
  have e2 := congrFun heig 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, voltageMatrix, hZv] at e0 e1 e2
  set z : ℂ := p.Zg / p.Lg with hz
  have hzre : z.re = p.Rg / p.Lg := by
    rw [hz, Complex.div_ofReal_re, Zg_eq]; simp
  have hrg : 0 < p.Rg / p.Lg := div_pos hRg hLg
  by_contra hneg
  have hre : 0 ≤ μ.re := not_lt.mp hneg
  have hμz : μ + z ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [Complex.add_re, hzre, Complex.zero_re] at this
    linarith
  by_cases hw0 : w 0 = 0
  · have hw2 : w 2 = 0 ∨ μ = 0 := by
      rw [hw0, neg_zero] at e2
      rcases mul_eq_zero.mp e2.symm with h | h
      · exact Or.inr h
      · exact Or.inl h
    rw [hw0] at e1
    have hw1 : w 1 = 0 := by
      have : (μ + z) * w 1 = 0 := by rw [hz]; linear_combination -e1
      exact (mul_eq_zero.mp this).resolve_left hμz
    rcases hw2 with h2 | hμ0
    · apply hw; funext k; fin_cases k <;> simp [hw0, hw1, h2]
    · rw [hw0, hw1, hμ0] at e0
      have : (p.Kiv : ℂ) / p.Cf * w 2 = 0 := by linear_combination e0
      have hc : (p.Kiv : ℂ) / p.Cf ≠ 0 := by
        have : ((p.Kiv / p.Cf : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hKiv hCf).ne'
        simpa using this
      have h2 := (mul_eq_zero.mp this).resolve_left hc
      apply hw; funext k; fin_cases k <;> simp [hw0, hw1, h2]
  · have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hw0 (by simpa using e2)
    -- the scalar equation
    have hpoly : (μ ^ 2 * (μ + z) - ((-p.Kpv + p.kdv * (p.Bf * I) - p.Bf * I) / p.Cf) * μ * (μ + z)
        - ((p.kff - 1) / p.Cf) * (1 / p.Lg) * μ + (p.Kiv / p.Cf) * (μ + z)) * w 0 = 0 := by
      rw [hz]
      linear_combination (-μ * (μ + p.Zg / p.Lg)) * e0 + (-((p.kff - 1) / p.Cf) * μ) * e1 +
        (-(p.Kiv / p.Cf) * (μ + p.Zg / p.Lg)) * e2
    have hpoly' := (mul_eq_zero.mp hpoly).resolve_right hw0
    clear_value z
    have hmz : μ * (μ + z) ≠ 0 := mul_ne_zero hμ0 hμz
    have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg.ne'
    have hCf' : (p.Cf : ℂ) ≠ 0 := by exact_mod_cast hCf.ne'
    have hscal : μ + (p.Kpv - (p.kdv - 1) * p.Bf * I) / p.Cf +
        (((1 - p.kff) / (p.Cf * p.Lg) : ℝ) : ℂ) * (μ + z)⁻¹ +
        ((p.Kiv / p.Cf : ℝ) : ℂ) * μ⁻¹ = 0 := by
      have hid : μ + (p.Kpv - (p.kdv - 1) * p.Bf * I) / p.Cf +
          (((1 - p.kff) / (p.Cf * p.Lg) : ℝ) : ℂ) * (μ + z)⁻¹ +
          ((p.Kiv / p.Cf : ℝ) : ℂ) * μ⁻¹ =
          (μ ^ 2 * (μ + z) - ((-p.Kpv + p.kdv * (p.Bf * I) - p.Bf * I) / p.Cf) * μ * (μ + z)
            - ((p.kff - 1) / p.Cf) * (1 / p.Lg) * μ + (p.Kiv / p.Cf) * (μ + z)) *
            (μ * (μ + z))⁻¹ := by
        push_cast
        field_simp
        ring
      rw [hid, hpoly', zero_mul]
    have h1 := congrArg Complex.re hscal
    simp only [Complex.add_re, Complex.zero_re, Complex.re_ofReal_mul] at h1
    have hA : ((p.Kpv - (p.kdv - 1) * p.Bf * I) / p.Cf : ℂ).re = p.Kpv / p.Cf := by
      rw [show ((p.Kpv : ℂ) - (p.kdv - 1) * p.Bf * I) / p.Cf =
        (((p.Kpv / p.Cf : ℝ) : ℂ) + (((-(p.kdv - 1) * p.Bf / p.Cf) : ℝ) : ℂ) * I) by
          push_cast; ring]
      simp
    have hinv1 : 0 ≤ ((μ + z)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg (by rw [Complex.add_re, hzre]; linarith) (Complex.normSq_nonneg _)
    have hinv2 : 0 ≤ (μ⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hre (Complex.normSq_nonneg _)
    have hκ : 0 ≤ (1 - p.kff) / (p.Cf * p.Lg) := div_nonneg (by linarith) (by positivity)
    rw [hA] at h1
    nlinarith [mul_nonneg hκ hinv1, mul_nonneg (div_pos hKiv hCf).le hinv2, div_pos hKpv hCf]

/-! ### The voltage level decided by the Routh–Hurwitz criterion -/

/-- The coefficient `a₂ = Z_g/L_g + α_v` of the characteristic polynomial of the voltage level,
`α_v = (K_pv + (1 − k_dv) jω₀C_f)/C_f` the voltage PI damping. -/
def voltageA2 : ℂ := p.Zg / p.Lg + (p.Kpv + (1 - p.kdv) * p.Bf * I) / p.Cf

/-- The coefficient `a₁ = K_iv/C_f + α_v Z_g/L_g + (1 − k_ff + K_pv Z_v)/(C_f L_g)`. -/
def voltageA1 : ℂ :=
  p.Kiv / p.Cf + (p.Kpv + (1 - p.kdv) * p.Bf * I) / p.Cf * (p.Zg / p.Lg) +
    (1 - p.kff + p.Kpv * p.Zv) / (p.Cf * p.Lg)

/-- The coefficient `a₀ = K_iv Z_t/(C_f L_g)`. -/
def voltageA0 : ℂ := p.Kiv * p.Zt / (p.Cf * p.Lg)

/-- **The characteristic polynomial of the voltage level**, any `k_ff`, `Z_v`, `k_dv`:
`det(s − voltageMatrix) = s³ + a₂ s² + a₁ s + a₀`, i.e.
`(s + Z_g/L_g)(s² + α_v s + K_iv/C_f) + ((1 − k_ff + K_pv Z_v) s + K_iv Z_v)/(C_f L_g)`. -/
@[tmio M, powerlib_domain] theorem det_voltageMatrix (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0)
    (s : ℂ) : (Matrix.scalar (Fin 3) s - p.voltageMatrix).det =
      s ^ 3 + p.voltageA2 * s ^ 2 + p.voltageA1 * s + p.voltageA0 := by
  have hCf' : (p.Cf : ℂ) ≠ 0 := by exact_mod_cast hCf
  have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg
  rw [Matrix.det_fin_three]
  simp [voltageMatrix, voltageA2, voltageA1, voltageA0, Zt, Matrix.scalar_apply]
  field_simp
  ring

/-- The real and imaginary parts of the coefficients (`C_f, L_g ≠ 0`; `Z_v = R_v + jX_v`). -/
@[tmio M, powerlib_domain] theorem voltageA_parts (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) :
    p.voltageA2.re = p.Rg / p.Lg + p.Kpv / p.Cf ∧ p.voltageA2.im = p.ω0 * (2 - p.kdv) ∧
      p.voltageA1.re = (p.Kpv * (p.Rg + p.Rv) + p.Kiv * p.Lg + 1 - p.kff +
        p.Cf * p.Lg * p.ω0 ^ 2 * (p.kdv - 1)) / (p.Cf * p.Lg) ∧
      p.voltageA1.im = (p.Kpv * (p.ω0 * p.Lg + p.Xv) + (1 - p.kdv) * p.ω0 * p.Cf * p.Rg) /
        (p.Cf * p.Lg) ∧
      p.voltageA0.re = p.Kiv * (p.Rg + p.Rv) / (p.Cf * p.Lg) ∧
      p.voltageA0.im = p.Kiv * (p.ω0 * p.Lg + p.Xv) / (p.Cf * p.Lg) := by
  have hCf' : (p.Cf : ℂ) ≠ 0 := by exact_mod_cast hCf
  have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg
  have e2 : p.voltageA2 = ((p.Rg / p.Lg + p.Kpv / p.Cf : ℝ) : ℂ) +
      ((p.ω0 * (2 - p.kdv) : ℝ) : ℂ) * I := by
    rw [voltageA2, Zg_eq, Bf]; push_cast; field_simp; ring
  have e1 : p.voltageA1 = (((p.Kpv * (p.Rg + p.Rv) + p.Kiv * p.Lg + 1 - p.kff +
        p.Cf * p.Lg * p.ω0 ^ 2 * (p.kdv - 1)) / (p.Cf * p.Lg) : ℝ) : ℂ) +
      (((p.Kpv * (p.ω0 * p.Lg + p.Xv) + (1 - p.kdv) * p.ω0 * p.Cf * p.Rg) /
        (p.Cf * p.Lg) : ℝ) : ℂ) * I := by
    rw [voltageA1, Zg_eq, Bf, Zv]; push_cast; field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have e0 : p.voltageA0 = ((p.Kiv * (p.Rg + p.Rv) / (p.Cf * p.Lg) : ℝ) : ℂ) +
      ((p.Kiv * (p.ω0 * p.Lg + p.Xv) / (p.Cf * p.Lg) : ℝ) : ℂ) * I := by
    rw [voltageA0, Zt, Zg_eq, Zv]; push_cast; field_simp; ring
  rw [e2, e1, e0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

/-- **The voltage level as a complex cubic**: its real form is spectrally stable iff every root of
`s³ + a₂ s² + a₁ s + a₀` has negative real part (`C_f, L_g ≠ 0`, any `k_ff`, `Z_v`, `k_dv`). -/
@[tmio M, powerlib_domain] theorem spectrallyStable_voltageMatrix_iff_cubic (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) :
    Linear.SpectrallyStable (realify p.voltageMatrix) ↔
      ∀ s : ℂ, s ^ 3 + p.voltageA2 * s ^ 2 + p.voltageA1 * s + p.voltageA0 = 0 → s.re < 0 := by
  rw [Criteria.spectrallyStable_realify_iff_charpoly]
  simp only [Matrix.eval_charpoly, p.det_voltageMatrix hCf hLg]

/-- **The voltage level, exactly, for every feed-forward and virtual impedance** (Routh–Hurwitz
for the complex cubic, `Criteria.complexCubic_roots_re_neg_iff`): with `C_f, L_g ≠ 0`, its real
form is spectrally stable iff `Re a₂ > 0`, `Re a₂ (Re a₁ Re a₂ + Im a₁ Im a₂ − Re a₀) > (Im a₁)²`
and `complexCubicDet a₂ a₁ a₀ > 0`, with the parts of `a₂, a₁, a₀` of `voltageA_parts`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_voltageMatrix_iff_routh (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) :
    Linear.SpectrallyStable (realify p.voltageMatrix) ↔
      0 < p.voltageA2.re ∧
        0 < p.voltageA2.re * (p.voltageA1.re * p.voltageA2.re + p.voltageA1.im * p.voltageA2.im -
          p.voltageA0.re) - p.voltageA1.im ^ 2 ∧
        0 < Criteria.complexCubicDet p.voltageA2 p.voltageA1 p.voltageA0 := by
  rw [p.spectrallyStable_voltageMatrix_iff_cubic hCf hLg, Criteria.complexCubic_roots_re_neg_iff]

/-- A stable voltage level has `K_iv ≠ 0` and `Z_t ≠ 0` (otherwise `0` is a root of the cubic). -/
@[tmio M, powerlib_domain] theorem kiv_ne_zero_and_zt_ne_zero_of_spectrallyStable
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hV : Linear.SpectrallyStable (realify p.voltageMatrix)) :
    p.Kiv ≠ 0 ∧ p.Zt ≠ 0 := by
  have h0 := (p.spectrallyStable_voltageMatrix_iff_cubic hCf hLg).mp hV 0
  have ha0 : p.voltageA0 ≠ 0 := fun h => by simp [h] at h0
  rw [voltageA0] at ha0
  refine ⟨fun h => ha0 (by simp [h]), fun h => ha0 (by simp [h])⟩

/-! ### The current-loop time scale -/

/-- The current loop accelerated by `μ⁻¹`: `L_f ↦ μ L_f`, `K_ic ↦ K_ic/μ` (the roots of
`L_f s² + (K_pc + R_f) s + K_ic` multiplied by `μ⁻¹`); all other parameters unchanged. -/
def currentScaled (μ : ℝ) : Params := { p with Lf := μ * p.Lf, Kic := p.Kic / μ }

@[tmio M, powerlib_domain] theorem currentScaled_imp (μ : ℝ) :
    (p.currentScaled μ).Bf = p.Bf ∧ (p.currentScaled μ).Zg = p.Zg ∧
      (p.currentScaled μ).Zv = p.Zv := ⟨rfl, rfl, rfl⟩

/-- `diag(1, 1, 1, μ, 1)`: the current-loop integrator rescaled. -/
def xiScale (μ : ℝ) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal ![1, 1, 1, (μ : ℂ), 1]

@[tmio M, powerlib_domain] theorem xiScale_mul {μ : ℝ} (hμ : μ ≠ 0) :
    xiScale μ * xiScale μ⁻¹ = 1 := by
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  rw [xiScale, xiScale, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  fin_cases a <;> simp [hμ']

/-- The fast matrix of the current-scaled parameters is similar (by `xiScale μ`) to the fast matrix
with its current-loop rows multiplied by `μ⁻¹` (`SingularPerturbation.phasorScale`). -/
@[tmio M, powerlib_domain] theorem fastMatrix_currentScaled {μ : ℝ} (hμ : μ ≠ 0) :
    (p.currentScaled μ).fastMatrix 0 = xiScale μ *
      (SingularPerturbation.phasorScale loopSplit μ * p.fastMatrix 0) * xiScale μ⁻¹ := by
  have h0 : ej 0 = 1 := by simp [ej]
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  obtain ⟨hB, hZg, hZv⟩ := p.currentScaled_imp μ
  ext a b
  rw [xiScale, xiScale, SingularPerturbation.phasorScale, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [fastMatrix, hB, hZg, hZv, loopSplit, h0] <;>
    (try simp [currentScaled]) <;>
    first | ring1 | field_simp

/-- Spectral stability of the current-scaled fast block, at any angle, is that of the real form of
the fast matrix with its current-loop rows multiplied by `μ⁻¹`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_currentScaled_iff {μ : ℝ}
    (hμ : μ ≠ 0) (δ : ℝ) :
    Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) ↔
      Linear.SpectrallyStable
        (realify (SingularPerturbation.phasorScale loopSplit μ * p.fastMatrix 0)) := by
  rw [spectrallyStable_fastBlock_iff, fastBlock_eq_realify, p.fastMatrix_currentScaled hμ,
    SingularPerturbation.realify_mul _ (xiScale μ⁻¹), SingularPerturbation.realify_mul (xiScale μ)]
  refine Linear.spectrallyStable_conj ?_ _
  rw [← SingularPerturbation.realify_mul, show xiScale μ⁻¹ * xiScale μ = 1 by
    simpa using xiScale_mul (inv_ne_zero hμ), SingularPerturbation.realify_one]

/-- **Time-scale separation of the current and voltage loops (sufficient condition).** If the
current loop (`currentMatrix`) and the voltage level with an ideal current loop
(`voltageMatrix`) are stable, there is `μ* > 0` such that for every `μ ∈ (0, μ*)` the boundary
layer of `currentScaled μ` is spectrally stable at every angle. -/
@[tmio M, powerlib_domain] theorem exists_muStar_spectrallyStable_fastBlock (hKic : p.Kic ≠ 0)
    (hA : Linear.SpectrallyStable (realify p.currentMatrix))
    (hV : Linear.SpectrallyStable (realify p.voltageMatrix)) :
    ∃ μs > 0, ∀ μ, 0 < μ → μ < μs → ∀ δ,
      Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) := by
  obtain ⟨h11, hH, hR⟩ := p.fastMatrix_blocks hKic
  obtain ⟨μs, hμs, h⟩ := SingularPerturbation.exists_epsStar_spectrallyStable_realify loopSplit
    (p.fastMatrix 0) (by rw [h11]; exact hH) hR (by rw [h11]; exact hA) hV
  exact ⟨μs, hμs, fun μ hμ hlt δ =>
    (p.spectrallyStable_fastBlock_currentScaled_iff hμ.ne' δ).mpr (h μ hμ hlt)⟩

/-- The explicit current-loop time scale: Kokotović's bound
(`SingularPerturbation.graphEpsStar`) for the fast block at angle `0` split along `loopSplit`,
with Lyapunov matrices `P₀` of the voltage level and `P₂` of the current loop (real forms). -/
def muStar (P0 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ)
    (P2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) : ℝ :=
  SingularPerturbation.graphEpsStar (SingularPerturbation.realifySplit loopSplit) (p.fastBlock 0)
    P0 P2

/-- **Time-scale separation, explicit.** With positive definite Lyapunov matrices `P₀` of the real
voltage level and `P₂` of the real current loop, the boundary layer of `currentScaled μ` is
spectrally stable at every angle for every `μ ∈ (0, muStar P₀ P₂)`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_currentScaled_of_lt
    (hKic : p.Kic ≠ 0) {P0 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ}
    {P2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ} (hP0 : P0.PosDef) (hP2 : P2.PosDef)
    (hL0 : P0 * realify p.voltageMatrix + (realify p.voltageMatrix)ᵀ * P0 = -1)
    (hL2 : P2 * realify p.currentMatrix + (realify p.currentMatrix)ᵀ * P2 = -1) {μ : ℝ}
    (hμ : 0 < μ) (hlt : μ < p.muStar P0 P2) (δ : ℝ) :
    Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) := by
  obtain ⟨h11, hH, hR⟩ := p.fastMatrix_blocks hKic
  rw [p.spectrallyStable_fastBlock_currentScaled_iff hμ.ne']
  exact SingularPerturbation.spectrallyStable_realify_of_lt_graphEpsStar loopSplit (p.fastMatrix 0)
    (by rw [h11]; exact hH) hR hP0 hP2 hL0 (by rw [h11]; exact hL2) hμ hlt

/-- **From the gains, any feed-forward, decoupling and virtual impedance.** With a stable current
loop (`L_f, K_pc + R_f, K_ic > 0`), `C_f, L_g ≠ 0` and the three Routh–Hurwitz inequalities of the
voltage level (`spectrallyStable_voltageMatrix_iff_routh`), there is `μ* > 0` such that the
boundary layer of `currentScaled μ` is spectrally stable for every `μ ∈ (0, μ*)` and every
angle. -/
@[tmio M, powerlib_domain] theorem exists_muStar_spectrallyStable_fastBlock_of_routh
    (hLf : 0 < p.Lf) (hKpc : 0 < p.Kpc + p.Rf) (hKic : 0 < p.Kic) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (h2 : 0 < p.voltageA2.re)
    (h1 : 0 < p.voltageA2.re * (p.voltageA1.re * p.voltageA2.re + p.voltageA1.im * p.voltageA2.im -
      p.voltageA0.re) - p.voltageA1.im ^ 2)
    (h0 : 0 < Criteria.complexCubicDet p.voltageA2 p.voltageA1 p.voltageA0) :
    ∃ μs > 0, ∀ μ, 0 < μ → μ < μs → ∀ δ,
      Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) :=
  p.exists_muStar_spectrallyStable_fastBlock hKic.ne'
    (p.spectrallyStable_currentMatrix_iff.mpr ⟨div_pos hKpc hLf, div_pos hKic hLf⟩)
    ((p.spectrallyStable_voltageMatrix_iff_routh hCf hLg).mpr ⟨h2, h1, h0⟩)

/-- **From the gains.** With partial or full line-current feed-forward (`k_ff ≤ 1`), no virtual
impedance, any decoupling gain `k_dv`, positive `L_f, C_f, L_g, R_g`, `K_pc + R_f > 0` and
positive `K_ic, K_pv, K_iv`, there is `μ* > 0` such that the boundary layer of `currentScaled μ`
is spectrally stable for every `μ ∈ (0, μ*)` and every angle (the Routh–Hurwitz inequalities of
the voltage level hold by `spectrallyStable_voltageMatrix_of_kff_le_one`). -/
@[tmio M, powerlib_domain] theorem exists_muStar_spectrallyStable_fastBlock_of_gains
    (hLf : 0 < p.Lf) (hCf : 0 < p.Cf) (hLg : 0 < p.Lg) (hRg : 0 < p.Rg)
    (hKpc : 0 < p.Kpc + p.Rf) (hKic : 0 < p.Kic) (hKpv : 0 < p.Kpv) (hKiv : 0 < p.Kiv)
    (hkff : p.kff ≤ 1) (hZv : p.Zv = 0) :
    ∃ μs > 0, ∀ μ, 0 < μ → μ < μs → ∀ δ,
      Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) := by
  obtain ⟨h2, h1, h0⟩ := (p.spectrallyStable_voltageMatrix_iff_routh hCf.ne' hLg.ne').mp
    (p.spectrallyStable_voltageMatrix_of_kff_le_one hZv hkff hCf hLg hRg hKpv hKiv)
  exact p.exists_muStar_spectrallyStable_fastBlock_of_routh hLf hKpc hKic hCf.ne' hLg.ne' h2 h1 h0

/-! ### Necessity for a fast current loop -/

/-- The current-loop block of the fast matrix needs no nondegeneracy. -/
@[tmio M, powerlib_domain] theorem fastMatrix_toBlocks₁₁ :
    ((p.fastMatrix 0).reindex loopSplit loopSplit).toBlocks₁₁ = p.currentMatrix := by
  have h0 : ej 0 = 1 := by simp [ej]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.toBlocks₁₁, loopSplit, fastMatrix, currentMatrix, h0]

/-- The fast matrix is invertible under the nondegeneracy hypotheses (`det_fastMatrix`). -/
@[tmio M, powerlib_domain] theorem isUnit_det_fastMatrix (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0) (δ : ℝ) :
    IsUnit (p.fastMatrix δ).det := by
  rw [p.det_fastMatrix hLf hCf hLg, isUnit_iff_ne_zero, neg_ne_zero]
  have hden : (p.Lf : ℂ) * p.Cf * p.Lg ≠ 0 := by
    exact_mod_cast mul_ne_zero (mul_ne_zero hLf hCf) hLg
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast hKic) (by exact_mod_cast hKiv))
    hZt) hden

/-- **A strictly unstable current loop.** If the current loop has an eigenvalue with positive
real part, the boundary layer of `currentScaled μ` is not spectrally stable, at any angle, for
every sufficiently small `μ > 0`
(`SingularPerturbation.eventually_not_spectrallyStable_realify_of_fast`). -/
@[tmio M, powerlib_domain] theorem eventually_not_spectrallyStable_fastBlock_of_current
    {lam : ℂ} (hlam : 0 < lam.re) {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (h : p.currentMatrix *ᵥ v = lam • v) :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ δ, ¬ Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) := by
  have hev := SingularPerturbation.eventually_not_spectrallyStable_realify_of_fast loopSplit
    (p.fastMatrix 0) hlam hv (by rw [p.fastMatrix_toBlocks₁₁]; exact h)
  filter_upwards [hev, self_mem_nhdsWithin] with μ hμ hpos δ
  rwa [p.spectrallyStable_fastBlock_currentScaled_iff (ne_of_gt hpos) δ]

/-- **A strictly unstable voltage level.** Under the nondegeneracy hypotheses, if the voltage level
with an ideal current loop has an eigenvalue with positive real part, the boundary layer of
`currentScaled μ` is not spectrally stable, at any angle, for every sufficiently small `μ > 0`
(`SingularPerturbation.eventually_not_spectrallyStable_realify_of_slow`). -/
@[tmio M, powerlib_domain] theorem eventually_not_spectrallyStable_fastBlock_of_voltage
    (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0)
    (hZt : p.Zt ≠ 0) {lam : ℂ} (hlam : 0 < lam.re) {w : Fin 3 → ℂ} (hw : w ≠ 0)
    (h : p.voltageMatrix *ᵥ w = lam • w) :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ δ, ¬ Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) := by
  obtain ⟨-, hH, hR⟩ := p.fastMatrix_blocks hKic
  have hev := SingularPerturbation.eventually_not_spectrallyStable_realify_of_slow loopSplit
    (p.isUnit_det_fastMatrix hLf hCf hLg hKic hKiv hZt 0)
    (by rw [p.fastMatrix_toBlocks₁₁]; exact hH) hR hlam hw h
  filter_upwards [hev, self_mem_nhdsWithin] with μ hμ hpos δ
  rwa [p.spectrallyStable_fastBlock_currentScaled_iff (ne_of_gt hpos) δ]

/-- A current-loop polynomial `s² + (K_pc + R_f)/L_f · s + K_ic/L_f` with a negative coefficient
gives an eigenvalue of the current loop with positive real part
(`Criteria.exists_root_re_pos_of_coeff_neg`). -/
@[tmio M, powerlib_domain] theorem exists_currentMatrix_eigen_re_pos
    (h : (p.Kpc + p.Rf) / p.Lf < 0 ∨ p.Kic / p.Lf < 0) :
    ∃ (lam : ℂ) (v : Fin 2 → ℂ), v ≠ 0 ∧ p.currentMatrix *ᵥ v = lam • v ∧ 0 < lam.re := by
  set a1 := (p.Kpc + p.Rf) / p.Lf
  set a0 := p.Kic / p.Lf
  have hmon : (Polynomial.X ^ 2 + Polynomial.C a1 * Polynomial.X + Polynomial.C a0 :
      Polynomial ℝ).Monic := by monicity!
  have hroot : ∃ s : ℂ, s ^ 2 + (a1 : ℂ) * s + (a0 : ℂ) = 0 ∧ 0 < s.re := by
    rcases h with h1 | h0
    · obtain ⟨s, hs, hre⟩ := Criteria.exists_root_re_pos_of_coeff_neg hmon (k := 1)
        (by simpa [Polynomial.coeff_X, Polynomial.coeff_C] using h1)
      exact ⟨s, by simpa using hs, hre⟩
    · obtain ⟨s, hs, hre⟩ := Criteria.exists_root_re_pos_of_coeff_neg hmon (k := 0)
        (by simpa [Polynomial.coeff_X, Polynomial.coeff_C] using h0)
      exact ⟨s, by simpa using hs, hre⟩
  obtain ⟨s, hs, hre⟩ := hroot
  refine ⟨s, ![-s, 1], fun h0 => by simpa using congrFun h0 1, ?_, hre⟩
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, currentMatrix, a1, a0] at hs ⊢
  linear_combination hs

/-- With `k_ff = 1`, `Z_v = 0`: a negative `R_g/L_g`, a negative `K_pv/C_f`, or a negative
`K_iv/C_f` with `K_pv ≠ 0` gives an eigenvalue of the voltage level with positive real part (the
line eigenvalue `−Z_g/L_g`, or a root of the voltage PI polynomial,
`SingularPerturbation.exists_complexQuadratic_root_re_pos`). -/
@[tmio M, powerlib_domain] theorem exists_voltageMatrix_eigen_re_pos (hkff : p.kff = 1)
    (hZv : p.Zv = 0)
    (h : p.Rg / p.Lg < 0 ∨ p.Kpv / p.Cf < 0 ∨ (p.Kiv / p.Cf < 0 ∧ p.Kpv / p.Cf ≠ 0)) :
    ∃ (lam : ℂ) (w : Fin 3 → ℂ), w ≠ 0 ∧ p.voltageMatrix *ᵥ w = lam • w ∧ 0 < lam.re := by
  rcases h with hg | hq
  · refine ⟨-p.Zg / p.Lg, ![0, 1, 0], fun h0 => by simpa using congrFun h0 1,
      p.voltageMatrix_mulVec_line hkff hZv, ?_⟩
    rw [neg_div, Complex.neg_re, Complex.div_ofReal_re, Zg_eq]
    simp
    linarith
  · obtain ⟨s, hs, hre⟩ := SingularPerturbation.exists_complexQuadratic_root_re_pos (p.Kpv / p.Cf)
      ((1 - p.kdv) * p.Bf / p.Cf) (p.Kiv / p.Cf) hq
    obtain ⟨w, hw, hws⟩ := p.voltageMatrix_eigen_of_root hkff hZv hs
    exact ⟨s, w, hw, hws, hre⟩

/-- **Necessity of the gain conditions for a fast current loop.** With `k_ff = 1`, `Z_v = 0` and
the nondegeneracy hypotheses, if one of the block conditions fails strictly —
`(K_pc + R_f)/L_f < 0`, `K_ic/L_f < 0`, `R_g/L_g < 0`, `K_pv/C_f < 0`, or `K_iv/C_f < 0` with
`K_pv ≠ 0` — the boundary layer of `currentScaled μ` is not spectrally stable, at any angle, for
every sufficiently small `μ > 0`. Together with `exists_muStar_spectrallyStable_fastBlock_of_gains`
this decides the boundary layer for a fast current loop, up to the boundary cases (a vanishing
coefficient, or `K_iv/C_f < 0` with `K_pv = 0`). -/
@[tmio M, powerlib_domain] theorem eventually_not_spectrallyStable_fastBlock_of_gains
    (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0)
    (hZg : p.Zg ≠ 0) (hkff : p.kff = 1) (hZv : p.Zv = 0)
    (h : (p.Kpc + p.Rf) / p.Lf < 0 ∨ p.Kic / p.Lf < 0 ∨ p.Rg / p.Lg < 0 ∨ p.Kpv / p.Cf < 0 ∨
      (p.Kiv / p.Cf < 0 ∧ p.Kpv / p.Cf ≠ 0)) :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ δ, ¬ Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) := by
  have hZt : p.Zt ≠ 0 := by rwa [Zt, hZv, add_zero]
  rcases h with h1 | h1 | h1 | h1 | h1
  · obtain ⟨lam, v, hv, hlv, hre⟩ := p.exists_currentMatrix_eigen_re_pos (Or.inl h1)
    exact p.eventually_not_spectrallyStable_fastBlock_of_current hre hv hlv
  · obtain ⟨lam, v, hv, hlv, hre⟩ := p.exists_currentMatrix_eigen_re_pos (Or.inr h1)
    exact p.eventually_not_spectrallyStable_fastBlock_of_current hre hv hlv
  · obtain ⟨lam, w, hw, hlw, hre⟩ := p.exists_voltageMatrix_eigen_re_pos hkff hZv (Or.inl h1)
    exact p.eventually_not_spectrallyStable_fastBlock_of_voltage hLf hCf hLg hKic hKiv hZt hre hw
      hlw
  · obtain ⟨lam, w, hw, hlw, hre⟩ :=
      p.exists_voltageMatrix_eigen_re_pos hkff hZv (Or.inr (Or.inl h1))
    exact p.eventually_not_spectrallyStable_fastBlock_of_voltage hLf hCf hLg hKic hKiv hZt hre hw
      hlw
  · obtain ⟨lam, w, hw, hlw, hre⟩ :=
      p.exists_voltageMatrix_eigen_re_pos hkff hZv (Or.inr (Or.inr h1))
    exact p.eventually_not_spectrallyStable_fastBlock_of_voltage hLf hCf hLg hKic hKiv hZt hre hw
      hlw

end Params

/-! ### The witness with a faster current loop -/

/-- The real part of the fast matrix of `blWitness.currentScaled (1/10)` at `δ = 0`
(`L_f = 1/10`, `K_ic = 20`). -/
def blFastRe : Matrix (Fin 5) (Fin 5) ℚ :=
  !![-11, -56 / 3, 10, 200, 240; 1, 0, -1, 0, 0; 0, 10, -1, 0, 0; -1, -28 / 15, 1, 0, 24;
    0, -1, 0, 0, 0]

/-- The imaginary part of the fast matrix of `blWitness.currentScaled (1/10)` at `δ = 0`. -/
def blFastIm : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0, 10, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 0]

/-- The rational `10 × 10` real fast block of `blWitness.currentScaled (1/10)`, coordinates
`2a + c` (`finProdFinEquiv`). -/
def blFastA10 : Matrix (Fin 10) (Fin 10) ℚ := Matrix.of fun i j =>
  let a := finProdFinEquiv.symm i
  let b := finProdFinEquiv.symm j
  !![blFastRe a.1 b.1, -blFastIm a.1 b.1; blFastIm a.1 b.1, blFastRe a.1 b.1] a.2 b.2

@[tmio M, powerlib_domain] private theorem blFast_fastMatrix_apply (a b : Fin 5) :
    (blWitness.currentScaled (1 / 10)).fastMatrix 0 a b =
      ((blFastRe a b : ℝ) : ℂ) + ((blFastIm a b : ℝ) : ℂ) * I := by
  have h0 : ej 0 = 1 := by simp [ej]
  fin_cases a <;> fin_cases b <;>
    simp [Params.fastMatrix, Params.currentScaled, blFastRe, blFastIm, h0, Params.Bf,
      Params.Zg_eq, Params.Zv, blWitness] <;>
    norm_num [Complex.ext_iff]

/-- The fast block of `blWitness.currentScaled (1/10)`, relabelled by `finProdFinEquiv`, is the
real image of the rational matrix `blFastA10`. -/
@[tmio M, powerlib_domain] theorem blFast_fastBlock_reindex :
    ((blWitness.currentScaled (1 / 10)).fastBlock 0).reindex finProdFinEquiv finProdFinEquiv =
      Linear.Positive.real blFastA10 := by
  ext i j
  obtain ⟨⟨a, c'⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Linear.Positive.real, Matrix.map_apply, blFastA10, Matrix.of_apply,
    Params.fastBlock_apply, blFast_fastMatrix_apply]
  fin_cases c' <;> fin_cases c <;> simp [component, axisUnit]

/-- A rational Lyapunov certificate of the fast block of `blWitness.currentScaled (1/10)`,
produced by the verified synthesizer of `theorem/Linear/Synthesis.lean` and checked by the
kernel. -/
def blFastCertificate : Linear.Certificate (Linear.Positive.real blFastA10) :=
  lyapunov_certificate% blFastA10

/-- **A ten times faster current loop stabilizes the witness's boundary layer**: the fast block
of `blWitness.currentScaled (1/10)` is spectrally stable at every angle (the rational certificate
`blFastCertificate`), while that of `blWitness` is not (`blWitness_not_spectrallyStable`). -/
@[tmio M, powerlib_domain] theorem blWitness_currentScaled_spectrallyStable (δ : ℝ) :
    Linear.SpectrallyStable ((blWitness.currentScaled (1 / 10)).fastBlock δ) := by
  rw [Params.spectrallyStable_fastBlock_iff, ← Linear.spectrallyStable_reindex finProdFinEquiv,
    blFast_fastBlock_reindex, Linear.spectrallyStable_iff_isHurwitz]
  exact blFastCertificate.isHurwitz

/-! ### Beyond `k_ff ≤ 1`, `Z_v = 0`: positive gains do not suffice -/

/-- A witness with over-compensating line-current feed-forward `k_ff = 2` (no virtual
impedance, `ω₀ = 1`, `C_f = L_g = 1/10`, `R_g = 1/2`, `K_pv = 4/5`, `K_iv = 6/5`, `k_dv = 1`; the
current loop `L_f = K_pc = K_ic = 1`, `R_f = 0`). -/
def kffWitness : Params where
  ω0 := 1
  Lf := 1
  Rf := 0
  Cf := 1 / 10
  Lg := 1 / 10
  Rg := 1 / 2
  V := 1
  Rv := 0
  Xv := 0
  Kpv := 4 / 5
  Kiv := 6 / 5
  Kpc := 1
  Kic := 1
  kff := 2
  kdv := 1
  M := 1
  D := 1
  Pref := 0
  E0 := 1
  nq := 0
  Qref := 0
  ωq := 1

/-- The voltage level of `kffWitness` has the eigenvalue `1 + j`. -/
@[tmio M, powerlib_domain] theorem kffWitness_voltageMatrix_mulVec :
    kffWitness.voltageMatrix *ᵥ ![-1 - I, -2 - I, 1] = (1 + I) • ![-1 - I, -2 - I, 1] := by
  funext a
  fin_cases a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Params.voltageMatrix, Params.Bf,
      Params.Zg_eq, Params.Zv, kffWitness] <;>
    apply Complex.ext <;> simp <;> norm_num

/-- **`k_ff ≤ 1` is needed**: without virtual impedance and with positive `C_f, L_g, R_g, K_pv,
K_iv`, the voltage level need not be stable once `k_ff > 1` (witness `k_ff = 2`). -/
@[tmio M, powerlib_domain] theorem not_forall_spectrallyStable_voltageMatrix_of_kff :
    ¬ ∀ p : Params, p.Zv = 0 → 0 < p.Cf → 0 < p.Lg → 0 < p.Rg → 0 < p.Kpv → 0 < p.Kiv →
      Linear.SpectrallyStable (realify p.voltageMatrix) := by
  intro h
  refine SingularPerturbation.not_spectrallyStable_realify (w := ![-1 - I, -2 - I, 1])
    (fun h0 => by simpa using congrFun h0 2) kffWitness_voltageMatrix_mulVec (by simp)
    (h kffWitness ?_ ?_ ?_ ?_ ?_ ?_) <;> norm_num [kffWitness, Params.Zv]

/-- With `k_ff = 2` the boundary layer of `kffWitness.currentScaled μ` is unstable for every
sufficiently small `μ > 0`: no current-loop speed compensates the over-compensation. -/
@[tmio M, powerlib_domain] theorem kffWitness_eventually_not_spectrallyStable :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ δ,
      ¬ Linear.SpectrallyStable ((kffWitness.currentScaled μ).fastBlock δ) := by
  have hZt : kffWitness.Zt ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [Params.Zt, Params.Zg_eq, Params.Zv, kffWitness] at this
  refine kffWitness.eventually_not_spectrallyStable_fastBlock_of_voltage (by norm_num [kffWitness])
    (by norm_num [kffWitness]) (by norm_num [kffWitness]) (by norm_num [kffWitness])
    (by norm_num [kffWitness]) hZt (lam := 1 + I) (by simp)
    (fun h0 => by simpa using congrFun h0 2) kffWitness_voltageMatrix_mulVec

/-- A witness with virtual resistance `R_v = 1` (`k_ff = k_dv = 1`, `ω₀ = 1`, `C_f = 1`,
`L_g = R_g = 1/10`, `K_pv = 1/6`, `K_iv = 10/3`; current loop `L_f = K_pc = K_ic = 1`,
`R_f = 0`). -/
def rvWitness : Params where
  ω0 := 1
  Lf := 1
  Rf := 0
  Cf := 1
  Lg := 1 / 10
  Rg := 1 / 10
  V := 1
  Rv := 1
  Xv := 0
  Kpv := 1 / 6
  Kiv := 10 / 3
  Kpc := 1
  Kic := 1
  kff := 1
  kdv := 1
  M := 1
  D := 1
  Pref := 0
  E0 := 1
  nq := 0
  Qref := 0
  ωq := 1

/-- The voltage level of `rvWitness` has the eigenvalue `1 + 3j`. -/
@[tmio M, powerlib_domain] theorem rvWitness_voltageMatrix_mulVec :
    rvWitness.voltageMatrix *ᵥ ![1 / 2 - I, -3 / 2 - 2 * I, 1] =
      (1 + 3 * I) • ![1 / 2 - I, -3 / 2 - 2 * I, 1] := by
  funext a
  fin_cases a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Params.voltageMatrix, Params.Bf,
      Params.Zg_eq, Params.Zv, rvWitness] <;>
    apply Complex.ext <;> simp <;> norm_num

/-- **`Z_v = 0` is needed**: with full feed-forward, a nonnegative virtual resistance and
positive `C_f, L_g, R_g, K_pv, K_iv`, the voltage level need not be stable (witness `R_v = 1`). -/
@[tmio M, powerlib_domain] theorem not_forall_spectrallyStable_voltageMatrix_of_virtualResistance :
    ¬ ∀ p : Params, p.kff = 1 → 0 ≤ p.Rv → p.Xv = 0 → 0 < p.Cf → 0 < p.Lg → 0 < p.Rg →
      0 < p.Kpv → 0 < p.Kiv → Linear.SpectrallyStable (realify p.voltageMatrix) := by
  intro h
  refine SingularPerturbation.not_spectrallyStable_realify (w := ![1 / 2 - I, -3 / 2 - 2 * I, 1])
    (fun h0 => by simpa using congrFun h0 2) rvWitness_voltageMatrix_mulVec (by simp)
    (h rvWitness ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;> norm_num [rvWitness]

/-- With `R_v = 1` the boundary layer of `rvWitness.currentScaled μ` is unstable for every
sufficiently small `μ > 0`. -/
@[tmio M, powerlib_domain] theorem rvWitness_eventually_not_spectrallyStable :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ δ,
      ¬ Linear.SpectrallyStable ((rvWitness.currentScaled μ).fastBlock δ) := by
  have hZt : rvWitness.Zt ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [Params.Zt, Params.Zg_eq, Params.Zv, rvWitness] at this
    norm_num at this
  refine rvWitness.eventually_not_spectrallyStable_fastBlock_of_voltage (by norm_num [rvWitness])
    (by norm_num [rvWitness]) (by norm_num [rvWitness]) (by norm_num [rvWitness])
    (by norm_num [rvWitness]) hZt (lam := 1 + 3 * I) (by simp)
    (fun h0 => by simpa using congrFun h0 2) rvWitness_voltageMatrix_mulVec

/-! ## Connection conclusions -/

/-- The full model with its current loop accelerated by `μ⁻¹`, at the selected point of `m`. -/
def Model.currentScaled (m : Model) (μ : ℝ) : Model := ⟨m.p.currentScaled μ, m.δ, m.Qf⟩

/-- **Stability transfer from the Routh–Hurwitz inequalities (connection).** For every
feed-forward gain, decoupling gain and virtual impedance: with a stable current loop
(`L_f, K_pc + R_f, K_ic > 0`), `C_f, L_g ≠ 0`, the three Routh–Hurwitz inequalities of the voltage
level (`Params.spectrallyStable_voltageMatrix_iff_routh`; they force `K_iv ≠ 0`, `Z_t ≠ 0`), at a
balanced quasi-steady point with a Hurwitz reduced Jacobian: there is `μ* > 0` such that for
every current-loop time scale `μ ∈ (0, μ*)` there is `ε*(μ) > 0` with the time-scaled model
`(currentScaled μ).timeScaled ε` locally exponentially stable for every `ε ∈ (0, ε*(μ))`. The
boundary-layer hypothesis of `exists_epsStar_mem_den_LES` is discharged by
`Params.exists_muStar_spectrallyStable_fastBlock_of_routh`. -/
@[tmio TM, powerlib_domain] theorem exists_muStar_epsStar_mem_den_LES_of_routh (m : Model)
    (hLf : 0 < m.p.Lf) (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKpc : 0 < m.p.Kpc + m.p.Rf)
    (hKic : 0 < m.p.Kic) (h2 : 0 < m.p.voltageA2.re)
    (h1 : 0 < m.p.voltageA2.re * (m.p.voltageA1.re * m.p.voltageA2.re +
      m.p.voltageA1.im * m.p.voltageA2.im - m.p.voltageA0.re) - m.p.voltageA1.im ^ 2)
    (h0 : 0 < Criteria.complexCubicDet m.p.voltageA2 m.p.voltageA1 m.p.voltageA0)
    (hM : m.p.M ≠ 0) (hωq : m.p.ωq ≠ 0) (hP : m.p.Pq m.δ (m.p.emf m.Qf) = m.p.Pref)
    (hQ : m.p.Qq m.δ (m.p.emf m.Qf) = m.Qf)
    (hR : LinearSystems.IsHurwitz (m.p.reducedJacobian m.δ m.Qf)) :
    connection% (∃ μs > 0, ∀ μ, 0 < μ → μ < μs → ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      (m.currentScaled μ).timeScaled ε ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨hKiv, hZt⟩ := m.p.kiv_ne_zero_and_zt_ne_zero_of_spectrallyStable hCf hLg
    ((m.p.spectrallyStable_voltageMatrix_iff_routh hCf hLg).mpr ⟨h2, h1, h0⟩)
  obtain ⟨μs, hμs, h⟩ := m.p.exists_muStar_spectrallyStable_fastBlock_of_routh hLf hKpc hKic
    hCf hLg h2 h1 h0
  refine ⟨μs, hμs, fun μ hμ hlt => ?_⟩
  exact (connection_proof% exists_epsStar_mem_den_LES) (m.currentScaled μ)
    (mul_ne_zero hμ.ne' hLf.ne') hCf hLg (div_ne_zero hKic.ne' hμ.ne') hKiv hZt hM hωq
    hP hQ (h μ hμ hlt m.δ) hR

/-- **Stability transfer from the gains (connection).** With partial or full line-current
feed-forward (`k_ff ≤ 1`), no virtual impedance, any decoupling gain and positive
`L_f, C_f, L_g, R_g`, `K_pc + R_f`, `K_ic, K_pv, K_iv`, at a balanced quasi-steady point with a
Hurwitz reduced Jacobian: there is `μ* > 0` such that for every current-loop time scale
`μ ∈ (0, μ*)` there is `ε*(μ) > 0` with the time-scaled model
`(currentScaled μ).timeScaled ε` locally exponentially stable for every `ε ∈ (0, ε*(μ))`. The
case of `exists_muStar_epsStar_mem_den_LES_of_routh` in which the Routh–Hurwitz inequalities of
the voltage level follow from the gains (`Params.spectrallyStable_voltageMatrix_of_kff_le_one`). -/
@[tmio TM, powerlib_domain] theorem exists_muStar_epsStar_mem_den_LES (m : Model)
    (hLf : 0 < m.p.Lf) (hCf : 0 < m.p.Cf) (hLg : 0 < m.p.Lg) (hRg : 0 < m.p.Rg)
    (hKpc : 0 < m.p.Kpc + m.p.Rf) (hKic : 0 < m.p.Kic) (hKpv : 0 < m.p.Kpv)
    (hKiv : 0 < m.p.Kiv) (hkff : m.p.kff ≤ 1) (hZv : m.p.Zv = 0)
    (hM : m.p.M ≠ 0) (hωq : m.p.ωq ≠ 0) (hP : m.p.Pq m.δ (m.p.emf m.Qf) = m.p.Pref)
    (hQ : m.p.Qq m.δ (m.p.emf m.Qf) = m.Qf)
    (hR : LinearSystems.IsHurwitz (m.p.reducedJacobian m.δ m.Qf)) :
    connection% (∃ μs > 0, ∀ μ, 0 < μ → μ < μs → ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      (m.currentScaled μ).timeScaled ε ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨h2, h1, h0⟩ := (m.p.spectrallyStable_voltageMatrix_iff_routh hCf.ne' hLg.ne').mp
    (m.p.spectrallyStable_voltageMatrix_of_kff_le_one hZv hkff hCf hLg hRg hKpv hKiv)
  exact (connection_proof% exists_muStar_epsStar_mem_den_LES_of_routh) m hLf hCf.ne' hLg.ne'
    hKpc hKic h2 h1 h0 hM hωq hP hQ hR

/-- **Reading the reduced Q–V droop model, from the gains (connection).** With `k_ff ≤ 1`,
`Z_v = 0` and positive `L_f, C_f, L_g, R_g`, `K_pc + R_f`, `K_ic, K_pv, K_iv`, if the reduced Q–V
droop model `Params.qvDroop` is locally exponentially stable at the selected point
(`QVDroop.family`), then
for every fast enough current loop (`μ ∈ (0, μ*)`) the time-scaled full model
`(currentScaled μ).timeScaled ε` is locally exponentially stable for every `ε ∈ (0, ε*(μ))`
(`exists_epsStar_mem_den_LES_of_qvDroop` with its boundary-layer hypothesis discharged by
`Params.exists_muStar_spectrallyStable_fastBlock_of_gains`; scaffold
`theorem/GridTiedConverter/GFM/FullModel/FullModelTimeScale.agda`). -/
@[tmio TM, powerlib_domain] theorem exists_muStar_epsStar_mem_den_LES_of_qvDroop (m : Model)
    (hLf : 0 < m.p.Lf) (hCf : 0 < m.p.Cf) (hLg : 0 < m.p.Lg) (hRg : 0 < m.p.Rg)
    (hKpc : 0 < m.p.Kpc + m.p.Rf) (hKic : 0 < m.p.Kic) (hKpv : 0 < m.p.Kpv)
    (hKiv : 0 < m.p.Kiv) (hkff : m.p.kff ≤ 1) (hZv : m.p.Zv = 0)
    (hM : m.p.M ≠ 0) (hωq : m.p.ωq ≠ 0)
    (hred : (⟨m.p.qvDroop, m.δ, m.Qf⟩ : QVDroop.Model) ∈
      QVDroop.family.den (.flow .locallyExponentiallyStable)) :
    connection% (∃ μs > 0, ∀ μ, 0 < μ → μ < μs → ∃ εs > 0, ∀ ε, 0 < ε → ε < εs →
      (m.currentScaled μ).timeScaled ε ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨μs, hμs, h⟩ := m.p.exists_muStar_spectrallyStable_fastBlock_of_gains hLf hCf hLg hRg
    hKpc hKic hKpv hKiv hkff hZv
  have hZg : m.p.Zg ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [Params.Zg_eq] at this
    simp at this
    linarith
  refine ⟨μs, hμs, fun μ hμ hlt => ?_⟩
  exact (connection_proof% exists_epsStar_mem_den_LES_of_qvDroop) (m.currentScaled μ)
    (mul_ne_zero hμ.ne' hLf.ne') hCf.ne' hLg.ne' (div_ne_zero hKic.ne' hμ.ne') hKiv.ne' hZv hZg
    hM hωq hred (h μ hμ hlt m.δ)

end powerlib.GFM.FullModel
