import theorem.GridTiedConverter.GFM.Discrete.LinearPort
import theorem.Numerics.EulerOutputs
import theorem.Numerics.SchurStable

/-! # Linearized grid-forming port models: explicit Euler with an output that sees the step

The linearized grid-forming port plants of
`theorem/GridTiedConverter/GFM/Discrete/LinearPort.lean` (set-point port, frequency output)
discretized by explicit Euler, `x⁺ = x + h (A x + B u)`, with the output read at a fraction of the
step (`Numerics.eulerOutputSystem`): averaged, `C (x + x⁺)/2`, or at the end of the step, `C x⁺`.
Unlike the Euler output `C x` (never passive), these outputs see the input of the step, and the
discretization is passive under conditions on the step. Two-state swing, averaged output: passive
exactly when `K h ≤ D` and `4 M − 2 D h + K h² ≥ 0`, with the storage
`½ K (Δδ + h Δω/2)² + ½ M' Δω²`, `M' = M − D h/2 + K h²/4`; end-of-step output: passive exactly
when `3 K h ≤ 2 D` and `4 M − 2 D h + K h² ≥ 0`, with the storage
`½ K (Δδ + h Δω)² + ½ (M − K h²/2) Δω²`. The refutations are a discrete periodic input (the
damping conditions) and a real mode of `I + h A` with a multiplier `r ≤ −1` driven by `r^k U`
(the condition `4 M − 2 D h + K h² ≥ 0`). By the Jury criterion (not formalized here) the strict
conditions `4 M − 2 D h + K h² > 0`, `K h < D` are the Schur stability of `I + h A`: the study's
conditions with `ρ(I + h A) < 1` are the interiors of these regions, and on their boundary the
averaged output is lossless or the mode `z = −1` is hidden. Three-state VSM + filter, with
`Δ = (2 − h ω_c)(4 M − 2 D h) − K h³ ω_c` (`−M` times the characteristic polynomial of `I + h A`
at `z = −1`): averaged output passive exactly when `h ω_c < 2`, `K (1 + h ω_c) ≤ D ω_c` and
`Δ ≥ 0`, with the storage `½ (K (Δδ + h Δω/2)² + (ε ξ − K h Δω)²/(2 K ε) + Δ Δω²/(4 ε))`,
`ξ = ΔP_f − K Δδ`, `ε = 2 − h ω_c`; end-of-step output passive exactly when `h ω_c < 2`,
`K (2 + 3 h ω_c) ≤ 2 D ω_c` and `Δ ≥ 0`, with the storage
`½ (K (Δδ + h Δω)² + (M − K h²/2) Δω² + ξ²/K)`. The refutations are a discrete periodic input at
a low frequency (the damping conditions) and real modes of `I + h A` with multipliers `r < −1`
(just below `σ = −ω_c` when `h ω_c ≥ 2`, just below `σ = −2/h` when `Δ < 0`). A Schur stable
`I + h A` has `K > 0`, `h ω_c < 2` and `Δ > 0` (the signs of its characteristic cubic at `1`,
`1 − h ω_c` and `−1`, `Numerics.SchurStable.cubic_pos`, `Numerics.SchurStable.cubic_neg`), so the
study's sufficient condition — Schur stability with `K (1 + h ω_c) ≤ D ω_c` — holds; it is not
necessary: on `Δ = 0` the step matrix has the eigenvalue `−1` and the discretization is passive.
Scaffold: `theorem/Numerics/EulerPorts.agda`.

Model boundary.
* The plants of `theorem/GridTiedConverter/GFM/Discrete/LinearPort.lean`: the two-state swing
  `SwingPort.Model.plant` (state `(Δδ, Δω)`, `M > 0`, `D ≥ 0`, synchronizing coefficient
  `K = A cos(δ* − α)`, here `K ≥ 0`) and the three-state VSM + filter `FilterPort.plant` (state
  `(Δδ, Δω, ΔP_f)`, `M, ω_c > 0`, any `D` and `K = K₀ cos δ*`); export-positive power, input the
  set-point deviation, output the frequency deviation, no feedthrough; linearization about the
  selected angle.
* Discretization (I): over `Numerics.EulerStep` (a model and a step `h > 0`), the explicit Euler
  state update with the input held over the step, the output `C (x + ν (x⁺ − x))` with
  `ν = 1/2` (averaged) or `ν = 1` (end of step), step length `h`, exact arithmetic, fixed step.
  The three-state statements ask `M, ω_c, K > 0` (any `D`); Schur stability of `I + h A` is
  `Numerics.SchurStable` (every root of `det(z I − (I + h A))` in the open unit disk).
  Excluded: other output fractions, step-size control, delays, PWM, inner loops, PLL, line
  dynamics.

Source: work-sync GFM study note t9 (scratchpad `gfm/t9-discrete/REPORT-coord.md`, (b): step-aware
outputs; script `s3_step_aware_output.py`, closed forms of `Re G_d` on the unit circle: averaged
two-state `4 h² v² (D − K h)`, end two-state `2 h v² ((4 M − 2 D h + K h²) v² + h (2 D − 3 K h))`,
averaged three-state with the low-frequency coefficient `h² ω_c (D ω_c − K (1 + h ω_c))`; the
three-state storages, the end-of-step three-state condition and the exact regions were derived
for this module, SymPy discovery evidence only);
`theorem/Numerics/SchurStable.lean` (`Numerics.SchurStable`, `Numerics.SchurStable.cubic_pos`,
`Numerics.SchurStable.cubic_neg`, `Numerics.not_schurStable_of_det_eq_zero`);
`theorem/Numerics/EulerOutputs.lean` (`Numerics.eulerOutputSystem_passiveWith_of`,
`Numerics.eulerOutputSystem_not_passive_of_phasor`,
`Numerics.eulerOutputSystem_not_passive_of_geometric`), `theorem/Numerics/PeriodicInput.lean`
(`Numerics.exists_periodic_frequency`); Brogliato, Lozano, Maschke and Egeland, *Dissipative
Systems Analysis and Control* (2007), §3 (positive real discrete-time transfer functions); Jury,
*Theory and Application of the z-Transform Method* (1964) (the stability test).

Results.
* `SwingPort.plant_phasor` (the swing plant's phasor at a complex frequency, output phasor
  `Δω = 1`).
* `FilterPort.eulerStep_charDet` (the characteristic polynomial of the filter's Euler step matrix
  `I + h A` on the real axis, computed from the plant), `FilterPort.not_schurStable_of_boundary`
  (`Δ = 0`: `z = −1` is a characteristic root, `I + h A` is not Schur stable).

Family and connection conclusions.
* Two-state swing, averaged output: `SwingPort.linearAverageFamily`,
  `SwingPort.linearAverage_mem_den_passive` (`K h ≤ D`, `4 M − 2 D h + K h² ≥ 0`: passive with
  the storage above), `SwingPort.linearAverage_not_mem_den_passive_of_damping` (`K h > D`: at any
  closing frequency the mean supplied power is `(1 + cos θ)(D − K h)/2 < 0`),
  `SwingPort.linearAverage_not_mem_den_passive_of_mode` (`4 M − 2 D h + K h² < 0`: a real mode
  with multiplier `r < −1` draws energy at every step),
  `SwingPort.linearAverage_mem_den_passive_iff` (`K ≥ 0`: passive iff `K h ≤ D` and
  `4 M − 2 D h + K h² ≥ 0`).
* Two-state swing, end-of-step output: `SwingPort.linearEndFamily`,
  `SwingPort.linearEnd_mem_den_passive` (`3 K h ≤ 2 D`, `4 M − 2 D h + K h² ≥ 0`),
  `SwingPort.linearEnd_not_mem_den_passive_of_damping` (`3 K h > 2 D`: a low closing frequency),
  `SwingPort.linearEnd_not_mem_den_passive_of_mode` (`4 M − 2 D h + K h² < 0`: the two-cycle of
  the multiplier `−1`), `SwingPort.linearEnd_mem_den_passive_iff` (`K ≥ 0`: passive iff
  `3 K h ≤ 2 D` and `4 M − 2 D h + K h² ≥ 0`).
* Three-state VSM + filter, averaged output: `FilterPort.linearAverageFamily`,
  `FilterPort.linearAverage_mem_den_passive` (`h ω_c < 2`, `K (1 + h ω_c) ≤ D ω_c`, `Δ ≥ 0`:
  passive with the storage above), `FilterPort.linearAverage_not_mem_den_passive`
  (`K (1 + h ω_c) > D ω_c`: not passive, at a low closing frequency),
  `FilterPort.linearAverage_not_mem_den_passive_of_mode` (`h ω_c ≥ 2` or `Δ < 0`: a real mode
  with multiplier `r < −1` draws energy at every step),
  `FilterPort.linearAverage_mem_den_passive_iff` (within `M, ω_c, K > 0`: passive iff
  `h ω_c < 2`, `K (1 + h ω_c) ≤ D ω_c` and `Δ ≥ 0`),
  `FilterPort.linearAverage_mem_den_passive_of_schurStable` (a Schur stable `I + h A` and
  `K (1 + h ω_c) ≤ D ω_c`: passive — the study's claim).
* Three-state VSM + filter, end-of-step output: `FilterPort.linearEndFamily`,
  `FilterPort.linearEnd_mem_den_passive` (`h ω_c < 2`, `K (2 + 3 h ω_c) ≤ 2 D ω_c`, `Δ ≥ 0`),
  `FilterPort.linearEnd_not_mem_den_passive_of_damping` (`K (2 + 3 h ω_c) > 2 D ω_c`: a low
  closing frequency), `FilterPort.linearEnd_not_mem_den_passive_of_mode` (`h ω_c ≥ 2` or
  `Δ < 0`), `FilterPort.linearEnd_mem_den_passive_iff` (within `M, ω_c, K > 0`: passive iff
  `h ω_c < 2`, `K (2 + 3 h ω_c) ≤ 2 D ω_c` and `Δ ≥ 0`),
  `FilterPort.linearEnd_mem_den_passive_of_schurStable` (a Schur stable `I + h A` and
  `K (2 + 3 h ω_c) ≤ 2 D ω_c`: passive).
-/

noncomputable section

namespace powerlib.GFM

open powerlib.Dynamics (State)
open Matrix Filter Topology

/-- The frequency data of a closing frequency `θ` (`sin θ ≠ 0`): with `σ = (cos θ − 1)/h`,
`ω = sin θ/h` (`h s = e^{iθ} − 1`), the angle phasor `1/s = p + i q` is
`p = −h/2`, `q = −h (1 + cos θ)/(2 sin θ)`. -/
@[tmio T, powerlib_foundation] private theorem euler_frequency {h c s : ℝ} (hh : h ≠ 0)
    (hs : s ≠ 0) (hsc : s ^ 2 + c ^ 2 = 1) :
    (c - 1) / h * (-(h / 2)) - s / h * (-(h * (1 + c) / (2 * s))) = 1 ∧
      s / h * (-(h / 2)) + (c - 1) / h * (-(h * (1 + c) / (2 * s))) = 0 := by
  constructor
  · field_simp
    ring
  · have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
    field_simp
    linear_combination -hs2

namespace SwingPort

/-- **The phasor of the swing plant at a complex frequency** `s = σ + i ω`: the output phasor
`Δω = 1`, the angle `1/s = p + i q` (in real form `h1`, `h2`), the input `M s + D + K/s` solve
`A X + B U = s X`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem plant_phasor (m : Model) {σ ω p q : ℝ}
    (h1 : σ * p - ω * q = 1) (h2 : ω * p + σ * q = 0) :
    m.plant.A *ᵥ ![p, 1] + m.plant.B *ᵥ ![m.p.M * σ + m.p.D + m.K * p] =
        σ • ![p, 1] - ω • ![q, 0] ∧
      m.plant.A *ᵥ ![q, 0] + m.plant.B *ᵥ ![m.p.M * ω + m.K * q] =
        ω • ![p, 1] + σ • ![q, 0] := by
  have hM := m.p.M_pos.ne'
  constructor <;> ext i <;> fin_cases i <;> simp [Model.plant]
  · linear_combination -h1
  · field_simp
    ring
  · linear_combination -h2
  · field_simp
    ring

/-- The explicit Euler discretization family of the linearized swing port with the averaged
output `C (x + x⁺)/2`. -/
def linearAverageFamily : Family LinearStep LinearRequirement 2 1 :=
  Numerics.eulerOutputPortFamily linearFamily Model.plant Numerics.EulerStep.design
    Numerics.EulerStep.h (1 / 2)

/-- The step update of the swing plant: `A x + B u = (x₁, (u − K x₀ − D x₁)/M)`. -/
@[tmio M, powerlib_domain] private theorem plant_field (m : Model) (x : Fin 2 → ℝ)
    (u : Fin 1 → ℝ) :
    m.plant.A *ᵥ x + m.plant.B *ᵥ u = ![x 1, (u 0 - m.K * x 0 - m.p.D * x 1) / m.p.M] := by
  ext i
  fin_cases i <;> simp [Model.plant, dotProduct, Fin.sum_univ_two]
  ring

/-- **The averaged-output Euler discretizations of the linearized swing port are passive when
`K h ≤ D` and `4 M − 2 D h + K h² ≥ 0`** (with `K ≥ 0`), with the storage
`½ K (Δδ + h Δω/2)² + ½ M' Δω²`, `M' = M − D h/2 + K h²/4`: over a step it changes by
`h u ȳ − h (D − K h) ((D h − 2 M) Δω + K h Δδ − h u)²/(4 M²)`
(`Numerics.eulerOutputSystem_passiveWith_of`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_mem_den_passive (m : Model) (hK : 0 ≤ m.K)
    (h : ℝ) (hh : 0 < h) (hKh : m.K * h ≤ m.p.D)
    (hM : 0 ≤ 4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearAverageFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change (Numerics.eulerOutputSystem m.plant h (1 / 2)).Passive
  have hM0 := m.p.M_pos
  refine ⟨_, Numerics.eulerOutputSystem_passiveWith_of
    (P := !![m.K, m.K * h / 2; m.K * h / 2, m.p.M - m.p.D * h / 2 + m.K * h ^ 2 / 2])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp) (fun x => ?_) hh.le (fun x u => ?_)⟩
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    have e : x 0 * (m.K * x 0 + m.K * h / 2 * x 1) + x 1 * (m.K * h / 2 * x 0 +
        (m.p.M - m.p.D * h / 2 + m.K * h ^ 2 / 2) * x 1) =
        m.K * (x 0 + h / 2 * x 1) ^ 2 + (4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) / 4 *
          x 1 ^ 2 := by ring
    rw [e]
    have := mul_nonneg hK (sq_nonneg (x 0 + h / 2 * x 1))
    have := mul_nonneg (div_nonneg hM zero_le_four) (sq_nonneg (x 1))
    linarith
  · rw [plant_field]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Model.plant,
      Matrix.zero_apply]
    set v := (u 0 - m.K * x 0 - m.p.D * x 1) / m.p.M with hv
    have hvM : v * m.p.M = u 0 - m.K * x 0 - m.p.D * x 1 := by
      rw [hv]; field_simp
    have key : u 0 * (x 1 + 1 / 2 * h * v) - ((x 0 + h / 2 * x 1) * (m.K * x 1 +
        m.K * h / 2 * v) + (x 1 + h / 2 * v) * (m.K * h / 2 * x 1 +
        (m.p.M - m.p.D * h / 2 + m.K * h ^ 2 / 2) * v)) =
        (m.p.D - m.K * h) / 4 * (h * v + 2 * x 1) ^ 2 := by
      linear_combination (-(x 1 + h / 2 * v)) * hvM
    nlinarith [mul_nonneg (div_nonneg (sub_nonneg.mpr hKh) zero_le_four)
      (sq_nonneg (h * v + 2 * x 1))]

/-- **No averaged-output Euler discretization of the linearized swing port with `K h > D` is
passive**, whatever the storage: at any closing frequency `θ` (`cos(N θ) = 1`, `sin θ ≠ 0`) the
plant's phasor at `s = (e^{iθ} − 1)/h` with the output phasor `Δω = 1` has the mean supplied
power `(1 + cos θ)(D − K h)/2 < 0` (`Numerics.eulerOutputSystem_not_passive_of_phasor`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_not_mem_den_passive_of_damping (m : Model)
    (h : ℝ) (hh : 0 < h) (hKh : m.p.D < m.K * h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearAverageFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem m.plant h (1 / 2)).Passive
  obtain ⟨θ, N, hN, hper, hsin, -⟩ :=
    Numerics.exists_periodic_frequency (f := fun _ => (-1 : ℝ)) continuousAt_const (by norm_num)
  set c := Real.cos θ with hcdef
  set s := Real.sin θ with hsdef
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hc : 0 < 1 + c := by
    by_contra hle
    have hc1 : c = -1 := le_antisymm (by linarith) (Real.neg_one_le_cos θ)
    rw [hc1] at hsc
    have : s ^ 2 = 0 := by nlinarith
    exact hsin.ne' (pow_eq_zero_iff two_ne_zero |>.mp this)
  obtain ⟨h1, h2⟩ := euler_frequency hh.ne' hsin.ne' hsc
  obtain ⟨hr, hi⟩ := plant_phasor m h1 h2
  refine Numerics.eulerOutputSystem_not_passive_of_phasor m.plant hh (1 / 2) hN hper hsin.ne'
    (σ := (c - 1) / h) (ω := s / h) (by rw [hcdef]; field_simp) (by rw [hsdef]; field_simp)
    hr hi ?_
  simp [Model.plant, dotProduct]
  have hM := m.p.M_pos.ne'
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  have e : (m.p.M * ((c - 1) / h) + m.p.D + m.K * (-(h / 2))) * (1 + 2⁻¹ * (c - 1)) +
      (m.p.M * (s / h) + m.K * (-(h * (1 + c) / (2 * s)))) * (2⁻¹ * s) =
      (1 + c) * (m.p.D - m.K * h) / 2 := by
    field_simp
    linear_combination (2 * m.p.M) * hs2
  nlinarith [mul_pos hc (sub_pos.mpr hKh)]

/-- A real mode of the swing plant at `σ` (`σ p = 1`): the angle `p`, the frequency `1`, the input
`M σ + D + K p` solve `A X + B U = σ X`. -/
@[tmio M, powerlib_domain] private theorem plant_mode (m : Model) {σ p : ℝ} (hp : σ * p = 1) :
    m.plant.A *ᵥ ![p, 1] + m.plant.B *ᵥ ![m.p.M * σ + m.p.D + m.K * p] = σ • ![p, 1] := by
  have h := (plant_phasor m (ω := 0) (q := 0) (by simpa using hp) (by simp)).1
  simpa using h

/-- **No averaged-output Euler discretization of the linearized swing port with
`4 M − 2 D h + K h² < 0` is passive**, whatever the storage: then `M σ² + D σ + K < 0` at
`σ = −2/h`, so at some `σ < −2/h` (a multiplier `r = 1 + h σ < −1` of `I + h A`), and the real
mode at `σ` driven by `r^k U` draws `(M σ² + D σ + K)(2 + h σ)/(2 σ) < 0` per step and unit
`|r|^{2k}` (`Numerics.eulerOutputSystem_not_passive_of_geometric`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_not_mem_den_passive_of_mode (m : Model)
    (h : ℝ) (hh : 0 < h) (hM : 4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2 < 0) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearAverageFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem m.plant h (1 / 2)).Passive
  have hq0 : m.p.M * (-2 / h) ^ 2 + m.p.D * (-2 / h) + m.K < 0 := by
    have e : m.p.M * (-2 / h) ^ 2 + m.p.D * (-2 / h) + m.K =
        (4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) / h ^ 2 := by
      field_simp
      ring
    rw [e]
    exact div_neg_of_neg_of_pos hM (by positivity)
  have hcont : ContinuousAt (fun σ => m.p.M * σ ^ 2 + m.p.D * σ + m.K) (-2 / h) := by fun_prop
  have hev : ∀ᶠ σ in 𝓝[<] (-2 / h), m.p.M * σ ^ 2 + m.p.D * σ + m.K < 0 ∧ σ < -2 / h :=
    ((hcont.tendsto.eventually_lt_const hq0).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin.mono fun _ hx => hx)
  obtain ⟨σ, hqσ, hσ⟩ := hev.exists
  have h2h : (0 : ℝ) < 2 / h := by positivity
  have hσ0 : σ < 0 := by
    have : -2 / h = -(2 / h) := neg_div h 2
    linarith
  have hσne := hσ0.ne
  have hr : 1 + h * σ < -1 := by
    nlinarith [(lt_div_iff₀ hh).mp hσ]
  refine Numerics.eulerOutputSystem_not_passive_of_geometric m.plant hh (1 / 2)
    (r := 1 + h * σ) (σ := σ) (by rw [abs_of_neg (by linarith)]; linarith) (by ring)
    (plant_mode m (p := σ⁻¹) (mul_inv_cancel₀ hσne)) ?_
  simp [Model.plant, dotProduct]
  have e : (m.p.M * σ + m.p.D + m.K * σ⁻¹) * (1 + 2⁻¹ * (h * σ)) =
      (m.p.M * σ ^ 2 + m.p.D * σ + m.K) * ((2 + h * σ) / (2 * σ)) := by
    field_simp
  rw [e]
  exact mul_neg_of_neg_of_pos hqσ (div_pos_of_neg_of_neg (by linarith) (by linarith))

/-- **Passivity of the averaged-output Euler discretizations of the linearized swing port**: with
`K ≥ 0` and a step `h > 0`, a discretization is passive exactly when `K h ≤ D` and
`4 M − 2 D h + K h² ≥ 0` (`linearAverage_mem_den_passive`,
`linearAverage_not_mem_den_passive_of_damping`, `linearAverage_not_mem_den_passive_of_mode`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_mem_den_passive_iff (m : Model) (hK : 0 ≤ m.K)
    (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearAverageFamily.den .passive ↔
      m.K * h ≤ m.p.D ∧ 0 ≤ 4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) := by
  have hp := linearAverage_mem_den_passive m hK h hh
  have hd := linearAverage_not_mem_den_passive_of_damping m h hh
  have hm := linearAverage_not_mem_den_passive_of_mode m h hh
  unfold powerlib.TMIO.Statement at hp hd hm ⊢
  exact ⟨fun hy => ⟨not_lt.mp fun hlt => hd hlt hy, not_lt.mp fun hlt => hm hlt hy⟩,
    fun ⟨h1, h2⟩ => hp h1 h2⟩

/-! ### The end-of-step output -/

/-- The explicit Euler discretization family of the linearized swing port with the end-of-step
output `C x⁺`. -/
def linearEndFamily : Family LinearStep LinearRequirement 2 1 :=
  Numerics.eulerOutputPortFamily linearFamily Model.plant Numerics.EulerStep.design
    Numerics.EulerStep.h 1

/-- **The end-of-step-output Euler discretizations of the linearized swing port are passive when
`3 K h ≤ 2 D` and `4 M − 2 D h + K h² ≥ 0`** (with `K ≥ 0`), with the storage
`½ K (Δδ + h Δω)² + ½ (M − K h²/2) Δω²`: the slack of the dissipation inequality is
`((2 D − 3 K h)/2) (Δω + h v/2)² + (h/8)(4 M − 2 D h + K h²) v²`, `v = (u − K Δδ − D Δω)/M`
(`Numerics.eulerOutputSystem_passiveWith_of`). -/
@[tmio TM, powerlib_domain] theorem linearEnd_mem_den_passive (m : Model) (hK : 0 ≤ m.K)
    (h : ℝ) (hh : 0 < h) (hKh : 3 * m.K * h ≤ 2 * m.p.D)
    (hM : 0 ≤ 4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearEndFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change (Numerics.eulerOutputSystem m.plant h 1).Passive
  have hM0 := m.p.M_pos
  have hMh : 0 ≤ m.p.M - m.K * h ^ 2 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hKh hh.le]
  refine ⟨_, Numerics.eulerOutputSystem_passiveWith_of
    (P := !![m.K, m.K * h; m.K * h, m.p.M + m.K * h ^ 2 / 2])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp) (fun x => ?_) hh.le (fun x u => ?_)⟩
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    have e : x 0 * (m.K * x 0 + m.K * h * x 1) + x 1 * (m.K * h * x 0 +
        (m.p.M + m.K * h ^ 2 / 2) * x 1) =
        m.K * (x 0 + h * x 1) ^ 2 + (m.p.M - m.K * h ^ 2 / 2) * x 1 ^ 2 := by ring
    rw [e]
    have := mul_nonneg hK (sq_nonneg (x 0 + h * x 1))
    have := mul_nonneg hMh (sq_nonneg (x 1))
    linarith
  · rw [plant_field]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Model.plant,
      Matrix.zero_apply]
    set v := (u 0 - m.K * x 0 - m.p.D * x 1) / m.p.M with hv
    have hvM : v * m.p.M = u 0 - m.K * x 0 - m.p.D * x 1 := by
      rw [hv]; field_simp
    have key : u 0 * (x 1 + 1 * h * v) - ((x 0 + h / 2 * x 1) * (m.K * x 1 +
        m.K * h * v) + (x 1 + h / 2 * v) * (m.K * h * x 1 + (m.p.M + m.K * h ^ 2 / 2) * v)) =
        (2 * m.p.D - 3 * m.K * h) / 2 * (x 1 + h * v / 2) ^ 2 +
          h / 8 * (4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) * v ^ 2 := by
      linear_combination (-(x 1 + h * v)) * hvM
    nlinarith [mul_nonneg (div_nonneg (by linarith : 0 ≤ 2 * m.p.D - 3 * m.K * h) zero_le_two)
      (sq_nonneg (x 1 + h * v / 2)), mul_nonneg (mul_nonneg (by positivity : 0 ≤ h / 8) hM)
      (sq_nonneg v)]

/-- **No end-of-step-output Euler discretization of the linearized swing port with
`3 K h > 2 D` is passive**, whatever the storage: at a closing frequency `θ` near zero the
plant's phasor with output phasor `Δω = 1` has the mean supplied power
`M (1 − cos θ)/h + D cos θ − K h (2 cos θ + 1)/2`, equal to `D − 3 K h/2 < 0` at `θ = 0`
(`Numerics.exists_periodic_frequency`, `Numerics.eulerOutputSystem_not_passive_of_phasor`). -/
@[tmio TM, powerlib_domain] theorem linearEnd_not_mem_den_passive_of_damping (m : Model)
    (h : ℝ) (hh : 0 < h) (hKh : 2 * m.p.D < 3 * m.K * h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearEndFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem m.plant h 1).Passive
  set f : ℝ → ℝ := fun θ => m.p.M * (1 - Real.cos θ) / h + m.p.D * Real.cos θ -
    m.K * h * (2 * Real.cos θ + 1) / 2 with hf
  have hf0 : f 0 < 0 := by
    simp only [hf, Real.cos_zero, sub_self, mul_zero, zero_div, zero_add, mul_one]
    linarith
  obtain ⟨θ, N, hN, hper, hsin, hθ⟩ :=
    Numerics.exists_periodic_frequency (f := f) (by fun_prop) hf0
  set c := Real.cos θ with hcdef
  set s := Real.sin θ with hsdef
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  obtain ⟨h1, h2⟩ := euler_frequency hh.ne' hsin.ne' hsc
  obtain ⟨hr, hi⟩ := plant_phasor m h1 h2
  refine Numerics.eulerOutputSystem_not_passive_of_phasor m.plant hh 1 hN hper hsin.ne'
    (σ := (c - 1) / h) (ω := s / h) (by rw [hcdef]; field_simp) (by rw [hsdef]; field_simp)
    hr hi ?_
  simp [Model.plant, dotProduct]
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  have e : (m.p.M * ((c - 1) / h) + m.p.D + m.K * (-(h / 2))) * (1 + (c - 1)) +
      (m.p.M * (s / h) + m.K * (-(h * (1 + c) / (2 * s)))) * s = f θ := by
    simp only [hf]
    field_simp
    linear_combination (2 * m.p.M) * hs2
  linarith

/-- **No end-of-step-output Euler discretization of the linearized swing port with
`4 M − 2 D h + K h² < 0` is passive**, whatever the storage: the real mode at `σ = −2/h`
(multiplier `−1`, a two-cycle) driven by `(−1)^k U` draws `(4 M − 2 D h + K h²)/(2 h) < 0` per
step (`Numerics.eulerOutputSystem_not_passive_of_geometric`). -/
@[tmio TM, powerlib_domain] theorem linearEnd_not_mem_den_passive_of_mode (m : Model) (h : ℝ)
    (hh : 0 < h) (hM : 4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2 < 0) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearEndFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem m.plant h 1).Passive
  refine Numerics.eulerOutputSystem_not_passive_of_geometric m.plant hh 1 (r := -1)
    (σ := -2 / h) (by simp) (by field_simp; ring)
    (plant_mode m (p := -(h / 2)) (by field_simp)) ?_
  simp [Model.plant, dotProduct]
  have e : -(m.p.M * (-2 / h)) - m.p.D - m.K * (-(h / 2)) =
      (4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) / (2 * h) := by
    field_simp
    ring
  nlinarith [div_neg_of_neg_of_pos hM (by positivity : (0 : ℝ) < 2 * h)]

/-- **Passivity of the end-of-step-output Euler discretizations of the linearized swing port**:
with `K ≥ 0` and a step `h > 0`, a discretization is passive exactly when `3 K h ≤ 2 D` and
`4 M − 2 D h + K h² ≥ 0`. -/
@[tmio TM, powerlib_domain] theorem linearEnd_mem_den_passive_iff (m : Model) (hK : 0 ≤ m.K)
    (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearEndFamily.den .passive ↔
      3 * m.K * h ≤ 2 * m.p.D ∧ 0 ≤ 4 * m.p.M - 2 * m.p.D * h + m.K * h ^ 2) := by
  have hp := linearEnd_mem_den_passive m hK h hh
  have hd := linearEnd_not_mem_den_passive_of_damping m h hh
  have hm := linearEnd_not_mem_den_passive_of_mode m h hh
  unfold powerlib.TMIO.Statement at hp hd hm ⊢
  exact ⟨fun hy => ⟨not_lt.mp fun hlt => hd hlt hy, not_lt.mp fun hlt => hm hlt hy⟩,
    fun ⟨h1, h2⟩ => hp h1 h2⟩

end SwingPort

namespace FilterPort

/-- The explicit Euler discretization family of the linearized VSM + filter port with the
averaged output `C (x + x⁺)/2`. -/
def linearAverageFamily : Family LinearStep Requirement 3 1 :=
  Numerics.eulerOutputPortFamily linearFamily plant Numerics.EulerStep.design
    Numerics.EulerStep.h (1 / 2)

/-- **No averaged-output Euler discretization of the linearized VSM + filter port with
`K (1 + h ω_c) > D ω_c` is passive** (with `M > 0`, `D ≥ 0`, `ω_c > 0`, `h > 0`), whatever the
storage. At a closing frequency `θ` the plant's phasor at `s = (e^{iθ} − 1)/h` with the output
phasor `Δω = 1` (`plant_phasor_complex`) has the mean supplied power
`(1 + cos θ)/2 · (D − ω_c K (h ω_c + 2 cos θ − 1)/|s + ω_c|²)`, continuous in `θ` and equal to
`D − K (1 + h ω_c)/ω_c < 0` at `θ = 0`; a frequency `θ = 2π/N` near zero keeps it negative
(`Numerics.exists_periodic_frequency`, `Numerics.eulerOutputSystem_not_passive_of_phasor`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_not_mem_den_passive (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (h : ℝ) (hh : 0 < h)
    (hKh : m.g.D * m.g.ωc < m.K * (1 + h * m.g.ωc)) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearAverageFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem (plant m) h (1 / 2)).Passive
  set E : ℝ → ℝ := fun θ => ((Real.cos θ - 1) / h + m.g.ωc) ^ 2 + (Real.sin θ / h) ^ 2
    with hE
  set f : ℝ → ℝ := fun θ => (1 + Real.cos θ) / 2 *
    (m.g.D - m.g.ωc * m.K * (h * m.g.ωc + 2 * Real.cos θ - 1) / E θ) with hf
  have hE0 : E 0 = m.g.ωc ^ 2 := by simp [hE]
  have hcont : ContinuousAt f 0 := by
    have hEc : ContinuousAt E 0 := by simp only [hE]; fun_prop
    exact (by fun_prop : ContinuousAt (fun θ => (1 + Real.cos θ) / 2) 0).mul
      (continuousAt_const.sub ((by fun_prop : ContinuousAt
        (fun θ => m.g.ωc * m.K * (h * m.g.ωc + 2 * Real.cos θ - 1)) 0).div hEc
        (by rw [hE0]; positivity)))
  have hf0 : f 0 < 0 := by
    simp only [hf, Real.cos_zero, hE0]
    have e : (1 + 1) / 2 * (m.g.D - m.g.ωc * m.K * (h * m.g.ωc + 2 * 1 - 1) / m.g.ωc ^ 2) =
        (m.g.D * m.g.ωc - m.K * (1 + h * m.g.ωc)) / m.g.ωc := by
      field_simp
      ring
    rw [e]
    exact div_neg_of_neg_of_pos (by linarith) hω
  obtain ⟨θ, N, hN, hper, hsin, hθ⟩ := Numerics.exists_periodic_frequency hcont hf0
  set c := Real.cos θ with hcdef
  set s := Real.sin θ with hsdef
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  set σ := (c - 1) / h with hσdef
  set ω := s / h with hωdef
  have hσ : h * σ = c - 1 := by rw [hσdef]; field_simp
  have hω' : h * ω = s := by rw [hωdef]; field_simp
  have hω0 : 0 < ω := div_pos hsin hh
  set Eθ := (σ + m.g.ωc) ^ 2 + ω ^ 2 with hEθdef
  have hEθ : 0 < Eθ := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hω0 2)
  have hEθE : E θ = Eθ := rfl
  set p : ℝ := -(h / 2)
  set q : ℝ := -(h * (1 + c) / (2 * s))
  obtain ⟨h1, h2⟩ := euler_frequency hh.ne' hsin.ne' hsc
  set a := m.g.ωc * m.K * (p * (σ + m.g.ωc) + q * ω) / Eθ
  set b := m.g.ωc * m.K * (q * (σ + m.g.ωc) - p * ω) / Eθ
  have h3 : (σ + m.g.ωc) * a - ω * b = m.g.ωc * m.K * p := by
    simp only [a, b]
    field_simp
    ring
  have h4 : ω * a + (σ + m.g.ωc) * b = m.g.ωc * m.K * q := by
    simp only [a, b]
    field_simp
    ring
  obtain ⟨hr, hi⟩ := plant_phasor_complex m hM.ne' h1 h2 h3 h4
  refine Numerics.eulerOutputSystem_not_passive_of_phasor (plant m) hh (1 / 2) hN hper
    hsin.ne' hσ hω' hr hi ?_
  simp [plant, dotProduct]
  have hqs : q * s = -(h * (1 + c) / 2) := by simp only [q]; field_simp
  have hqω : q * ω = -((1 + c) / 2) := by simp only [q, ω]; field_simp
  have hωs : ω * s = s ^ 2 / h := by simp only [ω]; field_simp
  have hMpart : σ * (1 + c) + ω * s = 0 := by
    rw [hωs, hs2]
    simp only [σ]
    field_simp
    ring
  have hbr : (p * (σ + m.g.ωc) + q * ω) * (1 + c) + (q * (σ + m.g.ωc) - p * ω) * s =
      -((1 + c) * (2 * c - 1 + h * m.g.ωc)) := by
    have e : (p * (σ + m.g.ωc) + q * ω) * (1 + c) + (q * (σ + m.g.ωc) - p * ω) * s =
        p * (σ + m.g.ωc) * (1 + c) + (q * ω) * (1 + c) + (q * s) * (σ + m.g.ωc) -
          p * (ω * s) := by ring
    rw [e, hqω, hqs, hωs]
    simp only [p]
    field_simp
    linear_combination (-(2 * (1 + c))) * hσ + hs2
  have hab : a * (1 + c) + b * s = -(m.g.ωc * m.K * ((1 + c) * (2 * c - 1 + h * m.g.ωc))) /
      Eθ := by
    have e : a * (1 + c) + b * s = m.g.ωc * m.K * ((p * (σ + m.g.ωc) + q * ω) * (1 + c) +
        (q * (σ + m.g.ωc) - p * ω) * s) / Eθ := by
      simp only [a, b]
      field_simp
    rw [e, hbr]
    ring
  have key : (m.g.M * σ + m.g.D + a) * (1 + 2⁻¹ * (c - 1)) + (m.g.M * ω + b) * (2⁻¹ * s) =
      f θ := by
    simp only [hf, hEθE]
    linear_combination (m.g.M / 2) * hMpart + (1 / 2) * hab
  linarith

/-- The step update of the filter plant:
`A x + B u = (x₁, (u − D x₁ − x₂)/M, ω_c (K x₀ − x₂))`. -/
@[tmio M, powerlib_domain] private theorem plant_field (m : VSMLPF.Model) (x : Fin 3 → ℝ)
    (u : Fin 1 → ℝ) :
    (plant m).A *ᵥ x + (plant m).B *ᵥ u =
      ![x 1, (u 0 - m.g.D * x 1 - x 2) / m.g.M, m.g.ωc * (m.K * x 0 - x 2)] := by
  have hK : m.g.K0 * Real.cos m.δ = m.K := rfl
  ext i
  fin_cases i <;> simp [plant, VSMLPF.jacobian, hK, dotProduct, Fin.sum_univ_three]
  · ring
  · ring

/-- **The averaged-output Euler discretizations of the linearized VSM + filter port are passive
when `h ω_c < 2`, `K (1 + h ω_c) ≤ D ω_c` and `Δ = (2 − h ω_c)(4 M − 2 D h) − K h³ ω_c ≥ 0`**
(with `M, ω_c, K > 0`, `h > 0`), with the storage `½ xᵀ P x`,
`xᵀ P x = K (Δδ + h Δω/2)² + (ε ξ − K h Δω)²/(2 K ε) + Δ Δω²/(4 ε)`, `ξ = ΔP_f − K Δδ`,
`ε = 2 − h ω_c`. Over a step it changes by `h (u ȳ − R)`, `ȳ` the averaged output, with
`R = (ω_c ξ̄ + K Δω̄)²/(K ω_c) + ((D ω_c − K (1 + h ω_c))/ω_c) Δω̄² ≥ 0` at the midpoint state
`x̄ = (x + x⁺)/2` (`Numerics.eulerOutputSystem_passiveWith_of`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_mem_den_passive (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h)
    (ht : h * m.g.ωc < 2) (hKh : m.K * (1 + h * m.g.ωc) ≤ m.g.D * m.g.ωc)
    (hΔ : 0 ≤ (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearAverageFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change (Numerics.eulerOutputSystem (plant m) h (1 / 2)).Passive
  have hε : 0 < 2 - h * m.g.ωc := by linarith
  have hKne := hK.ne'
  refine ⟨_, Numerics.eulerOutputSystem_passiveWith_of
    (P := !![m.K * (4 - h * m.g.ωc) / 2, m.K * h, -((2 - h * m.g.ωc) / 2);
      m.K * h, m.g.M - m.g.D * h / 2 + m.K * h ^ 2 / 2, -(h / 2);
      -((2 - h * m.g.ωc) / 2), -(h / 2), (2 - h * m.g.ωc) / (2 * m.K)])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp) (fun x => ?_) hh.le (fun x u => ?_)⟩
  · have e : x ⬝ᵥ (!![m.K * (4 - h * m.g.ωc) / 2, m.K * h, -((2 - h * m.g.ωc) / 2);
        m.K * h, m.g.M - m.g.D * h / 2 + m.K * h ^ 2 / 2, -(h / 2);
        -((2 - h * m.g.ωc) / 2), -(h / 2), (2 - h * m.g.ωc) / (2 * m.K)] *ᵥ x) =
        m.K * (x 0 + h / 2 * x 1) ^ 2 +
          ((2 - h * m.g.ωc) * (x 2 - m.K * x 0) - m.K * h * x 1) ^ 2 /
            (2 * m.K * (2 - h * m.g.ωc)) +
          ((2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) /
            (4 * (2 - h * m.g.ωc)) * x 1 ^ 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      field_simp
      ring
    rw [e]
    have := mul_nonneg hK.le (sq_nonneg (x 0 + h / 2 * x 1))
    have := div_nonneg (sq_nonneg ((2 - h * m.g.ωc) * (x 2 - m.K * x 0) - m.K * h * x 1))
      (by positivity : (0 : ℝ) ≤ 2 * m.K * (2 - h * m.g.ωc))
    have := mul_nonneg (div_nonneg hΔ (by positivity : (0 : ℝ) ≤ 4 * (2 - h * m.g.ωc)))
      (sq_nonneg (x 1))
    linarith
  · rw [plant_field, ← sub_nonneg]
    set v := (u 0 - m.g.D * x 1 - x 2) / m.g.M with hv
    set y1 := x 1 + h / 2 * v
    set ξ := x 2 + h / 2 * (m.g.ωc * (m.K * x 0 - x 2)) - m.K * (x 0 + h / 2 * x 1)
    have hR : 0 ≤ (m.g.ωc * ξ + m.K * y1) ^ 2 / (m.K * m.g.ωc) +
        (m.g.D * m.g.ωc - m.K * (1 + h * m.g.ωc)) / m.g.ωc * y1 ^ 2 := by
      have := div_nonneg (sq_nonneg (m.g.ωc * ξ + m.K * y1)) (by positivity :
        (0 : ℝ) ≤ m.K * m.g.ωc)
      have := mul_nonneg (div_nonneg (sub_nonneg.mpr hKh) hω.le) (sq_nonneg y1)
      linarith
    convert hR using 1
    simp only [y1, ξ, v]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, plant, Matrix.vecHead,
      Matrix.vecTail]
    field_simp
    ring

/-- A real mode of the filter plant at `σ` (`σ ≠ 0`, `σ + ω_c ≠ 0`): the angle `1/σ`, the
frequency `1`, the filter `ω_c K/(σ (σ + ω_c))` and the input `M σ + D + ω_c K/(σ (σ + ω_c))`
solve `A X + B U = σ X` (`plant_phasor_complex` at `ω = 0`). -/
@[tmio M, powerlib_domain] private theorem plant_mode (m : VSMLPF.Model) (hM : m.g.M ≠ 0)
    {σ : ℝ} (hσ : σ ≠ 0) (hσω : σ + m.g.ωc ≠ 0) :
    (plant m).A *ᵥ ![σ⁻¹, 1, m.g.ωc * m.K / (σ * (σ + m.g.ωc))] +
        (plant m).B *ᵥ ![m.g.M * σ + m.g.D + m.g.ωc * m.K / (σ * (σ + m.g.ωc))] =
      σ • ![σ⁻¹, 1, m.g.ωc * m.K / (σ * (σ + m.g.ωc))] := by
  have h := (plant_phasor_complex m hM (σ := σ) (ω := 0) (p := σ⁻¹) (q := 0)
    (a := m.g.ωc * m.K / (σ * (σ + m.g.ωc))) (b := 0) (by simp [hσ]) (by simp)
    (by field_simp; simp) (by simp)).1
  simpa using h

/-- The cubic `M σ³ + (M ω_c + D) σ² + D ω_c σ + ω_c K` (`M det(σ I − A)`, `VSMLPF`'s
`characteristic_polynomial`): the input of the real mode at `σ` is this cubic over
`σ (σ + ω_c)`. -/
private def cubic (m : VSMLPF.Model) (σ : ℝ) : ℝ :=
  m.g.M * σ ^ 3 + (m.g.M * m.g.ωc + m.g.D) * σ ^ 2 + m.g.D * m.g.ωc * σ + m.g.ωc * m.K

/-- A real mode at `σ` with `h σ < −2`, `σ + ω_c < 0` and a positive cubic draws energy at every
step from an output read at a fraction `ν ≥ 1/2` of the step: the multiplier `r = 1 + h σ < −1`,
the input `cubic σ/(σ (σ + ω_c)) > 0` and the output factor `1 + ν h σ < 0`
(`Numerics.eulerOutputSystem_not_passive_of_geometric`). -/
@[tmio TM, powerlib_domain] private theorem not_passive_of_mode (m : VSMLPF.Model)
    (hM : 0 < m.g.M) {h : ℝ} (hh : 0 < h) {ν : ℝ} (hν : 1 / 2 ≤ ν) {σ : ℝ}
    (hσh : h * σ < -2) (hσω : σ + m.g.ωc < 0) (hq : 0 < cubic m σ) :
    ¬ (Numerics.eulerOutputSystem (plant m) h ν).Passive := by
  have hσ0 : σ < 0 := by nlinarith
  refine Numerics.eulerOutputSystem_not_passive_of_geometric (plant m) hh ν (r := 1 + h * σ)
    (σ := σ) (by rw [abs_of_neg (by linarith)]; linarith) (by ring)
    (plant_mode m hM.ne' hσ0.ne hσω.ne) ?_
  simp [plant, dotProduct]
  have hpos : 0 < σ * (σ + m.g.ωc) := mul_pos_of_neg_of_neg hσ0 hσω
  have hσne := hσ0.ne
  have hσωne := hσω.ne
  have e : m.g.M * σ + m.g.D + m.g.ωc * m.K / (σ * (σ + m.g.ωc)) =
      cubic m σ / (σ * (σ + m.g.ωc)) := by
    simp only [cubic]
    field_simp
    ring
  have hU : 0 < m.g.M * σ + m.g.D + m.g.ωc * m.K / (σ * (σ + m.g.ωc)) := by
    rw [e]; exact div_pos hq hpos
  have hY : 1 + ν * (h * σ) < 0 := by nlinarith
  exact mul_neg_of_pos_of_neg hU hY

/-- A large filter step `h ω_c ≥ 2` (with `K > 0`): the cubic is `ω_c K > 0` at `−ω_c`, so it is
positive at some `σ < −ω_c ≤ −2/h`, and that real mode refutes passivity
(`not_passive_of_mode`). -/
@[tmio TM, powerlib_domain] private theorem not_passive_of_filter_step (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (hK : 0 < m.K) {h : ℝ} (hh : 0 < h) {ν : ℝ}
    (hν : 1 / 2 ≤ ν) (ht : 2 ≤ h * m.g.ωc) :
    ¬ (Numerics.eulerOutputSystem (plant m) h ν).Passive := by
  have hq0 : 0 < cubic m (-m.g.ωc) := by
    have e : cubic m (-m.g.ωc) = m.g.ωc * m.K := by simp only [cubic]; ring
    rw [e]; positivity
  have hcont : ContinuousAt (cubic m) (-m.g.ωc) := by unfold cubic; fun_prop
  have hev : ∀ᶠ σ in 𝓝[<] (-m.g.ωc), 0 < cubic m σ ∧ σ < -m.g.ωc :=
    ((hcont.tendsto.eventually_const_lt hq0).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin.mono fun _ hx => hx)
  obtain ⟨σ, hqσ, hσ⟩ := hev.exists
  exact not_passive_of_mode m hM hh hν (by nlinarith [mul_lt_mul_of_pos_left hσ hh])
    (by linarith) hqσ

/-- The step mode (`h ω_c ≤ 2`, `Δ < 0`): the cubic is `−Δ/h³ > 0` at `−2/h`, so it is positive at
some `σ < −2/h ≤ −ω_c`, and that real mode refutes passivity (`not_passive_of_mode`). -/
@[tmio TM, powerlib_domain] private theorem not_passive_of_step_mode (m : VSMLPF.Model)
    (hM : 0 < m.g.M) {h : ℝ} (hh : 0 < h) {ν : ℝ} (hν : 1 / 2 ≤ ν) (ht : h * m.g.ωc ≤ 2)
    (hΔ : (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc < 0) :
    ¬ (Numerics.eulerOutputSystem (plant m) h ν).Passive := by
  have hq0 : 0 < cubic m (-2 / h) := by
    have e : cubic m (-2 / h) =
        -((2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) / h ^ 3 := by
      simp only [cubic]
      field_simp
      ring
    rw [e]
    exact div_pos (by linarith) (by positivity)
  have hcont : ContinuousAt (cubic m) (-2 / h) := by unfold cubic; fun_prop
  have hev : ∀ᶠ σ in 𝓝[<] (-2 / h), 0 < cubic m σ ∧ σ < -2 / h :=
    ((hcont.tendsto.eventually_const_lt hq0).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin.mono fun _ hx => hx)
  obtain ⟨σ, hqσ, hσ⟩ := hev.exists
  have hσh : h * σ < -2 := by
    have := (lt_div_iff₀ hh).mp hσ
    linarith
  exact not_passive_of_mode m hM hh hν hσh (by nlinarith) hqσ

/-- **No averaged-output Euler discretization of the linearized VSM + filter port with
`h ω_c ≥ 2` or `Δ < 0` is passive** (with `M, ω_c, K > 0`, `h > 0`), whatever the storage: a real
mode with multiplier `r < −1` driven by `r^k U` draws energy at every step (`h ω_c ≥ 2`: just below
`σ = −ω_c`, where the cubic is `ω_c K`; `h ω_c < 2`, `Δ < 0`: just below `σ = −2/h`, where it is
`−Δ/h³`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_not_mem_den_passive_of_mode
    (m : VSMLPF.Model) (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h)
    (hmode : 2 ≤ h * m.g.ωc ∨
      (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc < 0) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearAverageFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem (plant m) h (1 / 2)).Passive
  rcases le_or_gt 2 (h * m.g.ωc) with ht | ht
  · exact not_passive_of_filter_step m hM hω hK hh le_rfl ht
  · exact not_passive_of_step_mode m hM hh le_rfl ht.le (hmode.resolve_left (not_le.mpr ht))

/-- **Passivity of the averaged-output Euler discretizations of the linearized VSM + filter
port**: within `M, ω_c, K > 0`, a discretization with step `h > 0` is passive exactly when
`h ω_c < 2`, `K (1 + h ω_c) ≤ D ω_c` and `(2 − h ω_c)(4 M − 2 D h) − K h³ ω_c ≥ 0`
(`linearAverage_mem_den_passive`, `linearAverage_not_mem_den_passive`,
`linearAverage_not_mem_den_passive_of_mode`). -/
@[tmio TM, powerlib_domain] theorem linearAverage_mem_den_passive_iff (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearAverageFamily.den .passive ↔
      h * m.g.ωc < 2 ∧ m.K * (1 + h * m.g.ωc) ≤ m.g.D * m.g.ωc ∧
        0 ≤ (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) := by
  have hp := linearAverage_mem_den_passive m hM hω hK h hh
  have hd := linearAverage_not_mem_den_passive m hM hω h hh
  have hm := linearAverage_not_mem_den_passive_of_mode m hM hω hK h hh
  unfold powerlib.TMIO.Statement at hp hd hm ⊢
  refine ⟨fun hy => ⟨not_le.mp fun hle => hm (Or.inl hle) hy, not_lt.mp fun hlt => hd hlt hy,
    not_lt.mp fun hlt => hm (Or.inr hlt) hy⟩, fun ⟨h1, h2, h3⟩ => hp h1 h2 h3⟩

/-- **The characteristic polynomial of the Euler step matrix** `I + h A` on the real axis:
`det(r I − (I + h A)) = r³ + c₂ r² + c₁ r + c₀`, the cubic `h³ det((r − 1)/h · I − A)`, computed
from the plant. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem eulerStep_charDet (m : VSMLPF.Model) (h r : ℝ) :
    (Linear.characteristicMatrix (1 + h • (plant m).A) (r : ℂ)).det =
      ((r ^ 3 + (h * (m.g.D / m.g.M + m.g.ωc) - 3) * r ^ 2 +
        (3 - 2 * h * (m.g.D / m.g.M + m.g.ωc) + h ^ 2 * m.g.D * m.g.ωc / m.g.M) * r +
        (-1 + h * (m.g.D / m.g.M + m.g.ωc) - h ^ 2 * m.g.D * m.g.ωc / m.g.M +
          h ^ 3 * m.g.ωc * m.K / m.g.M) : ℝ) : ℂ) := by
  have hK : m.g.K0 * Real.cos m.δ = m.K := rfl
  simp [Linear.characteristicMatrix, Matrix.det_fin_three, plant, VSMLPF.jacobian, hK]
  field_simp
  ring

/-- The value of the Euler step's characteristic cubic at `−1`: `−Δ/M`. -/
@[tmio M, powerlib_domain] private theorem eulerStep_charDet_neg_one (m : VSMLPF.Model)
    (hM : m.g.M ≠ 0) (h : ℝ) :
    (-1 : ℝ) ^ 3 + (h * (m.g.D / m.g.M + m.g.ωc) - 3) * (-1) ^ 2 +
      (3 - 2 * h * (m.g.D / m.g.M + m.g.ωc) + h ^ 2 * m.g.D * m.g.ωc / m.g.M) * (-1) +
      (-1 + h * (m.g.D / m.g.M + m.g.ωc) - h ^ 2 * m.g.D * m.g.ωc / m.g.M +
        h ^ 3 * m.g.ωc * m.K / m.g.M) =
      -((2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) / m.g.M := by
  field_simp
  ring

/-- A Schur stable Euler step matrix (`M, ω_c > 0`, `h > 0`) forces `K > 0`, `h ω_c < 2` and
`Δ > 0`: its characteristic cubic is `h³ ω_c K/M` at `1` and at `1 − h ω_c`, and `−Δ/M` at `−1`
(`Numerics.SchurStable.cubic_pos`, `Numerics.SchurStable.cubic_neg`). -/
@[tmio M, powerlib_domain] private theorem schur_conditions (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) {h : ℝ} (hh : 0 < h)
    (hS : Numerics.SchurStable (1 + h • (plant m).A)) :
    0 < m.K ∧ h * m.g.ωc < 2 ∧
      0 < (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc := by
  have hp := eulerStep_charDet m h
  have hMne := hM.ne'
  have h1 := hS.cubic_pos hp le_rfl
  have h3 := hS.cubic_neg hp le_rfl
  have hK : 0 < m.K := by
    have e : (1 : ℝ) ^ 3 + (h * (m.g.D / m.g.M + m.g.ωc) - 3) * 1 ^ 2 +
        (3 - 2 * h * (m.g.D / m.g.M + m.g.ωc) + h ^ 2 * m.g.D * m.g.ωc / m.g.M) * 1 +
        (-1 + h * (m.g.D / m.g.M + m.g.ωc) - h ^ 2 * m.g.D * m.g.ωc / m.g.M +
          h ^ 3 * m.g.ωc * m.K / m.g.M) = h ^ 3 * m.g.ωc * m.K / m.g.M := by ring
    rw [e] at h1
    have h1' : 0 < h ^ 3 * m.g.ωc * m.K := by
      have := mul_pos h1 hM
      rwa [div_mul_cancel₀ _ hMne] at this
    exact pos_of_mul_pos_right h1' (by positivity)
  refine ⟨hK, lt_of_not_ge fun ht => ?_, ?_⟩
  · have h2 := hS.cubic_neg hp (x := 1 - h * m.g.ωc) (by linarith)
    have e : (1 - h * m.g.ωc) ^ 3 +
        (h * (m.g.D / m.g.M + m.g.ωc) - 3) * (1 - h * m.g.ωc) ^ 2 +
        (3 - 2 * h * (m.g.D / m.g.M + m.g.ωc) + h ^ 2 * m.g.D * m.g.ωc / m.g.M) *
          (1 - h * m.g.ωc) + (-1 + h * (m.g.D / m.g.M + m.g.ωc) -
          h ^ 2 * m.g.D * m.g.ωc / m.g.M + h ^ 3 * m.g.ωc * m.K / m.g.M) =
        h ^ 3 * m.g.ωc * m.K / m.g.M := by
      field_simp
      ring
    rw [e] at h2
    have : 0 < h ^ 3 * m.g.ωc * m.K / m.g.M := by positivity
    linarith
  · rw [eulerStep_charDet_neg_one m hMne] at h3
    have := mul_neg_of_neg_of_pos h3 hM
    rw [div_mul_cancel₀ _ hMne] at this
    linarith

/-- **A Schur stable Euler step and `K (1 + h ω_c) ≤ D ω_c` make the averaged-output
discretization of the linearized VSM + filter port passive** (with `M, ω_c > 0`, `h > 0`): the
study's sufficient condition. Schur stability of `I + h A` gives `K > 0`, `h ω_c < 2` and
`Δ > 0` (`Numerics.SchurStable.cubic_pos`, `Numerics.SchurStable.cubic_neg`), and
`linearAverage_mem_den_passive` applies. -/
@[tmio TM, powerlib_domain] theorem linearAverage_mem_den_passive_of_schurStable
    (m : VSMLPF.Model) (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (h : ℝ) (hh : 0 < h)
    (hS : Numerics.SchurStable (1 + h • (plant m).A))
    (hKh : m.K * (1 + h * m.g.ωc) ≤ m.g.D * m.g.ωc) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearAverageFamily.den .passive) := by
  obtain ⟨hK, ht, hΔ⟩ := schur_conditions m hM hω hh hS
  exact linearAverage_mem_den_passive m hM hω hK h hh ht hKh hΔ.le

/-- **On the boundary `Δ = 0` the Euler step matrix is not Schur stable**: `z = −1` is a root of
its characteristic polynomial, whose value there is `−Δ/M` (`eulerStep_charDet`). With
`h ω_c < 2` and `K (1 + h ω_c) ≤ D ω_c` the averaged-output discretization is passive there
(`linearAverage_mem_den_passive`): Schur stability is sufficient, not necessary. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem not_schurStable_of_boundary (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (h : ℝ)
    (hΔ : (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc = 0) :
    ¬ Numerics.SchurStable (1 + h • (plant m).A) := by
  refine Numerics.not_schurStable_of_det_eq_zero (z := ((-1 : ℝ) : ℂ)) (by simp) ?_
  rw [eulerStep_charDet, eulerStep_charDet_neg_one m hM.ne', hΔ]
  simp

/-! ### The end-of-step output -/

/-- The explicit Euler discretization family of the linearized VSM + filter port with the
end-of-step output `C x⁺`. -/
def linearEndFamily : Family LinearStep Requirement 3 1 :=
  Numerics.eulerOutputPortFamily linearFamily plant Numerics.EulerStep.design
    Numerics.EulerStep.h 1

/-- **The end-of-step-output Euler discretizations of the linearized VSM + filter port are
passive when `h ω_c < 2`, `K (2 + 3 h ω_c) ≤ 2 D ω_c` and `Δ ≥ 0`** (with `M, ω_c, K > 0`,
`h > 0`), with the storage `½ xᵀ P x`, `xᵀ P x = K (Δδ + h Δω)² + (M − K h²/2) Δω² + ξ²/K`,
`ξ = ΔP_f − K Δδ` (`M ≥ K h²/2` follows from the conditions). The slack of the dissipation
inequality is `2 (ω_c ξ̄ + K Δω̄)²/(K ω_c ε) + ((2 D ω_c − K (2 + 3 h ω_c))/(2 ω_c)) Δω̄² +
(h Δ/(8 ε)) v²` at the midpoint state, `ε = 2 − h ω_c`, `v = (u − D Δω − ΔP_f)/M`
(`Numerics.eulerOutputSystem_passiveWith_of`). -/
@[tmio TM, powerlib_domain] theorem linearEnd_mem_den_passive (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h)
    (ht : h * m.g.ωc < 2) (hKh : m.K * (2 + 3 * h * m.g.ωc) ≤ 2 * m.g.D * m.g.ωc)
    (hΔ : 0 ≤ (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearEndFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change (Numerics.eulerOutputSystem (plant m) h 1).Passive
  have hε : 0 < 2 - h * m.g.ωc := by linarith
  have hKne := hK.ne'
  have hMh : 0 ≤ m.g.M - m.K * h ^ 2 / 2 := by
    have ht0 : 0 < h * m.g.ωc := by positivity
    have h1 := mul_le_mul_of_nonneg_left hΔ (by positivity : (0 : ℝ) ≤ h * m.g.ωc)
    have h2 := mul_le_mul_of_nonneg_left hKh
      (by positivity : (0 : ℝ) ≤ h * (2 - h * m.g.ωc))
    have h3 : 0 ≤ m.K * h ^ 2 * (2 * (2 - h * m.g.ωc) + h * m.g.ωc * (2 - h * m.g.ωc) +
        (h * m.g.ωc) ^ 2) := by positivity
    nlinarith [mul_pos ht0 hε]
  refine ⟨_, Numerics.eulerOutputSystem_passiveWith_of
    (P := !![2 * m.K, m.K * h, -1; m.K * h, m.g.M + m.K * h ^ 2 / 2, 0; -1, 0, 1 / m.K])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp) (fun x => ?_) hh.le (fun x u => ?_)⟩
  · have e : x ⬝ᵥ (!![2 * m.K, m.K * h, -1; m.K * h, m.g.M + m.K * h ^ 2 / 2, 0;
        -1, 0, 1 / m.K] *ᵥ x) = m.K * (x 0 + h * x 1) ^ 2 +
          (m.g.M - m.K * h ^ 2 / 2) * x 1 ^ 2 + (x 2 - m.K * x 0) ^ 2 / m.K := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      field_simp
      ring
    rw [e]
    have := mul_nonneg hK.le (sq_nonneg (x 0 + h * x 1))
    have := mul_nonneg hMh (sq_nonneg (x 1))
    have := div_nonneg (sq_nonneg (x 2 - m.K * x 0)) hK.le
    linarith
  · rw [plant_field, ← sub_nonneg]
    set v := (u 0 - m.g.D * x 1 - x 2) / m.g.M with hv
    set y1 := x 1 + h / 2 * v
    set ξ := x 2 + h / 2 * (m.g.ωc * (m.K * x 0 - x 2)) - m.K * (x 0 + h / 2 * x 1)
    have hR : 0 ≤ 2 * (m.g.ωc * ξ + m.K * y1) ^ 2 / (m.K * m.g.ωc * (2 - h * m.g.ωc)) +
        (2 * m.g.D * m.g.ωc - m.K * (2 + 3 * h * m.g.ωc)) / (2 * m.g.ωc) * y1 ^ 2 +
        h * ((2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) /
          (8 * (2 - h * m.g.ωc)) * v ^ 2 := by
      have := div_nonneg (mul_nonneg zero_le_two (sq_nonneg (m.g.ωc * ξ + m.K * y1)))
        (by positivity : (0 : ℝ) ≤ m.K * m.g.ωc * (2 - h * m.g.ωc))
      have := mul_nonneg (div_nonneg (sub_nonneg.mpr hKh) (by positivity : (0 : ℝ) ≤
        2 * m.g.ωc)) (sq_nonneg y1)
      have := mul_nonneg (div_nonneg (mul_nonneg hh.le hΔ) (by positivity : (0 : ℝ) ≤
        8 * (2 - h * m.g.ωc))) (sq_nonneg v)
      linarith
    convert hR using 1
    simp only [y1, ξ, v]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, plant, Matrix.vecHead,
      Matrix.vecTail]
    field_simp
    ring

/-- **No end-of-step-output Euler discretization of the linearized VSM + filter port with
`K (2 + 3 h ω_c) > 2 D ω_c` is passive** (with `M, ω_c > 0`, `h > 0`), whatever the storage. At a
closing frequency `θ` the plant's phasor at `s = (e^{iθ} − 1)/h` with the output phasor `Δω = 1`
(`plant_phasor_complex`) has the mean supplied power
`M (1 − cos θ)/h + D cos θ + ω_c K (2 − h ω_c − 4 cos² θ − 2 h ω_c cos θ)/(2 |s + ω_c|²)`,
continuous in `θ` and equal to `(2 D ω_c − K (2 + 3 h ω_c))/(2 ω_c) < 0` at `θ = 0`; a frequency
`θ = 2π/N` near zero keeps it negative (`Numerics.exists_periodic_frequency`,
`Numerics.eulerOutputSystem_not_passive_of_phasor`). -/
@[tmio TM, powerlib_domain] theorem linearEnd_not_mem_den_passive_of_damping (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (h : ℝ) (hh : 0 < h)
    (hKh : 2 * m.g.D * m.g.ωc < m.K * (2 + 3 * h * m.g.ωc)) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearEndFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem (plant m) h 1).Passive
  set E : ℝ → ℝ := fun θ => ((Real.cos θ - 1) / h + m.g.ωc) ^ 2 + (Real.sin θ / h) ^ 2
    with hE
  set f : ℝ → ℝ := fun θ => m.g.M * (1 - Real.cos θ) / h + m.g.D * Real.cos θ +
    m.g.ωc * m.K * (2 - h * m.g.ωc - 4 * Real.cos θ ^ 2 - 2 * Real.cos θ * (h * m.g.ωc)) /
      (2 * E θ) with hf
  have hE0 : E 0 = m.g.ωc ^ 2 := by simp [hE]
  have hcont : ContinuousAt f 0 := by
    have hEc : ContinuousAt E 0 := by simp only [hE]; fun_prop
    exact (by fun_prop : ContinuousAt (fun θ => m.g.M * (1 - Real.cos θ) / h +
      m.g.D * Real.cos θ) 0).add ((by fun_prop : ContinuousAt (fun θ => m.g.ωc * m.K *
        (2 - h * m.g.ωc - 4 * Real.cos θ ^ 2 - 2 * Real.cos θ * (h * m.g.ωc))) 0).div
        (continuousAt_const.mul hEc) (by rw [hE0]; positivity))
  have hf0 : f 0 < 0 := by
    simp only [hf, Real.cos_zero, hE0]
    have e : m.g.M * (1 - 1) / h + m.g.D * 1 + m.g.ωc * m.K * (2 - h * m.g.ωc - 4 * 1 ^ 2 -
        2 * 1 * (h * m.g.ωc)) / (2 * m.g.ωc ^ 2) =
        (2 * m.g.D * m.g.ωc - m.K * (2 + 3 * h * m.g.ωc)) / (2 * m.g.ωc) := by
      field_simp
      ring
    rw [e]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  obtain ⟨θ, N, hN, hper, hsin, hθ⟩ := Numerics.exists_periodic_frequency hcont hf0
  set c := Real.cos θ with hcdef
  set s := Real.sin θ with hsdef
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
  set σ := (c - 1) / h with hσdef
  set ω := s / h with hωdef
  have hσ : h * σ = c - 1 := by rw [hσdef]; field_simp
  have hω' : h * ω = s := by rw [hωdef]; field_simp
  have hω0 : 0 < ω := div_pos hsin hh
  set Eθ := (σ + m.g.ωc) ^ 2 + ω ^ 2 with hEθdef
  have hEθ : 0 < Eθ := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hω0 2)
  have hEθE : E θ = Eθ := rfl
  set p : ℝ := -(h / 2)
  set q : ℝ := -(h * (1 + c) / (2 * s))
  obtain ⟨h1, h2⟩ := euler_frequency hh.ne' hsin.ne' hsc
  set a := m.g.ωc * m.K * (p * (σ + m.g.ωc) + q * ω) / Eθ
  set b := m.g.ωc * m.K * (q * (σ + m.g.ωc) - p * ω) / Eθ
  have h3 : (σ + m.g.ωc) * a - ω * b = m.g.ωc * m.K * p := by
    simp only [a, b]
    field_simp
    ring
  have h4 : ω * a + (σ + m.g.ωc) * b = m.g.ωc * m.K * q := by
    simp only [a, b]
    field_simp
    ring
  obtain ⟨hr, hi⟩ := plant_phasor_complex m hM.ne' h1 h2 h3 h4
  refine Numerics.eulerOutputSystem_not_passive_of_phasor (plant m) hh 1 hN hper
    hsin.ne' hσ hω' hr hi ?_
  simp [plant, dotProduct]
  rw [← hcdef, ← hsdef]
  have hqs : q * s = -(h * (1 + c) / 2) := by simp only [q]; field_simp
  have hqω : q * ω = -((1 + c) / 2) := by simp only [q, ω]; field_simp
  have hωs : ω * s = s ^ 2 / h := by simp only [ω]; field_simp
  have hMpart : σ * c + ω * s = (1 - c) / h := by
    rw [hωs, hs2]
    simp only [σ]
    field_simp
    ring
  have hbr : (p * (σ + m.g.ωc) + q * ω) * c + (q * (σ + m.g.ωc) - p * ω) * s =
      (2 - h * m.g.ωc - 4 * c ^ 2 - 2 * c * (h * m.g.ωc)) / 2 := by
    have e : (p * (σ + m.g.ωc) + q * ω) * c + (q * (σ + m.g.ωc) - p * ω) * s =
        p * (σ + m.g.ωc) * c + (q * ω) * c + (q * s) * (σ + m.g.ωc) - p * (ω * s) := by ring
    have hpωs : p * (ω * s) = -(s ^ 2 / 2) := by rw [hωs]; simp only [p]; field_simp
    rw [e, hqω, hqs, hpωs]
    simp only [p]
    linear_combination (-(1 + 2 * c) / 2) * hσ + (1 / 2) * hs2
  have hab : a * c + b * s = m.g.ωc * m.K *
      (2 - h * m.g.ωc - 4 * c ^ 2 - 2 * c * (h * m.g.ωc)) / (2 * Eθ) := by
    have e : a * c + b * s = m.g.ωc * m.K * ((p * (σ + m.g.ωc) + q * ω) * c +
        (q * (σ + m.g.ωc) - p * ω) * s) / Eθ := by
      simp only [a, b]
      field_simp
    rw [e, hbr]
    field_simp
  have key : (m.g.M * ((c - 1) / h) + m.g.D + a) * c + (m.g.M * (s / h) + b) * s = f θ := by
    simp only [hf, hEθE]
    rw [← hcdef]
    have e : (m.g.M * ((c - 1) / h) + m.g.D + a) * c + (m.g.M * (s / h) + b) * s =
        m.g.M * (σ * c + ω * s) + m.g.D * c + (a * c + b * s) := by ring
    rw [e, hMpart, hab]
    ring
  linarith

/-- **No end-of-step-output Euler discretization of the linearized VSM + filter port with
`h ω_c ≥ 2` or `Δ < 0` is passive** (with `M, ω_c, K > 0`, `h > 0`), whatever the storage: the
real modes of `linearAverage_not_mem_den_passive_of_mode`, read at the end of the step. -/
@[tmio TM, powerlib_domain] theorem linearEnd_not_mem_den_passive_of_mode (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h)
    (hmode : 2 ≤ h * m.g.ωc ∨
      (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc < 0) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∉ linearEndFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den)]
  change ¬ (Numerics.eulerOutputSystem (plant m) h 1).Passive
  rcases le_or_gt 2 (h * m.g.ωc) with ht | ht
  · exact not_passive_of_filter_step m hM hω hK hh (by norm_num) ht
  · exact not_passive_of_step_mode m hM hh (by norm_num) ht.le
      (hmode.resolve_left (not_le.mpr ht))

/-- **Passivity of the end-of-step-output Euler discretizations of the linearized VSM + filter
port**: within `M, ω_c, K > 0`, a discretization with step `h > 0` is passive exactly when
`h ω_c < 2`, `K (2 + 3 h ω_c) ≤ 2 D ω_c` and `(2 − h ω_c)(4 M − 2 D h) − K h³ ω_c ≥ 0`. -/
@[tmio TM, powerlib_domain] theorem linearEnd_mem_den_passive_iff (m : VSMLPF.Model)
    (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (hK : 0 < m.K) (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearEndFamily.den .passive ↔
      h * m.g.ωc < 2 ∧ m.K * (2 + 3 * h * m.g.ωc) ≤ 2 * m.g.D * m.g.ωc ∧
        0 ≤ (2 - h * m.g.ωc) * (4 * m.g.M - 2 * m.g.D * h) - m.K * h ^ 3 * m.g.ωc) := by
  have hp := linearEnd_mem_den_passive m hM hω hK h hh
  have hd := linearEnd_not_mem_den_passive_of_damping m hM hω h hh
  have hm := linearEnd_not_mem_den_passive_of_mode m hM hω hK h hh
  unfold powerlib.TMIO.Statement at hp hd hm ⊢
  refine ⟨fun hy => ⟨not_le.mp fun hle => hm (Or.inl hle) hy, not_lt.mp fun hlt => hd hlt hy,
    not_lt.mp fun hlt => hm (Or.inr hlt) hy⟩, fun ⟨h1, h2, h3⟩ => hp h1 h2 h3⟩

/-- **A Schur stable Euler step and `K (2 + 3 h ω_c) ≤ 2 D ω_c` make the end-of-step-output
discretization of the linearized VSM + filter port passive** (with `M, ω_c > 0`, `h > 0`;
`linearEnd_mem_den_passive` with the conditions of a Schur stable `I + h A`). -/
@[tmio TM, powerlib_domain] theorem linearEnd_mem_den_passive_of_schurStable
    (m : VSMLPF.Model) (hM : 0 < m.g.M) (hω : 0 < m.g.ωc) (h : ℝ) (hh : 0 < h)
    (hS : Numerics.SchurStable (1 + h • (plant m).A))
    (hKh : m.K * (2 + 3 * h * m.g.ωc) ≤ 2 * m.g.D * m.g.ωc) :
    connection% ((⟨m, h, hh⟩ : LinearStep) ∈ linearEndFamily.den .passive) := by
  obtain ⟨hK, ht, hΔ⟩ := schur_conditions m hM hω hh hS
  exact linearEnd_mem_den_passive m hM hω hK h hh ht hKh hΔ.le

end FilterPort

end powerlib.GFM
