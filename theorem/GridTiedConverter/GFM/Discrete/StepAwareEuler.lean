import theorem.GridTiedConverter.GFM.Discrete.LinearPort
import theorem.Numerics.EulerOutputs

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
averaged output is lossless or the mode `z = −1` is hidden. Three-state VSM + filter, averaged
output: not passive when `K (1 + h ω_c) > D ω_c` (a discrete periodic input at a low
frequency). Scaffold: `theorem/Numerics/EulerPorts.agda`.

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
  Excluded: the three-state end-of-step output, the sufficiency of the three-state averaged
  condition (no closed-form storage), step-size control, delays, PWM, inner loops, PLL, line
  dynamics.

Source: work-sync GFM study note t9 (scratchpad `gfm/t9-discrete/REPORT-coord.md`, (b): step-aware
outputs; script `s3_step_aware_output.py`, closed forms of `Re G_d` on the unit circle: averaged
two-state `4 h² v² (D − K h)`, end two-state `2 h v² ((4 M − 2 D h + K h²) v² + h (2 D − 3 K h))`,
averaged three-state with the low-frequency coefficient `h² ω_c (D ω_c − K (1 + h ω_c))`);
`theorem/Numerics/EulerOutputs.lean` (`Numerics.eulerOutputSystem_passiveWith_of`,
`Numerics.eulerOutputSystem_not_passive_of_phasor`,
`Numerics.eulerOutputSystem_not_passive_of_geometric`), `theorem/Numerics/PeriodicInput.lean`
(`Numerics.exists_periodic_frequency`); Brogliato, Lozano, Maschke and Egeland, *Dissipative
Systems Analysis and Control* (2007), §3 (positive real discrete-time transfer functions); Jury,
*Theory and Application of the z-Transform Method* (1964) (the stability test).

Results.
* `SwingPort.plant_phasor` (the swing plant's phasor at a complex frequency, output phasor
  `Δω = 1`).

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
  `FilterPort.linearAverage_not_mem_den_passive` (`K (1 + h ω_c) > D ω_c`: not passive, at a low
  closing frequency). The converse (passivity under `K (1 + h ω_c) ≤ D ω_c` and a Schur stable
  `I + h A`) is not proved here.
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

end FilterPort

end powerlib.GFM
