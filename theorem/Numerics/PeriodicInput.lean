import theorem.Map.Defs

/-! # Periodic inputs refute passivity of discrete-time systems (foundation)

A discrete-time system is passive when a nonnegative storage grows over every step by at most
the energy supplied through the ports. Along a closed orbit — states that return to the initial
one after `N` steps — the storage telescopes to zero, so a closed orbit along which the ports
deliver net energy refutes passivity (`Map.System.not_passive_of_cycle`, the discrete counterpart
of `Port.System.not_passive_of_cycle`). A periodic input produces such an orbit for a system that
is linear on a plane of states and inputs. Write the phasor of a sinusoid in real form,
`X = X_r + i X_i`, `U = U_r + i U_i`. If one step maps the pair `(X, U)` to `e^{iθ} X`, that is
`step(X_r, U_r) = cos θ X_r − sin θ X_i` and `step(X_i, U_i) = sin θ X_r + cos θ X_i`, then the
sampled sinusoid `x_k = cos(θ k) X_r − sin(θ k) X_i` driven by
`u_k = cos(θ k) U_r − sin(θ k) U_i` is an orbit; it closes after `N` steps when `cos(N θ) = 1`,
and when `sin θ ≠ 0` the energy supplied over these `N` steps is
`T N/2 (U_r · Y_r + U_i · Y_i)` (`T` the step length, `Y_r`, `Y_i` the outputs at `(X_r, U_r)` and
`(X_i, U_i)`): the mean of the oscillating terms `cos(2θk)`, `sin(2θk)` over a period vanishes. A
negative mean supplied power `Re(Ū Y) = U_r · Y_r + U_i · Y_i < 0` therefore refutes passivity,
for any storage (`Map.System.not_passive_of_periodic_input`). The frequencies `θ = 2π/N`,
`N ≥ 3`, have `sin θ > 0` and accumulate at zero, so a condition continuous at zero frequency and
strict there holds at one of them (`Numerics.exists_periodic_frequency`). An unstable real mode
refutes passivity in the same way when its real phasor `(X, U)`, `step(X, U) = r X` with
`|r| ≥ 1`, has a negative supplied power: the input `r^k U` draws at least a fixed amount at every
step (`Map.System.not_passive_of_geometric_input`).

Scope.
* Generic: an arbitrary discrete-time system with ports `Map.System n p`
  (`theorem/Map/Defs.lean`), with a positive step length; the periodic-input law asks for
  linearity of the step and the output only on the plane spanned by the phasor's real and
  imaginary parts. No model. The implicit midpoint and backward Euler discretizations of linear
  plants read the law in `theorem/Numerics/ImplicitPorts.lean`.

Source: the map semantics of `theorem/Map/Defs.lean` (passivity as one-step dissipativity with
respect to the supplied energy `T u · y`); the continuous counterpart
`Port.System.not_passive_of_cycle` (`theorem/Port/Basic.lean`); Willems, "Dissipative dynamical
systems", Arch. Rational Mech. Anal. 45 (1972) (storage functions, periodic inputs); Brogliato,
Lozano, Maschke and Egeland, *Dissipative Systems Analysis and Control* (2007), §3 (positive real
discrete-time transfer functions).

Results.
* `Map.System.PassiveWith.sub_le_sum`: along an orbit the storage grows by at most the
  supplied energy.
* `Map.System.not_passive_of_cycle`: a closed orbit with negative total supply refutes
  passivity.
* `Map.System.not_passive_of_geometric_input`: a geometrically growing input `r^k U`, `|r| ≥ 1`,
  whose real phasor has a negative supplied power, refutes passivity.
* `Map.System.not_passive_of_periodic_input`: a periodic input at a frequency `θ` with
  `cos(N θ) = 1`, `sin θ ≠ 0`, whose phasor has a negative mean supplied power, refutes
  passivity.
* `Numerics.exists_periodic_frequency`: a function continuous at `0` and negative there is
  negative at some `θ = 2π/N` with `N > 0`, `cos(N θ) = 1` and `sin θ > 0`.
-/

noncomputable section

namespace powerlib

open Filter Topology

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **The storage telescopes along an orbit.** For states `x 0, …, x N` of a discrete system with
storage `V` driven by inputs `u 0, …, u (N − 1)`, the storage grows over the `N` steps by at most
the energy supplied. -/
@[tmio T, powerlib_foundation] theorem Map.System.PassiveWith.sub_le_sum {s : Map.System n p}
    {V : ℝⁿ → ℝ} (hV : s.PassiveWith V) (x : ℕ → ℝⁿ) (u : ℕ → Fin p → ℝ) {N : ℕ}
    (hx : ∀ k < N, s.step (x k) (u k) = x (k + 1)) :
    V (x N) - V (x 0) ≤ ∑ k ∈ Finset.range N, s.supply (x k) (u k) := by
  have key : ∀ m ≤ N, V (x m) - V (x 0) ≤ ∑ k ∈ Finset.range m, s.supply (x k) (u k) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ]
      have hs := hV.2 (x m) (u m)
      rw [hx m (by omega)] at hs
      linarith [ih (by omega)]
  exact key N le_rfl

/-- **A closed orbit that draws energy refutes passivity.** States `x 0, …, x N` of a discrete
system driven by inputs `u 0, …, u (N − 1)`, with `x N = x 0` and a negative total supply: with a
nonnegative storage `V` the increments `V (x (k + 1)) − V (x k)` telescope to zero, and each is
bounded by the supply of its step (`Map.System.PassiveWith.sub_le_sum`). -/
@[tmio T, powerlib_foundation] theorem Map.System.not_passive_of_cycle (s : Map.System n p)
    (x : ℕ → ℝⁿ) (u : ℕ → Fin p → ℝ) {N : ℕ} (hx : ∀ k < N, s.step (x k) (u k) = x (k + 1))
    (hcycle : x N = x 0) (hneg : ∑ k ∈ Finset.range N, s.supply (x k) (u k) < 0) :
    ¬ s.Passive := by
  rintro ⟨V, hV⟩
  have h := hV.sub_le_sum x u hx
  rw [hcycle, sub_self] at h
  linarith

/-- **A geometrically growing input that draws energy refutes passivity.** For a discrete system
with step length `T > 0`, homogeneous on the line spanned by `(X, U)`, with `step(X, U) = r X` for
a real `r` with `|r| ≥ 1`: the orbit `x_k = r^k X` under `u_k = r^k U` draws at least
`−T (U · Y)`, `Y = output(X, U)`, at every step (`r^{2k} ≥ 1`); when `U · Y < 0` the energy drawn
grows without bound while a nonnegative storage pays at most `V X`
(`Map.System.PassiveWith.sub_le_sum`). With `r = ±1` the orbit is an equilibrium or a two-cycle. -/
@[tmio T, powerlib_foundation] theorem Map.System.not_passive_of_geometric_input
    (s : Map.System n p) (hT : 0 < s.period) {r : ℝ} (hr : 1 ≤ |r|) {X : ℝⁿ} {U : Fin p → ℝ}
    (hstep : ∀ a : ℝ, s.step (a • X) (a • U) = a • s.step X U)
    (hout : ∀ a : ℝ, s.output (a • X) (a • U) = a • s.output X U)
    (hX : s.step X U = r • X) (hneg : U ⬝ᵥ s.output X U < 0) : ¬ s.Passive := by
  rintro ⟨V, hV⟩
  set x : ℕ → ℝⁿ := fun k => r ^ k • X
  set u : ℕ → Fin p → ℝ := fun k => r ^ k • U
  have hx : ∀ N, ∀ k < N, s.step (x k) (u k) = x (k + 1) := fun N k _ => by
    simp only [x, u]
    rw [hstep, hX, smul_smul, pow_succ]
  have hk : ∀ k : ℕ, s.supply (x k) (u k) ≤ s.period * (U ⬝ᵥ s.output X U) := by
    intro k
    have e : s.supply (x k) (u k) = s.period * (r ^ k * r ^ k) * (U ⬝ᵥ s.output X U) := by
      simp only [Map.System.supply, x, u]
      rw [hout, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    have h1 : 1 ≤ r ^ k * r ^ k := by
      rw [← mul_pow]
      exact one_le_pow₀ (by nlinarith [abs_mul_abs_self r])
    rw [e]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hT.le (sub_nonneg.mpr h1)) hneg.le]
  obtain ⟨N, hN⟩ := exists_nat_gt (V X / (-(s.period * (U ⬝ᵥ s.output X U))))
  have hsum := hV.sub_le_sum x u (hx N)
  have hbound : ∑ k ∈ Finset.range N, s.supply (x k) (u k) ≤
      N * (s.period * (U ⬝ᵥ s.output X U)) := by
    calc ∑ k ∈ Finset.range N, s.supply (x k) (u k)
        ≤ ∑ _k ∈ Finset.range N, s.period * (U ⬝ᵥ s.output X U) :=
          Finset.sum_le_sum fun k _ => hk k
      _ = N * (s.period * (U ⬝ᵥ s.output X U)) := by simp
  have hpos : 0 < -(s.period * (U ⬝ᵥ s.output X U)) := by nlinarith
  have hx0 : x 0 = X := by simp [x]
  have hVN := hV.1 (x N)
  rw [div_lt_iff₀ hpos] at hN
  rw [hx0] at hsum
  nlinarith

/-- The telescoping sums `2 sin θ Σ_{k<m} cos(2θk) = sin((2m − 1)θ) + sin θ` and
`2 sin θ Σ_{k<m} sin(2θk) = cos θ − cos((2m − 1)θ)`. -/
@[tmio T, powerlib_foundation] private theorem sum_range_cos_sin (θ : ℝ) (m : ℕ) :
    2 * Real.sin θ * ∑ k ∈ Finset.range m, Real.cos (2 * (θ * k)) =
        Real.sin ((2 * m - 1) * θ) + Real.sin θ ∧
      2 * Real.sin θ * ∑ k ∈ Finset.range m, Real.sin (2 * (θ * k)) =
        Real.cos θ - Real.cos ((2 * m - 1) * θ) := by
  induction m with
  | zero => simp [neg_mul, Real.sin_neg, Real.cos_neg]
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add, ih.1, ih.2]
    have e1 : (2 * ((m + 1 : ℕ) : ℝ) - 1) * θ = 2 * (θ * m) + θ := by push_cast; ring
    have e2 : (2 * (m : ℝ) - 1) * θ = 2 * (θ * m) - θ := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
    constructor <;> ring

/-- Over a closed period, `cos(N θ) = 1` with `sin θ ≠ 0`, the oscillating terms average out:
`Σ_{k<N} cos(2θk) = 0` and `Σ_{k<N} sin(2θk) = 0`. -/
@[tmio T, powerlib_foundation] private theorem sum_range_cos_sin_eq_zero {θ : ℝ} {N : ℕ}
    (hper : Real.cos (N * θ) = 1) (hθ : Real.sin θ ≠ 0) :
    ∑ k ∈ Finset.range N, Real.cos (2 * (θ * k)) = 0 ∧
      ∑ k ∈ Finset.range N, Real.sin (2 * (θ * k)) = 0 := by
  obtain ⟨h1, h2⟩ := sum_range_cos_sin θ N
  have hs : Real.sin (N * θ) = 0 := by
    have := Real.sin_sq_add_cos_sq (N * θ)
    rw [hper] at this
    nlinarith [sq_nonneg (Real.sin (N * θ))]
  have e : (2 * (N : ℝ) - 1) * θ = 2 * (N * θ) - θ := by ring
  rw [e, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul, hper, hs] at h1
  rw [e, Real.cos_sub, Real.sin_two_mul, Real.cos_two_mul, hper, hs] at h2
  have h2θ : (2 : ℝ) * Real.sin θ ≠ 0 := mul_ne_zero two_ne_zero hθ
  constructor
  · exact (mul_eq_zero.mp (by rw [h1]; ring)).resolve_left h2θ
  · exact (mul_eq_zero.mp (by rw [h2]; ring)).resolve_left h2θ

/-- **A periodic input with a negative mean supplied power refutes passivity.** For a discrete
system with step length `T > 0` that is linear on the plane spanned by `(X_r, U_r)` and
`(X_i, U_i)` and maps the phasor `(X_r + i X_i, U_r + i U_i)` to `e^{iθ} (X_r + i X_i)`, with
`cos(N θ) = 1` for some `N > 0` and `sin θ ≠ 0`: the orbit `x_k = cos(θ k) X_r − sin(θ k) X_i`
under `u_k = cos(θ k) U_r − sin(θ k) U_i` closes after `N` steps and draws the energy
`−T N/2 (U_r · Y_r + U_i · Y_i)`, `Y_r = output(X_r, U_r)`, `Y_i = output(X_i, U_i)`; when the
mean supplied power `U_r · Y_r + U_i · Y_i` is negative no storage pays for it
(`Map.System.not_passive_of_cycle`). -/
@[tmio T, powerlib_foundation] theorem Map.System.not_passive_of_periodic_input
    (s : Map.System n p) (hT : 0 < s.period) {θ : ℝ} {N : ℕ} (hN : 0 < N)
    (hper : Real.cos (N * θ) = 1) (hθ : Real.sin θ ≠ 0) {Xr Xi : ℝⁿ} {Ur Ui : Fin p → ℝ}
    (hstep : ∀ a b : ℝ, s.step (a • Xr + b • Xi) (a • Ur + b • Ui) =
      a • s.step Xr Ur + b • s.step Xi Ui)
    (hout : ∀ a b : ℝ, s.output (a • Xr + b • Xi) (a • Ur + b • Ui) =
      a • s.output Xr Ur + b • s.output Xi Ui)
    (hr : s.step Xr Ur = Real.cos θ • Xr - Real.sin θ • Xi)
    (hi : s.step Xi Ui = Real.sin θ • Xr + Real.cos θ • Xi)
    (hneg : Ur ⬝ᵥ s.output Xr Ur + Ui ⬝ᵥ s.output Xi Ui < 0) : ¬ s.Passive := by
  set x : ℕ → ℝⁿ := fun k => Real.cos (θ * k) • Xr + (-Real.sin (θ * k)) • Xi
  set u : ℕ → Fin p → ℝ := fun k => Real.cos (θ * k) • Ur + (-Real.sin (θ * k)) • Ui
  refine s.not_passive_of_cycle x u (N := N) (fun k _ => ?_) ?_ ?_
  · simp only [x, u]
    rw [hstep, hr, hi]
    have e : θ * ((k + 1 : ℕ) : ℝ) = θ * k + θ := by push_cast; ring
    rw [e, Real.cos_add, Real.sin_add]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  · have hs : Real.sin (N * θ) = 0 := by
      have := Real.sin_sq_add_cos_sq (N * θ)
      rw [hper] at this
      nlinarith [sq_nonneg (Real.sin (N * θ))]
    simp only [x]
    rw [mul_comm θ, hper, hs]
    simp
  · obtain ⟨hc, hs⟩ := sum_range_cos_sin_eq_zero hper hθ
    set α := Ur ⬝ᵥ s.output Xr Ur
    set β := Ur ⬝ᵥ s.output Xi Ui
    set γ := Ui ⬝ᵥ s.output Xr Ur
    set δ := Ui ⬝ᵥ s.output Xi Ui
    have hk : ∀ k : ℕ, s.supply (x k) (u k) = s.period * ((α + δ) / 2 +
        (α - δ) / 2 * Real.cos (2 * (θ * k)) - (β + γ) / 2 * Real.sin (2 * (θ * k))) := by
      intro k
      simp only [Map.System.supply, x, u]
      rw [hout]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [Real.cos_two_mul, Real.sin_two_mul]
      have := Real.sin_sq_add_cos_sq (θ * k)
      linear_combination (s.period * δ) * this
    simp only [hk]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hc, hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    nlinarith [mul_pos hT hNpos]

namespace Numerics

/-- **A frequency `2π/N` near zero.** A function continuous at `0` and negative there is negative
at some frequency `θ = 2π/N`, `N > 0`, which closes after `N` steps (`cos(N θ) = 1`) and has
`sin θ > 0`. -/
@[tmio T, powerlib_foundation] theorem exists_periodic_frequency {f : ℝ → ℝ}
    (hf : ContinuousAt f 0) (h0 : f 0 < 0) :
    ∃ θ : ℝ, ∃ N : ℕ, 0 < N ∧ Real.cos (N * θ) = 1 ∧ 0 < Real.sin θ ∧ f θ < 0 := by
  have ht : Tendsto (fun N : ℕ => 2 * Real.pi / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hev := (hf.tendsto.comp ht).eventually (gt_mem_nhds h0)
  obtain ⟨N, hN, h3⟩ := (hev.and (eventually_ge_atTop 3)).exists
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hNpos : (0 : ℝ) < N := by linarith
  refine ⟨2 * Real.pi / N, N, by omega, ?_, ?_, hN⟩
  · rw [mul_div_cancel₀ _ hNpos.ne', Real.cos_two_pi]
  · apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hNpos]
    nlinarith [Real.pi_pos]

end Numerics

end powerlib
