import theorem.GridTiedConverter.GFM.Line.Model
import theorem.PH.Nonlinear

/-! # Port-Hamiltonian form of the grid-forming VSM on an R–L line with a weighted line energy

The four-state Layer-0 VSM (`Line.VSM`, `theorem/GridTiedConverter/GFM/Line/Model.lean`) with
the candidate energy of its quasi-static reduction plus a weighted magnetic energy of the current
deviation, `H_c = U(δ) + ½ M ω² + (c L/2) |i − i_s(δ)|²`: an explicit angle-dependent
interconnection `J_c(δ)` and dissipation `R_c(δ)` with `(J_c − R_c) ∇H_c = f`, the exact
condition `R_c ⪰ 0`, and the exact condition for some weight `c > 0` to work.

Model boundary.
* The law of `Line.VSM`: state `x = (δ, ω, i_d, i_q) : State 4` in this order, dq frame at the
  nominal `ω₀` aligned with the stiff grid `V ∠ 0`, `δ̇ = ω`, `M ω̇ = P_ref − P_e − D ω`,
  `L i̇ = E e^{jδ} − V − (R + jX) i` (`X = ω₀ L`), constant EMF magnitude `E`, line current out
  of the converter, `P_e = E (cos δ i_d + sin δ i_q)` export-positive (per unit, no `3/2`).
* The energy: `U = Synchronous.SwingParams.potential 0` of the quasi-static reduction
  `VSM.swingParams`
  (`U' = P(δ) − P_ref`, `P(δ) = c₀ + A sin(δ − α)`, `VSM.reducedField_eq_swing`), the
  quasi-steady current `i_s(δ) = (E e^{jδ} − V)/(R + jX)` (`Network.is`) and a weight `c > 0`
  on the magnetic energy of the deviation `ĩ = i − i_s(δ)`; `c = 1` is the unweighted candidate.
  Its angle rate along the swing is `i_s'(δ) = j E e^{jδ}/Z` (`isRateD`, `isRateQ`).
* Port of the pH model: one input `u`, an additive set-point deviation `P_ref ↦ P_ref + u`
  (input matrix `(0, 1/M, 0, 0)ᵀ`), output `y = ω` (incoming-positive power `u y`, as in
  `theorem/PH/Nonlinear.lean`). The grid voltage is not a port (the energy depends on `V`).
* Parameters: `M ≠ 0`, `L > 0`, `|Z|² = R² + X² > 0`; the dissipation statements assume a lossy
  line `R > 0`. `D`, `E`, `V`, `P_ref` arbitrary unless stated.
* Level: static structure of the field (an identity at every state and the sign of `R_c`);
  no stability statement. Excluded: reactive / voltage loop, power filter, inner loops, limits,
  PLL, delay, PWM, grid-frequency variation.

Source: GFM port-structure study note (t1-port, §(c) "pH form", Layer 0 with line item (ii):
the candidate energy, `Ḣ = −D ω² − R |ĩ|² − ω ĩ·w(δ)`, `|w|² = E² |Z + jL|²/|Z|²`; symbolic
checks `c3_ph_layer0.py`; the weighted energy and its existence condition are derived here); van
der Schaft and Jeltsema, *Port-Hamiltonian Systems Theory: An Introductory Overview* (2014), §2;
the matching-control analogue `theorem/GridTiedConverter/GFM/Matching/StiffGrid.lean`
(`MatchingStiffGrid.Model.margin_pos_iff`), where a feedforward removes the `E`-sized coupling.

Results.
* `H_c` (`phEnergy`) has the gradient `phGrad` (`hasGradientAt_phEnergy`),
  `∂H_c/∂δ = P(δ) − P_ref − c L ĩ·i_s'(δ)`, `∂H_c/∂ω = M ω`, `∂H_c/∂i = c L ĩ`.
* With the coupling vector `w_c(δ) = E e^{jδ} + c L i_s'(δ)` (`couplingD`, `couplingQ`) and
  `k = w_c/(2 M c L)` (`phKD`, `phKQ`), `J₂ = [[0, −1], [1, 0]]`:
  `J_c = [[0, 1/M, 0, 0], [−1/M, 0, −kᵀ], [0, k, −X/(c L²) J₂]]` (`phJ`, skew: `phJ_skew`),
  `R_c = diag(0, [[D/M², kᵀ], [k, R/(c L²) I]])` (`phR`), and `(J_c − R_c) ∇H_c = f`
  (`phField_eq`).
* `R_c(δ) ⪰ 0 ⇔ |w_c(δ)|² ≤ 4 D c R` (`phR_posSemidef_iff`, `R > 0`); `|w_c|²` does not depend on
  the angle, `|w_c|² = E² (R² + (X + c L)²)/|Z|²` (`normSq_coupling`), so `R_c ⪰ 0` at every state
  iff `E² (R² + (X + c L)²) ≤ 4 D c R |Z|²` (`forall_phR_posSemidef_iff`; at `c = 1` the study's
  `4 D R ≥ |w|²`).
* Some weight works iff `2 D R ≥ E² L (X + |Z|)/|Z|²`, i.e. `E² L (X + |Z|) ≤ 2 D R |Z|²`
  (`exists_phR_posSemidef_iff`), and then `c = |Z|/L` works: it is the best weight
  (`forall_phR_posSemidef_optimal_iff`).
* The condition belongs to the energy, not to the chosen structure: along the field
  `⟨∇H_c, f⟩ = −D ω² − c R |ĩ|² − ω ĩ·w_c(δ)` (`phGrad_dotProduct_field`), and some skew
  `J(x)` and `R(x) ⪰ 0` with `(J − R) ∇H_c = f` exist iff
  `E² (R² + (X + c L)²) ≤ 4 D c R |Z|²` (`exists_structure_iff`).
* `phModel`: the pH model (`PH.NonlinearModel 4 1`) given `R_c ⪰ 0` at every state; its field is
  the VSM field at the shifted set point (`phModel_field`), its zero-input field the VSM field
  (`phModel_zeroInputField`), its output `ω` (`phModel_output`).

Family and connection conclusions.
* None: static structure. The behaviour of the VSM is that of the families of
  `theorem/GridTiedConverter/GFM/Line/VSM.lean`; no family reads `phModel`.
-/

noncomputable section
namespace powerlib.GFM.Line
open Matrix
open powerlib.Dynamics (State coord hasFDerivAt_coord)

namespace VSM

variable (g : VSM)

/-! ## The weighted energy and its gradient -/

/-- d-component of the angle rate of the quasi-steady current, `i_s'(δ) = j E e^{jδ}/Z`. -/
def isRateD (δ : ℝ) : ℝ := g.E * (g.X * Real.cos δ - g.R * Real.sin δ) / g.absSq

/-- q-component of the angle rate `i_s'(δ)`. -/
def isRateQ (δ : ℝ) : ℝ := g.E * (g.X * Real.sin δ + g.R * Real.cos δ) / g.absSq

/-- The coupling vector `w_c(δ) = E e^{jδ} + c L i_s'(δ)`, d-component. -/
def couplingD (c δ : ℝ) : ℝ := g.E * Real.cos δ + c * g.L * g.isRateD δ

/-- The coupling vector `w_c(δ)`, q-component. -/
def couplingQ (c δ : ℝ) : ℝ := g.E * Real.sin δ + c * g.L * g.isRateQ δ

/-- The weighted energy `H_c = U(δ) + ½ M ω² + (c L/2) |i − i_s(δ)|²`. -/
def phEnergy (c : ℝ) (x : State 4) : ℝ :=
  g.swingParams.potential 0 (x 0) + g.M * x 1 ^ 2 / 2 +
    c * g.L / 2 * ((x 2 - (g.is (x 0)).re) ^ 2 + (x 3 - (g.is (x 0)).im) ^ 2)

/-- The gradient of `H_c`. -/
def phGrad (c : ℝ) (x : State 4) : State 4 :=
  WithLp.toLp 2 ![g.swingParams.Pe (x 0) - g.Pref - c * g.L *
      ((x 2 - (g.is (x 0)).re) * g.isRateD (x 0) + (x 3 - (g.is (x 0)).im) * g.isRateQ (x 0)),
    g.M * x 1, c * g.L * (x 2 - (g.is (x 0)).re), c * g.L * (x 3 - (g.is (x 0)).im)]

/-- The angle derivative of the d-component of `i_s`. -/
@[tmio M, powerlib_domain] private theorem hasDerivAt_is_re (δ : ℝ) :
    HasDerivAt (fun δ => (g.is δ).re) (g.isRateD δ) δ := by
  have h := ((((Real.hasDerivAt_cos δ).const_mul g.E).sub_const g.V).const_mul g.R).add
    ((Real.hasDerivAt_sin δ).const_mul g.E |>.const_mul g.X) |>.div_const g.absSq
  convert h using 1
  · funext y; rw [Network.is_re]; rfl
  · simp only [isRateD]; ring

/-- The angle derivative of the q-component of `i_s`. -/
@[tmio M, powerlib_domain] private theorem hasDerivAt_is_im (δ : ℝ) :
    HasDerivAt (fun δ => (g.is δ).im) (g.isRateQ δ) δ := by
  have h := (((Real.hasDerivAt_sin δ).const_mul g.E).const_mul g.R).sub
    ((((Real.hasDerivAt_cos δ).const_mul g.E).sub_const g.V).const_mul g.X) |>.div_const g.absSq
  convert h using 1
  · funext y; rw [Network.is_im]; rfl
  · simp only [isRateQ]; ring

@[tmio M, powerlib_domain] theorem hasGradientAt_phEnergy (c : ℝ) (x : State 4) :
    HasGradientAt (g.phEnergy c) (g.phGrad c x) x := by
  have h0 := hasFDerivAt_coord 0 x
  have h1 := hasFDerivAt_coord 1 x
  have hU := (g.swingParams.hasDerivAt_potential 0 (x 0)).comp_hasFDerivAt x h0
  have e2 := (hasFDerivAt_coord 2 x).sub ((g.hasDerivAt_is_re (x 0)).comp_hasFDerivAt x h0)
  have e3 := (hasFDerivAt_coord 3 x).sub ((g.hasDerivAt_is_im (x 0)).comp_hasFDerivAt x h0)
  have h := (hU.add ((h1.mul h1).const_mul (g.M / 2))).add
    (((e2.mul e2).add (e3.mul e3)).const_mul (c * g.L / 2))
  refine PH.hasGradientAt_of_hasFDerivAt (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)) fun v => ?_
  · simp [phEnergy]
    ring
  · simp [phGrad, dotProduct, Fin.sum_univ_four, swingParams]
    ring

/-! ## The angle-dependent structure -/

/-- The coupling coefficient `k_d = w_{c,d}/(2 M c L)`. -/
def phKD (c : ℝ) (x : State 4) : ℝ := g.couplingD c (x 0) / (2 * g.M * c * g.L)

/-- The coupling coefficient `k_q = w_{c,q}/(2 M c L)`. -/
def phKQ (c : ℝ) (x : State 4) : ℝ := g.couplingQ c (x 0) / (2 * g.M * c * g.L)

/-- The interconnection `J_c(δ)`: the rotor pair `±1/M`, the coupling `±k` between the rotor and
the line, the line gyrator `X/(c L²)`. -/
def phJ (c : ℝ) (x : State 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1 / g.M, 0, 0;
    -(1 / g.M), 0, -g.phKD c x, -g.phKQ c x;
    0, g.phKD c x, 0, g.X / (c * g.L ^ 2);
    0, g.phKQ c x, -(g.X / (c * g.L ^ 2)), 0]

/-- The dissipation `R_c(δ)`: damping `D/M²`, line resistance `R/(c L²)`, coupling `k`. -/
def phR (c : ℝ) (x : State 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0;
    0, g.D / g.M ^ 2, g.phKD c x, g.phKQ c x;
    0, g.phKD c x, g.R / (c * g.L ^ 2), 0;
    0, g.phKQ c x, 0, g.R / (c * g.L ^ 2)]

@[tmio M, powerlib_domain] theorem phJ_skew (c : ℝ) (x : State 4) :
    (g.phJ c x)ᵀ = -g.phJ c x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phJ]

/-- The quasi-steady current carries the source voltage across the line:
`R i_{s,d} − X i_{s,q} = E cos δ − V`, `R i_{s,q} + X i_{s,d} = E sin δ`. -/
@[tmio M, powerlib_domain] private theorem is_line (hZ : g.absSq ≠ 0) (δ : ℝ) :
    g.R * (g.is δ).re - g.X * (g.is δ).im = g.E * Real.cos δ - g.V ∧
      g.R * (g.is δ).im + g.X * (g.is δ).re = g.E * Real.sin δ := by
  rw [Network.is_re, Network.is_im]
  have hZ' : g.R ^ 2 + g.X ^ 2 ≠ 0 := hZ
  constructor <;> (unfold Network.absSq; field_simp; ring)

/-- `(J_c(δ) − R_c(δ)) ∇H_c = f` for `M ≠ 0`, `L ≠ 0`, `c ≠ 0`, `|Z|² > 0`. -/
@[tmio M, powerlib_domain] theorem phField_eq (hM : g.M ≠ 0) (hL : g.L ≠ 0) (hZ : 0 < g.absSq)
    {c : ℝ} (hc : c ≠ 0) (x : State 4) :
    (g.phJ c x - g.phR c x) *ᵥ WithLp.ofLp (g.phGrad c x) = WithLp.ofLp (g.field x) := by
  have hP : g.swingParams.Pe (x 0) = g.power (x 0) (g.is (x 0)).re (g.is (x 0)).im :=
    (g.qssPower_eq_polar hZ (x 0)).symm
  obtain ⟨hd, hq⟩ := g.is_line hZ.ne' (x 0)
  funext i
  fin_cases i
  · simp [phJ, phR, phGrad, field, mulVec, dotProduct, Fin.sum_univ_four]
    field_simp
  · simp only [phJ, phR, phGrad, field, phKD, phKQ, couplingD, couplingQ, hP,
      Network.power_eq]
    simp [mulVec, dotProduct, Fin.sum_univ_four]
    field_simp
    ring
  · simp [phJ, phR, phGrad, field, mulVec, dotProduct, Fin.sum_univ_four, Network.rateD]
    field_simp
    linear_combination hd
  · simp [phJ, phR, phGrad, field, mulVec, dotProduct, Fin.sum_univ_four, Network.rateQ]
    field_simp
    linear_combination hq

/-! ## The sign of the dissipation -/

/-- **The dissipation condition.** For a lossy line (`R > 0`), `M ≠ 0`, `L ≠ 0` and a weight
`c > 0`: `R_c(δ) ⪰ 0 ⇔ |w_c(δ)|² ≤ 4 D c R`. -/
@[tmio M, powerlib_domain] theorem phR_posSemidef_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hR : 0 < g.R) {c : ℝ} (hc : 0 < c) (x : State 4) :
    (g.phR c x).PosSemidef ↔
      g.couplingD c (x 0) ^ 2 + g.couplingQ c (x 0) ^ 2 ≤ 4 * g.D * c * g.R := by
  set kd := g.couplingD c (x 0)
  set kq := g.couplingQ c (x 0)
  have hsymm : (g.phR c x).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [phR]
  -- the quadratic form, scaled by `4 M² c² L²`
  set A := 4 * c ^ 2 * g.L ^ 2 * g.D
  set B := 2 * g.M * c * g.L
  set C := 4 * g.M ^ 2 * c * g.R
  have hq : ∀ v : Fin 4 → ℝ, 4 * g.M ^ 2 * c ^ 2 * g.L ^ 2 * (star v ⬝ᵥ (g.phR c x *ᵥ v)) =
      A * v 1 ^ 2 + 2 * B * v 1 * (kd * v 2 + kq * v 3) + C * (v 2 ^ 2 + v 3 ^ 2) := by
    intro v
    simp [phR, phKD, phKQ, dotProduct, mulVec, Fin.sum_univ_four, A, B, C, kd, kq]
    field_simp
    ring
  have hs : 0 < 4 * g.M ^ 2 * c ^ 2 * g.L ^ 2 := by positivity
  have hC : 0 < C := by positivity
  have hgap : A * C - B ^ 2 * (kd ^ 2 + kq ^ 2) =
      4 * g.M ^ 2 * c ^ 2 * g.L ^ 2 * (4 * g.D * c * g.R - (kd ^ 2 + kq ^ 2)) := by
    simp only [A, B, C]; ring
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩
    have hv := mul_nonneg hs.le (h ![0, C, -(B * kd), -(B * kq)])
    rw [hq] at hv
    simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons] at hv
    have e : A * C ^ 2 + 2 * B * C * (kd * -(B * kd) + kq * -(B * kq)) +
        C * ((-(B * kd)) ^ 2 + (-(B * kq)) ^ 2) = C * (A * C - B ^ 2 * (kd ^ 2 + kq ^ 2)) := by
      ring
    rw [e, hgap] at hv
    have h2 := (mul_nonneg_iff_of_pos_left hC).mp hv
    have h3 := (mul_nonneg_iff_of_pos_left hs).mp h2
    linarith
  · intro h
    refine ⟨hsymm, fun v => ?_⟩
    have hsq : 0 ≤ C * (A * v 1 ^ 2 + 2 * B * v 1 * (kd * v 2 + kq * v 3) +
        C * (v 2 ^ 2 + v 3 ^ 2)) := by
      have e : C * (A * v 1 ^ 2 + 2 * B * v 1 * (kd * v 2 + kq * v 3) +
          C * (v 2 ^ 2 + v 3 ^ 2)) = (A * C - B ^ 2 * (kd ^ 2 + kq ^ 2)) * v 1 ^ 2 +
            (B * kd * v 1 + C * v 2) ^ 2 + (B * kq * v 1 + C * v 3) ^ 2 := by ring
      rw [e, hgap]
      have : 0 ≤ 4 * g.D * c * g.R - (kd ^ 2 + kq ^ 2) := by linarith
      positivity
    rw [← hq] at hsq
    exact (mul_nonneg_iff_of_pos_left hs).mp ((mul_nonneg_iff_of_pos_left hC).mp hsq)

/-- The coupling has the angle-independent size `|w_c|² = E² (R² + (X + c L)²)/|Z|²`. -/
@[tmio M, powerlib_domain] theorem normSq_coupling (hZ : g.absSq ≠ 0) (c δ : ℝ) :
    g.couplingD c δ ^ 2 + g.couplingQ c δ ^ 2 =
      g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) / g.absSq := by
  have hZ' : g.R ^ 2 + g.X ^ 2 ≠ 0 := hZ
  simp only [couplingD, couplingQ, isRateD, isRateQ]
  unfold Network.absSq
  field_simp
  linear_combination (g.E ^ 2 * ((g.R ^ 2 + g.X ^ 2 + c * g.L * g.X) ^ 2 +
    (c * g.L * g.R) ^ 2)) * Real.sin_sq_add_cos_sq δ

/-- `R_c ⪰ 0` at every state `⇔ E² (R² + (X + c L)²) ≤ 4 D c R |Z|²` (the weight `c` explicit;
`c = 1` is the unweighted candidate). -/
@[tmio M, powerlib_domain] theorem forall_phR_posSemidef_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hR : 0 < g.R) (hZ : 0 < g.absSq) {c : ℝ} (hc : 0 < c) :
    (∀ x, (g.phR c x).PosSemidef) ↔
      g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) ≤ 4 * g.D * c * g.R * g.absSq := by
  simp only [g.phR_posSemidef_iff hM hL hR hc, g.normSq_coupling hZ.ne', div_le_iff₀ hZ]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- **The best weight.** With `c = |Z|/L` the dissipation is positive semidefinite at every state
iff `E² L (X + |Z|) ≤ 2 D R |Z|²`. -/
@[tmio M, powerlib_domain] theorem forall_phR_posSemidef_optimal_iff (hM : g.M ≠ 0)
    (hL : 0 < g.L) (hR : 0 < g.R) (hZ : 0 < g.absSq) :
    (∀ x, (g.phR (Real.sqrt g.absSq / g.L) x).PosSemidef) ↔
      g.E ^ 2 * g.L * (g.X + Real.sqrt g.absSq) ≤ 2 * g.D * g.R * g.absSq := by
  have hs := Real.sqrt_pos.mpr hZ
  have hss := Real.sq_sqrt hZ.le
  rw [g.forall_phR_posSemidef_iff hM hL.ne' hR hZ (by positivity)]
  set z := Real.sqrt g.absSq
  have hR2 : g.R ^ 2 = g.absSq - g.X ^ 2 := by unfold Network.absSq; ring
  have e1 : g.E ^ 2 * (g.R ^ 2 + (g.X + z / g.L * g.L) ^ 2) =
      2 * z * (g.E ^ 2 * (g.X + z)) := by
    rw [div_mul_cancel₀ _ hL.ne', hR2, ← hss]; ring
  have e2 : 4 * g.D * (z / g.L) * g.R * g.absSq =
      2 * z / g.L * (2 * g.D * g.R * g.absSq) := by ring
  rw [e1, e2, ← hss]
  have hzL : 0 < 2 * z / g.L := by positivity
  constructor
  · intro h
    have h' : 2 * z * (g.E ^ 2 * (g.X + z)) ≤ 2 * z * (2 * g.D * g.R * z ^ 2 / g.L) := by
      calc 2 * z * (g.E ^ 2 * (g.X + z)) ≤ 2 * z / g.L * (2 * g.D * g.R * z ^ 2) := h
        _ = 2 * z * (2 * g.D * g.R * z ^ 2 / g.L) := by ring
    have h'' := le_of_mul_le_mul_left h' (by positivity)
    rw [le_div_iff₀ hL] at h''
    linarith
  · intro h
    have : g.E ^ 2 * (g.X + z) ≤ 2 * g.D * g.R * z ^ 2 / g.L := by
      rw [le_div_iff₀ hL]; linarith
    calc 2 * z * (g.E ^ 2 * (g.X + z)) ≤ 2 * z * (2 * g.D * g.R * z ^ 2 / g.L) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * z / g.L * (2 * g.D * g.R * z ^ 2) := by ring

/-- **Existence of a weight.** Some `c > 0` makes `R_c ⪰ 0` at every state iff
`2 D R ≥ E² L (X + |Z|)/|Z|²` (stated as `E² L (X + |Z|) ≤ 2 D R |Z|²`); then `c = |Z|/L`
works (`forall_phR_posSemidef_optimal_iff`). The unweighted `c = 1` (the study's candidate)
needs `E² (R² + (X + L)²) ≤ 4 D R |Z|²` (`forall_phR_posSemidef_iff`), which implies it. -/
@[tmio M, powerlib_domain] theorem exists_phR_posSemidef_iff (hM : g.M ≠ 0) (hL : 0 < g.L)
    (hR : 0 < g.R) (hZ : 0 < g.absSq) :
    (∃ c, 0 < c ∧ ∀ x, (g.phR c x).PosSemidef) ↔
      g.E ^ 2 * g.L * (g.X + Real.sqrt g.absSq) ≤ 2 * g.D * g.R * g.absSq := by
  constructor
  · rintro ⟨c, hc, h⟩
    have h' := (g.forall_phR_posSemidef_iff hM hL.ne' hR hZ hc).mp h
    have hss := Real.sq_sqrt hZ.le
    set z := Real.sqrt g.absSq
    have hR2 : g.R ^ 2 = z ^ 2 - g.X ^ 2 := by rw [hss]; unfold Network.absSq; ring
    -- `E² (z² + c² L²) ≥ 2 E² z c L`
    have hamgm : 2 * c * g.L * (g.E ^ 2 * (g.X + z)) ≤
        g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) := by
      rw [hR2]
      nlinarith [mul_nonneg (sq_nonneg g.E) (sq_nonneg (z - c * g.L))]
    have h2 : 2 * c * (g.E ^ 2 * g.L * (g.X + z)) ≤ 2 * c * (2 * g.D * g.R * g.absSq) := by
      nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  · intro h
    exact ⟨Real.sqrt g.absSq / g.L, by positivity,
      (g.forall_phR_posSemidef_optimal_iff hM hL hR hZ).mpr h⟩

/-! ## The condition is intrinsic to the energy -/

/-- **Energy balance.** Along the field, `⟨∇H_c, f⟩ = −D ω² − c R |ĩ|² − ω ĩ·w_c(δ)`. -/
@[tmio M, powerlib_domain] theorem phGrad_dotProduct_field (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) (c : ℝ) (x : State 4) :
    WithLp.ofLp (g.phGrad c x) ⬝ᵥ WithLp.ofLp (g.field x) =
      -(g.D * x 1 ^ 2 + c * g.R * ((x 2 - (g.is (x 0)).re) ^ 2 + (x 3 - (g.is (x 0)).im) ^ 2) +
        x 1 * (g.couplingD c (x 0) * (x 2 - (g.is (x 0)).re) +
          g.couplingQ c (x 0) * (x 3 - (g.is (x 0)).im))) := by
  have hP : g.swingParams.Pe (x 0) = g.power (x 0) (g.is (x 0)).re (g.is (x 0)).im :=
    (g.qssPower_eq_polar hZ (x 0)).symm
  obtain ⟨hd, hq⟩ := g.is_line hZ.ne' (x 0)
  have hrd : g.rateD (x 0) (x 2) (x 3) =
      (-g.R * (x 2 - (g.is (x 0)).re) + g.X * (x 3 - (g.is (x 0)).im)) / g.L := by
    rw [Network.rateD]; congr 1; linear_combination -hd
  have hrq : g.rateQ (x 0) (x 2) (x 3) =
      (-g.R * (x 3 - (g.is (x 0)).im) - g.X * (x 2 - (g.is (x 0)).re)) / g.L := by
    rw [Network.rateQ]; congr 1; linear_combination -hq
  simp only [phGrad, field, hP, Network.power_eq, couplingD, couplingQ, hrd, hrq]
  simp [dotProduct, Fin.sum_univ_four]
  field_simp
  ring

/-- **Some structure with the energy `H_c` iff the dissipation condition.** For a weight `c > 0`,
a state-dependent structure `J(x)` skew, `R(x) ⪰ 0` with `(J − R) ∇H_c = f` exists iff
`E² (R² + (X + c L)²) ≤ 4 D c R |Z|²`, whatever the structure (`J_c`, `R_c` is one): any such
structure gives `⟨∇H_c, f⟩ = −∇H_cᵀ R ∇H_c ≤ 0`, and at the state `ω = 2 c R`,
`ĩ = −w_c(0)` the energy balance (`phGrad_dotProduct_field`) is `−c R (4 D c R − |w_c|²)`. -/
@[tmio M, powerlib_domain] theorem exists_structure_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hR : 0 < g.R) (hZ : 0 < g.absSq) {c : ℝ} (hc : 0 < c) :
    (∃ J R : State 4 → Matrix (Fin 4) (Fin 4) ℝ, (∀ x, (J x)ᵀ = -J x) ∧
      (∀ x, (R x).PosSemidef) ∧
      ∀ x, (J x - R x) *ᵥ WithLp.ofLp (g.phGrad c x) = WithLp.ofLp (g.field x)) ↔
      g.E ^ 2 * (g.R ^ 2 + (g.X + c * g.L) ^ 2) ≤ 4 * g.D * c * g.R * g.absSq := by
  constructor
  · rintro ⟨J, R, hJ, hRp, hf⟩
    set wd := g.couplingD c 0
    set wq := g.couplingQ c 0
    set x : State 4 := WithLp.toLp 2 ![0, 2 * c * g.R, (g.is 0).re - wd, (g.is 0).im - wq]
    have hdiss : WithLp.ofLp (g.phGrad c x) ⬝ᵥ WithLp.ofLp (g.field x) ≤ 0 := by
      rw [← hf x]
      set y := WithLp.ofLp (g.phGrad c x)
      have hskew := PH.dotProduct_mulVec_self_eq_zero_of_skew (hJ x) y
      have hpsd : 0 ≤ y ⬝ᵥ (R x *ᵥ y) := by simpa using (hRp x).dotProduct_mulVec_nonneg y
      rw [sub_mulVec, dotProduct_sub, hskew]
      linarith
    rw [g.phGrad_dotProduct_field hM hL hZ] at hdiss
    have hx0 : x 0 = 0 := by simp [x]
    have hx1 : x 1 = 2 * c * g.R := by simp [x]
    have hx2 : x 2 - (g.is (x 0)).re = -wd := by rw [hx0]; simp [x]
    have hx3 : x 3 - (g.is (x 0)).im = -wq := by rw [hx0]; simp [x]
    rw [hx2, hx3, hx1, hx0] at hdiss
    have hn := g.normSq_coupling hZ.ne' c 0
    have hcR : 0 < c * g.R := mul_pos hc hR
    have key : 0 ≤ c * g.R * (4 * g.D * c * g.R - (wd ^ 2 + wq ^ 2)) := by nlinarith
    have h2 := (mul_nonneg_iff_of_pos_left hcR).mp key
    rw [hn, sub_nonneg, div_le_iff₀ hZ] at h2
    linarith
  · intro h
    exact ⟨g.phJ c, g.phR c, g.phJ_skew c,
      (g.forall_phR_posSemidef_iff hM hL hR hZ hc).mpr h, g.phField_eq hM hL hZ hc.ne'⟩

/-! ## The pH model -/

/-- The VSM on the line as a nonlinear pH model with the weighted energy `H_c`, the
angle-dependent structure and the set-point port (input matrix `(0, 1/M, 0, 0)ᵀ`), given
`R_c ⪰ 0` at every state (`exists_phR_posSemidef_iff`). -/
def phModel (c : ℝ) (hR : ∀ x, (g.phR c x).PosSemidef) : PH.NonlinearModel 4 1 where
  J := g.phJ c
  R := g.phR c
  g _ := !![0; 1 / g.M; 0; 0]
  H := g.phEnergy c
  dH := g.phGrad c
  skew := g.phJ_skew c
  dissipation_posSemidef := hR
  hasGradient := g.hasGradientAt_phEnergy c

/-- With input `u` the pH model is the VSM field at the set point `P_ref + u`. -/
@[tmio M, powerlib_domain] theorem phModel_field (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) {c : ℝ} (hc : c ≠ 0) (hR : ∀ x, (g.phR c x).PosSemidef) (x : State 4)
    (u : Fin 1 → ℝ) :
    (g.phModel c hR).field x u = ({ g with Pref := g.Pref + u 0 } : VSM).field x := by
  apply WithLp.ofLp_injective
  rw [PH.NonlinearModel.ofLp_field]
  change (g.phJ c x - g.phR c x) *ᵥ WithLp.ofLp (g.phGrad c x) + !![0; 1 / g.M; 0; 0] *ᵥ u = _
  rw [g.phField_eq hM hL hZ hc x]
  funext i
  fin_cases i
  · simp [field, dotProduct]
  · simp [field, dotProduct]
    field_simp
    ring
  · simp [field, dotProduct, Network.rateD]
  · simp [field, dotProduct, Network.rateQ]

/-- The zero-input field of the pH model is the VSM field. -/
@[tmio M, powerlib_domain] theorem phModel_zeroInputField (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hZ : 0 < g.absSq) {c : ℝ} (hc : c ≠ 0) (hR : ∀ x, (g.phR c x).PosSemidef) :
    (g.phModel c hR).zeroInputField = g.field := by
  funext x
  rw [PH.NonlinearModel.zeroInputField, g.phModel_field hM hL hZ hc hR x 0]
  simp

/-- The collocated output of the set-point port is the frequency deviation `ω`. -/
@[tmio M, powerlib_domain] theorem phModel_output (hM : g.M ≠ 0) {c : ℝ}
    (hR : ∀ x, (g.phR c x).PosSemidef) (x : State 4) :
    (g.phModel c hR).output x = ![x 1] := by
  funext i
  fin_cases i
  simp [PH.NonlinearModel.output, phModel, phGrad, mulVec, dotProduct, Fin.sum_univ_four]
  field_simp

end VSM

end powerlib.GFM.Line
