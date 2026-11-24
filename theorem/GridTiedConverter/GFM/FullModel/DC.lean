import theorem.GridTiedConverter.GFM.FullModel.Basic
import theorem.SpecialFunctions.Sinusoid

/-! # The 16-state grid-forming converter with a DC link: bridge power and equilibria

Model boundary.
* State `x : State 16`: the 13 coordinates of the AC model of
  `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (`x 0 … x 12`, same order, frames,
  directions and per-unit powers: currents out of the converter positive, export-positive power),
  followed by `x 13 = v_dc` (DC-link voltage), `x 14 = ξ_dc` (DC-voltage PI integrator),
  `x 15 = v_f` (filtered DC voltage).
* DC side, continuous time: `C_dc v_dc v̇_dc = P_dc − P_br` (constant-power source `P_dc` into the
  link, bridge power `P_br = Re(u i*)` drawn by an ideal averaged, lossless bridge whose AC voltage
  `u` is not limited by `v_dc`), DC-voltage PI on the filtered voltage setting the active-power
  reference of the VSM, `P_ref(x) = P_ref + K_pdc (v_f − v_ref) + K_idc ξ_dc` (`powerRef`),
  `ξ̇_dc = v_f − v_ref`, `v̇_f = ω_f (v_dc − v_f)`. The AC rows are those of the 13-state field
  with the set-point `P_ref` replaced by `P_ref(x)`.
* Excluded: modulation limits and the dependence of `u` on `v_dc`, switching losses, DC-source
  dynamics, current limiting, PLL, delays, PWM. Level: the bridge power on the quasi-steady set
  and the equilibrium set; no stability statement.

Source: GFM counterpart study, full-order model note (t5 (d): the 16-state DC variant,
`P_br = c_br + A_br sin(δ − α_br)`, two angle branches iff `|P_dc − c_br| ≤ A_br`); the DC-link
model of `theorem/GridTiedConverter/GFL/LCLine/FullModelDC.lean` (the GFL counterpart).

Results.
* `Params.PbrQ_eq`: on the quasi-steady set the bridge power is a single harmonic of `δ`,
  `P_br = c_br(E) + E |κ| sin(δ + arg(jκ))` (`bridgeOffset`, `bridgeCoeff`): the PCC power plus
  the filter loss, both quadratic in the phasor `E e^{jδ}`, contain no `2δ` term.
* `DCParams.fastAtRest_iff`: the ten fast rows vanish iff the AC core of the state is the
  quasi-steady state of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean`;
  `DCParams.Pbr_eq_PbrQ`: there the bridge power is the quasi-steady one.
* `DCParams.field_eq_zero_iff`: the equilibria are the quasi-steady states with
  `v_dc = v_f = v_ref`, `P_br(δ*, E*) = P_dc`, the AC balance `P(δ*, E*) = P_ref + K_idc ξ_dc*`
  and `Q(δ*, E*) = Q*`; `DCParams.exists_equilibrium_iff` (`n_q = 0`, `K_idc ≠ 0`): an equilibrium
  exists iff `|P_dc − c_br(E₀)| ≤ |E₀ |κ||` — the angle branches are the zeros of one sinusoid
  (`SpecialFunctions.exists_sinusoid_zero_iff_abs`).

Family and connection conclusions.
The module states no behaviour of the field: it has no Family and every result is static
evidence on the model.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex ComplexConjugate
open powerlib.Dynamics (State)

/-- `Re((μZ + ν)(αZ + β)*) = |Z|² Re(μα*) + Re(νβ*) + Re((μβ* + ν*α) Z)`: the real part of the
product of two affine functions of a phasor has no second harmonic. -/
@[tmio T, powerlib_foundation] private theorem re_affine_mul_conj (μ ν α β Z : ℂ) :
    ((μ * Z + ν) * conj (α * Z + β)).re = Complex.normSq Z * (μ * conj α).re +
      (ν * conj β).re + ((μ * conj β + conj ν * α) * Z).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

/-- `Re(w e^{jδ}) = |w| sin(δ + arg(jw))`. -/
@[tmio T, powerlib_foundation] private theorem re_mul_ej (w : ℂ) (δ : ℝ) :
    (w * ej δ).re = ‖w‖ * Real.sin (δ + Complex.arg (I * w)) := by
  have hc := Complex.norm_mul_cos_arg (I * w)
  have hs := Complex.norm_mul_sin_arg (I * w)
  rw [norm_mul, Complex.norm_I, one_mul] at hc hs
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, zero_add] at hc hs
  rw [ej, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_add]
  linear_combination (-Real.cos δ) * hs + (-Real.sin δ) * hc

namespace Params

variable (p : Params)

/-- Bridge power on the quasi-steady set with internal EMF `E`, `Re(u i*)` with
`u = v_c + Z_f i` (the filter row at rest). -/
def PbrQ (δ E : ℝ) : ℝ := ((p.vcQ δ E + p.Zf * p.iQ δ E) * conj (p.iQ δ E)).re

/-- The coefficient `μ` of the bridge voltage `u = μ E e^{jδ} + ν` on the quasi-steady set. -/
def bridgeMu : ℂ := (p.Zg + p.Zf * (1 + p.Bf * I * p.Zg)) / p.Zt
/-- The constant `ν` of the bridge voltage on the quasi-steady set. -/
def bridgeNu : ℂ := p.V * (p.Zv + p.Zf * (p.Bf * I * p.Zv - 1)) / p.Zt
/-- The coefficient `α` of the filter current `i = α E e^{jδ} + β` on the quasi-steady set. -/
def currentAl : ℂ := (1 + p.Bf * I * p.Zg) / p.Zt
/-- The constant `β` of the filter current on the quasi-steady set. -/
def currentBe : ℂ := p.V * (p.Bf * I * p.Zv - 1) / p.Zt

/-- The constant part `c_br(E) = E² Re(μα*) + Re(νβ*)` of the quasi-steady bridge power. -/
def bridgeOffset (E : ℝ) : ℝ :=
  E ^ 2 * (p.bridgeMu * conj p.currentAl).re + (p.bridgeNu * conj p.currentBe).re

/-- The harmonic coefficient `κ = μβ* + ν*α` of the quasi-steady bridge power. -/
def bridgeCoeff : ℂ := p.bridgeMu * conj p.currentBe + conj p.bridgeNu * p.currentAl

/-- On the quasi-steady set the bridge power is a single harmonic of `δ`:
`P_br = c_br(E) + E |κ| sin(δ + arg(jκ))`. -/
@[tmio M, powerlib_domain] theorem PbrQ_eq (hZt : p.Zt ≠ 0) (δ E : ℝ) :
    p.PbrQ δ E = p.bridgeOffset E +
      E * ‖p.bridgeCoeff‖ * Real.sin (δ + Complex.arg (I * p.bridgeCoeff)) := by
  have hZv : p.Zv = p.Zt - p.Zg := by rw [Zt]; ring
  have hu : p.vcQ δ E + p.Zf * p.iQ δ E = p.bridgeMu * (E * ej δ) + p.bridgeNu := by
    simp only [vcQ, iQ, igQ, bridgeMu, bridgeNu, hZv]
    field_simp
    ring
  have hi : p.iQ δ E = p.currentAl * (E * ej δ) + p.currentBe := by
    simp only [vcQ, iQ, igQ, currentAl, currentBe, hZv]
    field_simp
    ring
  have hn : Complex.normSq (E * ej δ) = E ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, ej, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    ring
  rw [PbrQ, hu, hi, re_affine_mul_conj, hn, bridgeOffset, ← bridgeCoeff,
    show p.bridgeCoeff * (E * ej δ) = E * (p.bridgeCoeff * ej δ) by ring,
    Complex.re_ofReal_mul, re_mul_ej]
  ring

end Params

/-- Parameters of the 16-state model: the AC model and the DC link with its voltage loop. -/
structure DCParams extends Params where
  /-- DC-link capacitance `C_dc`. -/
  Cdc : ℝ
  /-- Power `P_dc` delivered by the DC source into the link. -/
  Pdc : ℝ
  /-- DC-voltage reference `v_ref`. -/
  vref : ℝ
  /-- DC-voltage proportional gain `K_pdc`. -/
  Kpdc : ℝ
  /-- DC-voltage integral gain `K_idc`. -/
  Kidc : ℝ
  /-- Bandwidth `ω_f` of the DC-voltage measurement filter. -/
  ωf : ℝ

namespace DCParams

variable (q : DCParams)

/-- The AC core `(x 0, …, x 12)` of a 16-state vector. -/
def core (x : State 16) : State 13 := WithLp.toLp 2 fun i : Fin 13 => x (Fin.castAdd 3 i)

/-- The 16-state vector with AC core `y` and DC coordinates `(v_dc, ξ_dc, v_f)`. -/
def join (y : State 13) (vdc ξdc vf : ℝ) : State 16 := WithLp.toLp 2 (Fin.append y ![vdc, ξdc, vf])

@[tmio M, simp, powerlib_domain] theorem core_join (y : State 13) (a b c : ℝ) :
    core (join y a b c) = y := by
  ext i; exact Fin.append_left _ _ _

/-- Active-power reference set by the DC-voltage PI,
`P_ref(x) = P_ref + K_pdc (v_f − v_ref) + K_idc ξ_dc`. -/
def powerRef (x : State 16) : ℝ := q.Pref + q.Kpdc * (x 15 - q.vref) + q.Kidc * x 14

/-- Bridge power `P_br = Re(u i*)`. -/
def Pbr (x : State 16) : ℝ := (q.uBridge (core x) * conj (convCurrent (core x))).re

/-- The complete 16-state field: the 13 AC rows with the VSM set-point `P_ref` replaced by the
DC-loop reference `P_ref(x)`, then the DC rows. -/
def field (x : State 16) : State 16 :=
  WithLp.toLp 2 (Fin.append
    (Function.update (fun i : Fin 13 => q.toParams.field (core x) i) 11
      ((q.powerRef x - Pe (core x) - q.D * x 11) / q.M))
    ![(q.Pdc - q.Pbr x) / (q.Cdc * x 13), x 15 - q.vref, q.ωf * (x 13 - x 15)])

@[tmio M, powerlib_domain] private theorem field_castAdd (x : State 16) (j : Fin 13) :
    q.field x (Fin.castAdd 3 j) = Function.update (fun i : Fin 13 => q.toParams.field (core x) i)
      11 ((q.powerRef x - Pe (core x) - q.D * x 11) / q.M) j := by
  show Fin.append _ _ (Fin.castAdd 3 j) = _
  exact Fin.append_left _ _ _

@[tmio M, powerlib_domain] private theorem field_fast (x : State 16) (j : Fin 13)
    (hj : j ≠ 11) : q.field x (Fin.castAdd 3 j) = q.toParams.field (core x) j := by
  rw [field_castAdd, Function.update_of_ne hj]

/-- The ten fast rows of the 16-state field vanish iff its AC core is the quasi-steady state at
its own slow coordinates (`Params.fastAtRest_iff`). -/
@[tmio M, powerlib_domain] theorem fastAtRest_iff (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0)
    (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (x : State 16) :
    (∀ i : Fin 16, i.val < 10 → q.field x i = 0) ↔
      core x = q.qssState (x 10) (x 11) (x 12) := by
  change _ ↔ core x = q.qssState ((core x) 10) ((core x) 11) ((core x) 12)
  rw [← q.toParams.fastAtRest_iff hLf hCf hLg hKic hKiv hZt (core x)]
  constructor
  · intro h j hj
    rw [← q.field_fast x j (by intro e; rw [e] at hj; simp at hj)]
    exact h _ (by simpa using hj)
  · intro h i hi
    have := q.field_fast x ⟨i.val, by omega⟩ (by intro e; rw [Fin.ext_iff] at e; simp at e; omega)
    rw [show (Fin.castAdd 3 ⟨i.val, by omega⟩ : Fin 16) = i from Fin.ext rfl] at this
    rw [this]
    exact h _ hi

/-- On the quasi-steady set the bridge power is the quasi-steady bridge power `Params.PbrQ`
(the filter row at rest gives `u = v_c + Z_f i`). -/
@[tmio M, powerlib_domain] theorem Pbr_eq_PbrQ (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0)
    (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (x : State 16)
    (hx : core x = q.qssState (x 10) (x 11) (x 12)) :
    q.Pbr x = q.PbrQ (x 10) (q.emf (x 12)) := by
  have hfast := (q.toParams.fastAtRest_iff hLf hCf hLg hKic hKiv hZt (core x)).mpr hx
  have h0 : (q.convRow (core x)).re = 0 := hfast 0 (by decide)
  have h1 : (q.convRow (core x)).im = 0 := hfast 1 (by decide)
  have hrow : q.convRow (core x) = 0 := Complex.ext h0 h1
  have hLf' : (q.Lf : ℂ) ≠ 0 := by exact_mod_cast hLf
  rw [Params.convRow, div_eq_zero_iff, or_iff_left hLf', sub_sub, sub_eq_zero] at hrow
  rw [Pbr, hrow, hx]
  simp [convCurrent, capVoltage, phasor, Params.qssState, Params.PbrQ]

@[tmio M, powerlib_domain] private theorem field_natAdd (x : State 16) (k : Fin 3) :
    q.field x (Fin.natAdd 13 k) =
      ![(q.Pdc - q.Pbr x) / (q.Cdc * x 13), x 15 - q.vref, q.ωf * (x 13 - x 15)] k := by
  show Fin.append _ _ (Fin.natAdd 13 k) = _
  exact Fin.append_right _ _ _

@[tmio M, powerlib_domain] private theorem field_13 (x : State 16) :
    q.field x 13 = (q.Pdc - q.Pbr x) / (q.Cdc * x 13) := by
  exact q.field_natAdd x 0

@[tmio M, powerlib_domain] private theorem field_14 (x : State 16) :
    q.field x 14 = x 15 - q.vref := by
  exact q.field_natAdd x 1

@[tmio M, powerlib_domain] private theorem field_15 (x : State 16) :
    q.field x 15 = q.ωf * (x 13 - x 15) := by
  exact q.field_natAdd x 2

/-- The equilibria of the 16-state field: the AC core is a quasi-steady state `qssState δ* 0 Q*`,
`v_dc = v_f = v_ref`, the bridge power balances the source, `P_br(δ*, E*) = P_dc`, and the AC side
balances at the integrator's set-point, `P(δ*, E*) = P_ref + K_idc ξ_dc*`, `Q(δ*, E*) = Q*`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0)
    (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (hM : q.M ≠ 0)
    (hωq : q.ωq ≠ 0) (hCdc : q.Cdc ≠ 0) (hvref : q.vref ≠ 0) (hωf : q.ωf ≠ 0) (x : State 16) :
    q.field x = 0 ↔ ∃ δ Qf, core x = q.qssState δ 0 Qf ∧ x 13 = q.vref ∧ x 15 = q.vref ∧
      q.Pq δ (q.emf Qf) = q.Pref + q.Kidc * x 14 ∧ q.Qq δ (q.emf Qf) = Qf ∧
      q.PbrQ δ (q.emf Qf) = q.Pdc := by
  have hcore : ∀ y : State 16, core y 10 = y 10 ∧ core y 11 = y 11 ∧ core y 12 = y 12 :=
    fun y => ⟨rfl, rfl, rfl⟩
  have hrow : ∀ y : State 16, (∀ i, q.field y i = 0) ↔
      ((∀ i : Fin 16, i.val < 10 → q.field y i = 0) ∧ y 11 = 0 ∧
        (q.powerRef y - Pe (core y) - q.D * y 11) / q.M = 0 ∧ q.ωq * (Qe (core y) - y 12) = 0 ∧
        q.field y 13 = 0 ∧ q.field y 14 = 0 ∧ q.field y 15 = 0) := by
    intro y
    have h10 : q.field y 10 = y 11 := by
      rw [show (10 : Fin 16) = Fin.castAdd 3 (10 : Fin 13) from rfl, q.field_fast y 10 (by decide)]
      rfl
    have h11 : q.field y 11 = (q.powerRef y - Pe (core y) - q.D * y 11) / q.M := by
      rw [show (11 : Fin 16) = Fin.castAdd 3 (11 : Fin 13) from rfl, field_castAdd,
        Function.update_self]
      rfl
    have h12 : q.field y 12 = q.ωq * (Qe (core y) - y 12) := by
      rw [show (12 : Fin 16) = Fin.castAdd 3 (12 : Fin 13) from rfl, q.field_fast y 12 (by decide)]
      rfl
    constructor
    · intro h
      exact ⟨fun i _ => h i, by rw [← h10]; exact h 10, by rw [← h11]; exact h 11,
        by rw [← h12]; exact h 12, h 13, h 14, h 15⟩
    · rintro ⟨hf, ha, hb, hc, hd, he, hg⟩ i
      fin_cases i
      iterate 10 · exact hf _ (by decide)
      · show q.field y 10 = 0; rw [h10]; exact ha
      · show q.field y 11 = 0; rw [h11]; exact hb
      · show q.field y 12 = 0; rw [h12]; exact hc
      · exact hd
      · exact he
      · exact hg
  have hx0 : ∀ y : State 16, q.field y = 0 ↔ ∀ i, q.field y i = 0 := fun y => by
    constructor
    · intro h i; rw [h]; rfl
    · intro h; ext i; exact h i
  rw [hx0, hrow, q.fastAtRest_iff hLf hCf hLg hKic hKiv hZt x, field_13, field_14, field_15]
  constructor
  · rintro ⟨hq, h11, hP, hQ, hbr, h15, h13⟩
    rw [sub_eq_zero] at h15
    rw [mul_eq_zero, or_iff_right hωf, sub_eq_zero, h15] at h13
    rw [div_eq_zero_iff, or_iff_left (mul_ne_zero hCdc (by rw [h13]; exact hvref)),
      sub_eq_zero] at hbr
    rw [div_eq_zero_iff, or_iff_left hM, h11, mul_zero, sub_zero, hq, q.Pe_qssState,
      sub_eq_zero] at hP
    rw [mul_eq_zero, or_iff_right hωq, hq, q.Qe_qssState, sub_eq_zero] at hQ
    refine ⟨x 10, x 12, by rw [hq, h11], h13, h15, ?_, hQ, ?_⟩
    · rw [← hP, powerRef, h15]; ring
    · rw [hbr, q.Pbr_eq_PbrQ hLf hCf hLg hKic hKiv hZt x hq]
  · rintro ⟨δ, Qf, hq, h13, h15, hP, hQ, hbr⟩
    have hδ : x 10 = δ := by
      have := congrArg (· 10) hq; simpa [core] using this
    have hω : x 11 = 0 := by
      have := congrArg (· 11) hq; simpa [core] using this
    have hQf : x 12 = Qf := by
      have := congrArg (· 12) hq; simpa [core] using this
    have hq' : core x = q.qssState (x 10) (x 11) (x 12) := by rw [hδ, hω, hQf]; exact hq
    refine ⟨hq', hω, ?_, ?_, ?_, by rw [h15, sub_self], by rw [h13, h15, sub_self, mul_zero]⟩
    · rw [hω, mul_zero, sub_zero, hq, q.Pe_qssState, hP, powerRef, h15]; ring_nf
    · rw [hq, q.Qe_qssState, hQ, hQf, sub_self, mul_zero]
    · rw [q.Pbr_eq_PbrQ hLf hCf hLg hKic hKiv hZt x hq', hδ, hQf, hbr, sub_self, zero_div]

/-- Equilibrium existence without droop (`n_q = 0`, `K_idc ≠ 0`): the 16-state field has an
equilibrium iff `|P_dc − c_br(E₀)| ≤ |E₀ |κ||`, the angle branches being the zeros of the single
sinusoid `P_dc − P_br(δ, E₀)` (`Params.PbrQ_eq`, `SpecialFunctions.exists_sinusoid_zero_iff_abs`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem exists_equilibrium_iff (hLf : q.Lf ≠ 0) (hCf : q.Cf ≠ 0)
    (hLg : q.Lg ≠ 0) (hKic : q.Kic ≠ 0) (hKiv : q.Kiv ≠ 0) (hZt : q.Zt ≠ 0) (hM : q.M ≠ 0)
    (hωq : q.ωq ≠ 0) (hCdc : q.Cdc ≠ 0) (hvref : q.vref ≠ 0) (hωf : q.ωf ≠ 0)
    (hnq : q.nq = 0) (hKidc : q.Kidc ≠ 0) :
    (∃ x, q.field x = 0) ↔
      |q.Pdc - q.bridgeOffset q.E0| ≤ |q.E0 * ‖q.bridgeCoeff‖| := by
  have hE : ∀ Qf, q.emf Qf = q.E0 := fun Qf => by simp [Params.emf, hnq]
  have hsin : ∀ δ, q.Pdc - q.bridgeOffset q.E0 - q.E0 * ‖q.bridgeCoeff‖ *
      Real.sin (δ + Complex.arg (I * q.bridgeCoeff)) = q.Pdc - q.PbrQ δ q.E0 := fun δ => by
    rw [q.PbrQ_eq hZt]; ring
  rw [← SpecialFunctions.exists_sinusoid_zero_iff_abs (φ := Complex.arg (I * q.bridgeCoeff))]
  simp only [hsin, sub_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨δ, Qf, -, -, -, -, -, hbr⟩ :=
      (q.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq hCdc hvref hωf x).mp hx
    exact ⟨δ, by rw [← hE Qf]; exact hbr.symm⟩
  · rintro ⟨δ, hδ⟩
    refine ⟨join (q.qssState δ 0 (q.Qq δ q.E0)) q.vref ((q.Pq δ q.E0 - q.Pref) / q.Kidc) q.vref,
      (q.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq hCdc hvref hωf _).mpr
        ⟨δ, q.Qq δ q.E0, core_join _ _ _ _, rfl, rfl, ?_, by rw [hE], by rw [hE]; exact hδ.symm⟩⟩
    rw [hE]
    show q.Pq δ q.E0 = q.Pref + q.Kidc * ((q.Pq δ q.E0 - q.Pref) / q.Kidc)
    field_simp
    ring

end DCParams

end powerlib.GFM.FullModel
