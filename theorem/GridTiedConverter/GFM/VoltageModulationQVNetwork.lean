import theorem.GridTiedConverter.GFM.VoltageModulationQVHopf

/-! # Dynamic Q–V loop behind a dynamic line: forced orbit and Floquet multipliers

The quasi-static port maps of `VoltageModulationQVHopf` are replaced by a dynamic line
`(X/ω_b) i̇ = E e^{jδ} − V − (R + jX) i` in the grid frame, with the power measured at the EMF. The
operating point carries the quasi-static current, so its powers are exactly `lossyP`, `lossyQ`
(`network_static`). The six-state field is identified with explicit Jacobian, input
`∂_V F = (0, 0, 0, 0, −ω_b/X, 0)` and second derivatives (the Jacobian does not depend on `V`), and
`SmoothForcedOrbit` gives the end-to-end statements. The forced response at `2jΩ` is constructed,
`z = (2jΩ − A₀)⁻¹ V̂ B_V`.

Model boundary.
* States `(δ, Δω, P_f, E, i_d, i_q)` (`nfield`), `P = E(cos δ i_d + sin δ i_q)`,
  `Q = E(sin δ i_d − cos δ i_q)`, constant `R`, `X ≠ 0`, `R² + X² ≠ 0`, base frequency `ω_b`;
  grid voltage `V₀ + εV̂ cos 2Ωt` on the real axis of the grid frame.
* The six-state Jacobian has no closed-form eigen-data: the eigenvectors `r`, `u` of `±jΩ`
  (`u r = 1`), geometric simplicity of `jΩ` and the left-half-plane condition on the other
  eigenvalues are hypotheses on the explicit matrix `njac`.
* The connection to the quasi-static model is at the operating point and its powers
  (`network_static`); the limit `ω_b → ∞` of the multipliers is not stated.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2, §5 (network dynamics and sidebands); the dynamic Q–V loop with a dynamic line
and the voltage excitation are new.

Results.
* `nfield`, `contDiff_nfield`, `njac`, `matX_nfield` — the field and its Jacobian at every state.
* `nid`, `niq`, `network_static`, `nxeq`, `nfield_eq_zero` — the operating point with the
  quasi-static current and powers.
* `Bnet`, `fderivW_nfield`, `ndx`, `smDx_nfield`, `smM1_nfield`, `nA1`, `smA1_nfield` — the
  voltage input, the second derivatives and `A₁(z)`.
* `nz`, `nz_eq` — the forced response at `2jΩ`.
* `orbit_net_stable`, `orbit_net_unstable`, `orbit_net_exp_stable` — end-to-end.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated dynamic Q–V core with a dynamic line.
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)

variable (c : DynQV) (R X ωb : ℝ)

/-- The synchronizing core with a dynamic Q–V loop behind a dynamic `R + jX` line (base frequency
`ω_b`), in the grid frame: states `(δ, Δω, P_f, E, i_d, i_q)`, power at the EMF
`P = E(cos δ i_d + sin δ i_q)`, `Q = E(sin δ i_d − cos δ i_q)`,
`(X/ω_b) i̇ = E e^{jδ} − V − (R + jX) i`. -/
def nfield (Pset Eset Qset : ℝ) (q : (Fin 6 → ℝ) × ℝ) : Fin 6 → ℝ :=
  ![c.ω0 * q.1 1,
    (Pset - q.1 2 - c.D * q.1 1) / (2 * c.H),
    c.ωc * (q.1 3 * (Real.cos (q.1 0) * q.1 4 + Real.sin (q.1 0) * q.1 5) - q.1 2),
    (Eset - q.1 3 - c.kq * (q.1 3 * (Real.sin (q.1 0) * q.1 4 - Real.cos (q.1 0) * q.1 5) - Qset)) /
      c.τ,
    ωb / X * (q.1 3 * Real.cos (q.1 0) - q.2 - R * q.1 4 + X * q.1 5),
    ωb / X * (q.1 3 * Real.sin (q.1 0) - R * q.1 5 - X * q.1 4)]

@[tmio M, powerlib_domain] theorem contDiff_nfield {n : WithTop ℕ∞} (Pset Eset Qset : ℝ) :
    ContDiff ℝ n (c.nfield R X ωb Pset Eset Qset) := by
  have hx : ∀ i : Fin 6, ContDiff ℝ n fun q : (Fin 6 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hc : ContDiff ℝ n fun q : (Fin 6 → ℝ) × ℝ => Real.cos (q.1 0) :=
    Real.contDiff_cos.comp (hx 0)
  have hs : ContDiff ℝ n fun q : (Fin 6 → ℝ) × ℝ => Real.sin (q.1 0) :=
    Real.contDiff_sin.comp (hx 0)
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (hx 1)
  · exact ((contDiff_const.sub (hx 2)).sub (contDiff_const.mul (hx 1))).div_const _
  · exact contDiff_const.mul (((hx 3).mul ((hc.mul (hx 4)).add (hs.mul (hx 5)))).sub (hx 2))
  · exact ((contDiff_const.sub (hx 3)).sub (contDiff_const.mul
      (((hx 3).mul ((hs.mul (hx 4)).sub (hc.mul (hx 5)))).sub contDiff_const))).div_const _
  · exact contDiff_const.mul (((((hx 3).mul hc).sub contDiff_snd).sub
      (contDiff_const.mul (hx 4))).add (contDiff_const.mul (hx 5)))
  · exact contDiff_const.mul ((((hx 3).mul hs).sub (contDiff_const.mul (hx 5))).sub
      (contDiff_const.mul (hx 4)))

/-- The Jacobian of the field at `(x, V)`. -/
def njac (q : (Fin 6 → ℝ) × ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, c.ω0, 0, 0, 0, 0;
    0, -c.D / (2 * c.H), -1 / (2 * c.H), 0, 0, 0;
    c.ωc * (q.1 3 * (-Real.sin (q.1 0) * q.1 4 + Real.cos (q.1 0) * q.1 5)), 0, -c.ωc,
      c.ωc * (Real.cos (q.1 0) * q.1 4 + Real.sin (q.1 0) * q.1 5),
      c.ωc * (q.1 3 * Real.cos (q.1 0)), c.ωc * (q.1 3 * Real.sin (q.1 0));
    -(c.kq * (q.1 3 * (Real.cos (q.1 0) * q.1 4 + Real.sin (q.1 0) * q.1 5))) / c.τ, 0, 0,
      (-1 - c.kq * (Real.sin (q.1 0) * q.1 4 - Real.cos (q.1 0) * q.1 5)) / c.τ,
      -(c.kq * (q.1 3 * Real.sin (q.1 0))) / c.τ, c.kq * (q.1 3 * Real.cos (q.1 0)) / c.τ;
    ωb / X * -(q.1 3 * Real.sin (q.1 0)), 0, 0, ωb / X * Real.cos (q.1 0), ωb / X * -R,
      ωb / X * X;
    ωb / X * (q.1 3 * Real.cos (q.1 0)), 0, 0, ωb / X * Real.sin (q.1 0), ωb / X * -X,
      ωb / X * -R]

@[tmio M, powerlib_domain] theorem matX_nfield (Pset Eset Qset : ℝ) (q : (Fin 6 → ℝ) × ℝ) :
    matX (c.nfield R X ωb Pset Eset Qset) q = c.njac R X ωb q := by
  refine ParametricResonance.ForcedOrbit.matX_of_line
    ((c.contDiff_nfield R X ωb (n := 1) _ _ _).differentiable (by norm_num) _) fun y => ?_
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (q.1 + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (q.1 i)
  have hc : HasDerivAt (fun s : ℝ => Real.cos ((q.1 + s • y) 0))
      (-Real.sin (q.1 0) * y 0) 0 := by simpa using (hl 0).cos
  have hs : HasDerivAt (fun s : ℝ => Real.sin ((q.1 + s • y) 0))
      (Real.cos (q.1 0) * y 0) 0 := by simpa using (hl 0).sin
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine ((hl 1).const_mul c.ω0).congr_deriv ?_
    show _ = (c.njac R X ωb q *ᵥ y) 0
    simp [njac, mulVec, dotProduct, Fin.sum_univ_six]
  · refine ((((hasDerivAt_const (0 : ℝ) Pset).sub (hl 2)).sub
      ((hl 1).const_mul c.D)).div_const (2 * c.H)).congr_deriv ?_
    show _ = (c.njac R X ωb q *ᵥ y) 1
    simp [njac, mulVec, dotProduct, Fin.sum_univ_six]; ring
  · refine ((((hl 3).mul ((hc.mul (hl 4)).add (hs.mul (hl 5)))).sub (hl 2)).const_mul
      c.ωc).congr_deriv ?_
    show _ = (c.njac R X ωb q *ᵥ y) 2
    simp [njac, mulVec, dotProduct, Fin.sum_univ_six]; ring
  · refine ((((hasDerivAt_const (0 : ℝ) Eset).sub (hl 3)).sub
      ((((hl 3).mul ((hs.mul (hl 4)).sub (hc.mul (hl 5)))).sub_const Qset).const_mul
        c.kq)).div_const c.τ).congr_deriv ?_
    show _ = (c.njac R X ωb q *ᵥ y) 3
    simp [njac, mulVec, dotProduct, Fin.sum_univ_six]; ring
  · refine ((((((hl 3).mul hc).sub_const q.2).sub ((hl 4).const_mul R)).add
      ((hl 5).const_mul X)).const_mul (ωb / X)).congr_deriv ?_
    show _ = (c.njac R X ωb q *ᵥ y) 4
    simp [njac, mulVec, dotProduct, Fin.sum_univ_six]; ring
  · refine (((((hl 3).mul hs).sub ((hl 5).const_mul R)).sub
      ((hl 4).const_mul X)).const_mul (ωb / X)).congr_deriv ?_
    show _ = (c.njac R X ωb q *ᵥ y) 5
    simp [njac, mulVec, dotProduct, Fin.sum_univ_six]; ring

/-! ### The operating point -/

/-- The line current at the operating point, `i = (E e^{jδ} − V)/(R + jX)`: real part. -/
def nid (δ0 E0 V0 : ℝ) : ℝ :=
  ((E0 * Real.cos δ0 - V0) * R + E0 * Real.sin δ0 * X) / (R ^ 2 + X ^ 2)

/-- Imaginary part. -/
def niq (δ0 E0 V0 : ℝ) : ℝ :=
  (E0 * Real.sin δ0 * R - (E0 * Real.cos δ0 - V0) * X) / (R ^ 2 + X ^ 2)

omit c ωb in
/-- At the operating point the power at the EMF is the quasi-static power through `R + jX`:
the dynamic line reproduces `lossyP`, `lossyQ`. -/
@[tmio M, powerlib_domain] theorem network_static (hZ : R ^ 2 + X ^ 2 ≠ 0) (δ0 E0 V0 : ℝ) :
    E0 * (Real.cos δ0 * nid R X δ0 E0 V0 + Real.sin δ0 * niq R X δ0 E0 V0) =
        lossyP R X ((δ0, E0), V0) ∧
      E0 * (Real.sin δ0 * nid R X δ0 E0 V0 - Real.cos δ0 * niq R X δ0 E0 V0) =
        lossyQ R X ((δ0, E0), V0) := by
  have h := Real.sin_sq_add_cos_sq δ0
  constructor
  · simp only [nid, niq, lossyP, linkP, linkQ]
    field_simp
    linear_combination (E0 ^ 2 * R) * h
  · simp only [nid, niq, lossyQ, linkP, linkQ]
    field_simp
    linear_combination (E0 ^ 2 * X) * h

/-- The operating point `(δ₀, 0, P, E₀, i_d, i_q)`. -/
def nxeq (δ0 E0 V0 : ℝ) : Fin 6 → ℝ :=
  ![δ0, 0, lossyP R X ((δ0, E0), V0), E0, nid R X δ0 E0 V0, niq R X δ0 E0 V0]

@[tmio M, powerlib_domain] theorem nfield_eq_zero (hZ : R ^ 2 + X ^ 2 ≠ 0) (δ0 E0 V0 : ℝ) :
    c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0, V0) = 0 := by
  obtain ⟨h1, h2⟩ := network_static R X hZ δ0 E0 V0
  funext i
  fin_cases i
  · simp [nfield, nxeq]
  · simp [nfield, nxeq]
  · simp [nfield, nxeq, h1]
  · simp [nfield, nxeq, h2]
  · simp only [nfield, nxeq, nid, niq]; simp; right; field_simp; ring
  · simp only [nfield, nxeq, nid, niq]; simp; right; field_simp; ring

/-- The voltage input `∂_V F = (0, 0, 0, 0, −ω_b/X, 0)`. -/
def Bnet : Fin 6 → ℂ := ![0, 0, 0, 0, -((ωb / X : ℝ) : ℂ), 0]

@[tmio M, powerlib_domain] theorem fderivW_nfield (δ0 E0 V0 : ℝ) :
    ofv (fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1)) = Bnet X ωb := by
  have e : fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1) = ![0, 0, 0, 0, -(ωb / X), 0] := by
    refine ParametricResonance.ForcedOrbit.fderivW_of_line
      ((c.contDiff_nfield R X ωb (n := 1) _ _ _).differentiable (by norm_num) _)
      (hasDerivAt_pi.2 fun i => ?_)
    fin_cases i
    · refine (hasDerivAt_const (0 : ℝ) ((c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) 0)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)
      simp [nfield]
    · refine (hasDerivAt_const (0 : ℝ) ((c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) 1)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)
      simp [nfield]
    · refine (hasDerivAt_const (0 : ℝ) ((c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) 2)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)
      simp [nfield]
    · refine (hasDerivAt_const (0 : ℝ) ((c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) 3)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)
      simp [nfield]
    · have h := (((hasDerivAt_id' (0 : ℝ)).const_add V0).const_sub
        (E0 * Real.cos δ0 - R * nid R X δ0 E0 V0 + X * niq R X δ0 E0 V0)).const_mul (ωb / X)
      refine (h.congr_deriv (show ωb / X * -1 = -(ωb / X) by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)
      simp [nfield, nxeq, -mul_eq_mul_left_iff]; ring
    · refine (hasDerivAt_const (0 : ℝ) ((c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) 5)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)
      simp [nfield]
  rw [e]
  funext i
  fin_cases i <;> simp [ofv, Bnet]

/-- The second derivatives of the field along `y` at the state `x`. -/
def ndx (x y : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    c.ωc * (y 3 * (-Real.sin (x 0) * x 4 + Real.cos (x 0) * x 5) +
      x 3 * (-Real.cos (x 0) * y 0 * x 4 - Real.sin (x 0) * y 4 - Real.sin (x 0) * y 0 * x 5 +
        Real.cos (x 0) * y 5)), 0, 0,
      c.ωc * (-Real.sin (x 0) * y 0 * x 4 + Real.cos (x 0) * y 4 + Real.cos (x 0) * y 0 * x 5 +
        Real.sin (x 0) * y 5),
      c.ωc * (y 3 * Real.cos (x 0) - x 3 * Real.sin (x 0) * y 0),
      c.ωc * (y 3 * Real.sin (x 0) + x 3 * Real.cos (x 0) * y 0);
    -(c.kq * (y 3 * (Real.cos (x 0) * x 4 + Real.sin (x 0) * x 5) +
      x 3 * (-Real.sin (x 0) * y 0 * x 4 + Real.cos (x 0) * y 4 + Real.cos (x 0) * y 0 * x 5 +
        Real.sin (x 0) * y 5))) / c.τ, 0, 0,
      -(c.kq * (Real.cos (x 0) * y 0 * x 4 + Real.sin (x 0) * y 4 + Real.sin (x 0) * y 0 * x 5 -
        Real.cos (x 0) * y 5)) / c.τ,
      -(c.kq * (y 3 * Real.sin (x 0) + x 3 * Real.cos (x 0) * y 0)) / c.τ,
      c.kq * (y 3 * Real.cos (x 0) - x 3 * Real.sin (x 0) * y 0) / c.τ;
    ωb / X * -(y 3 * Real.sin (x 0) + x 3 * Real.cos (x 0) * y 0), 0, 0,
      ωb / X * (-Real.sin (x 0) * y 0), 0, 0;
    ωb / X * (y 3 * Real.cos (x 0) - x 3 * Real.sin (x 0) * y 0), 0, 0,
      ωb / X * (Real.cos (x 0) * y 0), 0, 0]

@[tmio M, powerlib_domain] theorem smDx_nfield (δ0 E0 V0 : ℝ) (y : Fin 6 → ℝ) :
    smDx (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) y = c.ndx X ωb (nxeq R X δ0 E0 V0) y := by
  set x := nxeq R X δ0 E0 V0
  have hl : ∀ i, HasDerivAt (fun t : ℝ => (x + t • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (x i)
  have hc : HasDerivAt (fun t : ℝ => Real.cos ((x + t • y) 0)) (-Real.sin (x 0) * y 0) 0 := by
    simpa using (hl 0).cos
  have hs : HasDerivAt (fun t : ℝ => Real.sin ((x + t • y) 0)) (Real.cos (x 0) * y 0) 0 := by
    simpa using (hl 0).sin
  have hF2 : ContDiffAt ℝ 2 (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (x, V0) := (c.contDiff_nfield R X ωb _ _ _).contDiffAt
  have hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (x + t • y, V0) = c.njac R X ωb (x + t • y, V0) :=
    Filter.Eventually.of_forall fun t => c.matX_nfield R X ωb _ _ _ _
  refine ParametricResonance.ForcedOrbit.smDx_of_line hF2 y hJ fun i j => ?_
  have ev : ∀ {f g : ℝ → ℝ}, (∀ t, f t = g t) → f =ᶠ[𝓝 (0 : ℝ)] g :=
    fun h => Filter.Eventually.of_forall h
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (c.ω0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.D / (2 * c.H) : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-1 / (2 * c.H) : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact ((((hl 3).mul ((hs.neg.mul (hl 4)).add (hc.mul (hl 5)))).const_mul c.ωc).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.ωc : ℝ)
  · exact ((((hc.mul (hl 4)).add (hs.mul (hl 5))).const_mul c.ωc).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact ((((hl 3).mul hc).const_mul c.ωc).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact ((((hl 3).mul hs).const_mul c.ωc).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact ((((((hl 3).mul ((hc.mul (hl 4)).add (hs.mul (hl 5)))).const_mul c.kq).neg).div_const c.τ).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact ((((hasDerivAt_const (0 : ℝ) (-1 : ℝ)).sub (((hs.mul (hl 4)).sub (hc.mul (hl 5))).const_mul c.kq)).div_const c.τ).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact ((((((hl 3).mul hs).const_mul c.kq).neg).div_const c.τ).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact (((((hl 3).mul hc).const_mul c.kq).div_const c.τ).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact (((((hl 3).mul hs).neg).const_mul (ωb / X)).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact ((hc.const_mul (ωb / X)).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff])).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact hasDerivAt_const (0 : ℝ) (ωb / X * -R : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (ωb / X * X : ℝ)
  · exact ((((hl 3).mul hc).const_mul (ωb / X)).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]; ring)).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact ((hs.const_mul (ωb / X)).congr_deriv (by simp [ndx, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff])).congr_of_eventuallyEq
      (ev fun t => by simp [njac])
  · exact hasDerivAt_const (0 : ℝ) (ωb / X * -X : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (ωb / X * -R : ℝ)

@[tmio M, powerlib_domain] theorem smM1_nfield (δ0 E0 V0 : ℝ) :
    smM1 (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) = 0 := by
  have hF2 : ContDiffAt ℝ 2 (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) :=
    (c.contDiff_nfield R X ωb _ _ _).contDiffAt
  have hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0 + t) =
      c.njac R X ωb (nxeq R X δ0 E0 V0, V0 + t) :=
    Filter.Eventually.of_forall fun t => c.matX_nfield R X ωb _ _ _ _
  refine ParametricResonance.ForcedOrbit.smM1_of_line hF2 hJ fun i j => ?_
  have e : (fun t => c.njac R X ωb (nxeq R X δ0 E0 V0, V0 + t) i j) =
      fun _ => c.njac R X ωb (nxeq R X δ0 E0 V0, V0) i j := rfl
  rw [e]
  exact hasDerivAt_const _ _

/-- The modulation `A₁ = D_x(∂ₓF)[z]` of the network field along a complex direction `z` (the
grid voltage does not enter the Jacobian). -/
def nA1 (x : Fin 6 → ℝ) (z : Fin 6 → ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    c.ωc * (z 3 * (-Real.sin (x 0) * x 4 + Real.cos (x 0) * x 5) +
      x 3 * (-Real.cos (x 0) * z 0 * x 4 - Real.sin (x 0) * z 4 - Real.sin (x 0) * z 0 * x 5 +
        Real.cos (x 0) * z 5)), 0, 0,
      c.ωc * (-Real.sin (x 0) * z 0 * x 4 + Real.cos (x 0) * z 4 + Real.cos (x 0) * z 0 * x 5 +
        Real.sin (x 0) * z 5),
      c.ωc * (z 3 * Real.cos (x 0) - x 3 * Real.sin (x 0) * z 0),
      c.ωc * (z 3 * Real.sin (x 0) + x 3 * Real.cos (x 0) * z 0);
    -(c.kq * (z 3 * (Real.cos (x 0) * x 4 + Real.sin (x 0) * x 5) +
      x 3 * (-Real.sin (x 0) * z 0 * x 4 + Real.cos (x 0) * z 4 + Real.cos (x 0) * z 0 * x 5 +
        Real.sin (x 0) * z 5))) / c.τ, 0, 0,
      -(c.kq * (Real.cos (x 0) * z 0 * x 4 + Real.sin (x 0) * z 4 + Real.sin (x 0) * z 0 * x 5 -
        Real.cos (x 0) * z 5)) / c.τ,
      -(c.kq * (z 3 * Real.sin (x 0) + x 3 * Real.cos (x 0) * z 0)) / c.τ,
      c.kq * (z 3 * Real.cos (x 0) - x 3 * Real.sin (x 0) * z 0) / c.τ;
    ((ωb / X : ℝ) : ℂ) * -(z 3 * Real.sin (x 0) + x 3 * Real.cos (x 0) * z 0), 0, 0,
      ((ωb / X : ℝ) : ℂ) * (-Real.sin (x 0) * z 0), 0, 0;
    ((ωb / X : ℝ) : ℂ) * (z 3 * Real.cos (x 0) - x 3 * Real.sin (x 0) * z 0), 0, 0,
      ((ωb / X : ℝ) : ℂ) * (Real.cos (x 0) * z 0), 0, 0]

@[tmio M, powerlib_domain] theorem smA1_nfield (δ0 E0 V0 Vh : ℝ) (z : Fin 6 → ℂ) :
    smA1 (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) Vh z = c.nA1 X ωb (nxeq R X δ0 E0 V0) z := by
  have hdx := c.smDx_nfield R X ωb δ0 E0 V0
  have hm := c.smM1_nfield R X ωb δ0 E0 V0
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC, hdx, hm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, map_zero,
    smul_zero, add_zero]
  generalize nxeq R X δ0 E0 V0 = x
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [ndx, nA1, Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im,
      Complex.cos_ofReal_im, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]

/-- The forced response of the network core at `2jΩ`: `z = (2jΩ − A₀)⁻¹ V̂ B_V`. -/
def nz (δ0 E0 V0 Ω Vh : ℝ) : Fin 6 → ℂ :=
  ((((2 * Ω : ℝ) : ℂ) * I) • (1 : Matrix (Fin 6) (Fin 6) ℂ) - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ))⁻¹ *ᵥ
    ((Vh : ℂ) • Bnet X ωb)

/-- When `2jΩ` is not an eigenvalue (in particular when every eigenvalue other than `±jΩ` has
negative real part), `nz` solves `(2jΩ − A₀) z = V̂ B_V`. -/
@[tmio M, powerlib_domain] theorem nz_eq {δ0 E0 V0 Ω : ℝ} (hΩ : Ω ≠ 0)
    (hstab : ∀ (μ : ℂ) (v : Fin 6 → ℂ), v ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0) (Vh : ℝ) :
    (((2 * Ω : ℝ) : ℂ) * I) • c.nz R X ωb δ0 E0 V0 Ω Vh -
        (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ c.nz R X ωb δ0 E0 V0 Ω Vh = (Vh : ℂ) • Bnet X ωb := by
  set M := (((2 * Ω : ℝ) : ℂ) * I) • (1 : Matrix (Fin 6) (Fin 6) ℂ) - (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ)
    with hM
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have hAv : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = (((2 * Ω : ℝ) : ℂ) * I) • v := by
      rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
      exact hMv.symm
    have h1 : (((2 * Ω : ℝ) : ℂ) * I) ≠ (Ω : ℂ) * I := by
      intro h0; have := congrArg Complex.im h0; simp at this; exact hΩ (by linarith)
    have h2 : (((2 * Ω : ℝ) : ℂ) * I) ≠ -((Ω : ℂ) * I) := by
      intro h0; have := congrArg Complex.im h0; simp at this; exact hΩ (by linarith)
    have := hstab _ v hv hAv h1 h2
    simp at this
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  have hz : M *ᵥ c.nz R X ωb δ0 E0 V0 Ω Vh = (Vh : ℂ) • Bnet X ωb := by
    simp only [nz]
    rw [← hM, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  rw [← hz, hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The synchronizing core with a dynamic Q–V loop behind a dynamic `R + jX` line, grid-voltage
modulation, end-to-end, stability. The operating point is the quasi-static one
(`network_static`); the critical pair `±jΩ` of the six-state Jacobian is simple with eigenvectors
`r`, `u`, and every other eigenvalue lies in the open left half plane; `z = nz` is the forced
response at `2jΩ`. Then `Re λ₁ < 0` and `|g_V/2| < |λ₁|` (`g_V = u A₁(z) r̄`) give, for all small
`ε > 0`, the forced periodic orbit with all Floquet multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_net_stable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ v : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v →
      v = (u ⬝ᵥ v) • r)
    (hstab : ∀ (μ : ℂ) (v : Fin 6 → ℂ), v ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (Vh : ℝ)
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0) (hg : ‖u ⬝ᵥ (c.nA1 X ωb (nxeq R X δ0 E0 V0) (c.nz R X ωb δ0 E0 V0 Ω Vh) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 6 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hm : matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) = (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)) :=
    c.matX_nfield R X ωb _ _ _ _
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 6) (m := 4) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz' : (((2 * Ω : ℝ) : ℂ) * I) • c.nz R X ωb δ0 E0 V0 Ω Vh -
      (matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        c.nz R X ωb δ0 E0 V0 Ω Vh =
      (Vh : ℂ) • fun i => ((fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ) := by
    have hb : (fun i => ((fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ)) =
        Bnet X ωb := c.fderivW_nfield R X ωb δ0 E0 V0
    rw [hm, hb]; exact c.nz_eq R X ωb hΩ.ne' hstab Vh
  have hA1 := c.smA1_nfield R X ωb δ0 E0 V0 Vh (c.nz R X ωb δ0 E0 V0 Ω Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable
    (c.contDiff_nfield R X ωb _ _ _).contDiffAt (c.nfield_eq_zero R X ωb hZ δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz' A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

/-- The dynamic-network core, end-to-end, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_net_unstable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ v : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v →
      v = (u ⬝ᵥ v) • r)
    (hstab : ∀ (μ : ℂ) (v : Fin 6 → ℂ), v ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (Vh : ℝ)
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ (c.nA1 X ωb (nxeq R X δ0 E0 V0) (c.nz R X ωb δ0 E0 V0 Ω Vh) *ᵥ star r) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t
          (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hm : matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) = (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)) :=
    c.matX_nfield R X ωb _ _ _ _
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 6) (m := 4) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz' : (((2 * Ω : ℝ) : ℂ) * I) • c.nz R X ωb δ0 E0 V0 Ω Vh -
      (matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        c.nz R X ωb δ0 E0 V0 Ω Vh =
      (Vh : ℂ) • fun i => ((fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ) := by
    have hb : (fun i => ((fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ)) =
        Bnet X ωb := c.fderivW_nfield R X ωb δ0 E0 V0
    rw [hm, hb]; exact c.nz_eq R X ωb hΩ.ne' hstab Vh
  have hA1 := c.smA1_nfield R X ωb δ0 E0 V0 Vh (c.nz R X ωb δ0 E0 V0 Ω Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable
    (c.contDiff_nfield R X ωb _ _ _).contDiffAt (c.nfield_eq_zero R X ωb hZ δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz' A0' ?_
  rw [hL, hR, hA1]; exact hg

/-- The dynamic-network core: the forced orbit exists and is locally exponentially stable for the
nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_net_exp_stable
    (hZ : R ^ 2 + X ^ 2 ≠ 0) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω) {r u : Fin 6 → ℂ}
    (hr : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hsimple : ∀ v : Fin 6 → ℂ, (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v →
      v = (u ⬝ᵥ v) • r)
    (hstab : ∀ (μ : ℂ) (v : Fin 6 → ℂ), v ≠ 0 → (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
      μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0)
    (Vh : ℝ)
    (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0) (hg : ‖u ⬝ᵥ (c.nA1 X ωb (nxeq R X δ0 E0 V0) (c.nz R X ωb δ0 E0 V0 Ω Vh) *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
        V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 6 → ℝ),
        IsIntegralCurveOn x (fun t v => c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + v,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm : matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) = (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)) :=
    c.matX_nfield R X ωb _ _ _ _
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR, hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 6) (m := 4) rfl hΩ.ne' hr hu hur
      hsimple hstab (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz' : (((2 * Ω : ℝ) : ℂ) * I) • c.nz R X ωb δ0 E0 V0 Ω Vh -
      (matX (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
        c.nz R X ωb δ0 E0 V0 Ω Vh =
      (Vh : ℂ) • fun i => ((fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ) := by
    have hb : (fun i => ((fderiv ℝ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ)) =
        Bnet X ωb := c.fderivW_nfield R X ωb δ0 E0 V0
    rw [hm, hb]; exact c.nz_eq R X ωb hΩ.ne' hstab Vh
  have hA1 := c.smA1_nfield R X ωb δ0 E0 V0 Vh (c.nz R X ωb δ0 E0 V0 Ω Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable
    (c.contDiff_nfield R X ωb _ _ _).contDiffAt (c.nfield_eq_zero R X ωb hZ δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz' A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, hA1]; exact hg

end DynQV
end VoltageModulation
end powerlib.GFM
