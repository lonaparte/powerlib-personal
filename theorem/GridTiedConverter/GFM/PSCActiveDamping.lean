import theorem.GridTiedConverter.GFM.PSCPump

/-! # PSC with a high-pass active resistance: the synchronizing transfer and the damping budget (13)

The power-synchronization loop with the active-damping branch `−r_a(i − ℓ)`,
`ℓ̇ = α_d(i − ℓ)`, on a quasi-static network: the linearized branch, the closed form of the
frequency-dependent synchronizing coefficient `K(s)` of `D_PSC(s) = s(s + ω_f) + k ω_f K(s)`,
its lag at the mode frequency (exact form of the active-damping term `F_i` of (13)), the exact
damping identity behind (13), and the eigenvectors of the linearization.

Model boundary.
* Converter frame, quasi-static network: the converter EMF `E` (real), the grid voltage
  `V e^{−jδ}`, the series impedance `R + jX` and the active resistance `r_a`; the current is
  `i_c = (E + r_a ℓ − V e^{−jδ})/Z`, `Z = R + r_a + jX` (`current`), the high-pass state obeys
  `ℓ̇ = α_d(i_c − ℓ)`, the power fed to the low-pass is the EMF power `p = Re(E ī_c)`, and
  `δ̇ = k(p* − p_f)`, `ṗ_f = ω_f(p − p_f)` with a constant grid angle. No AVR, inner loops, current
  limiting, PLL, delay, PWM or network dynamics. The terminal power `Re(u ī_c)`,
  `u = E − r_a(i_c − ℓ)`, differs in its linearization by `Re(Δu ī_c₀)`, which vanishes when the
  equilibrium current is zero; that term is not included.
* Small-signal analysis in the coordinates `(Δδ, Δp_f, Δℓ, Δℓ̄)` (`jac`), a complex-linear change of
  the real coordinates `(Δδ, Δp_f, Re Δℓ, Im Δℓ)`; transfers are evaluated along `e^{st}`, and
  `K(s) = E (T(s) + conj T(conj s))/2` is the transfer of a real angle to the power
  (`syncTransfer`).
* The closed forms of the lag (`im_syncClosed`, `neg_im_syncClosed_noLoad`) take the lossless
  network `R = 0` with `r_a = ρ sin α`, `X = ρ cos α` (`α = arctan(r_a/X)`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (PSC core: `D_PSC(s) = s(s + ω_f) + k_PSC ω_f K(s)`,
`K(s) = K_hf + K_ℓ(s)`, `K_ℓ(0) = ΔK ≈ V₀² sin²α/X`, `α = arctan((R + r_a)/X)`), §4.2 ((13):
`σ_m/Ω_m ≈ ω_f/(2Ω_m) − (1/2)(ΔK/K_r) F_i(x, α)`, `x = Ω_m/α_d`,
`F_i = 2x³cos²α/((x² + cos²α)² − x² sin²2α)`), Table 4 (PSC: the `ℓ` branch gives
`+(Ω_m/2)(ΔK/K_r) F_i`).

Results.
* Linearization: `hasDerivAt_current_angle` (`∂i_c/∂δ = jV e^{−jδ}/Z`, `angleCoeff`),
  `current_add_ell` (`i_c` is affine in `ℓ` with slope `r_a/Z`).
* Branch transfers along `e^{st}`: `ellTransfer_eq` (the `ℓ` equation
  `s c(s) = α_d (T(s) − c(s))` for `c(s) = α_d (∂i_c/∂δ)/(s + a)`, pole `a = α_d (R + jX)/Z`),
  `currentTransfer_eq`, `currentTransfer_eq'` (`T(s) = jV e^{−jδ₀}(s + α_d)/(Z s + α_d(R + jX))`).
* `syncTransfer_eq` — closed form `K(s) = E V (s + α_d)(X cos δ₀ (s + α_d) + sin δ₀((R + r_a)s +
  α_d R))/(|Z|² s² + 2α_d (R(R + r_a) + X²) s + α_d²(R² + X²))` (`syncClosed`, denominator
  `syncDen_eq`); `syncClosed_zero` — `K(0) = E V (X cos δ₀ + R sin δ₀)/(R² + X²)`: the high-pass
  `r_a` does not change the static synchronizing coefficient; `deltaK_eq` — for `R = 0`,
  `ΔK = K(0) − K_hf = E V sin α sin(α − δ₀)/X` with `K_hf = E V cos α cos(α − δ₀)/X`.
* Lag at the mode frequency (`R = 0`, `s = j x α_d`): `syncClosed_imag`, `im_syncClosed`
  (exact `Im K` for every load angle), `neg_im_syncClosed_noLoad` — at no load
  `−Im K(j x α_d) = ΔK F_i(x, α)` exactly, with `ΔK = E V sin²α/X` (`branchLag` is `F_i`).
* `im_syncClosed_load_alpha` — at `δ₀ = α`, `ΔK = 0` but
  `Im K(j x α_d) = E V x sin²α (cos²α − x²)/(ρ((cos²α − x²)² + 4x²cos⁴α))`, nonzero for
  `sin α ≠ 0`, `x ≠ 0`, `x² ≠ cos²α`.
* Damping budget: `root_damping` — a root `λ = −σ + jΩ` of `λ² + ω_f λ + k ω_f K = 0` has
  `σ = ω_f/2 + k ω_f Im K/(2Ω)` and `Ω² = k ω_f Re K + σ(σ − ω_f)` exactly; `relDamping_eq` —
  `σ/Ω = ω_f/(2Ω) + (k ω_f/Ω²) Im K(λ)/2`.
* `jac_modeVec` — every root of `λ(λ + ω_f) + k ω_f K(λ) = 0` off the branch poles is an
  eigenvalue of the linearization (`jac`) with eigenvector `k (1, −λ/k, c(λ), conj c(conj λ))`.

Comparison with the source.
* The source's check model feeds the PCC power `Re(u ī)` to the low-pass; it is formalized in
  `PSCFull.lean`, where `ΔK = V² sin²α/X` and `−Im K(jΩ) = ΔK F_i` hold exactly for every load angle
  (`PSCFull.Model.Kl_zero`, `PSCFull.Model.neg_im_K`). The EMF-power variant of this module agrees
  with it at no load (`neg_im_syncClosed_noLoad`); at load its `ΔK = E V sin α sin(α − δ₀)/X` and
  its lag differ (`im_syncClosed_load_alpha`). The load dependence found here is a property of the
  power measurement point, not of (13).
* In both models (13) is exact up to `k ω_f/Ω² ≈ 1/K_r` and `K(λ) ≈ K(jΩ)` (`relDamping_eq`).
* `F_i` uses the pole `α_d cos α e^{±jα}` of the lossless network (`R = 0`). With `R ≠ 0` the pole
  is `α_d (R + jX)/Z` (`pole`), not a function of `α = arctan((R + r_a)/X)` alone.

Family and connection conclusions.
None: static evidence on the active-damping PSC (linearization, transfers, damping identity,
eigenvectors).
-/

noncomputable section
namespace powerlib.GFM
namespace PSCActiveDamping
open Complex ComplexConjugate Matrix

/-! ## The linearized active-damping branch -/

/-- Fast-time-scale impedance `Z = R + r_a + jX`. -/
def imp (R ra X : ℝ) : ℂ := ((R + ra : ℝ) : ℂ) + (X : ℂ) * I

/-- Converter-frame current of the quasi-static network, `i_c = (E + r_a ℓ − V e^{−jδ})/Z`. -/
def current (E V R ra X δ : ℝ) (ℓ : ℂ) : ℂ :=
  ((E : ℂ) + ra * ℓ - V * exp (-((δ : ℂ) * I))) / imp R ra X

/-- Angle coefficient `∂i_c/∂δ = jV e^{−jδ}/Z`. -/
def angleCoeff (V R ra X δ : ℝ) : ℂ := I * V * exp (-((δ : ℂ) * I)) / imp R ra X

/-- Pole of the active-damping branch, `a = α_d (R + jX)/Z`. -/
def pole (R ra X αd : ℝ) : ℂ := αd * (((R : ℂ) + X * I) / imp R ra X)

/-- Transfer `c(s) = α_d (∂i_c/∂δ)/(s + a)` from the angle to the high-pass state `ℓ`. -/
def ellTransfer (V R ra X αd δ0 : ℝ) (s : ℂ) : ℂ :=
  αd * angleCoeff V R ra X δ0 / (s + pole R ra X αd)

/-- Transfer from the angle to the current, `(r_a/Z) c(s) + ∂i_c/∂δ`. -/
def currentTransfer (V R ra X αd δ0 : ℝ) (s : ℂ) : ℂ :=
  ra / imp R ra X * ellTransfer V R ra X αd δ0 s + angleCoeff V R ra X δ0

/-- Synchronizing transfer of a real angle, `K(s) = E (T(s) + conj T(conj s))/2`. -/
def syncTransfer (E V R ra X αd δ0 : ℝ) (s : ℂ) : ℂ :=
  E * (currentTransfer V R ra X αd δ0 s + conj (currentTransfer V R ra X αd δ0 (conj s))) / 2

/-- The active-damping lag function of (13),
`F_i(x, α) = 2x³cos²α/((x² + cos²α)² − x² sin²2α)`. -/
def branchLag (x α : ℝ) : ℝ :=
  2 * x ^ 3 * Real.cos α ^ 2 / ((x ^ 2 + Real.cos α ^ 2) ^ 2 - x ^ 2 * Real.sin (2 * α) ^ 2)

/-- Closed form of `K(s)`. -/
def syncClosed (E V R ra X αd δ0 : ℝ) (s : ℂ) : ℂ :=
  ((E * V : ℝ) : ℂ) * (s + αd) *
      ((X * Real.cos δ0 : ℝ) * (s + αd) + (Real.sin δ0 : ℂ) * ((R + ra : ℝ) * s + (αd * R : ℝ))) /
    (((R + ra) ^ 2 + X ^ 2 : ℝ) * s ^ 2 + ((2 * αd * (R * (R + ra) + X ^ 2) : ℝ) : ℂ) * s +
      ((αd ^ 2 * (R ^ 2 + X ^ 2) : ℝ) : ℂ))

@[tmio T, powerlib_foundation] theorem exp_neg_mul_I (δ : ℝ) :
    exp (-((δ : ℂ) * I)) = (Real.cos δ : ℂ) - (Real.sin δ : ℂ) * I := by
  rw [show -((δ : ℂ) * I) = ((-δ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_current_angle (E V R ra X δ : ℝ) (ℓ : ℂ) :
    HasDerivAt (fun δ : ℝ => current E V R ra X δ ℓ) (angleCoeff V R ra X δ) δ := by
  have h1 : HasDerivAt (fun δ : ℝ => (δ : ℂ) * (-I)) (1 * (-I)) δ :=
    (hasDerivAt_id δ).ofReal_comp.mul_const (-I)
  have h2 := (h1.cexp.const_mul (V : ℂ)).const_sub ((E : ℂ) + ra * ℓ)
  have h3 := h2.div_const (imp R ra X)
  have hf : (fun δ : ℝ => current E V R ra X δ ℓ) =
      fun δ : ℝ => ((E : ℂ) + ra * ℓ - V * exp ((δ : ℂ) * (-I))) / imp R ra X := by
    funext δ; simp only [current, mul_neg]
  rw [hf]
  convert h3 using 1
  simp only [angleCoeff, mul_neg]
  ring

@[tmio M, powerlib_domain] theorem current_add_ell (E V R ra X δ : ℝ) (ℓ h : ℂ) :
    current E V R ra X δ (ℓ + h) = current E V R ra X δ ℓ + ra / imp R ra X * h := by
  simp only [current]
  ring

@[tmio M, powerlib_domain] theorem imp_ne_zero {R ra X : ℝ} (hX : X ≠ 0) : imp R ra X ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [imp] at this
  exact hX this

/-- `s + a = (Z s + α_d (R + jX))/Z`. -/
@[tmio M, powerlib_domain] theorem add_pole {R ra X αd : ℝ} (hX : X ≠ 0) (s : ℂ) :
    s + pole R ra X αd = (imp R ra X * s + αd * ((R : ℂ) + X * I)) / imp R ra X := by
  have hZ := imp_ne_zero (R := R) (ra := ra) hX
  simp only [pole]
  field_simp

@[tmio M, powerlib_domain] theorem ellTransfer_eq' {V R ra X αd δ0 : ℝ} {s : ℂ} (hX : X ≠ 0) :
    ellTransfer V R ra X αd δ0 s =
      αd * angleCoeff V R ra X δ0 * imp R ra X / (imp R ra X * s + αd * ((R : ℂ) + X * I)) := by
  have hZ := imp_ne_zero (R := R) (ra := ra) hX
  rw [ellTransfer, add_pole hX, div_div_eq_mul_div]

/-- The `ℓ` equation `ℓ̇ = α_d(Δi_c − ℓ)` along `e^{st}`: `s c(s) = α_d (T(s) − c(s))`. -/
@[tmio M, powerlib_domain] theorem ellTransfer_eq {V R ra X αd δ0 : ℝ} {s : ℂ} (hX : X ≠ 0)
    (hs : imp R ra X * s + αd * ((R : ℂ) + X * I) ≠ 0) :
    s * ellTransfer V R ra X αd δ0 s =
      αd * (currentTransfer V R ra X αd δ0 s - ellTransfer V R ra X αd δ0 s) := by
  have hZ := imp_ne_zero (R := R) (ra := ra) hX
  have hZd : imp R ra X = (R : ℂ) + ra + X * I := by simp only [imp]; push_cast; ring
  simp only [currentTransfer, ellTransfer_eq' hX]
  generalize angleCoeff V R ra X δ0 = c
  generalize hw : imp R ra X * s + αd * ((R : ℂ) + X * I) = w at hs ⊢
  generalize imp R ra X = Z at hZ hZd hw
  field_simp
  rw [← hw, hZd]
  ring

@[tmio M, powerlib_domain] theorem currentTransfer_eq {V R ra X αd δ0 : ℝ} {s : ℂ} (hX : X ≠ 0)
    (hs : imp R ra X * s + αd * ((R : ℂ) + X * I) ≠ 0) :
    currentTransfer V R ra X αd δ0 s =
      angleCoeff V R ra X δ0 * imp R ra X * (s + αd) /
        (imp R ra X * s + αd * ((R : ℂ) + X * I)) := by
  have hZ := imp_ne_zero (R := R) (ra := ra) hX
  have hZd : imp R ra X = (R : ℂ) + ra + X * I := by simp only [imp]; push_cast; ring
  simp only [currentTransfer, ellTransfer_eq' hX]
  generalize angleCoeff V R ra X δ0 = c
  generalize hw : imp R ra X * s + αd * ((R : ℂ) + X * I) = w at hs ⊢
  generalize imp R ra X = Z at hZ hZd hw
  field_simp
  rw [← hw, hZd]
  ring

/-- `T(s) = jV e^{−jδ₀}(s + α_d)/(Z s + α_d (R + jX))`. -/
@[tmio M, powerlib_domain] theorem currentTransfer_eq' {V R ra X αd δ0 : ℝ} {s : ℂ} (hX : X ≠ 0)
    (hs : imp R ra X * s + αd * ((R : ℂ) + X * I) ≠ 0) :
    currentTransfer V R ra X αd δ0 s =
      I * V * ((Real.cos δ0 : ℂ) - (Real.sin δ0 : ℂ) * I) * (s + αd) /
        (imp R ra X * s + αd * ((R : ℂ) + X * I)) := by
  have hZ := imp_ne_zero (R := R) (ra := ra) hX
  rw [currentTransfer_eq hX hs, angleCoeff, exp_neg_mul_I]
  field_simp

@[tmio M, powerlib_domain] theorem conj_imp (R ra X : ℝ) : conj (imp R ra X) = ((R + ra : ℝ) : ℂ) - (X : ℂ) * I := by
  simp [imp, map_add, map_mul, conj_ofReal, conj_I]
  ring

/-- The denominator of `K(s)` is `(Z s + α_d(R + jX))(Z̄ s + α_d(R − jX))`. -/
@[tmio M, powerlib_domain] theorem syncDen_eq (R ra X αd : ℝ) (s : ℂ) :
    (((R + ra) ^ 2 + X ^ 2 : ℝ) : ℂ) * s ^ 2 + ((2 * αd * (R * (R + ra) + X ^ 2) : ℝ) : ℂ) * s +
        ((αd ^ 2 * (R ^ 2 + X ^ 2) : ℝ) : ℂ) =
      (imp R ra X * s + αd * ((R : ℂ) + X * I)) *
        (conj (imp R ra X) * s + αd * ((R : ℂ) - X * I)) := by
  rw [conj_imp]
  simp only [imp]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Closed form of the synchronizing transfer of the active-damping PSC:
`K(s) = E V (s + α_d)(X cos δ₀ (s + α_d) + sin δ₀ ((R + r_a) s + α_d R))/(|Z|² s² +
2α_d (R(R + r_a) + X²) s + α_d² (R² + X²))`. -/
@[tmio M, powerlib_domain] theorem syncTransfer_eq {E V R ra X αd δ0 : ℝ} {s : ℂ} (hX : X ≠ 0)
    (hs1 : imp R ra X * s + αd * ((R : ℂ) + X * I) ≠ 0)
    (hs2 : conj (imp R ra X) * s + αd * ((R : ℂ) - X * I) ≠ 0) :
    syncTransfer E V R ra X αd δ0 s = syncClosed E V R ra X αd δ0 s := by
  have hs2' : imp R ra X * conj s + αd * ((R : ℂ) + X * I) ≠ 0 := by
    intro h
    apply hs2
    have := congrArg conj h
    simpa [map_add, map_mul, conj_ofReal, conj_I, map_sub, sub_eq_add_neg] using this
  rw [syncTransfer, syncClosed, syncDen_eq, currentTransfer_eq' hX hs1,
    currentTransfer_eq' hX hs2']
  have hc : conj (imp R ra X * conj s + αd * ((R : ℂ) + X * I)) =
      conj (imp R ra X) * s + αd * ((R : ℂ) - X * I) := by
    simp [map_add, map_mul, conj_ofReal, conj_I, sub_eq_add_neg]
  rw [map_div₀, hc]
  simp only [map_mul, map_add, map_sub, conj_ofReal, conj_I, Complex.conj_conj]
  rw [conj_imp] at hs2 ⊢
  generalize hw1 : imp R ra X * s + αd * ((R : ℂ) + X * I) = w1 at hs1 ⊢
  generalize hw2 : (((R + ra : ℝ) : ℂ) - (X : ℂ) * I) * s + αd * ((R : ℂ) - X * I) = w2 at hs2 ⊢
  field_simp
  rw [← hw1, ← hw2]
  simp only [imp]
  push_cast
  ring_nf
  rw [I_sq]
  ring_nf

/-! ## Static and fast synchronizing coefficients -/

/-- `K(0) = E V (X cos δ₀ + R sin δ₀)/(R² + X²)`: the active resistance does not enter. -/
@[tmio M, powerlib_domain] theorem syncClosed_zero {E V R ra X αd δ0 : ℝ} (hαd : αd ≠ 0) (hX : X ≠ 0) :
    syncClosed E V R ra X αd δ0 0 =
      ((E * V * (X * Real.cos δ0 + R * Real.sin δ0) / (R ^ 2 + X ^ 2) : ℝ) : ℂ) := by
  have h : R ^ 2 + X ^ 2 ≠ 0 := by positivity
  simp only [syncClosed]
  push_cast
  have h' : (R : ℂ) ^ 2 + (X : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h
  have hα : (αd : ℂ) ≠ 0 := by exact_mod_cast hαd
  field_simp
  ring

/-- Lossless network (`R = 0`) with `r_a = ρ sin α`, `X = ρ cos α`: `K(0) = E V cos δ₀/X`, the
fast value `K_hf = E V cos α cos(α − δ₀)/X` (the leading-coefficient ratio of `K(s)`), and
`ΔK = K(0) − K_hf = E V sin α sin(α − δ₀)/X`. -/
@[tmio M, powerlib_domain] theorem deltaK_eq {E V ρ α δ0 : ℝ} (hρ : 0 < ρ) (hc : Real.cos α ≠ 0) :
    E * V * Real.cos δ0 / (ρ * Real.cos α) -
        E * V * ((ρ * Real.cos α) * Real.cos δ0 + (ρ * Real.sin α) * Real.sin δ0) /
          ((ρ * Real.sin α) ^ 2 + (ρ * Real.cos α) ^ 2) =
      E * V * Real.sin α * Real.sin (α - δ0) / (ρ * Real.cos α) := by
  have hsc := Real.sin_sq_add_cos_sq α
  have hρ2 : (ρ * Real.sin α) ^ 2 + (ρ * Real.cos α) ^ 2 = ρ ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, hsc, mul_one]
  rw [hρ2, Real.sin_sub]
  have hρ0 : ρ ≠ 0 := hρ.ne'
  field_simp
  linear_combination (-(E * V * Real.cos δ0)) * hsc

/-! ## The lag of the synchronizing coefficient at the mode frequency -/

@[tmio M, powerlib_domain] theorem syncDen_imag_ne_zero {ra X x : ℝ} (hX : X ≠ 0) :
    (((X ^ 2 - (ra ^ 2 + X ^ 2) * x ^ 2 : ℝ) : ℂ) + ((2 * X ^ 2 * x : ℝ) : ℂ) * I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero, zero_add, Complex.zero_re, Complex.zero_im] at hre him
  have hx : x = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        (by linarith : X ^ 2 = 0)) hX
    · exact h1
  subst hx
  have : X ^ 2 = 0 := by linarith
  exact hX (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

/-- At `s = j x α_d` (lossless network): `K = E V N/D` with
`N = (X cos δ₀ − x² B) + j x (2X cos δ₀ + r_a sin δ₀)`, `B = X cos δ₀ + r_a sin δ₀`,
`D = X² − (r_a² + X²) x² + 2j X² x`. -/
@[tmio M, powerlib_domain] theorem syncClosed_imag {E V ra X αd δ0 x : ℝ} (hαd : αd ≠ 0) (hX : X ≠ 0) :
    syncClosed E V 0 ra X αd δ0 (((x * αd : ℝ) : ℂ) * I) =
      ((E * V : ℝ) : ℂ) *
        (((X * Real.cos δ0 - x ^ 2 * (X * Real.cos δ0 + ra * Real.sin δ0) : ℝ) : ℂ) +
          ((x * (2 * X * Real.cos δ0 + ra * Real.sin δ0) : ℝ) : ℂ) * I) /
        (((X ^ 2 - (ra ^ 2 + X ^ 2) * x ^ 2 : ℝ) : ℂ) + ((2 * X ^ 2 * x : ℝ) : ℂ) * I) := by
  have hD := syncDen_imag_ne_zero (ra := ra) (x := x) hX
  have hα : (αd : ℂ) ≠ 0 := by exact_mod_cast hαd
  have hD2 : (((0 + ra) ^ 2 + X ^ 2 : ℝ) : ℂ) * (((x * αd : ℝ) : ℂ) * I) ^ 2 +
      ((2 * αd * (0 * (0 + ra) + X ^ 2) : ℝ) : ℂ) * (((x * αd : ℝ) : ℂ) * I) +
      ((αd ^ 2 * (0 ^ 2 + X ^ 2) : ℝ) : ℂ) =
      (αd : ℂ) ^ 2 * (((X ^ 2 - (ra ^ 2 + X ^ 2) * x ^ 2 : ℝ) : ℂ) +
        ((2 * X ^ 2 * x : ℝ) : ℂ) * I) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [syncClosed, hD2]
  field_simp
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Exact lag of the synchronizing coefficient at `s = j x α_d` (lossless network,
`r_a = ρ sin α`, `X = ρ cos α`, any load angle `δ₀`):
`Im K = E V x [cos(α − δ₀)(c² − x² + 2x²c²) − c cos δ₀ (c² + x²)]/(ρ((c² − x²)² + 4x²c⁴))`,
`c = cos α`. -/
@[tmio M, powerlib_domain] theorem im_syncClosed {E V ρ α αd δ0 x : ℝ} (hρ : 0 < ρ) (hc : Real.cos α ≠ 0)
    (hαd : αd ≠ 0) :
    (syncClosed E V 0 (ρ * Real.sin α) (ρ * Real.cos α) αd δ0
        (((x * αd : ℝ) : ℂ) * I)).im =
      E * V * x * (Real.cos (α - δ0) * (Real.cos α ^ 2 - x ^ 2 + 2 * x ^ 2 * Real.cos α ^ 2) -
          Real.cos α * Real.cos δ0 * (Real.cos α ^ 2 + x ^ 2)) /
        (ρ * ((Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4)) := by
  have hX : ρ * Real.cos α ≠ 0 := mul_ne_zero hρ.ne' hc
  rw [syncClosed_imag hαd hX]
  have hsc := Real.sin_sq_add_cos_sq α
  have hρ2 : (ρ * Real.sin α) ^ 2 + (ρ * Real.cos α) ^ 2 = ρ ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, hsc, mul_one]
  rw [hρ2]
  have hpos : 0 < (Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4 := by
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp; positivity
    · have : 0 < 4 * x ^ 2 * Real.cos α ^ 4 := by positivity
      nlinarith [sq_nonneg (Real.cos α ^ 2 - x ^ 2)]
  have hnorm : Complex.normSq (((ρ * Real.cos α) ^ 2 - ρ ^ 2 * x ^ 2 : ℝ) +
      ((2 * (ρ * Real.cos α) ^ 2 * x : ℝ) : ℂ) * I) =
      ρ ^ 4 * ((Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4) := by
    rw [Complex.normSq_add_mul_I]; ring
  rw [Complex.div_im, hnorm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  rw [Real.cos_sub]
  have hρ0 : ρ ≠ 0 := hρ.ne'
  field_simp
  ring

/-- No load (`δ₀ = 0`): `−Im K(j x α_d) = ΔK F_i(x, α)` with `ΔK = E V sin²α/X` and
`F_i = 2x³cos²α/((x² + cos²α)² − x² sin²2α)` — the active-damping term of (13) is exact. -/
@[tmio M, powerlib_domain] theorem neg_im_syncClosed_noLoad {E V ρ α αd x : ℝ} (hρ : 0 < ρ) (hc : Real.cos α ≠ 0)
    (hαd : αd ≠ 0) :
    -(syncClosed E V 0 (ρ * Real.sin α) (ρ * Real.cos α) αd 0
        (((x * αd : ℝ) : ℂ) * I)).im =
      E * V * Real.sin α ^ 2 / (ρ * Real.cos α) * branchLag x α := by
  rw [im_syncClosed hρ hc hαd, branchLag, Real.sin_two_mul]
  have hsc := Real.sin_sq_add_cos_sq α
  have hden : (x ^ 2 + Real.cos α ^ 2) ^ 2 - x ^ 2 * (2 * Real.sin α * Real.cos α) ^ 2 =
      (Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4 := by
    linear_combination (-4 * x ^ 2 * Real.cos α ^ 2) * hsc
  rw [hden]
  have hpos : 0 < (Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4 := by
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp; positivity
    · have : 0 < 4 * x ^ 2 * Real.cos α ^ 4 := by positivity
      nlinarith [sq_nonneg (Real.cos α ^ 2 - x ^ 2)]
  simp only [sub_zero, Real.cos_zero, mul_one]
  rw [show Real.sin α ^ 2 = 1 - Real.cos α ^ 2 by linarith]
  generalize (Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4 = D at hpos ⊢
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hD : D ≠ 0 := hpos.ne'
  field_simp
  ring

/-- At the load angle `δ₀ = α` the static/fast stiffness gap vanishes, `ΔK = 0`, while the lag
does not: `Im K(j x α_d) = E V x sin²α (cos²α − x²)/(ρ((cos²α − x²)² + 4x²cos⁴α))`. Hence at load
the lag is not `−ΔK F_i` with the exact `ΔK`. -/
@[tmio M, powerlib_domain] theorem im_syncClosed_load_alpha {E V ρ α αd x : ℝ} (hρ : 0 < ρ) (hc : Real.cos α ≠ 0)
    (hαd : αd ≠ 0) :
    Real.sin α * Real.sin (α - α) = 0 ∧
      (syncClosed E V 0 (ρ * Real.sin α) (ρ * Real.cos α) αd α
          (((x * αd : ℝ) : ℂ) * I)).im =
        E * V * x * Real.sin α ^ 2 * (Real.cos α ^ 2 - x ^ 2) /
          (ρ * ((Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4)) := by
  refine ⟨by simp, ?_⟩
  rw [im_syncClosed hρ hc hαd, sub_self, Real.cos_zero]
  congr 1
  rw [show Real.sin α ^ 2 = 1 - Real.cos α ^ 2 by linarith [Real.sin_sq_add_cos_sq α]]
  ring

/-! ## The damping budget of the PSC loop -/

/-- Exact damping and frequency of a root `λ = −σ + jΩ` of `λ² + ω_f λ + k ω_f K = 0` with an
arbitrary complex value `K = K(λ)`: `σ = ω_f/2 + k ω_f Im K/(2Ω)` and
`Ω² = k ω_f Re K + σ(σ − ω_f)`. -/
@[tmio T, powerlib_foundation] theorem root_damping {k ωf σ Ω : ℝ} {K : ℂ} (hΩ : Ω ≠ 0)
    (h : ((-σ : ℝ) + (Ω : ℂ) * I) ^ 2 + (ωf : ℂ) * ((-σ : ℝ) + (Ω : ℂ) * I) +
      ((k * ωf : ℝ) : ℂ) * K = 0) :
    σ = ωf / 2 + k * ωf * K.im / (2 * Ω) ∧ Ω ^ 2 = k * ωf * K.re + σ * (σ - ωf) := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
    Complex.zero_im] at hre him
  constructor
  · field_simp
    linarith
  · linarith

/-- The PSC form of (13): along a root `λ = −σ + jΩ` of `D_PSC(λ) = λ(λ + ω_f) + k ω_f K(λ)`,
`σ/Ω = ω_f/(2Ω) + (k ω_f/Ω²) Im K(λ)/2` exactly. The source's first-order reading replaces
`k ω_f/Ω²` by `1/K_r` and `K(λ)` by `K(jΩ)`, where `−Im K(jΩ) = ΔK F_i` at no load
(`neg_im_syncClosed_noLoad`). -/
@[tmio T, powerlib_foundation] theorem relDamping_eq {k ωf σ Ω : ℝ} {K : ℂ} (hΩ : Ω ≠ 0)
    (h : ((-σ : ℝ) + (Ω : ℂ) * I) ^ 2 + (ωf : ℂ) * ((-σ : ℝ) + (Ω : ℂ) * I) +
      ((k * ωf : ℝ) : ℂ) * K = 0) :
    σ / Ω = ωf / (2 * Ω) + k * ωf / Ω ^ 2 * K.im / 2 := by
  rw [(root_damping hΩ h).1]
  field_simp

/-! ## Eigenvectors of the linearization -/

/-- The linearized PSC with active damping in the coordinates `(Δδ, Δp_f, Δℓ, Δℓ̄)`:
`δ̇ = −k p_f`, `ṗ_f = ω_f(E Re Δi_c − p_f)`, `ℓ̇ = α_d(Δi_c − ℓ)` with
`Δi_c = a Δδ + (r_a/Z) Δℓ` (`hasDerivAt_current_angle`, `current_add_ell`). -/
def jac (k ωf E V R ra X αd δ0 : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -(k : ℂ), 0, 0;
    (ωf : ℂ) * E * (angleCoeff V R ra X δ0 + conj (angleCoeff V R ra X δ0)) / 2, -(ωf : ℂ),
      (ωf : ℂ) * E * (ra / imp R ra X) / 2, (ωf : ℂ) * E * conj (ra / imp R ra X) / 2;
    (αd : ℂ) * angleCoeff V R ra X δ0, 0, (αd : ℂ) * (ra / imp R ra X - 1), 0;
    (αd : ℂ) * conj (angleCoeff V R ra X δ0), 0, 0, (αd : ℂ) * (conj (ra / imp R ra X) - 1)]

/-- The mode vector `k (1, −λ/k, c(λ), conj c(conj λ))`. -/
def modeVec (k V R ra X αd δ0 : ℝ) (lam : ℂ) : Fin 4 → ℂ :=
  ![k, -lam, k * ellTransfer V R ra X αd δ0 lam,
    k * conj (ellTransfer V R ra X αd δ0 (conj lam))]

/-- Every root of `λ(λ + ω_f) + k ω_f K(λ) = 0` away from the poles of the `ℓ` branch is an
eigenvalue of the linearization, with eigenvector `modeVec`. -/
@[tmio M, powerlib_domain] theorem jac_modeVec {k ωf E V R ra X αd δ0 : ℝ} {lam : ℂ} (hX : X ≠ 0)
    (h1 : imp R ra X * lam + αd * ((R : ℂ) + X * I) ≠ 0)
    (h2 : imp R ra X * conj lam + αd * ((R : ℂ) + X * I) ≠ 0)
    (hroot : lam * (lam + ωf) + (k : ℂ) * ωf * syncTransfer E V R ra X αd δ0 lam = 0) :
    jac k ωf E V R ra X αd δ0 *ᵥ modeVec k V R ra X αd δ0 lam =
      lam • modeVec k V R ra X αd δ0 lam := by
  have e1 := ellTransfer_eq (V := V) (δ0 := δ0) hX h1
  have e2 := congrArg conj (ellTransfer_eq (V := V) (δ0 := δ0) hX h2)
  simp only [currentTransfer, map_mul, map_sub, map_add, conj_ofReal, Complex.conj_conj] at e1 e2
  simp only [syncTransfer, currentTransfer, map_add, map_mul] at hroot
  funext i
  fin_cases i <;>
    simp [jac, modeVec, mulVec, dotProduct, Fin.sum_univ_four, -map_div₀]
  · ring
  · linear_combination hroot
  · linear_combination (-(k : ℂ)) * e1
  · linear_combination (-(k : ℂ)) * e2

end PSCActiveDamping
end powerlib.GFM
