import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import theorem.SpecialFunctions.BesselI

/-! # Klein–Kramers operator: Gibbs stationarity, washboard partition function, Langer factor

Laws of the stationary Fokker–Planck (Klein–Kramers) operator of an underdamped Langevin system in
position–momentum coordinates, of its Gibbs function, and of the linearized drift at a saddle.

Scope.
* Foundation (generic calculus and algebra). The system is `q̇ = p/M`,
  `ṗ = −V'(q) − D p/M` (Hamiltonian `H = p²/(2M) + V(q)`, momentum damping `D`), with a
  diffusion matrix `diag(b, a(q))`: constant position diffusion `b`, momentum diffusion `a(q)`
  depending on the position only.  `kkOp` is the **differential operator**
  `L*ρ = −∂_q((p/M) ρ) − ∂_p((−V' − D p/M) ρ) + ½ b ∂²_q ρ + ½ ∂²_p(a ρ)`; that it governs the
  density of an Itô diffusion, and every statement about laws or expectations, is not formalized.
* The stationarity statements are pointwise PDE identities; the partition function is a Lebesgue
  integral on `[0, 2π] × ℝ` (the angle read on one period); the Langer factor is an eigenvalue
  computation of the linearized drift.

Source: work-sync `theory/T-fokker-planck.md` §1.1 (`L* p = −∇·(μ p) + ½ ∂ᵢ∂ⱼ[(ΣΣᵀ)ᵢⱼ p]`),
§1.4 (Gibbs form); H. A. Kramers, Physica 7 (1940) 284 (Klein–Kramers equation, escape over a
barrier); J. S. Langer, Ann. Phys. 54 (1969) 258 (the saddle eigenvalue prefactor
`λ₊/ω_b = √(1 + ζ²) − ζ`); Hänggi, Talkner, Borkovec, Rev. Mod. Phys. 62 (1990) 251, §IV.

Results.
* `kkOp_gibbs`: `L* e^{−H/T} = e^{−H/T} [(D − a(q)/(2T))(1/M − p²/(M²T)) +
  (b/2)(V'(q)²/T² − V''(q)/T)]` (`M, T ≠ 0`).
* `kkOp_gibbs_eq_zero_iff`: with momentum noise only (`b = 0`), `e^{−H/T}` solves the stationary
  equation at every `(q, p)` iff `a ≡ 2 D T` (fluctuation–dissipation with temperature `T`);
  `kkOp_gibbs_not_stationary`: with position noise only (`a ≡ 0`) and `D ≠ 0`, at no position
  does `e^{−H/T}` solve it for all momenta, whatever `T`.
* `gibbs_washboard_periodic_iff`: on the tilted washboard `V = −c q − A cos(q − α)` the Gibbs
  function is `2π`-periodic in `q` (a function on the circle) iff `c = 0`;
  `integrable_gibbs_circle`, `integral_gibbs_circle`: for `c = 0`, `M T > 0`, it is integrable on
  `(0, 2π] × ℝ`, with partition function `Z = 2π I₀(A/T) √(2π M T)`
  (`SpecialFunctions.integral_cexp_cos`, Mathlib `integral_gaussian`).
* `kkJacobian`, `kkJacobian_mulVec`, `kkLambda_div`: at a saddle of `V` (`V'' = −κ`, `κ > 0`) the
  linearized drift `!![0, 1/M; κ, −D/M]` has the unstable eigenvalue
  `λ₊ = −D/(2M) + √(D²/(4M²) + κ/M)` with eigenvector `(1, M λ₊)`, and
  `λ₊/ω_b = √(1 + ζ²) − ζ` with `ω_b = √(κ/M)`, `ζ = D/(2√(M κ))` (Langer's momentum-damping
  factor, `≤ 1` for `ζ ≥ 0`, `kkLambda_div_le_one`).
-/

noncomputable section
namespace powerlib.Stochastic.KleinKramers

open Real MeasureTheory Set Matrix

/-! ## The operator and the Gibbs function -/

/-- Partial derivative in the position `q`. -/
def dq (F : ℝ → ℝ → ℝ) (q p : ℝ) : ℝ := deriv (fun x => F x p) q

/-- Partial derivative in the momentum `p`. -/
def dp (F : ℝ → ℝ → ℝ) (q p : ℝ) : ℝ := deriv (fun y => F q y) p

/-- Stationary Klein–Kramers operator
`L*ρ = −∂_q((p/M) ρ) − ∂_p((−V'(q) − D p/M) ρ) + ½ b ∂²_q ρ + ½ ∂²_p(a(q) ρ)`
(drift `(p/M, −V' − D p/M)`, diffusion matrix `diag(b, a(q))`). -/
def kkOp (M D b : ℝ) (V' a : ℝ → ℝ) (ρ : ℝ → ℝ → ℝ) (q p : ℝ) : ℝ :=
  -dq (fun x y => y / M * ρ x y) q p - dp (fun x y => (-V' x - D * (y / M)) * ρ x y) q p +
    b / 2 * dq (dq ρ) q p + 1 / 2 * dp (dp (fun x y => a x * ρ x y)) q p

/-- Gibbs function `e^{−H/T}`, `H = p²/(2M) + V(q)`. -/
def gibbs (V : ℝ → ℝ) (M T q p : ℝ) : ℝ := exp (-(p ^ 2 / (2 * M) + V q) / T)

@[tmio T, powerlib_foundation] theorem gibbs_pos (V : ℝ → ℝ) (M T q p : ℝ) :
    0 < gibbs V M T q p := exp_pos _

@[tmio T, powerlib_foundation] theorem gibbs_hasDerivAt_q {V V' : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (M T p x : ℝ) :
    HasDerivAt (fun x => gibbs V M T x p) (-(V' x) / T * gibbs V M T x p) x := by
  have hq : HasDerivAt (fun x => -(p ^ 2 / (2 * M) + V x) / T) (-(V' x) / T) x := by
    have := ((hV x).const_add (p ^ 2 / (2 * M))).neg.div_const T
    convert this using 1
  have h := hq.exp
  unfold gibbs
  convert h using 1
  ring

@[tmio T, powerlib_foundation] theorem gibbs_hasDerivAt_p (V : ℝ → ℝ) {M : ℝ} (hM : M ≠ 0)
    (T q y : ℝ) :
    HasDerivAt (fun y => gibbs V M T q y) (-(y / (M * T)) * gibbs V M T q y) y := by
  have hq : HasDerivAt (fun y : ℝ => y ^ 2 / (2 * M) + V q) (y / M) y := by
    have := ((hasDerivAt_pow 2 y).div_const (2 * M)).add_const (V q)
    convert this using 1; field_simp; push_cast; ring
  have hq' : HasDerivAt (fun y => -(y ^ 2 / (2 * M) + V q) / T) (-(y / M) / T) y := by
    have := hq.neg.div_const T
    convert this using 1
  have h := hq'.exp
  unfold gibbs
  convert h using 1
  field_simp

/-- **Klein–Kramers residual of the Gibbs function**:
`L* e^{−H/T} = e^{−H/T} [(D − a(q)/(2T))(1/M − p²/(M²T)) + (b/2)(V'(q)²/T² − V''(q)/T)]`. -/
@[tmio T, powerlib_foundation] theorem kkOp_gibbs {V V' V'' a : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x) {M D b T : ℝ}
    (hM : M ≠ 0) (hT : T ≠ 0) (q p : ℝ) :
    kkOp M D b V' a (gibbs V M T) q p = gibbs V M T q p *
      ((D - a q / (2 * T)) * (1 / M - p ^ 2 / (M ^ 2 * T)) +
        b / 2 * (V' q ^ 2 / T ^ 2 - V'' q / T)) := by
  set ρ := gibbs V M T with hρ
  have hρq : ∀ y, (fun x => ρ x y) = fun x => gibbs V M T x y := fun _ => rfl
  have hdqρ : dq ρ = fun x y => -(V' x) / T * ρ x y := by
    funext x y; exact (gibbs_hasDerivAt_q hV M T y x).deriv
  have hdpρ : ∀ x, dp (fun x y => a x * ρ x y) x =
      fun y => a x * (-(y / (M * T)) * ρ x y) := by
    intro x; funext y; exact ((gibbs_hasDerivAt_p V hM T x y).const_mul (a x)).deriv
  have e1 : dq (fun x y => y / M * ρ x y) q p = p / M * (-(V' q) / T * ρ q p) :=
    ((gibbs_hasDerivAt_q hV M T p q).const_mul (p / M)).deriv
  have e2 : dp (fun x y => (-V' x - D * (y / M)) * ρ x y) q p =
      -(D * (1 / M)) * ρ q p + (-V' q - D * (p / M)) * (-(p / (M * T)) * ρ q p) := by
    have hl : HasDerivAt (fun y : ℝ => -V' q - D * (y / M)) (-(D * (1 / M))) p := by
      have := (((hasDerivAt_id p).div_const M).const_mul D).const_sub (-V' q)
      convert this using 1; simp
    exact (hl.mul (gibbs_hasDerivAt_p V hM T q p)).deriv
  have e3 : dq (dq ρ) q p =
      -(V'' q) / T * ρ q p + -(V' q) / T * (-(V' q) / T * ρ q p) := by
    rw [hdqρ]
    exact ((((hV' q).neg).div_const T).mul (gibbs_hasDerivAt_q hV M T p q)).deriv
  have e4 : dp (dp (fun x y => a x * ρ x y)) q p =
      a q * (-(1 / (M * T)) * ρ q p + -(p / (M * T)) * (-(p / (M * T)) * ρ q p)) := by
    unfold dp at hdpρ ⊢
    rw [hdpρ q]
    have hl : HasDerivAt (fun y : ℝ => -(y / (M * T))) (-(1 / (M * T))) p := by
      have := (hasDerivAt_id p).const_mul (-(1 / (M * T)))
      convert this using 1
      · funext y; simp; ring
      · simp
    exact ((hl.mul (gibbs_hasDerivAt_p V hM T q p)).const_mul (a q)).deriv
  unfold kkOp
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-- **Gibbs stationarity iff fluctuation–dissipation**: with momentum noise only (`b = 0`),
`e^{−H/T}` solves `L* ρ = 0` at every `(q, p)` iff the momentum diffusion is the constant
`a ≡ 2 D T`. -/
@[tmio T, powerlib_foundation] theorem kkOp_gibbs_eq_zero_iff {V V' V'' a : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x) {M D T : ℝ}
    (hM : M ≠ 0) (hT : T ≠ 0) :
    (∀ q p, kkOp M D 0 V' a (gibbs V M T) q p = 0) ↔ ∀ q, a q = 2 * D * T := by
  simp only [kkOp_gibbs hV hV' hM hT, zero_div, zero_mul, add_zero]
  constructor
  · intro h q
    have h0 := h q 0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (gibbs_pos V M T q 0).ne'
    · have h2 : (D - a q / (2 * T)) * (1 / M) = 0 := by simpa using h1
      have h3 := (mul_eq_zero.mp h2).resolve_right (one_div_ne_zero hM)
      field_simp at h3
      linarith
  · intro h q p
    rw [h q]
    field_simp
    ring

/-- **Position noise alone is never Gibbs**: with no momentum diffusion (`a ≡ 0`) and `D ≠ 0`, at
every position `q` the stationary equation fails for some momentum, whatever `b` and `T`. -/
@[tmio T, powerlib_foundation] theorem kkOp_gibbs_not_stationary {V V' V'' : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (V' x) x) (hV' : ∀ x, HasDerivAt V' (V'' x) x) {M D b T : ℝ}
    (hM : M ≠ 0) (hD : D ≠ 0) (hT : T ≠ 0) (q : ℝ) :
    ¬ ∀ p, kkOp M D b V' (fun _ => 0) (gibbs V M T) q p = 0 := by
  intro h
  have h0 := h 0
  have h1 := h 1
  rw [kkOp_gibbs hV hV' hM hT] at h0 h1
  have h0' := (mul_eq_zero.mp h0).resolve_left (gibbs_pos V M T q 0).ne'
  have h1' := (mul_eq_zero.mp h1).resolve_left (gibbs_pos V M T q 1).ne'
  have : D / (M ^ 2 * T) = 0 := by
    have e : D / (M ^ 2 * T) =
        (D - 0 / (2 * T)) * (1 / M - 0 ^ 2 / (M ^ 2 * T)) + b / 2 * (V' q ^ 2 / T ^ 2 - V'' q / T) -
        ((D - 0 / (2 * T)) * (1 / M - 1 ^ 2 / (M ^ 2 * T)) +
          b / 2 * (V' q ^ 2 / T ^ 2 - V'' q / T)) := by
      field_simp; ring
    rw [e, h0', h1', sub_zero]
  exact div_ne_zero hD (mul_ne_zero (pow_ne_zero 2 hM) hT) this

/-! ## The tilted washboard: periodicity and the partition function on the circle -/

/-- The tilted-washboard Gibbs function is `2π`-periodic in the position iff the tilt vanishes:
`H(q + 2π, p) − H(q, p) = −2π c`. -/
@[tmio T, powerlib_foundation] theorem gibbs_washboard_periodic_iff {c A α M T : ℝ} (hT : T ≠ 0) :
    (∀ q p, gibbs (fun x => -(c * x) - A * cos (x - α)) M T (q + 2 * π) p =
      gibbs (fun x => -(c * x) - A * cos (x - α)) M T q p) ↔ c = 0 := by
  have hcos : ∀ q, cos (q + 2 * π - α) = cos (q - α) := fun q => by
    rw [show q + 2 * π - α = (q - α) + 2 * π by ring, cos_add_two_pi]
  constructor
  · intro h
    have h0 := h 0 0
    simp only [gibbs, hcos] at h0
    have := exp_injective h0
    field_simp at this
    have hpi := pi_pos
    nlinarith [this]
  · rintro rfl q p
    simp [gibbs, hcos]

/-- `∫₀^{2π} e^{z cos(q − α)} dq = 2π I₀(z)` (periodicity and evenness of `cos`,
`SpecialFunctions.integral_cexp_cos`). -/
@[tmio T, powerlib_foundation] theorem integral_cexp_cos_sub (z : ℂ) (α : ℝ) :
    ∫ q in (0 : ℝ)..2 * π, Complex.exp (z * Real.cos (q - α)) =
      2 * π * SpecialFunctions.besselI0 z := by
  set f : ℝ → ℂ := fun u => Complex.exp (z * Real.cos u)
  have hper : Function.Periodic f (2 * π) := fun u => by
    show Complex.exp (z * ((Real.cos (u + 2 * π) : ℝ) : ℂ)) = _
    rw [Real.cos_add_two_pi]
  have hf : Continuous f := by fun_prop
  have h1 : ∫ q in (0 : ℝ)..2 * π, Complex.exp (z * Real.cos (q - α)) =
      ∫ u in (0 : ℝ) - α..2 * π - α, f u :=
    intervalIntegral.integral_comp_sub_right f α
  have h2 : ∫ u in (0 : ℝ) - α..2 * π - α, f u = ∫ u in -π..π, f u := by
    have := hper.intervalIntegral_add_eq (0 - α) (-π)
    rw [show (0 : ℝ) - α + 2 * π = 2 * π - α by ring, show -π + 2 * π = π by ring] at this
    exact this
  have h3 : ∫ u in -π..π, f u = (∫ u in -π..0, f u) + ∫ u in (0 : ℝ)..π, f u :=
    (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (μ := volume) (-π) 0)
      (hf.intervalIntegrable (μ := volume) 0 π)).symm
  have h4 : ∫ u in -π..0, f u = ∫ u in (0 : ℝ)..π, f u := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π) f
    rw [neg_zero] at this
    rw [← this]
    congr 1; funext u; simp [f]
  rw [h1, h2, h3, h4, SpecialFunctions.integral_cexp_cos]
  ring

/-- The Gibbs function of the untilted washboard `V = −A cos(q − α)` factors into the
Maxwell factor `e^{−p²/(2MT)}` and the von Mises factor `e^{A cos(q − α)/T}`. -/
@[tmio T, powerlib_foundation] theorem gibbs_cos_eq (A α M T q p : ℝ) :
    gibbs (fun x => -(A * cos (x - α))) M T q p =
      exp (A / T * cos (q - α)) * exp (-(1 / (2 * M * T)) * p ^ 2) := by
  rw [gibbs, ← exp_add]
  congr 1
  ring

/-- For `c = 0`, `M T > 0` the Gibbs function is integrable on one period of the angle times the
momentum line: the circle density is normalizable. -/
@[tmio T, powerlib_foundation] theorem integrable_gibbs_circle {M T : ℝ} (hMT : 0 < M * T)
    (A α : ℝ) :
    Integrable (fun z : ℝ × ℝ => gibbs (fun x => -(A * cos (x - α))) M T z.1 z.2)
      ((volume.restrict (Ioc 0 (2 * π))).prod volume) := by
  simp only [gibbs_cos_eq]
  have hc : Continuous fun q : ℝ => exp (A / T * cos (q - α)) := by fun_prop
  exact Integrable.mul_prod (f := fun q : ℝ => exp (A / T * cos (q - α)))
    (g := fun p : ℝ => exp (-(1 / (2 * M * T)) * p ^ 2))
    (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (integrable_exp_neg_mul_sq (one_div_pos.mpr (by nlinarith)))

/-- **Partition function on the circle**: for `c = 0`,
`Z = ∫₀^{2π} ∫_ℝ e^{−H/T} dp dq = 2π I₀(A/T) √(2π M T)` (a finite normalization when `M T > 0`,
`integrable_gibbs_circle`). -/
@[tmio T, powerlib_foundation] theorem integral_gibbs_circle (M T A α : ℝ) :
    (((∫ z, gibbs (fun x => -(A * cos (x - α))) M T z.1 z.2
        ∂((volume.restrict (Ioc 0 (2 * π))).prod volume)) : ℝ) : ℂ) =
      2 * π * SpecialFunctions.besselI0 ((A / T : ℝ) : ℂ) * √(2 * π * M * T) := by
  simp only [gibbs_cos_eq]
  rw [integral_prod_mul (f := fun q : ℝ => exp (A / T * cos (q - α)))
    (g := fun p : ℝ => exp (-(1 / (2 * M * T)) * p ^ 2)), integral_gaussian,
    ← intervalIntegral.integral_of_le (by positivity)]
  have hq : (((∫ q in (0 : ℝ)..2 * π, exp (A / T * cos (q - α))) : ℝ) : ℂ) =
      2 * π * SpecialFunctions.besselI0 ((A / T : ℝ) : ℂ) := by
    rw [← integral_cexp_cos_sub, ← intervalIntegral.integral_ofReal]
    congr 1; funext q; push_cast; rfl
  have hg : π / (1 / (2 * M * T)) = 2 * π * M * T := by field_simp
  rw [Complex.ofReal_mul, hq, hg]

/-! ## Linearized drift at a saddle: the Langer factor -/

/-- Linearized Klein–Kramers drift at a critical point of `V` with `V'' = −κ`:
`!![0, 1/M; κ, −D/M]` (`(J − R) ∇²H` with `J = !![0, 1; −1, 0]`, `R = diag(0, D)`,
`∇²H = diag(−κ, 1/M)`). -/
def kkJacobian (M D κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / M; κ, -D / M]

/-- Unstable eigenvalue `λ₊ = −D/(2M) + √(D²/(4M²) + κ/M)`. -/
def kkLambda (M D κ : ℝ) : ℝ := -D / (2 * M) + √(D ^ 2 / (4 * M ^ 2) + κ / M)

/-- `λ₊` solves the characteristic equation `M λ² + D λ − κ = 0`. -/
@[tmio T, powerlib_foundation] theorem kkLambda_quadratic {M D κ : ℝ} (hM : M ≠ 0)
    (hs : 0 ≤ D ^ 2 / (4 * M ^ 2) + κ / M) :
    M * kkLambda M D κ ^ 2 + D * kkLambda M D κ - κ = 0 := by
  unfold kkLambda
  set s := √(D ^ 2 / (4 * M ^ 2) + κ / M)
  have hsq : s ^ 2 = D ^ 2 / (4 * M ^ 2) + κ / M := Real.sq_sqrt hs
  have h1 : M * (-D / (2 * M) + s) ^ 2 = D ^ 2 / (4 * M) - D * s + M * s ^ 2 := by
    field_simp; ring
  have h2 : M * s ^ 2 = D ^ 2 / (4 * M) + κ := by rw [hsq]; field_simp
  rw [h1, h2]
  ring

/-- `λ₊` is an eigenvalue of the linearized drift with eigenvector `(1, M λ₊)`. -/
@[tmio T, powerlib_foundation] theorem kkJacobian_mulVec {M D κ : ℝ} (hM : M ≠ 0)
    (hs : 0 ≤ D ^ 2 / (4 * M ^ 2) + κ / M) :
    kkJacobian M D κ *ᵥ ![1, M * kkLambda M D κ] =
      kkLambda M D κ • ![1, M * kkLambda M D κ] := by
  have hquad := kkLambda_quadratic hM hs
  have hdm : D / M * (M * kkLambda M D κ) = D * kkLambda M D κ := by field_simp
  ext i; fin_cases i
  · simp [kkJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  · simp [kkJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (-1 : ℝ) * hquad - hdm

/-- **Langer factor**: `λ₊/ω_b = √(1 + ζ²) − ζ` with `ω_b = √(κ/M)`, `ζ = D/(2√(M κ))`. -/
@[tmio T, powerlib_foundation] theorem kkLambda_div {M D κ : ℝ} (hM : 0 < M) (hκ : 0 < κ) :
    kkLambda M D κ / √(κ / M) = √(1 + (D / (2 * √(M * κ))) ^ 2) - D / (2 * √(M * κ)) := by
  have hω : 0 < √(κ / M) := Real.sqrt_pos.mpr (div_pos hκ hM)
  have hs : 0 < √(M * κ) := Real.sqrt_pos.mpr (mul_pos hM hκ)
  have hMκ : √(κ / M) * √(M * κ) = κ := by
    rw [← Real.sqrt_mul (div_pos hκ hM).le, show κ / M * (M * κ) = κ ^ 2 by field_simp,
      Real.sqrt_sq hκ.le]
  rw [div_eq_iff hω.ne']
  have h1 : D / (2 * √(M * κ)) * √(κ / M) = D / (2 * M) := by
    have hsM : √(M * κ) = M * √(κ / M) := by
      rw [← Real.sqrt_sq hM.le, ← Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM.le]
      congr 1; field_simp
    rw [hsM]; field_simp
  have h2 : √(1 + (D / (2 * √(M * κ))) ^ 2) * √(κ / M) =
      √(D ^ 2 / (4 * M ^ 2) + κ / M) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_pos hM hκ).le]
    field_simp
    ring
  rw [sub_mul, h1, h2, kkLambda]
  ring

/-- For `ζ ≥ 0` the Langer factor is at most one: momentum damping slows the escape. -/
@[tmio T, powerlib_foundation] theorem kkLambda_div_le_one {ζ : ℝ} (hζ : 0 ≤ ζ) :
    √(1 + ζ ^ 2) - ζ ≤ 1 := by
  have : √(1 + ζ ^ 2) ≤ 1 + ζ := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  linarith

end powerlib.Stochastic.KleinKramers
