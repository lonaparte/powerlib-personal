import theorem.GridTiedConverter.GFM.VoltageModulationFloquet

/-! # Synchronizing core with a dynamic Q–V loop: eigen-data, forced response and voltage pump

`VoltageModulationQV` treats the Q–V droop as quasi-static: the EMF magnitude is solved from the
droop law and only its slope enters. Here the Q–V loop has its own dynamics,
`τ Ė = E* − E − k_q(Q − Q*)`, so the EMF is a fourth state. Through the partial derivatives of the
port maps `P(δ, E, V)`, `Q(δ, E, V)` at the operating point, the eigenvalue equation and the
forced angle of the four-state linearization are those of the three-state core with a
frequency-dependent synchronizing coefficient `K_eff(s) = P_δ − k_q P_E Q_δ/(τs + b)` and voltage
sensitivity `P_V,eff(s) = P_V − k_q P_E Q_V/(τs + b)`, `b = 1 + k_q Q_E`.

Model boundary.
* States `(δ, Δω, P_f, E)`: `δ̇ = ω₀Δω`, `2HΔω̇ = P* − P_f − DΔω`, `Ṗ_f = ω_c(P − P_f)`,
  `τĖ = E* − E − k_q(Q − Q*)`. `DynQV` holds `ω₀, H, D, ω_c, τ, k_q` and the first and second
  partial derivatives of `P`, `Q` in `(δ, E)` and their `V`-derivatives at the operating point;
  the smooth field is `VoltageModulationQVOrbit`.
* Quasi-static network (the port maps); the Q–V loop is a first-order lag on the EMF magnitude.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2 (framework: `A₀`, `A₁ = Σ (∂A/∂x_l) z_l + G û`, `g = u A₁ r̄`), §3 (VSG core);
the dynamic Q–V loop and the voltage excitation are new.

Results.
* `A0r`, `Bv`, `A1` — the state matrix, the voltage input and the modulation (rows `P_f` and `E`).
* `lag`, `Keff`, `PVeff`, `charF`, `charFd`, `hasDerivAt_charF`, `charF_clear` — the
  characteristic function `F(s) = s(s + a)(s + ω_c) + ω₀ω_c K_eff(s)/(2H)` and its derivative.
* `right_eig`, `left_eig`, `left_right` — the eigentriple at a root of `F`; `lag_ne` — the lag
  never vanishes on the imaginary axis.
* `forcedδ`, `forced`, `forced_eq` — the forced response
  `z_δ = −(ω₀ω_c P_V,eff(s) V/2H)/F(s)`, `z_E = −k_q(Q_δ z_δ + Q_V V)/(τs + b)`.
* `gV`, `gV_eq` — the voltage pump `u A₁ r̄` element by element.
* `core3`, `charF_kq_zero`, `gV_kq_zero` — without the Q–V loop the core is the three-state core
  and its pump is that of `VoltageModulationQV.pump_eq`.
* `Keff_static`, `PVeff_static` — at `τ = 0` the effective coefficients are the total
  derivatives along the quasi-static branch `E = E* − k_q(Q − Q*)`.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the dynamic Q–V core (eigentriple, forced response, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
open Complex Matrix
open powerlib.ParametricResonance

/-- The synchronizing core with a dynamic Q–V loop, through the partial derivatives of the port
maps `P(δ, E, V)`, `Q(δ, E, V)` at the operating point. -/
structure DynQV where
  ω0 : ℝ
  H : ℝ
  D : ℝ
  ωc : ℝ
  τ : ℝ
  kq : ℝ
  Pδ : ℝ
  PE : ℝ
  PV : ℝ
  Qδ : ℝ
  QE : ℝ
  QV : ℝ
  Pδδ : ℝ
  PδE : ℝ
  PEE : ℝ
  PδV : ℝ
  PEV : ℝ
  Qδδ : ℝ
  QδE : ℝ
  QEE : ℝ
  QδV : ℝ
  QEV : ℝ

namespace DynQV

variable (c : DynQV)

/-- The state matrix in `(δ, Δω, P_f, E)`. -/
def A0r : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, c.ω0, 0, 0;
    0, -c.D / (2 * c.H), -1 / (2 * c.H), 0;
    c.ωc * c.Pδ, 0, -c.ωc, c.ωc * c.PE;
    -(c.kq * c.Qδ) / c.τ, 0, 0, -(1 + c.kq * c.QE) / c.τ]

/-- The voltage input `∂_V f`. -/
def Bv : Fin 4 → ℂ := ![0, 0, c.ωc * c.PV, -(c.kq * c.QV) / c.τ]

/-- `A₁`: the rows `P_f` and `E` are modulated through the second derivatives of `P` and `Q`. -/
def A1 (zδ zE V : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    c.ωc * (c.Pδδ * zδ + c.PδE * zE + c.PδV * V), 0, 0,
      c.ωc * (c.PδE * zδ + c.PEE * zE + c.PEV * V);
    -(c.kq / c.τ) * (c.Qδδ * zδ + c.QδE * zE + c.QδV * V), 0, 0,
      -(c.kq / c.τ) * (c.QδE * zδ + c.QEE * zE + c.QEV * V)]

def a : ℂ := (c.D : ℂ) / (2 * c.H)
/-- `b = 1 + k_q Q_E`: the static gain of the Q–V loop. -/
def b : ℝ := 1 + c.kq * c.QE
/-- The Q–V lag `τ s + b`. -/
def lag (s : ℂ) : ℂ := c.τ * s + c.b
/-- The synchronizing coefficient seen through the Q–V loop, `P_δ − k_q P_E Q_δ/(τ s + b)`. -/
def Keff (s : ℂ) : ℂ := c.Pδ - c.kq * c.PE * c.Qδ / c.lag s
/-- The voltage sensitivity seen through the Q–V loop, `P_V − k_q P_E Q_V/(τ s + b)`. -/
def PVeff (s : ℂ) : ℂ := c.PV - c.kq * c.PE * c.QV / c.lag s
/-- The characteristic function `s(s + a)(s + ω_c) + ω₀ω_c K_eff(s)/(2H)`; its zeros away from
`s = −b/τ` are the eigenvalues. -/
def charF (s : ℂ) : ℂ := s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * c.Keff s / (2 * c.H)
/-- Its derivative. -/
def charFd (s : ℂ) : ℂ :=
  3 * s ^ 2 + 2 * (c.a + c.ωc) * s + c.a * c.ωc +
    c.ω0 * c.ωc * c.τ * c.kq * c.PE * c.Qδ / (2 * c.H * c.lag s ^ 2)

def right (s : ℂ) : Fin 4 → ℂ :=
  ![1, s / c.ω0, -(2 * c.H * s + c.D) * s / c.ω0, -(c.kq * c.Qδ) / c.lag s]

def left (s : ℂ) : Fin 4 → ℂ :=
  let k := -(c.ω0 : ℂ) / (2 * c.H * c.charFd s)
  ![k * (-(2 * c.H * (s + c.ωc) * (s + c.a)) / c.ω0), k * (-(2 * c.H * (s + c.ωc))), k,
    k * (c.τ * c.ωc * c.PE / c.lag s)]

/-- The forced angle `z_δ = −(ω₀ω_c P_V,eff(s) V/2H)/F(s)`. -/
def forcedδ (s V : ℂ) : ℂ := -(c.ω0 * c.ωc * c.PVeff s * V / (2 * c.H)) / c.charF s

def forced (s V : ℂ) : Fin 4 → ℂ :=
  ![c.forcedδ s V, s * c.forcedδ s V / c.ω0, -(2 * c.H * s + c.D) * s * c.forcedδ s V / c.ω0,
    -(c.kq * (c.Qδ * c.forcedδ s V + c.QV * V)) / c.lag s]

@[tmio M, powerlib_domain] theorem hasDerivAt_charF {s : ℂ} (hl : c.lag s ≠ 0) :
    HasDerivAt c.charF (c.charFd s) s := by
  have hlag' : HasDerivAt (fun x : ℂ => (c.τ : ℂ) * x + c.b) (c.τ : ℂ) s := by
    simpa using ((hasDerivAt_id s).const_mul (c.τ : ℂ)).add_const (c.b : ℂ)
  have hlag : HasDerivAt c.lag (c.τ : ℂ) s := hlag'
  have hinv := hlag.inv hl
  have hK : HasDerivAt c.Keff (-(c.kq * c.PE * c.Qδ) * (-(c.τ : ℂ) / c.lag s ^ 2)) s := by
    have := (hinv.const_mul (-(c.kq * c.PE * c.Qδ : ℂ))).const_add (c.Pδ : ℂ)
    convert this using 1
    funext x; simp [Keff, div_eq_mul_inv]; ring
  have hp : HasDerivAt (fun x : ℂ => x * (x + c.a) * (x + c.ωc))
      (3 * s ^ 2 + 2 * (c.a + c.ωc) * s + c.a * c.ωc) s := by
    have h1 := (((hasDerivAt_id' s).mul ((hasDerivAt_id' s).add_const c.a)).mul
      ((hasDerivAt_id' s).add_const (c.ωc : ℂ)))
    convert h1 using 1
    simp only [Pi.mul_apply]; ring
  have := hp.add (hK.const_mul ((c.ω0 * c.ωc : ℂ) / (2 * c.H)))
  convert this using 1
  · funext x; simp [charF]; ring
  · simp only [charFd]; field_simp

/-- The characteristic function with the denominators cleared:
`2H (τs + b) F(s) = s(2Hs + D)(s + ω_c)(τs + b) + ω₀ω_c(P_δ(τs + b) − k_q P_E Q_δ)`. -/
@[tmio M, powerlib_domain] theorem charF_clear (hH : c.H ≠ 0) {s : ℂ} (hl : c.lag s ≠ 0) :
    2 * c.H * c.lag s * c.charF s = s * (2 * c.H * s + c.D) * (s + c.ωc) * c.lag s +
      c.ω0 * c.ωc * (c.Pδ * c.lag s - c.kq * c.PE * c.Qδ) := by
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [charF, Keff, a]
  field_simp

@[tmio M, powerlib_domain] theorem right_eig {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hl : c.lag s ≠ 0) (hs : c.charF s = 0) :
    c.A0r.map (algebraMap ℝ ℂ) *ᵥ c.right s = s • c.right s := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have key := c.charF_clear hH hl
  rw [hs, mul_zero] at key
  funext i
  fin_cases i <;> simp [A0r, right, mulVec, dotProduct, Fin.sum_univ_four] <;> field_simp
  · ring
  · linear_combination (-1 : ℂ) * key
  · simp only [lag, b]; push_cast; ring

@[tmio M, powerlib_domain] theorem left_eig {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hl : c.lag s ≠ 0) (hs : c.charF s = 0) :
    c.left s ᵥ* c.A0r.map (algebraMap ℝ ℂ) = s • c.left s := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have key := c.charF_clear hH hl
  rw [hs, mul_zero] at key
  funext j
  fin_cases j <;> simp [A0r, left, vecMul, dotProduct, Fin.sum_univ_four, a] <;> field_simp
  · congr 1; linear_combination key
  · ring
  · ring
  · simp only [lag, b]; push_cast; ring

@[tmio M, powerlib_domain] theorem left_right {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hl : c.lag s ≠ 0) (hd : c.charFd s ≠ 0) : c.left s ⬝ᵥ c.right s = 1 := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  calc c.left s ⬝ᵥ c.right s = c.charFd s / c.charFd s := by
        conv_rhs => arg 1; rw [charFd]
        simp [left, right, dotProduct, Fin.sum_univ_four, a]
        field_simp
        ring
    _ = 1 := div_self hd

@[tmio M, powerlib_domain] theorem forced_eq {s : ℂ} (V : ℂ) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hl : c.lag s ≠ 0) (hF : c.charF s ≠ 0) :
    s • c.forced s V - c.A0r.map (algebraMap ℝ ℂ) *ᵥ c.forced s V = V • c.Bv := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have key := c.charF_clear hH hl
  funext i
  fin_cases i <;> simp [A0r, forced, forcedδ, Bv, PVeff, mulVec, dotProduct, Fin.sum_univ_four] <;>
    field_simp
  · ring
  · ring
  · linear_combination (-((c.ωc : ℂ) * V * ((c.PV : ℂ) * c.lag s - c.kq * c.PE * c.QV))) * key
  · simp only [lag, b]; push_cast; ring

/-- On the imaginary axis the Q–V lag never vanishes: `τ jω + b ≠ 0` for `τ ≠ 0`, `ω ≠ 0`. -/
@[tmio M, powerlib_domain] theorem lag_ne {ω : ℝ} (hτ : c.τ ≠ 0) (hω : ω ≠ 0) :
    c.lag (ω * I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [lag] at this
  tauto

/-- The voltage pump `g_V = u A₁ r̄` at `λ = jΩ` along the first-order orbit `z(2jΩ) V̂`. -/
def gV (Ω Vh : ℝ) : ℂ :=
  Element.pump (c.A1 (c.forced (2 * Ω * I) Vh 0) (c.forced (2 * Ω * I) Vh 3) Vh)
    (c.left (Ω * I)) (c.right (Ω * I))

/-- `g_V` element by element: the `P_f` row through the second derivatives of `P`, the `E` row
through those of `Q`, each on the angle and EMF components `1`, `r̄_E` of `r̄`. -/
@[tmio M, powerlib_domain] theorem gV_eq (Ω Vh : ℝ) :
    c.gV Ω Vh =
      c.left (Ω * I) 2 * (c.ωc * (c.Pδδ * c.forced (2 * Ω * I) Vh 0 +
          c.PδE * c.forced (2 * Ω * I) Vh 3 + c.PδV * Vh) +
        c.ωc * (c.PδE * c.forced (2 * Ω * I) Vh 0 + c.PEE * c.forced (2 * Ω * I) Vh 3 +
          c.PEV * Vh) * star (c.right (Ω * I) 3)) -
      c.left (Ω * I) 3 * (c.kq / c.τ) * ((c.Qδδ * c.forced (2 * Ω * I) Vh 0 +
          c.QδE * c.forced (2 * Ω * I) Vh 3 + c.QδV * Vh) +
        (c.QδE * c.forced (2 * Ω * I) Vh 0 + c.QEE * c.forced (2 * Ω * I) Vh 3 +
          c.QEV * Vh) * star (c.right (Ω * I) 3)) := by
  simp only [gV, Element.pump, A1, dotProduct, mulVec, Fin.sum_univ_four]
  simp [right]
  ring

/-! ### Reductions -/

/-- The three-state synchronizing core with the same `P_δ`, `P_V`, `P_δδ`, `P_δV`. -/
def core3 : Core := ⟨c.ω0, c.H, c.D, c.ωc, c.Pδ, c.PV, c.Pδδ, c.PδV⟩

/-- Without the Q–V loop (`k_q = 0`) the characteristic function is that of the three-state core. -/
@[tmio M, powerlib_domain] theorem charF_kq_zero (h : c.kq = 0) (s : ℂ) :
    c.charF s = c.core3.charP s := by
  simp [charF, Keff, h, Core.charP, Core.d0, a, Core.a, core3]

/-- Without the Q–V loop the voltage pump is the pump of the three-state core
(`VoltageModulationQV.pump_eq`). -/
@[tmio M, powerlib_domain] theorem gV_kq_zero (h : c.kq = 0) (Ω Vh : ℝ) :
    c.gV Ω Vh = Element.pump (c.core3.A1 (c.core3.forcedVδ (2 * Ω * I) Vh) Vh)
      (c.core3.left (Ω * I)) (c.core3.right (Ω * I)) := by
  rw [gV_eq]
  simp [Element.pump, Core.A1, Core.left, Core.right, left, right, forced, forcedδ,
    Core.forcedVδ, PVeff, Keff, charF, Core.charP, charFd, Core.charD, h, core3, a, Core.a,
    Core.d0, dotProduct, mulVec, Fin.sum_univ_three]

/-- The quasi-static limit `τ = 0`: the effective synchronizing coefficient is the total
derivative `P_δ + P_E E_δ` along the branch `E = E* − k_q(Q − Q*)`, whose slope solves
`E_δ = −k_q(Q_δ + Q_E E_δ)`. -/
@[tmio M, powerlib_domain] theorem Keff_static (hτ : c.τ = 0) (hb : c.b ≠ 0) {e : ℝ}
    (he : e = -(c.kq * (c.Qδ + c.QE * e))) (s : ℂ) : c.Keff s = c.Pδ + c.PE * e := by
  have hbc : (c.b : ℂ) ≠ 0 := by exact_mod_cast hb
  have he' : e = -(c.kq * c.Qδ) / c.b := by
    rw [eq_div_iff hb, b]; linear_combination (1 + c.kq * c.QE) * he - c.kq * c.QE * he + he * 0
  have hi : (c.b : ℂ) * (c.b : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hbc
  simp only [Keff, lag, hτ, he']
  push_cast
  field_simp
  linear_combination (-(c.kq * c.PE * c.Qδ : ℂ)) * hi

/-- The quasi-static limit `τ = 0`: the effective voltage sensitivity is the total derivative
`P_V + P_E E_V` along the quasi-static Q–V branch, `E_V = −k_q(Q_V + Q_E E_V)`. -/
@[tmio M, powerlib_domain] theorem PVeff_static (hτ : c.τ = 0) (hb : c.b ≠ 0) {e : ℝ}
    (he : e = -(c.kq * (c.QV + c.QE * e))) (s : ℂ) : c.PVeff s = c.PV + c.PE * e := by
  have hbc : (c.b : ℂ) ≠ 0 := by exact_mod_cast hb
  have he' : e = -(c.kq * c.QV) / c.b := by
    rw [eq_div_iff hb, b]; linear_combination he
  have hi : (c.b : ℂ) * (c.b : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hbc
  simp only [PVeff, lag, hτ, he']
  push_cast
  field_simp
  linear_combination (-(c.kq * c.PE * c.QV : ℂ)) * hi

end DynQV
end VoltageModulation
end powerlib.GFM
