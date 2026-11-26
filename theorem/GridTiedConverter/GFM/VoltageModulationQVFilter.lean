import theorem.GridTiedConverter.GFM.VoltageModulationQVHopf
import theorem.Criteria.Routh3

/-! # Dynamic Q–V loop with a filtered reactive-power measurement

The Q–V loop of `VoltageModulationQVDynamic` acts on the instantaneous reactive power. Here the
measurement is filtered, `Q̇_f = ω_q(Q − Q_f)`, `τĖ = E* − E − k_q(Q_f − Q*)`, which adds a fifth
state. The structure is the same with the loop polynomial `L(s) = (s + ω_q)(τs + 1) + k_qω_qQ_E` in
place of `τs + b`: `K_f(s) = P_δ − k_qω_qP_EQ_δ/L(s)`. Every eigenvalue is a root of the quintic
`L(s)(s(s + a)(s + ω_c) + d₀) − ω_q d₁`; at the Hopf point it factors as
`(s² + Ω²)(τs³ + c₂s² + c₁s + c₀)`, and the Routh–Hurwitz conditions `c₂ > 0`, `c₀ > 0`,
`c₀τ < c₂c₁` make every other mode stable. As `ω_q → ∞` the filtered coefficient tends to the
unfiltered one.

Model boundary.
* States `(δ, Δω, P_f, E, Q_f)` (`qfieldf`), port maps `P`, `Q` of class `C³` as in
  `VoltageModulationQVOrbit`; `τ, ω_q > 0`; quasi-static network.
* Hopf conditions `c₁Ω² = l₁d₀ + l₀aω_c`, `c₀Ω² = l₀d₀ − ω_q d₁` (`l₁ = τω_q + 1`, `l₀ = ω_q b`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2, §3 (VSG core); the filtered dynamic Q–V loop and the voltage excitation
are new.

Results.
* `A0f`, `Bvf`, `A1f`, `lagf`, `lagfd`, `Kf`, `PVf`, `charFf`, `charFfd`, `rightf`, `leftf`,
  `forcedfδ`, `forcedf`, `charFf_clear`, `rightf_eig`, `leftf_eig`, `leftf_rightf`, `forcedf_eq`,
  `lagf_ne` — the algebraic core.
* `gVf`, `rhoEfff`, `gVf_compact` — `g_V = −(ω₀ω_c/(2H F'(jΩ))) ρ_eff`.
* `charP5`, `charP5d`, `c2f`, `c1f`, `c0f`, `charP5_eq`, `charP5d_eq`, `charP5_factor`,
  `charP5d_factor`, `eigf_cases`, `cubicf_ne`, `hopff_facts`, `hopff_simple`, `eigf_stable` — the
  quintic, its factorization, and the stability of the other modes (`Criteria.cubic_roots_re_neg_of`).
* `portf`, `qfieldf`, `contDiff_portf`, `contDiff_qfieldf`, `qjacf`, `matX_qfieldf`, `qxeqf`,
  `qfieldf_eq_zero`, `qjacf_eq`, `fderivW_qfieldf`, `smDx_qfieldf`, `smM1_qfieldf`,
  `smA1_qfieldf`, `zorbf_qfieldf` — the smooth field.
* `orbit_qvf_hopf_stable`, `orbit_qvf_hopf_unstable`, `orbit_qvf_hopf_exp_stable`,
  `orbit_lossyf_hopf_stable`, `orbit_lossyf_hopf_unstable` — end-to-end with explicit conditions.
* `Kf_tendsto` — `K_f(s) → K_eff(s)` as `ω_q → ∞`.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the voltage-modulated filtered dynamic Q–V core.
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace DynQV
open Complex Matrix
open powerlib.ParametricResonance
open Filter Topology
open powerlib.ParametricResonance.ForcedOrbit (ofv matX smDx smM1 smA1 smJ)

variable (c : DynQV) (ωq : ℝ)

/-! ### The core with a filtered reactive-power measurement -/

/-- The state matrix in `(δ, Δω, P_f, E, Q_f)`, `Q̇_f = ω_q(Q − Q_f)`. -/
def A0f : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, c.ω0, 0, 0, 0;
    0, -c.D / (2 * c.H), -1 / (2 * c.H), 0, 0;
    c.ωc * c.Pδ, 0, -c.ωc, c.ωc * c.PE, 0;
    0, 0, 0, -1 / c.τ, -c.kq / c.τ;
    ωq * c.Qδ, 0, 0, ωq * c.QE, -ωq]

/-- The voltage input. -/
def Bvf : Fin 5 → ℂ := ![0, 0, c.ωc * c.PV, 0, ωq * c.QV]

/-- `A₁`: the rows `P_f` and `Q_f` are modulated. -/
def A1f (zδ zE V : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 0, 0, 0, 0;
    0, 0, 0, 0, 0;
    c.ωc * (c.Pδδ * zδ + c.PδE * zE + c.PδV * V), 0, 0,
      c.ωc * (c.PδE * zδ + c.PEE * zE + c.PEV * V), 0;
    0, 0, 0, 0, 0;
    ωq * (c.Qδδ * zδ + c.QδE * zE + c.QδV * V), 0, 0,
      ωq * (c.QδE * zδ + c.QEE * zE + c.QEV * V), 0]

/-- The filtered Q–V loop `(s + ω_q)(τs + 1) + k_q ω_q Q_E`. -/
def lagf (s : ℂ) : ℂ := (s + ωq) * (c.τ * s + 1) + c.kq * ωq * c.QE

/-- Its derivative. -/
def lagfd (s : ℂ) : ℂ := 2 * c.τ * s + c.τ * ωq + 1

/-- The effective synchronizing coefficient `P_δ − k_q ω_q P_E Q_δ/L(s)`. -/
def Kf (s : ℂ) : ℂ := c.Pδ - c.kq * ωq * c.PE * c.Qδ / c.lagf ωq s

/-- The effective voltage sensitivity `P_V − k_q ω_q P_E Q_V/L(s)`. -/
def PVf (s : ℂ) : ℂ := c.PV - c.kq * ωq * c.PE * c.QV / c.lagf ωq s

def charFf (s : ℂ) : ℂ := s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * c.Kf ωq s / (2 * c.H)

def charFfd (s : ℂ) : ℂ :=
  3 * s ^ 2 + 2 * (c.a + c.ωc) * s + c.a * c.ωc +
    c.ω0 * c.ωc * c.kq * ωq * c.PE * c.Qδ * c.lagfd ωq s / (2 * c.H * c.lagf ωq s ^ 2)

def rightf (s : ℂ) : Fin 5 → ℂ :=
  ![1, s / c.ω0, -(2 * c.H * s + c.D) * s / c.ω0, -(c.kq * ωq * c.Qδ) / c.lagf ωq s,
    ωq * c.Qδ * (c.τ * s + 1) / c.lagf ωq s]

def leftf (s : ℂ) : Fin 5 → ℂ :=
  let k := -(c.ω0 : ℂ) / (2 * c.H * c.charFfd ωq s)
  ![k * (-(2 * c.H * (s + c.ωc) * (s + c.a)) / c.ω0), k * (-(2 * c.H * (s + c.ωc))), k,
    k * (c.τ * c.ωc * c.PE * (s + ωq) / c.lagf ωq s), k * (-(c.kq * c.ωc * c.PE) / c.lagf ωq s)]

def forcedfδ (s V : ℂ) : ℂ := -(c.ω0 * c.ωc * c.PVf ωq s * V / (2 * c.H)) / c.charFf ωq s

def forcedf (s V : ℂ) : Fin 5 → ℂ :=
  ![c.forcedfδ ωq s V, s * c.forcedfδ ωq s V / c.ω0,
    -(2 * c.H * s + c.D) * s * c.forcedfδ ωq s V / c.ω0,
    -(c.kq * ωq * (c.Qδ * c.forcedfδ ωq s V + c.QV * V)) / c.lagf ωq s,
    ωq * (c.τ * s + 1) * (c.Qδ * c.forcedfδ ωq s V + c.QV * V) / c.lagf ωq s]

@[tmio M, powerlib_domain] theorem charFf_clear (hH : c.H ≠ 0) {s : ℂ} (hl : c.lagf ωq s ≠ 0) :
    2 * c.H * c.lagf ωq s * c.charFf ωq s = s * (2 * c.H * s + c.D) * (s + c.ωc) * c.lagf ωq s +
      c.ω0 * c.ωc * (c.Pδ * c.lagf ωq s - c.kq * ωq * c.PE * c.Qδ) := by
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [charFf, Kf, a]
  field_simp

@[tmio M, powerlib_domain] theorem rightf_eig {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hl : c.lagf ωq s ≠ 0) (hs : c.charFf ωq s = 0) :
    (c.A0f ωq).map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq s = s • c.rightf ωq s := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have key := c.charFf_clear ωq hH hl
  rw [hs, mul_zero] at key
  funext i
  fin_cases i <;> simp [A0f, rightf, mulVec, dotProduct, Fin.sum_univ_five] <;> field_simp
  · ring
  · linear_combination (-1 : ℂ) * key
  · ring
  · simp only [lagf]; ring

@[tmio M, powerlib_domain] theorem leftf_eig {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hl : c.lagf ωq s ≠ 0) (hs : c.charFf ωq s = 0) :
    c.leftf ωq s ᵥ* (c.A0f ωq).map (algebraMap ℝ ℂ) = s • c.leftf ωq s := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have key := c.charFf_clear ωq hH hl
  rw [hs, mul_zero] at key
  funext j
  fin_cases j <;> simp [A0f, leftf, vecMul, dotProduct, Fin.sum_univ_five, a] <;> field_simp
  · congr 1; linear_combination key
  · ring
  · ring
  · simp only [lagf]; ring
  · ring

@[tmio M, powerlib_domain] theorem leftf_rightf {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hl : c.lagf ωq s ≠ 0) (hd : c.charFfd ωq s ≠ 0) : c.leftf ωq s ⬝ᵥ c.rightf ωq s = 1 := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  calc c.leftf ωq s ⬝ᵥ c.rightf ωq s = c.charFfd ωq s / c.charFfd ωq s := by
        conv_rhs => arg 1; rw [charFfd]
        simp [leftf, rightf, dotProduct, Fin.sum_univ_five, a, lagfd]
        field_simp
        ring
    _ = 1 := div_self hd

@[tmio M, powerlib_domain] theorem forcedf_eq {s : ℂ} (V : ℂ) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hl : c.lagf ωq s ≠ 0) (hF : c.charFf ωq s ≠ 0) :
    s • c.forcedf ωq s V - (c.A0f ωq).map (algebraMap ℝ ℂ) *ᵥ c.forcedf ωq s V = V • c.Bvf ωq := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have key := c.charFf_clear ωq hH hl
  funext i
  fin_cases i <;> simp [A0f, forcedf, forcedfδ, Bvf, PVf, mulVec, dotProduct, Fin.sum_univ_five] <;>
    field_simp
  · ring
  · ring
  · linear_combination (-((c.ωc : ℂ) * V * ((c.PV : ℂ) * c.lagf ωq s -
      c.kq * ωq * c.PE * c.QV))) * key
  · ring
  · simp only [lagf]; ring

@[tmio M, powerlib_domain] theorem lagf_ne {ω : ℝ} (hτ : 0 < c.τ) (hωq : 0 < ωq) (hω : ω ≠ 0) :
    c.lagf ωq (ω * I) ≠ 0 := by
  intro h
  have him : (c.lagf ωq (ω * I)).im = (c.τ * ωq + 1) * ω := by
    simp [lagf, Complex.mul_im, Complex.mul_re]; ring
  rw [h, Complex.zero_im] at him
  rcases mul_eq_zero.mp him.symm with h1 | h1
  · nlinarith [mul_pos hτ hωq]
  · exact hω h1

/-- The voltage pump `g_V = u A₁ r̄` of the filtered core at `λ = jΩ`. -/
def gVf (Ω Vh : ℝ) : ℂ :=
  Element.pump (c.A1f ωq (c.forcedf ωq (2 * Ω * I) Vh 0) (c.forcedf ωq (2 * Ω * I) Vh 3) Vh)
    (c.leftf ωq (Ω * I)) (c.rightf ωq (Ω * I))

/-- The modulation of the effective coefficient of the filtered core. -/
def rhoEfff (Ω Vh : ℝ) : ℂ :=
  (c.Pδδ * c.forcedf ωq (2 * Ω * I) Vh 0 + c.PδE * c.forcedf ωq (2 * Ω * I) Vh 3 + c.PδV * Vh) +
    (c.PδE * c.forcedf ωq (2 * Ω * I) Vh 0 + c.PEE * c.forcedf ωq (2 * Ω * I) Vh 3 +
      c.PEV * Vh) * star (c.rightf ωq (Ω * I) 3) -
    c.kq * ωq * c.PE / c.lagf ωq (Ω * I) *
      ((c.Qδδ * c.forcedf ωq (2 * Ω * I) Vh 0 + c.QδE * c.forcedf ωq (2 * Ω * I) Vh 3 +
          c.QδV * Vh) +
        (c.QδE * c.forcedf ωq (2 * Ω * I) Vh 0 + c.QEE * c.forcedf ωq (2 * Ω * I) Vh 3 +
          c.QEV * Vh) * star (c.rightf ωq (Ω * I) 3))

/-- `g_V = −(ω₀ω_c/(2H F'(jΩ))) ρ_eff` for the filtered core. -/
@[tmio M, powerlib_domain] theorem gVf_compact (Ω Vh : ℝ) :
    c.gVf ωq Ω Vh = -(c.ω0 * c.ωc / (2 * c.H * c.charFfd ωq (Ω * I))) * c.rhoEfff ωq Ω Vh := by
  simp only [gVf, Element.pump, A1f, leftf, rhoEfff, dotProduct, mulVec, Fin.sum_univ_five]
  simp [rightf]
  ring

/-! ### The quintic and its factorization at the Hopf point -/

/-- The characteristic quintic `L(s)(s(s + a)(s + ω_c) + d₀) − ω_q d₁`. -/
def charP5 (s : ℂ) : ℂ :=
  c.lagf ωq s * (s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
    ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H))

/-- Its derivative. -/
def charP5d (s : ℂ) : ℂ :=
  c.lagfd ωq s * (s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
    c.lagf ωq s * (3 * s ^ 2 + 2 * (c.a + c.ωc) * s + c.a * c.ωc)

/-- The cubic factor `τs³ + c₂s² + c₁s + c₀`: `c₂`. -/
def c2f : ℝ := c.τ * (c.D / (2 * c.H) + c.ωc) + (c.τ * ωq + 1)

/-- `c₁`. -/
def c1f (Ω : ℝ) : ℝ :=
  c.τ * (c.D / (2 * c.H) * c.ωc) + (c.τ * ωq + 1) * (c.D / (2 * c.H) + c.ωc) + ωq * c.b -
    c.τ * Ω ^ 2

/-- `c₀`. -/
def c0f (Ω : ℝ) : ℝ :=
  c.τ * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) + (c.τ * ωq + 1) * (c.D / (2 * c.H) * c.ωc) +
    ωq * c.b * (c.D / (2 * c.H) + c.ωc) - c.c2f ωq * Ω ^ 2

@[tmio M, powerlib_domain] theorem charP5_eq {s : ℂ} (hl : c.lagf ωq s ≠ 0) :
    c.lagf ωq s * c.charFf ωq s = c.charP5 ωq s := by
  simp only [charFf, Kf, charP5]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem charP5d_eq {s : ℂ} (hl : c.lagf ωq s ≠ 0) :
    c.lagfd ωq s * c.charFf ωq s + c.lagf ωq s * c.charFfd ωq s = c.charP5d ωq s := by
  simp only [charFf, Kf, charFfd, charP5d]
  field_simp
  ring

/-- At the Hopf point, in the explicit conditions `c₁Ω² = l₁d₀ + l₀aω_c` and
`c₀Ω² = l₀d₀ − ω_q d₁` (`l₁ = τω_q + 1`, `l₀ = ω_q b`), the quintic factors as
`(s² + Ω²)(τs³ + c₂s² + c₁s + c₀)`. -/
@[tmio M, powerlib_domain] theorem charP5_factor {Ω : ℝ}
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H))) (s : ℂ) :
    c.charP5 ωq s = (s ^ 2 + (Ω : ℂ) ^ 2) *
      (c.τ * s ^ 3 + c.c2f ωq * s ^ 2 + c.c1f ωq Ω * s + c.c0f ωq Ω) := by
  have hA' : ((c.c1f ωq Ω * Ω ^ 2 : ℝ) : ℂ) = (((c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc) : ℝ) : ℂ) := by rw [hA]
  have hB' : ((c.c0f ωq Ω * Ω ^ 2 : ℝ) : ℂ) = ((ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)) : ℝ) : ℂ) := by rw [hB]
  simp only [charP5, lagf, a, c2f, c1f, c0f, b] at hA' hB' ⊢
  push_cast at hA' hB' ⊢
  linear_combination (-s) * hA' - hB'

@[tmio M, powerlib_domain] theorem charP5d_factor {Ω : ℝ}
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc)) (s : ℂ) :
    c.charP5d ωq s = 2 * s * (c.τ * s ^ 3 + c.c2f ωq * s ^ 2 + c.c1f ωq Ω * s + c.c0f ωq Ω) +
      (s ^ 2 + (Ω : ℂ) ^ 2) * (3 * c.τ * s ^ 2 + 2 * c.c2f ωq * s + c.c1f ωq Ω) := by
  have hA' : ((c.c1f ωq Ω * Ω ^ 2 : ℝ) : ℂ) = (((c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc) : ℝ) : ℂ) := by rw [hA]
  simp only [charP5d, lagf, lagfd, a, c2f, c1f, c0f, b] at hA' ⊢
  push_cast at hA' ⊢
  linear_combination -hA'

/-! ### Eigenpairs of the filtered core -/

/-- Every eigenvalue of the filtered core is a root of the quintic; off the poles of the loop
the eigenvector is a multiple of `rightf λ`. -/
@[tmio M, powerlib_domain] theorem eigf_cases (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    {μ : ℂ} {v : Fin 5 → ℂ} (h : (c.A0f ωq).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (c.lagf ωq μ ≠ 0 → μ + ωq ≠ 0 → v = v 0 • c.rightf ωq μ) ∧
      (v ≠ 0 → c.charP5 ωq μ = 0) := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  simp [A0f, mulVec, dotProduct, Fin.sum_univ_five] at h0 h1 h2 h3 h4
  have e1 : v 1 = μ * v 0 / c.ω0 := by field_simp; linear_combination h0
  have e2 : v 2 = -(2 * c.H * μ + c.D) * μ * v 0 / c.ω0 := by
    rw [e1] at h1; field_simp at h1 ⊢; linear_combination -h1
  have h3' : (c.τ * μ + 1) * v 3 + c.kq * v 4 = 0 := by
    field_simp at h3; linear_combination -h3
  have h4' : (μ + ωq) * v 4 = ωq * (c.Qδ * v 0 + c.QE * v 3) := by linear_combination -h4
  have E1 : c.lagf ωq μ * v 3 = -(c.kq * ωq * c.Qδ * v 0) := by
    simp only [lagf]; linear_combination (μ + ωq) * h3' - c.kq * h4'
  have hchar : c.charP5 ωq μ * v 0 = 0 := by
    rw [e2] at h2
    simp only [charP5, a]
    field_simp at h2 ⊢
    linear_combination (c.lagf ωq μ) * h2 - (c.ωc * c.ω0 * c.PE) * E1
  refine ⟨fun hl hq => ?_, fun hv => ?_⟩
  · have e3 : v 3 = -(c.kq * ωq * c.Qδ) * v 0 / c.lagf ωq μ := by
      field_simp; linear_combination E1
    have e4 : v 4 = ωq * c.Qδ * (c.τ * μ + 1) * v 0 / c.lagf ωq μ := by
      field_simp
      have : (μ + ωq) * (v 4 * c.lagf ωq μ - ωq * c.Qδ * (c.τ * μ + 1) * v 0) = 0 := by
        rw [e3] at h4'; field_simp at h4'
        simp only [lagf] at h4' ⊢
        linear_combination h4'
      have := (mul_eq_zero.mp this).resolve_left hq
      linear_combination this
    funext i; fin_cases i <;> simp [rightf, e1, e2, e3, e4] <;> ring
  · rcases eq_or_ne (v 0) 0 with hv0 | hv0
    · have hz1 : v 1 = 0 := by rw [e1, hv0]; simp
      have hz2 : v 2 = 0 := by rw [e2, hv0]; simp
      rw [hz2, hv0] at h2
      simp at h2
      rw [hv0] at E1 h4'
      rcases eq_or_ne (v 3) 0 with hv3 | hv3
      · rw [hv3] at h3' h4'
        simp at h3' h4'
        have hv4 : v 4 ≠ 0 := by
          intro hv4; apply hv; funext i; fin_cases i <;> simp [hv0, hz1, hz2, hv3, hv4]
        have hk : (c.kq : ℂ) = 0 := by
          rcases h3' with h | h
          · exact_mod_cast h
          · exact absurd h hv4
        have hm : μ = -ωq := by
          rcases h4' with h | h
          · linear_combination h
          · exact absurd h hv4
        simp only [charP5, lagf, hk, hm]
        ring
      · have hl : c.lagf ωq μ = 0 := by
          simp at E1; rcases E1 with h | h
          · exact h
          · exact absurd h hv3
        have hp : (c.ωc : ℂ) * c.PE = 0 := by
          rcases h2 with (h | h) | h
          · simp [h]
          · simp [h]
          · exact absurd h hv3
        simp only [charP5, hl, zero_mul, zero_sub]
        linear_combination (-(ωq * c.ω0 * c.kq * c.Qδ / (2 * c.H) : ℂ)) * hp
    · exact (mul_eq_zero.mp hchar).resolve_right hv0

/-- On the imaginary axis the cubic factor vanishes only where `c₀ = c₂ω²` and `c₁ = τω²`, which
the strict Routh condition `c₀τ < c₂c₁` excludes. -/
@[tmio M, powerlib_domain] theorem cubicf_ne {Ω k : ℝ} (hk : k ≠ 0)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω) :
    c.τ * ((k : ℂ) * I) ^ 3 + c.c2f ωq * ((k : ℂ) * I) ^ 2 + c.c1f ωq Ω * ((k : ℂ) * I) +
      c.c0f ωq Ω ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_succ, Complex.mul_re, Complex.mul_im] at hre him
  have h1 : c.c0f ωq Ω = c.c2f ωq * k ^ 2 := by linarith
  have h2 : c.c1f ωq Ω = c.τ * k ^ 2 := by
    have : k * (c.c1f ωq Ω - c.τ * k ^ 2) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hk
    linarith
  rw [h1, h2] at hR
  nlinarith

/-- At the explicit Hopf point with the strict Routh condition: `F(jΩ) = 0`, `F'(jΩ) ≠ 0`,
`F(2jΩ) ≠ 0`. -/
@[tmio M, powerlib_domain] theorem hopff_facts (hτ : 0 < c.τ) (hωq : 0 < ωq) {Ω : ℝ}
    (hΩ : Ω ≠ 0) (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω) (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H))) :
    c.charFf ωq (Ω * I) = 0 ∧ c.charFfd ωq (Ω * I) ≠ 0 ∧ c.charFf ωq (2 * Ω * I) ≠ 0 := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hl1 := c.lagf_ne ωq hτ hωq hΩ
  have hl2 : c.lagf ωq (2 * Ω * I) ≠ 0 := by
    have := c.lagf_ne ωq (ω := 2 * Ω) hτ hωq (mul_ne_zero two_ne_zero hΩ)
    push_cast at this; exact this
  have hF : c.charFf ωq (Ω * I) = 0 := by
    have h := c.charP5_eq ωq hl1
    rw [c.charP5_factor ωq hA hB, show ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 by
      linear_combination (Ω : ℂ) ^ 2 * I_sq, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hl1
  refine ⟨hF, ?_, ?_⟩
  · intro hd
    have h := c.charP5d_eq ωq hl1
    rw [hF, hd, mul_zero, mul_zero, add_zero, c.charP5d_factor ωq hA,
      show ((Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 by linear_combination (Ω : ℂ) ^ 2 * I_sq,
      zero_mul, add_zero] at h
    exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero))
      (c.cubicf_ne ωq hΩ hR) h.symm
  · intro h0
    have h := c.charP5_eq ωq hl2
    rw [h0, mul_zero, c.charP5_factor ωq hA hB] at h
    have e : (2 * (Ω : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
      linear_combination 4 * (Ω : ℂ) ^ 2 * I_sq
    rw [e] at h
    have h3 := c.cubicf_ne ωq (k := 2 * Ω) (mul_ne_zero two_ne_zero hΩ) hR
    push_cast at h3
    rw [show (2 * (Ω : ℂ) * I) = (2 * (Ω : ℂ)) * I by ring] at h
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hΩc)) h3 h.symm

/-- Geometric simplicity of `jΩ` for the filtered core. -/
@[tmio M, powerlib_domain] theorem hopff_simple (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ)
    (hωq : 0 < ωq) {Ω : ℝ} (hΩ : Ω ≠ 0) (hFd : c.charFfd ωq (Ω * I) ≠ 0) (v : Fin 5 → ℂ)
    (h : (c.A0f ωq).map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v) :
    v = (c.leftf ωq (Ω * I) ⬝ᵥ v) • c.rightf ωq (Ω * I) := by
  have hl := c.lagf_ne ωq hτ hωq hΩ
  have hq : (Ω : ℂ) * I + ωq ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; exact hΩ this
  have hv := (c.eigf_cases ωq hω0 hH hτ.ne' h).1 hl hq
  conv_rhs => rw [hv]
  rw [dotProduct_smul, c.leftf_rightf ωq hω0 hH hl hFd, smul_eq_mul, mul_one]
  exact hv

/-- Every eigenvalue of the filtered core other than `±jΩ` lies in the open left half plane when
the cubic factor satisfies the Routh–Hurwitz conditions `c₂ > 0`, `c₀ > 0`, `c₀τ < c₂c₁`. -/
@[tmio M, powerlib_domain] theorem eigf_stable (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ)
    {Ω : ℝ} (h2 : 0 < c.c2f ωq) (h0 : 0 < c.c0f ωq Ω)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω) (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    {μ : ℂ} {v : Fin 5 → ℂ} (hv : v ≠ 0) (h : (c.A0f ωq).map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (h1 : μ ≠ (Ω : ℂ) * I) (hm : μ ≠ -((Ω : ℂ) * I)) : μ.re < 0 := by
  have hP := (c.eigf_cases ωq hω0 hH hτ.ne' h).2 hv
  rw [c.charP5_factor ωq hA hB] at hP
  have hne : μ ^ 2 + (Ω : ℂ) ^ 2 ≠ 0 := by
    have : μ ^ 2 + (Ω : ℂ) ^ 2 = (μ - (Ω : ℂ) * I) * (μ + (Ω : ℂ) * I) := by
      linear_combination (Ω : ℂ) ^ 2 * I_sq
    rw [this]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (fun h => hm (eq_neg_of_add_eq_zero_left h))
  have hC := (mul_eq_zero.mp hP).resolve_left hne
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hg : c.c0f ωq Ω / c.τ < c.c2f ωq / c.τ * (c.c1f ωq Ω / c.τ) := by
    have e : c.c2f ωq / c.τ * (c.c1f ωq Ω / c.τ) - c.c0f ωq Ω / c.τ =
        (c.c2f ωq * c.c1f ωq Ω - c.c0f ωq Ω * c.τ) / c.τ ^ 2 := by
      field_simp
    have : 0 < (c.c2f ωq * c.c1f ωq Ω - c.c0f ωq Ω * c.τ) / c.τ ^ 2 :=
      div_pos (by linarith) (by positivity)
    linarith
  refine Criteria.cubic_roots_re_neg_of (div_pos h2 hτ) (div_pos h0 hτ) hg μ ?_
  push_cast
  field_simp
  linear_combination hC

/-! ### The filtered core as a smooth field -/

/-- The port point `((δ, E), V)` of a state of the filtered core. -/
def portf (q : (Fin 5 → ℝ) × ℝ) : (ℝ × ℝ) × ℝ := ((q.1 0, q.1 3), q.2)

/-- The synchronizing core with a filtered dynamic Q–V loop: states `(δ, Δω, P_f, E, Q_f)`,
`τĖ = E* − E − k_q(Q_f − Q*)`, `Q̇_f = ω_q(Q(δ, E, V) − Q_f)`. -/
def qfieldf (P Q : (ℝ × ℝ) × ℝ → ℝ) (Pset Eset Qset : ℝ) (q : (Fin 5 → ℝ) × ℝ) : Fin 5 → ℝ :=
  ![c.ω0 * q.1 1, (Pset - q.1 2 - c.D * q.1 1) / (2 * c.H), c.ωc * (P (portf q) - q.1 2),
    (Eset - q.1 3 - c.kq * (q.1 4 - Qset)) / c.τ, ωq * (Q (portf q) - q.1 4)]

omit c ωq in
@[tmio T, powerlib_foundation] theorem contDiff_portf {n : WithTop ℕ∞} : ContDiff ℝ n portf :=
  (((contDiff_apply ℝ ℝ (0 : Fin 5)).comp contDiff_fst).prodMk
    ((contDiff_apply ℝ ℝ (3 : Fin 5)).comp contDiff_fst)).prodMk contDiff_snd

@[tmio M, powerlib_domain] theorem contDiff_qfieldf {P Q : (ℝ × ℝ) × ℝ → ℝ} {n : WithTop ℕ∞}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) (Pset Eset Qset : ℝ) :
    ContDiff ℝ n (c.qfieldf ωq P Q Pset Eset Qset) := by
  have hx : ∀ i : Fin 5, ContDiff ℝ n fun q : (Fin 5 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have hPq : ContDiff ℝ n fun q => P (portf q) := hP.comp contDiff_portf
  have hQq : ContDiff ℝ n fun q => Q (portf q) := hQ.comp contDiff_portf
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (hx 1)
  · exact ((contDiff_const.sub (hx 2)).sub (contDiff_const.mul (hx 1))).div_const _
  · exact contDiff_const.mul (hPq.sub (hx 2))
  · exact ((contDiff_const.sub (hx 3)).sub
      (contDiff_const.mul ((hx 4).sub contDiff_const))).div_const _
  · exact contDiff_const.mul (hQq.sub (hx 4))

/-- The Jacobian of the filtered field at `(x, V)`. -/
def qjacf (P Q : (ℝ × ℝ) × ℝ → ℝ) (q : (Fin 5 → ℝ) × ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, c.ω0, 0, 0, 0;
    0, -c.D / (2 * c.H), -1 / (2 * c.H), 0, 0;
    c.ωc * dδ P (portf q), 0, -c.ωc, c.ωc * dE P (portf q), 0;
    0, 0, 0, -1 / c.τ, -c.kq / c.τ;
    ωq * dδ Q (portf q), 0, 0, ωq * dE Q (portf q), -ωq]

@[tmio M, powerlib_domain] theorem matX_qfieldf {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) (Pset Eset Qset : ℝ) (q : (Fin 5 → ℝ) × ℝ) :
    matX (c.qfieldf ωq P Q Pset Eset Qset) q = c.qjacf ωq P Q q := by
  refine ParametricResonance.ForcedOrbit.matX_of_line
    ((c.contDiff_qfieldf ωq hP hQ _ _ _).differentiable (by norm_num) _) fun y => ?_
  have hl : ∀ i, HasDerivAt (fun s : ℝ => (q.1 + s • y) i) (y i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y i)).const_add (q.1 i)
  have hline : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 3 G →
      HasDerivAt (fun s : ℝ => G (portf (q.1 + s • y, q.2)))
        (y 0 * dδ G (portf q) + y 3 * dE G (portf q)) 0 := fun G hG => by
    have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) (portf q)) (y 0) (y 3) 0
    simp only [zero_mul, add_zero, portf] at h ⊢
    convert h using 1
    funext s; simp
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine ((hl 1).const_mul c.ω0).congr_deriv ?_
    show _ = (c.qjacf ωq P Q q *ᵥ y) 0
    simp [qjacf, mulVec, dotProduct, Fin.sum_univ_five]
  · refine ((((hasDerivAt_const (0 : ℝ) Pset).sub (hl 2)).sub
      ((hl 1).const_mul c.D)).div_const (2 * c.H)).congr_deriv ?_
    show _ = (c.qjacf ωq P Q q *ᵥ y) 1
    simp [qjacf, mulVec, dotProduct, Fin.sum_univ_five]; ring
  · refine (((hline P hP).sub (hl 2)).const_mul c.ωc).congr_deriv ?_
    show _ = (c.qjacf ωq P Q q *ᵥ y) 2
    simp [qjacf, mulVec, dotProduct, Fin.sum_univ_five]; ring
  · refine ((((hasDerivAt_const (0 : ℝ) Eset).sub (hl 3)).sub
      (((hl 4).sub_const Qset).const_mul c.kq)).div_const c.τ).congr_deriv ?_
    show _ = (c.qjacf ωq P Q q *ᵥ y) 3
    simp [qjacf, mulVec, dotProduct, Fin.sum_univ_five]; ring
  · refine (((hline Q hQ).sub (hl 4)).const_mul ωq).congr_deriv ?_
    show _ = (c.qjacf ωq P Q q *ᵥ y) 4
    simp [qjacf, mulVec, dotProduct, Fin.sum_univ_five]; ring

/-- The operating point `(δ₀, 0, P, E₀, Q)` of the filtered core. -/
def qxeqf (P Q : (ℝ × ℝ) × ℝ → ℝ) (δ0 E0 V0 : ℝ) : Fin 5 → ℝ :=
  ![δ0, 0, P ((δ0, E0), V0), E0, Q ((δ0, E0), V0)]

@[tmio M, powerlib_domain] theorem qfieldf_eq_zero (P Q : (ℝ × ℝ) × ℝ → ℝ) (δ0 E0 V0 : ℝ) :
    c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeqf P Q δ0 E0 V0, V0) = 0 := by
  funext i
  fin_cases i <;> simp [qfieldf, qxeqf, portf]

@[tmio M, powerlib_domain] theorem qjacf_eq {P Q : (ℝ × ℝ) × ℝ → ℝ} {δ0 E0 V0 : ℝ}
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE) :
    c.qjacf ωq P Q (qxeqf P Q δ0 E0 V0, V0) = c.A0f ωq := by
  have e : portf (qxeqf P Q δ0 E0 V0, V0) = ((δ0, E0), V0) := by simp [portf, qxeqf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qjacf, A0f, e, hPδ, hPE, hQδ, hQE]

@[tmio M, powerlib_domain] theorem fderivW_qfieldf {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ} (hPV : dV P ((δ0, E0), V0) = c.PV)
    (hQV : dV Q ((δ0, E0), V0) = c.QV) :
    ofv (fderiv ℝ (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) (0, 1)) = c.Bvf ωq := by
  have hlv : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 3 G →
      HasDerivAt (fun s : ℝ => G (portf (qxeqf P Q δ0 E0 V0, V0 + s))) (dV G ((δ0, E0), V0)) 0 :=
    fun G hG => by
      have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) ((δ0, E0), V0)) 0 0 1
      simp only [zero_mul, mul_zero, add_zero, mul_one, one_mul, zero_add] at h
      convert h using 1
      funext s; simp [portf, qxeqf]
  have e : fderiv ℝ (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) (0, 1) =
      ![0, 0, c.ωc * c.PV, 0, ωq * c.QV] := by
    refine ParametricResonance.ForcedOrbit.fderivW_of_line
      ((c.contDiff_qfieldf ωq hP hQ _ _ _).differentiable (by norm_num) _)
      (hasDerivAt_pi.2 fun i => ?_)
    fin_cases i
    · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [qfieldf, qxeqf])
    · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [qfieldf, qxeqf])
    · have h := ((hlv P hP).sub_const (P ((δ0, E0), V0))).const_mul c.ωc
      rw [hPV] at h
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [qfieldf, qxeqf])
    · exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [qfieldf, qxeqf])
    · have h := ((hlv Q hQ).sub_const (Q ((δ0, E0), V0))).const_mul ωq
      rw [hQV] at h
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [qfieldf, qxeqf])
  rw [e]
  funext i
  fin_cases i <;> simp [ofv, Bvf]

@[tmio M, powerlib_domain] theorem smDx_qfieldf {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ}
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (y : Fin 5 → ℝ) :
    smDx (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) y =
      !![0, 0, 0, 0, 0;
        0, 0, 0, 0, 0;
        c.ωc * (y 0 * c.Pδδ + y 3 * c.PδE), 0, 0, c.ωc * (y 0 * c.PδE + y 3 * c.PEE), 0;
        0, 0, 0, 0, 0;
        ωq * (y 0 * c.Qδδ + y 3 * c.QδE), 0, 0, ωq * (y 0 * c.QδE + y 3 * c.QEE), 0] := by
  have hline : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 2 G →
      HasDerivAt (fun t : ℝ => G (portf (qxeqf P Q δ0 E0 V0 + t • y, V0)))
        (y 0 * dδ G ((δ0, E0), V0) + y 3 * dE G ((δ0, E0), V0)) 0 := fun G hG => by
    have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) ((δ0, E0), V0))
      (y 0) (y 3) 0
    simp only [zero_mul, mul_zero, add_zero] at h
    convert h using 1
    funext t; simp [portf, qxeqf]
  have hPd := hline _ (contDiff_dδ hP)
  rw [hPδδ, hPδE] at hPd
  have hPe := hline _ (contDiff_dE hP)
  rw [dδ_dE hP, hPδE, hPEE] at hPe
  have hQd := hline _ (contDiff_dδ hQ)
  rw [hQδδ, hQδE] at hQd
  have hQe := hline _ (contDiff_dE hQ)
  rw [dδ_dE hQ, hQδE, hQEE] at hQe
  have hF2 : ContDiffAt ℝ 2 (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) :=
    (c.contDiff_qfieldf ωq (hP.of_le (by norm_num)) (hQ.of_le (by norm_num)) _ _ _).contDiffAt
  have hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0 + t • y, V0) =
      c.qjacf ωq P Q (qxeqf P Q δ0 E0 V0 + t • y, V0) :=
    Filter.Eventually.of_forall fun t => c.matX_qfieldf ωq hP hQ _ _ _ _
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
  · exact hasDerivAt_const (0 : ℝ) (-c.D / (2 * c.H) : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-1 / (2 * c.H) : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact (hPd.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.ωc : ℝ)
  · exact (hPe.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-1 / c.τ : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.kq / c.τ : ℝ)
  · exact (hQd.const_mul ωq).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact (hQe.const_mul ωq).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (-ωq : ℝ)

@[tmio M, powerlib_domain] theorem smM1_qfieldf {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ}
    (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV) (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV) :
    smM1 (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) =
      !![0, 0, 0, 0, 0;
        0, 0, 0, 0, 0;
        c.ωc * c.PδV, 0, 0, c.ωc * c.PEV, 0;
        0, 0, 0, 0, 0;
        ωq * c.QδV, 0, 0, ωq * c.QEV, 0] := by
  have hline : ∀ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ 2 G →
      HasDerivAt (fun t : ℝ => G (portf (qxeqf P Q δ0 E0 V0, V0 + t))) (dV G ((δ0, E0), V0)) 0 :=
    fun G hG => by
      have h := hasDerivAt_port_line ((hG.differentiable (by norm_num)) ((δ0, E0), V0)) 0 0 1
      simp only [zero_mul, mul_zero, add_zero, mul_one, one_mul, zero_add] at h
      convert h using 1
      funext t; simp [portf, qxeqf]
  have hPd := hline _ (contDiff_dδ hP)
  rw [hPδV] at hPd
  have hPe := hline _ (contDiff_dE hP)
  rw [hPEV] at hPe
  have hQd := hline _ (contDiff_dδ hQ)
  rw [hQδV] at hQd
  have hQe := hline _ (contDiff_dE hQ)
  rw [hQEV] at hQe
  have hF2 : ContDiffAt ℝ 2 (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) :=
    (c.contDiff_qfieldf ωq (hP.of_le (by norm_num)) (hQ.of_le (by norm_num)) _ _ _).contDiffAt
  have hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0 + t) =
      c.qjacf ωq P Q (qxeqf P Q δ0 E0 V0, V0 + t) :=
    Filter.Eventually.of_forall fun t => c.matX_qfieldf ωq hP hQ _ _ _ _
  refine ParametricResonance.ForcedOrbit.smM1_of_line hF2 hJ fun i j => ?_
  have ev : ∀ {f g : ℝ → ℝ}, (∀ t, f t = g t) → f =ᶠ[𝓝 (0 : ℝ)] g :=
    fun h => Filter.Eventually.of_forall h
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (c.ω0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.D / (2 * c.H) : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-1 / (2 * c.H) : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact (hPd.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.ωc : ℝ)
  · exact (hPe.const_mul c.ωc).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-1 / c.τ : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (-c.kq / c.τ : ℝ)
  · exact (hQd.const_mul ωq).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · exact (hQe.const_mul ωq).congr_of_eventuallyEq (ev fun t => by simp [qjacf])
  · exact hasDerivAt_const (0 : ℝ) (-ωq : ℝ)

@[tmio M, powerlib_domain] theorem smA1_qfieldf {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 : ℝ}
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV) (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (Vh : ℝ) (z : Fin 5 → ℂ) :
    smA1 (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) Vh z = c.A1f ωq (z 0) (z 3) Vh := by
  have hdx := c.smDx_qfieldf ωq hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE
  have hm := c.smM1_qfieldf ωq hP hQ hPδV hPEV hQδV hQEV
  ext i j
  simp only [ParametricResonance.ForcedOrbit.smA1, ParametricResonance.ForcedOrbit.DxC, hdx, hm,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [A1f, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

@[tmio M, powerlib_domain] theorem zorbf_qfieldf {P Q : (ℝ × ℝ) × ℝ → ℝ} (hP : ContDiff ℝ 3 P)
    (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hτ : c.τ ≠ 0) (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ) (hQE : dE Q ((δ0, E0), V0) = c.QE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hl : c.lagf ωq (2 * Ω * I) ≠ 0) (hF2 : c.charFf ωq (2 * Ω * I) ≠ 0) (Vh : ℝ) :
    (((2 * Ω : ℝ) : ℂ) * I) • c.forcedf ωq (2 * Ω * I) Vh -
        (matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ c.forcedf ωq (2 * Ω * I) Vh =
      (Vh : ℂ) • fun i => ((fderiv ℝ (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ) := by
  have hf := c.forcedf_eq ωq (Vh : ℂ) hω0 hH hτ hl hF2
  have hb : (fun i => ((fderiv ℝ (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) (0, 1) i : ℝ) : ℂ)) = c.Bvf ωq :=
    c.fderivW_qfieldf ωq hP hQ hPV hQV
  rw [hb, c.matX_qfieldf ωq hP hQ, c.qjacf_eq ωq hPδ hPE hQδ hQE]
  push_cast
  exact hf

/-! ### End-to-end with explicit conditions -/

/-- The synchronizing core with a filtered dynamic Q–V loop at any operating point, grid-voltage
modulation, end-to-end, stability: at the Hopf point `c₁Ω² = l₁d₀ + l₀aω_c`,
`c₀Ω² = l₀d₀ − ω_q d₁`, with the cubic factor Routh–Hurwitz (`c₂ > 0`, `c₀ > 0`, `c₀τ < c₂c₁`),
`τ, ω_q > 0`, `Re λ₁ < 0` and `|g_V/2| < |λ₁|` give the forced periodic orbit with all Floquet
multipliers inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_hopf_stable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (h2 : 0 < c.c2f ωq) (h0 : 0 < c.c0f ωq Ω)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (Vh : ℝ) (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0) (hg : ‖c.gVf ωq Ω Vh / 2‖ ^ 2 < ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeqf P Q δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeqf P Q δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 5 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hm : matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) = c.A0f ωq := by
    rw [c.matX_qfieldf ωq hP hQ, c.qjacf_eq ωq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, hF2⟩ := c.hopff_facts ωq hτ hωq hΩ.ne' hR hA hB
  have hl := c.lagf_ne ωq hτ hωq hΩ.ne'
  have hl2 : c.lagf ωq (2 * Ω * I) ≠ 0 := by
    have := c.lagf_ne ωq (ω := 2 * Ω) hτ hωq (by positivity)
    push_cast at this; exact this
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR', hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 5) (m := 3) rfl hΩ.ne'
      (c.rightf_eig ωq hω0 hH hτ.ne' hl hF) (c.leftf_eig ωq hω0 hH hτ.ne' hl hF)
      (c.leftf_rightf ωq hω0 hH hl hFd) (c.hopff_simple ωq hω0 hH hτ hωq hΩ.ne' hFd)
      (fun μ v hv h h1 h2' => c.eigf_stable ωq hω0 hH hτ h2 h0 hR hA hB hv h h1 h2')
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorbf_qfieldf ωq hP hQ hω0 hH hτ.ne' hPδ hPE hQδ hQE hPV hQV hl2 hF2 Vh
  have hA1 := c.smA1_qfieldf ωq hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forcedf ωq (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable
    (c.contDiff_qfieldf ωq hP hQ _ _ _).contDiffAt (c.qfieldf_eq_zero ωq P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR']; exact hs
  · rw [hL, hR', hA1]; exact hg

/-- The filtered dynamic Q–V core with explicit conditions, parametric instability. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_hopf_unstable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (h2 : 0 < c.c2f ωq) (h0 : 0 < c.c0f ωq Ω)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (Vh : ℝ) (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hg : ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2 < ‖c.gVf ωq Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeqf P Q δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeqf P Q δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t
          (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hm : matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) = c.A0f ωq := by
    rw [c.matX_qfieldf ωq hP hQ, c.qjacf_eq ωq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, hF2⟩ := c.hopff_facts ωq hτ hωq hΩ.ne' hR hA hB
  have hl := c.lagf_ne ωq hτ hωq hΩ.ne'
  have hl2 : c.lagf ωq (2 * Ω * I) ≠ 0 := by
    have := c.lagf_ne ωq (ω := 2 * Ω) hτ hωq (by positivity)
    push_cast at this; exact this
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR', hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 5) (m := 3) rfl hΩ.ne'
      (c.rightf_eig ωq hω0 hH hτ.ne' hl hF) (c.leftf_eig ωq hω0 hH hτ.ne' hl hF)
      (c.leftf_rightf ωq hω0 hH hl hFd) (c.hopff_simple ωq hω0 hH hτ hωq hΩ.ne' hFd)
      (fun μ v hv h h1 h2' => c.eigf_stable ωq hω0 hH hτ h2 h0 hR hA hB hv h h1 h2')
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorbf_qfieldf ωq hP hQ hω0 hH hτ.ne' hPδ hPE hQδ hQE hPV hQV hl2 hF2 Vh
  have hA1 := c.smA1_qfieldf ωq hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forcedf ωq (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable
    (c.contDiff_qfieldf ωq hP hQ _ _ _).contDiffAt (c.qfieldf_eq_zero ωq P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_
  rw [hL, hR', hA1]; exact hg

/-- The filtered dynamic Q–V core with explicit conditions: the forced orbit exists and is
locally exponentially stable for the nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_qvf_hopf_exp_stable {P Q : (ℝ × ℝ) × ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (hQ : ContDiff ℝ 3 Q) {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : 0 < c.τ) (hωq : 0 < ωq)
    (hPδ : dδ P ((δ0, E0), V0) = c.Pδ) (hPE : dE P ((δ0, E0), V0) = c.PE)
    (hPV : dV P ((δ0, E0), V0) = c.PV) (hQδ : dδ Q ((δ0, E0), V0) = c.Qδ)
    (hQE : dE Q ((δ0, E0), V0) = c.QE) (hQV : dV Q ((δ0, E0), V0) = c.QV)
    (hPδδ : dδ (dδ P) ((δ0, E0), V0) = c.Pδδ) (hPδE : dE (dδ P) ((δ0, E0), V0) = c.PδE)
    (hPEE : dE (dE P) ((δ0, E0), V0) = c.PEE) (hPδV : dV (dδ P) ((δ0, E0), V0) = c.PδV)
    (hPEV : dV (dE P) ((δ0, E0), V0) = c.PEV) (hQδδ : dδ (dδ Q) ((δ0, E0), V0) = c.Qδδ)
    (hQδE : dE (dδ Q) ((δ0, E0), V0) = c.QδE) (hQEE : dE (dE Q) ((δ0, E0), V0) = c.QEE)
    (hQδV : dV (dδ Q) ((δ0, E0), V0) = c.QδV) (hQEV : dV (dE Q) ((δ0, E0), V0) = c.QEV)
    (h2 : 0 < c.c2f ωq) (h0 : 0 < c.c0f ωq Ω)
    (hR : c.c0f ωq Ω * c.τ < c.c2f ωq * c.c1f ωq Ω)
    (hA : c.c1f ωq Ω * Ω ^ 2 = (c.τ * ωq + 1) * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) +
      ωq * c.b * (c.D / (2 * c.H) * c.ωc))
    (hB : c.c0f ωq Ω * Ω ^ 2 = ωq * c.b * (c.ω0 * c.ωc * c.Pδ / (2 * c.H)) -
      ωq * (c.ω0 * c.ωc * c.kq * c.PE * c.Qδ / (2 * c.H)))
    (Vh : ℝ) (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : (c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))).re < 0) (hg : ‖c.gVf ωq Ω Vh / 2‖ ^ 2 < ‖c.leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ c.rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeqf P Q δ0 E0 V0 + y t,
        V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 5 → ℝ),
        IsIntegralCurveOn x (fun t v => c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0)) (qxeqf P Q δ0 E0 V0 + v,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hm : matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) = c.A0f ωq := by
    rw [c.matX_qfieldf ωq hP hQ, c.qjacf_eq ωq hPδ hPE hQδ hQE]
  obtain ⟨hF, hFd, hF2⟩ := c.hopff_facts ωq hτ hωq hΩ.ne' hR hA hB
  have hl := c.lagf_ne ωq hτ hωq hΩ.ne'
  have hl2 : c.lagf ωq (2 * Ω * I) ≠ 0 := by
    have := c.lagf_ne ωq (ω := 2 * Ω) hτ hωq (by positivity)
    push_cast at this; exact this
  obtain ⟨Pm, Qm, As, hPQ, hQP, hA0, hL, hR', hsrs⟩ :=
    ParametricResonance.ForcedOrbit.stable_modal_of_hurwitz (n := 5) (m := 3) rfl hΩ.ne'
      (c.rightf_eig ωq hω0 hH hτ.ne' hl hF) (c.leftf_eig ωq hω0 hH hτ.ne' hl hF)
      (c.leftf_rightf ωq hω0 hH hl hFd) (c.hopff_simple ωq hω0 hH hτ hωq hΩ.ne' hFd)
      (fun μ v hv h h1 h2' => c.eigf_stable ωq hω0 hH hτ h2 h0 hR hA hB hv h h1 h2')
      (T := 2 * Real.pi / (2 * Ω)) (by positivity)
  have hA0' : Qm * matX (c.qfieldf ωq P Q (P ((δ0, E0), V0)) E0 (Q ((δ0, E0), V0))) (qxeqf P Q δ0 E0 V0, V0) * Pm =
      Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As := by
    rw [hm, hA0, mul_div_cancel_left₀ Ω two_ne_zero]
  have hz := c.zorbf_qfieldf ωq hP hQ hω0 hH hτ.ne' hPδ hPE hQδ hQE hPV hQV hl2 hF2 Vh
  have hA1 := c.smA1_qfieldf ωq hP hQ hPδδ hPδE hPEE hQδδ hQδE hQEE hPδV hPEV hQδV hQEV Vh
    (c.forcedf ωq (2 * Ω * I) Vh)
  refine ParametricResonance.ForcedOrbit.smooth_orbit_exp_stable
    (c.contDiff_qfieldf ωq hP hQ _ _ _).contDiffAt (c.qfieldf_eq_zero ωq P Q δ0 E0 V0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0' hsrs hz A0' ?_ ?_
  · rw [hL, hR']; exact hs
  · rw [hL, hR', hA1]; exact hg

/-! ### Connection with the unfiltered loop -/

omit ωq in
/-- A fast measurement filter (`ω_q → ∞`) recovers the unfiltered loop:
`K_f(s) → K_eff(s) = P_δ − k_q P_E Q_δ/(τs + b)`. -/
@[tmio M, powerlib_domain] theorem Kf_tendsto {s : ℂ} (hl : c.lag s ≠ 0) :
    Tendsto (fun ωq : ℝ => c.Kf ωq s) atTop (𝓝 (c.Keff s)) := by
  have h1 : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa [Function.comp_def] using h
  have hg : Tendsto (fun x : ℝ => (s * ((x : ℂ))⁻¹ + 1) * (c.τ * s + 1) + c.kq * c.QE) atTop
      (𝓝 (c.lag s)) := by
    have := (((h1.const_mul s).add_const 1).mul_const (c.τ * s + 1)).add_const
      ((c.kq : ℂ) * c.QE)
    convert this using 2
    simp [lag, b]; ring
  have hK := (tendsto_const_nhds (x := (c.Pδ : ℂ))).sub
    ((tendsto_const_nhds (x := (c.kq * c.PE * c.Qδ : ℂ))).div hg hl)
  refine (hK.congr' ?_).trans (by simp [Keff])
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [Kf, lagf]
  congr 1
  show (c.kq * c.PE * c.Qδ : ℂ) / ((s * (x : ℂ)⁻¹ + 1) * (c.τ * s + 1) + c.kq * c.QE) = _
  rw [show (s * (x : ℂ)⁻¹ + 1) * (c.τ * s + 1) + c.kq * c.QE =
    ((s + x) * (c.τ * s + 1) + c.kq * x * c.QE) / x by field_simp, div_div_eq_mul_div]
  ring

/-- The EMF behind `R + jX` with a filtered dynamic Q–V loop at any operating point, end-to-end, stability, with explicit conditions. -/
@[tmio M, powerlib_domain] theorem orbit_lossyf_hopf_stable {ω0 H D ωc τ kq ωq R X δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : 0 < τ) (hωq : 0 < ωq)
    (h2 : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c2f ωq) (h0 : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c0f ωq Ω)
    (hR : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c0f ωq Ω * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).τ < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c2f ωq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c1f ωq Ω)
    (hA : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c1f ωq Ω * Ω ^ 2 = ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).τ * ωq + 1) *
        ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) +
      ωq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).D / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H) * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc))
    (hB : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c0f ωq Ω * Ω ^ 2 = ωq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b *
        ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) -
      ωq * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).kq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).PE * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Qδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)))
    (Vh : ℝ) (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hs : ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).rightf ωq (Ω * I))).re < 0) (hg : ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).gVf ωq Ω Vh / 2‖ ^ 2 < ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).rightf ωq (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfieldf ωq (lossyP R X) (lossyQ R X) (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (qxeqf (lossyP R X) (lossyQ R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfieldf ωq (lossyP R X) (lossyQ R X) (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (qxeqf (lossyP R X) (lossyQ R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 5 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfieldf ωq (lossyP R X) (lossyQ R X) (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0))) (qxeqf (lossyP R X) (lossyQ R X) δ0 E0 V0, V0)
            Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v =
            μ • v → ‖μ‖ < 1 :=
  (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).orbit_qvf_hopf_stable ωq (contDiff_lossyP R X) (contDiff_lossyQ R X) hΩ hω0 hH hτ hωq
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h2 h0 hR hA hB Vh A0' hs hg

/-- The EMF behind `R + jX` with a filtered dynamic Q–V loop at any operating point, end-to-end, parametric instability, with explicit conditions. -/
@[tmio M, powerlib_domain] theorem orbit_lossyf_hopf_unstable {ω0 H D ωc τ kq ωq R X δ0 E0 V0 Ω : ℝ}
    (hΩ : 0 < Ω) (hω0 : ω0 ≠ 0) (hH : H ≠ 0) (hτ : 0 < τ) (hωq : 0 < ωq)
    (h2 : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c2f ωq) (h0 : 0 < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c0f ωq Ω)
    (hR : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c0f ωq Ω * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).τ < (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c2f ωq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c1f ωq Ω)
    (hA : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c1f ωq Ω * Ω ^ 2 = ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).τ * ωq + 1) *
        ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) +
      ωq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).D / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H) * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc))
    (hB : (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).c0f ωq Ω * Ω ^ 2 = ωq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).b *
        ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Pδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)) -
      ωq * ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ω0 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).ωc * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).kq * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).PE * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).Qδ / (2 * (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).H)))
    (Vh : ℝ) (A0' : Matrix (Fin 5) (Fin 5) ℝ)
    (hg : ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).leftf ωq (Ω * I) ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).rightf ωq (Ω * I))‖ ^ 2 < ‖(lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).gVf ωq Ω Vh / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 5 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfieldf ωq (lossyP R X) (lossyQ R X) (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (qxeqf (lossyP R X) (lossyQ R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 5 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfieldf ωq (lossyP R X) (lossyQ R X) (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)) (qxeqf (lossyP R X) (lossyQ R X) δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ ((lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).qfieldf ωq (lossyP R X) (lossyQ R X) (lossyP R X ((δ0, E0), V0)) E0 (lossyQ R X ((δ0, E0), V0)))
          (qxeqf (lossyP R X) (lossyQ R X) δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) :=
  (lossyCore ω0 H D ωc τ kq R X δ0 E0 V0).orbit_qvf_hopf_unstable ωq (contDiff_lossyP R X) (contDiff_lossyQ R X) hΩ hω0 hH hτ hωq
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h2 h0 hR hA hB Vh A0' hg

end DynQV
end VoltageModulation
end powerlib.GFM
