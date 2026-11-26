import theorem.GridTiedConverter.GFM.HopfLineLPF

/-! # The first Lyapunov coefficient of the VSM with a power filter on the zero-current slice

Model boundary.
* The five-state VSM + power filter `Line.VSMLPF` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, ω, P_f, i_d, i_q)`, grid dq
  frame at `ω₀`, export-positive power, constant `E`, `M ω̇ = P_ref − P_f − D ω`,
  `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no voltage loop, inner loops, PLL,
  delay or PWM. Read about a selected angle (`Line.VSMLPF.Model`), translated so that the
  operating point is the origin.
* The zero-current slice (`Line.VSMLPF.Model.OnSlice`): `δ* = 0` and `V = E`, so the operating
  current vanishes (balance forces `P_ref = 0`, and `Q = 0`). Every physical model on the slice;
  at a Hopf point (`Line.VSMLPF.Model.HopfAt`), the quintic has `±iω` and a Hurwitz cubic
  cofactor.
* Level: Lyapunov instability and local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) of the operating point, through `Line.VSMLPF.family`. Off the slice
  the all-parameter closed form is `theorem/GridTiedConverter/GFM/HopfLineLPFAngle.lean`.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4 (the
projection formula `NormalForm.LyapunovCoefficient.firstLyapunov_eq_of_solve`); the Hopf laws of
`theorem/GridTiedConverter/GFM/HopfLineLPF.lean` and `theorem/Dynamics/HopfDichotomy.lean`; the
quintic Routh–Hurwitz criterion of `theorem/Criteria/Routh5.lean` (Orlando's boundary `Δ₄ = 0`).
The closed form was derived with exact computer algebra (SymPy, untrusted): in the coordinates
`(δ, ω, P_f/M, (L/E) i_d, (L/E) i_q)` the slice depends on `d = D/M`, `c = ω_c`, `g = E²/(M L)`,
`σ = R/L`, `w = ω₀`; the two Hopf relations are linear in `c` (`c Q_c = P_c`,
`Q_c = d (σ² + w² − ω²) − 2σω²`) and in `g`, so `c` and `g` are eliminated with powers of `Q_c`
(`(ω² + c²) Q_c = c g w > 0`). Every identity is proved here by `linear_combination` with its
certificate, split under the heartbeat limit: the eigenvector, resolvent and reduction lemmas
(`sl_right` … `sl_Y3`), and the key identity along the powers of `d` (`sl_key0` … `sl_key8`).
Sanity check (untrusted, outside the proof): the closed form reproduces the exact witnesses of
`HopfLineLPF.lean`, `ℓ₁ = −14341/14450` and `ℓ₁ = 795686360348046533/264278927960175000`.

Results.
* `Line.VSMLPF.sliceBautin`, `Line.VSMLPF.sliceBautinCoeff`: the Bautin form of the slice,
  `𝔅(d, σ, w, ω) = Σ_k d^k 𝔅_k(σ, w, ω)`, a polynomial of degree 23 with 336 terms, even in `w`;
  `Line.VSMLPF.slicePairRe`, `slicePairIm`, `sliceShiftRe`, `sliceShiftIm`: `Q_c ⟨p̃, q⟩` and
  `Q_c χ(2iω)` with `c`, `g` eliminated (`χ(s) = s (s + d)(s + c)((s + σ)² + w²) + c g w`).
* The slice pattern: `Line.VSMLPF.sliceVecQ`, `Line.VSMLPF.sliceVecP`,
  `Line.VSMLPF.slicePairing`, `Line.VSMLPF.sliceScale`; the critical pair of a slice model
  `Line.VSMLPF.Model.sliceQ`, `Line.VSMLPF.Model.sliceP`
  (`Line.VSMLPF.Model.isCriticalPair_slice`).
* **`Line.VSMLPF.Model.firstLyapunov_slice`** (closed form): at a Hopf point `ω` of a physical
  slice model,
  `ℓ₁ = −9 ω⁷ (ω² + d²) ((σ² + w² − ω²)² + 4σ²ω²) 𝔅 / ((Re² Ĉ + Im² Ĉ)(Re² χ̂ + Im² χ̂))`.
* **`Line.VSMLPF.Model.sign_firstLyapunov_slice`** (sign law): for every critical pair,
  `sign ℓ₁ = −sign 𝔅(D/M, R/L, ω₀, ω)`.
* `Line.VSMLPF.Model.sliceOmega`: the Hopf frequency read from the coefficients,
  `ω = √(a₀ Δ₂/Δ₃)` (`Line.VSMLPF.Model.hopfAt_sliceOmega`: a boundary point `Δ₄ = 0`,
  `Δ₂, Δ₃ > 0` of the quintic Routh region is a Hopf point at this `ω`);
  `Line.VSMLPF.Model.SliceDegenerate`: the degenerate balanced slice models (`Δ₃ = 0` of the
  quintic, or `Δ₄ = 0`, `Δ₂, Δ₃ > 0` and `𝔅` vanishing at `sliceOmega`).
* The `ω` row of the critical pair (the only row the damping derivative of the Jacobian reads):
  `Line.VSMLPF.sliceTransversality` `𝔗(d, σ, w, ω)` (degree 6, 17 terms,
  `d Re Ĉ − ω Im Ĉ = 2 ω² w 𝔗`); `Line.VSMLPF.Model.re_sliceP_one_mul_sliceQ_one`:
  `Re(conj p₁ q₁) = 2 w² ω⁴ ((σ² + w² − ω²)² + 4σ²ω²) 𝔗 / (Re² Ĉ + Im² Ĉ)`;
  `Line.VSMLPF.Model.sign_re_sliceP_one_mul_sliceQ_one`: its sign is `sign 𝔗`.
* The `δ` row (read by the inverse-inertia derivative of the Jacobian):
  `Line.VSMLPF.sliceInertia` `𝔍(d, σ, w, ω)` (13 terms, `ω Re Ĉ + d Im Ĉ = ω w 𝔍`);
  `Line.VSMLPF.Model.re_sliceP_one_mul_sliceQ_zero`:
  `Re(conj p₁ q₀) = −w² ω² ((σ² + w² − ω²)² + 4σ²ω²) 𝔍 / (Re² Ĉ + Im² Ĉ)`;
  `Line.VSMLPF.Model.sign_re_sliceP_one_mul_sliceQ_zero`: its sign is `−sign 𝔍`.
* The two forms never vanish together: `Line.VSMLPF.sliceTransversality_sq_add_sliceInertia_sq`
  (`ω² w² (4ω² 𝔗² + 𝔍²) = (d² + ω²)(Re² Ĉ + Im² Ĉ)`, an identity for all values) and
  `Line.VSMLPF.Model.sliceInertia_ne_zero_of_sliceTransversality_eq_zero` (`𝔗 = 0 ⇒ 𝔍 ≠ 0` at a
  slice Hopf point, `Re Ĉ > 0`). The transversality coefficients along the damping and the
  inverse inertia and the Hopf cycles are in
  `theorem/GridTiedConverter/GFM/LineVSMLPFHopfCycle.lean`.
* Off the slice: the first Lyapunov coefficient at every angle and load, in closed form, with its
  sign law (`Line.VSMLPF.Model.firstLyapunov_crit`, `Line.VSMLPF.Model.sign_firstLyapunov_crit`),
  is `theorem/GridTiedConverter/GFM/HopfLineLPFAngle.lean` (rotated and scaled current frame, in
  which both Hopf relations are linear).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSMLPF.family`.
* **`Line.VSMLPF.mem_den_locallyAsymptoticallyStable_of_sliceBautin_pos`** (supercritical) and
  **`Line.VSMLPF.mem_den_unstable_of_sliceBautin_neg`** (subcritical) at a Hopf point of a
  balanced physical slice model.
* **`Line.VSMLPF.mem_den_locallyAsymptoticallyStable_iff_slice`** (complete membership on the
  slice, off `Line.VSMLPF.Model.SliceDegenerate`): locally asymptotically stable iff balanced and
  either the strict quintic Routh conditions or a Hopf point with `𝔅 > 0`. The excluded cases are
  unstable: not balanced, a strict Routh violation (`Line.VSMLPF.mem_den_unstable`), a Hopf point
  with `𝔅 < 0`; on the slice `a₀ = c g w > 0`, so there is no fold, and `Δ₂ = 0` forces `Δ₃ = 0`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSMLPF
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

/-! ## The slice pattern

Polynomial vectors in complex atoms `d, c, g, σ, w`, the frequency `O` and a square root `j` of
`−1`, under the slice Hopf relations
`h1 : c Q_c = P_c` and `h2 : c g w = O² ((d + c)(σ² + w² − O²) + 2σ(dc − O²))`. -/

/-- The Jacobian pattern of the zero-current slice in the scaled coordinates
`(δ, ω, P_f/M, (L/E) i_d, (L/E) i_q)`. -/
private def slJ (d c g σ w : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 1, 0, 0, 0; 0, -d, -1, 0, 0; 0, 0, -c, c * g, 0; 0, 0, 0, -σ, w; 1, 0, 0, -w, -σ]

/-- The second-derivative pattern of the slice. -/
private def slBil (c g : ℂ) (u v : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![0, 0, c * g * (u 0 * v 4 + u 4 * v 0), -(u 0 * v 0), 0]

/-- The third-derivative pattern of the slice. -/
private def slTri (c g : ℂ) (u v z : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![0, 0, -(c * g * (u 0 * v 0 * z 3 + u 0 * v 3 * z 0 + u 3 * v 0 * z 0)), 0, -(u 0 * v 0 * z 0)]


/-- **The critical right eigenvector of the slice pattern** at the frequency `O` (`j² = −1`,
`d = D/M`, `σ = R/L`, `w = ω₀`): `q = (L_q, jO L_q, −(d + jO) jO L_q, w, σ + jO)`,
`L_q = (σ + jO)² + w²`, with the powers of `j` reduced. -/
def sliceVecQ (d σ w O j : ℂ) : Fin 5 → ℂ :=
  ![σ ^ (2:ℕ) + 2 * σ * O * j + w ^ (2:ℕ) - O ^ (2:ℕ), σ ^ (2:ℕ) * O * j - 2 * σ * O ^ (2:ℕ) +
    w ^ (2:ℕ) * O * j - O ^ (3:ℕ) * j, -d * σ ^ (2:ℕ) * O * j + 2 * d * σ * O ^ (2:ℕ) -
    d * w ^ (2:ℕ) * O * j + d * O ^ (3:ℕ) * j + σ ^ (2:ℕ) * O ^ (2:ℕ) + 2 * σ * O ^ (3:ℕ) * j +
    w ^ (2:ℕ) * O ^ (2:ℕ) - O ^ (4:ℕ), w, σ + O * j]

/-- **The unnormalised critical left eigenvector of the slice pattern** (`μ = −jO`, `c = ω_c`):
`p̃ = (−w(μ + d)(μ + c), −w(μ + c), w, −(μ + σ) μ (μ + d)(μ + c), −w μ (μ + d)(μ + c))`. -/
def sliceVecP (d c σ w O j : ℂ) : Fin 5 → ℂ :=
  ![-d * c * w + d * w * O * j + c * w * O * j + w * O ^ (2:ℕ), -c * w + w * O * j, w,
    d * c * σ * O * j + d * c * O ^ (2:ℕ) + d * σ * O ^ (2:ℕ) - d * O ^ (3:ℕ) * j +
    c * σ * O ^ (2:ℕ) - c * O ^ (3:ℕ) * j - σ * O ^ (3:ℕ) * j - O ^ (4:ℕ), d * c * w * O * j +
    d * w * O ^ (2:ℕ) + c * w * O ^ (2:ℕ) - w * O ^ (3:ℕ) * j]

/-- `w` times the solution of `J r = B(q, q̄)`. -/
private def slR (σ w O : ℂ) : Fin 5 → ℂ :=
  ![σ ^ (5:ℕ) + 2 * σ ^ (3:ℕ) * w ^ (2:ℕ) + σ * w ^ (4:ℕ) + 4 * σ * w ^ (2:ℕ) * O ^ (2:ℕ) -
    σ * O ^ (4:ℕ), 0, 0, 2 * σ ^ (3:ℕ) * w + 2 * σ * w ^ (3:ℕ) + 2 * σ * w * O ^ (2:ℕ), σ ^ (4:ℕ) -
    w ^ (4:ℕ) + 2 * w ^ (2:ℕ) * O ^ (2:ℕ) - O ^ (4:ℕ)]

/-- `χ = det(2iω − J)` of the slice. -/
private def slChi (d c g σ w O j : ℂ) : ℂ :=
  2 * d * c * σ ^ (2:ℕ) * O * j - 8 * d * c * σ * O ^ (2:ℕ) + 2 * d * c * w ^ (2:ℕ) * O * j -
    8 * d * c * O ^ (3:ℕ) * j - 4 * d * σ ^ (2:ℕ) * O ^ (2:ℕ) - 16 * d * σ * O ^ (3:ℕ) * j -
    4 * d * w ^ (2:ℕ) * O ^ (2:ℕ) + 16 * d * O ^ (4:ℕ) + c * g * w - 4 * c * σ ^ (2:ℕ) * O ^ (2:ℕ) -
    16 * c * σ * O ^ (3:ℕ) * j - 4 * c * w ^ (2:ℕ) * O ^ (2:ℕ) + 16 * c * O ^ (4:ℕ) -
    8 * σ ^ (2:ℕ) * O ^ (3:ℕ) * j + 32 * σ * O ^ (4:ℕ) - 8 * w ^ (2:ℕ) * O ^ (3:ℕ) * j +
    32 * O ^ (5:ℕ) * j

/-- `w χ` times the solution of `(2iω − J) s = B(q, q)`. -/
private def slS (d c g σ w O j : ℂ) : Fin 5 → ℂ :=
  ![-c * g * σ ^ (5:ℕ) * w - 8 * c * g * σ ^ (4:ℕ) * w * O * j - 2 * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) +
    24 * c * g * σ ^ (3:ℕ) * w * O ^ (2:ℕ) - 8 * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O * j +
    34 * c * g * σ ^ (2:ℕ) * w * O ^ (3:ℕ) * j - c * g * σ * w ^ (5:ℕ) +
    12 * c * g * σ * w ^ (3:ℕ) * O ^ (2:ℕ) - 23 * c * g * σ * w * O ^ (4:ℕ) +
    6 * c * g * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 6 * c * g * w * O ^ (5:ℕ) * j,
    -2 * c * g * σ ^ (5:ℕ) * w * O * j + 16 * c * g * σ ^ (4:ℕ) * w * O ^ (2:ℕ) -
    4 * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O * j + 48 * c * g * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j +
    16 * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - 68 * c * g * σ ^ (2:ℕ) * w * O ^ (4:ℕ) -
    2 * c * g * σ * w ^ (5:ℕ) * O * j + 24 * c * g * σ * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    46 * c * g * σ * w * O ^ (5:ℕ) * j - 12 * c * g * w ^ (3:ℕ) * O ^ (4:ℕ) +
    12 * c * g * w * O ^ (6:ℕ), 2 * d * c * g * σ ^ (5:ℕ) * w * O * j -
    16 * d * c * g * σ ^ (4:ℕ) * w * O ^ (2:ℕ) + 4 * d * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O * j -
    48 * d * c * g * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j -
    16 * d * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) + 68 * d * c * g * σ ^ (2:ℕ) * w * O ^ (4:ℕ)
    + 2 * d * c * g * σ * w ^ (5:ℕ) * O * j - 24 * d * c * g * σ * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    46 * d * c * g * σ * w * O ^ (5:ℕ) * j + 12 * d * c * g * w ^ (3:ℕ) * O ^ (4:ℕ) -
    12 * d * c * g * w * O ^ (6:ℕ) - 4 * c * g * σ ^ (5:ℕ) * w * O ^ (2:ℕ) -
    32 * c * g * σ ^ (4:ℕ) * w * O ^ (3:ℕ) * j - 8 * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    96 * c * g * σ ^ (3:ℕ) * w * O ^ (4:ℕ) - 32 * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    136 * c * g * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j - 4 * c * g * σ * w ^ (5:ℕ) * O ^ (2:ℕ) +
    48 * c * g * σ * w ^ (3:ℕ) * O ^ (4:ℕ) - 92 * c * g * σ * w * O ^ (6:ℕ) +
    24 * c * g * w ^ (3:ℕ) * O ^ (5:ℕ) * j - 24 * c * g * w * O ^ (7:ℕ) * j,
    -2 * d * c * σ ^ (5:ℕ) * w * O * j + 12 * d * c * σ ^ (4:ℕ) * w * O ^ (2:ℕ) -
    4 * d * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O * j + 28 * d * c * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j +
    16 * d * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - 32 * d * c * σ ^ (2:ℕ) * w * O ^ (4:ℕ) -
    2 * d * c * σ * w ^ (5:ℕ) * O * j + 20 * d * c * σ * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    18 * d * c * σ * w * O ^ (5:ℕ) * j + 4 * d * c * w ^ (5:ℕ) * O ^ (2:ℕ) -
    8 * d * c * w ^ (3:ℕ) * O ^ (4:ℕ) + 4 * d * c * w * O ^ (6:ℕ) +
    4 * d * σ ^ (5:ℕ) * w * O ^ (2:ℕ) + 24 * d * σ ^ (4:ℕ) * w * O ^ (3:ℕ) * j +
    8 * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - 56 * d * σ ^ (3:ℕ) * w * O ^ (4:ℕ) +
    32 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 64 * d * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j +
    4 * d * σ * w ^ (5:ℕ) * O ^ (2:ℕ) - 40 * d * σ * w ^ (3:ℕ) * O ^ (4:ℕ) +
    36 * d * σ * w * O ^ (6:ℕ) + 8 * d * w ^ (5:ℕ) * O ^ (3:ℕ) * j -
    16 * d * w ^ (3:ℕ) * O ^ (5:ℕ) * j + 8 * d * w * O ^ (7:ℕ) * j -
    2 * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) - 6 * c * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O * j -
    2 * c * g * σ * w ^ (4:ℕ) + 6 * c * g * σ * w ^ (2:ℕ) * O ^ (2:ℕ) -
    2 * c * g * w ^ (4:ℕ) * O * j + 2 * c * g * w ^ (2:ℕ) * O ^ (3:ℕ) * j +
    4 * c * σ ^ (5:ℕ) * w * O ^ (2:ℕ) + 24 * c * σ ^ (4:ℕ) * w * O ^ (3:ℕ) * j +
    8 * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - 56 * c * σ ^ (3:ℕ) * w * O ^ (4:ℕ) +
    32 * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 64 * c * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j +
    4 * c * σ * w ^ (5:ℕ) * O ^ (2:ℕ) - 40 * c * σ * w ^ (3:ℕ) * O ^ (4:ℕ) +
    36 * c * σ * w * O ^ (6:ℕ) + 8 * c * w ^ (5:ℕ) * O ^ (3:ℕ) * j -
    16 * c * w ^ (3:ℕ) * O ^ (5:ℕ) * j + 8 * c * w * O ^ (7:ℕ) * j +
    8 * σ ^ (5:ℕ) * w * O ^ (3:ℕ) * j - 48 * σ ^ (4:ℕ) * w * O ^ (4:ℕ) +
    16 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 112 * σ ^ (3:ℕ) * w * O ^ (5:ℕ) * j -
    64 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) + 128 * σ ^ (2:ℕ) * w * O ^ (6:ℕ) +
    8 * σ * w ^ (5:ℕ) * O ^ (3:ℕ) * j - 80 * σ * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    72 * σ * w * O ^ (7:ℕ) * j - 16 * w ^ (5:ℕ) * O ^ (4:ℕ) + 32 * w ^ (3:ℕ) * O ^ (6:ℕ) -
    16 * w * O ^ (8:ℕ), 2 * d * c * σ ^ (4:ℕ) * w ^ (2:ℕ) * O * j -
    8 * d * c * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) + 4 * d * c * σ ^ (2:ℕ) * w ^ (4:ℕ) * O * j -
    12 * d * c * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j - 8 * d * c * σ * w ^ (4:ℕ) * O ^ (2:ℕ) +
    8 * d * c * σ * w ^ (2:ℕ) * O ^ (4:ℕ) + 2 * d * c * w ^ (6:ℕ) * O * j -
    4 * d * c * w ^ (4:ℕ) * O ^ (3:ℕ) * j + 2 * d * c * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    4 * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) - 16 * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    8 * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) + 24 * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    16 * d * σ * w ^ (4:ℕ) * O ^ (3:ℕ) * j + 16 * d * σ * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    4 * d * w ^ (6:ℕ) * O ^ (2:ℕ) + 8 * d * w ^ (4:ℕ) * O ^ (4:ℕ) - 4 * d * w ^ (2:ℕ) * O ^ (6:ℕ) -
    c * g * σ ^ (4:ℕ) * w - 6 * c * g * σ ^ (3:ℕ) * w * O * j +
    12 * c * g * σ ^ (2:ℕ) * w * O ^ (2:ℕ) - 2 * c * g * σ * w ^ (3:ℕ) * O * j +
    10 * c * g * σ * w * O ^ (3:ℕ) * j + c * g * w ^ (5:ℕ) + 2 * c * g * w ^ (3:ℕ) * O ^ (2:ℕ) -
    3 * c * g * w * O ^ (4:ℕ) - 4 * c * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    16 * c * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j - 8 * c * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    24 * c * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) - 16 * c * σ * w ^ (4:ℕ) * O ^ (3:ℕ) * j +
    16 * c * σ * w ^ (2:ℕ) * O ^ (5:ℕ) * j - 4 * c * w ^ (6:ℕ) * O ^ (2:ℕ) +
    8 * c * w ^ (4:ℕ) * O ^ (4:ℕ) - 4 * c * w ^ (2:ℕ) * O ^ (6:ℕ) -
    8 * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j + 32 * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    16 * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j + 48 * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    32 * σ * w ^ (4:ℕ) * O ^ (4:ℕ) - 32 * σ * w ^ (2:ℕ) * O ^ (6:ℕ) - 8 * w ^ (6:ℕ) * O ^ (3:ℕ) * j
    + 16 * w ^ (4:ℕ) * O ^ (5:ℕ) * j - 8 * w ^ (2:ℕ) * O ^ (7:ℕ) * j]

/-- **The pairing `⟨p̃, q⟩`** of the slice pattern (`p̃` conjugated: `O ↦ −O`). -/
def slicePairing (d c σ w O j : ℂ) : ℂ :=
  -d * c * σ ^ (2:ℕ) * w - 4 * d * c * σ * w * O * j - d * c * w ^ (3:ℕ) + 3 * d * c * w * O ^ (2:ℕ)
    - 2 * d * σ ^ (2:ℕ) * w * O * j + 6 * d * σ * w * O ^ (2:ℕ) - 2 * d * w ^ (3:ℕ) * O * j +
    4 * d * w * O ^ (3:ℕ) * j - 2 * c * σ ^ (2:ℕ) * w * O * j + 6 * c * σ * w * O ^ (2:ℕ) -
    2 * c * w ^ (3:ℕ) * O * j + 4 * c * w * O ^ (3:ℕ) * j + 3 * σ ^ (2:ℕ) * w * O ^ (2:ℕ) +
    8 * σ * w * O ^ (3:ℕ) * j + 3 * w ^ (3:ℕ) * O ^ (2:ℕ) - 5 * w * O ^ (4:ℕ)

@[tmio M, powerlib_domain] private theorem sl_right {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d))
    (h2 : c * g * w = O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    slJ d c g σ w *ᵥ sliceVecQ d σ w O j = (O * j) • sliceVecQ d σ w O j := by
  ext k
  fin_cases k <;> simp only [slJ, sliceVecQ, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linear_combination (-2 * σ * O ^ (2:ℕ)) * hj
  · linear_combination (-σ ^ (2:ℕ) * O ^ (2:ℕ) - w ^ (2:ℕ) * O ^ (2:ℕ) + O ^ (4:ℕ)) * hj
  · linear_combination (O * j) * h1 + (1) * h2 + (d * σ ^ (2:ℕ) * O ^ (2:ℕ) +
      d * w ^ (2:ℕ) * O ^ (2:ℕ) - d * O ^ (4:ℕ) - 2 * σ * O ^ (4:ℕ)) * hj
  · ring
  · linear_combination (-O ^ (2:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem sl_left {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d))
    (h2 : c * g * w = O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    (slJ d c g σ w)ᵀ *ᵥ sliceVecP d c σ w O j = (-(O * j)) • sliceVecP d c σ w O j := by
  ext k
  fin_cases k <;> simp only [slJ, sliceVecP, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linear_combination (d * w * O ^ (2:ℕ) + c * w * O ^ (2:ℕ)) * hj
  · linear_combination (w * O ^ (2:ℕ)) * hj
  · ring
  · linear_combination (-O * j) * h1 + (1) * h2 + (d * c * σ * O ^ (2:ℕ) - d * O ^ (4:ℕ) -
      c * O ^ (4:ℕ) - σ * O ^ (4:ℕ)) * hj
  · linear_combination (d * c * w * O ^ (2:ℕ) - w * O ^ (4:ℕ)) * hj

@[tmio M, powerlib_domain] private theorem sl_r {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1) :
    slJ d c g σ w *ᵥ slR σ w O = w • slBil c g (sliceVecQ d σ w O j) (sliceVecQ d σ w (-O) j) := by
  ext k
  fin_cases k <;> simp only [slJ, slR, slBil, sliceVecQ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · ring
  · ring
  · linear_combination (4 * c * g * σ * w * O ^ (2:ℕ)) * hj
  · linear_combination (-4 * σ ^ (2:ℕ) * w * O ^ (2:ℕ)) * hj
  · ring

@[tmio M, powerlib_domain] private theorem sl_S {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1) :
    ((2 * O * j) • (1 : Matrix (Fin 5) (Fin 5) ℂ) - slJ d c g σ w) *ᵥ slS d c g σ w O j =
      (w * slChi d c g σ w O j) • slBil c g (sliceVecQ d σ w O j) (sliceVecQ d σ w O j) := by
  ext k
  fin_cases k <;> simp only [slJ, slS, slChi, slBil, sliceVecQ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
  · linear_combination (-16 * c * g * σ ^ (4:ℕ) * w * O ^ (2:ℕ) -
      16 * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) + 68 * c * g * σ ^ (2:ℕ) * w * O ^ (4:ℕ) +
      12 * c * g * w ^ (3:ℕ) * O ^ (4:ℕ) - 12 * c * g * w * O ^ (6:ℕ)) * hj
  · linear_combination (-4 * c * g * σ ^ (5:ℕ) * w * O ^ (2:ℕ) -
      8 * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) + 96 * c * g * σ ^ (3:ℕ) * w * O ^ (4:ℕ) -
      4 * c * g * σ * w ^ (5:ℕ) * O ^ (2:ℕ) + 48 * c * g * σ * w ^ (3:ℕ) * O ^ (4:ℕ) -
      92 * c * g * σ * w * O ^ (6:ℕ)) * hj
  · linear_combination (((-12 * d * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w * O ^ (2:ℕ) -
      8 * d * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j -
      16 * d * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
      84 * d * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w * O ^ (4:ℕ) -
      8 * d * c ^ (2:ℕ) * g * σ * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
      32 * d * c ^ (2:ℕ) * g * σ * w * O ^ (5:ℕ) * j -
      4 * d * c ^ (2:ℕ) * g * w ^ (5:ℕ) * O ^ (2:ℕ)) +
      (20 * d * c ^ (2:ℕ) * g * w ^ (3:ℕ) * O ^ (4:ℕ) - 16 * d * c ^ (2:ℕ) * g * w * O ^ (6:ℕ) +
      4 * d * c * g * σ ^ (5:ℕ) * w * O ^ (2:ℕ) + 8 * d * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ)
      + 16 * d * c * g * σ ^ (3:ℕ) * w * O ^ (4:ℕ) + 64 * d * c * g * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j
      + 4 * d * c * g * σ * w ^ (5:ℕ) * O ^ (2:ℕ))) + ((-4 * d * c * g * σ * w * O ^ (6:ℕ) -
      4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (2:ℕ) * O ^ (2:ℕ) +
      112 * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w * O ^ (4:ℕ) +
      64 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j +
      48 * c ^ (2:ℕ) * g * σ * w ^ (3:ℕ) * O ^ (4:ℕ) - 96 * c ^ (2:ℕ) * g * σ * w * O ^ (6:ℕ) -
      16 * c * g * σ ^ (4:ℕ) * w * O ^ (4:ℕ)) + (32 * c * g * σ ^ (3:ℕ) * w * O ^ (5:ℕ) * j -
      64 * c * g * σ ^ (2:ℕ) * w * O ^ (6:ℕ) + 32 * c * g * σ * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
      128 * c * g * σ * w * O ^ (7:ℕ) * j + 16 * c * g * w ^ (5:ℕ) * O ^ (4:ℕ) -
      32 * c * g * w ^ (3:ℕ) * O ^ (6:ℕ) + 16 * c * g * w * O ^ (8:ℕ)))) * hj
  · linear_combination (((4 * d * c * σ ^ (5:ℕ) * w * O ^ (2:ℕ) +
      8 * d * c * σ ^ (4:ℕ) * w * O ^ (3:ℕ) * j + 8 * d * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
      16 * d * c * σ ^ (3:ℕ) * w * O ^ (4:ℕ) + 8 * d * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
      32 * d * c * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j + 4 * d * c * σ * w ^ (5:ℕ) * O ^ (2:ℕ)) +
      (-4 * d * c * σ * w * O ^ (6:ℕ) - 32 * d * σ ^ (4:ℕ) * w * O ^ (4:ℕ) -
      64 * d * σ ^ (3:ℕ) * w * O ^ (5:ℕ) * j - 16 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
      16 * d * w ^ (5:ℕ) * O ^ (4:ℕ) - 32 * d * w ^ (3:ℕ) * O ^ (6:ℕ) + 16 * d * w * O ^ (8:ℕ) -
      8 * c * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ))) + ((-4 * c * g * w ^ (4:ℕ) * O ^ (2:ℕ) +
      4 * c * g * w ^ (2:ℕ) * O ^ (4:ℕ) - 32 * c * σ ^ (4:ℕ) * w * O ^ (4:ℕ) -
      64 * c * σ ^ (3:ℕ) * w * O ^ (5:ℕ) * j - 16 * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
      16 * c * w ^ (5:ℕ) * O ^ (4:ℕ) - 32 * c * w ^ (3:ℕ) * O ^ (6:ℕ) + 16 * c * w * O ^ (8:ℕ)) +
      (-16 * σ ^ (5:ℕ) * w * O ^ (4:ℕ) - 32 * σ ^ (4:ℕ) * w * O ^ (5:ℕ) * j -
      32 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) + 64 * σ ^ (3:ℕ) * w * O ^ (6:ℕ) -
      32 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j + 128 * σ ^ (2:ℕ) * w * O ^ (7:ℕ) * j -
      16 * σ * w ^ (5:ℕ) * O ^ (4:ℕ) + 16 * σ * w * O ^ (8:ℕ)))) * hj
  · linear_combination (((4 * d * c * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) +
      8 * d * c * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) - 24 * d * c * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ)
      + 4 * d * c * w ^ (6:ℕ) * O ^ (2:ℕ) - 8 * d * c * w ^ (4:ℕ) * O ^ (4:ℕ)) +
      (4 * d * c * w ^ (2:ℕ) * O ^ (6:ℕ) - 32 * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
      32 * d * σ * w ^ (4:ℕ) * O ^ (4:ℕ) + 32 * d * σ * w ^ (2:ℕ) * O ^ (6:ℕ) -
      12 * c * g * σ ^ (3:ℕ) * w * O ^ (2:ℕ))) + ((-4 * c * g * σ * w ^ (3:ℕ) * O ^ (2:ℕ) +
      20 * c * g * σ * w * O ^ (4:ℕ) - 32 * c * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
      32 * c * σ * w ^ (4:ℕ) * O ^ (4:ℕ) + 32 * c * σ * w ^ (2:ℕ) * O ^ (6:ℕ)) +
      (-16 * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) - 32 * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
      96 * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) - 16 * w ^ (6:ℕ) * O ^ (4:ℕ) +
      32 * w ^ (4:ℕ) * O ^ (6:ℕ) - 16 * w ^ (2:ℕ) * O ^ (8:ℕ)))) * hj

@[tmio M, powerlib_domain] private theorem sl_norm {d c σ w O j : ℂ} (hj : j ^ 2 = -1) :
    sliceVecP d c σ w (-O) j ⬝ᵥ sliceVecQ d σ w O j = slicePairing d c σ w O j := by
  simp only [sliceVecP, sliceVecQ, slicePairing, dotProduct, Fin.sum_univ_five, Fin.isValue,
      Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination (-d * c * w * O ^ (2:ℕ) - 2 * d * σ * w * O ^ (2:ℕ) - 2 * c * σ * w * O ^ (2:ℕ)
    - σ ^ (2:ℕ) * w * O ^ (2:ℕ) - w ^ (3:ℕ) * O ^ (2:ℕ) + 2 * w * O ^ (4:ℕ)) * hj

/-- The real part of `w Q_c ⟨p̃, C(q, q, q̄)⟩`, reduced modulo the Hopf relations. -/
private def slY1r {R : Type*} [CommRing R] (d σ w O : R) : R :=
  ((-4 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    16 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    8 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    24 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    8 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    16 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ)) +
    (24 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    8 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) - 4 * d ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) +
    16 * d ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) - 24 * d ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    16 * d ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) - 4 * d ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ))) +
    ((-4 * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) - 16 * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    8 * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) - 24 * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    8 * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) - 16 * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ)) +
    (24 * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) - 8 * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    4 * w ^ (10:ℕ) * O ^ (4:ℕ) + 16 * w ^ (8:ℕ) * O ^ (6:ℕ) - 24 * w ^ (6:ℕ) * O ^ (8:ℕ) +
    16 * w ^ (4:ℕ) * O ^ (10:ℕ) - 4 * w ^ (2:ℕ) * O ^ (12:ℕ)))

/-- The imaginary part of `w Q_c ⟨p̃, C(q, q, q̄)⟩`, reduced modulo the Hopf relations. -/
private def slY1i {R : Type*} [CommRing R] (d σ w O : R) : R :=
  -4 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) -
    12 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) -
    4 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) -
    12 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) +
    8 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) +
    4 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) - 4 * d ^ (2:ℕ) * σ * w ^ (8:ℕ) * O ^ (3:ℕ) +
    12 * d ^ (2:ℕ) * σ * w ^ (6:ℕ) * O ^ (5:ℕ) - 12 * d ^ (2:ℕ) * σ * w ^ (4:ℕ) * O ^ (7:ℕ) +
    4 * d ^ (2:ℕ) * σ * w ^ (2:ℕ) * O ^ (9:ℕ) - 4 * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) -
    12 * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) - 4 * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) -
    12 * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) + 8 * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) +
    4 * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) - 4 * σ * w ^ (8:ℕ) * O ^ (5:ℕ) +
    12 * σ * w ^ (6:ℕ) * O ^ (7:ℕ) - 12 * σ * w ^ (4:ℕ) * O ^ (9:ℕ) + 4 * σ * w ^ (2:ℕ) * O ^ (11:ℕ)

/-- The real part of `w Q_c ⟨p̃, B(q, w r)⟩`, reduced modulo the Hopf relations. -/
private def slY2r {R : Type*} [CommRing R] (d σ w O : R) : R :=
  (((d ^ (2:ℕ) * σ ^ (10:ℕ) * w * O ^ (2:ℕ) + 3 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    d ^ (2:ℕ) * σ ^ (8:ℕ) * w * O ^ (4:ℕ) + 2 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)) +
    (-2 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w * O ^ (6:ℕ) - 2 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ)
    + 2 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    2 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) - 2 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (8:ℕ)))
    + ((-3 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) +
    8 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    6 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) + d ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (10:ℕ) -
    d ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (2:ℕ)) + (5 * d ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) -
    10 * d ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) + 10 * d ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    5 * d ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) + d ^ (2:ℕ) * w * O ^ (12:ℕ)))) +
    (((σ ^ (10:ℕ) * w * O ^ (4:ℕ) + 3 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    σ ^ (8:ℕ) * w * O ^ (6:ℕ) + 2 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)) +
    (-2 * σ ^ (6:ℕ) * w * O ^ (8:ℕ) - 2 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    2 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) + 2 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    2 * σ ^ (4:ℕ) * w * O ^ (10:ℕ))) + ((-3 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    8 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) - 6 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    σ ^ (2:ℕ) * w * O ^ (12:ℕ) - w ^ (11:ℕ) * O ^ (4:ℕ)) + (5 * w ^ (9:ℕ) * O ^ (6:ℕ) -
    10 * w ^ (7:ℕ) * O ^ (8:ℕ) + 10 * w ^ (5:ℕ) * O ^ (10:ℕ) - 5 * w ^ (3:ℕ) * O ^ (12:ℕ) +
    w * O ^ (14:ℕ))))

/-- The imaginary part of `w Q_c ⟨p̃, B(q, w r)⟩`, reduced modulo the Hopf relations. -/
private def slY2i {R : Type*} [CommRing R] (d σ w O : R) : R :=
  2 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w * O ^ (3:ℕ) + 4 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) +
    4 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w * O ^ (5:ℕ) - 4 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) +
    4 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) +
    4 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) - 4 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (9:ℕ) -
    2 * d ^ (2:ℕ) * σ * w ^ (9:ℕ) * O ^ (3:ℕ) + 8 * d ^ (2:ℕ) * σ * w ^ (7:ℕ) * O ^ (5:ℕ) -
    12 * d ^ (2:ℕ) * σ * w ^ (5:ℕ) * O ^ (7:ℕ) + 8 * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (9:ℕ) -
    2 * d ^ (2:ℕ) * σ * w * O ^ (11:ℕ) + 2 * σ ^ (9:ℕ) * w * O ^ (5:ℕ) +
    4 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) + 4 * σ ^ (7:ℕ) * w * O ^ (7:ℕ) -
    4 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) + 4 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) +
    4 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) - 4 * σ ^ (3:ℕ) * w * O ^ (11:ℕ) -
    2 * σ * w ^ (9:ℕ) * O ^ (5:ℕ) + 8 * σ * w ^ (7:ℕ) * O ^ (7:ℕ) - 12 * σ * w ^ (5:ℕ) * O ^ (9:ℕ) +
    8 * σ * w ^ (3:ℕ) * O ^ (11:ℕ) - 2 * σ * w * O ^ (13:ℕ)

/-- The real part of `w Q_c² ⟨p̃, B(q̄, w χ s)⟩`, reduced modulo the Hopf relations. -/
private def slY3r {R : Type*} [CommRing R] (d σ w O : R) : R :=
  (((((-d ^ (4:ℕ) * σ ^ (14:ℕ) * w * O ^ (4:ℕ) - 9 * d ^ (4:ℕ) * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ)
    + 9 * d ^ (4:ℕ) * σ ^ (12:ℕ) * w * O ^ (6:ℕ) -
    33 * d ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)) +
    (26 * d ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    51 * d ^ (4:ℕ) * σ ^ (10:ℕ) * w * O ^ (8:ℕ) - 65 * d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ)
    + 35 * d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    41 * d ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ))) +
    ((85 * d ^ (4:ℕ) * σ ^ (8:ℕ) * w * O ^ (10:ℕ) -
    75 * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    60 * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) -
    10 * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)) +
    (-84 * d ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    45 * d ^ (4:ℕ) * σ ^ (6:ℕ) * w * O ^ (12:ℕ) -
    51 * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (4:ℕ) +
    95 * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) +
    10 * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ)))) +
    (((70 * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) -
    103 * d ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) -
    21 * d ^ (4:ℕ) * σ ^ (4:ℕ) * w * O ^ (14:ℕ) -
    19 * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (4:ℕ)) +
    (74 * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ) -
    41 * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) -
    100 * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) +
    91 * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) +
    26 * d ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ))) +
    ((-31 * d ^ (4:ℕ) * σ ^ (2:ℕ) * w * O ^ (16:ℕ) - 3 * d ^ (4:ℕ) * w ^ (15:ℕ) * O ^ (4:ℕ) +
    21 * d ^ (4:ℕ) * w ^ (13:ℕ) * O ^ (6:ℕ) - 51 * d ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (8:ℕ) +
    45 * d ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (10:ℕ)) + (15 * d ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (12:ℕ) -
    57 * d ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (14:ℕ) + 39 * d ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (16:ℕ) -
    9 * d ^ (4:ℕ) * w * O ^ (18:ℕ) + 12 * d ^ (3:ℕ) * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ))))) +
    ((((60 * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    36 * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    120 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    48 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)) +
    (24 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    120 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) -
    72 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    24 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) -
    24 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ))) +
    ((60 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ) -
    144 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) +
    72 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) +
    48 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) -
    36 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ)) +
    (12 * d ^ (3:ℕ) * σ * w ^ (13:ℕ) * O ^ (6:ℕ) - 60 * d ^ (3:ℕ) * σ * w ^ (11:ℕ) * O ^ (8:ℕ) +
    120 * d ^ (3:ℕ) * σ * w ^ (9:ℕ) * O ^ (10:ℕ) - 120 * d ^ (3:ℕ) * σ * w ^ (7:ℕ) * O ^ (12:ℕ) +
    60 * d ^ (3:ℕ) * σ * w ^ (5:ℕ) * O ^ (14:ℕ)))) + (((-12 * d ^ (3:ℕ) * σ * w ^ (3:ℕ) * O ^ (16:ℕ)
    - 2 * d ^ (2:ℕ) * σ ^ (14:ℕ) * w * O ^ (6:ℕ) -
    18 * d ^ (2:ℕ) * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    18 * d ^ (2:ℕ) * σ ^ (12:ℕ) * w * O ^ (8:ℕ)) +
    (-66 * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    28 * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    102 * d ^ (2:ℕ) * σ ^ (10:ℕ) * w * O ^ (10:ℕ) -
    130 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) -
    26 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ))) +
    ((-14 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    170 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w * O ^ (12:ℕ) -
    150 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) -
    24 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    116 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ)) +
    (-312 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) +
    90 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w * O ^ (14:ℕ) -
    102 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ) +
    94 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) +
    116 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ)))))) +
    (((((236 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) -
    302 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) -
    42 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (16:ℕ) -
    38 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (6:ℕ)) +
    (124 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (8:ℕ) +
    14 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (10:ℕ) -
    344 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (12:ℕ) +
    278 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (14:ℕ) +
    28 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (16:ℕ))) +
    ((-62 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (18:ℕ) - 6 * d ^ (2:ℕ) * w ^ (15:ℕ) * O ^ (6:ℕ) +
    42 * d ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (8:ℕ) - 102 * d ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (10:ℕ)) +
    (90 * d ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (12:ℕ) + 30 * d ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (14:ℕ) -
    114 * d ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (16:ℕ) + 78 * d ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (18:ℕ) -
    18 * d ^ (2:ℕ) * w * O ^ (20:ℕ)))) + (((12 * d * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    60 * d * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) + 36 * d * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    120 * d * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ)) + (48 * d * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) +
    24 * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) + 120 * d * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) -
    72 * d * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) - 24 * d * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ))) +
    ((-24 * d * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) + 60 * d * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (8:ℕ) -
    144 * d * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (10:ℕ) + 72 * d * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (12:ℕ) +
    48 * d * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (14:ℕ)) + (-36 * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (16:ℕ) +
    12 * d * σ * w ^ (13:ℕ) * O ^ (8:ℕ) - 60 * d * σ * w ^ (11:ℕ) * O ^ (10:ℕ) +
    120 * d * σ * w ^ (9:ℕ) * O ^ (12:ℕ) - 120 * d * σ * w ^ (7:ℕ) * O ^ (14:ℕ))))) +
    ((((60 * d * σ * w ^ (5:ℕ) * O ^ (16:ℕ) - 12 * d * σ * w ^ (3:ℕ) * O ^ (18:ℕ) -
    σ ^ (14:ℕ) * w * O ^ (8:ℕ) - 9 * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)) +
    (9 * σ ^ (12:ℕ) * w * O ^ (10:ℕ) - 33 * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    2 * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) + 51 * σ ^ (10:ℕ) * w * O ^ (12:ℕ) -
    65 * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ))) + ((-61 * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) -
    55 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) + 85 * σ ^ (8:ℕ) * w * O ^ (14:ℕ) -
    75 * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) - 84 * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ)) +
    (-106 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) - 228 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) +
    45 * σ ^ (6:ℕ) * w * O ^ (16:ℕ) - 51 * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (8:ℕ) -
    σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (10:ℕ)))) + (((106 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (12:ℕ) +
    166 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (14:ℕ) - 199 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (16:ℕ) -
    21 * σ ^ (4:ℕ) * w * O ^ (18:ℕ)) + (-19 * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (8:ℕ) +
    50 * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (10:ℕ) + 55 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (12:ℕ) -
    244 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (14:ℕ) + 187 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (16:ℕ))) +
    ((2 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (18:ℕ) - 31 * σ ^ (2:ℕ) * w * O ^ (20:ℕ) -
    3 * w ^ (15:ℕ) * O ^ (8:ℕ) + 21 * w ^ (13:ℕ) * O ^ (10:ℕ) - 51 * w ^ (11:ℕ) * O ^ (12:ℕ)) +
    (45 * w ^ (9:ℕ) * O ^ (14:ℕ) + 15 * w ^ (7:ℕ) * O ^ (16:ℕ) - 57 * w ^ (5:ℕ) * O ^ (18:ℕ) +
    39 * w ^ (3:ℕ) * O ^ (20:ℕ) - 9 * w * O ^ (22:ℕ))))))

/-- The imaginary part of `w Q_c² ⟨p̃, B(q̄, w χ s)⟩`, reduced modulo the Hopf relations. -/
private def slY3i {R : Type*} [CommRing R] (d σ w O : R) : R :=
  ((((-6 * d ^ (4:ℕ) * σ ^ (13:ℕ) * w * O ^ (5:ℕ) -
    36 * d ^ (4:ℕ) * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) -
    12 * d ^ (4:ℕ) * σ ^ (11:ℕ) * w * O ^ (7:ℕ) - 90 * d ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ)
    - 36 * d ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) +
    30 * d ^ (4:ℕ) * σ ^ (9:ℕ) * w * O ^ (9:ℕ) - 120 * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ)
    - 24 * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ)) +
    ((24 * d ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) +
    120 * d ^ (4:ℕ) * σ ^ (7:ℕ) * w * O ^ (11:ℕ) -
    90 * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) +
    24 * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ)) +
    (-12 * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) -
    72 * d ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) +
    150 * d ^ (4:ℕ) * σ ^ (5:ℕ) * w * O ^ (13:ℕ) -
    36 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (5:ℕ) +
    36 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ)))) +
    ((24 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) +
    72 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) -
    180 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) +
    84 * d ^ (4:ℕ) * σ ^ (3:ℕ) * w * O ^ (15:ℕ) - 6 * d ^ (4:ℕ) * σ * w ^ (13:ℕ) * O ^ (5:ℕ) +
    12 * d ^ (4:ℕ) * σ * w ^ (11:ℕ) * O ^ (7:ℕ) + 30 * d ^ (4:ℕ) * σ * w ^ (9:ℕ) * O ^ (9:ℕ) -
    120 * d ^ (4:ℕ) * σ * w ^ (7:ℕ) * O ^ (11:ℕ)) + ((150 * d ^ (4:ℕ) * σ * w ^ (5:ℕ) * O ^ (13:ℕ) -
    84 * d ^ (4:ℕ) * σ * w ^ (3:ℕ) * O ^ (15:ℕ) + 18 * d ^ (4:ℕ) * σ * w * O ^ (17:ℕ) -
    6 * d ^ (3:ℕ) * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ)) +
    (-36 * d ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) -
    12 * d ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) -
    90 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) -
    12 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) +
    6 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ))))) +
    (((-120 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) +
    72 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) +
    24 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) +
    24 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) -
    90 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (5:ℕ) +
    168 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) -
    60 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) -
    24 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ)) +
    ((6 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) -
    36 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (5:ℕ) +
    132 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (7:ℕ) -
    168 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ)) +
    (72 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ) +
    12 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) -
    12 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ) - 6 * d ^ (3:ℕ) * w ^ (15:ℕ) * O ^ (5:ℕ) +
    36 * d ^ (3:ℕ) * w ^ (13:ℕ) * O ^ (7:ℕ)))) + ((-90 * d ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (9:ℕ) +
    120 * d ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (11:ℕ) - 90 * d ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (13:ℕ) +
    36 * d ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (15:ℕ) - 6 * d ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (17:ℕ) -
    12 * d ^ (2:ℕ) * σ ^ (13:ℕ) * w * O ^ (7:ℕ) -
    60 * d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) -
    24 * d ^ (2:ℕ) * σ ^ (11:ℕ) * w * O ^ (9:ℕ)) +
    ((-120 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) -
    36 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) + 60 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w * O ^ (11:ℕ)
    - 120 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ)) +
    (72 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) +
    240 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w * O ^ (13:ℕ) -
    60 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) -
    24 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) -
    48 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ)))))) +
    ((((-168 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) +
    300 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w * O ^ (15:ℕ) -
    12 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (7:ℕ) -
    72 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ) +
    120 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ) +
    192 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) -
    396 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ) +
    168 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (17:ℕ)) + ((-36 * d ^ (2:ℕ) * σ * w ^ (11:ℕ) * O ^ (9:ℕ) +
    180 * d ^ (2:ℕ) * σ * w ^ (9:ℕ) * O ^ (11:ℕ) - 360 * d ^ (2:ℕ) * σ * w ^ (7:ℕ) * O ^ (13:ℕ) +
    360 * d ^ (2:ℕ) * σ * w ^ (5:ℕ) * O ^ (15:ℕ)) + (-180 * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (17:ℕ) +
    36 * d ^ (2:ℕ) * σ * w * O ^ (19:ℕ) - 6 * d * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) -
    36 * d * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) - 12 * d * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ)))) +
    ((-90 * d * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) - 12 * d * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) +
    6 * d * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) - 120 * d * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) +
    72 * d * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) + 24 * d * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) +
    24 * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) - 90 * d * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (7:ℕ)) +
    ((168 * d * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ) - 60 * d * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ) -
    24 * d * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) + 6 * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ)) +
    (-36 * d * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (7:ℕ) + 132 * d * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (9:ℕ) -
    168 * d * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (11:ℕ) + 72 * d * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (13:ℕ) +
    12 * d * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (15:ℕ))))) +
    (((-12 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (17:ℕ) - 6 * d * w ^ (15:ℕ) * O ^ (7:ℕ) +
    36 * d * w ^ (13:ℕ) * O ^ (9:ℕ) - 90 * d * w ^ (11:ℕ) * O ^ (11:ℕ) +
    120 * d * w ^ (9:ℕ) * O ^ (13:ℕ) - 90 * d * w ^ (7:ℕ) * O ^ (15:ℕ) +
    36 * d * w ^ (5:ℕ) * O ^ (17:ℕ) - 6 * d * w ^ (3:ℕ) * O ^ (19:ℕ)) +
    ((-6 * σ ^ (13:ℕ) * w * O ^ (9:ℕ) - 24 * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) -
    12 * σ ^ (11:ℕ) * w * O ^ (11:ℕ) - 30 * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ)) +
    (30 * σ ^ (9:ℕ) * w * O ^ (13:ℕ) + 24 * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) +
    48 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) + 120 * σ ^ (7:ℕ) * w * O ^ (15:ℕ) +
    30 * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ)))) + ((-48 * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ) -
    36 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) - 96 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ) +
    150 * σ ^ (5:ℕ) * w * O ^ (17:ℕ) + 24 * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (9:ℕ) -
    108 * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (11:ℕ) + 96 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (13:ℕ) +
    120 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (15:ℕ)) + ((-216 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (17:ℕ) +
    84 * σ ^ (3:ℕ) * w * O ^ (19:ℕ) + 6 * σ * w ^ (13:ℕ) * O ^ (9:ℕ) -
    48 * σ * w ^ (11:ℕ) * O ^ (11:ℕ)) + (150 * σ * w ^ (9:ℕ) * O ^ (13:ℕ) -
    240 * σ * w ^ (7:ℕ) * O ^ (15:ℕ) + 210 * σ * w ^ (5:ℕ) * O ^ (17:ℕ) -
    96 * σ * w ^ (3:ℕ) * O ^ (19:ℕ) + 18 * σ * w * O ^ (21:ℕ))))))

/-- The real part of `Q_c ⟨p̃, q⟩`, reduced modulo the Hopf relations (`Q_c = d (σ² + w² − ω²) −
2σω²`, `p̃` the unnormalised left eigenvector of the slice). -/
def slicePairRe {R : Type*} [CommRing R] (d σ w ω : R) : R :=
  4 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w * ω ^ (2:ℕ) + 4 * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * ω ^ (2:ℕ) +
    2 * d * σ ^ (4:ℕ) * w * ω ^ (2:ℕ) + 4 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (2:ℕ) -
    4 * d * σ ^ (2:ℕ) * w * ω ^ (4:ℕ) + 2 * d * w ^ (5:ℕ) * ω ^ (2:ℕ) -
    4 * d * w ^ (3:ℕ) * ω ^ (4:ℕ) + 2 * d * w * ω ^ (6:ℕ) + 4 * σ * w * ω ^ (6:ℕ)

/-- The imaginary part of `Q_c ⟨p̃, q⟩`, reduced modulo the Hopf relations (`Q_c = d (σ² + w² − ω²)
− 2σω²`, `p̃` the unnormalised left eigenvector of the slice). -/
def slicePairIm {R : Type*} [CommRing R] (d σ w ω : R) : R :=
  -2 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w * ω - 4 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω -
    2 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w * ω ^ (3:ℕ) - 2 * d ^ (2:ℕ) * w ^ (5:ℕ) * ω +
    6 * d ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (3:ℕ) - 4 * d ^ (2:ℕ) * w * ω ^ (5:ℕ) +
    4 * d * σ ^ (3:ℕ) * w * ω ^ (3:ℕ) + 4 * d * σ * w ^ (3:ℕ) * ω ^ (3:ℕ) -
    4 * d * σ * w * ω ^ (5:ℕ) - 2 * σ ^ (4:ℕ) * w * ω ^ (3:ℕ) -
    4 * σ ^ (2:ℕ) * w ^ (3:ℕ) * ω ^ (3:ℕ) - 10 * σ ^ (2:ℕ) * w * ω ^ (5:ℕ) -
    2 * w ^ (5:ℕ) * ω ^ (3:ℕ) + 6 * w ^ (3:ℕ) * ω ^ (5:ℕ) - 4 * w * ω ^ (7:ℕ)

/-- The real part of `Q_c χ`, reduced modulo the Hopf relations (`χ(s) = s(s + d)(s + c)((s + σ)² +
w²) + c g w` at `s = 2iω`). -/
def sliceShiftRe {R : Type*} [CommRing R] (d σ w ω : R) : R :=
  -3 * d ^ (2:ℕ) * σ ^ (4:ℕ) * ω ^ (2:ℕ) - 6 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) +
    6 * d ^ (2:ℕ) * σ ^ (2:ℕ) * ω ^ (4:ℕ) - 3 * d ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ) +
    18 * d ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) - 15 * d ^ (2:ℕ) * ω ^ (6:ℕ) +
    24 * d * σ ^ (3:ℕ) * ω ^ (4:ℕ) + 24 * d * σ * w ^ (2:ℕ) * ω ^ (4:ℕ) - 24 * d * σ * ω ^ (6:ℕ) -
    3 * σ ^ (4:ℕ) * ω ^ (4:ℕ) - 6 * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) - 42 * σ ^ (2:ℕ) * ω ^ (6:ℕ) -
    3 * w ^ (4:ℕ) * ω ^ (4:ℕ) + 18 * w ^ (2:ℕ) * ω ^ (6:ℕ) - 15 * ω ^ (8:ℕ)

/-- The imaginary part of `Q_c χ`, reduced modulo the Hopf relations (`χ(s) = s(s + d)(s + c)((s +
σ)² + w²) + c g w` at `s = 2iω`). -/
def sliceShiftIm {R : Type*} [CommRing R] (d σ w ω : R) : R :=
  -12 * d ^ (2:ℕ) * σ ^ (3:ℕ) * ω ^ (3:ℕ) - 12 * d ^ (2:ℕ) * σ * w ^ (2:ℕ) * ω ^ (3:ℕ) -
    6 * d * σ ^ (4:ℕ) * ω ^ (3:ℕ) - 12 * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (3:ℕ) +
    30 * d * σ ^ (2:ℕ) * ω ^ (5:ℕ) - 6 * d * w ^ (4:ℕ) * ω ^ (3:ℕ) + 30 * d * w ^ (2:ℕ) * ω ^ (5:ℕ)
    - 24 * d * ω ^ (7:ℕ) - 48 * σ * ω ^ (7:ℕ)

@[tmio M, powerlib_domain] private theorem sl_Y1 {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d))
    (h2 : c * g * w = O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    w * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) * (sliceVecP d c σ w (-O) j ⬝ᵥ
        slTri c g (sliceVecQ d σ w O j) (sliceVecQ d σ w O j)
      (sliceVecQ d σ w (-O) j)) =
      slY1r d σ w O + slY1i d σ w O * j := by
  simp only [sliceVecP, slTri, sliceVecQ, slY1r, slY1i, dotProduct, Fin.sum_univ_five, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (((d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O * j -
    8 * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) + 3 * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O * j -
    7 * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j - 16 * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    3 * d * σ ^ (2:ℕ) * w ^ (6:ℕ) * O * j - 10 * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j) +
    (7 * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j - 8 * d * σ * w ^ (6:ℕ) * O ^ (2:ℕ) +
    16 * d * σ * w ^ (4:ℕ) * O ^ (4:ℕ) - 8 * d * σ * w ^ (2:ℕ) * O ^ (6:ℕ) + d * w ^ (8:ℕ) * O * j -
    3 * d * w ^ (6:ℕ) * O ^ (3:ℕ) * j + 3 * d * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    d * w ^ (2:ℕ) * O ^ (7:ℕ) * j)) + ((-4 * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    6 * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j - 12 * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    4 * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) - 12 * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j +
    4 * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j - 12 * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    16 * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ)) + (-4 * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    6 * σ * w ^ (6:ℕ) * O ^ (3:ℕ) * j + 12 * σ * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    6 * σ * w ^ (2:ℕ) * O ^ (7:ℕ) * j - 4 * w ^ (8:ℕ) * O ^ (2:ℕ) + 12 * w ^ (6:ℕ) * O ^ (4:ℕ) -
    12 * w ^ (4:ℕ) * O ^ (6:ℕ) + 4 * w ^ (2:ℕ) * O ^ (8:ℕ)))) * h1 +
    (((-3 * d * σ ^ (6:ℕ) * w ^ (2:ℕ) - 4 * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O * j -
    9 * d * σ ^ (4:ℕ) * w ^ (4:ℕ) + 5 * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    8 * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O * j + 8 * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j) +
    (-9 * d * σ ^ (2:ℕ) * w ^ (6:ℕ) + 14 * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    5 * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) - 4 * d * σ * w ^ (6:ℕ) * O * j +
    8 * d * σ * w ^ (4:ℕ) * O ^ (3:ℕ) * j - 4 * d * σ * w ^ (2:ℕ) * O ^ (5:ℕ) * j)) +
    ((-3 * d * w ^ (8:ℕ) + 9 * d * w ^ (6:ℕ) * O ^ (2:ℕ) - 9 * d * w ^ (4:ℕ) * O ^ (4:ℕ) +
    3 * d * w ^ (2:ℕ) * O ^ (6:ℕ) + 6 * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) +
    8 * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j) + (12 * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    4 * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) + 8 * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    8 * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j + 6 * σ * w ^ (6:ℕ) * O ^ (2:ℕ) -
    12 * σ * w ^ (4:ℕ) * O ^ (4:ℕ) + 6 * σ * w ^ (2:ℕ) * O ^ (6:ℕ)))) * h2 +
    ((((2 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    4 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j +
    6 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    8 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    2 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    8 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j +
    8 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    6 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ)) +
    ((-8 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    4 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    8 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    2 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ)) +
    (-4 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j +
    8 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    4 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    2 * d ^ (2:ℕ) * c * σ * w ^ (8:ℕ) * O ^ (2:ℕ) - 6 * d ^ (2:ℕ) * c * σ * w ^ (6:ℕ) * O ^ (4:ℕ))))
    + (((6 * d ^ (2:ℕ) * c * σ * w ^ (4:ℕ) * O ^ (6:ℕ) -
    2 * d ^ (2:ℕ) * c * σ * w ^ (2:ℕ) * O ^ (8:ℕ) +
    4 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    8 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j) +
    (8 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    8 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    8 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    8 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    4 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ))) +
    ((-8 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    4 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    4 * d * c * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    4 * d * c * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)) +
    (-4 * d * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    16 * d * c * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    16 * d * c * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    16 * d * c * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    16 * d * c * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j)))) +
    (((-16 * d * c * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j -
    2 * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) + 4 * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    6 * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    8 * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    10 * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) + 8 * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    24 * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j) + ((-6 * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    8 * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    4 * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    8 * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ)) +
    (10 * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) + 4 * d * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j -
    8 * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j + 4 * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j -
    2 * d * σ * w ^ (8:ℕ) * O ^ (4:ℕ)))) + (((6 * d * σ * w ^ (6:ℕ) * O ^ (6:ℕ) -
    6 * d * σ * w ^ (4:ℕ) * O ^ (8:ℕ) + 2 * d * σ * w ^ (2:ℕ) * O ^ (10:ℕ) -
    8 * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ)) + (-8 * c * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    16 * c * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j - 8 * c * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    8 * c * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) + 4 * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ))) +
    ((-8 * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j + 8 * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    16 * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) + 8 * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)) +
    (-8 * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j + 8 * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    4 * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) - 8 * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    4 * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ)))))) * hj

@[tmio M, powerlib_domain] private theorem sl_Y2 {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d))
    (h2 : c * g * w = O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    w * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) * (sliceVecP d c σ w (-O) j ⬝ᵥ
        slBil c g (sliceVecQ d σ w O j) (slR σ w O)) =
      slY2r d σ w O + slY2i d σ w O * j := by
  simp only [sliceVecP, slBil, sliceVecQ, slR, slY2r, slY2i, dotProduct, Fin.sum_univ_five,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination ((((d * σ ^ (8:ℕ) * w * O * j + d * σ ^ (7:ℕ) * w * O ^ (2:ℕ) +
    3 * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * O * j + 3 * d * σ ^ (6:ℕ) * w * O ^ (3:ℕ) * j) +
    (-d * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - d * σ ^ (5:ℕ) * w * O ^ (4:ℕ) +
    3 * d * σ ^ (4:ℕ) * w ^ (5:ℕ) * O * j + 2 * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    d * σ ^ (4:ℕ) * w * O ^ (5:ℕ) * j)) + ((-5 * d * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    2 * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) - d * σ ^ (3:ℕ) * w * O ^ (6:ℕ) +
    d * σ ^ (2:ℕ) * w ^ (7:ℕ) * O * j - d * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j) +
    (3 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j - 3 * d * σ ^ (2:ℕ) * w * O ^ (7:ℕ) * j -
    3 * d * σ * w ^ (7:ℕ) * O ^ (2:ℕ) + 3 * d * σ * w ^ (5:ℕ) * O ^ (4:ℕ) -
    d * σ * w ^ (3:ℕ) * O ^ (6:ℕ)))) + (((d * σ * w * O ^ (8:ℕ) + σ ^ (8:ℕ) * w * O ^ (2:ℕ) +
    2 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - 2 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    2 * σ ^ (5:ℕ) * w * O ^ (5:ℕ) * j) + (4 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    4 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j - 4 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    2 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) + 8 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ))) +
    ((2 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) - 2 * σ * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    6 * σ * w ^ (5:ℕ) * O ^ (5:ℕ) * j - 6 * σ * w ^ (3:ℕ) * O ^ (7:ℕ) * j +
    2 * σ * w * O ^ (9:ℕ) * j) + (-w ^ (9:ℕ) * O ^ (2:ℕ) + 4 * w ^ (7:ℕ) * O ^ (4:ℕ) -
    6 * w ^ (5:ℕ) * O ^ (6:ℕ) + 4 * w ^ (3:ℕ) * O ^ (8:ℕ) - w * O ^ (10:ℕ))))) * h1 +
    ((((2 * d * σ ^ (8:ℕ) * w + 3 * d * σ ^ (7:ℕ) * w * O * j + 5 * d * σ ^ (6:ℕ) * w ^ (3:ℕ) -
    3 * d * σ ^ (6:ℕ) * w * O ^ (2:ℕ)) + (5 * d * σ ^ (5:ℕ) * w ^ (3:ℕ) * O * j -
    3 * d * σ ^ (5:ℕ) * w * O ^ (3:ℕ) * j + 3 * d * σ ^ (4:ℕ) * w ^ (5:ℕ) +
    2 * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - d * σ ^ (4:ℕ) * w * O ^ (4:ℕ))) +
    ((d * σ ^ (3:ℕ) * w ^ (5:ℕ) * O * j + 6 * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    3 * d * σ ^ (3:ℕ) * w * O ^ (5:ℕ) * j - d * σ ^ (2:ℕ) * w ^ (7:ℕ) +
    9 * d * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)) + (-11 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    3 * d * σ ^ (2:ℕ) * w * O ^ (6:ℕ) - d * σ * w ^ (7:ℕ) * O * j +
    9 * d * σ * w ^ (5:ℕ) * O ^ (3:ℕ) * j - 11 * d * σ * w ^ (3:ℕ) * O ^ (5:ℕ) * j))) +
    (((3 * d * σ * w * O ^ (7:ℕ) * j - d * w ^ (9:ℕ) + 4 * d * w ^ (7:ℕ) * O ^ (2:ℕ) -
    6 * d * w ^ (5:ℕ) * O ^ (4:ℕ) + 4 * d * w ^ (3:ℕ) * O ^ (6:ℕ)) + (-d * w * O ^ (8:ℕ) -
    4 * σ ^ (7:ℕ) * w * O ^ (2:ℕ) - 6 * σ ^ (6:ℕ) * w * O ^ (3:ℕ) * j -
    6 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) + 2 * σ ^ (5:ℕ) * w * O ^ (4:ℕ))) +
    ((-4 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 12 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    4 * σ ^ (3:ℕ) * w * O ^ (6:ℕ) + 2 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j -
    16 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j) + (6 * σ ^ (2:ℕ) * w * O ^ (7:ℕ) * j +
    2 * σ * w ^ (7:ℕ) * O ^ (2:ℕ) - 6 * σ * w ^ (5:ℕ) * O ^ (4:ℕ) + 6 * σ * w ^ (3:ℕ) * O ^ (6:ℕ) -
    2 * σ * w * O ^ (8:ℕ))))) * h2 + ((((2 * d ^ (2:ℕ) * c * σ ^ (9:ℕ) * w * O ^ (2:ℕ) +
    6 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    2 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w * O ^ (4:ℕ) +
    6 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    4 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    2 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w * O ^ (6:ℕ)) +
    (2 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    6 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    10 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    2 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w * O ^ (8:ℕ) - 2 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w * O ^ (4:ℕ) -
    6 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ))) +
    ((2 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w * O ^ (6:ℕ) - 6 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)
    - 4 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) + 2 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (8:ℕ)
    - 2 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    6 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)) +
    (10 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) - 2 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (10:ℕ)
    - 6 * d * c * σ ^ (8:ℕ) * w * O ^ (4:ℕ) - 14 * d * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    2 * d * c * σ ^ (6:ℕ) * w * O ^ (6:ℕ) - 10 * d * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    20 * d * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ)))) + (((6 * d * c * σ ^ (4:ℕ) * w * O ^ (8:ℕ) -
    2 * d * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) - 6 * d * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    10 * d * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) - 2 * d * c * σ ^ (2:ℕ) * w * O ^ (10:ℕ) -
    2 * d * σ ^ (9:ℕ) * w * O ^ (4:ℕ)) + (-6 * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    6 * d * σ ^ (7:ℕ) * w * O ^ (6:ℕ) - 6 * d * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    4 * d * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) + 2 * d * σ ^ (5:ℕ) * w * O ^ (8:ℕ) -
    2 * d * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ))) + ((-2 * d * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    26 * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) - 6 * d * σ ^ (3:ℕ) * w * O ^ (10:ℕ) +
    4 * c * σ ^ (7:ℕ) * w * O ^ (6:ℕ) + 8 * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    4 * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)) + (16 * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    4 * c * σ ^ (3:ℕ) * w * O ^ (10:ℕ) + 4 * σ ^ (8:ℕ) * w * O ^ (6:ℕ) +
    8 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) + 4 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    16 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) - 4 * σ ^ (4:ℕ) * w * O ^ (10:ℕ))))) * hj

@[tmio M, powerlib_domain] private theorem sl_Y3 {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d))
    (h2 : c * g * w = O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    w * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) ^ 2 * (sliceVecP d c σ w (-O) j ⬝ᵥ
      slBil c g (sliceVecQ d σ w (-O) j) (slS d c g σ w O j)) =
      slY3r d σ w O + slY3i d σ w O * j := by
  simp only [sliceVecP, slBil, sliceVecQ, slS, slY3r, slY3i, dotProduct, Fin.sum_univ_five,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (((((((-2 * d ^ (3:ℕ) * c * σ ^ (11:ℕ) * w * O ^ (3:ℕ) * j +
    6 * d ^ (3:ℕ) * c * σ ^ (10:ℕ) * w * O ^ (4:ℕ) -
    4 * d ^ (3:ℕ) * c * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    12 * d ^ (3:ℕ) * c * σ ^ (9:ℕ) * w * O ^ (5:ℕ) * j +
    16 * d ^ (3:ℕ) * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ)) +
    (56 * d ^ (3:ℕ) * c * σ ^ (8:ℕ) * w * O ^ (6:ℕ) +
    4 * d ^ (3:ℕ) * c * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    4 * d ^ (3:ℕ) * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    76 * d ^ (3:ℕ) * c * σ ^ (7:ℕ) * w * O ^ (7:ℕ) * j +
    12 * d ^ (3:ℕ) * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    52 * d ^ (3:ℕ) * c * σ ^ (6:ℕ) * w * O ^ (8:ℕ))) +
    ((16 * d ^ (3:ℕ) * c * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    28 * d ^ (3:ℕ) * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j -
    44 * d ^ (3:ℕ) * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    72 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    128 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)) +
    (-56 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w * O ^ (10:ℕ) +
    14 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j -
    4 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    108 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    172 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j -
    74 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w * O ^ (11:ℕ) * j))) +
    (((-2 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) -
    16 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    84 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    112 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    46 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w * O ^ (12:ℕ)) +
    (4 * d ^ (3:ℕ) * c * σ * w ^ (11:ℕ) * O ^ (3:ℕ) * j -
    16 * d ^ (3:ℕ) * c * σ * w ^ (9:ℕ) * O ^ (5:ℕ) * j +
    12 * d ^ (3:ℕ) * c * σ * w ^ (7:ℕ) * O ^ (7:ℕ) * j +
    20 * d ^ (3:ℕ) * c * σ * w ^ (5:ℕ) * O ^ (9:ℕ) * j -
    32 * d ^ (3:ℕ) * c * σ * w ^ (3:ℕ) * O ^ (11:ℕ) * j +
    12 * d ^ (3:ℕ) * c * σ * w * O ^ (13:ℕ) * j)) + ((-d ^ (3:ℕ) * σ ^ (12:ℕ) * w * O ^ (3:ℕ) * j +
    d ^ (3:ℕ) * σ ^ (11:ℕ) * w * O ^ (4:ℕ) - 3 * d ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j
    - 17 * d ^ (3:ℕ) * σ ^ (10:ℕ) * w * O ^ (5:ℕ) * j -
    3 * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ)) + (47 * d ^ (3:ℕ) * σ ^ (9:ℕ) * w * O ^ (6:ℕ)
    - 50 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    44 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w * O ^ (7:ℕ) * j -
    22 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    52 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    6 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w * O ^ (8:ℕ))))) +
    ((((10 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j -
    58 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    14 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j +
    34 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w * O ^ (9:ℕ) * j -
    38 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ)) +
    (-14 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    6 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) + 26 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w * O ^ (10:ℕ)
    + 15 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j -
    44 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    90 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j)) +
    ((60 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    59 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w * O ^ (11:ℕ) * j -
    27 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    4 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    194 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)) +
    (-196 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    25 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w * O ^ (12:ℕ) +
    9 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (3:ℕ) * j -
    29 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j -
    46 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j +
    222 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j))) +
    (((-235 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j +
    79 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w * O ^ (13:ℕ) * j - 7 * d ^ (3:ℕ) * σ * w ^ (11:ℕ) * O ^ (4:ℕ) +
    23 * d ^ (3:ℕ) * σ * w ^ (9:ℕ) * O ^ (6:ℕ) + 14 * d ^ (3:ℕ) * σ * w ^ (7:ℕ) * O ^ (8:ℕ)) +
    (-110 * d ^ (3:ℕ) * σ * w ^ (5:ℕ) * O ^ (10:ℕ) + 121 * d ^ (3:ℕ) * σ * w ^ (3:ℕ) * O ^ (12:ℕ) -
    41 * d ^ (3:ℕ) * σ * w * O ^ (14:ℕ) + 2 * d ^ (3:ℕ) * w ^ (13:ℕ) * O ^ (3:ℕ) * j -
    10 * d ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (5:ℕ) * j + 14 * d ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) * j)) +
    ((4 * d ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) * j - 26 * d ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) * j +
    22 * d ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) * j - 6 * d ^ (3:ℕ) * w * O ^ (15:ℕ) * j -
    d ^ (2:ℕ) * c * σ ^ (12:ℕ) * w * O ^ (3:ℕ) * j + d ^ (2:ℕ) * c * σ ^ (11:ℕ) * w * O ^ (4:ℕ)) +
    (-3 * d ^ (2:ℕ) * c * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    9 * d ^ (2:ℕ) * c * σ ^ (10:ℕ) * w * O ^ (5:ℕ) * j -
    3 * d ^ (2:ℕ) * c * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    23 * d ^ (2:ℕ) * c * σ ^ (9:ℕ) * w * O ^ (6:ℕ) -
    42 * d ^ (2:ℕ) * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    100 * d ^ (2:ℕ) * c * σ ^ (8:ℕ) * w * O ^ (7:ℕ) * j))))) +
    (((((-22 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    12 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    242 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w * O ^ (8:ℕ) +
    10 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j -
    82 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j) +
    (-50 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    214 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w * O ^ (9:ℕ) * j -
    38 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    22 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    202 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    14 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w * O ^ (10:ℕ))) +
    ((15 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j -
    84 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    162 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    420 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j -
    189 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w * O ^ (11:ℕ) * j) +
    (-27 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    12 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    266 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    460 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    209 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w * O ^ (12:ℕ) +
    9 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (3:ℕ) * j))) +
    (((-45 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j +
    2 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j +
    222 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j -
    315 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j +
    127 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w * O ^ (13:ℕ) * j) +
    (-7 * d ^ (2:ℕ) * c * σ * w ^ (11:ℕ) * O ^ (4:ℕ) +
    23 * d ^ (2:ℕ) * c * σ * w ^ (9:ℕ) * O ^ (6:ℕ) + 14 * d ^ (2:ℕ) * c * σ * w ^ (7:ℕ) * O ^ (8:ℕ)
    - 110 * d ^ (2:ℕ) * c * σ * w ^ (5:ℕ) * O ^ (10:ℕ) +
    121 * d ^ (2:ℕ) * c * σ * w ^ (3:ℕ) * O ^ (12:ℕ) - 41 * d ^ (2:ℕ) * c * σ * w * O ^ (14:ℕ))) +
    ((2 * d ^ (2:ℕ) * c * w ^ (13:ℕ) * O ^ (3:ℕ) * j -
    10 * d ^ (2:ℕ) * c * w ^ (11:ℕ) * O ^ (5:ℕ) * j + 14 * d ^ (2:ℕ) * c * w ^ (9:ℕ) * O ^ (7:ℕ) * j
    + 4 * d ^ (2:ℕ) * c * w ^ (7:ℕ) * O ^ (9:ℕ) * j -
    26 * d ^ (2:ℕ) * c * w ^ (5:ℕ) * O ^ (11:ℕ) * j +
    22 * d ^ (2:ℕ) * c * w ^ (3:ℕ) * O ^ (13:ℕ) * j) + (-6 * d ^ (2:ℕ) * c * w * O ^ (15:ℕ) * j -
    2 * d ^ (2:ℕ) * σ ^ (12:ℕ) * w * O ^ (4:ℕ) - 6 * d ^ (2:ℕ) * σ ^ (11:ℕ) * w * O ^ (5:ℕ) * j -
    16 * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) + 6 * d ^ (2:ℕ) * σ ^ (10:ℕ) * w * O ^ (6:ℕ)
    - 60 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j)))) +
    ((((48 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w * O ^ (7:ℕ) * j -
    50 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    44 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) - 130 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w * O ^ (8:ℕ)
    - 180 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j) +
    (36 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    156 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w * O ^ (9:ℕ) * j -
    80 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    132 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    8 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    124 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w * O ^ (10:ℕ))) +
    ((-240 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j +
    36 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    180 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    24 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w * O ^ (11:ℕ) * j -
    70 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ)) +
    (192 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    148 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    384 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    114 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (12:ℕ) -
    150 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j +
    156 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j))) +
    (((300 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j -
    468 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j +
    162 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (13:ℕ) * j -
    32 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (4:ℕ) +
    134 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ)) +
    (-56 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    292 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) +
    376 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) -
    130 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (14:ℕ) - 36 * d ^ (2:ℕ) * σ * w ^ (11:ℕ) * O ^ (5:ℕ) * j +
    108 * d ^ (2:ℕ) * σ * w ^ (9:ℕ) * O ^ (7:ℕ) * j)) +
    ((-36 * d ^ (2:ℕ) * σ * w ^ (7:ℕ) * O ^ (9:ℕ) * j -
    180 * d ^ (2:ℕ) * σ * w ^ (5:ℕ) * O ^ (11:ℕ) * j +
    216 * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (13:ℕ) * j - 72 * d ^ (2:ℕ) * σ * w * O ^ (15:ℕ) * j -
    6 * d ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (4:ℕ) + 36 * d ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ)) +
    (-66 * d ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) + 24 * d ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) +
    54 * d ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) - 60 * d ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) +
    18 * d ^ (2:ℕ) * w * O ^ (16:ℕ) - d * c * σ ^ (12:ℕ) * w * O ^ (4:ℕ))))))) +
    ((((((-2 * d * c * σ ^ (11:ℕ) * w * O ^ (5:ℕ) * j -
    8 * d * c * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) + 4 * d * c * σ ^ (10:ℕ) * w * O ^ (6:ℕ) -
    22 * d * c * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j + 46 * d * c * σ ^ (9:ℕ) * w * O ^ (7:ℕ) * j)
    + (-25 * d * c * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    26 * d * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) - 109 * d * c * σ ^ (8:ℕ) * w * O ^ (8:ℕ) -
    68 * d * c * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    88 * d * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    156 * d * c * σ ^ (7:ℕ) * w * O ^ (9:ℕ) * j)) +
    ((-40 * d * c * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    72 * d * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) + 8 * d * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    200 * d * c * σ ^ (6:ℕ) * w * O ^ (10:ℕ) - 92 * d * c * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j) +
    (76 * d * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    276 * d * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    76 * d * c * σ ^ (5:ℕ) * w * O ^ (11:ℕ) * j - 35 * d * c * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    100 * d * c * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    118 * d * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)))) +
    (((-460 * d * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) + 181 * d * c * σ ^ (4:ℕ) * w * O ^ (12:ℕ)
    - 58 * d * c * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j +
    72 * d * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j +
    220 * d * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j) +
    (-472 * d * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j +
    238 * d * c * σ ^ (3:ℕ) * w * O ^ (13:ℕ) * j - 16 * d * c * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (4:ℕ) +
    68 * d * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) - 32 * d * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ)
    - 200 * d * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ))) +
    ((304 * d * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) - 124 * d * c * σ ^ (2:ℕ) * w * O ^ (14:ℕ) -
    14 * d * c * σ * w ^ (11:ℕ) * O ^ (5:ℕ) * j + 38 * d * c * σ * w ^ (9:ℕ) * O ^ (7:ℕ) * j +
    12 * d * c * σ * w ^ (7:ℕ) * O ^ (9:ℕ) * j) + (-124 * d * c * σ * w ^ (5:ℕ) * O ^ (11:ℕ) * j +
    130 * d * c * σ * w ^ (3:ℕ) * O ^ (13:ℕ) * j - 42 * d * c * σ * w * O ^ (15:ℕ) * j -
    3 * d * c * w ^ (13:ℕ) * O ^ (4:ℕ) + 18 * d * c * w ^ (11:ℕ) * O ^ (6:ℕ) -
    33 * d * c * w ^ (9:ℕ) * O ^ (8:ℕ))))) + ((((12 * d * c * w ^ (7:ℕ) * O ^ (10:ℕ) +
    27 * d * c * w ^ (5:ℕ) * O ^ (12:ℕ) - 30 * d * c * w ^ (3:ℕ) * O ^ (14:ℕ) +
    9 * d * c * w * O ^ (16:ℕ) + 2 * d * σ ^ (11:ℕ) * w * O ^ (6:ℕ)) +
    (-6 * d * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j + 26 * d * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    14 * d * σ ^ (9:ℕ) * w * O ^ (8:ℕ) - 30 * d * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    66 * d * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j - 84 * d * σ ^ (8:ℕ) * w * O ^ (9:ℕ) * j)) +
    ((84 * d * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) - 20 * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    312 * d * σ ^ (7:ℕ) * w * O ^ (10:ℕ) - 60 * d * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j +
    228 * d * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j) +
    (132 * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j + 300 * d * σ ^ (6:ℕ) * w * O ^ (11:ℕ) * j +
    116 * d * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) - 160 * d * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    388 * d * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) + 32 * d * σ ^ (5:ℕ) * w * O ^ (12:ℕ)))) +
    (((-60 * d * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j +
    288 * d * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j + 24 * d * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j
    - 528 * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j + 276 * d * σ ^ (4:ℕ) * w * O ^ (13:ℕ) * j) +
    (74 * d * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) - 204 * d * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    16 * d * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) + 396 * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) -
    250 * d * σ ^ (3:ℕ) * w * O ^ (14:ℕ) - 30 * d * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (5:ℕ) * j)) +
    ((156 * d * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) * j -
    252 * d * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) * j +
    48 * d * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) * j +
    186 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) * j - 108 * d * σ ^ (2:ℕ) * w * O ^ (15:ℕ) * j +
    18 * d * σ * w ^ (11:ℕ) * O ^ (6:ℕ)) + (-78 * d * σ * w ^ (9:ℕ) * O ^ (8:ℕ) +
    108 * d * σ * w ^ (7:ℕ) * O ^ (10:ℕ) - 36 * d * σ * w ^ (5:ℕ) * O ^ (12:ℕ) -
    30 * d * σ * w ^ (3:ℕ) * O ^ (14:ℕ) + 18 * d * σ * w * O ^ (16:ℕ) -
    6 * d * w ^ (13:ℕ) * O ^ (5:ℕ) * j))))) + (((((30 * d * w ^ (11:ℕ) * O ^ (7:ℕ) * j -
    60 * d * w ^ (9:ℕ) * O ^ (9:ℕ) * j + 60 * d * w ^ (7:ℕ) * O ^ (11:ℕ) * j -
    30 * d * w ^ (5:ℕ) * O ^ (13:ℕ) * j + 6 * d * w ^ (3:ℕ) * O ^ (15:ℕ) * j) +
    (2 * c * σ ^ (11:ℕ) * w * O ^ (6:ℕ) + 8 * c * σ ^ (10:ℕ) * w * O ^ (7:ℕ) * j +
    14 * c * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) - 10 * c * σ ^ (9:ℕ) * w * O ^ (8:ℕ) +
    44 * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j - 28 * c * σ ^ (8:ℕ) * w * O ^ (9:ℕ) * j)) +
    ((36 * c * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) - 12 * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    64 * c * σ ^ (7:ℕ) * w * O ^ (10:ℕ) + 84 * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    32 * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j) + (52 * c * σ ^ (6:ℕ) * w * O ^ (11:ℕ) * j +
    44 * c * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) - 24 * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    60 * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) - 8 * c * σ ^ (5:ℕ) * w * O ^ (12:ℕ) +
    68 * c * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j))) +
    (((36 * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j -
    132 * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j + 28 * c * σ ^ (4:ℕ) * w * O ^ (13:ℕ) * j +
    26 * c * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) - 52 * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ)) +
    (-88 * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) + 180 * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) -
    66 * c * σ ^ (3:ℕ) * w * O ^ (14:ℕ) + 20 * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) * j -
    24 * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) * j -
    72 * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) * j)) +
    ((136 * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) * j - 60 * c * σ ^ (2:ℕ) * w * O ^ (15:ℕ) * j +
    6 * c * σ * w ^ (11:ℕ) * O ^ (6:ℕ) - 30 * c * σ * w ^ (9:ℕ) * O ^ (8:ℕ) +
    36 * c * σ * w ^ (7:ℕ) * O ^ (10:ℕ) + 12 * c * σ * w ^ (5:ℕ) * O ^ (12:ℕ)) +
    (-42 * c * σ * w ^ (3:ℕ) * O ^ (14:ℕ) + 18 * c * σ * w * O ^ (16:ℕ) - σ ^ (12:ℕ) * w * O ^ (6:ℕ)
    - 6 * σ ^ (11:ℕ) * w * O ^ (7:ℕ) * j - 8 * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    8 * σ ^ (10:ℕ) * w * O ^ (8:ℕ))))) + ((((-18 * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    10 * σ ^ (9:ℕ) * w * O ^ (9:ℕ) * j - 25 * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    14 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) + 35 * σ ^ (8:ℕ) * w * O ^ (10:ℕ)) +
    (-12 * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j - 48 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    76 * σ ^ (7:ℕ) * w * O ^ (11:ℕ) * j - 40 * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) -
    72 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) - 48 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ))) +
    ((-128 * σ ^ (6:ℕ) * w * O ^ (12:ℕ) + 12 * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j -
    108 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j - 188 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j -
    52 * σ ^ (5:ℕ) * w * O ^ (13:ℕ) * j) + (-35 * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) -
    52 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) + 54 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) +
    252 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) - 123 * σ ^ (4:ℕ) * w * O ^ (14:ℕ) +
    18 * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) * j))) + (((-112 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) * j
    + 68 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) * j + 176 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) * j -
    150 * σ ^ (3:ℕ) * w * O ^ (15:ℕ) * j - 16 * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ)) +
    (16 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) + 104 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) -
    152 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) + 8 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) +
    40 * σ ^ (2:ℕ) * w * O ^ (16:ℕ) + 6 * σ * w ^ (11:ℕ) * O ^ (7:ℕ) * j)) +
    ((-42 * σ * w ^ (9:ℕ) * O ^ (9:ℕ) * j + 108 * σ * w ^ (7:ℕ) * O ^ (11:ℕ) * j -
    132 * σ * w ^ (5:ℕ) * O ^ (13:ℕ) * j + 78 * σ * w ^ (3:ℕ) * O ^ (15:ℕ) * j -
    18 * σ * w * O ^ (17:ℕ) * j - 3 * w ^ (13:ℕ) * O ^ (6:ℕ)) + (18 * w ^ (11:ℕ) * O ^ (8:ℕ) -
    33 * w ^ (9:ℕ) * O ^ (10:ℕ) + 12 * w ^ (7:ℕ) * O ^ (12:ℕ) + 27 * w ^ (5:ℕ) * O ^ (14:ℕ) -
    30 * w ^ (3:ℕ) * O ^ (16:ℕ) + 9 * w * O ^ (18:ℕ)))))))) * h1 +
    (((((((-d ^ (3:ℕ) * c * σ ^ (12:ℕ) * w * O * j + 3 * d ^ (3:ℕ) * c * σ ^ (11:ℕ) * w * O ^ (2:ℕ)
    - 3 * d ^ (3:ℕ) * c * σ ^ (10:ℕ) * w ^ (3:ℕ) * O * j -
    5 * d ^ (3:ℕ) * c * σ ^ (10:ℕ) * w * O ^ (3:ℕ) * j +
    11 * d ^ (3:ℕ) * c * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    25 * d ^ (3:ℕ) * c * σ ^ (9:ℕ) * w * O ^ (4:ℕ)) +
    (-2 * d ^ (3:ℕ) * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    44 * d ^ (3:ℕ) * c * σ ^ (8:ℕ) * w * O ^ (5:ℕ) * j +
    14 * d ^ (3:ℕ) * c * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    20 * d ^ (3:ℕ) * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    54 * d ^ (3:ℕ) * c * σ ^ (7:ℕ) * w * O ^ (6:ℕ) +
    10 * d ^ (3:ℕ) * c * σ ^ (6:ℕ) * w ^ (7:ℕ) * O * j)) +
    ((14 * d ^ (3:ℕ) * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    14 * d ^ (3:ℕ) * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    38 * d ^ (3:ℕ) * c * σ ^ (6:ℕ) * w * O ^ (7:ℕ) * j +
    6 * d ^ (3:ℕ) * c * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) -
    42 * d ^ (3:ℕ) * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    38 * d ^ (3:ℕ) * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ)) +
    (-2 * d ^ (3:ℕ) * c * σ ^ (5:ℕ) * w * O ^ (8:ℕ) +
    15 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w ^ (9:ℕ) * O * j +
    4 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j -
    90 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    108 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    37 * d ^ (3:ℕ) * c * σ ^ (4:ℕ) * w * O ^ (9:ℕ) * j))) +
    (((-d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) -
    44 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    142 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    148 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    51 * d ^ (3:ℕ) * c * σ ^ (3:ℕ) * w * O ^ (10:ℕ) +
    9 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (11:ℕ) * O * j) +
    (-17 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j -
    46 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j +
    150 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    139 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    43 * d ^ (3:ℕ) * c * σ ^ (2:ℕ) * w * O ^ (11:ℕ) * j -
    d ^ (3:ℕ) * c * σ * w ^ (11:ℕ) * O ^ (2:ℕ))) + ((-7 * d ^ (3:ℕ) * c * σ * w ^ (9:ℕ) * O ^ (4:ℕ)
    + 50 * d ^ (3:ℕ) * c * σ * w ^ (7:ℕ) * O ^ (6:ℕ) -
    98 * d ^ (3:ℕ) * c * σ * w ^ (5:ℕ) * O ^ (8:ℕ) + 79 * d ^ (3:ℕ) * c * σ * w ^ (3:ℕ) * O ^ (10:ℕ)
    - 23 * d ^ (3:ℕ) * c * σ * w * O ^ (12:ℕ) + 2 * d ^ (3:ℕ) * c * w ^ (13:ℕ) * O * j) +
    (-10 * d ^ (3:ℕ) * c * w ^ (11:ℕ) * O ^ (3:ℕ) * j +
    14 * d ^ (3:ℕ) * c * w ^ (9:ℕ) * O ^ (5:ℕ) * j + 4 * d ^ (3:ℕ) * c * w ^ (7:ℕ) * O ^ (7:ℕ) * j -
    26 * d ^ (3:ℕ) * c * w ^ (5:ℕ) * O ^ (9:ℕ) * j + 22 * d ^ (3:ℕ) * c * w ^ (3:ℕ) * O ^ (11:ℕ) * j
    - 6 * d ^ (3:ℕ) * c * w * O ^ (13:ℕ) * j)))) + ((((-d ^ (3:ℕ) * σ ^ (12:ℕ) * w * O ^ (2:ℕ) -
    4 * d ^ (3:ℕ) * σ ^ (11:ℕ) * w * O ^ (3:ℕ) * j -
    8 * d ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) + 6 * d ^ (3:ℕ) * σ ^ (10:ℕ) * w * O ^ (4:ℕ)
    - 26 * d ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    18 * d ^ (3:ℕ) * σ ^ (9:ℕ) * w * O ^ (5:ℕ) * j) +
    (-25 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    18 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) - 37 * d ^ (3:ℕ) * σ ^ (8:ℕ) * w * O ^ (6:ℕ)
    - 64 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    20 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    40 * d ^ (3:ℕ) * σ ^ (7:ℕ) * w * O ^ (7:ℕ) * j)) +
    ((-40 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    36 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    8 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) + 36 * d ^ (3:ℕ) * σ ^ (6:ℕ) * w * O ^ (8:ℕ) -
    76 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    8 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j) +
    (56 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j +
    12 * d ^ (3:ℕ) * σ ^ (5:ℕ) * w * O ^ (9:ℕ) * j -
    35 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) +
    60 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    62 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    116 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)))) +
    (((29 * d ^ (3:ℕ) * σ ^ (4:ℕ) * w * O ^ (10:ℕ) -
    44 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j +
    28 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j +
    120 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    148 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    44 * d ^ (3:ℕ) * σ ^ (3:ℕ) * w * O ^ (11:ℕ) * j) +
    (-16 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (2:ℕ) +
    54 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) -
    140 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    144 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    42 * d ^ (3:ℕ) * σ ^ (2:ℕ) * w * O ^ (12:ℕ) - 10 * d ^ (3:ℕ) * σ * w ^ (11:ℕ) * O ^ (3:ℕ) * j))
    + ((22 * d ^ (3:ℕ) * σ * w ^ (9:ℕ) * O ^ (5:ℕ) * j +
    24 * d ^ (3:ℕ) * σ * w ^ (7:ℕ) * O ^ (7:ℕ) * j - 104 * d ^ (3:ℕ) * σ * w ^ (5:ℕ) * O ^ (9:ℕ) * j
    + 98 * d ^ (3:ℕ) * σ * w ^ (3:ℕ) * O ^ (11:ℕ) * j - 30 * d ^ (3:ℕ) * σ * w * O ^ (13:ℕ) * j -
    3 * d ^ (3:ℕ) * w ^ (13:ℕ) * O ^ (2:ℕ)) + (18 * d ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (4:ℕ) -
    33 * d ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) + 12 * d ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) +
    27 * d ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) - 30 * d ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) +
    9 * d ^ (3:ℕ) * w * O ^ (14:ℕ)))))) + (((((-2 * d ^ (2:ℕ) * c * g * σ ^ (10:ℕ) * w ^ (2:ℕ) -
    11 * d ^ (2:ℕ) * c * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O * j -
    7 * d ^ (2:ℕ) * c * g * σ ^ (8:ℕ) * w ^ (4:ℕ) +
    21 * d ^ (2:ℕ) * c * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    36 * d ^ (2:ℕ) * c * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O * j +
    24 * d ^ (2:ℕ) * c * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j) +
    (-8 * d ^ (2:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (6:ℕ) +
    58 * d ^ (2:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    20 * d ^ (2:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    42 * d ^ (2:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O * j +
    56 * d ^ (2:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    2 * d ^ (2:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j)) +
    ((-2 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (8:ℕ) +
    52 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    32 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    18 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    20 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O * j +
    40 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j) +
    (4 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    24 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    2 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (10:ℕ) +
    14 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    12 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    26 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ)))) +
    (((22 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    3 * d ^ (2:ℕ) * c * g * σ * w ^ (10:ℕ) * O * j +
    8 * d ^ (2:ℕ) * c * g * σ * w ^ (8:ℕ) * O ^ (3:ℕ) * j +
    6 * d ^ (2:ℕ) * c * g * σ * w ^ (6:ℕ) * O ^ (5:ℕ) * j -
    24 * d ^ (2:ℕ) * c * g * σ * w ^ (4:ℕ) * O ^ (7:ℕ) * j +
    13 * d ^ (2:ℕ) * c * g * σ * w ^ (2:ℕ) * O ^ (9:ℕ) * j) + (d ^ (2:ℕ) * c * g * w ^ (12:ℕ) -
    d ^ (2:ℕ) * c * g * w ^ (10:ℕ) * O ^ (2:ℕ) - 4 * d ^ (2:ℕ) * c * g * w ^ (6:ℕ) * O ^ (6:ℕ) +
    7 * d ^ (2:ℕ) * c * g * w ^ (4:ℕ) * O ^ (8:ℕ) - 3 * d ^ (2:ℕ) * c * g * w ^ (2:ℕ) * O ^ (10:ℕ) -
    d ^ (2:ℕ) * c * σ ^ (12:ℕ) * w * O ^ (2:ℕ))) +
    ((-8 * d ^ (2:ℕ) * c * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    6 * d ^ (2:ℕ) * c * σ ^ (10:ℕ) * w * O ^ (4:ℕ) -
    18 * d ^ (2:ℕ) * c * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    42 * d ^ (2:ℕ) * c * σ ^ (9:ℕ) * w * O ^ (5:ℕ) * j -
    25 * d ^ (2:ℕ) * c * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) -
    14 * d ^ (2:ℕ) * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ)) +
    (-149 * d ^ (2:ℕ) * c * σ ^ (8:ℕ) * w * O ^ (6:ℕ) -
    72 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    12 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    192 * d ^ (2:ℕ) * c * σ ^ (7:ℕ) * w * O ^ (7:ℕ) * j -
    40 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    12 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ))))) +
    ((((-8 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    140 * d ^ (2:ℕ) * c * σ ^ (6:ℕ) * w * O ^ (8:ℕ) -
    108 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j -
    48 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    144 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j +
    12 * d ^ (2:ℕ) * c * σ ^ (5:ℕ) * w * O ^ (9:ℕ) * j) +
    (-35 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) +
    60 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    206 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    372 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    141 * d ^ (2:ℕ) * c * σ ^ (4:ℕ) * w * O ^ (10:ℕ) -
    72 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j)) +
    ((36 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j +
    336 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    492 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    192 * d ^ (2:ℕ) * c * σ ^ (3:ℕ) * w * O ^ (11:ℕ) * j -
    16 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (2:ℕ) +
    58 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ)) +
    (32 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) -
    308 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    368 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    134 * d ^ (2:ℕ) * c * σ ^ (2:ℕ) * w * O ^ (12:ℕ) -
    18 * d ^ (2:ℕ) * c * σ * w ^ (11:ℕ) * O ^ (3:ℕ) * j +
    54 * d ^ (2:ℕ) * c * σ * w ^ (9:ℕ) * O ^ (5:ℕ) * j))) +
    (((-144 * d ^ (2:ℕ) * c * σ * w ^ (5:ℕ) * O ^ (9:ℕ) * j +
    162 * d ^ (2:ℕ) * c * σ * w ^ (3:ℕ) * O ^ (11:ℕ) * j -
    54 * d ^ (2:ℕ) * c * σ * w * O ^ (13:ℕ) * j - 3 * d ^ (2:ℕ) * c * w ^ (13:ℕ) * O ^ (2:ℕ) +
    18 * d ^ (2:ℕ) * c * w ^ (11:ℕ) * O ^ (4:ℕ) - 33 * d ^ (2:ℕ) * c * w ^ (9:ℕ) * O ^ (6:ℕ)) +
    (12 * d ^ (2:ℕ) * c * w ^ (7:ℕ) * O ^ (8:ℕ) + 27 * d ^ (2:ℕ) * c * w ^ (5:ℕ) * O ^ (10:ℕ) -
    30 * d ^ (2:ℕ) * c * w ^ (3:ℕ) * O ^ (12:ℕ) + 9 * d ^ (2:ℕ) * c * w * O ^ (14:ℕ) +
    d ^ (2:ℕ) * σ ^ (12:ℕ) * w * O ^ (3:ℕ) * j + d ^ (2:ℕ) * σ ^ (11:ℕ) * w * O ^ (4:ℕ))) +
    ((-3 * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    21 * d ^ (2:ℕ) * σ ^ (10:ℕ) * w * O ^ (5:ℕ) * j +
    29 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) - 45 * d ^ (2:ℕ) * σ ^ (9:ℕ) * w * O ^ (6:ℕ)
    - 30 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    96 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j) +
    (-100 * d ^ (2:ℕ) * σ ^ (8:ℕ) * w * O ^ (7:ℕ) * j +
    106 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    44 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) + 182 * d ^ (2:ℕ) * σ ^ (7:ℕ) * w * O ^ (8:ℕ)
    - 70 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    202 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    62 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j)))))) +
    ((((((142 * d ^ (2:ℕ) * σ ^ (6:ℕ) * w * O ^ (9:ℕ) * j +
    154 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    54 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    182 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    14 * d ^ (2:ℕ) * σ ^ (5:ℕ) * w * O ^ (10:ℕ) -
    75 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j) +
    (240 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j +
    126 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    384 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    93 * d ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (11:ℕ) * j +
    101 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) -
    156 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ))) +
    ((-270 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    508 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    183 * d ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (12:ℕ) -
    39 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (3:ℕ) * j +
    153 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j -
    110 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j) +
    (-246 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j +
    405 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j -
    163 * d ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (13:ℕ) * j + 25 * d ^ (2:ℕ) * σ * w ^ (11:ℕ) * O ^ (4:ℕ) -
    101 * d ^ (2:ℕ) * σ * w ^ (9:ℕ) * O ^ (6:ℕ) + 94 * d ^ (2:ℕ) * σ * w ^ (7:ℕ) * O ^ (8:ℕ)))) +
    (((74 * d ^ (2:ℕ) * σ * w ^ (5:ℕ) * O ^ (10:ℕ) - 151 * d ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (12:ℕ) +
    59 * d ^ (2:ℕ) * σ * w * O ^ (14:ℕ) - 8 * d ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (3:ℕ) * j +
    40 * d ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (5:ℕ) * j - 74 * d ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) * j) +
    (56 * d ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) * j - 4 * d ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) * j -
    16 * d ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) * j + 6 * d ^ (2:ℕ) * w * O ^ (15:ℕ) * j +
    8 * d * c * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) +
    44 * d * c * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j)) +
    ((20 * d * c * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    76 * d * c * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    100 * d * c * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    52 * d * c * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    12 * d * c * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    136 * d * c * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ)) +
    (4 * d * c * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    68 * d * c * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    72 * d * c * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    44 * d * c * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j -
    4 * d * c * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    60 * d * c * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ))))) +
    ((((-12 * d * c * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    76 * d * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    12 * d * c * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    20 * d * c * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j -
    44 * d * c * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j +
    52 * d * c * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j) +
    (-4 * d * c * g * σ * w ^ (10:ℕ) * O ^ (2:ℕ) + 16 * d * c * g * σ * w ^ (4:ℕ) * O ^ (8:ℕ) -
    12 * d * c * g * σ * w ^ (2:ℕ) * O ^ (10:ℕ) + 4 * d * c * σ ^ (11:ℕ) * w * O ^ (4:ℕ) +
    12 * d * c * σ ^ (10:ℕ) * w * O ^ (5:ℕ) * j + 28 * d * c * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ))) +
    ((-8 * d * c * σ ^ (9:ℕ) * w * O ^ (6:ℕ) + 84 * d * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    84 * d * c * σ ^ (8:ℕ) * w * O ^ (7:ℕ) * j + 72 * d * c * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    4 * d * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) + 252 * d * c * σ ^ (7:ℕ) * w * O ^ (8:ℕ)) +
    (180 * d * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    96 * d * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j + 228 * d * c * σ ^ (6:ℕ) * w * O ^ (9:ℕ) * j
    + 88 * d * c * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    44 * d * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    224 * d * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)))) + (((4 * d * c * σ ^ (5:ℕ) * w * O ^ (10:ℕ) +
    156 * d * c * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j +
    108 * d * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    444 * d * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j +
    180 * d * c * σ ^ (4:ℕ) * w * O ^ (11:ℕ) * j + 52 * d * c * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ)) +
    (-108 * d * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) -
    212 * d * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    492 * d * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) - 224 * d * c * σ ^ (3:ℕ) * w * O ^ (12:ℕ) +
    48 * d * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j -
    72 * d * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j)) +
    ((-144 * d * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j +
    312 * d * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j -
    144 * d * c * σ ^ (2:ℕ) * w * O ^ (13:ℕ) * j + 12 * d * c * σ * w ^ (11:ℕ) * O ^ (4:ℕ) -
    60 * d * c * σ * w ^ (9:ℕ) * O ^ (6:ℕ) + 72 * d * c * σ * w ^ (7:ℕ) * O ^ (8:ℕ)) +
    (24 * d * c * σ * w ^ (5:ℕ) * O ^ (10:ℕ) - 84 * d * c * σ * w ^ (3:ℕ) * O ^ (12:ℕ) +
    36 * d * c * σ * w * O ^ (14:ℕ) - 4 * d * σ ^ (11:ℕ) * w * O ^ (5:ℕ) * j +
    8 * d * σ ^ (10:ℕ) * w * O ^ (6:ℕ) + 16 * d * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j))))) +
    (((((-40 * d * σ ^ (9:ℕ) * w * O ^ (7:ℕ) * j - 40 * d * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    128 * d * σ ^ (8:ℕ) * w * O ^ (8:ℕ) + 104 * d * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j -
    64 * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j + 192 * d * σ ^ (7:ℕ) * w * O ^ (9:ℕ) * j) +
    (-168 * d * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) - 64 * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    216 * d * σ ^ (6:ℕ) * w * O ^ (10:ℕ) + 176 * d * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    136 * d * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    312 * d * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j)) + ((-64 * d * σ ^ (5:ℕ) * w * O ^ (11:ℕ) * j -
    184 * d * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) - 32 * d * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    520 * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) - 208 * d * σ ^ (4:ℕ) * w * O ^ (12:ℕ) +
    124 * d * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j) +
    (-240 * d * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j -
    112 * d * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j +
    496 * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j - 268 * d * σ ^ (3:ℕ) * w * O ^ (13:ℕ) * j -
    64 * d * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) + 160 * d * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ)))) +
    (((-224 * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) + 128 * d * σ ^ (2:ℕ) * w * O ^ (14:ℕ) +
    32 * d * σ * w ^ (11:ℕ) * O ^ (5:ℕ) * j - 128 * d * σ * w ^ (9:ℕ) * O ^ (7:ℕ) * j +
    168 * d * σ * w ^ (7:ℕ) * O ^ (9:ℕ) * j - 56 * d * σ * w ^ (5:ℕ) * O ^ (11:ℕ) * j) +
    (-40 * d * σ * w ^ (3:ℕ) * O ^ (13:ℕ) * j + 24 * d * σ * w * O ^ (15:ℕ) * j -
    8 * c * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    44 * c * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    12 * c * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    68 * c * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ))) +
    ((-56 * c * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    8 * c * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    56 * c * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) + 64 * c * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)
    - 12 * c * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    8 * c * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j) +
    (52 * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    4 * c * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) + 4 * c * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    4 * c * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) - 12 * c * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ)
    - 4 * c * σ ^ (10:ℕ) * w * O ^ (6:ℕ))))) + ((((-16 * c * σ ^ (9:ℕ) * w * O ^ (7:ℕ) * j -
    24 * c * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) + 16 * c * σ ^ (8:ℕ) * w * O ^ (8:ℕ) -
    72 * c * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j + 40 * c * σ ^ (7:ℕ) * w * O ^ (9:ℕ) * j -
    48 * c * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)) + (-16 * c * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    112 * c * σ ^ (6:ℕ) * w * O ^ (10:ℕ) - 96 * c * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    176 * c * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j - 64 * c * σ ^ (5:ℕ) * w * O ^ (11:ℕ) * j -
    40 * c * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ))) + ((16 * c * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    216 * c * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) - 96 * c * σ ^ (4:ℕ) * w * O ^ (12:ℕ) -
    40 * c * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j + 8 * c * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j +
    152 * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j) + (-120 * c * σ ^ (3:ℕ) * w * O ^ (13:ℕ) * j -
    12 * c * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) + 48 * c * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    24 * c * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) - 48 * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) +
    36 * c * σ ^ (2:ℕ) * w * O ^ (14:ℕ)))) + (((4 * σ ^ (10:ℕ) * w * O ^ (7:ℕ) * j -
    12 * σ ^ (9:ℕ) * w * O ^ (8:ℕ) - 20 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j +
    28 * σ ^ (8:ℕ) * w * O ^ (9:ℕ) * j + 28 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    124 * σ ^ (7:ℕ) * w * O ^ (10:ℕ)) + (-84 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j -
    56 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j - 124 * σ ^ (6:ℕ) * w * O ^ (11:ℕ) * j +
    92 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) + 200 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    20 * σ ^ (5:ℕ) * w * O ^ (12:ℕ))) + ((-92 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j +
    12 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j + 204 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j -
    124 * σ ^ (4:ℕ) * w * O ^ (13:ℕ) * j + 52 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    60 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ)) + (-84 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) +
    92 * σ ^ (3:ℕ) * w * O ^ (14:ℕ) - 32 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) * j +
    96 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) * j - 72 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) * j -
    16 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) * j + 24 * σ ^ (2:ℕ) * w * O ^ (15:ℕ) * j))))))) * h2 +
    ((((((-6 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) +
    16 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    28 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    10 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    48 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    100 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    52 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ)) +
    (32 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    112 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    48 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    212 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    164 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j -
    48 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) +
    116 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    108 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ))) +
    ((-176 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    16 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    124 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    200 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    92 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j -
    22 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) +
    96 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ)) +
    (-40 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    120 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    86 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    12 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (5:ℕ) * j +
    36 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j -
    36 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j +
    12 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j -
    4 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (12:ℕ) * O ^ (2:ℕ)))) +
    (((22 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (10:ℕ) * O ^ (4:ℕ) -
    36 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (8:ℕ) * O ^ (6:ℕ) +
    16 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (6:ℕ) * O ^ (8:ℕ) +
    8 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (4:ℕ) * O ^ (10:ℕ) -
    6 * d ^ (3:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (2:ℕ) * O ^ (12:ℕ) -
    10 * d ^ (3:ℕ) * c * g * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    16 * d ^ (3:ℕ) * c * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j) +
    (8 * d ^ (3:ℕ) * c * g * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    94 * d ^ (3:ℕ) * c * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    48 * d ^ (3:ℕ) * c * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    100 * d ^ (3:ℕ) * c * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    84 * d ^ (3:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    68 * d ^ (3:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    176 * d ^ (3:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    48 * d ^ (3:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j)) +
    ((212 * d ^ (3:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    164 * d ^ (3:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    104 * d ^ (3:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) -
    152 * d ^ (3:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    56 * d ^ (3:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    104 * d ^ (3:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    16 * d ^ (3:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (5:ℕ) * j) +
    (124 * d ^ (3:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j -
    200 * d ^ (3:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j +
    92 * d ^ (3:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j +
    38 * d ^ (3:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) -
    132 * d ^ (3:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) +
    144 * d ^ (3:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) -
    44 * d ^ (3:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    6 * d ^ (3:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ))))) +
    ((((12 * d ^ (3:ℕ) * c * g * σ * w ^ (8:ℕ) * O ^ (7:ℕ) * j -
    36 * d ^ (3:ℕ) * c * g * σ * w ^ (6:ℕ) * O ^ (9:ℕ) * j +
    36 * d ^ (3:ℕ) * c * g * σ * w ^ (4:ℕ) * O ^ (11:ℕ) * j -
    12 * d ^ (3:ℕ) * c * g * σ * w ^ (2:ℕ) * O ^ (13:ℕ) * j -
    6 * d ^ (3:ℕ) * c * g * w ^ (10:ℕ) * O ^ (6:ℕ) + 24 * d ^ (3:ℕ) * c * g * w ^ (8:ℕ) * O ^ (8:ℕ)
    - 36 * d ^ (3:ℕ) * c * g * w ^ (6:ℕ) * O ^ (10:ℕ)) +
    (24 * d ^ (3:ℕ) * c * g * w ^ (4:ℕ) * O ^ (12:ℕ) -
    6 * d ^ (3:ℕ) * c * g * w ^ (2:ℕ) * O ^ (14:ℕ) +
    20 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    52 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) -
    94 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    44 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) -
    178 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    134 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ))) +
    ((12 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) -
    90 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    144 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    66 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    6 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    18 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) -
    18 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)) +
    (6 * d ^ (2:ℕ) * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    14 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    80 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    96 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    158 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    176 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    436 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    204 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ)))) +
    (((-36 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    560 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    112 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    596 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    484 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    176 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) -
    392 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ)) +
    (-208 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    424 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    16 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (5:ℕ) * j +
    172 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j -
    296 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j +
    140 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j +
    54 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) -
    204 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ))) +
    ((216 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) -
    36 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    30 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    12 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (8:ℕ) * O ^ (7:ℕ) * j -
    36 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (6:ℕ) * O ^ (9:ℕ) * j +
    36 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (4:ℕ) * O ^ (11:ℕ) * j -
    12 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * σ * w ^ (2:ℕ) * O ^ (13:ℕ) * j) +
    (-6 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * w ^ (10:ℕ) * O ^ (6:ℕ) +
    24 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * w ^ (8:ℕ) * O ^ (8:ℕ) -
    36 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * w ^ (6:ℕ) * O ^ (10:ℕ) +
    24 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * w ^ (4:ℕ) * O ^ (12:ℕ) -
    6 * d ^ (2:ℕ) * c ^ (2:ℕ) * g * w ^ (2:ℕ) * O ^ (14:ℕ) +
    6 * d ^ (2:ℕ) * c * g * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    16 * d ^ (2:ℕ) * c * g * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    40 * d ^ (2:ℕ) * c * g * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ)))))) +
    (((((50 * d ^ (2:ℕ) * c * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    48 * d ^ (2:ℕ) * c * g * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    164 * d ^ (2:ℕ) * c * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    100 * d ^ (2:ℕ) * c * g * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    200 * d ^ (2:ℕ) * c * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    448 * d ^ (2:ℕ) * c * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    48 * d ^ (2:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j) +
    (340 * d ^ (2:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    500 * d ^ (2:ℕ) * c * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    120 * d ^ (2:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) -
    620 * d ^ (2:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    52 * d ^ (2:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    544 * d ^ (2:ℕ) * c * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    16 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (5:ℕ) * j +
    188 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j)) +
    ((-584 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j +
    412 * d ^ (2:ℕ) * c * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j +
    70 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) -
    440 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) +
    632 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) -
    128 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    134 * d ^ (2:ℕ) * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ)) +
    (12 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (7:ℕ) * j -
    84 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (9:ℕ) * j +
    132 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (11:ℕ) * j -
    60 * d ^ (2:ℕ) * c * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (13:ℕ) * j +
    16 * d ^ (2:ℕ) * c * g * σ * w ^ (12:ℕ) * O ^ (4:ℕ) -
    70 * d ^ (2:ℕ) * c * g * σ * w ^ (10:ℕ) * O ^ (6:ℕ) +
    132 * d ^ (2:ℕ) * c * g * σ * w ^ (8:ℕ) * O ^ (8:ℕ) -
    136 * d ^ (2:ℕ) * c * g * σ * w ^ (6:ℕ) * O ^ (10:ℕ)))) +
    (((76 * d ^ (2:ℕ) * c * g * σ * w ^ (4:ℕ) * O ^ (12:ℕ) -
    18 * d ^ (2:ℕ) * c * g * σ * w ^ (2:ℕ) * O ^ (14:ℕ) -
    80 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    128 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    296 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    48 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    288 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)) +
    (-240 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    24 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (7:ℕ) * O ^ (6:ℕ) -
    48 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (5:ℕ) * O ^ (8:ℕ) +
    24 * d * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (10:ℕ) +
    16 * d * c ^ (2:ℕ) * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    128 * d * c ^ (2:ℕ) * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j -
    136 * d * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    424 * d * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ))) +
    ((192 * d * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    608 * d * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j -
    320 * d * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    120 * d * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    664 * d * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    64 * d * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j -
    432 * d * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j) +
    (368 * d * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j -
    168 * d * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) +
    408 * d * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) -
    168 * d * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    72 * d * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    48 * d * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (9:ℕ) * j +
    96 * d * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (11:ℕ) * j -
    48 * d * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (13:ℕ) * j)))) +
    ((((24 * d * c ^ (2:ℕ) * g * σ * w ^ (8:ℕ) * O ^ (8:ℕ) -
    72 * d * c ^ (2:ℕ) * g * σ * w ^ (6:ℕ) * O ^ (10:ℕ) +
    72 * d * c ^ (2:ℕ) * g * σ * w ^ (4:ℕ) * O ^ (12:ℕ) -
    24 * d * c ^ (2:ℕ) * g * σ * w ^ (2:ℕ) * O ^ (14:ℕ) -
    24 * d * c * g * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    64 * d * c * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j -
    136 * d * c * g * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ)) +
    (-104 * d * c * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    128 * d * c * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    400 * d * c * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j -
    264 * d * c * g * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    552 * d * c * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    680 * d * c * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    64 * d * c * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j -
    448 * d * c * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j)) +
    ((592 * d * c * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j -
    216 * d * c * g * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) +
    872 * d * c * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) -
    360 * d * c * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    392 * d * c * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    48 * d * c * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (9:ℕ) * j +
    144 * d * c * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (11:ℕ) * j) +
    (-96 * d * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (13:ℕ) * j -
    64 * d * c * g * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) +
    216 * d * c * g * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) -
    240 * d * c * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) +
    88 * d * c * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    80 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    48 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    216 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)))) +
    (((-24 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    24 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    40 * c ^ (2:ℕ) * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    64 * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    112 * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    296 * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    64 * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j) +
    (272 * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j +
    152 * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) -
    176 * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    72 * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    48 * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (11:ℕ) * j -
    48 * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (13:ℕ) * j -
    24 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) +
    48 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ))) +
    ((-24 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) +
    24 * c * g * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    64 * c * g * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    112 * c * g * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    88 * c * g * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    64 * c * g * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j +
    272 * c * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j +
    152 * c * g * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ)) +
    (-416 * c * g * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    296 * c * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    48 * c * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (11:ℕ) * j -
    48 * c * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (13:ℕ) * j +
    64 * c * g * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) -
    152 * c * g * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) +
    64 * c * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    24 * c * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ))))))) * hj

@[tmio M, powerlib_domain] private theorem sl_C {d c σ w O j : ℂ}
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d)):
    (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) * slicePairing d c σ w O j =
      slicePairRe d σ w O + slicePairIm d σ w O * j := by
  simp only [slicePairing, slicePairRe, slicePairIm]
  linear_combination (-d * σ ^ (2:ℕ) * w - 4 * d * σ * w * O * j - d * w ^ (3:ℕ) +
    3 * d * w * O ^ (2:ℕ) - 2 * σ ^ (2:ℕ) * w * O * j + 6 * σ * w * O ^ (2:ℕ) -
    2 * w ^ (3:ℕ) * O * j + 4 * w * O ^ (3:ℕ) * j) * h1

@[tmio M, powerlib_domain] private theorem sl_X {d c g σ w O j : ℂ}
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d))
    (h2 : c * g * w = O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) * slChi d c g σ w O j =
      sliceShiftRe d σ w O + sliceShiftIm d σ w O * j := by
  simp only [slChi, sliceShiftRe, sliceShiftIm]
  linear_combination (2 * d * σ ^ (2:ℕ) * O * j - 6 * d * σ * O ^ (2:ℕ) + 2 * d * w ^ (2:ℕ) * O * j
    - 8 * d * O ^ (3:ℕ) * j - 3 * σ ^ (2:ℕ) * O ^ (2:ℕ) - 16 * σ * O ^ (3:ℕ) * j -
    3 * w ^ (2:ℕ) * O ^ (2:ℕ) + 15 * O ^ (4:ℕ)) * h1 + (d * σ ^ (2:ℕ) + d * w ^ (2:ℕ) -
    d * O ^ (2:ℕ) - 2 * σ * O ^ (2:ℕ)) * h2

@[tmio M, powerlib_domain] private theorem sl_chi_cubic {d c g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d))
    (h2 : c * g * w = O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    slChi d c g σ w O j = -3 * O ^ 2 * ((2 * O * j) ^ 3 + (c + d + 2 * σ) * (2 * O * j) ^ 2 +
      (σ ^ 2 + w ^ 2 + 2 * σ * (c + d) + c * d - O ^ 2) * (2 * O * j) +
      (2 * c * d * σ + (c + d) * (σ ^ 2 + w ^ 2) - (c + d + 2 * σ) * O ^ 2)) := by
  simp only [slChi]
  linear_combination (2 * O * j) * h1 + (1) * h2 + (12 * d * O ^ (4:ℕ) + 12 * c * O ^ (4:ℕ) +
    24 * σ * O ^ (4:ℕ) + 24 * O ^ (5:ℕ) * j) * hj

/-- The coefficients of `d^k` in the Bautin form of the zero-current slice
(`Line.VSMLPF.sliceBautin`), polynomials in `σ = R/L`, `w = ω₀` and the Hopf frequency `ω`. -/
def sliceBautinCoeff : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, σ, w, ω => (((-2 * σ ^ (17:ℕ) * ω ^ (6:ℕ) - 16 * σ ^ (15:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) -
        96 * σ ^ (15:ℕ) * ω ^ (8:ℕ) - 56 * σ ^ (13:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) -
        500 * σ ^ (13:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ)) + (-1108 * σ ^ (13:ℕ) * ω ^ (10:ℕ) -
        112 * σ ^ (11:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) - 1048 * σ ^ (11:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) -
        2696 * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) - 4728 * σ ^ (11:ℕ) * ω ^ (12:ℕ) -
        140 * σ ^ (9:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ))) + ((-1100 * σ ^ (9:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) -
        1516 * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) - 3900 * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) -
        7520 * σ ^ (9:ℕ) * ω ^ (14:ℕ) - 112 * σ ^ (7:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ)) +
        (-560 * σ ^ (7:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) + 528 * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) -
        2624 * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) - 2432 * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) -
        688 * σ ^ (7:ℕ) * ω ^ (16:ℕ) - 56 * σ ^ (5:ℕ) * w ^ (12:ℕ) * ω ^ (6:ℕ)))) +
        (((-76 * σ ^ (5:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) + 340 * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) -
        2248 * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) + 10016 * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) -
        11244 * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ)) + (7364 * σ ^ (5:ℕ) * ω ^ (18:ℕ) -
        16 * σ ^ (3:ℕ) * w ^ (14:ℕ) * ω ^ (6:ℕ) + 40 * σ ^ (3:ℕ) * w ^ (12:ℕ) * ω ^ (8:ℕ) -
        136 * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (10:ℕ) + 1176 * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ) -
        4288 * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ))) + ((9848 * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) -
        10984 * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (18:ℕ) + 4360 * σ ^ (3:ℕ) * ω ^ (20:ℕ) -
        2 * σ * w ^ (16:ℕ) * ω ^ (6:ℕ) + 12 * σ * w ^ (14:ℕ) * ω ^ (8:ℕ) -
        20 * σ * w ^ (12:ℕ) * ω ^ (10:ℕ)) + (-28 * σ * w ^ (10:ℕ) * ω ^ (12:ℕ) +
        256 * σ * w ^ (8:ℕ) * ω ^ (14:ℕ) - 652 * σ * w ^ (6:ℕ) * ω ^ (16:ℕ) +
        804 * σ * w ^ (4:ℕ) * ω ^ (18:ℕ) - 484 * σ * w ^ (2:ℕ) * ω ^ (20:ℕ) +
        114 * σ * ω ^ (22:ℕ))))
  | 1, σ, w, ω => (((σ ^ (18:ℕ) * ω ^ (4:ℕ) + 9 * σ ^ (16:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
        109 * σ ^ (16:ℕ) * ω ^ (6:ℕ) + 36 * σ ^ (14:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
        706 * σ ^ (14:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) + 1250 * σ ^ (14:ℕ) * ω ^ (8:ℕ)) +
        (84 * σ ^ (12:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) + 1930 * σ ^ (12:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
        4332 * σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) + 4246 * σ ^ (12:ℕ) * ω ^ (10:ℕ) +
        126 * σ ^ (10:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) + 2858 * σ ^ (10:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) +
        4550 * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ))) + ((8470 * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) +
        2580 * σ ^ (10:ℕ) * ω ^ (12:ℕ) + 126 * σ ^ (8:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) +
        2420 * σ ^ (8:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 16 * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) +
        10020 * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 5882 * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ)) +
        (-8352 * σ ^ (8:ℕ) * ω ^ (14:ℕ) + 84 * σ ^ (6:ℕ) * w ^ (12:ℕ) * ω ^ (4:ℕ) +
        1094 * σ ^ (6:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) - 2674 * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) +
        11788 * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 13136 * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) +
        8206 * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ)))) + (((-8434 * σ ^ (6:ℕ) * ω ^ (16:ℕ) +
        36 * σ ^ (4:ℕ) * w ^ (14:ℕ) * ω ^ (4:ℕ) + 166 * σ ^ (4:ℕ) * w ^ (12:ℕ) * ω ^ (6:ℕ) -
        1156 * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) + 5854 * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) -
        13476 * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ) + 13906 * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ)) +
        (-9340 * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 4010 * σ ^ (4:ℕ) * ω ^ (18:ℕ) +
        9 * σ ^ (2:ℕ) * w ^ (16:ℕ) * ω ^ (4:ℕ) - 50 * σ ^ (2:ℕ) * w ^ (14:ℕ) * ω ^ (6:ℕ) +
        138 * σ ^ (2:ℕ) * w ^ (12:ℕ) * ω ^ (8:ℕ) - 450 * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (10:ℕ) +
        3500 * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (12:ℕ))) + ((-13222 * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (14:ℕ)
        + 21894 * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (16:ℕ) - 16422 * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (18:ℕ) +
        4603 * σ ^ (2:ℕ) * ω ^ (20:ℕ) + w ^ (18:ℕ) * ω ^ (4:ℕ) - 17 * w ^ (16:ℕ) * ω ^ (6:ℕ) +
        104 * w ^ (14:ℕ) * ω ^ (8:ℕ)) + (-312 * w ^ (12:ℕ) * ω ^ (10:ℕ) +
        538 * w ^ (10:ℕ) * ω ^ (12:ℕ) - 586 * w ^ (8:ℕ) * ω ^ (14:ℕ) + 432 * w ^ (6:ℕ) * ω ^ (16:ℕ)
        - 224 * w ^ (4:ℕ) * ω ^ (18:ℕ) + 77 * w ^ (2:ℕ) * ω ^ (20:ℕ) - 13 * ω ^ (22:ℕ))))
  | 2, σ, w, ω => (((-52 * σ ^ (17:ℕ) * ω ^ (4:ℕ) - 392 * σ ^ (15:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) -
        548 * σ ^ (15:ℕ) * ω ^ (6:ℕ) - 1288 * σ ^ (13:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
        2404 * σ ^ (13:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ)) + (-1636 * σ ^ (13:ℕ) * ω ^ (8:ℕ) -
        2408 * σ ^ (11:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) - 3508 * σ ^ (11:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) -
        4608 * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) - 1868 * σ ^ (11:ℕ) * ω ^ (10:ℕ) -
        2800 * σ ^ (9:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ))) + ((-660 * σ ^ (9:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
        7764 * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 3484 * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) -
        2564 * σ ^ (9:ℕ) * ω ^ (12:ℕ) - 2072 * σ ^ (7:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ)) +
        (3540 * σ ^ (7:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) - 13088 * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) +
        13448 * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) + 4408 * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) -
        3164 * σ ^ (7:ℕ) * ω ^ (14:ℕ) - 952 * σ ^ (5:ℕ) * w ^ (12:ℕ) * ω ^ (4:ℕ)))) +
        (((4052 * σ ^ (5:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) - 14220 * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) +
        21496 * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) - 2784 * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) -
        2380 * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ)) + (932 * σ ^ (5:ℕ) * ω ^ (16:ℕ) -
        248 * σ ^ (3:ℕ) * w ^ (14:ℕ) * ω ^ (4:ℕ) + 1796 * σ ^ (3:ℕ) * w ^ (12:ℕ) * ω ^ (6:ℕ) -
        7008 * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) + 14404 * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ) -
        14456 * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ))) + ((10284 * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ)
        - 8816 * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) + 4044 * σ ^ (3:ℕ) * ω ^ (18:ℕ) -
        28 * σ * w ^ (16:ℕ) * ω ^ (4:ℕ) + 292 * σ * w ^ (14:ℕ) * ω ^ (6:ℕ) -
        1084 * σ * w ^ (12:ℕ) * ω ^ (8:ℕ)) + (1004 * σ * w ^ (10:ℕ) * ω ^ (10:ℕ) +
        3748 * σ * w ^ (8:ℕ) * ω ^ (12:ℕ) - 12004 * σ * w ^ (6:ℕ) * ω ^ (14:ℕ) +
        14396 * σ * w ^ (4:ℕ) * ω ^ (16:ℕ) - 8108 * σ * w ^ (2:ℕ) * ω ^ (18:ℕ) +
        1784 * σ * ω ^ (20:ℕ))))
  | 3, σ, w, ω => (((10 * σ ^ (18:ℕ) * ω ^ (2:ℕ) + 86 * σ ^ (16:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) +
        82 * σ ^ (16:ℕ) * ω ^ (4:ℕ) + 328 * σ ^ (14:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ) +
        464 * σ ^ (14:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) + 428 * σ ^ (14:ℕ) * ω ^ (6:ℕ)) +
        (728 * σ ^ (12:ℕ) * w ^ (6:ℕ) * ω ^ (2:ℕ) + 968 * σ ^ (12:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) +
        1356 * σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) + 1956 * σ ^ (12:ℕ) * ω ^ (8:ℕ) +
        1036 * σ ^ (10:ℕ) * w ^ (8:ℕ) * ω ^ (2:ℕ) + 656 * σ ^ (10:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) +
        2108 * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ))) + ((-328 * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) +
        3168 * σ ^ (10:ℕ) * ω ^ (10:ℕ) + 980 * σ ^ (8:ℕ) * w ^ (10:ℕ) * ω ^ (2:ℕ) -
        740 * σ ^ (8:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) + 3964 * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
        6788 * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 6448 * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ)) +
        (-3480 * σ ^ (8:ℕ) * ω ^ (12:ℕ) + 616 * σ ^ (6:ℕ) * w ^ (12:ℕ) * ω ^ (2:ℕ) -
        1808 * σ ^ (6:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) + 6916 * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) -
        10224 * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 5152 * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) +
        12896 * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ)))) + (((-7084 * σ ^ (6:ℕ) * ω ^ (14:ℕ) +
        248 * σ ^ (4:ℕ) * w ^ (14:ℕ) * ω ^ (2:ℕ) - 1496 * σ ^ (4:ℕ) * w ^ (12:ℕ) * ω ^ (4:ℕ) +
        6692 * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) - 12580 * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) +
        2496 * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 9472 * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ)) +
        (-6172 * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 1340 * σ ^ (4:ℕ) * ω ^ (16:ℕ) +
        58 * σ ^ (2:ℕ) * w ^ (16:ℕ) * ω ^ (2:ℕ) - 592 * σ ^ (2:ℕ) * w ^ (14:ℕ) * ω ^ (4:ℕ) +
        3092 * σ ^ (2:ℕ) * w ^ (12:ℕ) * ω ^ (6:ℕ) - 8264 * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (8:ℕ) +
        12736 * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (10:ℕ))) + ((-15360 * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (12:ℕ)
        + 16732 * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (14:ℕ) - 11880 * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (16:ℕ) +
        3478 * σ ^ (2:ℕ) * ω ^ (18:ℕ) + 6 * w ^ (18:ℕ) * ω ^ (2:ℕ) - 94 * w ^ (16:ℕ) * ω ^ (4:ℕ) +
        532 * w ^ (14:ℕ) * ω ^ (6:ℕ)) + (-1404 * w ^ (12:ℕ) * ω ^ (8:ℕ) +
        1808 * w ^ (10:ℕ) * ω ^ (10:ℕ) - 776 * w ^ (8:ℕ) * ω ^ (12:ℕ) - 756 * w ^ (6:ℕ) * ω ^ (14:ℕ)
        + 1148 * w ^ (4:ℕ) * ω ^ (16:ℕ) - 566 * w ^ (2:ℕ) * ω ^ (18:ℕ) + 102 * ω ^ (20:ℕ))))
  | 4, σ, w, ω => (((-2 * σ ^ (17:ℕ) * ω ^ (2:ℕ) - 16 * σ ^ (15:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) -
        136 * σ ^ (15:ℕ) * ω ^ (4:ℕ) - 56 * σ ^ (13:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ) -
        476 * σ ^ (13:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ)) + (-596 * σ ^ (13:ℕ) * ω ^ (6:ℕ) -
        112 * σ ^ (11:ℕ) * w ^ (6:ℕ) * ω ^ (2:ℕ) - 416 * σ ^ (11:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
        984 * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) - 352 * σ ^ (11:ℕ) * ω ^ (8:ℕ) -
        140 * σ ^ (9:ℕ) * w ^ (8:ℕ) * ω ^ (2:ℕ))) + ((300 * σ ^ (9:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
        348 * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) - 916 * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) +
        1280 * σ ^ (9:ℕ) * ω ^ (10:ℕ) - 112 * σ ^ (7:ℕ) * w ^ (10:ℕ) * ω ^ (2:ℕ)) +
        (600 * σ ^ (7:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) - 400 * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) +
        2416 * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 992 * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) -
        40 * σ ^ (7:ℕ) * ω ^ (12:ℕ) - 56 * σ ^ (5:ℕ) * w ^ (12:ℕ) * ω ^ (2:ℕ)))) +
        (((124 * σ ^ (5:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) - 12 * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) +
        5192 * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 6912 * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) +
        6076 * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ)) + (-2108 * σ ^ (5:ℕ) * ω ^ (14:ℕ) -
        16 * σ ^ (3:ℕ) * w ^ (14:ℕ) * ω ^ (2:ℕ) - 176 * σ ^ (3:ℕ) * w ^ (12:ℕ) * ω ^ (4:ℕ) +
        1128 * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) - 304 * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ) -
        1696 * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ))) + ((912 * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) +
        8 * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 144 * σ ^ (3:ℕ) * ω ^ (16:ℕ) -
        2 * σ * w ^ (16:ℕ) * ω ^ (2:ℕ) - 76 * σ * w ^ (14:ℕ) * ω ^ (4:ℕ) +
        700 * σ * w ^ (12:ℕ) * ω ^ (6:ℕ)) + (-2516 * σ * w ^ (10:ℕ) * ω ^ (8:ℕ) +
        5696 * σ * w ^ (8:ℕ) * ω ^ (10:ℕ) - 8852 * σ * w ^ (6:ℕ) * ω ^ (12:ℕ) +
        8692 * σ * w ^ (4:ℕ) * ω ^ (14:ℕ) - 4684 * σ * w ^ (2:ℕ) * ω ^ (16:ℕ) +
        1042 * σ * ω ^ (18:ℕ))))
  | 5, σ, w, ω => (((σ ^ (18:ℕ) + 9 * σ ^ (16:ℕ) * w ^ (2:ℕ) + 13 * σ ^ (16:ℕ) * ω ^ (2:ℕ) +
        36 * σ ^ (14:ℕ) * w ^ (4:ℕ) + 82 * σ ^ (14:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) +
        2 * σ ^ (14:ℕ) * ω ^ (4:ℕ)) + (84 * σ ^ (12:ℕ) * w ^ (6:ℕ) +
        202 * σ ^ (12:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ) + 60 * σ ^ (12:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) +
        118 * σ ^ (12:ℕ) * ω ^ (6:ℕ) + 126 * σ ^ (10:ℕ) * w ^ (8:ℕ) +
        218 * σ ^ (10:ℕ) * w ^ (6:ℕ) * ω ^ (2:ℕ) + 374 * σ ^ (10:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ))) +
        ((-746 * σ ^ (10:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ) + 564 * σ ^ (10:ℕ) * ω ^ (8:ℕ) +
        126 * σ ^ (8:ℕ) * w ^ (10:ℕ) + 20 * σ ^ (8:ℕ) * w ^ (8:ℕ) * ω ^ (2:ℕ) +
        1040 * σ ^ (8:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) - 2460 * σ ^ (8:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ) +
        986 * σ ^ (8:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ)) + (-192 * σ ^ (8:ℕ) * ω ^ (10:ℕ) +
        84 * σ ^ (6:ℕ) * w ^ (12:ℕ) - 202 * σ ^ (6:ℕ) * w ^ (10:ℕ) * ω ^ (2:ℕ) +
        1550 * σ ^ (6:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) - 3188 * σ ^ (6:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ) -
        368 * σ ^ (6:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 2398 * σ ^ (6:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ)))) +
        (((-1042 * σ ^ (6:ℕ) * ω ^ (12:ℕ) + 36 * σ ^ (4:ℕ) * w ^ (14:ℕ) -
        218 * σ ^ (4:ℕ) * w ^ (12:ℕ) * ω ^ (2:ℕ) + 1292 * σ ^ (4:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) -
        2882 * σ ^ (4:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) + 1020 * σ ^ (4:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) +
        1618 * σ ^ (4:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ)) + (-940 * σ ^ (4:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ) +
        74 * σ ^ (4:ℕ) * ω ^ (14:ℕ) + 9 * σ ^ (2:ℕ) * w ^ (16:ℕ) -
        98 * σ ^ (2:ℕ) * w ^ (14:ℕ) * ω ^ (2:ℕ) + 570 * σ ^ (2:ℕ) * w ^ (12:ℕ) * ω ^ (4:ℕ) -
        1602 * σ ^ (2:ℕ) * w ^ (10:ℕ) * ω ^ (6:ℕ) + 2348 * σ ^ (2:ℕ) * w ^ (8:ℕ) * ω ^ (8:ℕ))) +
        ((-2326 * σ ^ (2:ℕ) * w ^ (6:ℕ) * ω ^ (10:ℕ) + 2166 * σ ^ (2:ℕ) * w ^ (4:ℕ) * ω ^ (12:ℕ) -
        1542 * σ ^ (2:ℕ) * w ^ (2:ℕ) * ω ^ (14:ℕ) + 475 * σ ^ (2:ℕ) * ω ^ (16:ℕ) + w ^ (18:ℕ) -
        17 * w ^ (16:ℕ) * ω ^ (2:ℕ) + 104 * w ^ (14:ℕ) * ω ^ (4:ℕ)) + (-312 * w ^ (12:ℕ) * ω ^ (6:ℕ)
        + 538 * w ^ (10:ℕ) * ω ^ (8:ℕ) - 586 * w ^ (8:ℕ) * ω ^ (10:ℕ) + 432 * w ^ (6:ℕ) * ω ^ (12:ℕ)
        - 224 * w ^ (4:ℕ) * ω ^ (14:ℕ) + 77 * w ^ (2:ℕ) * ω ^ (16:ℕ) - 13 * ω ^ (18:ℕ))))
  | 6, σ, w, ω => (((-4 * σ ^ (15:ℕ) * ω ^ (2:ℕ) + 4 * σ ^ (13:ℕ) * w ^ (2:ℕ) * ω ^ (2:ℕ) -
        52 * σ ^ (13:ℕ) * ω ^ (4:ℕ) + 60 * σ ^ (11:ℕ) * w ^ (4:ℕ) * ω ^ (2:ℕ)) +
        (40 * σ ^ (11:ℕ) * w ^ (2:ℕ) * ω ^ (4:ℕ) - 12 * σ ^ (11:ℕ) * ω ^ (6:ℕ) +
        100 * σ ^ (9:ℕ) * w ^ (6:ℕ) * ω ^ (2:ℕ) + 452 * σ ^ (9:ℕ) * w ^ (4:ℕ) * ω ^ (4:ℕ) -
        428 * σ ^ (9:ℕ) * w ^ (2:ℕ) * ω ^ (6:ℕ))) + ((404 * σ ^ (9:ℕ) * ω ^ (8:ℕ) +
        20 * σ ^ (7:ℕ) * w ^ (8:ℕ) * ω ^ (2:ℕ) + 752 * σ ^ (7:ℕ) * w ^ (6:ℕ) * ω ^ (4:ℕ) -
        280 * σ ^ (7:ℕ) * w ^ (4:ℕ) * ω ^ (6:ℕ)) + (-48 * σ ^ (7:ℕ) * w ^ (2:ℕ) * ω ^ (8:ℕ) +
        196 * σ ^ (7:ℕ) * ω ^ (10:ℕ) - 84 * σ ^ (5:ℕ) * w ^ (10:ℕ) * ω ^ (2:ℕ) +
        724 * σ ^ (5:ℕ) * w ^ (8:ℕ) * ω ^ (4:ℕ) - 56 * σ ^ (5:ℕ) * w ^ (6:ℕ) * ω ^ (6:ℕ)))) +
        (((-1320 * σ ^ (5:ℕ) * w ^ (4:ℕ) * ω ^ (8:ℕ) + 1484 * σ ^ (5:ℕ) * w ^ (2:ℕ) * ω ^ (10:ℕ) -
        492 * σ ^ (5:ℕ) * ω ^ (12:ℕ) - 76 * σ ^ (3:ℕ) * w ^ (12:ℕ) * ω ^ (2:ℕ)) +
        (488 * σ ^ (3:ℕ) * w ^ (10:ℕ) * ω ^ (4:ℕ) - 668 * σ ^ (3:ℕ) * w ^ (8:ℕ) * ω ^ (6:ℕ) +
        272 * σ ^ (3:ℕ) * w ^ (6:ℕ) * ω ^ (8:ℕ) - 292 * σ ^ (3:ℕ) * w ^ (4:ℕ) * ω ^ (10:ℕ) +
        456 * σ ^ (3:ℕ) * w ^ (2:ℕ) * ω ^ (12:ℕ))) + ((-180 * σ ^ (3:ℕ) * ω ^ (14:ℕ) -
        20 * σ * w ^ (14:ℕ) * ω ^ (2:ℕ) + 156 * σ * w ^ (12:ℕ) * ω ^ (4:ℕ) -
        476 * σ * w ^ (10:ℕ) * ω ^ (6:ℕ)) + (884 * σ * w ^ (8:ℕ) * ω ^ (8:ℕ) -
        1196 * σ * w ^ (6:ℕ) * ω ^ (10:ℕ) + 1124 * σ * w ^ (4:ℕ) * ω ^ (12:ℕ) -
        612 * σ * w ^ (2:ℕ) * ω ^ (14:ℕ) + 140 * σ * ω ^ (16:ℕ))))
  | _, _, _, _ => 0

/-- **The Bautin form of the zero-current slice**, `𝔅(d, σ, w, ω) = Σ_k d^k 𝔅_k(σ, w, ω)`
(`sliceBautinCoeff`), `d = D/M`, `σ = R/L`, `w = ω₀`, `ω` the Hopf frequency: a polynomial of degree
23 with 336 terms, even in `w`. -/
def sliceBautin (d σ w ω : ℝ) : ℝ :=
  sliceBautinCoeff 0 σ w ω + d * sliceBautinCoeff 1 σ w ω + d ^ 2 * sliceBautinCoeff 2 σ w ω +
    d ^ 3 * sliceBautinCoeff 3 σ w ω + d ^ 4 * sliceBautinCoeff 4 σ w ω +
    d ^ 5 * sliceBautinCoeff 5 σ w ω + d ^ 6 * sliceBautinCoeff 6 σ w ω

/-- The real part of `N̂ = w χ̂ Ŷ₁ − 2 χ̂ Ŷ₂ + Ŷ₃`. -/
private def slNr (d σ w O : ℝ) : ℝ :=
  w * (sliceShiftRe d σ w O * slY1r d σ w O - sliceShiftIm d σ w O * slY1i d σ w O) -
    2 * (sliceShiftRe d σ w O * slY2r d σ w O - sliceShiftIm d σ w O * slY2i d σ w O) +
      slY3r d σ w O

/-- The imaginary part of `N̂`. -/
private def slNi (d σ w O : ℝ) : ℝ :=
  w * (sliceShiftRe d σ w O * slY1i d σ w O + sliceShiftIm d σ w O * slY1r d σ w O) -
    2 * (sliceShiftRe d σ w O * slY2i d σ w O + sliceShiftIm d σ w O * slY2r d σ w O) +
      slY3i d σ w O

/-- The real part of `D̂ = Ĉ χ̂`. -/
private def slDr (d σ w O : ℝ) : ℝ :=
  slicePairRe d σ w O * sliceShiftRe d σ w O - slicePairIm d σ w O * sliceShiftIm d σ w O

/-- The imaginary part of `D̂`. -/
private def slDi (d σ w O : ℝ) : ℝ :=
  slicePairRe d σ w O * sliceShiftIm d σ w O + slicePairIm d σ w O * sliceShiftRe d σ w O

private def slNr0 (σ w O : ℝ) : ℝ :=
  (((5 * σ ^ (14:ℕ) * w * O ^ (8:ℕ) + 33 * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    99 * σ ^ (12:ℕ) * w * O ^ (10:ℕ) + 93 * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)) +
    (422 * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) - 39 * σ ^ (10:ℕ) * w * O ^ (12:ℕ) +
    145 * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) + 665 * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) -
    169 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ))) + ((-449 * σ ^ (8:ℕ) * w * O ^ (14:ℕ) +
    135 * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) + 420 * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) -
    334 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ)) + (276 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) -
    177 * σ ^ (6:ℕ) * w * O ^ (16:ℕ) + 75 * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (8:ℕ) +
    5 * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (10:ℕ) - 218 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (12:ℕ)))) +
    (((-446 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (14:ℕ) + 191 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (16:ℕ) +
    393 * σ ^ (4:ℕ) * w * O ^ (18:ℕ) + 23 * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (8:ℕ)) +
    (-106 * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (10:ℕ) + 85 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (12:ℕ) -
    124 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (14:ℕ) + 577 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (16:ℕ) -
    730 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (18:ℕ))) + ((275 * σ ^ (2:ℕ) * w * O ^ (20:ℕ) +
    3 * w ^ (15:ℕ) * O ^ (8:ℕ) - 33 * w ^ (13:ℕ) * O ^ (10:ℕ) + 99 * w ^ (11:ℕ) * O ^ (12:ℕ)) +
    (-105 * w ^ (9:ℕ) * O ^ (14:ℕ) - 15 * w ^ (7:ℕ) * O ^ (16:ℕ) + 117 * w ^ (5:ℕ) * O ^ (18:ℕ) -
    87 * w ^ (3:ℕ) * O ^ (20:ℕ) + 21 * w * O ^ (22:ℕ))))

private def slNr1 (σ w O : ℝ) : ℝ :=
  ((-72 * σ ^ (13:ℕ) * w * O ^ (8:ℕ) - 396 * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    72 * σ ^ (11:ℕ) * w * O ^ (10:ℕ) - 900 * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    396 * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) + 288 * σ ^ (9:ℕ) * w * O ^ (12:ℕ) -
    1080 * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ)) + (864 * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) +
    72 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) - 144 * σ ^ (7:ℕ) * w * O ^ (14:ℕ) -
    720 * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) + 936 * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) -
    72 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) + 216 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ))) +
    ((-360 * σ ^ (5:ℕ) * w * O ^ (16:ℕ) - 252 * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (8:ℕ) +
    504 * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (10:ℕ) + 216 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (12:ℕ) -
    864 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (14:ℕ) + 324 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (16:ℕ) +
    72 * σ ^ (3:ℕ) * w * O ^ (18:ℕ)) + (-36 * σ * w ^ (13:ℕ) * O ^ (8:ℕ) +
    108 * σ * w ^ (11:ℕ) * O ^ (10:ℕ) + 72 * σ * w ^ (9:ℕ) * O ^ (12:ℕ) -
    648 * σ * w ^ (7:ℕ) * O ^ (14:ℕ) + 972 * σ * w ^ (5:ℕ) * O ^ (16:ℕ) -
    612 * σ * w ^ (3:ℕ) * O ^ (18:ℕ) + 144 * σ * w * O ^ (20:ℕ)))

private def slNr2 (σ w O : ℝ) : ℝ :=
  (((10 * σ ^ (14:ℕ) * w * O ^ (6:ℕ) + 66 * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    54 * σ ^ (12:ℕ) * w * O ^ (8:ℕ) + 186 * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)) +
    (196 * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) - 78 * σ ^ (10:ℕ) * w * O ^ (10:ℕ) +
    290 * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) + 178 * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    194 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ))) + ((-322 * σ ^ (8:ℕ) * w * O ^ (12:ℕ) +
    270 * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) - 168 * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    236 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ)) + (264 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) -
    66 * σ ^ (6:ℕ) * w * O ^ (14:ℕ) + 150 * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ) -
    422 * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) - 4 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ)))) +
    (((-316 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) + 238 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) +
    354 * σ ^ (4:ℕ) * w * O ^ (16:ℕ) + 46 * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (6:ℕ)) +
    (-284 * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (8:ℕ) + 314 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (10:ℕ) +
    40 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (12:ℕ) + 146 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (14:ℕ) -
    524 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (16:ℕ))) + ((262 * σ ^ (2:ℕ) * w * O ^ (18:ℕ) +
    6 * w ^ (15:ℕ) * O ^ (6:ℕ) - 66 * w ^ (13:ℕ) * O ^ (8:ℕ) + 198 * w ^ (11:ℕ) * O ^ (10:ℕ)) +
    (-210 * w ^ (9:ℕ) * O ^ (12:ℕ) - 30 * w ^ (7:ℕ) * O ^ (14:ℕ) + 234 * w ^ (5:ℕ) * O ^ (16:ℕ) -
    174 * w ^ (3:ℕ) * O ^ (18:ℕ) + 42 * w * O ^ (20:ℕ))))

private def slNr3 (σ w O : ℝ) : ℝ :=
  ((-72 * σ ^ (13:ℕ) * w * O ^ (6:ℕ) - 396 * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    72 * σ ^ (11:ℕ) * w * O ^ (8:ℕ) - 900 * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    396 * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) + 288 * σ ^ (9:ℕ) * w * O ^ (10:ℕ) -
    1080 * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ)) + (864 * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    72 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) - 144 * σ ^ (7:ℕ) * w * O ^ (12:ℕ) -
    720 * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) + 936 * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ) -
    72 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) + 216 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ))) +
    ((-360 * σ ^ (5:ℕ) * w * O ^ (14:ℕ) - 252 * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ) +
    504 * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) + 216 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) -
    864 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) + 324 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ) +
    72 * σ ^ (3:ℕ) * w * O ^ (16:ℕ)) + (-36 * σ * w ^ (13:ℕ) * O ^ (6:ℕ) +
    108 * σ * w ^ (11:ℕ) * O ^ (8:ℕ) + 72 * σ * w ^ (9:ℕ) * O ^ (10:ℕ) -
    648 * σ * w ^ (7:ℕ) * O ^ (12:ℕ) + 972 * σ * w ^ (5:ℕ) * O ^ (14:ℕ) -
    612 * σ * w ^ (3:ℕ) * O ^ (16:ℕ) + 144 * σ * w * O ^ (18:ℕ)))

private def slNr4 (σ w O : ℝ) : ℝ :=
  (((5 * σ ^ (14:ℕ) * w * O ^ (4:ℕ) + 33 * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    45 * σ ^ (12:ℕ) * w * O ^ (6:ℕ) + 93 * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)) +
    (-226 * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) - 39 * σ ^ (10:ℕ) * w * O ^ (8:ℕ) +
    145 * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) - 487 * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    25 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ))) + ((127 * σ ^ (8:ℕ) * w * O ^ (10:ℕ) +
    135 * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) - 588 * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    98 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)) + (-12 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    111 * σ ^ (6:ℕ) * w * O ^ (12:ℕ) + 75 * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (4:ℕ) -
    427 * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (6:ℕ) + 214 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (8:ℕ)))) +
    (((130 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (10:ℕ) + 47 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (12:ℕ) -
    39 * σ ^ (4:ℕ) * w * O ^ (14:ℕ) + 23 * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (4:ℕ)) +
    (-178 * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (6:ℕ) + 229 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (8:ℕ) +
    164 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (10:ℕ) - 431 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (12:ℕ) +
    206 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (14:ℕ))) + ((-13 * σ ^ (2:ℕ) * w * O ^ (16:ℕ) +
    3 * w ^ (15:ℕ) * O ^ (4:ℕ) - 33 * w ^ (13:ℕ) * O ^ (6:ℕ) + 99 * w ^ (11:ℕ) * O ^ (8:ℕ)) +
    (-105 * w ^ (9:ℕ) * O ^ (10:ℕ) - 15 * w ^ (7:ℕ) * O ^ (12:ℕ) + 117 * w ^ (5:ℕ) * O ^ (14:ℕ) -
    87 * w ^ (3:ℕ) * O ^ (16:ℕ) + 21 * w * O ^ (18:ℕ))))

@[tmio M, powerlib_domain] private theorem sl_Nr_coeffs (d σ w O : ℝ) :
    slNr d σ w O =
      slNr0 σ w O +
      d * slNr1 σ w O +
      d ^ 2 * slNr2 σ w O +
      d ^ 3 * slNr3 σ w O +
      d ^ 4 * slNr4 σ w O := by
  simp only [slNr, slY1r, slY1i, slY2r, slY2i, slY3r, sliceShiftRe, sliceShiftIm, slNr0, slNr1,
      slNr2, slNr3, slNr4]
  ring

private def slNi0 (σ w O : ℝ) : ℝ :=
  ((6 * σ ^ (13:ℕ) * w * O ^ (9:ℕ) + 36 * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) +
    276 * σ ^ (11:ℕ) * w * O ^ (11:ℕ) + 90 * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) +
    972 * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) + 522 * σ ^ (9:ℕ) * w * O ^ (13:ℕ) +
    120 * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ)) + (1320 * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) +
    648 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) + 24 * σ ^ (7:ℕ) * w * O ^ (15:ℕ) +
    90 * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ) + 888 * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ) +
    252 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) + 696 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ))) +
    ((-390 * σ ^ (5:ℕ) * w * O ^ (17:ℕ) + 36 * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (9:ℕ) +
    324 * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (11:ℕ) - 120 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (13:ℕ) -
    984 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (15:ℕ) + 852 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (17:ℕ) -
    108 * σ ^ (3:ℕ) * w * O ^ (19:ℕ)) + (6 * σ * w ^ (13:ℕ) * O ^ (9:ℕ) +
    60 * σ * w ^ (11:ℕ) * O ^ (11:ℕ) - 246 * σ * w ^ (9:ℕ) * O ^ (13:ℕ) +
    264 * σ * w ^ (7:ℕ) * O ^ (15:ℕ) - 6 * σ * w ^ (5:ℕ) * O ^ (17:ℕ) -
    132 * σ * w ^ (3:ℕ) * O ^ (19:ℕ) + 54 * σ * w * O ^ (21:ℕ)))

private def slNi1 (σ w O : ℝ) : ℝ :=
  (((12 * σ ^ (14:ℕ) * w * O ^ (7:ℕ) + 78 * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) -
    144 * σ ^ (12:ℕ) * w * O ^ (9:ℕ) + 216 * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ)) +
    (-684 * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) - 132 * σ ^ (10:ℕ) * w * O ^ (11:ℕ) +
    330 * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) - 1356 * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) -
    30 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ))) + ((336 * σ ^ (8:ℕ) * w * O ^ (13:ℕ) +
    300 * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) - 1464 * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) +
    384 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ)) + (-24 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) +
    228 * σ ^ (6:ℕ) * w * O ^ (15:ℕ) + 162 * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (7:ℕ) -
    936 * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ) + 492 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ)))) +
    (((360 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) + 162 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ) -
    240 * σ ^ (4:ℕ) * w * O ^ (17:ℕ) + 48 * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (7:ℕ)) +
    (-348 * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (9:ℕ) + 372 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (11:ℕ) +
    600 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (13:ℕ) - 1272 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (15:ℕ) +
    708 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (17:ℕ))) + ((-108 * σ ^ (2:ℕ) * w * O ^ (19:ℕ) +
    6 * w ^ (15:ℕ) * O ^ (7:ℕ) - 60 * w ^ (13:ℕ) * O ^ (9:ℕ) + 162 * w ^ (11:ℕ) * O ^ (11:ℕ)) +
    (-120 * w ^ (9:ℕ) * O ^ (13:ℕ) - 150 * w ^ (7:ℕ) * O ^ (15:ℕ) + 324 * w ^ (5:ℕ) * O ^ (17:ℕ) -
    210 * w ^ (3:ℕ) * O ^ (19:ℕ) + 48 * w * O ^ (21:ℕ))))

private def slNi2 (σ w O : ℝ) : ℝ :=
  ((36 * σ ^ (13:ℕ) * w * O ^ (7:ℕ) + 204 * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) +
    288 * σ ^ (11:ℕ) * w * O ^ (9:ℕ) + 480 * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) +
    972 * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) + 516 * σ ^ (9:ℕ) * w * O ^ (11:ℕ) +
    600 * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ)) + (1200 * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) +
    792 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) + 192 * σ ^ (7:ℕ) * w * O ^ (13:ℕ) +
    420 * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) + 648 * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) +
    336 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) + 696 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ))) +
    ((-180 * σ ^ (5:ℕ) * w * O ^ (15:ℕ) + 156 * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (7:ℕ) +
    144 * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ) - 216 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ) -
    720 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) + 732 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ) -
    96 * σ ^ (3:ℕ) * w * O ^ (17:ℕ)) + (24 * σ * w ^ (13:ℕ) * O ^ (7:ℕ) +
    12 * σ * w ^ (11:ℕ) * O ^ (9:ℕ) - 276 * σ * w ^ (9:ℕ) * O ^ (11:ℕ) +
    504 * σ * w ^ (7:ℕ) * O ^ (13:ℕ) - 336 * σ * w ^ (5:ℕ) * O ^ (15:ℕ) +
    60 * σ * w ^ (3:ℕ) * O ^ (17:ℕ) + 12 * σ * w * O ^ (19:ℕ)))

private def slNi3 (σ w O : ℝ) : ℝ :=
  (((12 * σ ^ (14:ℕ) * w * O ^ (5:ℕ) + 78 * σ ^ (12:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) -
    144 * σ ^ (12:ℕ) * w * O ^ (7:ℕ) + 216 * σ ^ (10:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ)) +
    (-684 * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) - 132 * σ ^ (10:ℕ) * w * O ^ (9:ℕ) +
    330 * σ ^ (8:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) - 1356 * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) -
    30 * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ))) + ((336 * σ ^ (8:ℕ) * w * O ^ (11:ℕ) +
    300 * σ ^ (6:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) - 1464 * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) +
    384 * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ)) + (-24 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) +
    228 * σ ^ (6:ℕ) * w * O ^ (13:ℕ) + 162 * σ ^ (4:ℕ) * w ^ (11:ℕ) * O ^ (5:ℕ) -
    936 * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) + 492 * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ)))) +
    (((360 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) + 162 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) -
    240 * σ ^ (4:ℕ) * w * O ^ (15:ℕ) + 48 * σ ^ (2:ℕ) * w ^ (13:ℕ) * O ^ (5:ℕ)) +
    (-348 * σ ^ (2:ℕ) * w ^ (11:ℕ) * O ^ (7:ℕ) + 372 * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (9:ℕ) +
    600 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (11:ℕ) - 1272 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (13:ℕ) +
    708 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (15:ℕ))) + ((-108 * σ ^ (2:ℕ) * w * O ^ (17:ℕ) +
    6 * w ^ (15:ℕ) * O ^ (5:ℕ) - 60 * w ^ (13:ℕ) * O ^ (7:ℕ) + 162 * w ^ (11:ℕ) * O ^ (9:ℕ)) +
    (-120 * w ^ (9:ℕ) * O ^ (11:ℕ) - 150 * w ^ (7:ℕ) * O ^ (13:ℕ) + 324 * w ^ (5:ℕ) * O ^ (15:ℕ) -
    210 * w ^ (3:ℕ) * O ^ (17:ℕ) + 48 * w * O ^ (19:ℕ))))

private def slNi4 (σ w O : ℝ) : ℝ :=
  ((30 * σ ^ (13:ℕ) * w * O ^ (5:ℕ) + 168 * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) +
    12 * σ ^ (11:ℕ) * w * O ^ (7:ℕ) + 390 * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) -
    6 * σ ^ (9:ℕ) * w * O ^ (9:ℕ) + 480 * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ)) +
    (-120 * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) + 144 * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) +
    168 * σ ^ (7:ℕ) * w * O ^ (11:ℕ) + 330 * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) -
    240 * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) + 84 * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) +
    210 * σ ^ (5:ℕ) * w * O ^ (13:ℕ))) + ((120 * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (5:ℕ) -
    180 * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (7:ℕ) - 96 * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (9:ℕ) +
    264 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (11:ℕ) - 120 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (13:ℕ) +
    12 * σ ^ (3:ℕ) * w * O ^ (15:ℕ)) + (18 * σ * w ^ (13:ℕ) * O ^ (5:ℕ) -
    48 * σ * w ^ (11:ℕ) * O ^ (7:ℕ) - 30 * σ * w ^ (9:ℕ) * O ^ (9:ℕ) +
    240 * σ * w ^ (7:ℕ) * O ^ (11:ℕ) - 330 * σ * w ^ (5:ℕ) * O ^ (13:ℕ) +
    192 * σ * w ^ (3:ℕ) * O ^ (15:ℕ) - 42 * σ * w * O ^ (17:ℕ)))

@[tmio M, powerlib_domain] private theorem sl_Ni_coeffs (d σ w O : ℝ) :
    slNi d σ w O =
      slNi0 σ w O +
      d * slNi1 σ w O +
      d ^ 2 * slNi2 σ w O +
      d ^ 3 * slNi3 σ w O +
      d ^ 4 * slNi4 σ w O := by
  simp only [slNi, slY1r, slY1i, slY2r, slY2i, slY3i, sliceShiftRe, sliceShiftIm, slNi0, slNi1,
      slNi2, slNi3, slNi4]
  ring

private def slDr0 (σ w O : ℝ) : ℝ :=
  -108 * σ ^ (5:ℕ) * w * O ^ (10:ℕ) - 216 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    648 * σ ^ (3:ℕ) * w * O ^ (12:ℕ) - 108 * σ * w ^ (5:ℕ) * O ^ (10:ℕ) +
    360 * σ * w ^ (3:ℕ) * O ^ (12:ℕ) - 252 * σ * w * O ^ (14:ℕ)

private def slDr1 (σ w O : ℝ) : ℝ :=
  -18 * σ ^ (8:ℕ) * w * O ^ (6:ℕ) - 72 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    72 * σ ^ (6:ℕ) * w * O ^ (8:ℕ) - 108 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    648 * σ ^ (4:ℕ) * w * O ^ (10:ℕ) - 72 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    216 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) + 288 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    432 * σ ^ (2:ℕ) * w * O ^ (12:ℕ) - 18 * w ^ (9:ℕ) * O ^ (6:ℕ) + 144 * w ^ (7:ℕ) * O ^ (8:ℕ) -
    360 * w ^ (5:ℕ) * O ^ (10:ℕ) + 360 * w ^ (3:ℕ) * O ^ (12:ℕ) - 126 * w * O ^ (14:ℕ)

private def slDr2 (σ w O : ℝ) : ℝ :=
  36 * σ ^ (7:ℕ) * w * O ^ (6:ℕ) + 108 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    684 * σ ^ (5:ℕ) * w * O ^ (8:ℕ) + 108 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    936 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) + 180 * σ ^ (3:ℕ) * w * O ^ (10:ℕ) +
    36 * σ * w ^ (7:ℕ) * O ^ (6:ℕ) - 252 * σ * w ^ (5:ℕ) * O ^ (8:ℕ) +
    612 * σ * w ^ (3:ℕ) * O ^ (10:ℕ) - 396 * σ * w * O ^ (12:ℕ)

private def slDr3 (σ w O : ℝ) : ℝ :=
  -18 * σ ^ (8:ℕ) * w * O ^ (4:ℕ) - 72 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    216 * σ ^ (6:ℕ) * w * O ^ (6:ℕ) - 108 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    576 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) - 216 * σ ^ (4:ℕ) * w * O ^ (8:ℕ) -
    72 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) + 504 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    576 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) + 144 * σ ^ (2:ℕ) * w * O ^ (10:ℕ) -
    18 * w ^ (9:ℕ) * O ^ (4:ℕ) + 144 * w ^ (7:ℕ) * O ^ (6:ℕ) - 360 * w ^ (5:ℕ) * O ^ (8:ℕ) +
    360 * w ^ (3:ℕ) * O ^ (10:ℕ) - 126 * w * O ^ (12:ℕ)

private def slDr4 (σ w O : ℝ) : ℝ :=
  -36 * σ ^ (7:ℕ) * w * O ^ (4:ℕ) - 108 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    108 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) + 144 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    108 * σ ^ (3:ℕ) * w * O ^ (8:ℕ) - 36 * σ * w ^ (7:ℕ) * O ^ (4:ℕ) +
    144 * σ * w ^ (5:ℕ) * O ^ (6:ℕ) - 108 * σ * w ^ (3:ℕ) * O ^ (8:ℕ)

@[tmio M, powerlib_domain] private theorem sl_Dr_coeffs (d σ w O : ℝ) :
    slDr d σ w O =
      slDr0 σ w O +
      d * slDr1 σ w O +
      d ^ 2 * slDr2 σ w O +
      d ^ 3 * slDr3 σ w O +
      d ^ 4 * slDr4 σ w O := by
  simp only [slDr, slicePairRe, slicePairIm, sliceShiftRe, sliceShiftIm, slDr0, slDr1, slDr2, slDr3,
      slDr4]
  ring

private def slDi0 (σ w O : ℝ) : ℝ :=
  6 * σ ^ (8:ℕ) * w * O ^ (7:ℕ) + 24 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) +
    114 * σ ^ (6:ℕ) * w * O ^ (9:ℕ) + 36 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) +
    174 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) + 462 * σ ^ (4:ℕ) * w * O ^ (11:ℕ) +
    24 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) + 6 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) -
    348 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) + 126 * σ ^ (2:ℕ) * w * O ^ (13:ℕ) +
    6 * w ^ (9:ℕ) * O ^ (7:ℕ) - 54 * w ^ (7:ℕ) * O ^ (9:ℕ) + 150 * w ^ (5:ℕ) * O ^ (11:ℕ) -
    162 * w ^ (3:ℕ) * O ^ (13:ℕ) + 60 * w * O ^ (15:ℕ)

private def slDi1 (σ w O : ℝ) : ℝ :=
  -60 * σ ^ (7:ℕ) * w * O ^ (7:ℕ) - 180 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) -
    468 * σ ^ (5:ℕ) * w * O ^ (9:ℕ) - 180 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) -
    312 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) + 564 * σ ^ (3:ℕ) * w * O ^ (11:ℕ) -
    60 * σ * w ^ (7:ℕ) * O ^ (7:ℕ) + 156 * σ * w ^ (5:ℕ) * O ^ (9:ℕ) -
    60 * σ * w ^ (3:ℕ) * O ^ (11:ℕ) - 36 * σ * w * O ^ (13:ℕ)

private def slDi2 (σ w O : ℝ) : ℝ :=
  288 * σ ^ (6:ℕ) * w * O ^ (7:ℕ) + 552 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) -
    504 * σ ^ (4:ℕ) * w * O ^ (9:ℕ) + 240 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) -
    1056 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) + 576 * σ ^ (2:ℕ) * w * O ^ (11:ℕ) -
    24 * w ^ (7:ℕ) * O ^ (7:ℕ) + 120 * w ^ (5:ℕ) * O ^ (9:ℕ) - 168 * w ^ (3:ℕ) * O ^ (11:ℕ) +
    72 * w * O ^ (13:ℕ)

private def slDi3 (σ w O : ℝ) : ℝ :=
  -108 * σ ^ (7:ℕ) * w * O ^ (5:ℕ) - 324 * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) +
    204 * σ ^ (5:ℕ) * w * O ^ (7:ℕ) - 324 * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) +
    648 * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) - 252 * σ ^ (3:ℕ) * w * O ^ (9:ℕ) -
    108 * σ * w ^ (7:ℕ) * O ^ (5:ℕ) + 444 * σ * w ^ (5:ℕ) * O ^ (7:ℕ) -
    492 * σ * w ^ (3:ℕ) * O ^ (9:ℕ) + 156 * σ * w * O ^ (11:ℕ)

private def slDi4 (σ w O : ℝ) : ℝ :=
  6 * σ ^ (8:ℕ) * w * O ^ (3:ℕ) + 24 * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) -
    54 * σ ^ (6:ℕ) * w * O ^ (5:ℕ) + 36 * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) -
    162 * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) + 30 * σ ^ (4:ℕ) * w * O ^ (7:ℕ) +
    24 * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) - 162 * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) +
    84 * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) + 6 * σ ^ (2:ℕ) * w * O ^ (9:ℕ) +
    6 * w ^ (9:ℕ) * O ^ (3:ℕ) - 54 * w ^ (7:ℕ) * O ^ (5:ℕ) + 150 * w ^ (5:ℕ) * O ^ (7:ℕ) -
    162 * w ^ (3:ℕ) * O ^ (9:ℕ) + 60 * w * O ^ (11:ℕ)

@[tmio M, powerlib_domain] private theorem sl_Di_coeffs (d σ w O : ℝ) :
    slDi d σ w O =
      slDi0 σ w O +
      d * slDi1 σ w O +
      d ^ 2 * slDi2 σ w O +
      d ^ 3 * slDi3 σ w O +
      d ^ 4 * slDi4 σ w O := by
  simp only [slDi, slicePairRe, slicePairIm, sliceShiftRe, sliceShiftIm, slDi0, slDi1, slDi2, slDi3,
      slDi4]
  ring

@[tmio M, powerlib_domain] private theorem sl_key0 (σ w O : ℝ) :
    slNr0 σ w O * slDr0 σ w O + slNi0 σ w O * slDi0 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (O ^ 2 *
          sliceBautinCoeff 0 σ w O) := by
  simp only [slDi0, slDr0, slNi0, slNr0, sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key1 (σ w O : ℝ) :
    slNr0 σ w O * slDr1 σ w O + slNi0 σ w O * slDi1 σ w O +
      slNr1 σ w O * slDr0 σ w O + slNi1 σ w O * slDi0 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (O ^ 2 *
          sliceBautinCoeff 1 σ w O) := by
  simp only [slDi0, slDi1, slDr0, slDr1, slNi0, slNi1, slNr0, slNr1, sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key2 (σ w O : ℝ) :
    slNr0 σ w O * slDr2 σ w O + slNi0 σ w O * slDi2 σ w O +
      slNr1 σ w O * slDr1 σ w O + slNi1 σ w O * slDi1 σ w O +
      slNr2 σ w O * slDr0 σ w O + slNi2 σ w O * slDi0 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (O ^ 2 *
          sliceBautinCoeff 2 σ w O + sliceBautinCoeff 0 σ w O) := by
  simp only [slDi0, slDi1, slDi2, slDr0, slDr1, slDr2, slNi0, slNi1, slNi2, slNr0, slNr1, slNr2,
      sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key3 (σ w O : ℝ) :
    slNr0 σ w O * slDr3 σ w O + slNi0 σ w O * slDi3 σ w O +
      slNr1 σ w O * slDr2 σ w O + slNi1 σ w O * slDi2 σ w O +
      slNr2 σ w O * slDr1 σ w O + slNi2 σ w O * slDi1 σ w O +
      slNr3 σ w O * slDr0 σ w O + slNi3 σ w O * slDi0 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (O ^ 2 *
          sliceBautinCoeff 3 σ w O + sliceBautinCoeff 1 σ w O) := by
  simp only [slDi0, slDi1, slDi2, slDi3, slDr0, slDr1, slDr2, slDr3, slNi0, slNi1, slNi2, slNi3,
      slNr0, slNr1, slNr2, slNr3, sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key4 (σ w O : ℝ) :
    slNr0 σ w O * slDr4 σ w O + slNi0 σ w O * slDi4 σ w O +
      slNr1 σ w O * slDr3 σ w O + slNi1 σ w O * slDi3 σ w O +
      slNr2 σ w O * slDr2 σ w O + slNi2 σ w O * slDi2 σ w O +
      slNr3 σ w O * slDr1 σ w O + slNi3 σ w O * slDi1 σ w O +
      slNr4 σ w O * slDr0 σ w O + slNi4 σ w O * slDi0 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (O ^ 2 *
          sliceBautinCoeff 4 σ w O + sliceBautinCoeff 2 σ w O) := by
  simp only [slDi0, slDi1, slDi2, slDi3, slDi4, slDr0, slDr1, slDr2, slDr3, slDr4, slNi0, slNi1,
      slNi2, slNi3, slNi4, slNr0, slNr1, slNr2, slNr3, slNr4, sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key5 (σ w O : ℝ) :
    slNr1 σ w O * slDr4 σ w O + slNi1 σ w O * slDi4 σ w O +
      slNr2 σ w O * slDr3 σ w O + slNi2 σ w O * slDi3 σ w O +
      slNr3 σ w O * slDr2 σ w O + slNi3 σ w O * slDi2 σ w O +
      slNr4 σ w O * slDr1 σ w O + slNi4 σ w O * slDi1 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (O ^ 2 *
          sliceBautinCoeff 5 σ w O + sliceBautinCoeff 3 σ w O) := by
  simp only [slDi1, slDi2, slDi3, slDi4, slDr1, slDr2, slDr3, slDr4, slNi1, slNi2, slNi3, slNi4,
      slNr1, slNr2, slNr3, slNr4, sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key6 (σ w O : ℝ) :
    slNr2 σ w O * slDr4 σ w O + slNi2 σ w O * slDi4 σ w O +
      slNr3 σ w O * slDr3 σ w O + slNi3 σ w O * slDi3 σ w O +
      slNr4 σ w O * slDr2 σ w O + slNi4 σ w O * slDi2 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (O ^ 2 *
          sliceBautinCoeff 6 σ w O + sliceBautinCoeff 4 σ w O) := by
  simp only [slDi2, slDi3, slDi4, slDr2, slDr3, slDr4, slNi2, slNi3, slNi4, slNr2, slNr3, slNr4,
      sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key7 (σ w O : ℝ) :
    slNr3 σ w O * slDr4 σ w O + slNi3 σ w O * slDi4 σ w O +
      slNr4 σ w O * slDr3 σ w O + slNi4 σ w O * slDi3 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (0 +
          sliceBautinCoeff 5 σ w O) := by
  simp only [slDi3, slDi4, slDr3, slDr4, slNi3, slNi4, slNr3, slNr4, sliceBautinCoeff]
  ring

@[tmio M, powerlib_domain] private theorem sl_key8 (σ w O : ℝ) :
    slNr4 σ w O * slDr4 σ w O + slNi4 σ w O * slDi4 σ w O =
      -18 * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * (0 +
          sliceBautinCoeff 6 σ w O) := by
  simp only [slDi4, slDr4, slNi4, slNr4, sliceBautinCoeff]
  ring

/-- **The key identity of the slice**: `Re(N̂ conj D̂) = −18 (ω² + d²) w² ω⁸ |L_q|² 𝔅`
(certificate split along the powers of `d`). -/
@[tmio M, powerlib_domain] private theorem sl_key (d σ w O : ℝ) :
    slNr d σ w O * slDr d σ w O + slNi d σ w O * slDi d σ w O =
      -18 * (O ^ 2 + d ^ 2) * w ^ 2 * O ^ 8 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) *
          sliceBautin d σ w O := by
  rw [sl_Nr_coeffs, sl_Ni_coeffs, sl_Dr_coeffs, sl_Di_coeffs, sliceBautin]
  linear_combination sl_key0 σ w O + d * sl_key1 σ w O + d ^ 2 * sl_key2 σ w O + d ^ 3 *
      sl_key3 σ w O + d ^ 4 * sl_key4 σ w O + d ^ 5 * sl_key5 σ w O + d ^ 6 * sl_key6 σ w O +
      d ^ 7 * sl_key7 σ w O + d ^ 8 * sl_key8 σ w O

@[tmio M, powerlib_domain] private theorem slY1r_cast (d σ w ω : ℝ) :
    slY1r (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slY1r d σ w ω : ℝ) : ℂ) := by
  simp only [slY1r]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem slY1i_cast (d σ w ω : ℝ) :
    slY1i (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slY1i d σ w ω : ℝ) : ℂ) := by
  simp only [slY1i]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem slY2r_cast (d σ w ω : ℝ) :
    slY2r (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slY2r d σ w ω : ℝ) : ℂ) := by
  simp only [slY2r]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem slY2i_cast (d σ w ω : ℝ) :
    slY2i (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slY2i d σ w ω : ℝ) : ℂ) := by
  simp only [slY2i]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem slY3r_cast (d σ w ω : ℝ) :
    slY3r (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slY3r d σ w ω : ℝ) : ℂ) := by
  simp only [slY3r]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem slY3i_cast (d σ w ω : ℝ) :
    slY3i (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slY3i d σ w ω : ℝ) : ℂ) := by
  simp only [slY3i]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem slicePairRe_cast (d σ w ω : ℝ) :
    slicePairRe (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slicePairRe d σ w ω : ℝ) : ℂ) := by
  simp only [slicePairRe]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem slicePairIm_cast (d σ w ω : ℝ) :
    slicePairIm (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((slicePairIm d σ w ω : ℝ) : ℂ) := by
  simp only [slicePairIm]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem sliceShiftRe_cast (d σ w ω : ℝ) :
    sliceShiftRe (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((sliceShiftRe d σ w ω : ℝ) : ℂ) := by
  simp only [sliceShiftRe]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem sliceShiftIm_cast (d σ w ω : ℝ) :
    sliceShiftIm (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) = ((sliceShiftIm d σ w ω : ℝ) : ℂ) := by
  simp only [sliceShiftIm]
  push_cast
  ring

@[tmio M, powerlib_domain] private theorem sl_star_Q (d σ w ω : ℝ) :
    star (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
        sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I := by
  ext k
  fin_cases k <;> simp only [Pi.star_apply, RCLike.star_def, sliceVecQ, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, map_mul, map_add, map_sub, map_neg,
    map_pow, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> ring

@[tmio M, powerlib_domain] private theorem sl_star_Pt (d c σ w ω : ℝ) :
    star (sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I := by
  ext k
  fin_cases k <;> simp only [Pi.star_apply, RCLike.star_def, sliceVecP, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, map_mul, map_add, map_sub, map_neg,
      map_pow, Complex.conj_ofReal, Complex.conj_I, Fin.zero_eta, Fin.mk_one,
          Fin.reduceFinMk] <;> ring

/-- The projection-formula combination in the reduced quantities. -/
@[tmio M, powerlib_domain] private theorem sl_alg {Y1 Y2 Y3 Cp X Qc w A1 A2 A3 Ch Xh : ℂ}
    (hQ : Qc ≠ 0) (hw : w ≠ 0) (hC : Ch ≠ 0) (hX : Xh ≠ 0)
    (e1 : w * Qc * Y1 = A1) (e2 : w * Qc * Y2 = A2) (e3 : w * Qc ^ 2 * Y3 = A3)
    (eC : Qc * Cp = Ch) (eX : Qc * X = Xh) :
    Cp⁻¹ * Y1 - 2 * (w⁻¹ * (Cp⁻¹ * Y2)) + (w * X)⁻¹ * (Cp⁻¹ * Y3) =
      (w * Xh * A1 - 2 * Xh * A2 + A3) / (w ^ 2 * (Ch * Xh)) := by
  have hCp : Cp ≠ 0 := by
    rintro rfl
    exact hC (by rw [← eC, mul_zero])
  have hX0 : X ≠ 0 := by
    rintro rfl
    exact hX (by rw [← eX, mul_zero])
  subst e1 e2 e3 eC eX
  field_simp

/-- The real part of the reduced quotient. -/
@[tmio M, powerlib_domain] private theorem sl_re (a b e f w : ℝ) (hw : w ≠ 0)
    (hef : e ^ 2 + f ^ 2 ≠ 0) :
    (((a : ℂ) + (b : ℂ) * I) / ((w : ℂ) ^ 2 * ((e : ℂ) + (f : ℂ) * I))).re =
      (a * e + b * f) / (w ^ 2 * (e ^ 2 + f ^ 2)) := by
  have hz : (w : ℂ) ^ 2 * ((e : ℂ) + (f : ℂ) * I) =
      ((w ^ 2 * e : ℝ) : ℂ) + ((w ^ 2 * f : ℝ) : ℂ) * I := by push_cast; ring
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hd : w ^ 2 * e * (w ^ 2 * e) + w ^ 2 * f * (w ^ 2 * f) ≠ 0 := by
    rw [show w ^ 2 * e * (w ^ 2 * e) + w ^ 2 * f * (w ^ 2 * f) = (w ^ 2) ^ 2 * (e ^ 2 + f ^ 2) by
      ring]
    exact mul_ne_zero (pow_ne_zero 2 hw2) hef
  rw [hz, Complex.div_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, Complex.normSq_apply, mul_zero, sub_zero,
    zero_add, add_zero, mul_one]
  field_simp

/-- The cubic cofactor does not vanish at `2iω`: `χ ≠ 0`. -/
@[tmio M, powerlib_domain] private theorem sl_chi_ne {d c g σ w ω : ℝ} (hω : 0 < ω)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2) =
      ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d))
    (h2 : c * g * w = ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2)))
    (k4 : 0 < c + d + 2 * σ)
    (k0 : 0 < 2 * c * d * σ + (c + d) * (σ ^ 2 + w ^ 2) - (c + d + 2 * σ) * ω ^ 2)
    (kg : 2 * c * d * σ + (c + d) * (σ ^ 2 + w ^ 2) - (c + d + 2 * σ) * ω ^ 2 <
      (c + d + 2 * σ) * (σ ^ 2 + w ^ 2 + 2 * σ * (c + d) + c * d - ω ^ 2)) :
    slChi (d : ℂ) (c : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I ≠ 0 := by
  have h1c : (c : ℂ) * ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) =
      (ω : ℂ) ^ 2 * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d) := by exact_mod_cast h1
  have h2c : (c : ℂ) * g * w = (ω : ℂ) ^ 2 * (((d : ℂ) + c) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 -
      (ω : ℂ) ^ 2) + 2 * σ * (d * c - (ω : ℂ) ^ 2)) := by exact_mod_cast h2
  rw [sl_chi_cubic I_sq h1c h2c]
  have hω2 : (ω : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hω 2).ne'
  refine mul_ne_zero (mul_ne_zero (by norm_num) hω2) fun h => ?_
  have hre := Criteria.cubic_roots_re_neg_of k4 k0 kg (2 * ω *
      I) (by push_cast; linear_combination h)
  simp at hre

/-- `Q_c > 0` at a slice Hopf point: `(ω² + c²) Q_c = c g w`. -/
@[tmio M, powerlib_domain] private theorem sl_Qc_pos {d c g σ w ω : ℝ} (hG : 0 < c * g * w)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2) =
      ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d))
    (h2 : c * g * w = ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2))) :
    0 < d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2 := by
  have hQ : (ω ^ 2 + c ^ 2) * (d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2) = c * g * w := by
    linear_combination c * h1 - h2
  by_contra hn
  push Not at hn
  have : 0 ≤ ω ^ 2 + c ^ 2 := by positivity
  nlinarith

/-- `Re Ĉ > 0` at a slice Hopf point. -/
@[tmio M, powerlib_domain] private theorem sl_pairRe_pos {d σ w ω : ℝ} (hω : 0 < ω) (hw : 0 < w)
    (hd : 0 < d) (hσ : 0 ≤ σ) (hQ : 0 < d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2) :
    0 < slicePairRe d σ w ω := by
  have e : slicePairRe d σ w ω = 2 * ω ^ 2 * w * (d * (σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 +
      2 * σ * ω ^ 4 + 2 * d ^ 2 * σ * (σ ^ 2 + w ^ 2)) := by
    simp only [slicePairRe]
    ring
  have hτ : 0 < σ ^ 2 + w ^ 2 - ω ^ 2 := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonneg hσ (sq_nonneg ω)]
  rw [e]
  positivity

/-- **The critical pair of the slice pattern**. -/
@[tmio M, powerlib_domain] private theorem sl_isCriticalPair {f : State 5 → State 5}
    {d c g σ w ω : ℝ} (hω : 0 < ω)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2) =
      ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d))
    (h2 : c * g * w = ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2)))
    (hc0 : slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I ≠ 0) (hf : f 0 = 0)
    (hJ : jacobianC f 0 = slJ (d : ℂ) (c : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ)) :
    IsCriticalPair f 0 ω (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
      ((starRingEnd ℂ (slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))⁻¹ •
        sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) := by
  have h1c : (c : ℂ) * ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) =
      (ω : ℂ) ^ 2 * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d) := by exact_mod_cast h1
  have h2c : (c : ℂ) * g * w = (ω : ℂ) ^ 2 * (((d : ℂ) + c) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 -
      (ω : ℂ) ^ 2) + 2 * σ * (d * c - (ω : ℂ) ^ 2)) := by exact_mod_cast h2
  refine ⟨hf, hω, ?_, ?_, ?_⟩
  · rw [hJ]
    exact sl_right I_sq h1c h2c
  · rw [hJ, Matrix.mulVec_smul, sl_left I_sq h1c h2c, smul_comm]
  · have hstar : star ((starRingEnd ℂ (slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))⁻¹ •
        sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
        (slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)⁻¹ •
          star (sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) := by
      ext k
      simp [Pi.star_apply]
    rw [hstar, smul_dotProduct, sl_star_Pt, sl_norm I_sq, smul_eq_mul, inv_mul_cancel₀ hc0]

/-- **The first Lyapunov coefficient of the slice pattern in closed form**. -/
@[tmio M, powerlib_domain] private theorem sl_firstLyapunov {f : State 5 → State 5}
    {d c g σ w ω : ℝ} (hω : 0 < ω) (hw : 0 < w) (hd : 0 < d) (hσ : 0 ≤ σ) (hG : 0 < c * g * w)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2) =
      ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d))
    (h2 : c * g * w = ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2)))
    (k4 : 0 < c + d + 2 * σ)
    (k0 : 0 < 2 * c * d * σ + (c + d) * (σ ^ 2 + w ^ 2) - (c + d + 2 * σ) * ω ^ 2)
    (kg : 2 * c * d * σ + (c + d) * (σ ^ 2 + w ^ 2) - (c + d + 2 * σ) * ω ^ 2 <
      (c + d + 2 * σ) * (σ ^ 2 + w ^ 2 + 2 * σ * (c + d) + c * d - ω ^ 2))
    (hJ : jacobianC f 0 = slJ (d : ℂ) (c : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ))
    (hB : ∀ u v, bilinC f 0 u v = slBil (c : ℂ) (g : ℂ) u v)
    (hC : ∀ u v z, trilinC f 0 u v z = slTri (c : ℂ) (g : ℂ) u v z)
    (hA : IsUnit (jacobianC f 0).det) (h2' : IsUnit (shift2 (jacobianC f 0) ω).det) :
    firstLyapunov f 0 ω (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        ((starRingEnd ℂ (slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))⁻¹ •
          sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      -(9 * ω ^ 7 * (ω ^ 2 + d ^ 2) * ((σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2) /
        ((slicePairRe d σ w ω ^ 2 + slicePairIm d σ w ω ^ 2) *
          (sliceShiftRe d σ w ω ^ 2 + sliceShiftIm d σ w ω ^ 2))) * sliceBautin d σ w ω := by
  have h1c : (c : ℂ) * ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) =
      (ω : ℂ) ^ 2 * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d) := by exact_mod_cast h1
  have h2c : (c : ℂ) * g * w = (ω : ℂ) ^ 2 * (((d : ℂ) + c) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 -
      (ω : ℂ) ^ 2) + 2 * σ * (d * c - (ω : ℂ) ^ 2)) := by exact_mod_cast h2
  have hQ := sl_Qc_pos hG h1 h2
  have hQc : ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) ≠ 0 := by
    have e : ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) =
        ((d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    exact_mod_cast hQ.ne'
  have hCr := sl_pairRe_pos hω hw hd hσ hQ
  have eC := sl_C (j := I) h1c
  have eX := sl_X (j := I) h1c h2c
  have e1 := sl_Y1 I_sq h1c h2c
  have e2 := sl_Y2 I_sq h1c h2c
  have e3 := sl_Y3 I_sq h1c h2c
  rw [slicePairRe_cast, slicePairIm_cast] at eC
  rw [sliceShiftRe_cast, sliceShiftIm_cast] at eX
  rw [slY1r_cast, slY1i_cast] at e1
  rw [slY2r_cast, slY2i_cast] at e2
  rw [slY3r_cast, slY3i_cast] at e3
  have hCh : ((slicePairRe d σ w ω : ℝ) : ℂ) + ((slicePairIm d σ w ω : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hχ := sl_chi_ne hω h1 h2 k4 k0 kg
  have hXh : ((sliceShiftRe d σ w ω : ℝ) : ℂ) + ((sliceShiftIm d σ w ω : ℝ) : ℂ) * I ≠ 0 := by
    rw [← eX]
    exact mul_ne_zero hQc hχ
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hc0 : slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I ≠ 0 := by
    intro h
    rw [h, mul_zero] at eC
    exact hCh eC.symm
  have hq : star (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I := sl_star_Q d σ w ω
  have hr : jacobianC f 0 *ᵥ ((w : ℂ)⁻¹ • slR (σ : ℂ) (w : ℂ) (ω : ℂ)) =
      bilinC f 0 (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        (star (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)) := by
    rw [Matrix.mulVec_smul, hJ, sl_r I_sq, hB, hq, smul_smul, inv_mul_cancel₀ hw', one_smul]
  have hs : shift2 (jacobianC f 0) ω *ᵥ (((w : ℂ) * slChi (d : ℂ) (c : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ)
      (ω : ℂ) I)⁻¹ • slS (d : ℂ) (c : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      bilinC f 0 (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        (sliceVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) := by
    rw [Matrix.mulVec_smul, hJ, shift2, sl_S I_sq, hB, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero hw' hχ), one_smul]
  have hpair : ∀ (z : ℂ) (v : Fin 5 → ℂ),
      pairing ((starRingEnd ℂ z)⁻¹ • sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) v =
        z⁻¹ * (sliceVecP (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ v) := by
    intro z v
    rw [← sl_star_Pt, ← pairing_eq_dotProduct]
    simp [pairing_apply, Finset.mul_sum, mul_assoc]
  rw [firstLyapunov_eq_of_solve hA h2' hr hs, (bilinC f 0 _).map_smul, (bilinC f 0 _).map_smul,
    hC, hB, hB, hq, (pairing _).map_smul, (pairing _).map_smul, hpair, hpair, hpair, smul_eq_mul,
    smul_eq_mul, sl_alg hQc hw' hCh hXh e1 e2 e3 eC eX]
  have hN : (w : ℂ) * (((sliceShiftRe d σ w ω : ℝ) : ℂ) + ((sliceShiftIm d σ w ω : ℝ) : ℂ) * I) *
        (((slY1r d σ w ω : ℝ) : ℂ) + ((slY1i d σ w ω : ℝ) : ℂ) * I) -
      2 * (((sliceShiftRe d σ w ω : ℝ) : ℂ) + ((sliceShiftIm d σ w ω : ℝ) : ℂ) * I) *
        (((slY2r d σ w ω : ℝ) : ℂ) + ((slY2i d σ w ω : ℝ) : ℂ) * I) +
      (((slY3r d σ w ω : ℝ) : ℂ) + ((slY3i d σ w ω : ℝ) : ℂ) * I) =
      ((slNr d σ w ω : ℝ) : ℂ) + ((slNi d σ w ω : ℝ) : ℂ) * I := by
    simp only [slNr, slNi]
    push_cast
    linear_combination ((w : ℂ) * ((sliceShiftIm d σ w ω : ℝ) : ℂ) * ((slY1i d σ w ω : ℝ) : ℂ) -
      2 * ((sliceShiftIm d σ w ω : ℝ) : ℂ) * ((slY2i d σ w ω : ℝ) : ℂ)) * I_sq
  have hD : (((slicePairRe d σ w ω : ℝ) : ℂ) + ((slicePairIm d σ w ω : ℝ) : ℂ) * I) *
      (((sliceShiftRe d σ w ω : ℝ) : ℂ) + ((sliceShiftIm d σ w ω : ℝ) : ℂ) * I) =
      ((slDr d σ w ω : ℝ) : ℂ) + ((slDi d σ w ω : ℝ) : ℂ) * I := by
    simp only [slDr, slDi]
    push_cast
    linear_combination (((slicePairIm d σ w ω : ℝ) : ℂ) * ((sliceShiftIm d σ w ω : ℝ) : ℂ)) * I_sq
  have hDD : slDr d σ w ω ^ 2 + slDi d σ w ω ^ 2 =
      (slicePairRe d σ w ω ^ 2 + slicePairIm d σ w ω ^ 2) *
        (sliceShiftRe d σ w ω ^ 2 + sliceShiftIm d σ w ω ^ 2) := by
    simp only [slDr, slDi]
    ring
  have hC2 : slicePairRe d σ w ω ^ 2 + slicePairIm d σ w ω ^ 2 ≠ 0 := by positivity
  have hX2 : sliceShiftRe d σ w ω ^ 2 + sliceShiftIm d σ w ω ^ 2 ≠ 0 := by
    intro h
    apply hXh
    have hr : sliceShiftRe d σ w ω = 0 := by nlinarith [sq_nonneg (sliceShiftIm d σ w ω)]
    have hi : sliceShiftIm d σ w ω = 0 := by nlinarith [sq_nonneg (sliceShiftRe d σ w ω)]
    rw [hr, hi]
    simp
  rw [hN, hD, sl_re _ _ _ _ _ hw.ne' (by rw [hDD]; exact mul_ne_zero hC2 hX2), sl_key, hDD]
  field_simp
  ring

/-- The pairing `⟨p̃, q⟩` of the slice does not vanish at a slice Hopf point. -/
@[tmio M, powerlib_domain] private theorem sl_pairing_ne {d c g σ w ω : ℝ} (hω : 0 < ω)
    (hw : 0 < w) (hd : 0 < d) (hσ : 0 ≤ σ) (hG : 0 < c * g * w)
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * ω ^ 2) =
      ω ^ 2 * (σ ^ 2 + w ^ 2 - ω ^ 2 + 2 * σ * d))
    (h2 : c * g * w = ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2))) :
    slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I ≠ 0 := by
  have h1c : (c : ℂ) * ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) =
      (ω : ℂ) ^ 2 * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d) := by exact_mod_cast h1
  have h2c : (c : ℂ) * g * w = (ω : ℂ) ^ 2 * (((d : ℂ) + c) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 -
      (ω : ℂ) ^ 2) + 2 * σ * (d * c - (ω : ℂ) ^ 2)) := by exact_mod_cast h2
  have hCr := sl_pairRe_pos hω hw hd hσ (sl_Qc_pos hG h1 h2)
  have eC := sl_C (j := I) h1c
  rw [slicePairRe_cast, slicePairIm_cast] at eC
  intro h
  rw [h, mul_zero] at eC
  have := congrArg Complex.re eC
  simp at this
  linarith

/-! ## The zero-current slice of the model -/

/-- **The zero-current slice**: operating angle `δ* = 0` and grid voltage `V = E`, so that the
operating current `i_s(0) = (E − V)/(R + jX)` vanishes (and balance forces `P_ref = 0`). -/
def Model.OnSlice (m : Model) : Prop := m.δ = 0 ∧ m.g.V = m.g.E

/-- The diagonal scaling `(1, 1, a, b, b)`. -/
private def slDiag (a b : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![1, 1, a, b, b]

@[tmio M, powerlib_domain] private theorem slDiag_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (x : State 5) :
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a b)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a⁻¹ b⁻¹) x) = x := by
  ext i
  fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, slDiag, Matrix.diagonal_apply, ha, hb]

/-- The scaling `(δ, ω, P_f, i_d, i_q) ↦ (δ, ω, a P_f, b i_d, b i_q)` as a linear isomorphism. -/
private def slScale (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : State 5 ≃L[ℝ] State 5 :=
  ContinuousLinearEquiv.equivOfInverse (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a b))
    (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a⁻¹ b⁻¹))
    (fun x => by simpa using slDiag_inv (inv_ne_zero ha) (inv_ne_zero hb) x)
    (slDiag_inv ha hb)

/-- **The slice scaling of a vector**: `(v₀, v₁, a v₂, b v₃, b v₄)`. -/
def sliceScale (a b : ℝ) (v : Fin 5 → ℂ) : Fin 5 → ℂ := ![v 0, v 1, a * v 2, b * v 3, b * v 4]

@[tmio M, powerlib_domain] private theorem slScale_cmat {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 5 → ℂ) :
    cmat (slScale a b ha hb : State 5 →L[ℝ] State 5) *ᵥ v = sliceScale a b v := by
  rw [show (slScale a b ha hb : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a b) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [sliceScale, slDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

@[tmio M, powerlib_domain] private theorem slScale_symm_cmat {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 5 → ℂ) :
    cmat ((slScale a b ha hb).symm : State 5 →L[ℝ] State 5) *ᵥ v = sliceScale a⁻¹ b⁻¹ v := by
  rw [show ((slScale a b ha hb).symm : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a⁻¹ b⁻¹) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [sliceScale, slDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

@[tmio M, powerlib_domain] private theorem slScale_symm_transpose {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) (v : Fin 5 → ℂ) :
    (cmat ((slScale a b ha hb).symm : State 5 →L[ℝ] State 5))ᵀ *ᵥ v = sliceScale a⁻¹ b⁻¹ v := by
  rw [show ((slScale a b ha hb).symm : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a⁻¹ b⁻¹) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [sliceScale, slDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

@[tmio M, powerlib_domain] private theorem slScale_mul_symm {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    cmat (slScale a b ha hb : State 5 →L[ℝ] State 5) *
      cmat ((slScale a b ha hb).symm : State 5 →L[ℝ] State 5) = 1 := by
  rw [← cmat_comp, (slScale a b ha hb).coe_comp_coe_symm, cmat_id]

@[tmio M, powerlib_domain] private theorem sl_model_hess (m : Model) :
    hess m.field 0 = hess m.g.field m.point := by
  funext k i j
  show iteratedFDeriv ℝ 2 (fun z => m.g.field (z + m.point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, hess]

@[tmio M, powerlib_domain] private theorem sl_model_third (m : Model) :
    third m.field 0 = third m.g.field m.point := by
  funext k i j l
  show iteratedFDeriv ℝ 3 (fun z => m.g.field (z + m.point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, third]

@[tmio M, powerlib_domain] private theorem sl_is_zero {m : Model} (hs : m.OnSlice) :
    m.g.is m.δ = 0 := by
  rw [hs.1, Network.is, hs.2]
  simp

/-- **The slice in the scaled coordinates**: for a physical model on the slice, in the coordinates
`(δ, ω, P_f/M, (L/E) i_d, (L/E) i_q)` the Jacobian, the second and the third derivative at the
operating point are the slice patterns with `d = D/M`, `c = ω_c`, `g = E²/(M L)`, `σ = R/L`,
`w = ω₀`. -/
@[tmio M, powerlib_domain] private theorem sl_data {m : Model} (hp : Meets m .physical)
    (hs : m.OnSlice) :
    jacobianC (fun z => slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hp.2.1.ne')
        (div_ne_zero hp.1.L.ne' hp.1.E.ne') (m.field ((slScale m.g.M⁻¹ (m.g.L / m.g.E)
          (inv_ne_zero hp.2.1.ne') (div_ne_zero hp.1.L.ne' hp.1.E.ne')).symm z))) 0 =
        slJ ((m.g.D / m.g.M : ℝ) : ℂ) (m.g.ωc : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
          ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) ∧
      (∀ u v, bilinC (fun z => slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hp.2.1.ne')
        (div_ne_zero hp.1.L.ne' hp.1.E.ne') (m.field ((slScale m.g.M⁻¹ (m.g.L / m.g.E)
          (inv_ne_zero hp.2.1.ne') (div_ne_zero hp.1.L.ne' hp.1.E.ne')).symm z))) 0 u v =
        slBil (m.g.ωc : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) u v) ∧
      (∀ u v z, trilinC (fun z => slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hp.2.1.ne')
        (div_ne_zero hp.1.L.ne' hp.1.E.ne') (m.field ((slScale m.g.M⁻¹ (m.g.L / m.g.E)
          (inv_ne_zero hp.2.1.ne') (div_ne_zero hp.1.L.ne' hp.1.E.ne')).symm z))) 0 u v z =
        slTri (m.g.ωc : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) u v z) := by
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  set T := slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hM) (div_ne_zero hL hE) with hTdef
  have hinv : ∀ u : Fin 5 → ℂ, cmat (T : State 5 →L[ℝ] State 5) *ᵥ
      (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, slScale_mul_symm, Matrix.one_mulVec]
  have hi := sl_is_zero hs
  have hi0 : m.g.is 0 = 0 := by rw [← hs.1]; exact hi
  have hMc : (m.g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hLc : (m.g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hEc : (m.g.E : ℂ) ≠ 0 := by exact_mod_cast hE
  have hX : (m.g.X : ℂ) = m.g.ω0 * m.g.L := by simp [Network.X]
  have p0 : m.point 0 = 0 := by simp [Model.point, qss, hs.1]
  have p3 : m.point 3 = 0 := by simp [Model.point, qss, hi]
  have p4 : m.point 4 = 0 := by simp [Model.point, qss, hi]
  have hB0 : ∀ u v, bilinC m.field 0 u v = ![0, 0, (m.g.ωc : ℂ) * m.g.E * (u 0 * v 4 + u 4 * v 0),
      -((m.g.E / m.g.L : ℝ) : ℂ) * (u 0 * v 0), 0] := fun u v => by
    rw [show bilinC m.field 0 = bilinC m.g.field m.point by unfold bilinC; rw [sl_model_hess],
      bilinC_field_eq, p0, p3, p4]
    ext k
    fin_cases k <;> simp [Network.power_eq]
  have hC0 : ∀ u v z, trilinC m.field 0 u v z = ![0, 0,
      -((m.g.ωc : ℂ) * m.g.E * (u 0 * v 0 * z 3 + u 0 * v 3 * z 0 + u 3 * v 0 * z 0)), 0,
      -((m.g.E / m.g.L : ℝ) : ℂ) * (u 0 * v 0 * z 0)] := fun u v z => by
    rw [show trilinC m.field 0 = trilinC m.g.field m.point by unfold trilinC; rw [sl_model_third],
      trilinC_field_eq, p0, p3, p4]
    ext k
    fin_cases k <;> simp [Network.reactive_eq]
  refine ⟨?_, fun u v => ?_, fun u v z => ?_⟩
  · have h := jacobianC_conj T m.field 0
    rw [map_zero] at h
    rw [h, Model.jacobianC_field, show (T : State 5 →L[ℝ] State 5) = Matrix.toEuclideanCLM
      (n := Fin 5) (𝕜 := ℝ) (slDiag m.g.M⁻¹ (m.g.L / m.g.E)) from rfl,
      show (T.symm : State 5 →L[ℝ] State 5) = Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
        (slDiag m.g.M⁻¹⁻¹ (m.g.L / m.g.E)⁻¹) from rfl, cmat_toEuclideanCLM, cmat_toEuclideanCLM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slJ, slDiag, Matrix.mul_apply, Model.jac, jacobian, hi0,
      hs.1, Network.reactive_eq, Matrix.diagonal_apply, hX]
    all_goals field_simp
  · have h := bilinC_conj T m.field 0 (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ u)
      (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ v)
    rw [hinv, hinv, map_zero] at h
    rw [h, slScale_symm_cmat, slScale_symm_cmat, hB0, slScale_cmat]
    ext k
    fin_cases k <;> simp [slBil, sliceScale]
    all_goals field_simp
  · have h := trilinC_conj T m.field 0 (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ u)
      (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ v) (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ z)
    rw [hinv, hinv, hinv, map_zero] at h
    rw [h, slScale_symm_cmat, slScale_symm_cmat, slScale_symm_cmat, hC0, slScale_cmat]
    ext k
    fin_cases k <;> simp [slTri, sliceScale]
    all_goals field_simp

@[tmio M, powerlib_domain] private theorem slScale_transpose {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 5 → ℂ) :
    (cmat (slScale a b ha hb : State 5 →L[ℝ] State 5))ᵀ *ᵥ v = sliceScale a b v := by
  rw [show (slScale a b ha hb : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (slDiag a b) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [sliceScale, slDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

@[tmio M, powerlib_domain] private theorem sliceScale_sliceScale (a b a' b' : ℝ)
    (v : Fin 5 → ℂ) : sliceScale a b (sliceScale a' b' v) = sliceScale (a * a') (b * b') v := by
  ext i
  fin_cases i <;> simp [sliceScale] <;> ring

@[tmio M, powerlib_domain] private theorem sliceScale_one (v : Fin 5 → ℂ) :
    sliceScale 1 1 v = v := by
  ext i
  fin_cases i <;> simp [sliceScale]

/-- The quintic coefficients on the slice, in the slice atoms `d = D/M`, `c = ω_c`,
`g = E²/(M L)`, `σ = R/L`, `w = ω₀` (`Q = 0`). -/
@[tmio M, powerlib_domain] private theorem sl_coeffs {m : Model} (hp : Meets m .physical)
    (hs : m.OnSlice) :
    m.Q = 0 ∧
    m.g.coeff4 = m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L) ∧
    m.g.coeff3 = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 + 2 * (m.g.R / m.g.L) *
      (m.g.ωc + m.g.D / m.g.M) + m.g.ωc * (m.g.D / m.g.M) ∧
    m.g.coeff2 m.Q = 2 * m.g.ωc * (m.g.D / m.g.M) * (m.g.R / m.g.L) +
      (m.g.ωc + m.g.D / m.g.M) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) ∧
    m.g.coeff1 m.Q = m.g.ωc * (m.g.D / m.g.M) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) ∧
    m.g.coeff0 m.Q = m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L)) * m.g.ω0 := by
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hQ : m.Q = 0 := by
    rw [Model.Q, Network.qssReactive, sl_is_zero hs, hs.1]
    simp [Network.reactive_eq]
  have hXL : m.g.X / m.g.L = m.g.ω0 := by simp only [Network.X]; field_simp
  have hρ : m.g.ρ = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 := by
    rw [Network.ρ, hXL, Network.σ]
  refine ⟨hQ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [coeff4, Network.σ]; ring
  · rw [coeff3, hρ, Network.σ]; ring
  · rw [coeff2, hρ, Network.σ, hQ]; ring
  · rw [coeff1, VSM.coeff1, hQ, show m.g.toVSM.ρ = m.g.ρ from rfl, hρ,
      show m.g.toVSM.D = m.g.D from rfl, show m.g.toVSM.M = m.g.M from rfl]
    field_simp
    ring
  · rw [coeff0, VSM.coeff0, hQ, show m.g.toVSM.E = m.g.E from rfl,
      show m.g.toVSM.X = m.g.X from rfl, show m.g.toVSM.L = m.g.L from rfl,
      show m.g.toVSM.M = m.g.M from rfl, Network.X]
    field_simp
    ring

/-- The Hopf relations of a slice model in the slice atoms. -/
@[tmio M, powerlib_domain] private theorem sl_hopf {m : Model} (hp : Meets m .physical)
    (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    m.g.ωc * (m.g.D / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) -
        2 * (m.g.R / m.g.L) * ω ^ 2) =
      ω ^ 2 * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2 + 2 * (m.g.R / m.g.L) * (m.g.D / m.g.M)) ∧
    m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L)) * m.g.ω0 = ω ^ 2 * ((m.g.D / m.g.M + m.g.ωc) *
      ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) + 2 * (m.g.R / m.g.L) *
        (m.g.D / m.g.M * m.g.ωc - ω ^ 2)) ∧
    0 < m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L) ∧
    0 < 2 * m.g.ωc * (m.g.D / m.g.M) * (m.g.R / m.g.L) + (m.g.ωc + m.g.D / m.g.M) *
      ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) - (m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L)) * ω ^ 2 ∧
    2 * m.g.ωc * (m.g.D / m.g.M) * (m.g.R / m.g.L) + (m.g.ωc + m.g.D / m.g.M) *
      ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) - (m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L)) * ω ^ 2 <
      (m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L)) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 +
        2 * (m.g.R / m.g.L) * (m.g.ωc + m.g.D / m.g.M) + m.g.ωc * (m.g.D / m.g.M) - ω ^ 2) := by
  obtain ⟨-, c4, c3, c2, c1, c0⟩ := sl_coeffs hp hs
  obtain ⟨-, e1, e2, e4, e0, eg⟩ := hH
  rw [c3, c1] at e1
  rw [c4, c2, c0] at e2
  rw [c4] at e4
  rw [c2, c4] at e0
  rw [c2, c4, c3] at eg
  refine ⟨by linear_combination e1, by linear_combination e2, e4, e0, eg⟩

@[tmio M, powerlib_domain] private theorem sl_equilibrium {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) : m.field 0 = 0 := by
  have h' := (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne'
    hp.1.absSq_pos.ne').mpr hb
  simpa [Model.field] using h'

/-- The determinants of the Jacobian and of `2iω − J` are units in the scaled coordinates. -/
@[tmio M, powerlib_domain] private theorem sl_isUnit {m : Model} (hp : Meets m .physical)
    {ω : ℝ} (hH : m.HopfAt ω) :
    IsUnit (jacobianC (fun z => slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hp.2.1.ne')
        (div_ne_zero hp.1.L.ne' hp.1.E.ne') (m.field ((slScale m.g.M⁻¹ (m.g.L / m.g.E)
          (inv_ne_zero hp.2.1.ne') (div_ne_zero hp.1.L.ne' hp.1.E.ne')).symm z))) 0).det ∧
      IsUnit (shift2 (jacobianC (fun z => slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hp.2.1.ne')
        (div_ne_zero hp.1.L.ne' hp.1.E.ne') (m.field ((slScale m.g.M⁻¹ (m.g.L / m.g.E)
          (inv_ne_zero hp.2.1.ne') (div_ne_zero hp.1.L.ne' hp.1.E.ne')).symm z))) 0) ω).det := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_hopfAt hH
  obtain ⟨hA, h2⟩ := Dynamics.CenterManifold.isUnit_det_of_charpoly hH.1.ne' hchar hr
  set T := slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hp.2.1.ne')
    (div_ne_zero hp.1.L.ne' hp.1.E.ne')
  have hTS := slScale_mul_symm (inv_ne_zero hp.2.1.ne') (div_ne_zero hp.1.L.ne' hp.1.E.ne')
  have hdet : ∀ X : Matrix (Fin 5) (Fin 5) ℂ, (cmat (T : State 5 →L[ℝ] State 5) * X *
      cmat (T.symm : State 5 →L[ℝ] State 5)).det = X.det := fun X => by
    have h := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at h
    rw [Matrix.det_mul, Matrix.det_mul]
    linear_combination X.det * h
  have h0 := jacobianC_conj T m.field 0
  rw [map_zero] at h0
  rw [h0]
  refine ⟨by rw [hdet]; exact hA, ?_⟩
  have hs : shift2 (cmat (T : State 5 →L[ℝ] State 5) * jacobianC m.field 0 *
      cmat (T.symm : State 5 →L[ℝ] State 5)) ω = cmat (T : State 5 →L[ℝ] State 5) *
        shift2 (jacobianC m.field 0) ω * cmat (T.symm : State 5 →L[ℝ] State 5) := by
    rw [shift2, shift2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hTS]
  rw [hs, hdet]
  exact h2

/-- **The critical right eigenvector of a slice model** at the frequency `ω`: the slice vector
`Line.VSMLPF.sliceVecQ` (`d = D/M`, `σ = R/L`, `w = ω₀`) read in the model coordinates
(`P_f = M y₂`, `i = (E/L) y`). -/
def Model.sliceQ (m : Model) (ω : ℝ) : Fin 5 → ℂ :=
  sliceScale m.g.M (m.g.E / m.g.L) (sliceVecQ ((m.g.D / m.g.M : ℝ) : ℂ)
    ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I)

/-- **The critical left eigenvector of a slice model** at the frequency `ω` (`⟨p, q⟩ = 1`;
`c = ω_c`). -/
def Model.sliceP (m : Model) (ω : ℝ) : Fin 5 → ℂ :=
  sliceScale m.g.M⁻¹ (m.g.L / m.g.E)
    ((starRingEnd ℂ (slicePairing ((m.g.D / m.g.M : ℝ) : ℂ) (m.g.ωc : ℂ)
      ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I))⁻¹ •
      sliceVecP ((m.g.D / m.g.M : ℝ) : ℂ) (m.g.ωc : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ)
        (ω : ℂ) I)

@[tmio M, powerlib_domain] private theorem sl_pos {m : Model} (hp : Meets m .physical) :
    0 < m.g.D / m.g.M ∧ 0 ≤ m.g.R / m.g.L ∧ 0 < m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L)) * m.g.ω0 :=
        by
  obtain ⟨hN, hM, hD, hc⟩ := hp
  have := hN.E
  have := hN.L
  have := hN.ω0
  refine ⟨div_pos hD hM, div_nonneg hN.R hN.L.le, by positivity⟩

/-- **The critical pair of a slice model**: at a Hopf point of its quintic at `ω`, a balanced
physical model on the zero-current slice has the critical pair (`Model.sliceQ`,
`Model.sliceP`) (the slice pattern in the scaled coordinates,
`NormalForm.LyapunovCoefficient.isCriticalPair_conj`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isCriticalPair_slice {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    IsCriticalPair m.field 0 ω (m.sliceQ ω) (m.sliceP ω) := by
  obtain ⟨h1, h2, k4, k0, kg⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  obtain ⟨hJ, -, -⟩ := sl_data hp hs
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  set T := slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hM) (div_ne_zero hL hE)
  have hf : (fun z => T (m.field (T.symm z))) 0 = 0 := by simp [sl_equilibrium hp hb]
  have hc := sl_isCriticalPair hH.1 h1 h2 (sl_pairing_ne hH.1 hp.1.ω0 hd hσ hG h1 h2) hf hJ
  have h := isCriticalPair_conj T.symm hc
  have e : (fun z => T.symm ((fun z => T (m.field (T.symm z))) (T.symm.symm z))) = m.field := by
    funext z
    simp
  rw [e, map_zero, slScale_symm_cmat, ContinuousLinearEquiv.symm_symm, slScale_transpose,
    inv_inv, inv_div] at h
  exact h

/-- **The first Lyapunov coefficient on the zero-current slice in closed form**: for a physical
model on the slice (`δ* = 0`, `V = E`) with a Hopf point of its quintic at `ω`
(`Line.VSMLPF.Model.HopfAt`), at (`Model.sliceQ`, `Model.sliceP`),
`ℓ₁ = −9 ω⁷ (ω² + d²) ((σ² + w² − ω²)² + 4σ²ω²) 𝔅 / (|Ĉ|² |χ̂|²)`, `d = D/M`, `σ = R/L`,
`w = ω₀`, `𝔅 = Line.VSMLPF.sliceBautin d σ w ω`, `Ĉ = slicePairRe + i slicePairIm`,
`χ̂ = sliceShiftRe + i sliceShiftIm` (the pairing `⟨p̃, q⟩` and `χ(2iω)` times
`Q_c = d (σ² + w² − ω²) − 2σω²`, the filter bandwidth `ω_c` and the gain `E²/(M L)` eliminated by
the two Hopf relations). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.firstLyapunov_slice {m : Model} (hp : Meets m .physical)
    (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    firstLyapunov m.field 0 ω (m.sliceQ ω) (m.sliceP ω) =
      -(9 * ω ^ 7 * (ω ^ 2 + (m.g.D / m.g.M) ^ 2) *
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) /
        ((slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
            slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) *
          (sliceShiftRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
            sliceShiftIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2))) *
        sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω := by
  obtain ⟨h1, h2, k4, k0, kg⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  obtain ⟨hJ, hB, hC⟩ := sl_data hp hs
  obtain ⟨hA, h2'⟩ := sl_isUnit hp hH
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  set T := slScale m.g.M⁻¹ (m.g.L / m.g.E) (inv_ne_zero hM) (div_ne_zero hL hE)
  rw [← firstLyapunov_conj T m.field 0 ω (m.sliceQ ω) (m.sliceP ω), map_zero, slScale_cmat,
    slScale_symm_transpose, Model.sliceQ, Model.sliceP, sliceScale_sliceScale,
    sliceScale_sliceScale, inv_mul_cancel₀ hM, div_mul_div_cancel₀ hE, div_self hL, inv_inv,
    mul_inv_cancel₀ hM, inv_div, div_mul_div_cancel₀ hL, div_self hE, sliceScale_one,
    sliceScale_one]
  exact sl_firstLyapunov hH.1 hp.1.ω0 hd hσ hG h1 h2 k4 k0 kg hJ hB hC hA h2'

/-- The prefactor of the closed form is positive at a slice Hopf point. -/
@[tmio M, powerlib_domain] private theorem sl_prefactor_pos {m : Model} (hp : Meets m .physical)
    (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    0 < 9 * ω ^ 7 * (ω ^ 2 + (m.g.D / m.g.M) ^ 2) *
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) /
        ((slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
            slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) *
          (sliceShiftRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
            sliceShiftIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2)) := by
  obtain ⟨h1, h2, k4, k0, kg⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  have hω := hH.1
  have hQ := sl_Qc_pos hG h1 h2
  have hCr := sl_pairRe_pos hω hp.1.ω0 hd hσ hQ
  have hτ : 0 < (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2 := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonneg hσ (sq_nonneg ω)]
  have hX : 0 < sliceShiftRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
      sliceShiftIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 := by
    rcases (add_nonneg (sq_nonneg (sliceShiftRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω))
      (sq_nonneg (sliceShiftIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω))).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1c : (m.g.ωc : ℂ) * (((m.g.D / m.g.M : ℝ) : ℂ) * (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 +
          (m.g.ω0 : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * ((m.g.R / m.g.L : ℝ) : ℂ) * ω ^ 2) =
          (ω : ℂ) ^ 2 * (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 - (ω : ℂ) ^ 2 +
            2 * ((m.g.R / m.g.L : ℝ) : ℂ) * ((m.g.D / m.g.M : ℝ) : ℂ)) := by exact_mod_cast h1
      have h2c : (m.g.ωc : ℂ) * ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) * m.g.ω0 =
          (ω : ℂ) ^ 2 * ((((m.g.D / m.g.M : ℝ) : ℂ) + m.g.ωc) * (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 +
            (m.g.ω0 : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * ((m.g.R / m.g.L : ℝ) : ℂ) *
              (((m.g.D / m.g.M : ℝ) : ℂ) * m.g.ωc - (ω : ℂ) ^ 2)) := by exact_mod_cast h2
      have eX := sl_X (j := I) h1c h2c
      rw [sliceShiftRe_cast, sliceShiftIm_cast] at eX
      have hr : sliceShiftRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω = 0 := by
        nlinarith [sq_nonneg (sliceShiftIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω)]
      have hi : sliceShiftIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω = 0 := by
        nlinarith [sq_nonneg (sliceShiftRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω)]
      rw [hr, hi] at eX
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at eX
      have hQc : ((m.g.D / m.g.M : ℝ) : ℂ) * (((m.g.R / m.g.L : ℝ) : ℂ) ^ 2 + (m.g.ω0 : ℂ) ^ 2 -
          (ω : ℂ) ^ 2) - 2 * ((m.g.R / m.g.L : ℝ) : ℂ) * ω ^ 2 ≠ 0 := by
        exact_mod_cast hQ.ne'
      exact mul_ne_zero hQc (sl_chi_ne hω h1 h2 k4 k0 kg) eX
  have hC : 0 < slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
      slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 := by positivity
  positivity

/-- **The sign law on the zero-current slice**: for every critical pair at a Hopf point of a
balanced physical slice model, `sign ℓ₁ = −sign 𝔅(D/M, R/L, ω₀, ω)`
(`Line.VSMLPF.sliceBautin`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_slice {m : Model}
    (hp : Meets m .physical) (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω)
    {q p : Fin 5 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    SignType.sign (firstLyapunov m.field 0 ω q p) =
      -SignType.sign (sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) := by
  rw [m.sign_firstLyapunov_eq_of_hopfAt hH (m.isCriticalPair_slice hp hb hs hH) hcp,
    m.firstLyapunov_slice hp hs hH, sign_mul,
    sign_neg (neg_neg_of_pos (sl_prefactor_pos hp hs hH))]
  simp

/-- **Supercritical slice Hopf points are locally asymptotically stable**: a balanced physical
slice model with a Hopf point at `ω` and `𝔅(D/M, R/L, ω₀, ω) > 0` is locally asymptotically
stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_sliceBautin_pos
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ}
    (hH : m.HopfAt ω) (hB : 0 < sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have hcp := m.isCriticalPair_slice hp hb hs hH
  have hs' := m.sign_firstLyapunov_slice hp hb hs hH hcp
  rw [sign_pos hB] at hs'
  exact mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg m hH hcp
    (sign_eq_neg_one_iff.mp hs')

/-- **Subcritical slice Hopf points are unstable**: a balanced physical slice model with a Hopf
point at `ω` and `𝔅(D/M, R/L, ω₀, ω) < 0` is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_sliceBautin_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω)
    (hB : sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hcp := m.isCriticalPair_slice hp hb hs hH
  have hs' := m.sign_firstLyapunov_slice hp hb hs hH hcp
  rw [sign_neg hB, neg_neg] at hs'
  exact mem_den_unstable_of_firstLyapunov_pos m hH hcp (sign_eq_one_iff.mp hs')

/-! ## Complete local asymptotic membership on the slice -/

/-- The boundary `Δ₄ = 0` of the quintic Routh region with `a₀, Δ₂, Δ₃ > 0` is a Hopf point:
`ω = √(a₀ Δ₂/Δ₃)` solves both frequency equations and the cubic cofactor is Hurwitz. -/
@[tmio M, powerlib_domain] private theorem sl_quintic_boundary {a4 a3 a2 a1 a0 : ℝ}
    (h0 : 0 < a0) (d2 : 0 < Criteria.quinticHurwitzDet2 a4 a3 a2)
    (d3 : 0 < Criteria.quinticHurwitzDet3 a4 a3 a2 a1 a0)
    (d4 : Criteria.quinticHurwitzDet4 a4 a3 a2 a1 a0 = 0) {ω : ℝ}
    (hω : ω = Real.sqrt (a0 * Criteria.quinticHurwitzDet2 a4 a3 a2 /
      Criteria.quinticHurwitzDet3 a4 a3 a2 a1 a0)) :
    0 < ω ∧ ω ^ 4 - a3 * ω ^ 2 + a1 = 0 ∧ a4 * ω ^ 4 - a2 * ω ^ 2 + a0 = 0 ∧
      0 < a2 - a4 * ω ^ 2 ∧ a2 - a4 * ω ^ 2 < a4 * (a3 - ω ^ 2) := by
  subst hω
  unfold Criteria.quinticHurwitzDet4 Criteria.quinticHurwitzDet3 Criteria.quinticHurwitzDet2
    at d4
  unfold Criteria.quinticHurwitzDet3 Criteria.quinticHurwitzDet2 at d3 ⊢
  unfold Criteria.quinticHurwitzDet2 at d2
  set D2 := a4 * a3 - a2 with hD2
  set D3 := a2 * D2 - a4 * (a4 * a1 - a0) with hD3
  set x := a0 * D2 / D3 with hx
  have hxpos : 0 < x := by positivity
  have hxD : x * D3 = a0 * D2 := by rw [hx]; field_simp
  have e1 : x ^ 2 - a3 * x + a1 = 0 := by
    have h : D3 ^ 2 * (x ^ 2 - a3 * x + a1) = 0 := by
      rw [show D3 ^ 2 * (x ^ 2 - a3 * x + a1) = (x * D3) ^ 2 - a3 * D3 * (x * D3) + a1 * D3 ^ 2
        by ring, hxD, hD3, hD2]
      linear_combination (-a1 * a4 ^ 2 - a2 ^ 2 + a2 * a3 * a4) * d4
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 d3.ne')
  have e2 : a4 * x ^ 2 - a2 * x + a0 = 0 := by
    have h : D3 ^ 2 * (a4 * x ^ 2 - a2 * x + a0) = 0 := by
      rw [show D3 ^ 2 * (a4 * x ^ 2 - a2 * x + a0) =
        a4 * (x * D3) ^ 2 - a2 * D3 * (x * D3) + a0 * D3 ^ 2 by ring, hxD, hD3, hD2]
      linear_combination (-a0 * a4 ^ 2) * d4
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 d3.ne')
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hs4 : Real.sqrt x ^ 4 = x ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2]
  refine ⟨Real.sqrt_pos.mpr hxpos, ?_, ?_, ?_, ?_⟩
  · rw [hs4, hs2]; exact e1
  · rw [hs4, hs2]; exact e2
  · rw [hs2]
    by_contra hn
    push Not at hn
    nlinarith
  · rw [hs2]
    linarith

/-- **The Hopf frequency of a slice model read from its coefficients**,
`ω = √(a₀ Δ₂/Δ₃)` (`Δ₂`, `Δ₃` the Hurwitz determinants of the quintic at the operating point): on
the boundary `Δ₄ = 0` with `Δ₂, Δ₃ > 0` it is the frequency of the critical pair `±iω`. -/
def Model.sliceOmega (m : Model) : ℝ :=
  Real.sqrt (m.g.coeff0 m.Q * Criteria.quinticHurwitzDet2 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) /
    Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q))

/-- **The Hopf frequency read from the coefficients**: a physical slice model on the boundary
`Δ₄ = 0` of the quintic Routh region with `Δ₂, Δ₃ > 0` has a Hopf point at
`Line.VSMLPF.Model.sliceOmega` (`a₀ = c g w > 0` on the slice). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.hopfAt_sliceOmega {m : Model} (hp : Meets m .physical)
    (hs : m.OnSlice)
    (d2 : 0 < Criteria.quinticHurwitzDet2 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q))
    (d3 : 0 < Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q)
      (m.g.coeff1 m.Q) (m.g.coeff0 m.Q))
    (d4 : Criteria.quinticHurwitzDet4 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) = 0) :
    m.HopfAt m.sliceOmega := by
  obtain ⟨-, c4, -, -, -, c0⟩ := sl_coeffs hp hs
  obtain ⟨hd0, hσ, hG⟩ := sl_pos hp
  have h4 : 0 < m.g.coeff4 := by rw [c4]; have := hp.2.2.2; positivity
  have h0 : 0 < m.g.coeff0 m.Q := by rw [c0]; exact hG
  obtain ⟨hω, e1, e2, e0, eg⟩ := sl_quintic_boundary h0 d2 d3 d4 (ω := m.sliceOmega) rfl
  exact ⟨hω, e1, e2, h4, e0, eg⟩

/-- **The degenerate balanced slice models**: a vanishing third Hurwitz determinant `Δ₃ = 0`
of the quintic (two critical pairs, a multiple critical pair or worse), or a Hopf point
(`Δ₄ = 0`, `Δ₂, Δ₃ > 0`) with a vanishing slice Bautin form `𝔅` at its frequency
`Line.VSMLPF.Model.sliceOmega`. -/
def Model.SliceDegenerate (m : Model) : Prop :=
  Meets m .balanced ∧ (Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q)
    (m.g.coeff1 m.Q) (m.g.coeff0 m.Q) = 0 ∨
    (Criteria.quinticHurwitzDet4 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) = 0 ∧
    0 < Criteria.quinticHurwitzDet2 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) ∧
    0 < Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) ∧
    sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 m.sliceOmega = 0))

/-- **Complete local asymptotic membership on the zero-current slice**: a physical model on the
slice (`δ* = 0`, `V = E`) off the degenerate set (`Line.VSMLPF.Model.SliceDegenerate`) is locally
asymptotically stable iff it is balanced and either meets the strict quintic Routh conditions or
has a Hopf point at some `ω` with `𝔅(D/M, R/L, ω₀, ω) > 0` (supercritical). The excluded cases
are unstable: not balanced, a strict Routh violation (`Line.VSMLPF.mem_den_unstable`), a Hopf
point with `𝔅 < 0` (`Line.VSMLPF.mem_den_unstable_of_sliceBautin_neg`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_slice (m : Model)
    (hp : Meets m .physical) (hs : m.OnSlice) (hd : ¬ m.SliceDegenerate) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      Meets m .balanced ∧ (m.Routh ∨ ∃ ω, m.HopfAt ω ∧
        0 < sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω)) := by
  unfold TMIO.Statement
  have hsem := chain_le_semantics
  unfold powerlib.TMIO.Statement at hsem
  have hunst : m ∈ family.den (.flow .unstable) →
      m ∉ family.den (.flow .locallyAsymptoticallyStable) := by
    intro hu hl
    rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hu hl
    change Unstable m.field 0 at hu
    change LocalAsymptoticStable m.field 0 at hl
    exact hu hl.1
  obtain ⟨-, c4, -, -, -, c0⟩ := sl_coeffs hp hs
  obtain ⟨hd0, hσ, hG⟩ := sl_pos hp
  have h4 : 0 < m.g.coeff4 := by rw [c4]; have := hp.2.2.2; positivity
  have h0 : 0 < m.g.coeff0 m.Q := by rw [c0]; exact hG
  constructor
  · intro hl
    have hb : Meets m .balanced := by
      by_contra hb
      have hne : m.field 0 ≠ 0 := by
        intro h0'
        apply hb
        have h' : m.g.field m.point = 0 := by simpa [Model.field] using h0'
        exact (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne'
          hp.1.absSq_pos.ne').mp h'
      rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hl
      change LocalAsymptoticStable m.field 0 at hl
      exact Dynamics.unstable_of_ne_zero m.contDiff_field hne hl.1
    refine ⟨hb, ?_⟩
    by_cases hv : m.RouthViolation
    · exact absurd hl (hunst (mem_den_unstable m hp hb hv))
    by_cases hr : m.Routh
    · exact Or.inl hr
    right
    unfold Model.RouthViolation Criteria.QuinticRouthViolation at hv
    unfold Model.Routh Criteria.QuinticRouth at hr
    push Not at hv hr
    obtain ⟨-, -, -, v1, -, v2, v3, v4⟩ := hv
    have d3 : 0 < Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q)
        (m.g.coeff1 m.Q) (m.g.coeff0 m.Q) := by
      rcases v3.lt_or_eq with h | h
      · exact h
      · exact absurd ⟨hb, Or.inl h.symm⟩ hd
    have d2 : 0 < Criteria.quinticHurwitzDet2 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) := by
      rcases v2.lt_or_eq with h | h
      · exact h
      · exfalso
        unfold Criteria.quinticHurwitzDet4 at v4
        unfold Criteria.quinticHurwitzDet3 at d3 v4
        rw [← h] at d3 v4
        have ht : m.g.coeff4 * m.g.coeff1 m.Q - m.g.coeff0 m.Q < 0 := by nlinarith
        nlinarith [mul_pos_of_neg_of_neg ht ht]
    have d4 : Criteria.quinticHurwitzDet4 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q)
        (m.g.coeff1 m.Q) (m.g.coeff0 m.Q) = 0 := by
      rcases v4.lt_or_eq with h | h
      · exfalso
        have h5 : 0 < Criteria.quinticHurwitzDet5 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q)
            (m.g.coeff1 m.Q) (m.g.coeff0 m.Q) := by
          unfold Criteria.quinticHurwitzDet5; positivity
        exact absurd (hr h4 d2 d3 h) (not_le.mpr h5)
      · exact h.symm
    have hH : m.HopfAt m.sliceOmega := m.hopfAt_sliceOmega hp hs d2 d3 d4
    refine ⟨m.sliceOmega, hH, ?_⟩
    rcases lt_trichotomy (sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 m.sliceOmega) 0 with
      hB | hB | hB
    · exact absurd hl (hunst (mem_den_unstable_of_sliceBautin_neg m hp hb hs hH hB))
    · exact absurd ⟨hb, Or.inr ⟨d4, d2, d3, hB⟩⟩ hd
    · exact hB
  · rintro ⟨hb, hr | ⟨ω, hH, hB⟩⟩
    · refine (Family.chain_le_semantics_iff.mp hsem _) ((TMIO.mem_realize _ _ _).mpr ?_)
      intro q hq
      simp only [family, translate, Spectral.localTable, Spectral.table, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact hb
      · exact hp
      · exact hr
    · exact mem_den_locallyAsymptoticallyStable_of_sliceBautin_pos m hp hb hs hH hB


/-! ## The angular-speed row of the slice critical pair

The parameter derivative of the Jacobian along the damping has the single entry `−1/M` in the
`ω` row (`theorem/GridTiedConverter/GFM/LineVSMLPFHopfCycle.lean`), so its transversality
coefficient reads only `Re(conj p₁ q₁)`, the `ω` components of the critical pair. -/

/-- **The transversality form of the slice**, `𝔗(d, σ, w, ω)`: the reduced numerator of
`Re(conj p₁ q₁)` at a slice Hopf point (`d Re Ĉ − ω Im Ĉ = 2 ω² w 𝔗`). -/
def sliceTransversality (d σ w ω : ℝ) : ℝ :=
  2 * ω ^ 6 + 3 * ω ^ 4 * d ^ 2 + 4 * ω ^ 4 * d * σ + 5 * ω ^ 4 * σ ^ 2 - 3 * ω ^ 4 * w ^ 2 -
    ω ^ 2 * d ^ 2 * σ ^ 2 - 5 * ω ^ 2 * d ^ 2 * w ^ 2 - 2 * ω ^ 2 * d * σ ^ 3 -
    2 * ω ^ 2 * d * σ * w ^ 2 + ω ^ 2 * σ ^ 4 + 2 * ω ^ 2 * σ ^ 2 * w ^ 2 + ω ^ 2 * w ^ 4 +
    2 * d ^ 3 * σ ^ 3 + 2 * d ^ 3 * σ * w ^ 2 + 2 * d ^ 2 * σ ^ 4 + 4 * d ^ 2 * σ ^ 2 * w ^ 2 +
    2 * d ^ 2 * w ^ 4

/-- The `ω` components of the slice pattern: `Q_c (−c w − w ω i) q₁ = w ω² τ' d − w ω³ τ' i`,
`τ' = (σ² + w² − ω²)² + 4σ²ω²`, modulo the first Hopf relation. -/
@[tmio M, powerlib_domain] private theorem sl_row {d c σ w O : ℂ}
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d)) :
    (-(c * w) - w * O * I) * (σ ^ (2:ℕ) * O * I - 2 * σ * O ^ (2:ℕ) + w ^ (2:ℕ) * O * I -
        O ^ (3:ℕ) * I) * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      w * O ^ 2 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * d +
        (-(w * O ^ 3 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2))) * I := by
  linear_combination (-w * (σ ^ (2:ℕ) * O * I - 2 * σ * O ^ (2:ℕ) + w ^ (2:ℕ) * O * I -
      O ^ (3:ℕ) * I)) * h1 +
    (-(O ^ 2 * w * (σ ^ 2 + w ^ 2 - O ^ 2) * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2))) *
      I_sq

/-- **The `ω` row of the slice critical pair**: at a Hopf point `ω` of a physical slice model,
the `ω` components of (`Model.sliceQ`, `Model.sliceP`) satisfy
`Re(conj p₁ q₁) = 2 w² ω⁴ ((σ² + w² − ω²)² + 4σ²ω²) 𝔗 / (Re² Ĉ + Im² Ĉ)`, `d = D/M`, `σ = R/L`,
`w = ω₀`, `𝔗 = Line.VSMLPF.sliceTransversality d σ w ω`, `Ĉ = slicePairRe + i slicePairIm`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.re_sliceP_one_mul_sliceQ_one {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    (starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 1).re =
      2 * m.g.ω0 ^ 2 * ω ^ 4 *
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) *
          sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω /
        (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
          slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) := by
  obtain ⟨h1, h2, -, -, -⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  have hω := hH.1
  have hw := hp.1.ω0
  set d := m.g.D / m.g.M with hd_def
  set σ := m.g.R / m.g.L with hσ_def
  set w := m.g.ω0 with hw_def
  set c := m.g.ωc with hc_def
  set g := m.g.E ^ 2 / (m.g.M * m.g.L) with hg_def
  have hQ := sl_Qc_pos hG h1 h2
  have hCr0 := sl_pairRe_pos hω hw hd hσ hQ
  have hPa := sl_pairing_ne hω hw hd hσ hG h1 h2
  have h1c : (c : ℂ) * ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) =
      (ω : ℂ) ^ 2 * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d) := by exact_mod_cast h1
  have eC := sl_C (j := I) h1c
  rw [slicePairRe_cast, slicePairIm_cast] at eC
  set Cr := slicePairRe d σ w ω with hCr_def
  set Ci := slicePairIm d σ w ω with hCi_def
  set Pa := slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I with hPadef
  set τ' := (σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2 with hτ'
  have hp1 : m.sliceP ω 1 = (starRingEnd ℂ Pa)⁻¹ * (-(c : ℂ) * w + w * ω * I) := by
    simp [Model.sliceP, sliceScale, sliceVecP, hPadef, hd_def, hσ_def, hw_def, hc_def]
  have hq1 : m.sliceQ ω 1 = (σ : ℂ) ^ (2:ℕ) * ω * I - 2 * σ * (ω : ℂ) ^ (2:ℕ) +
      (w : ℂ) ^ (2:ℕ) * ω * I - (ω : ℂ) ^ (3:ℕ) * I := by
    simp [Model.sliceQ, sliceScale, sliceVecQ, hσ_def, hw_def]
  set X := starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 1 with hX
  have hXc : X * ((Cr : ℂ) + (Ci : ℂ) * I) =
      ((w * ω ^ 2 * τ' * d : ℝ) : ℂ) + ((-(w * ω ^ 3 * τ') : ℝ) : ℂ) * I := by
    rw [← eC, hX, hp1, hq1]
    simp only [map_mul, map_inv₀, Complex.conj_conj, map_add, map_neg, Complex.conj_ofReal,
      Complex.conj_I]
    have e := sl_row (d := (d : ℂ)) (c := (c : ℂ)) (σ := (σ : ℂ)) (w := (w : ℂ)) (O := (ω : ℂ))
      h1c
    have hinv : Pa⁻¹ * Pa = 1 := inv_mul_cancel₀ hPa
    rw [hτ']
    push_cast
    linear_combination ((-(c : ℂ) * w + w * ω * -I) * ((σ : ℂ) ^ (2:ℕ) * ω * I -
      2 * σ * (ω : ℂ) ^ (2:ℕ) + (w : ℂ) ^ (2:ℕ) * ω * I - (ω : ℂ) ^ (3:ℕ) * I) *
      ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2)) * hinv + e
  have hre := congrArg Complex.re hXc
  have him := congrArg Complex.im hXc
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
  have hC2 : Cr ^ 2 + Ci ^ 2 ≠ 0 := by positivity
  have hT : d * Cr - ω * Ci = 2 * ω ^ 2 * w * sliceTransversality d σ w ω := by
    simp only [hCr_def, hCi_def, slicePairRe, slicePairIm, sliceTransversality]
    ring
  rw [eq_div_iff hC2]
  linear_combination Cr * hre + Ci * him + w * ω ^ 2 * τ' * hT

/-- **The sign of the `ω` row**: at a Hopf point `ω` of a physical slice model,
`sign Re(conj p₁ q₁) = sign 𝔗(D/M, R/L, ω₀, ω)` (`Line.VSMLPF.sliceTransversality`; the prefactor
of `Line.VSMLPF.Model.re_sliceP_one_mul_sliceQ_one` is positive). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_re_sliceP_one_mul_sliceQ_one {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    SignType.sign (starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 1).re =
      SignType.sign (sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) := by
  obtain ⟨h1, h2, -, -, -⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  have hω := hH.1
  have hw := hp.1.ω0
  have hQ := sl_Qc_pos hG h1 h2
  have hCr := sl_pairRe_pos hω hw hd hσ hQ
  have hτ : 0 < (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2 := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonneg hσ (sq_nonneg ω)]
  have hC : 0 < slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
      slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 := by positivity
  have hpre : 0 < 2 * m.g.ω0 ^ 2 * ω ^ 4 *
      (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) /
      (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
        slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) := by positivity
  rw [m.re_sliceP_one_mul_sliceQ_one hp hs hH, mul_div_right_comm, sign_mul, sign_pos hpre,
    one_mul]

/-- **The inertia form of the slice**, `𝔍(d, σ, w, ω)`: the reduced numerator of
`Re(conj p₁ q₀)` at a slice Hopf point (`ω Re Ĉ + d Im Ĉ = ω w 𝔍`); the transversality
coefficient along the inverse inertia reads it. -/
def sliceInertia (d σ w ω : ℝ) : ℝ :=
  -2 * ω ^ 6 * d + 4 * ω ^ 6 * σ - 4 * ω ^ 4 * d ^ 3 - 4 * ω ^ 4 * d ^ 2 * σ -
    14 * ω ^ 4 * d * σ ^ 2 + 2 * ω ^ 4 * d * w ^ 2 - 2 * ω ^ 2 * d ^ 3 * σ ^ 2 +
    6 * ω ^ 2 * d ^ 3 * w ^ 2 + 8 * ω ^ 2 * d ^ 2 * σ ^ 3 + 8 * ω ^ 2 * d ^ 2 * σ * w ^ 2 -
    2 * d ^ 3 * σ ^ 4 - 4 * d ^ 3 * σ ^ 2 * w ^ 2 - 2 * d ^ 3 * w ^ 4

/-- **The two forms never vanish together**: `ω² w² (4ω² 𝔗² + 𝔍²) = (d² + ω²)(Re² Ĉ + Im² Ĉ)`
(`d Re Ĉ − ω Im Ĉ = 2ω²w 𝔗`, `ω Re Ĉ + d Im Ĉ = ωw 𝔍`), for all values. -/
@[tmio M, powerlib_domain] theorem sliceTransversality_sq_add_sliceInertia_sq (d σ w ω : ℝ) :
    ω ^ 2 * w ^ 2 * (4 * ω ^ 2 * sliceTransversality d σ w ω ^ 2 + sliceInertia d σ w ω ^ 2) =
      (d ^ 2 + ω ^ 2) * (slicePairRe d σ w ω ^ 2 + slicePairIm d σ w ω ^ 2) := by
  simp only [sliceTransversality, sliceInertia, slicePairRe, slicePairIm]
  ring

/-- The `δ` component of the slice pattern: `Q_c (−c w − w ω i) q₀ = −w ω² τ' − w ω τ' d i`,
`τ' = (σ² + w² − ω²)² + 4σ²ω²`, modulo the first Hopf relation. -/
@[tmio M, powerlib_domain] private theorem sl_row0 {d c σ w O : ℂ}
    (h1 : c * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      O ^ 2 * (σ ^ 2 + w ^ 2 - O ^ 2 + 2 * σ * d)) :
    (-(c * w) - w * O * I) * (σ ^ (2:ℕ) + 2 * σ * O * I + w ^ (2:ℕ) - O ^ (2:ℕ)) *
        (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2) =
      -(w * O ^ 2 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)) +
        (-(w * O * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * d)) * I := by
  linear_combination (-w * (σ ^ (2:ℕ) + 2 * σ * O * I + w ^ (2:ℕ) - O ^ (2:ℕ))) * h1 +
    (-(2 * O ^ 2 * σ * w * (d * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * O ^ 2))) * I_sq

/-- **The `δ` row of the slice critical pair**: at a Hopf point `ω` of a physical slice model,
`Re(conj p₁ q₀) = −w² ω² ((σ² + w² − ω²)² + 4σ²ω²) 𝔍 / (Re² Ĉ + Im² Ĉ)`
(`𝔍 = Line.VSMLPF.sliceInertia (D/M) (R/L) ω₀ ω`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.re_sliceP_one_mul_sliceQ_zero {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    (starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 0).re =
      -(m.g.ω0 ^ 2 * ω ^ 2 *
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) *
          sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω /
        (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
          slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2)) := by
  obtain ⟨h1, h2, -, -, -⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  have hω := hH.1
  have hw := hp.1.ω0
  set d := m.g.D / m.g.M with hd_def
  set σ := m.g.R / m.g.L with hσ_def
  set w := m.g.ω0 with hw_def
  set c := m.g.ωc with hc_def
  set g := m.g.E ^ 2 / (m.g.M * m.g.L) with hg_def
  have hQ := sl_Qc_pos hG h1 h2
  have hCr0 := sl_pairRe_pos hω hw hd hσ hQ
  have hPa := sl_pairing_ne hω hw hd hσ hG h1 h2
  have h1c : (c : ℂ) * ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2) =
      (ω : ℂ) ^ 2 * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 + 2 * σ * d) := by exact_mod_cast h1
  have eC := sl_C (j := I) h1c
  rw [slicePairRe_cast, slicePairIm_cast] at eC
  set Cr := slicePairRe d σ w ω with hCr_def
  set Ci := slicePairIm d σ w ω with hCi_def
  set Pa := slicePairing (d : ℂ) (c : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I with hPadef
  set τ' := (σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2 with hτ'
  have hp1 : m.sliceP ω 1 = (starRingEnd ℂ Pa)⁻¹ * (-(c : ℂ) * w + w * ω * I) := by
    simp [Model.sliceP, sliceScale, sliceVecP, hPadef, hd_def, hσ_def, hw_def, hc_def]
  have hq0 : m.sliceQ ω 0 = (σ : ℂ) ^ (2:ℕ) + 2 * σ * ω * I + (w : ℂ) ^ (2:ℕ) -
      (ω : ℂ) ^ (2:ℕ) := by
    simp [Model.sliceQ, sliceScale, sliceVecQ, hσ_def, hw_def]
  set X := starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 0 with hX
  have hXc : X * ((Cr : ℂ) + (Ci : ℂ) * I) =
      (((-(w * ω ^ 2 * τ')) : ℝ) : ℂ) + (((-(w * ω * τ' * d)) : ℝ) : ℂ) * I := by
    rw [← eC, hX, hp1, hq0]
    simp only [map_mul, map_inv₀, Complex.conj_conj, map_add, map_neg, Complex.conj_ofReal,
      Complex.conj_I]
    have e := sl_row0 (d := (d : ℂ)) (c := (c : ℂ)) (σ := (σ : ℂ)) (w := (w : ℂ))
      (O := (ω : ℂ)) h1c
    have hinv : Pa⁻¹ * Pa = 1 := inv_mul_cancel₀ hPa
    rw [hτ']
    push_cast
    linear_combination ((-(c : ℂ) * w + w * ω * -I) * ((σ : ℂ) ^ (2:ℕ) + 2 * σ * ω * I +
      (w : ℂ) ^ (2:ℕ) - (ω : ℂ) ^ (2:ℕ)) *
      ((d : ℂ) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) - 2 * σ * ω ^ 2)) * hinv + e
  have hre := congrArg Complex.re hXc
  have him := congrArg Complex.im hXc
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
  have hC2 : Cr ^ 2 + Ci ^ 2 ≠ 0 := by positivity
  have hJ : ω * Cr + d * Ci = ω * w * sliceInertia d σ w ω := by
    simp only [hCr_def, hCi_def, slicePairRe, slicePairIm, sliceInertia]
    ring
  rw [eq_neg_iff_add_eq_zero, add_div' _ _ _ hC2, div_eq_zero_iff]
  left
  linear_combination Cr * hre + Ci * him - w * ω * τ' * hJ

/-- **The sign of the `δ` row**: at a Hopf point `ω` of a physical slice model,
`sign Re(conj p₁ q₀) = −sign 𝔍(D/M, R/L, ω₀, ω)` (`Line.VSMLPF.sliceInertia`). Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_re_sliceP_one_mul_sliceQ_zero {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    SignType.sign (starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 0).re =
      -SignType.sign (sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) := by
  obtain ⟨h1, h2, -, -, -⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  have hω := hH.1
  have hw := hp.1.ω0
  have hQ := sl_Qc_pos hG h1 h2
  have hCr := sl_pairRe_pos hω hw hd hσ hQ
  have hτ : 0 < (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2 := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonneg hσ (sq_nonneg ω)]
  have hC : 0 < slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
      slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 := by positivity
  have hpre : 0 < m.g.ω0 ^ 2 * ω ^ 2 *
      (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) /
      (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
        slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) := by positivity
  rw [m.re_sliceP_one_mul_sliceQ_zero hp hs hH, mul_div_right_comm, Left.sign_neg, sign_mul,
    sign_pos hpre, one_mul]

/-- **The forms are never both zero at a slice Hopf point**: `𝔗 = 0` forces `𝔍 ≠ 0`
(`Line.VSMLPF.sliceTransversality_sq_add_sliceInertia_sq`, `Re Ĉ > 0`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.sliceInertia_ne_zero_of_sliceTransversality_eq_zero
    {m : Model} (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω)
    (hT : sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω = 0) :
    sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0 := by
  obtain ⟨h1, h2, -, -, -⟩ := sl_hopf hp hs hH
  obtain ⟨hd, hσ, hG⟩ := sl_pos hp
  have hω := hH.1
  have hw := hp.1.ω0
  have hCr := sl_pairRe_pos hω hw hd hσ (sl_Qc_pos hG h1 h2)
  intro hJ
  have e := sliceTransversality_sq_add_sliceInertia_sq (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω
  rw [hT, hJ] at e
  have hpos : 0 < ((m.g.D / m.g.M) ^ 2 + ω ^ 2) *
      (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
        slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) := by positivity
  have e' : ((m.g.D / m.g.M) ^ 2 + ω ^ 2) *
      (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
        slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) = 0 := by
    rw [← e]; ring
  exact hpos.ne' e'

end VSMLPF
end powerlib.GFM.Line
