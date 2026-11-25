import theorem.GridTiedConverter.GFM.HopfBautinLine
import theorem.Dynamics.PolyCertificate

/-! # The Bautin path of the four-state VSM: exact centre-manifold and Lyapunov data

Model boundary.
* The path `Line.VSM.bautinPath s` (`s > 0`) of `theorem/GridTiedConverter/GFM/HopfBautinLine.lean`
  (the four-state VSM on a dynamic R–L line, `E = V = 1`, `R = s`, `L = ω₀ = 1`,
  `M = 1/(4 + s²)`, `D = 2/(s(4 + s²))`, `P_ref = 0`, `δ* = 0`) in the critical chart of
  `(bautinPathQ s, bautinPathP s)`, chart coordinates `y = (y₀, y₁)`.
* Content: exact rational functions of `s`, valid for every `s > 0`, written as integer numerators
  over products of powers of the bases `2, 3, 5, s, D₁, D₂, E, F, s² + 4`
  (`Dynamics.PolyCertificate`): the coefficients of the order-four approximate centre manifold
  (`h₁ = x₂`, `h₂ = x₃` and `x₀ = −h₁ − (2/s) h₂` components, degrees two to four), the
  critical-chart coordinates `PV0ₖ = Re pₖ + Im pₖ`, `PV1ₖ = Re pₖ − Im pₖ`, the 36 coefficients
  of the quintic jet of the chart field, the weight-five truncations `T` of the three
  nonlinearities (through the coefficients `S` of the 34 products of manifold pieces they are
  made of) and their values `TV`, the homological coefficients `Hom`, and the Lyapunov
  polynomial of the jet. No analysis here: the analytic
  statements (Taylor remainders, invariance defect, jet of the chart field, stability) are in
  `theorem/GridTiedConverter/GFM/HopfBautinPoint.lean`.

Source: the derivation was done with SymPy over `ℚ(s)` (the homological equations of orders two
to four as linear systems over `ℚ(s)`, exact rational elimination; scripts in the study notes,
untrusted, discovery evidence only); every identity below is checked by the kernel
(`Dynamics.PolyCertificate.PExpr.val_eq_zero`, `decide +kernel`). Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed.), §8.3 (Bautin points); Carr, *Applications of Centre Manifold
Theory* (1981), §2.5 (the homological equations of an approximate centre manifold).

Results.
* `bases`, `zeval_bases_pos`, `bases_ne_zero`, `bval_s`; the atoms `CM1_ij`, `CM2_ij`, `CA_ij`
  (manifold), `PV0_k`, `PV1_k`, `DETV` (chart), `TVk_ij` (truncations), `JA_ij`, `JB_ij` (jet),
  `LY_*`, `L1V`, `L2V` (Lyapunov polynomial); the coefficient expressions `S*_ij` (products of
  pieces), `T1_ij`, `T2_ij`, `T3_ij` (truncations), `jet`, `Hom2_ij`, `Hom3_ij`, `highD2`,
  `highD3`.
* The manifold: `CA_ij_eq` (`x₀ = −h₁ − (2/s) h₂` coefficientwise); `Tk_ij_val` (the values of
  the truncation coefficients).
* Chart: `PV0_k_eq`, `PV1_k_eq` (the atoms are the real and imaginary parts of `p`),
  `DETV_eq`, `piw1_0`, `piw1_1`, `piw2_0`, `piw2_1` (`w₁`, `w₂` span `ker π`).
* The jet: `JA_ij_eq`, `JB_ij_eq` (`J = Σₖ PVₖ Tₖ`, the chart coordinates of the truncated
  nonlinearities).
* **The homological equations**: `Hom2_ij_eq`, `Hom3_ij_eq` (the polynomial part of the invariance
  defect of the manifold vanishes in degrees two to four, for every `s > 0`).
* The Lyapunov polynomial: `jet_c30` … `jet_k6`, `jet_l1`, `jet_l2` (every step of
  `Jet.l1`, `Jet5.l2` at `ω = 1`); `L1V_eq` (`l₁(J) = s³(s² + 4)² N(s)/(D₁ D₂)`, the first
  Lyapunov coefficient of the path), `nL2V_eq` (the numerator of `l₂(J)` is `Q(s) N(s) + ρ(s)`,
  exact division by `N = bautinNum`), `zeval_nNR` (`ρ(s) = −512 s P(s²)`), `nNR_pos`
  (`ρ > 0` on `(2, 21/10)`), **`L2V_pos`** (`l₂(J) > 0` wherever `N(s) = 0` in `(2, 21/10)`).
-/

noncomputable section
namespace powerlib.GFM.Line.VSM
namespace Bautin
open powerlib.Dynamics.PolyCertificate Dynamics.Degenerate.PlanarFocus

/-! ## The bases of the denominators -/

/-- The bases `2, 3, 5, s, D₁, D₂, E, F, s² + 4` (`D₁ = s⁶ + 10s⁴ + 17s² + 4`,
`D₂ = s⁶ + 16s⁴ + 32s² + 16`, `E = s⁴ + 22s² + 9`, `F = s⁶ + 40s⁴ + 272s² + 64`). -/
def bases : List (List ℤ) :=
  [[2], [3], [5], [0, 1], [4, 0, 17, 0, 10, 0, 1], [16, 0, 32, 0, 16, 0, 1], [9, 0, 22, 0, 1],
   [64, 0, 272, 0, 40, 0, 1], [4, 0, 1]]

/-- Every base is positive for `s > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeval_bases_pos {s : ℝ} (hs : 0 < s) :
    ∀ b ∈ bases, 0 < zeval b s := by
  intro b hb
  simp only [bases, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [zeval] <;> push_cast <;> ring_nf <;> positivity

/-- Every base is nonzero for `s > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bases_ne_zero {s : ℝ} (hs : 0 < s) :
    ∀ b ∈ bases, zeval b s ≠ 0 :=
  fun b hb => (zeval_bases_pos hs b hb).ne'

/-- The denominator `sᵏ`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem bval_s (s : ℝ) (k : ℕ) :
    bval bases [0, 0, 0, k] s = s ^ k := by
  simp [zeval, bval, bases]

/-! ## The approximate centre manifold: coefficients of `h₁ = x₂`, `h₂ = x₃` -/

/-- Numerator coefficients (constant term first) of `CM1_20`. -/
def nCM1_20 : List ℤ :=
  [0, -1024, 1024, -5120, 4864, -10304, 8384, -10848, 6640, -6480, 2672, -2196, 558, -394, 56, -33,
   2, -1]
/-- Denominator exponents of `CM1_20` over `bases`. -/
def eCM1_20 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^2 y₁^0` in `h₁` (the `x₂` component of the manifold). -/
def CM1_20 (s : ℝ) : ℝ := zeval nCM1_20 s / bval bases eCM1_20 s

/-- Numerator coefficients (constant term first) of `CM1_11`. -/
def nCM1_11 : List ℤ :=
  [0, 0, 0, -512, 0, -2944, 0, -5152, 0, -3944, 0, -1516, 0, -302, 0, -29, 0, -1]
/-- Denominator exponents of `CM1_11` over `bases`. -/
def eCM1_11 : List ℕ := [0, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^1 y₁^1` in `h₁` (the `x₂` component of the manifold). -/
def CM1_11 (s : ℝ) : ℝ := zeval nCM1_11 s / bval bases eCM1_11 s

/-- Numerator coefficients (constant term first) of `CM1_02`. -/
def nCM1_02 : List ℤ :=
  [0, -1024, -1024, -5120, -4864, -10304, -8384, -10848, -6640, -6480, -2672, -2196, -558, -394,
   -56, -33, -2, -1]
/-- Denominator exponents of `CM1_02` over `bases`. -/
def eCM1_02 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^0 y₁^2` in `h₁` (the `x₂` component of the manifold). -/
def CM1_02 (s : ℝ) : ℝ := zeval nCM1_02 s / bval bases eCM1_02 s

/-- Numerator coefficients (constant term first) of `CM1_30`. -/
def nCM1_30 : List ℤ :=
  [0, 0, -221184, 110592, -2445312, 1903616, -9639936, 8304384, -17835264, 14544448, -16009248,
   9886944, -4118784, -1881424, 5273520, -7468076, 6000450, -5288413, 2876352, -1942852, 762372,
   -416776, 115122, -52576, 9516, -3729, 390, -136, 6, -2]
/-- Denominator exponents of `CM1_30` over `bases`. -/
def eCM1_30 : List ℕ := [0, 1, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^3 y₁^0` in `h₁` (the `x₂` component of the manifold). -/
def CM1_30 (s : ℝ) : ℝ := zeval nCM1_30 s / bval bases eCM1_30 s

/-- Numerator coefficients (constant term first) of `CM1_21`. -/
def nCM1_21 : List ℤ :=
  [0, 0, 73728, -110592, 782336, -650240, 2879488, -1655552, 4853504, -2883904, 4000096, -4097824,
   1272256, -4663936, -275960, -3888212, -254578, -2232225, 12676, -853224, 47428, -209764, 14942,
   -31668, 1972, -2737, 110, -120, 2, -2]
/-- Denominator exponents of `CM1_21` over `bases`. -/
def eCM1_21 : List ℕ := [0, 0, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^2 y₁^1` in `h₁` (the `x₂` component of the manifold). -/
def CM1_21 (s : ℝ) : ℝ := zeval nCM1_21 s / bval bases eCM1_21 s

/-- Numerator coefficients (constant term first) of `CM1_12`. -/
def nCM1_12 : List ℤ :=
  [0, 0, -73728, -110592, -782336, -650240, -2879488, -1655552, -4853504, -2883904, -4000096,
   -4097824, -1272256, -4663936, 275960, -3888212, 254578, -2232225, -12676, -853224, -47428,
   -209764, -14942, -31668, -1972, -2737, -110, -120, -2, -2]
/-- Denominator exponents of `CM1_12` over `bases`. -/
def eCM1_12 : List ℕ := [0, 0, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^1 y₁^2` in `h₁` (the `x₂` component of the manifold). -/
def CM1_12 (s : ℝ) : ℝ := zeval nCM1_12 s / bval bases eCM1_12 s

/-- Numerator coefficients (constant term first) of `CM1_03`. -/
def nCM1_03 : List ℤ :=
  [0, 0, 221184, 110592, 2445312, 1903616, 9639936, 8304384, 17835264, 14544448, 16009248, 9886944,
   4118784, -1881424, -5273520, -7468076, -6000450, -5288413, -2876352, -1942852, -762372, -416776,
   -115122, -52576, -9516, -3729, -390, -136, -6, -2]
/-- Denominator exponents of `CM1_03` over `bases`. -/
def eCM1_03 : List ℕ := [0, 1, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^0 y₁^3` in `h₁` (the `x₂` component of the manifold). -/
def CM1_03 (s : ℝ) : ℝ := zeval nCM1_03 s / bval bases eCM1_03 s

/-- Numerator coefficients (constant term first) of `CM1_40`. -/
def nCM1_40 : List ℤ :=
  [0, 0, 0, -1043677052928, 695784701952, -22471268892672, 16464757129216, -207622745620480,
   162956427919360, -1107387054292992, 919240844509184, -3879863370907648, 3385379726032896,
   -9650471589380096, 8815402280812544, -18024760091869184, 17136322407825408, -26466269448634368,
   25886181824659456, -31755019863261184, 31307759424241664, -32043536687726592, 30922150234685440,
   -27573941818261504, 25173100299001856, -20179535263662080, 16884988544172032, -12377814929100800,
   9265765638765568, -6243372555739136, 4116236140304384, -2542543928596480, 1462957172217856,
   -822808500768192, 410850660839552, -208702332102016, 89946044136224, -40956370928608,
   15108200852832, -6132125892836, 1907506628444, -688138818932, 175749943012, -56328196705,
   11236579208, -3194832046, 444681364, -109797160, 6490424, -974947, -309716, 104007, -19704, 5460,
   -452, 118, -4, 1]
/-- Denominator exponents of `CM1_40` over `bases`. -/
def eCM1_40 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^4 y₁^0` in `h₁` (the `x₂` component of the manifold). -/
def CM1_40 (s : ℝ) : ℝ := zeval nCM1_40 s / bval bases eCM1_40 s

/-- Numerator coefficients (constant term first) of `CM1_31`. -/
def nCM1_31 : List ℤ :=
  [0, 0, 0, 231928233984, -231928233984, 4773856149504, -4298188521472, 43084427558912,
   -34936874598400, 225832064778240, -164247602462720, 765247040258048, -492813271695360,
   1752566824173568, -967574149922816, 2708531184664576, -1162559468077056, 2586905495470080,
   -475916847284224, 765332705509376, 1176609926152192, -1980182355935232, 2987763808944128,
   -4010944418971648, 3882665426649088, -4355516932505600, 3494434972450816, -3356803598710784,
   2349930842693120, -1979715573635072, 1215223614532864, -918570993938944, 488691652334336,
   -337841100744576, 153142631001472, -98155244735296, 37246773472624, -22308313740112,
   6966104200656, -3910903211528, 987030600766, -519302276564, 103594698722, -50947533541,
   7774098172, -3554444590, 391523810, -163954432, 11372668, -4069651, 77078, 7347, -6276, 3828,
   -202, 106, -2, 1]
/-- Denominator exponents of `CM1_31` over `bases`. -/
def eCM1_31 : List ℕ := [1, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^3 y₁^1` in `h₁` (the `x₂` component of the manifold). -/
def CM1_31 (s : ℝ) : ℝ := zeval nCM1_31 s / bval bases eCM1_31 s

/-- Numerator coefficients (constant term first) of `CM1_22`. -/
def nCM1_22 : List ℤ :=
  [0, 0, 0, -21743271936, 0, -415538085888, 0, -3272983183360, 0, -14180467867648, 0,
   -38209834713088, 0, -68878520549376, 0, -88244895678464, 0, -87166243225600, 0, -75628818280448,
   0, -64967999023104, 0, -53835631934464, 0, -38156225187072, 0, -21287194557952, 0,
   -9050817072320, 0, -2904677294224, 0, -700573847060, 0, -126060232644, 0, -16663710433, 0,
   -1571143550, 0, -99883320, 0, -3770899, 0, -49177, 0, 1940, 0, 86, 0, 1]
/-- Denominator exponents of `CM1_22` over `bases`. -/
def eCM1_22 : List ℕ := [2, 0, 0, 0, 3, 2, 1, 1]
/-- Coefficient of `y₀^2 y₁^2` in `h₁` (the `x₂` component of the manifold). -/
def CM1_22 (s : ℝ) : ℝ := zeval nCM1_22 s / bval bases eCM1_22 s

/-- Numerator coefficients (constant term first) of `CM1_13`. -/
def nCM1_13 : List ℤ :=
  [0, 0, 0, 231928233984, 231928233984, 4773856149504, 4298188521472, 43084427558912,
   34936874598400, 225832064778240, 164247602462720, 765247040258048, 492813271695360,
   1752566824173568, 967574149922816, 2708531184664576, 1162559468077056, 2586905495470080,
   475916847284224, 765332705509376, -1176609926152192, -1980182355935232, -2987763808944128,
   -4010944418971648, -3882665426649088, -4355516932505600, -3494434972450816, -3356803598710784,
   -2349930842693120, -1979715573635072, -1215223614532864, -918570993938944, -488691652334336,
   -337841100744576, -153142631001472, -98155244735296, -37246773472624, -22308313740112,
   -6966104200656, -3910903211528, -987030600766, -519302276564, -103594698722, -50947533541,
   -7774098172, -3554444590, -391523810, -163954432, -11372668, -4069651, -77078, 7347, 6276, 3828,
   202, 106, 2, 1]
/-- Denominator exponents of `CM1_13` over `bases`. -/
def eCM1_13 : List ℕ := [1, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^1 y₁^3` in `h₁` (the `x₂` component of the manifold). -/
def CM1_13 (s : ℝ) : ℝ := zeval nCM1_13 s / bval bases eCM1_13 s

/-- Numerator coefficients (constant term first) of `CM1_04`. -/
def nCM1_04 : List ℤ :=
  [0, 0, 0, -1043677052928, -695784701952, -22471268892672, -16464757129216, -207622745620480,
   -162956427919360, -1107387054292992, -919240844509184, -3879863370907648, -3385379726032896,
   -9650471589380096, -8815402280812544, -18024760091869184, -17136322407825408, -26466269448634368,
   -25886181824659456, -31755019863261184, -31307759424241664, -32043536687726592,
   -30922150234685440, -27573941818261504, -25173100299001856, -20179535263662080,
   -16884988544172032, -12377814929100800, -9265765638765568, -6243372555739136, -4116236140304384,
   -2542543928596480, -1462957172217856, -822808500768192, -410850660839552, -208702332102016,
   -89946044136224, -40956370928608, -15108200852832, -6132125892836, -1907506628444, -688138818932,
   -175749943012, -56328196705, -11236579208, -3194832046, -444681364, -109797160, -6490424,
   -974947, 309716, 104007, 19704, 5460, 452, 118, 4, 1]
/-- Denominator exponents of `CM1_04` over `bases`. -/
def eCM1_04 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^0 y₁^4` in `h₁` (the `x₂` component of the manifold). -/
def CM1_04 (s : ℝ) : ℝ := zeval nCM1_04 s / bval bases eCM1_04 s

/-- Numerator coefficients (constant term first) of `CM2_20`. -/
def nCM2_20 : List ℤ :=
  [0, 0, 512, -512, 2560, -2304, 4768, -3296, 4208, -2032, 1840, -580, 378, -73, 33, -3, 1]
/-- Denominator exponents of `CM2_20` over `bases`. -/
def eCM2_20 : List ℕ := [0, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^2 y₁^0` in `h₂` (the `x₃` component of the manifold). -/
def CM2_20 (s : ℝ) : ℝ := zeval nCM2_20 s / bval bases eCM2_20 s

/-- Numerator coefficients (constant term first) of `CM2_11`. -/
def nCM2_11 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 128, 0, 832, 0, 872, 0, 320, 0, 46, 0, 2]
/-- Denominator exponents of `CM2_11` over `bases`. -/
def eCM2_11 : List ℕ := [0, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^1 y₁^1` in `h₂` (the `x₃` component of the manifold). -/
def CM2_11 (s : ℝ) : ℝ := zeval nCM2_11 s / bval bases eCM2_11 s

/-- Numerator coefficients (constant term first) of `CM2_02`. -/
def nCM2_02 : List ℤ :=
  [0, 0, 512, 512, 2560, 2304, 4768, 3296, 4208, 2032, 1840, 580, 378, 73, 33, 3, 1]
/-- Denominator exponents of `CM2_02` over `bases`. -/
def eCM2_02 : List ℕ := [0, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^0 y₁^2` in `h₂` (the `x₃` component of the manifold). -/
def CM2_02 (s : ℝ) : ℝ := zeval nCM2_02 s / bval bases eCM2_02 s

/-- Numerator coefficients (constant term first) of `CM2_30`. -/
def nCM2_30 : List ℤ :=
  [0, 0, 0, 442368, -110592, 4780032, -2513920, 18342912, -11667200, 32674560, -22524224, 28554624,
   -23235936, 10038720, -14586752, -1263240, -6147180, -1726122, -1971382, -210273, -551999, 103983,
   -126277, 34386, -18918, 3864, -1556, 183, -63, 3, -1]
/-- Denominator exponents of `CM2_30` over `bases`. -/
def eCM2_30 : List ℕ := [1, 1, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^3 y₁^0` in `h₂` (the `x₃` component of the manifold). -/
def CM2_30 (s : ℝ) : ℝ := zeval nCM2_30 s / bval bases eCM2_30 s

/-- Numerator coefficients (constant term first) of `CM2_21`. -/
def nCM2_21 : List ℤ :=
  [0, 0, 0, -147456, 258048, -1675264, 1620992, -6769664, 3855104, -12708096, 4556352, -11509632,
   3465952, -4514624, 2122192, -7768, 1040276, 590794, 290330, 211605, -12943, 42109, -33965, 7054,
   -9214, 888, -1068, 53, -55, 1, -1]
/-- Denominator exponents of `CM2_21` over `bases`. -/
def eCM2_21 : List ℕ := [1, 0, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^2 y₁^1` in `h₂` (the `x₃` component of the manifold). -/
def CM2_21 (s : ℝ) : ℝ := zeval nCM2_21 s / bval bases eCM2_21 s

/-- Numerator coefficients (constant term first) of `CM2_12`. -/
def nCM2_12 : List ℤ :=
  [0, 0, 0, 147456, 258048, 1675264, 1620992, 6769664, 3855104, 12708096, 4556352, 11509632,
   3465952, 4514624, 2122192, 7768, 1040276, -590794, 290330, -211605, -12943, -42109, -33965,
   -7054, -9214, -888, -1068, -53, -55, -1, -1]
/-- Denominator exponents of `CM2_12` over `bases`. -/
def eCM2_12 : List ℕ := [1, 0, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^1 y₁^2` in `h₂` (the `x₃` component of the manifold). -/
def CM2_12 (s : ℝ) : ℝ := zeval nCM2_12 s / bval bases eCM2_12 s

/-- Numerator coefficients (constant term first) of `CM2_03`. -/
def nCM2_03 : List ℤ :=
  [0, 0, 0, -442368, -110592, -4780032, -2513920, -18342912, -11667200, -32674560, -22524224,
   -28554624, -23235936, -10038720, -14586752, 1263240, -6147180, 1726122, -1971382, 210273,
   -551999, -103983, -126277, -34386, -18918, -3864, -1556, -183, -63, -3, -1]
/-- Denominator exponents of `CM2_03` over `bases`. -/
def eCM2_03 : List ℕ := [1, 1, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^0 y₁^3` in `h₂` (the `x₃` component of the manifold). -/
def CM2_03 (s : ℝ) : ℝ := zeval nCM2_03 s / bval bases eCM2_03 s

/-- Numerator coefficients (constant term first) of `CM2_40`. -/
def nCM2_40 : List ℤ :=
  [0, 0, 0, 0, 260919263232, -115964116992, 5692710715392, -2908229730304, 53574482526208,
   -29982764040192, 292663114858496, -175448373854208, 1056031723487232, -670994586927104,
   2717947322695680, -1814525370171392, 5261551912091648, -3637582070022144, 7964079001108480,
   -5563156164116480, 9678689785675776, -6604344662163456, 9573771268874240, -6151812709138432,
   7717349628588032, -4526737890932736, 5028238360648704, -2641141566914560, 2612644455542272,
   -1222139859768064, 1065635018986752, -446505440655872, 335260491438272, -127428034339456,
   79617300786336, -27880946397600, 13807279933712, -4536682884408, 1632872062176, -520089914120,
   104689445994, -36897397775, -2516107324, -768676681, -1395465943, 141511444, -165436279,
   17582676, -11574526, 1031561, -528738, 35591, -15555, 698, -267, 6, -2]
/-- Denominator exponents of `CM2_40` over `bases`. -/
def eCM2_40 : List ℕ := [1, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^4 y₁^0` in `h₂` (the `x₃` component of the manifold). -/
def CM2_40 (s : ℝ) : ℝ := zeval nCM2_40 s / bval bases eCM2_40 s

/-- Numerator coefficients (constant term first) of `CM2_31`. -/
def nCM2_31 : List ℤ :=
  [0, 0, 0, 0, -115964116992, 115964116992, -2367600721920, 2073395462144, -21228144295936,
   16196321673216, -111119930753024, 73284792090624, -381186887122944, 214036230701056,
   -912271714811904, 421169622679552, -1583672600821760, 549205787541504, -2045554230034432,
   399049065103360, -1993159954268160, -57541452791808, -1459572479442944, -572255534497792,
   -769604300939264, -829927016361984, -244247682539520, -742055884801024, 6226122194432,
   -472015520323840, 59077811088384, -222779965107968, 37609461461632, -78965168392960,
   13625875572672, -20963174484864, 3060481811008, -4108994117424, 357364061016, -577379112884,
   -12389083230, -54663524459, -13084604378, -2915200717, -2554784570, -3761132, -286468094,
   12136560, -20761670, 937853, -987990, 35291, -29886, 698, -522, 6, -4]
/-- Denominator exponents of `CM2_31` over `bases`. -/
def eCM2_31 : List ℕ := [0, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^3 y₁^1` in `h₂` (the `x₃` component of the manifold). -/
def CM2_31 (s : ℝ) : ℝ := zeval nCM2_31 s / bval bases eCM2_31 s

/-- Numerator coefficients (constant term first) of `CM2_22`. -/
def nCM2_22 : List ℤ :=
  [0, 0, 0, 0, 5435817984, 0, 108263374848, 0, 893982343168, 0, 4096097517568, 0, 11796637548544, 0,
   22993943199744, 0, 32004205838336, 0, 33175479177216, 0, 26364128247808, 0, 16204830562816, 0,
   7562262092800, 0, 2531174187072, 0, 519615656576, 0, 15975094448, 0, -30806440784, 0,
   -12635121250, 0, -3001779080, 0, -502013167, 0, -60879671, 0, -5230330, 0, -303342, 0, -11075, 0,
   -227, 0, -2]
/-- Denominator exponents of `CM2_22` over `bases`. -/
def eCM2_22 : List ℕ := [0, 0, 0, 0, 3, 2, 1, 1]
/-- Coefficient of `y₀^2 y₁^2` in `h₂` (the `x₃` component of the manifold). -/
def CM2_22 (s : ℝ) : ℝ := zeval nCM2_22 s / bval bases eCM2_22 s

/-- Numerator coefficients (constant term first) of `CM2_13`. -/
def nCM2_13 : List ℤ :=
  [0, 0, 0, 0, -115964116992, -115964116992, -2367600721920, -2073395462144, -21228144295936,
   -16196321673216, -111119930753024, -73284792090624, -381186887122944, -214036230701056,
   -912271714811904, -421169622679552, -1583672600821760, -549205787541504, -2045554230034432,
   -399049065103360, -1993159954268160, 57541452791808, -1459572479442944, 572255534497792,
   -769604300939264, 829927016361984, -244247682539520, 742055884801024, 6226122194432,
   472015520323840, 59077811088384, 222779965107968, 37609461461632, 78965168392960, 13625875572672,
   20963174484864, 3060481811008, 4108994117424, 357364061016, 577379112884, -12389083230,
   54663524459, -13084604378, 2915200717, -2554784570, 3761132, -286468094, -12136560, -20761670,
   -937853, -987990, -35291, -29886, -698, -522, -6, -4]
/-- Denominator exponents of `CM2_13` over `bases`. -/
def eCM2_13 : List ℕ := [0, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^1 y₁^3` in `h₂` (the `x₃` component of the manifold). -/
def CM2_13 (s : ℝ) : ℝ := zeval nCM2_13 s / bval bases eCM2_13 s

/-- Numerator coefficients (constant term first) of `CM2_04`. -/
def nCM2_04 : List ℤ :=
  [0, 0, 0, 0, 260919263232, 115964116992, 5692710715392, 2908229730304, 53574482526208,
   29982764040192, 292663114858496, 175448373854208, 1056031723487232, 670994586927104,
   2717947322695680, 1814525370171392, 5261551912091648, 3637582070022144, 7964079001108480,
   5563156164116480, 9678689785675776, 6604344662163456, 9573771268874240, 6151812709138432,
   7717349628588032, 4526737890932736, 5028238360648704, 2641141566914560, 2612644455542272,
   1222139859768064, 1065635018986752, 446505440655872, 335260491438272, 127428034339456,
   79617300786336, 27880946397600, 13807279933712, 4536682884408, 1632872062176, 520089914120,
   104689445994, 36897397775, -2516107324, 768676681, -1395465943, -141511444, -165436279,
   -17582676, -11574526, -1031561, -528738, -35591, -15555, -698, -267, -6, -2]
/-- Denominator exponents of `CM2_04` over `bases`. -/
def eCM2_04 : List ℕ := [1, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^0 y₁^4` in `h₂` (the `x₃` component of the manifold). -/
def CM2_04 (s : ℝ) : ℝ := zeval nCM2_04 s / bval bases eCM2_04 s

/-- Numerator coefficients (constant term first) of `CA_20`. -/
def nCA_20 : List ℤ :=
  [0, -1024, 1024, -5120, 4352, -8768, 4800, -5984, 1488, -880, -352, 684, -266, 262, -44, 29, -2,
   1]
/-- Denominator exponents of `CA_20` over `bases`. -/
def eCA_20 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^2 y₁^0` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_20 (s : ℝ) : ℝ := zeval nCA_20 s / bval bases eCA_20 s

/-- Numerator coefficients (constant term first) of `CA_11`. -/
def nCA_11 : List ℤ :=
  [0, 0, 0, 512, 0, 2688, 0, 3488, 0, 2200, 0, 876, 0, 210, 0, 25, 0, 1]
/-- Denominator exponents of `CA_11` over `bases`. -/
def eCA_11 : List ℕ := [0, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^1 y₁^1` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_11 (s : ℝ) : ℝ := zeval nCA_11 s / bval bases eCA_11 s

/-- Numerator coefficients (constant term first) of `CA_02`. -/
def nCA_02 : List ℤ :=
  [0, -1024, -1024, -5120, -4352, -8768, -4800, -5984, -1488, -880, 352, 684, 266, 262, 44, 29, 2,
   1]
/-- Denominator exponents of `CA_02` over `bases`. -/
def eCA_02 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- Coefficient of `y₀^0 y₁^2` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_02 (s : ℝ) : ℝ := zeval nCA_02 s / bval bases eCA_02 s

/-- Numerator coefficients (constant term first) of `CA_30`. -/
def nCA_30 : List ℤ :=
  [0, 0, -221184, 0, -2334720, 610304, -8702976, 3362816, -14839296, 7979776, -12545376, 13348992,
   -5919936, 16468176, -4010280, 13615256, -4274328, 7259795, -2666079, 2494851, -866355, 543053,
   -149508, 71494, -13380, 5285, -573, 199, -9, 3]
/-- Denominator exponents of `CA_30` over `bases`. -/
def eCA_30 : List ℕ := [0, 1, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^3 y₁^0` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_30 (s : ℝ) : ℝ := zeval nCA_30 s / bval bases eCA_30 s

/-- Numerator coefficients (constant term first) of `CA_21`. -/
def nCA_21 : List ℤ :=
  [0, 0, 73728, -147456, 892928, -970752, 3890176, -2199552, 7854592, -1672448, 7509536, 631872,
   3242368, 2541744, 283728, 2847936, -336216, 1941895, -224281, 866167, -89537, 243729, -21996,
   40882, -2860, 3805, -163, 175, -3, 3]
/-- Denominator exponents of `CA_21` over `bases`. -/
def eCA_21 : List ℕ := [0, 0, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^2 y₁^1` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_21 (s : ℝ) : ℝ := zeval nCA_21 s / bval bases eCA_21 s

/-- Numerator coefficients (constant term first) of `CA_12`. -/
def nCA_12 : List ℤ :=
  [0, 0, -73728, -147456, -892928, -970752, -3890176, -2199552, -7854592, -1672448, -7509536,
   631872, -3242368, 2541744, -283728, 2847936, 336216, 1941895, 224281, 866167, 89537, 243729,
   21996, 40882, 2860, 3805, 163, 175, 3, 3]
/-- Denominator exponents of `CA_12` over `bases`. -/
def eCA_12 : List ℕ := [0, 0, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^1 y₁^2` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_12 (s : ℝ) : ℝ := zeval nCA_12 s / bval bases eCA_12 s

/-- Numerator coefficients (constant term first) of `CA_03`. -/
def nCA_03 : List ℤ :=
  [0, 0, 221184, 0, 2334720, 610304, 8702976, 3362816, 14839296, 7979776, 12545376, 13348992,
   5919936, 16468176, 4010280, 13615256, 4274328, 7259795, 2666079, 2494851, 866355, 543053, 149508,
   71494, 13380, 5285, 573, 199, 9, 3]
/-- Denominator exponents of `CA_03` over `bases`. -/
def eCA_03 : List ℕ := [0, 1, 0, 0, 2, 1, 1]
/-- Coefficient of `y₀^0 y₁^3` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_03 (s : ℝ) : ℝ := zeval nCA_03 s / bval bases eCA_03 s

/-- Numerator coefficients (constant term first) of `CA_40`. -/
def nCA_40 : List ℤ :=
  [0, 0, 0, -1043677052928, 231928233984, -23070416830464, 6801080713216, -220973114589184,
   76905684402176, -1233917864574976, 484346146324480, -4568390416990208, 1982576969383936,
   -12093106992185344, 5700800680558592, -24067655204864000, 11964334152351744, -37246362560233472,
   18619067488272384, -45674498422145024, 21526997873065984, -44546633463267328, 18292351438422016,
   -34164855210442752, 11040802828460032, -20046371621527552, 4244143991144448, -8523340715237376,
   511353239378944, -2281707596154880, -544192615057408, -139540002909696, -443532897502208,
   185870094477504, -187803089658752, 98244092632320, -53652581060960, 27893394431200,
   -10947481539872, 5294610324884, -1612327446244, 708267677524, -169600529564, 67491924249,
   -12368670760, 4518322278, -585342772, 202393368, -14742912, 5204851, 24988, 20433, 14120, -3324,
   404, -102, 4, -1]
/-- Denominator exponents of `CA_40` over `bases`. -/
def eCA_40 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^4 y₁^0` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_40 (s : ℝ) : ℝ := zeval nCA_40 s / bval bases eCA_40 s

/-- Numerator coefficients (constant term first) of `CA_31`. -/
def nCA_31 : List ℤ :=
  [0, 0, 0, 231928233984, -231928233984, 4696546738176, -3995393327104, 41828149624832,
   -29848412094464, 218647658233856, -128891565899776, 759500508233728, -363331651108864,
   1896520035074048, -717104340795392, 3626159218622464, -1034263682088960, 5595311424667648,
   -1120279413129216, 7207307111563264, -946444114984960, 7818472273707008, -698741670952960,
   7089361622728704, -562957361201152, 5332507662663680, -526211433246720, 3331899109933056,
   -461868761397760, 1743404329281536, -324103754100992, 768133148092416, -172830978762496,
   283337598453888, -69289933062016, 85913317491264, -20810797002928, 20878857496048,
   -4656587749120, 3960459544448, -768376502930, 571640694076, -91933895854, 61166671821,
   -7759053644, 4700316966, -440070050, 247001112, -15124080, 8021611, -218242, 112197, 3484, -1740,
   178, -90, 2, -1]
/-- Denominator exponents of `CA_31` over `bases`. -/
def eCA_31 : List ℕ := [1, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^3 y₁^1` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_31 (s : ℝ) : ℝ := zeval nCA_31 s / bval bases eCA_31 s

/-- Numerator coefficients (constant term first) of `CA_22`. -/
def nCA_22 : List ℤ :=
  [0, 0, 0, -21743271936, 0, -450568912896, 0, -3878875561984, 0, -18588312272896, 0,
   -56163265675264, 0, -115073025048576, 0, -167788751028224, 0, -178237590192128, 0,
   -135284207702016, 0, -64670645479424, 0, -6662464807936, 0, 17906831690496, 0, 17130269305344, 0,
   8923016316736, 0, 3151128820496, 0, 801654817060, 0, 150074465284, 0, 20679815769, 0, 2058180918,
   0, 141725960, 0, 6197635, 0, 137777, 0, -124, 0, -70, 0, -1]
/-- Denominator exponents of `CA_22` over `bases`. -/
def eCA_22 : List ℕ := [2, 0, 0, 0, 3, 2, 1, 1]
/-- Coefficient of `y₀^2 y₁^2` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_22 (s : ℝ) : ℝ := zeval nCA_22 s / bval bases eCA_22 s

/-- Numerator coefficients (constant term first) of `CA_13`. -/
def nCA_13 : List ℤ :=
  [0, 0, 0, 231928233984, 231928233984, 4696546738176, 3995393327104, 41828149624832,
   29848412094464, 218647658233856, 128891565899776, 759500508233728, 363331651108864,
   1896520035074048, 717104340795392, 3626159218622464, 1034263682088960, 5595311424667648,
   1120279413129216, 7207307111563264, 946444114984960, 7818472273707008, 698741670952960,
   7089361622728704, 562957361201152, 5332507662663680, 526211433246720, 3331899109933056,
   461868761397760, 1743404329281536, 324103754100992, 768133148092416, 172830978762496,
   283337598453888, 69289933062016, 85913317491264, 20810797002928, 20878857496048, 4656587749120,
   3960459544448, 768376502930, 571640694076, 91933895854, 61166671821, 7759053644, 4700316966,
   440070050, 247001112, 15124080, 8021611, 218242, 112197, -3484, -1740, -178, -90, -2, -1]
/-- Denominator exponents of `CA_13` over `bases`. -/
def eCA_13 : List ℕ := [1, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^1 y₁^3` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_13 (s : ℝ) : ℝ := zeval nCA_13 s / bval bases eCA_13 s

/-- Numerator coefficients (constant term first) of `CA_04`. -/
def nCA_04 : List ℤ :=
  [0, 0, 0, -1043677052928, -231928233984, -23070416830464, -6801080713216, -220973114589184,
   -76905684402176, -1233917864574976, -484346146324480, -4568390416990208, -1982576969383936,
   -12093106992185344, -5700800680558592, -24067655204864000, -11964334152351744,
   -37246362560233472, -18619067488272384, -45674498422145024, -21526997873065984,
   -44546633463267328, -18292351438422016, -34164855210442752, -11040802828460032,
   -20046371621527552, -4244143991144448, -8523340715237376, -511353239378944, -2281707596154880,
   544192615057408, -139540002909696, 443532897502208, 185870094477504, 187803089658752,
   98244092632320, 53652581060960, 27893394431200, 10947481539872, 5294610324884, 1612327446244,
   708267677524, 169600529564, 67491924249, 12368670760, 4518322278, 585342772, 202393368, 14742912,
   5204851, -24988, 20433, -14120, -3324, -404, -102, -4, -1]
/-- Denominator exponents of `CA_04` over `bases`. -/
def eCA_04 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- Coefficient of `y₀^0 y₁^4` in `x₀ = −h₁ − (2/s) h₂` of the manifold. -/
def CA_04 (s : ℝ) : ℝ := zeval nCA_04 s / bval bases eCA_04 s

/-! ## The critical chart: `π x = (Σ PV0ₖ xₖ, Σ PV1ₖ xₖ)` -/

/-- Numerator coefficients (constant term first) of `PV0_0`. -/
def nPV0_0 : List ℤ :=
  [2, 3, 2, 1]
/-- Denominator exponents of `PV0_0` over `bases`. -/
def ePV0_0 : List ℕ := [1, 0, 0, 0, 1]
/-- `Re pₖ + Im pₖ` for `p = bautinPathP s`, `k = 0`. -/
def PV0_0 (s : ℝ) : ℝ := zeval nPV0_0 s / bval bases ePV0_0 s

/-- Numerator coefficients (constant term first) of `PV0_1`. -/
def nPV0_1 : List ℤ :=
  [0, 4, 4, 7, 0, 1]
/-- Denominator exponents of `PV0_1` over `bases`. -/
def ePV0_1 : List ℕ := [1, 0, 0, 0, 1, 0, 0, 0, 1]
/-- `Re pₖ + Im pₖ` for `p = bautinPathP s`, `k = 1`. -/
def PV0_1 (s : ℝ) : ℝ := zeval nPV0_1 s / bval bases ePV0_1 s

/-- Numerator coefficients (constant term first) of `PV0_2`. -/
def nPV0_2 : List ℤ :=
  [-2, -1, -5, 1, -1]
/-- Denominator exponents of `PV0_2` over `bases`. -/
def ePV0_2 : List ℕ := [1, 0, 0, 0, 1]
/-- `Re pₖ + Im pₖ` for `p = bautinPathP s`, `k = 2`. -/
def PV0_2 (s : ℝ) : ℝ := zeval nPV0_2 s / bval bases ePV0_2 s

/-- Numerator coefficients (constant term first) of `PV0_3`. -/
def nPV0_3 : List ℤ :=
  [2, -3, 2, -1]
/-- Denominator exponents of `PV0_3` over `bases`. -/
def ePV0_3 : List ℕ := [1, 0, 0, 0, 1]
/-- `Re pₖ + Im pₖ` for `p = bautinPathP s`, `k = 3`. -/
def PV0_3 (s : ℝ) : ℝ := zeval nPV0_3 s / bval bases ePV0_3 s

/-- Numerator coefficients (constant term first) of `PV1_0`. -/
def nPV1_0 : List ℤ :=
  [-2, 3, -2, 1]
/-- Denominator exponents of `PV1_0` over `bases`. -/
def ePV1_0 : List ℕ := [1, 0, 0, 0, 1]
/-- `Re pₖ − Im pₖ` for `p = bautinPathP s`, `k = 0`. -/
def PV1_0 (s : ℝ) : ℝ := zeval nPV1_0 s / bval bases ePV1_0 s

/-- Numerator coefficients (constant term first) of `PV1_1`. -/
def nPV1_1 : List ℤ :=
  [0, -4, 4, -7, 0, -1]
/-- Denominator exponents of `PV1_1` over `bases`. -/
def ePV1_1 : List ℕ := [1, 0, 0, 0, 1, 0, 0, 0, 1]
/-- `Re pₖ − Im pₖ` for `p = bautinPathP s`, `k = 1`. -/
def PV1_1 (s : ℝ) : ℝ := zeval nPV1_1 s / bval bases ePV1_1 s

/-- Numerator coefficients (constant term first) of `PV1_2`. -/
def nPV1_2 : List ℤ :=
  [2, -1, 5, 1, 1]
/-- Denominator exponents of `PV1_2` over `bases`. -/
def ePV1_2 : List ℕ := [1, 0, 0, 0, 1]
/-- `Re pₖ − Im pₖ` for `p = bautinPathP s`, `k = 2`. -/
def PV1_2 (s : ℝ) : ℝ := zeval nPV1_2 s / bval bases ePV1_2 s

/-- Numerator coefficients (constant term first) of `PV1_3`. -/
def nPV1_3 : List ℤ :=
  [2, 3, 2, 1]
/-- Denominator exponents of `PV1_3` over `bases`. -/
def ePV1_3 : List ℕ := [1, 0, 0, 0, 1]
/-- `Re pₖ − Im pₖ` for `p = bautinPathP s`, `k = 3`. -/
def PV1_3 (s : ℝ) : ℝ := zeval nPV1_3 s / bval bases ePV1_3 s

/-- Numerator coefficients (constant term first) of `DETV`. -/
def nDETV : List ℤ :=
  [0, 0, -1]
/-- Denominator exponents of `DETV` over `bases`. -/
def eDETV : List ℕ := [1, 0, 0, 0, 1, 0, 0, 0, 1]
/-- The determinant `PV0₀ PV1₁ − PV0₁ PV1₀`. -/
def DETV (s : ℝ) : ℝ := zeval nDETV s / bval bases eDETV s

/-! ## The quintic jet of the chart field -/

/-- Numerator coefficients (constant term first) of `JA_20`. -/
def nJA_20 : List ℤ :=
  [0, 0, -32, -16, -32, 8, -42, 7, -13, 1, -1]
/-- Denominator exponents of `JA_20` over `bases`. -/
def eJA_20 : List ℕ := [2, 0, 0, 0, 1]
/-- Coefficient of `y₀^2 y₁^0` in the first chart coordinate of the field. -/
def JA_20 (s : ℝ) : ℝ := zeval nJA_20 s / bval bases eJA_20 s

/-- Numerator coefficients (constant term first) of `JA_11`. -/
def nJA_11 : List ℤ :=
  [0, 0, -32, -48, -64, -56, -50, -15, -13, -1, -1]
/-- Denominator exponents of `JA_11` over `bases`. -/
def eJA_11 : List ℕ := [1, 0, 0, 0, 1]
/-- Coefficient of `y₀^1 y₁^1` in the first chart coordinate of the field. -/
def JA_11 (s : ℝ) : ℝ := zeval nJA_11 s / bval bases eJA_11 s

/-- Numerator coefficients (constant term first) of `JA_02`. -/
def nJA_02 : List ℤ :=
  [0, 0, -32, -80, -96, -120, -58, -37, -13, -3, -1]
/-- Denominator exponents of `JA_02` over `bases`. -/
def eJA_02 : List ℕ := [2, 0, 0, 0, 1]
/-- Coefficient of `y₀^0 y₁^2` in the first chart coordinate of the field. -/
def JA_02 (s : ℝ) : ℝ := zeval nJA_02 s / bval bases eJA_02 s

/-- Numerator coefficients (constant term first) of `JA_30`. -/
def nJA_30 : List ℤ :=
  [0, 0, 0, -16384, -36864, -118784, -194560, -308224, -381184, -405760, -400128, -282880, -270976,
   -93152, -128736, -4248, -41792, 5736, -8380, 1541, -929, 150, -50, 5, -1]
/-- Denominator exponents of `JA_30` over `bases`. -/
def eJA_30 : List ℕ := [1, 1, 0, 0, 2, 1]
/-- Coefficient of `y₀^3 y₁^0` in the first chart coordinate of the field. -/
def JA_30 (s : ℝ) : ℝ := zeval nJA_30 s / bval bases eJA_30 s

/-- Numerator coefficients (constant term first) of `JA_21`. -/
def nJA_21 : List ℤ :=
  [0, 0, 0, -4096, -4096, -33792, 0, -85760, 67072, -103872, 142208, -83392, 120272, -49600, 48552,
   -19276, 8366, -4164, -110, -432, -235, -16, -28, 0, -1]
/-- Denominator exponents of `JA_21` over `bases`. -/
def eJA_21 : List ℕ := [1, 0, 0, 0, 2, 1]
/-- Coefficient of `y₀^2 y₁^1` in the first chart coordinate of the field. -/
def JA_21 (s : ℝ) : ℝ := zeval nJA_21 s / bval bases eJA_21 s

/-- Numerator coefficients (constant term first) of `JA_12`. -/
def nJA_12 : List ℤ :=
  [0, 0, 0, 0, 4096, -16384, 38912, -87040, 107776, -182016, 141056, -211136, 93632, -147728, 29024,
   -63072, 1832, -16104, -1184, -2341, -313, -174, -30, -5, -1]
/-- Denominator exponents of `JA_12` over `bases`. -/
def eJA_12 : List ℕ := [1, 0, 0, 0, 2, 1]
/-- Coefficient of `y₀^1 y₁^2` in the first chart coordinate of the field. -/
def JA_12 (s : ℝ) : ℝ := zeval nJA_12 s / bval bases eJA_12 s

/-- Numerator coefficients (constant term first) of `JA_03`. -/
def nJA_03 : List ℤ :=
  [0, 0, 0, 20480, 12288, 111616, 57344, 205568, 15872, 102080, -176256, -125632, -276976, -196736,
   -182712, -110340, -62642, -31212, -11698, -4666, -1163, -348, -56, -10, -1]
/-- Denominator exponents of `JA_03` over `bases`. -/
def eJA_03 : List ℕ := [1, 1, 0, 0, 2, 1]
/-- Coefficient of `y₀^0 y₁^3` in the first chart coordinate of the field. -/
def JA_03 (s : ℝ) : ℝ := zeval nJA_03 s / bval bases eJA_03 s

/-- Numerator coefficients (constant term first) of `JA_40`. -/
def nJA_40 : List ℤ :=
  [0, 0, 56623104, 254803968, 506462208, 3085959168, -40108032, 15390867456, -15751970816,
   45825851392, -81180205056, 103578251264, -210614562816, 201497722880, -336163428352,
   328034978816, -355902775296, 415247196160, -263680855296, 393657189888, -148084660736,
   277348262400, -71994964704, 145372633680, -33337366920, 56514452316, -13648116868, 16061795780,
   -4267378626, 3234428623, -920198397, 435662614, -126771496, 34718072, -9831576, 989257, -237093,
   -75529, 24379, -7936, 2310, -266, 78, -3, 1]
/-- Denominator exponents of `JA_40` over `bases`. -/
def eJA_40 : List ℕ := [4, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^4 y₁^0` in the first chart coordinate of the field. -/
def JA_40 (s : ℝ) : ℝ := zeval nJA_40 s / bval bases eJA_40 s

/-- Numerator coefficients (constant term first) of `JA_31`. -/
def nJA_31 : List ℤ :=
  [0, 0, 0, 56623104, -226492416, 978321408, -3576692736, 7252082688, -23269474304, 31781552128,
   -84738244608, 91878989824, -196904304640, 182273847296, -315788304384, 253049216512,
   -367902085120, 249430968832, -321357576960, 176498638976, -214563670976, 90281115552,
   -111333429840, 33538111200, -45802573200, 9145357632, -15200375872, 1895031242, -4050099744,
   318541619, -832639601, 44488408, -123343202, 4455750, -11973512, 192477, -634903, -12633, -5353,
   -1934, 1304, -80, 66, -1, 1]
/-- Denominator exponents of `JA_31` over `bases`. -/
def eJA_31 : List ℕ := [2, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^3 y₁^1` in the first chart coordinate of the field. -/
def JA_31 (s : ℝ) : ℝ := zeval nJA_31 s / bval bases eJA_31 s

/-- Numerator coefficients (constant term first) of `JA_22`. -/
def nJA_22 : List ℤ :=
  [0, 0, 18874368, 47185920, 263192576, 775946240, 1203503104, 4923719680, 1822949376, 16786325504,
   -2910511104, 34717683712, -18099204096, 44754546688, -42855161856, 31119633408, -72425549824,
   -2770491392, -96827517696, -32408956288, -99908291328, -38780884416, -76713981600, -26831357680,
   -43094200696, -12447233476, -17609042772, -4028975368, -5206237294, -913202969, -1100427269,
   -142054518, -162128412, -14448228, -15820648, -858631, -907321, -19049, -18509, 804, 938, 58, 62,
   1, 1]
/-- Denominator exponents of `JA_22` over `bases`. -/
def eJA_22 : List ℕ := [3, 0, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^2 y₁^2` in the first chart coordinate of the field. -/
def JA_22 (s : ℝ) : ℝ := zeval nJA_22 s / bval bases eJA_22 s

/-- Numerator coefficients (constant term first) of `JA_13`. -/
def nJA_13 : List ℤ :=
  [0, 0, 0, 56623104, -113246208, 676331520, -1956642816, 2310144000, -13973061632, -2362966016,
   -57416220672, -40158355456, -154785644544, -137697906688, -290804322304, -265727136256,
   -393475562496, -339045384704, -392542949376, -306574143360, -294703012928, -204696063072,
   -169518030384, -103502491200, -75635351040, -40000602384, -26201046256, -11706070690,
   -6942177852, -2524182677, -1363820505, -383817140, -189639286, -38405686, -17390952, -2183507,
   -908955, -33433, -13073, 3446, 1212, 196, 66, 3, 1]
/-- Denominator exponents of `JA_13` over `bases`. -/
def eJA_13 : List ℕ := [2, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^1 y₁^3` in the first chart coordinate of the field. -/
def JA_13 (s : ℝ) : ℝ := zeval nJA_13 s / bval bases eJA_13 s

/-- Numerator coefficients (constant term first) of `JA_04`. -/
def nJA_04 : List ℤ :=
  [0, 0, 56623104, 28311552, 166723584, 286261248, -3906207744, 458096640, -33127399424,
   -3588030464, -122464739328, -23307014144, -273818546176, -81332248576, -425009301504,
   -203603416064, -504420327424, -365014802432, -489425508096, -458657328640, -394892677376,
   -402797376384, -256949757024, -248383663152, -128679479784, -107826510084, -47657677252,
   -32815065652, -12654627162, -6898269313, -2339223629, -970042946, -289189904, -85167456,
   -22113464, -3829047, -822157, 5367, 8555, 9160, 2126, 382, 78, 5, 1]
/-- Denominator exponents of `JA_04` over `bases`. -/
def eJA_04 : List ℕ := [4, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^0 y₁^4` in the first chart coordinate of the field. -/
def JA_04 (s : ℝ) : ℝ := zeval nJA_04 s / bval bases eJA_04 s

/-- Numerator coefficients (constant term first) of `JA_50`. -/
def nJA_50 : List ℤ :=
  [0, 0, 0, 0, 29377576304640, -10926396801024, 622108832956416, -367297013219328, 5749642654384128,
   -4867894458449920, 30962160465084416, -35621138050580480, 109378629946834944,
   -165306405182504960, 269119030009266176, -524162054949437440, 470703835367604224,
   -1187770092268552192, 562362573928792064, -1976426666349559808, 345478329806618624,
   -2445410720073383936, -250039877230657536, -2233804682221846528, -1030575916765118464,
   -1427965550068531200, -1620537980979085312, -489732728571437056, -1739862754599727104,
   150666159997333504, -1413070352332232704, 373610604599347200, -899753353233159168,
   319808801830807040, -456145241475355392, 184235623872859776, -185346919159679232,
   79246695581708416, -60459672812822880, 26252038653997152, -15802786173036816, 6760951042073400,
   -3294870917323440, 1354550850535288, -544354740773202, 210279331603758, -70627450421909,
   25108465181136, -7107619803594, 2280869624555, -544175123199, 155037409715, -30586540201,
   7669180219, -1162911105, 261286695, -22402177, 5326089, 295571, 31057, 31439, -1109, 786, -19, 7]
/-- Denominator exponents of `JA_50` over `bases`. -/
def eJA_50 : List ℕ := [3, 1, 1, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^5 y₁^0` in the first chart coordinate of the field. -/
def JA_50 (s : ℝ) : ℝ := zeval nJA_50 s / bval bases eJA_50 s

/-- Numerator coefficients (constant term first) of `JA_41`. -/
def nJA_41 : List ℤ :=
  [0, 0, 0, -927712935936, 2783138807808, -27084063768576, 55353538510848, -381296459120640,
   468344708792320, -3243153427529728, 2269422601371648, -18013602195701760, 7370636997427200,
   -68209723911962624, 18917716467384320, -180997788413198336, 45799451817672704,
   -340969432526356480, 109044985065635840, -451275759662661632, 228253502713888768,
   -391131864056856576, 379661719636410368, -148727061462974464, 480533861065588736,
   138102788071849984, 454043772297543680, 308237362950897664, 311954968130547712,
   316173160268673024, 144220326260299776, 228842391979845632, 30564899364275200,
   130182174226511872, -13819739158675200, 61079737448982016, -17367493711197056, 24061938722892992,
   -9584126244389472, 7922112688564640, -3581451813014096, 2141289764521104, -986181792843432,
   464934859432428, -205046352068042, 79436668334292, -32276952206081, 10478277263459,
   -3807660589354, 1046615833408, -328818175775, 77366818845, -19819388845, 4100238942, -740119749,
   147916645, -9311145, 3260180, 585619, 29943, 34899, -310, 794, -8, 7]
/-- Denominator exponents of `JA_41` over `bases`. -/
def eJA_41 : List ℕ := [3, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^4 y₁^1` in the first chart coordinate of the field. -/
def JA_41 (s : ℝ) : ℝ := zeval nJA_41 s / bval bases eJA_41 s

/-- Numerator coefficients (constant term first) of `JA_32`. -/
def nJA_32 : List ℤ :=
  [0, 0, 0, 0, 2473901162496, 9483287789568, 41566693490688, 197731704373248, 242940530130944,
   1840004791795712, 247869541974016, 10208555831394304, -4283900104802304, 37986162328993792,
   -28111595368349696, 100551479177248768, -94398537751592960, 194487136408305664,
   -211013070252670976, 275431925657632768, -343511947461263360, 277681859208413184,
   -426933126282477568, 180179205786697728, -417272719258877952, 41949000574140416,
   -327901039982641152, -52517112224890880, -212189124084207616, -72486474731573248,
   -117290983983122432, -48322108963072000, -58447618542141952, -20466079573455360,
   -27569892137066752, -5395270779973632, -12313291012547456, -536279020356608, -4943188028482688,
   240267153622336, -1677079385484720, 146769175314736, -459978382765280, 45243323478800,
   -99135976549558, 9753528162162, -16427485056601, 1573128269286, -2043634632178, 192261389225,
   -184160151491, 17679838783, -11205895913, 1204137357, -374005405, 59420483, 1585671, 2055875,
   803959, 46917, 37427, 613, 802, 3, 7]
/-- Denominator exponents of `JA_32` over `bases`. -/
def eJA_32 : List ℕ := [2, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^3 y₁^2` in the first chart coordinate of the field. -/
def JA_32 (s : ℝ) : ℝ := zeval nJA_32 s / bval bases eJA_32 s

/-- Numerator coefficients (constant term first) of `JA_23`. -/
def nJA_23 : List ℤ :=
  [0, 0, 0, -927712935936, 2473901162496, -19868518711296, 36850819399680, -197892765646848,
   159347581648896, -1278953213919232, -416476536242176, -6136601356795904, -7426872749064192,
   -22638950925467648, -37914798897233920, -63586689926299648, -115222131427508224,
   -134172864239632384, -240683350711336960, -212557200194797568, -370283957595406336,
   -258034285049151488, -442589599889620992, -255297078356672512, -435063110940295168,
   -233065020500606976, -373826894305951744, -220337665917657088, -293052724324970496,
   -207842183964188672, -209555919942338560, -172422348134393856, -132188690916619776,
   -116000977979524096, -70944830415125760, -61507481844996480, -31639489248963840,
   -25549758890415296, -11574485762597568, -8313691654791744, -3443501246382000, -2117637526140792,
   -825685875295608, -420602928450692, -157664540862342, -64572339017616, -23578669165829,
   -7541481943095, -2696545601490, -651624073162, -227133597411, -39509699143, -13111102717,
   -1478973080, -421667553, -17623599, 1465247, 1252566, 835223, 71683, 38303, 1588, 810, 14, 7]
/-- Denominator exponents of `JA_23` over `bases`. -/
def eJA_23 : List ℕ := [2, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^2 y₁^3` in the first chart coordinate of the field. -/
def JA_23 (s : ℝ) : ℝ := zeval nJA_23 s / bval bases eJA_23 s

/-- Numerator coefficients (constant term first) of `JA_14`. -/
def nJA_14 : List ℤ :=
  [0, 0, 0, 0, -927712935936, 6803228196864, -32753420599296, 162736310845440, -405432027840512,
   1727564695470080, -2514907362754560, 10888441101287424, -8575775158566912, 45665974963142656,
   -14272675648110592, 134115281587929088, 4008083286130688, 279850858525491200, 78449684196098048,
   405031866779828224, 196065578616094720, 359351068018606080, 265336496803807232,
   57701347416866816, 187998222851735552, -384410672407150592, -22749223959494656,
   -718356670884995072, -235982847821066240, -782410328350347264, -328052924796377088,
   -616845084240394240, -285115913542313984, -375548459055729152, -180207579494115072,
   -181332062390323328, -86932181222348288, -70163299361593984, -32630438167842336,
   -21780853525264480, -9598147510293968, -5398509307289592, -2213368019139984, -1058674102158264,
   -398374086620522, -162183100799370, -55446177021485, -19080035203396, -5874413331514,
   -1682714975177, -461261618999, -107088580245, -25509052105, -4571023281, -875395497, -106509857,
   -9350673, 178637, 685579, 92217, 37575, 2543, 818, 25, 7]
/-- Denominator exponents of `JA_14` over `bases`. -/
def eJA_14 : List ℕ := [3, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^1 y₁^4` in the first chart coordinate of the field. -/
def JA_14 (s : ℝ) : ℝ := zeval nJA_14 s / bval bases eJA_14 s

/-- Numerator coefficients (constant term first) of `JA_05`. -/
def nJA_05 : List ℤ :=
  [0, 0, 0, -4638564679680, 10823317585920, -48421461295104, 235432927297536, 241224690696192,
   2362287847374848, 6853919548375040, 14672662160736256, 53829875374489600, 63494751428542464,
   244944342089728000, 202252727307206656, 751630331014021120, 483185569011073024,
   1655030311643250688, 855602701338148864, 2680963057337761792, 1057048835940941824,
   3178679326089805824, 709292117455929344, 2603845640923840512, -299322406692225024,
   1111779800549457920, -1528732861201907712, -472328650243260416, -2273963013470900224,
   -1358397872922136576, -2195203850536577024, -1387761689606318080, -1551128416521177088,
   -946051026199449600, -836279293325032192, -478487280029355264, -350344682798628992,
   -185986107318473024, -114987453832242080, -56306462715075488, -29648629126697616,
   -13328283377521760, -5999843779509320, -2462725535511412, -949108033680082, -353114676254292,
   -116524569058489, -38880052896849, -10976096212954, -3232496077060, -778061680439, -197317438475,
   -39993845741, -8383532766, -1362587725, -216685315, -21393657, -1567576, 482731, 98607, 36059,
   3406, 826, 36, 7]
/-- Denominator exponents of `JA_05` over `bases`. -/
def eJA_05 : List ℕ := [3, 1, 1, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^0 y₁^5` in the first chart coordinate of the field. -/
def JA_05 (s : ℝ) : ℝ := zeval nJA_05 s / bval bases eJA_05 s

/-- Numerator coefficients (constant term first) of `JB_20`. -/
def nJB_20 : List ℤ :=
  [0, 0, 32, -80, 96, -120, 58, -37, 13, -3, 1]
/-- Denominator exponents of `JB_20` over `bases`. -/
def eJB_20 : List ℕ := [2, 0, 0, 0, 1]
/-- Coefficient of `y₀^2 y₁^0` in the second chart coordinate of the field. -/
def JB_20 (s : ℝ) : ℝ := zeval nJB_20 s / bval bases eJB_20 s

/-- Numerator coefficients (constant term first) of `JB_11`. -/
def nJB_11 : List ℤ :=
  [0, 0, 32, -48, 64, -56, 50, -15, 13, -1, 1]
/-- Denominator exponents of `JB_11` over `bases`. -/
def eJB_11 : List ℕ := [1, 0, 0, 0, 1]
/-- Coefficient of `y₀^1 y₁^1` in the second chart coordinate of the field. -/
def JB_11 (s : ℝ) : ℝ := zeval nJB_11 s / bval bases eJB_11 s

/-- Numerator coefficients (constant term first) of `JB_02`. -/
def nJB_02 : List ℤ :=
  [0, 0, 32, -16, 32, 8, 42, 7, 13, 1, 1]
/-- Denominator exponents of `JB_02` over `bases`. -/
def eJB_02 : List ℕ := [2, 0, 0, 0, 1]
/-- Coefficient of `y₀^0 y₁^2` in the second chart coordinate of the field. -/
def JB_02 (s : ℝ) : ℝ := zeval nJB_02 s / bval bases eJB_02 s

/-- Numerator coefficients (constant term first) of `JB_30`. -/
def nJB_30 : List ℤ :=
  [0, 0, 0, 20480, -12288, 111616, -57344, 205568, -15872, 102080, 176256, -125632, 276976, -196736,
   182712, -110340, 62642, -31212, 11698, -4666, 1163, -348, 56, -10, 1]
/-- Denominator exponents of `JB_30` over `bases`. -/
def eJB_30 : List ℕ := [1, 1, 0, 0, 2, 1]
/-- Coefficient of `y₀^3 y₁^0` in the second chart coordinate of the field. -/
def JB_30 (s : ℝ) : ℝ := zeval nJB_30 s / bval bases eJB_30 s

/-- Numerator coefficients (constant term first) of `JB_21`. -/
def nJB_21 : List ℤ :=
  [0, 0, 0, 0, -4096, -16384, -38912, -87040, -107776, -182016, -141056, -211136, -93632, -147728,
   -29024, -63072, -1832, -16104, 1184, -2341, 313, -174, 30, -5, 1]
/-- Denominator exponents of `JB_21` over `bases`. -/
def eJB_21 : List ℕ := [1, 0, 0, 0, 2, 1]
/-- Coefficient of `y₀^2 y₁^1` in the second chart coordinate of the field. -/
def JB_21 (s : ℝ) : ℝ := zeval nJB_21 s / bval bases eJB_21 s

/-- Numerator coefficients (constant term first) of `JB_12`. -/
def nJB_12 : List ℤ :=
  [0, 0, 0, -4096, 4096, -33792, 0, -85760, -67072, -103872, -142208, -83392, -120272, -49600,
   -48552, -19276, -8366, -4164, 110, -432, 235, -16, 28, 0, 1]
/-- Denominator exponents of `JB_12` over `bases`. -/
def eJB_12 : List ℕ := [1, 0, 0, 0, 2, 1]
/-- Coefficient of `y₀^1 y₁^2` in the second chart coordinate of the field. -/
def JB_12 (s : ℝ) : ℝ := zeval nJB_12 s / bval bases eJB_12 s

/-- Numerator coefficients (constant term first) of `JB_03`. -/
def nJB_03 : List ℤ :=
  [0, 0, 0, -16384, 36864, -118784, 194560, -308224, 381184, -405760, 400128, -282880, 270976,
   -93152, 128736, -4248, 41792, 5736, 8380, 1541, 929, 150, 50, 5, 1]
/-- Denominator exponents of `JB_03` over `bases`. -/
def eJB_03 : List ℕ := [1, 1, 0, 0, 2, 1]
/-- Coefficient of `y₀^0 y₁^3` in the second chart coordinate of the field. -/
def JB_03 (s : ℝ) : ℝ := zeval nJB_03 s / bval bases eJB_03 s

/-- Numerator coefficients (constant term first) of `JB_40`. -/
def nJB_40 : List ℤ :=
  [0, 0, -56623104, 28311552, -166723584, 286261248, 3906207744, 458096640, 33127399424,
   -3588030464, 122464739328, -23307014144, 273818546176, -81332248576, 425009301504, -203603416064,
   504420327424, -365014802432, 489425508096, -458657328640, 394892677376, -402797376384,
   256949757024, -248383663152, 128679479784, -107826510084, 47657677252, -32815065652, 12654627162,
   -6898269313, 2339223629, -970042946, 289189904, -85167456, 22113464, -3829047, 822157, 5367,
   -8555, 9160, -2126, 382, -78, 5, -1]
/-- Denominator exponents of `JB_40` over `bases`. -/
def eJB_40 : List ℕ := [4, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^4 y₁^0` in the second chart coordinate of the field. -/
def JB_40 (s : ℝ) : ℝ := zeval nJB_40 s / bval bases eJB_40 s

/-- Numerator coefficients (constant term first) of `JB_31`. -/
def nJB_31 : List ℤ :=
  [0, 0, 0, 56623104, 113246208, 676331520, 1956642816, 2310144000, 13973061632, -2362966016,
   57416220672, -40158355456, 154785644544, -137697906688, 290804322304, -265727136256,
   393475562496, -339045384704, 392542949376, -306574143360, 294703012928, -204696063072,
   169518030384, -103502491200, 75635351040, -40000602384, 26201046256, -11706070690, 6942177852,
   -2524182677, 1363820505, -383817140, 189639286, -38405686, 17390952, -2183507, 908955, -33433,
   13073, 3446, -1212, 196, -66, 3, -1]
/-- Denominator exponents of `JB_31` over `bases`. -/
def eJB_31 : List ℕ := [2, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^3 y₁^1` in the second chart coordinate of the field. -/
def JB_31 (s : ℝ) : ℝ := zeval nJB_31 s / bval bases eJB_31 s

/-- Numerator coefficients (constant term first) of `JB_22`. -/
def nJB_22 : List ℤ :=
  [0, 0, -18874368, 47185920, -263192576, 775946240, -1203503104, 4923719680, -1822949376,
   16786325504, 2910511104, 34717683712, 18099204096, 44754546688, 42855161856, 31119633408,
   72425549824, -2770491392, 96827517696, -32408956288, 99908291328, -38780884416, 76713981600,
   -26831357680, 43094200696, -12447233476, 17609042772, -4028975368, 5206237294, -913202969,
   1100427269, -142054518, 162128412, -14448228, 15820648, -858631, 907321, -19049, 18509, 804,
   -938, 58, -62, 1, -1]
/-- Denominator exponents of `JB_22` over `bases`. -/
def eJB_22 : List ℕ := [3, 0, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^2 y₁^2` in the second chart coordinate of the field. -/
def JB_22 (s : ℝ) : ℝ := zeval nJB_22 s / bval bases eJB_22 s

/-- Numerator coefficients (constant term first) of `JB_13`. -/
def nJB_13 : List ℤ :=
  [0, 0, 0, 56623104, 226492416, 978321408, 3576692736, 7252082688, 23269474304, 31781552128,
   84738244608, 91878989824, 196904304640, 182273847296, 315788304384, 253049216512, 367902085120,
   249430968832, 321357576960, 176498638976, 214563670976, 90281115552, 111333429840, 33538111200,
   45802573200, 9145357632, 15200375872, 1895031242, 4050099744, 318541619, 832639601, 44488408,
   123343202, 4455750, 11973512, 192477, 634903, -12633, 5353, -1934, -1304, -80, -66, -1, -1]
/-- Denominator exponents of `JB_13` over `bases`. -/
def eJB_13 : List ℕ := [2, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^1 y₁^3` in the second chart coordinate of the field. -/
def JB_13 (s : ℝ) : ℝ := zeval nJB_13 s / bval bases eJB_13 s

/-- Numerator coefficients (constant term first) of `JB_04`. -/
def nJB_04 : List ℤ :=
  [0, 0, -56623104, 254803968, -506462208, 3085959168, 40108032, 15390867456, 15751970816,
   45825851392, 81180205056, 103578251264, 210614562816, 201497722880, 336163428352, 328034978816,
   355902775296, 415247196160, 263680855296, 393657189888, 148084660736, 277348262400, 71994964704,
   145372633680, 33337366920, 56514452316, 13648116868, 16061795780, 4267378626, 3234428623,
   920198397, 435662614, 126771496, 34718072, 9831576, 989257, 237093, -75529, -24379, -7936, -2310,
   -266, -78, -3, -1]
/-- Denominator exponents of `JB_04` over `bases`. -/
def eJB_04 : List ℕ := [4, 1, 0, 0, 3, 2, 1]
/-- Coefficient of `y₀^0 y₁^4` in the second chart coordinate of the field. -/
def JB_04 (s : ℝ) : ℝ := zeval nJB_04 s / bval bases eJB_04 s

/-- Numerator coefficients (constant term first) of `JB_50`. -/
def nJB_50 : List ℤ :=
  [0, 0, 0, -4638564679680, -10823317585920, -48421461295104, -235432927297536, 241224690696192,
   -2362287847374848, 6853919548375040, -14672662160736256, 53829875374489600, -63494751428542464,
   244944342089728000, -202252727307206656, 751630331014021120, -483185569011073024,
   1655030311643250688, -855602701338148864, 2680963057337761792, -1057048835940941824,
   3178679326089805824, -709292117455929344, 2603845640923840512, 299322406692225024,
   1111779800549457920, 1528732861201907712, -472328650243260416, 2273963013470900224,
   -1358397872922136576, 2195203850536577024, -1387761689606318080, 1551128416521177088,
   -946051026199449600, 836279293325032192, -478487280029355264, 350344682798628992,
   -185986107318473024, 114987453832242080, -56306462715075488, 29648629126697616,
   -13328283377521760, 5999843779509320, -2462725535511412, 949108033680082, -353114676254292,
   116524569058489, -38880052896849, 10976096212954, -3232496077060, 778061680439, -197317438475,
   39993845741, -8383532766, 1362587725, -216685315, 21393657, -1567576, -482731, 98607, -36059,
   3406, -826, 36, -7]
/-- Denominator exponents of `JB_50` over `bases`. -/
def eJB_50 : List ℕ := [3, 1, 1, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^5 y₁^0` in the second chart coordinate of the field. -/
def JB_50 (s : ℝ) : ℝ := zeval nJB_50 s / bval bases eJB_50 s

/-- Numerator coefficients (constant term first) of `JB_41`. -/
def nJB_41 : List ℤ :=
  [0, 0, 0, 0, 927712935936, 6803228196864, 32753420599296, 162736310845440, 405432027840512,
   1727564695470080, 2514907362754560, 10888441101287424, 8575775158566912, 45665974963142656,
   14272675648110592, 134115281587929088, -4008083286130688, 279850858525491200, -78449684196098048,
   405031866779828224, -196065578616094720, 359351068018606080, -265336496803807232,
   57701347416866816, -187998222851735552, -384410672407150592, 22749223959494656,
   -718356670884995072, 235982847821066240, -782410328350347264, 328052924796377088,
   -616845084240394240, 285115913542313984, -375548459055729152, 180207579494115072,
   -181332062390323328, 86932181222348288, -70163299361593984, 32630438167842336,
   -21780853525264480, 9598147510293968, -5398509307289592, 2213368019139984, -1058674102158264,
   398374086620522, -162183100799370, 55446177021485, -19080035203396, 5874413331514,
   -1682714975177, 461261618999, -107088580245, 25509052105, -4571023281, 875395497, -106509857,
   9350673, 178637, -685579, 92217, -37575, 2543, -818, 25, -7]
/-- Denominator exponents of `JB_41` over `bases`. -/
def eJB_41 : List ℕ := [3, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^4 y₁^1` in the second chart coordinate of the field. -/
def JB_41 (s : ℝ) : ℝ := zeval nJB_41 s / bval bases eJB_41 s

/-- Numerator coefficients (constant term first) of `JB_32`. -/
def nJB_32 : List ℤ :=
  [0, 0, 0, -927712935936, -2473901162496, -19868518711296, -36850819399680, -197892765646848,
   -159347581648896, -1278953213919232, 416476536242176, -6136601356795904, 7426872749064192,
   -22638950925467648, 37914798897233920, -63586689926299648, 115222131427508224,
   -134172864239632384, 240683350711336960, -212557200194797568, 370283957595406336,
   -258034285049151488, 442589599889620992, -255297078356672512, 435063110940295168,
   -233065020500606976, 373826894305951744, -220337665917657088, 293052724324970496,
   -207842183964188672, 209555919942338560, -172422348134393856, 132188690916619776,
   -116000977979524096, 70944830415125760, -61507481844996480, 31639489248963840,
   -25549758890415296, 11574485762597568, -8313691654791744, 3443501246382000, -2117637526140792,
   825685875295608, -420602928450692, 157664540862342, -64572339017616, 23578669165829,
   -7541481943095, 2696545601490, -651624073162, 227133597411, -39509699143, 13111102717,
   -1478973080, 421667553, -17623599, -1465247, 1252566, -835223, 71683, -38303, 1588, -810, 14, -7]
/-- Denominator exponents of `JB_32` over `bases`. -/
def eJB_32 : List ℕ := [2, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^3 y₁^2` in the second chart coordinate of the field. -/
def JB_32 (s : ℝ) : ℝ := zeval nJB_32 s / bval bases eJB_32 s

/-- Numerator coefficients (constant term first) of `JB_23`. -/
def nJB_23 : List ℤ :=
  [0, 0, 0, 0, -2473901162496, 9483287789568, -41566693490688, 197731704373248, -242940530130944,
   1840004791795712, -247869541974016, 10208555831394304, 4283900104802304, 37986162328993792,
   28111595368349696, 100551479177248768, 94398537751592960, 194487136408305664, 211013070252670976,
   275431925657632768, 343511947461263360, 277681859208413184, 426933126282477568,
   180179205786697728, 417272719258877952, 41949000574140416, 327901039982641152,
   -52517112224890880, 212189124084207616, -72486474731573248, 117290983983122432,
   -48322108963072000, 58447618542141952, -20466079573455360, 27569892137066752, -5395270779973632,
   12313291012547456, -536279020356608, 4943188028482688, 240267153622336, 1677079385484720,
   146769175314736, 459978382765280, 45243323478800, 99135976549558, 9753528162162, 16427485056601,
   1573128269286, 2043634632178, 192261389225, 184160151491, 17679838783, 11205895913, 1204137357,
   374005405, 59420483, -1585671, 2055875, -803959, 46917, -37427, 613, -802, 3, -7]
/-- Denominator exponents of `JB_23` over `bases`. -/
def eJB_23 : List ℕ := [2, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^2 y₁^3` in the second chart coordinate of the field. -/
def JB_23 (s : ℝ) : ℝ := zeval nJB_23 s / bval bases eJB_23 s

/-- Numerator coefficients (constant term first) of `JB_14`. -/
def nJB_14 : List ℤ :=
  [0, 0, 0, -927712935936, -2783138807808, -27084063768576, -55353538510848, -381296459120640,
   -468344708792320, -3243153427529728, -2269422601371648, -18013602195701760, -7370636997427200,
   -68209723911962624, -18917716467384320, -180997788413198336, -45799451817672704,
   -340969432526356480, -109044985065635840, -451275759662661632, -228253502713888768,
   -391131864056856576, -379661719636410368, -148727061462974464, -480533861065588736,
   138102788071849984, -454043772297543680, 308237362950897664, -311954968130547712,
   316173160268673024, -144220326260299776, 228842391979845632, -30564899364275200,
   130182174226511872, 13819739158675200, 61079737448982016, 17367493711197056, 24061938722892992,
   9584126244389472, 7922112688564640, 3581451813014096, 2141289764521104, 986181792843432,
   464934859432428, 205046352068042, 79436668334292, 32276952206081, 10478277263459, 3807660589354,
   1046615833408, 328818175775, 77366818845, 19819388845, 4100238942, 740119749, 147916645, 9311145,
   3260180, -585619, 29943, -34899, -310, -794, -8, -7]
/-- Denominator exponents of `JB_14` over `bases`. -/
def eJB_14 : List ℕ := [3, 1, 0, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^1 y₁^4` in the second chart coordinate of the field. -/
def JB_14 (s : ℝ) : ℝ := zeval nJB_14 s / bval bases eJB_14 s

/-- Numerator coefficients (constant term first) of `JB_05`. -/
def nJB_05 : List ℤ :=
  [0, 0, 0, 0, -29377576304640, -10926396801024, -622108832956416, -367297013219328,
   -5749642654384128, -4867894458449920, -30962160465084416, -35621138050580480,
   -109378629946834944, -165306405182504960, -269119030009266176, -524162054949437440,
   -470703835367604224, -1187770092268552192, -562362573928792064, -1976426666349559808,
   -345478329806618624, -2445410720073383936, 250039877230657536, -2233804682221846528,
   1030575916765118464, -1427965550068531200, 1620537980979085312, -489732728571437056,
   1739862754599727104, 150666159997333504, 1413070352332232704, 373610604599347200,
   899753353233159168, 319808801830807040, 456145241475355392, 184235623872859776,
   185346919159679232, 79246695581708416, 60459672812822880, 26252038653997152, 15802786173036816,
   6760951042073400, 3294870917323440, 1354550850535288, 544354740773202, 210279331603758,
   70627450421909, 25108465181136, 7107619803594, 2280869624555, 544175123199, 155037409715,
   30586540201, 7669180219, 1162911105, 261286695, 22402177, 5326089, -295571, 31057, -31439, -1109,
   -786, -19, -7]
/-- Denominator exponents of `JB_05` over `bases`. -/
def eJB_05 : List ℕ := [3, 1, 1, 0, 4, 3, 1, 1]
/-- Coefficient of `y₀^0 y₁^5` in the second chart coordinate of the field. -/
def JB_05 (s : ℝ) : ℝ := zeval nJB_05 s / bval bases eJB_05 s

/-! ## The Lyapunov polynomial of the jet (`ω = 1`) -/

/-- Numerator coefficients (constant term first) of `LY_c30`. -/
def nLY_c30 : List ℤ :=
  [0, 0, 32, -208, 32, -216, 42, -53, 13, -3, 1]
/-- Denominator exponents of `LY_c30` over `bases`. -/
def eLY_c30 : List ℕ := [1, 1, 0, 0, 1]
/-- The value of `Jet5.c30` (or `Jet.c30`) of the jet at `ω = 1`. -/
def LY_c30 (s : ℝ) : ℝ := zeval nLY_c30 s / bval bases eLY_c30 s

/-- Numerator coefficients (constant term first) of `LY_c21`. -/
def nLY_c21 : List ℤ :=
  [0, 0, 32, 16, 32, -8, 42, -7, 13, -1, 1]
/-- Denominator exponents of `LY_c21` over `bases`. -/
def eLY_c21 : List ℕ := [1, 0, 0, 0, 1]
/-- The value of `Jet5.c21` (or `Jet.c21`) of the jet at `ω = 1`. -/
def LY_c21 (s : ℝ) : ℝ := zeval nLY_c21 s / bval bases eLY_c21 s

/-- Numerator coefficients (constant term first) of `LY_c12`. -/
def nLY_c12 : List ℤ :=
  [0, 0, 32, -16, 32, 8, 42, 7, 13, 1, 1]
/-- Denominator exponents of `LY_c12` over `bases`. -/
def eLY_c12 : List ℕ := [1, 0, 0, 0, 1]
/-- The value of `Jet5.c12` (or `Jet.c12`) of the jet at `ω = 1`. -/
def LY_c12 (s : ℝ) : ℝ := zeval nLY_c12 s / bval bases eLY_c12 s

/-- Numerator coefficients (constant term first) of `LY_c03`. -/
def nLY_c03 : List ℤ :=
  [0, 0, 32, 208, 32, 216, 42, 53, 13, 3, 1]
/-- Denominator exponents of `LY_c03` over `bases`. -/
def eLY_c03 : List ℕ := [1, 1, 0, 0, 1]
/-- The value of `Jet5.c03` (or `Jet.c03`) of the jet at `ω = 1`. -/
def LY_c03 (s : ℝ) : ℝ := zeval nLY_c03 s / bval bases eLY_c03 s

/-- Numerator coefficients (constant term first) of `LY_d40`. -/
def nLY_d40 : List ℤ :=
  [0, 0, 0, 4096, 0, 5120, 0, 11008, 0, 21184, 0, -24320, 0, -70048, 0, -51060, 0, -16428, 0, -2561,
   0, -186, 0, -5]
/-- Denominator exponents of `LY_d40` over `bases`. -/
def eLY_d40 : List ℕ := [0, 1, 0, 0, 2, 1]
/-- The value of `Jet5.d40` (or `Jet.d40`) of the jet at `ω = 1`. -/
def LY_d40 (s : ℝ) : ℝ := zeval nLY_d40 s / bval bases eLY_d40 s

/-- Numerator coefficients (constant term first) of `LY_d31`. -/
def nLY_d31 : List ℤ :=
  [0, 0, 0, 4096, 36864, 5120, 169984, -18944, 313600, -59648, 327936, -100304, 226048, -103204,
   109536, -60354, 36896, -19248, 7780, -3242, 905, -264, 50, -8, 1]
/-- Denominator exponents of `LY_d31` over `bases`. -/
def eLY_d31 : List ℕ := [0, 1, 0, 0, 2, 1]
/-- The value of `Jet5.d31` (or `Jet.d31`) of the jet at `ω = 1`. -/
def LY_d31 (s : ℝ) : ℝ := zeval nLY_d31 s / bval bases eLY_d31 s

/-- Numerator coefficients (constant term first) of `LY_d22`. -/
def nLY_d22 : List ℤ :=
  [0, 0, 0, 4096, 12288, 5120, -45056, 11008, -393728, 21184, -806784, -24320, -770096, -70048,
   -393432, -51060, -110014, -16428, -16124, -2561, -1045, -186, -10, -5, 1]
/-- Denominator exponents of `LY_d22` over `bases`. -/
def eLY_d22 : List ℕ := [0, 1, 0, 0, 2, 1]
/-- The value of `Jet5.d22` (or `Jet.d22`) of the jet at `ω = 1`. -/
def LY_d22 (s : ℝ) : ℝ := zeval nLY_d22 s / bval bases eLY_d22 s

/-- Numerator coefficients (constant term first) of `LY_d13`. -/
def nLY_d13 : List ℤ :=
  [0, 0, 0, -4096, 36864, -5120, 169984, 18944, 313600, 59648, 327936, 100304, 226048, 103204,
   109536, 60354, 36896, 19248, 7780, 3242, 905, 264, 50, 8, 1]
/-- Denominator exponents of `LY_d13` over `bases`. -/
def eLY_d13 : List ℕ := [0, 1, 0, 0, 2, 1]
/-- The value of `Jet5.d13` (or `Jet.d13`) of the jet at `ω = 1`. -/
def LY_d13 (s : ℝ) : ℝ := zeval nLY_d13 s / bval bases eLY_d13 s

/-- Numerator coefficients (constant term first) of `LY_r50`. -/
def nLY_r50 : List ℤ :=
  [0, 0, 56623104, 254803968, 506462208, 3010461696, 752615424, 16150036480, -4131651584,
   57040109568, -11961212928, 155977625600, 19207639040, 335744155648, 150720931840, 546569579520,
   353852780544, 655048211456, 482205595904, 576536367360, 433546624128, 378874287360, 270204647136,
   191531780112, 119878299864, 76798170764, 38771176964, 24642572148, 9466979514, 6171618031,
   1838760811, 1154522886, 297083094, 154660716, 39364404, 14346453, 3954477, 893599, 273835, 35784,
   11928, 842, 290, 9, 3]
/-- Denominator exponents of `LY_r50` over `bases`. -/
def eLY_r50 : List ℕ := [3, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.r50` (or `Jet.r50`) of the jet at `ω = 1`. -/
def LY_r50 (s : ℝ) : ℝ := zeval nLY_r50 s / bval bases eLY_r50 s

/-- Numerator coefficients (constant term first) of `LY_r41`. -/
def nLY_r41 : List ℤ :=
  [0, 0, -56623104, 254803968, -1072693248, 3897556992, -12061507584, 24255004672, -72834351104,
   87412899840, -262525050880, 207427514368, -632892100608, 333037346816, -1102224996352,
   357387150336, -1417524240384, 254714063872, -1313361489664, 135974950144, -832202695552,
   90364477440, -329210476320, 85936313232, -61090333176, 67726485644, 7303954508, 36208775460,
   6901665382, 12973134347, 1616195313, 3135047606, 171050990, 509347596, 5429132, 54777297,
   -308189, 3786715, 5937, 159888, 4620, 3730, 278, 37, 5]
/-- Denominator exponents of `LY_r41` over `bases`. -/
def eLY_r41 : List ℕ := [3, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.r41` (or `Jet.r41`) of the jet at `ω = 1`. -/
def LY_r41 (s : ℝ) : ℝ := zeval nLY_r41 s / bval bases eLY_r41 s

/-- Numerator coefficients (constant term first) of `LY_r32`. -/
def nLY_r32 : List ℤ :=
  [0, 0, 56623104, 254803968, 1016070144, 3340763136, 7165181952, 10982916096, 32241090560,
   -18288672768, 109828857856, -219958628352, 275809972224, -695359197184, 473383641088,
   -1254089592832, 529475162112, -1497759534080, 368648400640, -1264592095616, 139922683264,
   -786082337280, 7566702720, -371196325200, -21034413672, -135971880972, -12724829276,
   -38539466988, -4498418170, -8125518933, -1195033341, -1169638838, -244816016, -94593848,
   -35950520, -690679, -3445357, 663955, -193989, 63860, -5298, 2518, -26, 37, 1]
/-- Denominator exponents of `LY_r32` over `bases`. -/
def eLY_r32 : List ℕ := [2, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.r32` (or `Jet.r32`) of the jet at `ω = 1`. -/
def LY_r32 (s : ℝ) : ℝ := zeval nLY_r32 s / bval bases eLY_r32 s

/-- Numerator coefficients (constant term first) of `LY_r23`. -/
def nLY_r23 : List ℤ :=
  [0, 0, -56623104, 254803968, -1016070144, 3340763136, -7618166784, 10982916096, -35349069824,
   -18288672768, -119431716864, -219958628352, -296539795456, -695359197184, -506597220352,
   -1254089592832, -550785781760, -1497759534080, -322097098496, -1264592095616, -1740105088,
   -786082337280, 165479628672, -371196325200, 151507211880, -135971880972, 77307323228,
   -38539466988, 26193664698, -8125518933, 6205151869, -1169638838, 1040755328, -94593848,
   122038088, -690679, 9627277, 663955, 474213, 63860, 12514, 2518, 106, 37, -1]
/-- Denominator exponents of `LY_r23` over `bases`. -/
def eLY_r23 : List ℕ := [2, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.r23` (or `Jet.r23`) of the jet at `ω = 1`. -/
def LY_r23 (s : ℝ) : ℝ := zeval nLY_r23 s / bval bases eLY_r23 s

/-- Numerator coefficients (constant term first) of `LY_r14`. -/
def nLY_r14 : List ℤ :=
  [0, 0, 56623104, 254803968, 1072693248, 4048551936, 11231035392, 25265831936, 67010560000,
   90621542400, 244146659328, 214897045504, 592766504960, 345907109888, 1037050263552, 368548144128,
   1372180103168, 246540061696, 1397049437952, 94214399232, 1099325401984, 20529598464,
   674931344160, 12921044880, 328789878264, 15681042316, 128456511284, 10486768740, 39773447802,
   4140107819, 9411340111, 1030991718, 1621329322, 163707300, 192910684, 16137513, 14874029, 924011,
   668639, 26352, 13100, 202, -78, -3, -5]
/-- Denominator exponents of `LY_r14` over `bases`. -/
def eLY_r14 : List ℕ := [3, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.r14` (or `Jet.r14`) of the jet at `ω = 1`. -/
def LY_r14 (s : ℝ) : ℝ := zeval nLY_r14 s / bval bases eLY_r14 s

/-- Numerator coefficients (constant term first) of `LY_r05`. -/
def nLY_r05 : List ℤ :=
  [0, 0, -56623104, 254803968, -506462208, 3161456640, -828112896, 17160863744, 3739484160,
   60248752128, 11133886464, 163447156736, -20541689856, 348613918720, -151973357568, 557730573312,
   -351129882624, 646874209280, -472790939904, 534775816448, -424304174208, 309039408384,
   -269832852192, 118516511760, -126632248536, 24752727436, -45366654852, -1079434572, -12751599642,
   -2661408497, -2846059179, -949533002, -497584782, -190979580, -65529084, -24293331, -6156477,
   -1969105, -387963, -97752, -15216, -2686, -330, -31, -3]
/-- Denominator exponents of `LY_r05` over `bases`. -/
def eLY_r05 : List ℕ := [3, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.r05` (or `Jet.r05`) of the jet at `ω = 1`. -/
def LY_r05 (s : ℝ) : ℝ := zeval nLY_r05 s / bval bases eLY_r05 s

/-- Numerator coefficients (constant term first) of `LY_e50`. -/
def nLY_e50 : List ℤ :=
  [0, 0, -849346560, 3822059520, -11334057984, 50347376640, -73282093056, 253983588352,
   -329983459328, 671074025472, -1176230928384, 1050025283584, -3249169002496, 1006586601472,
   -6548850731008, 517647666176, -9264754909184, -51902270464, -9010800382208, -372237000448,
   -5898001900672, -400920649728, -2484375731808, -278844267024, -590300140296, -142686247468,
   -31792082380, -54167018148, 23466857802, -14873940667, 6900719983, -2869676550, 695496026,
   -378169244, -19792924, -32777473, -11667275, -1736875, -1189041, -46912, -57812, -226, -1382, 11,
   -13]
/-- Denominator exponents of `LY_e50` over `bases`. -/
def eLY_e50 : List ℕ := [3, 2, 1, 0, 3, 2, 1]
/-- The value of `Jet5.e50` (or `Jet.e50`) of the jet at `ω = 1`. -/
def LY_e50 (s : ℝ) : ℝ := zeval nLY_e50 s / bval bases eLY_e50 s

/-- Numerator coefficients (constant term first) of `LY_e41`. -/
def nLY_e41 : List ℤ :=
  [0, 0, -56623104, -254803968, -506462208, -3010461696, -752615424, -16150036480, 4131651584,
   -57040109568, 11961212928, -155977625600, -19207639040, -335744155648, -150720931840,
   -546569579520, -353852780544, -655048211456, -482205595904, -576536367360, -433546624128,
   -378874287360, -270204647136, -191531780112, -119878299864, -76798170764, -38771176964,
   -24642572148, -9466979514, -6171618031, -1838760811, -1154522886, -297083094, -154660716,
   -39364404, -14346453, -3954477, -893599, -273835, -35784, -11928, -842, -290, -9, -3]
/-- Denominator exponents of `LY_e41` over `bases`. -/
def eLY_e41 : List ℕ := [3, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.e41` (or `Jet.e41`) of the jet at `ω = 1`. -/
def LY_e41 (s : ℝ) : ℝ := zeval nLY_e41 s / bval bases eLY_e41 s

/-- Numerator coefficients (constant term first) of `LY_e32`. -/
def nLY_e32 : List ℤ :=
  [0, 0, -169869312, 764411904, -2028994560, 9663676416, -9274392576, 45304643584, -27870101504,
   102208831488, -97163943936, 106935685120, -337623175168, 1868640256, -810543935488,
   -138628446208, -1253045547008, -204011115520, -1267678978304, -195040462720, -850348453504,
   -168003520512, -374186075712, -134163301680, -101757285192, -86466426100, -13425986476,
   -40698336132, 690465414, -13448335927, 513033511, -3068704842, 45585764, -476553008, -9020080,
   -49277341, -2685677, -3274255, -301713, -131644, -17918, -2854, -554, -25, -7]
/-- Denominator exponents of `LY_e32` over `bases`. -/
def eLY_e32 : List ℕ := [2, 2, 0, 0, 3, 2, 1]
/-- The value of `Jet5.e32` (or `Jet.e32`) of the jet at `ω = 1`. -/
def LY_e32 (s : ℝ) : ℝ := zeval nLY_e32 s / bval bases eLY_e32 s

/-- Numerator coefficients (constant term first) of `LY_e23`. -/
def nLY_e23 : List ℤ :=
  [0, 0, -169869312, -764411904, -2028994560, -9361686528, -8670412800, -43282989056, -23977787392,
   -95791546368, -85906432000, -91996622848, -314225250304, 23870885888, -774825504768,
   160950433792, -1237180723200, 187663111168, -1333059592448, 111519360896, -1007015931520,
   28333762560, -547975996992, -11867235024, -218722186056, -17624460556, -64817524652,
   -10745677308, -14435540858, -4217717129, -2482488281, -1139406934, -349350172, -214727584,
   -42778288, -28002227, -4463597, -2451153, -353681, -135428, -18558, -4202, -554, -55, -7]
/-- Denominator exponents of `LY_e23` over `bases`. -/
def eLY_e23 : List ℕ := [2, 2, 0, 0, 3, 2, 1]
/-- The value of `Jet5.e23` (or `Jet.e23`) of the jet at `ω = 1`. -/
def LY_e23 (s : ℝ) : ℝ := zeval nLY_e23 s / bval bases eLY_e23 s

/-- Numerator coefficients (constant term first) of `LY_e14`. -/
def nLY_e14 : List ℤ :=
  [0, 0, -56623104, 254803968, -506462208, 3161456640, -828112896, 17160863744, 3739484160,
   60248752128, 11133886464, 163447156736, -20541689856, 348613918720, -151973357568, 557730573312,
   -351129882624, 646874209280, -472790939904, 534775816448, -424304174208, 309039408384,
   -269832852192, 118516511760, -126632248536, 24752727436, -45366654852, -1079434572, -12751599642,
   -2661408497, -2846059179, -949533002, -497584782, -190979580, -65529084, -24293331, -6156477,
   -1969105, -387963, -97752, -15216, -2686, -330, -31, -3]
/-- Denominator exponents of `LY_e14` over `bases`. -/
def eLY_e14 : List ℕ := [3, 1, 0, 0, 3, 2, 1]
/-- The value of `Jet5.e14` (or `Jet.e14`) of the jet at `ω = 1`. -/
def LY_e14 (s : ℝ) : ℝ := zeval nLY_e14 s / bval bases eLY_e14 s

/-- Numerator coefficients (constant term first) of `LY_e05`. -/
def nLY_e05 : List ℤ :=
  [0, 0, -849346560, -3822059520, -11334057984, -49592401920, -68374757376, -248929452032,
   -296942829568, -655030812672, -1076065705984, -1012677627904, -3035200516096, -942237786112,
   -6210452809728, -461842697216, -9065263202304, 11032259584, -9523386683648, 163434245888,
   -7326039932032, 51746254848, -4216698020448, -86232074736, -1861258379016, -117540969172,
   -644639632460, -74443015452, -177062506838, -29291191973, -38163973457, -7650602890, -6261388654,
   -1350032236, -749845204, -160421447, -62476475, -12576645, -3420641, -620768, -113532, -17414,
   -1982, -211, -13]
/-- Denominator exponents of `LY_e05` over `bases`. -/
def eLY_e05 : List ℕ := [3, 2, 1, 0, 3, 2, 1]
/-- The value of `Jet5.e05` (or `Jet.e05`) of the jet at `ω = 1`. -/
def LY_e05 (s : ℝ) : ℝ := zeval nLY_e05 s / bval bases eLY_e05 s

/-- Numerator coefficients (constant term first) of `LY_r60`. -/
def nLY_r60 : List ℤ :=
  [0, 0, 0, 0, 204096845905920, -232546709274624, 4128477183737856, -5517263448834048,
   36810137469452288, -56138078711971840, 195885533082157056, -328466541387448320,
   716298877459759104, -1244721846755000320, 1967927814652952576, -3241648863240519680,
   4304131993416761344, -5955425805650624512, 7725015092495908864, -7676251759253127168,
   11488990923418763264, -6475149206414688256, 14178322252940181504, -2335831001281855488,
   14555622835896713216, 2475455925188362240, 12488691463492272128, 5501149640905129984,
   8948662011912011776, 5994480022276931584, 5264031969599676416, 4771480904677294080,
   2433242169715597312, 3027406688759316480, 805024674266236928, 1565214944348048896,
   140934770619938048, 657981961201371136, -21111774301905280, 222601865580804352,
   -23958205556762176, 59914674474034400, -8586467584519760, 12692236341914768, -1838656238055032,
   2093904935512928, -241416485258524, 265828398937856, -14115174434664, 25545061815020,
   1296798016686, 1806063840850, 400573764139, 88240906234, 47690928725, 2430108810, 3505925003,
   -10632726, 170701601, -4169658, 5463889, -179314, 108611, -3634, 1177, -30, 5]
/-- Denominator exponents of `LY_r60` over `bases`. -/
def eLY_r60 : List ℕ := [3, 2, 1, 0, 4, 3, 1, 1]
/-- The value of `Jet5.r60` (or `Jet.r60`) of the jet at `ω = 1`. -/
def LY_r60 (s : ℝ) : ℝ := zeval nLY_r60 s / bval bases eLY_r60 s

/-- Numerator coefficients (constant term first) of `LY_r42`. -/
def nLY_r42 : List ℤ :=
  [0, 0, 0, 0, 40819369181184, 232546709274624, 703979499552768, 4881470850072576, 3957898262609920,
   46258726218235904, 1261087223709696, 269971036731080704, -87959560395948032, 1121397446455328768,
   -478004868703846400, 3605615919595782144, -1256211381447819264, 9368179201472987136,
   -1619865741505331200, 19940794221585235968, 435066956871106560, 34732239934013308928,
   6559108954573766656, 49258835284536066048, 15513715919033466880, 56653604569599901696,
   22973721962768564224, 52701907318443802624, 24866003997268787200, 39588193758980538368,
   20786191612279595008, 23990815821253459968, 13782515788525051904, 11730353872984678400,
   7355415502430242816, 4637312119902169600, 3184677949255706880, 1490661839897743360,
   1122829804014677632, 394078826304386816, 322701662394111168, 87239360860058272,
   75583246004087472, 16517822794521392, 14423471720280520, 2711209168361312, 2243394625535172,
   383379500350512, 284599915719032, 45455312591732, 29420484021054, 4352798783298, 2463371350923,
   324078741594, 164558211205, 18080102394, 8535146315, 725819642, 329766801, 19872182, 8939249,
   340910, 155187, 3118, 1465, 10, 5]
/-- Denominator exponents of `LY_r42` over `bases`. -/
def eLY_r42 : List ℕ := [3, 2, 0, 0, 4, 3, 1, 1]
/-- The value of `Jet5.r42` (or `Jet.r42`) of the jet at `ω = 1`. -/
def LY_r42 (s : ℝ) : ℝ := zeval nLY_r42 s / bval bases eLY_r42 s

/-- Numerator coefficients (constant term first) of `LY_r24`. -/
def nLY_r24 : List ℤ :=
  [0, 0, 0, 0, -40819369181184, 232546709274624, -713875104202752, 4916105466347520,
   -4276481756758016, 46685405449289728, -4618377259646976, 272108641954299904, 69375271265894400,
   1127160399213363200, 411324741224235008, 3614249615609561088, 1081268245266169856,
   9369388671779733504, 1271590046712987648, 19903402635671109632, -924247848156921856,
   34608018621548462080, -6891722393789923328, 49049107666476990464, -15114236239329361920,
   56501033132903038976, -21333830758207913984, 52836030827352489984, -22015385382469648384,
   40097355878315589632, -17389218865159806976, 24696996042478862336, -10723262520896823296,
   12350068871279206400, -5201923106953545728, 5018009494151027200, -1985171609595570432,
   1659030364141703168, -592298616821227136, 447274786931305216, -136397801376220352,
   98558431506013600, -23719939353471152, 17759254609908528, -3005009295477960, 2602541297491872,
   -261620064563716, 304603404137984, -14717890296440, 27294414258148, -780224877102, 1695324709974,
   -119053718107, 50129401230, -18794623861, -2328983170, -1808268827, -368266210, -107554017,
   -21231246, -3993313, -683254, -89027, -12022, -1065, -90, -5]
/-- Denominator exponents of `LY_r24` over `bases`. -/
def eLY_r24 : List ℕ := [3, 2, 0, 0, 4, 3, 1, 1]
/-- The value of `Jet5.r24` (or `Jet.r24`) of the jet at `ω = 1`. -/
def LY_r24 (s : ℝ) : ℝ := zeval nLY_r24 s / bval bases eLY_r24 s

/-- Numerator coefficients (constant term first) of `LY_r06`. -/
def nLY_r06 : List ℤ :=
  [0, 0, 0, 0, -204096845905920, -232546709274624, -4177955206987776, -5393568390709248,
   -37512450521694208, -54385388457820160, -200234445167394816, -317485083105689600,
   -732361883348107264, -1202434715450081280, -2008328488947286016, -3124856268531957760,
   -4374559793394745344, -5710556486237683712, -7790410722227257344, -7305933945546211328,
   -11427986915866968064, -6166222982051004416, -13811502603022106624, -2502380028667363328,
   -13842642760872493056, 1410797316680253440, -11756492018737020928, 3464288234626023424,
   -8778783943023149056, 3392953442163687424, -5983597305167077376, 2255084245900165120,
   -3770309008819167232, 1103273466818969600, -2151245487532607488, 383769796738776576,
   -1072628338350748928, 73159169555941376, -453145750094638720, -10491822379848448,
   -158812430887694784, -14655573635760160, -45522168696831920, -6388168131091312,
   -10558582591178888, -1797170683503712, -1963338945470116, -364260373870384, -290029592645016,
   -55105688453540, -33702703412286, -6302157893530, -3044737561179, -545944235986, -210593844965,
   -35600376050, -10916248763, -1719866866, -410889041, -59695358, -10688609, -1405974, -176691,
   -20054, -1577, -130, -5]
/-- Denominator exponents of `LY_r06` over `bases`. -/
def eLY_r06 : List ℕ := [3, 2, 1, 0, 4, 3, 1, 1]
/-- The value of `Jet5.r06` (or `Jet.r06`) of the jet at `ω = 1`. -/
def LY_r06 (s : ℝ) : ℝ := zeval nLY_r06 s / bval bases eLY_r06 s

/-- Numerator coefficients (constant term first) of `LY_k6`. -/
def nLY_k6 : List ℤ :=
  [0, 0, 0, 0, 0, 0, -4831838208, -90596966400, -42010148864, -660535771136, -167671496704,
   -919043309568, -438850027520, 6872270635008, -849382211584, 39696605904896, -1065019244544,
   106705353244672, -211166822400, 184713399418880, 2235400028160, 227204668497920, 5056988397568,
   208028998359040, 6079926345728, 145409813188608, 4713896034304, 78662785265408, 2444738093056,
   33137274421504, 821837835776, 10876455256128, 149843207552, 2769578671760, -3236946112,
   541560548168, -10180090400, 79632911584, -3032288944, 8401831056, -503728192, 555684234,
   -53287880, 8942207, -3650432, -2435557, -156512, -282714, -3808, -15264, -40, -429, 0, -5]
/-- Denominator exponents of `LY_k6` over `bases`. -/
def eLY_k6 : List ℕ := [3, 1, 0, 0, 3, 3, 1]
/-- The value of `Jet5.k6` (or `Jet.k6`) of the jet at `ω = 1`. -/
def LY_k6 (s : ℝ) : ℝ := zeval nLY_k6 s / bval bases eLY_k6 s

/-- Numerator coefficients (constant term first) of `L1V`. -/
def nL1V : List ℤ :=
  [0, 0, 0, -1024, 0, -3072, 0, -3456, 0, -1568, 0, -116, 0, 90, 0, 20, 0, 1]
/-- Denominator exponents of `L1V` over `bases`. -/
def eL1V : List ℕ := [0, 0, 0, 0, 1, 1]
/-- The value of `Jet.l1` of the jet at `ω = 1`. -/
def L1V (s : ℝ) : ℝ := zeval nL1V s / bval bases eL1V s

/-- Numerator coefficients (constant term first) of `L2V`. -/
def nL2V : List ℤ :=
  [0, 0, 0, 0, 0, 0, -4831838208, -90596966400, -42010148864, -660535771136, -167671496704,
   -919043309568, -438850027520, 6872270635008, -849382211584, 39696605904896, -1065019244544,
   106705353244672, -211166822400, 184713399418880, 2235400028160, 227204668497920, 5056988397568,
   208028998359040, 6079926345728, 145409813188608, 4713896034304, 78662785265408, 2444738093056,
   33137274421504, 821837835776, 10876455256128, 149843207552, 2769578671760, -3236946112,
   541560548168, -10180090400, 79632911584, -3032288944, 8401831056, -503728192, 555684234,
   -53287880, 8942207, -3650432, -2435557, -156512, -282714, -3808, -15264, -40, -429, 0, -5]
/-- Denominator exponents of `L2V` over `bases`. -/
def eL2V : List ℕ := [2, 1, 0, 0, 3, 3, 1]
/-- The value of `Jet5.l2` of the jet at `ω = 1`. -/
def L2V (s : ℝ) : ℝ := zeval nL2V s / bval bases eL2V s

/-! ## The values of the truncation coefficients -/

/-- Numerator coefficients (constant term first) of `TV1_02`. -/
def nTV1_02 : List ℤ :=
  [0, -32, -16, -32, -8, -10, -1, -1]
/-- Denominator exponents of `TV1_02` over `bases`. -/
def eTV1_02 : List ℕ := []
/-- The value of `T1_02`. -/
def TV1_02 (s : ℝ) : ℝ := zeval nTV1_02 s / bval bases eTV1_02 s

/-- Numerator coefficients (constant term first) of `TV1_03`. -/
def nTV1_03 : List ℤ :=
  [0, 8192, 20480, 38912, 103424, 58880, 162048, 3712, 96192, -72704, 2784, -77504, -22656, -36880,
   -10848, -9282, -2210, -1243, -207, -81, -7, -2]
/-- Denominator exponents of `TV1_03` over `bases`. -/
def eTV1_03 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T1_03`. -/
def TV1_03 (s : ℝ) : ℝ := zeval nTV1_03 s / bval bases eTV1_03 s

/-- Numerator coefficients (constant term first) of `TV1_04`. -/
def nTV1_04 : List ℤ :=
  [0, 0, -226492416, -188743680, -2812280832, -2771386368, -14294188032, -14902362112, -39989280768,
   -41747480576, -71162626048, -72140374016, -92177965056, -87915655168, -101997023232,
   -86769330176, -105342269440, -76088125952, -94521149952, -57808785792, -65772092928,
   -34837437888, -33320607744, -15558766176, -11965637952, -4957197752, -2993464368, -1096080448,
   -509781248, -162404974, -56781756, -15117177, -3829854, -748191, -128304, -5034, -180, 1412, 108,
   67, 2, 1]
/-- Denominator exponents of `TV1_04` over `bases`. -/
def eTV1_04 : List ℕ := [2, 1, 0, 0, 2, 2, 1]
/-- The value of `T1_04`. -/
def TV1_04 (s : ℝ) : ℝ := zeval nTV1_04 s / bval bases eTV1_04 s

/-- Numerator coefficients (constant term first) of `TV1_05`. -/
def nTV1_05 : List ℤ :=
  [0, 0, 927712935936, 16234976378880, 31877247270912, 352492260950016, 480312635162624,
   3336793378258944, 4065861929271296, 18476974003453952, 21798534340673536, 67896924933455872,
   79874925149552640, 178087984854204416, 210368599909466112, 349123022201815040,
   410873023260786688, 524417441661452288, 603448098076753920, 603232369682415616,
   662094700683853824, 508490446654734336, 519155720407941120, 263020861254991872,
   243935875280011264, -8125098488971264, -10034559278686208, -174131763732180992,
   -136180719463559168, -198805611521048576, -139357725956329472, -139703329717280768,
   -88401806217899520, -70717549357064448, -40546316390069632, -27029388871801024,
   -14069346796768448, -7941189357080384, -3752598805953408, -1803506125732288, -772042159995848,
   -316092930466300, -122045253878220, -42416665759360, -14676373350666, -4289149195323,
   -1319557994777, -316997611268, -86166257030, -15998693770, -3868240984, -441408471, -104009631,
   3275255, -740465, 870150, 51796, 36852, 1790, 741, 19, 6]
/-- Denominator exponents of `TV1_05` over `bases`. -/
def eTV1_05 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T1_05`. -/
def TV1_05 (s : ℝ) : ℝ := zeval nTV1_05 s / bval bases eTV1_05 s

/-- Numerator coefficients (constant term first) of `TV1_11`. -/
def nTV1_11 : List ℤ :=
  [0, -64, 0, -64, 0, -20, 0, -2]
/-- Denominator exponents of `TV1_11` over `bases`. -/
def eTV1_11 : List ℕ := []
/-- The value of `T1_11`. -/
def TV1_11 (s : ℝ) : ℝ := zeval nTV1_11 s / bval bases eTV1_11 s

/-- Numerator coefficients (constant term first) of `TV1_12`. -/
def nTV1_12 : List ℤ :=
  [0, 8192, 12288, 30720, 56320, 30208, 59136, 1664, -2496, -43520, -40800, -61792, -30352, -38560,
   -10816, -12542, -2074, -2177, -199, -187, -7, -6]
/-- Denominator exponents of `TV1_12` over `bases`. -/
def eTV1_12 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T1_12`. -/
def TV1_12 (s : ℝ) : ℝ := zeval nTV1_12 s / bval bases eTV1_12 s

/-- Numerator coefficients (constant term first) of `TV1_13`. -/
def nTV1_13 : List ℤ :=
  [0, 0, 0, 37748736, 25165824, 108527616, 105381888, -857866240, -796262400, -6384189440,
   -6977159168, -20076412928, -22104588288, -38933530624, -39526643712, -51927104000, -46106828288,
   -50122635776, -37930033152, -36117310656, -23034680832, -19801595424, -10543670304, -8296230144,
   -3634246896, -2620618292, -926221200, -605641264, -169029340, -97837810, -21056706, -10289199,
   -1656783, -606363, -69936, -9294, -750, 1040, 42, 61, 1, 1]
/-- Denominator exponents of `TV1_13` over `bases`. -/
def eTV1_13 : List ℕ := [0, 1, 0, 0, 2, 2, 1]
/-- The value of `T1_13`. -/
def TV1_13 (s : ℝ) : ℝ := zeval nTV1_13 s / bval bases eTV1_13 s

/-- Numerator coefficients (constant term first) of `TV1_14`. -/
def nTV1_14 : List ℤ :=
  [0, 0, -927712935936, -6030134083584, -31258771980288, -129196911230976, -341121335033856,
   -1248530886819840, -1742215902658560, -6980869117968384, -4074590510776320, -24420034671542272,
   483603989397504, -54488679804043264, 30160814837071872, -74628731192213504, 87097570756657152,
   -50725557490417664, 114561084882419712, 7468731929198592, 20636523906072576, 26108492971048960,
   -210054445570129920, -54171373792067584, -458384826848182272, -193839006017896448,
   -572925740828418048, -289079196084809728, -510364169769725952, -280807800618049536,
   -347503871229050880, -198110566028478464, -186481653305654784, -106028104480135424,
   -79885321285232256, -43908598453982400, -27380820715579200, -14183728874959936,
   -7475121807682752, -3575977328417856, -1610700867648216, -699766722153148, -270428313202548,
   -105003449045872, -34782017702286, -11826124032823, -3348421377435, -961465960164, -233001820146,
   -51797833922, -11017870152, -1362150531, -305116941, 31423203, -2008995, 4437486, 163452, 181412,
   5418, 3641, 57, 30]
/-- Denominator exponents of `TV1_14` over `bases`. -/
def eTV1_14 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T1_14`. -/
def TV1_14 (s : ℝ) : ℝ := zeval nTV1_14 s / bval bases eTV1_14 s

/-- Numerator coefficients (constant term first) of `TV1_20`. -/
def nTV1_20 : List ℤ :=
  [0, -32, 16, -32, 8, -10, 1, -1]
/-- Denominator exponents of `TV1_20` over `bases`. -/
def eTV1_20 : List ℕ := []
/-- The value of `T1_20`. -/
def TV1_20 (s : ℝ) : ℝ := zeval nTV1_20 s / bval bases eTV1_20 s

/-- Numerator coefficients (constant term first) of `TV1_21`. -/
def nTV1_21 : List ℤ :=
  [0, 8192, -12288, 30720, -56320, 30208, -59136, 1664, 2496, -43520, 40800, -61792, 30352, -38560,
   10816, -12542, 2074, -2177, 199, -187, 7, -6]
/-- Denominator exponents of `TV1_21` over `bases`. -/
def eTV1_21 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T1_21`. -/
def TV1_21 (s : ℝ) : ℝ := zeval nTV1_21 s / bval bases eTV1_21 s

/-- Numerator coefficients (constant term first) of `TV1_22`. -/
def nTV1_22 : List ℤ :=
  [0, 0, 0, 113246208, 0, 1039138816, 0, 4113039360, 0, 9328132096, 0, 13501546496, 0, 11903086592,
   0, 2901426176, 0, -8098530816, 0, -13160047744, 0, -10753019584, 0, -5661948640, 0, -2037712904,
   0, -506963200, 0, -85796126, 0, -9400513, 0, -586095, 0, -11098, 0, 916, 0, 59, 0, 1]
/-- Denominator exponents of `TV1_22` over `bases`. -/
def eTV1_22 : List ℕ := [1, 0, 0, 0, 2, 2, 1]
/-- The value of `T1_22`. -/
def TV1_22 (s : ℝ) : ℝ := zeval nTV1_22 s / bval bases eTV1_22 s

/-- Numerator coefficients (constant term first) of `TV1_23`. -/
def nTV1_23 : List ℤ :=
  [0, 0, 927712935936, 5102421147648, 10539849744384, 112059991719936, 7282117050368,
   997874447941632, -542410346070016, 4805141765029888, -4593331560513536, 13801115787198464,
   -20354446412218368, 23400700218179584, -58714366735810560, 16455906447327232,
   -118201275719352320, -26670992797466624, -171449973951430656, -107815503552053248,
   -184483140148002816, -204411056471605248, -157205283665805312, -281317090410233856,
   -123545387345936384, -308056448099483648, -105717467605409792, -275090412563206144,
   -93629750403534848, -201003440738240512, -72268644868763648, -119901829926464512,
   -44271743638517760, -58204199145351936, -21000227101524352, -22905827640180416,
   -7704219932944064, -7268502668784832, -2192023737219744, -1844350812820736, -483871754295752,
   -369594628385252, -82500373082580, -57416040076232, -10746539596578, -6717686694879,
   -1048307904929, -562389572620, -73985707190, -29881975946, -3543067192, -560010507, -98491671,
   49251787, -588665, 4626390, 56212, 180948, 1814, 3609, 19, 30]
/-- Denominator exponents of `TV1_23` over `bases`. -/
def eTV1_23 : List ℕ := [2, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T1_23`. -/
def TV1_23 (s : ℝ) : ℝ := zeval nTV1_23 s / bval bases eTV1_23 s

/-- Numerator coefficients (constant term first) of `TV1_30`. -/
def nTV1_30 : List ℤ :=
  [0, 8192, -20480, 38912, -103424, 58880, -162048, 3712, -96192, -72704, -2784, -77504, 22656,
   -36880, 10848, -9282, 2210, -1243, 207, -81, 7, -2]
/-- Denominator exponents of `TV1_30` over `bases`. -/
def eTV1_30 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T1_30`. -/
def TV1_30 (s : ℝ) : ℝ := zeval nTV1_30 s / bval bases eTV1_30 s

/-- Numerator coefficients (constant term first) of `TV1_31`. -/
def nTV1_31 : List ℤ :=
  [0, 0, 0, 37748736, -25165824, 108527616, -105381888, -857866240, 796262400, -6384189440,
   6977159168, -20076412928, 22104588288, -38933530624, 39526643712, -51927104000, 46106828288,
   -50122635776, 37930033152, -36117310656, 23034680832, -19801595424, 10543670304, -8296230144,
   3634246896, -2620618292, 926221200, -605641264, 169029340, -97837810, 21056706, -10289199,
   1656783, -606363, 69936, -9294, 750, 1040, -42, 61, -1, 1]
/-- Denominator exponents of `TV1_31` over `bases`. -/
def eTV1_31 : List ℕ := [0, 1, 0, 0, 2, 2, 1]
/-- The value of `T1_31`. -/
def TV1_31 (s : ℝ) : ℝ := zeval nTV1_31 s / bval bases eTV1_31 s

/-- Numerator coefficients (constant term first) of `TV1_32`. -/
def nTV1_32 : List ℤ :=
  [0, 0, -927712935936, 5102421147648, -10539849744384, 112059991719936, -7282117050368,
   997874447941632, 542410346070016, 4805141765029888, 4593331560513536, 13801115787198464,
   20354446412218368, 23400700218179584, 58714366735810560, 16455906447327232, 118201275719352320,
   -26670992797466624, 171449973951430656, -107815503552053248, 184483140148002816,
   -204411056471605248, 157205283665805312, -281317090410233856, 123545387345936384,
   -308056448099483648, 105717467605409792, -275090412563206144, 93629750403534848,
   -201003440738240512, 72268644868763648, -119901829926464512, 44271743638517760,
   -58204199145351936, 21000227101524352, -22905827640180416, 7704219932944064, -7268502668784832,
   2192023737219744, -1844350812820736, 483871754295752, -369594628385252, 82500373082580,
   -57416040076232, 10746539596578, -6717686694879, 1048307904929, -562389572620, 73985707190,
   -29881975946, 3543067192, -560010507, 98491671, 49251787, 588665, 4626390, -56212, 180948, -1814,
   3609, -19, 30]
/-- Denominator exponents of `TV1_32` over `bases`. -/
def eTV1_32 : List ℕ := [2, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T1_32`. -/
def TV1_32 (s : ℝ) : ℝ := zeval nTV1_32 s / bval bases eTV1_32 s

/-- Numerator coefficients (constant term first) of `TV1_40`. -/
def nTV1_40 : List ℤ :=
  [0, 0, 226492416, -188743680, 2812280832, -2771386368, 14294188032, -14902362112, 39989280768,
   -41747480576, 71162626048, -72140374016, 92177965056, -87915655168, 101997023232, -86769330176,
   105342269440, -76088125952, 94521149952, -57808785792, 65772092928, -34837437888, 33320607744,
   -15558766176, 11965637952, -4957197752, 2993464368, -1096080448, 509781248, -162404974, 56781756,
   -15117177, 3829854, -748191, 128304, -5034, 180, 1412, -108, 67, -2, 1]
/-- Denominator exponents of `TV1_40` over `bases`. -/
def eTV1_40 : List ℕ := [2, 1, 0, 0, 2, 2, 1]
/-- The value of `T1_40`. -/
def TV1_40 (s : ℝ) : ℝ := zeval nTV1_40 s / bval bases eTV1_40 s

/-- Numerator coefficients (constant term first) of `TV1_41`. -/
def nTV1_41 : List ℤ :=
  [0, 0, 927712935936, -6030134083584, 31258771980288, -129196911230976, 341121335033856,
   -1248530886819840, 1742215902658560, -6980869117968384, 4074590510776320, -24420034671542272,
   -483603989397504, -54488679804043264, -30160814837071872, -74628731192213504, -87097570756657152,
   -50725557490417664, -114561084882419712, 7468731929198592, -20636523906072576, 26108492971048960,
   210054445570129920, -54171373792067584, 458384826848182272, -193839006017896448,
   572925740828418048, -289079196084809728, 510364169769725952, -280807800618049536,
   347503871229050880, -198110566028478464, 186481653305654784, -106028104480135424,
   79885321285232256, -43908598453982400, 27380820715579200, -14183728874959936, 7475121807682752,
   -3575977328417856, 1610700867648216, -699766722153148, 270428313202548, -105003449045872,
   34782017702286, -11826124032823, 3348421377435, -961465960164, 233001820146, -51797833922,
   11017870152, -1362150531, 305116941, 31423203, 2008995, 4437486, -163452, 181412, -5418, 3641,
   -57, 30]
/-- Denominator exponents of `TV1_41` over `bases`. -/
def eTV1_41 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T1_41`. -/
def TV1_41 (s : ℝ) : ℝ := zeval nTV1_41 s / bval bases eTV1_41 s

/-- Numerator coefficients (constant term first) of `TV1_50`. -/
def nTV1_50 : List ℤ :=
  [0, 0, -927712935936, 16234976378880, -31877247270912, 352492260950016, -480312635162624,
   3336793378258944, -4065861929271296, 18476974003453952, -21798534340673536, 67896924933455872,
   -79874925149552640, 178087984854204416, -210368599909466112, 349123022201815040,
   -410873023260786688, 524417441661452288, -603448098076753920, 603232369682415616,
   -662094700683853824, 508490446654734336, -519155720407941120, 263020861254991872,
   -243935875280011264, -8125098488971264, 10034559278686208, -174131763732180992,
   136180719463559168, -198805611521048576, 139357725956329472, -139703329717280768,
   88401806217899520, -70717549357064448, 40546316390069632, -27029388871801024, 14069346796768448,
   -7941189357080384, 3752598805953408, -1803506125732288, 772042159995848, -316092930466300,
   122045253878220, -42416665759360, 14676373350666, -4289149195323, 1319557994777, -316997611268,
   86166257030, -15998693770, 3868240984, -441408471, 104009631, 3275255, 740465, 870150, -51796,
   36852, -1790, 741, -19, 6]
/-- Denominator exponents of `TV1_50` over `bases`. -/
def eTV1_50 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T1_50`. -/
def TV1_50 (s : ℝ) : ℝ := zeval nTV1_50 s / bval bases eTV1_50 s

/-- Numerator coefficients (constant term first) of `TV2_02`. -/
def nTV2_02 : List ℤ :=
  [0, 0, -16, 0, -8, 0, -1]
/-- Denominator exponents of `TV2_02` over `bases`. -/
def eTV2_02 : List ℕ := [1]
/-- The value of `T2_02`. -/
def TV2_02 (s : ℝ) : ℝ := zeval nTV2_02 s / bval bases eTV2_02 s

/-- Numerator coefficients (constant term first) of `TV2_03`. -/
def nTV2_03 : List ℤ :=
  [0, 0, 4096, 4096, 21504, 18432, 40192, 23552, 32704, 10752, 9504, 80, -1856, -1416, -1732, -442,
   -378, -52, -33, -2, -1]
/-- Denominator exponents of `TV2_03` over `bases`. -/
def eTV2_03 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T2_03`. -/
def TV2_03 (s : ℝ) : ℝ := zeval nTV2_03 s / bval bases eTV2_03 s

/-- Numerator coefficients (constant term first) of `TV2_04`. -/
def nTV2_04 : List ℤ :=
  [0, 0, -28311552, -169869312, -371195904, -2112356352, -2359689216, -10555490304, -8465743872,
   -28086239232, -18208206848, -44204826624, -25366081536, -43095877632, -25572406272, -27353428992,
   -21527072768, -14027467008, -16486018560, -9164160768, -10888547904, -6775698048, -5594872080,
   -3712793136, -2085883692, -1329300456, -539953788, -306750564, -92947255, -45311700, -9942753,
   -4191288, -562041, -231600, -5226, -6900, 1203, -84, 63, 0, 1]
/-- Denominator exponents of `TV2_04` over `bases`. -/
def eTV2_04 : List ℕ := [3, 1, 0, 0, 2, 2, 1]
/-- The value of `T2_04`. -/
def TV2_04 (s : ℝ) : ℝ := zeval nTV2_04 s / bval bases eTV2_04 s

/-- Numerator coefficients (constant term first) of `TV2_05`. -/
def nTV2_05 : List ℤ :=
  [0, 0, 0, 927712935936, 4793183502336, 20847771254784, 107704894881792, 215510721495040,
   1040759696392192, 1343537710891008, 5815463565066240, 5630733397786624, 21357250543091712,
   16937944346525696, 55644662567796736, 38357160521891840, 108591077375606784, 67620480357498880,
   165442242127855616, 94435996361293824, 202543621212209152, 104577992027930624,
   201778692126212096, 90565154392965120, 162576874200006656, 59455879433191424, 103442041768624128,
   27558195884523520, 49759870100365312, 6975106105065472, 16570670223218688, -1121008529636352,
   2788725663651840, -2146666761206272, -508397524578304, -1187584767032704, -520622141085632,
   -417277771547200, -186999212438208, -103695240832704, -42114644779904, -18697085421800,
   -6456322535244, -2436870263328, -667988878272, -223456625504, -41897190263, -13448147432,
   -736326556, -420049648, 132022426, 4410264, 14521631, 1055808, 763173, 46120, 23466, 952, 404, 8,
   3]
/-- Denominator exponents of `TV2_05` over `bases`. -/
def eTV2_05 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T2_05`. -/
def TV2_05 (s : ℝ) : ℝ := zeval nTV2_05 s / bval bases eTV2_05 s

/-- Numerator coefficients (constant term first) of `TV2_11`. -/
def nTV2_11 : List ℤ :=
  [0, 0, -16, 0, -8, 0, -1]
/-- Denominator exponents of `TV2_11` over `bases`. -/
def eTV2_11 : List ℕ := []
/-- The value of `T2_11`. -/
def TV2_11 (s : ℝ) : ℝ := zeval nTV2_11 s / bval bases eTV2_11 s

/-- Numerator coefficients (constant term first) of `TV2_12`. -/
def nTV2_12 : List ℤ :=
  [0, 0, 4096, 4096, 17408, 18432, 17664, 23552, -576, 10752, -15072, 80, -13264, -1416, -5164,
   -442, -998, -52, -91, -2, -3]
/-- Denominator exponents of `TV2_12` over `bases`. -/
def eTV2_12 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T2_12`. -/
def TV2_12 (s : ℝ) : ℝ := zeval nTV2_12 s / bval bases eTV2_12 s

/-- Numerator coefficients (constant term first) of `TV2_13`. -/
def nTV2_13 : List ℤ :=
  [0, 0, 0, 0, 80216064, 58195968, 752222208, 648019968, 3136684032, 2846392320, 7732903936,
   6398607360, 12581578752, 8100452352, 14096309760, 5610055680, 10872901888, 1062915456,
   5499280896, -1885019904, 1482588960, -2197641264, -108619104, -1261947240, -276808728,
   -455956860, -117473052, -108507762, -26107951, -16968426, -3139257, -1692876, -147933, -101472,
   8094, -3258, 1371, -42, 63, 0, 1]
/-- Denominator exponents of `TV2_13` over `bases`. -/
def eTV2_13 : List ℕ := [1, 1, 0, 0, 2, 2, 1]
/-- The value of `T2_13`. -/
def TV2_13 (s : ℝ) : ℝ := zeval nTV2_13 s / bval bases eTV2_13 s

/-- Numerator coefficients (constant term first) of `TV2_14`. -/
def nTV2_14 : List ℤ :=
  [0, 0, 0, -927712935936, -3246995275776, -28166395527168, -59644210839552, -333699631546368,
   -499342561509376, -2167881521430528, -2529271344005120, -8850530793160704, -8639423017123840,
   -24308300560465920, -21109310570364928, -46541060381343744, -38672481698971648,
   -63080805345263616, -55865188093526016, -60637607815544832, -67196967884685312,
   -41657987748986880, -70494551634542592, -23065263443607552, -66062354268258304,
   -16382228657111040, -55321749825306624, -17599705251594240, -40793962862108672,
   -17480057199796224, -25879113555859456, -13085871604755456, -13743195136897024,
   -7305529578020352, -5949775810848256, -3086407515744384, -2052283013767360, -994774764042816,
   -552697961926336, -244387985781888, -113738053448224, -45357733427448, -17360881668620,
   -6249751457760, -1861539479840, -620142183696, -121442234771, -41779247400, -1640979836,
   -1637947152, 547001202, -11558232, 61130651, 2353680, 3384409, 124872, 109250, 2760, 1956, 24,
   15]
/-- Denominator exponents of `TV2_14` over `bases`. -/
def eTV2_14 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T2_14`. -/
def TV2_14 (s : ℝ) : ℝ := zeval nTV2_14 s / bval bases eTV2_14 s

/-- Numerator coefficients (constant term first) of `TV2_20`. -/
def nTV2_20 : List ℤ :=
  [0, 0, -16, 0, -8, 0, -1]
/-- Denominator exponents of `TV2_20` over `bases`. -/
def eTV2_20 : List ℕ := [1]
/-- The value of `T2_20`. -/
def TV2_20 (s : ℝ) : ℝ := zeval nTV2_20 s / bval bases eTV2_20 s

/-- Numerator coefficients (constant term first) of `TV2_21`. -/
def nTV2_21 : List ℤ :=
  [0, 0, 4096, -4096, 17408, -18432, 17664, -23552, -576, -10752, -15072, -80, -13264, 1416, -5164,
   442, -998, 52, -91, 2, -3]
/-- Denominator exponents of `TV2_21` over `bases`. -/
def eTV2_21 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T2_21`. -/
def TV2_21 (s : ℝ) : ℝ := zeval nTV2_21 s / bval bases eTV2_21 s

/-- Numerator coefficients (constant term first) of `TV2_22`. -/
def nTV2_22 : List ℤ :=
  [0, 0, -9437184, 0, -23068672, 0, 286654464, 0, 1881210880, 0, 5341933568, 0, 9649385472, 0,
   12815756288, 0, 12906793984, 0, 9554338176, 0, 4957052736, 0, 1698160432, 0, 342613444, 0,
   26014052, 0, -3797847, 0, -892353, 0, -11433, 0, 12502, 0, 1427, 0, 63, 0, 1]
/-- Denominator exponents of `TV2_22` over `bases`. -/
def eTV2_22 : List ℕ := [2, 0, 0, 0, 2, 2, 1]
/-- The value of `T2_22`. -/
def TV2_22 (s : ℝ) : ℝ := zeval nTV2_22 s / bval bases eTV2_22 s

/-- Numerator coefficients (constant term first) of `TV2_23`. -/
def nTV2_23 : List ℤ :=
  [0, 0, 0, 927712935936, 773094113280, 18322330484736, 29287381991424, 161252399644672,
   362844205875200, 841010431131648, 2328957290545152, 2892540348989440, 9185283564109824,
   6801327405400064, 24235428823433216, 10695441335189504, 44812144377593856, 9768885280571392,
   59180699581677568, 865666395537408, 54731827988922368, -11849396161478656, 30887806530420736,
   -19825959931084800, 960595978584064, -19296855545970688, -19530122987864064, -13744937071075328,
   -24654971986272256, -8066707366019072, -19070806089357312, -4225257368094720, -10764257409168384,
   -1999185946542592, -4654000458425600, -813421720971904, -1565433218947648, -268350278768128,
   -409797328687680, -68924256167904, -82526741233840, -13430340365960, -12441068570772,
   -1941824485920, -1322754465072, -202312060184, -83492100115, -14411566112, -302599796,
   -617766928, 528262442, -8153784, 56861371, 647592, 3194697, 39376, 105402, 904, 1924, 8, 15]
/-- Denominator exponents of `TV2_23` over `bases`. -/
def eTV2_23 : List ℕ := [2, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T2_23`. -/
def TV2_23 (s : ℝ) : ℝ := zeval nTV2_23 s / bval bases eTV2_23 s

/-- Numerator coefficients (constant term first) of `TV2_30`. -/
def nTV2_30 : List ℤ :=
  [0, 0, 4096, -4096, 21504, -18432, 40192, -23552, 32704, -10752, 9504, -80, -1856, 1416, -1732,
   442, -378, 52, -33, 2, -1]
/-- Denominator exponents of `TV2_30` over `bases`. -/
def eTV2_30 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T2_30`. -/
def TV2_30 (s : ℝ) : ℝ := zeval nTV2_30 s / bval bases eTV2_30 s

/-- Numerator coefficients (constant term first) of `TV2_31`. -/
def nTV2_31 : List ℤ :=
  [0, 0, 0, 0, 80216064, -58195968, 752222208, -648019968, 3136684032, -2846392320, 7732903936,
   -6398607360, 12581578752, -8100452352, 14096309760, -5610055680, 10872901888, -1062915456,
   5499280896, 1885019904, 1482588960, 2197641264, -108619104, 1261947240, -276808728, 455956860,
   -117473052, 108507762, -26107951, 16968426, -3139257, 1692876, -147933, 101472, 8094, 3258, 1371,
   42, 63, 0, 1]
/-- Denominator exponents of `TV2_31` over `bases`. -/
def eTV2_31 : List ℕ := [1, 1, 0, 0, 2, 2, 1]
/-- The value of `T2_31`. -/
def TV2_31 (s : ℝ) : ℝ := zeval nTV2_31 s / bval bases eTV2_31 s

/-- Numerator coefficients (constant term first) of `TV2_32`. -/
def nTV2_32 : List ℤ :=
  [0, 0, 0, -927712935936, 773094113280, -18322330484736, 29287381991424, -161252399644672,
   362844205875200, -841010431131648, 2328957290545152, -2892540348989440, 9185283564109824,
   -6801327405400064, 24235428823433216, -10695441335189504, 44812144377593856, -9768885280571392,
   59180699581677568, -865666395537408, 54731827988922368, 11849396161478656, 30887806530420736,
   19825959931084800, 960595978584064, 19296855545970688, -19530122987864064, 13744937071075328,
   -24654971986272256, 8066707366019072, -19070806089357312, 4225257368094720, -10764257409168384,
   1999185946542592, -4654000458425600, 813421720971904, -1565433218947648, 268350278768128,
   -409797328687680, 68924256167904, -82526741233840, 13430340365960, -12441068570772,
   1941824485920, -1322754465072, 202312060184, -83492100115, 14411566112, -302599796, 617766928,
   528262442, 8153784, 56861371, -647592, 3194697, -39376, 105402, -904, 1924, -8, 15]
/-- Denominator exponents of `TV2_32` over `bases`. -/
def eTV2_32 : List ℕ := [2, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T2_32`. -/
def TV2_32 (s : ℝ) : ℝ := zeval nTV2_32 s / bval bases eTV2_32 s

/-- Numerator coefficients (constant term first) of `TV2_40`. -/
def nTV2_40 : List ℤ :=
  [0, 0, -28311552, 169869312, -371195904, 2112356352, -2359689216, 10555490304, -8465743872,
   28086239232, -18208206848, 44204826624, -25366081536, 43095877632, -25572406272, 27353428992,
   -21527072768, 14027467008, -16486018560, 9164160768, -10888547904, 6775698048, -5594872080,
   3712793136, -2085883692, 1329300456, -539953788, 306750564, -92947255, 45311700, -9942753,
   4191288, -562041, 231600, -5226, 6900, 1203, 84, 63, 0, 1]
/-- Denominator exponents of `TV2_40` over `bases`. -/
def eTV2_40 : List ℕ := [3, 1, 0, 0, 2, 2, 1]
/-- The value of `T2_40`. -/
def TV2_40 (s : ℝ) : ℝ := zeval nTV2_40 s / bval bases eTV2_40 s

/-- Numerator coefficients (constant term first) of `TV2_41`. -/
def nTV2_41 : List ℤ :=
  [0, 0, 0, 927712935936, -3246995275776, 28166395527168, -59644210839552, 333699631546368,
   -499342561509376, 2167881521430528, -2529271344005120, 8850530793160704, -8639423017123840,
   24308300560465920, -21109310570364928, 46541060381343744, -38672481698971648, 63080805345263616,
   -55865188093526016, 60637607815544832, -67196967884685312, 41657987748986880, -70494551634542592,
   23065263443607552, -66062354268258304, 16382228657111040, -55321749825306624, 17599705251594240,
   -40793962862108672, 17480057199796224, -25879113555859456, 13085871604755456, -13743195136897024,
   7305529578020352, -5949775810848256, 3086407515744384, -2052283013767360, 994774764042816,
   -552697961926336, 244387985781888, -113738053448224, 45357733427448, -17360881668620,
   6249751457760, -1861539479840, 620142183696, -121442234771, 41779247400, -1640979836, 1637947152,
   547001202, 11558232, 61130651, -2353680, 3384409, -124872, 109250, -2760, 1956, -24, 15]
/-- Denominator exponents of `TV2_41` over `bases`. -/
def eTV2_41 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T2_41`. -/
def TV2_41 (s : ℝ) : ℝ := zeval nTV2_41 s / bval bases eTV2_41 s

/-- Numerator coefficients (constant term first) of `TV2_50`. -/
def nTV2_50 : List ℤ :=
  [0, 0, 0, -927712935936, 4793183502336, -20847771254784, 107704894881792, -215510721495040,
   1040759696392192, -1343537710891008, 5815463565066240, -5630733397786624, 21357250543091712,
   -16937944346525696, 55644662567796736, -38357160521891840, 108591077375606784,
   -67620480357498880, 165442242127855616, -94435996361293824, 202543621212209152,
   -104577992027930624, 201778692126212096, -90565154392965120, 162576874200006656,
   -59455879433191424, 103442041768624128, -27558195884523520, 49759870100365312, -6975106105065472,
   16570670223218688, 1121008529636352, 2788725663651840, 2146666761206272, -508397524578304,
   1187584767032704, -520622141085632, 417277771547200, -186999212438208, 103695240832704,
   -42114644779904, 18697085421800, -6456322535244, 2436870263328, -667988878272, 223456625504,
   -41897190263, 13448147432, -736326556, 420049648, 132022426, -4410264, 14521631, -1055808,
   763173, -46120, 23466, -952, 404, -8, 3]
/-- Denominator exponents of `TV2_50` over `bases`. -/
def eTV2_50 : List ℕ := [3, 1, 0, 0, 3, 3, 1, 1]
/-- The value of `T2_50`. -/
def TV2_50 (s : ℝ) : ℝ := zeval nTV2_50 s / bval bases eTV2_50 s

/-- Numerator coefficients (constant term first) of `TV3_03`. -/
def nTV3_03 : List ℤ :=
  [0, 0, 0, -64, 0, -48, 0, -12, 0, -1]
/-- Denominator exponents of `TV3_03` over `bases`. -/
def eTV3_03 : List ℕ := [1, 1]
/-- The value of `T3_03`. -/
def TV3_03 (s : ℝ) : ℝ := zeval nTV3_03 s / bval bases eTV3_03 s

/-- Numerator coefficients (constant term first) of `TV3_04`. -/
def nTV3_04 : List ℤ :=
  [0, 0, 0, 16384, 16384, 90112, 77824, 182272, 112640, 171008, 66560, 70720, 11072, 2080, -5584,
   -8784, -3184, -3244, -650, -510, -60, -37, -2, -1]
/-- Denominator exponents of `TV3_04` over `bases`. -/
def eTV3_04 : List ℕ := [2, 0, 0, 0, 1, 1]
/-- The value of `T3_04`. -/
def TV3_04 (s : ℝ) : ℝ := zeval nTV3_04 s / bval bases eTV3_04 s

/-- Numerator coefficients (constant term first) of `TV3_05`. -/
def nTV3_05 : List ℤ :=
  [0, 0, 0, -566231040, -2264924160, -7716470784, -28311552000, -48370286592, -144892231680,
   -173151485952, -401693736960, -384295288832, -670124605440, -564954705920, -703588270080,
   -593374593024, -477302538240, -490660779008, -230129172480, -351861890048, -115553529600,
   -225130789632, -80427649920, -121493706432, -51036766080, -51326358528, -22502576880,
   -16115553228, -6613737240, -3638061772, -1295873400, -574194895, -168029640, -61244589,
   -14063880, -4190409, -721680, -166482, -20400, -2853, -240, 19, 0, 1]
/-- Denominator exponents of `TV3_05` over `bases`. -/
def eTV3_05 : List ℕ := [3, 1, 1, 0, 2, 2, 1]
/-- The value of `T3_05`. -/
def TV3_05 (s : ℝ) : ℝ := zeval nTV3_05 s / bval bases eTV3_05 s

/-- Numerator coefficients (constant term first) of `TV3_12`. -/
def nTV3_12 : List ℤ :=
  [0, 0, 0, -64, 0, -48, 0, -12, 0, -1]
/-- Denominator exponents of `TV3_12` over `bases`. -/
def eTV3_12 : List ℕ := [1]
/-- The value of `T3_12`. -/
def TV3_12 (s : ℝ) : ℝ := zeval nTV3_12 s / bval bases eTV3_12 s

/-- Numerator coefficients (constant term first) of `TV3_13`. -/
def nTV3_13 : List ℤ :=
  [0, 0, 0, 8192, 8192, 40960, 38912, 67584, 56320, 46592, 33280, 2464, 5536, -16512, -2792, -10676,
   -1592, -3100, -325, -468, -30, -35, -1, -1]
/-- Denominator exponents of `TV3_13` over `bases`. -/
def eTV3_13 : List ℕ := [0, 0, 0, 0, 1, 1]
/-- The value of `T3_13`. -/
def TV3_13 (s : ℝ) : ℝ := zeval nTV3_13 s / bval bases eTV3_13 s

/-- Numerator coefficients (constant term first) of `TV3_14`. -/
def nTV3_14 : List ℤ :=
  [0, 0, 0, -113246208, -452984832, -833617920, -5083496448, -2763522048, -22296920064, -5229379584,
   -49461854208, -5527420928, -59328823296, -5848592384, -35519889408, -20695302144, -7322124288,
   -56200629248, -9000265728, -87469826048, -29077411584, -86508912384, -36101796480, -58255139904,
   -25003830336, -27647847552, -11002005936, -9356268828, -3229581960, -2249155804, -641562264,
   -377945407, -85589304, -43090845, -7452024, -3165129, -399888, -135186, -11808, -2469, -144, 19,
   0, 1]
/-- Denominator exponents of `TV3_14` over `bases`. -/
def eTV3_14 : List ℕ := [3, 1, 0, 0, 2, 2, 1]
/-- The value of `T3_14`. -/
def TV3_14 (s : ℝ) : ℝ := zeval nTV3_14 s / bval bases eTV3_14 s

/-- Numerator coefficients (constant term first) of `TV3_21`. -/
def nTV3_21 : List ℤ :=
  [0, 0, 0, -64, 0, -48, 0, -12, 0, -1]
/-- Denominator exponents of `TV3_21` over `bases`. -/
def eTV3_21 : List ℕ := [1]
/-- The value of `T3_21`. -/
def TV3_21 (s : ℝ) : ℝ := zeval nTV3_21 s / bval bases eTV3_21 s

/-- Numerator coefficients (constant term first) of `TV3_22`. -/
def nTV3_22 : List ℤ :=
  [0, 0, 0, 16384, 0, 73728, 0, 88064, 0, 15360, 0, -60864, 0, -68128, 0, -33920, 0, -9156, 0,
   -1362, 0, -103, 0, -3]
/-- Denominator exponents of `TV3_22` over `bases`. -/
def eTV3_22 : List ℕ := [1, 0, 0, 0, 1, 1]
/-- The value of `T3_22`. -/
def TV3_22 (s : ℝ) : ℝ := zeval nTV3_22 s / bval bases eTV3_22 s

/-- Numerator coefficients (constant term first) of `TV3_23`. -/
def nTV3_23 : List ℤ :=
  [0, 0, 0, -113246208, 0, -493879296, 289406976, 1244135424, 3340763136, 12747669504, 15438446592,
   36031578112, 37348048896, 53613481984, 52598882304, 44858597376, 44069191680, 12325875712,
   18512784384, -20852602880, -2983352832, -34809083520, -10008133248, -28847259648, -7398238560,
   -15677740224, -3250745280, -5895512772, -953417256, -1546358212, -191193792, -279980791,
   -25991688, -34095189, -2319624, -2657481, -127776, -119634, -3864, -2277, -48, 19, 0, 1]
/-- Denominator exponents of `TV3_23` over `bases`. -/
def eTV3_23 : List ℕ := [2, 1, 0, 0, 2, 2, 1]
/-- The value of `T3_23`. -/
def TV3_23 (s : ℝ) : ℝ := zeval nTV3_23 s / bval bases eTV3_23 s

/-- Numerator coefficients (constant term first) of `TV3_30`. -/
def nTV3_30 : List ℤ :=
  [0, 0, 0, -64, 0, -48, 0, -12, 0, -1]
/-- Denominator exponents of `TV3_30` over `bases`. -/
def eTV3_30 : List ℕ := [1, 1]
/-- The value of `T3_30`. -/
def TV3_30 (s : ℝ) : ℝ := zeval nTV3_30 s / bval bases eTV3_30 s

/-- Numerator coefficients (constant term first) of `TV3_31`. -/
def nTV3_31 : List ℤ :=
  [0, 0, 0, 8192, -8192, 40960, -38912, 67584, -56320, 46592, -33280, 2464, -5536, -16512, 2792,
   -10676, 1592, -3100, 325, -468, 30, -35, 1, -1]
/-- Denominator exponents of `TV3_31` over `bases`. -/
def eTV3_31 : List ℕ := [0, 0, 0, 0, 1, 1]
/-- The value of `T3_31`. -/
def TV3_31 (s : ℝ) : ℝ := zeval nTV3_31 s / bval bases eTV3_31 s

/-- Numerator coefficients (constant term first) of `TV3_32`. -/
def nTV3_32 : List ℤ :=
  [0, 0, 0, -113246208, 0, -493879296, -289406976, 1244135424, -3340763136, 12747669504,
   -15438446592, 36031578112, -37348048896, 53613481984, -52598882304, 44858597376, -44069191680,
   12325875712, -18512784384, -20852602880, 2983352832, -34809083520, 10008133248, -28847259648,
   7398238560, -15677740224, 3250745280, -5895512772, 953417256, -1546358212, 191193792, -279980791,
   25991688, -34095189, 2319624, -2657481, 127776, -119634, 3864, -2277, 48, 19, 0, 1]
/-- Denominator exponents of `TV3_32` over `bases`. -/
def eTV3_32 : List ℕ := [2, 1, 0, 0, 2, 2, 1]
/-- The value of `T3_32`. -/
def TV3_32 (s : ℝ) : ℝ := zeval nTV3_32 s / bval bases eTV3_32 s

/-- Numerator coefficients (constant term first) of `TV3_40`. -/
def nTV3_40 : List ℤ :=
  [0, 0, 0, 16384, -16384, 90112, -77824, 182272, -112640, 171008, -66560, 70720, -11072, 2080,
   5584, -8784, 3184, -3244, 650, -510, 60, -37, 2, -1]
/-- Denominator exponents of `TV3_40` over `bases`. -/
def eTV3_40 : List ℕ := [2, 0, 0, 0, 1, 1]
/-- The value of `T3_40`. -/
def TV3_40 (s : ℝ) : ℝ := zeval nTV3_40 s / bval bases eTV3_40 s

/-- Numerator coefficients (constant term first) of `TV3_41`. -/
def nTV3_41 : List ℤ :=
  [0, 0, 0, -113246208, 452984832, -833617920, 5083496448, -2763522048, 22296920064, -5229379584,
   49461854208, -5527420928, 59328823296, -5848592384, 35519889408, -20695302144, 7322124288,
   -56200629248, 9000265728, -87469826048, 29077411584, -86508912384, 36101796480, -58255139904,
   25003830336, -27647847552, 11002005936, -9356268828, 3229581960, -2249155804, 641562264,
   -377945407, 85589304, -43090845, 7452024, -3165129, 399888, -135186, 11808, -2469, 144, 19, 0, 1]
/-- Denominator exponents of `TV3_41` over `bases`. -/
def eTV3_41 : List ℕ := [3, 1, 0, 0, 2, 2, 1]
/-- The value of `T3_41`. -/
def TV3_41 (s : ℝ) : ℝ := zeval nTV3_41 s / bval bases eTV3_41 s

/-- Numerator coefficients (constant term first) of `TV3_50`. -/
def nTV3_50 : List ℤ :=
  [0, 0, 0, -566231040, 2264924160, -7716470784, 28311552000, -48370286592, 144892231680,
   -173151485952, 401693736960, -384295288832, 670124605440, -564954705920, 703588270080,
   -593374593024, 477302538240, -490660779008, 230129172480, -351861890048, 115553529600,
   -225130789632, 80427649920, -121493706432, 51036766080, -51326358528, 22502576880, -16115553228,
   6613737240, -3638061772, 1295873400, -574194895, 168029640, -61244589, 14063880, -4190409,
   721680, -166482, 20400, -2853, 240, 19, 0, 1]
/-- Denominator exponents of `TV3_50` over `bases`. -/
def eTV3_50 : List ℕ := [3, 1, 1, 0, 2, 2, 1]
/-- The value of `T3_50`. -/
def TV3_50 (s : ℝ) : ℝ := zeval nTV3_50 s / bval bases eTV3_50 s

/-- The coefficients of `bautinNum`. -/
def nNN : List ℤ :=
  [-64, 0, -160, 0, -132, 0, -22, 0, 12, 0, 1]

/-- The quotient of the numerator of `L2V` by `bautinNum`. -/
def nNQ : List ℤ :=
  [0, 28716555050445445376, 0, 412946415126575872, 0, 614859243328992640, 75497472,
   111949462632177408, 467664896, 30624038768388288, 1294991360, 7309911365316928, 2629042176,
   1818802328406048, 3881467904, 446368322466752, 1158569984, 109567711224080, -8256086016,
   26455596349616, -17498535936, 6131222592280, -17870330880, 1305769059440, -11116382208,
   242242071628, -4520904320, 36952153396, -1236284192, 4340245774, -228985824, 352295336,
   -28484136, 13565259, -2319456, -804197, -117456, -160140, -3328, -10946, -40, -369, 0, -5]

/-- The remainder of the numerator of `L2V` by `bautinNum`. -/
def nNR : List ℤ :=
  [0, 1837859523228508504064, 0, 4621077378639372115968, 0, 3896007684652106458112, 0,
   791815382357009023488, 0, -234480567511344182272]

/-! ## The weight-five truncations of the nonlinearities in the chart -/

/-- Coefficient of `y₀^0 y₁^4` in the product `a2 · a2` of pieces. -/
def Sa2_a2_04 (s : ℝ) : ℝ := CA_02 s ^ 2

/-- Coefficient of `y₀^1 y₁^3` in the product `a2 · a2` of pieces. -/
def Sa2_a2_13 (s : ℝ) : ℝ := 2 * CA_02 s * CA_11 s

/-- Coefficient of `y₀^2 y₁^2` in the product `a2 · a2` of pieces. -/
def Sa2_a2_22 (s : ℝ) : ℝ := CA_11 s ^ 2 + 2 * CA_02 s * CA_20 s

/-- Coefficient of `y₀^3 y₁^1` in the product `a2 · a2` of pieces. -/
def Sa2_a2_31 (s : ℝ) : ℝ := 2 * CA_11 s * CA_20 s

/-- Coefficient of `y₀^4 y₁^0` in the product `a2 · a2` of pieces. -/
def Sa2_a2_40 (s : ℝ) : ℝ := CA_20 s ^ 2

/-- Coefficient of `y₀^0 y₁^5` in the product `a2 · a2 · l0` of pieces. -/
def Sa2_a2_l0_05 (s : ℝ) : ℝ := CA_02 s ^ 2 * s ^ 3 + 4 * s * CA_02 s ^ 2

/-- Coefficient of `y₀^1 y₁^4` in the product `a2 · a2 · l0` of pieces. -/
def Sa2_a2_l0_14 (s : ℝ) : ℝ := CA_02 s ^ 2 * s ^ 3 + 4 * s * CA_02 s ^ 2 + 2 * CA_02 s * CA_11 s *
    s ^ 3 + 8 * CA_02 s * CA_11 s * s

/-- Coefficient of `y₀^2 y₁^3` in the product `a2 · a2 · l0` of pieces. -/
def Sa2_a2_l0_23 (s : ℝ) : ℝ := CA_11 s ^ 2 * s ^ 3 + 4 * s * CA_11 s ^ 2 + 2 * CA_02 s * CA_11 s *
    s ^ 3 + 2 * CA_02 s * CA_20 s * s ^ 3 + 8 * CA_02 s * CA_11 s * s + 8 * CA_02 s * CA_20 s * s

/-- Coefficient of `y₀^3 y₁^2` in the product `a2 · a2 · l0` of pieces. -/
def Sa2_a2_l0_32 (s : ℝ) : ℝ := CA_11 s ^ 2 * s ^ 3 + 4 * s * CA_11 s ^ 2 + 2 * CA_02 s * CA_20 s *
    s ^ 3 + 2 * CA_11 s * CA_20 s * s ^ 3 + 8 * CA_02 s * CA_20 s * s + 8 * CA_11 s * CA_20 s * s

/-- Coefficient of `y₀^4 y₁^1` in the product `a2 · a2 · l0` of pieces. -/
def Sa2_a2_l0_41 (s : ℝ) : ℝ := CA_20 s ^ 2 * s ^ 3 + 4 * s * CA_20 s ^ 2 + 2 * CA_11 s * CA_20 s *
    s ^ 3 + 8 * CA_11 s * CA_20 s * s

/-- Coefficient of `y₀^5 y₁^0` in the product `a2 · a2 · l0` of pieces. -/
def Sa2_a2_l0_50 (s : ℝ) : ℝ := CA_20 s ^ 2 * s ^ 3 + 4 * s * CA_20 s ^ 2

/-- Coefficient of `y₀^0 y₁^5` in the product `a2 · a2 · l2` of pieces. -/
def Sa2_a2_l2_05 (s : ℝ) : ℝ := 2 * CA_02 s ^ 2 + s * CA_02 s ^ 2

/-- Coefficient of `y₀^1 y₁^4` in the product `a2 · a2 · l2` of pieces. -/
def Sa2_a2_l2_14 (s : ℝ) : ℝ := -2 * CA_02 s ^ 2 + s * CA_02 s ^ 2 + 4 * CA_02 s * CA_11 s + 2 *
    CA_02 s * CA_11 s * s

/-- Coefficient of `y₀^2 y₁^3` in the product `a2 · a2 · l2` of pieces. -/
def Sa2_a2_l2_23 (s : ℝ) : ℝ := 2 * CA_11 s ^ 2 + s * CA_11 s ^ 2 - 4 * CA_02 s * CA_11 s + 4 *
    CA_02 s * CA_20 s + 2 * CA_02 s * CA_11 s * s + 2 * CA_02 s * CA_20 s * s

/-- Coefficient of `y₀^3 y₁^2` in the product `a2 · a2 · l2` of pieces. -/
def Sa2_a2_l2_32 (s : ℝ) : ℝ := -2 * CA_11 s ^ 2 + s * CA_11 s ^ 2 - 4 * CA_02 s * CA_20 s + 4 *
    CA_11 s * CA_20 s + 2 * CA_02 s * CA_20 s * s + 2 * CA_11 s * CA_20 s * s

/-- Coefficient of `y₀^4 y₁^1` in the product `a2 · a2 · l2` of pieces. -/
def Sa2_a2_l2_41 (s : ℝ) : ℝ := 2 * CA_20 s ^ 2 + s * CA_20 s ^ 2 - 4 * CA_11 s * CA_20 s + 2 *
    CA_11 s * CA_20 s * s

/-- Coefficient of `y₀^5 y₁^0` in the product `a2 · a2 · l2` of pieces. -/
def Sa2_a2_l2_50 (s : ℝ) : ℝ := -2 * CA_20 s ^ 2 + s * CA_20 s ^ 2

/-- Coefficient of `y₀^0 y₁^5` in the product `a2 · a3` of pieces. -/
def Sa2_a3_05 (s : ℝ) : ℝ := CA_02 s * CA_03 s

/-- Coefficient of `y₀^1 y₁^4` in the product `a2 · a3` of pieces. -/
def Sa2_a3_14 (s : ℝ) : ℝ := CA_02 s * CA_12 s + CA_03 s * CA_11 s

/-- Coefficient of `y₀^2 y₁^3` in the product `a2 · a3` of pieces. -/
def Sa2_a3_23 (s : ℝ) : ℝ := CA_02 s * CA_21 s + CA_03 s * CA_20 s + CA_11 s * CA_12 s

/-- Coefficient of `y₀^3 y₁^2` in the product `a2 · a3` of pieces. -/
def Sa2_a3_32 (s : ℝ) : ℝ := CA_02 s * CA_30 s + CA_11 s * CA_21 s + CA_12 s * CA_20 s

/-- Coefficient of `y₀^4 y₁^1` in the product `a2 · a3` of pieces. -/
def Sa2_a3_41 (s : ℝ) : ℝ := CA_11 s * CA_30 s + CA_20 s * CA_21 s

/-- Coefficient of `y₀^5 y₁^0` in the product `a2 · a3` of pieces. -/
def Sa2_a3_50 (s : ℝ) : ℝ := CA_20 s * CA_30 s

/-- Coefficient of `y₀^0 y₁^5` in the product `a2 · b2 · l0` of pieces. -/
def Sa2_b2_l0_05 (s : ℝ) : ℝ := CA_02 s * CM1_02 s * s ^ 3 + 4 * CA_02 s * CM1_02 s * s

/-- Coefficient of `y₀^1 y₁^4` in the product `a2 · b2 · l0` of pieces. -/
def Sa2_b2_l0_14 (s : ℝ) : ℝ := CA_02 s * CM1_02 s * s ^ 3 + CA_02 s * CM1_11 s * s ^ 3 + CA_11 s *
    CM1_02 s * s ^ 3 + 4 * CA_02 s * CM1_02 s * s + 4 * CA_02 s * CM1_11 s * s + 4 * CA_11 s *
    CM1_02 s * s

/-- Coefficient of `y₀^2 y₁^3` in the product `a2 · b2 · l0` of pieces. -/
def Sa2_b2_l0_23 (s : ℝ) : ℝ := CA_02 s * CM1_11 s * s ^ 3 + CA_02 s * CM1_20 s * s ^ 3 + CA_11 s *
    CM1_02 s * s ^ 3 + CA_11 s * CM1_11 s * s ^ 3 + CA_20 s * CM1_02 s * s ^ 3 + 4 * CA_02 s *
    CM1_11 s * s + 4 * CA_02 s * CM1_20 s * s + 4 * CA_11 s * CM1_02 s * s + 4 * CA_11 s * CM1_11 s
    * s + 4 * CA_20 s * CM1_02 s * s

/-- Coefficient of `y₀^3 y₁^2` in the product `a2 · b2 · l0` of pieces. -/
def Sa2_b2_l0_32 (s : ℝ) : ℝ := CA_02 s * CM1_20 s * s ^ 3 + CA_11 s * CM1_11 s * s ^ 3 + CA_11 s *
    CM1_20 s * s ^ 3 + CA_20 s * CM1_02 s * s ^ 3 + CA_20 s * CM1_11 s * s ^ 3 + 4 * CA_02 s *
    CM1_20 s * s + 4 * CA_11 s * CM1_11 s * s + 4 * CA_11 s * CM1_20 s * s + 4 * CA_20 s * CM1_02 s
    * s + 4 * CA_20 s * CM1_11 s * s

/-- Coefficient of `y₀^4 y₁^1` in the product `a2 · b2 · l0` of pieces. -/
def Sa2_b2_l0_41 (s : ℝ) : ℝ := CA_11 s * CM1_20 s * s ^ 3 + CA_20 s * CM1_11 s * s ^ 3 + CA_20 s *
    CM1_20 s * s ^ 3 + 4 * CA_11 s * CM1_20 s * s + 4 * CA_20 s * CM1_11 s * s + 4 * CA_20 s *
    CM1_20 s * s

/-- Coefficient of `y₀^5 y₁^0` in the product `a2 · b2 · l0` of pieces. -/
def Sa2_b2_l0_50 (s : ℝ) : ℝ := CA_20 s * CM1_20 s * s ^ 3 + 4 * CA_20 s * CM1_20 s * s

/-- Coefficient of `y₀^0 y₁^4` in the product `a2 · c2` of pieces. -/
def Sa2_c2_04 (s : ℝ) : ℝ := CA_02 s * CM2_02 s

/-- Coefficient of `y₀^1 y₁^3` in the product `a2 · c2` of pieces. -/
def Sa2_c2_13 (s : ℝ) : ℝ := CA_02 s * CM2_11 s + CA_11 s * CM2_02 s

/-- Coefficient of `y₀^2 y₁^2` in the product `a2 · c2` of pieces. -/
def Sa2_c2_22 (s : ℝ) : ℝ := CA_02 s * CM2_20 s + CA_11 s * CM2_11 s + CA_20 s * CM2_02 s

/-- Coefficient of `y₀^3 y₁^1` in the product `a2 · c2` of pieces. -/
def Sa2_c2_31 (s : ℝ) : ℝ := CA_11 s * CM2_20 s + CA_20 s * CM2_11 s

/-- Coefficient of `y₀^4 y₁^0` in the product `a2 · c2` of pieces. -/
def Sa2_c2_40 (s : ℝ) : ℝ := CA_20 s * CM2_20 s

/-- Coefficient of `y₀^0 y₁^5` in the product `a2 · c3` of pieces. -/
def Sa2_c3_05 (s : ℝ) : ℝ := CA_02 s * CM2_03 s

/-- Coefficient of `y₀^1 y₁^4` in the product `a2 · c3` of pieces. -/
def Sa2_c3_14 (s : ℝ) : ℝ := CA_02 s * CM2_12 s + CA_11 s * CM2_03 s

/-- Coefficient of `y₀^2 y₁^3` in the product `a2 · c3` of pieces. -/
def Sa2_c3_23 (s : ℝ) : ℝ := CA_02 s * CM2_21 s + CA_11 s * CM2_12 s + CA_20 s * CM2_03 s

/-- Coefficient of `y₀^3 y₁^2` in the product `a2 · c3` of pieces. -/
def Sa2_c3_32 (s : ℝ) : ℝ := CA_02 s * CM2_30 s + CA_11 s * CM2_21 s + CA_20 s * CM2_12 s

/-- Coefficient of `y₀^4 y₁^1` in the product `a2 · c3` of pieces. -/
def Sa2_c3_41 (s : ℝ) : ℝ := CA_11 s * CM2_30 s + CA_20 s * CM2_21 s

/-- Coefficient of `y₀^5 y₁^0` in the product `a2 · c3` of pieces. -/
def Sa2_c3_50 (s : ℝ) : ℝ := CA_20 s * CM2_30 s

/-- Coefficient of `y₀^0 y₁^3` in the product `a2 · l0` of pieces. -/
def Sa2_l0_03 (s : ℝ) : ℝ := CA_02 s * s ^ 3 + 4 * CA_02 s * s

/-- Coefficient of `y₀^1 y₁^2` in the product `a2 · l0` of pieces. -/
def Sa2_l0_12 (s : ℝ) : ℝ := CA_02 s * s ^ 3 + CA_11 s * s ^ 3 + 4 * CA_02 s * s + 4 * CA_11 s * s

/-- Coefficient of `y₀^2 y₁^1` in the product `a2 · l0` of pieces. -/
def Sa2_l0_21 (s : ℝ) : ℝ := CA_11 s * s ^ 3 + CA_20 s * s ^ 3 + 4 * CA_11 s * s + 4 * CA_20 s * s

/-- Coefficient of `y₀^3 y₁^0` in the product `a2 · l0` of pieces. -/
def Sa2_l0_30 (s : ℝ) : ℝ := CA_20 s * s ^ 3 + 4 * CA_20 s * s

/-- Coefficient of `y₀^0 y₁^4` in the product `a2 · l0 · l0` of pieces. -/
def Sa2_l0_l0_04 (s : ℝ) : ℝ := CA_02 s * s ^ 6 + 8 * CA_02 s * s ^ 4 + 16 * CA_02 s * s ^ 2

/-- Coefficient of `y₀^1 y₁^3` in the product `a2 · l0 · l0` of pieces. -/
def Sa2_l0_l0_13 (s : ℝ) : ℝ := CA_11 s * s ^ 6 + 2 * CA_02 s * s ^ 6 + 8 * CA_11 s * s ^ 4 + 16 *
    CA_02 s * s ^ 4 + 16 * CA_11 s * s ^ 2 + 32 * CA_02 s * s ^ 2

/-- Coefficient of `y₀^2 y₁^2` in the product `a2 · l0 · l0` of pieces. -/
def Sa2_l0_l0_22 (s : ℝ) : ℝ := CA_02 s * s ^ 6 + CA_20 s * s ^ 6 + 2 * CA_11 s * s ^ 6 + 8 * CA_02
    s * s ^ 4 + 8 * CA_20 s * s ^ 4 + 16 * CA_02 s * s ^ 2 + 16 * CA_11 s * s ^ 4 + 16 * CA_20 s * s
    ^ 2 + 32 * CA_11 s * s ^ 2

/-- Coefficient of `y₀^3 y₁^1` in the product `a2 · l0 · l0` of pieces. -/
def Sa2_l0_l0_31 (s : ℝ) : ℝ := CA_11 s * s ^ 6 + 2 * CA_20 s * s ^ 6 + 8 * CA_11 s * s ^ 4 + 16 *
    CA_11 s * s ^ 2 + 16 * CA_20 s * s ^ 4 + 32 * CA_20 s * s ^ 2

/-- Coefficient of `y₀^4 y₁^0` in the product `a2 · l0 · l0` of pieces. -/
def Sa2_l0_l0_40 (s : ℝ) : ℝ := CA_20 s * s ^ 6 + 8 * CA_20 s * s ^ 4 + 16 * CA_20 s * s ^ 2

/-- Coefficient of `y₀^0 y₁^5` in the product `a2 · l0 · l0 · l0` of pieces. -/
def Sa2_l0_l0_l0_05 (s : ℝ) : ℝ := CA_02 s * s ^ 9 + 12 * CA_02 s * s ^ 7 + 48 * CA_02 s * s ^ 5 +
    64 * CA_02 s * s ^ 3

/-- Coefficient of `y₀^1 y₁^4` in the product `a2 · l0 · l0 · l0` of pieces. -/
def Sa2_l0_l0_l0_14 (s : ℝ) : ℝ := CA_11 s * s ^ 9 + 3 * CA_02 s * s ^ 9 + 12 * CA_11 s * s ^ 7 + 36
    * CA_02 s * s ^ 7 + 48 * CA_11 s * s ^ 5 + 64 * CA_11 s * s ^ 3 + 144 * CA_02 s * s ^ 5 + 192 *
    CA_02 s * s ^ 3

/-- Coefficient of `y₀^2 y₁^3` in the product `a2 · l0 · l0 · l0` of pieces. -/
def Sa2_l0_l0_l0_23 (s : ℝ) : ℝ := CA_20 s * s ^ 9 + 3 * CA_02 s * s ^ 9 + 3 * CA_11 s * s ^ 9 + 12
    * CA_20 s * s ^ 7 + 36 * CA_02 s * s ^ 7 + 36 * CA_11 s * s ^ 7 + 48 * CA_20 s * s ^ 5 + 64 *
    CA_20 s * s ^ 3 + 144 * CA_02 s * s ^ 5 + 144 * CA_11 s * s ^ 5 + 192 * CA_02 s * s ^ 3 + 192 *
    CA_11 s * s ^ 3

/-- Coefficient of `y₀^3 y₁^2` in the product `a2 · l0 · l0 · l0` of pieces. -/
def Sa2_l0_l0_l0_32 (s : ℝ) : ℝ := CA_02 s * s ^ 9 + 3 * CA_11 s * s ^ 9 + 3 * CA_20 s * s ^ 9 + 12
    * CA_02 s * s ^ 7 + 36 * CA_11 s * s ^ 7 + 36 * CA_20 s * s ^ 7 + 48 * CA_02 s * s ^ 5 + 64 *
    CA_02 s * s ^ 3 + 144 * CA_11 s * s ^ 5 + 144 * CA_20 s * s ^ 5 + 192 * CA_11 s * s ^ 3 + 192 *
    CA_20 s * s ^ 3

/-- Coefficient of `y₀^4 y₁^1` in the product `a2 · l0 · l0 · l0` of pieces. -/
def Sa2_l0_l0_l0_41 (s : ℝ) : ℝ := CA_11 s * s ^ 9 + 3 * CA_20 s * s ^ 9 + 12 * CA_11 s * s ^ 7 + 36
    * CA_20 s * s ^ 7 + 48 * CA_11 s * s ^ 5 + 64 * CA_11 s * s ^ 3 + 144 * CA_20 s * s ^ 5 + 192 *
    CA_20 s * s ^ 3

/-- Coefficient of `y₀^5 y₁^0` in the product `a2 · l0 · l0 · l0` of pieces. -/
def Sa2_l0_l0_l0_50 (s : ℝ) : ℝ := CA_20 s * s ^ 9 + 12 * CA_20 s * s ^ 7 + 48 * CA_20 s * s ^ 5 +
    64 * CA_20 s * s ^ 3

/-- Coefficient of `y₀^0 y₁^5` in the product `a2 · l0 · l0 · l3` of pieces. -/
def Sa2_l0_l0_l3_05 (s : ℝ) : ℝ := CA_02 s * s ^ 7 + CA_02 s * s ^ 8 + 8 * CA_02 s * s ^ 5 + 10 *
    CA_02 s * s ^ 6 + 16 * CA_02 s * s ^ 3 + 32 * CA_02 s * s ^ 2 + 32 * CA_02 s * s ^ 4

/-- Coefficient of `y₀^1 y₁^4` in the product `a2 · l0 · l0 · l3` of pieces. -/
def Sa2_l0_l0_l3_14 (s : ℝ) : ℝ := CA_02 s * s ^ 7 + CA_11 s * s ^ 7 + CA_11 s * s ^ 8 + 3 * CA_02 s
    * s ^ 8 + 8 * CA_02 s * s ^ 5 + 8 * CA_11 s * s ^ 5 + 10 * CA_11 s * s ^ 6 + 16 * CA_02 s * s ^
    3 + 16 * CA_11 s * s ^ 3 + 30 * CA_02 s * s ^ 6 + 32 * CA_11 s * s ^ 2 + 32 * CA_11 s * s ^ 4 +
    96 * CA_02 s * s ^ 2 + 96 * CA_02 s * s ^ 4

/-- Coefficient of `y₀^2 y₁^3` in the product `a2 · l0 · l0 · l3` of pieces. -/
def Sa2_l0_l0_l3_23 (s : ℝ) : ℝ := CA_11 s * s ^ 7 + CA_20 s * s ^ 7 + CA_20 s * s ^ 8 - CA_02 s * s
    ^ 7 - 16 * CA_02 s * s ^ 3 - 8 * CA_02 s * s ^ 5 + 3 * CA_02 s * s ^ 8 + 3 * CA_11 s * s ^ 8 + 8
    * CA_11 s * s ^ 5 + 8 * CA_20 s * s ^ 5 + 10 * CA_20 s * s ^ 6 + 16 * CA_11 s * s ^ 3 + 16 *
    CA_20 s * s ^ 3 + 30 * CA_02 s * s ^ 6 + 30 * CA_11 s * s ^ 6 + 32 * CA_20 s * s ^ 2 + 32 *
    CA_20 s * s ^ 4 + 96 * CA_02 s * s ^ 2 + 96 * CA_02 s * s ^ 4 + 96 * CA_11 s * s ^ 2 + 96 *
    CA_11 s * s ^ 4

/-- Coefficient of `y₀^3 y₁^2` in the product `a2 · l0 · l0 · l3` of pieces. -/
def Sa2_l0_l0_l3_32 (s : ℝ) : ℝ := CA_02 s * s ^ 8 + CA_20 s * s ^ 7 - CA_02 s * s ^ 7 - CA_11 s * s
    ^ 7 - 16 * CA_02 s * s ^ 3 - 16 * CA_11 s * s ^ 3 - 8 * CA_02 s * s ^ 5 - 8 * CA_11 s * s ^ 5 +
    3 * CA_11 s * s ^ 8 + 3 * CA_20 s * s ^ 8 + 8 * CA_20 s * s ^ 5 + 10 * CA_02 s * s ^ 6 + 16 *
    CA_20 s * s ^ 3 + 30 * CA_11 s * s ^ 6 + 30 * CA_20 s * s ^ 6 + 32 * CA_02 s * s ^ 2 + 32 *
    CA_02 s * s ^ 4 + 96 * CA_11 s * s ^ 2 + 96 * CA_11 s * s ^ 4 + 96 * CA_20 s * s ^ 2 + 96 *
    CA_20 s * s ^ 4

/-- Coefficient of `y₀^4 y₁^1` in the product `a2 · l0 · l0 · l3` of pieces. -/
def Sa2_l0_l0_l3_41 (s : ℝ) : ℝ := CA_11 s * s ^ 8 - CA_11 s * s ^ 7 - CA_20 s * s ^ 7 - 16 * CA_11
    s * s ^ 3 - 16 * CA_20 s * s ^ 3 - 8 * CA_11 s * s ^ 5 - 8 * CA_20 s * s ^ 5 + 3 * CA_20 s * s ^
    8 + 10 * CA_11 s * s ^ 6 + 30 * CA_20 s * s ^ 6 + 32 * CA_11 s * s ^ 2 + 32 * CA_11 s * s ^ 4 +
    96 * CA_20 s * s ^ 2 + 96 * CA_20 s * s ^ 4

/-- Coefficient of `y₀^5 y₁^0` in the product `a2 · l0 · l0 · l3` of pieces. -/
def Sa2_l0_l0_l3_50 (s : ℝ) : ℝ := CA_20 s * s ^ 8 - CA_20 s * s ^ 7 - 16 * CA_20 s * s ^ 3 - 8 *
    CA_20 s * s ^ 5 + 10 * CA_20 s * s ^ 6 + 32 * CA_20 s * s ^ 2 + 32 * CA_20 s * s ^ 4

/-- Coefficient of `y₀^0 y₁^4` in the product `a2 · l0 · l2` of pieces. -/
def Sa2_l0_l2_04 (s : ℝ) : ℝ := CA_02 s * s ^ 4 + 2 * CA_02 s * s ^ 3 + 4 * CA_02 s * s ^ 2 + 8 *
    CA_02 s * s

/-- Coefficient of `y₀^1 y₁^3` in the product `a2 · l0 · l2` of pieces. -/
def Sa2_l0_l2_13 (s : ℝ) : ℝ := CA_11 s * s ^ 4 + 2 * CA_02 s * s ^ 4 + 2 * CA_11 s * s ^ 3 + 4 *
    CA_11 s * s ^ 2 + 8 * CA_02 s * s ^ 2 + 8 * CA_11 s * s

/-- Coefficient of `y₀^2 y₁^2` in the product `a2 · l0 · l2` of pieces. -/
def Sa2_l0_l2_22 (s : ℝ) : ℝ := CA_02 s * s ^ 4 + CA_20 s * s ^ 4 - 8 * CA_02 s * s - 2 * CA_02 s *
    s ^ 3 + 2 * CA_11 s * s ^ 4 + 2 * CA_20 s * s ^ 3 + 4 * CA_02 s * s ^ 2 + 4 * CA_20 s * s ^ 2 +
    8 * CA_11 s * s ^ 2 + 8 * CA_20 s * s

/-- Coefficient of `y₀^3 y₁^1` in the product `a2 · l0 · l2` of pieces. -/
def Sa2_l0_l2_31 (s : ℝ) : ℝ := CA_11 s * s ^ 4 - 8 * CA_11 s * s - 2 * CA_11 s * s ^ 3 + 2 * CA_20
    s * s ^ 4 + 4 * CA_11 s * s ^ 2 + 8 * CA_20 s * s ^ 2

/-- Coefficient of `y₀^4 y₁^0` in the product `a2 · l0 · l2` of pieces. -/
def Sa2_l0_l2_40 (s : ℝ) : ℝ := CA_20 s * s ^ 4 - 8 * CA_20 s * s - 2 * CA_20 s * s ^ 3 + 4 * CA_20
    s * s ^ 2

/-- Coefficient of `y₀^0 y₁^3` in the product `a2 · l3` of pieces. -/
def Sa2_l3_03 (s : ℝ) : ℝ := 2 * CA_02 s + CA_02 s * s + CA_02 s * s ^ 2

/-- Coefficient of `y₀^1 y₁^2` in the product `a2 · l3` of pieces. -/
def Sa2_l3_12 (s : ℝ) : ℝ := 2 * CA_02 s + 2 * CA_11 s + CA_02 s * s ^ 2 + CA_11 s * s + CA_11 s * s
    ^ 2 - CA_02 s * s

/-- Coefficient of `y₀^2 y₁^1` in the product `a2 · l3` of pieces. -/
def Sa2_l3_21 (s : ℝ) : ℝ := 2 * CA_11 s + 2 * CA_20 s + CA_11 s * s ^ 2 + CA_20 s * s + CA_20 s * s
    ^ 2 - CA_11 s * s

/-- Coefficient of `y₀^3 y₁^0` in the product `a2 · l3` of pieces. -/
def Sa2_l3_30 (s : ℝ) : ℝ := 2 * CA_20 s + CA_20 s * s ^ 2 - CA_20 s * s

/-- Coefficient of `y₀^0 y₁^5` in the product `a3 · c2` of pieces. -/
def Sa3_c2_05 (s : ℝ) : ℝ := CA_03 s * CM2_02 s

/-- Coefficient of `y₀^1 y₁^4` in the product `a3 · c2` of pieces. -/
def Sa3_c2_14 (s : ℝ) : ℝ := CA_03 s * CM2_11 s + CA_12 s * CM2_02 s

/-- Coefficient of `y₀^2 y₁^3` in the product `a3 · c2` of pieces. -/
def Sa3_c2_23 (s : ℝ) : ℝ := CA_03 s * CM2_20 s + CA_12 s * CM2_11 s + CA_21 s * CM2_02 s

/-- Coefficient of `y₀^3 y₁^2` in the product `a3 · c2` of pieces. -/
def Sa3_c2_32 (s : ℝ) : ℝ := CA_12 s * CM2_20 s + CA_21 s * CM2_11 s + CA_30 s * CM2_02 s

/-- Coefficient of `y₀^4 y₁^1` in the product `a3 · c2` of pieces. -/
def Sa3_c2_41 (s : ℝ) : ℝ := CA_21 s * CM2_20 s + CA_30 s * CM2_11 s

/-- Coefficient of `y₀^5 y₁^0` in the product `a3 · c2` of pieces. -/
def Sa3_c2_50 (s : ℝ) : ℝ := CA_30 s * CM2_20 s

/-- Coefficient of `y₀^0 y₁^4` in the product `a3 · l0` of pieces. -/
def Sa3_l0_04 (s : ℝ) : ℝ := CA_03 s * s ^ 3 + 4 * CA_03 s * s

/-- Coefficient of `y₀^1 y₁^3` in the product `a3 · l0` of pieces. -/
def Sa3_l0_13 (s : ℝ) : ℝ := CA_03 s * s ^ 3 + CA_12 s * s ^ 3 + 4 * CA_03 s * s + 4 * CA_12 s * s

/-- Coefficient of `y₀^2 y₁^2` in the product `a3 · l0` of pieces. -/
def Sa3_l0_22 (s : ℝ) : ℝ := CA_12 s * s ^ 3 + CA_21 s * s ^ 3 + 4 * CA_12 s * s + 4 * CA_21 s * s

/-- Coefficient of `y₀^3 y₁^1` in the product `a3 · l0` of pieces. -/
def Sa3_l0_31 (s : ℝ) : ℝ := CA_21 s * s ^ 3 + CA_30 s * s ^ 3 + 4 * CA_21 s * s + 4 * CA_30 s * s

/-- Coefficient of `y₀^4 y₁^0` in the product `a3 · l0` of pieces. -/
def Sa3_l0_40 (s : ℝ) : ℝ := CA_30 s * s ^ 3 + 4 * CA_30 s * s

/-- Coefficient of `y₀^0 y₁^5` in the product `a3 · l0 · l0` of pieces. -/
def Sa3_l0_l0_05 (s : ℝ) : ℝ := CA_03 s * s ^ 6 + 8 * CA_03 s * s ^ 4 + 16 * CA_03 s * s ^ 2

/-- Coefficient of `y₀^1 y₁^4` in the product `a3 · l0 · l0` of pieces. -/
def Sa3_l0_l0_14 (s : ℝ) : ℝ := CA_12 s * s ^ 6 + 2 * CA_03 s * s ^ 6 + 8 * CA_12 s * s ^ 4 + 16 *
    CA_03 s * s ^ 4 + 16 * CA_12 s * s ^ 2 + 32 * CA_03 s * s ^ 2

/-- Coefficient of `y₀^2 y₁^3` in the product `a3 · l0 · l0` of pieces. -/
def Sa3_l0_l0_23 (s : ℝ) : ℝ := CA_03 s * s ^ 6 + CA_21 s * s ^ 6 + 2 * CA_12 s * s ^ 6 + 8 * CA_03
    s * s ^ 4 + 8 * CA_21 s * s ^ 4 + 16 * CA_03 s * s ^ 2 + 16 * CA_12 s * s ^ 4 + 16 * CA_21 s * s
    ^ 2 + 32 * CA_12 s * s ^ 2

/-- Coefficient of `y₀^3 y₁^2` in the product `a3 · l0 · l0` of pieces. -/
def Sa3_l0_l0_32 (s : ℝ) : ℝ := CA_12 s * s ^ 6 + CA_30 s * s ^ 6 + 2 * CA_21 s * s ^ 6 + 8 * CA_12
    s * s ^ 4 + 8 * CA_30 s * s ^ 4 + 16 * CA_12 s * s ^ 2 + 16 * CA_21 s * s ^ 4 + 16 * CA_30 s * s
    ^ 2 + 32 * CA_21 s * s ^ 2

/-- Coefficient of `y₀^4 y₁^1` in the product `a3 · l0 · l0` of pieces. -/
def Sa3_l0_l0_41 (s : ℝ) : ℝ := CA_21 s * s ^ 6 + 2 * CA_30 s * s ^ 6 + 8 * CA_21 s * s ^ 4 + 16 *
    CA_21 s * s ^ 2 + 16 * CA_30 s * s ^ 4 + 32 * CA_30 s * s ^ 2

/-- Coefficient of `y₀^5 y₁^0` in the product `a3 · l0 · l0` of pieces. -/
def Sa3_l0_l0_50 (s : ℝ) : ℝ := CA_30 s * s ^ 6 + 8 * CA_30 s * s ^ 4 + 16 * CA_30 s * s ^ 2

/-- Coefficient of `y₀^0 y₁^5` in the product `a3 · l0 · l2` of pieces. -/
def Sa3_l0_l2_05 (s : ℝ) : ℝ := CA_03 s * s ^ 4 + 2 * CA_03 s * s ^ 3 + 4 * CA_03 s * s ^ 2 + 8 *
    CA_03 s * s

/-- Coefficient of `y₀^1 y₁^4` in the product `a3 · l0 · l2` of pieces. -/
def Sa3_l0_l2_14 (s : ℝ) : ℝ := CA_12 s * s ^ 4 + 2 * CA_03 s * s ^ 4 + 2 * CA_12 s * s ^ 3 + 4 *
    CA_12 s * s ^ 2 + 8 * CA_03 s * s ^ 2 + 8 * CA_12 s * s

/-- Coefficient of `y₀^2 y₁^3` in the product `a3 · l0 · l2` of pieces. -/
def Sa3_l0_l2_23 (s : ℝ) : ℝ := CA_03 s * s ^ 4 + CA_21 s * s ^ 4 - 8 * CA_03 s * s - 2 * CA_03 s *
    s ^ 3 + 2 * CA_12 s * s ^ 4 + 2 * CA_21 s * s ^ 3 + 4 * CA_03 s * s ^ 2 + 4 * CA_21 s * s ^ 2 +
    8 * CA_12 s * s ^ 2 + 8 * CA_21 s * s

/-- Coefficient of `y₀^3 y₁^2` in the product `a3 · l0 · l2` of pieces. -/
def Sa3_l0_l2_32 (s : ℝ) : ℝ := CA_12 s * s ^ 4 + CA_30 s * s ^ 4 - 8 * CA_12 s * s - 2 * CA_12 s *
    s ^ 3 + 2 * CA_21 s * s ^ 4 + 2 * CA_30 s * s ^ 3 + 4 * CA_12 s * s ^ 2 + 4 * CA_30 s * s ^ 2 +
    8 * CA_21 s * s ^ 2 + 8 * CA_30 s * s

/-- Coefficient of `y₀^4 y₁^1` in the product `a3 · l0 · l2` of pieces. -/
def Sa3_l0_l2_41 (s : ℝ) : ℝ := CA_21 s * s ^ 4 - 8 * CA_21 s * s - 2 * CA_21 s * s ^ 3 + 2 * CA_30
    s * s ^ 4 + 4 * CA_21 s * s ^ 2 + 8 * CA_30 s * s ^ 2

/-- Coefficient of `y₀^5 y₁^0` in the product `a3 · l0 · l2` of pieces. -/
def Sa3_l0_l2_50 (s : ℝ) : ℝ := CA_30 s * s ^ 4 - 8 * CA_30 s * s - 2 * CA_30 s * s ^ 3 + 4 * CA_30
    s * s ^ 2

/-- Coefficient of `y₀^0 y₁^4` in the product `a3 · l3` of pieces. -/
def Sa3_l3_04 (s : ℝ) : ℝ := 2 * CA_03 s + CA_03 s * s + CA_03 s * s ^ 2

/-- Coefficient of `y₀^1 y₁^3` in the product `a3 · l3` of pieces. -/
def Sa3_l3_13 (s : ℝ) : ℝ := 2 * CA_03 s + 2 * CA_12 s + CA_03 s * s ^ 2 + CA_12 s * s + CA_12 s * s
    ^ 2 - CA_03 s * s

/-- Coefficient of `y₀^2 y₁^2` in the product `a3 · l3` of pieces. -/
def Sa3_l3_22 (s : ℝ) : ℝ := 2 * CA_12 s + 2 * CA_21 s + CA_12 s * s ^ 2 + CA_21 s * s + CA_21 s * s
    ^ 2 - CA_12 s * s

/-- Coefficient of `y₀^3 y₁^1` in the product `a3 · l3` of pieces. -/
def Sa3_l3_31 (s : ℝ) : ℝ := 2 * CA_21 s + 2 * CA_30 s + CA_21 s * s ^ 2 + CA_30 s * s + CA_30 s * s
    ^ 2 - CA_21 s * s

/-- Coefficient of `y₀^4 y₁^0` in the product `a3 · l3` of pieces. -/
def Sa3_l3_40 (s : ℝ) : ℝ := 2 * CA_30 s + CA_30 s * s ^ 2 - CA_30 s * s

/-- Coefficient of `y₀^0 y₁^5` in the product `a4 · l0` of pieces. -/
def Sa4_l0_05 (s : ℝ) : ℝ := CA_04 s * s ^ 3 + 4 * CA_04 s * s

/-- Coefficient of `y₀^1 y₁^4` in the product `a4 · l0` of pieces. -/
def Sa4_l0_14 (s : ℝ) : ℝ := CA_04 s * s ^ 3 + CA_13 s * s ^ 3 + 4 * CA_04 s * s + 4 * CA_13 s * s

/-- Coefficient of `y₀^2 y₁^3` in the product `a4 · l0` of pieces. -/
def Sa4_l0_23 (s : ℝ) : ℝ := CA_13 s * s ^ 3 + CA_22 s * s ^ 3 + 4 * CA_13 s * s + 4 * CA_22 s * s

/-- Coefficient of `y₀^3 y₁^2` in the product `a4 · l0` of pieces. -/
def Sa4_l0_32 (s : ℝ) : ℝ := CA_22 s * s ^ 3 + CA_31 s * s ^ 3 + 4 * CA_22 s * s + 4 * CA_31 s * s

/-- Coefficient of `y₀^4 y₁^1` in the product `a4 · l0` of pieces. -/
def Sa4_l0_41 (s : ℝ) : ℝ := CA_31 s * s ^ 3 + CA_40 s * s ^ 3 + 4 * CA_31 s * s + 4 * CA_40 s * s

/-- Coefficient of `y₀^5 y₁^0` in the product `a4 · l0` of pieces. -/
def Sa4_l0_50 (s : ℝ) : ℝ := CA_40 s * s ^ 3 + 4 * CA_40 s * s

/-- Coefficient of `y₀^0 y₁^5` in the product `a4 · l3` of pieces. -/
def Sa4_l3_05 (s : ℝ) : ℝ := 2 * CA_04 s + CA_04 s * s + CA_04 s * s ^ 2

/-- Coefficient of `y₀^1 y₁^4` in the product `a4 · l3` of pieces. -/
def Sa4_l3_14 (s : ℝ) : ℝ := 2 * CA_04 s + 2 * CA_13 s + CA_04 s * s ^ 2 + CA_13 s * s + CA_13 s * s
    ^ 2 - CA_04 s * s

/-- Coefficient of `y₀^2 y₁^3` in the product `a4 · l3` of pieces. -/
def Sa4_l3_23 (s : ℝ) : ℝ := 2 * CA_13 s + 2 * CA_22 s + CA_13 s * s ^ 2 + CA_22 s * s + CA_22 s * s
    ^ 2 - CA_13 s * s

/-- Coefficient of `y₀^3 y₁^2` in the product `a4 · l3` of pieces. -/
def Sa4_l3_32 (s : ℝ) : ℝ := 2 * CA_22 s + 2 * CA_31 s + CA_22 s * s ^ 2 + CA_31 s * s + CA_31 s * s
    ^ 2 - CA_22 s * s

/-- Coefficient of `y₀^4 y₁^1` in the product `a4 · l3` of pieces. -/
def Sa4_l3_41 (s : ℝ) : ℝ := 2 * CA_31 s + 2 * CA_40 s + CA_31 s * s ^ 2 + CA_40 s * s + CA_40 s * s
    ^ 2 - CA_31 s * s

/-- Coefficient of `y₀^5 y₁^0` in the product `a4 · l3` of pieces. -/
def Sa4_l3_50 (s : ℝ) : ℝ := 2 * CA_40 s + CA_40 s * s ^ 2 - CA_40 s * s

/-- Coefficient of `y₀^0 y₁^4` in the product `b2 · l0 · l0` of pieces. -/
def Sb2_l0_l0_04 (s : ℝ) : ℝ := CM1_02 s * s ^ 6 + 8 * CM1_02 s * s ^ 4 + 16 * CM1_02 s * s ^ 2

/-- Coefficient of `y₀^1 y₁^3` in the product `b2 · l0 · l0` of pieces. -/
def Sb2_l0_l0_13 (s : ℝ) : ℝ := CM1_11 s * s ^ 6 + 2 * CM1_02 s * s ^ 6 + 8 * CM1_11 s * s ^ 4 + 16
    * CM1_02 s * s ^ 4 + 16 * CM1_11 s * s ^ 2 + 32 * CM1_02 s * s ^ 2

/-- Coefficient of `y₀^2 y₁^2` in the product `b2 · l0 · l0` of pieces. -/
def Sb2_l0_l0_22 (s : ℝ) : ℝ := CM1_02 s * s ^ 6 + CM1_20 s * s ^ 6 + 2 * CM1_11 s * s ^ 6 + 8 *
    CM1_02 s * s ^ 4 + 8 * CM1_20 s * s ^ 4 + 16 * CM1_02 s * s ^ 2 + 16 * CM1_11 s * s ^ 4 + 16 *
    CM1_20 s * s ^ 2 + 32 * CM1_11 s * s ^ 2

/-- Coefficient of `y₀^3 y₁^1` in the product `b2 · l0 · l0` of pieces. -/
def Sb2_l0_l0_31 (s : ℝ) : ℝ := CM1_11 s * s ^ 6 + 2 * CM1_20 s * s ^ 6 + 8 * CM1_11 s * s ^ 4 + 16
    * CM1_11 s * s ^ 2 + 16 * CM1_20 s * s ^ 4 + 32 * CM1_20 s * s ^ 2

/-- Coefficient of `y₀^4 y₁^0` in the product `b2 · l0 · l0` of pieces. -/
def Sb2_l0_l0_40 (s : ℝ) : ℝ := CM1_20 s * s ^ 6 + 8 * CM1_20 s * s ^ 4 + 16 * CM1_20 s * s ^ 2

/-- Coefficient of `y₀^0 y₁^5` in the product `b3 · l0 · l0` of pieces. -/
def Sb3_l0_l0_05 (s : ℝ) : ℝ := CM1_03 s * s ^ 6 + 8 * CM1_03 s * s ^ 4 + 16 * CM1_03 s * s ^ 2

/-- Coefficient of `y₀^1 y₁^4` in the product `b3 · l0 · l0` of pieces. -/
def Sb3_l0_l0_14 (s : ℝ) : ℝ := CM1_12 s * s ^ 6 + 2 * CM1_03 s * s ^ 6 + 8 * CM1_12 s * s ^ 4 + 16
    * CM1_03 s * s ^ 4 + 16 * CM1_12 s * s ^ 2 + 32 * CM1_03 s * s ^ 2

/-- Coefficient of `y₀^2 y₁^3` in the product `b3 · l0 · l0` of pieces. -/
def Sb3_l0_l0_23 (s : ℝ) : ℝ := CM1_03 s * s ^ 6 + CM1_21 s * s ^ 6 + 2 * CM1_12 s * s ^ 6 + 8 *
    CM1_03 s * s ^ 4 + 8 * CM1_21 s * s ^ 4 + 16 * CM1_03 s * s ^ 2 + 16 * CM1_12 s * s ^ 4 + 16 *
    CM1_21 s * s ^ 2 + 32 * CM1_12 s * s ^ 2

/-- Coefficient of `y₀^3 y₁^2` in the product `b3 · l0 · l0` of pieces. -/
def Sb3_l0_l0_32 (s : ℝ) : ℝ := CM1_12 s * s ^ 6 + CM1_30 s * s ^ 6 + 2 * CM1_21 s * s ^ 6 + 8 *
    CM1_12 s * s ^ 4 + 8 * CM1_30 s * s ^ 4 + 16 * CM1_12 s * s ^ 2 + 16 * CM1_21 s * s ^ 4 + 16 *
    CM1_30 s * s ^ 2 + 32 * CM1_21 s * s ^ 2

/-- Coefficient of `y₀^4 y₁^1` in the product `b3 · l0 · l0` of pieces. -/
def Sb3_l0_l0_41 (s : ℝ) : ℝ := CM1_21 s * s ^ 6 + 2 * CM1_30 s * s ^ 6 + 8 * CM1_21 s * s ^ 4 + 16
    * CM1_21 s * s ^ 2 + 16 * CM1_30 s * s ^ 4 + 32 * CM1_30 s * s ^ 2

/-- Coefficient of `y₀^5 y₁^0` in the product `b3 · l0 · l0` of pieces. -/
def Sb3_l0_l0_50 (s : ℝ) : ℝ := CM1_30 s * s ^ 6 + 8 * CM1_30 s * s ^ 4 + 16 * CM1_30 s * s ^ 2

/-- Coefficient of `y₀^0 y₁^3` in the product `c2 · l0` of pieces. -/
def Sc2_l0_03 (s : ℝ) : ℝ := CM2_02 s * s ^ 3 + 4 * CM2_02 s * s

/-- Coefficient of `y₀^1 y₁^2` in the product `c2 · l0` of pieces. -/
def Sc2_l0_12 (s : ℝ) : ℝ := CM2_02 s * s ^ 3 + CM2_11 s * s ^ 3 + 4 * CM2_02 s * s + 4 * CM2_11 s *
    s

/-- Coefficient of `y₀^2 y₁^1` in the product `c2 · l0` of pieces. -/
def Sc2_l0_21 (s : ℝ) : ℝ := CM2_11 s * s ^ 3 + CM2_20 s * s ^ 3 + 4 * CM2_11 s * s + 4 * CM2_20 s *
    s

/-- Coefficient of `y₀^3 y₁^0` in the product `c2 · l0` of pieces. -/
def Sc2_l0_30 (s : ℝ) : ℝ := CM2_20 s * s ^ 3 + 4 * CM2_20 s * s

/-- Coefficient of `y₀^0 y₁^5` in the product `c2 · l0 · l0 · l0` of pieces. -/
def Sc2_l0_l0_l0_05 (s : ℝ) : ℝ := CM2_02 s * s ^ 9 + 12 * CM2_02 s * s ^ 7 + 48 * CM2_02 s * s ^ 5
    + 64 * CM2_02 s * s ^ 3

/-- Coefficient of `y₀^1 y₁^4` in the product `c2 · l0 · l0 · l0` of pieces. -/
def Sc2_l0_l0_l0_14 (s : ℝ) : ℝ := CM2_11 s * s ^ 9 + 3 * CM2_02 s * s ^ 9 + 12 * CM2_11 s * s ^ 7 +
    36 * CM2_02 s * s ^ 7 + 48 * CM2_11 s * s ^ 5 + 64 * CM2_11 s * s ^ 3 + 144 * CM2_02 s * s ^ 5 +
    192 * CM2_02 s * s ^ 3

/-- Coefficient of `y₀^2 y₁^3` in the product `c2 · l0 · l0 · l0` of pieces. -/
def Sc2_l0_l0_l0_23 (s : ℝ) : ℝ := CM2_20 s * s ^ 9 + 3 * CM2_02 s * s ^ 9 + 3 * CM2_11 s * s ^ 9 +
    12 * CM2_20 s * s ^ 7 + 36 * CM2_02 s * s ^ 7 + 36 * CM2_11 s * s ^ 7 + 48 * CM2_20 s * s ^ 5 +
    64 * CM2_20 s * s ^ 3 + 144 * CM2_02 s * s ^ 5 + 144 * CM2_11 s * s ^ 5 + 192 * CM2_02 s * s ^ 3
    + 192 * CM2_11 s * s ^ 3

/-- Coefficient of `y₀^3 y₁^2` in the product `c2 · l0 · l0 · l0` of pieces. -/
def Sc2_l0_l0_l0_32 (s : ℝ) : ℝ := CM2_02 s * s ^ 9 + 3 * CM2_11 s * s ^ 9 + 3 * CM2_20 s * s ^ 9 +
    12 * CM2_02 s * s ^ 7 + 36 * CM2_11 s * s ^ 7 + 36 * CM2_20 s * s ^ 7 + 48 * CM2_02 s * s ^ 5 +
    64 * CM2_02 s * s ^ 3 + 144 * CM2_11 s * s ^ 5 + 144 * CM2_20 s * s ^ 5 + 192 * CM2_11 s * s ^ 3
    + 192 * CM2_20 s * s ^ 3

/-- Coefficient of `y₀^4 y₁^1` in the product `c2 · l0 · l0 · l0` of pieces. -/
def Sc2_l0_l0_l0_41 (s : ℝ) : ℝ := CM2_11 s * s ^ 9 + 3 * CM2_20 s * s ^ 9 + 12 * CM2_11 s * s ^ 7 +
    36 * CM2_20 s * s ^ 7 + 48 * CM2_11 s * s ^ 5 + 64 * CM2_11 s * s ^ 3 + 144 * CM2_20 s * s ^ 5 +
    192 * CM2_20 s * s ^ 3

/-- Coefficient of `y₀^5 y₁^0` in the product `c2 · l0 · l0 · l0` of pieces. -/
def Sc2_l0_l0_l0_50 (s : ℝ) : ℝ := CM2_20 s * s ^ 9 + 12 * CM2_20 s * s ^ 7 + 48 * CM2_20 s * s ^ 5
    + 64 * CM2_20 s * s ^ 3

/-- Coefficient of `y₀^0 y₁^4` in the product `c3 · l0` of pieces. -/
def Sc3_l0_04 (s : ℝ) : ℝ := CM2_03 s * s ^ 3 + 4 * CM2_03 s * s

/-- Coefficient of `y₀^1 y₁^3` in the product `c3 · l0` of pieces. -/
def Sc3_l0_13 (s : ℝ) : ℝ := CM2_03 s * s ^ 3 + CM2_12 s * s ^ 3 + 4 * CM2_03 s * s + 4 * CM2_12 s *
    s

/-- Coefficient of `y₀^2 y₁^2` in the product `c3 · l0` of pieces. -/
def Sc3_l0_22 (s : ℝ) : ℝ := CM2_12 s * s ^ 3 + CM2_21 s * s ^ 3 + 4 * CM2_12 s * s + 4 * CM2_21 s *
    s

/-- Coefficient of `y₀^3 y₁^1` in the product `c3 · l0` of pieces. -/
def Sc3_l0_31 (s : ℝ) : ℝ := CM2_21 s * s ^ 3 + CM2_30 s * s ^ 3 + 4 * CM2_21 s * s + 4 * CM2_30 s *
    s

/-- Coefficient of `y₀^4 y₁^0` in the product `c3 · l0` of pieces. -/
def Sc3_l0_40 (s : ℝ) : ℝ := CM2_30 s * s ^ 3 + 4 * CM2_30 s * s

/-- Coefficient of `y₀^0 y₁^5` in the product `c4 · l0` of pieces. -/
def Sc4_l0_05 (s : ℝ) : ℝ := CM2_04 s * s ^ 3 + 4 * CM2_04 s * s

/-- Coefficient of `y₀^1 y₁^4` in the product `c4 · l0` of pieces. -/
def Sc4_l0_14 (s : ℝ) : ℝ := CM2_04 s * s ^ 3 + CM2_13 s * s ^ 3 + 4 * CM2_04 s * s + 4 * CM2_13 s *
    s

/-- Coefficient of `y₀^2 y₁^3` in the product `c4 · l0` of pieces. -/
def Sc4_l0_23 (s : ℝ) : ℝ := CM2_13 s * s ^ 3 + CM2_22 s * s ^ 3 + 4 * CM2_13 s * s + 4 * CM2_22 s *
    s

/-- Coefficient of `y₀^3 y₁^2` in the product `c4 · l0` of pieces. -/
def Sc4_l0_32 (s : ℝ) : ℝ := CM2_22 s * s ^ 3 + CM2_31 s * s ^ 3 + 4 * CM2_22 s * s + 4 * CM2_31 s *
    s

/-- Coefficient of `y₀^4 y₁^1` in the product `c4 · l0` of pieces. -/
def Sc4_l0_41 (s : ℝ) : ℝ := CM2_31 s * s ^ 3 + CM2_40 s * s ^ 3 + 4 * CM2_31 s * s + 4 * CM2_40 s *
    s

/-- Coefficient of `y₀^5 y₁^0` in the product `c4 · l0` of pieces. -/
def Sc4_l0_50 (s : ℝ) : ℝ := CM2_40 s * s ^ 3 + 4 * CM2_40 s * s

/-- Coefficient of `y₀^0 y₁^2` in the product `l0 · l0` of pieces. -/
def Sl0_l0_02 (s : ℝ) : ℝ := s ^ 6 + 8 * s ^ 4 + 16 * s ^ 2

/-- Coefficient of `y₀^1 y₁^1` in the product `l0 · l0` of pieces. -/
def Sl0_l0_11 (s : ℝ) : ℝ := 2 * s ^ 6 + 16 * s ^ 4 + 32 * s ^ 2

/-- Coefficient of `y₀^2 y₁^0` in the product `l0 · l0` of pieces. -/
def Sl0_l0_20 (s : ℝ) : ℝ := s ^ 6 + 8 * s ^ 4 + 16 * s ^ 2

/-- Coefficient of `y₀^0 y₁^3` in the product `l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_03 (s : ℝ) : ℝ := s ^ 9 + 12 * s ^ 7 + 48 * s ^ 5 + 64 * s ^ 3

/-- Coefficient of `y₀^1 y₁^2` in the product `l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_12 (s : ℝ) : ℝ := 3 * s ^ 9 + 36 * s ^ 7 + 144 * s ^ 5 + 192 * s ^ 3

/-- Coefficient of `y₀^2 y₁^1` in the product `l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_21 (s : ℝ) : ℝ := 3 * s ^ 9 + 36 * s ^ 7 + 144 * s ^ 5 + 192 * s ^ 3

/-- Coefficient of `y₀^3 y₁^0` in the product `l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_30 (s : ℝ) : ℝ := s ^ 9 + 12 * s ^ 7 + 48 * s ^ 5 + 64 * s ^ 3

/-- Coefficient of `y₀^0 y₁^4` in the product `l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_04 (s : ℝ) : ℝ := s ^ 12 + 16 * s ^ 10 + 96 * s ^ 8 + 256 * s ^ 4 + 256 * s ^ 6

/-- Coefficient of `y₀^1 y₁^3` in the product `l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_13 (s : ℝ) : ℝ := 4 * s ^ 12 + 64 * s ^ 10 + 384 * s ^ 8 + 1024 * s ^ 4 + 1024 * s
    ^ 6

/-- Coefficient of `y₀^2 y₁^2` in the product `l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_22 (s : ℝ) : ℝ := 6 * s ^ 12 + 96 * s ^ 10 + 576 * s ^ 8 + 1536 * s ^ 4 + 1536 * s
    ^ 6

/-- Coefficient of `y₀^3 y₁^1` in the product `l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_31 (s : ℝ) : ℝ := 4 * s ^ 12 + 64 * s ^ 10 + 384 * s ^ 8 + 1024 * s ^ 4 + 1024 * s
    ^ 6

/-- Coefficient of `y₀^4 y₁^0` in the product `l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_40 (s : ℝ) : ℝ := s ^ 12 + 16 * s ^ 10 + 96 * s ^ 8 + 256 * s ^ 4 + 256 * s ^ 6

/-- Coefficient of `y₀^0 y₁^5` in the product `l0 · l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_l0_05 (s : ℝ) : ℝ := s ^ 15 + 20 * s ^ 13 + 160 * s ^ 11 + 640 * s ^ 9 + 1024 * s ^
    5 + 1280 * s ^ 7

/-- Coefficient of `y₀^1 y₁^4` in the product `l0 · l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_l0_14 (s : ℝ) : ℝ := 5 * s ^ 15 + 100 * s ^ 13 + 800 * s ^ 11 + 3200 * s ^ 9 + 5120
    * s ^ 5 + 6400 * s ^ 7

/-- Coefficient of `y₀^2 y₁^3` in the product `l0 · l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_l0_23 (s : ℝ) : ℝ := 10 * s ^ 15 + 200 * s ^ 13 + 1600 * s ^ 11 + 6400 * s ^ 9 +
    10240 * s ^ 5 + 12800 * s ^ 7

/-- Coefficient of `y₀^3 y₁^2` in the product `l0 · l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_l0_32 (s : ℝ) : ℝ := 10 * s ^ 15 + 200 * s ^ 13 + 1600 * s ^ 11 + 6400 * s ^ 9 +
    10240 * s ^ 5 + 12800 * s ^ 7

/-- Coefficient of `y₀^4 y₁^1` in the product `l0 · l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_l0_41 (s : ℝ) : ℝ := 5 * s ^ 15 + 100 * s ^ 13 + 800 * s ^ 11 + 3200 * s ^ 9 + 5120
    * s ^ 5 + 6400 * s ^ 7

/-- Coefficient of `y₀^5 y₁^0` in the product `l0 · l0 · l0 · l0 · l0` of pieces. -/
def Sl0_l0_l0_l0_l0_50 (s : ℝ) : ℝ := s ^ 15 + 20 * s ^ 13 + 160 * s ^ 11 + 640 * s ^ 9 + 1024 * s ^
    5 + 1280 * s ^ 7

/-- Coefficient of `y₀^0 y₁^5` in the product `l0 · l0 · l0 · l0 · l2` of pieces. -/
def Sl0_l0_l0_l0_l2_05 (s : ℝ) : ℝ := s ^ 13 + 2 * s ^ 12 + 16 * s ^ 11 + 32 * s ^ 10 + 96 * s ^ 9 +
    192 * s ^ 8 + 256 * s ^ 5 + 256 * s ^ 7 + 512 * s ^ 4 + 512 * s ^ 6

/-- Coefficient of `y₀^1 y₁^4` in the product `l0 · l0 · l0 · l0 · l2` of pieces. -/
def Sl0_l0_l0_l0_l2_14 (s : ℝ) : ℝ := 5 * s ^ 13 + 6 * s ^ 12 + 80 * s ^ 11 + 96 * s ^ 10 + 480 * s
    ^ 9 + 576 * s ^ 8 + 1280 * s ^ 5 + 1280 * s ^ 7 + 1536 * s ^ 4 + 1536 * s ^ 6

/-- Coefficient of `y₀^2 y₁^3` in the product `l0 · l0 · l0 · l0 · l2` of pieces. -/
def Sl0_l0_l0_l0_l2_23 (s : ℝ) : ℝ := 4 * s ^ 12 + 10 * s ^ 13 + 64 * s ^ 10 + 160 * s ^ 11 + 384 *
    s ^ 8 + 960 * s ^ 9 + 1024 * s ^ 4 + 1024 * s ^ 6 + 2560 * s ^ 5 + 2560 * s ^ 7

/-- Coefficient of `y₀^3 y₁^2` in the product `l0 · l0 · l0 · l0 · l2` of pieces. -/
def Sl0_l0_l0_l0_l2_32 (s : ℝ) : ℝ := -1024 * s ^ 4 - 1024 * s ^ 6 - 384 * s ^ 8 - 64 * s ^ 10 - 4 *
    s ^ 12 + 10 * s ^ 13 + 160 * s ^ 11 + 960 * s ^ 9 + 2560 * s ^ 5 + 2560 * s ^ 7

/-- Coefficient of `y₀^4 y₁^1` in the product `l0 · l0 · l0 · l0 · l2` of pieces. -/
def Sl0_l0_l0_l0_l2_41 (s : ℝ) : ℝ := -1536 * s ^ 4 - 1536 * s ^ 6 - 576 * s ^ 8 - 96 * s ^ 10 - 6 *
    s ^ 12 + 5 * s ^ 13 + 80 * s ^ 11 + 480 * s ^ 9 + 1280 * s ^ 5 + 1280 * s ^ 7

/-- Coefficient of `y₀^5 y₁^0` in the product `l0 · l0 · l0 · l0 · l2` of pieces. -/
def Sl0_l0_l0_l0_l2_50 (s : ℝ) : ℝ := s ^ 13 - 512 * s ^ 4 - 512 * s ^ 6 - 192 * s ^ 8 - 32 * s ^ 10
    - 2 * s ^ 12 + 16 * s ^ 11 + 96 * s ^ 9 + 256 * s ^ 5 + 256 * s ^ 7

/-- Coefficient of `y₀^0 y₁^4` in the product `l0 · l0 · l0 · l3` of pieces. -/
def Sl0_l0_l0_l3_04 (s : ℝ) : ℝ := s ^ 10 + s ^ 11 + 12 * s ^ 8 + 14 * s ^ 9 + 48 * s ^ 6 + 64 * s ^
    4 + 72 * s ^ 7 + 128 * s ^ 3 + 160 * s ^ 5

/-- Coefficient of `y₀^1 y₁^3` in the product `l0 · l0 · l0 · l3` of pieces. -/
def Sl0_l0_l0_l3_13 (s : ℝ) : ℝ := 2 * s ^ 10 + 4 * s ^ 11 + 24 * s ^ 8 + 56 * s ^ 9 + 96 * s ^ 6 +
    128 * s ^ 4 + 288 * s ^ 7 + 512 * s ^ 3 + 640 * s ^ 5

/-- Coefficient of `y₀^2 y₁^2` in the product `l0 · l0 · l0 · l3` of pieces. -/
def Sl0_l0_l0_l3_22 (s : ℝ) : ℝ := 6 * s ^ 11 + 84 * s ^ 9 + 432 * s ^ 7 + 768 * s ^ 3 + 960 * s ^ 5

/-- Coefficient of `y₀^3 y₁^1` in the product `l0 · l0 · l0 · l3` of pieces. -/
def Sl0_l0_l0_l3_31 (s : ℝ) : ℝ := -128 * s ^ 4 - 96 * s ^ 6 - 24 * s ^ 8 - 2 * s ^ 10 + 4 * s ^ 11
    + 56 * s ^ 9 + 288 * s ^ 7 + 512 * s ^ 3 + 640 * s ^ 5

/-- Coefficient of `y₀^4 y₁^0` in the product `l0 · l0 · l0 · l3` of pieces. -/
def Sl0_l0_l0_l3_40 (s : ℝ) : ℝ := s ^ 11 - s ^ 10 - 64 * s ^ 4 - 48 * s ^ 6 - 12 * s ^ 8 + 14 * s ^
    9 + 72 * s ^ 7 + 128 * s ^ 3 + 160 * s ^ 5

/-- Coefficient of `y₀^0 y₁^3` in the product `l0 · l0 · l2` of pieces. -/
def Sl0_l0_l2_03 (s : ℝ) : ℝ := s ^ 7 + 2 * s ^ 6 + 8 * s ^ 5 + 16 * s ^ 3 + 16 * s ^ 4 + 32 * s ^ 2

/-- Coefficient of `y₀^1 y₁^2` in the product `l0 · l0 · l2` of pieces. -/
def Sl0_l0_l2_12 (s : ℝ) : ℝ := 2 * s ^ 6 + 3 * s ^ 7 + 16 * s ^ 4 + 24 * s ^ 5 + 32 * s ^ 2 + 48 *
    s ^ 3

/-- Coefficient of `y₀^2 y₁^1` in the product `l0 · l0 · l2` of pieces. -/
def Sl0_l0_l2_21 (s : ℝ) : ℝ := -32 * s ^ 2 - 16 * s ^ 4 - 2 * s ^ 6 + 3 * s ^ 7 + 24 * s ^ 5 + 48 *
    s ^ 3

/-- Coefficient of `y₀^3 y₁^0` in the product `l0 · l0 · l2` of pieces. -/
def Sl0_l0_l2_30 (s : ℝ) : ℝ := s ^ 7 - 32 * s ^ 2 - 16 * s ^ 4 - 2 * s ^ 6 + 8 * s ^ 5 + 16 * s ^ 3

/-- Coefficient of `y₀^0 y₁^2` in the product `l0 · l3` of pieces. -/
def Sl0_l3_02 (s : ℝ) : ℝ := s ^ 4 + s ^ 5 + 4 * s ^ 2 + 6 * s ^ 3 + 8 * s

/-- Coefficient of `y₀^1 y₁^1` in the product `l0 · l3` of pieces. -/
def Sl0_l3_11 (s : ℝ) : ℝ := 2 * s ^ 5 + 12 * s ^ 3 + 16 * s

/-- Coefficient of `y₀^2 y₁^0` in the product `l0 · l3` of pieces. -/
def Sl0_l3_20 (s : ℝ) : ℝ := s ^ 5 - s ^ 4 - 4 * s ^ 2 + 6 * s ^ 3 + 8 * s

/-- Coefficient of `y₀^0 y₁^2` in the weight-five part of the nonlinearity `f_1`. -/
def T1_02 (s : ℝ) : ℝ := Sl0_l3_02 s * (-4 - s ^ 2)

/-- Coefficient of `y₀^0 y₁^3` in the weight-five part of the nonlinearity `f_1`. -/
def T1_03 (s : ℝ) : ℝ := Sa2_l3_03 s * (-4 - s ^ 2) + Sc2_l0_03 s * (-4 - s ^ 2) + Sl0_l0_l2_03 s *
    (2 + (s ^ 2) / (2))

/-- Coefficient of `y₀^0 y₁^4` in the weight-five part of the nonlinearity `f_1`. -/
def T1_04 (s : ℝ) : ℝ := Sa2_c2_04 s * (-4 - s ^ 2) + Sa2_l0_l2_04 s * (4 + s ^ 2) + Sa3_l3_04 s *
    (-4 - s ^ 2) + Sb2_l0_l0_04 s * (2 + (s ^ 2) / (2)) + Sc3_l0_04 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l3_04 s * ((2 / 3) + (s ^ 2) / (6))

/-- Coefficient of `y₀^0 y₁^5` in the weight-five part of the nonlinearity `f_1`. -/
def T1_05 (s : ℝ) : ℝ := Sa2_a2_l2_05 s * (2 + (s ^ 2) / (2)) + Sa2_b2_l0_05 s * (4 + s ^ 2) +
    Sa2_c3_05 s * (-4 - s ^ 2) + Sa2_l0_l0_l3_05 s * (2 + (s ^ 2) / (2)) + Sa3_c2_05 s * (-4 - s ^
    2) + Sa3_l0_l2_05 s * (4 + s ^ 2) + Sa4_l3_05 s * (-4 - s ^ 2) + Sb3_l0_l0_05 s * (2 + (s ^ 2) /
    (2)) + Sc2_l0_l0_l0_05 s * ((2 / 3) + (s ^ 2) / (6)) + Sc4_l0_05 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l0_l2_05 s * ((-1 / 6) + (-s ^ 2) / (24))

/-- Coefficient of `y₀^1 y₁^1` in the weight-five part of the nonlinearity `f_1`. -/
def T1_11 (s : ℝ) : ℝ := Sl0_l3_11 s * (-4 - s ^ 2)

/-- Coefficient of `y₀^1 y₁^2` in the weight-five part of the nonlinearity `f_1`. -/
def T1_12 (s : ℝ) : ℝ := Sa2_l3_12 s * (-4 - s ^ 2) + Sc2_l0_12 s * (-4 - s ^ 2) + Sl0_l0_l2_12 s *
    (2 + (s ^ 2) / (2))

/-- Coefficient of `y₀^1 y₁^3` in the weight-five part of the nonlinearity `f_1`. -/
def T1_13 (s : ℝ) : ℝ := Sa2_c2_13 s * (-4 - s ^ 2) + Sa2_l0_l2_13 s * (4 + s ^ 2) + Sa3_l3_13 s *
    (-4 - s ^ 2) + Sb2_l0_l0_13 s * (2 + (s ^ 2) / (2)) + Sc3_l0_13 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l3_13 s * ((2 / 3) + (s ^ 2) / (6))

/-- Coefficient of `y₀^1 y₁^4` in the weight-five part of the nonlinearity `f_1`. -/
def T1_14 (s : ℝ) : ℝ := Sa2_a2_l2_14 s * (2 + (s ^ 2) / (2)) + Sa2_b2_l0_14 s * (4 + s ^ 2) +
    Sa2_c3_14 s * (-4 - s ^ 2) + Sa2_l0_l0_l3_14 s * (2 + (s ^ 2) / (2)) + Sa3_c2_14 s * (-4 - s ^
    2) + Sa3_l0_l2_14 s * (4 + s ^ 2) + Sa4_l3_14 s * (-4 - s ^ 2) + Sb3_l0_l0_14 s * (2 + (s ^ 2) /
    (2)) + Sc2_l0_l0_l0_14 s * ((2 / 3) + (s ^ 2) / (6)) + Sc4_l0_14 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l0_l2_14 s * ((-1 / 6) + (-s ^ 2) / (24))

/-- Coefficient of `y₀^2 y₁^0` in the weight-five part of the nonlinearity `f_1`. -/
def T1_20 (s : ℝ) : ℝ := Sl0_l3_20 s * (-4 - s ^ 2)

/-- Coefficient of `y₀^2 y₁^1` in the weight-five part of the nonlinearity `f_1`. -/
def T1_21 (s : ℝ) : ℝ := Sa2_l3_21 s * (-4 - s ^ 2) + Sc2_l0_21 s * (-4 - s ^ 2) + Sl0_l0_l2_21 s *
    (2 + (s ^ 2) / (2))

/-- Coefficient of `y₀^2 y₁^2` in the weight-five part of the nonlinearity `f_1`. -/
def T1_22 (s : ℝ) : ℝ := Sa2_c2_22 s * (-4 - s ^ 2) + Sa2_l0_l2_22 s * (4 + s ^ 2) + Sa3_l3_22 s *
    (-4 - s ^ 2) + Sb2_l0_l0_22 s * (2 + (s ^ 2) / (2)) + Sc3_l0_22 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l3_22 s * ((2 / 3) + (s ^ 2) / (6))

/-- Coefficient of `y₀^2 y₁^3` in the weight-five part of the nonlinearity `f_1`. -/
def T1_23 (s : ℝ) : ℝ := Sa2_a2_l2_23 s * (2 + (s ^ 2) / (2)) + Sa2_b2_l0_23 s * (4 + s ^ 2) +
    Sa2_c3_23 s * (-4 - s ^ 2) + Sa2_l0_l0_l3_23 s * (2 + (s ^ 2) / (2)) + Sa3_c2_23 s * (-4 - s ^
    2) + Sa3_l0_l2_23 s * (4 + s ^ 2) + Sa4_l3_23 s * (-4 - s ^ 2) + Sb3_l0_l0_23 s * (2 + (s ^ 2) /
    (2)) + Sc2_l0_l0_l0_23 s * ((2 / 3) + (s ^ 2) / (6)) + Sc4_l0_23 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l0_l2_23 s * ((-1 / 6) + (-s ^ 2) / (24))

/-- Coefficient of `y₀^3 y₁^0` in the weight-five part of the nonlinearity `f_1`. -/
def T1_30 (s : ℝ) : ℝ := Sa2_l3_30 s * (-4 - s ^ 2) + Sc2_l0_30 s * (-4 - s ^ 2) + Sl0_l0_l2_30 s *
    (2 + (s ^ 2) / (2))

/-- Coefficient of `y₀^3 y₁^1` in the weight-five part of the nonlinearity `f_1`. -/
def T1_31 (s : ℝ) : ℝ := Sa2_c2_31 s * (-4 - s ^ 2) + Sa2_l0_l2_31 s * (4 + s ^ 2) + Sa3_l3_31 s *
    (-4 - s ^ 2) + Sb2_l0_l0_31 s * (2 + (s ^ 2) / (2)) + Sc3_l0_31 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l3_31 s * ((2 / 3) + (s ^ 2) / (6))

/-- Coefficient of `y₀^3 y₁^2` in the weight-five part of the nonlinearity `f_1`. -/
def T1_32 (s : ℝ) : ℝ := Sa2_a2_l2_32 s * (2 + (s ^ 2) / (2)) + Sa2_b2_l0_32 s * (4 + s ^ 2) +
    Sa2_c3_32 s * (-4 - s ^ 2) + Sa2_l0_l0_l3_32 s * (2 + (s ^ 2) / (2)) + Sa3_c2_32 s * (-4 - s ^
    2) + Sa3_l0_l2_32 s * (4 + s ^ 2) + Sa4_l3_32 s * (-4 - s ^ 2) + Sb3_l0_l0_32 s * (2 + (s ^ 2) /
    (2)) + Sc2_l0_l0_l0_32 s * ((2 / 3) + (s ^ 2) / (6)) + Sc4_l0_32 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l0_l2_32 s * ((-1 / 6) + (-s ^ 2) / (24))

/-- Coefficient of `y₀^4 y₁^0` in the weight-five part of the nonlinearity `f_1`. -/
def T1_40 (s : ℝ) : ℝ := Sa2_c2_40 s * (-4 - s ^ 2) + Sa2_l0_l2_40 s * (4 + s ^ 2) + Sa3_l3_40 s *
    (-4 - s ^ 2) + Sb2_l0_l0_40 s * (2 + (s ^ 2) / (2)) + Sc3_l0_40 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l3_40 s * ((2 / 3) + (s ^ 2) / (6))

/-- Coefficient of `y₀^4 y₁^1` in the weight-five part of the nonlinearity `f_1`. -/
def T1_41 (s : ℝ) : ℝ := Sa2_a2_l2_41 s * (2 + (s ^ 2) / (2)) + Sa2_b2_l0_41 s * (4 + s ^ 2) +
    Sa2_c3_41 s * (-4 - s ^ 2) + Sa2_l0_l0_l3_41 s * (2 + (s ^ 2) / (2)) + Sa3_c2_41 s * (-4 - s ^
    2) + Sa3_l0_l2_41 s * (4 + s ^ 2) + Sa4_l3_41 s * (-4 - s ^ 2) + Sb3_l0_l0_41 s * (2 + (s ^ 2) /
    (2)) + Sc2_l0_l0_l0_41 s * ((2 / 3) + (s ^ 2) / (6)) + Sc4_l0_41 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l0_l2_41 s * ((-1 / 6) + (-s ^ 2) / (24))

/-- Coefficient of `y₀^5 y₁^0` in the weight-five part of the nonlinearity `f_1`. -/
def T1_50 (s : ℝ) : ℝ := Sa2_a2_l2_50 s * (2 + (s ^ 2) / (2)) + Sa2_b2_l0_50 s * (4 + s ^ 2) +
    Sa2_c3_50 s * (-4 - s ^ 2) + Sa2_l0_l0_l3_50 s * (2 + (s ^ 2) / (2)) + Sa3_c2_50 s * (-4 - s ^
    2) + Sa3_l0_l2_50 s * (4 + s ^ 2) + Sa4_l3_50 s * (-4 - s ^ 2) + Sb3_l0_l0_50 s * (2 + (s ^ 2) /
    (2)) + Sc2_l0_l0_l0_50 s * ((2 / 3) + (s ^ 2) / (6)) + Sc4_l0_50 s * (-4 - s ^ 2) +
    Sl0_l0_l0_l0_l2_50 s * ((-1 / 6) + (-s ^ 2) / (24))

/-- Coefficient of `y₀^0 y₁^2` in the weight-five part of the nonlinearity `f_2`. -/
def T2_02 (s : ℝ) : ℝ := (-Sl0_l0_02 s) / (2)

/-- Coefficient of `y₀^0 y₁^3` in the weight-five part of the nonlinearity `f_2`. -/
def T2_03 (s : ℝ) : ℝ := -Sa2_l0_03 s

/-- Coefficient of `y₀^0 y₁^4` in the weight-five part of the nonlinearity `f_2`. -/
def T2_04 (s : ℝ) : ℝ := -Sa3_l0_04 s + (-Sa2_a2_04 s) / (2) + (Sl0_l0_l0_l0_04 s) / (24)

/-- Coefficient of `y₀^0 y₁^5` in the weight-five part of the nonlinearity `f_2`. -/
def T2_05 (s : ℝ) : ℝ := -Sa2_a3_05 s - Sa4_l0_05 s + (Sa2_l0_l0_l0_05 s) / (6)

/-- Coefficient of `y₀^1 y₁^1` in the weight-five part of the nonlinearity `f_2`. -/
def T2_11 (s : ℝ) : ℝ := (-Sl0_l0_11 s) / (2)

/-- Coefficient of `y₀^1 y₁^2` in the weight-five part of the nonlinearity `f_2`. -/
def T2_12 (s : ℝ) : ℝ := -Sa2_l0_12 s

/-- Coefficient of `y₀^1 y₁^3` in the weight-five part of the nonlinearity `f_2`. -/
def T2_13 (s : ℝ) : ℝ := -Sa3_l0_13 s + (-Sa2_a2_13 s) / (2) + (Sl0_l0_l0_l0_13 s) / (24)

/-- Coefficient of `y₀^1 y₁^4` in the weight-five part of the nonlinearity `f_2`. -/
def T2_14 (s : ℝ) : ℝ := -Sa2_a3_14 s - Sa4_l0_14 s + (Sa2_l0_l0_l0_14 s) / (6)

/-- Coefficient of `y₀^2 y₁^0` in the weight-five part of the nonlinearity `f_2`. -/
def T2_20 (s : ℝ) : ℝ := (-Sl0_l0_20 s) / (2)

/-- Coefficient of `y₀^2 y₁^1` in the weight-five part of the nonlinearity `f_2`. -/
def T2_21 (s : ℝ) : ℝ := -Sa2_l0_21 s

/-- Coefficient of `y₀^2 y₁^2` in the weight-five part of the nonlinearity `f_2`. -/
def T2_22 (s : ℝ) : ℝ := -Sa3_l0_22 s + (-Sa2_a2_22 s) / (2) + (Sl0_l0_l0_l0_22 s) / (24)

/-- Coefficient of `y₀^2 y₁^3` in the weight-five part of the nonlinearity `f_2`. -/
def T2_23 (s : ℝ) : ℝ := -Sa2_a3_23 s - Sa4_l0_23 s + (Sa2_l0_l0_l0_23 s) / (6)

/-- Coefficient of `y₀^3 y₁^0` in the weight-five part of the nonlinearity `f_2`. -/
def T2_30 (s : ℝ) : ℝ := -Sa2_l0_30 s

/-- Coefficient of `y₀^3 y₁^1` in the weight-five part of the nonlinearity `f_2`. -/
def T2_31 (s : ℝ) : ℝ := -Sa3_l0_31 s + (-Sa2_a2_31 s) / (2) + (Sl0_l0_l0_l0_31 s) / (24)

/-- Coefficient of `y₀^3 y₁^2` in the weight-five part of the nonlinearity `f_2`. -/
def T2_32 (s : ℝ) : ℝ := -Sa2_a3_32 s - Sa4_l0_32 s + (Sa2_l0_l0_l0_32 s) / (6)

/-- Coefficient of `y₀^4 y₁^0` in the weight-five part of the nonlinearity `f_2`. -/
def T2_40 (s : ℝ) : ℝ := -Sa3_l0_40 s + (-Sa2_a2_40 s) / (2) + (Sl0_l0_l0_l0_40 s) / (24)

/-- Coefficient of `y₀^4 y₁^1` in the weight-five part of the nonlinearity `f_2`. -/
def T2_41 (s : ℝ) : ℝ := -Sa2_a3_41 s - Sa4_l0_41 s + (Sa2_l0_l0_l0_41 s) / (6)

/-- Coefficient of `y₀^5 y₁^0` in the weight-five part of the nonlinearity `f_2`. -/
def T2_50 (s : ℝ) : ℝ := -Sa2_a3_50 s - Sa4_l0_50 s + (Sa2_l0_l0_l0_50 s) / (6)

/-- Coefficient of `y₀^0 y₁^2` in the weight-five part of the nonlinearity `f_3`. -/
def T3_02 (_s : ℝ) : ℝ := 0

/-- Coefficient of `y₀^0 y₁^3` in the weight-five part of the nonlinearity `f_3`. -/
def T3_03 (s : ℝ) : ℝ := (-Sl0_l0_l0_03 s) / (6)

/-- Coefficient of `y₀^0 y₁^4` in the weight-five part of the nonlinearity `f_3`. -/
def T3_04 (s : ℝ) : ℝ := (-Sa2_l0_l0_04 s) / (2)

/-- Coefficient of `y₀^0 y₁^5` in the weight-five part of the nonlinearity `f_3`. -/
def T3_05 (s : ℝ) : ℝ := (-Sa2_a2_l0_05 s) / (2) + (-Sa3_l0_l0_05 s) / (2) + (Sl0_l0_l0_l0_l0_05 s)
    / (120)

/-- Coefficient of `y₀^1 y₁^1` in the weight-five part of the nonlinearity `f_3`. -/
def T3_11 (_s : ℝ) : ℝ := 0

/-- Coefficient of `y₀^1 y₁^2` in the weight-five part of the nonlinearity `f_3`. -/
def T3_12 (s : ℝ) : ℝ := (-Sl0_l0_l0_12 s) / (6)

/-- Coefficient of `y₀^1 y₁^3` in the weight-five part of the nonlinearity `f_3`. -/
def T3_13 (s : ℝ) : ℝ := (-Sa2_l0_l0_13 s) / (2)

/-- Coefficient of `y₀^1 y₁^4` in the weight-five part of the nonlinearity `f_3`. -/
def T3_14 (s : ℝ) : ℝ := (-Sa2_a2_l0_14 s) / (2) + (-Sa3_l0_l0_14 s) / (2) + (Sl0_l0_l0_l0_l0_14 s)
    / (120)

/-- Coefficient of `y₀^2 y₁^0` in the weight-five part of the nonlinearity `f_3`. -/
def T3_20 (_s : ℝ) : ℝ := 0

/-- Coefficient of `y₀^2 y₁^1` in the weight-five part of the nonlinearity `f_3`. -/
def T3_21 (s : ℝ) : ℝ := (-Sl0_l0_l0_21 s) / (6)

/-- Coefficient of `y₀^2 y₁^2` in the weight-five part of the nonlinearity `f_3`. -/
def T3_22 (s : ℝ) : ℝ := (-Sa2_l0_l0_22 s) / (2)

/-- Coefficient of `y₀^2 y₁^3` in the weight-five part of the nonlinearity `f_3`. -/
def T3_23 (s : ℝ) : ℝ := (-Sa2_a2_l0_23 s) / (2) + (-Sa3_l0_l0_23 s) / (2) + (Sl0_l0_l0_l0_l0_23 s)
    / (120)

/-- Coefficient of `y₀^3 y₁^0` in the weight-five part of the nonlinearity `f_3`. -/
def T3_30 (s : ℝ) : ℝ := (-Sl0_l0_l0_30 s) / (6)

/-- Coefficient of `y₀^3 y₁^1` in the weight-five part of the nonlinearity `f_3`. -/
def T3_31 (s : ℝ) : ℝ := (-Sa2_l0_l0_31 s) / (2)

/-- Coefficient of `y₀^3 y₁^2` in the weight-five part of the nonlinearity `f_3`. -/
def T3_32 (s : ℝ) : ℝ := (-Sa2_a2_l0_32 s) / (2) + (-Sa3_l0_l0_32 s) / (2) + (Sl0_l0_l0_l0_l0_32 s)
    / (120)

/-- Coefficient of `y₀^4 y₁^0` in the weight-five part of the nonlinearity `f_3`. -/
def T3_40 (s : ℝ) : ℝ := (-Sa2_l0_l0_40 s) / (2)

/-- Coefficient of `y₀^4 y₁^1` in the weight-five part of the nonlinearity `f_3`. -/
def T3_41 (s : ℝ) : ℝ := (-Sa2_a2_l0_41 s) / (2) + (-Sa3_l0_l0_41 s) / (2) + (Sl0_l0_l0_l0_l0_41 s)
    / (120)

/-- Coefficient of `y₀^5 y₁^0` in the weight-five part of the nonlinearity `f_3`. -/
def T3_50 (s : ℝ) : ℝ := (-Sa2_a2_l0_50 s) / (2) + (-Sa3_l0_l0_50 s) / (2) + (Sl0_l0_l0_l0_l0_50 s)
    / (120)

/-- **The quintic jet** of the chart field of the approximate centre manifold in the
critical chart (rotation coordinates of `rotL 1`). -/
def jet (s : ℝ) : Jet5 where
  a20 := JA_20 s
  a11 := JA_11 s
  a02 := JA_02 s
  a30 := JA_30 s
  a21 := JA_21 s
  a12 := JA_12 s
  a03 := JA_03 s
  a40 := JA_40 s
  a31 := JA_31 s
  a22 := JA_22 s
  a13 := JA_13 s
  a04 := JA_04 s
  a50 := JA_50 s
  a41 := JA_41 s
  a32 := JA_32 s
  a23 := JA_23 s
  a14 := JA_14 s
  a05 := JA_05 s
  b20 := JB_20 s
  b11 := JB_11 s
  b02 := JB_02 s
  b30 := JB_30 s
  b21 := JB_21 s
  b12 := JB_12 s
  b03 := JB_03 s
  b40 := JB_40 s
  b31 := JB_31 s
  b22 := JB_22 s
  b13 := JB_13 s
  b04 := JB_04 s
  b50 := JB_50 s
  b41 := JB_41 s
  b32 := JB_32 s
  b23 := JB_23 s
  b14 := JB_14 s
  b05 := JB_05 s

/-! ## The homological equations of orders two to four -/

/-- Coefficient of `y₀^0 y₁^2` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_02 (s : ℝ) : ℝ := -CM1_11 s - CM2_02 s - T2_02 s - 2 * JA_02 s + 2 * JB_02 s + CM1_02 s * s
    + JA_02 s * s + JB_02 s * s

/-- Coefficient of `y₀^0 y₁^3` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_03 (s : ℝ) : ℝ := -CM1_12 s - CM2_03 s - T2_03 s - 2 * JA_03 s + 2 * JB_03 s + CM1_03 s * s
    + CM1_11 s * JA_02 s + JA_03 s * s + JB_03 s * s + 2 * CM1_02 s * JB_02 s

/-- Coefficient of `y₀^0 y₁^4` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_04 (s : ℝ) : ℝ := -CM1_13 s - CM2_04 s - T2_04 s - 2 * JA_04 s + 2 * JB_04 s + CM1_04 s * s
    + CM1_11 s * JA_03 s + CM1_12 s * JA_02 s + JA_04 s * s + JB_04 s * s + 2 * CM1_02 s * JB_03 s +
    3 * CM1_03 s * JB_02 s

/-- Coefficient of `y₀^1 y₁^1` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_11 (s : ℝ) : ℝ := -CM2_11 s - T2_11 s - 2 * CM1_20 s - 2 * JA_11 s + 2 * CM1_02 s + 2 *
    JB_11 s + CM1_11 s * s + JA_11 s * s + JB_11 s * s

/-- Coefficient of `y₀^1 y₁^2` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_12 (s : ℝ) : ℝ := -CM2_12 s - T2_12 s - 2 * CM1_21 s - 2 * JA_12 s + 2 * JB_12 s + 3 *
    CM1_03 s + CM1_11 s * JA_11 s + CM1_11 s * JB_02 s + CM1_12 s * s + JA_12 s * s + JB_12 s * s +
    2 * CM1_02 s * JB_11 s + 2 * CM1_20 s * JA_02 s

/-- Coefficient of `y₀^1 y₁^3` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_13 (s : ℝ) : ℝ := -CM2_13 s - T2_13 s - 2 * CM1_22 s - 2 * JA_13 s + 2 * JB_13 s + 4 *
    CM1_04 s + CM1_11 s * JA_12 s + CM1_11 s * JB_03 s + CM1_12 s * JA_11 s + CM1_13 s * s + JA_13 s
    * s + JB_13 s * s + 2 * CM1_02 s * JB_12 s + 2 * CM1_12 s * JB_02 s + 2 * CM1_20 s * JA_03 s + 2
    * CM1_21 s * JA_02 s + 3 * CM1_03 s * JB_11 s

/-- Coefficient of `y₀^2 y₁^0` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_20 (s : ℝ) : ℝ := CM1_11 s - CM2_20 s - T2_20 s - 2 * JA_20 s + 2 * JB_20 s + CM1_20 s * s
    + JA_20 s * s + JB_20 s * s

/-- Coefficient of `y₀^2 y₁^1` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_21 (s : ℝ) : ℝ := -CM2_21 s - T2_21 s - 3 * CM1_30 s - 2 * JA_21 s + 2 * CM1_12 s + 2 *
    JB_21 s + CM1_11 s * JA_20 s + CM1_11 s * JB_11 s + CM1_21 s * s + JA_21 s * s + JB_21 s * s + 2
    * CM1_02 s * JB_20 s + 2 * CM1_20 s * JA_11 s

/-- Coefficient of `y₀^2 y₁^2` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_22 (s : ℝ) : ℝ := -CM2_22 s - T2_22 s - 3 * CM1_31 s - 2 * JA_22 s + 2 * JB_22 s + 3 *
    CM1_13 s + CM1_11 s * JA_21 s + CM1_11 s * JB_12 s + CM1_12 s * JA_20 s + CM1_21 s * JB_02 s +
    CM1_22 s * s + JA_22 s * s + JB_22 s * s + 2 * CM1_02 s * JB_21 s + 2 * CM1_12 s * JB_11 s + 2 *
    CM1_20 s * JA_12 s + 2 * CM1_21 s * JA_11 s + 3 * CM1_03 s * JB_20 s + 3 * CM1_30 s * JA_02 s

/-- Coefficient of `y₀^3 y₁^0` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_30 (s : ℝ) : ℝ := CM1_21 s - CM2_30 s - T2_30 s - 2 * JA_30 s + 2 * JB_30 s + CM1_11 s *
    JB_20 s + CM1_30 s * s + JA_30 s * s + JB_30 s * s + 2 * CM1_20 s * JA_20 s

/-- Coefficient of `y₀^3 y₁^1` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_31 (s : ℝ) : ℝ := -CM2_31 s - T2_31 s - 4 * CM1_40 s - 2 * JA_31 s + 2 * CM1_22 s + 2 *
    JB_31 s + CM1_11 s * JA_30 s + CM1_11 s * JB_21 s + CM1_21 s * JB_11 s + CM1_31 s * s + JA_31 s
    * s + JB_31 s * s + 2 * CM1_02 s * JB_30 s + 2 * CM1_12 s * JB_20 s + 2 * CM1_20 s * JA_21 s + 2
    * CM1_21 s * JA_20 s + 3 * CM1_30 s * JA_11 s

/-- Coefficient of `y₀^4 y₁^0` in the polynomial part of the invariance defect, component `2`. -/
def Hom2_40 (s : ℝ) : ℝ := CM1_31 s - CM2_40 s - T2_40 s - 2 * JA_40 s + 2 * JB_40 s + CM1_11 s *
    JB_30 s + CM1_21 s * JB_20 s + CM1_40 s * s + JA_40 s * s + JB_40 s * s + 2 * CM1_20 s * JA_30 s
    + 3 * CM1_30 s * JA_20 s

/-- Coefficient of `y₀^0 y₁^2` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_02 (s : ℝ) : ℝ := -CM2_11 s - T3_02 s + 2 * CM1_02 s + 2 * JA_02 s + 2 * JB_02 s + CM2_02 s
    * s + JA_02 s * s ^ 2 + JB_02 s * s + JB_02 s * s ^ 2 - JA_02 s * s + (2 * CM2_02 s) / (s)

/-- Coefficient of `y₀^0 y₁^3` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_03 (s : ℝ) : ℝ := -CM2_12 s - T3_03 s + 2 * CM1_03 s + 2 * JA_03 s + 2 * JB_03 s + CM2_03 s
    * s + CM2_11 s * JA_02 s + JA_03 s * s ^ 2 + JB_03 s * s + JB_03 s * s ^ 2 - JA_03 s * s + 2 *
    CM2_02 s * JB_02 s + (2 * CM2_03 s) / (s)

/-- Coefficient of `y₀^0 y₁^4` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_04 (s : ℝ) : ℝ := -CM2_13 s - T3_04 s + 2 * CM1_04 s + 2 * JA_04 s + 2 * JB_04 s + CM2_04 s
    * s + CM2_11 s * JA_03 s + CM2_12 s * JA_02 s + JA_04 s * s ^ 2 + JB_04 s * s + JB_04 s * s ^ 2
    - JA_04 s * s + 2 * CM2_02 s * JB_03 s + (2 * CM2_04 s) / (s) + 3 * CM2_03 s * JB_02 s

/-- Coefficient of `y₀^1 y₁^1` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_11 (s : ℝ) : ℝ := -T3_11 s - 2 * CM2_20 s + 2 * CM1_11 s + 2 * CM2_02 s + 2 * JA_11 s + 2 *
    JB_11 s + CM2_11 s * s + JA_11 s * s ^ 2 + JB_11 s * s + JB_11 s * s ^ 2 - JA_11 s * s + (2 *
    CM2_11 s) / (s)

/-- Coefficient of `y₀^1 y₁^2` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_12 (s : ℝ) : ℝ := -T3_12 s - 2 * CM2_21 s + 2 * CM1_12 s + 2 * JA_12 s + 2 * JB_12 s + 3 *
    CM2_03 s + CM2_11 s * JA_11 s + CM2_11 s * JB_02 s + CM2_12 s * s + JA_12 s * s ^ 2 + JB_12 s *
    s + JB_12 s * s ^ 2 - JA_12 s * s + 2 * CM2_02 s * JB_11 s + (2 * CM2_12 s) / (s) + 2 * CM2_20 s
    * JA_02 s

/-- Coefficient of `y₀^1 y₁^3` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_13 (s : ℝ) : ℝ := -T3_13 s - 2 * CM2_22 s + 2 * CM1_13 s + 2 * JA_13 s + 2 * JB_13 s + 4 *
    CM2_04 s + CM2_11 s * JA_12 s + CM2_11 s * JB_03 s + CM2_12 s * JA_11 s + CM2_13 s * s + JA_13 s
    * s ^ 2 + JB_13 s * s + JB_13 s * s ^ 2 - JA_13 s * s + 2 * CM2_02 s * JB_12 s + 2 * CM2_12 s *
    JB_02 s + (2 * CM2_13 s) / (s) + 2 * CM2_20 s * JA_03 s + 2 * CM2_21 s * JA_02 s + 3 * CM2_03 s
    * JB_11 s

/-- Coefficient of `y₀^2 y₁^0` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_20 (s : ℝ) : ℝ := CM2_11 s - T3_20 s + 2 * CM1_20 s + 2 * JA_20 s + 2 * JB_20 s + CM2_20 s
    * s + JA_20 s * s ^ 2 + JB_20 s * s + JB_20 s * s ^ 2 - JA_20 s * s + (2 * CM2_20 s) / (s)

/-- Coefficient of `y₀^2 y₁^1` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_21 (s : ℝ) : ℝ := -T3_21 s - 3 * CM2_30 s + 2 * CM1_21 s + 2 * CM2_12 s + 2 * JA_21 s + 2 *
    JB_21 s + CM2_11 s * JA_20 s + CM2_11 s * JB_11 s + CM2_21 s * s + JA_21 s * s ^ 2 + JB_21 s * s
    + JB_21 s * s ^ 2 - JA_21 s * s + 2 * CM2_02 s * JB_20 s + 2 * CM2_20 s * JA_11 s + (2 * CM2_21
    s) / (s)

/-- Coefficient of `y₀^2 y₁^2` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_22 (s : ℝ) : ℝ := -T3_22 s - 3 * CM2_31 s + 2 * CM1_22 s + 2 * JA_22 s + 2 * JB_22 s + 3 *
    CM2_13 s + CM2_11 s * JA_21 s + CM2_11 s * JB_12 s + CM2_12 s * JA_20 s + CM2_21 s * JB_02 s +
    CM2_22 s * s + JA_22 s * s ^ 2 + JB_22 s * s + JB_22 s * s ^ 2 - JA_22 s * s + 2 * CM2_02 s *
    JB_21 s + 2 * CM2_12 s * JB_11 s + 2 * CM2_20 s * JA_12 s + 2 * CM2_21 s * JA_11 s + (2 * CM2_22
    s) / (s) + 3 * CM2_03 s * JB_20 s + 3 * CM2_30 s * JA_02 s

/-- Coefficient of `y₀^3 y₁^0` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_30 (s : ℝ) : ℝ := CM2_21 s - T3_30 s + 2 * CM1_30 s + 2 * JA_30 s + 2 * JB_30 s + CM2_11 s
    * JB_20 s + CM2_30 s * s + JA_30 s * s ^ 2 + JB_30 s * s + JB_30 s * s ^ 2 - JA_30 s * s + 2 *
    CM2_20 s * JA_20 s + (2 * CM2_30 s) / (s)

/-- Coefficient of `y₀^3 y₁^1` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_31 (s : ℝ) : ℝ := -T3_31 s - 4 * CM2_40 s + 2 * CM1_31 s + 2 * CM2_22 s + 2 * JA_31 s + 2 *
    JB_31 s + CM2_11 s * JA_30 s + CM2_11 s * JB_21 s + CM2_21 s * JB_11 s + CM2_31 s * s + JA_31 s
    * s ^ 2 + JB_31 s * s + JB_31 s * s ^ 2 - JA_31 s * s + 2 * CM2_02 s * JB_30 s + 2 * CM2_12 s *
    JB_20 s + 2 * CM2_20 s * JA_21 s + 2 * CM2_21 s * JA_20 s + (2 * CM2_31 s) / (s) + 3 * CM2_30 s
    * JA_11 s

/-- Coefficient of `y₀^4 y₁^0` in the polynomial part of the invariance defect, component `3`. -/
def Hom3_40 (s : ℝ) : ℝ := CM2_31 s - T3_40 s + 2 * CM1_40 s + 2 * JA_40 s + 2 * JB_40 s + CM2_11 s
    * JB_30 s + CM2_21 s * JB_20 s + CM2_40 s * s + JA_40 s * s ^ 2 + JB_40 s * s + JB_40 s * s ^ 2
    - JA_40 s * s + 2 * CM2_20 s * JA_30 s + (2 * CM2_40 s) / (s) + 3 * CM2_30 s * JA_20 s

/-- The monomials of degree five and six of the polynomial part of the defect, component `2`. -/
def highD2 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [(CM1_21 s * JB_30 s + CM1_31 s * JB_20 s + 3 * CM1_30
    s * JA_30 s + 4 * CM1_40 s * JA_20 s, 5, 0, 0), (CM1_21 s * JB_21 s + CM1_31 s * JB_11 s + 2 *
    CM1_12 s * JB_30 s + 2 * CM1_21 s * JA_30 s + 2 * CM1_22 s * JB_20 s + 3 * CM1_30 s * JA_21 s +
    3 * CM1_31 s * JA_20 s + 4 * CM1_40 s * JA_11 s, 4, 1, 0), (CM1_12 s * JA_30 s + CM1_21 s *
    JB_12 s + CM1_31 s * JB_02 s + 2 * CM1_12 s * JB_21 s + 2 * CM1_21 s * JA_21 s + 2 * CM1_22 s *
    JA_20 s + 2 * CM1_22 s * JB_11 s + 3 * CM1_03 s * JB_30 s + 3 * CM1_13 s * JB_20 s + 3 * CM1_30
    s * JA_12 s + 3 * CM1_31 s * JA_11 s + 4 * CM1_40 s * JA_02 s, 3, 2, 0), (CM1_12 s * JA_21 s +
    CM1_13 s * JA_20 s + CM1_21 s * JB_03 s + 2 * CM1_12 s * JB_12 s + 2 * CM1_21 s * JA_12 s + 2 *
    CM1_22 s * JA_11 s + 2 * CM1_22 s * JB_02 s + 3 * CM1_03 s * JB_21 s + 3 * CM1_13 s * JB_11 s +
    3 * CM1_30 s * JA_03 s + 3 * CM1_31 s * JA_02 s + 4 * CM1_04 s * JB_20 s, 2, 3, 0), (CM1_12 s *
    JA_12 s + CM1_13 s * JA_11 s + 2 * CM1_12 s * JB_03 s + 2 * CM1_21 s * JA_03 s + 2 * CM1_22 s *
    JA_02 s + 3 * CM1_03 s * JB_12 s + 3 * CM1_13 s * JB_02 s + 4 * CM1_04 s * JB_11 s, 1, 4, 0),
    (CM1_12 s * JA_03 s + CM1_13 s * JA_02 s + 3 * CM1_03 s * JB_03 s + 4 * CM1_04 s * JB_02 s, 0,
    5, 0), (CM1_31 s * JB_30 s + 4 * CM1_40 s * JA_30 s, 6, 0, 0), (CM1_31 s * JB_21 s + 2 * CM1_22
    s * JB_30 s + 3 * CM1_31 s * JA_30 s + 4 * CM1_40 s * JA_21 s, 5, 1, 0), (CM1_31 s * JB_12 s + 2
    * CM1_22 s * JA_30 s + 2 * CM1_22 s * JB_21 s + 3 * CM1_13 s * JB_30 s + 3 * CM1_31 s * JA_21 s
    + 4 * CM1_40 s * JA_12 s, 4, 2, 0), (CM1_13 s * JA_30 s + CM1_31 s * JB_03 s + 2 * CM1_22 s *
    JA_21 s + 2 * CM1_22 s * JB_12 s + 3 * CM1_13 s * JB_21 s + 3 * CM1_31 s * JA_12 s + 4 * CM1_04
    s * JB_30 s + 4 * CM1_40 s * JA_03 s, 3, 3, 0), (CM1_13 s * JA_21 s + 2 * CM1_22 s * JA_12 s + 2
    * CM1_22 s * JB_03 s + 3 * CM1_13 s * JB_12 s + 3 * CM1_31 s * JA_03 s + 4 * CM1_04 s * JB_21 s,
    2, 4, 0), (CM1_13 s * JA_12 s + 2 * CM1_22 s * JA_03 s + 3 * CM1_13 s * JB_03 s + 4 * CM1_04 s *
    JB_12 s, 1, 5, 0), (CM1_13 s * JA_03 s + 4 * CM1_04 s * JB_03 s, 0, 6, 0)]

/-- The monomials of degree five and six of the polynomial part of the defect, component `3`. -/
def highD3 (s : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [(CM2_21 s * JB_30 s + CM2_31 s * JB_20 s + 3 * CM2_30
    s * JA_30 s + 4 * CM2_40 s * JA_20 s, 5, 0, 0), (CM2_21 s * JB_21 s + CM2_31 s * JB_11 s + 2 *
    CM2_12 s * JB_30 s + 2 * CM2_21 s * JA_30 s + 2 * CM2_22 s * JB_20 s + 3 * CM2_30 s * JA_21 s +
    3 * CM2_31 s * JA_20 s + 4 * CM2_40 s * JA_11 s, 4, 1, 0), (CM2_12 s * JA_30 s + CM2_21 s *
    JB_12 s + CM2_31 s * JB_02 s + 2 * CM2_12 s * JB_21 s + 2 * CM2_21 s * JA_21 s + 2 * CM2_22 s *
    JA_20 s + 2 * CM2_22 s * JB_11 s + 3 * CM2_03 s * JB_30 s + 3 * CM2_13 s * JB_20 s + 3 * CM2_30
    s * JA_12 s + 3 * CM2_31 s * JA_11 s + 4 * CM2_40 s * JA_02 s, 3, 2, 0), (CM2_12 s * JA_21 s +
    CM2_13 s * JA_20 s + CM2_21 s * JB_03 s + 2 * CM2_12 s * JB_12 s + 2 * CM2_21 s * JA_12 s + 2 *
    CM2_22 s * JA_11 s + 2 * CM2_22 s * JB_02 s + 3 * CM2_03 s * JB_21 s + 3 * CM2_13 s * JB_11 s +
    3 * CM2_30 s * JA_03 s + 3 * CM2_31 s * JA_02 s + 4 * CM2_04 s * JB_20 s, 2, 3, 0), (CM2_12 s *
    JA_12 s + CM2_13 s * JA_11 s + 2 * CM2_12 s * JB_03 s + 2 * CM2_21 s * JA_03 s + 2 * CM2_22 s *
    JA_02 s + 3 * CM2_03 s * JB_12 s + 3 * CM2_13 s * JB_02 s + 4 * CM2_04 s * JB_11 s, 1, 4, 0),
    (CM2_12 s * JA_03 s + CM2_13 s * JA_02 s + 3 * CM2_03 s * JB_03 s + 4 * CM2_04 s * JB_02 s, 0,
    5, 0), (CM2_31 s * JB_30 s + 4 * CM2_40 s * JA_30 s, 6, 0, 0), (CM2_31 s * JB_21 s + 2 * CM2_22
    s * JB_30 s + 3 * CM2_31 s * JA_30 s + 4 * CM2_40 s * JA_21 s, 5, 1, 0), (CM2_31 s * JB_12 s + 2
    * CM2_22 s * JA_30 s + 2 * CM2_22 s * JB_21 s + 3 * CM2_13 s * JB_30 s + 3 * CM2_31 s * JA_21 s
    + 4 * CM2_40 s * JA_12 s, 4, 2, 0), (CM2_13 s * JA_30 s + CM2_31 s * JB_03 s + 2 * CM2_22 s *
    JA_21 s + 2 * CM2_22 s * JB_12 s + 3 * CM2_13 s * JB_21 s + 3 * CM2_31 s * JA_12 s + 4 * CM2_04
    s * JB_30 s + 4 * CM2_40 s * JA_03 s, 3, 3, 0), (CM2_13 s * JA_21 s + 2 * CM2_22 s * JA_12 s + 2
    * CM2_22 s * JB_03 s + 3 * CM2_13 s * JB_12 s + 3 * CM2_31 s * JA_03 s + 4 * CM2_04 s * JB_21 s,
    2, 4, 0), (CM2_13 s * JA_12 s + 2 * CM2_22 s * JA_03 s + 3 * CM2_13 s * JB_03 s + 4 * CM2_04 s *
    JB_12 s, 1, 5, 0), (CM2_13 s * JA_03 s + 4 * CM2_04 s * JB_03 s, 0, 6, 0)]

/-! ## Certificates -/

/-- `PV0_0` is `Re p_0 + Im p_0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV0_0_eq {s : ℝ} (hs : 0 < s) :
    PV0_0 s = (bautinPathP s 0).re + (bautinPathP s 0).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV0_0, nPV0_0, ePV0_0, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- `PV1_0` is `Re p_0 − Im p_0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV1_0_eq {s : ℝ} (hs : 0 < s) :
    PV1_0 s = (bautinPathP s 0).re - (bautinPathP s 0).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV1_0, nPV1_0, ePV1_0, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- `PV0_1` is `Re p_1 + Im p_1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV0_1_eq {s : ℝ} (hs : 0 < s) :
    PV0_1 s = (bautinPathP s 1).re + (bautinPathP s 1).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV0_1, nPV0_1, ePV0_1, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- `PV1_1` is `Re p_1 − Im p_1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV1_1_eq {s : ℝ} (hs : 0 < s) :
    PV1_1 s = (bautinPathP s 1).re - (bautinPathP s 1).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV1_1, nPV1_1, ePV1_1, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- `PV0_2` is `Re p_2 + Im p_2`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV0_2_eq {s : ℝ} (hs : 0 < s) :
    PV0_2 s = (bautinPathP s 2).re + (bautinPathP s 2).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV0_2, nPV0_2, ePV0_2, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- `PV1_2` is `Re p_2 − Im p_2`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV1_2_eq {s : ℝ} (hs : 0 < s) :
    PV1_2 s = (bautinPathP s 2).re - (bautinPathP s 2).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV1_2, nPV1_2, ePV1_2, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- `PV0_3` is `Re p_3 + Im p_3`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV0_3_eq {s : ℝ} (hs : 0 < s) :
    PV0_3 s = (bautinPathP s 3).re + (bautinPathP s 3).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV0_3, nPV0_3, ePV0_3, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- `PV1_3` is `Re p_3 − Im p_3`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem PV1_3_eq {s : ℝ} (hs : 0 < s) :
    PV1_3 s = (bautinPathP s 3).re - (bautinPathP s 3).im := by
  have h1 : bautinDen1 s ≠ 0 := by unfold bautinDen1; positivity
  have h4 : s ^ 2 + 4 ≠ 0 := by positivity
  simp only [PV1_3, nPV1_3, ePV1_3, zeval, bval, bases]
  simp only [bautinPathP, bautinDen1] at h1 ⊢
  simp [-Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

/-- The certificate expression of `DETV_eq`. -/
def cDETV_eq : PExpr := (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nPV1_0
    ePV1_0)) (.mul (.mul (.atom [1] []) (.atom nPV0_0 ePV0_0)) (.atom nPV1_1 ePV1_1))) (.mul (.atom
    [-1] []) (.atom nDETV eDETV)))

@[tmio M, powerlib_domain] theorem DETV_eq {s : ℝ} (hs : 0 < s) :
    PV0_0 s * PV1_1 s - PV0_1 s * PV1_0 s = DETV s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cDETV_eq (by decide +kernel)
  simp only [cDETV_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [DETV, PV0_0, PV0_1, PV1_0, PV1_1]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `piw1_0`. -/
def cpiw1_0 : PExpr := (.add (.add (.add (.mul (.atom [1] []) (.atom nPV0_2 ePV0_2)) (.mul (.atom
    [0, 1] []) (.atom nPV0_1 ePV0_1))) (.mul (.atom [4] [0, 0, 0, 1]) (.atom nPV0_1 ePV0_1))) (.mul
    (.atom [-1] []) (.atom nPV0_0 ePV0_0)))

@[tmio M, powerlib_domain] theorem piw1_0 {s : ℝ} (hs : 0 < s) :
    PV0_2 s - PV0_0 s + PV0_1 s * s + (4 * PV0_1 s) / (s) = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cpiw1_0 (by decide +kernel)
  simp only [cpiw1_0, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [PV0_0, PV0_1, PV0_2]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `piw1_1`. -/
def cpiw1_1 : PExpr := (.add (.add (.add (.mul (.atom [1] []) (.atom nPV1_2 ePV1_2)) (.mul (.atom
    [0, 1] []) (.atom nPV1_1 ePV1_1))) (.mul (.atom [4] [0, 0, 0, 1]) (.atom nPV1_1 ePV1_1))) (.mul
    (.atom [-1] []) (.atom nPV1_0 ePV1_0)))

@[tmio M, powerlib_domain] theorem piw1_1 {s : ℝ} (hs : 0 < s) :
    PV1_2 s - PV1_0 s + PV1_1 s * s + (4 * PV1_1 s) / (s) = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cpiw1_1 (by decide +kernel)
  simp only [cpiw1_1, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [PV1_0, PV1_1, PV1_2]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `piw2_0`. -/
def cpiw2_0 : PExpr := (.add (.add (.add (.mul (.atom [1] []) (.atom nPV0_3 ePV0_3)) (.mul (.atom
    [1] []) (.atom nPV0_1 ePV0_1))) (.mul (.atom [4] [0, 0, 0, 2]) (.atom nPV0_1 ePV0_1))) (.mul
    (.atom [-2] [0, 0, 0, 1]) (.atom nPV0_0 ePV0_0)))

@[tmio M, powerlib_domain] theorem piw2_0 {s : ℝ} (hs : 0 < s) :
    PV0_1 s + PV0_3 s + (-2 * PV0_0 s) / (s) + (4 * PV0_1 s) / (s ^ 2) = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cpiw2_0 (by decide +kernel)
  simp only [cpiw2_0, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [PV0_0, PV0_1, PV0_3]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `piw2_1`. -/
def cpiw2_1 : PExpr := (.add (.add (.add (.mul (.atom [1] []) (.atom nPV1_3 ePV1_3)) (.mul (.atom
    [1] []) (.atom nPV1_1 ePV1_1))) (.mul (.atom [4] [0, 0, 0, 2]) (.atom nPV1_1 ePV1_1))) (.mul
    (.atom [-2] [0, 0, 0, 1]) (.atom nPV1_0 ePV1_0)))

@[tmio M, powerlib_domain] theorem piw2_1 {s : ℝ} (hs : 0 < s) :
    PV1_1 s + PV1_3 s + (-2 * PV1_0 s) / (s) + (4 * PV1_1 s) / (s ^ 2) = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cpiw2_1 (by decide +kernel)
  simp only [cpiw2_1, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [PV1_0, PV1_1, PV1_3]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_20_eq`. -/
def cCA_20_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_20 eCM2_20)) (.mul
    (.atom [1] []) (.atom nCM1_20 eCM1_20))) (.mul (.atom [1] []) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem CA_20_eq {s : ℝ} (hs : 0 < s) :
    CA_20 s = -CM1_20 s - 2 / s * CM2_20 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_20_eq (by decide +kernel)
  simp only [cCA_20_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_20, CM1_20, CM2_20]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_11_eq`. -/
def cCA_11_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_11 eCM2_11)) (.mul
    (.atom [1] []) (.atom nCM1_11 eCM1_11))) (.mul (.atom [1] []) (.atom nCA_11 eCA_11)))

@[tmio M, powerlib_domain] theorem CA_11_eq {s : ℝ} (hs : 0 < s) :
    CA_11 s = -CM1_11 s - 2 / s * CM2_11 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_11_eq (by decide +kernel)
  simp only [cCA_11_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_11, CM1_11, CM2_11]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_02_eq`. -/
def cCA_02_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_02 eCM2_02)) (.mul
    (.atom [1] []) (.atom nCM1_02 eCM1_02))) (.mul (.atom [1] []) (.atom nCA_02 eCA_02)))

@[tmio M, powerlib_domain] theorem CA_02_eq {s : ℝ} (hs : 0 < s) :
    CA_02 s = -CM1_02 s - 2 / s * CM2_02 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_02_eq (by decide +kernel)
  simp only [cCA_02_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_02, CM1_02, CM2_02]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_30_eq`. -/
def cCA_30_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_30 eCM2_30)) (.mul
    (.atom [1] []) (.atom nCM1_30 eCM1_30))) (.mul (.atom [1] []) (.atom nCA_30 eCA_30)))

@[tmio M, powerlib_domain] theorem CA_30_eq {s : ℝ} (hs : 0 < s) :
    CA_30 s = -CM1_30 s - 2 / s * CM2_30 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_30_eq (by decide +kernel)
  simp only [cCA_30_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_30, CM1_30, CM2_30]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_21_eq`. -/
def cCA_21_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_21 eCM2_21)) (.mul
    (.atom [1] []) (.atom nCM1_21 eCM1_21))) (.mul (.atom [1] []) (.atom nCA_21 eCA_21)))

@[tmio M, powerlib_domain] theorem CA_21_eq {s : ℝ} (hs : 0 < s) :
    CA_21 s = -CM1_21 s - 2 / s * CM2_21 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_21_eq (by decide +kernel)
  simp only [cCA_21_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_21, CM1_21, CM2_21]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_12_eq`. -/
def cCA_12_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_12 eCM2_12)) (.mul
    (.atom [1] []) (.atom nCM1_12 eCM1_12))) (.mul (.atom [1] []) (.atom nCA_12 eCA_12)))

@[tmio M, powerlib_domain] theorem CA_12_eq {s : ℝ} (hs : 0 < s) :
    CA_12 s = -CM1_12 s - 2 / s * CM2_12 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_12_eq (by decide +kernel)
  simp only [cCA_12_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_12, CM1_12, CM2_12]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_03_eq`. -/
def cCA_03_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_03 eCM2_03)) (.mul
    (.atom [1] []) (.atom nCM1_03 eCM1_03))) (.mul (.atom [1] []) (.atom nCA_03 eCA_03)))

@[tmio M, powerlib_domain] theorem CA_03_eq {s : ℝ} (hs : 0 < s) :
    CA_03 s = -CM1_03 s - 2 / s * CM2_03 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_03_eq (by decide +kernel)
  simp only [cCA_03_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_03, CM1_03, CM2_03]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_40_eq`. -/
def cCA_40_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_40 eCM2_40)) (.mul
    (.atom [1] []) (.atom nCM1_40 eCM1_40))) (.mul (.atom [1] []) (.atom nCA_40 eCA_40)))

@[tmio M, powerlib_domain] theorem CA_40_eq {s : ℝ} (hs : 0 < s) :
    CA_40 s = -CM1_40 s - 2 / s * CM2_40 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_40_eq (by decide +kernel)
  simp only [cCA_40_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_40, CM1_40, CM2_40]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_31_eq`. -/
def cCA_31_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_31 eCM2_31)) (.mul
    (.atom [1] []) (.atom nCM1_31 eCM1_31))) (.mul (.atom [1] []) (.atom nCA_31 eCA_31)))

@[tmio M, powerlib_domain] theorem CA_31_eq {s : ℝ} (hs : 0 < s) :
    CA_31 s = -CM1_31 s - 2 / s * CM2_31 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_31_eq (by decide +kernel)
  simp only [cCA_31_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_31, CM1_31, CM2_31]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_22_eq`. -/
def cCA_22_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_22 eCM2_22)) (.mul
    (.atom [1] []) (.atom nCM1_22 eCM1_22))) (.mul (.atom [1] []) (.atom nCA_22 eCA_22)))

@[tmio M, powerlib_domain] theorem CA_22_eq {s : ℝ} (hs : 0 < s) :
    CA_22 s = -CM1_22 s - 2 / s * CM2_22 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_22_eq (by decide +kernel)
  simp only [cCA_22_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_22, CM1_22, CM2_22]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_13_eq`. -/
def cCA_13_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_13 eCM2_13)) (.mul
    (.atom [1] []) (.atom nCM1_13 eCM1_13))) (.mul (.atom [1] []) (.atom nCA_13 eCA_13)))

@[tmio M, powerlib_domain] theorem CA_13_eq {s : ℝ} (hs : 0 < s) :
    CA_13 s = -CM1_13 s - 2 / s * CM2_13 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_13_eq (by decide +kernel)
  simp only [cCA_13_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_13, CM1_13, CM2_13]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `CA_04_eq`. -/
def cCA_04_eq : PExpr := (.add (.add (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_04 eCM2_04)) (.mul
    (.atom [1] []) (.atom nCM1_04 eCM1_04))) (.mul (.atom [1] []) (.atom nCA_04 eCA_04)))

@[tmio M, powerlib_domain] theorem CA_04_eq {s : ℝ} (hs : 0 < s) :
    CA_04 s = -CM1_04 s - 2 / s * CM2_04 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cCA_04_eq (by decide +kernel)
  simp only [cCA_04_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CA_04, CM1_04, CM2_04]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T1_02_val`. -/
def cT1_02_val : PExpr := (.add (.atom [0, -32, -16, -32, -8, -10, -1, -1] []) (.mul (.atom [-1] [])
    (.atom nTV1_02 eTV1_02)))

@[tmio M, powerlib_domain] theorem T1_02_val {s : ℝ} (hs : 0 < s) :
    T1_02 s = TV1_02 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_02_val (by decide +kernel)
  simp only [cT1_02_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l3_02, T1_02, TV1_02]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T1_03_val`. -/
def cT1_03_val : PExpr := (.add (.add (.add (.atom [0, 0, 128, 64, 96, 48, 24, 12, 2, 1] []) (.mul
    (.atom [-2] []) (.atom nTV1_03 eTV1_03))) (.mul (.atom [0, -32, 0, -16, 0, -2] []) (.atom
    nCM2_02 eCM2_02))) (.mul (.atom [-16, -8, -12, -2, -2] []) (.atom nCA_02 eCA_02)))

@[tmio M, powerlib_domain] theorem T1_03_val {s : ℝ} (hs : 0 < s) :
    T1_03 s = TV1_03 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_03_val (by decide +kernel)
  simp only [cT1_03_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CM2_02, Sa2_l3_03, Sc2_l0_03, Sl0_l0_l2_03, T1_03, TV1_03]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T1_04_val`. -/
def cT1_04_val : PExpr := (.add (.add (.add (.add (.add (.add (.atom [0, 0, 0, 512, 256, 768, 256,
    448, 96, 128, 16, 18, 1, 1] []) (.mul (.atom [-6] []) (.atom nTV1_04 eTV1_04))) (.mul (.atom [0,
    -96, 0, -48, 0, -6] []) (.atom nCM2_03 eCM2_03))) (.mul (.atom [0, 0, 192, 0, 144, 0, 36, 0, 3]
    []) (.atom nCM1_02 eCM1_02))) (.mul (.atom [-48, -24, -36, -6, -6] []) (.atom nCA_03 eCA_03)))
    (.mul (.atom [0, 192, 96, 96, 48, 12, 6] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-24, 0,
    -6] []) (.atom nCA_02 eCA_02)) (.atom nCM2_02 eCM2_02)))

@[tmio M, powerlib_domain] theorem T1_04_val {s : ℝ} (hs : 0 < s) :
    T1_04 s = TV1_04 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_04_val (by decide +kernel)
  simp only [cT1_04_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CM1_02, CM2_02, CM2_03, Sa2_c2_04, Sa2_l0_l2_04, Sa3_l3_04, Sb2_l0_l0_04,
    Sc3_l0_04, Sl0_l0_l0_l3_04, T1_04, TV1_04]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T1_05_val`. -/
def cT1_05_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.atom
    [0, 0, 0, 0, -2048, -1024, -2560, -1280, -1280, -640, -320, -160, -40, -20, -2, -1] []) (.mul
    (.atom [-24] []) (.atom nTV1_05 eTV1_05))) (.mul (.atom [0, -384, 0, -192, 0, -24] []) (.atom
    nCM2_04 eCM2_04))) (.mul (.atom [0, 0, 0, 1024, 0, 1024, 0, 384, 0, 64, 0, 4] []) (.atom nCM2_02
    eCM2_02))) (.mul (.atom [0, 0, 768, 0, 576, 0, 144, 0, 12] []) (.atom nCM1_03 eCM1_03))) (.mul
    (.atom [-192, -96, -144, -24, -24] []) (.atom nCA_04 eCA_04))) (.mul (.atom [0, 768, 384, 384,
    192, 48, 24] []) (.atom nCA_03 eCA_03))) (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_03
    eCA_03)) (.atom nCM2_02 eCM2_02))) (.mul (.atom [0, 0, 1536, 768, 1920, 576, 864, 144, 168, 12,
    12] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_02 eCA_02))
    (.atom nCM2_03 eCM2_03))) (.mul (.mul (.atom [0, 384, 0, 192, 0, 24] []) (.atom nCA_02 eCA_02))
    (.atom nCM1_02 eCM1_02))) (.mul (.atom [96, 48, 24, 12] []) (.pow (.atom nCA_02 eCA_02) 2)))

@[tmio M, powerlib_domain] theorem T1_05_val {s : ℝ} (hs : 0 < s) :
    T1_05 s = TV1_05 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_05_val (by decide +kernel)
  simp only [cT1_05_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_04, CM1_02, CM1_03, CM2_02, CM2_03, CM2_04, Sa2_a2_l2_05,
    Sa2_b2_l0_05, Sa2_c3_05, Sa2_l0_l0_l3_05, Sa3_c2_05, Sa3_l0_l2_05, Sa4_l3_05, Sb3_l0_l0_05,
    Sc2_l0_l0_l0_05, Sc4_l0_05, Sl0_l0_l0_l0_l2_05, T1_05, TV1_05]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T1_11_val`. -/
def cT1_11_val : PExpr := (.add (.atom [0, -64, 0, -64, 0, -20, 0, -2] []) (.mul (.atom [-1] [])
    (.atom nTV1_11 eTV1_11)))

@[tmio M, powerlib_domain] theorem T1_11_val {s : ℝ} (hs : 0 < s) :
    T1_11 s = TV1_11 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_11_val (by decide +kernel)
  simp only [cT1_11_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l3_11, T1_11, TV1_11]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T1_12_val`. -/
def cT1_12_val : PExpr := (.add (.add (.add (.add (.add (.atom [0, 0, 128, 192, 96, 144, 24, 36, 2,
    3] []) (.mul (.atom [-2] []) (.atom nTV1_12 eTV1_12))) (.mul (.atom [0, -32, 0, -16, 0, -2] [])
    (.atom nCM2_11 eCM2_11))) (.mul (.atom [0, -32, 0, -16, 0, -2] []) (.atom nCM2_02 eCM2_02)))
    (.mul (.atom [-16, -8, -12, -2, -2] []) (.atom nCA_11 eCA_11))) (.mul (.atom [-16, 8, -12, 2,
    -2] []) (.atom nCA_02 eCA_02)))

@[tmio M, powerlib_domain] theorem T1_12_val {s : ℝ} (hs : 0 < s) :
    T1_12 s = TV1_12 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_12_val (by decide +kernel)
  simp only [cT1_12_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, CM2_02, CM2_11, Sa2_l3_12, Sc2_l0_12, Sl0_l0_l2_12, T1_12, TV1_12]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T1_13_val`. -/
def cT1_13_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.atom
    [0, 0, 0, 2048, 512, 3072, 512, 1792, 192, 512, 32, 72, 2, 4] []) (.mul (.atom [-6] []) (.atom
    nTV1_13 eTV1_13))) (.mul (.atom [0, -96, 0, -48, 0, -6] []) (.atom nCM2_12 eCM2_12))) (.mul
    (.atom [0, -96, 0, -48, 0, -6] []) (.atom nCM2_03 eCM2_03))) (.mul (.atom [0, 0, 192, 0, 144, 0,
    36, 0, 3] []) (.atom nCM1_11 eCM1_11))) (.mul (.atom [0, 0, 384, 0, 288, 0, 72, 0, 6] []) (.atom
    nCM1_02 eCM1_02))) (.mul (.atom [-48, -24, -36, -6, -6] []) (.atom nCA_12 eCA_12))) (.mul (.atom
    [0, 192, 96, 96, 48, 12, 6] []) (.atom nCA_11 eCA_11))) (.mul (.mul (.atom [-24, 0, -6] [])
    (.atom nCA_11 eCA_11)) (.atom nCM2_02 eCM2_02))) (.mul (.atom [-48, 24, -36, 6, -6] []) (.atom
    nCA_03 eCA_03))) (.mul (.atom [0, 0, 192, 0, 96, 0, 12] []) (.atom nCA_02 eCA_02))) (.mul (.mul
    (.atom [-24, 0, -6] []) (.atom nCA_02 eCA_02)) (.atom nCM2_11 eCM2_11)))

@[tmio M, powerlib_domain] theorem T1_13_val {s : ℝ} (hs : 0 < s) :
    T1_13 s = TV1_13 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_13_val (by decide +kernel)
  simp only [cT1_13_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_11, CA_12, CM1_02, CM1_11, CM2_02, CM2_03, CM2_11, CM2_12, Sa2_c2_13,
    Sa2_l0_l2_13, Sa3_l3_13, Sb2_l0_l0_13, Sc3_l0_13, Sl0_l0_l0_l3_13, T1_13, TV1_13]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T1_14_val`. -/
def cT1_14_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.atom [0, 0, 0, 0, -6144, -5120,
    -7680, -6400, -3840, -3200, -960, -800, -120, -100, -6, -5] []) (.mul (.atom [-24] []) (.atom
    nTV1_14 eTV1_14))) (.mul (.atom [0, -384, 0, -192, 0, -24] []) (.atom nCM2_13 eCM2_13))) (.mul
    (.atom [0, 0, 0, 1024, 0, 1024, 0, 384, 0, 64, 0, 4] []) (.atom nCM2_11 eCM2_11))) (.mul (.atom
    [0, -384, 0, -192, 0, -24] []) (.atom nCM2_04 eCM2_04))) (.mul (.atom [0, 0, 0, 3072, 0, 3072,
    0, 1152, 0, 192, 0, 12] []) (.atom nCM2_02 eCM2_02))) (.mul (.atom [0, 0, 768, 0, 576, 0, 144,
    0, 12] []) (.atom nCM1_12 eCM1_12))) (.mul (.atom [0, 0, 1536, 0, 1152, 0, 288, 0, 24] [])
    (.atom nCM1_03 eCM1_03))) (.mul (.atom [-192, -96, -144, -24, -24] []) (.atom nCA_13 eCA_13)))
    (.mul (.atom [0, 768, 384, 384, 192, 48, 24] []) (.atom nCA_12 eCA_12))) (.mul (.mul (.atom
    [-96, 0, -24] []) (.atom nCA_12 eCA_12)) (.atom nCM2_02 eCM2_02))) (.mul (.atom [0, 0, 1536,
    768, 1920, 576, 864, 144, 168, 12, 12] []) (.atom nCA_11 eCA_11))) (.mul (.mul (.atom [-96, 0,
    -24] []) (.atom nCA_11 eCA_11)) (.atom nCM2_03 eCM2_03))) (.mul (.mul (.atom [0, 384, 0, 192, 0,
    24] []) (.atom nCA_11 eCA_11)) (.atom nCM1_02 eCM1_02))) (.mul (.atom [-192, 96, -144, 24, -24]
    []) (.atom nCA_04 eCA_04))) (.mul (.atom [0, 0, 768, 0, 384, 0, 48] []) (.atom nCA_03 eCA_03)))
    (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_03 eCA_03)) (.atom nCM2_11 eCM2_11))) (.mul
    (.atom [0, 0, 4608, 768, 5760, 576, 2592, 144, 504, 12, 36] []) (.atom nCA_02 eCA_02))) (.mul
    (.mul (.atom [-96, 0, -24] []) (.atom nCA_02 eCA_02)) (.atom nCM2_12 eCM2_12))) (.mul (.mul
    (.atom [0, 384, 0, 192, 0, 24] []) (.atom nCA_02 eCA_02)) (.atom nCM1_11 eCM1_11))) (.mul (.mul
    (.atom [0, 384, 0, 192, 0, 24] []) (.atom nCA_02 eCA_02)) (.atom nCM1_02 eCM1_02))) (.mul (.mul
    (.atom [192, 96, 48, 24] []) (.atom nCA_02 eCA_02)) (.atom nCA_11 eCA_11))) (.mul (.atom [-96,
    48, -24, 12] []) (.pow (.atom nCA_02 eCA_02) 2)))

@[tmio M, powerlib_domain] theorem T1_14_val {s : ℝ} (hs : 0 < s) :
    T1_14 s = TV1_14 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_14_val (by decide +kernel)
  simp only [cT1_14_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_04, CA_11, CA_12, CA_13, CM1_02, CM1_03, CM1_11, CM1_12, CM2_02,
    CM2_03, CM2_04, CM2_11, CM2_12, CM2_13, Sa2_a2_l2_14, Sa2_b2_l0_14, Sa2_c3_14, Sa2_l0_l0_l3_14,
    Sa3_c2_14, Sa3_l0_l2_14, Sa4_l3_14, Sb3_l0_l0_14, Sc2_l0_l0_l0_14, Sc4_l0_14,
    Sl0_l0_l0_l0_l2_14, T1_14, TV1_14]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T1_20_val`. -/
def cT1_20_val : PExpr := (.add (.atom [0, -32, 16, -32, 8, -10, 1, -1] []) (.mul (.atom [-1] [])
    (.atom nTV1_20 eTV1_20)))

@[tmio M, powerlib_domain] theorem T1_20_val {s : ℝ} (hs : 0 < s) :
    T1_20 s = TV1_20 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_20_val (by decide +kernel)
  simp only [cT1_20_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l3_20, T1_20, TV1_20]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T1_21_val`. -/
def cT1_21_val : PExpr := (.add (.add (.add (.add (.add (.atom [0, 0, -128, 192, -96, 144, -24, 36,
    -2, 3] []) (.mul (.atom [-2] []) (.atom nTV1_21 eTV1_21))) (.mul (.atom [0, -32, 0, -16, 0, -2]
    []) (.atom nCM2_20 eCM2_20))) (.mul (.atom [0, -32, 0, -16, 0, -2] []) (.atom nCM2_11 eCM2_11)))
    (.mul (.atom [-16, -8, -12, -2, -2] []) (.atom nCA_20 eCA_20))) (.mul (.atom [-16, 8, -12, 2,
    -2] []) (.atom nCA_11 eCA_11)))

@[tmio M, powerlib_domain] theorem T1_21_val {s : ℝ} (hs : 0 < s) :
    T1_21 s = TV1_21 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_21_val (by decide +kernel)
  simp only [cT1_21_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, CM2_11, CM2_20, Sa2_l3_21, Sc2_l0_21, Sl0_l0_l2_21, T1_21, TV1_21]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T1_22_val`. -/
def cT1_22_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.atom [0, 0, 0, 1024, 0, 1536, 0, 896, 0, 256, 0, 36, 0, 2] []) (.mul (.atom [-2]
    []) (.atom nTV1_22 eTV1_22))) (.mul (.atom [0, -32, 0, -16, 0, -2] []) (.atom nCM2_21 eCM2_21)))
    (.mul (.atom [0, -32, 0, -16, 0, -2] []) (.atom nCM2_12 eCM2_12))) (.mul (.atom [0, 0, 64, 0,
    48, 0, 12, 0, 1] []) (.atom nCM1_20 eCM1_20))) (.mul (.atom [0, 0, 128, 0, 96, 0, 24, 0, 2] [])
    (.atom nCM1_11 eCM1_11))) (.mul (.atom [0, 0, 64, 0, 48, 0, 12, 0, 1] []) (.atom nCM1_02
    eCM1_02))) (.mul (.atom [-16, -8, -12, -2, -2] []) (.atom nCA_21 eCA_21))) (.mul (.atom [0, 64,
    32, 32, 16, 4, 2] []) (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-8, 0, -2] []) (.atom nCA_20
    eCA_20)) (.atom nCM2_02 eCM2_02))) (.mul (.atom [-16, 8, -12, 2, -2] []) (.atom nCA_12 eCA_12)))
    (.mul (.atom [0, 0, 64, 0, 32, 0, 4] []) (.atom nCA_11 eCA_11))) (.mul (.mul (.atom [-8, 0, -2]
    []) (.atom nCA_11 eCA_11)) (.atom nCM2_11 eCM2_11))) (.mul (.atom [0, -64, 32, -32, 16, -4, 2]
    []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-8, 0, -2] []) (.atom nCA_02 eCA_02)) (.atom
    nCM2_20 eCM2_20)))

@[tmio M, powerlib_domain] theorem T1_22_val {s : ℝ} (hs : 0 < s) :
    T1_22 s = TV1_22 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_22_val (by decide +kernel)
  simp only [cT1_22_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, CA_12, CA_20, CA_21, CM1_02, CM1_11, CM1_20, CM2_02, CM2_11, CM2_12,
    CM2_20, CM2_21, Sa2_c2_22, Sa2_l0_l2_22, Sa3_l3_22, Sb2_l0_l0_22, Sc3_l0_22, Sl0_l0_l0_l3_22,
    T1_22, TV1_22]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T1_23_val`. -/
def cT1_23_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.atom [0, 0, 0, 0, -2048, -5120, -2560, -6400, -1280, -3200, -320, -800, -40,
    -100, -2, -5] []) (.mul (.atom [-12] []) (.atom nTV1_23 eTV1_23))) (.mul (.atom [0, -192, 0,
    -96, 0, -12] []) (.atom nCM2_22 eCM2_22))) (.mul (.atom [0, 0, 0, 512, 0, 512, 0, 192, 0, 32, 0,
    2] []) (.atom nCM2_20 eCM2_20))) (.mul (.atom [0, -192, 0, -96, 0, -12] []) (.atom nCM2_13
    eCM2_13))) (.mul (.atom [0, 0, 0, 1536, 0, 1536, 0, 576, 0, 96, 0, 6] []) (.atom nCM2_11
    eCM2_11))) (.mul (.atom [0, 0, 0, 1536, 0, 1536, 0, 576, 0, 96, 0, 6] []) (.atom nCM2_02
    eCM2_02))) (.mul (.atom [0, 0, 384, 0, 288, 0, 72, 0, 6] []) (.atom nCM1_21 eCM1_21))) (.mul
    (.atom [0, 0, 768, 0, 576, 0, 144, 0, 12] []) (.atom nCM1_12 eCM1_12))) (.mul (.atom [0, 0, 384,
    0, 288, 0, 72, 0, 6] []) (.atom nCM1_03 eCM1_03))) (.mul (.atom [-96, -48, -72, -12, -12] [])
    (.atom nCA_22 eCA_22))) (.mul (.atom [0, 384, 192, 192, 96, 24, 12] []) (.atom nCA_21 eCA_21)))
    (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_21 eCA_21)) (.atom nCM2_02 eCM2_02))) (.mul
    (.atom [0, 0, 768, 384, 960, 288, 432, 72, 84, 6, 6] []) (.atom nCA_20 eCA_20))) (.mul (.mul
    (.atom [-48, 0, -12] []) (.atom nCA_20 eCA_20)) (.atom nCM2_03 eCM2_03))) (.mul (.mul (.atom [0,
    192, 0, 96, 0, 12] []) (.atom nCA_20 eCA_20)) (.atom nCM1_02 eCM1_02))) (.mul (.atom [-96, 48,
    -72, 12, -12] []) (.atom nCA_13 eCA_13))) (.mul (.atom [0, 0, 384, 0, 192, 0, 24] []) (.atom
    nCA_12 eCA_12))) (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_12 eCA_12)) (.atom nCM2_11
    eCM2_11))) (.mul (.atom [0, 0, 2304, 384, 2880, 288, 1296, 72, 252, 6, 18] []) (.atom nCA_11
    eCA_11))) (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_11 eCA_11)) (.atom nCM2_12 eCM2_12)))
    (.mul (.mul (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_11 eCA_11)) (.atom nCM1_11 eCM1_11)))
    (.mul (.mul (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_11 eCA_11)) (.atom nCM1_02 eCM1_02)))
    (.mul (.atom [48, 24, 12, 6] []) (.pow (.atom nCA_11 eCA_11) 2))) (.mul (.atom [0, -384, 192,
    -192, 96, -24, 12] []) (.atom nCA_03 eCA_03))) (.mul (.mul (.atom [-48, 0, -12] []) (.atom
    nCA_03 eCA_03)) (.atom nCM2_20 eCM2_20))) (.mul (.atom [0, 0, 2304, -384, 2880, -288, 1296, -72,
    252, -6, 18] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_02
    eCA_02)) (.atom nCM2_21 eCM2_21))) (.mul (.mul (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_02
    eCA_02)) (.atom nCM1_20 eCM1_20))) (.mul (.mul (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_02
    eCA_02)) (.atom nCM1_11 eCM1_11))) (.mul (.mul (.atom [96, 48, 24, 12] []) (.atom nCA_02
    eCA_02)) (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-96, 48, -24, 12] []) (.atom nCA_02
    eCA_02)) (.atom nCA_11 eCA_11)))

@[tmio M, powerlib_domain] theorem T1_23_val {s : ℝ} (hs : 0 < s) :
    T1_23 s = TV1_23 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_23_val (by decide +kernel)
  simp only [cT1_23_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_11, CA_12, CA_13, CA_20, CA_21, CA_22, CM1_02, CM1_03, CM1_11, CM1_12,
    CM1_20, CM1_21, CM2_02, CM2_03, CM2_11, CM2_12, CM2_13, CM2_20, CM2_21, CM2_22, Sa2_a2_l2_23,
    Sa2_b2_l0_23, Sa2_c3_23, Sa2_l0_l0_l3_23, Sa3_c2_23, Sa3_l0_l2_23, Sa4_l3_23, Sb3_l0_l0_23,
    Sc2_l0_l0_l0_23, Sc4_l0_23, Sl0_l0_l0_l0_l2_23, T1_23, TV1_23]
  linear_combination (1 / 12 : ℝ) * h

/-- The certificate expression of `T1_30_val`. -/
def cT1_30_val : PExpr := (.add (.add (.add (.atom [0, 0, -128, 64, -96, 48, -24, 12, -2, 1] [])
    (.mul (.atom [-2] []) (.atom nTV1_30 eTV1_30))) (.mul (.atom [0, -32, 0, -16, 0, -2] []) (.atom
    nCM2_20 eCM2_20))) (.mul (.atom [-16, 8, -12, 2, -2] []) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T1_30_val {s : ℝ} (hs : 0 < s) :
    T1_30 s = TV1_30 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_30_val (by decide +kernel)
  simp only [cT1_30_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, CM2_20, Sa2_l3_30, Sc2_l0_30, Sl0_l0_l2_30, T1_30, TV1_30]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T1_31_val`. -/
def cT1_31_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.atom
    [0, 0, 0, 2048, -512, 3072, -512, 1792, -192, 512, -32, 72, -2, 4] []) (.mul (.atom [-6] [])
    (.atom nTV1_31 eTV1_31))) (.mul (.atom [0, -96, 0, -48, 0, -6] []) (.atom nCM2_30 eCM2_30)))
    (.mul (.atom [0, -96, 0, -48, 0, -6] []) (.atom nCM2_21 eCM2_21))) (.mul (.atom [0, 0, 384, 0,
    288, 0, 72, 0, 6] []) (.atom nCM1_20 eCM1_20))) (.mul (.atom [0, 0, 192, 0, 144, 0, 36, 0, 3]
    []) (.atom nCM1_11 eCM1_11))) (.mul (.atom [-48, -24, -36, -6, -6] []) (.atom nCA_30 eCA_30)))
    (.mul (.atom [-48, 24, -36, 6, -6] []) (.atom nCA_21 eCA_21))) (.mul (.atom [0, 0, 192, 0, 96,
    0, 12] []) (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-24, 0, -6] []) (.atom nCA_20 eCA_20))
    (.atom nCM2_11 eCM2_11))) (.mul (.atom [0, -192, 96, -96, 48, -12, 6] []) (.atom nCA_11
    eCA_11))) (.mul (.mul (.atom [-24, 0, -6] []) (.atom nCA_11 eCA_11)) (.atom nCM2_20 eCM2_20)))

@[tmio M, powerlib_domain] theorem T1_31_val {s : ℝ} (hs : 0 < s) :
    T1_31 s = TV1_31 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_31_val (by decide +kernel)
  simp only [cT1_31_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, CA_21, CA_30, CM1_11, CM1_20, CM2_11, CM2_20, CM2_21, CM2_30, Sa2_c2_31,
    Sa2_l0_l2_31, Sa3_l3_31, Sb2_l0_l0_31, Sc3_l0_31, Sl0_l0_l0_l3_31, T1_31, TV1_31]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T1_32_val`. -/
def cT1_32_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.atom [0, 0, 0, 0, 2048, -5120, 2560, -6400, 1280, -3200, 320, -800, 40,
    -100, 2, -5] []) (.mul (.atom [-12] []) (.atom nTV1_32 eTV1_32))) (.mul (.atom [0, -192, 0, -96,
    0, -12] []) (.atom nCM2_31 eCM2_31))) (.mul (.atom [0, -192, 0, -96, 0, -12] []) (.atom nCM2_22
    eCM2_22))) (.mul (.atom [0, 0, 0, 1536, 0, 1536, 0, 576, 0, 96, 0, 6] []) (.atom nCM2_20
    eCM2_20))) (.mul (.atom [0, 0, 0, 1536, 0, 1536, 0, 576, 0, 96, 0, 6] []) (.atom nCM2_11
    eCM2_11))) (.mul (.atom [0, 0, 0, 512, 0, 512, 0, 192, 0, 32, 0, 2] []) (.atom nCM2_02
    eCM2_02))) (.mul (.atom [0, 0, 384, 0, 288, 0, 72, 0, 6] []) (.atom nCM1_30 eCM1_30))) (.mul
    (.atom [0, 0, 768, 0, 576, 0, 144, 0, 12] []) (.atom nCM1_21 eCM1_21))) (.mul (.atom [0, 0, 384,
    0, 288, 0, 72, 0, 6] []) (.atom nCM1_12 eCM1_12))) (.mul (.atom [-96, -48, -72, -12, -12] [])
    (.atom nCA_31 eCA_31))) (.mul (.atom [0, 384, 192, 192, 96, 24, 12] []) (.atom nCA_30 eCA_30)))
    (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_30 eCA_30)) (.atom nCM2_02 eCM2_02))) (.mul
    (.atom [-96, 48, -72, 12, -12] []) (.atom nCA_22 eCA_22))) (.mul (.atom [0, 0, 384, 0, 192, 0,
    24] []) (.atom nCA_21 eCA_21))) (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_21 eCA_21))
    (.atom nCM2_11 eCM2_11))) (.mul (.atom [0, 0, 2304, 384, 2880, 288, 1296, 72, 252, 6, 18] [])
    (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_20 eCA_20)) (.atom
    nCM2_12 eCM2_12))) (.mul (.mul (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_20 eCA_20)) (.atom
    nCM1_11 eCM1_11))) (.mul (.mul (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_20 eCA_20)) (.atom
    nCM1_02 eCM1_02))) (.mul (.atom [0, -384, 192, -192, 96, -24, 12] []) (.atom nCA_12 eCA_12)))
    (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_12 eCA_12)) (.atom nCM2_20 eCM2_20))) (.mul
    (.atom [0, 0, 2304, -384, 2880, -288, 1296, -72, 252, -6, 18] []) (.atom nCA_11 eCA_11))) (.mul
    (.mul (.atom [-48, 0, -12] []) (.atom nCA_11 eCA_11)) (.atom nCM2_21 eCM2_21))) (.mul (.mul
    (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_11 eCA_11)) (.atom nCM1_20 eCM1_20))) (.mul (.mul
    (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_11 eCA_11)) (.atom nCM1_11 eCM1_11))) (.mul (.mul
    (.atom [96, 48, 24, 12] []) (.atom nCA_11 eCA_11)) (.atom nCA_20 eCA_20))) (.mul (.atom [-48,
    24, -12, 6] []) (.pow (.atom nCA_11 eCA_11) 2))) (.mul (.atom [0, 0, 768, -384, 960, -288, 432,
    -72, 84, -6, 6] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-48, 0, -12] []) (.atom nCA_02
    eCA_02)) (.atom nCM2_30 eCM2_30))) (.mul (.mul (.atom [0, 192, 0, 96, 0, 12] []) (.atom nCA_02
    eCA_02)) (.atom nCM1_20 eCM1_20))) (.mul (.mul (.atom [-96, 48, -24, 12] []) (.atom nCA_02
    eCA_02)) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T1_32_val {s : ℝ} (hs : 0 < s) :
    T1_32 s = TV1_32 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_32_val (by decide +kernel)
  simp only [cT1_32_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, CA_12, CA_20, CA_21, CA_22, CA_30, CA_31, CM1_02, CM1_11, CM1_12, CM1_20,
    CM1_21, CM1_30, CM2_02, CM2_11, CM2_12, CM2_20, CM2_21, CM2_22, CM2_30, CM2_31, Sa2_a2_l2_32,
    Sa2_b2_l0_32, Sa2_c3_32, Sa2_l0_l0_l3_32, Sa3_c2_32, Sa3_l0_l2_32, Sa4_l3_32, Sb3_l0_l0_32,
    Sc2_l0_l0_l0_32, Sc4_l0_32, Sl0_l0_l0_l0_l2_32, T1_32, TV1_32]
  linear_combination (1 / 12 : ℝ) * h

/-- The certificate expression of `T1_40_val`. -/
def cT1_40_val : PExpr := (.add (.add (.add (.add (.add (.add (.atom [0, 0, 0, 512, -256, 768, -256,
    448, -96, 128, -16, 18, -1, 1] []) (.mul (.atom [-6] []) (.atom nTV1_40 eTV1_40))) (.mul (.atom
    [0, -96, 0, -48, 0, -6] []) (.atom nCM2_30 eCM2_30))) (.mul (.atom [0, 0, 192, 0, 144, 0, 36, 0,
    3] []) (.atom nCM1_20 eCM1_20))) (.mul (.atom [-48, 24, -36, 6, -6] []) (.atom nCA_30 eCA_30)))
    (.mul (.atom [0, -192, 96, -96, 48, -12, 6] []) (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-24,
    0, -6] []) (.atom nCA_20 eCA_20)) (.atom nCM2_20 eCM2_20)))

@[tmio M, powerlib_domain] theorem T1_40_val {s : ℝ} (hs : 0 < s) :
    T1_40 s = TV1_40 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_40_val (by decide +kernel)
  simp only [cT1_40_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, CA_30, CM1_20, CM2_20, CM2_30, Sa2_c2_40, Sa2_l0_l2_40, Sa3_l3_40, Sb2_l0_l0_40,
    Sc3_l0_40, Sl0_l0_l0_l3_40, T1_40, TV1_40]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T1_41_val`. -/
def cT1_41_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.atom [0, 0, 0, 0, 6144, -5120,
    7680, -6400, 3840, -3200, 960, -800, 120, -100, 6, -5] []) (.mul (.atom [-24] []) (.atom nTV1_41
    eTV1_41))) (.mul (.atom [0, -384, 0, -192, 0, -24] []) (.atom nCM2_40 eCM2_40))) (.mul (.atom
    [0, -384, 0, -192, 0, -24] []) (.atom nCM2_31 eCM2_31))) (.mul (.atom [0, 0, 0, 3072, 0, 3072,
    0, 1152, 0, 192, 0, 12] []) (.atom nCM2_20 eCM2_20))) (.mul (.atom [0, 0, 0, 1024, 0, 1024, 0,
    384, 0, 64, 0, 4] []) (.atom nCM2_11 eCM2_11))) (.mul (.atom [0, 0, 1536, 0, 1152, 0, 288, 0,
    24] []) (.atom nCM1_30 eCM1_30))) (.mul (.atom [0, 0, 768, 0, 576, 0, 144, 0, 12] []) (.atom
    nCM1_21 eCM1_21))) (.mul (.atom [-192, -96, -144, -24, -24] []) (.atom nCA_40 eCA_40))) (.mul
    (.atom [-192, 96, -144, 24, -24] []) (.atom nCA_31 eCA_31))) (.mul (.atom [0, 0, 768, 0, 384, 0,
    48] []) (.atom nCA_30 eCA_30))) (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_30 eCA_30))
    (.atom nCM2_11 eCM2_11))) (.mul (.atom [0, -768, 384, -384, 192, -48, 24] []) (.atom nCA_21
    eCA_21))) (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_21 eCA_21)) (.atom nCM2_20 eCM2_20)))
    (.mul (.atom [0, 0, 4608, -768, 5760, -576, 2592, -144, 504, -12, 36] []) (.atom nCA_20
    eCA_20))) (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_20 eCA_20)) (.atom nCM2_21 eCM2_21)))
    (.mul (.mul (.atom [0, 384, 0, 192, 0, 24] []) (.atom nCA_20 eCA_20)) (.atom nCM1_20 eCM1_20)))
    (.mul (.mul (.atom [0, 384, 0, 192, 0, 24] []) (.atom nCA_20 eCA_20)) (.atom nCM1_11 eCM1_11)))
    (.mul (.atom [96, 48, 24, 12] []) (.pow (.atom nCA_20 eCA_20) 2))) (.mul (.atom [0, 0, 1536,
    -768, 1920, -576, 864, -144, 168, -12, 12] []) (.atom nCA_11 eCA_11))) (.mul (.mul (.atom [-96,
    0, -24] []) (.atom nCA_11 eCA_11)) (.atom nCM2_30 eCM2_30))) (.mul (.mul (.atom [0, 384, 0, 192,
    0, 24] []) (.atom nCA_11 eCA_11)) (.atom nCM1_20 eCM1_20))) (.mul (.mul (.atom [-192, 96, -48,
    24] []) (.atom nCA_11 eCA_11)) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T1_41_val {s : ℝ} (hs : 0 < s) :
    T1_41 s = TV1_41 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_41_val (by decide +kernel)
  simp only [cT1_41_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, CA_21, CA_30, CA_31, CA_40, CM1_11, CM1_20, CM1_21, CM1_30, CM2_11,
    CM2_20, CM2_21, CM2_30, CM2_31, CM2_40, Sa2_a2_l2_41, Sa2_b2_l0_41, Sa2_c3_41, Sa2_l0_l0_l3_41,
    Sa3_c2_41, Sa3_l0_l2_41, Sa4_l3_41, Sb3_l0_l0_41, Sc2_l0_l0_l0_41, Sc4_l0_41,
    Sl0_l0_l0_l0_l2_41, T1_41, TV1_41]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T1_50_val`. -/
def cT1_50_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.atom
    [0, 0, 0, 0, 2048, -1024, 2560, -1280, 1280, -640, 320, -160, 40, -20, 2, -1] []) (.mul (.atom
    [-24] []) (.atom nTV1_50 eTV1_50))) (.mul (.atom [0, -384, 0, -192, 0, -24] []) (.atom nCM2_40
    eCM2_40))) (.mul (.atom [0, 0, 0, 1024, 0, 1024, 0, 384, 0, 64, 0, 4] []) (.atom nCM2_20
    eCM2_20))) (.mul (.atom [0, 0, 768, 0, 576, 0, 144, 0, 12] []) (.atom nCM1_30 eCM1_30))) (.mul
    (.atom [-192, 96, -144, 24, -24] []) (.atom nCA_40 eCA_40))) (.mul (.atom [0, -768, 384, -384,
    192, -48, 24] []) (.atom nCA_30 eCA_30))) (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_30
    eCA_30)) (.atom nCM2_20 eCM2_20))) (.mul (.atom [0, 0, 1536, -768, 1920, -576, 864, -144, 168,
    -12, 12] []) (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-96, 0, -24] []) (.atom nCA_20 eCA_20))
    (.atom nCM2_30 eCM2_30))) (.mul (.mul (.atom [0, 384, 0, 192, 0, 24] []) (.atom nCA_20 eCA_20))
    (.atom nCM1_20 eCM1_20))) (.mul (.atom [-96, 48, -24, 12] []) (.pow (.atom nCA_20 eCA_20) 2)))

@[tmio M, powerlib_domain] theorem T1_50_val {s : ℝ} (hs : 0 < s) :
    T1_50 s = TV1_50 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT1_50_val (by decide +kernel)
  simp only [cT1_50_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, CA_30, CA_40, CM1_20, CM1_30, CM2_20, CM2_30, CM2_40, Sa2_a2_l2_50,
    Sa2_b2_l0_50, Sa2_c3_50, Sa2_l0_l0_l3_50, Sa3_c2_50, Sa3_l0_l2_50, Sa4_l3_50, Sb3_l0_l0_50,
    Sc2_l0_l0_l0_50, Sc4_l0_50, Sl0_l0_l0_l0_l2_50, T1_50, TV1_50]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T2_02_val`. -/
def cT2_02_val : PExpr := (.add (.atom [0, 0, -16, 0, -8, 0, -1] []) (.mul (.atom [-2] []) (.atom
    nTV2_02 eTV2_02)))

@[tmio M, powerlib_domain] theorem T2_02_val {s : ℝ} (hs : 0 < s) :
    T2_02 s = TV2_02 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_02_val (by decide +kernel)
  simp only [cT2_02_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l0_02, T2_02, TV2_02]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T2_03_val`. -/
def cT2_03_val : PExpr := (.add (.mul (.atom [-1] []) (.atom nTV2_03 eTV2_03)) (.mul (.atom [0, -4,
    0, -1] []) (.atom nCA_02 eCA_02)))

@[tmio M, powerlib_domain] theorem T2_03_val {s : ℝ} (hs : 0 < s) :
    T2_03 s = TV2_03 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_03_val (by decide +kernel)
  simp only [cT2_03_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, Sa2_l0_03, T2_03, TV2_03]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T2_04_val`. -/
def cT2_04_val : PExpr := (.add (.add (.add (.atom [0, 0, 0, 0, 256, 0, 256, 0, 96, 0, 16, 0, 1] [])
    (.mul (.atom [-24] []) (.atom nTV2_04 eTV2_04))) (.mul (.atom [0, -96, 0, -24] []) (.atom nCA_03
    eCA_03))) (.mul (.atom [-12] []) (.pow (.atom nCA_02 eCA_02) 2)))

@[tmio M, powerlib_domain] theorem T2_04_val {s : ℝ} (hs : 0 < s) :
    T2_04 s = TV2_04 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_04_val (by decide +kernel)
  simp only [cT2_04_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, Sa2_a2_04, Sa3_l0_04, Sl0_l0_l0_l0_04, T2_04, TV2_04]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T2_05_val`. -/
def cT2_05_val : PExpr := (.add (.add (.add (.mul (.atom [-6] []) (.atom nTV2_05 eTV2_05)) (.mul
    (.atom [0, -24, 0, -6] []) (.atom nCA_04 eCA_04))) (.mul (.atom [0, 0, 0, 64, 0, 48, 0, 12, 0,
    1] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-6] []) (.atom nCA_02 eCA_02)) (.atom nCA_03
    eCA_03)))

@[tmio M, powerlib_domain] theorem T2_05_val {s : ℝ} (hs : 0 < s) :
    T2_05 s = TV2_05 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_05_val (by decide +kernel)
  simp only [cT2_05_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_04, Sa2_a3_05, Sa2_l0_l0_l0_05, Sa4_l0_05, T2_05, TV2_05]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T2_11_val`. -/
def cT2_11_val : PExpr := (.add (.atom [0, 0, -16, 0, -8, 0, -1] []) (.mul (.atom [-1] []) (.atom
    nTV2_11 eTV2_11)))

@[tmio M, powerlib_domain] theorem T2_11_val {s : ℝ} (hs : 0 < s) :
    T2_11 s = TV2_11 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_11_val (by decide +kernel)
  simp only [cT2_11_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l0_11, T2_11, TV2_11]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T2_12_val`. -/
def cT2_12_val : PExpr := (.add (.add (.mul (.atom [-1] []) (.atom nTV2_12 eTV2_12)) (.mul (.atom
    [0, -4, 0, -1] []) (.atom nCA_11 eCA_11))) (.mul (.atom [0, -4, 0, -1] []) (.atom nCA_02
    eCA_02)))

@[tmio M, powerlib_domain] theorem T2_12_val {s : ℝ} (hs : 0 < s) :
    T2_12 s = TV2_12 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_12_val (by decide +kernel)
  simp only [cT2_12_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, Sa2_l0_12, T2_12, TV2_12]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T2_13_val`. -/
def cT2_13_val : PExpr := (.add (.add (.add (.add (.atom [0, 0, 0, 0, 256, 0, 256, 0, 96, 0, 16, 0,
    1] []) (.mul (.atom [-6] []) (.atom nTV2_13 eTV2_13))) (.mul (.atom [0, -24, 0, -6] []) (.atom
    nCA_12 eCA_12))) (.mul (.atom [0, -24, 0, -6] []) (.atom nCA_03 eCA_03))) (.mul (.mul (.atom
    [-6] []) (.atom nCA_02 eCA_02)) (.atom nCA_11 eCA_11)))

@[tmio M, powerlib_domain] theorem T2_13_val {s : ℝ} (hs : 0 < s) :
    T2_13 s = TV2_13 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_13_val (by decide +kernel)
  simp only [cT2_13_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_11, CA_12, Sa2_a2_13, Sa3_l0_13, Sl0_l0_l0_l0_13, T2_13, TV2_13]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T2_14_val`. -/
def cT2_14_val : PExpr := (.add (.add (.add (.add (.add (.add (.mul (.atom [-6] []) (.atom nTV2_14
    eTV2_14)) (.mul (.atom [0, -24, 0, -6] []) (.atom nCA_13 eCA_13))) (.mul (.atom [0, 0, 0, 64, 0,
    48, 0, 12, 0, 1] []) (.atom nCA_11 eCA_11))) (.mul (.atom [0, -24, 0, -6] []) (.atom nCA_04
    eCA_04))) (.mul (.mul (.atom [-6] []) (.atom nCA_03 eCA_03)) (.atom nCA_11 eCA_11))) (.mul
    (.atom [0, 0, 0, 192, 0, 144, 0, 36, 0, 3] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-6]
    []) (.atom nCA_02 eCA_02)) (.atom nCA_12 eCA_12)))

@[tmio M, powerlib_domain] theorem T2_14_val {s : ℝ} (hs : 0 < s) :
    T2_14 s = TV2_14 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_14_val (by decide +kernel)
  simp only [cT2_14_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_04, CA_11, CA_12, CA_13, Sa2_a3_14, Sa2_l0_l0_l0_14, Sa4_l0_14, T2_14,
    TV2_14]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T2_20_val`. -/
def cT2_20_val : PExpr := (.add (.atom [0, 0, -16, 0, -8, 0, -1] []) (.mul (.atom [-2] []) (.atom
    nTV2_20 eTV2_20)))

@[tmio M, powerlib_domain] theorem T2_20_val {s : ℝ} (hs : 0 < s) :
    T2_20 s = TV2_20 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_20_val (by decide +kernel)
  simp only [cT2_20_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l0_20, T2_20, TV2_20]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T2_21_val`. -/
def cT2_21_val : PExpr := (.add (.add (.mul (.atom [-1] []) (.atom nTV2_21 eTV2_21)) (.mul (.atom
    [0, -4, 0, -1] []) (.atom nCA_20 eCA_20))) (.mul (.atom [0, -4, 0, -1] []) (.atom nCA_11
    eCA_11)))

@[tmio M, powerlib_domain] theorem T2_21_val {s : ℝ} (hs : 0 < s) :
    T2_21 s = TV2_21 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_21_val (by decide +kernel)
  simp only [cT2_21_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, Sa2_l0_21, T2_21, TV2_21]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T2_22_val`. -/
def cT2_22_val : PExpr := (.add (.add (.add (.add (.add (.atom [0, 0, 0, 0, 256, 0, 256, 0, 96, 0,
    16, 0, 1] []) (.mul (.atom [-4] []) (.atom nTV2_22 eTV2_22))) (.mul (.atom [0, -16, 0, -4] [])
    (.atom nCA_21 eCA_21))) (.mul (.atom [0, -16, 0, -4] []) (.atom nCA_12 eCA_12))) (.mul (.atom
    [-2] []) (.pow (.atom nCA_11 eCA_11) 2))) (.mul (.mul (.atom [-4] []) (.atom nCA_02 eCA_02))
    (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T2_22_val {s : ℝ} (hs : 0 < s) :
    T2_22 s = TV2_22 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_22_val (by decide +kernel)
  simp only [cT2_22_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, CA_12, CA_20, CA_21, Sa2_a2_22, Sa3_l0_22, Sl0_l0_l0_l0_22, T2_22,
    TV2_22]
  linear_combination (1 / 4 : ℝ) * h

/-- The certificate expression of `T2_23_val`. -/
def cT2_23_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-6] [])
    (.atom nTV2_23 eTV2_23)) (.mul (.atom [0, -24, 0, -6] []) (.atom nCA_22 eCA_22))) (.mul (.atom
    [0, 0, 0, 64, 0, 48, 0, 12, 0, 1] []) (.atom nCA_20 eCA_20))) (.mul (.atom [0, -24, 0, -6] [])
    (.atom nCA_13 eCA_13))) (.mul (.atom [0, 0, 0, 192, 0, 144, 0, 36, 0, 3] []) (.atom nCA_11
    eCA_11))) (.mul (.mul (.atom [-6] []) (.atom nCA_11 eCA_11)) (.atom nCA_12 eCA_12))) (.mul (.mul
    (.atom [-6] []) (.atom nCA_03 eCA_03)) (.atom nCA_20 eCA_20))) (.mul (.atom [0, 0, 0, 192, 0,
    144, 0, 36, 0, 3] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-6] []) (.atom nCA_02 eCA_02))
    (.atom nCA_21 eCA_21)))

@[tmio M, powerlib_domain] theorem T2_23_val {s : ℝ} (hs : 0 < s) :
    T2_23 s = TV2_23 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_23_val (by decide +kernel)
  simp only [cT2_23_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_11, CA_12, CA_13, CA_20, CA_21, CA_22, Sa2_a3_23, Sa2_l0_l0_l0_23,
    Sa4_l0_23, T2_23, TV2_23]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T2_30_val`. -/
def cT2_30_val : PExpr := (.add (.mul (.atom [-1] []) (.atom nTV2_30 eTV2_30)) (.mul (.atom [0, -4,
    0, -1] []) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T2_30_val {s : ℝ} (hs : 0 < s) :
    T2_30 s = TV2_30 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_30_val (by decide +kernel)
  simp only [cT2_30_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, Sa2_l0_30, T2_30, TV2_30]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `T2_31_val`. -/
def cT2_31_val : PExpr := (.add (.add (.add (.add (.atom [0, 0, 0, 0, 256, 0, 256, 0, 96, 0, 16, 0,
    1] []) (.mul (.atom [-6] []) (.atom nTV2_31 eTV2_31))) (.mul (.atom [0, -24, 0, -6] []) (.atom
    nCA_30 eCA_30))) (.mul (.atom [0, -24, 0, -6] []) (.atom nCA_21 eCA_21))) (.mul (.mul (.atom
    [-6] []) (.atom nCA_11 eCA_11)) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T2_31_val {s : ℝ} (hs : 0 < s) :
    T2_31 s = TV2_31 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_31_val (by decide +kernel)
  simp only [cT2_31_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, CA_21, CA_30, Sa2_a2_31, Sa3_l0_31, Sl0_l0_l0_l0_31, T2_31, TV2_31]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T2_32_val`. -/
def cT2_32_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-6] [])
    (.atom nTV2_32 eTV2_32)) (.mul (.atom [0, -24, 0, -6] []) (.atom nCA_31 eCA_31))) (.mul (.atom
    [0, -24, 0, -6] []) (.atom nCA_22 eCA_22))) (.mul (.atom [0, 0, 0, 192, 0, 144, 0, 36, 0, 3] [])
    (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-6] []) (.atom nCA_12 eCA_12)) (.atom nCA_20
    eCA_20))) (.mul (.atom [0, 0, 0, 192, 0, 144, 0, 36, 0, 3] []) (.atom nCA_11 eCA_11))) (.mul
    (.mul (.atom [-6] []) (.atom nCA_11 eCA_11)) (.atom nCA_21 eCA_21))) (.mul (.atom [0, 0, 0, 64,
    0, 48, 0, 12, 0, 1] []) (.atom nCA_02 eCA_02))) (.mul (.mul (.atom [-6] []) (.atom nCA_02
    eCA_02)) (.atom nCA_30 eCA_30)))

@[tmio M, powerlib_domain] theorem T2_32_val {s : ℝ} (hs : 0 < s) :
    T2_32 s = TV2_32 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_32_val (by decide +kernel)
  simp only [cT2_32_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, CA_12, CA_20, CA_21, CA_22, CA_30, CA_31, Sa2_a3_32, Sa2_l0_l0_l0_32,
    Sa4_l0_32, T2_32, TV2_32]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T2_40_val`. -/
def cT2_40_val : PExpr := (.add (.add (.add (.atom [0, 0, 0, 0, 256, 0, 256, 0, 96, 0, 16, 0, 1] [])
    (.mul (.atom [-24] []) (.atom nTV2_40 eTV2_40))) (.mul (.atom [0, -96, 0, -24] []) (.atom nCA_30
    eCA_30))) (.mul (.atom [-12] []) (.pow (.atom nCA_20 eCA_20) 2)))

@[tmio M, powerlib_domain] theorem T2_40_val {s : ℝ} (hs : 0 < s) :
    T2_40 s = TV2_40 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_40_val (by decide +kernel)
  simp only [cT2_40_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, CA_30, Sa2_a2_40, Sa3_l0_40, Sl0_l0_l0_l0_40, T2_40, TV2_40]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T2_41_val`. -/
def cT2_41_val : PExpr := (.add (.add (.add (.add (.add (.add (.mul (.atom [-6] []) (.atom nTV2_41
    eTV2_41)) (.mul (.atom [0, -24, 0, -6] []) (.atom nCA_40 eCA_40))) (.mul (.atom [0, -24, 0, -6]
    []) (.atom nCA_31 eCA_31))) (.mul (.atom [0, 0, 0, 192, 0, 144, 0, 36, 0, 3] []) (.atom nCA_20
    eCA_20))) (.mul (.mul (.atom [-6] []) (.atom nCA_20 eCA_20)) (.atom nCA_21 eCA_21))) (.mul
    (.atom [0, 0, 0, 64, 0, 48, 0, 12, 0, 1] []) (.atom nCA_11 eCA_11))) (.mul (.mul (.atom [-6] [])
    (.atom nCA_11 eCA_11)) (.atom nCA_30 eCA_30)))

@[tmio M, powerlib_domain] theorem T2_41_val {s : ℝ} (hs : 0 < s) :
    T2_41 s = TV2_41 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_41_val (by decide +kernel)
  simp only [cT2_41_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, CA_21, CA_30, CA_31, CA_40, Sa2_a3_41, Sa2_l0_l0_l0_41, Sa4_l0_41, T2_41,
    TV2_41]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T2_50_val`. -/
def cT2_50_val : PExpr := (.add (.add (.add (.mul (.atom [-6] []) (.atom nTV2_50 eTV2_50)) (.mul
    (.atom [0, -24, 0, -6] []) (.atom nCA_40 eCA_40))) (.mul (.atom [0, 0, 0, 64, 0, 48, 0, 12, 0,
    1] []) (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [-6] []) (.atom nCA_20 eCA_20)) (.atom nCA_30
    eCA_30)))

@[tmio M, powerlib_domain] theorem T2_50_val {s : ℝ} (hs : 0 < s) :
    T2_50 s = TV2_50 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT2_50_val (by decide +kernel)
  simp only [cT2_50_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, CA_30, CA_40, Sa2_a3_50, Sa2_l0_l0_l0_50, Sa4_l0_50, T2_50, TV2_50]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T3_03_val`. -/
def cT3_03_val : PExpr := (.add (.atom [0, 0, 0, -64, 0, -48, 0, -12, 0, -1] []) (.mul (.atom [-6]
    []) (.atom nTV3_03 eTV3_03)))

@[tmio M, powerlib_domain] theorem T3_03_val {s : ℝ} (hs : 0 < s) :
    T3_03 s = TV3_03 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_03_val (by decide +kernel)
  simp only [cT3_03_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l0_l0_03, T3_03, TV3_03]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T3_04_val`. -/
def cT3_04_val : PExpr := (.add (.mul (.atom [-2] []) (.atom nTV3_04 eTV3_04)) (.mul (.atom [0, 0,
    -16, 0, -8, 0, -1] []) (.atom nCA_02 eCA_02)))

@[tmio M, powerlib_domain] theorem T3_04_val {s : ℝ} (hs : 0 < s) :
    T3_04 s = TV3_04 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_04_val (by decide +kernel)
  simp only [cT3_04_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, Sa2_l0_l0_04, T3_04, TV3_04]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T3_05_val`. -/
def cT3_05_val : PExpr := (.add (.add (.add (.atom [0, 0, 0, 0, 0, 1024, 0, 1280, 0, 640, 0, 160, 0,
    20, 0, 1] []) (.mul (.atom [-120] []) (.atom nTV3_05 eTV3_05))) (.mul (.atom [0, 0, -960, 0,
    -480, 0, -60] []) (.atom nCA_03 eCA_03))) (.mul (.atom [0, -240, 0, -60] []) (.pow (.atom nCA_02
    eCA_02) 2)))

@[tmio M, powerlib_domain] theorem T3_05_val {s : ℝ} (hs : 0 < s) :
    T3_05 s = TV3_05 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_05_val (by decide +kernel)
  simp only [cT3_05_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, Sa2_a2_l0_05, Sa3_l0_l0_05, Sl0_l0_l0_l0_l0_05, T3_05, TV3_05]
  linear_combination (1 / 120 : ℝ) * h

/-- The certificate expression of `T3_12_val`. -/
def cT3_12_val : PExpr := (.add (.atom [0, 0, 0, -64, 0, -48, 0, -12, 0, -1] []) (.mul (.atom [-2]
    []) (.atom nTV3_12 eTV3_12)))

@[tmio M, powerlib_domain] theorem T3_12_val {s : ℝ} (hs : 0 < s) :
    T3_12 s = TV3_12 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_12_val (by decide +kernel)
  simp only [cT3_12_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l0_l0_12, T3_12, TV3_12]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T3_13_val`. -/
def cT3_13_val : PExpr := (.add (.add (.mul (.atom [-2] []) (.atom nTV3_13 eTV3_13)) (.mul (.atom
    [0, 0, -16, 0, -8, 0, -1] []) (.atom nCA_11 eCA_11))) (.mul (.atom [0, 0, -32, 0, -16, 0, -2]
    []) (.atom nCA_02 eCA_02)))

@[tmio M, powerlib_domain] theorem T3_13_val {s : ℝ} (hs : 0 < s) :
    T3_13 s = TV3_13 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_13_val (by decide +kernel)
  simp only [cT3_13_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, Sa2_l0_l0_13, T3_13, TV3_13]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T3_14_val`. -/
def cT3_14_val : PExpr := (.add (.add (.add (.add (.add (.atom [0, 0, 0, 0, 0, 1024, 0, 1280, 0,
    640, 0, 160, 0, 20, 0, 1] []) (.mul (.atom [-24] []) (.atom nTV3_14 eTV3_14))) (.mul (.atom [0,
    0, -192, 0, -96, 0, -12] []) (.atom nCA_12 eCA_12))) (.mul (.atom [0, 0, -384, 0, -192, 0, -24]
    []) (.atom nCA_03 eCA_03))) (.mul (.mul (.atom [0, -96, 0, -24] []) (.atom nCA_02 eCA_02))
    (.atom nCA_11 eCA_11))) (.mul (.atom [0, -48, 0, -12] []) (.pow (.atom nCA_02 eCA_02) 2)))

@[tmio M, powerlib_domain] theorem T3_14_val {s : ℝ} (hs : 0 < s) :
    T3_14 s = TV3_14 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_14_val (by decide +kernel)
  simp only [cT3_14_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_11, CA_12, Sa2_a2_l0_14, Sa3_l0_l0_14, Sl0_l0_l0_l0_l0_14, T3_14,
    TV3_14]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T3_21_val`. -/
def cT3_21_val : PExpr := (.add (.atom [0, 0, 0, -64, 0, -48, 0, -12, 0, -1] []) (.mul (.atom [-2]
    []) (.atom nTV3_21 eTV3_21)))

@[tmio M, powerlib_domain] theorem T3_21_val {s : ℝ} (hs : 0 < s) :
    T3_21 s = TV3_21 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_21_val (by decide +kernel)
  simp only [cT3_21_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l0_l0_21, T3_21, TV3_21]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T3_22_val`. -/
def cT3_22_val : PExpr := (.add (.add (.add (.mul (.atom [-2] []) (.atom nTV3_22 eTV3_22)) (.mul
    (.atom [0, 0, -16, 0, -8, 0, -1] []) (.atom nCA_20 eCA_20))) (.mul (.atom [0, 0, -32, 0, -16, 0,
    -2] []) (.atom nCA_11 eCA_11))) (.mul (.atom [0, 0, -16, 0, -8, 0, -1] []) (.atom nCA_02
    eCA_02)))

@[tmio M, powerlib_domain] theorem T3_22_val {s : ℝ} (hs : 0 < s) :
    T3_22 s = TV3_22 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_22_val (by decide +kernel)
  simp only [cT3_22_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, CA_20, Sa2_l0_l0_22, T3_22, TV3_22]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T3_23_val`. -/
def cT3_23_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.atom [0, 0, 0, 0, 0, 1024, 0,
    1280, 0, 640, 0, 160, 0, 20, 0, 1] []) (.mul (.atom [-12] []) (.atom nTV3_23 eTV3_23))) (.mul
    (.atom [0, 0, -96, 0, -48, 0, -6] []) (.atom nCA_21 eCA_21))) (.mul (.atom [0, 0, -192, 0, -96,
    0, -12] []) (.atom nCA_12 eCA_12))) (.mul (.atom [0, -24, 0, -6] []) (.pow (.atom nCA_11 eCA_11)
    2))) (.mul (.atom [0, 0, -96, 0, -48, 0, -6] []) (.atom nCA_03 eCA_03))) (.mul (.mul (.atom [0,
    -48, 0, -12] []) (.atom nCA_02 eCA_02)) (.atom nCA_20 eCA_20))) (.mul (.mul (.atom [0, -48, 0,
    -12] []) (.atom nCA_02 eCA_02)) (.atom nCA_11 eCA_11)))

@[tmio M, powerlib_domain] theorem T3_23_val {s : ℝ} (hs : 0 < s) :
    T3_23 s = TV3_23 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_23_val (by decide +kernel)
  simp only [cT3_23_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_03, CA_11, CA_12, CA_20, CA_21, Sa2_a2_l0_23, Sa3_l0_l0_23,
    Sl0_l0_l0_l0_l0_23, T3_23, TV3_23]
  linear_combination (1 / 12 : ℝ) * h

/-- The certificate expression of `T3_30_val`. -/
def cT3_30_val : PExpr := (.add (.atom [0, 0, 0, -64, 0, -48, 0, -12, 0, -1] []) (.mul (.atom [-6]
    []) (.atom nTV3_30 eTV3_30)))

@[tmio M, powerlib_domain] theorem T3_30_val {s : ℝ} (hs : 0 < s) :
    T3_30 s = TV3_30 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_30_val (by decide +kernel)
  simp only [cT3_30_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [Sl0_l0_l0_30, T3_30, TV3_30]
  linear_combination (1 / 6 : ℝ) * h

/-- The certificate expression of `T3_31_val`. -/
def cT3_31_val : PExpr := (.add (.add (.mul (.atom [-2] []) (.atom nTV3_31 eTV3_31)) (.mul (.atom
    [0, 0, -32, 0, -16, 0, -2] []) (.atom nCA_20 eCA_20))) (.mul (.atom [0, 0, -16, 0, -8, 0, -1]
    []) (.atom nCA_11 eCA_11)))

@[tmio M, powerlib_domain] theorem T3_31_val {s : ℝ} (hs : 0 < s) :
    T3_31 s = TV3_31 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_31_val (by decide +kernel)
  simp only [cT3_31_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, Sa2_l0_l0_31, T3_31, TV3_31]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T3_32_val`. -/
def cT3_32_val : PExpr := (.add (.add (.add (.add (.add (.add (.add (.atom [0, 0, 0, 0, 0, 1024, 0,
    1280, 0, 640, 0, 160, 0, 20, 0, 1] []) (.mul (.atom [-12] []) (.atom nTV3_32 eTV3_32))) (.mul
    (.atom [0, 0, -96, 0, -48, 0, -6] []) (.atom nCA_30 eCA_30))) (.mul (.atom [0, 0, -192, 0, -96,
    0, -12] []) (.atom nCA_21 eCA_21))) (.mul (.atom [0, 0, -96, 0, -48, 0, -6] []) (.atom nCA_12
    eCA_12))) (.mul (.mul (.atom [0, -48, 0, -12] []) (.atom nCA_11 eCA_11)) (.atom nCA_20 eCA_20)))
    (.mul (.atom [0, -24, 0, -6] []) (.pow (.atom nCA_11 eCA_11) 2))) (.mul (.mul (.atom [0, -48, 0,
    -12] []) (.atom nCA_02 eCA_02)) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T3_32_val {s : ℝ} (hs : 0 < s) :
    T3_32 s = TV3_32 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_32_val (by decide +kernel)
  simp only [cT3_32_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_02, CA_11, CA_12, CA_20, CA_21, CA_30, Sa2_a2_l0_32, Sa3_l0_l0_32,
    Sl0_l0_l0_l0_l0_32, T3_32, TV3_32]
  linear_combination (1 / 12 : ℝ) * h

/-- The certificate expression of `T3_40_val`. -/
def cT3_40_val : PExpr := (.add (.mul (.atom [-2] []) (.atom nTV3_40 eTV3_40)) (.mul (.atom [0, 0,
    -16, 0, -8, 0, -1] []) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T3_40_val {s : ℝ} (hs : 0 < s) :
    T3_40 s = TV3_40 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_40_val (by decide +kernel)
  simp only [cT3_40_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, Sa2_l0_l0_40, T3_40, TV3_40]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `T3_41_val`. -/
def cT3_41_val : PExpr := (.add (.add (.add (.add (.add (.atom [0, 0, 0, 0, 0, 1024, 0, 1280, 0,
    640, 0, 160, 0, 20, 0, 1] []) (.mul (.atom [-24] []) (.atom nTV3_41 eTV3_41))) (.mul (.atom [0,
    0, -384, 0, -192, 0, -24] []) (.atom nCA_30 eCA_30))) (.mul (.atom [0, 0, -192, 0, -96, 0, -12]
    []) (.atom nCA_21 eCA_21))) (.mul (.atom [0, -48, 0, -12] []) (.pow (.atom nCA_20 eCA_20) 2)))
    (.mul (.mul (.atom [0, -96, 0, -24] []) (.atom nCA_11 eCA_11)) (.atom nCA_20 eCA_20)))

@[tmio M, powerlib_domain] theorem T3_41_val {s : ℝ} (hs : 0 < s) :
    T3_41 s = TV3_41 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_41_val (by decide +kernel)
  simp only [cT3_41_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_11, CA_20, CA_21, CA_30, Sa2_a2_l0_41, Sa3_l0_l0_41, Sl0_l0_l0_l0_l0_41, T3_41,
    TV3_41]
  linear_combination (1 / 24 : ℝ) * h

/-- The certificate expression of `T3_50_val`. -/
def cT3_50_val : PExpr := (.add (.add (.add (.atom [0, 0, 0, 0, 0, 1024, 0, 1280, 0, 640, 0, 160, 0,
    20, 0, 1] []) (.mul (.atom [-120] []) (.atom nTV3_50 eTV3_50))) (.mul (.atom [0, 0, -960, 0,
    -480, 0, -60] []) (.atom nCA_30 eCA_30))) (.mul (.atom [0, -240, 0, -60] []) (.pow (.atom nCA_20
    eCA_20) 2)))

@[tmio M, powerlib_domain] theorem T3_50_val {s : ℝ} (hs : 0 < s) :
    T3_50 s = TV3_50 s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cT3_50_val (by decide +kernel)
  simp only [cT3_50_val, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CA_20, CA_30, Sa2_a2_l0_50, Sa3_l0_l0_50, Sl0_l0_l0_l0_l0_50, T3_50, TV3_50]
  linear_combination (1 / 120 : ℝ) * h

/-- The certificate expression of `JA_20_eq`. -/
def cJA_20_eq : PExpr := (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom
    nTV2_20 eTV2_20)) (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_20 eTV1_20)))
    (.mul (.atom [1] []) (.atom nJA_20 eJA_20)))

@[tmio M, powerlib_domain] theorem JA_20_eq {s : ℝ} (hs : 0 < s) :
    JA_20 s = PV0_1 s * T1_20 s + PV0_2 s * T2_20 s + PV0_3 s * T3_20 s := by
  rw [T1_20_val hs, T2_20_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_20_eq (by decide +kernel)
  simp only [cJA_20_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_20, PV0_1, PV0_2, T3_20, TV1_20, TV2_20]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_20_eq`. -/
def cJB_20_eq : PExpr := (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom
    nTV2_20 eTV2_20)) (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_20 eTV1_20)))
    (.mul (.atom [1] []) (.atom nJB_20 eJB_20)))

@[tmio M, powerlib_domain] theorem JB_20_eq {s : ℝ} (hs : 0 < s) :
    JB_20 s = PV1_1 s * T1_20 s + PV1_2 s * T2_20 s + PV1_3 s * T3_20 s := by
  rw [T1_20_val hs, T2_20_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_20_eq (by decide +kernel)
  simp only [cJB_20_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_20, PV1_1, PV1_2, T3_20, TV1_20, TV2_20]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_11_eq`. -/
def cJA_11_eq : PExpr := (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom
    nTV2_11 eTV2_11)) (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_11 eTV1_11)))
    (.mul (.atom [1] []) (.atom nJA_11 eJA_11)))

@[tmio M, powerlib_domain] theorem JA_11_eq {s : ℝ} (hs : 0 < s) :
    JA_11 s = PV0_1 s * T1_11 s + PV0_2 s * T2_11 s + PV0_3 s * T3_11 s := by
  rw [T1_11_val hs, T2_11_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_11_eq (by decide +kernel)
  simp only [cJA_11_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_11, PV0_1, PV0_2, T3_11, TV1_11, TV2_11]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_11_eq`. -/
def cJB_11_eq : PExpr := (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom
    nTV2_11 eTV2_11)) (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_11 eTV1_11)))
    (.mul (.atom [1] []) (.atom nJB_11 eJB_11)))

@[tmio M, powerlib_domain] theorem JB_11_eq {s : ℝ} (hs : 0 < s) :
    JB_11 s = PV1_1 s * T1_11 s + PV1_2 s * T2_11 s + PV1_3 s * T3_11 s := by
  rw [T1_11_val hs, T2_11_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_11_eq (by decide +kernel)
  simp only [cJB_11_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_11, PV1_1, PV1_2, T3_11, TV1_11, TV2_11]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_02_eq`. -/
def cJA_02_eq : PExpr := (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom
    nTV2_02 eTV2_02)) (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_02 eTV1_02)))
    (.mul (.atom [1] []) (.atom nJA_02 eJA_02)))

@[tmio M, powerlib_domain] theorem JA_02_eq {s : ℝ} (hs : 0 < s) :
    JA_02 s = PV0_1 s * T1_02 s + PV0_2 s * T2_02 s + PV0_3 s * T3_02 s := by
  rw [T1_02_val hs, T2_02_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_02_eq (by decide +kernel)
  simp only [cJA_02_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, PV0_1, PV0_2, T3_02, TV1_02, TV2_02]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_02_eq`. -/
def cJB_02_eq : PExpr := (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom
    nTV2_02 eTV2_02)) (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_02 eTV1_02)))
    (.mul (.atom [1] []) (.atom nJB_02 eJB_02)))

@[tmio M, powerlib_domain] theorem JB_02_eq {s : ℝ} (hs : 0 < s) :
    JB_02 s = PV1_1 s * T1_02 s + PV1_2 s * T2_02 s + PV1_3 s * T3_02 s := by
  rw [T1_02_val hs, T2_02_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_02_eq (by decide +kernel)
  simp only [cJB_02_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_02, PV1_1, PV1_2, T3_02, TV1_02, TV2_02]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_30_eq`. -/
def cJA_30_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_30 eTV3_30)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_30 eTV2_30)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_30 eTV1_30))) (.mul (.atom [1]
    []) (.atom nJA_30 eJA_30)))

@[tmio M, powerlib_domain] theorem JA_30_eq {s : ℝ} (hs : 0 < s) :
    JA_30 s = PV0_1 s * T1_30 s + PV0_2 s * T2_30 s + PV0_3 s * T3_30 s := by
  rw [T1_30_val hs, T2_30_val hs, T3_30_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_30_eq (by decide +kernel)
  simp only [cJA_30_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_30, PV0_1, PV0_2, PV0_3, TV1_30, TV2_30, TV3_30]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_30_eq`. -/
def cJB_30_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_30 eTV3_30)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_30 eTV2_30)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_30 eTV1_30))) (.mul (.atom [1]
    []) (.atom nJB_30 eJB_30)))

@[tmio M, powerlib_domain] theorem JB_30_eq {s : ℝ} (hs : 0 < s) :
    JB_30 s = PV1_1 s * T1_30 s + PV1_2 s * T2_30 s + PV1_3 s * T3_30 s := by
  rw [T1_30_val hs, T2_30_val hs, T3_30_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_30_eq (by decide +kernel)
  simp only [cJB_30_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_30, PV1_1, PV1_2, PV1_3, TV1_30, TV2_30, TV3_30]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_21_eq`. -/
def cJA_21_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_21 eTV3_21)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_21 eTV2_21)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_21 eTV1_21))) (.mul (.atom [1]
    []) (.atom nJA_21 eJA_21)))

@[tmio M, powerlib_domain] theorem JA_21_eq {s : ℝ} (hs : 0 < s) :
    JA_21 s = PV0_1 s * T1_21 s + PV0_2 s * T2_21 s + PV0_3 s * T3_21 s := by
  rw [T1_21_val hs, T2_21_val hs, T3_21_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_21_eq (by decide +kernel)
  simp only [cJA_21_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_21, PV0_1, PV0_2, PV0_3, TV1_21, TV2_21, TV3_21]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_21_eq`. -/
def cJB_21_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_21 eTV3_21)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_21 eTV2_21)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_21 eTV1_21))) (.mul (.atom [1]
    []) (.atom nJB_21 eJB_21)))

@[tmio M, powerlib_domain] theorem JB_21_eq {s : ℝ} (hs : 0 < s) :
    JB_21 s = PV1_1 s * T1_21 s + PV1_2 s * T2_21 s + PV1_3 s * T3_21 s := by
  rw [T1_21_val hs, T2_21_val hs, T3_21_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_21_eq (by decide +kernel)
  simp only [cJB_21_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_21, PV1_1, PV1_2, PV1_3, TV1_21, TV2_21, TV3_21]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_12_eq`. -/
def cJA_12_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_12 eTV3_12)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_12 eTV2_12)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_12 eTV1_12))) (.mul (.atom [1]
    []) (.atom nJA_12 eJA_12)))

@[tmio M, powerlib_domain] theorem JA_12_eq {s : ℝ} (hs : 0 < s) :
    JA_12 s = PV0_1 s * T1_12 s + PV0_2 s * T2_12 s + PV0_3 s * T3_12 s := by
  rw [T1_12_val hs, T2_12_val hs, T3_12_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_12_eq (by decide +kernel)
  simp only [cJA_12_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_12, PV0_1, PV0_2, PV0_3, TV1_12, TV2_12, TV3_12]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_12_eq`. -/
def cJB_12_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_12 eTV3_12)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_12 eTV2_12)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_12 eTV1_12))) (.mul (.atom [1]
    []) (.atom nJB_12 eJB_12)))

@[tmio M, powerlib_domain] theorem JB_12_eq {s : ℝ} (hs : 0 < s) :
    JB_12 s = PV1_1 s * T1_12 s + PV1_2 s * T2_12 s + PV1_3 s * T3_12 s := by
  rw [T1_12_val hs, T2_12_val hs, T3_12_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_12_eq (by decide +kernel)
  simp only [cJB_12_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_12, PV1_1, PV1_2, PV1_3, TV1_12, TV2_12, TV3_12]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_03_eq`. -/
def cJA_03_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_03 eTV3_03)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_03 eTV2_03)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_03 eTV1_03))) (.mul (.atom [1]
    []) (.atom nJA_03 eJA_03)))

@[tmio M, powerlib_domain] theorem JA_03_eq {s : ℝ} (hs : 0 < s) :
    JA_03 s = PV0_1 s * T1_03 s + PV0_2 s * T2_03 s + PV0_3 s * T3_03 s := by
  rw [T1_03_val hs, T2_03_val hs, T3_03_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_03_eq (by decide +kernel)
  simp only [cJA_03_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_03, PV0_1, PV0_2, PV0_3, TV1_03, TV2_03, TV3_03]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_03_eq`. -/
def cJB_03_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_03 eTV3_03)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_03 eTV2_03)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_03 eTV1_03))) (.mul (.atom [1]
    []) (.atom nJB_03 eJB_03)))

@[tmio M, powerlib_domain] theorem JB_03_eq {s : ℝ} (hs : 0 < s) :
    JB_03 s = PV1_1 s * T1_03 s + PV1_2 s * T2_03 s + PV1_3 s * T3_03 s := by
  rw [T1_03_val hs, T2_03_val hs, T3_03_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_03_eq (by decide +kernel)
  simp only [cJB_03_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_03, PV1_1, PV1_2, PV1_3, TV1_03, TV2_03, TV3_03]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_40_eq`. -/
def cJA_40_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_40 eTV3_40)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_40 eTV2_40)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_40 eTV1_40))) (.mul (.atom [1]
    []) (.atom nJA_40 eJA_40)))

@[tmio M, powerlib_domain] theorem JA_40_eq {s : ℝ} (hs : 0 < s) :
    JA_40 s = PV0_1 s * T1_40 s + PV0_2 s * T2_40 s + PV0_3 s * T3_40 s := by
  rw [T1_40_val hs, T2_40_val hs, T3_40_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_40_eq (by decide +kernel)
  simp only [cJA_40_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_40, PV0_1, PV0_2, PV0_3, TV1_40, TV2_40, TV3_40]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_40_eq`. -/
def cJB_40_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_40 eTV3_40)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_40 eTV2_40)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_40 eTV1_40))) (.mul (.atom [1]
    []) (.atom nJB_40 eJB_40)))

@[tmio M, powerlib_domain] theorem JB_40_eq {s : ℝ} (hs : 0 < s) :
    JB_40 s = PV1_1 s * T1_40 s + PV1_2 s * T2_40 s + PV1_3 s * T3_40 s := by
  rw [T1_40_val hs, T2_40_val hs, T3_40_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_40_eq (by decide +kernel)
  simp only [cJB_40_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_40, PV1_1, PV1_2, PV1_3, TV1_40, TV2_40, TV3_40]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_31_eq`. -/
def cJA_31_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_31 eTV3_31)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_31 eTV2_31)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_31 eTV1_31))) (.mul (.atom [1]
    []) (.atom nJA_31 eJA_31)))

@[tmio M, powerlib_domain] theorem JA_31_eq {s : ℝ} (hs : 0 < s) :
    JA_31 s = PV0_1 s * T1_31 s + PV0_2 s * T2_31 s + PV0_3 s * T3_31 s := by
  rw [T1_31_val hs, T2_31_val hs, T3_31_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_31_eq (by decide +kernel)
  simp only [cJA_31_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_31, PV0_1, PV0_2, PV0_3, TV1_31, TV2_31, TV3_31]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_31_eq`. -/
def cJB_31_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_31 eTV3_31)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_31 eTV2_31)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_31 eTV1_31))) (.mul (.atom [1]
    []) (.atom nJB_31 eJB_31)))

@[tmio M, powerlib_domain] theorem JB_31_eq {s : ℝ} (hs : 0 < s) :
    JB_31 s = PV1_1 s * T1_31 s + PV1_2 s * T2_31 s + PV1_3 s * T3_31 s := by
  rw [T1_31_val hs, T2_31_val hs, T3_31_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_31_eq (by decide +kernel)
  simp only [cJB_31_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_31, PV1_1, PV1_2, PV1_3, TV1_31, TV2_31, TV3_31]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_22_eq`. -/
def cJA_22_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_22 eTV3_22)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_22 eTV2_22)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_22 eTV1_22))) (.mul (.atom [1]
    []) (.atom nJA_22 eJA_22)))

@[tmio M, powerlib_domain] theorem JA_22_eq {s : ℝ} (hs : 0 < s) :
    JA_22 s = PV0_1 s * T1_22 s + PV0_2 s * T2_22 s + PV0_3 s * T3_22 s := by
  rw [T1_22_val hs, T2_22_val hs, T3_22_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_22_eq (by decide +kernel)
  simp only [cJA_22_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_22, PV0_1, PV0_2, PV0_3, TV1_22, TV2_22, TV3_22]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_22_eq`. -/
def cJB_22_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_22 eTV3_22)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_22 eTV2_22)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_22 eTV1_22))) (.mul (.atom [1]
    []) (.atom nJB_22 eJB_22)))

@[tmio M, powerlib_domain] theorem JB_22_eq {s : ℝ} (hs : 0 < s) :
    JB_22 s = PV1_1 s * T1_22 s + PV1_2 s * T2_22 s + PV1_3 s * T3_22 s := by
  rw [T1_22_val hs, T2_22_val hs, T3_22_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_22_eq (by decide +kernel)
  simp only [cJB_22_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_22, PV1_1, PV1_2, PV1_3, TV1_22, TV2_22, TV3_22]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_13_eq`. -/
def cJA_13_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_13 eTV3_13)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_13 eTV2_13)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_13 eTV1_13))) (.mul (.atom [1]
    []) (.atom nJA_13 eJA_13)))

@[tmio M, powerlib_domain] theorem JA_13_eq {s : ℝ} (hs : 0 < s) :
    JA_13 s = PV0_1 s * T1_13 s + PV0_2 s * T2_13 s + PV0_3 s * T3_13 s := by
  rw [T1_13_val hs, T2_13_val hs, T3_13_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_13_eq (by decide +kernel)
  simp only [cJA_13_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_13, PV0_1, PV0_2, PV0_3, TV1_13, TV2_13, TV3_13]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_13_eq`. -/
def cJB_13_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_13 eTV3_13)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_13 eTV2_13)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_13 eTV1_13))) (.mul (.atom [1]
    []) (.atom nJB_13 eJB_13)))

@[tmio M, powerlib_domain] theorem JB_13_eq {s : ℝ} (hs : 0 < s) :
    JB_13 s = PV1_1 s * T1_13 s + PV1_2 s * T2_13 s + PV1_3 s * T3_13 s := by
  rw [T1_13_val hs, T2_13_val hs, T3_13_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_13_eq (by decide +kernel)
  simp only [cJB_13_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_13, PV1_1, PV1_2, PV1_3, TV1_13, TV2_13, TV3_13]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_04_eq`. -/
def cJA_04_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_04 eTV3_04)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_04 eTV2_04)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_04 eTV1_04))) (.mul (.atom [1]
    []) (.atom nJA_04 eJA_04)))

@[tmio M, powerlib_domain] theorem JA_04_eq {s : ℝ} (hs : 0 < s) :
    JA_04 s = PV0_1 s * T1_04 s + PV0_2 s * T2_04 s + PV0_3 s * T3_04 s := by
  rw [T1_04_val hs, T2_04_val hs, T3_04_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_04_eq (by decide +kernel)
  simp only [cJA_04_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_04, PV0_1, PV0_2, PV0_3, TV1_04, TV2_04, TV3_04]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_04_eq`. -/
def cJB_04_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_04 eTV3_04)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_04 eTV2_04)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_04 eTV1_04))) (.mul (.atom [1]
    []) (.atom nJB_04 eJB_04)))

@[tmio M, powerlib_domain] theorem JB_04_eq {s : ℝ} (hs : 0 < s) :
    JB_04 s = PV1_1 s * T1_04 s + PV1_2 s * T2_04 s + PV1_3 s * T3_04 s := by
  rw [T1_04_val hs, T2_04_val hs, T3_04_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_04_eq (by decide +kernel)
  simp only [cJB_04_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_04, PV1_1, PV1_2, PV1_3, TV1_04, TV2_04, TV3_04]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_50_eq`. -/
def cJA_50_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_50 eTV3_50)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_50 eTV2_50)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_50 eTV1_50))) (.mul (.atom [1]
    []) (.atom nJA_50 eJA_50)))

@[tmio M, powerlib_domain] theorem JA_50_eq {s : ℝ} (hs : 0 < s) :
    JA_50 s = PV0_1 s * T1_50 s + PV0_2 s * T2_50 s + PV0_3 s * T3_50 s := by
  rw [T1_50_val hs, T2_50_val hs, T3_50_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_50_eq (by decide +kernel)
  simp only [cJA_50_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_50, PV0_1, PV0_2, PV0_3, TV1_50, TV2_50, TV3_50]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_50_eq`. -/
def cJB_50_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_50 eTV3_50)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_50 eTV2_50)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_50 eTV1_50))) (.mul (.atom [1]
    []) (.atom nJB_50 eJB_50)))

@[tmio M, powerlib_domain] theorem JB_50_eq {s : ℝ} (hs : 0 < s) :
    JB_50 s = PV1_1 s * T1_50 s + PV1_2 s * T2_50 s + PV1_3 s * T3_50 s := by
  rw [T1_50_val hs, T2_50_val hs, T3_50_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_50_eq (by decide +kernel)
  simp only [cJB_50_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_50, PV1_1, PV1_2, PV1_3, TV1_50, TV2_50, TV3_50]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_41_eq`. -/
def cJA_41_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_41 eTV3_41)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_41 eTV2_41)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_41 eTV1_41))) (.mul (.atom [1]
    []) (.atom nJA_41 eJA_41)))

@[tmio M, powerlib_domain] theorem JA_41_eq {s : ℝ} (hs : 0 < s) :
    JA_41 s = PV0_1 s * T1_41 s + PV0_2 s * T2_41 s + PV0_3 s * T3_41 s := by
  rw [T1_41_val hs, T2_41_val hs, T3_41_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_41_eq (by decide +kernel)
  simp only [cJA_41_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_41, PV0_1, PV0_2, PV0_3, TV1_41, TV2_41, TV3_41]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_41_eq`. -/
def cJB_41_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_41 eTV3_41)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_41 eTV2_41)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_41 eTV1_41))) (.mul (.atom [1]
    []) (.atom nJB_41 eJB_41)))

@[tmio M, powerlib_domain] theorem JB_41_eq {s : ℝ} (hs : 0 < s) :
    JB_41 s = PV1_1 s * T1_41 s + PV1_2 s * T2_41 s + PV1_3 s * T3_41 s := by
  rw [T1_41_val hs, T2_41_val hs, T3_41_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_41_eq (by decide +kernel)
  simp only [cJB_41_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_41, PV1_1, PV1_2, PV1_3, TV1_41, TV2_41, TV3_41]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_32_eq`. -/
def cJA_32_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_32 eTV3_32)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_32 eTV2_32)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_32 eTV1_32))) (.mul (.atom [1]
    []) (.atom nJA_32 eJA_32)))

@[tmio M, powerlib_domain] theorem JA_32_eq {s : ℝ} (hs : 0 < s) :
    JA_32 s = PV0_1 s * T1_32 s + PV0_2 s * T2_32 s + PV0_3 s * T3_32 s := by
  rw [T1_32_val hs, T2_32_val hs, T3_32_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_32_eq (by decide +kernel)
  simp only [cJA_32_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_32, PV0_1, PV0_2, PV0_3, TV1_32, TV2_32, TV3_32]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_32_eq`. -/
def cJB_32_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_32 eTV3_32)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_32 eTV2_32)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_32 eTV1_32))) (.mul (.atom [1]
    []) (.atom nJB_32 eJB_32)))

@[tmio M, powerlib_domain] theorem JB_32_eq {s : ℝ} (hs : 0 < s) :
    JB_32 s = PV1_1 s * T1_32 s + PV1_2 s * T2_32 s + PV1_3 s * T3_32 s := by
  rw [T1_32_val hs, T2_32_val hs, T3_32_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_32_eq (by decide +kernel)
  simp only [cJB_32_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_32, PV1_1, PV1_2, PV1_3, TV1_32, TV2_32, TV3_32]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_23_eq`. -/
def cJA_23_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_23 eTV3_23)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_23 eTV2_23)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_23 eTV1_23))) (.mul (.atom [1]
    []) (.atom nJA_23 eJA_23)))

@[tmio M, powerlib_domain] theorem JA_23_eq {s : ℝ} (hs : 0 < s) :
    JA_23 s = PV0_1 s * T1_23 s + PV0_2 s * T2_23 s + PV0_3 s * T3_23 s := by
  rw [T1_23_val hs, T2_23_val hs, T3_23_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_23_eq (by decide +kernel)
  simp only [cJA_23_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_23, PV0_1, PV0_2, PV0_3, TV1_23, TV2_23, TV3_23]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_23_eq`. -/
def cJB_23_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_23 eTV3_23)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_23 eTV2_23)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_23 eTV1_23))) (.mul (.atom [1]
    []) (.atom nJB_23 eJB_23)))

@[tmio M, powerlib_domain] theorem JB_23_eq {s : ℝ} (hs : 0 < s) :
    JB_23 s = PV1_1 s * T1_23 s + PV1_2 s * T2_23 s + PV1_3 s * T3_23 s := by
  rw [T1_23_val hs, T2_23_val hs, T3_23_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_23_eq (by decide +kernel)
  simp only [cJB_23_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_23, PV1_1, PV1_2, PV1_3, TV1_23, TV2_23, TV3_23]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_14_eq`. -/
def cJA_14_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_14 eTV3_14)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_14 eTV2_14)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_14 eTV1_14))) (.mul (.atom [1]
    []) (.atom nJA_14 eJA_14)))

@[tmio M, powerlib_domain] theorem JA_14_eq {s : ℝ} (hs : 0 < s) :
    JA_14 s = PV0_1 s * T1_14 s + PV0_2 s * T2_14 s + PV0_3 s * T3_14 s := by
  rw [T1_14_val hs, T2_14_val hs, T3_14_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_14_eq (by decide +kernel)
  simp only [cJA_14_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_14, PV0_1, PV0_2, PV0_3, TV1_14, TV2_14, TV3_14]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_14_eq`. -/
def cJB_14_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_14 eTV3_14)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_14 eTV2_14)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_14 eTV1_14))) (.mul (.atom [1]
    []) (.atom nJB_14 eJB_14)))

@[tmio M, powerlib_domain] theorem JB_14_eq {s : ℝ} (hs : 0 < s) :
    JB_14 s = PV1_1 s * T1_14 s + PV1_2 s * T2_14 s + PV1_3 s * T3_14 s := by
  rw [T1_14_val hs, T2_14_val hs, T3_14_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_14_eq (by decide +kernel)
  simp only [cJB_14_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_14, PV1_1, PV1_2, PV1_3, TV1_14, TV2_14, TV3_14]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JA_05_eq`. -/
def cJA_05_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV0_3 ePV0_3)) (.atom
    nTV3_05 eTV3_05)) (.mul (.mul (.atom [-1] []) (.atom nPV0_2 ePV0_2)) (.atom nTV2_05 eTV2_05)))
    (.mul (.mul (.atom [-1] []) (.atom nPV0_1 ePV0_1)) (.atom nTV1_05 eTV1_05))) (.mul (.atom [1]
    []) (.atom nJA_05 eJA_05)))

@[tmio M, powerlib_domain] theorem JA_05_eq {s : ℝ} (hs : 0 < s) :
    JA_05 s = PV0_1 s * T1_05 s + PV0_2 s * T2_05 s + PV0_3 s * T3_05 s := by
  rw [T1_05_val hs, T2_05_val hs, T3_05_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJA_05_eq (by decide +kernel)
  simp only [cJA_05_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_05, PV0_1, PV0_2, PV0_3, TV1_05, TV2_05, TV3_05]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `JB_05_eq`. -/
def cJB_05_eq : PExpr := (.add (.add (.add (.mul (.mul (.atom [-1] []) (.atom nPV1_3 ePV1_3)) (.atom
    nTV3_05 eTV3_05)) (.mul (.mul (.atom [-1] []) (.atom nPV1_2 ePV1_2)) (.atom nTV2_05 eTV2_05)))
    (.mul (.mul (.atom [-1] []) (.atom nPV1_1 ePV1_1)) (.atom nTV1_05 eTV1_05))) (.mul (.atom [1]
    []) (.atom nJB_05 eJB_05)))

@[tmio M, powerlib_domain] theorem JB_05_eq {s : ℝ} (hs : 0 < s) :
    JB_05 s = PV1_1 s * T1_05 s + PV1_2 s * T2_05 s + PV1_3 s * T3_05 s := by
  rw [T1_05_val hs, T2_05_val hs, T3_05_val hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cJB_05_eq (by decide +kernel)
  simp only [cJB_05_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_05, PV1_1, PV1_2, PV1_3, TV1_05, TV2_05, TV3_05]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_02_eq`. -/
def cHom2_02_eq : PExpr := (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nTV2_02
    eTV2_02)) (.mul (.atom [2, 1] []) (.atom nJB_02 eJB_02))) (.mul (.atom [-2, 1] []) (.atom nJA_02
    eJA_02))) (.mul (.atom [-1] []) (.atom nCM2_02 eCM2_02))) (.mul (.atom [-1] []) (.atom nCM1_11
    eCM1_11))) (.mul (.atom [0, 1] []) (.atom nCM1_02 eCM1_02)))

@[tmio M, powerlib_domain] theorem Hom2_02_eq {s : ℝ} (hs : 0 < s) :
    Hom2_02 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_02_eq (by decide +kernel)
  simp only [cHom2_02_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_11, CM2_02, Hom2_02, JA_02, JB_02, T2_02_val hs, TV2_02]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_03_eq`. -/
def cHom2_03_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom
    nTV2_03 eTV2_03)) (.mul (.atom [2, 1] []) (.atom nJB_03 eJB_03))) (.mul (.atom [-2, 1] [])
    (.atom nJA_03 eJA_03))) (.mul (.atom [-1] []) (.atom nCM2_03 eCM2_03))) (.mul (.atom [-1] [])
    (.atom nCM1_12 eCM1_12))) (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)) (.atom nJA_02
    eJA_02))) (.mul (.atom [0, 1] []) (.atom nCM1_03 eCM1_03))) (.mul (.mul (.atom [2] []) (.atom
    nCM1_02 eCM1_02)) (.atom nJB_02 eJB_02)))

@[tmio M, powerlib_domain] theorem Hom2_03_eq {s : ℝ} (hs : 0 < s) :
    Hom2_03 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_03_eq (by decide +kernel)
  simp only [cHom2_03_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_03, CM1_11, CM1_12, CM2_03, Hom2_03, JA_02, JA_03, JB_02, JB_03, T2_03_val
    hs, TV2_03]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_04_eq`. -/
def cHom2_04_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1]
    []) (.atom nTV2_04 eTV2_04)) (.mul (.atom [2, 1] []) (.atom nJB_04 eJB_04))) (.mul (.atom [-2,
    1] []) (.atom nJA_04 eJA_04))) (.mul (.atom [-1] []) (.atom nCM2_04 eCM2_04))) (.mul (.atom [-1]
    []) (.atom nCM1_13 eCM1_13))) (.mul (.mul (.atom [1] []) (.atom nCM1_12 eCM1_12)) (.atom nJA_02
    eJA_02))) (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)) (.atom nJA_03 eJA_03))) (.mul
    (.atom [0, 1] []) (.atom nCM1_04 eCM1_04))) (.mul (.mul (.atom [3] []) (.atom nCM1_03 eCM1_03))
    (.atom nJB_02 eJB_02))) (.mul (.mul (.atom [2] []) (.atom nCM1_02 eCM1_02)) (.atom nJB_03
    eJB_03)))

@[tmio M, powerlib_domain] theorem Hom2_04_eq {s : ℝ} (hs : 0 < s) :
    Hom2_04 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_04_eq (by decide +kernel)
  simp only [cHom2_04_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_03, CM1_04, CM1_11, CM1_12, CM1_13, CM2_04, Hom2_04, JA_02, JA_03, JA_04,
    JB_02, JB_03, JB_04, T2_04_val hs, TV2_04]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_11_eq`. -/
def cHom2_11_eq : PExpr := (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nTV2_11
    eTV2_11)) (.mul (.atom [2, 1] []) (.atom nJB_11 eJB_11))) (.mul (.atom [-2, 1] []) (.atom nJA_11
    eJA_11))) (.mul (.atom [-1] []) (.atom nCM2_11 eCM2_11))) (.mul (.atom [-2] []) (.atom nCM1_20
    eCM1_20))) (.mul (.atom [0, 1] []) (.atom nCM1_11 eCM1_11))) (.mul (.atom [2] []) (.atom nCM1_02
    eCM1_02)))

@[tmio M, powerlib_domain] theorem Hom2_11_eq {s : ℝ} (hs : 0 < s) :
    Hom2_11 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_11_eq (by decide +kernel)
  simp only [cHom2_11_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_11, CM1_20, CM2_11, Hom2_11, JA_11, JB_11, T2_11_val hs, TV2_11]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_12_eq`. -/
def cHom2_12_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom
    [-1] []) (.atom nTV2_12 eTV2_12)) (.mul (.atom [2, 1] []) (.atom nJB_12 eJB_12))) (.mul (.atom
    [-2, 1] []) (.atom nJA_12 eJA_12))) (.mul (.atom [-1] []) (.atom nCM2_12 eCM2_12))) (.mul (.atom
    [-2] []) (.atom nCM1_21 eCM1_21))) (.mul (.mul (.atom [2] []) (.atom nCM1_20 eCM1_20)) (.atom
    nJA_02 eJA_02))) (.mul (.atom [0, 1] []) (.atom nCM1_12 eCM1_12))) (.mul (.mul (.atom [1] [])
    (.atom nCM1_11 eCM1_11)) (.atom nJB_02 eJB_02))) (.mul (.mul (.atom [1] []) (.atom nCM1_11
    eCM1_11)) (.atom nJA_11 eJA_11))) (.mul (.atom [3] []) (.atom nCM1_03 eCM1_03))) (.mul (.mul
    (.atom [2] []) (.atom nCM1_02 eCM1_02)) (.atom nJB_11 eJB_11)))

@[tmio M, powerlib_domain] theorem Hom2_12_eq {s : ℝ} (hs : 0 < s) :
    Hom2_12 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_12_eq (by decide +kernel)
  simp only [cHom2_12_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_03, CM1_11, CM1_12, CM1_20, CM1_21, CM2_12, Hom2_12, JA_02, JA_11, JA_12,
    JB_02, JB_11, JB_12, T2_12_val hs, TV2_12]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_13_eq`. -/
def cHom2_13_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.mul (.atom [-1] []) (.atom nTV2_13 eTV2_13)) (.mul (.atom [2, 1] []) (.atom nJB_13
    eJB_13))) (.mul (.atom [-2, 1] []) (.atom nJA_13 eJA_13))) (.mul (.atom [-1] []) (.atom nCM2_13
    eCM2_13))) (.mul (.atom [-2] []) (.atom nCM1_22 eCM1_22))) (.mul (.mul (.atom [2] []) (.atom
    nCM1_21 eCM1_21)) (.atom nJA_02 eJA_02))) (.mul (.mul (.atom [2] []) (.atom nCM1_20 eCM1_20))
    (.atom nJA_03 eJA_03))) (.mul (.atom [0, 1] []) (.atom nCM1_13 eCM1_13))) (.mul (.mul (.atom [2]
    []) (.atom nCM1_12 eCM1_12)) (.atom nJB_02 eJB_02))) (.mul (.mul (.atom [1] []) (.atom nCM1_12
    eCM1_12)) (.atom nJA_11 eJA_11))) (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)) (.atom
    nJB_03 eJB_03))) (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)) (.atom nJA_12 eJA_12)))
    (.mul (.atom [4] []) (.atom nCM1_04 eCM1_04))) (.mul (.mul (.atom [3] []) (.atom nCM1_03
    eCM1_03)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [2] []) (.atom nCM1_02 eCM1_02)) (.atom
    nJB_12 eJB_12)))

@[tmio M, powerlib_domain] theorem Hom2_13_eq {s : ℝ} (hs : 0 < s) :
    Hom2_13 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_13_eq (by decide +kernel)
  simp only [cHom2_13_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_03, CM1_04, CM1_11, CM1_12, CM1_13, CM1_20, CM1_21, CM1_22, CM2_13,
    Hom2_13, JA_02, JA_03, JA_11, JA_12, JA_13, JB_02, JB_03, JB_11, JB_12, JB_13, T2_13_val hs,
    TV2_13]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_20_eq`. -/
def cHom2_20_eq : PExpr := (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nTV2_20
    eTV2_20)) (.mul (.atom [2, 1] []) (.atom nJB_20 eJB_20))) (.mul (.atom [-2, 1] []) (.atom nJA_20
    eJA_20))) (.mul (.atom [-1] []) (.atom nCM2_20 eCM2_20))) (.mul (.atom [0, 1] []) (.atom nCM1_20
    eCM1_20))) (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)))

@[tmio M, powerlib_domain] theorem Hom2_20_eq {s : ℝ} (hs : 0 < s) :
    Hom2_20 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_20_eq (by decide +kernel)
  simp only [cHom2_20_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_11, CM1_20, CM2_20, Hom2_20, JA_20, JB_20, T2_20_val hs, TV2_20]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_21_eq`. -/
def cHom2_21_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom
    [-1] []) (.atom nTV2_21 eTV2_21)) (.mul (.atom [2, 1] []) (.atom nJB_21 eJB_21))) (.mul (.atom
    [-2, 1] []) (.atom nJA_21 eJA_21))) (.mul (.atom [-1] []) (.atom nCM2_21 eCM2_21))) (.mul (.atom
    [-3] []) (.atom nCM1_30 eCM1_30))) (.mul (.atom [0, 1] []) (.atom nCM1_21 eCM1_21))) (.mul (.mul
    (.atom [2] []) (.atom nCM1_20 eCM1_20)) (.atom nJA_11 eJA_11))) (.mul (.atom [2] []) (.atom
    nCM1_12 eCM1_12))) (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)) (.atom nJB_11 eJB_11)))
    (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom
    [2] []) (.atom nCM1_02 eCM1_02)) (.atom nJB_20 eJB_20)))

@[tmio M, powerlib_domain] theorem Hom2_21_eq {s : ℝ} (hs : 0 < s) :
    Hom2_21 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_21_eq (by decide +kernel)
  simp only [cHom2_21_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_11, CM1_12, CM1_20, CM1_21, CM1_30, CM2_21, Hom2_21, JA_11, JA_20, JA_21,
    JB_11, JB_20, JB_21, T2_21_val hs, TV2_21]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_22_eq`. -/
def cHom2_22_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nTV2_22 eTV2_22)) (.mul (.atom [2, 1] [])
    (.atom nJB_22 eJB_22))) (.mul (.atom [-2, 1] []) (.atom nJA_22 eJA_22))) (.mul (.atom [-1] [])
    (.atom nCM2_22 eCM2_22))) (.mul (.atom [-3] []) (.atom nCM1_31 eCM1_31))) (.mul (.mul (.atom [3]
    []) (.atom nCM1_30 eCM1_30)) (.atom nJA_02 eJA_02))) (.mul (.atom [0, 1] []) (.atom nCM1_22
    eCM1_22))) (.mul (.mul (.atom [1] []) (.atom nCM1_21 eCM1_21)) (.atom nJB_02 eJB_02))) (.mul
    (.mul (.atom [2] []) (.atom nCM1_21 eCM1_21)) (.atom nJA_11 eJA_11))) (.mul (.mul (.atom [2] [])
    (.atom nCM1_20 eCM1_20)) (.atom nJA_12 eJA_12))) (.mul (.atom [3] []) (.atom nCM1_13 eCM1_13)))
    (.mul (.mul (.atom [2] []) (.atom nCM1_12 eCM1_12)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom
    [1] []) (.atom nCM1_12 eCM1_12)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [1] []) (.atom
    nCM1_11 eCM1_11)) (.atom nJB_12 eJB_12))) (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11))
    (.atom nJA_21 eJA_21))) (.mul (.mul (.atom [3] []) (.atom nCM1_03 eCM1_03)) (.atom nJB_20
    eJB_20))) (.mul (.mul (.atom [2] []) (.atom nCM1_02 eCM1_02)) (.atom nJB_21 eJB_21)))

@[tmio M, powerlib_domain] theorem Hom2_22_eq {s : ℝ} (hs : 0 < s) :
    Hom2_22 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_22_eq (by decide +kernel)
  simp only [cHom2_22_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_03, CM1_11, CM1_12, CM1_13, CM1_20, CM1_21, CM1_22, CM1_30, CM1_31, CM2_22,
    Hom2_22, JA_02, JA_11, JA_12, JA_20, JA_21, JA_22, JB_02, JB_11, JB_12, JB_20, JB_21, JB_22,
    T2_22_val hs, TV2_22]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_30_eq`. -/
def cHom2_30_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom
    nTV2_30 eTV2_30)) (.mul (.atom [2, 1] []) (.atom nJB_30 eJB_30))) (.mul (.atom [-2, 1] [])
    (.atom nJA_30 eJA_30))) (.mul (.atom [-1] []) (.atom nCM2_30 eCM2_30))) (.mul (.atom [0, 1] [])
    (.atom nCM1_30 eCM1_30))) (.mul (.atom [1] []) (.atom nCM1_21 eCM1_21))) (.mul (.mul (.atom [2]
    []) (.atom nCM1_20 eCM1_20)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [1] []) (.atom nCM1_11
    eCM1_11)) (.atom nJB_20 eJB_20)))

@[tmio M, powerlib_domain] theorem Hom2_30_eq {s : ℝ} (hs : 0 < s) :
    Hom2_30 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_30_eq (by decide +kernel)
  simp only [cHom2_30_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_11, CM1_20, CM1_21, CM1_30, CM2_30, Hom2_30, JA_20, JA_30, JB_20, JB_30, T2_30_val
    hs, TV2_30]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_31_eq`. -/
def cHom2_31_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.mul (.atom [-1] []) (.atom nTV2_31 eTV2_31)) (.mul (.atom [2, 1] []) (.atom nJB_31
    eJB_31))) (.mul (.atom [-2, 1] []) (.atom nJA_31 eJA_31))) (.mul (.atom [-1] []) (.atom nCM2_31
    eCM2_31))) (.mul (.atom [-4] []) (.atom nCM1_40 eCM1_40))) (.mul (.atom [0, 1] []) (.atom
    nCM1_31 eCM1_31))) (.mul (.mul (.atom [3] []) (.atom nCM1_30 eCM1_30)) (.atom nJA_11 eJA_11)))
    (.mul (.atom [2] []) (.atom nCM1_22 eCM1_22))) (.mul (.mul (.atom [1] []) (.atom nCM1_21
    eCM1_21)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [2] []) (.atom nCM1_21 eCM1_21)) (.atom
    nJA_20 eJA_20))) (.mul (.mul (.atom [2] []) (.atom nCM1_20 eCM1_20)) (.atom nJA_21 eJA_21)))
    (.mul (.mul (.atom [2] []) (.atom nCM1_12 eCM1_12)) (.atom nJB_20 eJB_20))) (.mul (.mul (.atom
    [1] []) (.atom nCM1_11 eCM1_11)) (.atom nJB_21 eJB_21))) (.mul (.mul (.atom [1] []) (.atom
    nCM1_11 eCM1_11)) (.atom nJA_30 eJA_30))) (.mul (.mul (.atom [2] []) (.atom nCM1_02 eCM1_02))
    (.atom nJB_30 eJB_30)))

@[tmio M, powerlib_domain] theorem Hom2_31_eq {s : ℝ} (hs : 0 < s) :
    Hom2_31 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_31_eq (by decide +kernel)
  simp only [cHom2_31_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_02, CM1_11, CM1_12, CM1_20, CM1_21, CM1_22, CM1_30, CM1_31, CM1_40, CM2_31,
    Hom2_31, JA_11, JA_20, JA_21, JA_30, JA_31, JB_11, JB_20, JB_21, JB_30, JB_31, T2_31_val hs,
    TV2_31]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom2_40_eq`. -/
def cHom2_40_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1]
    []) (.atom nTV2_40 eTV2_40)) (.mul (.atom [2, 1] []) (.atom nJB_40 eJB_40))) (.mul (.atom [-2,
    1] []) (.atom nJA_40 eJA_40))) (.mul (.atom [-1] []) (.atom nCM2_40 eCM2_40))) (.mul (.atom [0,
    1] []) (.atom nCM1_40 eCM1_40))) (.mul (.atom [1] []) (.atom nCM1_31 eCM1_31))) (.mul (.mul
    (.atom [3] []) (.atom nCM1_30 eCM1_30)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [1] [])
    (.atom nCM1_21 eCM1_21)) (.atom nJB_20 eJB_20))) (.mul (.mul (.atom [2] []) (.atom nCM1_20
    eCM1_20)) (.atom nJA_30 eJA_30))) (.mul (.mul (.atom [1] []) (.atom nCM1_11 eCM1_11)) (.atom
    nJB_30 eJB_30)))

@[tmio M, powerlib_domain] theorem Hom2_40_eq {s : ℝ} (hs : 0 < s) :
    Hom2_40 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom2_40_eq (by decide +kernel)
  simp only [cHom2_40_eq, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [CM1_11, CM1_20, CM1_21, CM1_30, CM1_31, CM1_40, CM2_40, Hom2_40, JA_20, JA_30, JA_40,
    JB_20, JB_30, JB_40, T2_40_val hs, TV2_40]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_02_eq`. -/
def cHom3_02_eq : PExpr := (.add (.add (.add (.add (.add (.mul (.atom [2, 1, 1] []) (.atom nJB_02
    eJB_02)) (.mul (.atom [2, -1, 1] []) (.atom nJA_02 eJA_02))) (.mul (.atom [-1] []) (.atom
    nCM2_11 eCM2_11))) (.mul (.atom [0, 1] []) (.atom nCM2_02 eCM2_02))) (.mul (.atom [2] [0, 0, 0,
    1]) (.atom nCM2_02 eCM2_02))) (.mul (.atom [2] []) (.atom nCM1_02 eCM1_02)))

@[tmio M, powerlib_domain] theorem Hom3_02_eq {s : ℝ} (hs : 0 < s) :
    Hom3_02 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_02_eq (by decide +kernel)
  simp only [cHom3_02_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_02, CM2_02, CM2_11, Hom3_02, JA_02, JB_02, T3_02]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_03_eq`. -/
def cHom3_03_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] [])
    (.atom nTV3_03 eTV3_03)) (.mul (.atom [2, 1, 1] []) (.atom nJB_03 eJB_03))) (.mul (.atom [2, -1,
    1] []) (.atom nJA_03 eJA_03))) (.mul (.atom [-1] []) (.atom nCM2_12 eCM2_12))) (.mul (.mul
    (.atom [1] []) (.atom nCM2_11 eCM2_11)) (.atom nJA_02 eJA_02))) (.mul (.atom [0, 1] []) (.atom
    nCM2_03 eCM2_03))) (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_03 eCM2_03))) (.mul (.mul (.atom
    [2] []) (.atom nCM2_02 eCM2_02)) (.atom nJB_02 eJB_02))) (.mul (.atom [2] []) (.atom nCM1_03
    eCM1_03)))

@[tmio M, powerlib_domain] theorem Hom3_03_eq {s : ℝ} (hs : 0 < s) :
    Hom3_03 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_03_eq (by decide +kernel)
  simp only [cHom3_03_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_03, CM2_02, CM2_03, CM2_11, CM2_12, Hom3_03, JA_02, JA_03, JB_02, JB_03, T3_03_val
    hs, TV3_03]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_04_eq`. -/
def cHom3_04_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom
    [-1] []) (.atom nTV3_04 eTV3_04)) (.mul (.atom [2, 1, 1] []) (.atom nJB_04 eJB_04))) (.mul
    (.atom [2, -1, 1] []) (.atom nJA_04 eJA_04))) (.mul (.atom [-1] []) (.atom nCM2_13 eCM2_13)))
    (.mul (.mul (.atom [1] []) (.atom nCM2_12 eCM2_12)) (.atom nJA_02 eJA_02))) (.mul (.mul (.atom
    [1] []) (.atom nCM2_11 eCM2_11)) (.atom nJA_03 eJA_03))) (.mul (.atom [0, 1] []) (.atom nCM2_04
    eCM2_04))) (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_04 eCM2_04))) (.mul (.mul (.atom [3] [])
    (.atom nCM2_03 eCM2_03)) (.atom nJB_02 eJB_02))) (.mul (.mul (.atom [2] []) (.atom nCM2_02
    eCM2_02)) (.atom nJB_03 eJB_03))) (.mul (.atom [2] []) (.atom nCM1_04 eCM1_04)))

@[tmio M, powerlib_domain] theorem Hom3_04_eq {s : ℝ} (hs : 0 < s) :
    Hom3_04 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_04_eq (by decide +kernel)
  simp only [cHom3_04_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_04, CM2_02, CM2_03, CM2_04, CM2_11, CM2_12, CM2_13, Hom3_04, JA_02, JA_03, JA_04,
    JB_02, JB_03, JB_04, T3_04_val hs, TV3_04]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_11_eq`. -/
def cHom3_11_eq : PExpr := (.add (.add (.add (.add (.add (.add (.mul (.atom [2, 1, 1] []) (.atom
    nJB_11 eJB_11)) (.mul (.atom [2, -1, 1] []) (.atom nJA_11 eJA_11))) (.mul (.atom [-2] []) (.atom
    nCM2_20 eCM2_20))) (.mul (.atom [0, 1] []) (.atom nCM2_11 eCM2_11))) (.mul (.atom [2] [0, 0, 0,
    1]) (.atom nCM2_11 eCM2_11))) (.mul (.atom [2] []) (.atom nCM2_02 eCM2_02))) (.mul (.atom [2]
    []) (.atom nCM1_11 eCM1_11)))

@[tmio M, powerlib_domain] theorem Hom3_11_eq {s : ℝ} (hs : 0 < s) :
    Hom3_11 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_11_eq (by decide +kernel)
  simp only [cHom3_11_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_11, CM2_02, CM2_11, CM2_20, Hom3_11, JA_11, JB_11, T3_11]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_12_eq`. -/
def cHom3_12_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul
    (.atom [-1] []) (.atom nTV3_12 eTV3_12)) (.mul (.atom [2, 1, 1] []) (.atom nJB_12 eJB_12)))
    (.mul (.atom [2, -1, 1] []) (.atom nJA_12 eJA_12))) (.mul (.atom [-2] []) (.atom nCM2_21
    eCM2_21))) (.mul (.mul (.atom [2] []) (.atom nCM2_20 eCM2_20)) (.atom nJA_02 eJA_02))) (.mul
    (.atom [0, 1] []) (.atom nCM2_12 eCM2_12))) (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_12
    eCM2_12))) (.mul (.mul (.atom [1] []) (.atom nCM2_11 eCM2_11)) (.atom nJB_02 eJB_02))) (.mul
    (.mul (.atom [1] []) (.atom nCM2_11 eCM2_11)) (.atom nJA_11 eJA_11))) (.mul (.atom [3] [])
    (.atom nCM2_03 eCM2_03))) (.mul (.mul (.atom [2] []) (.atom nCM2_02 eCM2_02)) (.atom nJB_11
    eJB_11))) (.mul (.atom [2] []) (.atom nCM1_12 eCM1_12)))

@[tmio M, powerlib_domain] theorem Hom3_12_eq {s : ℝ} (hs : 0 < s) :
    Hom3_12 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_12_eq (by decide +kernel)
  simp only [cHom3_12_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_12, CM2_02, CM2_03, CM2_11, CM2_12, CM2_20, CM2_21, Hom3_12, JA_02, JA_11, JA_12,
    JB_02, JB_11, JB_12, T3_12_val hs, TV3_12]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_13_eq`. -/
def cHom3_13_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.mul (.atom [-1] []) (.atom nTV3_13 eTV3_13)) (.mul (.atom [2, 1, 1] [])
    (.atom nJB_13 eJB_13))) (.mul (.atom [2, -1, 1] []) (.atom nJA_13 eJA_13))) (.mul (.atom [-2]
    []) (.atom nCM2_22 eCM2_22))) (.mul (.mul (.atom [2] []) (.atom nCM2_21 eCM2_21)) (.atom nJA_02
    eJA_02))) (.mul (.mul (.atom [2] []) (.atom nCM2_20 eCM2_20)) (.atom nJA_03 eJA_03))) (.mul
    (.atom [0, 1] []) (.atom nCM2_13 eCM2_13))) (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_13
    eCM2_13))) (.mul (.mul (.atom [2] []) (.atom nCM2_12 eCM2_12)) (.atom nJB_02 eJB_02))) (.mul
    (.mul (.atom [1] []) (.atom nCM2_12 eCM2_12)) (.atom nJA_11 eJA_11))) (.mul (.mul (.atom [1] [])
    (.atom nCM2_11 eCM2_11)) (.atom nJB_03 eJB_03))) (.mul (.mul (.atom [1] []) (.atom nCM2_11
    eCM2_11)) (.atom nJA_12 eJA_12))) (.mul (.atom [4] []) (.atom nCM2_04 eCM2_04))) (.mul (.mul
    (.atom [3] []) (.atom nCM2_03 eCM2_03)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [2] [])
    (.atom nCM2_02 eCM2_02)) (.atom nJB_12 eJB_12))) (.mul (.atom [2] []) (.atom nCM1_13 eCM1_13)))

@[tmio M, powerlib_domain] theorem Hom3_13_eq {s : ℝ} (hs : 0 < s) :
    Hom3_13 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_13_eq (by decide +kernel)
  simp only [cHom3_13_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_13, CM2_02, CM2_03, CM2_04, CM2_11, CM2_12, CM2_13, CM2_20, CM2_21, CM2_22,
    Hom3_13, JA_02, JA_03, JA_11, JA_12, JA_13, JB_02, JB_03, JB_11, JB_12, JB_13, T3_13_val hs,
    TV3_13]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_20_eq`. -/
def cHom3_20_eq : PExpr := (.add (.add (.add (.add (.add (.mul (.atom [2, 1, 1] []) (.atom nJB_20
    eJB_20)) (.mul (.atom [2, -1, 1] []) (.atom nJA_20 eJA_20))) (.mul (.atom [0, 1] []) (.atom
    nCM2_20 eCM2_20))) (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_20 eCM2_20))) (.mul (.atom [1] [])
    (.atom nCM2_11 eCM2_11))) (.mul (.atom [2] []) (.atom nCM1_20 eCM1_20)))

@[tmio M, powerlib_domain] theorem Hom3_20_eq {s : ℝ} (hs : 0 < s) :
    Hom3_20 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_20_eq (by decide +kernel)
  simp only [cHom3_20_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_20, CM2_11, CM2_20, Hom3_20, JA_20, JB_20, T3_20]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_21_eq`. -/
def cHom3_21_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul
    (.atom [-1] []) (.atom nTV3_21 eTV3_21)) (.mul (.atom [2, 1, 1] []) (.atom nJB_21 eJB_21)))
    (.mul (.atom [2, -1, 1] []) (.atom nJA_21 eJA_21))) (.mul (.atom [-3] []) (.atom nCM2_30
    eCM2_30))) (.mul (.atom [0, 1] []) (.atom nCM2_21 eCM2_21))) (.mul (.atom [2] [0, 0, 0, 1])
    (.atom nCM2_21 eCM2_21))) (.mul (.mul (.atom [2] []) (.atom nCM2_20 eCM2_20)) (.atom nJA_11
    eJA_11))) (.mul (.atom [2] []) (.atom nCM2_12 eCM2_12))) (.mul (.mul (.atom [1] []) (.atom
    nCM2_11 eCM2_11)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [1] []) (.atom nCM2_11 eCM2_11))
    (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [2] []) (.atom nCM2_02 eCM2_02)) (.atom nJB_20
    eJB_20))) (.mul (.atom [2] []) (.atom nCM1_21 eCM1_21)))

@[tmio M, powerlib_domain] theorem Hom3_21_eq {s : ℝ} (hs : 0 < s) :
    Hom3_21 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_21_eq (by decide +kernel)
  simp only [cHom3_21_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_21, CM2_02, CM2_11, CM2_12, CM2_20, CM2_21, CM2_30, Hom3_21, JA_11, JA_20, JA_21,
    JB_11, JB_20, JB_21, T3_21_val hs, TV3_21]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_22_eq`. -/
def cHom3_22_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nTV3_22 eTV3_22)) (.mul (.atom [2, 1,
    1] []) (.atom nJB_22 eJB_22))) (.mul (.atom [2, -1, 1] []) (.atom nJA_22 eJA_22))) (.mul (.atom
    [-3] []) (.atom nCM2_31 eCM2_31))) (.mul (.mul (.atom [3] []) (.atom nCM2_30 eCM2_30)) (.atom
    nJA_02 eJA_02))) (.mul (.atom [0, 1] []) (.atom nCM2_22 eCM2_22))) (.mul (.atom [2] [0, 0, 0,
    1]) (.atom nCM2_22 eCM2_22))) (.mul (.mul (.atom [1] []) (.atom nCM2_21 eCM2_21)) (.atom nJB_02
    eJB_02))) (.mul (.mul (.atom [2] []) (.atom nCM2_21 eCM2_21)) (.atom nJA_11 eJA_11))) (.mul
    (.mul (.atom [2] []) (.atom nCM2_20 eCM2_20)) (.atom nJA_12 eJA_12))) (.mul (.atom [3] [])
    (.atom nCM2_13 eCM2_13))) (.mul (.mul (.atom [2] []) (.atom nCM2_12 eCM2_12)) (.atom nJB_11
    eJB_11))) (.mul (.mul (.atom [1] []) (.atom nCM2_12 eCM2_12)) (.atom nJA_20 eJA_20))) (.mul
    (.mul (.atom [1] []) (.atom nCM2_11 eCM2_11)) (.atom nJB_12 eJB_12))) (.mul (.mul (.atom [1] [])
    (.atom nCM2_11 eCM2_11)) (.atom nJA_21 eJA_21))) (.mul (.mul (.atom [3] []) (.atom nCM2_03
    eCM2_03)) (.atom nJB_20 eJB_20))) (.mul (.mul (.atom [2] []) (.atom nCM2_02 eCM2_02)) (.atom
    nJB_21 eJB_21))) (.mul (.atom [2] []) (.atom nCM1_22 eCM1_22)))

@[tmio M, powerlib_domain] theorem Hom3_22_eq {s : ℝ} (hs : 0 < s) :
    Hom3_22 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_22_eq (by decide +kernel)
  simp only [cHom3_22_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_22, CM2_02, CM2_03, CM2_11, CM2_12, CM2_13, CM2_20, CM2_21, CM2_22, CM2_30, CM2_31,
    Hom3_22, JA_02, JA_11, JA_12, JA_20, JA_21, JA_22, JB_02, JB_11, JB_12, JB_20, JB_21, JB_22,
    T3_22_val hs, TV3_22]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_30_eq`. -/
def cHom3_30_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] [])
    (.atom nTV3_30 eTV3_30)) (.mul (.atom [2, 1, 1] []) (.atom nJB_30 eJB_30))) (.mul (.atom [2, -1,
    1] []) (.atom nJA_30 eJA_30))) (.mul (.atom [0, 1] []) (.atom nCM2_30 eCM2_30))) (.mul (.atom
    [2] [0, 0, 0, 1]) (.atom nCM2_30 eCM2_30))) (.mul (.atom [1] []) (.atom nCM2_21 eCM2_21))) (.mul
    (.mul (.atom [2] []) (.atom nCM2_20 eCM2_20)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [1] [])
    (.atom nCM2_11 eCM2_11)) (.atom nJB_20 eJB_20))) (.mul (.atom [2] []) (.atom nCM1_30 eCM1_30)))

@[tmio M, powerlib_domain] theorem Hom3_30_eq {s : ℝ} (hs : 0 < s) :
    Hom3_30 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_30_eq (by decide +kernel)
  simp only [cHom3_30_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_30, CM2_11, CM2_20, CM2_21, CM2_30, Hom3_30, JA_20, JA_30, JB_20, JB_30, T3_30_val
    hs, TV3_30]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_31_eq`. -/
def cHom3_31_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.mul (.atom [-1] []) (.atom nTV3_31 eTV3_31)) (.mul (.atom [2, 1, 1] [])
    (.atom nJB_31 eJB_31))) (.mul (.atom [2, -1, 1] []) (.atom nJA_31 eJA_31))) (.mul (.atom [-4]
    []) (.atom nCM2_40 eCM2_40))) (.mul (.atom [0, 1] []) (.atom nCM2_31 eCM2_31))) (.mul (.atom [2]
    [0, 0, 0, 1]) (.atom nCM2_31 eCM2_31))) (.mul (.mul (.atom [3] []) (.atom nCM2_30 eCM2_30))
    (.atom nJA_11 eJA_11))) (.mul (.atom [2] []) (.atom nCM2_22 eCM2_22))) (.mul (.mul (.atom [1]
    []) (.atom nCM2_21 eCM2_21)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [2] []) (.atom nCM2_21
    eCM2_21)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [2] []) (.atom nCM2_20 eCM2_20)) (.atom
    nJA_21 eJA_21))) (.mul (.mul (.atom [2] []) (.atom nCM2_12 eCM2_12)) (.atom nJB_20 eJB_20)))
    (.mul (.mul (.atom [1] []) (.atom nCM2_11 eCM2_11)) (.atom nJB_21 eJB_21))) (.mul (.mul (.atom
    [1] []) (.atom nCM2_11 eCM2_11)) (.atom nJA_30 eJA_30))) (.mul (.mul (.atom [2] []) (.atom
    nCM2_02 eCM2_02)) (.atom nJB_30 eJB_30))) (.mul (.atom [2] []) (.atom nCM1_31 eCM1_31)))

@[tmio M, powerlib_domain] theorem Hom3_31_eq {s : ℝ} (hs : 0 < s) :
    Hom3_31 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_31_eq (by decide +kernel)
  simp only [cHom3_31_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_31, CM2_02, CM2_11, CM2_12, CM2_20, CM2_21, CM2_22, CM2_30, CM2_31, CM2_40,
    Hom3_31, JA_11, JA_20, JA_21, JA_30, JA_31, JB_11, JB_20, JB_21, JB_30, JB_31, T3_31_val hs,
    TV3_31]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `Hom3_40_eq`. -/
def cHom3_40_eq : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom
    [-1] []) (.atom nTV3_40 eTV3_40)) (.mul (.atom [2, 1, 1] []) (.atom nJB_40 eJB_40))) (.mul
    (.atom [2, -1, 1] []) (.atom nJA_40 eJA_40))) (.mul (.atom [0, 1] []) (.atom nCM2_40 eCM2_40)))
    (.mul (.atom [2] [0, 0, 0, 1]) (.atom nCM2_40 eCM2_40))) (.mul (.atom [1] []) (.atom nCM2_31
    eCM2_31))) (.mul (.mul (.atom [3] []) (.atom nCM2_30 eCM2_30)) (.atom nJA_20 eJA_20))) (.mul
    (.mul (.atom [1] []) (.atom nCM2_21 eCM2_21)) (.atom nJB_20 eJB_20))) (.mul (.mul (.atom [2] [])
    (.atom nCM2_20 eCM2_20)) (.atom nJA_30 eJA_30))) (.mul (.mul (.atom [1] []) (.atom nCM2_11
    eCM2_11)) (.atom nJB_30 eJB_30))) (.mul (.atom [2] []) (.atom nCM1_40 eCM1_40)))

@[tmio M, powerlib_domain] theorem Hom3_40_eq {s : ℝ} (hs : 0 < s) :
    Hom3_40 s = 0 := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cHom3_40_eq (by decide +kernel)
  simp only [cHom3_40_eq, PExpr.val, zeval, bval_nil_right, div_one, bval_s] at h
  push_cast at h
  simp only [CM1_40, CM2_11, CM2_20, CM2_21, CM2_30, CM2_31, CM2_40, Hom3_40, JA_20, JA_30, JA_40,
    JB_20, JB_30, JB_40, T3_40_val hs, TV3_40]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_c30`. -/
def cjet_c30 : PExpr := (.add (.add (.add (.mul (.atom [-3] []) (.atom nLY_c30 eLY_c30)) (.mul
    (.atom [2] []) (.atom nJB_20 eJB_20))) (.mul (.atom [4] []) (.atom nJB_02 eJB_02))) (.mul (.atom
    [2] []) (.atom nJA_11 eJA_11)))

@[tmio M, powerlib_domain] theorem jet_c30 {s : ℝ} (hs : 0 < s) :
    (jet s).c30 1 = LY_c30 s := by
  rw [Jet.c30]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_c30 (by decide +kernel)
  simp only [cjet_c30, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_11, JB_02, JB_20, LY_c30]
  linear_combination (1 / 3 : ℝ) * h

/-- The certificate expression of `jet_c21`. -/
def cjet_c21 : PExpr := (.add (.mul (.atom [-1] []) (.atom nLY_c21 eLY_c21)) (.mul (.atom [-2] [])
    (.atom nJA_20 eJA_20)))

@[tmio M, powerlib_domain] theorem jet_c21 {s : ℝ} (hs : 0 < s) :
    (jet s).c21 1 = LY_c21 s := by
  rw [Jet.c21]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_c21 (by decide +kernel)
  simp only [cjet_c21, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_20, LY_c21]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_c12`. -/
def cjet_c12 : PExpr := (.add (.mul (.atom [-1] []) (.atom nLY_c12 eLY_c12)) (.mul (.atom [2] [])
    (.atom nJB_02 eJB_02)))

@[tmio M, powerlib_domain] theorem jet_c12 {s : ℝ} (hs : 0 < s) :
    (jet s).c12 1 = LY_c12 s := by
  rw [Jet.c12]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_c12 (by decide +kernel)
  simp only [cjet_c12, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JB_02, LY_c12]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_c03`. -/
def cjet_c03 : PExpr := (.add (.add (.add (.mul (.atom [-3] []) (.atom nLY_c03 eLY_c03)) (.mul
    (.atom [-2] []) (.atom nJB_11 eJB_11))) (.mul (.atom [-4] []) (.atom nJA_20 eJA_20))) (.mul
    (.atom [-2] []) (.atom nJA_02 eJA_02)))

@[tmio M, powerlib_domain] theorem jet_c03 {s : ℝ} (hs : 0 < s) :
    (jet s).c03 1 = LY_c03 s := by
  rw [Jet.c03]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_c03 (by decide +kernel)
  simp only [cjet_c03, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_20, JB_11, LY_c03]
  linear_combination (1 / 3 : ℝ) * h

/-- The certificate expression of `jet_d40`. -/
def cjet_d40 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.mul (.atom [-2] []) (.atom nLY_d40 eLY_d40)) (.mul (.atom [1] []) (.atom nJB_30
    eJB_30))) (.mul (.atom [1] []) (.atom nJB_12 eJB_12))) (.mul (.atom [-1] []) (.pow (.atom nJB_11
    eJB_11) 2))) (.mul (.mul (.atom [2] []) (.atom nJB_02 eJB_02)) (.atom nJB_20 eJB_20))) (.mul
    (.atom [2] []) (.pow (.atom nJB_02 eJB_02) 2))) (.mul (.atom [1] []) (.atom nJA_21 eJA_21)))
    (.mul (.mul (.atom [-3] []) (.atom nJA_20 eJA_20)) (.atom nJB_11 eJB_11))) (.mul (.atom [-2] [])
    (.pow (.atom nJA_20 eJA_20) 2))) (.mul (.mul (.atom [1] []) (.atom nJA_11 eJA_11)) (.atom nJB_20
    eJB_20))) (.mul (.mul (.atom [3] []) (.atom nJA_11 eJA_11)) (.atom nJB_02 eJB_02))) (.mul (.atom
    [1] []) (.pow (.atom nJA_11 eJA_11) 2))) (.mul (.atom [1] []) (.atom nJA_03 eJA_03))) (.mul
    (.mul (.atom [-1] []) (.atom nJA_02 eJA_02)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [-2] [])
    (.atom nJA_02 eJA_02)) (.atom nJA_20 eJA_20)))

@[tmio M, powerlib_domain] theorem jet_d40 {s : ℝ} (hs : 0 < s) :
    (jet s).d40 1 = LY_d40 s := by
  rw [Jet.d40]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_d40 (by decide +kernel)
  simp only [cjet_d40, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_03, JA_11, JA_20, JA_21, JB_02, JB_11, JB_12, JB_20, JB_30, LY_d40]
  linear_combination (1 / 2 : ℝ) * h

/-- The certificate expression of `jet_d31`. -/
def cjet_d31 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul
    (.atom [-4] []) (.atom nLY_d31 eLY_d31)) (.mul (.atom [1] []) (.atom nJB_21 eJB_21))) (.mul
    (.mul (.atom [-1] []) (.atom nJB_11 eJB_11)) (.atom nJB_20 eJB_20))) (.mul (.atom [3] []) (.atom
    nJB_03 eJB_03))) (.mul (.mul (.atom [-1] []) (.atom nJB_02 eJB_02)) (.atom nJB_11 eJB_11)))
    (.mul (.atom [-5] []) (.atom nJA_30 eJA_30))) (.mul (.mul (.atom [-2] []) (.atom nJA_20 eJA_20))
    (.atom nJB_20 eJB_20))) (.mul (.mul (.atom [-16] []) (.atom nJA_20 eJA_20)) (.atom nJB_02
    eJB_02))) (.mul (.atom [1] []) (.atom nJA_12 eJA_12))) (.mul (.mul (.atom [-7] []) (.atom nJA_11
    eJA_11)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [2] []) (.atom nJA_02 eJA_02)) (.atom nJB_02
    eJB_02))) (.mul (.mul (.atom [1] []) (.atom nJA_02 eJA_02)) (.atom nJA_11 eJA_11)))

@[tmio M, powerlib_domain] theorem jet_d31 {s : ℝ} (hs : 0 < s) :
    (jet s).d31 1 = LY_d31 s := by
  rw [Jet.d31]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_d31 (by decide +kernel)
  simp only [cjet_d31, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_11, JA_12, JA_20, JA_30, JB_02, JB_03, JB_11, JB_20, JB_21, LY_d31]
  linear_combination (1 / 4 : ℝ) * h

/-- The certificate expression of `jet_d22`. -/
def cjet_d22 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom
    nLY_d22 eLY_d22)) (.mul (.atom [1] []) (.atom nJB_12 eJB_12))) (.mul (.atom [-1] []) (.pow
    (.atom nJB_11 eJB_11) 2))) (.mul (.atom [2] []) (.pow (.atom nJB_02 eJB_02) 2))) (.mul (.mul
    (.atom [-2] []) (.atom nJA_20 eJA_20)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [1] []) (.atom
    nJA_11 eJA_11)) (.atom nJB_02 eJB_02))) (.mul (.atom [1] []) (.atom nJA_03 eJA_03))) (.mul (.mul
    (.atom [-1] []) (.atom nJA_02 eJA_02)) (.atom nJB_11 eJB_11))) (.mul (.mul (.atom [-2] [])
    (.atom nJA_02 eJA_02)) (.atom nJA_20 eJA_20)))

@[tmio M, powerlib_domain] theorem jet_d22 {s : ℝ} (hs : 0 < s) :
    (jet s).d22 1 = LY_d22 s := by
  rw [Jet.d22]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_d22 (by decide +kernel)
  simp only [cjet_d22, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_03, JA_11, JA_20, JB_02, JB_11, JB_12, LY_d22]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_d13`. -/
def cjet_d13 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul
    (.atom [-4] []) (.atom nLY_d13 eLY_d13)) (.mul (.atom [-1] []) (.atom nJB_21 eJB_21))) (.mul
    (.mul (.atom [1] []) (.atom nJB_11 eJB_11)) (.atom nJB_20 eJB_20))) (.mul (.atom [5] []) (.atom
    nJB_03 eJB_03))) (.mul (.mul (.atom [-7] []) (.atom nJB_02 eJB_02)) (.atom nJB_11 eJB_11)))
    (.mul (.atom [-3] []) (.atom nJA_30 eJA_30))) (.mul (.mul (.atom [2] []) (.atom nJA_20 eJA_20))
    (.atom nJB_20 eJB_20))) (.mul (.mul (.atom [-16] []) (.atom nJA_20 eJA_20)) (.atom nJB_02
    eJB_02))) (.mul (.atom [-1] []) (.atom nJA_12 eJA_12))) (.mul (.mul (.atom [-1] []) (.atom
    nJA_11 eJA_11)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [-2] []) (.atom nJA_02 eJA_02))
    (.atom nJB_02 eJB_02))) (.mul (.mul (.atom [-1] []) (.atom nJA_02 eJA_02)) (.atom nJA_11
    eJA_11)))

@[tmio M, powerlib_domain] theorem jet_d13 {s : ℝ} (hs : 0 < s) :
    (jet s).d13 1 = LY_d13 s := by
  rw [Jet.d13]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_d13 (by decide +kernel)
  simp only [cjet_d13, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_11, JA_12, JA_20, JA_30, JB_02, JB_03, JB_11, JB_20, JB_21, LY_d13]
  linear_combination (1 / 4 : ℝ) * h

/-- The certificate expression of `jet_r50`. -/
def cjet_r50 : PExpr := (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nLY_r50 eLY_r50))
    (.mul (.mul (.atom [1] []) (.atom nJB_30 eJB_30)) (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom
    [1] []) (.atom nJB_20 eJB_20)) (.atom nLY_d31 eLY_d31))) (.mul (.atom [2] []) (.atom nJA_40
    eJA_40))) (.mul (.mul (.atom [3] []) (.atom nJA_30 eJA_30)) (.atom nLY_c30 eLY_c30))) (.mul
    (.mul (.atom [4] []) (.atom nJA_20 eJA_20)) (.atom nLY_d40 eLY_d40)))

@[tmio M, powerlib_domain] theorem jet_r50 {s : ℝ} (hs : 0 < s) :
    (jet s).r50 1 = LY_r50 s := by
  rw [Jet5.r50, jet_c30 hs, jet_c21 hs, jet_d40 hs, jet_d31 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r50 (by decide +kernel)
  simp only [cjet_r50, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_20, JA_30, JA_40, JB_20, JB_30, LY_c21, LY_c30, LY_d31, LY_d40, LY_r50]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r41`. -/
def cjet_r41 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom
    [-1] []) (.atom nLY_r41 eLY_r41)) (.mul (.atom [2] []) (.atom nJB_40 eJB_40))) (.mul (.mul
    (.atom [2] []) (.atom nJB_30 eJB_30)) (.atom nLY_c12 eLY_c12))) (.mul (.mul (.atom [1] [])
    (.atom nJB_21 eJB_21)) (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom [2] []) (.atom nJB_20
    eJB_20)) (.atom nLY_d22 eLY_d22))) (.mul (.mul (.atom [1] []) (.atom nJB_11 eJB_11)) (.atom
    nLY_d31 eLY_d31))) (.mul (.atom [2] []) (.atom nJA_31 eJA_31))) (.mul (.mul (.atom [2] [])
    (.atom nJA_30 eJA_30)) (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom [3] []) (.atom nJA_21
    eJA_21)) (.atom nLY_c30 eLY_c30))) (.mul (.mul (.atom [3] []) (.atom nJA_20 eJA_20)) (.atom
    nLY_d31 eLY_d31))) (.mul (.mul (.atom [4] []) (.atom nJA_11 eJA_11)) (.atom nLY_d40 eLY_d40)))

@[tmio M, powerlib_domain] theorem jet_r41 {s : ℝ} (hs : 0 < s) :
    (jet s).r41 1 = LY_r41 s := by
  rw [Jet5.r41, jet_c30 hs, jet_c21 hs, jet_c12 hs, jet_d40 hs, jet_d31 hs, jet_d22 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r41 (by decide +kernel)
  simp only [cjet_r41, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_11, JA_20, JA_21, JA_30, JA_31, JB_11, JB_20, JB_21, JB_30, JB_40, LY_c12, LY_c21,
    LY_c30, LY_d22, LY_d31, LY_d40, LY_r41]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r32`. -/
def cjet_r32 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.mul (.atom [-1] []) (.atom nLY_r32 eLY_r32)) (.mul (.atom [2] []) (.atom nJB_31
    eJB_31))) (.mul (.mul (.atom [3] []) (.atom nJB_30 eJB_30)) (.atom nLY_c03 eLY_c03))) (.mul
    (.mul (.atom [2] []) (.atom nJB_21 eJB_21)) (.atom nLY_c12 eLY_c12))) (.mul (.mul (.atom [3] [])
    (.atom nJB_20 eJB_20)) (.atom nLY_d13 eLY_d13))) (.mul (.mul (.atom [1] []) (.atom nJB_12
    eJB_12)) (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom [2] []) (.atom nJB_11 eJB_11)) (.atom
    nLY_d22 eLY_d22))) (.mul (.mul (.atom [1] []) (.atom nJB_02 eJB_02)) (.atom nLY_d31 eLY_d31)))
    (.mul (.mul (.atom [1] []) (.atom nJA_30 eJA_30)) (.atom nLY_c12 eLY_c12))) (.mul (.atom [2] [])
    (.atom nJA_22 eJA_22))) (.mul (.mul (.atom [2] []) (.atom nJA_21 eJA_21)) (.atom nLY_c21
    eLY_c21))) (.mul (.mul (.atom [2] []) (.atom nJA_20 eJA_20)) (.atom nLY_d22 eLY_d22))) (.mul
    (.mul (.atom [3] []) (.atom nJA_12 eJA_12)) (.atom nLY_c30 eLY_c30))) (.mul (.mul (.atom [3] [])
    (.atom nJA_11 eJA_11)) (.atom nLY_d31 eLY_d31))) (.mul (.mul (.atom [4] []) (.atom nJA_02
    eJA_02)) (.atom nLY_d40 eLY_d40)))

@[tmio M, powerlib_domain] theorem jet_r32 {s : ℝ} (hs : 0 < s) :
    (jet s).r32 1 = LY_r32 s := by
  rw [Jet5.r32, jet_c30 hs, jet_c21 hs, jet_c12 hs, jet_c03 hs, jet_d40 hs, jet_d31 hs, jet_d22 hs,
    jet_d13 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r32 (by decide +kernel)
  simp only [cjet_r32, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_11, JA_12, JA_20, JA_21, JA_22, JA_30, JB_02, JB_11, JB_12, JB_20, JB_21,
    JB_30, JB_31, LY_c03, LY_c12, LY_c21, LY_c30, LY_d13, LY_d22, LY_d31, LY_d40, LY_r32]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r23`. -/
def cjet_r23 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.mul (.atom [-1] []) (.atom nLY_r23 eLY_r23)) (.mul (.atom [2] []) (.atom nJB_22
    eJB_22))) (.mul (.mul (.atom [3] []) (.atom nJB_21 eJB_21)) (.atom nLY_c03 eLY_c03))) (.mul
    (.mul (.atom [2] []) (.atom nJB_12 eJB_12)) (.atom nLY_c12 eLY_c12))) (.mul (.mul (.atom [3] [])
    (.atom nJB_11 eJB_11)) (.atom nLY_d13 eLY_d13))) (.mul (.mul (.atom [1] []) (.atom nJB_03
    eJB_03)) (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom [2] []) (.atom nJB_02 eJB_02)) (.atom
    nLY_d22 eLY_d22))) (.mul (.mul (.atom [1] []) (.atom nJA_21 eJA_21)) (.atom nLY_c12 eLY_c12)))
    (.mul (.mul (.atom [1] []) (.atom nJA_20 eJA_20)) (.atom nLY_d13 eLY_d13))) (.mul (.atom [2] [])
    (.atom nJA_13 eJA_13))) (.mul (.mul (.atom [2] []) (.atom nJA_12 eJA_12)) (.atom nLY_c21
    eLY_c21))) (.mul (.mul (.atom [2] []) (.atom nJA_11 eJA_11)) (.atom nLY_d22 eLY_d22))) (.mul
    (.mul (.atom [3] []) (.atom nJA_03 eJA_03)) (.atom nLY_c30 eLY_c30))) (.mul (.mul (.atom [3] [])
    (.atom nJA_02 eJA_02)) (.atom nLY_d31 eLY_d31)))

@[tmio M, powerlib_domain] theorem jet_r23 {s : ℝ} (hs : 0 < s) :
    (jet s).r23 1 = LY_r23 s := by
  rw [Jet5.r23, jet_c30 hs, jet_c21 hs, jet_c12 hs, jet_c03 hs, jet_d31 hs, jet_d22 hs, jet_d13 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r23 (by decide +kernel)
  simp only [cjet_r23, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_03, JA_11, JA_12, JA_13, JA_20, JA_21, JB_02, JB_03, JB_11, JB_12, JB_21,
    JB_22, LY_c03, LY_c12, LY_c21, LY_c30, LY_d13, LY_d22, LY_d31, LY_r23]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r14`. -/
def cjet_r14 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] [])
    (.atom nLY_r14 eLY_r14)) (.mul (.atom [2] []) (.atom nJB_13 eJB_13))) (.mul (.mul (.atom [3] [])
    (.atom nJB_12 eJB_12)) (.atom nLY_c03 eLY_c03))) (.mul (.mul (.atom [2] []) (.atom nJB_03
    eJB_03)) (.atom nLY_c12 eLY_c12))) (.mul (.mul (.atom [3] []) (.atom nJB_02 eJB_02)) (.atom
    nLY_d13 eLY_d13))) (.mul (.mul (.atom [1] []) (.atom nJA_12 eJA_12)) (.atom nLY_c12 eLY_c12)))
    (.mul (.mul (.atom [1] []) (.atom nJA_11 eJA_11)) (.atom nLY_d13 eLY_d13))) (.mul (.atom [2] [])
    (.atom nJA_04 eJA_04))) (.mul (.mul (.atom [2] []) (.atom nJA_03 eJA_03)) (.atom nLY_c21
    eLY_c21))) (.mul (.mul (.atom [2] []) (.atom nJA_02 eJA_02)) (.atom nLY_d22 eLY_d22)))

@[tmio M, powerlib_domain] theorem jet_r14 {s : ℝ} (hs : 0 < s) :
    (jet s).r14 1 = LY_r14 s := by
  rw [Jet5.r14, jet_c21 hs, jet_c12 hs, jet_c03 hs, jet_d22 hs, jet_d13 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r14 (by decide +kernel)
  simp only [cjet_r14, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_03, JA_04, JA_11, JA_12, JB_02, JB_03, JB_12, JB_13, LY_c03, LY_c12, LY_c21,
    LY_d13, LY_d22, LY_r14]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r05`. -/
def cjet_r05 : PExpr := (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nLY_r05 eLY_r05)) (.mul
    (.atom [2] []) (.atom nJB_04 eJB_04))) (.mul (.mul (.atom [3] []) (.atom nJB_03 eJB_03)) (.atom
    nLY_c03 eLY_c03))) (.mul (.mul (.atom [1] []) (.atom nJA_03 eJA_03)) (.atom nLY_c12 eLY_c12)))
    (.mul (.mul (.atom [1] []) (.atom nJA_02 eJA_02)) (.atom nLY_d13 eLY_d13)))

@[tmio M, powerlib_domain] theorem jet_r05 {s : ℝ} (hs : 0 < s) :
    (jet s).r05 1 = LY_r05 s := by
  rw [Jet5.r05, jet_c12 hs, jet_c03 hs, jet_d13 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r05 (by decide +kernel)
  simp only [cjet_r05, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_03, JB_03, JB_04, LY_c03, LY_c12, LY_d13, LY_r05]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_e50`. -/
def cjet_e50 : PExpr := (.add (.add (.add (.mul (.atom [3] []) (.atom nLY_r41 eLY_r41)) (.mul (.atom
    [2] []) (.atom nLY_r23 eLY_r23))) (.mul (.atom [8] []) (.atom nLY_r05 eLY_r05))) (.mul (.atom
    [-15] []) (.atom nLY_e50 eLY_e50)))

@[tmio M, powerlib_domain] theorem jet_e50 {s : ℝ} (hs : 0 < s) :
    (jet s).e50 1 = LY_e50 s := by
  rw [Jet5.e50, jet_r41 hs, jet_r23 hs, jet_r05 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_e50 (by decide +kernel)
  simp only [cjet_e50, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [LY_e50, LY_r05, LY_r23, LY_r41]
  linear_combination (1 / 15 : ℝ) * h

/-- The certificate expression of `jet_e41`. -/
def cjet_e41 : PExpr := (.add (.mul (.atom [-1] []) (.atom nLY_r50 eLY_r50)) (.mul (.atom [-1] [])
    (.atom nLY_e41 eLY_e41)))

@[tmio M, powerlib_domain] theorem jet_e41 {s : ℝ} (hs : 0 < s) :
    (jet s).e41 1 = LY_e41 s := by
  rw [Jet5.e41, jet_r50 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_e41 (by decide +kernel)
  simp only [cjet_e41, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [LY_e41, LY_r50]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_e32`. -/
def cjet_e32 : PExpr := (.add (.add (.mul (.atom [1] []) (.atom nLY_r23 eLY_r23)) (.mul (.atom [4]
    []) (.atom nLY_r05 eLY_r05))) (.mul (.atom [-3] []) (.atom nLY_e32 eLY_e32)))

@[tmio M, powerlib_domain] theorem jet_e32 {s : ℝ} (hs : 0 < s) :
    (jet s).e32 1 = LY_e32 s := by
  rw [Jet5.e32, jet_r23 hs, jet_r05 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_e32 (by decide +kernel)
  simp only [cjet_e32, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [LY_e32, LY_r05, LY_r23]
  linear_combination (1 / 3 : ℝ) * h

/-- The certificate expression of `jet_e23`. -/
def cjet_e23 : PExpr := (.add (.add (.mul (.atom [-4] []) (.atom nLY_r50 eLY_r50)) (.mul (.atom [-1]
    []) (.atom nLY_r32 eLY_r32))) (.mul (.atom [-3] []) (.atom nLY_e23 eLY_e23)))

@[tmio M, powerlib_domain] theorem jet_e23 {s : ℝ} (hs : 0 < s) :
    (jet s).e23 1 = LY_e23 s := by
  rw [Jet5.e23, jet_r50 hs, jet_r32 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_e23 (by decide +kernel)
  simp only [cjet_e23, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [LY_e23, LY_r32, LY_r50]
  linear_combination (1 / 3 : ℝ) * h

/-- The certificate expression of `jet_e14`. -/
def cjet_e14 : PExpr := (.add (.mul (.atom [1] []) (.atom nLY_r05 eLY_r05)) (.mul (.atom [-1] [])
    (.atom nLY_e14 eLY_e14)))

@[tmio M, powerlib_domain] theorem jet_e14 {s : ℝ} (hs : 0 < s) :
    (jet s).e14 1 = LY_e14 s := by
  rw [Jet5.e14, jet_r05 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_e14 (by decide +kernel)
  simp only [cjet_e14, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [LY_e14, LY_r05]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_e05`. -/
def cjet_e05 : PExpr := (.add (.add (.add (.mul (.atom [-8] []) (.atom nLY_r50 eLY_r50)) (.mul
    (.atom [-2] []) (.atom nLY_r32 eLY_r32))) (.mul (.atom [-3] []) (.atom nLY_r14 eLY_r14))) (.mul
    (.atom [-15] []) (.atom nLY_e05 eLY_e05)))

@[tmio M, powerlib_domain] theorem jet_e05 {s : ℝ} (hs : 0 < s) :
    (jet s).e05 1 = LY_e05 s := by
  rw [Jet5.e05, jet_r50 hs, jet_r32 hs, jet_r14 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_e05 (by decide +kernel)
  simp only [cjet_e05, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [LY_e05, LY_r14, LY_r32, LY_r50]
  linear_combination (1 / 15 : ℝ) * h

/-- The certificate expression of `jet_r60`. -/
def cjet_r60 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom
    nLY_r60 eLY_r60)) (.mul (.mul (.atom [1] []) (.atom nJB_40 eJB_40)) (.atom nLY_c21 eLY_c21)))
    (.mul (.mul (.atom [1] []) (.atom nJB_30 eJB_30)) (.atom nLY_d31 eLY_d31))) (.mul (.mul (.atom
    [1] []) (.atom nJB_20 eJB_20)) (.atom nLY_e41 eLY_e41))) (.mul (.atom [2] []) (.atom nJA_50
    eJA_50))) (.mul (.mul (.atom [3] []) (.atom nJA_40 eJA_40)) (.atom nLY_c30 eLY_c30))) (.mul
    (.mul (.atom [4] []) (.atom nJA_30 eJA_30)) (.atom nLY_d40 eLY_d40))) (.mul (.mul (.atom [5] [])
    (.atom nJA_20 eJA_20)) (.atom nLY_e50 eLY_e50)))

@[tmio M, powerlib_domain] theorem jet_r60 {s : ℝ} (hs : 0 < s) :
    (jet s).r60 1 = LY_r60 s := by
  rw [Jet5.r60, jet_c30 hs, jet_c21 hs, jet_d40 hs, jet_d31 hs, jet_e50 hs, jet_e41 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r60 (by decide +kernel)
  simp only [cjet_r60, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_20, JA_30, JA_40, JA_50, JB_20, JB_30, JB_40, LY_c21, LY_c30, LY_d31, LY_d40,
    LY_e41, LY_e50, LY_r60]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r42`. -/
def cjet_r42 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nLY_r42 eLY_r42))
    (.mul (.atom [2] []) (.atom nJB_41 eJB_41))) (.mul (.mul (.atom [3] []) (.atom nJB_40 eJB_40))
    (.atom nLY_c03 eLY_c03))) (.mul (.mul (.atom [2] []) (.atom nJB_31 eJB_31)) (.atom nLY_c12
    eLY_c12))) (.mul (.mul (.atom [3] []) (.atom nJB_30 eJB_30)) (.atom nLY_d13 eLY_d13))) (.mul
    (.mul (.atom [1] []) (.atom nJB_22 eJB_22)) (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom [2] [])
    (.atom nJB_21 eJB_21)) (.atom nLY_d22 eLY_d22))) (.mul (.mul (.atom [3] []) (.atom nJB_20
    eJB_20)) (.atom nLY_e23 eLY_e23))) (.mul (.mul (.atom [1] []) (.atom nJB_12 eJB_12)) (.atom
    nLY_d31 eLY_d31))) (.mul (.mul (.atom [2] []) (.atom nJB_11 eJB_11)) (.atom nLY_e32 eLY_e32)))
    (.mul (.mul (.atom [1] []) (.atom nJB_02 eJB_02)) (.atom nLY_e41 eLY_e41))) (.mul (.mul (.atom
    [1] []) (.atom nJA_40 eJA_40)) (.atom nLY_c12 eLY_c12))) (.mul (.atom [2] []) (.atom nJA_32
    eJA_32))) (.mul (.mul (.atom [2] []) (.atom nJA_31 eJA_31)) (.atom nLY_c21 eLY_c21))) (.mul
    (.mul (.atom [2] []) (.atom nJA_30 eJA_30)) (.atom nLY_d22 eLY_d22))) (.mul (.mul (.atom [3] [])
    (.atom nJA_22 eJA_22)) (.atom nLY_c30 eLY_c30))) (.mul (.mul (.atom [3] []) (.atom nJA_21
    eJA_21)) (.atom nLY_d31 eLY_d31))) (.mul (.mul (.atom [3] []) (.atom nJA_20 eJA_20)) (.atom
    nLY_e32 eLY_e32))) (.mul (.mul (.atom [4] []) (.atom nJA_12 eJA_12)) (.atom nLY_d40 eLY_d40)))
    (.mul (.mul (.atom [4] []) (.atom nJA_11 eJA_11)) (.atom nLY_e41 eLY_e41))) (.mul (.mul (.atom
    [5] []) (.atom nJA_02 eJA_02)) (.atom nLY_e50 eLY_e50)))

@[tmio M, powerlib_domain] theorem jet_r42 {s : ℝ} (hs : 0 < s) :
    (jet s).r42 1 = LY_r42 s := by
  rw [Jet5.r42, jet_c30 hs, jet_c21 hs, jet_c12 hs, jet_c03 hs, jet_d40 hs, jet_d31 hs, jet_d22 hs,
    jet_d13 hs, jet_e50 hs, jet_e41 hs, jet_e32 hs, jet_e23 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r42 (by decide +kernel)
  simp only [cjet_r42, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_11, JA_12, JA_20, JA_21, JA_22, JA_30, JA_31, JA_32, JA_40, JB_02, JB_11,
    JB_12, JB_20, JB_21, JB_22, JB_30, JB_31, JB_40, JB_41, LY_c03, LY_c12, LY_c21, LY_c30, LY_d13,
    LY_d22, LY_d31, LY_d40, LY_e23, LY_e32, LY_e41, LY_e50, LY_r42]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r24`. -/
def cjet_r24 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nLY_r24 eLY_r24)) (.mul
    (.atom [2] []) (.atom nJB_23 eJB_23))) (.mul (.mul (.atom [3] []) (.atom nJB_22 eJB_22)) (.atom
    nLY_c03 eLY_c03))) (.mul (.mul (.atom [5] []) (.atom nJB_20 eJB_20)) (.atom nLY_e05 eLY_e05)))
    (.mul (.mul (.atom [2] []) (.atom nJB_13 eJB_13)) (.atom nLY_c12 eLY_c12))) (.mul (.mul (.atom
    [3] []) (.atom nJB_12 eJB_12)) (.atom nLY_d13 eLY_d13))) (.mul (.mul (.atom [4] []) (.atom
    nJB_11 eJB_11)) (.atom nLY_e14 eLY_e14))) (.mul (.mul (.atom [1] []) (.atom nJB_04 eJB_04))
    (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom [2] []) (.atom nJB_03 eJB_03)) (.atom nLY_d22
    eLY_d22))) (.mul (.mul (.atom [3] []) (.atom nJB_02 eJB_02)) (.atom nLY_e23 eLY_e23))) (.mul
    (.mul (.atom [1] []) (.atom nJA_22 eJA_22)) (.atom nLY_c12 eLY_c12))) (.mul (.mul (.atom [1] [])
    (.atom nJA_21 eJA_21)) (.atom nLY_d13 eLY_d13))) (.mul (.mul (.atom [1] []) (.atom nJA_20
    eJA_20)) (.atom nLY_e14 eLY_e14))) (.mul (.atom [2] []) (.atom nJA_14 eJA_14))) (.mul (.mul
    (.atom [2] []) (.atom nJA_13 eJA_13)) (.atom nLY_c21 eLY_c21))) (.mul (.mul (.atom [2] [])
    (.atom nJA_12 eJA_12)) (.atom nLY_d22 eLY_d22))) (.mul (.mul (.atom [2] []) (.atom nJA_11
    eJA_11)) (.atom nLY_e23 eLY_e23))) (.mul (.mul (.atom [3] []) (.atom nJA_04 eJA_04)) (.atom
    nLY_c30 eLY_c30))) (.mul (.mul (.atom [3] []) (.atom nJA_03 eJA_03)) (.atom nLY_d31 eLY_d31)))
    (.mul (.mul (.atom [3] []) (.atom nJA_02 eJA_02)) (.atom nLY_e32 eLY_e32)))

@[tmio M, powerlib_domain] theorem jet_r24 {s : ℝ} (hs : 0 < s) :
    (jet s).r24 1 = LY_r24 s := by
  rw [Jet5.r24, jet_c30 hs, jet_c21 hs, jet_c12 hs, jet_c03 hs, jet_d31 hs, jet_d22 hs, jet_d13 hs,
    jet_e32 hs, jet_e23 hs, jet_e14 hs, jet_e05 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r24 (by decide +kernel)
  simp only [cjet_r24, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_03, JA_04, JA_11, JA_12, JA_13, JA_14, JA_20, JA_21, JA_22, JB_02, JB_03,
    JB_04, JB_11, JB_12, JB_13, JB_20, JB_22, JB_23, LY_c03, LY_c12, LY_c21, LY_c30, LY_d13, LY_d22,
    LY_d31, LY_e05, LY_e14, LY_e23, LY_e32, LY_r24]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_r06`. -/
def cjet_r06 : PExpr := (.add (.add (.add (.add (.add (.add (.mul (.atom [-1] []) (.atom nLY_r06
    eLY_r06)) (.mul (.atom [2] []) (.atom nJB_05 eJB_05))) (.mul (.mul (.atom [3] []) (.atom nJB_04
    eJB_04)) (.atom nLY_c03 eLY_c03))) (.mul (.mul (.atom [5] []) (.atom nJB_02 eJB_02)) (.atom
    nLY_e05 eLY_e05))) (.mul (.mul (.atom [1] []) (.atom nJA_04 eJA_04)) (.atom nLY_c12 eLY_c12)))
    (.mul (.mul (.atom [1] []) (.atom nJA_03 eJA_03)) (.atom nLY_d13 eLY_d13))) (.mul (.mul (.atom
    [1] []) (.atom nJA_02 eJA_02)) (.atom nLY_e14 eLY_e14)))

@[tmio M, powerlib_domain] theorem jet_r06 {s : ℝ} (hs : 0 < s) :
    (jet s).r06 1 = LY_r06 s := by
  rw [Jet5.r06, jet_c12 hs, jet_c03 hs, jet_d13 hs, jet_e14 hs, jet_e05 hs]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_r06 (by decide +kernel)
  simp only [cjet_r06, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_03, JA_04, JB_02, JB_04, JB_05, LY_c03, LY_c12, LY_d13, LY_e05, LY_e14,
    LY_r06]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `jet_k6`. -/
def cjet_k6 : PExpr := (.add (.add (.add (.add (.mul (.atom [5] []) (.atom nLY_r60 eLY_r60)) (.mul
    (.atom [1] []) (.atom nLY_r42 eLY_r42))) (.mul (.atom [1] []) (.atom nLY_r24 eLY_r24))) (.mul
    (.atom [5] []) (.atom nLY_r06 eLY_r06))) (.mul (.atom [-16] []) (.atom nLY_k6 eLY_k6)))

@[tmio M, powerlib_domain] theorem jet_k6 {s : ℝ} (hs : 0 < s) :
    (jet s).k6 1 = LY_k6 s := by
  rw [Jet5.k6, jet_r60 hs, jet_r42 hs, jet_r24 hs, jet_r06 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_k6 (by decide +kernel)
  simp only [cjet_k6, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [LY_k6, LY_r06, LY_r24, LY_r42, LY_r60]
  linear_combination (1 / 16 : ℝ) * h

/-- The certificate expression of `jet_l1`. -/
def cjet_l1 : PExpr := (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.atom [-4]
    []) (.atom nL1V eL1V)) (.mul (.atom [1] []) (.atom nJB_21 eJB_21))) (.mul (.mul (.atom [-1] [])
    (.atom nJB_11 eJB_11)) (.atom nJB_20 eJB_20))) (.mul (.atom [3] []) (.atom nJB_03 eJB_03)))
    (.mul (.mul (.atom [-1] []) (.atom nJB_02 eJB_02)) (.atom nJB_11 eJB_11))) (.mul (.atom [3] [])
    (.atom nJA_30 eJA_30))) (.mul (.mul (.atom [-2] []) (.atom nJA_20 eJA_20)) (.atom nJB_20
    eJB_20))) (.mul (.atom [1] []) (.atom nJA_12 eJA_12))) (.mul (.mul (.atom [1] []) (.atom nJA_11
    eJA_11)) (.atom nJA_20 eJA_20))) (.mul (.mul (.atom [2] []) (.atom nJA_02 eJA_02)) (.atom nJB_02
    eJB_02))) (.mul (.mul (.atom [1] []) (.atom nJA_02 eJA_02)) (.atom nJA_11 eJA_11)))

@[tmio M, powerlib_domain] theorem jet_l1 {s : ℝ} (hs : 0 < s) :
    (jet s).l1 1 = L1V s := by
  rw [Jet.l1]
  simp only [jet]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_l1 (by decide +kernel)
  simp only [cjet_l1, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [JA_02, JA_11, JA_12, JA_20, JA_30, JB_02, JB_03, JB_11, JB_20, JB_21, L1V]
  linear_combination (1 / 4 : ℝ) * h

/-- The certificate expression of `jet_l2`. -/
def cjet_l2 : PExpr := (.add (.mul (.atom [2] []) (.atom nLY_k6 eLY_k6)) (.mul (.atom [-1] [])
    (.atom nL2V eL2V)))

@[tmio M, powerlib_domain] theorem jet_l2 {s : ℝ} (hs : 0 < s) :
    (jet s).l2 1 = L2V s := by
  rw [Jet5.l2, jet_k6 hs]
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cjet_l2 (by decide +kernel)
  simp only [cjet_l2, PExpr.val, zeval, bval_nil_right, div_one] at h
  push_cast at h
  simp only [L2V, LY_k6]
  linear_combination (1 / 1 : ℝ) * h

/-- The certificate expression of `nL2V_eq`. -/
def cL2num : PExpr := (.add (.add (.atom nL2V []) (.mul (.int (-1)) (.atom nNR []))) (.mul (.mul
    (.int (-1)) (.atom nNN [])) (.atom nNQ [])))

/-- `nNN` is `bautinNum`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeval_nNN (s : ℝ) : zeval nNN s = bautinNum s := by
  simp only [nNN, zeval, bautinNum]; push_cast; ring

/-- **The numerator of `l₂(J)` modulo `bautinNum`**: `n(s) = Q(s) N(s) + ρ(s)` (exact division,
`deg ρ ≤ 9`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem nL2V_eq {s : ℝ} (hs : 0 < s) :
    zeval nL2V s = zeval nNQ s * bautinNum s + zeval nNR s := by
  have h := PExpr.val_eq_zero (bases_ne_zero hs) cL2num (by decide +kernel)
  simp only [cL2num, PExpr.val, bval_nil_right, div_one] at h
  rw [← zeval_nNN]
  linear_combination h

/-- The remainder `ρ(s) = −512 s P(s²)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeval_nNR (s : ℝ) :
    zeval nNR s = -512 * s * (457969858420594106 * (s ^ 2) ^ 4 -
      1546514418666033249 * (s ^ 2) ^ 3 - 7609390009086145426 * (s ^ 2) ^ 2 -
      9025541755155023664 * s ^ 2 - 3589569381305680672) := by
  simp only [nNR, zeval]; push_cast; ring

/-- **The remainder is positive on `(2, 21/10)`**: `P(t) < 0` for `4 < t < 441/100` (`t = s²`;
`t³(at − b) ≤ (441/100)³ (441a/100 − b)` and `ct² + dt + e > 16c + 4d + e`). Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem nNR_pos {s : ℝ} (h2 : 2 < s) (h21 : s < 21 / 10) :
    0 < zeval nNR s := by
  rw [zeval_nNR]
  have hs : 0 < s := by linarith
  have ht : 4 < s ^ 2 := by nlinarith
  have htU : s ^ 2 < 441 / 100 := by nlinarith
  set t := s ^ 2 with htd
  have ht0 : 0 < t := by linarith
  have h3 : t ^ 3 < (441 / 100) ^ 3 := by
    have := pow_lt_pow_left₀ htU ht0.le (by norm_num : (3 : ℕ) ≠ 0); linarith
  have hlin : 457969858420594106 * t - 1546514418666033249 <
      457969858420594106 * (441 / 100) - 1546514418666033249 := by linarith
  have hpos : (0 : ℝ) < 457969858420594106 * (441 / 100) - 1546514418666033249 := by norm_num
  have hA : t ^ 3 * (457969858420594106 * t - 1546514418666033249) <
      (441 / 100) ^ 3 * (457969858420594106 * (441 / 100) - 1546514418666033249) := by
    calc t ^ 3 * (457969858420594106 * t - 1546514418666033249)
        ≤ t ^ 3 * (457969858420594106 * (441 / 100) - 1546514418666033249) := by
          gcongr
      _ < (441 / 100) ^ 3 * (457969858420594106 * (441 / 100) - 1546514418666033249) := by
          gcongr
  have hB : 16 < t ^ 2 := by nlinarith
  have hP : 457969858420594106 * t ^ 4 - 1546514418666033249 * t ^ 3 -
      7609390009086145426 * t ^ 2 - 9025541755155023664 * t - 3589569381305680672 < 0 := by
    nlinarith
  nlinarith

/-- `l₁(J)` is the first Lyapunov coefficient of the path:
`L1V = s³(s² + 4)² N(s)/(D₁ D₂)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem L1V_eq (s : ℝ) :
    L1V s = s ^ 3 * (s ^ 2 + 4) ^ 2 * bautinNum s / (bautinDen1 s * bautinDen2 s) := by
  have hn : zeval nL1V s = s ^ 3 * (s ^ 2 + 4) ^ 2 * bautinNum s := by
    simp only [nL1V, zeval, bautinNum]; push_cast; ring
  have hd : bval bases eL1V s = bautinDen1 s * bautinDen2 s := by
    simp only [eL1V, bval, bases, zeval, bautinDen1, bautinDen2]; push_cast; ring
  rw [L1V, hn, hd]

/-- **`l₂(J) > 0` at a zero of `bautinNum` in `(2, 21/10)`**: there `l₂(J) = ρ(s)/(12 E D₁³ D₂³)`
with `ρ > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem L2V_pos {s : ℝ} (hN : bautinNum s = 0) (h2 : 2 < s)
    (h21 : s < 21 / 10) : 0 < L2V s := by
  have hs : 0 < s := by linarith
  rw [L2V, nL2V_eq hs, hN, mul_zero, zero_add]
  exact div_pos (nNR_pos h2 h21) (bval_pos (zeval_bases_pos hs) _)

/-- **The first coefficient of the jet along the path**:
`l₁(J) = s³(s² + 4)² N(s)/(D₁ D₂)`, the first Lyapunov coefficient of
`bautinPath_firstLyapunov`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jet_l1_eq {s : ℝ} (hs : 0 < s) :
    (jet s).l1 1 = s ^ 3 * (s ^ 2 + 4) ^ 2 * bautinNum s / (bautinDen1 s * bautinDen2 s) :=
  (jet_l1 hs).trans (L1V_eq s)

end Bautin
end VSM
end powerlib.GFM.Line
