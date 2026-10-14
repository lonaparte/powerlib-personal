import theorem.GFL.PowerLoop.QuasiStaticFold
import theorem.Dynamics.Degenerate.WeakFocus

/-! # Quasi-static three-state GFL: a supercritical Hopf point (gains of arbitrary sign)

**Model boundary.** The model of `theorem/GFL/PowerLoop/QuasiStatic.lean`, unchanged: a single
grid-following converter on an infinite bus of amplitude `V` behind a lossless reactance `X_g`;
three-phase balanced averaged dq model in the PLL frame, algebraic (quasi-static) network,
continuous time. States, in order: `θ` (PLL error angle), `x` (PLL integrator), `I_d` (d-axis
current); `I_q = 0`; OUT-positive current, export-positive power `P = (3/2) V cos θ I_d`. SRF-PLL
`θ̇ = k_p v_q + k_i x`, `ẋ = v_q`; dispatch `İ_d = k_P (P_ref − P)`. Ideal current loop; no line
dynamics, resistance, dc link, PWM, delay or limiter. `QuasiStatic.family` admits every real
parameter set; the statements below concern one explicit member (with `k_p < 0`), locally, through
the field translated to its selected point.

**Witness.** `supercriticalQS`: `V = √5`, `X_g = 1`, `k_p = −1/4`, `k_i = 21/4`, `k_P = 4/3`,
`P_ref = 3`, `(θ*, 0, I_d*) = (arctan(1/2), 0, 1)` (`supercriticalQS_trig`: `V cos θ* = 2`,
`V sin θ* = 1`; `supercriticalQS_isEq`). Its characteristic polynomial is
`s³ + (7/2)s² + 9s + 63/2 = (s + 7/2)(s² + 9)`: eigenvalues `±3i`, `−7/2`
(`supercriticalQS_routh_boundary`: `tr J · m₂(J) = det J`, the strict Routh–Hurwitz condition
fails). In the eigen-coordinates `c = M z` (`hopfQS_c1`, `hopfQS_c2`, `hopfQS_c3`, `z = T c`,
`hopfQS_coords`) the linear part is a rotation of `(c₁, c₂)` with frequency `3` and the decay
`ċ₃ = −(7/2)c₃`.

**Normal form (static, SymPy-generated, kernel-checked).** `hopfQS_W` is the Lyapunov polynomial
`(c₁² + c₂²)/2 + W₃ + W₄ + 32 (c₃ − h₂(c₁, c₂))²` with the quadratic centre-manifold approximation
`h₂ = hopfQS_h` (`hopfQS_W_eq`); `hopfQS_key` is the identity
`Ẇ = w₄ + R + (sin φ − (φ − φ³/6)) K_S + (cos φ − (1 − φ²/2)) K_C` along the exact field, where
`w₄ = −κ₁(c₁² + c₂²)² − 224 (c₃ − h₂)² + (c₃ − h₂) q(c₁, c₂)` (`hopfQS_w4`,
`κ₁ = 22482719/1574880`), the remainder `R = hopfQS_R` has 90 monomials of weight `≥ 5` (weights
`(1, 1, 2)`), and `K_S`, `K_C` have weight `≥ 1`. `hopfQS_w4_le`:
`w₄ ≤ −((c₁² + c₂²)² + (c₃ − h₂)²)`. `Dynamics.Degenerate.isBigO_poly3_weight` (generic,
`theorem/Dynamics/Degenerate/WeakFocus.lean`): a polynomial of weight `≥ k` is `O(σ^k)` when
`c₁, c₂ = O(σ)`, `c₃ = O(σ²)`; with `σ = |c₁| + |c₂| + √|c₃ − h₂|` the remainder is
`O(σ⁵) = o(σ⁴)` and `W > 0`, `Ẇ < 0` on a punctured neighbourhood. No centre-manifold
theorem is used; the term `32 (c₃ − h₂)²` absorbs the centre manifold. (A1's
`Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus` needs a nonlinearity entering through one
scalar of one linear combination; the quasi-static field has two independent nonlinear channels,
`v_q` and the bilinear power term, so the witness uses its own polynomial with `Dynamics.Degenerate.poly3`.)

**Connection conclusions.**
* `supercriticalQS_mem_den_locallyAsymptoticallyStable`: the witness is locally asymptotically
  stable (a weak focus: asymptotically, not exponentially, stable).
* `not_exact_locallyAsymptoticallyStable`: the local asymptotic translation of
  `QuasiStatic.family` (`{equilibrium, jacobianStable}`, strict Routh–Hurwitz) is **not exact**
  for gains of arbitrary sign. Within positive gains it is exact
  (`exactUnder_locallyAsymptoticallyStable`, `theorem/GFL/PowerLoop/QuasiStaticFold.lean`).

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/contrast-conclusions.md` (推论二 准静态无 Hopf: stated for positive gains; the
witness shows that the positivity of the gains is essential for both the absence of a Hopf pair
and the exactness of the Routh–Hurwitz translation); model `GFLQuasiStatic` in
`.../archive/simulation/src/gfl_gfm_contrast_sim/models.py`. The first Lyapunov coefficient of the
witness (`l₁ ≈ −0.51 < 0`, Kuznetsov's formula) and the normal form were computed in SymPy;
only the Lyapunov argument is formal.
-/

noncomputable section
namespace powerlib.GFL.PowerLoop.QuasiStatic
open Filter Topology Asymptotics powerlib.Dynamics.Degenerate

/-! ## Polynomial data of the witness (static) -/

/-- The Lyapunov polynomial `W(c₁, c₂, c₃)` of the witness in eigen-coordinates. -/
def hopfQS_W : List (ℝ × ℕ × ℕ × ℕ) := [
  ((374777442 / 269124025 : ℝ), 4, 0, 0),
  ((-19727241919 / 4559277600 : ℝ), 3, 1, 0),
  ((-3821 / 3060 : ℝ), 3, 0, 0),
  ((4240288479 / 538248050 : ℝ), 2, 2, 0),
  ((-141 / 340 : ℝ), 2, 1, 0),
  ((-219024 / 16405 : ℝ), 2, 0, 1),
  ((1 / 2 : ℝ), 2, 0, 0),
  ((-645468045109 / 77507719200 : ℝ), 1, 3, 0),
  ((-508 / 255 : ℝ), 1, 2, 0),
  ((-36288 / 16405 : ℝ), 1, 1, 1),
  ((68881445927 / 4844232450 : ℝ), 0, 4, 0),
  ((553 / 1530 : ℝ), 0, 3, 0),
  ((-673408 / 16405 : ℝ), 0, 2, 1),
  ((1 / 2 : ℝ), 0, 2, 0),
  ((32 : ℝ), 0, 0, 2)]
/-- The cubic and quartic part of `W` in `(c₁, c₂)`. -/
def hopfQS_W34 : List (ℝ × ℕ × ℕ × ℕ) := [
  ((-1922947439 / 401594400 : ℝ), 3, 1, 0),
  ((-3821 / 3060 : ℝ), 3, 0, 0),
  ((-2017761 / 2788850 : ℝ), 2, 2, 0),
  ((-141 / 340 : ℝ), 2, 1, 0),
  ((-3914159989 / 401594400 : ℝ), 1, 3, 0),
  ((-508 / 255 : ℝ), 1, 2, 0),
  ((26482151 / 25099650 : ℝ), 0, 4, 0),
  ((553 / 1530 : ℝ), 0, 3, 0)]
/-- Remainder of `Ẇ` along the Taylor-truncated field: weight `≥ 5`. -/
def hopfQS_R : List (ℝ × ℕ × ℕ × ℕ) := [
  ((-4791464077283 / 732017348000 : ℝ), 6, 1, 0),
  ((-33540248540981 / 366008674000 : ℝ), 6, 0, 1),
  ((7551575952039 / 366008674000 : ℝ), 6, 0, 0),
  ((-2284126905887 / 732017348000 : ℝ), 5, 2, 0),
  ((-65518025223399 / 732017348000 : ℝ), 5, 1, 1),
  ((34002163263133 / 732017348000 : ℝ), 5, 1, 0),
  ((-234781739786867 / 366008674000 : ℝ), 5, 0, 2),
  ((33950928436943 / 73201734800 : ℝ), 5, 0, 1),
  ((39332180770411 / 2928069392000 : ℝ), 5, 0, 0),
  ((46733957078803 / 2196052044000 : ℝ), 4, 3, 0),
  ((740469728243539 / 2196052044000 : ℝ), 4, 2, 1),
  ((-520573764287 / 27450650550 : ℝ), 4, 2, 0),
  ((971938868177291 / 2196052044000 : ℝ), 4, 1, 2),
  ((319609696814073 / 732017348000 : ℝ), 4, 1, 1),
  ((-111944407742131 / 2928069392000 : ℝ), 4, 1, 0),
  ((-1643472178508069 / 1098026022000 : ℝ), 4, 0, 3),
  ((2351886332147219 / 1098026022000 : ℝ), 4, 0, 2),
  ((-190508764124063 / 878420817600 : ℝ), 4, 0, 1),
  ((167698886558663 / 3952893679200 : ℝ), 3, 4, 0),
  ((2729765881077487 / 3952893679200 : ℝ), 3, 3, 1),
  ((-26571268944967 / 1317631226400 : ℝ), 3, 3, 0),
  ((68335870669549 / 43059844000 : ℝ), 3, 2, 2),
  ((43104637543069 / 193769298000 : ℝ), 3, 2, 1),
  ((-2380105219573309 / 26352624528000 : ℝ), 3, 2, 0),
  ((12628198574586581 / 3952893679200 : ℝ), 3, 1, 3),
  ((-10381212070380109 / 6588156132000 : ℝ), 3, 1, 2),
  ((-15110031568273151 / 13176312264000 : ℝ), 3, 1, 1),
  ((-11504305249556483 / 9882234198000 : ℝ), 3, 0, 4),
  ((11402661034966117 / 3294078066000 : ℝ), 3, 0, 3),
  ((-19010813812427143 / 8784208176000 : ℝ), 3, 0, 2),
  ((-250849723 / 1394425 : ℝ), 3, 0, 1),
  ((294895887563561 / 1647039033000 : ℝ), 2, 5, 0),
  ((17621809003952251 / 6588156132000 : ℝ), 2, 4, 1),
  ((-405139128333847 / 3294078066000 : ℝ), 2, 4, 0),
  ((1659531556986541 / 732017348000 : ℝ), 2, 3, 2),
  ((6346156419845417 / 6588156132000 : ℝ), 2, 3, 1),
  ((-708459990655601 / 8784208176000 : ℝ), 2, 3, 0),
  ((-6066182301587149 / 6588156132000 : ℝ), 2, 2, 3),
  ((-1429790761063973 / 549013011000 : ℝ), 2, 2, 2),
  ((-1341571396775 / 2066872512 : ℝ), 2, 2, 1),
  ((2702202153146083 / 658815613200 : ℝ), 2, 1, 4),
  ((-17323482649600309 / 1317631226400 : ℝ), 2, 1, 3),
  ((-637253421287497 / 351368327040 : ℝ), 2, 1, 2),
  ((567334423 / 16733100 : ℝ), 2, 1, 1),
  ((21073914169 / 12549825 : ℝ), 2, 0, 4),
  ((-23733082331 / 3346620 : ℝ), 2, 0, 3),
  ((1224684657 / 1394425 : ℝ), 2, 0, 2),
  ((27734376809503 / 82351951650 : ℝ), 1, 6, 0),
  ((4730341809737411 / 823519516500 : ℝ), 1, 5, 1),
  ((-126119577024614 / 205879879125 : ℝ), 1, 5, 0),
  ((2183762243155423 / 146403469600 : ℝ), 1, 4, 2),
  ((-5801262887573999 / 1647039033000 : ℝ), 1, 4, 1),
  ((-236431078927373 / 549013011000 : ℝ), 1, 4, 0),
  ((43826886509577059 / 6588156132000 : ℝ), 1, 3, 3),
  ((-13822601388735671 / 2196052044000 : ℝ), 1, 3, 2),
  ((-7342505250956477 / 4392104088000 : ℝ), 1, 3, 1),
  ((-21124363625242801 / 3294078066000 : ℝ), 1, 2, 4),
  ((-61452152314194803 / 3294078066000 : ℝ), 1, 2, 3),
  ((48034627943075977 / 8784208176000 : ℝ), 1, 2, 2),
  ((4917797711 / 16733100 : ℝ), 1, 2, 1),
  ((-332874760393 / 12549825 : ℝ), 1, 1, 4),
  ((31882527131 / 8366550 : ℝ), 1, 1, 3),
  ((62933252109 / 11155400 : ℝ), 1, 1, 2),
  ((-53936064 / 1394425 : ℝ), 1, 0, 5),
  ((-48246744266 / 4183275 : ℝ), 1, 0, 4),
  ((8234041193 / 1394425 : ℝ), 1, 0, 3),
  ((238287 / 340 : ℝ), 1, 0, 2),
  ((38636554037582 / 205879879125 : ℝ), 0, 7, 0),
  ((1487507330446907 / 411759758250 : ℝ), 0, 6, 1),
  ((-833708086423 / 1647039033 : ℝ), 0, 6, 0),
  ((2839786721762277 / 183004337000 : ℝ), 0, 5, 2),
  ((-364199233267141 / 68626626375 : ℝ), 0, 5, 1),
  ((-256645016612599 / 549013011000 : ℝ), 0, 5, 0),
  ((6626169017445313 / 263526245280 : ℝ), 0, 4, 3),
  ((-17862819078338381 / 1098026022000 : ℝ), 0, 4, 2),
  ((-155266889750493 / 45751084250 : ℝ), 0, 4, 1),
  ((46383183122117191 / 3294078066000 : ℝ), 0, 3, 4),
  ((-168532299194528689 / 6588156132000 : ℝ), 0, 3, 3),
  ((-4460591248796739 / 2928069392000 : ℝ), 0, 3, 2),
  ((-750828502 / 4183275 : ℝ), 0, 3, 1),
  ((-125921827633 / 4183275 : ℝ), 0, 2, 4),
  ((43639211056 / 4183275 : ℝ), 0, 2, 3),
  ((50419494601 / 11155400 : ℝ), 0, 2, 2),
  ((-16780416128 / 836655 : ℝ), 0, 1, 5),
  ((3594515834 / 836655 : ℝ), 0, 1, 4),
  ((3325542682 / 278885 : ℝ), 0, 1, 3),
  ((323547 / 340 : ℝ), 0, 1, 2),
  ((-2151296 / 255 : ℝ), 0, 0, 5),
  ((1805552 / 255 : ℝ), 0, 0, 4),
  ((112504 / 85 : ℝ), 0, 0, 3)]
/-- Coefficient of `sin φ` in `Ẇ`. -/
def hopfQS_KS : List (ℝ × ℕ × ℕ × ℕ) := [
  ((4791464077283 / 3294078066000 : ℝ), 3, 1, 0),
  ((33540248540981 / 1647039033000 : ℝ), 3, 0, 1),
  ((-839063994671 / 183004337000 : ℝ), 3, 0, 0),
  ((-1125448626883 / 219605204400 : ℝ), 2, 2, 0),
  ((-7878140388181 / 109802602200 : ℝ), 2, 1, 1),
  ((2399558167183 / 219605204400 : ℝ), 2, 1, 0),
  ((-7442302 / 246075 : ℝ), 2, 0, 1),
  ((184657 / 164050 : ℝ), 2, 0, 0),
  ((8798152280401 / 1098026022000 : ℝ), 1, 3, 0),
  ((61587065962807 / 549013011000 : ℝ), 1, 2, 1),
  ((-9625060537093 / 549013011000 : ℝ), 1, 2, 0),
  ((49097918 / 4183275 : ℝ), 1, 1, 1),
  ((-1875781 / 1394425 : ℝ), 1, 1, 0),
  ((943488 / 1394425 : ℝ), 1, 0, 2),
  ((17550988 / 1394425 : ℝ), 1, 0, 1),
  ((-42 / 85 : ℝ), 1, 0, 0),
  ((-19318277018791 / 1098026022000 : ℝ), 0, 4, 0),
  ((-135227939131537 / 549013011000 : ℝ), 0, 3, 1),
  ((23129339873251 / 1098026022000 : ℝ), 0, 3, 0),
  ((-104433298 / 1394425 : ℝ), 0, 2, 1),
  ((-770468 / 1394425 : ℝ), 0, 2, 0),
  ((97844992 / 278885 : ℝ), 0, 1, 2),
  ((-7646764 / 278885 : ℝ), 0, 1, 1),
  ((36 / 85 : ℝ), 0, 1, 0),
  ((12544 / 85 : ℝ), 0, 0, 2),
  ((224 / 85 : ℝ), 0, 0, 1)]
/-- Coefficient of `cos φ` in `Ẇ`. -/
def hopfQS_KC : List (ℝ × ℕ × ℕ × ℕ) := [
  ((-4791464077283 / 1647039033000 : ℝ), 3, 1, 0),
  ((-33540248540981 / 823519516500 : ℝ), 3, 0, 1),
  ((-54163624194571 / 13176312264000 : ℝ), 3, 0, 0),
  ((1125448626883 / 109802602200 : ℝ), 2, 2, 0),
  ((7878140388181 / 54901301100 : ℝ), 2, 1, 1),
  ((5056821836847 / 292806939200 : ℝ), 2, 1, 0),
  ((14884604 / 246075 : ℝ), 2, 0, 1),
  ((802984 / 246075 : ℝ), 2, 0, 0),
  ((-8798152280401 / 549013011000 : ℝ), 1, 3, 0),
  ((-61587065962807 / 274506505500 : ℝ), 1, 2, 1),
  ((-91658256664777 / 4392104088000 : ℝ), 1, 2, 0),
  ((-98195836 / 4183275 : ℝ), 1, 1, 1),
  ((-29701751 / 16733100 : ℝ), 1, 1, 0),
  ((-1886976 / 1394425 : ℝ), 1, 0, 2),
  ((7542904 / 1394425 : ℝ), 1, 0, 1),
  ((-47 / 170 : ℝ), 1, 0, 0),
  ((19318277018791 / 549013011000 : ℝ), 0, 4, 0),
  ((135227939131537 / 274506505500 : ℝ), 0, 3, 1),
  ((221244181625257 / 4392104088000 : ℝ), 0, 3, 0),
  ((208866596 / 1394425 : ℝ), 0, 2, 1),
  ((52502199 / 5577700 : ℝ), 0, 2, 0),
  ((-195689984 / 278885 : ℝ), 0, 1, 2),
  ((-16923272 / 278885 : ℝ), 0, 1, 1),
  ((101 / 170 : ℝ), 0, 1, 0),
  ((-25088 / 85 : ℝ), 0, 0, 2),
  ((-1008 / 85 : ℝ), 0, 0, 1)]

/-- Quadratic part `h₂(c₁, c₂)` of the centre manifold of the witness. -/
def hopfQS_h (c1 c2 : ℝ) : ℝ := 13689*c1^2/65620 + 567*c1*c2/16405 + 10522*c2^2/16405

/-- Coefficient of `c₃ − h₂` in the weight-four part of `Ẇ`. -/
def hopfQS_q (c1 c2 : ℝ) : ℝ := 231*c1^2/34 - 161*c1*c2/10 - 3052*c2^2/85

/-- The weight-four part of `Ẇ`: `−κ₁(c₁² + c₂²)² − 224 (c₃ − h₂)² + (c₃ − h₂) q`. -/
def hopfQS_w4 (c1 c2 c3 : ℝ) : ℝ :=
  -(22482719/1574880) * (c1 ^ 2 + c2 ^ 2) ^ 2 - 224 * (c3 - hopfQS_h c1 c2) ^ 2 +
    (c3 - hopfQS_h c1 c2) * hopfQS_q c1 c2

/-- **The normal-form identity of the witness.** Along the field written in the eigen-coordinates
`c = M z` (`φ = 3c₁ + 4c₂ + 7c₃`, `S = sin φ`, `C = cos φ` kept as atoms), the derivative of `W`
is its weight-four part plus a remainder of weight `≥ 5` and the Taylor remainders of `sin`, `cos`
times polynomials of weight `≥ 1`. -/
@[powerlib_foundation] theorem hopfQS_key (c1 c2 c3 S C : ℝ) :
    dpoly3 hopfQS_W c1 c2 c3 (-4*C*c2/85 - 56*C*c3/85 - 47*C/170 + 2*S*c2/85 + 28*S*c3/85 - 42*S/85 + 126*c1/85 - 83*c2/85 + 70*c3/17 + 47/170)
        (52*C*c2/85 + 728*C*c3/85 + 101*C/170 - 26*S*c2/85 - 364*S*c3/85 + 36*S/85 + 147*c1/85 - 196*c2/85 - 196*c3/17 - 101/170)
        (-28*C*c2/85 - 392*C*c3/85 - 63*C/340 + 14*S*c2/85 + 196*S*c3/85 + 7*S/170 - 21*c1/170 + 14*c2/85 + 14*c3/17 + 63/340) =
      hopfQS_w4 c1 c2 c3 + poly3 hopfQS_R c1 c2 c3 +
        (S - ((3 * c1 + 4 * c2 + 7 * c3) - (3 * c1 + 4 * c2 + 7 * c3) ^ 3 / 6)) * poly3 hopfQS_KS c1 c2 c3 +
        (C - (1 - (3 * c1 + 4 * c2 + 7 * c3) ^ 2 / 2)) * poly3 hopfQS_KC c1 c2 c3 := by
  simp only [hopfQS_W, hopfQS_R, hopfQS_KS, hopfQS_KC, hopfQS_w4, hopfQS_h, hopfQS_q, dpoly3_cons,
    dpoly3_nil, poly3_cons, poly3_nil]
  norm_num
  ring

/-! ## The witness model (static) -/

/-- Eigen-coordinate `c₁` of the witness. -/
def hopfQS_c1 : Dynamics.State 3 →L[ℝ] ℝ :=
  (12 / 85 : ℝ) • EuclideanSpace.proj (0 : Fin 3) + (49 / 170 : ℝ) • EuclideanSpace.proj (1 : Fin 3) +
    (1 / 170 : ℝ) • EuclideanSpace.proj (2 : Fin 3)

/-- Eigen-coordinate `c₂` of the witness. -/
def hopfQS_c2 : Dynamics.State 3 →L[ℝ] ℝ :=
  (14 / 85 : ℝ) • EuclideanSpace.proj (0 : Fin 3) + (-21 / 85 : ℝ) • EuclideanSpace.proj (1 : Fin 3) +
    (-13 / 170 : ℝ) • EuclideanSpace.proj (2 : Fin 3)

/-- Eigen-coordinate `c₃` (the stable mode) of the witness. -/
def hopfQS_c3 : Dynamics.State 3 →L[ℝ] ℝ :=
  (-1 / 85 : ℝ) • EuclideanSpace.proj (0 : Fin 3) + (3 / 170 : ℝ) • EuclideanSpace.proj (1 : Fin 3) +
    (7 / 170 : ℝ) • EuclideanSpace.proj (2 : Fin 3)

@[powerlib_foundation] theorem hopfQS_c_apply (z : Dynamics.State 3) :
    hopfQS_c1 z = 12 / 85 * z 0 + 49 / 170 * z 1 + 1 / 170 * z 2 ∧
    hopfQS_c2 z = 14 / 85 * z 0 + -21 / 85 * z 1 + -13 / 170 * z 2 ∧
    hopfQS_c3 z = -1 / 85 * z 0 + 3 / 170 * z 1 + 7 / 170 * z 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hopfQS_c1, hopfQS_c2, hopfQS_c3]

/-- The state in terms of the eigen-coordinates: `z = T c`,
`T = [[3, 4, 7], [2, −2, −4], [0, 2, 28]]`. -/
@[powerlib_foundation] theorem hopfQS_coords (z : Dynamics.State 3) :
    z 0 = 3 * hopfQS_c1 z + 4 * hopfQS_c2 z + 7 * hopfQS_c3 z ∧
    z 1 = 2 * hopfQS_c1 z - 2 * hopfQS_c2 z - 4 * hopfQS_c3 z ∧
    z 2 = 2 * hopfQS_c2 z + 28 * hopfQS_c3 z := by
  obtain ⟨h1, h2, h3⟩ := hopfQS_c_apply z
  rw [h1, h2, h3]
  refine ⟨by ring, by ring, by ring⟩

/-- A supercritical quasi-static model: `V = √5`, `X_g = 1`, `k_p = −1/4`, `k_i = 21/4`,
`k_P = 4/3`, `P_ref = 3` at `(θ*, 0, I_d*) = (arctan(1/2), 0, 1)` (so `V cos θ* = 2`,
`V sin θ* = 1`). -/
def supercriticalQS : Model := ⟨⟨Real.sqrt 5, 1, -1 / 4, 21 / 4, 4 / 3, 3⟩, Real.arctan (1 / 2), 1⟩

@[powerlib_foundation] theorem supercriticalQS_trig :
    supercriticalQS.params.V * Real.cos supercriticalQS.θ = 2 ∧
      supercriticalQS.params.V * Real.sin supercriticalQS.θ = 1 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt (1 + (1 / 2 : ℝ) ^ 2) = Real.sqrt 5 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
    nlinarith [h5]
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  simp only [supercriticalQS, Real.cos_arctan, Real.sin_arctan, hs]
  constructor <;> field_simp

@[powerlib_foundation] theorem supercriticalQS_isEq :
    IsEq supercriticalQS.params supercriticalQS.θ supercriticalQS.Id := by
  obtain ⟨hc, hs⟩ := supercriticalQS_trig
  refine ⟨?_, ?_⟩
  · rw [hs]; simp [supercriticalQS]
  · unfold power; rw [hc]; simp [supercriticalQS]

/-- The translated field of the witness, `S = sin φ`, `C = cos φ`. -/
@[powerlib_foundation] theorem supercriticalQS_field (z : Dynamics.State 3) :
    supercriticalQS.field z 0 = -1 / 4 * (-2 * Real.sin (z 0) + (1 - Real.cos (z 0)) + z 2) +
        21 / 4 * z 1 ∧
      supercriticalQS.field z 1 = -2 * Real.sin (z 0) + (1 - Real.cos (z 0)) + z 2 ∧
      supercriticalQS.field z 2 =
        2 * (2 - (2 * Real.cos (z 0) - Real.sin (z 0)) * (z 2 + 1)) := by
  obtain ⟨h0, h1, h2⟩ := model_fold_form supercriticalQS_isEq z
  obtain ⟨hc, hs⟩ := supercriticalQS_trig
  rw [hc, hs] at h0 h1 h2
  simp only [supercriticalQS] at h0 h1 h2 ⊢
  refine ⟨by rw [h0]; ring, by rw [h1]; ring, ?_⟩
  rw [one_mul] at h2
  rw [h2]
  ring

/-! ## The witness is locally asymptotically stable (implementation evidence) -/

/-- `sin x − (x − x³/6) = O(x⁴)`. -/
private theorem sin_sub_taylor_isBigO :
    (fun x : ℝ => Real.sin x - (x - x ^ 3 / 6)) =O[𝓝 0] fun x => x ^ 4 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hb := Real.sin_bound hx.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have h5 : |x| ^ 5 ≤ |x| ^ 4 := pow_le_pow_of_le_one (abs_nonneg _) hx.le (by norm_num)
  have h4 : 0 ≤ |x| ^ 4 := by positivity
  linarith

/-- The Lie derivative of `W` along the witness field. -/
private theorem supercriticalQS_lie (z : Dynamics.State 3) :
    fderiv ℝ (fun z => poly3 hopfQS_W (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z)) z
        (supercriticalQS.field z) =
      hopfQS_w4 (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) +
        poly3 hopfQS_R (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) +
        (Real.sin (z 0) - (z 0 - z 0 ^ 3 / 6)) *
          poly3 hopfQS_KS (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) +
        (Real.cos (z 0) - (1 - z 0 ^ 2 / 2)) *
          poly3 hopfQS_KC (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) := by
  rw [fderiv_poly3_apply]
  have key := hopfQS_key (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) (Real.sin (z 0))
    (Real.cos (z 0))
  have hφ : 3 * hopfQS_c1 z + 4 * hopfQS_c2 z + 7 * hopfQS_c3 z = z 0 :=
    (hopfQS_coords z).1.symm
  rw [hφ] at key
  rw [← key]
  obtain ⟨f0, f1, f2⟩ := supercriticalQS_field z
  obtain ⟨a1, a2, a3⟩ := hopfQS_c_apply (supercriticalQS.field z)
  obtain ⟨b1, b2, b3⟩ := hopfQS_c_apply z
  rw [a1, a2, a3, f0, f1, f2, b1, b2, b3]
  exact congr (congr (congrArg _ (by ring)) (by ring)) (by ring)

/-- `W = (c₁² + c₂²)/2 + 32 (c₃ − h₂)² + W₃₄(c₁, c₂)`. -/
private theorem hopfQS_W_eq (c1 c2 c3 : ℝ) :
    poly3 hopfQS_W c1 c2 c3 = (c1 ^ 2 + c2 ^ 2) / 2 + 32 * (c3 - hopfQS_h c1 c2) ^ 2 +
      poly3 hopfQS_W34 c1 c2 0 := by
  simp only [hopfQS_W, hopfQS_W34, hopfQS_h, poly3_cons, poly3_nil]
  norm_num
  ring

/-- `w₄ ≤ −((c₁² + c₂²)² + (c₃ − h₂)²)`. -/
private theorem hopfQS_w4_le (c1 c2 c3 : ℝ) :
    hopfQS_w4 c1 c2 c3 ≤ -((c1 ^ 2 + c2 ^ 2) ^ 2 + (c3 - hopfQS_h c1 c2) ^ 2) := by
  set v := c3 - hopfQS_h c1 c2 with hv
  set Q := c1 ^ 2 + c2 ^ 2 with hQ
  have hq : |hopfQS_q c1 c2| ≤ 51 * Q := by
    unfold hopfQS_q
    have h1 : |c1 * c2| ≤ Q / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|c1| - |c2|), sq_abs c1, sq_abs c2]
    have := abs_add_three (231 * c1 ^ 2 / 34) (-(161 * c1 * c2 / 10)) (-(3052 * c2 ^ 2 / 85))
    have e1 : |231 * c1 ^ 2 / 34| = 231 / 34 * c1 ^ 2 := by
      rw [abs_of_nonneg (by positivity)]; ring
    have e2 : |-(161 * c1 * c2 / 10)| = 161 / 10 * |c1 * c2| := by
      rw [abs_neg, show 161 * c1 * c2 / 10 = 161 / 10 * (c1 * c2) by ring, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 161 / 10)]
    have e3 : |-(3052 * c2 ^ 2 / 85)| = 3052 / 85 * c2 ^ 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]; ring
    have hsum : 231 * c1 ^ 2 / 34 - 161 * c1 * c2 / 10 - 3052 * c2 ^ 2 / 85 =
        231 * c1 ^ 2 / 34 + -(161 * c1 * c2 / 10) + -(3052 * c2 ^ 2 / 85) := by ring
    rw [hsum]
    rw [e1, e2, e3] at this
    nlinarith [sq_nonneg c1, sq_nonneg c2]
  have hvq : v * hopfQS_q c1 c2 ≤ 112 * v ^ 2 + 2601 / 448 * Q ^ 2 := by
    have h1 : v * hopfQS_q c1 c2 ≤ |v| * (51 * Q) := by
      calc v * hopfQS_q c1 c2 ≤ |v * hopfQS_q c1 c2| := le_abs_self _
        _ = |v| * |hopfQS_q c1 c2| := abs_mul _ _
        _ ≤ |v| * (51 * Q) := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
    nlinarith [sq_nonneg (|v| - 51 / 224 * Q), sq_abs v]
  unfold hopfQS_w4
  rw [← hv, ← hQ]
  have hQ0 : 0 ≤ Q ^ 2 := sq_nonneg _
  nlinarith

/-- `|h₂(c₁, c₂)| ≤ (|c₁| + |c₂|)²`. -/
private theorem abs_hopfQS_h_le (c1 c2 : ℝ) : |hopfQS_h c1 c2| ≤ (|c1| + |c2|) ^ 2 := by
  unfold hopfQS_h
  have h12 : |c1 * c2| = |c1| * |c2| := abs_mul _ _
  have := abs_add_three (13689 * c1 ^ 2 / 65620) (567 * c1 * c2 / 16405) (10522 * c2 ^ 2 / 16405)
  have e1 : |13689 * c1 ^ 2 / 65620| = 13689 / 65620 * c1 ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; ring
  have e2 : |567 * c1 * c2 / 16405| = 567 / 16405 * (|c1| * |c2|) := by
    rw [show 567 * c1 * c2 / 16405 = 567 / 16405 * (c1 * c2) by ring, abs_mul, h12,
      abs_of_pos (by norm_num : (0 : ℝ) < 567 / 16405)]
  have e3 : |10522 * c2 ^ 2 / 16405| = 10522 / 16405 * c2 ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; ring
  rw [e1, e2, e3] at this
  nlinarith [sq_abs c1, sq_abs c2, abs_nonneg c1, abs_nonneg c2, mul_nonneg (abs_nonneg c1)
    (abs_nonneg c2)]

/-- The eigen-coordinates vanish only at the origin. -/
private theorem hopfQS_eq_zero {z : Dynamics.State 3} (h1 : hopfQS_c1 z = 0)
    (h2 : hopfQS_c2 z = 0) (h3 : hopfQS_c3 z = 0) : z = 0 := by
  obtain ⟨e0, e1, e2⟩ := hopfQS_coords z
  simp only [h1, h2, h3, mul_zero, add_zero, sub_zero] at e0 e1 e2
  ext i
  fin_cases i
  · simpa using e0
  · simpa using e1
  · simpa using e2

/-- The weighted size `σ = |c₁| + |c₂| + √|c₃ − h₂(c₁, c₂)|` of a state. -/
def hopfQS_size (z : Dynamics.State 3) : ℝ :=
  |hopfQS_c1 z| + |hopfQS_c2 z| + Real.sqrt |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)|

/-- The weight-four comparison form `(c₁² + c₂²)² + (c₃ − h₂)²`. -/
def hopfQS_q4 (z : Dynamics.State 3) : ℝ :=
  (hopfQS_c1 z ^ 2 + hopfQS_c2 z ^ 2) ^ 2 + (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)) ^ 2

/-- The quadratic comparison form `(c₁² + c₂²)/2 + 32 (c₃ − h₂)²`. -/
def hopfQS_q2 (z : Dynamics.State 3) : ℝ :=
  (hopfQS_c1 z ^ 2 + hopfQS_c2 z ^ 2) / 2 +
    32 * (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)) ^ 2

private theorem hopfQS_size_nonneg (z : Dynamics.State 3) : 0 ≤ hopfQS_size z := by
  unfold hopfQS_size; positivity

private theorem hopfQS_size_tendsto : Tendsto hopfQS_size (𝓝 0) (𝓝 0) := by
  have hc : Continuous hopfQS_size := by
    unfold hopfQS_size hopfQS_h
    fun_prop
  simpa [hopfQS_size, hopfQS_h] using hc.tendsto 0

private theorem hopfQS_sqrt_sq (z : Dynamics.State 3) :
    |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)| =
      Real.sqrt |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)| ^ 2 :=
  (Real.sq_sqrt (abs_nonneg _)).symm

private theorem hopfQS_c1_isBigO : (fun z => hopfQS_c1 z) =O[𝓝 0] hopfQS_size :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (hopfQS_size_nonneg z)]
    unfold hopfQS_size
    have := Real.sqrt_nonneg |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)|
    linarith [abs_nonneg (hopfQS_c2 z)])

private theorem hopfQS_c2_isBigO : (fun z => hopfQS_c2 z) =O[𝓝 0] hopfQS_size :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (hopfQS_size_nonneg z)]
    unfold hopfQS_size
    have := Real.sqrt_nonneg |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)|
    linarith [abs_nonneg (hopfQS_c1 z)])

private theorem hopfQS_c3_isBigO :
    (fun z => hopfQS_c3 z) =O[𝓝 0] fun z => hopfQS_size z ^ 2 :=
  IsBigO.of_bound 2 (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (hopfQS_size z))]
    have hh := abs_hopfQS_h_le (hopfQS_c1 z) (hopfQS_c2 z)
    have h3 : |hopfQS_c3 z| ≤ |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)| +
        |hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)| := by
      have := abs_add_le (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z))
        (hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z))
      rwa [sub_add_cancel] at this
    rw [hopfQS_sqrt_sq z] at h3
    unfold hopfQS_size
    have hw := Real.sqrt_nonneg |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)|
    nlinarith [abs_nonneg (hopfQS_c1 z), abs_nonneg (hopfQS_c2 z)])

private theorem hopfQS_z0_isBigO : (fun z : Dynamics.State 3 => z 0) =O[𝓝 0] hopfQS_size := by
  have hc1 : (fun z => hopfQS_c3 z) =O[𝓝 0] hopfQS_size :=
    (hopfQS_c3_isBigO.trans (Dynamics.isBigO_pow_of_tendsto hopfQS_size_tendsto
      (by norm_num : 1 ≤ 2))).congr_right fun z => pow_one _
  exact (((hopfQS_c1_isBigO.const_mul_left 3).add (hopfQS_c2_isBigO.const_mul_left 4)).add
    (hc1.const_mul_left 7)).congr_left fun z => ((hopfQS_coords z).1).symm

/-- The remainder of `Ẇ` is `O(σ⁵)`. -/
private theorem hopfQS_remainder_isBigO :
    (fun z : Dynamics.State 3 => poly3 hopfQS_R (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) +
      (Real.sin (z 0) - (z 0 - z 0 ^ 3 / 6)) *
        poly3 hopfQS_KS (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) +
      (Real.cos (z 0) - (1 - z 0 ^ 2 / 2)) *
        poly3 hopfQS_KC (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z)) =O[𝓝 0]
      fun z => hopfQS_size z ^ 5 := by
  have ht : Tendsto (fun z : Dynamics.State 3 => z 0) (𝓝 0) (𝓝 0) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) :
      Dynamics.State 3 →L[ℝ] ℝ).continuous.tendsto' 0 0 (by simp)
  have hs4 : (fun z : Dynamics.State 3 => Real.sin (z 0) - (z 0 - z 0 ^ 3 / 6)) =O[𝓝 0]
      fun z => hopfQS_size z ^ 4 :=
    (sin_sub_taylor_isBigO.comp_tendsto ht).trans (hopfQS_z0_isBigO.pow 4)
  have hc4 : (fun z : Dynamics.State 3 => Real.cos (z 0) - (1 - z 0 ^ 2 / 2)) =O[𝓝 0]
      fun z => hopfQS_size z ^ 4 := by
    have := (Dynamics.one_sub_cos_sub_isBigO.comp_tendsto ht).trans (hopfQS_z0_isBigO.pow 4)
    exact (this.neg_left).congr_left fun z => by simp only [Function.comp]; ring
  have hKS := isBigO_poly3_weight hopfQS_size_tendsto hopfQS_c1_isBigO hopfQS_c2_isBigO
    hopfQS_c3_isBigO hopfQS_KS (k := 1) (by simp [hopfQS_KS])
  have hKC := isBigO_poly3_weight hopfQS_size_tendsto hopfQS_c1_isBigO hopfQS_c2_isBigO
    hopfQS_c3_isBigO hopfQS_KC (k := 1) (by simp [hopfQS_KC])
  have hR := isBigO_poly3_weight hopfQS_size_tendsto hopfQS_c1_isBigO hopfQS_c2_isBigO
    hopfQS_c3_isBigO hopfQS_R (k := 5) (by simp [hopfQS_R])
  exact (hR.add ((hs4.mul hKS).congr_right fun z => by ring)).add
    ((hc4.mul hKC).congr_right fun z => by ring)

/-- `σ⁴ ≤ 27 ((c₁² + c₂²)² + (c₃ − h₂)²)`. -/
private theorem hopfQS_size4_isBigO : (fun z => hopfQS_size z ^ 4) =O[𝓝 0] hopfQS_q4 :=
  IsBigO.of_bound 27 (Eventually.of_forall fun z => by
    have hq0 : 0 ≤ hopfQS_q4 z := by unfold hopfQS_q4; positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hopfQS_size_nonneg z) 4),
      abs_of_nonneg hq0]
    unfold hopfQS_size hopfQS_q4
    set x := |hopfQS_c1 z|
    set y := |hopfQS_c2 z|
    set w := Real.sqrt |hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)|
    have hx : x ^ 2 = hopfQS_c1 z ^ 2 := sq_abs _
    have hy : y ^ 2 = hopfQS_c2 z ^ 2 := sq_abs _
    have hw : (w ^ 2) ^ 2 = (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)) ^ 2 := by
      rw [← hopfQS_sqrt_sq z, sq_abs]
    have hx0 : 0 ≤ x := abs_nonneg _
    have hy0 : 0 ≤ y := abs_nonneg _
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have h1 : (x + y + w) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + w ^ 2) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - w), sq_nonneg (x - w)]
    have h2 : (x ^ 2 + y ^ 2 + w ^ 2) ^ 2 ≤ 3 * ((x ^ 2) ^ 2 + (y ^ 2) ^ 2 + (w ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - w ^ 2), sq_nonneg (x ^ 2 - w ^ 2)]
    have h3 : (x + y + w) ^ 4 ≤ 9 * (x ^ 2 + y ^ 2 + w ^ 2) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h1 2
      nlinarith
    rw [← hx, ← hy, ← hw]
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), mul_nonneg (sq_nonneg x) (sq_nonneg y)])

private theorem hopfQS_q4_pos : ∀ᶠ z in 𝓝[≠] (0 : Dynamics.State 3), 0 < hopfQS_q4 z := by
  refine eventually_nhdsWithin_of_forall fun z hz => ?_
  have hz' : z ≠ 0 := hz
  unfold hopfQS_q4
  by_contra hle
  push Not at hle
  have hA0 := sq_nonneg (hopfQS_c1 z ^ 2 + hopfQS_c2 z ^ 2)
  have hB0 := sq_nonneg (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z))
  have hA : (hopfQS_c1 z ^ 2 + hopfQS_c2 z ^ 2) ^ 2 = 0 := by linarith
  have hB : (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)) ^ 2 = 0 := by linarith
  have hA' : hopfQS_c1 z ^ 2 + hopfQS_c2 z ^ 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp hA
  have h1 : hopfQS_c1 z = 0 := by nlinarith [sq_nonneg (hopfQS_c1 z), sq_nonneg (hopfQS_c2 z)]
  have h2 : hopfQS_c2 z = 0 := by nlinarith [sq_nonneg (hopfQS_c1 z), sq_nonneg (hopfQS_c2 z)]
  have h3 : hopfQS_c3 z = 0 := by
    have := pow_eq_zero_iff two_ne_zero |>.mp hB
    rw [h1, h2] at this
    simpa [hopfQS_h] using this
  exact hz' (hopfQS_eq_zero h1 h2 h3)

private theorem hopfQS_q2_pos : ∀ᶠ z in 𝓝[≠] (0 : Dynamics.State 3), 0 < hopfQS_q2 z := by
  filter_upwards [hopfQS_q4_pos] with z hz
  unfold hopfQS_q4 at hz
  unfold hopfQS_q2
  by_contra hle
  push Not at hle
  have h0 : hopfQS_c1 z ^ 2 + hopfQS_c2 z ^ 2 = 0 := by
    nlinarith [sq_nonneg (hopfQS_c1 z), sq_nonneg (hopfQS_c2 z),
      sq_nonneg (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z))]
  have h1 : (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (hopfQS_c1 z), sq_nonneg (hopfQS_c2 z),
      sq_nonneg (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z))]
  rw [h0, h1] at hz
  norm_num at hz

/-- `W > 0` on a punctured neighbourhood: `W = q₂ + O(τ³)`, `τ = |c₁| + |c₂|`. -/
private theorem hopfQS_W_pos : ∀ᶠ z in 𝓝[≠] (0 : Dynamics.State 3),
    0 < poly3 hopfQS_W (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z) := by
  have hτ0 : Tendsto (fun z : Dynamics.State 3 => |hopfQS_c1 z| + |hopfQS_c2 z|) (𝓝 0)
      (𝓝 0) := by
    have hc : Continuous (fun z : Dynamics.State 3 => |hopfQS_c1 z| + |hopfQS_c2 z|) := by
      fun_prop
    simpa using hc.tendsto 0
  have ha' : (fun z => hopfQS_c1 z) =O[𝓝 0] fun z => |hopfQS_c1 z| + |hopfQS_c2 z| :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans (le_abs_self _))
  have hb' : (fun z => hopfQS_c2 z) =O[𝓝 0] fun z => |hopfQS_c1 z| + |hopfQS_c2 z| :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans (le_abs_self _))
  have h34 := isBigO_poly3_weight hτ0 ha' hb' (isBigO_zero _ _) hopfQS_W34 (k := 3)
    (by simp [hopfQS_W34])
  have hτ2 : (fun z => (|hopfQS_c1 z| + |hopfQS_c2 z|) ^ 2) =O[𝓝 0] hopfQS_q2 :=
    IsBigO.of_bound 4 (Eventually.of_forall fun z => by
      have hp0 : 0 ≤ hopfQS_q2 z := by unfold hopfQS_q2; positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hp0]
      unfold hopfQS_q2
      nlinarith [sq_abs (hopfQS_c1 z), sq_abs (hopfQS_c2 z),
        sq_nonneg (|hopfQS_c1 z| - |hopfQS_c2 z|),
        sq_nonneg (hopfQS_c3 z - hopfQS_h (hopfQS_c1 z) (hopfQS_c2 z))])
  refine Dynamics.eventually_pos_of_isLittleO (q := hopfQS_q2) hopfQS_q2_pos ?_
  refine ((h34.trans_isLittleO ((Dynamics.isLittleO_pow_of_tendsto hτ0
    (by norm_num : 2 < 3)).trans_isBigO hτ2)).mono nhdsWithin_le_nhds).congr_left fun z => ?_
  unfold hopfQS_q2
  rw [hopfQS_W_eq]
  ring

/-- `Ẇ < 0` on a punctured neighbourhood: `Ẇ ≤ −q₄ + O(σ⁵)`, `σ⁵ = o(q₄)`. -/
private theorem hopfQS_lie_neg : ∀ᶠ z in 𝓝[≠] (0 : Dynamics.State 3),
    fderiv ℝ (fun z => poly3 hopfQS_W (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z)) z
      (supercriticalQS.field z) < 0 := by
  refine Dynamics.eventually_neg_of_le_of_isLittleO (q := hopfQS_q4) hopfQS_q4_pos
    (Eventually.of_forall fun z => ?_)
    ((hopfQS_remainder_isBigO.trans_isLittleO ((Dynamics.isLittleO_pow_of_tendsto
      hopfQS_size_tendsto (by norm_num : 4 < 5)).trans_isBigO hopfQS_size4_isBigO)).mono
      nhdsWithin_le_nhds)
  rw [supercriticalQS_lie]
  have := hopfQS_w4_le (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z)
  unfold hopfQS_q4
  linarith

/-- **The supercritical quasi-static witness is locally asymptotically stable** (a weak focus). -/
private theorem supercriticalQS_las : LocalAsymptoticStable supercriticalQS.field 0 := by
  have hfz : supercriticalQS.field 0 = 0 := by
    have := field_point_eq_zero supercriticalQS.params supercriticalQS_isEq
    simpa [Model.field] using this
  exact Dynamics.localAsymptoticStable_of_eventually_lyapunov
    (W := fun z => poly3 hopfQS_W (hopfQS_c1 z) (hopfQS_c2 z) (hopfQS_c3 z)) (by norm_num)
    (contDiff_model_field _) hfz (contDiff_poly3 _ _ _ _) (by simp [hopfQS_W]) hopfQS_W_pos
    hopfQS_lie_neg

/-! ## Connection conclusions -/

/-- The supercritical quasi-static witness (`V = √5`, `X_g = 1`, `k_p = −1/4`, `k_i = 21/4`,
`k_P = 4/3`, `P_ref = 3`, `(θ*, I_d*) = (arctan(1/2), 1)`) is locally asymptotically stable: a
weak focus, its Jacobian has the eigenvalues `±3i` and `−7/2`. -/
@[powerlib_domain] theorem supercriticalQS_mem_den_locallyAsymptoticallyStable :
    connection% (supercriticalQS ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isAutonomous.mem_den_flow]
  exact supercriticalQS_las

/-- The witness Jacobian is on the Hopf boundary: `a₂ = 7/2`, `a₁ = 9`, `a₀ = 63/2 = a₂a₁`, so
`tr J · m₂(J) = det J` and the strict Routh–Hurwitz condition fails. -/
@[powerlib_foundation] theorem supercriticalQS_routh_boundary :
    (jac supercriticalQS.params supercriticalQS.θ supercriticalQS.Id).trace *
        Criteria.principalMinorSum
          (jac supercriticalQS.params supercriticalQS.θ supercriticalQS.Id) =
      (jac supercriticalQS.params supercriticalQS.θ supercriticalQS.Id).det := by
  obtain ⟨hc, hs⟩ := supercriticalQS_trig
  have heq := supercriticalQS_isEq
  rw [trace_jac, principalMinorSum_jac _ heq.1, det_jac _ heq.1]
  unfold a2 a1 a0
  have hcos2 : supercriticalQS.params.V ^ 2 * Real.cos (2 * supercriticalQS.θ) = 3 := by
    rw [Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq supercriticalQS.θ
    nlinarith [hc, hs]
  have e1 : supercriticalQS.params.V * Real.cos supercriticalQS.θ / 2 *
      (3 * supercriticalQS.params.kP + 2 * supercriticalQS.params.kp) = 7 / 2 := by
    rw [hc]; simp [supercriticalQS]; norm_num
  have e2 : supercriticalQS.params.V / 2 * (3 * supercriticalQS.params.V *
      supercriticalQS.params.kP * supercriticalQS.params.kp * Real.cos (2 * supercriticalQS.θ) +
      2 * supercriticalQS.params.ki * Real.cos supercriticalQS.θ) = 9 := by
    have : supercriticalQS.params.V / 2 * (3 * supercriticalQS.params.V *
        supercriticalQS.params.kP * supercriticalQS.params.kp *
        Real.cos (2 * supercriticalQS.θ) + 2 * supercriticalQS.params.ki *
        Real.cos supercriticalQS.θ) = 3 / 2 * supercriticalQS.params.kP *
        supercriticalQS.params.kp * (supercriticalQS.params.V ^ 2 *
        Real.cos (2 * supercriticalQS.θ)) + supercriticalQS.params.ki *
        (supercriticalQS.params.V * Real.cos supercriticalQS.θ) := by ring
    rw [this, hcos2, hc]; simp [supercriticalQS]; norm_num
  have e3 : 3 / 2 * supercriticalQS.params.V ^ 2 * supercriticalQS.params.kP *
      supercriticalQS.params.ki * Real.cos (2 * supercriticalQS.θ) = 63 / 2 := by
    have : 3 / 2 * supercriticalQS.params.V ^ 2 * supercriticalQS.params.kP *
        supercriticalQS.params.ki * Real.cos (2 * supercriticalQS.θ) =
        3 / 2 * supercriticalQS.params.kP * supercriticalQS.params.ki *
        (supercriticalQS.params.V ^ 2 * Real.cos (2 * supercriticalQS.θ)) := by ring
    rw [this, hcos2]; simp [supercriticalQS]; norm_num
  rw [e1, e2, e3]
  norm_num

/-- **The local asymptotic translation is not exact** (gains of arbitrary sign): the supercritical
witness is locally asymptotically stable, but `tr J · m₂(J) = det J`, so it meets no strict
Routh–Hurwitz requirement. -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := supercriticalQS_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hs : Meets supercriticalQS .jacobianStable :=
    hmem .jacobianStable (by simp [family, translate])
  have := hs.2.2
  rw [supercriticalQS_routh_boundary] at this
  exact lt_irrefl _ this

end powerlib.GFL.PowerLoop.QuasiStatic
