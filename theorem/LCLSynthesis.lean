import theorem.LCLPassivity

noncomputable section
namespace powerlib.LCL.PassiveWitness

-- A symbolic witness generated from model coefficients, with every endpoint
-- independently checked below. No submitted Lyapunov matrix is required.
def coupling (a d b e : ℝ) : ℝ := a*e+b*d
def gap (a d b e k : ℝ) : ℝ := a*d*(a+d)+k*(a*b+d*e)
def denominator (a d b e k : ℝ) : ℝ := 2*k*coupling a d b e*gap a d b e k

def n11 (a d b e k : ℝ) : ℝ :=
  a ^ 2 * d * e * k + a * d ^ 2 * b * k + a * d ^ 2 * e * k + a * d ^ 2 * k ^ 2 + a * b * e * k ^ 2 +
    a * e ^ 2 * k ^ 2 + a * e * k ^ 3 + d ^ 3 * b * k + d ^ 3 * k ^ 2 + d * b * k ^ 3 +
    d * k ^ 2 * ((b-e)^2 + b*e + e^2)

def n12 (a d b e k : ℝ) : ℝ :=
  a ^ 2 * d ^ 2 * k + a ^ 2 * e ^ 2 * k + a ^ 2 * e * k ^ 2 + a * d ^ 3 * k - a * d * b * e * k +
    a * d * b * k ^ 2 + a * d * e ^ 2 * k - d ^ 2 * b * e * k

def n13 (a d b e k : ℝ) : ℝ :=
  - a ^ 2 * d * k ^ 2 - a * d ^ 2 * k ^ 2 +
    a * b * e * k ^ 2 - a * e ^ 2 * k ^ 2 - a * e * k ^ 3 - d * b ^ 2 * k ^ 2 +
    d * b * e * k ^ 2 - d * b * k ^ 3

def n22 (a d b e k : ℝ) : ℝ :=
  a ^ 3 * d ^ 2 + a ^ 3 * e ^ 2 + a ^ 3 * e * k + a ^ 2 * d ^ 3 + a ^ 2 * d * b * k +
    a ^ 2 * d * e ^ 2 + a ^ 2 * d * e * k + a * d ^ 2 * b ^ 2 + a * d ^ 2 * b * k +
    a * d ^ 2 * e * k + a * b ^ 2 * e * k + a * b * e * k ^ 2 + a * e ^ 3 * k + a * e ^ 2 * k ^ 2 +
    d ^ 3 * b ^ 2 + d ^ 3 * b * k + d * b ^ 3 * k + d * b ^ 2 * k ^ 2 + d * b * e ^ 2 * k +
    d * b * e * k ^ 2

def n23 (a d b e k : ℝ) : ℝ :=
  - a ^ 3 * d * k - a ^ 2 * d ^ 2 * k + a ^ 2 * b * e * k - a * d * b ^ 2 * k +
    a * d * b * e * k - a * d * e * k ^ 2 - d ^ 2 * b ^ 2 * k - d ^ 2 * b * k ^ 2

def n33 (a d b e k : ℝ) : ℝ :=
  a ^ 3 * e * k + a ^ 3 * k ^ 2 + a ^ 2 * d * b * k + a ^ 2 * d * e * k + a ^ 2 * d * k ^ 2 +
    a * d ^ 2 * b * k + 2 * a * b ^ 2 * k ^ 2 - a * b * e * k ^ 2 + a * e ^ 2 * k ^ 2 +
    a * e * k ^ 3 + d * b ^ 2 * k ^ 2 + d * b * e * k ^ 2 + d * b * k ^ 3

def minorNumerator (a d b e k : ℝ) : ℝ :=
  a ^ 4 * d ^ 3 + a ^ 4 * d * e ^ 2 + a ^ 4 * d * e * k + 2 * a ^ 3 * d ^ 4 +
    2 * a ^ 3 * d ^ 2 * b * k + 2 * a ^ 3 * d ^ 2 * e ^ 2 + 2 * a ^ 3 * d ^ 2 * e * k +
    a ^ 3 * b * e ^ 2 * k + a ^ 3 * b * e * k ^ 2 + a ^ 2 * d ^ 5 + a ^ 2 * d ^ 3 * b ^ 2 +
    4 * a ^ 2 * d ^ 3 * b * k + a ^ 2 * d ^ 3 * e ^ 2 + 3 * a ^ 2 * d ^ 3 * e * k +
    a ^ 2 * d ^ 3 * k ^ 2 + a ^ 2 * d * b ^ 2 * e * k + a ^ 2 * d * b ^ 2 * k ^ 2 +
    2 * a ^ 2 * d * b * e ^ 2 * k + 3 * a ^ 2 * d * b * e * k ^ 2 + 2 * a ^ 2 * d * e ^ 3 * k +
    3 * a ^ 2 * d * e ^ 2 * k ^ 2 + a ^ 2 * d * e * k ^ 3 + 2 * a * d ^ 4 * b ^ 2 +
    4 * a * d ^ 4 * b * k + 2 * a * d ^ 4 * e * k + 2 * a * d ^ 4 * k ^ 2 +
    2 * a * d ^ 2 * b ^ 3 * k + 4 * a * d ^ 2 * b ^ 2 * k ^ 2 + 3 * a * d ^ 2 * b * e ^ 2 * k +
    4 * a * d ^ 2 * b * e * k ^ 2 + 2 * a * d ^ 2 * b * k ^ 3 + 2 * a * d ^ 2 * e ^ 3 * k +
    5 * a * d ^ 2 * e ^ 2 * k ^ 2 + 2 * a * d ^ 2 * e * k ^ 3 + a * b ^ 3 * e * k ^ 2 +
    a * b ^ 2 * e ^ 2 * k ^ 2 + 2 * a * b ^ 2 * e * k ^ 3 + a * b * e ^ 3 * k ^ 2 +
    2 * a * b * e ^ 2 * k ^ 3 + a * b * e * k ^ 4 + a * e ^ 4 * k ^ 2 + 2 * a * e ^ 3 * k ^ 3 +
    a * e ^ 2 * k ^ 4 + d ^ 5 * b ^ 2 + 2 * d ^ 5 * b * k + d ^ 5 * k ^ 2 +
    4 * d ^ 3 * b ^ 2 * k ^ 2 + 2 * d ^ 3 * b * k ^ 3 + 3 * d ^ 3 * e ^ 2 * k ^ 2 +
    d ^ 3 * e * k ^ 3 + 2 * d * b ^ 3 * k ^ 3 + d * b ^ 2 * k ^ 4 + 2 * d * b * e ^ 2 * k ^ 3 +
    d * b * e * k ^ 4 + 2 * d * e ^ 3 * k ^ 3 + d ^ 3 * b * k * ((b-e)^2 + b^2 + b*e + e^2) +
    d * k ^ 2 * ((b-e)^2 * (b^2+e^2) + b^3*e + b^2*e^2 + b*e^3 + e^4)

def detNumerator (a d b e k : ℝ) : ℝ :=
  a ^ 4 * d ^ 2 + a ^ 4 * e ^ 2 + 2 * a ^ 4 * e * k + a ^ 4 * k ^ 2 + 2 * a ^ 3 * d ^ 3 +
    2 * a ^ 3 * d * b * k + 2 * a ^ 3 * d * e ^ 2 + 4 * a ^ 3 * d * e * k + 2 * a ^ 3 * d * k ^ 2 +
    a ^ 2 * d ^ 4 + a ^ 2 * d ^ 2 * b ^ 2 + 4 * a ^ 2 * d ^ 2 * b * k + a ^ 2 * d ^ 2 * e ^ 2 +
    4 * a ^ 2 * d ^ 2 * e * k + 2 * a ^ 2 * d ^ 2 * k ^ 2 + 2 * a ^ 2 * b ^ 2 * e * k +
    3 * a ^ 2 * b ^ 2 * k ^ 2 + 2 * a ^ 2 * b * e * k ^ 2 + 2 * a ^ 2 * b * k ^ 3 +
    2 * a ^ 2 * e ^ 3 * k + 5 * a ^ 2 * e ^ 2 * k ^ 2 + 4 * a ^ 2 * e * k ^ 3 +
    2 * a * d ^ 3 * b ^ 2 + 4 * a * d ^ 3 * b * k + 2 * a * d ^ 3 * e * k + 2 * a * d ^ 3 * k ^ 2 +
    2 * a * d * b ^ 3 * k + 2 * a * d * b ^ 2 * e * k + 6 * a * d * b ^ 2 * k ^ 2 +
    2 * a * d * b * e ^ 2 * k + 4 * a * d * b * e * k ^ 2 + 2 * a * d * b * k ^ 3 +
    2 * a * d * e ^ 3 * k + 6 * a * d * e ^ 2 * k ^ 2 + 2 * a * d * e * k ^ 3 + d ^ 4 * b ^ 2 +
    2 * d ^ 4 * b * k + d ^ 4 * k ^ 2 + 2 * d ^ 2 * b ^ 3 * k + 5 * d ^ 2 * b ^ 2 * k ^ 2 +
    2 * d ^ 2 * b * e ^ 2 * k + 2 * d ^ 2 * b * e * k ^ 2 + 4 * d ^ 2 * b * k ^ 3 +
    3 * d ^ 2 * e ^ 2 * k ^ 2 + 2 * d ^ 2 * e * k ^ 3 + 2 * b ^ 4 * k ^ 2 + 4 * b ^ 3 * k ^ 3 +
    4 * b ^ 2 * e ^ 2 * k ^ 2 + 4 * b ^ 2 * e * k ^ 3 + 2 * b ^ 2 * k ^ 4 + 4 * b * e ^ 2 * k ^ 3 +
    4 * b * e * k ^ 4 + 2 * e ^ 4 * k ^ 2 + 4 * e ^ 3 * k ^ 3 + 2 * e ^ 2 * k ^ 4 + (a-d)^2 * k^4

def matrix (a d b e k : ℝ) : SymmetricMatrix :=
  let q := denominator a d b e k
  ⟨n11 a d b e k / q, n12 a d b e k / q, n13 a d b e k / q,
    n22 a d b e k / q, n23 a d b e k / q, n33 a d b e k / q⟩

@[powerlib_foundation] theorem coupling_pos {a d b e : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (had : 0 < a ∨ 0 < d) :
    0 < coupling a d b e := by
  rcases had with ha' | hd' <;> dsimp [coupling] <;> positivity

@[powerlib_foundation] theorem gap_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k)
    (had : 0 < a ∨ 0 < d) : 0 < gap a d b e k := by
  rcases had with ha' | hd' <;> dsimp [gap] <;> positivity

@[powerlib_foundation] theorem n11_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k)
    (had : 0 < a ∨ 0 < d) : 0 < n11 a d b e k := by
  rcases had with ha' | hd' <;> dsimp [n11] <;> positivity

@[powerlib_foundation] theorem minorNumerator_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k)
    (had : 0 < a ∨ 0 < d) : 0 < minorNumerator a d b e k := by
  rcases had with ha' | hd' <;> dsimp [minorNumerator] <;> positivity

@[powerlib_foundation] theorem detNumerator_pos {a d b e k : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hb : 0 < b) (he : 0 < e) (hk : 0 < k) :
    0 < detNumerator a d b e k := by
  dsimp [detNumerator]
  positivity

set_option maxHeartbeats 4000000 in
@[powerlib_foundation] theorem minor_identity (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    (matrix a d b e k).minor2 =
      k * coupling a d b e * minorNumerator a d b e k / (denominator a d b e k)^2 := by
  dsimp [matrix, SymmetricMatrix.minor2]
  field_simp [hq]
  dsimp [n11,n12,n22,coupling,minorNumerator]
  ring

set_option maxHeartbeats 4000000 in
@[powerlib_foundation] theorem det_identity (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) :
    (matrix a d b e k).det =
      k^2 * (coupling a d b e)^2 * gap a d b e k * detNumerator a d b e k /
        (denominator a d b e k)^3 := by
  dsimp [matrix, SymmetricMatrix.det]
  field_simp [hq]
  dsimp [n11,n12,n13,n22,n23,n33,coupling,gap,detNumerator]
  ring

@[powerlib_foundation] theorem eq11 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) : -2*a*(matrix a d b e k).p11 + 2*k*(matrix a d b e k).p12 = -1 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11,n12,n13,n22,n23,n33,denominator,coupling,gap]
  ring

@[powerlib_foundation] theorem eq12 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) : -b*(matrix a d b e k).p11 - a*(matrix a d b e k).p12 + k*(matrix a d b e k).p22 + e*(matrix a d b e k).p13 = 0 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11,n12,n13,n22,n23,n33,denominator,coupling,gap]
  ring

@[powerlib_foundation] theorem eq13 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) : -(a+d)*(matrix a d b e k).p13 - k*(matrix a d b e k).p12 + k*(matrix a d b e k).p23 = 0 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11,n12,n13,n22,n23,n33,denominator,coupling,gap]
  ring

@[powerlib_foundation] theorem eq22 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) : -2*b*(matrix a d b e k).p12 + 2*e*(matrix a d b e k).p23 = -1 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11,n12,n13,n22,n23,n33,denominator,coupling,gap]
  ring

@[powerlib_foundation] theorem eq23 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) : -b*(matrix a d b e k).p13 - k*(matrix a d b e k).p22 - d*(matrix a d b e k).p23 + e*(matrix a d b e k).p33 = 0 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11,n12,n13,n22,n23,n33,denominator,coupling,gap]
  ring

@[powerlib_foundation] theorem eq33 (a d b e k : ℝ)
    (hq : denominator a d b e k ≠ 0) : -2*k*(matrix a d b e k).p23 - 2*d*(matrix a d b e k).p33 = -1 := by
  dsimp [matrix]
  field_simp [hq]
  dsimp [n11,n12,n13,n22,n23,n33,denominator,coupling,gap]
  ring

end powerlib.LCL.PassiveWitness

namespace powerlib.LCL

def synthesize (m : Circuit) (hp : m.Passive) (hd : m.Damped) : Accepted m := by
  let a := (toStateSpace m).first.decay
  let d := (toStateSpace m).second.decay
  let b := (toStateSpace m).first.inputGain.val
  let e := (toStateSpace m).second.inputGain.val
  let k := (toStateSpace m).capacitorGain.val
  have ha : 0 ≤ a := by
    dsimp [a,toStateSpace,generated.convertLCL,powerlib.reciprocal]
    exact mul_nonneg hp.1 (inv_pos.mpr m.first.inductance.property).le
  have hd' : 0 ≤ d := by
    dsimp [d,toStateSpace,generated.convertLCL,powerlib.reciprocal]
    exact mul_nonneg hp.2 (inv_pos.mpr m.second.inductance.property).le
  have hb : 0 < b := (toStateSpace m).first.inputGain.property
  have he : 0 < e := (toStateSpace m).second.inputGain.property
  have hk : 0 < k := (toStateSpace m).capacitorGain.property
  have had : 0 < a ∨ 0 < d := by
    rcases hd with hr | hr
    · left
      have hR : 0 < m.first.resistance := lt_of_le_of_ne hp.1 (Ne.symm hr)
      dsimp [a,toStateSpace,generated.convertLCL,powerlib.reciprocal]
      exact mul_pos hR (inv_pos.mpr m.first.inductance.property)
    · right
      have hR : 0 < m.second.resistance := lt_of_le_of_ne hp.2 (Ne.symm hr)
      dsimp [d,toStateSpace,generated.convertLCL,powerlib.reciprocal]
      exact mul_pos hR (inv_pos.mpr m.second.inductance.property)
  have hJ := PassiveWitness.coupling_pos ha hd' hb he had
  have hG := PassiveWitness.gap_pos ha hd' hb he hk had
  have hq : 0 < PassiveWitness.denominator a d b e k := by
    dsimp [PassiveWitness.denominator]
    positivity
  have hn := ne_of_gt hq
  have hc := passive_hurwitz m hp hd
  refine {
    p := PassiveWitness.matrix a d b e k
    p11_pos := ?_
    minor2_pos := ?_
    det_pos := ?_
    a2_pos := hc.1
    a1_pos := hc.2.1
    a0_pos := hc.2.2.1
    gap_pos := hc.2.2.2
    eq11 := PassiveWitness.eq11 a d b e k hn
    eq12 := PassiveWitness.eq12 a d b e k hn
    eq13 := PassiveWitness.eq13 a d b e k hn
    eq22 := PassiveWitness.eq22 a d b e k hn
    eq23 := PassiveWitness.eq23 a d b e k hn
    eq33 := PassiveWitness.eq33 a d b e k hn }
  · exact div_pos (PassiveWitness.n11_pos ha hd' hb he hk had) hq
  · rw [PassiveWitness.minor_identity a d b e k hn]
    exact div_pos (mul_pos (mul_pos hk hJ)
      (PassiveWitness.minorNumerator_pos ha hd' hb he hk had)) (pow_pos hq 2)
  · rw [PassiveWitness.det_identity a d b e k hn]
    exact div_pos (mul_pos (mul_pos (mul_pos (pow_pos hk 2) (pow_pos hJ 2)) hG)
      (PassiveWitness.detNumerator_pos ha hd' hb he hk)) (pow_pos hq 3)

@[powerlib_domain, aesop norm forward (immediate := [hp, hd])]
theorem passive_asymptoticallyStable (m : Circuit) (hp : m.Passive) (hd : m.Damped)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : AsymptoticallyStable m u vg e :=
  (synthesize m hp hd).asymptoticallyStable he

@[powerlib_domain, aesop norm forward (immediate := [hp, hd])]
theorem passive_globallyAsymptoticallyStable
    (m : Circuit) (hp : m.Passive) (hd : m.Damped)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : GloballyAsymptoticallyStable m u vg e :=
  (synthesize m hp hd).globallyAsymptoticallyStable he

@[powerlib_domain, aesop norm forward (immediate := [hp, hd])]
theorem passive_globallyExponentiallyStable
    (m : Circuit) (hp : m.Passive) (hd : m.Damped)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) : GloballyExponentiallyStable m u vg e :=
  (synthesize m hp hd).globallyExponentiallyStable he

@[simp, powerlib_domain] theorem passive_asymptoticallyStable_iff (m : Circuit) (hp : m.Passive)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    AsymptoticallyStable m u vg e ↔ m.Damped :=
  ⟨asymptoticallyStable_requires_damping he,
    fun hd => passive_asymptoticallyStable m hp hd he⟩

@[simp, powerlib_domain] theorem passive_globallyAsymptoticallyStable_iff (m : Circuit) (hp : m.Passive)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    GloballyAsymptoticallyStable m u vg e ↔ m.Damped := by
  constructor
  · intro h
    exact asymptoticallyStable_requires_damping he ⟨h.1, 1, zero_lt_one, fun x hx _ => h.2 x hx⟩
  · exact fun hd => (synthesize m hp hd).globallyAsymptoticallyStable he

@[simp, powerlib_domain] theorem passive_globallyExponentiallyStable_iff (m : Circuit) (hp : m.Passive)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    GloballyExponentiallyStable m u vg e ↔ m.Damped := by
  constructor
  · intro h
    by_contra hd
    simp only [Circuit.Damped, not_or, not_not] at hd
    exact lossless_not_globallyExponentiallyStable hd.1 hd.2 he h
  · exact fun hd => (synthesize m hp hd).globallyExponentiallyStable he

@[powerlib_domain] theorem passive_asymptoticallyStable_iff_poles (m : Circuit) (hp : m.Passive)
    {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    AsymptoticallyStable m u vg e ↔ (toStateSpace m).Stable :=
  (passive_asymptoticallyStable_iff m hp he).trans
    ((stability_agrees m).trans (passive_stable_iff m hp)).symm

@[powerlib_domain] theorem passive_globallyExponentiallyStable_iff_poles
    (m : Circuit) (hp : m.Passive) {u vg : ℝ} {e : State} (he : IsEquilibrium m u vg e) :
    GloballyExponentiallyStable m u vg e ↔ (toStateSpace m).Stable :=
  (passive_globallyExponentiallyStable_iff m hp he).trans
    ((stability_agrees m).trans (passive_stable_iff m hp)).symm

end powerlib.LCL

namespace powerlib
@[simp, powerlib_domain] theorem lcl_asymptotically_stable_iff (m : LCL.Circuit) (hp : m.Passive)
    {u vg : ℝ} {e : LCL.State} (he : LCL.IsEquilibrium m u vg e) :
    LCL.AsymptoticallyStable m u vg e ↔ m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 :=
  LCL.passive_asymptoticallyStable_iff m hp he

@[simp, powerlib_domain] theorem lcl_globally_exponentially_stable_iff (m : LCL.Circuit) (hp : m.Passive)
    {u vg : ℝ} {e : LCL.State} (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyExponentiallyStable m u vg e ↔ m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 :=
  LCL.passive_globallyExponentiallyStable_iff m hp he
end powerlib
