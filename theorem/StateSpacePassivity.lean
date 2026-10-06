import dependencies.Mathlib
import theorem.Passivity

noncomputable section
namespace powerlib.StateSpacePassivity
open Set Matrix
open scoped Topology

abbrev State (ι : Type*) := ι → ℝ

structure Model (ι κ : Type*) where
  A : Matrix ι ι ℝ
  B : Matrix ι κ ℝ
  C : Matrix κ ι ℝ
  D : Matrix κ κ ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def field (m : Model ι κ) (x : State ι) (u : κ → ℝ) : State ι :=
  m.A.mulVec x + m.B.mulVec u

def output (m : Model ι κ) (x : State ι) (u : κ → ℝ) : κ → ℝ :=
  m.C.mulVec x + m.D.mulVec u

def system (m : Model ι κ) : Passivity.System (State ι) κ :=
  ⟨field m, output m⟩

def energy (P : Matrix ι ι ℝ) (x : State ι) : ℝ :=
  dotProduct x (P.mulVec x) / 2

structure Certificate (m : Model ι κ) where
  P : Matrix ι ι ℝ
  positive : P.PosDef
  kyp : ∀ x u, dotProduct (P.mulVec x) (field m x u) ≤
    Passivity.supply (system m) x u

@[simp, powerlib_foundation] theorem zero_equilibrium (m : Model ι κ) :
    Passivity.IsEquilibrium (system m) 0 := by
  simp [Passivity.IsEquilibrium, system, field]

@[simp, powerlib_foundation] theorem energy_zero (P : Matrix ι ι ℝ) : energy P 0 = 0 := by
  simp [energy]

@[powerlib_foundation] theorem energy_continuous (P : Matrix ι ι ℝ) :
    Continuous (energy P) := by
  unfold energy dotProduct Matrix.mulVec
  fun_prop

@[powerlib_foundation] theorem energy_smul (P : Matrix ι ι ℝ) (a : ℝ) (x : State ι) :
    energy P (a • x) = a ^ 2 * energy P x := by
  simp only [energy, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

@[powerlib_foundation, aesop unsafe 75% apply] theorem energy_positive {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (x : State ι) (hx : x ≠ 0) : 0 < energy P x := by
  apply div_pos _ (by norm_num)
  simpa only [star_trivial] using hP.dotProduct_mulVec_pos hx

omit [Fintype ι] in
@[powerlib_foundation] theorem symmetric_of_posDef {P : Matrix ι ι ℝ}
    (hP : P.PosDef) : P.transpose = P := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq

@[powerlib_foundation] theorem dotProduct_derivative
    {x y : ℝ → State ι} {dx dy : State ι} {t : ℝ}
    (hx : HasDerivWithinAt x dx (Ici 0) t)
    (hy : HasDerivWithinAt y dy (Ici 0) t) :
    HasDerivWithinAt (fun τ => dotProduct (x τ) (y τ))
      (dotProduct dx (y t) + dotProduct (x t) dy) (Ici 0) t := by
  have hd (i : ι) :=
    ((ContinuousLinearMap.proj i : State ι →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hx).mul
      ((ContinuousLinearMap.proj i : State ι →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hy)
  simpa [dotProduct, Finset.sum_add_distrib, Pi.mul_apply, Function.comp_def] using!
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hd i)

@[powerlib_foundation] theorem energy_derivative (P : Matrix ι ι ℝ)
    (hP : P.transpose = P) {x : ℝ → State ι} {dx : State ι} {t : ℝ}
    (hx : HasDerivWithinAt x dx (Ici 0) t) :
    HasDerivWithinAt (fun τ => energy P (x τ))
      (dotProduct (P.mulVec (x t)) dx) (Ici 0) t := by
  have hPx : HasDerivWithinAt (fun τ => P.mulVec (x τ)) (P.mulVec dx) (Ici 0) t :=
    (P.mulVecLin.toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt t hx
  have hsym : dotProduct (x t) (P.mulVec dx) = dotProduct (P.mulVec (x t)) dx := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hP]
  convert! (dotProduct_derivative hx hPx).div_const 2 using 1
  rw [hsym, dotProduct_comm dx (P.mulVec (x t))]
  ring

def Certificate.storage {m : Model ι κ} (c : Certificate m) :
    Passivity.QuadraticStorage (system m) where
  energy := energy c.P
  rate := fun x u => dotProduct (c.P.mulVec x) (field m x u)
  energyDerivative := by
    intro u x hx t ht
    exact energy_derivative c.P (symmetric_of_posDef c.positive) (hx t ht)
  dissipation := c.kyp
  continuous := energy_continuous c.P
  homogeneous := energy_smul c.P
  positive := energy_positive c.positive

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Certificate.passiveWithStorage
    {m : Model ι κ} (c : Certificate m) :
    Passivity.PassiveWithStorage (system m) (energy c.P) :=
  c.storage.passiveWithStorage

@[powerlib_domain, aesop norm forward (immediate := [c, hx, ht, hpower])] theorem Certificate.integral_passivity
    {m : Model ι κ} (c : Certificate m) {u : ℝ → (κ → ℝ)} {x : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) u x) {t : ℝ} (ht : 0 ≤ t)
    (hpower : IntervalIntegrable (fun τ => Passivity.supply (system m) (x τ) (u τ))
      MeasureTheory.volume 0 t) :
    energy c.P (x t) - energy c.P (x 0) ≤
      ∫ τ in (0 : ℝ)..t, Passivity.supply (system m) (x τ) (u τ) :=
  c.storage.integral_passivity hx ht hpower

@[powerlib_domain] theorem Certificate.zeroInput_energy_antitone
    {m : Model ι κ} (c : Certificate m) {x : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x) :
    AntitoneOn (fun t => energy c.P (x t)) (Ici 0) :=
  c.storage.toDissipativeStorage.zeroInput_energy_antitone hx

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem Certificate.lyapunovStable [Nonempty ι]
    {m : Model ι κ} (c : Certificate m) : Passivity.LyapunovStable (system m) :=
  c.storage.lyapunovStable (zero_equilibrium m)

structure CollocatedCertificate (m : Model ι κ) where
  P : Matrix ι ι ℝ
  positive : P.PosDef
  dissipation : (-(P * m.A + m.A.transpose * P)).PosSemidef
  collocated : P * m.B = m.C.transpose
  feedthrough : m.D.PosSemidef

@[powerlib_foundation] theorem dotProduct_symmetric (P : Matrix ι ι ℝ)
    (hP : P.transpose = P) (x y : State ι) :
    dotProduct x (P.mulVec y) = dotProduct (P.mulVec x) y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hP]

@[powerlib_foundation] theorem state_dissipation_form (P : Matrix ι ι ℝ)
    (hP : P.transpose = P) (A : Matrix ι ι ℝ) (x : State ι) :
    dotProduct x ((P * A + A.transpose * P).mulVec x) =
      2 * dotProduct (P.mulVec x) (A.mulVec x) := by
  have hA : dotProduct x (A.transpose.mulVec (P.mulVec x)) =
      dotProduct (P.mulVec x) (A.mulVec x) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, dotProduct_comm]
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_symmetric P hP, hA]
  ring

omit [Fintype κ] in
@[powerlib_foundation] theorem CollocatedCertificate.state_rate_nonpos
    {m : Model ι κ} (c : CollocatedCertificate m) (x : State ι) :
    dotProduct (c.P.mulVec x) (m.A.mulVec x) ≤ 0 := by
  have h : 0 ≤ dotProduct x ((-(c.P * m.A + m.A.transpose * c.P)).mulVec x) := by
    simpa only [star_trivial] using c.dissipation.dotProduct_mulVec_nonneg x
  rw [neg_mulVec, dotProduct_neg,
    state_dissipation_form c.P (symmetric_of_posDef c.positive)] at h
  linarith

@[powerlib_foundation] theorem CollocatedCertificate.port_power
    {m : Model ι κ} (c : CollocatedCertificate m) (x : State ι) (u : κ → ℝ) :
    dotProduct (c.P.mulVec x) (m.B.mulVec u) = dotProduct u (m.C.mulVec x) := by
  rw [← dotProduct_symmetric c.P (symmetric_of_posDef c.positive),
    mulVec_mulVec, c.collocated, dotProduct_mulVec, ← mulVec_transpose,
    transpose_transpose, dotProduct_comm]

def CollocatedCertificate.toCertificate {m : Model ι κ} (c : CollocatedCertificate m) :
    Certificate m where
  P := c.P
  positive := c.positive
  kyp := by
    intro x u
    have hD : 0 ≤ dotProduct u (m.D.mulVec u) := by
      simpa only [star_trivial] using c.feedthrough.dotProduct_mulVec_nonneg u
    have hA := c.state_rate_nonpos x
    change dotProduct (c.P.mulVec x) (m.A.mulVec x + m.B.mulVec u) ≤
      dotProduct u (m.C.mulVec x + m.D.mulVec u)
    rw [dotProduct_add, c.port_power, dotProduct_add]
    linarith

def kypMatrix (m : Model ι κ) (P : Matrix ι ι ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks (-(P * m.A + m.A.transpose * P)) (m.C.transpose - P * m.B)
    (m.C - m.B.transpose * P) (m.D + m.D.transpose)

omit [Fintype κ] in
@[powerlib_foundation] theorem kypMatrix_isHermitian (m : Model ι κ)
    (P : Matrix ι ι ℝ) (hP : P.transpose = P) : (kypMatrix m P).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · have h := (isHermitian_add_transpose_self (P * m.A)).neg
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_mul, hP] using h
  · simp only [conjTranspose_eq_transpose_of_trivial, transpose_sub,
      transpose_transpose, transpose_mul, hP]
  · simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_add_transpose_self m.D

@[powerlib_foundation] theorem kypMatrix_quadraticForm (m : Model ι κ)
    (P : Matrix ι ι ℝ) (hP : P.transpose = P) (x : State ι) (u : κ → ℝ) :
    dotProduct (Sum.elim x u) ((kypMatrix m P).mulVec (Sum.elim x u)) =
      2 * (Passivity.supply (system m) x u -
        dotProduct (P.mulVec x) (field m x u)) := by
  have hC : dotProduct x (m.C.transpose.mulVec u) = dotProduct u (m.C.mulVec x) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, dotProduct_comm]
  have hPB : dotProduct x ((P * m.B).mulVec u) =
      dotProduct (P.mulVec x) (m.B.mulVec u) := by
    rw [← mulVec_mulVec, dotProduct_symmetric P hP]
  have hBP : dotProduct u ((m.B.transpose * P).mulVec x) =
      dotProduct (P.mulVec x) (m.B.mulVec u) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      transpose_transpose, dotProduct_comm]
  have hD : dotProduct u (m.D.transpose.mulVec u) = dotProduct u (m.D.mulVec u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, dotProduct_comm]
  have hPA : dotProduct x ((P * m.A).mulVec x) =
      dotProduct (P.mulVec x) (m.A.mulVec x) := by
    rw [← mulVec_mulVec, dotProduct_symmetric P hP]
  have hAP : dotProduct x ((m.A.transpose * P).mulVec x) =
      dotProduct (P.mulVec x) (m.A.mulVec x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      transpose_transpose, dotProduct_comm]
  simp only [kypMatrix, fromBlocks_mulVec, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr, sumElim_dotProduct_sumElim, dotProduct_add, neg_mulVec,
    dotProduct_neg, sub_mulVec, dotProduct_sub, add_mulVec,
    hPA, hAP, hC, hPB, hBP, hD]
  change _ = 2 * (dotProduct u (m.C.mulVec x + m.D.mulVec u) -
    dotProduct (P.mulVec x) (m.A.mulVec x + m.B.mulVec u))
  rw [dotProduct_add, dotProduct_add]
  ring

@[powerlib_foundation] theorem kypMatrix_posSemidef_iff (m : Model ι κ)
    (P : Matrix ι ι ℝ) (hP : P.transpose = P) :
    (kypMatrix m P).PosSemidef ↔ ∀ x u,
      dotProduct (P.mulVec x) (field m x u) ≤ Passivity.supply (system m) x u := by
  constructor
  · intro h x u
    have hq : 0 ≤ dotProduct (Sum.elim x u) ((kypMatrix m P).mulVec (Sum.elim x u)) := by
      simpa only [star_trivial] using h.dotProduct_mulVec_nonneg (Sum.elim x u)
    rw [kypMatrix_quadraticForm m P hP] at hq
    linarith
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (kypMatrix_isHermitian m P hP)
    intro z
    have hz : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z := by
      ext i
      cases i <;> rfl
    have hq := kypMatrix_quadraticForm m P hP (z ∘ Sum.inl) (z ∘ Sum.inr)
    rw [hz] at hq
    simp only [star_trivial]
    rw [hq]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (h _ _))

structure MatrixCertificate (m : Model ι κ) where
  P : Matrix ι ι ℝ
  positive : P.PosDef
  kyp_nonneg : (kypMatrix m P).PosSemidef

def MatrixCertificate.toCertificate {m : Model ι κ} (c : MatrixCertificate m) :
    Certificate m where
  P := c.P
  positive := c.positive
  kyp := (kypMatrix_posSemidef_iff m c.P (symmetric_of_posDef c.positive)).mp c.kyp_nonneg

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem MatrixCertificate.passiveWithStorage
    {m : Model ι κ} (c : MatrixCertificate m) :
    Passivity.PassiveWithStorage (system m) (energy c.P) :=
  c.toCertificate.passiveWithStorage

@[powerlib_domain, aesop norm forward (immediate := [c])] theorem MatrixCertificate.lyapunovStable [Nonempty ι]
    {m : Model ι κ} (c : MatrixCertificate m) : Passivity.LyapunovStable (system m) :=
  c.toCertificate.lyapunovStable

end powerlib.StateSpacePassivity
