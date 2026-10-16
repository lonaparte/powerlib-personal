import theorem.PH.Linear
import theorem.Criteria.Hurwitz2

/-! # Spectrum and positive realness of linear port-Hamiltonian systems

Static foundation: the spectrum of a linear pH system lies in the closed left half plane, and its
collocated port admittance (and impedance) is positive real.

Model boundary.
* The constant-coefficient pH system of `theorem/PH/Linear.lean`, `ẋ = (J − R) Q x + g u`,
  `y = gᵀ Q x`, as the linear plant `linearLTIModel J R g Q` (`A = (J − R) Q`, `B = g`,
  `C = gᵀ Q`, `D = 0`; a `Linear.Plant`), with `J` skew, `R ⪰ 0`, `Q ≻ 0`, all real.
* Transfer matrix `G(s) = C (sI − A)⁻¹ B` (`Linear.transfer`), the collocated port admittance
  (effort in, flow out) of T-ph (1.16).
* Excluded: strict positive realness (`R ≻ 0`, note §1.10 last paragraph), behaviour on the
  imaginary axis, Nyquist arguments, nonlinear pH systems.

Source: work-sync `theory/T-ph.md` §1.10 ((1.15), (1.16), "正实 … 导纳正实 ⇔ 阻抗也正实").

Results.
* Spectrum (T-ph §1.10): every complex eigenvalue of `A_ph = (J − R) Q` has `Re λ ≤ 0`
  (`phSpectral_re_nonpos`, from the Lyapunov identity `Aᵀ Q + Q A = −2 Q R Q`,
  `linearStateMatrix_lyapunov` of `theorem/PH/Linear.lean`, read at an eigenvector by
  `Criteria.re_nonpos_of_lyapunov`), hence `sI − A` is invertible for `Re s > 0`
  (`phSpectral_det_ne_zero`, `Criteria.det_characteristicMatrix_ne_zero_of_re_lt`).
* Positive realness: `IsPositiveReal m` means: no pole and `Re uᴴ (G(s) + G(s)ᴴ) u ≥ 0` for
  every `s` with `Re s > 0` and every complex `u`. For the linear pH system the key identity is
  `Re uᴴ G(s) u = Re(s) xᴴ Q x + xᴴ Q R Q x` with `x = (sI − A)⁻¹ g u`
  (`linearLTIModel_transfer_re`), so `uᴴ (G + Gᴴ) u = 2 Re(s) xᴴ Q x + 2 xᴴ Q R Q x ≥ 0`:
  `R ⪰ 0 ⇒ G` positive real (`linearLTIModel_isPositiveReal`).
* Admittance / impedance: at a fixed `s`, an invertible `G` is positive real iff `G⁻¹` is
  (`positiveRealAt_inv_iff`). Hence the port impedance `Z(s) = G(s)⁻¹` is positive real
  wherever `G(s)` is invertible (`linearLTIModel_impedance_positiveRealAt`).

Family and connection conclusions.
* None: every result here is static (spectral bounds, transfer matrix identities, positive
  realness at frequencies), all public foundation; `IsPositiveReal` is stated for a
  `Linear.Plant`.
-/

noncomputable section
namespace powerlib.PH
open Matrix
open powerlib.Dynamics (State)

variable {n m : ℕ}

/-! ## Complex quadratic forms of real matrices -/

/-- For real `M` and complex `x`: `xᴴ Mᵀ x = conj (xᴴ M x)`. -/
@[powerlib_foundation] theorem phCx_transpose_form (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℂ) :
    star x ⬝ᵥ (Linear.complexify Mᵀ *ᵥ x) = star (star x ⬝ᵥ (Linear.complexify M *ᵥ x)) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, star_sum, star_mul', Pi.star_apply, star_star,
    map_apply, transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.coe_algebraMap, Complex.star_def, Complex.conj_ofReal]
  ring

/-- Real part of a complex quadratic form of a real matrix:
`Re vᴴ P v = aᵀ P a + bᵀ P b` with `v = a + i b`. -/
@[powerlib_foundation] theorem phCx_form_re (P : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (Linear.complexify P *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (P *ᵥ fun i => (v i).re) +
        (fun i => (v i).im) ⬝ᵥ (P *ᵥ fun i => (v i).im) := by
  simp only [dotProduct, mulVec, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    Pi.star_apply, map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.coe_algebraMap, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

@[powerlib_foundation] theorem phCx_form_re_nonneg {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) (v : Fin n → ℂ) : 0 ≤ (star v ⬝ᵥ (Linear.complexify P *ᵥ v)).re := by
  rw [phCx_form_re]
  have h1 := hP.dotProduct_mulVec_nonneg (fun i => (v i).re)
  have h2 := hP.dotProduct_mulVec_nonneg (fun i => (v i).im)
  rw [star_trivial] at h1 h2
  linarith

@[powerlib_foundation] theorem phCx_form_re_pos {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosDef) {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < (star v ⬝ᵥ (Linear.complexify P *ᵥ v)).re := by
  rw [phCx_form_re]
  have h1 := hP.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
  have h2 := hP.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
  rw [star_trivial] at h1 h2
  by_cases ha : (fun i => (v i).re) = 0
  · have hb : (fun i => (v i).im) ≠ 0 := by
      intro hb
      apply hv
      funext i
      apply Complex.ext
      · simpa using congrFun ha i
      · simpa using congrFun hb i
    have := hP.dotProduct_mulVec_pos hb
    rw [star_trivial] at this
    linarith
  · have := hP.dotProduct_mulVec_pos ha
    rw [star_trivial] at this
    linarith

/-- `uᴴ Gᴴ u = conj (uᴴ G u)` for complex `G`. -/
@[powerlib_foundation] theorem phCx_conjTranspose_form {κ : Type*} [Fintype κ]
    (G : Matrix κ κ ℂ) (u : κ → ℂ) :
    star u ⬝ᵥ (Gᴴ *ᵥ u) = star (star u ⬝ᵥ (G *ᵥ u)) := by
  simp only [dotProduct, mulVec, star_sum, star_mul', conjTranspose_apply, Pi.star_apply,
    star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[powerlib_foundation] theorem phCx_complexify_add (M N : Matrix (Fin n) (Fin m) ℝ) :
    Linear.complexify (M + N) = Linear.complexify M + Linear.complexify N := by
  ext i j
  simp

@[powerlib_foundation] theorem phCx_complexify_conjTranspose (M : Matrix (Fin n) (Fin m) ℝ) :
    (Linear.complexify M)ᴴ = Linear.complexify Mᵀ := by
  ext i j
  simp [conjTranspose_apply, Complex.coe_algebraMap, Complex.conj_ofReal]

/-! ## Spectrum of `A_ph = (J − R) Q` -/

section Spectrum

variable {J R Q : Matrix (Fin n) (Fin n) ℝ}

/-- T-ph §1.10: every complex eigenvalue of `(J − R) Q` (`J` skew, `R ⪰ 0`, `Q ≻ 0`) has
nonpositive real part. -/
@[powerlib_foundation] theorem phSpectral_re_nonpos (hJ : Jᵀ = -J) (hR : R.PosSemidef)
    (hQ : Q.PosDef) {μ : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0)
    (heig : Linear.complexify (linearStateMatrix J R Q) *ᵥ v = μ • v) : μ.re ≤ 0 := by
  have hQt : Qᵀ = Q := symmetric_of_posDef hQ
  refine Criteria.re_nonpos_of_lyapunov hQt (fun w hw => by
    simpa only [star_trivial] using hQ.dotProduct_mulVec_pos hw) (fun w => ?_) hv heig
  have h := (linearStateMatrix_lyapunov_negSemidef hJ hR hQt).dotProduct_mulVec_nonneg w
  rw [star_trivial, neg_mulVec, dotProduct_neg, Linear.quadratic_sym hQt] at h
  linarith

/-- No pole of the linear pH system in the open right half-plane. -/
@[powerlib_foundation] theorem phSpectral_det_ne_zero (hJ : Jᵀ = -J) (hR : R.PosSemidef)
    (hQ : Q.PosDef) {s : ℂ} (hs : 0 < s.re) :
    (Linear.characteristicMatrix (linearStateMatrix J R Q) s).det ≠ 0 :=
  Criteria.det_characteristicMatrix_ne_zero_of_re_lt _ fun _ _ hv heig =>
    (phSpectral_re_nonpos hJ hR hQ hv heig).trans_lt hs

end Spectrum

/-! ## Positive realness -/

/-- Positive realness of a complex matrix at one frequency: `Re uᴴ (G + Gᴴ) u ≥ 0`. -/
def PositiveRealAt {κ : Type*} [Fintype κ] (G : Matrix κ κ ℂ) : Prop :=
  ∀ u : κ → ℂ, 0 ≤ (star u ⬝ᵥ ((G + Gᴴ) *ᵥ u)).re

/-- Positive realness of the transfer matrix of a linear plant on the open right half-plane,
including the absence of poles there. -/
def IsPositiveReal {p : ℕ} (sys : Linear.Plant n p) : Prop :=
  ∀ s : ℂ, 0 < s.re →
    (Linear.characteristicMatrix sys.A s).det ≠ 0 ∧ PositiveRealAt (Linear.transfer sys s)

/-- `Re uᴴ (G + Gᴴ) u = 2 Re uᴴ G u`. -/
@[powerlib_foundation] theorem positiveRealAt_iff_re {κ : Type*} [Fintype κ]
    (G : Matrix κ κ ℂ) : PositiveRealAt G ↔ ∀ u : κ → ℂ, 0 ≤ (star u ⬝ᵥ (G *ᵥ u)).re := by
  have h : ∀ u : κ → ℂ, (star u ⬝ᵥ ((G + Gᴴ) *ᵥ u)).re = 2 * (star u ⬝ᵥ (G *ᵥ u)).re := by
    intro u
    rw [add_mulVec, dotProduct_add, phCx_conjTranspose_form, Complex.add_re, Complex.star_def,
      Complex.conj_re]
    ring
  simp only [PositiveRealAt, h]
  constructor
  · intro H u; linarith [H u]
  · intro H u; linarith [H u]

section PR

variable {J R Q : Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin n) (Fin m) ℝ}

/-- The key identity: with `x = (sI − A)⁻¹ g u`,
`Re uᴴ G(s) u = Re(s) · Re(xᴴ Q x) + Re(xᴴ Q R Q x)`. -/
@[powerlib_foundation] theorem linearLTIModel_transfer_re (hJ : Jᵀ = -J) (hRt : Rᵀ = R)
    (hQt : Qᵀ = Q) (s : ℂ) (hdet : (Linear.characteristicMatrix (linearStateMatrix J R Q) s).det ≠ 0)
    (u : Fin m → ℂ) :
    (star u ⬝ᵥ (Linear.transfer (linearLTIModel J R g Q) s *ᵥ u)).re =
      s.re * (star ((Linear.characteristicMatrix (linearStateMatrix J R Q) s)⁻¹ *ᵥ
          (Linear.complexify g *ᵥ u)) ⬝ᵥ (Linear.complexify Q *ᵥ
          ((Linear.characteristicMatrix (linearStateMatrix J R Q) s)⁻¹ *ᵥ
            (Linear.complexify g *ᵥ u)))).re +
        (star ((Linear.characteristicMatrix (linearStateMatrix J R Q) s)⁻¹ *ᵥ
          (Linear.complexify g *ᵥ u)) ⬝ᵥ (Linear.complexify (Q * R * Q) *ᵥ
          ((Linear.characteristicMatrix (linearStateMatrix J R Q) s)⁻¹ *ᵥ
            (Linear.complexify g *ᵥ u)))).re := by
  set A := linearStateMatrix J R Q
  set C := Linear.characteristicMatrix A s
  set x := C⁻¹ *ᵥ (Linear.complexify g *ᵥ u)
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hCx : C *ᵥ x = Linear.complexify g *ᵥ u := by
    simp only [x]
    rw [mulVec_mulVec, mul_nonsing_inv _ hC, one_mulVec]
  have hCdef : C = s • (1 : Matrix (Fin n) (Fin n) ℂ) - Linear.complexify A := rfl
  have hGu : Linear.transfer (linearLTIModel J R g Q) s *ᵥ u =
      Linear.complexify (gᵀ * Q) *ᵥ x := by
    simp only [Linear.transfer, linearLTIModel, Linear.complexify_zero, add_zero, x, C, A,
      mulVec_mulVec, Matrix.mul_assoc]
  -- `uᴴ G u = (g u)ᴴ Q x = (C x)ᴴ Q x = conj s · xᴴ Q x − (A x)ᴴ Q x`.
  have ha : star u ⬝ᵥ (Linear.complexify (gᵀ * Q) *ᵥ x) =
      star (Linear.complexify g *ᵥ u) ⬝ᵥ (Linear.complexify Q *ᵥ x) := by
    rw [Linear.complexify_mul, ← mulVec_mulVec, ← phCx_complexify_conjTranspose, dotProduct_mulVec,
      ← star_mulVec]
  have hb : Linear.complexify g *ᵥ u = s • x - Linear.complexify A *ᵥ x := by
    rw [← hCx, hCdef, sub_mulVec, smul_mulVec, one_mulVec]
  have hc : star (Linear.complexify A *ᵥ x) ⬝ᵥ (Linear.complexify Q *ᵥ x) =
      star x ⬝ᵥ (Linear.complexify (Aᵀ * Q) *ᵥ x) := by
    rw [star_mulVec, ← dotProduct_mulVec, phCx_complexify_conjTranspose, mulVec_mulVec,
      ← Linear.complexify_mul]
  have hstep : star u ⬝ᵥ (Linear.transfer (linearLTIModel J R g Q) s *ᵥ u) =
      star s * (star x ⬝ᵥ (Linear.complexify Q *ᵥ x)) -
        star x ⬝ᵥ (Linear.complexify (Aᵀ * Q) *ᵥ x) := by
    rw [hGu, ha, hb, star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul, hc]
  -- `Re xᴴ Aᵀ Q x = ½ Re xᴴ (Aᵀ Q + Q A) x = −Re xᴴ Q R Q x`.
  have hsym : (star x ⬝ᵥ (Linear.complexify (Q * A) *ᵥ x)).re =
      (star x ⬝ᵥ (Linear.complexify (Aᵀ * Q) *ᵥ x)).re := by
    have h := phCx_transpose_form (Q * A) x
    rw [transpose_mul, hQt] at h
    rw [h, Complex.star_def, Complex.conj_re]
  have hly : Aᵀ * Q + Q * A = -(2 : ℝ) • (Q * R * Q) := linearStateMatrix_lyapunov hJ hQt hRt
  have hsum : (star x ⬝ᵥ (Linear.complexify (Aᵀ * Q) *ᵥ x)).re +
      (star x ⬝ᵥ (Linear.complexify (Q * A) *ᵥ x)).re =
        -2 * (star x ⬝ᵥ (Linear.complexify (Q * R * Q) *ᵥ x)).re := by
    rw [← Complex.add_re, ← dotProduct_add, ← add_mulVec, ← phCx_complexify_add, hly,
      phCx_form_re, phCx_form_re]
    simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
    ring
  have hSim : (star x ⬝ᵥ (Linear.complexify Q *ᵥ x)).im = 0 := by
    have h := phCx_transpose_form Q x
    rw [hQt] at h
    have := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [hstep, Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    hSim]
  linarith

/-- T-ph §1.10: the port admittance `G(s) = gᵀ Q (sI − (J − R) Q)⁻¹ g` of a linear pH system
with `R ⪰ 0`, `Q ≻ 0` is positive real (no right-half-plane pole and
`Re uᴴ (G + Gᴴ) u = 2 Re(s) xᴴQx + 2 xᴴQRQx ≥ 0`). -/
@[powerlib_foundation] theorem linearLTIModel_isPositiveReal (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) : IsPositiveReal (linearLTIModel J R g Q) := by
  intro s hs
  have hdet := phSpectral_det_ne_zero hJ hR hQ hs
  refine ⟨hdet, (positiveRealAt_iff_re _).mpr fun u => ?_⟩
  have hQt : Qᵀ = Q := symmetric_of_posDef hQ
  have hRt : Rᵀ = R := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  rw [linearLTIModel_transfer_re hJ hRt hQt s hdet u]
  have hQRQ : (Q * R * Q).PosSemidef := by
    have h := hR.conjTranspose_mul_mul_same Q
    rwa [conjTranspose_eq_transpose_of_trivial, hQt] at h
  have h1 := phCx_form_re_nonneg hQ.posSemidef
    ((Linear.characteristicMatrix (linearStateMatrix J R Q) s)⁻¹ *ᵥ (Linear.complexify g *ᵥ u))
  have h2 := phCx_form_re_nonneg hQRQ
    ((Linear.characteristicMatrix (linearStateMatrix J R Q) s)⁻¹ *ᵥ (Linear.complexify g *ᵥ u))
  have := mul_nonneg hs.le h1
  linarith

end PR

/-! ## Admittance versus impedance -/

/-- For invertible `G`: `wᴴ Gᴴ (G⁻¹ + G⁻ᴴ) G w = wᴴ (G + Gᴴ) w`. -/
@[powerlib_foundation] theorem positiveRealAt_inv_form {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : Matrix κ κ ℂ} (hG : IsUnit G.det) (w : κ → ℂ) :
    star (G *ᵥ w) ⬝ᵥ ((G⁻¹ + G⁻¹ᴴ) *ᵥ (G *ᵥ w)) = star w ⬝ᵥ ((G + Gᴴ) *ᵥ w) := by
  have h1 : G⁻¹ *ᵥ (G *ᵥ w) = w := by rw [mulVec_mulVec, nonsing_inv_mul _ hG, one_mulVec]
  have h2 : Gᴴ *ᵥ (G⁻¹ᴴ *ᵥ (G *ᵥ w)) = G *ᵥ w := by
    rw [mulVec_mulVec, mulVec_mulVec, ← conjTranspose_mul, nonsing_inv_mul _ hG,
      conjTranspose_one, one_mul]
  rw [add_mulVec, dotProduct_add, h1, star_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, h2,
    add_mulVec, dotProduct_add, add_comm]

/-- At a fixed frequency, an invertible matrix is positive real iff its inverse is
(admittance PR ⇔ impedance PR). -/
@[powerlib_foundation] theorem positiveRealAt_inv_iff {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : Matrix κ κ ℂ} (hG : IsUnit G.det) : PositiveRealAt G⁻¹ ↔ PositiveRealAt G := by
  constructor
  · intro h w
    have := h (G *ᵥ w)
    rwa [positiveRealAt_inv_form hG] at this
  · intro h u
    have hu : u = G *ᵥ (G⁻¹ *ᵥ u) := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec]
    rw [hu, positiveRealAt_inv_form hG]
    exact h _

/-- The port impedance `Z(s) = G(s)⁻¹` of a linear pH system with `R ⪰ 0`, `Q ≻ 0` is positive
real at every right-half-plane point where `G(s)` is invertible. -/
@[powerlib_foundation] theorem linearLTIModel_impedance_positiveRealAt
    {J R Q : Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin n) (Fin m) ℝ}
    (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Q.PosDef) {s : ℂ} (hs : 0 < s.re)
    (hG : IsUnit (Linear.transfer (linearLTIModel J R g Q) s).det) :
    PositiveRealAt (Linear.transfer (linearLTIModel J R g Q) s)⁻¹ :=
  (positiveRealAt_inv_iff hG).mpr ((linearLTIModel_isPositiveReal hJ hR hQ) s hs).2

end powerlib.PH
