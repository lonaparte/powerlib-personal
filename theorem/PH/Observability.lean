import theorem.PH.PositiveReal
import theorem.Criteria.Hurwitz2
import theorem.Modal.Poles

/-! # Passivity, zero-state observability and asymptotic stability of linear pH systems

Refutes the literal claim "passive and zero-state observable ⇒ asymptotically stable" on a lossless
LC loop, and proves the corrected statement: damping injection on an observable linear pH system
is exponentially stable.

Model boundary.
* The constant-coefficient pH system of `theorem/PH/Linear.lean` as the linear plant
  `linearLTIModel J R g Q` (a `Linear.Plant`): `ẋ = (J − R) Q x + g u`, `y = gᵀ Q x`,
  `H = ½ xᵀ Q x`, with `J` skew, `R ⪰ 0`, `Q ≻ 0`, real, continuous time.
* For a linear system zero-state observability is observability of the pair
  `(A, C) = ((J − R) Q, gᵀ Q)` (`LinearSystems.IsObservable`).
* The counterexample is the lossless series `LC` loop `losslessLC`
  (`J = [[0, −1], [1, 0]]`, `R = 0`, `g = (1, 0)ᵀ`, `Q = I`, output the loop current) — the
  `r = 0`, `L = C = 1` case of the series RLC loop `seriesRLCPH` of
  `theorem/PH/Models/RLC.lean`.
* The corrected statement uses the output feedback `u = −k y` (`k > 0`), closed loop
  `phOutputFeedback` with dissipation `R + k g gᵀ`.

Source: work-sync `theory/T-ph.md` Part 2, "Passivity 不等于稳定": "(1.4) 给的是 input-output
passivity … 需配合 zero-state observability + detectability（Khalil 2002 §6）才推出渐近稳定".

Results.
* The lossless loop is passive (`losslessLC_mem_den_passive`) and observable
  (`losslessLC_observable`), but `x(t) = (cos t, sin t)` is an unforced trajectory that keeps
  its energy (`losslessLC_trajectory`, `losslessLC_not_tendsto`), and its state matrix is not
  Hurwitz (`losslessLC_not_isHurwitz`).
* Corrected statement (`phOutputFeedback_isHurwitz`,
  `phOutputFeedback_mem_den_globallyExponentiallyStable`): with damping injection `u = −k y`
  (`k > 0`; the closed loop is the pH system with dissipation `R + k g gᵀ`, i.e. output strictly
  passive, `Ḣ ≤ −k |y|²`) and `(A, C)` observable, the closed loop is Hurwitz, hence
  exponentially stable. The proof is spectral (an eigenvector on the imaginary axis would have
  `C v = 0` and be an eigenvector of `A`, contradicting observability,
  `phCx_eq_zero_of_isObservable`, from `Modal.eq_zero_of_isObservable`); for linear systems this
  replaces the LaSalle argument.
* `phCx_mulVec_re`, `phCx_mulVec_im`: the instances of `Modal.complexify_mulVec_re`/`_im`.
* Nonlinear LaSalle version: for an arbitrary passive system `ẋ = F(x, u)`, `y = H(x)` with a
  `C¹` positive definite storage, zero-state detectability (or observability) and an output
  feedback `u = −ψ(y)` with `⟪ψ(y), y⟫ > 0` give local / global asymptotic stability of the
  closed loop (Khalil, *Nonlinear Systems*, 3rd ed., Lemma 6.7); these generic results are in
  `theorem/Dynamics/LaSalle/Passivity.lean`. Together with the counterexample above, this is the
  corrected nonlinear reading of the note: passivity and zero-state observability/detectability
  give asymptotic stability once the output is fed back (or, equivalently, the system is output
  strictly passive), not for the unforced passive system.

Family and connection conclusions.
* No new family: the lossless loop and the damped closed loop are linear port-Hamiltonian
  plants (`losslessLC`, `phOutputFeedback`, via `toPortHamiltonian`), read through
  `Port.PortHamiltonian.family` (sentences at the origin, the unforced state).
* Connection conclusions: the loop is passive (`losslessLC_mem_den_passive`) and conservative
  (`losslessLC_mem_den_conservative`) but not locally asymptotically stable
  (`losslessLC_not_mem_den_locallyAsymptoticallyStable`); the literal claim "passive and
  observable ⇒ asymptotically stable" is refuted on the semantics connection
  (`passive_observable_not_asymptotic`); and damping injection on an observable pH plant is
  globally exponentially stable (`phOutputFeedback_mem_den_globallyExponentiallyStable`).
* Observability, Hurwitz and spectral facts are static evidence; the explicit unforced solution
  `(cos t, sin t)` is private implementation evidence (`losslessLC_trajectory`).

Correction (refutation of the literal claim).
* Passivity together with zero-state observability does **not** give asymptotic stability of
  the unforced system (the lossless loop above); Khalil's results need output strict passivity
  or an output feedback `u = −φ(y)`.
-/

noncomputable section
namespace powerlib.PH
open Matrix
open Set Filter Topology
open scoped Pointwise

variable {n m : ℕ}

/-! ## Helpers: real and imaginary parts of real matrices acting on complex vectors -/

@[powerlib_foundation] theorem phCx_mulVec_re {p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ)
    (v : Fin n → ℂ) (i : Fin p) :
    ((Linear.complexify M *ᵥ v) i).re = (M *ᵥ fun j => (v j).re) i :=
  Modal.complexify_mulVec_re M v i

@[powerlib_foundation] theorem phCx_mulVec_im {p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ)
    (v : Fin n → ℂ) (i : Fin p) :
    ((Linear.complexify M *ᵥ v) i).im = (M *ᵥ fun j => (v j).im) i :=
  Modal.complexify_mulVec_im M v i

/-- A complex eigenvector of a real `A` lying in `ker C` contradicts observability of `(A, C)`:
`C Aᵏ v = μᵏ C v = 0` for every `k` (`Linear.mulVec_pow_of_eigen`,
`Modal.eq_zero_of_isObservable`). -/
@[powerlib_foundation] theorem phCx_eq_zero_of_isObservable {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin p) (Fin n) ℝ} (hobs : LinearSystems.IsObservable A C) {μ : ℂ}
    {v : Fin n → ℂ} (heig : Linear.complexify A *ᵥ v = μ • v) (hC : Linear.complexify C *ᵥ v = 0) :
    v = 0 :=
  Modal.eq_zero_of_isObservable hobs fun k => by
    rw [← mulVec_mulVec, Linear.mulVec_pow_of_eigen heig, mulVec_smul, hC, smul_zero]

/-! ## Counterexample: the lossless `LC` loop -/

/-- Interconnection of the lossless `LC` loop, state `(φ, q)` with `L = C = 1`. -/
def losslessJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Input matrix: the source drives the inductor; the output is the loop current. -/
def losslessG : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

@[powerlib_foundation] theorem losslessJ_skew : losslessJᵀ = -losslessJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [losslessJ]

@[powerlib_foundation] theorem losslessLC_stateMatrix :
    linearStateMatrix losslessJ 0 1 = !![0, -1; 1, 0] := by
  simp [linearStateMatrix, losslessJ]

/-- The lossless `LC` loop as a linear port-Hamiltonian plant: `J = losslessJ`, `R = 0`,
`g = losslessG`, `Q = 1`. These are the data of the series RLC loop `PH.Models.seriesRLCPH`
(`theorem/PH/Models/RLC.lean`) with `r = 0`, `L = C = 1`. -/
def losslessLC : Port.PortHamiltonian 2 1 :=
  toPortHamiltonian losslessJ 0 losslessG 1 losslessJ_skew PosSemidef.zero PosDef.one

@[powerlib_foundation] theorem losslessLC_plant :
    losslessLC.plant = linearLTIModel losslessJ 0 losslessG 1 := rfl

/-- The lossless loop is passive (storage `H = ½ |x|²`). -/
@[powerlib_domain] theorem losslessLC_mem_den_passive :
    connection% (losslessLC ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- The lossless loop conserves its energy. -/
@[powerlib_domain] theorem losslessLC_mem_den_conservative :
    connection% (losslessLC ∈ Port.PortHamiltonian.family.den (.flow .conservative)) :=
  mem_den_conservative_of_lossless _ rfl

/-- The lossless loop is (zero-state) observable from the loop current.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem losslessLC_observable :
    LinearSystems.IsObservable (linearLTIModel losslessJ 0 losslessG 1).A
      (linearLTIModel losslessJ 0 losslessG 1).C := by
  intro x hx
  have h0 := congrFun (hx ⟨0, by norm_num⟩) 0
  have h1 := congrFun (hx ⟨1, by norm_num⟩) 0
  simp [linearLTIModel, linearStateMatrix, losslessJ, losslessG, mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.mul_apply] at h0 h1
  funext i; fin_cases i <;> simp [h0, h1]

/-- `x(t) = (cos t, sin t)` is an unforced solution of the lossless loop on every segment.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem losslessLC_trajectory (t₀ t₁ : ℝ) :
    IsTrajectoryOn (fun t => WithLp.toLp 2 ![Real.cos t, Real.sin t])
      losslessLC.plant.system.zeroInput t₀ t₁ := by
  intro t _
  apply HasDerivAt.hasDerivWithinAt
  have h : HasDerivAt (fun t => ![Real.cos t, Real.sin t]) ![-Real.sin t, Real.cos t] t := by
    apply hasDerivAt_pi.2
    intro i; fin_cases i
    · simpa using Real.hasDerivAt_cos t
    · simpa using Real.hasDerivAt_sin t
  have h' : HasDerivAt (fun t => WithLp.toLp 2 ![Real.cos t, Real.sin t])
      (WithLp.toLp 2 ![-Real.sin t, Real.cos t]) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h
  convert h' using 1
  apply WithLp.ofLp_injective
  ext i; fin_cases i <;>
    simp [Linear.Plant.system, Port.System.zeroInput, losslessLC, toPortHamiltonian,
      Port.PortHamiltonian.plant, losslessJ, Linear.op, Matrix.ofLp_toEuclideanCLM, mulVec,
      dotProduct, Fin.sum_univ_two]

/-- That trajectory keeps unit energy, so it does not converge to the origin.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem losslessLC_not_tendsto :
    ¬ Filter.Tendsto (fun t => ![Real.cos t, Real.sin t]) Filter.atTop (nhds 0) := by
  intro h
  have h2 : Filter.Tendsto (fun t => (![Real.cos t, Real.sin t] : Fin 2 → ℝ) 0 ^ 2 +
      (![Real.cos t, Real.sin t] : Fin 2 → ℝ) 1 ^ 2) Filter.atTop (nhds ((0 : Fin 2 → ℝ) 0 ^ 2 +
        (0 : Fin 2 → ℝ) 1 ^ 2)) := by
    have hc0 := ((continuous_apply 0).tendsto _).comp h
    have hc1 := ((continuous_apply 1).tendsto _).comp h
    exact (hc0.pow 2).add (hc1.pow 2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.cos_sq_add_sin_sq,
    Pi.zero_apply] at h2
  norm_num at h2

/-- The lossless loop's state matrix is not Hurwitz (trace zero).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem losslessLC_not_isHurwitz :
    ¬ LinearSystems.IsHurwitz (linearLTIModel losslessJ 0 losslessG 1).A := by
  intro h
  rw [show (linearLTIModel losslessJ 0 losslessG 1).A = !![0, -1; 1, 0] from
    losslessLC_stateMatrix, Criteria.isHurwitz_fin_two_of_iff] at h
  linarith [h.1]

/-- The lossless loop is not locally asymptotically stable. -/
@[powerlib_domain] theorem losslessLC_not_mem_den_locallyAsymptoticallyStable :
    connection% (losslessLC ∉
      Port.PortHamiltonian.family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [Port.PortHamiltonian.family_isLinear.den_hurwitz (P := .locallyAsymptoticallyStable)
    (Or.inl trivial)]
  exact losslessLC_not_isHurwitz

/-- Correction of T-ph Part 2: passivity together with zero-state observability does **not**
give asymptotic stability, on the semantics connection of the linear port-Hamiltonian family. -/
@[powerlib_domain] theorem passive_observable_not_asymptotic :
    connection% (¬ ∀ h : Port.PortHamiltonian 2 1,
      h ∈ Port.PortHamiltonian.family.den .passive →
        LinearSystems.IsObservable h.plant.A h.plant.C →
          h ∈ Port.PortHamiltonian.family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro H
  have := H losslessLC losslessLC_mem_den_passive losslessLC_observable
  exact losslessLC_not_mem_den_locallyAsymptoticallyStable this

/-! ## Corrected statement: damping injection + observability ⇒ Hurwitz -/

section Feedback

variable {J R Q : Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin n) (Fin m) ℝ} {k : ℝ}

/-- Output feedback `u = −k y` turns `(J − R) Q x + g u` into `(J − (R + k g gᵀ)) Q x`. -/
@[powerlib_foundation] theorem phOutputFeedback_stateMatrix (k : ℝ) :
    linearStateMatrix J R Q - g * (k • (gᵀ * Q)) = linearStateMatrix J (R + k • (g * gᵀ)) Q := by
  simp only [linearStateMatrix, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sub_mul,
    add_mul]
  abel

/-- Damping injection `u = −k y` (`k > 0`) on an observable linear pH system gives a Hurwitz
closed loop. -/
@[powerlib_foundation] theorem phOutputFeedback_isHurwitz (hJ : Jᵀ = -J) (hR : R.PosSemidef)
    (hQ : Q.PosDef) (hk : 0 < k)
    (hobs : LinearSystems.IsObservable (linearStateMatrix J R Q) (gᵀ * Q)) :
    LinearSystems.IsHurwitz (linearStateMatrix J (R + k • (g * gᵀ)) Q) := by
  intro μ v hv heig
  rw [neg_zero]
  have hQt : Qᵀ = Q := symmetric_of_posDef hQ
  set C := gᵀ * Q with hCdef
  have hggt : (g * gᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose g
  have hR' : (R + k • (g * gᵀ)).PosSemidef := hR.add (hggt.smul hk.le)
  refine (phSpectral_re_nonpos hJ hR' hQ hv heig).lt_of_ne fun heq0 => ?_
  set A' := linearStateMatrix J (R + k • (g * gᵀ)) Q with hA'def
  have hR't : (R + k • (g * gᵀ))ᵀ = R + k • (g * gᵀ) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR'.isHermitian.eq
  -- The closed-loop Lyapunov form: `wᵀ Q A' w = -(Q w)ᵀ R (Q w) - k |C w|²`.
  have hform : ∀ w : Fin n → ℝ, w ⬝ᵥ (Q *ᵥ (A' *ᵥ w)) =
      -((Q *ᵥ w) ⬝ᵥ (R *ᵥ (Q *ᵥ w))) - k * ((C *ᵥ w) ⬝ᵥ (C *ᵥ w)) := by
    intro w
    have h := Linear.quadratic_sym (A := A') hQt w
    rw [linearStateMatrix_lyapunov hJ hQt hR't, Matrix.smul_mulVec, dotProduct_smul,
      ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hQt, add_mulVec,
      Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, ← mulVec_mulVec,
      dotProduct_mulVec (Q *ᵥ w) g, ← mulVec_transpose] at h
    rw [hCdef, ← mulVec_mulVec]
    simp only [smul_eq_mul] at h
    linarith
  -- At `Re μ = 0` the form vanishes at the real and imaginary parts of `v`, so `C v = 0`.
  have hsum := Criteria.lyapunov_form_eigenpair hQt heig
  rw [heq0, zero_mul, hform, hform] at hsum
  have hsq : ∀ u : Fin m → ℝ, 0 ≤ u ⬝ᵥ u := fun u =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hRQ : ∀ w : Fin n → ℝ, 0 ≤ (Q *ᵥ w) ⬝ᵥ (R *ᵥ (Q *ᵥ w)) := fun w => by
    simpa only [star_trivial] using hR.dotProduct_mulVec_nonneg (Q *ᵥ w)
  have hzero : ∀ w : Fin n → ℝ, (C *ᵥ w) ⬝ᵥ (C *ᵥ w) ≤ 0 →
      C *ᵥ w = 0 := fun w h => dotProduct_self_eq_zero.mp (le_antisymm h (hsq _))
  have ha := hzero (fun i => (v i).re) (by
    nlinarith [hRQ (fun i => (v i).re), hRQ (fun i => (v i).im), hsq (C *ᵥ fun i => (v i).re),
      hsq (C *ᵥ fun i => (v i).im)])
  have hb := hzero (fun i => (v i).im) (by
    nlinarith [hRQ (fun i => (v i).re), hRQ (fun i => (v i).im), hsq (C *ᵥ fun i => (v i).re),
      hsq (C *ᵥ fun i => (v i).im)])
  have hCv : Linear.complexify C *ᵥ v = 0 := by
    funext i
    apply Complex.ext
    · rw [phCx_mulVec_re, ha]; rfl
    · rw [phCx_mulVec_im, hb]; rfl
  -- and `v` is an eigenvector of the open-loop `A`
  have hAv : Linear.complexify (linearStateMatrix J R Q) *ᵥ v = μ • v := by
    have hA : linearStateMatrix J R Q = A' + g * (k • C) := by
      rw [hA'def, ← phOutputFeedback_stateMatrix (J := J) (R := R) (Q := Q) (g := g) k, hCdef]
      abel
    rw [hA, phCx_complexify_add, add_mulVec, heig, Linear.complexify_mul, ← mulVec_mulVec]
    have : Linear.complexify (k • C) *ᵥ v = 0 := by
      rw [show Linear.complexify (k • C) = (k : ℂ) • Linear.complexify C by
        ext i j; simp [Linear.complexify]]
      rw [Matrix.smul_mulVec, hCv, smul_zero]
    rw [this, mulVec_zero, add_zero]
  exact hv (phCx_eq_zero_of_isObservable hobs hAv hCv)

/-- The damped closed loop `u = −k y + v` as a linear port-Hamiltonian plant: dissipation
`R + k g gᵀ`, same ports. -/
def phOutputFeedback (J R : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (k : ℝ) (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Q.PosDef)
    (hk : 0 ≤ k) : Port.PortHamiltonian n m :=
  toPortHamiltonian J (R + k • (g * gᵀ)) g Q hJ
    (hR.add ((by simpa [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_self_mul_conjTranspose g : (g * gᵀ).PosSemidef).smul hk)) hQ

/-- Damping injection `u = −k y` (`k > 0`) on an observable linear pH system: the unforced
closed loop `ẋ = (J − (R + k g gᵀ)) Q x` is globally exponentially stable. -/
@[powerlib_domain] theorem phOutputFeedback_mem_den_globallyExponentiallyStable (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) (hk : 0 < k)
    (hobs : LinearSystems.IsObservable (linearStateMatrix J R Q) (gᵀ * Q)) :
    connection% (phOutputFeedback J R g Q k hJ hR hQ hk.le ∈
      Port.PortHamiltonian.family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [Port.PortHamiltonian.family_isLinear.den_hurwitz (P := .globallyExponentiallyStable)
    (Or.inl trivial)]
  exact phOutputFeedback_isHurwitz hJ hR hQ hk hobs

end Feedback

end powerlib.PH
