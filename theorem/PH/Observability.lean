import theorem.PH.PositiveReal
import theorem.Criteria.Hurwitz2
import theorem.Dynamics.Basin

/-! # Passivity, zero-state observability and asymptotic stability of linear pH systems

Source: work-sync `theory/T-ph.md` Part 2, "Passivity 不等于稳定": "(1.4) 给的是 input-output
passivity … 需配合 zero-state observability + detectability（Khalil 2002 §6）才推出渐近稳定".

Model: the constant-coefficient pH system of `theorem/PH/Linear.lean` (P0b) as the linear plant
`linearLTIModel J R g Q` (a `Linear.Plant`): `ẋ = (J − R) Q x + g u`, `y = gᵀ Q x`, `H = ½ xᵀ Q x`, with `J`
skew, `R ⪰ 0`, `Q ≻ 0`, real, continuous time. For a linear system zero-state observability is
observability of the pair `(A, C) = ((J − R) Q, gᵀ Q)` (`LinearSystems.IsObservable`).

Correction (refutation of the literal claim). Passivity together with zero-state observability
does **not** give asymptotic stability of the unforced system: the lossless series `LC` loop
(`J = [[0, −1], [1, 0]]`, `R = 0`, `g = (1, 0)ᵀ`, `Q = I`, output the loop current) is passive
(`losslessLC_passive`) and observable (`losslessLC_observable`), but `x(t) = (cos t, sin t)` is an
unforced trajectory that keeps its energy (`losslessLC_trajectory`, `losslessLC_not_tendsto`),
and its state matrix is not Hurwitz (`losslessLC_not_isHurwitz`). Khalil's results need output
strict passivity or an output feedback `u = −φ(y)`.

Corrected statement (`phOutputFeedback_isHurwitz`, `phOutputFeedback_mem_den_globallyExponentiallyStable`):
with damping injection `u = −k y` (`k > 0`; the closed loop is the pH system with dissipation
`R + k g gᵀ`, i.e. output strictly passive, `Ḣ ≤ −k |y|²`) and `(A, C)` observable, the closed
loop is Hurwitz, hence exponentially stable. The proof is spectral (an eigenvector on the
imaginary axis would have `C v = 0` and be an eigenvector of `A`, contradicting observability);
for linear systems this replaces the LaSalle argument.

Nonlinear LaSalle version (generic, foundation; Khalil, *Nonlinear Systems*, 3rd ed., Lemma 6.7
with zero-state detectability). Model boundary: an arbitrary continuous-time input-affine or
general system `ẋ = F(x, u)`, `y = H(x)` on `EuclideanSpace ℝ (Fin n)` with `m` ports, no delay,
switching or time variation; passivity is the static dissipation inequality
`V̇(x, u) = DV(x)·F(x, u) ≤ ⟪u, y⟫` for a `C¹` storage `V` that is positive definite (`V(0) = 0`,
`V > 0` elsewhere); `F(0, 0) = 0`; zero-state detectability: every unforced forward solution
(`u ≡ 0`) with `y ≡ 0` converges to `0`. The loop is closed by an output feedback `u = −ψ(y)`
with `ψ(0) = 0` and `⟪ψ(y), y⟫ > 0` for `y ≠ 0` (damping injection `ψ(y) = k y`, `k > 0`), and
the closed-loop field is assumed `C¹`.
* `tendsto_zero_of_lasalle_detectable`: LaSalle's principle (via
  `Dynamics.lasalle_invariance_principle_of_contDiff`) with detectability on `{V̇ = 0}` — every
  forward solution from a compact positively invariant set converges to `0` (a positively
  invariant subset of `{V̇ = 0}` carries a forward solution along which `V` is constant and which
  converges to `0`, so `V = 0` on it).
* `output_eq_zero_of_passive` (`H(0) = 0`), `lieDeriv_feedback_le` (`V̇ ≤ −⟪ψ(y), y⟫ ≤ 0`, and
  `V̇ = 0` only on `{y = 0}`, where the closed loop is the unforced system).
* `globallyAsymptoticallyStable_of_passive_detectable`: with `V` radially unbounded, `0` is a
  globally asymptotically stable equilibrium of the closed loop (Flow semantics: equilibrium,
  forward completeness, LeanForControl's `GlobalAsymptoticStable`).
* `localAsymptoticStable_of_passive_detectable`: with one compact sublevel set `{V ≤ c₀}`,
  `c₀ > 0`, local asymptotic stability.
* `detectable_of_observable`, `globallyAsymptoticallyStable_of_passive_observable`: the
  zero-state-observable special case.
Together with the counterexample above, this is the corrected nonlinear reading of the note:
passivity and zero-state observability/detectability give asymptotic stability once the output
is fed back (or, equivalently, the system is output strictly passive), not for the unforced
passive system. These are generic implications about arbitrary fields, hence foundation results
(no model family).

Family and connection conclusions. No new family: the lossless loop and the damped closed loop
are linear port-Hamiltonian plants (`losslessLC`, `phOutputFeedback`, via `toPortHamiltonian`),
read through `Port.PortHamiltonian.family` (sentences at the origin, the unforced state).
Connection conclusions: the loop is passive (`losslessLC_mem_den_passive`) and conservative
(`losslessLC_mem_den_conservative`) but not locally asymptotically stable
(`losslessLC_not_mem_den_locallyAsymptoticallyStable`); the literal claim "passive and observable
⇒ asymptotically stable" is refuted on the semantics connection
(`passive_observable_not_asymptotic`); and damping injection on an observable pH plant is
globally exponentially stable (`phOutputFeedback_mem_den_globallyExponentiallyStable`, formerly
`phOutputFeedback_exponentiallyStable` on the removed `LTI` semantics). Observability, Hurwitz
and spectral facts are static evidence; the explicit unforced solution `(cos t, sin t)` is
private implementation evidence (`losslessLC_trajectory`).
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
    ((Linear.complexify M *ᵥ v) i).re = (M *ᵥ fun j => (v j).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

@[powerlib_foundation] theorem phCx_mulVec_im {p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ)
    (v : Fin n → ℂ) (i : Fin p) :
    ((Linear.complexify M *ᵥ v) i).im = (M *ᵥ fun j => (v j).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

/-- A complex eigenvector of a real `A` lying in `ker C` contradicts observability of `(A, C)`. -/
@[powerlib_foundation] theorem phCx_eq_zero_of_isObservable {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin p) (Fin n) ℝ} (hobs : LinearSystems.IsObservable A C) {μ : ℂ}
    {v : Fin n → ℂ} (heig : Linear.complexify A *ᵥ v = μ • v) (hC : Linear.complexify C *ᵥ v = 0) :
    v = 0 := by
  have hpow : ∀ k : ℕ, Linear.complexify (C * A ^ k) *ᵥ v = 0 := by
    intro k
    have hA : ∀ j : ℕ, Linear.complexify (A ^ j) *ᵥ v = μ ^ j • v := by
      intro j
      induction j with
      | zero => simp [Linear.complexify]
      | succ j ih =>
        rw [pow_succ, Linear.complexify_mul, ← mulVec_mulVec, heig, mulVec_smul, ih, smul_smul,
          pow_succ, mul_comm]
    rw [Linear.complexify_mul, ← mulVec_mulVec, hA, mulVec_smul, hC, smul_zero]
  have hre := hobs (fun j => (v j).re) fun k => by
    funext i
    have := congrFun (hpow k) i
    rw [← phCx_mulVec_re, this]
    simp
  have him := hobs (fun j => (v j).im) fun k => by
    funext i
    have := congrFun (hpow k) i
    rw [← phCx_mulVec_im, this]
    simp
  funext j
  apply Complex.ext
  · simpa using congrFun hre j
  · simpa using congrFun him j

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
`g = losslessG`, `Q = 1`. -/
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

/-- Formerly the public `losslessLC_trajectory`: `x(t) = (cos t, sin t)` is an unforced solution
of the lossless loop on every segment.
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
  have hle : μ.re ≤ 0 := phSpectral_re_nonpos hJ hR' hQ hv heig
  rcases hle.lt_or_eq with hlt | heq0
  · exact hlt
  · exfalso
    -- the Lyapunov identity with `μ.re = 0` forces `Re vᴴ (Q (R + k g gᵀ) Q) v = 0`
    set A' := linearStateMatrix J (R + k • (g * gᵀ)) Q with hA'def
    set S := star v ⬝ᵥ (Linear.complexify Q *ᵥ v)
    have hR't : (R + k • (g * gᵀ))ᵀ = R + k • (g * gᵀ) := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using hR'.isHermitian.eq
    have hlyap := linearStateMatrix_lyapunov hJ hQt hR't
    have h1 : star v ⬝ᵥ (Linear.complexify (Q * A') *ᵥ v) = μ * S := by
      rw [Linear.complexify_mul, ← mulVec_mulVec, heig, mulVec_smul, dotProduct_smul, smul_eq_mul]
    have h2 : star v ⬝ᵥ (Linear.complexify (A'ᵀ * Q) *ᵥ v) = star μ * S := by
      rw [Linear.complexify_mul, ← mulVec_mulVec, ← phCx_complexify_conjTranspose,
        dotProduct_mulVec, ← star_mulVec, heig, star_smul, smul_dotProduct, smul_eq_mul]
    have hsum : star v ⬝ᵥ (Linear.complexify (A'ᵀ * Q + Q * A') *ᵥ v) = star μ * S + μ * S := by
      rw [phCx_complexify_add, add_mulVec, dotProduct_add, h1, h2]
    have hre0 : (star v ⬝ᵥ (Linear.complexify (A'ᵀ * Q + Q * A') *ᵥ v)).re = 0 := by
      rw [hsum]
      simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
        Complex.conj_im]
      rw [heq0]; ring
    rw [hlyap] at hre0
    -- split `Q (R + k g gᵀ) Q = Qᵀ R Q + k Cᵀ C`
    have hsplit : -(2 : ℝ) • (Q * (R + k • (g * gᵀ)) * Q) =
        -(2 : ℝ) • (Qᵀ * R * Q) + -(2 * k) • (Cᵀ * C) := by
      rw [hCdef, transpose_mul, transpose_transpose, hQt]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
        smul_smul, Matrix.mul_assoc]
      ring_nf
    rw [hsplit, phCx_complexify_add, add_mulVec, dotProduct_add, Complex.add_re] at hre0
    have hQRQ : (Qᵀ * R * Q).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hR.conjTranspose_mul_mul_same Q
    have hCC : (Cᵀ * C).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self C
    have hsm : ∀ (c : ℝ) (P : Matrix (Fin n) (Fin n) ℝ),
        (star v ⬝ᵥ (Linear.complexify (c • P) *ᵥ v)).re = c * (star v ⬝ᵥ (Linear.complexify P *ᵥ v)).re := by
      intro c P
      rw [phCx_form_re, phCx_form_re, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul,
        dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsm, hsm] at hre0
    have hn1 := phCx_form_re_nonneg hQRQ v
    have hn2 := phCx_form_re_nonneg hCC v
    have hCC0 : (star v ⬝ᵥ (Linear.complexify (Cᵀ * C) *ᵥ v)).re = 0 := by nlinarith
    -- hence `C v = 0`
    have hCv : Linear.complexify C *ᵥ v = 0 := by
      rw [phCx_form_re] at hCC0
      have ha := hCC.dotProduct_mulVec_nonneg (fun i => (v i).re)
      have hb := hCC.dotProduct_mulVec_nonneg (fun i => (v i).im)
      rw [star_trivial] at ha hb
      have ha0 : (fun i => (v i).re) ⬝ᵥ ((Cᵀ * C) *ᵥ fun i => (v i).re) = 0 := by linarith
      have hb0 : (fun i => (v i).im) ⬝ᵥ ((Cᵀ * C) *ᵥ fun i => (v i).im) = 0 := by linarith
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, dotProduct_self_eq_zero] at ha0 hb0
      funext i
      apply Complex.ext
      · rw [phCx_mulVec_re, ha0]; rfl
      · rw [phCx_mulVec_im, hb0]; rfl
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

section ZeroState

variable {n m : ℕ}

/-- **LaSalle with detectability.** `f` C¹, `V` C¹ positive definite with `V̇ ≤ 0` everywhere,
and every forward solution of `f` along which `V̇` vanishes identically converges to `0`. Then
every forward solution starting in a compact positively invariant set converges to `0`. -/
@[powerlib_foundation] theorem tendsto_zero_of_lasalle_detectable
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) (hV : ContDiff ℝ 1 V)
    (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0)
    (hdet : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => f x) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), fderiv ℝ V (φ t) (f (φ t)) = 0) → Tendsto φ atTop (𝓝 0))
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩc : IsCompact Ω) (hΩi : IsPositivelyInvariant Ω f)
    {φ : ℝ → EuclideanSpace ℝ (Fin n)} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0))
    (hφ0 : φ 0 ∈ Ω) : Tendsto φ atTop (𝓝 0) := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hM : ∀ N ⊆ Dynamics.LieDerivZeroSet f V Ω, IsPositivelyInvariant N f →
      N ⊆ ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
    intro N hN hNinv p hp
    obtain ⟨g, -, ⟨K, hglip⟩, -, -, -, -, hgf⟩ := Dynamics.exists_globalization hf hΩc hΩi
    obtain ⟨χ, hχ0, hχ⟩ := Flow.forwardComplete_of_lipschitzWith hglip 0 p
    have hχf : IsIntegralCurveOn χ (fun _ x => f x) (Ici 0) :=
      hgf hχ (hχ0 ▸ (hN hp).1)
    have hstay : ∀ t ∈ Ici (0 : ℝ), χ t ∈ N := fun t ht =>
      hNinv 0 t χ (hχf.mono Icc_subset_Ici_self) (hχ0 ▸ hp) t ⟨ht, le_rfl⟩
    have hzero : ∀ t ∈ Ici (0 : ℝ), fderiv ℝ V (χ t) (f (χ t)) = 0 := fun t ht =>
      (hN (hstay t ht)).2
    have hlim := hdet χ hχf hzero
    -- `V ∘ χ` is constant on `[0, ∞)`
    have hanti : AntitoneOn (V ∘ χ) (Ici 0) :=
      antitoneOn_V_comp_traj hVd hVd.continuous (convex_Ici 0) hχf
        (fun t ht => (hzero t (interior_subset ht)).le)
    have hmono : AntitoneOn ((fun x => -V x) ∘ χ) (Ici 0) := by
      refine antitoneOn_V_comp_traj hVd.neg hVd.continuous.neg (convex_Ici 0) hχf
        (fun t ht => ?_)
      rw [fderiv_neg]
      simp [hzero t (interior_subset ht)]
    have hconst : ∀ t ∈ Ici (0 : ℝ), V (χ t) = V p := by
      intro t ht
      have h1 := hanti (mem_Ici.mpr le_rfl) ht ht
      have h2 := hmono (mem_Ici.mpr le_rfl) ht ht
      simp only [Function.comp_apply, hχ0] at h1 h2
      linarith
    have hVlim : Tendsto (fun t => V (χ t)) atTop (𝓝 (V 0)) :=
      (hVd.continuous.tendsto 0).comp hlim
    have hVlim' : Tendsto (fun t => V (χ t)) atTop (𝓝 (V p)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 0] with t ht
        exact (hconst t ht).symm)
    have hVp : V p = 0 := by rw [← hV0]; exact tendsto_nhds_unique hVlim' hVlim
    by_contra hne
    exact (hVpos p hne).ne' hVp
  have h := Dynamics.lasalle_invariance_principle_of_contDiff hΩc hΩi hf hV
    (fun x _ => hdec x) hφ hφ0 hM
  rwa [nhdsSet_singleton] at h

/-- Passivity with a storage minimized at `0` forces the output to vanish at `0`. -/
@[powerlib_foundation] theorem output_eq_zero_of_passive
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x)) : H 0 = 0 := by
  have hmin : IsLocalMin V 0 := Filter.Eventually.of_forall fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · exact le_rfl
    · rw [hV0]; exact (hVpos x hx).le
  have hd : fderiv ℝ V 0 = 0 := hmin.fderiv_eq_zero
  have h := hpass 0 (-H 0)
  rw [hd, inner_neg_left, real_inner_self_eq_norm_sq] at h
  rw [_root_.zero_apply] at h
  have : ‖H 0‖ ^ 2 ≤ 0 := by linarith
  exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (le_antisymm this (sq_nonneg _)))

/-- Output feedback `u = −ψ(y)` with `⟪ψ(y), y⟫ > 0` (`y ≠ 0`), `ψ(0) = 0` on a passive system:
`V̇ ≤ −⟪ψ(y), y⟫ ≤ 0`, and `V̇ = 0` only where `y = 0`. -/
@[powerlib_foundation] theorem lieDeriv_feedback_le
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ V x (F x (-ψ (H x))) ≤ 0 ∧
      (fderiv ℝ V x (F x (-ψ (H x))) = 0 → H x = 0) := by
  have h := hpass x (-ψ (H x))
  rw [inner_neg_left] at h
  constructor
  · rcases eq_or_ne (H x) 0 with h0 | h0
    · simp only [h0, hψ0, inner_zero_left, neg_zero] at h ⊢; exact h
    · linarith [hψ (H x) h0]
  · intro hz
    by_contra h0
    linarith [hψ (H x) h0]

/-- Zero-state detectability transported to the closed loop: a closed-loop solution along which
`V̇` vanishes stays in `{y = 0}`, where the closed loop is the unforced system. -/
private theorem closedLoop_detectable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y)
    (hzsd : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0)) :
    ∀ φ : ℝ → EuclideanSpace ℝ (Fin n),
      IsIntegralCurveOn φ (fun _ x => F x (-ψ (H x))) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), fderiv ℝ V (φ t) (F (φ t) (-ψ (H (φ t)))) = 0) →
        Tendsto φ atTop (𝓝 0) := by
  intro φ hφ hz
  have hH : ∀ t ∈ Ici (0 : ℝ), H (φ t) = 0 := fun t ht =>
    (lieDeriv_feedback_le hpass hψ0 hψ (φ t)).2 (hz t ht)
  refine hzsd φ (Dynamics.isIntegralCurveOn_of_eq_on_curve hφ fun t ht => ?_) hH
  rw [hH t ht, hψ0, neg_zero]

/-- **Passivity + zero-state detectability ⇒ global asymptotic stability** (Khalil, *Nonlinear
Systems*, Lemma 6.7, global part, with detectability in place of observability). For
`ẋ = F(x, u)`, `y = H(x)` passive with a `C¹` storage `V` that is positive definite and radially
unbounded (`V̇ ≤ ⟪u, y⟫`), with `F(0, 0) = 0`, and zero-state detectable (every unforced forward
solution with `y ≡ 0` converges to `0`), the output feedback `u = −ψ(y)` with `ψ(0) = 0`,
`⟪ψ(y), y⟫ > 0` (`y ≠ 0`; e.g. `ψ(y) = k y`, `k > 0`) makes `0` globally asymptotically stable,
provided the closed-loop field is `C¹`. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_of_passive_detectable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hn : 0 < n)
    (hf : ContDiff ℝ 1 fun x => F x (-ψ (H x)))
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hradial : Tendsto V (comap norm atTop) atTop)
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y) (hF0 : F 0 0 = 0)
    (hzsd : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0)) :
    Flow.GloballyAsymptoticallyStable (fun x => F x (-ψ (H x))) 0 := by
  set f := fun x => F x (-ψ (H x)) with hfdef
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hH0 := output_eq_zero_of_passive hV0 hVpos hpass
  have hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0 := fun x => (lieDeriv_feedback_le hpass hψ0 hψ x).1
  have hdet := closedLoop_detectable hpass hψ0 hψ hzsd
  have hsub : ∀ c : ℝ, IsCompact {x : EuclideanSpace ℝ (Fin n) | V x ≤ c} :=
    isCompact_sublevel_set V hV.continuous hradial
  refine ⟨?_, Flow.forwardComplete_of_compact_sublevel hf hVd hdec hsub, ?_, ?_⟩
  · show F 0 (-ψ (H 0)) = 0
    rw [hH0, hψ0, neg_zero, hF0]
  · exact lyapunov_stable hn ⟨isOpen_univ, mem_univ _, hVd.continuous, hVd, hV0,
      fun x _ hx => hVpos x hx, fun x _ => hdec x⟩
  · intro t₀ φ hφ
    have hψs : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Ici 0) := by
      have hset : -t₀ +ᵥ Ici t₀ = Ici (0 : ℝ) := by
        ext x
        simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, mem_Ici]
        constructor <;> intro h <;> linarith
      have h' := _root_.IsIntegralCurveOn.comp_add_autonomous hφ t₀
      rwa [hset] at h'
    have hinv : IsPositivelyInvariant {x | V x ≤ V (φ t₀)} f := by
      have h := Dynamics.isPositivelyInvariant_sublevel_of_isOpen (f := f) (c := V (φ t₀))
        isOpen_univ hVd (fun x _ => hdec x) (by
          simpa using (isClosed_le hVd.continuous continuous_const))
      simpa using h
    have hconv := tendsto_zero_of_lasalle_detectable hf hV hV0 hVpos hdec hdet (hsub _) hinv hψs
      (by simp)
    exact Tendsto.congr (fun x => by simp)
      (hconv.comp (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id))

/-- **Passivity + zero-state detectability ⇒ local asymptotic stability** (Khalil, Lemma 6.7,
local part). As `globallyAsymptoticallyStable_of_passive_detectable`, with radial unboundedness
replaced by one compact sublevel set `{V ≤ c₀}`, `c₀ > 0`. -/
@[powerlib_foundation] theorem localAsymptoticStable_of_passive_detectable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hn : 0 < n)
    (hf : ContDiff ℝ 1 fun x => F x (-ψ (H x)))
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hcompact : ∃ c > 0, IsCompact {x : EuclideanSpace ℝ (Fin n) | V x ≤ c})
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y)
    (hzsd : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0)) :
    LocalAsymptoticStable (fun x => F x (-ψ (H x))) 0 := by
  set f := fun x => F x (-ψ (H x)) with hfdef
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hdec : ∀ x, fderiv ℝ V x (f x) ≤ 0 := fun x => (lieDeriv_feedback_le hpass hψ0 hψ x).1
  have hdet := closedLoop_detectable hpass hψ0 hψ hzsd
  obtain ⟨c₀, hc₀, hK⟩ := hcompact
  refine ⟨lyapunov_stable hn ⟨isOpen_univ, mem_univ _, hVd.continuous, hVd, hV0,
      fun x _ hx => hVpos x hx, fun x _ => hdec x⟩, ?_⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuousAt_iff.mp (hVd.continuous.continuousAt (x := 0)) c₀ hc₀
  refine ⟨δ, hδ, fun t₀ φ hφ hφ0 => ?_⟩
  have hlt : V (φ t₀) < c₀ := by
    have h := hδV (x := φ t₀) (by rwa [dist_eq_norm])
    rw [Real.dist_eq, hV0, sub_zero] at h
    exact (abs_lt.mp h).2
  have hψs : IsIntegralCurveOn (fun s => φ (s + t₀)) (fun _ x => f x) (Ici 0) := by
    have hset : -t₀ +ᵥ Ici t₀ = Ici (0 : ℝ) := by
      ext x
      simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, mem_Ici]
      constructor <;> intro h <;> linarith
    have h' := _root_.IsIntegralCurveOn.comp_add_autonomous hφ t₀
    rwa [hset] at h'
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin n) | V x ≤ V (φ t₀)} :=
    isClosed_le hVd.continuous continuous_const
  have hinv : IsPositivelyInvariant {x | V x ≤ V (φ t₀)} f := by
    have h := Dynamics.isPositivelyInvariant_sublevel_of_isOpen (f := f) (c := V (φ t₀))
      isOpen_univ hVd (fun x _ => hdec x) (by simpa using hclosed)
    simpa using h
  have hΩ : IsCompact {x : EuclideanSpace ℝ (Fin n) | V x ≤ V (φ t₀)} :=
    hK.of_isClosed_subset hclosed fun x (hx : V x ≤ V (φ t₀)) => show V x ≤ c₀ by linarith
  have hconv := tendsto_zero_of_lasalle_detectable hf hV hV0 hVpos hdec hdet hΩ hinv hψs
    (by simp)
  exact Tendsto.congr (fun x => by simp)
    (hconv.comp (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id))

/-- Zero-state observability (the only unforced forward solution with `y ≡ 0` is `x ≡ 0`)
implies zero-state detectability. -/
@[powerlib_foundation] theorem detectable_of_observable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hzso : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → ∀ t ∈ Ici (0 : ℝ), φ t = 0) :
    ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → Tendsto φ atTop (𝓝 0) := by
  intro φ hφ hH
  exact tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hzso φ hφ hH t ht).symm)

/-- **Passivity + zero-state observability ⇒ global asymptotic stability under output feedback**
(Khalil, Lemma 6.7): the zero-state-observable special case of
`globallyAsymptoticallyStable_of_passive_detectable`. -/
@[powerlib_foundation] theorem globallyAsymptoticallyStable_of_passive_observable
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hn : 0 < n)
    (hf : ContDiff ℝ 1 fun x => F x (-ψ (H x)))
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hradial : Tendsto V (comap norm atTop) atTop)
    (hpass : ∀ x u, fderiv ℝ V x (F x u) ≤ inner ℝ u (H x))
    (hψ0 : ψ 0 = 0) (hψ : ∀ y, y ≠ 0 → 0 < inner ℝ (ψ y) y) (hF0 : F 0 0 = 0)
    (hzso : ∀ φ : ℝ → EuclideanSpace ℝ (Fin n), IsIntegralCurveOn φ (fun _ x => F x 0) (Ici 0) →
      (∀ t ∈ Ici (0 : ℝ), H (φ t) = 0) → ∀ t ∈ Ici (0 : ℝ), φ t = 0) :
    Flow.GloballyAsymptoticallyStable (fun x => F x (-ψ (H x))) 0 :=
  globallyAsymptoticallyStable_of_passive_detectable hn hf hV hV0 hVpos hradial hpass hψ0 hψ hF0
    (detectable_of_observable hzso)

end ZeroState

end powerlib.PH
