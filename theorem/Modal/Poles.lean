import theorem.Modal.Spectral
import theorem.Modal.Perturbation
import theorem.Linear.Realization
import theorem.Linear.EigenMap
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Constructions

/-! # Poles of a minimal realization are exactly the eigenvalues

For every minimal realization the pole set of the transfer matrix equals the spectrum of the
state matrix; minimality cannot be dropped.

Scope.
* Matrix / transfer-function level, no model family: transfer functions and spectra, no
  trajectories. Static evidence on the plant, not a connection conclusion.
* A real LTI plant `m : Linear.Plant n p` (`ẋ = A x + B u`, `y = C x + D u`, state `ℝⁿ`, `p`
  inputs and outputs, continuous time, no delay), its transfer matrix
  `G(s) = Linear.transfer m s = C (sI − A)⁻¹ B + D` over `s ∈ ℂ`, and minimality
  `Linear.Plant.Minimal m` = LeanForControl's `IsControllable A B ∧ IsObservable A C` (real rank
  conditions).
* A **pole** of `G` at `μ ∈ ℂ` means: some entry `G_ij` is unbounded on every punctured
  neighbourhood of `μ` (`¬ IsBoundedUnder (≤) (𝓝[≠] μ) ‖G_ij‖`); for the rational entries of `G`
  this is the usual notion of a (non-removable) pole. Eigenvalues are the complex spectrum
  `σ(A) = spectrum ℂ (complexify A)`; `Modal.mem_spectrum_iff_exists_eigvec` identifies it with
  the set of eigenvalues.
* `theorem/Modal/Spectral.lean` (`transfer_pole_iff`) proves the statement only for
  diagonalisable `A` with simple eigenvalues and modal PBH data; here the general case is proved.

Source: work-sync theory/T-small-signal-stability.md §1.9 (transfer-function poles versus
eigenvalues; minimal realizations), theory/T-participation-factor.md §2.5 (hidden modes).

Results.
* `transfer_isBoundedUnder_of_not_mem_spectrum` — off `σ(A)` every entry of `G` is bounded near
  `μ` (any realization; `G` is continuous there).
* `transfer_not_isBoundedUnder_of_mem_spectrum` — for a minimal realization, every `μ ∈ σ(A)` is
  a pole. Proof: if all entries of `C (sI − A)⁻¹ B` were bounded near `μ`, so would be
  `C q(A) (sI − A)⁻¹ B` for every polynomial `q` (`A (sI − A)⁻¹ = s (sI − A)⁻¹ − I`). Writing
  the minimal polynomial as `π = (X − μ) φ`, `Φ = Aⁱ φ(A) Aʲ` satisfies `Φ A = μ Φ`, hence
  `C Φ (sI − A)⁻¹ B = C Φ B / (s − μ)`, which is bounded only if `C Aⁱ φ(A) Aʲ B = 0`.
  Observability and controllability (transferred from the real predicates to complex vectors)
  then give `φ(A) = 0`, contradicting `deg φ < deg π`.
* `minimal_pole_iff`, `minimal_poles_eq_spectrum` — **the pole set of `G` equals `σ(A)`** for
  every minimal realization.
* `minimal_pole_tendsto_iff` — strong form: `μ ∈ σ(A)` iff `‖G_ij(s)‖ → ∞` (`s → μ`, `s ≠ μ`)
  for some entry. Each entry is meromorphic (`meromorphicAt_transfer`: analytic numerator
  `C adj(sI − A) B` over `det(sI − A)`), so an unbounded entry tends to infinity
  (`tendsto_norm_transfer_of_not_isBoundedUnder`, Mathlib `meromorphicOrderAt`).
* `hiddenMode_eigenvalue_not_pole` — minimality cannot be dropped (`Linear.hiddenMode`, `A = 1`,
  `B = C = D = 0`: eigenvalue `1`, `G ≡ 0`).
* Supporting facts: `analyticAt_det`, `analyticAt_adjugate`, `analyticAt_characteristicMatrix`,
  `eventually_det_characteristicMatrix_ne_zero`, `mul_resolvent`,
  `mul_resolvent_of_mul_eq`, `eq_zero_of_isBigO_inv_sub`, `complexify_pow`,
  `complexify_mulVec_re/im`, `eq_zero_of_isObservable`, `eq_zero_of_isControllable`.
-/

noncomputable section
namespace powerlib.Modal
open Matrix Filter Polynomial Asymptotics Topology
open powerlib.Linear LinearSystems

variable {n p : ℕ}


/-! ## Resolvent facts -/

/-- Off a finite set of points, `sI − A` is invertible; in particular eventually near every `μ`
(punctured). -/
@[tmio T, powerlib_foundation] theorem eventually_det_characteristicMatrix_ne_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) :
    ∀ᶠ s in 𝓝[≠] μ, (characteristicMatrix A s).det ≠ 0 := by
  have hχ : (complexify A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hfin : ({x | IsRoot (complexify A).charpoly x} \ {μ}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hχ).subset Set.sdiff_subset
  have hmem : ({x | IsRoot (complexify A).charpoly x} \ {μ})ᶜ ∈ 𝓝 μ :=
    hfin.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs hsμ
  rw [det_characteristicMatrix]
  intro h0
  exact hs ⟨h0, hsμ⟩

/-- `A (sI − A)⁻¹ = s (sI − A)⁻¹ − I`. -/
@[powerlib_foundation] theorem mul_resolvent {A : Matrix (Fin n) (Fin n) ℝ} {s : ℂ}
    (h : (characteristicMatrix A s).det ≠ 0) :
    complexify A * (characteristicMatrix A s)⁻¹ = s • (characteristicMatrix A s)⁻¹ - 1 := by
  have hinv := Matrix.mul_nonsing_inv (characteristicMatrix A s) (isUnit_iff_ne_zero.mpr h)
  generalize (characteristicMatrix A s)⁻¹ = R at hinv ⊢
  rw [show characteristicMatrix A s = s • 1 - complexify A from rfl, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.one_mul] at hinv
  rw [← hinv]
  abel

/-- If `Φ A = μ Φ`, then `Φ (sI − A)⁻¹ = (s − μ)⁻¹ Φ` for `s ≠ μ` off the spectrum. -/
@[powerlib_foundation] theorem mul_resolvent_of_mul_eq {A : Matrix (Fin n) (Fin n) ℝ}
    {Φ : Matrix (Fin n) (Fin n) ℂ} {μ s : ℂ} (hΦ : Φ * complexify A = μ • Φ)
    (h : (characteristicMatrix A s).det ≠ 0) (hs : s ≠ μ) :
    Φ * (characteristicMatrix A s)⁻¹ = (s - μ)⁻¹ • Φ := by
  have hinv := Matrix.mul_nonsing_inv (characteristicMatrix A s) (isUnit_iff_ne_zero.mpr h)
  have hΦc : Φ * characteristicMatrix A s = (s - μ) • Φ := by
    rw [show characteristicMatrix A s = s • 1 - complexify A from rfl, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.mul_one, hΦ, sub_smul]
  have hsμ : s - μ ≠ 0 := sub_ne_zero.mpr hs
  calc Φ * (characteristicMatrix A s)⁻¹
      = (s - μ)⁻¹ • ((s - μ) • Φ * (characteristicMatrix A s)⁻¹) := by
        rw [Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hsμ, one_smul]
    _ = (s - μ)⁻¹ • Φ := by
        rw [← hΦc, Matrix.mul_assoc, hinv, Matrix.mul_one]

/-- A function `c / (s − μ)` that is bounded on a punctured neighbourhood of `μ` has `c = 0`. -/
@[powerlib_foundation] theorem eq_zero_of_isBigO_inv_sub {μ c : ℂ}
    (h : (fun s => (s - μ)⁻¹ * c) =O[𝓝[≠] μ] (fun _ => (1 : ℝ))) : c = 0 := by
  obtain ⟨K, hK⟩ := isBigO_iff.mp h
  have hev : ∀ᶠ s in 𝓝[≠] μ, ‖c‖ ≤ K * ‖s - μ‖ := by
    filter_upwards [hK, self_mem_nhdsWithin] with s hs hsμ
    have hne : s - μ ≠ 0 := sub_ne_zero.mpr hsμ
    rw [norm_one, mul_one, norm_mul, norm_inv] at hs
    have hpos : 0 < ‖s - μ‖ := norm_pos_iff.mpr hne
    calc ‖c‖ = ‖s - μ‖ * (‖s - μ‖⁻¹ * ‖c‖) := by field_simp
      _ ≤ ‖s - μ‖ * K := by gcongr
      _ = K * ‖s - μ‖ := mul_comm _ _
  have ht : Tendsto (fun s => K * ‖s - μ‖) (𝓝[≠] μ) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => K * ‖s - μ‖) (𝓝 μ) (𝓝 (K * ‖μ - μ‖)) :=
      (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto μ
    rw [sub_self, norm_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto ht hev
  exact norm_le_zero_iff.mp this

/-! ## Complex observability and controllability from the real predicates -/

@[powerlib_foundation] theorem complexify_mulVec_re {a b : Type*} [Fintype b]
    (M : Matrix a b ℝ) (v : b → ℂ) (i : a) :
    ((complexify M *ᵥ v) i).re = (M *ᵥ fun j => (v j).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

@[powerlib_foundation] theorem complexify_mulVec_im {a b : Type*} [Fintype b]
    (M : Matrix a b ℝ) (v : b → ℂ) (i : a) :
    ((complexify M *ᵥ v) i).im = (M *ᵥ fun j => (v j).im) i := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

@[powerlib_foundation] theorem complexify_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k :=
  map_pow (RingHom.mapMatrix (algebraMap ℝ ℂ)) A k

/-- Real observability gives observability of complex states. -/
@[powerlib_foundation] theorem eq_zero_of_isObservable {A : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin p) (Fin n) ℝ} (h : IsObservable A C) {v : Fin n → ℂ}
    (hv : ∀ k : ℕ, (complexify C * complexify A ^ k) *ᵥ v = 0) : v = 0 := by
  have hk : ∀ k : ℕ, complexify (C * A ^ k) *ᵥ v = 0 := fun k => by
    rw [complexify_mul, complexify_pow]; exact hv k
  have hre : (fun j => (v j).re) = 0 := h _ fun k => by
    funext i
    rw [← complexify_mulVec_re, hk k]; rfl
  have him : (fun j => (v j).im) = 0 := h _ fun k => by
    funext i
    rw [← complexify_mulVec_im, hk k]; rfl
  funext j
  exact Complex.ext (congrFun hre j) (congrFun him j)

/-- Real controllability: a complex matrix annihilating every `Aᵏ B` is zero. -/
@[powerlib_foundation] theorem eq_zero_of_isControllable {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin p) ℝ} (h : IsControllable A B) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ k : ℕ, M * complexify A ^ k * complexify B = 0) : M = 0 := by
  have hcol : ∀ l, M *ᵥ Pi.single l 1 = 0 := by
    intro l
    obtain ⟨u, hu⟩ := h (Pi.single l 1)
    have hx : (Pi.single l (1 : ℂ) : Fin n → ℂ) =
        ∑ k : Fin n, complexify (A ^ (k : ℕ) * B) *ᵥ fun c => (u k c : ℂ) := by
      funext i
      have := congrArg (fun x : Fin n → ℝ => ((x i : ℝ) : ℂ)) hu
      rw [Finset.sum_apply]
      convert this using 1
      · by_cases hil : i = l
        · subst hil; simp
        · simp [hil]
      · rw [Finset.sum_apply]
        push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        have := RingHom.map_mulVec (algebraMap ℝ ℂ) (A ^ (k : ℕ) * B) (u k) i
        exact this.symm
    rw [hx, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.mulVec_mulVec, complexify_mul, complexify_pow, ← Matrix.mul_assoc, hM k,
      Matrix.zero_mulVec]
  ext i l
  have := congrFun (hcol l) i
  rwa [Matrix.mulVec_single_one] at this

/-! ## Poles of a minimal realization -/

/-- Away from the spectrum every entry of the transfer matrix is bounded near `μ` (no minimality
needed): `G` is continuous at `μ`. -/
@[powerlib_foundation] theorem transfer_isBoundedUnder_of_not_mem_spectrum (m : Plant n p)
    {μ : ℂ} (hμ : μ ∉ spectrum ℂ (complexify m.A)) (i j : Fin p) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] μ) (fun s => ‖transfer m s i j‖) := by
  have hdet : (characteristicMatrix m.A μ).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, heig⟩ := exists_eigenvector_of_root h0
    exact hμ (mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, heig⟩)
  have hc := transfer_continuousAt m.A m.B m.C m.D hdet
  have hij : ContinuousAt (fun s => transfer m s i j) μ :=
    (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hc)
  exact (hij.tendsto.mono_left nhdsWithin_le_nhds).norm.isBoundedUnder_le

/-- **At every eigenvalue of a minimal realization the transfer matrix has a pole**: some entry
of `G(s) = C (sI − A)⁻¹ B + D` is unbounded on every punctured neighbourhood of `μ ∈ σ(A)`. -/
@[powerlib_foundation] theorem transfer_not_isBoundedUnder_of_mem_spectrum {m : Plant n p}
    (hm : m.Minimal) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (complexify m.A)) :
    ∃ i j, ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] μ) (fun s => ‖transfer m s i j‖) := by
  by_contra hcon
  push Not at hcon
  set Ac := complexify m.A with hAc
  set Bc := complexify m.B with hBc
  set Cc := complexify m.C with hCc
  -- `P M`: every entry of `C M (sI − A)⁻¹ B` is bounded near `μ`
  let P : Matrix (Fin n) (Fin n) ℂ → Prop := fun M => ∀ i j,
    (fun s => (Cc * M * (characteristicMatrix m.A s)⁻¹ * Bc) i j) =O[𝓝[≠] μ] (fun _ => (1 : ℝ))
  have hP1 : P 1 := by
    intro i j
    have h1 := (hcon i j).isBigO_one ℝ
    have h2 : (fun _ : ℂ => complexify m.D i j) =O[𝓝[≠] μ] (fun _ => (1 : ℝ)) :=
      isBigO_const_one _ _ _
    refine (h1.sub h2).congr_left fun s => ?_
    simp [transfer, Matrix.add_apply, Cc, Bc]
  have hs : (fun s : ℂ => s) =O[𝓝[≠] μ] (fun _ => (1 : ℝ)) :=
    ((continuous_id.tendsto μ).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have hPmul : ∀ M, P M → P (M * Ac) := by
    intro M hM i j
    have hK : (fun _ : ℂ => (Cc * M * Bc) i j) =O[𝓝[≠] μ] (fun _ => (1 : ℝ)) :=
      isBigO_const_one _ _ _
    refine (((hs.mul (hM i j)).congr_right fun _ => mul_one (1 : ℝ)).sub hK).congr' ?_
      EventuallyEq.rfl
    filter_upwards [eventually_det_characteristicMatrix_ne_zero m.A μ] with s hdet
    have e : Cc * (M * Ac) * (characteristicMatrix m.A s)⁻¹ * Bc =
        s • (Cc * M * (characteristicMatrix m.A s)⁻¹ * Bc) - Cc * M * Bc := by
      calc Cc * (M * Ac) * (characteristicMatrix m.A s)⁻¹ * Bc
          = Cc * M * (Ac * (characteristicMatrix m.A s)⁻¹) * Bc := by
            simp only [Matrix.mul_assoc]
        _ = Cc * M * (s • (characteristicMatrix m.A s)⁻¹ - 1) * Bc := by
            rw [hAc, mul_resolvent hdet]
        _ = _ := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    simp only [e, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hPpoly : ∀ q : ℂ[X], P (aeval Ac q) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro i j
      rw [aeval_C, Algebra.algebraMap_eq_smul_one]
      refine ((hP1 i j).const_mul_left a).congr_left fun s => ?_
      simp [Matrix.mul_smul, Matrix.smul_mul]
    | add p q hp hq =>
      intro i j
      refine ((hp i j).add (hq i j)).congr_left fun s => ?_
      simp [map_add, Matrix.mul_add, Matrix.add_mul]
    | monomial k a ih =>
      have e : aeval Ac (C a * X ^ (k + 1)) = aeval Ac (C a * X ^ k) * Ac := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [e]
      exact hPmul _ ih
  -- `μ` is a root of the minimal polynomial `π = (X − μ) φ`
  have hroot : (minpoly ℂ Ac).IsRoot μ := by
    obtain ⟨w, hw, hAw⟩ := mem_spectrum_iff_exists_eigvec.mp hμ
    have h0 := mulVec_aeval_of_eigen hAw (minpoly ℂ Ac)
    rw [minpoly.aeval, Matrix.zero_mulVec] at h0
    by_contra hne
    exact hw ((smul_eq_zero.mp h0.symm).resolve_left hne)
  set φ := minpoly ℂ Ac /ₘ (X - C μ) with hφ
  have hfac : (X - C μ) * φ = minpoly ℂ Ac := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hφA : aeval Ac φ * Ac = μ • aeval Ac φ := by
    have h0 : aeval Ac (φ * (X - C μ)) = 0 := by rw [mul_comm, hfac]; exact minpoly.aeval ℂ Ac
    rw [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.mul_one, sub_eq_zero] at h0
    exact h0
  -- `C Aⁱ φ(A) Aʲ B = 0`: the bounded function `C Aⁱ φ(A) Aʲ (sI − A)⁻¹ B` is
  -- `(s − μ)⁻¹ C Aⁱ φ(A) Aʲ B`
  have hK : ∀ i j : ℕ, Cc * (Ac ^ i * aeval Ac φ * Ac ^ j) * Bc = 0 := by
    intro i j
    set Φ := Ac ^ i * aeval Ac φ * Ac ^ j with hΦ
    have hΦA : Φ * Ac = μ • Φ := by
      rw [hΦ, Matrix.mul_assoc, ← pow_succ, pow_succ', ← Matrix.mul_assoc,
        Matrix.mul_assoc (Ac ^ i), hφA, Matrix.mul_smul, Matrix.smul_mul]
    have hPΦ : P Φ := by
      have := hPpoly (X ^ i * φ * X ^ j)
      simpa [hΦ, map_mul, map_pow, aeval_X] using this
    ext a b
    refine eq_zero_of_isBigO_inv_sub ((hPΦ a b).congr' ?_ EventuallyEq.rfl)
    filter_upwards [eventually_det_characteristicMatrix_ne_zero m.A μ, self_mem_nhdsWithin]
      with s hdet hsμ
    rw [Matrix.mul_assoc Cc Φ, mul_resolvent_of_mul_eq hΦA hdet hsμ, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  -- observability: `φ(A) Aʲ B = 0`
  have hobs : ∀ j : ℕ, aeval Ac φ * Ac ^ j * Bc = 0 := by
    intro j
    ext a b
    have hv := eq_zero_of_isObservable hm.2
      (v := (aeval Ac φ * Ac ^ j * Bc) *ᵥ Pi.single b 1) fun i => by
        rw [Matrix.mulVec_mulVec]
        rw [show Cc * Ac ^ i * (aeval Ac φ * Ac ^ j * Bc) =
            Cc * (Ac ^ i * aeval Ac φ * Ac ^ j) * Bc by simp only [Matrix.mul_assoc], hK i j,
          Matrix.zero_mulVec]
    simpa [Matrix.mulVec_single_one] using congrFun hv a
  -- controllability: `φ(A) = 0`, contradicting the minimality of `π`
  have hφ0 : aeval Ac φ = 0 := eq_zero_of_isControllable hm.1 hobs
  have hπ0 : minpoly ℂ Ac ≠ 0 := minpoly.ne_zero_of_finite ℂ Ac
  have hφne : φ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hπ0 hfac.symm
  have hdeg := minpoly.degree_le_of_ne_zero ℂ Ac hφne hφ0
  have hlt : φ.degree < (minpoly ℂ Ac).degree :=
    degree_divByMonic_lt _ _ hπ0 (by rw [degree_X_sub_C]; exact zero_lt_one)
  exact absurd hdeg (not_le.mpr hlt)

/-- **Poles of a minimal realization are exactly the eigenvalues** (`T-small-signal-stability`
§1.9, general case): for a controllable and observable real realization `(A, B, C, D)`, some entry
of `G(s) = C (sI − A)⁻¹ B + D` is unbounded near `μ` iff `μ ∈ σ(A)`. -/
@[powerlib_foundation] theorem minimal_pole_iff {m : Plant n p} (hm : m.Minimal) (μ : ℂ) :
    (∃ i j, ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] μ) (fun s => ‖transfer m s i j‖)) ↔
      μ ∈ spectrum ℂ (complexify m.A) := by
  constructor
  · rintro ⟨i, j, h⟩
    by_contra hμ
    exact h (transfer_isBoundedUnder_of_not_mem_spectrum m hμ i j)
  · exact transfer_not_isBoundedUnder_of_mem_spectrum hm

/-- The pole set of the transfer matrix of a minimal realization is the spectrum of `A`. -/
@[powerlib_foundation] theorem minimal_poles_eq_spectrum {m : Plant n p} (hm : m.Minimal) :
    {μ | ∃ i j, ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] μ) (fun s => ‖transfer m s i j‖)} =
      spectrum ℂ (complexify m.A) :=
  Set.ext (minimal_pole_iff hm)

/-- The determinant of a matrix with entries analytic at `x` is analytic at `x`. -/
@[powerlib_foundation] theorem analyticAt_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℂ → Matrix ι ι ℂ} {x : ℂ} (h : ∀ a b, AnalyticAt ℂ (fun s => M s a b) x) :
    AnalyticAt ℂ (fun s => (M s).det) x := by
  have e : (fun s => (M s).det) = fun s =>
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i :=
    funext fun s => Matrix.det_apply' _
  rw [e]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

/-- The adjugate of a matrix with entries analytic at `x` has entries analytic at `x`. -/
@[powerlib_foundation] theorem analyticAt_adjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℂ → Matrix ι ι ℂ} {x : ℂ} (h : ∀ a b, AnalyticAt ℂ (fun s => M s a b) x) (i j : ι) :
    AnalyticAt ℂ (fun s => (M s).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  refine analyticAt_det fun a b => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact analyticAt_const
  · exact h a b

@[powerlib_foundation] theorem analyticAt_characteristicMatrix (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℂ) (a b : Fin n) :
    AnalyticAt ℂ (fun s => characteristicMatrix A s a b) x := by
  simp only [characteristicMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  exact (analyticAt_id.mul analyticAt_const).sub analyticAt_const

/-- Every entry of the transfer matrix is meromorphic at every `μ ∈ ℂ` (a rational function). -/
@[powerlib_foundation] theorem meromorphicAt_transfer (m : Plant n p) (μ : ℂ) (i j : Fin p) :
    MeromorphicAt (fun s => transfer m s i j) μ := by
  have hdet : AnalyticAt ℂ (fun s => (characteristicMatrix m.A s).det) μ :=
    analyticAt_det (analyticAt_characteristicMatrix m.A μ)
  have hN : AnalyticAt ℂ (fun s => (complexify m.C * (characteristicMatrix m.A s).adjugate *
      complexify m.B) i j) μ := by
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun k _ =>
      (Finset.analyticAt_fun_sum _ fun l _ => analyticAt_const.mul
        (analyticAt_adjugate (analyticAt_characteristicMatrix m.A μ) l k)).mul analyticAt_const
  have h := ((hdet.meromorphicAt.inv).mul hN.meromorphicAt).add
    (MeromorphicAt.const (complexify m.D i j) μ)
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp [transfer_eq_adjugate, Matrix.add_apply, Matrix.smul_apply]

/-- An unbounded entry of the transfer matrix tends to infinity: near `μ` a rational function is
either bounded (removable) or has a genuine pole (Mathlib `meromorphicOrderAt`). -/
@[powerlib_foundation] theorem tendsto_norm_transfer_of_not_isBoundedUnder (m : Plant n p) {μ : ℂ}
    {i j : Fin p}
    (h : ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] μ) (fun s => ‖transfer m s i j‖)) :
    Tendsto (fun s => ‖transfer m s i j‖) (𝓝[≠] μ) atTop := by
  have hmer := meromorphicAt_transfer m μ i j
  rcases lt_or_ge (meromorphicOrderAt (fun s => transfer m s i j) μ) 0 with ho | ho
  · exact tendsto_norm_atTop_iff_cobounded.mpr (tendsto_cobounded_of_meromorphicOrderAt_neg ho)
  · obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmer ho
    exact absurd hc.norm.isBoundedUnder_le h

/-- **Poles of a minimal realization, strong form**: `μ ∈ σ(A)` iff some entry satisfies
`‖G_ij(s)‖ → ∞` as `s → μ`, `s ≠ μ`. -/
@[powerlib_foundation] theorem minimal_pole_tendsto_iff {m : Plant n p} (hm : m.Minimal) (μ : ℂ) :
    (∃ i j, Tendsto (fun s => ‖transfer m s i j‖) (𝓝[≠] μ) atTop) ↔
      μ ∈ spectrum ℂ (complexify m.A) := by
  constructor
  · rintro ⟨i, j, h⟩
    exact (minimal_pole_iff hm μ).mp ⟨i, j, not_isBoundedUnder_of_tendsto_atTop h⟩
  · intro hμ
    obtain ⟨i, j, h⟩ := transfer_not_isBoundedUnder_of_mem_spectrum hm hμ
    exact ⟨i, j, tendsto_norm_transfer_of_not_isBoundedUnder m h⟩

/-- Minimality cannot be dropped: `hiddenMode` (`A = 1`, `B = C = D = 0`) has the eigenvalue `1`,
but its transfer function is identically zero, hence bounded near `1`. -/
@[powerlib_foundation] theorem hiddenMode_eigenvalue_not_pole :
    (1 : ℂ) ∈ spectrum ℂ (complexify hiddenMode.A) ∧
      ∀ i j, IsBoundedUnder (· ≤ ·) (𝓝[≠] (1 : ℂ)) (fun s => ‖transfer hiddenMode s i j‖) := by
  refine ⟨mem_spectrum_iff_exists_eigvec.mpr ⟨fun _ => 1, ?_, ?_⟩, fun i j => ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · ext k
    fin_cases k
    simp [hiddenMode, Matrix.mulVec, dotProduct]
  · have e : (fun s => ‖transfer hiddenMode s i j‖) = fun _ => 0 := by
      funext s
      simp [transfer, hiddenMode]
    rw [e]
    exact isBoundedUnder_const

end powerlib.Modal
