import dependencies.Mathlib
import theorem.Attributes

/-! # Multiplicative versus additive drive: discriminants, extended coordinates, amplitudes

Foundation layer: calculus and multilinear-algebra facts about a vector field `F(x, u)` on
`W = E × ℝ` with a scalar drive parameter `u` (state `x ∈ E`, any real normed space). No
engineering model is fixed here.

Results.
* Global discriminant (B) (`affine_in_drive_iff`): on a convex open domain `Ω`, with `F`
  differentiable and its drive derivative `∂_u F` differentiable,
  `F(x, u) = f₀(x) + u b` on `Ω` iff the derivative of `∂_u F` vanishes on `Ω`, i.e. all second
  partial derivatives with a `u` index (`f_xu`, `f_uu`) vanish identically.
* Discriminant (A) does not imply (B) (`quadratic_drive_counterexample`): `F = f₀(x) + u b + u² d`
  (`d ≠ 0`) has `∂_x ∂_u F = 0` but is not affine in `u`.
* Jet version at an operating point (`apply_const_of_driveFree`): if the `k`-th derivative
  tensor vanishes whenever one argument is a pure drive direction `(0, s)`, then
  `D^kF[δ, …, δ] = D^kF[(δx, 0), …, (δx, 0)]` for every `δ = (δx, δu)`: the Taylor terms of order
  `k ≥ 2` see only the state. An affine drive channel (`F = f₀(x) + u b`, `f₀` of class `C^k`)
  has drive-free tensors of every order `k ≥ 2` (`iteratedFDeriv_affine_driveFree`).
* Extended coordinates (`cx_extended_eq_additive`): in the four-term cross-saturation formula
  `c_x = ⟨ψ, D³[ṽ, χ̃, χ̃'] ⟩ + ⟨ψ, D²[χ̃, g₋]⟩ + ⟨ψ, D²[χ̃', g₊]⟩ + ⟨ψ, D²[ṽ, d₀]⟩`
  (`g₊ = R₊ D²[ṽ, χ̃']`, `g₋ = R₋ D²[ṽ, χ̃]`, `d₀ = −A⁻¹ D²[χ̃, χ̃']`, all resolvents on the
  state space, results re-embedded with zero drive component), drive-free tensors make the drive
  components of `χ̃ = (χ, 1)`, `χ̃' = (χ', 1)` irrelevant: the extended (multiplicative) value
  equals the additive one (`(χ, 0)`), exactly. This is the bit-exact oracle of an affine
  channel such as the dc-source current `I_dc`.
* Amplitude conventions: `u = a cos ωt = û e^{jωt} + û* e^{−jωt}` with `û = a/2`, `|û|² = a²/4`;
  the mean square over a period is `a²/2`; the erosion `α_eff = α − c_x a²/4` vanishes at the
  leading-order threshold `a*₍₂₎ = 2√(α/c_x)`; tone-wise erosion `c_x a²/4` is one half of
  `c_x` times the spectral mass `a²/2`.

Source: work-sync theory/T-multiplicative-drive-normal-form.md §1.1–1.5;
projects/basin-guard/notes/concepts/erosion-coefficients.md §1, §3, §4 (discriminants, `u²`
counterexample, extended coordinates, `I_dc` oracle), projects/basin-guard/notes/concepts/
guard-object.md §3 (`a*₍₂₎ = 2√(α/c_x)`).
-/

noncomputable section
namespace powerlib.NormalForm.MultiplicativeDrive

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Drive derivative `∂_u F(p) = DF(p)(0, 1)`. -/
def driveDeriv (F : E × ℝ → E) (p : E × ℝ) : E := fderiv ℝ F p (0, 1)

/-! ## Global discriminant (B) -/

/-- Along a horizontal line, the derivative of `u ↦ F(x, u)` is the drive derivative. -/
@[powerlib_foundation] theorem hasDerivAt_line {F : E × ℝ → E} {x : E} {u : ℝ}
    (hF : DifferentiableAt ℝ F (x, u)) :
    HasDerivAt (fun s : ℝ => F (x, s)) (driveDeriv F (x, u)) u := by
  have hl : HasDerivAt (fun s : ℝ => ((x, s) : E × ℝ)) ((0, 1) : E × ℝ) u :=
    (hasDerivAt_const u x).prodMk (hasDerivAt_id u)
  exact hF.hasFDerivAt.comp_hasDerivAt u hl

/-- Discriminant (B): on a convex open domain, `F` is affine in the drive with a
state-independent coefficient iff all second derivatives with a drive index vanish. -/
@[powerlib_foundation] theorem affine_in_drive_iff {F : E × ℝ → E} {Ω : Set (E × ℝ)}
    (hΩ : Convex ℝ Ω) (hΩo : IsOpen Ω) (hF : DifferentiableOn ℝ F Ω)
    (hg : DifferentiableOn ℝ (driveDeriv F) Ω) :
    (∃ f₀ : E → E, ∃ b : E, ∀ p ∈ Ω, F p = f₀ p.1 + p.2 • b) ↔
      ∀ p ∈ Ω, fderiv ℝ (driveDeriv F) p = 0 := by
  constructor
  · rintro ⟨f₀, b, hFb⟩ p hp
    -- `∂_u F = b` on `Ω`
    have hconst : ∀ q ∈ Ω, driveDeriv F q = b := by
      intro q hq
      have h1 := hasDerivAt_line (hF.differentiableAt (hΩo.mem_nhds hq)) (x := q.1) (u := q.2)
      have hev : (fun s : ℝ => F (q.1, s)) =ᶠ[𝓝 q.2] fun s => f₀ q.1 + s • b := by
        have : ∀ᶠ s in 𝓝 q.2, ((q.1, s) : E × ℝ) ∈ Ω :=
          (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
            (by simpa using hΩo.mem_nhds hq)
        filter_upwards [this] with s hs
        exact hFb _ hs
      have h2 : HasDerivAt (fun s : ℝ => f₀ q.1 + s • b) b q.2 := by
        simpa using ((hasDerivAt_id q.2).smul_const b).const_add (f₀ q.1)
      simpa using (h1.congr_of_eventuallyEq hev.symm).unique h2 |>.symm |> fun h => h.symm
    have hev : driveDeriv F =ᶠ[𝓝 p] fun _ => b := by
      filter_upwards [hΩo.mem_nhds hp] with q hq
      exact hconst q hq
    rw [hev.fderiv_eq]
    exact fderiv_const_apply b
  · intro h
    rcases Ω.eq_empty_or_nonempty with hempty | ⟨p₀, hp₀⟩
    · exact ⟨fun _ => 0, 0, by simp [hempty]⟩
    set b := driveDeriv F p₀
    -- `∂_u F` is constant on `Ω`
    have hgc : ∀ q ∈ Ω, driveDeriv F q = b := fun q hq =>
      hΩ.is_const_of_fderivWithin_eq_zero hg
        (fun r hr => by rw [fderivWithin_of_isOpen hΩo hr]; exact h r hr) hq hp₀
    -- `F(x, u) − u b` does not depend on `u` inside `Ω`
    have hind : ∀ q ∈ Ω, ∀ r ∈ Ω, q.1 = r.1 → F q - q.2 • b = F r - r.2 • b := by
      intro q hq r hr hx
      set S : Set ℝ := {s | ((q.1, s) : E × ℝ) ∈ Ω}
      have hSc : Convex ℝ S := by
        intro s hs t ht c d hc hd hcd
        have := hΩ hs ht hc hd hcd
        simp only [S, Set.mem_ofPred_eq] at this ⊢
        convert this using 1
        ext <;> simp [← add_smul, hcd]
      have hSo : IsOpen S := hΩo.preimage (continuous_const.prodMk continuous_id)
      have hd : ∀ s ∈ S, HasDerivAt (fun s : ℝ => F (q.1, s) - s • b) 0 s := by
        intro s hs
        have h1 := hasDerivAt_line (hF.differentiableAt (hΩo.mem_nhds hs)) (x := q.1) (u := s)
        rw [hgc _ hs] at h1
        have h3 := h1.sub ((hasDerivAt_id s).smul_const b)
        rw [one_smul, sub_self] at h3
        exact h3
      have hqS : q.2 ∈ S := by simpa [S] using hq
      have hrS : r.2 ∈ S := by simp only [S, Set.mem_ofPred_eq, hx]; simpa using hr
      have := hSc.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
        (f := fun s : ℝ => F (q.1, s) - s • b)
        (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
        (fun s hs => by
          rw [fderivWithin_of_isOpen hSo hs, (hd s hs).hasFDerivAt.fderiv]
          ext; simp) hqS hrS
      have e2 : ((q.1, r.2) : E × ℝ) = r := Prod.ext hx rfl
      change F (q.1, q.2) - q.2 • b = F (q.1, r.2) - r.2 • b at this
      rw [e2] at this
      exact this
    classical
    refine ⟨fun x => if hx : ∃ u, ((x, u) : E × ℝ) ∈ Ω then F (x, hx.choose) - hx.choose • b
      else 0, b, fun p hp => ?_⟩
    have hx : ∃ u, ((p.1, u) : E × ℝ) ∈ Ω := ⟨p.2, by simpa using hp⟩
    simp only [hx, ↓reduceDIte]
    have := hind (p.1, hx.choose) hx.choose_spec p hp rfl
    simp only at this
    rw [this]; abel

/-- Discriminant (A) does not imply (B): `F = f₀(x) + u b + u² d` with `d ≠ 0` has
`∂_x ∂_u F = 0` everywhere but is not of the form `f₀'(x) + u b'`. -/
@[powerlib_foundation] theorem quadratic_drive_counterexample {f₀ : E → E} (hf₀ : Differentiable ℝ f₀)
    (b d : E) (hd : d ≠ 0) :
    (∀ p : E × ℝ, ∀ w : E, fderiv ℝ (driveDeriv fun q : E × ℝ => f₀ q.1 + q.2 • b + q.2 ^ 2 • d)
        p (w, 0) = 0) ∧
      ¬ ∃ f₁ : E → E, ∃ b' : E, ∀ p : E × ℝ,
        f₀ p.1 + p.2 • b + p.2 ^ 2 • d = f₁ p.1 + p.2 • b' := by
  set F : E × ℝ → E := fun q => f₀ q.1 + q.2 • b + q.2 ^ 2 • d with hFdef
  have hFd : Differentiable ℝ F := by
    intro q
    have h1 : DifferentiableAt ℝ (fun q : E × ℝ => f₀ q.1) q :=
      (hf₀ q.1).comp q differentiableAt_fst
    have h2 : DifferentiableAt ℝ (fun q : E × ℝ => q.2 • b) q :=
      differentiableAt_snd.smul_const b
    have h3 : DifferentiableAt ℝ (fun q : E × ℝ => q.2 ^ 2 • d) q :=
      (differentiableAt_snd.pow 2).smul_const d
    exact (h1.add h2).add h3
  have hdd : driveDeriv F = fun q => b + (2 * q.2) • d := by
    funext q
    have h1 := hasDerivAt_line (hFd q) (x := q.1) (u := q.2)
    have h2 : HasDerivAt (fun s : ℝ => F (q.1, s)) (b + (2 * q.2) • d) q.2 := by
      have := (((hasDerivAt_id q.2).smul_const b).const_add (f₀ q.1)).add
        (((hasDerivAt_pow 2 q.2).smul_const d))
      exact this.congr_deriv (by simp)
    exact h1.unique h2
  refine ⟨fun p w => ?_, ?_⟩
  · rw [hdd]
    set L : E × ℝ →L[ℝ] E := (2 : ℝ) • (ContinuousLinearMap.snd ℝ E ℝ).smulRight d with hL
    have hfun : (fun q : E × ℝ => b + (2 * q.2) • d) = fun q => b + L q := by
      funext q; simp [hL, mul_smul]
    have hl : HasFDerivAt (fun q : E × ℝ => b + (2 * q.2) • d) L p := by
      rw [hfun]; exact L.hasFDerivAt.const_add b
    rw [hl.fderiv]
    simp [hL]
  · rintro ⟨f₁, b', h⟩
    have h1 := h (0, 1)
    have h2 := h (0, -1)
    have h3 := h (0, 0)
    simp only [one_smul, one_pow, neg_smul, even_two, Even.neg_pow, zero_smul, add_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1 h2 h3
    apply hd
    have : (2 : ℝ) • d = 0 := by
      have e : (2 : ℝ) • d = (f₀ 0 + b + d) + (f₀ 0 + -b + d) - 2 • f₀ 0 := by
        rw [two_smul, two_smul]; abel
      rw [e, h1, h2, h3]
      rw [two_smul]; abel
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero

/-! ## Jet version at an operating point -/

/-- A multilinear tensor on `E × ℝ` that vanishes whenever one argument is a pure drive vector
sees only the state components: `D[δ, …, δ] = D[(δx, 0), …, (δx, 0)]`. -/
@[powerlib_foundation] theorem apply_const_of_driveFree {k : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin k => E × ℝ) E)
    (hD : ∀ (m : Fin k → E × ℝ) (i : Fin k) (s : ℝ), m i = (0, s) → D m = 0) (δ : E × ℝ) :
    D (fun _ => δ) = D (fun _ => (δ.1, 0)) := by
  classical
  have hsplit : (fun _ : Fin k => δ) = (fun _ => ((δ.1, 0) : E × ℝ)) + fun _ => (0, δ.2) := by
    funext i; ext <;> simp
  rw [hsplit, D.map_add_univ]
  rw [Finset.sum_eq_single Finset.univ]
  · simp
  · intro s _ hs
    obtain ⟨i, hi⟩ : ∃ i, i ∉ s := by
      by_contra hc
      push Not at hc
      exact hs (Finset.eq_univ_iff_forall.mpr hc)
    exact hD _ i δ.2 (by simp [Finset.piecewise, hi])
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Iterated derivatives (`k ≥ 2`) of an affine drive channel `F(x, u) = f₀(x) + u b` see only the
state: `D^kF(p) = D^kf₀(p.1) ∘ (fst, …, fst)`. -/
@[powerlib_foundation] theorem iteratedFDeriv_affine {f₀ : E → E} {k : ℕ} (hf₀ : ContDiff ℝ k f₀)
    (b : E) (hk : 2 ≤ k) (p : E × ℝ) :
    iteratedFDeriv ℝ k (fun q : E × ℝ => f₀ q.1 + q.2 • b) p =
      (iteratedFDeriv ℝ k f₀ p.1).compContinuousLinearMap
        fun _ => ContinuousLinearMap.fst ℝ E ℝ := by
  have hlin : ContDiff ℝ k fun s : ℝ => s • b := contDiff_id.smul contDiff_const
  have h1 : (fun q : E × ℝ => f₀ q.1) = f₀ ∘ (ContinuousLinearMap.fst ℝ E ℝ) := rfl
  have h2 : (fun q : E × ℝ => q.2 • b) = (fun s : ℝ => s • b) ∘ (ContinuousLinearMap.snd ℝ E ℝ) :=
    rfl
  have hc1 : ContDiff ℝ k fun q : E × ℝ => f₀ q.1 := by rw [h1]; exact hf₀.comp (ContinuousLinearMap.fst ℝ E ℝ).contDiff
  have hc2 : ContDiff ℝ k fun q : E × ℝ => q.2 • b := by
    rw [h2]; exact hlin.comp (ContinuousLinearMap.snd ℝ E ℝ).contDiff
  have hsum : (fun q : E × ℝ => f₀ q.1 + q.2 • b) =
      (fun q : E × ℝ => f₀ q.1) + fun q : E × ℝ => q.2 • b := rfl
  rw [hsum, iteratedFDeriv_add hc1 hc2]
  have hzero : iteratedFDeriv ℝ k (fun q : E × ℝ => q.2 • b) p = 0 := by
    rw [h2, ContinuousLinearMap.iteratedFDeriv_comp_right _ hlin _ le_rfl]
    have : iteratedFDeriv ℝ k (fun s : ℝ => s • b) ((ContinuousLinearMap.snd ℝ E ℝ) p) = 0 := by
      refine ContinuousMultilinearMap.ext fun m => ?_
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : deriv (fun s : ℝ => s • b) = fun _ => b := by
        funext s; simpa using ((hasDerivAt_id s).smul_const b).deriv
      have hdd : deriv (fun _ : ℝ => b) = fun _ => (0 : E) := by funext s; simp
      rw [hd, hdd]
      simp
    rw [this]
    rfl
  rw [Pi.add_apply, hzero, add_zero, h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf₀ _ le_rfl]
  rfl

/-- An affine drive channel has drive-free derivative tensors of every order `k ≥ 2`. -/
@[powerlib_foundation] theorem iteratedFDeriv_affine_driveFree {f₀ : E → E} {k : ℕ}
    (hf₀ : ContDiff ℝ k f₀) (b : E) (hk : 2 ≤ k) (p : E × ℝ) (m : Fin k → E × ℝ) (i : Fin k)
    (s : ℝ) (hm : m i = (0, s)) :
    iteratedFDeriv ℝ k (fun q : E × ℝ => f₀ q.1 + q.2 • b) p m = 0 := by
  rw [iteratedFDeriv_affine hf₀ b hk p, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact (iteratedFDeriv ℝ k f₀ p.1).map_coord_zero i (by simp [hm])

/-! ## Extended coordinates: the four-term `c_x` formula -/

section Extended

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- A bilinear tensor on `V × 𝕜` vanishing on pure drive arguments only sees state parts. -/
@[powerlib_foundation] theorem bilin_state_only (B : V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V)
    (hB₁ : ∀ s w, B (0, s) w = 0) (hB₂ : ∀ w s, B w (0, s) = 0) (a c : V × 𝕜) :
    B a c = B (a.1, 0) (c.1, 0) := by
  have ha : a = (a.1, 0) + (0, a.2) := by ext <;> simp
  have hc : c = (c.1, 0) + (0, c.2) := by ext <;> simp
  rw [ha, map_add, LinearMap.add_apply, hB₁, add_zero, hc, map_add, hB₂, add_zero]
  simp

/-- The same for a trilinear tensor. -/
@[powerlib_foundation] theorem trilin_state_only
    (B : V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V)
    (hB₁ : ∀ s w z, B (0, s) w z = 0) (hB₂ : ∀ w s z, B w (0, s) z = 0)
    (hB₃ : ∀ w z s, B w z (0, s) = 0) (a c e : V × 𝕜) :
    B a c e = B (a.1, 0) (c.1, 0) (e.1, 0) := by
  have ha : a = (a.1, 0) + (0, a.2) := by ext <;> simp
  have hc : c = (c.1, 0) + (0, c.2) := by ext <;> simp
  have he : e = (e.1, 0) + (0, e.2) := by ext <;> simp
  rw [ha, map_add, LinearMap.add_apply, LinearMap.add_apply, hB₁, add_zero, hc, map_add,
    LinearMap.add_apply, hB₂, add_zero, he, map_add, hB₃, add_zero]
  simp

/-- The four-term cross-saturation formula with tensors on the extended space `V × 𝕜`
(resolvents act on the state space `V`; their results re-enter with zero drive component). -/
def cxFormula (B2 : V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V)
    (B3 : V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V) (ψ : V →ₗ[𝕜] 𝕜)
    (Rp Rm Ainv : V →ₗ[𝕜] V) (v χ χ' : V × 𝕜) : 𝕜 :=
  ψ (B3 v χ χ') + ψ (B2 χ (Rm (B2 v χ), 0)) + ψ (B2 χ' (Rp (B2 v χ'), 0)) +
    ψ (B2 v (-(Ainv (B2 χ χ')), 0))

/-- With drive-free tensors the extended (multiplicative) `c_x` with `χ̃ = (χ, 1)`,
`χ̃' = (χ', 1)` equals the additive one with `(χ, 0)`, `(χ', 0)`, exactly. -/
@[powerlib_foundation] theorem cx_extended_eq_additive (B2 : V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V)
    (B3 : V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V × 𝕜 →ₗ[𝕜] V)
    (h2₁ : ∀ s w, B2 (0, s) w = 0) (h2₂ : ∀ w s, B2 w (0, s) = 0)
    (h3₁ : ∀ s w z, B3 (0, s) w z = 0) (h3₂ : ∀ w s z, B3 w (0, s) z = 0)
    (h3₃ : ∀ w z s, B3 w z (0, s) = 0) (ψ : V →ₗ[𝕜] 𝕜) (Rp Rm Ainv : V →ₗ[𝕜] V)
    (v χ χ' : V) :
    cxFormula B2 B3 ψ Rp Rm Ainv (v, 0) (χ, 1) (χ', 1) =
      cxFormula B2 B3 ψ Rp Rm Ainv (v, 0) (χ, 0) (χ', 0) := by
  obtain ⟨B2x, hB2⟩ : ∃ B2x : V → V → V, ∀ a c, B2 a c = B2x a.1 c.1 :=
    ⟨fun x y => B2 (x, 0) (y, 0), fun a c => bilin_state_only B2 h2₁ h2₂ a c⟩
  obtain ⟨B3x, hB3⟩ : ∃ B3x : V → V → V → V, ∀ a c e, B3 a c e = B3x a.1 c.1 e.1 :=
    ⟨fun x y z => B3 (x, 0) (y, 0) (z, 0), fun a c e => trilin_state_only B3 h3₁ h3₂ h3₃ a c e⟩
  simp only [cxFormula, hB2, hB3]

end Extended

/-! ## Amplitude conventions -/

/-- `a cos θ = û e^{jθ} + û* e^{−jθ}` with `û = a/2`, and `|û|² = a²/4`. -/
@[powerlib_foundation] theorem tone_coefficient (a θ : ℝ) :
    ((a * Real.cos θ : ℝ) : ℂ) = (a / 2 : ℂ) * Complex.exp (θ * Complex.I) +
        (starRingEnd ℂ) (a / 2 : ℂ) * Complex.exp (-(θ * Complex.I)) ∧
      ‖(a / 2 : ℂ)‖ ^ 2 = a ^ 2 / 4 := by
  constructor
  · have h1 : Complex.exp (θ * Complex.I) = Complex.cos θ + Complex.sin θ * Complex.I :=
      Complex.exp_mul_I θ
    have h2 : Complex.exp (-(θ * Complex.I)) = Complex.cos θ - Complex.sin θ * Complex.I := by
      rw [show -((θ : ℂ) * Complex.I) = (-(θ : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg]; ring
    rw [h1, h2, show (starRingEnd ℂ) (a / 2 : ℂ) = (a / 2 : ℂ) by
      rw [map_div₀, Complex.conj_ofReal, map_ofNat]]
    push_cast; ring
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    norm_num

/-- The mean square of a single tone over one period is `a²/2`. -/
@[powerlib_foundation] theorem tone_meanSquare (a : ℝ) {ω T : ℝ} (hT : 0 < T)
    (hωT : ω * T = 2 * Real.pi) :
    (1 / T) * ∫ t in (0 : ℝ)..T, (a * Real.cos (ω * t)) ^ 2 = a ^ 2 / 2 := by
  have hω : ω ≠ 0 := by
    intro h; rw [h, zero_mul] at hωT; linarith [Real.pi_pos]
  have hcos : ∀ t, (a * Real.cos (ω * t)) ^ 2 = a ^ 2 / 2 + a ^ 2 / 2 * Real.cos (2 * (ω * t)) := by
    intro t; rw [Real.cos_two_mul]; ring
  simp_rw [hcos]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  have hint : ∫ t in (0 : ℝ)..T, Real.cos (2 * (ω * t)) = 0 := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := T)
      (fun t => Real.cos t) (c := 2 * ω) (by positivity)
    simp only [mul_zero] at h
    rw [show (fun t => Real.cos (2 * (ω * t))) = fun t => Real.cos (2 * ω * t) by
      funext t; ring_nf, h, integral_cos, show 2 * ω * T = ((4 : ℕ) : ℝ) * Real.pi by
        rw [mul_assoc, hωT]; push_cast; ring,
      Real.sin_zero, sub_zero, Real.sin_nat_mul_pi]
    simp
  rw [hint, mul_zero, add_zero, smul_eq_mul, sub_zero]
  field_simp

/-- The leading-order background threshold: `α − c_x a²/4 = 0` with `a ≥ 0` iff
`a = a*₍₂₎ = 2√(α/c_x)` (`α ≥ 0`, `c_x > 0`); below it the erosion keeps `α_eff > 0`. -/
@[powerlib_foundation] theorem erosion_threshold {α cx a : ℝ} (hα : 0 ≤ α) (hc : 0 < cx)
    (ha : 0 ≤ a) :
    (α - cx * a ^ 2 / 4 = 0 ↔ a = 2 * √(α / cx)) ∧
      (a < 2 * √(α / cx) → 0 < α - cx * a ^ 2 / 4 ∨ α = 0 ∧ a = 0) := by
  have hs : √(α / cx) ^ 2 = α / cx := Real.sq_sqrt (div_nonneg hα hc.le)
  have hs0 := Real.sqrt_nonneg (α / cx)
  have key : α - cx * a ^ 2 / 4 = cx / 4 * ((2 * √(α / cx)) ^ 2 - a ^ 2) := by
    rw [mul_pow, hs]; field_simp; ring
  constructor
  · rw [key]
    constructor
    · intro h
      have h1 : (2 * √(α / cx)) ^ 2 - a ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · linarith
        · exact h
      have h2 : (2 * √(α / cx) - a) * (2 * √(α / cx) + a) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · linarith
      · nlinarith
    · intro h; rw [h]; ring
  · intro hlt
    left
    rw [key]
    apply mul_pos (by positivity)
    nlinarith

/-- Multi-tone bookkeeping: the tone-wise erosion `Σ c_k a_k²/4` is one half of
`Σ c_k · (a_k²/2)`, the latter being `c` weighted by the spectral mass `a_k²/2` of each tone. -/
@[powerlib_foundation] theorem multitone_erosion {ι : Type*} (s : Finset ι) (α : ℝ)
    (c a : ι → ℝ) :
    α - ∑ k ∈ s, c k * a k ^ 2 / 4 = α - 1 / 2 * ∑ k ∈ s, c k * (a k ^ 2 / 2) := by
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end powerlib.NormalForm.MultiplicativeDrive
