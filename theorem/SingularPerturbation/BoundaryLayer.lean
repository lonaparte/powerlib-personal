import theorem.SingularPerturbation.FiniteHorizon

/-! # Nonlinear boundary layer: exponential stability uniform in the frozen slow variables

Foundation layer (category B).

Sources: work-sync `theory/T-tikhonov.md` §1.1–§1.2 (Tikhonov hypothesis: the boundary-layer
system `dz/dτ = g(t, x, z)` is exponentially stable at `z = h(t, x)` uniformly in `(t, x)`;
linearized form `Re λ(∂g/∂z) < 0`), `theory/T-singular-perturbation.md` §1.4,
`theory/T-slow-manifold.md` §1.5 (attractivity uniform in `x`).

Model boundary. A parameter space `X` (the frozen slow variables `p = (t, x)`, e.g. a compact
time interval times a compact set of slow states, with the product topology) assumed compact;
the frozen boundary-layer field `g p : ℝᵐ → ℝᵐ` in the fast time `τ` (no `ε`, the slow variables
are frozen); an equilibrium branch `h p`; the Jacobian at the equilibrium `A p = ∂g/∂z (p, h p)`
continuous in `p` and Hurwitz for every `p`. Forward solutions are Mathlib integral curves on
`[0, ∞)` (`IsIntegralCurveOn y (fun _ v => g p v) (Ici 0)`, one-sided at `τ = 0`); no existence
claim is made. `|v|² = v ⬝ᵥ v`, `‖·‖` is the sup norm of `Fin m → ℝ`.

Results.
* `exists_uniform_dissipation`: one pair of energy bounds `lo, hi` and one bound on `Σ|Pᵢⱼ|`
  serve all parameters: for every `p` there is a symmetric `P` with `lo|v|² ≤ vᵀPv ≤ hi|v|²` and
  `vᵀ P A(p) v ≤ −|v|²/4` (finite subcover of the certificates of `FrozenFast`, via
  `dissipation_of_close`).
* `boundaryLayer_uniform_exponentialStability_of_certificates`: the same conclusion for an
  arbitrary (not necessarily compact or topological) parameter set, given uniform Lyapunov
  certificates of the linearizations as a hypothesis (Khalil's uniform form: one `lo`, `hi`, one
  bound on `Σ|Pᵢⱼ|`, `vᵀ P A(p) v ≤ −|v|²/4`).
* `boundaryLayer_uniform_exponentialStability`: under the uniform linearization hypothesis
  `∀ κ > 0, ∃ ρ > 0, ∀ p w, |w|² ≤ ρ → |g p (h p + w) − A p w|² ≤ κ |w|²`, there are
  `r, C, α > 0`, independent of `p`, such that every forward solution with `|y(0) − h p|² < r`
  satisfies `|y(τ) − h p|² ≤ C e^{−ατ} |y(0) − h p|²` for all `τ ≥ 0` (uniform local exponential
  stability; `C = hi/lo`, `α = 1/(8 hi)`, `r = lo ρ/hi`). The proof is a barrier argument
  (Mathlib `image_le_of_deriv_right_lt_deriv_boundary`) for `V = wᵀPw`, which keeps the
  solution in the region where the linearization dominates.
* `uniform_linearization_of_jacobian`, `boundaryLayer_uniform_exponentialStability_of_jacobian`:
  the hypothesis follows from a Jacobian `J p z = ∂g/∂z (p, z)` (`HasFDerivAt (g p) (J p z) z`)
  equal to `A p` at `h p` and uniformly continuous there
  (`∀ κ > 0, ∃ ρ > 0, ∀ p z, ‖z − h p‖ ≤ ρ → ‖J p z − J p (h p)‖ ≤ κ`), by the mean value
  inequality; this is the nonlinear, uniform-in-`(t, x)` version of the frozen linearized
  statement `uniform_frozen_exponentialStability`.
* `uniform_jacobian_of_lipschitz`: a Jacobian Lipschitz at the equilibrium with one constant `L`
  (`‖J p z − J p (h p)‖ ≤ L ‖z − h p‖`) satisfies that uniform continuity hypothesis.
* `boundaryLayer_uniform_exponentialStability_tx`: the Tikhonov hypothesis in its `(t, x)` form —
  `g(t, x, ·)` with `(t, x)` frozen in a compact `S ⊆ ℝ × ℝⁿ`, `g(t, x, h(t, x)) = 0`,
  `∂g/∂z(t, x, h(t, x)) = A(t, x)` continuous and Hurwitz on `S`, Jacobian Lipschitz at `h` with
  one constant: one `r, C, α` serve every `(t, x) ∈ S`.

Excluded: the full Tikhonov approximation theorem for the nonlinear slow–fast system (only its
boundary-layer hypothesis is established here), global (non-local) stability, existence of
solutions; on non-compact parameter sets only the certificate form is provided (deriving uniform
certificates from a uniform spectral bound `Re λ(A(p)) ≤ −c` with `‖A(p)‖` bounded needs the
continuity of eigenvalues, not formalized here).

Architecture: generic mathematical support (no `Family`, no definitions); every statement is
about an arbitrary parametrized field, so the results are public foundation.
-/

noncomputable section
namespace powerlib.SingularPerturbation
open Matrix Set

variable {m : ℕ}

/-- Right derivative of `yᵀ P y` for symmetric `P`. -/
@[powerlib_foundation] theorem hasDerivWithinAt_quadratic_of_symm {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P)
    {y : ℝ → Fin m → ℝ} {dy : Fin m → ℝ} {s : Set ℝ} {t : ℝ}
    (hy : HasDerivWithinAt y dy s t) :
    HasDerivWithinAt (fun τ => y τ ⬝ᵥ (P *ᵥ y τ)) (2 * (y t ⬝ᵥ (P *ᵥ dy))) s t := by
  have hPy : HasDerivWithinAt (fun τ => P *ᵥ y τ) (P *ᵥ dy) s t :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' P)).hasFDerivAt.comp_hasDerivWithinAt t hy
  convert Linear.dotProduct_hasDerivWithinAt hy hPy using 1
  rw [Criteria.dotProduct_mulVec_comm_of_symm hP dy (y t)]
  ring

/-- **Uniform Lyapunov dissipation** for a continuous Hurwitz family on a compact parameter
space: one pair of constants `lo, hi` and one bound `Pb` serve every parameter. -/
@[powerlib_foundation] theorem exists_uniform_dissipation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {A : X → Matrix (Fin m) (Fin m) ℝ} (hA : Continuous A)
    (hH : ∀ p, LinearSystems.IsHurwitz (A p)) :
    ∃ lo > 0, ∃ hi > 0, ∃ Pb ≥ 0, ∀ p, ∃ P : Matrix (Fin m) (Fin m) ℝ, Pᵀ = P ∧
      (∀ v, lo * (v ⬝ᵥ v) ≤ v ⬝ᵥ (P *ᵥ v)) ∧ (∀ v, v ⬝ᵥ (P *ᵥ v) ≤ hi * (v ⬝ᵥ v)) ∧
      absSum P ≤ Pb ∧ ∀ v, v ⬝ᵥ (P *ᵥ (A p *ᵥ v)) ≤ -(v ⬝ᵥ v) / 4 := by
  classical
  let cert : ∀ x, BoundedCertificate (A x) := fun x =>
    (nonempty_boundedCertificate_of_isHurwitz (hH x)).some
  let δ : X → ℝ := fun x => 1 / (4 * absSum (cert x).P + 4)
  have hδ : ∀ x, 0 < δ x := fun x => by have := absSum_nonneg (cert x).P; positivity
  let O : X → Set X := fun x₀ => {x | absSum (A x - A x₀) < δ x₀}
  have hO : ∀ x₀, IsOpen (O x₀) := fun x₀ =>
    isOpen_lt ((continuous_absSum_sub (A x₀)).comp hA) continuous_const
  have hcover : (Set.univ : Set X) ⊆ ⋃ x₀, O x₀ := fun x _ =>
    Set.mem_iUnion.mpr ⟨x, by simp [O, absSum, hδ x]⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  by_cases hX : Nonempty X
  swap
  · exact ⟨1, one_pos, 1, one_pos, 0, le_rfl, fun x => absurd ⟨x⟩ hX⟩
  have hsne : s.Nonempty := by
    obtain ⟨x⟩ := hX
    obtain ⟨x₀, hx₀, -⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨x₀, hx₀⟩
  refine ⟨s.inf' hsne fun x₀ => (cert x₀).lower, ?_, s.sup' hsne fun x₀ => (cert x₀).upper, ?_,
    s.sup' hsne fun x₀ => absSum (cert x₀).P, ?_, fun p => ?_⟩
  · show 0 < _
    rw [Finset.lt_inf'_iff]
    exact fun x₀ _ => (cert x₀).lower_pos
  · obtain ⟨x₀, hx₀⟩ := hsne
    exact lt_of_lt_of_le (cert x₀).upper_pos
      (Finset.le_sup' (fun x₀ => (cert x₀).upper) hx₀)
  · obtain ⟨x₀, hx₀⟩ := hsne
    exact le_trans (absSum_nonneg _) (Finset.le_sup' (fun x₀ => absSum (cert x₀).P) hx₀)
  obtain ⟨x₀, hx₀s, hxO⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
  refine ⟨(cert x₀).P, (cert x₀).symmetric, fun v => ?_, fun v => ?_,
    Finset.le_sup' (fun x₀ => absSum (cert x₀).P) hx₀s,
    dissipation_of_close (cert x₀) (le_of_lt hxO)⟩
  · have h1 := Finset.inf'_le (fun x₀ => (cert x₀).lower) hx₀s
    have h2 := (cert x₀).lower_bound v
    have h3 := dotProduct_self_nonneg' v
    nlinarith
  · have h1 := Finset.le_sup' (fun x₀ => (cert x₀).upper) hx₀s
    have h2 := (cert x₀).upper_bound v
    have h3 := dotProduct_self_nonneg' v
    nlinarith

/-- **Nonlinear boundary layer, uniform Lyapunov certificates** (no compactness): if one pair of
energy bounds `lo, hi` and one bound `Pb` on `Σ|Pᵢⱼ|` serve a dissipation certificate of every
linearization `A p` (Khalil's uniform form of the hypothesis), the boundary layer is locally
exponentially stable uniformly in `p`, with `r = lo ρ/hi`, `C = hi/lo`, `α = 1/(8 hi)`. -/
@[powerlib_foundation] theorem boundaryLayer_uniform_exponentialStability_of_certificates
    {X : Type*} {A : X → Matrix (Fin m) (Fin m) ℝ} {lo hi Pb : ℝ} (hlo : 0 < lo) (hhi : 0 < hi)
    (hPb : 0 ≤ Pb)
    (hcert : ∀ p, ∃ P : Matrix (Fin m) (Fin m) ℝ, Pᵀ = P ∧
      (∀ v, lo * (v ⬝ᵥ v) ≤ v ⬝ᵥ (P *ᵥ v)) ∧ (∀ v, v ⬝ᵥ (P *ᵥ v) ≤ hi * (v ⬝ᵥ v)) ∧
      absSum P ≤ Pb ∧ ∀ v, v ⬝ᵥ (P *ᵥ (A p *ᵥ v)) ≤ -(v ⬝ᵥ v) / 4)
    {g : X → (Fin m → ℝ) → Fin m → ℝ} {h : X → Fin m → ℝ}
    (hlin : ∀ κ > 0, ∃ ρ > 0, ∀ p w, w ⬝ᵥ w ≤ ρ →
      (g p (h p + w) - A p *ᵥ w) ⬝ᵥ (g p (h p + w) - A p *ᵥ w) ≤ κ * (w ⬝ᵥ w)) :
    ∃ r > 0, ∃ C > 0, ∃ α > 0, ∀ p (y : ℝ → Fin m → ℝ),
      IsIntegralCurveOn y (fun _ v => g p v) (Ici 0) →
      (y 0 - h p) ⬝ᵥ (y 0 - h p) < r → ∀ τ, 0 ≤ τ →
        (y τ - h p) ⬝ᵥ (y τ - h p) ≤ C * Real.exp (-(α * τ)) * ((y 0 - h p) ⬝ᵥ (y 0 - h p)) := by
  set δ : ℝ := 1 / (8 * (Pb + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨ρ, hρ, hrem⟩ := hlin (δ ^ 2) (by positivity)
  set β : ℝ := 1 / (8 * hi) with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨lo * ρ / hi, by positivity, hi / lo, by positivity, β, hβpos, ?_⟩
  intro p y hy hy0 τ hτ
  obtain ⟨P, hPs, hPlo, hPhi, hPabs, hdiss⟩ := hcert p
  -- the dissipation inequality near the equilibrium
  have hloc : ∀ w : Fin m → ℝ, w ⬝ᵥ w ≤ ρ →
      2 * (w ⬝ᵥ (P *ᵥ g p (h p + w))) ≤ -(w ⬝ᵥ w) / 4 := by
    intro w hw
    set r := g p (h p + w) - A p *ᵥ w with hr
    have hg : g p (h p + w) = A p *ᵥ w + r := by rw [hr]; abel
    rw [hg, mulVec_add, dotProduct_add]
    have h1 := hdiss w
    have h2 := le_of_abs_le (abs_dotProduct_mulVec_le P w r hδpos)
    have h3 := hrem p w hw
    have hww := dotProduct_self_nonneg' w
    have hPa := absSum_nonneg P
    -- `|P|₁ (δ|w|² + |r|²/δ)/2 ≤ |w|²/8`
    have h4 : (r ⬝ᵥ r) / δ ≤ δ * (w ⬝ᵥ w) := by
      rw [div_le_iff₀ hδpos]; nlinarith
    have h5 : absSum P * (δ * (w ⬝ᵥ w) + (r ⬝ᵥ r) / δ) / 2 ≤ absSum P * δ * (w ⬝ᵥ w) := by
      have := mul_le_mul_of_nonneg_left h4 hPa
      nlinarith
    have h6 : absSum P * δ ≤ 1 / 8 := by
      rw [hδ, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h7 : absSum P * δ * (w ⬝ᵥ w) ≤ 1 / 8 * (w ⬝ᵥ w) :=
      mul_le_mul_of_nonneg_right h6 hww
    linarith
  -- the Lyapunov function along the solution
  set w : ℝ → Fin m → ℝ := fun s => y s - h p with hw
  set V : ℝ → ℝ := fun s => w s ⬝ᵥ (P *ᵥ w s) with hV
  have hwd : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (g p (h p + w s)) (Ici 0) s := by
    intro s hs
    have := (hy s hs).sub_const (h p)
    simpa [hw] using this
  have hVd : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt V (2 * (w s ⬝ᵥ (P *ᵥ g p (h p + w s))))
      (Ici 0) s := fun s hs => hasDerivWithinAt_quadratic_of_symm hPs (hwd s hs)
  have hVc : ContinuousOn V (Ici 0) := fun s hs => (hVd s hs).continuousWithinAt
  set V0 := V 0 with hV0
  have hV0r : V0 < lo * ρ := by
    have := hPhi (w 0)
    have h' : hi * (w 0 ⬝ᵥ w 0) < hi * (lo * ρ / hi) := mul_lt_mul_of_pos_left hy0 hhi
    rw [mul_div_cancel₀ _ hhi.ne'] at h'
    exact lt_of_le_of_lt this h'
  have hV00 : 0 ≤ V0 := le_trans (mul_nonneg hlo.le (dotProduct_self_nonneg' _)) (hPlo (w 0))
  -- barrier: `V ≤ (V0 + s) e^{-βτ}` for every small slack `s > 0`
  have hbar : ∀ s, 0 < s → V0 + s < lo * ρ → V τ ≤ (V0 + s) * Real.exp (-(β * τ)) := by
    intro s hs hsρ
    have hB : ∀ x, HasDerivAt (fun x => (V0 + s) * Real.exp (-(β * x)))
        ((V0 + s) * (Real.exp (-(β * x)) * (-β))) x := by
      intro x
      have := ((hasDerivAt_id x).const_mul β).neg.exp.const_mul (V0 + s)
      simpa using this
    have key := image_le_of_deriv_right_lt_deriv_boundary (a := 0) (b := τ)
      (f := V) (hVc.mono Icc_subset_Ici_self)
      (fun x hx => (hVd x hx.1).mono (Ici_subset_Ici.mpr hx.1))
      (by simp only [hV0, mul_zero, neg_zero, Real.exp_zero, mul_one]; linarith) hB
      (fun x hx hfx => by
        have hx0 : 0 ≤ x := hx.1
        have hBpos : 0 < (V0 + s) * Real.exp (-(β * x)) := by positivity
        have hBle : (V0 + s) * Real.exp (-(β * x)) ≤ V0 + s := by
          have : Real.exp (-(β * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          nlinarith
        have hwx : w x ⬝ᵥ w x ≤ ρ := by
          have h1 := hPlo (w x)
          have h2 : lo * (w x ⬝ᵥ w x) < lo * ρ := by
            change lo * (w x ⬝ᵥ w x) ≤ V x at h1
            linarith
          exact (lt_of_mul_lt_mul_left h2 hlo.le).le
        have hd := hloc (w x) hwx
        have hup := hPhi (w x)
        change V x = _ at hfx
        have hVx : V x ≤ hi * (w x ⬝ᵥ w x) := hup
        -- `V' ≤ -|w|²/4 ≤ -2β V = -2β B < -β B`
        have h2b : -(w x ⬝ᵥ w x) / 4 ≤ -(2 * β) * V x := by
          rw [hβ]
          have : V x / (4 * hi) ≤ (w x ⬝ᵥ w x) / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
          have e : -(2 * (1 / (8 * hi))) * V x = -(V x / (4 * hi)) := by field_simp; ring
          rw [e]; linarith
        rw [hfx] at h2b
        nlinarith)
    exact key ⟨hτ, le_rfl⟩
  have hVτ : V τ ≤ V0 * Real.exp (-(β * τ)) := by
    have hgap : 0 < lo * ρ - V0 := by linarith
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set s := min ε ((lo * ρ - V0) / 2) with hs
    have hspos : 0 < s := lt_min hε (by linarith)
    have hsρ : V0 + s < lo * ρ := by
      have : s ≤ (lo * ρ - V0) / 2 := min_le_right _ _
      linarith
    have h1 := hbar s hspos hsρ
    have hexp : Real.exp (-(β * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : s * Real.exp (-(β * τ)) ≤ ε := by
      calc s * Real.exp (-(β * τ)) ≤ s * 1 := by gcongr
        _ ≤ ε := by rw [mul_one]; exact min_le_left _ _
    linarith
  -- back to `|w|²`
  have hlow := hPlo (w τ)
  have hup0 := hPhi (w 0)
  change lo * (w τ ⬝ᵥ w τ) ≤ V τ at hlow
  change V 0 ≤ hi * (w 0 ⬝ᵥ w 0) at hup0
  change w τ ⬝ᵥ w τ ≤ hi / lo * Real.exp (-(β * τ)) * (w 0 ⬝ᵥ w 0)
  have hE := Real.exp_pos (-(β * τ))
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hlo]
  calc w τ ⬝ᵥ w τ * lo = lo * (w τ ⬝ᵥ w τ) := mul_comm _ _
    _ ≤ V0 * Real.exp (-(β * τ)) := hlow.trans hVτ
    _ ≤ hi * (w 0 ⬝ᵥ w 0) * Real.exp (-(β * τ)) := by
        rw [hV0]; exact mul_le_mul_of_nonneg_right hup0 hE.le
    _ = hi * Real.exp (-(β * τ)) * (w 0 ⬝ᵥ w 0) := by ring

/-- **Nonlinear boundary layer: uniform local exponential stability** over a compact parameter
space with a continuous Hurwitz linearization (the certificates of
`boundaryLayer_uniform_exponentialStability_of_certificates` come from
`exists_uniform_dissipation`). -/
@[powerlib_foundation] theorem boundaryLayer_uniform_exponentialStability {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {A : X → Matrix (Fin m) (Fin m) ℝ} (hA : Continuous A)
    (hH : ∀ p, LinearSystems.IsHurwitz (A p)) {g : X → (Fin m → ℝ) → Fin m → ℝ}
    {h : X → Fin m → ℝ}
    (hlin : ∀ κ > 0, ∃ ρ > 0, ∀ p w, w ⬝ᵥ w ≤ ρ →
      (g p (h p + w) - A p *ᵥ w) ⬝ᵥ (g p (h p + w) - A p *ᵥ w) ≤ κ * (w ⬝ᵥ w)) :
    ∃ r > 0, ∃ C > 0, ∃ α > 0, ∀ p (y : ℝ → Fin m → ℝ),
      IsIntegralCurveOn y (fun _ v => g p v) (Ici 0) →
      (y 0 - h p) ⬝ᵥ (y 0 - h p) < r → ∀ τ, 0 ≤ τ →
        (y τ - h p) ⬝ᵥ (y τ - h p) ≤ C * Real.exp (-(α * τ)) * ((y 0 - h p) ⬝ᵥ (y 0 - h p)) := by
  obtain ⟨lo, hlo, hi, hhi, Pb, hPb, hcert⟩ := exists_uniform_dissipation hA hH
  exact boundaryLayer_uniform_exponentialStability_of_certificates hlo hhi hPb hcert hlin

/-- `|v|² ≤ m ‖v‖²` (sup norm). -/
@[powerlib_foundation] theorem dotProduct_self_le_card_mul_norm_sq (v : Fin m → ℝ) : v ⬝ᵥ v ≤ m * ‖v‖ ^ 2 := by
  have h : ∀ i, v i * v i ≤ ‖v‖ ^ 2 := fun i => by
    have h1 : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    have h2 := abs_nonneg (v i)
    nlinarith [abs_mul_abs_self (v i)]
  calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
    _ ≤ ∑ _i : Fin m, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = m * ‖v‖ ^ 2 := by simp

/-- `‖v‖² ≤ |v|²` (sup norm). -/
@[powerlib_foundation] theorem norm_sq_le_dotProduct_self (v : Fin m → ℝ) : ‖v‖ ^ 2 ≤ v ⬝ᵥ v := by
  have hs : ‖v‖ ≤ Real.sqrt (v ⬝ᵥ v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have : v i ^ 2 = v i * v i := sq _
    rw [this]
    exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have h0 := norm_nonneg v
  calc ‖v‖ ^ 2 ≤ Real.sqrt (v ⬝ᵥ v) ^ 2 := pow_le_pow_left₀ h0 hs 2
    _ = v ⬝ᵥ v := Real.sq_sqrt (dotProduct_self_nonneg' v)

/-- The uniform linearization hypothesis of `boundaryLayer_uniform_exponentialStability` follows
from a Jacobian `J p z = ∂g/∂z (p, z)` that is uniformly continuous at the equilibrium. -/
@[powerlib_foundation] theorem uniform_linearization_of_jacobian {X : Type*} {A : X → Matrix (Fin m) (Fin m) ℝ}
    {g : X → (Fin m → ℝ) → Fin m → ℝ} {h : X → Fin m → ℝ}
    {J : X → (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)}
    (heq : ∀ p, g p (h p) = 0) (hJ : ∀ p z, HasFDerivAt (g p) (J p z) z)
    (hJA : ∀ p v, J p (h p) v = A p *ᵥ v)
    (hunif : ∀ κ > 0, ∃ ρ > 0, ∀ p z, ‖z - h p‖ ≤ ρ → ‖J p z - J p (h p)‖ ≤ κ) :
    ∀ κ > 0, ∃ ρ > 0, ∀ p w, w ⬝ᵥ w ≤ ρ →
      (g p (h p + w) - A p *ᵥ w) ⬝ᵥ (g p (h p + w) - A p *ᵥ w) ≤ κ * (w ⬝ᵥ w) := by
  intro κ hκ
  set κ' := min 1 (κ / (m + 1)) with hκ'
  have hκ'pos : 0 < κ' := lt_min one_pos (by positivity)
  obtain ⟨ρ, hρ, hJρ⟩ := hunif κ' hκ'pos
  refine ⟨ρ ^ 2, by positivity, fun p w hw => ?_⟩
  have hwn : ‖w‖ ≤ ρ := by
    have := (norm_sq_le_dotProduct_self w).trans hw
    exact (pow_le_pow_iff_left₀ (norm_nonneg w) hρ.le two_ne_zero).1 this
  -- mean value inequality for `f z = g z − J(h)(z − h)` on the closed ball
  set L := J p (h p) with hL
  let f : (Fin m → ℝ) → Fin m → ℝ := fun z => g p z - L (z - h p)
  have hf : ∀ z ∈ Metric.closedBall (h p) ρ,
      HasFDerivWithinAt f (J p z - L) (Metric.closedBall (h p) ρ) z := by
    intro z _
    have h1 : HasFDerivAt (fun z => L (z - h p)) L z := by
      simpa using L.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (h p))
    exact ((hJ p z).sub h1).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall (h p) ρ, ‖J p z - L‖ ≤ κ' := by
    intro z hz
    exact hJρ p z (by simpa [dist_eq_norm] using hz)
  have hmv := (convex_closedBall (h p) ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hf hbound
    (Metric.mem_closedBall_self hρ.le)
    (show h p + w ∈ Metric.closedBall (h p) ρ by simpa [dist_eq_norm] using hwn)
  have hr : f (h p + w) - f (h p) = g p (h p + w) - A p *ᵥ w := by
    simp [f, heq, hJA, hL]
  rw [hr, add_sub_cancel_left] at hmv
  -- back to the dot product
  set r := g p (h p + w) - A p *ᵥ w
  have h1 := dotProduct_self_le_card_mul_norm_sq r
  have h2 : ‖r‖ ^ 2 ≤ κ' ^ 2 * ‖w‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg r) hmv 2
  have h3 := norm_sq_le_dotProduct_self w
  have hκ'1 : κ' ≤ 1 := min_le_left _ _
  have hκ'2 : κ' ≤ κ / (m + 1) := min_le_right _ _
  have hκsq : (m : ℝ) * κ' ^ 2 ≤ κ := by
    have : κ' ^ 2 ≤ κ' := by nlinarith
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc (m : ℝ) * κ' ^ 2 ≤ m * (κ / (m + 1)) := by
          apply mul_le_mul_of_nonneg_left (this.trans hκ'2) hm
      _ ≤ κ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hw0 := dotProduct_self_nonneg' w
  have hn0 : 0 ≤ ‖w‖ ^ 2 := by positivity
  calc r ⬝ᵥ r ≤ m * ‖r‖ ^ 2 := h1
    _ ≤ m * (κ' ^ 2 * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg m)
    _ = (m * κ' ^ 2) * ‖w‖ ^ 2 := by ring
    _ ≤ κ * (w ⬝ᵥ w) := mul_le_mul hκsq h3 hn0 hκ.le

/-- **Boundary layer, Jacobian form**: if `∂g/∂z` exists, equals the Hurwitz matrix `A(p)` at the
equilibrium `h(p)` (continuous in `p` over a compact parameter space) and is uniformly
continuous at the equilibrium, the boundary layer is locally exponentially stable uniformly in
`p`. -/
@[powerlib_foundation] theorem boundaryLayer_uniform_exponentialStability_of_jacobian {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {A : X → Matrix (Fin m) (Fin m) ℝ} (hA : Continuous A)
    (hH : ∀ p, LinearSystems.IsHurwitz (A p)) {g : X → (Fin m → ℝ) → Fin m → ℝ}
    {h : X → Fin m → ℝ} {J : X → (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)}
    (heq : ∀ p, g p (h p) = 0) (hJ : ∀ p z, HasFDerivAt (g p) (J p z) z)
    (hJA : ∀ p v, J p (h p) v = A p *ᵥ v)
    (hunif : ∀ κ > 0, ∃ ρ > 0, ∀ p z, ‖z - h p‖ ≤ ρ → ‖J p z - J p (h p)‖ ≤ κ) :
    ∃ r > 0, ∃ C > 0, ∃ α > 0, ∀ p (y : ℝ → Fin m → ℝ),
      IsIntegralCurveOn y (fun _ v => g p v) (Ici 0) →
      (y 0 - h p) ⬝ᵥ (y 0 - h p) < r → ∀ τ, 0 ≤ τ →
        (y τ - h p) ⬝ᵥ (y τ - h p) ≤ C * Real.exp (-(α * τ)) * ((y 0 - h p) ⬝ᵥ (y 0 - h p)) :=
  boundaryLayer_uniform_exponentialStability hA hH
    (uniform_linearization_of_jacobian heq hJ hJA hunif)

/-- A Jacobian that is Lipschitz at the equilibrium with one constant `L` for all parameters
(`‖J p z − J p (h p)‖ ≤ L ‖z − h p‖`) is uniformly continuous there. -/
@[powerlib_foundation] theorem uniform_jacobian_of_lipschitz {X : Type*} {h : X → Fin m → ℝ}
    {J : X → (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)} {L : ℝ}
    (hL : ∀ p z, ‖J p z - J p (h p)‖ ≤ L * ‖z - h p‖) :
    ∀ κ > 0, ∃ ρ > 0, ∀ p z, ‖z - h p‖ ≤ ρ → ‖J p z - J p (h p)‖ ≤ κ := by
  intro κ hκ
  refine ⟨κ / (|L| + 1), by positivity, fun p z hz => ?_⟩
  have hL0 := abs_nonneg L
  calc ‖J p z - J p (h p)‖ ≤ L * ‖z - h p‖ := hL p z
    _ ≤ |L| * ‖z - h p‖ := mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)
    _ ≤ |L| * (κ / (|L| + 1)) := mul_le_mul_of_nonneg_left hz hL0
    _ ≤ κ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **Tikhonov's boundary-layer hypothesis, `(t, x)` form.** The boundary-layer system
`dz/dτ = g(t, x, z)` with the slow variables `(t, x)` frozen in a compact set
`S ⊆ ℝ × ℝⁿ` (e.g. `[0, T] × K`): if `g(t, x, h(t, x)) = 0`, the Jacobian `∂g/∂z` exists, equals a
matrix `A(t, x)` at `z = h(t, x)` that is continuous on `S` and Hurwitz at every point of `S`, and
is Lipschitz at the equilibrium with one constant `L`, then `z = h(t, x)` is locally exponentially
stable uniformly in `(t, x) ∈ S`: one radius `r`, one constant `C` and one rate `α` serve every
frozen `(t, x)`. -/
@[powerlib_foundation] theorem boundaryLayer_uniform_exponentialStability_tx {n : ℕ}
    {S : Set (ℝ × (Fin n → ℝ))} (hS : IsCompact S)
    {g : ℝ → (Fin n → ℝ) → (Fin m → ℝ) → Fin m → ℝ} {h : ℝ → (Fin n → ℝ) → Fin m → ℝ}
    {J : ℝ → (Fin n → ℝ) → (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)}
    {A : ℝ → (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ} {L : ℝ}
    (hA : ContinuousOn (fun q : ℝ × (Fin n → ℝ) => A q.1 q.2) S)
    (hH : ∀ q ∈ S, LinearSystems.IsHurwitz (A q.1 q.2))
    (heq : ∀ q ∈ S, g q.1 q.2 (h q.1 q.2) = 0)
    (hJ : ∀ q ∈ S, ∀ z, HasFDerivAt (g q.1 q.2) (J q.1 q.2 z) z)
    (hJA : ∀ q ∈ S, ∀ v, J q.1 q.2 (h q.1 q.2) v = A q.1 q.2 *ᵥ v)
    (hL : ∀ q ∈ S, ∀ z, ‖J q.1 q.2 z - J q.1 q.2 (h q.1 q.2)‖ ≤ L * ‖z - h q.1 q.2‖) :
    ∃ r > 0, ∃ C > 0, ∃ α > 0, ∀ t x, (t, x) ∈ S → ∀ y : ℝ → Fin m → ℝ,
      IsIntegralCurveOn y (fun _ v => g t x v) (Ici 0) →
      (y 0 - h t x) ⬝ᵥ (y 0 - h t x) < r → ∀ τ, 0 ≤ τ →
        (y τ - h t x) ⬝ᵥ (y τ - h t x) ≤
          C * Real.exp (-(α * τ)) * ((y 0 - h t x) ⬝ᵥ (y 0 - h t x)) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨r, hr, C, hC, α, hα, H⟩ :=
    boundaryLayer_uniform_exponentialStability_of_jacobian (X := S)
      (A := fun q => A q.1.1 q.1.2) (g := fun q => g q.1.1 q.1.2) (h := fun q => h q.1.1 q.1.2)
      (J := fun q => J q.1.1 q.1.2) hA.domRestrict (fun q => hH q.1 q.2) (fun q => heq q.1 q.2)
      (fun q => hJ q.1 q.2) (fun q => hJA q.1 q.2)
      (uniform_jacobian_of_lipschitz (fun q => hL q.1 q.2))
  exact ⟨r, hr, C, hC, α, hα, fun t x htx y hy => H ⟨(t, x), htx⟩ y hy⟩

end powerlib.SingularPerturbation
