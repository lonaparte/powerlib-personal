import theorem.Map.CenterReduction
import theorem.Periodic.CriticalMultiplier

/-! # A periodic orbit with a simple multiplier `−1`: reduction to the flip normal form

At a periodic solution `x_*` of a `T`-periodic system `ẋ = G(t, x)` whose monodromy has the
multiplier `−1` (period doubling) the linearization does not decide stability
(`Periodic.critical_minus_undecided`); the period (Poincaré) map `P`, `P(x_*(0)) = x_*(0)`, does.
When `−1` is simple and every other multiplier lies strictly inside the unit circle, `P` has a
one-dimensional centre manifold, and the map restricted to it is
`r(x) = −x + a x² + b x³ + O(x⁴)` with
`a = w P₂(v, v)`, `b = w P₃(v, v, v) + w (P₂(v, k₂) + P₂(k₂, v))`, `(I − M) k₂ = Q P₂(v, v)`,
where `P(p + e) = p + M e + P₂(e, e) + P₃(e, e, e) + O(‖e‖⁴)`, `M v = −v`, `wᵀ M = −wᵀ`,
`w v = 1` and `Q e = e − (w e) v`. The **flip coefficient** `a² + b` decides: positive — `p` is
locally asymptotically (never exponentially) stable; negative — unstable. With `B = D²P(p) = 2P₂`
and `C = D³P(p) = 6P₃` it is Kuznetsov's multidimensional flip coefficient
`(1/6)⟨w, C(v, v, v)⟩ + (1/2)⟨w, B(v, (I − M)⁻¹ B(v, v))⟩` (the `Q` part of `B(v, v)` gives `b`,
the `v` part gives `a²`).

The chain: an adapted norm in which the stable part contracts in one step (the weighted orbit
embedding `T y = (θ^{−k} Lᵏ y)_{k<m}` of the deflated monodromy `L = M + v wᵀ`, with the weighted
shift `B̂`, `B̂ T = T L`, `‖B̂‖ ≤ θ < 1`); coordinates `Φ e = (w e, T Q e)` in which `P` reads
`(x, u) ↦ (−x + f(x, u), B̂ u + g(x, u))` near `0`; the centre manifold of the cut-off map
(`theorem/Map/CenterManifold.lean`), which lies in the range of `Φ`; the reduction principle and
the approximation theorem with `q = 3` (`theorem/Map/CenterReduction.lean`), giving
`h(x) = x² T k₂ + O(x³)`; the expansion of the reduced map to order four; the scalar flip normal
forms of `theorem/Periodic/CriticalMultiplier.lean`.

Scope.
* The map semantics on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (`Map.LocalAsymptoticStable`,
  `Map.Unstable`, `Map.LocallyExponentiallyStable`) for a map `P : ℝⁿ → ℝⁿ` with a fixed point
  `p`. For a periodic orbit, `P` is the period map `y ↦ x(T; 0, y)` and `p = x_*(0)`; its
  regularity is a **hypothesis**: strict derivative `M` at `p` (for the period map, the monodromy
  `Φ(T, 0)` of the linearization along `x_*`) and the cubic Taylor expansion with remainder
  `K ‖e‖⁴` on `‖e‖ ≤ ρ₀` (a period map of class `C⁴`). Neither the library nor Mathlib or
  LeanForControl differentiates ODE flows with respect to the initial state, so `DP(p) = Φ(T, 0)`
  and the expansion are not derived from `G` here.
* The spectral hypothesis is in projector form: `M v = −v`, `w ∘ M = −w`, `w v = 1`, and a power
  of the deflated map `L = M + v wᵀ` of norm below one. `multipliers_of_deflate` shows what it
  says about the multipliers: every complex multiplier other than `−1` lies strictly inside the
  unit circle, every eigenvector of `−1` is a multiple of `v`, and there is no Jordan chain at `−1`
  (`−1` is simple). The matrix form (`Linear.op` of the monodromy matrix with
  `LTI.SchurStable (M + v wᵀ)`) is `localAsymptoticStable_of_flipCoeff_pos_matrix`,
  `unstable_of_flipCoeff_neg_matrix`.
* The quadratic and cubic terms are a continuous bilinear map `P₂` (not assumed symmetric) and a
  continuous trilinear map `P₃` on the diagonal (`ContinuousMultilinearMap` on `Fin 3`); `k₂` is
  any solution of `k₂ − M k₂ = Q P₂(v, v)` (unique, `I − M` being invertible).
* `a² + b = 0` (a degenerate flip) is not decided here.
* Generic; nothing here describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §4.4–§4.5 (the flip
bifurcation of maps, the normal form `−η + c η³`) and §5.4.2 (restricted normalized maps: the flip
coefficient by the projection method); Carr, *Applications of Centre Manifold Theory* (1981), §2.8;
Iooss, *Bifurcation of Maps and Applications* (1979), Ch. III; the open item of
`theorem/Periodic/CriticalMultiplier.lean` (Scope: "a genuinely nonconstant periodic orbit with a
simple critical multiplier and a stable complement is not treated (it needs the centre-manifold
reduction)").

Results.
* The splitting: `specProj` (`Q`), `deflate` (`L = M + v wᵀ`), `specProj_apply`, `deflate_apply`,
  `w_specProj`, `specProj_idem`, `specProj_self`, `deflate_specProj` (`L Q = Q M = L`),
  `w_deflate`, `multipliers_of_deflate`.
* The adapted norm: `orbitEmb` (`T`), `orbitShift` (`B̂`), `orbitEmb_apply`, `orbitEmb_zero`,
  `norm_le_norm_orbitEmb`, `orbitShift_orbitEmb` (`B̂ T = T L`), `norm_orbitShift_le`
  (`‖B̂‖ ≤ θ`), `exists_rate` (`‖Lᵐ‖ < 1` gives `θ < 1` with `‖Lᵐ‖ ≤ θᵐ`).
* Coordinates: `eq_smul_single`, `centreCoord`, `centreCoord_apply_zero`, `coordMap` (`Φ`),
  `coordInv` (`Ψ`), `coordInv_apply`, `coordInv_coordMap`, `coordMap_linear`,
  `coordMap_coordInv`; the map in coordinates: `nonlin`, `nonlin_spec`, `cutF`, `cutG`,
  `lipschitzWith_cut`, `coordMap_conj`.
* Expansions: `isBigO_bilin`, `isBigO_cubic`, `isBigO_cubic_sub`, `isBigO_smul_const`,
  `isBigO_norm_pow_of_le`, `isBigO_coord_pow`, `isBigO_taylor_comp`, `bilin_add_self`,
  `reduced_expansion` (the reduced map to order four), `defect_expansion` (the invariance defect
  of `x ↦ x² k₂` is `O(x³)`).
* Translation: `iterate_translate`, `lyapunovStable_translate`,
  `localAsymptoticStable_of_translate`.
* **The theorems**: `exists_reduced_map` (a scalar map `r(x) = −x + a x² + b x³ + O(x⁴)` whose
  asymptotic stability gives that of `P` and whose instability gives that of `P`),
  `localAsymptoticStable_of_flipCoeff_pos` (`a² + b > 0`: locally asymptotically, not
  exponentially, stable), `unstable_of_flipCoeff_neg` (`a² + b < 0`: unstable), and their matrix
  forms `localAsymptoticStable_of_flipCoeff_pos_matrix`, `unstable_of_flipCoeff_neg_matrix`.

Corrections.
None: an extension (the critical multiplier `−1` of a nonconstant periodic orbit with a stable
complement, decided beyond the linearization).

Family and connection conclusions.
None: static evidence on maps (the period map of a periodic orbit).
-/

noncomputable section

open Filter Topology Asymptotics

namespace powerlib.Periodic.FlipReduction

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-! ## The splitting along a simple multiplier `−1` -/

/-- The spectral projection onto `ker w` along `v`: `Q e = e − (w e) v`. -/
def specProj (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) : ℝⁿ →L[ℝ] ℝⁿ :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - w.smulRight v

/-- The deflated monodromy `L = M + v wᵀ`: `M` on `ker w`, `0` on the eigenvector `v`. -/
def deflate (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) : ℝⁿ →L[ℝ] ℝⁿ := M + w.smulRight v

@[tmio T, powerlib_foundation] theorem specProj_apply (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) (e : ℝⁿ) :
    specProj v w e = e - w e • v := by
  simp [specProj]

@[tmio T, powerlib_foundation] theorem deflate_apply (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ)
    (w : ℝⁿ →L[ℝ] ℝ) (e : ℝⁿ) : deflate M v w e = M e + w e • v := by
  simp [deflate]

variable {M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {v : EuclideanSpace ℝ (Fin n)} {w : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}

@[tmio T, powerlib_foundation] theorem w_specProj (hwv : w v = 1) (e : ℝⁿ) :
    w (specProj v w e) = 0 := by
  rw [specProj_apply, map_sub, map_smul, hwv, smul_eq_mul, mul_one, sub_self]

@[tmio T, powerlib_foundation] theorem specProj_idem (hwv : w v = 1) (e : ℝⁿ) :
    specProj v w (specProj v w e) = specProj v w e := by
  rw [specProj_apply (e := specProj v w e), w_specProj hwv, zero_smul, sub_zero]

@[tmio T, powerlib_foundation] theorem specProj_self (hwv : w v = 1) : specProj v w v = 0 := by
  rw [specProj_apply, hwv, one_smul, sub_self]

/-- On `ker w` the deflated monodromy is `M`, and `L Q = Q M = L`. -/
@[tmio T, powerlib_foundation] theorem deflate_specProj (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) (e : ℝⁿ) :
    deflate M v w (specProj v w e) = specProj v w (M e) ∧
      specProj v w (M e) = deflate M v w e := by
  constructor
  · simp only [deflate_apply, specProj_apply, map_sub, map_smul, hv, hw, hwv]
    module
  · simp only [deflate_apply, specProj_apply, hw]
    module

@[tmio T, powerlib_foundation] theorem w_deflate (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1)
    (e : ℝⁿ) : w (deflate M v w e) = 0 := by
  rw [deflate_apply, map_add, map_smul, hw, hwv, smul_eq_mul, mul_one, neg_add_cancel]

open Matrix in
/-- **What the spectral hypothesis says about the multipliers** (matrix form). For a real matrix
`M` with `M v = −v`, `wᵀ M = −wᵀ`, `w ⬝ v = 1` and Schur stable deflated matrix `M + v wᵀ`:
every complex multiplier of `M` other than `−1` lies strictly inside the unit circle, every complex
eigenvector of `−1` is a multiple of `v`, and there is no Jordan chain at `−1`
(`(M + I) z = v` has no solution): `−1` is a simple multiplier. -/
@[tmio T, powerlib_foundation] theorem multipliers_of_deflate {Mm : Matrix (Fin n) (Fin n) ℝ}
    {vm wm : Fin n → ℝ} (hv : Mm *ᵥ vm = -vm) (hw : wm ᵥ* Mm = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (Mm + Matrix.vecMulVec vm wm)) :
    (∀ (μ : ℂ) (z : Fin n → ℂ), z ≠ 0 → Mm.map (algebraMap ℝ ℂ) *ᵥ z = μ • z →
      μ = -1 ∨ ‖μ‖ < 1) ∧
    (∀ z : Fin n → ℂ, Mm.map (algebraMap ℝ ℂ) *ᵥ z = -z →
      z = ((algebraMap ℝ ℂ ∘ wm) ⬝ᵥ z) • (algebraMap ℝ ℂ ∘ vm)) ∧
    ¬ ∃ z : Fin n → ℂ, (Mm.map (algebraMap ℝ ℂ) + 1) *ᵥ z = algebraMap ℝ ℂ ∘ vm := by
  set f := algebraMap ℝ ℂ with hf
  set Mc := Mm.map f with hMc
  set vc := f ∘ vm with hvc
  set wc := f ∘ wm with hwc
  have hvM : Mc *ᵥ vc = -vc := by
    funext i
    have := RingHom.map_mulVec f Mm vm i
    rw [hv] at this
    rw [← this]; simp [hvc]
  have hwM' : wc ᵥ* Mc = -wc := by
    funext i
    have := RingHom.map_vecMul f Mm wm i
    rw [hw] at this
    rw [← this]; simp [hwc]
  have hwv' : wc ⬝ᵥ vc = 1 := by
    have := RingHom.map_dotProduct f wm vm
    rw [hwv, map_one] at this
    exact this.symm
  have hLc : (Mm + Matrix.vecMulVec vm wm).map f = Mc + Matrix.vecMulVec vc wc := by
    ext i j; simp [Matrix.vecMulVec_apply, hMc, hvc, hwc]
  have hwM : ∀ z, wc ⬝ᵥ (Mc *ᵥ z) = -(wc ⬝ᵥ z) := fun z => by
    rw [Matrix.dotProduct_mulVec, hwM', neg_dotProduct]
  have hL : ∀ z, (Mc + Matrix.vecMulVec vc wc) *ᵥ z = Mc *ᵥ z + (wc ⬝ᵥ z) • vc := fun z => by
    rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  refine ⟨fun μ z hz hMz => ?_, fun z hMz => ?_, ?_⟩
  · have h1 : (μ + 1) * (wc ⬝ᵥ z) = 0 := by
      have := hwM z
      rw [hMz, dotProduct_smul, smul_eq_mul] at this
      linear_combination this
    rcases mul_eq_zero.mp h1 with h | h
    · left; linear_combination h
    · right
      refine hS μ z hz ?_
      rw [hLc, hL, h, zero_smul, add_zero, hMz]
  · set z' := z - (wc ⬝ᵥ z) • vc with hz'
    have hwz' : wc ⬝ᵥ z' = 0 := by
      rw [hz', dotProduct_sub, dotProduct_smul, hwv', smul_eq_mul, mul_one, sub_self]
    have hMz' : Mc *ᵥ z' = -z' := by
      rw [hz', Matrix.mulVec_sub, Matrix.mulVec_smul, hMz, hvM]; module
    by_contra hne
    have hz'0 : z' ≠ 0 := fun h0 => hne (by rw [← sub_eq_zero, ← hz', h0])
    have := hS (-1) z' hz'0 (by rw [hLc, hL, hwz', zero_smul, add_zero, hMz', neg_one_smul])
    simp at this
  · rintro ⟨z, hz⟩
    have := congrArg (fun u => wc ⬝ᵥ u) hz
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, hwM, hwv'] at this
    norm_num at this

/-! ## An adapted norm by the weighted orbit embedding -/

/-- The weighted orbit embedding `T y = (θ^{−k} Lᵏ y)_{k < m}` into `Fin m → ℝⁿ` with the sup
norm; `‖T y‖` is a norm in which `L` contracts by `θ` when `‖Lᵐ‖ ≤ θᵐ`. -/
def orbitEmb (m : ℕ) (θ : ℝ) (L : ℝⁿ →L[ℝ] ℝⁿ) : ℝⁿ →L[ℝ] (Fin m → ℝⁿ) :=
  ContinuousLinearMap.pi fun k => (θ⁻¹ ^ (k : ℕ)) • (L ^ (k : ℕ))

/-- The weighted shift on `Fin m → ℝⁿ`: `(B̂ u)_k = θ u_{k+1}` for `k + 1 < m` and
`(B̂ u)_{m−1} = θ^{1−m} Lᵐ u₀`, so that `B̂ ∘ T = T ∘ L` and `‖B̂‖ ≤ θ`. -/
def orbitShift (m : ℕ) (hm : 0 < m) (θ : ℝ) (L : ℝⁿ →L[ℝ] ℝⁿ) :
    (Fin m → ℝⁿ) →L[ℝ] (Fin m → ℝⁿ) :=
  ContinuousLinearMap.pi fun k =>
    if hk : (k : ℕ) + 1 < m then θ • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin n)) ⟨k + 1, hk⟩
    else (θ⁻¹ ^ (m - 1)) • ((L ^ m).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin n)) ⟨0, hm⟩))

@[tmio T, powerlib_foundation] theorem orbitEmb_apply (m : ℕ) (θ : ℝ) (L : ℝⁿ →L[ℝ] ℝⁿ)
    (y : ℝⁿ) (k : Fin m) : orbitEmb m θ L y k = (θ⁻¹ ^ (k : ℕ)) • (L ^ (k : ℕ)) y := by
  simp [orbitEmb]

@[tmio T, powerlib_foundation] theorem orbitEmb_zero {m : ℕ} (hm : 0 < m) (θ : ℝ)
    (L : ℝⁿ →L[ℝ] ℝⁿ) (y : ℝⁿ) : orbitEmb m θ L y ⟨0, hm⟩ = y := by
  simp [orbitEmb_apply]

@[tmio T, powerlib_foundation] theorem norm_le_norm_orbitEmb {m : ℕ} (hm : 0 < m) (θ : ℝ)
    (L : ℝⁿ →L[ℝ] ℝⁿ) (y : ℝⁿ) : ‖y‖ ≤ ‖orbitEmb m θ L y‖ := by
  have := norm_le_pi_norm (orbitEmb m θ L y) ⟨0, hm⟩
  rwa [orbitEmb_zero] at this

/-- `B̂ ∘ T = T ∘ L`. -/
@[tmio T, powerlib_foundation] theorem orbitShift_orbitEmb {m : ℕ} (hm : 0 < m) {θ : ℝ}
    (hθ : θ ≠ 0) (L : ℝⁿ →L[ℝ] ℝⁿ) (y : ℝⁿ) :
    orbitShift m hm θ L (orbitEmb m θ L y) = orbitEmb m θ L (L y) := by
  funext k
  rw [orbitEmb_apply]
  simp only [orbitShift, ContinuousLinearMap.pi_apply]
  have hL : (L ^ (k : ℕ)) (L y) = (L ^ ((k : ℕ) + 1)) y := by
    rw [pow_succ]; rfl
  split_ifs with hk
  · simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply]
    rw [orbitEmb_apply, hL, smul_smul]
    congr 1
    simp only [pow_succ]
    field_simp
  · have hk' : (k : ℕ) = m - 1 := by omega
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.proj_apply]
    rw [orbitEmb_zero, hL, hk', Nat.sub_add_cancel hm]

/-- `‖B̂ u‖ ≤ θ ‖u‖` when `‖Lᵐ‖ ≤ θᵐ`. -/
@[tmio T, powerlib_foundation] theorem norm_orbitShift_le {m : ℕ} (hm : 0 < m) {θ : ℝ}
    (hθ : 0 < θ) {L : ℝⁿ →L[ℝ] ℝⁿ} (hLm : ‖L ^ m‖ ≤ θ ^ m) (u : Fin m → ℝⁿ) :
    ‖orbitShift m hm θ L u‖ ≤ θ * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  simp only [orbitShift, ContinuousLinearMap.pi_apply]
  split_ifs with hk
  · simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply]
    rw [norm_smul, Real.norm_of_nonneg hθ.le]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u _) hθ.le
  · simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.proj_apply]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := (L ^ m).le_opNorm (u ⟨0, hm⟩)
    have h2 := norm_le_pi_norm u ⟨0, hm⟩
    have h3 : θ⁻¹ ^ (m - 1) * θ ^ m = θ := by
      rw [inv_pow, ← Nat.sub_add_cancel hm, pow_succ]
      field_simp
      simp
    calc θ⁻¹ ^ (m - 1) * ‖(L ^ m) (u ⟨0, hm⟩)‖ ≤ θ⁻¹ ^ (m - 1) * (θ ^ m * ‖u‖) := by
          gcongr
          exact h1.trans (mul_le_mul hLm h2 (norm_nonneg _) (by positivity))
      _ = θ * ‖u‖ := by rw [← mul_assoc, h3]

/-- A power of norm below one gives a contraction factor `θ < 1` with `‖Lᵐ‖ ≤ θᵐ`
(`θ = 1 − (1 − ‖Lᵐ‖)/(2m)`, Bernoulli). -/
@[tmio T, powerlib_foundation] theorem exists_rate {m : ℕ} (hm : 0 < m) {L : ℝⁿ →L[ℝ] ℝⁿ}
    (hL : ‖L ^ m‖ < 1) : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ‖L ^ m‖ ≤ θ ^ m := by
  set τ := ‖L ^ m‖ with hτ
  have hτ0 : 0 ≤ τ := norm_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨1 + (-(1 - τ) / (2 * m)), ?_, ?_, ?_⟩
  · have : (1 - τ) / (2 * m) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e : -(1 - τ) / (2 * m) = -((1 - τ) / (2 * m)) := by ring
    rw [e]; linarith
  · have : 0 < (1 - τ) / (2 * m) := by apply div_pos <;> [linarith; positivity]
    have e : -(1 - τ) / (2 * m) = -((1 - τ) / (2 * m)) := by ring
    rw [e]; linarith
  · have hb := one_add_mul_le_pow (a := -(1 - τ) / (2 * m)) (by
      have : (1 - τ) / (2 * m) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have e : -(1 - τ) / (2 * m) = -((1 - τ) / (2 * m)) := by ring
      rw [e]; linarith) m
    have e : 1 + (m : ℝ) * (-(1 - τ) / (2 * m)) = (1 + τ) / 2 := by field_simp; ring
    rw [e] at hb
    linarith

/-! ## Coordinates: the centre coordinate and the adapted stable coordinate -/

@[tmio T, powerlib_foundation] theorem eq_smul_single (x : ℝ¹) :
    x = x 0 • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  ext i
  fin_cases i
  simp

/-- The centre coordinate `e ↦ w e`, as a point of `ℝ¹`. -/
def centreCoord (w : ℝⁿ →L[ℝ] ℝ) : ℝⁿ →L[ℝ] ℝ¹ :=
  w.smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

@[tmio T, powerlib_foundation] theorem centreCoord_apply_zero (w : ℝⁿ →L[ℝ] ℝ) (e : ℝⁿ) :
    centreCoord w e 0 = w e := by
  simp [centreCoord]

/-- The coordinates `Φ e = (w e, T (Q e))` on `ℝ¹ × (Fin m → ℝⁿ)`. -/
def coordMap (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) (m : ℕ) (θ : ℝ) :
    ℝⁿ →L[ℝ] ℝ¹ × (Fin m → ℝⁿ) :=
  (centreCoord w).prod ((orbitEmb m θ (deflate M v w)).comp (specProj v w))

/-- Its left inverse `Ψ (x, u) = x₀ v + u₀`. -/
def coordInv (v : ℝⁿ) {m : ℕ} (hm : 0 < m) : ℝ¹ × (Fin m → ℝⁿ) →L[ℝ] ℝⁿ :=
  ((EuclideanSpace.proj (0 : Fin 1)).smulRight v).comp
      (ContinuousLinearMap.fst ℝ ℝ¹ (Fin m → EuclideanSpace ℝ (Fin n))) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin n))
      ⟨0, hm⟩).comp (ContinuousLinearMap.snd ℝ ℝ¹ (Fin m → EuclideanSpace ℝ (Fin n)))

@[tmio T, powerlib_foundation] theorem coordInv_apply (v : ℝⁿ) {m : ℕ} (hm : 0 < m)
    (q : ℝ¹ × (Fin m → ℝⁿ)) : coordInv v hm q = q.1 0 • v + q.2 ⟨0, hm⟩ := by
  simp [coordInv]

/-- `Ψ ∘ Φ = id`. -/
@[tmio T, powerlib_foundation] theorem coordInv_coordMap {m : ℕ} (hm : 0 < m)
    (θ : ℝ) (e : ℝⁿ) : coordInv v hm (coordMap M v w m θ e) = e := by
  rw [coordInv_apply]
  simp only [coordMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, centreCoord_apply_zero, orbitEmb_zero, specProj_apply]
  abel

/-- The linear part in the coordinates: `Φ (M e) = (−(Φ e)₁, B̂ (Φ e)₂)`. -/
@[tmio T, powerlib_foundation] theorem coordMap_linear (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : θ ≠ 0)
    (e : ℝⁿ) :
    coordMap M v w m θ (M e) = (-(coordMap M v w m θ e).1,
      orbitShift m hm θ (deflate M v w) (coordMap M v w m θ e).2) := by
  simp only [coordMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply]
  refine Prod.ext ?_ ?_
  · simp only [centreCoord, ContinuousLinearMap.smulRight_apply, hw, neg_smul]
  · simp only
    rw [orbitShift_orbitEmb hm hθ, (deflate_specProj hv hw hwv e).1]

/-- Points `(x, T (Q y))` are in the range of `Φ`: `Φ (Ψ (x, T (Q y))) = (x, T (Q y))`. -/
@[tmio T, powerlib_foundation] theorem coordMap_coordInv (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (θ : ℝ) (x : ℝ¹) (y : ℝⁿ) :
    coordMap M v w m θ (coordInv v hm (x, orbitEmb m θ (deflate M v w) (specProj v w y))) =
      (x, orbitEmb m θ (deflate M v w) (specProj v w y)) := by
  rw [coordInv_apply]
  simp only [coordMap, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, orbitEmb_zero]
  refine Prod.ext ?_ ?_
  · simp only [centreCoord, ContinuousLinearMap.smulRight_apply, map_add, map_smul, hwv,
      w_specProj hwv, one_smul, zero_smul, add_zero]
    exact (eq_smul_single x).symm
  · simp only [map_add, map_smul, specProj_self hwv, smul_zero, zero_add, specProj_idem hwv]

/-! ## The map in coordinates -/

/-- The nonlinear part of `P` at the fixed point `p`: `N e = P(p + e) − p − M e`. -/
def nonlin (P : ℝⁿ → ℝⁿ) (p : ℝⁿ) (M : ℝⁿ →L[ℝ] ℝⁿ) (e : ℝⁿ) : ℝⁿ := P (p + e) - p - M e

@[tmio T, powerlib_foundation] theorem nonlin_spec {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) :
    HasStrictFDerivAt (nonlin P p M) (0 : ℝⁿ →L[ℝ] ℝⁿ) 0 ∧ nonlin P p M 0 = 0 := by
  refine ⟨?_, by simp [nonlin, hPp]⟩
  have hf : HasStrictFDerivAt (fun e : ℝⁿ => p + e) (ContinuousLinearMap.id ℝ ℝⁿ) 0 :=
    (hasStrictFDerivAt_id (0 : ℝⁿ)).const_add p
  have hP' : HasStrictFDerivAt P M (p + 0) := by rwa [add_zero]
  have h1 : HasStrictFDerivAt (fun e : ℝⁿ => P (p + e)) M 0 := by
    simpa using hP'.comp (0 : ℝⁿ) hf
  have h2 := (h1.sub_const p).sub M.hasStrictFDerivAt
  rw [sub_self] at h2
  exact h2

/-- The nonlinearity read in the coordinates, centre component: `(Φ (Ñ (Ψ q)))₁`. -/
def cutF (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) {m : ℕ} (hm : 0 < m) (θ : ℝ)
    (Nc : ℝⁿ → ℝⁿ) (q : ℝ¹ × (Fin m → ℝⁿ)) : ℝ¹ :=
  (coordMap M v w m θ (Nc (coordInv v hm q))).1

/-- The nonlinearity read in the coordinates, stable component: `(Φ (Ñ (Ψ q)))₂`. -/
def cutG (M : ℝⁿ →L[ℝ] ℝⁿ) (v : ℝⁿ) (w : ℝⁿ →L[ℝ] ℝ) {m : ℕ} (hm : 0 < m) (θ : ℝ)
    (Nc : ℝⁿ → ℝⁿ) (q : ℝ¹ × (Fin m → ℝⁿ)) : Fin m → ℝⁿ :=
  (coordMap M v w m θ (Nc (coordInv v hm q))).2

@[tmio T, powerlib_foundation] theorem lipschitzWith_cut {m : ℕ} (hm : 0 < m) (θ : ℝ)
    {Nc : ℝⁿ → ℝⁿ} {ε' : NNReal} (hN : LipschitzWith ε' Nc) :
    LipschitzWith (‖coordMap M v w m θ‖₊ * ε' * ‖coordInv v hm‖₊) (cutF M v w hm θ Nc) ∧
      LipschitzWith (‖coordMap M v w m θ‖₊ * ε' * ‖coordInv v hm‖₊)
        (cutG M v w hm θ Nc) := by
  have h := ((coordMap M v w m θ).lipschitzWith.comp hN).comp (coordInv v hm).lipschitzWith
  refine ⟨?_, ?_⟩
  · have := LipschitzWith.prod_fst.comp h
    rw [one_mul] at this
    exact this
  · have := LipschitzWith.prod_snd.comp h
    rw [one_mul] at this
    exact this

/-- **The map in the coordinates.** Where the cut-off `Ñ` equals the nonlinearity, the map
`G e = P(p + e) − p` is read through `Φ` as the split map with linear part `(−1, B̂)` and
nonlinearities `cutF`, `cutG`. -/
@[tmio T, powerlib_foundation] theorem coordMap_conj {P : ℝⁿ → ℝⁿ} {p : ℝⁿ} (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : θ ≠ 0)
    {Nc : ℝⁿ → ℝⁿ} {e : ℝⁿ} (he : Nc e = nonlin P p M e) :
    coordMap M v w m θ (P (p + e) - p) =
      Map.CenterManifold.splitMap (-ContinuousLinearMap.id ℝ ℝ¹)
        (orbitShift m hm θ (deflate M v w)) (cutF M v w hm θ Nc) (cutG M v w hm θ Nc)
        (coordMap M v w m θ e) := by
  have hG : P (p + e) - p = M e + Nc (coordInv v hm (coordMap M v w m θ e)) := by
    rw [coordInv_coordMap hm θ e, he, nonlin]; abel
  rw [hG, map_add, coordMap_linear hv hw hwv hm hθ e]
  simp only [Map.CenterManifold.splitMap, cutF, cutG, neg_apply,
    ContinuousLinearMap.id_apply]
  rfl

/-! ## Expansions to the orders of the normal form -/

section Asymptotics

/-- A bilinear map of two functions is bounded by the product of their bounds. -/
@[tmio T, powerlib_foundation] theorem isBigO_bilin {Z E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {l : Filter Z} (B : E →L[ℝ] F →L[ℝ] G) {α : Z → E} {β : Z → F}
    {g₁ g₂ : Z → ℝ} (hα : α =O[l] g₁) (hβ : β =O[l] g₂) :
    (fun z => B (α z) (β z)) =O[l] fun z => g₁ z * g₂ z := by
  have h1 : (fun z => B (α z) (β z)) =O[l] fun z => ‖α z‖ * ‖β z‖ :=
    IsBigO.of_bound ‖B‖ (Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (by positivity), ← mul_assoc]; exact B.le_opNorm₂ _ _)
  exact h1.trans (hα.norm_left.mul hβ.norm_left)

/-- A cubic form `e ↦ P₃ (e, e, e)` (a continuous trilinear map on the diagonal) of a function
bounded by `g` is bounded by `g³`. -/
@[tmio T, powerlib_foundation] theorem isBigO_cubic {Z E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] {l : Filter Z}
    (P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) G) {α : Z → E} {g : Z → ℝ}
    (hα : α =O[l] g) : (fun z => P₃ (fun _ => α z)) =O[l] fun z => g z ^ 3 := by
  have h1 : (fun z => P₃ (fun _ => α z)) =O[l] fun z => ‖α z‖ ^ 3 :=
    IsBigO.of_bound ‖P₃‖ (Eventually.of_forall fun z => by
      rw [norm_pow, norm_norm]
      have := P₃.le_opNorm (fun _ => α z)
      simpa [Finset.prod_const] using this)
  exact h1.trans (hα.norm_left.pow 3)

/-- The difference of a cubic form at two points: `P₃(a) − P₃(b) = O(g² g')` when `a, b = O(g)`
and `a − b = O(g')`. -/
@[tmio T, powerlib_foundation] theorem isBigO_cubic_sub {Z E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] {l : Filter Z}
    (P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) G) {α β : Z → E} {g g' : Z → ℝ}
    (hα : α =O[l] g) (hβ : β =O[l] g) (hαβ : (fun z => α z - β z) =O[l] g') :
    (fun z => P₃ (fun _ => α z) - P₃ (fun _ => β z)) =O[l] fun z => g z ^ 2 * g' z := by
  have h1 : (fun z => P₃ (fun _ => α z) - P₃ (fun _ => β z)) =O[l]
      fun z => (‖α z‖ + ‖β z‖) ^ 2 * ‖α z - β z‖ :=
    IsBigO.of_bound (‖P₃‖ * 3) (Eventually.of_forall fun z => by
      have := P₃.norm_image_sub_le (fun _ => α z) (fun _ => β z)
      simp only [Fintype.card_fin, pi_norm_const] at this
      have hm : max ‖α z‖ ‖β z‖ ^ 2 ≤ (‖α z‖ + ‖β z‖) ^ 2 :=
        pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _))
          (max_le (le_add_of_nonneg_right (norm_nonneg _))
            (le_add_of_nonneg_left (norm_nonneg _))) 2
      have e : (fun _ : Fin 3 => α z) - (fun _ => β z) = fun _ => α z - β z := rfl
      rw [e, pi_norm_const] at this
      rw [Real.norm_of_nonneg (by positivity)]
      calc _ ≤ ‖P₃‖ * 3 * max ‖α z‖ ‖β z‖ ^ (3 - 1) * ‖α z - β z‖ := by exact_mod_cast this
        _ ≤ ‖P₃‖ * 3 * (‖α z‖ + ‖β z‖) ^ 2 * ‖α z - β z‖ := by gcongr
        _ = ‖P₃‖ * 3 * ((‖α z‖ + ‖β z‖) ^ 2 * ‖α z - β z‖) := by ring)
  exact h1.trans (IsBigO.mul (IsBigO.pow (hα.norm_left.add hβ.norm_left) 2) hαβ.norm_left)

/-- A real function times a fixed vector. -/
@[tmio T, powerlib_foundation] theorem isBigO_smul_const {Z E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {l : Filter Z} {c : Z → ℝ} {g : Z → ℝ} (hc : c =O[l] g) (k : E) :
    (fun z => c z • k) =O[l] g := by
  refine (IsBigO.of_bound ‖k‖ (Eventually.of_forall fun z => ?_)).trans hc
  rw [norm_smul, mul_comm]

/-- Near `0`, `‖x‖^j = O(‖x‖^i)` for `i ≤ j`. -/
@[tmio T, powerlib_foundation] theorem isBigO_norm_pow_of_le {E : Type*} [NormedAddCommGroup E]
    {i j : ℕ} (hij : i ≤ j) : (fun x : E => ‖x‖ ^ j) =O[𝓝 0] fun x => ‖x‖ ^ i := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [one_mul, norm_pow, norm_pow, norm_norm]
  exact pow_le_pow_of_le_one (norm_nonneg _) hx hij

/-- The coordinate of `ℝ¹`: `(x 0)^k = O(‖x‖^k)`. -/
@[tmio T, powerlib_foundation] theorem isBigO_coord_pow (k : ℕ) :
    (fun x : ℝ¹ => x 0 ^ k) =O[𝓝 0] fun x => ‖x‖ ^ k :=
  IsBigO.of_bound 1 (Eventually.of_forall fun x => by
    rw [one_mul, norm_pow, norm_pow, norm_norm, Real.norm_eq_abs, ← NormalForm.norm_state1])

/-- The Taylor remainder along a function of order one: if `N e − P₂ e e − P₃ e e e` is bounded
by `K ‖e‖⁴` near `0` and `α = O(‖x‖)`, then the remainder along `α` is `O(‖x‖⁴)`. -/
@[tmio T, powerlib_foundation] theorem isBigO_taylor_comp {N : ℝⁿ → ℝⁿ}
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖N e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {α : ℝ¹ → ℝⁿ} (hα : α =O[𝓝 0] fun x => ‖x‖ ^ 1) :
    (fun x => N (α x) - P₂ (α x) (α x) - P₃ (fun _ => α x)) =O[𝓝 0] fun x => ‖x‖ ^ 4 := by
  have hR : (fun e => N e - P₂ e e - P₃ (fun _ => e)) =O[𝓝 (0 : ℝⁿ)] fun e => ‖e‖ ^ 4 := by
    refine IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝⁿ) hρ₀] with e he
    rw [Metric.mem_closedBall, dist_zero_right] at he
    rw [norm_pow, norm_norm]
    exact hTay e he
  have hα0 : Tendsto α (𝓝 0) (𝓝 0) := hα.trans_tendsto (by
    simpa using (tendsto_norm_zero (E := ℝ¹)).pow 1)
  have h1 := hR.comp_tendsto hα0
  have h2 : (fun x => ‖α x‖ ^ 4) =O[𝓝 0] fun x => (‖x‖ ^ 1) ^ 4 := hα.norm_left.pow 4
  refine h1.trans (h2.trans ?_)
  refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
  simp only [one_mul, norm_pow, norm_norm]
  ring_nf
  exact le_rfl

/-- `B (a + z) (a + z) = B a a + B z (a + z) + B a z` for a bilinear `B`. -/
@[tmio T, powerlib_foundation] theorem bilin_add_self {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F)
    (a z : E) : B (a + z) (a + z) = B a a + B z (a + z) + B a z := by
  simp only [map_add, add_apply]; abel

/-- **The expansion of the reduced map.** If `y(x) = (x 0)² k₂ + O(‖x‖³)` and `N` has the cubic
Taylor expansion `P₂ e e + P₃(e, e, e) + O(‖e‖⁴)`, then along `e(x) = (x 0) v + y(x)`
`w (N (e x)) = a (x 0)² + b (x 0)³ + O(‖x‖⁴)` with `a = w (P₂ v v)` and
`b = w (P₃ (v, v, v)) + w (P₂ v k₂ + P₂ k₂ v)`. -/
@[tmio T, powerlib_foundation] theorem reduced_expansion {N : ℝⁿ → ℝⁿ}
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖N e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    (w : ℝⁿ →L[ℝ] ℝ) (v k₂ : ℝⁿ) {y : ℝ¹ → ℝⁿ}
    (hy : (fun x => y x - x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 3) :
    (fun x : ℝ¹ => w (N (x 0 • v + y x)) -
      (w (P₂ v v) * x 0 ^ 2 + (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v)) * x 0 ^ 3))
      =O[𝓝 0] fun x => ‖x‖ ^ 4 := by
  have hu1' : (fun x : ℝ¹ => x 0) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    simpa using isBigO_coord_pow 1
  have hav : (fun x : ℝ¹ => x 0 • v) =O[𝓝 0] fun x => ‖x‖ ^ 1 := isBigO_smul_const hu1' v
  have hk2 : (fun x : ℝ¹ => x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 2 :=
    isBigO_smul_const (isBigO_coord_pow 2) k₂
  have hd2 : (fun x => y x - x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 2 :=
    hy.trans (isBigO_norm_pow_of_le (by norm_num))
  have hy2 : y =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
    have := hd2.add hk2
    simpa using this
  have hy1 : y =O[𝓝 0] fun x => ‖x‖ ^ 1 := hy2.trans (isBigO_norm_pow_of_le (by norm_num))
  have he : (fun x : ℝ¹ => x 0 • v + y x) =O[𝓝 0] fun x => ‖x‖ ^ 1 := hav.add hy1
  have he₂ : (fun x : ℝ¹ => x 0 • v + x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 1 :=
    hav.add (hk2.trans (isBigO_norm_pow_of_le (by norm_num)))
  have hpow : ∀ i j k : ℕ, i + j = k →
      (fun x : ℝ¹ => ‖x‖ ^ i * ‖x‖ ^ j) =O[𝓝 0] fun x => ‖x‖ ^ k := fun i j k hk =>
    IsBigO.of_bound 1 (Eventually.of_forall fun x => by rw [← pow_add, hk, one_mul])
  -- the five terms
  have T1 : (fun x : ℝ¹ => w (N (x 0 • v + y x) - P₂ (x 0 • v + y x) (x 0 • v + y x) -
      P₃ (fun _ => x 0 • v + y x))) =O[𝓝 0] fun x => ‖x‖ ^ 4 :=
    (w.isBigO_comp _ _).trans (isBigO_taylor_comp hρ₀ hTay he)
  have T2a : (fun x : ℝ¹ => w (P₂ (y x - x 0 ^ 2 • k₂) (x 0 • v + y x))) =O[𝓝 0]
      fun x => ‖x‖ ^ 4 :=
    (w.isBigO_comp _ _).trans ((isBigO_bilin P₂ hy he).trans (hpow 3 1 4 rfl))
  have T2b : (fun x : ℝ¹ => w (P₂ (x 0 • v + x 0 ^ 2 • k₂) (y x - x 0 ^ 2 • k₂))) =O[𝓝 0]
      fun x => ‖x‖ ^ 4 :=
    (w.isBigO_comp _ _).trans ((isBigO_bilin P₂ he₂ hy).trans (hpow 1 3 4 rfl))
  have T2c : (fun x : ℝ¹ => x 0 ^ 4 * w (P₂ k₂ k₂)) =O[𝓝 0] fun x => ‖x‖ ^ 4 :=
    (IsBigO.of_bound |w (P₂ k₂ k₂)| (Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs (w _), mul_comm])).trans (isBigO_coord_pow 4)
  have T3 : (fun x : ℝ¹ => w (P₃ (fun _ => x 0 • v + y x) - P₃ (fun _ => x 0 • v)))
      =O[𝓝 0] fun x => ‖x‖ ^ 4 := by
    refine (w.isBigO_comp _ _).trans ((isBigO_cubic_sub P₃ he hav (by simpa using hy2)).trans ?_)
    exact IsBigO.of_bound 1 (Eventually.of_forall fun x => by
      simp only [one_mul, norm_mul, norm_pow, norm_norm]
      ring_nf
      exact le_rfl)
  have hsum := (((T1.add T2a).add T2b).add T2c).add T3
  refine hsum.congr_left fun x => ?_
  -- the algebra: expand the bilinear and trilinear terms
  have hee : x 0 • v + y x = (x 0 • v + x 0 ^ 2 • k₂) + (y x - x 0 ^ 2 • k₂) := by abel
  have i1 := bilin_add_self P₂ (x 0 • v + x 0 ^ 2 • k₂) (y x - x 0 ^ 2 • k₂)
  rw [← hee] at i1
  have i2 : w (P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂)) =
      w (P₂ v v) * x 0 ^ 2 + (w (P₂ v k₂) + w (P₂ k₂ v)) * x 0 ^ 3 +
        x 0 ^ 4 * w (P₂ k₂ k₂) := by
    simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have i3 : P₃ (fun _ => x 0 • v) = x 0 ^ 3 • P₃ (fun _ => v) := by
    have := P₃.map_smul_univ (fun _ => x 0) (fun _ => v)
    simpa [Finset.prod_const] using this
  simp only [i1, i3, map_sub w, map_add w, map_smul w, smul_eq_mul]
  linear_combination (-1 : ℝ) * i2

/-- **The invariance defect of the quadratic candidate.** With `e(x) = (x 0) v + (x 0)² k₂` and
`k₂ − L k₂ = Q (P₂ v v)`, the stable defect
`(−x₀ + w N(e))² k₂ − x₀² L k₂ − Q N(e)` of the candidate graph `x ↦ (x 0)² k₂` is
`O(‖x‖³)`: its `x₀²` coefficient `k₂ − L k₂ − Q P₂ v v` vanishes. -/
@[tmio T, powerlib_foundation] theorem defect_expansion {N : ℝⁿ → ℝⁿ}
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖N e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    (w : ℝⁿ →L[ℝ] ℝ) (v k₂ : ℝⁿ) (L Q : ℝⁿ →L[ℝ] ℝⁿ) (hk : k₂ - L k₂ = Q (P₂ v v)) :
    (fun x : ℝ¹ => (-x 0 + w (N (x 0 • v + x 0 ^ 2 • k₂))) ^ 2 • k₂ - x 0 ^ 2 • L k₂ -
      Q (N (x 0 • v + x 0 ^ 2 • k₂))) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
  have hu1' : (fun x : ℝ¹ => x 0) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    simpa using isBigO_coord_pow 1
  have hav : (fun x : ℝ¹ => x 0 • v) =O[𝓝 0] fun x => ‖x‖ ^ 1 := isBigO_smul_const hu1' v
  have hk2 : (fun x : ℝ¹ => x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 2 :=
    isBigO_smul_const (isBigO_coord_pow 2) k₂
  have he : (fun x : ℝ¹ => x 0 • v + x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 1 :=
    hav.add (hk2.trans (isBigO_norm_pow_of_le (by norm_num)))
  have hpow : ∀ i j k : ℕ, i + j = k →
      (fun x : ℝ¹ => ‖x‖ ^ i * ‖x‖ ^ j) =O[𝓝 0] fun x => ‖x‖ ^ k := fun i j k hk =>
    IsBigO.of_bound 1 (Eventually.of_forall fun x => by rw [← pow_add, hk, one_mul])
  have hR := isBigO_taylor_comp hρ₀ hTay he
  have hP₂e : (fun x : ℝ¹ => P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂)) =O[𝓝 0]
      fun x => ‖x‖ ^ 2 := (isBigO_bilin P₂ he he).trans (hpow 1 1 2 rfl)
  have hP₃e : (fun x : ℝ¹ => P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂)) =O[𝓝 0]
      fun x => ‖x‖ ^ 3 := (isBigO_cubic P₃ he).trans
        (IsBigO.of_bound 1 (Eventually.of_forall fun x => by
          simp only [one_mul, norm_pow, norm_norm]; ring_nf; exact le_rfl))
  have hNe : (fun x : ℝ¹ => N (x 0 • v + x 0 ^ 2 • k₂)) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
    have := ((hR.trans (isBigO_norm_pow_of_le (by norm_num))).add hP₂e).add
      (hP₃e.trans (isBigO_norm_pow_of_le (by norm_num)))
    exact this.congr_left fun x => by abel
  have hW := (w.isBigO_comp _ _).trans hNe
  have hW1 : (fun x : ℝ¹ => w (N (x 0 • v + x 0 ^ 2 • k₂)) - 2 * x 0) =O[𝓝 0]
      fun x => ‖x‖ ^ 1 :=
    (hW.trans (isBigO_norm_pow_of_le (by norm_num))).sub (hu1'.const_mul_left 2)
  have S1 : (fun x : ℝ¹ => (w (N (x 0 • v + x 0 ^ 2 • k₂)) *
      (w (N (x 0 • v + x 0 ^ 2 • k₂)) - 2 * x 0)) • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
    isBigO_smul_const ((hW.mul hW1).trans (hpow 2 1 3 rfl)) k₂
  have S2 : (fun x : ℝ¹ => Q (N (x 0 • v + x 0 ^ 2 • k₂) -
      P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) -
      P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂))) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
    (Q.isBigO_comp _ _).trans (hR.trans (isBigO_norm_pow_of_le (by norm_num)))
  have S3 : (fun x : ℝ¹ => Q (P₂ (x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂))) =O[𝓝 0]
      fun x => ‖x‖ ^ 3 :=
    (Q.isBigO_comp _ _).trans ((isBigO_bilin P₂ hk2 he).trans (hpow 2 1 3 rfl))
  have S4 : (fun x : ℝ¹ => Q (P₂ (x 0 • v) (x 0 ^ 2 • k₂))) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
    (Q.isBigO_comp _ _).trans ((isBigO_bilin P₂ hav hk2).trans (hpow 1 2 3 rfl))
  have S5 : (fun x : ℝ¹ => Q (P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂))) =O[𝓝 0]
      fun x => ‖x‖ ^ 3 := (Q.isBigO_comp _ _).trans hP₃e
  refine ((((S1.sub S2).sub S3).sub S4).sub S5).congr_left fun x => ?_
  have hL : L k₂ = k₂ - Q (P₂ v v) := by rw [← hk]; abel
  have i1 := bilin_add_self P₂ (x 0 • v) (x 0 ^ 2 • k₂)
  have i2 : P₂ (x 0 • v) (x 0 • v) = x 0 ^ 2 • P₂ v v := by
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_smul, pow_two]
  have hQN : Q (N (x 0 • v + x 0 ^ 2 • k₂)) =
      Q (N (x 0 • v + x 0 ^ 2 • k₂) - P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) -
        P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂)) + x 0 ^ 2 • Q (P₂ v v) +
      Q (P₂ (x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂)) + Q (P₂ (x 0 • v) (x 0 ^ 2 • k₂)) +
      Q (P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂)) := by
    have hN' : N (x 0 • v + x 0 ^ 2 • k₂) =
        (N (x 0 • v + x 0 ^ 2 • k₂) - P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) -
          P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂)) + x 0 ^ 2 • P₂ v v +
        P₂ (x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) + P₂ (x 0 • v) (x 0 ^ 2 • k₂) +
        P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂) := by
      rw [← i2]
      calc N (x 0 • v + x 0 ^ 2 • k₂)
          = (N (x 0 • v + x 0 ^ 2 • k₂) -
              P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) -
              P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂)) +
            P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) +
            P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂) := by abel
        _ = (N (x 0 • v + x 0 ^ 2 • k₂) -
              P₂ (x 0 • v + x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) -
              P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂)) +
            (P₂ (x 0 • v) (x 0 • v) + P₂ (x 0 ^ 2 • k₂) (x 0 • v + x 0 ^ 2 • k₂) +
              P₂ (x 0 • v) (x 0 ^ 2 • k₂)) +
            P₃ (fun _ => x 0 • v + x 0 ^ 2 • k₂) := by rw [i1]
        _ = _ := by abel
    conv_lhs => rw [hN']
    simp only [map_add, map_smul]
  rw [hQN, hL]
  module

end Asymptotics

/-! ## The reduction of a fixed point with a simple multiplier `−1` -/

/-- Iterates of the map read from the fixed point: `Gᵏ e = Pᵏ(p + e) − p`. -/
@[tmio T, powerlib_foundation] theorem iterate_translate (P : ℝⁿ → ℝⁿ) (p e : ℝⁿ) (k : ℕ) :
    (fun e => P (p + e) - p)^[k] e = P^[k] (p + e) - p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, add_sub_cancel]

@[tmio T, powerlib_foundation] theorem lyapunovStable_translate {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (h : Map.LyapunovStable P p) : Map.LyapunovStable (fun e => P (p + e) - p) 0 := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  refine ⟨δ, hδ, fun e he k => ?_⟩
  rw [iterate_translate, sub_zero]
  exact hb (p + e) (by rwa [add_sub_cancel_left, ← sub_zero e]) k

@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_translate {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (h : Map.LocalAsymptoticStable (fun e => P (p + e) - p) 0) :
    Map.LocalAsymptoticStable P p := by
  obtain ⟨hLS, c, hc, hatt⟩ := h
  refine ⟨fun ε hε => ?_, c, hc, fun y hy => ?_⟩
  · obtain ⟨δ, hδ, hb⟩ := hLS ε hε
    refine ⟨δ, hδ, fun y hy k => ?_⟩
    have := hb (y - p) (by rwa [sub_zero]) k
    rwa [iterate_translate, add_sub_cancel, sub_zero] at this
  · have := hatt (y - p) (by rwa [sub_zero])
    have h2 := this.const_add p
    simp only [iterate_translate, add_sub_cancel, add_zero] at h2
    exact h2

/-- **The reduced map of a fixed point with a simple multiplier `−1`.** Let `P : ℝⁿ → ℝⁿ` fix
`p` with strict derivative `M` there, `M v = −v`, `w ∘ M = −w`, `w v = 1`, the deflated map
`L = M + v wᵀ` with some power of norm below one (every other multiplier strictly inside the unit
circle), and the cubic Taylor expansion
`P(p + e) = p + M e + P₂ e e + P₃(e, e, e) + O(‖e‖⁴)`; let `k₂ − M k₂ = Q P₂(v, v)` with the
spectral projection `Q e = e − (w e) v`. Then there is a map `r : ℝ¹ → ℝ¹` (the map restricted
to a centre manifold, in the coordinate `w`) with `r(x) = −x + a x² + b x³ + O(x⁴)`,
`a = w P₂(v, v)`, `b = w P₃(v, v, v) + w (P₂(v, k₂) + P₂(k₂, v))`, whose local asymptotic
stability gives that of `P` at `p` and whose instability gives that of `P`. -/
@[tmio T, powerlib_foundation] theorem exists_reduced_map {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v) (hw : ∀ e, w (M e) = -w e)
    (hwv : w v = 1) {m : ℕ} (hm : 0 < m) (hLm : ‖deflate M v w ^ m‖ < 1)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v)) :
    ∃ r : ℝ¹ → ℝ¹, (∃ ρ K' : ℝ, 0 < ρ ∧ ∀ y : ℝ¹, ‖y‖ ≤ ρ →
        |r y 0 - (-y 0 + w (P₂ v v) * y 0 ^ 2 +
          (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v)) * y 0 ^ 3)| ≤ K' * |y 0| ^ 4) ∧
      (Map.LocalAsymptoticStable r 0 → Map.LocalAsymptoticStable P p) ∧
      (Map.Unstable r 0 → Map.Unstable P p) := by
  -- the spectral data
  have hwk : w k₂ = 0 := by
    have := congrArg w hk₂
    rw [map_sub, hw, w_specProj hwv] at this
    linarith
  set L := deflate M v w with hLdef
  have hLk : k₂ - L k₂ = specProj v w (P₂ v v) := by
    rw [hLdef, deflate_apply, hwk, zero_smul, add_zero]; exact hk₂
  obtain ⟨θ, hθ0, hθ1, hθm⟩ := exists_rate hm hLm
  -- the size of the nonlinearities
  have hεr : 0 < (1 - θ) / 8 := by linarith
  let ε : NNReal := ⟨(1 - θ) / 8, hεr.le⟩
  have hεe : (ε : ℝ) = (1 - θ) / 8 := rfl
  have hε0 : 0 < ε := by rw [← NNReal.coe_pos, hεe]; exact hεr
  have hgap : θ + 3 * ε < 1 := by rw [hεe]; linarith
  have hθ2 : θ + 2 * ε < 1 := by rw [hεe]; linarith
  have hεa : (ε : ℝ) < 1 := by rw [hεe]; linarith
  have hκ1 : θ + ε < 1 - ε := by rw [hεe]; linarith
  have hκq : θ + ε < (1 - ε) ^ 3 := by
    have h1 : 1 - 3 * (ε : ℝ) ≤ (1 - ε) ^ 3 := by
      have := ε.coe_nonneg
      nlinarith [sq_nonneg (ε : ℝ), mul_nonneg (sq_nonneg (ε : ℝ)) (by linarith : (0 : ℝ) ≤ 3 - ε)]
    rw [hεe] at h1 ⊢; linarith
  -- coordinates and the linear part
  set Φ := coordMap M v w m θ with hΦ
  set Ψ := coordInv (n := n) v hm with hΨ
  set B := orbitShift m hm θ L with hBdef
  set A : ℝ¹ →L[ℝ] ℝ¹ := -ContinuousLinearMap.id ℝ ℝ¹ with hAdef
  have hAs : Function.Surjective A := fun x => ⟨-x, by simp [hAdef]⟩
  have hA : ∀ x, 1 * ‖x‖ ≤ ‖A x‖ := fun x => by simp [hAdef]
  have hB : ∀ u, ‖B u‖ ≤ θ * ‖u‖ := norm_orbitShift_le hm hθ0 hθm
  -- the cut-off nonlinearity
  obtain ⟨hN, hN0⟩ := nonlin_spec hP hPp
  set ε' : NNReal := ε / ((‖Φ‖₊ + 1) * (‖Ψ‖₊ + 1)) with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨ρ₁, hρ₁, Nc, hNcl, hNc0, hNcN⟩ :=
    Map.CenterManifold.exists_lipschitz_cutoff hN hN0 hε'0
  set f := cutF M v w hm θ Nc with hfdef
  set g := cutG M v w hm θ Nc with hgdef
  have hK : ‖Φ‖₊ * ε' * ‖Ψ‖₊ ≤ ε := by
    rw [hε', ← NNReal.coe_le_coe]
    push_cast
    have ha := norm_nonneg Φ
    have hb := norm_nonneg Ψ
    have hε := ε.coe_nonneg
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hε ha, mul_nonneg hε hb, mul_nonneg (mul_nonneg hε ha) hb]
  have hfl : LipschitzWith ε f := (lipschitzWith_cut hm θ hNcl).1.weaken hK
  have hgl : LipschitzWith ε g := (lipschitzWith_cut hm θ hNcl).2.weaken hK
  have hf0 : f 0 = 0 := by simp [hfdef, cutF, hNc0]
  have hg0 : g 0 = 0 := by simp [hgdef, cutG, hNc0]
  -- the centre manifold, its range and its graph
  set h := Map.CenterManifold.centreGraph A B f g with hhdef
  obtain ⟨hh, hh0, hinv⟩ :=
    Map.CenterManifold.centreGraph_spec hAs hA hB hθ0.le hfl hgl hf0 hg0 (by simpa using hgap)
  set T : ℝⁿ →L[ℝ] (Fin m → ℝⁿ) := (orbitEmb m θ L).comp (specProj v w) with hTdef
  set Kr : Submodule ℝ (Fin m → ℝⁿ) := LinearMap.range (T : ℝⁿ →ₗ[ℝ] (Fin m → ℝⁿ)) with hKr
  have hKc : IsClosed (Kr : Set (Fin m → ℝⁿ)) := Submodule.closed_of_finiteDimensional _
  have hBK : ∀ y ∈ Kr, B y ∈ Kr := by
    rintro _ ⟨z, rfl⟩
    refine ⟨M z, ?_⟩
    simp only [hTdef, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply, hBdef]
    rw [orbitShift_orbitEmb hm hθ0.ne', (deflate_specProj hv hw hwv z).1]
  have hgK : ∀ x, ∀ y ∈ Kr, g (x, y) ∈ Kr := fun x y _ => ⟨Nc (Ψ (x, y)), rfl⟩
  have hhK : ∀ x, h x ∈ Kr := fun x =>
    Map.CenterManifold.centreGraph_mem hKc hBK hgK hAs hA hB hθ0.le hfl hgl hf0 hg0
      (by simpa using hgap) x
  have hgraph : ∀ x, Φ (Ψ (x, h x)) = (x, h x) := fun x => by
    obtain ⟨z, hz⟩ := hhK x
    rw [← hz]
    exact coordMap_coordInv hwv hm θ x z
  -- the map read in the coordinates
  have hG : ∀ e, ‖e‖ < ρ₁ →
      Φ ((fun e => P (p + e) - p) e) = Map.CenterManifold.splitMap A B f g (Φ e) :=
    fun e he => coordMap_conj hv hw hwv hm hθ0.ne' (hNcN e he.le)
  have hTay' : ∀ e, ‖e‖ ≤ ρ₀ →
      ‖nonlin P p M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4 := hTay
  -- the approximation of the centre manifold by `x ↦ (x 0)² k₂`
  set φ : ℝ¹ → (Fin m → ℝⁿ) := fun x => orbitEmb m θ L (x 0 ^ 2 • k₂) with hφdef
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  have hφ : HasStrictFDerivAt φ (0 : ℝ¹ →L[ℝ] (Fin m → ℝⁿ)) 0 := by
    have h1 : HasStrictFDerivAt (fun x : ℝ¹ => x 0)
        (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) 0 := by
      have e : (fun x : ℝ¹ => x 0) = ⇑(EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ) := by
        funext x; simp
      rw [e]
      exact ContinuousLinearMap.hasStrictFDerivAt
        (EuclideanSpace.proj (0 : Fin 1) : ℝ¹ →L[ℝ] ℝ)
    have h2 := ((h1.pow 2).smul_const k₂)
    have h3 := (orbitEmb m θ L).hasStrictFDerivAt.comp (0 : ℝ¹) h2
    convert h3 using 1
    ext x
    simp
  have hu1' : (fun x : ℝ¹ => x 0) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
    simpa using isBigO_coord_pow 1
  have he₂ : (fun x : ℝ¹ => x 0 • v + x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 1 :=
    (isBigO_smul_const hu1' v).add ((isBigO_smul_const (isBigO_coord_pow 2) k₂).trans
      (isBigO_norm_pow_of_le (by norm_num)))
  have hnorm0 : Tendsto (fun x : ℝ¹ => ‖x‖ ^ 1) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_norm_zero (E := ℝ¹)).pow 1
  have hev₂ : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + x 0 ^ 2 • k₂‖ ≤ ρ₁ := by
    have := (he₂.trans_tendsto hnorm0).eventually (Metric.closedBall_mem_nhds 0 hρ₁)
    filter_upwards [this] with x hx
    simpa using hx
  have hD : (fun x => φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)) =O[𝓝 0]
      fun x => ‖x‖ ^ 3 := by
    have hE := defect_expansion hρ₀ hTay' w v k₂ L (specProj v w) hLk
    refine (((orbitEmb m θ L).isBigO_comp _ _).trans hE).congr' ?_ EventuallyEq.rfl
    filter_upwards [hev₂] with x hx
    have hΨφ : coordInv v hm (x, φ x) = x 0 • v + x 0 ^ 2 • k₂ := by
      rw [coordInv_apply]
      show x 0 • v + orbitEmb m θ L (x 0 ^ 2 • k₂) ⟨0, hm⟩ = _
      rw [orbitEmb_zero]
    have hNe := hNcN _ hx
    have hfφ : f (x, φ x) = centreCoord w (nonlin P p M (x 0 • v + x 0 ^ 2 • k₂)) := by
      simp only [hfdef, cutF, hΨφ, hNe]; rfl
    have hgφ : g (x, φ x) =
        orbitEmb m θ L (specProj v w (nonlin P p M (x 0 • v + x 0 ^ 2 • k₂))) := by
      simp only [hgdef, cutG, hΨφ, hNe]; rfl
    have hc : (A x + f (x, φ x)) 0 = -x 0 + w (nonlin P p M (x 0 • v + x 0 ^ 2 • k₂)) := by
      rw [hfφ]; simp [hAdef, centreCoord_apply_zero]
    show orbitEmb m θ L _ = φ (A x + f (x, φ x)) - B (φ x) - g (x, φ x)
    rw [hgφ]
    simp only [hφdef]
    rw [hc, hBdef, orbitShift_orbitEmb hm hθ0.ne', L.map_smul (x 0 ^ 2) k₂]
    simp only [map_sub, map_smul]
  have happrox := Map.CenterManifold.isBigO_sub_of_defect hAs hA hB hθ0.le hfl hgl hf0 hg0
    (by simpa using hεa) hh hh0 hinv hφ hφ0 (by norm_num : 1 ≤ 3) hD (by simpa using hκq)
    (by simpa using hκ1)
  -- the stable coordinate of the centre manifold is `(x 0)² k₂ + O(‖x‖³)`
  set π₀ : (Fin m → ℝⁿ) →L[ℝ] ℝⁿ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin n)) ⟨0, hm⟩
    with hπ₀
  have hy : (fun x : ℝ¹ => h x ⟨0, hm⟩ - x 0 ^ 2 • k₂) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    refine ((π₀.isBigO_comp _ _).trans happrox).congr_left fun x => ?_
    show (h x - orbitEmb m θ L (x 0 ^ 2 • k₂)) ⟨0, hm⟩ = _
    rw [Pi.sub_apply, orbitEmb_zero]
  -- the reduced map
  have hred := reduced_expansion hρ₀ hTay' w v k₂ hy
  have hev : ∀ᶠ x : ℝ¹ in 𝓝 0, ‖x 0 • v + h x ⟨0, hm⟩‖ ≤ ρ₁ := by
    have hy1 : (fun x : ℝ¹ => h x ⟨0, hm⟩) =O[𝓝 0] fun x => ‖x‖ ^ 1 := by
      have := (hy.trans (isBigO_norm_pow_of_le (by norm_num : 1 ≤ 3))).add
        ((isBigO_smul_const (isBigO_coord_pow 2) k₂).trans
          (isBigO_norm_pow_of_le (by norm_num : 1 ≤ 2)))
      exact this.congr_left fun x => sub_add_cancel _ _
    have := (((isBigO_smul_const hu1' v).add hy1).trans_tendsto hnorm0).eventually
      (Metric.closedBall_mem_nhds 0 hρ₁)
    filter_upwards [this] with x hx
    simpa using hx
  set a := w (P₂ v v) with ha
  set b := w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v) with hb
  have hr : (fun x : ℝ¹ => Map.CenterManifold.reducedMap A f h x 0 -
      (-x 0 + a * x 0 ^ 2 + b * x 0 ^ 3)) =O[𝓝 0] fun x => ‖x‖ ^ 4 := by
    refine hred.congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with x hx
    have hΨh : coordInv v hm (x, h x) = x 0 • v + h x ⟨0, hm⟩ := by rw [coordInv_apply]
    have hfh : f (x, h x) = centreCoord w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) := by
      simp only [hfdef, cutF, hΨh, hNcN _ hx]; rfl
    have hc : Map.CenterManifold.reducedMap A f h x 0 =
        -x 0 + w (nonlin P p M (x 0 • v + h x ⟨0, hm⟩)) := by
      rw [Map.CenterManifold.reducedMap, hfh]; simp [hAdef, centreCoord_apply_zero]
    rw [hc]
    ring
  obtain ⟨C, hC⟩ := hr.bound
  obtain ⟨r₀, hr₀, hCb⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨Map.CenterManifold.reducedMap A f h, ⟨r₀ / 2, C, half_pos hr₀, fun y hy => ?_⟩,
    fun hr => localAsymptoticStable_of_translate
      (Map.CenterManifold.localAsymptoticStable_of_reduced hB hθ0.le hfl hgl hθ2 hh hh0 hinv
        (coordInv_coordMap hm θ) hρ₁ hG hr),
    fun hr hLS => Map.CenterManifold.unstable_of_reduced hh hh0 hinv hgraph hρ₁ hG hr
      (lyapunovStable_translate hLS)⟩
  have := hCb (show dist y 0 < r₀ by rw [dist_zero_right]; linarith)
  rw [Real.norm_eq_abs, norm_pow, norm_norm, NormalForm.norm_state1] at this
  exact this

/-- **Flip coefficient positive: asymptotically, not exponentially, stable.** Under the hypotheses
of `exists_reduced_map`, if the flip coefficient `a² + b` is positive
(`a = w P₂(v, v)`, `b = w P₃(v, v, v) + w (P₂(v, k₂) + P₂(k₂, v))`), the fixed point `p` of `P` is
locally asymptotically stable; it is never locally exponentially stable (the multiplier `−1`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_flipCoeff_pos {P : ℝⁿ → ℝⁿ}
    {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflate M v w ^ m‖ < 1) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hab : 0 < w (P₂ v v) ^ 2 + (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v))) :
    Map.LocalAsymptoticStable P p ∧ ¬ Map.LocallyExponentiallyStable P p := by
  obtain ⟨r, ⟨ρ, K', hρ, hb⟩, hS, -⟩ :=
    exists_reduced_map hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂
  refine ⟨hS (Map.flip_localAsymptoticStable hρ hab hb), ?_⟩
  have hv0 : v ≠ 0 := by rintro rfl; simp at hwv
  exact Map.not_locallyExponentiallyStable_of_eigenvector hP.hasFDerivAt hPp hv0
    (μ := -1) (by rw [hv, neg_one_smul]) (by norm_num)

/-- **Flip coefficient negative: unstable.** Under the hypotheses of `exists_reduced_map`, if the
flip coefficient `a² + b` is negative, the fixed point `p` of `P` is unstable. -/
@[tmio T, powerlib_foundation] theorem unstable_of_flipCoeff_neg {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {m : ℕ} (hm : 0 < m)
    (hLm : ‖deflate M v w ^ m‖ < 1) {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hab : w (P₂ v v) ^ 2 + (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v)) < 0) :
    Map.Unstable P p := by
  obtain ⟨r, ⟨ρ, K', hρ, hb⟩, -, hU⟩ :=
    exists_reduced_map hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂
  exact hU (Map.flip_unstable hρ hab hb)

/-- **Matrix form, stable side.** As `localAsymptoticStable_of_flipCoeff_pos`, with the
deflated monodromy given by a Schur stable matrix `Lm` (`Linear.op Lm = M + v wᵀ`,
`LTI.SchurStable Lm`; for a monodromy matrix `Mm`, `Lm = Mm + v wᵀ`, see
`multipliers_of_deflate`). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_flipCoeff_pos_matrix
    {P : ℝⁿ → ℝⁿ} {p : ℝⁿ} (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {Lm : Matrix (Fin n) (Fin n) ℝ}
    (hL : Linear.op Lm = deflate M v w) (hS : LTI.SchurStable Lm)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hab : 0 < w (P₂ v v) ^ 2 + (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v))) :
    Map.LocalAsymptoticStable P p ∧ ¬ Map.LocallyExponentiallyStable P p := by
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hLm
  exact localAsymptoticStable_of_flipCoeff_pos hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ hab

/-- **Matrix form, unstable side.** As `unstable_of_flipCoeff_neg`, with the deflated monodromy
given by a Schur stable matrix `Lm`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_flipCoeff_neg_matrix {P : ℝⁿ → ℝⁿ} {p : ℝⁿ}
    (hP : HasStrictFDerivAt P M p) (hPp : P p = p) (hv : M v = -v)
    (hw : ∀ e, w (M e) = -w e) (hwv : w v = 1) {Lm : Matrix (Fin n) (Fin n) ℝ}
    (hL : Linear.op Lm = deflate M v w) (hS : LTI.SchurStable Lm)
    {P₂ : ℝⁿ →L[ℝ] ℝⁿ →L[ℝ] ℝⁿ}
    {P₃ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))} {K ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hTay : ∀ e, ‖e‖ ≤ ρ₀ → ‖P (p + e) - p - M e - P₂ e e - P₃ (fun _ => e)‖ ≤ K * ‖e‖ ^ 4)
    {k₂ : ℝⁿ} (hk₂ : k₂ - M k₂ = specProj v w (P₂ v v))
    (hab : w (P₂ v v) ^ 2 + (w (P₃ (fun _ => v)) + w (P₂ v k₂ + P₂ k₂ v)) < 0) :
    Map.Unstable P p := by
  obtain ⟨m, hm, hLm⟩ := Map.exists_pow_norm_toEuclideanCLM_lt_one hS
  rw [hL] at hLm
  exact unstable_of_flipCoeff_neg hP hPp hv hw hwv hm hLm hρ₀ hTay hk₂ hab

end powerlib.Periodic.FlipReduction
