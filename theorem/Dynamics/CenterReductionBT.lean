import theorem.Dynamics.HopfDichotomy
import theorem.Dynamics.CenterManifoldSmooth
import theorem.NormalForm.BogdanovTakens
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Centre-manifold reduction to the Bogdanov–Takens normal form (foundation)

At an equilibrium of `ẋ = F(x)` on `ℝⁿ` whose linearization has a double zero eigenvalue with a
single Jordan block and the rest of its spectrum in the open left half plane, there is a locally
invariant, tangent centre manifold, and on it the field, read in the coordinates of the
Bogdanov–Takens chain and transformed by Kuznetsov's quadratic change of coordinates, is the
truncated normal form `ẏ₀ = y₁`, `ẏ₁ = a y₀² + b y₀ y₁` up to `o(‖y‖²)`, with Kuznetsov's
projection coefficients `a = ½⟨p₁, B(q₀, q₀)⟩`, `b = ⟨p₀, B(q₀, q₀)⟩ + ⟨p₁, B(q₀, q₁)⟩`
(`NormalForm.BogdanovTakens.coeffA`, `coeffB`): the coefficients of
`theorem/NormalForm/BogdanovTakens.lean` are those of the reduced dynamics.

Scope.
* Generic: `State n = ℝⁿ`, a field `F` of class `C²` with `F(0) = 0`, `A = DF(0)`,
  `B = D²F(0)`, a normalised Bogdanov–Takens chain `(q₀, q₁, p₀, p₁)` of `A`
  (`NormalForm.BogdanovTakens.IsBTChain`), the chart `ιw = w₀q₀ + w₁q₁`,
  `πx = (⟨p₀, x⟩, ⟨p₁, x⟩)` and the spectral projection `P = ιπ`. The dichotomy of the
  centre-manifold theorem is derived from two algebraic hypotheses: every real null vector of `A`
  is a multiple of `q₀` (a single Jordan block) and `det(sI − A) = s² r(s)` with `r` Hurwitz.
* Second order only: the reduced field is determined up to `o(‖w‖²)` (exact asymptotic
  statements, `IsLittleO` at `0`); its cubic terms, the parameter unfolding (versality), the
  fold, Hopf and homoclinic curves and the phase portraits are not stated here. The quadratic
  part of the centre manifold does not enter at this order (only its tangency). Nothing here
  describes a physical system (foundation).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed., 2004), §8.4 (Lemma 8.7: the
quadratic change of coordinates bringing `ẇ₀ = w₁ + G₀(w)`, `ẇ₁ = G₁(w)` to `ẏ₀ = y₁`,
`ẏ₁ = (b₂₀/2) y₀² + (a₂₀ + b₁₁) y₀ y₁`), §8.7 (the projection formulas for `a`, `b`), §5.1 (the
centre manifold); Carr, *Applications of Centre Manifold Theory* (1981), §2.1–§2.4;
Guckenheimer–Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector
Fields* (1983), §7.3 (Takens' normal form). The centre manifold is
`Dynamics.CenterManifold.exists_centerManifold_contDiff`
(`theorem/Dynamics/CenterManifoldSmooth.lean`); the
stable flow bound is `LyapunovPerron.norm_expFlow_le_of_hurwitz`
(`theorem/Dynamics/HopfDichotomy.lean`).

Results.
* `Dynamics.CenterManifold.taylor2_isLittleO`: a `C²` map has
  `F(x) = F(0) + DF(0)x + ½D²F(0)(x, x) + o(‖x‖²)` (mean value theorem and the symmetry of
  `D²F(0)`).
* Quadratic normal forms (any real normed space): `Dynamics.CenterManifold.quadMap`
  (`Φ(w) = w + H(w, w)`), `hasFDerivAt_quadMap`, **`quadMap_conj_isLittleO`**: if
  `G(w, w) + H(w, Lw) + H(Lw, w) = L H(w, w) + N(w, w)` (the homological equation), every field
  `g(w) = Lw + G(w, w) + o(‖w‖²)` satisfies `DΦ(w) g(w) − (LΦ(w) + N(Φ(w), Φ(w))) = o(‖w‖²)`.
* The planar Bogdanov–Takens normal form: `planeMono`, `btJ` (`Jw = (w₁, 0)`), `btNF`
  (`N(u, v) = (0, a u₀v₀ + b u₀v₁)`), `field_eq_btJ_add_btNF`, `btCoeffA`, `btCoeffB`
  (`a = G(e₁, e₁)₁`, `b = (G(e₁, e₂) + G(e₂, e₁))₁ + 2G(e₁, e₁)₀`), `btTransform` (Kuznetsov's
  `H`), `plane_bilin_diag`, `btTransform_homological`, **`btNormalForm_isLittleO`** (every planar
  `g(w) = Jw + G(w, w) + o(‖w‖²)` is the truncated normal form after `Φ`).
* `Dynamics.CenterManifold.chartField_expansion2`: for a tangent graph map (`h(u) = o(‖u‖)`) and
  `f(x) = Q(x, x) + o(‖x‖²)`, the chart field is `πAιy + πQ(ιy, ιy) + o(‖y‖²)`.
* The chart of a chain (`NormalForm.BogdanovTakens` namespace): `btι`, `btπ`, `btP`, `btι_apply`,
  `btπ_apply`, `IsBTChain.btπ_btι`, `IsBTChain.isChart`, `IsBTChain.btπ_map` (`πA = Jπ`),
  `IsBTChain.map_btι` (`Aι = ιJ`), `IsBTChain.isCommutingProjection`, `IsBTChain.btπ_comp`,
  `IsBTChain.map_map_btP` (`A²P = 0`), `IsBTChain.q₀_ne_zero`, `IsBTChain.btP_q₀`.
* The nilpotent flow: `expFlow_mul_eq_of_nilpotent` (`A²P = 0` ⇒ `e^{tA}P = P + tAP`),
  `norm_expFlow_mul_le_of_nilpotent` (`‖e^{tA}P‖ ≤ (‖P‖ + ‖AP‖/ε) e^{ε|t|}` for every `ε > 0`).
* The dichotomy: `IsBTChain.eq_zero_of_cmat`, `IsBTChain.stablePart_hurwitz`,
  **`IsBTChain.exists_dichotomy`** (`0 < ε < β`, the centre bound `K e^{ε|t|}`, the stable bound
  `K e^{−βt}`).
* **The reduction**: `btQuad` (`G(u, v) = ½πB(ιu, ιv)`), `btQuad_apply`, `btCoordChange`,
  `btCoeffA_btQuad`, `btCoeffB_btQuad` (the planar coefficients are Kuznetsov's projection
  formulas `coeffA F 0 q₀ p₁`, `coeffB F 0 q₀ q₁ p₀ p₁`), **`IsBTChain.btNormalForm_of_tangent`**
  (for every tangent graph map over the centre plane: `DΦ(w) πF(ιw + h(ιw)) −
  N_{a,b}(Φ(w)) = o(‖w‖²)`), **`IsBTChain.exists_centerManifold_btNormalForm`** (a locally
  invariant, Lipschitz, `C¹`, tangent centre manifold satisfying the invariance equation exists
  and carries this normal form; the `C¹` manifold of
  `Dynamics.CenterManifold.exists_centerManifold_contDiff`).
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold
open Set Filter Topology Asymptotics

/-! ## The second-order Taylor expansion of a `C²` map -/

section Taylor

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- **Second-order Taylor expansion of a `C²` map**:
`F(x) = F(0) + DF(0)x + ½ D²F(0)(x, x) + o(‖x‖²)`. -/
@[tmio T, powerlib_foundation] theorem taylor2_isLittleO {F : E → G} (hF : ContDiff ℝ 2 F) :
    (fun x => F x - (F 0 + fderiv ℝ F 0 x + (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0 x x))
      =o[𝓝 0] fun x => ‖x‖ ^ 2 := by
  set B := fderiv ℝ (fderiv ℝ F) 0 with hBdef
  have hsym : ∀ u v, B u v = B v u :=
    ContDiffAt.isSymmSndFDerivAt (hF.contDiffAt (x := 0)) (by simp)
  have hdF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDF : HasFDerivAt (fderiv ℝ F) B 0 := (hdF 0).hasFDerivAt
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  set g : E → G := fun x => F x - (F 0 + fderiv ℝ F 0 x + (1 / 2 : ℝ) • B x x) with hg
  have hg' : ∀ y, HasFDerivAt g (fderiv ℝ F y - fderiv ℝ F 0 - B y) y := by
    intro y
    have hb : HasFDerivAt (fun x => B x x) (B.precompR E y (ContinuousLinearMap.id ℝ E) +
        B.precompL E (ContinuousLinearMap.id ℝ E) y) y :=
      B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
    have h : HasFDerivAt (fun x => F x - (F 0 + fderiv ℝ F 0 x + (1 / 2 : ℝ) • B x x)) _ y :=
      (hF1 y).hasFDerivAt.sub (((hasFDerivAt_const (F 0) y).add
        (fderiv ℝ F 0).hasFDerivAt).add (hb.const_smul (1 / 2 : ℝ)))
    convert h using 1
    ext v
    simp only [sub_apply, add_apply, smul_apply, zero_add, ContinuousLinearMap.precompR,
      ContinuousLinearMap.precompL, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.id_apply]
    rw [hsym v y]
    module
  have hsmall : (fun y => fderiv ℝ F y - fderiv ℝ F 0 - B y) =o[𝓝 0] fun y => y := by
    have := hDF.isLittleO
    simpa using this
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (isLittleO_iff.mp hsmall hc)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with x hx
  have hx' : ‖x‖ < δ := by simpa using hx
  have hbound : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
      ‖fderiv ℝ F y - fderiv ℝ F 0 - B y‖ ≤ c * ‖x‖ := by
    intro y hy
    have hy' : ‖y‖ ≤ ‖x‖ := by simpa using hy
    have := hball y (by simpa using lt_of_le_of_lt hy' hx')
    calc _ ≤ c * ‖y‖ := this
      _ ≤ c * ‖x‖ := by gcongr
  have hmv := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y _ => (hg' y).hasFDerivWithinAt) hbound (Metric.mem_closedBall_self (norm_nonneg x))
    (show x ∈ Metric.closedBall (0 : E) ‖x‖ by simp)
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖g x‖ ≤ c * ‖x‖ * ‖x‖ := hmv
    _ = c * ‖x‖ ^ 2 := by ring

end Taylor

/-! ## Quadratic normal forms -/

section QuadraticNormalForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The quadratic near-identity map `w ↦ w + H(w, w)`. -/
def quadMap (H : F →L[ℝ] F →L[ℝ] F) (w : F) : F := w + H w w

@[tmio T, powerlib_foundation] theorem hasFDerivAt_quadMap (H : F →L[ℝ] F →L[ℝ] F) (w : F) :
    HasFDerivAt (quadMap H) (ContinuousLinearMap.id ℝ F + H w + H.flip w) w := by
  have hb := (H.hasFDerivAt (x := w)).clm_apply (hasFDerivAt_id w)
  rw [ContinuousLinearMap.comp_id, id] at hb
  rw [add_assoc]
  exact (hasFDerivAt_id w).add hb

/-- **A quadratic change of coordinates solving the homological equation conjugates a field to
its normal form at second order.** If `G(w, w) + H(w, Lw) + H(Lw, w) = L H(w, w) + N(w, w)` for
every `w`, then every field `g(w) = Lw + G(w, w) + o(‖w‖²)` is carried by `Φ(w) = w + H(w, w)` to
`y ↦ Ly + N(y, y)` up to `o(‖w‖²)`: `DΦ(w) g(w) − (LΦ(w) + N(Φ(w), Φ(w))) = o(‖w‖²)`. -/
@[tmio T, powerlib_foundation] theorem quadMap_conj_isLittleO {L : F →L[ℝ] F}
    {G H N : F →L[ℝ] F →L[ℝ] F} {g : F → F}
    (hhom : ∀ w, G w w + H w (L w) + H (L w) w = L (H w w) + N w w)
    (hg : (fun w => g w - (L w + G w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2) :
    (fun w => fderiv ℝ (quadMap H) w (g w) -
      (L (quadMap H w) + N (quadMap H w) (quadMap H w))) =o[𝓝 0] fun w => ‖w‖ ^ 2 := by
  set l := 𝓝 (0 : F)
  set ρ := fun w => g w - (L w + G w w) with hρ
  have hn1 : (fun w : F => w) =O[l] fun w => ‖w‖ := (isBigO_refl (fun w : F => w) l).norm_right
  have hL1 : (fun w => L w) =O[l] fun w => ‖w‖ := (L.isBigO_id l).trans hn1
  have hG2 : (fun w => G w w) =O[l] fun w => ‖w‖ ^ 2 :=
    (isBigO_bilin G (fun w => w) (fun w => w)).congr_right fun w => (sq _).symm
  have hH2 : (fun w => H w w) =O[l] fun w => ‖w‖ ^ 2 :=
    (isBigO_bilin H (fun w => w) (fun w => w)).congr_right fun w => (sq _).symm
  have h32 : (fun w : F => ‖w‖ ^ 3) =o[l] fun w => ‖w‖ ^ 2 := by
    simpa [l, nhdsWithin_univ] using norm_pow_isLittleO (E := F) (k := 2) (k' := 3)
      (by norm_num) Set.univ
  have h21 : (fun w : F => ‖w‖ ^ 2) =O[l] fun w => ‖w‖ := by
    have := norm_pow_isLittleO (E := F) (k := 1) (k' := 2) (by norm_num) Set.univ
    simpa [l, nhdsWithin_univ] using this.isBigO
  have hρ1 : ρ =O[l] fun w => ‖w‖ := hg.isBigO.trans h21
  -- the cubic and smaller terms
  have c1 : (fun w => H w (G w w)) =o[l] fun w => ‖w‖ ^ 2 :=
    (((isBigO_bilin H (fun w => w) fun w => G w w).trans (hn1.norm_left.mul hG2.norm_left))
      |>.congr_right fun w => by ring).trans_isLittleO h32
  have c2 : (fun w => H (G w w) w) =o[l] fun w => ‖w‖ ^ 2 :=
    (((isBigO_bilin H (fun w => G w w) fun w => w).trans (hG2.norm_left.mul hn1.norm_left))
      |>.congr_right fun w => by ring).trans_isLittleO h32
  have h3' : (fun w : F => ‖w‖ * ‖w‖ ^ 2) =O[l] fun w => ‖w‖ ^ 2 :=
    h32.isBigO.congr_left fun w => by ring
  have h3'' : (fun w : F => ‖w‖ ^ 2 * ‖w‖) =O[l] fun w => ‖w‖ ^ 2 :=
    h32.isBigO.congr_left fun w => by ring
  have c3 : (fun w => H w (ρ w)) =o[l] fun w => ‖w‖ ^ 2 :=
    (isBigO_bilin H (fun w => w) ρ).trans_isLittleO
      (((isBigO_refl (fun w => ‖w‖) l).mul_isLittleO hg.norm_left).trans_isBigO h3')
  have c4 : (fun w => H (ρ w) w) =o[l] fun w => ‖w‖ ^ 2 :=
    (isBigO_bilin H ρ (fun w => w)).trans_isLittleO
      ((hg.norm_left.mul_isBigO (isBigO_refl (fun w => ‖w‖) l)).trans_isBigO h3'')
  have c5 : (fun w => N w (H w w)) =o[l] fun w => ‖w‖ ^ 2 :=
    (((isBigO_bilin N (fun w => w) fun w => H w w).trans (hn1.norm_left.mul hH2.norm_left))
      |>.congr_right fun w => by ring).trans_isLittleO h32
  have c6 : (fun w => N (H w w) w) =o[l] fun w => ‖w‖ ^ 2 :=
    (((isBigO_bilin N (fun w => H w w) fun w => w).trans (hH2.norm_left.mul hn1.norm_left))
      |>.congr_right fun w => by ring).trans_isLittleO h32
  have h42 : (fun w : F => ‖w‖ ^ 4) =o[l] fun w => ‖w‖ ^ 2 := by
    simpa [l, nhdsWithin_univ] using norm_pow_isLittleO (E := F) (k := 2) (k' := 4)
      (by norm_num) Set.univ
  have c7 : (fun w => N (H w w) (H w w)) =o[l] fun w => ‖w‖ ^ 2 :=
    (((isBigO_bilin N (fun w => H w w) fun w => H w w).trans (hH2.norm_left.mul hH2.norm_left))
      |>.congr_right fun w => by ring).trans_isLittleO h42
  have hsum := ((((((hg.add c1).add c2).add c3).add c4).sub c5).sub c6).sub c7
  refine hsum.congr_left fun w => ?_
  rw [(hasFDerivAt_quadMap H w).fderiv]
  have hgw : g w = L w + G w w + ρ w := by simp [hρ]
  have hh := hhom w
  simp only [add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, quadMap, map_add, add_apply]
  rw [hgw]
  simp only [map_add, add_apply]
  rw [eq_comm, ← sub_eq_zero]
  have e : L w + G w w + ρ w + (H w (L w) + H w (G w w) + H w (ρ w)) +
        (H (L w) w + H (G w w) w + H (ρ w) w) -
      (L w + L (H w w) + (N w w + N (H w w) w + (N w (H w w) + N (H w w) (H w w)))) -
      (ρ w + H w (G w w) + H (G w w) w + H w (ρ w) + H (ρ w) w - N w (H w w) -
        N (H w w) w - N (H w w) (H w w)) =
      G w w + H w (L w) + H (L w) w - (L (H w w) + N w w) := by abel
  rw [e, hh, sub_self]

end QuadraticNormalForm

/-! ## Planar bilinear maps and the Bogdanov–Takens normal form at second order -/

section Planar

open powerlib.PhasePlane (mk mk_apply_zero mk_apply_one)

/-- The planar monomial bilinear map `(u, v) ↦ uᵢ vⱼ e`. -/
def planeMono (i j : Fin 2) (e : State 2) : State 2 →L[ℝ] State 2 →L[ℝ] State 2 :=
  (EuclideanSpace.proj i).smulRight ((EuclideanSpace.proj j).smulRight e)

@[tmio T, powerlib_foundation] theorem planeMono_apply (i j : Fin 2) (e u v : State 2) :
    planeMono i j e u v = (u i * v j) • e := by
  simp [planeMono, mul_smul]

/-- The nilpotent Jordan block on the plane, `J w = (w₁, 0)`. -/
def btJ : State 2 →L[ℝ] State 2 := (EuclideanSpace.proj (1 : Fin 2)).smulRight (mk 1 0)

@[tmio T, powerlib_foundation] theorem btJ_apply (w : State 2) : btJ w = mk (w 1) 0 := by
  ext i; fin_cases i <;> simp [btJ]

/-- The quadratic part `(u, v) ↦ (0, a u₀v₀ + b u₀v₁)` of the Bogdanov–Takens normal form. -/
def btNF (a b : ℝ) : State 2 →L[ℝ] State 2 →L[ℝ] State 2 :=
  planeMono 0 0 (mk 0 a) + planeMono 0 1 (mk 0 b)

/-- The truncated normal form at `β = 0` is `J y + N(y, y)`. -/
@[tmio T, powerlib_foundation] theorem field_eq_btJ_add_btNF (a b : ℝ) (y : State 2) :
    NormalForm.BogdanovTakens.field ⟨0, 0, a, b⟩ y = btJ y + btNF a b y y := by
  ext i; fin_cases i
  · simp [NormalForm.BogdanovTakens.field, btJ_apply, btNF, planeMono_apply]
  · simp [NormalForm.BogdanovTakens.field, btJ_apply, btNF, planeMono_apply]; ring

/-- The coefficient `a = G(e₁, e₁)₁` of a planar bilinear map `G` (`e₁ = (1, 0)`). -/
def btCoeffA (G : State 2 →L[ℝ] State 2 →L[ℝ] State 2) : ℝ := G (mk 1 0) (mk 1 0) 1

/-- The coefficient `b = (G(e₁, e₂) + G(e₂, e₁))₁ + 2 G(e₁, e₁)₀` of a planar bilinear map. -/
def btCoeffB (G : State 2 →L[ℝ] State 2 →L[ℝ] State 2) : ℝ :=
  G (mk 1 0) (mk 0 1) 1 + G (mk 0 1) (mk 1 0) 1 + 2 * G (mk 1 0) (mk 1 0) 0

/-- Kuznetsov's quadratic change of coordinates of the Bogdanov–Takens normal form:
`H(w, w) = (r w₀², g₂₀ w₀² + (g₁₁ + 2r) w₀w₁ + g₀₂ w₁²)`, `r = −(h₀₂ + g₁₁)/2`, with
`G(w, w) = (g₂₀ w₀² + g₁₁ w₀w₁ + g₀₂ w₁², h₂₀ w₀² + h₁₁ w₀w₁ + h₀₂ w₁²)`. -/
def btTransform (G : State 2 →L[ℝ] State 2 →L[ℝ] State 2) : State 2 →L[ℝ] State 2 →L[ℝ] State 2 :=
  planeMono 0 0 (mk (-(G (mk 0 1) (mk 0 1) 1 + (G (mk 1 0) (mk 0 1) 0 +
      G (mk 0 1) (mk 1 0) 0)) / 2) (G (mk 1 0) (mk 1 0) 0)) +
    planeMono 0 1 (mk 0 (-G (mk 0 1) (mk 0 1) 1)) + planeMono 1 1 (mk 0 (G (mk 0 1) (mk 0 1) 0))

/-- A planar bilinear map on the diagonal through its values on the basis. -/
@[tmio T, powerlib_foundation] theorem plane_bilin_diag (G : State 2 →L[ℝ] State 2 →L[ℝ] State 2)
    (w : State 2) :
    G w w = (w 0 * w 0) • G (mk 1 0) (mk 1 0) + (w 0 * w 1) • (G (mk 1 0) (mk 0 1) +
      G (mk 0 1) (mk 1 0)) + (w 1 * w 1) • G (mk 0 1) (mk 0 1) := by
  have hw : w = w 0 • mk 1 0 + w 1 • mk 0 1 := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hw]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_add, smul_smul]
  module

/-- **The homological equation of the Bogdanov–Takens normal form** is solved by
`btTransform G`: `G(w, w) + H(w, Jw) + H(Jw, w) = J H(w, w) + N(w, w)` with
`N = btNF a b`, `a = btCoeffA G`, `b = btCoeffB G`. -/
@[tmio T, powerlib_foundation] theorem btTransform_homological
    (G : State 2 →L[ℝ] State 2 →L[ℝ] State 2) (w : State 2) :
    G w w + btTransform G w (btJ w) + btTransform G (btJ w) w =
      btJ (btTransform G w w) + btNF (btCoeffA G) (btCoeffB G) w w := by
  rw [plane_bilin_diag G w]
  ext i; fin_cases i <;>
    simp [btTransform, btNF, btJ_apply, planeMono_apply, btCoeffA, btCoeffB] <;> ring

/-- **The Bogdanov–Takens normal form at second order.** A planar field
`g(w) = Jw + G(w, w) + o(‖w‖²)` is carried by `Φ(w) = w + H(w, w)`, `H = btTransform G`, to the
truncated normal form `ẏ₀ = y₁`, `ẏ₁ = a y₀² + b y₀y₁` up to `o(‖w‖²)`, with
`a = G(e₁, e₁)₁`, `b = (G(e₁, e₂) + G(e₂, e₁))₁ + 2 G(e₁, e₁)₀` (Kuznetsov's `a = b₂₀/2`,
`b = a₂₀ + b₁₁`). -/
@[tmio T, powerlib_foundation] theorem btNormalForm_isLittleO
    {G : State 2 →L[ℝ] State 2 →L[ℝ] State 2} {g : State 2 → State 2}
    (hg : (fun w => g w - (btJ w + G w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2) :
    (fun w => fderiv ℝ (quadMap (btTransform G)) w (g w) -
      NormalForm.BogdanovTakens.field ⟨0, 0, btCoeffA G, btCoeffB G⟩
        (quadMap (btTransform G) w)) =o[𝓝 0] fun w => ‖w‖ ^ 2 := by
  have h := quadMap_conj_isLittleO (N := btNF (btCoeffA G) (btCoeffB G))
    (btTransform_homological G) hg
  refine h.congr_left fun w => ?_
  rw [field_eq_btJ_add_btNF]

end Planar

/-! ## The second-order expansion of the reduced field -/

section Expansion2

variable {n m : ℕ}

/-- **The reduced field at second order.** For a tangent graph map (`h(u) = o(‖u‖)` on
`range P`) and `f(x) = Q(x, x) + o(‖x‖²)`, the chart field is
`πAιy + πQ(ιy, ιy) + o(‖y‖²)`: the quadratic part of the centre manifold does not enter. -/
@[tmio T, powerlib_foundation] theorem chartField_expansion2
    {A P : State n →L[ℝ] State n} {f h : State n → State n} {ι : State m →L[ℝ] State n}
    {π : State n →L[ℝ] State m} {Q : State n →L[ℝ] State n →L[ℝ] State n}
    (hc : IsChart P ι π) (hfQ : (fun x => f x - Q x x) =o[𝓝 0] fun x => ‖x‖ ^ 2)
    (hh : IsLittleOrder P h 1) :
    (fun y => chartField A f h ι π y - (π (A (ι y)) + π (Q (ι y) (ι y))))
      =o[𝓝 0] fun y => ‖y‖ ^ 2 := by
  set l := 𝓝 (0 : State m)
  have ht : Tendsto ι l (𝓝[Set.range P] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun y => ⟨ι y, hc.proj_ι y⟩⟩
    simpa using ι.continuous.tendsto 0
  have hι : (fun y => ι y) =O[l] fun y => ‖y‖ := (ι.isBigO_id l).trans
    ((isBigO_refl (fun y : State m => y) l).norm_right)
  have hh' : (fun y => h (ι y)) =o[l] fun y => ‖y‖ := by
    have h1 := (hh.comp_tendsto ht)
    have h2 : (fun y => ‖ι y‖ ^ (1 : ℝ)) =O[l] fun y => ‖y‖ := by
      simpa [Real.rpow_one] using hι.norm_left
    exact h1.trans_isBigO h2
  set x := fun y => ι y + h (ι y) with hx
  have hxO : x =O[l] fun y => ‖y‖ := hι.add hh'.isBigO
  have hxt : Tendsto x l (𝓝 0) :=
    hxO.trans_tendsto ((continuous_norm.tendsto' 0 0 norm_zero))
  have h1 : (fun y => f (x y) - Q (x y) (x y)) =o[l] fun y => ‖y‖ ^ 2 :=
    (hfQ.comp_tendsto hxt).trans_isBigO (hxO.norm_left.pow 2)
  have hO1 : (fun y : State m => ‖y‖) =O[l] fun y => ‖y‖ := isBigO_refl _ l
  have h2 : (fun y => Q (ι y) (h (ι y)) + Q (h (ι y)) (ι y) + Q (h (ι y)) (h (ι y)))
      =o[l] fun y => ‖y‖ ^ 2 := by
    have e1 : (fun y => Q (ι y) (h (ι y))) =o[l] fun y => ‖y‖ ^ 2 :=
      ((isBigO_bilin Q (fun y => ι y) fun y => h (ι y)).trans_isLittleO
        (hι.norm_left.mul_isLittleO hh'.norm_left)).congr_right fun y => by ring
    have e2 : (fun y => Q (h (ι y)) (ι y)) =o[l] fun y => ‖y‖ ^ 2 :=
      ((isBigO_bilin Q (fun y => h (ι y)) fun y => ι y).trans_isLittleO
        (hh'.norm_left.mul_isBigO hι.norm_left)).congr_right fun y => by ring
    have e3 : (fun y => Q (h (ι y)) (h (ι y))) =o[l] fun y => ‖y‖ ^ 2 :=
      ((isBigO_bilin Q (fun y => h (ι y)) fun y => h (ι y)).trans_isLittleO
        (hh'.norm_left.mul_isBigO hh'.isBigO.norm_left)).congr_right fun y => by ring
    exact (e1.add e2).add e3
  have hsum := (π.isBigO_comp _ l).trans_isLittleO (h1.add h2)
  refine hsum.congr_left fun y => ?_
  simp only [chartField, hx, map_add, map_sub, add_apply]
  abel

end Expansion2

end powerlib.Dynamics.CenterManifold

/-! ## The Bogdanov–Takens chart -/

namespace powerlib.NormalForm.BogdanovTakens

open Set Filter Topology Asymptotics
open scoped RealInnerProductSpace
open powerlib.Dynamics (State)
open powerlib.Dynamics.CenterManifold
open powerlib.PhasePlane (mk mk_apply_zero mk_apply_one)

section BTChart

variable {n : ℕ}

/-- The chart `ι w = w₀ q₀ + w₁ q₁` of the centre plane of a Bogdanov–Takens point. -/
def btι (q₀ q₁ : State n) : State 2 →L[ℝ] State n :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight q₀ + (EuclideanSpace.proj (1 : Fin 2)).smulRight q₁

/-- The coordinates `π x = (⟨p₀, x⟩, ⟨p₁, x⟩)` of the centre plane. -/
def btπ (p₀ p₁ : State n) : State n →L[ℝ] State 2 :=
  (innerSL ℝ p₀).smulRight (mk 1 0) + (innerSL ℝ p₁).smulRight (mk 0 1)

/-- The spectral projection `P = ιπ` onto the centre plane. -/
def btP (q₀ q₁ p₀ p₁ : State n) : State n →L[ℝ] State n := (btι q₀ q₁).comp (btπ p₀ p₁)

@[tmio T, powerlib_foundation] theorem btι_apply (q₀ q₁ : State n) (w : State 2) :
    btι q₀ q₁ w = w 0 • q₀ + w 1 • q₁ := by
  simp [btι]

@[tmio T, powerlib_foundation] theorem btπ_apply (p₀ p₁ x : State n) :
    btπ p₀ p₁ x = mk ⟪p₀, x⟫ ⟪p₁, x⟫ := by
  ext i; fin_cases i <;> simp [btπ]

variable {A : State n →L[ℝ] State n} {q₀ q₁ p₀ p₁ : State n}

@[tmio T, powerlib_foundation] theorem IsBTChain.btπ_btι (hc : IsBTChain A q₀ q₁ p₀ p₁)
    (w : State 2) : btπ p₀ p₁ (btι q₀ q₁ w) = w := by
  rw [btπ_apply, btι_apply]
  simp only [inner_add_right, real_inner_smul_right, hc.inner_p₀_q₀, hc.inner_p₀_q₁,
    hc.inner_p₁_q₀, hc.inner_p₁_q₁]
  ext i; fin_cases i <;> simp

/-- The chart of a normalised chain is a chart of `range P`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.isChart (hc : IsBTChain A q₀ q₁ p₀ p₁) :
    IsChart (btP q₀ q₁ p₀ p₁) (btι q₀ q₁) (btπ p₀ p₁) :=
  ⟨hc.btπ_btι, fun _ => rfl⟩

@[tmio T, powerlib_foundation] theorem IsBTChain.btπ_map (hc : IsBTChain A q₀ q₁ p₀ p₁)
    (x : State n) : btπ p₀ p₁ (A x) = btJ (btπ p₀ p₁ x) := by
  rw [btπ_apply, btπ_apply, btJ_apply, hc.inner_p₀_map, hc.inner_p₁_map]
  simp

@[tmio T, powerlib_foundation] theorem IsBTChain.map_btι (hc : IsBTChain A q₀ q₁ p₀ p₁)
    (w : State 2) : A (btι q₀ q₁ w) = btι q₀ q₁ (btJ w) := by
  rw [btι_apply, btι_apply, btJ_apply, map_add, map_smul, map_smul, hc.map_q₀, hc.map_q₁]
  simp

/-- `P = ιπ` is a projection commuting with `A`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.isCommutingProjection
    (hc : IsBTChain A q₀ q₁ p₀ p₁) : IsCommutingProjection A (btP q₀ q₁ p₀ p₁) :=
  ⟨fun x => by simp [btP, hc.btπ_btι],
    fun x => by simp only [btP, ContinuousLinearMap.comp_apply, hc.map_btι, hc.btπ_map]⟩

/-- The reduced linear part is the Jordan block: `π A ι = J`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.btπ_comp (hc : IsBTChain A q₀ q₁ p₀ p₁)
    (w : State 2) : btπ p₀ p₁ (A (btι q₀ q₁ w)) = btJ w := by
  rw [hc.btπ_map, hc.btπ_btι]

/-- `A² P = 0`: the centre plane carries the nilpotent block. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.map_map_btP (hc : IsBTChain A q₀ q₁ p₀ p₁) :
    A * (A * btP q₀ q₁ p₀ p₁) = 0 := by
  ext1 x
  show A (A (btι q₀ q₁ (btπ p₀ p₁ x))) = 0
  rw [hc.map_btι, hc.map_btι, btJ_apply, btJ_apply]
  simp [btι_apply]

@[tmio T, powerlib_foundation] theorem IsBTChain.q₀_ne_zero (hc : IsBTChain A q₀ q₁ p₀ p₁) :
    q₀ ≠ 0 := by
  rintro rfl
  have h := hc.inner_p₀_q₀
  simp at h

@[tmio T, powerlib_foundation] theorem IsBTChain.btP_q₀ (hc : IsBTChain A q₀ q₁ p₀ p₁) :
    btP q₀ q₁ p₀ p₁ q₀ = q₀ := by
  show btι q₀ q₁ (btπ p₀ p₁ q₀) = q₀
  rw [btπ_apply, btι_apply, hc.inner_p₀_q₀, hc.inner_p₁_q₀]
  simp

end BTChart

/-! ## The flow on a nilpotent block -/

section NilpotentFlow

open powerlib.Dynamics.LyapunovPerron

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E}

/-- **The flow on a nilpotent block.** If `A² P = 0`, then `e^{tA} P = P + t A P`. -/
@[tmio T, powerlib_foundation] theorem expFlow_mul_eq_of_nilpotent (hq : A * (A * P) = 0)
    (t : ℝ) : expFlow A t * P = P + t • (A * P) := by
  set F : ℝ → E →L[ℝ] E := fun s => P + s • (A * P) with hF
  have hG : ∀ s, HasDerivAt (fun s => expFlow A (-s) * F s) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => expFlow A (-s)) (-(expFlow A (-s) * A)) s := by
      have := (hasDerivAt_expFlow (A := A) (-s)).scomp s (hasDerivAt_neg s)
      rw [neg_one_smul] at this
      exact this
    have h2 : HasDerivAt F (A * P) s := by
      have := ((hasDerivAt_id s).smul_const (A * P)).const_add P
      simpa [hF] using this
    refine (h1.mul h2).congr_deriv ?_
    simp only [hF, neg_mul, mul_add, mul_smul_comm, mul_assoc, hq]
    simp
  have hconst : ∀ s, expFlow A (-s) * F s = expFlow A (-0) * F 0 := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt) (fun s => (hG s).deriv) s 0
  have h0 : expFlow A (-0) * F 0 = P := by simp [hF, expFlow_zero]
  calc expFlow A t * P = expFlow A t * (expFlow A (-t) * F t) := by rw [hconst, h0]
    _ = F t := by rw [← mul_assoc, expFlow_mul_neg, one_mul]

/-- The centre bound of a nilpotent block: for every `ε > 0`,
`‖e^{tA} P‖ ≤ (‖P‖ + ‖A P‖/ε) e^{ε|t|}`. -/
@[tmio T, powerlib_foundation] theorem norm_expFlow_mul_le_of_nilpotent (hq : A * (A * P) = 0)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖expFlow A t * P‖ ≤ (‖P‖ + ‖A * P‖ / ε) * Real.exp (ε * |t|) := by
  rw [expFlow_mul_eq_of_nilpotent hq t]
  have he1 : 1 ≤ Real.exp (ε * |t|) := Real.one_le_exp (by positivity)
  have he2 : ε * |t| ≤ Real.exp (ε * |t|) := by
    have := Real.add_one_le_exp (ε * |t|); linarith
  have ht : |t| ≤ Real.exp (ε * |t|) / ε := by rw [le_div_iff₀ hε]; linarith
  calc ‖P + t • (A * P)‖ ≤ ‖P‖ + |t| * ‖A * P‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖P‖ * Real.exp (ε * |t|) + Real.exp (ε * |t|) / ε * ‖A * P‖ := by
        gcongr; nlinarith [norm_nonneg P]
    _ = (‖P‖ + ‖A * P‖ / ε) * Real.exp (ε * |t|) := by ring

end NilpotentFlow

/-! ## The centre–stable dichotomy of a Bogdanov–Takens point -/

section Dichotomy

open Complex Polynomial Matrix
open powerlib.NormalForm.LyapunovCoefficient powerlib.Dynamics.LyapunovPerron

variable {n : ℕ} {A : State n →L[ℝ] State n} {q₀ q₁ p₀ p₁ : State n}

@[tmio T, powerlib_foundation] private theorem toC_add_I_smul_eq_zero {a b : State n}
    (h : toC a + I • toC b = 0) : a = 0 ∧ b = 0 := by
  constructor <;> ext k <;> have hk := congrFun h k <;>
    simp only [Pi.add_apply, Pi.smul_apply, toC_apply, smul_eq_mul, Pi.zero_apply] at hk
  · have := congrArg Complex.re hk; simpa using this
  · have := congrArg Complex.im hk; simpa using this

/-- **No complex null vector of `A` in `ker P`**: if every real null vector of `A` is a multiple
of `q₀`, a complex vector with `A w = 0` and `P w = 0` vanishes. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.eq_zero_of_cmat (hc : IsBTChain A q₀ q₁ p₀ p₁)
    (hker : ∀ v, A v = 0 → ∃ s : ℝ, v = s • q₀) {w : Fin n → ℂ} (hAw : cmat A *ᵥ w = 0)
    (hPw : cmat (btP q₀ q₁ p₀ p₁) *ᵥ w = 0) : w = 0 := by
  have e := toC_reV_add_imV w
  rw [← e, cmat_mulVec_toC_add_smul (A := A)] at hAw
  obtain ⟨h1, h2⟩ := toC_add_I_smul_eq_zero hAw
  obtain ⟨s, hs⟩ := hker _ h1
  obtain ⟨t, ht⟩ := hker _ h2
  have hP : cmat (btP q₀ q₁ p₀ p₁) *ᵥ w = w := by
    conv_lhs => rw [← e]
    rw [cmat_mulVec_toC_add_smul (A := btP q₀ q₁ p₀ p₁), hs, ht, map_smul, map_smul, hc.btP_q₀,
      ← hs, ← ht, e]
  rw [← hP, hPw]

/-- **The stable part is Hurwitz.** If `χ_A = X² r` with `r` Hurwitz and every real null vector
of `A` is a multiple of `q₀`, the complexified matrix of `B = A(1 − P) − P` has the eigenvalues
`−1` (on `range P`) and the roots of `r` (on `range (1 − P)`). -/
@[tmio T, powerlib_foundation] theorem IsBTChain.stablePart_hurwitz
    (hc : IsBTChain A q₀ q₁ p₀ p₁) (hker : ∀ v, A v = 0 → ∃ s : ℝ, v = s • q₀) {r : ℂ[X]}
    (hchar : (cmat A).charpoly = X ^ 2 * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) (μ : ℂ)
    (v : Fin n → ℂ) (hv : v ≠ 0)
    (he : cmat (A * (1 - btP q₀ q₁ p₀ p₁) - btP q₀ q₁ p₀ p₁) *ᵥ v = μ • v) : μ.re < 0 := by
  have hP := hc.isCommutingProjection
  set Pc := cmat (btP q₀ q₁ p₀ p₁) with hPc
  set Ac := cmat A with hAc
  have hPP : Pc * Pc = Pc := by
    rw [hPc, ← cmat_comp]; congr 1; ext1 x; exact hP.idem x
  have hAP : Pc * Ac = Ac * Pc := by
    rw [hPc, hAc, ← cmat_comp, ← cmat_comp]; congr 1; ext1 x; exact (hP.comm x).symm
  have hB : cmat (A * (1 - btP q₀ q₁ p₀ p₁) - btP q₀ q₁ p₀ p₁) = Ac * (1 - Pc) - Pc := by
    rw [cmat_sub, show A * (1 - btP q₀ q₁ p₀ p₁) = A.comp (1 - btP q₀ q₁ p₀ p₁) from rfl,
      cmat_comp, cmat_sub, show (1 : State n →L[ℝ] State n) = ContinuousLinearMap.id ℝ _ from rfl,
      cmat_id]
  rw [hB] at he
  set w := (1 - Pc) *ᵥ v with hwdef
  have hw : Ac *ᵥ w = μ • w := by
    have h := congrArg ((1 - Pc) *ᵥ ·) he
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
    have hm : (1 - Pc) * (Ac * (1 - Pc) - Pc) = Ac * (1 - Pc) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
        ← Matrix.mul_assoc, hAP, hPP]
      rw [Matrix.mul_assoc Ac Pc Pc, hPP]
      abel
    rw [hm, ← Matrix.mulVec_mulVec] at h
    exact h
  have hu : (μ + 1) • (Pc *ᵥ v) = 0 := by
    have h := congrArg (Pc *ᵥ ·) he
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
    have hm : Pc * (Ac * (1 - Pc) - Pc) = -Pc := by
      simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAP, hPP]
      rw [Matrix.mul_assoc Ac Pc Pc, hPP]
      abel
    rw [hm, Matrix.neg_mulVec] at h
    rw [add_smul, one_smul, ← h, neg_add_cancel]
  have hPw : Pc *ᵥ w = 0 := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
      Matrix.zero_mulVec]
  by_cases hw0 : w = 0
  · have hvP : Pc *ᵥ v = v := by
      have h : v - Pc *ᵥ v = 0 := by
        rw [← hw0, hwdef, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (sub_eq_zero.mp h).symm
    rw [hvP] at hu
    have h1 : μ + 1 = 0 := (smul_eq_zero.mp hu).resolve_right hv
    have h2 : μ = -1 := by linear_combination h1
    rw [h2]; norm_num
  · have hdet : (cmat A).charpoly.eval μ = 0 := by
      rw [Matrix.eval_charpoly]
      refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, ?_⟩
      rw [Matrix.sub_mulVec, ← hAc, hw]
      ext i
      simp [Matrix.scalar_apply]
    rw [hchar, eval_mul] at hdet
    rcases mul_eq_zero.mp hdet with h2 | h2
    · exfalso
      have hμ : μ = 0 := by simpa using h2
      rw [hμ, zero_smul] at hw
      exact hw0 (hc.eq_zero_of_cmat hker hw hPw)
    · exact hr μ h2

/-- **The centre–stable dichotomy of a Bogdanov–Takens point.** If `(q₀, q₁, p₀, p₁)` is a
normalised chain of `A`, every real null vector of `A` is a multiple of `q₀` and `χ_A = X² r`
with `r` Hurwitz, the projection `P = ιπ` of the chart has the dichotomy of the centre-manifold
theorem: `‖e^{tA} P‖ ≤ K e^{ε|t|}` for all `t` and `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` for `t ≥ 0`, with
`0 < ε < β` (the centre flow `P + tAP` grows linearly). -/
@[tmio T, powerlib_foundation] theorem IsBTChain.exists_dichotomy (hc : IsBTChain A q₀ q₁ p₀ p₁)
    (hker : ∀ v, A v = 0 → ∃ s : ℝ, v = s • q₀) {r : ℂ[X]}
    (hchar : (cmat A).charpoly = X ^ 2 * r) (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ K ε β : ℝ, 0 < ε ∧ ε < β ∧
      (∀ t, ‖expFlow A t * btP q₀ q₁ p₀ p₁‖ ≤ K * Real.exp (ε * |t|)) ∧
      ∀ t, 0 ≤ t → ‖expFlow A t * (1 - btP q₀ q₁ p₀ p₁)‖ ≤ K * Real.exp (-(β * t)) := by
  have hP := hc.isCommutingProjection
  set P := btP q₀ q₁ p₀ p₁ with hPdef
  have hPP : P * P = P := by ext1 x; exact hP.idem x
  have hAP : P * A = A * P := by ext1 x; exact (hP.comm x).symm
  set B := A * (1 - P) - P with hB
  obtain ⟨K₂, a, ha, hK₂⟩ := norm_expFlow_le_of_hurwitz (B := B)
    (hc.stablePart_hurwitz hker hchar hr)
  have hε : 0 < a / 2 := by positivity
  set K₁ := ‖P‖ + ‖A * P‖ / (a / 2)
  have hcomm : Commute A B := by
    simp only [Commute, SemiconjBy, hB, mul_sub, sub_mul, mul_one, mul_assoc, hAP]
  have hBS : B * (1 - P) = A * (1 - P) := by
    simp only [hB, mul_sub, sub_mul, mul_one, mul_assoc, hPP, sub_self]
    abel
  refine ⟨max K₁ (K₂ * ‖1 - P‖), a / 2, a, hε, by linarith, fun t => ?_, fun t ht => ?_⟩
  · calc ‖expFlow A t * P‖ ≤ K₁ * Real.exp (a / 2 * |t|) :=
          norm_expFlow_mul_le_of_nilpotent hc.map_map_btP hε t
      _ ≤ max K₁ (K₂ * ‖1 - P‖) * Real.exp (a / 2 * |t|) := by
        gcongr; exact le_max_left _ _
  · rw [expFlow_mul_eq_of_mul_eq hcomm hBS t]
    calc ‖expFlow B t * (1 - P)‖ ≤ ‖expFlow B t‖ * ‖1 - P‖ := norm_mul_le _ _
      _ ≤ K₂ * Real.exp (-(a * t)) * ‖1 - P‖ := by gcongr; exact hK₂ t ht
      _ ≤ max K₁ (K₂ * ‖1 - P‖) * Real.exp (-(a * t)) := by
        rw [mul_right_comm]; gcongr; exact le_max_right _ _

end Dichotomy

/-! ## The reduction to the Bogdanov–Takens normal form -/

section Reduction

open Polynomial
open powerlib.NormalForm.LyapunovCoefficient powerlib.Dynamics.LyapunovPerron

variable {n : ℕ} {q₀ q₁ p₀ p₁ : State n}

/-- The quadratic part of the reduced field in the chart, `G(u, v) = ½ π D²F(0)(ιu, ιv)`. -/
def btQuad (F : State n → State n) (q₀ q₁ p₀ p₁ : State n) :
    State 2 →L[ℝ] State 2 →L[ℝ] State 2 :=
  (1 / 2 : ℝ) • ((ContinuousLinearMap.compL ℝ (State 2) (State n) (State 2) (btπ p₀ p₁)).comp
    ((fderiv ℝ (fderiv ℝ F) 0).bilinearComp (btι q₀ q₁) (btι q₀ q₁)))

@[tmio T, powerlib_foundation] theorem btQuad_apply (F : State n → State n) (u v : State 2) :
    btQuad F q₀ q₁ p₀ p₁ u v =
      (1 / 2 : ℝ) • btπ p₀ p₁ (fderiv ℝ (fderiv ℝ F) 0 (btι q₀ q₁ u) (btι q₀ q₁ v)) := by
  simp [btQuad]

/-- Kuznetsov's quadratic change of coordinates of the reduced field, `Φ(w) = w + H(w, w)`,
`H = btTransform (btQuad F …)`. -/
def btCoordChange (F : State n → State n) (q₀ q₁ p₀ p₁ : State n) : State 2 → State 2 :=
  quadMap (btTransform (btQuad F q₀ q₁ p₀ p₁))

@[tmio T, powerlib_foundation] private theorem btι_e0 : btι q₀ q₁ (mk 1 0) = q₀ := by
  simp [btι_apply]

@[tmio T, powerlib_foundation] private theorem btι_e1 : btι q₀ q₁ (mk 0 1) = q₁ := by
  simp [btι_apply]

/-- The planar coefficient `a` of the chart quadratic part is Kuznetsov's `a = ½⟨p₁, B(q₀, q₀)⟩`. -/
@[tmio T, powerlib_foundation] theorem btCoeffA_btQuad (F : State n → State n) :
    btCoeffA (btQuad F q₀ q₁ p₀ p₁) = coeffA F 0 q₀ p₁ := by
  rw [btCoeffA, btQuad_apply, btι_e0, coeffA, btπ_apply]
  simp; ring

/-- For a symmetric second derivative the planar coefficient `b` of the chart quadratic part is
Kuznetsov's `b = ⟨p₀, B(q₀, q₀)⟩ + ⟨p₁, B(q₀, q₁)⟩`. -/
@[tmio T, powerlib_foundation] theorem btCoeffB_btQuad {F : State n → State n}
    (hsym : ∀ u v, fderiv ℝ (fderiv ℝ F) 0 u v = fderiv ℝ (fderiv ℝ F) 0 v u) :
    btCoeffB (btQuad F q₀ q₁ p₀ p₁) = coeffB F 0 q₀ q₁ p₀ p₁ := by
  rw [btCoeffB, btQuad_apply, btQuad_apply, btQuad_apply, btι_e0, btι_e1, coeffB, btπ_apply,
    btπ_apply, btπ_apply, hsym q₁ q₀]
  simp; ring

/-- **The reduced field of a Bogdanov–Takens point at second order, for every tangent centre
manifold.** Let `F` be `C²` with `F(0) = 0` and a normalised chain `(q₀, q₁, p₀, p₁)` of
`DF(0)`, and `h` any graph map over the centre plane with `h(u) = o(‖u‖)`. In the coordinates
`w = π x` the field on the graph, `g(w) = π F(ιw + h(ιw))`, is carried by Kuznetsov's quadratic
change of coordinates `Φ = btCoordChange F …` to the truncated normal form
`ẏ₀ = y₁`, `ẏ₁ = a y₀² + b y₀y₁` up to `o(‖w‖²)`, with `a = coeffA F 0 q₀ p₁`,
`b = coeffB F 0 q₀ q₁ p₀ p₁` (Kuznetsov's projection formulas): `DΦ(w) g(w) − N(Φ(w)) = o(‖w‖²)`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.btNormalForm_of_tangent {F : State n → State n}
    (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0) (hc : IsBTChain (fderiv ℝ F 0) q₀ q₁ p₀ p₁)
    {h : State n → State n} (hgm : IsGraphMap (btP q₀ q₁ p₀ p₁) h)
    (hh : IsLittleOrder (btP q₀ q₁ p₀ p₁) h 1) :
    (fun w => fderiv ℝ (btCoordChange F q₀ q₁ p₀ p₁) w
        (btπ p₀ p₁ (F (btι q₀ q₁ w + h (btι q₀ q₁ w)))) -
      field ⟨0, 0, coeffA F 0 q₀ p₁, coeffB F 0 q₀ q₁ p₀ p₁⟩ (btCoordChange F q₀ q₁ p₀ p₁ w))
      =o[𝓝 0] fun w => ‖w‖ ^ 2 := by
  set A := fderiv ℝ F 0 with hA
  have hsym : ∀ u v, fderiv ℝ (fderiv ℝ F) 0 u v = fderiv ℝ (fderiv ℝ F) 0 v u :=
    ContDiffAt.isSymmSndFDerivAt (hF.contDiffAt (x := 0)) (by simp)
  have hfQ : (fun x => (F x - A x) - ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) 0) x x)
      =o[𝓝 0] fun x => ‖x‖ ^ 2 :=
    (taylor2_isLittleO hF).congr_left fun x => by
      rw [hF0, zero_add]; simp only [smul_apply]; abel
  have hexp := chartField_expansion2 (A := A) hc.isChart hfQ hh
  have hπh : ∀ u, btπ p₀ p₁ (h u) = 0 := fun u => by
    rw [← hc.isChart.π_proj, hgm.proj_apply, map_zero]
  have hg : (fun w => btπ p₀ p₁ (F (btι q₀ q₁ w + h (btι q₀ q₁ w))) -
      (btJ w + btQuad F q₀ q₁ p₀ p₁ w w)) =o[𝓝 0] fun w => ‖w‖ ^ 2 := by
    refine hexp.congr_left fun w => ?_
    simp only [chartField, map_add, map_sub, hc.btπ_comp, btQuad_apply, smul_apply, map_smul]
    rw [hc.btπ_map (h (btι q₀ q₁ w)), hπh, map_zero]
    abel
  have hnf := btNormalForm_isLittleO hg
  rw [btCoeffA_btQuad, btCoeffB_btQuad hsym] at hnf
  exact hnf

/-- **Centre-manifold reduction to the Bogdanov–Takens normal form.** Let `F` be `C²` with
`F(0) = 0`, `(q₀, q₁, p₀, p₁)` a normalised chain of `A = DF(0)`, every real null vector of `A` a
multiple of `q₀`, and `χ_A = X² r` with `r` Hurwitz. Then there are `ρ > 0` and a Lipschitz, `C¹`
graph map `h` over the centre plane, tangent (`h(u) = o(‖u‖)`), satisfying the invariance
equation near `0` and locally invariant (solutions of `ẋ = F(x)` starting on its graph stay on it
while they stay in the ball of radius `ρ`), and on it
the field in the coordinates `w = π x` is the truncated Bogdanov–Takens normal form with
Kuznetsov's coefficients up to `o(‖w‖²)` after the change of coordinates `btCoordChange F …`. -/
@[tmio T, powerlib_foundation] theorem IsBTChain.exists_centerManifold_btNormalForm
    {F : State n → State n} (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (hc : IsBTChain (fderiv ℝ F 0) q₀ q₁ p₀ p₁)
    (hker : ∀ v, fderiv ℝ F 0 v = 0 → ∃ s : ℝ, v = s • q₀) {r : ℂ[X]}
    (hchar : (cmat (fderiv ℝ F 0)).charpoly = X ^ 2 * r)
    (hr : ∀ s : ℂ, r.eval s = 0 → s.re < 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap (btP q₀ q₁ p₀ p₁) h ∧
      LipschitzWith L h ∧ IsLittleOrder (btP q₀ q₁ p₀ p₁) h 1 ∧ ContDiff ℝ 1 h ∧
      IsInvariantGraph (fderiv ℝ F 0) (btP q₀ q₁ p₀ p₁) (fun x => F x - fderiv ℝ F 0 x) h ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ F t₀ t₁ →
        φ t₀ ∈ graph (btP q₀ q₁ p₀ p₁) h → (∀ t ∈ Set.Icc t₀ t₁, ‖φ t‖ < ρ) →
          ∀ t ∈ Set.Icc t₀ t₁, φ t ∈ graph (btP q₀ q₁ p₀ p₁) h) ∧
      (fun w => fderiv ℝ (btCoordChange F q₀ q₁ p₀ p₁) w
          (btπ p₀ p₁ (F (btι q₀ q₁ w + h (btι q₀ q₁ w)))) -
        field ⟨0, 0, coeffA F 0 q₀ p₁, coeffB F 0 q₀ q₁ p₀ p₁⟩ (btCoordChange F q₀ q₁ p₀ p₁ w))
        =o[𝓝 0] fun w => ‖w‖ ^ 2 := by
  obtain ⟨K, ε, β, hε, hεβ, hcen, hst⟩ := hc.exists_dichotomy hker hchar hr
  set A := fderiv ℝ F 0 with hA
  have hf : ContDiff ℝ 1 (fun x => F x - A x) := (hF.of_le (by norm_num)).sub A.contDiff
  have hf0 : (fun x => F x - A x) 0 = 0 := by simp [hF0]
  have hDf : fderiv ℝ (fun x => F x - A x) 0 = 0 := by
    have h := ((hF.differentiable (by norm_num)) 0).hasFDerivAt.sub A.hasFDerivAt
    change fderiv ℝ (F - ⇑A) 0 = 0
    rw [h.fderiv, ← hA, sub_self]
  obtain ⟨ρ, hρ, h, L, hgm, hL, hh, hC1, -, hieq, hinv⟩ :=
    exists_centerManifold_contDiff hc.isCommutingProjection hε.le hεβ hcen hst hf hf0 hDf
  have hfull : fullField A (fun x => F x - A x) = F := by
    funext x; simp [fullField]
  rw [hfull] at hinv
  exact ⟨ρ, hρ, h, L, hgm, hL, hh, hC1, hieq, hinv, hc.btNormalForm_of_tangent hF hF0 hgm hh⟩

end Reduction

end powerlib.NormalForm.BogdanovTakens
