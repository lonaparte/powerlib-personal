import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Calculus

/-! # Weak foci: polynomial Lyapunov functions at a Hopf point (foundation)

Local asymptotic stability at a Hopf point, where the linearization is not Hurwitz, from explicit
polynomial Lyapunov functions that solve the homological equations of the normal form.

Scope.
* Autonomous continuous-time ODE `ẋ = f x` on `Dynamics.State n = EuclideanSpace ℝ (Fin n)` with
  a `C¹` field supplied by the caller; no input, delay, switching or time variation.
  `V̇ x = fderiv ℝ V x (f x)`. Behaviour is LeanForControl's `LocalAsymptoticStable` (Lyapunov
  stability plus convergence of the forward-complete solutions that start in a ball).
* Nothing here describes a physical system: every statement is a generic implication about an
  arbitrary field, function or polynomial, a foundation result. No model family is defined or
  fixed here; model families apply these criteria inside their own connection proofs
  (`theorem/GFM/VSMLPFHopf.lean`, `theorem/GFL/RatePLLHopf.lean`,
  `theorem/GFL/PowerLoop/QuasiStaticFoldHopf.lean`).

Source: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.1 (local Lyapunov theorem) and Theorem 4.4
(LaSalle); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4 (first
Lyapunov coefficient, homological equations) for the construction. The coefficients of
`hopfW3`, `hopfW4`, `hopfH2` were computed with SymPy (untrusted) and are checked by the kernel
(`field_simp; ring`).

Results.
* The strict Lyapunov theorem on a punctured ball that the weak-focus criterion below applies is
  `Dynamics.localAsymptoticStable_of_lie_neg` (`theorem/Dynamics/Lyapunov.lean`): no global
  sublevel set `{V ≤ c}` has to be compact, so `V` may be a polynomial that is indefinite far from
  the equilibrium.
* Polynomials in three real variables. `poly3 l a b c = Σ κ a^i b^j c^k` over a list
  `l` of terms `(κ, i, j, k)`, its directional derivative `dpoly3`, the derivative of
  `z ↦ poly3 l (ℓa z) (ℓb z) (ℓc z)` for continuous linear functionals `ℓa, ℓb, ℓc`
  (`fderiv_poly3_apply`, `contDiff_poly3`), linearity of the derivative in the
  direction (`dpoly3_add_smul`) and the bounds of homogeneous polynomials:
  `|poly3 l a b c| ≤ (Σ |κ|) N^d` for degree `d`, and
  `|dpoly3 l a b c da db dc| ≤ (Σ |κ| (d + 1)) N^d` for degree `d + 1`, when `|a|, |b|, |c| ≤ N`
  and `|da|, |db|, |dc| ≤ 1` (`abs_poly3_le`, `abs_dpoly3_le`). Weighted bounds
  (`isBigO_poly3_weight`): if every monomial `a^i b^j c^k` has weight `i + j + 2k ≥ k₀`, the
  polynomial is `O(s^{k₀})` when `a, b = O(s)`, `c = O(s²)` and `s → 0` (the weights of a
  centre-manifold expansion).
* A Hopf point with one stable real eigenvalue. In coordinates `w = (a, b, c)` the normal form is
  `ȧ = b`, `ḃ = −H a − G`, `ċ = −λ c − G` (`H, λ > 0`): the linearization has eigenvalues
  `±i√H` and `−λ`, and one scalar `G = g₂ ξ² + g₃ ξ³ + O(ξ⁴)` of `ξ = (λ a − b + c)/(H + λ²)`
  forces the oscillator and the stable mode. The explicit cubic and quartic polynomials
  `W₃ = WeakFocus.hopfW3`, `W₄ = WeakFocus.hopfW4` solve the homological equations
  (`hopfW3_homological`, `hopfW4_homological`), so that for
  `W = H a² + b² + c² + W₃ + W₄`, up to order four,
  `Ẇ = −2λ (c − h₂(a, b))² − κ / (4 H² λ (H + λ²)² (4H + λ²)) · (H a² + b²)²`, where
  `h₂ = WeakFocus.hopfH2` is the quadratic part of the centre manifold and
  `κ = 2 g₂² (8H + λ²) − 3 H λ g₃ (4H + λ²)` (`hopfCoeff`). The term `−2λ(c − h₂)²`
  absorbs the centre manifold; no centre-manifold theorem is used.
* `localAsymptoticStable_of_hopf_weakFocus`: a `C¹` field conjugate, through an
  injective linear map `T`, to this normal form with an `O(ξ⁴)` remainder has a locally
  asymptotically stable origin when `κ > 0`. The linearization is not Hurwitz, so the origin is a
  weak focus: asymptotically, not exponentially, stable. (`κ > 0` says that the averaged radial
  rate of the normal form is negative; by a SymPy computation outside the library it is the sign
  condition `l₁ < 0` on the first Lyapunov coefficient. Only the Lyapunov argument is formal.)
* Planar sine–Liénard weak focus (`φ̇ = αw + βN(φ)`, `ẇ = −Aφ + N(φ)` with
  `N(φ) = A(φ − sin φ) + B(1 − cos φ)`, `hopfN`, and its cubic Taylor polynomial `hopfN3`):
  `hopfN_sub_hopfN3_isBigO` (`N − N₃ = O(φ⁴)`); the polynomial `lyapPoly` (quadratic form plus six
  cubic / quartic monomials), its partial derivatives `lyapPolyφ`, `lyapPolyw` and its derivative
  and smoothness in the coordinates `φ = z₀`, `w = z₁ − b z₀` (`hasFDerivAt_lyapPoly`,
  `contDiff_lyapPoly`); the normal-form Lyapunov polynomial `hopfW` (`hopfWφ`, `hopfWw`) with
  `hopf_lie_poly`: along the cubic truncation its derivative is `−κ (φ² + (α/A) w²)²` up to eight
  monomials of degree five and six, `κ = hopfκ A B β = −β(A² + B²)/(16A)` (coefficients from
  SymPy, checked by `field_simp; ring`).
-/

noncomputable section
namespace powerlib.Dynamics.Degenerate
open Set Filter Topology Metric
open scoped Pointwise

/-! ## Polynomials in three real variables -/

/-- The polynomial `Σ κ a^i b^j c^k` over a list of terms `(κ, i, j, k)`. -/
def poly3 : List (ℝ × ℕ × ℕ × ℕ) → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | t :: l, a, b, c => t.1 * (a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2) + poly3 l a b c

/-- The derivative of `poly3 l` at `(a, b, c)` in the direction `(da, db, dc)`. -/
def dpoly3 : List (ℝ × ℕ × ℕ × ℕ) → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _, _, _ => 0
  | t :: l, a, b, c, da, db, dc =>
      t.1 * ((t.2.1 : ℝ) * a ^ (t.2.1 - 1) * b ^ t.2.2.1 * c ^ t.2.2.2 * da +
        (t.2.2.1 : ℝ) * a ^ t.2.1 * b ^ (t.2.2.1 - 1) * c ^ t.2.2.2 * db +
        (t.2.2.2 : ℝ) * a ^ t.2.1 * b ^ t.2.2.1 * c ^ (t.2.2.2 - 1) * dc) +
      dpoly3 l a b c da db dc

@[tmio T, simp, powerlib_foundation] theorem poly3_nil (a b c : ℝ) : poly3 [] a b c = 0 := rfl

@[tmio T, simp, powerlib_foundation] theorem poly3_cons (t : ℝ × ℕ × ℕ × ℕ) (l : List (ℝ × ℕ × ℕ × ℕ))
    (a b c : ℝ) :
    poly3 (t :: l) a b c = t.1 * (a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2) + poly3 l a b c := rfl

@[tmio T, simp, powerlib_foundation] theorem dpoly3_nil (a b c da db dc : ℝ) :
    dpoly3 [] a b c da db dc = 0 := rfl

@[tmio T, simp, powerlib_foundation] theorem dpoly3_cons (t : ℝ × ℕ × ℕ × ℕ) (l : List (ℝ × ℕ × ℕ × ℕ))
    (a b c da db dc : ℝ) :
    dpoly3 (t :: l) a b c da db dc =
      t.1 * ((t.2.1 : ℝ) * a ^ (t.2.1 - 1) * b ^ t.2.2.1 * c ^ t.2.2.2 * da +
        (t.2.2.1 : ℝ) * a ^ t.2.1 * b ^ (t.2.2.1 - 1) * c ^ t.2.2.2 * db +
        (t.2.2.2 : ℝ) * a ^ t.2.1 * b ^ t.2.2.1 * c ^ (t.2.2.2 - 1) * dc) +
      dpoly3 l a b c da db dc := rfl

/-- The derivative is linear in the direction. -/
@[tmio T, powerlib_foundation] theorem dpoly3_add_smul (l : List (ℝ × ℕ × ℕ × ℕ))
    (a b c da db dc s ea eb ec : ℝ) :
    dpoly3 l a b c (da + s * ea) (db + s * eb) (dc + s * ec) =
      dpoly3 l a b c da db dc + s * dpoly3 l a b c ea eb ec := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [dpoly3_cons, ih]; ring

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `z ↦ poly3 l (ℓa z) (ℓb z) (ℓc z)` has the derivative `dpoly3`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_poly3 (l : List (ℝ × ℕ × ℕ × ℕ))
    (ℓa ℓb ℓc : E →L[ℝ] ℝ) (z : E) :
    ∃ L : E →L[ℝ] ℝ, HasFDerivAt (fun z => poly3 l (ℓa z) (ℓb z) (ℓc z)) L z ∧
      ∀ v, L v = dpoly3 l (ℓa z) (ℓb z) (ℓc z) (ℓa v) (ℓb v) (ℓc v) := by
  induction l with
  | nil => exact ⟨0, hasFDerivAt_const 0 z, fun v => by simp⟩
  | cons t l ih =>
    obtain ⟨L, hL, hLv⟩ := ih
    have hm := ((((ℓa.hasFDerivAt (x := z)).pow t.2.1).mul
      ((ℓb.hasFDerivAt (x := z)).pow t.2.2.1)).mul
        ((ℓc.hasFDerivAt (x := z)).pow t.2.2.2)).const_mul t.1
    refine ⟨_, hm.add hL, fun v => ?_⟩
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, hLv,
      dpoly3_cons]
    ring

@[tmio T, powerlib_foundation] theorem fderiv_poly3_apply (l : List (ℝ × ℕ × ℕ × ℕ))
    (ℓa ℓb ℓc : E →L[ℝ] ℝ) (z v : E) :
    fderiv ℝ (fun z => poly3 l (ℓa z) (ℓb z) (ℓc z)) z v =
      dpoly3 l (ℓa z) (ℓb z) (ℓc z) (ℓa v) (ℓb v) (ℓc v) := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_poly3 l ℓa ℓb ℓc z
  rw [hL.fderiv, hLv]

@[tmio T, powerlib_foundation] theorem contDiff_poly3 (l : List (ℝ × ℕ × ℕ × ℕ))
    (ℓa ℓb ℓc : E →L[ℝ] ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun z => poly3 l (ℓa z) (ℓb z) (ℓc z)) := by
  induction l with
  | nil => exact contDiff_const
  | cons t l ih =>
    exact (contDiff_const.mul (((ℓa.contDiff.pow _).mul (ℓb.contDiff.pow _)).mul
      (ℓc.contDiff.pow _))).add ih

end Deriv

/-! ### Bounds of homogeneous polynomials -/

@[tmio T] private theorem abs_mono_le {a b c N : ℝ} (ha : |a| ≤ N) (hb : |b| ≤ N) (hc : |c| ≤ N)
    (i j k : ℕ) : |a ^ i * b ^ j * c ^ k| ≤ N ^ (i + j + k) := by
  have hN : 0 ≤ N := (abs_nonneg a).trans ha
  rw [pow_add, pow_add, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
  gcongr

/-- A homogeneous polynomial of degree `d` is at most `(Σ |κ|) N^d` on `|a|, |b|, |c| ≤ N`. -/
@[tmio T, powerlib_foundation] theorem abs_poly3_le (l : List (ℝ × ℕ × ℕ × ℕ)) (d : ℕ)
    (hl : ∀ t ∈ l, t.2.1 + t.2.2.1 + t.2.2.2 = d) {a b c N : ℝ}
    (ha : |a| ≤ N) (hb : |b| ≤ N) (hc : |c| ≤ N) :
    |poly3 l a b c| ≤ (l.map fun t => |t.1|).sum * N ^ d := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [poly3_cons, List.map_cons, List.sum_cons]
    have hd := hl t List.mem_cons_self
    have ih' := ih fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')
    have hmono := abs_mono_le ha hb hc t.2.1 t.2.2.1 t.2.2.2
    rw [hd] at hmono
    calc |t.1 * (a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2) + poly3 l a b c|
        ≤ |t.1| * |a ^ t.2.1 * b ^ t.2.2.1 * c ^ t.2.2.2| + |poly3 l a b c| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |t.1| * N ^ d + (l.map fun t => |t.1|).sum * N ^ d := by
          gcongr
      _ = (|t.1| + (l.map fun t => |t.1|).sum) * N ^ d := by ring

@[tmio T] private theorem abs_dterm_le {x y w dv N : ℝ} (hx : |x| ≤ N) (hy : |y| ≤ N) (hw : |w| ≤ N)
    (hdv : |dv| ≤ 1) {m p q d : ℕ} (hd : m + p + q = d + 1) :
    |(m : ℝ) * x ^ (m - 1) * y ^ p * w ^ q * dv| ≤ (m : ℝ) * N ^ d := by
  have hN : 0 ≤ N := (abs_nonneg x).trans hx
  rcases m with _ | m
  · simp
  · have hd' : m + p + q = d := by omega
    have hmono := abs_mono_le hx hy hw m p q
    rw [hd'] at hmono
    simp only [Nat.add_sub_cancel]
    calc |((m + 1 : ℕ) : ℝ) * x ^ m * y ^ p * w ^ q * dv|
        = ((m + 1 : ℕ) : ℝ) * (|x ^ m * y ^ p * w ^ q| * |dv|) := by
          rw [show ((m + 1 : ℕ) : ℝ) * x ^ m * y ^ p * w ^ q * dv =
            ((m + 1 : ℕ) : ℝ) * ((x ^ m * y ^ p * w ^ q) * dv) by ring, abs_mul, abs_mul,
            Nat.abs_cast]
      _ ≤ ((m + 1 : ℕ) : ℝ) * (N ^ d * 1) := by gcongr
      _ = ((m + 1 : ℕ) : ℝ) * N ^ d := by ring

/-- The derivative of a homogeneous polynomial of degree `d + 1` in a direction with
`|da|, |db|, |dc| ≤ 1` is at most `(Σ |κ| (d + 1)) N^d` on `|a|, |b|, |c| ≤ N`. -/
@[tmio T, powerlib_foundation] theorem abs_dpoly3_le (l : List (ℝ × ℕ × ℕ × ℕ)) (d : ℕ)
    (hl : ∀ t ∈ l, t.2.1 + t.2.2.1 + t.2.2.2 = d + 1) {a b c N da db dc : ℝ}
    (ha : |a| ≤ N) (hb : |b| ≤ N) (hc : |c| ≤ N) (hda : |da| ≤ 1) (hdb : |db| ≤ 1)
    (hdc : |dc| ≤ 1) :
    |dpoly3 l a b c da db dc| ≤
      (l.map fun t => |t.1| * ((t.2.1 : ℝ) + t.2.2.1 + t.2.2.2)).sum * N ^ d := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [dpoly3_cons, List.map_cons, List.sum_cons]
    have hd := hl t List.mem_cons_self
    have ih' := ih fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')
    have h1 := abs_dterm_le ha hb hc hda hd
    have h2 := abs_dterm_le hb ha hc hdb (m := t.2.2.1) (p := t.2.1) (q := t.2.2.2) (d := d)
      (by omega)
    have h3 := abs_dterm_le hc ha hb hdc (m := t.2.2.2) (p := t.2.1) (q := t.2.2.1) (d := d)
      (by omega)
    have e2 : (t.2.2.1 : ℝ) * a ^ t.2.1 * b ^ (t.2.2.1 - 1) * c ^ t.2.2.2 * db =
        (t.2.2.1 : ℝ) * b ^ (t.2.2.1 - 1) * a ^ t.2.1 * c ^ t.2.2.2 * db := by ring
    have e3 : (t.2.2.2 : ℝ) * a ^ t.2.1 * b ^ t.2.2.1 * c ^ (t.2.2.2 - 1) * dc =
        (t.2.2.2 : ℝ) * c ^ (t.2.2.2 - 1) * a ^ t.2.1 * b ^ t.2.2.1 * dc := by ring
    rw [e2, e3]
    set A := (t.2.1 : ℝ) * a ^ (t.2.1 - 1) * b ^ t.2.2.1 * c ^ t.2.2.2 * da
    set B := (t.2.2.1 : ℝ) * b ^ (t.2.2.1 - 1) * a ^ t.2.1 * c ^ t.2.2.2 * db
    set C := (t.2.2.2 : ℝ) * c ^ (t.2.2.2 - 1) * a ^ t.2.1 * b ^ t.2.2.1 * dc
    calc |t.1 * (A + B + C) + dpoly3 l a b c da db dc|
        ≤ |t.1 * (A + B + C)| + |dpoly3 l a b c da db dc| := abs_add_le _ _
      _ ≤ |t.1| * (|A| + |B| + |C|) + |dpoly3 l a b c da db dc| := by
          rw [abs_mul]
          gcongr
          exact abs_add_three A B C
      _ ≤ |t.1| * ((t.2.1 : ℝ) * N ^ d + (t.2.2.1 : ℝ) * N ^ d + (t.2.2.2 : ℝ) * N ^ d) +
          (l.map fun t => |t.1| * ((t.2.1 : ℝ) + t.2.2.1 + t.2.2.2)).sum * N ^ d := by
          gcongr
      _ = (|t.1| * ((t.2.1 : ℝ) + t.2.2.1 + t.2.2.2) +
          (l.map fun t => |t.1| * ((t.2.1 : ℝ) + t.2.2.1 + t.2.2.2)).sum) * N ^ d := by ring

/-- `|η₀ a² + η₁ a b + η₂ b²| ≤ (|η₀| + |η₁| + |η₂|)(a² + b²)`. -/
@[tmio T, powerlib_foundation] theorem abs_quadratic_le (η₀ η₁ η₂ a b : ℝ) :
    |η₀ * a ^ 2 + η₁ * (a * b) + η₂ * b ^ 2| ≤ (|η₀| + |η₁| + |η₂|) * (a ^ 2 + b ^ 2) := by
  have hab : |a * b| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]
  calc |η₀ * a ^ 2 + η₁ * (a * b) + η₂ * b ^ 2|
      ≤ |η₀| * a ^ 2 + |η₁| * |a * b| + |η₂| * b ^ 2 := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
        · rw [abs_mul]
        · rw [abs_mul, abs_of_nonneg (sq_nonneg b)]
    _ ≤ |η₀| * (a ^ 2 + b ^ 2) + |η₁| * (a ^ 2 + b ^ 2) + |η₂| * (a ^ 2 + b ^ 2) := by
        gcongr
        · nlinarith [sq_nonneg b]
        · nlinarith [sq_nonneg a]
    _ = _ := by ring

/-! ### Weighted bounds of polynomials -/

section WeightedBounds

open Asymptotics

/-- A polynomial whose monomials `a^i b^j c^k` all have weight `i + j + 2k ≥ k₀` is `O(s^{k₀})`
when `a, b = O(s)`, `c = O(s²)` and `s → 0` (the weights of a centre-manifold expansion). -/
@[tmio T, powerlib_foundation] theorem isBigO_poly3_weight {α : Type*} {l : Filter α} {s a b c : α → ℝ}
    (hs : Tendsto s l (𝓝 0)) (ha : a =O[l] s) (hb : b =O[l] s)
    (hc : c =O[l] fun x => s x ^ 2) (L : List (ℝ × ℕ × ℕ × ℕ)) {k : ℕ}
    (hL : ∀ t ∈ L, k ≤ t.2.1 + t.2.2.1 + 2 * t.2.2.2) :
    (fun x => poly3 L (a x) (b x) (c x)) =O[l] fun x => s x ^ k := by
  induction L with
  | nil => simpa using isBigO_zero (fun x => s x ^ k) l
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')
    have hm : (fun x => a x ^ t.2.1 * b x ^ t.2.2.1 * c x ^ t.2.2.2) =O[l]
        fun x => s x ^ (t.2.1 + t.2.2.1 + 2 * t.2.2.2) := by
      refine (((ha.pow t.2.1).mul (hb.pow t.2.2.1)).mul (hc.pow t.2.2.2)).congr_right
        fun x => ?_
      rw [← pow_mul, ← pow_add, ← pow_add]
    simp only [poly3_cons]
    exact ((hm.trans (Dynamics.isBigO_pow_of_tendsto hs ht)).const_mul_left t.1).add ih'

end WeightedBounds

/-! ## A Hopf point with one stable real eigenvalue -/

/-- Coefficient of `a²` in the quadratic part of the centre manifold. -/
def hopfEta0 (H lam g2 : ℝ) : ℝ :=
  -g2 * (2 * H ^ 2 + lam ^ 4) / (lam * (H + lam ^ 2) ^ 2 * (4 * H + lam ^ 2))

/-- Coefficient of `a b` in the quadratic part of the centre manifold. -/
def hopfEta1 (H lam g2 : ℝ) : ℝ :=
  -2 * g2 * (H - 2 * lam ^ 2) / ((H + lam ^ 2) ^ 2 * (4 * H + lam ^ 2))

/-- Coefficient of `b²` in the quadratic part of the centre manifold. -/
def hopfEta2 (H lam g2 : ℝ) : ℝ :=
  -g2 * (2 * H + 5 * lam ^ 2) / (lam * (H + lam ^ 2) ^ 2 * (4 * H + lam ^ 2))

/-- The quadratic part `h₂(a, b)` of the centre manifold `c = h(a, b)` of
`ȧ = b, ḃ = −H a − G, ċ = −λ c − G`, `G = g₂ ξ² + …`. -/
def hopfH2 (H lam g2 a b : ℝ) : ℝ :=
  hopfEta0 H lam g2 * a ^ 2 + hopfEta1 H lam g2 * (a * b) + hopfEta2 H lam g2 * b ^ 2

/-- The quadratic part `H a² + b² + c²` of the Lyapunov function. -/
def hopfQ (H : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [(H, 2, 0, 0), (1, 0, 2, 0), (1, 0, 0, 2)]

set_option maxHeartbeats 1000000 in
/-- The cubic part `W₃` of the Lyapunov function. -/
def hopfW3 (H lam g2 : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [
    ((-2*g2/(3*lam*(H + lam^2)^2) : ℝ), 0, 0, 3),
    ((2*g2*(6*H + 5*lam^2)/(lam*(H + lam^2)^2*(4*H + lam^2)) : ℝ), 0, 2, 1),
    ((4*g2*lam/(3*H*(H + lam^2)^2) : ℝ), 0, 3, 0),
    ((-2*g2/(H + lam^2)^2 : ℝ), 1, 0, 2),
    ((-4*g2*(H + 3*lam^2)/((H + lam^2)^2*(4*H + lam^2)) : ℝ), 1, 1, 1),
    ((2*g2/(H + lam^2)^2 : ℝ), 1, 2, 0),
    ((2*g2*(6*H^2 + 2*H*lam^2 + lam^4)/(lam*(H + lam^2)^2*(4*H + lam^2)) : ℝ), 2, 0, 1),
    ((2*g2*(2*H + lam^2)/(3*(H + lam^2)^2) : ℝ), 3, 0, 0)]

set_option maxHeartbeats 4000000 in
/-- The quartic part `W₄` of the Lyapunov function. -/
def hopfW4 (H lam g2 g3 : ℝ) : List (ℝ × ℕ × ℕ × ℕ) := [
    (((-H*g3*lam + g2^2 - g3*lam^3)/(2*lam^2*(H + lam^2)^4) : ℝ), 0, 0, 4),
    ((-2*(-12*H^2*g3*lam + 42*H*g2^2 - 15*H*g3*lam^3 + 26*g2^2*lam^2 - 3*g3*lam^5) /
        ((H + lam^2)^4*(H + 9*lam^2)*(4*H + lam^2)) : ℝ), 0, 1, 3),
    ((2*g2^2*(2*H - lam^2)*(2*H + lam^2)/(H*lam^2*(H + lam^2)^4*(4*H + lam^2)) : ℝ), 0, 2, 2),
    ((2*(-20*H^2*g3*lam + 54*H*g2^2 - 25*H*g3*lam^3 + 30*g2^2*lam^2 - 5*g3*lam^5) /
        ((H + lam^2)^4*(4*H + lam^2)*(9*H + lam^2)) : ℝ), 0, 3, 1),
    (((-12*H^2*g3*lam + 22*H*g2^2 - 7*H*g3*lam^3 + 2*g2^2*lam^2 - g3*lam^5) /
        (2*H^2*(H + lam^2)^3*(4*H + lam^2)) : ℝ), 0, 4, 0),
    ((2*(-8*H^3*g3*lam + 20*H^2*g2^2 - 46*H^2*g3*lam^3 + 66*H*g2^2*lam^2 - 47*H*g3*lam^5 +
        30*g2^2*lam^4 - 9*g3*lam^7) /
        (lam*(H + lam^2)^4*(H + 9*lam^2)*(4*H + lam^2)) : ℝ), 1, 0, 3),
    ((-4*g2^2*(7*H + 4*lam^2)/(lam*(H + lam^2)^4*(4*H + lam^2)) : ℝ), 1, 1, 2),
    ((-2*(-72*H^4*g3 - 78*H^3*g3*lam^2 + 90*H^2*g2^2*lam - 3*H^2*g3*lam^4 + 22*H*g2^2*lam^3 +
        3*H*g3*lam^6 + 4*g2^2*lam^5) /
        (H*(H + lam^2)^4*(4*H + lam^2)*(9*H + lam^2)) : ℝ), 1, 2, 1),
    (((-80*H^5*g3*lam + 96*H^4*g2^2 - 72*H^4*g3*lam^3 + 152*H^3*g2^2*lam^2 + 27*H^3*g3*lam^5 -
        146*H^2*g2^2*lam^4 + 22*H^2*g3*lam^7 - 12*H*g2^2*lam^6 + 3*H*g3*lam^9 - 2*g2^2*lam^8) /
        (4*H^2*lam*(H + lam^2)^4*(4*H + lam^2)^2) : ℝ), 1, 3, 0),
    (((8*H^2*g2^2 - 12*H^2*g3*lam^3 + 30*H*g2^2*lam^2 - 15*H*g3*lam^5 + 16*g2^2*lam^4 -
        3*g3*lam^7) /
        (lam^2*(H + lam^2)^4*(4*H + lam^2)) : ℝ), 2, 0, 2),
    ((-2*(48*H^3*g3*lam + 72*H^2*g2^2 + 72*H^2*g3*lam^3 - 10*H*g2^2*lam^2 + 27*H*g3*lam^5 -
        10*g2^2*lam^4 + 3*g3*lam^7) /
        ((H + lam^2)^4*(4*H + lam^2)*(9*H + lam^2)) : ℝ), 2, 1, 1),
    (((56*H^3*g2^2 - 16*H^3*g3*lam^3 - 12*H^2*g2^2*lam^2 - 24*H^2*g3*lam^5 + 26*H*g2^2*lam^4 -
        9*H*g3*lam^7 - 2*g2^2*lam^6 - g3*lam^9) /
        (H*(H + lam^2)^4*(4*H + lam^2)^2) : ℝ), 2, 2, 0),
    ((-2*(-48*H^4*g3*lam + 36*H^3*g2^2 - 36*H^3*g3*lam^3 - 32*H^2*g2^2*lam^2 + 22*H^2*g3*lam^5 -
        50*H*g2^2*lam^4 + 11*H*g3*lam^7 - 6*g2^2*lam^6 + g3*lam^9) /
        (lam*(H + lam^2)^4*(4*H + lam^2)*(9*H + lam^2)) : ℝ), 3, 0, 1),
    (((-48*H^5*g3*lam + 96*H^4*g2^2 - 120*H^4*g3*lam^3 - 40*H^3*g2^2*lam^2 - 99*H^3*g3*lam^5 +
        34*H^2*g2^2*lam^4 - 30*H^2*g3*lam^7 - 20*H*g2^2*lam^6 - 3*H*g3*lam^9 + 2*g2^2*lam^8) /
        (4*H*lam*(H + lam^2)^4*(4*H + lam^2)^2) : ℝ), 3, 1, 0)]

/-- The weak-focus coefficient `κ = 2 g₂² (8H + λ²) − 3 H λ g₃ (4H + λ²)`. -/
def hopfCoeff (H lam g2 g3 : ℝ) : ℝ :=
  2 * g2 ^ 2 * (8 * H + lam ^ 2) - 3 * H * lam * g3 * (4 * H + lam ^ 2)

@[tmio T, powerlib_foundation] theorem hopfQ_degree (H : ℝ) :
    ∀ t ∈ hopfQ H, t.2.1 + t.2.2.1 + t.2.2.2 = 2 := by
  intro t ht
  simp only [hopfQ, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> rfl

@[tmio T, powerlib_foundation] theorem hopfW3_degree (H lam g2 : ℝ) :
    ∀ t ∈ hopfW3 H lam g2, t.2.1 + t.2.2.1 + t.2.2.2 = 2 + 1 := by
  intro t ht
  simp only [hopfW3, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[tmio T, powerlib_foundation] theorem hopfW4_degree (H lam g2 g3 : ℝ) :
    ∀ t ∈ hopfW4 H lam g2 g3, t.2.1 + t.2.2.1 + t.2.2.2 = 3 + 1 := by
  intro t ht
  simp only [hopfW4, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> rfl

@[tmio T, powerlib_foundation] theorem poly3_hopfQ (H a b c : ℝ) :
    poly3 (hopfQ H) a b c = H * a ^ 2 + b ^ 2 + c ^ 2 := by
  simp only [hopfQ, poly3_cons, poly3_nil]
  ring

@[tmio T, powerlib_foundation] theorem dpoly3_hopfQ_lie (H lam a b c : ℝ) :
    dpoly3 (hopfQ H) a b c b (-H * a) (-lam * c) = -2 * lam * c ^ 2 := by
  simp only [hopfQ, dpoly3_cons, dpoly3_nil]
  norm_num
  ring

@[tmio T, powerlib_foundation] theorem dpoly3_hopfQ_force (H a b c : ℝ) :
    dpoly3 (hopfQ H) a b c 0 1 1 = 2 * b + 2 * c := by
  simp only [hopfQ, dpoly3_cons, dpoly3_nil]
  norm_num

set_option maxHeartbeats 4000000 in
/-- **Cubic homological equation.** Along the linear part, `W₃` cancels the quadratic forcing
`−g₂ ξ² (∂_b + ∂_c)(H a² + b² + c²)` up to `4 λ c h₂(a, b)`. -/
@[tmio T, powerlib_foundation] theorem hopfW3_homological {H lam : ℝ} (hH : 0 < H) (hl : 0 < lam)
    (g2 a b c : ℝ) :
    dpoly3 (hopfW3 H lam g2) a b c b (-H * a) (-lam * c) -
      g2 * ((lam * a - b + c) / (H + lam ^ 2)) ^ 2 * (2 * b + 2 * c) =
      4 * lam * c * hopfH2 H lam g2 a b := by
  have h1 : H + lam ^ 2 ≠ 0 := by positivity
  have h2 : 4 * H + lam ^ 2 ≠ 0 := by positivity
  have h3 : lam ≠ 0 := hl.ne'
  have h4 : H ≠ 0 := hH.ne'
  simp only [hopfW3, hopfH2, hopfEta0, hopfEta1, hopfEta2, dpoly3]
  norm_num
  field_simp
  ring

set_option maxHeartbeats 40000000 in
/-- **Quartic homological equation.** Along the linear part, `W₄` cancels the quartic terms up
to `−2 λ h₂² − κ / (4 H² λ (H + λ²)² (4H + λ²)) (H a² + b²)²`. -/
@[tmio T, powerlib_foundation] theorem hopfW4_homological {H lam : ℝ} (hH : 0 < H) (hl : 0 < lam)
    (g2 g3 a b c : ℝ) :
    dpoly3 (hopfW4 H lam g2 g3) a b c b (-H * a) (-lam * c) -
      g3 * ((lam * a - b + c) / (H + lam ^ 2)) ^ 3 * (2 * b + 2 * c) -
      g2 * ((lam * a - b + c) / (H + lam ^ 2)) ^ 2 * dpoly3 (hopfW3 H lam g2) a b c 0 1 1 =
      -2 * lam * hopfH2 H lam g2 a b ^ 2 -
        hopfCoeff H lam g2 g3 / (4 * H ^ 2 * lam * (H + lam ^ 2) ^ 2 * (4 * H + lam ^ 2)) *
          (H * a ^ 2 + b ^ 2) ^ 2 := by
  have h1 : H + lam ^ 2 ≠ 0 := by positivity
  have h2 : 4 * H + lam ^ 2 ≠ 0 := by positivity
  have h5 : 9 * H + lam ^ 2 ≠ 0 := by positivity
  have h6 : H + 9 * lam ^ 2 ≠ 0 := by positivity
  have h3 : lam ≠ 0 := hl.ne'
  have h4 : H ≠ 0 := hH.ne'
  simp only [hopfW4, hopfW3, hopfH2, hopfEta0, hopfEta1, hopfEta2, hopfCoeff, dpoly3]
  norm_num
  field_simp
  ring

/-- `2λ (c − h)² + k r₂²` dominates `(a² + b² + c²)²` near the origin when
`r₂ ≥ H_m (a² + b²)` and `|h| ≤ C_h (a² + b²)`. -/
@[tmio T, powerlib_foundation] theorem exists_quartic_lower {lam k Hm Ch : ℝ} (hlam : 0 < lam)
    (hk : 0 < k) (hHm : 0 < Hm) (hCh : 0 ≤ Ch) :
    ∃ m > 0, ∀ a b c h r2 : ℝ, Hm * (a ^ 2 + b ^ 2) ≤ r2 → |h| ≤ Ch * (a ^ 2 + b ^ 2) →
      a ^ 2 + b ^ 2 + c ^ 2 ≤ 1 →
        m * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 2 * lam * (c - h) ^ 2 + k * r2 ^ 2 := by
  set ε := min 1 (k * Hm ^ 2 / (4 * lam * Ch ^ 2 + 1)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (4 * lam * Ch ^ 2 + 1) ≤ k * Hm ^ 2 := by
    have := min_le_right 1 (k * Hm ^ 2 / (4 * lam * Ch ^ 2 + 1))
    rwa [← hε, le_div_iff₀ (by positivity)] at this
  set μ := min (lam * ε) (k * Hm ^ 2 / 2) with hμ
  have hμ0 : 0 < μ := lt_min (by positivity) (by positivity)
  have hμ1 : μ ≤ lam * ε := min_le_left _ _
  have hμ2 : μ ≤ k * Hm ^ 2 / 2 := min_le_right _ _
  refine ⟨μ / 2, by positivity, fun a b c h r2 hr2 hh hσ => ?_⟩
  set u := a ^ 2 + b ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hHu : 0 ≤ Hm * u := by positivity
  have hr2' : Hm ^ 2 * u ^ 2 ≤ r2 ^ 2 := by nlinarith
  have hh2 : h ^ 2 ≤ Ch ^ 2 * u ^ 2 := by
    have h0 : 0 ≤ Ch * u := by positivity
    have := pow_le_pow_left₀ (abs_nonneg h) hh 2
    rw [sq_abs] at this
    nlinarith
  have hch : c ^ 2 ≤ 2 * (c - h) ^ 2 + 2 * h ^ 2 := by nlinarith [sq_nonneg (c - 2 * h)]
  have p1 : 0 ≤ (1 - ε) * lam * (c - h) ^ 2 := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have p2 := mul_le_mul_of_nonneg_left hch (by positivity : (0 : ℝ) ≤ lam * ε)
  have p3 := mul_le_mul_of_nonneg_left hh2 (by positivity : (0 : ℝ) ≤ lam * ε)
  have p4 := mul_le_mul_of_nonneg_left hr2' hk.le
  have p5 := mul_le_mul_of_nonneg_right hε2 (sq_nonneg u)
  have p6 : 0 ≤ ε * u ^ 2 := by positivity
  have step1 : lam * ε * c ^ 2 + k * Hm ^ 2 / 2 * u ^ 2 ≤
      2 * lam * (c - h) ^ 2 + k * r2 ^ 2 := by
    linarith
  have step2 : (u + c ^ 2) ^ 2 ≤ 2 * (u ^ 2 + c ^ 2 * (u + c ^ 2)) := by
    nlinarith [sq_nonneg c]
  have step3 : c ^ 2 * (u + c ^ 2) ≤ c ^ 2 := by
    have := sq_nonneg c
    nlinarith
  have q1 := mul_le_mul_of_nonneg_left step2 (by positivity : (0 : ℝ) ≤ μ / 2)
  have q2 := mul_le_mul_of_nonneg_left step3 hμ0.le
  have q3 := mul_le_mul_of_nonneg_right hμ1 (sq_nonneg c)
  have q4 := mul_le_mul_of_nonneg_right hμ2 (sq_nonneg u)
  linarith

@[tmio T] private theorem poly3_zero {l : List (ℝ × ℕ × ℕ × ℕ)} {d : ℕ} (hd : 0 < d)
    (hl : ∀ t ∈ l, t.2.1 + t.2.2.1 + t.2.2.2 = d) : poly3 l 0 0 0 = 0 := by
  have h := abs_poly3_le l d hl (a := 0) (b := 0) (c := 0) (N := 0) (by simp) (by simp) (by simp)
  rw [zero_pow hd.ne', mul_zero] at h
  exact abs_nonpos_iff.mp h

set_option maxHeartbeats 1000000 in
/-- **Weak stable focus.** Let `T` be an injective linear map with
`T(f z) = (b, −H a − G z, −λ c − G z)` for `T z = (a, b, c)`, `H, λ > 0`, where
`G z = g₂ ξ² + g₃ ξ³ + O(ξ⁴)` with `ξ = (λ a − b + c)/(H + λ²)`. If
`κ = 2 g₂² (8H + λ²) − 3 H λ g₃ (4H + λ²) > 0`, the origin of the `C¹` field `f` is locally
asymptotically stable: `W(T z)` with `W = H a² + b² + c² + W₃ + W₄` is a strict Lyapunov function on
a punctured ball. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_hopf_weakFocus {f : State 3 → State 3}
    {T : State 3 →L[ℝ] State 3} {G : State 3 → ℝ} {H lam g2 g3 : ℝ} (hf : ContDiff ℝ 1 f)
    (hT : Function.Injective T) (hH : 0 < H) (hl : 0 < lam)
    (hf0 : ∀ z, T (f z) 0 = T z 1) (hf1 : ∀ z, T (f z) 1 = -H * T z 0 - G z)
    (hf2 : ∀ z, T (f z) 2 = -lam * T z 2 - G z)
    (hG : ∃ ρ > 0, ∃ C, ∀ z, |(lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)| ≤ ρ →
      |G z - (g2 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 2 +
        g3 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 3)| ≤
        C * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 4)
    (hκ : 0 < hopfCoeff H lam g2 g3) :
    LocalAsymptoticStable f 0 := by
  obtain ⟨ρ, hρ, Ce, hCe⟩ := hG
  have hS : 0 < H + lam ^ 2 := by positivity
  set ℓa : State 3 →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 3)).comp T with hℓa
  set ℓb : State 3 →L[ℝ] ℝ := (EuclideanSpace.proj (1 : Fin 3)).comp T with hℓb
  set ℓc : State 3 →L[ℝ] ℝ := (EuclideanSpace.proj (2 : Fin 3)).comp T with hℓc
  have hla : ∀ z, ℓa z = T z 0 := fun z => rfl
  have hlb : ∀ z, ℓb z = T z 1 := fun z => rfl
  have hlc : ∀ z, ℓc z = T z 2 := fun z => rfl
  set V : State 3 → ℝ := fun z => poly3 (hopfQ H) (ℓa z) (ℓb z) (ℓc z) +
    poly3 (hopfW3 H lam g2) (ℓa z) (ℓb z) (ℓc z) +
    poly3 (hopfW4 H lam g2 g3) (ℓa z) (ℓb z) (ℓc z) with hVdef
  have hV : ContDiff ℝ 1 V :=
    ((contDiff_poly3 _ ℓa ℓb ℓc).add (contDiff_poly3 _ ℓa ℓb ℓc)).add (contDiff_poly3 _ ℓa ℓb ℓc)
  have hVd : ∀ z v, fderiv ℝ V z v =
      dpoly3 (hopfQ H) (ℓa z) (ℓb z) (ℓc z) (ℓa v) (ℓb v) (ℓc v) +
      dpoly3 (hopfW3 H lam g2) (ℓa z) (ℓb z) (ℓc z) (ℓa v) (ℓb v) (ℓc v) +
      dpoly3 (hopfW4 H lam g2 g3) (ℓa z) (ℓb z) (ℓc z) (ℓa v) (ℓb v) (ℓc v) := by
    intro z v
    obtain ⟨L1, h1, hv1⟩ := hasFDerivAt_poly3 (hopfQ H) ℓa ℓb ℓc z
    obtain ⟨L2, h2, hv2⟩ := hasFDerivAt_poly3 (hopfW3 H lam g2) ℓa ℓb ℓc z
    obtain ⟨L3, h3, hv3⟩ := hasFDerivAt_poly3 (hopfW4 H lam g2 g3) ℓa ℓb ℓc z
    have hVf : HasFDerivAt V (L1 + L2 + L3) z := (h1.add h2).add h3
    rw [hVf.fderiv, _root_.add_apply, _root_.add_apply, hv1, hv2, hv3]
  -- the equilibrium
  have hG0 : G 0 = 0 := by
    have h := hCe 0 (by simp [hρ.le])
    simp only [map_zero, PiLp.zero_apply, mul_zero, sub_zero, add_zero, zero_div,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    exact abs_nonpos_iff.mp h
  have hfeq : f 0 = 0 := by
    apply hT
    rw [map_zero]
    ext i
    fin_cases i
    · simp [hf0]
    · simp [hf1, hG0]
    · simp [hf2, hG0]
  -- the Lie derivative
  have hlie : ∀ z, fderiv ℝ V z (f z) =
      -2 * lam * (T z 2 - hopfH2 H lam g2 (T z 0) (T z 1)) ^ 2 -
        hopfCoeff H lam g2 g3 / (4 * H ^ 2 * lam * (H + lam ^ 2) ^ 2 * (4 * H + lam ^ 2)) *
          (H * T z 0 ^ 2 + T z 1 ^ 2) ^ 2 +
        (-(G z - (g2 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 2 +
            g3 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 3)) * (2 * T z 1 + 2 * T z 2) -
          (g3 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 3 +
            (G z - (g2 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 2 +
              g3 * ((lam * T z 0 - T z 1 + T z 2) / (H + lam ^ 2)) ^ 3))) *
            dpoly3 (hopfW3 H lam g2) (T z 0) (T z 1) (T z 2) 0 1 1 -
          G z * dpoly3 (hopfW4 H lam g2 g3) (T z 0) (T z 1) (T z 2) 0 1 1) := by
    intro z
    rw [hVd, hla, hlb, hlc, hla, hlb, hlc, hf0, hf1, hf2]
    set a := T z 0
    set b := T z 1
    set c := T z 2
    have key : ∀ l, dpoly3 l a b c b (-H * a - G z) (-lam * c - G z) =
        dpoly3 l a b c b (-H * a) (-lam * c) - G z * dpoly3 l a b c 0 1 1 := by
      intro l
      have h := dpoly3_add_smul l a b c b (-H * a) (-lam * c) (-G z) 0 1 1
      simp only [mul_zero, add_zero, mul_one] at h
      rw [show -H * a - G z = -H * a + -G z by ring, show -lam * c - G z = -lam * c + -G z by ring,
        h]
      ring
    rw [key, key, key, dpoly3_hopfQ_lie, dpoly3_hopfQ_force]
    have I3 := hopfW3_homological hH hl g2 a b c
    have I4 := hopfW4_homological hH hl g2 g3 a b c
    linear_combination I3 + I4
  -- constants
  have hsum : ∀ (l : List (ℝ × ℕ × ℕ × ℕ)) (g : ℝ × ℕ × ℕ × ℕ → ℝ), (∀ t, 0 ≤ g t) →
      0 ≤ (l.map g).sum := fun l g hg =>
    List.sum_nonneg fun x hx => by obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx; exact hg t
  obtain ⟨C3, hC3, hb3⟩ : ∃ C ≥ (0 : ℝ), ∀ a b c N : ℝ, |a| ≤ N → |b| ≤ N → |c| ≤ N →
      |poly3 (hopfW3 H lam g2) a b c| ≤ C * N ^ 3 :=
    ⟨_, hsum _ _ fun t => abs_nonneg _, fun a b c N ha hb hc =>
      abs_poly3_le _ (2 + 1) (hopfW3_degree H lam g2) ha hb hc⟩
  obtain ⟨C4, hC4, hb4⟩ : ∃ C ≥ (0 : ℝ), ∀ a b c N : ℝ, |a| ≤ N → |b| ≤ N → |c| ≤ N →
      |poly3 (hopfW4 H lam g2 g3) a b c| ≤ C * N ^ 4 :=
    ⟨_, hsum _ _ fun t => abs_nonneg _, fun a b c N ha hb hc =>
      abs_poly3_le _ (3 + 1) (hopfW4_degree H lam g2 g3) ha hb hc⟩
  obtain ⟨D3, hD3, hd3b⟩ : ∃ C ≥ (0 : ℝ), ∀ a b c N : ℝ, |a| ≤ N → |b| ≤ N → |c| ≤ N →
      |dpoly3 (hopfW3 H lam g2) a b c 0 1 1| ≤ C * N ^ 2 :=
    ⟨_, hsum _ _ fun t => by positivity, fun a b c N ha hb hc =>
      abs_dpoly3_le _ 2 (hopfW3_degree H lam g2) ha hb hc (by simp) (by simp) (by simp)⟩
  obtain ⟨D4, hD4, hd4b⟩ : ∃ C ≥ (0 : ℝ), ∀ a b c N : ℝ, |a| ≤ N → |b| ≤ N → |c| ≤ N →
      |dpoly3 (hopfW4 H lam g2 g3) a b c 0 1 1| ≤ C * N ^ 3 :=
    ⟨_, hsum _ _ fun t => by positivity, fun a b c N ha hb hc =>
      abs_dpoly3_le _ 3 (hopfW4_degree H lam g2 g3) ha hb hc (by simp) (by simp) (by simp)⟩
  obtain ⟨Ch, hCh, hbh⟩ : ∃ C ≥ (0 : ℝ), ∀ a b : ℝ,
      |hopfH2 H lam g2 a b| ≤ C * (a ^ 2 + b ^ 2) :=
    ⟨_, by positivity, fun a b => abs_quadratic_le _ _ _ a b⟩
  obtain ⟨k, hk, hkdef⟩ : ∃ k > (0 : ℝ),
      k = hopfCoeff H lam g2 g3 / (4 * H ^ 2 * lam * (H + lam ^ 2) ^ 2 * (4 * H + lam ^ 2)) :=
    ⟨_, by positivity, rfl⟩
  set m2 := min H 1 with hm2def
  have hm2 : 0 < m2 := lt_min hH one_pos
  obtain ⟨m, hm, hquart⟩ := exists_quartic_lower hl hk hm2 hCh
  set cx := (lam + 2) / (H + lam ^ 2) with hcxdef
  have hcx : 0 < cx := by positivity
  set CR := 4 * |Ce| * cx ^ 4 + (|g3| * cx ^ 3 + |Ce| * cx ^ 4) * D3 +
    (|g2| * cx ^ 2 + |g3| * cx ^ 3 + |Ce| * cx ^ 4) * D4 with hCR
  have hCR0 : 0 ≤ CR := by positivity
  set ν := min (min 1 (m2 / (2 * (C3 + C4) + 1))) (min (m / (CR + 1)) (ρ / (cx + 1))) with hν
  have hν0 : 0 < ν :=
    lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))
  have hν1 : ν ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hν2 : ν ≤ m2 / (2 * (C3 + C4) + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hν3 : ν ≤ m / (CR + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hν4 : ν ≤ ρ / (cx + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hcoord : ∀ z (i : Fin 3), |T z i| ≤ ‖T z‖ := fun z i => by
    have := PiLp.norm_apply_le (T z) i
    rwa [Real.norm_eq_abs] at this
  have hnormsq : ∀ z, T z 0 ^ 2 + T z 1 ^ 2 + T z 2 ^ 2 = ‖T z‖ ^ 2 := fun z => by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  -- `V` is positive definite near the origin
  have hVpos : ∀ z, ‖T z‖ < ν → m2 / 2 * ‖T z‖ ^ 2 ≤ V z := by
    intro z hz
    have hN0 : 0 ≤ ‖T z‖ := norm_nonneg _
    have hN1 : ‖T z‖ ≤ 1 := hz.le.trans hν1
    have hNm : ‖T z‖ * (2 * (C3 + C4) + 1) ≤ m2 := by
      have := hz.le.trans hν2
      rwa [le_div_iff₀ (by positivity)] at this
    have hQ : m2 * ‖T z‖ ^ 2 ≤ poly3 (hopfQ H) (T z 0) (T z 1) (T z 2) := by
      rw [poly3_hopfQ, ← hnormsq]
      have h1 : m2 ≤ H := min_le_left _ _
      have h2 : m2 ≤ 1 := min_le_right _ _
      have q0 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (T z 0))
      have q1 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (T z 1))
      have q2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (T z 2))
      linarith
    have h3 := hb3 _ _ _ _ (hcoord z 0) (hcoord z 1) (hcoord z 2)
    have h4 := hb4 _ _ _ _ (hcoord z 0) (hcoord z 1) (hcoord z 2)
    have e3 := neg_abs_le (poly3 (hopfW3 H lam g2) (T z 0) (T z 1) (T z 2))
    have e4 := neg_abs_le (poly3 (hopfW4 H lam g2 g3) (T z 0) (T z 1) (T z 2))
    have hN43 : ‖T z‖ ^ 4 ≤ ‖T z‖ ^ 3 := pow_le_pow_of_le_one hN0 hN1 (by norm_num)
    have k1 : C3 * ‖T z‖ ^ 3 + C4 * ‖T z‖ ^ 4 ≤ (C3 + C4) * ‖T z‖ * ‖T z‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hN43 hC4
      have e : (C3 + C4) * ‖T z‖ * ‖T z‖ ^ 2 = C3 * ‖T z‖ ^ 3 + C4 * ‖T z‖ ^ 3 := by ring
      rw [e]; linarith
    have k2 : (C3 + C4) * ‖T z‖ ≤ m2 / 2 := by
      have e : ‖T z‖ * (2 * (C3 + C4) + 1) = 2 * ((C3 + C4) * ‖T z‖) + ‖T z‖ := by ring
      rw [e] at hNm; linarith
    have k3 := mul_le_mul_of_nonneg_right k2 (sq_nonneg ‖T z‖)
    show m2 / 2 * ‖T z‖ ^ 2 ≤ poly3 (hopfQ H) (ℓa z) (ℓb z) (ℓc z) +
      poly3 (hopfW3 H lam g2) (ℓa z) (ℓb z) (ℓc z) + poly3 (hopfW4 H lam g2 g3) (ℓa z) (ℓb z) (ℓc z)
    rw [hla, hlb, hlc]
    linarith
  -- the Lie derivative is negative definite near the origin
  have hVlie : ∀ z, ‖T z‖ < ν →
      fderiv ℝ V z (f z) ≤ -(‖T z‖ ^ 4 * (m - CR * ‖T z‖)) := by
    intro z hz
    have hN0 : 0 ≤ ‖T z‖ := norm_nonneg _
    have hN1 : ‖T z‖ ≤ 1 := hz.le.trans hν1
    rw [hlie z]
    have ha := hcoord z 0
    have hb := hcoord z 1
    have hc := hcoord z 2
    have hsq := hnormsq z
    set N := ‖T z‖ with hNdef
    set a := T z 0
    set b := T z 1
    set c := T z 2
    set x := (lam * a - b + c) / (H + lam ^ 2) with hx
    set e := G z - (g2 * x ^ 2 + g3 * x ^ 3) with he
    -- bounds on the forcing
    have hX : |x| ≤ cx * N := by
      rw [hx, abs_div, abs_of_pos hS, div_le_iff₀ hS]
      have : |lam * a - b + c| ≤ lam * |a| + |b| + |c| := by
        calc |lam * a - b + c| ≤ |lam * a - b| + |c| := abs_add_le _ _
          _ ≤ |lam * a| + |b| + |c| := by gcongr; exact abs_sub _ _
          _ = lam * |a| + |b| + |c| := by rw [abs_mul, abs_of_pos hl]
      have hcx' : cx * N * (H + lam ^ 2) = (lam + 2) * N := by
        rw [hcxdef]; field_simp
      rw [hcx']
      have := mul_le_mul_of_nonneg_left ha hl.le
      linarith
    have hXρ : |x| ≤ ρ := by
      have h1 : N ≤ ρ / (cx + 1) := hz.le.trans hν4
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    have hE : |e| ≤ |Ce| * (cx * N) ^ 4 := by
      have h := hCe z hXρ
      have h4 : x ^ 4 ≤ (cx * N) ^ 4 := by
        have h' := pow_le_pow_left₀ (abs_nonneg x) hX 4
        rwa [pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)] at h'
      calc |e| ≤ Ce * x ^ 4 := h
        _ ≤ |Ce| * x ^ 4 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |Ce| * (cx * N) ^ 4 := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    have hX2 : |x| ^ 2 ≤ (cx * N) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hX 2
    have hX3 : |x| ^ 3 ≤ (cx * N) ^ 3 := pow_le_pow_left₀ (abs_nonneg x) hX 3
    have hg3e : |g3 * x ^ 3 + e| ≤ |g3| * (cx * N) ^ 3 + |Ce| * (cx * N) ^ 4 := by
      calc |g3 * x ^ 3 + e| ≤ |g3| * |x| ^ 3 + |e| := by
            rw [← abs_pow, ← abs_mul]; exact abs_add_le _ _
        _ ≤ _ := by gcongr
    have hGz : |G z| ≤ |g2| * (cx * N) ^ 2 + |g3| * (cx * N) ^ 3 + |Ce| * (cx * N) ^ 4 := by
      have hG : G z = g2 * x ^ 2 + (g3 * x ^ 3 + e) := by rw [he]; ring
      calc |G z| ≤ |g2| * |x| ^ 2 + |g3 * x ^ 3 + e| := by
            rw [hG, ← abs_pow, ← abs_mul]; exact abs_add_le _ _
        _ ≤ |g2| * (cx * N) ^ 2 + (|g3| * (cx * N) ^ 3 + |Ce| * (cx * N) ^ 4) := by gcongr
        _ = _ := by ring
    have hd3 := hd3b _ _ _ _ ha hb hc
    have hd4 := hd4b _ _ _ _ ha hb hc
    have hbc : |2 * b + 2 * c| ≤ 4 * N := by
      calc |2 * b + 2 * c| ≤ |2 * b| + |2 * c| := abs_add_le _ _
        _ = 2 * |b| + 2 * |c| := by rw [abs_mul, abs_mul, abs_two]
        _ ≤ 4 * N := by linarith
    set R := -e * (2 * b + 2 * c) - (g3 * x ^ 3 + e) * dpoly3 (hopfW3 H lam g2) a b c 0 1 1 -
      G z * dpoly3 (hopfW4 H lam g2 g3) a b c 0 1 1 with hR
    have hRb : |R| ≤ |Ce| * (cx * N) ^ 4 * (4 * N) +
        (|g3| * (cx * N) ^ 3 + |Ce| * (cx * N) ^ 4) * (D3 * N ^ 2) +
        (|g2| * (cx * N) ^ 2 + |g3| * (cx * N) ^ 3 + |Ce| * (cx * N) ^ 4) * (D4 * N ^ 3) := by
      calc |R| ≤ |e| * |2 * b + 2 * c| + |g3 * x ^ 3 + e| * |dpoly3 (hopfW3 H lam g2) a b c 0 1 1| +
            |G z| * |dpoly3 (hopfW4 H lam g2 g3) a b c 0 1 1| := by
            rw [hR, ← abs_mul, ← abs_mul, ← abs_mul]
            calc |-e * (2 * b + 2 * c) - (g3 * x ^ 3 + e) * dpoly3 (hopfW3 H lam g2) a b c 0 1 1 -
                  G z * dpoly3 (hopfW4 H lam g2 g3) a b c 0 1 1|
                ≤ |-e * (2 * b + 2 * c) - (g3 * x ^ 3 + e) * dpoly3 (hopfW3 H lam g2) a b c 0 1 1| +
                  |G z * dpoly3 (hopfW4 H lam g2 g3) a b c 0 1 1| := abs_sub _ _
              _ ≤ |-e * (2 * b + 2 * c)| +
                  |(g3 * x ^ 3 + e) * dpoly3 (hopfW3 H lam g2) a b c 0 1 1| +
                  |G z * dpoly3 (hopfW4 H lam g2 g3) a b c 0 1 1| := by
                  gcongr; exact abs_sub _ _
              _ = _ := by rw [neg_mul, abs_neg]
        _ ≤ _ := by gcongr
    have hR5 : |R| ≤ CR * N ^ 5 := by
      refine hRb.trans ?_
      have h6 : N ^ 6 ≤ N ^ 5 := pow_le_pow_of_le_one hN0 hN1 (by norm_num)
      have h7 : N ^ 7 ≤ N ^ 5 := pow_le_pow_of_le_one hN0 hN1 (by norm_num)
      have hB : 0 ≤ |Ce| * cx ^ 4 * D3 + |g3| * cx ^ 3 * D4 := by positivity
      have hC : 0 ≤ |Ce| * cx ^ 4 * D4 := by positivity
      have e1 : |Ce| * (cx * N) ^ 4 * (4 * N) +
          (|g3| * (cx * N) ^ 3 + |Ce| * (cx * N) ^ 4) * (D3 * N ^ 2) +
          (|g2| * (cx * N) ^ 2 + |g3| * (cx * N) ^ 3 + |Ce| * (cx * N) ^ 4) * (D4 * N ^ 3) =
          (4 * |Ce| * cx ^ 4 + |g3| * cx ^ 3 * D3 + |g2| * cx ^ 2 * D4) * N ^ 5 +
          (|Ce| * cx ^ 4 * D3 + |g3| * cx ^ 3 * D4) * N ^ 6 + |Ce| * cx ^ 4 * D4 * N ^ 7 := by
        ring
      rw [e1, hCR]
      have q6 := mul_le_mul_of_nonneg_left h6 hB
      have q7 := mul_le_mul_of_nonneg_left h7 hC
      linarith
    -- the definite part
    have hab : |hopfH2 H lam g2 a b| ≤ Ch * (a ^ 2 + b ^ 2) := hbh a b
    have hr2 : m2 * (a ^ 2 + b ^ 2) ≤ H * a ^ 2 + b ^ 2 := by
      have h1 : m2 ≤ H := min_le_left _ _
      have h2 : m2 ≤ 1 := min_le_right _ _
      have q0 := mul_le_mul_of_nonneg_right h1 (sq_nonneg a)
      have q1 := mul_le_mul_of_nonneg_right h2 (sq_nonneg b)
      linarith
    have hσ : a ^ 2 + b ^ 2 + c ^ 2 ≤ 1 := by
      rw [hsq]; exact pow_le_one₀ hN0 hN1
    have hq := hquart a b c (hopfH2 H lam g2 a b) (H * a ^ 2 + b ^ 2) hr2 hab hσ
    rw [hsq] at hq
    have hRle := le_abs_self R
    have e2 : (N ^ 2) ^ 2 = N ^ 4 := by ring
    rw [e2] at hq
    have e3 : -(N ^ 4 * (m - CR * N)) = -(m * N ^ 4) + CR * N ^ 5 := by ring
    rw [e3]
    rw [← hkdef]
    linarith
  -- conclusion
  set r := ν / (‖T‖ + 1) with hr
  have hr0 : 0 < r := by positivity
  have hTz : ∀ z : State 3, ‖z‖ < r → ‖T z‖ < ν := fun z hz => by
    calc ‖T z‖ ≤ ‖T‖ * ‖z‖ := T.le_opNorm z
      _ ≤ ‖T‖ * r := mul_le_mul_of_nonneg_left hz.le (norm_nonneg _)
      _ < ν := by
          rw [hr, mul_div_assoc', div_lt_iff₀ (by positivity)]
          linarith
  have hTne : ∀ z : State 3, z ≠ 0 → 0 < ‖T z‖ := fun z hz =>
    norm_pos_iff.mpr fun h => hz (hT (by rw [h, map_zero]))
  refine localAsymptoticStable_of_lie_neg (V := V) (R := r) (by norm_num) hr0 hV
    hf.continuous.continuousOn ?_ ?_ ?_
  · show poly3 (hopfQ H) (ℓa 0) (ℓb 0) (ℓc 0) + poly3 (hopfW3 H lam g2) (ℓa 0) (ℓb 0) (ℓc 0) +
      poly3 (hopfW4 H lam g2 g3) (ℓa 0) (ℓb 0) (ℓc 0) = 0
    simp only [map_zero]
    rw [poly3_zero (by norm_num) (hopfQ_degree H),
      poly3_zero (by norm_num) (hopfW3_degree H lam g2),
      poly3_zero (by norm_num) (hopfW4_degree H lam g2 g3)]
    ring
  · intro z hz hne
    rw [sub_zero] at hz
    have h1 := hVpos z (hTz z hz)
    have h2 := hTne z hne
    have : 0 < m2 / 2 * ‖T z‖ ^ 2 := by positivity
    linarith
  · intro z hz hne
    rw [sub_zero] at hz
    have hN := hTz z hz
    have h2 := hTne z hne
    have h1 := hVlie z hN
    have hlt : CR * ‖T z‖ < m := by
      have h3 : ‖T z‖ < m / (CR + 1) := hN.trans_le hν3
      rw [lt_div_iff₀ (by positivity)] at h3
      linarith [norm_nonneg (T z)]
    have : 0 < ‖T z‖ ^ 4 * (m - CR * ‖T z‖) := mul_pos (pow_pos h2 4) (by linarith)
    linarith

/-! ## Planar sine–Liénard weak focus: Lyapunov polynomials -/

section PlanarLienard

open Asymptotics

/-- Nonlinear part of the boundary normal form, `N(φ) = A(φ − sin φ) + B(1 − cos φ)`. -/
def hopfN (A B φ : ℝ) : ℝ := A * (φ - Real.sin φ) + B * (1 - Real.cos φ)

/-- The cubic Taylor polynomial `B φ²/2 + A φ³/6` of `N`. -/
def hopfN3 (A B φ : ℝ) : ℝ := B / 2 * φ ^ 2 + A / 6 * φ ^ 3

/-- A quadratic form plus six cubic/quartic monomials:
`(φ² + q w²)/2 + c₀ w³ + c₂ φ²w + c₃ φ³ + c₄ φw³ + c₅ φ³w + c₆ φ⁴`. -/
def lyapPoly (q c₀ c₂ c₃ c₄ c₅ c₆ φ w : ℝ) : ℝ :=
  1 / 2 * (φ ^ 2 + q * w ^ 2) + c₀ * w ^ 3 + c₂ * (φ ^ 2 * w) + c₃ * φ ^ 3 + c₄ * (φ * w ^ 3) +
    c₅ * (φ ^ 3 * w) + c₆ * φ ^ 4

/-- `∂ lyapPoly / ∂φ`. -/
def lyapPolyφ (c₂ c₃ c₄ c₅ c₆ φ w : ℝ) : ℝ :=
  φ + c₂ * (2 * (φ * w)) + c₃ * (3 * φ ^ 2) + c₄ * w ^ 3 + c₅ * (3 * (φ ^ 2 * w)) +
    c₆ * (4 * φ ^ 3)

/-- `∂ lyapPoly / ∂w`. -/
def lyapPolyw (q c₀ c₂ c₄ c₅ φ w : ℝ) : ℝ :=
  q * w + c₀ * (3 * w ^ 2) + c₂ * φ ^ 2 + c₄ * (3 * (φ * w ^ 2)) + c₅ * φ ^ 3

/-- First Lyapunov quantity of the normal form, `κ = −β(A² + B²)/(16A)`. -/
def hopfκ (A B β : ℝ) : ℝ := -β * (A ^ 2 + B ^ 2) / (16 * A)

/-- The normal-form Lyapunov polynomial of the boundary. -/
def hopfW (A B α β φ w : ℝ) : ℝ :=
  lyapPoly (α / A) (B * α * β / (3 * A ^ 2)) (B * β / (2 * A)) (-B / (6 * A))
    (α * β * (A ^ 2 + B ^ 2) / (16 * A ^ 3)) (β * (5 * A ^ 2 - 3 * B ^ 2) / (48 * A ^ 2))
    (-(A * α + 3 * B ^ 2 * β ^ 2) / (24 * A * α)) φ w

/-- `∂ hopfW / ∂φ`. -/
def hopfWφ (A B α β φ w : ℝ) : ℝ :=
  lyapPolyφ (B * β / (2 * A)) (-B / (6 * A)) (α * β * (A ^ 2 + B ^ 2) / (16 * A ^ 3))
    (β * (5 * A ^ 2 - 3 * B ^ 2) / (48 * A ^ 2)) (-(A * α + 3 * B ^ 2 * β ^ 2) / (24 * A * α)) φ w

/-- `∂ hopfW / ∂w`. -/
def hopfWw (A B α β φ w : ℝ) : ℝ :=
  lyapPolyw (α / A) (B * α * β / (3 * A ^ 2)) (B * β / (2 * A))
    (α * β * (A ^ 2 + B ^ 2) / (16 * A ^ 3)) (β * (5 * A ^ 2 - 3 * B ^ 2) / (48 * A ^ 2)) φ w

/-- The normal-form identity: along the cubic truncation `φ̇ = αw + βN₃`, `ẇ = −Aφ + N₃` the
derivative of `hopfW` is `−κ (φ² + (α/A) w²)²` up to eight monomials of degree five and six. -/
@[tmio T, powerlib_foundation] theorem hopf_lie_poly {A B α β : ℝ} (hA : A ≠ 0) (hα : α ≠ 0) (φ w : ℝ) :
    hopfWφ A B α β φ w * (α * w + β * hopfN3 A B φ) +
        hopfWw A B α β φ w * (-A * φ + hopfN3 A B φ) +
        hopfκ A B β * (φ ^ 2 + α / A * w ^ 2) ^ 2 =
      B * α * β ^ 2 * (A ^ 2 + B ^ 2) / (32 * A ^ 3) * (φ ^ 2 * w ^ 3) +
      B * α * β * (25 * A ^ 2 + 9 * B ^ 2) / (96 * A ^ 3) * (φ ^ 3 * w ^ 2) +
      α * β ^ 2 * (A ^ 2 + B ^ 2) / (96 * A ^ 2) * (φ ^ 3 * w ^ 3) +
      B * β ^ 2 * (31 * A ^ 2 - 9 * B ^ 2) / (96 * A ^ 2) * (φ ^ 4 * w ^ 1) +
      α * β * (A ^ 2 + B ^ 2) / (32 * A ^ 2) * (φ ^ 4 * w ^ 2) +
      -B * β * (A ^ 2 * α + 8 * A * B ^ 2 * β ^ 2 + B ^ 2 * α) / (32 * A ^ 2 * α) *
        (φ ^ 5 * w ^ 0) +
      β ^ 2 * (5 * A ^ 2 - 3 * B ^ 2) / (96 * A) * (φ ^ 5 * w ^ 1) +
      -β * (A ^ 2 * α + 8 * A * B ^ 2 * β ^ 2 + B ^ 2 * α) / (96 * A * α) * (φ ^ 6 * w ^ 0) := by
  unfold hopfWφ hopfWw lyapPolyφ lyapPolyw hopfN3 hopfκ
  field_simp
  ring

/-- The Taylor remainder of `N` is of fourth order. -/
@[tmio T, powerlib_foundation] theorem hopfN_sub_hopfN3_isBigO (A B : ℝ) :
    (fun φ => hopfN A B φ - hopfN3 A B φ) =O[𝓝 0] fun φ => φ ^ 4 := by
  refine IsBigO.of_bound (|A| + |B|) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with φ hφ
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hφ
  have hs := Real.sin_bound hφ.le
  have hc := Real.cos_bound hφ.le
  have he : hopfN A B φ - hopfN3 A B φ =
      -A * (Real.sin φ - (φ - φ ^ 3 / 6)) - B * (Real.cos φ - (1 - φ ^ 2 / 2)) := by
    unfold hopfN hopfN3; ring
  rw [he, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have h5 : |φ| ^ 5 ≤ |φ| ^ 4 := pow_le_pow_of_le_one (abs_nonneg _) hφ.le (by norm_num)
  have h4 : 0 ≤ |φ| ^ 4 := by positivity
  calc |-A * (Real.sin φ - (φ - φ ^ 3 / 6)) - B * (Real.cos φ - (1 - φ ^ 2 / 2))|
      ≤ |A| * |Real.sin φ - (φ - φ ^ 3 / 6)| + |B| * |Real.cos φ - (1 - φ ^ 2 / 2)| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_neg]
    _ ≤ |A| * (|φ| ^ 5 / 100) + |B| * (|φ| ^ 4 * (5 / 96)) := by
        gcongr
    _ ≤ (|A| + |B|) * |φ| ^ 4 := by
        have hA := abs_nonneg A
        have hB := abs_nonneg B
        nlinarith

/-- Derivative of `lyapPoly` in the coordinates `φ = z₀`, `w = z₁ − b z₀`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_lyapPoly (q c₀ c₂ c₃ c₄ c₅ c₆ b : ℝ)
    (z : Dynamics.State 2) :
    HasFDerivAt (fun z : Dynamics.State 2 => lyapPoly q c₀ c₂ c₃ c₄ c₅ c₆ (z 0) (z 1 - b * z 0))
      (lyapPolyφ c₂ c₃ c₄ c₅ c₆ (z 0) (z 1 - b * z 0) •
          (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ) +
        lyapPolyw q c₀ c₂ c₄ c₅ (z 0) (z 1 - b * z 0) •
          ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : Dynamics.State 2 →L[ℝ] ℝ) -
            b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : Dynamics.State 2 →L[ℝ] ℝ))) z := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2) :
    Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) :
    Dynamics.State 2 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have hw := h1.sub (h0.const_mul b)
  have h := ((((((((h0.pow 2).add ((hw.pow 2).const_mul q)).const_mul (1 / 2 : ℝ)).add
    ((hw.pow 3).const_mul c₀)).add (((h0.pow 2).mul hw).const_mul c₂)).add
    ((h0.pow 3).const_mul c₃)).add ((h0.mul (hw.pow 3)).const_mul c₄)).add
    (((h0.pow 3).mul hw).const_mul c₅)).add ((h0.pow 4).const_mul c₆)
  unfold lyapPoly
  refine h.congr_fderiv ?_
  ext v
  simp [lyapPolyφ, lyapPolyw]
  ring

@[tmio T, powerlib_foundation] theorem contDiff_lyapPoly (q c₀ c₂ c₃ c₄ c₅ c₆ b : ℝ) :
    ContDiff ℝ 1
      (fun z : Dynamics.State 2 => lyapPoly q c₀ c₂ c₃ c₄ c₅ c₆ (z 0) (z 1 - b * z 0)) := by
  unfold lyapPoly
  fun_prop

end PlanarLienard

end powerlib.Dynamics.Degenerate
