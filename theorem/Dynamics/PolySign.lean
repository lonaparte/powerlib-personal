import theorem.Dynamics.PolyCertificate

/-! # Signs of integer polynomials on intervals by Möbius transforms (foundation)

An integer polynomial `p` of degree `n` is positive on an interval when the coefficients of its
Möbius transform `(C + D t)ⁿ p((A + B t)/(C + D t))` are nonnegative with a positive constant
term: the map `t ↦ (A + B t)/(C + D t)` sends `t ≥ 0` onto the interval, and a polynomial with
nonnegative coefficients and positive constant term is positive on `t ≥ 0` (the case of zero sign
variations of Descartes' rule). The transform is computed by an executable function on
coefficient lists, so a sign certificate is a finite integer computation (`decide +kernel`).

Scope.
* Generic: integer coefficient lists read by `Dynamics.PolyCertificate.zeval`; the intervals
  `[A/C, B/C)` (`D = C`), `[A/C, ∞)` (`B = C`, `D = 0`) and `(0, B/C]` (`A = 0` in the numerator
  position, `s = B/(C + C t)`), `A, B, C` integers, `C > 0`. No model, no limit: exact
  inequalities only.

Source: the Möbius (Vincent–Collins–Akritas) transform of real-root isolation, Collins–Akritas,
*Polynomial real root isolation using Descartes' rule of signs* (SYMSAC 1976); the zero-variation
case needs no rule of signs, only the positivity of a polynomial with nonnegative coefficients.

Results.
* `zmob` (the transform), `zeval_zmob`, `zeval_zmob_list` (its value), `zPos` (positive constant
  term, nonnegative coefficients), `zeval_nonneg_of_all`, `zeval_pos_of_zPos`.
* **`zeval_pos_of_zmob_Ico`**, **`zeval_pos_of_zmob_Ici`**, **`zeval_pos_of_zmob_Ioc`**: a
  certified transform gives positivity on `[A/C, B/C)`, `[A/C, ∞)` and `(0, B/C]`.
-/

namespace powerlib.Dynamics.PolyCertificate

/-- The Möbius transform `(C + D t)^{deg} p((A + B t)/(C + D t))` of a coefficient list (degree
`= length − 1`). -/
def zmob (A B C D : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => zadd (zscale a (zpow [C, D] p.length)) (zmul [A, B] (zmob A B C D p))

/-- A positive constant term and nonnegative coefficients. -/
def zPos : List ℤ → Bool
  | [] => false
  | a :: p => decide (0 < a) && p.all (fun c => decide (0 ≤ c))

@[tmio T, powerlib_foundation] theorem zeval_zmob (A B C D : ℤ) {t : ℝ}
    (ht : (C : ℝ) + D * t ≠ 0) :
    ∀ (p : List ℤ) (a : ℤ), zeval (zmob A B C D (a :: p)) t =
      ((C : ℝ) + D * t) ^ p.length * zeval (a :: p) ((A + B * t) / (C + D * t))
  | [], a => by
    simp [zmob, zeval_zadd, zeval_zscale, zeval_zpow, zeval_zmul, zeval]
  | b :: p, a => by
    have ih := zeval_zmob A B C D ht p b
    have h2 : zeval [C, D] t = (C : ℝ) + D * t := by simp [zeval]; ring
    have h3 : zeval [A, B] t = ((C : ℝ) + D * t) * (((A : ℝ) + B * t) / (C + D * t)) := by
      rw [mul_div_cancel₀ _ ht]; simp [zeval]; ring
    rw [zmob, zeval_zadd, zeval_zscale, zeval_zpow, zeval_zmul, ih, h2, h3]
    simp only [zeval, List.length_cons, pow_succ]
    ring

/-- The value of the transform for any list (`deg = length − 1`). -/
@[tmio T, powerlib_foundation] theorem zeval_zmob_list (A B C D : ℤ) {t : ℝ}
    (ht : (C : ℝ) + D * t ≠ 0) (p : List ℤ) :
    zeval (zmob A B C D p) t =
      ((C : ℝ) + D * t) ^ (p.length - 1) * zeval p ((A + B * t) / (C + D * t)) := by
  cases p with
  | nil => simp [zmob, zeval]
  | cons a p => rw [zeval_zmob A B C D ht p a]; simp

@[tmio T, powerlib_foundation] theorem zeval_nonneg_of_all :
    ∀ {p : List ℤ}, p.all (fun c => decide (0 ≤ c)) = true → ∀ {t : ℝ}, 0 ≤ t → 0 ≤ zeval p t
  | [], _, t, _ => by simp [zeval]
  | a :: p, h, t, ht => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have h0 : (0 : ℝ) ≤ a := by exact_mod_cast h.1
    have := zeval_nonneg_of_all h.2 ht
    simp only [zeval]
    positivity

@[tmio T, powerlib_foundation] theorem zeval_pos_of_zPos {p : List ℤ} (h : zPos p = true)
    {t : ℝ} (ht : 0 ≤ t) : 0 < zeval p t := by
  cases p with
  | nil => simp [zPos] at h
  | cons a p =>
    simp only [zPos, Bool.and_eq_true, decide_eq_true_eq] at h
    have h0 : (0 : ℝ) < a := by exact_mod_cast h.1
    have := zeval_nonneg_of_all h.2 ht
    simp only [zeval]
    positivity

/-- **Positivity on `[A/C, B/C)`** from the transform `s = (A + B t)/(C + C t)`. -/
@[tmio T, powerlib_foundation] theorem zeval_pos_of_zmob_Ico {A B C : ℤ} (hC : 0 < C)
    {p : List ℤ} (h : zPos (zmob A B C C p) = true) {s : ℝ}
    (h1 : (A : ℝ) / C ≤ s) (h2 : s < (B : ℝ) / C) : 0 < zeval p s := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hA : (A : ℝ) ≤ C * s := by rwa [div_le_iff₀ hC', mul_comm] at h1
  have hB : C * s < (B : ℝ) := by rwa [lt_div_iff₀ hC', mul_comm] at h2
  set t : ℝ := (C * s - A) / (B - C * s) with htd
  have hden : (0 : ℝ) < B - C * s := by linarith
  have ht : 0 ≤ t := div_nonneg (by linarith) hden.le
  have hL : (0 : ℝ) < C + C * t := by positivity
  have hs : ((A : ℝ) + B * t) / (C + C * t) = s := by
    rw [div_eq_iff hL.ne', htd]
    field_simp
    ring
  have e := zeval_zmob_list A B C C hL.ne' p
  rw [hs] at e
  have hq := zeval_pos_of_zPos h ht
  rw [e] at hq
  exact (pos_iff_pos_of_mul_pos hq).mp (pow_pos hL _)

/-- **Positivity on `[A/C, ∞)`** from the transform `s = (A + C t)/C`. -/
@[tmio T, powerlib_foundation] theorem zeval_pos_of_zmob_Ici {A C : ℤ} (hC : 0 < C)
    {p : List ℤ} (h : zPos (zmob A C C 0 p) = true) {s : ℝ} (h1 : (A : ℝ) / C ≤ s) :
    0 < zeval p s := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hA : (A : ℝ) ≤ C * s := by rwa [div_le_iff₀ hC', mul_comm] at h1
  set t : ℝ := (C * s - A) / C with htd
  have ht : 0 ≤ t := div_nonneg (by linarith) hC'.le
  have hL : (0 : ℝ) < C + (0 : ℤ) * t := by simp [hC']
  have hs : ((A : ℝ) + C * t) / (C + (0 : ℤ) * t) = s := by
    rw [htd]
    field_simp
    ring
  have e := zeval_zmob_list A C C 0 hL.ne' p
  rw [hs] at e
  have hq := zeval_pos_of_zPos h ht
  rw [e] at hq
  exact (pos_iff_pos_of_mul_pos hq).mp (pow_pos hL _)

/-- **Positivity on `(0, B/C]`** from the transform `s = B/(C + C t)`. -/
@[tmio T, powerlib_foundation] theorem zeval_pos_of_zmob_Ioc {B C : ℤ} (hC : 0 < C) (hB : 0 < B)
    {p : List ℤ} (h : zPos (zmob B 0 C C p) = true) {s : ℝ} (h1 : 0 < s)
    (h2 : s ≤ (B : ℝ) / C) : 0 < zeval p s := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hBs : C * s ≤ (B : ℝ) := by rwa [le_div_iff₀ hC', mul_comm] at h2
  set t : ℝ := (B - C * s) / (C * s) with htd
  have hCs : (0 : ℝ) < C * s := by positivity
  have ht : 0 ≤ t := div_nonneg (by linarith) hCs.le
  have hL : (0 : ℝ) < C + C * t := by positivity
  have hs : ((B : ℝ) + (0 : ℤ) * t) / (C + C * t) = s := by
    rw [div_eq_iff hL.ne', htd]
    field_simp
    ring
  have e := zeval_zmob_list B 0 C C hL.ne' p
  rw [hs] at e
  have hq := zeval_pos_of_zPos h ht
  rw [e] at hq
  exact (pos_iff_pos_of_mul_pos hq).mp (pow_pos hL _)

end powerlib.Dynamics.PolyCertificate
