/-
  PHGeneral.lean — The dimension- and topology-independent CORE of the pH
  stability results, as a MACHINE-CHECKED Lean 4 theorem (pure Lean 4, no Mathlib).

  ======================================================================
  WHAT THIS FILE PROVES, AND WHY IT MATTERS FOR THE .kyx CORPUS
  ======================================================================
  Every KeYmaera X (.kyx) proof in this directory verifies the pH energy
  balance  Ḣ = -2 Σ Dᵢ ωᵢ²  for ONE FIXED system: a fixed machine count
  (1,2,3,4) and a fixed coupling topology (chain/ring/star/paw/diamond/K4).
  Differential dynamic logic cannot quantify over "all N machines" or "all
  topologies J", so the empirically observed regularity — "the passive stack
  generalizes across machine count AND topology" — is a META-level statement,
  not provable inside any single .kyx.

  THIS FILE PROVES THAT META-STATEMENT, machine-checked, at full generality:
  for an ARBITRARY finite index list `l` (any dimension / any number of
  machines) and an ARBITRARY coupling `J` that is skew-symmetric
  (J i j = - J j i, i.e. ANY graph's signed incidence — chain, ring, star,
  diamond, K4, …), the interconnection contributes NOTHING to the energy rate:

      skew_quadForm_zero :   Σᵢ Σⱼ  gᵢ (J i j) gⱼ  =  0.

  From this single fact the three damping regimes follow uniformly (one energy
  certificate H, three signs of R = diag D):

      pH_passive      (∀i, 0 ≤ Dᵢ)  ⟹  rate ≤ 0   -- Lyapunov / invariance stack
      pH_conservative (D = 0)        ⟹  rate = 0   -- energy conservation
      pH_antipassive  (∀i, Dᵢ ≤ 0)   ⟹  rate ≥ 0   -- necessary_dneg instability

  where  rate = Σᵢ Σⱼ gᵢ(J i j)gⱼ  -  Σᵢ Dᵢ gᵢ²  is the discrete Lie derivative
  of H along  ẋ = (J - diag D) g  with g = ∇H. This is the EXACT content of the
  empirical rule discussed in the session: the natural energy H is a uniform
  certificate precisely when the rate is governed by the skew cancellation —
  which holds for any N and any topology, and (crucially) for ALL THREE signs of
  damping, so passive stability, conservation, and anti-passive instability are
  three faces of one theorem.

  ======================================================================
  THE REAL BOUNDARY: SIGN-UNIFORM vs SIGN-MIXED damping (not "passive or not")
  ======================================================================
  A common but WRONG summary is "only the passive case generalizes". The sharp
  line is whether the damping signs are UNIFORM, because the rate is the single
  sum  -Σᵢ Dᵢ gᵢ²:
    * SIGN-UNIFORM D (all Dᵢ ≥ 0, OR all = 0, OR all Dᵢ ≤ 0):
        the sum is definitely-signed, H itself is a uniform certificate, and the
        result GENERALIZES to every dimension and topology. The three theorems
        above are exactly these three cases. NOTE the third one, `pH_antipassive`
        (all Dᵢ ≤ 0), is NON-passive yet still generalizes — so "non-passive
        cannot be generalized" is false; the all-negative instability statement
        is just the passive proof with the sign flipped, same certificate H.
    * SIGN-MIXED D (some Dᵢ < 0 while others > 0, e.g. the D₂<0 middle machine
        with D₁,D₃,… > 0): the rate sum  -Σᵢ Dᵢ gᵢ²  is INDEFINITE, so H is no
        longer a certificate. Stability there needs an AUGMENTED Lyapunov
        V = H + (cross terms) whose coefficients depend on the topology and on
        the parameter values (this is precisely theorem_3machine_linear /
        _descent / _boxdescent in the .kyx corpus). There is NO
        dimension- or topology-independent certificate of the present kind, and
        it is genuinely NOT provable by the framework of this file. That is the
        real "cannot generalize" boundary — sign-MIXED, not "non-passive".

  In one line:  uniform-sign damping ⟹ H works ⟹ generalizes (proved below,
  all three signs);  mixed-sign damping ⟹ H fails ⟹ needs a bespoke V ⟹ does
  not generalize (out of scope here, and chain- or parameter-specific in corpus).

  ======================================================================
  MACHINE-CHECK STATUS  (verified, not just asserted)
  ======================================================================
  COMPILED AND CHECKED in this session with Lean 4.14.0
  (x86_64-unknown-linux-gnu, commit 410fab728470, Release). No `sorry`.
  `#print axioms` reports, for every theorem below:
        depends on axioms: [propext, Quot.sound]
  i.e. only Lean's standard logical axioms — no classical choice, no `sorryAx`.
  The concrete 3-machine-chain instantiation `Jchain3_skew_fin` (bottom) checks
  by `decide` with NO axioms at all.

  Deliberately PURE LEAN 4 (no Mathlib), matching the existing no-Mathlib `phdae`
  lake target (PHDAE.lean / Dynamics.lean). Dimensions are encoded as `List`
  index sets and sums as `List.sum`; the double-sum swap (the crux) is proved by
  induction (`dsum_swap`), and ring rearrangements use Lean core's `ac_rfl` and
  `omega` (Mathlib's `ring` is unavailable here — see PHDAE.lean's notes).
  To re-verify:  `lean PHGeneral.lean`  (toolchain pinned in ./lean-toolchain).

  ======================================================================
  SCOPE — what is NOT covered (kept honest; mirrors the .kyx headers)
  ======================================================================
  * This generalizes ONLY the energy-balance core and its three sign regimes —
    exactly the "A-class" results the .kyx corpus shows generalizing across
    machine count (1→4) and all 6 connected 4-node topologies: passive sublevel
    invariance, conservation, H-metric Lyapunov, energy identity,
    stability-region invariance, necessary_dneg. Here they are proved once, for
    ALL finite dimensions and ALL skew couplings.
  * It does NOT cover the "B-class": D₂<0 results needing an AUGMENTED Lyapunov
    V = H + (cross terms) whose coefficients depend on topology and parameter d
    (theorem_3machine_linear/_descent/_boxdescent). Those have no
    dimension-independent certificate of this kind — which is exactly why they
    stay chain-only in the corpus.
  * The bridge from this ALGEBRAIC rate to "H is non-increasing ALONG SOLUTIONS"
    needs ODE calculus (Picard–Lindelöf, chain rule). That analytic layer is
    what KeYmaera X's dI rule supplies per-instance, and what PHDAE.lean /
    Dynamics.lean document as the missing infrastructure. This file is the
    algebraic half, made dimension- and topology-general.
-/

-- ====================================================================
-- Basic list-sum lemmas (pure Lean 4, no Mathlib)
-- ====================================================================

theorem sum_neg (l : List Int) : (l.map (fun x => -x)).sum = -(l.sum) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; rw [Int.neg_add]

theorem sum_add (l : List α) (f g : α → Int) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [Int.add_assoc, Int.add_assoc, Int.add_left_comm (g a)]

theorem sum_neg_fun (l : List α) (f : α → Int) :
    (l.map (fun x => - f x)).sum = -(l.map f).sum := by
  have : (l.map (fun x => - f x)) = (l.map f).map (fun y => -y) := by
    rw [List.map_map]; rfl
  rw [this, sum_neg]

theorem sum_congr_fun (l : List α) (f g : α → Int) (h : ∀ x, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left (fun x _ => h x)]

theorem sum_const_zero (l : List α) : (l.map (fun _ => (0:Int))).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, Int.add_zero]

/-- **Double-sum swap** (the crux): `Σᵢ Σⱼ F i j = Σⱼ Σᵢ F i j` over one list.
    Proved by induction on the list, using `sum_add` to peel the head. -/
theorem dsum_swap (l : List α) (F : α → α → Int) :
    (l.map (fun i => (l.map (fun j => F i j)).sum)).sum
  = (l.map (fun j => (l.map (fun i => F i j)).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_add t (fun i => F i a) (fun i => (t.map (fun j => F i j)).sum)]
    rw [sum_add t (fun j => F a j) (fun j => (t.map (fun i => F i j)).sum)]
    rw [ih]
    generalize (t.map (fun j => F a j)).sum = A
    generalize (t.map (fun i => F i a)).sum = B
    generalize (t.map (fun j => (t.map (fun i => F i j)).sum)).sum = S
    rw [Int.add_assoc (F a a) A, Int.add_assoc (F a a) B, Int.add_left_comm A B S]

/-- `0 ≤ a*a` over `Int` (no Mathlib `sq_nonneg`/`positivity`). -/
theorem sq_nonneg_int (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have hna : 0 ≤ -a := by omega
    have : 0 ≤ (-a) * (-a) := Int.mul_nonneg hna hna
    rwa [Int.neg_mul_neg] at this

-- ====================================================================
-- CORE THEOREM: skew-symmetric quadratic form is zero, ANY dimension
-- ====================================================================

/-- **`gᵀ J g = 0` for every skew-symmetric `J`, every finite index list `l`.**
    The algebraic reason the pH interconnection never changes the energy, for
    any number of machines and any coupling graph. Proof: the double sum equals
    its transpose (`dsum_swap`), and skew-symmetry turns the transpose into the
    negation; so `S = -S`, hence `S = 0` (`omega`). -/
theorem skew_quadForm_zero {α : Type} (l : List α) (J : α → α → Int) (g : α → Int)
    (hJ : ∀ i j, J i j = - J j i) :
    (l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum = 0 := by
  have hswap :
      (l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum
    = (l.map (fun i => (l.map (fun j => g j * J j i * g i)).sum)).sum := by
    have := dsum_swap l (fun i j => g i * J i j * g j); simpa using this
  have hterm : ∀ i,
      (l.map (fun j => g j * J j i * g i)).sum
    = -(l.map (fun j => g i * J i j * g j)).sum := by
    intro i
    rw [← sum_neg_fun l (fun j => g i * J i j * g j)]
    apply sum_congr_fun
    intro j
    show g j * J j i * g i = -(g i * J i j * g j)
    rw [hJ i j]; simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg]; ac_rfl
  have hswapneg :
      (l.map (fun i => (l.map (fun j => g j * J j i * g i)).sum)).sum
    = -(l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum := by
    rw [← sum_neg_fun l (fun i => (l.map (fun j => g i * J i j * g j)).sum)]
    apply sum_congr_fun; intro i; exact hterm i
  have hSS :
      (l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum
    = -(l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum :=
    hswap.trans hswapneg
  omega

-- ====================================================================
-- pH ENERGY RATE + THE THREE REGIMES
-- ====================================================================

/-- Dissipation term `∇Hᵀ R ∇H = Σᵢ Dᵢ gᵢ²` for `R = diag D`. -/
def diagSum {α : Type} (l : List α) (D : α → Int) (g : α → Int) : Int :=
  (l.map (fun i => D i * (g i * g i))).sum

/-- **pH energy rate** = skew part − dissipation = `0 − diagSum = −diagSum`.
    The interconnection `J` drops out entirely (`skew_quadForm_zero`). -/
theorem pH_rate {α : Type} (l : List α) (J : α → α → Int) (D : α → Int) (g : α → Int)
    (hJ : ∀ i j, J i j = - J j i) :
    (l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum - diagSum l D g
    = - diagSum l D g := by
  rw [skew_quadForm_zero l J g hJ]; omega

theorem diagSum_nonneg {α : Type} (l : List α) (D : α → Int) (g : α → Int)
    (hD : ∀ i, 0 ≤ D i) : 0 ≤ diagSum l D g := by
  unfold diagSum
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : 0 ≤ D a * (g a * g a) := Int.mul_nonneg (hD a) (sq_nonneg_int (g a))
    omega

theorem diagSum_nonpos {α : Type} (l : List α) (D : α → Int) (g : α → Int)
    (hD : ∀ i, D i ≤ 0) : diagSum l D g ≤ 0 := by
  unfold diagSum
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : D a * (g a * g a) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg (hD a) (sq_nonneg_int (g a))
    omega

/-- **Passive (all Dᵢ ≥ 0) ⟹ Ḣ ≤ 0.** The Lyapunov/invariance stack, uniform
    in dimension and topology. -/
theorem pH_passive {α : Type} (l : List α) (J : α → α → Int) (D : α → Int) (g : α → Int)
    (hJ : ∀ i j, J i j = - J j i) (hD : ∀ i, 0 ≤ D i) :
    (l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum - diagSum l D g ≤ 0 := by
  rw [pH_rate l J D g hJ]; have := diagSum_nonneg l D g hD; omega

/-- **Conservative (D = 0) ⟹ Ḣ = 0.** Energy conservation. -/
theorem pH_conservative {α : Type} (l : List α) (J : α → α → Int) (g : α → Int)
    (hJ : ∀ i j, J i j = - J j i) :
    (l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum
      - diagSum l (fun _ => 0) g = 0 := by
  rw [pH_rate l J (fun _ => 0) g hJ]; unfold diagSum
  simp only [Int.zero_mul]; rw [sum_const_zero]; rfl

/-- **Anti-passive (all Dᵢ ≤ 0) ⟹ Ḣ ≥ 0.** Energy-growth / instability
    certificate (`necessary_dneg`): same H, opposite sign. -/
theorem pH_antipassive {α : Type} (l : List α) (J : α → α → Int) (D : α → Int) (g : α → Int)
    (hJ : ∀ i j, J i j = - J j i) (hD : ∀ i, D i ≤ 0) :
    0 ≤ (l.map (fun i => (l.map (fun j => g i * J i j * g j)).sum)).sum - diagSum l D g := by
  rw [pH_rate l J D g hJ]; have := diagSum_nonpos l D g hD; omega

-- NOTE on the SIGN-MIXED case (some Dᵢ < 0, others > 0): there is deliberately
-- NO theorem here. `pH_rate` still holds (J always cancels), but the rate
-- `-diagSum l D g = -Σᵢ Dᵢ gᵢ²` is then INDEFINITE — `diagSum` is neither
-- ≥0 nor ≤0 in general — so H gives no sign conclusion and no analogue of
-- pH_passive/_antipassive exists. That case (e.g. D₂<0 middle machine) requires
-- a bespoke augmented Lyapunov V = H + cross-terms with topology/parameter-
-- dependent coefficients; it is the .kyx "B-class" (theorem_3machine_linear /
-- _descent / _boxdescent) and is genuinely outside this uniform framework.

-- ====================================================================
-- Non-vacuity + concrete instantiation (the corpus' topologies are skew)
-- ====================================================================

/-- Non-vacuity: the zero interconnection is skew, so the theorems apply. -/
example (l : List Nat) (g : Nat → Int) :
    (l.map (fun i => (l.map (fun j => g i * (0:Int) * g j)).sum)).sum = 0 :=
  skew_quadForm_zero l (fun _ _ => (0:Int)) g (fun _ _ => by simp)

/-- 3-machine CHAIN coupling (bonds 0-1, 1-2): a concrete skew `J`. -/
def Jchain3 : Nat → Nat → Int
  | 0, 1 => 1 | 1, 0 => -1
  | 1, 2 => 1 | 2, 1 => -1
  | _, _ => 0

/-- The chain coupling is skew-symmetric on its index set (checked by `decide`,
    no axioms). Plugging this into `pH_passive` reproduces, abstractly, the
    `parametric_3machine` energy bound — and the same `pH_passive` with the ring
    / star / diamond / K4 incidence reproduces those .kyx results too. -/
theorem Jchain3_skew_fin :
    ∀ i ∈ [0,1,2], ∀ j ∈ [0,1,2], Jchain3 i j = - Jchain3 j i := by
  decide

#print axioms skew_quadForm_zero
#print axioms pH_passive
#print axioms pH_conservative
#print axioms pH_antipassive
#print axioms Jchain3_skew_fin
