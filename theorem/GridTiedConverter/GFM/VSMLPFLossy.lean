import theorem.GridTiedConverter.GFM.VSMLPFHopf

/-! # Grid-forming VSM with a power filter on a lossy line, read as the lossless model

Model boundary.
* State `x = (δ, ω, P_f) : Dynamics.State 3`, in this order: angle of the internal EMF `E∠δ`
  relative to the stiff grid voltage `V∠0` (rad), angular-frequency deviation (rad/s), filtered
  (measured) active power (pu).
* Continuous time, autonomous, no input:
  `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P(δ) − P_f)`, with the one-harmonic power
  characteristic `P(δ) = c₀ + A sin(δ − α)` (`VSMLPFLossy.Pe`). For a voltage source behind a
  series impedance `R + jX` on a quasi-static (phasor) line, `c₀ = E²R/|Z|²`, `A = E V/|Z|`,
  `α = atan2(R, X)`, `|Z|² = R² + X²`; the lossless line `c₀ = α = 0`, `A = E V/X` is the model
  `VSMLPF` of `theorem/GridTiedConverter/GFM/VSMLPF.lean`. `M, D, ω_c, P_ref, c₀, A, α` are free
  reals; every statement lists its sign assumptions (physical range `M, D, ω_c > 0`, and `A > 0`
  for the loading angle).
* Active power is export-positive (the GFM exception, as in `VSMLPF`); per unit, single-phase
  equivalent (with amplitude-invariant dq quantities the three-phase power is `3/2` times it).
  Currents, reactive power and the line are not states.
* Excluded: line (electromagnetic) dynamics (the phasor reduction `di/dt = 0`), voltage and
  reactive-power loops (constant `E`), inner current and voltage loops, current limiting, PLL,
  delays, PWM.
* Level: equilibria and the sentences of a selected point `(δ*, 0, P_ref)`, read through the
  lossless family.

Source: GFM counterpart study, note t3-bifurcation (a) (lossy translation `L4`, derived and
checked symbolically; scratch notes outside the repository); Kundur, *Power System Stability and
Control* (1994), Ch. 6 (power transfer through a series impedance, `P = E²R/|Z|² +
(E V/|Z|) sin(δ − α)`). Scaffold of the reading: `theorem/GridTiedConverter/GFM/VSMLPFLossy.agda`.

Results.
* `field_eq`: the lossy field is the lossless field of `toVSMLPF = ⟨M, D, ω_c, P_ref − c₀, A⟩` in
  the coordinates `(δ − α, ω, P_f − c₀)` (`offset`): the load offset `c₀` and the angle `α` are
  absorbed by a translation, so a lossy line changes no law of the lossless model, only the
  set-point `P₀ = P_ref − c₀` and the angle reference. Static evidence on the model.
* Equilibria (`field_eq_zero_iff`, `exists_equilibrium_iff`): `ω = 0`, `P_f = P_ref`,
  `P(δ) = P_ref`; one exists iff `|P_ref − c₀| ≤ A` (`A > 0`).
* `Model.field_eq_toVSMLPF`: about a selected angle `δ*` the translated field is the translated
  field of the lossless model `⟨toVSMLPF, δ* − α⟩` (`Model.toVSMLPF`), with the same
  synchronizing coefficient `K = A cos(δ* − α) = P'(δ*)` (`Model.toVSMLPF_K`).

Family and connection conclusions.
* `VSMLPFLossy.family`: a complete system (`VSMLPFLossy.Model`) is a parameter set with a selected
  angle `δ*`, read as the field translated so that `(δ*, 0, P_ref)` is the origin. Its requirement
  language is the lossless one (`VSMLPF.Requirement`, translation `VSMLPF.translate`) read in the
  lossy parameters (`VSMLPFLossy.Meets`): balance `c₀ + A sin(δ* − α) = P_ref`, positive
  `M, D, ω_c`, `K > 0`, the fast-filter Routh condition `K < D ω_c + D²/M`, and a destabilizing
  sign (`D ω_c + D²/M < K` or `K < 0`).
* The reading (scaffold `theorem/GridTiedConverter/GFM/VSMLPFLossy.agda`): every sentence of a
  lossy model denotes the preimage of its lossless denotation (`VSMLPFLossy.den_eq_preimage`, an
  equality of the systems, no context needed) and every requirement set is the preimage of the
  lossless one (`VSMLPFLossy.realize_eq_preimage`). Hence the lossless laws hold on the lossy
  line: the translation is sound (`VSMLPFLossy.chain_le_semantics`, from
  `VSMLPF.chain_le_semantics`); within positive `M, D, ω_c` local exponential stability is
  translated exactly (`VSMLPFLossy.exactUnder_locallyExponentiallyStable`); local asymptotic
  stability holds exactly at a balanced angle with `0 < K ≤ D ω_c + D²/M`
  (`VSMLPFLossy.mem_den_locallyAsymptoticallyStable_iff_of_physical`), the Hopf boundary
  `K = D ω_c + D²/M` included: it is a weak stable focus at every load and every line angle
  (`VSMLPFLossy.mem_den_locallyAsymptoticallyStable_of_hopf`, a supercritical Hopf point through
  the weak-focus coefficient of `theorem/GridTiedConverter/GFM/VSMLPFHopf.lean` with
  `P₀ = P_ref − c₀`).
* At the loading angle `δ₀ = α + arcsin((P_ref − c₀)/A)` (`VSMLPFLossy.atLoading`, positive
  parameters, `|P_ref − c₀| < A`): local exponential stability iff `K < D ω_c + D²/M`
  (`VSMLPFLossy.locallyExponentiallyStable_iff`), local asymptotic stability iff
  `K ≤ D ω_c + D²/M` (`VSMLPFLossy.locallyAsymptoticallyStable_iff`); the second equilibrium
  `α + π − arcsin((P_ref − c₀)/A)` is unstable (`VSMLPFLossy.unstable_atAntiLoading`).
-/

noncomputable section
namespace powerlib.GFM
open Set
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)

/-- Parameters of the three-state VSM + power filter on a lossy line. -/
structure VSMLPFLossy where
  M : ℝ
  D : ℝ
  ωc : ℝ
  Pref : ℝ
  c0 : ℝ
  A : ℝ
  α : ℝ

namespace VSMLPFLossy

variable (p : VSMLPFLossy)

/-- The power characteristic `P(δ) = c₀ + A sin(δ − α)`. -/
def Pe (δ : ℝ) : ℝ := p.c0 + p.A * Real.sin (δ - p.α)

/-- The closed-loop field. -/
def field (x : State 3) : State 3 :=
  mk3 (x 1) ((p.Pref - x 2 - p.D * x 1) / p.M) (p.ωc * (p.Pe (x 0) - x 2))

/-- The lossless parameters of the reading: inertia, damping and bandwidth unchanged, set-point
`P₀ = P_ref − c₀`, amplitude `K₀ = A`. -/
def toVSMLPF : VSMLPF := ⟨p.M, p.D, p.ωc, p.Pref - p.c0, p.A⟩

/-- The offset `(α, 0, c₀)` of the lossless coordinates `(δ − α, ω, P_f − c₀)`. -/
def offset : State 3 := mk3 p.α 0 p.c0

/-- The lossy field is the lossless field in the coordinates `(δ − α, ω, P_f − c₀)`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq (x : State 3) :
    p.field x = p.toVSMLPF.field (x - p.offset) := by
  apply state3_ext <;>
    simp only [field, VSMLPF.field_apply_zero, VSMLPF.field_apply_one, VSMLPF.field_apply_two,
      mk3_zero, mk3_one, mk3_two, PiLp.sub_apply, offset, toVSMLPF, Pe] <;> ring

@[tmio M, powerlib_domain] theorem contDiff_field {k : WithTop ℕ∞} : ContDiff ℝ k p.field := by
  have h : p.field = fun x => p.toVSMLPF.field (x - p.offset) := funext p.field_eq
  rw [h]
  exact p.toVSMLPF.contDiff_field.comp (contDiff_id.sub contDiff_const)

/-- Equilibria: `ω = 0`, `P_f = P_ref` and `P(δ) = P_ref`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_iff (hM : p.M ≠ 0) (hω : p.ωc ≠ 0) (x : State 3) :
    p.field x = 0 ↔ x 1 = 0 ∧ x 2 = p.Pref ∧ p.Pe (x 0) = p.Pref := by
  rw [field_eq, p.toVSMLPF.field_eq_zero_iff hM hω]
  simp only [PiLp.sub_apply, offset, mk3_zero, mk3_one, mk3_two, sub_zero, toVSMLPF, Pe]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, by linarith⟩

/-- Equilibria exist iff `|P_ref − c₀| ≤ A` (`VSMLPF.exists_equilibrium_iff` through `field_eq`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem exists_equilibrium_iff (hM : p.M ≠ 0) (hω : p.ωc ≠ 0)
    (hA : 0 < p.A) : (∃ x, p.field x = 0) ↔ |p.Pref - p.c0| ≤ p.A := by
  rw [show |p.Pref - p.c0| ≤ p.A ↔ |p.toVSMLPF.P0| ≤ p.toVSMLPF.K0 from Iff.rfl,
    ← p.toVSMLPF.exists_equilibrium_iff hM hω hA]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x - p.offset, by rw [← field_eq]; exact hx⟩
  · rintro ⟨y, hy⟩
    exact ⟨y + p.offset, by rw [field_eq, add_sub_cancel_right]; exact hy⟩

/-! ## Models read about a selected angle -/

/-- A lossy VSM + power-filter model read about a selected angle `δ*`: the operating point is
`(δ*, 0, P_ref)`. -/
structure Model where
  /-- The parameters. -/
  p : VSMLPFLossy
  /-- The selected angle `δ*`. -/
  δ : ℝ

/-- The selected point `(δ*, 0, P_ref)`. -/
def Model.point (m : Model) : State 3 := mk3 m.δ 0 m.p.Pref

/-- The closed-loop field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 3) : State 3 := m.p.field (z + m.point)

/-- The synchronizing coefficient `K = A cos(δ* − α) = P'(δ*)` at the selected angle. -/
def Model.K (m : Model) : ℝ := m.p.A * Real.cos (m.δ - m.p.α)

/-- The lossless reading: the parameters `toVSMLPF` about the angle `δ* − α`. -/
def Model.toVSMLPF (m : Model) : VSMLPF.Model := ⟨m.p.toVSMLPF, m.δ - m.p.α⟩

/-- The translated lossy field is the translated field of the lossless reading.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Model.field_eq_toVSMLPF (m : Model) :
    m.field = m.toVSMLPF.field := by
  funext z
  rw [Model.field, field_eq]
  show m.p.toVSMLPF.field (z + m.point - m.p.offset) =
    m.p.toVSMLPF.field (z + mk3 (m.δ - m.p.α) 0 (m.p.Pref - m.p.c0))
  congr 1
  apply state3_ext <;>
    simp only [PiLp.add_apply, PiLp.sub_apply, Model.point, offset, mk3_zero, mk3_one,
      mk3_two] <;> ring

@[tmio M, simp, powerlib_domain] theorem Model.toVSMLPF_K (m : Model) :
    m.toVSMLPF.K = m.K := rfl

/-- Satisfaction of the lossless requirements by a lossy model, in its own parameters: balance
`P(δ*) = P_ref`, positive `M, D, ω_c`, `K > 0`, the fast-filter condition `K < D ω_c + D²/M` and a
destabilizing sign. -/
def Meets (m : Model) : VSMLPF.Requirement → Prop
  | .balanced => m.p.Pe m.δ = m.p.Pref
  | .physical => 0 < m.p.M ∧ 0 < m.p.D ∧ 0 < m.p.ωc
  | .synchronizing => 0 < m.K
  | .fastFilter => m.K < m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M
  | .destabilizing => m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M < m.K ∨ m.K < 0

/-- The lossy VSM + power-filter family, with the lossless translation. -/
def family : Family Model VSMLPF.Requirement 3 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, VSMLPF.translate⟩

@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-- A lossy model meets a requirement exactly when its lossless reading does. -/
@[tmio M, powerlib_domain] private theorem meets_iff (m : Model) (q : VSMLPF.Requirement) :
    Meets m q ↔ VSMLPF.Meets m.toVSMLPF q := by
  cases q
  · show m.p.c0 + m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref ↔
      m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref - m.p.c0
    constructor <;> intro h <;> linarith
  all_goals exact Iff.rfl

/-! ## The reading as the lossless model -/

/-- **The lossy line is the lossless model in other coordinates.** Every sentence of a lossy model
denotes the preimage of the denotation of its lossless reading `⟨⟨M, D, ω_c, P_ref − c₀, A⟩,
δ* − α⟩`: the two translated fields are equal (`Model.field_eq_toVSMLPF`). -/
@[tmio TM, powerlib_domain] theorem den_eq_preimage :
    connection% (∀ s, family.den s = Model.toVSMLPF ⁻¹' VSMLPF.family.den s) := by
  unfold powerlib.TMIO.Statement
  intro s
  ext m
  rw [Set.mem_preimage, (connection_proof% Family.mem_den), (connection_proof% Family.mem_den)]
  change s.holds (.continuous (Port.System.autonomous m.field)) ↔
    s.holds (.continuous (Port.System.autonomous m.toVSMLPF.field))
  rw [m.field_eq_toVSMLPF]

/-- Every requirement set of the lossy family is the preimage of the lossless one: the lossy
requirements are the lossless requirements of the reading. -/
@[tmio M, powerlib_domain] theorem realize_eq_preimage :
    connection% (∀ Γ, TMIO.realize Meets Γ = Model.toVSMLPF ⁻¹' TMIO.realize VSMLPF.Meets Γ) := by
  unfold powerlib.TMIO.Statement
  intro Γ
  ext m
  rw [Set.mem_preimage, (connection_proof% TMIO.mem_realize),
    (connection_proof% TMIO.mem_realize)]
  exact forall₂_congr fun q _ => meets_iff m q

@[tmio TM, powerlib_domain] private theorem mem_den_iff {m : Model} {s : Sentence} :
    m ∈ family.den s ↔ m.toVSMLPF ∈ VSMLPF.family.den s := by
  have h := den_eq_preimage
  unfold powerlib.TMIO.Statement at h
  rw [h s, Set.mem_preimage]

@[tmio M, powerlib_domain] private theorem mem_realize_iff {m : Model}
    {Γ : Set VSMLPF.Requirement} :
    m ∈ TMIO.realize Meets Γ ↔ m.toVSMLPF ∈ TMIO.realize VSMLPF.Meets Γ := by
  have h := realize_eq_preimage
  unfold powerlib.TMIO.Statement at h
  rw [h Γ, Set.mem_preimage]

/-- The lossy translation is sound: its requirements are those of the lossless reading
(`VSMLPF.chain_le_semantics`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hv := VSMLPF.chain_le_semantics
  unfold powerlib.TMIO.Statement at hv
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  exact mem_den_iff.mpr (Family.chain_le_semantics_iff.mp hv s (mem_realize_iff.mp hm))

/-- Within positive `M, D, ω_c` local exponential stability of a lossy model is translated
exactly: a balanced angle with `0 < K < D ω_c + D²/M`
(`VSMLPF.exactUnder_locallyExponentiallyStable` through the reading, `Spectral.exactUnder_of_hub`).
-/
@[tmio TM, powerlib_domain] theorem exactUnder_locallyExponentiallyStable :
    connection% (family.ExactUnder {.physical} (.flow .locallyExponentiallyStable)) := by
  have hv := VSMLPF.exactUnder_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hv ⊢
  exact Spectral.exactUnder_of_hub (F := family) (G := VSMLPF.family) Model.toVSMLPF
    (fun _ hm => mem_realize_iff.mp hm) (fun _ _ => mem_den_iff) (fun _ _ => mem_realize_iff) hv

/-- **Local asymptotic stability on a lossy line within positive `M, D, ω_c`.** The operating
point `(δ*, 0, P_ref)` is locally asymptotically stable exactly when the angle is balanced,
`c₀ + A sin(δ* − α) = P_ref`, and `0 < K ≤ D ω_c + D²/M`, `K = A cos(δ* − α)` (the Hopf boundary
included; `VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical` through the reading). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_physical (m : Model)
    (hM : 0 < m.p.M) (hD : 0 < m.p.D) (hω : 0 < m.p.ωc) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.p.Pe m.δ = m.p.Pref ∧ 0 < m.K ∧
        m.K ≤ m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M}) := by
  have hv := VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical m.toVSMLPF hM hD hω
  unfold powerlib.TMIO.Statement at hv ⊢
  rw [mem_den_iff, hv, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  exact and_congr ((meets_iff m .balanced).symm) Iff.rfl

/-- **Supercritical Hopf point on a lossy line.** Positive `M, D, ω_c`, a balanced angle and
`K = D ω_c + D²/M` place a lossy model in local asymptotic stability, at every load and every line
angle `α` (`VSMLPF.mem_den_locallyAsymptoticallyStable_of_hopf` at `P₀ = P_ref − c₀`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_hopf (m : Model)
    (hM : 0 < m.p.M) (hD : 0 < m.p.D) (hω : 0 < m.p.ωc) (hb : m.p.Pe m.δ = m.p.Pref)
    (hK : m.K = m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have hv := VSMLPF.mem_den_locallyAsymptoticallyStable_of_hopf m.toVSMLPF hM hD hω
    ((meets_iff m .balanced).mp hb) hK
  unfold powerlib.TMIO.Statement at hv ⊢
  exact mem_den_iff.mpr hv

/-! ## The loading angle -/

/-- The loading angle `δ₀ = α + arcsin((P_ref − c₀)/A)`. -/
def δ0 : ℝ := p.α + Real.arcsin ((p.Pref - p.c0) / p.A)

/-- The model read about its loading angle. -/
def atLoading : Model := ⟨p, p.δ0⟩

/-- The model read about the second equilibrium angle `α + π − arcsin((P_ref − c₀)/A)`. -/
def atAntiLoading : Model := ⟨p, p.α + (Real.pi - Real.arcsin ((p.Pref - p.c0) / p.A))⟩

@[tmio M, powerlib_domain] private theorem atLoading_toVSMLPF :
    (atLoading p).toVSMLPF = VSMLPF.atLoading p.toVSMLPF := by
  simp only [atLoading, Model.toVSMLPF, VSMLPF.atLoading, δ0, VSMLPF.δ0, add_sub_cancel_left]
  rfl

@[tmio M, powerlib_domain] private theorem atAntiLoading_toVSMLPF :
    (atAntiLoading p).toVSMLPF = VSMLPF.atAntiLoading p.toVSMLPF := by
  simp only [atAntiLoading, Model.toVSMLPF, VSMLPF.atAntiLoading, VSMLPF.δ0, add_sub_cancel_left]
  rfl

/-- At the loading angle (`M, D, ω_c, A > 0`, `|P_ref − c₀| < A`) the equilibrium is locally
exponentially stable iff `K < D ω_c + D²/M` (`VSMLPF.locallyExponentiallyStable_iff`). -/
@[tmio TM, powerlib_domain] theorem locallyExponentiallyStable_iff (hM : 0 < p.M) (hD : 0 < p.D)
    (hω : 0 < p.ωc) (hA : 0 < p.A) (h : |p.Pref - p.c0| < p.A) :
    connection% (atLoading p ∈ family.den (.flow .locallyExponentiallyStable) ↔
      atLoading p ∈ {m : Model | m.K < m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M}) := by
  have hv := VSMLPF.locallyExponentiallyStable_iff (g := p.toVSMLPF) ⟨hM, hD, hω, hA⟩ h
  unfold powerlib.TMIO.Statement at hv ⊢
  rw [mem_den_iff, atLoading_toVSMLPF, hv, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    ← atLoading_toVSMLPF, Model.toVSMLPF_K]
  rfl

/-- At the loading angle (`M, D, ω_c, A > 0`, `|P_ref − c₀| < A`) the equilibrium is locally
asymptotically stable iff `K ≤ D ω_c + D²/M`, the Hopf boundary included
(`VSMLPF.locallyAsymptoticallyStable_iff`). -/
@[tmio TM, powerlib_domain] theorem locallyAsymptoticallyStable_iff (hM : 0 < p.M) (hD : 0 < p.D)
    (hω : 0 < p.ωc) (hA : 0 < p.A) (h : |p.Pref - p.c0| < p.A) :
    connection% (atLoading p ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      atLoading p ∈ {m : Model | m.K ≤ m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M}) := by
  have hv := VSMLPF.locallyAsymptoticallyStable_iff (g := p.toVSMLPF) ⟨hM, hD, hω, hA⟩ h
  unfold powerlib.TMIO.Statement at hv ⊢
  rw [mem_den_iff, atLoading_toVSMLPF, hv, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    ← atLoading_toVSMLPF, Model.toVSMLPF_K]
  rfl

/-- The second equilibrium `α + π − arcsin((P_ref − c₀)/A)` is unstable for positive
`M, D, ω_c, A` and `|P_ref − c₀| < A` (`VSMLPF.unstable_atAntiLoading`). -/
@[tmio TM, powerlib_domain] theorem unstable_atAntiLoading (hM : 0 < p.M) (hD : 0 < p.D)
    (hω : 0 < p.ωc) (hA : 0 < p.A) (h : |p.Pref - p.c0| < p.A) :
    connection% (atAntiLoading p ∈ family.den (.flow .unstable)) := by
  have hv := VSMLPF.unstable_atAntiLoading (g := p.toVSMLPF) ⟨hM, hD, hω, hA⟩ h
  unfold powerlib.TMIO.Statement at hv ⊢
  rw [mem_den_iff, atAntiLoading_toVSMLPF]
  exact hv

end VSMLPFLossy
end powerlib.GFM
