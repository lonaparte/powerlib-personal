import powerlib

open powerlib Matrix
open scoped Topology

noncomputable section

namespace StateSpacePassivityCases

@[powerlib_domain] theorem arbitrary_dimensions_passive {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : StateSpacePassivity.Model ι κ) (c : StateSpacePassivity.Certificate m) :
    Passivity.PassiveWithStorage (StateSpacePassivity.system m)
      (StateSpacePassivity.energy c.P) := by aesop

@[powerlib_domain] theorem arbitrary_dimensions_stable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty ι] (m : StateSpacePassivity.Model ι κ)
    (c : StateSpacePassivity.Certificate m) :
    Passivity.LyapunovStable (StateSpacePassivity.system m) := by aesop

@[powerlib_domain] theorem arbitrary_dimensions_equilibrium_stable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty ι] (m : StateSpacePassivity.Model ι κ)
    (c : StateSpacePassivity.Certificate m) (u : κ → ℝ) (e : ι → ℝ)
    (he : StateSpacePassivity.IsEquilibrium m u e) :
    StateSpacePassivity.LyapunovStableAt m u e := by aesop

@[powerlib_domain] theorem arbitrary_dimensions_matrix_certificate_passive {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : StateSpacePassivity.Model ι κ)
    (c : StateSpacePassivity.MatrixCertificate m) :
    Passivity.PassiveWithStorage (StateSpacePassivity.system m)
      (StateSpacePassivity.energy c.P) := by
  let gc := c.toCertificate
  have hp : Passivity.PassiveWithStorage (StateSpacePassivity.system m)
      (StateSpacePassivity.energy gc.P) := by aesop
  exact hp

@[powerlib_domain] theorem arbitrary_dimensions_matrix_certificate_stable {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [Nonempty ι] (m : StateSpacePassivity.Model ι κ)
    (c : StateSpacePassivity.MatrixCertificate m) :
    Passivity.LyapunovStable (StateSpacePassivity.system m) := by
  let gc := c.toCertificate
  aesop

@[powerlib_domain] theorem arbitrary_dimensions_integral {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : StateSpacePassivity.Model ι κ) (c : StateSpacePassivity.Certificate m)
    {u : ℝ → (κ → ℝ)} {x : ℝ → (ι → ℝ)}
    (hx : Passivity.IsTrajectory (StateSpacePassivity.system m) u x)
    {t : ℝ} (ht : 0 ≤ t)
    (hpower : IntervalIntegrable
      (fun τ => Passivity.supply (StateSpacePassivity.system m) (x τ) (u τ))
      MeasureTheory.volume 0 t) :
    StateSpacePassivity.energy c.P (x t) - StateSpacePassivity.energy c.P (x 0) ≤
      ∫ τ in (0 : ℝ)..t, Passivity.supply (StateSpacePassivity.system m) (x τ) (u τ) := by
  aesop

@[powerlib_domain] theorem arbitrary_dimensions_forward_solution {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : StateSpacePassivity.Model ι κ) (initial : ι → ℝ) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0) x ∧
      x 0 = initial := by aesop

@[powerlib_domain] theorem arbitrary_input_uniqueness {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : StateSpacePassivity.Model ι κ) {u : ℝ → (κ → ℝ)}
    {x y : ℝ → (ι → ℝ)}
    (hx : Passivity.IsTrajectory (StateSpacePassivity.system m) u x)
    (hy : Passivity.IsTrajectory (StateSpacePassivity.system m) u y)
    (h0 : x 0 = y 0) : Set.EqOn x y (Set.Ici 0) := by aesop


@[powerlib_domain] theorem constructed_response_contract {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : StateSpacePassivity.Model ι κ) (initial : ι → ℝ) (t : ℝ) :
    HasDerivAt (StateSpacePassivity.response m initial)
      (StateSpacePassivity.operator m (StateSpacePassivity.response m initial t)) t ∧
      Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0)
        (StateSpacePassivity.response m initial) ∧
      StateSpacePassivity.response m initial 0 = initial := by aesop

@[powerlib_domain] theorem constructed_equilibrium_response_contract {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : StateSpacePassivity.Model ι κ)
    (u : κ → ℝ) (e initial : ι → ℝ) (he : StateSpacePassivity.IsEquilibrium m u e) :
    Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => u)
      (StateSpacePassivity.equilibriumResponse m e initial) ∧
      StateSpacePassivity.equilibriumResponse m e initial 0 = initial := by aesop

@[powerlib_domain] theorem supplied_equilibrium_forward_solution {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : StateSpacePassivity.Model ι κ)
    (u : κ → ℝ) (e initial : ι → ℝ) (he : StateSpacePassivity.IsEquilibrium m u e) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => u) x ∧
      x 0 = initial := by aesop

@[powerlib_domain] theorem constructed_unique_forward_solution {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : StateSpacePassivity.Model ι κ) (initial : ι → ℝ) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0) x ∧
      x 0 = initial ∧ ∀ y,
        Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0) y →
        y 0 = initial → Set.EqOn y x (Set.Ici 0) := by aesop

@[powerlib_domain] theorem supplied_quadratic_storage_passive {E κ : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Passivity.System E κ)
    (V : Passivity.QuadraticStorage s) : Passivity.PassiveWithStorage s V.energy := by aesop

@[powerlib_domain] theorem supplied_quadratic_storage_stable {E κ : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (s : Passivity.System E κ) (V : Passivity.QuadraticStorage s)
    (he : Passivity.IsEquilibrium s 0) : Passivity.LyapunovStable s := by aesop

@[powerlib_foundation] theorem supplied_positive_storage {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.PosDef) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < StateSpacePassivity.energy P x := by aesop

def fullStorage : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

def feedthroughModel : StateSpacePassivity.Model (Fin 2) (Fin 1) where
  A := !![-1, 0; 0, -1]
  B := !![1; 0]
  C := !![0, 0]
  D := !![1]

@[powerlib_foundation] theorem fullStorage_quadratic_positive (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    0 < dotProduct x (fullStorage.mulVec x) := by
  simp only [dotProduct, mulVec, fullStorage, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext i
    fin_cases i <;> simp_all
  rcases hn with h0 | h1
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 0 + x 1)]
  · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0 + x 1)]

@[powerlib_foundation] theorem fullStorage_posDef : fullStorage.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.IsHermitian, Matrix.conjTranspose,
      fullStorage]
  · intro x hx
    simpa only [star_trivial] using fullStorage_quadratic_positive x hx

@[powerlib_foundation] theorem feedthrough_full_kyp (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    dotProduct (fullStorage.mulVec x) (StateSpacePassivity.field feedthroughModel x u) ≤
      Passivity.supply (StateSpacePassivity.system feedthroughModel) x u := by
  simp [StateSpacePassivity.field, StateSpacePassivity.system, StateSpacePassivity.output,
    Passivity.supply, dotProduct, mulVec, fullStorage, feedthroughModel,
    Fin.sum_univ_two]
  nlinarith [sq_nonneg (u 0 - x 0 - x 1 / 2),
    sq_nonneg (x 0 + x 1 / 2), sq_nonneg (x 1)]

def feedthroughCertificate : StateSpacePassivity.Certificate feedthroughModel where
  P := fullStorage
  positive := fullStorage_posDef
  kyp := feedthrough_full_kyp

@[powerlib_foundation] theorem storage_has_off_diagonal_entry : fullStorage 0 1 ≠ 0 := by
  norm_num [fullStorage]

@[powerlib_foundation] theorem model_has_feedthrough : feedthroughModel.D ≠ 0 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) h
  norm_num [feedthroughModel] at he

@[powerlib_foundation] theorem model_is_not_collocated : fullStorage * feedthroughModel.B ≠
    feedthroughModel.C.transpose := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 1) ℝ => M 0 0) h
  norm_num [fullStorage, feedthroughModel, Matrix.mul_apply, Fin.sum_univ_two] at he

@[powerlib_domain] theorem full_kyp_passive :
    Passivity.PassiveWithStorage (StateSpacePassivity.system feedthroughModel)
      (StateSpacePassivity.energy feedthroughCertificate.P) := by
  let c := feedthroughCertificate
  aesop

@[powerlib_domain] theorem full_kyp_stable :
    Passivity.LyapunovStable (StateSpacePassivity.system feedthroughModel) := by
  let c := feedthroughCertificate
  aesop

@[powerlib_domain] theorem full_kyp_forward_solution (initial : Fin 2 → ℝ) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system feedthroughModel)
      (fun _ => 0) x ∧ x 0 = initial := by
  let submittedModel := feedthroughModel
  aesop


-- The same dimensions do not identify the submitted model.
def mismatchedModel : StateSpacePassivity.Model (Fin 2) (Fin 1) :=
  { feedthroughModel with D := !![-1] }

@[powerlib_foundation] theorem mismatched_model_certificate_is_rejected : True := by
  fail_if_success
    have forged : StateSpacePassivity.Certificate mismatchedModel := feedthroughCertificate
  trivial

@[powerlib_domain] theorem negative_feedthrough_has_no_certificate :
    ¬ Nonempty (StateSpacePassivity.Certificate mismatchedModel) := by
  rintro ⟨c⟩
  have hkyp := c.kyp 0 ![1]
  norm_num [StateSpacePassivity.field, StateSpacePassivity.system,
    StateSpacePassivity.output, Passivity.supply, mismatchedModel, feedthroughModel,
    dotProduct, mulVec, Fin.sum_univ_one, Fin.sum_univ_two] at hkyp

def reversedPortModel : StateSpacePassivity.Model (Fin 1) (Fin 1) where
  A := !![0]
  B := !![1]
  C := !![-1]
  D := !![0]

@[powerlib_domain] theorem reversed_port_has_no_positive_kyp_certificate :
    ¬ Nonempty (StateSpacePassivity.Certificate reversedPortModel) := by
  rintro ⟨c⟩
  have hnonzero : (![1] : Fin 1 → ℝ) ≠ 0 := by
    intro h
    have he := congrArg (fun x : Fin 1 → ℝ => x 0) h
    norm_num at he
  have hpositive := c.positive.dotProduct_mulVec_pos hnonzero
  have hkyp := c.kyp ![1] ![1]
  simp [star_trivial, dotProduct, mulVec] at hpositive
  simp [StateSpacePassivity.field, StateSpacePassivity.system, StateSpacePassivity.output,
    Passivity.supply, reversedPortModel, dotProduct, mulVec] at hkyp
  linarith

def indefiniteStorage : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

@[powerlib_foundation] theorem indefinite_storage_is_rejected : ¬ indefiniteStorage.PosDef := by
  intro hp
  have hnonzero : (![0, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have he := congrArg (fun x : Fin 2 → ℝ => x 1) h
    norm_num at he
  have hpositive := hp.dotProduct_mulVec_pos hnonzero
  norm_num [star_trivial, indefiniteStorage, dotProduct, mulVec, Fin.sum_univ_two] at hpositive

end StateSpacePassivityCases

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants do
    if name.getRoot == `StateSpacePassivityCases && info.isTheorem then
      for axiomName in powerlib.Search.declarationAxioms env name do
        unless powerlib.Search.allowedAxiom axiomName do
          throwError "Unexpected generic state-space consumer axiom: {name}: {axiomName}"
  for (consumer, source) in #[
      (`StateSpacePassivityCases.arbitrary_dimensions_passive,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`StateSpacePassivityCases.arbitrary_dimensions_stable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable),
      (`StateSpacePassivityCases.arbitrary_dimensions_integral,
        `powerlib.StateSpacePassivity.Certificate.integral_passivity),
      (`StateSpacePassivityCases.arbitrary_input_uniqueness,
        `powerlib.StateSpacePassivity.trajectory_unique),
      (`StateSpacePassivityCases.full_kyp_passive,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`StateSpacePassivityCases.full_kyp_stable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable),
      (`powerlib.StateSpacePassivity.MatrixCertificate.passiveWithStorage,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`powerlib.StateSpacePassivity.MatrixCertificate.lyapunovStable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable)] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing generic consumer proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Native consumer did not use the general state-space theorem {source}"
  for (consumer, sources) in #[
      (`StateSpacePassivityCases.arbitrary_dimensions_forward_solution,
        #[`powerlib.StateSpacePassivity.trajectory_exists,
          `powerlib.StateSpacePassivity.trajectory_exists_unique]),
      (`StateSpacePassivityCases.arbitrary_dimensions_equilibrium_stable,
        #[`powerlib.StateSpacePassivity.Certificate.lyapunovStableAt,
          `powerlib.StateSpacePassivity.Certificate.lyapunovStable]),
      (`StateSpacePassivityCases.arbitrary_dimensions_matrix_certificate_passive,
        #[`powerlib.StateSpacePassivity.Certificate.passiveWithStorage,
          `powerlib.StateSpacePassivity.MatrixCertificate.passiveWithStorage]),
      (`StateSpacePassivityCases.arbitrary_dimensions_matrix_certificate_stable,
        #[`powerlib.StateSpacePassivity.Certificate.lyapunovStable,
          `powerlib.StateSpacePassivity.MatrixCertificate.lyapunovStable])] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing generic matrix consumer proof: {consumer}"
    unless sources.any proof.getUsedConstants.contains do
      throwError "Matrix consumer did not use a general state-space semantic theorem: {consumer}"
  logInfo "POWERLIB_STATE_SPACE_PASSIVITY_CASES_OK"
