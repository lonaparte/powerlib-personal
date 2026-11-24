import theorem.GridTiedConverter.GFM.FullModel.Counterexample

/-! # The 13-state grid-forming converter: the Jacobian in closed form and the explicit `ε*`

Model boundary.
The 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (state order
`(i, v_c, i_g, ξ, ζ, δ, Δω, Q_f)` in dq components, system frame for the plant, controller frame
for the integrators, currents out of the converter positive, export-positive per-unit power),
with Q–V droop `E = E₀ − n_q (Q_f − Q_ref)`. Continuous time, autonomous, no input; free real
parameters. Level: the Jacobian matrix of the field at an arbitrary state, and the explicit bound
`ε*` of the time-scale transfer of `theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean`
written with it; no new behavioural statement.

Source: GFM counterpart study, full-order model note (t5, the fast and slow rows); the blocks of
the Jacobian on a quasi-steady graph, Kokotović–Khalil–O'Reilly, *Singular Perturbation Methods
in Control* (1986), §2.1 and Ch. 2 (the explicit `ε* = 1/(2c + 1)` of the composite Lyapunov
function).

Results.
* `Params.qfRows`, `Params.hasDerivAt_fast_qf`: the `Q_f` derivatives of the five complex fast
  rows, through the droop EMF only (`−n_q K_pc K_pv e^{jδ}/L_f`, `0`, `0`, `−n_q K_pv`, `−n_q`).
* `Params.jacobianClosed`: the closed-form `13 × 13` matrix — fast–fast block `fastBlock δ`,
  fast rows against `(δ, Δω, Q_f)` the real and imaginary parts of `deltaRows`, `0`, `qfRows`,
  slow rows `slowJac` — and `Params.jacobian_eq_jacobianClosed`: it is the Jacobian of the field
  at every state (`LinearAlgebra.hasDerivAt_line_apply` and uniqueness of derivatives).
* `Params.epsStar_eq_closed`: the explicit `ε*` of the time-scale transfer
  (`Params.epsStar`, `FullModel.mem_den_LES_of_lt_epsStar`) is Kokotović's bound
  `SingularPerturbation.graphEpsStar` for the closed-form Jacobian at the quasi-steady state
  `qssState δ* 0 Q*` (itself closed form, `Params.phasors_qssState`), the Lyapunov matrices `P₀`
  of `reducedJacobian δ* Q*` and `P₂` of `fastBlock δ*`.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex Matrix
open powerlib.Dynamics (State)

namespace Params

variable (p : Params)

/-- The `Q_f` derivatives of the five complex fast rows (through the droop EMF only). -/
def qfRows (x : State 13) : Fin 5 → ℂ :=
  ![-(p.nq * p.Kpc * p.Kpv) * ej (x 10) / p.Lf, 0, 0, -(p.nq * p.Kpv), -p.nq]

@[tmio M, powerlib_domain] private theorem shift_12_apply (x : State 13) (t : ℝ) (i : Fin 13) :
    (x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) i = x i + if i = 12 then t else 0 := by
  by_cases h : i = 12
  · subst h; simp
  · simp [h]

/-- The `Q_f` derivative of the fast rows of the 13-state field. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_fast_qf (x : State 13) (a : Fin 5) :
    HasDerivAt (fun t : ℝ => p.fastRows (x + t • EuclideanSpace.single 12 1) a)
      (p.qfRows x a) 0 := by
  have hph : ∀ t : ℝ, convCurrent (x + t • EuclideanSpace.single 12 1) = convCurrent x ∧
      capVoltage (x + t • EuclideanSpace.single 12 1) = capVoltage x ∧
      lineCurrent (x + t • EuclideanSpace.single 12 1) = lineCurrent x ∧
      currentInt (x + t • EuclideanSpace.single 12 1) = currentInt x ∧
      voltageInt (x + t • EuclideanSpace.single 12 1) = voltageInt x := by
    intro t
    simp only [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor,
      shift_12_apply]
    norm_num
  have h10 : ∀ t : ℝ, (x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) 10 = x 10 := by
    intro t; rw [shift_12_apply]; simp
  have hE : ∀ t : ℝ, (p.emf ((x + t • EuclideanSpace.single (12 : Fin 13) (1 : ℝ)) 12) : ℂ) =
      p.emf (x 12) + t * (-p.nq : ℂ) := by
    intro t; rw [shift_12_apply]; simp [emf]; ring
  have hlin : ∀ c d : ℂ, HasDerivAt (fun t : ℝ => c + t * d) d 0 := fun c d => by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const d).const_add c
  fin_cases a
  · simp only [fastRows, Fin.zero_eta, Matrix.cons_val_zero, convRow_eq_ej, (hph _).1,
      (hph _).2.1, (hph _).2.2.1, (hph _).2.2.2.1, (hph _).2.2.2.2, h10, hE, qfRows]
    convert hlin (p.convRow x) (-(p.nq * p.Kpc * p.Kpv) * ej (x 10) / p.Lf) using 1
    funext t
    rw [convRow_eq_ej]
    ring
  · simp only [fastRows, qfRows]
    have : ∀ t : ℝ, p.capRow (x + t • EuclideanSpace.single 12 1) = p.capRow x := fun t => by
      simp only [capRow, (hph t).1, (hph t).2.1, (hph t).2.2.1]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, this]
    exact hasDerivAt_const _ _
  · simp only [fastRows, qfRows]
    have : ∀ t : ℝ, p.lineRow (x + t • EuclideanSpace.single 12 1) = p.lineRow x := fun t => by
      simp only [lineRow, (hph t).2.1, (hph t).2.2.1]
    simp only [Fin.reduceFinMk, Matrix.cons_val, this]
    exact hasDerivAt_const _ _
  · simp only [fastRows, Fin.reduceFinMk, Matrix.cons_val, currentIntRow_eq_ej, (hph _).1,
      (hph _).2.1, (hph _).2.2.1, (hph _).2.2.2.2, h10, hE, qfRows]
    convert hlin (p.currentIntRow x) (-(p.nq * p.Kpv)) using 1
    funext t
    rw [currentIntRow_eq_ej]
    ring
  · simp only [fastRows, Fin.reduceFinMk, Matrix.cons_val, voltageIntRow_eq_ej, (hph _).2.1,
      (hph _).2.2.1, h10, hE, qfRows]
    convert hlin (p.voltageIntRow x) (-p.nq) using 1
    funext t
    rw [voltageIntRow_eq_ej]
    ring

/-- The Jacobian of the 13-state field in closed form, by blocks of `split`: the fast block
`fastBlock δ`, the fast rows against `(δ, Δω, Q_f)` (`deltaRows`, `0`, `qfRows`, real and
imaginary parts), and the slow rows `slowJac`. -/
def jacobianClosed (x : State 13) : Matrix (Fin 13) (Fin 13) ℝ := fun i j =>
  match split i, split j with
  | .inl a, .inl b => p.fastBlock (x 10) a b
  | .inl a, .inr l => component a.2 (![p.deltaRows x a.1, 0, p.qfRows x a.1] l)
  | .inr k, _ => p.slowJac x k j

@[tmio T, powerlib_foundation] private theorem hasDerivAt_component' {f : ℝ → ℂ} {f' : ℂ}
    (hf : HasDerivAt f f' 0) (c : Fin 2) :
    HasDerivAt (fun t => component c (f t)) (component c f') 0 := by
  fin_cases c
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hf
  · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hf

/-- **The Jacobian in closed form**: at every state, the Jacobian matrix of the 13-state field is
`jacobianClosed`. -/
@[tmio M, powerlib_domain] theorem jacobian_eq_jacobianClosed (x : State 13) :
    p.jacobian x = p.jacobianClosed x := by
  ext i j
  have hJ := LinearAlgebra.hasDerivAt_line_apply (p.hasFDerivAt_jacobian x) i j
  refine hJ.unique ?_
  obtain ⟨i', rfl⟩ := split.symm.surjective i
  obtain ⟨j', rfl⟩ := split.symm.surjective j
  rcases i' with ⟨a, c'⟩ | k
  · rcases j' with b | l
    · simp only [jacobianClosed, Equiv.apply_symm_apply]
      simpa using p.hasDerivAt_fast x (a, c') b
    · simp only [jacobianClosed, Equiv.apply_symm_apply]
      simp only [p.field_split_inl]
      refine hasDerivAt_component' ?_ c'
      fin_cases l
      · simpa [split_symm_inr] using p.hasDerivAt_fast_delta x a
      · have h : ∀ t : ℝ, p.fastRows (x + t • EuclideanSpace.single 11 1) a = p.fastRows x a :=
          fun t => congrFun (p.fastRows_shift_eq x t (j := 11) (Or.inl rfl)) a
        have hs : split.symm (.inr (1 : Fin 3)) = (11 : Fin 13) := by rw [split_symm_inr]; rfl
        show HasDerivAt (fun t => p.fastRows (x + t • EuclideanSpace.single
          (split.symm (Sum.inr 1)) 1) a) (![p.deltaRows x a, 0, p.qfRows x a] 1) 0
        rw [hs]
        simp only [h, Matrix.cons_val_one, Matrix.cons_val_zero]
        exact hasDerivAt_const _ _
      · simpa [split_symm_inr] using p.hasDerivAt_fast_qf x a
  · simp only [jacobianClosed, Equiv.apply_symm_apply]
    exact p.hasDerivAt_slow x k _

/-- **The explicit `ε*` in closed form.** The bound `Params.epsStar δ* Q* P₀ P₂` of the
time-scale transfer is `SingularPerturbation.graphEpsStar` for the closed-form Jacobian
`jacobianClosed` at the quasi-steady state `qssState δ* 0 Q*`. -/
@[tmio M, powerlib_domain] theorem epsStar_eq_closed (δ Qf : ℝ) (P0 : Matrix (Fin 3) (Fin 3) ℝ)
    (P2 : Matrix (Fin 5 × Fin 2) (Fin 5 × Fin 2) ℝ) :
    p.epsStar δ Qf P0 P2 =
      SingularPerturbation.graphEpsStar split (p.jacobianClosed (p.qssState δ 0 Qf)) P0 P2 := by
  rw [epsStar, jacobian_eq_jacobianClosed]

end Params

end powerlib.GFM.FullModel
