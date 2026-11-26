import theorem.GridTiedConverter.GFM.QVDroopVirtualBT
import theorem.GridTiedConverter.GFM.QVDroopVirtualHopf

/-! # Q–V droop with a virtual impedance: complete membership in the physical range

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P_t(δ, E) − D Δω`, `Q̇_f = ω_q (Q_t(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, the powers measured at the converter terminal behind the virtual
  impedance `Z_v = R_v + jX_v`, the grid branch `Z_g = R_g + jX_g` to a stiff grid `V ∠ 0`,
  export-positive, continuous time, autonomous. Read about a selected point
  (`QVDroopVirtual.Model`) on `QVDroopVirtual.family`. Excluded as there.
* The physical range with damping: `M, D, ω_q, n_q, X_g > 0`, an inductive or zero virtual
  reactance `X_v ≥ 0`, `E₀ + n_q Q_ref > 0` and a positive EMF `E* > 0` at the selected point;
  `R_g`, `R_v` are arbitrary. There `K_t > 0` at every equilibrium, so `A = D + M ω_q K_t > 0`:
  no zero–Hopf point; every fold point (`C = 0`) is a saddle-node, a strict Routh violation or a
  Bogdanov–Takens point, unstable, except the folds with `Q_tδ = 0` (possible only for
  `|Z_v| = |Z_g|`) where `n_q (∂P_t/∂E) ∂²Q_t/∂δ² = K_t ∂²P_t/∂δ²` (the fold coefficient
  vanishes). Excluded, not decided: those degenerate folds and the Bautin set (Hopf points
  `A, C > 0`, `G = 0` with `hopfNum = 0`).
* Level: Lyapunov instability, local asymptotic and Lyapunov stability (LeanForControl's
  `Unstable`, `LocalAsymptoticStable`, `LyapunovStable`) through `QVDroopVirtual.family`.

Source: the complete membership `QVDroopVirtual.mem_den_locallyAsymptoticallyStable_iff_complete`,
`QVDroopVirtual.mem_den_lyapunovStable_iff_complete`
(`theorem/GridTiedConverter/GFM/QVDroopVirtualHopf.lean`, off the cusp, double-zero and Bautin
sets), the physical-range facts `QVDroopVirtual.Model.gain_pos_of_physical`,
`QVDroopVirtual.foldQuad_ne_zero_of_physical` and the fold law at `Q_tδ = 0`
`QVDroopVirtual.mem_den_unstable_of_fold_of_Qtδ_eq_zero`
(`theorem/GridTiedConverter/GFM/QVDroopVirtualCusp.lean`), and the fold and Bogdanov–Takens law
`QVDroopVirtual.mem_den_unstable_of_fold_of_trace_ne`
(`theorem/GridTiedConverter/GFM/QVDroopVirtualBT.lean`); the counterpart without virtual
impedance is `theorem/GridTiedConverter/GFM/QVDroopMembership.lean`.

Results.
The three theorems below; no new definition.

Family and connection conclusions.
No new family: connection conclusions on `QVDroopVirtual.family`.
* **`QVDroopVirtual.mem_den_unstable_of_fold_of_physical_of_damping`**: in the physical range
  every fold equilibrium (`C = 0`) is unstable, unless `Q_tδ = 0` and
  `n_q (∂P_t/∂E) ∂²Q_t/∂δ² = K_t ∂²P_t/∂δ²`.
* **`QVDroopVirtual.mem_den_locallyAsymptoticallyStable_iff_of_physical_complete`**,
  **`QVDroopVirtual.mem_den_lyapunovStable_iff_of_physical_complete`**: in the physical range,
  off the degenerate folds with `Q_tδ = 0` and off the Bautin set, the model is locally
  asymptotically stable, equivalently Lyapunov stable, iff the point is an equilibrium with
  `A, C, G > 0` or a Hopf point with `hopfNum < 0`. For `|Z_v| ≠ |Z_g|` the fold hypothesis is
  void (`QVDroopVirtual.Qtδ_ne_zero_of_fold`).
-/

noncomputable section
namespace powerlib.GFM.QVDroopVirtual

/-- **Every physical fold equilibrium is unstable** (with damping). For `M, D, ω_q, n_q, X_g > 0`,
`X_v ≥ 0`, `E₀ + n_q Q_ref > 0`, an equilibrium with `E* > 0` at a fold (`C = 0`) is unstable,
unless `Q_tδ = 0` and `n_q (∂P_t/∂E) ∂²Q_t/∂δ² = K_t ∂²P_t/∂δ²`: `K_t > 0`, so `A > 0`; for
`Q_tδ ≠ 0`, `𝔉 ≠ 0` (`QVDroopVirtual.foldQuad_ne_zero_of_physical`) and
`QVDroopVirtual.mem_den_unstable_of_fold_of_trace_ne` applies (a violation, a saddle-node or a
Bogdanov–Takens point); for `Q_tδ = 0`, `P_tδ = 0`, `P_tδ + D ω_q K_t > 0` and the fold law
`QVDroopVirtual.mem_den_unstable_of_fold_of_Qtδ_eq_zero` applies. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_physical_of_damping (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hXg : 0 < m.q.Xg)
    (hXv : 0 ≤ m.q.Xv) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (heq : m.q.field m.point = 0)
    (hE : 0 < m.q.emf m.Qf) (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hdeg : m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 →
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδδ m.δ (m.q.emf m.Qf) ≠
        m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hk := m.gain_pos_of_physical hM.ne' hω.ne' hnq hXg hXv hlev heq hE
  have hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) := by unfold routhTrace; positivity
  by_cases hc : m.q.Qtδ m.δ (m.q.emf m.Qf) = 0
  · have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
        m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
    rw [hc, mul_zero, sub_zero] at h0
    have ha0 := (mul_eq_zero.mp h0).resolve_left hk.ne'
    have ha1 : 0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) := by
      rw [ha0, zero_add]; positivity
    exact mem_den_unstable_of_fold_of_Qtδ_eq_zero m hM hω heq hC hc hA ha1 hk.ne' hE.ne' (hdeg hc)
  · exact mem_den_unstable_of_fold_of_trace_ne m hM hω heq hC hA.ne' hk.ne' hE.ne'
      (m.q.foldQuad_ne_zero_of_physical hXg hXv hnq hE hC hc)

@[tmio TM, powerlib_domain] private theorem eq_of_lyapunovStable {m : Model}
    (hl : m ∈ family.den (.flow .lyapunovStable)) : m.q.field m.point = 0 :=
  Dynamics.isEquilibrium_of_lyapunovStable m.q.contDiff_field
    ((Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field) (pt := Model.point)
      family_isAutonomous).mp hl)

/-- **Complete Lyapunov membership in the physical range.** For `M, D, ω_q, n_q, X_g > 0`,
`X_v ≥ 0`, `E₀ + n_q Q_ref > 0` and `E* > 0`, off the degenerate folds (`C = 0`, `Q_tδ = 0`,
`n_q (∂P_t/∂E) ∂²Q_t/∂δ² = K_t ∂²P_t/∂δ²`) and off the Bautin set (`IsHopf → hopfNum ≠ 0`), the
model is Lyapunov stable iff the point is an equilibrium with `A, C, G > 0` or a Hopf point with
`hopfNum < 0` (`QVDroopVirtual.mem_den_lyapunovStable_iff_complete` off the fold; every fold
equilibrium is unstable, `QVDroopVirtual.mem_den_unstable_of_fold_of_physical_of_damping`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_physical_complete (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hXg : 0 < m.q.Xg)
    (hXv : 0 ≤ m.q.Xv) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (hE : 0 < m.q.emf m.Qf)
    (hdeg : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 →
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδδ m.δ (m.q.emf m.Qf) ≠
        m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf))
    (hbautin : m.IsHopf → m.hopfNumAt ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | (m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.IsHopf ∧ m.hopfNumAt < 0)}) := by
  by_cases heq : m.q.field m.point = 0
  · by_cases hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0
    · have hu := mem_den_unstable_of_fold_of_physical_of_damping m hM hD hω hnq hXg hXv hlev heq
        hE hC (hdeg hC)
      have hl := Spectral.not_mem_den_lyapunovStable_of_unstable hu
      unfold powerlib.TMIO.Statement at hl ⊢
      refine ⟨fun h => absurd h hl, ?_⟩
      rintro (⟨-, -, hC', -⟩ | ⟨⟨-, -, hC', -⟩, -⟩) <;> exact absurd hC hC'.ne'
    · exact mem_den_lyapunovStable_iff_complete m hM hD hω hE.ne' (fun h => absurd h hC)
        (fun h => absurd h hC) hbautin
  · unfold powerlib.TMIO.Statement
    refine ⟨fun h => absurd (eq_of_lyapunovStable h) heq, ?_⟩
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> exact absurd h heq

/-- **Complete local asymptotic membership in the physical range.** Under the hypotheses of
`QVDroopVirtual.mem_den_lyapunovStable_iff_of_physical_complete` the model is locally
asymptotically stable iff the point is an equilibrium with `A, C, G > 0` or a Hopf point with
`hopfNum < 0` (`QVDroopVirtual.mem_den_locallyAsymptoticallyStable_iff_complete` off the fold). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_physical_complete
    (m : Model) (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq)
    (hXg : 0 < m.q.Xg) (hXv : 0 ≤ m.q.Xv) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref)
    (hE : 0 < m.q.emf m.Qf)
    (hdeg : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 →
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδδ m.δ (m.q.emf m.Qf) ≠
        m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδδ m.δ (m.q.emf m.Qf))
    (hbautin : m.IsHopf → m.hopfNumAt ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | (m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.IsHopf ∧ m.hopfNumAt < 0)}) := by
  have hs := Spectral.den_las_subset_lyapunovStable (F := family)
  unfold powerlib.TMIO.Statement at hs
  by_cases heq : m.q.field m.point = 0
  · by_cases hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0
    · have hu := mem_den_unstable_of_fold_of_physical_of_damping m hM hD hω hnq hXg hXv hlev heq
        hE hC (hdeg hC)
      have hl := Spectral.not_mem_den_lyapunovStable_of_unstable hu
      unfold powerlib.TMIO.Statement at hl ⊢
      refine ⟨fun h => absurd (hs h) hl, ?_⟩
      rintro (⟨-, -, hC', -⟩ | ⟨⟨-, -, hC', -⟩, -⟩) <;> exact absurd hC hC'.ne'
    · exact mem_den_locallyAsymptoticallyStable_iff_complete m hM hD hω hE.ne'
        (fun h => absurd h hC) (fun h => absurd h hC) hbautin
  · unfold powerlib.TMIO.Statement
    refine ⟨fun h => absurd (eq_of_lyapunovStable (hs h)) heq, ?_⟩
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> exact absurd h heq

end QVDroopVirtual

end powerlib.GFM
