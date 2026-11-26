import theorem.GridTiedConverter.GFM.QVDroopBT
import theorem.GridTiedConverter.GFM.QVDroopHopf

/-! # Grid-forming converter with Q–V droop: complete membership in the physical range

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroop.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P(δ, E) − D Δω`, `Q̇_f = ω_q (Q(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, line `Z = R + jX` to a stiff grid `V ∠ 0`, export-positive powers,
  continuous time, autonomous. Read about a selected point (`QVDroop.Model`) on
  `QVDroop.family`. Excluded as there.
* The physical range: `M, D, ω_q, n_q, X, V > 0`, `E₀ + n_q Q_ref > 0` and a positive EMF
  `E* > 0` at the selected point. There `K > 0` at every equilibrium, so `A = D + M ω_q K > 0`:
  no zero–Hopf point (`A = 0`) and no cusp point (`𝔉 > 0`) occurs; the fold points (`C = 0`) are
  saddle-nodes, strict Routh violations or Bogdanov–Takens points, all unstable. Excluded, not
  decided: the Bautin set (Hopf points `A, C > 0`, `G = 0` with `hopfNum = 0`).
* Level: local asymptotic and Lyapunov stability (LeanForControl's `LocalAsymptoticStable`,
  `LyapunovStable`) through `QVDroop.family`.

Source: the complete membership `QVDroop.mem_den_locallyAsymptoticallyStable_iff_complete`,
`QVDroop.mem_den_lyapunovStable_iff_complete` (`theorem/GridTiedConverter/GFM/QVDroopHopf.lean`,
off the cusp, double-zero and Bautin sets), the physical-range facts
`QVDroop.Model.gain_pos_of_physical`, `QVDroop.Qδ_ne_zero_of_fold`,
`QVDroop.foldQuad_pos_of_physical` (`theorem/GridTiedConverter/GFM/QVDroopCusp.lean`) and the
Bogdanov–Takens law `QVDroop.mem_den_unstable_of_bt_of_physical`
(`theorem/GridTiedConverter/GFM/QVDroopBT.lean`).

Results.
The two membership theorems below; no new definition.

Family and connection conclusions.
No new family: connection conclusions on `QVDroop.family`.
* **`QVDroop.mem_den_locallyAsymptoticallyStable_iff_of_physical_complete`**,
  **`QVDroop.mem_den_lyapunovStable_iff_of_physical_complete`**: in the physical range, off the
  Bautin set, the model is locally asymptotically stable, equivalently Lyapunov stable, iff the
  point is an equilibrium with `A, C, G > 0` or a Hopf point with `hopfNum < 0`.
-/

noncomputable section
namespace powerlib.GFM.QVDroop

/-- In the physical range, at an equilibrium the cusp hypothesis holds (`K > 0`, `𝔉 > 0` at a
fold) and the double-zero points `C = G = 0` are unstable (Bogdanov–Takens, `A > 0`). -/
@[tmio TM, powerlib_domain] private theorem physical_cases (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X) (hV : 0 < m.q.V)
    (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (hE : 0 < m.q.emf m.Qf)
    (heq : m.q.field m.point = 0) :
    (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      foldQuad (m.q.Pδ m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) ≠ 0) ∧
    (m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.routhHopf m.δ (m.q.emf m.Qf) = 0 →
      m ∈ family.den (.flow .unstable)) := by
  have hk := m.gain_pos_of_physical hM hω hnq hX hlev heq hE
  have hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) := by unfold routhTrace; positivity
  refine ⟨fun hC => ⟨hk.ne', ?_⟩, fun hC hG => ?_⟩
  · exact (m.q.foldQuad_pos_of_physical hX hnq hE hk (m.q.Qδ_ne_zero_of_fold
      (m.q.zsq_pos hX.ne').ne' (mul_ne_zero hE.ne' hV.ne') hk.ne' hC)).ne'
  · have hGe := m.q.routhHopf_eq m.δ (m.q.emf m.Qf)
    rw [hC, mul_zero, sub_zero, hG] at hGe
    have hBT : m.q.Pδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) = 0 :=
      (mul_eq_zero.mp hGe.symm).resolve_left hA.ne'
    have hu := mem_den_unstable_of_bt_of_physical m hM hω hnq hX hV hlev heq hE hC hBT hA
    unfold powerlib.TMIO.Statement at hu
    exact hu

@[tmio TM, powerlib_domain] private theorem eq_of_lyapunovStable {m : Model}
    (hl : m ∈ family.den (.flow .lyapunovStable)) : m.q.field m.point = 0 :=
  Dynamics.isEquilibrium_of_lyapunovStable m.q.contDiff_field
    ((Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field) (pt := Model.point)
      family_isAutonomous).mp hl)

/-- **Complete Lyapunov membership in the physical range.** For `M, D, ω_q, n_q, X, V > 0`,
`E₀ + n_q Q_ref > 0` and `E* > 0`, off the Bautin set (`IsHopf → hopfNum ≠ 0`), the model is
Lyapunov stable iff the point is an equilibrium with `A, C, G > 0` or a Hopf point with
`hopfNum < 0` (`QVDroop.mem_den_lyapunovStable_iff_complete`; the cusp set is empty and the
double-zero points are unstable in this range). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_physical_complete (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hV : 0 < m.q.V) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref) (hE : 0 < m.q.emf m.Qf)
    (hbautin : m.IsHopf → m.hopfNumAt ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | (m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.IsHopf ∧ m.hopfNumAt < 0)}) := by
  by_cases heq : m.q.field m.point = 0
  · obtain ⟨hcusp, hbt⟩ := physical_cases m hM hD hω hnq hX hV hlev hE heq
    by_cases hCG : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧ m.q.routhHopf m.δ (m.q.emf m.Qf) = 0
    · have hu := hbt hCG.1 hCG.2
      have hl := Spectral.not_mem_den_lyapunovStable_of_unstable hu
      unfold powerlib.TMIO.Statement at hl ⊢
      refine ⟨fun h => absurd h hl, ?_⟩
      rintro (⟨-, -, hC, -⟩ | ⟨⟨-, -, hC, -⟩, -⟩) <;> exact absurd hCG.1 hC.ne'
    · exact mem_den_lyapunovStable_iff_complete m hM hD hω hE.ne' hcusp
        (fun hC hG => hCG ⟨hC, hG⟩) hbautin
  · unfold powerlib.TMIO.Statement
    refine ⟨fun h => absurd (eq_of_lyapunovStable h) heq, ?_⟩
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> exact absurd h heq

/-- **Complete local asymptotic membership in the physical range.** Under the hypotheses of
`QVDroop.mem_den_lyapunovStable_iff_of_physical_complete` the model is locally asymptotically
stable iff the point is an equilibrium with `A, C, G > 0` or a Hopf point with `hopfNum < 0`
(`QVDroop.mem_den_locallyAsymptoticallyStable_iff_complete`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_physical_complete
    (m : Model) (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq)
    (hX : 0 < m.q.X) (hV : 0 < m.q.V) (hlev : 0 < m.q.E0 + m.q.nq * m.q.Qref)
    (hE : 0 < m.q.emf m.Qf) (hbautin : m.IsHopf → m.hopfNumAt ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | (m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)) ∨
        (m.IsHopf ∧ m.hopfNumAt < 0)}) := by
  have hs := Spectral.den_las_subset_lyapunovStable (F := family)
  unfold powerlib.TMIO.Statement at hs
  by_cases heq : m.q.field m.point = 0
  · obtain ⟨hcusp, hbt⟩ := physical_cases m hM hD hω hnq hX hV hlev hE heq
    by_cases hCG : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 ∧ m.q.routhHopf m.δ (m.q.emf m.Qf) = 0
    · have hu := hbt hCG.1 hCG.2
      have hl := Spectral.not_mem_den_lyapunovStable_of_unstable hu
      unfold powerlib.TMIO.Statement at hl ⊢
      refine ⟨fun h => absurd (hs h) hl, ?_⟩
      rintro (⟨-, -, hC, -⟩ | ⟨⟨-, -, hC, -⟩, -⟩) <;> exact absurd hCG.1 hC.ne'
    · exact mem_den_locallyAsymptoticallyStable_iff_complete m hM hD hω hE.ne' hcusp
        (fun hC hG => hCG ⟨hC, hG⟩) hbautin
  · unfold powerlib.TMIO.Statement
    refine ⟨fun h => absurd (eq_of_lyapunovStable (hs h)) heq, ?_⟩
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> exact absurd h heq

end powerlib.GFM.QVDroop
