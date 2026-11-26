import theorem.GridTiedConverter.GFM.LinePSCZeroHopf

/-! # Power synchronization on a dynamic R–L line: membership with the fold decided

Domain module.

Model boundary.
* The three-state power-synchronization law `Line.PSC` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, i_d, i_q) : State 3`,
  grid dq frame at `ω₀`, export-positive power, constant `E`, `δ̇ = K_p (P_ref − P_e)`,
  `L i̇ = E e^{jδ} − V − (R + jX) i`; no damping loop, voltage loop, inner loops, PLL, delay or
  PWM. Read about a selected angle (`Line.PSC.Model`), translated so that the operating point is
  the origin; every physical model, every angle, balanced or not.
* The undecided set (`Line.PSC.Model.Undecided`): the balanced triple-zero points (`K = 0`,
  `a₁ = a₂ = 0`: the Bogdanov–Takens gain `K_p D_line = 1` with `X² = 3R²`, codimension three)
  and the Bautin-type points of the Hopf boundary (`𝔅_P = 0`). Every other fold point is decided:
  the saddle-node, the Bogdanov–Takens cusp and the zero–Hopf points are unstable.
* Level: local asymptotic and Lyapunov stability, instability (LeanForControl's
  `LocalAsymptoticStable`, `LyapunovStable`, `Unstable`) through `Line.PSC.family`.

Source: the membership off the degenerate set `Line.PSC.mem_den_locallyAsymptoticallyStable_iff`,
`Line.PSC.mem_den_lyapunovStable_iff` and the fold law
`Line.PSC.mem_den_unstable_of_fold_of_coeff2_ne` (`theorem/GridTiedConverter/GFM/HopfLinePSC.lean`,
the saddle-node and the Bogdanov–Takens cusp), the zero–Hopf law
`Line.PSC.mem_den_unstable_of_zeroHopf` (`theorem/GridTiedConverter/GFM/LinePSCZeroHopf.lean`);
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.2, §8.4, §8.5. One Bautin-type
point is decided by its second Lyapunov coefficient in
`theorem/GridTiedConverter/GFM/HopfBautinPSC.lean` (`Line.PSC.unitLine_bautin_mem_den_unstable`).

Results.
* `Line.PSC.Model.Undecided`: the triple-zero points and the Bautin-type points.

Family and connection conclusions.
No new family: connection conclusions on `Line.PSC.family`.
* **`Line.PSC.mem_den_unstable_of_fold_of_ne_tripleZero`** (the fold decided): a balanced
  physical model at `K = 0` other than a triple zero (`a₁ = a₂ = 0`) is unstable.
* **`Line.PSC.mem_den_locallyAsymptoticallyStable_iff_of_not_undecided`**,
  **`Line.PSC.mem_den_lyapunovStable_iff_of_not_undecided`**: off `Line.PSC.Model.Undecided` a
  physical model is locally asymptotically stable, equivalently Lyapunov stable, iff it is
  balanced and either meets the strict cubic Routh conditions or lies on the Hopf boundary with
  `𝔅_P > 0`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace PSC

/-- The balanced points of power synchronization on the line still undecided once the zero–Hopf
points are decided: the triple zero (`K = 0`, `a₁ = a₂ = 0`) and the Bautin-type points of the
Hopf boundary (`a₂ a₁ = a₀`, `a₁, a₀ > 0`, `𝔅_P = 0`). -/
def Model.Undecided (m : Model) : Prop :=
  Meets m .balanced ∧ ((m.K = 0 ∧ m.g.coeff1 m.Q = 0 ∧ m.g.coeff2 m.Q = 0) ∨
    (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
      0 < m.g.coeff0 m.Q ∧ bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift = 0))

/-- **The fold decided off the triple zero**: a balanced physical model at a fold `K = 0` with
`(a₁, a₂) ≠ (0, 0)` is unstable: `a₂ ≠ 0` (`Line.PSC.mem_den_unstable_of_fold_of_coeff2_ne`),
or `a₂ = 0` with a strict Routh violation (`a₁ < 0`, `Line.PSC.mem_den_unstable`) or the zero–Hopf
law (`a₁ > 0`, `Line.PSC.mem_den_unstable_of_zeroHopf`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_ne_tripleZero (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h : ¬ (m.g.coeff1 m.Q = 0 ∧ m.g.coeff2 m.Q = 0)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases h2 : m.g.coeff2 m.Q = 0
  · rcases lt_trichotomy (m.g.coeff1 m.Q) 0 with h1 | h1 | h1
    · exact mem_den_unstable m hp hb (Or.inr (Or.inl h1))
    · exact absurd ⟨h1, h2⟩ h
    · exact mem_den_unstable_of_zeroHopf m hp hb hK h2 h1
  · exact mem_den_unstable_of_fold_of_coeff2_ne m hp hb hK h2

/-- At a zero–Hopf point off the triple zero the model is unstable and the right-hand side of the
membership fails (`a₀ = 0`). -/
@[tmio TM, powerlib_domain] private theorem zeroHopf_cases (m : Model) (hp : Meets m .physical)
    (hd : ¬ m.Undecided) (hdeg : m.Degenerate) :
    m ∈ family.den (.flow .unstable) ∧ ¬ (Meets m .balanced ∧ (m.Routh ∨
      (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
        0 < m.g.coeff0 m.Q ∧
        0 < bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by
  obtain ⟨hb, ⟨hK, -, -⟩ | hB⟩ := hdeg
  · have hu := mem_den_unstable_of_fold_of_ne_tripleZero m hp hb hK
      fun h => hd ⟨hb, Or.inl ⟨hK, h.1, h.2⟩⟩
    unfold TMIO.Statement at hu
    have h0 : m.g.coeff0 m.Q = 0 := by
      rw [m.coeff0_eq hp.1.L.ne' hp.1.absSq_pos, hK]; simp
    refine ⟨hu, ?_⟩
    rintro ⟨-, hr | ⟨-, -, h0', -⟩⟩
    · exact (lt_irrefl (0 : ℝ)) (h0 ▸ hr.2.1)
    · exact (lt_irrefl (0 : ℝ)) (h0 ▸ h0')
  · exact absurd ⟨hb, Or.inr hB⟩ hd

/-- **Complete Lyapunov membership off the undecided points**: a physical model off
`Line.PSC.Model.Undecided` (the triple zero and the Bautin-type points) is Lyapunov stable iff it
is balanced and either meets the strict cubic Routh conditions or lies on the Hopf boundary with
`𝔅_P > 0` (`Line.PSC.mem_den_lyapunovStable_iff` off the degenerate set, the zero–Hopf points
unstable). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_not_undecided (m : Model)
    (hp : Meets m .physical) (hd : ¬ m.Undecided) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧
        0 < m.g.coeff1 m.Q ∧ 0 < m.g.coeff0 m.Q ∧
        0 < bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by
  by_cases hdeg : m.Degenerate
  · obtain ⟨hu, hn⟩ := zeroHopf_cases m hp hd hdeg
    have hl := Spectral.not_mem_den_lyapunovStable_of_unstable hu
    unfold TMIO.Statement at hl ⊢
    exact ⟨fun h => absurd h hl, fun h => absurd h hn⟩
  · exact mem_den_lyapunovStable_iff m hp hdeg

/-- **Complete local asymptotic membership off the undecided points**: a physical model off
`Line.PSC.Model.Undecided` is locally asymptotically stable iff it is balanced and either meets
the strict cubic Routh conditions or lies on the Hopf boundary with `𝔅_P > 0`
(`Line.PSC.mem_den_locallyAsymptoticallyStable_iff` off the degenerate set, the zero–Hopf points
unstable). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_not_undecided
    (m : Model) (hp : Meets m .physical) (hd : ¬ m.Undecided) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff2 m.Q * m.g.coeff1 m.Q = m.g.coeff0 m.Q ∧
        0 < m.g.coeff1 m.Q ∧ 0 < m.g.coeff0 m.Q ∧
        0 < bautinForm (m.g.Kp * m.Q) (m.g.R / m.g.L) m.g.ω0 m.angleShift))) := by
  by_cases hdeg : m.Degenerate
  · obtain ⟨hu, hn⟩ := zeroHopf_cases m hp hd hdeg
    have hl := Spectral.not_mem_den_lyapunovStable_of_unstable hu
    have hs := Spectral.den_las_subset_lyapunovStable (F := family)
    unfold TMIO.Statement at hl hs ⊢
    exact ⟨fun h => absurd (hs h) hl, fun h => absurd h hn⟩
  · exact mem_den_locallyAsymptoticallyStable_iff m hp hdeg

end PSC
end powerlib.GFM.Line
