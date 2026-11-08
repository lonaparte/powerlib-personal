# Changelog

Completed architectural and library changes, newest first. Detailed diffs remain
in Git; working statistics, build receipts and development plans are not kept here.

## 2026-11-08

- Reduced the passive elements to two dual topologies. `Passive.SeriesRLC`
  (`Passive/Series.lean`: `R`, `L`, elastance `S = 1/C`; impedance
  `R + Ls + S/s`) and `Passive.ParallelRLC` (`Passive/Parallel.lean`: `G`, `C`,
  reciprocal inductance `Γ = 1/L`; admittance `G + Cs + Γ/s`) replace
  `Passive.RL`, `Passive.GC` and `Passive.RX` (`Passive/Branch.lean`,
  `Passive/Shunt.lean`, `Passive/Phasor.lean` removed). RL, GC, pure L/C and the
  series RLC loop are the cases with some parameters zero; a phasor is the
  immittance at `s = jω` (`SeriesRLC.impedance_jω`, `reactance`, `absSq`).
  Models that need a first-order element state it with an explicit field
  (`S = 0` for series branches, `Γ = 0` for shunts): the RL impedance model, the
  dq branch, the current-loop plants, the GFL/GFM filters, lines and DC links,
  the SMIB11 link and terminal capacitor, the RL-network branches and nodes, the
  LCL and dq LC filters, the lossless line and the RLCG ladder. The quasi-static
  models' lines are series branches whose reactance is taken at the model's grid
  frequency (rate PLL `ω_s`, model B `ω_g`, VSG `ω_s`) or at the per-unit
  frequency `ω = 1` (quasi-static power loop, four-state, basin guard, post-fault
  SMIB). The power-flow line powers, the synchronous-machine line power and the
  current-limiting formulas take a series branch and a frequency; the form-B and
  stochastic-PH reactances are the reactances of the series branch
  `(R_g, L_g, C_f)`; the modulation-transfer reactances are series and parallel
  inductive branches. The dq immittances, per-unit laws, EMT companion elements
  and PH instances are stated for the two topologies.

## 2026-11-07

- Unified the remaining passive elements. Ideal inductors and capacitors are
  the lossless `Passive.RL`/`Passive.GC` (an explicit lossless field in the
  model): the DC links of the GFL models, the LCLine and form-B filter
  capacitors, the six-state carrier inductances, the SMIB11 terminal capacitor,
  the LCL and dq LC filters, the series RLC capacitor and the lossless line.
  Added the phasor branch `Passive.RX` (`Passive/Phasor.lean`: impedance,
  `|Z|²`, series and parallel connection, the reactances of `RL` and `GC`); the
  grid lines of the quasi-static models (rate PLL, quasi-static power loop, four-
  state, basin guard, model B, VSG) carry it, and the power-flow line powers,
  the synchronous-machine line power and the current-limiting formulas take
  it. The form-B and stochastic-PH line reactances are both built from the
  element reactances, and the modulation-transfer reactances are proved to be
  the series/parallel combinations. The DC-link PH instance is now the PH model
  of a `Passive.GC` (leakage `G ≥ 0`). The element per-unit laws moved from
  `Transform/PerUnit` to `Passive/PerUnit.lean` (the inductor law generalised to
  the RL branch), and the EMT companion elements are the RL branch and the GC
  shunt (companion formulas generalised to the lossy elements).
- The passive-component and grid-structure sources now declare in the
  namespaces of their directories: `Circuits.RL`/`Circuits.LCL` became
  `Passive.RL`/`Passive.LCL`, the dq RL branch `Passive.DqRL` (was
  `CurrentControl`), the PH instances `Passive` (was `PH.Models`), the lines
  `Passive.Line.*` (was `Line.*`); `Circuits.Interconnection` became
  `Grid.Interconnection`, and the RL networks, the grid impedance and the power
  flow declare in `Grid` (were `PH.Models`, `GFL.Impedance`, `Network`), the
  modulation transfer in `Grid.ModulationTransfer`. References in the library,
  tests, examples and Agda scaffolds follow. The KYP storage positivity of the
  RL model is now `Passive.RL.Impedance.energy_pos`, proved from the branch law.
- Separated passive components from grid structure. `Passive/` holds the
  components and their own properties (RL branch and its dq form, LCL filter,
  RLC and LC PH instances, lines and cables); `Grid/` holds how components are
  connected (source–load interconnection, RL networks, the grid impedance seen
  from a converter, power flow, shared network nodes). `Circuits/` is gone.
- Gave the series RL branch a single definition, `Passive.RL` (`Passive/Branch.lean`),
  with its decay rate, impedance, stored energy and power balance. The RL
  impedance model, the dq branch, the current-loop plants (PI, IMC, drive
  cascade), the GFL filters and lines, the GFM matching-control filters, the
  SMIB link, RL-network branches and the series RLC loop now carry a
  `Passive.RL` field; their former `R`/`L` names remain as accessors, and the
  restated sign-of-decay proofs now use `Passive.RL.decay_pos_iff`.
- Gathered the remaining simple R/L/C combinations into `Passive/`. Added the
  shunt `Passive.GC` (`Passive/Shunt.lean`, dual of `Passive.RL`) and the dq
  forms of both (`Passive/Dq.lean`: dq impedance and admittance matrices, the
  dq capacitor law moved from `Transform/Park`, and the dq power balance moved
  from `GFL/DCLink/PowerBalance`); both elements gained their trajectory energy
  balance. The GFL `Z_oc`/`Y_load` matrices are now the elements' dq
  immittances, and `Z_ext` moved to `Grid/GridImpedance`, which no longer
  depends on a GFL module. RL-network nodes, the GFM matching DC nodes and DC
  links, the closed-loop filter capacitor, the dq RL plant and impedance of
  `Passive/DqRL`, the RLCG ladder, the telegrapher equations and the line's
  characteristic impedance now carry `Passive.RL`/`Passive.GC`. Removed the
  restatements `dcEnergy_balance`, `pcc_eq_bridge_add_losses` and the duplicate
  dq impedance of `Passive/DqRL`; the IMC and drive-cascade decay proofs use
  `Passive.RL.decay_pos_iff`, the DC-droop one `Passive.GC.decay_pos_iff`.

## 2026-11-06

- Grouped the engineering sources by equipment class: `GridTiedConverter/` (`GFL`,
  `GFM` with current limiting under `GFM/Limiting`, `PLL`, `CurrentControl`),
  `PowerSystem/` (`Synchronous`, `Network`, `Frequency`), and `Circuits/Line`
  for lines and cables. Updated imports, scaffold module names and references
  while preserving public declaration namespaces.

- Consolidated the layer and implementation-interface documentation into
  `Architecture.md`, moved normative requirements into `Rules.md`, and removed
  the separate `Layers.md` and `ImplementationLayer.md` documents.
- Grouped Agda scaffolds by topic beside their Lean sources. Scaffold ownership
  now lives in source headers and is checked without a Markdown registry.
- Moved circuit PH instances to `Circuits/PH`, general family readings to
  `Family/Reading.lean`, symbolic resistance fitting to
  `Estimation/ResistanceFit.lean`, and formal tests to `tests/lean`.
  Updated imports while preserving public declaration namespaces.
- Completed TMIO classification of foundation and domain theorems
  (`ae37476`, `2ca127a`). Distinguished general coordinate theory from concrete
  electrical transformations and models, including Clarke/Park and dq (`4850810`).

## 2026-11-05

- Enforced incompatible TMIO and foundation/domain label combinations, while
  permitting M and TM with either class. Removed the automatic association of
  connection structure with domain metadata (`d34dd33`).
- Classified the remaining core theorems as foundation or domain (`0e1e9e9`).

## 2026-10-28–2026-10-30

- Established T and M nodes plus TM, MI and IO relations as the knowledge kinds;
  removed concrete observation records from the core (`7693ae3`).
- Stored classification directly on declarations with `@[tmio ...]` and removed
  duplicate maintained classification lists (`f7e37a9`, `232da3f`).
- Extended the closed connection grammar for polymorphic and constrained claims,
  migrated model results to certified connection interfaces, and completed their
  TMIO review. Added implicit EMT realization interfaces (`4ab6586`, `49c3d05`).

## 2026-10-26

- Added envelope sentences, random continuous-time behaviours and disturbed
  realizations, including the distinction between finite- and infinite-horizon
  safety (`bb46a37`).

## 2026-10-15–2026-10-21

- Introduced the model–implementation–record stack and the VSM platform interface,
  followed by current-loop mismatch, digital and voltage-limit realizations
  (`6368c01`, `a950849`, `18fe862`, `4741dfe`).
- Added discrete semantics, exact sampling, switched averaging and explicit Euler
  bridges, including systems with ports (`b730e23`, `2403c3e`, `dddf522`, `4ef99e1`).
- Shared family interpretation through generic spectral templates and hub readings;
  unified coordinate and base changes (`035d080`, `8316344`, `de6b8ba`).
- Added restatement checks and strengthened scaffold coverage, representation-change
  recognition and public-reference checks (`23deab3`, `825d15a`, `2f31b44`).

## 2026-10-11

- Established typed public connection claims and whole-package admission.
  Completed rational certificate synthesis and formalized certificate-language
  boundaries (`ffee892`, `af28db3`).
