# Changelog

Completed architectural and library changes, newest first. Detailed diffs remain
in Git; working statistics, build receipts and development plans are not kept here.

## 2026-11-07

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
