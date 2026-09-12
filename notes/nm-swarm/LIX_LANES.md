# LIX LANES (lead nonsofic-existence-41, 2026-09-11 ~21:20 CDT) — stronger Problem LIX, rad(n) | k

USER ORDERS: "let's launch way more agents to do literally everything as fast as possible" / "also do even
MORE agents on k1 injectivity" / "I meant LIX".  Plus every order in `$NM/COMMON_RULES.md` (binding: no
literature inputs ever; land everything constantly; rule 18 no hold; MSI only; never build locally).

TARGET: make `GroupApproximation.NinetyNineProblems.ClimbedPowersOutside n` a THEOREM for every `n ≥ 2`
(`GroupApproximation/Manuscript/NinetyNineProblems/ProblemLIXStrong.lean`), so that
`Palomar/LIXStrongSolution.lean`'s `exists_simple_separable_powers_outside_U0_of` etc. lose their hypothesis.
Chain: `Corollary4Powers n b` (lix-tower) + `LemmaTwoHoldsForSections n (b k)` for `p ∣ n`, `p ∤ k`
(Step C with k zeros: lix-oddside / lix-oddside-n; Step D mod p: lix-evenside / lix-evenside-n), over the
coefficient ports (lix-coeff, lix-lh, lix-thom, lix-cupone) and odd-primary operations (lix-steenrod,
lix-descent), with the powers layer (lix-powers).  Design: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
(§1 math, §3 protocol — binding: Lean only after solving; model-test numeric claims ON MSI, small; a
module is green only with its own `✔ [k/N] Built` line, never `Replayed`; grep
`notes/lix-lane-reports/FLEET_TRAPS.md` before the first probe).

## Ownership by file (a lane creates files only under its prefixes; two lanes never edit one file)
| lane | predecessor report (notes/lix-stronger-lane-reports/) | owns | clone |
|---|---|---|---|
| lix-tower | sp-tower.md | `Analysis/LIX*` EXCEPT `LIXPowers*`; `CharClass/LIXShape*`; the Gen shape layer; new `Analysis/LIXCor4Powers*` | lix-a (shared) |
| lix-powers | sp-powers.md | `Analysis/LIXPowers*` | lix-a (shared) |
| lix-oddside | sp-oddside.md | `CharClass/LIXK*` EXCEPT `LIXKGen*`; `CharClass/LIXSection*`, `LIXHsq*`, `LIXStepCOdd*` (Step C geometry) | lix-b (shared) |
| lix-oddside-n | sp-oddside-n.md | `CharClass/LIXKGen*` | lix-a (shared) |
| lix-evenside | sp-evenside.md | `CharClass/ParityP*`, `CharClass/StepDModP*` | lix-c (shared) |
| lix-evenside-n | sp-evenside-n.md | `CharClass/LIXStepDGen*` | lix-c (shared) |
| lix-steenrod | sp-steenrod.md | `CharClass/OddP*` EXCEPT `OddPDescent*` (21:50) | lix-c (shared) |
| lix-descent | sp-descent.md | `CharClass/OddPDescent*` | spare1 |
| lix-lh | sp-lh.md | `CharClass/LerayHirsch*`, `Chern*`, `Projective*`, `CohomologyChart*`, `MayerVietoris*`, `CohomologyDelta*` (21:40) | nm-b |
| lix-thom | sp-thom.md | `CharClass/Thom*`, `Gysin*`, `Bundle*`, `Slice*`, `RelativeSupport*`, `ThomStepCEuler*` | lix-b (shared) |
| lix-coeff | sp-coeff.md + sp-relhomotopy.md | `CharClass/Coeff*`, `Relative*` (not RelativeSupport), `RelHomotopy*`, `CohomologyBasic*`, `CohomologyAssoc*`, `CohomologyMayerVietoris*`, `CohomologyKunneth*`, `CohomologyLH*` | lix-b (shared) |
| lix-cupone | sp-cupone.md | `CharClass/CupOne*`, `SteenrodCupOne*`, `Kronecker*`, `CohomologySphere*`, `CohomologyContractible*` | lix-d |
| rescue-lix (→ endpoint) | sp-endpoint.md | `Palomar/LIXStrong*`, `comparator-lix-strong.json`, `Manuscript/NinetyNineProblems/ProblemLIXStrong*`, workflows/scripts | cs-endpoint |
Any other CharClass/Analysis file: ask the lead before editing.  `SteenrodCupOne*` is lix-cupone's (the
mod-2 cup-1 layer), odd-primary `Steenrod*` otherwise lix-steenrod's.

## Protocol (additions to COMMON_RULES)
- STEP 0: read your predecessor report IN FULL, and `$NM/reports/rescue-lix.md` (where the 09-10 in-flight work went: commits, states, repairs, traps); then find unlanded predecessor work in the SHARED tree:
  `git -C /Users/user/nonsofic_existence diff --stat origin/main -- <your prefixes>` and untracked files
  (`git status --porcelain -- <prefixes>`), plus `attic/inflight/rescue-lix/` on origin.  Copy anything
  worth keeping into your overlay list, land it at once per rule 18 (NM_UNVERIFIED / NM_ATTIC), then probe.
- FAMILY RULING (21:35): exponent k ↔ the degree-k section `KGen.bVecK n (k − 1)`; lix-tower proves
  `Corollary4Powers n (fun k => KGen.bVecK n (k-1))`; sphere hypothesis `IsSphereUnitary` (lix-powers).
- RULE 20 (user 21:45): shared artifact cache + SHARED clones; probe only changed files, batched. Your clone (if lix-a..d) is being warmed by hard links from cs-endpoint (`nm/lixclone2-lix.out` on MSI — v1
  `lixclone.out` died, ignore it); until then
  probes exit 5 (PROBE DEFERRED): author meanwhile and retry every ~15 min.  CharClass closures are
  large: start with ONE small module, and set `NM_CPUS=16` (SLURM) only when >300 modules must rebuild.
- Cross-lane needs go to the lead (SendMessage to "nonsofic-existence-41"), never by editing a peer's file.
- STAY ACTIVE while your probe runs (poll its output file every few minutes while authoring); a fork that
  ends its turn does not wake reliably.
- Keep your running report at `$NM/reports/<lane>.md` (NEEDS / GREEN / AUTHORED-UNVERIFIED / TRAPS) and land
  it as `notes/lix-stronger-lane-reports/<lane>.md` with each landing batch.
