# ct-* lanes: the unowned tail of sec:chain-core

Lead: session `nonsofic-existence-49`, launched 2026-09-13 ~16:25 CDT. The user re-issued the order in that session:
formalize every sentence of the non-MF manuscript unconditionally in Lean, with no literature inputs.

## Scope

- tex 1541–1807 at origin/main 68481e4d7, plus the rewritten Introduction paragraph at tex 249–259.
- This is the content added by 73a84cd9c: prop:bilateral-three, lem:involution-localization, cor:dynamic-rank-budget,
  the remark on the two-ended compactification (tex 1769–1792) and the remark on the rank-two limitation of the
  compression method (tex 1794–1807).
- Why it had no owner: the chain-* plans were scoped at 3c64a92ef, which predates 73a84cd9c, and none of the seven
  chain-* reports mentions this content.

## Lanes

Each lane probes and lands only through `nmprobe.sh` and `nmland.sh`, and shares its probe clone with one existing lane.

| lane | target | clone |
|---|---|---|
| ct-bilateral-cell | ring and matrix identities in the proof of prop:bilateral-three (tex 1549–1596) | lix-a |
| ct-bilateral-mf | prop:bilateral-three endpoint (tex 1541–1607), plus the Introduction sentence on GL_3 | ring-b-end |
| ct-involution | lem:involution-localization (tex 1658–1694) | lix-j |
| ct-return-tower | return sections, tower corner, Φ, block flattening (tex 1707–1741) | lix-h |
| ct-rank-budget | cor:dynamic-rank-budget endpoint (tex 1696–1767), plus the Introduction aperiodic sentence | lix-f |
| ct-two-ended | remark tex 1769–1792 | lix-e |
| ct-rank-two-limit | remark tex 1794–1807 | lix-i |
| ct-sentences | census rows and model tests for the block | ring-b-alg |

## Boundaries

- chain-radical keeps thm:core-mf-radical: the kernel identification, local finiteness, and the EL clauses.
  ct-bilateral-mf supplies the prop:bilateral-three endpoint that its GL_n (n ≥ 3) clauses use.
- ct lanes consume lem:transient-matrices, thm:core-ring-reflection and lem:chain-core-models through their owners'
  declaration names on main, or as named Props until those close.
- chain-radical's Introduction keys `684721560ced`, `aac4a95b387b` and `c6f8fb6abe29` hash the paragraph as it read
  before 73a84cd9c. ct-sentences keys only the new GL_3 and aperiodic sentences; the radical sentences stay with
  chain-radical.

## Coordination

ct lanes report to session `nonsofic-existence-49`. Send cross-lane needs, or pieces that need more lanes, to that
session.

## Wave 2 (2026-09-13 ~16:40 CDT): 33 more lanes from session nonsofic-existence-49

The user asked this session for a massive team. Every wave-2 lane runs an ownership check before it builds anything:
it greps origin and the shared tree, reads `lanes/*.files`, `landed.log` and the roster rulings, and first lands a
`CLAIM <piece> <module>` line in its report. A piece a lane of the other swarm landed on within about 3 hours, or holds
in-flight files for, is recorded with its owner and not rebuilt. All landings go through `nmland.sh`, which refuses
clobbers.

| family | lanes | job |
|---|---|---|
| range audit and fix | ms-intro-1..4 (tex 1–357), ms-compress-1..4 (358–739), ms-inverses-1..4 (740–1174), ms-binary (1175–1231), ms-units (1232–1337), ms-traces-1..3 (1808–2106), ms-torsionfree (2107–2507) | sentence ledger; verify each `formalized` row is closed, root-reachable, printed generality, printed route, no literature binder; build the missing carriers in new modules |
| chain-core ranges | ms-core-1..4 (1338–1540), ms-core-5 (1608–1662) | ledger and model tests; build only leaves an owner report lists as unowned, or sentence carriers no key map lists |
| W1 second starts | w1-binder-1..8 | one independent start per residual waist binder (ClassCountInput, UnboundSameCell, CaseOneSameCell, C6′ TwoGonHolds, MultipleEdgePocketRegion, SectionPocketFaceSet, PocketPinchLabelled, GeodesicCollar); new modules only, never owners' files |
| literature sweep | ms-cite-1 (1–1337), ms-cite-2 (1338–2507) | every `\cite` used as a step must have a proved carrier |

## Census findings for the census lane (from ct-sentences, 2026-09-13 ~17:00; details in `ct-sentences.md`)

- The ct block has 121 sentence keys, taken from census merge `merge-0913-160921` (after 73a84cd9c). All 121 are
  `unassigned` on main. Owners are recorded in `metadata/nm-census-rows/ct-sentences.tsv`. chain-radical's rows cover 22 of
  these keys: 10 still match its plan, and 12 were rekeyed by 73a84cd9c.
- Splitter defect 1: the abbreviation guard has no word boundary, so two rows each hold two sentences:
  `ded50f77e36b` ("…killed. Core restriction…") and `5e4354e1556b` ("…trivial. The same reasoning…").
- Splitter defect 2: unnumbered displays are dropped, so eleven fragment rows carry the displayed mathematics (for example
  `e94a545b030a` "Moreover,", `4c62dd1963db` "For $n\ge2$,", `4a0223a24da4` "Put", `10fe7a237145` "The identities"). They
  must not be graded `structural`. The full list is in `ct-sentences.md`.
- A hand audit plus closed `decide +kernel` models (`Dynamics/ChainCoreTailModels`, 313212d8a) found no false printed
  identity in the bilateral cell, the return tower or the two-ended codimension count.
