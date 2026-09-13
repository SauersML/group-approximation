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
