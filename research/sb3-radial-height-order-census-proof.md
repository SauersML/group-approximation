---
rg: 2
id: sb3-radial-height-order-census-proof
kind: route
title: A finite census of 197416 local configurations proves the detour condition for the K1 order on SB_3
target: sb3-radial-height-order-is-a-short-detour-enumeration
requires: []
artifacts:
  - research/artifacts/zp-sb3-short-detour-2026-09-13-part2.md
  - research/artifacts/zp-sb3-short-detour-2026-09-13-part4.md
  - research/artifacts/zp-sb3-short-detour-review-2026-09-17.md
  - experiments/sb3-short-detour-review-2026-09-17/sb3_abstract_as_published.py
  - experiments/sb3-short-detour-review-2026-09-17/sb3_independent_abstract.py
  - experiments/sb3-short-detour-review-2026-09-17/sb3_real_vertex_census.py
---

Computer-assisted proof, reviewed PASS on 2026-09-17
(`research/artifacts/zp-sb3-short-detour-review-2026-09-17.md`).

1. **Reduction to a local statement.** Neighbours of a level-0 vertex v never share its key, so the
   neighbours of v in any initial segment of the K1 order are exactly the neighbours E(v) of smaller key,
   and all vertices of smaller key precede v. It suffices to show, for every v ≠ o, that E(v) ≠ ∅ and that
   one e_0 ∈ E(v) reaches all of E(v) within 3 steps through vertices of smaller key; then L = 6 ≤ 10.
2. **Finite abstraction** (part 4 §2, re-derived in review §3). Record each coordinate exactly when
   |x_i| ≤ 2, and otherwise its last two letters with h(x_i) clipped to [−3, 3]. Forbid moves into the
   unknown prefix and count undetermined key comparisons as "not earlier". Then abstract paths are real
   paths through really earlier vertices, and abstract E(v) equals real E(v). So a pass on every feasible
   configuration proves the claim for every real v.
3. **Census.** All 197416 feasible configurations pass. The published `sb3_abstract.py 2 3 6` was re-run
   verbatim in review with bad 0; it proves a 6-step bound, so L = 12. An independent re-implementation
   (`sb3_independent_abstract.py 2 3 6 4`) reproduces the configuration count. It finds that in every
   configuration some e_0 reaches all of E(v) within 3 steps (least-eccentricity histogram
   {0: 400, 1: 6517, 2: 130003, 3: 60496}, bad 0), so L = 6. Real-vertex censuses without abstraction
   (exhaustive for |x_i| ≤ 3, random up to length 10) find no failure, with least eccentricity ≤ 3.

Condition 1 alone also has a hand proof (part 2 §2).
