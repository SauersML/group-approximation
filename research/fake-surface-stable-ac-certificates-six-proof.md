---
rg: 2
id: fake-surface-stable-ac-certificates-six-proof
kind: route
title: Enumerate the acyclic cellular fake surfaces of complexity 6 and certify each by a replayed stable Andrews–Curtis trivialization or an A₅ image
target: fake-surfaces-of-complexity-six-are-stably-ac-trivial
requires: []
artifacts:
  - research/artifacts/hl-andrews-curtis-fake-surfaces-2026-09-14.md
---

**Model and enumeration.** The model is the one described in
`fake-surface-census-recount-proof`: a connected 4-regular multigraph plus per-edge
sheet matchings, with classes taken as orbits of half-edge automorphisms.
`experiments/andrews-curtis-fake-surfaces/fsenum.cpp` (MSI job 780533) did the
following:
- **Graphs.** It generated the 97 connected 4-regular multigraphs on six vertices.
  That count equals Table `tab:complexity_table` of arXiv:2406.09439v3.
- **Search.** It ran over all 6¹² matchings on each graph and kept the acyclic ones:
  12 matchings, t+1 = 7 disks, determinant ±1.
- **Classes.** It kept orbit minima: 2,967,338 classes.
- **Checks.**
  - Orbit–stabilizer passes on every graph.
  - The same binary reproduced the t = 3, 4, 5 class files byte for byte.

**Certificates.** The certificate language and the trusted checker are those of
`fake-surface-stable-ac-certificates-proof`: macros `conj`, `inv`, `mulc`, `destab`,
each a composite of (AC1)–(AC5), replayed by `acverify.py`. That checker rebuilds the
relators from (graph, code, tree) with its own corner walk. MSI job 788925, script
`certify6.sbatch`, ran five stages:
1. `fsac.py certify`, 64 shards: 2,952,729 certified on the default tree, 14,609 stuck,
   0 model disagreements;
2. `fsac.py rescue`: 14,426 certified on another spanning tree, 5 with a nontrivial A₅
   image, 178 open;
3. `fsac.py rescue2`: all 178 certified by backtracking elimination with a bounded
   product search;
4. `acverify.py` over every record: 2,967,333 pass as stably AC-trivial, 5 as
   π₁-nontrivial, 0 failures;
5. `coverage.py 6`: every one of the 2,967,338 classes has a passing record, and 0
   are uncovered.

**Conclusion.** Each class is in case (a) or case (b), and the two are exclusive
because (a) forces π₁ = 1.

**Trust surface.**
- The model;
- `acverify.py` and `coverage.py`;
- the macro decomposition;
- completeness of the enumeration: orbit minima over all matchings on all 97 graphs.

A first run of the same pipeline (job 785018) wrote truncated gzip shards and is
discarded. The producer did not close its output streams; that is fixed in c4df83a50.
