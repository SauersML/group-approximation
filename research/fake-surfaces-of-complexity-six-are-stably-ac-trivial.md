---
rg: 2
id: fake-surfaces-of-complexity-six-are-stably-ac-trivial
kind: claim
title: Every contractible cellular fake surface of complexity 6 has a stably Andrews–Curtis trivial presentation
distinct_from:
  fake-surfaces-up-to-complexity-five-are-stably-ac-trivial: that covers complexity at most 5, which Fagan–Qiu–Wang also state; this is the first complexity beyond their theorem
  stable-andrews-curtis-conjecture: that is the open conjecture for every balanced presentation of the trivial group; this certifies it for presentations read off contractible fake surfaces with six vertices
artifacts:
  - research/artifacts/hl-andrews-curtis-fake-surfaces-2026-09-14.md
---

**ESTABLISHED** through `fake-surface-stable-ac-certificates-six-proof` (exhaustive
exact computation with replayable certificates). Unreviewed.

**Classes.** There are 97 connected 4-regular multigraphs with six vertices. On
them, `fsenum.cpp` finds 2,967,338 acyclic cellular fake surfaces up to
homeomorphism, 7762 of them without small disks (MSI job 780533). Orbit–stabilizer
passes on every graph, and a rerun reproduces the t ≤ 5 class files exactly.

**Statement.** For each class F, exactly one of the following holds:
- **(a)** for some spanning tree T of the singular graph, P(F, T) is stably AC-trivial;
- **(b)** π₁(F) ≠ 1, witnessed by a nontrivial permutation representation.

Case (b) occurs for exactly five classes: graph 78 code 1366823383, graph 88 code
704843050, graph 95 codes 520477952 and 1366799766, and graph 97 code 748582661. Each
has a nontrivial homomorphism to A₅. The other 2,967,333 classes are in case (a). So
every *contractible* cellular fake surface of complexity 6 is in case (a).

**Consequence.** Case (a) shows that every contractible cellular fake surface of
complexity 6 3-deforms to a point, through the correspondence between (AC1)–(AC5)
and 3-deformations. That correspondence is Wright (1975), cited in arXiv:2412.12293v2;
the primary source was not read.

This extends the verified range of the topological stable Andrews–Curtis conjecture
from complexity < 6 (Fagan–Qiu–Wang) to complexity ≤ 6. It is a range extension, not
progress on the conjecture beyond that range. AK(3) is not touched.
