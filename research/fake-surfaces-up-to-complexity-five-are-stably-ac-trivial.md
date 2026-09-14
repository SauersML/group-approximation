---
rg: 2
id: fake-surfaces-up-to-complexity-five-are-stably-ac-trivial
kind: claim
title: Every contractible cellular fake surface of complexity at most 5 has a stably Andrews–Curtis trivial presentation, and exactly one acyclic one has nontrivial fundamental group
distinct_from:
  stable-andrews-curtis-conjecture: that is the open conjecture for every balanced presentation of the trivial group; this certifies it for the presentations read off contractible fake surfaces with at most five vertices
  fake-surface-census-misses-acyclic-classes: that corrects the published list of these surfaces; this certifies every class of the corrected count
artifacts:
  - research/artifacts/hl-andrews-curtis-fake-surfaces-2026-09-14.md
---

**ESTABLISHED** through `fake-surface-stable-ac-certificates-proof` (exhaustive
exact computation with replayable certificates). Unreviewed.

Let F be an acyclic cellular fake surface of complexity t ≤ 5. There are 116,394
classes: 2, 17, 239, 4676 and 111,460 for t = 1, …, 5 (see
`fake-surface-census-misses-acyclic-classes`). For a spanning tree T of the
singular graph, P(F, T) is the balanced presentation whose generators are the edges
outside T and whose relators are the boundary words of the t+1 disks.

Exactly one of the following holds.
- **(a)** For some T, P(F, T) is stably Andrews–Curtis trivial.
- **(b)** π₁(F) has a nontrivial homomorphism to A₅.

Case (b) occurs for exactly one class: complexity 5, graph 28, code 37967319 in the
artifact's numbering. So every *contractible* cellular fake surface of complexity at
most 5 is in case (a).

**Scope.**
- **What this re-derives.** Fagan–Qiu–Wang (arXiv:2412.12293v2) state the
  topological version for complexity < 6: such surfaces 3-deform to a point. Case (a)
  gives it through the standard correspondence between (AC1)–(AC5) and 3-deformations
  of presentation complexes (P. Wright, *Group presentations and formal
  deformations*, Trans. AMS 208 (1975), cited there; the primary source was not read
  here).
- **What is new.** The coverage now includes the 62 classes missing from their check.
- **Unverified identification.** That the case-(b) class is the spine of the
  Poincaré homology sphere named in arXiv:2406.09439v3 §5.1 is plausible but was not
  checked.
