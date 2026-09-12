---
rg: 2
id: lef-graph-wreath-via-finite-lamp-tables
kind: route
title: Verify finite graph retractions and then transplant LEF lamp tables
target: lef-lamp-graph-wreaths-are-surjunctive
requires: [finitary-split-extension-surjunctivity-permanence, graph-product-normal-forms-and-rf-permanence]
artifacts:
  - research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Sections 2--5 of the artifact give the implication in full.

For a residually finite lamp, take `N_S` to be the induced graph product on
finite `S`, and kill all outside vertex groups. Induced subgraph inclusions
are split injections and these finite graph products are residually finite
by Green's graph-product theorem. A word's finite set of vertices proves
detection and the finite-support identity. An element fixing `S` pointwise
fixes all surviving lamp generators, so it fixes the retraction. The
required finitary theorem therefore proves the residually finite case.

For a LEF lamp, record all intermediate lamp products in reductions of
finitely many test words. An injective partial map to one finite group
preserves these reductions and their reduced survivors. This embeds every
finite partial group table into a graph wreath with that finite lamp, the
same graph and the same actor. Such model groups are surjunctive by the
first case. A strict injective cellular automaton would transplant its
finite left-inverse identity and its forbidden output cylinder to one of
them, a contradiction. The actor embeds as a subgroup, proving the reverse
implication.

Green's residual-finiteness theorem and closure of surjunctivity under
local embeddings are standard inputs, not claims of new results. The
artifact supplies the local-embedding proof explicitly and records primary
references for both. Green's normal form and residual finiteness theorems
are now required as `graph-product-normal-forms-and-rf-permanence`, added
2026-09-12 after an independent re-derivation of this route.
