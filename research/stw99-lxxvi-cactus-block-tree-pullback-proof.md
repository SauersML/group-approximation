---
rg: 2
id: stw99-lxxvi-cactus-block-tree-pullback-proof
kind: route
title: Absorb one articulation unitary on the child block and iterate the block-cut tree
target: stw99-lxxvi-cactus-enriched-cu-classification
requires:
  - stw99-lxxvi-unicyclic-enriched-cu-classification
  - stw99-lxxvi-finite-tree-formation-preserves-cu-regularity
  - stw99-lxxvi-circle-formation-preserves-cu-regularity
  - stw99-lxxvi-finite-graph-compact-clutching-rigidity
artifacts:
  - research/artifacts/stw99-lxxvi-cactus-enriched-cu-audit-2026-08-31.md
---

For a one-point wedge, compatible Cu classes on the two factors have
isomorphic Hilbert-module fibers because `D` has stable rank one. Their
Hilbert-module pullback is countably generated and proves surjectivity.

For order reflection, start with genuine comparisons on both factors.
Stable rank one gives one alignment unitary at the common fiber. On the
child graph, Antoine--Dadarlat--Perera--Santiago, Proposition 2.2, lifts an
arbitrary unitary prescribed at one point; there is no second `K_1` class
with which it must agree. If the target support is proper, lift on a compact
nonvanishing subgraph and splice comparison vectors where they tend to zero.
The source-square error tends to zero, proving the one-point wedge map is an
order isomorphism. Restriction makes it coefficient-natural.

Root the block-cut tree and attach its leaf blocks one at a time. The wedge
theorem gives the compatible-tuple formula over all actual block Cu
semigroups. For a cactus, bridge blocks use the interval `Lsc` formula and
circle blocks use their actual ADPS hybrid Cu semigroups. Regrouping the
pointwise coordinates gives the displayed cactus fiber product.

The compact-clutching theorem identifies every nonzero constant compact
circle fiber with a `K_1(D)` family of projection bundles; all other circle
evaluation fibers are singletons. Taking the finite product proves the exact
`K_1(D)^{m_X(F)}` fiber statement.

For the actual first-factor map, every bridge coordinate is an isomorphism
by the coefficient Cu map and every circle coordinate is an isomorphism by
`stw99-lxxvi-circle-formation-preserves-cu-regularity`. Naturality and the
block-cut fiber product prove cactus Cu-regularity. The simple pure
corollary uses Lin and the simple-case STW theorem for these hypotheses, and
Seth--Vilalta separately for purity.
