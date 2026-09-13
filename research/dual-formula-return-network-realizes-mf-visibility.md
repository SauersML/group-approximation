---
rg: 2
id: dual-formula-return-network-realizes-mf-visibility
kind: route
title: Realize the dual monotone formula by series and parallel return paths and add one feedback edge
target: lef-kazhdan-mf-closure-realizes-monotone-boolean-rules
requires:
  - directed-seam-mf-closure-is-cycle-pruning
  - directed-seam-normal-lattice-is-vertex-edge-incidence
artifacts:
  - research/artifacts/pestov91-mf-closure-and-monotone-rules-2026-09-13.md
---

Section 2 constructs a directed acyclic two-terminal network for
`F^*(y)=1-F(1-y)`, using series composition for AND and parallel
composition for OR. Add one feedback edge. All edges initially lie
on cycles, so the source group is LEF. Killing all occurrence factors
of selected variables removes their network edges. The feedback
factor becomes invisible exactly when every return path is lost,
which is `F(1_I)=1`. The cycle-core quotient is a faithful LEF target
for that factor in every other case.
