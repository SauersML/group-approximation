---
rg: 2
id: nonorthogonal-pair-forbids-single-term-syndrome-ports-proof
kind: route
title: Combine kernel support of flag effects with the compulsory fault-cover inequality
target: nonorthogonal-pair-forbids-single-term-syndrome-ports
requires: [qubit-pairs-have-half-gap-and-unbounded-rounder-cost]
artifacts:
  - research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md
---

Every exact output must flag `P` or `Q_N`, since their kernels have zero
intersection. For its input POVM this implies `F_P+F_Q >= I`.

For any positive contraction `F <= cP`, positivity forces
`ker P subset ker F`, so `F=PFP<=P`. Therefore the proposed individual
dominations imply `F_P+F_Q <= P+Q_N`. The least eigenvalue of the latter is
`2/(N^2+1)<1` for `N>1`, contradicting the covering inequality. The explicit
ground vector is `(N,-1)^T/sqrt(N^2+1)`; tensoring it with a spectator
vector gives the same contradiction on any extension. Sections 3 and 4 of
the artifact justify both the POVM argument and the kernel step in full.
