---
rg: 2
id: nonhyperlinear-from-three-dimensional-hyperrigid-lp
kind: route
title: Prove LP for one explicit three-dimensional hyperrigid system to get a non-hyperlinear group
target: non-hyperlinear-group
requires:
  - explicit-prs-harris-three-dimensional-system-has-lp
  - lp-of-harris-generator-system-forces-nonhyperlinear
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

Take `(G,pi,S_pi)` from
`explicit-prs-harris-three-dimensional-system-has-lp`.  Harris
hyperrigidity and Proposition 3.4(2) promote `LP(S_pi)` to LLP of
`C^*_pi(G)`.  The representation is nonamenable and weakly contains the
left regular representation, so Paulsen--Rahaman--Samei Theorem 4.6,
contraposed, makes `G` non-hyperlinear.

The witness is `G` itself.  The sole open input is now a lifting theorem
for one explicitly written three-dimensional operator system.
