---
rg: 2
id: perfect-two-generator-relation-module-not-cyclic-proof
kind: route
title: Five-term homology sequence on the coinvariants of the relation module
target: perfect-two-generator-relation-module-not-cyclic
requires: []
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

## Direct proof

Written out in the claim.  For `1 → K → F_2 → Q → 1` with `Q` perfect, the
five-term exact sequence in integral homology reads

    H_2(F_2) --> H_2(Q) --> K/[F_2,K] --> H_1(F_2) --> H_1(Q) --> 0 ,

and with `H_2(F_2) = 0`, `H_1(F_2) = Z²`, `H_1(Q) = 0` it forces
`K/[F_2,K] ↠ Z²`.  The coinvariants of a cyclic `ZQ`-module are a cyclic abelian
group, which admits no such surjection.

Entirely internal — group homology and nothing else — so `requires: []` is
literal here rather than a placeholder for unstated imports.
