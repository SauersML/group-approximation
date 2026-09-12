---
rg: 2
id: virtually-cyclic-inputs-have-fp-shell-stabilizers
kind: claim
title: Virtually cyclic inputs admit shell groups with finitely presented finite singularity stabilizers
artifacts:
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
---

Let P be infinite and virtually cyclic. Choose the finite-ray shell
enumeration from `shell-prefix-core-detects-finite-ray-enumerations`.
Write E=E_nu and Omega=V*0^infinity. For every finite M subset M'
subset Omega, the group

    S(M,M')={e in E: sing(e) subset M, e fixes M' pointwise}

is finitely presented. In particular this supplies all three clauses
A_1,A_12,A_2 of `decidable-inputs-have-fp-shell-stabilizers` for this
input family. E and all its finite pointwise stabilizers on Omega are
finitely presented.

The proof uses a central subgroup of the isotropy germ group which
has finite index in the prefix germ. It does not assume that the whole
prefix germ is normal. This is a positive control for the Cantor-shell
construction; it neither proves the universal shell-stabilizer claim
nor asserts that arbitrary subgroups of a finitely presented finite-ray
permutation group are finitely presented.
