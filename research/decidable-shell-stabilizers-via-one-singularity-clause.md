---
rg: 2
id: decidable-shell-stabilizers-via-one-singularity-clause
kind: route
title: The one-singularity clause alone yields all three shell stabilizer clauses
target: decidable-inputs-have-fp-shell-stabilizers
requires:
  - decidable-inputs-have-fp-one-singularity-shell-stabilizer
  - shell-one-singularity-fp-forces-two-point-stabilizers-fp
artifacts:
  - research/artifacts/shell-one-singularity-stabilizer-reduction-2026-09-16.md
---

Let P be an infinite finitely presented group with decidable word problem.
The first required claim supplies an enumeration nu for which A_1 is
finitely presented. The second required claim holds for every countable
input and every enumeration. For this same nu it makes A_12 and A_2
finitely presented. These are exactly clauses 1, 2 and 3 of the target,
with the same shell group, the same points p=0^infinity and q=1*0^infinity,
and singularities relative to V.

The converse holds as well, since clause 1 of the target is the first
required claim. The target and its one-clause form are therefore
equivalent. Any positive construction only has to present A_1.
