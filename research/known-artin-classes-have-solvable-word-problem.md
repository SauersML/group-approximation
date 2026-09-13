---
rg: 2
id: known-artin-classes-have-solvable-word-problem
kind: claim
title: Right-angled, spherical, euclidean, FC-type, large-type, 2-dimensional and rank-three Artin groups have solvable word problem
distinct_from:
  every-artin-group-has-solvable-word-problem: that is the open statement for every Artin group; this imports the classes where an algorithm is known.
  artin-groups-satisfy-boone-higman: that asks for finitely presented simple envelopes of Artin groups with solvable word problem; this only records which Artin groups are known to have solvable word problem.
artifacts:
  - research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md
---

**ESTABLISHED** (literature import) by
`known-artin-classes-have-solvable-word-problem-citation`.

An Artin group `A_Γ` on a finite generating set has solvable word problem in each of
these cases:

1. `A_Γ` is right-angled;
2. `A_Γ` is of spherical type;
3. `A_Γ` is of irreducible euclidean type;
4. `A_Γ` is of type FC;
5. `A_Γ` is of large type: every label is at least 3;
6. `A_Γ` has dimension at most 2: every triangle with labels `p, q, r` satisfies
   `1/p + 1/q + 1/r ≤ 1`;
7. `A_Γ` has rank three;
8. `Γ` is a join of graphs from cases 1–7 along edges labelled 2, so `A_Γ` is a finite
   direct product of such groups.

Cases 1 and 2 are contained in case 4. Case 5 is contained in case 6 once the rank is
at least 3. Case 8 holds because a finite direct product of groups with solvable word
problem has solvable word problem.

**Not included:** Artin groups with no relation of length 3 (Blasco-García, Cumplido
and Morris-Wright, arXiv:2204.03523). Only the abstract was read.
