---
rg: 2
id: cantor-punctured-prefix-groups-detect-word-problem
kind: claim
title: A recursive presentation of a group containing punctured binary prefix groups has decidable word problem
artifacts:
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
---

Let F be any finite subset of the binary Cantor set and put

    K_F={v in V: v is the identity on a neighborhood of F}.

For F empty use K_F=V. If K_F<=D<=Homeo(C), every nontrivial
normal subgroup of D contains K_F. Thus any fixed 1!=k in K_F
belongs to the normal closure in D of every nonidentity element.

If D is finitely generated and recursively presented, it follows
that D has decidable word problem. This applies to E_nu, to A_1,
and to any finitely generated S(M,M') in the shell construction
whenever that group is recursively presented. In particular a
finite presentation of any of these groups implies decidability
of its own word problem, not only of the input P.

No conclusion about the word problem of the germ quotient Q is
included: it kills K_F, so this discriminator does not descend.
