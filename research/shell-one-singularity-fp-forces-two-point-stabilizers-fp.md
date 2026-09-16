---
rg: 2
id: shell-one-singularity-fp-forces-two-point-stabilizers-fp
kind: claim
title: A finitely presented one-singularity shell stabilizer forces finite presentation of both two-point shell stabilizers
distinct_from:
  shell-fp-stabilizer-forces-fp-germ-group: that passes from a finite presentation of A_1 DOWN to its germ quotient Q by killing the neighborhood kernel; this passes SIDEWAYS from A_1 to the larger two-point groups A_12 and A_2 by an explicit finite presentation calculus.
  decidable-inputs-have-fp-shell-stabilizers: that is an existence problem for a good enumeration of a decidable input; this is an implication valid for every countable input and every enumeration, and asserts no finite presentation outright.
artifacts:
  - research/artifacts/shell-one-singularity-stabilizer-reduction-2026-09-16.md
---

Let P be any countably infinite group and nu:P->N any bijection. Use the
shell group E_nu=<V,hat(P)> of
`shell-cantor-embeddings-are-finite-germ-extensions`, put p=0^infinity
and q=1*0^infinity, and take singularities relative to V:

    A_1  = {e: sing(e) subset {p}, e(p)=p},
    A_12 = {e in A_1: e(q)=q},
    A_2  = {e: sing(e) subset {p,q}, e(p)=p, e(q)=q}.

If A_1 is finitely presented, then A_12 and A_2 are finitely presented.

Consequently, for each fixed enumeration the three clauses of
`decidable-inputs-have-fp-shell-stabilizers` are equivalent to the
single clause that A_1 is finitely presented. No finite presentation of
A_1 for any input beyond those already handled is asserted, and no
implication from a finitely presented germ group Q to A_1 is asserted.
This is a written proof, not a Lean formalization.
