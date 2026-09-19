---
rg: 2
id: stw59-simple-ah-factorial-unitary-torsion
kind: claim
title: Simple nuclear stably finite AH algebras with zero K1 realize every finite cyclic unitary-component order
distinct_from:
  stw59-simple-ah-non-k1-injective: This proves exact factorial orders and every prescribed finite cyclic order in a family of algebras; the earlier claim only supplies one order-two example.
artifacts:
  - research/artifacts/stw59-factorial-torsion-simple-ah-manuscript-2026-09-05.md
  - research/artifacts/stw59-factorial-torsion-independent-review-2026-09-05.md
---

For every integer n>=2, there are a separable simple unital nuclear
stably finite infinite-dimensional AH algebra A^(n) and a unitary v_n
such that K1(A^(n))=0, the component of v_n has exact order n! in
U(A^(n))/U0(A^(n)), and diag(v_n,1) is null-homotopic in U(M2(A^(n))).

The explicit tower has r_i=n 2^i, base S^(2n) times product_(j<i)
CP^(r_j), and bundle C^n direct-sum direct-sum_(j<i) L_(j+1)^(sum r_j).
Its maps are the line-twisted point-evaluation maps of the LIX
construction, with evaluation points having dense projected tails.
The initial unitary generates pi_(2n)(U(n))=Z/(n!).

The finite obstruction tests every power: a degree-k sphere pullback
would give mapping-torus top Chern number ±k, whereas all allowable
mapping-torus bundles have that number divisible by n!. Thus precisely
the powers divisible by n! are null-homotopic at every stage and in
the simple limit.

For any d>=2, choosing n with d dividing n! and taking v_n^(n!/d)
gives exact component order d. The algebra may depend on d. This is
not a calculation of the whole component group or a claim that one
fixed algebra contains all finite cyclic groups. It strengthens the
LIX counterexample and does not claim a separate named-problem solution.

ROUTES

stw59-factorial-chern-divisibility-tower-proof
