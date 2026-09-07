---
rg: 2
id: full-mf-radical-perfect-commutator-bound-proof
kind: route
title: Finite quotients are MF, and two commutator estimates give the quadratic bound
target: full-mf-radical-forces-perfect-commutator-bound
requires: []
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
---

## Proof

**Perfectness.**  If `G^ab != 1` then, being finitely generated abelian and
nontrivial, it surjects onto a nontrivial finite cyclic group `F`.  The
regular representation embeds `F` in some `U(k)`, and constant sequences
embed `U(k)` in the unitary group of a norm matrix corona, since the class of
`(V,V,...)` differs from `1` by `||V-I||_op>0`.  So `F` is MF and the
composite `G ->> G^ab ->> F` is a nontrivial homomorphism to an MF group,
against `Res_MF(G)=G`.  So `G^ab=1` and every generator is a product of
commutators.

**Two estimates.**  For unitaries,
`||V_1...V_k - I|| <= sum_j ||V_j - I||` and `||U_i^(-1)-I||=||U_i-I||`, so

```text
||a(U) - I|| <= |a| D(U)
```

for every word `a`.  For unitaries `A,B`, multiplying `ABA^(-1)B^(-1)-I` on
the right by `BA` gives

```text
||[A,B]-I|| = ||AB-BA|| = ||(A-I)(B-I)-(B-I)(A-I)||
           <= 2||A-I|| ||B-I||.
```

**The bound.**  From `w_i = x_i^(-1) prod_k [a_(ik),b_(ik)]` one gets
`U_i w_i(U) = prod_k [a_(ik)(U), b_(ik)(U)]`, so the distance from `U_i` to
that product is `||w_i(U)-I||`, while the product lies within
`sum_k 2|a_(ik)||b_(ik)| D(U)^2` of `I`.  Adding and maximizing over `i`
gives `(Q1)`.  If `D(U) <= 1/(2B)` then `B D(U)^2 <= D(U)/2`, and `(Q1)`
rearranges to `(Q2)`.
