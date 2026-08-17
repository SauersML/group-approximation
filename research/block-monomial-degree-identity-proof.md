---
rg: 2
id: block-monomial-degree-identity-proof
kind: route
title: Push the equation through the block-permutation homomorphism
target: block-monomial-root-forces-permutation-order
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Write `V = (+)_{j in J} V_j`.  An invertible operator is *block-monomial* if
it carries each `V_j` onto some `V_{p(j)}`; composition of two such carries
`V_j` to `V_{q(p(j))}`, so

    pi : { block-monomial invertibles }  ->  Sym(J)

is a group homomorphism.  Its kernel is the block-diagonal invertibles.

Let `w in G * <t>` have exponent sum `m`, let `rho(G)` be block-diagonal, and
let `T` be block-monomial with `pi(T) = sigma`.  Applying `pi` to the
evaluated word, every coefficient letter contributes `pi(rho(g)) = 1` and
every `t^{±1}` contributes `sigma^{±1}`.  The `sigma^{±1}` all commute with
one another, so the product is `sigma^{m}` regardless of the order in which
the letters occur:

    pi(w(rho, T))  =  sigma^{deg_t(w)}  =  sigma^m .

If `w(rho, T) = 1` then `sigma^m = 1`, and `m = ±1` gives `sigma = 1`, i.e.
`T` is block-diagonal.

`requires: []` is a proof commitment.  Full write-up in
`research/artifacts/kervaire-laudenbach-audit-2026-08-17.md` §H.2.
