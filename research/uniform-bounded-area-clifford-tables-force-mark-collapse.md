---
rg: 2
id: uniform-bounded-area-clifford-tables-force-mark-collapse
kind: claim
title: Uniform bounded-area Clifford tables force linear collapse of a common mark
distinct_from:
  marked-clifford-table-exponential-dimension: that starts from one all-pairs approximate extraspecial table and gives its dimension floor; this derives such a table for every rank from one presentation with one uniform van Kampen-area bound.
  thompson-clifford-central-product-tape: that constructs exact common-sign Clifford packets at arbitrarily many sites; this identifies the additional quantitative area property which would turn that exact tape into a nonhyperlinearity proof.
  hyperlinear-computable-hs-dehn-modulus-solvable-word-problem: that asks for a computable length-dependent modulus for all trivial words; this needs one constant area bound only for the multiplication identities of a selected Clifford family.
artifacts:
  - research/artifacts/static-challenger-occurrence-hs-breaker-2026-08-20.md
---

Let `Gamma=<S|R>` be finitely presented and let `j` be a word representing a
nonidentity element.  For every `N>=1`, suppose words

```text
sigma_N(g) in F(S),              g in E_N,              (BAC1)
```

are chosen for the extraspecial Pauli group `E_N`, with `sigma_N(J)=j`, and
there is one finite constant `A` such that

```text
Area_R(sigma_N(g)sigma_N(h)sigma_N(gh)^-1)<=A           (BAC2)
```

for every `N,g,h`.

Then every finite-dimensional unitary tuple `U` with
`epsilon=Def_R(U)` and `A epsilon<1/2` satisfies

```text
||j(U)-I||_2<=42 A epsilon.                              (BAC3)
```

Consequently `Gamma` is nonhyperlinear.

The theorem is insensitive to the lengths of the representative words.
Only the areas of their multiplication discrepancies matter: conjugating a
prototype relator to a remote address costs no normalized-HS error, whereas
deriving equality through a long stabilizer path generally makes `(BAC2)`
fail.  Thus an exact infinite Clifford tape is not enough; uniform bounded
multiplication-table area is the decisive additional property.
