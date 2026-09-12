---
rg: 2
id: occurrence-local-dimension-games-force-mark-collapse
kind: claim
title: Uniform local occurrence games force collapse of a marked matrix sector
distinct_from:
  uniform-bounded-area-clifford-tables-force-mark-collapse: that reconstructs every multiplication identity of a whole extraspecial group; this asks only for the sampled local checks of robust dimension-witness games.
  stabilizer-generator-control-has-unbounded-address-loss: that tries to identify all word names of one virtual observable through stabilizer paths; this assigns a separate word to every test occurrence and delegates global consistency to game soundness.
  marked-clifford-table-exponential-dimension: that is the terminal finite-group dimension breaker; this permits any robust finite game family whose certified dimension tends to infinity.
artifacts:
  - research/artifacts/static-challenger-occurrence-hs-breaker-2026-08-20.md
---

Let `Gamma=<S|R>` contain a nontrivial central involution `J`.  Suppose there
are finite games `G_N`, constants `C,C_0,beta,eta>0`, and numbers
`D_N->infinity` with the following property.

For every finite-dimensional tuple `U in U(d)^S` with

```text
Def_R(U)=epsilon,                 ||J(U)-I||_2>=beta,    (OGC1)
```

the occurrence words and a fixed local rounding/extraction procedure produce
a finite-dimensional strategy `S_N(U)` of local dimension at most `C_0 d`
such that

```text
1-value(S_N(U))<=C epsilon^2.                            (OGC2)
```

The constants are independent of `N,d`.  Assume every strategy for `G_N` of
value greater than `1-eta` has local dimension at least `D_N`.

Then there is `delta>0` such that every finite matrix tuple with
`Def_R(U)<delta` satisfies

```text
||J(U)-I||_2<beta.                                      (OGC3)
```

In particular `Gamma` is nonhyperlinear whenever `beta<sqrt(2)`.

The occurrence formulation requires no globally chosen observable for a
virtual label.  Different appearances may be different group words;
bounded-arity consistency tests compare them directly.  If every local test
is a literal conjugate of one of finitely many prototype relators, its
normalized-HS cost is independent of address length.  Global decoding is a
consequence of the robust game theorem, not a telescoping equality along a
stabilizer word.
