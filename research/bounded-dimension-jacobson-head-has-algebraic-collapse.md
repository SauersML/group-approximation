---
rg: 2
id: bounded-dimension-jacobson-head-has-algebraic-collapse
kind: claim
title: The Jacobson head has a quantitative collapse modulus in every bounded dimension
distinct_from:
  jacobson-property-t-and-finite-k-do-not-exactify-the-head: that identifies the missing dimension-free normalized-HS modulus; this proves the strongest modulus supplied by finite-dimensional compactness and shows exactly where its constants depend on dimension
  qutrit-complementary-jacobson-signs-with-minimal-router-are-finite: that constructs an exact finite model for all four mixed sign quarters; this uses that model to prove the mixed subpresentation cannot itself have any head-collapse modulus
  binary-jacobson-core-is-weakly-sofic-with-fd-head-radical: that proves exact finite-dimensional annihilation; this upgrades it to a semialgebraic quantitative estimate for each bounded dimension
---

Fix a finite presentation

```text
G=EL_28(F_2<S,T | TS=1>)=<Sigma | R>
```

and a word `w` representing the head root `x_13(1-ST)`.  For every integer
`D>=1` there are constants

```text
C_D<infinity,       alpha_D>0,                            (BDJ1)
```

such that every unitary `Sigma`-tuple `U` of dimension `n<=D` satisfies

```text
||w(U)-1||_(2,n)
 <= C_D max_(r in R)||r(U)-1||_(2,n)^alpha_D             (BDJ2)
```

whenever the maximum on the right is at most one.

Consequently every approximate representation sequence which keeps
`||w(U)-1||_2>=epsilon>0` and has presentation defect tending to zero must
have dimensions tending to infinity.  Exact finite-dimensional
annihilation plus compactness therefore does give quantitative head
collapse, but only after a dimension bound is fixed.

The mixed-orientation qutrit packet cannot improve (BDJ2) to a
dimension-free estimate by itself.  The subgroup

```text
<C,g_1,H,U,V>
```

containing all four complementary sign quarters is finite and has an exact
regular representation in which the head `H` is nonidentity.  Hence the
relators internal to that packet have zero defect while the head defect is
`sqrt(2)`.  Any global collapse proof must use full-presentation relations
outside this finite router envelope and control them uniformly as
`n->infinity`.

This result neither constructs Jacobson microstates nor proves global head
collapse.  It closes the finite-dimensional-compactness route exactly and
leaves the sole possible escape in unbounded multiplicity profiles.

DERIVATION
compact-semialgebraic-lojasiewicz-head-collapse-proof
