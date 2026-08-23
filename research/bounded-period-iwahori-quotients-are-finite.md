---
rg: 2
id: bounded-period-iwahori-quotients-are-finite
kind: claim
title: Every bounded-period BS14-Iwahori endpoint is a finite group
distinct_from:
  fixed-level-bs14-compatible-basin: that compares the moving preconditioning error with the stability basin; this proves unconditionally that every individual fixed-level target is finite and hence flexibly HS-stable.
  bs14-full-commutant-finite-period-preconditioner: that constructs an exact finite metacyclic core but leaves the adjoining involution arbitrary; this uses the ambient arithmetic normal-subgroup theorem to make the entire augmented Iwahori group finite.
  finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence: that classifies finite-dimensional unitary images of the unmodified group; this is an abstract quotient theorem after imposing one unipotent power relation.
---

Let

```text
Gamma=PSL_2(Z[1/2])
 =<x,r,s | x^2,(xr)^2,(xs^2)^3,(xrs)^3,
              r s r^(-1)=s^4>.                       (BPI1)
```

For every pair of positive integers `L,N`, the augmented quotient

```text
Gamma_(L,N)=Gamma/<<r^L,s^N>>                         (BPI2)
```

is finite.  It already becomes finite after imposing `s^N=1`.

Consequently every fixed bounded-period presentation arising from the
BS14 preconditioner is flexibly Hilbert--Schmidt stable.  In particular,
the bounded-support side of the proposed long/short staircase has no
remaining representation-semigroup or continuous-angle obstruction at a
fixed level.  What remains is quantitative uniformity as `L,N` move: the
finite-group stability radius may shrink faster than the preconditioning
error tends to zero.
