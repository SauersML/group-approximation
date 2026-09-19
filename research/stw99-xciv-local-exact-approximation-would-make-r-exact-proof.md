---
rg: 2
id: stw99-xciv-local-exact-approximation-would-make-r-exact-proof
kind: route
title: Use Kirchberg's local operator-space criterion and the nonexact matrix product in R
target: stw99-xciv-some-tuple-avoids-all-exact-cores
requires:
  - stw99-xciv-some-finite-tuple-has-positive-fd-radius
artifacts:
  - research/artifacts/stw99-xciv-exact-core-barrier-audit-2026-08-30.md
---

Assume, towards a contradiction, that every finite subset of `R` can be
approximated arbitrarily well in operator norm by a unital exact
C-star subalgebra of `R`.

Let `E subset R` be finite-dimensional and let `eta>0`.  Choose a basis
`x_1,...,x_d` for `E`.  For sufficiently small `delta>0`, find an exact
subalgebra `A subset R` and `a_i in A` with

```text
||x_i-a_i|| < delta                    (1 <= i <= d).
```

The linear map `u:E -> span{a_1,...,a_d}` defined by `u(x_i)=a_i` is a
complete near-isometry when `delta` is small enough.  One direct way to see
this is to identify `E` with a fixed `d`-dimensional operator space: on a
fixed finite-dimensional domain, perturbing the images of a basis changes
the completely bounded norm by at most a constant depending only on that
basis.  Thus `||u||_cb ||u^(-1)||_cb < 1+eta` after decreasing `delta`.

The range of `u` lies in the exact algebra `A`.  Hence every
finite-dimensional operator subspace of `R` has exactness constant one.
Kirchberg's local operator-space characterization of exact C-star algebras
then implies that `R`, considered as a C-star algebra, is exact.

This is impossible.  Choose pairwise orthogonal nonzero projections
`p_n in R` with strong sum `1`, and choose a unital copy of `M_n` in each
corner `p_n R p_n`.  Bounded block-diagonal strong sums define an isometric
unital embedding

```text
product_(n>=1) M_n  -->  R.
```

The unbounded matrix product `product_n M_n` is nonexact (the standard
Wassermann matrix-product obstruction), while exactness is inherited by
C-star subalgebras.  Therefore `R` is not exact, contradicting the preceding
local conclusion.

Negating the assumed approximation property supplies a finite `F subset R`
and an `epsilon>0` such that every unital exact subalgebra `A subset R`
satisfies

```text
max_(x in F) dist(x,A) >= epsilon.
```

Every nuclear algebra is exact.  Thus the same tuple excludes all nuclear
regularity cores, including AF, ASH, finite-nuclear-dimension, and exact
`Z`-stable cores.  The conclusion deliberately does not exclude nonexact
`Z`-stable subalgebras and therefore does not decide Problem XCIV.

