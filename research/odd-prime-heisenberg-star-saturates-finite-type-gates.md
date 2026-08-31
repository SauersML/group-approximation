---
rg: 2
id: odd-prime-heisenberg-star-saturates-finite-type-gates
kind: claim
title: An odd-prime Heisenberg star is an escaped nonpairing boundary cell, not a no-CE atlas
artifacts:
  - research/odd-prime-heisenberg-star-finite-type-proof.md
distinct_from:
  finite-type-partitions-obey-support-phase-balance: that gives the abstract no-leaf and phase-balance conditions; this constructs escaped partitions which attain them with the first genuine many-phase cancellation.
  clean-face-finite-type-packing-is-quadratically-bounded: that forbids several orthogonal atom groups attached only through one extremal clean face; here every context reuses one larger selector subgroup, so the bound is sharply avoided rather than contradicted.
  central-type-sum-equality-is-intersection-readable: that classifies common central chart sums; this example saturates that theorem and proves that all of its cross-chart proper marginals remain impossible.
---

Let `ell` be an odd prime. For `i=0,1,2`, let

```text
E_i=<J,X_i,Y_i |
     J^ell=X_i^ell=Y_i^ell=1,
     J central, X_i Y_i=J Y_i X_i>
```

be an order-`ell^3` Heisenberg group, and identify their centers
`Z=<J>`. Form the tree amalgam

```text
Gamma=E_0 *_Z E_1 *_Z E_2.                            (HPS1)
```

Fix a primitive `ell`-th root `zeta`. Let `pi_zeta` be the unique
`ell`-dimensional irreducible representation of `E_0` on which
`J` acts by `zeta`, and put

```text
q=z_(E_0,pi_zeta)=e_(Z,zeta).
```

For `i=1,2`, set `A_i=<J,X_i>`. For `r in F_ell`, let

```text
alpha_(i,r)(J)=zeta,       alpha_(i,r)(X_i)=zeta^r,
p_(i,r)=z_(A_i,alpha_(i,r)).                            (HPS2)
```

Then each family is an escaped finite-type context partition:

```text
p_(i,r)p_(i,s)=0 (r!=s),       sum_r p_(i,r)=q,         (HPS3)
p_(i,r) notin C[E_0].                                   (HPS4)
```

It simultaneously attains the root-intersection and phase-balance
boundaries:

```text
A_i intersect E_0=Z,
[E_0:Z]=ell^2=dim(pi_zeta)^2,                            (HPS5)
```

and every `J^a X_i^b` with `b!=0` has exactly `ell` incident nonzero
atom coefficients, whose `ell` character phases sum to zero. Thus
`ell=3` is the first escaped support cell whose cancellation is genuinely
not term pairing.

The two contexts have the exact dense overlap table

```text
A_1 intersect A_2=Z,
tau(p_(1,r)p_(2,s))=1/ell^3,
tau(p_(i,r))=1/ell^2.                                  (HPS6)
```

Hence the `ell by ell` restriction-overlap defect vanishes and both full
sums equal `q`.

This is a positive boundary countermodel, not a root closure. For subsets
`S,T subseteq F_ell`,

```text
sum_(r in S) p_(1,r)=sum_(s in T) p_(2,s)              (HPS7)
```

holds only when both sides are zero or both sides are `q`. In particular,
the cell shares no proper nonzero marginal. Moreover `Gamma` is the
fundamental group of a finite tree of finite groups, so it is virtually free
and hyperlinear.

The revised load-bearing gate is therefore stricter than a three-way phase
collision: construct a **proper** shared marginal which is not supported in
the literal intersection of two central charts. It must use atom-specific
chart groups within at least one side or a genuinely noncentral multipath
sum, and its cumulative support must also cross the finite-dimensional
visibility obstruction.
