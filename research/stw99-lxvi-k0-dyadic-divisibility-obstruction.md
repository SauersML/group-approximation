---
rg: 2
id: stw99-lxvi-k0-dyadic-divisibility-obstruction
kind: claim
title: K0 divisibility obstructs CAR insertion into a finite mixed corner
distinct_from:
  stw99-lxvi-car-corner-iff-coherent-dyadic-v-chain: that gives the exact positive-monoid criterion; this records its computable but weaker K0 obstruction.
---

Let `B` be a C\*-algebra and `p in B` a projection.  If `pBp` contains a
unital copy of the CAR algebra, then

```text
[p]_0 belongs to intersection_(n>=1) 2^n K_0(B).
```

More precisely, there are positive projection classes `g_n` with

```text
[p]_0=2^n g_n,          g_n=2g_(n+1).
```

Consequently no finite projection `p` with

```text
0!=[p]_0 notin intersection_n 2^n K_0(B)
```

can be used in the maximal-corner construction for Problem LXVI.  In
particular, the obstruction applies when `[p]_0` has nonzero image in a
finitely generated free abelian quotient of `K_0(B)`.
