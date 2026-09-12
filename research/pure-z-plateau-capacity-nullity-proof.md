---
rg: 2
id: pure-z-plateau-capacity-nullity-proof
kind: route
title: Sandwich Cuntz capacity between dimension functions and full orthogonal Jiang--Su plateaus
target: pure-z-plateau-capacity-equals-quasitrace-nullity
requires: []
artifacts:
  - research/artifacts/stw93-mixed-slice-capacity-audit-2026-08-30.md
---

Suppose first that `cap_D(a)=infinity`.  For every normalized
lower-semicontinuous `2`-quasitrace `q` and every `n`, additivity and order
preservation of its dimension function give

```text
n d_q(a)<=d_q(1_D)=1.
```

Letting `n` tend to infinity gives `d_q(a)=0`, and
`q(a)<=||a||d_q(a)` gives `q(a)=0`.  This proves `(1)=>(2)=>(3)`.

Conversely, assume `q(a)=0` for every normalized `q`.  The square-null set
of a bounded `2`-quasitrace is a hereditary closed ideal, so it contains all
positive roots of `a`.  Hence

```text
d_q(a)=lim_(m->infinity)q(a^(1/m))=0.                   (1)
```

Fix `n` and choose pairwise orthogonal nonzero positive contractions
`z_1,...,z_n in Z`.  Put `g_i=rho(z_i)`.  Each `g_i` is full in `D`, because
`Z` is simple and `rho` is unital.  Moreover `q o rho` is a normalized
`2`-quasitrace on `Z`, hence its faithful unique trace.  Therefore

```text
d_q(g_i)>=q(g_i)>0                                     (2)
```

for every normalized `q`.

Pureness gives strict comparison.  Fullness of `g_i` and `(1)--(2)` imply

```text
a Cuntz-subequivalent to g_i
```

for every `i`.  Adding these inequalities and using orthogonality yields

```text
n[a]<=[g_1]+...+[g_n]=[g_1+...+g_n]<=[1_D].
```

This holds for every `n`, proving `cap_D(a)=infinity` and completing the
equivalence.

The unital Jiang--Su copy is used only to supply arbitrarily large finite
families of orthogonal **full** elements whose dimension is positive for
every normalized quasitrace.  Any other subalgebra with that plateau
property gives the same conclusion.
