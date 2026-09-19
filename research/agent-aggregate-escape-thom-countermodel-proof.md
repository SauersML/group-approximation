---
rg: 2
id: agent-aggregate-escape-thom-countermodel-proof
kind: route
title: Use Thom's exact LEF windows and their regular representations
target: agent-aggregate-escape-kazhdan-root-no-upgrade
requires:
  - thom-kazhdan-central-fibre-hyperlinear-nonamenable
  - el-r-polynomial-robust-spectral-gap
---

Take Thom's group

```text
G=G_0(F_p[t,t^(-1)]) / direct_sum_(n>=0) F_p t^n
```

and the class `j` of the top-right root element `e_15(t^(-1))`.  The cited
Thom record gives finite generation, property `(T)`, LEF, centrality and
order `p` of `j`.  The finite-residual argument in
`thom-kazhdan-central-fibre-hyperlinear-nonamenable` proves that every
finite-dimensional representation kills `j`.

Let `F_n` exhaust `G`, with `1,j in F_n` and enough products included that
every fixed multiplication table occurs eventually.  LEF supplies injective
partial maps `theta_n:F_n->H_n` into finite groups, multiplicative whenever
the product stays in `F_n`.  Put

```text
sigma_n(g)=lambda_(H_n)(theta_n(g))                    (g in F_n),
```

and define it arbitrarily outside `F_n`.  Then every fixed relator has zero
defect for all sufficiently large `n`.  Injectivity gives
`theta_n(j)!=1`.  A nonidentity element has trace zero in the left regular
representation, so

```text
||sigma_n(j)-1||_(2,|H_n|)^2
 =2-2 Re tr(lambda_(H_n)(theta_n(j)))=2.
```

This is a genuine normalized-HS asymptotic countermodel to any implication
from property `(T)`, relative-root property `(T)`, exact finite-window
models, root torsion, and exact finite-dimensional invisibility to marked
word collapse.

Property `(T)` implies relative `(T)` for each subgroup: an almost invariant
vector yields a global invariant vector and therefore a vector invariant
under the chosen root subgroup.  It also implies `(T;FD)_rob`; the imported
polynomial elementary-group node records that implication independently of
the particular coefficient ring.  Neither assertion conflicts with the
microstates above because they provide spectral gap for an approximate
representation, not a correction of its multiplication law.

Finally, finite presentation is deliberately not asserted.  If `G` were
finitely presented, one sufficiently large LEF window containing a full
presentation would extend to a homomorphism separating each prescribed
nontrivial element, making `G` residually finite and contradicting the
finite-residual location of `j`.  This is exactly why the example refutes a
general rigidity upgrade without deciding the full finitely presented BCL
corner.
