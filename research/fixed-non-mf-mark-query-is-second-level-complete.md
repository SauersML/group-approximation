---
rg: 2
id: fixed-non-mf-mark-query-is-second-level-complete
kind: claim
title: A fixed non-MF marked constraint has exact second-level data complexity
root: true
distinct_from:
  mf-recognition-finite-presentations-is-pi2-complete: that asks whether every finite presentation defines an MF group; this classifies one fixed sound certificate for non-MF and makes no completeness claim for all non-MF groups.
  literal-central-mark-corona-invisible: that proves the fixed mark is an MF obstruction; this computes the exact data complexity of realizing that obstruction inside an input finite presentation.
  mf-recognition-recursive-presentations-is-second-level-complete: that varies a recursive presentation and asks MF itself; this uses one fixed finite existential template and varies only the finite target presentation.
---

Let `E=<x_1,...,x_r|R_E>` be the literal forty-one-relator sofic,
hyperlinear, non-MF group, and let `w` be its nontrivial central involution
which every norm-matrix-corona representation kills.  Given a finite group
presentation `p`, consider the fixed-template query

```text
exists g_1,...,g_r in G_p,
  [r(g_1,...,g_r)=1 for every r in R_E]
  and w(g_1,...,g_r)!=1.                               (FMQ1)
```

The set of finite presentations satisfying `(FMQ1)` is
`Sigma^0_2`-complete.  Its complement, equivalently

```text
every homomorphism E -> G_p kills w,                    (FMQ2)
```

is `Pi^0_2`-complete.

Every YES instance of `(FMQ1)` is non-MF: the satisfying tuple induces a
homomorphism `phi:E->G_p`, and the surviving element `phi(w)` is a nontrivial
member of `Rad_MF(G_p)`.  Hence exact second-level hardness already occurs
for a single fixed, finite, sound non-MF constraint template; the program is
part of the input only through the target finite presentation.

