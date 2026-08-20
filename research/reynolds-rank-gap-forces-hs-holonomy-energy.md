---
rg: 2
id: reynolds-rank-gap-forces-hs-holonomy-energy
kind: claim
title: A normalized adjoint Reynolds rank gap forces ordinary Hilbert--Schmidt holonomy energy
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that manufactures the rank gap from forbidden packet mass; this converts any such gap into an ordinary matrix-word energy lower bound.
  finite-group-intertwiner-laplacian-gap: that controls one almost-intertwiner using a fixed representation table; this compares the ranks of two possibly different Reynolds fixed spaces.
---

Let `U_1,...,U_D,V_1,...,V_D,T in U(d)` and define operators on
`L^2(M_d)` by

```text
P=(1/D) sum_j Ad(U_j),          Q=(1/D) sum_j Ad(V_j).
```

Assume `P,Q` are orthogonal projections; this holds when the two lists are
uniform enumerations of finite represented groups, with repetitions allowed.
Put

```text
epsilon=(1/D) sum_j ||T U_j T* - V_j||_2^2.                    (RHG1)
```

Then

```text
|rank(P)-rank(Q)|/d^2 <= 2 epsilon.                            (RHG2)
```

All matrix norms are normalized Hilbert--Schmidt norms. Thus an extensive
rank discrepancy between two adjoint fixed spaces cannot be hidden by
increasing `d`: any termwise finite-word holonomy between their Reynolds
averages pays a dimension-free amount of ordinary normalized-HS energy.

More generally, `(RHG2)` holds with `2 epsilon` replaced by the squared
normalized Hilbert--Schmidt superoperator distance between `Ad(T)PAd(T)*`
and `Q`. This is the interface for a sparse relation-ideal certificate that
controls the averaged channels without pairing their terms.

