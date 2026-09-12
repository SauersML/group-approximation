---
rg: 2
id: finite-order-normal-generation-controls-corona-rank-scale
kind: claim
title: Normal generation orders the active rank scales of finite-order elements in every matrix-corona representation
artifacts:
  - notes/EXACT_CORONA_DIMENSION_AND_HILBERT_HOTEL.md
---

**ESTABLISHED.**  Let `rho:G->U(Q_d)` be a norm-matrix-corona
homomorphism, and let `a,b in G` have finite orders.  Let `p_a,p_b` be the
spectral projections of `rho(a),rho(b)` away from the eigenvalue `1`, with
coordinate ranks `r_n(a),r_n(b)`.

If `b` is a product of `N` conjugates of `a` or `a^(-1)`, then

```text
r_n(b) <= N r_n(a) eventually,                       (NRS1)
p_b <=_MvN p_a^(directSum N),                         (NRS2)
Supp_rho(b) <= Supp_rho(a).                           (NRS3)
```

Consequently, if `a` and `b` have the same normal closure, their active
rank germs are mutually bounded by fixed multiples, their support ideals
coincide, and their active corners are full corners of the same ideal.  More
precisely, any fixed normal words witnessing

```text
b in <<a>> and a in <<b>>
```

give integers `N,M` for which

```text
p_b <=_MvN p_a^(directSum N),
p_a <=_MvN p_b^(directSum M).                         (NRS4)
```

Thus finite-order normal-equivalence classes carry a canonical corona rank
scale, independent of the chosen torsion mark.  In particular, in a simple
group all nonidentity finite-order elements have the same active rank scale
in every matrix-corona representation, and every active-core reblocking
obtained from one such element is Morita equivalent to the active-core
reblocking obtained from any other.

