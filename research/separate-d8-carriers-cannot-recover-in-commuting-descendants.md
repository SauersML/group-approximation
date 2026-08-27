---
rg: 2
id: separate-d8-carriers-cannot-recover-in-commuting-descendants
kind: claim
title: Two D8-holonomy carriers cannot separately recover inside commuting descendant algebras
distinct_from:
  tensor-independent-child-carrier-gap: that puts one projection near two independent algebras; this treats two distinct D8 carriers and merely commuting algebras.
  balanced-router-pauli-holonomy-interface: that exposes reflections as words; this only requires algebra membership after packet decoding.
---

For projections `F,G` and commuting von Neumann subalgebras `A,B`, define

```text
h(F,G)=||(2F-1)(2G-1)(2F-1)(2G-1)-1||_2.
```

Then

```text
h(F,G)<=4 sqrt(2)[dist_2(F,A)+dist_2(G,B)].
```

The canonical atlas quarter carriers have `h(F,G)^2=1/2`, so their total
distance from commuting descendants is at least `1/8`.  Separate recovery
of the two native carriers is therefore enough for a fixed
dimension-independent obstruction; same-carrier transverse recovery is not
required.
