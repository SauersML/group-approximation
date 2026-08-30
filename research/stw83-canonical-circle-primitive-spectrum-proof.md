---
rg: 2
id: stw83-canonical-circle-primitive-spectrum-proof
kind: route
title: Apply the primitive-ideal correspondence to the circle ideal and quotient
target: stw83-canonical-circle-primitive-spectrum-independent-of-n
requires: []
---

Let `J=K tensor C(T)`.  The defining extension is

```text
0 -> J -> A_N -> C(T) -> 0.                            (CPS2)
```

Both ideal and quotient are type I, and type I is closed under extensions,
so `A_N` is type I.

Primitive ideals containing `J` are the inverse images of the character
kernels of `C(T)`; call them `Q_lambda`, `lambda in T`.  The
primitive ideals not containing `J` correspond to `Prim(J)~=T`.  At
`t in T`, evaluation gives

```text
A_N/P_t ~= C*(S^N,K).
```

The standard representation of this Toeplitz algebra is irreducible because
it contains `K`, so `P_t` is primitive and these exhaust the open
stratum.

By hull--kernel topology, the closure of `{P_t}` is the set of primitive
ideals containing `P_t`.  Every `Q_lambda` contains `J` and hence
`P_t`.  No `P_s` with `s!=t` contains `P_t`, because their
intersections with `J` are the distinct, incomparable evaluation kernels.
This proves `(CPS1)`.

The relative topologies on both strata are their usual circle topologies.
Since every `Q_lambda` lies in the closure of every `P_t`, any open set
meeting the closed stratum contains the entire open stratum; its remaining
part is an open subset of the quotient circle.  This gives the displayed
topology, which contains no occurrence of `N`.  The two composition
factors in `(CPS2)` are stable or scalar circle algebras and have
one-dimensional spectrum, completing the claimed topological firewall.
