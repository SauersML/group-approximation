---
rg: 2
id: nonhaagerup-spectator-coupling-proof
kind: route
title: Quotient by the spectator action and expose a sofic kernel
target: nonhaagerup-spectator-must-couple-nonamenably
requires:
  - abelian-by-virtually-free-groups-are-sofic
---

Let `H_0=ker(H -> Aut(A))`.  There is an exact sequence

```text
1 -> A rtimes (Gamma x H_0)
  -> A rtimes (Gamma x H)
  -> J -> 1.                                             (NAS2)
```

The subgroup `H_0` acts trivially on `A` and commutes with `Gamma`, so the
kernel in `(NAS2)` is canonically

```text
(A rtimes Gamma) x H_0.
```

The first factor is sofic by
`abelian-by-virtually-free-groups-are-sofic`; the second is sofic because
subgroups of sofic groups are sofic.  Direct products of sofic groups are
sofic.  If `J` is amenable, sofic-by-amenable permanence applied to `(NAS2)`
proves the claim.

Now take `H=SL_3(Z)`.  It is finitely presented and residually finite, hence
sofic, and has property `(T)`, hence is non-Haagerup.  Every amenable quotient
of a discrete property-`(T)` group is finite, so the image condition reduces
to: the `SL_3(Z)` action on `A` must have infinite image.  This gives the
explicit actor `(NAS1)` and rules out its trivial and finite actions.

Finally, an independent finite-field Bernoulli module for `H` gives the
restricted wreath product `(direct_sum_H F_p) rtimes H`, which is sofic when
`H` is sofic and the lamp is amenable.  Tensoring the source construction
with this independent Haar Bernoulli action therefore tensors its crossed
product with a Connes-embeddable algebra.  It supplies no embedding of a
nonalgebraic source base and cannot turn a Connes-embeddable algebraic source
factor into a non-CE one.  Hence any viable compact algebraic extension over
`(NAS1)` must use a genuinely mixed module, rather than two independent
coordinate systems.
