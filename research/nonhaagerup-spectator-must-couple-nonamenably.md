---
rg: 2
id: nonhaagerup-spectator-must-couple-nonamenably
kind: claim
title: Appending a non-Haagerup spectator works only through nonamenable module coupling
distinct_from:
  haagerup-actors-cannot-host-property-t-algebraic-envelope: that says the total actor must be non-Haagerup; this tests the least circular way to satisfy that condition and shows that a spectator factor is insufficient.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that compares probability coinduction with the semifinite induction corner; this is a group-permanence obstruction for direct-product actor extensions.
  abelian-by-virtually-free-groups-are-sofic: that handles a virtually-free total actor; this permits a non-Haagerup total actor but proves soficity when its new direction acts through an amenable image.
---

Let `Gamma` be finitely generated virtually free, let `H` be sofic, and let
the direct product `Gamma x H` act on a countable abelian group `A`.  Write

```text
J = image(H -> Aut(A)).
```

If `J` is amenable, then

```text
A rtimes (Gamma x H)
```

is sofic.  Its group von Neumann algebra is Connes embeddable and cannot
contain the fixed non-CE relation factor.

Consequently the least circular explicit non-Haagerup replacement actor

```text
Lambda_min = Gamma_Manzoor x SL_3(Z)                    (NAS1)
```

can support the algebraic-envelope program only if the `SL_3(Z)` direction
has nonamenable (equivalently, because it is a property-`(T)` quotient,
infinite) image on the **same dual module**.  A trivial or finite spectator
action cannot help.  Nor does tensoring with an independent algebraic
Bernoulli `SL_3(Z)`-shift help: that adds a Connes-embeddable wreath-product
factor without algebraizing or importing the Manzoor base.

Thus `(NAS1)` is an explicit, finitely presented, residually finite,
non-Haagerup actor that contains the source actor and avoids circular use of
a non-hyperlinear group.  The remaining constructive datum is sharply a
mixed `F_p[Gamma_Manzoor x SL_3(Z)]`-module on which the two commuting actor
directions interact; actor enlargement by itself is barren.
