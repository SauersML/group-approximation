---
rg: 2
id: leavitt-prefix-packet-pressure-certificate
kind: claim
title: The first finite Leavitt prefix packets admit a supercritical multiplicity certificate
---

OPEN.  Let `R=L_(F_2)(1,2)` and let `z` be the distinguished nonzero
involutory elementary root in the binary-Leavitt elementary group.  Use the
depth-one and depth-two dual-prefix root packets, together with their
three-root Heisenberg enlargements and the fixed elementary conjugacies
between matching root positions.

Find a finite family of packet inclusions, conjugacies, central spectral
cuts, and restriction decompositions whose integer multiplicity matrix `B`
has rational dual certificates

```text
-e_pi=B^T y_pi+s_pi,
s_pi>=0,                                                  (LPC1)
```

for every packet type `pi` on which `z` acts nontrivially.

Equivalently, the nonnegative rational cone of multiplicity vectors
compatible with all selected depth-one/depth-two packet relations is
supported entirely on types on which `z` acts trivially.

Only a fixed finite packet diagram is permitted.  The certificate must list
the finite groups, their character tables, every inclusion or conjugacy map,
the resulting integer matrix `B`, and the exact rational vectors in `(LPC1)`.
Once listed, verification is finite rational arithmetic.

## Attempts

The restriction of the depth-two Heisenberg packet to its depth-one packet
already has multiplicity greater than one on the nontrivial central type.
By itself this does not close a pressure cycle: it compares two distinct
packet carriers, so its nonnegative multiplicity cone still contains
positive solutions.  A certificate must add fixed off-diagonal prefix
conjugacies which return the refined types to the original packet types.
The smallest unresolved calculation is therefore the complete
depth-one/depth-two restriction-and-return matrix, followed by its rational
dual cone.
