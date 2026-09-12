---
rg: 2
id: centralize-selector-packet-to-wordize-stabilizer-corrector
kind: route
title: Centralize the selector packet to wordize the selected stabilizer corrector
target: tailored-checks-to-common-marked-group-extensions
requires:
  - stabilizer-corrector-hermitianizes-zero-compression
  - central-marked-two-cycle-zero-compression-cell
---

**INVALIDATED CENTRALIZER-WORDIZATION PROPOSAL.**  Let `H` be the finite
selector group and let `q` be its selected character idempotent.  Given a
payload unitary `w` with `q w q=0`, adjoin a corrector `s`, impose

```text
[s,h]=1                    (h in H),
(sw)^2=1,
```

and feed the involution `sw` into the marked two-cycle cell.  The first
family of relators certainly makes `s` stabilize `q`, so this would be a
particularly simple ordinary-word implementation of the operator-level
corrector.

`selector-packet-central-corrector-fails-on-a-three-cycle` invalidates this
route.  Even for the regular multiplicity-free packet of `C_2^2`, a payload
with zero selected compression can have a three-cycle on character lines.
Every unitary centralizing the packet is diagonal and therefore preserves
that three-cycle support after left multiplication; its product with the
payload cannot square to the identity.  The countermodel does admit the
unrestricted selected-projection stabilizer corrector, and even a packet
normalizer corrector, so it does not invalidate either of those less
restrictive gates.
