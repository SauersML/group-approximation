---
rg: 2
id: same-side-modular-extensions-do-not-integralize-edge-transport
kind: claim
title: Same-side modular extendibility does not integralize low-energy Iwahori transport
distinct_from:
  low-gap-transport-not-geometric-integralization: that uses arbitrary representations of a cyclic group; this realizes the same obstruction with irreducible Iwahori types that extend to exact representations of the modular group.
  iwahori-fractional-transport-integralization: that now explicitly assumes one upper and one opposite Nielsen-twisted modular extension; this proves merely requiring modular extensions on the same side is still insufficient.
---

There are sequences of exact finite-dimensional representations of the
Iwahori group `B=Z*C_2`, each of which is the restriction of an exact unitary
representation of `PSL_2(Z)=C_2*C_3`, such that:

- the identity comparison has edge defect tending to zero;
- every pair of occurring irreducible `B`-types has mixed-intertwiner bottom
  energy tending to zero;
- the four isotypic overlap masses are all `1/4`;

but every block-respecting unitary matching on `1-o(1)` of the dimension has
squared normalized Hilbert--Schmidt distance at least

```text
(2-sqrt(2))(1-o(1))                                  (SME1)
```

from the identity.

Thus ordinary modular extendibility does not repair fractional transport.
Any positive Iwahori integralization theorem must use the **opposite**
extension locus, equivalently the specific Nielsen involution induced by the
Iwahori commensuration, and not just the fact that both edge types extend to
some modular representations.
