---
rg: 2
id: jacobson-full-boundary-forces-six-coordinate-packet
kind: claim
title: The full Jacobson boundary packet forces both first-level root directions and a GL6 times GL3 subgroup
distinct_from:
  jacobson-mixed-cells-reconstruct-full-first-level-root-packet: that uses the smaller boundary packet and reconstructs only the forward root group; this assumes the full five-coordinate boundary group and obtains the opposite roots and their complete six-coordinate relations.
artifacts:
  - research/artifacts/jacobson-full-boundary-opposite-roots-and-gl6-packet-2026-09-08.md
---

Use the full finite boundary group `C=GL_5(F_2) x GL_3(F_2)`
and its specified overlap `L=G_Q x K_P` with `F=G_Q x G_P`
from the boundary construction. Let

```text
Theta=<F *_L C | (hb)^3=1,W=1>.
```

Then `Theta` contains the forward and opposite first-level additive
root groups `Mat_(3 x 3)(F_2)`, joining levels zero and one in
the two directions. Together with their commutators and the head
group, these generate an embedded `K=GL_6(F_2)` on the first six
coordinates. The original tail splits into its local copy `tau(G_P)`
in `K` and a commuting residual copy `delta(G_P)`, so

```text
<K,F> = K x delta(G_P) ~= GL_6(F_2) x GL_3(F_2).
```

The literal Jacobson action proves injectivity and retains the head
mark. The full `C` is an explicit additional hypothesis; it has not
been derived from `Xi`. This theorem makes no assertion that `h`
lies in the resulting finite subgroup and proves no matrix gap.

DERIVATION
jacobson-opposite-root-steinberg-closure-proof
