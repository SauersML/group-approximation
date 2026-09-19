---
rg: 2
id: a4-triangle-propagates-inverse-c3-edge
kind: claim
title: One exact A4 triangle automatically propagates to the inverse C3 label
---

If unitaries or group elements satisfy

```text
x^3=y^2=(xy)^3=1,
```

then

```text
(x^-1 y)^3=1.                                         (A4-C3-INV)
```

Indeed the `(3,2,3)` spherical triangle presentation is `A4`, and in `A4`
the inverse of the order-three generator multiplied by the same involution is
again an order-three element.  Hence every central-`C3` constraint in the A4
packet automatically supplies its partner with `z` replaced by `z^-1`.

Applied to `atlas-central-c3-directed-gl5-classification`, bits `0` and `2`,
bits `1` and `3`, bits `4` and `5`, and bits `6` and `7` occur in forced pairs.
This explains the paired mask histogram exactly.  Thus the eight distinct
directed central constraints reduce algebraically to at most four: one for
each packet involution in each chart direction.  No propagation between the
two different involutions is asserted here.
