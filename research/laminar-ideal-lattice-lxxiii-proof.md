---
rg: 2
id: laminar-ideal-lattice-lxxiii-proof
kind: route
title: Compact the primitive cover and fuse its laminar maximal ideals orthogonally
target: laminar-ideal-lattice-solves-lxxiii
requires:
  - finite-square-zero-packet-covers-cutdown
  - laminar-square-zero-packets-fuse-intrinsically
artifacts:
  - research/artifacts/stw99-lxxiii-lxvi-focused-audit-2026-08-31.md
---

Apply `finite-square-zero-packet-covers-cutdown` to `a` and `epsilon`.  It
gives square-zero `x_1,...,x_n` with

```text
(a-epsilon)_+ in Ideal(x_1)+...+Ideal(x_n).
```

Condition (LIL1) applies to these packet ideals, so
`laminar-square-zero-packets-fuse-intrinsically` gives one square-zero `x`
whose ideal is exactly their sum.  The displayed cutdown therefore belongs
to `Ideal(x)`.
