---
rg: 2
id: steinberg-chord-fox-recurrence-has-zero-solutions
kind: claim
title: The two big-cell chord Fox recurrences have only the zero solution
---

For every odd prime `p`, the only function

```text
f:F_p^3 -> F_p
```

satisfying the two explicit equations `(SBC5)`, with boundary values read by
the signed tree-cut rule of `steinberg-cycles-have-big-cell-chord-coordinates`,
is `f=0`.

This is a strict coordinate form of the open Steinberg test.  It has exactly
three root parameters and no remaining panel-sum unknowns.  A proof may work
separately on the generic transformed chords and the exceptional affine
linear or bilinear loci where one of the transformed point/plane normalizing
coordinates vanishes; the latter terms are fixed cut-sums, not free boundary
data.  The seven generic rational transformations and all their exceptional
loci are recorded in `steinberg-fox-chord-actions-are-explicit`.
