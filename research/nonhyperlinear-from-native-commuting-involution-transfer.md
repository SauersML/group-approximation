---
rg: 2
id: nonhyperlinear-from-native-commuting-involution-transfer
kind: route
title: Collapse the finite arithmetic two-coordinate group through its native overlap transfer
target: non-hyperlinear-group
requires:
  - native-sl3-commuting-involution-group
  - commuting-conjugate-involution-transfer-for-sl3-pair
---

Assume `G_cc` were hyperlinear and take canonical microstates.  The actor
coordinates are regular-trace microstates of `A`; the word `c` is an
asymptotic trace-zero involution centralizing `C`; and the last relator in
`(GCC1)` says that `c` commutes with its `h`-conjugate.  The native transfer
therefore gives

```text
|tr(m)| -> 1.
```

But `m!=1` in `G_cc`, so canonical trace separation gives `tr(m)->0`, a
contradiction.  Therefore `G_cc` is nonhyperlinear.

This route needs neither the D8 extension, the full recursive lamp module,
nor Higman embedding.  Its sole open input is exclusion of the balanced
interior projection overlap `(CCI7)` in finite matrix microstates.
