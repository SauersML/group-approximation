---
rg: 2
id: shared-fanizza-exit-leakage-localization
kind: claim
title: The returned exit leakage localizes to the original shared Fanizza tuple
distinct_from:
  capacity-gated-common-corner-bcs-two-cell: that proves the analytic common-source estimate controlling the localized functional; this records the resulting NCL13 target for the actual returned exits.
  localized-non-ce-leakage-forces-cross-gram-overlap: that proves the matrix-only leakage-or-overlap inequality once this localization estimate is supplied; this is exactly the remaining word-decoder estimate NCL13.
  shared-bcs-eight-slice-full-overlap-actuator: that asks for near-full return into capacity; this asks only that off-capacity leakage be an approximately reducing BCS-quiet corner.
---

OPEN.  For the exits `T_(c,b)` decoded from the fixed shared Fanizza packet,
let

```text
L_(c,b)=(1-C)T_(c,b)T_(c,b)^*                           (SFEL1)
```

after fixed-packet exactification, and let `Lambda` be the finite mixed
moment functional `(NCL3)--(NCL5)` formed using the **original shared**
Fanizza involution tuple.  Construct the mixed actuator words so that every
sufficiently accurate finite-dimensional tuple satisfies

```text
Lambda <= K_loc E_rel+o(1),                              (SFEL2)
```

with `K_loc` independent of matrix dimension.

Independent context packets do not imply `(SFEL2)`: the leakage projection
must approximately reduce the original tuple before its occurrences split,
and the original BCS residuals must remain small after compression.  A
universal tracial proof is impossible because the exact non-CE/regular model
may have a nonzero residual-free leakage corner.  The estimate must therefore
use the finite-matrix decoder and the mixed shared-word actuator.

Once `(SFEL2)` is proved, no near-full overlap actuator is needed.
`positive-overlap-antiphase-closes-fanizza-return` combines it with the
explicit three-book HNN antiphase cell and gives the fixed energy floor.

The analytic reduction is now established by
`capacity-gated-common-corner-bcs-two-cell`.  The sole remaining construction
is `capacity-gated-common-source-gram-word-cell`: decode context intertwiners
whose Gram source is literally the same projection `(SFEL1)` for all four
native contexts.  Context-private sources do not suffice.
