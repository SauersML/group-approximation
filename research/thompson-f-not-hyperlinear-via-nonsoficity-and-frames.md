---
rg: 2
id: thompson-f-not-hyperlinear-via-nonsoficity-and-frames
kind: route
title: A nonsofic F whose hyperlinear models would carry a full invariant frame is not hyperlinear
target: thompson-f-is-not-hyperlinear
requires:
  - thompson-f-is-not-sofic
  - thompson-f-hyperlinear-models-normalize-a-full-masa
---

Suppose `F` were hyperlinear. By
`thompson-f-hyperlinear-models-normalize-a-full-masa` in its equivalent form,
`F` is sofic, contradicting `thompson-f-is-not-sofic`.

**The split is exact.** Conversely, if `F` is not hyperlinear then it is not
sofic (`thompson-f-not-sofic-from-not-hyperlinear`), and the frame claim holds
vacuously. So this route loses nothing, and its two premises fail in
different worlds: `thompson-f-is-not-sofic` fails if `F` is sofic (for example
amenable), and the frame claim fails if `F` is hyperlinear and nonsofic.

**Relation to nearby routes.** `thompson-f-not-sofic-from-not-hyperlinear` is
the trivial converse. `hyperlinear-implies-sofic-via-frame-extraction`
consumes the all-groups frame claim and pads by `Z`; this route consumes only
the frame claim at `F` and needs no padding.

**What it separates.** Every entropy-measure or counting tool delivers at most
the first premise. The second premise is where such a proof must stop being a
counting argument. See the entropy-measure attempt in
`thompson-f-is-not-hyperlinear` for where each tool dies.
