---
rg: 2
id: mf-thresholds-rescale-under-matrix-amplification
kind: claim
title: The MF thresholds of a matrix ring are those of the ring rescaled by the matrix size, so their finiteness is stable but their values are not
artifacts:
  - research/artifacts/un-open-2-mf-spectrum-2026-09-13.md
---

Let `R` be a countable unital ring with `1 != 0`, and let `mf(R)` and `rig(R)` be the MF thresholds of
`mf-rigidity-is-monotone-in-matrix-rank`.

**Lemma.** For `N >= 2` and `m >= 1`, `EL_N(M_m(R)) = EL_(Nm)(R)` under `M_N(M_m(R)) = M_(Nm)(R)`.

**Theorem.** For every `m >= 1`,

```text
rig(M_m(R)) = max(2, ceil(rig(R)/m)),
mf(M_m(R))  = floor(mf(R)/m)  when that is at least 2, and 1 otherwise,
```

with `ceil(infinity) = floor(infinity) = infinity`.

**Corollary.** `rig(R) < infinity` if and only if `rig(M_m(R)) < infinity`, and `mf(R) = infinity` if and
only if `mf(M_m(R)) = infinity`. The two dichotomy conditions are stable under matrix amplification while
the thresholds themselves are not: they rescale by `ceil(./m)` and `floor(./m)`.

This separates two kinds of question in the UN program. Finiteness of `rig` is a coarse condition, and for
simple `R` it is implied by the Morita-invariant condition that `V(R)` carries no nonzero state
(`simple-ring-stably-finite-iff-unit-not-paradoxical`, plus
`stably-infinite-ring-elementary-groups-have-no-mf-quotient`); a state nonzero anywhere on `V(R)` is nonzero
at `[R]` because every nonzero element of `V(R)` is full when `R` is simple. The value of `rig` is not of
that kind: it moves under `R |-> M_m(R)`, so no argument about the ordered monoid `V(-)` alone can compute
it. Lane `un-low-rank-band`'s target `EL_3(L_k(3,4))` is the computation of such a value.

**Review (un-verify, 2026-09-13): PASS.** The block identity `EL_N(M_m(R)) = EL_{Nm}(R)` (as in part 3 §1), both rescaling formulas via the monotone thresholds, the finiteness corollary and the state-space remark (`[e] ≤ j[1]` gives `ν([1]) > 0`) re-derived. See `research/artifacts/un-review-2026-09-13-part5.md` §2.
