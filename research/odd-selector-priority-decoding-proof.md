---
rg: 2
id: odd-selector-priority-decoding-proof
kind: route
title: Assign each odd joint spectral atom to its least active selector
target: odd-selector-priority-decoding
requires: [onehot-predicated-direct-sum-decoder]
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
---

All `P_a`, `W`, and `E` commute.  On a joint spectral atom of the `P_a`, let

```text
S = {a : P_a=1}.
```

There `W=(-1)^|S|` and hence `E=1` exactly when `|S|` is odd.  If `E=1`, the
set `S` is nonempty and exactly one of the projections

```text
P_a product_(b<a)(1-P_b)
```

is one: the one indexed by `min S`.  If `E=0`, every `Q_a` is zero.  Therefore
the `Q_a` are pairwise orthogonal, `Q_a<=EP_a`, and their sum is `E`.

Since `W` is a self-adjoint involution,

```text
(W+1)^*(W+1) = (W+1)^2 = 2(1+W) = 4(1-E).
```

Taking the trace gives the last identity in `(OPD1)`.

Finally, the direct-sum conclusion does not require the unused selectors to
be cold.  It uses only orthogonality of the `Q_a`, the containment `Q_a<=P_a`
(equivalently `Q_a Z_a=-Q_a`), and commutation of branch copies with the
selectors.  These are precisely the hypotheses established above, so
[[onehot-predicated-direct-sum-decoder]] applies on `EME` without an overlap
term.
