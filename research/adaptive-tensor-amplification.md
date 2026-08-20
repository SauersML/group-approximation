---
rg: 2
id: adaptive-tensor-amplification
kind: claim
title: Identity padding plus one tensor power converts operator separation to uniform 2-norm separation
distinct_from:
  mf-trace-gap-defect-ratio-models: That open claim seeks the sharper square-root dimension profile; this established lemma is elementary but pays a linear-in-dimension defect cost.
  weak-mf-embedding-not-reusable: That no-go says an arbitrary supplied MF embedding can be diluted; this lemma is a controlled post-processing statement and explicitly tracks the dimension cost.
artifacts:
  - research/artifacts/adaptive-tensor-amplification-2026-08-19.md
---

Let `z in U(d)` and `||z-1||_op >= delta`, with `0<delta<=2`.  Put

```text
z' = z directSum 1_d in U(2d).
```

Then there is one exponent

```text
p = ceil(8 d / delta^2)
```

such that

```text
||(z')^(tensor p)-1||_2 >= sqrt(2(1-e^-1)).
```

The same `p` works simultaneously for every unitary in a family having the
same operator-separation lower bound `delta` and the same dimension `d`.

Consequently, for a map `V:G->U(d)` with operator-norm multiplicative defect
`epsilon`, the single amplified map

```text
W(g)=(V(g) directSum 1_d)^(tensor p)
```

has defect at most `p epsilon` and converts every pair separated by `delta`
in operator norm into a pair separated by the displayed absolute constant in
normalized Hilbert--Schmidt norm.

The identity padding is essential to make the statement phase-safe: raw
tensor powers can return a scalar phase to `1`.
