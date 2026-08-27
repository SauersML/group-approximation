---
rg: 2
id: dimension-defect-controlled-mf-hyperlinear
kind: claim
title: MF models whose defect beats inverse dimension are hyperlinear
distinct_from:
  mf-implies-hyperlinear: This is a strict sufficient condition on a selectable family of MF models, not a proof that arbitrary MF groups possess such a family.
  mf-trace-gap-defect-ratio-models: That open profile only requires epsilon squared to beat the trace gap and is quantitatively stronger; this criterion assumes the simpler but stronger rate d epsilon -> 0.
artifacts:
  - research/artifacts/adaptive-tensor-amplification-2026-08-19.md
---

Let `G` be countable.  Suppose that along an exhaustion by finite windows it
has operator-norm approximate unitary models

```text
V_n:G->U(d_n)
```

with a fixed positive operator-separation constant on each window,
multiplicative defects `epsilon_n -> 0`, and

```text
d_n epsilon_n -> 0.
```

Then `G` is hyperlinear.

For the normalized MF convention with separation constant `1`, apply
`adaptive-tensor-amplification` with `delta=1`.  The amplified defects are at
most `(8d_n+1)epsilon_n -> 0`, while all distinct pairs in the finite window
have normalized Hilbert--Schmidt separation at least
`sqrt(2(1-e^-1))`.

This gives an elementary phase-safe bridge from a dimension-sensitive MF
profile to hyperlinearity.  It does not solve `mf-implies-hyperlinear` because
the MF definition supplies no relation between requested error and the
matrix dimension needed to achieve it.
