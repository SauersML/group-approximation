---
rg: 2
id: isotropic-mixing-has-only-logistic-carrier-growth
kind: claim
title: Isotropic payload mixing yields only logistic carrier growth
distinct_from:
  independent-address-capacity-cannot-drive-selected-atom-growth: That counts disjoint tensor-independent address cylinders; this treats even an ideal depolarizing actuator family inside the whole marked sector.
  full-marked-sector-single-escape-is-direct-atom-collapse: That computes the universal escape statement at the terminal carrier Q-minus; this quantifies the degeneration continuously as any carrier approaches Q-minus.
---

Let `A<=Q<=H` and let `D<=H` have the same trace as `A`. Any overlap bound

```text
tr(QD)<=(1-eta)tr(A)+epsilon
```

forces the uniform hole

```text
tr(H-Q)>=eta tr(A)-epsilon.                            (IMG1)
```

Even an exact depolarizing actuator average on `H` gives only some actuator
with overlap at most `(tr(Q)/tr(H))tr(A)`. Its escape fraction therefore
vanishes as `Q` fills `H`. If `tr(A)>=gamma tr(Q)`, the ideal normalized
growth recurrence is

```text
x_(n+1)>=x_n+gamma x_n(1-x_n),       x_n=tr(Q_n)/tr(H),
```

which approaches capacity one and does not force a finite overshoot. Thus a
fixed escape fraction cannot follow from generic unitary mixing, a design, or
an expander estimate using only the three scalar dimensions.
