---
rg: 2
id: odd-selector-overlap-rounding
kind: claim
title: Pairwise selector overlap quantitatively rounds commuting selectors to one-hot sectors
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
distinct_from:
  one-hot-selector-parity-barrier: that proves parity equations cannot enforce the exact one-hot set; this proves that odd-parity plus small pairwise overlap is already quantitatively close to one-hot, so exact enforcement is unnecessary.
  finite-group-selector-induction-barrier: that rules out pruning invalid selector characters with a standalone finite group gadget; this is a metric rounding theorem once overlap has been made small by any mechanism.
---

Let `Z_1,...,Z_m` be commuting self-adjoint involutions in a finite tracial
von Neumann algebra `(M,tau)`. Put

```text
P_a = (1-Z_a)/2,
W   = product_a Z_a,
Q_a = P_a product_(b!=a)(1-P_b),
Q   = sum_a Q_a,
S   = sum_(a<b) tau(P_a P_b).
```

Then the `Q_a` are pairwise orthogonal projections and

```text
tau(1-Q) <= (1/4)||W+1||_2^2 + S,
sum_a ||P_a-Q_a||_2^2 <= 2S.
```

If `W=-1` exactly, then the first estimate improves to

```text
tau(1-Q) <= S/3.
```

Thus an approximately odd selector family with vanishing pairwise overlap has
a one-hot corner of trace tending to one, with constants independent of matrix
dimension and of any representation-theoretic classification of the selector
gadget.
