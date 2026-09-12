---
rg: 2
id: odd-selector-priority-decoding
kind: claim
title: Odd selector parity admits lossless priority one-hot decoding regardless of overlap
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
distinct_from:
  odd-selector-overlap-rounding: that discards every joint atom carrying more than one active selector and therefore needs pairwise overlap to be small; this assigns every odd atom to its first active selector and loses no odd-parity mass.
  one-hot-selector-parity-barrier: that says parity equations cannot make the raw selector signs exactly one-hot; this shows exact one-hot signs are unnecessary for decoding because an orthogonal subpartition can be selected inside every odd sign pattern.
---

Let `Z_1,...,Z_m` be commuting self-adjoint involutions in a finite tracial
von Neumann algebra `(M,tau)`.  Put

```text
P_a = (1-Z_a)/2,
W   = product_a Z_a,
E   = (1-W)/2,
Q_a = E P_a product_(b<a) (1-P_b).
```

Then the `Q_a` are pairwise orthogonal projections satisfying

```text
Q_a <= E P_a,
sum_a Q_a = E,
tau(1-E) = (1/4) ||W+1||_2^2.                    (OPD1)
```

Thus every odd selector atom is assigned to its first active branch.  No
bound on the overlaps `tau(P_a P_b)` is required: the odd-parity corner is
partitioned completely even when many selectors are simultaneously active.

Consequently the projections `Q_a` meet exactly the hypotheses of
[[onehot-predicated-direct-sum-decoder]].  If branch copies `G_(a,i)` commute
with the selectors, the decoded operators

```text
U_i = sum_a Q_a G_(a,i)
```

are involutions in the corner `EME`, and every predicated equation selected
by branch `a` transfers to the decoded tuple with no selector-overlap loss.
Only the even-parity mass in `(OPD1)` is discarded.

This removes selector-overlap suppression from the ZPC-to-LCS compiler.  The
remaining quantitative issue is consistency between decoded copies belonging
to different local contexts.
