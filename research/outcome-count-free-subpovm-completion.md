---
rg: 2
id: outcome-count-free-subpovm-completion
kind: claim
title: A finite sub-POVM completes to a PVM with linear deficit and no outcome-count loss
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
distinct_from:
  target-packet-synchronization: that rounds a supplied approximate packet in a game strategy; this gives an explicit sub-POVM completion estimate and preserves prescribed coarse blocks.
  finite-clock-fejer-threshold-is-sharp: that studies return mass for one clock; this simultaneously rounds all compressed spectral effects without paying their number.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial von Neumann algebra and

```text
0<=a_j<=1,             s=sum_j a_j<=1.
```

Put

```text
mu=tau(1-s),           eta=sum_j tau(a_j-a_j^2).
```

There is an `m`-outcome PVM `(q_j)` in `M` satisfying

```text
sum_j ||a_j-q_j||_2^2 <=11mu+9eta.                    (SPC1)
```

The constant is independent of `m`.

The completion is block preserving.  If `(p_k)` is a coarse PVM, the fine
indices are partitioned into sets `Lambda_k`, and

```text
a_j<=p_k                  for j in Lambda_k,
sum_(j in Lambda_k)a_j<=p_k,
```

then `(q_j)` can be chosen with

```text
q_j<=p_k,
sum_(j in Lambda_k)q_j=p_k,                           (SPC2)
```

and `(SPC1)` holds after summing the corresponding blockwise missing-mass
and purity deficits.  Thus a group packet may output fuzzy fine effects in
authenticated coarse sectors; it need not manufacture an exact fine PVM.

