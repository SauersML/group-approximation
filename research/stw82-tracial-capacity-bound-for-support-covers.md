---
rg: 2
id: stw82-tracial-capacity-bound-for-support-covers
kind: claim
title: Traces impose a fractional capacity bound on support-local colour covers
artifacts:
  - research/artifacts/stw82-order-zero-spectral-subdivision-audit-2026-08-30.md
distinct_from:
  stw82-traces-block-unit-coupled-colour-reduction: that treats full-unit partitions and gives the integral bound on the number of original colours; this weights each colour by the trace of its actual order-zero support.
  stw82-support-local-coupled-covers-merge-colours: that proves sufficiency of a support-local cover for merging; this gives a necessary tracial capacity inequality for such a cover.
---

Let `B` be a unital C*-algebra with tracial state `tau`.  Let `h_v` be
positive contractions indexed by a finite set `V`.  Suppose positive
contractions `c_(v,k) in B`, for `k=1,...,d`, satisfy

```text
c_(v,k)c_(w,k)=0                         (v!=w)        (T1)
```

and, with `s_v=sum_k c_(v,k)`,

```text
norm((1-s_v)h_v)<=eta                    (v in V).     (T2)
```

Then

```text
sum_(v in V) tau(h_v) <= d+|V| eta.                    (T3)
```

In particular, an exact support-local cover (`eta=0`) by `d` labels can
exist only when the total tracial mass of the outgoing supports is at most
`d`.  For full-unit supports `h_v=1`, this recovers `|V|<=d`; for genuinely
complementary ideal--quotient supports it permits colour reuse whenever
their combined mass, rather than their raw count, fits the available label
capacity.
