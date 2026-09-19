---
rg: 2
id: stw82-spectral-support-hall-capacity
kind: claim
title: Coupled covers obey spectral-support Hall capacity, not only amplitude capacity
artifacts:
  - research/artifacts/stw82-support-hall-capacity-audit-2026-08-30.md
distinct_from:
  stw82-tracial-capacity-bound-for-support-covers: that bounds the sum of the amplitudes `tau(h_v)`; this strengthens the exact bound to support projections and gives an approximate bound on every upper spectral cut.
  stw82-traces-block-unit-coupled-colour-reduction: that assumes every colour covers the whole unit; this detects the same obstruction inside the support of each outgoing colour.
---

Let `M` be a finite von Neumann algebra with a normal tracial state `tau`,
let `h_v in M` be positive contractions, and let `L_v` be subsets of
`{1,...,d}`.  Suppose positive contractions `c_(v,k) in M`, with
`c_(v,k)=0` for `k notin L_v`, satisfy

```text
(1-sum_k c_(v,k))h_v=0                              (H1)
```

and

```text
c_(v,k)c_(w,k)=0                         (v!=w).     (H2)
```

Writing `p_v=s(h_v)` for the support projection, every `S subseteq V`
obeys the noncommutative Hall inequality

```text
sum_(v in S) tau(p_v)
 <= |union_(v in S) L_v|.                            (H3)
```

More generally, if projections `q_k` satisfy `c_(v,k)<=q_k`, then the
right side of (H3) can be replaced by

```text
sum_(k in union_(v in S) L_v) tau(q_k).              (H4)
```

There is also an approximate spectral version.  If the left side of (H1)
has norm at most `eta`, and

```text
p_(v,lambda)=1_[lambda,1](h_v),       lambda>eta,
```

then

```text
(1-eta/lambda) sum_(v in S) tau(p_(v,lambda))
 <= |union_(v in S) L_v|,                            (H5)
```

with the same replacement (H4) when capacity projections are present.

Thus the scalar mass condition `sum_v tau(h_v)<=d` is not sufficient for
a `d`-label support-local cover.  Already in `M=C`, with `d=1` and

```text
h_I=h_Q=1/2,
```

the total amplitude is exactly one, but both support projections equal
one, so (H3) fails.  Indeed exact coverage forces both scalar cutters to
be one, contradicting (H2), and every orthogonal one-label pair has cover
defect at least `1/2` for one of the two supports.
