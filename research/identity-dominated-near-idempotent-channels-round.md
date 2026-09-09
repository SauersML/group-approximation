---
rg: 2
id: identity-dominated-near-idempotent-channels-round
kind: claim
title: A fixed completely positive identity component forces tracial expectation rounding
distinct_from:
  cp-reflection-near-idempotents-round-to-pinchings: The reflection theorem gives an explicit rate at identity weight one half; this allows any fixed positive weight and gives a qualitative modulus.
  ucp-factorizations-round-to-matrix-expectations: This extracts a finite source from an identity component; that theorem assumes a supplied approximate source factorization.
artifacts:
  - research/artifacts/identity-dominated-channel-rounding-2026-09-08.md
---

Fix `lambda>0`. For every `epsilon>0` there is `delta>0`, independent
of matrix dimension, with the following property. If `P:M_d->M_d`
is unital, trace-preserving and completely positive, `P-lambda id`
is completely positive, and

```text
||P^2-P||_(infinity->2) < delta,
```

then some unital matrix subalgebra `A` satisfies

```text
||P-E_A||_(infinity->2) < epsilon.
```

All traces are normalized. Self-adjointness of `P` is unnecessary.
The conclusion is in the original matrix dimension. The proof gives
no rate in `lambda` or `delta`.

In fact, it suffices to replace the mixed-norm defect hypothesis by
the weaker Haar root-mean-square bound

```text
(integral_(U(d)) ||P^2(u)-P(u)||_2^2 du)^(1/2) < delta.
```

The conclusion still controls the entire operator unit ball.

More precisely, the limiting Kraus algebra in a counterexample
ultraproduct would have complex dimension at most `floor(1/lambda)`.
Its finite matrix units can be lifted after a vanishing relative
dimension loss, with the remaining corner filled by the identity
channel.

The fixed positive identity component is an additional hypothesis.
For canonical long-time group heats even the largest allowable
identity component tends to zero. Thus this theorem does not prove
native heat rounding or nonhyperlinearity.

This is a written proof with manual review, not a new formal certificate.

DERIVATION
atomic-kraus-frames-extract-identity-dominated-rounding
