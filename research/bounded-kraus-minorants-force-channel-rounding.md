---
rg: 2
id: bounded-kraus-minorants-force-channel-rounding
kind: claim
title: Domination of a bounded-Kraus bistochastic channel forces uniform expectation rounding
distinct_from:
  identity-dominated-near-idempotent-channels-round: That requires a fixed CP component of the identity map; this permits any bistochastic minorant of uniformly bounded Kraus rank and bounds the limiting Kraus algebra by r divided by lambda.
  cp-reflection-near-idempotents-round-to-pinchings: That gives an explicit square-root rate for a CP reflection; this has no self-adjointness assumption, permits arbitrary bounded-Kraus minorants, and gives a qualitative modulus from Haar RMS defect.
artifacts:
  - research/artifacts/bounded-kraus-minorant-channel-rounding-2026-09-08.md
---

Fix `0<lambda<=1` and an integer `r>=1`. For every `epsilon>0`
there is `delta>0`, independent of matrix dimension, such that the
following holds. Let `P,Q:M_d->M_d` be bistochastic UCP maps with

```text
P-lambda Q completely positive,       Kraus_rank(Q)<=r,
zeta(P):=(integral_(U(d)) ||P^2(u)-P(u)||_2^2 du)^(1/2)<delta.
```

Then some unital subalgebra `A subset M_d` satisfies

```text
||P-E_A||_(infinity->2)<epsilon.
```

No self-adjointness is needed for either map. The conclusion controls
the entire operator unit ball in the original dimension. The proof
gives no quantitative modulus. Its limiting Kraus algebra has complex
dimension at most `floor(r/lambda)`.

Taking `Q=P` and `lambda=1` gives rounding for uniformly bounded
Kraus rank from Haar RMS defect, without self-adjointness. Taking
`Q=id` recovers the fixed identity-component case. Small mixed
`infinity->2` idempotence defect implies the required Haar bound.

The minorant hypothesis does not persist for canonical long-time
heats of an infinite group. For every bistochastic `Q` of Kraus rank
at most `r` with `P-lambda Q` CP, the exact inequality is

```text
lambda/sqrt(r)<=||R_P||_HS,
R_P=sum_i |a_i><a_i| on normalized L^2, for P(x)=sum_i a_i* x a_i.
```

The right side tends to zero for canonical long-time group heat.
Thus no fixed positive coefficient and fixed Kraus-rank bound can
apply there, even with minorants chosen separately in each matrix.
No general heat-rounding or nonhyperlinearity conclusion is claimed.

DERIVATION
finite-minorant-frames-extract-rounding-algebras
