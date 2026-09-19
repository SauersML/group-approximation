---
rg: 2
id: low-odd-square-removes-pairwise-green-stationarity
kind: claim
title: Low odd square removes pairwise finite-Green stationarity exactly
distinct_from:
  clifford-packets-are-stationary-for-intrinsic-green-step: that exhibits the endpoint `R=I` where the skew descent signal vanishes; this computes the full interpolation and proves uniform coercivity away from that endpoint.
  one-anchor-grading-makes-parity-damage-quadratic: that expands parity and commutator words in even/odd pieces; this gives an exact functional-calculus identity for the intrinsic square-commutator residual.
  regularized-anchor-cut-makes-residual-spikes-boundary-heavy: that makes residual high spectral pieces pay boundary; this proves why removing those pieces restores the local descent signal.
---

ESTABLISHED.  Let `A,B` be reflections, put `U=AB`, and define

```text
 R=((B-ABA)/2)^2=(2-U^2-U^(-2))/4,
 beta=(I-U^2)/2,
 omega=(beta-beta^*)/2=(U^(-2)-U^2)/4.                (LOS1)
```

Then `R` and `omega` are commuting Laurent functions of `U`, and

```text
 omega^*omega=R(I-R).                                  (LOS2)
```

Consequently, on any reducing block where `R<=sI` with `s<1`,

```text
 omega^*omega >=(1-s)R,
 ||omega||_2^2 >=(1-s)||[A,B]||_2^2/4.                (LOS3)
```

Thus a pair cannot be stationary for the intrinsic skew correction in the
pointwise low-odd-square sector.  Clifford stationarity is exactly the
opposite endpoint `R=I`, where `(LOS2)` vanishes.

For a whole tuple, if every retained compressed pair satisfies
`R_(a,i)<=sI`, summing `(LOS3)` gives a uniform edge-level descent signal.
The remaining coercivity problem is whether the oriented edge signals
`omega_(a,i)` cancel in the normalized divergences `c_a`.
`ordinary-green-triangle-curl-has-a-linear-code-tangent` shows that the
ordinary triangle curl need not be quadratic even here.  Its linear part
must be charged by the balanced parity/equality syndrome (or treated in the
support-weighted code complex).  Hence the final low-sector PL target is a
parity-charged curl estimate, not a local spectral or endpoint-Riesz
estimate.

The regularized aggregate cut gives only an averaged operator bound and can
leave individual high `R_(a,i)` spikes.  Those are precisely the residual
cuts shown boundary-heavy by
`regularized-anchor-cut-makes-residual-spikes-boundary-heavy`; they must be
peeled or charged before applying `(LOS3)` globally.
