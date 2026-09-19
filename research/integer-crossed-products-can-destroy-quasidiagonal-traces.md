---
rg: 2
id: integer-crossed-products-can-destroy-quasidiagonal-traces
kind: claim
title: An integer crossed product can turn a quasidiagonal invariant trace into an amenable nonquasidiagonal trace
distinct_from:
  stw10-finite-crossed-products-preserve-amenable-and-qd-traces: finite acting groups preserve both trace properties; this proves that the quasidiagonal half fails for the first infinite amenable acting group.
  mf-not-closed-under-integer-extensions: that is a group-level operator-norm MF nonpermanence statement; this identifies the sharper trace phenomenon, including quasidiagonality of the invariant base trace and amenability of the induced crossed-product trace.
artifacts:
  - research/artifacts/amenable-crossed-product-trace-dichotomy-2026-08-30.md
---

There exist a separable unital C-star algebra `A`, an automorphism
`alpha in Aut(A)`, and an `alpha`-invariant quasidiagonal trace `tau`
such that the canonical trace

```text
sigma=tau compose E
```

on `A rtimes_alpha Z` is amenable but is not quasidiagonal.

One may take `A=C*_(max)(K)`, where `K` is the locally residually finite
telescope core of the explicit literal group, and
`A rtimes_alpha Z=C*_(max)(E)`, where `E` is the explicit finitely
presented sofic non-MF group.  Since `Z` is amenable, maximal and reduced
crossed products agree here.  Thus the failure is not an ambiguity between
crossed-product completions.
