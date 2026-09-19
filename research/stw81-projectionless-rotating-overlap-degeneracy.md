---
rg: 2
id: stw81-projectionless-rotating-overlap-degeneracy
kind: claim
title: Near-unital rotating two-colour overlaps degenerate in a projectionless fibre
distinct_from:
  stw81-stationary-two-colour-interval-patching-forces-af: that theorem uses the same fibre frame on both base patches and a combinatorial two-by-two colouring argument; the present theorem permits two completely unrelated, independently rotated frames and uses only near-unitality plus the matched cross-orthogonality forced on their overlap.
  stw82-complementary-cutdowns-merge-iff-near-projections: that theorem characterizes when one prescribed complementary pair can be perturbed to an orthogonal pair; the present theorem extracts approximate projections from two different near-partitions whose corresponding terms are already orthogonal.
artifacts:
  - research/artifacts/stw81-projectionless-rotating-overlap-audit-2026-08-30.md
---

Let `D` be a unital C-star algebra and let

```text
h_0,h_1,k_0,k_1 in D_+
```

be contractions such that

```text
h_0+h_1<=1,                 k_0+k_1<=1,
norm(1-h_0-h_1)<=epsilon,   norm(1-k_0-k_1)<=epsilon,
h_0 k_0=0,                  h_1 k_1=0.                 (RTO1)
```

Then every support is a `2epsilon`-almost projection:

```text
max_i(
  norm(h_i-h_i^2),
  norm(k_i-k_i^2)
) <= 2epsilon.                                      (RTO2)
```

Suppose moreover that `D` is projectionless, meaning that its only
projections are zero and one, and that `epsilon<1/8`.  Put

```text
alpha(epsilon)=(1-sqrt(1-8epsilon))/2.
```

For each of the two frames, one support has norm at most
`alpha(epsilon)` and the other is within `alpha(epsilon)+epsilon` of the
unit.  In particular, as `epsilon` tends to zero, each near-unital
two-colour frame in (RTO1) degenerates uniformly to one colour.  The two
frames may be unrelated and may be obtained from each other by arbitrary
unitary rotations.

Consequently let `D` be separable, unital, and projectionless.  Suppose
that on every finite set and at every tolerance one has two ordinary
piecewise-c.p.c. two-colour factorizations for `D`, each approximating the
unit, such that,
after possibly interchanging the labels of the second frame, corresponding
return colours have orthogonal ranges.  If the first factorization
approximates the prescribed finite set, then `D` is AF: after rescaling the
two returned unit pieces to a subunital near-partition, discard the return
colour whose composition has vanishing norm to obtain a one-colour
approximation.

This rules out the natural rotating-frame repair of stationary scalar
interval patching for

```text
C([0,1]) tensor Z.                                    (RTO3)
```

Indeed, at a point where two scalar base cutoffs are both nonzero, order
zero of each reused global colour makes the corresponding fibre supports
orthogonal.  If both local fibre factorizations separately approximate the
unit, the theorem would make `Z` AF.  No contractivity of the sum of the two
return colours is assumed.  Thus a successful two-colour proof must escape
at least one of the remaining hypotheses: local frames cannot each return
the unit on the overlap, outgoing colours must be split before reuse, or the
approximation must couple the base patches through genuinely nonlocal
incoming data.  Merely rotating the two fibre frames, even by the strong
self-absorption homotopies of `Z`, does not suffice.

DERIVATION
[[stw81-cross-orthogonal-near-partitions-force-projections]]
