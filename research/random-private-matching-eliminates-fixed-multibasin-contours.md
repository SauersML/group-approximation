---
rg: 2
id: random-private-matching-eliminates-fixed-multibasin-contours
kind: claim
title: A private matching can avoid every bounded multi-basin contour while retaining the Weyl gap
distinct_from:
  private-matching-free-product-separates-pauli-signs: that proves the mixed graph alone is a sign-separated matching; this controls contours created after the bounded-degree same-basis incidence is added.
  equality-synchronized-lifts-create-two-pair-contours: that diagnoses short contours for reused mixed fibers; this uses private degree-one matching and chooses it to avoid all bounded alternating returns.
  relative-c-sixth-pauli-incidence-labeling: that asks for a global relative small-cancellation placement; this proves only fixed-radius contour avoidance.
---

Let `G_X,G_Z` be the bounded-degree Gaifman graphs of the X and Z occurrence
systems, each on `N` vertices.  For every fixed radius `g`, there is a perfect
matching `pi:X->Z` such that no distinct `x,x'` satisfy simultaneously

```text
dist_X(x,x')<=g,       dist_Z(pi(x),pi(x'))<=g.             (RPM1)
```

Consequently the combined incidence has no closed contour of length at most
`g` using two or more private mixed edges.

For a uniform random permutation, index a bad event by a near pair in X and
a near pair in Z, asking that the former map to the latter.  There are
`O_(Delta,g)(N^2)` events, each of probability `2/(N(N-1))`, and each event
has only `O_(Delta,g)(N)` lopsidependencies.  The permutation Lovasz local
lemma applies for large `N`.  Its standard product lower bound gives

```text
P(no bad event)>=c_(Delta,g)>0,                             (RPM2)
```

because the sum of the local-lemma charges is `O_(Delta,g)(1)`.  The bad
probability for the repeated-LDPC private Weyl energy is `exp(-Omega(N))`.
Thus, for all large `N`, one matching simultaneously satisfies `(RPM1)` and
the Weyl dimension gap.  Finite search makes the joint choice recursive.

This resolves every fixed collection of threshold rectangles or bounded
multi-basin diagrams.  It does not establish relative `Gr'(1/6)` for
unbounded contours: a long relation can still share a long section or carry
nontrivial holonomy through many basins.  That residual is
`sign-safe-unbounded-multibasin-placement`.
