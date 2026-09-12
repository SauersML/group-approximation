---
rg: 2
id: stw40-minimal-affine-trace-flow-extracts-boundary-proof
kind: route
title: Extract a minimal strongly proximal extreme boundary from the trace simplex
target: stw40-trace-simplex-contains-a-nontrivial-boundary
requires:
  - amenable-action-invariant-trace-forces-amenability
artifacts:
  - research/artifacts/stw40-trace-boundary-extraction-audit-2026-08-30.md
---

The established invariant-trace obstruction says that the affine action on
`T(A)` has no fixed point.

## 1. A minimal affine subsystem

Among the nonempty compact convex invariant subsets of `T(A)`, choose a
minimal one `C`.  It exists by the usual nested-intersection argument and
Zorn's lemma.  Let

```text
X=closure(ext(C)).
```

Krein--Milman makes `X` nonempty, and affine homeomorphisms preserve extreme
points, so `X` is compact and invariant.

We use the following elementary extreme-point observation twice:

```text
If S is compact in a compact convex set D and
D=closed convex hull(S), then ext(D) is contained in S.       (E)
```

Indeed, approximate `x in ext(D)` by finite convex combinations of points
of `S`.  The associated finitely supported probability measures have a
convergent subnet in `Prob(S)`; its limit represents `x`.  An extreme point
has only its point mass as a representing probability measure.  To see the
last assertion directly, if a representing measure is not concentrated at
`x`, choose a continuous affine function separating `x` from a positive-mass
part of its support and split the measure across a suitable level set.  The
two conditional barycenters give a nontrivial convex decomposition of `x`.

If `Y` is a nonempty closed invariant subset of `X`, then
`closed convex hull(Y)` is a nonempty compact convex invariant subset of
`C`, hence equals `C`.  Observation `(E)` gives `ext(C) subset Y`, and
therefore `X subset Y`.  Thus `X` is minimal.

## 2. Strong proximality

Take any probability measure `mu` on `X`, and let `b in C` be its barycenter.
Minimality of `C` implies

```text
C=closed convex hull(G b).                                  (1)
```

Fix `x in ext(C)`.  Approximate `x` by finite convex combinations
`sum_i t_i g_i b`.  Apply the same combinations to `mu`:

```text
nu=sum_i t_i (g_i mu).
```

The barycenters of these measures converge to `x`.  Compactness of
`Prob(X)` gives a convergent subnet, and its limit represents `x`; by
extremality it is `delta_x`.  Hence

```text
delta_x in closed convex hull(G mu).                        (2)
```

Put `S=closure(G mu)` inside `Prob(X)`.  The point mass `delta_x` is extreme
in `Prob(X)`, hence also extreme in `closed convex hull(S)`.  Applying
observation `(E)` in `Prob(X)` to `(2)` gives `delta_x in S`.  Thus the orbit
closure of every probability measure on `X` contains a point mass.  This is
strong proximality.

If `X` were a singleton, its unique trace would be fixed by `G`, contrary to
`amenable-action-invariant-trace-forces-amenability`.  Therefore the extracted
boundary is nontrivial.
