---
rg: 2
id: stw40-haar-average-equicontinuous-trace-island-proof
kind: route
title: Close an equicontinuous trace island to a compact group and Haar-average its orbit
target: stw40-trace-action-has-no-equicontinuous-island
requires:
  - amenable-action-invariant-trace-forces-amenability
artifacts:
  - research/artifacts/stw40-trace-equicontinuity-obstruction-audit-2026-08-30.md
---

Assume that `K` is a nonempty weak-star compact invariant subset of `T(A)`
and that the restricted `G`-action is equicontinuous.  Separability of `A`
makes `K` compact metrizable.  Choose a compatible metric.

Let `H` be the uniform closure in `C(K,K)` of the homeomorphisms induced by
`G`.  Equicontinuity and compactness give compactness of `H` by
Arzela--Ascoli.  The inverse family is the same `G`-family and is therefore
equicontinuous too.  If a net `g_i` converges uniformly to `h`, pass to a
subnet on which `g_i^(-1)` converges uniformly to `k`.  Taking limits in

```text
g_i g_i^(-1)=g_i^(-1) g_i=id_K
```

gives `hk=kh=id_K`.  Hence every element of `H` is a homeomorphism, and the
uniform closure is a compact topological group.

Fix `tau_0 in K`, let `m_H` be normalized Haar measure on `H`, and push it
forward under the continuous orbit map

```text
h |-> h tau_0.
```

This gives a `G`-invariant Borel probability measure `mu` on `K`.  Its
barycenter

```text
bar_tau(a)=integral_K sigma(a) d mu(sigma)
```

is a tracial state on `A`.  Since the action on traces is affine and `mu`
is invariant, `bar_tau` is `G`-invariant.

The established theorem
`amenable-action-invariant-trace-forces-amenability` now makes `G`
amenable, contrary to the hypothesis.  Therefore `K` cannot exist.

A finite orbit and an action factoring through a compact group are
equicontinuous, giving the first two consequences.  The negation of
equicontinuity on a compact metric space is precisely the third: for some
`epsilon>0`, arbitrarily close traces are separated by at least `epsilon`
under suitable group elements.
