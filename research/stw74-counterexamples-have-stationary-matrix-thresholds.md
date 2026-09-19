---
rg: 2
id: stw74-counterexamples-have-stationary-matrix-thresholds
kind: claim
title: Every LXXIV counterexample has a spectral tower with a stationary matrix-projection threshold
distinct_from:
  stw74-counterexample-has-uniform-root-towers: that freezes a Cuntz root multiplicity; this freezes the least actual matrix level at which a hereditary projection appears and identifies every such projection with the unit class.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Let `A` be a counterexample to Problem LXXIV and `D` its full
projectionless hereditary corner.  For every `0!=a in D_+` there are
strictly decreasing positive numbers `epsilon_k` tending to zero, an integer
`m>=2`, and hereditary algebras

```text
H_k = Her_A((a-epsilon_k)_+),
H_k subset H_(k+1),
```

such that, after discarding finitely many terms,

```text
M_j(H_k) has no nonzero projection for 1<=j<m,
M_m(H_k) contains a nonzero projection q_k.                  (T)
```

Every nonzero projection in the second line of `(T)` is properly infinite
and has the same Cuntz class as `1_A`; equivalently it is Murray--von
Neumann equivalent to `1_A` after stabilization.

Hence a counterexample has a locally stationary finite matrix obstruction:
projection return succeeds at one fixed level `m`, uniformly along a
rapidly increasing spectral tower, but fails at every smaller level.  The
universal hinge is precisely descent from such an `m>=2` to level one.
