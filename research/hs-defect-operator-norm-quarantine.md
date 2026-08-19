---
rg: 2
id: hs-defect-operator-norm-quarantine
kind: claim
title: A finite family of HS-small defects is operator-norm small off a small-trace corner
distinct_from:
  small-trace-rank-one-quarantine: That controls the block boundary and gap after a small-trace projection has been identified; this constructs a small-trace spectral projection from a finite family of HS-small matrices and controls those matrices in operator norm on its complement.
  coordinate-ultraproduct-transport: That requires an operator-norm asymptotic representation; this gives only two-sided operator-norm control of a prescribed finite defect family on a large projection, with no invariance of that projection and hence no compressed representation by itself.
---

Let `(M_d,tau)` have normalized trace and let `D_1,...,D_N in M_d`.  Put

```text
E = sum_(i=1)^N ||D_i||_2^2.
```

For every `eta>0` there is a projection `q` such that

```text
tau(1-q) <= 2 E / eta^2
```

and, for every `i`,

```text
||D_i q||_op <= eta,
||q D_i||_op <= eta,
||q D_i q||_op <= eta.
```

In particular, if a fixed finite packet of `N` multiplicative defects of a
normalized-HS almost-representation each has `||D_i||_2<=delta`, then one may
choose

```text
tau(1-q) <= 2 N delta^2 / eta^2.
```

Taking, for example, `eta=sqrt(delta)` makes the discarded trace `O(N delta)`
and all listed restrictions `O(sqrt(delta))` in operator norm.

This is only a **defect quarantine**.  It does not assert that `q` is almost
invariant under the model unitaries.  Consequently the compressed maps
`q phi(g) q` need not be almost unitary, and

```text
q phi(g) q phi(h) q - q phi(gh) q
```

contains the leakage term `q phi(g)(1-q)phi(h)q`, which the displayed defect
bounds do not control in operator norm.  Any route from this lemma toward
`hs-one-level-expander-block-decomposition` must solve that invariance/leakage
problem rather than silently dropping it.
