---
rg: 2
id: stw10-kazhdan-trace-rigidity-citation
kind: route
title: Apply Kirchberg--Brown rigidity to amenable trace models
target: stw10-kazhdan-full-group-traces-are-qd
requires: []
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Nathanial P. Brown, *Invariant means and finite representation theory of
C-star-algebras*, Memoirs of the American Mathematical Society 184 (2006),
no. 865, Proposition 4.1.12, proves for a countable Kazhdan group `Gamma`
that

```text
AT(C*(Gamma)) = AT(C*(Gamma))_LFD.
```

Here the left side is the set of amenable traces and the right side consists
of the locally finite-dimensional amenable traces.  The key input is
Brown's Lemma 4.1.11, which is Kirchberg's property-`(T)` rigidity lemma:
Hilbert--Schmidt asymptotically multiplicative u.c.p. models can be replaced,
without changing their limiting traces, by genuine finite-dimensional
representations.

Thus an amenable trace `tau` is a pointwise limit of normalized traces
composed with finite-dimensional star-representations of `C*(Gamma)`.
Those representations are u.c.p. maps with identically zero operator-norm
multiplicative defect, and hence witness that `tau` is quasidiagonal.  This
is exactly the target claim.  The cited result is also recorded as a typed
literature input in
`GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean`.

