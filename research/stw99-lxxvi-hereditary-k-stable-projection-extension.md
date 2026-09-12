---
rg: 2
id: stw99-lxxvi-hereditary-k-stable-projection-extension
kind: claim
title: Hereditary K-stability gives exact strict relative projection-source embeddings without real rank zero
distinct_from:
  stw99-lxxvi-rr0-relative-strict-positive-embedding: This removes real rank zero for projection sources under explicit hereditary K-stability, but does not assert arbitrary positive-source extension.
artifacts:
  - research/artifacts/stw99-lxxvi-hereditary-k-stability-and-cutoff-restriction-2026-09-05.md
---

Let D be separable, simple, stably finite, and of stable rank one.
Assume every nonzero hereditary subalgebra of B=D tensor K is
K-stable through the actual unitary stabilization maps in all degrees,
including components. Real rank zero and purity are not assumed.

For a projection p in B and d in B_+ with [p]<[d], the norm-topological
frame space

```text
E(p,d)={v in closure(dB):v*v=p}
```

is nonempty and weakly contractible.

Consequently, let X be finite-dimensional compact metrizable, Y closed,
p in C(X,B) a projection, and d in C(X,B)_+. Assume [p(x)]<=[d(x)]
everywhere, with strict inequality off Y whenever p(x) is nonzero.
Every continuous prescribed frame v_Y on Y, with v_Y*v_Y=p|Y and
v_Y(y) in closure(d(y)B), extends to such a frame over X. The resulting
global frame belongs to closure(d C(X,B)), so p<=_Cu d.

This applies, for example, to the non-RR0 coefficient Z. It does not
prove the corresponding theorem for arbitrary positive sources.
The proof is internally reviewed.

ROUTES

stw99-lxxvi-hereditary-k-stable-projection-extension-proof
