---
rg: 2
id: agent-aggregate-escape-faithful-extension-kernel-proof
kind: route
title: Restrict the extended representation back to each original context
target: agent-aggregate-escape-faithful-extension-keeps-affine-ghosts
requires:
  - non-ce-trace-does-not-promote-to-subgroup-character-gap
  - locally-affine-support-bcs-is-exactly-the-lcs-boundary
---

For `h in H_c`, injectivity of `iota` and the identity

```text
Theta(iota(h))=theta(h)
```

give `Theta(iota(h))=1` if and only if `theta(h)=1`, proving `(FEG2)`.
If `N<=ker(Theta)`, then `iota^(-1)(N)<=ker(theta)`, which gives `(FEG4)`.

For a finite abelian context, the common level set of all characters which
are constant on `S_c` is its affine hull.  Equivalently, the annihilator of
the difference span `S_c-S_c` is `ker(theta) intersect H_c`, and taking the
double annihilator gives `(FEG3)`.  The claims about wagon-wheel embeddings
and multiplicative restrictions of ucp maps are immediate applications.
