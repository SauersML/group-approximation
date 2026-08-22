---
rg: 2
id: non-ce-group-factor-corner-proof
kind: route
title: Restrict a hypothetical Connes embedding to the positive corner
target: nonce-factor-in-group-factor-corner-forces-nonhyperlinear
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
---

If `G` were hyperlinear, `L(G)` would admit a trace-preserving embedding into
`R^omega`.  Connes embeddability passes to nonzero corners, so the normalized
corner `pL(G)p` would be Connes embeddable.  Composing its embedding with
`Phi` in `(NGC1)` would give a trace-preserving embedding of `(M,tau_M)`, a
contradiction.

For the finite-subgroup specialization, orthogonality of the canonical group
basis gives

```text
tau_G(p_K)=|K|^-1.
```

