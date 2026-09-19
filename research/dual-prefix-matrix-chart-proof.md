---
rg: 2
id: dual-prefix-matrix-chart-proof
kind: route
title: Cancel dual prefixes to invert the iterated Leavitt matrix chart
target: iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
---

Iterate the two Leavitt identities.  Equal reversed prefixes cancel from the
inside out, a first mismatch gives zero, and the depth-`n` range projections
sum to the active identity.  Substitution into

```text
Phi_n(r)_(u,v)=t_u r s_v,
Psi_n(M)=sum_(u,v)s_u M_(u,v)t_v
```

shows both composites are identities.  Applying the same cancellation to
`s_ut_v` gives the standard matrix-unit multiplication table and sends each
prefix corner to the corresponding elementary matrix.
