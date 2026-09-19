---
rg: 2
id: finite-index-ce-invariance-proof
kind: route
title: Embed the finite-index extension in an endomorphism corner over the subfactor
target: finite-index-extensions-preserve-connes-embeddability
requires: []
---

If `M` is Connes embeddable, then so is its von Neumann subalgebra `N`.

Conversely, finite Jones index makes `L^2(M)` a finitely generated projective
right `N`-module.  Hence for some finite `r` and projection `p in M_r(N)`,

```text
End_N(L^2(M)_N) isomorphic_to p M_r(N) p.
```

Left multiplication is a faithful normal unital representation

```text
M -> End_N(L^2(M)_N).
```

If `N` embeds in `R^omega`, then matrix amplification, positive corners, and
von Neumann subalgebras of the amplification also embed in `R^omega` (after
the standard trace normalization on the corner).  Therefore `M` is CE.

The same argument applies to the finite-index extensions associated to
finite Q-systems.  It proves permanence only; it supplies no group-like
orthonormal basis and no canonical group trace.

