---
rg: 2
id: property-t-free-spectator-overlap-proof
kind: route
title: Tensor a local Reynolds range with congruence Steinberg representations
target: property-t-free-spectator-erases-old-commutant-overlap
requires: []
---

The packet Reynolds projection acts only on `End(K)`, so after tensoring its
range is `R_K tensor End(V_p)` and has normalized rank `delta`.
Irreducibility of `sigma_p` and Schur's lemma give

```text
End(H_p)^Lambda=End(K) tensor C I_(V_p).
```

Its intersection with the local range is
`R_K tensor C I_(V_p)`, of rank `rank(R_K)`.  Division by
`dim(K)^2 p^2` proves `(PFS1)`.

Selberg's congruence spectral gap, equivalently property `tau` for this
family of finite quotients, applies to every nontrivial constituent of the
adjoint representation.  Since the only invariant constituent is the
scalar line just computed, it gives one uniform gap on its orthogonal
complement.  No property `(T)` assertion is used.

