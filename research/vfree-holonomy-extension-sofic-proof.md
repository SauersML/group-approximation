---
rg: 2
id: vfree-holonomy-extension-sofic-proof
kind: route
title: Extract an amenable kernel and split over a finite-index free subgroup
target: finite-rank-holonomy-extensions-of-vfree-actors-are-sofic
requires: []
---

Regularity in `(VFH2)` makes `rho` extend to a trace-preserving embedding
of `L(Gamma)`. For `k in K`, `p(k)=e`, hence

```text
rho(k)=b_k in L^infinity(X) tensor M_n(C).               (VFP1)
```

Restricting the embedding gives

```text
L(K) -> L^infinity(X) tensor M_n(C).                     (VFP2)
```

The target is amenable. Every von Neumann subalgebra of a finite amenable
algebra is expected by the trace-preserving conditional expectation and is
amenable. Thus `L(K)` is amenable, and Connes's group-algebra criterion
gives that `K` is an amenable group.

Choose a normal finite-index free subgroup `F normal Q` and put
`Gamma_0=p^(-1)(F)`. The extension

```text
1 -> K -> Gamma_0 -> F -> 1                              (VFP3)
```

splits because a free group is projective: choose arbitrary lifts of a free
basis. Hence `Gamma_0=K semidirect F`. If `F=F_r` with free basis
`s_1,...,s_r`, then

```text
K semidirect F_r
 = (K semidirect_(s_1) Z) *_K ... *_K
   (K semidirect_(s_r) Z).                               (VFP4)
```

Each `K semidirect Z` is amenable, and amalgamated free products of sofic
groups over an amenable subgroup are sofic. Therefore `Gamma_0` is sofic.
Finally `Gamma_0 normal Gamma` has finite quotient `Q/F`; extensions of
a sofic normal subgroup by an amenable quotient are sofic. Thus `Gamma`
is sofic.

The same proof works for an infinite-rank free `F` by directed unions,
although the finitely generated virtually-free case needed by the source
has finite rank. The rank-zero case simply says `Gamma_0=K`.
