---
rg: 2
id: invertible-difference-modules-are-not-permutation-submodules
kind: claim
title: Inside a restricted permutation module, a subspace on which alpha minus one is invertible has locally finite alpha-orbits
distinct_from:
  augmentation-lamp-finite-presentation-criterion: that is a finite-presentation criterion for index-two lamp subgroups over a 2-transitive actor; this is a linear-algebra obstruction to placing a module inside any permutation module, with no finiteness hypothesis on the actor.
artifacts:
  - research/artifacts/solve-bh-apapa-2026-09-13.md
---

**ESTABLISHED** by `invertible-difference-permutation-module-proof`. Elementary;
no priority is claimed.

**Statement.** Let `K` be a field, `Omega` a set, `alpha` a permutation of
`Omega`, and `K[Omega]` the space of finitely supported functions
`Omega -> K`, with `alpha` acting by `(alpha v)(x) = v(alpha^-1 x)`. Let
`V <= K[Omega]` be an `alpha`-invariant subspace such that `alpha - 1` maps `V`
onto `V` injectively. Then for every `v in V` the span of
`{alpha^m v : m in Z}` is finite-dimensional, and `alpha` has finite order on it
when `K` is finite.

**Consequence used later.** An abelian group `T` of exponent `p` carrying commuting
automorphisms `a, a'` with `a' = a - 1` on `T`, and an element whose
`a`-orbit spans an infinite-dimensional subspace, can never be placed
equivariantly inside a restricted permutation module over `F_p`, whatever the
set and the permutations. See `kms-configuration-modules-avoid-abelian-lamp-bases`.
