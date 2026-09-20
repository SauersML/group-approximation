---
rg: 2
id: laurent-unstable-k2-splits-by-tame-symbol
kind: claim
title: For every field k and n >= 3, K_2(n, k[X,X^-1]) is K_2(k) plus k^* split by {X, -}, and field K_2 is stable from rank three
distinct_from:
  two-coordinate-relators-leave-stable-laurent-k2: that computes stable K_2 of a two-variable Laurent ring by the Bass fundamental theorem; this is the unstable, one-variable statement in every rank n >= 3, with an explicit splitting by Steinberg symbols.
  semilocal-steinberg-groups-have-central-k2: that is centrality of K_2(n, A) for semilocal A; this is the computation of K_2(n, -) of a Laurent ring over a field.
---

**ESTABLISHED by citation** (`laurent-unstable-k2-splits-by-tame-symbol-citation`). Let `k` be a field,
`n >= 3`, and `K_2(n, R) = ker(St_n(R) -> SL_n(R))`, the case `Φ = A_(n-1)` of `K_2(Φ, R)`.

1. There is an exact sequence of abelian groups `0 -> K_2(n,k) -> K_2(n,k[X,X^-1]) -> k^* -> 0`,
   split by the homomorphism `u -> {X,u}_α` for a fixed long root `α`. In particular `{X,u}_α ≠ 1`
   for `u ≠ 1`, and `u -> {X,u}_α` is an injective homomorphism.
2. `K_2(n, k[X,X^-1]) -> K_2(n, k(X))` is injective.
3. For every field `F`, the maps `K_2(3,F) -> K_2(n,F)` induced by the rank embeddings are
   isomorphisms. Hence `K_2(n,F) -> K_2(F)` is an isomorphism, `K_2(F)` being the colimit.
4. For every commutative ring `R` and units `u, v`, the symbol `{u,v}_α` is central in `St_n(R)`
   and lies in `K_2(n,R)`.

For a finite field, (3) and `quillen-k-theory-of-finite-fields` give `K_2(n, F_q) = 0` for all
`n >= 3`.
