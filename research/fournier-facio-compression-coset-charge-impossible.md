---
rg: 2
id: fournier-facio-compression-coset-charge-impossible
kind: claim
title: No invariant charge for the Fournier--Facio group can live over its compression cosets
invalidates:
  - fournier-facio-induced-schreier-charge-extension
distinct_from:
  no-invariant-mean-on-coset-space: That is the general Kazhdan theorem for a known infinite-index subgroup; this verifies infinite index for the explicit compression subgroup and pushes the obstruction through every charged basis fibred over its cosets.
  fournier-facio-monomial-near-witness-impossible: That excludes every basis-normalizing witness by nonsoficity; this needs only the compression coset factor and excludes even nonfree charges above it.
---

Let `Gamma<G` be the compression subgroup in the explicit Fournier--Facio
group.  Then `G/Gamma` admits no `G`-invariant finitely additive probability
measure.

More generally, let `X` carry a probability charge `mu`, maps `T_g:X->X`,
and a map

```text
p:X -> G/Gamma
```

such that `mu` is invariant under every `T_g` and

```text
p(T_g x)=g p(x)
```

on a `mu`-conull set for every fixed `g`.  No such data exist: pushing `mu`
forward through `p` would give a `G`-invariant mean on `G/Gamma`.

This includes every product-basis induction
`Ind_Gamma^G(sigma)`, every direct sum of such inductions, arbitrary phase
twists within the fibres, and every Banach-limit charge assembled from those
bases.  Countable additivity is never used, so choosing the charge singular
does not evade the obstruction.

