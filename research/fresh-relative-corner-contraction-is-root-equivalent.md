---
rg: 2
id: fresh-relative-corner-contraction-is-root-equivalent
kind: claim
title: Fresh relative corner contraction below the free baseline is root-equivalent
distinct_from:
  identity-return-makes-arbitrary-actuator-root-strength: that uses the collapsed input r=1; this uses the genuinely fresh noncollapsed ratio required by the pairwise consumer.
  canonical-positive-density-pairwise-game-overlap-packing: that asks for a simultaneous finite family; this shows that with ambient free-product embedding one fresh edge already has root strength, and also audits the batched variant without that embedding.
artifacts:
  - research/artifacts/fresh-relative-corner-root-equivalence-2026-08-30.md
---

**ESTABLISHED EQUIVALENCE.**  Let `H` be the authenticated finite packet,
let `q in C[H]` be its projection, and put `alpha=tau(q)>0`.  Suppose a
corrected version of
[[canonical-positive-density-amplified-acceptance-corner-actuator]] is
restricted to a fresh ratio `r=v^(-1)w`, preserves the embedding of the
ambient free product `H*F(v,w)`, and is available for every prescribed
`L`.

Then that corrected actuator is equivalent, in the intended effective
finitely presented category, to constructing an explicit nonhyperlinear
group.  One fresh edge has canonical corner mass exactly `alpha^2`, whereas
the actuator asks for at most `alpha rho^(2L)`; choosing
`rho^(2L)<alpha` rules out canonical-profile microstates.

Even if ambient freeness is not preserved, the simultaneous target
[[canonical-positive-density-pairwise-game-overlap-packing]] is itself
root-equivalent.  Its projection packing inequality is

```text
M(alpha-rho^(2L)) <= 1-rho^(2L).
```

Choosing first `L` with `rho^(2L)<alpha` and then larger `M`
contradicts hyperlinearity.

Conversely, from any explicit finitely presented nonhyperlinear group `N`,
free-product every requested output with `N`.  The packet and ambient input
stay embedded, the perfect model extends by the trivial representation of
`N`, and the universal microstate clauses hold vacuously.

Thus a genuinely weaker correction must stop at the sharp free baseline
`alpha^2`, bound `M` or `L`, allow density decay, or give up the
composability needed by the present consumer.

DERIVATION
[[fresh-relative-corner-root-equivalence-proof]]
