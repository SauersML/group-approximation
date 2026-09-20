---
rg: 2
id: quotient-gap-gives-uniform-relative-projection-repair-proof
kind: route
title: "Liu's maximal bad-projection exclusion gives all-rank relative repair"
target: quotient-gap-gives-uniform-relative-projection-repair
requires: []
artifacts:
  - research/artifacts/liu-analytic-leaves-proof-acceptance-2026-09-20.md
---

## Attribution and proof

This is an independently verified exposition of **Jihao Liu**,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 3.2, not a new proof mechanism or discovery by
Cairn. The complete proof, with the exact quantifier order, is Section A
of the acceptance artifact.

For each fixed averaging depth, bounded projection witnesses transfer
the quotient gap to a coordinate estimate with a uniform additive
error tending to zero. For a fixed relative target eta, choose finitely
many depths first. At each depth choose a maximum-rank bad projection,
and remove its bounded-word neighborhood. Its trace tends to zero by
the additive estimate. Any bad projection in the complement could be
adjoined orthogonally, with the squared defect norms adding, contradicting
maximal rank. Thus a single large corner works for every input projection,
including arbitrarily small ranks.

On that corner either the input already has relative energy below eta,
or fixed-depth averaging gives z with
```
||z-p||_2 <= (2/a) sqrt(E(p)),
E(z) <= (eta^2/576) tr(p).
```
A coarea cut at a threshold in [1/3,2/3] has squared distance at most
9||z-p||_2^2 and energy at most 6 sqrt(tr(z)E(z)). The input hypothesis
then gives the asserted trace bounds and L=36/a^2. Finally diagonalize
only the fixed target eta, after constructing each common corner; this
preserves the universal quantification over all test projections at
each coordinate. The exceptional coordinates use e_n=0.

The artifact supplies the norm identities, support-orthogonality proof,
noncommuting cut-distance computation, constants, and diagonal sets.
This direct route is backed by that full written proof, not by the earlier
partial audit or merely by citing the theorem. It does not assume
commutant internality or the later scalar-block construction and is not
a Lean certification.
