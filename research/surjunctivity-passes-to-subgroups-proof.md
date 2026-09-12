---
rg: 2
id: surjunctivity-passes-to-subgroups-proof
kind: route
title: Extend an automaton over the subgroup to one over the group by the same memory and rule
target: surjunctivity-passes-to-subgroups
requires: []
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

## Direct proof

Let `H <= G` with `G` surjunctive, and let `tau` be an injective cellular
automaton over `H`, with finite alphabet `A`, finite memory `M <= H`, and local
rule `mu: A^M -> A`, so `tau(y)(h) = mu((y(hm))_{m in M})` for `y in A^H`.

Define `tau^G` on `A^G` by the same data: `tau^G(x)(g) = mu((x(gm))_{m in M})`.
This is a cellular automaton over `G` (finite memory `M`, rule `mu`).

**Coset independence.** Since `M <= H`, every address `gm` read at a point `g`
lies in the coset `gH`. Fix left-coset representatives `{g_i}`. Under the
bijection `A^G = prod_i A^{g_i H}` and each identification `A^{g_i H} = A^H` via
`h -> g_i h`, `tau^G` acts on the `i`-th factor as exactly `tau`, independently
of the other factors.

**Injective.** `tau` is injective on `A^H`, so `tau^G` is injective on each
factor, hence on the product `A^G`.

**Transfer.** `G` is surjunctive, so `tau^G` is surjective. Surjectivity on the
product forces surjectivity on each factor, so `tau` is surjective on `A^H`.

Thus every injective cellular automaton over `H` is surjective: `H` is
surjunctive. The contrapositive gives the overgroup form. This uses no soficity;
the same argument is recorded as (F2) in the surjunctive-nonsofic artifacts and
is Ceccherini-Silberstein--Coornaert, *Cellular Automata and Groups*, 2010.
