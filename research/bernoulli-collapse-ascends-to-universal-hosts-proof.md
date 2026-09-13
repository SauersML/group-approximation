---
rg: 2
id: bernoulli-collapse-ascends-to-universal-hosts-proof
kind: route
title: Co-induce the collapse along an embedding into a two-generator simple group or into the fixed recursive host
target: bernoulli-collapse-ascends-to-universal-hosts
requires:
  - bernoulli-entropy-counterexample-constraints
  - countable-group-embeds-in-two-generator-simple-group
  - whitehead-universal-finitely-presented-container
  - binary-leavitt-unit-word-problem-decidable
---

**Permanence.** Part (d) of `bernoulli-entropy-counterexample-constraints`: if `G <= G'` and
`L^G ≅ K^G`, then `L^(G') ≅ K^(G')`, through the co-induction `L^(G') ≅ Coind(L^G)`. So `D(G) ⊆ D(G')`.

1. By `countable-group-embeds-in-two-generator-simple-group`, a countable `G` embeds in a two-generator simple
   group `S`, and `D(G) ⊆ D(S)`. For the equivalence, the root restricted to two-generator simple groups
   gives `D(S) = {0}` for all of them, hence `D(G) = {0}` for every countable `G`. Conversely, the restriction
   is a special case of the root.
2. By `whitehead-universal-finitely-presented-container`, every countably generated recursively presented `K`
   embeds in `U_*`. Permanence gives `D(K) ⊆ D(U_*)`.
3. `U` is countable, and its word problem is decidable (`binary-leavitt-unit-word-problem-decidable`) on the
   recursive generating set used there. The set of trivial words is then recursive, hence recursively
   enumerable, which gives a recursive presentation on those generators. Item 2 applies.
