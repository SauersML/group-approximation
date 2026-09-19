---
rg: 2
id: constructed-continuum-of-finitely-generated-groups-proof
kind: route
title: Alternating lamps over marked coset spaces, separated by countable fibres
target: constructed-continuum-of-finitely-generated-groups
requires: []
artifacts:
  - GroupApproximation/Monsters/NeumannAlternatingFamily.lean
  - GroupApproximation/Monsters/NeumannContinuum.lean
---

## Direct proof, machine-checked

**The index set.**  `markedSubgroup S = <a^n b a^{-n} : n in S>` for
`S subseteq N`.  `markedSubgroup_injective` proves these pairwise distinct, via
the lamplighter picture `a |-> inr a`, `b |-> inl (single 1 k)` of `F2` inside
`A5 wreath F2`: `a^n b a^{-n}` becomes the one-site lamp at site `a^n`, the
sites `a^n` are pairwise distinct (`site_injective`, off the degree
homomorphism `degHom`), so the subgroup remembers `S`.  The powerset of `N` has
cardinality continuum (`mk_set_nat`).

**Finite generation.**  `fg_wreathQuotient`: transitivity of the `F2`-action on
`F2 / H` makes the two free generators together with the lamps at the base
coset generate `W H`.

**Separation.**  `countable_isomorphic_subgroups`: for a fixed countable `Q`
only countably many `H` give `W H =~ Q`, because an isomorphism is determined
by the images of a finite generating set and there are only countably many
tuples in a countable group.  `countable_neumannGroup` supplies countability of
each member.  `exists_continuum_transversal` then extracts, from a
continuum-sized family with countable isomorphism fibres, a continuum-sized
subfamily that is pairwise nonisomorphic; `transversal_pairwise` and
`mk_transversal` are its two conclusions, and
`neumann_continuum_of_finitely_generated_groups` packages them.

No hypothesis, and no citation: the only external ingredient is Mathlib's
cardinal arithmetic for maps with countable fibres.
