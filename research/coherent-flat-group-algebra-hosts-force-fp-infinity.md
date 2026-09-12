---
rg: 2
id: coherent-flat-group-algebra-hosts-force-fp-infinity
kind: claim
title: A left coherent algebra containing a group algebra flatly as a module summand forces every finitely generated subgroup to be of type FP_infinity
distinct_from:
  full-group-algebra-to-steinberg-algebra-not-injective: that shows canonical Steinberg hosts do not contain the group algebra of their full group; this shows that regular coherent hosts cannot contain group algebras flatly once the group contains Z wr Z, so the non-injectivity is forced rather than incidental.
  decidable-group-algebras-have-fp-central-simple-hosts: that is the open group-algebra premise, with regular supercoherence suggested as a sufficient condition; this excludes coherent hosts of the flat-summand shape for every input containing Z wr Z.
artifacts:
  - research/artifacts/bh-steinberg-hosts-2026-09-12.md
---

**ESTABLISHED (with the Chase and Bieri--Eckmann criteria as imports).** Let `K`
be a field, `S` a finitely generated group, and `B` a left coherent `K`-algebra
containing `K[S]` as a unital subalgebra. Suppose `B` is flat as a right
`K[S]`-module and `K[S]` is a direct summand of `B` as a right `K[S]`-module.

1. Every finitely generated subgroup of `S` is of type `FP_infinity` over `K`.
2. If `B` is also left regular, and `K[S]` is a `K[S]`-bimodule summand of `B`,
   then `cd_K S < infinity`.

## Consequences

- **`Z wr Z` is excluded.** `H_2(Z wr Z; K)` is infinite-dimensional: the
  coinvariants of `Λ^2(K^(Z))` under the shift inject into it. So `Z wr Z` is not
  of type `FP_2` over `K`, and no algebra of this shape contains `K[S]` for any
  `S ⊇ Z wr Z`.
- **Every universal host family of this shape fails.** `Z wr Z` has solvable word
  problem, so some infinite simple input contains it
  (`boone-higman-iff-infinite-simple-inputs`).
- **Characteristic `p`.** In the regular case with a bimodule summand, inputs
  with elements of order `p` are excluded, because `cd_(F_p)(Z/p) = infinity`.
- **Unit hosts are untouched.** `L_2` is regular coherent and contains
  `V ⊇ Z wr Z` in its units. By `full-group-algebra-to-steinberg-algebra-not-injective`,
  `F_2[V]` does not embed canonically. So on the Leavitt route the unit-only
  premise `simple-inputs-have-fp-elementary-leavitt-tensor-hosts` is forced for
  regular coherent hosts, not only permitted.

## Trust

Folklore-level homological algebra; no novelty is claimed. The imports are:
- Chase: `B` is left coherent iff direct products of `B` are flat right modules.
- Bieri, *Homological Dimension of Discrete Groups*, Theorem 1.3.

Neither was re-read from source in this lane. Not reviewed, and not in Lean.

DERIVATION
coherent-flat-group-algebra-hosts-force-fp-infinity-proof
