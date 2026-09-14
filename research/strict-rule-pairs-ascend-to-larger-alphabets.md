---
rg: 2
id: strict-rule-pairs-ascend-to-larger-alphabets
kind: claim
title: Tables admitting strict rules over k symbols admit strict rules over every larger alphabet
distinct_from:
  strict-rule-pairs-pass-to-product-alphabets: that moves strictness from k symbols to multiples kl with the tables fixed; this asks for every n >= k, which multiples never reach when k has two distinct prime factors.
  equal-label-table-is-strict-at-three-symbols-not-two: that shows fixed tables do not descend; this asks whether fixed tables ascend, and that table admits every size n >= 3.
  surjunctivity-failure-descends-to-binary-alphabet: that is group-level descent to two symbols with the tables allowed to change; this is table-level ascent with the tables fixed, the other possible alphabet bridge.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

**OPEN.** Let `(T_f, T_r)` be a forward and a reverse product table. If some alphabet of size `k` admits
rules `(mu, nu)` strict for `(T_f, T_r)`, meaning the forward identity holds on `T_f` and the reverse
identity fails on `T_r`, then every alphabet of size `n >= k` admits such rules.

**Group-level consequence.** Through `surjunctivity-is-axiomatized-by-rectangle-clauses`, a group that is
not surjunctive over `k` symbols is not surjunctive over any `n >= k` symbols, with the same memories.
A strict automaton's rules are strict for its realized tables, and rules strict for those tables are
strict on the same group.

**Payoff.**
- **Alphabet bridge.** Gottschalk over binary-power alphabets gives Gottschalk over every alphabet
  (`gottschalk-via-alphabet-ascent`).
- **Why it is needed.** Product closure never reaches a size with two distinct prime factors from a prime
  power. So stable formalizability plus Kaplansky over every prime field gives Gottschalk only over
  prime-power alphabets (artifact, Section 7).
- **Linear soficity.** Linear soficity over a single prime field would then give surjunctivity over every
  alphabet (`linear-sofic-groups-are-surjunctive`).

Owned by lane gk-fz-alphabets, at gk-n-boolean's request.

## Attempts

- **Retraction onto a sub-alphabet** (boolean artifact, Section 5). Using `mu o r` and `nu o r` loses the
  demanded cell's position inside its fiber, unless all fibers of `r` have equal size, and equal fibers
  are exactly products.
- **Erasure symbol `*`** (boolean artifact, Section 5). The sink loses the values of relays that read a
  starred cell, while the forward identity uses every relay.
- **Walls, at group level** (this lane, artifact Section 7).
  - Construction: output `*` at starred sites, the raw symbol within radius `R` of a star, and `mu` of the
    window elsewhere.
  - What it gives: equal images agree near the stars, and far from them the `A`-parts have equal
    `tau`-images.
  - Where it dies: the decoder cannot certify sites in the annulus between radius `R - r_sigma` and `R`,
    because it reads band values that are output raw. Enlarging `R` moves the annulus without closing
    it, and outputting `tau`-values in the band too needs a product alphabet.
- **Evidence consistent with ascent.** Every classified table has upward-closed admissible sizes:
  - copy-code tables admit every `n >= 2`;
  - `x_a = x_b` and `x_a = x_b = x_a x_b` admit every `n >= 3`.

  Boolean artifact, Section 6, verified by gk-vf-nonlinear at 370dc8c2b3.
- **Where it stops.** No known construction adds a single symbol while keeping the forward identity on
  `T_f`. Every working extension is a product.
