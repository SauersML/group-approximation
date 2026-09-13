---
rg: 2
id: sofic-configurations-cannot-force-v-rank-triviality
kind: claim
title: No finitary rank argument confined to a sofic configuration of Thompson's V can push rk(1 - [g]) below 1 - 1/ord(g)
distinct_from:
  v-rank-models-act-freely-by-wandering-elements: that proves a lower bound for every rank function on F[V] and elements with a wandering clopen; this shows which arguments cannot prove upper bounds, for any configuration generating a sofic subgroup.
  anti-central-sofic-data-cannot-force-defect-submultiplicativity: that is the anti-central characteristic-three firewall for cylinder defects of the ternary Leavitt unit group; this is the firewall for triviality of rank functions on group algebras of V, over any field.
  thompson-v-carries-ternary-nonaugmentation-rank-function: that is the existence of a detecting rank function on all of F_3[V]; this produces detecting rank functions on F[K] for every sofic finitely generated K <= V, which is what blocks confined arguments.
artifacts:
  - research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md
---

**ESTABLISHED** by `sofic-configuration-v-rank-firewall-proof` (artifact Sections 0–2). Independently re-derived by
`w3-vf-linear`: PASS (Section 31.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`). Its three
precision notes are applied in the artifact: Lemma 1.1 step 4, `K != 1` in Theorem 1.2, and "complements" for the
comparison with Proposition 3.2.

**Setting.**
- `F` is any field, `S ⊆ V` is finite, and `K = <S>`.
- An argument about a rank function on `F[V]` is *confined to `S`* when its conclusion concerns ranks of matrices
  over `F[K]` and every premise is one of:
  - the Sylvester axioms applied to matrices over `F[K]`;
  - an equality of matrices that holds in `F[K]`;
  - single-element conjugacy data `rk(q([g])) = rk(q([g']))` for `g, g'` in `K` conjugate in `V`, with any
    conjugator.

**Statement.**
1. **Sofic rank functions** (Lemma 1.1, standard, proof included). Every countable sofic `K` has a Sylvester
   matrix rank function `rk_K` on `F[K]` with:
   - `rk_K(q([g])) = 1 - deg gcd(q, t^n - 1)/n` for `g` of order `n`, and `1` for infinite order;
   - in particular `rk_K(1 - [g]) = 1 - 1/ord(g)`.
2. **Inertness** (Theorem 1.2). If `K` is sofic, no argument confined to `S` concludes `rk(1 - [g]) < 1 - 1/ord(g)`,
   or, when `K != 1`, that the rank function is the augmentation rank on `F[K]`.
3. **Instances inside `V`** (Section 2):
   - lamp configurations `<x, L> ≅ L wr Z`, for `x` with a wandering clopen `W` and finite or amenable
     `L <= Rist_V(W)`; the sofic case imports Hayes–Sale at statement level;
   - configurations generating free products of finite groups, or residually finite or LEF subgroups;
   - every configuration inside `F`, if `thompson-f-is-amenable` holds.

**Consequences.**
- **What a proof needs.** Any step of a proof of `thompson-v-ternary-rank-functions-are-augmentation`, or of its
  characteristic-two analogue, that lowers `rk(1 - [g])` below the sofic value must be confined to a configuration
  that is not known to be sofic, or must use tuple-level `V`-conjugacy through a conjugator outside the configuration.
- **Compared with Proposition 3.2** of `thompson-v-rank-models-fixed-rank-and-wandering-freeness-2026-09-12.md`:
  this needs no Elek–Szabó import and covers free products, which that proposition listed as not covered.
- **What it produces:** for every tested sofic configuration, a detecting rank function consistent with all its
  premises.
