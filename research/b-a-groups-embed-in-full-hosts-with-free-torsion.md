---
rg: 2
id: b-a-groups-embed-in-full-hosts-with-free-torsion
kind: claim
title: Every group in B_A embeds in a full clopen-transitive Cantor group in B_A in which prescribed finite subgroups act freely
distinct_from:
  finite-subgroups-of-full-cantor-groups-conjugacy-criterion: that shows free finite subgroups of a full clopen-transitive group are conjugate along any isomorphism; this asks for hosts in which given finite subgroups become free.
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that puts finitely presented full clopen-transitive groups in B_A; this asks which groups embed in such hosts with free torsion.
---

**OPEN.** For every `G ∈ B_A` and finite subgroups `C_1, ..., C_k ≤ G`, there are a
Cantor space `Z`, a full clopen-transitive `D ≤ Homeo(Z)` with `D ∈ B_A`, and an embedding
`G -> D` under which every `C_i` acts freely on `Z`.

**Use.** With `k = 2` this gives every finite-edge HNN extension of `G`, and so the whole
finite-edge closure (`finite-edge-closure-via-free-torsion-full-hosts`).

## Attempts

1. **Twisted Brin–Thompson hosts through their actor: dead for that embedding.** In
   `SV_Γ` the actor `Γ` acts on `C^S` by permuting coordinates. Every constant
   configuration is fixed, so no nontrivial element of `Γ` acts freely. A stabilizing
   embedding must not factor through the coordinate action.
2. **The tautological section space: free torsion holds; the host is missing.**
   - **Construction.** Let `D` act on a Cantor space `Y`, with `𝒮` its proper nonempty
     clopen sets. Put `Z = ∏_(U ∈ 𝒮) U`, a Cantor space, with
     `(d·z)_U = d(z_(d^(-1)U))`. This is the space of sections of the tautological bundle
     over `𝒮`; `C^𝒮` is the trivial-bundle case of Attempt 1.
   - **Every nontrivial finite-order `c ∈ D` acts freely on `Z`** (hand proof).
     - Pick `p` with `cp ≠ p`, whose orbit has size `m >= 2`.
     - Choose a clopen `B ∋ p` with `B, cB, ..., c^(m-1)B` pairwise disjoint. Intersect it
       over the powers of `c^m` to make it `c^m`-invariant. Then `U = ⊔_(i<m) c^i B` is
       `c`-invariant, proper after shrinking `B`, and has no fixed point of `c`.
     - A fixed point `z` would satisfy `z_U = c(z_U)` with `z_U ∈ U`.
   - **What is missing.** Let `TV_D` be the group of homeomorphisms of `Z` that are locally
     a tautological `d` composed with D-local maps in finitely many coordinates. It is full by
     definition. Clopen transitivity should follow from the usual brick moves, but that was
     not checked in detail. The claim for `G ≤ D` follows if `TV_D ∈ B_A`, for instance if
     it is finitely presented. This is a twisted Brin–Thompson group over a *nontrivial
     bundle*. No finite-presentation criterion for it is known here; Zaremsky's criterion
     covers the trivial bundle.
3. **Padding: adds strata, never removes them.** Acting on a proper clopen and trivially
   elsewhere adds the whole-group stratum to every finite subgroup
   (`finite-subgroups-of-full-cantor-groups-conjugacy-criterion`, Part 4). That already
   settles edge groups whose stabilizers are trivial or everything, for example prime
   order. Removing an intermediate stratum is exactly what freeness does, and no natural
   host tried here does it.
4. **Bridge to the synthesis master route (S1, `gq-bh-synthesis-master-route`).** Suppose
   `Λ ⊇ G` carries a free minimal subshift `X` whose full group `[[Λ ⋉ X]]`, or the
   master route's host built from it, is finitely presented, full and clopen transitive.
   Then every finite subgroup of `G` acts freely there, since `Λ ↷ X` is free. So a success
   of the master route's crux G3g also settles this node for `G`, and with it finite-edge
   closure. The two targets ask for the same object: a *free* Cantor action inside a
   finitely presented full group.

## Lesson for general BH

Free torsion comes from sections of nontrivial bundles, not from coordinate permutations.
So the natural next host class is twisted Brin–Thompson groups over bundles of Cantor sets:
twisted Brin–Thompson groups whose coordinates are twisted by the actor's own dynamics.
Proving a Zaremsky-type finite-presentation criterion for them would settle finite-edge
closure of `B_A`.
