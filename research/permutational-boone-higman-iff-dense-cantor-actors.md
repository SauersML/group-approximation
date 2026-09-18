---
rg: 2
id: permutational-boone-higman-iff-dense-cantor-actors
kind: claim
title: Permutational Boone–Higman holds exactly when every decidable input lies in a finitely presented dense subgroup of Homeo(Cantor) with finitely generated clopen stabilizers
requires:
  - twisted-btb-clopen-action-is-type-a
  - type-a-action-gives-boone-higman-for-subgroups
distinct_from:
  permutational-boone-higman-conjecture: that is the conjecture itself (every decidable input embeds in some type (A) actor, on some set); this proves it is equivalent to the same statement with the actor forced to act on one fixed homogeneous structure, the countable atomless Boolean algebra, densely in its automorphism group.
  fp-full-binary-cantor-groups-have-type-a-actions: that shows one sufficient source of dense Cantor actors (finitely presented full groups containing standard V); this states the two-sided equivalence, with no fullness hypothesis.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C (high transitivity / MIF of a finitely presented simple overgroup); this is a different normal form, oligomorphic on clopens rather than highly transitive on points, and it keeps the stabilizer condition explicit.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no novelty claimed — it
repackages `twisted-btb-clopen-action-is-type-a` and Zaremsky's type (A) definition).

Let `C = {0,1}^N` and let `Ω` be the countable set of proper nonempty clopen
subsets of `C`. Give `Homeo(C)` the compact-open topology. Equivalently, this is the
permutation topology of its action on the countable atomless Boolean algebra
`Clop(C)`, since `Homeo(C) = Aut(Clop(C))` by Stone duality. Call `Γ ≤ Homeo(C)`
**dense** if it is dense in this topology.

**Theorem.** For a finitely generated group `H` with solvable word problem, the
following are equivalent.
1. `H` satisfies permutational Boone–Higman: `H` embeds in a group with an action of
   type (A) (`type-a-action-gives-boone-higman-for-subgroups`).
2. `H` embeds in a finitely presented dense subgroup `Γ ≤ Homeo(C)` such that
   `Stab_Γ(U)` is finitely generated for every `U ∈ Ω`.

Moreover, in (2) one can take `Γ` simple, with every clopen stabilizer finitely
presented. So `permutational-boone-higman-conjecture` is equivalent to: *every
decidable input lies in a finitely presented dense subgroup of Homeo(C) with finitely
generated clopen stabilizers.*

## Proof

**Density means Boolean-pattern transitivity.** For clopens `U_1, …, U_k`, their
*pattern* is the set of sign vectors `ε ∈ {±}^k` whose atom `⋂ U_i^{ε_i}` is nonempty.
Two `k`-tuples lie in one `Homeo(C)`-orbit exactly when their patterns agree. The
reason is that nonempty clopens are homeomorphic, so any bijection of atoms that
respects the pattern is realized by a homeomorphism. Basic open sets of `Homeo(C)`
are `{h : h(U_i) = V_i, i ≤ k}`. So `Γ` is dense if and only if its orbits on
`k`-tuples of clopens are exactly the pattern classes, for every `k`.

**(2) ⇒ (1).** Let `Γ` act on `Ω`.
- *Faithful:* if `γ(x) = y ≠ x`, pick a clopen `U ∋ x` with `y ∉ U`. Then
  `γ(U) ≠ U`.
- *Finitely presented:* by hypothesis.
- *Point stabilizers:* finitely generated, by hypothesis.
- *Orbits on two-element subsets:* for `U ≠ W` in `Ω` there are exactly five
  patterns, so density gives five orbits. The five are: disjoint with union `≠ C`;
  complementary; strictly nested; overlapping with union `≠ C`; overlapping with
  union `= C`.

So the action is of type (A), and `H ≤ Γ` gives (1).

**(1) ⇒ (2).** Let `H ≤ G`, with `G` acting on `S` with type (A). Then `S` is
countable, since `G` is finitely generated and has finitely many orbits.
- By `twisted-btb-clopen-action-is-type-a`:
  - `SV_G ≤ Homeo(C^S)` is finitely presented.
  - Two `k`-tuples of proper nonempty clopens of `C^S` lie in one `SV_G`-orbit
    exactly when their Boolean patterns agree, so `SV_G` is dense.
  - `Stab(U) = D(U) × D(U^c)`, and each factor is isomorphic to `SV_G`, hence
    finitely presented.
- `SV_G` is simple and contains `G` (Zaremsky's Corollary B, as imported in
  `type-a-action-gives-boone-higman-for-subgroups`).
- `C^S` is homeomorphic to `C`, since `S` is countable and nonempty. Conjugating by
  a homeomorphism `C^S → C` preserves finite presentation, density, simplicity and
  the stabilizer groups.

So `H ≤ G ≤ SV_G` gives (2), with `Γ = SV_G` simple and every clopen stabilizer
finitely presented. ∎

## Reading for the swarm: the homogeneous-structure angle

The motivating question was: *does every decidable finitely generated group embed in
a finitely presented group acting with finitely many orbits on pairs and finitely
generated stabilizers, built from a decidable homogeneous structure?* That question
is exactly PBH, which is OPEN, and the theorem gives the following sharper reading.
- **One structure suffices.** The countable atomless Boolean algebra is universal for
  PBH. It is decidable, homogeneous and ω-categorical. No other Fraïssé limit (random
  graph, Henson graphs, generic poset, rational Urysohn space) can widen the class
  `B_A`; such structures could only supply different actors for the same class.
- **Pair-orbit finiteness is free for dense actors.** A dense subgroup of an
  oligomorphic group has finitely many orbits on `k`-tuples for every `k`. Only
  finite presentation and finitely generated stabilizers carry content.
- **Decidability of the binary structure is automatic.** The orbit problem of a
  type (A) actor, i.e. stabilizer membership, reduces to the word problem of the
  finitely presented simple group `SV_G`
  (`twisted-brin-thompson-wp-equals-actor-orbit-problem`).

## The stabilizer clause cannot be dropped

It is not true that every finitely presented dense subgroup of `Homeo(C)` has finitely
generated clopen stabilizers. By `homeo-cantor-has-dense-free-subgroups-without-fg-stabilizers`,
the shift `σ` on `{0,1}^Z` and a generic homeomorphism `t` generate a dense free group
`⟨σ,t⟩ ≅ F_2`. It is finitely presented, yet none of its clopen stabilizers is finitely
generated, since free groups have no transitive actions with finitely many orbits on
pairs and finitely generated stabilizers
(`free-groups-have-no-pair-finite-actions-with-fg-stabilizers`). So the clause in (2)
carries real content.

*History (09-18, bh-free-19).* An earlier version cited
`fp-dense-cantor-subgroups-need-not-have-fg-clopen-stabilizers`, whose witness
`⟨V,t⟩ ≅ V * Z` does not exist: that claim is REFUTED by
`v-and-a-homeomorphism-never-generate-a-free-product`.

The clause does hold for finitely presented full groups containing standard `V`
(`fp-full-binary-cantor-groups-have-type-a-actions`) and for twisted Brin–Thompson
groups.
