---
rg: 2
id: twisted-bt-towers-climb-the-polynomial-hierarchy
kind: claim
title: The k-fold twisted Brin-Thompson tower over Thompson's F on the dyadics is a finitely presented simple group with Pi^p_k-complete word problem
distinct_from:
  twisted-brin-thompson-wp-equals-actor-orbit-problem: that proves the upper bound WP(SV_G) in coNP^OP(G,S) and the one-query lower bound OP <= co-WP; this proves the matching quantifier lower bound, that one SV layer adds a full universal quantifier over the actor's stabilizer problem, which that node lists as not claimed.
  leavitt-square-units-have-conp-parity-p-complete-word-problem: that pins one group at coNP^parityP, which lies above PH only conditionally and only under randomized reductions; this gives, unconditionally and under deterministic polynomial-time many-one reductions, one finitely presented simple group complete for each level Pi^p_k.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for hardness beyond every recursive bound; this stays inside PSPACE and shows twisted Brin-Thompson iteration reaches exactly the polynomial hierarchy, no more and no less.
  twisted-btb-groups-poly-dehn-only-if-np-eq-conp: that uses coNP-hardness of the copy of 2V inside a twisted Brin-Thompson group; here the hardness at level k is manufactured from the actor, not imported from 2V, and grows with k.
---

**ESTABLISHED** by `twisted-bt-towers-climb-the-polynomial-hierarchy-proof`.
Lane proof, unreviewed. It is self-contained apart from four established graph
nodes. The circuit encoding uses Birget's baker's-map idea, re-derived in the
proof and not imported.

**The tower.**
- `G_0 = F` acts on `S_0 = D = Z[1/2] ∩ (0,1)`.
- `G_(k+1) = SV_(G_k)` is the twisted Brin-Thompson group of the action of `G_k`
  on `S_k`. Its Cantor cube is `C^(S_k)`. The branch definition is the one in
  `twisted-btb-clopen-action-is-type-a`.
- `S_(k+1)` is the set of proper nonempty clopen subsets of `C^(S_k)`, with the
  natural action of `G_(k+1)`.

**Theorem.** For every `k >= 1`:
1. `G_k` is finitely presented and simple, and its action on `S_k` is of type (A).
2. The word problem of `G_k` is `Π^p_k`-complete under polynomial-time many-one
   reductions. The yes-instances are the trivial words.
3. The orbit problem `OP(G_k, S_k)` is `Π^p_k`-complete. This is the word problem
   together with membership in the stabilizer of a fixed clopen set.

So no finite level of the polynomial hierarchy bounds the word problems of
finitely presented simple groups. This holds unconditionally, with deterministic
reductions. All the groups `G_k` have word problems in PSPACE.

**The mechanism (Lemma Q, quantifier transfer).** Let `G` act faithfully on `S`
with `SV_G` finitely generated. Let `Y ⊂ G` be finite, and let `a, b, r ∈ S` be
distinct points such that every element of `Y` fixes `a` and `b`. Then every
language of the form

```text
L' = { z : for all y in {0,1}^m(|z|),  Φ(z,y) r != r },                (Q)
```

with `m` a polynomial and `Φ` a polynomial-time map to words over `Y`, reduces in
polynomial time to both of the following:
- the word problem of `SV_G`;
- membership in `SV_G` of the stabilizer of the fixed clopen set
  `{κ : κ(r) begins with 0}`.

Moreover the output words lie over a fixed finite set of elements supported in a
fixed proper brick.

This complements `(TBO1)` of `twisted-brin-thompson-wp-equals-actor-orbit-problem`,
which is the case `m = 0`. The new point is the universal quantifier. It is carried
by the digits of two workspace coordinates `a, b` that the labels in `Y` never move,
so the label of the branch over the workspace value `y` is the actor word `Φ(z,y)`.

**Obstruction (the complementary class kill).** Every finite tower of twisted
Brin-Thompson layers over an actor whose orbit problem is in `PSPACE` stays in
`PSPACE`. This follows from the relative upper bound `coNP^OP` and
`coNP^PSPACE = PSPACE`. An infinite tower is not finitely presented. So twisted
Brin-Thompson iteration, and the route `arbitrarily-complex-fp-simple-via-hard-type-a-actors`
started from any `PSPACE` actor, cannot reach beyond `PSPACE`. Within `PSPACE`, the
theorem shows that it reaches every level of PH. The heuristic that iteration adds
"at most one exponential and nothing sharp" is replaced by an exact count: each
layer adds exactly one alternation.
