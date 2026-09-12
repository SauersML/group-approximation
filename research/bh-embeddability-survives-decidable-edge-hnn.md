---
rg: 2
id: bh-embeddability-survives-decidable-edge-hnn
kind: claim
title: HNN extensions over finitely generated edges with decidable membership preserve embeddability into finitely presented simple groups
distinct_from:
  bh-embeddability-forces-decidable-edge-membership: that proves decidable edge membership is NECESSARY and that the unrestricted closure fails; this asserts that with that hypothesis the closure holds, which is open.
  boone-higman-type-a-class-closed-under-finite-extensions: that is a permanence of the type (A) class under finite extensions; this is a permanence of embeddability into finitely presented simple groups under HNN extensions with infinite, finitely generated associated subgroups.
---

Let `A` be a finitely generated group that embeds in a finitely presented
simple group. Let `C_1, C_2 <= A` be finitely generated subgroups with decidable
membership problems in `A`, and let `phi : C_1 -> C_2` be an isomorphism given
on generators. Then the HNN extension `A*_phi` embeds in a finitely presented
simple group.

**OPEN.** By `bh-embeddability-forces-decidable-edge-membership`, the
decidability hypothesis is necessary, and without it the statement is false.
With it, `A*_phi` has solvable word problem by Britton's reduction, so no
decidability obstruction remains. So the claim is a special case of
`boone-higman-conjecture`. It cannot be refuted without refuting that
conjecture, and it serves the route `boone-higman-via-decidable-edge-towers`
only through a proof that does not pass through the conjecture.

## Attempts

1. **Twisted Brin--Thompson group of the tree action.** On the Bass--Serre tree
   of `A*_phi`, distance between two vertices is an invariant of two-element
   subsets, and it takes infinitely many values. So the tree action has
   infinitely many orbits of two-element subsets, and
   `twisted-brin-thompson-finite-presentation-criterion` does not apply to it.
   *Dies* for this action. Attempt 5 extends this to every action of `A*_phi`.
2. **Pass to the envelope first.** Embed `A <= S` with `S` finitely presented
   simple, and form `S*_phi`. It is finitely presented because `C_1, C_2` are
   finitely generated, and it contains `A*_phi`. Two gaps remain. Membership of
   `C_i` in `S` need not be decidable even when it is decidable in `A`; it is if,
   for example, `A` has decidable membership in `S`. And `S*_phi` is not simple:
   a finitely presented simple overgroup of it is Boone--Higman for HNN
   extensions of finitely presented simple groups, no easier than the claim.
   The first gap does occur. Take `N <| G <= S` from
   `bh-embeddability-forces-decidable-edge-membership` (ii), with `G`
   hyperbolic, `N` two-generated and `S` finitely presented simple. The input
   `A = C_1 = C_2 = N`, `phi = id` meets every hypothesis. But `S*_phi` contains
   `<G, t>`, which is `G*_N` by the HNN subgroup theorem since `G ∩ N = N`, and
   by (ii) no finitely presented simple group contains `G*_N`. *Dies* for an
   arbitrary envelope `S`. Envelopes chosen so that `C_1, C_2` are decidable in
   them are untried.
3. **Iteration cannot reach FA inputs.** By
   `fa-subgroups-of-graph-towers-lie-in-base-pieces`, iterating this permanence
   along a tower reaches an input with property FA only through the base group.
   This does not refute the claim; it limits what iterating it can prove.
4. **Finite-index edges.** Suppose `A` is finitely presented, each `[A : C_i]`
   is finite, and `A*_phi` acts faithfully on its Bass--Serre tree. Then the
   claim holds without using the envelope of `A`, by
   `finite-index-edge-hnn-embeds-in-fp-simple-group` (Theorem 10.5 of
   Bux--Llosa Isenrich--Wu). That claim records where the method stops.
   Faithfulness forces `A` to be residually finite. For `A` an infinite finitely
   presented simple group, the only finite-index case is the mapping torus
   `A ⋊_phi Z`: its tree is a line with `A` in the kernel, so the case Attempt 2
   leads to is not covered. Embedding into an HNN extension with finite-index
   edges enlarges an infinite-index edge `C_i` to `A ∩ D_i != C_i`. The HNN
   subgroup theorem does not apply to such an embedding, so injectivity needs a
   different argument. *Partial.*
5. **Other actions of `A*_phi` of type (A).** Attempt 1 extends to every action
   of `K = A*_phi` itself. On an orbit `K/P`, the orbits of two-element subsets
   correspond to the double cosets `PgP` with `g notin P`, up to `g ~ g^-1`. If `P`
   fixes a vertex `v` of the Bass--Serre tree, then `d(v, gv)` is constant on
   `PgP` and unbounded. If `P` lies in the kernel of `chi : K -> Z` with
   `chi(t) = 1` and `chi(A) = 0`, then `chi` is constant on `PgP`. So every point
   stabilizer of a type (A) action of `K` fixes no vertex and has nonzero image
   under `chi`. Being finitely generated, it then contains a hyperbolic element
   (Serre, *Trees*, §I.6.5). No such stabilizer with finitely many double cosets
   has been found, and the actor must also be finitely presented. *Open.*
6. **Extend an existing type (A) action by a stable permutation.** By
   `stable-permutation-hnn-of-type-a-actor-is-type-a`, `A*_phi` embeds in a
   finitely presented simple group under four conditions:
   - `A` lies in a group `Gamma` acting on `X` of type (A);
   - `phi` extends to `psi : D_1 -> D_2`, with `D_i <= Gamma` finitely generated,
     `A ∩ D_i = C_i`, and `D_1` having finitely many orbits on `X`;
   - some permutation `pi` of `X` realizes `psi`;
   - `<Gamma, pi>` is the HNN extension `Gamma*_psi` itself.

   On this path finite presentation and pair-orbit finiteness are free, unlike
   Attempts 1 and 5. It breaks at three clauses:
   1. an actor containing `A` must exist, which is
      `permutational-boone-higman-conjecture` for `A` and is open even when `A`
      embeds in a finitely presented simple group;
   2. the edges must be enlarged to permutation-isomorphic `D_i` with finitely
      many orbits, which either meet `A` exactly in `C_i` or come with another
      proof that `<A, t> = A*_phi`;
   3. `pi` must satisfy a Britton-type ping-pong condition, which no
      construction here supplies.

   For `C_1 = C_2 = A` the claim's case (c) covers mapping tori `A ⋊_phi Z` in
   which `phi` is induced by a permutation normalizing an actor. This is the
   case Attempt 4 leaves open. *Partial.*
