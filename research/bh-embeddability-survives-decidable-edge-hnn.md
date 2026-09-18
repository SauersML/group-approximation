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
7. **Tree and self-similar engines, in any host.** *Dies* for the general
   statement (2026-09-17). By
   `profinite-tree-hosts-make-fa-subgroups-residually-finite`, every subgroup
   with property FA of a group acting faithfully on locally finite trees is
   residually finite. So is every such subgroup of a group of automorphisms of a
   locally finite rooted tree. The invariant is the finite residual of an FA
   subgroup. Every engine that first places `A*_phi`, or any overgroup of it, in
   one of these hosts dies at that placement whenever `A` contains an infinite FA
   subgroup that is not residually finite. The engines covered are:
   - Theorem B of Bux--Llosa Isenrich--Wu;
   - their Theorems 10.5 and 11.1, with the faithful enlargement;
   - Zaremsky's self-similar theorem;
   - hosts on products of trees with finite stabilizers.

   The Kazhdan group `S_q` of
   `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4` is such an `A`, with
   admissible edges trivial or all of `S_q`. Enlarging the input first, as
   Theorem 11.1 does, only produces another host of the same kind.

   The obstruction stops the engines, not the claim. The same claim puts
   `S_q * Z` and every mapping torus `S_q ⋊_phi Z` in `B_A`, through
   `outer-extensions-of-fp-simple-mif-groups-satisfy-pbh`, using that `S_q` is
   MIF. This settles, for finitely presented simple MIF bases, the mapping-torus
   case that Attempt 4 (L2) leaves open. So a proof of the general claim must use
   a type (A) or other non-profinite engine, as in Attempt 6. The free-base
   route `oriented-artin-bh-via-free-group-hnn-permanence` is not affected,
   because free groups have no nontrivial FA subgroups. Whether a one-relator
   base can contain an infinite non-residually-finite FA subgroup is not
   addressed.
8. **Tree and self-similar engines over a linear base with cyclic edges.**
   *Dies* for these engines (2026-09-17). This removes both hypotheses Attempt 7
   needed, FA and non-residual-finiteness. Take `A = BS(1,2) = <a, b | b a b^-1 = a^2>`,
   `C_1 = <a>`, `C_2 = <b>`, `phi(a) = b`. The input meets every hypothesis:
   - `A` is residually finite, linear and one-relator;
   - `A` embeds in a finitely presented simple group;
   - both memberships are decidable in the affine representation on `Z[1/2]`.

   Then `A*_phi` is the Baumslag--Gersten group. By
   `gersten-pairs-lie-in-no-locally-finite-tree-host`, no group acting on a
   locally finite tree, or factor by factor on finitely many such trees, with
   torsion kernel contains it. That covers the hosts of Theorem B and of Theorems
   10.5 and 11.1 of Bux--Llosa Isenrich--Wu, and every automorphism group of a
   locally finite rooted tree.

   The invariant is the set of primes dividing the orders of an elliptic element
   on finite balls. The base `<a, b>` is elliptic in every tree action. Since
   `a` and `b` are conjugate, their invariants agree. The relation
   `b a b^-1 = a^2` then forces the smallest prime to have a smaller prime in
   the same set, so `a` must act trivially. Every such engine dies when it places
   the input in its host.

   The same obstruction excludes every input in which some `a in C_1` of
   infinite order satisfies `phi(a) a phi(a)^-1 = a^2`. It applies to the
   Magnus-step permanence and to the one-relator route, which Attempt 7 had left
   open. Free bases are unaffected, since there `b a b^-1 = a^2` forces `a = 1`.
   A proof of the claim, even restricted to cyclic edges over residually finite
   linear bases, must therefore use a type (A) actor or another host in which
   `a` is not equicontinuous. A parallel attempt recorded on the live bus by
   agent c-hnn kills type (A) self-actions of `A*_phi` over proper-power cyclic
   edges, which also covers this input. Together the two leave, for this input, only
   engines whose host strictly contains `A*_phi` and is not a locally finite
   tree host.
9. **Untwist the edge map into a mapping torus (2026-09-17).** *Partial:* this
   is a decomposition, not a proof. By
   `extendable-edge-hnn-embeds-in-identity-hnn-of-mapping-torus`, whenever
   `phi = Phi|_C` for some `Phi in Aut(A')` with `A <= A'`, we have
   `A*_phi <= (A' ⋊_Phi Z) *_C (C × Z)`, via `t |-> u s`. The claim for such an
   input then follows from two prerequisites that can fail separately:
   - **(P1)** the mapping torus `A' ⋊_Phi Z` embeds in a finitely presented
     simple group;
   - **(P2)** the identity-edge extension `G *_C (C × Z)` of `G = A' ⋊_Phi Z`
     embeds in a finitely presented simple group.

   (P1) is established for three kinds of `A'`: free groups, finitely presented
   simple MIF groups, and `M * F_m` with `M` such a group. That is the mapping-torus
   case which Attempts 4 and 7 had isolated. (P2) is the case `phi = id` of this
   claim, and it is open. It is not easier in any known sense: the undecidability
   witness of `bh-embeddability-forces-decidable-edge-membership` is an identity
   edge.

   **Clean free-base inputs.** If `C` and `D` are free factors of a free group
   `F`, then `phi` extends inside `F`. So these inputs reduce to (P2) over
   free-by-cyclic groups.

   **Where the reduction stops over free overgroups.** Two invariants block any
   free `F' >= F`: the maximal root exponent and the lower-central depth. They
   apply to every unbalanced input, and also to balanced inputs such as
   `t a t^-1 = [a, b]`.

   **Literature check (2026-09-17).** Jankiewicz, arXiv:2503.16722 (abstract, as
   fetched): "the fundamental group of a geometrically clean graph of finite rank
   free groups does not need to be virtually compact special". So the route
   through virtual specialness and `virtually-special-groups-embed-in-brin-thompson-group-2v`
   cannot cover the clean free-base case in general. This does not exclude
   embeddings into `2V` by other means.

   **Also recorded.** For the free-base case, embedding `F*_phi` in `F*_psi`,
   where `psi` extends `phi` to Hall completions `H_1, H_2 <= F` of finite index,
   is never injective. Its kernel contains `t f t^-1 psi(f)^-1` for
   `f in (F ∩ H_1) - C`. More generally, for any locally finite tree host in
   which `F` fixes a vertex `v`, the set of `f in F` fixing `t^-1 v` has finite
   index in `F`. That only kills maps sending `t` to a stable letter whose vertex
   group contains `F`. It does not kill tree hosts for free bases; unlike
   Attempt 8, no invariant was found there.
10. **Type (A) actions of `A*_phi` itself, sharpened and killed on
   proper-power data.** *Dies* for that engine on concrete flagship inputs
   (2026-09-17, calibration family). This attempt sharpens Attempt 5 by
   `type-a-actors-split-only-over-orbit-finite-edges`. Let `C_1 != A != C_2`, and
   suppose `K = A*_phi` acts on `X` with finitely generated stabilizers and
   finitely many orbits of pairs. Then:
   - every point stabilizer contains a hyperbolic element and acts on the whole
     Bass--Serre tree with finite quotient;
   - `A`, `C_1` and `C_2` each have finitely many orbits on `X`.

   So the clause "`D_1` has finitely many orbits" in Attempt 6 is necessary for
   every type (A) action of a non-ascending HNN extension, not an artifact of
   that construction. The invariant is `r(c)`, the number of regular orbits of
   an element `c` generating a finite-index subgroup of a vertex or edge group.
   It is conjugation invariant, and `r(c^p) = |p| r(c)`. The engine dies at the
   step where `C_1` must be orbit-finite: whenever `C_1` is finite, or `phi`
   together with `A` makes such a `c` conjugate to a proper power `c^q`,
   `|q| != 1`, the set `X` is forced to be finite. By
   `type-a-actors-have-no-proper-power-cyclic-edge-splittings`, this rules out a
   type (A) action of the group itself in three cases:
   - the Baumslag--Gersten group (`A = BS(1,2)`, `<a> -> <b>`), which is one of
     the claims this node would flip;
   - `BS(m,n)` with `|m| != |n|` both at least 2, even though these groups
     satisfy Boone--Higman;
   - every non-ascending HNN extension over a finite group.

   Engines that build a *larger* actor containing `A*_phi` are not affected. But
   a proof reaching BG must use an actor in which the restricted action of BG
   has infinitely many orbits of pairs or an infinitely generated stabilizer. So
   pair-orbit finiteness can never be inherited by restriction to BG.

## Attempt (bh-free-05, 2026-09-18): Hall-type hosts for free bases

- **Setting.** Take `G = F*_{φ : A -> B}` with `F` finitely generated free and `A, B`
  finitely generated. With `Y = F * <b>`, M. Hall plus equal-index adjustment extends `φ` to
  `Φ = φ * α : C_1 = A * R -> C_2 = B * L` between finite-index subgroups of `Y`, for any
  choice of `α`. Then `H = Y*_Φ ∈ BS_{F_2}`, which satisfies BH by BLIW §12.5.
- **The ascending case.** `A = F` is `ascending-hnn-of-free-groups-satisfy-boone-higman`: the
  map `G -> H` is injective even though the subgroup criterion fails.
- **A necessary condition in general.** Put `Ā = F ∩ C_1` and `B̄ = F ∩ C_2`. The words
  `y x y'`, with `y, y'` in `tFt^-1`, show that injectivity requires
  `B̄ ∩ Φ(Ā) = B`. So no element of `Ā \ A` may be sent into `F`.
- **One-sided case.** It holds automatically when `A` has finite index in `F`, since then
  `C_1` can be chosen with `Ā = A`. So the one-sided case, `A` of finite index and `B`
  arbitrary, passes this first test. Full injectivity there is OPEN.
- **Two-sided case.** When both `A` and `B` have infinite index, the condition constrains the
  choice of `α`. Whether a generic `α` gives an injective map is OPEN.

- **Refinement (bh-free-05).** `domain-exact-hnn-hosts-have-multivalley-kernels`: in the one-sided case every kernel element of the Hall-host map is hyperbolic on `T_G`, with at least two height-maxima per period. That is the precise remaining gap there. Also checked: with `F` elliptic in a `BS_{F_2}` host, the forced subgroup `P' *_D tF_1t^-1` must be free. That imposes nothing, because M. Hall lets one choose `P'` with `D` a free factor, so it is not an obstruction.

## Attempt (bh-free-10, 2026-09-18): identity edges in the permutational class

*Settles (P2) of Attempt 9 over finite edges; reduces it over infinite ones.* By
`free-permutational-products-preserve-pbh` (lane proof, not reviewed):
- **Finite edges.** For `A ∈ B_A` and a finite `C <= A`, the identity-edge extension
  `A *_C (C × Z)` lies in `B_A`. So does `A *_C (C × K)` for every `K ∈ B_A`. No
  retraction `A -> C` is needed. An HNN extension `A*_phi` over finite edges lies in
  `B_A` as soon as `phi` is conjugation inside some `B_A`-overgroup of `A`; this is the
  same `t -> u s` untwisting as Attempt 9.
- **Infinite edges.** For any `C <= A`, `A *_C (C × Z)` lies in `B_A` if the
  lamplighter `Z/2 wr_(A/C) A` does. That is an instance of the open
  `pbh-closed-under-decidable-permutational-wreaths`, whose decidability hypothesis is
  exactly this claim's decidable membership. The version over arbitrary coset spaces
  is refuted by `pbh-wreath-closure-fails-over-undecidable-stabilizers`, through the
  same Mihailova mechanism as `bh-embeddability-forces-decidable-edge-membership`.
- **Mechanism.** In `Aut_M(M * F(x, y))`, the factors `w K w^(-1)` go to transvections
  by `g_w K g_w^(-1)`, with `g_w = y δ_(wC) y` built from a lamp `δ_(wC)`. The base `A`
  acts by twisted conjugations. The lamp's centralizer in `A` is exactly `C`, which is
  what makes the copies free.
