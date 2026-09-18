---
rg: 2
id: extension-product-closures-cannot-create-sl-n-q
kind: claim
title: Closing a class under subgroups, extensions, direct products and free products never creates SL_n(Q) or GL_n(Q) from groups that lack SL_n(Q) and PSL_n(Q)
distinct_from:
  bffhz-closures-cannot-create-gl-n-q: that handles free products and the BFFHZ mapping tori over M * F_m; this handles every extension, every direct product, every wreath product and every free product at once, for the perfect groups SL_n(Q), PSL_n(Q) and hence GL_n(Q).
  lifts-add-no-unipotent-divisibility: that handles central and covering lifts of Q-free groups, and also the non-perfect groups Aff(Q), B_2(Q), U_3(Q); for SL_n(Q) and GL_n(Q) this contains it, since central extensions are extensions and Q-free groups lie in the class.
  mixed-permanence-closures-collapse-boone-higman-to-base: that uses a finitely generated simple FA probe against the whole conjecture and includes directed unions and graphs of groups; this uses the non-finitely-generated perfect probe SL_n(Q) against one named input, where directed unions and graphs of groups genuinely escape.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this rules out every route that builds the host from known groups by the listed operations alone.
---

**ESTABLISHED** through `extension-product-closures-cannot-create-sl-n-q-proof`.
Lane-proved, not independently reviewed. The argument is elementary and no
priority is claimed.

## Statement

Fix `n >= 2`. Let `P_n` be the class of groups `H` such that every homomorphism
`SL_n(Q) -> H` is trivial. Equivalently, `H` contains no subgroup isomorphic to
`SL_n(Q)` or to `PSL_n(Q)`.

1. **Seeds.** `P_n` contains every group with no subgroup isomorphic to `(Q,+)`,
   and every group with no subgroup isomorphic to
   `BS(1,4) = <a, t | t a t^-1 = a^4>`. In particular `P_n` contains:
   - every residually finite group (O1 of the root), so every finitely generated
     linear group, every self-similar group, `Aut(F_m)`, mapping class groups,
     spherical Artin groups;
   - every abelian and every solvable group, and every group whose abelian
     subgroups are finitely generated (hyperbolic, CAT(0));
   - `V` and `T`, which contain no `(Q,+)` (survey arXiv:2306.16356v3, Theorem
     4.4);
   - `VA` and its subgroups `T-bar` and Brin's `A`, which have no distorted
     cyclic subgroups (Burillo--Felipe arXiv:2605.09763v1, Corollary 5, quoted
     as O4 of the root), while `a` is exponentially distorted in `BS(1,4)`.
2. **Closure.** `P_n` is closed under isomorphism, subgroups, extensions,
   arbitrary restricted or unrestricted direct products, and free products.
   Hence it is closed under semidirect products, restricted and unrestricted
   (permutational) wreath products over any set, and finite-index overgroups.
3. **Consequence.** Let `Cl(C)` be the closure of a class `C` under these
   operations, applied in any order and any transfinite number of times. If
   `GL_n(Q)` or `SL_n(Q)` embeds in a member of `Cl(C)`, then `SL_n(Q)` or
   `PSL_n(Q)` already embeds in a member of `C`.
4. **Sharpness.** `P_n` is not closed under directed unions, nor under
   fundamental groups of graphs of groups over infinite graphs. `SL_n(Q)` is the
   directed union of the residually finite groups `SL_n(Z[1/m!])`, and so it is the
   fundamental group of the ray of groups with these vertex groups. Whether
   amalgams and HNN extensions over finite graphs preserve `P_n` is not settled
   here.

## Consequences for the root

- **Permanence routes add nothing.** The permanence theorems of the permutational
  class used in this graph are products and finite-index overgroups
  (`boone-higman-type-a-class-closed-under-finite-extensions`), permutational
  wreath products (`permutational-boone-higman-closed-under-wreath-products`,
  `bh-type-a-class-closed-under-permutational-lamp-wreaths`) and free products
  (BFFHZ Corollary F). Applied to base groups in `P_n`, they never produce
  `GL_n(Q)` for any `n >= 2`.
  - Every base group these theorems are applied to in the graph so far lies in
    `P_n` by item 1: the residually finite (linear, self-similar, `Aut(F_m)`,
    Artin, mapping class) inputs, hyperbolic and CAT(0) groups, and `V`. Hosts
    such as `nV`, twisted Brin--Thompson groups and `L_(F_2)(1,2)^x` are not
    claimed to lie in `P_n`.
- **Where a route must leave `P_n`.** Every route to `gl-n-q-embeds-in-fp-simple-group`
  needs a step outside the operations of item 2. Three kinds remain:
  - a directed union, which is circular unless the host is built uniformly;
  - a graph of groups with nontrivial edge groups: HNN extensions or amalgams, as
    in the entry points of `bffhz-closures-cannot-create-gl-n-q`;
  - a Thompson-type completion whose output is not an extension of its inputs,
    such as a twisted Brin--Thompson group `SV_G`, a Röver--Nekrashevych group
    `V_d(G)`, a finite germ extension, or `nV`. By Kojima--Sheng
    arXiv:2603.18410v3, `(Q,+) <= nV` for `n >= 2`.

  The first such step must create a copy of `SL_n(Q)` or `PSL_n(Q)` itself.
- **Not for the non-perfect stepping stones.** The extension clause fails for
  `(Q,+)`, `Aff(Q)` and `U_3(Q)`. For example `(Q,+)` is an extension of the
  Q-free group `Z` by the Q-free group `Q/Z`, and Belk--Hyde--Matucci's
  `Q <= T-bar` is exactly of this shape. For those groups see
  `lifts-add-no-unipotent-divisibility`.
