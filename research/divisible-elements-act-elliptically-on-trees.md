---
rg: 2
id: divisible-elements-act-elliptically-on-trees
kind: claim
title: In any action on a tree, an element with roots of infinitely many orders is elliptic, and a copy of (Q,+) fixes a vertex or exactly one end
distinct_from:
  sl-n-q-lies-in-finite-residual-of-every-overgroup: that is the profinite side of O1; this is the tree-action side, and it says where divisibility must sit in any Bass-Serre-type host.
  lifts-add-no-unipotent-divisibility: that excludes central and covering lifts; this constrains every action of every overgroup on a simplicial tree.
---

**ESTABLISHED** through `divisible-elements-act-elliptically-on-trees-proof`. Not
independently reviewed. The argument is elementary (Tits' dichotomy for tree
automorphisms) and no priority is claimed. It is the tree analogue of Higman's
lemma that an infinite-order element of `V` has roots of only finitely many
orders. The calibration artifact `research/artifacts/gq-gq-calibration-worlds.md`
lists the tree case as a standard test without proof; this node proves it.

## Statement

Let a group `H` act on a simplicial tree `T` by automorphisms, and let `T'` be the
barycentric subdivision (so `H` acts on `T'` without inversions).

1. **Roots force ellipticity.** If `g in H` has a `k`-th root in `H` for
   infinitely many `k`, then `g` fixes a vertex of `T'`. A hyperbolic `g` has a
   `k`-th root only for `k <= l(g)`, where `l(g) >= 1` is its translation length
   on `T'`.
2. **Dichotomy for (Q,+).** Let `A <= H` with `A ~ (Q,+)`. Then either `A` fixes a
   vertex of `T'`, or `A` fixes no vertex of `T'` and fixes exactly one end `ξ` of
   `T`. In the second case each cyclic subgroup `A_m = (1/m!) Z` of `A` fixes
   pointwise a ray converging to `ξ`.
3. **Residually finite stabilizers force the parabolic case.** If the stabilizer
   in `H` of every vertex of `T` is residually finite (for example finite,
   profinite, or finitely generated linear, by Mal'cev), then every `A ~ (Q,+)` in `H` is in the
   second case. In particular, if `GL_n(Q) <= H` with `n >= 2`, each root group
   `U_ij(Q) = {e_ij(q)}` fixes exactly one end `ξ_ij` of `T` and no vertex of `T'`.

## What it says about hosts

- **Bass–Serre-type hosts.** Graphs of residually finite groups, for instance
  amalgams and HNN extensions of finitely generated linear groups and the tree
  actions used by
  Bux–Llosa Isenrich–Wu for Baumslag–Solitar groups, can contain `GL_n(Q)` only if
  every root group is parabolic. It must be an ascending union of subgroups of
  vertex groups along a ray to an end, as `Z[1/m]` sits in `BS(1,m)`. No vertex
  group can supply the divisibility.
- **The case occurs.** For one prime `p`, `PGL_2(Q)` and `Aff(Q)` act faithfully
  on the `(p+1)`-regular Bruhat–Tits tree. Their vertex stabilizers lie in compact
  open subgroups of `PGL_2(Q_p)`, so they are residually finite. The unipotent
  `(Q,+)` is parabolic there
  (`gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings`). So this is a
  constraint, not a kill.
- **Finite stabilizers kill.** With finite vertex stabilizers the second case is
  impossible too, since `A_m` is infinite cyclic and fixes a vertex of `T'`. See
  `no-q-in-tree-product-actions-with-finite-stabilizers`.
