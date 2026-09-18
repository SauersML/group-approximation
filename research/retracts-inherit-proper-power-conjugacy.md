---
rg: 2
id: retracts-inherit-proper-power-conjugacy
kind: claim
title: A retract inherits every proper-power conjugacy of its own elements, so the edge groups of both Higman splittings are retracts of neither side and the permutational closure theorems cannot be applied to Higman's group
distinct_from:
  pbh-class-closed-under-common-retract-amalgams: that is the closure theorem for amalgams whose edge group is a retract of both sides; this shows its hypothesis fails for every splitting of Higman's group that main records, so the theorem cannot be applied there.
  higman-group-splits-as-amalgams-over-free-subgroups: that establishes the two amalgam decompositions; this shows their edge groups are not retracts, so those decompositions feed no closure theorem on main.
  type-a-actors-have-no-proper-power-cyclic-edge-splittings: that excludes proper-power cyclic edge groups for an actor's own splittings; this is about retractions onto arbitrary edge groups and about which permanence theorems apply, not about type (A) actions.
  homogeneous-conjugation-invariants-vanish-on-bs-bases: that is the invariant lemma and its CAT(0) host exclusions; this is the retraction lemma and the method-kill for the closure engine.
---

**ESTABLISHED** by `higman-closure-theorems-inapplicable-proof` (lane proof,
elementary, not reviewed; no priority claimed).

## 1. The retraction lemma

Let `C <= G` and let `rho : G -> C` be a retraction, so `rho(c) = c` for all
`c in C`. If `c in C` and `g in G` satisfy `g c g^-1 = c^n`, then
`rho(g) c rho(g)^-1 = c^n` with `rho(g) in C`. So **a retract inherits every
proper-power conjugacy of its own elements.**

Consequently `C` is not a retract of `G` whenever some `c in C` of infinite
order is conjugate in `G` to `c^n` with `|n| >= 2` and `C` has no element of
infinite order conjugate in `C` to a proper power of itself. Groups with the
latter property include:

- free groups (cyclically reduced length is a conjugacy invariant, and
  `c` and `c^n` have different cyclically reduced lengths for `c != 1`);
- torsion-free hyperbolic groups, and more generally any group all of whose
  infinite-order elements have positive stable translation length in some
  isometric action, by
  `homogeneous-conjugation-invariants-vanish-on-bs-bases`;
- every group acting properly and cocompactly by isometries on a complete
  CAT(0) space, by item 3 of that node.

## 2. Higman's group: the edge groups are not retracts

Write `H4 = <g_0, g_1, g_2, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2, i in Z/4>`
and use the letters `a, b, c, d` for `g_0, g_1, g_2, g_3`. By
`higman-group-splits-as-amalgams-over-free-subgroups`,

    H4 = G_1 *_(F_ac) G_2 = G_3 *_(F_bd) G_4,

with `G_1 = <a, b, c>`, `G_2 = <c, d, a>`, `F_ac = <a, c>` free of rank two,
and similarly for the second splitting.

- In `G_1` the relation `c^b = c^2` makes `c` conjugate to `c^2`, and
  `c in F_ac`. By item 1, `F_ac` is not a retract of `G_1`.
- In `G_2` the relation `a^d = a^2` makes `a` conjugate to `a^2`, and
  `a in F_ac`. So `F_ac` is not a retract of `G_2` either.
- The second splitting is the image of the first under the order-four symmetry
  `a -> b -> c -> d -> a`, so `F_bd` is a retract of neither `G_3` nor `G_4`.
- For the index-two overgroup `E = G_1 *_F (F x|_theta Z/2)` of
  `higman-group-is-the-swap-twisted-double-of-a-bs-amalgam`, `F` is not a
  retract of `G_1` by the same computation, and it is not a retract of
  `F x|_theta Z/2` either: a retraction would make the swap `theta` an inner
  automorphism of `F`, but `theta` exchanges a free basis and so acts
  nontrivially on `F^ab`, while inner automorphisms act trivially there.

## 3. Higman's group is not an HNN extension

`H4` is perfect: the relations give `g_(i+1) = 2 g_(i+1)` in `H4^ab`, so every
generator dies. Every HNN extension `<A, t | t c t^-1 = phi(c), c in C>` admits
the homomorphism onto `Z` sending `t` to `1` and `A` to `0`. So `H4` is not an
HNN extension over any base, ascending or not.

## 4. What this kills

None of the permanence theorems on main can be applied to `H4` through its own
decompositions:

- `pbh-class-closed-under-common-retract-amalgams` needs the edge group to be a
  retract of both sides, and by item 2 it is a retract of neither, in both
  splittings and in `E`;
- `pbh-class-closed-under-graph-products` is the special case
  `Y = C x K` of that theorem, so it fails for the same reason;
- clause (T) of `pbh-class-closed-under-relative-holomorphs` produces ascending
  HNN extensions, and by item 3 `H4` is not one.

The same computation applies to the chain splittings of the Baumslag--Gersten
group, whose edge group `<a>` satisfies `a ~ a^2` inside its vertex group
`BS(1,2)`.

## 5. Scope

This is a method-kill, not an obstruction. The permutational class `B_A` is
closed under subgroups, so `H4` may well lie in `B_A` without being built from
its own splittings by these theorems. What item 4 says is that the closure
engine on main needs a different input for `H4`: either a one-sided retract
theorem, or an amalgam closure that tolerates an edge-group element conjugate
to a proper power on both sides.
