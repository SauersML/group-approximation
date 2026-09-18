---
rg: 2
id: nonfibered-graph-manifold-groups-have-no-fg-normal-subgroups
kind: claim
title: A closed graph manifold group with non-trivial JSJ decomposition and no fibered finite cover has no finitely generated normal subgroup of infinite index except the trivial one, so it meets every normal free or surface subgroup of a host trivially or in an infinitely generated subgroup
distinct_from:
  nonfibered-closed-graph-manifold-groups-satisfy-pbh: that is the open membership in B_A for these groups; this is a structural constraint on every host embedding of them, and it proves no membership.
  virtually-fibered-3-manifold-groups-satisfy-pbh: that embeds a fibered group through a Birman point-pushing kernel, meeting it in the fiber group, a finitely generated normal subgroup; this shows that such an intersection cannot occur for the groups left open.
  three-manifold-groups-linear-unless-closed-graph-manifold: that imports linearity for most 3-manifold groups; this imports the Hempel--Jaco classification of finitely generated normal subgroups.
---

**ESTABLISHED** (lane proof, elementary given one cited theorem; not independently
reviewed; no novelty claimed, since item 1 is immediate from the cited theorem).

## Setting

Let `N` be a closed orientable graph manifold with non-trivial JSJ decomposition
that has no finite cover fibering over the circle, the class of
`nonfibered-closed-graph-manifold-groups-satisfy-pbh`. Every finite cover of `N`
is again of this kind.

## Statement

1. **No finitely generated normal subgroups of infinite index.** If `L` is a
   finitely generated normal subgroup of `pi_1(N)`, then `L = 1` or `L` has finite
   index.
2. **Host constraint.** Let `pi_1(N) <= H` and let `K` be a normal subgroup of `H`
   that is free or the fundamental group of a surface. Then `pi_1(N) ∩ K` is
   trivial or infinitely generated.
3. **Birman kernels.** Suppose a finite-index subgroup of `pi_1(N)` embeds in a
   pure mapping class group `PMod(S_{g,n})` with `n >= 1` and `chi(S_{g,n-1}) < 0`.
   Then either the image meets the point-pushing kernel `pi_1(S_{g,n-1})` of the
   Birman exact sequence trivially, in which case the forgetful map embeds it in
   `PMod(S_{g,n-1})`, or it meets that kernel in an infinitely generated free or
   surface subgroup that is normal in the image. Iterating while the Birman sequence applies, some finite-index subgroup of
   `pi_1(N)` embeds in a closed-surface group `Mod(S_g)` with `g >= 2`, or at some
   stage the intersection with a point-pushing kernel is infinitely generated. (The
   iteration cannot stop anywhere else: the remaining pure mapping class groups are
   finite or virtually free, and contain no group of cohomological dimension 3.)
4. **Inner automorphisms.** If `pi_1(N) <= Aut(F_m)` with `m >= 2`, then
   `pi_1(N) ∩ Inn(F_m)` is trivial or infinitely generated. In the first case
   `pi_1(N)` embeds in `Out(F_m)`.

## Proof

**Cited input.** Aschenbrenner--Friedl--Wilton, *3-manifold groups*,
arXiv:1205.0202, item (K.9), l.3463--3470 of the TeX source (read on MSI):
"Let N be a compact orientable 3-manifold, and let Γ be a normal finitely
generated non-trivial subgroup of π1(N) of infinite index. Work of Hempel--Jaco
[HJ72, Theorem 3], the resolution of the Poincaré Conjecture, [...] imply that
one of the following conclusions hold: (a) N is Seifert fibered and Γ is a
subgroup of the Seifert fiber subgroup, or (b) N fibers over S^1 with surface
fiber Σ and Γ is a finite-index subgroup of π1(Σ), or (c) N is the union of two
twisted I-bundles over a compact connected surface Σ which meet in the
corresponding S^0-bundles and Γ is a finite-index subgroup of π1(Σ)."

**Item 1.** Suppose `L != 1` is finitely generated, normal and of infinite index.
- (a) is impossible: a closed Seifert fibered manifold has trivial JSJ
  decomposition, and `N` does not.
- (b) is impossible: `N` itself would fiber.
- (c) is impossible: a union of two twisted I-bundles over `Σ` along their
  `S^0`-bundles is double covered by a `Σ`-bundle over the circle, so `N` would
  be virtually fibered.

**Item 2.** `L = pi_1(N) ∩ K` is normal in `pi_1(N)`. If `L` had finite index,
then `pi_1(N)` would be virtually a subgroup of a free or surface group, of
cohomological dimension at most 2. But `N` is closed and aspherical (graph
manifolds with non-trivial JSJ decomposition are irreducible with infinite
fundamental group; AFW (C.1)), so `cd pi_1(N) = 3` and every finite-index
subgroup also has `cd = 3`. So `L` has infinite index, and item 1 makes it
trivial or infinitely generated.

**Item 3.** Apply item 2 to the finite-index subgroup `G'` (itself the group of
a manifold in the same class) and to `K = pi_1(S_{g,n-1})`, the point-pushing
kernel of the Birman exact sequence
`1 -> pi_1(S_{g,n-1}) -> PMod(S_{g,n}) -> PMod(S_{g,n-1}) -> 1`. If `G' ∩ K = 1`,
the forgetful map is injective on `G'`. Iterate on `n`. The last step, `n = 1`,
has closed-surface kernel `pi_1(S_g)` for `g >= 2`.

**Item 4.** `Inn(F_m) ≅ F_m` for `m >= 2` is normal in `Aut(F_m)`; apply item 2,
and note `Aut(F_m)/Inn(F_m) = Out(F_m)`.

## What this says about the open case

- **The fibered transplant cannot be adapted.** `virtually-fibered-3-manifold-pbh-proof`
  embeds the group through a Birman sequence so that it meets the point-pushing
  kernel exactly in the fiber group, which is finitely generated, normal, and of
  infinite index. By item 1 no such subgroup exists here.
- **Mapping class group hosts.** Punctured-surface mapping class groups are in
  `B_A` (`punctured-surface-mcgs-satisfy-permutational-boone-higman`), so an
  embedding of a finite-index subgroup of `pi_1(N)` in one would settle the open
  node. By item 3, any such embedding either survives forgetting all punctures,
  giving an embedding in a closed-surface `Mod(S_g)` (whose own Boone--Higman
  status is the open `closed-surface-mapping-class-groups-satisfy-boone-higman`),
  or meets some point-pushing kernel in an infinitely generated normal subgroup.
  So a successful mapping class group construction must use genuinely
  infinitely generated normal intersections, unlike the point-pushing construction
  used for the fibered case.
- **Aut(F_m) hosts** (in `B_A` by `aut-free-groups-satisfy-permutational-boone-higman`):
  the same dichotomy with `Out(F_m)` in place of the closed-surface group.

No membership in `B_A` is proved or refuted here.
