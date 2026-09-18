---
rg: 2
id: nonfibered-closed-graph-manifold-groups-satisfy-pbh
kind: claim
title: Fundamental groups of closed graph manifolds that are not virtually fibered lie in the permutational Boone--Higman class
distinct_from:
  three-manifold-groups-pbh-off-nonfibered-graph-manifolds: that proves membership in B_A for every compact 3-manifold outside this class; this is exactly the class left over.
  virtually-fibered-3-manifold-groups-satisfy-pbh: that handles graph manifolds with a fibered finite cover; this is the ones with none, where no fibre exists to embed in a mapping class group.
  compact-3-manifold-groups-satisfy-pbh: that is the statement for all compact 3-manifolds; this is its only missing case.
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

**OPEN.** Let `N` be a closed orientable graph manifold with non-trivial JSJ
decomposition that has no finite cover fibering over the circle. Then `pi_1(N)`
is in `B_A`, the class of `boone-higman-type-a-class-closed-under-finite-extensions`.

Such `N` are not non-positively curved (Svetlov; AFW arXiv:1205.0202, l.3327),
so `pi_1(N)` is not virtually special (AFW `thm:liu11`).

**Why it matters.** By `three-manifold-groups-pbh-off-nonfibered-graph-manifolds`,
this is the only case missing from `compact-3-manifold-groups-satisfy-pbh`. A
plain Boone--Higman envelope for these groups would not settle that claim,
because the plain class is not known to be closed under free products or finite
extensions.

## Attempts

1. **Linearity in characteristic zero.** *Open in the literature.* Douba,
   arXiv:2101.06797, l.206: "it is not known if a single non-NPC graph manifold
   without Sol geometry admits a faithful finite-dimensional linear
   representation over a field of characteristic zero." A faithful
   representation would settle this case through
   `char-zero-linear-groups-satisfy-permutational-boone-higman`.
2. **Positive characteristic, unitary.** *Dead.*
   - Same line: Button proved that a finitely generated group linear in positive
     characteristic acts properly by semisimple isometries on a complete CAT(0)
     space, and Leeb showed this forces a graph manifold to be NPC.
   - For one JSJ torus and product blocks, the abstract rules out faithful
     unitary representations as well.
   - A mixed-characteristic product embedding (as in
     `quasi-linear-groups-satisfy-permutational-boone-higman`) would need its
     characteristic-zero factor to be faithful on the kernel of the others. Not
     examined.
3. **Mapping class group of the fibre.** *Unavailable by hypothesis.* The
   fibered argument of `virtually-fibered-3-manifold-pbh-proof` needs a fibre.
4. **Rigid permutation groups of the JSJ tree (BLIW, arXiv:2408.05673).** *Dead as
   stated.* Their rigid permutation groups are defined for groups acting on
   locally finite graphs (TeX l.283, l.287, l.360). The JSJ Bass--Serre tree has
   edge groups `Z^2` of infinite index in the Seifert vertex groups, so it is not
   locally finite.
5. **HNN realization on an actor's set.** *Unclear.*
   `stable-permutation-hnn-of-type-a-actor-is-type-a` needs the edge group to
   have finitely many orbits on the actor's set. For an edge group `Z^2`, no type
   (A) actor containing a Seifert vertex group on such a set is known.
6. **Other mapping class group hosts.** *Untested.* Does `pi_1(N)` embed in
   `Mod(S)` for some punctured surface `S`, with the Seifert blocks
   `F_v x Z` realized by point-pushing subgroups and multitwists? That would put
   it in `B_A` through `punctured-surface-mcgs-satisfy-permutational-boone-higman`.
   The literature searched records no such embedding.
   - **Context.** AFW arXiv:1205.0202, l.3341--3344: "Bridson [Brd12, Corollary
     5.2] [...] showed that if a group has a subgroup of finite index that embeds
     in a RAAG, then it embeds in the mapping class group for infinitely many
     closed surfaces. [...] 'Most' 3-manifold groups thus can be viewed as
     subgroups of mapping class groups."
   - **Why it doesn't transfer.** That route goes through RAAGs. Groups in this
     class are not virtually special, and the closed-surface targets are not
     known to be in `B_A` (`closed-surface-mapping-class-groups-satisfy-boone-higman`).
7. **Normal-subgroup constraint on hosts** (bh-3manifold, 2026-09-18). *Constraint,
   not a construction.* By `nonfibered-graph-manifold-groups-have-no-fg-normal-subgroups`
   (Hempel--Jaco via AFW (K.9)), these groups have no finitely generated normal
   subgroup of infinite index other than `1`. So they meet every normal free or
   surface subgroup of a host trivially or in an infinitely generated subgroup.
   - This is exactly why attempt 3 fails: the fibered transplant meets the Birman
     point-pushing kernel in the fiber group.
   - For attempt 6, any embedding of a finite-index subgroup in a punctured-surface
     mapping class group either survives forgetting every puncture, giving an
     embedding in some closed `Mod(S_g)` with `g >= 2`, or meets a point-pushing
     kernel in an infinitely generated normal subgroup. Aut(F_m) hosts give the
     same dichotomy with `Out(F_m)`.
   - Remaining gap: a host embedding with infinitely generated normal
     intersections, or Boone--Higman in `B_A` for closed-surface mapping class
     groups or `Out(F_m)` together with an embedding into one of them.
8. **Common-retract amalgams over the JSJ splitting** (bh-3manifold, 2026-09-18).
   *Dies* for every closed graph manifold. `pbh-class-closed-under-common-retract-amalgams`
   part 2 puts finite trees of `B_A` groups with retract edge groups in `B_A`.
   - **Cycles.** If the JSJ graph has a cycle, no finite cover has a tree as JSJ graph:
     the map `pi_1(N) -> pi_1(graph)` restricts nontrivially to every finite-index
     subgroup and factors through the quotient graph of its tree action. A cycle needs
     an HNN extension identifying two different edge subgroups, which that node's Scope
     excludes.
   - **Leaves.** If the JSJ graph is a tree, a leaf piece `M_v` has one boundary torus
     `E = <c, t>`. Some `c^m t^n != 1` lies in `[G_v, G_v]`: the image of `E` in
     `H_1(M_v; Q)` has rank one (the boundary curve is a product of commutators and
     cone-point classes, which are rationally multiples of the fiber). A retraction of
     any overgroup `G'_v >= G_v` onto an abelian subgroup containing `E` kills
     `[G'_v, G'_v]`, which contains `c^m t^n`. So the leaf edge group is a retract of no
     overgroup of the leaf vertex group.
   - **Nonabelian amalgamating subgroups.** Enlarging the leaf edge group to a
     nonabelian `C` with `C ∩ G_v = E` also fails for the product-form enlargements
     `G'_v = G_v x D`, `C = {(chi(d), d)}` (which need an endomorphism of `G_v` through
     `D` with fixed subgroup exactly `E`, e.g. a pseudo-Anosov of the leaf base): on the
     neighbor's side `chi` must send the image of `F_v` into the centralizer of a
     non-fiber element of the neighbor's edge torus, which is abelian, so it kills the
     boundary word `c` it must preserve. Other enlargements are untested.
9. **Local product hosts** (bh-3manifold, 2026-09-18). *Dies* for a whole design class.
   By `fiber-detecting-block-characters-force-npc-graph-manifolds` (Svetlov's charge and
   Theorem III, read at source), in every finite cover some block has nonzero charge: its
   fiber is, rationally and modulo commutators of the block, a combination of the
   neighbors' fibers. So no embedding can send each block into a subgroup with a character
   that sees its own fiber and kills its neighbors' fibers, e.g. `K_v x A_v` with the fiber
   in the abelian factor, or twist realizations in a mapping class group with each fiber a
   twist about curves disjoint from the rest of the block's support. Designs must instead
   produce such a rational fiber relation, e.g. through chain or lantern relations. Untested.
10. **Twist realizations of charged two-leaf examples** (bh-3manifold, 2026-09-18).
    *Reduced, not constructed.* `two-leaf-graph-manifold-twist-realizations`:
    - For two leaf blocks, fibering is parallelism of the two boundary words in the JSJ
      torus, and (reading Svetlov) non-virtual-fibering is `β_v β_w ∉ (0, 1]`.
    - If the torus goes to a two-curve twist group `<T_x, T_y>` of `Mod^+(S)`, each fiber
      is a power of one twist. Point pushing on both sides lands exactly on the fibered case.
    - What remains is a single design problem: a leaf block with `ρ(F_w) <= Stab^+(x)` free
      of rank `2h'`, whose relator product is `T_x^{m'} T_y^{n'}` with boundary slope ratio
      `m'/n' ∉ [-1, 0)` (pushing gives `-1`), plus injectivity of the amalgam. A solution
      with `S` punctured would put that example in `B_A`.
