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
11. **Partially pushed leaf blocks** (bh-3manifold, 2026-09-18). *Sharpening of attempt 10;
    not constructed.* Put the `w` block in `Mod(Q, p)`, where `Q` has boundary `x` and
    `y ⊂ Q` bounds a pair of pants with `x` and the puncture `p` (the geometry of a pushed
    block). Forgetting `p` sends `T_y` to the boundary twist `T_x` of `Q̂ = Q ∪ {p}`. So
    `Π [ρ(a'_i), ρ(b'_i)] = T_x^{m'} T_y^{n'}` maps to `Π [ā'_i, b̄'_i] = T_x^{e}` in `Mod(Q̂)`
    with `e = m' + n'`, and the ratio is `m'/n' = e/n' - 1`.
    - Pure pushing is `ā'_i = b̄'_i = 1`, so `e = 0` and the ratio is `-1` (fibered).
    - With `v` pushed, non-fibered needs `e != 0`; non-virtually-fibered (reading Svetlov)
      needs `e/n' < 0` or `e/n' >= 1`.
    - If `e != 0`, the image of the block in `Mod(Q̂)` is not free, because its relator goes
      to the central `T_x^e != 1`. So freeness of the block must come from the
      point-pushing kernel: the block is a lift of a non-free surface-group image with a
      nontrivial boundary-twist relator. Such images need `T_x^e` to be a product of `h'`
      commutators in `Mod(Q̂)`. *Correction (attempt 12):* the ambient is `Mod(Q̂)`, of any
      genus `g`, not `Mod(Σ_{h',1})`. For `g >= 2`, Baykur (arXiv:1206.3512, abstract) gives
      commutator length `floor((|e|+3)/2)` for `T_∂^e`, so this is possible iff
      `|e| <= 2h' - 2`. In particular it fails for `h' = 1` and works for `h' = 2`, `e = ±1`.
    - Still open: choosing lifts whose kernel part is exactly `(T_y T_x^-1)^{-n'}`,
      freeness of the lift, and injectivity of the amalgam.
12. **Lifting the capped relator** (bh-3manifold, 2026-09-18). *Reduced to one explicit
    condition plus freeness and injectivity; not constructed.* Let `Σ' ⊂ Q̂` be the
    complement of the collar between `y` and `x = ∂Q̂`, so `∂Σ' = y` and `p` lies in the
    collar. `Mod(Σ')` meets the pushing kernel trivially, so
    `Push(pi_1(Q̂, p)) ⋊ Mod(Σ') <= Mod(Q, p)`, with `Mod(Σ')` acting on `pi_1(Q̂, p)` by based
    automorphisms. Write elements as `(u, a)`.
    - **Relator.** Take `a_1, b_1, a_2, b_2 ∈ Mod(Σ')` with `[a_1, b_1][a_2, b_2] = T_y` (Baykur,
      genus of `Σ' >= 2`), and the lifts `(u, a_1), (1, b_1), (1, a_2), (1, b_2)`. A direct
      computation gives `[(u, a_1), (1, b_1)] = (u · c(u)^-1, [a_1, b_1])` with
      `c = a_1 b_1 a_1^-1`. So the relator product is `Push(u c(u)^-1) T_y`, which equals `T_y`,
      i.e. `m' = 0`, `n' = 1`, exactly when `c` fixes `u`.
    - **Consequence.** With the `v` block pushed, that is the non-virtually-fibered case
      `m'/n' = 0` (attempt 10, item 5).
    - **Non-degeneracy.** `T_y` acts on `pi_1(Q̂, p)` as conjugation by the boundary loop
      `ℓ` (`T_y = T_x Push(ℓ)^-1`, and `T_x` acts trivially). So `T_y` is not central in the
      lifted block, as it must not be, iff `u ∉ <ℓ>`.
    - **The explicit condition.** Find a Baykur factorization in which `a_1 b_1 a_1^-1` fixes
      some based loop `u ∉ <ℓ>`, e.g. `b_1` supported on a proper subsurface `W` with
      `a_1(W)` missing a loop through the collar.
    - **Still open:** that condition, freeness of the four lifts (their capped images are
      not free), and injectivity of the amalgam with the pushed leaf.
13. **Explicit candidate** (bh-3manifold, 2026-09-18). *Item 1 of attempt 12 solved;
    freeness and injectivity open.*
    - **Source.** Baykur, arXiv:1206.3512v2 (TeX read on MSI), l.206--262: the explicit
      factorization of `t_δ^{2k}` into `k + 1` commutators by push maps and the generalized
      lantern relation. The odd powers are deferred to BKM there.
    - **An explicit `T_y` in two commutators** (same method, lantern case). Take a sphere
      with boundary `y` and holes `A_1, A_2, A_3`, glued along the holes to a connected `Z`,
      giving `Σ'` of genus `>= 2` with boundary `y`. Let `X_{ij}` be the lantern curve around
      `A_i, A_j`. Boundary twists commute with the lantern twists, so the lantern relation
      gives `T_y = (t_{X_12} t_{A_1}^-1)(t_{X_23} t_{A_2}^-1)(t_{X_13} t_{A_3}^-1)`. So
      `T_y = [t_{X_12} t_{A_1}^-1, φ] [t_{X_13}, ψ]` for `φ` with `φ(X_12) = A_2`,
      `φ(A_1) = X_23`, and `ψ` with `ψ(X_13) = A_3`. Both exist rel `∂` by change of
      coordinates: each pair consists of disjoint nonseparating curves with connected
      complement, since `Z` is connected.
    - **Lift.** Push `B_1 = φ` along the based loop `v` around `A_1` on the `y`-side of
      `X_23`. A computation like attempt 12's, for a push on the second entry, gives
      `[(1, a), (v, b)] = (a(v) [a, b](v)^-1, [a, b])`. So the relator is exactly `T_y` iff
      `(b a b^-1)(v) = v`. Here `b a b^-1 = t_{A_2} t_{X_23}^-1`, and `v` misses `A_2` and
      `X_23`, so the lifted relator is `T_y`: `m' = 0`, `n' = 1`. Also `v ∉ <ℓ>`, since `A_1`
      is essential.
    - **Lattice matching.** With the pushed leaf `(Push(pi_1 Y_v), T_y)` and the lifted leaf
      `H x <T_x>`, both boundary tori are `<T_x, T_y>`, since `(-1, 1), (0, 1)` and
      `(0, 1), (1, 0)` are both bases. The boundary words `(-1, 1)` and `(0, 1)` are not
      parallel, so the abstract amalgam is a non-fibered two-leaf graph manifold group
      (`two-leaf-graph-manifold-twist-realizations`, item 1). By item 2 (the Svetlov
      reading) it is not virtually fibered.
    - **Host.** `S = Σ' ∪_y P ∪_x Y'_v`, with `P` the pair of pants containing the puncture
      `p`. It is punctured, so `Mod(S)` is in `B_A`.
    - **Open:** (a) `H = <t_{X_12} t_{A_1}^-1, Push(v) φ, t_{X_13}, ψ>` is free of rank 4.
      Its image in `Mod(Σ')` is not free; kernel elements of exponent sum zero in the
      relator map to nontrivial push products `Π Push([u_i, ℓ])`, which is encouraging but
      proves nothing. (b) Injectivity of the amalgam. Candidate tools, untried: ping-pong
      on the curve complex (Koberda / Clay--Mangahas type combination theorems), or
      Bass--Serre theory for the pushed leaf through the Birman exact sequence.
14. **Correction to attempt 13: that `H` is not free** (bh-3manifold, 2026-09-18).
    - **Why.** `t_{X_12} t_{A_1}^-1`, `t_{X_13}` and `ψ` lie in `Mod(Σ')`, so they commute with its
      boundary twist `T_y`, the image of the relator `r = [a_1, b_1][a_2, b_2]`. So
      `[r, a_1] != 1` in `F_4` maps to `1`, and the candidate of attempt 13 fails at (a).
    - **Criterion.** In `Push(pi_1(Q̂, p)) ⋊ Mod(Σ')`, `(u, a)` commutes with `(1, T_y)` iff
      `u ∈ <ℓ>`. `T_y` acts by conjugation by `ℓ^{±1}`, and `ℓ`, the boundary loop, generates
      its own centralizer.
    - **Necessary condition for any freely lifted block.** In a free group the centralizer
      of `r` is `<r>`. So every element of the lifted block whose push part lies in `<ℓ>`
      must be a power of the relator image. In particular all four generators need push
      parts outside `<ℓ>`, not just one.
    - **What survives.** The factorization, the lattice matching and the host are unaffected.
      What is needed is a lift `(u_i, A_i), (v_i, B_i)` with all push parts outside `<ℓ>`,
      relator exactly `T_y`, and the centralizer condition above.
    - **Multiplier freedom.** Each generator may be multiplied by an element of its
      partner's centralizer, e.g. `B_1 -> B_1 ζ` with `ζ ∈ C(A_1)`. This keeps the relator
      and the attempt-13 fixed-loop condition. Such multipliers in `Mod(Σ')` do not add
      push parts, so they cannot cure the defect alone. Not constructed.
15. **Pushing all four generators** (bh-3manifold, 2026-09-18). *Simplest method dies for
    every lantern-based factorization; general case handed to bh-free-21.*
    - **Formula.** In `Push ⋊ Mod(Σ')` with `(u, a)(v, b) = (u·a(v), ab)`, the commutator
      `[(u, a), (v, b)]` is `(P, [a, b])` with `P = u · a(v) · c(u)^-1 · [a, b](v)^-1`, where
      `c = a b a^-1`. For two pairs the relator is `(P_1 · [a_1, b_1](P_2), T_y)`.
    - **Common fixed loops.** If `a(w) = b(w) = w`, the lifts `(w^k, a)` and `(w^j, b)` give
      `P = 1` for all `k, j`. So a pair with a common fixed based loop `w ∉ <ℓ>` can be pushed
      without changing the relator.
    - **Why it dies.** The first pair `[t_X t_{A_i}^-1, φ]`, with `φ(X) = A_j` and
      `φ(A_i) = Y`, always involves two lantern curves `X != Y`, which share exactly one hole.
      A loop fixed by the pair misses `X`, `A_i`, `A_j` and `Y`. From the collar of `y` such a
      loop stays on the `y`-side of both `X` and `Y` and cannot leave the lantern sphere
      through a hole without crossing one of them. So it lies in `<ℓ>`.
    - **Remaining freedom.** Twisted solutions of `P_1 · [a_1, b_1](P_2) = 1` with `P_i != 1`;
      non-lantern factorizations of `T_y` whose pairs have common fixed loops; the
      centralizer condition of attempt 14; then freeness and injectivity.
    - **Handoff.** The whole two-leaf test case is handed to bh-free-21 (see its board).
