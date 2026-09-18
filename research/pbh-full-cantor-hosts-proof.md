---
rg: 2
id: pbh-full-cantor-hosts-proof
kind: route
title: The twisted Brin--Thompson host is already full and clopen transitive, so the one-group criterion runs in both directions
target: permutational-boone-higman-iff-full-cantor-hosts
requires:
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
  - twisted-brin-thompson-finite-presentation-criterion
  - type-a-action-gives-boone-higman-for-subgroups
  - virtually-special-groups-embed-in-some-brin-thompson-group
  - cubulated-hyperbolic-groups-embed-in-some-brin-thompson-group
  - rationals-embed-in-brin-thompson-group-2v
---

Notation as in the target and in `twisted-btb-clopen-action-is-type-a`: `C = {0,1}^N`,
and for a group `G` acting on a countable set `S` the Cantor cube is `C^S`. A **brick**
is `B(u) = {κ : κ(s) has prefix u(s) for all s}` for a finitely supported
`u : S -> {0,1}^*`, `h_u : C^S -> B(u)` is prefix insertion, and `τ_g` is the coordinate
permutation. `SV_G` is the group of homeomorphisms of `C^S` for which there are brick
partitions `{B(u_i)}`, `{B(v_i)}` and `g_i in G` with `f = h_{v_i} τ_{g_i} h_{u_i}^{-1}`
on `B(u_i)`; each such piece is a **branch**. For `nV` read `S = {1, ..., n}` with
`G = 1`, so bricks are products of cones and branches are prefix maps.

**Step 0. Brick bookkeeping.** Three facts, each immediate from the definitions.
- (a) *Basis.* Bricks are clopen and form a basis of `C^S`, so every clopen set is a
  finite disjoint union of bricks and every finite clopen cover is refined by a finite
  brick partition. Both use compactness of `C^S`.
- (b) *Bisection.* `B(u) = B(u') ⊔ B(u'')`, where `u'` and `u''` extend `u` at one
  coordinate `s` by `0` and by `1`. So a disjoint union of `k` bricks can be rewritten as
  a disjoint union of `m` bricks for every `m >= k`.
- (c) *Transitivity on bricks.* For bricks `B(u)`, `B(v)` the map `h_v h_u^{-1}` is a
  homeomorphism `B(u) -> B(v)`. If both `B(u) ≠ C^S` and `B(v) ≠ C^S`, the complements
  are nonempty finite unions of bricks, so by (b) they can be written with the same
  number of bricks and paired by such maps; patching gives an element of `SV_G`
  restricting to `h_v h_u^{-1}` on `B(u)`. If `B(u) = B(v) = C^S` take the identity.
  In all cases `h_v h_u^{-1}` is `SV_G`-local, being the restriction of a group element
  in the first case and, in the mixed case `B(u) = C^S ≠ B(v)`, agreeing on each brick
  `B(w)` with the element supplied by the first case for the pair `(w, vw)`.

**Step 1. `SV_G` is full.** Let `f` be an `SV_G`-local homeomorphism of `C^S`. Each
point has a clopen neighbourhood on which `f` agrees with some element of `SV_G`. By
Step 0(a) finitely many such neighbourhoods cover `C^S` and are refined by a finite
brick partition `{B(w_j)}`. On `B(w_j)`, `f` agrees with `d_j in SV_G`, which is
branch-wise; refining `{B(w_j)}` further, again by Step 0(a), we may assume each
`B(w_j)` lies inside a single branch of its `d_j`. Then `f` is a branch on each piece of
a brick partition, and the images `f(B(w_j))` are bricks partitioning `C^S`. That is the
definition of `SV_G`, so `f in SV_G`. The same argument with `G = 1` gives fullness of
`nV`.

**Step 2. `SV_G` is clopen transitive.** Let `U, U'` be nonempty clopen. By Step 0(a)
write `U = ⊔_{i<=k} B(u_i)` and `U' = ⊔_{j<=m} B(v_j)`, and by Step 0(b) arrange
`k = m`. By Step 0(c) each `h_{v_i} h_{u_i}^{-1} : B(u_i) -> B(v_i)` is `SV_G`-local, and
a finite disjoint union of local maps is local. So there is an `SV_G`-local map
`U -> U'`. Again the same argument gives clopen transitivity for `nV`.

**Step 3. (2 => 1).** Let `H <= D` with `D` a finitely presented full clopen-transitive
Cantor host. By `fp-clopen-transitive-full-cantor-groups-have-type-a-actions` the action
of `D` on its proper nonempty clopen subsets is of type (A). So `H` embeds in a finitely
presented group with a type (A) action, which is (1).

**Step 4. (1 => 2).** Let `H <= Γ_0` with `Γ_0 ↷ S` of type (A). The action is faithful,
`Γ_0` is finitely presented, point stabilizers are finitely generated and there are
finitely many orbits of two-element subsets, so by
`twisted-brin-thompson-finite-presentation-criterion` the group `SV_{Γ_0}` is finitely
presented, is simple, and contains `Γ_0`, hence `H`. It acts on the Cantor space `C^S`,
and is full by Step 1 and clopen transitive by Step 2. That is (2).

Steps 3 and 4 give the equivalence for every group `H`, with no finite generation or
decidability hypothesis. Taking `H` to range over the finitely generated groups with
solvable word problem gives the reformulation of
`permutational-boone-higman-conjecture`.

**Step 5. Hosts and corollaries.** For `n >= 1`, `nV` is finitely presented (Brin for
`n = 2`, Hennig--Matucci in general; not read at source by this lane), and full and
clopen transitive by Steps 1 and 2. So by
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions` it has a type (A) action on
the proper nonempty clopen subsets of `C^n`, with point stabilizers `nV x nV`, and every
subgroup of `nV` lies in `B_A`. With
`virtually-special-groups-embed-in-some-brin-thompson-group`,
`cubulated-hyperbolic-groups-embed-in-some-brin-thompson-group` and
`rationals-embed-in-brin-thompson-group-2v` this gives the three corollaries stated on
the target. Each also follows from Belk--Fournier-Facio--Hyde--Zaremsky Remark 3.5 as
quoted in `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`, since `V <= nV`; the target
says so.

**Scope.** Nothing here bounds the number of orbits for `SV_G`; the counts of
`twisted-btb-clopen-action-is-type-a` apply. Nothing here is a statement about
`permutational-boone-higman-conjecture` itself beyond the reformulation: no new input is
placed in `B_A` that was not already inside a Brin--Thompson group or a type (A) actor.
