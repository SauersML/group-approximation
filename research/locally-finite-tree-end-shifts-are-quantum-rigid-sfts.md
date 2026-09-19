---
rg: 2
id: locally-finite-tree-end-shifts-are-quantum-rigid-sfts
kind: claim
title: For a cocompact action on a locally finite tree with finitely generated vertex stabilizers, the end shift over the group is a quantum-rigid SFT; it is topologically free exactly when the action is strongly faithful, and then every vertex stabilizer and every (FA) subgroup is residually finite
distinct_from:
  free-group-boundary-shifts-are-quantum-rigid: that treats groups whose Cayley graph is a tree, where every vertex stabilizer is trivial; this allows infinite finitely generated vertex stabilizers, which the coding absorbs by a descent step, and so reaches non-residually-finite groups such as BS(2,3).
  v-times-tree-boundary-full-groups-are-f-infinity: that proves the finiteness gate for the trivial-stabilizer scaffold; this proves the rigidity gate for the whole class of Bux–Llosa Isenrich–Wu, whose finiteness theorem is the tree analogue of gate E3′.
  kazhdan-simple-groups-act-only-on-exotic-2d-buildings: that shows hard inputs act trivially on trees; this shows the same wall from the coding side, since every elliptic subgroup of a topologically free tree coding is residually finite.
---

**ESTABLISHED** through `locally-finite-tree-end-shift-rigidity-proof` (lane bh-star-a, 2026-09-18;
elementary lane proof, not reviewed). No priority is claimed for the coding or for the residual
finiteness remark, both of which are folklore. The new point is quantum rigidity with infinite vertex
stabilizers. Quantum rigidity (conditions Q1–Q3) is as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Setting

- `Λ` is a group with a finite symmetric generating set `S`.
- `T` is a locally finite tree without leaves. `Λ` acts on `T` without inversions and with finitely many
  orbits of edges, and every vertex stabilizer is finitely generated.
- `F` is a finite subtree containing one vertex `v_i` of each vertex orbit (`i = 1, …, r`). `E(w)` is
  the (finite) set of edges at a vertex `w`.

**The end shift.** The alphabet is `A = E(v_1) × … × E(v_r)`. Read `x(g)_i = e` as "the out-edge at
`g v_i` is `g e`". `X_T ⊆ A^Λ` is cut out by two finite families of rules:
- (R1) **descent:** `x(gk)_i = k^(-1) x(g)_i` for each `i` and each `k` in a fixed finite generating set
  `K_i` of `Stab(v_i)`;
- (R2) **edges:** for each edge-orbit representative `ε_0 = {v_i, h v_j}` (a fixed `h ∈ Λ`), exactly one of
  `x(g)_i = ε_0` and `x(gh)_j = h^(-1) ε_0` holds.

Every rule relates two sites at distance at most `D_0 := max(|k|, |h|)` over the finitely many `k`, `h`.

## Statement

1. **Coding.** `X_T` is an SFT over `Λ`, and it is `Λ`-equivariantly homeomorphic to the end space `∂T`.
2. **Rigidity.** For every `D ≥ D_0` and every field, `X_T` is `D`-quantum rigid.
3. **Dynamics.** If `T` has more than two ends and the action is minimal (no invariant proper subtree),
   with no fixed end:
   - `X_T` is a minimal Cantor system;
   - it is **topologically free** iff the action is **strongly faithful** in the sense of Bux–Llosa
     Isenrich–Wu (no nontrivial element fixes a half-tree pointwise);
   - its isotropy is torsion-free iff no nontrivial element of finite order fixes an end.
4. **Limits.** If `X_T` is topologically free, then:
   - every vertex stabilizer embeds in the profinite group `Aut(T)_v`, and so is residually finite;
   - every finitely generated subgroup of `Λ` with Serre's property (FA) fixes a vertex, and so is
     residually finite. In particular a group with (FA) and no nontrivial finite quotient embeds in no
     such `Λ` except trivially.

## Instances (the gate (★′) of the master route)

`(★′)` asks for a quantum-rigid, minimal, topologically free SFT with torsion-free isotropy over a
finitely presented group (`master-route-needs-only-topological-freeness`). Each group below is
finitely presented and satisfies it by items 1–3.

1. **`BS(m,n) = ⟨a, t | t a^m t^(-1) = a^n⟩` with `2 ≤ |m| ≠ |n|`.**
   - The tree is `(|m|+|n|)`-regular with one vertex orbit and stabilizer `⟨a⟩`. So `X_T` is a
     nearest-neighbour SFT with `|m|+|n|` letters, rigid at `D = 1`.
   - It is strongly faithful: an elliptic element fixes all edges at a vertex only if its exponent is
     divisible by `lcm(m,n)`, and crossing an edge rescales the exponent by `m/n` or `n/m`. Every
     half-tree contains arbitrarily long paths of either type, so a prime with `v_p(m) ≠ v_p(n)` drives
     the valuation negative (route, §7).
   - `BS(m,n)` is torsion-free.
   - These are the **first recorded instances of (★′) over groups that are not residually finite**, e.g. `BS(2,3)`.
2. **Bux–Llosa Isenrich–Wu's class.** Take a finite graph of groups with finitely presented vertex groups
   and finite-index edge groups whose Bass–Serre tree action is strongly faithful, minimal and without a
   fixed end. (Ascending HNN extensions fix an end; BLIW embed them in larger such groups first.) By
   `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`, their Theorem `thm:main-graphs-of-groups`
   embeds these in simple groups of type `F_n` (read at source, `$GQ/src/bh-free-05/bliw-2408.05673v2.tex`).
   - Here `X_T` is a rigid, minimal, topologically free SFT.
   - Their rigid permutation group `RP_G(T)` maps to the topological full group of `Λ ⋉ ∂T`, and by
     strong faithfulness the kernel is the finitary permutations of vertices. Their remark after the
     definition of `RP_G` expects their finiteness proof to apply to that full group.
   - So their theorem is the tree case of the finiteness gate E3′
     (`v-times-rigid-topologically-free-sft-full-groups-are-fp`) in a neighbouring form, and this node
     supplies the rigidity half.
3. **`PSL_2(Z[1/p])` on its Bruhat–Tits tree, for `p = 2`, `p = 3` and primes `p ≡ 11 mod 12`.**
   - Vertex stabilizers are `PSL_2(Z)` and a conjugate, so they are finitely generated.
   - The boundary is `P^1(Q_p)`, and a nontrivial Möbius map has at most two fixed points, so the action
     is topologically free.
   - The group has torsion, of orders 2 and 3. An element of order 2 fixes a point of `P^1(Q_p)` iff
     `x^2 + 1` has a root in `Q_p`, i.e. `p ≡ 1 mod 4`. An element of order 3 fixes one iff `x^2 + x + 1`
     does, i.e. `p ≡ 1 mod 3`.
   - Neither holds for `p = 2, 3`. So for `p = 2, 3, 11, 23, 47, …` the isotropy is torsion-free, although
     the group is not.
4. **Products.** Finite products of the above, by `quantum-rigidity-is-product-stable`. Coupled
   (non-product) codings over lattices in products of trees are
   `tree-product-lattices-carry-rigid-topologically-free-sfts`.

## What this does and does not give

- **Calibration, not new BH.** Boone–Higman is already known for every group above (Bux–Llosa
  Isenrich–Wu; Zaremsky for `Q`-linear groups). What is new is that Track A's crux object exists over
  them, with rigidity supplied by compression and no determinism. In particular it exists over the
  non-residually-finite `BS(2,3)`.
- **The wall is item 4.** Topological freeness makes every elliptic subgroup profinitely faithful. A tree
  coding therefore carries non-residually-finite groups only through **scaling** (hyperbolic elements), never
  through **isotropy**. By `kazhdan-simple-groups-act-only-on-exotic-2d-buildings`, a hard input acts
  trivially on every tree, so it would be elliptic. Hence no locally finite tree coding, and no product of
  them, carries an input with a non-residually-finite (FA) subgroup.
- **Infinite valence.** At a vertex `w` of infinite valence the out-edge label ranges over an infinite
  set. Coded with finitely many letters (one bit per edge, as for `Z/2 ∗ B`), the orientation at `w`
  becomes the one-or-less condition "at most one edge at `w` points away" over `Stab(w)`, and `w` itself
  becomes a point of the space. That condition is not of finite type over an infinite `Stab(w)`. It is
  the infinite-emitter gate (IE) of the master route
  (`simple-inputs-have-finitely-presented-stabilizer-engines`).

## Lesson for general BH

Tree compression is **profinite scaling**.
- At finite valence it is always rigid: descent along vertex stabilizers plus monotone projection chains,
  with no hypothesis on the stabilizers beyond finite generation. So (★′) holds on the whole
  Bux–Llosa Isenrich–Wu class, including non-residually-finite groups.
- Topological freeness forces every elliptic subgroup to embed in a profinite group.
- So tree-type codings reach non-residually-finite inputs only through their hyperbolic, scaling part.
  Every input whose (FA) subgroups are not residually finite, in particular every simple Kazhdan input,
  needs a point of infinite valence (gate IE) or a non-tree compression (exotic buildings).

DERIVATION
locally-finite-tree-end-shift-rigidity-proof

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS

I checked `locally-finite-tree-end-shift-rigidity-proof` line by line.

- **§1.**
  - Out-edges are well defined, via (R1) and its inverse letters.
  - (R2) orients each edge from exactly one endpoint, and no inversions makes the representation
    `gε_0` consistent. The free-group Step 0 then gives ends.
  - `ξ ↦ x_ξ` is continuous, since the cylinders are shadows, and bijective between compact
    Hausdorff spaces.
- **§2.**
  - Lemma 1 is correct.
  - Lemma 2 is correct: descent along `K_i` by the two-sided ball-sum identity, with inverse letters
    applied at `gk^(-1)`. So `O_w(ε)` is well defined.
- **§3.** Lemma 3 is correct.
- **§4.** Steps 2–3 of `free-group-boundary-shift-rigidity-proof` are purely algebraic. The only
  inputs are orthogonality at a vertex and the edge identity, and I re-derived the chain and the
  four commutation cases. So they run on `T` for any degrees.
- **§5.** Both directions of topological freeness ⟺ strong faithfulness are correct:
  - a nontrivial `g` fixing an infinite perfect `∂H` pointwise is elliptic;
  - such an elliptic element fixes geodesics between fixed ends, hence the half-tree `H'`.
- **§6.** A topologically free action is faithful, and `Aut(T)_v` is profinite. (FA) subgroups fix
  vertices.
- **§7, BS(m,n).**
  - The edges at `A` are `a^iC` (`i mod m`) and `a^itC` (`i mod n`), fixed by `a^j` iff `m | j`,
    resp. `n | j`.
  - Crossing rescales the exponent by `n/m`, resp. `m/n`, using `a^m = b^n` with `b = t^(-1)at`.
  - Pure forward paths exist.
  - The `p`-adic descent contradicts pointwise fixing when `v_p(m) ≠ v_p(n)`.
  - There is no fixed end, since end stabilizers are abelian-by-cyclic and `BS(m,n) ⊇ F_2`.
- **§8, PSL₂(Z[1/p]).**
  - Integral trace in `[−2,2]` gives orders `1, 2, 3`.
  - The eigenvalue criterion: `i ∈ Q_p` iff `p ≡ 1 mod 4`, and `ζ_3 ∈ Q_p` iff `p ≡ 1 mod 3`.
  - So isotropy is torsion-free exactly for `p = 2, 3` and `p ≡ 11 mod 12`.

**Minor.** In §7, the edge `C` joins `A` to `t^(-1)A`. So with `ε_0 = C` the edge rule relates `g`
and `gt^(-1)`, not `gt`; alternatively take `ε_0 = tC`. `D_0 = 1` either way.

**Not checked:**
- the "first recorded instances" priority claim for `BS(2,3)`;
- Instance 2's relation between Bux–Llosa Isenrich–Wu's `RP_G(T)` and the full group;
- the companion node `tree-product-lattices-carry-rigid-topologically-free-sfts`;
- the artifact `gq-bh-star-a-clapham-square-report.md`, which landed in the same commit.
