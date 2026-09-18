---
rg: 2
id: relative-seeds-over-free-products-have-finite-ropes
kind: claim
title: A relative seed over a group acting on a tree with trivial edge stabilizers is determined on every far branch by one bounded entry datum; so over a free group the seeded subgroup is finitely generated, over P * Q it meets only finitely many (C∩P)-cosets of conjugates of Q, and the Aanderaa–Cohen rope has no relative seed over Z^2 * Z
requires:
  - relative-seeds-glue-graphs-of-groups-into-class-c
  - higman-clapham-towers-leave-the-seed-form-at-three-steps
distinct_from:
  relative-seeds-glue-graphs-of-groups-into-class-c: that builds relative seeds by gluing and asks whether infinitely generated C is allowed; this answers it negatively over free groups, and gives the exact finiteness constraint over free products.
  higman-clapham-towers-leave-the-seed-form-at-three-steps: that proposes the rope test (H_1, <t_α : α ∈ I>); this shows the rope cannot be seeded over the free product K = Z^2 * Z, so its seed must use the machine's HNN letters in K_M.
---
**ESTABLISHED** (lane proof, bh-invent-15, 2026-09-18; elementary; not reviewed). Only (RS1) is
used: `[π] ∩ Y = {y_*}` and `Stab(y_*) = C`. Rigidity and density play no role. Part 5 is a
sketch.

**Setting.** `A` is finitely generated and acts on a tree `T` with trivial edge stabilizers.
Examples are `A = P * Q`, graphs of groups with trivial edge groups, and free groups acting on
their Cayley trees.
- `(Y, π, y_*)` is a relative seed: an SFT with rule radius `w`, and `π` on `Ball(c)`.
- For an edge `e` of `T` whose far half-tree does not meet the base window, write `B_e ⊆ A` for
  the set of elements (edges) on the far side.
  - In a Cayley-type model, `B_e` is joined to the rest only through its entry element `ε_e`.
  - Define the **entry datum** `o_e = y_*|_{Ball(ε_e, 2w) \ B_e}`, read in coordinates at `ε_e`.

## Theorem
1. **Branch lemma.** `y_*|_{B_e} = ε_e · L_{o_e}`, where `L_o` is a fixed labelling of the
   standard branch that depends only on `o` and the edge orbit. So up to translation there are
   finitely many far-branch labellings.
2. **Free groups.** If `A = F` is free and `(F, C)` has a relative seed, then `C` is finitely
   generated.
3. **Finite ropes over free products.** Let `A = P * Q` with `1 ∈ P` as the base, and suppose
   `(A, C)` has a relative seed. Then `G_C = {g ∈ P : gQg^{-1} ∩ C ≠ 1}` is a finite union of
   cosets `(C ∩ P)g`.
4. **The Aanderaa–Cohen rope over `K`.** In `K = Z^2 * ⟨t⟩`, take `C_I = ⟨x^α t x^{-α} : α ∈ I⟩`
   with `I` infinite; for example the regular digit set of Cohen p. 279. Then `(K, C_I)` has no
   relative seed at all, rigid or not.
5. **Where the rope must be seeded (sketch).** Apply part 1 to the free product
   `H_1 = K_M * (C × F_n) * ⟨d⟩`. A relative seed for `(H_1, C_I)` restricts to one for
   `(K_M, C_I)`: on the `K_M`-coset of `1` it gives a block-labelled configuration whose other
   branches are canonically filled. `K_M` is an HNN extension of `K` along
   `⟨t(a,b), x^m, y^m⟩ → ⟨t(c,0), x^{m^2}, y⟩`, and part 3 does not apply to it. So **the rope
   can be seeded only through the machine letters `r_i, l_j`**, whose `x^m ↦ x^{m^2}` scaling
   is a BS(1,m)-type anchor transport.

## Proof
**1.** The only elements outside `B_e` adjacent to `B_e` are at the entry. A rule window at
`g ∈ B_e` that reaches outside sees only `Ball(ε_e, 2w)`.
- So the set of labellings of `B_e` compatible with `y_*` outside depends only on `o_e`.
- It is a single labelling. If there were two, swapping one for the other would give two
  distinct points of `[π] ∩ Y`, since `B_e` misses the base window.
- Left translation carries the standard branch onto `B_e`, which gives the form stated.

**2.** Apply part 1 to the Cayley tree.
- **The labelling is automatic.** For a reduced word `g` beyond the base ball, put
  `s(g) = o_{(g)}`. Then `s(gs')` for a child `gs'` is a function of `s(g)` and `s'`, because
  `y_*` on the branch at `g` is `g · L_{s(g)}`.
- **So `C` is rational.** `C` is the set of `g` at which `π` occurs. Beyond the base ball, that
  depends only on `s(g)`. So `C` is, up to a finite set, the image of a regular language of
  reduced words, hence a rational subset of `F`.
- **So `C` is finitely generated.** By Anisimov–Seifert, a subgroup that is a rational subset
  is finitely generated.

**3.** Let `z` be the `w`-block labelling of `y_*` on the coset `P`. A block determines the
radius-`w` pattern, so `Stab_P(z) = C ∩ P`.
- **The branches.** For `g ∈ G_C` choose `c_g = g q g^{-1} ∈ C` with `q ∈ Q \ 1`. Then `c_g`
  maps `P` onto the coset `gqP`. That coset lies in the far branch `B_g` behind the `Q`-vertex
  `gQ`, entered at `ε = gq`. The `B_g` for distinct cosets `gQ` are disjoint, so all but
  finitely many miss the base window.
- **Invariance.** From `c_g · y_* = y_*` and part 1:
  `z(h) = (block of y_* at gqg^{-1}h) = β_{o_g}(g^{-1}h)` for `h ∈ P`, with `β_o` a fixed
  function of `o`. So `z = g · β_{o_g}`.
- **Counting.** There are finitely many `o`. If `o_g = o_{g'}`, then `z = gg'^{-1} · z`, so
  `gg'^{-1} ∈ Stab_P(z) = C ∩ P`. So `G_C` is covered by finitely many cosets `(C∩P)g`,
  together with the finitely many `g` whose branch meets the window.

**4.** `C_I ∩ Z^2 = 1`, because `C_I` lies in the normal closure of `t`, which meets `Z^2`
trivially. So by part 3, `G_{C_I}` is finite. But it contains every `x^α` with `α ∈ I`, which
is infinite.

**5.** This is part 1 at the `H_1`-level edges joining the `K_M`-coset to the other factors.
Rules on block labels on `K_M` are "extendable branch data", a finite condition. Uniqueness and
the stabilizer restrict. This part was not written out in full.

## For the SEED TOWER team
- **The rope is not a separate step.** `higman-clapham-towers-leave-the-seed-form-at-three-steps`
  lists step 3 (the rope) and step 4 (the machine) separately. Part 4 shows the rope cannot be
  seeded below the machine. Its anchor (the position `α` of `t_α`) must be carried across
  `t`-edges, and over a free product a single edge carries only bounded data (part 1). The
  carrier must be `K_M`'s scaling letters.
- **Build order.**
  - First, a rigid seed on the digit-shifting part of `K_M`: `⟨x, y, r_i, l_j⟩`-type
    subgroups, which are BS(1,m)-like and force at linear radius (compare
    `bs12-rigid-seed-is-its-normal-form`).
  - Then, the rope as a relative seed over `K_M` that reads `α` from that counter.
  - This matches the target of `seed-collapse-is-bounded-by-forcing-radius-and-dehn`: linear
    forcing, with the machine's complexity carried by the tower's Dehn function.
- **Relative-seed gluing.** Infinitely generated `C` is impossible over free groups (part 2),
  and constrained over free products (part 3). It can occur only over vertex groups with
  nontrivial edge structure, such as `K_M`.

## Lesson for general BH
- **Bounded data per edge.** Across an edge with trivial stabilizer, a seed transmits only
  bounded data. So the far side of every such edge is one of finitely many canonical
  labellings.
- **What that forbids.** A relative seed cannot pick out infinitely many free-product
  branches by position: over free groups the seeded subgroup is finitely generated. Higman
  ropes can therefore be seeded only where the group itself transports positions, as the
  scaling HNN letters of the machine do.
- **What follows for towers.** In seed towers the counter and the machine must be built
  together, never the rope first.
