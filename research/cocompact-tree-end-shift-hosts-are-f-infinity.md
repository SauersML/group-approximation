---
rg: 2
id: cocompact-tree-end-shift-hosts-are-f-infinity
kind: claim
title: For a strongly faithful cocompact action on a locally finite leafless tree whose edge stabilizers are of type F_infinity-plus, the V-stabilized full group of the end shift is of type F_infinity; the end-shift SFT therefore satisfies the horizontal filling condition (A_N) in every degree, and E3′ holds for every graph of groups of this kind
distinct_from:
  nonascending-hnn-end-shifts-satisfy-e3-prime: that proves F_n for non-ascending multiple HNN extensions, one vertex group, through Li's Zappa–Szép theorem; this covers every cocompact graph of groups with locally finite tree, any number of vertex and edge orbits, through Thumann's theorem with infinite transformation groups.
  locally-finite-tree-end-shifts-are-quantum-rigid-sfts: that proves the end shift is a quantum-rigid, minimal, topologically free SFT; this proves the finiteness gate for the same class, so the class realizes (★′) and E3′ at once.
  v-times-tree-boundary-full-groups-are-f-infinity: that is the case of trivial vertex stabilizers; here the edge stabilizers are infinite and enter as transformations.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that embeds such groups in finitely presented simple groups through rigid permutation groups and twisted Brin–Thompson groups; this gives the direct master-route host, the V-stabilized end-shift full group, and shows it is F_infinity.
  crossing-wire-fixed-point-tile-sets-are-quantum-rigid: that is a rigid free SFT over the amenable group Z^2, where no finite cone basis can exist; this is the non-amenable, finitely coded regime, where (A_N) comes for free.
---

**ESTABLISHED** (lane proof, bh-invent-17, 2026-09-18; the finiteness input is Thumann's
Theorem `41762`, arXiv:1409.1085, read in the LaTeX source at `$GQ/src/bh-invent-07/thumann.tex`
l.2649–2669 for Defs. `77101`, `26536`, `13449`, `24121` and the theorem; one referee PASS, bh-ref-engines 2026-09-18; no priority claimed).

## Setting

- `Λ` acts on a locally finite tree `T` without leaves and without inversions, with finitely many
  orbits of edges and more than two ends. The action is minimal, has no fixed end, and is
  **strongly faithful**: no `g ≠ 1` fixes a half-tree pointwise.
- For an oriented edge `e`, `H(e)` is the half-tree beyond its terminal vertex, and `∂H(e)` is its
  set of ends, a clopen subset of `∂T`.
- Each edge stabilizer `Λ_e` is of type `F_∞^+`: it and all its subgroups are `F_∞`. Examples are
  finite, virtually polycyclic, and in particular `Z`.
- `X_T ⊆ A^Λ` is the end shift of `locally-finite-tree-end-shifts-are-quantum-rigid-sfts`, which
  that node shows is conjugate to `Λ ↷ ∂T`, and `F = F(G_V × (Λ ⋉ ∂T))`.

## Statement

1. `F` is of type `F_∞`. It is simple (`F = A`), and its action on `C × ∂T` has type (A)
   (`fp-v-times-minimal-action-full-groups-have-type-a-actions`), so every subgroup of `Λ` is PBH.
2. **(A_N) holds.** The domain filtration of `X_T` is essentially `n`-connected for every `n`. By
   `v-times-subshift-full-group-finiteness-is-horizontal` this is equivalent to item 1. So E3′
   (`v-times-rigid-topologically-free-sft-full-groups-are-fp`) holds for every such `X_T`, in
   every degree.
3. **Instances.** Every graph of groups with finite-index edge inclusions, edge groups of type
   `F_∞^+` and a strongly faithful action on its Bass–Serre tree. Examples:
   - `BS(m,n)` with `2 ≤ |m| ≠ |n|`, and every such generalized Baumslag–Solitar group;
   - graphs of virtually polycyclic groups with finite-index inclusions;
   - graphs of finite groups.

## Proof

**The operad.** This is a geometric dissection operad in the sense of
`non-lcm-dissection-operad-groups-are-f-infinity`. The only difference is that its tiles carry
infinite automorphism groups.
- *Colors.* Choose representatives `e_1, …, e_c` of the `Λ`-orbits of oriented edges. The tiles
  are `X_j = C × ∂H(e_j)`.
- *Transformations.* The degree-one operations `X_j → X_j` are `(w, ξ) ↦ (w, gξ)` for
  `g ∈ Λ_{e_j}`.
  - They act faithfully, by strong faithfulness.
  - `ℐ(𝒪)` has automorphism groups `Λ_{e_j}`, of type `F_∞^+`.
  - Valence-two vertices contribute degree-one splits, which are invertible and are absorbed into
    `ℐ(𝒪)` as identifications between colors.
- *Subdivisions.* There are two kinds.
  - The C-split `X_j = [0]×∂H(e_j) ⊔ [1]×∂H(e_j)`.
  - The tree split `∂H(e_j) = ⊔_{e'} ∂H(e')` over the edges `e' ≠ ē_j` leaving `t(e_j)`. It is
    finite by local finiteness, and each `e' = λ_{e'} e_{j'}` is labelled by `(w, ξ) ↦ (w, λ_{e'}ξ)`.
- *Root.* `C × ∂T = ⊔_{o(e) = v_0} C × ∂H(e)`, a finite word of tiles.

**Thumann's hypotheses.**
- *Finitely many colors:* cocompactness.
- *Color-tame* (Def. `77101`): any two equal colors merge by a C-split. So a reduced object has at
  most `c` letters.
- *Cancellative calculus of fractions.* Operations are injective maps, so cancellation is
  automatic. For the Ore condition, refine any two dissections of `X_j` to the uniform partition
  into cones `[u]×∂H(e)` with `|u| = L` and `e` at depth `D` below `e_j`. It is reachable from
  every dissection. Two labels of one piece differ by precomposition with some `g ∈ Λ_{e_j'}`,
  which is a transformation.
- *Finite type* (Def. `26536`).
  - The very elementary classes of color `j` are `C_j` and `T_j`.
  - Their unique minimal common refinement is the joint split `(C∨T)_j`: an operation refining both
    refines the joint partition, and by the swap lemma of
    `v-times-subshift-full-group-finiteness-is-horizontal` it factors through the joint split.
  - Composing with a transformation does not change a class, since `g·T_j = T_j·(permutation and
    transformations of the children)`.
  - So the spine is `{C_j, T_j, (C∨T)_j}`, which is finite.
- *`ℐ(𝒪)` of type `F_∞^+`:* by hypothesis.

So `π_1(𝒪, X)` is `F_∞` by Theorem `41762`.

**`π_1(𝒪, X) = F`.** Fractions `θ' ∘ θ^{-1}` of dissections of the root are homeomorphisms that
are canonical on cones, so they lie in `F`. Conversely, take `f ∈ F`.
- `f` is `(prefix replacement) × λ` on each cone `[u]×∂H(e)` of a fine partition. It maps each such
  cone onto `[u']×∂H(λe)` by `ℓ' ∘ ℓ^{-1}`, where `ℓ, ℓ'` are tile labels.
- Refine the image partition to a uniform one, and pull the refinement back through the canonical
  maps. This makes both sides reachable dissections. Reachability of the image side is not
  automatic: product partitions need not be guillotine.
- So `f` is a fraction.

**Item 2.** Item 1 and the exactness clause of `v-times-subshift-full-group-finiteness-is-horizontal`.
Concretely, a half-tree cone is a one-site cylinder of `X_T` (the out-edge at `o(e)` is `e`), and
the finite cone basis is the mechanism behind the filling; no explicit filling radius is computed here.

**Item 3.** The groups are those of `locally-finite-tree-end-shifts-are-quantum-rigid-sfts`, items
1–3. For `BS(m,n)` the edge stabilizers are `⟨a^m⟩ ≅ Z`, and strong faithfulness is §7 of that
node's route. `∎`

**Remarks.**
- With `F_∞` edge stabilizers in place of `F_∞^+`, the same proof runs through
  `thumann-operad-groups-need-only-f-infinity-transformations`, which is an unreviewed weakening.
- `F_n` edge stabilizers should give `F_n`, by the `F_n` form stated there. That form is not
  written out.

## Why this is the regime where (A_N) is free, and what the crossing-wire case needs

- **Mechanism.** (A_N) holds as soon as the SFT has a **finite shadow basis**. That means:
  - finitely many cylinder types, closed under a splitting rule with unique minimal common
    refinements;
  - canonical-similarity groupoid with `F_∞^+` automorphism groups.

  Then the whole complex is cocompact, and bounded-radius loops fill at bounded radius.
  Compression codings over non-amenable groups (trees, `Ã₂`, products of trees) are of this kind.
  Infinite isotropy is allowed; it enters only as transformations.
- **Amenable acting groups cannot have one.** Over `Z^2`, an invariant measure of full support
  gives infinitely many cone types (P2′ Attempt 1). For the crossing-wire tiles
  (`crossing-wire-fixed-point-tile-sets-are-quantum-rigid`), (A_N) is therefore an infinite-type
  statement. Their fixed-point structure (unique macrotile decomposition, sketched, not proved here) makes the groupoid self-similar, `𝒢 ≅ 𝒢 × Pair(N^2)`.
  That shrinks domain radii by the zoom factor. Its effect:
  - a filling at one scale propagates to every scale, with filling radius linear in the loop's
    radius, which is enough for essential connectivity;
  - but it does not create the one-scale filling. That still needs a genuinely new argument, and
    without it one gets only a self-similar (L-presentation-type) recursion.

  This is not attempted here.

## Lesson for general BH

The horizontal condition (A_N) is automatic exactly when compression supplies a finite shadow
basis. Isotropy is harmless there: infinite edge stabilizers enter Thumann's engine as
transformations, and the host is `F_∞` as soon as they are `F_∞^+`.

So the master-route object exists and is `F_∞` for every strongly faithful cocompact tree action,
including non-residually-finite groups such as `BS(2,3)`. The remaining E3′ frontier is precisely
the infinite-type regime:
- rigid SFTs over amenable or measure-carrying acting groups, where no finite shadow basis can
  exist;
- inputs that need non-residually-finite unit data.

There a one-scale filling theorem is the missing ingredient.

## Referee (bh-ref-engines, 2026-09-18): PASS

I checked the proof step by step, and checked Thumann's hypotheses against his source (`thumann.tex`: Def.
`77101`, color-tame; Def. `26536`, finite type; the `F_∞^+` groupoid definition at l.2650; Thm. `41762`).

**Operad and hypotheses.**
- The transformations act faithfully by strong faithfulness: fixing `∂H(e_j)` pointwise fixes the leafless
  half-tree.
- *Color-tame.* A word with a repeated colour is the domain of the C-merge `X_j X_j → X_j`, so reduced objects
  have at most `c` letters.
- *Ore.* Every piece of a dissection is a cone `[u]×∂H(e)`, and a common uniform refinement is reachable from
  both. The two labels of one uniform piece differ by an element of `Λ_(e_(j'))`, which is a transformation.
- *Finite type.* The very elementary classes are exactly `C_j` and `T_j`, stable under left and right
  transformations since `g T_j = T_j ∘ (permutation and transformations)`. Their join is the joint split. So
  the spine is finite.
- *`F_∞^+`.* Thumann's hypothesis is on the automorphism groups of **colours** (degree-one operations). His
  proof uses only subgroups of `Aut(c)` inside products with pure braid or symmetric groups. So `Λ_(e_j)` of
  type `F_∞^+` is exactly what is needed, and no closure under products is required.
- *`π_1(𝒪, X) = F`.* The operad is concrete. Fractions are canonical on cones. Conversely, for `f ∈ F`, first
  refine the image to a globally uniform (reachable) partition, then pull back through the canonical cone maps.
  This gives relatively uniform, reachable refinements of the domain cones. Correct.

**Imported, not re-checked here:**
- `F = A`, simplicity and type (A) (`fp-v-times-minimal-action-full-groups-have-type-a-actions`). This is
  consistent: `H_*(G_V) = 0` gives `F_ab = 0` by Künneth plus Matui.
- The (A_N) equivalence (`v-times-subshift-full-group-finiteness-is-horizontal`).
- The end-shift conjugacy (`locally-finite-tree-end-shifts-are-quantum-rigid-sfts`).

**Wording fix.** In item 3, "graphs of virtually polycyclic groups" and "graphs of finite groups" are instances
only when their action is strongly faithful, which is not automatic. The node states strong faithfulness as a
hypothesis, so the examples should repeat it. For `BS(m,n)`, `2 ≤ |m| ≠ |n|`, strong faithfulness holds. In
every half-tree the exponent of an elliptic `a^k` is multiplied by the non-integral ratio along some branch,
which agrees with Step 9 of the non-ascending HNN node, proved independently through Li.

**Credit.**
- Thumann (arXiv:1409.1085) for the operad finiteness engine.
- The Stein–Farley complex / Brown's criterion method it abstracts.
- Li (arXiv:2110.04505) for the parallel Zappa–Szép route.
- The rigid-permutation-group embeddings the node cites as BLIW, for prior embeddings of this class into
  finitely presented simple groups.
