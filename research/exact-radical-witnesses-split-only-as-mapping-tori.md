---
rg: 2
id: exact-radical-witnesses-split-only-as-mapping-tori
kind: claim
title: A witness of the exact Kazhdan MF radical over Z acts on trees only through its map to Z, so it is one-ended and its only reduced splitting is the tautological mapping-torus HNN extension
distinct_from:
  bieri-strebel-splitting-over-kernel-of-map-to-z: that gives, for any finitely presented group mapping onto Z, an HNN splitting with finitely generated base inside the kernel; this shows that for a witness every such base, and every associated subgroup, is the whole kernel K, so the splitting carries no finiteness information about K.
  arithmetic-defect-saturated-kazhdan-group-is-sofic: its Attempt 5 uses FA of the Kazhdan quotient Q itself; here the ambient group G = K x| Z is not Kazhdan and does split, and the point is that FA of the normal subgroup K pins down every splitting of G.
  kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds: that concerns Schreier graphs of Kazhdan inputs in a full-group gate; this is about Bass--Serre trees of the mapping-torus witness.
artifacts:
  - research/torsion-free-sofic-exact-mf-radical-over-z.md
  - research/bieri-strebel-splitting-over-kernel-of-map-to-z.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
---

**ESTABLISHED** (proof below, self-contained modulo Watatani's theorem that Kazhdan groups have
Serre's property FA, and Stallings' ends theorem).

**Setting.** `G` is a group, `K normal G` is nontrivial, torsion-free and Kazhdan, and
`chi : G ->> Z` has kernel `K`. Every witness of `torsion-free-sofic-exact-mf-radical-over-z`
is such a pair; neither finite presentation nor soficity is used.

**Statement.**

1. **(TR1) Trees.** For every action of `G` on a simplicial tree `T` without inversions, `K` fixes
   a point, and `K` acts trivially on every `G`-invariant subtree on which `G` acts minimally.
   Such a minimal subtree is a point or a line, and in the line case `G` acts by translations
   through `chi`.
2. **(TR2) Splittings.** In every reduced graph-of-groups decomposition of `G`, every vertex group
   and every edge group equals `K`. The graph is a single loop, and the decomposition is the
   mapping torus `K *_K` with stable letter a lift `t` of `+-1`. In particular `G` is not a
   nontrivial amalgamated free product, not a strictly ascending HNN extension, and not an HNN
   extension over any subgroup other than `K`.
3. **(TR3) Ends.** `G` is one-ended.
4. **(TR4) Bieri--Strebel data is tautological.** In any Bieri--Strebel splitting of `G` over
   `ker chi` the base group and both associated subgroups are `K` itself.

**Class killed.** Every approach that tries to certify, construct or constrain a witness through
a splitting of `G` other than the tautological one. This includes amalgam or graph-of-groups
assemblies of witnesses, strictly ascending HNN models such as Bartholdi-type embeddings of
ascending `L`-presentations with non-surjective substitutions, and every attempt to obtain
finite presentation (or `FP_2`) of `K` from a Bieri--Strebel base.

- *Invariant.* Property FA of the normal subgroup `K`.
- *Death step.* `Fix(K)` is nonempty and `G`-invariant, so `K` sits in every vertex and edge
  stabilizer of every minimal `G`-tree.

So the finiteness question for `K` is not a splitting question. By Renz, for finitely presented
`G` it is exactly the condition `+-chi in Sigma^2(G)` (homotopical), and region (IO) of
`finite-outer-order-radical-witnesses-cross-alekseev-thom` requires this condition to fail. The
w17 calibration already recorded this `Sigma^2` restatement as a tautology.

## Proof

**Watatani.** A countable Kazhdan group has property FA: every action on a simplicial tree
without inversions has a global fixed vertex. This is also Serre, *Trees*, I.6.1, together with
Watatani 1982.

**(TR1).** Let `G` act on a tree `T` without inversions. By FA, `F = Fix(K)` is a nonempty
subtree, because fixed-point sets of groups acting without inversions are subtrees. For `g in G`
we have `g F = Fix(g K g^-1) = Fix(K) = F`, since `K` is normal. So `F` is `G`-invariant.

Now let `T_0` be a `G`-invariant subtree on which the action is minimal, meaning that there is no
proper invariant subtree. Then `F ∩ T_0` is also invariant. It is nonempty for the following
reason. Pick `v in F` and let `p` be the nearest-point projection to `T_0`. Then `p(v)` is fixed
by every element fixing `v` and preserving `T_0`, in particular by `K`. So `F ∩ T_0` is a
nonempty invariant subtree of `T_0`, and minimality gives `T_0 ⊆ F`.

Hence `K` acts trivially on `T_0`, and the action factors through `G/K = Z`. A minimal action of
`Z` on a tree without inversions is one of two kinds:
- a fixed point, when the generator is elliptic;
- the axis of the generator, on which it translates, when it is hyperbolic.

**(TR2).** Take a finite graph-of-groups decomposition of `G` with at least one edge that is
reduced, meaning that no non-loop edge has its edge group equal to an endpoint vertex group. Its
Bass--Serre tree `T` is minimal and is not a point. (A proper invariant subtree would have to omit
the lifts of some edge whose removal splits off a part of the graph, and that forces an edge group
equal to a vertex group on a non-loop edge.) By (TR1),
`T` is a line and `G/K` acts on it by translations.

The stabilizer in `G/K` of every vertex and every edge is therefore trivial. So every vertex and
edge stabilizer in `G` equals `K`. A translation action of `Z` on a line with translation length
`n` has a quotient cycle of length `n`, and it is reduced only if `n = 1`: otherwise some edge
group equals an adjacent vertex group on a non-loop edge.

For `n = 1` the graph of groups is one loop with vertex and edge group `K`, both edge maps
isomorphisms. That is the HNN presentation `<K, t | t k t^-1 = phi(k)>`, i.e. `K x|_phi Z` itself.

An amalgam `A *_C B` with `A != C != B` has a tree with a non-loop edge, and a strictly ascending
HNN extension has an edge group properly contained in the vertex group. Both are excluded.

**(TR3).** `G` is finitely generated, because `K` is Kazhdan and hence finitely generated. `G` is
infinite. It is not virtually `Z`, because `K` is nontrivial and torsion-free, hence infinite, and
`K` has infinite index. So `G` is not two-ended. If `G` had infinitely many ends, Stallings'
theorem would give a reduced splitting over a finite edge group. By (TR2) that edge group equals
the infinite group `K`, a contradiction. So `G` has exactly one end.

**(TR4).** A Bieri--Strebel splitting is an HNN extension `G = <B, t | t a t^-1 = alpha(a),
a in A>` with `B` a finitely generated subgroup of `ker chi = K` and `chi(t) = 1`. Its graph
of groups is one vertex with one loop, which is reduced in the sense above, whether or not the
extension is ascending. So (TR2) applies and gives `B = A = alpha(A) = K`. Directly: the
Bass--Serre tree has one vertex orbit, and `K` fixes one vertex by FA. Being normal, it fixes all
of them, so `K ≤ B ≤ K`, and each edge stabilizer `A` satisfies `K ≤ A ≤ B = K`. QED.

## Attempts

- **Construction (swarm-0917-w21-w21-titz-break, 2026-09-20, host-geometry).** Written as a
  breaker class kill on `torsion-free-sofic-exact-mf-radical-over-z`. It was screened against
  `bieri-strebel-splitting-over-kernel-of-map-to-z`, the audit remark that strict ascending unions
  of Kazhdan cores stabilize (which is the special case "strictly ascending HNN extension" of
  (TR2)), and Attempt 5 of `arithmetic-defect-saturated-kazhdan-group-is-sofic`.
