---
rg: 2
id: thompson-f-in-permanence-closure-only-via-base-copy
kind: claim
title: "Tree actions of Thompson's F fix a vertex unless an edge stabilizer contains a copy of F, so group-level permanence closures reach F only through a base group containing F, and from amenable, LEA and LEF bases only if F is amenable"
distinct_from:
  f-free-groups-are-closed-under-recurrent-extensions: that closes F-freeness under subgroups, extensions, unions and recurrent extensions, the operations that build amenable groups; this adds unrestricted direct products, fundamental groups of arbitrary graphs of groups with arbitrary edge groups, and local embeddability (marked limits, residual and LEA/LEF-type operations), the operations that build sofic and hyperlinear groups, through a new tree lemma for F.
  thompson-f-is-lea-only-if-amenable: that collapses local embeddability into amenable groups for F; this uses the same finite-presentation step as one of seven closure operations and proves the collapse for the whole permanence closure.
  kazhdan-groups-in-sofic-permanence-closure-are-lef: that kills permanence for Kazhdan groups through property FA; F is Haagerup and surjects onto Z, so it has no property FA, and this replaces FA by the relative tree lemma of item 1.
  permanence-closure-fg-simple-groups-are-sofic: that uses local sofic-indicability, which F plausibly satisfies (F surjects onto Z^2, and its copies of F do too), so it gives no obstruction for F; this uses the invariant "contains a copy of F".
  nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f: that is the normal-subgroup input; this is the closure theorem and the tree lemma built on it.
  thompson-f-is-not-hyperlinear: that is the open problem; this shows only that no group-level permanence argument can refute it unless F is amenable.
---

**ESTABLISHED** through `thompson-f-in-permanence-closure-only-via-base-copy-proof`.

**Setting.** `F` is Thompson's group acting on `[0,1]` by piecewise linear homeomorphisms. A group `G` is
*F-free* if no subgroup of `G` is isomorphic to `F`; `𝓕` is the class of F-free groups. Trees are simplicial and
actions are without inversions.

## Statement

1. **Relative property FA.** Let a group `G` act on a tree `T`, and let `F_0 ≤ G` with `F_0 ≅ F`. Then `F_0` fixes
   a vertex, or some edge stabilizer `G_e` contains a subgroup isomorphic to `F`.
2. **Closure.** `𝓕` is closed under
   - (O1) subgroups;
   - (O2) directed unions;
   - (O3) arbitrary unrestricted direct products;
   - (O4) extensions: `N ◁ G` with `N, G/N ∈ 𝓕` gives `G ∈ 𝓕`;
   - (O5) fundamental groups of graphs of groups over arbitrary graphs, with vertex groups in `𝓕` and arbitrary
     edge groups;
   - (O6) local embeddability: if every finite subset of `G` admits a map into a member of `𝓕` that is injective on
     it and multiplicative on its pairs, then `G ∈ 𝓕`. This includes limits in the space of marked groups, and
     residually-`𝓕` groups;
   - (O7) recurrent extensions, in the sense of `f-free-groups-are-closed-under-recurrent-extensions`.
3. **Collapse.** Let `𝒫(𝓑)` be the smallest class containing a class `𝓑` and closed under (O1)–(O7). Then `F`
   embeds in a member of `𝒫(𝓑)` if and only if `F` embeds in a member of `𝓑`.
4. **Sofic and hyperlinear bases.** Let `𝓑_0` be the class of amenable groups, LEA groups and LEF groups. Then
   `F ∈ 𝒫(𝓑_0)` if and only if `F` is amenable. If `F` is not amenable, no group containing `F` lies in
   `𝒫(𝓑_0)`; examples are Thompson's `T` and `V`.

## What is killed

**The approaches.** These are the group-level permanence theorems for soficity and hyperlinearity, iterated in any
order and any number of times, over the bases of item 4. Each is an instance of (O1)–(O6):
- amenable extensions (Elek–Szabó) and arbitrary extensions;
- amalgamated free products and HNN extensions over amenable subgroups (Elek–Szabó, Păunescu,
  Dykema–Kerr–Pichot; Brown–Dykema–Jung on the operator-algebra side), which are (O5) with more restrictive
  edge groups;
- graph products (Ciobanu–Holt–Rees), which are iterated amalgams, with unions for infinite graphs;
- restricted and unrestricted wreath products (Hayes–Sale), which are extensions of products;
- direct products, directed unions, residual and local-embedding closures, and marked limits.

None of them can prove `thompson-f-is-sofic` or `thompson-f-is-hyperlinear` except by proving `F` amenable.

**The invariant.** "Contains a subgroup isomorphic to `F`".

**Where every member dies.** At the first step whose output contains a copy of `F`, an input already contained one:
- **(O3)** some coordinate projection is injective on the copy, because `F'` is simple with trivial centralizer;
- **(O5)** item 1 puts the copy in a vertex group or a copy of `F` in an edge group;
- **(O6)** a local embedding of a ball containing the relators and `c = [x_0, x_1]` is a homomorphism injective on
  `c`, and so injective;
- **(O4), (O2), (O7)** as in `f-free-groups-are-closed-under-recurrent-extensions`.

**For the inverter biography of `thompson-f-is-not-hyperlinear`.** Suppose `F` is hyperlinear but not amenable.
- Then no hyperlinear group assembled from amenable, LEA or LEF groups by these operations contains `F`.
- A hyperlinearity certificate for `F` must therefore be a direct metric construction: tracial almost-representations
  of `F` itself, or of a new base group that already contains `F`.
- Combined with `thompson-f-commutator-bound-holds-in-each-fixed-dimension`, such witnesses need unbounded irreducible
  degree, and they cannot be obtained by gluing witnesses for smaller groups along any splitting, product or
  extension.

## Scope

**What is not killed.**
- **Quotients.** `𝓕` is not closed under quotients, since `F` is a quotient of a free group. Metric ultraproducts are
  quotients of products, which is exactly why hyperlinearity itself is not a closure step here.
- **Action and measure-theoretic permanence.** Examples are soficity from a free p.m.p. action with sofic orbit
  relation (Elek–Lippner, Păunescu), and crossed-product or amalgamated von Neumann algebra embeddings that are not
  induced by a group-level operation.
- **Direct constructions.** Almost-representations of `F` itself, which is where
  `thompson-f-sofic-iff-defect-to-separation-ratio-vanishes` and
  `thompson-f-commutator-bound-holds-in-each-fixed-dimension` live.

**Novelty.** Item 1 is elementary. No source stating it for `F` is known here.
