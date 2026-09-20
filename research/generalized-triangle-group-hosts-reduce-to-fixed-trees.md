---
rg: 2
id: generalized-triangle-group-hosts-reduce-to-fixed-trees
kind: claim
title: For the BBMZ host of G * Z, singular sets are controlled by the generators and the free generator is never singular, so the uncountable form of Conjecture U for a hyperbolic group G is a statement about finitely many generators of G; for the Kazhdan group H_31 these all have order 5, each fixes a tree in the CAT(-1) triangle complex with Cantor boundary (vertex degrees 5, 12, 25 for a and b, 5-regular for c), the analogue of the wall tree, and whether a generator is singular over its fixed tree is open
distinct_from:
  racg-generators-are-singular-over-their-wall-trees: that proves singularity over the whole wall tree in girth-5 right-angled Coxeter groups, using halfspaces; this reduces the Kazhdan case for H_31 to its three torsion generators and computes their fixed trees, which play the role of wall trees but come with no halfspace structure.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - bbmz-singularity-is-a-recurrent-coincidence
  - racg-generators-are-singular-over-their-wall-trees
```

**Status.**
- **ESTABLISHED** (lane proof, bh-q12-kazhdan, 2026-09-19; not reviewed): Lemma 1, Lemma 2, Corollary 3 and
  Proposition 4.
- **OPEN:** Conjecture 5, the triangle-complex analogue of Proposition F. It would settle the uncountable form of
  Conjecture U for `𝓗_31`.
- No computation was run, and no priority is claimed.

## Setting

- `G` is hyperbolic with finite symmetric generating set `S_G`. The host is built on `H = G ∗ ⟨t⟩` with generating
  set `S = S_G ∪ {t^{±1}}`.
- `sing(g)` is as in `bbmz-singularity-is-a-recurrent-coincidence`: the points of `∂_h H` at which the local actions
  of `g` are not eventually surjective.

## Lemma 1 (singular sets are a cocycle)

For all `g, h`, `sing(gh) ⊆ sing(h) ∪ h^{-1} sing(g)`. Hence, for a word `g = s_1 ⋯ s_m` in `S`,
`sing(g) ⊆ ⋃_i (s_{i+1} ⋯ s_m)^{-1} sing(s_i)`.

*Proof.* Let `y ∉ sing(h)` with `hy ∉ sing(g)`.
- For large `n`, `h` maps the `B_n`-atom `D` of `y` onto an atom `D'` of level `n'` around `hy`, with
  `|n − n'| ≤ |h|` by Proposition C of `bbmz-singularity-is-a-recurrent-coincidence`.
- Once `n'` is large, `g` maps `D'` onto an atom. So `gh` maps `D` onto an atom.

So `y` is regular for `gh`. The word form follows by induction. ∎

**Consequence.** Every element has countable (respectively finite) singular set iff every generator in `S` does.

## Lemma 2 (the free generator is never singular)

`sing(t) = ∅`.

*Proof.*
- **Offsets.** Geodesics in `H` are concatenations of geodesic syllables. So `d(t,v) − d(1,v) = −1` if the normal
  form of `v` starts with a positive power of `t`, and `+1` otherwise.
- **Near a boundary point, the first syllable is eventually constant.** If `x_k → ζ ∈ ∂H`, the first syllables of
  the `x_k` eventually agree with that of `ζ`. When `ζ` lies in the boundary of the root copy of `G`, they are
  eventually non-`t` syllables.
- So `ℓ_t` is constant on every fiber, the offset frontier `F'_t` is empty, and Theorem A gives `sing(t) = ∅`. ∎

## Corollary 3

The uncountable form of Conjecture U for `G ∗ Z` holds iff some `s ∈ S_G` has uncountably many singular points in
this host.
- For `𝓗_31` with `S_G = {a^{±1}, b^{±1}, c^{±1}}`, every such `s` has order 5.
- So the question is about three elliptic generators and nothing else.
- The frontier theorems for loxodromic elements (`busemann-frontiers-separate-the-boundary`, and the countable-sets
  lemma) cannot decide it on their own, since by Lemma 1 every singular set is assembled from generator singular
  sets.

## Proposition 4 (fixed trees of the generators of 𝓗_31)

**Setting.** `𝓗_31` acts on its CAT(−1) triangle complex `X`, sharply transitively on triangles. The vertex groups
are `A = ⟨a,b⟩ ≅ PSL_2(31)`, `B = ⟨b,c⟩` (order `5^4`) and `C = ⟨c,a⟩ ≅ C_5 × C_5`, and the edge groups are
`⟨a⟩, ⟨b⟩, ⟨c⟩` (CCKW arXiv:2011.09276, Theorem 1.2 and the text after it).

**Statement.**
- **Fix(a) and Fix(b)** are trees made of `a`- and `b`-type edges. Their vertex degrees are:
  - 5 at `C`-type vertices;
  - 12 at `A`-type vertices, with 6 edges of each type;
  - 25 at `B`-type vertices.
- **Fix(c)** is a 5-regular tree made of `c`-type edges. It passes through `B`- and `C`-type vertices, 5 edges at
  each.
- In all three cases the boundary is a Cantor set in `∂X = ∂𝓗_31`, fixed pointwise by the generator.

*Proof.*
- **Fix(g) is a tree in the 1-skeleton.**
  - The action on triangles is free, so a nontrivial `g` fixes no triangle and no interior point of one.
  - Types are preserved, so a fixed interior point of an edge fixes the edge.
  - Fixed sets are convex in CAT(0) spaces. So `Fix(g)` is a convex subgraph, hence a tree.
- **Degrees.** At a vertex `xV` with `g ∈ xVx^{-1}`, the fixed edges of type `E` correspond to cosets `yE` in `V`
  with `(xy)^{-1} g (xy) ∈ E`.
  - **`C`-type vertices.** `C` is abelian, and `a ∉ ⟨c⟩`. So `a` fixes all 5 cosets of `⟨a⟩` and none of `⟨c⟩`.
    The same holds with `a, c` swapped.
  - **`A`-type vertices.** Subgroups of order 5 of `PSL_2(31)` lie in split tori of order 15, since `5 | 15 = (31−1)/2`.
    Their normalizer is dihedral of order 30. All of them are conjugate, being Sylow subgroups.
    - An element of order 5 fixes `30/5 = 6` cosets of `⟨a⟩` and, since its conjugates reach `⟨b⟩`, 6 cosets of
      `⟨b⟩`.
  - **`B`-type vertices.** The relations `[b,c,b] = [b,c,c,b] = [b,c,c,c] = 1` make `B` of class 3.
    - `γ_3 = ⟨[b,c,c]⟩` is central, and `C_B(b) = ⟨b, [b,c], [b,c,c]⟩` has order 125.
    - Conjugating by `c^k z`, with `z ∈ C_B(b)` and `k ≢ 0`, multiplies `b` by `[b,c]^k` modulo `γ_3`. So
      `N_B(⟨b⟩) = C_B(b)`, and `b` fixes `125/5 = 25` cosets of `⟨b⟩`.
    - Similarly `C_B(c) = ⟨c, [b,c,c]⟩` has order 25, because the class of `c` is `cγ_2`. So `c` fixes 5 cosets of
      `⟨c⟩`.
    - No conjugate of `b` lies in `⟨c⟩`, or conversely, because `b` and `c` are independent in the abelianization of
      `B`.
  - **Propagation.** Walk through the connected tree `Fix(a)` from `e_a`. Along an `a`-type edge, the acting element
    lies in a conjugate of `⟨a⟩`; along a `b`-type edge, in a conjugate of `⟨b⟩`. So the three vertex computations
    cover every vertex, and `Fix(a)` uses only `a`- and `b`-type edges. Likewise `Fix(c)` uses only `c`-type edges.
    The same walk from `e_b` gives `Fix(b)`; `a` and `b` generate conjugate Sylow subgroups of `A`.
- **Boundary.** All degrees are at least 5 and the trees are locally finite. A convex subtree of the CAT(−1) space
  `X` has Cantor boundary embedded in `∂X`. ∎

## Conjecture 5 (fixed-tree singularity; OPEN)

In the host of `𝓗_31 ∗ Z`, with `S_G = {a^{±1}, b^{±1}, c^{±1}}` or with all nontrivial edge-group elements, `a`
(or `c`) is singular at a horofunction over every point of a Cantor subset of `∂Fix(a)` (or `∂Fix(c)`). Here
`∂Fix(a) ⊂ ∂𝓗_31` is placed in the root copy inside `∂(𝓗_31 ∗ Z)`.

By Corollary 3 it implies the uncountable form of Conjecture U for `𝓗_31 ∗ Z`, the first such statement for a named
Kazhdan group.

## Why Proposition F does not transfer

- **What Proposition F used.** In a right-angled Coxeter group, `Fix(s)` is the wall `H_s`. The proof there used its
  two halfspaces: crossing walls against outer (+)-walls, with `f = ±1` constant on each side.
- **What is different here.** `a` has order 5, and around every edge of `Fix(a)` the complement has 5 local sectors,
  which `a` permutes.
  - A coarse separation of `X` by `Fix(a)` would make `Stab(Fix(a))` a codimension-one subgroup, if it acts
    cocompactly on `Fix(a)` (recalled, not checked).
  - Property (T) forbids codimension-one subgroups (Niblo–Roller 1998, recalled).
  - So, granting both recalled facts, the offset regions `{f = 1}, {f = 0}, {f = −1}` of `f = d(aT,·) − d(T,·)` are not halfspaces.
- **What the missing input is.** Theorem D's recurrent coincidence must be re-derived for the chamber graph.
  - The Cayley graph of the edge-group generators is the chamber graph.
  - The events should be read off the vertex links met by rays of `Fix(a)`: coset graphs of girth 10, 8 and 4.
  - Offsets there are preferred sets among the 5 chambers around `e_a` (the lemma in
    `racg-generators-are-singular-over-their-wall-trees`).

## Lesson for general BH

- **For a torsion-generated hyperbolic group, the bounded-host question is a question about fixed trees.** Singular
  sets are generated by the generators (Lemma 1), a free `Z` factor adds nothing (Lemma 2), and elliptic generators
  can only be singular where their offsets jump.
- **The wall tree survives in Kazhdan groups; its halfspaces do not.** Torsion elements of Kazhdan hyperbolic groups
  still have large fixed trees with Cantor boundaries. So the decisive question is whether singularity needs the two
  sides of a wall, or only a tree.
