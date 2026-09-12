---
rg: 2
id: subgroup-cosets-are-independent-over-division-closure
kind: claim
title: Distinct cosets of any subgroup are linearly independent over its division closure
distinct_from:
  atiyah-amalgam-unmixed-matrices-reduce-to-factors: that computes the von Neumann rank of a matrix supported in one vertex or the edge by induction; this is a linear-independence statement about single elements of the affiliated algebra, with no matrix, no amalgam and no Strong Atiyah hypothesis.
  atiyah-amalgam-rank-from-cohn-coproduct: that reduces Strong Atiyah for an amalgam to one rank function on the coproduct of the vertex division closures; this is the freeness half of the Hughes condition for an arbitrary subgroup, and it says nothing about that coproduct.
  kazhdan-edge-coproduct-rank-is-inner-rank: that is the open maximality statement at a property (T) edge; this is an unconditional lemma, and its Attempts record why the two are far apart.
artifacts:
  - research/artifacts/atiyah-coproduct-inner-rank-2026-09-12.md
---

**ESTABLISHED** by [[subgroup-cosets-independence-proof]].

Let `K` be a subfield of `C` closed under complex conjugation, `G` a group, and
`H <= G` any subgroup. Write `U(G)` for the algebra of operators affiliated to
the group von Neumann algebra `N(G)`, and `D_H` for the division closure of
`K[H]` in `U(H) <= U(G)`. Let `x_1, ..., x_n in G` lie in pairwise distinct right
cosets `H x_i`. Then for `a_1, ..., a_n in U(H)`,

```text
a_1 x_1 + ... + a_n x_n = 0   in U(G)   implies   a_1 = ... = a_n = 0.
```

In particular the `D_H`-span of `G` inside `U(G)` is the free left `D_H`-module

```text
span_(D_H)(G) = (+)_(Hg in H\G) D_H g,
```

so `D_G` contains a free left `D_H`-module on any set of coset representatives.

No hypothesis is used: `H` may be nonamenable, may have property (T), and
neither `H` nor `G` need satisfy the Strong Atiyah conjecture.

## What it is, and is not

This is the *freeness* half of the Hughes condition on a division ring of
fractions, and it holds unconditionally. The Hughes framework needs a second,
independent half: *uniqueness* of a Hughes-free division ring, which Hughes'
theorem supplies only for locally indicable groups. Property (T) of `H` blocks
exactly that second half, through finite abelianization
([[atiyah-kazhdan-edge-blocks-both-permanence-routes]]), and leaves this one
untouched.

So the failure of the Hughes-free route at a Kazhdan edge is a failure of
uniqueness, not of freeness.

The statement is standard in the `L^2` literature (it is the orthogonality of
the coset decomposition of `l^2(G)` as a left `N(H)`-module). No novelty is
claimed; it is recorded because the two halves of the Hughes condition are
treated as one elsewhere in this graph.
