---
rg: 2
id: reid-higman-thompson-variant-is-not-finitely-presented
kind: claim
title: Colin Reid's d = 0 Higman–Thompson variant (MathOverflow 339541), the full group of Z/2 * Z on its compactified Bass–Serre tree, is not finitely presented, and neither is its finitely generated simple derived subgroup
requires:
  - stabilizer-engines-force-isolated-vertex-groups
  - reid-higman-thompson-variant-d-zero-abelianization
distinct_from:
  reid-higman-thompson-variant-d-zero-abelianization: that computes the abelianization, homology and simplicity and leaves finite presentation open; this settles finite presentation (no).
---

**ESTABLISHED** (lane proof, bh-free-56, 2026-09-18; not reviewed; no priority claimed). The
question had no answers on MathOverflow when bh-free-60 read it on 2026-09-18.

## Statement

Let `G = [[D ⋉ X]]` be Reid's group, with `D = <a> * <t> ≅ Z/2 * Z` and `X` the Bass–Serre
tree of `D` compactified by its vertices
(`reid-higman-thompson-variant-d-zero-abelianization`). Then:
- `G` is not finitely presented;
- its derived group `G'` is not finitely presented. `G'` is finitely generated, simple and
  rationally acyclic.

## Proof

This is `stabilizer-engines-force-isolated-vertex-groups` with `B = Z`. `Z` is not finitely
discriminable: the subgroups `nZ` avoid any finite set.
- For `G'`: if `G'` were finitely presented, then so would be `G`, as an extension of `G'` by
  the finitely presented group `G/G' = Z ⊕ Z/2`.

**The argument in Reid's own terms.** Let `G_n` be Reid's group for `d = n`: the full group of
`Z/2 * Z/n` on the ends of the `n`-regular tree, which Reid identifies as a Higman–Thompson
group.
1. **Transport.** Every element of `G` is a finite list of (clopen piece, label in `D`). Read
   the same list with labels in `Z/2 * Z/n`. For `n` large compared with the length of a word
   `w` in fixed generators, `w = 1` in `G` iff its image is `1` in `G_n`. Here "length" means
   the size of the `t`-exponents that occur.
2. **Homomorphisms.** If `G` had a finite presentation with `a, t` among the generators, then
   for large `n` its relators would hold in `G_n`. That gives homomorphisms `φ_n : G → G_n`
   with `φ_n(t) = t` of order `n`.
3. **The kernel.** Then `1 ≠ t^n ∈ ker φ_n`. Every nontrivial normal subgroup of `G` contains
   the simple group `G'` (Nekrashevych).
4. **Contradiction.** So `φ_n` kills a fixed nontrivial `x ∈ G'` for every large `n`. But
   `φ_n(x) ≠ 1` for large `n`, by step 1.

## What this says

- **The Houghton heuristic is correct.** The copy of `H_2 = FSym(Z) ⋊ Z` at each vertex point
  of `bh-free-60`'s heuristic is not rescued by the Cantor room elsewhere.
  - The far-commutation relations of the branches around a vertex are exactly the relations
    that fail after wrapping the branch index `Z` onto `Z/n`.
- **A new kind of example.** `G'` is a finitely generated simple group with infinite-order
  parabolic germs and rational homology of a circle shifted up (`H_1(G; Q) = Q`). It is
  decidable and not finitely presented.
  - Reid noted that `G'` is finitely generated and simple. Now one also knows it is not
    finitely presented.
- **Positive side, for comparison.** Thompson's `T` also has parabolic germs, in its
  `PSL_2(Z)` picture, and is finitely presented.
  - The difference is the cut. In `T`, a parabolic point can be a breakpoint with independent
    left and right germs.
  - In `G` the two sides of a vertex are linked by one element of `<t>`. So the germ group
    sees the non-isolated group `Z`.

## Lesson for general BH

A parabolic (infinite-order, non-contracting) germ group at an infinite emitter is visible to
marked-group limits. If it is not isolated, the full group cannot be finitely presented,
however much Cantor room the rest of the space has. Emitters in a finitely presented host must
carry isolated germ groups, or germs that are cut, as in `T`. They cannot carry arbitrary
decidable finitely presented groups such as `Z`.
