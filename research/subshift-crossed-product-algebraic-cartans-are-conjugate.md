---
rg: 2
id: subshift-crossed-product-algebraic-cartans-are-conjugate
kind: claim
title: Open - every algebraic Cartan subalgebra of LC(X,F_2)⋊Z, for an infinite minimal subshift X, is the image of the diagonal under a ring automorphism
distinct_from:
  subshift-elementary-group-diagonal-iso-gives-flip-conjugacy: that proves flip rigidity for group isomorphisms that preserve the diagonal subgroup; this asks whether every Cartan subalgebra of the ring is conjugate to the diagonal, step (ii) of its Firewall F2
  cantor-crossed-product-matrix-ring-iso-forces-soe: that turns a ring isomorphism into strong orbit equivalence through the ordered K_0; this asks about the diagonal itself, which would give flip conjugacy
  subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity: that proves the reduction and the consequences; this is the open statement itself
---

**OPEN.** Setting:
- `X` is an infinite minimal subshift with shift `T`, `R_X = LC(X,F_2) ⋊_T Z` and `D_X = LC(X,F_2) ⊆ R_X`.
- A subalgebra `B ⊆ R_X` is an **algebraic Cartan subalgebra** if `(R_X, B)` is an algebraic Cartan pair
  (`algebraic-cartan-pairs-are-effective-groupoid-steinberg-algebras`). Concretely, `B` is commutative and spanned by its
  idempotents, the normalisers of `B` span `R_X`, a faithful conditional expectation `R_X → B` exists, and `B` is maximal
  commutative.
- `D_X` is such a subalgebra.

Question: is every algebraic Cartan subalgebra of `R_X` equal to `β(D_X)` for a ring automorphism `β` of `R_X`?

What is established (`subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`):
- **Groupoid form.** The question is equivalent to: every effective ample Hausdorff groupoid `G` with
  `A_{F_2}(G) ≅ R_X` as rings is isomorphic to the transformation groupoid of `(X,T)`. Every such `G` is minimal with
  Cantor unit space.
- **Ring rigidity.** A yes for `X` gives: every infinite minimal subshift `Y` with `R_Y ≅ R_X` is flip conjugate to `X`.
- **Group rigidity.** Suppose recognition holds: every isomorphism `G_Y → G_X` carries `GL_3(D_Y)` onto `GL_3(B)` for an
  algebraic Cartan `B`. Then a yes for `X` gives "`G_X ≅ G_Y` iff flip conjugate", by
  `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`.
- **Not literal equality.** Cartans are not unique as subsets: `w = 1 + e_U u` with `U ∩ TU = ∅` gives
  `wD_Xw^{-1} ≠ D_X` (artifact `research/artifacts/sk-rigidity-cartan-2026-09-13-part1.md` §4).

## Attempts

- **K-theory: dies.**
  - The unital ordered `K_0` of `R_X` is `K^0(X,T)` (`cantor-crossed-product-matrix-ring-iso-forces-soe`). It sees only
    strong orbit equivalence, and every Cartan model of `R_X` shares it.
  - The C*-analogue of uniqueness is false. Giordano–Putnam–Skau (1995) give `C(X)⋊Z ≅ C(Y)⋊Z` for strongly orbit
    equivalent systems that are not flip conjugate, and the image of `C(Y)` is then a non-conjugate Cartan.
  - So a proof must use a feature of the algebraic ring that the C*-completion forgets.
- **Growth: partial.** `subshift-ring-isomorphism-preserves-soe-class-and-growth`:
  - growth `≈ n·p_X(n)`, so zero entropy and the upper complexity exponent are ring invariants;
  - it says nothing between two models of equal complexity growth in one strong orbit equivalence class.
- **Minimal idempotents: dies.** `R_X` has none (Firewall F-MIN in `subshift-el3-isomorphisms-are-standard-over-f2`),
  so rank-one methods cannot single out a Cartan.
- **Corners, towers, Morita: nothing new.**
  - Clopen sets of equal class in `K^0` are full-group equidecomposable, so corners are conjugate by diagonal-preserving
    maps (sk-rigidity-intrinsic artifact §5 F3).
  - The tower identity `R_{X^(k)} ≅ M_k(R_X)` sends diagonal to diagonal.
  - So corners and matrix amplifications give no non-conjugate Cartan.
- **Sharpest decider.** Either find a ring isomorphism `R_X ≅ R_Y` between strongly orbit equivalent, non-flip-conjugate
  subshifts of equal complexity growth, or show that every effective groupoid model of `R_X` carries a continuous
  `Z`-cocycle whose kernel is a principal AF subgroupoid, which would identify it with a transformation groupoid.
