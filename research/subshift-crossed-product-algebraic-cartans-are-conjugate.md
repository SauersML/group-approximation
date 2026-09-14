---
rg: 2
id: subshift-crossed-product-algebraic-cartans-are-conjugate
kind: claim
title: Open - every algebraic Cartan subalgebra of LC(X,F_2)⋊Z, for an infinite minimal subshift X, is the image of the diagonal under a ring automorphism
distinct_from:
  subshift-elementary-group-diagonal-iso-gives-flip-conjugacy: that proves flip rigidity for group isomorphisms that preserve the diagonal subgroup; this asks whether every Cartan subalgebra of the ring is conjugate to the diagonal, step (ii) of its Firewall F2
  cantor-crossed-product-matrix-ring-iso-forces-soe: that turns a ring isomorphism into strong orbit equivalence through the ordered K_0; this asks about the diagonal itself, which would give flip conjugacy
---

**OPEN.** Setting:
- `X` is an infinite minimal subshift with shift `T`, `R_X = LC(X,F_2) ⋊_T Z` and `D_X = LC(X,F_2) ⊆ R_X`.
- A subalgebra `B ⊆ R_X` is an **algebraic Cartan subalgebra** if `(R_X, B)` is an algebraic Cartan pair in the
  sense of Armstrong–de Castro–Clark–Courtney–Lin–McCormick–Ramagge–Sims–Steinberg (IMRN 2021, arXiv:2101.08556,
  Definition `def:ACP`). Concretely, `B` is commutative and spanned by its idempotents, the normalisers of `B` span
  `R_X`, a faithful conditional expectation `R_X → B` exists, and `B` is maximal commutative.
- `D_X` is such a subalgebra.

Question: is every algebraic Cartan subalgebra of `R_X` equal to `β(D_X)` for a ring automorphism `β` of `R_X`?

What a yes gives:
- **Groupoid form.** It is equivalent to: every effective ample Hausdorff groupoid `G` with `A_{F_2}(G) ≅ R_X` as rings
  is isomorphic to the transformation groupoid of `(X,T)`. The reduction is being landed by lane sk-rigidity-cartan.
- **Ring rigidity.** For every minimal Cantor system `(Y,S)`, `R_Y ≅ R_X` as rings forces flip conjugacy.
- **Group rigidity.** Suppose recognition holds: every isomorphism `G_X → G_Y` carries `GL_3(D_X)` onto `GL_3(B)` for
  an algebraic Cartan `B ⊆ R_Y`, up to `Aut(G_Y)`. Then `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`
  turns a yes for `Y` into "`G_X ≅ G_Y` implies flip conjugacy".

## Attempts

- **K-theory: dies.**
  - The unital ordered `K_0` of `R_X` is `K^0(X,T)` (`cantor-crossed-product-matrix-ring-iso-forces-soe`). It sees only
    strong orbit equivalence, and every Cartan model of `R_X` shares it.
  - The C*-analogue of uniqueness is false. Giordano–Putnam–Skau (1995) give `C(X)⋊Z ≅ C(Y)⋊Z` for strongly orbit
    equivalent systems that are not flip conjugate, and the image of `C(Y)` is then a non-conjugate Cartan.
  - So a proof must use a feature of the algebraic ring that the C*-completion forgets.
- **Growth: partial, in progress in this lane.**
  - Growth of `R_X` is equivalent to `n·p_X(n)` (Nekrashevych, IJAC 26 (2016), Proposition `pr:shiftgrowth`). It is a
    ring invariant that sees entropy and polynomial complexity, which strong orbit equivalence forgets.
  - It says nothing between two systems of equal complexity growth in one strong orbit equivalence class, so by itself it
    does not reach flip conjugacy.
- **Minimal idempotents: dies.** `R_X` has none (Firewall F-MIN in `subshift-el3-isomorphisms-are-standard-over-f2`),
  so rank-one methods cannot single out a Cartan.
- **Corners, towers, Morita: nothing new.**
  - Clopen sets of equal class in `K^0` are full-group equidecomposable, so corners are conjugate by diagonal-preserving
    maps (sk-rigidity-intrinsic artifact §5 F3).
  - The tower identity `R_{X^(k)} ≅ M_k(R_X)` sends diagonal to diagonal.
  - So corners and matrix amplifications give no non-conjugate Cartan.
