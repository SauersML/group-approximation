---
rg: 2
id: subshift-el3-isomorphisms-recognize-diagonal-subgroups
kind: claim
title: Open - every isomorphism G_X → G_Y between the note's simple Kazhdan groups carries GL_3(LC(X,F_2)) to a conjugate of GL_3(B) for a maximal commutative idempotent-spanned subalgebra B of R_Y
refuted_by:
  - subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy
artifacts:
  - research/artifacts/sk-iso-rigidity-2026-09-13-part2.md
  - research/artifacts/sk-diagonal-recognition-2026-09-13-part1.md
distinct_from:
  diagonal-recognition-makes-subshift-el3-isos-standard: that proves what this recognition statement gives, namely standardness and strong orbit equivalence; this is the recognition statement itself
  subshift-el3-isomorphisms-are-standard-over-f2: that asks for standardness of every isomorphism; this is a sufficient condition for it, stated as a property of one subgroup
  subshift-crossed-product-algebraic-cartans-are-conjugate: that asks whether every Cartan-type B is conjugate to the diagonal; this asks whether group isomorphisms produce such a B at all
---

**OPEN.** Let `X, Y` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊ Z`, `G_X = EL_3(R_X)`, and
`L_X = GL_3(LC(X,F_2))`. Question: for every group isomorphism `α: G_X → G_Y`, is `α(L_X) = hGL_3(B)h^{-1}` for some
`h ∈ G_Y` and some subalgebra `B ⊆ R_Y` that is commutative, spanned by its idempotents, and maximal commutative?

Consequences of a yes:
- every isomorphism `G_X ≅ G_Y` is standard, so `M_3(R_X) ≅ M_3(R_Y)` and `X` and `Y` are strongly orbit equivalent
  (`diagonal-recognition-makes-subshift-el3-isos-standard`);
- with Cartan uniqueness at `Y`, `X` and `Y` are flip conjugate
  (`subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`, item 5).

What holds for free:
- `α(L_X) ≅ LC(X, GL_3(F_2))`;
- `C_{G_Y}(α(L_X)) = 1`, since `C_{G_X}(L_X) = 1`;
- the normalizer of `α(L_X)` acts on its maximal normal subgroups through a copy of a group between `[[T]]'` and
  `[[T]]` (`subshift-elementary-group-rigid-supports-are-mutual-centralizers`, transported by `α`).

## Attempts

- **Finite constant subgroups (sk-iso-rigidity, not carried out).** For a clopen partition `𝒫` of `X`, the constant
  pieces form a finite subgroup `GL_3(F_2)^{|𝒫|} ≤ L_X`. Its image is a representation on `R_Y^3`.
  - The block idempotents of `F_2[GL_3(F_2)]` (principal and Steinberg blocks) give idempotents of `M_3(R_Y)`.
  - What is needed: the image spans `M_3(F_2)`-type matrix units, i.e. only the natural or dual module occurs with
    projective multiplicity, before `B` can be read off.
  - Obstacle: `F_2[GL_3(F_2)]` is not semisimple, so non-split extensions with the trivial module are not excluded a
    priori.
- **Where a counterexample would live.** It would be a subgroup of `G_Y` isomorphic to `LC(Z, GL_3(F_2))`, with
  trivial centralizer and a normalizer acting like a full group, whose span is not `M_3(B)` for any Cartan-type `B`.
  None is known.
