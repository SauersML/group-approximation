---
rg: 2
id: subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer
kind: claim
title: Open - every isomorphism G_X → G_Y carries GL_3(LC(X,F_2)) to k·GL_3(B)·k^{-1} for some k normalizing G_Y in GL_3(R_Y) and a maximal commutative idempotent-spanned B ⊆ R_Y
distinct_from:
  subshift-el3-isomorphisms-recognize-diagonal-subgroups: that asks for conjugation by G_Y itself and is refuted by inn(diag(u,1,1)); this allows the normalizer of G_Y in GL_3(R_Y), which is what the standardness theorem needs
  subshift-el3-isomorphisms-are-standard-over-f2: that asks for standardness of every isomorphism; this is a sufficient condition for it, stated as a property of one subgroup
artifacts:
  - research/artifacts/sk-diagonal-recognition-2026-09-13-part1.md
---

**OPEN.** Let `X, Y` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊ Z`, `G_X = EL_3(R_X)`, `L_X = GL_3(LC(X,F_2))`,
and `N_Y = N_{GL_3(R_Y)}(G_Y)`. For every group isomorphism `α: G_X → G_Y`, are there `k ∈ N_Y` and a commutative,
idempotent-spanned, maximal commutative subalgebra `B ⊆ R_Y` with `α(L_X) = k·GL_3(B)·k^{-1}`?

Consequences of a yes:
- `inn(k^{-1})∘α` carries `L_X` onto `GL_3(B)`. So by the proof of `diagonal-recognition-makes-subshift-el3-isos-standard`,
  `α` is standard, `M_3(R_X) ≅ M_3(R_Y)`, and `X` and `Y` are strongly orbit equivalent.
- `ind(k) mod 3 ∈ Z/3` is then an invariant of `α` (`subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy`,
  item 2).

`N_Y` contains `G_Y` and every diagonal unit `diag(v_1,v_2,v_3)`, so `inn(diag(u,1,1))` satisfies this form, although
it fails the `G_Y`-conjugacy form.

## Attempts

- **Intrinsic reformulation through the hull (sk-diagonal-recognition).**
  - For `H ≤ G_Y` with `H ≅ LC(Z,Q)`, write `H_V` for its elements supported in `V`. Put `H^♮_V = C_{G_Y}(H_{Z∖V})` and
    `Ĥ = ⋂_V N_{G_Y}(H^♮_V)`.
  - On the `X`-side, `L^♮_U = G_U` and `L̂ = L` (C3, C4 of `subshift-elementary-group-rigid-supports-are-mutual-centralizers`).
    So `α(L_X)` is self-hull, has trivial centralizer, and its companions are mutual centralizers.
  - A classification of such subgroups of `G_Y` with `Q = GL_3(F_2)` would give a yes.
  - Sketched fakes and where they fail:
    - a Steinberg-type copy (8-dimensional module, dyadic `K_0`) fails self-hull;
    - natural ⊕ trivial and natural with multiplicity two fail trivial centralizer.
  - Where it dies: no proof that the companions come from commuting idempotents of `M_3(R_Y)`. Artifact
    `research/artifacts/sk-diagonal-recognition-2026-09-13-part1.md` §4.
- **Block idempotents of `F_2[GL_3(F_2)]` (sk-iso-rigidity).** Where it dies: the group algebra is not semisimple.
- **Orbit modules (sk-free-2's 2-transitive stabilizers `H_x`).** Where it dies: classifying the maximal subgroups of
  `G_Y` with 2-transitive coset actions of linear type.
