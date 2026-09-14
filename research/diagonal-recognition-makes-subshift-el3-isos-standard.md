---
rg: 2
id: diagonal-recognition-makes-subshift-el3-isos-standard
kind: claim
title: An isomorphism G_X → G_Y carrying GL_3(LC(X,F_2)) onto GL_3(B), for any maximal commutative idempotent-spanned subalgebra B of R_Y, is standard, so X and Y are strongly orbit equivalent
artifacts:
  - research/artifacts/sk-iso-rigidity-2026-09-13-part2.md
distinct_from:
  subshift-elementary-group-diagonal-iso-gives-flip-conjugacy: that needs the image of the diagonal subgroup to be GL_3(LC(Y,F_2)) itself and gets flip conjugacy; this allows GL_3(B) for any Cartan-type B and gets standardness and strong orbit equivalence
  subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity: its item 5 needs this recognition hypothesis together with Cartan uniqueness to get flip conjugacy; this shows the recognition hypothesis alone already gives standardness and strong orbit equivalence
  peirce-root-preserving-subshift-el3-isos-force-orbit-equivalence: that assumes the images of the root subgroups are Peirce root groups; this derives that from the image of the locally constant diagonal subgroup
---

Let `X, Y` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊ Z`, `G_X = EL_3(R_X)`, and
`L_X = GL_3(LC(X,F_2)) = LC(X, GL_3(F_2))`. Let `B ⊆ R_Y` be a subalgebra that is:
- commutative and spanned over `F_2` by its idempotents, so `B ≅ LC(Ω,F_2)` for a Stone space `Ω`;
- maximal commutative: `C_{R_Y}(B) = B`.

If `α: G_X → G_Y` is an isomorphism with `α(L_X) = h GL_3(B) h^{-1}` for some `h ∈ G_Y`, then there is a ring
isomorphism `Θ: M_3(R_X) → M_3(R_Y)` and `h′ ∈ G_Y` with:
- either `α(g) = h′Θ(g)h′^{-1}` for all `g`,
- or `α(g) = h′Θ(g*)^{-1}h′^{-1}` for all `g`, where `(g*)_ij = τ(g_ji)` and `τ(Σ f_ju^j) = Σ u^{-j}f_j`.

So `M_3(R_X) ≅ M_3(R_Y)`, and `X` and `Y` are strongly orbit equivalent.

The key step excludes a locally mixed orientation. Such an isomorphism is inner on one clopen piece of `Ω` and the
graph automorphism on the other, and the Steinberg relations rule it out once both pieces are nonempty, because
`R_Y` is simple. Over a product ring, where the pieces are central, such mixed isomorphisms do exist (Petechuk's
exceptional case).

With Cartan uniqueness at `Y` (`subshift-crossed-product-algebraic-cartans-are-conjugate`), the conclusion
improves to flip conjugacy (`subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`, item 5).

Status: proved in `diagonal-recognition-makes-subshift-el3-isos-standard-proof`, unreviewed.

**Scope (sk-diagonal-recognition, 2026-09-13).** The hypothesis may allow `h` in the normalizer
`N_Y = N_{GL_3(R_Y)}(G_Y)` instead of `G_Y`: the proof's first move, replacing `α` by `inn(h^{-1})∘α`, needs only
`h^{-1}G_Yh = G_Y`. The conclusion then gives `h′ ∈ GL_3(R_Y)`. This matters because the `G_Y`-conjugacy form of the
hypothesis fails for the standard automorphism `inn(diag(u,1,1))`
(`subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy`). The corrected recognition target is
`subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer`.

**Review (sk-verify-15, 2026-09-13): PASS-WITH-FIXES.** Pointwise form, normalization, double centralizers, and the exclusion of mixed orientation (W-conjugation identities, X_0² = Z_0² = 0, (1,2)-entry psq of the commutator, zero (1,2)-entries in M_13) re-derived. F3: give the reason c is a unit (row 2 of g is (0,c,0) and column 1 is (c,0,0)^T). Imports: `locally-constant-simple-group-normal-subgroups-are-open-sets` has no review line; Out(L_3(2)) = 2 recalled. See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §3.
