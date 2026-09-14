---
rg: 2
id: subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy
kind: claim
title: The automorphism inn(diag(u,1,1)) of G_X carries GL_3(LC(X,F_2)) to a subgroup that is not G_X-conjugate to any standard diagonal GL_3(B)
distinct_from:
  diagonal-recognition-makes-subshift-el3-isos-standard: that derives standardness from recognition of the diagonal; this shows that recognition up to G_Y-conjugacy fails for a standard automorphism, so the hypothesis must allow conjugation by the normalizer of G_Y in GL_3(R_Y)
  subshift-el3-isomorphisms-are-standard-over-f2: that asks whether every isomorphism is standard; this concerns only the position of the image of the diagonal subgroup, for an automorphism that is standard
artifacts:
  - research/artifacts/sk-diagonal-recognition-2026-09-13-part1.md
---

Let `X` be an infinite minimal subshift, `A = LC(X,F_2)`, `R = A ⋊_T Z`, `G = EL_3(R)`, `L = GL_3(A)`, and
`d = diag(u,1,1)`. Call a subalgebra `B ⊆ R` Boolean if it is commutative and spanned by its idempotents, and call
`GL_3(B)` its standard diagonal. For `g ∈ GL_3(R)` let `ind(g)` be the Fredholm index of the compression of `g` to the
half-orbit `⊕_{t≥0} F_2^3 δ_t` of a point.

1. `ind: GL_3(R) → Z` is a homomorphism that vanishes on `E_3(R)`, with `ind(d) = −1` and `ind(wI_3) ∈ 3Z` for
   `w ∈ R^×`.
2. If `k ∈ GL_3(R)` and `kM_3(A)k^{-1} = M_3(B)` for a Boolean `B`, then `k = c·wI_3` with `c ∈ GL_3(B)` and
   `w ∈ R^×`, `B = wAw^{-1}`, and `ind(k) ∈ 3Z`.
3. `inn(d)` is an automorphism of `G` that is not inner.
4. There are no `h ∈ G` and no Boolean `B ⊆ R` with `dLd^{-1} = hGL_3(B)h^{-1}`.
5. For `k ∈ GL_3(R)`, `ind(k) mod 3` is an invariant of the `G`-conjugacy class of `kLk^{-1}`. So `L`, `dLd^{-1}` and
   `d^2Ld^{-2}` are pairwise non-conjugate in `G`, and a standard diagonal can only be `G`-conjugate to `kLk^{-1}` when
   `ind(k) ≡ 0 mod 3`.

So `subshift-el3-isomorphisms-recognize-diagonal-subgroups`, which asks for `h ∈ G_Y`, is false, already for `X = Y`
and the isomorphism `inn(d)`. The corrected form allows `h` in the normalizer of `G_Y` in `GL_3(R_Y)`
(`subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer`).

Status: proved in `subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy-proof`, unreviewed.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived:
- the half-orbit index is a homomorphism vanishing on E_3(R), with ind(d) = −1;
- Lemma 2: pointwise matrix units give c ∈ GL_3(B) ⊆ E_3(R) and k = c·wI, so ind(k) ∈ 3Z;
- inn(d) is not inner (the centralizer of the root elements is {I});
- span transport of GL_3(F_2) and the mod-3 invariant.
See `research/artifacts/sk-verify-16-2026-09-13-part2.md` §4.
