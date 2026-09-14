---
rg: 2
id: singer-identities-make-subshift-el3-isos-standard
kind: claim
title: If an isomorphism G_X → G_Y sends each constant Singer cycle c_V to an element satisfying x³+x = S_V, and the constant Frobenius group has no fixed vectors, then the isomorphism is standard and X, Y are strongly orbit equivalent
distinct_from:
  frobenius-support-idempotents-give-boolean-realization: that assumes the ring identities (O) and (O′) and stops at a Boolean algebra centralizing α(L_X); this derives (O) from the Singer identities and goes on to root subgroups and standardness
  diagonal-recognition-makes-subshift-el3-isos-standard: that assumes α(L_X) is G_Y-conjugate to GL_3(B) with B maximal commutative; this produces the conjugate from the Singer identities and replaces maximality by generation
  subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer: that is the open recognition statement; this is a sufficient condition for it, stated as polynomial identities for images of elements of order 7
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part1.md
---

Let `X, Y` be infinite minimal subshifts, `G_X = EL_3(LC(X,F_2) ⋊ Z)` and likewise `G_Y`, and let `α: G_X → G_Y` be an
isomorphism. Let `c ∈ GL_3(F_2)` be a Singer cycle with `c³+c+I = 0`, `F21 = ⟨c,s⟩` its Frobenius normalizer, `c_V` and
`F21_V` the copies constant on a clopen `V`, and `S_V = I + Σ_{k∈α(F21_V)} k`. Assume:
- **(Sing)** `α(c_V)³ + α(c_V) = S_V` for every clopen `V`;
- **(O′)** `S_X = I`.

Then:
- `S_VS_W = 0` for disjoint `V, W`;
- `α(GL_3(LC(X,F_2))) = k·GL_3(𝔅′)·k^{-1}` for some `k ∈ GL_3(R_Y)` and a Boolean subalgebra `𝔅′ ≅ LC(X,F_2)`;
- `inn(k^{-1})∘α` maps every root subgroup onto the corresponding root subgroup.

So `α` is standard, and `X` and `Y` are strongly orbit equivalent.

Status: proved in `singer-identities-make-subshift-el3-isos-standard-proof`, unreviewed. The proof imports:
- the unreviewed index kernel theorem `subshift-gl3-index-kernel-is-elementary-group`;
- a division step for clopen classes in `K^0(Y,T)`, which is Lemma 2.5 of H. Matui, arXiv:math/0404224, quoted in the
  artifact.

Model tests: the identity and `inn(diag(u,1,1))` satisfy (Sing) and (O′). The graph automorphism has type `3*` and
fails (Sing), so the theorem applies after composing with it. The natural ⊕ trivial fake fails (O′). The Steinberg
fake fails (Sing).
