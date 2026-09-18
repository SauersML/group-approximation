---
rg: 2
id: adelic-deck-lifts-exclude-affine-q-n-and-fp-bases-proof
kind: route
title: The deck group Q^n is a normal subgroup of the lift group, so the normal-Q^n lemma bounds the monodromy and forbids a finitely presented base
target: adelic-deck-lifts-exclude-affine-q-n-and-fp-bases
requires: [fg-groups-with-normal-q-n-have-non-fp-quotients]
---

**Deck group.** `Q^n` acts freely on `A^n` by translation, so `q -> τ_q` is an isomorphism `Q^n ≅ D`.

**Monodromy.** By hypothesis `D` is normal in `L̃`. So for `f ∈ L̃` the map `τ_q -> f τ_q f^{-1}` is an
automorphism of `D ≅ Q^n`, which is `Q`-linear. This defines `μ(f) ∈ GL_n(Q)` with `f τ_q f^{-1} = τ_{μ(f) q}`,
and `μ` is the conjugation action of `L̃` on its normal subgroup `D`.

**Parts 1 and 2.** Apply `fg-groups-with-normal-q-n-have-non-fp-quotients` with `H = L̃` and `N = D`. Its part 1
is part 1 here. Its part 2 says `L̃/D = L` is not finitely presented.

**Consequences.**
- **No finitely presented base.** If `L` is finitely presented, then `L̃` cannot be finitely generated, by part 2.
- **No natural affine part.** Suppose `G ⋉ D' <= L̃` is a copy of `Aff_n(Q)` with `D' = D` its translation
  subgroup and `G ≅ GL_n(Q)` its linear part. In `Aff_n(Q)`, conjugation by `g ∈ G` acts on the translations by
  the natural representation. So `μ(G)` is the image of `GL_n(Q)` under the natural action of `G` on `D`, taken
  through a `Q`-linear identification `D ≅ Q^n`, and that image is all of `Aut(D) = GL_n(Q)`. This contradicts
  part 1, because `GL_n(Q) ⊄ GL_n(Z[1/m])`.

The two consequences named in the claim for `GL_{n+1}(Q)` and for `Aff(Q)` are the cases of the second
consequence with `Aff_n(Q) <= GL_{n+1}(Q)` and with `n = 1`. ∎
