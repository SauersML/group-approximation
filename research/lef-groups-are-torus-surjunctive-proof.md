---
rg: 2
id: lef-groups-are-torus-surjunctive-proof
kind: route
title: Exact finite models of an injective torus automaton have small fibres, so a dimension-free small-fibre lemma makes their degree invertible
target: lef-groups-are-torus-surjunctive
requires:
  - torus-automata-with-regular-degree-are-surjective
artifacts:
  - research/artifacts/lef-torus-small-fibre-2026-09-18.md
---

Full proof in `research/artifacts/lef-torus-small-fibre-2026-09-18.md`, Sections 2–3.

1. **Small-fibre lemma (Theorem 1).**
   - *Claim.* If `f: T^N -> T^N` has fibres of sup-diameter `<= 1/16`, then `f` is onto
     and `f^*` is bijective on `H^1`.
   - *Coarse inverse.* Compactness gives a modulus `eta`. Cover the image by
     `r`-balls with `r < eta/2`. Choose preimages of the centres. The pairwise
     displacements have norm `< 1/8`, and a partition of unity glues them into a
     continuous `h` on a neighbourhood `O` of the image with `h o f ≃ id`.
   - *Surjectivity.* If `f` missed a point `p`, choose `O` missing `p`. Then
     `H^N(O; Q) = 0` by Hatcher Prop. 3.29 ("If M is a connected noncompact
     n-manifold, then H_i(M;R) = 0 for i ≥ n") and universal coefficients. But the
     identity of `H^N(T^N; Q) = Q` would factor through it, a contradiction.
   - *`H^1`.* `f^*` is a split surjection of `Z^N`, hence bijective.
2. **Exact finite models (Lemmas A–C).**
   - *Uniform injectivity (Lemma A).* Since `tau^-1` is uniformly continuous, there
     are a finite `W` and `eta > 0` such that closeness of `tau(x), tau(y)` on `W` gives
     closeness of `x, y` at `1`.
   - *Finite memory (Lemma B).* A finite-memory `mu'` on `F`, within `eta/3` of
     `mu = ev_1 o tau`, has the same degree data.
   - *The model map.* For an LEF model `phi: K -> Q` with `K ⊇ W ∪ F ∪ WF`, put
     `tau_Q(u)_q = mu'(u(q phi(f)))_(f in F)`. Then `tau_Q^* = (right multiplication by
     phi(D))`.
   - *Small fibres (Lemma C).* Pull configurations on `Q` back along `phi` on `WF`.
     Lemma A then shows that the fibres of `tau_Q` have diameter `< 1/16`.
3. **Conclusion (Theorem 2).**
   - Theorem 1 gives `phi(D) in GL_d(Z[Q])`.
   - A zero divisor relation `xi D = 0` (or `D xi = 0`) survives under `phi` once `K`
     also contains `supp xi`, and `supp xi · F` (resp. `F · supp xi`). It would then
     contradict invertibility, since `phi` is injective on `supp xi`.
   - So `D` is regular, and the ESTABLISHED
     `torus-automata-with-regular-degree-are-surjective` makes `tau` onto.
