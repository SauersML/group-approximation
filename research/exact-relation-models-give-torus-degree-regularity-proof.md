---
rg: 2
id: exact-relation-models-give-torus-degree-regularity-proof
kind: route
title: Exact actions of the local cover certify every vertex, the small-fibre lemma inverts the model degree, and co-sofic statistics transport a zero divisor into a rank contradiction
target: exact-relation-models-give-torus-degree-regularity
requires:
  - torus-automata-with-regular-degree-are-surjective
artifacts:
  - research/artifacts/sofic-torus-rectangular-small-fibre-2026-09-19.md
  - research/artifacts/lef-torus-small-fibre-2026-09-18.md
---

Full proof in `research/artifacts/sofic-torus-rectangular-small-fibre-2026-09-19.md`:
Section 2 (Lemma P), Section 5 (Theorem E, Corollary E1) and Section 6
(Proposition B).

1. **Lemma P.** At a vertex `v` of a finite set with permutations `s(w), s(f)` where the
   relators `R_(W,F)` fix `v`, put `x_(wf) = u_(s(f)^-1 s(w)^-1 v)` and `x_1 = u_v`. This
   is well defined. By Lemmas A and B, `eta/3`-closeness of the model outputs on
   `s(W)^-1 v` gives `|u_v - u'_v| < 1/16`.
2. **Theorem E.**
   - *Reduction to `G_0`.* Decompose over the cosets of `G_0 = <W ∪ F>`, so that
     `xi in Z[G_0]^d`.
   - *Invertible model degree.* In a finite `Gamma`-set every vertex is certified, so
     the model map has fibres `<= 1/16`, and [LEF] Theorem 1 makes `s(D)` invertible.
   - *Transport.* Lift the support of `xi` to `Gamma`. Co-soficity makes
     `s(xi) s(D)` vanish off `o(|V|)` rows, so `rank s(xi) = o(|V|)`.
   - *Contradiction.* The same statistics make the rows of `s(xi)` non-zero with
     proportionally many disjoint supports, so `rank s(xi) >= |V|/(|E|^2 + 1) - o(|V|)`.
3. **Corollary E1.** Apply stability to a sofic approximation of `G_0` read on the
   generators. It lies within `o(1)` of an exact action, and the fixed-point
   proportions pass to the limit.
4. **Proposition B.**
   - *Lemma B1.* Certification at every vertex is the relator identities, i.e. a
     `Gamma`-action.
   - *"If".* Take `W = F = K ∪ {1}` and `phi(k) = s(w_k) s(f_1)`. The relators
     `w_1 f_1 = 1`, `w_1 f_b = w_b f_1` and `w_a f_b = w_(ab) f_1` make `phi` a partial
     homomorphism. Co-soficity makes it injective. This is LEF.
   - *"Only if".* Given an LEF model `phi: K -> Q` on a large `K`, the left action of
     `Q` on itself through `phi` is an exact `Gamma`-action. Words of length `<= r` act
     trivially exactly when they lie in `N`, and freely otherwise.
