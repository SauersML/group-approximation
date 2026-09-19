---
rg: 2
id: residually-li-amenable-groups-are-torus-surjunctive-proof
kind: route
title: Specialize the universal Hughes-free division ring to the augmentation, so every matrix with invertible constants becomes invertible, and apply it to the degree matrix
target: residually-li-amenable-groups-are-torus-surjunctive
requires:
  - residually-li-amenable-hughes-free-rings-are-universal
  - torus-automata-over-rf-or-domain-groups-are-surjunctive
  - torus-automata-with-regular-degree-are-surjective
artifacts:
  - research/artifacts/residually-li-amenable-torus-2026-09-18.md
---

Full proof in `research/artifacts/residually-li-amenable-torus-2026-09-18.md`, Sections 2–4.

1. **Constants.** The periodic-point lemma of
   `torus-automata-over-rf-or-domain-groups-are-surjunctive`, at `N = G`, gives
   `epsilon(D) in GL_d(Z)` for every group.
2. **Lemma 4 (specializations invert matrices).**
   - *Setting.* Let `alpha: R_0 -> L` be a map to a division ring such that every element
     outside `ker alpha` is a unit of `R_0`.
   - *Claim.* A square `A` over `R_0` with `alpha(A)` invertible is invertible over `R_0`.
   - *Proof.* Gaussian elimination: some entry of the first column is a unit. Pivot on it and
     recurse on the Schur block.
3. **Theorem 1 (criterion).**
   - *Setting.* `Q[H] ⊆ E` for a division ring `E`, and every square `A` with `epsilon(A)`
     invertible is invertible over `E`.
   - *`D` is invertible over `E`.* By step 1, `epsilon(D)` is invertible over `Q`, so `D`
     has an inverse over `E`.
   - *Injectivity on `Q[H]^d`.* `x D = 0` forces `x = 0`.
   - *Injectivity on `Q[G]^d`.* Decompose over left cosets of `H`.
   - *Surjectivity.* `torus-automata-with-regular-degree-are-surjective` makes `tau` onto.
4. **Theorem 2 (RLA hosts).**
   - *Universal ring.* RLA groups are locally indicable (Lemma 5).
     `residually-li-amenable-hughes-free-rings-are-universal`, with `E = Q`, gives the
     universal division ring of fractions `U = D_{Q[H]}`.
   - *Specialization.* `epsilon: Q[H] -> Q` is an epic `Q[H]`-field, so universality gives a
     specialization `(R_0 ⊇ Q[H], alpha|Q[H] = epsilon)`.
   - *Conclusion.* By Lemma 4, every `A` with `epsilon(A)` invertible is invertible over
     `R_0 ⊆ U`. This is the hypothesis of Theorem 1.
5. **Proposition 3 and the Baumslag–Solitar corollary.**
   - *Free-by-(LI amenable) is RLA.* Use the quotients `G/K^(n)`. They are poly-(free
     abelian)-by-(LI amenable), which is LI by Lemma 5(c)–(d) and amenable. They separate
     `K`, by Magnus's theorem and `K^(i) ⊆ gamma_(2^i)(K)`.
   - *Baumslag–Solitar groups.* For `BS(m,n)`, the map `a -> 1`, `t -> t` into
     `Z[1/mn] ⋊_(n/m) Z` has kernel meeting every vertex stabilizer of the Bass–Serre tree
     trivially. So the kernel is free (Serre).
