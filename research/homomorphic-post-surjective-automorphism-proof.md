---
rg: 2
id: homomorphic-post-surjective-automorphism-proof
kind: route
title: Push onto-ness of finitely supported configurations down the derived series, count factor sites in the centerless layer, and use direct finiteness on abelian layers
target: homomorphic-post-surjective-automata-are-automorphisms
requires: []
artifacts:
  - research/artifacts/homomorphic-post-surjective-automata-2026-09-19.md
---

## Why sufficient

Section numbers refer to the artifact, where every step is proved. The classical inputs are the Jordan–Hölder
theorem, compactness of `V^G`, and Lemma 1 of `research/artifacts/homomorphic-group-alphabet-surjunctivity-2026-09-16.md`
(the matrix calculus `alpha -> tau_alpha`, proved there).

- **Dictionary (Section 0).**
  - The local rule is a product of commuting homomorphisms `mu_m`.
  - Post-surjective means `L(V[G]) = V[G]`; pre-injective means a trivial finitely supported kernel.
  - Onto-ness passes to quotients, and bijectivity is assembled from a normal invariant subgroup and its quotient
    (five lemma).
- **Linear base (Section 1).**
  - Preimages of the unit vectors assemble a right inverse `tau_beta` with `alpha beta = 1`.
  - Direct finiteness gives `beta alpha = 1`.
  - Conversely `alpha beta = 1 != beta alpha` gives a post-surjective, non-pre-injective `tau_alpha` (sharpness).
- **Abelian alphabets (Section 2).**
  - Split into primary parts and filter by `p^i V`.
  - Onto-ness descends to each `p^i V[G]` by dividing by `p^i` sitewise before lifting.
  - Each graded piece is `F_p^d` with `p^d <= |V|`.
- **Centerless alphabets (Section 3), for every `G`.**
  - Onto-ness makes `mu` onto.
  - Commuting generating subgroups of a centerless group form a direct product, which gives Lemma 3.1.
  - So each indecomposable output factor reads one memory cell, and one input factor, through a surjection.
  - The factor-site map is then a product of maps `D_j -> prod_(phi^(-1)(j)) D_i`, each onto.
  - Counting `|W|` on both sides makes each of them bijective.
- **General `V` (Section 4).**
  - Derived subgroups are invariant, and onto-ness passes to them, because commutators of lifts are lifts of
    commutators.
  - The abelian layers are handled by Section 2.
  - On the perfect term `P`, the centre is invariant because the `mu_m(P)` generate `P` and commute. Grün's lemma
    makes `P/Z(P)` centerless, so Section 3 applies.
  - Injectivity on `P/Z(P)` gives onto-ness on `Z(P)[G]`, which is handled by Section 2.
- **Items 3–4 (Section 5).**
  - The equivalence is Theorem 4.2 plus Lemma 1.2.
  - For affine covers, lifts at one point give `L` onto `V[G]`. Theorem 4.2 then makes `L` bijective, the lifts are
    forced to be `x_0 w`, and `x_0 V[G]` is dense in `V^G`.
