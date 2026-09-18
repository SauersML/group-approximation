---
rg: 2
id: fpbs-saturated-cayley-repair-couples-to-ascending-union-proof
kind: route
title: Split any admissible family by letter, slide double-coset labels onto one letter, and transport a one-stage repair along the ascending union by its shift automorphism
target: fpbs-saturated-cayley-repair-couples-to-ascending-union
requires:
  - fpbs-relative-stage-costs-bound-cost-by-stage-liminf
  - fpbs-locally-free-free-action-costs-are-c-star-or-infinite
  - fpbs-shifted-stage-relative-cost-zero-or-infinite
  - fpbs-malnormal-coset-cycles-linear-perimeter
artifacts:
  - research/artifacts/fpbs-relative-cayley-cost-letter-saturation-2026-09-18.md
  - experiments/fpbs-relative-cayley-cost-2026-09-17/malnormal_check.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/census_usage.py
---

Written derivation. The details are in Sections 4–6 of the artifact.

1. **Proposition B.**
   - `<Phi_c cup S_v> = R_{H_c}`, so `Phi_c cup E` is admissible whenever `<R_{H_c} cup E> = R`. This gives the upper
     bound.
   - For an admissible `F_c cup F_d`, the relation `<R_{H_c} cup F_d>` contains `<F_c cup S_v cup F_d> = R`. So
     `mu(F_d) >= rho_d(H_c)`, and symmetrically for `F_c`. This gives the lower bound.
   - `RC >= 1` by Gaboriau's lecture notes, Corollary 2.25, verbatim: "The following groups are strongly treeable and
     have fixed price: C∗(Fn) = C∗(Fn) = n for the free group of rank n."
2. **Lemma 4.1.** A piece with label `h t^{e} h'` is replaced by the piece `(h' x, t^{e} h' x)` of `Phi_t`. It has the
   same measure, and its endpoints lie in the same `R_H`-classes as before.
3. **Corollary C.**
   - The restriction `beta_v|_{H_2}` is a Bernoulli shift of `F_2` over a standard nonatomic base. Here
     `(H_2, H_1) = (F_2, <c, v>)`, so Lemma 4.1 gives `relC(R_{H_2}; R_{H_1}) = 0`.
   - The shift automorphism of the direct limit moves `H_n` to `H_{n+1}` and conjugates `beta_v` to itself. So every
     consecutive stage pair has relative cost `0`.
   - The stage costs are `2`, by Corollary 2.25.
   - The integer case of `fpbs-relative-stage-costs-bound-cost-by-stage-liminf` gives `C(beta_v) <= 2`.
   - `fpbs-locally-free-free-action-costs-are-c-star-or-infinite` gives `= 2`.
   - This is the argument of Proposition 3, (1) ⇒ (2), in
     `research/artifacts/fpbs-relative-fixed-price-decomposition-2026-09-17.md`, and it uses only that the chain is the
     limit of one injective endomorphism.
   - For `Gamma_mal`, where `<c, ccdcDD> = <c, dcDD>`, the equivalent forms in
     `fpbs-mal-bernoulli-single-stage-floor`, via `fpbs-shifted-stage-relative-cost-zero-or-infinite`, turn
     `C(beta) = 2` into failure of the floor.
   - *Malnormal exhaustion.* Malnormality is transitive along `H <= K <= L`. So if `<c, v>` is malnormal, every
     `H_n` is malnormal in `Gamma_v`, and every finitely generated subgroup has proper malnormal hull.
4. **Packing floor.** Item 4 of `fpbs-malnormal-coset-cycles-linear-perimeter` applies to generators in `H t^{±1} H`.
   By Lemma 4.1 these are exactly the one-letter repairs.
5. **Class kill.**
   - *Lemma 6.1.* `t h_1 x ~_H t h_2 x` iff `h_1 h_2^{-1} in I`, by freeness.
   - *Lemma 6.2.* A cyclically reduced kernel element of `H * <t> -> F_2` reads as a closed non-backtracking walk in
     the class graph.
   - *Malnormality inputs.* The malnormality of `H_c(cdcDcd)`, `H_d(cdcDcd)` and `<c, dcDD>` is the Stallings
     product-graph certificate in `malnormal_check.py`.
   - *Contact counts.* The contact census is `census_usage.py`.
