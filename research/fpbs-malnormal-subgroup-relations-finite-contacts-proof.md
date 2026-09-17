---
rg: 2
id: fpbs-malnormal-subgroup-relations-finite-contacts-proof
kind: route
title: Count graphing edges between two subgroup classes by a coset of the intersection with the conjugate
target: fpbs-malnormal-subgroup-relations-finite-contacts
requires: []
artifacts:
  - research/artifacts/fpbs-finite-contact-obstruction-2026-09-17.md
---

Artifact §1–§2. The proof is self-contained: it uses freeness, invariance of
the measure and a coset count, and nothing is imported.

1. **Split the graphing.** By freeness, split every partial isomorphism of
   `Phi` into pieces `g|D`. The multiplicities `m_g` then satisfy
   `sum_g ∫ m_g = c(Phi)`.
2. **Integrate the outgoing edges.** An edge from `lambda x` through a piece
   `g` lands in `Lambda gamma x` exactly when `g lambda in Lambda gamma`. By
   invariance,
   `∫ N^+_gamma = sum_g ∫ m_g · #(Lambda ∩ g^{-1} Lambda gamma)`.
3. **Count the coset.** The set `Lambda ∩ g^{-1} Lambda gamma` is empty or a
   left coset of `I(gamma)`, because
   `lambda_0^{-1} lambda = gamma^{-1} mu_0^{-1} mu gamma`. Incoming edges are
   the outgoing edges for `gamma^{-1}` based at `gamma x`, and `I(gamma^{-1})`
   is conjugate to `I(gamma)`. This gives the factor 2.
4. **Finite contacts.** Integrable functions are finite almost everywhere.
   Intersecting over the countably many translates and the `gamma notin Q`
   gives an invariant conull set.
5. **Components.** Type `Q` depends only on the double coset
   `Lambda gamma Lambda`, so it is well defined for a pair of classes. Paths
   in the class graph multiply elements of `Q(Lambda)`, so a component lies in
   `<Q(Lambda)> x`. Contacts between `S`-classes project to contacts between
   `Lambda`-classes. Connectivity forces `<Q(Lambda)> x = Gamma x`, hence
   `<Q(Lambda)> = Gamma` by freeness.
6. **wq-normality.** Let `K ⊇ Lambda` be proper. Some `gamma in Q(Lambda)`
   lies outside `K`, and `gamma K gamma^{-1} ∩ K` contains
   `gamma I(gamma) gamma^{-1}`, which is infinite.
7. **Almost malnormal `M`.** `I(gamma) ⊆ M ∩ gamma^{-1} M gamma`, which is
   finite off `M`.
8. **`Gamma_mal`.** The malnormality of the stages is taken from the
   Stallings-graph certificate in
   `research/artifacts/fpbs-amalgam-descent-amenably-generated-2026-09-16.md`
   §5.1. Malnormality in each `H_m` for `m >= n` passes to the union.
