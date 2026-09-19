---
rg: 2
id: fpbs-finite-index-overrelations-live-in-commensurator
kind: claim
title: A finite-index over-relation of a subgroup orbit relation only uses group elements that commensurate the subgroup, so almost malnormal subgroup relations have no proper finite-index over-relations
distinct_from:
  fpbs-malnormal-measured-absorption-cap: that caps chains of single partial isomorphisms with infinite contact, for almost malnormal subgroups, through a label argument (Theorem A, quasi-normalizer case of Corollary C); this is about an arbitrary intermediate relation E between E_K and E_a, for an arbitrary subgroup K, and identifies the label set of every finite-index piece as the one-sided commensurating set C_K by an invariant-measure argument on finite coset sets.
  fpbs-malnormal-cosets-admit-no-amenable-bridges: that constrains amenable subrelations meeting E_K in infinite pieces; this constrains every over-relation of E_K on the set where it has finite index, with no amenability.
  fpbs-relative-sandwich-cost-bernoulli-lower-bound: that is the open sandwich-cost comparison; this computes which sandwich relations can have finite index over E_{a|<F>}, which removes finite-index gluing from its F_2 test.
---

**ESTABLISHED** through `fpbs-finite-index-overrelations-live-in-commensurator-proof`.

Let `Γ` be countable, `a` a free p.m.p. action of `Γ` on `(X, μ)`, and
`K ≤ Γ` any subgroup. Put

    C_K = { g ∈ Γ : [K : K ∩ g^{-1} K g] < ∞ }.

Let `E` be a Borel equivalence relation with `E_{a|K} ⊆ E ⊆ E_a`. Let `Z` be
the set of `x` whose class `[x]_E` is a union of finitely many
`E_{a|K}`-classes.

1. **Theorem.** `Z` is `E`-invariant and Borel. For almost every `x ∈ Z`,
   every `γ ∈ Γ` with `γx E x` lies in `C_K`.
2. **Almost malnormal case.** Suppose `K` is infinite and almost malnormal,
   meaning `K ∩ g^{-1}Kg` is finite for `g ∉ K`. Then `C_K = K`, so
   `E|_Z = E_{a|K}|_Z`. So `E_{a|K}` has no over-relation of finite index
   `n ≥ 2` on any set of positive measure.
3. **Sandwich cost consequence.** Let `K = ⟨F⟩` be infinite and almost
   malnormal. Every sandwich relation `E_{a|⟨F⟩} ⊆ E ⊆ E_a` splits into two
   `E`-invariant pieces. On `Z` it equals `E_{a|K}`. On `X \ Z` every
   `E`-class contains infinitely many `E_{a|K}`-classes. So the index formula
   `C(E) - 1 = (C(E_{a|K}) - 1)/n` never lowers a sandwich cost over a
   malnormal `⟨F⟩`. Examples of such `F` are the malnormal rank-2 test
   subgroups `⟨a, bab^{-2}⟩ ≤ F_2` of
   `fpbs-relative-sandwich-cost-bernoulli-lower-bound` and of the
   `Γ_mal` stages. Every sandwich strictly below `C(E_{a|K})` must use
   infinite-index gluing on a set of positive measure.

**Scope.** The theorem is general. It is the orbit-equivalence form of the
group-theoretic fact that a subgroup `L ⊇ K` with `[L : K] < ∞` lies in the
commensurator of `K`. Its sharpest use is for almost malnormal `K`. It proves
nothing about the infinite-index part `X \ Z`, where the open sandwich-cost
question lives.
