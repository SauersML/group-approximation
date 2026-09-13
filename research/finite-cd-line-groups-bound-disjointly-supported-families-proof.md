---
rg: 2
id: finite-cd-line-groups-bound-disjointly-supported-families-proof
kind: route
title: Disjointly supported nontrivial homeomorphisms commute and are independent, and F' and Z wreath Z contain every Z^n
target: finite-cd-line-groups-bound-disjointly-supported-families
requires: []
artifacts:
  - research/artifacts/zp-left-orderable-simple-type-f-fences-2026-09-13.md
---

Artifact §1 (Lemma A, Corollaries A1 and A2). Imported at statement level (K. S. Brown, *Cohomology of
Groups*, VIII.2): `cd H ≤ cd G` for `H ≤ G`, and `cd Z^k = k`.

1. **Infinite order.** A nontrivial orientation-preserving homeomorphism `f` has infinite order: if
   `f(x) > x`, then induction gives `f^k(x) ≥ f(x) > x` for `k ≥ 1`.
2. **Commuting.** For `i ≠ j`, `g_j` fixes `supp(g_i)` pointwise, and `g_i` preserves `supp(g_i)`.
   Checking on each support and off both gives `g_i g_j = g_j g_i`.
3. **Independence.** On `supp(g_i)` the product `∏ g_k^{a_k}` acts as `g_i^{a_i}`. If the product is
   trivial, `g_i^{a_i}` is the identity on its own support, hence everywhere, so `a_i = 0` by step 1.
   So `Z^k ≅ ⟨g_1, …, g_k⟩ ≤ G` and `k ≤ d`.
4. **Item 2.** `F'` contains nontrivial elements supported in any `n` disjoint dyadic intervals of
   `(0,1)`. The base of `Z ≀ Z` contains `Z^n`. So `F' ≤ F` and `Z ≀ Z` contain every `Z^n` and have
   infinite `cd`, and neither embeds in `G`.
