---
rg: 2
id: fpbs-seifert-fibred-every-generating-set
kind: claim
root: true
title: Every Cayley graph of a Seifert-fibred 3-manifold group with hyperbolic base has strict thresholds
distinct_from:
  fpbs-product-every-generating-set: that is the direct-product class; Seifert-fibred groups are central or cyclic-normal extensions of Fuchsian groups and are in general not direct products, so neither claim contains the other.
  fpbs-amenable-wq-normal-class-nonuniqueness: that is the general class with an infinite amenable wq-normal subgroup; this is the 3-manifold instance posed as an open question by Choi--Seo.
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
---

**OPEN.** Let `M` be a closed Seifert-fibred 3-manifold whose base orbifold is
hyperbolic. Then for every finite symmetric generating set `S` of `pi_1(M)`,

```text
p_c(Cay(pi_1(M),S)) < p_u(Cay(pi_1(M),S)).
```

This is Choi--Seo arXiv:2508.08932, Question 1.6 ("for every Seifert fibered
space M, does Benjamini--Schramm conjecture hold for pi_1(M)?"). The fibre
subgroup is infinite cyclic and normal and the quotient is a non-elementary
Fuchsian group, so `pi_1(M)` is nonamenable, has an infinite amenable normal
subgroup, and is not acylindrically hyperbolic. By
`fpbs-bs-iff-finite-relative-susceptibility` the claim is equivalent to finite
expected intersection of slightly supercritical clusters with the fibre
subgroup.

## Attempts

* **Special case of the amenable wq-normal class.** Route
  `fpbs-seifert-fibred-from-amenable-wq-normal-class`. Its premise is open; see
  `fpbs-amenable-wq-normal-relative-subcriticality` for where the direct attacks
  stop.
