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
* **Trivial bundles with product generating sets (partial, 2026-09-12).** For
  `M = S_g x S^1` with `g >= 3` and generating set standard surface generators
  plus `(1,±1)`, `p_c < p_{2->2} <= p_u`
  (`fpbs-surface-group-times-zk-product-sets-strict-thresholds`, the case `k = 1`).
  **Where it stops:** it is a perturbative comparison with the edge expansion of
  the `{4g,4g}` tiling. It gives nothing for genus two, for nontrivial bundles
  (central extensions have no product generating set), or for non-product
  generating sets.
* **Choi–Seo abstract L2 criteria (obstruction, 2026-09-19, swarm-0917
  w19).** The idea was to verify the hypotheses of Choi–Seo Theorems 2.9 and
  2.17 (arXiv:2508.08932v2), which give `p_c < p_(2->2)`.
  `fpbs-cs-barrier-hypothesis-fails-normal-cyclic` (ESTABLISHED) shows that
  both hypotheses fail on every Cayley graph of every group with an infinite
  cyclic normal subgroup. That includes every `pi_1(M)` here, via the regular
  fibre. **Where it dies:** the nested-barrier step. The core of an
  `r`-roughly branching set meets each coset of the fibre at most once, because
  two points collide at length 2. So at most `#B(r)#B(r+|z|)` disjoint
  barriers can separate `id` from any set meeting the fibre. **Invariant:**
  the fibre-coset multiplicity of branching cores. Any route through
  `p_c < p_(2->2)` here must count fibres instead, for example through
  `fpbs-fibre-bubble-forces-mean-field-susceptibility`.
