---
rg: 2
id: stw95-semisplit-successor-filtration-reduction
kind: claim
title: Semisplit successor filtrations preserve local tensor purity without exactness
distinct_from:
  stw95-nuclear-successor-filtrations-need-no-exact-factor: that obtains cpc sections uniformly from nuclearity of the successor quotients; this isolates semisplitting itself as the exact hypothesis and permits nonnuclear cells.
  stw95-transfinite-exact-filtration-reduction: that permits arbitrary successor extensions but requires the tensor factor to be exact; this permits an arbitrary tensor factor but requires each successor extension to be cpc semisplit.
artifacts:
  - research/artifacts/stw95-strongly-purely-infinite-cellular-tensor-audit-2026-08-30.md
---

Let `D` be any C*-algebra.  Let `E` be separable and admit a continuous
increasing filtration `(J_alpha)_(alpha<=gamma)` by closed ideals, indexed
by an arbitrary ordinal.  At every successor stage put

```text
L_alpha=J_(alpha+1)/J_alpha
```

and suppose the quotient map `J_(alpha+1)->L_alpha` has a completely
positive contractive section.  If every

```text
D tensor_min L_alpha
```

is pure, then `D tensor_min E` is pure.  No exactness or separability
assumption is imposed on `D`, and the cells need not be nuclear.
