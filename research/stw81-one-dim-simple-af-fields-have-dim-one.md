---
rg: 2
id: stw81-one-dim-simple-af-fields-have-dim-one
title: One-dimensional locally trivial simple AF fields have nuclear dimension at most one
kind: claim
distinct_from:
  stw81-one-dim-elementary-oinfty-fields-have-dim-one: that theorem permits elementary or O-infinity-stable fibres; this treats stably finite non-elementary simple AF fibres by a direct two-colour construction.
  stw81-zero-dim-simple-fields-obey-trichotomy: that theorem permits arbitrary simple nuclear fibres but requires a zero-dimensional base; this permits a one-dimensional base using the zero-colour AF approximation.
  stw81-separable-subhomogeneous-positive: an infinite-dimensional simple AF fibre is not subhomogeneous.
artifacts:
  - research/artifacts/stw81-one-dimensional-af-field-audit-2026-08-30.md
---

# One-dimensional locally trivial simple AF fields have nuclear dimension at most one

## Theorem

Let `X` be a second-countable locally compact Hausdorff space with
`dim(X)<=1`, let `D` be an infinite-dimensional simple unital AF algebra,
and let `A` be the section algebra of a locally trivial C-star bundle over
`X` with fibre `D`. Then

```text
dim_nuc(A) <= 1.
```

Moreover, for every ideal `I` of `A`, the quotient `A/I` has no nonzero
commutative hereditary subalgebra. Consequently `A` satisfies the hypothesis
of Problem LXXXI and its nuclear dimension belongs to `{0,1}`.

More generally, the same construction gives

```text
dim_nuc(A) <= dim(X)
```

whenever `X` has finite covering dimension; the shadow-vanishing assertion
does not require any bound on `dim(X)`. The one-dimensional conclusion is
the case relevant to Problem LXXXI.

This includes locally trivial UHF bundles over one-dimensional bases. It is
not covered by the elementary-fibre theorem: an infinite-dimensional unital
simple AF algebra is stably finite and non-elementary.

## Mechanism

On a compact part of the base relevant to a finite set of sections, refine
the trivializing cover into two families whose members are pairwise disjoint
within each family. Sample each section at one point in every patch and use
the AF property to replace the sampled fibre values by a finite-dimensional
subalgebra. Multiplication by the subordinate partition functions gives one
order-zero return map per colour. No separate fibre colour is needed.

The shadow assertion is fibrewise. Since the fibres are simple, ideals of
the locally trivial field are exactly the ideals associated to open subsets
of `X`, and every quotient is the restriction of the same bundle to a closed
subset. A nonzero commutative hereditary subalgebra in such a quotient would
have a nonzero commutative hereditary image in one fibre `D`. That would make
the simple algebra `D` Morita equivalent to a commutative algebra, hence
elementary, contrary to the hypotheses.

## Scope

The proof uses local triviality essentially to compare nearby fibre values
inside one fixed copy of `D`, and uses the AF property essentially to make
the fibre approximation with an order-zero return map carrying no additional
colour. It does not yet treat non-locally-trivial fields or simple stably
finite fibres of positive nuclear dimension such as the Jiang--Su algebra.
