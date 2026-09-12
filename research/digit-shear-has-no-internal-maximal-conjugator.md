---
rg: 2
id: digit-shear-has-no-internal-maximal-conjugator
kind: claim
title: The digit-reading shear has no internal maximal-C-star conjugator
distinct_from:
  digit-reading-p-edge-corona-conjugator: that asks for an external unitary in a matrix corona after choosing a regular MF realization; this excludes only a unitary internal to the maximal group C-star algebra and therefore does not decide that open claim.
  digit-edge-mf-is-a-free-entropy-model-uniqueness-question: that concerns approximate equivalence of correlated matrix models; this is an exact Fourier obstruction in a fixed quotient of the universal group algebra.
---

Let `m>=3`, `s>=2`, and let `Gamma'` be the p-free digit-reading base from
`machine-free-digit-reading-base-is-regular-mf`. Write `u_g` for the
canonical unitary associated to `g` in `C*_max(Gamma')`. There is no unitary
`V` in `C*_max(Gamma')` satisfying

```text
V u_(a_i) V* = u_(a_i)   for every i,
V u_t V*     = u_(td).
```

In fact, after quotienting `x` and every `b_j` to the identity, the regular
representation of the quotient admits no nonzero bounded intertwiner between
`lambda(t)` and `lambda(td)` in the commutant of all the `lambda(a_i)`.

Thus any solution of `digit-reading-p-edge-corona-conjugator` must be
genuinely external to the represented base algebra, or must use a quotient
representation whose new commutant has no unitary lift to the maximal group
C-star algebra. An internal universal-algebra implementer cannot supply the
missing edge.
