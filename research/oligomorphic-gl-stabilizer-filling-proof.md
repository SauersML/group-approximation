---
rg: 2
id: oligomorphic-gl-stabilizer-filling-proof
kind: route
title: Compare contextual linear transports with fixed sections at the base-vector stabilizer
target: oligomorphic-gl-has-unbounded-stabilizer-fillings
requires:
  - finitely-presented-oligomorphic-linear-pauli-addresser
  - bounded-centralizer-fillings-force-finite-stabilizer
  - two-transitive-occurrence-sections-have-unbounded-pair-holonomy
---

The finitary linear group is transitive on nonzero vectors and its
stabilizer of `e` contains the infinite finitary linear group of a
complement of `F_2 e`; hence `H` is infinite.  The semidirect action sends
`X_e` to `X_(he)=X_e`, so `H<=C(x)`.  Since `x` has order two, the uniform
centralizer-filling theorem applies and proves `(OGS3)`.

For a tuple prototype with endpoint word `u x u^(-1)`, contextual transport
by `g` gives `g u x u^(-1)g^(-1)`.  If its endpoint is `v`, then
`h=t_v^(-1)gu` fixes `e`, and

```text
guxu^(-1)g^(-1)=t_v h x h^(-1)t_v^(-1).
```

Its difference from the fixed name `t_vxt_v^(-1)` is the conjugate
`t_v[h,x]t_v^(-1)`.  Conjugation does not change diagram area, so `(OGS3)`
is exactly the failure of a uniform contextual-to-global proof.

The two-role holonomy theorem applies to the independent-vector orbit of
the finitary linear action, which is two-transitive in the needed ordered-
frame sense.  It prevents choosing separate `X` and `Z` sections that bound
both corrections.  Finally the amenable exact model from the addresser
theorem and the literal BLR--Weyl implication give the semantic
cross-check.
