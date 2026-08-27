---
rg: 2
id: hyperlinear-to-mf-saturation-compiler-proof
kind: route
title: Pull hyperlinear shadows back through the router, then detect the Kazhdan image
target: hyperlinear-to-mf-saturation-compiler
requires: [hyperlinear-killed-normal-kazhdan-mf-transfer]
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

## Proof

Let `B` be an operator-norm almost representation of `Q`.  Then `B.comap q`
is one of `E`.  If `y in q(D)`, choose `d in D` with `q(d)=y`; functoriality
of the ultraproduct homomorphism gives

```text
B_HS(y) = (B.comap q)_HS(d) = 1.
```

Thus `q(D)` satisfies the same quantified kill hypothesis in `Q`.  Apply
`hyperlinear-killed-normal-kazhdan-mf-transfer` to any normal Kazhdan
`K <= q(D)`.  This proves the partial-saturation statement and its
`normalKazhdanPart` form.

If `q(D)=Q` and `Q` has property `(T)`, use `K=Q`.  The resulting inclusion
`top <= normMFResidual Q` is equality.  If `r:Q->>L`, every corona
representation of `L` pulls back to a trivial one of `Q`; surjectivity makes
the original representation trivial.  This quotient step is kernel-checked
as `coronaMFResidual_eq_top_of_surjective` and, on routed data, as
`quotient_normMFResidual_eq_top`.

Finally, for `f:Q->M` with `M` operator MF, the image is a quotient of `Q`
and an MF subgroup of `M`.  Full residual and MF can coexist only for the
trivial group, so `f=1`; the routed interface proves the endpoint as
`DefectRoutingData.hom_eq_one_to_isOperatorMF`.
