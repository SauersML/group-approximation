---
rg: 2
id: z-fixed-support-five-hecke-normal-form
kind: claim
title: Every five-term C3-fixed factor is normalizer-supported or one Hecke rectangle
distinct_from:
  z-fixed-support-three-elements-cannot-witness: that completely excludes the three-term case; this classifies rather than excludes the first surviving five-term case.
  leavitt-corner-witness-has-unitized-rank-floor: that gives numerical support floors with no support geometry; this gives the exact left-right coset geometry at rank five.
  finite-subgroup-hecke-literals-cannot-block-escape: that says a nonzero literal compression `qgq` by a finite-subgroup projection forces `g` into the finite subgroup; this classifies sums fixing the C3 averaging projection and permits a four-term double-coset rectangle outside the subgroup.
artifacts:
  - research/artifacts/leavitt-corner-small-rank-coset-classification-2026-08-21.md
---

Let `H=<g>` have order three, `z=sum_H[h]`, and let `alpha in F_2[G]` have
support five with `alpha z=z alpha=z`.  Then exactly one of the following
holds:

1. the support is contained in the normalizer `N_G(H)`; or
2. for some `h_0 in H`, nonidentity `r,s in H`, and `x notin N_G(H)`,

```text
alpha=[h_0]+(1+[r])[x](1+[s]),
```

whose four expanded terms form one left-right `H`-double-coset rectangle.

Thus a minimal `(5,7)` Leavitt corner witness must begin either inside the
normalizer of the constant `C_3`, or with one explicit four-corner Hecke
rectangle.  There is no third five-term support geometry.
