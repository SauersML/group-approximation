---
rg: 2
id: stw93-factor-section-splitting-proof
kind: route
title: Descend the canonical slice and compute its kernel after saturation
target: stw93-residual-extension-splits-over-factor
requires:
  - stw93-jiang-su-slice-exhausts-tracial-central-quotient
  - stw93-all-z-central-slices-generate-quasitrace-null-ideal
artifacts:
  - research/artifacts/stw93-residual-factor-section-audit-2026-08-30.md
---

Let `iota:G->D` be the canonical tensor-factor slice.  Compose it with the
quotient map `D->E` and call the resulting homomorphism `kappa:G->E`.
Because the canonical slice is one of the embeddings used to generate
`K_Z^sat`,

```text
iota(J) subset K_Z^sat.                                  (4)
```

Conversely `K_Z^sat subset I`, while
`iota(G) intersect I=iota(J)` by
`stw93-jiang-su-slice-exhausts-tracial-central-quotient`.  Therefore

```text
ker(kappa)=J.                                            (5)
```

Equation `(5)` induces an injective unital homomorphism `s:Q=G/J->E`.
The composite

```text
Q --s--> E -> E/R=D/I
```

is exactly the quotient isomorphism furnished by slice surjectivity.  After
identifying `Q` with `D/I`, it is the identity, proving `(2)`.

For `e in E`, subtract from `e` the section of its image in `E/R`; the
difference lies in `R`.  This proves `E=R+s(Q)`.  If `s(x) in R`, its image
in `E/R` is `x`, so `x=0`; hence the intersection is zero and the
decomposition is unique.  The bounded linear projection

```text
e -> s(e+R)
```

also shows that the decomposition is topologically complemented.

Finally, `Q` is a II_1 factor and has its unique normalized trace as a
C*-algebra.  The restriction of any normalized trace on `E` along the
unital section is therefore that canonical trace.
