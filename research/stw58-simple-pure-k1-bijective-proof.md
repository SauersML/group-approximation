---
rg: 2
id: stw58-simple-pure-k1-bijective-proof
kind: route
title: Combine Lin's pure dichotomy with nonstable K1 theorems
target: stw58-simple-pure-k1-bijective
requires: []
artifacts:
  - research/artifacts/stw58-simple-pure-k1-bijectivity-audit-2026-08-30.md
---

Let `A` be unital, simple, and pure.  Lin's published Theorem 3.6 says that
`A` is either purely infinite or has stable rank one.

If `A` has stable rank one, Rieffel's Theorem 10.12 identifies the canonical
map

```text
U(A)/U_0(A) -> K_1(A)
```

as an isomorphism.

If `A` is purely infinite, then it is properly infinite.  Cuntz's nonstable
K-theory results give surjectivity for every unital properly infinite
C-star-algebra and injectivity for every unital simple purely infinite
C-star-algebra.  Hence the map is an isomorphism in this branch as well.

Sources:

- Huaxin Lin, *Strict comparison and stable rank one*, Journal of Functional
  Analysis 289 (2025), 111065, Theorem 3.6,
  https://doi.org/10.1016/j.jfa.2025.111065.
- Marc A. Rieffel, *Dimension and stable rank in the K-theory of
  C-star-algebras*, Proceedings of the London Mathematical Society 46 (1983),
  301--333, Theorem 10.12, https://doi.org/10.1112/plms/s3-46.2.301.
- Joachim Cuntz, *K-theory for certain C-star-algebras*, Annals of Mathematics
  113 (1981), 181--197, https://doi.org/10.2307/1971137.  The two nonstable
  consequences are also recorded in STW v2, footnote 113, with
  Rordam--Larsen--Laustsen, Exercises 4.6, 4.9, and 8.9 as explicit
  references.
