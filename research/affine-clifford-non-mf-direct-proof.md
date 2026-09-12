---
rg: 2
id: affine-clifford-non-mf-direct-proof
kind: route
title: Transport the explicit affine spectral projection in the finite adjoint matrix corona
target: affine-clifford-non-mf-from-rational-certificate
requires:
  - affine-seven-generator-distance-estimate
artifacts:
  - research/artifacts/affine-clifford-direct-non-mf-proof-2026-09-08.md
  - research/artifacts/affine-seven-generator-distance-estimate-2026-09-08.md
  - research/artifacts/p13-rational-certificate-audit-2026-09-08.md
  - research/artifacts/affine-hodge-integer-check-2026-09-08.json
---

The main artifact supplies the complete proof in six steps.

1. Construct the signed-monomial Clifford algebra explicitly. The two cosets
   `tB` and `atB` are different because `t^(-1)at` is translation by `e_1/2`.
   Their lamps anticommute, giving the nontrivial central sign and nine
   generators.
2. Use the required explicit all-representations distance estimate, with
   `C=2+5 sqrt(3000)`, to obtain a zero spectral projection for the affine
   seven-generator Laplacian inside any represented unital C-star algebra.
3. Prove finiteness of norm matrix coronas by polar decomposition of square
   matrices. Unitarily conjugate projections cannot be properly ordered.
4. If the sign survives, pass first to its nonzero negative corner and lift
   to square matrix unitaries on its positive ranks. The sign is now `-I`.
5. Conjugation of these unitaries defines an exact homomorphism into the
   corona on their normalized Hilbert-Schmidt spaces. The relation
   `tBt^(-1)<=B` implies `T*PT<=P`; finiteness gives equality. Apply this
   projection to the normed quotient of bounded Hilbert-Schmidt vector
   sequences to show the transported lamp asymptotically commutes with `a`.
6. Its commutator with its `a`-conjugate must tend to `I` in normalized
   Hilbert-Schmidt norm, while the marked group identity makes it tend to
   `-I` in operator norm. The distance between those two scalar matrices is
   exactly two, a contradiction.

The quotient vector space in step 5 is not assumed Hilbert. The identity
`1-P=h(L)L` in continuous functional calculus justifies its use there.
All universal quantifiers needed for the faithful C-star representation
are supplied by the required claim. No existing non-MF conclusion or
qualitative group rigidity theorem is an input to this route.
