---
rg: 2
id: fg-simple-weak-sofic-linear-sofic-via-nst-conjugacy
kind: route
title: The proof of NST Theorem 4 lands a simple weakly sofic group in a projective-rank ultraproduct of PSL_n(q), and the adjoint makes it linear sofic
target: fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic
requires: [nst-weakly-sofic-perfect-groups-psl-conjugacy-models, projective-rank-psl-ultraproducts-embed-by-adjoint]
artifacts: [research/artifacts/fg-simple-weak-soficity-finite-field-linear-2026-09-13.md]
---

Section 2 of the artifact. `G` is finitely generated, simple and weakly sofic.

1. **Finite `G`.** The regular representation over `F_2` gives normalized rank `>= 1/2` on nontrivial elements, so `G` is
   linear sofic over finite fields. From now on `G` is infinite, so nonabelian and perfect.
2. **Projective-rank ultraproduct.** By `nst-weakly-sofic-perfect-groups-psl-conjugacy-models`, `G` has a nontrivial
   homomorphism into `prod_U (PSL_(n_i)(q_i), l^pr)`. It is injective, because `G` is simple.
3. **Adjoint.** By item 3 of `projective-rank-psl-ultraproducts-embed-by-adjoint`, `G` is linear sofic over finite fields.

The route inherits the source status of the NST import, where the authors sketch the last step of their proof. Route
`fg-simple-weak-sofic-linear-sofic-via-near-scalar-covering` proves the same target from the statement of Theorem 4 only.
