---
rg: 2
id: regular-coherent-coefficients-leavitt-k-theory-citation
kind: route
title: Specialize the Leavitt path sequence to one vertex with two loops under regular coherent coefficients
target: regular-coherent-coefficients-kill-leavitt-tensor-k-theory
requires: []
---

**Source.** P. Ara, M. Brustenga, G. Cortiñas, *K-theory of Leavitt path
algebras*, arXiv:0903.0056v2, read from the PDF text on MSI on 2026-09-12.
- Section 1: "the Leavitt algebra L_R(E) = L_Z(E) ⊗ R".
- Section 7: "We say that R is regular coherent if it is coherent and in addition
  any finitely presented module has finite projective dimension."
- Theorem 7.6: "Let k be a regular supercoherent ring and let E be a row-finite
  quiver. Then K(L_k(E)) ≅ hocofiber(K(k)^(E^0 \ Sink(E)) --(1 − N_E^t)-->
  K(k)^(E^0)). It follows that there is a long exact sequence
  K_n(k)^(E^0 \ Sink(E)) -> K_n(k)^(E^0) -> K_n(L_k(E)) -> K_(n−1)(k)^(E^0 \ Sink(E))."
- Remark 7.8: "If we only assume that k is regular coherent in Theorem 7.6, then
  the long exact sequence in the statement terminates at K_0(L_k(E))."

**Derivation.** Let `E` be the quiver with one vertex and two loops, so
`L_R(E) = R ⊗ L_Z(1,2)`, `E` has no sinks, and `N_E = (2)`. The map `1 − N_E^t`
is multiplication by `−1`, an isomorphism on every `K_n(R)`.
- By Remark 7.8, for regular coherent `R` the sequence
  `K_n(R) --(−1)--> K_n(R) -> K_n(L_R(E)) -> K_(n−1)(R) --(−1)--> K_(n−1)(R)`
  is exact at `K_n(L_R(E))` for every `n >= 1`.
- The image of `K_n(R)` in `K_n(L_R(E))` is the cokernel of `−1`, which is zero.
- So `K_n(L_R(E))` injects into `K_(n−1)(R)`, with image the kernel of `−1`,
  which is zero.

Hence `K_n(R ⊗ L_Z(1,2)) = 0` for `n >= 1`.
