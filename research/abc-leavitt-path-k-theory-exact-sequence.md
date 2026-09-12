---
rg: 2
id: abc-leavitt-path-k-theory-exact-sequence
kind: claim
title: Leavitt path algebras over regular supercoherent coefficients have the 1 - N^t long exact sequence in K-theory
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports the vanishing of all K-groups of L_2 and of L_2 tensor a regular supercoherent ring; this imports the general long exact sequence for L_k(E) over any row-finite quiver, from which the K-groups of every graph algebra are computed.
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

**Established by citation.** Ara--Brustenga--Cortiñas, *K-theory of Leavitt
path algebras*, Münster J. Math. 2 (2009), arXiv:0903.0056v2. Read 2026-09-12
from the text on MSI (`/projects/standard/hsiehph/sauer354/lit-groups/abc-clean.txt`).

> Theorem 7.6. Let k be a regular supercoherent ring and let E be a row-finite
> quiver. Then K(L_k(E)) = hocofiber(K(k)^(E^0 \ Sink(E)) --(1 - N_E^t)-->
> K(k)^(E^0)). It follows that there is a long exact sequence
> K_n(k)^(E^0 \ Sink(E)) --(1 - N_E^t)--> K_n(k)^(E^0) -> K_n(L_k(E)) ->
> K_(n-1)(k)^(E^0 \ Sink(E)) -> ...

Here `N_E = (n_ij)`, `n_ij = #{arrows from i to j}`, and `N_E^t` and `1` have the
columns of sinks removed. The introduction states: "this holds if R is a field,
since fields are regular supercoherent".

Corollary 7.7 of the same paper, for a principal ideal domain `k`:
`K_0(L_k(E)) = coker(1 - N^t)` on integer vectors, and
`K_1(L_k(E)) = coker(1 - N^t | K_1(k)) ⊕ ker(1 - N^t | Z)`.

**Convention caution.** ABC discuss two incidence conventions (Section 4). For
finite graphs with no sinks and no sources the matrix is square, and the two
conventions differ by a transpose. Consumers should state results through
`det(1 - N^t)` and Smith invariants, which do not see the transpose.

DERIVATION
abc-leavitt-path-k-theory-citation
