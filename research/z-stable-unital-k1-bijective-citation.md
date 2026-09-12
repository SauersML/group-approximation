---
rg: 2
id: z-stable-unital-k1-bijective-citation
kind: route
title: Import Jiang's nonstable K-theory of Z-stable algebras at degree zero
target: z-stable-unital-algebras-are-k1-bijective
requires: []
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

**Established by citation.** Xinhui Jiang,
[*Nonstable K-theory for Z-stable C*-algebras*](https://arxiv.org/abs/math/9707228),
preprint FI-OA1997-001, Fields Institute. The abstract states that for
Z-stable algebras the homotopy groups of the unitary group are stable
invariants, `pi_i(U(A)) = K_(i-1)(A)`. Theorem 2.8, already used by
`stw99-lxxvi-z-stable-unitary-kernel-proof`, says that every canonical
matrix-stabilization map between the unitary groups of matrix algebras over
a Z-stable algebra induces isomorphisms on all homotopy groups.

Take `i = 0` and pass from `U(A)` to `U(M_infinity(A))`: the stabilization
map `pi_0 U(A) -> pi_0 U(M_infinity(A)) = K_1(A)` is an isomorphism. That is
the target claim.
