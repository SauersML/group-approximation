---
rg: 2
id: rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup-proof
kind: route
title: Push a Kazhdan subgroup through the symbol map into a rank-two linear group over a field, where it is finite, and note the symbol kernel is locally finite
target: rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup
requires: []
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

## Why sufficient

**Finiteness of Kazhdan subgroups.**  Let `L <= GL_2(A_m)` have
property (T).  The symbol map `A_m -> S = Z[z,z^-1]` induces
`GL_2(A_m) -> GL_2(S) <= GL_2(Q(z))`.  The image of `L` is countable,
Kazhdan (a quotient of `L`), and has the Haagerup property by
Guentner--Higson--Weinberger, Theorem 4 of Section 5; a group with both
properties is finite (a proper affine isometric action has no fixed
point unless the group is finite, while property (T) forces one).  The
symbol kernel consists of matrices congruent to the identity modulo
`I_m = M_fin(N_0, Z/m)`, so its finitely generated subgroups sit in
some `GL_N(Z/m)` and it is locally finite.  Thus `L cap ker` is locally
finite and of finite index in `L`; `L` is finitely generated (Kazhdan),
so `L cap ker` is finitely generated and locally finite, hence finite,
and `L` is finite.  For `J_k`, replace `Q(z)` by `k(z)` and `Z/m` by
`k`; the symbol kernel is again locally finite.

**Trivial defects.**  Let `L <= Delta` be finite and `u in Delta` with
`u L u^-1 <= L`.  Equal finite cardinalities give `u L u^-1 = L`, so `u`
normalizes `L` and `u C_Delta(L) u^-1 = C_Delta(u L u^-1) = C_Delta(L)`.
Hence for `c in C_Delta(L)` and `l in L`, `[u c u^-1, l] = 1`, and the
normal closure of these commutators is trivial: `D_Delta(L) = 1`.

**Homomorphic encodings.**  For `f : P -> GL_2(A_m)` (or `GL_2(J_k)`)
and Kazhdan `L_0 <= P`, `f(D_P(L_0)) <= D_(f(P))(f(L_0))`, and `f(L_0)`
is Kazhdan hence finite, so the right side is trivial by the previous
paragraph.
