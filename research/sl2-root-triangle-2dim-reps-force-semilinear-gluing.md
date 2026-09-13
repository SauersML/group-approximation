---
rg: 2
id: sl2-root-triangle-2dim-reps-force-semilinear-gluing
kind: claim
title: A Kazhdan SL_2 root triangle with a non-semilinear gluing twist has no nontrivial two-dimensional linear representation over any field
distinct_from:
  sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2: that exhibits the untwisted member with a vertex-injective map onto SL_2(q^2); this proves that every member admitting a nontrivial 2-dimensional representation has all gluing twists semilinear
---

**Setting.** Take the data of `kazhdan-hyperbolic-sl2-root-triangles`, `q = 2^f >= 8`. The standard
parametrizations of the edge groups `E_e ≅ (k, +)` inside the vertex groups are:
- `A_1`: `u(x)` for `E_12` and `v(x)` for `E_13`;
- `A_2`: `u(x)` for `E_12` and `v(x)` for `E_23`;
- `A_3`: `u(x)` for `E_13` and `v(sx)` for `E_23`.

A gluing precomposes each of these with an automorphism `α_i^e ∈ GL(k, +) = GL_f(F_2)`. The
**relative twist** of edge `e = (i, j)` is `φ_e = α_j^e (α_i^e)^{-1}`. A twist is **semilinear** if it
lies in `ΓL_1(F_q) = { x ↦ λ x^{2^a} : λ ∈ k^*, 0 <= a < f }`.

**ESTABLISHED (unreviewed).** If a homomorphism `ρ: Λ -> GL_2(K)`, for any field `K`, is nontrivial,
then:
- `ρ` is injective on all three vertex groups;
- `char K = 2`;
- all three relative twists are semilinear.

Equivalently, a member with a non-semilinear relative twist has only the trivial 2-dimensional
representation.

**Size of the exceptional set.** `|ΓL_1(F_q)| = f(q-1)`. That is `21` against `|GL_3(F_2)| = 168` for
`q = 8`, and `60` against `|GL_4(F_2)| = 20160` for `q = 16`.

**Calibration (a real object must pass).** The untwisted member has all twists the identity, which is
semilinear, and it does map onto `SL_2(q^2)`
(`sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2`).

**What it does not say.**
- It does not say that semilinear gluings always have 2-dimensional representations.
- It says nothing about representations of dimension `>= 3`. In characteristic 2 there are twisted
  tensor products of dimension `2^j`; in other characteristics the minimal degree is `q - 1`.

Proof: `sl2-root-triangle-2dim-reps-force-semilinear-gluing-proof`.
