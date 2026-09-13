---
rg: 2
id: sl2-root-kazhdan-triangle-without-finite-quotients
kind: claim
title: Some Kazhdan SL_2 root triangle (SL_2(q), SL_2(q), SL_2(q^2)) with a twisted gluing has no nontrivial finite quotient
distinct_from:
  kazhdan-hyperbolic-group-without-finite-quotients: that asks for any hyperbolic Kazhdan group without finite quotients; this asks it of one explicit family of triangles of finite simple groups, where one quotient decides virtual torsion-freeness
  a7a7a8-triangle-candidate-without-finite-quotients: that concerns four explicit (A_7, A_7, A_8) triangles with Z/7 edges and no property (T); this concerns the Kazhdan SL_2 root triangles with (Z/2)^f edges
---

Let `Λ` range over the colimits of `kazhdan-hyperbolic-sl2-root-triangles`, for:
- `q = 2^f >= 8`;
- `s ∈ F_{q^2} \ F_q`;
- gluing automorphisms of the edge groups `(Z/2)^f`.

Claim: some such `Λ` has no nontrivial finite quotient. Such a `Λ` is an infinite hyperbolic Kazhdan
group that is not virtually torsion-free (`simple-vertex-groups-vtf-iff-some-finite-quotient`).

**OPEN.**

## Attempts

- **The natural member has a quotient** (established): `sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2`.
  - With identity gluings, conjugating the `SL_2(q)` vertices by `h = [[P,1],[1,0]]` and `h u(1/P)`,
    where `P^2 = 1/s`, gives a vertex-injective map onto `SL_2(q^2)`.
  - A scalar twist `x ↦ λx` on `E_23` is absorbed by changing `P`.
  - So candidates must use gluings that are not absorbed by such configurations.
- **Two-dimensional representations force semilinear gluings** (established:
  `sl2-root-triangle-2dim-reps-force-semilinear-gluing`).
  - A member with a nontrivial `ρ: Λ -> GL_2(K)` has `char K = 2`, `ρ` vertex-injective, and every relative
    gluing twist in `ΓL_1(F_q) = F_q^* ⋊ Gal(F_q/F_2)`.
  - The proof is elementary: fixed lines of root groups, then Hua's identity makes the root
    parametrization a field embedding.
  - `ΓL_1` is small in `GL_f(F_2)`: 21 of 168 for `q = 8`, and 60 of 20160 for `q = 16`. So the members
    with a non-semilinear twist, the generic ones, have no linear representation of dimension 2.
  - In characteristic `≠ 2` the minimal degree of `SL_2(q)` is at least `q - 1`. In characteristic 2 the
    next targets are the twisted tensor products of dimension `2^j`.
- **Counting heuristic (not a proof).** Here `χ_orb = 2/|SL_2(q)| + 1/|SL_2(q^2)| - 3/q + 1`, which is
  `≈ 0.63` for `q = 8` and `≈ 0.81` for `q = 16`. That predicts few epimorphisms onto large simple groups.
  - The natural member shows that structure beats the count.
  - By `convergent-quotient-count-decides-gromov-question`, making the count rigorous would decide
    Gromov's question anyway.
- **Why this family.** Unlike the amalgamated cores of `simple-vertex-triangles-are-universal-for-triangle-vtf`,
  these members keep property (T). So they are not cubulable, and the goodness mechanism that kills
  persistent classes (`hyperbolic-triangle-colimit-with-persistent-edge-twist`, Attempts) does not apply.
  The natural member `Λ_0` supplies a torsion-free first level `N = ker(Λ_0 -> SL_2(q^2))` for the
  edge-twist moment test with `p = 2`.
- **Where it dies.** Excluding every finite quotient of a non-semilinear member is the large-quotient
  barrier of `hyperbolic-simple-triangle-group-without-finite-quotients`. Vertex-injective quotients must
  contain `SL_2(q^2)`, so bounded searches start at order `|SL_2(64)| = 262,080`.
