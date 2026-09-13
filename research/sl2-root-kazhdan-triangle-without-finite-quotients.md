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
- **Two-dimensional representations force semilinear gluings** (sketch, not written as a proof).
  - Let `ρ: Λ -> SL_2(K)` be vertex-injective, with `char K = 2`. Each `ρ|_{A_i}` should be conjugate to a
    Frobenius twist of the natural representation (Steinberg's tensor product theorem, not re-read).
  - A conjugation carrying one root subgroup `u(k)`-type onto another rescales parameters by a scalar.
  - So every relative gluing on an edge would lie in `ΓL_1(F_q) = F_q^* ⋊ Gal(F_q/F_2)`, of order
    `f(q-1)`.
  - This is small inside `GL_f(F_2)`: 21 versus 168 for `q = 8`, and 60 versus 20160 for `q = 16`. A twist
    outside `ΓL_1` on some edge would admit no vertex-injective 2-dimensional representation in
    characteristic 2.
  - In characteristic `≠ 2`, the torus argument of Step 1 of
    `sl2-subfield-root-links-codistance-large-q-proof` shows every nontrivial representation of `SL_2(q)`
    has dimension `>= q - 1`.
  - Calibration still needed: confirm by computation that a non-semilinear twist for `q = 8` has no map
    into `SL_2(64)`.
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
