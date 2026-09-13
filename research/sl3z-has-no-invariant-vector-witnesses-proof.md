---
rg: 2
id: sl3z-has-no-invariant-vector-witnesses-proof
kind: route
title: Sort nonamenable subgroups by Zariski closure and tensor one escaping representation per subgroup at distinct primes
target: sl3z-has-no-invariant-vector-witnesses
requires: []
artifacts:
  - research/artifacts/sl3z-invariant-vector-witnesses-2026-09-12.md
---

Full derivation: Sections 1--3 of the artifact.  Outline.

1. Replace each `H_j` by a nonabelian free subgroup `F_j` (Tits alternative);
   fixed vectors of `H_j` are fixed by `F_j`.
2. The Zariski closure of `F_j` over `Q` contains a simple subgroup of one of
   three types.  (a) `SL_3`: strong approximation for finitely generated
   Zariski-dense subgroups makes `F_j mod p = SL_3(F_p)` for almost all `p`.
   (b) Reducible `A_1`: conjugate over `Q` into the Levi of a parabolic; mod
   almost every `p` the image contains a conjugate of the block `SL_2(F_p)`
   (a complement is conjugate to it since `H^1(SL_2(F_p), F_p^2) = 0`), so the
   conjugated Deligne representations of MdlS Example 2.2 have no fixed vector.
   (c) Irreducible `A_1 = SO_Q`: mod almost every `p` the image contains
   `Omega_Q(F_p) = PSL_2(F_p)`.  For every prime `p >= 5` the degenerate
   principal series `Ind_(P_1)^(SL_3(F_p))(eta o (scalar on L))` with `eta` odd
   and `eta != sgn` has no fixed vector (artifact Lemma 2'): on the conic,
   exterior and interior points of `P^2(F_p)` the stabilizers act on the line
   by all squares, by `-1`, and by `-1`.  Lemma 2 gives a second family,
   `Ind_P(mu (x) sigma_theta)` with `theta` quadratic on `mu_(p+1)`, when
   `p == 1 mod 4`.
3. Choose distinct large primes `p_j`, one escaping representation `pi_j` of
   `SL_3(F_(p_j))` for each `F_j`, and put `pi = (x)_j pi_j`.  The perfect core
   of the image of `F_j` in `prod_i SL_3(F_(p_i))` is a subdirect product of
   perfect groups with pairwise distinct simple quotients (`PSL_2(F_p)`,
   `PSL_3(F_p)`), hence the full product (Goursat), so
   `pi^(F_j) <= (x)_i pi_i^(N_i) = 0`.

Census check (artifact Section 5, exact computation on MSI): at `p = 5` the
principal `SL_2` misses two degree-124 representations (Lemma 2) and two
degree-31 ones (Lemma 2'); at `p = 7` two degree-57 ones (Lemma 2') and four
degree-96 components that also miss the block; at level 9 four degree-144
representations miss both.

Trust surface: strong approximation (Matthews--Vaserstein--Weisfeiler, Nori,
Weisfeiler), the character values of cuspidal representations of `GL_2(F_q)`,
and MdlS Example 2.2 are imported.
