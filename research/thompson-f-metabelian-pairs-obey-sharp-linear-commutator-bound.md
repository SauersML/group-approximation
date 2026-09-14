---
rg: 2
id: thompson-f-metabelian-pairs-obey-sharp-linear-commutator-bound
kind: claim
title: Permutation pairs generating a metabelian group satisfy d(AB,BA) ≤ 2 d(R_1,1) + d(R_2,1), and the bound is attained, so a Thompson F witness below ratio 1/3 must be non-metabelian
distinct_from:
  thompson-f-almost-kernels-force-linear-commutator-bounds: that gives uncomputed constants on pairs where one fixed nontrivial word nearly vanishes; this gives the sharp constants 2 and 1 on the whole class of metabelian pairs, through an explicit free-group identity modulo the second derived subgroup.
  thompson-f-sofic-iff-defect-to-separation-ratio-vanishes: that reduces soficity to a vanishing ratio over all pairs; this shows the ratio is at least 1/3 on metabelian pairs and that the exact small-n minima on main are attained there.
artifacts:
  - research/artifacts/hl-f-skew-product-rate-2026-09-14.md
---

**ESTABLISHED (unreviewed).** **Setting.** As in
`thompson-f-sofic-iff-defect-to-separation-ratio-vanishes`: `F = <a, b | R_1, R_2>` with
`R_1 = bAABaaBAba` and `R_2 = bAAABaaaBAAbaa` (capitals are inverses; a word is a product and acts
last letter first), `c = abAB`, and `d` is the normalized Hamming distance on `Sym(n)`. For a pair
`(A, B)` write `t = d(AB, BA) = d(c(A,B), 1)`, `D_j = d(R_j(A,B), 1)`, `D = max_j D_j` and
`D_+ = D_1 + D_2`.

**Statement.**
1. **Metabelian bound.** If the group `<A, B>` is metabelian, then

   `d(AB, BA) ≤ 2 d(R_1(A,B), 1) + d(R_2(A,B), 1)`.

   So `D/t ≥ 1/3` and `D_+/t ≥ 1/2` whenever `t > 0`.
2. **Explicit identity.** In the free group on `a, b`,

   `c = u_2 · (a^2 R_1 a^-2)(a R_1 a^-1)(a^2 R_2 a^-2)^-1`, with
   `u_2 = abABaabAAABaaaBAbAAbaaBBabAAbaaBAA` (freely reduced, length 34),

   and `u_2` lies in the second derived subgroup `F_2''`. So every pair satisfies
   `d(AB, BA) ≤ 2 D_1 + D_2 + d(u_2(A,B), 1)`.
3. **Sharpness.** Equality holds in item 1 for the following certificates. They were recounted by
   two independent scripts, and the group orders and structures come from GAP.

   | certificate | n | m_1 | m_2 | m_c | group |
   |---|---|---|---|---|---|
   | `cert.x12` (main, job 780822) | 12 | 3 | 3 | 9 | `C3^4 : C8`, order 648 |
   | `cert.s10` (main, job 780822) | 10 | 4 | 0 | 8 | `C2^4 : C5`, order 80 |
   | torus skew product, fibre `Z/2` | 18 | 4 | 4 | 12 | abelian-by-abelian |
   | `Z/2 wr Z/5`, imprimitive | 10 | 4 | 0 | 8 | abelian-by-abelian |

   So `1/3` (max form) and `1/2` (sum form) are attained on metabelian pairs.
4. **Minimality of the identity.** Any expression of `c` modulo `F_2''` as a product of conjugates
   of `R_1^±1` and `R_2^±1` has at least three factors.

**Consequences.**
- **The small-n minima are the metabelian barrier.** The exact minima over all of `Sym(n)` on main,
  `1/3` in max form at `n = 12` and `1/2` in sum form from `n = 10` on, are attained by metabelian
  groups and coincide with item 1.
- **Going below 1/3 needs a non-metabelian group.** Both certificates on main below `1/3` are
  non-metabelian, and `u_2` does the work in each:
  - the `4/13` pair on 16 points generates a non-solvable group of order 38880 with an `A5` factor,
    and `u_2` moves 11 of its 16 points;
  - the `4/21` pair on 27 points (`hl-f-skew-product-rate`, a skew product with fibre `Sym(3)` over the
    commuting `Z/3 × Z/3`, so of derived length at most 3) has `2 m_1 + m_2 = 12 < 21 = m_c`, and `u_2`
    moves 24 of its 27 points.
- **Metabelian models are no witnesses.** Affine maps `x ↦ αx + β`, lamplighter actions
  `Z/k wr Z/m`, and skew products with abelian fibres over commuting bases never go below `1/3`.
- **Witnesses load an explicit second-derived word.** A family with `D_k/t_k → 0` has
  `d(u_2(A_k,B_k), 1) ≥ t_k (1 - 3 D_k/t_k)`, so the separation is carried by the 34-letter word
  `u_2 ∈ F_2''`. This is `thompson-f-almost-kernels-force-linear-commutator-bounds` for `w = u_2` with
  the computed constants `N = 3`, `M = 1`.

**Scope.** Elementary and import-free: Fox calculus on the grid Cayley graph of `Z^2`, checked by exact
computation. No novelty is claimed for the method. It decides nothing about `thompson-f-is-sofic` or
`thompson-f-relator-system-stable-in-permutations`.

Proof route: `thompson-f-metabelian-commutator-bound-proof`.
