---
rg: 2
id: fg-metabelian-coprimary-quotients-proof
kind: route
title: Take a primary decomposition of the derived subgroup as a module over the abelianization, and cite Remeslennikov and Wehrfritz for linearity of the pieces
target: fg-metabelian-groups-embed-in-products-of-coprimary-quotients
requires: []
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

Let `A = G'` and `Q = G/A`.

**(a) Primary decomposition.**
1. *A is a Noetherian module.* `A` is abelian and normal, so conjugation makes it
   a module over the commutative Noetherian ring `ZQ`. By P. Hall, *Finiteness
   conditions for soluble groups* (1954), it is finitely generated, hence
   Noetherian.
2. *Decompose.* By the Lasker--Noether theorem for finitely generated modules over
   Noetherian rings, `0 = M_1 ∩ ... ∩ M_r` with each `A/M_i` coprimary, with a
   single associated prime `P_i`. Then:
   - the zero divisors of `ZQ` on `A/M_i` are exactly the elements of `P_i`;
   - `P_i` is the radical of the annihilator of `A/M_i`, so every element of `P_i`
     is nilpotent on `A/M_i`.
3. *Normality.* Each `M_i` is a `ZQ`-submodule of `A`, so it is normal in `G`, and
   `(G/M_i)' = A/M_i`.
4. *Characteristic of each piece.* `P_i ∩ Z` is a prime ideal of `Z`.
   - If it is `pZ`, then `p` is nilpotent on `A/M_i`, so `p^k (A/M_i) = 0` for some `k`.
   - If it is `0`, no nonzero integer lies in `P_i`, so none is a zero divisor on
     `A/M_i`, and the module is torsion-free.
5. *Embedding.* `g -> (g M_i)_i` is injective because `∩ M_i = 1`.

**(b) Linearity (citation).** B. A. F. Wehrfritz, *Faithful representations of
finitely generated metabelian groups*, Canad. J. Math. 27 (6) (1975), 1355--1360,
doi:10.4153/CJM-1975-138-0. On 2026-09-12 the PDF was downloaded from Cambridge
Core on MSI (`/scratch.global/sauer354/bhmeta/wehrfritz1975.pdf`) and read page by
page. Verbatim:

- **§1, opening sentence:** "In [3] Remeslennikov proves that a finitely generated
  metabelian group G has a faithful representation of finite degree over some
  field F of characteristic zero (respectively, p > 0) if its derived group G' is
  torsion-free (respectively, of exponent p)." Here [3] is V. N. Remeslennikov,
  *Representations of finitely generated metabelian groups by matrices*, Alg. i
  Logika 8 (1969), 72--75. That primary source was not read.
- **Theorem 1.1:** "If the group G is a finite extension of a finitely generated
  metabelian group G_0 whose derived group G_0' is a p-group for some prime p,
  then G has a faithful representation of finite degree over some field of
  characteristic p."
- **The characteristic of a metabelian group:** "the set of prime divisors of the
  orders of the elements of G' of finite order, together with zero if G' is not a
  torsion group."
- **Corollary 1.2:** "If the group G is a finite extension, of a finitely generated
  metabelian group of characteristic π, then G is isomorphic to a quasi-linear
  group of characteristic π."

A quasi-linear group is, in Wehrfritz's definition, a group of matrices over a
direct sum of finitely many fields. Its characteristic is the set of
characteristics of those fields. His proof of Theorem 1.1 (§3.2) also starts from
a primary decomposition of the derived module.

So a piece with torsion-free derived subgroup is linear in characteristic zero,
and a piece whose derived subgroup has exponent `p^k` is linear in
characteristic `p`.

**Merging.** Suppose `G_j <= GL_(n_j)(F_j)` for finitely many `j`, where every
`F_j` has characteristic `c` and is finitely generated.
- Embed every `F_j` in one algebraically closed field `Ω` of characteristic `c`
  whose transcendence degree is at least that of each `F_j`.
- Block-diagonal sums embed `∏ G_j` in `GL_N(Ω)`.
- A finitely generated subgroup has entries in a finitely generated subfield of
  `Ω`. ∎
