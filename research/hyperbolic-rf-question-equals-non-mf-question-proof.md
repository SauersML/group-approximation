---
rg: 2
id: hyperbolic-rf-question-equals-non-mf-question-proof
kind: route
title: Chain Kapovich--Wise, a Kazhdan common quotient and Ozawa--Thom
target: hyperbolic-rf-question-equals-non-mf-question
requires:
  - kapovich-wise-rf-iff-finite-quotients
  - olshanskii-g-subgroup-quotient-theorem
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - mf-kazhdan-group-without-finite-quotients-is-trivial
  - mf-positive-controls
---

**(1) => (2).**  Contrapositive of `kapovich-wise-rf-iff-finite-quotients`:
some nontrivial hyperbolic group has no nontrivial finite quotient, and it is
infinite because a nontrivial finite group is its own finite quotient.

**(2) => (3).**  Let `G_0` be infinite, hyperbolic, with no nontrivial finite
quotient.

*a. Normalize.*  `G_0` is non-elementary: an infinite elementary group is
virtually infinite cyclic, hence residually finite, hence has a nontrivial
finite quotient.  Let `E_0` be its maximal finite normal subgroup (`E(G_0)` in
Olshanskii's notation) and put `G_1 = G_0/E_0`.  Then `G_1` is hyperbolic
(finite kernel), non-elementary, has no nontrivial finite quotient (it is a
quotient of `G_0`), and has no nontrivial finite normal subgroup: the preimage
of one would be a finite normal subgroup of `G_0` strictly containing `E_0`.

*b. The partner.*  By `torsion-free-hyperbolic-kazhdan-partner-exists` choose
`K` infinite, non-elementary, torsion-free, word-hyperbolic and Kazhdan.

*c. The free product.*  `H = G_1 * K` is word-hyperbolic: a free product is
hyperbolic relative to its factors, and a finitely generated group hyperbolic
relative to hyperbolic subgroups is hyperbolic (both quoted from Osin,
arXiv:math/0510195v3, pp. 2--3, in `residual-prime-torsion-via-free-factor`).
It is non-elementary.

*d. Trivial finite radicals.*  Every finite subgroup `F <= H` is conjugate into
a factor (Kurosh), and `K` is torsion-free, so `F <= uG_1u^(-1)` for some `u`.
A free factor is malnormal: `G_1 intersect wG_1w^(-1) = 1` for `w notin G_1`.

- If `F` is normalized by some `k in K \ {1}`, then
  `F <= u(G_1 intersect wG_1w^(-1))u^(-1)` with `w = u^(-1)ku`, whose image
  under the retraction `H -> K` is nontrivial, so `w notin G_1` and `F = 1`.
  Hence `E(K) = 1` and `E(H) = 1`.
- If `F` is normalized by `G_1`: when `u in G_1`, `F` is a finite normal
  subgroup of `G_1`, hence trivial by step a; when `u notin G_1`, pick
  `g in G_1 \ {1}`, so `w = u^(-1)gu` is a nontrivial element of `u^(-1)G_1u`,
  which meets `G_1` trivially, so `w notin G_1` and again `F = 1`.  Hence
  `E(G_1) = 1`.

*e. G-subgroups.*  With `E(H) = 1` the kernels `K(X)` of the conjugation actions
on `E(H)` are the whole subgroups, so both index conditions read `1 = 1`.  By
clause 1 of `olshanskii-g-subgroup-quotient-theorem`, the non-elementary
subgroups `G_1` and `K` are G-subgroups of `H`.

*f. The common quotient.*  Clause 2 gives an epimorphism `φ : H -> Q` onto a
non-elementary hyperbolic group with `φ(G_1) = φ(K) = Q`.  Then `Q` is
infinite and word-hyperbolic; it has property (T), being a quotient of `K`;
and it has no nontrivial finite quotient, being a quotient of `G_1`.

**(3) => (4).**  By `mf-kazhdan-group-without-finite-quotients-is-trivial`, an
infinite Kazhdan group without nontrivial finite quotients is not MF.

**(4) => (1).**  By `mf-positive-controls`, every countable residually finite
group is MF.  A hyperbolic group is finitely generated, hence countable, so a
non-MF hyperbolic group is not residually finite.  `QED`
