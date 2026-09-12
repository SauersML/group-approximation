---
rg: 2
id: commutator-compressor-carries-no-wall-proof
kind: route
title: Cancel the growth index across a Steinberg factorization
target: commutator-compressor-carries-no-wall
requires: [compressor-growth-index-homomorphism, relative-wall-commutant-growth]
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Submultiplicativity gives `lambda(ab)<=lambda(a)lambda(b)<infinity`, so the
two-factor form is multiplicative.  The same element equals `s b a`, whose
growth index is therefore also finite, so the three-factor form is
multiplicative too.  Equating and cancelling the finite nonzero factor
`lambda(a)lambda(b)` leaves `lambda(s)=1`, and the wall normal form excludes
a wall at `s`.  For the Kun--Thom Theorem E pair, `ell in SL_d(Z)` compresses
`EL_r(F_q[x_1..x_d])` exactly when `ell(N^d)<=N^d`, i.e. when `ell` is
nonnegative, so every positive elementary transvection is a compressor and
the Steinberg identity is a relation inside `P_Gamma`; strictness follows
because `I-e_(ij)` sends the exponent `e_j` to `e_j-e_i` and matrix entries
of `EL_r(R_+)` lie in `R_+`.  The same description of the external
projection of `P_Gamma` is proved for the repository's monomial-cone framing
in `notes/FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`.  Complete argument in
the cited note, Theorem 6 and Corollary 7.
