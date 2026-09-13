---
rg: 2
id: kt-wreath-monomial-models-kill-fibre-even-lamps-proof
kind: route
title: Soften the fibre-even lamps through the sofic radical, find a Gamma-invariant one in a compressed fibre, and let Kun--Thom 4.1 fix it under EL_r(R)
target: kt-wreath-monomial-models-kill-fibre-even-lamps
requires:
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
  - normal-closure-fixes-gamma-fixed-algebra
  - kun-thom-nonsofic-wreath
  - diagonal-normalizer-rigidity
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md
---

Full proofs: `research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md`,
Lemma 1, Lemma 2, Theorem 3 and Corollary 4.  Outline:

1. **Item 1.**  The permutation part of a block-monomial model is a
   homomorphism into `S_omega`, by the Hamming comparison
   `d_H <= ||.||_2^2 / 2`.  Its image is sofic, so it kills
   `Rad_sof(W) = K_even` (`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`).
   For block size `1`, `||M - (c; id)||_2^2 = 2 d_H(sigma, id)` makes `rho(v)`
   diagonal for `v in K_even`.
2. **Item 2.**  `s(R_+) = F_q[y_1..y_d]` with `y_j = x^(s e_j)` divisible by
   `x_1`, so `s Gamma s^(-1) = EL_r(s(R_+)) <= Gamma`.  The stabilizer of
   `s^(-1) h Gamma` in `Gamma` is conjugate to `EL_r(s(R_+)) ∩ h Gamma h^(-1)`.
   This contains the congruence kernel of `I = (y_1^2..y_d^2)`, since
   `I <= x_1^2 R_+` makes `h^(-1)(1 + B)h` polynomial, and
   `SL_r(R_+) = EL_r(R_+)` by Suslin.  `s(R_+)/I` is finite, so the orbit is
   finite.  It avoids `s^(-1) Gamma` because `h notin Gamma`.  `N`-orbits on
   `G/Gamma` are infinite, so `P^N = 0`.
3. **Item 3.**  `b = rho(v)` is diagonal.  Conjugation by a monomial acts on
   diagonals by its permutation part exactly, so `b` is fixed by
   `psi(Gamma')`.  Tensor `psi|G` with a sofic representation `lambda` of the
   residually finite group `G`.  The result is a trace-zero homomorphism
   `G -> S_omega` fixing `b ⊗ 1` on `Gamma'`.  Part 2 of
   `normal-closure-fixes-gamma-fixed-algebra` makes every `n in N` fix
   `b ⊗ 1`.  So `rho(n.v) = rho(n) b rho(n)^* = b`.
4. **Corollaries.**  Regular models are injective.  The finitary masa form
   follows from clause 1 of `diagonal-normalizer-rigidity` and the diagonal
   argument.
