---
rg: 2
id: standard-identity-witnesses-force-block-displacement-proof
kind: route
title: Conjugates inherit small displacement, block-diagonals satisfy S_2k, regular traces make the alternating sum large; then amplify by tensor powers
target: standard-identity-witnesses-force-block-displacement
requires:
  - coarse-frame-normalizers-are-near-block-monomial
artifacts:
  - research/artifacts/ex-q34-imprimitivity-witness-2026-09-12.md
---

Complete proof in the artifact, sections 2 to 4.

1. The exact identity `||(u; sigma) - (u; id)||_2^2 = 2 d_H(sigma, id)` and the
   bound `d_H(sigma, sigma') <= ||M - M'||_2^2/2` for block-monomials.
2. `U_(g_i)` is within `4 delta` of `U_(h_i) U_g U_(h_i)^*`, so its displacement is
   `<= eta + 8 delta^2` and its block-diagonal part `D_i` is within
   `rho = sqrt(2 eta + 16 delta^2)`.
3. `S_(2k)(D_1..D_(2k)) = 0`, and telescoping gives
   `||sum_pi sgn(pi) U_(w_pi)||_2 <= (2k)! 2k (rho + delta)`.
4. Expanding the square, the diagonal terms give `(2k)!` and each off-diagonal
   term has modulus `<= 4 delta`, since `w_pi^(-1) w_pi' != e` is trace-separated.
   So the square is `>= (2k)! - 4 ((2k)!)^2 delta`.
5. Combining 3 and 4 gives `eta >= 1/(8 k^2 (2k)!) - C_k delta`.
6. Tensor powers `sigma^(⊗m)` on `[n]^m` add Hamming defects over coordinates,
   and fixed-point densities multiply.  With displacement `>= c_k/2`,
   `m = ceil(2 log(1/eps)/c_k)` gives separation `>= 1 - eps`.
7. For microstates that only approximately preserve an equal-rank frame,
   apply `coarse-frame-normalizers-are-near-block-monomial` on the window
   first.
