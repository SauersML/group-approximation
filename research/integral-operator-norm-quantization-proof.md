---
rg: 2
id: integral-operator-norm-quantization-proof
kind: route
title: Capacity below one forces finite algebraic spectrum, and Kronecker's theorem turns conjugates inside (-2,2) into cosines of rational angles
target: integral-operator-norm-below-two-is-quantized
requires:
  - integral-spectra-of-small-capacity-are-finite
---

**1. `||A|| >= 1`.** Pick `i` with a nonzero entry in row `i`. Then
`||r_A(delta_e e_i)||_2^2 = sum_(j,g) |A_ij(g)|^2 >= 1`.

**2. Finite spectrum.** `sigma(A)` lies in `[-||A||, ||A||]`, whose logarithmic
capacity is `||A||/2 < 1`, and capacity is monotone under inclusion. By
`integral-spectra-of-small-capacity-are-finite`, `sigma(A)` is finite: a
Galois-stable set of real algebraic integers, hence totally real, and the
spectral measure is atomic with rational, Galois-equal masses.

**3. Kronecker.** Let `alpha` be an algebraic integer all of whose conjugates lie
in `[-2, 2]`, with minimal polynomial `f` of degree `d`.
- Put `h(z) = z^d f(z + 1/z)`, a monic integer polynomial of degree `2d`. Every
  root `z` has `z + 1/z` a conjugate of `alpha` in `[-2, 2]`, so `|z| = 1`.
- For a root `z`, every power `z^k` is an algebraic integer of degree at most
  `2d` all of whose conjugates have modulus `1`.
  - So its minimal polynomial has coefficients bounded by `binom(2d, i)`.
  - Finitely many such polynomials exist, so `z^k = z^l` for some `k != l`, and
    `z` is a root of unity.
- Hence `alpha = zeta + zeta^(-1) = 2cos(2 pi a/b)` with `gcd(a, b) = 1`.

**4. The norm.** The conjugates of `2cos(2 pi a/b)` are `2cos(2 pi k/b)` with
`gcd(k, b) = 1`, all in `sigma(A)` by step 2. Their largest absolute value is:
- `2cos(pi/b)`, attained at `k = (b-1)/2`, if `b` is odd;
- `2cos(2 pi/b)`, attained at `k = 1`, if `b` is even.

In both cases it is `2cos(pi/q)` with `q` an integer, `q >= 2` since `||A|| < 2`.
So `||A|| = max_(lambda in sigma(A)) |lambda|` is `2cos(pi/q)` for an integer
`q >= 2`, and every atom is a cosine of a rational multiple of `pi`.

**5. Corollary.** Let `A != 0` with `||A|| < sqrt 2 = 2cos(pi/4)`.
- By step 4 every Galois orbit in `sigma(A)` has maximal absolute value
  `2cos(pi/q) < sqrt 2`, so `q <= 3` and every `lambda` has `|lambda| <= 1`.
- The cosines of rational angles with all conjugates in `[-1, 1]` are `0, 1, -1`.
- So `A(A - 1)(A + 1) = 0`, `A^2` is a projection, and `||A|| = 1` by step 1.
QED
