---
rg: 2
id: higman-u2-word-energy-bound
kind: claim
title: Higman's marked HS energy is at most twice its relator energy on U(2)
distinct_from:
  higman-hs-word-coefficient-exceeds-nine-fifths: that supplies a lower bound using one rational two-dimensional tuple; this proves an upper bound on every U(2) tuple by a complete polynomial certificate.
  higman-hs-word-coefficient-exceeds-sixteen: that refutes coefficients at most sixteen in U(3); this proves coefficient two for U(2) and common sums of blocks of size at most two.
artifacts:
  - research/artifacts/higman-u2-bound.md
  - research/artifacts/higman-u2-bernstein-certificate.json
  - experiments/higman_u2_certificate.py
  - experiments/test_higman_u2_certificate.py
---

For every U in U(2)^4, with Higman relators
`r_i=U_i U_(i+1) U_i^-1 U_(i+1)^-2`, every generator satisfies
`e_(g_j)(U)<=2 sum_i e_(r_i)(U)`, in the normalized HS metric.
The same holds for common direct sums of blocks of size at most two.

If an arbitrary tuple U lies within epsilon, in maximum generator HS
distance, of that common-block class, then
`||U_j-I||_2<=sqrt(2 sum_i e_(r_i)(U))+(1+10 sqrt(2))epsilon`.
On an exact common invariant decomposition with dimension fraction theta
in blocks of size at least three, `e_(g_j)<=2 sum_i e_(r_i)+4 theta`.

The explicit U(3) counterexample prevents extending the coefficient to
unrestricted blocks. These results constrain hypothetical microstates
but prove no nonhyperlinear existence theorem.
