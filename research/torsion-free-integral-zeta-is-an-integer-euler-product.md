---
rg: 2
id: torsion-free-integral-zeta-is-an-integer-euler-product
kind: claim
title: Over a torsion-free group the trace zeta series of an integral matrix is an Euler product with integer coefficients
distinct_from:
  determinant-violations-have-finite-moment-certificates: that turns a violation into an archimedean certificate on finitely many moments; this is an exact arithmetic constraint on all moments, valid over every torsion-free group
  integer-moment-measure-with-negative-log-determinant: that shows integer moments alone allow a negative log determinant; this adds the Euler-product congruences, which that measure fails already at p = 2
---

**ESTABLISHED** by `torsion-free-integral-zeta-euler-product-proof`.

Let `G` be torsion-free and `T in M_n(Z[G])`. A *letter* is a triple
`(i, j, g)` with `T_ij(g) != 0`, weighted by `T_ij(g)`. A *closed word* of
length `d` is a sequence `(i_0,i_1,g_1)(i_1,i_2,g_2)...(i_(d-1),i_0,g_d)` with
`g_1 g_2 ... g_d = e`. Rotation acts on closed words. A *necklace* `c` is the
rotation class of a closed word with trivial rotation stabilizer. Its length
is `|c|`, and its weight `w(c) in Z` is the product of the letter weights.
Then, for every `j >= 1`,

```text
Tr(T^j) = sum_(d | j) d * sum_(|c| = d) w(c)^(j/d),
```

and, as formal power series,

```text
exp( sum_(j>=1) Tr(T^j) z^j / j ) = prod_c (1 - w(c) z^|c|)^(-1)  in 1 + z Z[[z]].
```

**Consequences.**

- **Frobenius congruences.** `Tr(T^(pj)) == Tr(T^j) (mod p)` for every prime
  `p` and every `j >= 1`.
- **FK form.** For self-adjoint `T` and real `|z| < 1/||T||` the series is
  `1/det_N(G)(1 - zT) = exp(-integral log(1 - xz) d mu_T(x))`. So the inverse
  Fuglede--Kadison characteristic function has integer Taylor coefficients.
  No approximation of `G` is used.
- **A necessary condition for counterexamples.** A determinant or Atiyah
  counterexample over a torsion-free group, such as Fournier-Facio's group or
  the torsion-free master tester, needs a spectral measure all of whose integral
  polynomial images have integer Euler products.
  - The Fibonacci measure of `integer-moment-measure-with-negative-log-determinant`
    fails this: its moments `1, 1, 2, 5` give `m_2 - m_1 = 1`, odd.

**Torsion is necessary.** Over `Z/2` with `T = g`, the moments are `1` at even
`j` and `0` at odd `j`, and the series is `(1 - z^2)^(-1/2)`, which is not
integral.
