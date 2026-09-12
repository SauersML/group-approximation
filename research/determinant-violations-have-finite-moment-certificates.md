---
rg: 2
id: determinant-violations-have-finite-moment-certificates
kind: claim
title: A determinant violation is certified by finitely many integer trace moments and one polynomial upper bound for the logarithm
distinct_from:
  integral-spectral-limits-satisfy-serre-inequalities: that proves limits of integer spectra obey the inequalities; this shows that every strict violation is an open condition on finitely many integer moments, so it is witnessed by a finite certificate
  determinant-conjecture-iff-serre-class-spectra: that reformulates the conjecture through all Serre inequalities; this makes a single failure finitely checkable from moments
  integer-moment-measure-with-negative-log-determinant: that exhibits one moment sequence of integers whose measure has negative log determinant; this says every violation over a group is detected by a finite segment of its moment sequence
---

**ESTABLISHED** by `determinant-moment-certificate-proof`.

Let `G` be a group and `A in M_(m x n)(Z[G])`. Put `T = A^* A`, let
`m_j = Tr(T^j)` be its integer trace moments, and let `C_T` be the sum of the
absolute values of all coefficients of `T`, so `||T|| <= C_T`. Then
`det_N(G)(A) < 1` if and only if there are `N`, a polynomial
`P = sum_(j<=N) p_j x^j in Q[x]` and an integer `k >= 1` with

```text
(i)   P(x) >= log x + 1/k    for all x in (0, C_T],
(ii)  P(0) >= 0,
(iii) sum_(j<=N) p_j m_j < 0.
```

For rational `P` and `k`, condition (i) is decidable by rigorous interval
subdivision.

**Consequences.**

- **Violations are Pi^0_1-refutable.** Suppose `G` is finitely generated with
  solvable word problem. Then the moments are computable, certificates are
  enumerable and checkable, and the set of violating matrices is recursively
  enumerable. So "G satisfies Lück's determinant conjecture" is a `Pi^0_1`
  statement. This covers the binary Leavitt unit group and the Kun--Thom
  wreaths. A counterexample hunt over them is a certificate search.
- **Transfer along moments.** Take a certificate `(N, P, k)` for `A` over `G`.
  Every `B in M(Z[H])`, over any group `H`, with
  `Tr((B^*B)^j) = m_j` for `j <= N` and `||B^* B|| <= C_T` also has
  `det_N(H)(B) < 1`. In particular the first `N` moments of a violating matrix
  are not the moments of any integral matrix over a sofic group.
