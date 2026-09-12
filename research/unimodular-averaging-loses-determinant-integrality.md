---
rg: 2
id: unimodular-averaging-loses-determinant-integrality
kind: claim
title: Sofic unimodular integral networks can have non-integer Fuglede--Kadison determinants and non-integer root moments
distinct_from:
  root-measures-of-integer-matrices-can-violate-serre: that breaks the Serre inequality at a single root of an integer matrix; this keeps the inequality under unimodular averaging and shows what averaging loses, namely integrality of the determinant and of the moments
  torsion-free-integral-zeta-is-an-integer-euler-product: that gets integer necklace numbers from the integer-valued trace of a group ring; this shows the trace of an integral network is an average over roots, so those numbers need not be integers
artifacts:
  - research/artifacts/unimodular-networks-mdc-2026-09-12.md
---

**ESTABLISHED** by `unimodular-averaging-loses-determinant-integrality-proof`
(artifact Proposition 2).

1. **Finite.** Take two vertices with loops of weight `2` and `3`, joined by an
   edge of weight `1`, and root uniformly. The determinant is `sqrt 5` and the
   first root moment is `N_1 = 5/2`.
2. **Infinite and ergodic.** On `Z`, take i.i.d. `g_k in {1,2}` with
   `P(g_k = 2) = p`, loops of weight `2 g_k^2`, and edges of weight
   `g_k g_(k+1)`. The network is connected, ergodic and sofic, and its operator
   is `M_g (2 + s + s^-1) M_g`. Its determinant is `4^p` and
   `N_1 = 2(1 + 3p)`. At `p = 1/4` these are `sqrt 2` and `7/2`.

**Consequences.**
- **No integer-valued determinant.** Any Fuglede--Kadison-type determinant for
  unimodular integral networks that agrees with the usual one on sofic networks
  takes every value in `(1,4)`. Part 2 has no vertex count to normalize away.
  Only the bound `det >= 1` can hold, and for all networks that bound is
  `measure-theoretic-determinant-conjecture`.
- **No integer necklace numbers.**
  - `p_1 = N_1` is `5/2` or `7/2`.
  - In a group ring the trace is an integer coefficient, and that is the source
    of integrality in `torsion-free-integral-zeta-is-an-integer-euler-product`.
  - In an integral groupoid ring, `tr(chi_E) = mu(E)` takes every value in
    `[0,1]`. Mass transport equates two averages and never makes an average an
    integer.
- **Not a counterexample.** Both networks obey every Serre inequality, so
  neither is a counterexample to
  `serre-class-from-unimodular-integral-realizability`.
