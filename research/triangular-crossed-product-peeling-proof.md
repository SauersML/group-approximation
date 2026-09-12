---
rg: 2
id: triangular-crossed-product-peeling-proof
kind: route
title: Back-substitute along the peeling rounds for kernel vectors, and invert a signed permutation plus a nilpotent
target: triangular-crossed-product-elements-are-units-or-zero-divisors
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
  - crossed-product-zero-divisors-are-detected-on-fibres
  - monomial-crossed-product-elements-are-units-or-zero-divisors
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Theorem 4.1 of the artifact.

**Back-substitution.** A vector supported on points removed before round `r` equals `x_mu eta` for some
`eta` supported on earlier columns. Clear the latest round present using the unique column removed with
each of its points, then repeat.

**Stops.**
- *A dead column.* A live column with no live point gives `x_mu (delta_k - eta) = 0`.
- *Two columns sharing their one live point.* With entries `d` and `d'` there, they give
  `x_mu (d' delta_k - d delta_(k') - eta) = 0`.
- In both cases Theorem 2.1 turns the kernel vector into a left zero divisor.

**Termination.**
- *The diagonal part.* `D = sum_(r,g) [g] b_g 1_(E_(r,g))`, where `E_(r,g)` is the clopen set on which the
  base column is removed in round `r` with live point `g`. `D` has `c_D = 1` and `n_D <= 1`, so
  `n_D = 1` by Haar balance, and `D` is a unit by the monomial dichotomy.
- *The nilpotent part.* `N = x - D` sends round-`r` columns to earlier points, so `D^-1 N` lowers the round
  and is nilpotent in every fibre. Fibres are faithful, so it is nilpotent in `B`.
- *Conclusion.* `x = D(1 + D^-1 N)` is a unit.

*Verification by `w4-vf-linear-b` (2026-09-12), Sections 18.1 and 23.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS, including part 3 and Example 4.3. Re-derived independently:*
- *back-substitution, and both stop types;*
- *termination with `c_D = 1`, `n_D <= 1` and Haar balance, then nilpotent `D^-1 N`;*
- *equal live measures, through disjoint translates of the removal sets;*
- *Example 4.3 type by type: round one removes exactly six odd types, and round two stops at type `(1,1,0,1)`.*
