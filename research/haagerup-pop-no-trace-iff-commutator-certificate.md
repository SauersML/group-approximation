---
rg: 2
id: haagerup-pop-no-trace-iff-commutator-certificate
kind: claim
title: A unital C*-algebra has no tracial state iff it carries commutator certificates of every defect
distinct_from:
  stw01-traceless-separable-simple-reduction: that reduces a Kaplansky counterexample to a traceless simple algebra; this is the general characterization of tracelessness by finite families with sum x*x = 1 and small sum xx*.
artifacts:
  - research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md
---

**ESTABLISHED (literature).**  For a unital C\*-algebra `A` the following are
equivalent:

1. `A` admits no tracial state;
2. there are `n >= 2` and `x_1,...,x_n in A` with `sum x_j* x_j = 1` and
   `||sum x_j x_j*|| < 1`;
3. for every `delta > 0` there are `n` and `x_1,...,x_n in A` with
   `sum x_j* x_j = 1` and `||sum x_j x_j*|| <= delta`;
4. there is `n >= 2` such that every element of `A` is a sum of `n` commutators;
5. `A tensor C*_r(F_infinity)` is properly infinite.

This is Theorem 3.1 of Milhøj–Rørdam, arXiv:2309.17412v2, due to Haagerup
(C. R. Math. Rep. Acad. Sci. Canada 36 (2014)), with condition 4 added by Pop
(Proc. AMS 130 (2002)).

In the Problem I region a family as in 2–3 is called a **certificate**.  The
Milhøj–Rørdam invariant `nu(A)` is the least size of a certificate with defect
`1/2`.  Every certificate of size `N` has defect at least `1/N` (artifact,
Lemma 1.1).
