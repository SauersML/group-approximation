---
rg: 2
id: sylvester-rank-function-quotients-are-weakly-finite
kind: claim
title: The null ideal of a Sylvester matrix rank function has a weakly finite quotient carrying a faithful rank function
distinct_from:
  simple-group-rank-functions-are-augmentation-or-detecting: that classifies rank functions on group algebras of simple groups by their null subgroup; this is the ring-level fact that any rank function descends to a faithful one on a weakly finite quotient, used to split the state upgrade.
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

**ESTABLISHED** (artifact Section 1, Lemma A.1 and Theorem A). Let `A` be a unital ring and `N` a
Sylvester matrix rank function on `A` with `N(1) = 1`. Then:
- `N(I_m - BA) - m = N(I_n - AB) - n` for every `n x m` matrix `A` and `m x n` matrix `B`;
- `ker N = {x : N(x) = 0}` is a proper two-sided ideal, and a matrix has rank 0 iff its entries lie in it;
- `N` descends to a faithful Sylvester matrix rank function on `A / ker N`;
- `A / ker N` is weakly finite: `AB = I_n` there implies `BA = I_n`, for every `n`.

So a ring with a Sylvester matrix rank function has a nonzero weakly finite image. The rank condition
(equivalently, a state on `(K_0(A), [A])`) does not obviously give one.

Proof: route `sylvester-rank-function-quotients-weakly-finite-proof`.
