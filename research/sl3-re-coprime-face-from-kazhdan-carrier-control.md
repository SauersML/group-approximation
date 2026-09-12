---
rg: 2
id: sl3-re-coprime-face-from-kazhdan-carrier-control
kind: route
title: Uniform Kazhdan carrier containment captures the moving congruence slot without a rate hypothesis
target: sl3-re-lambda-exact-coprime-face-is-unfaithful
requires:
  - odd-congruence-lambda-exact-sector-collapses
  - kazhdan-generators-control-matrix-algebra-distance
artifacts:
  - research/artifacts/kazhdan-carrier-uniformization-2026-09-08.md
---

Use the matrix witness data of the target. Write `H_k=pi_k(h)` and
let `H_(0,k)=sigma_k(h mod n_k)` be the congruence slot, which is
well defined because `n_k` is coprime to `p`. The established exact
sector proof gives

    ||H_k-H_(0,k)||_2 -> 0.

It also gives `H_(0,k) in sigma_k(Lambda)''` at every coordinate;
membership in `pi(Lambda)''` is neither needed nor asserted.
For a fixed Kazhdan generating set `S` of `Lambda`, `(KCU1)` gives

    dist_2(H_k,B_k)
      <= ||H_k-H_(0,k)||_2
         +(2/kappa)sqrt(sum_(s in S)dist_2(sigma_k(s),B_k)^2)
      -> 0.

Replacing the original source representatives by the exact `sigma_k(s)`
does not affect near containment if they originally agreed only in the
ultraproduct. Since `H_k` is unitary, conditional-expectation
orthogonality implies

    ||E_(B_k)(H_k)||_2^2=1-dist_2(H_k,B_k)^2 -> 1,

contradicting the outside-element expectation required by the witness.
The estimate has no dependence on `n_k` or on the word length of the
congruence slot. It closes every coprime exact matrix face, with arbitrary
multiplicities, and uses neither actor stability nor a trace-profile
restriction beyond those already present in the candidate witness.
