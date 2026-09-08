---
rg: 2
id: leavitt-finite-trace-tests-regularize-both-factor-profiles
kind: claim
title: Finite single-cycle trace tests regularize both Leavitt factor profiles in the same dimension
distinct_from:
  leavitt-single-cycle-trace-controls-finite-sets: That promotes one trace to finitely many word traces; this converts those traces into exact regular finite-factor profiles with explicit generator and relator perturbation bounds.
  binary-leavitt-hyperlinear-iff-24k-feasible: That characterizes full-kernel feasibility with both profiles frozen; this gives a finite quantitative correction from unfrozen profiles, including approximate laws for the second factor.
artifacts:
  - research/artifacts/leavitt-finite-factor-profile-correction-2026-09-08.md
---

Let `n` be divisible by `24`, let `C,B_1,B_2,B_3 in U(n)`, and
assume `C^3=I`. Use normalized trace and Hilbert--Schmidt norm. Set

```text
alpha=|tr C|,
beta=max( max_i ||B_i^2-I||_2,
          max_(i<j) ||[B_i,B_j]-I||_2 ).
```

Apply the finite single-cycle certificate to the seven words
`b_1^(v_1)b_2^(v_2)b_3^(v_3)`, `v in F_2^3\{0}`, with parameters
`N_0,M_0>=2`, `r>=1`. If its literal native rows have defect at
most `epsilon`, put

```text
eta_0=sqrt(1/N_0 + sqrt(1/M_0+3^(-r)+alpha+18 epsilon)),
d_C=sqrt(2 alpha),
d_B=10 beta+sqrt((9/2) (eta_0+30 beta)).
```

There exist unitaries `C',B_1',B_2',B_3'` on the same `C^n`
whose `C_3` and `C_2^3` representations are both exactly regular
multiples and such that

```text
||C'-C||_2<=d_C,      max_i ||B_i'-B_i||_2<=d_B.
```

If a word has `ell_c` occurrences of `c` or its inverse and
`ell_b` occurrences of the `b_i` or their inverses, its evaluation
changes by at most `ell_c*d_C+ell_b*d_B`. In particular any
length-`L` relator of initial defect `zeta` has corrected defect
at most `zeta+L*max(d_C,d_B)`.

When the second factor is exact, take `beta=0`. When `tr C=0`,
one can keep `C'=C` literally; otherwise a regular correction
cannot keep `C` fixed. A simultaneous final unitary conjugation
puts the tuple in the existing `24k` relative-unitary form and
preserves every relator defect. The displayed movement bounds
refer to the correction before this final choice of basis.

The artifact gives dimension adjustments when `24` does not
divide `n`, proves equivalence of full-kernel feasibility with
these unfrozen tests, and gives a trace-only counterexample to
omitting the second-factor laws. Its sharp eight-character
surplus bound is `f_B<=9 eta/8` when all seven traces have modulus
at most `eta`; no sharp generator-transport cost is asserted.
It establishes neither
feasibility nor a uniform gap for one fixed packet.
