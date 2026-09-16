---
rg: 2
id: stw74-separable-subcounterexample-proof
kind: route
title: Countable closure under fullness witnesses, infiniteness witnesses and CPAP factorizations
target: stw74-counterexamples-have-separable-subcounterexamples
requires:
  - stw74-property-sp-is-the-exact-missing-condition
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Full proof: Section 4 of the artifact.  Build separable
`C_0=C*(S union {1}) subset C_1 subset ...` and put
`C=closure(union C_n)`.  Passing from `C_n` to `C_(n+1)`, add:

* (alpha) for `c` in a countable dense subset `P_n` of the positive unit
  sphere of `C_n`, elements `y_(c,i) in A` with
  `sum_i y_(c,i)*((c-1/4)_+)^2 y_(c,i)=1` (these exist by the fullness normal
  form in the simple algebra `A`);
* (beta) for `q` in a countable dense subset `Q_n` of the nonzero
  projections of `C_n`, one `w_q in A` with `w_q*w_q=q`, `w_qw_q*<q`;
* (gamma) if `A` has the CPAP, for each finite subset `F` of a countable
  dense `G_n subset C_n` and each `j`, a c.p.c. factorization
  `psi phi` through some `M_k` that is `1/j`-good on `F`, and add
  `psi(e_rs)`.

*Simplicity.*  A normalized `a in I_+` is within `1/4` of some `c in P_n`,
so `(c-1/4)_+ in I` and (alpha) gives `1 in I`.

*Infiniteness.*  A projection `p in C` is within `2/5` of some `q in Q_n`;
`z=qp+(1-q)(1-p)` is invertible with `zp=qz`, the unitary
`u=z(z*z)^(-1/2) in C` has `upu*=q`, and `u*w_q u in C` witnesses that `p` is
infinite in `C`.

*CPAP.*  Restrict `phi` to `C`; `psi` lands in `C` by (gamma); an
`epsilon/3` argument.

*Consequences.*  `Her_C(a) subset Her_A(a)`.  If `A` is a counterexample,
the required claim gives `0!=a in A_+` with `Her_A(a)` projectionless; take
`S={a}`, so `C` fails (SP), and the required claim applied to `C` shows `C`
is not purely infinite.
