---
rg: 2
id: resolvent-assembly-controls-covariance-and-leakage-proof
kind: route
title: "Liu's Cholesky covariance and monotone inverse identity control resolvents"
target: resolvent-assembly-controls-covariance-and-leakage
requires: []
artifacts:
  - research/artifacts/liu-analytic-leaves-proof-acceptance-2026-09-20.md
---

## Attribution and proof

This is an independently verified exposition of **Jihao Liu**,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Lemmas 5.2 and 5.3. Their results and mechanisms are Liu's,
not new discoveries of Cairn. Section C of the acceptance artifact gives
the full matrix proof, with all rectangular norms normalized by d.

Write the projections as a column F of inclusions. Polar completions
give an auxiliary unitary V with squared inclusion defect at most
sum_i||[u,f_i]||_2^2. The rectangular map
Q_mu(Z)=(I+mu Z*Z)^(-1) is sqrt(mu)-Lipschitz, yielding (5.1).
The positive-diagonal block Cholesky factorization
I+mu ZZ*=C(Z)C(Z)* has J(Z)=C(Z)^(-1)Z 3-Lipschitz: differentiating
gives Xi+Xi*=Upsilon, and the diagonal multipliers
g_s/(g_r+g_s) show ||Xi||_2<=||Upsilon||_2 without a block-count
constant. The row formulas give B_i=W_i*W_i and the summed 72mu
energy estimate.

Since W_i F_i*=sqrt(mu) H_i/sqrt(1+mu H_i), its derivative is bounded
away from zero on [0,1]. Divided differences recover the commutator of
H_i, then of C_ii, and finally the localized commutator of
D_(i-1) on f_i. The explicit constant C_mu in the artifact depends
only on mu. Uniform approximation by finite linear combinations of
resolvents gives the fixed-continuous-function conclusion, taking the
ultrafilter limit before the approximation error tends to zero.

For any positive monotone chain, the noncommutative inverse identity
```
(A-B)^(-1)-A^(-1)-A^(-1)B A^(-1)
  =A^(-1)B(A-B)^(-1)B A^(-1)>=0
```
telescopes to a uniform resolvent sandwich bound. Direct-sum triangle
inequalities and the same resolvent approximation give total leakage
at most 2K_(g,rho) tr(I-e)+2rho^2, independent of dimensions and
chain length. No mutual commutation of the chain members is used.

This direct route is backed by the detailed differentiation, Schur
complement, divided-difference, approximation, and inverse-identity
calculations in the artifact. It does not accept Theorem 5.1's later
selection/assembly step merely from these estimates and is not a Lean
certification.
