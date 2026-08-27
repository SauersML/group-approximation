---
rg: 2
id: dfnqxy-answer-reduction-affine-support-audit-proof
kind: route
title: Separate the linear Hadamard tests and use PCPP soundness against the three-point affine ghost
target: dfnqxy-answer-reduction-does-not-preserve-affine-safe-support
requires:
  - fano-cap-witness-sections-force-source-affine-safety
---

Appendix B.4 of Dong, Fu, Natarajan, Qin, Xu, and Yao, *The Computational
Advantage of MIP* Vanishes in the Presence of Noise*, gives the answer-reduced
verifier explicitly.  The consistency, answer, and proof cross-checks are
equalities.  The Hadamard subset tester accepts by equations of the form

```text
a_i+c=a'_i,   a_i=d_i,   a'_i=d_i,
```

and its remaining checks are equalities.  These are affine equations, so
every subset of their satisfying relation obeys `(DAR1)`.

The `Verify` test instead applies the chosen PCPP verifier to restrictions of
three Hadamard codewords.  In the perfect-completeness construction, an
original joint outcome `(y_0,y_1)` is refined by the codewords of `y_0,y_1`
and a perfect PCPP proof for that accepted pair.  This gives `(DAR2)` and
shows that no other test family needs a source-support audit.

For the counterexample, take a diagonal PVM of ranks `2,1,1` on both halves
of the maximally entangled state in `C^4 tensor C^4`, namely two EPR pairs.
It is real, symmetric, commuting on the only queried pair, and its
correlation has support exactly `(DAR3)`.  PCPP perfect
completeness supplies proofs `pi_i` accepted for every random string.

The Hadamard code is linear.  Hence, for every fixed view, the xor of the
three honest response strings is the response obtained from
`(y_*,y_*,pi_*)`.  The invalid word `y_*=111` differs from each of
`e_1,e_2,e_3`, so each Hadamard block differs from every valid encoded block
on exactly half its coordinates.  In particular the concatenated input is
farther than the PCPP threshold `gamma<=1/4` from the accepted encoded
language.  PCPP soundness says that the fixed proof `pi_*` is rejected with
positive probability, and therefore on at least one view `r`.  At that view
the three original responses lie in `S_r`, while their xor does not lie in
`C_r`, proving `(DAR5)`.

Theorem 36 applies this transformation to one particular oracularized HALT
protocol, but its proof invokes Theorem 35 without any additional support
analysis.  Culf--Mastel Corollary 6.4 likewise records perfectness and
oracularizability only.  The counterexample therefore fences the formal
inference while leaving the particular HALT support as the exact open finite
audit.
