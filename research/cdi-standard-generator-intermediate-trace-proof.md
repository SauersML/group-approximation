---
rg: 2
id: cdi-standard-generator-intermediate-trace-proof
kind: route
title: Use the nonzero hyperfinite conditional expectation of the Ge-Popa block generator
target: cdi-standard-generator-choice-fails-projective-gate
requires:
  - cdi-wreath-extension-preserves-projective-basis-gate
---

Let `E_R:P tensor R -> 1 tensor R` be the trace-preserving conditional
expectation.  From `(CDI-S1)`,

```text
E_R(c)=sum_i tau_P(w_i) p_i.
```

This is nonzero because its compression by `p_1` is `p_1` (`w_1=1`).  The
linear span of group words in `u,v` is weakly and `L^2`-dense in `R`, since
`u,v` generate `R`.  Therefore some group word `r(u,v)` satisfies

```text
tau_Mtilde(c (1 tensor r))
  = tau_R(E_R(c) r) != 0.                              (CDI-S3)
```

The unitary `c` does not belong to `1 tensor R`: compressing by `p_2` would
otherwise force the non-scalar unitary `w_2` to be scalar.  Consequently
`c(1 tensor r)` is not scalar.  Equality in Cauchy--Schwarz for a unitary
says `|tau(z)|=1` only when `z` is scalar.  Together with `(CDI-S3)` this
gives `(CDI-S2)`.

Under the homomorphism `F_3->U(M_tilde)` sending its generators to `a,b,c`,
the unitary `c(1 tensor r)` is one group word.  It is outside the scalar
kernel and has nonzero character, so gate `(G1)` fails.  The transfer theorem
then puts the same single-site coefficient into the final CDI character.

