---
rg: 2
id: jnvwy-low-degree-affine-unsafety-reflection-proof
kind: route
title: Add the characteristic-two proof tables and invoke low-degree PCP soundness
target: jnvwy-low-degree-pcp-reflects-affine-unsafety
requires:
  - hadamard-pcpp-reflects-affine-unsafety
---

For an odd affine-unsafety witness in one source answer-pair support, choose
arbitrary perfect JNVWY Theorem 10.25 proof tables and add them over the
field `F_(2^k)`.  Individual-degree bounds survive addition.  Equation (13)
makes the first two low-degree tables the encodings of the sums of the
padded source words.  Definition 10.8 encodes a bit by `0 -> 00`, `1 -> 01`
and padding by `blank -> 10`; therefore an odd sum is precisely the padded
encoding of the bitwise-xor source answer.

If the sum proof were accepted on more than half the points, Theorem 10.25
soundness would decode those first two tables to a source answer accepted by
the old decider.  Injectivity of the symbol encoding identifies it with the
rejected xor answer, a contradiction.  Some point therefore rejects the
sum proof.  Every component proof accepts at that point by perfect
completeness, and evaluation in the fixed binary basis is linear.  The
rejected `POINT_6` response is consequently the odd xor of positive accepted
responses.

The oracle measurement preserves the source joint atom.  A fixed positive
answer in every other repeated coordinate is preserved by an odd xor, so
parallel repetition preserves the witness as well.  This proves the whole
Theorem 6.2 transformation reflects affine unsafety, and iterating proves
`(LPR4)`.
