---
rg: 2
id: jnvwy-low-degree-pcp-reflects-affine-unsafety
kind: claim
title: The low-degree PCP answer reductions reflect every earlier affine-unsafe support
distinct_from:
  hadamard-pcpp-reflects-affine-unsafety: that treats the final binary Hadamard-PCPP reduction of DFNQXY; this treats the characteristic-two low-degree PCP reduction used in each of the two preceding applications of their Theorem 6.2.
  dfnqxy-pcpp-contract-allows-nonlinear-proof-views: that shows an otherwise admissible PCPP can create affine unsafety over a safe source; this proves that the concrete low-degree PCP layer cannot delete affine unsafety already present at its source.
  dfnqxy-halt-completeness-support-is-not-canonically-specified: that audits the missing choice of one HALT completeness strategy; this is a universal implication for every choice of perfect low-degree PCP witnesses.
---

**ESTABLISHED.**  Consider the characteristic-two low-degree answer
reduction of Ji--Natarajan--Vidick--Wright--Yuen, arXiv:2001.04383v3,
Sections 10.4--10.6, which is the construction invoked in the two
pre-Hadamard applications of Theorem 6.2 of
Dong--Fu--Natarajan--Qin--Xu--Yao, arXiv:2312.04360v3.  Fix a source
question pair and an odd list of positive joint answers of the same answer
length

```text
(a^(1),b^(1)),...,(a^(2r+1),b^(2r+1))
```

which the source decider accepts, but whose bitwise xor `(a^*,b^*)` it
rejects.  For **every** choice of perfectly accepting PCP proofs for these
answers, the honest answer-reduced strategy has an affine-unsafe positive
support on a `POINT_6` game-check question.

Indeed, let

```text
Pi^(i)=(g_1^(i),...,g_5^(i),c_0^(i),...,c_m'^(i))
```

be any of the perfect low-degree proofs supplied by the completeness part
of JNVWY Theorem 10.25, and add the proof tables over `F_q`, where
`q=2^k`:

```text
Pi^* = sum_i Pi^(i).                                    (LPR1)
```

The sum is still a legal proof tuple with the same individual-degree
bound.  The low-degree encoding `a -> g_a` is linear (JNVWY (13)).  The
tape-symbol encoding is

```text
0 -> 00,   1 -> 01,   blank -> 10                       (LPR2)
```

(JNVWY Definition 10.8).  Hence, because the number of summands is odd and
all answers have the fixed protocol answer length, the first two tables of
`Pi^*` are exactly the low-degree encodings of the padded tape encodings of
`a^*` and `b^*`.  Addition in the fixed binary basis of `F_q` is bitwise
xor.

If the PCP verifier `M_AR` accepted `Pi^*` on more than half of its points,
the soundness clause of JNVWY Theorem 10.25 would decode its first two
tables to prefixes accepted by the source decider.  Injectivity of `(LPR2)`
and the fixed blank suffix make those prefixes exactly `a^*,b^*`, contrary
to their rejection.  Therefore some point `z` satisfies

```text
M_AR(z,eval_z(Pi^(i))) = 1   for every i,
M_AR(z,eval_z(Pi^*))    = 0.                              (LPR3)
```

The first line holds pointwise because each completeness proof is accepted
with probability one over a finite uniform point set.  Evaluation at `z`
is linear, so the rejected view in the second line is the odd xor of the
accepted views in the first line.  On the typed `ORACLE/POINT_6`
game-check question, every first-line view is a deterministic refinement of
the corresponding nonzero source atom and is therefore in the positive
support of the honest strategy.  Equation `(LPR3)` is an explicit odd-xor
certificate that this support is affine-unsafe.

Oracularization does not remove the certificate: the oracle outcome is the
same positive pair `(a,b)`.  Parallel repetition does not remove it either:
fix any positive answer in every other coordinate; an odd xor preserves
those fixed coordinates, while the bad coordinate still rejects.  Fixed
type labels introduced by detyping are likewise preserved by an odd xor.
Consequently the full parallel-repeated low-degree transformation used in
DFNQXY Theorem 6.2 reflects affine unsafety.

Applying this twice to DFNQXY Theorem 6.10 gives the exact contrapositive

```text
all positive supports of V_2 are affine-safe
    => all positive supports of the original chosen completeness
       strategy V are affine-safe.                         (LPR4)
```

Together with `hadamard-pcpp-reflects-affine-unsafety`, no one of the three
published answer-reduction layers can repair an earlier odd-xor violation.
This does not decide whether a suitable original HALT completeness strategy
has affine-safe supports; it moves that source-specific question all the
way back before the first answer reduction.
