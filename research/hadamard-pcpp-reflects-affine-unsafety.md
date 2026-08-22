---
rg: 2
id: hadamard-pcpp-reflects-affine-unsafety
kind: claim
title: Hadamard-PCPP answer reduction reflects every affine-unsafe source support into a Verify view
distinct_from:
  dfnqxy-answer-reduction-does-not-preserve-affine-safe-support: that gives one three-outcome counterexample and leaves the particular PCPP views as a finite audit; this proves the general contrapositive for every affine-unsafe positive source answer support and every choice of perfect PCPP proofs.
  fano-cap-witness-sections-force-source-affine-safety: that concerns the later classical pp reduction to R-star; this concerns the preceding Hadamard-PCPP answer reduction itself.
  cmps-copying-is-support-neutral: that substitutes copied binary observables in 3SAT clauses; this follows positive joint answers through the earlier constant-answer compiler.
---

**ESTABLISHED.**  Fix a question pair `(x_0,x_1)` of the verifier `V` fed
into Theorem 6.9 of Dong--Fu--Natarajan--Qin--Xu--Yao,
arXiv:2312.04360v3.  Let

```text
S subseteq {(y_0,y_1): C_(x_0,x_1)(y_0,y_1)=1}          (HPR1)
```

be the positive joint-answer support of the chosen perfect strategy.  If
`S` is affine-unsafe, so that for some odd list of positive answers

```text
y^(1),...,y^(2m+1) in S,
y^*=xor_i y^(i),
C_(x_0,x_1)(y^*)=0,                                    (HPR2)
```

then the honest perfect strategy constructed for the answer-reduced verifier
has an affine-unsafe positive support on at least one `Verify` question.
This conclusion holds for **every** choice of perfect PCPP proof assigned to
the source outcomes in `(HPR2)`.

Indeed, write `z^(i)` for the pair of Hadamard encodings of `y^(i)` and
choose any perfectly accepting PCPP proof `pi^(i)`.  Put

```text
z^*=xor_i z^(i)=Hadamard(y^*),
pi^*=xor_i pi^(i).                                      (HPR3)
```

The equality uses linearity of the Hadamard code and oddness of the list.
Since `y^*` is rejected, Definition 6.7 and the distance `1/2` of distinct
Hadamard words show that the two-block word `z^*` is at least `1/4`-far from
the accepted encoded language.  The PCPP is chosen with proximity parameter
`gamma<=1/4` and soundness `<1`; hence some random view rejects
`(z^*,pi^*)`.

For this fixed view, perfect completeness accepts the restricted response
coming from every `(z^(i),pi^(i))`.  The honest answer-reduced measurement is
a deterministic refinement of the original positive answer atom, so every
one of those restricted responses remains a nonzero atom.  Coordinate
restriction is linear, and therefore their odd xor is exactly the rejected
restriction of `(z^*,pi^*)`.  The positive support of this `Verify` context
is consequently not affine-safe inside its accepting relation.

Thus affine safety of **all** PCPP `Verify` supports in the published HALT
strategy has the following necessary precursor:

```text
every positive accepted-pair support of the verifier immediately before
the final Hadamard-PCPP reduction is affine-safe.         (HPR4)
```

The final answer reduction cannot use its proof oracle, random views,
bounded answer size, or a different choice of perfect proofs to repair an
earlier odd-xor violation.  This does not prove `(HPR4)` or its negation for
the particular MIP-star-equals-RE HALT strategy; it moves the remaining
source-specific audit strictly before the final PCPP layer.

